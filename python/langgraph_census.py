#!/usr/bin/env python3
"""langgraph_census.py -- how often do PUBLIC LangGraph graphs put a reader and a
writer of one channel into the same superstep?

WHY (2026-09-19 round 35). Every occurrence figure in the paper was either a
race we constructed or a precondition rate on our own scenarios, and the
structural bound of Section 5.8 ran on sixteen topologies transcribed from
documentation. This is the missing denominator: a STATED sampling frame of
public repositories, a SEEDED sample, every StateGraph construction site in the
sample analysed statically (langgraph_static.py: no import, no execution of
third-party code), and unknowns reported as the gap between two bounds.

FRAME. GitHub repository search, Python, query `langgraph in:name,description,readme`,
forks excluded (the API default), the framework's own organisation excluded, in
three star bands. For each band the API reports the band's size and returns at
most its first PAGES*100 repositories by most recent update; the sample is drawn
uniformly, seeded, from what it returned. So this is a sample of RECENTLY
UPDATED public repositories per band, not of all LangGraph code, and not of
private deployments. It measures how code is WRITTEN. It does not measure how
often a graph runs, nor whether a co-scheduled read actually goes stale.

WHAT IS COUNTED. Unit of sampling: the repository. Unit of analysis: the
StateGraph construction site. `rw_plain` -- a co-scheduled pair in which one node
reads a last-value channel the other writes -- is the lower bound; adding
`rw_unknown_channel` and `unknown` graphs gives the upper bound. Repository-level
shares carry Wilson 95% intervals, because repositories are what was sampled.

    python3 python/langgraph_census.py --summary         # tables, from the tracked facts (offline)
    python3 python/langgraph_census.py --check           # recompute the summary; exit 1 on disagreement
    python3 python/langgraph_census.py --hits            # every rw_plain site: repo@sha:path:line, pair, keys
    python3 python/langgraph_census.py --frame           # NETWORK: rebuild the frame (GitHub search API)
    python3 python/langgraph_census.py --sample 60       # NETWORK: draw, fetch, analyse (GITHUB_TOKEN optional)
    python3 python/langgraph_census.py --refetch 10      # NETWORK: re-download 10 sampled repos at their pinned
                                                         # commit and demand the same facts

Standard library only.
"""
import argparse
import io
import json
import math
import os
import random
import sys
import tarfile
import time
import urllib.error
import urllib.parse
import urllib.request

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from langgraph_static import extract  # noqa: E402

SEED = 20260919
DIR = "python/langgraph_census"
QUERY = "langgraph in:name,description,readme language:python"
BANDS = [("stars>=200", "stars:>=200"), ("stars 10-199", "stars:10..199"), ("stars 0-9", "stars:0..9")]
PAGES = 5
EXCLUDED_OWNERS = {"langchain-ai"}
MAX_TARBALL = 40 * 1024 * 1024
MAX_PY = 1024 * 1024
SKIP_PARTS = ("/site-packages/", "/.venv/", "/venv/", "/node_modules/", "/dist-packages/")
UPPER = ("rw_plain", "rw_unknown_channel", "unknown")


def _get(url, accept="application/vnd.github+json"):
    req = urllib.request.Request(url, headers={"Accept": accept, "User-Agent": "langgraph-census"})
    tok = os.environ.get("GITHUB_TOKEN")
    if tok and "api.github.com" in url:
        req.add_header("Authorization", "Bearer " + tok)
    return urllib.request.urlopen(req, timeout=60)


# -------------------------------------------------------------------- frame
def build_frame():
    frame = {"query": QUERY, "retrieved_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
             "pages_per_band": PAGES, "excluded_owners": sorted(EXCLUDED_OWNERS), "bands": []}
    for label, qual in BANDS:
        repos, total = [], None
        for page in range(1, PAGES + 1):
            q = urllib.parse.quote(QUERY + " " + qual)
            url = "https://api.github.com/search/repositories?q=%s&sort=updated&order=desc&per_page=100&page=%d" % (q, page)
            for attempt in range(6):
                try:
                    d = json.load(_get(url))
                    break
                except urllib.error.HTTPError as e:
                    if e.code in (403, 429):
                        time.sleep(20)
                        continue
                    raise
            else:
                raise SystemExit("FAIL: the search API kept refusing %s" % url)
            total = d["total_count"]
            for r in d["items"]:
                if r["owner"]["login"] not in EXCLUDED_OWNERS:
                    repos.append({"full_name": r["full_name"], "stars": r["stargazers_count"], "branch": r["default_branch"]})
            print("  %-14s page %d: %d returned, band size %d" % (label, page, len(d["items"]), total), flush=True)
            if len(d["items"]) < 100:
                break
            time.sleep(7)                       # 10 search requests a minute, unauthenticated
        seen, uniq = set(), []
        for r in repos:
            if r["full_name"] not in seen:
                seen.add(r["full_name"])
                uniq.append(r)
        frame["bands"].append({"band": label, "qualifier": qual, "band_size": total, "returned": uniq})
    os.makedirs(DIR, exist_ok=True)
    with open(os.path.join(DIR, "frame.json"), "w") as fh:
        json.dump(frame, fh, indent=1, sort_keys=True)
        fh.write("\n")
    print("wrote %s/frame.json" % DIR)


# -------------------------------------------------------------------- fetch
def analyse_sources(files):
    graphs = []
    for rel in sorted(files):
        try:
            graphs += extract(files[rel], rel)
        except (SyntaxError, ValueError, RecursionError):
            graphs.append({"path": rel, "status": "unparsed", "pairs": [], "nodes": {}})
    return graphs


def fetch_repo(full_name, ref):
    """(status, sha, {path: source}) -- the StateGraph-bearing .py files of the tarball at `ref`."""
    url = "https://codeload.github.com/%s/tar.gz/%s" % (full_name, ref)
    try:
        resp = _get(url, accept="*/*")
        blob = resp.read(MAX_TARBALL + 1)
    except Exception as e:                      # noqa: BLE001 -- any network failure is a recorded status
        return "fetch_error:%s" % type(e).__name__, None, {}
    if len(blob) > MAX_TARBALL:
        return "too_large", None, {}
    sha, files = None, {}
    try:
        with tarfile.open(fileobj=io.BytesIO(blob), mode="r:gz") as tf:
            sha = tf.pax_headers.get("comment")
            for m in tf:
                if not (m.isfile() and m.name.endswith(".py")) or m.size > MAX_PY:
                    continue
                rel = m.name.split("/", 1)[1] if "/" in m.name else m.name
                if any(p in "/" + rel for p in SKIP_PARTS):
                    continue
                src = tf.extractfile(m).read().decode("utf-8", errors="replace")
                if "StateGraph" in src or "MessageGraph" in src:
                    files[rel] = src
    except (tarfile.TarError, EOFError, OSError):
        return "bad_tarball", sha, {}
    return "ok", sha, files


def analyse_repo(full_name, ref):
    status, sha, files = fetch_repo(full_name, ref)
    return status, sha, analyse_sources(files)


def draw_sample(n):
    with open(os.path.join(DIR, "frame.json")) as fh:
        frame = json.load(fh)
    rng = random.Random(SEED)
    sample, facts = {"seed": SEED, "per_band": n, "repos": []}, []
    for band in frame["bands"]:
        pool = sorted(band["returned"], key=lambda r: r["full_name"])
        picks = []
        while pool and len(picks) < n:
            picks.append(pool.pop(int(rng.random() * len(pool))))
        for i, r in enumerate(picks):
            cache = os.environ.get("CENSUS_CACHE")          # resumable fetch; never shipped
            cfile = os.path.join(cache, r["full_name"].replace("/", "__") + ".json") if cache else None
            if cfile and os.path.exists(cfile):
                with open(cfile) as fh:
                    status, sha, files = json.load(fh)
            else:
                status, sha, files = fetch_repo(r["full_name"], r["branch"])
                if cfile:
                    os.makedirs(cache, exist_ok=True)
                    with open(cfile, "w") as fh:
                        json.dump([status, sha, files], fh)
            graphs = analyse_sources(files)
            sample["repos"].append({"band": band["band"], "full_name": r["full_name"], "stars": r["stars"],
                                    "sha": sha, "fetch": status, "graphs": len(graphs)})
            for g in graphs:
                g.update({"repo": r["full_name"], "sha": sha, "band": band["band"]})
                facts.append(g)
            print("  %-14s %3d/%d %-50s %-12s graphs=%d" % (band["band"], i + 1, len(picks), r["full_name"][:50], status, len(graphs)), flush=True)
    with open(os.path.join(DIR, "sample.json"), "w") as fh:
        json.dump(sample, fh, indent=1, sort_keys=True)
        fh.write("\n")
    with open(os.path.join(DIR, "graphs.jsonl"), "w") as fh:
        for g in facts:
            fh.write(json.dumps(g, sort_keys=True) + "\n")
    print("wrote %s/sample.json and graphs.jsonl (%d repositories, %d graph sites)" % (DIR, len(sample["repos"]), len(facts)))


# ------------------------------------------------------------------ summary
def wilson(k, n, z=1.959964):
    if n == 0:
        return [0.0, 0.0]
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return [round(max(0.0, c - h), 4), round(min(1.0, c + h), 4)]


def load():
    with open(os.path.join(DIR, "frame.json")) as fh:
        frame = json.load(fh)
    with open(os.path.join(DIR, "sample.json")) as fh:
        sample = json.load(fh)
    with open(os.path.join(DIR, "graphs.jsonl")) as fh:
        graphs = [json.loads(l) for l in fh if l.strip()]
    return frame, sample, graphs


def summarise():
    frame, sample, graphs = load()
    out = {"seed": sample["seed"], "query": frame["query"], "retrieved_utc": frame["retrieved_utc"], "bands": {}}
    for label in [b["band"] for b in frame["bands"]] + ["ALL"]:
        repos = [r for r in sample["repos"] if label in ("ALL", r["band"])]
        gs = [g for g in graphs if label in ("ALL", g["band"]) and g["status"] != "unparsed"]
        fetched = [r for r in repos if r["fetch"] == "ok"]
        with_graph = sorted({g["repo"] for g in gs})
        n = len(with_graph)
        by_status = {}
        for g in gs:
            by_status[g["status"]] = by_status.get(g["status"], 0) + 1
        parallel = [g for g in gs if g["pairs"]]
        repo_par = {g["repo"] for g in parallel}
        repo_low = {g["repo"] for g in gs if g["status"] == "rw_plain"}
        repo_up = {g["repo"] for g in gs if g["status"] in UPPER}
        ww_plain = sum(1 for g in gs for p in g["pairs"]
                       if g.get("schema_known") and [k for k in p["ww"] if k not in g.get("reducers", [])])
        band = next((b for b in frame["bands"] if b["band"] == label), None)
        out["bands"][label] = {
            "band_size": band["band_size"] if band else sum(b["band_size"] for b in frame["bands"]),
            "frame_returned": len(band["returned"]) if band else sum(len(b["returned"]) for b in frame["bands"]),
            "repos_sampled": len(repos), "repos_fetched": len(fetched),
            "repos_with_a_graph": n, "graph_sites": len(gs),
            "graphs_unparsed": sum(1 for g in graphs if label in ("ALL", g["band"]) and g["status"] == "unparsed"),
            "graphs_by_status": dict(sorted(by_status.items())),
            "graphs_parallel": len(parallel),
            "graphs_send_fanout": sum(1 for g in gs if g.get("send_fanout")),
            "graphs_unresolved_routing": sum(1 for g in gs if g.get("unresolved_routing")),
            # the WIDE upper bound also gives up on every graph whose fan-out or routing the
            # front end could not resolve, whatever status its resolved part received
            "graphs_upper_wide": sum(1 for g in gs if g["status"] in UPPER or g.get("send_fanout") or g.get("unresolved_routing")),
            "repos_upper_wide": (lambda k: {"k": k, "share": round(k / n, 4) if n else 0.0, "wilson95": wilson(k, n)})(
                len({g["repo"] for g in gs if g["status"] in UPPER or g.get("send_fanout") or g.get("unresolved_routing")})),
            "graphs_rw_plain_lower": by_status.get("rw_plain", 0),
            "graphs_upper": sum(by_status.get(s, 0) for s in UPPER),
            "co_scheduled_ww_pairs_on_a_plain_channel": ww_plain,
            "repos_parallel": {"k": len(repo_par), "share": round(len(repo_par) / n, 4) if n else 0.0, "wilson95": wilson(len(repo_par), n)},
            "repos_rw_plain_lower": {"k": len(repo_low), "share": round(len(repo_low) / n, 4) if n else 0.0, "wilson95": wilson(len(repo_low), n)},
            "repos_upper": {"k": len(repo_up), "share": round(len(repo_up) / n, 4) if n else 0.0, "wilson95": wilson(len(repo_up), n)},
        }
    return out


def print_summary(s):
    print("\nCensus of public LangGraph repositories  (frame retrieved %s, seed %d)" % (s["retrieved_utc"], s["seed"]))
    print("query: %s\n" % s["query"])
    hdr = "  %-13s %9s %8s %8s %8s %8s %9s %22s %22s %22s"
    print(hdr % ("band", "band size", "sampled", "fetched", "w/graph", "graphs", "parallel", "repos parallel", "repos rw_plain (lower)", "repos upper"))
    for label, b in s["bands"].items():
        f = lambda x: "%d  %.1f%% [%.1f, %.1f]" % (x["k"], 100 * x["share"], 100 * x["wilson95"][0], 100 * x["wilson95"][1])  # noqa: E731
        print(hdr % (label, b["band_size"], b["repos_sampled"], b["repos_fetched"], b["repos_with_a_graph"], b["graph_sites"],
                     b["graphs_parallel"], f(b["repos_parallel"]), f(b["repos_rw_plain_lower"]), f(b["repos_upper"])))
    a = s["bands"]["ALL"]
    print("\n  graph sites by status (ALL): %s" % json.dumps(a["graphs_by_status"]))
    print("  graph-level bounds (ALL): rw_plain %d of %d (%.1f%%) <= susceptible <= %d of %d (%.1f%%)" % (
        a["graphs_rw_plain_lower"], a["graph_sites"], 100.0 * a["graphs_rw_plain_lower"] / max(a["graph_sites"], 1),
        a["graphs_upper"], a["graph_sites"], 100.0 * a["graphs_upper"] / max(a["graph_sites"], 1)))
    print("  not pair-analysed: %d sites with a Send fan-out, %d with routing or edges the front end could not resolve" % (
        a["graphs_send_fanout"], a["graphs_unresolved_routing"]))
    w = a["repos_upper_wide"]
    print("  WIDE upper bound (those sites counted as possibly susceptible too): %d of %d sites (%.1f%%); repositories %d of %d, %.1f%% [%.1f, %.1f]" % (
        a["graphs_upper_wide"], a["graph_sites"], 100.0 * a["graphs_upper_wide"] / max(a["graph_sites"], 1),
        w["k"], a["repos_with_a_graph"], 100 * w["share"], 100 * w["wilson95"][0], 100 * w["wilson95"][1]))
    print("  co-scheduled writer/writer pairs on a plain channel (would fail-stop at run time): %d" % a["co_scheduled_ww_pairs_on_a_plain_channel"])


def diff(a, b, path=""):
    if isinstance(a, dict) and isinstance(b, dict):
        out = []
        for k in sorted(set(a) | set(b)):
            out += diff(a[k], b[k], path + "/" + k) if k in a and k in b else [path + "/" + k + ": present on one side only"]
        return out
    return [] if a == b else ["%s: tracked %r, recomputed %r" % (path, a, b)]


def main():
    ap = argparse.ArgumentParser()
    for flag in ("--frame", "--summary", "--write", "--check", "--hits"):
        ap.add_argument(flag, action="store_true")
    ap.add_argument("--sample", type=int)
    ap.add_argument("--refetch", type=int)
    a = ap.parse_args()
    if a.frame:
        build_frame()
    if a.sample:
        draw_sample(a.sample)
    if a.refetch:
        _, sample, graphs = load()
        rng = random.Random(SEED + 1)
        pool = [r for r in sample["repos"] if r["fetch"] == "ok" and r["sha"]]
        bad = 0
        for r in [pool[int(rng.random() * len(pool))] for _ in range(a.refetch)]:
            status, sha, got = analyse_repo(r["full_name"], r["sha"])
            want = [{k: v for k, v in g.items() if k not in ("repo", "sha", "band")} for g in graphs if g["repo"] == r["full_name"]]
            same = status == "ok" and sorted(json.dumps(g, sort_keys=True) for g in got) == sorted(json.dumps(g, sort_keys=True) for g in want)
            bad += 0 if same else 1
            print("  %-50s @%s  %s" % (r["full_name"][:50], (r["sha"] or "")[:10], "same facts" if same else "DIFFERS (%s)" % status))
        print("refetch: %d repositories, %d differ" % (a.refetch, bad))
        return 1 if bad else 0
    if a.hits:
        _, _, graphs = load()
        for g in graphs:
            if g["status"] == "rw_plain":
                for p in g["pairs"]:
                    if p["rw_plain"]:
                        print("%s@%s:%s:%d  %s | %s  keys=%s  (%s)" % (g["repo"], (g["sha"] or "")[:10], g["path"], g.get("line", 0),
                                                                     p["a"], p["b"], ",".join(p["rw_plain"]), p["via"]))
        return 0
    if a.summary or a.write or a.check:
        s = summarise()
        if a.write:
            with open(os.path.join(DIR, "summary.json"), "w") as fh:
                json.dump(s, fh, indent=1, sort_keys=True)
                fh.write("\n")
            print("wrote %s/summary.json" % DIR)
        if a.check:
            with open(os.path.join(DIR, "summary.json")) as fh:
                bad = diff(json.load(fh), s)
            for line in bad[:12]:
                print("DISAGREES  " + line)
            print("check: %s/summary.json against the tracked facts -- %s" % (DIR, "%d disagreement(s)" % len(bad) if bad else "identical"))
            return 1 if bad else 0
        if a.summary:
            print_summary(s)
    return 0


if __name__ == "__main__":
    sys.exit(main())
