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

2026-09-19 round 36, FOUR DEFECTS OF ROUND 35, found by using it as AB did and
by reading its result as a hostile reviewer would:
  1. SURVIVORSHIP. A 40 MB tarball cap dropped 15 of the 180 sampled
     repositories -- mlflow, agentops, a 138k-star application collection: the
     largest projects, the ones most likely to run agents in parallel. A census
     that silently loses its biggest members is biased toward the answer it
     reported. The fetch now STREAMS the tarball and keeps only the .py files
     that mention a graph, so there is no size cap, only a wall-clock one, and a
     repository that still cannot be read is counted and named.
  2. A PLACEHOLDER TOKEN WAS SENT AS A CREDENTIAL. `export GITHUB_TOKEN=...`
     produced HTTP 401 and a traceback. A token that does not look like one is
     now ignored with one line of warning, and a 401 is retried without it.
  3. THE NETWORK MODES OVERWROTE TRACKED RESULTS. `--frame` and `--sample` wrote
     straight into python/langgraph_census/. They now REQUIRE `--out DIR` and
     refuse the tracked directory unless `--overwrite-tracked` is also given.
  4. NO SPLIT BY WHAT KIND OF FILE A GRAPH LIVES IN. Tests, examples, tutorials
     and docs are not deployments; the summary now reports source and auxiliary
     paths separately.
OVERRULED (round 35): MAX_TARBALL, reading GITHUB_TOKEN unchecked, and network
modes that default to the tracked directory.

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
`rw_unknown_channel` and `unknown` graphs gives the upper bound; adding every
site whose fan-out or routing the front end could not resolve gives the WIDE
upper bound. Repository-level shares carry Wilson 95% intervals, because
repositories are what was sampled.

    python3 python/langgraph_census.py --summary          # tables, from the tracked facts (offline)
    python3 python/langgraph_census.py --check            # recompute the summary; exit 1 on disagreement
    python3 python/langgraph_census.py --hits             # every rw_plain site: repo@sha:path:line, pair, keys
    python3 python/langgraph_census.py --selftest         # known-answer checks (offline)
    python3 python/langgraph_census.py --refetch 10       # NETWORK: 10 sampled repos at their pinned commit, same facts?
    python3 python/langgraph_census.py --frame --out DIR  # NETWORK: build a frame into DIR (never the tracked one)
    python3 python/langgraph_census.py --sample 60 --out DIR   # NETWORK: draw, fetch, analyse into DIR

2026-09-19 round 37, A NAMED POPULATION. The random frame answers "how is public
code written"; it cannot answer "what do graphs look like WHERE PARALLELISM IS
KNOWN TO EXIST". github_corpus_survey.py already names such a population: the
third-party repositories whose issues or pull requests quote LangGraph's
co-superstep writer/writer error, i.e. projects that demonstrably ran two
writers of one key in one superstep. `--population` turns any such list into a
one-band frame and `--all` reads every member, so the same instrument and the
same bounds apply. It is an ENRICHED sample, not a prevalence estimate, and its
results live in their own directory (python/langgraph_census_errorstring).
    python3 python/langgraph_census.py --population NAME --repos-json FILE --json-key a.b --out DIR   # offline: build the frame
    python3 python/langgraph_census.py --sample 1 --all --out DIR                                     # NETWORK: read every member
    python3 python/langgraph_census.py --summary --dir DIR

Exit codes: 0 ok, 1 a check disagreed, 4 a network failure (one line, no traceback).
Standard library only.
"""
import argparse
import json
import math
import os
import random
import re
import sys
import tarfile
import time
import urllib.error
import urllib.parse
import urllib.request

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from langgraph_static import extract  # noqa: E402

SEED = 20260919
TRACKED = "python/langgraph_census"
QUERY = "langgraph in:name,description,readme language:python"
BANDS = [("stars>=200", "stars:>=200"), ("stars 10-199", "stars:10..199"), ("stars 0-9", "stars:0..9")]
PAGES = 5
EXCLUDED_OWNERS = {"langchain-ai"}
FETCH_SECONDS = int(os.environ.get("CENSUS_FETCH_SECONDS", "900"))   # wall-clock cap per repository; there is no size cap
MAX_PY = 1024 * 1024
SKIP_PARTS = ("/site-packages/", "/.venv/", "/venv/", "/node_modules/", "/dist-packages/")
UPPER = ("rw_plain", "rw_unknown_channel", "unknown")
AUX_DIRS = {"test", "tests", "testing", "example", "examples", "tutorial", "tutorials", "doc", "docs",
            "notebook", "notebooks", "demo", "demos", "cookbook", "cookbooks", "sample", "samples",
            "fixtures", "benchmark", "benchmarks"}
TOKEN_SHAPE = re.compile(r"^(gh[pousr]_[A-Za-z0-9_]{20,}|github_pat_[A-Za-z0-9_]{20,}|[0-9a-f]{40})$")


class Network(Exception):
    pass


def usable_token(raw):
    """The token to send, or None. A placeholder is not a credential."""
    return raw if raw and TOKEN_SHAPE.match(raw.strip()) else None


_warned = []


def _get(url, accept="application/vnd.github+json", token=True):
    req = urllib.request.Request(url, headers={"Accept": accept, "User-Agent": "langgraph-census"})
    raw = os.environ.get("GITHUB_TOKEN")
    tok = usable_token(raw) if token else None
    if raw and tok is None and token and not _warned:
        _warned.append(1)
        print("  note: GITHUB_TOKEN is set but does not look like a GitHub token; ignoring it", flush=True)
    if tok and "api.github.com" in url:
        req.add_header("Authorization", "Bearer " + tok.strip())
    try:
        return urllib.request.urlopen(req, timeout=60)
    except urllib.error.HTTPError as e:
        if e.code == 401 and tok and token:
            print("  note: GitHub rejected GITHUB_TOKEN (401); retrying without it", flush=True)
            return _get(url, accept, token=False)
        raise


def path_class(path):
    """`auxiliary` for tests, examples, tutorials, docs and the like; else `source`."""
    parts = [p.lower() for p in path.replace("\\", "/").split("/")]
    stem = parts[-1]
    if any(p in AUX_DIRS for p in parts[:-1]) or stem.startswith(("test_", "example")) or stem.endswith("_test.py"):
        return "auxiliary"
    return "source"


# -------------------------------------------------------------------- frame
def build_frame(out):
    frame = {"query": QUERY, "retrieved_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
             "pages_per_band": PAGES, "excluded_owners": sorted(EXCLUDED_OWNERS), "bands": []}
    for label, qual in BANDS:
        repos, total = [], None
        for page in range(1, PAGES + 1):
            q = urllib.parse.quote(QUERY + " " + qual)
            url = "https://api.github.com/search/repositories?q=%s&sort=updated&order=desc&per_page=100&page=%d" % (q, page)
            for _ in range(6):
                try:
                    d = json.load(_get(url))
                    break
                except urllib.error.HTTPError as e:
                    if e.code in (403, 429):
                        time.sleep(20)
                        continue
                    raise Network("HTTP %d %s for %s" % (e.code, e.reason, url))
                except urllib.error.URLError as e:
                    raise Network("%s for %s" % (e.reason, url))
            else:
                raise Network("the search API kept refusing %s (rate limit)" % url)
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
    os.makedirs(out, exist_ok=True)
    with open(os.path.join(out, "frame.json"), "w") as fh:
        json.dump(frame, fh, indent=1, sort_keys=True)
        fh.write("\n")
    print("wrote %s/frame.json" % out)


def build_population(name, repos_json, json_key, out):
    """A one-band frame from a list of repositories somebody else's method produced."""
    with open(repos_json) as fh:
        d = json.load(fh)
    for part in json_key.split("."):
        d = d[part]
    repos = sorted({r for r in d if isinstance(r, str) and r.count("/") == 1 and r.split("/")[0] not in EXCLUDED_OWNERS})
    frame = {"query": "population: %s (%s, key %s)" % (name, repos_json, json_key),
             "retrieved_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "pages_per_band": 0,
             "excluded_owners": sorted(EXCLUDED_OWNERS),
             "bands": [{"band": name, "qualifier": "listed", "band_size": len(repos),
                        "returned": [{"full_name": r, "stars": -1, "branch": "HEAD"} for r in repos]}]}
    os.makedirs(out, exist_ok=True)
    with open(os.path.join(out, "frame.json"), "w") as fh:
        json.dump(frame, fh, indent=1, sort_keys=True)
        fh.write("\n")
    print("wrote %s/frame.json (%d repositories)" % (out, len(repos)))


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
    """(status, sha, {path: source}) -- the graph-bearing .py files of the tarball at
    `ref`, STREAMED: nothing but those files is ever held, so size is no limit."""
    url = "https://codeload.github.com/%s/tar.gz/%s" % (full_name, ref)
    sha, files, started = None, {}, time.time()
    try:
        resp = _get(url, accept="*/*")
        with tarfile.open(fileobj=resp, mode="r|gz") as tf:
            for m in tf:
                if sha is None:
                    sha = tf.pax_headers.get("comment")
                if time.time() - started > FETCH_SECONDS:
                    return "timeout_after_%ds" % FETCH_SECONDS, sha, {}
                if not (m.isfile() and m.name.endswith(".py")) or m.size > MAX_PY:
                    continue
                rel = m.name.split("/", 1)[1] if "/" in m.name else m.name
                if any(p in "/" + rel for p in SKIP_PARTS):
                    continue
                src = tf.extractfile(m).read().decode("utf-8", errors="replace")
                if "StateGraph" in src or "MessageGraph" in src:
                    files[rel] = src
    except (tarfile.TarError, EOFError, OSError) as e:
        return "fetch_error:%s" % type(e).__name__, sha, {}
    return "ok", sha, files


def analyse_repo(full_name, ref):
    status, sha, files = fetch_repo(full_name, ref)
    return status, sha, analyse_sources(files)


def refuses(out, overwrite):
    """True when `out` already holds results and --overwrite-tracked was not given."""
    holds = os.path.abspath(out) == os.path.abspath(TRACKED) or os.path.exists(os.path.join(out, "summary.json"))
    return holds and not overwrite


def pick(pool, n, take_all, rng):
    """The seeded draw: uniform without replacement from the name-sorted pool."""
    pool, picks = sorted(pool, key=lambda r: r["full_name"]), []
    while pool and (take_all or len(picks) < n):
        picks.append(pool.pop(int(rng.random() * len(pool))))
    return picks


def draw_sample(n, out, take_all=False):
    with open(os.path.join(out, "frame.json")) as fh:
        frame = json.load(fh)
    rng = random.Random(SEED)
    sample, facts = {"seed": SEED, "per_band": n, "repos": []}, []
    for band in frame["bands"]:
        picks = pick(band["returned"], n, take_all, rng)
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
    with open(os.path.join(out, "sample.json"), "w") as fh:
        json.dump(sample, fh, indent=1, sort_keys=True)
        fh.write("\n")
    with open(os.path.join(out, "graphs.jsonl"), "w") as fh:
        for g in facts:
            fh.write(json.dumps(g, sort_keys=True) + "\n")
    print("wrote %s/sample.json and graphs.jsonl (%d repositories, %d graph sites)" % (out, len(sample["repos"]), len(facts)))


# ------------------------------------------------------------------ summary
def wilson(k, n, z=1.959964):
    if n == 0:
        return [0.0, 0.0]
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return [round(max(0.0, c - h), 4), round(min(1.0, c + h), 4)]


def load(d):
    with open(os.path.join(d, "frame.json")) as fh:
        frame = json.load(fh)
    with open(os.path.join(d, "sample.json")) as fh:
        sample = json.load(fh)
    with open(os.path.join(d, "graphs.jsonl")) as fh:
        graphs = [json.loads(l) for l in fh if l.strip()]
    return frame, sample, graphs


def wide(g):
    return g["status"] in UPPER or g.get("send_fanout") or g.get("unresolved_routing")


def share(k, n):
    return {"k": k, "share": round(k / n, 4) if n else 0.0, "wilson95": wilson(k, n)}


def block(gs):
    """Counts for one set of graph sites; repository shares are over repositories with a site in the set."""
    n = len({g["repo"] for g in gs})
    by_status = {}
    for g in gs:
        by_status[g["status"]] = by_status.get(g["status"], 0) + 1
    return {
        "repos_with_a_graph": n, "graph_sites": len(gs),
        "graphs_by_status": dict(sorted(by_status.items())),
        "graphs_parallel": sum(1 for g in gs if g["pairs"]),
        "graphs_send_fanout": sum(1 for g in gs if g.get("send_fanout")),
        "graphs_unresolved_routing": sum(1 for g in gs if g.get("unresolved_routing")),
        "graphs_rw_plain_lower": by_status.get("rw_plain", 0),
        "graphs_upper": sum(by_status.get(s, 0) for s in UPPER),
        "graphs_upper_wide": sum(1 for g in gs if wide(g)),
        "co_scheduled_ww_pairs_on_a_plain_channel": sum(
            1 for g in gs for p in g["pairs"] if g.get("schema_known") and [k for k in p["ww"] if k not in g.get("reducers", [])]),
        "repos_parallel": share(len({g["repo"] for g in gs if g["pairs"]}), n),
        "repos_rw_plain_lower": share(len({g["repo"] for g in gs if g["status"] == "rw_plain"}), n),
        "repos_upper": share(len({g["repo"] for g in gs if g["status"] in UPPER}), n),
        "repos_upper_wide": share(len({g["repo"] for g in gs if wide(g)}), n),
    }


def summarise(d):
    frame, sample, graphs = load(d)
    out = {"seed": sample["seed"], "query": frame["query"], "retrieved_utc": frame["retrieved_utc"], "bands": {}}
    parsed = [g for g in graphs if g["status"] != "unparsed"]
    for label in [b["band"] for b in frame["bands"]] + ["ALL"]:
        repos = [r for r in sample["repos"] if label in ("ALL", r["band"])]
        band = next((b for b in frame["bands"] if b["band"] == label), None)
        b = {
            "band_size": band["band_size"] if band else sum(x["band_size"] for x in frame["bands"]),
            "frame_returned": len(band["returned"]) if band else sum(len(x["returned"]) for x in frame["bands"]),
            "repos_sampled": len(repos), "repos_fetched": sum(1 for r in repos if r["fetch"] == "ok"),
            "repos_not_fetched": sorted("%s (%s)" % (r["full_name"], r["fetch"]) for r in repos if r["fetch"] != "ok"),
            "graphs_unparsed": sum(1 for g in graphs if label in ("ALL", g["band"]) and g["status"] == "unparsed"),
        }
        b.update(block([g for g in parsed if label in ("ALL", g["band"])]))
        out["bands"][label] = b
    out["by_path_class"] = {c: block([g for g in parsed if path_class(g["path"]) == c]) for c in ("source", "auxiliary")}
    return out


def print_summary(s):
    print("\nCensus of public LangGraph repositories  (frame retrieved %s, seed %d)" % (s["retrieved_utc"], s["seed"]))
    print("query: %s\n" % s["query"])
    f = lambda x: "%d  %.1f%% [%.1f, %.1f]" % (x["k"], 100 * x["share"], 100 * x["wilson95"][0], 100 * x["wilson95"][1])  # noqa: E731
    hdr = "  %-13s %9s %8s %8s %8s %8s %9s %22s %22s %22s"
    print(hdr % ("band", "band size", "sampled", "fetched", "w/graph", "graphs", "parallel", "repos parallel", "repos rw_plain (lower)", "repos upper"))
    for label, b in s["bands"].items():
        print(hdr % (label, b["band_size"], b["repos_sampled"], b["repos_fetched"], b["repos_with_a_graph"], b["graph_sites"],
                     b["graphs_parallel"], f(b["repos_parallel"]), f(b["repos_rw_plain_lower"]), f(b["repos_upper"])))
    a = s["bands"]["ALL"]
    print("\n  graph sites by status (ALL): %s" % json.dumps(a["graphs_by_status"]))
    print("  graph-level bounds (ALL): rw_plain %d of %d (%.1f%%) <= susceptible <= %d of %d (%.1f%%)" % (
        a["graphs_rw_plain_lower"], a["graph_sites"], 100.0 * a["graphs_rw_plain_lower"] / max(a["graph_sites"], 1),
        a["graphs_upper"], a["graph_sites"], 100.0 * a["graphs_upper"] / max(a["graph_sites"], 1)))
    print("  not pair-analysed: %d sites with a Send fan-out, %d with routing or edges the front end could not resolve" % (
        a["graphs_send_fanout"], a["graphs_unresolved_routing"]))
    print("  WIDE upper bound (those sites counted as possibly susceptible too): %d of %d sites (%.1f%%); repositories %s" % (
        a["graphs_upper_wide"], a["graph_sites"], 100.0 * a["graphs_upper_wide"] / max(a["graph_sites"], 1), f(a["repos_upper_wide"])))
    print("  co-scheduled writer/writer pairs on a plain channel (would fail-stop at run time): %d" % a["co_scheduled_ww_pairs_on_a_plain_channel"])
    if a["repos_not_fetched"]:
        print("  sampled but not read: %s" % "; ".join(a["repos_not_fetched"]))
    print("\n  by kind of file (a test, example, tutorial or doc is not a deployment):")
    for c, b in s["by_path_class"].items():
        print("    %-10s %4d sites in %3d repos; parallel sites %3d; repos parallel %s; repos rw_plain %s; repos upper %s; repos wide %s" % (
            c, b["graph_sites"], b["repos_with_a_graph"], b["graphs_parallel"], f(b["repos_parallel"]),
            f(b["repos_rw_plain_lower"]), f(b["repos_upper"]), f(b["repos_upper_wide"])))


def diff(a, b, path=""):
    if isinstance(a, dict) and isinstance(b, dict):
        out = []
        for k in sorted(set(a) | set(b)):
            out += diff(a[k], b[k], path + "/" + k) if k in a and k in b else [path + "/" + k + ": present on one side only"]
        return out
    return [] if a == b else ["%s: tracked %r, recomputed %r" % (path, a, b)]


# ----------------------------------------------------------------- selftest
def selftest():
    fails = []

    def expect(name, got, want):
        if got != want:
            fails.append("%s: got %r, want %r" % (name, got, want))

    expect("a placeholder is not a token", usable_token("..."), None)
    expect("an empty token is not a token", usable_token(""), None)
    expect("a classic token is accepted", usable_token("ghp_" + "a" * 36), "ghp_" + "a" * 36)
    expect("a fine-grained token is accepted", usable_token("github_pat_" + "B" * 30) is not None, True)
    expect("wilson of 0/84 upper limit", wilson(0, 84)[1], 0.0437)
    expect("wilson of 0/0", wilson(0, 0), [0.0, 0.0])
    expect("tests are auxiliary", path_class("pkg/tests/test_graph.py"), "auxiliary")
    expect("examples are auxiliary", path_class("examples/rag/graph.py"), "auxiliary")
    expect("a test file outside tests/ is auxiliary", path_class("src/app/test_flow.py"), "auxiliary")
    expect("application code is source", path_class("src/app/workflow/graph.py"), "source")
    expect("a directory merely containing the word is source", path_class("src/contest/graph.py"), "source")
    g = lambda repo, status, **kw: dict({"repo": repo, "status": status, "pairs": kw.pop("pairs", []), "path": "a.py"}, **kw)  # noqa: E731
    b = block([g("r1", "sequential"), g("r1", "unknown", pairs=[{"ww": []}]), g("r2", "sequential", unresolved_routing=True), g("r3", "sequential")])
    expect("upper counts unknown sites", (b["graphs_upper"], b["repos_upper"]["k"]), (1, 1))
    expect("wide adds unresolved routing", (b["graphs_upper_wide"], b["repos_upper_wide"]["k"]), (2, 2))
    expect("parallel is a site with a pair", b["graphs_parallel"], 1)
    pool = [{"full_name": "o/%d" % i} for i in range(5)]
    expect("a draw of 2 takes 2", len(pick(pool, 2, False, random.Random(1))), 2)
    expect("--all takes every member", sorted(r["full_name"] for r in pick(pool, 1, True, random.Random(1))), ["o/0", "o/1", "o/2", "o/3", "o/4"])
    expect("the draw is seeded", [r["full_name"] for r in pick(pool, 3, False, random.Random(7))],
           [r["full_name"] for r in pick(list(reversed(pool)), 3, False, random.Random(7))])
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        src = os.path.join(tmp, "list.json")
        with open(src, "w") as fh:
            json.dump({"union": {"third_party": ["b/two", "a/one", "langchain-ai/langgraph", "not-a-repo", "a/one"]}}, fh)
        import contextlib
        import io
        with contextlib.redirect_stdout(io.StringIO()):
            build_population("named", src, "union.third_party", os.path.join(tmp, "out"))
        with open(os.path.join(tmp, "out", "frame.json")) as fh:
            fr = json.load(fh)
        expect("a population is one band of the listed third-party repositories, de-duplicated",
               [r["full_name"] for r in fr["bands"][0]["returned"]], ["a/one", "b/two"])
        expect("a population's band size is its length", fr["bands"][0]["band_size"], 2)
        held = os.path.join(tmp, "held")
        os.makedirs(held)
        open(os.path.join(held, "summary.json"), "w").close()
        expect("a directory holding results is refused", refuses(held, False), True)
        expect("unless overwriting is asked for", refuses(held, True), False)
        expect("an empty directory is accepted", refuses(os.path.join(tmp, "out2"), False), False)
    expect("the tracked random census is refused even if its summary were missing", refuses(TRACKED, False), True)
    for f in fails:
        print("SELFTEST FAIL  " + f)
    print("selftest: 23 checks, %d failed" % len(fails))
    return 1 if fails else 0


def main():
    ap = argparse.ArgumentParser()
    for flag in ("--frame", "--summary", "--write", "--check", "--hits", "--selftest", "--overwrite-tracked", "--all"):
        ap.add_argument(flag, action="store_true")
    ap.add_argument("--sample", type=int)
    ap.add_argument("--refetch", type=int)
    ap.add_argument("--out", help="directory the NETWORK modes write into (required for --frame and --sample)")
    ap.add_argument("--dir", default=TRACKED, help="directory the offline modes read (default: the tracked results)")
    ap.add_argument("--population", help="name of a listed population (with --repos-json, --json-key, --out)")
    ap.add_argument("--repos-json")
    ap.add_argument("--json-key", default="")
    a = ap.parse_args()
    if a.selftest:
        return selftest()
    if a.frame or a.sample or a.population:
        if not a.out:
            print("REFUSED: --frame and --sample write results; name a directory with --out DIR (the tracked results in %s are not a default)" % TRACKED)
            return 1
        if refuses(a.out, a.overwrite_tracked):
            print("REFUSED: %s holds tracked results the paper cites; add --overwrite-tracked if replacing them is what you mean" % a.out)
            return 1
        if a.population:
            if not a.repos_json:
                print("REFUSED: --population needs --repos-json FILE (and --json-key for a nested list)")
                return 1
            build_population(a.population, a.repos_json, a.json_key, a.out)
        if a.frame:
            build_frame(a.out)
        if a.sample:
            draw_sample(a.sample, a.out, take_all=a.all)
        return 0
    if a.refetch:
        _, sample, graphs = load(a.dir)
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
        _, _, graphs = load(a.dir)
        for g in graphs:
            if g["status"] == "rw_plain":
                for p in g["pairs"]:
                    if p["rw_plain"]:
                        print("%s@%s:%s:%d  [%s]  %s | %s  keys=%s  (%s)" % (g["repo"], (g["sha"] or "")[:10], g["path"], g.get("line", 0),
                                                                           path_class(g["path"]), p["a"], p["b"], ",".join(p["rw_plain"]), p["via"]))
        return 0
    if a.summary or a.write or a.check:
        s = summarise(a.dir)
        if a.write:
            with open(os.path.join(a.dir, "summary.json"), "w") as fh:
                json.dump(s, fh, indent=1, sort_keys=True)
                fh.write("\n")
            print("wrote %s/summary.json" % a.dir)
        if a.check:
            with open(os.path.join(a.dir, "summary.json")) as fh:
                bad = diff(json.load(fh), s)
            for line in bad[:12]:
                print("DISAGREES  " + line)
            print("check: %s/summary.json against the tracked facts -- %s" % (a.dir, "%d disagreement(s)" % len(bad) if bad else "identical"))
            return 1 if bad else 0
        if a.summary:
            print_summary(s)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Network as e:
        print("NETWORK: %s" % e)
        sys.exit(4)
    except urllib.error.HTTPError as e:
        print("NETWORK: HTTP %d %s for %s" % (e.code, e.reason, e.url))
        sys.exit(4)
    except urllib.error.URLError as e:
        print("NETWORK: %s" % e.reason)
        sys.exit(4)
