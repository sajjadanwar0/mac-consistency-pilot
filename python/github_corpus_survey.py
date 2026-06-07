#!/usr/bin/env python3
"""
Corpus occurrence survey: how many real third-party projects have hit
LangGraph's concurrent-state-update conflict (the fail-stop variant of the
A1 / write-write coordination anomaly).

Method
------
We query the GitHub issues/PRs search API for the two exact error strings
LangGraph emits when concurrent nodes update a shared state key without a
reducer:

    "INVALID_CONCURRENT_GRAPH_UPDATE"      (the error code)
    "Can receive only one value per step"  (the message text)

We report, per query, GitHub's total_count and the number of distinct
repositories, then take the union across both queries and split it into
framework-org repos (langchain-ai/*) and THIRD-PARTY repos. With a token
(env GITHUB_TOKEN) we additionally fetch star counts to characterise the
third-party set (filtering out toy/tutorial repos).

Honest scope
------------
This counts only the FAIL-STOP variant: the conflict that raises an error and
therefore gets filed in issue trackers. The *silent* A1 variant (snapshot
staleness across a fan-out, demonstrated in langgraph_prevalence.py) emits no
error and is absent from issue trackers, so this count is a LOWER BOUND on
real coordination-anomaly incidence. The query is exact-string, so paraphrased
reports are also excluded -- again a lower bound.

Run
---
    python3 github_corpus_survey.py                  # unauthenticated (rate-limited)
    GITHUB_TOKEN=ghp_... python3 github_corpus_survey.py   # + star enrichment
"""

import json, os, time, urllib.parse, urllib.request

QUERIES = ["INVALID_CONCURRENT_GRAPH_UPDATE",
           "Can receive only one value per step"]
FRAMEWORK_ORGS = {"langchain-ai"}
TOKEN = ""

def gh(url):
    headers = {"Accept": "application/vnd.github+json", "User-Agent": "lattice-survey"}
    if TOKEN:
        headers["Authorization"] = f"Bearer {TOKEN}"
    req = urllib.request.Request(url, headers=headers)
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.load(r)

def search_issues(q):
    enc = urllib.parse.quote(f'"{q}"')
    return gh(f"https://api.github.com/search/issues?q={enc}&per_page=100")

def org(repo):
    return repo.split("/")[0] if "/" in repo else repo

def main():
    union = {}
    per_query = {}
    for q in QUERIES:
        d = search_issues(q)
        repos = {}
        for it in d.get("items", []):
            ru = it.get("repository_url", "").replace("https://api.github.com/repos/", "")
            repos.setdefault(ru, 0)
            repos[ru] += 1
            union.setdefault(ru, set()).add(it.get("html_url"))
        per_query[q] = {"total_count": d.get("total_count"), "distinct_repos": len(repos)}
        print(f"[{q}] total_count={d.get('total_count')} distinct_repos={len(repos)}")
        time.sleep(8)

    third = sorted(r for r in union if org(r) not in FRAMEWORK_ORGS)
    fw = sorted(r for r in union if org(r) in FRAMEWORK_ORGS)
    print(f"\nunion distinct repos: {len(union)} "
          f"(framework-org {len(fw)}, third-party {len(third)})")

    stars = {}
    if TOKEN:
        print("\nfetching stars for third-party repos...")
        for r in third:
            try:
                stars[r] = gh("https://api.github.com/repos/" + r).get("stargazers_count")
            except Exception:
                stars[r] = None
            time.sleep(0.5)
        have = {r: s for r, s in stars.items() if s is not None}
        print(f"  >=1000 stars: {sum(1 for s in have.values() if s >= 1000)}")
        print(f"  >=100 stars : {sum(1 for s in have.values() if s >= 100)}")
        for r, s in sorted(have.items(), key=lambda x: -(x[1] or 0))[:15]:
            print(f"    {s:7d}  {r}")

    out = {"framework": "LangGraph", "queries": per_query,
           "union": {"distinct_repos": len(union),
                     "framework_org_repos": fw,
                     "third_party_repos": third,
                     "third_party_count": len(third)},
           "stars": stars}
    json.dump(out, open("langgraph_corpus_results.json", "w"), indent=2)
    print("\nwrote langgraph_corpus_results.json")

if __name__ == "__main__":
    main()