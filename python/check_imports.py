#!/usr/bin/env python3
"""check_imports.py -- resolve every INTRA-REPO import statically.

Why this exists.  python/prevalence_static.py carried
`from prevalence_harness import compute_layers` while compute_layers was
defined in prevalence_dynamic_run.py.  The module therefore raised
ImportError on a clean clone, and nothing caught it: check_tables.sh's MAP
gate tests that a path EXISTS, not that it loads, and the analyzer is named
by filename in the appendix.  A cited artifact rotted with every gate green.

What this checks.  For every tracked .py in the repo, every
`from M import a, b` whose M resolves to a SIBLING .py file in the same
directory: assert that each imported name is bound at module level in that
sibling.  Pure AST, no execution, no third-party imports -- so a machine
without langgraph/openai/crewai installed still runs the gate, and a probe
that legitimately requires them is not flunked for it.

FATAL vs WARN.  The gate protects CITED artifacts: a file named in a
REPRODUCE.md TABLE ROW, or a sibling such a file imports, is FATAL when its
intra-repo imports do not resolve.  A path mentioned only in prose is
documentation, not a reproducibility claim, and does not gate.  Any other file is reported as a WARNING and does not set the exit
code -- an uncited, unreferenced module that no result depends on must not
flunk a correct tree.  Both lists are printed in full; nothing is hidden.

What this does NOT check: third-party imports, star imports, names bound by
runtime tricks (globals(), setattr).  Those are reported as skipped, not as
passes.

    python3 python/check_imports.py            # whole repo
    python3 python/check_imports.py --quiet    # verdict only
"""
from __future__ import annotations
import argparse
import ast
import os
import re
import sys

SKIP_DIRS = {".git", ".idea", ".venv", "venv", "node_modules", "__pycache__",
             "verus-count-clone", "MAST", "target"}


def module_level_names(tree: ast.Module) -> set[str]:
    """Names bound at module level, including inside if/try/with bodies."""
    out: set[str] = set()

    def bind_target(t):
        if isinstance(t, ast.Name):
            out.add(t.id)
        elif isinstance(t, (ast.Tuple, ast.List)):
            for e in t.elts:
                bind_target(e)

    def walk(body):
        for node in body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                out.add(node.name)
            elif isinstance(node, ast.Assign):
                for t in node.targets:
                    bind_target(t)
            elif isinstance(node, (ast.AnnAssign, ast.AugAssign)):
                bind_target(node.target)
            elif isinstance(node, (ast.Import, ast.ImportFrom)):
                for a in node.names:
                    out.add(a.asname or a.name.split(".")[0])
            elif isinstance(node, ast.If):
                walk(node.body)
                walk(node.orelse)
            elif isinstance(node, ast.Try):
                walk(node.body)
                for h in node.handlers:
                    walk(h.body)
                walk(node.orelse)
                walk(node.finalbody)
            elif isinstance(node, (ast.With, ast.AsyncWith)):
                walk(node.body)
    walk(tree.body)
    return out


def cited_paths(root: str) -> set[str]:
    """Every .py REPRODUCE.md names, plus every sibling those files import.

    A module a cited analyzer imports is load-bearing for that analyzer even
    when REPRODUCE.md does not name it directly, so it inherits FATAL status.
    """
    rm = os.path.join(root, "REPRODUCE.md")
    seed: set[str] = set()
    if os.path.isfile(rm):
        # The MAP is the TABLE, which is exactly the rule check_tables.sh's
        # gate 2 already applies: only lines beginning with `|`. A path named
        # in prose is documentation, not a reproducibility claim, so a
        # paragraph that discusses a dead module must not promote it to
        # FATAL -- that would be a gate flunking correct work.
        for line in open(rm, encoding="utf-8").read().splitlines():
            if not line.lstrip().startswith("|"):
                continue
            for m in re.finditer(r"`([A-Za-z0-9_][A-Za-z0-9_./-]*\.py)`", line):
                q = os.path.normpath(os.path.join(root, m.group(1)))
                if os.path.isfile(q):
                    seed.add(q)
    out, frontier = set(seed), list(seed)
    while frontier:
        cur = frontier.pop()
        try:
            tree = ast.parse(open(cur, encoding="utf-8", errors="replace").read())
        except SyntaxError:
            continue
        here = os.path.dirname(cur)
        for node in ast.walk(tree):
            mods = []
            if isinstance(node, ast.ImportFrom) and node.module and not node.level:
                mods.append(node.module)
            elif isinstance(node, ast.Import):
                mods += [a.name for a in node.names]
            for mod in mods:
                sib = os.path.normpath(
                    os.path.join(here, mod.replace(".", os.sep) + ".py"))
                if os.path.isfile(sib) and sib not in out:
                    out.add(sib)
                    frontier.append(sib)
    return out


def is_cited(path: str, cited: set[str]) -> bool:
    return os.path.normpath(path) in cited


def py_files(root: str) -> list[str]:
    found = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
        for fn in filenames:
            if fn.endswith(".py"):
                found.append(os.path.join(dirpath, fn))
    return sorted(found)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args()

    cited = cited_paths(args.root)
    cache: dict[str, set[str] | None] = {}
    bad: list[str] = []
    warn: list[str] = []
    checked = skipped = 0

    for path in py_files(args.root):
        try:
            tree = ast.parse(open(path, encoding="utf-8", errors="replace").read(),
                             filename=path)
        except SyntaxError as e:
            (bad if is_cited(path, cited) else warn).append(
                f"{path}: does not parse: {e}")
            continue
        here = os.path.dirname(path)
        for node in ast.walk(tree):
            if not isinstance(node, ast.ImportFrom):
                continue
            if node.level or not node.module:
                skipped += 1
                continue
            sibling = os.path.join(here, node.module.replace(".", os.sep) + ".py")
            if not os.path.isfile(sibling):
                skipped += 1
                continue
            if sibling not in cache:
                try:
                    cache[sibling] = module_level_names(
                        ast.parse(open(sibling, encoding="utf-8",
                                       errors="replace").read(), filename=sibling))
                except SyntaxError:
                    cache[sibling] = None
            names = cache[sibling]
            if names is None:
                (bad if is_cited(path, cited) else warn).append(
                    f"{path}: sibling {sibling} does not parse")
                continue
            for alias in node.names:
                if alias.name == "*":
                    skipped += 1
                    continue
                checked += 1
                if alias.name not in names:
                    (bad if is_cited(path, cited) else warn).append(
                        f"{path}: `from {node.module} import {alias.name}` "
                        f"-- {alias.name} is not defined in "
                        f"{os.path.basename(sibling)}")

    if not args.quiet:
        print(f"  intra-repo imported names checked: {checked} "
              f"(third-party/relative/star skipped: {skipped}); "
              f"{len(cited)} file(s) cited by REPRODUCE.md")
    for w in warn:
        print(f"  warn (uncited, does not gate) - {w}")
    if bad:
        print(f"FAIL: {len(bad)} unresolved intra-repo import(s) in CITED files")
        for b in bad:
            print(f"  - {b}")
        return 1
    print(f"OK: all {checked} intra-repo imported names resolve "
          f"({len(warn)} warning(s) in uncited files)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
