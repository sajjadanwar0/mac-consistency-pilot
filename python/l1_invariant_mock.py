#!/usr/bin/env python3
"""l1_invariant_mock.py -- is the refinement invariant INDUCTIVE, and does it
imply the abstract invariants under alpha?

Round 8 (python/l1_refinement_mock.py) established that the deployed SI store
simulates the abstract SSI machine, fixed the abstraction function and the two
hypotheses. That is not yet enough to write the proof. A Verus refinement
needs an invariant Inv on the concrete state such that

    (I1)  Inv holds initially,
    (I2)  Inv is PRESERVED by every transition -- from any state satisfying
          Inv, reachable or not, and
    (I3)  Inv(c) implies all_invariants(alpha(c)).

(I2) is the one that sinks these proofs. An invariant that holds on every
reachable state but is not preserved from arbitrary Inv-states is true and
unprovable by induction: Verus discharges the step obligation from Inv alone,
with no reachability to lean on. This file checks (I2) directly by
enumerating states that satisfy Inv WITHOUT regard to reachability.

Both sides are transcribed from source:
  verus-detector/src/lib_si_concurrent.rs  SiStore::inv and its four conjuncts
  verus-detector/src/lib_ssi.rs            all_invariants and its seven

Deterministic, stdlib only, no network.
"""
from __future__ import annotations
import itertools
import sys

CELLS = [0, 1]
VALS = [1, 2]        # non-NULL values; NULL is None
NULLV = None
AGENTS = [0, 1]
MAXCLOCK = 2


# ------------------------------------------------------------------ state
class C:
    """(SiStore, outstanding snapshots). versions/trace are tuples; snaps is
    the set of snapshots callers hold, which SiStore itself does not keep."""
    __slots__ = ("versions", "clock", "trace", "snaps")

    def __init__(self, versions, clock, trace, snaps):
        self.versions = tuple(versions)   # ((cell, time, val), ...)
        self.clock = clock
        self.trace = tuple(trace)         # ((agent, rcells, rt, wcells, wt), ...)
        self.snaps = tuple(snaps)         # ((agent, rt, rcells), ...)

    def key(self):
        return (self.versions, self.clock, self.trace, self.snaps)


# --------------------------------------- concrete invariant, from the source
def inv_versions_le_clock(c):
    return all(t <= c.clock for (_, t, _) in c.versions)


def inv_trace_times(c):
    return all(rt < wt and wt <= c.clock for (_, _, rt, _, wt) in c.trace)


def inv_link(c):
    for (_, _, _, wcells, wt) in c.trace:
        for cell in wcells:
            if not any(vc == cell and vt == wt for (vc, vt, _) in c.versions):
                return False
    return True


def a1_struct(c):
    """lib_si_concurrent.rs::a1_struct -- Definition 1 minus the value and
    different-agent conjuncts."""
    tr = c.trace
    for i in range(len(tr)):
        for j in range(len(tr)):
            if i == j:
                continue
            for cell in set(tr[i][1]) & set(tr[j][3]):
                if tr[i][2] < tr[j][4] < tr[i][4]:
                    return True
    return False


def inv_snap_read_time_le_clock(c):
    """NOT in SiStore::inv -- it cannot be, because SiStore does not hold the
    snapshots. Added here as the candidate extra conjunct the refinement needs
    to discharge the abstract inv_pending_read_time_le_clock."""
    return all(rt <= c.clock for (_, rt, _) in c.snaps)


CONJUNCTS = [
    ("versions_le_clock", inv_versions_le_clock),
    ("trace_times", inv_trace_times),
    ("link", inv_link),
    ("no_a1_struct", lambda c: not a1_struct(c)),
    ("snap_read_time_le_clock", inv_snap_read_time_le_clock),
]


def Inv(c, drop=None):
    return all(f(c) for n, f in CONJUNCTS if n != drop)


# ------------------------------------------------------------------- alpha
def alpha(c):
    store, last_write = {}, {}
    for (cell, t, v) in c.versions:
        if cell not in last_write or t >= last_write[cell]:
            last_write[cell] = t
            store[cell] = v
    pending = {a: (rt, rc) for (a, rt, rc) in c.snaps}
    return {"store": store, "last_write": last_write, "pending": pending,
            "clock": c.clock, "trace": c.trace}


# -------------------------------------- abstract invariants, from the source
def all_invariants(A):
    tr = A["trace"]
    if not all(rt < wt for (_, _, rt, _, wt) in tr):
        return "inv_clock_monotone"
    if not all(wt <= A["clock"] for (_, _, _, _, wt) in tr):
        return "inv_record_writetime_le_clock"
    for (_, _, _, wcells, wt) in tr:
        for cell in wcells:
            if cell not in A["last_write"] or wt > A["last_write"][cell]:
                return "inv_last_write_dominates"
    for (_, (rt, _)) in A["pending"].items():
        if rt > A["clock"]:
            return "inv_pending_read_time_le_clock"
    for i in range(len(tr)):
        for j in range(len(tr)):
            for cell in set(tr[i][1]) & set(tr[j][3]):
                if tr[i][2] < tr[j][4] < tr[i][4]:
                    return "inv_no_intervening_write"
    return None


# -------------------------------------------------------------- transitions
def c_fresh(versions, rcells, rt):
    return all(t <= rt for (cell, t, _) in versions if cell in rcells)


def steps(c):
    """Every (label, successor) the deployed store admits."""
    out = []
    for agent in AGENTS:
        if not any(a == agent for (a, _, _) in c.snaps):
            for r in range(len(CELLS) + 1):
                for rcells in itertools.combinations(CELLS, r):
                    out.append(("begin", C(c.versions, c.clock, c.trace,
                                           c.snaps + ((agent, c.clock, rcells),))))
        snap = next(((a, rt, rc) for (a, rt, rc) in c.snaps if a == agent), None)
        if snap is None:
            continue
        _, rt, rcells = snap
        rest = tuple(x for x in c.snaps if x[0] != agent)
        if rt > c.clock or c.clock >= MAXCLOCK:
            out.append(("refuse", C(c.versions, c.clock, c.trace, rest)))
            continue
        if not c_fresh(c.versions, rcells, rt):
            out.append(("abort", C(c.versions, c.clock, c.trace, rest)))
            continue
        nc = c.clock + 1
        for w in range(len(CELLS) + 1):
            for wcells in itertools.combinations(CELLS, w):
                for vals in itertools.product(VALS, repeat=len(wcells)):
                    wv = dict(zip(wcells, vals))
                    newv = c.versions + tuple((x, nc, wv[x]) for x in wcells)
                    rec = (agent, tuple(sorted(rcells)), rt, tuple(sorted(wcells)), nc)
                    out.append(("commit", C(newv, nc, c.trace + (rec,), rest)))
    return out


# ------------------------------------------------- enumerate Inv-states
def inv_states(max_versions=2, max_trace=2, max_snaps=1, drop=None):
    """All states satisfying Inv within bounds -- NOT only reachable ones.
    That distinction is the whole point of the test."""
    vers_pool = [(cell, t, v) for cell in CELLS
                 for t in range(MAXCLOCK + 1) for v in VALS]
    recs_pool = []
    for agent in AGENTS:
        for r in range(len(CELLS) + 1):
            for rcells in itertools.combinations(CELLS, r):
                for w in range(len(CELLS) + 1):
                    for wcells in itertools.combinations(CELLS, w):
                        for rt in range(MAXCLOCK + 1):
                            for wt in range(MAXCLOCK + 1):
                                recs_pool.append((agent, rcells, rt, wcells, wt))
    snaps_pool = [(a, rt, rc) for a in AGENTS for rt in range(MAXCLOCK + 1)
                  for r in range(len(CELLS) + 1)
                  for rc in itertools.combinations(CELLS, r)]
    for nv in range(max_versions + 1):
        for versions in itertools.combinations(vers_pool, nv):
            for clock in range(MAXCLOCK + 1):
                for nt in range(max_trace + 1):
                    for trace in itertools.permutations(recs_pool, nt):
                        for ns in range(max_snaps + 1):
                            for snaps in itertools.combinations(snaps_pool, ns):
                                if len({a for (a, _, _) in snaps}) != len(snaps):
                                    continue
                                c = C(versions, clock, trace, snaps)
                                if Inv(c, drop=drop):
                                    yield c


def main() -> int:
    print("  (I3) does Inv(c) imply all_invariants(alpha(c))?")
    checked = bad3 = 0
    fails3 = {}
    for c in inv_states(max_versions=2, max_trace=1, max_snaps=1):
        checked += 1
        v = all_invariants(alpha(c))
        if v:
            bad3 += 1
            fails3.setdefault(v, c)
    print(f"      Inv-states checked: {checked}   violations: {bad3}")
    for k, c in fails3.items():
        print(f"      FAILS {k}: versions={c.versions} clock={c.clock} "
              f"trace={c.trace} snaps={c.snaps}")

    print()
    print("  (I2) is Inv INDUCTIVE -- preserved from any Inv-state, not just")
    print("       reachable ones?")
    checked = bad2 = 0
    fails2 = {}
    for c in inv_states(max_versions=2, max_trace=1, max_snaps=1):
        for (label, n) in steps(c):
            checked += 1
            if not Inv(n):
                bad2 += 1
                broken = [nm for nm, f in CONJUNCTS if not f(n)]
                fails2.setdefault((label, tuple(broken)), (c, n))
    print(f"      transitions checked: {checked}   violations: {bad2}")
    for (label, broken), (c, n) in fails2.items():
        print(f"      NOT PRESERVED by {label}: breaks {list(broken)}")
        print(f"        pre : versions={c.versions} clock={c.clock} "
              f"trace={c.trace} snaps={c.snaps}")
        print(f"        post: versions={n.versions} clock={n.clock} "
              f"trace={n.trace} snaps={n.snaps}")

    print()
    print("  TARGETED witnesses for the two conjuncts the bounded sweep below")
    print("  cannot reach (a1_struct needs two trace entries and three distinct")
    print("  times, so it is vacuous at max_trace=1):")
    w = C(versions=((0, 1, 1),), clock=2,
          trace=((0, (0,), 0, (), 2), (1, (), 0, (0,), 1)), snaps=())
    ok = (not Inv(w)) and Inv(w, drop="no_a1_struct") \
        and all_invariants(alpha(w)) == "inv_no_intervening_write"
    print(f"      no_a1_struct load-bearing: {ok}  "
          f"(witness: i reads c0@0 commits@2, j writes c0@1)")
    w2 = C(versions=((0, 2, 1),), clock=0, trace=(), snaps=())
    needed = bool(all_invariants(alpha(w2)))
    pres = all(Inv(n, drop="versions_le_clock")
               for (_, n) in steps(w2))
    print(f"      versions_le_clock needed for (I3): {needed}; preserved without "
          f"it: {pres}")
    print("        nothing in all_invariants bounds last_write by the clock, so")
    print("        this conjunct does no work for THIS refinement. It may serve")
    print("        other properties of the store; that is a separate question.")

    print()
    print("  which conjuncts are load-bearing for (I3)? drop each in turn:")
    for drop, _ in CONJUNCTS:
        hit3 = hit2 = None
        for c in inv_states(max_versions=2, max_trace=1, max_snaps=1, drop=drop):
            if hit3 is None:
                v = all_invariants(alpha(c))
                if v:
                    hit3 = (v, c)
            if hit2 is None:
                for (label, n2) in steps(c):
                    if not Inv(n2, drop=drop):
                        hit2 = (label, [nm for nm, f in CONJUNCTS
                                        if nm != drop and not f(n2)])
                        break
            if hit3 and hit2:
                break
        why = []
        if hit3:
            why.append(f"(I3) breaks {hit3[0]}")
        if hit2:
            why.append(f"(I2) not preserved by {hit2[0]}, breaking {hit2[1]}")
        print(f"      without {drop:26s} -> "
              f"{'; '.join(why) if why else 'NOTHING BREAKS -- dead weight'}")
    return 0 if (bad2 == 0 and bad3 == 0) else 1


if __name__ == "__main__":
    sys.exit(main())
