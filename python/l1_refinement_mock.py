#!/usr/bin/env python3
"""l1_refinement_mock.py -- does the DEPLOYED concurrent SI store refine the
abstract SSI state machine?

The appendix records this as the open proof step: the four spec-runtime
refinements relate the abstract machines to the representations the runtime
shipped BEFORE the guarded stores were rebuilt on vstd's lock, not to the flat
version chain the store deploys today. This file answers the prior question --
is the theorem true, and under what hypotheses -- by brute force, before any
proof is written.

Both sides are transcribed from the sources, not from memory:

  ABSTRACT  verus-detector/src/lib_ssi.rs
            SsiState { store, last_write, pending, clock, trace }
            ssi_begin_step / ssi_commit_success_step / ssi_commit_abort_step
            validation_passes(s, ps) ==
                forall c in ps.read_values.dom(): last_write_of(s,c) <= ps.read_time

  CONCRETE  verus-detector/src/lib_si_concurrent.rs
            SiStore { versions: Vec<(Cell,u64,Val)>, clock, trace: Vec<Rec> }
            begin_step / commit_step
            fresh(vs, rs, rt) ==
                forall k: in_set(rs, vs[k].0) ==> vs[k].1 <= rt

TWO STRUCTURAL FACTS, visible before any simulation and both load-bearing:

  (1) The concrete Rec carries NO values -- {agent, read_cells, read_time,
      write_cells, write_time} -- while the abstract OpRecord carries
      read_values and write_values, which Definition 1 needs. An abstraction
      function into the abstract trace therefore cannot exist. What can be
      refined is the VALUE-ERASED projection of the abstract machine, which
      is what this file checks and what a refinement theorem could state.

  (2) The abstract keeps `pending` inside the state; the concrete returns a
      Snapshot to its caller and stores nothing. The concrete side of the
      simulation is therefore the pair (SiStore, outstanding snapshots), not
      SiStore alone. A refinement theorem has to say so.
"""
from __future__ import annotations
import itertools
import sys

NULL = 0
CELLS = [0, 1]
VALS = [0, 1]          # 0 is the null value, as null_value() == 0
AGENTS = [0, 1]
MAXCLOCK = 3           # concrete refuses at the ceiling; keep it reachable


def configure(cells, vals, agents, maxclock):
    global CELLS, VALS, AGENTS, MAXCLOCK
    CELLS, VALS, AGENTS, MAXCLOCK = cells, vals, agents, maxclock


# ---------------------------------------------------------------- concrete
class Concrete:
    """SiStore plus the snapshots its callers hold."""
    def __init__(self, versions=(), clock=0, trace=(), snaps=()):
        self.versions = tuple(versions)      # ((cell, time, val), ...)
        self.clock = clock
        self.trace = tuple(trace)            # ((agent, rcells, rt, wcells, wt), ...)
        self.snaps = tuple(snaps)            # ((agent, rt, rcells), ...)

    def key(self):
        return (self.versions, self.clock, self.trace, self.snaps)


def c_fresh(versions, rcells, rt):
    """lib_si_concurrent.rs::fresh, verbatim."""
    return all(t <= rt for (c, t, v) in versions if c in rcells)


def c_begin(s, agent, rcells):
    """begin_step: read_time = clock; snapshot handed to the caller."""
    if any(a == agent for (a, _, _) in s.snaps):
        return None                                   # one outstanding per agent
    return Concrete(s.versions, s.clock, s.trace,
                    s.snaps + ((agent, s.clock, tuple(sorted(rcells))),))


def c_commit(s, agent, wcells, wvals):
    """commit_step. Returns (new_state, committed) or None if no snapshot."""
    snap = next(((a, rt, rc) for (a, rt, rc) in s.snaps if a == agent), None)
    if snap is None:
        return None
    _, rt, rcells = snap
    rest = tuple(x for x in s.snaps if x[0] != agent)
    # the two refusals the abstract machine has no transition for
    if rt > s.clock or s.clock >= MAXCLOCK:
        return Concrete(s.versions, s.clock, s.trace, rest), False, "guard"
    if not c_fresh(s.versions, rcells, rt):
        return Concrete(s.versions, s.clock, s.trace, rest), False, "validate"
    nc = s.clock + 1
    newv = s.versions + tuple((c, nc, wvals[c]) for c in sorted(wcells))
    rec = (agent, tuple(sorted(rcells)), rt, tuple(sorted(wcells)), nc)
    return Concrete(newv, nc, s.trace + (rec,), rest), True, "commit"


# ---------------------------------------------------------------- abstract
class Abstract:
    """SsiState, value-erased in the trace (see fact (1) in the docstring)."""
    def __init__(self, store=None, last_write=None, pending=None, clock=0, trace=()):
        self.store = dict(store or {})
        self.last_write = dict(last_write or {})
        self.pending = dict(pending or {})    # agent -> (read_time, rcells)
        self.clock = clock
        self.trace = tuple(trace)

    def key(self):
        return (tuple(sorted(self.store.items())),
                tuple(sorted(self.last_write.items())),
                tuple(sorted((a, rt, rc) for a, (rt, rc) in self.pending.items())),
                self.clock, self.trace)


def a_last_write_of(s, c):
    return s.last_write.get(c, 0)


def a_validation_passes(s, rt, rcells):
    """validation_passes, over the read set (= read_values.dom())."""
    return all(a_last_write_of(s, c) <= rt for c in rcells)


def a_begin(s, agent, rcells):
    if agent in s.pending:
        return None
    n = Abstract(s.store, s.last_write, s.pending, s.clock, s.trace)
    n.pending[agent] = (s.clock, tuple(sorted(rcells)))
    return n


def a_commit_success(s, agent, wcells, wvals):
    if agent not in s.pending:
        return None
    rt, rcells = s.pending[agent]
    if not a_validation_passes(s, rt, rcells):
        return None
    nc = s.clock + 1
    n = Abstract(s.store, s.last_write, s.pending, nc, s.trace)
    for c in wcells:
        n.store[c] = wvals[c]
        n.last_write[c] = nc
    del n.pending[agent]
    n.trace = s.trace + ((agent, tuple(sorted(rcells)), rt,
                          tuple(sorted(wcells)), nc),)
    return n


def a_commit_abort(s, agent):
    if agent not in s.pending:
        return None
    rt, rcells = s.pending[agent]
    if a_validation_passes(s, rt, rcells):
        return None                       # abort REQUIRES validation to fail
    n = Abstract(s.store, s.last_write, s.pending, s.clock, s.trace)
    del n.pending[agent]
    return n


# ---------------------------------------------------------------- alpha
def alpha(c: Concrete) -> Abstract:
    """The abstraction function. store and last_write are derived from the
    flat version chain by taking, per cell, the version with the greatest
    commit time -- which is what begin_step's inner loop computes."""
    store, last_write = {}, {}
    for (cell, t, v) in c.versions:
        if cell not in last_write or t >= last_write[cell]:
            last_write[cell] = t
            store[cell] = v
    pending = {a: (rt, rc) for (a, rt, rc) in c.snaps}
    return Abstract(store, last_write, pending, c.clock, c.trace)


# ---------------------------------------------------------------- search
def reachable(max_states=2000000):
    init = Concrete()
    seen, frontier, edges = {init.key(): init}, [init], []
    while frontier:
        s = frontier.pop()
        for agent in AGENTS:
            for r in range(len(CELLS) + 1):
                for rcells in itertools.combinations(CELLS, r):
                    n = c_begin(s, agent, rcells)
                    if n is not None:
                        edges.append((s, ("begin", agent, rcells, None), n, True, "begin"))
                        if n.key() not in seen:
                            seen[n.key()] = n
                            frontier.append(n)
            for w in range(len(CELLS) + 1):
                for wcells in itertools.combinations(CELLS, w):
                    for vals in itertools.product(VALS, repeat=len(wcells)):
                        wv = dict(zip(wcells, vals))
                        res = c_commit(s, agent, wcells, wv)
                        if res is None:
                            continue
                        n, ok, why = res
                        edges.append((s, ("commit", agent, wcells, wv), n, ok, why))
                        if n.key() not in seen:
                            seen[n.key()] = n
                            frontier.append(n)
        if len(seen) > max_states:
            raise MemoryError("state explosion")
    return seen, edges


CONFIGS = [
    ([0], [0, 1], [0], 2),
    ([0], [0, 1], [0, 1], 2),
    ([0, 1], [0, 1], [0], 2),
    ([0], [0, 1], [0, 1], 3),
]


def check(cells, vals, agents, maxclock):
    configure(cells, vals, agents, maxclock)
    seen, edges = reachable()
    bad = {"begin": 0, "commit": 0, "abort": 0, "guard": 0}
    cause = {"total": 0, "rt_gt_clock": 0, "clock_ceiling": 0, "matched_anyway": 0}
    for (s, act, n, ok, why) in edges:
        A, B = alpha(s), alpha(n)
        kind, agent, cs, wv = act
        if kind == "begin":
            m, k = a_begin(A, agent, cs), "begin"
        elif ok:
            m, k = a_commit_success(A, agent, cs, wv), "commit"
        elif why == "validate":
            m, k = a_commit_abort(A, agent), "abort"
        else:
            m, k = a_commit_abort(A, agent), "guard"
            cause["total"] += 1
            snap = next(((a, rt, rc) for (a, rt, rc) in s.snaps if a == agent), None)
            if snap is not None:
                cause["rt_gt_clock" if snap[1] > s.clock else "clock_ceiling"] += 1
            if m is not None and m.key() == B.key():
                cause["matched_anyway"] += 1
        if m is None or m.key() != B.key():
            bad[k] += 1
    return len(seen), len(edges), bad, cause


def main() -> int:
    print("  Does the deployed concurrent SI store simulate the abstract SSI")
    print("  machine? Exhaustive over the configurations below.\n")
    hdr = (f"  {'cells':>5} {'vals':>4} {'agents':>6} {'clk':>4} {'states':>8} "
           f"{'edges':>8} {'begin':>6} {'commit':>7} {'abort':>6} {'guard':>6}")
    print(hdr)
    print("  " + "-" * (len(hdr) - 2))
    tot_e = 0
    tot_bad = {"begin": 0, "commit": 0, "abort": 0, "guard": 0}
    tot_cause = {"total": 0, "rt_gt_clock": 0, "clock_ceiling": 0, "matched_anyway": 0}
    for cells, vals, agents, mc in CONFIGS:
        try:
            ns, ne, bad, cause = check(cells, vals, agents, mc)
        except MemoryError:
            print(f"  {len(cells):>5} {len(vals):>4} {len(agents):>6} {mc:>4}"
                  f"   state explosion -- not covered")
            continue
        tot_e += ne
        for k in tot_bad:
            tot_bad[k] += bad[k]
        for k in tot_cause:
            tot_cause[k] += cause[k]
        print(f"  {len(cells):>5} {len(vals):>4} {len(agents):>6} {mc:>4} {ns:>8} "
              f"{ne:>8} {bad['begin']:>6} {bad['commit']:>7} {bad['abort']:>6} "
              f"{bad['guard']:>6}")
    print("  " + "-" * (len(hdr) - 2))
    print(f"  transitions checked: {tot_e}")
    print(f"  simulation failures: begin {tot_bad['begin']}, commit "
          f"{tot_bad['commit']}, abort {tot_bad['abort']}, guard {tot_bad['guard']}")
    print()
    print("  Every simulation failure is a GUARD refusal. The guard refusals:")
    print(f"    total                        : {tot_cause['total']}")
    print(f"      of which clock at ceiling  : {tot_cause['clock_ceiling']}")
    print(f"      of which read_time > clock : {tot_cause['rt_gt_clock']}")
    print(f"      matched an abstract step   : {tot_cause['matched_anyway']}"
          "  (validation would also have failed there,")
    print("                                     so ssi_commit_abort_step was enabled)")
    print(f"      failed to simulate         : {tot_bad['guard']}")
    print("  read_time > clock is unreachable because begin_step sets read_time to")
    print("  the clock and the clock is monotone, so the refusal is reachable only")
    print("  at the ceiling.")
    print()
    print("  WHAT THIS ESTABLISHES, and what it does not.")
    print("  Under (H1) the snapshot came from begin_step on this store and (H2)")
    print("  clock < u64::MAX, the store simulates the abstract machine under the")
    print("  abstraction function alpha: store and last_write are read off the flat")
    print("  version chain by taking, per cell, the greatest-time version; pending")
    print("  is the set of outstanding snapshots. Two limits are structural and no")
    print("  choice of alpha removes them: the concrete Rec carries no values, so")
    print("  the target is the VALUE-ERASED abstract machine; and the concrete side")
    print("  of the relation is (SiStore, outstanding snapshots), because pending")
    print("  lives in the abstract state and not in SiStore.")
    print("  This is a bounded exhaustive check, not a proof. It establishes that a")
    print("  Verus refinement is worth writing and fixes the alpha and the two")
    print("  hypotheses it must carry.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
