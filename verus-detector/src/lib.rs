// Verus proof: pessimistic-locking runtime produces traces satisfying !A_1.
//
// SCOPE
//   Sequential safety: under any sequential interleaving of begin/commit
//   calls by N agents, the pessimistic-locking runtime produces an
//   OpRecord trace that does not satisfy A_1.
//
// TARGET STATUS
//   Zero `assume` placeholders, zero `external_body` axioms in proof bodies.
//
// MODEL CHANGES vs. earlier draft
//   1. `inv_lock_unique` strengthened from a one-way implication to a
//      partition (locks <-> holds biconditional). The runtime maintains
//      this property by construction; we make the invariant explicit so
//      L3's `inv_pending_implies_locks` preservation closes.
//   2. Two finiteness invariants added (`inv_holds_finite`,
//      `inv_pending_snapshot_finite`) so `Set::to_seq()` and
//      `Map::dom().to_seq()` invocations are well-formed.
//   3. `commit_step` releases agent's locks via the direct recursive
//      spec `locks_with_released` instead of `Set::fold`. Semantically
//      equivalent; eliminates the need for a Set::fold axiom.
//   4. `begin_step`'s fold_left expressions are replaced by recursive
//      shadow specs (`locks_with_acquired`, `holds_set_with_acquired`,
//      `snapshot_built`). These match Verus's drop_last/last fold form
//      so they unfold definitionally.

#![allow(unused_imports)]
use vstd::prelude::*;

verus! {

// =====================================================================
// Section 1: Abstract trace model
// =====================================================================

pub type CellId = int;
pub type AgentId = int;
pub type Value = int;
pub type Time = int;

pub open spec fn null_value() -> Value { 0 }

pub struct OpRecord {
    pub agent: AgentId,
    pub read_set: Set<CellId>,
    pub read_values: Map<CellId, Value>,
    pub read_time: Time,
    pub write_set: Set<CellId>,
    pub write_values: Map<CellId, Value>,
    pub write_time: Time,
}

pub open spec fn a1(h: Seq<OpRecord>) -> bool {
    exists |i: int, j: int, c: CellId|
        0 <= i < h.len() && 0 <= j < h.len() && i != j
        && #[trigger] h[i].read_set.contains(c)
        && #[trigger] h[j].write_set.contains(c)
        && h[i].read_time < h[j].write_time
        && h[j].write_time < h[i].write_time
        && h[i].read_values.contains_key(c)
        && h[j].write_values.contains_key(c)
        && h[i].read_values[c] != h[j].write_values[c]
}

// =====================================================================
// Section 2: Runtime state and recursive shadow specs
// =====================================================================

pub struct RuntimeState {
    pub cells: Map<CellId, Value>,
    pub locks: Map<CellId, AgentId>,
    pub holds: Map<AgentId, Set<CellId>>,
    pub pending_snapshot: Map<AgentId, (Map<CellId, Value>, Time)>,
    pub clock: Time,
    pub trace: Seq<OpRecord>,
}

pub open spec fn init_state() -> RuntimeState {
    RuntimeState {
        cells: Map::<CellId, Value>::empty(),
        locks: Map::<CellId, AgentId>::empty(),
        holds: Map::<AgentId, Set<CellId>>::empty(),
        pending_snapshot: Map::<AgentId, (Map<CellId, Value>, Time)>::empty(),
        clock: 0,
        trace: Seq::<OpRecord>::empty(),
    }
}

// ---- Recursive shadow specs ------------------------------------------

pub open spec fn locks_with_acquired(
    base: Map<CellId, AgentId>,
    cells: Seq<CellId>,
    agent: AgentId,
) -> Map<CellId, AgentId>
    decreases cells.len()
{
    if cells.len() == 0 {
        base
    } else {
        locks_with_acquired(base, cells.drop_last(), agent).insert(cells.last(), agent)
    }
}

pub open spec fn holds_set_with_acquired(
    base: Set<CellId>,
    cells: Seq<CellId>,
) -> Set<CellId>
    decreases cells.len()
{
    if cells.len() == 0 {
        base
    } else {
        holds_set_with_acquired(base, cells.drop_last()).insert(cells.last())
    }
}

pub open spec fn snapshot_built(
    s_cells: Map<CellId, Value>,
    cells: Seq<CellId>,
) -> Map<CellId, Value>
    decreases cells.len()
{
    if cells.len() == 0 {
        Map::<CellId, Value>::empty()
    } else {
        snapshot_built(s_cells, cells.drop_last())
            .insert(
                cells.last(),
                if s_cells.contains_key(cells.last()) { s_cells[cells.last()] } else { null_value() }
            )
    }
}

// Direct spec: "the lock map restricted to keys not in `to_remove`."
pub open spec fn locks_with_released(
    base: Map<CellId, AgentId>,
    to_remove: Set<CellId>,
) -> Map<CellId, AgentId> {
    Map::new(
        |c: CellId| base.contains_key(c) && !to_remove.contains(c),
        |c: CellId| base[c],
    )
}

// ---- Properties of the recursive shadows -----------------------------

pub proof fn lemma_locks_with_acquired_in(
    base: Map<CellId, AgentId>,
    cells: Seq<CellId>,
    agent: AgentId,
    c: CellId,
)
    requires cells.contains(c)
    ensures
        locks_with_acquired(base, cells, agent).contains_key(c),
        locks_with_acquired(base, cells, agent)[c] == agent,
    decreases cells.len()
{
    if cells.len() == 0 {
        assert(false);
    } else {
        let last = cells.last();
        let pref = cells.drop_last();
        if c == last {
        } else {
            assert(pref.contains(c)) by {
                let k = choose |k: int| 0 <= k < cells.len() && cells[k] == c;
                assert(k != cells.len() - 1);
                assert(0 <= k < pref.len() && pref[k] == c);
            };
            lemma_locks_with_acquired_in(base, pref, agent, c);
        }
    }
}

pub proof fn lemma_locks_with_acquired_outside(
    base: Map<CellId, AgentId>,
    cells: Seq<CellId>,
    agent: AgentId,
    c: CellId,
)
    requires !cells.contains(c)
    ensures
        locks_with_acquired(base, cells, agent).contains_key(c) == base.contains_key(c),
        base.contains_key(c) ==> locks_with_acquired(base, cells, agent)[c] == base[c],
    decreases cells.len()
{
    if cells.len() == 0 {
    } else {
        let last = cells.last();
        let pref = cells.drop_last();
        assert(c != last);
        assert(!pref.contains(c)) by {
            if pref.contains(c) {
                let k = choose |k: int| 0 <= k < pref.len() && pref[k] == c;
                assert(cells[k] == c);
            }
        };
        lemma_locks_with_acquired_outside(base, pref, agent, c);
    }
}

pub proof fn lemma_holds_set_with_acquired_in(
    base: Set<CellId>,
    cells: Seq<CellId>,
    c: CellId,
)
    requires cells.contains(c) || base.contains(c)
    ensures holds_set_with_acquired(base, cells).contains(c),
    decreases cells.len()
{
    if cells.len() == 0 {
    } else {
        let last = cells.last();
        let pref = cells.drop_last();
        if c == last {
        } else if base.contains(c) {
            lemma_holds_set_with_acquired_in(base, pref, c);
        } else {
            assert(pref.contains(c)) by {
                let k = choose |k: int| 0 <= k < cells.len() && cells[k] == c;
                assert(k != cells.len() - 1);
                assert(0 <= k < pref.len() && pref[k] == c);
            };
            lemma_holds_set_with_acquired_in(base, pref, c);
        }
    }
}

pub proof fn lemma_holds_set_acquired_outside(
    base: Set<CellId>,
    cells: Seq<CellId>,
    c: CellId,
)
    requires !cells.contains(c)
    ensures holds_set_with_acquired(base, cells).contains(c) == base.contains(c),
    decreases cells.len()
{
    if cells.len() == 0 {
    } else {
        let last = cells.last();
        let pref = cells.drop_last();
        assert(c != last);
        assert(!pref.contains(c)) by {
            if pref.contains(c) {
                let k = choose |k: int| 0 <= k < pref.len() && pref[k] == c;
                assert(cells[k] == c);
            }
        };
        lemma_holds_set_acquired_outside(base, pref, c);
    }
}

pub proof fn lemma_holds_set_with_acquired_finite(
    base: Set<CellId>,
    cells: Seq<CellId>,
)
    requires base.finite()
    ensures holds_set_with_acquired(base, cells).finite(),
    decreases cells.len()
{
    if cells.len() == 0 {
    } else {
        lemma_holds_set_with_acquired_finite(base, cells.drop_last());
    }
}

pub proof fn lemma_snapshot_built_dom(
    s_cells: Map<CellId, Value>,
    cells: Seq<CellId>,
    c: CellId,
)
    ensures snapshot_built(s_cells, cells).dom().contains(c) == cells.contains(c)
    decreases cells.len()
{
    if cells.len() == 0 {
    } else {
        let last = cells.last();
        let pref = cells.drop_last();
        lemma_snapshot_built_dom(s_cells, pref, c);
        if c == last {
            assert(cells[cells.len() - 1] == last);
        } else {
            if cells.contains(c) {
                let k = choose |k: int| 0 <= k < cells.len() && cells[k] == c;
                assert(k != cells.len() - 1);
                assert(0 <= k < pref.len() && pref[k] == c);
            }
            if pref.contains(c) {
                let k = choose |k: int| 0 <= k < pref.len() && pref[k] == c;
                assert(cells[k] == c);
            }
        }
    }
}

pub proof fn lemma_snapshot_built_finite(
    s_cells: Map<CellId, Value>,
    cells: Seq<CellId>,
)
    ensures snapshot_built(s_cells, cells).dom().finite()
    decreases cells.len()
{
    if cells.len() == 0 {
    } else {
        lemma_snapshot_built_finite(s_cells, cells.drop_last());
    }
}

// =====================================================================
// Section 3: Transitions
// =====================================================================

pub open spec fn can_begin(s: &RuntimeState, agent: AgentId, cells: Seq<CellId>) -> bool {
    forall |c: CellId| #[trigger] cells.contains(c) ==>
        (!s.locks.contains_key(c) || s.locks[c] == agent)
}

pub open spec fn begin_step(
    s: &RuntimeState,
    agent: AgentId,
    cells: Seq<CellId>,
) -> RuntimeState
    recommends can_begin(s, agent, cells)
{
    let new_locks = locks_with_acquired(s.locks, cells, agent);
    let base_holds = if s.holds.contains_key(agent) {
        s.holds[agent]
    } else {
        Set::<CellId>::empty()
    };
    let new_holds_set = holds_set_with_acquired(base_holds, cells);
    let new_holds = s.holds.insert(agent, new_holds_set);
    let snapshot = snapshot_built(s.cells, cells);
    RuntimeState {
        locks: new_locks,
        holds: new_holds,
        pending_snapshot: s.pending_snapshot.insert(agent, (snapshot, s.clock)),
        ..*s
    }
}

pub open spec fn can_commit(
    s: &RuntimeState,
    agent: AgentId,
    write_kv: Map<CellId, Value>,
) -> bool {
    s.pending_snapshot.contains_key(agent)
    && write_kv.dom().finite()
    && (forall |c: CellId| #[trigger] write_kv.contains_key(c) ==>
        (s.locks.contains_key(c) && s.locks[c] == agent))
}

pub open spec fn commit_step(
    s: &RuntimeState,
    agent: AgentId,
    write_kv: Map<CellId, Value>,
) -> RuntimeState
    recommends can_commit(s, agent, write_kv)
{
    let pending = s.pending_snapshot[agent];
    let snap = pending.0;
    let rt = pending.1;
    let read_set = snap.dom();
    let write_set = write_kv.dom();
    let new_clock = s.clock + 1;
    let record = OpRecord {
        agent: agent,
        read_set: read_set,
        read_values: snap,
        read_time: rt,
        write_set: write_set,
        write_values: write_kv,
        write_time: new_clock,
    };
    let new_cells = Map::new(
        |c: CellId| s.cells.contains_key(c) || write_kv.contains_key(c),
        |c: CellId| if write_kv.contains_key(c) { write_kv[c] } else { s.cells[c] },
    );
    let agent_locks = if s.holds.contains_key(agent) {
        s.holds[agent]
    } else {
        Set::<CellId>::empty()
    };
    let new_locks = locks_with_released(s.locks, agent_locks);
    RuntimeState {
        cells: new_cells,
        locks: new_locks,
        holds: s.holds.insert(agent, Set::<CellId>::empty()),
        pending_snapshot: s.pending_snapshot.remove(agent),
        clock: new_clock,
        trace: s.trace.push(record),
    }
}

// =====================================================================
// Section 4: Invariants
// =====================================================================

pub open spec fn inv_clock_monotone(s: &RuntimeState) -> bool {
    forall |i: int| 0 <= i < s.trace.len() ==>
        #[trigger] s.trace[i].write_time <= s.clock
        && (forall |k: int| 0 <= k < i ==>
            #[trigger] s.trace[k].write_time < s.trace[i].write_time)
}

// Two separate invariants forming the partition. Splitting avoids a
// conjunction-step on the `assert(inv_lock_unique(...))` form that Verus
// has trouble closing even when both forall instances have been proven.

// Four single-conjunct invariants forming the lock-holds partition.
// Single-conjunct foralls are more reliably matched by Verus's SMT than
// foralls whose body contains a conjunction.

// Forward direction, conjunct 1: s.locks[c]'s agent is registered in holds.
pub open spec fn inv_lock_unique_a1(s: &RuntimeState) -> bool {
    forall |c: CellId| #[trigger] s.locks.contains_key(c) ==>
        s.holds.contains_key(s.locks[c])
}

// Forward direction, conjunct 2: that agent's holds set contains c.
pub open spec fn inv_lock_unique_a2(s: &RuntimeState) -> bool {
    forall |c: CellId| #[trigger] s.locks.contains_key(c) ==>
        s.holds[s.locks[c]].contains(c)
}

// Reverse direction, conjunct 1: if any agent holds c, then s.locks[c] exists.
pub open spec fn inv_lock_unique_b1(s: &RuntimeState) -> bool {
    forall |a: AgentId, c: CellId|
        s.holds.contains_key(a) && #[trigger] s.holds[a].contains(c) ==>
            s.locks.contains_key(c)
}

// Reverse direction, conjunct 2: that agent equals s.locks[c].
pub open spec fn inv_lock_unique_b2(s: &RuntimeState) -> bool {
    forall |a: AgentId, c: CellId|
        s.holds.contains_key(a) && #[trigger] s.holds[a].contains(c) ==>
            s.locks[c] == a
}

// Helper accessors that bypass trigger fragility.
pub proof fn lemma_inv_lock_unique_lookup(s: &RuntimeState, c: CellId)
    requires
        inv_lock_unique_a1(s), inv_lock_unique_a2(s),
        s.locks.contains_key(c),
    ensures
        s.holds.contains_key(s.locks[c]),
        s.holds[s.locks[c]].contains(c),
{
}

pub proof fn lemma_inv_lock_unique_partition(s: &RuntimeState, a: AgentId, c: CellId)
    requires
        inv_lock_unique_b1(s), inv_lock_unique_b2(s),
        s.holds.contains_key(a), s.holds[a].contains(c),
    ensures
        s.locks.contains_key(c),
        s.locks[c] == a,
{
}

pub open spec fn inv_pending_implies_locks(s: &RuntimeState) -> bool {
    forall |agent: AgentId|
        s.pending_snapshot.contains_key(agent) ==>
        (forall |c: CellId| #[trigger] s.pending_snapshot[agent].0.dom().contains(c) ==>
            (s.locks.contains_key(c) && s.locks[c] == agent))
}

pub open spec fn inv_records_held_locks_through_commit(s: &RuntimeState) -> bool {
    forall |i: int, c: CellId|
        0 <= i < s.trace.len() &&
        #[trigger] s.trace[i].read_set.contains(c) ==>
            (forall |j: int| 0 <= j < s.trace.len() && j != i &&
                #[trigger] s.trace[j].write_set.contains(c) ==>
                (s.trace[j].write_time <= s.trace[i].read_time
                 || s.trace[j].write_time >= s.trace[i].write_time))
}

pub open spec fn inv_pending_separates_old_writes(s: &RuntimeState) -> bool {
    forall |a: AgentId, c: CellId|
        s.pending_snapshot.contains_key(a)
        && #[trigger] s.pending_snapshot[a].0.dom().contains(c) ==>
            forall |j: int| 0 <= j < s.trace.len()
                && #[trigger] s.trace[j].write_set.contains(c) ==>
                s.trace[j].write_time <= s.pending_snapshot[a].1
}

pub open spec fn inv_holds_finite(s: &RuntimeState) -> bool {
    forall |a: AgentId| #[trigger] s.holds.contains_key(a) ==> s.holds[a].finite()
}

pub open spec fn inv_pending_snapshot_finite(s: &RuntimeState) -> bool {
    forall |a: AgentId| #[trigger] s.pending_snapshot.contains_key(a) ==>
        s.pending_snapshot[a].0.dom().finite()
}

pub open spec fn all_invariants(s: &RuntimeState) -> bool {
    inv_clock_monotone(s)
    && inv_lock_unique_a1(s)
    && inv_lock_unique_a2(s)
    && inv_lock_unique_b1(s)
    && inv_lock_unique_b2(s)
    && inv_pending_implies_locks(s)
    && inv_pending_separates_old_writes(s)
    && inv_records_held_locks_through_commit(s)
    && inv_holds_finite(s)
    && inv_pending_snapshot_finite(s)
}

// =====================================================================
// Section 5: Safety theorem (single-state form)
// =====================================================================

pub proof fn pessimistic_no_a1(s: &RuntimeState)
    requires inv_records_held_locks_through_commit(s)
    ensures !a1(s.trace)
{
    if a1(s.trace) {
        let witness = choose |i: int, j: int, c: CellId|
            #![auto]
            0 <= i < s.trace.len() && 0 <= j < s.trace.len() && i != j
            && s.trace[i].read_set.contains(c)
            && s.trace[j].write_set.contains(c)
            && s.trace[i].read_time < s.trace[j].write_time
            && s.trace[j].write_time < s.trace[i].write_time
            && s.trace[i].read_values.contains_key(c)
            && s.trace[j].write_values.contains_key(c)
            && s.trace[i].read_values[c] != s.trace[j].write_values[c];
        let i = witness.0;
        let j = witness.1;
        let c = witness.2;

        assert(s.trace[j].write_time <= s.trace[i].read_time
               || s.trace[j].write_time >= s.trace[i].write_time);
        assert(false);
    }
}

// =====================================================================
// Section 6: Inductive lemmas
// =====================================================================

pub proof fn lemma_init_invariants()
    ensures all_invariants(&init_state())
{
    let s0 = init_state();
    assert(s0.trace.len() == 0);
    assert(s0.locks.dom() =~= Set::<CellId>::empty());
    assert(s0.holds.dom() =~= Set::<AgentId>::empty());
    assert(s0.pending_snapshot.dom() =~= Set::<AgentId>::empty());

    assert(inv_clock_monotone(&s0));
    assert(inv_lock_unique_a1(&s0));
    assert(inv_lock_unique_a2(&s0));
    assert(inv_lock_unique_b1(&s0));
    assert(inv_lock_unique_b2(&s0));
    assert(inv_pending_implies_locks(&s0));
    assert(inv_pending_separates_old_writes(&s0));
    assert(inv_records_held_locks_through_commit(&s0));
    assert(inv_holds_finite(&s0));
    assert(inv_pending_snapshot_finite(&s0));
}

// ---- L2: begin preserves all invariants ------------------------------

// Extracted: inv_lock_unique_a1 + a2 (forward direction) preservation under begin.
pub proof fn lemma_begin_preserves_lock_unique_a(
    s: &RuntimeState,
    agent: AgentId,
    cells: Seq<CellId>,
)
    requires
        all_invariants(s),
        can_begin(s, agent, cells),
    ensures
        inv_lock_unique_a1(&begin_step(s, agent, cells)),
        inv_lock_unique_a2(&begin_step(s, agent, cells)),
{
    let s_new = begin_step(s, agent, cells);
    let base_holds = if s.holds.contains_key(agent) {
        s.holds[agent]
    } else {
        Set::<CellId>::empty()
    };
    let new_holds_set = holds_set_with_acquired(base_holds, cells);

    assert(s_new.locks == locks_with_acquired(s.locks, cells, agent));
    assert(s_new.holds == s.holds.insert(agent, new_holds_set));

    // a1: contains_key part
    assert forall |c: CellId| s_new.locks.contains_key(c) implies
        s_new.holds.contains_key(s_new.locks[c]) by
    {
        if cells.contains(c) {
            lemma_locks_with_acquired_in(s.locks, cells, agent, c);
        } else {
            lemma_locks_with_acquired_outside(s.locks, cells, agent, c);
            let holder = s.locks[c];
            lemma_inv_lock_unique_lookup(s, c);
        }
    };

    // a2: holds.contains part
    assert forall |c: CellId| s_new.locks.contains_key(c) implies
        s_new.holds[s_new.locks[c]].contains(c) by
    {
        if cells.contains(c) {
            lemma_locks_with_acquired_in(s.locks, cells, agent, c);
            assert(s_new.locks[c] == agent);
            assert(s_new.holds[agent] == new_holds_set);
            lemma_holds_set_with_acquired_in(base_holds, cells, c);
        } else {
            lemma_locks_with_acquired_outside(s.locks, cells, agent, c);
            let holder = s.locks[c];
            lemma_inv_lock_unique_lookup(s, c);
            assert(s.holds[holder].contains(c));
            if holder == agent {
                assert(s_new.holds[agent] == new_holds_set);
                lemma_holds_set_with_acquired_in(base_holds, cells, c);
            } else {
                assert(s_new.holds[holder] == s.holds[holder]);
            }
        }
    };
}

// Extracted: inv_lock_unique_b1 + b2 (reverse direction / partition) preservation under begin.
pub proof fn lemma_begin_preserves_lock_unique_b(
    s: &RuntimeState,
    agent: AgentId,
    cells: Seq<CellId>,
)
    requires
        all_invariants(s),
        can_begin(s, agent, cells),
    ensures
        inv_lock_unique_b1(&begin_step(s, agent, cells)),
        inv_lock_unique_b2(&begin_step(s, agent, cells)),
{
    let s_new = begin_step(s, agent, cells);
    let base_holds = if s.holds.contains_key(agent) {
        s.holds[agent]
    } else {
        Set::<CellId>::empty()
    };
    let new_holds_set = holds_set_with_acquired(base_holds, cells);

    assert(s_new.locks == locks_with_acquired(s.locks, cells, agent));
    assert(s_new.holds == s.holds.insert(agent, new_holds_set));

    // b1: contains_key part
    assert forall |a: AgentId, c: CellId|
        s_new.holds.contains_key(a) && #[trigger] s_new.holds[a].contains(c) implies
            s_new.locks.contains_key(c) by
    {
        if a == agent {
            assert(s_new.holds[agent] == new_holds_set);
            if cells.contains(c) {
                lemma_locks_with_acquired_in(s.locks, cells, agent, c);
            } else {
                lemma_holds_set_acquired_outside(base_holds, cells, c);
                assert(base_holds.contains(c));
                if s.holds.contains_key(agent) {
                    assert(base_holds == s.holds[agent]);
                    assert(s.holds[agent].contains(c));
                    lemma_inv_lock_unique_partition(s, agent, c);
                    lemma_locks_with_acquired_outside(s.locks, cells, agent, c);
                } else {
                    assert(base_holds == Set::<CellId>::empty());
                    assert(false);
                }
            }
        } else {
            assert(s_new.holds[a] == s.holds[a]);
            lemma_inv_lock_unique_partition(s, a, c);
            if cells.contains(c) {
                assert(false);
            } else {
                lemma_locks_with_acquired_outside(s.locks, cells, agent, c);
            }
        }
    };

    // b2: equality part
    assert forall |a: AgentId, c: CellId|
        s_new.holds.contains_key(a) && #[trigger] s_new.holds[a].contains(c) implies
            s_new.locks[c] == a by
    {
        if a == agent {
            assert(s_new.holds[agent] == new_holds_set);
            if cells.contains(c) {
                lemma_locks_with_acquired_in(s.locks, cells, agent, c);
            } else {
                lemma_holds_set_acquired_outside(base_holds, cells, c);
                assert(base_holds.contains(c));
                if s.holds.contains_key(agent) {
                    assert(base_holds == s.holds[agent]);
                    assert(s.holds[agent].contains(c));
                    lemma_inv_lock_unique_partition(s, agent, c);
                    lemma_locks_with_acquired_outside(s.locks, cells, agent, c);
                } else {
                    assert(base_holds == Set::<CellId>::empty());
                    assert(false);
                }
            }
        } else {
            assert(s_new.holds[a] == s.holds[a]);
            lemma_inv_lock_unique_partition(s, a, c);
            if cells.contains(c) {
                assert(false);
            } else {
                lemma_locks_with_acquired_outside(s.locks, cells, agent, c);
            }
        }
    };
}

pub proof fn lemma_begin_preserves(
    s: &RuntimeState,
    agent: AgentId,
    cells: Seq<CellId>,
)
    requires
        all_invariants(s),
        can_begin(s, agent, cells),
    ensures
        all_invariants(&begin_step(s, agent, cells))
{
    let s_new = begin_step(s, agent, cells);
    let base_holds = if s.holds.contains_key(agent) {
        s.holds[agent]
    } else {
        Set::<CellId>::empty()
    };
    let new_holds_set = holds_set_with_acquired(base_holds, cells);
    let snapshot = snapshot_built(s.cells, cells);

    assert(s_new.locks == locks_with_acquired(s.locks, cells, agent));
    assert(s_new.holds == s.holds.insert(agent, new_holds_set));
    assert(s_new.pending_snapshot == s.pending_snapshot.insert(agent, (snapshot, s.clock)));
    assert(s_new.trace == s.trace);
    assert(s_new.clock == s.clock);
    assert(s_new.cells == s.cells);

    // Trace and clock unchanged: monotonicity and history obligations follow trivially.
    assert(inv_clock_monotone(&s_new));
    assert(inv_records_held_locks_through_commit(&s_new));

    // ---- inv_pending_separates_old_writes ----
    assert forall |a: AgentId, c: CellId|
        s_new.pending_snapshot.contains_key(a)
        && #[trigger] s_new.pending_snapshot[a].0.dom().contains(c) implies
            forall |j: int| 0 <= j < s_new.trace.len()
                && #[trigger] s_new.trace[j].write_set.contains(c) ==>
                s_new.trace[j].write_time <= s_new.pending_snapshot[a].1 by
    {
        if a == agent {
            assert(s_new.pending_snapshot[a].0 == snapshot);
            assert(s_new.pending_snapshot[a].1 == s.clock);
            assert forall |j: int| 0 <= j < s_new.trace.len()
                && #[trigger] s_new.trace[j].write_set.contains(c) implies
                s_new.trace[j].write_time <= s_new.pending_snapshot[a].1 by
            {
                assert(s_new.trace[j] == s.trace[j]);
                assert(s.trace[j].write_time <= s.clock);
            };
        } else {
            assert(s_new.pending_snapshot[a] == s.pending_snapshot[a]);
            assert(s.pending_snapshot.contains_key(a));
            assert forall |j: int| 0 <= j < s_new.trace.len()
                && #[trigger] s_new.trace[j].write_set.contains(c) implies
                s_new.trace[j].write_time <= s_new.pending_snapshot[a].1 by
            {
                assert(s_new.trace[j] == s.trace[j]);
            };
        }
    };
    assert(inv_pending_separates_old_writes(&s_new));

    // ---- inv_lock_unique (forward + reverse via extracted lemmas) ----
    lemma_begin_preserves_lock_unique_a(s, agent, cells);
    lemma_begin_preserves_lock_unique_b(s, agent, cells);
    assert(inv_lock_unique_a1(&s_new));
    assert(inv_lock_unique_a2(&s_new));
    assert(inv_lock_unique_b1(&s_new));
    assert(inv_lock_unique_b2(&s_new));

    // ---- inv_pending_implies_locks ----
    assert forall |a: AgentId| s_new.pending_snapshot.contains_key(a) implies
        (forall |c: CellId| #[trigger] s_new.pending_snapshot[a].0.dom().contains(c) ==>
            (s_new.locks.contains_key(c) && s_new.locks[c] == a)) by
    {
        if a == agent {
            assert forall |c: CellId| #[trigger] s_new.pending_snapshot[agent].0.dom().contains(c) implies
                s_new.locks.contains_key(c) && s_new.locks[c] == agent by
            {
                assert(s_new.pending_snapshot[agent].0 == snapshot);
                lemma_snapshot_built_dom(s.cells, cells, c);
                assert(cells.contains(c));
                lemma_locks_with_acquired_in(s.locks, cells, agent, c);
            };
        } else {
            assert(s_new.pending_snapshot[a] == s.pending_snapshot[a]);
            assert(s.pending_snapshot.contains_key(a));
            assert forall |c: CellId| #[trigger] s_new.pending_snapshot[a].0.dom().contains(c) implies
                s_new.locks.contains_key(c) && s_new.locks[c] == a by
            {
                assert(s.locks.contains_key(c) && s.locks[c] == a);
                if cells.contains(c) {
                    assert(false);
                } else {
                    lemma_locks_with_acquired_outside(s.locks, cells, agent, c);
                }
            };
        }
    };
    assert(inv_pending_implies_locks(&s_new));

    // ---- inv_holds_finite ----
    assert forall |a: AgentId| #[trigger] s_new.holds.contains_key(a) implies s_new.holds[a].finite() by
    {
        if a == agent {
            assert(s_new.holds[a] == new_holds_set);
            assert(base_holds.finite()) by {
                if s.holds.contains_key(agent) {
                    assert(base_holds == s.holds[agent]);
                } else {
                    assert(base_holds == Set::<CellId>::empty());
                }
            };
            lemma_holds_set_with_acquired_finite(base_holds, cells);
        } else {
            assert(s_new.holds[a] == s.holds[a]);
            assert(s.holds.contains_key(a));
        }
    };
    assert(inv_holds_finite(&s_new));

    // ---- inv_pending_snapshot_finite ----
    assert forall |a: AgentId| #[trigger] s_new.pending_snapshot.contains_key(a) implies
        s_new.pending_snapshot[a].0.dom().finite() by
    {
        if a == agent {
            assert(s_new.pending_snapshot[a].0 == snapshot);
            lemma_snapshot_built_finite(s.cells, cells);
        } else {
            assert(s_new.pending_snapshot[a] == s.pending_snapshot[a]);
            assert(s.pending_snapshot.contains_key(a));
        }
    };
    assert(inv_pending_snapshot_finite(&s_new));
}

// ---- L3: commit preserves all invariants -----------------------------

// Extracted: inv_lock_unique_a1 + a2 (forward direction) preservation under commit.
pub proof fn lemma_commit_preserves_lock_unique_a(
    s: &RuntimeState,
    agent: AgentId,
    write_kv: Map<CellId, Value>,
)
    requires
        all_invariants(s),
        can_commit(s, agent, write_kv),
    ensures
        inv_lock_unique_a1(&commit_step(s, agent, write_kv)),
        inv_lock_unique_a2(&commit_step(s, agent, write_kv)),
{
    let s_new = commit_step(s, agent, write_kv);
    let agent_locks = if s.holds.contains_key(agent) {
        s.holds[agent]
    } else {
        Set::<CellId>::empty()
    };

    assert(s_new.locks == locks_with_released(s.locks, agent_locks));
    assert(s_new.holds == s.holds.insert(agent, Set::<CellId>::empty()));

    // a1: contains_key part
    assert forall |c: CellId| s_new.locks.contains_key(c) implies
        s_new.holds.contains_key(s_new.locks[c]) by
    {
        assert(s.locks.contains_key(c));
        assert(!agent_locks.contains(c));
        let holder = s.locks[c];
        lemma_inv_lock_unique_lookup(s, c);
        if holder == agent {
            assert(s.holds[agent].contains(c));
            assert(agent_locks == s.holds[agent]);
            assert(false);
        }
        assert(s_new.holds.contains_key(holder));
        assert(s_new.locks[c] == holder);
    };

    // a2: holds.contains part
    assert forall |c: CellId| s_new.locks.contains_key(c) implies
        s_new.holds[s_new.locks[c]].contains(c) by
    {
        assert(s.locks.contains_key(c));
        assert(!agent_locks.contains(c));
        let holder = s.locks[c];
        lemma_inv_lock_unique_lookup(s, c);
        assert(s.holds[holder].contains(c));
        if holder == agent {
            assert(s.holds[agent].contains(c));
            assert(agent_locks == s.holds[agent]);
            assert(false);
        }
        assert(s_new.holds[holder] == s.holds[holder]);
        assert(s_new.locks[c] == holder);
    };
}

// Extracted: inv_lock_unique_b1 + b2 (reverse direction / partition) preservation under commit.
pub proof fn lemma_commit_preserves_lock_unique_b(
    s: &RuntimeState,
    agent: AgentId,
    write_kv: Map<CellId, Value>,
)
    requires
        all_invariants(s),
        can_commit(s, agent, write_kv),
    ensures
        inv_lock_unique_b1(&commit_step(s, agent, write_kv)),
        inv_lock_unique_b2(&commit_step(s, agent, write_kv)),
{
    let s_new = commit_step(s, agent, write_kv);
    let agent_locks = if s.holds.contains_key(agent) {
        s.holds[agent]
    } else {
        Set::<CellId>::empty()
    };

    assert(s_new.locks == locks_with_released(s.locks, agent_locks));
    assert(s_new.holds == s.holds.insert(agent, Set::<CellId>::empty()));

    // b1: contains_key part
    assert forall |a: AgentId, c: CellId|
        s_new.holds.contains_key(a) && #[trigger] s_new.holds[a].contains(c) implies
            s_new.locks.contains_key(c) by
    {
        if a == agent {
            assert(s_new.holds[agent] == Set::<CellId>::empty());
            assert(false);
        } else {
            assert(s_new.holds[a] == s.holds[a]);
            lemma_inv_lock_unique_partition(s, a, c);
            if agent_locks.contains(c) {
                assert(s.holds[agent].contains(c));
                lemma_inv_lock_unique_partition(s, agent, c);
                assert(false);
            }
            assert(s_new.locks.contains_key(c));
        }
    };

    // b2: equality part
    assert forall |a: AgentId, c: CellId|
        s_new.holds.contains_key(a) && #[trigger] s_new.holds[a].contains(c) implies
            s_new.locks[c] == a by
    {
        if a == agent {
            assert(s_new.holds[agent] == Set::<CellId>::empty());
            assert(false);
        } else {
            assert(s_new.holds[a] == s.holds[a]);
            lemma_inv_lock_unique_partition(s, a, c);
            if agent_locks.contains(c) {
                assert(s.holds[agent].contains(c));
                lemma_inv_lock_unique_partition(s, agent, c);
                assert(false);
            }
            assert(s_new.locks[c] == s.locks[c]);
        }
    };
}

pub proof fn lemma_commit_preserves(
    s: &RuntimeState,
    agent: AgentId,
    write_kv: Map<CellId, Value>,
)
    requires
        all_invariants(s),
        can_commit(s, agent, write_kv),
    ensures
        all_invariants(&commit_step(s, agent, write_kv))
{
    let s_new = commit_step(s, agent, write_kv);
    let pending = s.pending_snapshot[agent];
    let snap = pending.0;
    let rt = pending.1;
    let read_set = snap.dom();
    let write_set = write_kv.dom();
    let new_clock = s.clock + 1;
    let record = OpRecord {
        agent: agent,
        read_set: read_set,
        read_values: snap,
        read_time: rt,
        write_set: write_set,
        write_values: write_kv,
        write_time: new_clock,
    };

    assert(s_new.trace == s.trace.push(record));
    assert(s_new.clock == s.clock + 1);

    let agent_locks = if s.holds.contains_key(agent) {
        s.holds[agent]
    } else {
        Set::<CellId>::empty()
    };
    assert(s_new.locks == locks_with_released(s.locks, agent_locks));
    assert(s_new.holds == s.holds.insert(agent, Set::<CellId>::empty()));
    assert(s_new.pending_snapshot == s.pending_snapshot.remove(agent));

    // Finiteness of snap.dom() comes from inv_pending_snapshot_finite.
    assert(s.pending_snapshot.contains_key(agent));
    assert(snap.dom().finite());
    assert(write_kv.dom().finite());

    // record.read_set == snap.dom() and record.write_set == write_kv.dom() directly,
    // so membership equivalence is trivial (no to_seq() conversion needed).

    // ---- inv_clock_monotone ----
    assert forall |i: int| 0 <= i < s_new.trace.len() implies
        #[trigger] s_new.trace[i].write_time <= s_new.clock
        && (forall |k: int| 0 <= k < i ==>
            #[trigger] s_new.trace[k].write_time < s_new.trace[i].write_time) by
    {
        if i < s.trace.len() {
            assert(s_new.trace[i] == s.trace[i]);
            assert(s.trace[i].write_time <= s.clock);
            assert forall |k: int| 0 <= k < i implies
                #[trigger] s_new.trace[k].write_time < s_new.trace[i].write_time by
            {
                assert(s_new.trace[k] == s.trace[k]);
            };
        } else {
            assert(i == s.trace.len() as int);
            assert(s_new.trace[i] == record);
            assert(record.write_time == s.clock + 1);
            assert forall |k: int| 0 <= k < i implies
                #[trigger] s_new.trace[k].write_time < s_new.trace[i].write_time by
            {
                assert(s_new.trace[k] == s.trace[k]);
                assert(s.trace[k].write_time <= s.clock);
            };
        }
    };
    assert(inv_clock_monotone(&s_new));

    // ---- inv_lock_unique (forward + reverse via extracted lemmas) ----
    lemma_commit_preserves_lock_unique_a(s, agent, write_kv);
    lemma_commit_preserves_lock_unique_b(s, agent, write_kv);
    assert(inv_lock_unique_a1(&s_new));
    assert(inv_lock_unique_a2(&s_new));
    assert(inv_lock_unique_b1(&s_new));
    assert(inv_lock_unique_b2(&s_new));

    // ---- inv_pending_implies_locks ----
    assert forall |a: AgentId| s_new.pending_snapshot.contains_key(a) implies
        (forall |c: CellId| #[trigger] s_new.pending_snapshot[a].0.dom().contains(c) ==>
            (s_new.locks.contains_key(c) && s_new.locks[c] == a)) by
    {
        assert(a != agent);
        assert(s.pending_snapshot.contains_key(a));
        assert(s_new.pending_snapshot[a] == s.pending_snapshot[a]);
        assert forall |c: CellId| #[trigger] s_new.pending_snapshot[a].0.dom().contains(c) implies
            s_new.locks.contains_key(c) && s_new.locks[c] == a by
        {
            assert(s.locks.contains_key(c) && s.locks[c] == a);
            if agent_locks.contains(c) {
                assert(s.holds.contains_key(agent));
                assert(s.holds[agent].contains(c));
                lemma_inv_lock_unique_partition(s, agent, c);
                assert(s.locks[c] == agent);
                assert(false);
            }
            assert(s_new.locks.contains_key(c));
            assert(s_new.locks[c] == s.locks[c]);
        };
    };
    assert(inv_pending_implies_locks(&s_new));

    // ---- inv_pending_separates_old_writes ----
    assert forall |a: AgentId, c: CellId|
        s_new.pending_snapshot.contains_key(a)
        && #[trigger] s_new.pending_snapshot[a].0.dom().contains(c) implies
            forall |j: int| 0 <= j < s_new.trace.len()
                && #[trigger] s_new.trace[j].write_set.contains(c) ==>
                s_new.trace[j].write_time <= s_new.pending_snapshot[a].1 by
    {
        assert(a != agent);
        assert(s.pending_snapshot.contains_key(a));
        assert(s_new.pending_snapshot[a] == s.pending_snapshot[a]);

        assert forall |j: int| 0 <= j < s_new.trace.len()
            && #[trigger] s_new.trace[j].write_set.contains(c) implies
            s_new.trace[j].write_time <= s_new.pending_snapshot[a].1 by
        {
            if j < s.trace.len() {
                assert(s_new.trace[j] == s.trace[j]);
            } else {
                assert(j == s.trace.len() as int);
                assert(s_new.trace[j] == record);
                assert(record.write_set == write_set);
                assert(record.write_set.contains(c));
                assert(write_kv.dom().contains(c));
                assert(s.locks.contains_key(c) && s.locks[c] == agent);
                assert(s.locks[c] == a);
                assert(false);
            }
        };
    };
    assert(inv_pending_separates_old_writes(&s_new));

    // ---- inv_records_held_locks_through_commit (substantive) ----
    assert forall |i: int, c: CellId|
        0 <= i < s_new.trace.len() &&
        #[trigger] s_new.trace[i].read_set.contains(c) implies
            (forall |j: int| 0 <= j < s_new.trace.len() && j != i &&
                #[trigger] s_new.trace[j].write_set.contains(c) ==>
                (s_new.trace[j].write_time <= s_new.trace[i].read_time
                 || s_new.trace[j].write_time >= s_new.trace[i].write_time)) by
    {
        assert forall |j: int| 0 <= j < s_new.trace.len() && j != i &&
            #[trigger] s_new.trace[j].write_set.contains(c) implies
            (s_new.trace[j].write_time <= s_new.trace[i].read_time
             || s_new.trace[j].write_time >= s_new.trace[i].write_time) by
        {
            if i < s.trace.len() && j < s.trace.len() {
                // CASE A: both old.
                assert(s_new.trace[i] == s.trace[i]);
                assert(s_new.trace[j] == s.trace[j]);
            } else if i < s.trace.len() && j == s.trace.len() as int {
                // CASE B: i old, j new. record.write_time = s.clock + 1.
                assert(s_new.trace[j] == record);
                assert(record.write_time == s.clock + 1);
                assert(s_new.trace[i] == s.trace[i]);
                assert(s.trace[i].write_time <= s.clock);
            } else if i == s.trace.len() as int && j < s.trace.len() {
                // CASE C: i new, j old. The substantive case.
                assert(s_new.trace[i] == record);
                assert(s_new.trace[j] == s.trace[j]);
                assert(record.read_set == read_set);
                assert(record.read_set.contains(c));
                // record.read_set == snap.dom() (direct, no Seq conversion)
                assert(snap.dom().contains(c));
                // Apply inv_pending_separates_old_writes(s) at (agent, c, j).
                assert(s.pending_snapshot[agent].0 == snap);
                assert(s.pending_snapshot[agent].0.dom().contains(c));
                assert(s.pending_snapshot[agent].1 == rt);
                assert(s.trace[j].write_set.contains(c));
                assert(s.trace[j].write_time <= rt);
                assert(record.read_time == rt);
            } else {
                assert(i == s.trace.len() as int && j == s.trace.len() as int);
                assert(false);
            }
        };
    };
    assert(inv_records_held_locks_through_commit(&s_new));

    // ---- inv_holds_finite ----
    assert forall |a: AgentId| #[trigger] s_new.holds.contains_key(a) implies s_new.holds[a].finite() by
    {
        if a == agent {
            assert(s_new.holds[a] == Set::<CellId>::empty());
        } else {
            assert(s_new.holds[a] == s.holds[a]);
            assert(s.holds.contains_key(a));
        }
    };
    assert(inv_holds_finite(&s_new));

    // ---- inv_pending_snapshot_finite ----
    assert forall |a: AgentId| #[trigger] s_new.pending_snapshot.contains_key(a) implies
        s_new.pending_snapshot[a].0.dom().finite() by
    {
        assert(a != agent);
        assert(s_new.pending_snapshot[a] == s.pending_snapshot[a]);
        assert(s.pending_snapshot.contains_key(a));
    };
    assert(inv_pending_snapshot_finite(&s_new));
}

// =====================================================================
// Section 7: Reachability and L4 induction
// =====================================================================

pub open spec fn is_begin_successor(s_pre: &RuntimeState, s: &RuntimeState) -> bool {
    exists |agent: AgentId, cells: Seq<CellId>|
        #[trigger] can_begin(s_pre, agent, cells) && *s == begin_step(s_pre, agent, cells)
}

pub open spec fn is_commit_successor(s_pre: &RuntimeState, s: &RuntimeState) -> bool {
    exists |agent: AgentId, write_kv: Map<CellId, Value>|
        #[trigger] can_commit(s_pre, agent, write_kv) && *s == commit_step(s_pre, agent, write_kv)
}

pub open spec fn reachable_step(s_pre: &RuntimeState, s: &RuntimeState) -> bool {
    is_begin_successor(s_pre, s) || is_commit_successor(s_pre, s)
}

// =====================================================================
// Section 7: Sequence-based reachability and L4 induction
// =====================================================================
// We avoid recursive spec functions for reachability because Verus's
// fuel-limited unfolding makes fact-based existential extraction brittle.
// Instead, reachability is witnessed by an explicit sequence of states
// starting from init_state(), with consecutive states connected by a
// transition. Induction is on Seq::len() — structural recursion, no fuel.

pub open spec fn execution(states: Seq<RuntimeState>) -> bool {
    states.len() > 0
    && states[0] == init_state()
    && (forall |i: int| 0 <= i < states.len() - 1 ==>
        #[trigger] reachable_step(&states[i], &states[i + 1]))
}

pub open spec fn reachable(s: &RuntimeState) -> bool {
    exists |states: Seq<RuntimeState>|
        #[trigger] execution(states) && states.last() == *s
}

pub proof fn lemma_states_imply_invariants(states: Seq<RuntimeState>)
    requires execution(states)
    ensures all_invariants(&states.last())
    decreases states.len()
{
    if states.len() == 1 {
        assert(states[0] == init_state());
        assert(states.last() == states[0]);
        lemma_init_invariants();
        // all_invariants(&init_state()) holds. states.last() == init_state(). Done.
    } else {
        let prefix = states.drop_last();
        assert(prefix.len() == states.len() - 1);
        assert(prefix.len() >= 1);
        assert(prefix[0] == states[0]);

        // Establish execution(prefix).
        assert forall |i: int| 0 <= i < prefix.len() - 1 implies
            #[trigger] reachable_step(&prefix[i], &prefix[i + 1]) by
        {
            assert(prefix[i] == states[i]);
            assert(prefix[i + 1] == states[i + 1]);
            assert(0 <= i < states.len() - 1);
        };
        assert(execution(prefix));

        lemma_states_imply_invariants(prefix);
        // Now all_invariants(&prefix.last()).

        let last_idx = (states.len() - 2) as int;
        assert(0 <= last_idx < states.len() - 1);
        assert(prefix.last() == states[last_idx]);
        assert(states.last() == states[last_idx + 1]);
        // The reachable_step from execution(states):
        assert(reachable_step(&states[last_idx], &states[last_idx + 1]));

        let s_pre = states[last_idx];
        let s_new = states.last();
        assert(prefix.last() == s_pre);
        assert(reachable_step(&s_pre, &s_new));
        assert(all_invariants(&s_pre));

        if is_begin_successor(&s_pre, &s_new) {
            let pair = choose |agent: AgentId, cells: Seq<CellId>|
                #[trigger] can_begin(&s_pre, agent, cells) && s_new == begin_step(&s_pre, agent, cells);
            let agent = pair.0;
            let cells = pair.1;
            assert(can_begin(&s_pre, agent, cells));
            assert(s_new == begin_step(&s_pre, agent, cells));
            lemma_begin_preserves(&s_pre, agent, cells);
            assert(all_invariants(&begin_step(&s_pre, agent, cells)));
        } else {
            assert(is_commit_successor(&s_pre, &s_new));
            let pair = choose |agent: AgentId, write_kv: Map<CellId, Value>|
                #[trigger] can_commit(&s_pre, agent, write_kv) && s_new == commit_step(&s_pre, agent, write_kv);
            let agent = pair.0;
            let write_kv = pair.1;
            assert(can_commit(&s_pre, agent, write_kv));
            assert(s_new == commit_step(&s_pre, agent, write_kv));
            lemma_commit_preserves(&s_pre, agent, write_kv);
            assert(all_invariants(&commit_step(&s_pre, agent, write_kv)));
        }
    }
}

pub proof fn lemma_invariants_inductive(s: &RuntimeState)
    requires reachable(s)
    ensures all_invariants(s)
{
    let states = choose |states: Seq<RuntimeState>|
        #[trigger] execution(states) && states.last() == *s;
    lemma_states_imply_invariants(states);
    assert(states.last() == *s);
}

// =====================================================================
// FINAL SAFETY THEOREM
// =====================================================================

pub proof fn theorem_pessimistic_prevents_a1(s: &RuntimeState)
    requires reachable(s)
    ensures !a1(s.trace)
{
    lemma_invariants_inductive(s);
    pessimistic_no_a1(s);
}

} // verus!