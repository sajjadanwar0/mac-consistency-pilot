// =====================================================================
// Verus proof: SSI (Serializable Snapshot Isolation) prevents A_1.
//
// COMPANION FILE
//   Standalone proof for the SSI strategy of `mac-consistency-runtime`.
//   Independent of `lib.rs` (the pessimistic proof). Compile with:
//
//     verus --crate-type=lib src/lib_ssi.rs
//
// SCOPE
//   Sequential safety: under any sequential interleaving of begin /
//   commit-success / commit-abort transitions, the SSI runtime
//   produces an OpRecord trace satisfying !A_1.
//
//   The proof targets SSI mode (validate_no_write = true). Default-SI
//   admits the no-write gap (paper §5.5); the conditional safety result
//   for default-SI is sketched at the end of this file but not closed.
//
// FIX HISTORY
//   v1: 7/8 verified — lemma_states_imply_invariants failed on
//       reachable_step / all_invariants reference plumbing.
//   v2 (this): mirrored pessimistic lib.rs structure exactly:
//       (a) ensures all_invariants(&states.last()), not forall k
//       (b) drop_last() instead of subrange()
//       (c) tuple-projection (pair.0, pair.1) for choose witnesses
//       (d) reachable uses states.last() == *s

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
// Section 2: SSI state
// =====================================================================

pub struct PendingSnapshot {
    pub read_time: Time,
    pub read_values: Map<CellId, Value>,
}

pub struct SsiState {
    pub store: Map<CellId, Value>,
    pub last_write: Map<CellId, Time>,
    pub pending: Map<AgentId, PendingSnapshot>,
    pub clock: Time,
    pub trace: Seq<OpRecord>,
}

pub open spec fn init_ssi_state() -> SsiState {
    SsiState {
        store: Map::<CellId, Value>::empty(),
        last_write: Map::<CellId, Time>::empty(),
        pending: Map::<AgentId, PendingSnapshot>::empty(),
        clock: 0,
        trace: Seq::<OpRecord>::empty(),
    }
}

pub open spec fn last_write_of(s: &SsiState, c: CellId) -> Time {
    if s.last_write.contains_key(c) { s.last_write[c] } else { 0 }
}

pub open spec fn validation_passes(s: &SsiState, ps: PendingSnapshot) -> bool {
    forall |c: CellId|
        #[trigger] ps.read_values.contains_key(c)
        ==> last_write_of(s, c) <= ps.read_time
}

// =====================================================================
// Section 3: Helper specs for last_write and store updates on commit
// =====================================================================

pub open spec fn last_write_after_commit(
    base: Map<CellId, Time>,
    write_set: Set<CellId>,
    new_clock: Time,
) -> Map<CellId, Time> {
    Map::new(
        |c: CellId| base.contains_key(c) || write_set.contains(c),
        |c: CellId| if write_set.contains(c) { new_clock }
                    else if base.contains_key(c) { base[c] }
                    else { 0 },
    )
}

pub open spec fn store_after_commit(
    base: Map<CellId, Value>,
    write_set: Set<CellId>,
    write_values: Map<CellId, Value>,
) -> Map<CellId, Value> {
    Map::new(
        |c: CellId| base.contains_key(c) || write_set.contains(c),
        |c: CellId| if write_set.contains(c) && write_values.contains_key(c) {
                        write_values[c]
                    } else if base.contains_key(c) {
                        base[c]
                    } else {
                        null_value()
                    },
    )
}

pub open spec fn read_values_snapshot(
    store: Map<CellId, Value>,
    read_cells: Set<CellId>,
) -> Map<CellId, Value> {
    Map::new(
        |c: CellId| read_cells.contains(c),
        |c: CellId| if store.contains_key(c) { store[c] } else { null_value() },
    )
}

// =====================================================================
// Section 4: Transition relation
// =====================================================================

pub open spec fn can_begin(s: &SsiState, agent: AgentId) -> bool {
    !s.pending.contains_key(agent)
}

pub open spec fn ssi_begin_step(
    s: &SsiState,
    agent: AgentId,
    read_cells: Set<CellId>,
    s_new: &SsiState,
) -> bool {
    can_begin(s, agent)
    && read_cells.finite()
    && s_new.store == s.store
    && s_new.last_write == s.last_write
    && s_new.clock == s.clock
    && s_new.trace == s.trace
    && s_new.pending == s.pending.insert(
        agent,
        PendingSnapshot {
            read_time: s.clock,
            read_values: read_values_snapshot(s.store, read_cells),
        },
    )
}

pub open spec fn can_commit(s: &SsiState, agent: AgentId) -> bool {
    s.pending.contains_key(agent)
}

pub open spec fn ssi_commit_success_step(
    s: &SsiState,
    agent: AgentId,
    write_set: Set<CellId>,
    write_values: Map<CellId, Value>,
    s_new: &SsiState,
) -> bool {
    can_commit(s, agent)
    && write_set.finite()
    && write_set.subset_of(write_values.dom())
    && validation_passes(s, s.pending[agent])
    && s_new.clock == s.clock + 1
    && s_new.last_write == last_write_after_commit(s.last_write, write_set, s_new.clock)
    && s_new.store == store_after_commit(s.store, write_set, write_values)
    && s_new.pending == s.pending.remove(agent)
    && s_new.trace == s.trace.push(OpRecord {
        agent: agent,
        read_set: s.pending[agent].read_values.dom(),
        read_values: s.pending[agent].read_values,
        read_time: s.pending[agent].read_time,
        write_set: write_set,
        write_values: write_values,
        write_time: s_new.clock,
    })
}

pub open spec fn ssi_commit_abort_step(
    s: &SsiState,
    agent: AgentId,
    s_new: &SsiState,
) -> bool {
    can_commit(s, agent)
    && !validation_passes(s, s.pending[agent])
    && s_new.store == s.store
    && s_new.last_write == s.last_write
    && s_new.clock == s.clock
    && s_new.trace == s.trace
    && s_new.pending == s.pending.remove(agent)
}

// =====================================================================
// Section 5: Invariants
// =====================================================================

pub open spec fn inv_clock_monotone(s: &SsiState) -> bool {
    forall |i: int|
        0 <= i < s.trace.len()
        ==> #[trigger] s.trace[i].read_time < s.trace[i].write_time
}

pub open spec fn inv_record_writetime_le_clock(s: &SsiState) -> bool {
    forall |i: int|
        0 <= i < s.trace.len()
        ==> #[trigger] s.trace[i].write_time <= s.clock
}

pub open spec fn inv_last_write_dominates(s: &SsiState) -> bool {
    forall |i: int, c: CellId|
        0 <= i < s.trace.len()
        && #[trigger] s.trace[i].write_set.contains(c)
        ==> s.last_write.contains_key(c)
            && s.trace[i].write_time <= s.last_write[c]
}

pub open spec fn inv_pending_read_time_le_clock(s: &SsiState) -> bool {
    forall |a: AgentId|
        #[trigger] s.pending.contains_key(a)
        ==> s.pending[a].read_time <= s.clock
}

pub open spec fn inv_no_intervening_write(s: &SsiState) -> bool {
    forall |i: int, j: int, c: CellId|
        0 <= i < s.trace.len() && 0 <= j < s.trace.len()
        && #[trigger] s.trace[i].read_set.contains(c)
        && #[trigger] s.trace[j].write_set.contains(c)
        ==> !(s.trace[i].read_time < s.trace[j].write_time
              && s.trace[j].write_time < s.trace[i].write_time)
}

pub open spec fn inv_pending_finite(s: &SsiState) -> bool {
    s.pending.dom().finite()
}

pub open spec fn inv_last_write_finite(s: &SsiState) -> bool {
    s.last_write.dom().finite()
}

pub open spec fn all_invariants(s: &SsiState) -> bool {
    inv_clock_monotone(s)
    && inv_record_writetime_le_clock(s)
    && inv_last_write_dominates(s)
    && inv_pending_read_time_le_clock(s)
    && inv_no_intervening_write(s)
    && inv_pending_finite(s)
    && inv_last_write_finite(s)
}

// =====================================================================
// Section 6: Safety theorem from invariants
// =====================================================================

pub proof fn ssi_no_a1(s: &SsiState)
    requires all_invariants(s)
    ensures !a1(s.trace)
{
    if a1(s.trace) {
        let (i, j, c) = choose |i: int, j: int, c: CellId|
            0 <= i < s.trace.len() && 0 <= j < s.trace.len() && i != j
            && #[trigger] s.trace[i].read_set.contains(c)
            && #[trigger] s.trace[j].write_set.contains(c)
            && s.trace[i].read_time < s.trace[j].write_time
            && s.trace[j].write_time < s.trace[i].write_time
            && s.trace[i].read_values.contains_key(c)
            && s.trace[j].write_values.contains_key(c)
            && s.trace[i].read_values[c] != s.trace[j].write_values[c];
        assert(s.trace[i].read_set.contains(c));
        assert(s.trace[j].write_set.contains(c));
        assert(false);
    }
}

// =====================================================================
// Section 7: Init satisfies invariants
// =====================================================================

pub proof fn lemma_init_invariants()
    ensures all_invariants(&init_ssi_state())
{
    let s = init_ssi_state();
    assert(s.trace.len() == 0);
    assert(s.pending.dom() =~= Set::<AgentId>::empty());
    assert(s.last_write.dom() =~= Set::<CellId>::empty());
}

// =====================================================================
// Section 8: begin_step preserves invariants
// =====================================================================

pub proof fn lemma_begin_preserves(
    s: &SsiState,
    s_new: &SsiState,
    agent: AgentId,
    read_cells: Set<CellId>,
)
    requires
        all_invariants(s),
        ssi_begin_step(s, agent, read_cells, s_new),
    ensures
        all_invariants(s_new),
{
    assert(s_new.trace == s.trace);
    assert(s_new.last_write == s.last_write);
    assert(s_new.store == s.store);
    assert(s_new.clock == s.clock);

    assert forall |a: AgentId| #[trigger] s_new.pending.contains_key(a)
        implies s_new.pending[a].read_time <= s_new.clock
    by {
        if a == agent {
            assert(s_new.pending[a].read_time == s.clock);
        } else {
            assert(s.pending.contains_key(a));
            assert(s.pending[a] == s_new.pending[a]);
        }
    };

    assert(s_new.pending.dom() =~= s.pending.dom().insert(agent));
}

// =====================================================================
// Section 9: commit_success_step preserves invariants
// =====================================================================

pub proof fn lemma_commit_success_preserves(
    s: &SsiState,
    s_new: &SsiState,
    agent: AgentId,
    write_set: Set<CellId>,
    write_values: Map<CellId, Value>,
)
    requires
        all_invariants(s),
        ssi_commit_success_step(s, agent, write_set, write_values, s_new),
    ensures
        all_invariants(s_new),
{
    let new_clock = s_new.clock;
    let n = s.trace.len() as int;

    assert forall |i: int| 0 <= i < s_new.trace.len()
        implies #[trigger] s_new.trace[i].read_time < s_new.trace[i].write_time
    by {
        if i < n {
            assert(s_new.trace[i] == s.trace[i]);
        } else {
            let ps = s.pending[agent];
            assert(ps.read_time <= s.clock);
            assert(new_clock == s.clock + 1);
            assert(s_new.trace[n].read_time == ps.read_time);
            assert(s_new.trace[n].write_time == new_clock);
        }
    };

    assert forall |i: int| 0 <= i < s_new.trace.len()
        implies #[trigger] s_new.trace[i].write_time <= s_new.clock
    by {
        if i < n {
            assert(s_new.trace[i] == s.trace[i]);
            assert(s.trace[i].write_time <= s.clock);
            assert(s.clock < new_clock);
        } else {
            assert(s_new.trace[n].write_time == new_clock);
        }
    };

    assert forall |i: int, c: CellId|
        0 <= i < s_new.trace.len()
        && #[trigger] s_new.trace[i].write_set.contains(c)
        implies s_new.last_write.contains_key(c)
                && s_new.trace[i].write_time <= s_new.last_write[c]
    by {
        if i < n {
            assert(s_new.trace[i] == s.trace[i]);
            assert(s.last_write.contains_key(c));
            if write_set.contains(c) {
                assert(s_new.last_write[c] == new_clock);
                assert(s.trace[i].write_time <= s.clock);
                assert(s.clock < new_clock);
            } else {
                assert(s_new.last_write[c] == s.last_write[c]);
            }
        } else {
            assert(s_new.trace[n].write_set == write_set);
            assert(s_new.trace[n].write_time == new_clock);
            assert(write_set.contains(c));
            assert(s_new.last_write.contains_key(c));
            assert(s_new.last_write[c] == new_clock);
        }
    };

    assert forall |a: AgentId| #[trigger] s_new.pending.contains_key(a)
        implies s_new.pending[a].read_time <= s_new.clock
    by {
        assert(a != agent);
        assert(s.pending.contains_key(a));
        assert(s.pending[a].read_time <= s.clock);
        assert(s.clock < new_clock);
        assert(s_new.pending[a] == s.pending[a]);
    };

    let ps = s.pending[agent];
    assert forall |i: int, j: int, c: CellId|
        0 <= i < s_new.trace.len() && 0 <= j < s_new.trace.len()
        && #[trigger] s_new.trace[i].read_set.contains(c)
        && #[trigger] s_new.trace[j].write_set.contains(c)
        implies !(s_new.trace[i].read_time < s_new.trace[j].write_time
                  && s_new.trace[j].write_time < s_new.trace[i].write_time)
    by {
        if i < n && j < n {
            assert(s_new.trace[i] == s.trace[i]);
            assert(s_new.trace[j] == s.trace[j]);
        } else if i == n && j < n {
            assert(s_new.trace[i].read_time == ps.read_time);
            assert(s_new.trace[i].write_time == new_clock);
            assert(s_new.trace[j] == s.trace[j]);
            assert(s.trace[j].write_set.contains(c));
            assert(s.last_write.contains_key(c));
            assert(s.trace[j].write_time <= s.last_write[c]);
            assert(s_new.trace[i].read_set == ps.read_values.dom());
            assert(s_new.trace[i].read_set.contains(c));
            assert(ps.read_values.contains_key(c));
            assert(last_write_of(s, c) <= ps.read_time);
            assert(last_write_of(s, c) == s.last_write[c]);
            assert(s.trace[j].write_time <= ps.read_time);
        } else if i < n && j == n {
            assert(s_new.trace[j].write_time == new_clock);
            assert(s_new.trace[i] == s.trace[i]);
            assert(s.trace[i].write_time <= s.clock);
            assert(s.clock < new_clock);
        } else {
            assert(i == n && j == n);
            assert(s_new.trace[i].write_time == s_new.trace[j].write_time);
        }
    };

    assert(s_new.pending.dom() =~= s.pending.dom().remove(agent));
    assert(s_new.last_write.dom() =~= s.last_write.dom().union(write_set));
}

// =====================================================================
// Section 10: commit_abort_step preserves invariants
// =====================================================================

pub proof fn lemma_commit_abort_preserves(
    s: &SsiState,
    s_new: &SsiState,
    agent: AgentId,
)
    requires
        all_invariants(s),
        ssi_commit_abort_step(s, agent, s_new),
    ensures
        all_invariants(s_new),
{
    assert(s_new.trace == s.trace);
    assert(s_new.clock == s.clock);
    assert(s_new.last_write == s.last_write);
    assert(s_new.store == s.store);

    assert forall |a: AgentId| #[trigger] s_new.pending.contains_key(a)
        implies s_new.pending[a].read_time <= s_new.clock
    by {
        assert(a != agent);
        assert(s.pending.contains_key(a));
        assert(s_new.pending[a] == s.pending[a]);
    };

    assert(s_new.pending.dom() =~= s.pending.dom().remove(agent));
}

// =====================================================================
// Section 11: Sequence-based reachability
// =====================================================================

pub open spec fn is_begin_successor(s_pre: &SsiState, s: &SsiState) -> bool {
    exists |a: AgentId, rc: Set<CellId>| ssi_begin_step(s_pre, a, rc, s)
}

pub open spec fn is_commit_success_successor(s_pre: &SsiState, s: &SsiState) -> bool {
    exists |a: AgentId, ws: Set<CellId>, wv: Map<CellId, Value>|
        ssi_commit_success_step(s_pre, a, ws, wv, s)
}

pub open spec fn is_commit_abort_successor(s_pre: &SsiState, s: &SsiState) -> bool {
    exists |a: AgentId| ssi_commit_abort_step(s_pre, a, s)
}

pub open spec fn reachable_step(s_pre: &SsiState, s: &SsiState) -> bool {
    is_begin_successor(s_pre, s)
    || is_commit_success_successor(s_pre, s)
    || is_commit_abort_successor(s_pre, s)
}

pub open spec fn execution(states: Seq<SsiState>) -> bool {
    states.len() > 0
    && states[0] == init_ssi_state()
    && (forall |k: int| 0 <= k < states.len() - 1
        ==> #[trigger] reachable_step(&states[k], &states[k + 1]))
}

pub open spec fn reachable(s: &SsiState) -> bool {
    exists |states: Seq<SsiState>|
        #[trigger] execution(states) && states.last() == *s
}

// =====================================================================
// Section 12: Lemma — reachable states satisfy invariants
//
// Mirrors the working pessimistic version (lib.rs lines 1230-1293):
//   * ensures all_invariants(&states.last()), not forall k
//   * uses drop_last() instead of subrange()
//   * uses tuple-projection (pair.0, pair.1) for choose witnesses
// =====================================================================

pub proof fn lemma_states_imply_invariants(states: Seq<SsiState>)
    requires execution(states)
    ensures all_invariants(&states.last())
    decreases states.len()
{
    if states.len() == 1 {
        assert(states[0] == init_ssi_state());
        assert(states.last() == states[0]);
        lemma_init_invariants();
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
        // Now we have all_invariants(&prefix.last()).

        let last_idx = (states.len() - 2) as int;
        assert(0 <= last_idx < states.len() - 1);
        assert(prefix.last() == states[last_idx]);
        assert(states.last() == states[last_idx + 1]);
        assert(reachable_step(&states[last_idx], &states[last_idx + 1]));

        let s_pre = states[last_idx];
        let s_cur = states.last();
        assert(prefix.last() == s_pre);
        assert(reachable_step(&s_pre, &s_cur));
        assert(all_invariants(&s_pre));

        if is_begin_successor(&s_pre, &s_cur) {
            let pair = choose |a: AgentId, rc: Set<CellId>|
                ssi_begin_step(&s_pre, a, rc, &s_cur);
            let a = pair.0;
            let rc = pair.1;
            assert(ssi_begin_step(&s_pre, a, rc, &s_cur));
            lemma_begin_preserves(&s_pre, &s_cur, a, rc);
        } else if is_commit_success_successor(&s_pre, &s_cur) {
            let triple = choose |a: AgentId, ws: Set<CellId>, wv: Map<CellId, Value>|
                ssi_commit_success_step(&s_pre, a, ws, wv, &s_cur);
            let a = triple.0;
            let ws = triple.1;
            let wv = triple.2;
            assert(ssi_commit_success_step(&s_pre, a, ws, wv, &s_cur));
            lemma_commit_success_preserves(&s_pre, &s_cur, a, ws, wv);
        } else {
            assert(is_commit_abort_successor(&s_pre, &s_cur));
            let a = choose |a: AgentId| ssi_commit_abort_step(&s_pre, a, &s_cur);
            assert(ssi_commit_abort_step(&s_pre, a, &s_cur));
            lemma_commit_abort_preserves(&s_pre, &s_cur, a);
        }
    }
}

pub proof fn lemma_invariants_inductive(s: &SsiState)
    requires reachable(s)
    ensures all_invariants(s)
{
    let states = choose |states: Seq<SsiState>|
        #[trigger] execution(states) && states.last() == *s;
    lemma_states_imply_invariants(states);
    assert(states.last() == *s);
}

// =====================================================================
// Section 13: Final theorem
// =====================================================================

pub proof fn theorem_ssi_prevents_a1(s: &SsiState)
    requires reachable(s)
    ensures !a1(s.trace)
{
    lemma_invariants_inductive(s);
    ssi_no_a1(s);
}

// =====================================================================
// Notes on default-SI (out of scope for this file)
// =====================================================================
//
// Default-SI (validate_no_write = false) admits the no-write-stale-read
// gap of paper §5.5: an operation with empty write_set bypasses
// validation. A conditional theorem "if every record has non-empty
// write_set then !a1" closes default-SI under the all-writers
// assumption; structure identical to the SSI proof above with the
// non-empty-write-set hypothesis carried in the safety invariant.
// Future work.

} // verus!