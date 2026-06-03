// =====================================================================
// Verus proof: Default-SI conditional safety theorem.
//
// COMPANION FILE
//   Standalone proof for the default-SI strategy of
//   `mac-consistency-runtime` (validate_no_write = false). Compile with:
//
//     verus --crate-type=lib src/lib_default_si.rs
//
// MODEL
//   Default-SI differs from SSI in one respect: an agent committing
//   with an EMPTY write_set bypasses read-set validation. This is the
//   classical no-write-stale-read gap. The state machine here has
//   FOUR transition kinds:
//
//     - default_si_begin_step           (same as SSI begin)
//     - default_si_commit_validated     (non-empty write_set, validation
//                                        must pass)
//     - default_si_commit_bypass        (empty write_set, no validation,
//                                        record still emitted)
//     - default_si_commit_abort         (validation fails on non-empty
//                                        write_set)
//
//   Under the bypass transition, an OpRecord with empty write_set is
//   appended to the trace, but the agent may have read stale values
//   relative to concurrent committers. The empirically-observed
//   3 % rate in the triage workload (paper Sec. 5.5) is the manifestation.
//
// CONDITIONAL THEOREM
//   We prove that under the "all-writers" workload hypothesis ---
//   every record in the trace has non-empty write_set --- default-SI
//   satisfies !A_1:
//
//     theorem_default_si_conditional_prevents_a1(s):
//       requires reachable(s)
//       requires all_records_have_writes(s.trace)
//       ensures !a1(s.trace)
//
//   The hypothesis is exactly the absence of bypass transitions in
//   any execution leading to s: a bypass transition appends an
//   empty-write-set record, which would violate the hypothesis at
//   the resulting state. Hence under the hypothesis, every commit
//   in the leading execution went through validation, and the SSI
//   safety argument applies.
//
// FIX HISTORY
//   v1: first draft
//   v2: moved two malformed #[trigger] annotations off the boolean
//       negation onto the write_set field access (Verus requires a
//       trigger to be a call/field/arith term); ASCII-only header.

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

pub open spec fn all_records_have_writes(h: Seq<OpRecord>) -> bool {
    forall |i: int| #![trigger h[i].write_set]
        0 <= i < h.len() ==> !h[i].write_set.is_empty()
}

// =====================================================================
// Section 2: State (identical to SSI)
// =====================================================================

pub struct PendingSnapshot {
    pub read_time: Time,
    pub read_values: Map<CellId, Value>,
}

pub struct DefaultSiState {
    pub store: Map<CellId, Value>,
    pub last_write: Map<CellId, Time>,
    pub pending: Map<AgentId, PendingSnapshot>,
    pub clock: Time,
    pub trace: Seq<OpRecord>,
}

pub open spec fn init_default_si_state() -> DefaultSiState {
    DefaultSiState {
        store: Map::<CellId, Value>::empty(),
        last_write: Map::<CellId, Time>::empty(),
        pending: Map::<AgentId, PendingSnapshot>::empty(),
        clock: 0,
        trace: Seq::<OpRecord>::empty(),
    }
}

pub open spec fn last_write_of(s: &DefaultSiState, c: CellId) -> Time {
    if s.last_write.contains_key(c) { s.last_write[c] } else { 0 }
}

pub open spec fn validation_passes(s: &DefaultSiState, ps: PendingSnapshot) -> bool {
    forall |c: CellId|
        #[trigger] ps.read_values.contains_key(c)
        ==> last_write_of(s, c) <= ps.read_time
}

// =====================================================================
// Section 3: Update specs (identical to SSI)
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
// Section 4: Four transitions
// =====================================================================

pub open spec fn can_begin(s: &DefaultSiState, agent: AgentId) -> bool {
    !s.pending.contains_key(agent)
}

pub open spec fn default_si_begin_step(
    s: &DefaultSiState,
    agent: AgentId,
    read_cells: Set<CellId>,
    s_new: &DefaultSiState,
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

pub open spec fn can_commit(s: &DefaultSiState, agent: AgentId) -> bool {
    s.pending.contains_key(agent)
}

// Validated commit: non-empty write_set, validation must pass.
pub open spec fn default_si_commit_validated_step(
    s: &DefaultSiState,
    agent: AgentId,
    write_set: Set<CellId>,
    write_values: Map<CellId, Value>,
    s_new: &DefaultSiState,
) -> bool {
    can_commit(s, agent)
    && !write_set.is_empty()
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

// Bypass commit: empty write_set, no validation. Appends an empty
// record. This is the no-write gap in default-SI.
pub open spec fn default_si_commit_bypass_step(
    s: &DefaultSiState,
    agent: AgentId,
    s_new: &DefaultSiState,
) -> bool {
    can_commit(s, agent)
    && s_new.clock == s.clock + 1
    && s_new.last_write == s.last_write
    && s_new.store == s.store
    && s_new.pending == s.pending.remove(agent)
    && s_new.trace == s.trace.push(OpRecord {
        agent: agent,
        read_set: s.pending[agent].read_values.dom(),
        read_values: s.pending[agent].read_values,
        read_time: s.pending[agent].read_time,
        write_set: Set::<CellId>::empty(),
        write_values: Map::<CellId, Value>::empty(),
        write_time: s_new.clock,
    })
}

// Abort: validation failed on a non-empty write_set commit attempt.
pub open spec fn default_si_commit_abort_step(
    s: &DefaultSiState,
    agent: AgentId,
    s_new: &DefaultSiState,
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
// Section 5: Invariants (identical to SSI; safety is the same)
// =====================================================================

pub open spec fn inv_clock_monotone(s: &DefaultSiState) -> bool {
    forall |i: int|
        0 <= i < s.trace.len()
        ==> #[trigger] s.trace[i].read_time < s.trace[i].write_time
}

pub open spec fn inv_record_writetime_le_clock(s: &DefaultSiState) -> bool {
    forall |i: int|
        0 <= i < s.trace.len()
        ==> #[trigger] s.trace[i].write_time <= s.clock
}

pub open spec fn inv_last_write_dominates(s: &DefaultSiState) -> bool {
    forall |i: int, c: CellId|
        0 <= i < s.trace.len()
        && #[trigger] s.trace[i].write_set.contains(c)
        ==> s.last_write.contains_key(c)
            && s.trace[i].write_time <= s.last_write[c]
}

pub open spec fn inv_pending_read_time_le_clock(s: &DefaultSiState) -> bool {
    forall |a: AgentId|
        #[trigger] s.pending.contains_key(a)
        ==> s.pending[a].read_time <= s.clock
}

pub open spec fn inv_no_intervening_write(s: &DefaultSiState) -> bool {
    forall |i: int, j: int, c: CellId|
        0 <= i < s.trace.len() && 0 <= j < s.trace.len()
        && #[trigger] s.trace[i].read_set.contains(c)
        && #[trigger] s.trace[j].write_set.contains(c)
        ==> !(s.trace[i].read_time < s.trace[j].write_time
              && s.trace[j].write_time < s.trace[i].write_time)
}

pub open spec fn inv_pending_finite(s: &DefaultSiState) -> bool {
    s.pending.dom().finite()
}

pub open spec fn inv_last_write_finite(s: &DefaultSiState) -> bool {
    s.last_write.dom().finite()
}

pub open spec fn all_invariants(s: &DefaultSiState) -> bool {
    inv_clock_monotone(s)
    && inv_record_writetime_le_clock(s)
    && inv_last_write_dominates(s)
    && inv_pending_read_time_le_clock(s)
    && inv_no_intervening_write(s)
    && inv_pending_finite(s)
    && inv_last_write_finite(s)
}

// =====================================================================
// Section 6: Safety from invariants
// =====================================================================

pub proof fn default_si_no_a1(s: &DefaultSiState)
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
    ensures all_invariants(&init_default_si_state())
{
    let s = init_default_si_state();
    assert(s.trace.len() == 0);
    assert(s.pending.dom() =~= Set::<AgentId>::empty());
    assert(s.last_write.dom() =~= Set::<CellId>::empty());
}

// =====================================================================
// Section 8: begin_step preserves
// =====================================================================

pub proof fn lemma_begin_preserves(
    s: &DefaultSiState,
    s_new: &DefaultSiState,
    agent: AgentId,
    read_cells: Set<CellId>,
)
    requires
        all_invariants(s),
        default_si_begin_step(s, agent, read_cells, s_new),
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
// Section 9: commit_validated preserves
//
// Identical to SSI commit_success_preserves; the !write_set.is_empty()
// precondition is additional but does not affect the invariant
// arguments (they are the same as in SSI).
// =====================================================================

pub proof fn lemma_commit_validated_preserves(
    s: &DefaultSiState,
    s_new: &DefaultSiState,
    agent: AgentId,
    write_set: Set<CellId>,
    write_values: Map<CellId, Value>,
)
    requires
        all_invariants(s),
        default_si_commit_validated_step(s, agent, write_set, write_values, s_new),
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
// Section 10: commit_abort preserves
// =====================================================================

pub proof fn lemma_commit_abort_preserves(
    s: &DefaultSiState,
    s_new: &DefaultSiState,
    agent: AgentId,
)
    requires
        all_invariants(s),
        default_si_commit_abort_step(s, agent, s_new),
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
// Section 11: Reachability with four transition kinds
// =====================================================================

pub open spec fn is_begin_successor(s_pre: &DefaultSiState, s: &DefaultSiState) -> bool {
    exists |a: AgentId, rc: Set<CellId>| default_si_begin_step(s_pre, a, rc, s)
}

pub open spec fn is_commit_validated_successor(s_pre: &DefaultSiState, s: &DefaultSiState) -> bool {
    exists |a: AgentId, ws: Set<CellId>, wv: Map<CellId, Value>|
        default_si_commit_validated_step(s_pre, a, ws, wv, s)
}

pub open spec fn is_commit_bypass_successor(s_pre: &DefaultSiState, s: &DefaultSiState) -> bool {
    exists |a: AgentId| default_si_commit_bypass_step(s_pre, a, s)
}

pub open spec fn is_commit_abort_successor(s_pre: &DefaultSiState, s: &DefaultSiState) -> bool {
    exists |a: AgentId| default_si_commit_abort_step(s_pre, a, s)
}

pub open spec fn reachable_step(s_pre: &DefaultSiState, s: &DefaultSiState) -> bool {
    is_begin_successor(s_pre, s)
    || is_commit_validated_successor(s_pre, s)
    || is_commit_bypass_successor(s_pre, s)
    || is_commit_abort_successor(s_pre, s)
}

pub open spec fn execution(states: Seq<DefaultSiState>) -> bool {
    states.len() > 0
    && states[0] == init_default_si_state()
    && (forall |k: int| 0 <= k < states.len() - 1
        ==> #[trigger] reachable_step(&states[k], &states[k + 1]))
}

pub open spec fn reachable(s: &DefaultSiState) -> bool {
    exists |states: Seq<DefaultSiState>|
        #[trigger] execution(states) && states.last() == *s
}

// =====================================================================
// Section 12: Conditional invariants lemma.
//
// The conditional hypothesis is all_records_have_writes(s.trace).
// Under this hypothesis, the bypass transition cannot have fired in
// any prefix of the execution (it would have added an empty-write-set
// record that would survive in the trace). So at every state in the
// execution, the trace contains only non-empty-write-set records,
// the bypass case is excluded, and the validated-commit case carries
// the same argument as in SSI.
// =====================================================================

// Key observation: trace grows monotonically, so if final state has
// all-non-empty records, every prefix also does.
pub proof fn lemma_prefix_preserves_writes(
    full: Seq<OpRecord>,
    k: int,
)
    requires
        0 <= k <= full.len(),
        all_records_have_writes(full),
    ensures
        all_records_have_writes(full.subrange(0, k)),
{
    let prefix = full.subrange(0, k);
    assert forall |i: int| #![trigger prefix[i].write_set]
        0 <= i < prefix.len()
        implies !prefix[i].write_set.is_empty()
    by {
        assert(prefix[i] == full[i]);
    };
}

pub proof fn lemma_states_imply_invariants(states: Seq<DefaultSiState>)
    requires
        execution(states),
        all_records_have_writes(states.last().trace),
    ensures
        all_invariants(&states.last())
    decreases states.len()
{
    if states.len() == 1 {
        assert(states[0] == init_default_si_state());
        assert(states.last() == states[0]);
        lemma_init_invariants();
    } else {
        let prefix = states.drop_last();
        assert(prefix.len() == states.len() - 1);
        assert(prefix.len() >= 1);
        assert(prefix[0] == states[0]);

        assert forall |i: int| 0 <= i < prefix.len() - 1 implies
            #[trigger] reachable_step(&prefix[i], &prefix[i + 1]) by
        {
            assert(prefix[i] == states[i]);
            assert(prefix[i + 1] == states[i + 1]);
            assert(0 <= i < states.len() - 1);
        };
        assert(execution(prefix));

        let last_idx = (states.len() - 2) as int;
        assert(0 <= last_idx < states.len() - 1);
        assert(prefix.last() == states[last_idx]);
        assert(states.last() == states[last_idx + 1]);
        assert(reachable_step(&states[last_idx], &states[last_idx + 1]));

        let s_pre = states[last_idx];
        let s_cur = states.last();
        assert(prefix.last() == s_pre);
        assert(reachable_step(&s_pre, &s_cur));

        // Establish prefix.last().trace has all writes.
        // Case analysis on which transition fired:
        //   * begin / abort: s_cur.trace == s_pre.trace, prefix's
        //     trace is identical to s_cur.trace, hypothesis carries.
        //   * commit_validated: s_cur.trace = s_pre.trace.push(non-empty),
        //     so s_pre.trace is s_cur.trace minus last record. By
        //     subrange lemma, all-writes carries to prefix.
        //   * commit_bypass: s_cur.trace = s_pre.trace.push(empty). The
        //     last record has empty write_set. But all_records_have_writes
        //     on s_cur.trace says every record is non-empty. Contradiction.
        //     This case is impossible.
        if is_commit_bypass_successor(&s_pre, &s_cur) {
            let a = choose |a: AgentId| default_si_commit_bypass_step(&s_pre, a, &s_cur);
            assert(default_si_commit_bypass_step(&s_pre, a, &s_cur));
            let n = s_pre.trace.len() as int;
            assert(s_cur.trace.len() == n + 1);
            assert(s_cur.trace[n].write_set == Set::<CellId>::empty());
            assert(s_cur.trace[n].write_set.is_empty());
            // But all_records_have_writes(s_cur.trace) says !s_cur.trace[n].write_set.is_empty().
            assert(0 <= n < s_cur.trace.len());
            assert(!s_cur.trace[n].write_set.is_empty());
            assert(false);
        }

        // Establish prefix-trace satisfies all_records_have_writes.
        assert(prefix.last().trace == s_pre.trace);
        if is_begin_successor(&s_pre, &s_cur) {
            let pair = choose |a: AgentId, rc: Set<CellId>|
                default_si_begin_step(&s_pre, a, rc, &s_cur);
            assert(s_cur.trace == s_pre.trace);
        } else if is_commit_validated_successor(&s_pre, &s_cur) {
            let triple = choose |a: AgentId, ws: Set<CellId>, wv: Map<CellId, Value>|
                default_si_commit_validated_step(&s_pre, a, ws, wv, &s_cur);
            let a = triple.0;
            let ws = triple.1;
            let wv = triple.2;
            assert(default_si_commit_validated_step(&s_pre, a, ws, wv, &s_cur));
            // s_cur.trace = s_pre.trace.push(r). s_pre.trace is s_cur.trace.subrange(0, len-1).
            assert(s_cur.trace == s_pre.trace.push(s_cur.trace[s_pre.trace.len() as int]));
            assert(s_pre.trace == s_cur.trace.subrange(0, s_pre.trace.len() as int));
            lemma_prefix_preserves_writes(s_cur.trace, s_pre.trace.len() as int);
        } else {
            // commit_abort: s_cur.trace == s_pre.trace
            assert(is_commit_abort_successor(&s_pre, &s_cur));
            let a = choose |a: AgentId| default_si_commit_abort_step(&s_pre, a, &s_cur);
            assert(default_si_commit_abort_step(&s_pre, a, &s_cur));
            assert(s_cur.trace == s_pre.trace);
        }

        assert(all_records_have_writes(s_pre.trace));
        assert(all_records_have_writes(prefix.last().trace));

        // Recursive call.
        lemma_states_imply_invariants(prefix);
        assert(all_invariants(&prefix.last()));
        assert(all_invariants(&s_pre));

        // Dispatch on transition kind.
        if is_begin_successor(&s_pre, &s_cur) {
            let pair = choose |a: AgentId, rc: Set<CellId>|
                default_si_begin_step(&s_pre, a, rc, &s_cur);
            let a = pair.0;
            let rc = pair.1;
            assert(default_si_begin_step(&s_pre, a, rc, &s_cur));
            lemma_begin_preserves(&s_pre, &s_cur, a, rc);
        } else if is_commit_validated_successor(&s_pre, &s_cur) {
            let triple = choose |a: AgentId, ws: Set<CellId>, wv: Map<CellId, Value>|
                default_si_commit_validated_step(&s_pre, a, ws, wv, &s_cur);
            let a = triple.0;
            let ws = triple.1;
            let wv = triple.2;
            assert(default_si_commit_validated_step(&s_pre, a, ws, wv, &s_cur));
            lemma_commit_validated_preserves(&s_pre, &s_cur, a, ws, wv);
        } else {
            assert(is_commit_abort_successor(&s_pre, &s_cur));
            let a = choose |a: AgentId| default_si_commit_abort_step(&s_pre, a, &s_cur);
            assert(default_si_commit_abort_step(&s_pre, a, &s_cur));
            lemma_commit_abort_preserves(&s_pre, &s_cur, a);
        }
    }
}

pub proof fn lemma_invariants_inductive_conditional(s: &DefaultSiState)
    requires
        reachable(s),
        all_records_have_writes(s.trace),
    ensures
        all_invariants(s)
{
    let states = choose |states: Seq<DefaultSiState>|
        #[trigger] execution(states) && states.last() == *s;
    assert(states.last().trace == s.trace);
    lemma_states_imply_invariants(states);
    assert(states.last() == *s);
}

// =====================================================================
// Section 13: Conditional theorem
// =====================================================================

pub proof fn theorem_default_si_conditional_prevents_a1(s: &DefaultSiState)
    requires
        reachable(s),
        all_records_have_writes(s.trace),
    ensures
        !a1(s.trace)
{
    lemma_invariants_inductive_conditional(s);
    default_si_no_a1(s);
}

} // verus!