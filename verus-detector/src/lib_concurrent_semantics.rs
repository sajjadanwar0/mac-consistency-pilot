// =====================================================================
// Verus proof: concurrent-semantics lift for the mac-consistency runtime.
//
// COMPILE
//   verus --crate-type=lib src/lib_concurrent_semantics.rs
//
// PURPOSE (paper sec:concurrent-semantics)
//   Lift the *sequential* refinement proofs to a multi-threaded execution
//   under an ABSTRACT mutex protocol. We model each runtime step as an
//   atomic event of one of four kinds -- LockAcquire / LockRelease / Read /
//   Write -- over a state <holders, values>. A trace is "well-formed" iff
//   every event is enabled from its preceding state (step_enabled encodes
//   the abstract Acquire/Release protocol). We then prove that the per-cell
//   access events of a well-formed trace project to a strictly serialised
//   sequence -- the sequential shape the refinement proofs consume.
//
// WHAT THIS IS / IS NOT
//   IS:  a mechanically-verified identification of the precise abstract
//        protocol the sequential refinement needs, with ZERO axioms,
//        ZERO external_body, ZERO assume, ZERO admit. The lemmas are
//        structural (induction over the trace).
//   NOT: a verification that std::sync::Mutex IMPLEMENTS this protocol.
//        That correspondence is the RustBelt residual (lib_rustbelt_interface.rs),
//        and the bounded weak-memory soundness of the protocol itself is the
//        GenMC RC11 check (weakmem/litmus_mutex_a1.c).
//
// This file replaces the placeholder that previously duplicated
// lib_probabilistic_a1.rs.
// =====================================================================
#![allow(unused_imports)]
#![allow(dead_code)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Carriers
// ---------------------------------------------------------------------
pub type AgentId = int;
pub type CellId  = int;
pub type Value   = int;
pub type Time    = int;

pub enum Kind { Acquire, Release, Read, Write }

pub struct Event {
    pub kind:  Kind,
    pub agent: AgentId,
    pub cell:  CellId,
    pub time:  Time,
    pub val:   Value,
}

pub struct State {
    pub holders: Map<CellId, AgentId>,  // absent key == cell unlocked
    pub values:  Map<CellId, Value>,    // absent key == cell never written
}

pub open spec fn init() -> State {
    State { holders: Map::empty(), values: Map::empty() }
}

// is the event a lock op on cell c?
pub open spec fn is_lock_on(e: Event, c: CellId) -> bool {
    (e.kind == Kind::Acquire || e.kind == Kind::Release) && e.cell == c
}
// is the event a memory access on cell c?
pub open spec fn is_access_on(e: Event, c: CellId) -> bool {
    (e.kind == Kind::Read || e.kind == Kind::Write) && e.cell == c
}

// ---------------------------------------------------------------------
// Operational semantics
// ---------------------------------------------------------------------
pub open spec fn step(s: State, e: Event) -> State {
    match e.kind {
        Kind::Acquire => State { holders: s.holders.insert(e.cell, e.agent), values: s.values },
        Kind::Release => State { holders: s.holders.remove(e.cell),          values: s.values },
        Kind::Read    => s,
        Kind::Write   => State { holders: s.holders, values: s.values.insert(e.cell, e.val) },
    }
}

// step_enabled encodes the abstract mutex protocol.
pub open spec fn step_enabled(s: State, e: Event) -> bool {
    match e.kind {
        Kind::Acquire => !s.holders.contains_key(e.cell),
        Kind::Release => s.holders.contains_key(e.cell) && s.holders[e.cell] == e.agent,
        Kind::Read    => s.holders.contains_key(e.cell) && s.holders[e.cell] == e.agent
                         && (s.values.contains_key(e.cell) ==> s.values[e.cell] == e.val),
        Kind::Write   => s.holders.contains_key(e.cell) && s.holders[e.cell] == e.agent,
    }
}

// State after the first i events of a trace.
pub open spec fn state_after(tr: Seq<Event>, i: int) -> State
    decreases i,
{
    if i <= 0 { init() } else { step(state_after(tr, i - 1), tr[i - 1]) }
}

pub open spec fn well_formed(tr: Seq<Event>) -> bool {
    forall |i: int| #![trigger step_enabled(state_after(tr, i), tr[i])]
        0 <= i < tr.len() ==> step_enabled(state_after(tr, i), tr[i])
}

// =====================================================================
// Lemma A (helper): state_after depends only on the prefix.
// =====================================================================
pub proof fn lemma_state_after_prefix(tr: Seq<Event>, m: int, i: int)
    requires 0 <= i <= m <= tr.len(),
    ensures  state_after(tr.subrange(0, m), i) == state_after(tr, i),
    decreases i,
{
    if i <= 0 {
        // both sides are init()
    } else {
        lemma_state_after_prefix(tr, m, i - 1);
        // subrange index: (tr[0..m])[i-1] == tr[i-1] for i-1 < m
        assert(tr.subrange(0, m)[i - 1] == tr[i - 1]);
        // state_after(sub, i) = step(state_after(sub,i-1), sub[i-1])
        //                     = step(state_after(tr,i-1),  tr[i-1]) = state_after(tr,i)
    }
}

// =====================================================================
// Theorem 1: prefix monotonicity.
// Every prefix of a well-formed trace is well-formed.
// =====================================================================
pub proof fn lemma_prefix_monotonicity(tr: Seq<Event>, m: int)
    requires well_formed(tr), 0 <= m <= tr.len(),
    ensures  well_formed(tr.subrange(0, m)),
{
    let p = tr.subrange(0, m);
    assert(p.len() == m);
    assert forall |i: int| #![trigger step_enabled(state_after(p, i), p[i])]
        0 <= i < p.len() implies step_enabled(state_after(p, i), p[i]) by {
        lemma_state_after_prefix(tr, m, i);          // state_after(p,i) == state_after(tr,i)
        assert(p[i] == tr[i]);                        // subrange index
        assert(step_enabled(state_after(tr, i), tr[i]));   // from well_formed(tr) at i
    }
}

// =====================================================================
// Theorem 2: mutex exclusion (structural).
// At any prefix state each cell has at most one lock holder.
// (Structural consequence of the Map representation; recorded for the
// narrative role the paper assigns it.)
// =====================================================================
pub proof fn lemma_mutex_exclusion(tr: Seq<Event>, i: int, c: CellId, a1: AgentId, a2: AgentId)
    requires
        state_after(tr, i).holders.contains_key(c),
        state_after(tr, i).holders[c] == a1,
        state_after(tr, i).holders[c] == a2,
    ensures a1 == a2,
{
    // a1 == holders[c] == a2.
}

// =====================================================================
// Theorem 3: access implies lock held.
// Every Read/Write in a well-formed trace is performed by the agent
// currently holding the accessed cell's lock.
// =====================================================================
pub proof fn lemma_access_implies_lock_held(tr: Seq<Event>, i: int)
    requires
        well_formed(tr),
        0 <= i < tr.len(),
        tr[i].kind == Kind::Read || tr[i].kind == Kind::Write,
    ensures
        state_after(tr, i).holders.contains_key(tr[i].cell),
        state_after(tr, i).holders[tr[i].cell] == tr[i].agent,
{
    assert(step_enabled(state_after(tr, i), tr[i]));   // instantiate well_formed at i
}

// =====================================================================
// Theorem 4: reads observe the current value (no torn reads).
// =====================================================================
pub proof fn lemma_reads_observe_current_value(tr: Seq<Event>, i: int)
    requires
        well_formed(tr),
        0 <= i < tr.len(),
        tr[i].kind == Kind::Read,
        state_after(tr, i).values.contains_key(tr[i].cell),
    ensures
        state_after(tr, i).values[tr[i].cell] == tr[i].val,
{
    assert(step_enabled(state_after(tr, i), tr[i]));   // Read case of step_enabled
}

// =====================================================================
// Theorem 5 (helper): holder-change requires an intervening lock event.
// If no LockAcquire/LockRelease on c occurs in [a, b), the lock-holder of
// c (membership and identity) is unchanged from a to b.
// =====================================================================
pub proof fn lemma_holder_unchanged_without_lock_event(tr: Seq<Event>, a: int, b: int, c: CellId)
    requires
        0 <= a <= b <= tr.len(),
        forall |k: int| a <= k < b ==> !(#[trigger] is_lock_on(tr[k], c)),
    ensures
        state_after(tr, a).holders.contains_key(c) == state_after(tr, b).holders.contains_key(c),
        state_after(tr, a).holders.contains_key(c)
            ==> state_after(tr, a).holders[c] == state_after(tr, b).holders[c],
    decreases b - a,
{
    if b <= a {
        // a == b
    } else {
        // The sub-forall over [a, b-1) holds, so recurse.
        assert(forall |k: int| a <= k < b - 1 ==> !(#[trigger] is_lock_on(tr[k], c)));
        lemma_holder_unchanged_without_lock_event(tr, a, b - 1, c);

        let e  = tr[b - 1];
        let sp = state_after(tr, b - 1);
        assert(!is_lock_on(e, c));   // instantiate the requires-forall at k = b-1

        // step(sp, e) leaves holders-at-c unchanged in every non-(lock-on-c) case.
        match e.kind {
            Kind::Read    => {}                   // holders unchanged entirely
            Kind::Write   => {}                   // holders unchanged entirely
            Kind::Acquire => { assert(e.cell != c); }  // insert at e.cell != c
            Kind::Release => { assert(e.cell != c); }  // remove at e.cell != c
        }
        // state_after(tr,b) == step(sp,e); holders-at-c equals sp's; chain with IH.
    }
}

// =====================================================================
// Theorem 6: distinct-agent access separation.
// Two accesses to the same cell by different agents are separated by a
// LockAcquire/LockRelease on that cell strictly between them.
// =====================================================================
pub proof fn lemma_distinct_agent_access_separation(tr: Seq<Event>, i: int, j: int, c: CellId)
    requires
        well_formed(tr),
        0 <= i < j < tr.len(),
        is_access_on(tr[i], c),
        is_access_on(tr[j], c),
        tr[i].agent != tr[j].agent,
    ensures
        exists |k: int| i < k < j && is_lock_on(tr[k], c),
{
    lemma_access_implies_lock_held(tr, i);   // holder at state_after(tr,i)[c] == tr[i].agent
    lemma_access_implies_lock_held(tr, j);   // holder at state_after(tr,j)[c] == tr[j].agent

    if forall |k: int| i <= k < j ==> !(#[trigger] is_lock_on(tr[k], c)) {
        lemma_holder_unchanged_without_lock_event(tr, i, j, c);
        // both states contain c, and holders[c] preserved => agents equal
        assert(state_after(tr, i).holders[c] == state_after(tr, j).holders[c]);
        assert(tr[i].agent == tr[j].agent);
        assert(false);
    }
    // hence a lock-on-c event exists in [i, j); it cannot be i (an access),
    // so it lies strictly between.
    let k = choose |k: int| i <= k < j && is_lock_on(tr[k], c);
    assert(is_access_on(tr[i], c));   // tr[i] is an access, not a lock
    assert(k != i);
    assert(i < k < j && is_lock_on(tr[k], c));
}

// =====================================================================
// Theorem 7 (non-vacuity): a well-formed trace containing a Read exists.
// Witness: agent 1 acquires cell 0, then reads it (value unconstrained
// because the cell has never been written). Establishes the universal
// theorems above are not vacuously true.
// =====================================================================
pub proof fn lemma_nonvacuous_witness()
    ensures
        exists |tr: Seq<Event>| #![trigger well_formed(tr)]
            well_formed(tr) && tr.len() == 2 && tr[1].kind == Kind::Read,
{
    let e0 = Event { kind: Kind::Acquire, agent: 1, cell: 0, time: 0, val: 0 };
    let e1 = Event { kind: Kind::Read,    agent: 1, cell: 0, time: 1, val: 7 };
    let tr = seq![e0, e1];

    assert(tr.len() == 2);
    assert(tr[0] == e0);
    assert(tr[1] == e1);

    // i = 0: Acquire on the empty holder map is enabled.
    assert(state_after(tr, 0) == init());
    assert(step_enabled(state_after(tr, 0), tr[0]));

    // i = 1: after the acquire, agent 1 holds cell 0; the read is enabled
    // (cell 0 not in values, so the value clause is vacuous).
    assert(state_after(tr, 1) == step(init(), e0));
    assert(state_after(tr, 1).holders.contains_key(0));
    assert(state_after(tr, 1).holders[0] == 1);
    assert(!state_after(tr, 1).values.contains_key(0));
    assert(step_enabled(state_after(tr, 1), tr[1]));

    assert forall |i: int| #![trigger step_enabled(state_after(tr, i), tr[i])]
        0 <= i < tr.len() implies step_enabled(state_after(tr, i), tr[i]) by {
        if i == 0 {} else { assert(i == 1); }
    }
    assert(well_formed(tr));
}

} // verus!