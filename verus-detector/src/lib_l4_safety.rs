// =====================================================================
// Verus proof: L_4 safety for a registry-validating runtime that
// prevents A_2 (phantom tool) under arbitrary registry churn.
//
// COMPILE
//   verus --crate-type=lib src/lib_l4_safety.rs
//
// A_2 (phantom tool): an operation plans a call against the registry it
// observed, and by the time the call is dispatched the tool has been
// revoked or re-signed, so the call reaches a tool that no longer matches
// the plan. It is a property of the DISPATCH, so each operation records
// what the live registry held for its planned tool at the instant it
// dispatched (its commit). This is the TLA+ predicate
// (Anomalies.tla PhantomTool: planned tool in read_registry, not in
// write_registry, the registry recorded at commit), with re-signing added
// because a signature change is the same hazard as a removal.
//
// 2026-09-16  round 29 (audit finding G2). OVERRULED, all of the previous
// contents of this file:
//   - L_4b ("snapshot isolation suppresses A_2 by construction") compared
//     resolve_via_snapshot(so) with pinned_sig_of(so), the same expression,
//     with an empty proof body. It said nothing about the registry.
//   - a2_witness read the CURRENT live registry, so any later revocation
//     turned an old, correctly dispatched operation into a "phantom"; the
//     model had no registry mutation at all, which is why that never showed.
//   - L_4a held only at the commit instant, and L_4c, L_4d, L_4e restated
//     their preconditions. None was a statement about executions.
// Now: registry churn (register, re-sign, revoke) is a step; validation at
// dispatch is an inductive invariant preserved by every step; an unvalidated
// dispatch reaches A_2 in a concrete four-step execution; and resolving the
// binding from a pinned snapshot -- the old L_4b discipline -- also reaches
// A_2, because the snapshot changes what the operation believes, not what
// its call reaches.
//
// TRUST BASE: zero axioms, zero external_body, zero assume, zero admit.

#![allow(unused_imports)]
#![allow(dead_code)]
use vstd::prelude::*;

verus! {

pub type ToolId    = int;
pub type Signature = int;
pub type OpId      = int;
pub type Time      = int;

pub struct Operation {
    pub started:          bool,
    pub planned_tool:     ToolId,
    /// the live signature of the planned tool when the operation planned
    pub pinned_sig:       Signature,
    pub committed:        bool,
    pub aborted:          bool,
    /// recorded at dispatch: the planned tool was in the live registry
    pub dispatch_present: bool,
    /// recorded at dispatch: its live signature then (when present)
    pub dispatch_sig:     Signature,
}

pub struct RegistryState {
    pub now:      Time,
    pub registry: Map<ToolId, Signature>,
    pub ops:      Map<OpId, Operation>,
}

pub open spec fn initial_state() -> RegistryState {
    RegistryState { now: 0, registry: Map::empty(), ops: Map::empty() }
}

/// A_2: a dispatched (committed, unaborted) operation whose call reached a
/// revoked tool or a tool re-signed since it planned.
pub open spec fn a2_witness(s: RegistryState, o: OpId) -> bool {
    &&& s.ops.contains_key(o)
    &&& s.ops[o].committed
    &&& !s.ops[o].aborted
    &&& (!s.ops[o].dispatch_present || s.ops[o].dispatch_sig != s.ops[o].pinned_sig)
}

// ---------------------------------------------------------------------
// Steps
// ---------------------------------------------------------------------

pub open spec fn begin_valid(s: RegistryState, o: OpId, t: ToolId) -> bool {
    !s.ops.contains_key(o) && s.registry.contains_key(t)
}

/// plan: the operation pins the live signature of its planned tool
pub open spec fn step_begin(s: RegistryState, o: OpId, t: ToolId) -> RegistryState
    recommends begin_valid(s, o, t)
{
    RegistryState {
        now: s.now + 1,
        ops: s.ops.insert(o, Operation {
            started:          true,
            planned_tool:     t,
            pinned_sig:       s.registry[t],
            committed:        false,
            aborted:          false,
            dispatch_present: false,
            dispatch_sig:     0,
        }),
        ..s
    }
}

/// churn: publish a tool or re-sign it
pub open spec fn step_register(s: RegistryState, t: ToolId, sig: Signature) -> RegistryState {
    RegistryState { now: s.now + 1, registry: s.registry.insert(t, sig), ..s }
}

/// churn: revoke a tool
pub open spec fn step_unregister(s: RegistryState, t: ToolId) -> RegistryState {
    RegistryState { now: s.now + 1, registry: s.registry.remove(t), ..s }
}

/// the record an operation carries after dispatching against `live`
pub open spec fn dispatched(op: Operation, live: Map<ToolId, Signature>) -> Operation {
    Operation {
        committed:        true,
        dispatch_present: live.contains_key(op.planned_tool),
        dispatch_sig:     if live.contains_key(op.planned_tool) { live[op.planned_tool] } else { op.dispatch_sig },
        ..op
    }
}

/// L_4's discipline: dispatch only if the planned tool is still live with
/// the signature the operation planned against.
pub open spec fn commit_valid(s: RegistryState, o: OpId) -> bool {
    &&& s.ops.contains_key(o)
    &&& s.ops[o].started
    &&& !s.ops[o].committed
    &&& !s.ops[o].aborted
    &&& s.registry.contains_key(s.ops[o].planned_tool)
    &&& s.registry[s.ops[o].planned_tool] == s.ops[o].pinned_sig
}

/// dispatch (commit) against the live registry. The L_4 runtime takes this
/// step only under commit_valid; a runtime without validation takes it for
/// any open operation.
pub open spec fn step_commit(s: RegistryState, o: OpId) -> RegistryState {
    RegistryState { now: s.now + 1, ops: s.ops.insert(o, dispatched(s.ops[o], s.registry)), ..s }
}

pub open spec fn abort_valid(s: RegistryState, o: OpId) -> bool {
    s.ops.contains_key(o) && !s.ops[o].committed && !s.ops[o].aborted
}

pub open spec fn step_abort(s: RegistryState, o: OpId) -> RegistryState {
    RegistryState { now: s.now + 1, ops: s.ops.insert(o, Operation { aborted: true, ..s.ops[o] }), ..s }
}

// ---------------------------------------------------------------------
// The invariant and its preservation by every step
// ---------------------------------------------------------------------

pub open spec fn inv_l4(s: RegistryState) -> bool {
    forall |o: OpId| #![trigger s.ops[o]]
        s.ops.contains_key(o) && s.ops[o].committed && !s.ops[o].aborted
        ==> s.ops[o].dispatch_present && s.ops[o].dispatch_sig == s.ops[o].pinned_sig
}

pub proof fn lemma_initial_inv_l4()
    ensures inv_l4(initial_state()),
{
    assert(initial_state().ops =~= Map::<OpId, Operation>::empty());
}

pub proof fn lemma_begin_preserves_inv_l4(s: RegistryState, o: OpId, t: ToolId)
    requires inv_l4(s), begin_valid(s, o, t),
    ensures inv_l4(step_begin(s, o, t)),
{
    let s2 = step_begin(s, o, t);
    assert forall |x: OpId| #![trigger s2.ops[x]]
        s2.ops.contains_key(x) && s2.ops[x].committed && !s2.ops[x].aborted
        implies s2.ops[x].dispatch_present && s2.ops[x].dispatch_sig == s2.ops[x].pinned_sig
    by {
        if x == o {
            assert(!s2.ops[x].committed);
        } else {
            assert(s2.ops[x] == s.ops[x]);
            assert(s.ops.contains_key(x));
        }
    }
}

/// Registry churn cannot create A_2: A_2 is about what a dispatch reached,
/// and churn changes no dispatch record.
pub proof fn lemma_register_preserves_inv_l4(s: RegistryState, t: ToolId, sig: Signature)
    requires inv_l4(s),
    ensures inv_l4(step_register(s, t, sig)),
{
    let s2 = step_register(s, t, sig);
    assert forall |x: OpId| #![trigger s2.ops[x]]
        s2.ops.contains_key(x) && s2.ops[x].committed && !s2.ops[x].aborted
        implies s2.ops[x].dispatch_present && s2.ops[x].dispatch_sig == s2.ops[x].pinned_sig
    by {
        assert(s2.ops[x] == s.ops[x]);
        assert(s.ops.contains_key(x));
    }
}

pub proof fn lemma_unregister_preserves_inv_l4(s: RegistryState, t: ToolId)
    requires inv_l4(s),
    ensures inv_l4(step_unregister(s, t)),
{
    let s2 = step_unregister(s, t);
    assert forall |x: OpId| #![trigger s2.ops[x]]
        s2.ops.contains_key(x) && s2.ops[x].committed && !s2.ops[x].aborted
        implies s2.ops[x].dispatch_present && s2.ops[x].dispatch_sig == s2.ops[x].pinned_sig
    by {
        assert(s2.ops[x] == s.ops[x]);
        assert(s.ops.contains_key(x));
    }
}

pub proof fn lemma_commit_preserves_inv_l4(s: RegistryState, o: OpId)
    requires inv_l4(s), commit_valid(s, o),
    ensures inv_l4(step_commit(s, o)),
{
    let s2 = step_commit(s, o);
    assert forall |x: OpId| #![trigger s2.ops[x]]
        s2.ops.contains_key(x) && s2.ops[x].committed && !s2.ops[x].aborted
        implies s2.ops[x].dispatch_present && s2.ops[x].dispatch_sig == s2.ops[x].pinned_sig
    by {
        if x == o {
            assert(s2.ops[o] == dispatched(s.ops[o], s.registry));
            assert(s.registry.contains_key(s.ops[o].planned_tool));
            assert(s2.ops[o].planned_tool == s.ops[o].planned_tool);
            assert(s2.ops[o].pinned_sig == s.ops[o].pinned_sig);
            assert(s2.ops[o].dispatch_present);
            assert(s2.ops[o].dispatch_sig == s.registry[s.ops[o].planned_tool]);
        } else {
            assert(s2.ops[x] == s.ops[x]);
            assert(s.ops.contains_key(x));
        }
    }
}

pub proof fn lemma_abort_preserves_inv_l4(s: RegistryState, o: OpId)
    requires inv_l4(s), abort_valid(s, o),
    ensures inv_l4(step_abort(s, o)),
{
    let s2 = step_abort(s, o);
    assert forall |x: OpId| #![trigger s2.ops[x]]
        s2.ops.contains_key(x) && s2.ops[x].committed && !s2.ops[x].aborted
        implies s2.ops[x].dispatch_present && s2.ops[x].dispatch_sig == s2.ops[x].pinned_sig
    by {
        if x == o {
            assert(s2.ops[x].aborted);
        } else {
            assert(s2.ops[x] == s.ops[x]);
            assert(s.ops.contains_key(x));
        }
    }
}

/// THEOREM L_4: every state the validating runtime reaches from
/// initial_state -- through any interleaving of plans, dispatches, aborts,
/// and registry churn -- satisfies inv_l4 (the lemmas above), and no
/// operation in such a state is an A_2 witness.
pub proof fn lemma_l4_no_a2(s: RegistryState)
    requires inv_l4(s),
    ensures forall |o: OpId| #![trigger a2_witness(s, o)] !a2_witness(s, o),
{
    assert forall |o: OpId| #![trigger a2_witness(s, o)] !a2_witness(s, o) by {
        if s.ops.contains_key(o) && s.ops[o].committed && !s.ops[o].aborted {
            assert(s.ops[o].dispatch_present && s.ops[o].dispatch_sig == s.ops[o].pinned_sig);
        }
    }
}

// ---------------------------------------------------------------------
// Non-vacuity: concrete executions that reach A_2 without validation
// ---------------------------------------------------------------------

/// Publish tool 7, plan against it, re-sign it, dispatch without validation.
/// Validation would have refused (and the abort that replaces the dispatch
/// keeps the invariant); the unvalidated dispatch is an A_2 witness.
pub proof fn lemma_unvalidated_dispatch_reaches_a2()
    ensures ({
        let s1 = step_register(initial_state(), 7, 1);
        let s2 = step_begin(s1, 0, 7);
        let s3 = step_register(s2, 7, 2);
        &&& begin_valid(s1, 0, 7)
        &&& inv_l4(s3)
        &&& !commit_valid(s3, 0)
        &&& abort_valid(s3, 0)
        &&& a2_witness(step_commit(s3, 0), 0)
    }),
{
    let s0 = initial_state();
    let s1 = step_register(s0, 7, 1);
    assert(s1.registry.contains_key(7) && s1.registry[7] == 1);
    assert(s1.ops == s0.ops);
    assert(!s1.ops.contains_key(0));
    let s2 = step_begin(s1, 0, 7);
    assert(s2.ops.contains_key(0));
    assert(s2.ops[0].pinned_sig == 1);
    assert(s2.ops[0].planned_tool == 7);
    assert(s2.ops[0].started && !s2.ops[0].committed && !s2.ops[0].aborted);
    let s3 = step_register(s2, 7, 2);
    assert(s3.ops == s2.ops);
    assert(s3.registry.contains_key(7) && s3.registry[7] == 2);
    assert(!commit_valid(s3, 0));
    assert forall |x: OpId| #![trigger s3.ops[x]]
        s3.ops.contains_key(x) && s3.ops[x].committed && !s3.ops[x].aborted
        implies s3.ops[x].dispatch_present && s3.ops[x].dispatch_sig == s3.ops[x].pinned_sig
    by {
        assert(x == 0);
        assert(!s3.ops[x].committed);
    }
    let s4 = step_commit(s3, 0);
    assert(s4.ops[0] == dispatched(s3.ops[0], s3.registry));
    assert(s4.ops[0].dispatch_present);
    assert(s4.ops[0].dispatch_sig == 2);
    assert(s4.ops[0].pinned_sig == 1);
    assert(s4.ops[0].committed && !s4.ops[0].aborted);
    assert(a2_witness(s4, 0));
}

/// The OVERRULED L_4b discipline: an operation that resolves its tool binding
/// from a pinned snapshot of the registry.
pub struct SnapshotOp {
    pub planned_tool: ToolId,
    pub snapshot:     Map<ToolId, Signature>,
}

pub open spec fn resolve_via_snapshot(so: SnapshotOp) -> Signature
    recommends so.snapshot.contains_key(so.planned_tool)
{
    so.snapshot[so.planned_tool]
}

/// What L_4b proved still holds here -- the snapshot resolves to the pinned
/// signature -- and A_2 fires anyway: the tool is revoked between plan and
/// dispatch, and the call reaches the live registry, not the snapshot.
pub proof fn lemma_snapshot_resolution_does_not_prevent_a2()
    ensures ({
        let s1 = step_register(initial_state(), 7, 1);
        let so = SnapshotOp { planned_tool: 7, snapshot: s1.registry };
        let s2 = step_begin(s1, 0, 7);
        let s3 = step_unregister(s2, 7);
        &&& begin_valid(s1, 0, 7)
        &&& resolve_via_snapshot(so) == s2.ops[0].pinned_sig
        &&& !commit_valid(s3, 0)
        &&& a2_witness(step_commit(s3, 0), 0)
    }),
{
    let s0 = initial_state();
    let s1 = step_register(s0, 7, 1);
    assert(s1.registry.contains_key(7) && s1.registry[7] == 1);
    assert(s1.ops == s0.ops);
    assert(!s1.ops.contains_key(0));
    let so = SnapshotOp { planned_tool: 7, snapshot: s1.registry };
    assert(resolve_via_snapshot(so) == 1);
    let s2 = step_begin(s1, 0, 7);
    assert(s2.ops.contains_key(0));
    assert(s2.ops[0].pinned_sig == 1);
    assert(s2.ops[0].planned_tool == 7);
    assert(!s2.ops[0].committed && !s2.ops[0].aborted);
    let s3 = step_unregister(s2, 7);
    assert(s3.ops == s2.ops);
    assert(!s3.registry.contains_key(7));
    assert(!commit_valid(s3, 0));
    let s4 = step_commit(s3, 0);
    assert(s4.ops[0] == dispatched(s3.ops[0], s3.registry));
    assert(!s4.ops[0].dispatch_present);
    assert(s4.ops[0].committed && !s4.ops[0].aborted);
    assert(a2_witness(s4, 0));
}

} // verus!
