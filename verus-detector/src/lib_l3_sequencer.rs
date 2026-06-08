// lib_l3_sequencer.rs
//
// A_6 (tool-effect reordering) prevention for GENUINELY CONCURRENT external
// effects, via a commit-order sequencer (reorder buffer) -- not by excluding
// concurrency.
//
// Theorem L3a in lib_l3_safety.rs prevents A_6 by saga well-formedness:
// calls are issued strictly sequentially (each issued only after the previous
// completes), so completion order trivially equals issuance order. That is
// exclusion-by-construction -- it forbids the concurrent executions that
// alone could exhibit A_6, rather than ordering genuinely concurrent effects
// (the paper's Scope note for sec:l3-safety says so explicitly).
//
// This file closes that admitted gap. External effects complete in an
// ARBITRARY schedule `cstep` (any permutation of completion times -- real
// concurrency, including fully reversed). A commit-order sequencer
// externalizes effect k only once effects 0..k have all completed, so its
// externalization time is max(cstep[0..k]). We prove:
//
//   * thm_sequencer_orders_concurrent_effects: externalization time is
//     monotone in issuance index, for ANY completion schedule -- so the
//     observable order never inverts issuance order.
//   * cor_sequencer_no_a6: hence the externalized sequence exhibits no A_6.
//   * lemma_no_sequencer_admits_a6: the UNSEQUENCED baseline
//     (externalize-on-completion) with a reversed completion schedule DOES
//     exhibit A_6 -- the prevented phenomenon, non-vacuous.
//   * lemma_sequencer_fixes_concurrent_reorder: on that same reversed
//     schedule (completions genuinely out of issuance order) the sequenced
//     output has no A_6 -- so the no-A_6 result is not vacuously true by
//     completions already being in order.
//
// Trust base: none. Zero `assume`, zero `admit`, zero `external_body`.

use vstd::prelude::*;

verus! {

pub open spec fn maxn(a: nat, b: nat) -> nat {
    if a >= b { a } else { b }
}

// cstep[i] = the logical time at which call i (issuance index i) completes.
// Arbitrary: any schedule, including completions wildly out of issuance order.
// Sequenced externalization time of call k: it cannot externalize until every
// earlier-issued call has also completed, so it is the max completion time
// over indices 0..k.
pub open spec fn ext_time(cstep: Seq<nat>, k: nat) -> nat
    decreases k,
{
    if k == 0 {
        cstep[0]
    } else {
        maxn(ext_time(cstep, (k - 1) as nat), cstep[k as int])
    }
}

// The externalization-time sequence: position k is the time call k's effect
// becomes observable under the sequencer.
pub open spec fn ext_seq(cstep: Seq<nat>) -> Seq<nat> {
    Seq::new(cstep.len(), |k: int| ext_time(cstep, k as nat))
}

// A_6 (observable reordering): some earlier-issued effect i (< j) becomes
// observable strictly LATER than a later-issued effect j -- an inversion of
// issuance order in the externalization times `et`.
pub open spec fn a6_inversion(et: Seq<nat>, n: nat) -> bool {
    exists|i: int, j: int|
        #![trigger et[i], et[j]]
        0 <= i && i < j && j < n && et[i] > et[j]
}

// ---------------------------------------------------------------------------
// Genuine ordering theorem: the sequencer's externalization time is monotone
// in issuance index, FOR ANY completion schedule. This is the content --
// concurrent, out-of-order completions are ordered, not excluded.
// ---------------------------------------------------------------------------
pub proof fn thm_sequencer_orders_concurrent_effects(cstep: Seq<nat>, i: nat, j: nat)
    requires
        i <= j,
        j < cstep.len(),
    ensures
        ext_time(cstep, i) <= ext_time(cstep, j),
    decreases j - i,
{
    if i < j {
        thm_sequencer_orders_concurrent_effects(cstep, i, (j - 1) as nat);
        assert(ext_time(cstep, j)
            == maxn(ext_time(cstep, (j - 1) as nat), cstep[j as int]));
        // maxn(a, b) >= a, so ext_time(j) >= ext_time(j-1) >= ext_time(i).
    }
}

// Corollary: the externalized sequence has no A_6 inversion -- for any schedule.
pub proof fn cor_sequencer_no_a6(cstep: Seq<nat>)
    ensures
        !a6_inversion(ext_seq(cstep), cstep.len()),
{
    let et = ext_seq(cstep);
    assert forall|i: int, j: int|
        0 <= i && i < j && j < cstep.len() implies et[i] <= et[j] by {
        // et[k] == ext_time(cstep, k) by Seq::new indexing, in bounds here.
        assert(et[i] == ext_time(cstep, i as nat));
        assert(et[j] == ext_time(cstep, j as nat));
        thm_sequencer_orders_concurrent_effects(cstep, i as nat, j as nat);
    }
    // No pair i<j has et[i] > et[j], so a6_inversion is false.
    assert(!a6_inversion(et, cstep.len()));
}

// ---------------------------------------------------------------------------
// Non-vacuity: the prevented phenomenon. Without the sequencer, effects
// externalize on completion, so the externalization times ARE `cstep`. A
// reversed completion schedule then inverts issuance order = A_6.
// ---------------------------------------------------------------------------
pub proof fn lemma_no_sequencer_admits_a6()
    ensures
        exists|cstep: Seq<nat>| #[trigger] a6_inversion(cstep, cstep.len()),
{
    let cstep: Seq<nat> = seq![1nat, 0nat]; // call 0 completes at t=1, call 1 at t=0
    assert(cstep.len() == 2);
    assert(cstep[0] == 1nat && cstep[1] == 0nat);
    assert(a6_inversion(cstep, cstep.len())) by {
        assert(0 <= 0int && 0int < 1int && 1int < 2int && cstep[0int] > cstep[1int]);
    }
}

// Regime non-vacuity: on a schedule whose completions are genuinely out of
// issuance order (call 1 completes before call 0), the sequenced output still
// has no A_6 -- so cor_sequencer_no_a6 is not vacuous (it is not holding
// merely because completions were already ordered).
pub proof fn lemma_sequencer_fixes_concurrent_reorder()
    ensures
        exists|cstep: Seq<nat>|
            #![trigger ext_seq(cstep)]
            cstep.len() == 2
            && cstep[0] > cstep[1]                          // completions reversed
            && !a6_inversion(ext_seq(cstep), cstep.len()),  // yet no A_6 after sequencing
{
    let cstep: Seq<nat> = seq![1nat, 0nat];
    assert(cstep[0] > cstep[1]);
    // ext_time(cstep,0)=cstep[0]=1; ext_time(cstep,1)=maxn(1, cstep[1]=0)=1.
    assert(ext_time(cstep, 0) == 1nat);
    assert(ext_time(cstep, 1)
        == maxn(ext_time(cstep, 0), cstep[1int]));
    assert(ext_time(cstep, 1) == 1nat);
    cor_sequencer_no_a6(cstep);
}

} // verus!