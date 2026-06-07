// =====================================================================
// Verus proof: L_4 COMPOSITION -- the consistency lattice composes.
//
// COMPILE (this is a multi-module crate root; it re-verifies the three
// component modules and adds the composition on top):
//   verus --crate-type=lib src/lib_consistency_lattice.rs
//
// The three component safety results are proved, each in its own file:
//   * lib_l2_safety.rs  -- inv_l2 prevents A_1 (reads supported) and A_3
//   * lib_l3_safety.rs  -- satisfies_l3 prevents A_6 (saga reorder)
//   * lib_l4_safety.rs  -- no_a2_anywhere prevents A_2 (phantom tool)
//
// This root does NOT re-prove any of them. It establishes the COMPOSITION:
// because the three disciplines act on disjoint carriers (the value memory,
// the external-effect log, and the tool registry share no fields), the
// conjunction of the three invariants entails JOINT prevention of
// A_1 /\ A_3 /\ A_6 /\ A_2, and a step on one carrier cannot disturb another
// discipline (non-interference / framing). That disjointness is the entire
// content of the orthogonality argument the paper makes in prose; the lemmas
// below are its machine-checked form. Each component theorem enters by being
// CALLED on its projection -- there is no `assume` and no `admit`.
//
// SCOPE (stated honestly): this mechanises joint prevention at any state
// satisfying the three disciplines, plus the framing fact that a single-carrier
// step preserves the others. It does NOT prove the product transition system
// closed under arbitrary interleaving for L_3/L_4, which would require global
// step-preservation lemmas for those carriers (L_2 has its five; L_3/L_4 would
// need theirs lifted). The L_2 closure corollary below is included because L_2
// does have them.
// =====================================================================

#![allow(unused_imports)]
#![allow(dead_code)]
use vstd::prelude::*;

// Pull the three component proof modules into one crate.
pub mod lib_l2_safety;
pub mod lib_l3_safety;
pub mod lib_l4_safety;

// The three files share several top-level names (initial_state, commit_valid,
// step_commit, Time, ...), so we import ONLY the items the composition needs,
// each qualified by its module. Nothing imported here collides.
use crate::lib_l2_safety::{
    RuntimeState, TxnId, CellId, inv_l2, a3_witness,
    lemma_l2_reachable_no_a3, lemma_l2_reads_supported,
};
use crate::lib_l3_safety::{SagaRecord, satisfies_l3, a6_witness, lemma_l3_implies_no_a6};
use crate::lib_l4_safety::{
    RegistryState, OpId, no_a2_anywhere, a2_witness, lemma_l4_invariant_implies_no_a2,
};

verus! {

// =====================================================================
// Section 1: the composed state
// =====================================================================

/// The composed L_2/L_3/L_4 state: three disjoint component carriers, one per
/// discipline. L_2 governs the shared value memory (A_1/A_3), L_3 the external
/// effect log (A_6), L_4 the tool registry (A_2). The carriers share NO fields;
/// this disjointness is what makes the disciplines orthogonal.
pub struct Lattice {
    pub l2: RuntimeState,
    pub l3: SagaRecord,
    pub l4: RegistryState,
}

/// The lattice invariant is exactly the conjunction of the three component
/// disciplines, each over its own carrier.
pub open spec fn lattice_inv(x: Lattice) -> bool {
    &&& inv_l2(x.l2)
    &&& satisfies_l3(x.l3)
    &&& no_a2_anywhere(x.l4)
}

// =====================================================================
// Section 2: joint prevention (the composition theorem)
// =====================================================================

/// THEOREM L_4-COMPOSE (joint prevention). A state satisfying all three
/// disciplines simultaneously prevents, at once:
///   * A_3  -- no committed-clean transaction has an aborted predecessor;
///   * A_1 (image) -- every committed-clean read has a surviving producer that
///                    wrote exactly the observed value;
///   * A_6  -- the saga log exhibits no reorder;
///   * A_2  -- no committed, non-aborted op resolves through a stale/absent tool.
/// Proof: the three carriers are disjoint, so each component theorem applies to
/// its own projection independently; there is no cross-domain obligation to
/// discharge. This is the mechanised form of the orthogonality argument.
pub proof fn lemma_lattice_jointly_safe(x: Lattice)
    requires lattice_inv(x),
    ensures
        // A_3 (L_2):
        forall |t: TxnId| #![trigger x.l2.txns[t].committed] !a3_witness(x.l2, t),
        // A_1 image (L_2): every committed-clean read has a surviving producer.
        forall |t: TxnId, c: CellId|
            (x.l2.txns.contains_key(t) && x.l2.txns[t].committed && !x.l2.txns[t].aborted
             && x.l2.txns[t].read_set.contains(c))
            ==> exists |w: TxnId|
                x.l2.txns.contains_key(w) && x.l2.txns[w].committed && !x.l2.txns[w].aborted
                && x.l2.txns[w].write_set.contains(c)
                && x.l2.txns[w].write_values[c] == x.l2.txns[t].read_values[c],
        // A_6 (L_3):
        !a6_witness(x.l3),
        // A_2 (L_4):
        forall |o: OpId| #![trigger x.l4.ops[o]]
            (x.l4.ops.contains_key(o) && x.l4.ops[o].committed && !x.l4.ops[o].aborted)
            ==> !a2_witness(x.l4, o),
{
    // inv_l2(x.l2), satisfies_l3(x.l3), no_a2_anywhere(x.l4) from lattice_inv(x).
    lemma_l2_reachable_no_a3(x.l2);          // A_3
    lemma_l2_reads_supported(x.l2);          // A_1 image
    lemma_l3_implies_no_a6(x.l3);            // A_6
    lemma_l4_invariant_implies_no_a2(x.l4);  // A_2
}

// =====================================================================
// Section 3: non-interference (framing)
// =====================================================================

/// Updating the L_2 carrier cannot affect the L_3 or L_4 disciplines, because
/// satisfies_l3 and no_a2_anywhere are predicates over the (unchanged) l3 and l4
/// carriers. So lattice_inv is re-established the instant the new L_2 carrier
/// satisfies inv_l2. This is the formal content of "the disciplines do not
/// interfere because they are orthogonal."
pub proof fn lemma_frame_l2(x: Lattice, l2new: RuntimeState)
    requires lattice_inv(x), inv_l2(l2new),
    ensures lattice_inv(Lattice { l2: l2new, ..x }),
{
    // (Lattice { l2: l2new, ..x }).l3 == x.l3 and .l4 == x.l4, so satisfies_l3
    // and no_a2_anywhere carry over unchanged.
}

/// Symmetric framing for the L_3 carrier.
pub proof fn lemma_frame_l3(x: Lattice, l3new: SagaRecord)
    requires lattice_inv(x), satisfies_l3(l3new),
    ensures lattice_inv(Lattice { l3: l3new, ..x }),
{
}

/// Symmetric framing for the L_4 carrier.
pub proof fn lemma_frame_l4(x: Lattice, l4new: RegistryState)
    requires lattice_inv(x), no_a2_anywhere(l4new),
    ensures lattice_inv(Lattice { l4: l4new, ..x }),
{
}

// =====================================================================
// Section 4: closure under a single-carrier step (L_2 instance)
// =====================================================================

/// COROLLARY. If the lattice is invariant and a step updates ONLY the L_2
/// carrier to a state still satisfying inv_l2 (which the L_2 component
/// preservation lemmas -- e.g. lemma_commit_preserves_inv_l2 -- supply), then
/// the resulting lattice is again jointly anomaly-free: A_3 holds of the new
/// L_2 carrier, and -- crucially -- A_6 and A_2 are UNDISTURBED on the untouched
/// L_3/L_4 carriers. This is orthogonal composition closed under an L_2 step;
/// the L_3 and L_4 cases are symmetric via lemma_frame_l3 / lemma_frame_l4.
pub proof fn lemma_l2_step_keeps_jointly_safe(x: Lattice, l2new: RuntimeState)
    requires lattice_inv(x), inv_l2(l2new),
    ensures
        forall |t: TxnId| #![trigger l2new.txns[t].committed] !a3_witness(l2new, t),
        !a6_witness(x.l3),
        forall |o: OpId| #![trigger x.l4.ops[o]]
            (x.l4.ops.contains_key(o) && x.l4.ops[o].committed && !x.l4.ops[o].aborted)
            ==> !a2_witness(x.l4, o),
{
    let x2 = Lattice { l2: l2new, ..x };
    lemma_frame_l2(x, l2new);             // lattice_inv(x2)
    assert(x2.l2 == l2new);
    assert(x2.l3 == x.l3);
    assert(x2.l4 == x.l4);
    lemma_lattice_jointly_safe(x2);       // joint safety transfers to x2
}

} // verus!