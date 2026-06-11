#![allow(unused_imports)]
#![allow(dead_code)]
use vstd::prelude::*;

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
pub struct Lattice {
    pub l2: RuntimeState,
    pub l3: SagaRecord,
    pub l4: RegistryState,
}

pub open spec fn lattice_inv(x: Lattice) -> bool {
    &&& inv_l2(x.l2)
    &&& satisfies_l3(x.l3)
    &&& no_a2_anywhere(x.l4)
}

pub proof fn lemma_lattice_jointly_safe(x: Lattice)
    requires lattice_inv(x),
    ensures
        forall |t: TxnId| #![trigger x.l2.txns[t].committed] !a3_witness(x.l2, t),
        forall |t: TxnId, c: CellId|
            (x.l2.txns.contains_key(t) && x.l2.txns[t].committed && !x.l2.txns[t].aborted
             && x.l2.txns[t].read_set.contains(c))
            ==> exists |w: TxnId|
                x.l2.txns.contains_key(w) && x.l2.txns[w].committed && !x.l2.txns[w].aborted
                && x.l2.txns[w].write_set.contains(c)
                && x.l2.txns[w].write_values[c] == x.l2.txns[t].read_values[c],
        !a6_witness(x.l3),
        forall |o: OpId| #![trigger x.l4.ops[o]]
            (x.l4.ops.contains_key(o) && x.l4.ops[o].committed && !x.l4.ops[o].aborted)
            ==> !a2_witness(x.l4, o),
{
    lemma_l2_reachable_no_a3(x.l2);
    lemma_l2_reads_supported(x.l2);
    lemma_l3_implies_no_a6(x.l3);
    lemma_l4_invariant_implies_no_a2(x.l4);
}

pub proof fn lemma_frame_l2(x: Lattice, l2new: RuntimeState)
    requires lattice_inv(x), inv_l2(l2new),
    ensures lattice_inv(Lattice { l2: l2new, ..x }),
{ }

pub proof fn lemma_frame_l3(x: Lattice, l3new: SagaRecord)
    requires lattice_inv(x), satisfies_l3(l3new),
    ensures lattice_inv(Lattice { l3: l3new, ..x }),
{
}

pub proof fn lemma_frame_l4(x: Lattice, l4new: RegistryState)
    requires lattice_inv(x), no_a2_anywhere(l4new),
    ensures lattice_inv(Lattice { l4: l4new, ..x }),
{
}

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
    lemma_frame_l2(x, l2new);
    assert(x2.l2 == l2new);
    assert(x2.l3 == x.l3);
    assert(x2.l4 == x.l4);
    lemma_lattice_jointly_safe(x2);
}

} // verus!