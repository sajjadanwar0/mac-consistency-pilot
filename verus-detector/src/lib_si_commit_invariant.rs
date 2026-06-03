// lib_si_commit_invariant.rs
//
// State-machine invariant for the snapshot-isolation commit operation. The
// verified validation gate (lib_si_validate_exec.rs) is only meaningful if the
// version log it inspects is well-formed: every cell's version chain is
// non-empty, strictly increasing in commit time, and bounded by the clock.
// `commit` is the sole mutator of that log. This file proves that `commit`
// PRESERVES the invariant across an arbitrary commit, and that the initial
// (empty) state satisfies it -- so the invariant holds across every reachable
// state by induction.
//
// This closes the gap the version-chain refinement explicitly flagged as
// "mechanical follow-up": preservation of the chain-monotonicity invariant
// across arbitrary execution histories.
//
// FIDELITY TO THE DEPLOYED commit
//   Deployed: `g.clock += 1; let ct = g.clock; for (k,v) in writes { versions
//   .entry(k).or_default().push((ct, v)); }`. The model below sets
//   clock' = clock + 1 and appends the single new commit time clock' to every
//   written cell's chain (creating a singleton for a first write) -- identical.
//   This is a proof-mode result over the chain model (Map<Cell, Seq<(Time,
//   Val)>>), connected to the deployed BTreeMap runtime by the existing
//   refinement proofs; std/parking_lot internals are not exec-verifiable.
//
// NO axiom, NO assume, NO admit, NO external_body in this file.

use vstd::prelude::*;

verus! {

/// A version chain is well-formed at `clock` iff it is non-empty, every commit
/// time is <= clock, and times are strictly increasing.
pub open spec fn chain_wf(chain: Seq<(int, int)>, clock: int) -> bool {
    &&& chain.len() > 0
    &&& (forall|k: int| 0 <= k < chain.len() ==> chain[k].0 <= clock)
    &&& (forall|a: int, b: int| 0 <= a < b < chain.len() ==> chain[a].0 < chain[b].0)
}

/// The whole version log is well-formed at `clock` iff every present cell's
/// chain is.
pub open spec fn store_wf(versions: Map<int, Seq<(int, int)>>, clock: int) -> bool {
    forall|c: int| #[trigger] versions.dom().contains(c) ==> chain_wf(versions[c], clock)
}

/// Raising the clock cannot break well-formedness (the bound only relaxes).
pub proof fn chain_wf_relax(chain: Seq<(int, int)>, clock: int, clock2: int)
    requires
        chain_wf(chain, clock),
        clock <= clock2,
    ensures
        chain_wf(chain, clock2),
{
    assert forall|k: int| 0 <= k < chain.len() implies chain[k].0 <= clock2 by {
        assert(chain[k].0 <= clock);
    }
}

/// Appending a fresh commit at time `clock2` strictly later than everything in
/// a (possibly empty, else well-formed) base chain yields a chain well-formed
/// at `clock2`.
pub proof fn push_preserves_wf(base: Seq<(int, int)>, clock: int, clock2: int, v: int)
    requires
        clock < clock2,
        base.len() == 0 || chain_wf(base, clock),
    ensures
        chain_wf(base.push((clock2, v)), clock2),
{
    let p = base.push((clock2, v));
    assert(p.len() == base.len() + 1);

    // bound: every time <= clock2
    assert forall|k: int| 0 <= k < p.len() implies p[k].0 <= clock2 by {
        if k < base.len() {
            assert(p[k] == base[k]);
            assert(base.len() > 0);
            assert(chain_wf(base, clock));
            assert(base[k].0 <= clock);
        } else {
            assert(p[k] == (clock2, v));
        }
    }

    // strict increase
    assert forall|a: int, b: int| 0 <= a < b < p.len() implies p[a].0 < p[b].0 by {
        if b < base.len() {
            assert(base.len() > 0);
            assert(chain_wf(base, clock));
            assert(p[a] == base[a]);
            assert(p[b] == base[b]);
        } else {
            // b is the new last element
            assert(p[b] == (clock2, v));
            assert(p[a] == base[a]);
            assert(base.len() > 0);
            assert(chain_wf(base, clock));
            assert(base[a].0 <= clock);   // bound
            // hence base[a].0 <= clock < clock2 = p[b].0
        }
    }
}

/// `commit` preserves the store invariant. `versions2`/`clock2` is the state
/// after a commit that advances the clock by one and appends the new commit
/// time to every written cell's chain (creating a singleton for first writes),
/// leaving unwritten cells untouched. `writes` maps each written cell to its
/// committed value.
pub proof fn commit_preserves_wf(
    versions: Map<int, Seq<(int, int)>>,
    clock: int,
    versions2: Map<int, Seq<(int, int)>>,
    clock2: int,
    writes: Map<int, int>,
)
    requires
        store_wf(versions, clock),
        clock2 == clock + 1,
        // domain of the new log is the old domain plus the written cells
        versions2.dom() == versions.dom().union(writes.dom()),
        // written cells: old chain (or empty) extended by (clock2, value)
        forall|c: int| #[trigger] writes.dom().contains(c) ==>
            versions2[c] == (if versions.dom().contains(c) { versions[c] }
                             else { Seq::<(int, int)>::empty() }).push((clock2, writes[c])),
        // unwritten present cells: unchanged
        forall|c: int| #[trigger] versions.dom().contains(c) && !writes.dom().contains(c) ==>
            versions2[c] == versions[c],
    ensures
        store_wf(versions2, clock2),
{
    assert forall|c: int| versions2.dom().contains(c) implies chain_wf(versions2[c], clock2) by {
        // c is in the old domain, the written set, or both.
        if writes.dom().contains(c) {
            let base = if versions.dom().contains(c) { versions[c] }
                       else { Seq::<(int, int)>::empty() };
            if versions.dom().contains(c) {
                assert(chain_wf(base, clock));   // from store_wf(versions, clock)
            }
            push_preserves_wf(base, clock, clock2, writes[c]);
            assert(versions2[c] == base.push((clock2, writes[c])));
        } else {
            // not written, so it must come from the old domain, unchanged
            assert(versions.dom().contains(c));
            assert(versions2[c] == versions[c]);
            assert(chain_wf(versions[c], clock));   // from store_wf
            chain_wf_relax(versions[c], clock, clock2);
        }
    }
}

/// The initial state (no versions, clock 0) is well-formed, vacuously.
pub proof fn initial_wf()
    ensures
        store_wf(Map::<int, Seq<(int, int)>>::empty(), 0),
{
}

} // verus!