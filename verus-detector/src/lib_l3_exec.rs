// lib_l3_exec.rs
// ---------------------------------------------------------------------------
// Exec-mode L_3: an EXECUTABLE commit-order sequencer verified to emit
// effects in issuance order, hence A_6-free, for ANY completion schedule.
//
// COMPILE
//   verus --crate-type=lib src/lib_l3_exec.rs
//
// RELATION TO THE MODEL (lib_l3_sequencer.rs)
//   The model file proves the schedule-level theorem: under sequenced
//   externalization, the externalization-time sequence is monotone in
//   issuance index for any completion schedule (thm_sequencer_orders_
//   concurrent_effects / cor_sequencer_no_a6), with non-vacuity witnesses.
//   THIS file is the exec-mode counterpart, mirroring how lib_l2_exec.rs
//   relates to lib_l2_safety.rs: a runnable sequencer whose data-structure
//   invariant is machine-checked across every public operation, with the
//   A_6-freedom capstone proved of the runnable code's emitted order. The
//   two files are deliberately self-contained (no `mod` or textual
//   re-inclusion), so verus_count.sh counts them independently with no
//   re-inclusion edge.
//
// CONSTRUCTION
//   Calls are issued with consecutive indices 0..n. Completions arrive in an
//   ARBITRARY order via `complete(i)` (the adversary chooses the schedule,
//   exactly as the model's `cstep` is arbitrary). The sequencer maintains a
//   completion bitmap and externalizes the maximal fully-completed prefix:
//   effect k is appended to `externalized` only when effects 0..k have all
//   completed. The invariant `wf` pins `externalized` to be the identity
//   prefix [0, 1, ..., len-1] over completed calls; A_6-freedom (no
//   issuance-order inversion in the emitted order) is a one-lemma corollary,
//   proved of the reachable states of the runnable structure.
//
// THEOREMS
//   * wf preserved by new / complete (every public op);
//   * thm_identity_prefix_no_inversion: identity prefix ==> no A_6 inversion;
//   * a6_free: every well-formed sequencer state's emitted order is
//     A_6-inversion-free (the exec capstone, mirroring lib_l2_exec's a3_free);
//   * lemma_unsequenced_admits_a6_exec: the unsequenced emitted order
//     (externalize-on-completion) admits an inversion -- the prevented
//     phenomenon, non-vacuous at the exec representation too.
//
// TRUST BASE: zero axioms, zero external_body, zero assume, zero admit
//   (verify with the standard greps; the file adds nothing to the crate's
//   trust base).
//
// STATUS: DRAFT until the first `verus` run on your machine; the reproduce
//   script pins this file at "?" (zero errors required, count reported but
//   not asserted) until you replace "?" with the live-confirmed count.
// ---------------------------------------------------------------------------

#![allow(unused_imports)]
#![allow(dead_code)]
use vstd::prelude::*;

verus! {

// =====================================================================
// Section 1: A_6 inversion at the exec representation
// =====================================================================

/// The emitted order `s` lists issuance indices in externalization order.
/// An A_6 inversion: some position pair i < j where a LATER-issued effect
/// (larger issuance index) was externalized BEFORE an earlier-issued one.
pub open spec fn a6_inversion_exec(s: Seq<usize>) -> bool {
    exists|i: int, j: int|
        #![trigger s[i], s[j]]
        0 <= i && i < j && j < s.len() && (s[i] as int) > (s[j] as int)
}

/// `s` is the identity prefix: position m holds issuance index m.
pub open spec fn is_identity_prefix(s: Seq<usize>) -> bool {
    forall|m: int| 0 <= m < s.len() ==> (#[trigger] s[m]) as int == m
}

/// Identity prefix ==> no inversion (positions are strictly increasing
/// issuance indices, so no pair can invert).
pub proof fn thm_identity_prefix_no_inversion(s: Seq<usize>)
    requires
        is_identity_prefix(s),
    ensures
        !a6_inversion_exec(s),
{
    assert forall|i: int, j: int|
        0 <= i && i < j && j < s.len() implies (s[i] as int) <= (s[j] as int) by {
        assert((s[i] as int) == i);
        assert((s[j] as int) == j);
    }
}

// =====================================================================
// Section 2: The executable sequencer
// =====================================================================

pub struct L3Sequencer {
    /// Number of issued calls (issuance indices are 0..n).
    pub n: usize,
    /// completed[i] == true iff call i's external effect has completed.
    pub completed: Vec<bool>,
    /// Issuance indices in EXTERNALIZATION order. The invariant pins this
    /// to the identity prefix over the fully-completed prefix of calls.
    pub externalized: Vec<usize>,
}

impl L3Sequencer {
    /// Data-structure invariant, maintained by every public operation.
    pub closed spec fn wf(&self) -> bool {
        &&& self.completed@.len() == self.n as int
        &&& self.externalized@.len() <= self.n as int
        &&& is_identity_prefix(self.externalized@)
        &&& forall|m: int| 0 <= m < self.externalized@.len()
                ==> #[trigger] self.completed@[m]
    }

    /// Spec accessor for the emitted order (for callers' postconditions).
    pub open spec fn emitted(&self) -> Seq<usize> {
        self.externalized@
    }

    pub fn new(n: usize) -> (r: Self)
        ensures
            r.wf(),
            r.emitted().len() == 0,
            r.n == n,
    {
        let mut completed: Vec<bool> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                k <= n,
                completed@.len() == k as int,
            decreases n - k,
        {
            completed.push(false);
            k = k + 1;
        }
        let r = L3Sequencer { n, completed, externalized: Vec::new() };
        assert(r.externalized@.len() == 0);
        assert(is_identity_prefix(r.externalized@));
        r
    }

    /// Adversary-scheduled completion of call `i`, in ANY order. Marks the
    /// call complete, then externalizes the maximal fully-completed prefix.
    /// The emitted order only ever GROWS and stays the identity prefix.
    pub fn complete(&mut self, i: usize)
        requires
            old(self).wf(),
            i < old(self).n,
        ensures
            final(self).wf(),
            final(self).n == old(self).n,
            // monotone growth: previously emitted effects keep their order
            old(self).emitted().len() <= final(self).emitted().len(),
            final(self).emitted().subrange(0, old(self).emitted().len() as int)
                =~= old(self).emitted(),
    {
        let ghost old_emitted = self.externalized@;
        assert(i < self.completed.len());
        self.completed.set(i, true);
        // Marking one entry true cannot falsify wf's prefix-completed clause
        // (it is monotone) nor touch `externalized`.
        assert(self.completed@.len() == self.n as int);
        assert(is_identity_prefix(self.externalized@));
        assert forall|m: int| 0 <= m < self.externalized@.len()
                implies #[trigger] self.completed@[m] by {
            // set(idx, true) is monotone toward true: entry idx becomes true,
            // every other entry is unchanged from old(self), where wf held.
            if m == i as int {
            } else {
                assert(self.completed@[m] == old(self).completed@[m]);
                assert(old(self).completed@[m]);
            }
        }

        // Pump: externalize while the next-issued call has completed.
        let mut next: usize = self.externalized.len();
        assert(next as int == self.externalized@.len());
        while next < self.n && self.completed[next]
            invariant
                self.n == old(self).n,
                self.completed@.len() == self.n as int,
                next as int == self.externalized@.len(),
                next <= self.n,
                is_identity_prefix(self.externalized@),
                forall|m: int| 0 <= m < self.externalized@.len()
                    ==> #[trigger] self.completed@[m],
                self.externalized@.subrange(0, old_emitted.len() as int)
                    =~= old_emitted,
                old_emitted.len() <= self.externalized@.len(),
            decreases self.n - next,
        {
            // The loop condition gives completed[next] == true here; make it
            // explicit for the prefix-completed invariant after the push.
            assert(self.completed@[next as int]);
            self.externalized.push(next);
            proof {
                // The pushed value equals its own position: identity preserved.
                // push semantics: new view = old view + [next], positions < next
                // unchanged; position next holds value next.
                let s = self.externalized@;
                assert(s.len() == next as int + 1);
                assert(s[next as int] == next);
                assert forall|m: int| 0 <= m < s.len()
                        implies (#[trigger] s[m]) as int == m by {
                    if m < next as int {
                        // unchanged below the push; identity held there (loop inv)
                    } else {
                        // m == next: the pushed value
                        assert(s[m] == next);
                    }
                }
                assert(s.subrange(0, old_emitted.len() as int) =~= old_emitted);
            }
            next = next + 1;
        }
    }

    /// EXEC CAPSTONE (mirrors lib_l2_exec::a3_free): every well-formed
    /// sequencer state's emitted order is A_6-inversion-free.
    pub fn a6_free(&self)
        requires
            self.wf(),
        ensures
            !a6_inversion_exec(self.emitted()),
    {
        proof {
            thm_identity_prefix_no_inversion(self.externalized@);
        }
    }
}

// =====================================================================
// Section 3: Non-vacuity at the exec representation
// =====================================================================

/// The UNSEQUENCED baseline externalizes on completion: the emitted order is
/// whatever the adversary's schedule dictates. A reversed two-call schedule
/// emits [1, 0] -- an A_6 inversion. The prevented phenomenon exists.
pub proof fn lemma_unsequenced_admits_a6_exec()
    ensures
        exists|s: Seq<usize>| #[trigger] a6_inversion_exec(s),
{
    let s: Seq<usize> = seq![1usize, 0usize];
    assert(s.len() == 2);
    assert(s[0] == 1usize && s[1] == 0usize);
    assert(a6_inversion_exec(s)) by {
        assert(0 <= 0int && 0int < 1int && 1int < s.len()
            && (s[0int] as int) > (s[1int] as int));
    }
}

} // verus!