// lib_l4_exec.rs
// ---------------------------------------------------------------------------
// Exec-mode L_4: an EXECUTABLE registry-snapshot runtime verified to be
// A_2-free (phantom-tool) by construction, regardless of registry churn.
//
// COMPILE
//   verus --crate-type=lib src/lib_l4_exec.rs
//
// RELATION TO THE MODEL (lib_l4_safety.rs)
//   The model file proves the two L_4 disciplines at the state-machine
//   level: validation-at-commit (Theorem L_4a) and snapshot isolation by
//   construction (Theorem L_4b), with non-vacuity (L_4c) and the lattice
//   placement (L_4d/L_4e). THIS file is the exec-mode counterpart of the
//   snapshot discipline -- the one the lattice point realises -- mirroring
//   how lib_l3_exec.rs relates to lib_l3_sequencer.rs: a runnable snapshot
//   operation whose dispatch is machine-checked to return exactly the
//   pinned signature, with non-vacuity at the exec representation. The
//   files are deliberately self-contained (no `mod`, no textual
//   re-inclusion), so verus_count.sh counts them independently.
//
// CONSTRUCTION
//   A live registry maps dense tool ids 0..n to signatures (Vec<u64>,
//   index = tool id) and supports arbitrary adversarial mutation. An
//   operation PINS at read time: it records its planned tool and takes a
//   full snapshot of the registry (built by a verified copy loop, so the
//   snapshot provably equals the registry's view at pin time). DISPATCH
//   resolves the tool's signature from the operation's own snapshot. The
//   capstone is structural: dispatch's postcondition equates the
//   dispatched signature with the pinned signature and does not mention
//   the live registry at all -- no interleaved mutation can introduce a
//   phantom, because the live registry is not an input to dispatch.
//
// THEOREMS
//   * pin: the snapshot equals the live registry's view at pin time, and
//     the pinned signature is the live signature of the planned tool;
//   * dispatch: returns exactly the pinned signature (A_2-freedom by
//     construction; the exec image of Theorem L_4b);
//   * a2_free: the dispatched signature admits no a2_witness_exec against
//     the operation's own pin -- the exec capstone;
//   * lemma_mutation_creates_a2_exec: a live-resolving baseline (dispatch
//     reads the post-mutation registry) admits an A_2 witness whenever the
//     planned tool's signature has changed -- the prevented phenomenon,
//     non-vacuous at the exec representation (exec image of Theorem L_4c).
//
// TRUST BASE: zero axioms, zero external_body, zero assume, zero admit.
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
// Section 1: A_2 at the exec representation
// =====================================================================

/// A_2 (phantom tool) against a resolution source `live`: the planned
/// tool resolves to a signature different from the one the operation
/// pinned. A dispatcher that resolves from `live` after registry churn
/// can exhibit this; a snapshot dispatcher cannot.
pub open spec fn a2_witness_exec(planned: usize, pinned: u64, live: Seq<u64>) -> bool {
    planned < live.len() && live[planned as int] != pinned
}

// =====================================================================
// Section 2: The live registry (adversary-mutable)
// =====================================================================

pub struct L4Registry {
    /// sigs[t] = current signature of tool id t.
    pub sigs: Vec<u64>,
}

impl L4Registry {
    pub fn new(n: usize, init: u64) -> (r: Self)
        ensures
            r.sigs@.len() == n as int,
            forall|t: int| 0 <= t < n as int ==> #[trigger] r.sigs@[t] == init,
    {
        let mut sigs: Vec<u64> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                k <= n,
                sigs@.len() == k as int,
                forall|t: int| 0 <= t < k as int ==> #[trigger] sigs@[t] == init,
            decreases n - k,
        {
            sigs.push(init);
            k = k + 1;
        }
        L4Registry { sigs }
    }

    /// Adversarial registry churn: change tool `t`'s signature, at any
    /// time, including between an operation's pin and its dispatch.
    pub fn mutate(&mut self, t: usize, new_sig: u64)
        requires
            t < old(self).sigs.len(),
        ensures
            final(self).sigs@ =~= old(self).sigs@.update(t as int, new_sig),
            final(self).sigs@.len() == old(self).sigs@.len(),
    {
        self.sigs.set(t, new_sig);
    }
}

// =====================================================================
// Section 3: The snapshot operation
// =====================================================================

pub struct SnapshotOp {
    /// The tool this operation planned to call.
    pub planned_tool: usize,
    /// The operation's own pinned copy of the registry, taken at pin time.
    pub snapshot: Vec<u64>,
}

impl SnapshotOp {
    pub closed spec fn wf(&self) -> bool {
        self.planned_tool < self.snapshot@.len()
    }

    /// The signature this operation planned against: the snapshot's value
    /// for the planned tool, fixed at pin time.
    pub open spec fn pinned_sig(&self) -> u64
        recommends self.wf(),
    {
        self.snapshot@[self.planned_tool as int]
    }

    /// PIN (read time): record the planned tool and take a snapshot of
    /// the live registry. The snapshot is built by a verified copy loop,
    /// so it provably equals the registry's view at this instant; the
    /// pinned signature is therefore the live signature at pin time.
    pub fn pin(reg: &L4Registry, tool: usize) -> (so: Self)
        requires
            tool < reg.sigs.len(),
        ensures
            so.wf(),
            so.planned_tool == tool,
            so.snapshot@ =~= reg.sigs@,
            so.pinned_sig() == reg.sigs@[tool as int],
    {
        let n = reg.sigs.len();
        let mut snap: Vec<u64> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                k <= n,
                n == reg.sigs@.len(),
                snap@.len() == k as int,
                forall|m: int| 0 <= m < k as int ==> #[trigger] snap@[m] == reg.sigs@[m],
            decreases n - k,
        {
            let v = reg.sigs[k];
            snap.push(v);
            k = k + 1;
        }
        assert(snap@ =~= reg.sigs@);
        SnapshotOp { planned_tool: tool, snapshot: snap }
    }

    /// DISPATCH (call time): resolve the planned tool's signature from
    /// the operation's OWN snapshot. The live registry is not an input:
    /// no mutation interleaved between pin and dispatch can change the
    /// result. This is A_2-freedom by construction (exec image of
    /// Theorem L_4b in lib_l4_safety.rs).
    pub fn dispatch(&self) -> (sig: u64)
        requires
            self.wf(),
        ensures
            sig == self.pinned_sig(),
    {
        self.snapshot[self.planned_tool]
    }

    /// EXEC CAPSTONE (mirrors lib_l3_exec::a6_free): the signature a
    /// well-formed snapshot operation dispatches admits no A_2 witness
    /// against the operation's own pin -- for any registry history,
    /// because the dispatched and pinned signatures are the same
    /// snapshot lookup.
    pub fn a2_free(&self)
        requires
            self.wf(),
        ensures
            !a2_witness_exec(self.planned_tool, self.pinned_sig(), self.snapshot@),
    {
        proof {
            // a2_witness_exec demands snapshot[planned] != pinned_sig,
            // but pinned_sig IS snapshot[planned].
            assert(self.snapshot@[self.planned_tool as int] == self.pinned_sig());
        }
    }
}

// =====================================================================
// Section 4: Non-vacuity at the exec representation
// =====================================================================

/// The LIVE-RESOLVING baseline dispatches against the post-mutation
/// registry. Whenever churn changed the planned tool's signature, an A_2
/// witness exists: the prevented phenomenon is genuinely reachable
/// without snapshot isolation (exec image of Theorem L_4c).
pub proof fn lemma_mutation_creates_a2_exec(live0: Seq<u64>, t: usize, new_sig: u64)
    requires
        (t as int) < live0.len(),
        new_sig != live0[t as int],
    ensures
        a2_witness_exec(t, live0[t as int], live0.update(t as int, new_sig)),
{
    let live1 = live0.update(t as int, new_sig);
    assert(live1.len() == live0.len());
    assert(live1[t as int] == new_sig);
}

/// Concrete two-line witness, so the existential form is also exhibited.
pub proof fn lemma_live_resolution_admits_a2_exec()
    ensures
        exists|live: Seq<u64>, pinned: u64|
            #[trigger] a2_witness_exec(0, pinned, live),
{
    let live: Seq<u64> = seq![1u64];
    assert(a2_witness_exec(0, 0u64, live)) by {
        assert(live.len() == 1 && live[0int] == 1u64 && 1u64 != 0u64);
    }
}

} // verus!