// lib_occ_l2_refinement.rs
// ---------------------------------------------------------------------------
// Extends the runtime-refinement bridge to the L1 -> L2 edge. Models a
// versioned channel update under two disciplines:
//   L1 (version-unaware): every write is applied (accumulates, bumps version)
//   L2 (optimistic concurrency / ETag): a write is applied ONLY if the version
//        it read still matches the channel head; otherwise it is rejected.
// This maps to a real runtime feature (Orleans-style ETag concurrency, which
// AutoGen's state-persistence work adopts). We prove the SUBSTANTIVE behavioral
// difference -- not prevention by exclusion:
//   (T1) version monotonicity under L2;
//   (T2) version-counts-commits: the head version equals the initial version
//        plus the number of writes that actually committed (a real inductive
//        invariant);
//   (T3) commit-implies-head-read: any write that changes the state read the
//        current head -- so no committed write is grounded in a stale read
//        (the L2 no-stale-generation guarantee);
//   (T4) stale rejection: a write whose read-version is not the head is a no-op;
//   (W)  witness: a concrete stale write that L1 ACCEPTS but L2 REJECTS.
// Discipline: zero axioms, zero external_body, zero assume, zero admit.
// ---------------------------------------------------------------------------

use vstd::prelude::*;

verus! {

pub struct VState {
    pub value: Seq<int>,
    pub version: nat,
}

pub struct VOp {
    pub rv: nat,          // the channel version this write observed (its read)
    pub payload: Seq<int>,
}

// L1: version-unaware -- always applies.
spec fn apply_l1(s: VState, op: VOp) -> VState {
    VState { value: s.value + op.payload, version: s.version + 1 }
}

// L2: optimistic concurrency -- applies only if the read version is the head.
spec fn apply_l2(s: VState, op: VOp) -> VState {
    if op.rv == s.version {
        VState { value: s.value + op.payload, version: s.version + 1 }
    } else {
        s
    }
}

spec fn run_l1(s: VState, ops: Seq<VOp>) -> VState
    decreases ops.len()
{
    if ops.len() == 0 { s } else { apply_l1(run_l1(s, ops.drop_last()), ops.last()) }
}

spec fn run_l2(s: VState, ops: Seq<VOp>) -> VState
    decreases ops.len()
{
    if ops.len() == 0 { s } else { apply_l2(run_l2(s, ops.drop_last()), ops.last()) }
}

// number of writes that actually committed under L2
spec fn num_commits(s: VState, ops: Seq<VOp>) -> nat
    decreases ops.len()
{
    if ops.len() == 0 {
        0
    } else {
        let prev = run_l2(s, ops.drop_last());
        num_commits(s, ops.drop_last())
            + (if ops.last().rv == prev.version { 1nat } else { 0nat })
    }
}

// --- T1: version monotonicity under L2 -----------------------------------
proof fn thm_l2_version_monotone(s: VState, ops: Seq<VOp>)
    ensures
        run_l2(s, ops).version >= s.version,
    decreases ops.len(),
{
    if ops.len() == 0 {
    } else {
        thm_l2_version_monotone(s, ops.drop_last());
        let prev = run_l2(s, ops.drop_last());
        assert(run_l2(s, ops) == apply_l2(prev, ops.last()));
        // apply_l2 yields prev.version or prev.version + 1, both >= prev.version >= s.version
    }
}

// --- T2: version counts commits (substantive inductive invariant) --------
proof fn thm_l2_version_counts_commits(s: VState, ops: Seq<VOp>)
    ensures
        run_l2(s, ops).version == s.version + num_commits(s, ops),
    decreases ops.len(),
{
    if ops.len() == 0 {
    } else {
        thm_l2_version_counts_commits(s, ops.drop_last());
        let prev = run_l2(s, ops.drop_last());
        let last = ops.last();
        assert(run_l2(s, ops) == apply_l2(prev, last));
        if last.rv == prev.version {
            assert(run_l2(s, ops).version == prev.version + 1);
            assert(num_commits(s, ops) == num_commits(s, ops.drop_last()) + 1);
        } else {
            assert(run_l2(s, ops).version == prev.version);
            assert(num_commits(s, ops) == num_commits(s, ops.drop_last()));
        }
    }
}

// --- T3: a committed write read the head (no stale-generation) -----------
proof fn thm_l2_commit_reads_head(s: VState, op: VOp)
    requires
        apply_l2(s, op).version != s.version,
    ensures
        op.rv == s.version,
{
    if op.rv == s.version {
    } else {
        assert(apply_l2(s, op) == s);
    }
}

// --- T4: a stale write is rejected (no-op) --------------------------------
proof fn thm_l2_rejects_stale(s: VState, op: VOp)
    requires
        op.rv != s.version,
    ensures
        apply_l2(s, op) == s,
{
}

// --- W: witness -- a stale write L1 ACCEPTS but L2 REJECTS ----------------
// State already at version 1; an op that read version 0 (rv = 0) is stale.
// L1 ignores the read version and commits it (value grows, version -> 2);
// L2 sees rv != head and rejects it (state unchanged). This is the exact
// behavioral gap the L1 -> L2 ascent closes.
proof fn thm_l1_l2_differ_on_stale()
    ensures
        apply_l1(VState { value: seq![1int], version: 1 },
                 VOp { rv: 0, payload: seq![2int] }).version == 2,
        apply_l1(VState { value: seq![1int], version: 1 },
                 VOp { rv: 0, payload: seq![2int] }).value =~= seq![1int, 2int],
        apply_l2(VState { value: seq![1int], version: 1 },
                 VOp { rv: 0, payload: seq![2int] })
            == (VState { value: seq![1int], version: 1 }),
{
    let s = VState { value: seq![1int], version: 1 };
    let op = VOp { rv: 0, payload: seq![2int] };
    // L1 accepts: value = [1] + [2], version = 1 + 1
    assert(apply_l1(s, op).value =~= seq![1int] + seq![2int]);
    assert(seq![1int] + seq![2int] =~= seq![1int, 2int]);
    assert(apply_l1(s, op).version == 2);
    // L2 rejects: rv (0) != head (1) -> else branch -> s unchanged
    assert(op.rv != s.version);
    assert(apply_l2(s, op) == s);
}

} // verus!