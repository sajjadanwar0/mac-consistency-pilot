// lib_a4_split_view.rs
//
// A_4 (split-view) under replication, formalized as a CONTENT property of a
// monotone, append-only primary -- not as exclusion-by-construction.
//
// The earlier version of this file proved "read-from-primary => not A_4"
// by the one-line observation that A_4 requires two distinct replica ids
// while read-from-primary uses one. That is a structural tautology: if you
// only ever read one replica you cannot observe two replicas disagreeing.
//
// This version instead proves a property with content:
//
//   The primary is an append-only, monotone-versioned log. Two primary reads
//   of the same cell that observe the SAME version necessarily observe the
//   SAME value -- there is no "split view" at a fixed committed version --
//   and primary read versions are monotone in trace order. The mechanism
//   (single append-only primary) does work; it is not a definitional dodge.
//
// We then exhibit (i) a concrete A_4 witness produced by a LAGGING SECONDARY
// serving an older log index while the primary has advanced -- the genuine
// split-view the primary discipline prevents, with its value tied to the
// model rather than hand-asserted -- and (ii) a cross-version witness showing
// two primary reads MAY legitimately differ at different versions, so the
// no-split theorem is non-vacuous (it does not hold merely because all
// primary reads are forced equal).
//
// Trust base: none. Zero `assume`, zero `admit`, zero `external_body`.

use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Domain
// ---------------------------------------------------------------------------

// NULL sentinel for "cell never written" (version 0). Distinct from any value
// written in the witnesses below (10, 5, 7), so no NULL/value collision.
pub open spec fn nullv() -> int { -1 }

// Runtime events over a single cell. The single-cell model carries the
// split-view argument without loss: A_4 is a per-cell predicate.
//   Write(v)         : the primary commits value v, advancing its version.
//   ReadP(t)         : a read served by the PRIMARY at logical time t.
//   ReadS(sid,idx,t) : a read served by SECONDARY `sid`, which replicates the
//                      primary up to log index `idx` (idx <= primary head).
pub enum Ev {
    Write(int),
    ReadP(nat),
    ReadS(nat, nat, nat),
}

pub open spec fn is_write(e: Ev) -> bool {
    match e {
        Ev::Write(_) => true,
        Ev::ReadP(_) => false,
        Ev::ReadS(_, _, _) => false,
    }
}

// The primary state is its committed log: log[i] is the value committed at
// version (i+1). The head version is log.len(); the head value is the last
// element (or NULL when empty).
pub open spec fn apply(s: Seq<int>, e: Ev) -> Seq<int> {
    match e {
        Ev::Write(v) => s.push(v),
        Ev::ReadP(_) => s,
        Ev::ReadS(_, _, _) => s,
    }
}

// State of the primary log after applying the first `n` events of `evs`.
// A read at trace index i observes state_after(evs, i) (the state in force
// when event i is processed; reads do not mutate the log).
pub open spec fn state_after(evs: Seq<Ev>, n: nat) -> Seq<int>
    decreases n,
{
    if n == 0 {
        Seq::<int>::empty()
    } else {
        apply(state_after(evs, (n - 1) as nat), evs[(n - 1) as int])
    }
}

pub open spec fn head_value(s: Seq<int>) -> int {
    if s.len() == 0 { nullv() } else { s[(s.len() - 1) as int] }
}

// Value a secondary serves when it has replicated up to log index k:
//   k == 0  -> the cell is, from the secondary's view, still unwritten (NULL);
//   k >= 1  -> the value the primary committed at version k.
pub open spec fn value_at(s: Seq<int>, k: nat) -> int {
    if k == 0 { nullv() } else { s[(k - 1) as int] }
}

// Version and value a PRIMARY read at trace position i observes.
pub open spec fn pread_version(evs: Seq<Ev>, i: nat) -> nat {
    state_after(evs, i).len()
}
pub open spec fn pread_value(evs: Seq<Ev>, i: nat) -> int {
    head_value(state_after(evs, i))
}

// ---------------------------------------------------------------------------
// Core inductive lemmas: the primary log is append-only and monotone.
// These carry the real content; the theorems below are their corollaries.
// ---------------------------------------------------------------------------

// One step never shrinks the log; a non-write step leaves it identical.
proof fn lemma_apply_step(s: Seq<int>, e: Ev)
    ensures
        s.len() <= apply(s, e).len(),
        is_write(e) ==> apply(s, e).len() == s.len() + 1,
        !is_write(e) ==> apply(s, e) =~= s,
{
    match e {
        Ev::Write(v) => {
            assert(apply(s, e) =~= s.push(v));
        }
        Ev::ReadP(_) => {}
        Ev::ReadS(_, _, _) => {}
    }
}

// Version (= log length) is monotone non-decreasing in trace order.
pub proof fn lemma_state_monotone_len(evs: Seq<Ev>, i: nat, j: nat)
    requires
        i <= j,
        j <= evs.len(),
    ensures
        state_after(evs, i).len() <= state_after(evs, j).len(),
    decreases j - i,
{
    if i < j {
        lemma_state_monotone_len(evs, i, (j - 1) as nat);
        assert(state_after(evs, j)
            == apply(state_after(evs, (j - 1) as nat), evs[(j - 1) as int]));
        lemma_apply_step(state_after(evs, (j - 1) as nat), evs[(j - 1) as int]);
    }
}

// If two trace points have equal log length, the logs are identical: a write
// would have grown the length, so every step between them was a read. This is
// the append-only invariant doing the work behind the no-split theorem.
pub proof fn lemma_state_stable_eq_len(evs: Seq<Ev>, i: nat, j: nat)
    requires
        i <= j,
        j <= evs.len(),
        state_after(evs, i).len() == state_after(evs, j).len(),
    ensures
        state_after(evs, i) =~= state_after(evs, j),
    decreases j - i,
{
    if i < j {
        lemma_state_monotone_len(evs, i, (j - 1) as nat);
        lemma_state_monotone_len(evs, (j - 1) as nat, j);
        // Squeeze: len_i <= len_{j-1} <= len_j == len_i, so all three equal.
        assert(state_after(evs, (j - 1) as nat).len() == state_after(evs, i).len());

        assert(state_after(evs, j)
            == apply(state_after(evs, (j - 1) as nat), evs[(j - 1) as int]));
        lemma_apply_step(state_after(evs, (j - 1) as nat), evs[(j - 1) as int]);
        // Length preserved over the last step => that step was not a write.
        assert(!is_write(evs[(j - 1) as int]));
        assert(state_after(evs, j) =~= state_after(evs, (j - 1) as nat));

        lemma_state_stable_eq_len(evs, i, (j - 1) as nat);
    }
}

// ---------------------------------------------------------------------------
// Theorems (corollaries of the append-only invariant).
// ---------------------------------------------------------------------------

// Theorem A4-mono: primary read versions are monotone in trace order.
pub proof fn thm_primary_version_monotone(evs: Seq<Ev>, i: nat, j: nat)
    requires
        i <= j,
        j <= evs.len(),
    ensures
        pread_version(evs, i) <= pread_version(evs, j),
{
    lemma_state_monotone_len(evs, i, j);
}

// Theorem A4-no-split: two primary reads of the cell that observe the SAME
// version observe the SAME value. No split view at a fixed committed version.
// This is the content statement replacing the old exclusion tautology.
pub proof fn thm_primary_no_split_at_version(evs: Seq<Ev>, i: nat, j: nat)
    requires
        i <= j,
        j <= evs.len(),
        pread_version(evs, i) == pread_version(evs, j),
    ensures
        pread_value(evs, i) == pread_value(evs, j),
{
    lemma_state_stable_eq_len(evs, i, j);
    // Equal states => equal head value.
    assert(head_value(state_after(evs, i)) == head_value(state_after(evs, j)));
}

// Corollary (A_4 framing): if two primary reads of the cell return DIFFERENT
// values, they must be at DIFFERENT versions. Equivalently, the value-mismatch
// half of A_4 cannot occur among primary reads at one version.
pub proof fn cor_primary_diff_value_implies_diff_version(evs: Seq<Ev>, i: nat, j: nat)
    requires
        i <= j,
        j <= evs.len(),
        pread_value(evs, i) != pread_value(evs, j),
    ensures
        pread_version(evs, i) != pread_version(evs, j),
{
    if pread_version(evs, i) == pread_version(evs, j) {
        thm_primary_no_split_at_version(evs, i, j);
        assert(false);
    }
}

// ---------------------------------------------------------------------------
// The A_4 predicate and the witness it is meant to exclude.
// ---------------------------------------------------------------------------

pub struct ReadRec {
    pub cell: nat,
    pub replica: nat, // 0 = primary; >0 = secondary id
    pub version: nat,
    pub value: int,
}

// Paper A_4: two reads of the same cell, from different replicas, disagree.
pub open spec fn a4_holds(rs: Seq<ReadRec>) -> bool {
    exists|i: int, j: int|
        #![trigger rs[i].cell, rs[j].cell]
        0 <= i < rs.len() && 0 <= j < rs.len()
        && rs[i].cell == rs[j].cell
        && rs[i].replica != rs[j].replica
        && rs[i].value != rs[j].value
}

// Non-vacuity / the prevented phenomenon: a LAGGING SECONDARY serving an old
// log index produces a genuine A_4 against the primary. The two observed
// values are taken from the model (head_value and value_at of an actual
// post-write state), not asserted by hand.
pub proof fn lemma_secondary_lag_admits_a4()
    ensures
        exists|rs: Seq<ReadRec>| #[trigger] a4_holds(rs),
{
    let evs: Seq<Ev> = seq![Ev::Write(10)];

    assert(state_after(evs, 0) =~= Seq::<int>::empty());
    assert(evs[0] == Ev::Write(10));
    assert(state_after(evs, 1)
        == apply(state_after(evs, 0), evs[0]));
    assert(state_after(evs, 1) =~= seq![10int]);

    let st = state_after(evs, 1);
    let pv = head_value(st);    // primary head value at version 1 = 10
    let sv = value_at(st, 0);   // lagging secondary at index 0 = NULL = -1
    assert(pv == 10);
    assert(sv == nullv());

    let rp = ReadRec { cell: 1, replica: 0, version: st.len(), value: pv };
    let rsec = ReadRec { cell: 1, replica: 1, version: 0, value: sv };
    let rs: Seq<ReadRec> = seq![rp, rsec];

    assert(rs.len() == 2);
    assert(rs[0].cell == rs[1].cell);
    assert(rs[0].replica != rs[1].replica);
    assert(rs[0].value != rs[1].value); // 10 != -1
    assert(a4_holds(rs)) by {
        assert(0 <= 0 < rs.len() && 0 <= 1 < rs.len()
            && rs[0].cell == rs[1].cell
            && rs[0].replica != rs[1].replica
            && rs[0].value != rs[1].value);
    }
}

// Regime non-vacuity: two primary reads MAY legitimately differ in value when
// they are at different versions. Without this, thm_primary_no_split_at_version
// could hold vacuously by all primary reads being equal. Here versions 1 and 2
// carry values 5 and 7, monotone and distinct.
pub proof fn lemma_cross_version_primary_differs()
    ensures
        exists|evs: Seq<Ev>, i: nat, j: nat|
            #![trigger pread_version(evs, i), pread_version(evs, j)]
            i <= j && j <= evs.len()
            && pread_version(evs, i) != pread_version(evs, j)
            && pread_value(evs, i) != pread_value(evs, j),
{
    let evs: Seq<Ev> = seq![Ev::Write(5), Ev::ReadP(0), Ev::Write(7), Ev::ReadP(0)];

    assert(state_after(evs, 0) =~= Seq::<int>::empty());
    assert(state_after(evs, 1) == apply(state_after(evs, 0), evs[0]));
    assert(state_after(evs, 1) =~= seq![5int]);
    assert(state_after(evs, 2) == apply(state_after(evs, 1), evs[1]));
    assert(state_after(evs, 2) =~= seq![5int]);            // ReadP: unchanged
    assert(state_after(evs, 3) == apply(state_after(evs, 2), evs[2]));
    assert(state_after(evs, 3) =~= seq![5int, 7int]);

    assert(pread_version(evs, 1) == 1);
    assert(pread_value(evs, 1) == 5);
    assert(pread_version(evs, 3) == 2);
    assert(pread_value(evs, 3) == 7);

    assert(1nat <= 3nat && 3nat <= evs.len()
        && pread_version(evs, 1) != pread_version(evs, 3)
        && pread_value(evs, 1) != pread_value(evs, 3));
}

} // verus!