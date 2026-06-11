use vstd::prelude::*;

verus! {
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

pub open spec fn apply(s: Seq<int>, e: Ev) -> Seq<int> {
    match e {
        Ev::Write(v) => s.push(v),
        Ev::ReadP(_) => s,
        Ev::ReadS(_, _, _) => s,
    }
}

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

pub open spec fn value_at(s: Seq<int>, k: nat) -> int {
    if k == 0 { nullv() } else { s[(k - 1) as int] }
}

pub open spec fn pread_version(evs: Seq<Ev>, i: nat) -> nat {
    state_after(evs, i).len()
}
pub open spec fn pread_value(evs: Seq<Ev>, i: nat) -> int {
    head_value(state_after(evs, i))
}

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
        assert(state_after(evs, (j - 1) as nat).len() == state_after(evs, i).len());

        assert(state_after(evs, j)
            == apply(state_after(evs, (j - 1) as nat), evs[(j - 1) as int]));
        lemma_apply_step(state_after(evs, (j - 1) as nat), evs[(j - 1) as int]);
        assert(!is_write(evs[(j - 1) as int]));
        assert(state_after(evs, j) =~= state_after(evs, (j - 1) as nat));

        lemma_state_stable_eq_len(evs, i, (j - 1) as nat);
    }
}

pub proof fn thm_primary_version_monotone(evs: Seq<Ev>, i: nat, j: nat)
    requires
        i <= j,
        j <= evs.len(),
    ensures
        pread_version(evs, i) <= pread_version(evs, j),
{
    lemma_state_monotone_len(evs, i, j);
}

pub proof fn thm_primary_no_split_at_version(evs: Seq<Ev>, i: nat, j: nat)
    requires
        i <= j,
        j <= evs.len(),
        pread_version(evs, i) == pread_version(evs, j),
    ensures
        pread_value(evs, i) == pread_value(evs, j),
{
    lemma_state_stable_eq_len(evs, i, j);
    assert(head_value(state_after(evs, i)) == head_value(state_after(evs, j)));
}

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

pub struct ReadRec {
    pub cell: nat,
    pub replica: nat,
    pub version: nat,
    pub value: int,
}

pub open spec fn a4_holds(rs: Seq<ReadRec>) -> bool {
    exists|i: int, j: int|
        #![trigger rs[i].cell, rs[j].cell]
        0 <= i < rs.len() && 0 <= j < rs.len()
        && rs[i].cell == rs[j].cell
        && rs[i].replica != rs[j].replica
        && rs[i].value != rs[j].value
}

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
    let pv = head_value(st);
    let sv = value_at(st, 0);
    assert(pv == 10);
    assert(sv == nullv());

    let rp = ReadRec { cell: 1, replica: 0, version: st.len(), value: pv };
    let rsec = ReadRec { cell: 1, replica: 1, version: 0, value: sv };
    let rs: Seq<ReadRec> = seq![rp, rsec];

    assert(rs.len() == 2);
    assert(rs[0].cell == rs[1].cell);
    assert(rs[0].replica != rs[1].replica);
    assert(rs[0].value != rs[1].value);
    assert(a4_holds(rs)) by {
        assert(0 <= 0 < rs.len() && 0 <= 1 < rs.len()
            && rs[0].cell == rs[1].cell
            && rs[0].replica != rs[1].replica
            && rs[0].value != rs[1].value);
    }
}

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
    assert(state_after(evs, 2) =~= seq![5int]);
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