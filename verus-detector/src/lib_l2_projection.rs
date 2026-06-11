#![allow(unused_imports)]
use vstd::prelude::*;

verus! {
pub open spec fn null_value() -> int { 0 }

pub struct OpRecord {
    pub read_set:     Seq<int>,
    pub read_values:  Seq<(int, int)>,
    pub read_time:    int,
    pub write_set:    Seq<int>,
    pub write_values: Seq<(int, int)>,
    pub write_time:   int,
}

pub open spec fn reads_spec(op: OpRecord, c: int) -> bool {
    exists |k: int| 0 <= k < op.read_set.len() && op.read_set[k] == c
}

pub open spec fn writes_spec(op: OpRecord, c: int) -> bool {
    exists |k: int| 0 <= k < op.write_set.len() && op.write_set[k] == c
}

pub open spec fn first_match(s: Seq<(int, int)>, c: int, k: int) -> bool {
    0 <= k < s.len()
    && s[k].0 == c
    && (forall |j: int| 0 <= j < k ==> s[j].0 != c)
}

pub open spec fn first_value(s: Seq<(int, int)>, c: int) -> Option<int> {
    if exists |k: int| first_match(s, c, k) {
        Some(s[choose |k: int| first_match(s, c, k)].1)
    } else {
        None
    }
}

pub open spec fn a3_witness(h: Seq<OpRecord>, j: int, c: int, v: int) -> bool {
    0 <= j < h.len()
    && reads_spec(h[j], c)
    && first_value(h[j].read_values, c) == Some(v)
    && v != null_value()
    && (forall |k: int|
        !(0 <= k < h.len()
          && k != j
          && writes_spec(h[k], c)
          && h[k].write_time <= h[j].read_time
          && first_value(h[k].write_values, c) == Some(v)))
}

pub open spec fn a3(h: Seq<OpRecord>) -> bool {
    exists |j: int, c: int, v: int| a3_witness(h, j, c, v)
}

pub struct TxnRec {
    pub committed:    bool,
    pub aborted:      bool,
    pub read_set:     Set<int>,
    pub read_values:  Map<int, int>,
    pub read_at:      Map<int, int>,
    pub write_set:    Set<int>,
    pub write_values: Map<int, int>,
    pub commit_time:  int,
}

pub struct CSt {
    pub txns: Map<int, TxnRec>,
}

pub open spec fn committed_clean(cs: CSt, t: int) -> bool {
    cs.txns.contains_key(t) && cs.txns[t].committed && !cs.txns[t].aborted
}

pub open spec fn l2i_support(cs: CSt) -> bool {
    forall |t: int, c: int|
        #![trigger cs.txns[t].read_set.contains(c)]
        (committed_clean(cs, t) && cs.txns[t].read_set.contains(c))
        ==> exists |w: int|
            #![trigger cs.txns[w].write_set.contains(c)]
            committed_clean(cs, w)
            && cs.txns[w].write_set.contains(c)
            && cs.txns[w].write_values[c] == cs.txns[t].read_values[c]
            && cs.txns[w].commit_time <= cs.txns[t].read_at[c]
}

pub open spec fn emit_reads_faithful(h: Seq<OpRecord>, cs: CSt) -> bool {
    forall |j: int, c: int|
        #![trigger reads_spec(h[j], c)]
        (0 <= j < h.len() && reads_spec(h[j], c))
        ==> !writes_spec(h[j], c)
            && exists |t: int|
                #![trigger cs.txns[t].read_set.contains(c)]
                committed_clean(cs, t)
                && cs.txns[t].read_set.contains(c)
                && first_value(h[j].read_values, c) == Some(cs.txns[t].read_values[c])
                && h[j].read_time == cs.txns[t].read_at[c]
}

pub open spec fn emit_writes_realized(h: Seq<OpRecord>, cs: CSt) -> bool {
    forall |w: int, c: int|
        #![trigger cs.txns[w].write_set.contains(c)]
        (committed_clean(cs, w) && cs.txns[w].write_set.contains(c))
        ==> exists |k: int|
            #![trigger writes_spec(h[k], c)]
            0 <= k < h.len()
            && writes_spec(h[k], c)
            && first_value(h[k].write_values, c) == Some(cs.txns[w].write_values[c])
            && h[k].write_time == cs.txns[w].commit_time
}

pub open spec fn faithful_emit(h: Seq<OpRecord>, cs: CSt) -> bool {
    emit_reads_faithful(h, cs) && emit_writes_realized(h, cs)
}

pub proof fn thm_l2_projection_no_a3(h: Seq<OpRecord>, cs: CSt)
    requires
        l2i_support(cs),
        faithful_emit(h, cs),
    ensures
        !a3(h),
{
    assert forall |j: int, c: int, v: int| !a3_witness(h, j, c, v) by {
        if a3_witness(h, j, c, v) {
            assert(0 <= j < h.len());
            assert(reads_spec(h[j], c));
            assert(first_value(h[j].read_values, c) == Some(v));
            assert(v != null_value());

            assert(emit_reads_faithful(h, cs));
            assert(!writes_spec(h[j], c));

            let t = choose |t: int|
                committed_clean(cs, t)
                && cs.txns[t].read_set.contains(c)
                && first_value(h[j].read_values, c) == Some(cs.txns[t].read_values[c])
                && h[j].read_time == cs.txns[t].read_at[c];
            assert(committed_clean(cs, t)
                && cs.txns[t].read_set.contains(c)
                && first_value(h[j].read_values, c) == Some(cs.txns[t].read_values[c])
                && h[j].read_time == cs.txns[t].read_at[c]);
            assert(Some(v) == Some(cs.txns[t].read_values[c]));
            assert(v == cs.txns[t].read_values[c]);

            assert(l2i_support(cs));

            let w = choose |w: int|
                committed_clean(cs, w)
                && cs.txns[w].write_set.contains(c)
                && cs.txns[w].write_values[c] == cs.txns[t].read_values[c]
                && cs.txns[w].commit_time <= cs.txns[t].read_at[c];
            assert(committed_clean(cs, w)
                && cs.txns[w].write_set.contains(c)
                && cs.txns[w].write_values[c] == cs.txns[t].read_values[c]
                && cs.txns[w].commit_time <= cs.txns[t].read_at[c]);
            assert(cs.txns[w].write_values[c] == v);
            assert(cs.txns[w].commit_time <= h[j].read_time);

            assert(emit_writes_realized(h, cs));

            let k = choose |k: int|
                0 <= k < h.len()
                && writes_spec(h[k], c)
                && first_value(h[k].write_values, c) == Some(cs.txns[w].write_values[c])
                && h[k].write_time == cs.txns[w].commit_time;
            assert(0 <= k < h.len()
                && writes_spec(h[k], c)
                && first_value(h[k].write_values, c) == Some(cs.txns[w].write_values[c])
                && h[k].write_time == cs.txns[w].commit_time);
            assert(first_value(h[k].write_values, c) == Some(v));
            assert(h[k].write_time <= h[j].read_time);
            assert(writes_spec(h[k], c));
            assert(!writes_spec(h[j], c));
            assert(k != j);

            assert(0 <= k < h.len()
                && k != j
                && writes_spec(h[k], c)
                && h[k].write_time <= h[j].read_time
                && first_value(h[k].write_values, c) == Some(v));
            assert(!(0 <= k < h.len()
                && k != j
                && writes_spec(h[k], c)
                && h[k].write_time <= h[j].read_time
                && first_value(h[k].write_values, c) == Some(v)));  // from a3_witness's forall
            assert(false);
        }
    }
}

pub open spec fn witness_writer() -> TxnRec {
    TxnRec {
        committed: true,
        aborted: false,
        read_set: Set::empty(),
        read_values: Map::empty(),
        read_at: Map::empty(),
        write_set: Set::empty().insert(1),
        write_values: Map::empty().insert(1, 5),
        commit_time: 1,
    }
}

pub open spec fn witness_reader() -> TxnRec {
    TxnRec {
        committed: true,
        aborted: false,
        read_set: Set::empty().insert(1),
        read_values: Map::empty().insert(1, 5),
        read_at: Map::empty().insert(1, 2),
        write_set: Set::empty(),
        write_values: Map::empty(),
        commit_time: 3,
    }
}

pub open spec fn witness_cst() -> CSt {
    CSt { txns: Map::empty().insert(0, witness_writer()).insert(10, witness_reader()) }
}

pub open spec fn witness_write_op() -> OpRecord {
    OpRecord {
        read_set: Seq::empty(),
        read_values: Seq::empty(),
        read_time: 0,
        write_set: seq![1int],
        write_values: seq![(1int, 5int)],
        write_time: 1,
    }
}

pub open spec fn witness_read_op() -> OpRecord {
    OpRecord {
        read_set: seq![1int],
        read_values: seq![(1int, 5int)],
        read_time: 2,
        write_set: Seq::empty(),
        write_values: Seq::empty(),
        write_time: 0,
    }
}

pub open spec fn witness_trace() -> Seq<OpRecord> {
    seq![witness_write_op(), witness_read_op()]
}

pub proof fn lemma_projection_nonvacuous()
    ensures
        exists |h: Seq<OpRecord>, cs: CSt|
            #![trigger l2i_support(cs), faithful_emit(h, cs)]
            l2i_support(cs) && faithful_emit(h, cs) && !a3(h),
{
    let cs = witness_cst();
    let h = witness_trace();

    assert(l2i_support(cs)) by {
        assert forall |t: int, c: int|
            #![trigger cs.txns[t].read_set.contains(c)]
            (committed_clean(cs, t) && cs.txns[t].read_set.contains(c)) implies
            exists |w: int|
                #![trigger cs.txns[w].write_set.contains(c)]
                committed_clean(cs, w)
                && cs.txns[w].write_set.contains(c)
                && cs.txns[w].write_values[c] == cs.txns[t].read_values[c]
                && cs.txns[w].commit_time <= cs.txns[t].read_at[c]
        by {
            assert(cs.txns[10].read_set =~= Set::empty().insert(1));
            if t == 10 && c == 1 {
                assert(committed_clean(cs, 0));
                assert(cs.txns[0].write_set.contains(1));
                assert(cs.txns[0].write_values[1] == 5);
                assert(cs.txns[10].read_values[1] == 5);
                assert(cs.txns[0].commit_time == 1);
                assert(cs.txns[10].read_at[1] == 2);
                // w == 0 witnesses.
                assert(committed_clean(cs, 0)
                    && cs.txns[0].write_set.contains(1)
                    && cs.txns[0].write_values[1] == cs.txns[10].read_values[1]
                    && cs.txns[0].commit_time <= cs.txns[10].read_at[1]);
            }
        }
    }

    assert(emit_reads_faithful(h, cs)) by {
        assert forall |j: int, c: int|
            #![trigger reads_spec(h[j], c)]
            (0 <= j < h.len() && reads_spec(h[j], c)) implies
                !writes_spec(h[j], c)
                && exists |t: int|
                    #![trigger cs.txns[t].read_set.contains(c)]
                    committed_clean(cs, t)
                    && cs.txns[t].read_set.contains(c)
                    && first_value(h[j].read_values, c) == Some(cs.txns[t].read_values[c])
                    && h[j].read_time == cs.txns[t].read_at[c]
        by {
            if j == 1 {
                assert(h[1] == witness_read_op());
                if reads_spec(h[1], c) {
                    assert(h[1].read_set =~= seq![1int]);
                    assert(c == 1) by {
                        let kk = choose |kk: int| 0 <= kk < h[1].read_set.len() && h[1].read_set[kk] == c;
                        assert(0 <= kk < 1);
                        assert(kk == 0);
                        assert(h[1].read_set[0] == 1);
                    }
                    assert(!writes_spec(h[1], 1)) by {
                        assert(h[1].write_set.len() == 0);
                    }
                    assert(first_match(h[1].read_values, 1, 0)) by {
                        assert(h[1].read_values[0] == (1int, 5int));
                    }
                    assert(first_value(h[1].read_values, 1) == Some(5int)) by {
                        let kc = choose |kc: int| first_match(h[1].read_values, 1, kc);
                        assert(first_match(h[1].read_values, 1, 0));
                        assert(kc == 0);
                    }

                    assert(committed_clean(cs, 10));
                    assert(cs.txns[10].read_set.contains(1));
                    assert(cs.txns[10].read_values[1] == 5);
                    assert(cs.txns[10].read_at[1] == 2);
                    assert(h[1].read_time == 2);
                }
            } else {
                assert(h[0] == witness_write_op());
                assert(h[0].read_set.len() == 0);
            }
        }
    }

    assert(emit_writes_realized(h, cs)) by {
        assert forall |w: int, c: int|
            #![trigger cs.txns[w].write_set.contains(c)]
            (committed_clean(cs, w) && cs.txns[w].write_set.contains(c)) implies
            exists |k: int|
                #![trigger writes_spec(h[k], c)]
                0 <= k < h.len()
                && writes_spec(h[k], c)
                && first_value(h[k].write_values, c) == Some(cs.txns[w].write_values[c])
                && h[k].write_time == cs.txns[w].commit_time
        by {
            assert(cs.txns[0].write_set =~= Set::empty().insert(1));

            if w == 0 && c == 1 {
                assert(h[0] == witness_write_op());
                assert(writes_spec(h[0], 1)) by {
                    assert(h[0].write_set[0] == 1);
                }
                assert(first_match(h[0].write_values, 1, 0)) by {
                    assert(h[0].write_values[0] == (1int, 5int));
                }
                assert(first_value(h[0].write_values, 1) == Some(5int)) by {
                    let kc = choose |kc: int| first_match(h[0].write_values, 1, kc);
                    assert(first_match(h[0].write_values, 1, 0));
                    assert(kc == 0);
                }
                assert(cs.txns[0].write_values[1] == 5);
                assert(h[0].write_time == 1);
                assert(cs.txns[0].commit_time == 1);
                // k == 0 witnesses.
            }
        }
    }

    thm_l2_projection_no_a3(h, cs);

    assert(l2i_support(cs) && faithful_emit(h, cs) && !a3(h));
}

pub proof fn lemma_unsupported_read_admits_a3()
    ensures
        exists |h: Seq<OpRecord>| #[trigger] a3(h),
{
    let h: Seq<OpRecord> = seq![witness_read_op()];

    assert(h.len() == 1);

    assert(h[0] == witness_read_op());

    assert(reads_spec(h[0], 1)) by {
        assert(h[0].read_set[0] == 1);
    }

    assert(first_match(h[0].read_values, 1, 0)) by {
        assert(h[0].read_values[0] == (1int, 5int));
    }

    assert(first_value(h[0].read_values, 1) == Some(5int)) by {
        let kc = choose |kc: int| first_match(h[0].read_values, 1, kc);
        assert(first_match(h[0].read_values, 1, 0));
        assert(kc == 0);
    }

    assert forall |k: int|
        !(0 <= k < h.len()
          && k != 0
          && writes_spec(h[k], 1)
          && h[k].write_time <= h[0].read_time
          && first_value(h[k].write_values, 1) == Some(5int))
    by { }

    assert(a3_witness(h, 0, 1, 5));
    assert(a3(h)) by {
        assert(a3_witness(h, 0, 1, 5));
    }
}

} // verus!