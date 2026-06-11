#![allow(unused_imports)]
#![allow(dead_code)]
use vstd::prelude::*;

verus! {
pub type CellId  = int;
pub type TxnId   = int;
pub type Value   = int;
pub type Time    = int;

pub struct TxnState {
    pub started:       bool,
    pub committed:     bool,
    pub aborted:       bool,
    pub read_set:      Set<CellId>,
    pub read_values:   Map<CellId, Value>,
    pub write_set:     Set<CellId>,
    pub write_values:  Map<CellId, Value>,
    pub predecessors:  Set<TxnId>,
    pub read_from:     Map<CellId, TxnId>,
    pub read_at:       Map<CellId, Time>,
    pub commit_time:   Time,
}

pub open spec fn empty_txn() -> TxnState {
    TxnState {
        started:       false,
        committed:     false,
        aborted:       false,
        read_set:      Set::empty(),
        read_values:   Map::empty(),
        write_set:     Set::empty(),
        write_values:  Map::empty(),
        predecessors:  Set::empty(),
        read_from:     Map::empty(),
        read_at:       Map::empty(),
        commit_time:   0,
    }
}

pub struct RuntimeState {
    pub now:           Time,
    pub txns:          Map<TxnId, TxnState>,
    pub cell_value:    Map<CellId, Value>,
    pub cell_writer:   Map<CellId, TxnId>,
    pub all_txns:      Set<TxnId>,
}

pub open spec fn initial_state() -> RuntimeState {
    RuntimeState {
        now:           0,
        txns:          Map::empty(),
        cell_value:    Map::empty(),
        cell_writer:   Map::empty(),
        all_txns:      Set::empty(),
    }
}

pub open spec fn reads_fresh(s: RuntimeState, t: TxnId) -> bool {
    let txn = s.txns[t];
    forall |c: CellId| #![trigger txn.read_set.contains(c)]
        txn.read_set.contains(c)
        ==> s.cell_value.contains_key(c)
            && s.cell_value[c] == txn.read_values[c]
}

pub open spec fn predecessors_clean(s: RuntimeState, t: TxnId) -> bool {
    let txn = s.txns[t];
    forall |p: TxnId| #![trigger txn.predecessors.contains(p)]
        txn.predecessors.contains(p)
        ==> s.txns.contains_key(p)
            && s.txns[p].committed
            && !s.txns[p].aborted
}

pub open spec fn commit_valid(s: RuntimeState, t: TxnId) -> bool {
    s.txns.contains_key(t)
    && s.txns[t].started
    && !s.txns[t].committed
    && !s.txns[t].aborted
    && reads_fresh(s, t)
    && predecessors_clean(s, t)
}

pub open spec fn pred_closed(s: RuntimeState) -> bool {
    forall |u: TxnId, p: TxnId, q: TxnId|
        #![trigger s.txns[u].predecessors.contains(p), s.txns[p].predecessors.contains(q)]
        s.txns.contains_key(u)
        && s.txns[u].predecessors.contains(p)
        && s.txns[p].predecessors.contains(q)
        ==> s.txns[u].predecessors.contains(q)
}

pub open spec fn invariant_committed_predecessors_clean(s: RuntimeState) -> bool {
    forall |t: TxnId| #![trigger s.txns[t].committed]
        s.txns.contains_key(t)
        && s.txns[t].committed
        && !s.txns[t].aborted
        ==> predecessors_clean(s, t)
}

pub open spec fn step_begin(s: RuntimeState, t: TxnId) -> RuntimeState {
    RuntimeState {
        now: s.now + 1,
        txns: s.txns.insert(t, TxnState {
            started: true,
            ..empty_txn()
        }),
        all_txns: s.all_txns.insert(t),
        ..s
    }
}

pub open spec fn step_read(s: RuntimeState, t: TxnId, c: CellId) -> RuntimeState
    recommends
        s.txns.contains_key(t),
        s.cell_value.contains_key(c),
        s.txns.contains_key(s.cell_writer[c]),
{
    let txn = s.txns[t];
    let writer = s.cell_writer[c];
    let new_txn = TxnState {
        read_set: txn.read_set.insert(c),
        read_values: txn.read_values.insert(c, s.cell_value[c]),
        predecessors: txn.predecessors.insert(writer).union(s.txns[writer].predecessors),
        read_from: txn.read_from.insert(c, writer),
        read_at: txn.read_at.insert(c, s.now),
        ..txn
    };

    RuntimeState {
        now: s.now + 1,
        txns: s.txns.insert(t, new_txn),
        ..s
    }
}

pub open spec fn step_write(s: RuntimeState, t: TxnId, c: CellId, v: Value)
    -> RuntimeState
    recommends s.txns.contains_key(t)
{
    let txn = s.txns[t];
    let new_txn = TxnState {
        write_set: txn.write_set.insert(c),
        write_values: txn.write_values.insert(c, v),
        ..txn
    };
    RuntimeState {
        now: s.now + 1,
        txns: s.txns.insert(t, new_txn),
        ..s
    }
}

pub open spec fn step_commit(s: RuntimeState, t: TxnId) -> RuntimeState
    recommends commit_valid(s, t)
{
    let txn = s.txns[t];
    let new_txn = TxnState {
        committed: true,
        commit_time: s.now,
        ..txn
    };

    RuntimeState {
        now: s.now + 1,
        txns: s.txns.insert(t, new_txn),
        cell_value: publish_writes(s.cell_value, txn.write_set,
                                    txn.write_values),
        cell_writer: publish_writer(s.cell_writer, txn.write_set, t),
        ..s
    }
}

pub open spec fn publish_writes(
    cv: Map<CellId, Value>,
    ws: Set<CellId>,
    wv: Map<CellId, Value>,
) -> Map<CellId, Value> {
    Map::new(
        |c: CellId| ws.contains(c) || cv.contains_key(c),
        |c: CellId| if ws.contains(c) { wv[c] } else { cv[c] },
    )
}

pub open spec fn publish_writer(
    cw: Map<CellId, TxnId>,
    ws: Set<CellId>,
    t: TxnId,
) -> Map<CellId, TxnId> {
    Map::new(
        |c: CellId| ws.contains(c) || cw.contains_key(c),
        |c: CellId| if ws.contains(c) { t } else { cw[c] },
    )
}

pub open spec fn step_abort(s: RuntimeState, t: TxnId) -> RuntimeState {
    let txn = s.txns[t];
    let new_txn = TxnState { aborted: true, ..txn };
    let new_txns = cascade_abort(s.txns.insert(t, new_txn), t);
    RuntimeState {
        now: s.now + 1,
        txns: new_txns,
        ..s
    }
}

pub open spec fn cascade_abort(
    txns: Map<TxnId, TxnState>,
    t: TxnId,
) -> Map<TxnId, TxnState> {
    Map::new(
        |id: TxnId| txns.contains_key(id),
        |id: TxnId| {
            let txn = txns[id];
            if txn.predecessors.contains(t) {
                TxnState { aborted: true, ..txn }
            } else {
                txn
            }
        },
    )
}

pub open spec fn a1_witness_at_commit(s: RuntimeState, t: TxnId) -> bool {
    s.txns.contains_key(t)
    && s.txns[t].committed
    && exists |c: CellId|
        #![trigger s.txns[t].read_set.contains(c)]
        s.txns[t].read_set.contains(c)
        && s.cell_value.contains_key(c)
        && s.cell_value[c] != s.txns[t].read_values[c]
}

pub open spec fn a3_witness(s: RuntimeState, t: TxnId) -> bool {
    s.txns.contains_key(t)
    && s.txns[t].committed
    && !s.txns[t].aborted
    && exists |p: TxnId|
        #![trigger s.txns[t].predecessors.contains(p)]
        s.txns[t].predecessors.contains(p)
        && s.txns.contains_key(p)
        && s.txns[p].aborted
}

pub proof fn lemma_l2_no_a1_at_commit(s: RuntimeState, t: TxnId)
    requires commit_valid(s, t),
    ensures
        forall |c: CellId|
            s.txns[t].read_set.contains(c)
            && !s.txns[t].write_set.contains(c)
            ==> s.cell_value.contains_key(c)
                && s.cell_value[c] == s.txns[t].read_values[c],
{ }

pub proof fn lemma_l2_no_a3_at_commit(s: RuntimeState, t: TxnId)
    requires commit_valid(s, t),
    ensures
        forall |p: TxnId|
            s.txns[t].predecessors.contains(p)
            ==> s.txns.contains_key(p)
                && s.txns[p].committed
                && !s.txns[p].aborted,
{ }

pub proof fn lemma_cascade_preserves_clean_predecessors(
    s: RuntimeState, t: TxnId,
)
    requires
        invariant_committed_predecessors_clean(s),
        pred_closed(s),
        s.txns.contains_key(t),
    ensures
        invariant_committed_predecessors_clean(step_abort(s, t)),
{
    let s2 = step_abort(s, t);
    assert forall |u: TxnId|
        s2.txns.contains_key(u)
        && s2.txns[u].committed
        && !s2.txns[u].aborted
        implies predecessors_clean(s2, u)
    by {
        let u_txn = s2.txns[u];
        assert(!u_txn.aborted);
        assert(!s.txns[u].predecessors.contains(t));
        assert(u_txn.predecessors == s.txns[u].predecessors);
        assert(predecessors_clean(s, u));
        assert forall |p: TxnId|
            u_txn.predecessors.contains(p)
            implies s2.txns.contains_key(p)
                && s2.txns[p].committed
                && !s2.txns[p].aborted
        by {
            assert(!s.txns[u].predecessors.contains(t));

            if s.txns[p].predecessors.contains(t) {
                assert(s.txns[u].predecessors.contains(t));
                assert(false);
            }
            assert(!s.txns[p].predecessors.contains(t));
            assert(p != t);
            assert(s.txns.contains_key(p));
            assert(s.txns[p].committed);
            assert(!s.txns[p].aborted);
            assert(s2.txns.contains_key(p));
            assert(s2.txns[p].committed);
            assert(!s2.txns[p].aborted);
        }
    }
}

pub proof fn lemma_commit_valid_implies_no_a1(s: RuntimeState, t: TxnId)
    requires commit_valid(s, t),
    ensures
        forall |c: CellId|
            #![trigger s.txns[t].read_set.contains(c)]
            s.txns[t].read_set.contains(c)
            && !s.txns[t].write_set.contains(c)
            ==> s.cell_value[c] == s.txns[t].read_values[c],
{ }

pub proof fn lemma_commit_valid_implies_no_a3(s: RuntimeState, t: TxnId)
    requires commit_valid(s, t),
    ensures !a3_witness(step_commit(s, t), t)
        || forall |p: TxnId|
            s.txns[t].predecessors.contains(p)
            ==> !s.txns[p].aborted,
{ }

pub proof fn lemma_no_cascade_admits_a3(s: RuntimeState, t: TxnId, p: TxnId)
    requires
        s.txns.contains_key(t),
        s.txns[t].committed,
        !s.txns[t].aborted,
        s.txns[t].predecessors.contains(p),
        s.txns.contains_key(p),
        s.txns[p].aborted,
    ensures a3_witness(s, t),
{
    assert(s.txns[t].predecessors.contains(p)
        && s.txns.contains_key(p)
        && s.txns[p].aborted);
}

pub open spec fn inv_writers_committed(s: RuntimeState) -> bool {
    forall |c: CellId| #![trigger s.cell_writer[c]]
        s.cell_value.contains_key(c)
        ==> s.txns.contains_key(s.cell_writer[c])
            && s.txns[s.cell_writer[c]].committed
}

pub open spec fn inv_cell_domains(s: RuntimeState) -> bool {
    forall |c: CellId| #![trigger s.cell_value.contains_key(c)]
        s.cell_value.contains_key(c) <==> s.cell_writer.contains_key(c)
}

pub open spec fn inv_cell_writer_wrote(s: RuntimeState) -> bool {
    forall |c: CellId| #![trigger s.cell_writer[c]]
        s.cell_value.contains_key(c)
        ==> s.txns.contains_key(s.cell_writer[c])
            && s.txns[s.cell_writer[c]].write_set.contains(c)
            && s.txns[s.cell_writer[c]].write_values[c] == s.cell_value[c]
}

pub open spec fn inv_read_provenance(s: RuntimeState) -> bool {
    forall |tt: TxnId, cc: CellId| #![trigger s.txns[tt].read_set.contains(cc)]
        (s.txns.contains_key(tt) && s.txns[tt].read_set.contains(cc))
        ==> s.txns[tt].read_from.contains_key(cc)
            && s.txns[tt].predecessors.contains(s.txns[tt].read_from[cc])
            && s.txns.contains_key(s.txns[tt].read_from[cc])
            && s.txns[s.txns[tt].read_from[cc]].write_set.contains(cc)
            && s.txns[s.txns[tt].read_from[cc]].write_values[cc]
                 == s.txns[tt].read_values[cc]
}

pub open spec fn inv_committed_frozen(s: RuntimeState) -> bool {
    forall |u: TxnId, p: TxnId| #![trigger s.txns[u].predecessors.contains(p)]
        s.txns.contains_key(u) && s.txns[u].predecessors.contains(p)
        ==> s.txns.contains_key(p) && s.txns[p].committed
}

pub proof fn lemma_step_read_preserves_pred_closed(
    s: RuntimeState, t: TxnId, c: CellId,
)
    requires
        pred_closed(s),
        inv_writers_committed(s),
        inv_committed_frozen(s),
        s.txns.contains_key(t),
        s.cell_value.contains_key(c),
        !s.txns[t].committed,
    ensures
        pred_closed(step_read(s, t, c)),
{
    let s2 = step_read(s, t, c);
    let writer = s.cell_writer[c];
    let old = s.txns[t].predecessors;
    let wp = s.txns[writer].predecessors;

    assert(s2.txns[t].predecessors =~= old.insert(writer).union(wp));

    assert forall |u: TxnId, p: TxnId, q: TxnId|
        #![trigger s2.txns[u].predecessors.contains(p), s2.txns[p].predecessors.contains(q)]
        s2.txns.contains_key(u)
        && s2.txns[u].predecessors.contains(p)
        && s2.txns[p].predecessors.contains(q)
        implies s2.txns[u].predecessors.contains(q)
    by {
        if u == t {
            if p == t {
            } else {
                assert(s2.txns[p].predecessors =~= s.txns[p].predecessors);
                assert(s2.txns[t].predecessors.contains(p));
                if old.contains(p) {
                    assert(s.txns[t].predecessors.contains(p));
                    assert(s.txns[p].predecessors.contains(q));
                    assert(old.contains(q));
                } else if p == writer {
                    assert(s.txns[writer].predecessors.contains(q));
                    assert(wp.contains(q));
                } else {
                    assert(s.txns.contains_key(writer));
                    assert(wp.contains(p));
                    assert(s.txns[writer].predecessors.contains(p));
                    assert(s.txns[p].predecessors.contains(q));
                    assert(wp.contains(q));
                }

                assert(old.insert(writer).union(wp).contains(q));
                assert(s2.txns[u].predecessors.contains(q));
            }
        } else {
            assert(s2.txns[u].predecessors =~= s.txns[u].predecessors);
            if p == t {
                assert(s.txns[u].predecessors.contains(t));
                assert(s.txns[t].committed);
                assert(false);
            } else {
                assert(s2.txns[p].predecessors =~= s.txns[p].predecessors);
                assert(s.txns[u].predecessors.contains(p));
                assert(s.txns[p].predecessors.contains(q));
                assert(s.txns[u].predecessors.contains(q));
            }
        }
    }
}

pub open spec fn inv_l2(s: RuntimeState) -> bool {
    &&& invariant_committed_predecessors_clean(s)
    &&& pred_closed(s)
    &&& inv_writers_committed(s)
    &&& inv_committed_frozen(s)
    &&& inv_cell_domains(s)
    &&& inv_cell_writer_wrote(s)
    &&& inv_read_provenance(s)
}

pub open spec fn inv_commit_time_le_now(s: RuntimeState) -> bool {
    forall |t: TxnId| #![trigger s.txns[t].commit_time]
        (s.txns.contains_key(t) && s.txns[t].committed)
        ==> s.txns[t].commit_time <= s.now
}

pub open spec fn inv_read_temporal(s: RuntimeState) -> bool {
    forall |tt: TxnId, cc: CellId| #![trigger s.txns[tt].read_set.contains(cc)]
        (s.txns.contains_key(tt) && s.txns[tt].read_set.contains(cc))
        ==> s.txns.contains_key(s.txns[tt].read_from[cc])
            && s.txns[s.txns[tt].read_from[cc]].commit_time
                 <= s.txns[tt].read_at[cc]
}

pub open spec fn inv_l2t(s: RuntimeState) -> bool {
    &&& inv_l2(s)
    &&& inv_commit_time_le_now(s)
    &&& inv_read_temporal(s)
}

pub proof fn lemma_begin_preserves_inv_l2(s: RuntimeState, t: TxnId)
    requires inv_l2(s), !s.txns.contains_key(t),
    ensures inv_l2(step_begin(s, t)),
{
    let s2 = step_begin(s, t);

    assert(inv_cell_writer_wrote(s2)) by {
        assert forall |c: CellId| #![trigger s2.cell_writer[c]]
            s2.cell_value.contains_key(c) implies
                s2.txns.contains_key(s2.cell_writer[c])
                && s2.txns[s2.cell_writer[c]].write_set.contains(c)
                && s2.txns[s2.cell_writer[c]].write_values[c] == s2.cell_value[c]
        by {
            assert(s2.cell_value[c] == s.cell_value[c]);
            assert(s2.cell_writer[c] == s.cell_writer[c]);
            let w = s.cell_writer[c];
            assert(s.txns.contains_key(w));
            assert(s.txns[w].write_set.contains(c));
            assert(s.txns[w].write_values[c] == s.cell_value[c]);
            assert(w != t);
            assert(s2.txns[w] == s.txns[w]);
        }
    }

    assert(inv_read_provenance(s2)) by {
        assert forall |tt: TxnId, cc: CellId| #![trigger s2.txns[tt].read_set.contains(cc)]
            (s2.txns.contains_key(tt) && s2.txns[tt].read_set.contains(cc)) implies
                s2.txns[tt].read_from.contains_key(cc)
                && s2.txns[tt].predecessors.contains(s2.txns[tt].read_from[cc])
                && s2.txns.contains_key(s2.txns[tt].read_from[cc])
                && s2.txns[s2.txns[tt].read_from[cc]].write_set.contains(cc)
                && s2.txns[s2.txns[tt].read_from[cc]].write_values[cc] == s2.txns[tt].read_values[cc]
        by {
            if tt == t {
                assert(s2.txns[t].read_set =~= Set::<CellId>::empty());
            } else {
                assert(s2.txns[tt] == s.txns[tt]);
                let w = s.txns[tt].read_from[cc];
                assert(s.txns[tt].read_set.contains(cc));
                assert(s.txns[tt].predecessors.contains(w));
                assert(s.txns.contains_key(w));
                assert(s.txns[w].write_set.contains(cc));
                assert(s.txns[w].write_values[cc] == s.txns[tt].read_values[cc]);
                assert(w != t);                   // w in s.txns, t fresh
                assert(s2.txns[w] == s.txns[w]);
            }
        }
    }
}

pub proof fn lemma_write_preserves_inv_l2(s: RuntimeState, t: TxnId, c: CellId, v: Value)
    requires inv_l2(s), s.txns.contains_key(t), !s.txns[t].committed,
    ensures inv_l2(step_write(s, t, c, v)),
{
    let s2 = step_write(s, t, c, v);

    assert(inv_cell_writer_wrote(s2)) by {
        assert forall |cc: CellId| #![trigger s2.cell_writer[cc]]
            s2.cell_value.contains_key(cc) implies
                s2.txns.contains_key(s2.cell_writer[cc])
                && s2.txns[s2.cell_writer[cc]].write_set.contains(cc)
                && s2.txns[s2.cell_writer[cc]].write_values[cc] == s2.cell_value[cc]
        by {
            assert(s2.cell_value[cc] == s.cell_value[cc]);
            assert(s2.cell_writer[cc] == s.cell_writer[cc]);
            let w = s.cell_writer[cc];
            assert(s.txns.contains_key(w) && s.txns[w].committed);
            assert(s.txns[w].write_set.contains(cc));
            assert(s.txns[w].write_values[cc] == s.cell_value[cc]);
            assert(w != t);
            assert(s2.txns[w] == s.txns[w]);
        }
    }

    assert(inv_read_provenance(s2)) by {
        assert forall |tt: TxnId, cc: CellId| #![trigger s2.txns[tt].read_set.contains(cc)]
            (s2.txns.contains_key(tt) && s2.txns[tt].read_set.contains(cc)) implies
                s2.txns[tt].read_from.contains_key(cc)
                && s2.txns[tt].predecessors.contains(s2.txns[tt].read_from[cc])
                && s2.txns.contains_key(s2.txns[tt].read_from[cc])
                && s2.txns[s2.txns[tt].read_from[cc]].write_set.contains(cc)
                && s2.txns[s2.txns[tt].read_from[cc]].write_values[cc] == s2.txns[tt].read_values[cc]
        by {
            if tt == t {
                assert(s2.txns[t].read_set == s.txns[t].read_set);
                assert(s2.txns[t].read_values == s.txns[t].read_values);
                assert(s2.txns[t].read_from == s.txns[t].read_from);
                assert(s2.txns[t].predecessors == s.txns[t].predecessors);
            } else {
                assert(s2.txns[tt] == s.txns[tt]);
            }

            let w = s.txns[tt].read_from[cc];

            assert(s.txns[tt].read_set.contains(cc));
            assert(s.txns[tt].predecessors.contains(w));
            assert(s.txns.contains_key(w));
            assert(s.txns[w].write_set.contains(cc));
            assert(s.txns[w].write_values[cc] == s.txns[tt].read_values[cc]);
            assert(s.txns[w].committed);
            assert(w != t);
            assert(s2.txns[w] == s.txns[w]);
        }
    }
}

pub proof fn lemma_abort_preserves_inv_l2(s: RuntimeState, t: TxnId)
    requires inv_l2(s), s.txns.contains_key(t),
    ensures inv_l2(step_abort(s, t)),
{
    lemma_cascade_preserves_clean_predecessors(s, t);

    let s2 = step_abort(s, t);

    assert forall |x: TxnId| #![trigger s2.txns[x]]
        s2.txns.contains_key(x) implies
            s.txns.contains_key(x)
            && s2.txns[x].predecessors == s.txns[x].predecessors
            && s2.txns[x].committed == s.txns[x].committed
            && s2.txns[x].write_set == s.txns[x].write_set
            && s2.txns[x].write_values == s.txns[x].write_values
            && s2.txns[x].read_set == s.txns[x].read_set
            && s2.txns[x].read_values == s.txns[x].read_values
            && s2.txns[x].read_from == s.txns[x].read_from
    by {
        let base = s.txns.insert(t, TxnState { aborted: true, ..s.txns[t] });

        assert(base.contains_key(x));
        assert(base[x].predecessors == s.txns[x].predecessors);
        assert(base[x].committed == s.txns[x].committed);
        assert(base[x].write_set == s.txns[x].write_set);
        assert(base[x].write_values == s.txns[x].write_values);
        assert(base[x].read_set == s.txns[x].read_set);
        assert(base[x].read_values == s.txns[x].read_values);
        assert(base[x].read_from == s.txns[x].read_from);
        assert(s2.txns[x].predecessors == base[x].predecessors);
        assert(s2.txns[x].committed == base[x].committed);
        assert(s2.txns[x].write_set == base[x].write_set);
        assert(s2.txns[x].write_values == base[x].write_values);
        assert(s2.txns[x].read_set == base[x].read_set);
        assert(s2.txns[x].read_values == base[x].read_values);
        assert(s2.txns[x].read_from == base[x].read_from);
    }

    assert(s2.cell_value =~= s.cell_value);
    assert(s2.cell_writer =~= s.cell_writer);
    assert(pred_closed(s2)) by {
        assert forall |u: TxnId, p: TxnId, q: TxnId|
            #![trigger s2.txns[u].predecessors.contains(p), s2.txns[p].predecessors.contains(q)]
            s2.txns.contains_key(u) && s2.txns[u].predecessors.contains(p)
            && s2.txns[p].predecessors.contains(q)
            implies s2.txns[u].predecessors.contains(q)
        by {
            assert(s2.txns[u].predecessors == s.txns[u].predecessors);
            assert(s2.txns[p].predecessors == s.txns[p].predecessors);
        }
    }

    assert(inv_committed_frozen(s2)) by {
        assert forall |u: TxnId, p: TxnId| #![trigger s2.txns[u].predecessors.contains(p)]
            s2.txns.contains_key(u) && s2.txns[u].predecessors.contains(p)
            implies s2.txns.contains_key(p) && s2.txns[p].committed
        by {
            assert(s2.txns[u].predecessors == s.txns[u].predecessors);
            assert(s2.txns[p].committed == s.txns[p].committed);
        }
    }

    assert(inv_cell_writer_wrote(s2)) by {
        assert forall |c: CellId| #![trigger s2.cell_writer[c]]
            s2.cell_value.contains_key(c) implies
                s2.txns.contains_key(s2.cell_writer[c])
                && s2.txns[s2.cell_writer[c]].write_set.contains(c)
                && s2.txns[s2.cell_writer[c]].write_values[c] == s2.cell_value[c]
        by {
            assert(s2.cell_value[c] == s.cell_value[c]);
            assert(s2.cell_writer[c] == s.cell_writer[c]);
            let w = s.cell_writer[c];
            assert(s.cell_value.contains_key(c));
            assert(s.txns.contains_key(w));
            assert(s.txns[w].write_set.contains(c));
            assert(s.txns[w].write_values[c] == s.cell_value[c]);
            assert(s2.txns.contains_key(w));
            assert(s2.txns[w].write_set == s.txns[w].write_set);
            assert(s2.txns[w].write_values == s.txns[w].write_values);
        }
    }

    assert(inv_read_provenance(s2)) by {
        assert forall |tt: TxnId, cc: CellId| #![trigger s2.txns[tt].read_set.contains(cc)]
            (s2.txns.contains_key(tt) && s2.txns[tt].read_set.contains(cc)) implies
                s2.txns[tt].read_from.contains_key(cc)
                && s2.txns[tt].predecessors.contains(s2.txns[tt].read_from[cc])
                && s2.txns.contains_key(s2.txns[tt].read_from[cc])
                && s2.txns[s2.txns[tt].read_from[cc]].write_set.contains(cc)
                && s2.txns[s2.txns[tt].read_from[cc]].write_values[cc] == s2.txns[tt].read_values[cc]
        by {
            assert(s2.txns[tt].read_set == s.txns[tt].read_set);
            assert(s2.txns[tt].read_values == s.txns[tt].read_values);
            assert(s2.txns[tt].read_from == s.txns[tt].read_from);
            assert(s2.txns[tt].predecessors == s.txns[tt].predecessors);
            let w = s.txns[tt].read_from[cc];
            assert(s.txns[tt].read_set.contains(cc));
            assert(s.txns[tt].predecessors.contains(w));
            assert(s.txns.contains_key(w));
            assert(s.txns[w].write_set.contains(cc));
            assert(s.txns[w].write_values[cc] == s.txns[tt].read_values[cc]);
            assert(s2.txns.contains_key(w));
            assert(s2.txns[w].write_set == s.txns[w].write_set);
            assert(s2.txns[w].write_values == s.txns[w].write_values);
        }
    }
}

pub proof fn lemma_read_preserves_inv_l2(s: RuntimeState, t: TxnId, c: CellId)
    requires
        inv_l2(s),
        s.txns.contains_key(t),
        s.cell_value.contains_key(c),
        !s.txns[t].committed,
    ensures inv_l2(step_read(s, t, c)),
{
    lemma_step_read_preserves_pred_closed(s, t, c);

    let s2 = step_read(s, t, c);
    let writer = s.cell_writer[c];

    assert forall |u: TxnId, p: TxnId| #![trigger s2.txns[u].predecessors.contains(p)]
        s2.txns.contains_key(u) && s2.txns[u].predecessors.contains(p)
        implies s2.txns.contains_key(p) && s2.txns[p].committed
    by {
        if u == t {
            if s.txns[t].predecessors.contains(p) {
            } else if p == writer {
            } else {
                assert(s.txns[writer].predecessors.contains(p));
            }
        }
    }

    assert(inv_cell_writer_wrote(s2)) by {
        assert forall |cc: CellId| #![trigger s2.cell_writer[cc]]
            s2.cell_value.contains_key(cc) implies
                s2.txns.contains_key(s2.cell_writer[cc])
                && s2.txns[s2.cell_writer[cc]].write_set.contains(cc)
                && s2.txns[s2.cell_writer[cc]].write_values[cc] == s2.cell_value[cc]
        by {
            assert(s2.cell_value[cc] == s.cell_value[cc]);
            assert(s2.cell_writer[cc] == s.cell_writer[cc]);
            let w = s.cell_writer[cc];
            assert(s.txns.contains_key(w));
            assert(s.txns[w].write_set.contains(cc));
            assert(s.txns[w].write_values[cc] == s.cell_value[cc]);
            if w == t {
                assert(s2.txns[t].write_set == s.txns[t].write_set);
                assert(s2.txns[t].write_values == s.txns[t].write_values);
            } else {
                assert(s2.txns[w] == s.txns[w]);
            }
        }
    }

    assert(inv_read_provenance(s2)) by {
        let writer = s.cell_writer[c];
        assert(s2.txns[t].predecessors =~=
               s.txns[t].predecessors.insert(writer).union(s.txns[writer].predecessors));
        assert forall |tt: TxnId, cc: CellId| #![trigger s2.txns[tt].read_set.contains(cc)]
            (s2.txns.contains_key(tt) && s2.txns[tt].read_set.contains(cc)) implies
                s2.txns[tt].read_from.contains_key(cc)
                && s2.txns[tt].predecessors.contains(s2.txns[tt].read_from[cc])
                && s2.txns.contains_key(s2.txns[tt].read_from[cc])
                && s2.txns[s2.txns[tt].read_from[cc]].write_set.contains(cc)
                && s2.txns[s2.txns[tt].read_from[cc]].write_values[cc] == s2.txns[tt].read_values[cc]
        by {
            if tt == t {
                if cc == c {
                    assert(s2.txns[t].read_from[c] == writer);
                    assert(s2.txns[t].read_from.contains_key(c));
                    assert(s2.txns[t].predecessors.contains(writer));
                    assert(s2.txns[t].read_values[c] == s.cell_value[c]);
                    assert(s.cell_value.contains_key(c));
                    assert(s.txns.contains_key(writer) && s.txns[writer].committed);
                    assert(writer != t);
                    assert(s2.txns[writer] == s.txns[writer]);
                    assert(s.txns[writer].write_set.contains(c));
                    assert(s.txns[writer].write_values[c] == s.cell_value[c]);
                } else {
                    assert(s.txns[t].read_set.contains(cc));
                    let w = s.txns[t].read_from[cc];
                    assert(s.txns[t].read_from.contains_key(cc));
                    assert(s.txns[t].predecessors.contains(w));
                    assert(s.txns.contains_key(w));
                    assert(s.txns[w].write_set.contains(cc));
                    assert(s.txns[w].write_values[cc] == s.txns[t].read_values[cc]);
                    assert(s2.txns[t].read_from[cc] == w);
                    assert(s2.txns[t].read_from.contains_key(cc));
                    assert(s2.txns[t].predecessors.contains(w));
                    assert(s2.txns[t].read_values[cc] == s.txns[t].read_values[cc]);
                    assert(s.txns[w].committed);
                    assert(w != t);
                    assert(s2.txns[w] == s.txns[w]);
                }
            } else {
                assert(s2.txns[tt] == s.txns[tt]);
                let w = s.txns[tt].read_from[cc];
                assert(s.txns[tt].read_set.contains(cc));
                assert(s.txns[tt].predecessors.contains(w));
                assert(s.txns.contains_key(w));
                assert(s.txns[w].write_set.contains(cc));
                assert(s.txns[w].write_values[cc] == s.txns[tt].read_values[cc]);
                assert(s.txns[w].committed);
                assert(w != t);
                assert(s2.txns[w] == s.txns[w]);
            }
        }
    }
}

pub proof fn lemma_commit_preserves_inv_l2(s: RuntimeState, t: TxnId)
    requires inv_l2(s), commit_valid(s, t),
    ensures inv_l2(step_commit(s, t)),
{
    let s2 = step_commit(s, t);
    let ws = s.txns[t].write_set;

    assert forall |x: TxnId| #![trigger s2.txns[x]]
        s2.txns.contains_key(x) implies
            s.txns.contains_key(x)
            && s2.txns[x].predecessors == s.txns[x].predecessors
            && (s2.txns[x].aborted == s.txns[x].aborted)
    by { }

    assert(inv_cell_domains(s2)) by {
        assert forall |c: CellId| #![trigger s2.cell_value.contains_key(c)]
            s2.cell_value.contains_key(c) <==> s2.cell_writer.contains_key(c)
        by { }
    }

    assert forall |c: CellId| #![trigger s2.cell_writer[c]]
        s2.cell_value.contains_key(c)
        implies s2.txns.contains_key(s2.cell_writer[c])
            && s2.txns[s2.cell_writer[c]].committed
    by {
        if ws.contains(c) {
            assert(s2.cell_writer[c] == t);
            assert(s2.txns[t].committed);
        } else {
            assert(s2.cell_value.contains_key(c));
            assert(s.cell_value.contains_key(c));
            assert(s.cell_writer.contains_key(c));
            assert(s2.cell_writer[c] == s.cell_writer[c]);
        }
    }

    assert(invariant_committed_predecessors_clean(s2)) by {
        assert forall |u: TxnId| #![trigger s2.txns[u].committed]
            s2.txns.contains_key(u) && s2.txns[u].committed && !s2.txns[u].aborted
            implies predecessors_clean(s2, u)
        by {
            assert(s2.txns[u].predecessors == s.txns[u].predecessors);

            if u != t {
                assert(s.txns[u].committed);
            }
            assert forall |p: TxnId| s.txns[u].predecessors.contains(p)
                implies s2.txns.contains_key(p)
                    && s2.txns[p].committed && !s2.txns[p].aborted
            by {
                assert(s.txns.contains_key(p) && s.txns[p].committed && !s.txns[p].aborted);
                assert(p != t);
                assert(s2.txns[p] == s.txns[p]);
            }
        }
    }

    assert(pred_closed(s2)) by {
        assert forall |u: TxnId, p: TxnId, q: TxnId|
            #![trigger s2.txns[u].predecessors.contains(p), s2.txns[p].predecessors.contains(q)]
            s2.txns.contains_key(u) && s2.txns[u].predecessors.contains(p)
            && s2.txns[p].predecessors.contains(q)
            implies s2.txns[u].predecessors.contains(q)
        by {
            assert(s2.txns[u].predecessors == s.txns[u].predecessors);
            assert(s2.txns[p].predecessors == s.txns[p].predecessors);
        }
    }
    assert(inv_committed_frozen(s2)) by {
        assert forall |u: TxnId, p: TxnId| #![trigger s2.txns[u].predecessors.contains(p)]
            s2.txns.contains_key(u) && s2.txns[u].predecessors.contains(p)
            implies s2.txns.contains_key(p) && s2.txns[p].committed
        by {
            assert(s2.txns[u].predecessors == s.txns[u].predecessors);
        }
    }

    assert(inv_cell_writer_wrote(s2)) by {
        assert forall |c: CellId| #![trigger s2.cell_writer[c]]
            s2.cell_value.contains_key(c) implies
                s2.txns.contains_key(s2.cell_writer[c])
                && s2.txns[s2.cell_writer[c]].write_set.contains(c)
                && s2.txns[s2.cell_writer[c]].write_values[c] == s2.cell_value[c]
        by {
            if ws.contains(c) {
                assert(s2.cell_writer[c] == t);
                assert(s2.cell_value[c] == s.txns[t].write_values[c]);
                assert(s2.txns[t].write_set == s.txns[t].write_set);
                assert(s2.txns[t].write_set.contains(c));
                assert(s2.txns[t].write_values == s.txns[t].write_values);
            } else {
                assert(s.cell_value.contains_key(c));
                assert(s.cell_writer.contains_key(c));
                assert(s2.cell_writer[c] == s.cell_writer[c]);
                assert(s2.cell_value[c] == s.cell_value[c]);
                let w = s.cell_writer[c];
                assert(s.txns.contains_key(w) && s.txns[w].committed);
                assert(s.txns[w].write_set.contains(c));
                assert(s.txns[w].write_values[c] == s.cell_value[c]);
                assert(w != t);
                assert(s2.txns[w] == s.txns[w]);
            }
        }
    }

    assert(inv_read_provenance(s2)) by {
        assert forall |tt: TxnId, cc: CellId| #![trigger s2.txns[tt].read_set.contains(cc)]
            (s2.txns.contains_key(tt) && s2.txns[tt].read_set.contains(cc)) implies
                s2.txns[tt].read_from.contains_key(cc)
                && s2.txns[tt].predecessors.contains(s2.txns[tt].read_from[cc])
                && s2.txns.contains_key(s2.txns[tt].read_from[cc])
                && s2.txns[s2.txns[tt].read_from[cc]].write_set.contains(cc)
                && s2.txns[s2.txns[tt].read_from[cc]].write_values[cc] == s2.txns[tt].read_values[cc]
        by {
            if tt == t {
                assert(s2.txns[t].read_set == s.txns[t].read_set);
                assert(s2.txns[t].read_values == s.txns[t].read_values);
                assert(s2.txns[t].read_from == s.txns[t].read_from);
                assert(s2.txns[t].predecessors == s.txns[t].predecessors);
            } else {
                assert(s2.txns[tt] == s.txns[tt]);
            }

            let w = s.txns[tt].read_from[cc];

            assert(s.txns[tt].read_set.contains(cc));
            assert(s.txns[tt].predecessors.contains(w));
            assert(s.txns.contains_key(w));
            assert(s.txns[w].write_set.contains(cc));
            assert(s.txns[w].write_values[cc] == s.txns[tt].read_values[cc]);
            assert(s.txns[w].committed);
            assert(w != t);
            assert(s2.txns[w] == s.txns[w]);
        }
    }
}

pub proof fn lemma_initial_inv_l2()
    ensures inv_l2(initial_state())
{
    assert(initial_state().txns =~= Map::<TxnId, TxnState>::empty());
    assert(initial_state().cell_value =~= Map::<CellId, Value>::empty());
    assert(initial_state().cell_writer =~= Map::<CellId, TxnId>::empty());
}

pub proof fn lemma_l2_reachable_no_a3(s: RuntimeState)
    requires inv_l2(s),
    ensures forall |t: TxnId| #![trigger s.txns[t].committed] !a3_witness(s, t),
{
    assert forall |t: TxnId| #![trigger s.txns[t].committed]
        !a3_witness(s, t)
    by {
        if a3_witness(s, t) {
            let p = choose |p: TxnId|
                s.txns[t].predecessors.contains(p)
                && s.txns.contains_key(p) && s.txns[p].aborted;
            assert(s.txns[t].predecessors.contains(p));   // witness of the exists
            assert(invariant_committed_predecessors_clean(s));  // conjunct of inv_l2
            assert(predecessors_clean(s, t));             // t is committed-clean
            assert(s.txns[p].committed && !s.txns[p].aborted);  // contradicts p.aborted
            assert(false);
        }
    }
}

pub proof fn lemma_l2_reads_supported(s: RuntimeState)
    requires inv_l2(s),
    ensures
        forall |t: TxnId, c: CellId|
            (s.txns.contains_key(t) && s.txns[t].committed && !s.txns[t].aborted
             && s.txns[t].read_set.contains(c))
            ==> exists |w: TxnId|
                s.txns.contains_key(w) && s.txns[w].committed && !s.txns[w].aborted
                && s.txns[w].write_set.contains(c)
                && s.txns[w].write_values[c] == s.txns[t].read_values[c],
{
    assert forall |t: TxnId, c: CellId|
        (s.txns.contains_key(t) && s.txns[t].committed && !s.txns[t].aborted
         && s.txns[t].read_set.contains(c)) implies
        exists |w: TxnId|
            s.txns.contains_key(w) && s.txns[w].committed && !s.txns[w].aborted
            && s.txns[w].write_set.contains(c)
            && s.txns[w].write_values[c] == s.txns[t].read_values[c]
    by {
        let w = s.txns[t].read_from[c];

        assert(s.txns[t].read_set.contains(c));
        assert(s.txns[t].predecessors.contains(w));
        assert(s.txns.contains_key(w));
        assert(s.txns[w].write_set.contains(c));
        assert(s.txns[w].write_values[c] == s.txns[t].read_values[c]);
        assert(invariant_committed_predecessors_clean(s));
        assert(predecessors_clean(s, t));
        assert(s.txns[w].committed && !s.txns[w].aborted);
        assert(s.txns.contains_key(w) && s.txns[w].committed && !s.txns[w].aborted
            && s.txns[w].write_set.contains(c)
            && s.txns[w].write_values[c] == s.txns[t].read_values[c]);
    }
}

pub proof fn lemma_begin_preserves_inv_l2t(s: RuntimeState, t: TxnId)
    requires inv_l2t(s), !s.txns.contains_key(t),
    ensures inv_l2t(step_begin(s, t)),
{
    lemma_begin_preserves_inv_l2(s, t);
    let s2 = step_begin(s, t);
    assert(inv_commit_time_le_now(s2)) by {
        assert forall |x: TxnId| #![trigger s2.txns[x].commit_time]
            (s2.txns.contains_key(x) && s2.txns[x].committed)
            implies s2.txns[x].commit_time <= s2.now
        by {
            if x == t {
                assert(!s2.txns[t].committed);
            } else {
                assert(s2.txns[x] == s.txns[x]);
                assert(s.txns[x].commit_time <= s.now);
            }
        }
    }

    assert(inv_read_temporal(s2)) by {
        assert forall |tt: TxnId, cc: CellId| #![trigger s2.txns[tt].read_set.contains(cc)]
            (s2.txns.contains_key(tt) && s2.txns[tt].read_set.contains(cc))
            implies s2.txns.contains_key(s2.txns[tt].read_from[cc])
                && s2.txns[s2.txns[tt].read_from[cc]].commit_time <= s2.txns[tt].read_at[cc]
        by {
            if tt == t {
                assert(s2.txns[t].read_set =~= Set::<CellId>::empty());
            } else {
                assert(s2.txns[tt] == s.txns[tt]);
                assert(s.txns[tt].read_set.contains(cc));
                let w = s.txns[tt].read_from[cc];
                assert(s.txns.contains_key(w));
                assert(s.txns[w].commit_time <= s.txns[tt].read_at[cc]);
                assert(w != t);
                assert(s2.txns[w] == s.txns[w]);
                assert(s2.txns[tt].read_from[cc] == w);
                assert(s2.txns[tt].read_at[cc] == s.txns[tt].read_at[cc]);
            }
        }
    }
}

pub proof fn lemma_write_preserves_inv_l2t(s: RuntimeState, t: TxnId, c: CellId, v: Value)
    requires inv_l2t(s), s.txns.contains_key(t), !s.txns[t].committed,
    ensures inv_l2t(step_write(s, t, c, v)),
{
    lemma_write_preserves_inv_l2(s, t, c, v);
    let s2 = step_write(s, t, c, v);
    assert(inv_commit_time_le_now(s2)) by {
        assert forall |x: TxnId| #![trigger s2.txns[x].commit_time]
            (s2.txns.contains_key(x) && s2.txns[x].committed)
            implies s2.txns[x].commit_time <= s2.now
        by {
            if x == t {
                assert(s2.txns[t].committed == s.txns[t].committed);
                assert(!s.txns[t].committed);
            } else {
                assert(s2.txns[x] == s.txns[x]);
                assert(s.txns[x].commit_time <= s.now);
            }
        }
    }

    assert(inv_read_temporal(s2)) by {
        assert forall |tt: TxnId, cc: CellId| #![trigger s2.txns[tt].read_set.contains(cc)]
            (s2.txns.contains_key(tt) && s2.txns[tt].read_set.contains(cc))
            implies s2.txns.contains_key(s2.txns[tt].read_from[cc])
                && s2.txns[s2.txns[tt].read_from[cc]].commit_time <= s2.txns[tt].read_at[cc]
        by {
            if tt == t {
                assert(s2.txns[t].read_set == s.txns[t].read_set);
                assert(s2.txns[t].read_from == s.txns[t].read_from);
                assert(s2.txns[t].read_at == s.txns[t].read_at);
            } else {
                assert(s2.txns[tt] == s.txns[tt]);
            }
            assert(s.txns[tt].read_set.contains(cc));

            let w = s.txns[tt].read_from[cc];
            assert(s.txns.contains_key(w));
            assert(s.txns[w].commit_time <= s.txns[tt].read_at[cc]);

            if w == t {
                assert(s2.txns[t].commit_time == s.txns[t].commit_time);
            } else {
                assert(s2.txns[w] == s.txns[w]);
            }
            assert(s2.txns[tt].read_from[cc] == w);
            assert(s2.txns[tt].read_at[cc] == s.txns[tt].read_at[cc]);
        }
    }
}

pub proof fn lemma_abort_preserves_inv_l2t(s: RuntimeState, t: TxnId)
    requires inv_l2t(s), s.txns.contains_key(t),
    ensures inv_l2t(step_abort(s, t)),
{
    lemma_abort_preserves_inv_l2(s, t);
    let s2 = step_abort(s, t);

    assert forall |x: TxnId| #![trigger s2.txns[x]]
        s2.txns.contains_key(x) implies
            s.txns.contains_key(x)
            && s2.txns[x].committed == s.txns[x].committed
            && s2.txns[x].commit_time == s.txns[x].commit_time
            && s2.txns[x].read_set == s.txns[x].read_set
            && s2.txns[x].read_from == s.txns[x].read_from
            && s2.txns[x].read_at == s.txns[x].read_at
    by {
        let base = s.txns.insert(t, TxnState { aborted: true, ..s.txns[t] });
        assert(base.contains_key(x));
        assert(base[x].committed == s.txns[x].committed);
        assert(base[x].commit_time == s.txns[x].commit_time);
        assert(base[x].read_set == s.txns[x].read_set);
        assert(base[x].read_from == s.txns[x].read_from);
        assert(base[x].read_at == s.txns[x].read_at);
        assert(s2.txns[x].committed == base[x].committed);
        assert(s2.txns[x].commit_time == base[x].commit_time);
        assert(s2.txns[x].read_set == base[x].read_set);
        assert(s2.txns[x].read_from == base[x].read_from);
        assert(s2.txns[x].read_at == base[x].read_at);
    }

    assert(inv_commit_time_le_now(s2)) by {
        assert forall |x: TxnId| #![trigger s2.txns[x].commit_time]
            (s2.txns.contains_key(x) && s2.txns[x].committed)
            implies s2.txns[x].commit_time <= s2.now
        by {
            assert(s2.txns[x].committed == s.txns[x].committed);
            assert(s2.txns[x].commit_time == s.txns[x].commit_time);
            assert(s.txns[x].commit_time <= s.now);
        }
    }

    assert(inv_read_temporal(s2)) by {
        assert forall |tt: TxnId, cc: CellId| #![trigger s2.txns[tt].read_set.contains(cc)]
            (s2.txns.contains_key(tt) && s2.txns[tt].read_set.contains(cc))
            implies s2.txns.contains_key(s2.txns[tt].read_from[cc])
                && s2.txns[s2.txns[tt].read_from[cc]].commit_time <= s2.txns[tt].read_at[cc]
        by {
            assert(s2.txns[tt].read_set == s.txns[tt].read_set);
            assert(s2.txns[tt].read_from == s.txns[tt].read_from);
            assert(s2.txns[tt].read_at == s.txns[tt].read_at);
            assert(s.txns[tt].read_set.contains(cc));
            let w = s.txns[tt].read_from[cc];
            assert(s.txns.contains_key(w));
            assert(s.txns[w].commit_time <= s.txns[tt].read_at[cc]);
            assert(s2.txns.contains_key(w));
            assert(s2.txns[w].commit_time == s.txns[w].commit_time);
        }
    }
}

pub proof fn lemma_read_preserves_inv_l2t(s: RuntimeState, t: TxnId, c: CellId)
    requires
        inv_l2t(s),
        s.txns.contains_key(t),
        s.cell_value.contains_key(c),
        !s.txns[t].committed,
    ensures inv_l2t(step_read(s, t, c)),
{
    lemma_read_preserves_inv_l2(s, t, c);
    let s2 = step_read(s, t, c);
    let writer = s.cell_writer[c];
    assert(inv_commit_time_le_now(s2)) by {
        assert forall |x: TxnId| #![trigger s2.txns[x].commit_time]
            (s2.txns.contains_key(x) && s2.txns[x].committed)
            implies s2.txns[x].commit_time <= s2.now
        by {
            if x == t {
                assert(s2.txns[t].committed == s.txns[t].committed);
                assert(!s.txns[t].committed);
            } else {
                assert(s2.txns[x] == s.txns[x]);
                assert(s.txns[x].commit_time <= s.now);
            }
        }
    }
    
    assert(inv_read_temporal(s2)) by {
        assert forall |tt: TxnId, cc: CellId| #![trigger s2.txns[tt].read_set.contains(cc)]
            (s2.txns.contains_key(tt) && s2.txns[tt].read_set.contains(cc))
            implies s2.txns.contains_key(s2.txns[tt].read_from[cc])
                && s2.txns[s2.txns[tt].read_from[cc]].commit_time <= s2.txns[tt].read_at[cc]
        by {
            if tt == t {
                if cc == c {
                    // freshly recorded read: producer = writer, read_at[c] = s.now
                    assert(s2.txns[t].read_from[c] == writer);           // insert(c, writer)
                    assert(s2.txns[t].read_at[c] == s.now);              // insert(c, s.now)
                    assert(s.txns.contains_key(writer) && s.txns[writer].committed);  // inv_writers_committed
                    assert(s.txns[writer].commit_time <= s.now);         // inv_commit_time_le_now(s)
                    assert(writer != t);                                 // writer committed, t not
                    assert(s2.txns[writer] == s.txns[writer]);
                } else {
                    // old read of t at cc != c: unchanged
                    assert(s.txns[t].read_set.contains(cc));
                    assert(s.txns[t].predecessors.contains(s.txns[t].read_from[cc])); // inv_read_provenance(s)
                    let w = s.txns[t].read_from[cc];
                    assert(s.txns.contains_key(w));
                    assert(s.txns[w].committed);                         // inv_committed_frozen(s)
                    assert(w != t);                                      // w committed, t not
                    assert(s.txns[w].commit_time <= s.txns[t].read_at[cc]); // inv_read_temporal(s)
                    assert(s2.txns[t].read_from[cc] == w);               // insert at c != cc
                    assert(s2.txns[t].read_at[cc] == s.txns[t].read_at[cc]);
                    assert(s2.txns[w] == s.txns[w]);
                }
            } else {
                assert(s2.txns[tt] == s.txns[tt]);
                assert(s.txns[tt].read_set.contains(cc));
                assert(s.txns[tt].predecessors.contains(s.txns[tt].read_from[cc])); // inv_read_provenance(s)
                let w = s.txns[tt].read_from[cc];
                assert(s.txns.contains_key(w));
                assert(s.txns[w].committed);                             // inv_committed_frozen(s)
                assert(w != t);                                          // w committed, t not
                assert(s.txns[w].commit_time <= s.txns[tt].read_at[cc]); // inv_read_temporal(s)
                assert(s2.txns[w] == s.txns[w]);
                assert(s2.txns[tt].read_from[cc] == w);
                assert(s2.txns[tt].read_at[cc] == s.txns[tt].read_at[cc]);
            }
        }
    }
}

/// commit: sets t.committed and t.commit_time = s.now and publishes cells; it
/// changes no read-side field. The only new committed time is t's (= s.now <=
/// s2.now). A producer of any existing read is committed in s
/// (inv_committed_frozen), hence != t, so its commit_time is unchanged.
pub proof fn lemma_commit_preserves_inv_l2t(s: RuntimeState, t: TxnId)
    requires inv_l2t(s), commit_valid(s, t),
    ensures inv_l2t(step_commit(s, t)),
{
    lemma_commit_preserves_inv_l2(s, t);
    let s2 = step_commit(s, t);
    assert(inv_commit_time_le_now(s2)) by {
        assert forall |x: TxnId| #![trigger s2.txns[x].commit_time]
            (s2.txns.contains_key(x) && s2.txns[x].committed)
            implies s2.txns[x].commit_time <= s2.now
        by {
            if x == t {
                assert(s2.txns[t].commit_time == s.now);                 // step_commit sets commit_time = s.now
            } else {
                assert(s2.txns[x] == s.txns[x]);                         // commit changes only t
                assert(s.txns[x].commit_time <= s.now);                  // inv_commit_time_le_now(s)
            }
        }
    }
    assert(inv_read_temporal(s2)) by {
        assert forall |tt: TxnId, cc: CellId| #![trigger s2.txns[tt].read_set.contains(cc)]
            (s2.txns.contains_key(tt) && s2.txns[tt].read_set.contains(cc))
            implies s2.txns.contains_key(s2.txns[tt].read_from[cc])
                && s2.txns[s2.txns[tt].read_from[cc]].commit_time <= s2.txns[tt].read_at[cc]
        by {
            if tt == t {
                assert(s2.txns[t].read_set == s.txns[t].read_set);       // ..txn
                assert(s2.txns[t].read_from == s.txns[t].read_from);
                assert(s2.txns[t].read_at == s.txns[t].read_at);
            } else {
                assert(s2.txns[tt] == s.txns[tt]);
            }
            assert(s.txns[tt].read_set.contains(cc));
            let w = s.txns[tt].read_from[cc];
            assert(s.txns[tt].predecessors.contains(w));                 // inv_read_provenance(s)
            assert(s.txns.contains_key(w));
            assert(s.txns[w].committed);                                 // inv_committed_frozen(s)
            assert(s.txns[w].commit_time <= s.txns[tt].read_at[cc]);     // inv_read_temporal(s)
            assert(w != t);                                              // t not committed in s
            assert(s2.txns[w] == s.txns[w]);                             // commit changes only t
            assert(s2.txns[tt].read_from[cc] == w);
            assert(s2.txns[tt].read_at[cc] == s.txns[tt].read_at[cc]);
        }
    }
}

/// BASE CASE: empty state -- no txns, so both temporal conjuncts are vacuous.
pub proof fn lemma_initial_inv_l2t()
    ensures inv_l2t(initial_state())
{
    lemma_initial_inv_l2();
    assert(initial_state().txns =~= Map::<TxnId, TxnState>::empty());
}

/// THEOREM L_2i+ (full catalogue-A_3 residue: value AND time). On any state
/// satisfying inv_l2t, for every committed, non-aborted txn t and every cell c
/// it read, there EXISTS a committed, non-aborted producer w that wrote c with
/// exactly the observed value AND committed no later than t read it
/// (commit_time(w) <= read_at[t][c]). The value half is L_2i (inv_read_provenance
/// + predecessors_clean); the temporal half (write_time <= read_time) is
/// inv_read_temporal. read_from[c] is the witness.
pub proof fn lemma_l2_reads_supported_temporal(s: RuntimeState)
    requires inv_l2t(s),
    ensures
        forall |t: TxnId, c: CellId|
            (s.txns.contains_key(t) && s.txns[t].committed && !s.txns[t].aborted
             && s.txns[t].read_set.contains(c))
            ==> exists |w: TxnId|
                s.txns.contains_key(w) && s.txns[w].committed && !s.txns[w].aborted
                && s.txns[w].write_set.contains(c)
                && s.txns[w].write_values[c] == s.txns[t].read_values[c]
                && s.txns[w].commit_time <= s.txns[t].read_at[c],
{
    lemma_l2_reads_supported(s);
    assert forall |t: TxnId, c: CellId|
        (s.txns.contains_key(t) && s.txns[t].committed && !s.txns[t].aborted
         && s.txns[t].read_set.contains(c)) implies
        exists |w: TxnId|
            s.txns.contains_key(w) && s.txns[w].committed && !s.txns[w].aborted
            && s.txns[w].write_set.contains(c)
            && s.txns[w].write_values[c] == s.txns[t].read_values[c]
            && s.txns[w].commit_time <= s.txns[t].read_at[c]
    by {
        let w = s.txns[t].read_from[c];
        // value half (inv_read_provenance + predecessors_clean), as in L_2i:
        assert(s.txns[t].predecessors.contains(w));
        assert(s.txns.contains_key(w));
        assert(s.txns[w].write_set.contains(c));
        assert(s.txns[w].write_values[c] == s.txns[t].read_values[c]);
        assert(invariant_committed_predecessors_clean(s));
        assert(predecessors_clean(s, t));
        assert(s.txns[w].committed && !s.txns[w].aborted);
        // temporal half (inv_read_temporal):
        assert(s.txns[w].commit_time <= s.txns[t].read_at[c]);
        assert(s.txns.contains_key(w) && s.txns[w].committed && !s.txns[w].aborted
            && s.txns[w].write_set.contains(c)
            && s.txns[w].write_values[c] == s.txns[t].read_values[c]
            && s.txns[w].commit_time <= s.txns[t].read_at[c]);
    }
}

} // verus!