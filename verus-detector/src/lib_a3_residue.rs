// =====================================================================
// Verus proof: what the flat-trace residue does and does not detect
//
// COMPILE
//   verus --crate-type=lib src/lib_a3_residue.rs
//
// 2026-09-16  round 31 (audit finding G3). The manuscript says
//   "A_3 => Residue on the projected flat history: the residue is a sound
//    detector for the cascade"
// and never defines the projection. The implication is false, and this file
// replaces it with what holds, mechanically:
//   projects(h, s)   the projected flat history, defined: exactly the reads
//                    and writes of committed, unaborted transactions, with
//                    their values and times;
//   R1  lemma_residue_misses_a_cascade_on_repeated_values
//       not sound: a surviving dependent of an aborted writer, and an earlier
//       surviving write of the SAME value, leave no residue;
//   R2  lemma_residue_sound_for_direct_cascades_under_unique_writes
//       sound when no two committed transactions write the same value to a
//       cell, for a dependent that read an aborted writer directly;
//   R3  lemma_residue_sound_for_cascade_chains_under_unique_writes
//       the same along a chain of reads ending at an aborted writer (the
//       causal-closure form), through its first aborted link;
//   R4  lemma_residue_fires_without_a_cascade
//       not complete: a read of a value no logged transaction wrote;
//   R5  lemma_residue_blind_to_relabeled_effects
//       blind to the cataloged A_3 when a cascade flagged the dependent
//       aborted after its effects were out: the projection drops it.
//
// The residue here is the event form of lib_l2_projection.rs's a3_witness
// (one read or write record per event rather than per operation; that the two
// forms agree is by inspection). Values use 0 as NULL, as there.
//
// TRUST BASE: zero axioms, zero external_body, zero assume, zero admit.

#![allow(unused_imports)]
#![allow(dead_code)]
use vstd::prelude::*;

verus! {

pub type TxnId  = int;
pub type CellId = int;
pub type Value  = int;
pub type Time   = int;

pub open spec fn null_value() -> Value { 0 }

pub struct Txn {
    pub committed:    bool,
    pub aborted:      bool,
    pub externalized: bool,
    pub read_set:     Set<CellId>,
    pub read_values:  Map<CellId, Value>,
    pub read_at:      Map<CellId, Time>,
    /// the transaction whose committed write each read observed
    pub read_from:    Map<CellId, TxnId>,
    pub write_set:    Set<CellId>,
    pub write_values: Map<CellId, Value>,
    pub commit_time:  Time,
}

pub struct State {
    pub txns: Map<TxnId, Txn>,
}

pub open spec fn clean(s: State, t: TxnId) -> bool {
    s.txns.contains_key(t) && s.txns[t].committed && !s.txns[t].aborted
}

/// A committed read observed a committed write of the same value, no later.
pub open spec fn read_provenance(s: State) -> bool {
    forall |t: TxnId, c: CellId| #![trigger s.txns[t].read_set.contains(c)]
        s.txns.contains_key(t) && s.txns[t].committed && s.txns[t].read_set.contains(c)
        ==> {
            let p = s.txns[t].read_from[c];
            &&& s.txns.contains_key(p)
            &&& s.txns[p].committed
            &&& s.txns[p].write_set.contains(c)
            &&& s.txns[p].write_values[c] == s.txns[t].read_values[c]
            &&& s.txns[p].commit_time <= s.txns[t].read_at[c]
        }
}

/// No two committed transactions write the same value to the same cell.
pub open spec fn unique_writes(s: State) -> bool {
    forall |a: TxnId, b: TxnId, c: CellId|
        #![trigger s.txns[a].write_values[c], s.txns[b].write_values[c]]
        a != b
        && s.txns.contains_key(a) && s.txns.contains_key(b)
        && s.txns[a].committed && s.txns[b].committed
        && s.txns[a].write_set.contains(c) && s.txns[b].write_set.contains(c)
        ==> s.txns[a].write_values[c] != s.txns[b].write_values[c]
}

/// The cascade through one read: a surviving transaction read a cell whose
/// producer was aborted.
pub open spec fn cascade_direct(s: State, t: TxnId, c: CellId) -> bool {
    &&& clean(s, t)
    &&& s.txns[t].read_set.contains(c)
    &&& s.txns.contains_key(s.txns[t].read_from[c])
    &&& s.txns[s.txns[t].read_from[c]].aborted
}

/// The cataloged A_3 through one read: an externalized transaction read a cell
/// whose producer was aborted (aborted itself or not).
pub open spec fn a3_externalized_direct(s: State, t: TxnId, c: CellId) -> bool {
    &&& s.txns.contains_key(t)
    &&& s.txns[t].externalized
    &&& s.txns[t].read_set.contains(c)
    &&& s.txns.contains_key(s.txns[t].read_from[c])
    &&& s.txns[s.txns[t].read_from[c]].aborted
}

// ---------------------------------------------------------------------
// Flat histories, the residue, and the projection
// ---------------------------------------------------------------------

pub struct Event {
    pub op:      TxnId,
    pub is_read: bool,
    pub cell:    CellId,
    pub value:   Value,
    pub time:    Time,
}

/// A read of a non-NULL value that no other operation's write produced at or
/// before the read.
pub open spec fn residue_at(h: Seq<Event>, i: int) -> bool {
    &&& 0 <= i < h.len()
    &&& h[i].is_read
    &&& h[i].value != null_value()
    &&& forall |k: int| #![trigger h[k]]
            0 <= k < h.len() && !h[k].is_read && h[k].op != h[i].op
            && h[k].cell == h[i].cell && h[k].time <= h[i].time
            ==> h[k].value != h[i].value
}

pub open spec fn residue(h: Seq<Event>) -> bool {
    exists |i: int| #![trigger residue_at(h, i)] residue_at(h, i)
}

/// `h` is the projected flat history of `s`: its events are exactly the reads
/// and writes of committed, unaborted transactions.
pub open spec fn projects(h: Seq<Event>, s: State) -> bool {
    &&& forall |i: int| #![trigger h[i]]
            0 <= i < h.len() ==> {
                let t = h[i].op;
                clean(s, t) && (if h[i].is_read {
                    &&& s.txns[t].read_set.contains(h[i].cell)
                    &&& h[i].value == s.txns[t].read_values[h[i].cell]
                    &&& h[i].time == s.txns[t].read_at[h[i].cell]
                } else {
                    &&& s.txns[t].write_set.contains(h[i].cell)
                    &&& h[i].value == s.txns[t].write_values[h[i].cell]
                    &&& h[i].time == s.txns[t].commit_time
                })
            }
    &&& forall |t: TxnId, c: CellId| #![trigger s.txns[t].read_set.contains(c)]
            clean(s, t) && s.txns[t].read_set.contains(c)
            ==> exists |i: int| #![trigger h[i]]
                    0 <= i < h.len() && h[i].op == t && h[i].is_read && h[i].cell == c
    &&& forall |t: TxnId, c: CellId| #![trigger s.txns[t].write_set.contains(c)]
            clean(s, t) && s.txns[t].write_set.contains(c)
            ==> exists |i: int| #![trigger h[i]]
                    0 <= i < h.len() && h[i].op == t && !h[i].is_read && h[i].cell == c
}

// ---------------------------------------------------------------------
// R2, R3: soundness under unique writes
// ---------------------------------------------------------------------

pub proof fn lemma_residue_sound_for_direct_cascades_under_unique_writes(
    h: Seq<Event>, s: State, t: TxnId, c: CellId)
    requires
        projects(h, s),
        read_provenance(s),
        unique_writes(s),
        cascade_direct(s, t, c),
        s.txns[t].read_values[c] != null_value(),
    ensures
        residue(h),
{
    assert(clean(s, t) && s.txns[t].read_set.contains(c));
    let i = choose |i: int| 0 <= i < h.len() && h[i].op == t && h[i].is_read && h[i].cell == c;
    assert(0 <= i < h.len() && h[i].op == t && h[i].is_read && h[i].cell == c);
    assert(h[i].value == s.txns[t].read_values[c]);
    assert(h[i].time == s.txns[t].read_at[c]);
    let p = s.txns[t].read_from[c];
    assert(s.txns.contains_key(p) && s.txns[p].aborted);
    assert(s.txns[p].committed && s.txns[p].write_set.contains(c));
    assert(s.txns[p].write_values[c] == s.txns[t].read_values[c]);
    assert forall |k: int| #![trigger h[k]]
        0 <= k < h.len() && !h[k].is_read && h[k].op != h[i].op
        && h[k].cell == h[i].cell && h[k].time <= h[i].time
        implies h[k].value != h[i].value
    by {
        let w = h[k].op;
        assert(clean(s, w));
        assert(s.txns[w].write_set.contains(c));
        assert(h[k].value == s.txns[w].write_values[c]);
        assert(w != p);
        assert(s.txns[w].write_values[c] != s.txns[p].write_values[c]);
    }
    assert(residue_at(h, i));
}

/// A chain of reads: path[i] read cells[i] from path[i + 1].
pub open spec fn read_path(s: State, path: Seq<TxnId>, cells: Seq<CellId>) -> bool {
    &&& path.len() >= 2
    &&& cells.len() == path.len() - 1
    &&& forall |i: int| #![trigger path[i]]
            0 <= i < path.len() - 1 ==> {
                &&& s.txns.contains_key(path[i])
                &&& s.txns[path[i]].committed
                &&& s.txns[path[i]].read_set.contains(cells[i])
                &&& s.txns[path[i]].read_from[cells[i]] == path[i + 1]
            }
}

/// Walking the chain from a surviving link, the first aborted producer is
/// read directly by a surviving transaction.
pub proof fn lemma_chain_has_a_direct_cascade_from(s: State, path: Seq<TxnId>, cells: Seq<CellId>, k: int)
    requires
        read_path(s, path, cells),
        0 <= k < path.len() - 1,
        clean(s, path[k]),
        s.txns.contains_key(path[path.len() - 1]),
        s.txns[path[path.len() - 1]].aborted,
    ensures
        exists |i: int| #![trigger cascade_direct(s, path[i], cells[i])]
            0 <= i < path.len() - 1 && cascade_direct(s, path[i], cells[i]),
    decreases path.len() - 1 - k,
{
    let q = path[k + 1];
    assert(s.txns[path[k]].read_set.contains(cells[k]));
    assert(s.txns[path[k]].read_from[cells[k]] == q);
    if s.txns.contains_key(q) && s.txns[q].aborted {
        assert(cascade_direct(s, path[k], cells[k]));
    } else {
        assert(k + 1 < path.len() - 1) by {
            if k + 1 == path.len() - 1 {
                assert(q == path[path.len() - 1]);
            }
        }
        assert(s.txns.contains_key(q) && s.txns[q].committed);
        assert(clean(s, q));
        lemma_chain_has_a_direct_cascade_from(s, path, cells, k + 1);
    }
}

pub proof fn lemma_residue_sound_for_cascade_chains_under_unique_writes(
    h: Seq<Event>, s: State, path: Seq<TxnId>, cells: Seq<CellId>)
    requires
        projects(h, s),
        read_provenance(s),
        unique_writes(s),
        read_path(s, path, cells),
        clean(s, path[0]),
        s.txns.contains_key(path[path.len() - 1]),
        s.txns[path[path.len() - 1]].aborted,
        forall |i: int| #![trigger cells[i]]
            0 <= i < cells.len() ==> s.txns[path[i]].read_values[cells[i]] != null_value(),
    ensures
        residue(h),
{
    lemma_chain_has_a_direct_cascade_from(s, path, cells, 0);
    let i = choose |i: int| 0 <= i < path.len() - 1 && cascade_direct(s, path[i], cells[i]);
    assert(0 <= i < cells.len());
    assert(s.txns[path[i]].read_values[cells[i]] != null_value());
    lemma_residue_sound_for_direct_cascades_under_unique_writes(h, s, path[i], cells[i]);
}

// ---------------------------------------------------------------------
// R1: not sound without unique writes
// ---------------------------------------------------------------------

pub open spec fn repeated_value_state() -> State {
    State {
        txns: Map::<TxnId, Txn>::empty()
            .insert(1, Txn {                       // surviving writer of 7 := 5
                committed: true, aborted: false, externalized: true,
                read_set: Set::empty(), read_values: Map::empty(), read_at: Map::empty(),
                read_from: Map::empty(),
                write_set: Set::empty().insert(7), write_values: Map::empty().insert(7, 5),
                commit_time: 1,
            })
            .insert(2, Txn {                       // aborted writer of the same 7 := 5
                committed: true, aborted: true, externalized: true,
                read_set: Set::empty(), read_values: Map::empty(), read_at: Map::empty(),
                read_from: Map::empty(),
                write_set: Set::empty().insert(7), write_values: Map::empty().insert(7, 5),
                commit_time: 2,
            })
            .insert(3, Txn {                       // surviving reader of 2's write
                committed: true, aborted: false, externalized: true,
                read_set: Set::empty().insert(7), read_values: Map::empty().insert(7, 5),
                read_at: Map::empty().insert(7, 3), read_from: Map::empty().insert(7, 2),
                write_set: Set::empty(), write_values: Map::empty(),
                commit_time: 4,
            }),
    }
}

pub open spec fn repeated_value_history() -> Seq<Event> {
    seq![
        Event { op: 1, is_read: false, cell: 7, value: 5, time: 1 },
        Event { op: 3, is_read: true,  cell: 7, value: 5, time: 3 },
    ]
}

pub proof fn lemma_residue_misses_a_cascade_on_repeated_values()
    ensures
        projects(repeated_value_history(), repeated_value_state()),
        read_provenance(repeated_value_state()),
        cascade_direct(repeated_value_state(), 3, 7),
        a3_externalized_direct(repeated_value_state(), 3, 7),
        repeated_value_state().txns[3].read_values[7] != null_value(),
        !residue(repeated_value_history()),
{
    let s = repeated_value_state();
    let h = repeated_value_history();
    assert(h.len() == 2);
    assert(s.txns.contains_key(1) && s.txns.contains_key(2) && s.txns.contains_key(3));
    let t1 = s.txns[1];
    let t2 = s.txns[2];
    let t3 = s.txns[3];
    assert(t1.committed && !t1.aborted && t1.write_set.contains(7) && t1.write_values[7] == 5 && t1.commit_time == 1);
    assert(t1.read_set =~= Set::<CellId>::empty());
    assert(t2.committed && t2.aborted && t2.write_set.contains(7) && t2.write_values[7] == 5 && t2.commit_time == 2);
    assert(t2.read_set =~= Set::<CellId>::empty());
    assert(t3.committed && !t3.aborted && t3.externalized);
    assert(t3.read_set.contains(7) && t3.read_values[7] == 5 && t3.read_at[7] == 3 && t3.read_from[7] == 2);
    assert(t3.write_set =~= Set::<CellId>::empty());
    assert(h[0] == Event { op: 1, is_read: false, cell: 7, value: 5, time: 1 });
    assert(h[1] == Event { op: 3, is_read: true, cell: 7, value: 5, time: 3 });

    assert forall |i: int| #![trigger h[i]]
        0 <= i < h.len() implies {
            let t = h[i].op;
            clean(s, t) && (if h[i].is_read {
                &&& s.txns[t].read_set.contains(h[i].cell)
                &&& h[i].value == s.txns[t].read_values[h[i].cell]
                &&& h[i].time == s.txns[t].read_at[h[i].cell]
            } else {
                &&& s.txns[t].write_set.contains(h[i].cell)
                &&& h[i].value == s.txns[t].write_values[h[i].cell]
                &&& h[i].time == s.txns[t].commit_time
            })
        }
    by {
        if i == 0 { assert(h[i].op == 1); } else { assert(i == 1); assert(h[i].op == 3); }
    }
    assert forall |t: TxnId, c: CellId| #![trigger s.txns[t].read_set.contains(c)]
        clean(s, t) && s.txns[t].read_set.contains(c)
        implies exists |i: int| #![trigger h[i]]
            0 <= i < h.len() && h[i].op == t && h[i].is_read && h[i].cell == c
    by {
        assert(t == 1 || t == 2 || t == 3);
        if t == 3 {
            assert(c == 7);
            assert(h[1].op == t && h[1].is_read && h[1].cell == c);
        }
    }
    assert forall |t: TxnId, c: CellId| #![trigger s.txns[t].write_set.contains(c)]
        clean(s, t) && s.txns[t].write_set.contains(c)
        implies exists |i: int| #![trigger h[i]]
            0 <= i < h.len() && h[i].op == t && !h[i].is_read && h[i].cell == c
    by {
        assert(t == 1 || t == 2 || t == 3);
        if t == 1 {
            assert(c == 7);
            assert(h[0].op == t && !h[0].is_read && h[0].cell == c);
        }
    }
    assert(projects(h, s));

    assert forall |t: TxnId, c: CellId| #![trigger s.txns[t].read_set.contains(c)]
        s.txns.contains_key(t) && s.txns[t].committed && s.txns[t].read_set.contains(c)
        implies {
            let p = s.txns[t].read_from[c];
            &&& s.txns.contains_key(p)
            &&& s.txns[p].committed
            &&& s.txns[p].write_set.contains(c)
            &&& s.txns[p].write_values[c] == s.txns[t].read_values[c]
            &&& s.txns[p].commit_time <= s.txns[t].read_at[c]
        }
    by {
        assert(t == 1 || t == 2 || t == 3);
        if t == 3 {
            assert(c == 7);
        }
    }
    assert(read_provenance(s));

    assert(!residue_at(h, 1)) by {
        assert(0 <= 0 < h.len() && !h[0].is_read && h[0].op != h[1].op
            && h[0].cell == h[1].cell && h[0].time <= h[1].time && h[0].value == h[1].value);
    }
    assert forall |i: int| #![trigger residue_at(h, i)] !residue_at(h, i) by {
        if 0 <= i < h.len() {
            if i == 0 {
                assert(!h[0].is_read);
            } else {
                assert(i == 1);
            }
        }
    }
}

// ---------------------------------------------------------------------
// R4: not complete
// ---------------------------------------------------------------------

pub open spec fn unlogged_read_state() -> State {
    State {
        txns: Map::<TxnId, Txn>::empty()
            .insert(1, Txn {                       // reads 7 = 5, produced by no logged transaction
                committed: true, aborted: false, externalized: true,
                read_set: Set::empty().insert(7), read_values: Map::empty().insert(7, 5),
                read_at: Map::empty().insert(7, 1), read_from: Map::empty().insert(7, 99),
                write_set: Set::empty(), write_values: Map::empty(),
                commit_time: 2,
            }),
    }
}

pub open spec fn unlogged_read_history() -> Seq<Event> {
    seq![Event { op: 1, is_read: true, cell: 7, value: 5, time: 1 }]
}

pub proof fn lemma_residue_fires_without_a_cascade()
    ensures
        projects(unlogged_read_history(), unlogged_read_state()),
        forall |t: TxnId, c: CellId| #![trigger cascade_direct(unlogged_read_state(), t, c)]
            !cascade_direct(unlogged_read_state(), t, c),
        residue(unlogged_read_history()),
{
    let s = unlogged_read_state();
    let h = unlogged_read_history();
    assert(h.len() == 1);
    assert(h[0] == Event { op: 1, is_read: true, cell: 7, value: 5, time: 1 });
    assert(s.txns.contains_key(1) && !s.txns.contains_key(99));
    let t1 = s.txns[1];
    assert(t1.committed && !t1.aborted);
    assert(t1.read_set.contains(7) && t1.read_values[7] == 5 && t1.read_at[7] == 1 && t1.read_from[7] == 99);
    assert(t1.write_set =~= Set::<CellId>::empty());

    assert forall |i: int| #![trigger h[i]]
        0 <= i < h.len() implies {
            let t = h[i].op;
            clean(s, t) && (if h[i].is_read {
                &&& s.txns[t].read_set.contains(h[i].cell)
                &&& h[i].value == s.txns[t].read_values[h[i].cell]
                &&& h[i].time == s.txns[t].read_at[h[i].cell]
            } else {
                &&& s.txns[t].write_set.contains(h[i].cell)
                &&& h[i].value == s.txns[t].write_values[h[i].cell]
                &&& h[i].time == s.txns[t].commit_time
            })
        }
    by {
        assert(i == 0);
    }
    assert forall |t: TxnId, c: CellId| #![trigger s.txns[t].read_set.contains(c)]
        clean(s, t) && s.txns[t].read_set.contains(c)
        implies exists |i: int| #![trigger h[i]]
            0 <= i < h.len() && h[i].op == t && h[i].is_read && h[i].cell == c
    by {
        assert(t == 1);
        assert(c == 7);
        assert(h[0].op == t && h[0].is_read && h[0].cell == c);
    }
    assert forall |t: TxnId, c: CellId| #![trigger s.txns[t].write_set.contains(c)]
        clean(s, t) && s.txns[t].write_set.contains(c)
        implies exists |i: int| #![trigger h[i]]
            0 <= i < h.len() && h[i].op == t && !h[i].is_read && h[i].cell == c
    by {
        assert(t == 1);
    }
    assert(projects(h, s));

    assert forall |t: TxnId, c: CellId| #![trigger cascade_direct(s, t, c)]
        !cascade_direct(s, t, c)
    by {
        if clean(s, t) && s.txns[t].read_set.contains(c) {
            assert(t == 1);
            assert(c == 7);
        }
    }
    assert(residue_at(h, 0));
}

// ---------------------------------------------------------------------
// R5: blind to an effect a cascade relabeled
// ---------------------------------------------------------------------

pub open spec fn relabeled_state() -> State {
    State {
        txns: Map::<TxnId, Txn>::empty()
            .insert(1, Txn {                       // wrote 7 := 5, released its effects, retracted
                committed: true, aborted: true, externalized: true,
                read_set: Set::empty(), read_values: Map::empty(), read_at: Map::empty(),
                read_from: Map::empty(),
                write_set: Set::empty().insert(7), write_values: Map::empty().insert(7, 5),
                commit_time: 1,
            })
            .insert(2, Txn {                       // read it, released, then flagged by the cascade
                committed: true, aborted: true, externalized: true,
                read_set: Set::empty().insert(7), read_values: Map::empty().insert(7, 5),
                read_at: Map::empty().insert(7, 2), read_from: Map::empty().insert(7, 1),
                write_set: Set::empty(), write_values: Map::empty(),
                commit_time: 3,
            }),
    }
}

pub proof fn lemma_residue_blind_to_relabeled_effects()
    ensures
        projects(Seq::<Event>::empty(), relabeled_state()),
        a3_externalized_direct(relabeled_state(), 2, 7),
        !residue(Seq::<Event>::empty()),
{
    let s = relabeled_state();
    let h = Seq::<Event>::empty();
    assert(s.txns.contains_key(1) && s.txns.contains_key(2));
    assert(s.txns[1].aborted && s.txns[2].aborted && s.txns[2].externalized);
    assert(s.txns[2].read_set.contains(7) && s.txns[2].read_from[7] == 1);
    assert forall |t: TxnId, c: CellId| #![trigger s.txns[t].read_set.contains(c)]
        clean(s, t) && s.txns[t].read_set.contains(c)
        implies exists |i: int| #![trigger h[i]]
            0 <= i < h.len() && h[i].op == t && h[i].is_read && h[i].cell == c
    by {
        assert(t == 1 || t == 2);
    }
    assert forall |t: TxnId, c: CellId| #![trigger s.txns[t].write_set.contains(c)]
        clean(s, t) && s.txns[t].write_set.contains(c)
        implies exists |i: int| #![trigger h[i]]
            0 <= i < h.len() && h[i].op == t && !h[i].is_read && h[i].cell == c
    by {
        assert(t == 1 || t == 2);
    }
    assert(projects(h, s));
    assert forall |i: int| #![trigger residue_at(h, i)] !residue_at(h, i) by {}
}

} // verus!
