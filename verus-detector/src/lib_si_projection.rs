// lib_si_projection.rs
//
// =====================================================================
// THE L1 PROJECTION THEOREM.  What the verified SI store guarantees about
// its OWN trace, transported to the trace the detector actually scores.
//
// WHY THIS FILE EXISTS
//   lib_si_concurrent.rs::trace_is_a1_free states, at a read handle, that
//   the store's invariant entails !a1_struct(store.trace).  That trace is
//   SiStore::trace: a Vec<Rec> carrying agent, read cells, read time,
//   write cells and write time -- and no values.  It is not the
//   Seq<OpRecord> the verified detector scores in the empirical sections,
//   and the two genuinely diverge: tick() appends a record with no read
//   cells, so a default-SI no-write bypass leaves the store's own trace
//   clean while the caller's emitted record can still fire.  That is the
//   silent residual measured in the real-LLM baseline.
//
//   L2 closes the corresponding gap with Theorem L2j.  L1 did not.  This
//   file closes it: under a faithful emission, the store's structural
//   guarantee becomes a Definition-1 guarantee on the emitted history.
//
// HOW THE EMISSION HYPOTHESIS DIFFERS FROM L2j's, AND WHY THAT MATTERS
//   Theorem L2j's emit relation quantifies over committed-clean
//   transactions, so it requires the emitter to have already dropped every
//   aborted record -- it presupposes the abort filtering the detector is
//   there to check.  emit_faithful below is index-preserving and total:
//   one OpRecord per store record, in order, filtering nothing.  That is
//   what SiStore does, since it pushes exactly one Rec per commit.  The
//   cell conjuncts are containments rather than equalities, so an emitter
//   that publishes FEWER cells than the record holds is still faithful;
//   that weakens the hypothesis and strengthens the theorem.
//
// WHAT REMAINS TRUSTED, STATED NOT HIDDEN
//   (a) Carriers.  This file uses int cells and times and Seq fields; the
//       deployed Rec uses usize, u64 and Vec.  usize embeds injectively
//       into int and Vec@ is Seq, so the correspondence is by inspection
//       -- the same trusted link Theorem L2j discloses for its int-vs-u32
//       carriers, and no wider.
//   (b) The emitter.  No emitter in this artifact is PROVED to satisfy
//       emit_faithful, and the Python instrumentation of the pilot
//       certainly is not verified.  The theorem states what a faithful
//       emission yields; it does not establish that any given emitter is
//       faithful.  Mechanizing one serializer against emit_faithful is the
//       step that would remove this.
//   (c) A degenerate emitter satisfies it.  Because the cell conjuncts are
//       containments, an emitter that publishes NO cells at all is
//       faithful, and its history is trivially Definition-1 clean even
//       from a windowed trace.  We keep containment rather than equality
//       because it makes the theorem strictly stronger for every emitter
//       that does publish cells, and we state the corner here rather than
//       leave it to be found: this theorem bounds what a faithful emitter
//       can leak, not what it must report.  Completeness of an emitter --
//       that it publishes every cell its record holds -- is a separate
//       property and is not proved here.
//
// ONE STRENGTH WORTH NAMING
//   emit_faithful constrains nothing about the VALUES the emitter writes,
//   and the theorem still holds.  That matters because
//   SiConcurrent::begin carries no postcondition on the values it returns
//   -- the field is commented "informational; unspecified".  Definition 1's
//   value-inequality conjunct only makes a witness harder to satisfy, so
//   leaving values wholly unconstrained strengthens this result instead of
//   weakening it.  The L1 projection is robust to that gap.
// =====================================================================

#![allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The store side.  Restated from lib_si_concurrent.rs with int carriers.
// ---------------------------------------------------------------------

pub type Cell = int;
pub type Agent = int;
pub type Time = int;

/// lib_si_concurrent.rs:87
pub open spec fn in_set(rs: Seq<Cell>, c: Cell) -> bool {
    exists|i: int| 0 <= i < rs.len() && rs[i] == c
}

/// lib_si_concurrent.rs:164-170, with Vec@ written as Seq.
pub struct Rec {
    pub agent: Agent,
    pub read_cells: Seq<Cell>,
    pub read_time: Time,
    pub write_cells: Seq<Cell>,
    pub write_time: Time,
}

/// lib_si_concurrent.rs:176-183.  Definition 1 without the
/// value-inequality and different-agent conjuncts: some record j commits a
/// write to a cell inside record i's read-to-commit window.
pub open spec fn a1_struct(tr: Seq<Rec>) -> bool {
    exists|i: int, j: int, c: Cell|
        0 <= i < tr.len() && 0 <= j < tr.len() && i != j
        && #[trigger] in_set(tr[i].read_cells, c)
        && #[trigger] in_set(tr[j].write_cells, c)
        && tr[i].read_time < tr[j].write_time
        && tr[j].write_time < tr[i].write_time
}

// ---------------------------------------------------------------------
// The detector side.  Definition 1 in full over OpRecords.
// ---------------------------------------------------------------------

pub struct OpRecord {
    pub agent:        int,
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

/// Definition 1, in full: cross-agent, both temporal bounds, and the
/// value-inequality conjunct.
pub open spec fn a1_witness(h: Seq<OpRecord>) -> bool {
    exists |i: int, j: int, c: int|
        0 <= i < h.len() && 0 <= j < h.len() && i != j
        && h[i].agent != h[j].agent
        && #[trigger] reads_spec(h[i], c)
        && #[trigger] writes_spec(h[j], c)
        && h[i].read_time < h[j].write_time
        && h[j].write_time < h[i].write_time
        && first_value(h[i].read_values, c) != first_value(h[j].write_values, c)
}

// ---------------------------------------------------------------------
// The emission relation.
// ---------------------------------------------------------------------

/// One emitted record agrees with its store record on agent and on both
/// times, and publishes no cell the record does not hold.  Nothing is said
/// about values: see the header.
pub open spec fn emit_at(r: Rec, op: OpRecord) -> bool {
    &&& op.agent == r.agent
    &&& op.read_time == r.read_time
    &&& op.write_time == r.write_time
    &&& forall |c: int| #[trigger] reads_spec(op, c) ==> in_set(r.read_cells, c)
    &&& forall |c: int| #[trigger] writes_spec(op, c) ==> in_set(r.write_cells, c)
}

/// A faithful emission publishes one OpRecord per store record, in order.
/// Index-preserving and total: it filters nothing, which is what SiStore
/// does and what distinguishes this hypothesis from Theorem L2j's.
pub open spec fn emit_faithful(tr: Seq<Rec>, h: Seq<OpRecord>) -> bool {
    &&& h.len() == tr.len()
    &&& forall |k: int| 0 <= k < tr.len() ==> #[trigger] emit_at(tr[k], h[k])
}

// ---------------------------------------------------------------------
// The theorem.
// ---------------------------------------------------------------------

/// THEOREM L1j.  A faithful emission of a window-free store trace contains
/// no Definition-1 witness.
///
/// Transport: a Definition-1 witness in h at (i, j, c) yields, through
/// emit_faithful, an a1_struct witness in tr at the same (i, j, c) --
/// the cell conjuncts by containment, the temporal ones by equality --
/// contradicting the hypothesis.  Definition 1's extra conjuncts
/// (cross-agent, value inequality) are simply discarded, which is sound
/// precisely because a1_struct has fewer of them.
pub proof fn thm_l1_projection(tr: Seq<Rec>, h: Seq<OpRecord>)
    requires
        !a1_struct(tr),
        emit_faithful(tr, h),
    ensures
        !a1_witness(h),
{
    if a1_witness(h) {
        let (i, j, c) = choose |i: int, j: int, c: int|
            0 <= i < h.len() && 0 <= j < h.len() && i != j
            && h[i].agent != h[j].agent
            && reads_spec(h[i], c)
            && writes_spec(h[j], c)
            && h[i].read_time < h[j].write_time
            && h[j].write_time < h[i].write_time
            && first_value(h[i].read_values, c) != first_value(h[j].write_values, c);

        assert(emit_at(tr[i], h[i]));
        assert(emit_at(tr[j], h[j]));
        assert(in_set(tr[i].read_cells, c));
        assert(in_set(tr[j].write_cells, c));
        assert(tr[i].read_time == h[i].read_time);
        assert(tr[j].write_time == h[j].write_time);
        assert(tr[i].write_time == h[i].write_time);
        assert(a1_struct(tr));
        assert(false);
    }
}

// ---------------------------------------------------------------------
// Non-vacuity.  Both directions, so neither the hypothesis nor the
// conclusion is idle.
// ---------------------------------------------------------------------

/// The prevented phenomenon.  A two-record trace that DOES carry a window,
/// faithfully emitted, DOES fire Definition 1 -- so !a1_struct(tr) is
/// carrying the theorem rather than the conclusion being unreachable.
pub proof fn lemma_windowed_trace_admits_a1()
    ensures
        exists |tr: Seq<Rec>, h: Seq<OpRecord>|
            a1_struct(tr) && emit_faithful(tr, h) && a1_witness(h),
{
    let r0 = Rec { agent: 1, read_cells: seq![7int], read_time: 0,
                   write_cells: Seq::<Cell>::empty(), write_time: 2 };
    let r1 = Rec { agent: 2, read_cells: Seq::<Cell>::empty(), read_time: 0,
                   write_cells: seq![7int], write_time: 1 };
    let tr = seq![r0, r1];

    let o0 = OpRecord { agent: 1, read_set: seq![7int], read_values: seq![(7int, 5int)],
                        read_time: 0, write_set: Seq::<int>::empty(),
                        write_values: Seq::<(int, int)>::empty(), write_time: 2 };
    let o1 = OpRecord { agent: 2, read_set: Seq::<int>::empty(),
                        read_values: Seq::<(int, int)>::empty(), read_time: 0,
                        write_set: seq![7int], write_values: seq![(7int, 9int)],
                        write_time: 1 };
    let h = seq![o0, o1];

    assert(in_set(tr[0].read_cells, 7int)) by { assert(tr[0].read_cells[0] == 7int); }
    assert(in_set(tr[1].write_cells, 7int)) by { assert(tr[1].write_cells[0] == 7int); }
    assert(a1_struct(tr));

    assert(reads_spec(h[0], 7int)) by { assert(h[0].read_set[0] == 7int); }
    assert(writes_spec(h[1], 7int)) by { assert(h[1].write_set[0] == 7int); }
    assert(first_match(h[0].read_values, 7int, 0));
    assert(first_match(h[1].write_values, 7int, 0));
    assert(first_value(h[0].read_values, 7int) == Some(5int));
    assert(first_value(h[1].write_values, 7int) == Some(9int));

    assert forall |k: int| 0 <= k < tr.len() implies #[trigger] emit_at(tr[k], h[k]) by {
        if k == 0 {
            assert forall |c: int| #[trigger] reads_spec(h[0], c) implies in_set(tr[0].read_cells, c) by {
                let m = choose |m: int| 0 <= m < h[0].read_set.len() && h[0].read_set[m] == c;
                assert(tr[0].read_cells[m] == c);
            }
            assert forall |c: int| #[trigger] writes_spec(h[0], c) implies in_set(tr[0].write_cells, c) by {
                assert(h[0].write_set.len() == 0);
            }
        } else {
            assert(k == 1);
            assert forall |c: int| #[trigger] reads_spec(h[1], c) implies in_set(tr[1].read_cells, c) by {
                assert(h[1].read_set.len() == 0);
            }
            assert forall |c: int| #[trigger] writes_spec(h[1], c) implies in_set(tr[1].write_cells, c) by {
                let m = choose |m: int| 0 <= m < h[1].write_set.len() && h[1].write_set[m] == c;
                assert(tr[1].write_cells[m] == c);
            }
        }
    }
    assert(emit_faithful(tr, h));
    assert(a1_witness(h));
}

/// The positive companion: a window-free trace, faithfully emitted, is
/// Definition-1 clean -- and the hypothesis is satisfiable, so the theorem
/// is not true merely because no trace meets it.
pub proof fn lemma_clean_trace_projects_clean()
    ensures
        exists |tr: Seq<Rec>, h: Seq<OpRecord>|
            !a1_struct(tr) && emit_faithful(tr, h) && !a1_witness(h),
{
    // A writer that commits before the reader even begins: the only
    // candidate pair is i = 1, j = 0, and 2 < 1 is false.
    let r0 = Rec { agent: 1, read_cells: Seq::<Cell>::empty(), read_time: 0,
                   write_cells: seq![7int], write_time: 1 };
    let r1 = Rec { agent: 2, read_cells: seq![7int], read_time: 2,
                   write_cells: Seq::<Cell>::empty(), write_time: 3 };
    let tr = seq![r0, r1];

    let o0 = OpRecord { agent: 1, read_set: Seq::<int>::empty(),
                        read_values: Seq::<(int, int)>::empty(), read_time: 0,
                        write_set: seq![7int], write_values: seq![(7int, 9int)],
                        write_time: 1 };
    let o1 = OpRecord { agent: 2, read_set: seq![7int], read_values: seq![(7int, 9int)],
                        read_time: 2, write_set: Seq::<int>::empty(),
                        write_values: Seq::<(int, int)>::empty(), write_time: 3 };
    let h = seq![o0, o1];

    assert forall |k: int| 0 <= k < tr.len() implies #[trigger] emit_at(tr[k], h[k]) by {
        if k == 0 {
            assert forall |c: int| #[trigger] reads_spec(h[0], c) implies in_set(tr[0].read_cells, c) by {
                assert(h[0].read_set.len() == 0);
            }
            assert forall |c: int| #[trigger] writes_spec(h[0], c) implies in_set(tr[0].write_cells, c) by {
                let m = choose |m: int| 0 <= m < h[0].write_set.len() && h[0].write_set[m] == c;
                assert(tr[0].write_cells[m] == c);
            }
        } else {
            assert(k == 1);
            assert forall |c: int| #[trigger] reads_spec(h[1], c) implies in_set(tr[1].read_cells, c) by {
                let m = choose |m: int| 0 <= m < h[1].read_set.len() && h[1].read_set[m] == c;
                assert(tr[1].read_cells[m] == c);
            }
            assert forall |c: int| #[trigger] writes_spec(h[1], c) implies in_set(tr[1].write_cells, c) by {
                assert(h[1].write_set.len() == 0);
            }
        }
    }
    assert(emit_faithful(tr, h));

    assert(!a1_struct(tr)) by {
        assert forall |i: int, j: int, c: Cell|
            (0 <= i < tr.len() && 0 <= j < tr.len() && i != j
             && in_set(tr[i].read_cells, c)
             && in_set(tr[j].write_cells, c)
             && tr[i].read_time < tr[j].write_time)
            implies !(tr[j].write_time < tr[i].write_time) by {
            if i == 1 && j == 0 {
                assert(tr[1].read_time == 2);
                assert(tr[0].write_time == 1);
            } else {
                assert(tr[0].read_cells.len() == 0 || tr[1].write_cells.len() == 0);
            }
        }
    }

    thm_l1_projection(tr, h);
    assert(!a1_witness(h));
}

} // verus!
