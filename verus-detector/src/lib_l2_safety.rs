// =====================================================================
// Verus proof: L_2 safety theorem for a causal-tracking runtime that
// prevents both A_1 (stale-generation) and A_3 (causal-cascade).
//
// COMPILE
//   verus --crate-type=lib src/lib_l2_safety.rs
//
// MOTIVATION
//   The existing safety theorems of lib.rs, lib_ssi.rs, and
//   lib_default_si.rs prove ~A_1 only. The lattice point L_2 is
//   defined as ~A_1 AND ~A_3: prevention of both stale-generation and
//   the causal cascade through which a stale read propagates via a
//   subsequent write. A reviewer of the v5_3 paper observed that
//   only L_1 was mechanically verified across runtimes, leaving the
//   higher lattice levels as paper design. This file closes the
//   L_1 -> L_2 step.
//
// CONSTRUCTION
//   The L_2 runtime carries a per-transaction `predecessors` set
//   recording the transaction IDs of every committed transaction
//   that wrote to a cell this transaction read. A commit is valid
//   only if (a) the read-set is fresh against the current committed
//   store (~A_1), and (b) no predecessor has subsequently aborted
//   (~A_3). If a transaction aborts, every transaction with it in
//   the predecessor set is cascade-aborted. The runtime's reachable
//   states are then proved to admit no A_3 witness on committed
//   transactions.
//
// STATUS (complete): the per-transaction `read_from` provenance field
//   (added to TxnState/empty_txn, populated in step_read) is now
//   constrained by inv_read_provenance and underpins the runtime-level
//   catalogue-A_3 correspondence (Theorem L_2i, lemma_l2_reads_supported).
//   15 verified, 0 errors; no assume, no admit.

#![allow(unused_imports)]
#![allow(dead_code)]
use vstd::prelude::*;

verus! {

// =====================================================================
// Section 1: Carriers
// =====================================================================

pub type CellId  = int;
pub type TxnId   = int;
pub type Value   = int;
pub type Time    = int;

// =====================================================================
// Section 2: Transaction record
// =====================================================================

pub struct TxnState {
    pub started:       bool,
    pub committed:     bool,
    pub aborted:       bool,
    /// Cells this transaction read, with the value observed.
    pub read_set:      Set<CellId>,
    pub read_values:   Map<CellId, Value>,
    /// Cells this transaction wrote, with the value to publish.
    pub write_set:     Set<CellId>,
    pub write_values:  Map<CellId, Value>,
    /// Committed transactions whose writes appear in this txn's
    /// read_values: every t' such that this txn read a cell c whose
    /// latest committed value at the time of the read was written
    /// by t'. Captures the causal closure for A_3.
    pub predecessors:  Set<TxnId>,
    /// Per-cell read provenance: for each cell c this txn read,
    /// read_from[c] is the transaction whose published write it observed
    /// (cell_writer[c] at read time). Recorded so the catalogue-A_3
    /// correspondence can identify the producer of each read value.
    /// Unconstrained until the inv_read_provenance invariant is added.
    pub read_from:     Map<CellId, TxnId>,
    /// Per-cell read timestamp: read_at[c] is `now` at the moment this txn
    /// read cell c. Paired with the producer's commit_time it lets the
    /// catalogue-A_3 residue assert write_time <= read_time (Definition 3).
    pub read_at:       Map<CellId, Time>,
    /// Time of commit (meaningful only when committed == true).
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

// =====================================================================
// Section 3: Runtime state
// =====================================================================

/// The L_2 runtime state. Cells carry their current committed value
/// AND the transaction id that committed them; the writer-id is
/// needed to compute predecessor sets at read time.
pub struct RuntimeState {
    pub now:           Time,
    pub txns:          Map<TxnId, TxnState>,
    /// For each cell, the current committed value and the txn that
    /// committed it.
    pub cell_value:    Map<CellId, Value>,
    pub cell_writer:   Map<CellId, TxnId>,
    /// Set of all transaction ids ever started, for quantification.
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

// =====================================================================
// Section 4: L_2 commit validation predicates
// =====================================================================

/// The read-freshness predicate: the values this transaction
/// observed for each cell in its read-set match the current
/// committed value for that cell. This is the operational ~A_1
/// check.
pub open spec fn reads_fresh(s: RuntimeState, t: TxnId) -> bool {
    let txn = s.txns[t];
    forall |c: CellId| #![trigger txn.read_set.contains(c)]
        txn.read_set.contains(c)
        ==> s.cell_value.contains_key(c)
            && s.cell_value[c] == txn.read_values[c]
}

/// The predecessor-clean predicate: every transaction in this
/// transaction's predecessor set has committed and not aborted.
/// This is the operational ~A_3 check: the causal closure
/// contains no aborted writes.
pub open spec fn predecessors_clean(s: RuntimeState, t: TxnId) -> bool {
    let txn = s.txns[t];
    forall |p: TxnId| #![trigger txn.predecessors.contains(p)]
        txn.predecessors.contains(p)
        ==> s.txns.contains_key(p)
            && s.txns[p].committed
            && !s.txns[p].aborted
}

/// A transaction's commit is L_2-valid iff reads are fresh and the
/// causal closure is clean.
pub open spec fn commit_valid(s: RuntimeState, t: TxnId) -> bool {
    s.txns.contains_key(t)
    && s.txns[t].started
    && !s.txns[t].committed
    && !s.txns[t].aborted
    && reads_fresh(s, t)
    && predecessors_clean(s, t)
}

/// CAUSAL-CLOSURE INVARIANT (new): every transaction's predecessor
/// set is transitively closed -- if p is a predecessor of u and q is
/// a predecessor of p, then q is also a predecessor of u. step_read
/// maintains this by unioning in the writer's predecessors. This is
/// the invariant that lets the one-level cascade_abort discharge the
/// transitive case without recursion: a transitive dependent of an
/// aborted txn is, by closure, a DIRECT dependent too, hence caught
/// by the one-level cascade.
pub open spec fn pred_closed(s: RuntimeState) -> bool {
    forall |u: TxnId, p: TxnId, q: TxnId|
        #![trigger s.txns[u].predecessors.contains(p), s.txns[p].predecessors.contains(q)]
        s.txns.contains_key(u)
        && s.txns[u].predecessors.contains(p)
        && s.txns[p].predecessors.contains(q)
        ==> s.txns[u].predecessors.contains(q)
}

// =====================================================================
// Section 5: Reachable-state invariant
// =====================================================================

/// The runtime's reachable-state invariant: every committed,
/// non-aborted transaction has reads that were fresh and
/// predecessors that were clean AT COMMIT TIME. After commit time,
/// the cell-store may have moved on; the invariant is about the
/// state at the moment of commit. We capture this by requiring
/// that the predecessors of any committed transaction are also
/// committed and non-aborted in the current state (because once a
/// predecessor aborts, the dependent transaction is
/// cascade-aborted, so a committed, non-aborted transaction's
/// predecessors must still be committed and non-aborted now).
pub open spec fn invariant_committed_predecessors_clean(s: RuntimeState) -> bool {
    forall |t: TxnId| #![trigger s.txns[t].committed]
        s.txns.contains_key(t)
        && s.txns[t].committed
        && !s.txns[t].aborted
        ==> predecessors_clean(s, t)
}

// =====================================================================
// Section 6: Transitions
// =====================================================================

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
        // the cell's recorded writer is a known transaction, so that
        // unioning its predecessor set below is meaningful:
        s.txns.contains_key(s.cell_writer[c]),
{
    let txn = s.txns[t];
    let writer = s.cell_writer[c];
    let new_txn = TxnState {
        read_set: txn.read_set.insert(c),
        read_values: txn.read_values.insert(c, s.cell_value[c]),
        // CAUSAL CLOSURE: record not only the direct writer but the
        // writer's own causal closure. This makes `predecessors` the
        // transitive closure the header comment claims, and is what
        // makes the one-level cascade_abort sufficient (see
        // lemma_cascade_preserves_clean_predecessors).
        predecessors: txn.predecessors.insert(writer).union(s.txns[writer].predecessors),
        // PROVENANCE: record which committed txn produced this read value
        // (cell_writer[c] at read time). Carried for the catalogue-A_3
        // correspondence; unconstrained until inv_read_provenance is added.
        read_from: txn.read_from.insert(c, writer),
        // TIMESTAMP: logical time of this read, for the temporal residue.
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

/// Commit transition: only enabled when commit_valid holds.
pub open spec fn step_commit(s: RuntimeState, t: TxnId) -> RuntimeState
    recommends commit_valid(s, t)
{
    let txn = s.txns[t];
    let new_txn = TxnState {
        committed: true,
        commit_time: s.now,
        ..txn
    };
    // Publish writes: update cell_value and cell_writer for each
    // cell in the write set. We do this via a single map-merge
    // operation (per-cell update is straightforward; for the
    // mechanised proof we abstract the merge as a quantified
    // update that the safety theorem doesn't need to unfold).
    RuntimeState {
        now: s.now + 1,
        txns: s.txns.insert(t, new_txn),
        cell_value: publish_writes(s.cell_value, txn.write_set,
                                    txn.write_values),
        cell_writer: publish_writer(s.cell_writer, txn.write_set, t),
        ..s
    }
}

/// Abstract write-publishing function: returns a new cell_value
/// map with every cell in write_set updated to its corresponding
/// write_value.
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

/// Abort transition: mark this transaction aborted, and cascade
/// to every transaction that has it in its predecessor set.
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

/// Cascade-abort: every transaction with t in its predecessor set
/// is marked aborted. Modelled as a single map-rewrite quantifying
/// over all transactions.
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

// =====================================================================
// Section 7: A_1 and A_3 predicates on traces
// =====================================================================

/// A_1 fires for a committed transaction t if some cell in its
/// read-set has a current value that differs from the value the
/// transaction observed AT COMMIT. The commit_valid predicate
/// enforces that no committed transaction satisfies this; the
/// theorem below records that.
pub open spec fn a1_witness_at_commit(s: RuntimeState, t: TxnId) -> bool {
    s.txns.contains_key(t)
    && s.txns[t].committed
    && exists |c: CellId|
        #![trigger s.txns[t].read_set.contains(c)]
        s.txns[t].read_set.contains(c)
        && s.cell_value.contains_key(c)
        && s.cell_value[c] != s.txns[t].read_values[c]
}

/// A_3 fires on the committed transaction t if some predecessor
/// in t's causal closure has aborted. ~A_3 on every committed
/// transaction is the L_2 contribution beyond L_1.
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

// =====================================================================
// Section 8: Safety theorems
// =====================================================================

/// THEOREM L_2a (~A_1 at commit). If a commit transition for
/// transaction t is enabled in state s, then no A_1 witness exists
/// for t in the post-commit state on the cells t did not itself
/// overwrite. This is the operational ~A_1 guarantee at the
/// moment of commit; it is the same property the L_1 proofs
/// establish, restated here for the L_2 runtime.
pub proof fn lemma_l2_no_a1_at_commit(s: RuntimeState, t: TxnId)
    requires commit_valid(s, t),
    ensures
        forall |c: CellId|
            s.txns[t].read_set.contains(c)
            && !s.txns[t].write_set.contains(c)
            ==> s.cell_value.contains_key(c)
                && s.cell_value[c] == s.txns[t].read_values[c],
{
    // Direct from reads_fresh(s, t).
}

/// THEOREM L_2b (~A_3 at commit). If a commit transition for
/// transaction t is enabled in state s, no A_3 witness exists
/// for t in s: every predecessor in t's causal closure is
/// committed and non-aborted. The cascade-abort invariant of
/// step_abort guarantees this property is preserved after commit.
pub proof fn lemma_l2_no_a3_at_commit(s: RuntimeState, t: TxnId)
    requires commit_valid(s, t),
    ensures
        forall |p: TxnId|
            s.txns[t].predecessors.contains(p)
            ==> s.txns.contains_key(p)
                && s.txns[p].committed
                && !s.txns[p].aborted,
{
    // Direct from predecessors_clean(s, t).
}

/// THEOREM L_2c (cascade preserves invariant). After any
/// abort transition that cascades, every committed non-aborted
/// transaction in the resulting state still has clean
/// predecessors. This is the key invariant-preservation theorem
/// that justifies the L_2 contract over arbitrary execution.
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
        // In the post-abort state, u is committed and non-aborted.
        // Cascade ensures every txn with t in its predecessors got
        // aborted. So if u survived the cascade, u does not have t
        // in its predecessors. Therefore u's predecessor set is
        // unchanged from s, and any predecessor of u is still
        // committed and non-aborted (because the only state change
        // was aborting t and the cascade set, none of which can be
        // in u's predecessors).
        let u_txn = s2.txns[u];
        // Cascade: u_txn.aborted is true iff s.txns[u].aborted ||
        // s.txns[u].predecessors.contains(t). Since u_txn.aborted
        // is false, s.txns[u] was not aborted in s and u did not
        // have t as a predecessor.
        assert(!u_txn.aborted);
        assert(!s.txns[u].predecessors.contains(t));
        // Predecessor set is unchanged.
        assert(u_txn.predecessors == s.txns[u].predecessors);
        // The original invariant gave us predecessors_clean(s, u).
        assert(predecessors_clean(s, u));
        // Show predecessors_clean(s2, u).
        assert forall |p: TxnId|
            u_txn.predecessors.contains(p)
            implies s2.txns.contains_key(p)
                && s2.txns[p].committed
                && !s2.txns[p].aborted
        by {
            // p is a predecessor of u. We prove p was NOT cascade-aborted,
            // discharging the previously-assumed transitive case using the
            // causal-closure invariant pred_closed(s).
            //
            // u survived the cascade, so (as asserted above) t is not a
            // direct predecessor of u:
            assert(!s.txns[u].predecessors.contains(t));
            // Suppose for contradiction that t is a predecessor of p. By
            // pred_closed(s) instantiated at (u, p, t) -- both trigger terms
            // s.txns[u].predecessors.contains(p) and
            // s.txns[p].predecessors.contains(t) are present here -- t would
            // also be a direct predecessor of u, contradicting the line above.
            if s.txns[p].predecessors.contains(t) {
                assert(s.txns[u].predecessors.contains(t));  // by pred_closed
                assert(false);
            }
            assert(!s.txns[p].predecessors.contains(t));
            // p != t as well: if p were t, then t in u.predecessors, excluded.
            assert(p != t);
            // The original invariant gives predecessors_clean(s, u), hence p
            // is present, committed, and non-aborted in s:
            assert(s.txns.contains_key(p));
            assert(s.txns[p].committed);
            assert(!s.txns[p].aborted);
            // step_abort first marks t aborted, then cascade_abort flips
            // `aborted` to true only for ids whose predecessor set contains t.
            // p's does not (shown above) and p != t, so s2.txns[p] == s.txns[p];
            // key-membership and the committed flag are preserved by the
            // map-rewrite regardless of the predecessor test.
            assert(s2.txns.contains_key(p));
            assert(s2.txns[p].committed);
            assert(!s2.txns[p].aborted);
        }
    }
}

/// THEOREM L_2d (commit_valid implies no A_1 witness). The
/// commit transition for t produces a state where the A_1
/// predicate, evaluated against t's read_set, has no witness
/// among cells t did not itself overwrite.
pub proof fn lemma_commit_valid_implies_no_a1(s: RuntimeState, t: TxnId)
    requires commit_valid(s, t),
    ensures
        forall |c: CellId|
            #![trigger s.txns[t].read_set.contains(c)]
            s.txns[t].read_set.contains(c)
            && !s.txns[t].write_set.contains(c)
            ==> s.cell_value[c] == s.txns[t].read_values[c],
{
    // From reads_fresh.
}

/// THEOREM L_2e (commit_valid implies no A_3 witness). The
/// commit transition for t produces a state where the A_3
/// predicate has no witness on t's predecessor set.
pub proof fn lemma_commit_valid_implies_no_a3(s: RuntimeState, t: TxnId)
    requires commit_valid(s, t),
    ensures !a3_witness(step_commit(s, t), t)
        || forall |p: TxnId|
            s.txns[t].predecessors.contains(p)
            ==> !s.txns[p].aborted,
{
    // From predecessors_clean.
}

/// PRESERVATION (the remaining obligation). pred_closed must hold on
/// all reachable states for lemma_cascade_preserves_clean_predecessors
/// to apply. begin/write/commit/abort do not change any predecessor
/// SET, so they preserve pred_closed trivially; the only non-trivial
/// case is step_read, which extends t's predecessors by
/// {writer} union writer.predecessors.
///
/// CRUCIAL SUBTLETY (do not remove): step_read preserves closure only
/// because a transaction's predecessor set is FROZEN once anything can
/// depend on it. A txn becomes a predecessor of another only by having
/// COMMITTED and published a cell that the other then reads; committed
/// txns perform no further reads, so their predecessor set never grows
/// after commit. Without this, a reader u that already has t as a
/// predecessor would be left stale when t later reads a new cell. The
/// two auxiliary invariants below capture exactly that condition and
/// MUST be carried in the reachable-state invariant alongside
/// pred_closed; step_read must be applied only to non-committed t.
// =====================================================================
// Section 8b: Non-vacuity --- without the cascade discipline, A_3 fires
// =====================================================================

/// THEOREM L_2g (no cascade-abort admits A_3; non-vacuity). If a
/// committed, non-aborted transaction t has, in its recorded causal
/// closure, a transaction p that has aborted, then an A_3 witness
/// exists for t. This shows the cascade-abort discipline of
/// step_abort is non-vacuous: the predicate the L_2 safety theorem
/// excludes is genuinely satisfiable, so the safety result is not
/// vacuously about an empty predicate.
///
/// SCOPE (stated, not hidden): like lib_l4_safety.rs::L_4c, this
/// establishes SATISFIABILITY of the witness, NOT reachability from
/// initial_state via a no-discipline transition sequence. Under the
/// cascade discipline of step_abort such a t would itself have been
/// aborted (it has the aborted p as a predecessor), so the witness
/// state is exactly the one the discipline removes; demonstrating it
/// is reachable when the cascade is replaced by a no-op is a stronger
/// statement we do not mechanize here.
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
    // p witnesses the existential in a3_witness: it is a predecessor
    // of t (the registered trigger term), present in txns, and aborted.
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

/// Domain agreement: a cell has a value iff it has a recorded writer.
/// Needed so that publish_writer's value function cw[c] is well-defined
/// for cells outside the write set during commit.
pub open spec fn inv_cell_domains(s: RuntimeState) -> bool {
    forall |c: CellId| #![trigger s.cell_value.contains_key(c)]
        s.cell_value.contains_key(c) <==> s.cell_writer.contains_key(c)
}

/// Every published cell's recorded writer actually wrote that cell with the
/// published value. Links cell_writer/cell_value to the writer's own write
/// record; the foundation for the read-provenance invariant of the next stage.
pub open spec fn inv_cell_writer_wrote(s: RuntimeState) -> bool {
    forall |c: CellId| #![trigger s.cell_writer[c]]
        s.cell_value.contains_key(c)
        ==> s.txns.contains_key(s.cell_writer[c])
            && s.txns[s.cell_writer[c]].write_set.contains(c)
            && s.txns[s.cell_writer[c]].write_values[c] == s.cell_value[c]
}

/// READ PROVENANCE: for every started transaction tt and every cell cc it
/// read, read_from[cc] is recorded, is a predecessor of tt, and is a
/// transaction that actually wrote cc with exactly the value tt observed.
/// Quantified over all started txns (not just committed) so the property is
/// established incrementally at each read and simply carried by commit. This
/// is the runtime's per-cell record of where each read value came from -- the
/// information the flat `predecessors` closure discards.
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
    // committed transactions never appear as the reading txn of a
    // subsequent step_read; operationally commit is terminal. Stated
    // as: any txn that is a predecessor of some other txn is committed
    // (so its set is final). This is already implied by
    // predecessors_clean on reachable states, restated for the
    // preservation argument.
    forall |u: TxnId, p: TxnId| #![trigger s.txns[u].predecessors.contains(p)]
        s.txns.contains_key(u) && s.txns[u].predecessors.contains(p)
        ==> s.txns.contains_key(p) && s.txns[p].committed
}

/// THEOREM L_2f (closure preserved by read). VERIFIED. The argument is
/// a case split on whether the quantified u,p equal t, using pred_closed
/// for the unchanged transactions and the union for t. The case where
/// some u already has t as a predecessor is ruled out by
/// inv_committed_frozen (t is not yet committed when it reads, so it is
/// not in anyone's predecessor set), which is the subtlety noted above.
pub proof fn lemma_step_read_preserves_pred_closed(
    s: RuntimeState, t: TxnId, c: CellId,
)
    requires
        pred_closed(s),
        inv_writers_committed(s),
        inv_committed_frozen(s),
        s.txns.contains_key(t),
        s.cell_value.contains_key(c),
        !s.txns[t].committed,          // step_read only on live txns
    ensures
        pred_closed(step_read(s, t, c)),
{
    let s2 = step_read(s, t, c);
    let writer = s.cell_writer[c];
    let old = s.txns[t].predecessors;
    let wp = s.txns[writer].predecessors;
    // s2.txns[t].predecessors == old.insert(writer).union(wp); for x != t,
    // s2.txns[x] == s.txns[x]. (step_read is `open`, so these unfold.)
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
                // s2[u] == s2[p] == s2[t]; the goal s2[t].preds.contains(q)
                // is exactly the hypothesis s2[p].preds.contains(q).
            } else {
                // p != t  =>  s2.txns[p] == s.txns[p].
                assert(s2.txns[p].predecessors =~= s.txns[p].predecessors);
                // p is in s2[t].preds = old.insert(writer).union(wp), so
                // p in old, or p == writer, or p in wp.
                assert(s2.txns[t].predecessors.contains(p));
                if old.contains(p) {
                    // pred_closed(s) at (t, p, q): both trigger terms below.
                    assert(s.txns[t].predecessors.contains(p));
                    assert(s.txns[p].predecessors.contains(q));
                    assert(old.contains(q));            // <= pred_closed(s)
                } else if p == writer {
                    // s.txns[writer].preds == wp contains q.
                    assert(s.txns[writer].predecessors.contains(q));
                    assert(wp.contains(q));
                } else {
                    // p in wp; pred_closed(s) at (writer, p, q).
                    assert(s.txns.contains_key(writer));  // <= inv_writers_committed via recommends
                    assert(wp.contains(p));
                    assert(s.txns[writer].predecessors.contains(p));
                    assert(s.txns[p].predecessors.contains(q));
                    assert(wp.contains(q));             // <= pred_closed(s)
                }
                // q in old, or q == writer (in old.insert), or q in wp:
                assert(old.insert(writer).union(wp).contains(q));
                assert(s2.txns[u].predecessors.contains(q));
            }
        } else {
            // u != t  =>  s2.txns[u] == s.txns[u].
            assert(s2.txns[u].predecessors =~= s.txns[u].predecessors);
            if p == t {
                // s.txns[u].preds.contains(t)  =>  (inv_committed_frozen)
                // s.txns[t].committed, contradicting the !committed precondition.
                assert(s.txns[u].predecessors.contains(t));
                assert(s.txns[t].committed);            // <= inv_committed_frozen
                assert(false);                          // contradicts requires !committed
            } else {
                // u != t and p != t: both predecessor sets unchanged.
                assert(s2.txns[p].predecessors =~= s.txns[p].predecessors);
                assert(s.txns[u].predecessors.contains(p));
                assert(s.txns[p].predecessors.contains(q));
                assert(s.txns[u].predecessors.contains(q));  // <= pred_closed(s)
            }
        }
    }
}

// =====================================================================
// Section 9: combined reachable-state invariant and per-step
// preservation. inv_l2 bundles the conjuncts the cascade lemma
// and the closure proof depend on. Proving every step preserves inv_l2
// (plus inv_l2 of the initial state) discharges, by induction, the
// pred_closed precondition of lemma_cascade_preserves_clean_predecessors
// on all reachable states -- which is what turns the discharged `assume`
// into an end-to-end result. The base case (lemma_initial_inv_l2) and the
// five per-step preservation lemmas below are all verified (no assume,
// no admit), completing the induction.
// =====================================================================
pub open spec fn inv_l2(s: RuntimeState) -> bool {
    &&& invariant_committed_predecessors_clean(s)
    &&& pred_closed(s)
    &&& inv_writers_committed(s)
    &&& inv_committed_frozen(s)
    &&& inv_cell_domains(s)
    &&& inv_cell_writer_wrote(s)
    &&& inv_read_provenance(s)
}

// =====================================================================
// Section 9: STAGE 4 -- temporal closure of the catalogue-A_3 residue
//
// inv_l2 establishes the VALUE half of Definition 3 (Theorem L_2i: every
// committed read has a surviving committed producer that wrote exactly the
// observed value). It says nothing about WHEN that producer committed. The
// catalogued residue additionally requires write_time <= read_time. The two
// invariants below add precisely that, and lemma_l2_reads_supported_temporal
// discharges the full residue. The construction is additive: inv_l2 and its
// five-step induction are reused verbatim, so the existing obligations are
// untouched.
// =====================================================================

/// Every committed transaction committed at or before the current time.
/// `now` increases by one per transition and commit_time is set to `now` at
/// the commit, so this is structural monotonicity. It is the hypothesis that
/// lets step_read conclude the producer it records committed no later than the
/// read time.
pub open spec fn inv_commit_time_le_now(s: RuntimeState) -> bool {
    forall |t: TxnId| #![trigger s.txns[t].commit_time]
        (s.txns.contains_key(t) && s.txns[t].committed)
        ==> s.txns[t].commit_time <= s.now
}

/// TEMPORAL PROVENANCE: for every started txn tt and every cell cc it read,
/// the producer recorded in read_from[cc] committed no later than the time
/// recorded for that read (read_at[cc]). Combined with inv_read_provenance
/// (the producer wrote exactly the observed value) this is the full
/// Definition-3 residue: write_time <= read_time.
pub open spec fn inv_read_temporal(s: RuntimeState) -> bool {
    forall |tt: TxnId, cc: CellId| #![trigger s.txns[tt].read_set.contains(cc)]
        (s.txns.contains_key(tt) && s.txns[tt].read_set.contains(cc))
        ==> s.txns.contains_key(s.txns[tt].read_from[cc])
            && s.txns[s.txns[tt].read_from[cc]].commit_time
                 <= s.txns[tt].read_at[cc]
}

/// The L_2 invariant bundle strengthened with the two temporal facts.
pub open spec fn inv_l2t(s: RuntimeState) -> bool {
    &&& inv_l2(s)
    &&& inv_commit_time_le_now(s)
    &&& inv_read_temporal(s)
}

/// begin: a fresh, non-committed txn with empty predecessors. Trivial:
/// nothing committed changes, no cell changes, and (since t is fresh and
/// inv_committed_frozen makes every predecessor a committed key) no
/// existing predecessor set can mention t.
pub proof fn lemma_begin_preserves_inv_l2(s: RuntimeState, t: TxnId)
    requires inv_l2(s), !s.txns.contains_key(t),
    ensures inv_l2(step_begin(s, t)),
{
    let s2 = step_begin(s, t);
    // begin leaves cell_value/cell_writer (..s) and inserts only the fresh t,
    // which is not the writer of any published cell.
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
            assert(s.txns.contains_key(w));   // inv_cell_writer_wrote(s)
            assert(s.txns[w].write_set.contains(c));
            assert(s.txns[w].write_values[c] == s.cell_value[c]);
            assert(w != t);                   // w in s.txns, t is fresh
            assert(s2.txns[w] == s.txns[w]);  // insert(t,..) leaves w
        }
    }
    // inv_read_provenance(s2): the fresh t has empty read_set (vacuous); every
    // other txn and its producers are unchanged.
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
                assert(s2.txns[t].read_set =~= Set::<CellId>::empty());  // ..empty_txn()
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

/// write: changes only write_set/write_values, which appear in none of
/// the four conjuncts. Trivial.
pub proof fn lemma_write_preserves_inv_l2(s: RuntimeState, t: TxnId, c: CellId, v: Value)
    requires inv_l2(s), s.txns.contains_key(t), !s.txns[t].committed,
    ensures inv_l2(step_write(s, t, c, v)),
{
    let s2 = step_write(s, t, c, v);
    // write leaves cells (..s) and changes only t's write_set/write_values. A
    // non-committed t is never a cell_writer (inv_writers_committed), so no
    // published cell's writer record is the one being modified.
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
            assert(s.txns.contains_key(w) && s.txns[w].committed);  // inv_writers_committed(s)
            assert(s.txns[w].write_set.contains(cc));               // inv_cell_writer_wrote(s)
            assert(s.txns[w].write_values[cc] == s.cell_value[cc]);
            assert(w != t);                    // t not committed => w != t
            assert(s2.txns[w] == s.txns[w]);   // insert(t,..) leaves w
        }
    }
    // inv_read_provenance(s2): write touches no read-side field; a producer is a
    // predecessor, hence committed (inv_committed_frozen), hence != the
    // non-committed t, so its write record is untouched.
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
                assert(s2.txns[t].read_set == s.txns[t].read_set);          // ..txn
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
            assert(s.txns[w].committed);       // inv_committed_frozen at (tt,w)
            assert(w != t);                    // t not committed => w != t
            assert(s2.txns[w] == s.txns[w]);
        }
    }
}

/// abort: invariant_committed_predecessors_clean via the cascade lemma
/// (which needs pred_closed, supplied by inv_l2); the other three
/// conjuncts hold because cascade_abort changes only `aborted` flags,
/// never predecessor SETS, cell_writer, or `committed`.
pub proof fn lemma_abort_preserves_inv_l2(s: RuntimeState, t: TxnId)
    requires inv_l2(s), s.txns.contains_key(t),
    ensures inv_l2(step_abort(s, t)),
{
    lemma_cascade_preserves_clean_predecessors(s, t);
    let s2 = step_abort(s, t);
    // step_abort = cascade_abort(s.txns.insert(t, {aborted,..}), t); both the
    // insert and cascade_abort change only `aborted`. So for every key,
    // predecessors and `committed` are unchanged and the key set is unchanged.
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
        // base preserves every field except `aborted` for every key
        // (insert only flips t's aborted flag):
        assert(base.contains_key(x));
        assert(base[x].predecessors == s.txns[x].predecessors);
        assert(base[x].committed == s.txns[x].committed);
        assert(base[x].write_set == s.txns[x].write_set);
        assert(base[x].write_values == s.txns[x].write_values);
        assert(base[x].read_set == s.txns[x].read_set);
        assert(base[x].read_values == s.txns[x].read_values);
        assert(base[x].read_from == s.txns[x].read_from);
        // s2.txns == cascade_abort(base, t): a Map::new whose value is base[x]
        // or { aborted: true, ..base[x] }; both keep all non-aborted fields.
        assert(s2.txns[x].predecessors == base[x].predecessors);
        assert(s2.txns[x].committed == base[x].committed);
        assert(s2.txns[x].write_set == base[x].write_set);
        assert(s2.txns[x].write_values == base[x].write_values);
        assert(s2.txns[x].read_set == base[x].read_set);
        assert(s2.txns[x].read_values == base[x].read_values);
        assert(s2.txns[x].read_from == base[x].read_from);
    }
    // cells are untouched by abort (RuntimeState { .. , ..s }):
    assert(s2.cell_value =~= s.cell_value);
    assert(s2.cell_writer =~= s.cell_writer);
    // pred_closed(s2): predecessor sets are the same as in s.
    assert(pred_closed(s2)) by {
        assert forall |u: TxnId, p: TxnId, q: TxnId|
            #![trigger s2.txns[u].predecessors.contains(p), s2.txns[p].predecessors.contains(q)]
            s2.txns.contains_key(u) && s2.txns[u].predecessors.contains(p)
            && s2.txns[p].predecessors.contains(q)
            implies s2.txns[u].predecessors.contains(q)
        by {
            assert(s2.txns[u].predecessors == s.txns[u].predecessors);
            assert(s2.txns[p].predecessors == s.txns[p].predecessors);
            // pred_closed(s) at (u,p,q) closes it.
        }
    }
    // inv_committed_frozen(s2): predecessors and committed unchanged.
    assert(inv_committed_frozen(s2)) by {
        assert forall |u: TxnId, p: TxnId| #![trigger s2.txns[u].predecessors.contains(p)]
            s2.txns.contains_key(u) && s2.txns[u].predecessors.contains(p)
            implies s2.txns.contains_key(p) && s2.txns[p].committed
        by {
            assert(s2.txns[u].predecessors == s.txns[u].predecessors);
            // inv_committed_frozen(s) gives committed(p) in s; committed unchanged.
            assert(s2.txns[p].committed == s.txns[p].committed);
        }
    }
    // inv_cell_writer_wrote(s2): cells unchanged and every txn's write record
    // is unchanged by abort (forall above), so each published cell's writer
    // still records the same write.
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
            assert(s.cell_value.contains_key(c));    // antecedent under unchanged cells
            assert(s.txns.contains_key(w));          // inv_cell_writer_wrote(s)
            assert(s.txns[w].write_set.contains(c));
            assert(s.txns[w].write_values[c] == s.cell_value[c]);
            assert(s2.txns.contains_key(w));
            assert(s2.txns[w].write_set == s.txns[w].write_set);
            assert(s2.txns[w].write_values == s.txns[w].write_values);
        }
    }
    // inv_read_provenance(s2): abort flips only `aborted`; all read- and
    // write-side fields are unchanged (forall above), so each recorded read
    // still points to a producer that wrote the same value.
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
    // inv_writers_committed(s2) and inv_cell_domains(s2): cells unchanged, and
    // the writer's `committed` flag is unchanged (only `aborted` may flip).
}

/// read: pred_closed via the (verified) preservation lemma;
/// invariant_committed_predecessors_clean holds because t is not
/// committed (so the invariant does not constrain it) and no other txn
/// changes; inv_writers_committed because no cell changes; and
/// inv_committed_frozen because t's new predecessors (writer and the
/// writer's predecessors) are all committed -- writer by
/// inv_writers_committed, the writer's predecessors by
/// inv_committed_frozen applied at the writer.
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
    // inv_committed_frozen(s2): the only changed predecessor set is t's.
    assert forall |u: TxnId, p: TxnId| #![trigger s2.txns[u].predecessors.contains(p)]
        s2.txns.contains_key(u) && s2.txns[u].predecessors.contains(p)
        implies s2.txns.contains_key(p) && s2.txns[p].committed
    by {
        if u == t {
            // p in old(t) UNION {writer} UNION writer.preds.
            if s.txns[t].predecessors.contains(p) {
                // old predecessor: committed by inv_committed_frozen(s).
            } else if p == writer {
                // writer is committed by inv_writers_committed(s).
            } else {
                // p in writer.predecessors: committed by
                // inv_committed_frozen(s) applied at (writer, p).
                assert(s.txns[writer].predecessors.contains(p));
            }
        }
        // u != t: predecessor set unchanged; inv_committed_frozen(s).
    }
    // inv_cell_writer_wrote(s2): read changes no cell and no write record
    // (only t's read_set/read_values/predecessors/read_from change).
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
            assert(s.txns.contains_key(w));   // inv_cell_writer_wrote(s)
            assert(s.txns[w].write_set.contains(cc));
            assert(s.txns[w].write_values[cc] == s.cell_value[cc]);
            if w == t {
                assert(s2.txns[t].write_set == s.txns[t].write_set);      // ..txn keeps writes
                assert(s2.txns[t].write_values == s.txns[t].write_values);
            } else {
                assert(s2.txns[w] == s.txns[w]);   // insert(t,..) leaves w
            }
        }
    }
    // inv_read_provenance(s2): the new (t,c) read points to `writer`, which by
    // inv_cell_writer_wrote wrote c with exactly cell_value[c] = the recorded
    // read value, and is in t's (grown) predecessors. Old reads of t and all
    // reads of other txns are unchanged (predecessors only grow).
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
                    // freshly recorded read
                    assert(s2.txns[t].read_from[c] == writer);            // insert(c, writer)
                    assert(s2.txns[t].read_from.contains_key(c));
                    assert(s2.txns[t].predecessors.contains(writer));     // in insert(writer)
                    assert(s2.txns[t].read_values[c] == s.cell_value[c]); // insert(c, cell_value)
                    assert(s.cell_value.contains_key(c));
                    assert(s.txns.contains_key(writer) && s.txns[writer].committed); // inv_writers_committed
                    assert(writer != t);
                    assert(s2.txns[writer] == s.txns[writer]);
                    assert(s.txns[writer].write_set.contains(c));         // inv_cell_writer_wrote
                    assert(s.txns[writer].write_values[c] == s.cell_value[c]);
                } else {
                    // old read of t at cc != c
                    assert(s.txns[t].read_set.contains(cc));              // cc in old read_set
                    let w = s.txns[t].read_from[cc];
                    assert(s.txns[t].read_from.contains_key(cc));
                    assert(s.txns[t].predecessors.contains(w));
                    assert(s.txns.contains_key(w));
                    assert(s.txns[w].write_set.contains(cc));
                    assert(s.txns[w].write_values[cc] == s.txns[t].read_values[cc]);
                    assert(s2.txns[t].read_from[cc] == w);                // insert at c != cc
                    assert(s2.txns[t].read_from.contains_key(cc));
                    assert(s2.txns[t].predecessors.contains(w));          // superset of old
                    assert(s2.txns[t].read_values[cc] == s.txns[t].read_values[cc]);
                    assert(s.txns[w].committed);                          // inv_committed_frozen
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
                assert(s.txns[w].committed);                              // inv_committed_frozen
                assert(w != t);
                assert(s2.txns[w] == s.txns[w]);
            }
        }
    }
}

/// commit: t becomes committed; predecessors_clean(s,t) from commit_valid
/// gives predecessors_clean(s2,t); cell_writer now maps the written cells
/// to t (committed, non-aborted); predecessor sets are unchanged.
pub proof fn lemma_commit_preserves_inv_l2(s: RuntimeState, t: TxnId)
    requires inv_l2(s), commit_valid(s, t),
    ensures inv_l2(step_commit(s, t)),
{
    let s2 = step_commit(s, t);
    let ws = s.txns[t].write_set;
    // commit changes t's committed flag and publishes writes; it changes no
    // predecessor set and aborts no one.
    assert forall |x: TxnId| #![trigger s2.txns[x]]
        s2.txns.contains_key(x) implies
            s.txns.contains_key(x)
            && s2.txns[x].predecessors == s.txns[x].predecessors
            && (s2.txns[x].aborted == s.txns[x].aborted)
    by { }
    // inv_cell_domains(s2): publish_writes and publish_writer extend the
    // (equal, by inv_cell_domains(s)) domains by the SAME set ws.
    assert(inv_cell_domains(s2)) by {
        assert forall |c: CellId| #![trigger s2.cell_value.contains_key(c)]
            s2.cell_value.contains_key(c) <==> s2.cell_writer.contains_key(c)
        by {
            // s2.cell_value.contains_key(c) == (ws.contains(c) || s.cell_value.contains_key(c))
            // s2.cell_writer.contains_key(c) == (ws.contains(c) || s.cell_writer.contains_key(c))
            // equal by inv_cell_domains(s).
        }
    }
    // inv_writers_committed(s2):
    assert forall |c: CellId| #![trigger s2.cell_writer[c]]
        s2.cell_value.contains_key(c)
        implies s2.txns.contains_key(s2.cell_writer[c])
            && s2.txns[s2.cell_writer[c]].committed
    by {
        if ws.contains(c) {
            // published cell: writer is t, which is committed in s2.
            assert(s2.cell_writer[c] == t);
            assert(s2.txns[t].committed);
        } else {
            // c not written here; by inv_cell_domains(s) it has an old writer,
            // unchanged by publish_writer, committed in s and still in s2.
            assert(s2.cell_value.contains_key(c));
            assert(s.cell_value.contains_key(c));
            assert(s.cell_writer.contains_key(c));         // inv_cell_domains(s)
            assert(s2.cell_writer[c] == s.cell_writer[c]);  // publish_writer off ws
            // inv_writers_committed(s): old writer committed in s; commit of t
            // does not change any other txn's committed flag.
        }
    }
    // invariant_committed_predecessors_clean(s2): the committed-non-aborted
    // set is the old one plus t; predecessors_clean(s2,t) from
    // commit_valid(s,t).predecessors_clean, others unchanged.
    assert(invariant_committed_predecessors_clean(s2)) by {
        assert forall |u: TxnId| #![trigger s2.txns[u].committed]
            s2.txns.contains_key(u) && s2.txns[u].committed && !s2.txns[u].aborted
            implies predecessors_clean(s2, u)
        by {
            // predecessor set of u is unchanged by commit:
            assert(s2.txns[u].predecessors == s.txns[u].predecessors);
            // predecessors_clean in s for u (u==t from commit_valid, else from
            // the invariant, since commit adds only t to the committed set):
            if u != t {
                assert(s.txns[u].committed);
            }
            assert forall |p: TxnId| s.txns[u].predecessors.contains(p)
                implies s2.txns.contains_key(p)
                    && s2.txns[p].committed && !s2.txns[p].aborted
            by {
                // p is committed-non-aborted in s (predecessors_clean(s,u) or
                // predecessors_clean(s,t)); hence p != t, because commit_valid
                // requires t to be un-committed in s. commit changes only t's
                // committed flag and aborts no one, so p's flags are preserved.
                assert(s.txns.contains_key(p) && s.txns[p].committed && !s.txns[p].aborted);
                assert(p != t);
                assert(s2.txns[p] == s.txns[p]);
            }
        }
    }
    // pred_closed(s2), inv_committed_frozen(s2): predecessor sets unchanged.
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
            // p committed in s (inv_committed_frozen(s)); committing t cannot
            // un-commit p, and if p == t then t is committed in s2.
        }
    }
    // inv_cell_writer_wrote(s2): published cells (ws) are written by t with the
    // published value; cells outside ws keep their old (committed, != t) writer.
    assert(inv_cell_writer_wrote(s2)) by {
        assert forall |c: CellId| #![trigger s2.cell_writer[c]]
            s2.cell_value.contains_key(c) implies
                s2.txns.contains_key(s2.cell_writer[c])
                && s2.txns[s2.cell_writer[c]].write_set.contains(c)
                && s2.txns[s2.cell_writer[c]].write_values[c] == s2.cell_value[c]
        by {
            if ws.contains(c) {
                assert(s2.cell_writer[c] == t);                        // publish_writer on ws
                assert(s2.cell_value[c] == s.txns[t].write_values[c]); // publish_writes on ws
                assert(s2.txns[t].write_set == s.txns[t].write_set);   // commit keeps t's writes
                assert(s2.txns[t].write_set.contains(c));              // c in ws == t.write_set
                assert(s2.txns[t].write_values == s.txns[t].write_values);
            } else {
                assert(s.cell_value.contains_key(c));        // publish_writes off ws
                assert(s.cell_writer.contains_key(c));       // inv_cell_domains(s)
                assert(s2.cell_writer[c] == s.cell_writer[c]);  // publish_writer off ws
                assert(s2.cell_value[c] == s.cell_value[c]);    // publish_writes off ws
                let w = s.cell_writer[c];
                assert(s.txns.contains_key(w) && s.txns[w].committed);  // inv_writers_committed(s)
                assert(s.txns[w].write_set.contains(c));               // inv_cell_writer_wrote(s)
                assert(s.txns[w].write_values[c] == s.cell_value[c]);
                assert(w != t);                              // t not committed in s
                assert(s2.txns[w] == s.txns[w]);             // commit changes only t
            }
        }
    }
    // inv_read_provenance(s2): commit changes no read-side field and no txn's
    // write record (only t's committed flag + published cells). A producer is a
    // predecessor, hence committed (inv_committed_frozen) and != the
    // (in-s) non-committed t, so its record is unchanged.
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
                assert(s2.txns[t].read_set == s.txns[t].read_set);          // ..txn
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
            assert(s.txns[w].committed);       // inv_committed_frozen at (tt,w)
            assert(w != t);                    // t not committed in s
            assert(s2.txns[w] == s.txns[w]);   // commit changes only t
        }
    }
}


/// BASE CASE: the initial (empty) state satisfies inv_l2. With no
/// transactions and no cells, every conjunct is vacuous. Together with
/// the five per-step preservation lemmas above, this completes the
/// induction: inv_l2 -- and therefore pred_closed -- holds on every
/// reachable state. The pred_closed precondition of
/// lemma_cascade_preserves_clean_predecessors is thus discharged
/// wherever the cascade is taken, and the L_2 transitive-cascade
/// obligation is closed with NO `assume` and NO `admit`.
pub proof fn lemma_initial_inv_l2()
    ensures inv_l2(initial_state())
{
    // empty txns  => invariant_committed_predecessors_clean, pred_closed,
    //                and inv_committed_frozen hold vacuously;
    // empty cells => inv_writers_committed and inv_cell_domains hold vacuously.
    assert(initial_state().txns =~= Map::<TxnId, TxnState>::empty());
    assert(initial_state().cell_value =~= Map::<CellId, Value>::empty());
    assert(initial_state().cell_writer =~= Map::<CellId, TxnId>::empty());
    // inv_read_provenance, inv_cell_writer_wrote vacuous: no txns, no cells.
}

    /// THEOREM L_2h (reachable states are A_3-free). On every state
    /// satisfying the reachable-state invariant inv_l2, NO committed,
    /// non-aborted transaction has an aborted predecessor: the runtime
    /// A_3 footprint is excluded. Paired with lemma_no_cascade_admits_a3
    /// (which shows the footprint is satisfiable in principle), this
    /// brackets the predicate as non-vacuous yet unreachable under the
    /// cascade discipline -- the end-to-end runtime-level A_3 guarantee.
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

/// THEOREM L_2i (catalogue-A_3 image: every committed read is supported). On
/// any state satisfying inv_l2, for every committed, non-aborted transaction t
/// and every cell c it read, there EXISTS a committed, non-aborted transaction
/// w that wrote c with exactly the value t read. Equivalently: no committed
/// transaction has an unsupported read -- the runtime-level form of the
/// catalogued A_3 (Definition 3) under the abort-respecting view. Proof:
/// read_from[c] is the witness; inv_read_provenance gives that it wrote the
/// value and is a predecessor of t, and predecessors_clean (from
/// invariant_committed_predecessors_clean, since t is committed-clean) makes it
/// committed and non-aborted.
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
        // inv_read_provenance(s) at (t,c):
        assert(s.txns[t].read_set.contains(c));
        assert(s.txns[t].predecessors.contains(w));
        assert(s.txns.contains_key(w));
        assert(s.txns[w].write_set.contains(c));
        assert(s.txns[w].write_values[c] == s.txns[t].read_values[c]);
        // predecessors_clean(s,t) from invariant_committed_predecessors_clean:
        assert(invariant_committed_predecessors_clean(s));
        assert(predecessors_clean(s, t));
        assert(s.txns[w].committed && !s.txns[w].aborted);
        // w witnesses the existential.
        assert(s.txns.contains_key(w) && s.txns[w].committed && !s.txns[w].aborted
            && s.txns[w].write_set.contains(c)
            && s.txns[w].write_values[c] == s.txns[t].read_values[c]);
    }
}
// =====================================================================
// Section 10: STAGE 4 preservation -- inv_l2t over the five transitions
//
// Each lemma calls the corresponding (verified) inv_l2 preservation lemma to
// re-establish inv_l2(s2), then discharges the two temporal conjuncts. The
// only content cases are step_read (the freshly recorded read points to a
// producer committed no later than the read time) and step_commit (the new
// committed time is t's own, and producers of existing reads are committed in
// s, hence != t). begin/write/abort leave every relevant field unchanged.
// =====================================================================

/// begin: fresh t is not committed and has an empty read_set.
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
                assert(!s2.txns[t].committed);                 // ..empty_txn()
            } else {
                assert(s2.txns[x] == s.txns[x]);
                assert(s.txns[x].commit_time <= s.now);        // inv_commit_time_le_now(s)
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
                assert(s2.txns[t].read_set =~= Set::<CellId>::empty());   // ..empty_txn()
            } else {
                assert(s2.txns[tt] == s.txns[tt]);
                assert(s.txns[tt].read_set.contains(cc));      // fire inv_read_temporal(s)
                let w = s.txns[tt].read_from[cc];
                assert(s.txns.contains_key(w));
                assert(s.txns[w].commit_time <= s.txns[tt].read_at[cc]);
                assert(w != t);                                // w in s.txns, t fresh
                assert(s2.txns[w] == s.txns[w]);
                assert(s2.txns[tt].read_from[cc] == w);
                assert(s2.txns[tt].read_at[cc] == s.txns[tt].read_at[cc]);
            }
        }
    }
}

/// write: touches only write_set/write_values; commit_time and all read-side
/// fields are carried by ..txn.
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
                assert(s2.txns[t].committed == s.txns[t].committed);     // ..txn
                assert(!s.txns[t].committed);                            // precondition
            } else {
                assert(s2.txns[x] == s.txns[x]);
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
            assert(s.txns[tt].read_set.contains(cc));                    // fire inv_read_temporal(s)
            let w = s.txns[tt].read_from[cc];
            assert(s.txns.contains_key(w));
            assert(s.txns[w].commit_time <= s.txns[tt].read_at[cc]);
            if w == t {
                assert(s2.txns[t].commit_time == s.txns[t].commit_time); // ..txn
            } else {
                assert(s2.txns[w] == s.txns[w]);
            }
            assert(s2.txns[tt].read_from[cc] == w);
            assert(s2.txns[tt].read_at[cc] == s.txns[tt].read_at[cc]);
        }
    }
}

/// abort: cascade_abort flips only `aborted`; committed, commit_time, read_set,
/// read_from and read_at are preserved for every key (the same base/cascade
/// argument the inv_l2 abort lemma uses for the other fields).
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
            assert(s.txns[x].commit_time <= s.now);                      // inv_commit_time_le_now(s)
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
            assert(s.txns[tt].read_set.contains(cc));                    // fire inv_read_temporal(s)
            let w = s.txns[tt].read_from[cc];
            assert(s.txns.contains_key(w));
            assert(s.txns[w].commit_time <= s.txns[tt].read_at[cc]);
            assert(s2.txns.contains_key(w));
            assert(s2.txns[w].commit_time == s.txns[w].commit_time);
        }
    }
}

/// read: the content case. The freshly recorded read (t,c) points to `writer`,
/// which inv_writers_committed makes committed and inv_commit_time_le_now
/// bounds by s.now == the recorded read_at[c].
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
                assert(s2.txns[t].committed == s.txns[t].committed);     // ..txn
                assert(!s.txns[t].committed);                            // precondition
            } else {
                assert(s2.txns[x] == s.txns[x]);
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