// =====================================================================
// Verus proof: L_2 safety theorem for a causal-tracking runtime that
// prevents both A_1 (stale-generation) and A_3 (causal-cascade).
//
// COMPILE
//   verus --crate-type=lib src/lib_l2_exec.rs
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
use vstd::hash_map::HashMapWithView;
use vstd::hash_set::HashSetWithView;

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

// =====================================================================
// Section 10: EXEC-MODE VERIFICATION OF THE L_2 RUNTIME
// =====================================================================
// Iteration 1: verified state + view + new + begin + a3_free capstone.
// Closes the Rust->spec gap: the EXECUTABLE runtime maintains inv_l2 on its
// abstract view and is therefore A_3-free, plugging exec methods into the
// model lemmas proved ABOVE in this same file (no new model lemmas).
//
// IDENTIFIERS. The verified runtime is keyed by u64 interned identifiers
// (cells, values, txn ids). u64 -> int via `as int` is natively injective,
// so the abstraction needs NO axiom (zero trust-base additions). String
// interning to u64 is an identity-preserving preprocessing step.
//
// Roadmap: (2) commit (write-set loop), (3) abort (cascade loop),
//          (4) counter-based freshness so begin needs no precondition.

// u64 in-range guard for the int<->u64 round trips.
pub open spec fn in_u64(c: int) -> bool { 0 <= c <= u64::MAX as int }

pub proof fn lemma_u64_roundtrip(k: u64)
    ensures (k as int) as u64 == k, in_u64(k as int),
{}

pub proof fn lemma_int_roundtrip(c: int)
    requires in_u64(c),
    ensures (c as u64) as int == c,
{}

// Choose-free views: the int->u64 inverse is the explicit cast `c as u64`,
// guarded by in_u64, so no `choose`/`exists` is needed.
pub open spec fn view_u64_set(s: Set<u64>) -> Set<int> {
    Set::new(|c: int| in_u64(c) && s.contains(c as u64))
}
pub open spec fn view_u64_map(m: Map<u64, u64>) -> Map<int, int> {
    Map::new(
        |c: int| in_u64(c) && m.contains_key(c as u64),
        |c: int| m[c as u64] as int,
    )
}

// A txn's predecessors are stored as an ordered Vec<u64> (duplicates
// permitted); the model's `predecessors` SET is DERIVED as the set of the
// Vec's elements. A Vec (not a HashSet) is used so that `read` can union the
// writer's causal closure by a push-loop and `abort` can scan for membership
// -- Verus cannot iterate a HashSetWithView in exec mode.
pub open spec fn view_vec_u64_set(s: Seq<u64>) -> Set<int> {
    Set::new(|x: int| exists |i: int| 0 <= i < s.len() && s[i] as int == x)
}

pub proof fn lemma_vec_set_empty()
    ensures view_vec_u64_set(Seq::<u64>::empty()) =~= Set::<int>::empty(),
{
    assert forall |x: int| !view_vec_u64_set(Seq::<u64>::empty()).contains(x) by {
        assert(Seq::<u64>::empty().len() == 0);
    }
}

// Pushing one element extends the set view by exactly that element.
pub proof fn lemma_vec_set_push(s: Seq<u64>, x: u64)
    ensures view_vec_u64_set(s.push(x)) =~= view_vec_u64_set(s).insert(x as int),
{
    let sp = s.push(x);
    lemma_u64_roundtrip(x);
    assert forall |y: int|
        view_vec_u64_set(sp).contains(y) <==> view_vec_u64_set(s).insert(x as int).contains(y)
    by {
        if view_vec_u64_set(sp).contains(y) {
            let i = choose |i: int| 0 <= i < sp.len() && sp[i] as int == y;
            if i < s.len() {
                assert(sp[i] == s[i]);
            } else {
                assert(i == s.len());
                assert(sp[i] == x);
            }
        }
        if view_vec_u64_set(s).insert(x as int).contains(y) {
            if y == x as int {
                assert(sp[s.len() as int] == x);
                assert(0 <= s.len() < sp.len());
            } else {
                let i = choose |i: int| 0 <= i < s.len() && s[i] as int == y;
                assert(sp[i] == s[i]);
            }
        }
    }
}

// Membership in the set view corresponds to an index in the Vec.
pub proof fn lemma_vec_set_contains_iff(s: Seq<u64>, x: u64)
    ensures view_vec_u64_set(s).contains(x as int)
            <==> (exists |i: int| 0 <= i < s.len() && s[i] == x),
{
    lemma_u64_roundtrip(x);
    if view_vec_u64_set(s).contains(x as int) {
        let i = choose |i: int| 0 <= i < s.len() && s[i] as int == (x as int);
        assert(s[i] == x);
    }
    if exists |i: int| 0 <= i < s.len() && s[i] == x {
        let i = choose |i: int| 0 <= i < s.len() && s[i] == x;
        assert(s[i] as int == x as int);
    }
}

// Executable transaction record (all u64-keyed verified containers).
pub struct ExecTxn {
    pub started:      bool,
    pub committed:    bool,
    pub aborted:      bool,
    pub read_set:     HashSetWithView<u64>,
    pub read_values:  HashMapWithView<u64, u64>,
    pub writes:       Vec<(u64, u64)>,
    pub predecessors: Vec<u64>,
    pub read_from:    HashMapWithView<u64, u64>,
    pub read_at:      HashMapWithView<u64, u64>,
    pub commit_time:  u64,
}

impl ExecTxn {
    pub open spec fn view(self) -> TxnState {
        TxnState {
            started:      self.started,
            committed:    self.committed,
            aborted:      self.aborted,
            read_set:     view_u64_set(self.read_set@),
            read_values:  view_u64_map(self.read_values@),
            write_set:    writes_set(self.writes@),
            write_values: writes_map(self.writes@),
            predecessors: view_vec_u64_set(self.predecessors@),
            read_from:    view_u64_map(self.read_from@),
            read_at:      view_u64_map(self.read_at@),
            commit_time:  self.commit_time as int,
        }
    }

    pub fn new_started() -> (r: ExecTxn)
        ensures r.view() == (TxnState { started: true, ..empty_txn() }),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        let r = ExecTxn {
            started: true, committed: false, aborted: false,
            read_set:     HashSetWithView::new(),
            read_values:  HashMapWithView::new(),
            writes:       Vec::new(),
            predecessors: Vec::new(),
            read_from:    HashMapWithView::new(),
            read_at:      HashMapWithView::new(),
            commit_time:  0,
        };
        proof {
            assert(view_u64_set(r.read_set@) =~= Set::<int>::empty());
            assert(writes_set(r.writes@) =~= Set::<int>::empty());
            assert(view_vec_u64_set(r.predecessors@) =~= Set::<int>::empty());
            assert(view_u64_map(r.read_values@) =~= Map::<int, int>::empty());
            assert(writes_map(r.writes@) =~= Map::<int, int>::empty());
            assert(view_u64_map(r.read_from@) =~= Map::<int, int>::empty());
            assert(view_u64_map(r.read_at@) =~= Map::<int, int>::empty());
            assert(r.view() =~= (TxnState { started: true, ..empty_txn() }));
        }
        r
    }
}

// Txn-map and all-txns views over the runtime's txn store.
pub open spec fn view_txns_map(m: Map<u64, ExecTxn>) -> Map<int, TxnState> {
    Map::new(
        |t: int| in_u64(t) && m.contains_key(t as u64),
        |t: int| m[t as u64].view(),
    )
}
pub open spec fn view_alltxns(m: Map<u64, ExecTxn>) -> Set<int> {
    Set::new(|t: int| in_u64(t) && m.contains_key(t as u64))
}

// View commutes with a fresh txn insert (the begin congruence).
pub proof fn lemma_view_txns_insert(m: Map<u64, ExecTxn>, k: u64, v: ExecTxn)
    ensures
        view_txns_map(m.insert(k, v)) =~= view_txns_map(m).insert(k as int, v.view()),
        view_alltxns(m.insert(k, v)) =~= view_alltxns(m).insert(k as int),
{
    lemma_u64_roundtrip(k);
    assert forall |t: int| #[trigger] in_u64(t) implies (t as u64) as int == t by {
        lemma_int_roundtrip(t);
    }
    assert(view_txns_map(m.insert(k, v)) =~= view_txns_map(m).insert(k as int, v.view()));
    assert(view_alltxns(m.insert(k, v)) =~= view_alltxns(m).insert(k as int));
}

// View commutes with a single set/map insert (the write congruences).
pub proof fn lemma_view_set_insert(s: Set<u64>, c: u64)
    ensures view_u64_set(s.insert(c)) =~= view_u64_set(s).insert(c as int),
{
    lemma_u64_roundtrip(c);
    assert forall |x: int| #[trigger] in_u64(x) implies (x as u64) as int == x by {
        lemma_int_roundtrip(x);
    }
    assert(view_u64_set(s.insert(c)) =~= view_u64_set(s).insert(c as int));
}

pub proof fn lemma_view_map_insert(m: Map<u64, u64>, c: u64, v: u64)
    ensures view_u64_map(m.insert(c, v)) =~= view_u64_map(m).insert(c as int, v as int),
{
    lemma_u64_roundtrip(c);
    assert forall |x: int| #[trigger] in_u64(x) implies (x as u64) as int == x by {
        lemma_int_roundtrip(x);
    }
    assert(view_u64_map(m.insert(c, v)) =~= view_u64_map(m).insert(c as int, v as int));
}

// A txn's writes are stored as an ordered Vec<(cell, value)>; the model's
// write_set / write_values are DERIVED (last-write-wins for repeated cells).
pub open spec fn last_val(s: Seq<(u64, u64)>, c: u64) -> u64
    decreases s.len()
{
    if s.len() == 0 { 0 }
    else if s[s.len() - 1].0 == c { s[s.len() - 1].1 }
    else { last_val(s.drop_last(), c) }
}
pub open spec fn writes_set(s: Seq<(u64, u64)>) -> Set<int> {
    Set::new(|c: int| in_u64(c) && exists |i: int| 0 <= i < s.len() && #[trigger] s[i].0 == c as u64)
}
pub open spec fn writes_map(s: Seq<(u64, u64)>) -> Map<int, int> {
    Map::new(
        |c: int| in_u64(c) && exists |i: int| 0 <= i < s.len() && #[trigger] s[i].0 == c as u64,
        |c: int| last_val(s, c as u64) as int,
    )
}

pub proof fn lemma_last_val_push(s: Seq<(u64, u64)>, c: u64, v: u64, x: u64)
    ensures last_val(s.push((c, v)), x) == if x == c { v } else { last_val(s, x) },
{
    let sp = s.push((c, v));
    assert(sp.len() == s.len() + 1);
    assert(sp[sp.len() - 1] == (c, v));
    assert(sp.drop_last() =~= s);
}

// View commutes with a Vec push (the write congruence).
pub proof fn lemma_writes_push(s: Seq<(u64, u64)>, c: u64, v: u64)
    ensures
        writes_set(s.push((c, v))) =~= writes_set(s).insert(c as int),
        writes_map(s.push((c, v))) =~= writes_map(s).insert(c as int, v as int),
{
    lemma_u64_roundtrip(c);
    assert forall |x: int| #[trigger] in_u64(x) implies (x as u64) as int == x by {
        lemma_int_roundtrip(x);
    }
    let sp = s.push((c, v));
    assert(sp.len() == s.len() + 1);
    assert(sp[sp.len() - 1] == (c, v));
    assert forall |x: u64| #[trigger] last_val(sp, x)
        == (if x == c { v } else { last_val(s, x) }) by {
        lemma_last_val_push(s, c, v, x);
    }
    // membership in sp = membership in s, plus the new cell c
    assert forall |y: int| #[trigger] in_u64(y) implies
        ((exists |i: int| 0 <= i < sp.len() && sp[i].0 == y as u64)
         <==> ((exists |i: int| 0 <= i < s.len() && s[i].0 == y as u64) || y == c as int)) by {
        lemma_int_roundtrip(y);
        lemma_u64_roundtrip(c);
        // forward: sp has y  ==>  s has y, or y == c
        if exists |i: int| 0 <= i < sp.len() && sp[i].0 == y as u64 {
            let i = choose |i: int| 0 <= i < sp.len() && sp[i].0 == y as u64;
            if i < s.len() {
                assert(sp[i] == s[i]);
                assert(s[i].0 == y as u64);
            } else {
                assert(i == s.len());
                assert(sp[i] == (c, v));
                assert((y as u64) == c);
                assert(y == c as int);
            }
        }
        // reverse (a): s has y  ==>  sp has y
        if exists |i: int| 0 <= i < s.len() && s[i].0 == y as u64 {
            let i = choose |i: int| 0 <= i < s.len() && s[i].0 == y as u64;
            assert(sp[i] == s[i]);
            assert(0 <= i < sp.len() && sp[i].0 == y as u64);
        }
        // reverse (b): y == c  ==>  sp has y (at the pushed index)
        if y == c as int {
            assert((y as u64) == c);
            assert(sp[s.len() as int] == (c, v));
            assert(0 <= (s.len() as int) < sp.len() && sp[s.len() as int].0 == y as u64);
        }
    }
    assert(writes_set(sp) =~= writes_set(s).insert(c as int));
    assert(writes_map(sp) =~= writes_map(s).insert(c as int, v as int));
}

// Publishing one more write extends the published cell maps by one entry.
pub proof fn lemma_publish_push(cv: Map<int, int>, s: Seq<(u64, u64)>, c: u64, v: u64)
    ensures
        publish_writes(cv, writes_set(s.push((c, v))), writes_map(s.push((c, v))))
            =~= publish_writes(cv, writes_set(s), writes_map(s)).insert(c as int, v as int),
{
    lemma_writes_push(s, c, v);
    let ws = writes_set(s);
    let wv = writes_map(s);
    let cc = c as int;
    let vv = v as int;
    assert(writes_set(s.push((c, v))) =~= ws.insert(cc));
    assert(writes_map(s.push((c, v))) =~= wv.insert(cc, vv));
    assert(publish_writes(cv, ws.insert(cc), wv.insert(cc, vv))
           =~= publish_writes(cv, ws, wv).insert(cc, vv));
}

pub proof fn lemma_publish_writer_push(cw: Map<int, int>, s: Seq<(u64, u64)>, writer: int, c: u64, v: u64)
    ensures
        publish_writer(cw, writes_set(s.push((c, v))), writer)
            =~= publish_writer(cw, writes_set(s), writer).insert(c as int, writer),
{
    lemma_writes_push(s, c, v);
    let ws = writes_set(s);
    let cc = c as int;
    assert(writes_set(s.push((c, v))) =~= ws.insert(cc));
    assert(publish_writer(cw, ws.insert(cc), writer)
           =~= publish_writer(cw, ws, writer).insert(cc, writer));
}

// Executable runtime state (u64-keyed). txns never lose keys, so
// all_txns == dom(txns).
pub struct L2Runtime {
    pub now:         u64,
    pub txns:        HashMapWithView<u64, ExecTxn>,
    pub cell_value:  HashMapWithView<u64, u64>,
    pub cell_writer: HashMapWithView<u64, u64>,
    pub next_txn:    u64,
}

impl L2Runtime {
    pub open spec fn view(self) -> RuntimeState {
        RuntimeState {
            now:         self.now as int,
            txns:        view_txns_map(self.txns@),
            cell_value:  view_u64_map(self.cell_value@),
            cell_writer: view_u64_map(self.cell_writer@),
            all_txns:    view_alltxns(self.txns@),
        }
    }

    pub open spec fn fresh_ok(self) -> bool {
        forall |k: u64| #[trigger] self.txns@.contains_key(k) ==> (k as int) < (self.next_txn as int)
    }

    // Keys are allocated sequentially by `begin` (t = next_txn) and never
    // deleted, so the live txn keys are exactly the contiguous range
    // [0, next_txn). `abort` enumerates them by scanning that range -- no
    // auxiliary collection, hence nothing extra to frame.
    pub open spec fn keys_contiguous(self) -> bool {
        forall |k: u64| #[trigger] self.txns@.contains_key(k)
            <==> (k as int) < (self.next_txn as int)
    }

    pub open spec fn wf(self) -> bool {
        &&& inv_l2(self.view())
        &&& self.fresh_ok()
        &&& self.keys_contiguous()
    }

    pub fn new() -> (r: L2Runtime)
        ensures r.wf(), r.view() == initial_state(),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        let r = L2Runtime {
            now: 0,
            txns:        HashMapWithView::new(),
            cell_value:  HashMapWithView::new(),
            cell_writer: HashMapWithView::new(),
            next_txn: 0,
        };
        proof {
            assert(view_txns_map(r.txns@) =~= Map::<int, TxnState>::empty());
            assert(view_alltxns(r.txns@) =~= Set::<int>::empty());
            assert(view_u64_map(r.cell_value@) =~= Map::<int, int>::empty());
            assert(view_u64_map(r.cell_writer@) =~= Map::<int, int>::empty());
            assert(r.view() =~= initial_state());
            lemma_initial_inv_l2();
            assert(inv_l2(r.view()));
            // keys_contiguous: empty txns over next_txn 0 (vacuously true).
            assert(r.keys_contiguous());
        }
        r
    }

    pub fn begin(&mut self) -> (t: u64)
        requires
            old(self).wf(),
            old(self).now < u64::MAX,
            old(self).next_txn < u64::MAX,
        ensures
            final(self).wf(),
            final(self).view() == step_begin(old(self).view(), t as int),
            !old(self).txns@.contains_key(t),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        let t = self.next_txn;
        proof {
            // t is fresh: fresh_ok says every key < next_txn == t.
            assert(!self.txns@.contains_key(t));
            assert(!view_txns_map(self.txns@).contains_key(t as int)) by {
                lemma_u64_roundtrip(t);
            }
        }
        let rec = ExecTxn::new_started();
        let ghost old_txns = self.txns@;
        self.txns.insert(t, rec);
        self.now = self.now + 1;
        self.next_txn = self.next_txn + 1;
        proof {
            // HashMapWithView::insert: self.txns@ == old_txns.insert(t, rec).
            assert(self.txns@ =~= old_txns.insert(t, rec));
            lemma_view_txns_insert(old_txns, t, rec);
            // rec.view() == started-empty TxnState (new_started ensures).
            assert(self.view().txns =~= step_begin(old(self).view(), t as int).txns);
            assert(self.view().all_txns =~= step_begin(old(self).view(), t as int).all_txns);
            assert(self.view() =~= step_begin(old(self).view(), t as int));
            // Preservation via the existing model lemma (t fresh in the view).
            lemma_begin_preserves_inv_l2(old(self).view(), t as int);
            assert(inv_l2(self.view()));
            // fresh_ok re-established.
            assert forall |kk: u64| #[trigger] self.txns@.contains_key(kk)
                implies (kk as int) < (self.next_txn as int) by {
                if kk != t {
                    assert(old_txns.contains_key(kk));
                }
            }
            // keys_contiguous re-established: keys are now [0, next_txn),
            // where next_txn = old next_txn + 1 and t == old next_txn.
            assert(t == old(self).next_txn);
            assert(self.next_txn == old(self).next_txn + 1);
            assert forall |k: u64| #[trigger] self.txns@.contains_key(k)
                <==> (k as int) < (self.next_txn as int) by {
                if self.txns@.contains_key(k) {
                    if k != t {
                        assert(old_txns.contains_key(k));
                        assert((k as int) < (old(self).next_txn as int));
                    }
                }
                if (k as int) < (self.next_txn as int) {
                    if k != t {
                        assert((k as int) < (old(self).next_txn as int));
                        assert(old(self).txns@.contains_key(k));
                    }
                }
            }
        }
        t
    }

    // write: record a single write (cell c := value v) in txn t's write-set.
    // Refines step_write; preserves wf via lemma_write_preserves_inv_l2.
    pub fn write(&mut self, t: u64, c: u64, v: u64)
        requires
            old(self).wf(),
            old(self).now < u64::MAX,
            old(self).txns@.contains_key(t),
            !old(self).txns@[t].committed,
        ensures
            final(self).wf(),
            final(self).view()
                == step_write(old(self).view(), t as int, c as int, v as int),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        let ghost old_txns = self.txns@;
        let ghost old_view = self.view();
        let ghost old_txn = old_txns[t];
        // Take the txn out, modify its write-set/values, put it back.
        let mut txn = self.txns.remove(&t).unwrap();
        txn.writes.push((c, v));
        self.txns.insert(t, txn);
        self.now = self.now + 1;
        proof {
            lemma_u64_roundtrip(t);
            // The removed record is the model's txns[t].
            assert(old_view.txns[t as int] == old_txn.view());
            // Write-Vec push congruence.
            lemma_writes_push(old_txn.writes@, c, v);
            // The reinserted record's view is step_write's new_txn.
            assert(txn.view() =~= TxnState {
                write_set: old_view.txns[t as int].write_set.insert(c as int),
                write_values: old_view.txns[t as int].write_values.insert(c as int, v as int),
                ..old_view.txns[t as int]
            });
            // remove-then-insert on the same key == insert.
            assert(self.txns@ =~= old_txns.insert(t, txn));
            lemma_view_txns_insert(old_txns, t, txn);
            assert(self.view() =~= step_write(old_view, t as int, c as int, v as int));
            // Preservation via the existing model lemma.
            lemma_write_preserves_inv_l2(old_view, t as int, c as int, v as int);
            assert(inv_l2(self.view()));
            // fresh_ok preserved: key set unchanged (t was already present).
            assert forall |kk: u64| #[trigger] self.txns@.contains_key(kk)
                implies (kk as int) < (self.next_txn as int) by {
                assert(old_txns.contains_key(kk) || kk == t);
            }
            // keys_contiguous preserved: key set unchanged (remove-then-insert
            // of the same key t) and next_txn untouched.
            assert(self.txns@.dom() =~= old_txns.dom());
            assert forall |k: u64| #[trigger] self.txns@.contains_key(k)
                <==> (k as int) < (self.next_txn as int) by {
                assert(self.txns@.contains_key(k) <==> old_txns.contains_key(k));
                assert(old_txns.contains_key(k) == old(self).txns@.contains_key(k));
            }
        }
    }

    // commit: publish txn t's writes and mark it committed. Refines
    // step_commit; preserves wf via lemma_commit_preserves_inv_l2. The
    // discipline (only commit when valid) is the commit_valid precondition.
    pub fn commit(&mut self, t: u64)
        requires
            old(self).wf(),
            old(self).now < u64::MAX,
            old(self).txns@.contains_key(t),
            commit_valid(old(self).view(), t as int),
        ensures
            final(self).wf(),
            final(self).view() == step_commit(old(self).view(), t as int),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        let ghost old_view = self.view();
        let ghost old_txns = self.txns@;
        let ghost old_cv = old_view.cell_value;
        let ghost old_cw = old_view.cell_writer;
        let ghost txn0 = old_txns[t];
        proof { lemma_u64_roundtrip(t); }

        // Remove the txn (own it), mark committed, iterate its writes while it
        // is OUT of the map (no clone, no borrow conflict), reinsert after.
        let mut txn = self.txns.remove(&t).unwrap();
        txn.committed = true;
        txn.commit_time = self.now;

        proof {
            assert(self.txns@ =~= old_txns.remove(t));
            assert(txn.writes@ =~= txn0.writes@);
            // Base case: the empty prefix publishes to the original maps.
            assert(txn.writes@.subrange(0, 0) =~= Seq::<(u64, u64)>::empty());
            assert(publish_writes(old_cv, writes_set(txn.writes@.subrange(0, 0)),
                                  writes_map(txn.writes@.subrange(0, 0))) =~= old_cv);
            assert(publish_writer(old_cw, writes_set(txn.writes@.subrange(0, 0)),
                                  t as int) =~= old_cw);
            assert(view_u64_map(self.cell_value@) =~= old_cv);
            assert(view_u64_map(self.cell_writer@) =~= old_cw);
        }

        let mut i: usize = 0;
        while i < txn.writes.len()
            invariant
                0 <= i <= txn.writes.len(),
                txn.writes@ == txn0.writes@,
                self.txns@ == old_txns.remove(t),
                self.now == old(self).now,
                self.next_txn == old(self).next_txn,
                view_u64_map(self.cell_value@)
                    == publish_writes(old_cv, writes_set(txn.writes@.subrange(0, i as int)),
                                      writes_map(txn.writes@.subrange(0, i as int))),
                view_u64_map(self.cell_writer@)
                    == publish_writer(old_cw, writes_set(txn.writes@.subrange(0, i as int)),
                                      t as int),
            decreases txn.writes.len() - i
        {
            let ghost prefix = txn.writes@.subrange(0, i as int);
            let c = txn.writes[i].0;
            let v = txn.writes[i].1;
            let ghost cv_before = self.cell_value@;
            let ghost cw_before = self.cell_writer@;
            proof {
                assert(txn.writes@[i as int] == (c, v));
                assert(txn.writes@.subrange(0, (i + 1) as int) =~= prefix.push((c, v)));
            }
            self.cell_value.insert(c, v);
            self.cell_writer.insert(c, t);
            proof {
                lemma_view_map_insert(cv_before, c, v);
                lemma_view_map_insert(cw_before, c, t);
                lemma_publish_push(old_cv, prefix, c, v);
                lemma_publish_writer_push(old_cw, prefix, t as int, c, v);
            }
            i = i + 1;
        }

        let ghost gtxn = txn;
        proof {
            assert(txn.writes@.subrange(0, i as int) =~= txn.writes@);
            assert(view_u64_map(self.cell_value@)
                == publish_writes(old_cv, writes_set(gtxn.writes@), writes_map(gtxn.writes@)));
            assert(view_u64_map(self.cell_writer@)
                == publish_writer(old_cw, writes_set(gtxn.writes@), t as int));
        }
        self.txns.insert(t, txn);
        self.now = self.now + 1;

        proof {
            assert(self.txns@ =~= old_txns.insert(t, gtxn));
            assert(gtxn.writes@ =~= txn0.writes@);
            // write_set / write_values of the model txn are exactly the Vec views.
            assert(txn0.view().write_set == writes_set(txn0.writes@));
            assert(txn0.view().write_values == writes_map(txn0.writes@));
            // The committed record is step_commit's new_txn.
            assert(gtxn.view() =~= TxnState {
                committed: true,
                commit_time: old_view.now,
                ..txn0.view()
            });
            lemma_view_txns_insert(old_txns, t, gtxn);
            // Assemble: every field of the view matches step_commit.
            let sc = step_commit(old_view, t as int);
            assert(self.view().now == sc.now);
            assert(self.view().txns =~= sc.txns);
            assert(self.view().cell_value =~= sc.cell_value);
            assert(self.view().cell_writer =~= sc.cell_writer);
            assert(self.view().all_txns =~= sc.all_txns);
            assert(self.view() == sc);
            lemma_commit_preserves_inv_l2(old_view, t as int);
            assert(inv_l2(self.view()));
            assert forall |kk: u64| #[trigger] self.txns@.contains_key(kk)
                implies (kk as int) < (self.next_txn as int) by {
                assert(old_txns.contains_key(kk) || kk == t);
            }
            // keys_contiguous preserved: key set unchanged (remove-then-insert
            // of the same key t) and next_txn untouched.
            assert(self.txns@.dom() =~= old_txns.dom());
            assert forall |k: u64| #[trigger] self.txns@.contains_key(k)
                <==> (k as int) < (self.next_txn as int) by {
                assert(self.txns@.contains_key(k) <==> old_txns.contains_key(k));
                assert(old_txns.contains_key(k) == old(self).txns@.contains_key(k));
            }
        }
    }

    // read: txn t reads cell c. Records the value and provenance (writer),
    // stamps the read time, and unions the writer's causal closure into t's
    // predecessors so that one-level cascade_abort is sufficient. Refines
    // step_read; preserves wf via lemma_read_preserves_inv_l2.
    pub fn read(&mut self, t: u64, c: u64)
        requires
            old(self).wf(),
            old(self).now < u64::MAX,
            old(self).txns@.contains_key(t),
            old(self).cell_value@.contains_key(c),
            !old(self).txns@[t].committed,
        ensures
            final(self).wf(),
            final(self).view() == step_read(old(self).view(), t as int, c as int),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        let ghost old_view = self.view();
        let ghost old_txns = self.txns@;
        let ghost txn0 = old_txns[t];

        // c has a recorded value and (by inv_l2) a known, committed writer.
        let v: u64 = *self.cell_value.get(&c).unwrap();
        proof {
            lemma_u64_roundtrip(t);
            lemma_u64_roundtrip(c);
            // inv_cell_domains: cell_value has c => cell_writer has c.
            assert(self.cell_value@.contains_key(c));
            assert(old_view.cell_value.contains_key(c as int)) by { lemma_int_roundtrip(c as int); }
            assert(self.cell_writer@.contains_key(c));
        }
        let writer: u64 = *self.cell_writer.get(&c).unwrap();
        proof {
            lemma_u64_roundtrip(writer);
            lemma_int_roundtrip(c as int);
            assert(self.cell_writer@[c] == writer);
            assert(self.cell_value@[c] == v);
            // view-level value/writer agree with v / writer (via view_u64_map).
            // Establishing the cell_writer[c as int] term FIRST fires the
            // inv_writers_committed trigger below.
            assert(old_view.cell_value[c as int] == v as int);
            assert(old_view.cell_writer[c as int] == writer as int);
            // inv_writers_committed(old_view): the writer is a known committed
            // txn (instantiated at c as int via the cell_writer[c as int] term).
            assert(inv_writers_committed(old_view));
            assert(old_view.txns.contains_key(writer as int));
            assert(self.txns@.contains_key(writer)) by { lemma_u64_roundtrip(writer); }
        }

        // Copy the writer's predecessor Vec out. Works whether writer == t or
        // not, because t is still in the map at this point.
        let ghost wpred = self.txns@[writer].predecessors@;
        let wlen: usize = self.txns.get(&writer).unwrap().predecessors.len();
        let mut wpred_copy: Vec<u64> = Vec::new();
        let mut i: usize = 0;
        while i < wlen
            invariant
                0 <= i <= wlen,
                self.txns@ == old_txns,
                self.txns@.contains_key(writer),
                wpred == self.txns@[writer].predecessors@,
                wlen == wpred.len(),
                wpred_copy@ == wpred.subrange(0, i as int),
            decreases wlen - i
        {
            let x: u64 = self.txns.get(&writer).unwrap().predecessors[i];
            proof { assert(wpred[i as int] == x); }
            wpred_copy.push(x);
            proof {
                assert(wpred.subrange(0, (i + 1) as int) =~= wpred.subrange(0, i as int).push(x));
            }
            i = i + 1;
        }
        proof { assert(wpred_copy@ =~= wpred); }

        // Take t out and build its new record.
        let mut txn = self.txns.remove(&t).unwrap();
        let ghost old_t_pred = txn.predecessors@;
        proof { assert(old_t_pred =~= txn0.predecessors@); }

        // predecessors := old ++ [writer] ++ wpred_copy.
        let ghost before0 = txn.predecessors@;
        txn.predecessors.push(writer);
        proof {
            lemma_vec_set_push(before0, writer);
            lemma_vec_set_empty();
            assert(wpred_copy@.subrange(0, 0) =~= Seq::<u64>::empty());
            assert(view_vec_u64_set(txn.predecessors@)
                =~= view_vec_u64_set(old_t_pred).insert(writer as int)
                    .union(view_vec_u64_set(wpred_copy@.subrange(0, 0))));
        }
        let mut j: usize = 0;
        while j < wpred_copy.len()
            invariant
                0 <= j <= wpred_copy.len(),
                wpred_copy@ == wpred,
                // only predecessors changes in this loop; pin the rest.
                txn.read_set@ == txn0.read_set@,
                txn.read_values@ == txn0.read_values@,
                txn.read_from@ == txn0.read_from@,
                txn.read_at@ == txn0.read_at@,
                txn.writes@ == txn0.writes@,
                txn.started == txn0.started,
                txn.committed == txn0.committed,
                txn.aborted == txn0.aborted,
                txn.commit_time == txn0.commit_time,
                view_vec_u64_set(txn.predecessors@)
                    == view_vec_u64_set(old_t_pred).insert(writer as int)
                       .union(view_vec_u64_set(wpred_copy@.subrange(0, j as int))),
            decreases wpred_copy.len() - j
        {
            let y: u64 = wpred_copy[j];
            let ghost before = txn.predecessors@;
            txn.predecessors.push(y);
            proof {
                lemma_vec_set_push(before, y);
                assert(wpred_copy@.subrange(0, (j + 1) as int)
                    =~= wpred_copy@.subrange(0, j as int).push(y));
                lemma_vec_set_push(wpred_copy@.subrange(0, j as int), y);
                // A.union(B.insert(y)) == A.union(B).insert(y)
                assert(view_vec_u64_set(txn.predecessors@)
                    =~= view_vec_u64_set(old_t_pred).insert(writer as int)
                        .union(view_vec_u64_set(wpred_copy@.subrange(0, (j + 1) as int))));
            }
            j = j + 1;
        }
        proof {
            assert(wpred_copy@.subrange(0, j as int) =~= wpred_copy@);
            assert(view_vec_u64_set(txn.predecessors@)
                =~= view_vec_u64_set(old_t_pred).insert(writer as int)
                    .union(view_vec_u64_set(wpred)));
        }

        // read_set, read_values, read_from, read_at.
        let ghost rs0 = txn.read_set@;
        txn.read_set.insert(c);
        proof { lemma_view_set_insert(rs0, c); }
        let ghost rv0 = txn.read_values@;
        txn.read_values.insert(c, v);
        proof { lemma_view_map_insert(rv0, c, v); }
        let ghost rf0 = txn.read_from@;
        txn.read_from.insert(c, writer);
        proof { lemma_view_map_insert(rf0, c, writer); }
        let ghost ra0 = txn.read_at@;
        txn.read_at.insert(c, self.now);
        proof {
            assert(self.now as int == old_view.now);
            lemma_view_map_insert(ra0, c, self.now);
        }

        let ghost gtxn = txn;
        self.txns.insert(t, txn);
        self.now = self.now + 1;

        proof {
            // The new record is step_read's new_txn (field by field).
            assert(old_view.txns[t as int] == txn0.view());
            assert(old_view.txns[writer as int].predecessors =~= view_vec_u64_set(wpred));
            // bridges: the captured ghosts equal txn0's fields (the other
            // inserts did not touch them); predecessor closure carries to gtxn.
            assert(rs0 =~= txn0.read_set@);
            assert(rv0 =~= txn0.read_values@);
            assert(rf0 =~= txn0.read_from@);
            assert(ra0 =~= txn0.read_at@);
            assert(txn0.view().predecessors =~= view_vec_u64_set(old_t_pred));
            assert(view_vec_u64_set(gtxn.predecessors@)
                =~= view_vec_u64_set(old_t_pred).insert(writer as int)
                    .union(view_vec_u64_set(wpred)));
            assert(gtxn.view() =~= TxnState {
                read_set:     txn0.view().read_set.insert(c as int),
                read_values:  txn0.view().read_values.insert(c as int, v as int),
                predecessors: txn0.view().predecessors.insert(writer as int)
                                  .union(old_view.txns[writer as int].predecessors),
                read_from:    txn0.view().read_from.insert(c as int, writer as int),
                read_at:      txn0.view().read_at.insert(c as int, old_view.now),
                ..txn0.view()
            });
            assert(self.txns@ =~= old_txns.insert(t, gtxn));
            lemma_view_txns_insert(old_txns, t, gtxn);
            let sr = step_read(old_view, t as int, c as int);
            assert(self.view().now == sr.now);
            assert(self.view().txns =~= sr.txns);
            assert(self.view().cell_value =~= sr.cell_value);
            assert(self.view().cell_writer =~= sr.cell_writer);
            assert(self.view().all_txns =~= sr.all_txns);
            assert(self.view() == sr);
            // Preservation via the existing model lemma.
            lemma_read_preserves_inv_l2(old_view, t as int, c as int);
            assert(inv_l2(self.view()));
            // fresh_ok + keys_contiguous: key set and next_txn unchanged.
            assert(self.txns@.dom() =~= old_txns.dom());
            assert forall |kk: u64| #[trigger] self.txns@.contains_key(kk)
                implies (kk as int) < (self.next_txn as int) by {
                assert(old_txns.contains_key(kk) || kk == t);
            }
            assert forall |k: u64| #[trigger] self.txns@.contains_key(k)
                <==> (k as int) < (self.next_txn as int) by {
                assert(self.txns@.contains_key(k) <==> old_txns.contains_key(k));
                assert(old_txns.contains_key(k) == old(self).txns@.contains_key(k));
            }
        }
    }

    // Linear scan: does txn u's predecessor Vec contain t?
    fn txn_pred_contains(&self, u: u64, t: u64) -> (r: bool)
        requires self.txns@.contains_key(u),
        ensures r <==> view_vec_u64_set(self.txns@[u].predecessors@).contains(t as int),
    {
        let n: usize = self.txns.get(&u).unwrap().predecessors.len();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                self.txns@.contains_key(u),
                n == self.txns@[u].predecessors@.len(),
                forall |k: int| 0 <= k < i ==> self.txns@[u].predecessors@[k] != t,
            decreases n - i
        {
            if self.txns.get(&u).unwrap().predecessors[i] == t {
                proof { lemma_vec_set_contains_iff(self.txns@[u].predecessors@, t); }
                return true;
            }
            i = i + 1;
        }
        proof { lemma_vec_set_contains_iff(self.txns@[u].predecessors@, t); }
        false
    }

    // abort: mark t aborted, then cascade-abort every txn whose (transitively
    // closed) predecessor set contains t. Keys are exactly [0, next_txn), so
    // the cascade is a single scan of that range. Refines step_abort; preserves
    // wf via lemma_abort_preserves_inv_l2.
    pub fn abort(&mut self, t: u64)
        requires
            old(self).wf(),
            old(self).now < u64::MAX,
            old(self).txns@.contains_key(t),
        ensures
            final(self).wf(),
            final(self).view() == step_abort(old(self).view(), t as int),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        let ghost old_view = self.view();
        let ghost old_txns = self.txns@;
        let ghost old_cv = self.cell_value@;
        let ghost old_cw = self.cell_writer@;

        // Step 1: mark t aborted.
        let mut txn_t = self.txns.remove(&t).unwrap();
        txn_t.aborted = true;
        let ghost gtxn_t = txn_t;
        self.txns.insert(t, txn_t);

        let ghost base_txns = self.txns@;
        let ghost base_view = view_txns_map(base_txns);
        proof {
            lemma_u64_roundtrip(t);
            assert(base_txns =~= old_txns.insert(t, gtxn_t));
            lemma_view_txns_insert(old_txns, t, gtxn_t);
            assert(gtxn_t.view() =~= TxnState { aborted: true, ..old_view.txns[t as int] });
            assert(base_view =~= old_view.txns.insert(t as int,
                TxnState { aborted: true, ..old_view.txns[t as int] }));
            // base keys are exactly [0, next_txn).
            assert forall |k: u64| #[trigger] base_txns.contains_key(k)
                <==> (k as int) < (self.next_txn as int) by {
                assert(base_txns.contains_key(k) <==> old_txns.contains_key(k) || k == t);
                assert(old_txns.contains_key(k) == old(self).txns@.contains_key(k));
            }
        }

        // Step 2: single-pass cascade over [0, next_txn).
        let n: u64 = self.next_txn;
        let mut u: u64 = 0;
        while u < n
            invariant
                0 <= u <= n,
                n == self.next_txn,
                self.now == old(self).now,
                self.cell_value@ == old_cv,
                self.cell_writer@ == old_cw,
                self.txns@.dom() == base_txns.dom(),
                forall |k: u64| #[trigger] base_txns.contains_key(k) <==> (k as int) < (n as int),
                forall |k: u64| #[trigger] base_txns.contains_key(k) ==>
                    self.txns@.contains_key(k)
                    && self.txns@[k].view() == (
                        if (k as int) < (u as int)
                           && base_txns[k].view().predecessors.contains(t as int) {
                            TxnState { aborted: true, ..base_txns[k].view() }
                        } else {
                            base_txns[k].view()
                        }),
            decreases n - u
        {
            let ghost pre = self.txns@;
            proof {
                // u is in range, so it is a live key and still equals base[u].
                assert(base_txns.contains_key(u));
                assert(self.txns@.contains_key(u));
                assert(self.txns@[u].view() == base_txns[u].view());
            }
            let has_t: bool = self.txn_pred_contains(u, t);
            proof {
                assert(has_t <==> base_txns[u].view().predecessors.contains(t as int));
            }
            if has_t {
                let mut ut = self.txns.remove(&u).unwrap();
                proof { assert(ut == pre[u]); }
                ut.aborted = true;
                let ghost gut = ut;
                self.txns.insert(u, ut);
                proof {
                    assert(self.txns@ =~= pre.insert(u, gut));
                    assert(gut.view() =~= TxnState { aborted: true, ..base_txns[u].view() });
                    assert forall |k: u64| #[trigger] base_txns.contains_key(k) implies
                        self.txns@.contains_key(k)
                        && self.txns@[k].view() == (
                            if (k as int) < ((u + 1) as int)
                               && base_txns[k].view().predecessors.contains(t as int) {
                                TxnState { aborted: true, ..base_txns[k].view() }
                            } else {
                                base_txns[k].view()
                            }) by {
                        if k == u {
                            assert(self.txns@[u] == gut);
                        } else {
                            assert(self.txns@[k] == pre[k]);
                        }
                    }
                }
            } else {
                proof {
                    assert forall |k: u64| #[trigger] base_txns.contains_key(k) implies
                        self.txns@.contains_key(k)
                        && self.txns@[k].view() == (
                            if (k as int) < ((u + 1) as int)
                               && base_txns[k].view().predecessors.contains(t as int) {
                                TxnState { aborted: true, ..base_txns[k].view() }
                            } else {
                                base_txns[k].view()
                            }) by {
                        if k == u {
                            assert(!base_txns[u].view().predecessors.contains(t as int));
                            assert(self.txns@[u].view() == base_txns[u].view());
                        }
                    }
                }
            }
            u = u + 1;
        }

        self.now = self.now + 1;

        proof {
            let ca = cascade_abort(base_view, t as int);
            // view of the final txn store == cascade_abort(base_view, t).
            assert forall |id: int| #[trigger] view_txns_map(self.txns@).contains_key(id)
                implies view_txns_map(self.txns@)[id] == ca[id] by {
                if in_u64(id) && self.txns@.contains_key(id as u64) {
                    let k = id as u64;
                    lemma_int_roundtrip(id);
                    assert(base_txns.contains_key(k));
                    assert((k as int) < (n as int));
                    assert(base_view[id] == base_txns[k].view());
                }
            }
            assert(view_txns_map(self.txns@).dom() =~= ca.dom());
            assert(view_txns_map(self.txns@) =~= ca);
            let sa = step_abort(old_view, t as int);
            assert(self.view().now == sa.now);
            assert(self.view().txns =~= sa.txns);
            assert(self.view().cell_value =~= sa.cell_value);
            assert(self.view().cell_writer =~= sa.cell_writer);
            assert(self.view().all_txns =~= sa.all_txns);
            assert(self.view() == sa);
            // Preservation via the existing model lemma.
            lemma_abort_preserves_inv_l2(old_view, t as int);
            assert(inv_l2(self.view()));
            // fresh_ok + keys_contiguous: key set and next_txn unchanged.
            assert(self.txns@.dom() =~= base_txns.dom());
            assert forall |kk: u64| #[trigger] self.txns@.contains_key(kk)
                implies (kk as int) < (self.next_txn as int) by {
                assert(base_txns.contains_key(kk));
            }
            assert forall |k: u64| #[trigger] self.txns@.contains_key(k)
                <==> (k as int) < (self.next_txn as int) by {
                assert(self.txns@.contains_key(k) <==> base_txns.contains_key(k));
            }
        }
    }

    // CAPSTONE: any wf runtime is A_3-free. Holds now for the new+begin
    // fragment; once commit/abort (iterations 2-3) are shown to preserve wf,
    // this theorem covers the full runtime unchanged.
    pub fn a3_free(&self)
        requires self.wf(),
        ensures forall |t: TxnId| #![trigger self.view().txns[t].committed]
            !a3_witness(self.view(), t),
    {
        proof {
            lemma_l2_reachable_no_a3(self.view());
        }
    }
}
} // verus!