// =====================================================================
// Verus proof: Spec ↔ executable runtime refinement (default-SI).
//
// COMPILE
//   verus --crate-type=lib src/lib_refinement_default_si.rs
//
// MODEL
//   Same simplified (store, last_write) projection as the SSI
//   refinement. Default-SI differs from SSI only in commit semantics:
//   commits with empty write_sets bypass validation and append an
//   empty-write OpRecord. This bypass branch is the source of A_1
//   under no-write workloads.
//
// SCOREBOARD (target)
//   2 foundational axioms shared with pessimistic/SSI refinements:
//     - axiom_string_to_int_injective
//     - axiom_null_sentinel
//   Set::map finiteness preservation is now a proven lemma
//   (lemma_set_map_preserves_finite), not an axiom.
//
//   Real proofs (target):
//     - lemma_init_correspondence_default_si
//     - lemma_set_map_preserves_finite
//     - lemma_abstract_data_insert
//     - lemma_abstract_last_write_insert
//     - lemma_abstract_pending_insert
//     - lemma_abstract_pending_remove
//     - lemma_store_after_commit_commutes
//     - lemma_last_write_after_commit_commutes
//     - lemma_snapshot_commutes
//     - lemma_abstract_default_si_trace_push
//     - lemma_validation_passes_corresponds
//     - lemma_default_si_begin_refines
//     - lemma_default_si_commit_validated_refines
//     - lemma_default_si_commit_bypass_refines    [NEW vs SSI]
//     - lemma_default_si_commit_abort_refines

#![allow(unused_imports)]
#![allow(dead_code)]
use vstd::prelude::*;

verus! {

// =====================================================================
// Section 1: Carriers
// =====================================================================

pub type ConcreteString = Seq<char>;
pub type ConcreteCellId = ConcreteString;
pub type ConcreteAgentId = ConcreteString;
pub type ConcreteValue = ConcreteString;
pub type ConcreteTime = nat;

pub type AbstractCellId = int;
pub type AbstractAgentId = int;
pub type AbstractValue = int;
pub type AbstractTime = int;

pub open spec fn abs_null_value() -> AbstractValue { 0 }

pub open spec fn null_sentinel_string() -> ConcreteString {
    seq!['N', 'U', 'L', 'L']
}

// =====================================================================
// Section 2: Axioms (two foundational, plus proven map-finiteness lemma)
// =====================================================================

pub uninterp spec fn string_to_int(s: ConcreteString) -> int;

#[verifier::external_body]
pub broadcast proof fn axiom_string_to_int_injective(s1: ConcreteString, s2: ConcreteString)
    ensures #![trigger string_to_int(s1), string_to_int(s2)]
        string_to_int(s1) == string_to_int(s2) ==> s1 == s2
{
}

#[verifier::external_body]
pub broadcast proof fn axiom_null_sentinel()
    ensures #![trigger value_alpha(null_sentinel_string())]
        value_alpha(null_sentinel_string()) == abs_null_value()
{
}

// Set::map preserves finiteness — proven by induction, not axiom.
pub proof fn lemma_set_map_preserves_finite<A, B>(s: Set<A>, f: spec_fn(A) -> B)
    requires s.finite()
    ensures s.map(f).finite()
    decreases s.len()
{
    if s.len() == 0 {
        assert(s =~= Set::<A>::empty());
        assert(s.map(f) =~= Set::<B>::empty()) by {
            assert forall |y: B| !#[trigger] s.map(f).contains(y) by {
                if s.map(f).contains(y) {
                    let x = choose |x: A| #[trigger] s.contains(x) && f(x) == y;
                    assert(s.contains(x));
                    assert(false);
                }
            };
        };
    } else {
        let x = s.choose();
        assert(s.contains(x));
        let s_rest = s.remove(x);
        assert(s_rest.finite());
        assert(s_rest.len() < s.len());
        lemma_set_map_preserves_finite(s_rest, f);
        assert(s.map(f) =~= s_rest.map(f).insert(f(x))) by {
            assert forall |y: B|
                s.map(f).contains(y) <==> s_rest.map(f).insert(f(x)).contains(y) by {
                if s.map(f).contains(y) {
                    let z = choose |z: A| #[trigger] s.contains(z) && f(z) == y;
                    if z == x {
                        assert(f(x) == y);
                        assert(s_rest.map(f).insert(f(x)).contains(y));
                    } else {
                        assert(s_rest.contains(z));
                        assert(s_rest.map(f).contains(y));
                        assert(s_rest.map(f).insert(f(x)).contains(y));
                    }
                }
                if s_rest.map(f).insert(f(x)).contains(y) {
                    if y == f(x) {
                        assert(s.contains(x) && f(x) == y);
                        assert(s.map(f).contains(y));
                    } else {
                        assert(s_rest.map(f).contains(y));
                        let z = choose |z: A| #[trigger] s_rest.contains(z) && f(z) == y;
                        assert(s.contains(z));
                        assert(s.map(f).contains(y));
                    }
                }
            };
        };
        assert(s_rest.map(f).insert(f(x)).finite());
    }
}

pub open spec fn cell_alpha(c: ConcreteCellId) -> AbstractCellId { string_to_int(c) }
pub open spec fn agent_alpha(a: ConcreteAgentId) -> AbstractAgentId { string_to_int(a) }
pub open spec fn value_alpha(v: ConcreteValue) -> AbstractValue { string_to_int(v) }

// =====================================================================
// Section 3: Concrete default-SI state (mirrors SSI refinement)
// =====================================================================

pub struct ConcreteDefaultSiOpRecord {
    pub agent: ConcreteAgentId,
    pub read_set: Set<ConcreteCellId>,
    pub read_values: Map<ConcreteCellId, ConcreteValue>,
    pub read_time: ConcreteTime,
    pub write_set: Set<ConcreteCellId>,
    pub write_values: Map<ConcreteCellId, ConcreteValue>,
    pub write_time: ConcreteTime,
}

pub struct ConcreteDefaultSiInner {
    pub store: Map<ConcreteCellId, ConcreteValue>,
    pub last_write: Map<ConcreteCellId, ConcreteTime>,
    pub clock: ConcreteTime,
    pub trace: Seq<ConcreteDefaultSiOpRecord>,
}

pub open spec fn init_concrete_default_si() -> ConcreteDefaultSiInner {
    ConcreteDefaultSiInner {
        store: Map::<ConcreteCellId, ConcreteValue>::empty(),
        last_write: Map::<ConcreteCellId, ConcreteTime>::empty(),
        clock: 0,
        trace: Seq::<ConcreteDefaultSiOpRecord>::empty(),
    }
}

pub struct CallerSnapshot {
    pub read_time: ConcreteTime,
    pub read_values: Map<ConcreteCellId, ConcreteValue>,
}

pub type CallerSnapshotMap = Map<ConcreteAgentId, CallerSnapshot>;

pub open spec fn snapshot_concrete(
    data: Map<ConcreteCellId, ConcreteValue>,
    cells: Seq<ConcreteCellId>,
) -> Map<ConcreteCellId, ConcreteValue>
    decreases cells.len()
{
    if cells.len() == 0 {
        Map::<ConcreteCellId, ConcreteValue>::empty()
    } else {
        snapshot_concrete(data, cells.drop_last()).insert(
            cells.last(),
            if data.contains_key(cells.last()) { data[cells.last()] }
            else { null_sentinel_string() },
        )
    }
}

pub open spec fn concrete_last_write_of(c: &ConcreteDefaultSiInner, cc: ConcreteCellId) -> ConcreteTime {
    if c.last_write.contains_key(cc) { c.last_write[cc] } else { 0 }
}

pub open spec fn concrete_validation_passes(c: &ConcreteDefaultSiInner, snap: CallerSnapshot) -> bool {
    forall |cc: ConcreteCellId|
        #[trigger] snap.read_values.contains_key(cc)
        ==> concrete_last_write_of(c, cc) <= snap.read_time
}

pub open spec fn concrete_store_after_commit(
    base: Map<ConcreteCellId, ConcreteValue>,
    write_set: Set<ConcreteCellId>,
    write_values: Map<ConcreteCellId, ConcreteValue>,
) -> Map<ConcreteCellId, ConcreteValue> {
    Map::new(
        |cc: ConcreteCellId| base.contains_key(cc) || write_set.contains(cc),
        |cc: ConcreteCellId| if write_set.contains(cc) && write_values.contains_key(cc) {
                                 write_values[cc]
                             } else if base.contains_key(cc) {
                                 base[cc]
                             } else {
                                 null_sentinel_string()
                             },
    )
}

pub open spec fn concrete_last_write_after_commit(
    base: Map<ConcreteCellId, ConcreteTime>,
    write_set: Set<ConcreteCellId>,
    new_clock: ConcreteTime,
) -> Map<ConcreteCellId, ConcreteTime> {
    Map::new(
        |cc: ConcreteCellId| base.contains_key(cc) || write_set.contains(cc),
        |cc: ConcreteCellId| if write_set.contains(cc) { new_clock }
                             else if base.contains_key(cc) { base[cc] }
                             else { 0 },
    )
}

// --- Concrete default-SI transitions ---

pub open spec fn concrete_default_si_begin_step(
    c: &ConcreteDefaultSiInner,
    cs: &CallerSnapshotMap,
    agent: ConcreteAgentId,
    cells: Seq<ConcreteCellId>,
    c_new: &ConcreteDefaultSiInner,
    cs_new: &CallerSnapshotMap,
) -> bool {
    !cs.contains_key(agent)
    && c_new.store == c.store
    && c_new.last_write == c.last_write
    && c_new.clock == c.clock
    && c_new.trace == c.trace
    && *cs_new == cs.insert(agent, CallerSnapshot {
        read_time: c.clock,
        read_values: snapshot_concrete(c.store, cells),
    })
}

// Validated commit: non-empty writes + validation passes.
pub open spec fn concrete_default_si_commit_validated_step(
    c: &ConcreteDefaultSiInner,
    cs: &CallerSnapshotMap,
    agent: ConcreteAgentId,
    write_set: Set<ConcreteCellId>,
    write_values: Map<ConcreteCellId, ConcreteValue>,
    c_new: &ConcreteDefaultSiInner,
    cs_new: &CallerSnapshotMap,
) -> bool {
    cs.contains_key(agent)
    && !write_set.is_empty()
    && write_set.finite()
    && write_set.subset_of(write_values.dom())
    && concrete_validation_passes(c, cs[agent])
    && c_new.clock == (c.clock + 1) as nat
    && c_new.last_write == concrete_last_write_after_commit(c.last_write, write_set, c_new.clock)
    && c_new.store == concrete_store_after_commit(c.store, write_set, write_values)
    && c_new.trace == c.trace.push(ConcreteDefaultSiOpRecord {
        agent: agent,
        read_set: cs[agent].read_values.dom(),
        read_values: cs[agent].read_values,
        read_time: cs[agent].read_time,
        write_set: write_set,
        write_values: write_values,
        write_time: c_new.clock,
    })
    && *cs_new == cs.remove(agent)
}

// Bypass commit: empty writes, no validation, append empty record.
pub open spec fn concrete_default_si_commit_bypass_step(
    c: &ConcreteDefaultSiInner,
    cs: &CallerSnapshotMap,
    agent: ConcreteAgentId,
    c_new: &ConcreteDefaultSiInner,
    cs_new: &CallerSnapshotMap,
) -> bool {
    cs.contains_key(agent)
    && c_new.clock == (c.clock + 1) as nat
    && c_new.last_write == c.last_write
    && c_new.store == c.store
    && c_new.trace == c.trace.push(ConcreteDefaultSiOpRecord {
        agent: agent,
        read_set: cs[agent].read_values.dom(),
        read_values: cs[agent].read_values,
        read_time: cs[agent].read_time,
        write_set: Set::<ConcreteCellId>::empty(),
        write_values: Map::<ConcreteCellId, ConcreteValue>::empty(),
        write_time: c_new.clock,
    })
    && *cs_new == cs.remove(agent)
}

// Abort: validation failed on a non-empty write_set commit attempt.
pub open spec fn concrete_default_si_commit_abort_step(
    c: &ConcreteDefaultSiInner,
    cs: &CallerSnapshotMap,
    agent: ConcreteAgentId,
    c_new: &ConcreteDefaultSiInner,
    cs_new: &CallerSnapshotMap,
) -> bool {
    cs.contains_key(agent)
    && !concrete_validation_passes(c, cs[agent])
    && c_new.store == c.store
    && c_new.last_write == c.last_write
    && c_new.clock == c.clock
    && c_new.trace == c.trace
    && *cs_new == cs.remove(agent)
}

// =====================================================================
// Section 4: Abstract default-SI state (mirroring lib_default_si.rs)
// =====================================================================

pub struct AbstractOpRecord {
    pub agent: AbstractAgentId,
    pub read_set: Set<AbstractCellId>,
    pub read_values: Map<AbstractCellId, AbstractValue>,
    pub read_time: AbstractTime,
    pub write_set: Set<AbstractCellId>,
    pub write_values: Map<AbstractCellId, AbstractValue>,
    pub write_time: AbstractTime,
}

pub struct AbstractPendingSnapshot {
    pub read_time: AbstractTime,
    pub read_values: Map<AbstractCellId, AbstractValue>,
}

pub struct AbstractDefaultSiState {
    pub store: Map<AbstractCellId, AbstractValue>,
    pub last_write: Map<AbstractCellId, AbstractTime>,
    pub pending: Map<AbstractAgentId, AbstractPendingSnapshot>,
    pub clock: AbstractTime,
    pub trace: Seq<AbstractOpRecord>,
}

pub open spec fn init_abstract_default_si() -> AbstractDefaultSiState {
    AbstractDefaultSiState {
        store: Map::<AbstractCellId, AbstractValue>::empty(),
        last_write: Map::<AbstractCellId, AbstractTime>::empty(),
        pending: Map::<AbstractAgentId, AbstractPendingSnapshot>::empty(),
        clock: 0,
        trace: Seq::<AbstractOpRecord>::empty(),
    }
}

pub open spec fn abstract_last_write_of(s: &AbstractDefaultSiState, c: AbstractCellId) -> AbstractTime {
    if s.last_write.contains_key(c) { s.last_write[c] } else { 0 }
}

pub open spec fn abstract_validation_passes(s: &AbstractDefaultSiState, ps: AbstractPendingSnapshot) -> bool {
    forall |c: AbstractCellId|
        #[trigger] ps.read_values.contains_key(c)
        ==> abstract_last_write_of(s, c) <= ps.read_time
}

pub open spec fn abstract_store_after_commit(
    base: Map<AbstractCellId, AbstractValue>,
    write_set: Set<AbstractCellId>,
    write_values: Map<AbstractCellId, AbstractValue>,
) -> Map<AbstractCellId, AbstractValue> {
    Map::new(
        |c: AbstractCellId| base.contains_key(c) || write_set.contains(c),
        |c: AbstractCellId| if write_set.contains(c) && write_values.contains_key(c) {
                                write_values[c]
                            } else if base.contains_key(c) {
                                base[c]
                            } else {
                                abs_null_value()
                            },
    )
}

pub open spec fn abstract_last_write_after_commit(
    base: Map<AbstractCellId, AbstractTime>,
    write_set: Set<AbstractCellId>,
    new_clock: AbstractTime,
) -> Map<AbstractCellId, AbstractTime> {
    Map::new(
        |c: AbstractCellId| base.contains_key(c) || write_set.contains(c),
        |c: AbstractCellId| if write_set.contains(c) { new_clock }
                            else if base.contains_key(c) { base[c] }
                            else { 0 },
    )
}

pub open spec fn snapshot_built_abs(
    s_store: Map<AbstractCellId, AbstractValue>,
    cells: Seq<AbstractCellId>,
) -> Map<AbstractCellId, AbstractValue>
    decreases cells.len()
{
    if cells.len() == 0 {
        Map::<AbstractCellId, AbstractValue>::empty()
    } else {
        snapshot_built_abs(s_store, cells.drop_last()).insert(
            cells.last(),
            if s_store.contains_key(cells.last()) { s_store[cells.last()] }
            else { abs_null_value() },
        )
    }
}

// --- Abstract default-SI transitions ---

pub open spec fn abstract_default_si_begin_step(
    s: &AbstractDefaultSiState,
    agent: AbstractAgentId,
    cells: Seq<AbstractCellId>,
    s_new: &AbstractDefaultSiState,
) -> bool {
    !s.pending.contains_key(agent)
    && s_new.store == s.store
    && s_new.last_write == s.last_write
    && s_new.clock == s.clock
    && s_new.trace == s.trace
    && s_new.pending == s.pending.insert(
        agent,
        AbstractPendingSnapshot {
            read_time: s.clock,
            read_values: snapshot_built_abs(s.store, cells),
        },
    )
}

pub open spec fn abstract_default_si_commit_validated_step(
    s: &AbstractDefaultSiState,
    agent: AbstractAgentId,
    write_set: Set<AbstractCellId>,
    write_values: Map<AbstractCellId, AbstractValue>,
    s_new: &AbstractDefaultSiState,
) -> bool {
    s.pending.contains_key(agent)
    && !write_set.is_empty()
    && write_set.finite()
    && write_set.subset_of(write_values.dom())
    && abstract_validation_passes(s, s.pending[agent])
    && s_new.clock == s.clock + 1
    && s_new.last_write == abstract_last_write_after_commit(s.last_write, write_set, s_new.clock)
    && s_new.store == abstract_store_after_commit(s.store, write_set, write_values)
    && s_new.pending == s.pending.remove(agent)
    && s_new.trace == s.trace.push(AbstractOpRecord {
        agent: agent,
        read_set: s.pending[agent].read_values.dom(),
        read_values: s.pending[agent].read_values,
        read_time: s.pending[agent].read_time,
        write_set: write_set,
        write_values: write_values,
        write_time: s_new.clock,
    })
}

pub open spec fn abstract_default_si_commit_bypass_step(
    s: &AbstractDefaultSiState,
    agent: AbstractAgentId,
    s_new: &AbstractDefaultSiState,
) -> bool {
    s.pending.contains_key(agent)
    && s_new.clock == s.clock + 1
    && s_new.last_write == s.last_write
    && s_new.store == s.store
    && s_new.pending == s.pending.remove(agent)
    && s_new.trace == s.trace.push(AbstractOpRecord {
        agent: agent,
        read_set: s.pending[agent].read_values.dom(),
        read_values: s.pending[agent].read_values,
        read_time: s.pending[agent].read_time,
        write_set: Set::<AbstractCellId>::empty(),
        write_values: Map::<AbstractCellId, AbstractValue>::empty(),
        write_time: s_new.clock,
    })
}

pub open spec fn abstract_default_si_commit_abort_step(
    s: &AbstractDefaultSiState,
    agent: AbstractAgentId,
    s_new: &AbstractDefaultSiState,
) -> bool {
    s.pending.contains_key(agent)
    && !abstract_validation_passes(s, s.pending[agent])
    && s_new.store == s.store
    && s_new.last_write == s.last_write
    && s_new.clock == s.clock
    && s_new.trace == s.trace
    && s_new.pending == s.pending.remove(agent)
}

// =====================================================================
// Section 5: Abstraction function
// =====================================================================

pub open spec fn abstract_data(d: Map<ConcreteCellId, ConcreteValue>)
    -> Map<AbstractCellId, AbstractValue>
{
    Map::new(
        |c: AbstractCellId| exists |cc: ConcreteCellId|
            #[trigger] d.contains_key(cc) && cell_alpha(cc) == c,
        |c: AbstractCellId| {
            let cc = choose |cc: ConcreteCellId|
                #[trigger] d.contains_key(cc) && cell_alpha(cc) == c;
            value_alpha(d[cc])
        },
    )
}

pub open spec fn abstract_last_write_map(lw: Map<ConcreteCellId, ConcreteTime>)
    -> Map<AbstractCellId, AbstractTime>
{
    Map::new(
        |c: AbstractCellId| exists |cc: ConcreteCellId|
            #[trigger] lw.contains_key(cc) && cell_alpha(cc) == c,
        |c: AbstractCellId| {
            let cc = choose |cc: ConcreteCellId|
                #[trigger] lw.contains_key(cc) && cell_alpha(cc) == c;
            lw[cc] as int
        },
    )
}

pub open spec fn abstract_pending(cs: CallerSnapshotMap)
    -> Map<AbstractAgentId, AbstractPendingSnapshot>
{
    Map::new(
        |a: AbstractAgentId| exists |ca: ConcreteAgentId|
            #[trigger] cs.contains_key(ca) && agent_alpha(ca) == a,
        |a: AbstractAgentId| {
            let ca = choose |ca: ConcreteAgentId|
                #[trigger] cs.contains_key(ca) && agent_alpha(ca) == a;
            AbstractPendingSnapshot {
                read_time: cs[ca].read_time as int,
                read_values: abstract_data(cs[ca].read_values),
            }
        },
    )
}

pub open spec fn abstract_default_si_record(r: ConcreteDefaultSiOpRecord) -> AbstractOpRecord {
    AbstractOpRecord {
        agent: agent_alpha(r.agent),
        read_set: r.read_set.map(|c: ConcreteCellId| cell_alpha(c)),
        read_values: abstract_data(r.read_values),
        read_time: r.read_time as int,
        write_set: r.write_set.map(|c: ConcreteCellId| cell_alpha(c)),
        write_values: abstract_data(r.write_values),
        write_time: r.write_time as int,
    }
}

pub open spec fn abstract_default_si_trace(t: Seq<ConcreteDefaultSiOpRecord>) -> Seq<AbstractOpRecord>
    decreases t.len()
{
    if t.len() == 0 {
        Seq::<AbstractOpRecord>::empty()
    } else {
        abstract_default_si_trace(t.drop_last()).push(abstract_default_si_record(t.last()))
    }
}

pub open spec fn abstract_of_default_si(c: ConcreteDefaultSiInner, cs: CallerSnapshotMap)
    -> AbstractDefaultSiState
{
    AbstractDefaultSiState {
        store: abstract_data(c.store),
        last_write: abstract_last_write_map(c.last_write),
        pending: abstract_pending(cs),
        clock: c.clock as int,
        trace: abstract_default_si_trace(c.trace),
    }
}

pub open spec fn cells_alpha(cells: Seq<ConcreteCellId>) -> Seq<AbstractCellId> {
    cells.map_values(|c: ConcreteCellId| cell_alpha(c))
}

pub open spec fn abstract_writes(w: Map<ConcreteCellId, ConcreteValue>)
    -> Map<AbstractCellId, AbstractValue>
{
    abstract_data(w)
}

// =====================================================================
// Section 6: Init correspondence
// =====================================================================

pub proof fn lemma_init_correspondence_default_si()
    ensures abstract_of_default_si(init_concrete_default_si(),
                                   Map::<ConcreteAgentId, CallerSnapshot>::empty())
        == init_abstract_default_si()
{
    let c = init_concrete_default_si();
    let cs = Map::<ConcreteAgentId, CallerSnapshot>::empty();
    let a_act = abstract_of_default_si(c, cs);
    let a_exp = init_abstract_default_si();

    assert(a_act.store.dom() =~= Set::<AbstractCellId>::empty()) by {
        assert forall |k: AbstractCellId| !#[trigger] a_act.store.dom().contains(k) by {
            if a_act.store.dom().contains(k) {
                let cc = choose |cc: ConcreteCellId|
                    #[trigger] c.store.contains_key(cc) && cell_alpha(cc) == k;
                assert(c.store.contains_key(cc));
                assert(false);
            }
        };
    };
    assert(a_act.store =~= a_exp.store);

    assert(a_act.last_write.dom() =~= Set::<AbstractCellId>::empty()) by {
        assert forall |k: AbstractCellId| !#[trigger] a_act.last_write.dom().contains(k) by {
            if a_act.last_write.dom().contains(k) {
                let cc = choose |cc: ConcreteCellId|
                    #[trigger] c.last_write.contains_key(cc) && cell_alpha(cc) == k;
                assert(c.last_write.contains_key(cc));
                assert(false);
            }
        };
    };
    assert(a_act.last_write =~= a_exp.last_write);

    assert(a_act.pending.dom() =~= Set::<AbstractAgentId>::empty()) by {
        assert forall |k: AbstractAgentId| !#[trigger] a_act.pending.dom().contains(k) by {
            if a_act.pending.dom().contains(k) {
                let ca = choose |ca: ConcreteAgentId|
                    #[trigger] cs.contains_key(ca) && agent_alpha(ca) == k;
                assert(cs.contains_key(ca));
                assert(false);
            }
        };
    };
    assert(a_act.pending =~= a_exp.pending);

    assert(a_act.trace.len() == 0);
    assert(a_act.trace =~= Seq::<AbstractOpRecord>::empty());
    assert(a_act.clock == 0);
    assert(a_act == a_exp);
}

// =====================================================================
// Section 7: Map-insert/remove commutativity helpers (parallel to SSI)
// =====================================================================

pub proof fn lemma_abstract_data_insert(
    base: Map<ConcreteCellId, ConcreteValue>,
    k: ConcreteCellId,
    v: ConcreteValue,
)
    ensures abstract_data(base.insert(k, v))
        == abstract_data(base).insert(cell_alpha(k), value_alpha(v))
{
    broadcast use axiom_string_to_int_injective;

    let lhs = abstract_data(base.insert(k, v));
    let rhs = abstract_data(base).insert(cell_alpha(k), value_alpha(v));
    let bplus = base.insert(k, v);

    assert(lhs.dom() =~= rhs.dom()) by {
        assert forall |x: AbstractCellId| lhs.dom().contains(x) implies rhs.dom().contains(x) by {
            let cc = choose |cc: ConcreteCellId|
                #[trigger] bplus.contains_key(cc) && cell_alpha(cc) == x;
            if cc == k {
                assert(x == cell_alpha(k));
            } else {
                assert(base.contains_key(cc));
                assert(abstract_data(base).dom().contains(x)) by {
                    assert(exists |cc2: ConcreteCellId|
                        #[trigger] base.contains_key(cc2) && cell_alpha(cc2) == x);
                };
            }
        };
        assert forall |x: AbstractCellId| rhs.dom().contains(x) implies lhs.dom().contains(x) by {
            if x == cell_alpha(k) {
                assert(bplus.contains_key(k));
                assert(cell_alpha(k) == x);
            } else {
                assert(abstract_data(base).dom().contains(x));
                let cc = choose |cc: ConcreteCellId|
                    #[trigger] base.contains_key(cc) && cell_alpha(cc) == x;
                assert(bplus.contains_key(cc));
            }
        };
    };

    assert forall |x: AbstractCellId| lhs.dom().contains(x) implies lhs[x] == rhs[x] by {
        let cc = choose |cc: ConcreteCellId|
            #[trigger] bplus.contains_key(cc) && cell_alpha(cc) == x;
        if x == cell_alpha(k) {
            assert(cell_alpha(cc) == cell_alpha(k));
            assert(cc == k);
            assert(bplus[cc] == v);
        } else {
            assert(cc != k);
            assert(base.contains_key(cc));
            assert(bplus[cc] == base[cc]);
            let cc2 = choose |cc2: ConcreteCellId|
                #[trigger] base.contains_key(cc2) && cell_alpha(cc2) == x;
            assert(cell_alpha(cc) == cell_alpha(cc2));
            assert(cc == cc2);
        }
    };

    assert(lhs =~= rhs);
}

pub proof fn lemma_abstract_pending_insert(
    base: CallerSnapshotMap,
    a: ConcreteAgentId,
    snap: CallerSnapshot,
)
    ensures abstract_pending(base.insert(a, snap))
        == abstract_pending(base).insert(
            agent_alpha(a),
            AbstractPendingSnapshot {
                read_time: snap.read_time as int,
                read_values: abstract_data(snap.read_values),
            },
        )
{
    broadcast use axiom_string_to_int_injective;

    let lhs = abstract_pending(base.insert(a, snap));
    let rhs = abstract_pending(base).insert(
        agent_alpha(a),
        AbstractPendingSnapshot {
            read_time: snap.read_time as int,
            read_values: abstract_data(snap.read_values),
        },
    );
    let bplus = base.insert(a, snap);

    assert(lhs.dom() =~= rhs.dom()) by {
        assert forall |x: AbstractAgentId| lhs.dom().contains(x) implies rhs.dom().contains(x) by {
            let ca = choose |ca: ConcreteAgentId|
                #[trigger] bplus.contains_key(ca) && agent_alpha(ca) == x;
            if ca == a {
                assert(x == agent_alpha(a));
            } else {
                assert(base.contains_key(ca));
                assert(abstract_pending(base).dom().contains(x)) by {
                    assert(exists |ca2: ConcreteAgentId|
                        #[trigger] base.contains_key(ca2) && agent_alpha(ca2) == x);
                };
            }
        };
        assert forall |x: AbstractAgentId| rhs.dom().contains(x) implies lhs.dom().contains(x) by {
            if x == agent_alpha(a) {
                assert(bplus.contains_key(a));
                assert(agent_alpha(a) == x);
            } else {
                assert(abstract_pending(base).dom().contains(x));
                let ca = choose |ca: ConcreteAgentId|
                    #[trigger] base.contains_key(ca) && agent_alpha(ca) == x;
                assert(bplus.contains_key(ca));
            }
        };
    };

    assert forall |x: AbstractAgentId| lhs.dom().contains(x) implies lhs[x] == rhs[x] by {
        let ca = choose |ca: ConcreteAgentId|
            #[trigger] bplus.contains_key(ca) && agent_alpha(ca) == x;
        if x == agent_alpha(a) {
            assert(ca == a);
            assert(bplus[ca] == snap);
        } else {
            assert(ca != a);
            assert(base.contains_key(ca));
            assert(bplus[ca] == base[ca]);
            let ca2 = choose |ca2: ConcreteAgentId|
                #[trigger] base.contains_key(ca2) && agent_alpha(ca2) == x;
            assert(ca == ca2);
        }
    };

    assert(lhs =~= rhs);
}

pub proof fn lemma_abstract_pending_remove(
    base: CallerSnapshotMap,
    a: ConcreteAgentId,
)
    ensures abstract_pending(base.remove(a))
        == abstract_pending(base).remove(agent_alpha(a))
{
    broadcast use axiom_string_to_int_injective;

    let lhs = abstract_pending(base.remove(a));
    let rhs = abstract_pending(base).remove(agent_alpha(a));
    let bminus = base.remove(a);

    assert(lhs.dom() =~= rhs.dom()) by {
        assert forall |x: AbstractAgentId| lhs.dom().contains(x) implies rhs.dom().contains(x) by {
            let ca = choose |ca: ConcreteAgentId|
                #[trigger] bminus.contains_key(ca) && agent_alpha(ca) == x;
            assert(ca != a);
            assert(base.contains_key(ca));
            assert(abstract_pending(base).dom().contains(x)) by {
                assert(exists |ca2: ConcreteAgentId|
                    #[trigger] base.contains_key(ca2) && agent_alpha(ca2) == x);
            };
            assert(x != agent_alpha(a)) by {
                if x == agent_alpha(a) {
                    assert(agent_alpha(ca) == agent_alpha(a));
                    assert(ca == a);
                    assert(false);
                }
            };
        };
        assert forall |x: AbstractAgentId| rhs.dom().contains(x) implies lhs.dom().contains(x) by {
            assert(abstract_pending(base).dom().contains(x));
            assert(x != agent_alpha(a));
            let ca = choose |ca: ConcreteAgentId|
                #[trigger] base.contains_key(ca) && agent_alpha(ca) == x;
            assert(ca != a) by {
                if ca == a {
                    assert(agent_alpha(a) == x);
                    assert(false);
                }
            };
            assert(bminus.contains_key(ca));
        };
    };

    assert forall |x: AbstractAgentId| lhs.dom().contains(x) implies lhs[x] == rhs[x] by {
        let ca = choose |ca: ConcreteAgentId|
            #[trigger] bminus.contains_key(ca) && agent_alpha(ca) == x;
        assert(ca != a);
        assert(base.contains_key(ca));
        assert(bminus[ca] == base[ca]);
        let ca2 = choose |ca2: ConcreteAgentId|
            #[trigger] base.contains_key(ca2) && agent_alpha(ca2) == x;
        assert(ca == ca2);
    };

    assert(lhs =~= rhs);
}

// =====================================================================
// Section 8: Trace push commutativity
// =====================================================================

pub proof fn lemma_abstract_default_si_trace_push(
    t: Seq<ConcreteDefaultSiOpRecord>,
    r: ConcreteDefaultSiOpRecord,
)
    ensures abstract_default_si_trace(t.push(r))
        == abstract_default_si_trace(t).push(abstract_default_si_record(r))
{
    let pushed = t.push(r);
    assert(pushed.len() == t.len() + 1);
    assert(pushed.len() > 0);
    assert(pushed.drop_last() =~= t);
    assert(pushed.last() == r);
}

// =====================================================================
// Section 9: Snapshot commutativity
// =====================================================================

pub proof fn lemma_snapshot_built_abs_push(
    s_store: Map<AbstractCellId, AbstractValue>,
    cells_pre: Seq<AbstractCellId>,
    last_cell: AbstractCellId,
)
    ensures snapshot_built_abs(s_store, cells_pre.push(last_cell))
        == snapshot_built_abs(s_store, cells_pre).insert(
            last_cell,
            if s_store.contains_key(last_cell) { s_store[last_cell] }
            else { abs_null_value() },
        )
{
    let pushed = cells_pre.push(last_cell);
    assert(pushed.len() == cells_pre.len() + 1);
    assert(pushed.len() > 0);
    assert(pushed.drop_last() =~= cells_pre);
    assert(pushed.last() == last_cell);
}

pub proof fn lemma_snapshot_commutes(
    data: Map<ConcreteCellId, ConcreteValue>,
    cells: Seq<ConcreteCellId>,
)
    ensures abstract_data(snapshot_concrete(data, cells))
        == snapshot_built_abs(abstract_data(data), cells_alpha(cells))
    decreases cells.len()
{
    broadcast use axiom_string_to_int_injective;
    broadcast use axiom_null_sentinel;

    if cells.len() == 0 {
        assert(cells_alpha(cells).len() == 0);
        assert(snapshot_concrete(data, cells) == Map::<ConcreteCellId, ConcreteValue>::empty());
        assert(abstract_data(snapshot_concrete(data, cells)).dom()
               =~= Set::<AbstractCellId>::empty()) by {
            assert forall |x: AbstractCellId|
                !#[trigger] abstract_data(snapshot_concrete(data, cells)).dom().contains(x) by {
                if abstract_data(snapshot_concrete(data, cells)).dom().contains(x) {
                    let cc = choose |cc: ConcreteCellId|
                        #[trigger] snapshot_concrete(data, cells).contains_key(cc)
                        && cell_alpha(cc) == x;
                    assert(snapshot_concrete(data, cells).contains_key(cc));
                    assert(false);
                }
            };
        };
        assert(abstract_data(snapshot_concrete(data, cells))
               =~= Map::<AbstractCellId, AbstractValue>::empty());
    } else {
        let prefix = cells.drop_last();
        let last = cells.last();
        lemma_snapshot_commutes(data, prefix);

        let inner_concrete = snapshot_concrete(data, prefix);

        let val_c = if data.contains_key(last) { data[last] }
                    else { null_sentinel_string() };
        assert(snapshot_concrete(data, cells) == inner_concrete.insert(last, val_c));

        lemma_abstract_data_insert(inner_concrete, last, val_c);

        let pushed = cells_alpha(prefix).push(cell_alpha(last));
        assert(cells_alpha(cells).len() == cells.len());
        assert(pushed.len() == prefix.len() + 1);
        assert(cells.len() == prefix.len() + 1);
        assert forall |i: int| 0 <= i < cells_alpha(cells).len()
            implies cells_alpha(cells)[i] == pushed[i] by {
            if i < prefix.len() {
                assert(cells[i] == prefix[i]);
            } else {
                assert(i == prefix.len() as int);
                assert(cells[i] == last);
            }
        };
        assert(cells_alpha(cells) =~= pushed);

        lemma_snapshot_built_abs_push(abstract_data(data), cells_alpha(prefix), cell_alpha(last));

        if data.contains_key(last) {
            assert(abstract_data(data).dom().contains(cell_alpha(last))) by {
                assert(data.contains_key(last) && cell_alpha(last) == cell_alpha(last));
            };
            let cc = choose |cc: ConcreteCellId|
                #[trigger] data.contains_key(cc) && cell_alpha(cc) == cell_alpha(last);
            assert(cc == last);
        } else {
            assert(!abstract_data(data).dom().contains(cell_alpha(last))) by {
                if abstract_data(data).dom().contains(cell_alpha(last)) {
                    let cc = choose |cc: ConcreteCellId|
                        #[trigger] data.contains_key(cc) && cell_alpha(cc) == cell_alpha(last);
                    assert(cc == last);
                    assert(false);
                }
            };
            assert(value_alpha(val_c) == abs_null_value());
        }

        assert(snapshot_built_abs(abstract_data(data), cells_alpha(cells))
               == snapshot_built_abs(abstract_data(data), pushed));
    }
}

// =====================================================================
// Section 10: Validation passes lift + commit helpers
// =====================================================================

pub proof fn lemma_validation_passes_corresponds(
    c: &ConcreteDefaultSiInner,
    cs: &CallerSnapshotMap,
    agent: ConcreteAgentId,
)
    requires
        cs.contains_key(agent),
        concrete_validation_passes(c, cs[agent]),
    ensures ({
        let s = abstract_of_default_si(*c, *cs);
        let agent_a = agent_alpha(agent);
        s.pending.contains_key(agent_a) && abstract_validation_passes(&s, s.pending[agent_a])
    })
{
    broadcast use axiom_string_to_int_injective;

    let s = abstract_of_default_si(*c, *cs);
    let agent_a = agent_alpha(agent);

    assert(s.pending.dom().contains(agent_a)) by {
        assert(cs.contains_key(agent) && agent_alpha(agent) == agent_a);
    };

    let ca = choose |ca: ConcreteAgentId|
        #[trigger] cs.contains_key(ca) && agent_alpha(ca) == agent_a;
    assert(ca == agent);

    assert forall |x: AbstractCellId|
        #[trigger] s.pending[agent_a].read_values.contains_key(x)
        implies abstract_last_write_of(&s, x) <= s.pending[agent_a].read_time by {
        let cc = choose |cc: ConcreteCellId|
            #[trigger] cs[agent].read_values.contains_key(cc) && cell_alpha(cc) == x;
        assert(concrete_last_write_of(c, cc) <= cs[agent].read_time);
        if c.last_write.contains_key(cc) {
            assert(s.last_write.dom().contains(cell_alpha(cc))) by {
                assert(c.last_write.contains_key(cc) && cell_alpha(cc) == cell_alpha(cc));
            };
            let cc2 = choose |cc2: ConcreteCellId|
                #[trigger] c.last_write.contains_key(cc2) && cell_alpha(cc2) == x;
            assert(cell_alpha(cc) == x);
            assert(cc == cc2);
        } else {
            assert(!s.last_write.dom().contains(x)) by {
                if s.last_write.dom().contains(x) {
                    let cc2 = choose |cc2: ConcreteCellId|
                        #[trigger] c.last_write.contains_key(cc2) && cell_alpha(cc2) == x;
                    assert(cell_alpha(cc) == cell_alpha(cc2));
                    assert(cc == cc2);
                    assert(false);
                }
            };
        }
    };
}

pub proof fn lemma_store_after_commit_commutes(
    base: Map<ConcreteCellId, ConcreteValue>,
    write_set: Set<ConcreteCellId>,
    write_values: Map<ConcreteCellId, ConcreteValue>,
)
    requires
        write_set.finite(),
        write_set.subset_of(write_values.dom()),
    ensures abstract_data(concrete_store_after_commit(base, write_set, write_values))
        == abstract_store_after_commit(
            abstract_data(base),
            write_set.map(|c: ConcreteCellId| cell_alpha(c)),
            abstract_data(write_values),
        )
{
    broadcast use axiom_string_to_int_injective;
    broadcast use axiom_null_sentinel;

    let lhs = abstract_data(concrete_store_after_commit(base, write_set, write_values));
    let rhs = abstract_store_after_commit(
        abstract_data(base),
        write_set.map(|c: ConcreteCellId| cell_alpha(c)),
        abstract_data(write_values),
    );
    let csc = concrete_store_after_commit(base, write_set, write_values);
    let ws_a = write_set.map(|c: ConcreteCellId| cell_alpha(c));

    assert(lhs.dom() =~= rhs.dom()) by {
        assert forall |x: AbstractCellId| lhs.dom().contains(x) implies rhs.dom().contains(x) by {
            let cc = choose |cc: ConcreteCellId|
                #[trigger] csc.contains_key(cc) && cell_alpha(cc) == x;
            assert(base.contains_key(cc) || write_set.contains(cc));
            if base.contains_key(cc) {
                assert(abstract_data(base).dom().contains(x)) by {
                    assert(exists |cc2: ConcreteCellId|
                        #[trigger] base.contains_key(cc2) && cell_alpha(cc2) == x);
                };
            } else {
                assert(write_set.contains(cc));
                assert(ws_a.contains(cell_alpha(cc)));
            }
        };
        assert forall |x: AbstractCellId| rhs.dom().contains(x) implies lhs.dom().contains(x) by {
            if abstract_data(base).dom().contains(x) {
                let cc = choose |cc: ConcreteCellId|
                    #[trigger] base.contains_key(cc) && cell_alpha(cc) == x;
                assert(csc.contains_key(cc));
            } else {
                assert(ws_a.contains(x));
                let cc = choose |cc: ConcreteCellId|
                    write_set.contains(cc) && cell_alpha(cc) == x;
                assert(csc.contains_key(cc));
            }
        };
    };

    assert forall |x: AbstractCellId| lhs.dom().contains(x) implies lhs[x] == rhs[x] by {
        let cc = choose |cc: ConcreteCellId|
            #[trigger] csc.contains_key(cc) && cell_alpha(cc) == x;
        if write_set.contains(cc) && write_values.contains_key(cc) {
            assert(csc[cc] == write_values[cc]);
            assert(ws_a.contains(x));
            assert(abstract_data(write_values).dom().contains(x)) by {
                assert(write_values.contains_key(cc) && cell_alpha(cc) == x);
            };
            let cw = choose |cw: ConcreteCellId|
                #[trigger] write_values.contains_key(cw) && cell_alpha(cw) == x;
            assert(cw == cc);
        } else if base.contains_key(cc) {
            assert(!write_set.contains(cc) || !write_values.contains_key(cc));
            assert(!write_set.contains(cc)) by {
                if write_set.contains(cc) {
                    assert(write_values.contains_key(cc));
                    assert(false);
                }
            };
            assert(csc[cc] == base[cc]);
            assert(!ws_a.contains(x)) by {
                if ws_a.contains(x) {
                    let cw = choose |cw: ConcreteCellId|
                        write_set.contains(cw) && cell_alpha(cw) == x;
                    assert(cell_alpha(cw) == cell_alpha(cc));
                    assert(cw == cc);
                    assert(false);
                }
            };
            let cb = choose |cb: ConcreteCellId|
                #[trigger] base.contains_key(cb) && cell_alpha(cb) == x;
            assert(cb == cc);
        }
    };

    assert(lhs =~= rhs);
}

pub proof fn lemma_last_write_after_commit_commutes(
    base: Map<ConcreteCellId, ConcreteTime>,
    write_set: Set<ConcreteCellId>,
    new_clock: ConcreteTime,
)
    requires write_set.finite()
    ensures abstract_last_write_map(concrete_last_write_after_commit(base, write_set, new_clock))
        == abstract_last_write_after_commit(
            abstract_last_write_map(base),
            write_set.map(|c: ConcreteCellId| cell_alpha(c)),
            new_clock as int,
        )
{
    broadcast use axiom_string_to_int_injective;

    let lhs = abstract_last_write_map(concrete_last_write_after_commit(base, write_set, new_clock));
    let rhs = abstract_last_write_after_commit(
        abstract_last_write_map(base),
        write_set.map(|c: ConcreteCellId| cell_alpha(c)),
        new_clock as int,
    );
    let clw = concrete_last_write_after_commit(base, write_set, new_clock);
    let ws_a = write_set.map(|c: ConcreteCellId| cell_alpha(c));

    assert(lhs.dom() =~= rhs.dom()) by {
        assert forall |x: AbstractCellId| lhs.dom().contains(x) implies rhs.dom().contains(x) by {
            let cc = choose |cc: ConcreteCellId|
                #[trigger] clw.contains_key(cc) && cell_alpha(cc) == x;
            assert(base.contains_key(cc) || write_set.contains(cc));
            if base.contains_key(cc) {
                assert(abstract_last_write_map(base).dom().contains(x)) by {
                    assert(exists |cc2: ConcreteCellId|
                        #[trigger] base.contains_key(cc2) && cell_alpha(cc2) == x);
                };
            } else {
                assert(write_set.contains(cc));
                assert(ws_a.contains(cell_alpha(cc)));
            }
        };
        assert forall |x: AbstractCellId| rhs.dom().contains(x) implies lhs.dom().contains(x) by {
            if abstract_last_write_map(base).dom().contains(x) {
                let cc = choose |cc: ConcreteCellId|
                    #[trigger] base.contains_key(cc) && cell_alpha(cc) == x;
                assert(clw.contains_key(cc));
            } else {
                assert(ws_a.contains(x));
                let cc = choose |cc: ConcreteCellId|
                    write_set.contains(cc) && cell_alpha(cc) == x;
                assert(clw.contains_key(cc));
            }
        };
    };

    assert forall |x: AbstractCellId| lhs.dom().contains(x) implies lhs[x] == rhs[x] by {
        let cc = choose |cc: ConcreteCellId|
            #[trigger] clw.contains_key(cc) && cell_alpha(cc) == x;
        if write_set.contains(cc) {
            assert(clw[cc] == new_clock);
            assert(ws_a.contains(x));
        } else {
            assert(base.contains_key(cc));
            assert(clw[cc] == base[cc]);
            assert(!ws_a.contains(x)) by {
                if ws_a.contains(x) {
                    let cw = choose |cw: ConcreteCellId|
                        write_set.contains(cw) && cell_alpha(cw) == x;
                    assert(cw == cc);
                    assert(false);
                }
            };
            let cb = choose |cb: ConcreteCellId|
                #[trigger] base.contains_key(cb) && cell_alpha(cb) == x;
            assert(cb == cc);
        }
    };

    assert(lhs =~= rhs);
}

// =====================================================================
// Section 11: Refinement lemmas (4: begin, validated, bypass, abort)
// =====================================================================

pub proof fn lemma_default_si_begin_refines(
    c: &ConcreteDefaultSiInner,
    cs: &CallerSnapshotMap,
    agent: ConcreteAgentId,
    cells: Seq<ConcreteCellId>,
    c_new: &ConcreteDefaultSiInner,
    cs_new: &CallerSnapshotMap,
)
    requires concrete_default_si_begin_step(c, cs, agent, cells, c_new, cs_new)
    ensures abstract_default_si_begin_step(
        &abstract_of_default_si(*c, *cs),
        agent_alpha(agent),
        cells_alpha(cells),
        &abstract_of_default_si(*c_new, *cs_new),
    )
{
    broadcast use axiom_string_to_int_injective;

    let s = abstract_of_default_si(*c, *cs);
    let s_new = abstract_of_default_si(*c_new, *cs_new);
    let agent_a = agent_alpha(agent);
    let cells_a = cells_alpha(cells);

    assert(s_new.store == s.store);
    assert(s_new.last_write == s.last_write);
    assert(s_new.clock == s.clock);
    assert(s_new.trace == s.trace);

    assert(!s.pending.dom().contains(agent_a)) by {
        if s.pending.dom().contains(agent_a) {
            let ca = choose |ca: ConcreteAgentId|
                #[trigger] cs.contains_key(ca) && agent_alpha(ca) == agent_a;
            assert(agent_alpha(ca) == agent_alpha(agent));
            assert(ca == agent);
            assert(cs.contains_key(agent));
            assert(false);
        }
    };

    let snap_c = CallerSnapshot {
        read_time: c.clock,
        read_values: snapshot_concrete(c.store, cells),
    };
    assert(*cs_new == cs.insert(agent, snap_c));

    lemma_abstract_pending_insert(*cs, agent, snap_c);
    lemma_snapshot_commutes(c.store, cells);

    assert(abstract_data(snap_c.read_values) == snapshot_built_abs(s.store, cells_a));
    assert(snap_c.read_time as int == s.clock);

    assert(s_new.pending == s.pending.insert(
        agent_a,
        AbstractPendingSnapshot {
            read_time: s.clock,
            read_values: snapshot_built_abs(s.store, cells_a),
        },
    ));
}

pub proof fn lemma_default_si_commit_validated_refines(
    c: &ConcreteDefaultSiInner,
    cs: &CallerSnapshotMap,
    agent: ConcreteAgentId,
    write_set: Set<ConcreteCellId>,
    write_values: Map<ConcreteCellId, ConcreteValue>,
    c_new: &ConcreteDefaultSiInner,
    cs_new: &CallerSnapshotMap,
)
    requires concrete_default_si_commit_validated_step(c, cs, agent, write_set, write_values, c_new, cs_new)
    ensures abstract_default_si_commit_validated_step(
        &abstract_of_default_si(*c, *cs),
        agent_alpha(agent),
        write_set.map(|c: ConcreteCellId| cell_alpha(c)),
        abstract_writes(write_values),
        &abstract_of_default_si(*c_new, *cs_new),
    )
{
    broadcast use axiom_string_to_int_injective;

    let s = abstract_of_default_si(*c, *cs);
    let s_new = abstract_of_default_si(*c_new, *cs_new);
    let agent_a = agent_alpha(agent);
    let write_set_a = write_set.map(|c: ConcreteCellId| cell_alpha(c));
    let write_kv = abstract_writes(write_values);

    lemma_set_map_preserves_finite(write_set, |c: ConcreteCellId| cell_alpha(c));

    assert(s.pending.dom().contains(agent_a)) by {
        assert(cs.contains_key(agent) && agent_alpha(agent) == agent_a);
    };

    // !write_set.is_empty() lifts to !write_set_a.is_empty()
    assert(!write_set_a.is_empty()) by {
        let cw = choose |cw: ConcreteCellId| write_set.contains(cw);
        assert(write_set_a.contains(cell_alpha(cw)));
    };

    assert(write_set.finite());
    assert(write_set_a.finite());

    assert(write_set_a.subset_of(write_kv.dom())) by {
        assert forall |x: AbstractCellId| write_set_a.contains(x)
            implies write_kv.dom().contains(x) by {
            let cw = choose |cw: ConcreteCellId|
                write_set.contains(cw) && cell_alpha(cw) == x;
            assert(write_values.contains_key(cw));
            assert(write_kv.dom().contains(x)) by {
                assert(write_values.contains_key(cw) && cell_alpha(cw) == x);
            };
        };
    };

    lemma_validation_passes_corresponds(c, cs, agent);

    assert(s_new.clock == s.clock + 1);

    lemma_last_write_after_commit_commutes(c.last_write, write_set, c_new.clock);
    assert(s_new.last_write == abstract_last_write_after_commit(
        s.last_write, write_set_a, s_new.clock,
    ));

    lemma_store_after_commit_commutes(c.store, write_set, write_values);
    assert(s_new.store == abstract_store_after_commit(s.store, write_set_a, write_kv));

    lemma_abstract_pending_remove(*cs, agent);
    assert(s_new.pending == s.pending.remove(agent_a));

    let record_c = ConcreteDefaultSiOpRecord {
        agent: agent,
        read_set: cs[agent].read_values.dom(),
        read_values: cs[agent].read_values,
        read_time: cs[agent].read_time,
        write_set: write_set,
        write_values: write_values,
        write_time: c_new.clock,
    };
    assert(c_new.trace == c.trace.push(record_c));
    lemma_abstract_default_si_trace_push(c.trace, record_c);

    let ca_pending = choose |ca: ConcreteAgentId|
        #[trigger] cs.contains_key(ca) && agent_alpha(ca) == agent_a;
    assert(ca_pending == agent);
    assert(s.pending[agent_a].read_values == abstract_data(cs[agent].read_values));
    assert(s.pending[agent_a].read_time == cs[agent].read_time as int);

    // read_set domain equality: abstract_record(record_c).read_set is
    // cs[agent].read_values.dom().map(cell_alpha), and the abstract spec
    // requires it to equal s.pending[agent_a].read_values.dom() which is
    // abstract_data(cs[agent].read_values).dom().
    let read_dom_a = cs[agent].read_values.dom().map(|cc: ConcreteCellId| cell_alpha(cc));
    assert(abstract_data(cs[agent].read_values).dom() =~= read_dom_a) by {
        assert forall |x: AbstractCellId|
            abstract_data(cs[agent].read_values).dom().contains(x)
            <==> read_dom_a.contains(x) by {
            if abstract_data(cs[agent].read_values).dom().contains(x) {
                let cc = choose |cc: ConcreteCellId|
                    #[trigger] cs[agent].read_values.contains_key(cc) && cell_alpha(cc) == x;
                assert(read_dom_a.contains(cell_alpha(cc)));
            }
            if read_dom_a.contains(x) {
                let cc = choose |cc: ConcreteCellId|
                    cs[agent].read_values.dom().contains(cc) && cell_alpha(cc) == x;
                assert(cs[agent].read_values.contains_key(cc));
            }
        };
    };
}

pub proof fn lemma_default_si_commit_bypass_refines(
    c: &ConcreteDefaultSiInner,
    cs: &CallerSnapshotMap,
    agent: ConcreteAgentId,
    c_new: &ConcreteDefaultSiInner,
    cs_new: &CallerSnapshotMap,
)
    requires concrete_default_si_commit_bypass_step(c, cs, agent, c_new, cs_new)
    ensures abstract_default_si_commit_bypass_step(
        &abstract_of_default_si(*c, *cs),
        agent_alpha(agent),
        &abstract_of_default_si(*c_new, *cs_new),
    )
{
    broadcast use axiom_string_to_int_injective;

    let s = abstract_of_default_si(*c, *cs);
    let s_new = abstract_of_default_si(*c_new, *cs_new);
    let agent_a = agent_alpha(agent);

    assert(s.pending.dom().contains(agent_a)) by {
        assert(cs.contains_key(agent) && agent_alpha(agent) == agent_a);
    };

    assert(s_new.store == s.store);
    assert(s_new.last_write == s.last_write);
    assert(s_new.clock == s.clock + 1);

    lemma_abstract_pending_remove(*cs, agent);
    assert(s_new.pending == s.pending.remove(agent_a));

    // Trace push of the empty-write record.
    let record_c = ConcreteDefaultSiOpRecord {
        agent: agent,
        read_set: cs[agent].read_values.dom(),
        read_values: cs[agent].read_values,
        read_time: cs[agent].read_time,
        write_set: Set::<ConcreteCellId>::empty(),
        write_values: Map::<ConcreteCellId, ConcreteValue>::empty(),
        write_time: c_new.clock,
    };
    assert(c_new.trace == c.trace.push(record_c));
    lemma_abstract_default_si_trace_push(c.trace, record_c);

    // abstract_default_si_record(record_c) has empty write_set/write_values
    // after the cell_alpha/value_alpha maps.
    assert(Set::<ConcreteCellId>::empty().map(|c: ConcreteCellId| cell_alpha(c))
           =~= Set::<AbstractCellId>::empty()) by {
        let mapped_empty = Set::<ConcreteCellId>::empty().map(|c: ConcreteCellId| cell_alpha(c));
        assert forall |x: AbstractCellId| !#[trigger] mapped_empty.contains(x) by {
            // No element of the empty set maps to anything.
            if mapped_empty.contains(x) {
                let cc = choose |cc: ConcreteCellId|
                    Set::<ConcreteCellId>::empty().contains(cc) && cell_alpha(cc) == x;
                assert(false);
            }
        };
    };
    assert(abstract_data(Map::<ConcreteCellId, ConcreteValue>::empty())
           =~= Map::<AbstractCellId, AbstractValue>::empty()) by {
        assert forall |x: AbstractCellId| !#[trigger]
            abstract_data(Map::<ConcreteCellId, ConcreteValue>::empty()).dom().contains(x) by {
            if abstract_data(Map::<ConcreteCellId, ConcreteValue>::empty()).dom().contains(x) {
                let cc = choose |cc: ConcreteCellId|
                    #[trigger] Map::<ConcreteCellId, ConcreteValue>::empty().contains_key(cc)
                    && cell_alpha(cc) == x;
                assert(false);
            }
        };
    };

    let ca_pending = choose |ca: ConcreteAgentId|
        #[trigger] cs.contains_key(ca) && agent_alpha(ca) == agent_a;
    assert(ca_pending == agent);
    assert(s.pending[agent_a].read_values == abstract_data(cs[agent].read_values));
    assert(s.pending[agent_a].read_time == cs[agent].read_time as int);

    // read_set domain equality (same as in commit_validated): needed
    // because abstract_record(record_c).read_set is
    // cs[agent].read_values.dom().map(cell_alpha) but the abstract spec's
    // record uses s.pending[agent_a].read_values.dom().
    let read_dom_a = cs[agent].read_values.dom().map(|cc: ConcreteCellId| cell_alpha(cc));
    assert(abstract_data(cs[agent].read_values).dom() =~= read_dom_a) by {
        assert forall |x: AbstractCellId|
            abstract_data(cs[agent].read_values).dom().contains(x)
            <==> read_dom_a.contains(x) by {
            if abstract_data(cs[agent].read_values).dom().contains(x) {
                let cc = choose |cc: ConcreteCellId|
                    #[trigger] cs[agent].read_values.contains_key(cc) && cell_alpha(cc) == x;
                assert(read_dom_a.contains(cell_alpha(cc)));
            }
            if read_dom_a.contains(x) {
                let cc = choose |cc: ConcreteCellId|
                    cs[agent].read_values.dom().contains(cc) && cell_alpha(cc) == x;
                assert(cs[agent].read_values.contains_key(cc));
            }
        };
    };
}

pub proof fn lemma_default_si_commit_abort_refines(
    c: &ConcreteDefaultSiInner,
    cs: &CallerSnapshotMap,
    agent: ConcreteAgentId,
    c_new: &ConcreteDefaultSiInner,
    cs_new: &CallerSnapshotMap,
)
    requires concrete_default_si_commit_abort_step(c, cs, agent, c_new, cs_new)
    ensures abstract_default_si_commit_abort_step(
        &abstract_of_default_si(*c, *cs),
        agent_alpha(agent),
        &abstract_of_default_si(*c_new, *cs_new),
    )
{
    broadcast use axiom_string_to_int_injective;

    let s = abstract_of_default_si(*c, *cs);
    let s_new = abstract_of_default_si(*c_new, *cs_new);
    let agent_a = agent_alpha(agent);

    assert(s_new.store == s.store);
    assert(s_new.last_write == s.last_write);
    assert(s_new.clock == s.clock);
    assert(s_new.trace == s.trace);

    assert(s.pending.dom().contains(agent_a)) by {
        assert(cs.contains_key(agent) && agent_alpha(agent) == agent_a);
    };

    lemma_abstract_pending_remove(*cs, agent);
    assert(s_new.pending == s.pending.remove(agent_a));

    let ca = choose |ca: ConcreteAgentId|
        #[trigger] cs.contains_key(ca) && agent_alpha(ca) == agent_a;
    assert(ca == agent);

    assert(!concrete_validation_passes(c, cs[agent]));
    let cc_witness = choose |cc: ConcreteCellId|
        cs[agent].read_values.contains_key(cc)
        && concrete_last_write_of(c, cc) > cs[agent].read_time;

    let x = cell_alpha(cc_witness);
    assert(s.pending[agent_a].read_values.dom().contains(x)) by {
        assert(cs[agent].read_values.contains_key(cc_witness) && cell_alpha(cc_witness) == x);
    };

    if c.last_write.contains_key(cc_witness) {
        assert(s.last_write.dom().contains(x)) by {
            assert(c.last_write.contains_key(cc_witness) && cell_alpha(cc_witness) == x);
        };
        let cc2 = choose |cc2: ConcreteCellId|
            #[trigger] c.last_write.contains_key(cc2) && cell_alpha(cc2) == x;
        assert(cc2 == cc_witness);
        assert(s.last_write[x] == c.last_write[cc_witness] as int);
    } else {
        assert(false);
    }

    assert(!abstract_validation_passes(&s, s.pending[agent_a]));
}

} // verus!