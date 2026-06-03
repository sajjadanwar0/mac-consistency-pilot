// =====================================================================
// Verus proof: Spec - executable runtime refinement (SSI, version-chain).
//
// COMPILE
//   verus --crate-type=lib src/lib_refinement_ssi_chain.rs
//
// MODEL
//   This refinement closes the gap left by lib_refinement_ssi.rs, which
//   refined against a (store, last_write) projection of the version-chain
//   implementation. Here the concrete state IS the literal version-chain
//   representation Map<CellId, Seq<(Time, Value)>>, matching the deployed
//   Rust runtime's BTreeMap<CellId, Vec<(Time, Value)>>.
//
//   The abstraction extracts the latest version per cell. Under the
//   chain-monotonicity invariant (every chain non-empty and times
//   strictly increasing), the latest version captures all
//   observationally-relevant state and the projection-level reasoning
//   transfers.
//
// SCORECARD (target)
//   Two foundational axioms (shared with all other refinement files):
//     - axiom_string_to_int_injective
//     - axiom_null_sentinel
//   Set::map finiteness preservation is a proven lemma, not an axiom.

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
// Section 2: Axioms (two foundational)
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
                        assert(s_rest.map(f).insert(f(x)).contains(y));
                    } else {
                        assert(s_rest.contains(z));
                        assert(s_rest.map(f).contains(y));
                    }
                }
                if s_rest.map(f).insert(f(x)).contains(y) {
                    if y == f(x) {
                        assert(s.contains(x) && f(x) == y);
                    } else {
                        assert(s_rest.map(f).contains(y));
                        let z = choose |z: A| #[trigger] s_rest.contains(z) && f(z) == y;
                        assert(s.contains(z));
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
// Section 3: Concrete SSI chain state (version chains)
// =====================================================================

pub struct ConcreteOpRecord {
    pub agent: ConcreteAgentId,
    pub read_set: Set<ConcreteCellId>,
    pub read_values: Map<ConcreteCellId, ConcreteValue>,
    pub read_time: ConcreteTime,
    pub write_set: Set<ConcreteCellId>,
    pub write_values: Map<ConcreteCellId, ConcreteValue>,
    pub write_time: ConcreteTime,
}

// Each cell maps to a Seq of (commit_time, value) pairs. The Rust
// runtime uses BTreeMap<CellId, Vec<(Time, Value)>>; this is the
// Verus-level model.
pub type VersionChain = Seq<(ConcreteTime, ConcreteValue)>;

pub struct ConcreteSsiChainInner {
    pub versions: Map<ConcreteCellId, VersionChain>,
    pub clock: ConcreteTime,
    pub trace: Seq<ConcreteOpRecord>,
}

pub open spec fn init_concrete_ssi_chain() -> ConcreteSsiChainInner {
    ConcreteSsiChainInner {
        versions: Map::<ConcreteCellId, VersionChain>::empty(),
        clock: 0,
        trace: Seq::<ConcreteOpRecord>::empty(),
    }
}

// Chain monotonicity invariant: for every cell present in versions,
// the chain is non-empty and times are strictly increasing.
pub open spec fn chain_monotonic(c: &ConcreteSsiChainInner) -> bool {
    forall |cc: ConcreteCellId|
        #[trigger] c.versions.contains_key(cc) ==>
            c.versions[cc].len() > 0 &&
            (forall |i: int, j: int|
                0 <= i < j < c.versions[cc].len() ==>
                    #[trigger] c.versions[cc][i].0 < #[trigger] c.versions[cc][j].0)
}

// Latest version time at a cell (assumes cell is in versions).
pub open spec fn chain_latest_time(c: &ConcreteSsiChainInner, cc: ConcreteCellId) -> ConcreteTime
    recommends c.versions.contains_key(cc),
{
    if c.versions.contains_key(cc) && c.versions[cc].len() > 0 {
        c.versions[cc][c.versions[cc].len() - 1].0
    } else {
        0
    }
}

pub open spec fn chain_latest_value(c: &ConcreteSsiChainInner, cc: ConcreteCellId) -> ConcreteValue
    recommends c.versions.contains_key(cc),
{
    if c.versions.contains_key(cc) && c.versions[cc].len() > 0 {
        c.versions[cc][c.versions[cc].len() - 1].1
    } else {
        null_sentinel_string()
    }
}

pub open spec fn concrete_last_write_of(c: &ConcreteSsiChainInner, cc: ConcreteCellId) -> ConcreteTime {
    if c.versions.contains_key(cc) { chain_latest_time(c, cc) } else { 0 }
}

pub struct CallerSnapshot {
    pub read_time: ConcreteTime,
    pub read_values: Map<ConcreteCellId, ConcreteValue>,
}

pub type CallerSnapshotMap = Map<ConcreteAgentId, CallerSnapshot>;

// Validation: under chain monotonicity, "no version with time > read_time"
// is equivalent to "latest time <= read_time".
pub open spec fn concrete_validation_passes(c: &ConcreteSsiChainInner, snap: CallerSnapshot) -> bool {
    forall |cc: ConcreteCellId|
        #[trigger] snap.read_values.contains_key(cc)
        ==> concrete_last_write_of(c, cc) <= snap.read_time
}

// Snapshot construction: read the latest value for each cell in the
// given list, or NULL if cell has no chain.
pub open spec fn snapshot_concrete(
    versions: Map<ConcreteCellId, VersionChain>,
    cells: Seq<ConcreteCellId>,
) -> Map<ConcreteCellId, ConcreteValue>
    decreases cells.len()
{
    if cells.len() == 0 {
        Map::<ConcreteCellId, ConcreteValue>::empty()
    } else {
        let last = cells.last();
        snapshot_concrete(versions, cells.drop_last()).insert(
            last,
            if versions.contains_key(last) && versions[last].len() > 0 {
                versions[last][versions[last].len() - 1].1
            } else {
                null_sentinel_string()
            },
        )
    }
}

// Post-commit version map: each cell in write_set gets an additional
// version (new_clock, write_values[cell]) appended to its chain.
pub open spec fn concrete_versions_after_commit(
    base: Map<ConcreteCellId, VersionChain>,
    write_set: Set<ConcreteCellId>,
    write_values: Map<ConcreteCellId, ConcreteValue>,
    new_clock: ConcreteTime,
) -> Map<ConcreteCellId, VersionChain> {
    Map::new(
        |cc: ConcreteCellId| base.contains_key(cc) || write_set.contains(cc),
        |cc: ConcreteCellId|
            if write_set.contains(cc) && write_values.contains_key(cc) {
                let base_chain = if base.contains_key(cc) { base[cc] }
                                 else { Seq::<(ConcreteTime, ConcreteValue)>::empty() };
                base_chain.push((new_clock, write_values[cc]))
            } else if base.contains_key(cc) {
                base[cc]
            } else {
                Seq::<(ConcreteTime, ConcreteValue)>::empty()
            },
    )
}

// ----- Concrete chain transitions -----

pub open spec fn concrete_ssi_chain_begin_step(
    c: &ConcreteSsiChainInner,
    cs: &CallerSnapshotMap,
    agent: ConcreteAgentId,
    cells: Seq<ConcreteCellId>,
    c_new: &ConcreteSsiChainInner,
    cs_new: &CallerSnapshotMap,
) -> bool {
    !cs.contains_key(agent)
    && c_new.versions == c.versions
    && c_new.clock == c.clock
    && c_new.trace == c.trace
    && *cs_new == cs.insert(agent, CallerSnapshot {
        read_time: c.clock,
        read_values: snapshot_concrete(c.versions, cells),
    })
}

pub open spec fn concrete_ssi_chain_commit_success_step(
    c: &ConcreteSsiChainInner,
    cs: &CallerSnapshotMap,
    agent: ConcreteAgentId,
    write_set: Set<ConcreteCellId>,
    write_values: Map<ConcreteCellId, ConcreteValue>,
    c_new: &ConcreteSsiChainInner,
    cs_new: &CallerSnapshotMap,
) -> bool {
    cs.contains_key(agent)
    && write_set.finite()
    && write_set.subset_of(write_values.dom())
    && concrete_validation_passes(c, cs[agent])
    && c_new.clock == (c.clock + 1) as nat
    && c_new.versions == concrete_versions_after_commit(c.versions, write_set, write_values, c_new.clock)
    && c_new.trace == c.trace.push(ConcreteOpRecord {
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

pub open spec fn concrete_ssi_chain_commit_abort_step(
    c: &ConcreteSsiChainInner,
    cs: &CallerSnapshotMap,
    agent: ConcreteAgentId,
    c_new: &ConcreteSsiChainInner,
    cs_new: &CallerSnapshotMap,
) -> bool {
    cs.contains_key(agent)
    && !concrete_validation_passes(c, cs[agent])
    && c_new.versions == c.versions
    && c_new.clock == c.clock
    && c_new.trace == c.trace
    && *cs_new == cs.remove(agent)
}

// =====================================================================
// Section 4: Abstract SSI state (mirrors lib_ssi.rs)
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

pub struct AbstractSsiState {
    pub store: Map<AbstractCellId, AbstractValue>,
    pub last_write: Map<AbstractCellId, AbstractTime>,
    pub pending: Map<AbstractAgentId, AbstractPendingSnapshot>,
    pub clock: AbstractTime,
    pub trace: Seq<AbstractOpRecord>,
}

pub open spec fn init_abstract_ssi() -> AbstractSsiState {
    AbstractSsiState {
        store: Map::<AbstractCellId, AbstractValue>::empty(),
        last_write: Map::<AbstractCellId, AbstractTime>::empty(),
        pending: Map::<AbstractAgentId, AbstractPendingSnapshot>::empty(),
        clock: 0,
        trace: Seq::<AbstractOpRecord>::empty(),
    }
}

pub open spec fn abstract_last_write_of(s: &AbstractSsiState, c: AbstractCellId) -> AbstractTime {
    if s.last_write.contains_key(c) { s.last_write[c] } else { 0 }
}

pub open spec fn abstract_validation_passes(s: &AbstractSsiState, ps: AbstractPendingSnapshot) -> bool {
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

pub open spec fn abstract_ssi_begin_step(
    s: &AbstractSsiState,
    agent: AbstractAgentId,
    cells: Seq<AbstractCellId>,
    s_new: &AbstractSsiState,
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

pub open spec fn abstract_ssi_commit_success_step(
    s: &AbstractSsiState,
    agent: AbstractAgentId,
    write_set: Set<AbstractCellId>,
    write_values: Map<AbstractCellId, AbstractValue>,
    s_new: &AbstractSsiState,
) -> bool {
    s.pending.contains_key(agent)
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

pub open spec fn abstract_ssi_commit_abort_step(
    s: &AbstractSsiState,
    agent: AbstractAgentId,
    s_new: &AbstractSsiState,
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
// Section 5: Abstraction function (chain -> abstract)
// =====================================================================

// abstract_store: latest value per cell present in chain, with the
// abstraction extracting the int-encoded value via value_alpha.
pub open spec fn abstract_store_from_chain(versions: Map<ConcreteCellId, VersionChain>)
    -> Map<AbstractCellId, AbstractValue>
{
    Map::new(
        |c: AbstractCellId| exists |cc: ConcreteCellId|
            #[trigger] versions.contains_key(cc) && versions[cc].len() > 0 && cell_alpha(cc) == c,
        |c: AbstractCellId| {
            let cc = choose |cc: ConcreteCellId|
                #[trigger] versions.contains_key(cc) && versions[cc].len() > 0 && cell_alpha(cc) == c;
            value_alpha(versions[cc][versions[cc].len() - 1].1)
        },
    )
}

pub open spec fn abstract_last_write_from_chain(versions: Map<ConcreteCellId, VersionChain>)
    -> Map<AbstractCellId, AbstractTime>
{
    Map::new(
        |c: AbstractCellId| exists |cc: ConcreteCellId|
            #[trigger] versions.contains_key(cc) && versions[cc].len() > 0 && cell_alpha(cc) == c,
        |c: AbstractCellId| {
            let cc = choose |cc: ConcreteCellId|
                #[trigger] versions.contains_key(cc) && versions[cc].len() > 0 && cell_alpha(cc) == c;
            versions[cc][versions[cc].len() - 1].0 as int
        },
    )
}

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

pub open spec fn abstract_record(r: ConcreteOpRecord) -> AbstractOpRecord {
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

pub open spec fn abstract_trace(t: Seq<ConcreteOpRecord>) -> Seq<AbstractOpRecord>
    decreases t.len()
{
    if t.len() == 0 {
        Seq::<AbstractOpRecord>::empty()
    } else {
        abstract_trace(t.drop_last()).push(abstract_record(t.last()))
    }
}

pub open spec fn abstract_of_chain(c: ConcreteSsiChainInner, cs: CallerSnapshotMap)
    -> AbstractSsiState
{
    AbstractSsiState {
        store: abstract_store_from_chain(c.versions),
        last_write: abstract_last_write_from_chain(c.versions),
        pending: abstract_pending(cs),
        clock: c.clock as int,
        trace: abstract_trace(c.trace),
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

pub proof fn lemma_init_correspondence_chain()
    ensures abstract_of_chain(init_concrete_ssi_chain(),
                              Map::<ConcreteAgentId, CallerSnapshot>::empty())
        == init_abstract_ssi()
{
    let c = init_concrete_ssi_chain();
    let cs = Map::<ConcreteAgentId, CallerSnapshot>::empty();
    let a_act = abstract_of_chain(c, cs);
    let a_exp = init_abstract_ssi();

    assert(a_act.store.dom() =~= Set::<AbstractCellId>::empty()) by {
        assert forall |k: AbstractCellId| !#[trigger] a_act.store.dom().contains(k) by {
            if a_act.store.dom().contains(k) {
                let cc = choose |cc: ConcreteCellId|
                    #[trigger] c.versions.contains_key(cc) && c.versions[cc].len() > 0 && cell_alpha(cc) == k;
                assert(c.versions.contains_key(cc));
                assert(false);
            }
        };
    };
    assert(a_act.store =~= a_exp.store);

    assert(a_act.last_write.dom() =~= Set::<AbstractCellId>::empty()) by {
        assert forall |k: AbstractCellId| !#[trigger] a_act.last_write.dom().contains(k) by {
            if a_act.last_write.dom().contains(k) {
                let cc = choose |cc: ConcreteCellId|
                    #[trigger] c.versions.contains_key(cc) && c.versions[cc].len() > 0 && cell_alpha(cc) == k;
                assert(c.versions.contains_key(cc));
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
// Section 7: Pending insert/remove + trace push helpers
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
            assert(cc == k);
        } else {
            assert(cc != k);
            assert(base.contains_key(cc));
            let cc2 = choose |cc2: ConcreteCellId|
                #[trigger] base.contains_key(cc2) && cell_alpha(cc2) == x;
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
        } else {
            assert(ca != a);
            assert(base.contains_key(ca));
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
        let ca2 = choose |ca2: ConcreteAgentId|
            #[trigger] base.contains_key(ca2) && agent_alpha(ca2) == x;
        assert(ca == ca2);
    };

    assert(lhs =~= rhs);
}

pub proof fn lemma_abstract_trace_push(
    t: Seq<ConcreteOpRecord>,
    r: ConcreteOpRecord,
)
    ensures abstract_trace(t.push(r)) == abstract_trace(t).push(abstract_record(r))
{
    let pushed = t.push(r);
    assert(pushed.len() == t.len() + 1);
    assert(pushed.len() > 0);
    assert(pushed.drop_last() =~= t);
    assert(pushed.last() == r);
}

// =====================================================================
// Section 8: Snapshot commutativity
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

// snapshot_concrete commutes with abstraction: reading the chain's
// latest value and then abstracting equals snapshotting from the
// already-abstracted store.
pub proof fn lemma_snapshot_commutes(
    versions: Map<ConcreteCellId, VersionChain>,
    cells: Seq<ConcreteCellId>,
)
    ensures abstract_data(snapshot_concrete(versions, cells))
        == snapshot_built_abs(abstract_store_from_chain(versions), cells_alpha(cells))
    decreases cells.len()
{
    broadcast use axiom_string_to_int_injective;
    broadcast use axiom_null_sentinel;

    let abs_store = abstract_store_from_chain(versions);

    if cells.len() == 0 {
        assert(cells_alpha(cells).len() == 0);
        assert(snapshot_concrete(versions, cells) == Map::<ConcreteCellId, ConcreteValue>::empty());
        assert(abstract_data(snapshot_concrete(versions, cells)).dom()
               =~= Set::<AbstractCellId>::empty()) by {
            assert forall |x: AbstractCellId|
                !#[trigger] abstract_data(snapshot_concrete(versions, cells)).dom().contains(x) by {
                if abstract_data(snapshot_concrete(versions, cells)).dom().contains(x) {
                    let cc = choose |cc: ConcreteCellId|
                        #[trigger] snapshot_concrete(versions, cells).contains_key(cc)
                        && cell_alpha(cc) == x;
                    assert(snapshot_concrete(versions, cells).contains_key(cc));
                    assert(false);
                }
            };
        };
        assert(abstract_data(snapshot_concrete(versions, cells))
               =~= Map::<AbstractCellId, AbstractValue>::empty());
    } else {
        let prefix = cells.drop_last();
        let last = cells.last();
        lemma_snapshot_commutes(versions, prefix);

        let inner_concrete = snapshot_concrete(versions, prefix);
        let val_c = if versions.contains_key(last) && versions[last].len() > 0 {
                        versions[last][versions[last].len() - 1].1
                    } else {
                        null_sentinel_string()
                    };
        assert(snapshot_concrete(versions, cells) == inner_concrete.insert(last, val_c));

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

        lemma_snapshot_built_abs_push(abs_store, cells_alpha(prefix), cell_alpha(last));

        if versions.contains_key(last) && versions[last].len() > 0 {
            // abs_store has cell_alpha(last)
            assert(abs_store.dom().contains(cell_alpha(last))) by {
                assert(versions.contains_key(last) && versions[last].len() > 0
                       && cell_alpha(last) == cell_alpha(last));
            };
            let cc = choose |cc: ConcreteCellId|
                #[trigger] versions.contains_key(cc) && versions[cc].len() > 0
                && cell_alpha(cc) == cell_alpha(last);
            assert(cc == last);
            assert(abs_store[cell_alpha(last)] == value_alpha(versions[last][versions[last].len() - 1].1));
            assert(value_alpha(val_c) == abs_store[cell_alpha(last)]);
        } else {
            // !versions.contains_key(last) || versions[last].len() == 0
            // abs_store should not contain cell_alpha(last)
            assert(!abs_store.dom().contains(cell_alpha(last))) by {
                if abs_store.dom().contains(cell_alpha(last)) {
                    let cc = choose |cc: ConcreteCellId|
                        #[trigger] versions.contains_key(cc) && versions[cc].len() > 0
                        && cell_alpha(cc) == cell_alpha(last);
                    assert(cc == last);
                    assert(false);
                }
            };
            assert(value_alpha(val_c) == abs_null_value());
        }

        assert(snapshot_built_abs(abs_store, cells_alpha(cells))
               == snapshot_built_abs(abs_store, pushed));
    }
}

// =====================================================================
// Section 9: Validation correspondence + store/last_write commutativity
// =====================================================================

pub proof fn lemma_validation_passes_corresponds(
    c: &ConcreteSsiChainInner,
    cs: &CallerSnapshotMap,
    agent: ConcreteAgentId,
)
    requires
        cs.contains_key(agent),
        concrete_validation_passes(c, cs[agent]),
    ensures ({
        let s = abstract_of_chain(*c, *cs);
        let agent_a = agent_alpha(agent);
        s.pending.contains_key(agent_a) && abstract_validation_passes(&s, s.pending[agent_a])
    })
{
    broadcast use axiom_string_to_int_injective;

    let s = abstract_of_chain(*c, *cs);
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
        assert(cs[agent].read_values.contains_key(cc));
        assert(concrete_last_write_of(c, cc) <= cs[agent].read_time);
        if c.versions.contains_key(cc) && c.versions[cc].len() > 0 {
            assert(s.last_write.dom().contains(cell_alpha(cc))) by {
                assert(c.versions.contains_key(cc) && c.versions[cc].len() > 0
                       && cell_alpha(cc) == cell_alpha(cc));
            };
            let cc2 = choose |cc2: ConcreteCellId|
                #[trigger] c.versions.contains_key(cc2) && c.versions[cc2].len() > 0
                && cell_alpha(cc2) == x;
            assert(cc == cc2);
        } else {
            assert(!s.last_write.dom().contains(x)) by {
                if s.last_write.dom().contains(x) {
                    let cc2 = choose |cc2: ConcreteCellId|
                        #[trigger] c.versions.contains_key(cc2) && c.versions[cc2].len() > 0
                        && cell_alpha(cc2) == x;
                    assert(cc == cc2);
                    assert(false);
                }
            };
        }
    };
}

// store_after_commit commutativity at the chain level. The chain at
// each c in write_set grows by one element; the latest value becomes
// write_values[c].
pub proof fn lemma_chain_store_commutes(
    base: Map<ConcreteCellId, VersionChain>,
    write_set: Set<ConcreteCellId>,
    write_values: Map<ConcreteCellId, ConcreteValue>,
    new_clock: ConcreteTime,
)
    requires
        write_set.finite(),
        write_set.subset_of(write_values.dom()),
        // chain monotonicity precondition (so that the post-commit chain
        // is also monotone, and we can extract the latest value cleanly)
        forall |cc: ConcreteCellId|
            #[trigger] base.contains_key(cc) ==>
                base[cc].len() > 0 && chain_max_lt(base[cc], new_clock),
    ensures abstract_store_from_chain(concrete_versions_after_commit(base, write_set, write_values, new_clock))
        == abstract_store_after_commit(
            abstract_store_from_chain(base),
            write_set.map(|c: ConcreteCellId| cell_alpha(c)),
            abstract_data(write_values),
        )
{
    broadcast use axiom_string_to_int_injective;
    broadcast use axiom_null_sentinel;

    let new_versions = concrete_versions_after_commit(base, write_set, write_values, new_clock);
    let lhs = abstract_store_from_chain(new_versions);
    let abs_base = abstract_store_from_chain(base);
    let ws_a = write_set.map(|c: ConcreteCellId| cell_alpha(c));
    let rhs = abstract_store_after_commit(abs_base, ws_a, abstract_data(write_values));

    assert(lhs.dom() =~= rhs.dom()) by {
        assert forall |x: AbstractCellId| lhs.dom().contains(x) implies rhs.dom().contains(x) by {
            let cc = choose |cc: ConcreteCellId|
                #[trigger] new_versions.contains_key(cc) && new_versions[cc].len() > 0
                && cell_alpha(cc) == x;
            // cc is in base or in write_set
            if base.contains_key(cc) {
                assert(abs_base.dom().contains(x)) by {
                    assert(base.contains_key(cc) && base[cc].len() > 0 && cell_alpha(cc) == x);
                };
            } else {
                assert(write_set.contains(cc));
                assert(ws_a.contains(x));
            }
        };
        assert forall |x: AbstractCellId| rhs.dom().contains(x) implies lhs.dom().contains(x) by {
            if abs_base.dom().contains(x) {
                let cc = choose |cc: ConcreteCellId|
                    #[trigger] base.contains_key(cc) && base[cc].len() > 0 && cell_alpha(cc) == x;
                assert(new_versions.contains_key(cc));
                assert(new_versions[cc].len() > 0);
            } else {
                assert(ws_a.contains(x));
                let cc = choose |cc: ConcreteCellId|
                    write_set.contains(cc) && cell_alpha(cc) == x;
                assert(write_values.contains_key(cc));
                assert(new_versions.contains_key(cc));
                assert(new_versions[cc].len() > 0);
            }
        };
    };

    assert forall |x: AbstractCellId| lhs.dom().contains(x) implies lhs[x] == rhs[x] by {
        let cc = choose |cc: ConcreteCellId|
            #[trigger] new_versions.contains_key(cc) && new_versions[cc].len() > 0
            && cell_alpha(cc) == x;
        let chain = new_versions[cc];
        let latest_val = chain[chain.len() - 1].1;
        assert(lhs[x] == value_alpha(latest_val));

        if write_set.contains(cc) && write_values.contains_key(cc) {
            // chain = (base.contains_key(cc) ? base[cc] : empty).push((new_clock, write_values[cc]))
            // chain.last() == (new_clock, write_values[cc]); chain.last().1 == write_values[cc]
            let base_chain = if base.contains_key(cc) { base[cc] }
                             else { Seq::<(ConcreteTime, ConcreteValue)>::empty() };
            assert(chain == base_chain.push((new_clock, write_values[cc])));
            assert(chain.len() == base_chain.len() + 1);
            assert(chain[chain.len() - 1] == (new_clock, write_values[cc]));
            assert(latest_val == write_values[cc]);

            assert(ws_a.contains(x));
            assert(abstract_data(write_values).dom().contains(x)) by {
                assert(write_values.contains_key(cc) && cell_alpha(cc) == x);
            };
            let cw = choose |cw: ConcreteCellId|
                #[trigger] write_values.contains_key(cw) && cell_alpha(cw) == x;
            assert(cw == cc);
            assert(abstract_data(write_values)[x] == value_alpha(write_values[cc]));
            assert(rhs[x] == value_alpha(write_values[cc]));
        } else {
            // cc not in write_set or write_values doesn't have cc.
            // From subset_of: write_set.contains(cc) ==> write_values.contains_key(cc).
            // So !write_set.contains(cc).
            assert(!write_set.contains(cc));
            // Therefore cc is in base.
            assert(base.contains_key(cc));
            assert(chain == base[cc]);
            assert(latest_val == base[cc][base[cc].len() - 1].1);

            // x not in ws_a
            assert(!ws_a.contains(x)) by {
                if ws_a.contains(x) {
                    let cw = choose |cw: ConcreteCellId|
                        write_set.contains(cw) && cell_alpha(cw) == x;
                    assert(cw == cc);
                    assert(false);
                }
            };

            // abs_base[x] == value_alpha(base[cc].last().1)
            assert(abs_base.dom().contains(x));
            let cb = choose |cb: ConcreteCellId|
                #[trigger] base.contains_key(cb) && base[cb].len() > 0 && cell_alpha(cb) == x;
            assert(cb == cc);
            assert(abs_base[x] == value_alpha(base[cc][base[cc].len() - 1].1));
            assert(rhs[x] == abs_base[x]);
        }
    };

    assert(lhs =~= rhs);
}

// Helper: all times in chain are strictly less than t.
pub open spec fn chain_max_lt(chain: VersionChain, t: ConcreteTime) -> bool {
    forall |i: int| 0 <= i < chain.len() ==> #[trigger] chain[i].0 < t
}

pub proof fn lemma_chain_last_write_commutes(
    base: Map<ConcreteCellId, VersionChain>,
    write_set: Set<ConcreteCellId>,
    write_values: Map<ConcreteCellId, ConcreteValue>,
    new_clock: ConcreteTime,
)
    requires
        write_set.finite(),
        write_set.subset_of(write_values.dom()),
        forall |cc: ConcreteCellId|
            #[trigger] base.contains_key(cc) ==>
                base[cc].len() > 0 && chain_max_lt(base[cc], new_clock),
    ensures abstract_last_write_from_chain(concrete_versions_after_commit(base, write_set, write_values, new_clock))
        == abstract_last_write_after_commit(
            abstract_last_write_from_chain(base),
            write_set.map(|c: ConcreteCellId| cell_alpha(c)),
            new_clock as int,
        )
{
    broadcast use axiom_string_to_int_injective;

    let new_versions = concrete_versions_after_commit(base, write_set, write_values, new_clock);
    let lhs = abstract_last_write_from_chain(new_versions);
    let abs_base = abstract_last_write_from_chain(base);
    let ws_a = write_set.map(|c: ConcreteCellId| cell_alpha(c));
    let rhs = abstract_last_write_after_commit(abs_base, ws_a, new_clock as int);

    assert(lhs.dom() =~= rhs.dom()) by {
        assert forall |x: AbstractCellId| lhs.dom().contains(x) implies rhs.dom().contains(x) by {
            let cc = choose |cc: ConcreteCellId|
                #[trigger] new_versions.contains_key(cc) && new_versions[cc].len() > 0
                && cell_alpha(cc) == x;
            if base.contains_key(cc) {
                assert(abs_base.dom().contains(x)) by {
                    assert(base.contains_key(cc) && base[cc].len() > 0 && cell_alpha(cc) == x);
                };
            } else {
                assert(write_set.contains(cc));
                assert(ws_a.contains(x));
            }
        };
        assert forall |x: AbstractCellId| rhs.dom().contains(x) implies lhs.dom().contains(x) by {
            if abs_base.dom().contains(x) {
                let cc = choose |cc: ConcreteCellId|
                    #[trigger] base.contains_key(cc) && base[cc].len() > 0 && cell_alpha(cc) == x;
                assert(new_versions.contains_key(cc));
                assert(new_versions[cc].len() > 0);
            } else {
                assert(ws_a.contains(x));
                let cc = choose |cc: ConcreteCellId|
                    write_set.contains(cc) && cell_alpha(cc) == x;
                assert(write_values.contains_key(cc));
                assert(new_versions.contains_key(cc));
                assert(new_versions[cc].len() > 0);
            }
        };
    };

    assert forall |x: AbstractCellId| lhs.dom().contains(x) implies lhs[x] == rhs[x] by {
        let cc = choose |cc: ConcreteCellId|
            #[trigger] new_versions.contains_key(cc) && new_versions[cc].len() > 0
            && cell_alpha(cc) == x;
        let chain = new_versions[cc];
        let latest_time = chain[chain.len() - 1].0;
        assert(lhs[x] == latest_time as int);

        if write_set.contains(cc) && write_values.contains_key(cc) {
            let base_chain = if base.contains_key(cc) { base[cc] }
                             else { Seq::<(ConcreteTime, ConcreteValue)>::empty() };
            assert(chain == base_chain.push((new_clock, write_values[cc])));
            assert(chain[chain.len() - 1] == (new_clock, write_values[cc]));
            assert(latest_time == new_clock);
            assert(ws_a.contains(x));
            assert(rhs[x] == new_clock as int);
        } else {
            assert(!write_set.contains(cc));
            assert(base.contains_key(cc));
            assert(chain == base[cc]);
            assert(latest_time == base[cc][base[cc].len() - 1].0);
            assert(!ws_a.contains(x)) by {
                if ws_a.contains(x) {
                    let cw = choose |cw: ConcreteCellId|
                        write_set.contains(cw) && cell_alpha(cw) == x;
                    assert(cw == cc);
                    assert(false);
                }
            };
            assert(abs_base.dom().contains(x));
            let cb = choose |cb: ConcreteCellId|
                #[trigger] base.contains_key(cb) && base[cb].len() > 0 && cell_alpha(cb) == x;
            assert(cb == cc);
            assert(abs_base[x] == base[cc][base[cc].len() - 1].0 as int);
            assert(rhs[x] == abs_base[x]);
        }
    };

    assert(lhs =~= rhs);
}

// =====================================================================
// Section 10: Refinement lemmas
// =====================================================================

pub proof fn lemma_ssi_chain_begin_refines(
    c: &ConcreteSsiChainInner,
    cs: &CallerSnapshotMap,
    agent: ConcreteAgentId,
    cells: Seq<ConcreteCellId>,
    c_new: &ConcreteSsiChainInner,
    cs_new: &CallerSnapshotMap,
)
    requires concrete_ssi_chain_begin_step(c, cs, agent, cells, c_new, cs_new)
    ensures abstract_ssi_begin_step(
        &abstract_of_chain(*c, *cs),
        agent_alpha(agent),
        cells_alpha(cells),
        &abstract_of_chain(*c_new, *cs_new),
    )
{
    broadcast use axiom_string_to_int_injective;

    let s = abstract_of_chain(*c, *cs);
    let s_new = abstract_of_chain(*c_new, *cs_new);
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
            assert(ca == agent);
            assert(false);
        }
    };

    let snap_c = CallerSnapshot {
        read_time: c.clock,
        read_values: snapshot_concrete(c.versions, cells),
    };

    lemma_abstract_pending_insert(*cs, agent, snap_c);
    lemma_snapshot_commutes(c.versions, cells);

    assert(s_new.pending == s.pending.insert(
        agent_a,
        AbstractPendingSnapshot {
            read_time: s.clock,
            read_values: snapshot_built_abs(s.store, cells_a),
        },
    ));
}

pub proof fn lemma_ssi_chain_commit_success_refines(
    c: &ConcreteSsiChainInner,
    cs: &CallerSnapshotMap,
    agent: ConcreteAgentId,
    write_set: Set<ConcreteCellId>,
    write_values: Map<ConcreteCellId, ConcreteValue>,
    c_new: &ConcreteSsiChainInner,
    cs_new: &CallerSnapshotMap,
)
    requires
        concrete_ssi_chain_commit_success_step(c, cs, agent, write_set, write_values, c_new, cs_new),
        // Chain-monotonicity precondition: every existing chain has
        // strictly increasing times bounded by clock. This is the
        // invariant the Rust runtime maintains by construction.
        forall |cc: ConcreteCellId|
            #[trigger] c.versions.contains_key(cc) ==>
                c.versions[cc].len() > 0 && chain_max_lt(c.versions[cc], c_new.clock),
    ensures abstract_ssi_commit_success_step(
        &abstract_of_chain(*c, *cs),
        agent_alpha(agent),
        write_set.map(|c: ConcreteCellId| cell_alpha(c)),
        abstract_writes(write_values),
        &abstract_of_chain(*c_new, *cs_new),
    )
{
    broadcast use axiom_string_to_int_injective;

    let s = abstract_of_chain(*c, *cs);
    let s_new = abstract_of_chain(*c_new, *cs_new);
    let agent_a = agent_alpha(agent);
    let write_set_a = write_set.map(|c: ConcreteCellId| cell_alpha(c));
    let write_kv = abstract_writes(write_values);

    // pending precondition
    assert(s.pending.dom().contains(agent_a)) by {
        assert(cs.contains_key(agent) && agent_alpha(agent) == agent_a);
    };

    // finiteness via proven lemma
    lemma_set_map_preserves_finite(write_set, |c: ConcreteCellId| cell_alpha(c));
    assert(write_set_a.finite());

    // subset
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

    // validation
    lemma_validation_passes_corresponds(c, cs, agent);

    // clock
    assert(s_new.clock == s.clock + 1);

    // last_write
    lemma_chain_last_write_commutes(c.versions, write_set, write_values, c_new.clock);

    // store
    lemma_chain_store_commutes(c.versions, write_set, write_values, c_new.clock);

    // pending remove
    lemma_abstract_pending_remove(*cs, agent);

    // trace push
    let record_c = ConcreteOpRecord {
        agent: agent,
        read_set: cs[agent].read_values.dom(),
        read_values: cs[agent].read_values,
        read_time: cs[agent].read_time,
        write_set: write_set,
        write_values: write_values,
        write_time: c_new.clock,
    };
    assert(c_new.trace == c.trace.push(record_c));
    lemma_abstract_trace_push(c.trace, record_c);

    let ca_pending = choose |ca: ConcreteAgentId|
        #[trigger] cs.contains_key(ca) && agent_alpha(ca) == agent_a;
    assert(ca_pending == agent);
    assert(s.pending[agent_a].read_values == abstract_data(cs[agent].read_values));
    assert(s.pending[agent_a].read_time == cs[agent].read_time as int);

    // read_set domain equality
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

pub proof fn lemma_ssi_chain_commit_abort_refines(
    c: &ConcreteSsiChainInner,
    cs: &CallerSnapshotMap,
    agent: ConcreteAgentId,
    c_new: &ConcreteSsiChainInner,
    cs_new: &CallerSnapshotMap,
)
    requires concrete_ssi_chain_commit_abort_step(c, cs, agent, c_new, cs_new)
    ensures abstract_ssi_commit_abort_step(
        &abstract_of_chain(*c, *cs),
        agent_alpha(agent),
        &abstract_of_chain(*c_new, *cs_new),
    )
{
    broadcast use axiom_string_to_int_injective;

    let s = abstract_of_chain(*c, *cs);
    let s_new = abstract_of_chain(*c_new, *cs_new);
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
    if c.versions.contains_key(cc_witness) && c.versions[cc_witness].len() > 0 {
        assert(s.last_write.dom().contains(x)) by {
            assert(c.versions.contains_key(cc_witness) && c.versions[cc_witness].len() > 0
                   && cell_alpha(cc_witness) == x);
        };
        let cc2 = choose |cc2: ConcreteCellId|
            #[trigger] c.versions.contains_key(cc2) && c.versions[cc2].len() > 0
            && cell_alpha(cc2) == x;
        assert(cc2 == cc_witness);
    } else {
        assert(concrete_last_write_of(c, cc_witness) == 0);
        assert(false);
    }

    assert(!abstract_validation_passes(&s, s.pending[agent_a]));
}

} // verus!