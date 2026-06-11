#![allow(unused_imports)]
#![allow(dead_code)]
use vstd::prelude::*;

verus! {
pub type AgentId = int;
pub type CellId  = int;
pub type Value   = int;
pub type Time    = int;

pub enum Kind { Acquire, Release, Read, Write }

pub struct Event {
    pub kind:  Kind,
    pub agent: AgentId,
    pub cell:  CellId,
    pub time:  Time,
    pub val:   Value,
}

pub struct State {
    pub holders: Map<CellId, AgentId>,
    pub values:  Map<CellId, Value>,
}

pub open spec fn init() -> State {
    State { holders: Map::empty(), values: Map::empty() }
}

pub open spec fn is_lock_on(e: Event, c: CellId) -> bool {
    (e.kind == Kind::Acquire || e.kind == Kind::Release) && e.cell == c
}

pub open spec fn is_access_on(e: Event, c: CellId) -> bool {
    (e.kind == Kind::Read || e.kind == Kind::Write) && e.cell == c
}

pub open spec fn step(s: State, e: Event) -> State {
    match e.kind {
        Kind::Acquire => State { holders: s.holders.insert(e.cell, e.agent), values: s.values },
        Kind::Release => State { holders: s.holders.remove(e.cell),          values: s.values },
        Kind::Read    => s,
        Kind::Write   => State { holders: s.holders, values: s.values.insert(e.cell, e.val) },
    }
}

pub open spec fn step_enabled(s: State, e: Event) -> bool {
    match e.kind {
        Kind::Acquire => !s.holders.contains_key(e.cell),
        Kind::Release => s.holders.contains_key(e.cell) && s.holders[e.cell] == e.agent,
        Kind::Read    => s.holders.contains_key(e.cell) && s.holders[e.cell] == e.agent
                         && (s.values.contains_key(e.cell) ==> s.values[e.cell] == e.val),
        Kind::Write   => s.holders.contains_key(e.cell) && s.holders[e.cell] == e.agent,
    }
}

pub open spec fn state_after(tr: Seq<Event>, i: int) -> State
    decreases i,
{
    if i <= 0 { init() } else { step(state_after(tr, i - 1), tr[i - 1]) }
}

pub open spec fn well_formed(tr: Seq<Event>) -> bool {
    forall |i: int| #![trigger step_enabled(state_after(tr, i), tr[i])]
        0 <= i < tr.len() ==> step_enabled(state_after(tr, i), tr[i])
}

pub proof fn lemma_state_after_prefix(tr: Seq<Event>, m: int, i: int)
    requires 0 <= i <= m <= tr.len(),
    ensures  state_after(tr.subrange(0, m), i) == state_after(tr, i),
    decreases i,
{
    if i <= 0 {
    } else {
        lemma_state_after_prefix(tr, m, i - 1);
        assert(tr.subrange(0, m)[i - 1] == tr[i - 1]);
    }
}

pub proof fn lemma_prefix_monotonicity(tr: Seq<Event>, m: int)
    requires well_formed(tr), 0 <= m <= tr.len(),
    ensures  well_formed(tr.subrange(0, m)),
{
    let p = tr.subrange(0, m);
    assert(p.len() == m);
    assert forall |i: int| #![trigger step_enabled(state_after(p, i), p[i])]
        0 <= i < p.len() implies step_enabled(state_after(p, i), p[i]) by {
        lemma_state_after_prefix(tr, m, i);
        assert(p[i] == tr[i]);
        assert(step_enabled(state_after(tr, i), tr[i]));
    }
}

pub proof fn lemma_mutex_exclusion(tr: Seq<Event>, i: int, c: CellId, a1: AgentId, a2: AgentId)
    requires
        state_after(tr, i).holders.contains_key(c),
        state_after(tr, i).holders[c] == a1,
        state_after(tr, i).holders[c] == a2,
    ensures a1 == a2,
{
}

pub proof fn lemma_access_implies_lock_held(tr: Seq<Event>, i: int)
    requires
        well_formed(tr),
        0 <= i < tr.len(),
        tr[i].kind == Kind::Read || tr[i].kind == Kind::Write,
    ensures
        state_after(tr, i).holders.contains_key(tr[i].cell),
        state_after(tr, i).holders[tr[i].cell] == tr[i].agent,
{
    assert(step_enabled(state_after(tr, i), tr[i]));
}

pub proof fn lemma_reads_observe_current_value(tr: Seq<Event>, i: int)
    requires
        well_formed(tr),
        0 <= i < tr.len(),
        tr[i].kind == Kind::Read,
        state_after(tr, i).values.contains_key(tr[i].cell),
    ensures
        state_after(tr, i).values[tr[i].cell] == tr[i].val,
{
    assert(step_enabled(state_after(tr, i), tr[i]));
}

pub proof fn lemma_holder_unchanged_without_lock_event(tr: Seq<Event>, a: int, b: int, c: CellId)
    requires
        0 <= a <= b <= tr.len(),
        forall |k: int| a <= k < b ==> !(#[trigger] is_lock_on(tr[k], c)),
    ensures
        state_after(tr, a).holders.contains_key(c) == state_after(tr, b).holders.contains_key(c),
        state_after(tr, a).holders.contains_key(c)
            ==> state_after(tr, a).holders[c] == state_after(tr, b).holders[c],
    decreases b - a,
{
    if b <= a {
    } else {
        assert(forall |k: int| a <= k < b - 1 ==> !(#[trigger] is_lock_on(tr[k], c)));
        lemma_holder_unchanged_without_lock_event(tr, a, b - 1, c);

        let e  = tr[b - 1];
        let sp = state_after(tr, b - 1);
        assert(!is_lock_on(e, c));

        match e.kind {
            Kind::Read    => {}
            Kind::Write   => {}
            Kind::Acquire => { assert(e.cell != c); }
            Kind::Release => { assert(e.cell != c); }
        }
    }
}

pub proof fn lemma_distinct_agent_access_separation(tr: Seq<Event>, i: int, j: int, c: CellId)
    requires
        well_formed(tr),
        0 <= i < j < tr.len(),
        is_access_on(tr[i], c),
        is_access_on(tr[j], c),
        tr[i].agent != tr[j].agent,
    ensures
        exists |k: int| #![trigger is_lock_on(tr[k], c)] i < k < j && is_lock_on(tr[k], c),
{
    lemma_access_implies_lock_held(tr, i);
    lemma_access_implies_lock_held(tr, j);

    if forall |k: int| i <= k < j ==> !(#[trigger] is_lock_on(tr[k], c)) {
        lemma_holder_unchanged_without_lock_event(tr, i, j, c);
        assert(state_after(tr, i).holders[c] == state_after(tr, j).holders[c]);
        assert(tr[i].agent == tr[j].agent);
        assert(false);
    }

    let k = choose |k: int| #![trigger is_lock_on(tr[k], c)] i <= k < j && is_lock_on(tr[k], c);
    assert(is_access_on(tr[i], c));
    assert(k != i);
    assert(i < k < j && is_lock_on(tr[k], c));
}

pub proof fn lemma_nonvacuous_witness()
    ensures
        exists |tr: Seq<Event>| #![trigger well_formed(tr)]
            well_formed(tr) && tr.len() == 2 && tr[1].kind == Kind::Read,
{
    let e0 = Event { kind: Kind::Acquire, agent: 1, cell: 0, time: 0, val: 0 };
    let e1 = Event { kind: Kind::Read,    agent: 1, cell: 0, time: 1, val: 7 };
    let tr = seq![e0, e1];

    assert(tr.len() == 2);
    assert(tr[0] == e0);
    assert(tr[1] == e1);

    assert(state_after(tr, 0) == init());
    assert(step_enabled(state_after(tr, 0), tr[0]));
    assert(state_after(tr, 1) == step(init(), e0));
    assert(state_after(tr, 1).holders.contains_key(0));
    assert(state_after(tr, 1).holders[0] == 1);
    assert(!state_after(tr, 1).values.contains_key(0));
    assert(step_enabled(state_after(tr, 1), tr[1]));

    assert forall |i: int| #![trigger step_enabled(state_after(tr, i), tr[i])]
        0 <= i < tr.len() implies step_enabled(state_after(tr, i), tr[i]) by {
        if i == 0 {} else { assert(i == 1); }
    }
    assert(well_formed(tr));
}

} // verus!