// lib_langgraph_refinement.rs
// ---------------------------------------------------------------------------
// Closes the model<->runtime gap for the L0 -> L1 ascent by giving a faithful
// core model of LangGraph's channel-update semantics and PROVING:
//
//   (T1) an accumulating reducer channel refines L1: its value is exactly the
//        full history of contributions, so NO committed contribution is lost;
//   (Cor) hence every contribution written by any update survives;
//   (T0) the default last-write-wins (LWW) channel ADMITS L0: a concrete
//        execution silently drops a committed contribution.
//
// This is exactly the deer-flow #3123 fix stated as a refinement theorem:
// without the reducer a downstream write overwrites accumulated state (todos
// lost); with the accumulating reducer the history is preserved (L1).
//
// Discipline: zero axioms, zero external_body, zero assume, zero admit.
//
// --- Senior-reviewer self-challenge (per the proof methodology) ----------
// (a) Right fix? Yes: it formalizes a REAL runtime's reducer (LangGraph's
//     `operator.add` / additive channels) and proves the L0/L1 distinction,
//     rather than excluding the bad execution by construction. Both modes are
//     modeled; the difference is proved, not assumed.
// (b) Add it? Yes: it directly discharges the paper's #1 weakness (the
//     informal model->runtime bridge) for the L0->L1 edge.
// Soundness: T1 is a structural equation (channel == init + concat of all
//     payloads), not an axiom; the LWW counterexample (T0) gives non-vacuity.
//     No trust is relocated to an admitted lemma. The accumulate combinator is
//     a faithful abstraction of an additive reducer (it concatenates payloads
//     in superstep order); the claim "this models LangGraph additive channels"
//     is a modeling claim stated in the paper, not a Verus axiom.
// ---------------------------------------------------------------------------

use vstd::prelude::*;

verus! {

// A channel value is the sequence of contributions accumulated so far
// (e.g., todo items). A per-superstep update carries a payload of new
// contributions. LangGraph applies the channel's reducer to (old, payload):
//   default channel        : LWW        -> new value REPLACES old
//   additive reducer channel: concat     -> new value EXTENDS old
spec fn lww(old: Seq<int>, payload: Seq<int>) -> Seq<int> {
    payload
}

spec fn accumulate(old: Seq<int>, payload: Seq<int>) -> Seq<int> {
    old + payload
}

// Apply a whole sequence of per-superstep payloads, left to right.
spec fn run(init: Seq<int>, updates: Seq<Seq<int>>, lww_mode: bool) -> Seq<int>
    decreases updates.len()
{
    if updates.len() == 0 {
        init
    } else if lww_mode {
        lww(run(init, updates.drop_last(), lww_mode), updates.last())
    } else {
        accumulate(run(init, updates.drop_last(), lww_mode), updates.last())
    }
}

// The full history: concatenation of every payload in superstep order.
spec fn concat_all(updates: Seq<Seq<int>>) -> Seq<int>
    decreases updates.len()
{
    if updates.len() == 0 {
        Seq::empty()
    } else {
        concat_all(updates.drop_last()) + updates.last()
    }
}

// --- T1: the additive reducer channel refines L1 -------------------------
// The channel value is EXACTLY init followed by the full contribution
// history. Nothing committed is ever overwritten or dropped.
proof fn thm_accumulate_refines_l1(init: Seq<int>, updates: Seq<Seq<int>>)
    ensures
        run(init, updates, false) =~= init + concat_all(updates),
    decreases updates.len(),
{
    if updates.len() == 0 {
        assert(concat_all(updates) =~= Seq::<int>::empty());
        assert(init + Seq::<int>::empty() =~= init);
    } else {
        thm_accumulate_refines_l1(init, updates.drop_last());
        let pre = run(init, updates.drop_last(), false);
        assert(run(init, updates, false) =~= pre + updates.last());
        // pre == init + concat_all(drop_last); concat associativity gives the goal
        assert((init + concat_all(updates.drop_last())) + updates.last()
               =~= init + (concat_all(updates.drop_last()) + updates.last()));
        assert(concat_all(updates) =~= concat_all(updates.drop_last()) + updates.last());
    }
}

// Membership distributes over concatenation (proved by index witnesses,
// so the file stays self-contained and axiom-free).
proof fn lemma_concat_contains(a: Seq<int>, b: Seq<int>, x: int)
    ensures
        (a + b).contains(x) <==> (a.contains(x) || b.contains(x)),
{
    if a.contains(x) {
        let i = choose|i: int| 0 <= i < a.len() && a[i] == x;
        assert(0 <= i < (a + b).len());
        assert((a + b)[i] == a[i]);
        assert((a + b).contains(x));
    }
    if b.contains(x) {
        let j = choose|j: int| 0 <= j < b.len() && b[j] == x;
        assert(0 <= a.len() + j < (a + b).len());
        assert((a + b)[a.len() + j] == b[j]);
        assert((a + b).contains(x));
    }
    if (a + b).contains(x) {
        let i = choose|i: int| 0 <= i < (a + b).len() && (a + b)[i] == x;
        if i < a.len() {
            assert(a[i] == x);
            assert(a.contains(x));
        } else {
            assert(b[i - a.len()] == x);
            assert(b.contains(x));
        }
    }
}

// concat_all contains every element of every payload.
proof fn lemma_concat_all_contains(updates: Seq<Seq<int>>, k: int, x: int)
    requires
        0 <= k < updates.len(),
        updates[k].contains(x),
    ensures
        concat_all(updates).contains(x),
    decreases updates.len(),
{
    let pre = concat_all(updates.drop_last());
    let last = updates.last();
    assert(concat_all(updates) =~= pre + last);
    lemma_concat_contains(pre, last, x);
    if k == updates.len() - 1 {
        assert(last =~= updates[k]);
        assert(last.contains(x));
    } else {
        assert(updates.drop_last()[k] =~= updates[k]);
        lemma_concat_all_contains(updates.drop_last(), k, x);
        assert(pre.contains(x));
    }
    assert((pre + last).contains(x));
    assert(concat_all(updates).contains(x));
}

// --- Cor: no lost update under the reducer -------------------------------
// Every contribution committed by any update survives in the final channel.
proof fn cor_no_lost_update(init: Seq<int>, updates: Seq<Seq<int>>, k: int, x: int)
    requires
        0 <= k < updates.len(),
        updates[k].contains(x),
    ensures
        run(init, updates, false).contains(x),
{
    thm_accumulate_refines_l1(init, updates);
    lemma_concat_all_contains(updates, k, x);
    lemma_concat_contains(init, concat_all(updates), x);
    assert((init + concat_all(updates)).contains(x));
    assert(run(init, updates, false).contains(x));
}

// --- T0: the default LWW channel admits L0 (lost update) -----------------
// Concrete non-vacuity witness: two supersteps each commit one contribution;
// under LWW the first is silently dropped from the final channel value. This
// is deer-flow #3123 in miniature (a later partial write clobbers the
// accumulated value).
proof fn thm_lww_admits_l0()
    ensures
        seq![seq![1int], seq![2int]][0].contains(1int),
        !run(Seq::<int>::empty(), seq![seq![1int], seq![2int]], true).contains(1int),
{
    reveal_with_fuel(run, 3);
    let init: Seq<int> = Seq::empty();
    let u1: Seq<Seq<int>> = seq![seq![1int]];
    let u2: Seq<Seq<int>> = seq![seq![1int], seq![2int]];

    assert(run(init, Seq::<Seq<int>>::empty(), true) =~= init);

    assert(u1.drop_last() =~= Seq::<Seq<int>>::empty());
    assert(u1.last() =~= seq![1int]);
    assert(run(init, u1, true) =~= seq![1int]);

    assert(u2.drop_last() =~= u1);
    assert(u2.last() =~= seq![2int]);
    assert(run(init, u2, true) =~= seq![2int]);

    assert(seq![seq![1int], seq![2int]][0] =~= seq![1int]);
    assert(seq![1int].len() == 1);
    assert(seq![1int][0] == 1int);
    assert(seq![1int].contains(1int));
    assert(!seq![2int].contains(1int));
}

} // verus!
