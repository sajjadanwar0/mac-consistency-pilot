// =====================================================================
// Verus proof: Probabilistic refinement of the A_1 (stale-generation) predicate.
//
// COMPILE
//   verus --crate-type=lib src/lib_probabilistic_a1.rs
//
// MOTIVATION
//   The deterministic A_1 predicate of lib.rs uses a string-level
//   comparison r1.read_values[c] != r2.write_values[c] to detect stale
//   reads. Under stochastic LLM generation, this comparison is too
//   strict in one direction (string differences may have no operational
//   effect) and too lax in another (string equality does not preclude
//   distributional divergence). This file develops a probabilistic
//   refinement: an abstract disagreement_probability function captures
//   the probability that an agent receiving a stale value rather than
//   a fresh one produces a different downstream output. The
//   deterministic detector is then proved to be a SOUND OVER-APPROXIMATION
//   of the probabilistic predicate: every probabilistic A_1 event is
//   also a deterministic A_1 event, but not vice versa.
//
//   We additionally model an empirical estimator (re-running the agent's
//   prompt k times with the fresh value substituted) and prove that
//   under a Hoeffding-style concentration assumption, the empirical
//   estimator is sound for the probabilistic predicate.
//
// SCORECARD (target)
//   Three foundational axioms specific to this file:
//     - axiom_disagreement_is_percentage
//     - axiom_equal_values_zero_disagreement
//     - axiom_empirical_concentration
//   Zero external_body on safety-bearing proof bodies.

#![allow(unused_imports)]
#![allow(dead_code)]
use vstd::prelude::*;

verus! {

// =====================================================================
// Section 1: Carriers
// =====================================================================

pub type CellId = int;
pub type AgentId = int;
pub type Value = int;
pub type Time = int;

/// A unique identifier for an agent's invocation context, used as the
/// argument to the disagreement function. Operationally this corresponds
/// to a hash or sequence number identifying which prompt-execution
/// context we are reasoning about.
pub type PromptId = int;

pub struct OpRecord {
    pub agent: AgentId,
    pub read_set: Set<CellId>,
    pub read_values: Map<CellId, Value>,
    pub read_time: Time,
    pub write_set: Set<CellId>,
    pub write_values: Map<CellId, Value>,
    pub write_time: Time,
    /// Identifies the prompt-execution context for the disagreement
    /// function. Distinct OpRecords have distinct prompt ids unless
    /// they share the exact same agent invocation context.
    pub prompt: PromptId,
}

pub struct Trace {
    pub records: Seq<OpRecord>,
}

// =====================================================================
// Section 2: Disagreement probability (abstract spec)
// =====================================================================

/// disagreement_probability(p, v_stale, v_fresh) returns the
/// percentage probability (0..=100) that an agent in prompt-context p,
/// having observed value v_stale for cell c, would have produced a
/// different downstream output if it had observed v_fresh instead.
///
/// This is abstract over the LLM implementation. Operationally one
/// can estimate it by re-running the prompt with v_fresh substituted
/// for v_stale k times and counting the fraction of outputs that
/// differ from the actual output (see Section 6 for the empirical
/// estimator and its concentration bound).
pub uninterp spec fn disagreement_probability(
    p: PromptId,
    v_stale: Value,
    v_fresh: Value,
) -> nat;

/// Axiom 1: the disagreement probability is a percentage in [0, 100].
#[verifier::external_body]
pub broadcast proof fn axiom_disagreement_is_percentage(
    p: PromptId, v1: Value, v2: Value,
)
    ensures
        #![trigger disagreement_probability(p, v1, v2)]
        disagreement_probability(p, v1, v2) <= 100,
{
}

/// Axiom 2: if the stale value EQUALS the fresh value, there is no
/// possible disagreement. This is the key bridge between the
/// deterministic detector's string comparison and the operational
/// disagreement: string equality forces operational equivalence.
#[verifier::external_body]
pub broadcast proof fn axiom_equal_values_zero_disagreement(
    p: PromptId, v: Value,
)
    ensures
        #![trigger disagreement_probability(p, v, v)]
        disagreement_probability(p, v, v) == 0,
{
}

// =====================================================================
// Section 3: Deterministic A_1 predicate (compatible with lib.rs)
// =====================================================================

/// The classical, string-level A_1 predicate. A trace exhibits
/// deterministic A_1 if there is a pair (i, j) of records and a cell c
/// such that record i read c before record j wrote c, and the recorded
/// values differ syntactically.
pub open spec fn a1_deterministic(t: Trace) -> bool {
    exists |i: int, j: int, c: CellId|
        #![trigger t.records[i].read_set.contains(c), t.records[j].write_set.contains(c)]
        0 <= i < t.records.len()
        && 0 <= j < t.records.len()
        && t.records[j].write_time > t.records[i].read_time
        && t.records[i].read_set.contains(c)
        && t.records[j].write_set.contains(c)
        && t.records[i].read_values[c] != t.records[j].write_values[c]
}

// =====================================================================
// Section 4: Probabilistic A_1 predicate
// =====================================================================

/// The probabilistic A_1 predicate at threshold theta. A trace
/// exhibits probabilistic A_1 if the same structural conditions hold
/// AND the operational disagreement probability for the witness pair
/// exceeds theta percent. At theta = 0, ANY non-zero disagreement
/// fires the predicate; at theta = 100, only certain disagreement
/// fires.
pub open spec fn a1_probabilistic(t: Trace, theta: nat) -> bool {
    exists |i: int, j: int, c: CellId|
        #![trigger t.records[i].read_set.contains(c), t.records[j].write_set.contains(c)]
        0 <= i < t.records.len()
        && 0 <= j < t.records.len()
        && t.records[j].write_time > t.records[i].read_time
        && t.records[i].read_set.contains(c)
        && t.records[j].write_set.contains(c)
        && disagreement_probability(
              t.records[i].prompt,
              t.records[i].read_values[c],
              t.records[j].write_values[c],
           ) > theta
}

// =====================================================================
// Section 5: Refinement theorems
// =====================================================================

/// THEOREM 1 (Soundness of the deterministic detector for the
/// probabilistic predicate). If the probabilistic A_1 predicate fires
/// at threshold 0, then the deterministic A_1 predicate also fires.
/// Operationally: any trace flagged by the probabilistic predicate
/// (under any non-zero disagreement) is also flagged by the
/// deterministic detector. The deterministic detector therefore
/// over-approximates the probabilistic predicate from above: it is a
/// sound screen.
pub proof fn lemma_prob_implies_det_at_zero(t: Trace)
    requires a1_probabilistic(t, 0),
    ensures a1_deterministic(t),
{
    broadcast use axiom_equal_values_zero_disagreement;
    broadcast use axiom_disagreement_is_percentage;

    let (i, j, c) = choose |i: int, j: int, c: CellId|
        0 <= i < t.records.len()
        && 0 <= j < t.records.len()
        && t.records[j].write_time > t.records[i].read_time
        && #[trigger] t.records[i].read_set.contains(c)
        && #[trigger] t.records[j].write_set.contains(c)
        && disagreement_probability(
              t.records[i].prompt,
              t.records[i].read_values[c],
              t.records[j].write_values[c],
           ) > 0;

    let v_stale = t.records[i].read_values[c];
    let v_fresh = t.records[j].write_values[c];
    let p = t.records[i].prompt;

    // If the values were equal, the disagreement probability would be
    // zero, contradicting the witness.
    if v_stale == v_fresh {
        axiom_equal_values_zero_disagreement(p, v_stale);
        assert(disagreement_probability(p, v_stale, v_stale) == 0);
        assert(false);
    }
    assert(v_stale != v_fresh);

    // The deterministic predicate's witness is the same (i, j, c).
    assert(t.records[i].read_set.contains(c));
    assert(t.records[j].write_set.contains(c));
    assert(t.records[i].read_values[c] != t.records[j].write_values[c]);
}

/// THEOREM 2 (Monotonicity in theta). If the probabilistic predicate
/// fires at a higher threshold, it also fires at any lower threshold.
/// Operationally: a more permissive threshold catches more events.
pub proof fn lemma_a1_prob_monotone(t: Trace, theta_low: nat, theta_high: nat)
    requires theta_low < theta_high, a1_probabilistic(t, theta_high),
    ensures a1_probabilistic(t, theta_low),
{
    let (i, j, c) = choose |i: int, j: int, c: CellId|
        0 <= i < t.records.len()
        && 0 <= j < t.records.len()
        && t.records[j].write_time > t.records[i].read_time
        && #[trigger] t.records[i].read_set.contains(c)
        && #[trigger] t.records[j].write_set.contains(c)
        && disagreement_probability(
              t.records[i].prompt,
              t.records[i].read_values[c],
              t.records[j].write_values[c],
           ) > theta_high;

    // The same witness (i, j, c) works for theta_low because
    // disagreement > theta_high > theta_low.
    assert(disagreement_probability(
              t.records[i].prompt,
              t.records[i].read_values[c],
              t.records[j].write_values[c],
           ) > theta_low);
}

/// THEOREM 3 (Contrapositive form of soundness). If the deterministic
/// detector does NOT fire, then the probabilistic predicate does not
/// fire at threshold 0. Equivalent to Theorem 1 by contraposition;
/// stated explicitly because it is the form that practitioners use:
/// "the deterministic detector is sufficient to certify the absence of
/// probabilistic A_1 events."
pub proof fn lemma_det_negative_implies_prob_negative(t: Trace)
    requires !a1_deterministic(t),
    ensures !a1_probabilistic(t, 0),
{
    if a1_probabilistic(t, 0) {
        lemma_prob_implies_det_at_zero(t);
        assert(a1_deterministic(t));
        assert(false);
    }
}

// =====================================================================
// Section 6: Empirical estimator and its concentration bound
// =====================================================================

/// empirical_disagreement_count(p, v_stale, v_fresh, k) is the number
/// of sample re-runs (out of k total) in which the agent's output with
/// v_fresh substituted differs from its output with v_stale. The
/// empirical estimator is empirical_count / k (as a percentage,
/// empirical_count * 100 / k).
pub uninterp spec fn empirical_disagreement_count(
    p: PromptId,
    v_stale: Value,
    v_fresh: Value,
    k: nat,
) -> nat;

/// Axiom 3 (Hoeffding-style concentration). For k >= 100 samples, the
/// empirical estimator's percentage is within 10 percentage points of
/// the true disagreement probability. This is a deliberately loose
/// bound chosen to be axiomatized rather than proved; it captures the
/// essential property that as k grows, the empirical estimate
/// converges to the true probability. A formal Hoeffding bound in
/// Verus would require the sampling axioms developed in the
/// probabilistic-Verus literature (out of scope here).
///
/// Formally: for k >= 100, |emp_count * 100 - k * disagreement| <= 10 * k.
#[verifier::external_body]
pub broadcast proof fn axiom_empirical_concentration(
    p: PromptId, v1: Value, v2: Value, k: nat,
)
    requires k >= 100,
    ensures
        #![trigger empirical_disagreement_count(p, v1, v2, k)]
        empirical_disagreement_count(p, v1, v2, k) * 100
            <= k * disagreement_probability(p, v1, v2) + 10 * k,
        k * disagreement_probability(p, v1, v2)
            <= empirical_disagreement_count(p, v1, v2, k) * 100 + 10 * k,
{
}

/// The empirical A_1 predicate at threshold theta and sample size k.
/// Mirrors the structure of a1_probabilistic but uses the empirical
/// estimator in place of the abstract disagreement probability.
pub open spec fn a1_empirical(t: Trace, theta: nat, k: nat) -> bool {
    exists |i: int, j: int, c: CellId|
        #![trigger t.records[i].read_set.contains(c), t.records[j].write_set.contains(c)]
        0 <= i < t.records.len()
        && 0 <= j < t.records.len()
        && t.records[j].write_time > t.records[i].read_time
        && t.records[i].read_set.contains(c)
        && t.records[j].write_set.contains(c)
        && empirical_disagreement_count(
              t.records[i].prompt,
              t.records[i].read_values[c],
              t.records[j].write_values[c],
              k,
           ) * 100 > k * theta
}

/// THEOREM 4 (Soundness of the empirical estimator). If the empirical
/// estimator fires at threshold (theta + 10) with sample size k >= 100,
/// then the true probabilistic predicate fires at threshold theta.
/// In words: empirical detection at a slightly inflated threshold
/// implies true detection at the original threshold, with the
/// inflation absorbing the 10-percentage-point sampling error.
pub proof fn lemma_empirical_sound(t: Trace, theta: nat, k: nat)
    requires
        k >= 100,
        a1_empirical(t, theta + 10, k),
    ensures a1_probabilistic(t, theta),
{
    broadcast use axiom_empirical_concentration;
    broadcast use axiom_disagreement_is_percentage;

    let (i, j, c) = choose |i: int, j: int, c: CellId|
        0 <= i < t.records.len()
        && 0 <= j < t.records.len()
        && t.records[j].write_time > t.records[i].read_time
        && #[trigger] t.records[i].read_set.contains(c)
        && #[trigger] t.records[j].write_set.contains(c)
        && empirical_disagreement_count(
              t.records[i].prompt,
              t.records[i].read_values[c],
              t.records[j].write_values[c],
              k,
           ) * 100 > k * (theta + 10);

    let p = t.records[i].prompt;
    let v_stale = t.records[i].read_values[c];
    let v_fresh = t.records[j].write_values[c];

    // Empirical count * 100 > k * (theta + 10). Distribute the RHS so
    // Verus sees k * theta + 10 * k explicitly. The concentration
    // axiom then gives k * disagreement >= emp * 100 - 10 * k.
    // Combining:
    //   k * disagreement + 10 * k >= emp * 100 > k * theta + 10 * k
    // which yields k * disagreement > k * theta, and since k > 0,
    // disagreement > theta.
    let emp = empirical_disagreement_count(p, v_stale, v_fresh, k);
    assert(emp * 100 > k * (theta + 10));

    // Distributivity: k * (theta + 10) == k * theta + 10 * k.
    assert(k * (theta + 10) == k * theta + k * 10) by (nonlinear_arith);
    assert(k * 10 == 10 * k) by (nonlinear_arith);
    assert(k * (theta + 10) == k * theta + 10 * k);

    axiom_empirical_concentration(p, v_stale, v_fresh, k);
    // The axiom's second ensures clause:
    //   k * disagreement <= emp * 100 + 10 * k
    // is the side we DON'T need here. The first one:
    //   emp * 100 <= k * disagreement + 10 * k
    // is what we use. So: emp * 100 <= k * disagreement + 10 * k,
    // and we have emp * 100 > k * theta + 10 * k. Chaining:
    assert(emp * 100 <= k * disagreement_probability(p, v_stale, v_fresh) + 10 * k);
    assert(k * disagreement_probability(p, v_stale, v_fresh) + 10 * k > k * theta + 10 * k);

    // Subtract 10 * k from both sides (linear arithmetic over int).
    assert(k * disagreement_probability(p, v_stale, v_fresh) > k * theta);

    // Since k >= 100 > 0, divide both sides by k.
    assert(k >= 100);
    assert(k > 0);
    if disagreement_probability(p, v_stale, v_fresh) <= theta {
        // d <= theta and k > 0 implies k*d <= k*theta. Use nonlinear
        // because multiplication is involved.
        assert(k * disagreement_probability(p, v_stale, v_fresh) <= k * theta)
            by (nonlinear_arith)
            requires disagreement_probability(p, v_stale, v_fresh) <= theta, k > 0;
        assert(false);
    }
    assert(disagreement_probability(p, v_stale, v_fresh) > theta);
}

/// THEOREM 5 (Empirical sufficiency for sound detection). At
/// theta = 0 and k >= 100, if the deterministic detector does not
/// fire, neither does the empirical estimator with at least 10% of
/// samples showing disagreement (the empirical theta = 10 threshold
/// chosen to absorb sampling error). In words: the deterministic
/// detector is sufficient to certify the absence of practically-
/// significant A_1 events under sampling.
pub proof fn lemma_det_negative_implies_emp_negative(t: Trace, k: nat)
    requires k >= 100, !a1_deterministic(t),
    ensures !a1_empirical(t, 10, k),
{
    if a1_empirical(t, 10, k) {
        lemma_empirical_sound(t, 0, k);
        assert(a1_probabilistic(t, 0));
        lemma_prob_implies_det_at_zero(t);
        assert(a1_deterministic(t));
        assert(false);
    }
}

} // verus!