//! measure_l2_unified.rs — unified A3-prevention measurement.
//!
//! PURPOSE. Closes the "two artifacts of one protocol" gap of paper §5.12.
//! The PREVENTION arm is measured on the *exec-mode-verified* runtime
//! `lib_l2_exec::L2Runtime` — so the artifact we measure IS the artifact we
//! verify. The BASELINE arm is a deliberately-unverified no-cascade foil: the
//! L1-class counterfactual that must still exhibit A3.
//!
//! WHY THIS IS HONEST. (1) Verus erases `requires`/`ensures` in compiled
//! output, so this plain-Rust driver can call L2Runtime's methods directly.
//! (2) The cascade chain only ever commits *valid* transactions (each
//! dependent reads a just-committed fresh value and has clean predecessors),
//! so every call stays inside the verified contract — we are not exercising
//! out-of-contract behavior. (3) The A3 outcome is structural, not value- or
//! seed-dependent; the seed only perturbs payloads (as in l2_causal.rs's
//! run_one), so the per-depth rate is exact and the 1000-run denominator just
//! matches the paper's reported figure.
//!
//! PLACEMENT. This is plain Rust and must live OUTSIDE any `verus!{}` block.
//! Easiest: drop it in the verus-detector crate as `tests/measure_l2_unified.rs`
//! (an integration test) or `src/bin/measure_l2_unified.rs`, ensure lib.rs has
//! `pub mod lib_l2_exec;`, and import via the crate name (here `verus_detector`).
//! Add the `has_a3_witness` method to `impl L2Runtime` (see the accompanying
//! snippet) before building.
//!
//! RUN.  cargo test --release measure_l2_prevention -- --nocapture
//!   or  cargo run  --release --bin measure_l2_unified

use verus_detector::lib_l2_exec::L2Runtime;

/// One depth-`depth` causal cascade on the VERIFIED runtime. Mirrors
/// l2_causal.rs::run_one exactly: a root writes cell 0 and commits; each
/// dependent reads the previous cell (acquiring the chain as predecessors) and
/// writes the next cell; then the root is aborted (saga compensation) and the
/// cascade discipline propagates. Returns whether an A3 witness survives —
/// which must be `false`, because every wf L2Runtime state is a3_free.
fn verified_cascade(seed: u64, depth: u64) -> bool {
    assert!(depth >= 2, "need a root plus at least one dependent");
    let mut rt = L2Runtime::new();

    let root = rt.begin();
    rt.write(root, 0, 1 + seed % 7); // cell 0 := payload (value irrelevant to A3)
    rt.commit(root);

    let mut prev: u64 = 0;
    let mut d: u64 = 1;
    while d < depth {
        let t = rt.begin();
        rt.read(t, prev); // acquires prev's writer (and its closure) as predecessors
        rt.write(t, d, 100 + d + seed % 5);
        rt.commit(t);
        prev = d;
        d += 1;
    }

    // Saga compensation rolls the root back after the chain committed.
    rt.abort(root); // cascade discipline (the verified path)

    rt.has_a3_witness()
}

/// The no-cascade L1-class baseline foil (deliberately unverified): commit the
/// whole chain, then abort ONLY the root without cascading. Surviving
/// dependents retain the aborted root in their predecessor closure -> A3.
/// This is the exec image of l2_causal.rs with `AbortPolicy::NoCascade`, made
/// self-contained so the harness needs no cross-crate dependency for the foil.
fn baseline_cascade(_seed: u64, depth: u64) -> bool {
    assert!(depth >= 2);
    // (txn_id, committed, aborted, predecessor closure)
    let mut txns: Vec<(u64, bool, bool, Vec<u64>)> = Vec::new();
    txns.push((0, true, false, Vec::new())); // root
    let mut closure: Vec<u64> = vec![0];
    let mut d: u64 = 1;
    while d < depth {
        txns.push((d, true, false, closure.clone())); // dependent d
        closure.push(d);
        d += 1;
    }
    txns[0].2 = true; // abort root, NO cascade

    // detect_a3_cascade: a committed, non-aborted record retaining an aborted
    // predecessor (paper Def. 3 / a3_witness lifted to the trace).
    let aborted: std::collections::BTreeSet<u64> =
        txns.iter().filter(|t| t.2).map(|t| t.0).collect();
    txns.iter()
        .any(|t| t.1 && !t.2 && t.3.iter().any(|p| aborted.contains(p)))
}

fn run_measurement() {
    for &depth in &[2u64, 3, 5] {
        let mut verified_pos = 0u32;
        let mut baseline_pos = 0u32;
        for s in 0..1000u64 {
            let seed = s.wrapping_mul(2_654_435_761);
            if verified_cascade(seed, depth) {
                verified_pos += 1;
            }
            if baseline_cascade(seed, depth) {
                baseline_pos += 1;
            }
        }
        println!(
            "depth={}  verified-L2 A3 = {}/1000 ({:.0}%)   baseline A3 = {}/1000 ({:.0}%)",
            depth,
            verified_pos,
            verified_pos as f64 / 10.0,
            baseline_pos,
            baseline_pos as f64 / 10.0,
        );
        assert_eq!(verified_pos, 0, "verified L2 runtime must prevent A3 at depth {depth}");
        assert_eq!(baseline_pos, 1000, "no-cascade baseline must exhibit A3 at depth {depth}");
    }
}

// As an integration test:
#[test]
fn measure_l2_prevention() {
    run_measurement();
}

// As a binary (if placed in src/bin/):
#[allow(dead_code)]
fn main() {
    run_measurement();
}