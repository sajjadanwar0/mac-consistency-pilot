//! verified_a1.rs -- runtime delegation to the Verus-verified detect_a1.
//!
//! This REPLACES the hand-mirrored `detect_a1` in `detectors.rs` with a thin
//! marshalling adapter around `verus_detector::detect_a1`, which is
//! mechanically verified SOUND and COMPLETE against the a1_witness spec
//! (lib_detect_a1_exec.rs: 9 verified, 0 errors, no assume/admit/external_body).
//!
//! WHY THIS CLOSES THE GAP (and what residual remains)
//!   Before: two copies of the A_1 search algorithm -- the verified Verus one
//!   and this crate's std-collections one -- kept in sync "by inspection."
//!   After: ONE verified algorithm, called directly. The detection logic is no
//!   longer duplicated. The only unverified code left on this path is the
//!   `to_oprec` conversion below, whose faithfulness rests on two documented
//!   correspondences, NOT on a re-implemented algorithm:
//!     1. String cells/values <-> usize via CONSISTENT interning -- the
//!        injective string->int map already trusted as
//!        axiom_string_to_int_injective in the refinement layer.
//!     2. BTreeMap (unique keys) <-> first-match Vec<(usize,usize)>: iterating
//!        the BTreeMap yields each (cell,value) once, so first-match over the
//!        resulting vector equals BTreeMap::get.
//!
//! BEHAVIOURAL NOTE (honest): soundness+completeness are preserved exactly --
//! this returns Some iff an A_1 witness exists. But it may return a DIFFERENT
//! valid witness than the old hand-written scan, because the verified detector
//! iterates the value-map order rather than the read_set order. Any returned
//! witness is still a genuine A_1 witness. Tests that assert a SPECIFIC witness
//! identity (e.g. detectors.rs::si_triage_replication checking w.i==2, w.j==1)
//! should assert `is_some()` / re-validate the returned witness rather than its
//! exact indices.
//!
//! BUILD: add `verus-detector` as a path dependency in this crate's Cargo.toml.
//! Verus `exec fn`s compile to ordinary Rust, so `verus_detector::detect_a1`
//! and `verus_detector::OpRec` are callable as normal items.

use std::collections::HashMap;

use crate::detectors::A1Witness;
use crate::oprecord::OpRecord;
use verus_detector::{detect_a1 as verified_detect_a1, OpRec};

/// Consistent string<->usize interning for one detection call. A fresh
/// interner per call keeps ids local and deterministic; equality of ids holds
/// iff the underlying strings are equal, which is the injectivity property the
/// verified detector's integer model assumes.
struct Interner {
    to_id: HashMap<String, usize>,
    to_str: Vec<String>,
}

impl Interner {
    fn new() -> Self {
        Self { to_id: HashMap::new(), to_str: Vec::new() }
    }

    fn id(&mut self, s: &str) -> usize {
        if let Some(&i) = self.to_id.get(s) {
            return i;
        }
        let i = self.to_str.len();
        self.to_id.insert(s.to_string(), i);
        self.to_str.push(s.to_string());
        i
    }

    fn name(&self, i: usize) -> String {
        self.to_str[i].clone()
    }
}

/// Convert one OpRecord into the verified detector's OpRec. The (cell,value)
/// pairs are taken from the VALUE maps (read_values / write_values), mirroring
/// the deployed detector's use of first_read_value / first_write_value: a cell
/// present in read_set but absent from read_values has no read value and so
/// never participates in an A_1 witness, exactly as before.
fn to_oprec(r: &OpRecord, intern: &mut Interner) -> OpRec {
    let read: Vec<(usize, usize)> = r
        .read_values
        .iter()
        .map(|(c, v)| (intern.id(c), intern.id(v)))
        .collect();
    let write: Vec<(usize, usize)> = r
        .write_values
        .iter()
        .map(|(c, v)| (intern.id(c), intern.id(v)))
        .collect();
    OpRec {
        read,
        read_time: r.read_time,
        write,
        write_time: r.write_time,
    }
}

/// A_1 detection via the verified algorithm. Sound and complete by the Verus
/// proof; the conversion above is the only unverified step.
pub fn detect_a1(h: &[OpRecord]) -> Option<A1Witness> {
    let mut intern = Interner::new();
    let recs: Vec<OpRec> = h.iter().map(|r| to_oprec(r, &mut intern)).collect();
    verified_detect_a1(&recs).map(|(i, j, c)| A1Witness {
        i,
        j,
        cell: intern.name(c),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::oprecord::OpRecord;
    use std::collections::BTreeMap;

    fn rec(rv: &[(&str, &str)], rt: u64, wv: &[(&str, &str)], wt: u64) -> OpRecord {
        OpRecord {
            agent: "a".to_string(),
            read_set: rv.iter().map(|(k, _)| k.to_string()).collect(),
            read_values: rv
                .iter()
                .map(|(k, v)| (k.to_string(), v.to_string()))
                .collect::<BTreeMap<_, _>>(),
            read_time: rt,
            write_set: wv.iter().map(|(k, _)| k.to_string()).collect(),
            write_values: wv
                .iter()
                .map(|(k, v)| (k.to_string(), v.to_string()))
                .collect::<BTreeMap<_, _>>(),
            write_time: wt,
            planned_tool: None,
            tools_used: vec![],
            tools_visible_at_read: vec![],
            io: wv.iter().map(|(k, v)| (k.to_string(), v.to_string())).collect(),
            co: wv.iter().map(|(k, v)| (k.to_string(), v.to_string())).collect(),
        }
    }

    #[test]
    fn delegated_a1_fires_on_stale_read() {
        // agent 0 reads c=NULL at t0, commits c=v1 at t2; agent 1 commits
        // c=v2 at t1 (in the window). Stale generation => A_1.
        let h = vec![
            rec(&[("c", "NULL")], 0, &[("c", "v1")], 2),
            rec(&[("c", "NULL")], 0, &[("c", "v2")], 1),
        ];
        assert!(detect_a1(&h).is_some());
    }

    #[test]
    fn delegated_a1_silent_on_clean_trace() {
        let h = vec![rec(&[("c", "NULL")], 0, &[("c", "v")], 1)];
        assert!(detect_a1(&h).is_none());
    }
}