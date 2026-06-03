// lib_detect_a1_exec.rs
//
// Verified EXEC-mode A_1 detector. This is the deployed algorithm from
// mac-consistency-runtime/src/detectors.rs::detect_a1, written as a Verus
// `exec fn` and proven SOUND and COMPLETE against the a1_witness spec
// predicate (the same predicate lib_l2_safety.rs reasons about). It closes
// the model-vs-implementation gap for the detector: instead of two
// hand-mirrored copies kept in sync "by inspection" (deployed Rust + Verus
// twin), there is ONE exec function whose loop structure is the deployed
// search and whose result is mechanically tied to the predicate.
//
// CORRESPONDENCE TO THE DEPLOYED CODE (the only residual, stated not hidden)
//   1. Cells/values are integers here; deployed uses interned Strings. The
//      correspondence is the injective string->int interning already trusted
//      as axiom_string_to_int_injective in the refinement layer -- not new.
//   2. Deployed read_values/write_values are BTreeMaps (unique keys);
//      BTreeMap::get(c) equals first-match lookup over a (cell,value) vector
//      under the dup-free-key invariant the BTreeMap enforces (carried here as
//      wf_keys). The proof below uses first-match throughout, so it does not
//      even rely on uniqueness; wf_keys only documents the BTreeMap<->vector
//      correspondence for the deployed instantiation.
//   3. The deployed code computes the read/write values lazily inside the
//      time-window branch; this version computes them eagerly. Lookups are
//      pure, so the returned result is identical; eager computation only makes
//      the values available to the completeness proof.
//   Everything else -- the (i,j) scan, the i!=j guard, the read-set walk, the
//   time-window test read_time_i < write_time_j < write_time_i, and the
//   value-inequality test -- is the deployed detect_a1.
//
// NO axiom, NO assume, NO admit, NO external_body in this file.

use vstd::prelude::*;

verus! {

pub type Cell = usize;
pub type Val = usize;

pub struct OpRec {
    pub read: Vec<(Cell, Val)>,
    pub read_time: u64,
    pub write: Vec<(Cell, Val)>,
    pub write_time: u64,
}

// =====================================================================
// Spec layer
// =====================================================================

pub open spec fn spec_lookup(s: Seq<(Cell, Val)>, c: Cell) -> Option<Val>
    decreases s.len()
{
    if s.len() == 0 {
        None
    } else if s[0].0 == c {
        Some(s[0].1)
    } else {
        spec_lookup(s.subrange(1, s.len() as int), c)
    }
}

pub open spec fn spec_has_cell(s: Seq<(Cell, Val)>, c: Cell) -> bool {
    exists|k: int| 0 <= k < s.len() && s[k].0 == c
}

pub open spec fn wf_keys(s: Seq<(Cell, Val)>) -> bool {
    forall|a: int, b: int|
        0 <= a < s.len() && 0 <= b < s.len() && s[a].0 == s[b].0 ==> a == b
}

pub open spec fn wf_rec(r: OpRec) -> bool {
    wf_keys(r.read@) && wf_keys(r.write@)
}

pub open spec fn wf_hist(h: Seq<OpRec>) -> bool {
    forall|k: int| 0 <= k < h.len() ==> wf_rec(h[k])
}

/// A_1 (stale-generation) witness at indices (i,j) and cell c.
pub open spec fn is_a1_witness(h: Seq<OpRec>, i: int, j: int, c: Cell) -> bool {
    &&& 0 <= i < h.len()
    &&& 0 <= j < h.len()
    &&& i != j
    &&& spec_has_cell(h[i].read@, c)
    &&& spec_has_cell(h[j].write@, c)
    &&& h[i].read_time < h[j].write_time
    &&& h[j].write_time < h[i].write_time
    &&& spec_lookup(h[i].read@, c) != spec_lookup(h[j].write@, c)
}

// =====================================================================
// Verified exec helpers
// =====================================================================

pub fn lookup(v: &Vec<(Cell, Val)>, c: Cell) -> (r: Option<Val>)
    ensures r == spec_lookup(v@, c)
{
    let n = v.len();
    proof {
        assert(v@.subrange(0, n as int) =~= v@);
    }
    let mut k: usize = 0;
    while k < n
        invariant
            0 <= k <= n,
            n == v@.len(),
            spec_lookup(v@, c) == spec_lookup(v@.subrange(k as int, n as int), c),
        decreases n - k
    {
        assert(v@.subrange(k as int, n as int).len() > 0);
        assert(v@.subrange(k as int, n as int)[0] == v@[k as int]);
        if v[k].0 == c {
            return Some(v[k].1);
        }
        assert(v@.subrange(k as int, n as int).subrange(1, (n - k) as int)
               == v@.subrange((k + 1) as int, n as int));
        k = k + 1;
    }
    assert(v@.subrange(k as int, n as int).len() == 0);
    None
}

pub fn has_cell(v: &Vec<(Cell, Val)>, c: Cell) -> (b: bool)
    ensures b == spec_has_cell(v@, c)
{
    let n = v.len();
    let mut k: usize = 0;
    while k < n
        invariant
            0 <= k <= n,
            n == v@.len(),
            forall|t: int| 0 <= t < k ==> v@[t].0 != c,
        decreases n - k
    {
        if v[k].0 == c {
            assert(v@[k as int].0 == c);
            return true;
        }
        k = k + 1;
    }
    false
}

// =====================================================================
// detect_a1: SOUND + COMPLETE
// =====================================================================

pub fn detect_a1(h: &Vec<OpRec>) -> (res: Option<(usize, usize, Cell)>)
    requires wf_hist(h@)
    ensures
        match res {
            Some((i, j, c)) => is_a1_witness(h@, i as int, j as int, c),
            None => forall|i: int, j: int, c: Cell| !is_a1_witness(h@, i, j, c),
        }
{
    let n = h.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == h@.len(),
            forall|i2: int, j2: int, c2: Cell|
                0 <= i2 < i ==> !is_a1_witness(h@, i2, j2, c2),
        decreases n - i
    {
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= i < n,
                0 <= j <= n,
                n == h@.len(),
                forall|i2: int, j2: int, c2: Cell|
                    0 <= i2 < i ==> !is_a1_witness(h@, i2, j2, c2),
                forall|j2: int, c2: Cell|
                    0 <= j2 < j ==> !is_a1_witness(h@, i as int, j2, c2),
            decreases n - j
        {
            if i != j {
                let m = h[i].read.len();
                let mut p: usize = 0;
                while p < m
                    invariant
                        0 <= i < n,
                        0 <= j < n,
                        i != j,
                        0 <= p <= m,
                        n == h@.len(),
                        m == h@[i as int].read@.len(),
                        forall|c2: Cell|
                            (exists|t: int| 0 <= t < p && h@[i as int].read@[t].0 == c2)
                            ==> !is_a1_witness(h@, i as int, j as int, c2),
                    decreases m - p
                {
                    let c = h[i].read[p].0;

                    // Persistent facts linking exec checks to the spec.
                    let writes_c = has_cell(&h[j].write, c);   // == spec_has_cell(write_j, c)
                    let tw_ok = h[i].read_time < h[j].write_time
                                && h[j].write_time < h[i].write_time;
                    let rv = lookup(&h[i].read, c);             // == spec_lookup(read_i, c)
                    let wv = lookup(&h[j].write, c);            // == spec_lookup(write_j, c)

                    // c is a read cell of i (witnessed at index p).
                    assert(spec_has_cell(h@[i as int].read@, c)) by {
                        assert(h@[i as int].read@[p as int].0 == c);
                    }

                    if writes_c && tw_ok && rv != wv {
                        // Soundness: every conjunct of is_a1_witness holds.
                        return Some((i, j, c));
                    }

                    // Completeness for this cell: not reaching the return means
                    // !writes_c, or !tw_ok, or rv == wv -- each falsifies a
                    // conjunct of is_a1_witness(i,j,c).
                    assert(!is_a1_witness(h@, i as int, j as int, c)) by {
                        if !writes_c {
                            assert(!spec_has_cell(h@[j as int].write@, c));
                        } else if !tw_ok {
                            assert(!(h@[i as int].read_time < h@[j as int].write_time
                                     && h@[j as int].write_time < h@[i as int].write_time));
                        } else {
                            assert(rv == wv);
                            assert(spec_lookup(h@[i as int].read@, c)
                                   == spec_lookup(h@[j as int].write@, c));
                        }
                    }
                    p = p + 1;
                }
                // No witness at (i, j) for ANY cell: is_a1_witness(i,j,c2)
                // requires c2 to be a read cell of i, all of which were scanned.
                assert forall|c2: Cell| !is_a1_witness(h@, i as int, j as int, c2) by {
                    if is_a1_witness(h@, i as int, j as int, c2) {
                        assert(spec_has_cell(h@[i as int].read@, c2));
                        let t = choose|t: int|
                            0 <= t < h@[i as int].read@.len()
                            && h@[i as int].read@[t].0 == c2;
                        assert(0 <= t < m);
                    }
                }
            } else {
                assert forall|c2: Cell| !is_a1_witness(h@, i as int, j as int, c2) by {}
            }
            j = j + 1;
        }
        i = i + 1;
    }
    None
}

} // verus!