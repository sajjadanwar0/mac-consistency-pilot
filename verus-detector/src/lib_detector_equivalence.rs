#![allow(unused_imports)]
use vstd::prelude::*;

verus! {
pub type CellId = u32;
pub type Value = u32;
pub type ToolId = u32;

pub open spec fn null_value() -> Value { 0u32 }

pub struct OpRecord {
    pub read_set: Vec<CellId>,
    pub read_values: Vec<(CellId, Value)>,
    pub read_time: u64,
    pub write_set: Vec<CellId>,
    pub write_values: Vec<(CellId, Value)>,
    pub write_time: u64,
    pub planned_tool: Option<ToolId>,
    pub tools_used: Vec<ToolId>,
    pub tools_visible_at_read: Vec<ToolId>,
    pub io_seq: Vec<(CellId, Value)>,
    pub co_seq: Vec<(CellId, Value)>,
}

pub open spec fn reads_spec(op: OpRecord, c: CellId) -> bool {
    exists |k: int| 0 <= k < op.read_set.len() && op.read_set[k] == c
}

pub open spec fn writes_spec(op: OpRecord, c: CellId) -> bool {
    exists |k: int| 0 <= k < op.write_set.len() && op.write_set[k] == c
}

pub open spec fn tool_visible_spec(op: OpRecord, t: ToolId) -> bool {
    exists |k: int| 0 <= k < op.tools_visible_at_read.len()
        && op.tools_visible_at_read[k] == t
}

pub open spec fn tool_used_spec(op: OpRecord, t: ToolId) -> bool {
    exists |k: int| 0 <= k < op.tools_used.len() && op.tools_used[k] == t
}

pub fn reads(op: &OpRecord, c: CellId) -> (r: bool)
    ensures r == reads_spec(*op, c)
{
    let n = op.read_set.len();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            n == op.read_set.len(),
            forall |m: int| 0 <= m < k as int ==> op.read_set[m] != c,
        decreases n - k
    {
        if op.read_set[k] == c {
            assert(op.read_set[k as int] == c);
            return true;
        }
        k += 1;
    }
    false
}

pub fn writes(op: &OpRecord, c: CellId) -> (r: bool)
    ensures r == writes_spec(*op, c)
{
    let n = op.write_set.len();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            n == op.write_set.len(),
            forall |m: int| 0 <= m < k as int ==> op.write_set[m] != c,
        decreases n - k
    {
        if op.write_set[k] == c {
            assert(op.write_set[k as int] == c);
            return true;
        }
        k += 1;
    }
    false
}

pub fn contains_tool(v: &Vec<ToolId>, t: ToolId) -> (r: bool)
    ensures r == (exists |k: int| 0 <= k < v.len() && v[k] == t)
{
    let n = v.len();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            n == v.len(),
            forall |m: int| 0 <= m < k as int ==> v[m] != t,
        decreases n - k
    {
        if v[k] == t {
            assert(v[k as int] == t);
            return true;
        }
        k += 1;
    }
    false
}

pub open spec fn first_match(s: Seq<(CellId, Value)>, c: CellId, k: int) -> bool {
    0 <= k < s.len()
    && s[k].0 == c
    && (forall |j: int| 0 <= j < k ==> s[j].0 != c)
}

pub open spec fn first_value(s: Seq<(CellId, Value)>, c: CellId) -> Option<Value> {
    if exists |k: int| first_match(s, c, k) {
        Some(s[choose |k: int| first_match(s, c, k)].1)
    } else {
        None
    }
}

proof fn lemma_first_match_unique(s: Seq<(CellId, Value)>, c: CellId, k1: int, k2: int)
    requires
        first_match(s, c, k1),
        first_match(s, c, k2),
    ensures k1 == k2
{
    if k1 < k2 {
        assert(s[k1].0 == c);
    }
    if k2 < k1 {
        assert(s[k2].0 == c);
    }
}

pub fn first_value_exec(s: &Vec<(CellId, Value)>, c: CellId) -> (r: Option<Value>)
    ensures r == first_value(s@, c)
{
    let n = s.len();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            n == s.len(),
            forall |m: int| 0 <= m < k as int ==> s@[m].0 != c,
        decreases n - k
    {
        if s[k].0 == c {
            assert(first_match(s@, c, k as int));
            assert(first_value(s@, c) == Some::<Value>(s@[k as int].1)) by {
                let k_chosen = choose |kc: int| first_match(s@, c, kc);
                lemma_first_match_unique(s@, c, k as int, k_chosen);
            };
            return Some(s[k].1);
        }
        k += 1;
    }
    assert(forall |k: int| !first_match(s@, c, k));
    None
}

pub open spec fn a1_witness(h: Seq<OpRecord>, i: int, j: int, c: CellId) -> bool {
    0 <= i < h.len()
    && 0 <= j < h.len()
    && i != j
    && reads_spec(h[i], c)
    && writes_spec(h[j], c)
    && h[i].read_time < h[j].write_time
    && h[j].write_time < h[i].write_time
    && {
        let rv = first_value(h[i].read_values@, c);
        let wv = first_value(h[j].write_values@, c);
        match (rv, wv) {
            (Some(r), Some(w)) => r != w,
            _ => false,
        }
    }
}

pub open spec fn a1(h: Seq<OpRecord>) -> bool {
    exists |i: int, j: int, c: CellId| a1_witness(h, i, j, c)
}

pub struct A1Witness {
    pub i: usize,
    pub j: usize,
    pub cell: CellId,
}

pub fn detect_a1(h: &Vec<OpRecord>) -> (result: Option<A1Witness>)
    ensures
        match result {
            Some(w) => {
                &&& w.i < h.len()
                &&& w.j < h.len()
                &&& a1_witness(h@, w.i as int, w.j as int, w.cell)
            }
            None => !a1(h@),
        }
{
    let n = h.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n, n == h.len(), n == h@.len(),
            forall |i2: int, j2: int, c2: CellId|
                0 <= i2 < i as int && 0 <= j2 < n as int
                ==> !a1_witness(h@, i2, j2, c2),
        decreases n - i
    {
        let mut j: usize = 0;
        while j < n
            invariant
                i < n, j <= n, n == h.len(), n == h@.len(),
                forall |i2: int, j2: int, c2: CellId|
                    0 <= i2 < i as int && 0 <= j2 < n as int
                    ==> !a1_witness(h@, i2, j2, c2),
                forall |j2: int, c2: CellId|
                    0 <= j2 < j as int
                    ==> !a1_witness(h@, i as int, j2, c2),
            decreases n - j
        {
            if i != j {
                let read_set_len = h[i].read_set.len();
                let mut k: usize = 0;
                while k < read_set_len
                    invariant
                        i < n, j < n, i != j,
                        k <= read_set_len,
                        n == h.len(), n == h@.len(),
                        read_set_len == h@[i as int].read_set.len(),
                        forall |i2: int, j2: int, c2: CellId|
                            0 <= i2 < i as int && 0 <= j2 < n as int
                            ==> !a1_witness(h@, i2, j2, c2),
                        forall |j2: int, c2: CellId|
                            0 <= j2 < j as int
                            ==> !a1_witness(h@, i as int, j2, c2),
                        forall |k2: int|
                            0 <= k2 < k as int
                            ==> !a1_witness(h@, i as int, j as int,
                                             h@[i as int].read_set[k2]),
                    decreases read_set_len - k
                {
                    let c = h[i].read_set[k];
                    assert(h@[i as int].read_set[k as int] == c);
                    assert(reads_spec(h@[i as int], c));

                    if writes(&h[j], c) {
                        assert(writes_spec(h@[j as int], c));
                        if h[i].read_time < h[j].write_time
                            && h[j].write_time < h[i].write_time
                        {
                            let rv = first_value_exec(&h[i].read_values, c);
                            let wv = first_value_exec(&h[j].write_values, c);
                            assert(rv == first_value(h@[i as int].read_values@, c));
                            assert(wv == first_value(h@[j as int].write_values@, c));
                            match (rv, wv) {
                                (Some(r_val), Some(w_val)) => {
                                    if r_val != w_val {
                                        assert(a1_witness(h@, i as int, j as int, c));
                                        return Some(A1Witness { i, j, cell: c });
                                    }
                                    // r_val == w_val: mismatch conjunct fails
                                    assert(!a1_witness(h@, i as int, j as int, c));
                                }
                                _ => {
                                    assert(!a1_witness(h@, i as int, j as int, c));
                                }
                            }
                        } else {
                            assert(!a1_witness(h@, i as int, j as int, c));
                        }
                    } else {
                        // !writes_spec
                        assert(!a1_witness(h@, i as int, j as int, c));
                    }
                    k += 1;
                }

                assert forall |c2: CellId|
                    !a1_witness(h@, i as int, j as int, c2)
                by {
                    if reads_spec(h@[i as int], c2) {
                        let k2 = choose |k2: int|
                            0 <= k2 < h@[i as int].read_set.len()
                            && h@[i as int].read_set[k2] == c2;
                        assert(0 <= k2 < read_set_len);
                        assert(h@[i as int].read_set[k2] == c2);
                    }
                };
            } else {
                assert forall |c2: CellId|
                    !a1_witness(h@, i as int, j as int, c2)
                by {};
            }
            j += 1;
        }
        i += 1;
    }

    assert(!a1(h@)) by {
        assert forall |i2: int, j2: int, c2: CellId|
            !a1_witness(h@, i2, j2, c2)
        by { };
    };
    None
}

pub open spec fn a2_witness(op: OpRecord) -> bool {
    match op.planned_tool {
        Some(t) => tool_visible_spec(op, t) && !tool_used_spec(op, t),
        None => false,
    }
}

pub open spec fn a2(h: Seq<OpRecord>) -> bool {
    exists |i: int| 0 <= i < h.len() && a2_witness(h[i])
}

pub fn detect_a2(h: &Vec<OpRecord>) -> (result: Option<usize>)
    ensures
        match result {
            Some(i) => i < h.len() && a2_witness(h@[i as int]),
            None => !a2(h@),
        }
{
    let n = h.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n, n == h.len(), n == h@.len(),
            forall |i2: int| 0 <= i2 < i as int ==> !a2_witness(h@[i2]),
        decreases n - i
    {
        match h[i].planned_tool {
            Some(t) => {
                let was_visible = contains_tool(&h[i].tools_visible_at_read, t);
                let was_used = contains_tool(&h[i].tools_used, t);
                if was_visible && !was_used {
                    assert(tool_visible_spec(h@[i as int], t));
                    assert(!tool_used_spec(h@[i as int], t));
                    assert(a2_witness(h@[i as int]));
                    return Some(i);
                }
                assert(!a2_witness(h@[i as int]));
            }
            None => {
                assert(!a2_witness(h@[i as int]));
            }
        }
        i += 1;
    }
    None
}

pub open spec fn a6_witness(op: OpRecord) -> bool {
    op.io_seq.len() > 0 && op.io_seq@ != op.co_seq@
}

pub open spec fn a6(h: Seq<OpRecord>) -> bool {
    exists |i: int| 0 <= i < h.len() && a6_witness(h[i])
}

fn seqs_equal(a: &Vec<(CellId, Value)>, b: &Vec<(CellId, Value)>) -> (r: bool)
    ensures r == (a@ == b@)
{
    if a.len() != b.len() {
        assert(a@.len() != b@.len());
        return false;
    }
    let n = a.len();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n, n == a.len(), a.len() == b.len(),
            forall |m: int| 0 <= m < k as int ==> a@[m] == b@[m],
        decreases n - k
    {
        if a[k].0 != b[k].0 || a[k].1 != b[k].1 {
            assert(a@[k as int] != b@[k as int]);
            return false;
        }
        k += 1;
    }
    assert(forall |m: int| 0 <= m < n as int ==> a@[m] == b@[m]);
    assert(a@ =~= b@);
    true
}

pub fn detect_a6(h: &Vec<OpRecord>) -> (result: Option<usize>)
    ensures
        match result {
            Some(i) => i < h.len() && a6_witness(h@[i as int]),
            None => !a6(h@),
        }
{
    let n = h.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n, n == h.len(), n == h@.len(),
            forall |i2: int| 0 <= i2 < i as int ==> !a6_witness(h@[i2]),
        decreases n - i
    {
        if h[i].io_seq.len() > 0 {
            let equal = seqs_equal(&h[i].io_seq, &h[i].co_seq);
            if !equal {
                assert(a6_witness(h@[i as int]));
                return Some(i);
            }
            assert(!a6_witness(h@[i as int]));
        } else {
            assert(!a6_witness(h@[i as int]));
        }
        i += 1;
    }
    None
}

pub open spec fn a3_witness(h: Seq<OpRecord>, j: int, c: CellId, v: Value) -> bool {
    0 <= j < h.len()
    && reads_spec(h[j], c)
    && first_value(h[j].read_values@, c) == Some(v)
    && v != null_value()
    && (forall |k: int|
        !(0 <= k < h.len()
          && k != j
          && writes_spec(h[k], c)
          && h[k].write_time <= h[j].read_time
          && first_value(h[k].write_values@, c) == Some(v)))
}

pub open spec fn a3(h: Seq<OpRecord>) -> bool {
    exists |j: int, c: CellId, v: Value| a3_witness(h, j, c, v)
}

pub struct A3Witness {
    pub j: usize,
    pub cell: CellId,
    pub value: Value,
}

pub fn detect_a3(h: &Vec<OpRecord>) -> (result: Option<A3Witness>)
    ensures
        match result {
            Some(w) => w.j < h.len() && a3_witness(h@, w.j as int, w.cell, w.value),
            None => !a3(h@),
        }
{
    let n = h.len();
    let mut j: usize = 0;
    while j < n
        invariant
            j <= n, n == h.len(), n == h@.len(),
            forall |j2: int, c2: CellId, v2: Value|
                0 <= j2 < j as int ==> !a3_witness(h@, j2, c2, v2),
        decreases n - j
    {
        let read_set_len = h[j].read_set.len();
        let mut q: usize = 0;
        while q < read_set_len
            invariant
                j < n, q <= read_set_len,
                n == h.len(), n == h@.len(),
                read_set_len == h@[j as int].read_set.len(),
                forall |j2: int, c2: CellId, v2: Value|
                    0 <= j2 < j as int ==> !a3_witness(h@, j2, c2, v2),
                forall |q2: int, v2: Value|
                    0 <= q2 < q as int
                    ==> !a3_witness(h@, j as int,
                                    h@[j as int].read_set[q2], v2),
            decreases read_set_len - q
        {
            let c = h[j].read_set[q];
            assert(h@[j as int].read_set[q as int] == c);
            assert(reads_spec(h@[j as int], c));

            let rv = first_value_exec(&h[j].read_values, c);
            assert(rv == first_value(h@[j as int].read_values@, c));

            match rv {
                Some(v) => {
                    if v != 0u32 {
                        assert(v != null_value());

                        let mut k: usize = 0;
                        let mut has_antecedent = false;

                        while k < n
                            invariant
                                j < n, k <= n,
                                n == h.len(), n == h@.len(),
                                !has_antecedent ==>
                                    (forall |k2: int|
                                        0 <= k2 < k as int && k2 != j as int ==>
                                        !(writes_spec(h@[k2], c)
                                          && h@[k2].write_time <= h@[j as int].read_time
                                          && first_value(h@[k2].write_values@, c) == Some(v))),
                                has_antecedent ==>
                                    (exists |k2: int|
                                        0 <= k2 < n as int && k2 != j as int
                                        && writes_spec(h@[k2], c)
                                        && h@[k2].write_time <= h@[j as int].read_time
                                        && first_value(h@[k2].write_values@, c) == Some(v)),
                            decreases n - k
                        {
                            if !has_antecedent && k != j {
                                if writes(&h[k], c) && h[k].write_time <= h[j].read_time {
                                    let wv = first_value_exec(&h[k].write_values, c);
                                    if wv == Some(v) {
                                        has_antecedent = true;
                                    }
                                }
                            }
                            k += 1;
                        }

                        if !has_antecedent {
                            assert(k == n);
                            assert(forall |k2: int|
                                0 <= k2 < h@.len() && k2 != j as int ==>
                                !(writes_spec(h@[k2], c)
                                  && h@[k2].write_time <= h@[j as int].read_time
                                  && first_value(h@[k2].write_values@, c) == Some(v)));
                            assert(a3_witness(h@, j as int, c, v));
                            return Some(A3Witness { j, cell: c, value: v });
                        }

                        assert forall |v2: Value| !a3_witness(h@, j as int, c, v2) by {
                        };
                    } else {
                        assert forall |v2: Value| !a3_witness(h@, j as int, c, v2) by {};
                    }
                }
                None => {
                    assert forall |v2: Value| !a3_witness(h@, j as int, c, v2) by {};
                }
            }
            q += 1;
        }

        assert forall |c2: CellId, v2: Value|
            !a3_witness(h@, j as int, c2, v2)
        by {
            if reads_spec(h@[j as int], c2) {
                let q2 = choose |q2: int|
                    0 <= q2 < h@[j as int].read_set.len()
                    && h@[j as int].read_set[q2] == c2;
                assert(0 <= q2 < read_set_len);
                assert(h@[j as int].read_set[q2] == c2);
            }
        };
        j += 1;
    }

    assert(!a3(h@)) by {
        assert forall |j2: int, c2: CellId, v2: Value|
            !a3_witness(h@, j2, c2, v2)
        by {};
    };
    None
}

proof fn smoke_test_a1_full(h: Seq<OpRecord>)
    requires
        h.len() == 2,
        h[0].read_set.len() == 1,
        h[0].read_set[0] == 1u32,
        h[0].read_values.len() == 1,
        h[0].read_values[0] == (1u32, 0u32),
        h[0].read_time == 0u64,
        h[0].write_time == 2u64,
        h[1].write_set.len() == 1,
        h[1].write_set[0] == 1u32,
        h[1].write_values.len() == 1,
        h[1].write_values[0] == (1u32, 7u32),
        h[1].write_time == 1u64,
    ensures a1(h)
{
    assert(reads_spec(h[0], 1u32)) by {
        assert(h[0].read_set[0int] == 1u32);
    }
    assert(writes_spec(h[1], 1u32)) by {
        assert(h[1].write_set[0int] == 1u32);
    }
    assert(first_match(h[0].read_values@, 1u32, 0)) by {
        assert(h[0].read_values[0int] == (1u32, 0u32));
    }
    assert(first_match(h[1].write_values@, 1u32, 0)) by {
        assert(h[1].write_values[0int] == (1u32, 7u32));
    }
    assert(first_value(h[0].read_values@, 1u32) == Some(0u32));
    assert(first_value(h[1].write_values@, 1u32) == Some(7u32));
    assert(a1_witness(h, 0, 1, 1u32));
}

}  // verus!

fn main() { }