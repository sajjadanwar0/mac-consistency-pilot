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

                    let writes_c = has_cell(&h[j].write, c);
                    let tw_ok = h[i].read_time < h[j].write_time
                                && h[j].write_time < h[i].write_time;
                    let rv = lookup(&h[i].read, c);
                    let wv = lookup(&h[j].write, c);

                    assert(spec_has_cell(h@[i as int].read@, c)) by {
                        assert(h@[i as int].read@[p as int].0 == c);
                    }

                    if writes_c && tw_ok && rv != wv {
                        return Some((i, j, c));
                    }

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