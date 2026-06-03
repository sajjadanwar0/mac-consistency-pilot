// lib_pessimistic_exec.rs
//
// Verified EXEC-mode pessimistic acquisition gate. This is the begin-time
// check from mac-consistency-runtime/src/pessimistic.rs::begin, written as a
// Verus `exec fn` and proven SOUND and COMPLETE against the no-foreign-holder
// predicate. `begin` grants exclusive access only if none of the requested
// cells is currently held by a DIFFERENT agent; that exclusivity is what
// prevents A_1 at the pessimistic-locking layer (no two agents operate on one
// cell in the same window).
//
// CORRESPONDENCE TO THE DEPLOYED CODE (residual, stated not hidden)
//   1. Deployed cell_holders is HashMap<CellId, String>; here it is an assoc
//      Vec<(Cell, Agent)> with unique cell keys, so first-match lookup equals
//      HashMap::get under the dup-free-key invariant the map enforces.
//   2. Cells/agents are integers; deployed uses interned Strings
//      (axiom_string_to_int_injective).
//   3. The surrounding critical section uses parking_lot::Mutex, a RustBelt-
//      class lock bounded by the GenMC/RC11 check.
//   The acquisition LOGIC -- scan the requested cells, deny if any has a
//   foreign holder -- is the deployed `begin` check, now mechanically tied to
//   the predicate.
//
// NO axiom, NO assume, NO admit, NO external_body in this file.

use vstd::prelude::*;

verus! {

pub type Cell = usize;
pub type Agent = usize;

// =====================================================================
// Spec layer
// =====================================================================

/// First agent paired with cell `c` in an assoc sequence, or None.
pub open spec fn holder_of(hs: Seq<(Cell, Agent)>, c: Cell) -> Option<Agent>
    decreases hs.len()
{
    if hs.len() == 0 {
        None
    } else if hs[0].0 == c {
        Some(hs[0].1)
    } else {
        holder_of(hs.subrange(1, hs.len() as int), c)
    }
}

/// No requested cell is held by an agent other than `agent`.
pub open spec fn no_foreign(hs: Seq<(Cell, Agent)>, cells: Seq<Cell>, agent: Agent) -> bool {
    forall|t: int|
        0 <= t < cells.len() ==>
            (holder_of(hs, cells[t]) is None || holder_of(hs, cells[t]) == Some(agent))
}

// =====================================================================
// Verified exec helper: first-match holder lookup
// =====================================================================

pub fn lookup_holder(hs: &Vec<(Cell, Agent)>, c: Cell) -> (r: Option<Agent>)
    ensures r == holder_of(hs@, c)
{
    let n = hs.len();
    proof {
        assert(hs@.subrange(0, n as int) =~= hs@);
    }
    let mut k: usize = 0;
    while k < n
        invariant
            0 <= k <= n,
            n == hs@.len(),
            holder_of(hs@, c) == holder_of(hs@.subrange(k as int, n as int), c),
        decreases n - k
    {
        assert(hs@.subrange(k as int, n as int).len() > 0);
        assert(hs@.subrange(k as int, n as int)[0] == hs@[k as int]);
        if hs[k].0 == c {
            return Some(hs[k].1);
        }
        assert(hs@.subrange(k as int, n as int).subrange(1, (n - k) as int)
               == hs@.subrange((k + 1) as int, n as int));
        k = k + 1;
    }
    assert(hs@.subrange(k as int, n as int).len() == 0);
    None
}

// =====================================================================
// can_acquire: SOUND + COMPLETE against no_foreign
// =====================================================================

pub fn can_acquire(hs: &Vec<(Cell, Agent)>, cells: &Vec<Cell>, agent: Agent) -> (ok: bool)
    ensures ok == no_foreign(hs@, cells@, agent)
{
    let n = cells.len();
    let mut s: usize = 0;
    while s < n
        invariant
            0 <= s <= n,
            n == cells@.len(),
            forall|t: int|
                0 <= t < s ==>
                    (holder_of(hs@, cells@[t]) is None
                     || holder_of(hs@, cells@[t]) == Some(agent)),
        decreases n - s
    {
        let c = cells[s];
        let h = lookup_holder(hs, c);   // == holder_of(hs@, c)
        if let Some(a) = h {
            if a != agent {
                // Foreign holder at index s witnesses !no_foreign.
                assert(holder_of(hs@, cells@[s as int]) == Some(a));
                assert(a != agent);
                return false;
            }
        }
        // Did not return: holder is None or our own.
        assert(holder_of(hs@, cells@[s as int]) is None
               || holder_of(hs@, cells@[s as int]) == Some(agent));
        s = s + 1;
    }
    true
}

} // verus!