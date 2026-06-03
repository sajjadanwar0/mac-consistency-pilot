// lib_pessimistic_invariant.rs
//
// State-machine invariant for the pessimistic-locking enforcer. Exclusivity
// (each cell held by at most one agent) is what prevents A_1 under pessimistic
// locking. It is automatic that `cell_holders` maps each cell to a single
// agent; the content of the invariant is that `cell_holders` and `agent_holds`
// stay MUTUALLY CONSISTENT across operations, so that release frees exactly the
// cells an agent holds and never desyncs the two views (which would let a cell
// look free while still held, breaking exclusivity).
//
// We model the holder state as
//     holders : Map<Cell, Agent>          (cell_holders)
//     held    : Map<Agent, Set<Cell>>     (agent_holds)
// and prove that acquisition (begin/commit) and release preserve the
// consistency invariant `wf`, with `initial_wf` for the empty base case. By
// induction the invariant holds in every reachable state.
//
// FIDELITY: acquisition sets holders[c]=agent and adds c to held[agent] for a
// set of non-foreign cells -- exactly the deployed begin/commit hold-registration.
// Release removes the agent from `held` and every cell it holds from `holders`
// -- exactly the deployed release loop. Proof-mode over the Map model, connected
// to the deployed HashMap runtime by refinement; std/parking_lot internals are
// not exec-verifiable.
//
// NO axiom, NO assume, NO admit, NO external_body in this file.

use vstd::prelude::*;

verus! {

/// Consistency between the two holder views.
pub open spec fn wf(holders: Map<int, int>, held: Map<int, Set<int>>) -> bool {
    // forward: a held cell's recorded holder actually lists it
    &&& (forall|c: int| #[trigger] holders.dom().contains(c) ==>
            held.dom().contains(holders[c]) && held[holders[c]].contains(c))
    // backward: anything an agent lists is recorded to that agent
    &&& (forall|a: int, c: int| #![trigger held[a].contains(c)]
            held.dom().contains(a) && held[a].contains(c) ==>
            holders.dom().contains(c) && holders[c] == a)
}

/// Acquisition (begin / commit hold-registration) preserves consistency.
/// `cells` is the set acquired; the non-foreign precondition is that none is
/// currently held by a different agent.
pub proof fn acquire_preserves_wf(
    holders: Map<int, int>, held: Map<int, Set<int>>,
    holders2: Map<int, int>, held2: Map<int, Set<int>>,
    agent: int, cells: Set<int>,
)
    requires
        wf(holders, held),
        // non-foreign: acquiring does not steal another agent's cell
        forall|c: int| cells.contains(c) ==> (!holders.dom().contains(c) || holders[c] == agent),
        // holders2 = holders with every acquired cell mapped to agent
        holders2.dom() == holders.dom().union(cells),
        forall|c: int| cells.contains(c) ==> holders2[c] == agent,
        forall|c: int| (holders.dom().contains(c) && !cells.contains(c)) ==> holders2[c] == holders[c],
        // held2 = held with agent's set extended by the acquired cells
        held2.dom() == held.dom().insert(agent),
        held2[agent] == (if held.dom().contains(agent) { held[agent] } else { Set::<int>::empty() }).union(cells),
        forall|a: int| (held.dom().contains(a) && a != agent) ==> held2[a] == held[a],
        forall|a: int| a != agent ==> (held2.dom().contains(a) == held.dom().contains(a)),
    ensures
        wf(holders2, held2),
{
    // forward
    assert forall|c: int| holders2.dom().contains(c) implies
        held2.dom().contains(holders2[c]) && held2[holders2[c]].contains(c) by
    {
        if cells.contains(c) {
            assert(holders2[c] == agent);
            assert(held2.dom().contains(agent));
            assert(held2[agent].contains(c));   // agent's set is base.union(cells), c in cells
        } else {
            // c in holders.dom(), unchanged
            assert(holders.dom().contains(c));
            assert(holders2[c] == holders[c]);
            let a2 = holders[c];
            assert(held.dom().contains(a2) && held[a2].contains(c));   // wf(holders,held)
            if a2 == agent {
                assert(held2[agent].contains(c));   // base = held[agent] contains c, and union keeps it
            } else {
                assert(held2.dom().contains(a2));
                assert(held2[a2] == held[a2]);
            }
        }
    }
    // backward
    assert forall|a: int, c: int| held2.dom().contains(a) && held2[a].contains(c) implies
        holders2.dom().contains(c) && holders2[c] == a by
    {
        if a == agent {
            // c in held[agent] (base) or c in cells
            if cells.contains(c) {
                assert(holders2.dom().contains(c));   // union
                assert(holders2[c] == agent);
            } else {
                // c was in base = held[agent]; needs held.dom().contains(agent)
                assert(held.dom().contains(agent));
                assert(held[agent].contains(c));
                assert(holders.dom().contains(c) && holders[c] == agent);   // wf backward
                assert(holders2.dom().contains(c));
                assert(holders2[c] == agent);   // unchanged (c not in cells) or set to agent
            }
        } else {
            // a != agent: held2[a] == held[a]
            assert(held.dom().contains(a));
            assert(held2[a] == held[a]);
            assert(held[a].contains(c));
            assert(holders.dom().contains(c) && holders[c] == a);   // wf backward
            // c cannot be in cells: that would force holders[c]==agent (non-foreign),
            // but holders[c]==a != agent -- contradiction.
            assert(!cells.contains(c));
            assert(holders2[c] == holders[c]);
            assert(holders2.dom().contains(c));
        }
    }
}

/// Release preserves consistency: drop `agent` from `held` and every cell it
/// holds from `holders`.
pub proof fn release_preserves_wf(
    holders: Map<int, int>, held: Map<int, Set<int>>,
    holders2: Map<int, int>, held2: Map<int, Set<int>>,
    agent: int,
)
    requires
        wf(holders, held),
        forall|c: int| #![trigger holders2.dom().contains(c)]
            holders2.dom().contains(c) <==> (holders.dom().contains(c) && holders[c] != agent),
        forall|c: int| #![trigger holders2.dom().contains(c)]
            holders2.dom().contains(c) ==> holders2[c] == holders[c],
        held2 == held.remove(agent),
    ensures
        wf(holders2, held2),
{
    // forward
    assert forall|c: int| holders2.dom().contains(c) implies
        held2.dom().contains(holders2[c]) && held2[holders2[c]].contains(c) by
    {
        assert(holders.dom().contains(c) && holders[c] != agent);
        let a2 = holders[c];
        assert(holders2[c] == a2);
        assert(held.dom().contains(a2) && held[a2].contains(c));   // wf forward
        assert(a2 != agent);
        assert(held2.dom().contains(a2));        // remove(agent) keeps a2 != agent
        assert(held2[a2] == held[a2]);
    }
    // backward
    assert forall|a: int, c: int| held2.dom().contains(a) && held2[a].contains(c) implies
        holders2.dom().contains(c) && holders2[c] == a by
    {
        assert(a != agent);                       // agent was removed from held2
        assert(held.dom().contains(a));
        assert(held2[a] == held[a]);
        assert(held[a].contains(c));
        assert(holders.dom().contains(c) && holders[c] == a);   // wf backward
        assert(holders[c] == a && a != agent);
        assert(holders2.dom().contains(c));       // holders[c] != agent
        assert(holders2[c] == holders[c]);
    }
}

/// The initial state (no holders) is consistent, vacuously.
pub proof fn initial_wf()
    ensures
        wf(Map::<int, int>::empty(), Map::<int, Set<int>>::empty()),
{
}

} // verus!