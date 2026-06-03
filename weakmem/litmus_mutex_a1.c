/* litmus_mutex_a1.c
 *
 * Weak-memory (RC11) bounded model-check of the mac-consistency runtime's
 * core concurrency discipline: acquire-lock -> read -> generate -> write ->
 * release. Verified with GenMC (https://github.com/MPI-SWS/genmc), which
 * EXHAUSTIVELY explores every RC11-consistent execution of this program for
 * the fixed agent count N.
 *
 * WHAT THIS ESTABLISHES (and what it does NOT)
 *   Establishes: under the C11 release/acquire lock protocol, N agents each
 *     performing a locked read-modify-write never lose an update under RC11
 *     -- i.e. no A_1 stale-generation -- for the bound N, across ALL RC11
 *     executions (GenMC is exhaustive for fixed N).
 *   Does NOT establish: (a) the property for unbounded N (that is the
 *     standard lock-protocol induction, not mechanized here); (b) that
 *     std::sync::Mutex specifically implements this protocol -- that
 *     correspondence is RustBelt's verified Mutex result, cited separately.
 *
 * A lost update IS an A_1 witness: agent i reads value v, agent j commits
 * v+1 concurrently, agent i then writes v+1 (its generate based on the now
 * stale v), so one increment is lost. With a correct release/acquire lock
 * the critical sections are mutually exclusive and ordered, so the final
 * counter is exactly N. The negative control litmus_mutex_a1_relaxed.c
 * weakens the orderings and MUST exhibit a lost update, proving the
 * acquire/release annotations are load-bearing (non-vacuity).
 *
 * BUILD / RUN
 *   genmc litmus_mutex_a1.c
 *   # sweep the bound:
 *   for n in 2 3 4; do clang -DAGENTS=$n -E ... ; done   # or edit AGENTS below
 * Expected: "No errors were detected" / 0 assertion violations, all
 * executions explored.
 */
#include <stdatomic.h>
#include <pthread.h>
#include <assert.h>

#ifndef AGENTS
#define AGENTS 3      /* bound: number of concurrent agents */
#endif

/* The lock: 0 = free, 1 = held. */
static atomic_int lock_state;

/* The shared cell, protected by the lock. Deliberately a PLAIN int: if the
 * lock fails to provide mutual exclusion or happens-before under RC11,
 * GenMC reports a data race on this access, and/or the final assertion
 * fails. */
static int cell;

/* Acquire: CAS 0 -> 1 with acquire ordering, so the prior critical
 * section's release is observed (happens-before into this section). */
static void acquire(void)
{
    int expected = 0;
    while (!atomic_compare_exchange_strong_explicit(
               &lock_state, &expected, 1,
               memory_order_acquire, memory_order_relaxed)) {
        expected = 0;
    }
}

/* Release: store 0 with release ordering, publishing this section's write
 * to the next acquirer. */
static void release(void)
{
    atomic_store_explicit(&lock_state, 0, memory_order_release);
}

/* One agent: the read-generate-write discipline under the lock. */
static void *agent(void *unused)
{
    (void)unused;
    acquire();
    int v = cell;        /* READ   the shared cell                      */
    int g = v + 1;       /* GENERATE a new value from what was read      */
    cell = g;            /* WRITE  the generated value back              */
    release();
    return NULL;
}

int main(void)
{
    pthread_t t[AGENTS];

    atomic_init(&lock_state, 0);
    cell = 0;

    for (int i = 0; i < AGENTS; i++)
        pthread_create(&t[i], NULL, agent, NULL);
    for (int i = 0; i < AGENTS; i++)
        pthread_join(t[i], NULL);

    /* No lost update == no A_1 stale-generation: every agent's read saw the
     * previous committed write, so all AGENTS increments are reflected. */
    assert(cell == AGENTS);
    return 0;
}