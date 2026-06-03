/* litmus_mutex_a1_relaxed.c  --  NEGATIVE CONTROL
 *
 * Identical to litmus_mutex_a1.c EXCEPT the lock uses memory_order_relaxed
 * for both the acquire-CAS and the release-store. This breaks the
 * happens-before between consecutive critical sections: an agent's read of
 * `cell` may not observe the previous agent's write, so two agents can read
 * the same v and both write v+1 -- a lost update, i.e. an A_1 witness.
 *
 * PURPOSE (non-vacuity): GenMC MUST report an assertion violation
 * (cell < AGENTS) and/or a data race on `cell` here. If it does, that
 * proves the release/acquire annotations in litmus_mutex_a1.c are
 * load-bearing -- the positive result is not vacuous, it genuinely depends
 * on the memory ordering the runtime's lock provides. If GenMC reported NO
 * violation here, the positive litmus would be suspect.
 *
 * BUILD / RUN
 *   genmc litmus_mutex_a1_relaxed.c
 * Expected: an assertion violation (lost update) and/or a detected race on
 * `cell`, with a counterexample trace.
 */
#include <stdatomic.h>
#include <pthread.h>
#include <assert.h>

#ifndef AGENTS
#define AGENTS 2      /* two agents suffice to exhibit the lost update */
#endif

static atomic_int lock_state;
static int cell;

/* BROKEN acquire: relaxed CAS -- no acquire barrier, prior release not
 * necessarily observed. */
static void acquire_relaxed(void)
{
    int expected = 0;
    while (!atomic_compare_exchange_strong_explicit(
               &lock_state, &expected, 1,
               memory_order_relaxed, memory_order_relaxed)) {
        expected = 0;
    }
}

/* BROKEN release: relaxed store -- this section's write not published with
 * release semantics. */
static void release_relaxed(void)
{
    atomic_store_explicit(&lock_state, 0, memory_order_relaxed);
}

static void *agent(void *unused)
{
    (void)unused;
    acquire_relaxed();
    int v = cell;
    int g = v + 1;
    cell = g;
    release_relaxed();
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

    /* Under relaxed ordering this CAN fail: a lost update (A_1). */
    assert(cell == AGENTS);
    return 0;
}