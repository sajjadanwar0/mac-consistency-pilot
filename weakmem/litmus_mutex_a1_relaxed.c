#include <stdatomic.h>
#include <pthread.h>
#include <assert.h>

#ifndef AGENTS
#define AGENTS 2
#endif

static atomic_int lock_state;
static int cell;

static void acquire_relaxed(void)
{
    int expected = 0;
    while (!atomic_compare_exchange_strong_explicit(
               &lock_state, &expected, 1,
               memory_order_relaxed, memory_order_relaxed)) {
        expected = 0;
    }
}

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

    assert(cell == AGENTS);

    return 0;
}