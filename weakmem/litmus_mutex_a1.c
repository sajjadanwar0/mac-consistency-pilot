#include <stdatomic.h>
#include <pthread.h>
#include <assert.h>

#ifndef AGENTS
#define AGENTS 3
#endif

static atomic_int lock_state;

static int cell;

static void acquire(void)
{
    int expected = 0;
    while (!atomic_compare_exchange_strong_explicit(
               &lock_state, &expected, 1,
               memory_order_acquire, memory_order_relaxed)) {
        expected = 0;
    }
}

static void release(void)
{
    atomic_store_explicit(&lock_state, 0, memory_order_release);
}

static void *agent(void *unused)
{
    (void)unused;
    acquire();
    int v = cell;
    int g = v + 1;
    cell = g;
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

    assert(cell == AGENTS);

    return 0;
}