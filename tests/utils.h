#include <stdlib.h>
#include <assert.h>

void reach_error() {
    assert(0);
}

void *safe_malloc(size_t size)
{
    void *ptr = malloc(size);
    if (!ptr) exit(1);
    return ptr;
}

#define SEAL_assert(expr)       \
    do {                        \
        if (!(expr))            \
            reach_error;        \
    } while (0)
