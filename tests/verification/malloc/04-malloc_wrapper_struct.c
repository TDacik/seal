#include <stdio.h>
#include <stdlib.h>

typedef struct SLL {
    struct SLL *next;
} SLL;

void *safe_malloc(size_t size) {
  void *ptr = malloc(size);
  if (!ptr) exit(1);
  return ptr;
}

int main() {
  SLL *x = safe_malloc(sizeof(*x));
  x->next = NULL;
  free(x);
}
