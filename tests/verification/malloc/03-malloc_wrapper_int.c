#include <stdio.h>
#include <stdlib.h>

void *safe_malloc(size_t size) {
  void *ptr = malloc(size);
  if (!ptr) exit(1);
  return ptr;
}

int main() {
  int *x = safe_malloc(sizeof(int));
  *x = 3;
  free(x);
}
