#include <stdio.h>
#include <stdlib.h>

typedef struct SLL {
    struct SLL *next;
} SLL;

int main() {
  SLL *x = malloc(sizeof(SLL));
  if (!x) exit(1);
  free(x);
}
