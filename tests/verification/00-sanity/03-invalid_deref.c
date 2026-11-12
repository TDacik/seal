#include "../../utils.h"

int main() {
  int *x = NULL;
  free(x); // invalid-free
}
