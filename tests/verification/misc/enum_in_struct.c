#include "../../utils.h"

typedef enum {A, B} Enum;

struct S {
    Enum e;
};



int main() {
    struct S* p = safe_malloc(sizeof(struct S));
    p->e = A;
    free(p);
}
