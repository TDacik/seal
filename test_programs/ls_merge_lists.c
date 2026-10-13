#include <stdlib.h>

typedef struct List {
    struct List *next;
    int data;
} SLL;

void construct_list(SLL *s) {
    int __VERIFIER_nondet_int();
    while (__VERIFIER_nondet_int()) {
        s->next = malloc(sizeof(SLL));
        if (s->next == NULL) {
            return;
        }

        s = s->next;
    }

    s->next = NULL;
}

SLL *merge_lists(SLL *x, SLL *y) {
    SLL *a = x;
    while (a->next != NULL) {
        a = a->next;
    }
    a->next = y;

    return x->next;
}

void free_list(SLL *s) {
    while (s) {
        SLL *next = s->next;
        free(s);
        s = next;
    }
}

int main() {
    SLL *first = malloc(sizeof(SLL));
    if (first == NULL) {
        return 0;
    }
    construct_list(first);

    SLL *second = malloc(sizeof(SLL));
    if (second == NULL) {
        return 0;
    }
    construct_list(second);

    SLL *c = merge_lists(first, second);

    free_list(first);
}
