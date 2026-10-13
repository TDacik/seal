#include <stdlib.h>

int __VERIFIER_nondet_int();

typedef struct SLL {
    struct SLL *next;
    int data;
} SLL;

void construct_list(SLL *s) {
    while (__VERIFIER_nondet_int()) {
        s->next = malloc(sizeof(SLL));
        if (s->next == NULL) {
            return;
        }

        s = s->next;
    }

    s->next = NULL;
}

void traverse_list(SLL *s) {
    while (s != NULL) {
        int d = s->data;
        s = s->next;
    }
}

void free_list(SLL *s) {
    while (s != NULL) {
        SLL *next = s->next;
        free(s);
        s = next;
    }
}

int main() {
    SLL *start = malloc(sizeof(SLL));
    if (start == NULL) {
        return 0;
    }

    construct_list(start);
    traverse_list(start);
    free_list(start);

    start = malloc(sizeof(SLL));
    if (start == NULL) {
        return 0;
    }

    construct_list(start);
    traverse_list(start);
    free_list(start);

    traverse_list(start);
}
