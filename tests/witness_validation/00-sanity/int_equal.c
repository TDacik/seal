#include <stdio.h>
#include <stdlib.h>

#include "../utils.h"
#include "../nondet_builtins.h"

int main()
{
    int a = 0;
    int b = a;

    for(int i = 0; i < 100; i++);

    return 0;
}
