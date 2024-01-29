#include "assert.h"
int main() {
    int i = 0;
    int k = 0;
    int j;
    while(i < LARGE_INT) {
        j = __VERIFIER_nondet_int();
        if (!(1 <= j && j < LARGE_INT)) return 0;
        i = i + j;
        k ++;
    }
    __VERIFIER_assert(k <= LARGE_INT);
    return 0;
}
