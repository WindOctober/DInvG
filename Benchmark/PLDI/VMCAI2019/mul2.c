extern void abort(void);
extern void __assert_fail(const char*, const char*, unsigned int, const char*)
    __attribute__((__nothrow__, __leaf__)) __attribute__((__noreturn__));
void reach_error() {
    __assert_fail("0", "const.c", 3, "reach_error");
}
void __VERIFIER_assert(int cond) {
    if (!(cond)) {
    ERROR: {
        reach_error();
        abort();
    }
    }
    return;
}
int main() {
    int r;
    int a;
    int x = a;
    int i;
    for (i = 0; i < a; i++) {
        __VERIFIER_assert(1 * a - 1 * x + 1 * i == 0);
        __VERIFIER_assert(-1 * a + 1 * x >= 0);
        __VERIFIER_assert(2 * a - 1 * x - 1 >= 0);
        x = x + 1;
    }

    return;
}
