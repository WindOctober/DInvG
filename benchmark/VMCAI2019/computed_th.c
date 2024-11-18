extern void read_reset(int* reset);
extern void read_event(int* event);

extern void abort(void);
extern void __assert_fail(const char*, const char*, unsigned int, const char*)
    __attribute__((__nothrow__, __leaf__)) __attribute__((__noreturn__));
void reach_error() {
    __assert_fail("0", "const.c", 3, "reach_error");
}
extern unsigned int __VERIFIER_nondet_uint(void);
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
    int n;
    int a;

    n = __VERIFIER_nondet_uint();
    a = __VERIFIER_nondet_uint();

    int i;
    int j;
    int th;

    if (n < 0 || a < 0)
        return 0;

    th = 0;
    i = 0;

    while (i < n) {
        th++;
        i++;
    }

    j = a;
    while (j < th) {
        __VERIFIER_assert(1 * n - 1 * th == 0);
        __VERIFIER_assert(1 * n - 1 * i == 0);
        __VERIFIER_assert(-1 * a + 1 * j >= 0);
        __VERIFIER_assert(1 * n - 1 * j - 1 >= 0);
        __VERIFIER_assert(1 * a >= 0);
        j++;
    }

    r = j;
    return 0;
}
