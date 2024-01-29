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
    int n;
    int a;
    int r;
    int i;
    int j;

    if (n < 1)
        return -1;

    i = 0;

    while (i < n) {
        i++;
    }

    j = a;

    while (j < n) {
        assert(1 * n - 1 * i == 0);
        assert(-1 * a + 1 * j >= 0);
        assert(1 * n - 1 * j - 1 >= 0);
        assert(1 * n - 1 >= 0);
        j = j + 1;
    }
    return 0;
}
