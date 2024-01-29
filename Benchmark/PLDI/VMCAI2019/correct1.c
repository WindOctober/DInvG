extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "const.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}

int main(){
    int x;
    int obj;
    int tol;
    int step;
    
    if (tol < 0 || step < 0)
        return;

    int err = x - obj;

    while (err > tol) {
        __VERIFIER_assert(1 * x -1 * obj -1 * err  ==0 );
        __VERIFIER_assert(1 * x -1 * obj -1 * tol -1 >= 0);
        __VERIFIER_assert(1 * step  >= 0);
        __VERIFIER_assert(1 * tol  >= 0);
        if (err > tol)
            x = x - step;
        else if (err < -tol)
            x = x + step;

        err = x - obj;
    }
    
    return 0;
}
