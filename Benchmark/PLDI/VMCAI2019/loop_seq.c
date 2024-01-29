extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "const.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
int main()
{
    int r;
    int n;
    int m;
    int i;
    int j;

    if(n < 0 || m < 0)
        return;

    r = 0;
    i = 0;

    while(i < n){
      __VERIFIER_assert(1 * r -1 * i  == 0);
      __VERIFIER_assert(1 * r  >= 0);
      __VERIFIER_assert(1 * m  >= 0);
      __VERIFIER_assert(-1 * r  + 1 * n -1 >= 0);
      r = r + 1;
      i++;
    }

    j = i;
    while(j < m){
      __VERIFIER_assert(1 * r -1 * j  == 0);
      __VERIFIER_assert(1 * i  == 0);
      __VERIFIER_assert(1 * n  == 0);
      __VERIFIER_assert(-1 * r  + 1 * m -1 >= 0);
      __VERIFIER_assert(1 * r  >= 0);
      r = r + 1;
      j++;
    }
    return;
}
