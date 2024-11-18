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
    int a = 6;
    int b = 2;
    int q;
    int r;

    if(a < 0)
        return 0;

    if(b < 1)
        return 0;

    q = 0;
    r = a;

    if(r > b)
    {
        do
        {
            r = r - b;
            q = q + 1;
        }
        while(r > b);
        __VERIFIER_assert(r==2);
        __VERIFIER_assert(a==6);
        __VERIFIER_assert(b==2);
        __VERIFIER_assert(q==2);
    }
    return 0;
}
