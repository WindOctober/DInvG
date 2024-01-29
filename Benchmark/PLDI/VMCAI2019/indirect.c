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
    int a;
    int b;
    int c;
    int n;

    if(n < 0)
       return; 

    int i;
    int j;

    i = 0;
    j = 0;

    while(i < n)
    {
        __VERIFIER_assert(i==j);
        __VERIFIER_assert(1 * i  >= 0);
        __VERIFIER_assert(1 * n -1 * i -1 >= 0);
        i = i + 1;
        j = j + 1;
    }

    if(j >= c)
    {
        r = a;
    }
    else
    {
        r = b;
    }
}
