extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__nothrow__, __leaf__)) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "const.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond)
{
  if (!(cond))
  {
  ERROR:
  {
    reach_error();
    abort();
  }
  }
  return;
}
extern int __VERIFIER_nondet_int(void);
int main()
{
  int a = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  if (a < 0 || b < 0 || a>10000 || b>10000)
    return 0;
  int x = a;
  int y = b;
  int i;
  for (i = 0; i < y; i++)
  {
    __VERIFIER_assert(1 * a - 1 * x + 2 * i == 0);
    __VERIFIER_assert(1 * b - 1 * y == 0);
    __VERIFIER_assert(-1 * a + 1 * x >= 0);
    __VERIFIER_assert(1 * a + 2 * b - 1 * x - 2 >= 0);
    x = x + 2;
  }
  for (i = 0; i < y; i++)
  {
    x = x + 2;
  }
  return 0;
}
