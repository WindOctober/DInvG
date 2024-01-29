extern void read_reset(int * reset);
extern void read_event(int * event);

extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "const.c", 3, "reach_error"); }
extern unsigned int __VERIFIER_nondet_uint(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}

int main()
{
    int cnt1;
    int reset;
    int event;
    int max;
    max=__VERIFIER_nondet_uint();
    cnt1=0;
    if(max < 0)
        return;
    while(1)
    {
        __VERIFIER_assert(cnt1 >= 0 && cnt1 <= max);
        reset=__VERIFIER_nondet_uint();
        event=__VERIFIER_nondet_uint();
        if(reset)
        {
            cnt1 = 0;
        }
        else if(event && cnt1 < max)
        {
            cnt1 = cnt1 + 1;
        }
    }
    return 0;
}
