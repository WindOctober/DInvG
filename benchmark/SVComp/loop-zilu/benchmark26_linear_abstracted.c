void reach_error(void) {assert(0);}
extern void abort(void);

extern int __VERIFIER_nondet_int(void);
extern _Bool __VERIFIER_nondet_bool(void);

void __VERIFIER_assert(int cond) {
  if (!cond) {
    reach_error();
  }
}

/* 26.cfg:
names=x y
precondition=x<y
loopcondition=x<y
loop= x=x+1;
postcondition=x==y
learners=linear
*/
int main() {
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  if (!(x<y)) return 0;
  // START NAIVELOOPABSTRACTION
  if (x < y) {
  x = __VERIFIER_nondet_int();
  if (!(x < y)) abort();
  if (x<y) {
      x=x+1;
    }
  if (x < y) abort();
  }
  // END NAIVELOOPABSTRACTION
  __VERIFIER_assert(x==y);
  return 0;
}
