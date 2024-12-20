void reach_error(void) {assert(0);}
extern void abort(void);

extern int __VERIFIER_nondet_int(void);
extern _Bool __VERIFIER_nondet_bool(void);

void __VERIFIER_assert(int cond) {
  if (!cond) {
    reach_error();
  }
}

/* 25.cfg:
names=x
precondition=x<0
loopcondition=x<10 
loop= x=x+1;
postcondition=x==10
learners=linear
*/
int main() {
  int x = __VERIFIER_nondet_int();
  if (!(x<0)) return 0;
  // START NAIVELOOPABSTRACTION
  if (x < (10)) {
  x = __VERIFIER_nondet_int();
  if (!(x < (10))) abort();
  if (x<10) {
      x=x+1;
    }
  if (x < (10)) abort();
  }
  // END NAIVELOOPABSTRACTION
  __VERIFIER_assert(x==10);
  return 0;
}
