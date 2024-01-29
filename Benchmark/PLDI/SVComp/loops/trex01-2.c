extern void abort(void);
void reach_error() { assert(0); }
extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
_Bool __VERIFIER_nondet_bool();
int __VERIFIER_nondet_int();

#define LARGE_INT 1000000


int main() {
  _Bool c = __VERIFIER_nondet_bool();
  int x = __VERIFIER_nondet_int(), y = __VERIFIER_nondet_int(), k = __VERIFIER_nondet_int(), z = 1;
  int d=1;
  //int d=2;
  if (!(k <= 1073741823))
    return;
  while (z < k) { z = 2 * z; }
  __VERIFIER_assert(z>=1);
  if (!(x <= LARGE_INT && x >= -LARGE_INT)) return;
  if (!(y <= LARGE_INT && y >= -LARGE_INT)) return;
  if (!(k <= LARGE_INT && k >= -LARGE_INT)) return;
  while (x > 0 && y > 0) {
    c = __VERIFIER_nondet_bool();
    if (c) {
      x = x - d;
      y = __VERIFIER_nondet_bool();
      z = z - 1;
    } else {
      y = y - d;
    }
  }

  return 0;
}


