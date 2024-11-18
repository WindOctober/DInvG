void reach_error(void) {assert(0);}

extern int __VERIFIER_nondet_int(void);
extern _Bool __VERIFIER_nondet_bool(void);

void __VERIFIER_assert(int cond) {
  if (!cond) {
    reach_error();
  }
}

int main() {
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  if (!(x < 100 && y < 100)) return 0;
  while (x < 100 && y < 100) {
    x=x+1;
    y=y+1;
  }
  __VERIFIER_assert(x == 100 || y == 100);
  return 0;
}
