// goto-cc -o invar_assigns_opt.goto invar_assigns_opt.c && goto-instrument --apply-loop-contracts invar_assigns_opt.goto invar_assigns_opt_inst.goto && cbmc invar_assigns_opt_inst.goto --pointer-check --bounds-check --signed-overflow-check
#include <assert.h>

int main()
{
  int r1, s1 = 1;
  while (r1 > 0)
  {
    s1 = 1;
    r1--;
  }
  #ifdef DEBUG
  assert(r1 == 0);
  #endif
  int r2, s2 = 1;
  while (r2 > 0)
  {
    s2 = 1;
    r2--;
  }
  #ifdef DEBUG
  assert(r2 == 0);
  #endif
  return 0;
}
