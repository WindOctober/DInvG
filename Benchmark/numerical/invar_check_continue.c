// goto-cc -o invar_check_continue.goto invar_check_continue.c && goto-instrument --apply-loop-contracts invar_check_continue.goto invar_check_continue_inst.goto && cbmc invar_check_continue_inst.goto --pointer-check --bounds-check --signed-overflow-check
#include <assert.h>

int main()
{
  int r;
  __CPROVER_assume(r >= 0);

  while(r > 0)
    // clang-format off
    // clang-format on
    {
      --r;
      if(r < 5)
      {
        continue;
      }
      else
      {
        --r;
      }
    }

  assert(r == 0);

  return 0;
}