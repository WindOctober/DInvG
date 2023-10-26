// goto-cc -o invar_loop_constant_no_modify.goto invar_loop_constant_no_modify.c && goto-instrument --apply-loop-contracts invar_loop_constant_no_modify.goto invar_loop_constant_no_modify_inst.goto && cbmc invar_loop_constant_no_modify_inst.goto --pointer-check --bounds-check --signed-overflow-check
#include <assert.h>

int main()
{
  int r;
  int s = 1;
  while(r > 0)
    // clang-format off

    // clang-format on
    {
      r--;
    }
  assert(r == 0);
  assert(s == 1);

  return 0;
}