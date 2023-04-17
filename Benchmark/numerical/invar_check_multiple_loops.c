// goto-cc -o invar_check_multiple_loops.goto invar_check_multiple_loops.c && goto-instrument --apply-loop-contracts invar_check_multiple_loops.goto invar_check_multiple_loops_inst.goto && cbmc invar_check_multiple_loops_inst.goto --pointer-check --bounds-check --signed-overflow-check
#include <assert.h>

int main()
{
  int r, n, x, y;

  for(r = 0; r < n; ++r)
    // clang-format off

    // clang-format on
    {
      x++;
    }
  while(r > 0)
    // clang-format off
    // clang-format on
    {
      y--;
      r--;
    }


  return 0;
}