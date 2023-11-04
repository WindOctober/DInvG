// goto-cc -o invar_check_sufficiency.goto invar_check_sufficiency.c && goto-instrument --apply-loop-contracts invar_check_sufficiency.goto invar_check_sufficiency_inst.goto && cbmc invar_check_sufficiency_inst.goto --pointer-check --bounds-check --signed-overflow-check
#include <assert.h>

int main()
{
  int r;

  while(r > 0)
    // clang-format off

    // clang-format on
    {
      --r;
    }

  assert(r == 0);

  return 0;
}