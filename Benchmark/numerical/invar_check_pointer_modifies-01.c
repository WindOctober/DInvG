// goto-cc -o invar_check_pointer_modifies-01.goto invar_check_pointer_modifies-01.c && goto-instrument --apply-loop-contracts invar_check_pointer_modifies-01.goto invar_check_pointer_modifies-01_inst.goto && cbmc invar_check_pointer_modifies-01_inst.goto --pointer-check --bounds-check --signed-overflow-check
#include <assert.h>
#include <stdlib.h>

void main()
{
  char *data = malloc(1);
  *data = 42;

  unsigned i;
  while(i > 0)
    // clang-format off

    // clang-format on
    {
      *data = 42;
      i--;
    }

  assert(*data = 42);
}