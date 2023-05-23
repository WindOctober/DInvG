// goto-cc -o invariant_side_effects.goto invariant_side_effects.c && goto-instrument --apply-loop-contracts invariant_side_effects.goto invariant_side_effects_inst.goto && cbmc invariant_side_effects_inst.goto --pointer-check --bounds-check --signed-overflow-check
#include <assert.h>
#include <stdlib.h>

int main()
{
  unsigned N, *a = malloc(sizeof(unsigned int));

  *a = 0;
  while(*a < N)
    // clang-format off

    // clang-format on
    {
      ++(*a);
    }

  assert(*a == N);
}