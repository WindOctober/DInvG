// goto-cc -o invar_havoc_static_multi-dim_array.goto invar_havoc_static_multi-dim_array.c && goto-instrument --apply-loop-contracts invar_havoc_static_multi-dim_array.goto invar_havoc_static_multi-dim_array_inst.goto && cbmc invar_havoc_static_multi-dim_array_inst.goto --pointer-check --bounds-check --signed-overflow-check
#include <assert.h>
#include <stdlib.h>

#define SIZE 8

void main()
{
  char data[SIZE][SIZE][SIZE];

  data[1][2][3] = 0;
  char *old_data123 = &(data[1][2][3]);

  for(unsigned i = 0; i < SIZE; i++)
    {
      data[i][(i + 1) % SIZE][(i + 2) % SIZE] = 1;
    }

  assert(data[1][2][3] == 0);
}