// goto-cc -o invar_havoc_static_array_const_idx.goto invar_havoc_static_array_const_idx.c && goto-instrument --apply-loop-contracts invar_havoc_static_array_const_idx.goto invar_havoc_static_array_const_idx_inst.goto && cbmc invar_havoc_static_array_const_idx_inst.goto --pointer-check --bounds-check --signed-overflow-check
#include <assert.h>
#include <stdlib.h>

#define SIZE 8

void main()
{
  char data[SIZE];
  data[1] = 0;
  data[4] = 0;

  for(unsigned i = 0; i < SIZE; i++)
    {
      data[1] = i;
    }

  assert(data[1] == 0 || data[1] == 1);
  assert(data[4] == 0);
}