// frama-c-gui foo_loop_contract.c
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <assert.h>

#define SIZE 10

/*@ 
  requires \valid((uint32_t *)(map+(0..len-1)));
  requires \valid((uint32_t *)(key+(0..len-1)));
  requires len <= SIZE;
  ensures \result == -1 ==> \forall integer i; 0 <= i < len ==> map[i] != key[i];
  ensures \result == 0 ==> \exists integer i; 0 <= i < len && map[i] == key[i];
  assigns \nothing;	
@*/
int foo(uint32_t *map, uint32_t *key, uint32_t len)
{
	int ret = -1;
	for (int i = 0; i < len; i++)
	{
		if (map[i] == key[i])
		{
			ret = 0;
			break;
		}
	}
	return ret;
}
