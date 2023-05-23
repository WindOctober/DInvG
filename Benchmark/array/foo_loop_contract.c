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
    /*@
    loop invariant 0 <= i <= len;
    loop invariant ret == -1 || ret == 0;
	loop invariant ret == -1 ==> \forall integer j; 0 <= j < len ==> (j < i ==> map[j] != key[j]);
	loop invariant ret == 0 ==> map[i] == key[i];
    loop assigns i;
	*/
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

int main()
{
    uint32_t *map = malloc(sizeof(uint32_t)*SIZE);
	uint32_t *key = malloc(sizeof(uint32_t)*SIZE);
    memset(map, 0, sizeof(uint32_t)*SIZE);
	memset(key, 0, sizeof(uint32_t)*SIZE);
    key[0] = 1;
	map[0] = 2;

    int ret;
    for (int i = 1; i < SIZE; i++) {
        ret = foo(map, key, i);
    }
    assert(ret == 0);
    assert(ret == -1);
    assert(0);
}