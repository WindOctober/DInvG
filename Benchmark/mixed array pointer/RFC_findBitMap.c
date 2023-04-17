// frama-c-gui RFC_findBitMap.c

#include <stdio.h>
#include <malloc.h>
#include <memory.h>
#include <assert.h>

typedef unsigned int U32;

#define ONE_BYTE 16
#define BYTE_COUNT 1

typedef struct BitMap {
    int mapId;
    U32 bits[BYTE_COUNT];
} BitMap;

/*@
requires \valid((U32*)(bits+(0..(BYTE_COUNT-1))));
requires \valid((U32*)(pTmpbits+(0..(BYTE_COUNT-1))));
ensures (\forall integer j; 0 <= j < BYTE_COUNT ==> pTmpbits[j] == bits[j]) ==> \result == 1;
ensures (\exists integer j; 0 <= j < BYTE_COUNT && pTmpbits[j] != bits[j]) ==> \result == 0;
assigns \nothing;
*/
int isMatch( const U32 *pTmpbits, const U32 *bits)
{
    int ret = 1;
    /*@
    loop invariant 0 <= j <= BYTE_COUNT;
    loop invariant ret == 1 || ret == 0;
    loop invariant ret == 1 ==> \forall integer k; 0<= k < BYTE_COUNT ==> ( k < j ==> pTmpbits[k] == bits[k] ); 
    loop invariant ret == 0 ==>  pTmpbits[j] != bits[j];
    loop assigns j;
    */
    for (int j = 0; j < BYTE_COUNT; ++j) 
    {
		    if (pTmpbits[j] != bits[j])
		    {
			    ret = 0;
			    break;
		    }
    }
    return ret;
}


/*
// CBMC format
requires \forall integer i; 0 <= i < used ==> \valid((BitMap*)(bitMap+i));
requires \valid((U32*)(bits+(0..(BYTE_COUNT-1))));
ensures (\forall integer i; 0 <= i < used ==> \exists integer k; 0 <= k < BYTE_COUNT && (bitMap+i)->bits[k] != bits[k]) ==> \result == -1;
ensures \exists integer i; 0 <= i < used && (\forall integer j; 0 <= j < i ==> \exists integer k; 0 <= k < BYTE_COUNT && (bitMap+i)->bits[k] != bits[k]) && (\forall integer k; 0 <= k < BYTE_COUNT ==> (bitMap+i)->bits[k] == bits[k]) ==> \result == (bitMap+i)->mapId;
*/
/*@
// Frama-C format
requires \forall integer i; 0 <= i < used ==> \valid((BitMap*)(bitMap+i));
requires \valid((U32*)(bits+(0..(BYTE_COUNT-1))));

behavior can_find:
    assumes \forall integer i; 0 <= i < used ==> \exists integer k; 0 <= k < BYTE_COUNT && (bitMap+i)->bits[k] != bits[k];
    ensures \result == -1;

behavior can_not_find:
    assumes \exists integer i; 0 <= i < used && \forall integer k; 0 <= k < BYTE_COUNT ==> (bitMap+i)->bits[k] == bits[k];
    ensures \exists integer i; 0 <= i < used && (\forall integer j; 0 <= j < i ==> \exists integer k; 0 <= k < BYTE_COUNT && (bitMap+i)->bits[k] != bits[k]) && (\forall integer k; 0 <= k < BYTE_COUNT ==> (bitMap+i)->bits[k] == bits[k]) ==> \result == (bitMap+i)->mapId;

complete behaviors;
disjoint behaviors;
*/
int findBitMap(BitMap *bitMap, U32 used, const U32 *bits)
{
    int matched = 1;
    
    /*@
    loop invariant 0 <= i <= used;
    loop invariant matched == 1 || matched == 0;
    loop invariant \forall integer j; 0 <= j < used ==> ( j < i ==> \exists integer k; 0 <= k < BYTE_COUNT && (bitMap+j)->bits[k] != bits[k]); 
    //loop invariant matched == 1 ==> \forall integer j; 0 <= j < used ==> ( j < i ==> \forall integer k; 0 <= k < BYTE_COUNT ==> (bitMap+j)->bits[k] == bits[k]); 
    //loop invariant matched == 0 ==> \exists integer j; 0 <= j < used && \exists integer k; 0 <= k < BYTE_COUNT && (bitMap+j)->bits[k] != bits[k];
    loop assigns matched, i;
    */
    for (int i = 0; i < used; ++i)
    {
        BitMap *pTmp = bitMap + i;
        matched = isMatch(pTmp->bits, bits);
        if (matched)
        {
            return pTmp->mapId;
        }
    }

    return -1;
}