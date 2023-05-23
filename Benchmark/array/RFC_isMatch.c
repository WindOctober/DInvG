// frama-c-gui RFC_isMatch.c

typedef unsigned int U32;

#define ONE_BYTE 16
#define BYTE_COUNT 1

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