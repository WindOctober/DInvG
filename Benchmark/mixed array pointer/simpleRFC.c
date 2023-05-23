// goto-cc -o test.goto simpleRFC.c && goto-instrument --apply-loop-contracts test.goto test_inst.goto && cbmc test_inst.goto
// RFC算法：https://blog.csdn.net/wolfzone025/article/details/6577668
#include <stdio.h>
#include <malloc.h>
#include <memory.h>
#include <assert.h>
#include <stddef.h>

#define BYTE_COUNT 1
#define ONE_BYTE 16
#define BIT_WIDTH (ONE_BYTE*BYTE_COUNT)
#define PORT_MAX (64+1)

typedef unsigned int U32;
//typedef unsigned short U16;

typedef struct Rule {
    int id;
    int start;
    int end;
} Rule;

typedef struct BitMap {
    int mapId;
    U32 bits[BYTE_COUNT];
} BitMap;

void setBit(U32 *bits, U32 bit)
{
    U32 index = bit / ONE_BYTE;
    U32 offset = bit % ONE_BYTE;
    *(bits + index) |= (U32)1 << offset;
}

void clearBit(U32 *bits, U32 bit)

{
    U32 index = bit / ONE_BYTE;
    U32 offset = bit % ONE_BYTE;
    *(bits + index) &= ~((U32)1 << offset);
}

int isMatch( const U32 *pTmpbits, const U32 *bits)

{
	int ret = 1;
	for (unsigned int j = 0; j < BYTE_COUNT; ++j)
	__CPROVER_assigns(j, ret)
	__CPROVER_loop_invariant(0 <= j <= BYTE_COUNT)
	__CPROVER_loop_invariant(ret == 1 || ret == 0)
	__CPROVER_loop_invariant(ret == 1 ==> __CPROVER_forall {int k; (0 <= k && k < BYTE_COUNT) ==> ( k < j ==> pTmpbits[k] == bits[k] )})
	__CPROVER_loop_invariant(ret == 0 ==> (j < BYTE_COUNT && pTmpbits[j] != bits[j]))
	__CPROVER_decreases(BYTE_COUNT - j)
	{
		if (pTmpbits[j] != bits[j])
		{
			ret = 0;
			break;
		}
	}
	return ret;
}

int findBitMap(BitMap *bitMap, U32 used, const U32 *bits)
{
    int matched = 1;
    for (int i = 0; i < used; ++i)
    {
        BitMap *pTmp = bitMap + i;
        int matched = isMatch(pTmp->bits, bits);
        if (matched)
        {
            //return pTmp->mapId;
            return 0;
        }
    }

    return -1;
}

/*
int findBitMap(BitMap *bitMap, U32 used, const U32 *bits)
{
	for (int i = 0; i < used; ++i)
    {
		BitMap *pTmp = bitMap + i;
        int matched = 1;
        for (int j = 0; j < BYTE_COUNT; ++j)
        {
            if (pTmp->bits[j] != bits[j])
            {
                matched = 0;
                break;
            }
        }

        if (matched)
        {
            return pTmp->mapId;
        }
    }

    return -1;
}
*/

int main()
{
    U32 *table = malloc(sizeof(U32) * PORT_MAX);
    BitMap *bitMap = malloc(sizeof(BitMap) * PORT_MAX);
    memset(bitMap, 0, sizeof(BitMap) * PORT_MAX);
    int used = 0;

    Rule rules[BIT_WIDTH];
    for (unsigned int i = 0; i < BIT_WIDTH; i++)
    {
        rules[i].id = i;
        rules[i].start = i + 1;
        rules[i].end = i + 50;
    }

    int *ppStart = malloc(sizeof(int) * PORT_MAX * BIT_WIDTH);
    int *ppEnd = malloc(sizeof(int) * PORT_MAX * BIT_WIDTH);
    memset(ppStart, -1, sizeof(int)* PORT_MAX * BIT_WIDTH);
    memset(ppEnd, -1, sizeof(int)* PORT_MAX * BIT_WIDTH);
    int startIndex[PORT_MAX], endIndex[PORT_MAX];
    memset(startIndex, 0, sizeof(startIndex));
    memset(endIndex, 0, sizeof(endIndex));

    for (unsigned int i = 0; i < BIT_WIDTH; ++i)
	//__CPROVER_loop_invariant(0 <= i <= BIT_WIDTH)
	//__CPROVER_loop_invariant(__CPROVER_forall {int k; (0 <= k && k < BIT_WIDTH) ==> ( k < i ==> *(ppStart + (k+1) * BIT_WIDTH) == k )})
	//__CPROVER_loop_invariant(__CPROVER_forall {int k; (0 <= k && k < BIT_WIDTH) ==> ( k < i ==> startIndex[rules[k].start] == 1 )})
    //__CPROVER_loop_invariant(__CPROVER_forall {int k; (0 <= k && k < BIT_WIDTH) ==> ( k < i ==> *(ppEnd + (k+51) * BIT_WIDTH) == k )})
	//__CPROVER_loop_invariant(__CPROVER_forall {int k; (0 <= k && k < BIT_WIDTH) ==> ( k < i ==> endIndex[rules[k].start + 1] == 1 )})
	//__CPROVER_decreases(BIT_WIDTH - i)
    {
        int start = rules[i].start;
        int index = 0; //int index = startIndex[rules[i].start];
        int offset = start * BIT_WIDTH + index; //int offset = rules[i].start * BIT_WIDTH + startIndex[rules[i].start];
        *(ppStart + offset) = i; //*(ppStart + offset) = rules[i].id;
        startIndex[start] = 1; //startIndex[start]++;

        int end = rules[i].end + 1;
        index = 0; //index = endIndex[end];
        offset = end * BIT_WIDTH; //offset = end * BIT_WIDTH + index;
        *(ppEnd + offset) = i; //*(ppEnd + offset) = rules[i].id;
        endIndex[end] = 1; //endIndex[end]++;
	}
		
    U32 bits[BYTE_COUNT];
    memset(&bits, 0, sizeof(bits));
    U32 changed = 0;
    int id = -1;
    for (int i = 1; i < PORT_MAX; ++i)
    {
        for (int j = 0; j < BIT_WIDTH; ++j)
        {
            int offset = i * BIT_WIDTH + j;
            int end = *(ppEnd + offset);
            if (end >= 0)
            {
                clearBit(bits, end);
                changed = 1;
            }

            int start = *(ppStart + offset);
            if (start >= 0)
            {
                setBit(bits, start);
                changed = 1;
            }
        }

        if (changed == 1)
        {
            id = findBitMap(bitMap, used, bits);
            if (id < 0)
            {
                id = used;
                bitMap[used].mapId = used;
                bitMap[used].bits[0] = bits[0];
                //memcpy(bitMap[used].bits, bits, BIT_WIDTH);
                used++;
            }
            changed = 0;
        }

        if (id >= 0) *(table + i) = id;
    }

    U32 result = *(table + 50);
    printf("0x%X", bitMap[result].bits[0]);

    assert(bitMap[0].bits[0] == 1);
    assert(bitMap[1].bits[0] == 3);
    assert(bitMap[2].bits[0] == 7);
    assert(bitMap[3].bits[0] == 15);
    assert(bitMap[4].bits[0] == 31);
    assert(bitMap[5].bits[0] == 63);
    assert(bitMap[6].bits[0] == 127);
    assert(bitMap[7].bits[0] == 255);
    assert(bitMap[8].bits[0] == 511);
    assert(bitMap[9].bits[0] == 1023);
    assert(bitMap[10].bits[0] == 2047);
    assert(bitMap[11].bits[0] == 4095);
    assert(bitMap[12].bits[0] == 8191);
    assert(bitMap[13].bits[0] == 16383);
    assert(bitMap[14].bits[0] == 32767);
    assert(bitMap[15].bits[0] == 65535);
    
    free(ppStart);
    free(ppEnd);
	
    return 0;
}