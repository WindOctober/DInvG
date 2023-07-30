// frama-c-gui RFC_isMatch.c

typedef unsigned int U32;

#define ONE_BYTE 16
#define BYTE_COUNT 1

int isMatch( const U32 *pTmpbits, const U32 *bits)
{
    int ret = 1;

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