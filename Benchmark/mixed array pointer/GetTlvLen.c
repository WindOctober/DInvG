#define HEADER_TAG_LEN_SIZE 256
static Uint32 GetTlvLen(BuffConst **array, Uint32 arrayNum)
{
    Uint32 i = 0;
    Uint32 totalLen = 0;
    for (; i < arrayNum; ++i) {
        /* if equal, only tag + len */
        totalLen += (array[i] == NULL) ? HEADER_TAG_LEN_SIZE : HEADER_TAG_LEN_SIZE + array[i]->len;
    }
    return totalLen;
}
