// frama-c-gui file_from_patch.c
#include <stdio.h>
#include <stdlib.h>

typedef struct PD
{
    char acs[32];
    unsigned int type;
    unsigned int Btype;
    unsigned int Intype;
    unsigned int cptype;
    unsigned int otype;
    unsigned int uoffset;
    unsigned int Length;
    unsigned int Reserve;
} PDS;

typedef struct PH
{
    char mver[32];
    char aver[32];
    unsigned int type;
    unsigned int num;
    unsigned int uiFileLen;
    unsigned short usCrc;
    unsigned short usReserve;
    PDS ast[100];
} load_head;

unsigned int file_from_patch(const load_head* psthead, unsigned int filetype,
    unsigned int* pset, unsigned int* uiLen);
//int info_pat(const char* file_buf, unsigned int* len, unsigned int* offset);
int info_pat(load_head* file_buf, unsigned int* len, unsigned int* offset);

//@ ghost int g = -1;
/*@
    behavior null_input:
        assumes psthead == NULL || pset == NULL || uiLen == NULL;
        ensures \result == 1;
    behavior good_input:
        assumes \exists integer uiIndex; (0 <= uiIndex < \min(100, psthead->num)
            && (filetype == psthead->ast[uiIndex].type));
        assumes \valid(psthead) && \valid(pset) && \valid(uiLen);
        assumes \separated(psthead, pset, uiLen);
        ensures \result== 0;
        ensures 0 <= g < \min(100, psthead->num);
        ensures *pset == psthead->ast[g].uoffset;
        ensures *uiLen == psthead->ast[g].Length;
        assigns *pset, *uiLen, g;
    behavior bad_input:
        assumes \forall integer uiIndex; 0 <= uiIndex < \min(100, psthead->num)
            ==> (filetype != psthead->ast[uiIndex].type);
        assumes \valid(psthead) && \valid(pset) && \valid(uiLen);
        assumes \separated(psthead, pset, uiLen);
        ensures \result == 1;
        
    disjoint behaviors null_input, good_input, bad_input;
*/
unsigned int file_from_patch(const load_head* psthead, unsigned int filetype,
    unsigned int* pset, unsigned int* uiLen)
{
    //@ ghost g = -1;
    unsigned int uiIndex= 0;
    int ret= 1;
    if ((psthead == NULL) || (pset == NULL) || (uiLen == NULL)) {
        return ret;
    }

    /*@
    loop invariant 0 <= uiIndex <= \min(psthead->num, 100);
    loop invariant ret == 0 || ret== 1;
    loop invariant (ret == 0) ==> (0 <= g < \min(100, psthead->num));
    loop invariant (ret == 1) ==> (\forall integer i;
            0 <= i < uiIndex ==> (filetype != psthead->ast[i].type));
    loop assigns uiIndex, ret, *pset, *uiLen;
    */
    for (uiIndex = 0; uiIndex < psthead->num && uiIndex < 100; uiIndex++) {
        if (filetype == psthead->ast[uiIndex].type) {
            //@ ghost g = uiIndex;
            *pset = psthead->ast[uiIndex].uoffset;
            *uiLen = psthead->ast[uiIndex].Length;
            ret = 0;
            return ret;
        }
    }
    return ret;
}


/*@
    behavior good_input:
        assumes \exists integer uiIndex; (0 <= uiIndex < \min(100, file_buf->num)
            && (0xAA == file_buf->ast[uiIndex].type) && file_buf->ast[uiIndex].Length != 0);
        assumes \exists integer uiIndex; (0 <= uiIndex < \min(100, file_buf->num)
            && (0xAE == file_buf->ast[uiIndex].type) && file_buf->ast[uiIndex].Length != 0);
        assumes \valid(file_buf);
        assumes \separated(file_buf, len, offset);
        ensures \result== 0;
        ensures 0 <= g < \min(100, file_buf->num);
        ensures *len == file_buf->ast[g].uoffset;
        ensures *offset == file_buf->ast[g].Length;
        assigns *len, *offset;
        
    behavior bad_input:
        assumes \forall integer uiIndex; 0 <= uiIndex < \min(100, file_buf->num)
            ==> ((0xAA != file_buf->ast[uiIndex].type || file_buf->ast[uiIndex].Length ==0) && (0xAE != file_buf->ast[uiIndex].type || file_buf->ast[uiIndex].Length ==0));
        assumes \valid(file_buf);
        assumes \separated(file_buf, len, offset);
        ensures \result== 1;
*/
//int info_pat(const char* file_buf, unsigned int* len, unsigned int* offset)
int info_pat(load_head* file_buf, unsigned int* len, unsigned int* offset)
{
    int ret;
    unsigned int length_of_check = 0;
    unsigned int offset_of_check= 0;
    //@ ghost int g = -1;
    ret = (int)file_from_patch(file_buf, 0xAA, &offset_of_check, &length_of_check);
    //@ for bad_input: assert ret == 1 ;
    if ((ret) || (length_of_check == 0)){
        ret = (int) file_from_patch(file_buf, 0xAE, &offset_of_check, &length_of_check);
        if ((ret) || (length_of_check == 0)){
            return 1;
        }
    }
    *len = length_of_check;
    *offset = offset_of_check;
    return 0x0;
}


typedef struct {
    unsigned char *pC;
    unsigned int ucrlen;
    unsigned char *pcm;
    unsigned int ucmlen;
    unsigned char *pb;
    unsigned int ublen;
} em_sig_info;

int ver_ba_si(em_sig_info *sig_info);

int patch_cms_check(char *file_buf){
    int ret;
    unsigned int length_of_check = 0;
    unsigned int offset;
    char *cm_buf = NULL;
    unsigned int cms_len;
    char *crl_buf = NULL;
    unsigned int crl_len;
    char *pContent = NULL;
    em_sig_info sig_info;

    ret = info_pat(file_buf, &length_of_check, &offset);
    if (ret != 0x0) {
        return 1;
    }
    pContent = file_buf + offset;
    
    ret = (int)file_from_patch((load_head *)(unsigned int)file_buf, 0xA0, &offset, &cms_len);

    if (ret) {
        return 1;
    }
    cm_buf = file_buf + offset;

    ret = (int)file_from_patch((load_head *)(unsigned int)file_buf, 0xA1, &offset, &crl_len);
    
    if (ret) {
        return 1;
    }
    crl_buf= file_buf + offset;
    
    sig_info.pb = (unsigned char *)pContent;
    sig_info.ublen = length_of_check;
    sig_info.pcm = (unsigned char *)(cm_buf);
    sig_info.ucmlen = cms_len;
    sig_info.pC = (unsigned char *)(crl_buf);
    sig_info.ucrlen = crl_len;

    ret = ver_ha_si(&sig_info);
    if(ret) {
        return 1;
    }
    return 0x0;
}

                                 

