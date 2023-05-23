// frama-c-gui adp_1.c
#include <stdio.h>
#include <stdlib.h>

typedef struct tagPatchFileDescS
{
    char acSubFileVer[32];
    unsigned int uiPatchType;
    unsigned int uiBoardType;
    unsigned int uiInterfaceType;
    unsigned int uiCpuType;
    unsigned int uiOtherType;
    unsigned int uiOffset;
    unsigned int uiLength;
    unsigned int uiReserve;
} PATCH_DESC_S;

typedef struct tagLoadPatchHeaderS
{
    char acMainVer[32];
    char acPatchVer[32];
    unsigned int uiPatchType;
    unsigned int uiPatchNum;
    unsigned int uiFileLen;
    unsigned short usCrc;
    unsigned short usReserve;
    PATCH_DESC_S astPatchInfo[100];
} LOAD_PATCH_HEADER_S;

unsigned int bootload_get_file_from_patch_pkg(const LOAD_PATCH_HEADER_S* pstPatHeader, unsigned int uiFileType, unsigned int* puiOffset, unsigned int* uiLen);
int get_patch_cms_info_for_pat(LOAD_PATCH_HEADER_S* file_buf, unsigned int* pat_len, unsigned int* offset);

//@ ghost int g = -1;
/*@
	requires \separated(pstPatHeader, puiOffset, uiLen);
	requires \valid(pstPatHeader) && \valid(puiOffset) && \valid(uiLen);
 
	assigns *puiOffset, *uiLen, g;
 
	behavior null_input:
		assumes pstPatHeader == NULL || puiOffset == NULL || uiLen == NULL;
		ensures \result == 1;
   
	behavior good_input:		
		assumes \exists integer uiIndex; (0 <= uiIndex < \min(100, pstPatHeader->uiPatchNum) 
		    && (uiFileType == pstPatHeader->astPatchInfo[uiIndex].uiPatchType));
		ensures \result == 0;
		ensures 0 <= g < \min(100, pstPatHeader->uiPatchNum);
		ensures *puiOffset == pstPatHeader->astPatchInfo[g].uiOffset;
		ensures *uiLen == pstPatHeader->astPatchInfo[g].uiLength;
   
	behavior bad_input:				
		assumes \forall integer uiIndex; 0<= uiIndex < \min(100, pstPatHeader->uiPatchNum) 
			==> (uiFileType != pstPatHeader->astPatchInfo[uiIndex].uiPatchType); 
		ensures \result == 1;
  
  complete behaviors;
  disjoint behaviors;
*/
unsigned int bootload_get_file_from_patch_pkg(const LOAD_PATCH_HEADER_S* pstPatHeader, unsigned int uiFileType, unsigned int* puiOffset, unsigned int* uiLen)
{
	//@ ghost g = -1;
    unsigned int uiIndex = 0;
	int ret = 1;
    if ((pstPatHeader == ((void*)0)) || (puiOffset == ((void*)0)) || (uiLen == ((void*)0))){
        return ret;
    }
	
	/*@
		loop invariant 0 <= uiIndex <= \min(100, pstPatHeader->uiPatchNum);
		loop invariant ret == 0 || ret == 1;
		loop invariant (ret == 0) ==> (0 <= g < \min(100, pstPatHeader->uiPatchNum));
		loop invariant (ret == 1) ==> (\forall integer i; 0<= i < uiIndex ==> (uiFileType != pstPatHeader->astPatchInfo[i].uiPatchType));
		loop assigns uiIndex, ret, *puiOffset, *uiLen;
	*/
    for (uiIndex = 0;uiIndex < pstPatHeader->uiPatchNum && uiIndex < 100;uiIndex++){
        if (uiFileType == pstPatHeader->astPatchInfo[uiIndex].uiPatchType){
			//@ ghost g = uiIndex;
            *puiOffset = pstPatHeader->astPatchInfo[uiIndex].uiOffset;
            *uiLen = pstPatHeader->astPatchInfo[uiIndex].uiLength;
			ret = 0;
            return ret;
        }
    }

    return ret;
}


/*@	requires \valid(file_buf);
 
	behavior null_input:
		assumes file_buf == NULL;
		ensures \result == 1;
   
	behavior bad_input_1:
		assumes \forall integer i; 0 <= i < \min(100, file_buf->uiPatchNum)
			==> (0xAA != file_buf->astPatchInfo[i].uiPatchType);
		assumes \forall integer i; 0 <= i < \min(100, file_buf->uiPatchNum)
			==> (0xAE != file_buf->astPatchInfo[i].uiPatchType);
		ensures \result == 1;
		
	behavior bad_input_2:
		assumes \exists integer j; (0 <= j < \min(100, file_buf->uiPatchNum)
				&& 0xAA == file_buf->astPatchInfo[j].uiPatchType
				&& file_buf->astPatchInfo[j].uiLength == 0
				&& (\forall integer i; 0 <= i < j ==> 0xAA != file_buf->astPatchInfo[i].uiPatchType));	
		assumes \exists integer j; (0 <= j < \min(100, file_buf->uiPatchNum)
				&& 0xAE == file_buf->astPatchInfo[j].uiPatchType
				&& file_buf->astPatchInfo[j].uiLength == 0
				&& (\forall integer i; 0 <= i < j ==> 0xAE != file_buf->astPatchInfo[i].uiPatchType));
		ensures \result == 1;

  behavior bad_input_3:
    assumes \forall integer i; 0 <= i < \min(100, file_buf->uiPatchNum)
			==> (0xAE != file_buf->astPatchInfo[i].uiPatchType);
		assumes \exists integer j; (0 <= j < \min(100, file_buf->uiPatchNum)
				&& 0xAA == file_buf->astPatchInfo[j].uiPatchType
				&& file_buf->astPatchInfo[j].uiLength == 0
				&& (\forall integer i; 0 <= i < j ==> 0xAA != file_buf->astPatchInfo[i].uiPatchType));
		ensures \result == 1;
  
  behavior bad_input_4:
    assumes \forall integer i; 0 <= i < \min(100, file_buf->uiPatchNum)
			==> (0xAA != file_buf->astPatchInfo[i].uiPatchType);
		assumes \exists integer j; (0 <= j < \min(100, file_buf->uiPatchNum)
				&& 0xAE == file_buf->astPatchInfo[j].uiPatchType
				&& file_buf->astPatchInfo[j].uiLength == 0
				&& (\forall integer i; 0 <= i < j ==> 0xAE != file_buf->astPatchInfo[i].uiPatchType));
		ensures \result == 1;
   
	behavior good_input_1:
		assumes \exists integer i; (0<= i < \min(100, file_buf->uiPatchNum)
			&& 0xAA == file_buf->astPatchInfo[i].uiPatchType && file_buf->astPatchInfo[i].uiLength != 0);
		ensures \result == 0;
		ensures 0<= g < \min(100, file_buf->uiPatchNum);
		ensures *offset == file_buf->astPatchInfo[g].uiOffset;
		ensures *pat_len == file_buf->astPatchInfo[g].uiLength;
		assigns *offset, *pat_len, g;
 
  behavior good_input_2:
    assumes \forall integer i; 0 <= i < \min(100, file_buf->uiPatchNum)
      ==> (0xAA != file_buf->astPatchInfo[i].uiPatchType) && (0xAA == file_buf->astPatchInfo[i].uiPatchType && file_buf->astPatchInfo[i].uiLength == 0);
    assumes \exists integer i; (0<= i < \min(100, file_buf->uiPatchNum)
			&& (0xAE == file_buf->astPatchInfo[i].uiPatchType) && file_buf->astPatchInfo[i].uiLength != 0);
		ensures \result == 0;
		ensures 0<= g < \min(100, file_buf->uiPatchNum);
		ensures *offset == file_buf->astPatchInfo[g].uiOffset;
		ensures *pat_len == file_buf->astPatchInfo[g].uiLength;
		assigns *offset, *pat_len, g;
  
  disjoint behaviors;
  complete behaviors;
*/
int get_patch_cms_info_for_pat(LOAD_PATCH_HEADER_S* file_buf, unsigned int* pat_len, unsigned int* offset)
{
    int ret;
    unsigned int length_of_check = 0;
    unsigned int offset_of_check = 0;
    ret = (int)bootload_get_file_from_patch_pkg((LOAD_PATCH_HEADER_S*)(unsigned int)file_buf, 0xAA, &offset_of_check, &length_of_check);
    //@ for good_input_1: assert ret == 0;
    //@ for bad_input_1: assert ret == 1;
    //@ for bad_input_2: assert ret == 0;
    //@ for bad_input_3: assert ret == 0;
    //@ for bad_input_4: assert ret == 1;
    if ((ret) || (length_of_check == 0)){
        ret = (int)bootload_get_file_from_patch_pkg((LOAD_PATCH_HEADER_S*)(unsigned int)file_buf, 0xAE, &offset_of_check, &length_of_check);
        //@ for good_input_2: assert ret == 0;
        //@ for bad_input_1: assert ret == 1;
        //@ for bad_input_2: assert ret == 0;
        //@ for bad_input_4: assert ret == 0;
        //@ for bad_input_3: assert ret == 1;
        if ((ret) || (length_of_check == 0)){
            return 1;
        }
    }
    *pat_len = length_of_check;
    *offset = offset_of_check;
    return 0x0;
}