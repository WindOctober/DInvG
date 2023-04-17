// frama-c-gui nested_string_cmp.c

/*
* 函数功能：字符串输入处理
* 输入参数:
* \param *bufTer: 输入字符串的存放地址
* \param *len: 输出维冲区的长度
* \param fg: XXX 幵头的宏
* \param *list: 键列表
* \param listlen: 键列表长度
* 输出参数 ：
* \param *len: 写入输出缓冲区的数据长度。不包括字符串结束的0
* 返回值：unsigned int: 如果功能键有效，则返回功能键的键值，否则返回0。
*/

#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <string.h>

/*@
  predicate bad_char(char c) = c \in
    {'\\', '<', '>', '?', '"', '~', '/', '\\', '[', '(', ')', '!'};
*/

/*@
  requires \valid(name + (0 .. length));
  requires length < UINT_MAX;
  //assigns \result;
  behavior good_input:
    assumes \forall integer i; 0 <= i < length + 1 ==> !bad_char(name[i]);
    ensures \result == 0;
  behavior  bad_input:
    assumes \exists integer i; 0 <= i < length + 1 && bad_char(name[i]);
    ensures \result == -1;
  complete behaviors good_input, bad_input;
  disjoint behaviors good_input, bad_input;
*/
int test(const char *name, unsigned int length);

/*@
  requires \valid(filename + (0 .. namelength));
  requires namelength < UINT_MAX;
  //assigns \result;
  ensures \result == 0 || \result == -1;
  behavior good_input:
    assumes (\forall integer i; 0 <= i < namelength + 1 ==> !bad_char(filename[i]))
	&& (((fg & 0x02) == 0) && ((fg & 0x01) == 0));
    ensures \result == 0;
  behavior bad_input:
    assumes (\exists integer i; 0 <= i < namelength + 1 && bad_char(filename[i]));
	assumes ((fg & 0x02) == 0) && ((fg & 0x01) == 0);
    ensures \result == -1;
  behavior about_fg:
    assumes !(((fg & 0x02) == 0) && ((fg & 0x01) == 0));
	ensures \result == 0;
  complete behaviors good_input, bad_input, about_fg;
  disjoint behaviors good_input, bad_input, about_fg;
*/
int input_test(const char *filename, unsigned int namelength, unsigned int fg);

unsigned int menu_input_test(unsigned char *buffer, unsigned int *len,
	unsigned int fg, const char *list, unsigned int listlen)
{
	unsigned int bufferlen;
	char filename[513] = {0};
	//@ assert \valid(filename + (0 .. 512));
	unsigned int namelength;
	int res;

	if ((buffer == NULL) || (len == NULL)) {
		return -1;
	}

	bufferlen = *len;
	if ((bufferlen > (513)) || (bufferlen == 0)) {
		return -1;
	}

	/* 获取输入字符串 */
	// res = initial_input(buffer, listlen, len, fg, list);
	// if (res !=0) {
	// 	return (unsigned int)res;
	// }

	/* 去除字符串中的空格 */
	// res = strip_space(buffer, bufferlen, filename, 513);
	// if (res != 0) {
	// 	return -1;
	// }

	// /* 如果去除空格后只刺下结束符，则提示文件名是无效的 */
	// if (strcmp(filename, "") == 0) {
	// 	*len = 0;
	// 	return 0;
	// }

	namelength = strlen(filename);
	//@ assert \valid(filename + (0 .. namelength));
	res = input_test(filename, namelength, fg);
	/*@ assert (!(((fg & 0x02) == 0) && ((fg & 0x01) == 0))) ==> (res == 0);
 	 */
	 /*@ assert ((bad_char(filename[0]))
  	  && ((fg & 0x02) == 0) && ((fg & 0x01) == 0))
 	  ==> res == -1;
  	 */
	 /*@ assert ((\forall integer i; 0 <= i < namelength + 1 ==> !bad_char(filename[i]))
 	&& (((fg & 0x02) == 0) && ((fg & 0x01) == 0)))
	 ==> (res == 0);
	*/


	if (res !=0) {
		*len = 0;
		return 0;
	}

	/* 对字符串处理完成 */
	// *len = namelength;
	// res = strcpy_s((char *)buffer, bufferlen, filename);
	// if (res != 0) {
	// 	return -1;
	// }

	return 0;
}

int input_test(const char *filename, unsigned int namelength, unsigned int fg)
{
	unsigned int type;
	int res = 0;

	if (((fg & 0x02) == 0) && ((fg & 0x01) == 0)) {
		/* 判断文件名是否包含非法的字符 */
		res = test(filename, namelength);
		//@ for bad_input: assert res == -1;
		if (res !=0) {
			return res;
		}
	} else {
		/* ••••• */
	}
	////@ for bad_input: assert res == -1;
	return res;
}
//这个再说
int test(const char *name, unsigned int length)
{
	unsigned int i, j;

	/* 该数组是只存在此函数中的，不是全局定义的数组 */
	char compare[12] = {'\\','<','>','?','"','~','/','\\','[','(',')','!'};

	int ret = 0;	// it's needed to prove the bad_input case

	/*@
      loop invariant 0 <= i <= length + 1;
      loop invariant ret == -1 || ret == 0;
      loop invariant
	    (ret == 0)  ==> \forall integer m; 0 <= m < i ==> !bad_char(name[m]);
      loop invariant
	    (ret == -1) ==> \exists integer m; 0 <= m < i && bad_char(name[m]);
      loop assigns i, j, ret;
    */
	for (i = 0; i < (length + 1); i++) {
		/*@
	      loop invariant 0 <= j <= 12;
	      loop invariant ret == -1 || ret == 0;
	      loop invariant
		    (ret == 0) ==> \forall integer m; 0 <= m < i ==> !bad_char(name[m]);
		  loop invariant
		    (ret == 0) ==> \forall integer m; 0 <= m < j ==> name[i] != compare[m];
	      loop invariant
		    (ret == -1) ==> \exists integer m; 0 <= m <= i && bad_char(name[m]);
		  loop assigns j, ret;
	    */
		for (j = 0; j < 12; j++) {
			if (name[i] == compare[j]) {
				// with the printf() here, it is not possible to
				// prove the crucial "loop assigns" condition
				// printf("The input is invalid\n");
				ret = -1;
				// return ret;
			}
		}
	}

	if(ret) printf("The input is invalid\n");

	return ret;
}
