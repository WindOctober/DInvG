#include <assert.h>
#include <stdio.h>
#include <malloc.h>

void assign(void *v, int len)

{
    char* p=v;
    for (int i = 0; i < len; ++i)

    {
        p[i] = i;
    }
}


// int main() {
//     int len = 0;
// 	for(int i = 0; i < 11; i++)
// 	{
// 		len = 1000;
// 	}
// 	assert(len == 1000);
	
//     int *p = malloc(sizeof(int)*len);
//     assign(p, len);
// 	assert(p[len-1] == len-1);
// }