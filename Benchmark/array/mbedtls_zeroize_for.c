#include <stdio.h>
#include <stdlib.h>
/*@
  requires \valid((char *)(v+(0..n-1)));
  requires n > 0;
  assigns ((char*)v)[0..n - 1];
  ensures \forall integer i; 0 <= i < n ==> ((char*)v)[i] == 0;
@*/
void mbedtls_zeroize(void *v, int n)
{
  char *p;
  for (int i = 0; i < n; i++){
    p[i] = 0;
  }
}
