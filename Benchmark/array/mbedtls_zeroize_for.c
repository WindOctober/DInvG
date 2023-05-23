// frama-c-gui mbedtls_zeroize_for.c

#include <stdio.h>
#include <stdlib.h>
/*@ 
  requires \valid((char *)(v+(0..n-1)));
  requires n > 0;
  assigns ((char*)v)[0..n - 1];
  ensures \forall integer i; 0 <= i < n ==> ((char*)v)[i] == 0;
@*/
static void mbedtls_zeroize(void *v, size_t n) {

  char *p = v;
  /*@
    loop invariant 0 <= i <= n;
    loop invariant \forall integer j; 0 <= j < i ==> ((char*)p)[j] == 0;
    loop assigns ((char*)p)[0..n-1], i;
  */
  for(int i=0; i<n ; i++)
    p[i] = 0;
}
