// frama-c-gui mbedtls_zeroize_while.c

#include <stdio.h>
#include <stdlib.h>
/*@
  requires \valid(((char *)v)+(0..n-1));
  requires n > 0;
  assigns ((char*)v)[0..\old(n)-1];
  ensures \forall integer i; 0 <= i < \old(n) ==> ((char*)v)[i] == 0;
@*/
static void mbedtls_zeroize(void *v, unsigned int n) {

  char *p = v;
  //@ ghost size_t N = n;
  /*@
    loop invariant 0 <= N - n <= N;
    loop invariant n >= 0;
    loop invariant p == ((char*)v) + (N - n);
    loop invariant \forall integer j; 0 <= j < N - n ==> ((char*)v)[j] == 0;
    loop assigns ((char*)v)[0..N-1], n, p;
  */
  while( n-- )
    *p++ = 0;
}
