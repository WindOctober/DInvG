// frama-c-gui mbedtls_ssl_safer_memcmp.c

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/*@
  requires valid_a: valid_read_or_empty(a, n);
  requires valid_b: valid_read_or_empty(b, n);
  requires danglingness:a: non_escaping(a, n);
  requires danglingness:b: non_escaping(b, n);
  
  behavior different:
    assumes \exists integer i; 0 <= i < n && ((volatile const unsigned char *)a)[i] != ((volatile const unsigned char *)b)[i];
    ensures \result != 0;
    
  behavior same:
    assumes \forall integer i; 0 <= i < n ==> (((volatile const unsigned char *)a)[i] == ((volatile const unsigned char *)b)[i]);
    ensures \result == 0;
    
  complete behaviors;
  disjoint behaviors;
*/
static inline int prototype_mbedtls_ssl_safer_memcmp(const void *a, const void *b, size_t n )
{
   size_t i;
   volatile const unsigned char *A = (volatile const unsigned char *) a;
   volatile const unsigned char *B = (volatile const unsigned char *) b;
   volatile unsigned char diff = 0;

  /*@
		loop invariant 0 <= i <= n;
		loop invariant diff == 0 || diff != 0;
		loop invariant (diff != 0) ==> (\exists integer i; 0 <= i < n && A[i] != B[i]);
		loop invariant (diff == 0) ==> (\forall integer i; 0 <= i < n ==> (A[i] == B[i]));
  */
   for( i = 0; i < n; i++ )
   {
       /* Read volatile data in order before computing diff.
        * This avoids IAR compiler warning:
        * 'the order of volatile accesses is undefined ..' */
       unsigned char x = A[i], y = B[i];
       //但这个涉及到位运算，本身有一个逻辑的转化。
       diff |= x ^ y;
   }

   return(diff);
}