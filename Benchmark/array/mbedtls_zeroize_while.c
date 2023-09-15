// frama-c-gui mbedtls_zeroize_while.c

#include <stdio.h>
#include <stdlib.h>

static void mbedtls_zeroize(void *v, unsigned int n)
{
  char *p = v;
  while (n--)
  {
    *p++ = 0;
  }
}
