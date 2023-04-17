// frama-c-gui IP_string_test.c

#include <limits.h>

/*@
  requires \valid(s + (0..len));
  requires len < UINT_MAX;
  assigns \result;
  behavior good_input:
   assumes \forall integer i; 0 <= i < len ==> s[i] != '<' && s[i] != '>';
   ensures \result == 0;
  behavior  bad_input:
   assumes \exists integer i; 0 <= i < len && (s[i] == '<' || s[i] == '>');
   ensures \result == -1;
  complete behaviors good_input, bad_input;
  disjoint behaviors good_input, bad_input;
*/
int test(const char*s, unsigned int len) {
	int ret = 0;
	unsigned int i, j;
	char c[2] = {'<','>'};
	/*@
      loop invariant 0 <= i <= len;
      loop invariant ret == -1 || ret == 0;
      loop invariant GOOD: (ret == 0)  ==> \forall integer m; 0 <= m < i ==> s[m] != '<' && s[m] != '>';
      loop invariant BAD:  (ret == -1) ==> \exists integer m; 0 <= m < i && (s[m] == '<' || s[m] == '>');
      loop assigns i, j, ret;
    */
	for(i = 0; i < len; i++) {
		//@ assert (ret == 0) ==> \forall integer m; 0 <= m < i ==> s[m] != '<' && s[m] != '>';
		//@ assert (ret == -1) ==> \exists integer m; 0 <= m < i && (s[m] == '<' || s[m] == '>');
		/*@
	      loop invariant 0 <= j <= 2;
	      loop invariant ret == -1 || ret == 0;
	      loop invariant (ret == 0) ==> \forall integer m; 0 <= m < i ==> s[m] != '<' && s[m] != '>';
		  loop invariant (ret == 0) ==> \forall integer m; 0 <= m < j ==> s[i] != c[m];
	      loop invariant (ret == -1) ==> \exists integer m; 0 <= m <= i && (s[m] == '<' || s[m] == '>');
	      loop assigns j, ret;
	    */
		for(j = 0; j < 2; j++) {
			if (s[i] == c[j]) {
				ret = -1;
			}
		}
	}
	return ret;
}

int main() {
	int len = 15;
	char s1[16] = "192.168.0.1";
	int  r1     = test(s1, len);
	char s2[16] = "192.168.0<1";
	int  r2     = test(s2, len);
}
