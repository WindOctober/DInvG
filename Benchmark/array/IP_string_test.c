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
	for(i = 0; i < len; i++) {
		for(j = 0; j < 2; j++) {
			if (s[i] == c[j]) {
				ret = -1;
			}
		}
	}
	return ret;
}

// int main() {
// 	int len = 15;
// 	char s1[16] = "192.168.0.1";
// 	int  r1     = test(s1, len);
// 	char s2[16] = "192.168.0<1";
// 	int  r2     = test(s2, len);
// }
