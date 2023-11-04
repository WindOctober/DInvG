
/* Summary:

[ n0 = 0 and m0 = 0 ]
n0 = 0 and m = 0 and m0 = 0 and n = 0 and r = 0

or

[ n0 = 0 and m0 >= 1 ]
r = m and r = m0 and n0 = 0 and n = 0 and r >= 1

or

[ n0 >= m0 and n0 >= 1 and m0 >= 0 ]
r = n0 and r = n and m = m0 and m0 >= 0 and r >= m0 and r >= 1

or

[ m0 > n0 and n0 >= 1 ]
r = m and r = m0 and n = n0 and n >= 1 and r > n

or

[ m0 <= -1 and n0 >= 0 ]
r = r0 and n = n0 and m = m0 and m0 <= -1 and n >= 0

or

[ n0 <= -1 ]
r = r0 and n = n0 and m = m0 and n <= -1

*/
void loop_seq(int * r, int n, int m) {
    int i;
    int j;

    if(n < 0 || m < 0)
        return;

    *r = 0;
    i = 0;

    while(i < n){
        *r = *r + 1;
        i++;
    }

    j = i;
    while(j < m){
        *r = *r + 1;
        j++;
    }
}

void test()
{
    int r;
    int n;
    int m;
    loop_seq(&r, n, m);
}
