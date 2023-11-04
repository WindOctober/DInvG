extern int undet();

/* Summary:
 *
 * [ a0 >= 0 and n0 = 0 ]
 * r = a and r = a0 and n0 = 0 and n = 0 and r >= 0
 *
 * or
 *
 * [ n0 >= 1 and a0 >= n0 ]
 * r = a and r = a0 and n = n0 and n >= 1 and r >= n
 *
 * or
 *
 * [ a0 >= 0 and a0 < n0 ]
 * r = n0 and r = n and a = a0 and a0 >= 0 and r >= a0+1
 *
 * or
 *
 * [ a0 <= -1 and n0 >= 0 ]
 * r = r0 and n = n0 and a = a0 and a0 <= -1 and n >= 0
 *
 * or
 *
 * [ n0 <= -1 ]
 * r = r0 and n = n0 and a = a0 and n <= -1 
 *
 */
void computed_th(int * r, int n, int a){
    int i;
    int j;
    int th;

    if(n < 0 || a < 0)
        return;

    th = 0;
    i = 0;

    while(i < n){
        th++;
        i++;
    }
    
    j = a;
    while(j < th){
        j++;
    }

    *r = j;
}

void test()
{
    int r;
    int n;
    int a;

    n = undet();
    a = undet();

    computed_th(&r, n, a);
}
