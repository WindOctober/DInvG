
/* Summary:
 *
 * [ n0 = 0 and c0 <= 0 ]
 * r = a0 and r = a and b = b0 and c = c0 and n = 0 and n0 = 0 and c0 <= 0 
 *
 * or
 *
 * [ n0 = 0 and c0 >= 1 ]
 * r = b and r = b0 and a = a0 and c = c0 and n = 0 and n0 = 0 and c0 >= 1
 *
 * or
 *
 * [ c0 <= n0 and n0 >= 1 ]
 * r = a0 and r = a and b = b0 and c = c0 and n = n0 and c0 <= n0 and n0 >= 1
 *
 * or
 *
 * [ n0 >= 1 and c0 > n0 ]
 * r = b and r = b0 and a = a0 and c = c0 and n = n0 and n0 >= 1 and c0 > n0
 *
 * or
 *
 * [ n0 <= -1 ]
 * r = r0 and a = a0 and b = b0 and c = c0 and n = n0 and n0 <= -1
 *
 */
void indirect(int * r, int a, int b, int c, int n)
{
    if(n < 0)
       return; 

    int i;
    int j;

    i = 0;
    j = 0;

    while(i < n)
    {
        i = i + 1;
        j = j + 1;
    }

    if(j >= c)
    {
        *r = a;
    }
    else
    {
        *r = b;
    }
}

void test()
{
    int r;
    int a;
    int b;
    int c;
    int n;

    indirect(&r, a, b, c, n);
}
