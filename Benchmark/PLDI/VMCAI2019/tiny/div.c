
/* Summary:

[ 2b0 >= a0 and a0 >= b0+1 ]
a = a0 and r = a-b and b = b0 and q = 1 and 2b >= a and a >= b+1

or

[ b0 >= 1 and a0 >= 2b0+1 ]
a = a0 and b = b0 and r >= 1 and q >= 1 and q+r >= 3 and b >= r
and a+1 >= 2b+q and a >= 2b+1

or

[ b0 >= a0 and b0 >= 1 and a0 >= 0 ]
a = a0 and r = a and b = b0 and q = 0 and b >= a and b >= 1 and a >= 0

or

[ a0 >= 0 and b0 <= 0 ]
a = a0 and b = b0 and q = q0 and r = r0 and b <= 0 and a >= 0

or

[ a0 <= -1 ]
a = a0 and b = b0 and q = q0 and r = r0 and a <= -1

*/
void div(int a, int b, int * q, int * r)
{
    if(a < 0)
        return;

    if(b < 1)
        return;

    *q = 0;
    *r = a;

    if(*r > b)
    {
        do
        {
            *r = *r - b;
            *q = *q + 1;
        }
        while(*r > b);
    }
}

void test()
{
    int a = 6;
    int b = 2;
    int q;
    int r;

    div(a, b, &q, &r);
}
