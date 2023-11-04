
/* Summary:
 *
 * [ a0 <= 0 ]
 * %ret = a0 and %ret = a and %ret <= 0
 *
 * or
 *
 * [ a0 >= 1 ]
 * %ret = 2a0 and %ret = 2a and %ret >= 2
 *
 */
int mul2(int a)
{
    int x = a;
    int i;

    for(i = 0; i < a; i++)
    {
        x = x+1;
    }

    return x;
}

void test()
{
    int r;
    int a;

    r = mul2(a);
}
