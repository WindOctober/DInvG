
/* Summary:
 *
 *  [ b0 <= 0 ]
 *  %ret = a0 and %ret = a and b = b0 and b0 <= 0
 *
 *  or
 *
 *  [ b0 >= 1 ]
 *  %ret = a+4b and %ret = a+4b0 and a = a0 and %ret >= a+4
 *
 */
int ex2b(int a, int b)
{
    int x = a;
    int y = b;
    int i;
    
    for (i=0; i < y; i++) 
    {
        x = x + 2;
    }

    for (i=0; i < y; i++) 
    {
        x = x + 2;
    }

    return x;
}

void test()
{
    int a;
    int b;

    int r = ex2b(a, b);
}
