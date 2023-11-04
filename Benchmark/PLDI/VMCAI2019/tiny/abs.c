
/* Summary:
 *
 * [ x0 >= 0 ]
 * %ret = x0 and %ret = x and %ret >= 0
 * 
 * or
 * 
 * [ x0 <= -1 ]
 * %ret = -x0 and %ret = -x and %ret >= 1
 *
 */
int my_abs(int x)
{
    int r;

    if(x < 0)
        r = -x;
    else
        r = x;

    return r;
}

void test()
{
    int r;
    int k = 42;

    r = my_abs(k);
}

