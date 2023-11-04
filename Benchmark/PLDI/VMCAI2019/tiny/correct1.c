
/* Summary
 *
 * [ x0 <= obj0 + tol0 ]
 * x = x0 and obj = obj0 and tol = tol0 and step = step0
 * and x <= obj+tol0
 *
 * or
 *
 * [ x0 > obj0 + tol0 and step0 >= 1 ]
 * obj = obj0 and tol = tol0 and step = step0 and x <= obj+tol0
 * and x0 >= obj+tol0+1 and x+step0 >= obj+tol0+1
 *
 * or
 * 
 * [ step0 <= -1 and tol0 >= 0 ] 
 * x = x0 and obj = obj0 and tol = tol0 and step = step0
 * and step0 <= -1 and tol0 >= 0
 *
 * or
 *
 * [ tol0 <= -1 ]
 * x = x0 and obj = obj0 and tol = tol0 and step = step0 and tol0 <= -1
 *
 */
void correct1(int * x, int obj, int tol, int step)
{
    if(tol < 0 || step < 0)
        return;

    int err = *x - obj;

    while(err > tol)
    {
        if(err > tol)
            *x = *x - step;
        else if(err < -tol)
            *x = *x + step;

        err = *x - obj;
    }
}

void test()
{
    int x;
    int obj;
    int tol;
    int step;

    correct1(&x, obj, tol, step);
}
