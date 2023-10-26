// frama-c-gui numeq.c

/*------------------------ Preparation -----------------------*/
/*@
    // number of equals signs before index i
    logic integer num_eq(char* a, integer i) =
        i <= 0 ? 0 :
        (a[i - 1] == '=' ? num_eq(a, i - 1) + 1 : num_eq(a, i - 1));

    axiomatic Num_Eq {
        axiom MONO_INCR_NUM_EQ:
            \forall char* a, int i, j; i <= j
                ==> num_eq(a, i) <= num_eq(a, j);
}*/

/*@
    requires \valid(array + (0 .. nEncoded - 1));
    requires nEncoded > 1;

    behavior ERR:
        assumes num_eq(array, nEncoded) > 2;
        ensures \result == -1;
    behavior SUCCESS:
        assumes num_eq(array, nEncoded) <= 2;
        ensures \result == 0;

    complete behaviors;
    disjoint behaviors;
*/
int GetDecLen(const char *array, int nEncoded)
{
    int i = 0;
    int equalSignNum = 0;
    int ret = 0;
    /* count of "=" */
    // the following assertion is important.
    //@ assert \forall char* a, int i; num_eq(a, i) <= num_eq(a, i + 1);

    while (i < nEncoded)
    {
        if (array[i] == '=')
        {
            if (++equalSignNum > 2)
            {
                ret = -1;
                break;
            }
        }
        ++i;
    }

    return ret;
}