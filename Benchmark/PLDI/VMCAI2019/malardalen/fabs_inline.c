
static double fabs(double n,
        int * cptr_fabs_1,
        int * cptr_fabs_2)
{ 
  double f ;
  *cptr_fabs_1 = 0;
  *cptr_fabs_2 = 0;
  {
  if (n >= (double )0) {
    (*cptr_fabs_1) ++;
    f = n;
  } else {
    (*cptr_fabs_2) ++;
    f = - n;
  }
  return (f);
}
}

int main()
{
    double n;
    int cptr_fabs_1;
    int cptr_fabs_2;

    double r;
    {
        double f;
        cptr_fabs_1 = 0;
        cptr_fabs_2 = 0;

        if(n >= (double)0) {
            cptr_fabs_1++;
            f = n;
        } else {
            cptr_fabs_2++;
            f = -n;
        }
        r = f;
    }


    return 0;
}
