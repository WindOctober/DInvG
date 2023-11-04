
/*----------------------------------------------------------------------
 *  WCET Benchmark created by Andreas Ermedahl, Uppsala university, 
 *  May 2000.  
 *
 *  The purpose of this benchmark is to have two loop where the inner 
 *  loops max number of iterations depends on the outer loops current 
 *  iterations.  The results corresponds to something Jannes flow-analysis 
 *  should produce.
 *
 * The example appeard for the first time in: 
 * 
 *  @InProceedings{Ermedahl:Annotations,
 * author =       "A. Ermedahl and J. Gustafsson",
 * title =        "Deriving Annotations for Tight Calculation of Execution Time",
 * year =         1997,
 * month =        aug,
 * booktitle =    EUROPAR97,
 * publisher =    "Springer Verlag",
 * pages =        "1298-1307"
 * }
 *
 * The result of Jannes tool is something like:
 *   outer loop:       1   2   3   4   5   6   7   8   9   10   11 
 *   inner loop max:   5   9   8   7   4   2   1   1   1   1    1 
 *
 *----------------------------------------------------------------------*/

extern int undet();
extern void __assume(int cond);

void janne_complex(int * cnt1,
                   int * cnt2,
                   int a, 
                   int b)
{
    int x = a;
    int y = b;
    *cnt1 = 0; *cnt2 = 0;
    while(x < 30)
    {
        *cnt1 = *cnt1 + 1;
        while(y < x)
        {
            *cnt2 = *cnt2 + 1;
            if(y > 5) 
                y = y * 3; 
            else
                y = y + 2;
            if(y >= 10 && y <= 12) 
                x = x + 10;
            else 
                x = x + 1;
        }
        
        x = x + 2; 
        y = y - 10; 
    }
}

int main()
{   
    int a1 = undet(), b1 = undet(), cnt1, cnt2;
    __assume(a1 >= 0); __assume(b1 >= 0);
    
    {
        int x1 = a1;
        int y1 = b1;
        cnt1 = 0; cnt2 = 0;
        while(x1 < 30)
        {
            cnt1 = cnt1 + 1;
            while(y1 < x1)
            {
                cnt2 = cnt2 + 1;
                if(y1 > 5) 
                    y1 = y1 * 3; 
                else
                    y1 = y1 + 2;
                if(y1 >= 10 && y1 <= 12) 
                    x1 = x1 + 10;
                else 
                    x1 = x1 + 1;
            }
            
            x1 = x1 + 2; 
            y1 = y1 - 10; 
        }
    }

  return 0;
}



