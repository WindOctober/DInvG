// frama-c-gui max_seq.c


int max_seq(int* p, int n) {
    int res=*p;
    /*@
	 loop invariant \forall integer IndexI; 0 <= IndexI < i ==> ((res >= p[IndexI]) || res == p[IndexI]) ;
     loop invariant 
        ((i == n))
	||	((0 <= i) && (-1 * i + n - 1 >= 0));
	 loop assigns i,res;
	 */
    for(int i = 0; i < n; i++) {
        if (res < p[i]) {
            res = p[i];
        }
    }   
    return res;
}

