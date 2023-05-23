// frama-c-gui max_seq.c

/*@ requires n > 0 && \valid(p + (0..n-1));
    ensures \forall int i; 0 <= i <= n−1 ==> \result >= p[i];
    ensures \exists int e; 0 <= e <= n−1 && \result == p[e];
*/
int max_seq(int* p, int n) {
    int res = *p;
    //@ ghost int e = 0;
    /*@ loop invariant \forall integer j;
            0 <= j < i ==> res >= p[j];
        loop invariant \valid(p + e) && p[e] == res;
        loop invariant about_i: 0 <= i <= n;
        loop invariant 0 <= e < n;
        loop invariant p == \at(p, Pre) && n == \at(n, Pre);
        loop invariant \valid(p + (0..n-1));
    */
    for(int i = 0; i < n; i+=2) {
        if (res < p[i]) {
            res = p[i];
            //@ ghost e = i;
        }
    }
    return res;
}


int main() {
    int array[10] = {3, 1, 4, 1, 5, 9, 2, 6, 5, 3};
    int m = max_seq(array, 10);
    //@ assert \exists int i; m == array[i];
    //@ assert \forall int i; 0 <= i < 10 ==> m >= array[i];
    return 0;
}
