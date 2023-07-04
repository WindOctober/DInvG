// frama-c-gui max_seq.c


int max_seq(int* p, int n) {
    int res = *p;

    for(int i = 0; i < n; i++) {
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
