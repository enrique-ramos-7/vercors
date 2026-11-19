int x;

int cubed(int n) {
    int i = 0;
    int res = 0;
    int nn = n * n;  
//@ loop_invariant Perm(x,1);
    while (1) {
        if (i >= n) {
            break;
        }
        res = res + nn;
        i = i + 1;
    }
    return res;
}

/*@ 
context Perm(x,1);
requires x >= 0 && x <= 5;
ensures \result == x * x * x;
*/    
int main() {
    return cubed(x);
}