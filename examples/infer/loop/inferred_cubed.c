int x;

/*@
  requires n == x && 10 >= x && x >= 0;
  ensures 10 >= x && x >= 0 && 10 >= \old(n) && \old(n) >= 0 && 10 >= \old(x) && \old(x) >= 0 && ((\result == 1000 && x == 10) || (\result == 729 && x == 9) || (\result == 512 && x == 8) || (\result == 343 && x == 7) || (\result == 216 && x == 6) || (\result == 125 && x == 5) || (\result == 64 && x == 4) || (\result == 27 && x == 3) || (\result == 8 && x == 2) || (\result == 1 && x == 1) || (\result == 0 && x == 0));
*/
int cubed(int n) {
    int i = 0;
    int res = 0;
    int nn = n * n;         
    /* loop invariant for the loop on line 8 */
    //Saida doesn't do loop invariants, have to call tricera manually for that
    //Tricera doesn't generate variants for termination, but the invariant here does work
    /*@
    loop invariant \at(n, Pre) == n && \at(x, Pre) == n && x == n && 10 >= i && i >= 0 && 10 >= n && n >= 0 && ((res == 1000 && i == 10 && n == 10) || (i == 9 && n >= 9 && (n != 10 || nn + res == 1000) && (n != 9 || res == 729)) || (i == 8 && n >= 8 && (n != 10 || 2*nn + res == 1000) && (n != 9 || nn + res == 729) && (n != 8 || res == 512)) || (i == 7 && n >= 7 && (n != 10 || 3*nn + res == 1000) && (n != 9 || 2*nn + res == 729) && (n != 8 || nn + res == 512) && (n != 7 || res == 343)) || (i == 6 && n >= 6 && (n != 10 || 4*nn + res == 1000) && (n != 9 || 3*nn + res == 729) && (n != 8 || 2*nn + res == 512) && (n != 7 || nn + res == 343) && (n != 6 || res == 216)) || (i == 5 && n >= 5 && (n != 10 || 5*nn + res == 1000) && (n != 9 || 4*nn + res == 729) && (n != 8 || 3*nn + res == 512) && (n != 7 || 2*nn + res == 343) && (n != 6 || nn + res == 216) && (n != 5 || res == 125)) || (i == 4 && n >= 4 && (n != 10 || 6*nn + res == 1000) && (n != 9 || 5*nn + res == 729) && (n != 8 || 4*nn + res == 512) && (n != 7 || 3*nn + res == 343) && (n != 6 || 2*nn + res == 216) && (n != 5 || nn + res == 125) && (n != 4 || res == 64)) || (i == 3 && n >= 3 && (n != 10 || 7*nn + res == 1000) && (n != 9 || 6*nn + res == 729) && (n != 8 || 5*nn + res == 512) && (n != 7 || 4*nn + res == 343) && (n != 6 || 3*nn + res == 216) && (n != 5 || 2*nn + res == 125) && (n != 4 || nn + res == 64) && (n != 3 || res == 27)) || (i == 2 && n >= 2 && (n != 10 || 8*nn + res == 1000) && (n != 9 || 7*nn + res == 729) && (n != 8 || 6*nn + res == 512) && (n != 7 || 5*nn + res == 343) && (n != 6 || 4*nn + res == 216) && (n != 5 || 3*nn + res == 125) && (n != 4 || 2*nn + res == 64) && (n != 3 || nn + res == 27) && (n != 2 || res == 8)) || (i == 1 && n >= 1 && (n != 10 || 9*nn + res == 1000) && (n != 9 || 8*nn + res == 729) && (n != 8 || 7*nn + res == 512) && (n != 7 || 6*nn + res == 343) && (n != 6 || 5*nn + res == 216) && (n != 5 || 4*nn + res == 125) && (n != 4 || 3*nn + res == 64) && (n != 3 || 2*nn + res == 27) && (n != 2 || nn + res == 8) && (n != 1 || res == 1)) || (i == 0 && (n != 10 || 10*nn + res == 1000) && (n != 9 || 9*nn + res == 729) && (n != 8 || 8*nn + res == 512) && (n != 7 || 7*nn + res == 343) && (n != 6 || 6*nn + res == 216) && (n != 5 || 5*nn + res == 125) && (n != 4 || 4*nn + res == 64) && (n != 3 || 3*nn + res == 27) && (n != 2 || 2*nn + res == 8) && (n != 1 || nn + res == 1) && (n != 0 || res == 0)));
    */
    while (1) {
        if (i >= n) {
            break;
        }
        res = res + nn;
        i = i + 1;
    }
    return res;
}
//For this to work, x has to be bounded
/*@ requires x >= 0 && x <= 10;
    ensures \result == x * x * x;
*/    
int main() {
    return cubed(x);
}
