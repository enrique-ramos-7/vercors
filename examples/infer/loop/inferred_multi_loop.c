int x;
/*@
context Perm(x,1);
requires x >= 0;
ensures x >= 0 && \old(x) >= 0 && ((x == 2*\old(x) && \old(x) >= 2) || (x == 2 && \old(x) == 1) || (x == 0 && \old(x) == 0));
*/
void incr1(){
  int n = x;
//@ ghost int pre_x = x;
  //@ loop_invariant Perm(x,1);
//@loop_invariant pre_x == n && i >= 0 && x >= 0 && n >= 0 && ((i + n - x == 0 && 2*n >= x && x - n >= 1 && x >= 4) || (i == 1 && x - n == 1 && n >= 1) || (i == 0 && x == n));
  for(int i = 0; i < n; i++) {
    x++;
  }
}

/*@
context Perm(x,1);
*/
void incr2(){
  int n = x;
  //@ loop_invariant Perm(x,1);
  for(int i = 0; i < n; i++) {
    x++;
  }
}

/*@
context Perm(x,1);
requires x != 1 && x >= 0;
ensures x >= 0 && \old(x) >= 0 && ((x == 0 && \old(x) != 2 && 3 >= \old(x)) || (\old(x) >= 1 && (\old(x) != 2 || x == 4) && (x == 2*\old(x) || 3 >= \old(x))));
*/
void incr3(){
  int n = x;
//@ ghost int pre_x = x;
  //@ loop_invariant Perm(x,1);
//@loop_invariant pre_x == n && i >= 0 && x >= 0 && n >= 0 && ((i + n - x == 0 && 2*n >= x && x - n >= 3 && n >= 4) || (i == 3 && x - n == 3 && n >= 3) || (i == 2 && x - n == 2 && n >= 2) || (i == 1 && x - n == 1 && n >= 2) || (i == 0 && x == n && n >= 2) || (i == 0 && x == 0 && n == 0));
  for(int i = 0; i < n; i++) {
    x++;
  }
}

/*@
context Perm(x,1);
requires x >= 0;
ensures x == \old(x) * 4;
*/
void main() {
    incr1();
    incr3();
}
