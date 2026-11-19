int x;
/*@
context Perm(x,1);
requires x >= 0;
ensures x == 2*\old(x) && \old(x) >= 0;
*/
void incr(){
  int n = x;
//@ ghost int pre_x = x;
  //@ loop_invariant Perm(x,1);
//@loop_invariant i + n - x == 0 && pre_x == n && 2*n >= x && x >= n;
  for(int i = 0; i < n; i++) {
    x++;
  }
}

/*@
context Perm(x,1);
requires x >= 0;
ensures x == \old(x) * 2;
*/
void main() {
    incr();
}
