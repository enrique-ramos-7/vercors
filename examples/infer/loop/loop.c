int x;
/*@
context Perm(x,1);
*/
void incr(){
  int n = x;
  //@ loop_invariant Perm(x,1);
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