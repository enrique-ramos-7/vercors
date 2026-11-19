int x;
/*@
context Perm(x,1);
*/
void incr1(){
  int n = x;
  //@ loop_invariant Perm(x,1);
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
*/
void incr3(){
  int n = x;
  //@ loop_invariant Perm(x,1);
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