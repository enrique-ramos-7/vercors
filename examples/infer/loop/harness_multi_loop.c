int x;

/*@contract@*/
void incr1(){
  int n = x;
  
  for(int i = 0; i < n; i++) {
    x++;
  }
}


/*@contract@*/
void incr2(){
  int n = x;
  
  for(int i = 0; i < n; i++) {
    x++;
  }
}


/*@contract@*/
void incr3(){
  int n = x;
  
  for(int i = 0; i < n; i++) {
    x++;
  }
}


void main() {
    incr1();
    incr3();
}

 void harness_main()
{
assume(x >= 0);
	main();
assert(x == $at("Old", (int)(x)) * 4);
}
