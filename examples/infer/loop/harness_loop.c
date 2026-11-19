int x;

/*@contract@*/
void incr(){
  int n = x;
  
  for(int i = 0; i < n; i++) {
    x++;
  }
}


void main() {
    incr();
}

 void harness_main()
{
assume(x >= 0);
	main();
assert(x == $at("Old", (int)(x)) * 2);
}
