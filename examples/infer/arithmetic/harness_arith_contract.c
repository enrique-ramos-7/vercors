int p,q,r;


/*@contract@*/
int foo (int a, int b) {

    return a * b + 1;
}


/*@contract@*/
    
int bar (int x) {
    int y = 1;
    y += x;
    y *= 42;
    return y;
}


void main() {
    p = bar(p);
    r = foo(q,r);
}

 void harness_main()
{
assume((1 != 0) && p < 0 && q >= 0 && r >= 0);
	main();
assert((1 != 0) && p == ($at("Old", (int)(p)) + 1) * 42 && r == $at("Old", (int)(q)) * $at("Old", (int)(r)) + 1);
}
