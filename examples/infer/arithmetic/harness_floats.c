float p,q,r;


/*@contract@*/
float foo (float a, float b) {

    return (a * b) / 2;
}


/*@contract@*/
    
float bar (float x) {
    float y = 1;
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
assert((1 != 0) && p == ($at("Old", (float)(p)) + 1) * 42 && (r == $at("Old", (float)(q)) * $at("Old", (float)(r))) / 2);
}
