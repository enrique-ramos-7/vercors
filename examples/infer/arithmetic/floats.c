float p,q,r;

/*@
    context Perm(p,1);
    context Perm(q,1);
    context Perm(r,1);
@*/
float foo (float a, float b) {

    return (a * b) / 2;
}

/*@
    context Perm(p,1);
    context Perm(q,1);
    context Perm(r,1);
@*/    
float bar (float x) {
    float y = 1;
    y += x;
    y *= 42;
    return y;
}

/*@
    context Perm(p,1);
    context Perm(q,1);
    context Perm(r,1);
    requires p < 0 && q >= 0  && r >= 0;
    ensures (p == (\old(p)+1) * 42) && ((r == \old(q) * \old(r)) / 2);
@*/
void main() {
    p = bar(p);
    r = foo(q,r);
}