int p,q,r;

/*@
    context Perm(p,1);
    context Perm(q,1);
    context Perm(r,1);
@*/
int foo (int a, int b) {

    return a * b + 1;
}

/*@
    context Perm(p,1);
    context Perm(q,1);
    context Perm(r,1);
@*/    
int bar (int x) {
    int y = 1;
    y += x;
    y *= 42;
    return y;
}

/*@
    context Perm(p,1);
    context Perm(q,1);
    context Perm(r,1);
    requires p < 0 && q >= 0  && r >= 0;
    ensures (p == (\old(p)+1) * 42) && (r == \old(q) * \old(r) + 1);
@*/
void main() {
    p = bar(p);
    r = foo(q,r);
}