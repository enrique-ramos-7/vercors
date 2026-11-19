int p,q,r;

/*@
    context Perm(p,1);
    context Perm(q,1);
    context Perm(r,1);
requires a == q && b >= 0 && r >= 0 && q >= 0;
ensures p == \old(p) && r >= 0 && q >= 0 && \old(b) >= 0 && \old(a) >= 0 && \old(r) >= 0 && \old(q) >= 0 && \old(a) * \old(b) - \result == -1;
@*/
int foo (int a, int b) {

    return a * b + 1;
}

/*@
    context Perm(p,1);
    context Perm(q,1);
    context Perm(r,1);
requires -1 >= x && r >= 0 && q >= 0 && -1 >= p;
ensures \result - 42*\old(x) == 42 && r == \old(r) && q == \old(q) && -1 >= p && -1 >= \old(p) && -1 >= \old(x) && \old(r) >= 0 && \old(q) >= 0;
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
