


/*@
requires \pointer_index(b,0,write);
requires \pointer_index(a,0,write);
ensures \pointer_index(b,0,write);
ensures \pointer_index(a,0,write);

requires (b != NULL) && (a != NULL) && *b == 1 && *a == 2;
ensures (b != NULL) && (a != NULL) && \old(*b) == 1 && *a == 1 && *b == 2 && \old(*a) == 2;
*/
void swap(int *a, int *b) {
    int tmp = *a;
    *a = *b;
    *b = tmp;
}


/*@
requires true;
ensures \result == 2;
*/
int main() {
    int x = 1;
    int y = 2;
    swap(&y, &x);
    return x;
}
