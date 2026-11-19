


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