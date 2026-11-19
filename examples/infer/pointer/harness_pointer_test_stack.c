


/*@contract@*/
void swap(int *a, int *b) {
    int tmp = *a;
    *a = *b;
    *b = tmp;
}



int main() {
    int x = 1;
    int y = 2;
    swap(&y, &x);
    return x;
}

 void harness_main()
{
assume((1 != 0));
	int main_result = main();
assert(main_result == 2);
}
