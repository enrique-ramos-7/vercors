int x;

/*@contract@*/
int cubed(int n) {
    int i = 0;
    int res = 0;
    int nn = n * n;  

    while (1) {
        if (i >= n) {
            break;
        }
        res = res + nn;
        i = i + 1;
    }
    return res;
}


    
int main() {
    return cubed(x);
}

 void harness_main()
{
assume(x >= 0 && x <= 5);
	int main_result = main();
assert(main_result == x * x * x);
}
