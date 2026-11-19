struct nums {
  int x;
  int y;
};

struct nums xy;
struct nums* p;
int z;


/*@contract@*/
void switcher(){
  int temp = xy.x;
  xy.x = xy.y;
  xy.y = temp;
}


int main() {
    switcher();
    xy.x++;
    xy.y++;
    z = 1;
    return 0;
}

 void harness_main()
{
assume((1 != 0));
	int main_result = main();
assert(xy.x == $at("Old", (int)(xy.y)) + 1 && xy.y == $at("Old", (int)(xy.x)) + 1 && z > 0);
}
