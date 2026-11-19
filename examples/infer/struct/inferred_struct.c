struct nums {
  int x;
  int y;
};

struct nums xy;
struct nums* p;
int z;

/*@
context Perm(xy,1);
requires true;
ensures xy.y == \old(xy.x) && \old(xy.y) == xy.x;
*/
void switcher(){
  int temp = xy.x;
  xy.x = xy.y;
  xy.y = temp;
}

/*@
context Perm(xy,1);
context Perm(z,1);
requires true;
ensures xy.x == \old(xy.y) + 1 && xy.y == \old(xy.x) + 1 && z > 0;
*/
int main() {
    switcher();
    xy.x++;
    xy.y++;
    z = 1;
    return 0;
}
