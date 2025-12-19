/*@ 
  requires \valid(a) && \valid(b) && \valid(c);
  requires *a <= *b && *b <= *c;
  assigns *a, *b, *c;
*/
void order_3(int *a, int *b, int *c)
{
  int temp;
  /*@ assert rte: mem_access: \valid_read(a); */
  /*@ assert rte: mem_access: \valid_read(b); */
  if (*a > *b) {
    /*@ assert rte: mem_access: \valid_read(a); */
    temp = *a;
    /*@ assert rte: mem_access: \valid(a); */
    /*@ assert rte: mem_access: \valid_read(b); */
    *a = *b;
    /*@ assert rte: mem_access: \valid(b); */
    *b = temp;
    /*@ assert *a ≤ *b; */ ;
  }
  /*@ assert rte: mem_access: \valid_read(a); */
  /*@ assert rte: mem_access: \valid_read(c); */
  if (*a > *c) {
    /*@ assert rte: mem_access: \valid_read(a); */
    temp = *a;
    /*@ assert rte: mem_access: \valid(a); */
    /*@ assert rte: mem_access: \valid_read(c); */
    *a = *c;
    /*@ assert rte: mem_access: \valid(c); */
    *c = temp;
    /*@ assert *a ≤ *c; */ ;
  }
  /*@ assert rte: mem_access: \valid_read(b); */
  /*@ assert rte: mem_access: \valid_read(c); */
  if (*b > *c) {
    /*@ assert rte: mem_access: \valid_read(b); */
    temp = *b;
    /*@ assert rte: mem_access: \valid(b); */
    /*@ assert rte: mem_access: \valid_read(c); */
    *b = *c;
    /*@ assert rte: mem_access: \valid(c); */
    *c = temp;
    /*@ assert *b ≤ *c; */ ;
  }
  return;
}

/*@ terminates \true;
    exits \false; */
int main(void)
{
  int __retres;
  int a1 = 5;
  int b1 = 3;
  int c1 = 4;
  order_3(& a1,& b1,& c1);
  /*@ assert a1 ≡ 3 ∧ b1 ≡ 4 ∧ c1 ≡ 5; */ ;
  int a2 = 2;
  int b2 = 2;
  int c2 = 2;
  order_3(& a2,& b2,& c2);
  /*@ assert a2 ≡ 2 ∧ b2 ≡ 2 ∧ c2 ≡ 2; */ ;
  int a3 = 4;
  int b3 = 3;
  int c3 = 4;
  order_3(& a3,& b3,& c3);
  /*@ assert a3 ≡ 3 ∧ b3 ≡ 4 ∧ c3 ≡ 4; */ ;
  int a4 = 4;
  int b4 = 5;
  int c4 = 4;
  order_3(& a4,& b4,& c4);
  /*@ assert a4 ≡ 4 ∧ b4 ≡ 4 ∧ c4 ≡ 5; */ ;
  __retres = 0;
  return __retres;
}

