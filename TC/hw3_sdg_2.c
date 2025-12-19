#include <stdio.h>
#include <limits.h>

/*@
  assigns \nothing;
*/
short sum_short(short sa, short sb) {
    return sa + sb;
}

/*@
  assigns \nothing;
*/
long sum_long(long la, long lb) {
    return la + lb;
}
/*@ 
  assigns \nothing;
  ensures \result == 0;
*/
int main() {
    // Instance of values
    short sa = 1000, sb = 2000;
    long la = 100000L, lb = 200000L;
    /*@ assert (int)sa + (int)sb <= SHRT_MAX; */
    /*@ assert (int)sa + (int)sb >= SHRT_MIN; */

    short short_res = sum_short(sa, sb);
    /*@ assert short_res == sa + sb; */

    long long_res = sum_long(la, lb);
    /*@ assert long_res == la + lb; */
    /*@ assert (long)la + (long)lb <= LONG_MAX; */
    /*@ assert (long)la + (long)lb >= LONG_MIN; */

    // Print results (causes warnings thus commented)
    //printf("The sum of short integers %hd and %hd is %hd\n", sa, sb, short_res);
    //printf("The sum of long integers %ld and %ld is %ld\n", la, lb, long_res);

    return 0;
}
