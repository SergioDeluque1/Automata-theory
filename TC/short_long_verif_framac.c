#include <stdio.h>
#include <limits.h>

/*@
  requires (int)sa + (int)sb <= SHRT_MAX;
  requires (int)sa + (int)sb >= SHRT_MIN;
  assigns \nothing;
  ensures \result == sa + sb;
  ensures (sa > 0 && sb > 0) ==> \result >= sa && \result >= sb;
  ensures (sa < 0 && sb < 0) ==> \result <= sa && \result <= sb;
*/
short sum_short(short sa, short sb) {
    return sa + sb;
}

/*@
  assigns \nothing;
  ensures \result == la + lb;
  ensures (la > 0 && lb > 0) ==> \result >= la && \result >= lb;
  ensures (la < 0 && lb < 0) ==> \result <= la && \result <= lb;
*/
long sum_long(long la, long lb) {
    return la + lb;
}

int main() {
    // Instance of values
    short sa = 1000, sb = 2000;
    long la = 100000L, lb = 200000L;

    short short_res = sum_short(sa, sb);
    /*@ assert short_res == sa + sb; */
    /*@assert (int)sa + (int)sb <= SHRT_MAX; */
    /*@ assert (int)sa + (int)sb >= SHRT_MIN; */

    long long_res = sum_long(la, lb);
    /*@ assert long_res == la + lb; */
    /*@ assert (long)la + (long)lb <= LONG_MAX; */
    /*@ assert (long)la + (long)lb >= LONG_MIN; */

    // Print results
    printf("The sum of short integers %hd and %hd is %hd\n", sa, sb, short_res);
    printf("The sum of long integers %ld and %ld is %ld\n", la, lb, long_res);

    return 0;
}
