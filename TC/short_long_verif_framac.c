/*
 * safe_sum.c — overflow-contracted integer addition, specified in ACSL.
 *
 * Verify with Frama-C (WP + runtime-error goals):
 *     frama-c -wp -wp-rte safe_sum.c
 *
 * The contracts rely on ACSL's mathematical-integer (Z) semantics: inside an
 * annotation, `a + b` is the exact sum and never overflows, so writing
 * `a + b <= TYPE_MAX` cleanly and correctly expresses "the C addition does not
 * overflow." No cast to a wider type is needed to make the spec sound.
 */

#include <limits.h>

/*@
  requires no_overflow:  sa + sb <= SHRT_MAX;
  requires no_underflow: sa + sb >= SHRT_MIN;
  assigns \nothing;
  ensures  value:  \result == sa + sb;
  ensures  pos_lb: (sa > 0 && sb > 0) ==> (\result >= sa && \result >= sb);
  ensures  neg_ub: (sa < 0 && sb < 0) ==> (\result <= sa && \result <= sb);
*/
short sum_short(short sa, short sb)
{
    /* sa and sb promote to int; their sum fits in int and then narrows back
       to short. The precondition guarantees it is in short range, so the
       narrowing conversion is exact (no implementation-defined result). */
    return (short)(sa + sb);
}

/*@
  requires no_overflow:  la + lb <= LONG_MAX;
  requires no_underflow: la + lb >= LONG_MIN;
  assigns \nothing;
  ensures  value:  \result == la + lb;
  ensures  pos_lb: (la > 0 && lb > 0) ==> (\result >= la && \result >= lb);
  ensures  neg_ub: (la < 0 && lb < 0) ==> (\result <= la && \result <= lb);
*/
long sum_long(long la, long lb)
{
    return la + lb;
}

/*@
  assigns \nothing;
  ensures \result == 0;
*/
int main(void)
{
    short sa = 1000, sb = 2000;
    long  la = 100000L, lb = 200000L;

    /*@ assert short_in_range: sa + sb <= SHRT_MAX && sa + sb >= SHRT_MIN; */
    short short_res = sum_short(sa, sb);
    /*@ assert short_ok: short_res == sa + sb; */

    /*@ assert long_in_range: la + lb <= LONG_MAX && la + lb >= LONG_MIN; */
    long long_res = sum_long(la, lb);
    /*@ assert long_ok: long_res == la + lb; */

    (void)short_res;   /* used only in annotations above */
    (void)long_res;
    return 0;
}
