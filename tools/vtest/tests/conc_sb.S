/* conc_sb -- STORE BUFFERING, the classic litmus test that separates a
 * sequentially consistent machine from a weak one.
 *
 *     hart 0:  X = 1 ; a = Y          hart 1:  Y = 1 ; b = X
 *
 * Under SEQUENTIAL CONSISTENCY (a,b) = (0,0) is impossible: whichever store
 * is second in the total order, the load that follows it sees the first one.
 * Under RVWMO -- and on any machine that lets a store sit in a buffer while
 * a later load to a different address completes -- (0,0) is allowed.
 *
 * OUR MODEL IS SC.  RiscvLang steps one hart at a time over one memory, so
 * no schedule of VConc can produce (0,0).  If QEMU ever does, that is an
 * UNSOUNDNESS -- a hardware behaviour with no model execution -- and by far
 * the most valuable thing this area could find.  So the test exists to look
 * for it, and its capture records how hard we looked.
 *
 * The two-pass warm-up is the same device as conc_lost.S and for the same
 * reason: a QEMU basic block costs thousands of guest instructions the first
 * time it is reached, so without a pass that leaves the whole hot path in
 * the TB cache the two harts do not overlap at all.  On top of that each
 * hart runs a short delay loop of its OWN length (D0 / D1 rounds) right
 * after the rendezvous: hart 0 leaves the rendezvous systematically ahead,
 * and trimming that bias is what raises the interesting outcome from 1.3%
 * of runs to 4.6%.
 *
 * MEASURED, 1200 runs at D0 = 2, D1 = 1:
 *     (0,1)  905     (1,0)  226     (1,1)   14     (0,0)   55
 * All four appear, so the capture is a set of four; (1,1) is the rarest at
 * 1.2%, which is why `repeat` is 700 and not 100.  (0,0) -- the one the
 * model cannot have -- is 4.6%.
 *
 * RESULT layout (mirrored in vtest-rocq/ConcSb.v):
 *   +0x000  DONE          +0x100  X               +0x104  Y
 *   +0x004  status = 1    +0x108  BAR0A  +0x10c  BAR1A   pass-1 rendezvous
 *   +0x008  a = hart 0's load of Y    +0x110  BAR0B  +0x114  BAR1B  pass 2
 *   +0x00c  b = hart 1's load of X    +0x118  P0X    +0x11c  P0Y
 *                                     +0x120  P1X    +0x124  P1Y
 *                                     +0x128  A0     +0x12c  A1  (warm-up)
 *                                     +0x130  DONE1
 */
/* vtest: smp=2 repeat=700 */
#include "abi.h"

#define R_A       8
#define R_B       12
#define X         0x100
#define Y         0x104
#define BAR0A     0x108
#define BAR1A     0x10c
#define BAR0B     0x110
#define BAR1B     0x114
#define P0X       0x118
#define P0Y       0x11c
#define P1X       0x120
#define P1Y       0x124
#define A0        0x128
#define A1        0x12c
#define DONE1     0x130
#define D0        2              /* skew trim: see the header */
#define D1        1

    .globl _vtest_body
_vtest_body:                     /* hart 0 */
    li   s1, 2
    li   s3, D0
    li   s2, P0X                 /* pass 1 stores here... */
    li   s6, P0Y                 /* ...loads here... */
    li   s7, A0                  /* ...and records there */
    li   s4, BAR0A
    li   s5, BAR1A
    li   s8, X                   /* pass 2: THE LITMUS TEST */
    li   s9, Y
    li   s10, R_A
    j    pass

    .globl _vtest_body_ap
_vtest_body_ap:                  /* hart 1 */
    li   s1, 2
    li   s3, D1
    li   s2, P1Y
    li   s6, P1X
    li   s7, A1
    li   s4, BAR1A
    li   s5, BAR0A
    li   s8, Y
    li   s9, X
    li   s10, R_B
    j    pass

/* ONE pass, run twice by BOTH harts: rendezvous, then store 1 to
 * RESULT+s2, load RESULT+s6, record it at RESULT+s7. */
pass:
    add  t1, s11, s2             /* my store target */
    add  t3, s11, s6             /* the word I load */
    add  t5, s11, s7             /* where I record it */
    add  t2, s11, s4
    li   t0, 1
    sw   t0, 0(t2)               /* I have arrived */
    add  t2, s11, s5
1:  lw   t0, 0(t2)
    beqz t0, 1b                  /* ...now wait for the other hart */
    mv   a0, s3
3:  addi a0, a0, -1
    bnez a0, 3b                  /* per-hart skew trim */
    li   t0, 1
    sw   t0, 0(t1)               /* MY STORE -- no fence after it */
    lw   t4, 0(t3)               /* MY LOAD of the OTHER word */
    sw   t4, 0(t5)               /* what I saw */
    addi s1, s1, -1
    beqz s1, out
    mv   s2, s8                  /* pass 2 is the shared pair */
    mv   s6, s9
    mv   s7, s10
    addi s4, s4, 8               /* ...at the pass-2 rendezvous flags */
    addi s5, s5, 8
    j    pass

out:
    csrr t0, mhartid
    bnez t0, out_ap
    li   t1, DONE1               /* hart 0 waits for hart 1 to record b */
    add  t1, s11, t1
2:  lw   t0, 0(t1)
    beqz t0, 2b
    li   t0, 1
    sw   t0, RES_STATUS(s11)
    ret
out_ap:
    fence
    li   t0, 1
    sw   t0, DONE1(s11)
    ret
