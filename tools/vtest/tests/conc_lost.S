/* conc_lost -- A LOST UPDATE: two harts, one word, no atomics.
 *
 * Each hart runs NITER rounds of `lw; nop x4; addi 1; sw` on the SAME word.
 * Every pair of rounds that reads the same value loses one increment, so the
 * final counter's exact value IS the interleaving.  With NITER = 2 there are
 * exactly three possible answers -- 4 (neither round collided), 3 (one did),
 * 2 (both did; 2 is the floor, since a hart's second round cannot read less
 * than what its own first round wrote) -- and QEMU produces all three, none
 * of them rarely: over 300 runs, 4 came out 208 times, 2 came out 59 times
 * and 3 came out 33 times.
 *
 * The four nops between the load and the add are not decoration: they hold
 * the read value across four instructions, which is what makes the window
 * wide enough to be hit with only two rounds.  Without them the collision
 * rate drops by an order of magnitude (2 in 200 for the middle outcome).
 *
 * GETTING THE HARTS TO ACTUALLY OVERLAP was the whole difficulty, and the
 * two-pass structure below is the answer.  A plain rendezvous is not enough:
 * QEMU translates a basic block the first time it is reached, and
 * tb_gen_code costs thousands of guest instructions' worth of wall time, so
 * whichever hart is still inside the translator when the other leaves the
 * rendezvous loses the race before it starts -- measured, a 16-round loop
 * came out at 32 in 60 runs out of 60.  So both harts run the WHOLE hot path
 * TWICE: pass 1 is a warm-up on a PRIVATE word, whose only purpose is to
 * leave every block of the path in QEMU's (shared) TB cache, and pass 2 is
 * the race.  With that, TWO rounds each is enough to lose an update.
 *
 * The model does not care about any of this -- pass 1 is just 2 more rounds
 * on a word nobody else touches -- but it is why the program has the shape
 * it has, and removing it would silently turn the test deterministic.
 *
 * RESULT layout (mirrored in vtest-rocq/ConcLost.v):
 *   +0x000  DONE          +0x100  CTR    -- THE RACY WORD (= the total)
 *   +0x004  status = 1    +0x104  BAR0A  +0x108  BAR1A   pass-1 rendezvous
 *   +0x008  the total     +0x10c  BAR0B  +0x110  BAR1B   pass-2 rendezvous
 *                         +0x114  PRIV0  +0x118  PRIV1   warm-up words
 *                         +0x11c  DONE1  -- hart 1's loop is over
 */
/* vtest: smp=2 repeat=100 */
#include "abi.h"

#define R_TOTAL   8
#define CTR       0x100
#define BAR0A     0x104
#define BAR1A     0x108
#define BAR0B     0x10c
#define BAR1B     0x110
#define PRIV0     0x114
#define PRIV1     0x118
#define DONE1     0x11c

#define NITER     2              /* rounds each, in the racing pass */
#define W         2              /* rounds each, in the warm-up pass */

    .globl _vtest_body
_vtest_body:                     /* hart 0 */
    li   s1, 2                   /* passes to run */
    li   s2, PRIV0               /* pass 1: my own word */
    li   s3, W
    li   s4, BAR0A               /* my rendezvous flag */
    li   s5, BAR1A               /* ...and the other hart's */
    j    pass

    .globl _vtest_body_ap
_vtest_body_ap:                  /* hart 1 */
    li   s1, 2
    li   s2, PRIV1
    li   s3, W
    li   s4, BAR1A
    li   s5, BAR0A
    j    pass

/* ONE pass, run twice by BOTH harts: rendezvous, then s3 rounds of
 * `lw; addi 1; sw` at RESULT+s2. */
pass:
    add  t2, s11, s4
    li   t0, 1
    sw   t0, 0(t2)               /* I have arrived */
    add  t2, s11, s5
1:  lw   t0, 0(t2)
    beqz t0, 1b                  /* ...now wait for the other hart */
    add  t1, s11, s2
    mv   a0, s3
2:  lw   t0, 0(t1)               /* THE RACE: read... */
    nop                          /* ...hold the value for four instructions, */
    nop                          /* which is what makes the window wide */
    nop                          /* enough for the other hart to land in it */
    nop
    addi t0, t0, 1
    sw   t0, 0(t1)               /* ...and write back */
    addi a0, a0, -1
    bnez a0, 2b
    addi s1, s1, -1
    beqz s1, out
    li   s2, CTR                 /* pass 2 races on the SHARED word */
    li   s3, NITER
    addi s4, s4, 8               /* ...at the pass-2 rendezvous flags */
    addi s5, s5, 8
    j    pass

out:
    csrr t0, mhartid
    bnez t0, out_ap
    li   t1, DONE1               /* hart 0 waits for hart 1's loop to end */
    add  t1, s11, t1
3:  lw   t0, 0(t1)
    beqz t0, 3b
    li   t1, CTR
    add  t1, s11, t1
    lw   t0, 0(t1)
    sw   t0, R_TOTAL(s11)        /* THE OBSERVATION */
    li   t0, 1
    sw   t0, RES_STATUS(s11)
    ret
out_ap:
    fence
    li   t0, 1
    sw   t0, DONE1(s11)
    ret
