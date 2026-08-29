/* conc_mp -- MESSAGE PASSING: the litmus test that separates RVWMO from TSO.
 *
 * conc_sb (store buffering) separates TSO from SEQUENTIAL CONSISTENCY, and
 * it is what found finding 24: QEMU on an x86 host produces (0,0), which no
 * SC machine can, because the host is TSO and TSO permits a store to be
 * reordered past a later load.  That tells us the model is not SC-correct.
 * It tells us NOTHING about whether real RISC-V hardware is weaker still.
 *
 * RVWMO IS WEAKER THAN TSO.  TSO keeps store->store and load->load order and
 * relaxes only store->load; RVWMO relaxes all of them.  So the test that
 * separates them is the one whose forbidden-under-TSO outcome needs a
 * store->store or a load->load reordering:
 *
 *     writer:  X = 1 ; Y = 1              (no fence between)
 *     reader:  r1 = Y ; r2 = X            (no fence between)
 *
 *     (r1,r2) = (1,0)  --  "I saw the flag but not the data"
 *
 * Under TSO that is IMPOSSIBLE: the writer's two stores reach memory in
 * order, so Y=1 implies X=1 is already visible, and the reader's two loads
 * are performed in order, so having seen Y=1 it cannot then see a stale X.
 * Under RVWMO it is ALLOWED, by either reordering.  It is also the exact
 * shape of a real bug: it is why a lock release needs a release fence and
 * why xv6's acquire/release carry __sync_synchronize().
 *
 * SO THE THREE MACHINES SHOULD DISAGREE THREE WAYS, and that is the point:
 *   - the MODEL is sequentially consistent, so (1,0) is impossible;
 *   - QEMU on an x86 host is TSO, so (1,0) should be impossible THERE TOO
 *     -- which makes QEMU useless for finding this class of bug, and is why
 *     a board is worth the trouble;
 *   - the hardware is RVWMO and MAY produce it.
 * A (1,0) on the board with none on QEMU is a hardware behaviour that
 * neither the model NOR our previous reference machine can produce.
 *
 * IF IT DOES NOT APPEAR, THAT IS NOT A RESULT.  An in-order core like the
 * U74 may well never reorder these in this window -- its loads issue in
 * order and its store buffer may drain in order -- and a null result here
 * says only "not observed by this test at this timing", never "the machine
 * is TSO".  Report it as a count out of a run total, not as a property.
 *
 * NO PER-ITERATION BARRIER, deliberately.  A barrier between the writer's
 * pair and the reader's pair would impose the very ordering under test.
 * Instead both harts sweep an ARRAY of independent slots at their own pace
 * after one rendezvous, so the reader lands in the writer's window at
 * whatever offsets the timing gives, and the interesting outcome is counted
 * over the whole sweep.  Most slots come out (0,0) (reader ahead) or (1,1)
 * (reader behind); those are not failures, they are the sweep missing.
 *
 * SLOTS ARE 64 BYTES APART, one cache line each, and X and Y are 2 KB
 * apart.  If X[i] and Y[i] shared a line, seeing Y=1 would mean the line
 * carrying X=1 had already arrived and (1,0) could never appear for a
 * reason that has nothing to do with the memory model.
 *
 * THE SECOND PASS IS THE CONTROL, and it is what makes a (1,0) in the first
 * pass believable: the same sweep with `fence w,w` between the stores and
 * `fence r,r` between the loads.  That outcome is forbidden on EVERY
 * machine, model included.  A (1,0) there means the harness is broken --
 * the slots alias, or the tally is wrong -- and not that the hardware is
 * exotic.
 *
 * RESULT layout (mirrored in vtest-rocq/ConcMp.v):
 *   +8    N, the number of slots swept
 *   ---- pass 1: NO FENCES ----
 *   +12   count of (r1,r2) = (0,0)   reader ran ahead of the writer
 *   +16   count of (1,1)             reader ran behind
 *   +20   count of (0,1)             saw old flag, new data -- legal anywhere
 *   +24   count of (1,0)   <-- THE RVWMO-ONLY OUTCOME
 *   ---- pass 2: FENCED (the control) ----
 *   +28   count of (0,0)
 *   +32   count of (1,1)
 *   +36   count of (0,1)
 *   +40   count of (1,0)   <-- MUST BE 0 ON EVERY MACHINE
 *   ---- rendezvous flags ----
 *   +0x100 BARW1  +0x104 BARR1   +0x108 BARW2  +0x10c BARR2
 */
/* vtest: smp=2 repeat=1 */
    .option norvc
#include "abi.h"

#define N         16              /* slots per sweep; 64 B apart */
#define ROUNDS    16              /* sweeps per pass -- see the stagger note */
#define DSTEP     6               /* reader delay added per round            */
#define XBASE     DMA_BASE        /* X[i] at XBASE + 64*i        */
#define YBASE     (DMA_BASE + 0x800)   /* Y[i], 2 KB away        */

#define R_N       8
#define R_P1      12              /* four counts: 00 11 01 10 */
#define R_P2      28
#define BARW1     0x100
#define BARR1     0x104
#define BARW2     0x108
#define BARR2     0x10c
#define BARD1     0x110           /* reader has FINISHED round r  */
#define BARD2     0x114

/* rendezvous: set my flag, spin on the other's */
/* A SENSE-REVERSING rendezvous: each round bumps the flag to the round
   number + 1 rather than to 1, so a flag left set by the previous round
   does not let a hart through early.  s9 holds the round. */
.macro SYNC mine, theirs
    addi t0, s9, 1
    li   t1, \mine
    add  t1, s11, t1
    sw   t0, 0(t1)
    li   t1, \theirs
    add  t1, s11, t1
    addi t2, s9, 1
9:  lw   t0, 0(t1)
    blt  t0, t2, 9b
.endm

/* ---- the WRITER's sweep.  \fenced != 0 puts a w,w fence between the two
 * stores, which is the control pass. ---- */
.macro WSWEEP fenced
    li   s2, 0                    /* i */
    li   s3, XBASE
    li   s4, YBASE
1:  li   t0, 1
    sw   t0, 0(s3)                /* X[i] = 1  -- the DATA  */
.if \fenced
    fence w, w
.endif
    sw   t0, 0(s4)                /* Y[i] = 1  -- the FLAG  */
    addi s3, s3, 64
    addi s4, s4, 64
    addi s2, s2, 1
    li   t1, N
    blt  s2, t1, 1b
.endm

/* ---- the READER's sweep, tallying the four outcomes into s5..s8 ---- */
.macro RSWEEP fenced
    li   s2, 0
    li   s3, XBASE
    li   s4, YBASE
    /* s5..s8 are NOT reset here: they ACCUMULATE across the rounds of a
       pass, and the round loop zeroes them once before entering. */
2:  lw   t0, 0(s4)                /* r1 = Y[i]  -- the FLAG first */
.if \fenced
    fence r, r
.endif
    lw   t1, 0(s3)                /* r2 = X[i]  -- then the DATA  */
    bnez t0, 3f
    /* r1 == 0 */
    bnez t1, 4f
    addi s5, s5, 1                /* (0,0) */
    j    5f
4:  addi s7, s7, 1                /* (0,1) */
    j    5f
3:  /* r1 == 1 */
    bnez t1, 6f
    addi s8, s8, 1                /* (1,0)  THE RVWMO-ONLY OUTCOME */
    j    5f
6:  addi s6, s6, 1                /* (1,1) */
5:  addi s3, s3, 64
    addi s4, s4, 64
    addi s2, s2, 1
    li   t1, N
    blt  s2, t1, 2b
.endm

/* THE EXIT BARRIER, and the control is what proved it necessary.
 *
 * The entry rendezvous synchronises the START of a round and nothing else.
 * The writer's sweep is shorter than the reader's, so it finished first,
 * looped, and ZEROED THE ARRAYS FOR THE NEXT ROUND while the reader was
 * still sweeping this one -- whereupon the reader saw Y[i] = 1 (written this
 * round) and X[i] = 0 (already zeroed for the next), which is a (1,0) that
 * has nothing to do with the memory model.
 *
 * MEASURED, and this is exactly what the fenced control exists to catch: on
 * QEMU, pass 2 -- with `fence w,w` and `fence r,r`, where (1,0) is forbidden
 * on every machine there is -- reported (1,0) = 12 out of 256.  Without the
 * control that would have been read as the board being exotic; with it, it
 * could only be the harness.
 *
 * So the reader publishes "round done" and the writer waits for it before
 * zeroing.  This is BETWEEN rounds, never between the accesses under test,
 * so it imposes no ordering on the thing being measured. */
.macro RDONE flag
    addi t0, s9, 1
    li   t1, \flag
    add  t1, s11, t1
    sw   t0, 0(t1)
.endm

.macro WWAITD flag
    li   t1, \flag
    add  t1, s11, t1
    addi t2, s9, 1
14: lw   t0, 0(t1)
    blt  t0, t2, 14b
.endm

/* store the reader's four tallies at \off */
.macro RSTORE off
    sw   s5, (\off + 0)(s11)
    sw   s6, (\off + 4)(s11)
    sw   s7, (\off + 8)(s11)
    sw   s8, (\off + 12)(s11)
.endm

/* THE STAGGER, and it is what makes this test sensitive rather than lucky.
 *
 * Measured first attempt, N = 32, one round, no stagger: the reader came out
 * 32 x (0,0) in pass 1 and 32 x (1,1) in pass 2 -- it swept entirely AHEAD of
 * the writer, then entirely behind.  Its loop is a few instructions longer
 * per slot than the writer's, so with both released from the same rendezvous
 * the relative phase is not jitter, it is a CONSTANT, and no number of runs
 * would have found the window.
 *
 * So the WRITER delays (round * DSTEP) loop iterations after each
 * rendezvous.  It is the writer and not the reader because the writer's
 * loop is the SHORTER one: with both released together it finishes first
 * and the reader sees a completed sweep every time (measured: 256 x (1,1)).
 * Delaying the writer walks its sweep forward across the reader's, which
 * covers the window deterministically instead of hoping the machine's
 * timing wanders into it.  The tallies accumulate
 * across rounds, so the totals are out of N * ROUNDS.
 *
 * The writer re-zeroes both arrays BEFORE each rendezvous, so a round never
 * sees the previous round's flags. */
.macro DELAY r
    mv   t2, \r
    li   t1, DSTEP
    mul  t2, t2, t1
    beqz t2, 8f
7:  addi t2, t2, -1
    bnez t2, 7b
8:
.endm

.macro ZERO
    li   t2, 0
    li   t0, XBASE
    li   t1, YBASE
1:  sw   zero, 0(t0)
    sw   zero, 0(t1)
    addi t0, t0, 64
    addi t1, t1, 64
    addi t2, t2, 1
    li   a1, N
    blt  t2, a1, 1b
.endm

    .globl _vtest_body
_vtest_body:                     /* the PRIMARY is the READER, because it is
                                    the one that has to publish the result */
    mv   s10, ra
    li   t0, N * ROUNDS
    sw   t0, R_N(s11)

    /* pass 1: no fences */
    li   s5, 0
    li   s6, 0
    li   s7, 0
    li   s8, 0
    li   s9, 0                    /* round */
10: SYNC BARR1, BARW1
    RSWEEP 0
    RDONE BARD1
    addi s9, s9, 1
    li   t1, ROUNDS
    blt  s9, t1, 10b
    RSTORE R_P1

    /* pass 2: the fenced control */
    li   s5, 0
    li   s6, 0
    li   s7, 0
    li   s8, 0
    li   s9, 0
11: SYNC BARR2, BARW2
    RSWEEP 1
    RDONE BARD2
    addi s9, s9, 1
    li   t1, ROUNDS
    blt  s9, t1, 11b
    RSTORE R_P2

    li   t0, 1
    sw   t0, RES_STATUS(s11)
    mv   ra, s10
    ret

    .globl _vtest_body_ap
_vtest_body_ap:                  /* the AP is the WRITER */
    li   s9, 0
12: ZERO
    SYNC BARW1, BARR1
    DELAY s9
    WSWEEP 0
    WWAITD BARD1
    addi s9, s9, 1
    li   t1, ROUNDS
    blt  s9, t1, 12b

    li   s9, 0
13: ZERO
    SYNC BARW2, BARR2
    DELAY s9
    WSWEEP 1
    WWAITD BARD2
    addi s9, s9, 1
    li   t1, ROUNDS
    blt  s9, t1, 13b
    ret
