/* clint_raw -- THE RAW CLOCK WORDS, AND THEY ARE EXPECTED TO DISAGREE.
 *
 * This test exists to be RED.  clint_time asks the questions two machines
 * can both answer -- did mtime advance, did it go backwards, do the 4-byte
 * halves bracket an 8-byte read, did the counters move -- and records them
 * as FLAGS.  Those flags agree with the model, so clint_time has a proof.
 * The underlying VALUES cannot agree: mtime is a free-running counter whose
 * value at any instruction depends on how fast the machine is, and the
 * minstret and mcycle deltas depend on how many instructions the wait loop
 * executed, which the model and QEMU do not share.
 *
 * Publishing them in clint_time made that whole test unprovable to record a
 * divergence nobody disputes.  They are published HERE instead, at the
 * offsets clint_time used to use, so a reader comparing the two captures
 * reads the same layout.  A proof of this run is not expected and its
 * absence is not a regression; what would be a finding is this test
 * suddenly agreeing, which would mean the model had grown a real clock.
 *
 * RESULT layout:
 *   +8    mtime, 8-byte read, low word
 *   +12   mtime, 8-byte read, high word
 *   +16   mtime after the wait loop, low word
 *   +20   mtime after the wait loop, high word
 *   +32   4-byte read of MTIME    (lo half)
 *   +36   4-byte read of MTIME_HI (hi half)
 *   +44   minstret delta over the wait loop
 *   +52   mcycle delta over the wait loop, low word
 */
/* vtest: repeat=1 tick=1 budget=8000 */
#include "abi.h"

#define R_T0LO    8
#define R_T0HI    12
#define R_T1LO    16
#define R_T1HI    20
#define R_W4LO    32
#define R_W4HI    36
#define R_INSTR   44
#define R_CYCLE   52

/* the same dead-clock backstop as clint_time: the loop waits for mtime to
   CHANGE, and the cap is reached only when the clock is not running. */
#define WAITCAP   4000

    .globl _vtest_body
_vtest_body:
    li   s0, CLINT_MTIME

    li   t0, 1
    sw   t0, RES_STATUS(s11)

    ld   s1, 0(s0)                   /* s1 = mtime before */
    csrr s2, minstret
    csrr s3, mcycle

    sw   s1, R_T0LO(s11)
    srli t0, s1, 32
    sw   t0, R_T0HI(s11)

    li   t2, WAITCAP
1:  ld   t1, 0(s0)
    bne  t1, s1, 2f
    addi t2, t2, -1
    bnez t2, 1b
2:

    ld   s4, 0(s0)                   /* s4 = mtime after */
    csrr s5, minstret
    csrr s6, mcycle

    sw   s4, R_T1LO(s11)
    srli t0, s4, 32
    sw   t0, R_T1HI(s11)

    /* the 4-byte halves, which the model decodes from two addresses */
    lwu  t1, 0(s0)
    lwu  t2, 4(s0)
    sw   t1, R_W4LO(s11)
    sw   t2, R_W4HI(s11)

    sub  t0, s5, s2
    sw   t0, R_INSTR(s11)
    sub  t0, s6, s3
    sw   t0, R_CYCLE(s11)

    li   t0, 2
    sw   t0, RES_STATUS(s11)
    ret
