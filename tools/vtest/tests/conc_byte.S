/* conc_byte -- two harts racing on ADJACENT BYTES of ONE word.
 *
 * Hart 0 runs NITER rounds of `lbu; addi 1; sb` on byte 0 of RESULT+0x100;
 * hart 1 does the same on byte 1.  The two are disjoint, so on any machine
 * whose memory is byte-granular BOTH counts survive and the word is
 * 0x0303 -- but on a machine that implemented a sub-word store as a
 * read-modify-write of the containing word, the harts would false-share and
 * one side's increments would be lost.  So this is the question: does the
 * model's store granularity match the hardware's under CONCURRENT access?
 *
 * It is the same two-pass warm-up as conc_lost.S -- pass 1 on a private
 * pair of adjacent bytes, pass 2 on the shared word -- and the same four
 * nops holding the loaded byte, so the harts really are inside each other's
 * read-modify-write windows.  conc_lost, which differs only in racing on
 * the SAME byte, loses updates 1 run in 3; this one, if the answer is the
 * expected one, never does.
 *
 * RESULT layout (mirrored in vtest-rocq/ConcByte.v):
 *   +0x000  DONE          +0x100  W  -- byte 0 hart 0's count,
 *   +0x004  status = 1                  byte 1 hart 1's count
 *   +0x008  W read back by hart 0
 *                         +0x104  BAR0A  +0x108  BAR1A   pass-1 rendezvous
 *                         +0x10c  BAR0B  +0x110  BAR1B   pass-2 rendezvous
 *                         +0x114  PRIV0  +0x115  PRIV1   warm-up bytes
 *                         +0x118  DONE1  -- hart 1's loop is over
 */
/* vtest: smp=2 repeat=100 */
#include "abi.h"

#define R_WORD    8
#define W0        0x100
#define W1        0x101
#define BAR0A     0x104
#define BAR1A     0x108
#define BAR0B     0x10c
#define BAR1B     0x110
#define PRIV0     0x114
#define PRIV1     0x115
#define DONE1     0x118

#define NITER     3
#define WARM      2

    .globl _vtest_body
_vtest_body:                     /* hart 0 */
    li   s1, 2
    li   s2, PRIV0               /* pass 1: my own byte */
    li   s3, WARM
    li   s4, BAR0A
    li   s5, BAR1A
    li   s8, W0                  /* pass 2: byte 0 of the shared word */
    j    pass

    .globl _vtest_body_ap
_vtest_body_ap:                  /* hart 1 */
    li   s1, 2
    li   s2, PRIV1
    li   s3, WARM
    li   s4, BAR1A
    li   s5, BAR0A
    li   s8, W1                  /* pass 2: byte 1 of the SAME word */
    j    pass

/* ONE pass, run twice by BOTH harts: rendezvous, then s3 rounds of
 * `lbu; addi 1; sb` at RESULT+s2. */
pass:
    add  t2, s11, s4
    li   t0, 1
    sw   t0, 0(t2)               /* I have arrived */
    add  t2, s11, s5
1:  lw   t0, 0(t2)
    beqz t0, 1b                  /* ...now wait for the other hart */
    add  t1, s11, s2
    mv   a0, s3
2:  lbu  t0, 0(t1)               /* THE RACE: read one byte... */
    nop
    nop
    nop
    nop
    addi t0, t0, 1
    sb   t0, 0(t1)               /* ...and write it back */
    addi a0, a0, -1
    bnez a0, 2b
    addi s1, s1, -1
    beqz s1, out
    mv   s2, s8                  /* pass 2 shares a word with the other hart */
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
    li   t1, W0
    add  t1, s11, t1
    lw   t0, 0(t1)
    sw   t0, R_WORD(s11)         /* THE OBSERVATION: the whole word */
    li   t0, 1
    sw   t0, RES_STATUS(s11)
    ret
out_ap:
    fence
    li   t0, 1
    sw   t0, DONE1(s11)
    ret
