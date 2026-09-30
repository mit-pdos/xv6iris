/* core_hart -- WHICH HART AM I, and does the model agree?
 *
 * Every other test in this suite runs on hart 0, and until this one nothing
 * had ever checked that the hart id reaches the program at all.  It is the
 * baseline test for the hart-variant mechanism (README.md, "Running a test
 * on a hart that is not 0"): built once with PRIMARY_HART=0 and once with
 * PRIMARY_HART=1, captured twice, and checked against the model started on
 * the matching hart with [VTest.start_hart].
 *
 * WHAT IT PINS.  [ColdBoot.cold_regs] is parametric in the hart id, and the
 * boot chain does exactly two things with it -- it stores it (so `csrr
 * mhartid` reads it) and it copies it into a0.  Those two claims are what
 * make `csrr mhartid` the right way for a program to tell harts apart, and
 * they are what this test checks against a real machine on TWO DIFFERENT
 * HARTS.  On hart 0 both are 0 and the test is nearly vacuous; the hart-1
 * capture is what gives it teeth, because a model that ignored its hart-id
 * argument would pass on hart 0 and fail here.
 *
 * EVERYTHING IS SAMPLED FIRST, then stored.  a0, a1 and t0 still hold entry
 * values when _vtest_body is reached (the prologue writes t0, t1, t2, sp and
 * s11 and nothing else, and the `jal` does not touch the argument
 * registers), so they have to be moved out of the way before the body uses a
 * temporary for anything.
 *
 * a1 IS NOT RECORDED HERE, and that is deliberate.  It is the one entry
 * register that diverges -- finding 18: the model writes a hardcoded 0x1000
 * where QEMU passes the real device-tree pointer, which moves with -m and
 * with the image -- and measured, +32 is the ONLY word of this test's
 * result region the model and QEMU disagree on.  Publishing it here makes
 * the boot contract's six agreeing claims unprovable in order to record one
 * divergence that is already written down.  core_dtb publishes a1 instead,
 * and is expected to be RED for as long as finding 18 stands.
 *
 * RESULT layout (the gap is deliberate; the region is zero-filled, so an
 * unwritten word reads 0 on both machines):
 *   +8    mhartid, read with csrr           hart 0: 0    hart 1: 1
 *   +12   a0 at entry (the boot contract)   hart 0: 0    hart 1: 1
 *   +16   1 if a0 == mhartid                both: 1
 *   +20   the prologue's SLOT (t0 at entry) both: 0 -- the primary is slot 0
 *   +24   sp at entry                       both: STACK_BASE + STACK_SIZE
 *   +28   s11 at entry                      both: RESULT_BASE
 *   +40   mstatus, low word
 *   +44   mstatus, high word
 */
/* vtest: repeat=1 tick=0 budget=2000 */
#include "abi.h"

#define R_HARTID   8
#define R_A0       12
#define R_AGREE    16
#define R_SLOT     20
#define R_SP       24
#define R_S11      28
#define R_MSTLO    40
#define R_MSTHI    44

    .globl _vtest_body
_vtest_body:
    /* sample everything that is still an ENTRY value, before touching a
       temporary.  t0 is the prologue's slot; a0 is the boot contract's. */
    mv   s1, a0
    mv   s3, t0
    mv   s4, sp
    mv   s5, s11
    csrr s6, mhartid
    csrr s7, mstatus

    li   t0, 1
    sw   t0, RES_STATUS(s11)

    sw   s6, R_HARTID(s11)
    sw   s1, R_A0(s11)

    /* the claim that makes `csrr mhartid` usable: the boot chain put the
       SAME id in a0 that the CSR reports */
    xor  t0, s1, s6
    seqz t0, t0
    sw   t0, R_AGREE(s11)

    sw   s3, R_SLOT(s11)
    sw   s4, R_SP(s11)
    sw   s5, R_S11(s11)

    sw   s7, R_MSTLO(s11)
    srli t0, s7, 32
    sw   t0, R_MSTHI(s11)

    li   t0, 2
    sw   t0, RES_STATUS(s11)
    ret
