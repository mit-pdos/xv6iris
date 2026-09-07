/* core_dtb -- a1 AT ENTRY, AND IT IS EXPECTED TO DISAGREE.
 *
 * This test exists to be RED.  It is finding 18: the boot chain hands the
 * program a device-tree pointer in a1, and the model writes a hardcoded
 * 0x1000 where QEMU passes the real one -- which moves with -m and with the
 * image, so it is not a value the two can be made to share by pinning a
 * constant.
 *
 * It used to live in core_hart, whose subject is the OTHER half of the boot
 * contract: mhartid, a0, and that the two agree.  Measured, a1 was the only
 * word of core_hart's result region the model and QEMU disagreed on, so one
 * already-recorded divergence was costing six agreeing claims their proof.
 * Splitting it out is what lets core_hart be proved and still leaves a1
 * captured on both machines.
 *
 * a1 IS STILL AN ENTRY VALUE, so it is sampled before any temporary is
 * touched -- the prologue writes t0, t1, t2, sp and s11 and nothing else,
 * and the `jal` does not touch the argument registers.
 *
 * RESULT layout (core_hart's old offsets, so the two captures read the same):
 *   +32   a1 at entry, low word
 *   +36   a1 at entry, high word
 */
/* vtest: repeat=1 tick=0 budget=2000 */
#include "abi.h"

#define R_A1LO     32
#define R_A1HI     36

    .globl _vtest_body
_vtest_body:
    mv   s2, a1

    li   t0, 1
    sw   t0, RES_STATUS(s11)

    sw   s2, R_A1LO(s11)
    srli t0, s2, 32
    sw   t0, R_A1HI(s11)

    li   t0, 2
    sw   t0, RES_STATUS(s11)
    ret
