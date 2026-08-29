/* core_csrwide -- FINDING 22's SEVEN, the CSRs where the MODEL IS WIDER
 * than the hardware.  QEMU ONLY, and deliberately so.
 *
 * core_csrprobe is the half of this question that every machine can be
 * asked; this is the half that only QEMU can.  The split is not tidiness:
 *
 *   - on the VisionFive 2 all seven trap, which core_csrprobe would have
 *     told us nothing new about -- QEMU already refuses them, and the
 *     interesting column is the MODEL's;
 *   - in the model the first of them, `csrr mseccfg`, has NO TRANSITION AT
 *     ALL.  [exec] answers None and the harness reports VStuck, so the run
 *     stops there and every later probe in the same image goes unasked.
 *
 * That second point is why these seven cannot share a test with anything
 * else, and it is a finding in its own right.  Finding 22 records the model
 * as IMPLEMENTING these CSRs -- "implemented, read successfully" -- and for
 * the interpreter this suite runs, that is not what happens: it neither
 * answers nor refuses.  Compare finding 25, where `sc.w` does not evaluate
 * because [execute_STORECON] goes through opaque platform axioms; this is
 * the same class of limit, in the CSR file.
 *
 * WHAT THE OPEN DECISION NEEDS.  README.md asks "which machine is the model
 * claiming to be?" and leaves findings 19 and 22 unclassified until someone
 * answers it.  This test and core_csrprobe together make the question
 * concrete for the first time: with the board's column beside QEMU's, the
 * model is now known to be wider than BOTH machines on exactly these seven,
 * and narrower than the board on none of them.
 *
 * `.option norvc` is required: trap.S advances mepc by 4.
 *
 * RESULT layout (mirrored in vtest-rocq/CoreCsrwide.v):
 *   +8 + 4*i   CSR i below: 1 if reading it TRAPPED, else 0
 *   +8 + 4*7   THE CONTROL: an all-zeros (illegal) instruction word, which
 *              must be 1 -- otherwise a run that never reached the handler
 *              is indistinguishable from one where nothing trapped
 *   +0x800     the total number of traps taken
 *   +0x810..   the trap records: mcause, mepc, mtval, 0
 */
/* vtest: repeat=1 machines=qemu */
    .option norvc
#include "abi.h"

.macro PROBE csr, slot
    lw   s2, 0(s9)
    csrr t2, \csr
    lw   s3, 0(s9)
    xor  s4, s2, s3
    snez s4, s4
    sw   s4, (RES_PAYLOAD + 4 * \slot)(s11)
.endm

.macro PROBEINSN word, slot
    lw   s2, 0(s9)
    .word \word
    lw   s3, 0(s9)
    xor  s4, s2, s3
    snez s4, s4
    sw   s4, (RES_PAYLOAD + 4 * \slot)(s11)
.endm

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
    lla  t0, _vtest_trap
    csrw mtvec, t0
    li   s9, RESULT_BASE + RES_TRAPS

    li   t0, 1
    sw   t0, RES_STATUS(s11)

    PROBE 0x747, 0          /* mseccfg     -- Smepmp.  THE MODEL IS STUCK
                               HERE: [exec] has no transition at all, so
                               nothing below this line is reached in the
                               model.  On QEMU it is an ordinary trap. */
    PROBE 0x30C, 1          /* mstateen0   -- Smstateen  */
    PROBE 0x10C, 2          /* sstateen0   -- Smstateen  */
    PROBE 0xDA0, 3          /* scountovf   -- Sscofpmf   */
    PROBE 0x321, 4          /* mcyclecfg   -- Smcntrpmf  */
    PROBE 0x322, 5          /* minstretcfg -- Smcntrpmf  */
    PROBE 0x011, 6          /* ssp         -- Zicfiss    */

    PROBEINSN 0x00000000, 7 /* the control */

    li   t0, 2
    sw   t0, RES_STATUS(s11)
    mv   ra, s10
    ret

#include "trap.S"
