/* core_csrprobe -- WHICH CSRs DOES THIS MACHINE ACTUALLY IMPLEMENT?
 *
 * The first test in the suite that treats a trap as DATA.  It reads forty
 * CSRs one at a time under the M-mode handler in trap.S, and records for
 * each whether the read TRAPPED.  One word per CSR, 1 = illegal
 * instruction, 0 = the machine answered.
 *
 * WHY A SCOREBOARD AND NOT A DUMP.  core_regs_mcsr and core_regs_scsr read
 * these registers for their VALUES, which means the first one the machine
 * refuses ends the run and the remaining thirty-odd questions go unasked.
 * On the VisionFive 2 that is exactly what happens: `csrr t0, menvcfg`
 * takes an illegal-instruction trap (mcause 2, mtval 0x30a022f3) at the
 * seventh register, and everything after it is unmeasured.  With trap.S the
 * program steps over each refusal and keeps going, so one run answers the
 * whole question on any machine.
 *
 * FINDING 22's SEVEN CSRs ARE NOT HERE.  They are core_csrwide's, because
 * the model does not merely refuse the first of them -- it has NO
 * TRANSITION for `csrr mseccfg` at all and [exec] answers None, which stops
 * the run and would cost the other thirty-six answers.  That is a finding of
 * its own and it gets its own test.
 *
 * WHAT IT IS FOR.  README.md's OPEN DECISION -- "which machine is the model
 * claiming to be?" (findings 19 and 22) -- is a question about exactly this
 * set.  Finding 22 is the only row in the table where the MODEL IS WIDER
 * than the hardware, and it was found by a value dump that could only report
 * one refusal at a time.  This test turns that into a table: the model's
 * column, QEMU's column and the board's column, side by side, for every CSR
 * anyone has wondered about.
 *
 * A NOTE ON METHOD, learned the hard way.  Reading a CSR over JTAG is NOT
 * the same question.  All twenty of core_regs_mcsr's CSRs read fine through
 * OpenOCD on the U74 -- menvcfg included, answering 0 -- while the hart
 * refuses to EXECUTE a read of menvcfg.  The debug module can report a value
 * for a register the machine will not let an instruction touch, so only a
 * `csrr` in the image measures what a kernel would see.
 *
 * `.option norvc` is required: trap.S advances mepc by 4, so every
 * instruction that can fault must be four bytes, and a board image is built
 * -march=rv64gc where the assembler compresses freely.
 *
 * RESULT layout (mirrored in vtest-rocq/CoreCsrprobe.v):
 *   +8 + 4*i   CSR i of the list below: 1 if reading it TRAPPED, else 0
 *   +8 + 4*36  THE CONTROL: an all-zeros (illegal) instruction word.  Must
 *              be 1 on every machine and in the model; if it is 0, the
 *              handler was never reached and the whole table is worthless.
 *   +0x800     the total number of traps taken (trap.S's own count)
 *   +0x810..   the individual trap records: mcause, mepc, mtval, 0
 */
/* vtest: repeat=1 */
    .option norvc
#include "abi.h"

/* Probe one CSR.  The trap COUNT before and after is the oracle: if the
   read trapped, trap.S incremented it and stepped over the csrr.
   t0/t1 are clobbered by any trap, so nothing here may hold a value in
   them across the read -- the count is loaded into s2/s3.

   s9 holds RESULT_BASE + RES_TRAPS.  It has to: RES_TRAPS is 0x800 and a
   load offset is a signed 12-bit immediate, so `lw s2, RES_TRAPN(s11)`
   does not assemble. */
.macro PROBE csr, slot
    lw   s2, 0(s9)
    csrr t2, \csr
    lw   s3, 0(s9)
    xor  s4, s2, s3
    snez s4, s4
    sw   s4, (RES_PAYLOAD + 4 * \slot)(s11)
.endm

/* the same, for a raw instruction word rather than a CSR read */
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

    /* install the handler.  Direct mode: mtvec's low two bits are 0 and
       _vtest_trap is .align 2. */
    lla  t0, _vtest_trap
    csrw mtvec, t0
    li   s9, RESULT_BASE + RES_TRAPS

    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- the M-mode file every machine here is expected to have ---- */
    PROBE 0x300, 0          /* mstatus       */
    PROBE 0x301, 1          /* misa          */
    PROBE 0x302, 2          /* medeleg       */
    PROBE 0x303, 3          /* mideleg       */
    PROBE 0x304, 4          /* mie           */
    PROBE 0x305, 5          /* mtvec         */
    PROBE 0x306, 6          /* mcounteren    */
    PROBE 0x340, 7          /* mscratch      */
    PROBE 0x341, 8          /* mepc          */
    PROBE 0x342, 9          /* mcause        */
    PROBE 0x343, 10         /* mtval         */
    PROBE 0x344, 11         /* mip           */
    PROBE 0xF11, 12         /* mvendorid     */
    PROBE 0xF12, 13         /* marchid       */
    PROBE 0xF13, 14         /* mimpid        */
    PROBE 0xF14, 15         /* mhartid       */

/* ---- privileged spec 1.11/1.12 additions: the ones a U74 predates ---- */
    PROBE 0x30A, 16         /* menvcfg       -- 1.12                     */
    PROBE 0xF15, 17         /* mconfigptr    -- 1.12                     */
    PROBE 0x320, 18         /* mcountinhibit -- 1.11                     */
    PROBE 0x10A, 19         /* senvcfg       -- 1.12                     */

/* ---- the S-mode file ---- */
    PROBE 0x100, 20         /* sstatus       */
    PROBE 0x104, 21         /* sie           */
    PROBE 0x105, 22         /* stvec         */
    PROBE 0x106, 23         /* scounteren    */
    PROBE 0x140, 24         /* sscratch      */
    PROBE 0x141, 25         /* sepc          */
    PROBE 0x142, 26         /* scause        */
    PROBE 0x143, 27         /* stval         */
    PROBE 0x144, 28         /* sip           */
    PROBE 0x180, 29         /* satp          */

/* ---- counters, M and unprivileged ---- */
    PROBE 0xB00, 30         /* mcycle        */
    PROBE 0xB02, 31         /* minstret      */
    PROBE 0xC00, 32         /* cycle         */
    PROBE 0xC01, 33         /* time          */
    PROBE 0xC02, 34         /* instret       */

/* ---- the debug/trigger stub core_regs_mcsr found instructive ---- */
    PROBE 0x7A0, 35         /* tselect       */

/* ---- THE CONTROL, and it is what makes every 0 above mean something.
 * All-zeros is a defined ILLEGAL instruction on RISC-V, so every machine
 * must trap on it -- and so must the model, which CoreRegsFpr.v already
 * shows takes mcause 2 on an instruction it does not implement.  Without
 * this, a run in which the handler was never reached and one in which every
 * CSR was readable produce the same all-zero table. */
    PROBEINSN 0x00000000, 36

    li   t0, 2
    sw   t0, RES_STATUS(s11)
    mv   ra, s10
    ret

#include "trap.S"
