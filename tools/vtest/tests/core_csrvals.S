/* core_csrvals -- WHAT THE CSRs READ BACK, AND SOME OF IT IS EXPECTED TO
 * DISAGREE.
 *
 * This test exists to be RED.  It is core_csrprobe's value table, split out
 * into a run of its own: for each of the same thirty-seven registers, the
 * low 32 bits of what a `csrr` returned, or 0xffffffff if the read trapped.
 *
 * WHY IT IS SEPARATE.  core_csrprobe's subject is the SCOREBOARD -- does
 * reading this register trap? -- and measured, the model and QEMU give the
 * same answer for all thirty-seven.  The values do not: nine of them
 * disagree, and every one of the nine made the scoreboard unprovable.
 * Five are COUNTERS (mcycle, minstret, cycle, time, instret), which cannot
 * agree between two machines that execute a different number of
 * instructions and are not a finding about anything.  The other four are
 * real and are already in the findings table: `misa` (findings 19 and 29 --
 * the model, QEMU and the board all three differ), `mideleg` (finding 19's
 * consequence, hypervisor-dependent), and `mip` and `tselect`, which
 * README.md records as WITNESSED rather than findings.
 *
 * WHAT IT IS FOR.  The same thing the table always was: the model's column,
 * QEMU's column and the board's column side by side, for every CSR anyone
 * has wondered about, on a machine that refuses some of them partway
 * through the list.  That is a question core_regs_mcsr cannot answer,
 * because the first refusal ends its run.  A proof of this run is not
 * expected; what would be news is a word MOVING between the agreeing and
 * disagreeing sets.
 *
 * The poison matters: `li t2, -1` before each read means a slot whose read
 * TRAPPED is visibly 0xffffffff and not a plausible zero.
 *
 * `.option norvc` is required: trap.S advances mepc by 4, so every
 * instruction that can fault must be four bytes, and a board image is built
 * -march=rv64gc where the assembler compresses freely.
 *
 * RESULT layout:
 *   +8 + 4*i   the low 32 bits CSR i of the list below read back, or
 *              0xffffffff if reading it trapped
 *   +8 + 4*36  THE CONTROL: an all-zeros (illegal) instruction word, which
 *              every machine must trap on, so this slot must be 0xffffffff.
 *              If it is not, the handler was never reached and the whole
 *              table is worthless.
 *   +0x800     the total number of traps taken (trap.S's own count)
 *   +0x810..   the individual trap records: mcause, mepc, mtval, 0
 */
/* vtest: repeat=1 tick=0 budget=4000 */
    .option norvc
#include "abi.h"

/* Read one CSR and publish what it returned.  Unlike core_csrprobe this
   does not need the trap COUNT as an oracle -- the poison is the oracle --
   but it does need trap.S installed, so that a refusal steps over the
   `csrr` instead of ending the run. */
.macro VAL csr, slot
    li   t2, -1                 /* poison: a read that TRAPPED leaves this */
    csrr t2, \csr
    sw   t2, (RES_PAYLOAD + 4 * \slot)(s11)
.endm

/* the same, for a raw instruction word rather than a CSR read */
.macro VALINSN word, slot
    li   t2, -1
    .word \word
    sw   t2, (RES_PAYLOAD + 4 * \slot)(s11)
.endm

    .globl _vtest_body
_vtest_body:
    mv   s10, ra

    /* install the handler.  Direct mode: mtvec's low two bits are 0 and
       _vtest_trap is .align 2. */
    lla  t0, _vtest_trap
    csrw mtvec, t0

    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- the M-mode file every machine here is expected to have ---- */
    VAL 0x300, 0          /* mstatus       */
    VAL 0x301, 1          /* misa          */
    VAL 0x302, 2          /* medeleg       */
    VAL 0x303, 3          /* mideleg       */
    VAL 0x304, 4          /* mie           */
    VAL 0x305, 5          /* mtvec         */
    VAL 0x306, 6          /* mcounteren    */
    VAL 0x340, 7          /* mscratch      */
    VAL 0x341, 8          /* mepc          */
    VAL 0x342, 9          /* mcause        */
    VAL 0x343, 10         /* mtval         */
    VAL 0x344, 11         /* mip           */
    VAL 0xF11, 12         /* mvendorid     */
    VAL 0xF12, 13         /* marchid       */
    VAL 0xF13, 14         /* mimpid        */
    VAL 0xF14, 15         /* mhartid       */

/* ---- privileged spec 1.11/1.12 additions: the ones a U74 predates ---- */
    VAL 0x30A, 16         /* menvcfg       -- 1.12                     */
    VAL 0xF15, 17         /* mconfigptr    -- 1.12                     */
    VAL 0x320, 18         /* mcountinhibit -- 1.11                     */
    VAL 0x10A, 19         /* senvcfg       -- 1.12                     */

/* ---- the S-mode file ---- */
    VAL 0x100, 20         /* sstatus       */
    VAL 0x104, 21         /* sie           */
    VAL 0x105, 22         /* stvec         */
    VAL 0x106, 23         /* scounteren    */
    VAL 0x140, 24         /* sscratch      */
    VAL 0x141, 25         /* sepc          */
    VAL 0x142, 26         /* scause        */
    VAL 0x143, 27         /* stval         */
    VAL 0x144, 28         /* sip           */
    VAL 0x180, 29         /* satp          */

/* ---- counters, M and unprivileged ---- */
    VAL 0xB00, 30         /* mcycle        */
    VAL 0xB02, 31         /* minstret      */
    VAL 0xC00, 32         /* cycle         */
    VAL 0xC01, 33         /* time          */
    VAL 0xC02, 34         /* instret       */

/* ---- the debug/trigger stub core_regs_mcsr found instructive ---- */
    VAL 0x7A0, 35         /* tselect       */

/* ---- THE CONTROL, and it is what makes every value above mean something.
 * All-zeros is a defined ILLEGAL instruction on RISC-V, so every machine
 * must trap on it -- and so must the model, which CoreRegsFpr.v already
 * shows takes mcause 2 on an instruction it does not implement.  This slot
 * must therefore read 0xffffffff; if it reads anything else the handler was
 * never reached and every 0xffffffff above is a real value, not a refusal. */
    VALINSN 0x00000000, 36

    li   t0, 2
    sw   t0, RES_STATUS(s11)
    mv   ra, s10
    ret

#include "trap.S"
