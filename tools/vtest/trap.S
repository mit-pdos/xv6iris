/* trap.S -- AN M-MODE TRAP HANDLER, for a test that wants a trap to be DATA
 * rather than the end of the run.
 *
 * Include it at the END of a test source (after the body's `ret`) and point
 * mtvec at [_vtest_trap].  It is NOT in vtest.S: putting it there would add
 * bytes to all 58 images and invalidate every checked-in capture, to serve
 * the two tests that want it.
 *
 * WHY IT EXISTS.  mtvec is 0 at power-on, so by this suite's default rules a
 * fault sends the pc to 0, the fetch there is an undeclared address, and the
 * machine trap-loops forever (README.md, "A bad FETCH is a TRAP LOOP").  That
 * is fine when a trap is the ANSWER -- CoreRegsFpr.v pins the pc at two step
 * counts and reads the story out of mcause/mepc/mtval.  It is useless when a
 * trap is something to STEP OVER, for two reasons:
 *
 *   1. THE LOOP DESTROYS THE EVIDENCE.  The second trap overwrites mcause,
 *      mepc and mtval with its own (Instruction Access Fault at 0), so by the
 *      time anything looks, the original fault is gone.  Measured on the
 *      board 2026-08-29: core_regs_mcsr reported mcause=1 mepc=0 mtval=0,
 *      which says nothing; catching the FIRST trap with a hardware
 *      breakpoint gave mcause=2 mepc=0x8000008c mtval=0x30a022f3, i.e.
 *      `csrr t0, menvcfg`, which says everything.
 *   2. ONE TRAP ENDS THE RUN, so a program can only ever report its FIRST
 *      failure.  A probe that wants to ask forty questions gets one answer.
 *
 * WHAT IT DOES.  Records the trap and RESUMES PAST THE FAULTING INSTRUCTION,
 * so the program continues and can be asked the next question.
 *
 * THE CONTRACT, and a test using this must obey all four:
 *
 *   - t0 AND t1 ARE CLOBBERED BY ANY TRAP.  There is no save area; a handler
 *     that needed one would need a register to find it with.  Treat t0/t1 as
 *     dead across any instruction that might fault.
 *   - IT ADVANCES mepc BY 4, so every instruction that might trap must be
 *     four bytes.  Put `.option norvc` in the test source: it is its own
 *     compilation unit, and a board image is built -march=rv64gc where the
 *     assembler compresses freely.
 *   - IT DOES NOT NEST.  The handler itself must never fault -- it reads
 *     three always-present CSRs and stores into the declared RESULT region,
 *     and that is all it may ever do.
 *   - IT IS FOR SYNCHRONOUS EXCEPTIONS.  An interrupt would be recorded and
 *     "skipped" by advancing a pc that was not faulting.  Keep interrupts
 *     masked (they are: mstatus.MIE and mie are 0 at entry on every machine
 *     this suite runs on).
 *
 * THE RECORD, at RESULT_BASE + RES_TRAPS (see abi.h):
 *     +0            the number of traps taken so far
 *     +16 + 16*n    trap n: mcause, mepc, mtval, 0
 */

    .option norvc
    .align 2
    .globl _vtest_trap
_vtest_trap:
    /* t0 = the record area; t1 = the running count.  Both are documented as
       clobbered, which is what makes a save area unnecessary. */
    li   t0, RESULT_BASE + RES_TRAPS
    lw   t1, 0(t0)
    addi t1, t1, 1
    sw   t1, 0(t0)

    /* record n lands at +16*(n+1), so the count word at +0 is never
       overwritten by the first record */
    slli t1, t1, 4
    add  t0, t0, t1

    csrr t1, mcause
    sw   t1, 0(t0)
    csrr t1, mepc
    sw   t1, 4(t0)
    csrr t1, mtval
    sw   t1, 8(t0)

    /* step over the faulting instruction and go back.  Four bytes: see the
       contract above. */
    csrr t1, mepc
    addi t1, t1, 4
    csrw mepc, t1
    mret
