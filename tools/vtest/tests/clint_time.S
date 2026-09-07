/* clint_time -- THE CLOCK.  The first test in this suite to touch the CLINT
 * at all, and the first to ask a question whose answer the harness itself
 * decides.
 *
 * WHY THIS AREA IS DIFFERENT.  The UART, the PLIC and the disk are
 * DevModel.v's -- a device fabric beside the byte memory, stepped by
 * VSched.  The CLINT is not: the Sail model dispatches its window itself
 * ([plat_clint_base] = 0x0200_0000, [plat_clint_size] = 0xC_0000, and
 * clint_load/clint_store in rv64d.v), so an access here never reaches the
 * interpreter's device fabric and nothing in tools/vtest/ has ever
 * exercised it.  This is unexplored ground on both machines.
 *
 * WHAT IT IS LOOKING FOR.  vtest-rocq/VTest.v always steps
 * [riscv_step false] -- the clock does NOT tick -- so [mtime] is frozen at
 * whatever the reset chain left, and two reads separated by a thousand
 * instructions return the SAME value.  On any real machine they do not.
 * That is a hardware behaviour with no model execution, which is the
 * unsound direction, and it is why this test records the comparison as a
 * FLAG rather than only recording the raw values: the raw words can only
 * ever be pinned as a divergence, but "did it advance?" is a question both
 * machines answer and the model answers WRONGLY.
 *
 * [minstret] and [mcycle] are the CONTROLS, and they are what make the
 * result attributable.  [minstret] advances in the model as well as on the
 * machine, so a frozen [mtime] is about the CLOCK and not about counters
 * being unimplemented; [mcycle] is driven by the same clock as [mtime] and
 * should freeze with it.
 *
 * Both machines: no hart indexing anywhere in this test.  MTIME is at a
 * fixed offset (0xBFF8) that is not per-hart, so this test asks the same
 * question of QEMU's hart 0 and of the board's hart 2.  clint_msip and
 * clint_mtimecmp are the ones that need the index; see those.
 *
 * ONLY THE FLAGS ARE RECORDED, and that is the whole reason this test is
 * shaped the way it is.  A raw mtime, a raw minstret delta and a raw mcycle
 * delta are values no two machines can be asked to agree on -- measured,
 * the model and QEMU differ at every one of them (+8, +16, +32, +44, +52) --
 * so putting them in the result region makes this test unprovable while
 * telling nobody anything a comparison of the flags does not.  The
 * questions "did it advance?", "did it go backwards?" and "do the 4-byte
 * halves bracket the 8-byte read?" are questions both machines and the
 * model answer, and they are the ones this test is about.
 *
 * The raw words are not thrown away: clint_raw publishes exactly them, and
 * is expected to be RED for as long as the divergence stands.
 *
 * RESULT layout (the gaps are deliberate; the region is zero-filled, so an
 * unwritten word reads 0 on both machines):
 *   +24   1 if mtime STRICTLY advanced              <- THE FINDING
 *   +28   1 if mtime did not go BACKWARDS           <- both machines: 1
 *   +40   1 if the 4-byte halves bracket the 8-byte read
 *   +48   1 if minstret advanced                    <- control: 1 in both
 *   +56   1 if mcycle advanced                      <- driven by the same clock
 */
/* vtest: repeat=1 tick=1 budget=8000 */
#include "abi.h"

#define R_ADV     24
#define R_NOBACK  28
#define R_BRACKET 40
#define R_INSTRADV 48
#define R_CYCLEADV 56

/* THE CAP IS A DEAD-CLOCK BACKSTOP, NOT THE WAIT.  The loop below spins
   until mtime CHANGES and gives up after this many tries, so the cap is
   reached only when the clock is not running -- which is the very thing
   R_ADV reports.  It is not a delay: a fixed-count delay has to be sized
   for the SLOWEST clock and then everyone pays for it. */
#define WAITCAP   4000

    .globl _vtest_body
_vtest_body:
    li   s0, CLINT_MTIME

    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- the first sample: mtime, minstret and mcycle together ---- */
    ld   s1, 0(s0)                   /* s1 = mtime before */
    csrr s2, minstret                /* s2 = minstret before */
    csrr s3, mcycle                  /* s3 = mcycle before */

/* ---- WAIT FOR THE CLOCK TO MOVE, rather than spinning a fixed count ----
 *
 * This used to be `DELAY` iterations of a two-instruction loop, sized so
 * that even the slowest clock must tick.  That is the wrong shape twice
 * over.  It made this test the most expensive in the suite -- ~2000 model
 * instructions, essentially its whole runtime on BOTH platforms, and the
 * model needs none of it because with tick=1 mtime advances on every step.
 * And it was sized by guesswork: measured, DELAY=1000 bought the board
 * about 4 RTC ticks and DELAY=250 bought exactly ONE, i.e. no margin at
 * all, so the cheap version was one scheduling wobble from reporting a
 * stopped clock.
 *
 * Spinning until mtime CHANGES removes the sizing question entirely: the
 * model leaves after one iteration, the board after ~one RTC period, and
 * neither depends on a constant somebody has to re-tune per machine.  The
 * cap keeps a dead clock reporting R_ADV = 0 instead of hanging. */
    li   t2, WAITCAP
1:  ld   t1, 0(s0)
    bne  t1, s1, 2f                  /* it moved -- stop waiting */
    addi t2, t2, -1
    bnez t2, 1b
2:

/* ---- the second sample ---- */
    ld   s4, 0(s0)                   /* s4 = mtime after */
    csrr s5, minstret
    csrr s6, mcycle

/* ---- THE FINDING: did the clock advance at all? ---- */
    sltu t0, s1, s4                  /* before <u after */
    sw   t0, R_ADV(s11)
    sltu t0, s4, s1                  /* after <u before, i.e. went backwards */
    xori t0, t0, 1
    sw   t0, R_NOBACK(s11)

/* ---- the 4-byte halves.  The model decodes MTIME at width 4 and width 8
 * from two different addresses (MTIME_BASE / MTIME_BASE_HI); this checks
 * the pair is consistent with an 8-byte read taken around it, which is the
 * only way to compare a moving counter across access widths. */
    ld   s7, 0(s0)                   /* bracket low  */
    lwu  t1, 0(s0)                   /* 4-byte lo    */
    lwu  t2, 4(s0)                   /* 4-byte hi    */
    ld   s8, 0(s0)                   /* bracket high */
    slli t2, t2, 32
    or   t1, t1, t2                  /* the reassembled 64-bit value */
    sltu t3, t1, s7                  /* below the bracket? */
    sltu t4, s8, t1                  /* above the bracket? */
    or   t3, t3, t4
    xori t3, t3, 1                   /* 1 iff s7 <= t1 <= s8 */
    sw   t3, R_BRACKET(s11)

/* ---- the controls ---- */
    sub  t0, s5, s2
    snez t0, t0
    sw   t0, R_INSTRADV(s11)
    sub  t0, s6, s3
    snez t0, t0
    sw   t0, R_CYCLEADV(s11)

    li   t0, 2
    sw   t0, RES_STATUS(s11)
    ret
