/* uart_irq_tx -- the UART as an INTERRUPT SOURCE, transmit side, end to end
 * into mip.
 *
 * The chain under test is four model components in series, and the UART is
 * the only one of them this suite had never driven: [uart_tx_int] (IER bit 1
 * AND the tx FIFO empty), [uart_irq] / [dev_irq_level] (which puts that level
 * on PLIC source 10), [plic_latch] (the per-source gateway) and [plic_step]
 * (the wire onto hart 0's sig_seip, visible in mip bit 9).  disk_intr.S
 * exercises the last three from source 1; nothing had ever raised source 10.
 *
 * We are in M-mode with interrupts disabled throughout, so nothing traps:
 * every step is observed by POLLING, which is also what makes the model's
 * deliberate propagation delay (the gateway latch and the wire are the
 * device's own steps, not side effects of the MMIO write) testable rather
 * than assumed -- the test spins on the pending bit instead of reading it
 * once.
 *
 * mip is masked to bit 9 (SEIP): the harness always steps riscv_step with
 * the clock tick off, so the timer bit would diverge for a reason that has
 * nothing to do with the UART, and our plic_step drives sig_seip only.
 *
 * PLIC, source 10:  priority at +4*10, S-enable bit 10 at +0x2080,
 * threshold at +0x201000, claim/complete at +0x201004.
 *
 * RESULT layout (mirrored in vtest-rocq/UartIrqTx.v):
 *   +8   LSR at rest                                  (0x60: THRE|TEMT)
 *   +12  PLIC pending, IER = 0                        (0: no line)
 *   +16  mip & SEIP, IER = 0                          (0)
 *   +20  ISR, IER = 0
 *   +24  PLIC pending after IER bit 1 set             (0x400: source 10)
 *   +28  mip & SEIP                                   (0x200)
 *   +32  ISR: the cause                               (THRE)
 *   +36  ISR & 0x0f: the cause with the FIFO bits masked off  (2)
 *   +40  what the S-context claim returned            (10)
 *   +44  PLIC pending after the claim                 (0)
 *   +48  mip & SEIP after the claim                   (0)
 *   +52  PLIC pending after clearing IER bit 1 and completing   (0)
 *   +56  mip & SEIP at the end of the chain           (0)
 *   ---- and then, separately, the SECOND ISR READ ----
 *   +60  ISR, IER bit 1 set again, first read
 *   +64  ISR, second read, nothing in between
 *   +68  PLIC pending after those two reads
 *   +72  mip & SEIP after those two reads
 */
/* vtest: repeat=1 */
#include "abi.h"

#define PLIC        0x0c000000
#define P_PRIO10    40                  /* 4 * 10 */
#define P_PENDING   0x1000
#define P_SENABLE   0x2080              /* hart 0, S context */
#define P_STHRESH   0x201000
#define P_SCLAIM    0x201004
#define SRC10       0x400               /* bit 10 */

#define R_LSR0    8
#define R_PEND0   12
#define R_MIP0    16
#define R_ISR0    20
#define R_PEND1   24
#define R_MIP1    28
#define R_ISR1    32
#define R_CAUSE1  36
#define R_CLAIM   40
#define R_PEND2   44
#define R_MIP2    48
#define R_PEND3   52
#define R_MIP3    56
#define R_ISR3    60
#define R_ISR4    64
#define R_PEND4   68
#define R_MIP4    72

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
    li   s0, UART0
    li   s2, PLIC

/* ---- PLIC: source 10 routed to hart 0's S context ---- */
    li   t0, 1
    sw   t0, P_PRIO10(s2)            /* priority[10] = 1 */
    li   t1, P_SENABLE
    add  t1, s2, t1
    li   t0, SRC10
    sw   t0, 0(t1)
    li   t1, P_STHRESH
    add  t1, s2, t1
    sw   zero, 0(t1)                 /* threshold 0: priority 1 gets through */

    li   s1, P_PENDING
    add  s1, s2, s1                  /* s1 = pending word */
    li   s3, P_SCLAIM
    add  s3, s2, s3                  /* s3 = claim/complete */

/* ---- (1) IER = 0: the UART drives nothing ---- */
    lbu  t0, 5(s0)
    sw   t0, R_LSR0(s11)
    lw   t0, 0(s1)
    sw   t0, R_PEND0(s11)
    csrr t0, mip
    andi t0, t0, 0x200
    sw   t0, R_MIP0(s11)
    lbu  t0, 2(s0)
    sw   t0, R_ISR0(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- (2) enable the THRE interrupt: the FIFO is empty, so the line goes
 * high at once.  SPIN: the latch and the wire are separate device steps. ---- */
    li   t0, 0x02
    sb   t0, 1(s0)                   /* IER = THRE interrupt enable */
1:  lw   t0, 0(s1)
    andi t0, t0, SRC10
    beqz t0, 1b
    lw   t0, 0(s1)
    sw   t0, R_PEND1(s11)
    csrr t0, mip
    andi t0, t0, 0x200
    sw   t0, R_MIP1(s11)

/* ---- (3) the ISR identifies the cause ---- */
    lbu  t0, 2(s0)
    sw   t0, R_ISR1(s11)
    andi t2, t0, 0x0f
    sw   t2, R_CAUSE1(s11)
    li   t0, 2
    sw   t0, RES_STATUS(s11)

/* ---- (4) claim ---- */
    lw   t0, 0(s3)
    sw   t0, R_CLAIM(s11)
    lw   t0, 0(s1)
    sw   t0, R_PEND2(s11)
    csrr t0, mip
    andi t0, t0, 0x200
    sw   t0, R_MIP2(s11)

/* ---- (5,6) remove the condition, then complete ---- */
    sb   zero, 1(s0)                 /* IER = 0: the line drops */
    li   t0, 10
    sw   t0, 0(s3)                   /* PLIC complete, source 10 */
    lw   t0, 0(s1)
    sw   t0, R_PEND3(s11)
    csrr t0, mip
    andi t0, t0, 0x200
    sw   t0, R_MIP3(s11)
    li   t0, 3
    sw   t0, RES_STATUS(s11)

/* ---- the SECOND ISR READ, on its own, so it does not contaminate the
 * chain above.  Our model treats the THRE interrupt as a LEVEL; a real
 * 16550 latches it and the ISR read is what clears it. ---- */
    li   t0, 0x02
    sb   t0, 1(s0)
2:  lw   t0, 0(s1)
    andi t0, t0, SRC10
    beqz t0, 2b
    lbu  t0, 2(s0)
    sw   t0, R_ISR3(s11)
    lbu  t0, 2(s0)
    sw   t0, R_ISR4(s11)
    lw   t0, 0(s1)
    sw   t0, R_PEND4(s11)
    csrr t0, mip
    andi t0, t0, 0x200
    sw   t0, R_MIP4(s11)
    li   t0, 4
    sw   t0, RES_STATUS(s11)

    mv   ra, s10
    ret
