/* uart1_irq -- THE SECOND PORT'S INTERRUPT, and it is on SOURCE 12.
 *
 * uart_irq_tx drives the same chain from port 0 -- [uart_tx_int] ->
 * [uart_irq] / [dev_irq_level] -> [plic_latch] -> [plic_step]'s wire onto
 * sig_seip -- and the ONE thing it cannot check is which PLIC source the
 * UART is wired to, because there was only one UART.  With two ports the
 * routing is a real question and the model answers it with [uart_irq_id]
 * (10 and 12) and its inverse [uart_of_irq], which is what the gateway
 * uses to decide whose level it is looking at.  QEMU virt's own device tree
 * says the same: serial@10000000 interrupts <0xa>, serial@1000a000 <0xc>.
 *
 * So this case asks it BOTH WAYS, and the negative half is the load-bearing
 * one -- a model that put both ports on source 10 would pass a
 * source-12-only test that never looked at 10:
 *
 *   (1) WITH ONLY SOURCE 10 ENABLED at this hart's S context, port 1's line
 *       does NOT reach the hart.  Source 12's pending bit DOES latch (the
 *       enable bit is not the gateway -- plic_mask), and the claim still
 *       returns 0 and leaves it pending, and mip.SEIP stays clear.  Source
 *       10's own pending bit is never set at all: port 0's IER is 0.
 *   (2) ENABLE SOURCE 12 and the same still-asserted level is delivered:
 *       SEIP goes high and the claim hands back 12, not 10.
 *
 * We are in M-mode with interrupts disabled throughout, so nothing traps
 * and every step is observed by POLLING -- which is what makes the model's
 * propagation delay (the gateway latch and the wire are the device's own
 * steps, not side effects of the MMIO write) tested rather than assumed.
 * mip is masked to bit 9 (SEIP): the harness holds the clock still, so the
 * timer bit would diverge for reasons that have nothing to do with the UART.
 *
 * QEMU QUIRK, and it is why the threshold is re-written at (2):
 * sifive_plic_write does not recompute the context notification on an
 * ENABLE write, so it lags by one register access.  The re-write is the
 * same value and is a no-op on the model side (plic_mask.S does the same).
 *
 * Priorities are <= 7: the virt PLIC is built with num-priorities = 7 and
 * silently ignores anything above.
 *
 * RESULT layout:
 *   +8   PLIC pending, both IERs 0                        (0)
 *   +12  PLIC pending after port 1's IER bit 1 is set     (0x1000: source 12)
 *   +16  that pending word AND bit 10                     (0: port 0 is quiet)
 *   +20  mip & SEIP, only source 10 enabled               (0: NOT delivered)
 *   +24  what the S-context claim returns then            (0)
 *   +28  PLIC pending after that claim                    (0x1000: still there)
 *   +32  port 1's ISR: the cause, FIFO bits masked        (2: THRE)
 *   +36  port 0's ISR                                     (1: nothing pending)
 *   +40  mip & SEIP once source 12 is enabled             (0x200)
 *   +44  PLIC pending at that point                       (0x1000)
 *   +48  what the S-context claim returns                 (12)
 *   +52  PLIC pending after the claim                     (0)
 *   +56  mip & SEIP after the claim                       (0)
 *   +60  PLIC pending after IER = 0 and PLIC complete     (0)
 *   +64  mip & SEIP at the end                            (0)
 */
/* vtest: repeat=1 platforms=qemu uarts=2 budget=50000 */
#include "abi.h"

#define PLIC        0x0c000000
#define P_PRIO10    40                  /* 4 * 10 */
#define P_PRIO12    48                  /* 4 * 12 */
#define P_PENDING   0x1000
#define P_SENABLE   PLIC_SENABLE
#define P_STHRESH   PLIC_STHRESH
#define P_SCLAIM    PLIC_SCLAIM
#define SRC10       0x400               /* bit 10 */
#define SRC12       0x1000              /* bit 12 */

#define R_PEND0   8
#define R_PEND1   12
#define R_P10     16
#define R_MIP0    20
#define R_CLAIM0  24
#define R_PEND2   28
#define R_ISR1    32
#define R_ISR0    36
#define R_MIP1    40
#define R_PEND3   44
#define R_CLAIM1  48
#define R_PEND4   52
#define R_MIP2    56
#define R_PEND5   60
#define R_MIP3    64

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
    li   s0, UART1
    li   s6, UART0
    li   s2, PLIC

/* ---- PLIC: both sources given a priority, ONLY SOURCE 10 ENABLED ---- */
    li   t0, 1
    sw   t0, P_PRIO10(s2)
    li   t0, 1
    sw   t0, P_PRIO12(s2)
    li   s4, P_SENABLE
    add  s4, s2, s4
    li   t0, SRC10
    sw   t0, 0(s4)                   /* enable source 10 and nothing else */
    li   s5, P_STHRESH
    add  s5, s2, s5
    sw   zero, 0(s5)                 /* threshold 0: priority 1 gets through */

    li   s1, P_PENDING
    add  s1, s2, s1                  /* s1 = pending word 0 */
    li   s3, P_SCLAIM
    add  s3, s2, s3                  /* s3 = claim/complete */

/* ---- (0) nothing is pending: neither port's IER is set ---- */
    lw   t0, 0(s1)
    sw   t0, R_PEND0(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- (1) port 1's THRE interrupt.  Its FIFO is empty, so the line goes
 * high at once and the gateway latches source 12 even though the context
 * does not have it enabled.  SPIN: the latch is a device step of its own. ---- */
    li   t0, 0x02
    sb   t0, UART_REG(1)(s0)                   /* port 1 IER = THRE enable */
    li   s7, SRC12                   /* > 2047: andi cannot take it */
1:  lw   t0, 0(s1)
    and  t0, t0, s7
    beqz t0, 1b
    lw   t0, 0(s1)
    sw   t0, R_PEND1(s11)
    andi t1, t0, SRC10
    sw   t1, R_P10(s11)
    csrr t0, mip
    andi t0, t0, 0x200
    sw   t0, R_MIP0(s11)             /* NOT delivered: source 12 is masked */
    lw   t0, 0(s3)
    sw   t0, R_CLAIM0(s11)           /* ...and not claimable either */
    lw   t0, 0(s1)
    sw   t0, R_PEND2(s11)            /* the refused claim left it pending */
    li   t0, 2
    sw   t0, RES_STATUS(s11)

/* ---- the two ISRs: port 1 names THRE, port 0 has nothing ---- */
    lbu  t0, UART_REG(2)(s0)
    andi t0, t0, 0x0f
    sw   t0, R_ISR1(s11)
    lbu  t0, UART_REG(2)(s6)
    andi t0, t0, 0x0f
    sw   t0, R_ISR0(s11)

/* ---- (2) enable source 12.  The level never dropped, so the SAME request
 * is now visible to this context.  The threshold re-write is the QEMU
 * recompute nudge described in the header. ---- */
    li   t0, SRC10 + SRC12
    sw   t0, 0(s4)
    sw   zero, 0(s5)                 /* same value: forces the recompute */
2:  csrr t0, mip
    andi t0, t0, 0x200
    beqz t0, 2b
    sw   t0, R_MIP1(s11)
    lw   t0, 0(s1)
    sw   t0, R_PEND3(s11)
    li   t0, 3
    sw   t0, RES_STATUS(s11)

/* ---- (3) the claim names the SECOND port's source ---- */
    lw   t0, 0(s3)
    sw   t0, R_CLAIM1(s11)
    lw   t0, 0(s1)
    sw   t0, R_PEND4(s11)
    csrr t0, mip
    andi t0, t0, 0x200
    sw   t0, R_MIP2(s11)

/* ---- (4) remove the condition, then complete ---- */
    sb   zero, UART_REG(1)(s0)                 /* port 1 IER = 0: the line drops */
    li   t0, 12
    sw   t0, 0(s3)                   /* PLIC complete, source 12 */
    lw   t0, 0(s1)
    sw   t0, R_PEND5(s11)
    csrr t0, mip
    andi t0, t0, 0x200
    sw   t0, R_MIP3(s11)
    li   t0, 4
    sw   t0, RES_STATUS(s11)

    mv   ra, s10
    ret
