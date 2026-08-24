/* uart_irq_rx -- the UART as an INTERRUPT SOURCE, receive side, end to end
 * into mip.  The companion of uart_irq_tx, and the only test in the suite
 * that uses the runner's serial INPUT.
 *
 * One byte, 0x41, is pushed in by the host (the `vtest:` directive below).
 * On the model side that byte is not an automatic event -- receiving is the
 * only externally-driven thing in the suite -- it is a SCHEDULE choice, the
 * [SUartRx] arm of VSched, and vtest-rocq/UartIrqRx.v delivers it explicitly.
 *
 * Exactly ONE byte on purpose.  With the FIFOs disabled QEMU's 16550 accepts
 * a single character at a time and the front end re-offers the next one
 * asynchronously, so a two-byte injection would let the drain loop see the
 * FIFO empty and the interrupt re-raise afterwards -- nondeterminism with
 * nothing to do with the subject.  The FIFOs are deliberately NOT enabled:
 * any FCR write that flips FIFO-enable also flushes the receive FIFO in real
 * hardware, which would race with the host's byte.
 *
 * We are in M-mode with interrupts disabled: nothing traps, everything is
 * polled, and the spin on the PLIC pending bit is what makes the model's
 * propagation delay (the gateway latch and the wire are the device's own
 * steps) tested rather than assumed.  mip is masked to bit 9, SEIP.
 *
 * RESULT layout (mirrored in vtest-rocq/UartIrqRx.v):
 *   +8   LSR with the byte waiting, IER = 0       (0x61: DR|THRE|TEMT)
 *   +12  PLIC pending, IER = 0                    (0: rx int not enabled)
 *   +16  mip & SEIP, IER = 0                      (0)
 *   +20  ISR, IER = 0
 *   +24  PLIC pending after IER bit 0 set         (0x400: source 10)
 *   +28  mip & SEIP                               (0x200)
 *   +32  ISR: the cause                           (rx data available)
 *   +36  ISR & 0x0f: the cause, FIFO bits masked  (4)
 *   +40  what the S-context claim returned        (10)
 *   +44  PLIC pending after the claim             (0)
 *   +48  mip & SEIP after the claim               (0)
 *   +52  the byte read out of RHR                 (0x41)
 *   +56  how many bytes the drain loop read       (1)
 *   +60  LSR after draining                       (0x60: DR gone)
 *   +64  ISR after draining                       (nothing pending)
 *   +68  PLIC pending after PLIC complete         (0)
 *   +72  mip & SEIP at the end                    (0)
 */
/* vtest: serial_in=0x41 */
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
#define R_RX0     52
#define R_RXN     56
#define R_LSR1    60
#define R_ISR2    64
#define R_PEND3   68
#define R_MIP3    72

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
    li   s0, UART0
    li   s2, PLIC

/* ---- PLIC: source 10 routed to hart 0's S context ---- */
    li   t0, 1
    sw   t0, P_PRIO10(s2)
    li   t1, P_SENABLE
    add  t1, s2, t1
    li   t0, SRC10
    sw   t0, 0(t1)
    li   t1, P_STHRESH
    add  t1, s2, t1
    sw   zero, 0(t1)

    li   s1, P_PENDING
    add  s1, s2, s1
    li   s3, P_SCLAIM
    add  s3, s2, s3

/* ---- (1) wait for the host's byte; IER = 0, so no interrupt ---- */
1:  lbu  t0, 5(s0)
    andi t0, t0, 0x01                /* DR: data ready */
    beqz t0, 1b
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

/* ---- (2) enable the rx interrupt; SPIN for the pending bit ---- */
    li   t0, 0x01
    sb   t0, 1(s0)                   /* IER = rx data available */
2:  lw   t0, 0(s1)
    andi t0, t0, SRC10
    beqz t0, 2b
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

/* ---- (5) remove the condition: drain RHR until DR is clear ---- */
    li   t3, 0                       /* count */
    li   t4, 0                       /* first byte */
3:  lbu  t0, 5(s0)
    andi t0, t0, 0x01
    beqz t0, 4f
    lbu  t5, 0(s0)                   /* RHR: pops the receive FIFO */
    bnez t3, 5f
    mv   t4, t5
5:  addi t3, t3, 1
    j    3b
4:  sw   t4, R_RX0(s11)
    sw   t3, R_RXN(s11)
    lbu  t0, 5(s0)
    sw   t0, R_LSR1(s11)
    lbu  t0, 2(s0)
    sw   t0, R_ISR2(s11)

/* ---- (6) complete at the PLIC; the line is low, so nothing re-latches ---- */
    li   t0, 10
    sw   t0, 0(s3)
    lw   t0, 0(s1)
    sw   t0, R_PEND3(s11)
    csrr t0, mip
    andi t0, t0, 0x200
    sw   t0, R_MIP3(s11)
    sb   zero, 1(s0)                 /* IER = 0 */
    li   t0, 3
    sw   t0, RES_STATUS(s11)

    mv   ra, s10
    ret
