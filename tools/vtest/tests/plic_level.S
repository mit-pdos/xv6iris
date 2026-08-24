/* plic_level -- the GATEWAY, on a source whose level the driver never drops.
 *
 * disk_intr walks the happy path: the driver acknowledges the DEVICE first,
 * so by the time it completes at the PLIC the line is already low and the
 * gateway has nothing to re-forward.  This test does the two things that
 * path never does, on one source, and they are where the model and QEMU
 * separate.
 *
 *   Phase 1 -- the level DROPS while the request is still pending, nothing
 *   having claimed it.  [DevModel.plic_latch] only ever SETS a pending bit;
 *   nothing in the model clears it but a claim, so the model keeps the
 *   request.  So does QEMU, and this half AGREES: a forwarded request
 *   survives its source going quiet, and the context still sees it.
 *
 *   Phase 2 -- the context COMPLETES while the level is still asserted.  The
 *   model's gateway forwards the still-high level again the moment
 *   [plic_complete] clears the claimed bit, so one device request yields a
 *   SECOND interrupt.  QEMU's pending bit is edge-driven and there is no new
 *   edge, so it stays down.
 *
 * The source is the 16550 at source 10, raised with NO serial input by
 * enabling the transmit-holding-register-empty interrupt in IER while the
 * FIFO is empty -- and note that the model's THRE interrupt is a LEVEL that
 * an ISR read does not clear (see the comment above [DevModel.uart_isr]),
 * which is exactly why it is a good probe for a gateway question: the level
 * stays up unless this program lowers IER itself.  Nothing here reads the
 * ISR, so nothing here depends on that.
 */
/* vtest: repeat=1 */
#include "abi.h"

#define PLIC        0x0c000000
#define P_PENDING   0x1000
#define P_SENABLE   0x2080          /* hart 0, S context */
#define P_STHRESH   0x201000
#define P_SCLAIM    0x201004

/* result-region offsets -- MIRRORED in vtest-rocq/PlicLevel.v */
#define R_PEND0    8   /* pending, line up                          0x400  */
#define R_PENDD   12   /* pending after the line DROPS -- STICKY     0x400 */
#define R_MIPD    16   /* mip & SEIP there                           0x200 */
#define R_PENDR   20   /* pending, line up again                    0x400  */
#define R_CLAIM1  24   /* the claim                                  10    */
#define R_PEND1   28   /* pending after it                           0     */
#define R_PENDC   32   /* pending after COMPLETE, line still up             */
                       /*                              QEMU 0  model 0x400 */
#define R_MIPC    36   /* mip & SEIP there             QEMU 0  model 0x200 */
#define R_CLAIM2  40   /* a second claim               QEMU 0  model 10    */
#define R_IER     44   /* the UART's IER read back                   2     */
#define R_LSR     48   /* the UART's LSR: THRE|TEMT still set        0x60   */

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
    li   s3, UART0
    li   s2, PLIC
    li   s4, P_PENDING
    add  s4, s2, s4
    li   s5, P_SCLAIM
    add  s5, s2, s5

    li   t0, 7
    sw   t0, 40(s2)                  /* prio[10] = 7 */
    li   t1, P_STHRESH
    add  t1, s2, t1
    sw   zero, 0(t1)                 /* threshold 0 */
    li   t1, P_SENABLE
    add  t1, s2, t1
    li   t0, 0x400
    sw   t0, 0(t1)                   /* enable source 10 */

    li   t0, 3
    sb   t0, 3(s3)                   /* LCR = 8N1, DLAB clear */

/* ---- phase 1: raise the line, then drop it with nothing claimed ---- */
    li   t0, 2
    sb   t0, 1(s3)                   /* IER = THRE: the FIFO is empty, so the
                                        line goes high with no serial input */
/* the gateway latch is the DEVICE's own step, not a side effect of the
   completing MMIO write, so SPIN rather than reading once */
1:  lw   t0, 0(s4)
    andi t6, t0, 0x400
    beqz t6, 1b
    sw   t0, R_PEND0(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)

    sb   zero, 1(s3)                 /* IER = 0: the line drops */
    lw   t0, 0(s4)
    sw   t0, R_PENDD(s11)            /* read ONCE -- this is the observation */
    csrr t0, mip
    andi t0, t0, 0x200               /* SEIP only: the harness steps
                                        riscv_step with the clock tick off,
                                        so MTIP would diverge for a reason
                                        that has nothing to do with the PLIC */
    sw   t0, R_MIPD(s11)

    li   t0, 2
    sb   t0, 1(s3)                   /* IER = THRE again: the line is back up */
2:  lw   t0, 0(s4)
    andi t6, t0, 0x400
    beqz t6, 2b
    sw   t0, R_PENDR(s11)
    li   t0, 2
    sw   t0, RES_STATUS(s11)

/* ---- phase 2: claim, then complete with the line STILL up ---- */
    lw   t0, 0(s5)
    sw   t0, R_CLAIM1(s11)
    lw   t0, 0(s4)
    sw   t0, R_PEND1(s11)

    li   t0, 10
    sw   t0, 0(s5)                   /* complete source 10 */
    lw   t0, 0(s4)
    sw   t0, R_PENDC(s11)            /* read ONCE -- this is the observation */
    csrr t0, mip
    andi t0, t0, 0x200
    sw   t0, R_MIPC(s11)
    lw   t0, 0(s5)
    sw   t0, R_CLAIM2(s11)           /* a second interrupt for one request? */

/* The UART's own registers, to settle what the divergence above IS about:
   IER bit 1 is still set and the transmit FIFO is still empty, on BOTH
   machines, and that conjunction is the definition of the THRE interrupt
   condition.  So the source's level really is still asserted at this point
   and the two machines differ on what the GATEWAY does with it, not on
   whether there is anything to forward.  Neither read perturbs the line:
   [DevModel.uart_read] is pure at both offsets, and QEMU re-runs
   serial_update_irq on an LSR read only when a break/overrun bit is set. */
    lbu  t0, 1(s3)
    sw   t0, R_IER(s11)
    lbu  t0, 5(s3)
    sw   t0, R_LSR(s11)

    li   t0, 3
    sw   t0, RES_STATUS(s11)
    mv   ra, s10
    ret
