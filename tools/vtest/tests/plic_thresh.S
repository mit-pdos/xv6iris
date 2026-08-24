/* plic_thresh -- the CONTEXT THRESHOLD, and what it is supposed to gate.
 *
 * One source is enough for this one, so it uses the cheap one: the 16550 at
 * source 10, raised with NO serial input by enabling the transmit-holding-
 * register-empty interrupt in IER while the FIFO is empty.  No virtqueue,
 * so the model side declares only the stack and the result region.
 *
 * Two separate questions, and the model answers only the first of them the
 * way the hardware does:
 *
 *   (a) does the threshold gate the NOTIFICATION (the wire onto mip.SEIP)?
 *       -- and it must gate it STRICTLY: priority == threshold is masked,
 *       priority > threshold is not.  Both machines agree, both ways round.
 *
 *   (b) does the threshold gate the CLAIM?  On the hardware it does: a claim
 *       whose only pending source is at or below the threshold returns 0 and
 *       leaves that source PENDING.  [DevModel.plic_claim] goes through
 *       [plic_best]/[plic_cand], which never look at [p_thresh] at all, so
 *       the model hands the masked source back and clears its pending bit.
 *       See vtest-rocq/PlicThresh.v section 3.
 *
 * NOTE ON PRIORITY VALUES: QEMU's virt machine builds its PLIC with
 * num-priorities = 7 and SILENTLY IGNORES a priority or threshold write
 * above that, so every value here is <= 7.
 */
/* vtest: repeat=1 */
#include "abi.h"

#define PLIC        0x0c000000
#define P_PENDING   0x1000
#define P_SENABLE   0x2080          /* hart 0, S context */
#define P_STHRESH   0x201000
#define P_SCLAIM    0x201004

/* result-region offsets -- MIRRORED in vtest-rocq/PlicThresh.v */
#define R_PEND0    8   /* pending, source 10 up                     0x400  */
#define R_MIPEQ   12   /* mip & SEIP, threshold == priority         0      */
#define R_MIPLT   16   /* mip & SEIP, threshold <  priority         0x200  */
#define R_MIPEQ2  20   /* mip & SEIP, threshold == priority again   0      */
#define R_CLAIM1  24   /* claim while MASKED    QEMU 0     model 10        */
#define R_PEND1   28   /* pending after it      QEMU 0x400 model 0         */
#define R_MIP0    32   /* mip after threshold 0 QEMU 0x200 model 0         */
#define R_CLAIM2  36   /* claim, unmasked       QEMU 10    model 0         */
#define R_PEND2   40   /* pending after it                          0      */
#define R_THRESH  44   /* the threshold register read back           0     */

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
    li   s3, UART0
    li   s2, PLIC
    li   s4, P_PENDING
    add  s4, s2, s4
    li   s5, P_SCLAIM
    add  s5, s2, s5
    li   s6, P_STHRESH
    add  s6, s2, s6

    li   t0, 3
    sw   t0, 40(s2)                  /* prio[10] = 3 */
    li   t0, 3
    sw   t0, 0(s6)                   /* threshold = 3, i.e. EQUAL */
    li   t1, P_SENABLE
    add  t1, s2, t1
    li   t0, 0x400
    sw   t0, 0(t1)                   /* enable source 10 */

/* ---- raise source 10: IER bit 1 (THRE) with DLAB clear ---- */
    li   t0, 3
    sb   t0, 3(s3)                   /* LCR = 8N1, DLAB clear */
    li   t0, 2
    sb   t0, 1(s3)
/* the gateway latch is the DEVICE's own step, not a side effect of the
   completing MMIO write, so SPIN rather than reading once */
1:  lw   t0, 0(s4)
    andi t6, t0, 0x400
    beqz t6, 1b
    sw   t0, R_PEND0(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- (a) the threshold gates the notification, strictly ---- */
    csrr t0, mip
    andi t0, t0, 0x200               /* SEIP only: the harness steps
                                        riscv_step with the clock tick off,
                                        so MTIP would diverge for a reason
                                        that has nothing to do with the PLIC */
    sw   t0, R_MIPEQ(s11)            /* == : masked */
    li   t0, 2
    sw   t0, 0(s6)                   /* threshold 2 < priority 3 */
    csrr t0, mip
    andi t0, t0, 0x200
    sw   t0, R_MIPLT(s11)            /* <  : through */
    li   t0, 3
    sw   t0, 0(s6)                   /* back to equal */
    csrr t0, mip
    andi t0, t0, 0x200
    sw   t0, R_MIPEQ2(s11)           /* == : masked again */
    li   t0, 2
    sw   t0, RES_STATUS(s11)

/* ---- (b) ...and it is supposed to gate the CLAIM too ---- */
    lw   t0, 0(s5)
    sw   t0, R_CLAIM1(s11)
    lw   t0, 0(s4)
    sw   t0, R_PEND1(s11)

    sw   zero, 0(s6)                 /* threshold 0: nothing is masked now */
    csrr t0, mip
    andi t0, t0, 0x200
    sw   t0, R_MIP0(s11)
    lw   t0, 0(s5)
    sw   t0, R_CLAIM2(s11)
    lw   t0, 0(s4)
    sw   t0, R_PEND2(s11)
    lw   t0, 0(s6)
    sw   t0, R_THRESH(s11)

    li   t0, 3
    sw   t0, RES_STATUS(s11)
    mv   ra, s10
    ret
