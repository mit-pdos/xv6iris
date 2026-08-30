/* plic_thresh -- the CONTEXT THRESHOLD: it gates the NOTIFICATION and the
 * CLAIM, and both strictly.
 *
 * This program walks one source (the 16550 on source 10, raised with no
 * serial input by enabling the THRE interrupt while the FIFO is empty) at
 * priority 3 past thresholds 3, 2, 3, and then claims while masked.
 *
 * IT USED TO BE THIS AREA'S ONE NON-INCOMPLETENESS (finding 10).
 * [plic_claim] went through [plic_best]/[plic_cand], which never looked at
 * [p_thresh] at all, so the model handed back the id of a source the context
 * could not see and cleared its pending bit on the way out -- a value the
 * hardware never produces, and the hardware's answer (0, source still
 * pending) had no model execution.  The threshold now lives in [plic_cand],
 * which the notification and the claim both read, so the two agree by
 * construction and every field below agrees with the machine.
 *
 */
/* QEMU ONLY, and the reason is MEASURED, not assumed.  This case drives an
   interrupt through the PLIC, so it needs a source it can RAISE AND LOWER --
   and the only one a test can drive is the UART.  On QEMU (and in the model,
   DevModel.uart_irq_id) that is source 10; on the JH7110 it is source 32,
   confirmed over JTAG: asserting IER made source 32 claimable while source
   10 was never pending.  One image cannot satisfy both, and the model's
   device fabric has its UART at 10, so the board's execution is not one the
   model can exhibit -- the run would burn its whole budget waiting for an
   interrupt that never arrives.

   This is finding 30's sibling: the board's UART is a different chip AND it
   sits on a different PLIC source.  The PLIC itself is fine on this board --
   plic_mctx and plic_prio0 exercise its registers there and pass.  What is
   QEMU-specific is this test, not the question, and a board-shaped version
   driving source 32 would be a new case rather than a platform of this one.

   (The context numbering is handled and verified separately -- see
   PLIC_SCTX in abi.h.  There are exactly 9 contexts on this PLIC, measured:
   0..8 can claim, 9 cannot, which is the E24's M-only context followed by
   four U74s with an M and an S each.) */
/* vtest: repeat=1 platforms=qemu */
#include "abi.h"

#define PLIC        0x0c000000
#define P_PENDING   0x1000
#define P_SENABLE   PLIC_SENABLE
#define P_STHRESH   PLIC_STHRESH
#define P_SCLAIM    PLIC_SCLAIM

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
