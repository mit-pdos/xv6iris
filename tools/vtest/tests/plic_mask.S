/* plic_mask -- the ENABLE bit, and the two degenerate accesses.
 *
 * Three things disk_intr never does, all of them cheap enough to share one
 * program because none of them disturbs the others:
 *
 *   - a CLAIM WHEN NOTHING IS PENDING must return 0 and change nothing;
 *   - a COMPLETE of a source that was never CLAIMED must be a no-op -- in
 *     particular it must NOT clear that source's PENDING bit, which is a
 *     different bit ([DevModel.plic_complete] touches [p_claimed] alone);
 *   - the ENABLE bit is not the gateway.  A source whose enable bit is clear
 *     still becomes PENDING (the gateway does not consult the context), but
 *     it drives no notification and a claim must not return it.  Setting the
 *     bit afterwards makes the already-latched request claimable with no
 *     new edge from the device.
 *
 * One source, the cheap one: the 16550 at source 10, raised with NO serial
 * input by enabling the transmit-holding-register-empty interrupt in IER
 * while the FIFO is empty.  No virtqueue, so the model side declares only
 * the stack and the result region.
 */
/* vtest: repeat=1 */
#include "abi.h"

#define PLIC        0x0c000000
#define P_PENDING   0x1000
#define P_SENABLE   0x2080          /* hart 0, S context */
#define P_STHRESH   0x201000
#define P_SCLAIM    0x201004

/* result-region offsets -- MIRRORED in vtest-rocq/PlicMask.v */
#define R_CLAIM0   8   /* claim with nothing pending                 0     */
#define R_PENDC    12  /* pending after completing an unclaimed src  0     */
#define R_PEND0    16  /* pending, source up but NOT enabled        0x400  */
#define R_MIP0     20  /* mip & SEIP -- no notification              0     */
#define R_CLAIM1   24  /* claim, source not enabled                  0     */
#define R_PEND1    28  /* pending -- the claim took nothing         0x400  */
#define R_PEND2    32  /* pending after complete(10), never claimed 0x400  */
#define R_MIP1     36  /* mip & SEIP once the enable bit is set     0x200  */
#define R_CLAIM2   40  /* claim, now enabled                         10    */
#define R_PEND3    44  /* pending after it                           0     */
#define R_MIP2     48  /* mip & SEIP                                 0     */
#define R_ENAB     52  /* the S-context enable word read back       0x400  */

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
    li   s3, UART0
    li   s2, PLIC
    li   s4, P_PENDING
    add  s4, s2, s4
    li   s5, P_SCLAIM
    add  s5, s2, s5
    li   s6, P_SENABLE
    add  s6, s2, s6
    li   s7, P_STHRESH
    add  s7, s2, s7

    li   t0, 7
    sw   t0, 40(s2)                  /* prio[10] = 7 */
    sw   zero, 0(s7)                 /* threshold 0 */
    /* the enable word is left at its reset value: source 10 is NOT enabled */

/* ---- the two degenerate accesses, on a quiescent PLIC ---- */
    lw   t0, 0(s5)
    sw   t0, R_CLAIM0(s11)           /* claim, nothing pending */
    li   t0, 5
    sw   t0, 0(s5)                   /* complete source 5, never claimed */
    lw   t0, 0(s4)
    sw   t0, R_PENDC(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- raise source 10: IER bit 1 (THRE) with DLAB clear ---- */
    li   t0, 3
    sb   t0, 3(s3)                   /* LCR = 8N1, DLAB clear */
    li   t0, 2
    sb   t0, 1(s3)
/* the gateway latch is the DEVICE's own step, not a side effect of the
   completing MMIO write, so SPIN rather than reading once.  The gateway does
   not consult the context, so this bit appears even though the source is
   masked at the enable word. */
1:  lw   t0, 0(s4)
    andi t6, t0, 0x400
    beqz t6, 1b
    sw   t0, R_PEND0(s11)
    csrr t0, mip
    andi t0, t0, 0x200               /* SEIP only: the harness steps
                                        riscv_step with the clock tick off,
                                        so MTIP would diverge for a reason
                                        that has nothing to do with the PLIC */
    sw   t0, R_MIP0(s11)
    lw   t0, 0(s5)
    sw   t0, R_CLAIM1(s11)           /* not enabled -> not claimable */
    lw   t0, 0(s4)
    sw   t0, R_PEND1(s11)
    li   t0, 10
    sw   t0, 0(s5)                   /* complete 10: pending, never claimed */
    lw   t0, 0(s4)
    sw   t0, R_PEND2(s11)            /* ...and pending is a DIFFERENT bit */
    li   t0, 2
    sw   t0, RES_STATUS(s11)

/* ---- enable it: the already-latched request becomes claimable ---- */
    li   t0, 0x400
    sw   t0, 0(s6)
    sw   zero, 0(s7)                 /* re-write the threshold with the value
                                        it already has.  QEMU's PLIC does not
                                        recompute a context's notification
                                        level on an ENABLE write -- its
                                        sifive_plic_write returns without
                                        calling sifive_plic_update -- so
                                        without this the pin would lag by one
                                        register access on QEMU and not on
                                        the model, for a reason that has
                                        nothing to do with the enable bit
                                        this test is about.  The value is
                                        unchanged, so on the model side this
                                        write moves nothing. */
    csrr t0, mip
    andi t0, t0, 0x200
    sw   t0, R_MIP1(s11)
    lw   t0, 0(s5)
    sw   t0, R_CLAIM2(s11)
    lw   t0, 0(s4)
    sw   t0, R_PEND3(s11)
    csrr t0, mip
    andi t0, t0, 0x200
    sw   t0, R_MIP2(s11)
    lw   t0, 0(s6)
    sw   t0, R_ENAB(s11)

    li   t0, 3
    sw   t0, RES_STATUS(s11)
    mv   ra, s10
    ret
