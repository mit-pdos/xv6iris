/* plic_arb -- ARBITRATION between TWO sources at DIFFERENT priorities.
 *
 * The PLIC as SUBJECT, not as the disk's plumbing.  disk_intr only ever has
 * one source up, at priority 1, with threshold 0, so nothing in the suite
 * had ever exercised [plic_best]/[plic_better] -- the fold that picks the
 * winner -- nor the pending WORD with more than one bit in it.
 *
 * Two sources, and they are the only two this machine has: the virtio disk
 * (source 1, raised by completing a write request, as disk_intr does) and
 * the 16550 (source 10, raised with NO serial input at all by enabling the
 * transmit-holding-register-empty interrupt in IER while the FIFO is empty).
 * The disk is given the LOWER priority and the LOWER id, so the claim order
 * 10-then-1 can only come from the priority comparison: an implementation
 * that scanned ids in order, or that ignored priority, would answer 1 first.
 *
 * NOTHING IS EVER COMPLETED here.  A completed source whose level is still
 * asserted is a separate question with a divergence of its own -- see
 * plic_level -- and keeping it out of this test keeps this test's subject
 * to arbitration alone.
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

#define VDESC   0x000
#define VAVAIL  0x100
#define VUSED   0x200
#define VHDR    0x300
#define VST     0x340
#define VBUF    0x400
#define SECTOR  7

/* result-region offsets -- MIRRORED in vtest-rocq/PlicArb.v */
#define R_PEND0   8    /* pending, before anything                   0     */
#define R_PENDU   12   /* pending, after the UART line rises         0x400 */
#define R_WSTAT   16   /* the disk request's status byte             0     */
#define R_PEND1   20   /* pending, BOTH sources up                   0x402 */
#define R_MIP1    24   /* mip & SEIP                                 0x200 */
#define R_CLAIM1  28   /* first claim  -- the HIGHER PRIORITY one    10    */
#define R_PEND2   32   /* pending after it                          0x002  */
#define R_MIP2    36   /* mip & SEIP (source 1 still above thresh)  0x200  */
#define R_CLAIM2  40   /* second claim                               1     */
#define R_PEND3   44   /* pending after it                           0     */
#define R_MIP3    48   /* mip & SEIP                                 0     */
#define R_CLAIM3  52   /* third claim -- nothing pending             0     */
#define R_PRIO1   56   /* prio[1]   read back                        3     */
#define R_PRIO10  60   /* prio[10]  read back                        7     */
#define R_ENAB    64   /* the S-context enable word read back       0x402  */
#define R_THRESH  68   /* the S-context threshold read back          0     */

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
    li   s0, VIRTIO0
    li   s1, DMA_BASE
    li   s2, PLIC
    li   s3, UART0
    li   s4, P_PENDING
    add  s4, s2, s4
    li   s5, P_SCLAIM
    add  s5, s2, s5

/* ---- PLIC: source 1 at priority 3, source 10 at priority 7 ---- */
    li   t0, 3
    sw   t0, 4(s2)                   /* prio[1]  = 3  (virtio disk) */
    li   t0, 7
    sw   t0, 40(s2)                  /* prio[10] = 7  (16550)       */
    li   t1, P_STHRESH
    add  t1, s2, t1
    sw   zero, 0(t1)                 /* threshold 0: both get through */
    li   t1, P_SENABLE
    add  t1, s2, t1
    li   t0, 0x402                   /* enable sources 1 and 10 */
    sw   t0, 0(t1)

    lw   t0, 0(s4)
    sw   t0, R_PEND0(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- raise source 10: IER bit 1 (THRE) with DLAB clear ---- */
    li   t0, 3
    sb   t0, 3(s3)                   /* LCR = 8N1, DLAB clear */
    li   t0, 2
    sb   t0, 1(s3)                   /* IER = THRE; the FIFO is empty, so the
                                        line goes high with no serial input */
/* the gateway latch is the DEVICE's own step, not a side effect of the
   completing MMIO write, so SPIN rather than reading once */
1:  lw   t0, 0(s4)
    andi t6, t0, 0x400
    beqz t6, 1b
    sw   t0, R_PENDU(s11)
    li   t0, 2
    sw   t0, RES_STATUS(s11)

/* ---- device bring-up ---- */
    sw   zero, 0x70(s0)
    li   t0, 1
    sw   t0, 0x70(s0)
    li   t0, 3
    sw   t0, 0x70(s0)
    lw   t0, 0x10(s0)
    li   t1, 0x38001AA0
    not  t1, t1
    and  t0, t0, t1
    sw   t0, 0x20(s0)
    li   t0, 11
    sw   t0, 0x70(s0)
    sw   zero, 0x30(s0)
    li   t0, 8
    sw   t0, 0x38(s0)
    mv   t0, s1
    sw   t0, 0x80(s0)
    srli t1, t0, 32
    sw   t1, 0x84(s0)
    addi t0, s1, VAVAIL
    sw   t0, 0x90(s0)
    srli t1, t0, 32
    sw   t1, 0x94(s0)
    addi t0, s1, VUSED
    sw   t0, 0xa0(s0)
    srli t1, t0, 32
    sw   t1, 0xa4(s0)
    li   t0, 1
    sw   t0, 0x44(s0)
    li   t0, 15
    sw   t0, 0x70(s0)

/* ---- one WRITE request, so the disk raises source 1 ---- */
    li   t4, 0xc0ffee0000000007
    addi t0, s1, VBUF
    sd   t4, 0(t0)
    addi t0, s1, VHDR
    li   t1, 1                       /* VIRTIO_BLK_T_OUT */
    sw   t1, 0(t0)
    sw   zero, 4(t0)
    li   t1, SECTOR
    sd   t1, 8(t0)
    mv   t2, s1
    addi t3, s1, VHDR
    sd   t3, 0(t2)
    li   t4, 16
    sw   t4, 8(t2)
    li   t4, 1
    sh   t4, 12(t2)
    li   t4, 1
    sh   t4, 14(t2)
    addi t3, s1, VBUF
    sd   t3, 16(t2)
    li   t4, 512
    sw   t4, 24(t2)
    li   t4, 1
    sh   t4, 28(t2)
    li   t4, 2
    sh   t4, 30(t2)
    addi t3, s1, VST
    sd   t3, 32(t2)
    li   t4, 1
    sw   t4, 40(t2)
    li   t4, 2
    sh   t4, 44(t2)
    sh   zero, 46(t2)

    addi t2, s1, VAVAIL
    sh   zero, 4(t2)
    fence
    li   t4, 1
    sh   t4, 2(t2)
    fence
    sw   zero, 0x50(s0)

    addi t3, s1, VUSED
2:  lhu  t4, 2(t3)
    beqz t4, 2b

    addi t5, s1, VST
    lbu  t6, 0(t5)
    sw   t6, R_WSTAT(s11)

/* ---- both lines are up: spin until BOTH pending bits are in ---- */
3:  lw   t0, 0(s4)
    andi t6, t0, 0x402
    li   t5, 0x402
    bne  t6, t5, 3b
    sw   t0, R_PEND1(s11)
    csrr t0, mip
    andi t0, t0, 0x200               /* SEIP only: the harness steps
                                        riscv_step with the clock tick off,
                                        so MTIP would diverge for a reason
                                        that has nothing to do with the PLIC */
    sw   t0, R_MIP1(s11)
    li   t0, 3
    sw   t0, RES_STATUS(s11)

/* ---- the arbitration itself: three claims, no completes ---- */
    lw   t0, 0(s5)
    sw   t0, R_CLAIM1(s11)           /* priority 7 beats priority 3 */
    lw   t0, 0(s4)
    sw   t0, R_PEND2(s11)
    csrr t0, mip
    andi t0, t0, 0x200
    sw   t0, R_MIP2(s11)

    lw   t0, 0(s5)
    sw   t0, R_CLAIM2(s11)
    lw   t0, 0(s4)
    sw   t0, R_PEND3(s11)
    csrr t0, mip
    andi t0, t0, 0x200
    sw   t0, R_MIP3(s11)

    lw   t0, 0(s5)
    sw   t0, R_CLAIM3(s11)           /* nothing pending -> 0 */

/* ---- the configuration registers read back ---- */
    lw   t0, 4(s2)
    sw   t0, R_PRIO1(s11)
    lw   t0, 40(s2)
    sw   t0, R_PRIO10(s11)
    li   t1, P_SENABLE
    add  t1, s2, t1
    lw   t0, 0(t1)
    sw   t0, R_ENAB(s11)
    li   t1, P_STHRESH
    add  t1, s2, t1
    lw   t0, 0(t1)
    sw   t0, R_THRESH(s11)

    li   t0, 4
    sw   t0, RES_STATUS(s11)
    mv   ra, s10
    ret
