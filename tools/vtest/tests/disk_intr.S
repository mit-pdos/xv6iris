/* disk_intr -- the INTERRUPT PATH, end to end: the disk raises its line, the
 * PLIC gateway latches it, the wire drives hart 0's external pin, the driver
 * claims, acknowledges and completes, and the line drops.
 *
 * Nothing in the suite had touched this before.  It is four model components
 * that only ever appear together -- [virtio_irq] (ISR nonzero => line high),
 * [dev_irq_level] (which device drives which source), [plic_latch] (the
 * per-source gateway) and [plic_step] (the wire onto sig_seip, which the
 * model deliberately makes a SEPARATE step from the MMIO write that caused
 * it, so the pin has propagation delay).  Two of VSched's schedule arms,
 * SLatch and SWire, existed for this and had never been driven.
 *
 * It takes no trap: everything here is observable by polling, so the test
 * stays inside the same M-mode straight-line shape as the others.  mip is
 * read as a cross-check -- bit 9, SEIP, is the pin the wire drives.
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

#define R_PEND0   8    /* PLIC pending, before any request         */
#define R_ISR1    12   /* virtio InterruptStatus, after completion */
#define R_PEND1   16   /* PLIC pending, after completion           */
#define R_MIP1    20   /* mip, after completion                    */
#define R_CLAIM   24   /* what the claim register returned         */
#define R_PEND2   28   /* PLIC pending, after the claim            */
#define R_MIP2    32   /* mip, after the claim                     */
#define R_ISR2    36   /* virtio InterruptStatus, after the ack    */
#define R_PEND3   40   /* PLIC pending, after complete             */
#define R_MIP3    44   /* mip, at the end                          */
#define R_WSTAT   48   /* the request's status byte                */

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
    li   s0, VIRTIO0
    li   s1, DMA_BASE
    li   s2, PLIC

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

/* ---- PLIC: source 1 (VIRTIO0) routed to hart 0's S context ---- */
    li   t0, 1
    sw   t0, 4(s2)                   /* source 1 priority = 1 */
    li   t1, P_SENABLE
    add  t1, s2, t1
    li   t0, 2                       /* bit 1 */
    sw   t0, 0(t1)
    li   t1, P_STHRESH
    add  t1, s2, t1
    sw   zero, 0(t1)                 /* threshold 0: priority 1 gets through */

    li   t1, P_PENDING
    add  t1, s2, t1
    lw   t0, 0(t1)
    sw   t0, R_PEND0(s11)            /* nothing pending yet */
    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- one WRITE request, so the device raises its line ---- */
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
1:  lhu  t4, 2(t3)
    beqz t4, 1b

    addi t5, s1, VST
    lbu  t6, 0(t5)
    sw   t6, R_WSTAT(s11)

/* ---- the line is up: ISR, PLIC pending, and the pin ---- */
/* The gateway latch and the wire are the DEVICE's own steps, not side
 * effects of the completion, so spin until the pending bit appears rather
 * than reading once -- exactly what a driver must do against real hardware,
 * and what makes the model's propagation delay observable rather than
 * assumed away. */
    li   t1, P_PENDING
    add  t1, s2, t1
2:  lw   t0, 0(t1)
    andi t0, t0, 2
    beqz t0, 2b

    lw   t0, 0x60(s0)
    sw   t0, R_ISR1(s11)
    lw   t0, 0(t1)
    sw   t0, R_PEND1(s11)
    csrr t0, mip
    andi t0, t0, 0x200               /* SEIP only: mip also carries MTIP, and
                                        the harness steps riscv_step with the
                                        clock tick off, so the timer bit would
                                        diverge for a reason that has nothing
                                        to do with the device */
    sw   t0, R_MIP1(s11)
    li   t0, 2
    sw   t0, RES_STATUS(s11)

/* ---- claim ---- */
    li   t2, P_SCLAIM
    add  t2, s2, t2
    lw   t0, 0(t2)
    sw   t0, R_CLAIM(s11)
    lw   t0, 0(t1)
    sw   t0, R_PEND2(s11)
    csrr t0, mip
    andi t0, t0, 0x200               /* SEIP only: mip also carries MTIP, and
                                        the harness steps riscv_step with the
                                        clock tick off, so the timer bit would
                                        diverge for a reason that has nothing
                                        to do with the device */
    sw   t0, R_MIP2(s11)

/* ---- acknowledge the device, then complete at the PLIC ---- */
    li   t0, 3
    sw   t0, 0x64(s0)                /* InterruptACK: drops the line */
    lw   t0, 0x60(s0)
    sw   t0, R_ISR2(s11)
    li   t0, 1
    sw   t0, 0(t2)                   /* PLIC complete, source 1 */
    lw   t0, 0(t1)
    sw   t0, R_PEND3(s11)
    csrr t0, mip
    andi t0, t0, 0x200               /* SEIP only: mip also carries MTIP, and
                                        the harness steps riscv_step with the
                                        clock tick off, so the timer bit would
                                        diverge for a reason that has nothing
                                        to do with the device */
    sw   t0, R_MIP3(s11)
    li   t0, 3
    sw   t0, RES_STATUS(s11)

    mv   ra, s10
    ret
