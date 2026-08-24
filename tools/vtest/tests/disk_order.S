/* disk_order -- TWO requests published in ONE batch, and who finishes first.
 *
 * The model serves the available ring strictly in order: [virtio_req_step]
 * reads the chain at position [v_seen] and advances [v_seen] by one, so the
 * used ring can only ever come out in publication order.  A real virtio-blk
 * has no such obligation -- the used element carries the descriptor id
 * precisely so the driver can cope with completions arriving in any order,
 * and xv6's own virtio_disk_intr reads that id rather than assuming.
 *
 * So this test publishes two requests at once, deliberately LOPSIDED: A is
 * eight sectors at 100, B is one sector at 5, both in one notify.  If a
 * backend ever lets the small one overtake the large one, it shows up here
 * as used.ring[0].id = 3 instead of 0 -- an execution the model cannot
 * produce at all.  Run it with `vtest.py run t5_order --repeat N
 * --drive-opts aio=threads` to hunt for it.
 *
 * Only the first doubleword of each written sector is filled: enough for the
 * disk diff to see every one of the nine sectors, without a 4096-iteration
 * fill loop the model would have to execute instruction by instruction.
 */
/* vtest: repeat=20 drives=cache=writeback;cache=none,aio=threads */
#include "abi.h"

#define VDESC   0x000
#define VAVAIL  0x100
#define VUSED   0x200
#define VHDRA   0x300
#define VHDRB   0x320
#define VSTA    0x340
#define VSTB    0x341
#define VBUFA   0x400          /* 4096 bytes: sectors 100..107 */
#define VBUFB   0x1400         /* 512 bytes:  sector 5 */

#define SECTA   100
#define SECTB   5

#define R_AID    8
#define R_ALEN   12
#define R_BID    16
#define R_BLEN   20
#define R_ASTAT  24
#define R_BSTAT  28
#define R_UIDX   32
#define R_ISR    36

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
    li   s0, VIRTIO0
    li   s1, DMA_BASE

/* ---- device bring-up (identical to t2_rw) ---- */
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
    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- fill: one distinct doubleword per sector ---- */
    li   t1, 0xa000000000000000
    addi t0, s1, VBUFA
    li   t2, 0
1:  slli t3, t2, 9                   /* i * 512 */
    add  t5, t0, t3
    add  t4, t1, t2
    sd   t4, 0(t5)
    addi t2, t2, 1
    li   t3, 8
    blt  t2, t3, 1b
    li   t4, 0xb000000000000005
    li   t0, VBUFB                   /* > 2047: too big for addi's immediate */
    add  t0, s1, t0
    sd   t4, 0(t0)

/* ---- request A: eight sectors at 100, descriptors 0,1,2 ---- */
    addi t0, s1, VHDRA
    li   t1, 1                       /* VIRTIO_BLK_T_OUT */
    sw   t1, 0(t0)
    sw   zero, 4(t0)
    li   t1, SECTA
    sd   t1, 8(t0)
    mv   t2, s1
    addi t3, s1, VHDRA
    sd   t3, 0(t2)
    li   t4, 16
    sw   t4, 8(t2)
    li   t4, 1
    sh   t4, 12(t2)
    li   t4, 1
    sh   t4, 14(t2)
    addi t3, s1, VBUFA
    sd   t3, 16(t2)
    li   t4, 4096                    /* EIGHT sectors */
    sw   t4, 24(t2)
    li   t4, 1
    sh   t4, 28(t2)
    li   t4, 2
    sh   t4, 30(t2)
    addi t3, s1, VSTA
    sd   t3, 32(t2)
    li   t4, 1
    sw   t4, 40(t2)
    li   t4, 2
    sh   t4, 44(t2)
    sh   zero, 46(t2)

/* ---- request B: one sector at 5, descriptors 3,4,5 ---- */
    addi t0, s1, VHDRB
    li   t1, 1
    sw   t1, 0(t0)
    sw   zero, 4(t0)
    li   t1, SECTB
    sd   t1, 8(t0)
    addi t2, s1, 48
    addi t3, s1, VHDRB
    sd   t3, 0(t2)
    li   t4, 16
    sw   t4, 8(t2)
    li   t4, 1
    sh   t4, 12(t2)
    li   t4, 4
    sh   t4, 14(t2)
    li   t3, VBUFB
    add  t3, s1, t3
    sd   t3, 16(t2)
    li   t4, 512
    sw   t4, 24(t2)
    li   t4, 1
    sh   t4, 28(t2)
    li   t4, 5
    sh   t4, 30(t2)
    addi t3, s1, VSTB
    sd   t3, 32(t2)
    li   t4, 1
    sw   t4, 40(t2)
    li   t4, 2
    sh   t4, 44(t2)
    sh   zero, 46(t2)

/* ---- publish BOTH, then one notify ---- */
    addi t2, s1, VAVAIL
    sh   zero, 4(t2)                 /* avail.ring[0] = 0  (A) */
    li   t4, 3
    sh   t4, 6(t2)                   /* avail.ring[1] = 3  (B) */
    fence
    li   t4, 2
    sh   t4, 2(t2)                   /* avail.idx = 2 */
    fence
    sw   zero, 0x50(s0)

    addi t3, s1, VUSED
2:  lhu  t4, 2(t3)
    li   t5, 2
    bltu t4, t5, 2b

/* ---- record the ORDER: which id landed in which used slot ---- */
    lw   t4, 4(t3)                   /* used.ring[0].id  */
    sw   t4, R_AID(s11)
    lw   t4, 8(t3)                   /* used.ring[0].len */
    sw   t4, R_ALEN(s11)
    lw   t4, 12(t3)                  /* used.ring[1].id  */
    sw   t4, R_BID(s11)
    lw   t4, 16(t3)                  /* used.ring[1].len */
    sw   t4, R_BLEN(s11)
    addi t5, s1, VSTA
    lbu  t6, 0(t5)
    sw   t6, R_ASTAT(s11)
    addi t5, s1, VSTB
    lbu  t6, 0(t5)
    sw   t6, R_BSTAT(s11)
    lhu  t4, 2(t3)
    sw   t4, R_UIDX(s11)
    lw   t4, 0x60(s0)
    sw   t4, R_ISR(s11)
    li   t4, 3
    sw   t4, 0x64(s0)
    li   t0, 2
    sw   t0, RES_STATUS(s11)

    mv   ra, s10
    ret
