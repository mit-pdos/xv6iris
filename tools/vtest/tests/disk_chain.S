/* disk_chain -- A CHAIN THAT IS NOT EXACTLY THREE DESCRIPTORS.
 *
 * [VirtioModel.chain_at] accepts one shape and one only: d0 with NEXT, d1
 * with NEXT, d2 WITHOUT.  Anything else is None, so [req_at] is None,
 * [virtio_req_step] and [virtio_capture_step] are both None, and
 * [virtio_stalled] is true: the device owes the driver a completion it can
 * never produce.  The guest's poll loop then spins forever, so the model
 * side runs out of BUDGET rather than getting STUCK -- a different failure
 * from the disk_ident_* programs and worth telling apart.
 *
 * Nothing about the chain is illegal.  Splitting a 512-byte payload across
 * two data descriptors is ordinary scatter-gather -- it is what a driver
 * does when its buffer is not physically contiguous -- and QEMU serves it
 * normally: 512 bytes land on sector 7, status OK, one used-ring entry.
 *
 * The chain, four descriptors:
 *   desc[0]  header, 16 bytes, NEXT -> 1
 *   desc[1]  first  256 bytes of the payload, NEXT -> 2
 *   desc[2]  second 256 bytes of the payload, NEXT -> 3   <== the extra one
 *   desc[3]  status byte, WRITE, end of chain
 */
#include "abi.h"

/* offsets within the DMA region */
#define VDESC   0x000
#define VAVAIL  0x100
#define VUSED   0x200
#define VHDR0   0x300
#define VST0    0x340
#define VWBUF   0x400          /* 512 bytes, split 256 + 256 */

#define SECTOR  7

/* result-region offsets (mirrored in vtest-rocq/DiskChain.v) */
#define R_STAT      8          /* the request's status byte */
#define R_ID        12         /* used.ring[0].id */
#define R_LEN       16         /* used.ring[0].len */
#define R_UIDX      20         /* used.idx */
#define R_ISR       24         /* InterruptStatus */

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
    li   s0, VIRTIO0
    li   s1, DMA_BASE

/* ---- 1. bring the device up (kernel/virtio_disk.c's sequence) ---- */
    sw   zero, 0x70(s0)              /* Status = 0: reset */
    li   t0, 1                       /* ACKNOWLEDGE */
    sw   t0, 0x70(s0)
    li   t0, 3                       /* | DRIVER */
    sw   t0, 0x70(s0)
    lw   t0, 0x10(s0)                /* DeviceFeatures */
    li   t1, 0x38001AA0              /* what xv6 clears */
    not  t1, t1
    and  t0, t0, t1
    sw   t0, 0x20(s0)                /* DriverFeatures */
    li   t0, 11                      /* | FEATURES_OK */
    sw   t0, 0x70(s0)
    sw   zero, 0x30(s0)              /* QueueSel = 0 */
    li   t0, 8
    sw   t0, 0x38(s0)                /* QueueNum = 8 */
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
    sw   t0, 0x44(s0)                /* QueueReady = 1 */
    li   t0, 15                      /* | DRIVER_OK */
    sw   t0, 0x70(s0)

/* ---- 2. the payload: 64 distinct doublewords ---- */
    addi t0, s1, VWBUF
    li   t1, 0x1122334455667700
    li   t2, 0
1:  slli t3, t2, 3
    add  t5, t0, t3
    add  t4, t1, t2
    sd   t4, 0(t5)
    addi t2, t2, 1
    li   t3, 64
    blt  t2, t3, 1b

/* ---- 3. the FOUR-descriptor chain ---- */
    addi t0, s1, VHDR0
    li   t1, 1                       /* VIRTIO_BLK_T_OUT */
    sw   t1, 0(t0)
    sw   zero, 4(t0)
    li   t1, SECTOR
    sd   t1, 8(t0)

    mv   t2, s1                      /* &desc[0] */
    addi t3, s1, VHDR0
    sd   t3, 0(t2)                   /* desc[0].addr  = header */
    li   t4, 16
    sw   t4, 8(t2)
    li   t4, 1
    sh   t4, 12(t2)                  /* NEXT */
    li   t4, 1
    sh   t4, 14(t2)                  /* -> desc[1] */

    addi t3, s1, VWBUF
    sd   t3, 16(t2)                  /* desc[1].addr = payload[0..256) */
    li   t4, 256
    sw   t4, 24(t2)
    li   t4, 1
    sh   t4, 28(t2)                  /* NEXT */
    li   t4, 2
    sh   t4, 30(t2)                  /* -> desc[2] */

    addi t3, s1, VWBUF + 256
    sd   t3, 32(t2)                  /* desc[2].addr = payload[256..512) */
    li   t4, 256
    sw   t4, 40(t2)
    li   t4, 1
    sh   t4, 44(t2)                  /* NEXT -- THE DESCRIPTOR chain_at REFUSES */
    li   t4, 3
    sh   t4, 46(t2)                  /* -> desc[3] */

    addi t3, s1, VST0
    sd   t3, 48(t2)                  /* desc[3].addr = status byte */
    li   t4, 1
    sw   t4, 56(t2)
    li   t4, 2
    sh   t4, 60(t2)                  /* WRITE, end of chain */
    sh   zero, 62(t2)

    addi t2, s1, VAVAIL
    sh   zero, 4(t2)                 /* avail.ring[0] = 0 */
    fence
    li   t4, 1
    sh   t4, 2(t2)                   /* avail.idx = 1 -- publishes it */
    fence
    li   t0, 1
    sw   t0, RES_STATUS(s11)         /* progress: published */
    sw   zero, 0x50(s0)              /* QueueNotify = 0 */

/* ---- 4. poll for the completion.  QEMU produces one; the MODEL never can,
          so on the model this loop is where the budget runs out. ---- */
    addi t3, s1, VUSED
2:  lhu  t4, 2(t3)
    beqz t4, 2b

    addi t5, s1, VST0
    lbu  t6, 0(t5)
    sw   t6, R_STAT(s11)
    lw   t4, 4(t3)                   /* used.ring[0].id */
    sw   t4, R_ID(s11)
    lw   t4, 8(t3)                   /* used.ring[0].len */
    sw   t4, R_LEN(s11)
    lhu  t4, 2(t3)
    sw   t4, R_UIDX(s11)
    lw   t4, 0x60(s0)                /* InterruptStatus */
    sw   t4, R_ISR(s11)
    li   t4, 3
    sw   t4, 0x64(s0)                /* InterruptACK */
    li   t0, 2
    sw   t0, RES_STATUS(s11)

    mv   ra, s10
    ret
