/* disk_rw -- one virtqueue, one WRITE request, one READ request.
 *
 * The first test that makes the device do work.  It brings the device up the
 * way kernel/virtio_disk.c does, writes a known pattern to sector 5, then
 * reads sector 5 back -- and the READ's data descriptor points INTO THE
 * RESULT REGION, so the bytes the device DMAs are compared directly with no
 * copy loop in between, which also checks that a DMA write lands where the
 * CPU can see it.
 *
 * Both observation channels are exercised: the result region (request status
 * bytes, used-ring entries, interrupt status, the data read back) and the
 * disk image itself (sector 5 must hold the pattern).
 */
#include "abi.h"

/* offsets within the DMA region */
#define VDESC   0x000          /* 8 descriptors, 16 bytes each */
#define VAVAIL  0x100          /* flags:2 idx:2 ring[8]:2 each */
#define VUSED   0x200          /* flags:2 idx:2 ring[8]:8 each */
#define VHDR0   0x300          /* write request header */
#define VHDR1   0x320          /* read request header */
#define VST0    0x340          /* write request status byte */
#define VST1    0x341          /* read request status byte */
#define VWBUF   0x400          /* 512-byte source buffer */

/* the READ lands here, inside the RESULT region */
#define RBUF    0x200

#define SECTOR  5

/* result-region offsets (mirrored in vtest-rocq/T2Rw.v) */
#define R_QNUMMAX   8
#define R_STATUS    12
#define R_FEATURES  16
#define R_WSTAT     20
#define R_WIDX      24
#define R_WID       28
#define R_WLEN      32
#define R_WISR      36
#define R_RSTAT     40
#define R_RIDX      44
#define R_RID       48
#define R_RLEN      52
#define R_RISR      56

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
    li   t1, 0x38001AA0              /* RO|SCSI|FLUSH|CONFIG_WCE|MQ|ANY_LAYOUT
                                        |INDIRECT_DESC|EVENT_IDX -- what xv6 clears */
    not  t1, t1
    and  t0, t0, t1
    sw   t0, R_FEATURES(s11)         /* what we negotiated */
    sw   t0, 0x20(s0)                /* DriverFeatures */
    li   t0, 11                      /* | FEATURES_OK */
    sw   t0, 0x70(s0)
    lw   t0, 0x70(s0)                /* it must have stuck */
    sw   t0, R_STATUS(s11)
    sw   zero, 0x30(s0)              /* QueueSel = 0 */
    lw   t0, 0x34(s0)                /* QueueNumMax */
    sw   t0, R_QNUMMAX(s11)
    li   t0, 8
    sw   t0, 0x38(s0)                /* QueueNum = 8 */
    mv   t0, s1                      /* descriptor table */
    sw   t0, 0x80(s0)
    srli t1, t0, 32
    sw   t1, 0x84(s0)
    addi t0, s1, VAVAIL              /* available ring (driver -> device) */
    sw   t0, 0x90(s0)
    srli t1, t0, 32
    sw   t1, 0x94(s0)
    addi t0, s1, VUSED               /* used ring (device -> driver) */
    sw   t0, 0xa0(s0)
    srli t1, t0, 32
    sw   t1, 0xa4(s0)
    li   t0, 1
    sw   t0, 0x44(s0)                /* QueueReady = 1 */
    li   t0, 15                      /* | DRIVER_OK */
    sw   t0, 0x70(s0)
    li   t0, 1
    sw   t0, RES_STATUS(s11)         /* progress marker: device is up */

/* ---- 2. fill the source buffer: 64 distinct doublewords ---- */
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

/* ---- 3. the WRITE request: descriptors 0,1,2 ---- */
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
    sw   t4, 8(t2)                   /* desc[0].len   = 16 */
    li   t4, 1
    sh   t4, 12(t2)                  /* desc[0].flags = NEXT */
    li   t4, 1
    sh   t4, 14(t2)                  /* desc[0].next  = 1 */
    addi t3, s1, VWBUF
    sd   t3, 16(t2)                  /* desc[1].addr  = source buffer */
    li   t4, 512
    sw   t4, 24(t2)                  /* desc[1].len   = 512 */
    li   t4, 1
    sh   t4, 28(t2)                  /* desc[1].flags = NEXT (device reads it) */
    li   t4, 2
    sh   t4, 30(t2)                  /* desc[1].next  = 2 */
    addi t3, s1, VST0
    sd   t3, 32(t2)                  /* desc[2].addr  = status byte */
    li   t4, 1
    sw   t4, 40(t2)                  /* desc[2].len   = 1 */
    li   t4, 2
    sh   t4, 44(t2)                  /* desc[2].flags = WRITE, no NEXT */
    sh   zero, 46(t2)

    addi t2, s1, VAVAIL
    sh   zero, 4(t2)                 /* avail.ring[0] = 0 */
    fence
    li   t4, 1
    sh   t4, 2(t2)                   /* avail.idx = 1 -- publishes it */
    fence
    sw   zero, 0x50(s0)              /* QueueNotify = 0 */

    addi t3, s1, VUSED
2:  lhu  t4, 2(t3)                   /* poll used.idx */
    beqz t4, 2b

    addi t5, s1, VST0
    lbu  t6, 0(t5)
    sw   t6, R_WSTAT(s11)
    lhu  t4, 2(t3)
    sw   t4, R_WIDX(s11)
    lw   t4, 4(t3)                   /* used.ring[0].id */
    sw   t4, R_WID(s11)
    lw   t4, 8(t3)                   /* used.ring[0].len */
    sw   t4, R_WLEN(s11)
    lw   t4, 0x60(s0)                /* InterruptStatus */
    sw   t4, R_WISR(s11)
    li   t4, 3
    sw   t4, 0x64(s0)                /* InterruptACK */
    li   t0, 2
    sw   t0, RES_STATUS(s11)

/* ---- 4. the READ request: descriptors 3,4,5, landing in RESULT ---- */
    addi t0, s1, VHDR1
    sw   zero, 0(t0)                 /* VIRTIO_BLK_T_IN */
    sw   zero, 4(t0)
    li   t1, SECTOR
    sd   t1, 8(t0)

    addi t2, s1, 48                  /* &desc[3] */
    addi t3, s1, VHDR1
    sd   t3, 0(t2)
    li   t4, 16
    sw   t4, 8(t2)
    li   t4, 1
    sh   t4, 12(t2)
    li   t4, 4
    sh   t4, 14(t2)                  /* -> desc[4] */
    li   t3, RESULT_BASE + RBUF      /* the device writes straight into RESULT */
    sd   t3, 16(t2)
    li   t4, 512
    sw   t4, 24(t2)
    li   t4, 3
    sh   t4, 28(t2)                  /* NEXT | WRITE */
    li   t4, 5
    sh   t4, 30(t2)                  /* -> desc[5] */
    addi t3, s1, VST1
    sd   t3, 32(t2)
    li   t4, 1
    sw   t4, 40(t2)
    li   t4, 2
    sh   t4, 44(t2)
    sh   zero, 46(t2)

    addi t2, s1, VAVAIL
    li   t4, 3
    sh   t4, 6(t2)                   /* avail.ring[1] = 3 */
    fence
    li   t4, 2
    sh   t4, 2(t2)                   /* avail.idx = 2 */
    fence
    sw   zero, 0x50(s0)

    addi t3, s1, VUSED
3:  lhu  t4, 2(t3)
    li   t5, 2
    bltu t4, t5, 3b

    addi t5, s1, VST1
    lbu  t6, 0(t5)
    sw   t6, R_RSTAT(s11)
    lhu  t4, 2(t3)
    sw   t4, R_RIDX(s11)
    lw   t4, 12(t3)                  /* used.ring[1].id */
    sw   t4, R_RID(s11)
    lw   t4, 16(t3)                  /* used.ring[1].len */
    sw   t4, R_RLEN(s11)
    lw   t4, 0x60(s0)
    sw   t4, R_RISR(s11)
    li   t4, 3
    sw   t4, 0x64(s0)
    li   t0, 3
    sw   t0, RES_STATUS(s11)

    mv   ra, s10
    ret
