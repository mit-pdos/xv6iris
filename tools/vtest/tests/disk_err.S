/* disk_err -- THE ERROR PATHS OF THE REQUEST PROTOCOL, never run before.
 *
 * [VirtioModel.virtio_complete] is TOTAL: it answers every request, and the
 * two branches nothing in the tree had ever exercised are
 *   - an UNRECOGNISED request type, which must complete with status
 *     VIRTIO_BLK_S_UNSUPP (2) and move no data at all, and
 *   - VIRTIO_BLK_T_FLUSH (4), which the model RECOGNISES (status OK, no
 *     data) and gates on the write cache being empty.
 *
 * The FLUSH is the interesting one, because this driver -- like xv6's --
 * DECLINES VIRTIO_BLK_F_FLUSH during negotiation.  So the question the test
 * actually asks is whether QEMU still serves a type-4 request from a driver
 * that never negotiated the feature.  Both machines' answers are recorded in
 * vtest-rocq/DiskErr.v.
 *
 * Three requests, in one queue, in order:
 *   A  a WRITE of a known pattern to sector 5              (descs 0,1,2)
 *   B  type 0x2a, sector 5, with a 512-byte DEVICE-WRITABLE data descriptor
 *      pointing INTO THE RESULT REGION and prefilled with 0xaa   (descs 3,4,5)
 *   C  a FLUSH                                             (descs 0,1,2 again)
 *
 * B's data descriptor is inside the result region on purpose: "no data
 * transfer" is then a CHANNEL, not an inference -- if either machine DMA'd
 * anything for the unsupported request, the 0xaa prefill at result+0x200
 * would say so.  And B names sector 5, the sector A just wrote, so if either
 * machine treated the unknown type as a write the disk capture would move.
 */
#include "abi.h"

/* offsets within the DMA region */
#define VDESC   0x000          /* 8 descriptors, 16 bytes each */
#define VAVAIL  0x100          /* flags:2 idx:2 ring[8]:2 each */
#define VUSED   0x200          /* flags:2 idx:2 ring[8]:8 each */
#define VHDR0   0x300          /* write   request header */
#define VHDR1   0x320          /* unknown request header */
#define VHDR2   0x340          /* flush   request header */
#define VST0    0x360          /* write   status byte */
#define VST1    0x361          /* unknown status byte */
#define VST2    0x362          /* flush   status byte */
#define VWBUF   0x400          /* 512-byte source buffer for the write */
#define VFBUF   0x700          /* 512-byte scratch for the flush chain (0x800
                                  would not fit addi's 12-bit signed imm) */

/* the unsupported request's data descriptor points HERE, inside RESULT */
#define RBUF    0x200

#define SECTOR      5
#define BADTYPE     0x2a       /* not IN, not OUT, not FLUSH */
#define BLK_T_FLUSH 4

/* result-region offsets (mirrored in vtest-rocq/DiskErr.v) */
#define R_WSTAT     8          /* the write's status byte        = 0 */
#define R_WID       12         /* used.ring[0].id                = 0 */
#define R_USTAT     16         /* the UNKNOWN type's status byte = 2 (UNSUPP) */
#define R_UID       20         /* used.ring[1].id                = 3 */
#define R_ULEN      24         /* used.ring[1].len */
#define R_FSTAT     28         /* the FLUSH's status byte        = 0 (OK) */
#define R_FID       32         /* used.ring[2].id                = 0 */
#define R_FLEN      36         /* used.ring[2].len */
#define R_UIDX      40         /* used.idx after all three       = 3 */
#define R_ISR       44         /* InterruptStatus                = 1 */
#define R_MARK      48         /* the first word of the 0xaa prefill */

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
                                        |INDIRECT_DESC|EVENT_IDX -- what xv6
                                        clears.  FLUSH IS DECLINED HERE. */
    not  t1, t1
    and  t0, t0, t1
    sw   t0, 0x20(s0)                /* DriverFeatures */
    li   t0, 11                      /* | FEATURES_OK */
    sw   t0, 0x70(s0)
    sw   zero, 0x30(s0)              /* QueueSel = 0 */
    li   t0, 8
    sw   t0, 0x38(s0)                /* QueueNum = 8 */
    mv   t0, s1                      /* descriptor table */
    sw   t0, 0x80(s0)
    srli t1, t0, 32
    sw   t1, 0x84(s0)
    addi t0, s1, VAVAIL              /* available ring */
    sw   t0, 0x90(s0)
    srli t1, t0, 32
    sw   t1, 0x94(s0)
    addi t0, s1, VUSED               /* used ring */
    sw   t0, 0xa0(s0)
    srli t1, t0, 32
    sw   t1, 0xa4(s0)
    li   t0, 1
    sw   t0, 0x44(s0)                /* QueueReady = 1 */
    li   t0, 15                      /* | DRIVER_OK */
    sw   t0, 0x70(s0)

/* ---- 2. the two buffers: the write pattern, and the 0xaa prefill ---- */
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

    li   t0, RESULT_BASE + RBUF      /* the untouchability marker */
    li   t1, 0xaaaaaaaaaaaaaaaa
    li   t2, 0
2:  slli t3, t2, 3
    add  t5, t0, t3
    sd   t1, 0(t5)
    addi t2, t2, 1
    li   t3, 64
    blt  t2, t3, 2b

/* ---- 3. request A: an ordinary WRITE of sector 5 (descs 0,1,2) ---- */
    addi t0, s1, VHDR0
    li   t1, 1                       /* VIRTIO_BLK_T_OUT */
    sw   t1, 0(t0)
    sw   zero, 4(t0)
    li   t1, SECTOR
    sd   t1, 8(t0)

    mv   t2, s1                      /* &desc[0] */
    addi t3, s1, VHDR0
    sd   t3, 0(t2)
    li   t4, 16
    sw   t4, 8(t2)
    li   t4, 1
    sh   t4, 12(t2)                  /* NEXT */
    li   t4, 1
    sh   t4, 14(t2)
    addi t3, s1, VWBUF
    sd   t3, 16(t2)
    li   t4, 512
    sw   t4, 24(t2)
    li   t4, 1
    sh   t4, 28(t2)                  /* NEXT, device-readable */
    li   t4, 2
    sh   t4, 30(t2)
    addi t3, s1, VST0
    sd   t3, 32(t2)
    li   t4, 1
    sw   t4, 40(t2)
    li   t4, 2
    sh   t4, 44(t2)                  /* WRITE, end of chain */
    sh   zero, 46(t2)

    addi t2, s1, VAVAIL
    sh   zero, 4(t2)                 /* avail.ring[0] = 0 */
    fence
    li   t4, 1
    sh   t4, 2(t2)
    fence
    sw   zero, 0x50(s0)              /* QueueNotify = 0 */

    addi t3, s1, VUSED
3:  lhu  t4, 2(t3)
    beqz t4, 3b

    addi t5, s1, VST0
    lbu  t6, 0(t5)
    sw   t6, R_WSTAT(s11)
    lw   t4, 4(t3)
    sw   t4, R_WID(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- 4. request B: AN UNRECOGNISED TYPE (descs 3,4,5) ---- */
    addi t0, s1, VHDR1
    li   t1, BADTYPE
    sw   t1, 0(t0)
    sw   zero, 4(t0)
    li   t1, SECTOR                  /* the sector A just wrote */
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
    li   t3, RESULT_BASE + RBUF      /* device-WRITABLE, into RESULT */
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
    sh   t4, 2(t2)
    fence
    sw   zero, 0x50(s0)

    addi t3, s1, VUSED
4:  lhu  t4, 2(t3)
    li   t5, 2
    bltu t4, t5, 4b

    addi t5, s1, VST1
    lbu  t6, 0(t5)
    sw   t6, R_USTAT(s11)
    lw   t4, 12(t3)                  /* used.ring[1].id */
    sw   t4, R_UID(s11)
    lw   t4, 16(t3)                  /* used.ring[1].len */
    sw   t4, R_ULEN(s11)
    li   t0, 2
    sw   t0, RES_STATUS(s11)

/* ---- 5. request C: a FLUSH, with the cache empty (descs 0,1,2 again) ---- */
    addi t0, s1, VHDR2
    li   t1, BLK_T_FLUSH
    sw   t1, 0(t0)
    sw   zero, 4(t0)
    sd   zero, 8(t0)                 /* the spec says sector must be 0 */

    mv   t2, s1                      /* &desc[0], reused */
    addi t3, s1, VHDR2
    sd   t3, 0(t2)
    li   t4, 16
    sw   t4, 8(t2)
    li   t4, 1
    sh   t4, 12(t2)
    li   t4, 1
    sh   t4, 14(t2)
    addi t3, s1, VFBUF               /* a flush carries no data; chain_at
                                        still wants exactly three descriptors */
    sd   t3, 16(t2)
    li   t4, 512
    sw   t4, 24(t2)
    li   t4, 3
    sh   t4, 28(t2)                  /* NEXT | WRITE */
    li   t4, 2
    sh   t4, 30(t2)
    addi t3, s1, VST2
    sd   t3, 32(t2)
    li   t4, 1
    sw   t4, 40(t2)
    li   t4, 2
    sh   t4, 44(t2)
    sh   zero, 46(t2)

    addi t2, s1, VAVAIL
    sh   zero, 8(t2)                 /* avail.ring[2] = 0 */
    fence
    li   t4, 3
    sh   t4, 2(t2)
    fence
    sw   zero, 0x50(s0)

    addi t3, s1, VUSED
5:  lhu  t4, 2(t3)
    li   t5, 3
    bltu t4, t5, 5b

    addi t5, s1, VST2
    lbu  t6, 0(t5)
    sw   t6, R_FSTAT(s11)
    lw   t4, 20(t3)                  /* used.ring[2].id */
    sw   t4, R_FID(s11)
    lw   t4, 24(t3)                  /* used.ring[2].len */
    sw   t4, R_FLEN(s11)

/* ---- 6. the closing observations ---- */
    lhu  t4, 2(t3)
    sw   t4, R_UIDX(s11)
    lw   t4, 0x60(s0)                /* InterruptStatus */
    sw   t4, R_ISR(s11)
    li   t4, 3
    sw   t4, 0x64(s0)                /* InterruptACK */
    li   t0, RESULT_BASE + RBUF
    lw   t4, 0(t0)                   /* the marker, still 0xaaaaaaaa? */
    sw   t4, R_MARK(s11)
    li   t0, 3
    sw   t0, RES_STATUS(s11)

    mv   ra, s10
    ret
