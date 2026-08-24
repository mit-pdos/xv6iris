/* disk_ident -- every virtio-mmio register the MODEL DECODES, read back and
 * compared with QEMU.  The positive half of the "stuck matrix": the
 * disk_ident_* programs each pin ONE access the model refuses; this one pins
 * the whole of what it does answer.
 *
 * Nine readable registers ([VirtioModel.vio_readable]): MagicValue, Version,
 * DeviceID, VendorID, DeviceFeatures, QueueNumMax, QueueReady,
 * InterruptStatus, Status.  QueueNumMax and QueueReady are read at BOTH a
 * selected queue 0 and a selected queue 1, which is the one place the model
 * has a per-queue answer at all.  The program then RESETS the device
 * (Status <- 0) and reads Status/QueueReady/DeviceFeatures back, so
 * [virtio_reset] is checked against QEMU's reset too.
 *
 * Two of the fields are the ALREADY-KNOWN divergences of findings 1 and 2
 * (QueueNumMax 8 vs 1024, DeviceFeatures FLUSH|CONFIG_WCE vs 0x30006e54);
 * they are pinned on both sides in vtest-rocq/DiskIdent.v rather than
 * re-reported.
 *
 * No virtqueue is ever published, so this test needs no DMA region: the
 * queue addresses are programmed (QEMU wants them before QUEUE_READY) but
 * avail.idx stays 0, so the device never has work and never DMAs.
 */
#include "abi.h"

/* result-region offsets (mirrored in vtest-rocq/DiskIdent.v) */
#define R_MAGIC      8
#define R_VERSION    12
#define R_DEVID      16
#define R_VENDOR     20
#define R_FEATURES   24    /* DIVERGES -- finding 2 */
#define R_ST_DRIVER  28    /* Status after ACKNOWLEDGE|DRIVER      = 3  */
#define R_ST_FEATOK  32    /* Status after FEATURES_OK             = 11 */
#define R_QNM0       36    /* QueueNumMax, QueueSel = 0  DIVERGES -- finding 1 */
#define R_QNM1       40    /* QueueNumMax, QueueSel = 1  (no such queue) */
#define R_QRDY1      44    /* QueueReady,  QueueSel = 1 */
#define R_QRDY0A     48    /* QueueReady,  QueueSel = 0, before */
#define R_QRDY0B     52    /* QueueReady,  QueueSel = 0, after QueueReady <- 1 */
#define R_ISR        56    /* InterruptStatus, nothing outstanding = 0 */
#define R_ST_DRVOK   60    /* Status after DRIVER_OK               = 15 */
#define R_ST_RESET   64    /* Status after Status <- 0             = 0  */
#define R_QRDY_RST   68    /* QueueReady after the reset           = 0  */
#define R_FEAT_RST   72    /* DeviceFeatures after the reset (unchanged) */
#define R_ISR_RST    76    /* InterruptStatus after the reset      = 0  */

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
    li   s0, VIRTIO0
    li   s1, DMA_BASE

/* ---- 1. identity, before any bring-up ---- */
    lw   t0, 0x00(s0)                /* MagicValue */
    sw   t0, R_MAGIC(s11)
    lw   t0, 0x04(s0)                /* Version */
    sw   t0, R_VERSION(s11)
    lw   t0, 0x08(s0)                /* DeviceID */
    sw   t0, R_DEVID(s11)
    lw   t0, 0x0c(s0)                /* VendorID */
    sw   t0, R_VENDOR(s11)

/* ---- 2. bring-up (kernel/virtio_disk.c's sequence) ---- */
    sw   zero, 0x70(s0)              /* Status = 0: reset */
    li   t0, 1                       /* ACKNOWLEDGE */
    sw   t0, 0x70(s0)
    li   t0, 3                       /* | DRIVER */
    sw   t0, 0x70(s0)
    lw   t0, 0x70(s0)
    sw   t0, R_ST_DRIVER(s11)
    lw   t0, 0x10(s0)                /* DeviceFeatures */
    sw   t0, R_FEATURES(s11)
    li   t1, 0x38001AA0              /* what xv6 clears */
    not  t1, t1
    and  t0, t0, t1
    sw   t0, 0x20(s0)                /* DriverFeatures */
    li   t0, 11                      /* | FEATURES_OK */
    sw   t0, 0x70(s0)
    lw   t0, 0x70(s0)                /* it must have stuck */
    sw   t0, R_ST_FEATOK(s11)

/* ---- 3. the per-queue registers, at a queue that does not exist ---- */
    li   t0, 1
    sw   t0, 0x30(s0)                /* QueueSel = 1 */
    lw   t0, 0x34(s0)
    sw   t0, R_QNM1(s11)
    lw   t0, 0x44(s0)
    sw   t0, R_QRDY1(s11)

/* ---- 4. ...and at queue 0, the only one this device has ---- */
    sw   zero, 0x30(s0)              /* QueueSel = 0 */
    lw   t0, 0x34(s0)                /* QueueNumMax */
    sw   t0, R_QNM0(s11)
    lw   t0, 0x44(s0)                /* QueueReady, before */
    sw   t0, R_QRDY0A(s11)
    li   t0, 8
    sw   t0, 0x38(s0)                /* QueueNum = 8 */
    mv   t0, s1                      /* descriptor table */
    sw   t0, 0x80(s0)
    srli t1, t0, 32
    sw   t1, 0x84(s0)
    addi t0, s1, 0x100               /* available ring */
    sw   t0, 0x90(s0)
    srli t1, t0, 32
    sw   t1, 0x94(s0)
    addi t0, s1, 0x200               /* used ring */
    sw   t0, 0xa0(s0)
    srli t1, t0, 32
    sw   t1, 0xa4(s0)
    li   t0, 1
    sw   t0, 0x44(s0)                /* QueueReady = 1 */
    lw   t0, 0x44(s0)
    sw   t0, R_QRDY0B(s11)
    li   t0, 15                      /* | DRIVER_OK */
    sw   t0, 0x70(s0)
    lw   t0, 0x70(s0)
    sw   t0, R_ST_DRVOK(s11)
    lw   t0, 0x60(s0)                /* InterruptStatus: nothing outstanding */
    sw   t0, R_ISR(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)         /* progress: the device came up */

/* ---- 5. the RESET command, and what survives it ---- */
    sw   zero, 0x70(s0)              /* Status = 0 */
    lw   t0, 0x70(s0)
    sw   t0, R_ST_RESET(s11)
    lw   t0, 0x44(s0)                /* QueueReady must be back to 0 */
    sw   t0, R_QRDY_RST(s11)
    lw   t0, 0x10(s0)                /* the offered features do not reset */
    sw   t0, R_FEAT_RST(s11)
    lw   t0, 0x60(s0)
    sw   t0, R_ISR_RST(s11)
    li   t0, 2
    sw   t0, RES_STATUS(s11)

    mv   ra, s10
    ret
