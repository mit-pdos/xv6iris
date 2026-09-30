/* disk_ident_cap -- THE DEVICE CAPACITY.  The virtio-blk CONFIG SPACE starts
 * at offset 0x100 of the mmio window and its first eight bytes are the
 * capacity in 512-byte sectors.
 *
 * THIS HEADER USED TO SAY THE MODEL WAS STUCK HERE -- [VirtioModel.virtio_read]
 * had no case for 0x100, so the load was [None] -- and that it was the entry
 * in the stuck matrix the owner had ruled should be FIXED.  It HAS been:
 * measured, the model decodes the config space, answers 128 sectors, and
 * AGREES with QEMU on both halves of the capacity and on size_max.  A driver
 * that asks the disk how big it is now has a model execution.
 *
 * What still diverges is seg_max: QEMU reports 254 and the model 0.  That is
 * disk_ident_segmax's, published there and nowhere else, so that the
 * capacity -- this test's subject, and the thing that was fixed -- can be
 * proved.
 */
/* vtest: platforms=qemu */
#include "abi.h"

/* result-region offsets (mirrored in vtest-rocq/DiskIdent.v) */
#define R_CAPLO      8    /* capacity, low 32 bits -- MODEL STUCK HERE */
#define R_CAPHI      12    /* capacity, high 32 bits */
#define R_SIZEMAX    16    /* config+8: size_max (only if F_SIZE_MAX) */
#define R_SEGMAX     20    /* config+12: seg_max -- disk_ident_segmax's */

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
/* ---- bring-up, verbatim from disk_rw.S but without the queue: enough that
       QEMU answers every register sensibly, and every access in it is one
       the model DOES decode, so the model reaches the stuck access below
       and not some earlier one. ---- */
    li   s0, VIRTIO0
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

    li   t0, 1
    sw   t0, RES_STATUS(s11)         /* progress: the device is up */

/* ---- THE STUCK ACCESS: virtio-blk config space, capacity ---- */
    lw   t0, 0x100(s0)               /* <== the model has no transition here */
    sw   t0, R_CAPLO(s11)
    lw   t0, 0x104(s0)
    sw   t0, R_CAPHI(s11)
    lw   t0, 0x108(s0)
    sw   t0, R_SIZEMAX(s11)
    lw   t0, 0x10c(s0)
#ifdef DISK_IDENT_SEGMAX
    sw   t0, R_SEGMAX(s11)
#endif
    li   t0, 2
    sw   t0, RES_STATUS(s11)
    mv   ra, s10
    ret
