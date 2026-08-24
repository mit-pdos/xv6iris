/* disk_ident_drvfsel -- DriverFeaturesSel (0x024).  Finding 3, second half:
 * with no way to select the high half of the DRIVER feature word, a driver
 * cannot ACKNOWLEDGE VIRTIO_F_VERSION_1 either.  The store is stuck.
 *
 * After the stuck store the program does, on QEMU only, the negotiation a
 * spec-conforming 1.x driver performs -- ack the low half, select the high
 * half, ack VERSION_1, then FEATURES_OK -- and records the Status register,
 * which is how a driver learns the device ACCEPTED its feature set.  That
 * whole sequence is outside the model.
 */
#include "abi.h"

/* result-region offsets (mirrored in vtest-rocq/DiskIdent.v) */
#define R_FEATLO     8    /* DeviceFeatures, low half */
#define R_FEATHI     12    /* DeviceFeatures, high half */
#define R_STATUS_OK  16    /* Status after FEATURES_OK with VERSION_1 acked */

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

    lw   t0, 0x10(s0)
    sw   t0, R_FEATLO(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- THE STUCK ACCESS: DriverFeaturesSel = 1 ---- */
    li   t0, 1
    sw   t0, 0x24(s0)                /* <== the model has no transition here */
    li   t0, 1
    sw   t0, 0x14(s0)                /* DeviceFeaturesSel = 1 */
    lw   t0, 0x10(s0)
    sw   t0, R_FEATHI(s11)
    li   t0, 1
    sw   t0, 0x20(s0)                /* ack VERSION_1 (bit 32) */
    li   t0, 11                      /* FEATURES_OK again, with the full set */
    sw   t0, 0x70(s0)
    lw   t0, 0x70(s0)
    sw   t0, R_STATUS_OK(s11)
    li   t0, 2
    sw   t0, RES_STATUS(s11)
    mv   ra, s10
    ret
