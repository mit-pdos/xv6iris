/* disk_ident_featsel -- DeviceFeaturesSel (0x014).  Finding 3, first half:
 * the register that selects WHICH 32-bit half of the device's feature word
 * DeviceFeatures (0x010) reports is not decoded by [virtio_write] at all, so
 * the store is stuck.  The consequence is that VIRTIO_F_VERSION_1 -- bit 32,
 * which the virtio 1.x spec REQUIRES a modern driver to negotiate -- cannot
 * even be READ under this model.
 *
 * The store is last for the model; the reads after it are QEMU's answer.
 */
#include "abi.h"

/* result-region offsets (mirrored in vtest-rocq/DiskIdent.v) */
#define R_FEATLO     8    /* DeviceFeatures with sel = 0 */
#define R_FEATHI     12    /* DeviceFeatures with sel = 1 -- bit 32 is VERSION_1 */

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

/* ---- THE STUCK ACCESS: DeviceFeaturesSel = 1 ---- */
    li   t0, 1
    sw   t0, 0x14(s0)                /* <== the model has no transition here */
    lw   t0, 0x10(s0)                /* the HIGH half of the feature word */
    sw   t0, R_FEATHI(s11)
    li   t0, 2
    sw   t0, RES_STATUS(s11)
    mv   ra, s10
    ret
