/* disk_ident_rd1 -- a ONE-BYTE read of the virtio window.  [DevModel.
 * dev_read] decodes the virtio window at width 4 ONLY, so an [lbu] anywhere
 * in it is stuck, whatever the offset.  Here it is byte 0 of MagicValue,
 * which is 'v' = 0x76 if you read it a byte at a time.
 *
 * QEMU does NOT fault: virtio_mmio_read logs a guest error for any width
 * other than 4 below the config space and returns 0.  So the divergence is
 * not "the model is stricter about something the hardware also refuses" --
 * the hardware completes the access.
 */
#include "abi.h"

/* result-region offsets (mirrored in vtest-rocq/DiskIdent.v) */
#define R_B0         8    /* lbu of the virtio window -- MODEL STUCK HERE */

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
    sw   t0, RES_STATUS(s11)

/* ---- THE STUCK ACCESS: a 1-byte load ---- */
    lbu  t0, 0x00(s0)                /* <== the model has no transition here */
    sw   t0, R_B0(s11)
    li   t0, 2
    sw   t0, RES_STATUS(s11)
    mv   ra, s10
    ret
