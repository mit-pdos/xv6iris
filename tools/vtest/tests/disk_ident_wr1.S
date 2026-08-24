/* disk_ident_wr1 -- a ONE-BYTE WRITE to the virtio window.  [DevModel.
 * dev_write] decodes width 4 only, so an [sb] to Status is stuck.  QEMU
 * completes the access and DROPS it (guest-error log, no state change), so
 * the Status read after it still shows 11 rather than 15 -- which is the
 * interesting half: the model refuses a transaction the hardware performs,
 * and the hardware performs it as a NO-OP.
 */
#include "abi.h"

/* result-region offsets (mirrored in vtest-rocq/DiskIdent.v) */
#define R_ST_BEFORE  8    /* Status before the byte write */
#define R_ST_AFTER   12    /* Status after it -- QEMU dropped the write */

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

    lw   t0, 0x70(s0)
    sw   t0, R_ST_BEFORE(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- THE STUCK ACCESS: a 1-byte store of DRIVER_OK into Status ---- */
    li   t0, 15
    sb   t0, 0x70(s0)                /* <== the model has no transition here */
    lw   t0, 0x70(s0)
    sw   t0, R_ST_AFTER(s11)
    li   t0, 2
    sw   t0, RES_STATUS(s11)
    mv   ra, s10
    ret
