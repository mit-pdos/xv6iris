/* disk_ident_confgen -- ConfigGeneration (0x0fc).  The register a driver
 * reads before and after a config-space read to detect that the device
 * changed the configuration underneath it (virtio spec 4.2.2.2).  Not
 * decoded: the load is stuck.  Together with disk_ident_cap this means the
 * whole config-space protocol is outside the model.
 */
#include "abi.h"

/* result-region offsets (mirrored in vtest-rocq/DiskIdent.v) */
#define R_CFGGEN     8    /* ConfigGeneration -- MODEL STUCK HERE */

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

/* ---- THE STUCK ACCESS: ConfigGeneration ---- */
    lw   t0, 0xfc(s0)                /* <== the model has no transition here */
    sw   t0, R_CFGGEN(s11)
    li   t0, 2
    sw   t0, RES_STATUS(s11)
    mv   ra, s10
    ret
