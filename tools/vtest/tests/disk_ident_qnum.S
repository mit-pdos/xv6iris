/* disk_ident_qnum -- a QueueNum the model refuses.  [VirtioModel.vq_size_ok]
 * accepts only {1,2,4,8} and [virtio_write] returns None for anything else,
 * so QueueNum = 16 is stuck -- even though the very same device just
 * reported QueueNumMax = 1024 on QEMU (finding 1).  A driver that believes
 * QueueNumMax has no model execution.
 */
#include "abi.h"

/* result-region offsets (mirrored in vtest-rocq/DiskIdent.v) */
#define R_QNUMMAX    8    /* QueueNumMax -- what the driver is entitled to ask for */

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

    sw   zero, 0x30(s0)              /* QueueSel = 0 */
    lw   t0, 0x34(s0)
    sw   t0, R_QNUMMAX(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- THE STUCK ACCESS: QueueNum = 16, a legal size QEMU accepts ---- */
    li   t0, 16
    sw   t0, 0x38(s0)                /* <== the model has no transition here */
    li   t0, 2
    sw   t0, RES_STATUS(s11)
    mv   ra, s10
    ret
