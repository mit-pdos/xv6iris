/* disk_ident_qsel -- a per-queue write with a NON-ZERO QueueSel.  The model
 * lets QueueSel be set to anything, and then REFUSES every per-queue write
 * while it is not 0 (see the comment in [virtio_write]): the machine is
 * stuck rather than the write being ignored.  QEMU ignores it -- queue 1
 * does not exist, and virtio_queue_set_num declines to move a queue between
 * existent and non-existent -- so a driver that probes the queues by walking
 * QueueSel upward completes on hardware and not on the model.
 */
#include "abi.h"

/* result-region offsets (mirrored in vtest-rocq/DiskIdent.v) */
#define R_QNM1       8    /* QueueNumMax at QueueSel = 1: no such queue */

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
    sw   t0, 0x30(s0)                /* QueueSel = 1 -- the model allows this */
    lw   t0, 0x34(s0)                /* ...and answers the read with 0 */
    sw   t0, R_QNM1(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- THE STUCK ACCESS: QueueNum while QueueSel = 1 ---- */
    li   t0, 8
    sw   t0, 0x38(s0)                /* <== the model has no transition here */
    li   t0, 2
    sw   t0, RES_STATUS(s11)
    mv   ra, s10
    ret
