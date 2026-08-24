/* disk_ident_qreset -- QueueReset (0x0c0).  Per-queue reset, virtio 1.2
 * (VIRTIO_F_RING_RESET).  Note the offset: 0x0c0, not 0x08c -- 0x08c is not
 * a virtio-mmio register at all.  Not decoded by the model: the load is
 * stuck.  The write that would actually reset the queue is stuck too, and
 * is not attempted here because one program can only pin one stuck access.
 */
#include "abi.h"

/* result-region offsets (mirrored in vtest-rocq/DiskIdent.v) */
#define R_QRESET     8    /* QueueReset -- MODEL STUCK HERE */

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
    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- THE STUCK ACCESS: QueueReset ---- */
    lw   t0, 0xc0(s0)                /* <== the model has no transition here */
    sw   t0, R_QRESET(s11)
    li   t0, 2
    sw   t0, RES_STATUS(s11)
    mv   ra, s10
    ret
