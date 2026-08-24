/* disk_ident_shmsel -- SHMSel (0x0ac) and the shared-memory region
 * registers.  A driver discovers a device's shared-memory regions by writing
 * a region id to SHMSel and reading SHMLen/SHMBase back; a length of all-ones
 * means "no such region".  None of the five registers is decoded, so the
 * SELECT is already stuck.
 */
#include "abi.h"

/* result-region offsets (mirrored in vtest-rocq/DiskIdent.v) */
#define R_SHMLENLO   8    /* SHMLenLow for region 0 -- all-ones means absent */
#define R_SHMLENHI   12    /* SHMLenHigh */

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

/* ---- THE STUCK ACCESS: SHMSel = 0 ---- */
    sw   zero, 0xac(s0)              /* <== the model has no transition here */
    lw   t0, 0xb0(s0)
    sw   t0, R_SHMLENLO(s11)
    lw   t0, 0xb4(s0)
    sw   t0, R_SHMLENHI(s11)
    li   t0, 2
    sw   t0, RES_STATUS(s11)
    mv   ra, s10
    ret
