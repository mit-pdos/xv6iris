/* plic_prio0 -- the priority register of source 0, which the model does not
 * decode either, and which an ordinary init loop touches.
 *
 * [DevModel.plic_read] and [plic_write] gate the priority window on
 * [(0 <? off) && (off <? 4 * plic_nsrc)].  The lower bound is the problem:
 * offset 0 is source 0's priority register, and source 0 does not exist, so
 * the register is hardwired to zero on real hardware -- reads give 0, writes
 * are dropped.  The model has no transition for it at all, so
 *
 *     for (i = 0; i < NSRC; i++) plic_priority[i] = 0;
 *
 * -- the loop a driver writes to mask everything before it enables what it
 * wants -- is a STUCK machine on its very first iteration.
 *
 * A stuck run is over, so everything after the offset-0 store below is for
 * the QEMU capture's benefit.  It records two more things worth having on
 * the record: that offset 0 really is read-only-zero on the hardware, and
 * that source 32's priority register (offset 128) is a perfectly good
 * register there -- the virt machine's PLIC has 96 sources where
 * [plic_nsrc] is 32, so the upper bound cuts real registers off too.
 *
 * Incompleteness, not unsoundness: the system theorem proves xv6 never gets
 * stuck, so these states are never reached.  What it costs is which drivers
 * can be described.
 */
/* vtest: repeat=1 */
#include "abi.h"

#define PLIC        0x0c000000

/* result-region offsets -- MIRRORED in vtest-rocq/PlicPrio0.v */
#define R_PRIO1    8   /* source 1's priority, read back             7     */
#define R_PRIO0   12   /* source 0's priority after a store of 0     0     */
#define R_PRIO0W  16   /* ...and after a store of 5: read-only       0     */
#define R_PRIO32  20   /* source 32's priority after a store of 4    4     */

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
    li   s2, PLIC

    li   t0, 7
    sw   t0, 4(s2)                   /* source 1: an ordinary priority write */
    lw   t0, 4(s2)
    sw   t0, R_PRIO1(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)

    sw   zero, 0(s2)                 /* <-- THE MODEL IS STUCK HERE */
    lw   t0, 0(s2)
    sw   t0, R_PRIO0(s11)
    li   t0, 5
    sw   t0, 0(s2)
    lw   t0, 0(s2)
    sw   t0, R_PRIO0W(s11)

    li   t0, 4
    sw   t0, 128(s2)                 /* source 32 -- beyond plic_nsrc */
    lw   t0, 128(s2)
    sw   t0, R_PRIO32(s11)

    li   t0, 2
    sw   t0, RES_STATUS(s11)
    mv   ra, s10
    ret
