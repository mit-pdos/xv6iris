/* plic_prio0 -- source 0's priority register, and the sources past the
 * thirty-second.
 *
 * [DevModel.plic_read]/[plic_write] used to gate the priority window on
 * [(0 <? off) && (off <? 4 * plic_nsrc)] with [plic_nsrc] = 32, and BOTH
 * bounds cut off registers the hardware has (finding 12).
 *
 * The lower one had a driver behind it.  Offset 0 is source 0's priority
 * register; source 0 does not exist, so the register is hardwired to zero --
 * readable, and writes dropped -- and with no transition for it at all,
 *
 *     for (i = 0; i < NSRC; i++) plic_priority[i] = 0;
 *
 * the loop a driver writes to mask everything before enabling what it wants
 * was a STUCK machine on its first iteration.
 *
 * The upper one was the source count: the virt PLIC has 96, so source 32's
 * register at offset 128 is a register too, which needs the enable and
 * pending bitmaps to be three words each rather than one.
 *
 * Both are now modelled, so every field below AGREES.
 *
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

    sw   zero, 0(s2)                 /* source 0: hardwired zero */
    lw   t0, 0(s2)
    sw   t0, R_PRIO0(s11)
    li   t0, 5
    sw   t0, 0(s2)
    lw   t0, 0(s2)
    sw   t0, R_PRIO0W(s11)

    li   t0, 4
    sw   t0, 128(s2)                 /* source 32: the second bitmap word */
    lw   t0, 128(s2)
    sw   t0, R_PRIO32(s11)

    li   t0, 2
    sw   t0, RES_STATUS(s11)
    mv   ra, s10
    ret
