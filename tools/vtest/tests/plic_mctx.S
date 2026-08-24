/* plic_mctx -- the M-CONTEXT registers, which the model does not decode.
 *
 * The virt machine's PLIC gives every hart TWO contexts: context 2h is the
 * M-mode one and context 2h+1 the S-mode one.  [DevModel]'s decode
 * ([plic_senable_hart], [plic_sthresh_hart], [plic_sclaim_hart]) recognises
 * only the second of each pair -- enable at 0x2080 + h*0x100, threshold at
 * 0x201000 + h*0x2000, claim/complete at 0x201004 + h*0x2000 -- because
 * that is all xv6 uses.  Hart 0's M-context registers sit one stride BELOW
 * each of those, at 0x2000, 0x200000 and 0x200004, and [plic_read] /
 * [plic_write] answer [None] for all three, which is a STUCK machine.
 *
 * So this program does its S-context work first, to show the window and the
 * program are otherwise fine, and then makes ONE M-context access.  A stuck
 * run is over, so the M-context threshold and claim below are for the QEMU
 * capture's benefit -- the model never reaches them.
 *
 * WHAT KIND OF FINDING THIS IS: incompleteness, not unsoundness.  Nothing
 * proved about xv6 is weakened by it -- the system theorem proves xv6 never
 * gets stuck, so these states are simply never reached.  What it costs is
 * reach: an M-mode interrupt handler, or a machine-mode bootloader that
 * parks the M context by writing its threshold, cannot be described in this
 * model at all.
 */
/* vtest: repeat=1 */
#include "abi.h"

#define PLIC        0x0c000000
#define P_SENABLE   0x2080          /* hart 0, S context -- decoded */
#define P_STHRESH   0x201000
#define P_SCLAIM    0x201004
#define P_MENABLE   0x2000          /* hart 0, M context -- NOT decoded */
#define P_MTHRESH   0x200000
#define P_MCLAIM    0x200004

/* result-region offsets -- MIRRORED in vtest-rocq/PlicMctx.v */
#define R_SENAB    8   /* S-context enable word read back           0x402  */
#define R_STHR    12   /* S-context threshold read back              3     */
#define R_MENAB   16   /* M-context enable word read back           0x402  */
#define R_MTHR    20   /* M-context threshold read back              2     */
#define R_MCLAIM  24   /* M-context claim                            0     */

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
    li   s2, PLIC

/* ---- the S context, which the model DOES decode ---- */
    li   t1, P_SENABLE
    add  t1, s2, t1
    li   t0, 0x402
    sw   t0, 0(t1)
    lw   t0, 0(t1)
    sw   t0, R_SENAB(s11)
    li   t1, P_STHRESH
    add  t1, s2, t1
    li   t0, 3
    sw   t0, 0(t1)
    lw   t0, 0(t1)
    sw   t0, R_STHR(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- the M context, one stride below each of them ---- */
    li   t1, P_MENABLE
    add  t1, s2, t1
    li   t0, 0x402
    sw   t0, 0(t1)                   /* <-- THE MODEL IS STUCK HERE */
    lw   t0, 0(t1)
    sw   t0, R_MENAB(s11)
    li   t1, P_MTHRESH
    add  t1, s2, t1
    li   t0, 2
    sw   t0, 0(t1)
    lw   t0, 0(t1)
    sw   t0, R_MTHR(s11)
    li   t1, P_MCLAIM
    add  t1, s2, t1
    lw   t0, 0(t1)
    sw   t0, R_MCLAIM(s11)

    li   t0, 2
    sw   t0, RES_STATUS(s11)
    mv   ra, s10
    ret
