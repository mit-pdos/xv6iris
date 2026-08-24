/* conc_amo -- the SAME lost-update race, done CORRECTLY.
 *
 * conc_lost.S races two harts on one word with plain loads and stores and
 * loses updates: QEMU answers 4, 3 or 2.  This is how the increment is
 * actually written -- `amoadd.w` -- and both machines answer 2*NITER = 8
 * every time, with no interleaving to name.
 *
 * WHY IT IS WORTH HAVING.  vtest-rocq/VConc.v's header says an AMO-based
 * test will get VStuck; that is not what happens.  RiscvExec's [exec]
 * executes `amoadd.w` and `lr.w` perfectly well and this whole program runs
 * on the model.  What it will not do is `sc.w` -- see the note in
 * vtest-rocq/ConcAmo.v -- which is why hart 1 here uses amoadd too rather
 * than the lr/sc retry loop the first version of this test had.
 *
 * RESULT layout (mirrored in vtest-rocq/ConcAmo.v):
 *   +0x000  DONE          +0x100  CTR  -- the shared counter
 *   +0x004  status = 1    +0x104  DONE1
 *   +0x008  CTR read back by hart 0 = 2*NITER
 */
/* vtest: smp=2 repeat=40 */
#include "abi.h"

#define R_TOTAL   8
#define CTR       0x100
#define DONE1     0x104
#define NITER     4

    .globl _vtest_body
_vtest_body:                     /* hart 0 */
    li   t1, CTR
    add  t1, s11, t1
    li   a0, NITER
1:  li   t0, 1
    amoadd.w zero, t0, (t1)      /* THE INCREMENT, atomically */
    addi a0, a0, -1
    bnez a0, 1b
    li   t2, DONE1               /* wait for hart 1's four */
    add  t2, s11, t2
2:  lw   t0, 0(t2)
    beqz t0, 2b
    lw   t0, 0(t1)
    sw   t0, R_TOTAL(s11)        /* THE OBSERVATION */
    li   t0, 1
    sw   t0, RES_STATUS(s11)
    ret

    .globl _vtest_body_ap
_vtest_body_ap:                  /* hart 1 -- the same four */
    li   t1, CTR
    add  t1, s11, t1
    li   a0, NITER
1:  li   t0, 1
    amoadd.w zero, t0, (t1)
    addi a0, a0, -1
    bnez a0, 1b
    fence
    li   t0, 1
    sw   t0, DONE1(s11)
    ret
