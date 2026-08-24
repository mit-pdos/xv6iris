/* conc_smoke -- the two-hart plumbing test.  Hart 1 stores a magic word,
 * hart 0 spins until it sees it and records what it saw.  No race: this
 * exists to check that -smp 2 works on both machines, that vtest.S's AP
 * dispatch runs _vtest_body_ap on hart 1 only, and that the model's
 * two-hart stepper (vtest-rocq/VConc.v) can interleave them at all.
 */
/* vtest: smp=2 */
#include "abi.h"

#define HANDSHAKE  0x100        /* offset in RESULT: hart 1 -> hart 0 */
#define R_SEEN     8
#define MAGIC      0xa5a5

    .globl _vtest_body
_vtest_body:                     /* hart 0 */
    li   t1, HANDSHAKE
    add  t1, s11, t1
1:  lw   t0, 0(t1)               /* spin until hart 1 publishes */
    beqz t0, 1b
    sw   t0, R_SEEN(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)
    ret

    .globl _vtest_body_ap
_vtest_body_ap:                  /* every other hart */
    li   t1, HANDSHAKE
    add  t1, s11, t1
    li   t0, MAGIC
    fence
    sw   t0, 0(t1)
    ret
