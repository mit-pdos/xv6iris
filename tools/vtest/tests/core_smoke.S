/* core_smoke -- the plumbing test.  Touches no device: it exists to check that
   one image, run on QEMU and on the Rocq semantics, produces the same RESULT
   region.  If this is red, nothing else in the suite means anything. */
#include "abi.h"

    .globl _vtest_body
_vtest_body:
    li   t0, 1
    sw   t0, RES_STATUS(s11)
    li   t0, 0xcafebabe
    sw   t0, RES_PAYLOAD(s11)
    li   t0, 0x12345678
    sw   t0, RES_PAYLOAD+4(s11)
    /* a stack round trip, so the declared STACK region is exercised too */
    addi sp, sp, -16
    li   t0, 0x5a5a5a5a
    sd   t0, 8(sp)
    ld   t1, 8(sp)
    addi sp, sp, 16
    sw   t1, RES_PAYLOAD+8(s11)
    ret
