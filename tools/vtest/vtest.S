/* vtest.S -- the prologue/epilogue every vtest program uses.  Include it,
   then define _vtest_body.  See abi.h for the ABI it implements. */
#include "abi.h"

    .option norvc
    .section .text.init,"ax",@progbits
    .globl _start
_start:
    li   sp, STACK_BASE + STACK_SIZE
    li   s11, RESULT_BASE          /* s11 is the result cursor, ABI-reserved */
    jal  ra, _vtest_body
    /* the DONE handshake: everything the test wrote is already in memory,
       the fence orders it before the flag, and the flag is written last so
       a reader that sees it sees a complete result. */
    fence
    li   t0, DONE_MAGIC
    sw   t0, RES_DONE(s11)
1:  j    1b
