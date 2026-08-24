/* vtest.S -- the prologue/epilogue every vtest program uses.  Include it,
   then define _vtest_body.  See abi.h for the ABI it implements.

   MULTI-HART.  Every hart enters here.  Hart 0 runs _vtest_body and owns the
   DONE flag; every other hart runs _vtest_body_ap, which defaults to nothing
   and which a concurrency test overrides.  An AP never sets DONE -- the
   result is published once, by hart 0, after whatever synchronisation the
   test does itself.

   Each hart gets 2 KB of stack carved DOWNWARD from the top of the single
   declared STACK region, so raising `smp` costs no extra declared memory
   (and declared memory, not instruction count, is what a test costs on the
   model side -- see vtest-rocq/VTest.v section 2). */
#include "abi.h"

    .option norvc
    .section .text.init,"ax",@progbits
    .globl _start
_start:
    csrr t0, mhartid
    li   t1, STACK_BASE + STACK_SIZE
    slli t2, t0, 11                /* 2 KB per hart */
    sub  sp, t1, t2
    li   s11, RESULT_BASE          /* s11 is the result cursor, ABI-reserved */
    bnez t0, .Lap

    jal  ra, _vtest_body
    /* the DONE handshake: everything the test wrote is already in memory,
       the fence orders it before the flag, and the flag is written last so
       a reader that sees it sees a complete result. */
    fence
    li   t0, DONE_MAGIC
    sw   t0, RES_DONE(s11)
1:  j    1b

.Lap:
    jal  ra, _vtest_body_ap
2:  j    2b

    /* the default AP body: a test that wants its APs to do something defines
       its own _vtest_body_ap, and the strong definition wins over this one */
    .weak _vtest_body_ap
_vtest_body_ap:
    ret
