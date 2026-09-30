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
#ifdef VTEST_BOARD
    /* BOARD ONLY, and it must be the FIRST instruction.  A board image is
       written into DRAM by a debugger over JTAG, which reaches the hart's
       data path but not its instruction cache; the U74's I-cache does not
       snoop, so a line left over from the PREVIOUS image at this address is
       still valid as far as the fetcher is concerned.  This instruction
       fixes that at no cost, and the reason it works even though its OWN
       fetch may be the stale one is that it is the same four bytes in every
       board image: a stale line decodes to this same [fence.i], which then
       invalidates the line, so the fetch at _start+4 is already correct.

       It is under an #ifdef and not unconditional because adding it to the
       QEMU images would change all 56 of them and invalidate every checked-in
       capture, to fix a problem QEMU does not have. */
    fence.i
#endif
    csrr t0, mhartid
#if PRIMARY_HART != 0
    /* THE HART SLOT, not the hart id.  Everything below indexes by slot:
       the primary is slot 0 and takes the top 2 KB of the stack region, an
       AP is slot 1 and takes the next 2 KB down.  Without this bias a board
       that runs on mhartid 2 and 3 would put slot 3's stack a page BELOW
       STACK_BASE -- outside the declared region, which is a stuck model and
       looks exactly like a genuine finding.  See README-hw.md.

       A test body that reads [mhartid] itself still sees the REAL id; only
       the prologue's slot arithmetic is biased. */
    addi t0, t0, -(PRIMARY_HART)
#endif
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
    /* A SYMBOL, not an instruction: `.globl` emits no bytes, so every image
       is unchanged.  It exists so a debugger-driven runner can put a
       hardware breakpoint on the exact instruction the primary parks at,
       instead of polling the DONE word over JTAG -- which costs a round trip
       per poll and cannot tell "not finished yet" from "hung".  See
       tools/vtest/board.py. */
    .globl _vtest_done
_vtest_done:
1:  j    1b

.Lap:
    jal  ra, _vtest_body_ap
2:  j    2b

    /* the default AP body: a test that wants its APs to do something defines
       its own _vtest_body_ap, and the strong definition wins over this one */
    .weak _vtest_body_ap
_vtest_body_ap:
    ret
