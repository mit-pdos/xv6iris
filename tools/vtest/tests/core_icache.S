/* core_icache -- SELF-MODIFYING CODE WITHOUT fence.i.

   Is the instruction fetch coherent with the data side?  The model says NO
   (claude-notes/projects/icache.md): a fetch reads at the hart's
   INSTRUCTION view, which only fence.i raises, so a word the program has
   just stored over its own code may fetch as either the old or the new
   instruction until a fence.i.  A non-coherent I-cache (the JH7110's U74)
   is expected to keep answering the OLD instruction; QEMU's TCG invalidates
   its translation of a page the guest writes and answers the NEW one.

   The probe is one instruction, `li a0, 1`, on its own 64-byte line.  It is
   executed once so the line is in the I-cache, then its first word is
   overwritten with `li a0, 2` by an ordinary store, then it is executed
   three more times, then once more after a fence.i.

     RES_PAYLOAD+0   the warm-up answer (1 everywhere)
     RES_PAYLOAD+4   first run after the store   -- 1 stale, 2 fresh
     RES_PAYLOAD+8   second
     RES_PAYLOAD+12  third
     RES_PAYLOAD+16  after fence.i               -- 2 everywhere

   The model side (vtest-rocq/CoreIcacheSched.v) exhibits both: a fetch
   policy that reads at the top of the log (fresh) and one that reads at the
   instruction view (stale), each until the fence.i raises the view.

   vtest: builder=icache repeat=3 board_repeat=5 budget=4000 selfmod=1 */
#include "abi.h"

    .option norvc
    .globl _vtest_body
_vtest_body:
    addi sp, sp, -16
    sd   ra, 8(sp)
    /* 1. warm the I-cache: run the probe once */
    jal  ra, probe
    sw   a0, RES_PAYLOAD(s11)
    /* 2. overwrite the probe's first word with `li a0, 2` (addi a0, x0, 2).
       An ordinary store; NO fence.i. */
    lla  t0, probe
    li   t1, 0x00200513
    sw   t1, 0(t0)
    /* 3. run it again, three times */
    jal  ra, probe
    sw   a0, RES_PAYLOAD+4(s11)
    jal  ra, probe
    sw   a0, RES_PAYLOAD+8(s11)
    jal  ra, probe
    sw   a0, RES_PAYLOAD+12(s11)
    /* 4. the fence, then once more: every machine answers 2 now */
    .word 0x0000100f              /* fence.i -- spelled as a word: the QEMU
                                     images are built -march=rv64imafd, and this
                                     assembler wants zifencei named for the mnemonic */
    jal  ra, probe
    sw   a0, RES_PAYLOAD+16(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)
    ld   ra, 8(sp)
    addi sp, sp, 16
    ret

    /* on its own I-cache line, so the store hits exactly the line the
       warm-up fetched and nothing else on it */
    .p2align 6
probe:
    li   a0, 1
    ret
