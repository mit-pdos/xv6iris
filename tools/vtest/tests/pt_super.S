/* pt_super -- A MISALIGNED SUPERPAGE.

   A leaf PTE at level 1 maps 2 MB, so the low 9 bits of its PPN must be
   ZERO; the spec calls a nonzero value a misaligned superpage and requires
   a page fault.  Nothing in xv6 can produce one -- mappages only ever
   builds level-0 leaves -- which is exactly why a model can omit the check
   and never be caught, so it gets its own image.

   L1[1] (VA 0x40200000) is a level-1 leaf whose PPN is 0x80001, i.e. PA
   0x80001000: one 4 KB page above the 2 MB boundary, and therefore
   misaligned by exactly one page.  A load and a store through it must both
   fault.  A control load through a WELL-ALIGNED megapage at L1[2]
   (VA 0x40400000 -> PA 0x80000000) runs first, so a fault at the misaligned
   one cannot be blamed on megapages being unsupported.

   menvcfg.ADUE is SET (Svadu) so both machines are in the same A/D mode;
   both leaves carry A and D, so an A/D update cannot be an alternative
   explanation for the fault.

   RESULT LAYOUT (mirrored in vtest-rocq/PtSuper.v); 8-byte LE words:
     +0   done                    +4   status = 1
     +8   the control load through the ALIGNED megapage (the image's first
          word, 0xF14022F3)
     +16  the load through the MISALIGNED megapage      (0xBAD1 poison)
     +24  PA 0x80100340 after a store through the misaligned megapage
          (0 -- if the check were missing the store would land at
          0x80001000 + 0x100340, which is outside every declared region and
          would make the MODEL stuck rather than merely disagreeing)
     +32  how many faults were taken                    (2)
     +0x80   the M-mode backstop's record: mcause, mepc, mtval (all zero
             unless an UNDELEGATED trap happened)
     +0x100  the fault records, 24 bytes each: scause, sepc, stval          */
#include "abi.h"

#define PTE_V   0x001
#define PTE_R   0x002
#define PTE_W   0x004
#define PTE_A   0x040
#define PTE_D   0x080

#define L1PAGE  (PT_BASE + 0x1000)
#define FAULTS  0x100

    .globl _vtest_body
_vtest_body:
    lla  t0, mtrap
    csrw mtvec, t0
    li   t0, -1
    srli t0, t0, 10
    csrw pmpaddr0, t0
    li   t0, 0xf
    csrw pmpcfg0, t0
    li   t0, (1<<12)|(1<<13)|(1<<15)
    csrw medeleg, t0
    li   t0, 1
    slli t0, t0, 61
    csrs 0x30A, t0

    li   t0, PT_BASE
    li   t1, (0x80000000 >> 12) << 10
    ori  t1, t1, PTE_D|PTE_A|0x8|PTE_W|PTE_R|PTE_V
    sd   t1, 16(t0)                        /* root[2] identity gigapage */
    li   t1, (L1PAGE >> 12) << 10
    ori  t1, t1, PTE_V
    sd   t1, 8(t0)                         /* root[1] -> L1 */

    li   t0, L1PAGE
    li   t1, (0x80001000 >> 12) << 10      /* PPN 0x80001: LOW 9 BITS NONZERO */
    ori  t1, t1, PTE_D|PTE_A|PTE_W|PTE_R|PTE_V
    sd   t1, 8(t0)                         /* L1[1] misaligned megapage */
    li   t1, (0x80000000 >> 12) << 10      /* PPN 0x80000: properly aligned */
    ori  t1, t1, PTE_D|PTE_A|PTE_W|PTE_R|PTE_V
    sd   t1, 16(t0)                        /* L1[2] control megapage */

    li   t0, PT_BASE
    srli t0, t0, 12
    li   t1, 8
    slli t1, t1, 60
    or   t0, t0, t1
    csrw satp, t0
    sfence.vma

    lla  t0, strap
    csrw stvec, t0
    li   s10, RESULT_BASE + FAULTS

    lla  t0, smode
    csrw mepc, t0
    csrr t0, mstatus
    li   t1, 0x1800
    not  t1, t1
    and  t0, t0, t1
    li   t1, 0x800
    or   t0, t0, t1
    csrw mstatus, t0
    mret

smode:
    li   s2, 0x40400000            /* the ALIGNED megapage: must work */
    lwu  s3, 0(s2)
    sd   s3, 8(s11)

    li   s3, 0xBAD1
    li   s2, 0x40200000            /* the MISALIGNED one: must fault */
    ld   s3, 0(s2)
    sd   s3, 16(s11)

    li   s2, 0x40300340            /* would be PA 0x80101340 if allowed */
    li   s3, 0x99
    sd   s3, 0(s2)
    li   s2, RESULT_BASE + 0x340
    ld   s3, 0(s2)
    sd   s3, 24(s11)

    li   t0, RESULT_BASE + FAULTS
    sub  t0, s10, t0
    srli t0, t0, 3
    li   t1, 3
    divu t0, t0, t1
    sd   t0, 32(s11)

    li   t0, 1
    sw   t0, RES_STATUS(s11)
    ret

    .align 4
strap:
    csrr t0, scause
    sd   t0, 0(s10)
    csrr t1, sepc
    sd   t1, 8(s10)
    csrr t2, stval
    sd   t2, 16(s10)
    addi s10, s10, 24
    addi t1, t1, 4
    csrw sepc, t1
    sret

    .align 4
mtrap:
    li   t1, RESULT_BASE + 0x80
    csrr t0, mcause
    sd   t0, 0(t1)
    csrr t0, mepc
    sd   t0, 8(t1)
    csrr t0, mtval
    sd   t0, 16(t1)
    li   t0, 0x4D
    sw   t0, RES_STATUS(s11)
    fence
    li   t0, DONE_MAGIC
    sw   t0, RES_DONE(s11)
1:  j    1b
