/* pt_levels -- THE WALK ACTUALLY DESCENDS: a full three-level walk to a
   4 KB leaf, and a level-1 MEGAPAGE, in the same table.

   pt_ident only ever uses a level-2 leaf, so its walk terminates at the
   root and nothing below it is exercised.  Here root[1] (VA 0x40000000)
   points at an L1 page, and

     L1[0] -> an L0 page whose slot 5 is a 4 KB leaf:
              VA 0x40005000 -> PA 0x80303000     (three levels, level 0 leaf)
     L1[1] is itself a LEAF -- a 2 MB megapage:
              VA 0x40200000 -> PA 0x80000000     (two levels, level 1 leaf)

   The megapage is the one that checks the offset arithmetic, because a
   level-1 leaf takes 21 bits of offset from the VA rather than 12: VA
   0x40200000 lands on the first word of the image, and VA 0x40300000 --
   1 MB into the same megapage -- lands on the RESULT region itself, so a
   store through it is visible at PA 0x80100000 through the identity map.
   A model that took only 12 offset bits would put both at the same place.

   menvcfg.ADUE is SET (Svadu) so both machines are in the same A/D mode;
   every leaf carries A and D, so no write-back fires.

   RESULT LAYOUT (mirrored in vtest-rocq/PtLevels.v); 8-byte LE words:
     +0   done                    +4   status = 1
     +8   the load from the 4 KB leaf VA 0x40005000     (0x11223344)
     +16  PA 0x80303010 through the identity map, after storing 0xDEC0DE
          through VA 0x40005010
     +24  the load from the megapage VA 0x40200000  (the image's first word)
     +32  PA 0x80100300 through the identity map, after storing 0xC0FFEE
          through VA 0x40300300 -- 1 MB into the megapage
     +40  how many faults were taken (0)
     +0x80   the M-mode backstop's record: mcause, mepc, mtval (all zero
             unless an UNDELEGATED trap happened)
     +0x100  the fault records, 24 bytes each: scause, sepc, stval          */
#include "abi.h"

#define PTE_V   0x001
#define PTE_R   0x002
#define PTE_W   0x004
#define PTE_X   0x008
#define PTE_A   0x040
#define PTE_D   0x080

#define L1PAGE  (PT_BASE + 0x1000)
#define L0PAGE  (PT_BASE + 0x2000)
#define DATPAGE (PT_BASE + 0x3000)
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
    csrs 0x30A, t0                 /* menvcfg.ADUE = 1 */

    li   t0, PT_BASE
    li   t1, (0x80000000 >> 12) << 10
    ori  t1, t1, PTE_D|PTE_A|PTE_X|PTE_W|PTE_R|PTE_V
    sd   t1, 16(t0)                        /* root[2] identity gigapage */
    li   t1, (L1PAGE >> 12) << 10
    ori  t1, t1, PTE_V
    sd   t1, 8(t0)                         /* root[1] -> L1 */

    li   t0, L1PAGE
    li   t1, (L0PAGE >> 12) << 10
    ori  t1, t1, PTE_V
    sd   t1, 0(t0)                         /* L1[0] -> L0 */
    li   t1, (0x80000000 >> 12) << 10
    ori  t1, t1, PTE_D|PTE_A|PTE_W|PTE_R|PTE_V
    sd   t1, 8(t0)                         /* L1[1] = 2 MB MEGAPAGE */

    li   t0, L0PAGE
    li   t1, (DATPAGE >> 12) << 10
    ori  t1, t1, PTE_D|PTE_A|PTE_W|PTE_R|PTE_V
    sd   t1, 40(t0)                        /* L0[5] -> VA 0x40005000 */

    li   t0, DATPAGE
    li   t1, 0x11223344
    sd   t1, 0(t0)

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

    /* ===================== S-MODE ===================== */
smode:
    /* the three-level 4 KB leaf */
    li   s2, 0x40005000
    ld   s3, 0(s2)
    sd   s3, 8(s11)
    li   s3, 0xDEC0DE
    li   s2, 0x40005010
    sd   s3, 0(s2)
    li   s2, DATPAGE + 0x10
    ld   s3, 0(s2)
    sd   s3, 16(s11)

    /* the level-1 megapage */
    li   s2, 0x40200000
    lwu  s3, 0(s2)
    sd   s3, 24(s11)
    li   s3, 0xC0FFEE
    li   s2, 0x40300300            /* 1 MB into the megapage = RESULT+0x300 */
    sd   s3, 0(s2)
    li   s2, RESULT_BASE + 0x300
    ld   s3, 0(s2)
    sd   s3, 32(s11)

    li   t0, RESULT_BASE + FAULTS
    sub  t0, s10, t0
    srli t0, t0, 3
    li   t1, 3
    divu t0, t0, t1
    sd   t0, 40(s11)

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
