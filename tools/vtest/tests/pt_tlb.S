/* vtest: repeat=20 */
/* pt_tlb -- A STALE TRANSLATION: change a PTE without sfence.vma, look,
   then sfence.vma and look again -- at TWO virtual addresses that differ
   only in which TLB SET they fall in.

   The middle observation is DELIBERATELY NOT PINNED to one value.  The
   architecture permits an implementation to keep the old translation until
   an sfence.vma, and equally permits it to have discarded the entry for any
   reason at all, so both answers are legal and the test is captured as a
   SET (`repeat=20` above).

   WHY TWO ADDRESSES.  The model's TLB is 64 entries, DIRECT-MAPPED, and
   `tlb_hash` is literally the low 6 bits of the VPN (rv64d.v:24650).  Every
   instruction fetch in this image is at VA 0x800001xx, VPN 0x80000, set 0,
   and every result-region store is at VPN 0x80100, set 0 -- so an entry for
   a test VA in set 0 is EVICTED by the next instruction the program
   executes, and the model can never show it stale.  A test VA in a set
   nothing else touches has no such problem.  So:

     VA 0x40000300  VPN 0x40000, set 0   -- collides with text and result
     VA 0x40007300  VPN 0x40007, set 7   -- collides with nothing here

   Both are mapped through a full three-level walk, first at PA 0x80303300
   (the spare PT page, holding 0x11223344) and then, by rewriting the
   level-0 slots through the identity map, at PA 0x80100300 (the RESULT
   region, holding 0x99887766).  The two values are distinguishable, so
   "which mapping was used" is directly readable.

   menvcfg.ADUE is SET (Svadu) so both machines are in the same A/D mode;
   every leaf carries A and D, so no write-back can fire and perturb the
   comparison.

   RESULT LAYOUT (mirrored in vtest-rocq/PtTlb.v); 8-byte LE words:
     +0   done                    +4   status = 1
     +8   VA 0x40000300, first load -- fills set 0        (0x11223344)
     +16  VA 0x40007300, first load -- fills set 7        (0x11223344)
     +24  VA 0x40000300 after the rewrite, NO sfence.vma
     +32  VA 0x40007300 after the rewrite, NO sfence.vma
          (0x11223344 = the stale entry was used, 0x99887766 = re-walked)
     +40  VA 0x40000300 after sfence.vma                  (0x99887766)
     +48  VA 0x40007300 after sfence.vma                  (0x99887766)
     +56  how many faults were taken (0)
     +0x80   the M-mode backstop's record: mcause, mepc, mtval (all zero
             unless an UNDELEGATED trap happened)
     +0x100  the fault records, 24 bytes each: scause, sepc, stval
     +0x300  0x99887766, planted in M-mode so the second mapping has a
             recognisable value                                             */
#include "abi.h"

#define PTE_V   0x001
#define PTE_R   0x002
#define PTE_W   0x004
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
    ori  t1, t1, PTE_D|PTE_A|0x8|PTE_W|PTE_R|PTE_V
    sd   t1, 16(t0)
    li   t1, (L1PAGE >> 12) << 10
    ori  t1, t1, PTE_V
    sd   t1, 8(t0)

    li   t0, L1PAGE
    li   t1, (L0PAGE >> 12) << 10
    ori  t1, t1, PTE_V
    sd   t1, 0(t0)

    li   t0, L0PAGE
    li   t1, (DATPAGE >> 12) << 10
    ori  t1, t1, PTE_D|PTE_A|PTE_W|PTE_R|PTE_V
    sd   t1, 0(t0)                         /* VA 0x40000000 -> the PT page */
    sd   t1, 56(t0)                        /* VA 0x40007000 -> the PT page */

    li   t0, DATPAGE + 0x300
    li   t1, 0x11223344
    sd   t1, 0(t0)
    li   t0, RESULT_BASE + 0x300
    li   t1, 0x99887766
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
    li   s2, 0x40000300
    li   s4, 0x40007300
    ld   s3, 0(s2)                 /* fills TLB set 0 */
    sd   s3, 8(s11)
    ld   s3, 0(s4)                 /* fills TLB set 7 */
    sd   s3, 16(s11)

    /* repoint both leaves at the RESULT page, through the identity map */
    li   t0, L0PAGE
    li   t1, (RESULT_BASE >> 12) << 10
    ori  t1, t1, PTE_D|PTE_A|PTE_W|PTE_R|PTE_V
    sd   t1, 0(t0)
    sd   t1, 56(t0)

    ld   s3, 0(s2)                 /* NO sfence.vma: stale or not, both legal */
    sd   s3, 24(s11)
    ld   s3, 0(s4)
    sd   s3, 32(s11)

    sfence.vma
    ld   s3, 0(s2)
    sd   s3, 40(s11)
    ld   s3, 0(s4)
    sd   s3, 48(s11)

    li   t0, RESULT_BASE + FAULTS
    sub  t0, s10, t0
    srli t0, t0, 3
    li   t1, 3
    divu t0, t0, t1
    sd   t0, 56(s11)

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
