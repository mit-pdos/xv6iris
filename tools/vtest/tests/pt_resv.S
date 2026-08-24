/* pt_resv -- THE RESERVED LEAF ENCODING R=0, W=1.

   A PTE with W set and R clear is reserved by the privileged spec and must
   raise a page fault; it is NOT a pointer to the next level (a pointer is
   R=W=X=0) and it is NOT a write-only page.  This is exactly the kind of
   check a translation model quietly omits, because omitting it costs
   nothing until software gets a bit wrong -- so it gets its own image.

   Two accesses through the same reserved leaf at VA 0x40000000: a load and
   a store.  Both must fault; nothing must be written.  A control load
   through a well-formed leaf at VA 0x40001000 runs first, so a fault at the
   reserved leaf cannot be blamed on the table being broken generally.

   menvcfg.ADUE is SET (Svadu) so both machines are in the same A/D mode;
   the reserved leaf carries A and D too, so "needs an A/D update" cannot be
   an alternative explanation for the fault.

   RESULT LAYOUT (mirrored in vtest-rocq/PtResv.v); 8-byte LE words:
     +0   done                    +4   status = 1
     +8   the control load through the well-formed leaf   (0x11223344)
     +16  the load through the reserved leaf              (0xBAD1 poison)
     +24  PA 0x80303020 after a store through the reserved leaf (0 -- the
          page is zeroed, so the store never landed)
     +32  how many faults were taken                      (2)
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
    csrs 0x30A, t0

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
    ori  t2, t1, PTE_D|PTE_A|PTE_W|PTE_V   /* W = 1, R = 0 -- RESERVED */
    sd   t2, 0(t0)
    ori  t2, t1, PTE_D|PTE_A|PTE_W|PTE_R|PTE_V
    sd   t2, 8(t0)                         /* the control leaf */

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

smode:
    li   s2, 0x40001000
    ld   s3, 0(s2)
    sd   s3, 8(s11)

    li   s3, 0xBAD1
    li   s2, 0x40000000
    ld   s3, 0(s2)
    sd   s3, 16(s11)

    li   s2, 0x40000020
    li   s3, 0x99
    sd   s3, 0(s2)
    li   s2, DATPAGE + 0x20
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
