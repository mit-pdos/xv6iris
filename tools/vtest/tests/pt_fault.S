/* pt_fault -- THE FAULT MATRIX: five ways a translation can be refused,
   each recorded as scause / sepc / stval.

   The interesting half of a translation model is what it REFUSES, and a
   model that quietly omits a check passes every positive test.  This one
   drives, in order:

     1  a LOAD  of an unmapped VA                     -> scause 13
     2  a STORE to an unmapped VA                     -> scause 15
     3  a STORE to a read-only page (R=1, W=0)        -> scause 15
     4  an S-mode LOAD of a U=1 page, sstatus.SUM = 0 -> scause 13
     5  the same load with SUM = 1                    -> SUCCEEDS
     6  an instruction FETCH of an unmapped VA        -> scause 12

   Case 6 cannot recover by skipping the faulting instruction the way the
   others do -- sepc+4 is unmapped too, and the handler would fault forever
   -- so the handler special-cases scause 12 and resumes at a label.

   menvcfg.ADUE is SET (Svadu) so both machines are in the same A/D mode
   (finding 20: the power-on value differs), and every leaf here carries A
   and D anyway, so no write-back can fire and confuse a fault case.

   THE TABLE.  root[2] is the gigapage identity map; root[1] (VA 0x40000000)
   descends three levels into
     L0[0]  VA 0x40000000  R|W|A|D|V   the control page
     L0[1]  VA 0x40001000  R|A|D|V     READ-ONLY
     L0[2]  VA 0x40002000  R|W|U|A|D|V a USER page
     L0[3]  VA 0x40003000  0           UNMAPPED
   all pointing at the spare PT page 0x80303000.

   RESULT LAYOUT (mirrored in vtest-rocq/PtFault.v); 8-byte LE words:
     +0   done                    +4   status = 1
     +8   the control load from VA 0x40000000        (0x11223344)
     +16  the load from the unmapped VA              (0xBAD1 poison)
     +24  the word at PA 0x80303018 after the read-only store attempt
          (0 -- the page is zeroed, so the store never landed)
     +32  the load from the U page with SUM = 0      (0xBAD2 poison)
     +40  the load from the U page with SUM = 1      (0x11223344)
     +48  how many faults were taken                 (5)
     +56  sstatus after SUM was set
     +0x80   the M-mode backstop's record: mcause, mepc, mtval (all zero
             unless an UNDELEGATED trap happened)
     +0x100  the fault records, 24 bytes each: scause, sepc, stval          */
#include "abi.h"

#define PTE_V   0x001
#define PTE_R   0x002
#define PTE_W   0x004
#define PTE_X   0x008
#define PTE_U   0x010
#define PTE_A   0x040
#define PTE_D   0x080

#define L1PAGE  (PT_BASE + 0x1000)
#define L0PAGE  (PT_BASE + 0x2000)
#define DATPAGE (PT_BASE + 0x3000)
#define FAULTS  0x100

    .globl _vtest_body
_vtest_body:
    mv   s5, ra                    /* case 6's jalr clobbers ra; keep a copy */
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
    slli t0, t0, 61                /* menvcfg.ADUE = 1: Svadu on both */
    csrs 0x30A, t0

    /* ---- the table ---- */
    li   t0, PT_BASE
    li   t1, (0x80000000 >> 12) << 10
    ori  t1, t1, PTE_D|PTE_A|PTE_X|PTE_W|PTE_R|PTE_V
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
    ori  t2, t1, PTE_D|PTE_A|PTE_W|PTE_R|PTE_V
    sd   t2, 0(t0)                         /* VA 0x40000000  RW      */
    ori  t2, t1, PTE_D|PTE_A|PTE_R|PTE_V
    sd   t2, 8(t0)                         /* VA 0x40001000  RO      */
    ori  t2, t1, PTE_D|PTE_A|PTE_U|PTE_W|PTE_R|PTE_V
    sd   t2, 16(t0)                        /* VA 0x40002000  USER    */
    sd   zero, 24(t0)                      /* VA 0x40003000  UNMAPPED */

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
    /* control: a load that must WORK */
    li   s2, 0x40000000
    ld   s3, 0(s2)
    sd   s3, 8(s11)

    /* 1. load an unmapped VA */
    li   s3, 0xBAD1
    li   s2, 0x40003000
    ld   s3, 0(s2)
    sd   s3, 16(s11)

    /* 2. store to an unmapped VA */
    li   s2, 0x40003008
    li   s3, 0x77
    sd   s3, 0(s2)

    /* 3. store to the read-only page */
    li   s2, 0x40001018
    li   s3, 0x88
    sd   s3, 0(s2)
    li   s2, DATPAGE + 0x18
    ld   s3, 0(s2)                 /* still 0 if the store was refused */
    sd   s3, 24(s11)

    /* 4. load the U page with SUM clear */
    li   s3, 0xBAD2
    li   s2, 0x40002000
    ld   s3, 0(s2)
    sd   s3, 32(s11)

    /* 5. the same load with SUM set */
    li   s4, 1
    slli s4, s4, 18                /* sstatus.SUM */
    csrs sstatus, s4
    li   s2, 0x40002000
    ld   s3, 0(s2)
    sd   s3, 40(s11)
    csrr s4, sstatus
    sd   s4, 56(s11)

    /* 6. FETCH an unmapped VA */
    li   s2, 0x40003000
    jalr ra, s2, 0
fetch_recover:

    li   t0, RESULT_BASE + FAULTS
    sub  t0, s10, t0
    srli t0, t0, 3
    li   t1, 3
    divu t0, t0, t1
    sd   t0, 48(s11)

    li   t0, 1
    sw   t0, RES_STATUS(s11)
    mv   ra, s5
    ret

    /* the S-mode page-fault handler.  A DATA fault resumes at sepc+4; an
       INSTRUCTION fault cannot (sepc+4 is unmapped too) and resumes at a
       label instead. */
    .align 4
strap:
    csrr t0, scause
    sd   t0, 0(s10)
    csrr t1, sepc
    sd   t1, 8(s10)
    csrr t2, stval
    sd   t2, 16(s10)
    addi s10, s10, 24
    li   t2, 12
    beq  t0, t2, 2f
    addi t1, t1, 4
    csrw sepc, t1
    sret
2:  lla  t1, fetch_recover
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
