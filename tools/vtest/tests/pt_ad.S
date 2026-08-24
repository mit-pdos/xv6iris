/* pt_ad -- A/D BITS IN THE DEFAULT CONFIGURATION.  NEITHER SIDE TOUCHES
   menvcfg, and that is the point.

   Finding 20 says menvcfg bit 61 (ADUE, the Svadu enable) is 0 in the model
   at power-on and SET on QEMU.  With ADUE set the walker WRITES A (and D on
   a store) back into the leaf PTE and the access succeeds; with it clear the
   walk raises a page fault and software must do the update.  So a page
   mapped with A = 0 and then touched is expected to diverge in the DEFAULT
   configuration -- and this is what xv6 actually does, since riscv.h defines
   no PTE_A/PTE_D at all and mappages writes PA2PTE(pa) | perm | PTE_V.

   THE TABLE.  Root slot 2 is a gigapage identity map (A and D set) so text,
   stack and result are reachable and no A/D update can fire for them.  Root
   slot 1 (VA 0x40000000) descends a full three levels into two 4 KB leaves
   that BOTH point at the spare PT page 0x80303000:

     VA 0x40000000  leaf flags R|W|V              -- A = 0, D = 0, LOADED
     VA 0x40001000  leaf flags R|W|V|A            -- A = 1, D = 0, STORED to

   RESULT LAYOUT (mirrored in vtest-rocq/PtAd.v); 8-byte LE words:
     +0   done                    +4   status = 1
     +8   menvcfg, read in M-mode at entry
     +16  the value loaded from VA 0x40000000 (0xBAD1 if it faulted -- the
          register is preloaded and the handler skips the instruction)
     +24  the A=0 leaf PTE, read back out of memory after the load
     +32  the word read back from PA 0x80303008 after a store through
          VA 0x40001008 (the page is zeroed, so 0 means the store never ran)
     +40  the D=0 leaf PTE, read back out of memory after the store
     +48  how many faults were taken
     +56/+64/+72  the M-mode backstop's record: mcause, mepc, mtval (all
          zero unless an UNDELEGATED trap happened)
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

    csrr t0, 0x30A                 /* menvcfg */
    sd   t0, 8(s11)

    /* ---- the table ---- */
    li   t0, PT_BASE
    li   t1, (0x80000000 >> 12) << 10
    ori  t1, t1, PTE_D|PTE_A|PTE_X|PTE_W|PTE_R|PTE_V
    sd   t1, 16(t0)                        /* root[2] gigapage identity */
    li   t1, (L1PAGE >> 12) << 10
    ori  t1, t1, PTE_V
    sd   t1, 8(t0)                         /* root[1] -> L1 */

    li   t0, L1PAGE
    li   t1, (L0PAGE >> 12) << 10
    ori  t1, t1, PTE_V
    sd   t1, 0(t0)                         /* L1[0] -> L0 */

    li   t0, L0PAGE
    li   t1, (DATPAGE >> 12) << 10
    ori  t2, t1, PTE_W|PTE_R|PTE_V         /* A = 0, D = 0 */
    sd   t2, 0(t0)                         /* L0[0]  <- VA 0x40000000 */
    ori  t2, t1, PTE_A|PTE_W|PTE_R|PTE_V   /* A = 1, D = 0 */
    sd   t2, 8(t0)                         /* L0[1]  <- VA 0x40001000 */

    /* something recognisable in the data page, so the load has an answer */
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
    /* (1) LOAD through the A = 0 leaf */
    li   t3, 0xBAD1
    li   t2, 0x40000000
    ld   t3, 0(t2)                 /* faults under Svade, succeeds under Svadu */
    sd   t3, 16(s11)

    /* what the leaf looks like now */
    li   t0, L0PAGE
    ld   t1, 0(t0)
    sd   t1, 24(s11)

    /* (2) STORE through the D = 0 (A = 1) leaf */
    li   t1, 0x5A5A
    li   t2, 0x40001008
    sd   t1, 0(t2)                 /* faults under Svade, succeeds under Svadu */

    li   t0, DATPAGE + 8
    ld   t1, 0(t0)
    sd   t1, 32(s11)

    li   t0, L0PAGE
    ld   t1, 8(t0)
    sd   t1, 40(s11)

    li   t0, RESULT_BASE + FAULTS
    sub  t0, s10, t0
    srli t0, t0, 3                 /* /24 done as /8 then /3 below */
    li   t1, 3
    divu t0, t0, t1
    sd   t0, 48(s11)

    li   t0, 1
    sw   t0, RES_STATUS(s11)
    ret

    /* the S-mode page-fault handler: record and SKIP the instruction */
    .align 4
strap:
    csrr t0, scause
    sd   t0, 0(s10)
    csrr t0, sepc
    sd   t0, 8(s10)
    csrr t0, stval
    sd   t0, 16(s10)
    addi s10, s10, 24
    csrr t0, sepc
    addi t0, t0, 4
    csrw sepc, t0
    sret

    .align 4
mtrap:
    csrr t0, mcause
    sd   t0, 56(s11)
    csrr t0, mepc
    sd   t0, 64(s11)
    csrr t0, mtval
    sd   t0, 72(s11)
    li   t0, 0x4D
    sw   t0, RES_STATUS(s11)
    fence
    li   t0, DONE_MAGIC
    sw   t0, RES_DONE(s11)
1:  j    1b
