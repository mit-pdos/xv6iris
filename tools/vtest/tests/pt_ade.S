/* pt_ade -- SVADE DELIBERATELY SELECTED: menvcfg.ADUE = 0 ON BOTH SIDES.

   The other half of the architectural choice pt_adu exercises.  With ADUE
   clear the walker must NOT update the PTE: an access whose leaf lacks A
   (or D, for a store) raises a page fault and software is expected to set
   the bit.  xv6 never runs this way -- start() sets ADUE -- but it is the
   spec's other mode and it is cheap once the machinery exists.

   ADUE is WARL, so the first thing this test establishes is whether QEMU
   ACCEPTS the clear at all; the menvcfg readback at +8 is that check, and
   if the bit were hardwired the whole test would silently become a second
   copy of pt_adu.

   Same table as pt_ad/pt_adu: root[2] a gigapage identity map with A and D
   set, root[1] a full three-level descent to two 4 KB leaves onto the spare
   PT page, one with A = 0 (loaded through) and one with A = 1, D = 0
   (stored through).  Both accesses are expected to FAULT, and both leaf
   PTEs are read back to confirm nothing was written.

   RESULT LAYOUT (mirrored in vtest-rocq/PtAde.v); 8-byte LE words:
     +0   done                    +4   status = 1
     +8   menvcfg read back AFTER the clear -- did bit 61 actually clear?
     +16  the value loaded from VA 0x40000000 (0xBAD1 -- the poison, since
          the handler skips the faulting instruction)
     +24  the A = 0 leaf PTE, read back: must be UNCHANGED
     +32  the word at PA 0x80303008: must still be 0, the store never ran
     +40  the D = 0 leaf PTE, read back: must be UNCHANGED
     +48  how many faults were taken (2 is the Svade answer)
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

    /* ---- Svadu OFF: this is the Svade half ---- */
    li   t0, 1
    slli t0, t0, 61                /* ADUE */
    csrc 0x30A, t0                 /* menvcfg */
    csrr t0, 0x30A
    sd   t0, 8(s11)

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
    ori  t2, t1, PTE_W|PTE_R|PTE_V         /* A = 0, D = 0 */
    sd   t2, 0(t0)
    ori  t2, t1, PTE_A|PTE_W|PTE_R|PTE_V   /* A = 1, D = 0 */
    sd   t2, 8(t0)

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
    li   t3, 0xBAD1
    li   t2, 0x40000000
    ld   t3, 0(t2)
    sd   t3, 16(s11)

    li   t0, L0PAGE
    ld   t1, 0(t0)
    sd   t1, 24(s11)

    li   t1, 0x5A5A
    li   t2, 0x40001008
    sd   t1, 0(t2)

    li   t0, DATPAGE + 8
    ld   t1, 0(t0)
    sd   t1, 32(s11)

    li   t0, L0PAGE
    ld   t1, 8(t0)
    sd   t1, 40(s11)

    li   t0, RESULT_BASE + FAULTS
    sub  t0, s10, t0
    srli t0, t0, 3
    li   t1, 3
    divu t0, t0, t1
    sd   t0, 48(s11)

    li   t0, 1
    sw   t0, RES_STATUS(s11)
    ret

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
