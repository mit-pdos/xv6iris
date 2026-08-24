/* pt_ident -- THE BASELINE: S-MODE WITH PAGING ON.

   Everything else in the `pt` area depends on this one agreeing.  It builds
   the smallest possible Sv39 table -- ONE level-2 leaf (a gigapage) at
   VA 0x80000000 -> PA 0x80000000, which covers the text, the stack, the
   result region and the page-table pages themselves -- drops to S-mode,
   and does a load and a store through it.

   FOUR THINGS THAT ARE NOT OPTIONAL, and each kills the image silently:

   1. PMP.  The model implements 16 PMP entries and the boot chain leaves
      them ALL OFF.  With entries implemented but none matching, M-mode
      passes and S/U-mode FAILS EVERY ACCESS -- so the first S-mode fetch
      dies and it does not look like a PMP problem.  xv6's start() writes
      pmpaddr0 = 0x3fffffffffffff, pmpcfg0 = 0xf (TOR, R|W|X, base 0), and
      so does this.
   2. mtvec.  It is 0 at power-on, so ANY undelegated trap sends the pc to
      0, where the fetch faults, and traps back to 0 forever -- a budget
      exhaustion on the model side that reads like a small budget.
   3. medeleg = 0 at power-on, so page faults go to M-mode.  Bits 12/13/15
      (instruction/load/store page fault) are delegated here so the S-mode
      handler in the other pt_ tests sees them; this test takes no fault.
   4. menvcfg.ADUE.  Finding 20: the power-on value DIFFERS -- bit 61 is 0
      in the model (Svade) and SET on QEMU (Svadu) -- so a table written the
      natural way, with no A/D bits, faults on the model and succeeds on
      QEMU for a reason that has nothing to do with translation.  EVERY pt_
      program therefore pins the mode explicitly.  This one picks Svadu,
      which is what xv6 runs under (start() sets ADUE), and additionally
      presets A and D in the leaf so no write-back can fire either; pt_ad,
      pt_adu and pt_ade are the tests that are ABOUT that path.

   RESULT LAYOUT (mirrored in vtest-rocq/PtIdent.v); 8-byte LE words:
     +0   done               +4   status = 1
     +8   satp read back IN S-MODE
     +16  the value stored and re-loaded through the VA
     +24  scause  (0 -- nothing trapped)
     +32  the first word of the image, loaded through the VA
     +40  sstatus read back in S-mode
     +48  menvcfg after the ADUE write
     +0x100 the M-mode backstop's record: mcause, mepc, mtval                */
#include "abi.h"

#define PTE_V   0x001
#define PTE_R   0x002
#define PTE_W   0x004
#define PTE_X   0x008
#define PTE_U   0x010
#define PTE_A   0x040
#define PTE_D   0x080

    .globl _vtest_body
_vtest_body:
    /* ---- M-mode: the backstop trap vector ---- */
    lla  t0, mtrap
    csrw mtvec, t0
    csrw scause, zero
    csrw stval, zero

    /* ---- PMP: one TOR entry covering everything ---- */
    li   t0, -1
    srli t0, t0, 10                /* 0x003fffffffffffff */
    csrw pmpaddr0, t0
    li   t0, 0xf                   /* TOR | X | W | R */
    csrw pmpcfg0, t0

    /* ---- delegate the three page faults to S-mode ---- */
    li   t0, (1<<12)|(1<<13)|(1<<15)
    csrw medeleg, t0

    /* ---- pin the A/D mode: Svadu on BOTH machines ---- */
    li   t0, 1
    slli t0, t0, 61                /* menvcfg.ADUE */
    csrs 0x30A, t0
    csrr t0, 0x30A
    sd   t0, 48(s11)

    /* ---- the table: root slot 2 is a gigapage 0x80000000 -> 0x80000000 ---- */
    li   t0, PT_BASE
    li   t1, (0x80000000 >> 12) << 10
    ori  t1, t1, PTE_D|PTE_A|PTE_X|PTE_W|PTE_R|PTE_V
    sd   t1, 16(t0)                /* VPN[2] of 0x80000000 is 2 */

    /* ---- satp = Sv39 | root ppn ---- */
    li   t0, PT_BASE
    srli t0, t0, 12
    li   t1, 8
    slli t1, t1, 60
    or   t0, t0, t1
    csrw satp, t0
    sfence.vma

    /* ---- to S-mode: MPP = 1 ---- */
    lla  t0, smode
    csrw mepc, t0
    csrr t0, mstatus
    li   t1, 0x1800
    not  t1, t1
    and  t0, t0, t1
    li   t1, 0x800                 /* MPP = Supervisor */
    or   t0, t0, t1
    csrw mstatus, t0
    mret

    /* ================= everything below runs in S-MODE ================= */
smode:
    csrr t0, satp
    sd   t0, 8(s11)

    /* a store and a load back, through the gigapage */
    li   t1, 0x123456789ABCDEF0 >> 4   /* keep the literal short */
    slli t1, t1, 4
    li   t2, RESULT_BASE + 0x200
    sd   t1, 0(t2)
    ld   t3, 0(t2)
    sd   t3, 16(s11)

    csrr t0, scause
    sd   t0, 24(s11)

    /* read the first word of the image itself, through the VA */
    li   t0, TEXT_BASE
    lwu  t1, 0(t0)
    sd   t1, 32(s11)

    csrr t0, sstatus
    sd   t0, 40(s11)

    li   t0, 1
    sw   t0, RES_STATUS(s11)
    ret

    /* the M-mode backstop: a trap that was NOT delegated lands here and is
       recorded rather than looping forever at pc 0 */
    .align 4
mtrap:
    li   t1, RESULT_BASE + 0x100
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
