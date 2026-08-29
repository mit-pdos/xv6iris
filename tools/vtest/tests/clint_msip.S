/* clint_msip -- the software-interrupt register, and WHETHER THE CLINT IS
 * INDEXED BY HART.
 *
 * The CLINT gives every hart its own MSIP word at CLINT+4*hartid and its own
 * MTIMECMP at CLINT+0x4000+8*hartid.  That indexing is the whole point of
 * the device: it is how one hart interrupts another, and how each hart arms
 * its own timer.  xv6's start() writes CLINT_MTIMECMP(id) for exactly that
 * reason.
 *
 * THE MODEL DECODES ONE OF EACH.  rv64d.v's clint_load/clint_store compare
 * the offset with [eq_vec] against MSIP_BASE = 0x00000 and MTIMECMP_BASE =
 * 0x04000 -- single addresses, not a range with the hart id in it -- so
 * only hart 0's registers exist.  That is the same shape the PLIC had
 * before findings 11 and 12, where the controller was indexed by hart
 * instead of by CONTEXT and half the register file was simply absent.
 *
 * SO THIS TEST READS DIFFERENTLY ON THE TWO MACHINES, deliberately:
 *   - on QEMU it runs on hart 0, [4*hartid] is 0, and it exercises the
 *     model's MSIP semantics end to end;
 *   - on the VisionFive 2 it runs on hart 2, so the very first access is to
 *     CLINT+8, which the model does not decode -- and the test's job there
 *     is to say so precisely, with the pc of the offending instruction.
 * ClintMsip.v states both, and the pair is the finding.
 *
 * IT ONLY EVER WRITES ITS OWN HART'S WORD.  Reading another hart's MSIP is
 * harmless and +28 does it; WRITING one would send that hart an IPI, and on
 * a board the other harts are running firmware.
 *
 * Interrupts stay masked throughout (mstatus.MIE and mie are 0 at entry on
 * both machines), so setting MSIP makes mip.MSIP visible without ever
 * taking a trap.
 *
 * RESULT layout (mirrored in vtest-rocq/ClintMsip.v):
 *   +8    msip(self) before anything            expect 0
 *   +12   msip(self) after writing 1            expect 1
 *   +16   mip after writing 1, masked to MSIP   expect 8
 *   +20   msip(self) after writing 0            expect 0
 *   +24   mip after writing 0, masked to MSIP   expect 0
 *   +28   msip(hart 0), read only               distinguishes the registers
 *   +32   mhartid                               which hart this ran on
 */
/* vtest: repeat=1 */
#include "abi.h"

#define R_BEFORE   8
#define R_SET      12
#define R_MIPSET   16
#define R_CLEARED  20
#define R_MIPCLR   24
#define R_MSIP0    28
#define R_HARTID   32

#define MIP_MSIP   0x8              /* mip bit 3 */

    .globl _vtest_body
_vtest_body:
    csrr s1, mhartid
    sw   s1, R_HARTID(s11)

    li   t0, 1
    sw   t0, RES_STATUS(s11)

    /* s0 = CLINT_MSIP(mhartid) = CLINT0 + 4*mhartid */
    li   s0, CLINT0
    slli t0, s1, 2
    add  s0, s0, t0

/* ---- the register before we touch it ---- */
    lw   t0, 0(s0)
    sw   t0, R_BEFORE(s11)

/* ---- set it, and look at mip ---- */
    li   t0, 1
    sw   t0, 0(s0)
    lw   t0, 0(s0)
    sw   t0, R_SET(s11)
    csrr t0, mip
    andi t0, t0, MIP_MSIP
    sw   t0, R_MIPSET(s11)
    li   t0, 2
    sw   t0, RES_STATUS(s11)

/* ---- clear it again, and look at mip ---- */
    sw   zero, 0(s0)
    lw   t0, 0(s0)
    sw   t0, R_CLEARED(s11)
    csrr t0, mip
    andi t0, t0, MIP_MSIP
    sw   t0, R_MIPCLR(s11)

/* ---- hart 0's word, READ ONLY.  On a machine where the CLINT is indexed
 * this is a different register from the one above; writing it would IPI
 * whatever is running on hart 0, so this only reads. ---- */
    li   t0, CLINT0
    lw   t0, 0(t0)
    sw   t0, R_MSIP0(s11)

    li   t0, 3
    sw   t0, RES_STATUS(s11)
    ret
