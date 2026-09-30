/* core_regs_fcsr -- THE FLOATING-POINT CONTROL CSRs AT BOOT.

   Split out of core_regs_fpr on purpose.  fcsr/fflags/frm are Zicsr reads,
   so both machines can do them; the fp REGISTER FILE needs an fp store,
   which the Rocq model has no encoding for (see vtest-rocq/CoreRegsFpr.v),
   and mixing the two in one image would have made this comparison
   unreachable.

   mstatus.FS is Off at boot on both machines and an fp CSR read with FS =
   Off is an illegal instruction, so the body's first act is to set FS =
   Initial.  That write is the ONLY state this test changes; +32 reads
   mstatus back so the test says what it changed.

   RESULT LAYOUT (mirrored in vtest-rocq/CoreRegsFcsr.v); 8-byte words:
     +0   done             +4   status = 1
     +8   fcsr    0x003    +16  fflags 0x001
     +24  frm     0x002    +32  mstatus 0x300, AFTER the FS write  */
#include "abi.h"

    .globl _vtest_body
_vtest_body:
    li   t0, 0x2000            /* mstatus.FS = 1 (Initial) */
    csrs mstatus, t0
    csrr t0, 0x003
    sd   t0, 8(s11)
    csrr t0, 0x001
    sd   t0, 16(s11)
    csrr t0, 0x002
    sd   t0, 24(s11)
    csrr t0, 0x300
    sd   t0, 32(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)
    ret
