/* core_regs_ctr -- THE COUNTERS, kept apart from every other register test
   ON PURPOSE.

   These are the only architecturally readable registers whose value is not a
   constant of the boot, and BOTH sides make them useless as an equality:
   QEMU's mcycle/minstret/cycle/instret are the host's counters and change on
   every run, and the vtest harness always steps [riscv_step false], so the
   model's clock NEVER TICKS.  So this test states the MODEL's values (which
   are constants and can be pinned) and only the SHAPE of QEMU's, and
   vtest-rocq/CoreRegsCtr.v classifies the gap as a property of the harness
   rather than of the model.

   RESULT LAYOUT (mirrored in vtest-rocq/CoreRegsCtr.v); 8-byte words:
     +0   done          +4   status = 1
     +8   mcycle  0xB00 +16  minstret 0xB02
     +24  cycle   0xC00 +32  time     0xC01
     +40  instret 0xC02 +48  mcycle again, read after the first four, so the
                             two samples say whether the counter MOVED */
/* vtest: platforms=qemu */
/* NOT ON THE BOARD: the U74 traps executing `csrr menvcfg` (finding 31),
   and with mtvec=0 the second trap overwrites mcause/mepc/mtval, so the
   run never publishes and there is nothing to capture.  This case would
   also never agree there: its fields are counters.
   NOT ON CVA6 either, for the same shape of reason: CVA6 has no `time` CSR
   (rdtime is left to firmware, as on the U74), so `csrr time` at +0x64 is
   an illegal instruction and, with mtvec=0, the run parks in the boot ROM's
   wfi loop without publishing.  core_csrprobe asks it by stepping over the
   refusal. */
#include "abi.h"

    .globl _vtest_body
_vtest_body:
    csrr t0, 0xB00
    sd   t0, 8(s11)
    csrr t0, 0xB02
    sd   t0, 16(s11)
    csrr t0, 0xC00
    sd   t0, 24(s11)
    csrr t0, 0xC01
    sd   t0, 32(s11)
    csrr t0, 0xC02
    sd   t0, 40(s11)
    csrr t0, 0xB00
    sd   t0, 48(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)
    ret
