/* core_regs_mcsr -- THE M-MODE CSRs AT BOOT, dumped whole.

   The image is still in M-mode (vtest.S never leaves it), so every read here
   is architecturally legal for the hart that boots, and nothing here WRITES
   a CSR: what is under test is the value the boot chain left.

   WHAT IS DELIBERATELY *NOT* HERE, and why -- each was probed one-per-image
   first, because an unimplemented CSR is a hang on QEMU (no handler is
   installed) and a STUCK machine on the model:
     mseccfg (0x747)          QEMU's default rv64 CPU has no Smepmp and the
                              read traps.  The Rocq model implements it.
     mstateen0 (0x30C),       Smstateen: QEMU traps.
     sstateen0 (0x10C)
     scountovf (0xDA0),       Smcdeleg / Smcntrpmf: QEMU traps.
     mcyclecfg (0x321),
     minstretcfg (0x322)
     ssp (0x011)              Zicfiss: QEMU traps.
   The counters live in core_regs_ctr (they do not settle), the PMP file in
   core_regs_pmp, the S-mode file in core_regs_scsr.

   RESULT LAYOUT (mirrored in vtest-rocq/CoreRegsMcsr.v); each is one 8-byte
   little-endian word:
     +0   done                +4   status = 1
     +8   mstatus  0x300      +16  misa          0x301
     +24  medeleg  0x302      +32  mideleg       0x303
     +40  mie      0x304      +48  mtvec         0x305
     +56  mcounteren 0x306    +64  menvcfg       0x30A
     +72  mcountinhibit 0x320 +80  mscratch      0x340
     +88  mepc     0x341      +96  mcause        0x342
     +104 mtval    0x343      +112 mip           0x344
     +120 mvendorid 0xF11     +128 marchid       0xF12
     +136 mimpid   0xF13      +144 mhartid       0xF14
     +152 mconfigptr 0xF15    +160 tselect       0x7A0  */
#include "abi.h"

    .globl _vtest_body
_vtest_body:
    csrr t0, 0x300
    sd   t0, 8(s11)
    csrr t0, 0x301
    sd   t0, 16(s11)
    csrr t0, 0x302
    sd   t0, 24(s11)
    csrr t0, 0x303
    sd   t0, 32(s11)
    csrr t0, 0x304
    sd   t0, 40(s11)
    csrr t0, 0x305
    sd   t0, 48(s11)
    csrr t0, 0x306
    sd   t0, 56(s11)
    csrr t0, 0x30A
    sd   t0, 64(s11)
    csrr t0, 0x320
    sd   t0, 72(s11)
    csrr t0, 0x340
    sd   t0, 80(s11)
    csrr t0, 0x341
    sd   t0, 88(s11)
    csrr t0, 0x342
    sd   t0, 96(s11)
    csrr t0, 0x343
    sd   t0, 104(s11)
    csrr t0, 0x344
    sd   t0, 112(s11)
    csrr t0, 0xF11
    sd   t0, 120(s11)
    csrr t0, 0xF12
    sd   t0, 128(s11)
    csrr t0, 0xF13
    sd   t0, 136(s11)
    csrr t0, 0xF14
    sd   t0, 144(s11)
    csrr t0, 0xF15
    sd   t0, 152(s11)
    csrr t0, 0x7A0
    sd   t0, 160(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)
    ret
