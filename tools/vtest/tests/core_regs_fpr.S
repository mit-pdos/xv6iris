/* core_regs_fpr -- THE FLOATING-POINT REGISTER FILE, plus the three fp CSRs.

   THE ONE PLACE THIS TEST HAS TO WRITE SOMETHING FIRST.  mstatus.FS is 0
   (Off) at boot on both machines, and with FS = Off every fp instruction --
   including `fsd` and a read of fcsr/fflags/frm -- is an illegal
   instruction.  So the body's FIRST act is `csrs mstatus, 0x2000`, which
   sets FS = Initial, and only then can the register file be dumped.  The fp
   registers themselves are untouched by that write, so what lands in the
   result region is still their power-on content; the three fp CSRs are read
   after the write, which is why fcsr's value is the one to read with care.

   RESULT LAYOUT (mirrored in vtest-rocq/CoreRegsFpr.v); 8-byte words:
     +0   done                 +4   status = 1
     +8 + 8*i   f<i>, i = 0..31   ->  +8 .. +256   (raw 64-bit pattern, fsd)
     +264 fcsr   0x003          +272 fflags 0x001
     +280 frm    0x002          +288 mstatus AFTER the FS write  */
#include "abi.h"

    .globl _vtest_body
_vtest_body:
    li   t0, 0x2000            /* mstatus.FS = 1 (Initial) */
    csrs mstatus, t0
    fsd  f0,  8(s11)
    fsd  f1,  16(s11)
    fsd  f2,  24(s11)
    fsd  f3,  32(s11)
    fsd  f4,  40(s11)
    fsd  f5,  48(s11)
    fsd  f6,  56(s11)
    fsd  f7,  64(s11)
    fsd  f8,  72(s11)
    fsd  f9,  80(s11)
    fsd  f10, 88(s11)
    fsd  f11, 96(s11)
    fsd  f12, 104(s11)
    fsd  f13, 112(s11)
    fsd  f14, 120(s11)
    fsd  f15, 128(s11)
    fsd  f16, 136(s11)
    fsd  f17, 144(s11)
    fsd  f18, 152(s11)
    fsd  f19, 160(s11)
    fsd  f20, 168(s11)
    fsd  f21, 176(s11)
    fsd  f22, 184(s11)
    fsd  f23, 192(s11)
    fsd  f24, 200(s11)
    fsd  f25, 208(s11)
    fsd  f26, 216(s11)
    fsd  f27, 224(s11)
    fsd  f28, 232(s11)
    fsd  f29, 240(s11)
    fsd  f30, 248(s11)
    fsd  f31, 256(s11)
    csrr t0, 0x003
    sd   t0, 264(s11)
    csrr t0, 0x001
    sd   t0, 272(s11)
    csrr t0, 0x002
    sd   t0, 280(s11)
    csrr t0, 0x300
    sd   t0, 288(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)
    ret
