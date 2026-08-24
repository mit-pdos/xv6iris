/* core_regs_gpr -- THE 31 GENERAL-PURPOSE REGISTERS AS THEY ARE AT ENTRY.
   "Just dump everything into memory and compare memory snapshots": this is
   that dump for the integer register file.

   WHAT "AT ENTRY" MEANS.  vtest.S's prologue has already run, so five
   registers are NOT power-on values but values the prologue itself wrote:

     x1  ra  = the return address of `jal ra, _vtest_body` (an image address)
     x2  sp  = STACK_BASE + STACK_SIZE - (hartid << 11)   (prologue)
     x5  t0  = mhartid                                    (prologue, csrr)
     x6  t1  = STACK_BASE + STACK_SIZE                    (prologue, li)
     x7  t2  = hartid << 11                               (prologue, slli)
     x27 s11 = RESULT_BASE                                (prologue, li)

   Every OTHER register still holds exactly what the machine handed the image
   at 0x80000000, which is the thing under test.  Nothing here clobbers a
   register before it is stored: the body is 31 stores, and only afterwards
   does it touch t0 to publish the status word.

   RESULT LAYOUT (mirrored in vtest-rocq/CoreRegsGpr.v):
     +0    done flag
     +4    status = 1
     +8    x1 ..  +248 x31, one 8-byte little-endian word each:
           x_i is at RES_PAYLOAD + 8*(i-1) = 8*i.
   (x0 is not stored: it is architecturally zero.) */
#include "abi.h"

    .globl _vtest_body
_vtest_body:
    sd  x1,  8(s11)
    sd  x2,  16(s11)
    sd  x3,  24(s11)
    sd  x4,  32(s11)
    sd  x5,  40(s11)
    sd  x6,  48(s11)
    sd  x7,  56(s11)
    sd  x8,  64(s11)
    sd  x9,  72(s11)
    sd  x10, 80(s11)
    sd  x11, 88(s11)
    sd  x12, 96(s11)
    sd  x13, 104(s11)
    sd  x14, 112(s11)
    sd  x15, 120(s11)
    sd  x16, 128(s11)
    sd  x17, 136(s11)
    sd  x18, 144(s11)
    sd  x19, 152(s11)
    sd  x20, 160(s11)
    sd  x21, 168(s11)
    sd  x22, 176(s11)
    sd  x23, 184(s11)
    sd  x24, 192(s11)
    sd  x25, 200(s11)
    sd  x26, 208(s11)
    sd  x27, 216(s11)
    sd  x28, 224(s11)
    sd  x29, 232(s11)
    sd  x30, 240(s11)
    sd  x31, 248(s11)
    /* only now is a register clobbered, and t0 (x5) is already stored */
    li  t0, 1
    sw  t0, RES_STATUS(s11)
    ret
