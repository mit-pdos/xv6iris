/* core_regs_pmp -- THE PHYSICAL-MEMORY-PROTECTION REGISTER FILE AT BOOT.

   Both machines have sys_pmp_count = 16 entries, so this is pmpcfg0 /
   pmpcfg2 (rv64 packs eight entries per even-numbered cfg register) and
   pmpaddr0..15 -- the whole file, nothing sampled.

   These are the registers whose power-on value the spec's own [reset_pmp]
   establishes over ARBITRARY garbage (ArchReset.v's board list says so in
   as many words: pmpcfg is NOT a board obligation), so if the model matched
   QEMU here it did so from its own reset code, not from the power-on file.

   RESULT LAYOUT (mirrored in vtest-rocq/CoreRegsPmp.v); 8-byte words:
     +0   done            +4   status = 1
     +8   pmpcfg0  0x3A0  +16  pmpcfg2  0x3A2
     +24 + 8*i           pmpaddr<i>  (0x3B0 + i), i = 0..15  -> +24 .. +144 */
#include "abi.h"

    .globl _vtest_body
_vtest_body:
    csrr t0, 0x3A0
    sd   t0, 8(s11)
    csrr t0, 0x3A2
    sd   t0, 16(s11)
    csrr t0, 0x3B0
    sd   t0, 24(s11)
    csrr t0, 0x3B1
    sd   t0, 32(s11)
    csrr t0, 0x3B2
    sd   t0, 40(s11)
    csrr t0, 0x3B3
    sd   t0, 48(s11)
    csrr t0, 0x3B4
    sd   t0, 56(s11)
    csrr t0, 0x3B5
    sd   t0, 64(s11)
    csrr t0, 0x3B6
    sd   t0, 72(s11)
    csrr t0, 0x3B7
    sd   t0, 80(s11)
    csrr t0, 0x3B8
    sd   t0, 88(s11)
    csrr t0, 0x3B9
    sd   t0, 96(s11)
    csrr t0, 0x3BA
    sd   t0, 104(s11)
    csrr t0, 0x3BB
    sd   t0, 112(s11)
    csrr t0, 0x3BC
    sd   t0, 120(s11)
    csrr t0, 0x3BD
    sd   t0, 128(s11)
    csrr t0, 0x3BE
    sd   t0, 136(s11)
    csrr t0, 0x3BF
    sd   t0, 144(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)
    ret
