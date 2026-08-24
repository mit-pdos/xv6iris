/* core_regs_scsr -- THE S-MODE CSRs AT BOOT, read from M-mode (which is
   allowed: M can read anything S can).  Nothing is written.

   Not here, because QEMU's default rv64 CPU traps on the read (probed one
   per image): sstateen0 (0x10C).  stimecmp (0x14D) IS here -- QEMU's default
   CPU has Sstc -- and is the one entry whose value is a clock, so read the
   note in vtest-rocq/CoreRegsScsr.v before trusting it.

   RESULT LAYOUT (mirrored in vtest-rocq/CoreRegsScsr.v); 8-byte words:
     +0   done               +4   status = 1
     +8   sstatus  0x100     +16  sie      0x104
     +24  stvec    0x105     +32  scounteren 0x106
     +40  senvcfg  0x10A     +48  sscratch 0x140
     +56  sepc     0x141     +64  scause   0x142
     +72  stval    0x143     +80  sip      0x144
     +88  satp     0x180     +96  stimecmp 0x14D  */
#include "abi.h"

    .globl _vtest_body
_vtest_body:
    csrr t0, 0x100
    sd   t0, 8(s11)
    csrr t0, 0x104
    sd   t0, 16(s11)
    csrr t0, 0x105
    sd   t0, 24(s11)
    csrr t0, 0x106
    sd   t0, 32(s11)
    csrr t0, 0x10A
    sd   t0, 40(s11)
    csrr t0, 0x140
    sd   t0, 48(s11)
    csrr t0, 0x141
    sd   t0, 56(s11)
    csrr t0, 0x142
    sd   t0, 64(s11)
    csrr t0, 0x143
    sd   t0, 72(s11)
    csrr t0, 0x144
    sd   t0, 80(s11)
    csrr t0, 0x180
    sd   t0, 88(s11)
    csrr t0, 0x14D
    sd   t0, 96(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)
    ret
