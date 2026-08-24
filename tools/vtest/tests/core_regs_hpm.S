/* core_regs_hpm -- THE HARDWARE PERFORMANCE-MONITOR FILE AT BOOT.

   The last block of architecturally readable state on this hart: the sixteen
   implemented HPM counters, read through both their M-mode and their
   unprivileged aliases, and their sixteen event selectors.

   THE RANGE IS THE INTERSECTION, established by probing one CSR per image
   first.  QEMU's default rv64 CPU implements counters 3..18 (0xB03..0xB12
   and 0xC03..0xC12) and traps on 19..31; the RV32-only high halves
   (mcycleh 0xB80, cycleh 0xC80, ...) trap on both machines, being illegal at
   xlen = 64, so they are not read here.  The event selectors 0x323..0x33F
   are all present on QEMU; only the sixteen matching the counters are read,
   so that a divergence lines up with a counter.

   RESULT LAYOUT (mirrored in vtest-rocq/CoreRegsHpm.v); 8-byte words:
     +8   + 8*k   mhpmcounter<3+k>  (0xB03 + k), k = 0..15  ->  +8   .. +128
     +136 + 8*k   hpmcounter<3+k>   (0xC03 + k), k = 0..15  ->  +136 .. +256
     +264 + 8*k   mhpmevent<3+k>    (0x323 + k), k = 0..15  ->  +264 .. +384 */
#include "abi.h"

    .globl _vtest_body
_vtest_body:
    csrr t0, 0xB03          /* mhpmcounter3 */
    sd   t0, 8(s11)
    csrr t0, 0xB04          /* mhpmcounter4 */
    sd   t0, 16(s11)
    csrr t0, 0xB05          /* mhpmcounter5 */
    sd   t0, 24(s11)
    csrr t0, 0xB06          /* mhpmcounter6 */
    sd   t0, 32(s11)
    csrr t0, 0xB07          /* mhpmcounter7 */
    sd   t0, 40(s11)
    csrr t0, 0xB08          /* mhpmcounter8 */
    sd   t0, 48(s11)
    csrr t0, 0xB09          /* mhpmcounter9 */
    sd   t0, 56(s11)
    csrr t0, 0xB0A          /* mhpmcounter10 */
    sd   t0, 64(s11)
    csrr t0, 0xB0B          /* mhpmcounter11 */
    sd   t0, 72(s11)
    csrr t0, 0xB0C          /* mhpmcounter12 */
    sd   t0, 80(s11)
    csrr t0, 0xB0D          /* mhpmcounter13 */
    sd   t0, 88(s11)
    csrr t0, 0xB0E          /* mhpmcounter14 */
    sd   t0, 96(s11)
    csrr t0, 0xB0F          /* mhpmcounter15 */
    sd   t0, 104(s11)
    csrr t0, 0xB10          /* mhpmcounter16 */
    sd   t0, 112(s11)
    csrr t0, 0xB11          /* mhpmcounter17 */
    sd   t0, 120(s11)
    csrr t0, 0xB12          /* mhpmcounter18 */
    sd   t0, 128(s11)
    csrr t0, 0xC03          /* hpmcounter3 */
    sd   t0, 136(s11)
    csrr t0, 0xC04          /* hpmcounter4 */
    sd   t0, 144(s11)
    csrr t0, 0xC05          /* hpmcounter5 */
    sd   t0, 152(s11)
    csrr t0, 0xC06          /* hpmcounter6 */
    sd   t0, 160(s11)
    csrr t0, 0xC07          /* hpmcounter7 */
    sd   t0, 168(s11)
    csrr t0, 0xC08          /* hpmcounter8 */
    sd   t0, 176(s11)
    csrr t0, 0xC09          /* hpmcounter9 */
    sd   t0, 184(s11)
    csrr t0, 0xC0A          /* hpmcounter10 */
    sd   t0, 192(s11)
    csrr t0, 0xC0B          /* hpmcounter11 */
    sd   t0, 200(s11)
    csrr t0, 0xC0C          /* hpmcounter12 */
    sd   t0, 208(s11)
    csrr t0, 0xC0D          /* hpmcounter13 */
    sd   t0, 216(s11)
    csrr t0, 0xC0E          /* hpmcounter14 */
    sd   t0, 224(s11)
    csrr t0, 0xC0F          /* hpmcounter15 */
    sd   t0, 232(s11)
    csrr t0, 0xC10          /* hpmcounter16 */
    sd   t0, 240(s11)
    csrr t0, 0xC11          /* hpmcounter17 */
    sd   t0, 248(s11)
    csrr t0, 0xC12          /* hpmcounter18 */
    sd   t0, 256(s11)
    csrr t0, 0x323          /* mhpmevent3 */
    sd   t0, 264(s11)
    csrr t0, 0x324          /* mhpmevent4 */
    sd   t0, 272(s11)
    csrr t0, 0x325          /* mhpmevent5 */
    sd   t0, 280(s11)
    csrr t0, 0x326          /* mhpmevent6 */
    sd   t0, 288(s11)
    csrr t0, 0x327          /* mhpmevent7 */
    sd   t0, 296(s11)
    csrr t0, 0x328          /* mhpmevent8 */
    sd   t0, 304(s11)
    csrr t0, 0x329          /* mhpmevent9 */
    sd   t0, 312(s11)
    csrr t0, 0x32A          /* mhpmevent10 */
    sd   t0, 320(s11)
    csrr t0, 0x32B          /* mhpmevent11 */
    sd   t0, 328(s11)
    csrr t0, 0x32C          /* mhpmevent12 */
    sd   t0, 336(s11)
    csrr t0, 0x32D          /* mhpmevent13 */
    sd   t0, 344(s11)
    csrr t0, 0x32E          /* mhpmevent14 */
    sd   t0, 352(s11)
    csrr t0, 0x32F          /* mhpmevent15 */
    sd   t0, 360(s11)
    csrr t0, 0x330          /* mhpmevent16 */
    sd   t0, 368(s11)
    csrr t0, 0x331          /* mhpmevent17 */
    sd   t0, 376(s11)
    csrr t0, 0x332          /* mhpmevent18 */
    sd   t0, 384(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)
    ret
