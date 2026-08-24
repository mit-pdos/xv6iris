/* uart_width -- THE BUS NARROWS a wide access to ONE byte register.
 *
 * All eight of the 16550's registers are bytes inside a single aligned
 * doubleword, so reading the status word with one `lw` is a thing real
 * drivers do.  The question this test settles is what such an access MEANS,
 * and the answer is not the one a reader guesses: the bus does NOT gather
 * offsets 4..7 into a word.  It hands the access to the ONE register the
 * address names, zero-extends the byte on the way back, and takes the low
 * byte on the way in -- at 2, 4 and 8 bytes alike.
 *
 * Every access here is ALIGNED, so the only thing under test is the WIDTH.
 *
 * (The model used to decode this window at width 1 and refuse every other,
 * which made an ordinary `lw` of the status word a STUCK machine -- finding
 * 9.  It is now the narrowing above, which is why the fields below are
 * expected to AGREE rather than to record a divergence.)
 *
 * RESULT layout (mirrored in vtest-rocq/UartWidth.v):
 *   +8   LSR by a 1-byte read                            0x60
 *   +12  SCRATCH by a 1-byte read, after storing 0x5a    0x5a
 *   +16  4-byte read at UART0+4, MCR = 3                 3
 *   +20  2-byte read at UART0+6, MSR                     0xb0
 *   +24  2-byte read at UART0+4, MCR again               3
 *   +28  4-byte read at UART0+0 with DLAB set, DLL = 0x33   0x33
 *   +32  8-byte read at the same place, low word         0x33
 *   +36  ...and its high word                            0
 *   +40  MCR after a 4-byte STORE of 0x11223344 to +4    4  (0x44 & 0x1f)
 *   +44  DLL after a 2-byte STORE of 0xbeef to +0        0xef
 *   +48  DLM, which that store did NOT reach             0x44
 */
/* vtest: repeat=1 */
#include "abi.h"

#define R_LSR    8
#define R_SCR    12
#define R_W4     16
#define R_H6     20
#define R_H4     24
#define R_W0     28
#define R_D0LO   32
#define R_D0HI   36
#define R_MCRW   40
#define R_DLLW   44
#define R_DLMW   48

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
    li   s0, UART0

/* ---- the byte-wide baseline, so the wide reads have something to be
 * compared against ---- */
    lbu  t0, 5(s0)
    sw   t0, R_LSR(s11)
    li   t0, 0x5a
    sb   t0, 7(s0)                   /* SCRATCH */
    lbu  t0, 7(s0)
    sw   t0, R_SCR(s11)
    li   t0, 0x03
    sb   t0, 4(s0)                   /* MCR = DTR|RTS */
    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- wide READS.  If the bus gathered, +16 would carry the SCRATCH byte
 * this program just stored at +7; it does not. ---- */
    lw   t0, 4(s0)
    sw   t0, R_W4(s11)
    lhu  t0, 6(s0)
    sw   t0, R_H6(s11)
    lhu  t0, 4(s0)
    sw   t0, R_H4(s11)

    li   t0, 0x80
    sb   t0, 3(s0)                   /* LCR: DLAB, so offset 0 is DLL */
    li   t0, 0x33
    sb   t0, 0(s0)                   /* DLL = 0x33 */
    li   t0, 0x44
    sb   t0, 1(s0)                   /* DLM = 0x44 */
    lw   t0, 0(s0)
    sw   t0, R_W0(s11)
    ld   t0, 0(s0)                   /* eight bytes, one register */
    sw   t0, R_D0LO(s11)
    srli t0, t0, 32
    sw   t0, R_D0HI(s11)
    li   t0, 2
    sw   t0, RES_STATUS(s11)

/* ---- wide WRITES: the low byte lands, the rest is dropped ---- */
    li   t0, 0xbeef
    sh   t0, 0(s0)                   /* 2-byte store to DLL */
    lbu  t0, 0(s0)
    sw   t0, R_DLLW(s11)
    lbu  t0, 1(s0)                   /* DLM: untouched by it */
    sw   t0, R_DLMW(s11)
    sb   zero, 3(s0)                 /* LCR = 0: DLAB clear again */

    li   t0, 0x11223344
    sw   t0, 4(s0)                   /* 4-byte store to MCR */
    lbu  t0, 4(s0)
    sw   t0, R_MCRW(s11)
    li   t0, 3
    sw   t0, RES_STATUS(s11)

    mv   ra, s10
    ret
