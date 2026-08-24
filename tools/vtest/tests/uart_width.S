/* uart_width -- the UART window at an access width the model does not decode.
 *
 * [DevModel.dev_read]/[dev_write] service the UART at width 1 ONLY: every
 * other [n] falls through to [None], which is a STUCK machine.  The hardware
 * has no such restriction -- QEMU's 16550 is a byte-wide device behind a
 * bus that splits a wider access -- so a driver that reads its four status
 * bytes with one `lw` completes on the machine and has NO model execution.
 *
 * The load is aligned (offset 4 -> MCR, LSR, MSR, SCRATCH) so that the only
 * thing under test is the WIDTH, not a misalignment trap.  Everything the
 * model can do happens before it: the byte-wide reads at +8 and +12 pin
 * where the model is when it stops.
 *
 * RESULT layout (mirrored in vtest-rocq/UartWidth.v):
 *   +8   LSR by a 1-byte read       (both machines: 0x60)
 *   +12  SCRATCH by a 1-byte read, after storing 0x5a
 *   +16  the 4-byte read at UART0+4 -- QEMU only; the model is STUCK here
 */
/* vtest: repeat=1 */
#include "abi.h"

#define R_LSR    8
#define R_SCR    12
#define R_WORD   16

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
    li   s0, UART0

    lbu  t0, 5(s0)
    sw   t0, R_LSR(s11)
    li   t0, 0x5a
    sb   t0, 7(s0)
    lbu  t0, 7(s0)
    sw   t0, R_SCR(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)

    lw   t0, 4(s0)                   /* <-- the model has no transition here */
    sw   t0, R_WORD(s11)
    li   t0, 2
    sw   t0, RES_STATUS(s11)

    mv   ra, s10
    ret
