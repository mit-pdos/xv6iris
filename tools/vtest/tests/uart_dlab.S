/* uart_dlab -- the DIVISOR-LATCH ALIASING, which is the highest-value thing
 * to pin down in this area.
 *
 * LCR (offset 3) bit 7 is DLAB.  While it is set, offset 0 is NOT the
 * transmit register but the divisor latch low byte, and offset 1 is not IER
 * but the divisor latch high byte.  So the SAME store instruction either
 * sends a character or programs the baud rate depending on a bit written
 * three instructions earlier.  The whole [un_dlab] ghost in the device
 * design (claude-notes/design/device.md) exists to track that, and the
 * model's [uart_dlab]/[uart_read]/[uart_write] implement it; this test is
 * what says the hardware really behaves that way.
 *
 * The serial channel is the sharp end: 'N' (0x4e) is stored to offset 0 with
 * DLAB SET and must NOT appear on the wire, and 'Y' (0x59) is stored to the
 * same offset with DLAB CLEAR and must.  So the whole captured serial output
 * of this test is exactly one byte, "Y".
 *
 * RESULT layout (mirrored in vtest-rocq/UartDlab.v):
 *   +8   LCR read back after writing 0x80        (expect 0x80)
 *   +12  offset 0 read with DLAB set   = DLL     (expect 0x03, just written)
 *   +16  offset 1 read with DLAB set   = DLM     (expect 0x12, just written)
 *   +20  offset 0 read after storing 'N' to it   (expect 0x4e: it went to DLL)
 *   +24  LCR read back after writing 0x03        (expect 0x03, DLAB clear)
 *   +28  offset 1 read with DLAB clear = IER     (expect 0x00: DLM writes did
 *                                                 not land in IER)
 *   +32  offset 0 read with DLAB clear = RHR     (expect 0x00: no input)
 *   +36  LSR at the end                          (expect 0x60)
 */
/* vtest: repeat=1 */
#include "abi.h"

#define R_LCR1   8
#define R_DLL    12
#define R_DLM    16
#define R_DLL2   20
#define R_LCR2   24
#define R_IER    28
#define R_RHR    32
#define R_LSR    36

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
    li   s0, UART0

/* ---- DLAB set: offset 0/1 are the divisor latches ---- */
    li   t0, 0x80
    sb   t0, 3(s0)
    lbu  t0, 3(s0)
    sw   t0, R_LCR1(s11)

    li   t0, 0x03
    sb   t0, 0(s0)                   /* DLL = 3 */
    li   t0, 0x12
    sb   t0, 1(s0)                   /* DLM = 0x12 */
    lbu  t0, 0(s0)
    sw   t0, R_DLL(s11)
    lbu  t0, 1(s0)
    sw   t0, R_DLM(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- the aliased store: 'N' to offset 0 while DLAB is set ----
 * It must land in DLL and never reach the wire. */
    li   t0, 0x4e                    /* 'N' */
    sb   t0, 0(s0)
    lbu  t0, 0(s0)
    sw   t0, R_DLL2(s11)
    li   t0, 2
    sw   t0, RES_STATUS(s11)

/* ---- DLAB clear: offset 0/1 are THR/RHR and IER again ---- */
    li   t0, 0x03                    /* 8N1, DLAB clear */
    sb   t0, 3(s0)
    lbu  t0, 3(s0)
    sw   t0, R_LCR2(s11)
    lbu  t0, 1(s0)
    sw   t0, R_IER(s11)
    lbu  t0, 0(s0)
    sw   t0, R_RHR(s11)

/* ---- and now the same store instruction DOES transmit ---- */
1:  lbu  t0, 5(s0)
    andi t0, t0, 0x20
    beqz t0, 1b
    li   t0, 0x59                    /* 'Y' */
    sb   t0, 0(s0)
2:  lbu  t0, 5(s0)
    andi t0, t0, 0x40
    beqz t0, 2b
    lbu  t0, 5(s0)
    sw   t0, R_LSR(s11)
    li   t0, 3
    sw   t0, RES_STATUS(s11)

    mv   ra, s10
    ret
