/* uart_tx -- the TRANSMIT path of the 16550, through all THREE observation
 * channels: the result region, and (unique to this area) the SERIAL output
 * the host actually saw.
 *
 * The driver shape is the one xv6's uartputc_sync uses: poll LSR (offset 5)
 * for THRE (bit 5), then store the byte to THR (offset 0).  What the model
 * has to get right is [uart_write] offset 0 with DLAB clear (push onto the
 * tx FIFO), [uart_tx_pop] (the device's own drain onto the wire) and
 * [uart_lsr]'s THRE/TEMT bits -- and, through [uart_acc], that every byte
 * pushed is a byte transmitted.
 *
 * UART registers are BYTE registers: lbu/sb only.  A 4-byte access to the
 * window is a separate test (uart_width).
 *
 * RESULT layout (mirrored in vtest-rocq/UartTx.v):
 *   +8   LSR before anything has been written        (expect 0x60: THRE|TEMT)
 *   +12  LSR after the whole string has drained      (expect 0x60)
 *   +16  the number of bytes written                 (expect 20)
 *   +20  LSR read IMMEDIATELY after a THR store, no poll in between
 *   +24  LSR after polling TEMT again at the very end
 *   +28  LSR after a 24-byte BURST with no polling at all
 */
/* vtest: repeat=1 */
#include "abi.h"

#define R_LSR0    8
#define R_LSR1    12
#define R_NBYTES  16
#define R_LSRHOT  20
#define R_LSR2    24
#define R_LSR3    28

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
    li   s0, UART0

    lbu  t0, 5(s0)
    sw   t0, R_LSR0(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- the polled-transmit loop ---- */
    lla  s1, uart_tx_msg
    li   s2, 0
1:  lbu  t1, 0(s1)
    beqz t1, 3f
2:  lbu  t0, 5(s0)
    andi t0, t0, 0x20                /* THRE */
    beqz t0, 2b
    sb   t1, 0(s0)
    addi s1, s1, 1
    addi s2, s2, 1
    j    1b

3:  /* wait for the transmitter to go idle (TEMT), then look at LSR */
4:  lbu  t0, 5(s0)
    andi t0, t0, 0x40                /* TEMT */
    beqz t0, 4b
    lbu  t0, 5(s0)
    sw   t0, R_LSR1(s11)
    sw   s2, R_NBYTES(s11)
    li   t0, 2
    sw   t0, RES_STATUS(s11)

/* ---- one more byte, and LSR read with NO poll in between ----
 * The model's harness drains the tx FIFO after every instruction, so the
 * model reads THRE set here; whether the hardware does is the question. */
    li   t1, 0x5a                    /* 'Z' */
    sb   t1, 0(s0)
    lbu  t0, 5(s0)
    sw   t0, R_LSRHOT(s11)
5:  lbu  t0, 5(s0)
    andi t0, t0, 0x40
    beqz t0, 5b
    lbu  t0, 5(s0)
    sw   t0, R_LSR2(s11)
    li   t0, 3
    sw   t0, RES_STATUS(s11)

/* ---- a BURST with no THRE poll at all ----
 * 24 bytes stored to THR back to back.  The model's tx FIFO holds 16 and
 * [uart_write] DROPS a push into a full one, so this is the only shape in
 * which the depth could ever be observable -- see the note in
 * vtest-rocq/UartTx.v about why, under the harness's eager drain, it is not. */
    li   t2, 0x61                    /* 'a' */
    li   t3, 24
6:  sb   t2, 0(s0)
    addi t2, t2, 1
    addi t3, t3, -1
    bnez t3, 6b
7:  lbu  t0, 5(s0)
    andi t0, t0, 0x40
    beqz t0, 7b
    lbu  t0, 5(s0)
    sw   t0, R_LSR3(s11)
    li   t0, 4
    sw   t0, RES_STATUS(s11)

    mv   ra, s10
    ret

uart_tx_msg:
    .ascii "uart_tx: hello 16550"
    .byte 0
    .align 2
