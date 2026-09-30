/* uart1_tx -- the TRANSMIT path of the SECOND 16550, at 0x1000a000.
 *
 * uart_tx asks these questions of port 0; this asks the identical questions
 * of port 1, so that a difference between the two answers is a difference
 * between the PORTS and not between two test programs.  What it pins on the
 * model side is that [uart_write] offset 0, [uart_tx_pop] and [uart_lsr]
 * are reached at the SECOND window -- i.e. that [uart_decode] routes
 * 0x1000a000..+8 to [Uart1] and that [duart] really is indexed.
 *
 * THE MESSAGE IS DISTINCTIVE ON PURPOSE.  The two ports' wires are captured
 * separately and compared separately, so a model that put port 1's bytes on
 * port 0's wire has to fail on the wire and not on a result word -- which
 * it can only do if the two wires never carry the same string.  Nothing
 * this program writes appears in any uart_ case.
 *
 * RESULT layout (mirrored in the generated Test/Run modules):
 *   +8   LSR before anything has been written        (expect 0x60: THRE|TEMT)
 *   +12  LSR after the whole string has drained      (expect 0x60)
 *   +16  the number of bytes written                 (expect 21)
 *   +20  LSR read IMMEDIATELY after a THR store, no poll in between
 *   +24  LSR after polling TEMT again at the very end
 *   +28  LSR after a 24-byte BURST with no polling at all
 *   +32  port 0's LSR, read once, never written to   (expect 0x60)
 */
/* vtest: repeat=1 platforms=qemu uarts=2 */
#include "abi.h"

#define R_LSR0    8
#define R_LSR1    12
#define R_NBYTES  16
#define R_LSRHOT  20
#define R_LSR2    24
#define R_LSR3    28
#define R_LSR00   32

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
    li   s0, UART1

    lbu  t0, UART_REG(5)(s0)
    sw   t0, R_LSR0(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- the polled-transmit loop, on port 1 ---- */
    lla  s1, uart1_tx_msg
    li   s2, 0
1:  lbu  t1, 0(s1)
    beqz t1, 3f
2:  lbu  t0, UART_REG(5)(s0)
    andi t0, t0, 0x20                /* THRE */
    beqz t0, 2b
    sb   t1, UART_REG(0)(s0)
    addi s1, s1, 1
    addi s2, s2, 1
    j    1b

3:  /* wait for the transmitter to go idle (TEMT), then look at LSR */
4:  lbu  t0, UART_REG(5)(s0)
    andi t0, t0, 0x40                /* TEMT */
    beqz t0, 4b
    lbu  t0, UART_REG(5)(s0)
    sw   t0, R_LSR1(s11)
    sw   s2, R_NBYTES(s11)
    li   t0, 2
    sw   t0, RES_STATUS(s11)

/* ---- one more byte, and LSR read with NO poll in between ---- */
    li   t1, 0x7a                    /* 'z' */
    sb   t1, UART_REG(0)(s0)
    lbu  t0, UART_REG(5)(s0)
    sw   t0, R_LSRHOT(s11)
5:  lbu  t0, UART_REG(5)(s0)
    andi t0, t0, 0x40
    beqz t0, 5b
    lbu  t0, UART_REG(5)(s0)
    sw   t0, R_LSR2(s11)
    li   t0, 3
    sw   t0, RES_STATUS(s11)

/* ---- a BURST with no THRE poll at all: 24 bytes back to back ---- */
    li   t2, 0x41                    /* 'A' */
    li   t3, 24
6:  sb   t2, UART_REG(0)(s0)
    addi t2, t2, 1
    addi t3, t3, -1
    bnez t3, 6b
7:  lbu  t0, UART_REG(5)(s0)
    andi t0, t0, 0x40
    beqz t0, 7b
    lbu  t0, UART_REG(5)(s0)
    sw   t0, R_LSR3(s11)

/* ---- and port 0, which this program has never written to ---- */
    li   s3, UART0
    lbu  t0, UART_REG(5)(s3)
    sw   t0, R_LSR00(s11)
    li   t0, 4
    sw   t0, RES_STATUS(s11)

    mv   ra, s10
    ret

uart1_tx_msg:
    .ascii "uart1_tx: second port"
    .byte 0
    .align 2
