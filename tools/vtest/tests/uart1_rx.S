/* uart1_rx -- THE RECEIVE DATAPATH OF THE SECOND PORT.
 *
 * The shape is uart_rx's, at 0x1000a000 and fed by `serial1_in=`: four bytes
 * are pushed in by the host, three are read out one at a time and checked
 * for ORDER, and the fourth is still queued when an FCR write clears the
 * receive FIFO.  Read uart_rx's header for why the FIFOs are never enabled
 * here and why order-plus-a-spin is the race-free way to ask these
 * questions -- every word of it applies unchanged to this port.
 *
 * WHAT IS NEW HERE is that the bytes must arrive at PORT 1 and nowhere
 * else, which is the input half of the claim uart1_both makes about output:
 * the test also reads port 0's LSR while port 1's queue is full, and DR
 * must be clear there.  On the model side the host's bytes are [SUartRx
 * Uart1 b] schedule items, and the test's [uart_input] is a list of
 * (port, byte) pairs -- so a model that delivered them to port 0 would fail
 * the trace equation in [VRun.run_agrees] rather than quietly pass.
 *
 * RESULT layout:
 *   +8   LSR with bytes waiting                     (0x61: DR|THRE|TEMT)
 *   +12  RHR #1                                     (0x50 'P')
 *   +16  RHR #2                                     (0x51 'Q')
 *   +20  RHR #3                                     (0x52 'R')
 *   +24  LSR with the fourth byte still waiting      (0x61)
 *   +28  port 0's LSR at that same moment            (0x60: no DR)
 *   +32  LSR after an FCR write with bit 1 set       (0x60: DR gone)
 *   +36  RHR on the FIFO that clear just emptied
 *   +40  LSR after that read                         (0x60)
 *   +44  how many bytes a drain loop still finds     (0)
 *   +48  LSR at the end                              (0x60)
 */
/* vtest: serial1_in=0x50,0x51,0x52,0x53 platforms=qemu uarts=2 budget=50000 */
#include "abi.h"

#define R_LSR0    8
#define R_B0      12
#define R_B1      16
#define R_B2      20
#define R_LSR1    24
#define R_LSR00   28
#define R_LSRC    32
#define R_EMPTY   36
#define R_LSR2    40
#define R_DRAINN  44
#define R_LSR3    48

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
    li   s0, UART1
    li   s1, UART0

/* ---- the first byte, and the state it leaves LSR in ---- */
1:  lbu  t0, UART_REG(5)(s0)
    andi t0, t0, 0x01                /* DR */
    beqz t0, 1b
    lbu  t0, UART_REG(5)(s0)
    sw   t0, R_LSR0(s11)
    lbu  t0, UART_REG(0)(s0)                   /* RHR: pops one byte */
    sw   t0, R_B0(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- two more, in order ---- */
2:  lbu  t0, UART_REG(5)(s0)
    andi t0, t0, 0x01
    beqz t0, 2b
    lbu  t0, UART_REG(0)(s0)
    sw   t0, R_B1(s11)
3:  lbu  t0, UART_REG(5)(s0)
    andi t0, t0, 0x01
    beqz t0, 3b
    lbu  t0, UART_REG(0)(s0)
    sw   t0, R_B2(s11)
    li   t0, 2
    sw   t0, RES_STATUS(s11)

/* ---- the fourth is still queued.  Port 0 has nothing: nobody typed at it,
 * and port 1's queue is not port 0's. ---- */
4:  lbu  t0, UART_REG(5)(s0)
    andi t0, t0, 0x01
    beqz t0, 4b
    lbu  t0, UART_REG(5)(s0)
    sw   t0, R_LSR1(s11)
    lbu  t0, UART_REG(5)(s1)
    sw   t0, R_LSR00(s11)

/* ---- clear the receive FIFO out from under the fourth byte ---- */
    li   t0, 0x02                    /* FCR bit 1: clear the receive FIFO */
    sb   t0, UART_REG(2)(s0)
    lbu  t0, UART_REG(5)(s0)
    sw   t0, R_LSRC(s11)

/* ---- and what RHR gives back once the FIFO is empty ---- */
    lbu  t0, UART_REG(0)(s0)
    sw   t0, R_EMPTY(s11)
    lbu  t0, UART_REG(5)(s0)
    sw   t0, R_LSR2(s11)

/* ---- nothing is left to drain ---- */
    li   t3, 0
5:  lbu  t0, UART_REG(5)(s0)
    andi t0, t0, 0x01
    beqz t0, 6f
    lbu  t4, UART_REG(0)(s0)
    addi t3, t3, 1
    j    5b
6:  sw   t3, R_DRAINN(s11)
    lbu  t0, UART_REG(5)(s0)
    sw   t0, R_LSR3(s11)
    li   t0, 3
    sw   t0, RES_STATUS(s11)

    mv   ra, s10
    ret
