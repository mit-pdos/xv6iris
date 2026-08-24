/* uart_rx -- THE RECEIVE DATAPATH: does the UART correctly receive bytes?
 *
 * uart_irq_rx receives one byte, but only as the condition that raises an
 * interrupt.  This test is about the FIFO itself: four bytes are pushed in
 * by the host (the `vtest:` directive below), three are read out one at a
 * time and checked for ORDER, and the fourth is still queued when an FCR
 * write clears the receive FIFO -- which is what makes the clear observable.
 *
 * WHY THE FIFOs ARE NEVER ENABLED HERE, deliberately.  Writing FCR bit 0
 * flips QEMU's 16550 from its one-byte holding register to its 16-byte FIFO,
 * and the transition FLUSHES: measured, the host's first byte is already in
 * the holding register by the time the guest's very first instructions run,
 * so an FCR FIFO-enable at the top of the program silently EATS it (the run
 * then reads 0x42 first, 8 times out of 8).  Leaving the FIFOs off costs one
 * thing -- QEMU's front end then hands over one character at a time and
 * re-offers the next only after the guest has read RHR, so "is LSR bit 0
 * still set immediately after a read?" is a race against the host rather
 * than a fact about the device, and this test does not ask it.  Order plus
 * a spin before each read establishes the same property without the race:
 * a one-deep register or a LIFO cannot produce 0x41, 0x42, 0x43 in that
 * order from four queued bytes, and a read that popped two would run the
 * queue dry and hang the spin.
 *
 * RESULT layout (mirrored in vtest-rocq/UartRx.v):
 *   +8   LSR with bytes waiting                    (0x61: DR|THRE|TEMT)
 *   +12  RHR #1                                    (0x41 'A')
 *   +16  RHR #2                                    (0x42 'B')
 *   +20  RHR #3                                    (0x43 'C')
 *   +24  LSR with the fourth byte still waiting     (0x61)
 *   +28  LSR after an FCR write with bit 1 set      (0x60: DR gone)
 *   +32  RHR on the FIFO that clear just emptied
 *   +36  LSR after that read                        (0x60)
 *   +40  how many bytes a drain loop still finds    (0)
 *   +44  LSR at the end                             (0x60)
 */
/* vtest: serial_in=0x41,0x42,0x43,0x44 */
#include "abi.h"

#define R_LSR0    8
#define R_B0      12
#define R_B1      16
#define R_B2      20
#define R_LSR1    24
#define R_LSRC    28
#define R_EMPTY   32
#define R_LSR2    36
#define R_DRAINN  40
#define R_LSR3    44

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
    li   s0, UART0

/* ---- the first byte, and the state it leaves LSR in ---- */
1:  lbu  t0, 5(s0)
    andi t0, t0, 0x01                /* DR */
    beqz t0, 1b
    lbu  t0, 5(s0)
    sw   t0, R_LSR0(s11)
    lbu  t0, 0(s0)                   /* RHR: pops one byte */
    sw   t0, R_B0(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- two more, in order ---- */
2:  lbu  t0, 5(s0)
    andi t0, t0, 0x01
    beqz t0, 2b
    lbu  t0, 0(s0)
    sw   t0, R_B1(s11)
3:  lbu  t0, 5(s0)
    andi t0, t0, 0x01
    beqz t0, 3b
    lbu  t0, 0(s0)
    sw   t0, R_B2(s11)
    li   t0, 2
    sw   t0, RES_STATUS(s11)

/* ---- the fourth is still queued: clear the receive FIFO out from under it ---- */
4:  lbu  t0, 5(s0)
    andi t0, t0, 0x01
    beqz t0, 4b
    lbu  t0, 5(s0)
    sw   t0, R_LSR1(s11)
    li   t0, 0x02                    /* FCR bit 1: clear the receive FIFO */
    sb   t0, 2(s0)
    lbu  t0, 5(s0)
    sw   t0, R_LSRC(s11)

/* ---- and what RHR gives back once the FIFO is empty ---- */
    lbu  t0, 0(s0)
    sw   t0, R_EMPTY(s11)
    lbu  t0, 5(s0)
    sw   t0, R_LSR2(s11)

/* ---- nothing is left to drain ---- */
    li   t3, 0
5:  lbu  t0, 5(s0)
    andi t0, t0, 0x01
    beqz t0, 6f
    lbu  t4, 0(s0)
    addi t3, t3, 1
    j    5b
6:  sw   t3, R_DRAINN(s11)
    lbu  t0, 5(s0)
    sw   t0, R_LSR3(s11)
    li   t0, 3
    sw   t0, RES_STATUS(s11)

    mv   ra, s10
    ret
