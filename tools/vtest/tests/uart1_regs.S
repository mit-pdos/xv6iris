/* uart1_regs -- the eight registers of the SECOND 16550, at 0x1000a000.
 *
 * uart_regs asks these questions of port 0 (see its header for what each
 * one is FOR -- the SCRATCH presence test, MCR's five bits, MSR's modem
 * inputs, the ISR's FIFO bits before and after FCR, and the THRE LATCH read
 * twice).  This asks them again at the second window, so that "the register
 * file is per port" is a measurement and not an assumption: a model with
 * ONE [uart_state] behind two windows would answer these correctly and only
 * fail the cross-port half, which is uart1_both's job.  What this case
 * establishes on its own is that the second window has a register file at
 * ALL, with the same semantics as the first.
 *
 * The two ports are given DIFFERENT scratch values here and in uart1_both,
 * so a capture cannot be satisfied by reading the wrong port's byte.
 *
 * RESULT layout:
 *   +8   offset 7 read back after storing 0xa5   (SCRATCH; port 0 uses 0x5a)
 *   +12  offset 4 read back after storing 0x03   (MCR: DTR|RTS)
 *   +16  offset 6 read                           (MSR)
 *   +20  ISR at reset, IER = 0                   (no interrupt pending)
 *   +24  ISR after FCR = 0x07 (FIFO enable + clear both)
 *   +28  ISR with IER = 0x02 (THRE int enabled), FIRST read
 *   +32  ISR with IER = 0x02, SECOND read, nothing in between
 *   +36  IER read back                           (expect 0x02)
 *   +40  LSR after the FIFO-clearing FCR write   (expect 0x60)
 *   +44  LSR after "K1" has drained              (expect 0x60)
 *   +48  MCR at power-on, read BEFORE anything was written  (expect 8)
 */
/* vtest: repeat=1 platforms=qemu uarts=2 */
#include "abi.h"

#define R_SCR    8
#define R_MCR    12
#define R_MSR    16
#define R_ISR0   20
#define R_ISR1   24
#define R_ISR2   28
#define R_ISR3   32
#define R_IER    36
#define R_LSR1   40
#define R_LSR2   44
#define R_MCR0   48

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
    li   s0, UART1

/* ---- power-on MCR, before this program has written anything ---- */
    lbu  t0, UART_REG(4)(s0)
    sw   t0, R_MCR0(s11)

/* ---- (a) SCRATCH, MCR, MSR ---- */
    li   t0, 0xa5
    sb   t0, UART_REG(7)(s0)                   /* SCRATCH */
    lbu  t0, UART_REG(7)(s0)
    sw   t0, R_SCR(s11)
    li   t0, 0x03
    sb   t0, UART_REG(4)(s0)                   /* MCR: DTR|RTS, no loopback */
    lbu  t0, UART_REG(4)(s0)
    sw   t0, R_MCR(s11)
    lbu  t0, UART_REG(6)(s0)                   /* MSR */
    sw   t0, R_MSR(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- (b) the ISR ---- */
    lbu  t0, UART_REG(2)(s0)                   /* IER is still 0: nothing pending */
    sw   t0, R_ISR0(s11)
    li   t0, 0x07                    /* FCR: FIFO enable + clear rx + clear tx */
    sb   t0, UART_REG(2)(s0)
    lbu  t0, UART_REG(2)(s0)
    sw   t0, R_ISR1(s11)

    li   t0, 0x02                    /* IER: THRE interrupt enabled */
    sb   t0, UART_REG(1)(s0)
    lbu  t0, UART_REG(2)(s0)                   /* first ISR read: THRE is pending */
    sw   t0, R_ISR2(s11)
    lbu  t0, UART_REG(2)(s0)                   /* second, with nothing in between */
    sw   t0, R_ISR3(s11)
    lbu  t0, UART_REG(1)(s0)
    sw   t0, R_IER(s11)
    sb   zero, UART_REG(1)(s0)                 /* IER off again */
    li   t0, 2
    sw   t0, RES_STATUS(s11)

/* ---- (c) the FIFO-clearing write, and a transmit after it ---- */
    li   t0, 0x06                    /* FCR: clear rx + clear tx */
    sb   t0, UART_REG(2)(s0)
    lbu  t0, UART_REG(5)(s0)
    sw   t0, R_LSR1(s11)

1:  lbu  t0, UART_REG(5)(s0)
    andi t0, t0, 0x20
    beqz t0, 1b
    li   t0, 0x4b                    /* 'K' */
    sb   t0, UART_REG(0)(s0)
2:  lbu  t0, UART_REG(5)(s0)
    andi t0, t0, 0x20
    beqz t0, 2b
    li   t0, 0x31                    /* '1' */
    sb   t0, UART_REG(0)(s0)
3:  lbu  t0, UART_REG(5)(s0)
    andi t0, t0, 0x40
    beqz t0, 3b
    lbu  t0, UART_REG(5)(s0)
    sw   t0, R_LSR2(s11)
    li   t0, 3
    sw   t0, RES_STATUS(s11)

    mv   ra, s10
    ret
