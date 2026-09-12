/* uart1_both -- THE QUESTION ONLY A TWO-PORT MACHINE CAN ASK: are the two
 * 16550s two DEVICES, or one device behind two windows?
 *
 * Every other uart case would pass against a model with a single
 * [uart_state] aliased at both bases -- they only ever touch one port, so
 * "the register file is per port" is invisible to them.  This case makes it
 * visible from both sides at once:
 *
 *  (a) THE WIRES.  Two different strings are transmitted BYTE BY BYTE,
 *      alternating between the ports, so the two tx FIFOs are non-empty at
 *      the same time and the drains interleave.  The capture records what
 *      left each port SEPARATELY, and the claim [VRun.observed_at] makes is
 *      TOTAL over ports -- it says what BOTH wires hold -- so a byte the
 *      model put on the wrong port is a violation, not an omission.  The
 *      two strings share no byte value at any position, so a swap cannot
 *      hide.
 *
 *  (b) THE REGISTERS.  The two ports are given DIFFERENT scratch bytes and
 *      DIFFERENT MCRs and both are read back afterwards, so a shared
 *      register would report the last write on both.  The FIFOs are enabled
 *      on port 0 ALONE and the ISRs of both are read: port 0's carries the
 *      FIFO bits 7:6 and port 1's does not.  The THRE interrupt is enabled
 *      in port 1's IER ALONE and both ISRs are read again: port 1 names
 *      THRE, port 0 does not.  Each of those is a bit that lives in the
 *      per-port state, so each of them separates the two models.
 *
 * NO INTERRUPT IS ROUTED.  Nothing is enabled at the PLIC and we are in
 * M-mode with interrupts off, so IER here only moves the ISR; uart1_irq is
 * where the second port's line reaches the controller.
 *
 * RESULT layout:
 *   +8   port 0 SCRATCH read back                 (0x11)
 *   +12  port 1 SCRATCH read back                 (0x22)
 *   +16  port 0 MCR read back                     (0x03: DTR|RTS)
 *   +20  port 1 MCR read back                     (0x0c: OUT1|OUT2)
 *   +24  port 0 ISR, FIFOs enabled on port 0      (0xc1)
 *   +28  port 1 ISR, its FCR never written        (0x01)
 *   +32  bytes written to port 0                  (11)
 *   +36  bytes written to port 1                  (11)
 *   +40  port 0 LSR once both have drained        (0x60)
 *   +44  port 1 LSR once both have drained        (0x60)
 *   +48  port 0 ISR while port 1's IER = 0x02     (0xc1: not THRE)
 *   +52  port 1 ISR with its own IER = 0x02       (0x02: THRE)
 *   +56  port 0 SCRATCH re-read at the end        (0x11)
 *   +60  port 1 SCRATCH re-read at the end        (0x22)
 *
 * The two wires are the other half of the result, and they are exactly
 *   port 0: "P0=ABCDEFGH"      port 1: "p1-abcdefgh"
 */
/* vtest: repeat=1 platforms=qemu uarts=2 */
#include "abi.h"

#define R_SCR0    8
#define R_SCR1    12
#define R_MCR0    16
#define R_MCR1    20
#define R_ISR0    24
#define R_ISR1    28
#define R_N0      32
#define R_N1      36
#define R_LSR0    40
#define R_LSR1    44
#define R_ISR0B   48
#define R_ISR1B   52
#define R_SCR0B   56
#define R_SCR1B   60

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
    li   s0, UART0
    li   s1, UART1

/* ---- (b1) two scratch registers, written in one order, read in the other.
 * A single shared byte answers 0x22 twice. ---- */
    li   t0, 0x11
    sb   t0, UART_REG(7)(s0)
    li   t0, 0x22
    sb   t0, UART_REG(7)(s1)
    lbu  t0, UART_REG(7)(s0)
    sw   t0, R_SCR0(s11)
    lbu  t0, UART_REG(7)(s1)
    sw   t0, R_SCR1(s11)

/* ---- (b2) two modem control registers ---- */
    li   t0, 0x03                    /* DTR|RTS */
    sb   t0, UART_REG(4)(s0)
    li   t0, 0x0c                    /* OUT1|OUT2 -- deliberately NOT LOOP */
    sb   t0, UART_REG(4)(s1)
    lbu  t0, UART_REG(4)(s0)
    sw   t0, R_MCR0(s11)
    lbu  t0, UART_REG(4)(s1)
    sw   t0, R_MCR1(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- (b3) enable the FIFOs on PORT 0 ONLY, and read both ISRs.  Bits 7:6
 * come from FCR bit 0, and FCR is per port. ---- */
    li   t0, 0x07                    /* FIFO enable + clear rx + clear tx */
    sb   t0, UART_REG(2)(s0)
    lbu  t0, UART_REG(2)(s0)
    sw   t0, R_ISR0(s11)
    lbu  t0, UART_REG(2)(s1)
    sw   t0, R_ISR1(s11)
    li   t0, 2
    sw   t0, RES_STATUS(s11)

/* ---- (a) the interleaved transmit.  One byte to port 0, one byte to
 * port 1, round and round: both transmitters are busy at once. ---- */
    lla  s2, uart1_both_m0
    lla  s3, uart1_both_m1
    li   s4, 0                       /* bytes written to port 0 */
    li   s5, 0                       /* bytes written to port 1 */
1:  lbu  t1, 0(s2)
    beqz t1, 3f
2:  lbu  t0, UART_REG(5)(s0)
    andi t0, t0, 0x20                /* THRE, port 0 */
    beqz t0, 2b
    sb   t1, UART_REG(0)(s0)
    addi s2, s2, 1
    addi s4, s4, 1
3:  lbu  t1, 0(s3)
    beqz t1, 4f
5:  lbu  t0, UART_REG(5)(s1)
    andi t0, t0, 0x20                /* THRE, port 1 */
    beqz t0, 5b
    sb   t1, UART_REG(0)(s1)
    addi s3, s3, 1
    addi s5, s5, 1
4:  lbu  t1, 0(s2)
    bnez t1, 1b
    lbu  t1, 0(s3)
    bnez t1, 1b

/* ---- both transmitters idle ---- */
6:  lbu  t0, UART_REG(5)(s0)
    andi t0, t0, 0x40                /* TEMT, port 0 */
    beqz t0, 6b
7:  lbu  t0, UART_REG(5)(s1)
    andi t0, t0, 0x40                /* TEMT, port 1 */
    beqz t0, 7b
    sw   s4, R_N0(s11)
    sw   s5, R_N1(s11)
    lbu  t0, UART_REG(5)(s0)
    sw   t0, R_LSR0(s11)
    lbu  t0, UART_REG(5)(s1)
    sw   t0, R_LSR1(s11)
    li   t0, 3
    sw   t0, RES_STATUS(s11)

/* ---- (b4) the THRE interrupt enabled in PORT 1's IER ONLY.  Port 0's
 * transmitter is just as idle, but its IER is 0, so its ISR must not name
 * THRE.  A shared IER would make both report it. ---- */
    li   t0, 0x02
    sb   t0, UART_REG(1)(s1)
    lbu  t0, UART_REG(2)(s0)
    sw   t0, R_ISR0B(s11)
    lbu  t0, UART_REG(2)(s1)
    sw   t0, R_ISR1B(s11)
    sb   zero, UART_REG(1)(s1)                 /* IER off again */

/* ---- (b5) ...and neither port's scratch byte moved under all of that ---- */
    lbu  t0, UART_REG(7)(s0)
    sw   t0, R_SCR0B(s11)
    lbu  t0, UART_REG(7)(s1)
    sw   t0, R_SCR1B(s11)
    li   t0, 4
    sw   t0, RES_STATUS(s11)

    mv   ra, s10
    ret

uart1_both_m0:
    .ascii "P0=ABCDEFGH"
    .byte 0
    .align 2
uart1_both_m1:
    .ascii "p1-abcdefgh"
    .byte 0
    .align 2
