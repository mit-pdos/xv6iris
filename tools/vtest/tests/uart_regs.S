/* uart_regs -- the eight registers, and the interrupt-status semantics.
 *
 * Three questions:
 *
 *  (a) offsets 4 (MCR), 6 (MSR) and 7 (SCRATCH).  [uart_read] used to return
 *      ZERO for all three and [uart_write] to accept and discard, which is
 *      finding 6.  A real 16550 has a scratch register at 7 that reads back
 *      whatever was stored -- the standard PRESENCE TEST -- and an MCR at 4
 *      that reads back five bits, whose bit 4 has real semantics
 *      (uart_loop.S).  MSR at 6 reports the port's modem inputs.
 *
 *  (b) the ISR (offset 2).  [uart_isr] used to be 0xc0 + (rx ? 4 : tx ? 2 :
 *      1): bits 7:6 ("FIFOs enabled") unconditionally, where the hardware
 *      sets them from FCR bit 0 (finding 7), and the transmit interrupt as
 *      a LEVEL, where the hardware LATCHES it and clears it on an ISR read
 *      (finding 8).  So this test reads the ISR before and after the FCR
 *      write, and TWICE in a row with IER bit 1 set.
 *
 *  (c) the FCR (offset 2, write).  Bit 1 clears the receive FIFO, bit 2 the
 *      transmit FIFO.  A FIFO-clearing write must not break the
 *      transmitter, so the test sends "OK" after one.
 *
 * RESULT layout (mirrored in vtest-rocq/UartRegs.v):
 *   +8   offset 7 read back after storing 0x5a   (SCRATCH)
 *   +12  offset 4 read back after storing 0x03   (MCR: DTR|RTS)
 *   +16  offset 6 read                           (MSR)
 *   +20  ISR at reset, IER = 0                   (no interrupt pending)
 *   +24  ISR after FCR = 0x07 (FIFO enable + clear both)
 *   +28  ISR with IER = 0x02 (THRE int enabled), FIRST read
 *   +32  ISR with IER = 0x02, SECOND read, nothing in between
 *   +36  IER read back                           (expect 0x02)
 *   +40  LSR after the FIFO-clearing FCR write   (expect 0x60)
 *   +44  LSR after "OK" has drained              (expect 0x60)
 */
/* vtest: repeat=1 */
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

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
    li   s0, UART0

/* ---- (a) the registers the model reads as zero ---- */
    li   t0, 0x5a
    sb   t0, 7(s0)                   /* SCRATCH */
    lbu  t0, 7(s0)
    sw   t0, R_SCR(s11)
    li   t0, 0x03
    sb   t0, 4(s0)                   /* MCR: DTR|RTS, no loopback */
    lbu  t0, 4(s0)
    sw   t0, R_MCR(s11)
    lbu  t0, 6(s0)                   /* MSR */
    sw   t0, R_MSR(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- (b) the ISR ---- */
    lbu  t0, 2(s0)                   /* IER is still 0: nothing pending */
    sw   t0, R_ISR0(s11)
    li   t0, 0x07                    /* FCR: FIFO enable + clear rx + clear tx */
    sb   t0, 2(s0)
    lbu  t0, 2(s0)
    sw   t0, R_ISR1(s11)

    li   t0, 0x02                    /* IER: THRE interrupt enabled */
    sb   t0, 1(s0)
    lbu  t0, 2(s0)                   /* first ISR read: THRE is pending */
    sw   t0, R_ISR2(s11)
    lbu  t0, 2(s0)                   /* second, with nothing in between */
    sw   t0, R_ISR3(s11)
    lbu  t0, 1(s0)
    sw   t0, R_IER(s11)
    sb   zero, 1(s0)                 /* IER off again */
    li   t0, 2
    sw   t0, RES_STATUS(s11)

/* ---- (c) the FIFO-clearing write, and a transmit after it ---- */
    li   t0, 0x06                    /* FCR: clear rx + clear tx */
    sb   t0, 2(s0)
    lbu  t0, 5(s0)
    sw   t0, R_LSR1(s11)

1:  lbu  t0, 5(s0)
    andi t0, t0, 0x20
    beqz t0, 1b
    li   t0, 0x4f                    /* 'O' */
    sb   t0, 0(s0)
2:  lbu  t0, 5(s0)
    andi t0, t0, 0x20
    beqz t0, 2b
    li   t0, 0x4b                    /* 'K' */
    sb   t0, 0(s0)
3:  lbu  t0, 5(s0)
    andi t0, t0, 0x40
    beqz t0, 3b
    lbu  t0, 5(s0)
    sw   t0, R_LSR2(s11)
    li   t0, 3
    sw   t0, RES_STATUS(s11)

    mv   ra, s10
    ret
