/* uart_loop -- MCR, and the one bit of it with semantics: LOOPBACK.
 *
 * MCR bit 4 disconnects the transmitter from SOUT and wires it to this
 * UART's own receiver, and wires the four modem OUTPUTS to the four modem
 * INPUTS (DTR->DSR, RTS->CTS, OUT1->RI, OUT2->DCD).  It is the standard way
 * to self-test a 16550 and the only way to exercise the receive path on a
 * port nobody is typing at, which is why a model whose MCR swallowed its
 * writes (finding 6) could not describe a driver that does either.
 *
 * THE SERIAL CHANNEL IS HALF THE TEST.  The byte transmitted under LOOP must
 * come back on RHR and must NOT reach the host; the byte transmitted after
 * LOOP is cleared must reach the host and must not come back.  So the
 * expected serial output is exactly "Y", and a model that let the loopbacked
 * 'A' onto the wire fails on that line rather than on a result word.
 *
 * RESULT layout (mirrored in vtest-rocq/UartLoop.v):
 *   +8   MCR at power-on                                 8   (OUT2)
 *   +12  MCR read back after storing 0xff                0x1f (five bits)
 *   +16  MSR with LOOP|RTS|DTR                           0x30 (DSR|CTS)
 *   +20  MSR with LOOP and all four outputs driven       0xf0 (all four in)
 *   +24  LSR after a THR write under LOOP                0x61 (DR is set)
 *   +28  RHR: the byte, back from our own transmitter    0x41 'A'
 *   +32  LSR after that read                             0x60 (DR gone)
 *   +36  MSR with LOOP cleared again                     0xb0 (the cable)
 *   +40  LSR at the end                                  0x60
 */
/* vtest: repeat=1 */
#include "abi.h"

#define R_MCR0    8
#define R_MCRFF   12
#define R_MSRL1   16
#define R_MSRL2   20
#define R_LSRD    24
#define R_RHR     28
#define R_LSRE    32
#define R_MSR0    36
#define R_LSRF    40

    .globl _vtest_body
_vtest_body:
    mv   s10, ra
    li   s0, UART0

/* ---- MCR is five bits of storage ---- */
    lbu  t0, 4(s0)
    sw   t0, R_MCR0(s11)
    li   t0, 0xff
    sb   t0, 4(s0)
    lbu  t0, 4(s0)
    sw   t0, R_MCRFF(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)

/* ---- the modem outputs, looped back to the inputs ---- */
    li   t0, 0x13                    /* LOOP|RTS|DTR */
    sb   t0, 4(s0)
    lbu  t0, 6(s0)
    sw   t0, R_MSRL1(s11)
    li   t0, 0x1f                    /* LOOP|OUT2|OUT1|RTS|DTR */
    sb   t0, 4(s0)
    lbu  t0, 6(s0)
    sw   t0, R_MSRL2(s11)
    li   t0, 2
    sw   t0, RES_STATUS(s11)

/* ---- the DATA path: 'A' goes out and comes straight back in.  SPIN on DR:
 * the return trip is the device's own step, not a side effect of the
 * store ---- */
    li   t0, 0x41                    /* 'A' */
    sb   t0, 0(s0)
1:  lbu  t0, 5(s0)
    andi t0, t0, 0x01
    beqz t0, 1b
    lbu  t0, 5(s0)
    sw   t0, R_LSRD(s11)
    lbu  t0, 0(s0)
    sw   t0, R_RHR(s11)
    lbu  t0, 5(s0)
    sw   t0, R_LSRE(s11)
    li   t0, 3
    sw   t0, RES_STATUS(s11)

/* ---- out of loopback: the port is a port again, and 'Y' reaches the host
 * while 'A' never did ---- */
    li   t0, 0x03                    /* LOOP clear */
    sb   t0, 4(s0)
    lbu  t0, 6(s0)
    sw   t0, R_MSR0(s11)
2:  lbu  t0, 5(s0)
    andi t0, t0, 0x20
    beqz t0, 2b
    li   t0, 0x59                    /* 'Y' */
    sb   t0, 0(s0)
3:  lbu  t0, 5(s0)
    andi t0, t0, 0x40                /* TEMT: it has left the transmitter */
    beqz t0, 3b
    lbu  t0, 5(s0)
    sw   t0, R_LSRF(s11)
    li   t0, 4
    sw   t0, RES_STATUS(s11)

    mv   ra, s10
    ret
