/* conc_mp -- MESSAGE PASSING: the litmus test that separates RVWMO from TSO.
 *
 * conc_sb (store buffering) separates TSO from SEQUENTIAL CONSISTENCY, and
 * it is what found finding 24: QEMU on an x86 host produces (0,0), which no
 * SC machine can, because the host is TSO and TSO permits a store to be
 * reordered past a later load.  That tells us the model is not SC-correct.
 * It tells us NOTHING about whether real RISC-V hardware is weaker still.
 *
 * RVWMO IS WEAKER THAN TSO.  TSO keeps store->store and load->load order and
 * relaxes only store->load; RVWMO relaxes all of them.  So the test that
 * separates them is the one whose forbidden-under-TSO outcome needs a
 * store->store or a load->load reordering:
 *
 *     writer:  X = 1 ; Y = 1              (no fence between)
 *     reader:  r1 = Y ; r2 = X            (no fence between)
 *
 *     (r1,r2) = (1,0)  --  "I saw the flag but not the data"
 *
 * Under TSO that is IMPOSSIBLE: the writer's two stores reach memory in
 * order, so Y=1 implies X=1 is already visible, and the reader's two loads
 * are performed in order, so having seen Y=1 it cannot then see a stale X.
 * Under RVWMO it is ALLOWED, by either reordering.  It is also the exact
 * shape of a real bug: it is why a lock release needs a release fence and
 * why xv6's acquire/release carry __sync_synchronize().
 *
 * SO THE THREE MACHINES SHOULD DISAGREE THREE WAYS, and that is the point:
 *   - the MODEL is sequentially consistent, so (1,0) is impossible;
 *   - QEMU on an x86 host is TSO, so (1,0) should be impossible THERE TOO
 *     -- which makes QEMU useless for finding this class of bug, and is why
 *     a board is worth the trouble;
 *   - the hardware is RVWMO and MAY produce it.
 * A (1,0) on the board with none on QEMU is a hardware behaviour that
 * neither the model NOR our previous reference machine can produce.
 *
 * IF IT DOES NOT APPEAR, THAT IS NOT A RESULT.  An in-order core like the
 * U74 may well never reorder these in this window -- its loads issue in
 * order and its store buffer may drain in order -- and a null result here
 * says only "not observed by this test at this timing", never "the machine
 * is TSO".  Report it as a count out of a run total, not as a property.
 *
 * IT RACES REPEATEDLY, AND EVERY ITERATION IS A REAL RACE.
 *
 * The obvious encoding -- a flag and a data word, both reset between rounds
 * -- needs the reader to be PHASE-ALIGNED with the writer for a given slot
 * to be contended at all, and resetting needs barriers that serialise the
 * two harts.  Measured on QEMU: 76 contended slots out of 5120, i.e. 98.5%
 * of the work bought nothing, and a reordering with probability 1% would
 * have needed a hundred runs to appear once.
 *
 * So there is no flag and no reset.  The writer stores a MONOTONIC SEQUENCE
 * NUMBER to both words, data first:
 *
 *     writer:  i = i+1 ; X = i ; Y = i          (forever, until told to stop)
 *     reader:  r1 = Y ; r2 = X                  (NITER times)
 *
 * X is written before Y on every iteration, so the writer's own sequence has
 * X at least as new as Y at every instant.  A reader that observes the two
 * in program order must therefore see
 *
 *     r2 >= r1        (the data is at least as new as the flag)
 *
 * and seeing r1 > r2 means Y was observed NEWER THAN X -- the stores, or the
 * loads, were reordered.  IMPOSSIBLE UNDER TSO.  ALLOWED UNDER RVWMO.
 *
 * That buys three things at once.  There is nothing to reset, so no barrier
 * and no zeroing pass, so both harts free-run at full speed on the same two
 * cache lines.  Every reader iteration observes some writer state, so every
 * iteration is a chance rather than one in sixty-five.  And the detector is
 * one unsigned compare, ACCUMULATED, so a SINGLE occurrence anywhere in the
 * run makes the published result differ -- which is the whole point: we do
 * not need to catch the machine at a known moment, only to notice that it
 * ever happened.
 *
 * THE WITNESS, beside the detector, is the count of iterations where
 * r1 != r2 at all: the reader caught the writer BETWEEN its two stores.
 * That is the number of genuine opportunities the run gave the machine, and
 * a null detector count is only meaningful beside a large witness count.
 *
 * X AND Y ARE ON SEPARATE CACHE LINES (64 bytes apart).  If they shared
 * one, a reader that saw the new Y would necessarily have the line carrying
 * the new X, and the forbidden outcome could never appear for a reason that
 * has nothing to do with the memory model.
 *
 * THE SECOND PASS IS THE CONTROL, and it is what makes a (1,0) in the first
 * pass believable: the same sweep with `fence w,w` between the stores and
 * `fence r,r` between the loads.  That outcome is forbidden on EVERY
 * machine, model included.  A (1,0) there means the harness is broken --
 * the slots alias, or the tally is wrong -- and not that the hardware is
 * exotic.
 *
 * RESULT layout (mirrored in vtest-rocq/ConcMp.v):
 *   +8    NITER, the reader's iterations per pass
 *   +12   pass 1 WITNESS   -- iterations where r1 != r2 (caught mid-pair)
 *   +16   pass 1 FORBIDDEN -- iterations where r1 >  r2   <-- RVWMO-only
 *   +20   pass 2 WITNESS   (fenced)
 *   +24   pass 2 FORBIDDEN (fenced)  <-- MUST BE 0 ON EVERY MACHINE
 *   +28   X as pass 1 ended    } the writer's sequence number: 0 here means
 *   +32   Y as pass 1 ended    } the writer never ran, see below
 *   +36   number of FORBIDDEN events logged (capped at LOGMAX)
 *   +0x200 + 16*k   event k: r1 (=Y), r2 (=X), the iteration, the pass
 *   +0x300 + 8*k    SAMPLE k: the RAW r1 and r2 of the first SMPMAX
 *                   iterations of pass 1, whatever they were.  The forbidden
 *                   log above is empty on a machine that never reorders, and
 *                   an empty log shows nothing about what the machine IS
 *                   doing; this shows the actual sequence numbers the reader
 *                   observed, so "how far apart are the two words in flight"
 *                   is answerable even when the answer to "did it reorder"
 *                   is no.
 *
 * THE LOG IS THE MAGNITUDE, and a bare count does not have it.  If the
 * machine ever does reorder, what matters is HOW FAR: r1 - r2 is the number
 * of sequence numbers by which the flag ran ahead of the data, i.e. how many
 * of the writer's iterations became visible out of order.  A difference of 1
 * is a single store slipping past its partner; a large one is a store buffer
 * draining a whole burst out of order, which is a different mechanism and a
 * different problem for a driver.  The iteration index says whether events
 * cluster (a cache-line transition) or scatter (a steady rate).
 *
 * The logging branch is on the NOT-TAKEN path in every run so far, so it
 * costs two instructions per iteration and does not disturb the timing that
 * makes the witness count high -- verified: the witness stayed at 100%.
 */
/* vtest: smp=2 repeat=1 builder=multi */
    .option norvc
#include "abi.h"

#define NITER     4096            /* reader iterations per pass */
/* WGAP nops between the writer's two stores.  This imposes NO ORDERING --
   nops are not fences -- it only widens the interval during which X has
   been written and Y has not, which is the interval the reader has to
   sample in for the observation to be about the pair at all.  Measured
   without it on QEMU: the witness count was ZERO over 20480 races, because
   the writer's unfenced loop is five instructions and the reader never
   landed inside it.  The READER's two loads are deliberately left ADJACENT:
   widening its gap would raise the witness too, but by making X strictly
   newer, which is the direction that HIDES the forbidden outcome. */
#define WGAP      12
#define XADDR     DMA_BASE        /* the DATA word              */
/* X AND Y ARE 1 KB APART, which is sixteen 64-byte cache lines on this core.
   64 would already put them in DIFFERENT lines, but adjacent is not
   independent: a next-line prefetcher pulls the neighbour and re-couples
   them, and adjacent lines also sit in adjacent L1 sets.  1 KB is clear of
   both, costs nothing (the declared DMA region is 8 KB), and removes the
   question. */
#define YOFFR     1024

#define R_NITER   8
#define R_P1WIT   12
#define R_P1BAD   16
#define R_P2WIT   20
#define R_P2BAD   24
#define R_LOGN    36              /* how many events were logged  */
#define LOGBASE   0x200           /* 16 entries x 16 bytes        */
#define LOGMAX    16
#define SMPBASE   0x300           /* the SAMPLE log: 32 entries x 8 bytes */
#define SMPMAX    32
#define STOP1     0x100           /* reader tells the writer to stop  */
#define STOP2     0x104
#define READY1    0x10c           /* writer has entered its UNFENCED loop */
#define READY2    0x108           /* writer has entered its FENCED loop   */

/* ---- the WRITER: store the sequence number to X then Y, forever, until
 * the reader says stop.  \fenced puts a w,w fence between them, which is
 * the control pass. ---- */
.macro WLOOP fenced, stop
    li   s2, 0
1:  addi s2, s2, 1
    sw   s2, 0(s3)                /* X = i  -- the DATA first */
.if \fenced
    fence w, w
.endif
    .rept WGAP
    nop
    .endr
    sw   s2, YOFFR(s3)            /* Y = i  -- then the FLAG  */
    lw   t0, \stop(s11)
    beqz t0, 1b
.endm

/* ---- the READER: r1 = Y, r2 = X, and accumulate.  Branch-free apart from
 * the loop, so nothing here depends on what was observed. ---- */
.macro RLOOP fenced
    li   s2, 0
    li   s7, 0                    /* witness:  r1 != r2 */
    li   s8, 0                    /* FORBIDDEN: r1 >  r2 */
2:  lw   t0, YOFFR(s3)            /* r1 = Y -- the FLAG first */
.if \fenced
    fence r, r
.endif
    lw   t1, 0(s3)                /* r2 = X -- then the DATA  */
    sltu t2, t1, t0               /* r2 < r1: the flag is NEWER than the
                                     data, which the writer's own order
                                     makes impossible to observe in order */
    add  s8, s8, t2
    beqz t2, 6f                   /* the common path: nothing to log */
    beqz s5, 6f                   /* ...or the log is full */
    sw   t0, 0(s4)                /* r1, the flag we saw  */
    sw   t1, 4(s4)                /* r2, the data we saw  */
    sw   s2, 8(s4)                /* which iteration      */
    sw   s6, 12(s4)               /* which pass           */
    addi s4, s4, 16
    addi s5, s5, -1
6:
    xor  t2, t0, t1
    snez t2, t2
    add  s7, s7, t2
    /* the RAW sample log: the first SMPMAX observations of this pass,
       unconditionally, so the numbers are visible even when nothing is
       forbidden.  Guarded by a counter, so it costs one branch after the
       first SMPMAX iterations. */
    beqz a2, 7f
    sw   t0, 0(a3)
    sw   t1, 4(a3)
    addi a3, a3, 8
    addi a2, a2, -1
7:  addi s2, s2, 1
    li   t1, NITER
    blt  s2, t1, 2b
.endm


    .globl _vtest_body
_vtest_body:                     /* the PRIMARY is the READER: it publishes */
    mv   s10, ra
    li   s3, XADDR
    li   t0, NITER
    sw   t0, R_NITER(s11)
    li   s4, LOGBASE              /* the log cursor... */
    add  s4, s4, s11
    li   s5, LOGMAX               /* ...and how much room is left */
    li   s6, 1                    /* the pass number */
    li   a3, SMPBASE              /* the raw-sample cursor... */
    add  a3, a3, s11
    li   a2, SMPMAX               /* ...and its remaining room */

    /* WAIT FOR THE WRITER TO BE RUNNING.  Without this the reader finishes
       all NITER iterations before the AP has even left the prologue, reads
       X = Y = 0 every time, and reports a witness of ZERO -- which looks
       exactly like a machine that never reorders.  Measured: 0 out of 20480
       until this handshake existed. */
4:  lw   t0, READY1(s11)
    beqz t0, 4b

    RLOOP 0
    sw   s7, R_P1WIT(s11)
    sw   s8, R_P1BAD(s11)
    lw   t0, 0(s3)
    sw   t0, 28(s11)              /* DIAG: X as pass 1 ended */
    lw   t0, YOFFR(s3)
    sw   t0, 32(s11)              /* DIAG: Y as pass 1 ended */
    li   t0, 1
    sw   t0, STOP1(s11)           /* release the writer's first loop */

    /* WAIT FOR THE WRITER TO REACH ITS FENCED LOOP.  Without this the
       control pass would spend its first iterations racing against the
       UNFENCED writer that has not noticed STOP1 yet -- which is exactly
       the configuration the control is supposed to exclude. */
3:  lw   t0, READY2(s11)
    beqz t0, 3b

    li   s6, 2
    RLOOP 1
    sw   s7, R_P2WIT(s11)
    sw   s8, R_P2BAD(s11)
    li   t0, LOGMAX
    sub  t0, t0, s5
    sw   t0, R_LOGN(s11)
    li   t0, 1
    sw   t0, STOP2(s11)

    li   t0, 1
    sw   t0, RES_STATUS(s11)
    mv   ra, s10
    ret

    .globl _vtest_body_ap
_vtest_body_ap:                  /* the AP is the WRITER */
    li   s3, XADDR
    li   t0, 1
    sw   t0, READY1(s11)
    WLOOP 0, STOP1
    li   t0, 1
    sw   t0, READY2(s11)          /* now in the fenced loop */
    WLOOP 1, STOP2
    ret
