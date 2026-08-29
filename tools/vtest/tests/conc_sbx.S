/* conc_sbx -- STORE BUFFERING, made sensitive.  The high-yield sibling of
 * conc_sb.
 *
 * !! THIS TEST IS NOT YET VALIDATED, AND ITS NULL RESULT MEANS NOTHING. !!
 *
 * A litmus test is only worth its null when there is a machine that DOES
 * produce the outcome and the test finds it there.  For store buffering
 * that machine is QEMU: its x86 host is TSO, and conc_sb measures (0,0) on
 * it in about 4.6% of runs.  conc_sbx, run on the same QEMU, finds ZERO in
 * 3.84 MILLION races with 40593 of them aligned.  So the test cannot see
 * the thing it is looking for, and the board reporting zero (15.36 million
 * races, 22900 aligned) says nothing about the board.
 *
 * What it DOES now do, which the first three versions did not, is overlap
 * the two harts at all -- see A RANDOM PHASE PER ROUND below.  What is
 * missing is whichever part of conc_sb's structure makes the outcome
 * reachable: conc_sb warms both harts through the whole hot path before
 * racing and tunes a per-hart delay, and neither is reproduced here.  The
 * likely culprit is the sweep itself: (1,1) is the alignment where both
 * STORES land before both loads, and (0,0) needs the opposite clustering --
 * both LOADS issuing before either store is visible -- so a high (1,1)
 * count is evidence of overlap but not of the RIGHT overlap.
 *
 * DO NOT QUOTE A NUMBER FROM THIS TEST until it reproduces (0,0) on QEMU.
 *
 * conc_sb races ONCE per run: two harts, two rounds, one chance to hit the
 * outcome.  On QEMU that is enough, because QEMU inherits its x86 host's TSO
 * and produces (0,0) in a few percent of runs.  On the board it found
 * nothing in 16 runs -- which is 16 chances, and says almost nothing.
 *
 * THE OUTCOME.  Each hart stores 1 to its OWN word and then loads the
 * OTHER's:
 *
 *     hart P:  X = 1 ; a = Y            hart Q:  Y = 1 ; b = X
 *
 *     (a,b) = (0,0)   -- neither saw the other's store
 *
 * Under SEQUENTIAL CONSISTENCY that is impossible: whichever store is second
 * in the total order, the load that follows it must see the first.  Under
 * TSO it is allowed, and it is the ONLY thing TSO relaxes -- a store sitting
 * in a store buffer while a later load to a different address completes.
 * So this is the test that asks whether the board is as weak as TSO at all,
 * where conc_mp asks whether it is weaker.
 *
 * WHY THIS ONE SHOULD WORK WHERE conc_mp DID NOT.  conc_mp needs the writer
 * to have TWO stores outstanding so they can complete out of order, and the
 * measured lockstep -- both harts touching both lines every iteration --
 * serialises the writer's stores through the coherence protocol, so it never
 * has two in flight.  Store buffering needs no such thing: ONE buffered
 * store per hart is enough, and the contention actually HELPS.  Each hart's
 * store is to a line the other hart is simultaneously loading, so it must
 * wait for ownership -- which is exactly the condition that leaves it
 * sitting in the store buffer while the following load proceeds.
 *
 * HOW IT GETS THE YIELD.  NSLOT independent slot pairs swept ROUNDS times,
 * so one run is NSLOT * ROUNDS races instead of one.  There is no
 * per-iteration barrier -- that would impose the very ordering under test --
 * and no communication during the race: each hart writes what it OBSERVED
 * into its own private array, and the primary counts the pairs afterwards,
 * once the exit barrier says both sweeps are done.  The counts ACCUMULATE
 * across rounds, so a single (0,0) anywhere in the run is visible.
 *
 * The two sweeps are the same eight instructions so the harts stay in phase
 * and slot i is genuinely contended for most i; the four-way tally below is
 * what says whether that worked.  (1,1) -- both saw the other's store --
 * is the sign of real overlap, and a run that is all (0,1) or all (1,0) is
 * one where the harts simply took turns.
 *
 * X[] and Y[] ARE 4 KB APART and each slot is its own 64-byte line, so
 * neither false sharing nor a next-line prefetcher can couple them.  The
 * observation arrays are in the RESULT region, in separate lines per hart,
 * so recording an observation does not itself create sharing.
 *
 * RESULT layout (mirrored in vtest-rocq/ConcSbx.v):
 *   +8    NSLOT * ROUNDS, the races per run
 *   +12   count of (a,b) = (0,0)   <-- THE TSO-ONLY OUTCOME, sticky
 *   +16   count of (1,1)           both saw: real overlap
 *   +20   count of (0,1)
 *   +24   count of (1,0)
 *   +0x400 + 4*i   A[i], hart P's observation of Y[i]  (scratch)
 *   +0x600 + 4*i   B[i], hart Q's observation of X[i]  (scratch)
 *   +0x100  the entry gate's counter,  +0x140 the exit gate's
 */
/* vtest: smp=2 repeat=1 */
    .option norvc
#include "abi.h"

/* NSLOT * 64 bytes for X and the same for Y is exactly the declared 8 KB
   DMA region, so 64 slots is the most this ABI allows. */
#define NSLOT     64
/* RUN FOR ABOUT A SECOND, and that is the point rather than an accident.
   A round is ~50 us -- every slot access is a coherence miss, not a cache
   hit, so it is hundreds of cycles rather than one -- which makes 20000
   rounds about a second and 1.28 MILLION races.  Any rendezvous releases the two harts a coherence round
   apart -- several slots of an eight-instruction sweep -- and measured that
   skew was totally systematic: with per-hart flags the outcome was (0,1) on
   8185 of 8192 races and with a shared-counter gate it was (1,0) on 8192 of
   8192, i.e. one hart finished its whole sweep before the other began, both
   times.  Fighting that with a barrier does not work, and staggering the
   phase by hand only samples the offsets one thinks to try.  Running for a
   second lets the two harts drift through every relative phase on their own,
   many times over, and makes the startup skew negligible against the run. */
#define ROUNDS    20000
#define XBASE     DMA_BASE               /* X[i] at XBASE + 64*i          */
#define YBASE     (DMA_BASE + 0x1000)    /* Y[i], 4 KB away               */
#define AOFF      0x400                  /* hart P's observations         */
#define BOFF      0x600                  /* hart Q's, a different line    */

#define R_TOTAL   8
#define R_00      12
#define R_11      16
#define R_01      20
#define R_10      24

#define GATE_IN   0x100           /* the entry gate's shared counter */
#define GATE_OUT  0x140           /* the exit gate's, a separate line */

/* A SHARED-COUNTER GATE, and the shape matters more than it looks.
 *
 * The obvious rendezvous -- each hart writes its own flag and spins on the
 * other's -- RELEASES THE TWO HARTS AT DIFFERENT TIMES.  Whoever arrives
 * last sees the other's flag already set and proceeds immediately; whoever
 * arrived first must still observe the late writer's store, which costs a
 * coherence round.  So the last arriver starts EARLIER, systematically.
 *
 * That is not a theoretical worry: hart P does the counting pass at the end
 * of each round, so it always arrived last, so it always started first --
 * and the measured result was (0,1) on 8185 of 8192 races, i.e. P had
 * finished its store and load before Q stored at all.  The harts never
 * overlapped, and a run with no overlap cannot exhibit store buffering
 * however many races it contains.
 *
 * Both harts now increment ONE counter and spin on THAT word, so they are
 * released by the same coherence event rather than by two different ones.
 * amoadd.w is used for the increment because two plain read-modify-writes
 * would lose one. */
.macro GATE off
    li   t1, \off
    add  t1, s11, t1
    li   t0, 1
    amoadd.w zero, t0, (t1)
    addi t2, s9, 1
    slli t2, t2, 1                /* both harts have arrived: 2*(round+1) */
9:  lw   t0, 0(t1)
    blt  t0, t2, 9b
.endm

/* A RANDOM PHASE PER ROUND, and it is what a long run alone does not give.
 *
 * Any rendezvous releases the two harts a coherence round apart -- several
 * slots of an eight-instruction sweep -- and the difference is SYSTEMATIC,
 * because one hart always has more work than the other between rounds.
 * Measured three ways, all uniform: per-hart flags gave (0,1) on 8185 of
 * 8192; a shared-counter gate gave (1,0) on 8192 of 8192; and running for a
 * second gave (0,1) on 1280000 of 1280000.  THE LAST ONE IS THE INSTRUCTIVE
 * ONE -- a long run does not help by itself, because the barrier re-imposes
 * the same skew every round and drift never accumulates.  One hart finishes
 * its whole sweep before the other starts, a million times in a row.
 *
 * So each hart delays a PSEUDO-RANDOM number of iterations after the gate,
 * from its own LCG with its own seed.  The relative offset is then a random
 * variable of a few hundred instructions in either direction, resampled
 * every round, so over 20000 rounds every offset -- including zero -- is
 * visited many times.  The (1,1) tally reports whether it worked: that is
 * the count of races where each hart really did see the other's store, and
 * it is the sensitivity witness for this test the way `witness` is for
 * conc_mp. */
.macro LCG reg
    li   t1, 1103515245
    mul  \reg, \reg, t1
    li   t1, 12345
    add  \reg, \reg, t1
    srli t2, \reg, 16
    andi t2, t2, 0xff             /* 0..255 iterations */
    beqz t2, 8f
7:  addi t2, t2, -1
    bnez t2, 7b
8:
.endm

/* THE RACE, eight instructions, identical on both harts up to which word is
   stored and which is loaded.  Nothing in here communicates: the observation
   goes to a private array and is compared afterwards. */
.macro SWEEP store_base, load_base, obs_off
    li   s2, \store_base
    li   s3, \load_base
    li   s4, \obs_off
    add  s4, s4, s11
    li   s6, 0
    li   s5, 1
1:  sw   s5, 0(s2)                /* MY word = 1        */
    lw   t1, 0(s3)                /* ...then THEIR word */
    sw   t1, 0(s4)                /* what I observed    */
    addi s2, s2, 64
    addi s3, s3, 64
    addi s4, s4, 4
    addi s6, s6, 1
    li   t2, NSLOT
    blt  s6, t2, 1b
.endm

.macro ZEROHALF base
    li   t2, 0
    li   t0, \base
2:  sw   zero, 0(t0)
    addi t0, t0, 64
    addi t2, t2, 1
    li   a1, NSLOT
    blt  t2, a1, 2b
.endm

    .globl _vtest_body
_vtest_body:                      /* hart P: stores X, loads Y */
    mv   s10, ra
    li   t0, NSLOT * ROUNDS
    sw   t0, R_TOTAL(s11)

    li   s8, 22222                /* this hart's LCG seed */
    li   a4, 0                    /* (0,0) -- the one that matters */
    li   a5, 0                    /* (1,1) */
    li   a6, 0                    /* (0,1) */
    li   a7, 0                    /* (1,0) */
    li   s9, 0
10: ZEROHALF XBASE
    GATE GATE_IN
    LCG  s8
    SWEEP XBASE, YBASE, AOFF
    GATE GATE_OUT                 /* both sweeps are over before counting */

    /* count this round's pairs.  Outside the race entirely. */
    li   s2, AOFF
    add  s2, s2, s11
    li   s3, BOFF
    add  s3, s3, s11
    li   s6, 0
3:  lw   t0, 0(s2)                /* a: what P saw of Y */
    lw   t1, 0(s3)                /* b: what Q saw of X */
    bnez t0, 4f
    bnez t1, 5f
    addi a4, a4, 1                /* (0,0)  <-- TSO-ONLY */
    j    6f
5:  addi a6, a6, 1                /* (0,1) */
    j    6f
4:  bnez t1, 7f
    addi a7, a7, 1                /* (1,0) */
    j    6f
7:  addi a5, a5, 1                /* (1,1) */
6:  addi s2, s2, 4
    addi s3, s3, 4
    addi s6, s6, 1
    li   t2, NSLOT
    blt  s6, t2, 3b

    addi s9, s9, 1
    li   t1, ROUNDS
    blt  s9, t1, 10b

    sw   a4, R_00(s11)
    sw   a5, R_11(s11)
    sw   a6, R_01(s11)
    sw   a7, R_10(s11)
    li   t0, 1
    sw   t0, RES_STATUS(s11)
    mv   ra, s10
    ret

    .globl _vtest_body_ap
_vtest_body_ap:                   /* hart Q: stores Y, loads X */
    li   s8, 98765                /* a DIFFERENT seed, so the two delays are
                                     independent and the relative offset
                                     takes both signs */
    li   s9, 0
11: ZEROHALF YBASE
    GATE GATE_IN
    LCG  s8
    SWEEP YBASE, XBASE, BOFF
    GATE GATE_OUT
    addi s9, s9, 1
    li   t1, ROUNDS
    blt  s9, t1, 11b
    ret
