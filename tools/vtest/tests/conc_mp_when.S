/* conc_mp_when -- conc_mp's TIMING-DEPENDENT fields, and they are expected
 * to disagree.
 *
 * This test exists to be RED.  It is the same program as conc_mp, built
 * from the same source with -DCONC_MP_WHEN, and the only difference is that
 * it also publishes the four counters and the sample array that say WHEN
 * the reader happened to sample the writer:
 *
 *   +12   pass 1 WITNESS   -- iterations where r1 != r2
 *   +20   pass 2 WITNESS   (fenced)
 *   +28   X as pass 1 ended  } the writer's sequence number when the
 *   +32   Y as pass 1 ended  } reader's pass finished
 *   +0x300 + 8*k  SAMPLE k: the raw r1 and r2 of the first 32 iterations
 *
 * None of those is a property of the machine's memory model; every one of
 * them is a property of how the two harts happened to interleave.  Measured:
 * QEMU's eight captured observations of conc_mp differ in exactly one word
 * (+20) and the board's two differ in five more plus the whole sample array.
 * Published in conc_mp itself they made the case unprovable -- eight
 * observations the model would need eight interleavings to reproduce, none
 * of which says anything about reordering.
 *
 * WHY IT IS STILL WORTH RUNNING.  conc_mp's FORBIDDEN counts are the
 * finding, and a null FORBIDDEN count means little without the witness count
 * beside it: zero reorderings out of zero opportunities is not evidence.
 * The witness count is the number of genuine opportunities the run gave the
 * machine, and the sample log is how far apart the two words were in flight.
 * Both are read from this capture, by a human, and neither is something the
 * model can be asked to agree with.
 *
 * A proof of this run is not expected.  What would be news is conc_mp's
 * FORBIDDEN count moving off zero -- and that is conc_mp's business, not
 * this test's.
 */
/* vtest: smp=2 repeat=20 budget=6000 */
#define CONC_MP_WHEN 1
#include "conc_mp.S"
