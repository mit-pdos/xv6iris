/* core_regs_hpm_live -- the two HPM counters the U74 ACTUALLY IMPLEMENTS,
 * and it is expected to disagree on the board.
 *
 * The same program as core_regs_hpm, built from the same source with
 * -DCORE_REGS_HPM_LIVE, and the only difference is that it also publishes
 * the four words that read counters 3 and 4:
 *
 *     +8    mhpmcounter3 (0xB03)     +16   mhpmcounter4 (0xB04)
 *     +136  hpmcounter3  (0xC03)     +144  hpmcounter4  (0xC04)
 *
 * QEMU's default rv64 CPU implements no programmable HPM counter -- it
 * answers 0 for all sixteen of 0xB03..0xB12 -- and so does the model, so on
 * QEMU this test is the same comparison as core_regs_hpm and passes.
 *
 * THE VISIONFIVE 2 IMPLEMENTS TWO, and they are counting.  Measured, one
 * boot: mhpmcounter3 = 0x64_8490_0744 and mhpmcounter4 = 0x19_0201_0210,
 * with the unprivileged aliases hpmcounter3/4 reading the same registers;
 * counters 5..18 read 0 there as everywhere, and all sixteen mhpmevent
 * selectors agree.  So the divergence is exactly two registers wide and it
 * is not a model bug: a free-running counter cannot agree between two
 * machines that execute a different number of cycles, and the model has no
 * counter to run.
 *
 * A proof of the board run is not expected, and one of the QEMU run says
 * only that QEMU has no HPM counters either.  What would be news is the
 * BOARD reading 0 here, which would mean the two counters had been gated
 * off between the firmware and the payload.
 */
/* vtest: repeat=1 */
#define CORE_REGS_HPM_LIVE 1
#include "core_regs_hpm.S"
