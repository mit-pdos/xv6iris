/* core_regs_pmp_fw -- the PMP entries THE BOARD'S FIRMWARE PROGRAMS, and it
 * is expected to disagree there.
 *
 * The same program as core_regs_pmp, built from the same source with
 * -DCORE_REGS_PMP_FW, and the only difference is that it also publishes
 * pmpcfg0 (+8) and pmpaddr0..7 (+24 .. +80).
 *
 * QEMU is started with no firmware, so its whole PMP file is zero at entry
 * and this test is the same comparison as core_regs_pmp: it passes, and
 * what it says is that the model's reset agrees with a machine that has
 * nothing to reset from.
 *
 * ON THE VISIONFIVE 2 OPENSBI HAS ALREADY RUN.  Measured, one boot:
 * pmpcfg0 = 0x0F -- entry 0 is TOR with R, W and X -- and pmpaddr0..7 hold
 * the bounds it programmed; pmpcfg2 and pmpaddr8..15 are still zero, which
 * is why they stay in core_regs_pmp.  The model reads the whole file as 0.
 *
 * NEITHER IS WRONG, and core_regs_pmp's header says why in as many words:
 * the spec's own [reset_pmp] establishes these values over ARBITRARY
 * garbage, and ArchReset.v's board list does not make pmpcfg a board
 * obligation.  The model's reset is simply more specific than the machine
 * a payload actually lands on.  A proof of the board run is not expected;
 * what would be news is the board reading 0, which would mean it had been
 * entered without firmware.
 */
/* vtest: repeat=1 */
#define CORE_REGS_PMP_FW 1
#include "core_regs_pmp.S"
