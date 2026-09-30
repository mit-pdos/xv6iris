/* disk_ident_segmax -- the one config-space field that still diverges, and
 * it is expected to.
 *
 * This test exists to be RED.  It is the same program as disk_ident_cap,
 * built from the same source with -DDISK_IDENT_SEGMAX, and the only
 * difference is that it also publishes +20: seg_max, at config+12.
 *
 * QEMU reports 254 -- the largest number of descriptors it will accept in
 * one chain, one less than the 255 its queue can hold -- and the model
 * reports 0.  A driver that believed 0 would conclude it may not submit a
 * chain at all, so this is an incompleteness in the same family as finding
 * 17 (the model serves only a three-descriptor chain): the model has no
 * notion of a segment limit, and reports the absence as a limit of zero.
 *
 * The rest of the config space AGREES.  The capacity -- both halves -- and
 * size_max match, which is what disk_ident_cap proves; that was not true
 * when this file's sibling was written, because the model had no case for
 * offset 0x100 at all.
 *
 * A proof of this run is not expected.  What would be news is the model
 * reporting 254, or reporting a limit it then enforces.
 */
/* vtest: platforms=qemu */
#define DISK_IDENT_SEGMAX 1
#include "disk_ident_cap.S"
