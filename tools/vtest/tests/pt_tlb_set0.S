/* pt_tlb_set0 -- pt_tlb's SET-0 middle observation, and it is expected to
 * disagree.
 *
 * This test exists to be RED.  It is the same program as pt_tlb, built from
 * the same source with -DPT_TLB_SET0, and the only difference is that it
 * also publishes +24: the load of VA 0x40000300 after the PTE rewrite and
 * before the sfence.vma.
 *
 * BOTH MACHINES ANSWER 0x11223344 THERE -- they kept the stale translation
 * -- and the model answers 0x99887766, because it re-walked.  Neither is
 * wrong: the architecture permits an implementation to keep the old entry
 * until an sfence.vma and equally permits it to have dropped the entry for
 * any reason.  But the model cannot be made to agree, and the reason is
 * structural rather than incidental: its TLB is 64 entries and DIRECT-
 * MAPPED, `tlb_hash` is the low 6 bits of the VPN, and VA 0x40000300 lands
 * in set 0 -- the same set as every instruction fetch in the image
 * (VPN 0x80000) and every result-region store (VPN 0x80100).  The entry is
 * evicted by the next instruction the program executes, so the model can
 * NEVER show it stale.
 *
 * That is why pt_tlb uses two addresses.  VA 0x40007300 is in set 7, which
 * nothing else here touches, and at +32 the model and both machines agree
 * on 0x11223344: the stale entry WAS used.  So the stale-translation
 * question does get asked and answered -- it is asked at set 7, and pt_tlb
 * proves it on both platforms.
 *
 * A proof of this run is not expected.  What would be news is the model
 * answering 0x11223344 at +24, which would mean its TLB had stopped being
 * direct-mapped.
 */
/* vtest: repeat=20 */
#define PT_TLB_SET0 1
#include "pt_tlb.S"
