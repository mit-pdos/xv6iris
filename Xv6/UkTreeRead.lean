/-
**THE TREE'S open COROLLARY, its pure tie** (Rocq `UkTreeRead.v`, 631 lines,
pinned `1900b8a43`).

CONE TRIM (union_cone.md, 1/13 reached; re-walked on the pinned globs): the
union reaches ONLY `tree_open_fd_tie` -- the pure fact that, at the slot the
open call wrote, the two spellings of the new row (the ledger's allocation and
the kernel's receipt `open_fd_rcpt`) agree, so the handle the caller keeps is
at the pinned node.  Not ported, as unreached: `tree_open_bundle_abs`,
`tree_open_recv_file`, `tree_open_fam`, `tree_open_sup`,
`wp_uk_ecall_open_own`, `tree_read_recv`, `tree_read_piece`,
`read_arms_tree_learn`, `wp_uk_tree_read_learns` (and the section notations
`a0_idx`…`a2_idx`).

## Deviations from Rocq

1. Rocq's `l` (an unused ledger argument) is dropped; `i : Z` is `Nat`
   (`FdType.inode`'s field); `mword_of_int (Z.of_nat fd)` is
   `BitVec.ofNat 64 fd` (SysOpenDefs deviation 5); `<[fd := x]> sts` is
   `sts.set fd x`.
-/
import Xv6.UConsOpen

namespace Xv6

open Iris

/-- **Rocq `tree_open_fd_tie`**: at the slot the call wrote, the ledger's
row and the receipt's row agree. -/
theorem treeOpen_fd_tie (sts fdv' : List FdState) (rv : BitVec 64) (rb wb : Bool) (i : Nat) (γo : GName)
    (omo : OffMode) (fd : Nat) (rd wr : Bool) (ty : FdType)
    (hlen : sts.length = NOFILE) (hrv : rv = BitVec.ofNat 64 fd) (hlt : fd < NOFILE)
    (hfdv : fdv' = sts.set fd (.open rd wr ty)) (hr : openFdRcpt rb wb (.inode i γo omo) sts rv fdv') :
    FdState.open rd wr ty = .open rb wb (.inode i γo omo) := by
  obtain ⟨fd0, hr0, hcl0, hfdv0⟩ := hr
  have hlt0 : fd0 < NOFILE := by
    rw [← hlen]
    rcases Nat.lt_or_ge fd0 sts.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hcl0; cases hcl0
  have hfd : fd = fd0 := initCons_moiNat_inj fd fd0 hlt hlt0 (hrv.symm.trans hr0)
  subst hfd
  have hfdlt : fd < sts.length := by rw [hlen]; exact hlt
  have hins := congrArg (fun l : List FdState => l[fd]?) (hfdv.symm.trans hfdv0)
  simp only [List.getElem?_set_self hfdlt, Option.some.injEq] at hins
  exact hins

end Xv6
