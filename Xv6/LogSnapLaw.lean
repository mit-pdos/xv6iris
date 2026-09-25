/-
**THE FILE SYSTEM'S LAW, AS THE WAL PARKS IT** -- a port of Rocq
`LogSnapLaw.v` (`/shared/xv6rocq/iris/LogSnapLaw.v`).  Crash batch C-1, agent
CG.

The commit RECONSTRUCTS the file-system predicate at the one moment the era's
invariants are all clean, and the WAL stays file-system-agnostic: what it holds
(in `log_ctx`, batch C-2b) is a PERSISTENT law that, given the byte authority
at the logged view and "no transaction is open", yields the next durable EPOCH
paired with the guest (`durPair`, `Xv6/FsDurSnap.lean`) and hands both
authorities back.  It moves NO durable resource: the epoch is ALLOCATED.

ARITY-FREE (`snapLaw`), as `Xv6/SbPark.lean`'s park is: the mask it runs in and
the guest are closed over, with the one fact a holder needs about the mask --
that it misses the byte view's own `fsbN`, so a committer holding `fsbN` open
can still run it (`snapLaw_run`) -- and, beside the law, THE CRASH SEAM AT THE
SAME GUEST, so the committer reads seam and epoch off ONE handle and hands both
to `fsCommitL_seqPermit` (`Xv6/FsCrashCommit.lean`) at one `G`.

The premises are the rows of the byte view's body (`Xv6/FsBytesInv.lean`),
NOT the collection's `col_auth` (Rocq's reason: this file sits below the log
invariant, which sits below the inode region and the collection).

## DEVIATIONS from Rocq

1. Rocq's `dom C = fs_home_set cov logstart` is
   `∀ b, (∃ bs, get? C b = some bs) ↔ fsHome cov logstart b` (the
   `fsRecovery_dom` spelling; the port has no `dom` on `ExtTreeMap`).
2. Rocq's `ghost_map_auth (ln_tx γ) 1 ∅` is `logTxAuth γ ∅`.

## NOT PORTED (D36): none.
-/
import Xv6.FsBytesInv
import Xv6.FsCrashSeam

namespace Xv6

open Iris Iris.BI Iris.ProofMode Std MachCSL

set_option linter.unusedSectionVars false

/-! ## The law -/

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachFixedGS hlc GF] [Xv6G GF] [FsBytesG GF]
  [MonoListG GF BlockMap] [FsLinkG GF] [FsTopG GF]

/-- THE CONCLUSION, AS ONE NAME: the next epoch at the map the commit jumps to,
with the guest (Rocq `snap_law_out`). -/
def snapLawOut (G : GName → IProp GF) (C : BlockMap) (home : List Nat) : IProp GF :=
  durPair G (fsRestrict (dvOfD C) home)

/-- THE LAW, at a NAMED mask and a NAMED guest (Rocq `snap_law_at`). -/
def snapLawAt (γ : LogNames) (γfs : FsNames) (cov : ExtTreeSet Nat compare) (logstart : Nat)
    (N : CoPset) (G : GName → IProp GF) : IProp GF :=
  iprop(□ (∀ (E : CoPset) (Lb : RegMapF (BitVec 8)) (C : BlockMap),
    ⌜N ⊆ E⌝ -∗
    ⌜∀ b, (∃ bs, PartialMap.get? C b = some bs) ↔ fsHome cov logstart b⌝ -∗
    ⌜∀ b bs, PartialMap.get? C b = some bs → bs.length = BSIZE⌝ -∗
    ⌜bytesTie Lb C⌝ -∗
    ⌜bytesDom Lb (fsHomeList cov logstart)⌝ -∗
    (γfs.bytes ↪●MAP Lb) -∗ logTxAuth γ ∅ ={E}=∗
      snapLawOut (hlc := hlc) G C (fsHomeList cov logstart) ∗ (γfs.bytes ↪●MAP Lb) ∗
      logTxAuth γ ∅))

/-- ...and the arity-free form the log carries: mask and guest closed over,
the seam at the same guest beside it (Rocq `snap_law`). -/
def snapLaw (γ : LogNames) (γfs : FsNames) (cov : ExtTreeSet Nat compare) (logstart : Nat) :
    IProp GF :=
  iprop(∃ (N : CoPset) (G : GName → IProp GF),
    ⌜(↑fsbN : CoPset) ## N⌝ ∗ fsCrashSeamAt (hlc := hlc) G cov logstart ∗
    snapLawAt (hlc := hlc) γ γfs cov logstart N G)

instance snapLawAt_persistent (γ : LogNames) (γfs : FsNames) (cov : ExtTreeSet Nat compare)
    (logstart : Nat) (N : CoPset) (G : GName → IProp GF) :
    Persistent (snapLawAt (hlc := hlc) γ γfs cov logstart N G) := by
  unfold snapLawAt; infer_instance

instance snapLaw_persistent (γ : LogNames) (γfs : FsNames) (cov : ExtTreeSet Nat compare)
    (logstart : Nat) : Persistent (snapLaw (hlc := hlc) (GF := GF) γ γfs cov logstart) := by
  unfold snapLaw; infer_instance

/-- Rocq `snap_law_intro`. -/
theorem snapLaw_intro (γ : LogNames) (γfs : FsNames) (cov : ExtTreeSet Nat compare)
    (logstart : Nat) (N : CoPset) (G : GName → IProp GF) (hdj : (↑fsbN : CoPset) ## N) :
    fsCrashSeamAt (hlc := hlc) G cov logstart ⊢
      snapLawAt (hlc := hlc) γ γfs cov logstart N G -∗ snapLaw (hlc := hlc) γ γfs cov logstart := by
  iintro #Hseam #H
  unfold snapLaw
  iexists N, G
  isplitr
  · ipureintro; exact hdj
  isplitr
  · iexact Hseam
  · iexact H

/-- THE READING A COMMITTER TAKES, at `⊤ ∖ ↑fsbN` (Rocq `snap_law_run`): the
epoch and the seam at the law's own guest, both authorities back. -/
theorem snapLaw_run (γ : LogNames) (γfs : FsNames) (cov : ExtTreeSet Nat compare)
    (logstart : Nat) (Lb : RegMapF (BitVec 8)) (C : BlockMap)
    (hdom : ∀ b, (∃ bs, PartialMap.get? C b = some bs) ↔ fsHome cov logstart b)
    (hlens : ∀ b bs, PartialMap.get? C b = some bs → bs.length = BSIZE)
    (htie : bytesTie Lb C) (hdm : bytesDom Lb (fsHomeList cov logstart)) :
    snapLaw (hlc := hlc) (GF := GF) γ γfs cov logstart ⊢
      (γfs.bytes ↪●MAP Lb) -∗ logTxAuth γ ∅ ={⊤ \ ↑fsbN}=∗
        (∃ G : GName → IProp GF, fsCrashSeamAt (hlc := hlc) G cov logstart ∗
          snapLawOut (hlc := hlc) G C (fsHomeList cov logstart)) ∗
        (γfs.bytes ↪●MAP Lb) ∗ logTxAuth γ ∅ := by
  iintro #Hlaw Hb Ht
  unfold snapLaw
  icases Hlaw with ⟨%N, %G, %hdj, #Hseam, #Hbody⟩
  have hsub : N ⊆ ⊤ \ (↑fsbN : CoPset) := by
    intro p hp
    rw [CoPset.in_diff]
    exact ⟨CoPset.subseteq_top p hp, fun hc => hdj p ⟨hc, hp⟩⟩
  unfold snapLawAt
  imod Hbody $$ %(⊤ \ ↑fsbN) %Lb %C %hsub %hdom %hlens %htie %hdm Hb Ht with ⟨Hout, Hb, Ht⟩
  imodintro
  iframe Hb Ht
  iexists G
  iframe Hout
  iexact Hseam

end

end Xv6
