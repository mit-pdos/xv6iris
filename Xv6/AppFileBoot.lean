/-
**THE FILE CLAIM AT BOOT: /init'S RESOURCE AND THE ERA-0 CLAIM** -- §6a
and §7 of Rocq `AppFile.v` (`/shared/xv6rocq/iris/AppFile.v`, pinned
1900b8a43, l.1250-1353), the reached part.

* `fileBoot` (Rocq `file_boot`): WHAT /init IS HANDED AT THE ERA MINT --
  echo's (the console key or flag) and THE DEED, both halves the process
  chain owns, at the clone's content, beside the typed witness of that
  content (under ONE later), or the taint;
* `fileInit` (Rocq `file_init`): at the map a boot founds its file system
  at, when the disk is mkfs's image, echo's era-0 claim with NO FILE of the
  class present (law L4) and the deed at the empty map;
* `fileInit_img` (Rocq `file_init_img`): ...at the theorem's own literal
  shape (`AppLaws.xv6AppAdequacy`'s `Happ_init`).

## DEVIATIONS from Rocq

1. Stated at Lean's era-0 vocabulary (`dk : Nat → BitVec 8`, `D :
   BlockMap`, `cov : ExtTreeSet Nat compare`), as `AppEcho.echoInit`.
2. Scope: `file_xfer_boot` is unreached and not ported.
3. `escRecs_nil` (the empty ledger's invariant; Rocq `rewrite /esc_recs //`)
   is a one-line helper.
-/
import Xv6.AppFileSteps
import Xv6.FileNamePins
import Xv6.FsDurImg

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL

set_option linter.unusedSectionVars false

section AppFileBoot
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [DiskG GF]
  [EchoOutG GF] [FileAppG GF]

/-- WHAT /init IS HANDED AT THE ERA MINT (Rocq `file_boot`). -/
def fileBoot (c : FileFixed) (k : Nat) (r : FileAppNames) : IProp GF :=
  iprop(echoBoot (GF := GF) c.1 k r.fnCons
    ∗ ∃ s : Dst, fown r s ∗ ▷ (fTyped c s ∨ fileTaint (hlc := hlc) c))

/-- The empty ledger is all spent. -/
theorem escRecs_nil : ⊢@{IProp GF} escRecs (hlc := hlc) ([] : List EscRec) := by
  unfold escRecs
  exact BigSepL.bigSepL_nil_intro

/-- THE ERA-0 CLAIM (Rocq `file_init`). -/
theorem fileInit (c : FileFixed) (dk : Nat → BitVec 8) (D : BlockMap) (S : FsStateRec)
    (hdk : fsBlocks dk = fsimgP)
    (hrec : fsRecovery (fsBlocks dk) D fsimgCov fsimgSb.sbLogstart) (hS : snapOk S D) :
    ⊢@{IProp GF} |==> ∃ r : FileAppNames, filePred (hlc := hlc) c r (absView S.fssInodes) := by
  imod (echoInit (hlc := hlc) (GF := GF) c.1 dk D S hdk hrec hS) with ⟨%rc, He⟩
  imod (fnamesAlloc (GF := GF) rc ∅) with ⟨%r, %hrc, Hd1, -, Ht1, -, Ha1⟩
  imodintro
  iexists r
  subst hrc
  iapply filePred_join c r _ $$ He
  iright
  isplitr
  · ipureintro; exact fileFsEra0 dk D S hdk hrec hS
  unfold fState
  ileft
  isplitl [Ha1]
  · unfold fEscWrap
    iexists []
    iframe Ha1
    iapply escRecs_nil
  unfold fCore
  ileft
  iexists ∅
  iframe Hd1 Ht1
  isplitr
  · iapply fTyped_empty
  ipureintro
  apply fOk_empty
  intro N hN
  exact era0RecoveryClassAbsent txtName dk D S N txtLaws hdk hrec hS hN

/-- ...at the theorem's own literal shape (Rocq `file_init_img`). -/
theorem fileInit_img (c : FileFixed) (dk : Nat → BitVec 8) (ndisk : Nat) (sb : FsSb)
    (nib : Nat) (cov : Std.ExtTreeSet Nat compare)
    (himg : fsBootImageWf dk ndisk sb nib cov) (hdk : fsBlocks dk = fsimgP)
    (hsb : sb = fsimgSb) (hcov : cov = fsimgCov) :
    ⊢@{IProp GF} |==> ∃ r : FileAppNames,
      filePred (hlc := hlc) c r (absView (imgState (fsBlocks dk) sb nib).fssInodes) := by
  subst hsb hcov
  have hS := imgSnapOk dk ndisk fsimgSb nib fsimgCov himg
  rw [hdk] at hS ⊢
  exact fileInit c dk era0D _ hdk (era0Recovery dk hdk) hS

end AppFileBoot

end Xv6
