/-
The O_CREATE arm's ARM BUILDERS: the SHIM that lets the plain blocks below
the join (`sysOpenJoinBody` and everything it calls, all stated at
`openArmsPlain`) run UNDER the create arm, and the conversion of what they
deliver into `SpecSysOpen.openArmsCreate` (stage file of `ProofSysOpen`;
Rocq `ProofSysOpenCreArm.v`, 484 lines).

Rocq's header, kept (the reasons are the content):

> THE SHIM, AND WHY IT IS THE WHOLE DESIGN.  The blocks from the join down
> are stated at `open_arms_plain` -- but they are PARAMETRIC in the caller
> predicates `P`, `Pmiss`, `Phio`, and that is the seam.  The create arm
> runs them at SHIM predicates and converts the armed post afterwards:
> `socr_P R i0` is the create-side residue `R`, carried inert through the
> whole plain tail, TAGGED with the inum so the post's existential `i` is
> pinned back to the created (or found) node; `socr_Pm R` is the same
> without the tag; `socr_Phio_*` is the terminal observation in the arm's
> two flavours.
>
> AND THE FLAVOUR IS DECIDED BY create's OWN `made` BIT.  made = true
> (FRESH): the FRESH arms REFUND the terminal observation, so the real
> `Phio` is never fired: it rides inside `R` and the plain tail runs at the
> PURE `socr_Phio_pure` (a row equation, no resource); the pure receipt
> refutes the tail's DEVICE and DIRECTORY arms and identifies the tail's
> `bs0` with `[]`.  THE TRUNC COMMIT IS THE CALLER'S OWN AND FIRES (the tail
> runs at `Phit` itself).  made = false (EXISTS-OPENS): the tail runs at
> `socr_Phio_tag` -- the real `Phio` with the row equation stapled on --
> and the staple refutes the DIRECTORY arm.
>
> THE ONE FUPD.  `open_post_fail_plain`'s first two disjuncts are
> unreachable below the join, but all three have to be converted; the
> first two return the residue inside the walk one-shot / the death
> receipt, so recovering it costs one `={⊤}=>` -- paid under the loop
> (`sysOpenK_mono_fupd`).

## Deviations from Rocq

1. Names: `socr_P` / `socr_Pm` / `socr_Phio_pure` / `socr_Phio_tag` /
   `socr_fresh` / `socr_exists` are `sysOpenCrP` / `sysOpenCrPm` /
   `sysOpenCrFoPure` / `sysOpenCrFoTag` / `sysOpenCrFresh` /
   `sysOpenCrExists`; the lemmas `socr_*` are `sys_open_cr_*`.  Inums are
   `Nat` (FsAbsDefs deviation 1).
2. The two residues take the view names `Γ` as a parameter (Rocq fixes
   `fs_gamma_L fsc_fs`); every use is at `fsGammaL fscFs`.
3. ADDED (the Lean continuation is NAMED, `SysOpenParts.sysOpenK`):
   `sysOpenK_mono_fupd` (the fupd twin of `SysOpenParts.sysOpenK_mono`),
   the shimmed record `sysOpenCrA` (with `sysOpenCrA_static`, its static
   premises for the seal's join instance), and the two continuation shims
   `sys_open_cr_post_fresh` / `sys_open_cr_post_exists`, which are Rocq's
   two inline `iAssert (wp_next … so_cont_au …)` blocks of
   `ProofSysOpenEntryC.so_entry_c_au`, hoisted here so the entry stage
   only applies them.
4. `sys_open_cr_ite`: the `if omTrunc vom` receipt moved under its key
   (Rocq destructs the key in place).

Imports only `SysOpenParts` (and through it the definitional layer).
-/
import Xv6.SysOpenParts

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF]
  [BcacheG GF] [SleepLockG GF] [DiskG GF] [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF]
  [FsTopG GF] [FsLinkG GF] [IcboxG GF] [OffboxG GF] [OffboxBoxG GF] [IrefslotG GF] [CtokG GF] [WchG GF]
  [Appcfg GF] [FileG GF] [Fscfg] [Icfg] [CurCtx]

/-! ## 1.  THE SHIM PREDICATES -/

/-- The cursor slot, TAGGED (Rocq's `socr_P`). -/
def sysOpenCrP (R : IProp GF) (i0 : Nat) : Nat → Nat → IProp GF :=
  fun _ x => iprop(⌜x = i0⌝ ∗ R)

/-- ...and untagged, for the miss side (Rocq's `socr_Pm`). -/
def sysOpenCrPm (R : IProp GF) : Nat → Nat → IProp GF := fun _ _ => R

/-- The FRESH flavour: a PURE row receipt (Rocq's `socr_Phio_pure`). -/
def sysOpenCrFoPure (i0 : Nat) (a0 : Anode) : Pfam GF (Aview → Nat → Anode → IProp GF) :=
  pfamTriv (fun _ x a => iprop(⌜x = i0 ∧ a = a0⌝))

/-- The EXISTS flavour: the caller's own receipt with the row equation
stapled on, the refund the caller's own (Rocq's `socr_Phio_tag`). -/
def sysOpenCrFoTag (i0 : Nat) (a0 : Anode) (Fo : Pfam GF (Aview → Nat → Anode → IProp GF)) :
    Pfam GF (Aview → Nat → Anode → IProp GF) :=
  ⟨fun av x a => iprop(⌜x = i0 ∧ a = a0⌝ ∗ Fo.pfRecv av x a), Fo.pfRefund⟩

/-! ## 2.  THE TWO RESIDUES (create's payout, held for the tail) -/

/-- ARM C-OK's payout, plus the two commits the FRESH arms refund and the
inum bound they assert (Rocq's `socr_fresh`). -/
def sysOpenCrFresh (Γ : FsViewNames GF) (P : Nat → Nat → IProp GF)
    (Farm Fun : Pfam GF (Aview → Nat → IProp GF))
    (Fok Fex : Pfam GF (Aview → Nat → Fname → Nat → IProp GF))
    (Fo : Pfam GF (Aview → Nat → Anode → IProp GF)) (pl : List (BitVec 8)) (i0 : Nat) :
    IProp GF :=
  iprop(∃ (d : Nat) (nm : Fname) (av : Aview) (ents : Std.ExtTreeMap Fname Nat compare) (nl : Nat),
    ⌜(pathElems pl).getLast? = some nm⌝ ∗
    ⌜crePre av d nm ents nl i0 (.AFile [])⌝ ∗
    ⌜0 < i0 ∧ i0 < 16 * icfgNib⌝ ∗
    P (nparElems pl).length d ∗
    Fok.pfRecv av d nm i0 ∗
    pfAt (dlookupCommitAt (hlc := hlc) Γ appE) Fex ∗
    pfAt (aopenCommitAt (hlc := hlc) Γ appE) Fo ∗
    pfAt (aunarmOfArm (hlc := hlc) Γ appE Farm) Fun)

/-- ARM F-OK's payout: the exists observation fired, the create commit
refunded (Rocq's `socr_exists`). -/
def sysOpenCrExists (Γ : FsViewNames GF) (P : Nat → Nat → IProp GF)
    (Farm Fun : Pfam GF (Aview → Nat → IProp GF))
    (Fok Fex : Pfam GF (Aview → Nat → Fname → Nat → IProp GF))
    (pl : List (BitVec 8)) (i0 : Nat) : IProp GF :=
  iprop(∃ (d : Nat) (nm : Fname) (av : Aview) (ents : Std.ExtTreeMap Fname Nat compare) (nl : Nat),
    ⌜(pathElems pl).getLast? = some nm⌝ ∗
    ⌜PartialMap.get? av d = some ⟨.ADir ents, nl⟩⌝ ∗
    ⌜ents[nm]? = some i0⌝ ∗
    P (nparElems pl).length d ∗
    Fex.pfRecv av d nm i0 ∗
    pfAt (acreCommitAt (hlc := hlc) Γ appE (.AFile []) Farm) Fok ∗
    creChildUnfired (hlc := hlc) Γ (.AFile []) Farm Fun)

/-- The record the plain tail runs at: the contract's, with the shim's
cursor pair and terminal family (deviation 3). -/
abbrev sysOpenCrA (A : SysOpenArgs GF) (P Pmiss : Nat → Nat → IProp GF)
    (Fo : Pfam GF (Aview → Nat → Anode → IProp GF)) : SysOpenArgs GF :=
  { A with P := P, Pmiss := Pmiss, Fo := Fo }

/-- The shimmed record keeps the contract's static premises (the seal's
instantiation of the join at `sysOpenCrA`). -/
theorem sysOpenCrA_static (k : KCtx) (A : SysOpenArgs GF) (P Pmiss : Nat → Nat → IProp GF)
    (Fo : Pfam GF (Aview → Nat → Anode → IProp GF)) (hS : SysOpenStatic k A) :
    SysOpenStatic k (sysOpenCrA A P Pmiss Fo) :=
  ⟨hS.hj, hS.hproc, hS.htier, hS.hnoff, hS.hK, hS.hns, hS.hv0, hS.hv1⟩

/-! ## 3.  THE TWO OBSERVATION SEEDS -/

/-- The FRESH tail's receipt costs NOTHING (Rocq's `socr_obs_pure`). -/
theorem sys_open_cr_obs_pure (i0 : Nat) (n0 : FsNode) :
    ⊢ sysOpenObs (GF := GF) (sysOpenCrFoPure i0 (absRow n0)) i0 n0 := by
  unfold sysOpenObs sysOpenCrFoPure pfamTriv
  iexists (if (absRow n0).anNlink = 0 then (∅ : Aview) else PartialMap.singleton i0 (absRow n0))
  isplitr
  · ipureintro; exact arowAt_witness i0 (absRow n0)
  · ipureintro; exact ⟨rfl, rfl⟩

/-- ...and the EXISTS tail's is the real fire, tagged (Rocq's
`socr_obs_tag`). -/
theorem sys_open_cr_obs_tag (i0 : Nat) (n0 : FsNode) (Fo : Pfam GF (Aview → Nat → Anode → IProp GF)) :
    (∃ av : Aview, ⌜arowAt av i0 (absRow n0)⌝ ∗ Fo.pfRecv av i0 (absRow n0)) ⊢
      sysOpenObs (sysOpenCrFoTag i0 (absRow n0) Fo) i0 n0 := by
  simp only [sysOpenObs, sysOpenCrFoTag]
  iintro ⟨%av, %hav, HP⟩
  iexists av
  isplitr
  · ipureintro; exact hav
  iframe HP
  ipureintro; trivial

/-! ## 4.  RECOVERING THE RESIDUE FROM THE PLAIN FOLD -/

/-- THE READING IS A PREMISE, and it is what fires the walk's wand on the
"nothing happened" arm (Rocq's `socr_res_of_fail`). -/
theorem sys_open_cr_res_of_fail (Γ : FsViewNames GF) (γfs : FsNames) (cw : Nat) (R : IProp GF)
    (i0 : Nat) (Mim : Nat → List (BitVec 8)) (pv : Nat) (vom : BitVec 64) (pl0 : List (BitVec 8))
    (Fo : Pfam GF (Aview → Nat → Anode → IProp GF))
    (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF)) (hpl0 : argPathOf Mim pv pl0) :
    openPostFailPlain (hlc := hlc) Γ γfs cw Mim pv vom (sysOpenCrP R i0) (sysOpenCrPm R) Fo Ft ⊢
      |={⊤}=> R ∗
        (pfAt (aopenCommitAt (hlc := hlc) Γ appE) Fo ∨
          ∃ (i : Nat) (av : Aview) (a : Anode), ⌜arowAt av i a⌝ ∗ Fo.pfRecv av i a) ∗
        openTruncPiece (hlc := hlc) Γ vom Ft := by
  unfold openPostFailPlain openAuPlainAt exStart nameiWalkDeadEra
  simp only [sysOpenCrP, sysOpenCrPm]
  iintro (⟨Hwp, Hoc, Htc⟩ | ⟨%pl, -, (⟨⟨%kk, %d, -, Hd⟩, Hoc, Htc⟩ | ⟨%i, ⟨-, HR⟩, Hobs, Htc⟩)⟩)
  · ihave Hst := Hwp $$ %pl0 %hpl0
    imod Hst $$ %(umStartOf cw pl0) %rfl with ⟨⟨-, HR⟩, -⟩
    imodintro
    iframe HR Htc
    ileft; iexact Hoc
  · icases Hd with (⟨⟨-, HR⟩, -⟩ | ⟨HR, -⟩)
    · imodintro
      iframe HR Htc
      ileft; iexact Hoc
    · imodintro
      iframe HR Htc
      ileft; iexact Hoc
  · icases Hobs with ⟨%av, %a, %hav, HP⟩
    imodintro
    iframe HR Htc
    iright
    iexists i, av, a
    iframe HP
    ipureintro; exact hav

/-! ## 5.  RECOVERING THE RESIDUE AND THE DESCRIPTOR FROM THE PLAIN OK -/

/-- The `if omTrunc vom` receipt moved under its key (deviation 4). -/
theorem sys_open_cr_ite (b : Bool) (X Y : IProp GF) (h : X ⊢ Y) :
    (if b then X else iprop(emp)) ⊢ (if b then Y else iprop(emp)) := by
  cases b
  · exact .rfl
  · exact h

/-- THE FRESH READING (Rocq's `socr_ok_fresh_arm`): the tail's DEVICE and
DIRECTORY arms are refuted by the pure receipt (create ran at T_FILE), and
the trunc component comes out at the caller's own `Ft`. -/
theorem sys_open_cr_ok_fresh (Γ : FsViewNames GF) (R : IProp GF) (i0 : Nat) (bs : List (BitVec 8))
    (nl0 : Nat) (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF))
    (γ : FileNames) (pa : BitVec 64) (pid : BitVec 32) (Mim : Nat → List (BitVec 8)) (pv : Nat)
    (vom : BitVec 64) (sts : List FdState) (VW : ProcPriv) (MW : Nat → List (BitVec 8))
    (r : BitVec 64) :
    openPostOkPlain (hlc := hlc) Γ γ pa pid Mim pv vom (sysOpenCrP R i0)
      (sysOpenCrFoPure i0 ⟨.AFile bs, nl0⟩) Ft sts VW MW r ⊢
      R ∗
      (if omTrunc vom then
        iprop(∃ (av' : Aview) (nl' : Nat), ⌜arowAt av' i0 ⟨.AFile bs, nl'⟩⌝ ∗ Ft.pfRecv av' i0 bs)
       else iprop(emp)) ∗
      ∃ γo : GName, openFdOk γ pa pid VW MW (omReadable vom) (omWritable vom)
        (.inode i0 γo .parked) sts r := by
  unfold openPostOkPlain sysOpenCrFoPure pfamTriv
  simp only [sysOpenCrP]
  iintro ⟨%pl, %av, %i, -, ⟨%hi, HR⟩, Harm⟩
  subst hi
  icases Harm with (⟨%ma, %mi, %nl, -, -, %hbad, -⟩ | ⟨%bs0, %nl, -, %heq, Htr, Hfd⟩ |
    ⟨%ents, %nl, -, -, %hbad, -⟩)
  · obtain ⟨-, h⟩ := hbad; cases h
  · obtain ⟨-, h⟩ := heq
    simp only [Anode.mk.injEq, Absnode.AFile.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst bs0
    iframe HR Hfd
    iapply (sys_open_cr_ite (omTrunc vom) _ _ ?_) $$ Htr
    iintro ⟨%av', %hrow, HP⟩
    iexists av', nl
    iframe HP
    ipureintro; exact hrow
  · obtain ⟨-, h⟩ := hbad; cases h

/-- THE EXISTS READING (Rocq's `socr_ok_exists_arm`): the DIRECTORY arm is
refuted by the staple (ARM F-OK admits only T_FILE and T_DEVICE); the other
two ARE `openPostOkCreate`'s EXISTS sub-arms. -/
theorem sys_open_cr_ok_exists (Γ : FsViewNames GF) (R : IProp GF) (i0 : Nat) (a0 : Anode)
    (Fo : Pfam GF (Aview → Nat → Anode → IProp GF))
    (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF))
    (γ : FileNames) (pa : BitVec 64) (pid : BitVec 32) (Mim : Nat → List (BitVec 8)) (pv : Nat)
    (vom : BitVec 64) (sts : List FdState) (VW : ProcPriv) (MW : Nat → List (BitVec 8))
    (r : BitVec 64) (hnd : ∀ (ents : Std.ExtTreeMap Fname Nat compare) (nl : Nat),
      a0 ≠ ⟨.ADir ents, nl⟩) :
    openPostOkPlain (hlc := hlc) Γ γ pa pid Mim pv vom (sysOpenCrP R i0)
      (sysOpenCrFoTag i0 a0 Fo) Ft sts VW MW r ⊢
      R ∗ ∃ (av : Aview) (nl : Nat),
        (∃ bs0 : List (BitVec 8),
          ⌜arowAt av i0 ⟨.AFile bs0, nl⟩⌝ ∗
          Fo.pfRecv av i0 ⟨.AFile bs0, nl⟩ ∗
          (if omTrunc vom then
            iprop(∃ av' : Aview, ⌜arowAt av' i0 ⟨.AFile bs0, nl⟩⌝ ∗ Ft.pfRecv av' i0 bs0)
           else iprop(emp)) ∗
          ∃ γo : GName,
            openFdOk γ pa pid VW MW (omReadable vom) (omWritable vom) (.inode i0 γo .parked) sts r) ∨
        (∃ (ma mi : Nat),
          ⌜arowAt av i0 ⟨.ADev ma mi, nl⟩⌝ ∗ ⌜ma ≤ NDEV_max⌝ ∗
          Fo.pfRecv av i0 ⟨.ADev ma mi, nl⟩ ∗
          openTruncPiece (hlc := hlc) Γ vom Ft ∗
          openFdOk γ pa pid VW MW (omReadable vom) (omWritable vom) (.device ma) sts r) := by
  unfold openPostOkPlain sysOpenCrFoTag
  simp only [sysOpenCrP]
  iintro ⟨%pl, %av, %i, -, ⟨%hi, HR⟩, Harm⟩
  subst hi
  iframe HR
  icases Harm with (⟨%ma, %mi, %nl, %hrow, %hmb, ⟨-, HP⟩, Htc, Hfd⟩ |
    ⟨%bs0, %nl, %hrow, ⟨-, HP⟩, Htr, Hfd⟩ | ⟨%ents, %nl, -, -, ⟨%hbad, -⟩, -⟩)
  · iexists av, nl
    iright
    iexists ma, mi
    iframe HP Htc Hfd
    isplitr
    · ipureintro; exact hrow
    · ipureintro; exact hmb
  · iexists av, nl
    ileft
    iexists bs0
    iframe HP Htr Hfd
    ipureintro; exact hrow
  · exact absurd hbad.2.symm (hnd ents nl)

/-! ## 6.  THE TWO ARM CONVERSIONS -/

/-- Rocq's `socr_arms_fresh`. -/
theorem sys_open_cr_arms_fresh (Γ : FsViewNames GF) (γfs : FsNames) (cw : Nat) (γ : FileNames)
    (pa : BitVec 64) (pid : BitVec 32) (Mim : Nat → List (BitVec 8)) (pv : Nat) (vom : BitVec 64)
    (P Pmiss : Nat → Nat → IProp GF)
    (Farm Fun : Pfam GF (Aview → Nat → IProp GF))
    (Fok Fex : Pfam GF (Aview → Nat → Fname → Nat → IProp GF))
    (Fo : Pfam GF (Aview → Nat → Anode → IProp GF))
    (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF))
    (sts : List FdState) (VW : ProcPriv) (MW : Nat → List (BitVec 8)) (r : BitVec 64)
    (pl : List (BitVec 8)) (i0 nl0 : Nat) (hpl : argPathOf Mim pv pl) :
    openArmsPlain (hlc := hlc) Γ γfs cw γ pa pid Mim pv vom
      (sysOpenCrP (sysOpenCrFresh (hlc := hlc) Γ P Farm Fun Fok Fex Fo pl i0) i0)
      (sysOpenCrPm (sysOpenCrFresh (hlc := hlc) Γ P Farm Fun Fok Fex Fo pl i0))
      (sysOpenCrFoPure i0 ⟨.AFile [], nl0⟩) Ft sts VW MW r ⊢
      |={⊤}=> openArmsCreate (hlc := hlc) Γ γfs cw γ pa pid Mim pv vom P Pmiss Farm Fun Fok Fex Fo Ft
        sts VW MW r := by
  unfold openArmsPlain openArmsCreate
  iintro ⟨(⟨%hr, Hpriv, Hfrag, Hf⟩ | Hok), Hslot⟩
  · imod sys_open_cr_res_of_fail Γ γfs cw _ i0 Mim pv vom pl _ Ft hpl $$ Hf with ⟨HR, -, Htc⟩
    imodintro
    iframe Hslot
    ileft
    iframe Hpriv Hfrag
    isplitr
    · ipureintro; exact hr
    unfold openPostFailCreate sysOpenCrFresh
    icases HR with ⟨%d, %nm, %av, %ents, %nl, %hl, %hpre, %hib, HP, HΦ, Hdl, Hoc, Hun⟩
    iright
    iexists pl
    isplitr
    · ipureintro; exact hpl
    iright
    iexists d
    iframe HP Htc
    ileft
    iexists av, i0, nm, ents, nl
    iframe HΦ Hdl Hoc Hun
    ipureintro; exact ⟨hl, hpre, hib⟩
  · ihave ⟨HR, Htr, Hfd⟩ := sys_open_cr_ok_fresh Γ _ i0 [] nl0 Ft γ pa pid Mim pv vom sts VW MW r
      $$ Hok
    unfold sysOpenCrFresh
    icases HR with ⟨%d, %nm, %av, %ents, %nl, %hl, %hpre, %hib, HP, HΦ, Hdl, Hoc, Hun⟩
    imodintro
    iframe Hslot
    iright
    unfold openPostOkCreate
    iexists pl, d, i0, nm
    iframe HP
    isplitr
    · ipureintro; exact hpl
    isplitr
    · ipureintro; exact hl
    ileft
    iexists av, ents, nl
    iframe HΦ Hdl Hoc Htr Hun Hfd
    ipureintro; exact ⟨hpre, hib⟩

/-- Rocq's `socr_arms_exists`. -/
theorem sys_open_cr_arms_exists (Γ : FsViewNames GF) (γfs : FsNames) (cw : Nat) (γ : FileNames)
    (pa : BitVec 64) (pid : BitVec 32) (Mim : Nat → List (BitVec 8)) (pv : Nat) (vom : BitVec 64)
    (P Pmiss : Nat → Nat → IProp GF)
    (Farm Fun : Pfam GF (Aview → Nat → IProp GF))
    (Fok Fex : Pfam GF (Aview → Nat → Fname → Nat → IProp GF))
    (Fo : Pfam GF (Aview → Nat → Anode → IProp GF))
    (Ft : Pfam GF (Aview → Nat → List (BitVec 8) → IProp GF))
    (sts : List FdState) (VW : ProcPriv) (MW : Nat → List (BitVec 8)) (r : BitVec 64)
    (pl : List (BitVec 8)) (i0 : Nat) (a0 : Anode) (hpl : argPathOf Mim pv pl)
    (hnd : ∀ (ents : Std.ExtTreeMap Fname Nat compare) (nl : Nat), a0 ≠ ⟨.ADir ents, nl⟩) :
    openArmsPlain (hlc := hlc) Γ γfs cw γ pa pid Mim pv vom
      (sysOpenCrP (sysOpenCrExists (hlc := hlc) Γ P Farm Fun Fok Fex pl i0) i0)
      (sysOpenCrPm (sysOpenCrExists (hlc := hlc) Γ P Farm Fun Fok Fex pl i0))
      (sysOpenCrFoTag i0 a0 Fo) Ft sts VW MW r ⊢
      |={⊤}=> openArmsCreate (hlc := hlc) Γ γfs cw γ pa pid Mim pv vom P Pmiss Farm Fun Fok Fex Fo Ft
        sts VW MW r := by
  unfold openArmsPlain openArmsCreate
  iintro ⟨(⟨%hr, Hpriv, Hfrag, Hf⟩ | Hok), Hslot⟩
  · imod sys_open_cr_res_of_fail Γ γfs cw _ i0 Mim pv vom pl _ Ft hpl $$ Hf with ⟨HR, Hob, Htc⟩
    imodintro
    iframe Hslot
    ileft
    iframe Hpriv Hfrag
    isplitr
    · ipureintro; exact hr
    unfold openPostFailCreate sysOpenCrExists
    icases HR with ⟨%d, %nm, %av, %ents, %nl, %hl, %hrow, %hent, HP, HΦ, Hac, Hcl⟩
    iright
    iexists pl
    isplitr
    · ipureintro; exact hpl
    iright
    iexists d
    iframe HP Htc
    iright; ileft
    iexists av, i0, nm, ents, nl
    iframe HΦ Hac
    isplitr
    · ipureintro; exact hl
    isplitr
    · ipureintro; exact hrow
    isplitr
    · ipureintro; exact hent
    isplitl [Hcl]
    · ileft; iexact Hcl
    icases Hob with (Hoc | ⟨%ix, %avx, %ax, %hax, HP2⟩)
    · -- THE TAG COMES OFF THE RECEIPT AND THE REFUND IS UNTOUCHED
      ileft
      iapply (pfAt_mono_pair (aopenCommitAt (hlc := hlc) Γ appE) (aopenCommitAt (hlc := hlc) Γ appE)
        (sysOpenCrFoTag i0 a0 Fo) Fo rfl) $$ [] Hoc
      iintro Hoc
      unfold aopenCommitAt sysOpenCrFoTag
      iintro %I %ix %a %hix Ha
      imod Hoc $$ %I %ix %a %hix Ha with ⟨Ha, -, HP2⟩
      imodintro
      iframe Ha HP2
    · ihave HP2 := (show (sysOpenCrFoTag (GF := GF) i0 a0 Fo).pfRecv avx ix ax ⊢
          iprop(⌜ix = i0 ∧ ax = a0⌝ ∗ Fo.pfRecv avx ix ax) from .rfl) $$ HP2
      icases HP2 with ⟨%heq, HP2⟩
      obtain ⟨hix, -⟩ := heq
      subst hix
      iright
      iexists avx, ax
      iframe HP2
      ipureintro; exact hax
  · ihave ⟨HR, Hrest⟩ := sys_open_cr_ok_exists Γ _ i0 a0 Fo Ft γ pa pid Mim pv vom sts VW MW r hnd
      $$ Hok
    unfold sysOpenCrExists
    icases HR with ⟨%d, %nm, %av, %ents, %nl, %hl, %hrow, %hent, HP, HΦ, Hac, Hcl⟩
    imodintro
    iframe Hslot
    iright
    unfold openPostOkCreate
    iexists pl, d, i0, nm
    iframe HP
    isplitr
    · ipureintro; exact hpl
    isplitr
    · ipureintro; exact hl
    iright
    iexists av, ents, nl
    iframe HΦ Hac Hcl Hrest
    ipureintro; exact ⟨hrow, hent⟩

/-! ## 7.  THE CONTINUATION SHIMS (deviation 3) -/

/-- THE CONTINUATION IS MONOTONE IN ITS ARMS, under a fupd (the loop pays
it; `SysOpenParts.sysOpenK_mono`'s twin). -/
theorem sysOpenK_mono_fupd (k : KCtx) (ns : Nat) (V : ProcPriv) (M : Nat → List (BitVec 8))
    (ARMS ARMS' : ProcPriv → (Nat → List (BitVec 8)) → BitVec 64 → IProp GF) (c : CPU) :
    sysOpenK (hlc := hlc) k ns V M ARMS c ⊢
      (∀ (VW : ProcPriv) (MW : Nat → List (BitVec 8)) (r : BitVec 64),
        ARMS' VW MW r -∗ |={⊤}=> ARMS VW MW r) -∗
      sysOpenK (hlc := hlc) k ns V M ARMS' c := by
  unfold sysOpenK
  iintro H Hw %spie %spp %R' %P' %hcs %hext Hk Hpc Hte Hce Hbs Hir Harms
  iapply wpLoop_fupd
  imod Hw $$ %_ %_ %_ Harms with Harms
  imodintro
  iapply H $$ %spie %spp %R' %P' %hcs %hext Hk Hpc Hte Hce Hbs Hir Harms

/-- The FRESH continuation shim: the create arms' continuation, read at the
shimmed record (Rocq's first inline `iAssert` of `so_entry_c_au`). -/
theorem sys_open_cr_post_fresh (k : KCtx) (A : SysOpenArgs GF)
    (Farm Fun : Pfam GF (Aview → Nat → IProp GF))
    (Fok Fex : Pfam GF (Aview → Nat → Fname → Nat → IProp GF))
    (pl : List (BitVec 8)) (i0 nl0 : Nat) (hpl : argPathOf (sysOpenIm A) A.v.toNat pl) :
    (∀ c : CPU, sysOpenPostC (hlc := hlc) k A Farm Fun Fok Fex c) ⊢
      ∀ c : CPU, sysOpenPostP (hlc := hlc) k
        (sysOpenCrA A
          (sysOpenCrP (sysOpenCrFresh (hlc := hlc) (fsGammaL fscFs) A.P Farm Fun Fok Fex A.Fo pl i0) i0)
          (sysOpenCrPm (sysOpenCrFresh (hlc := hlc) (fsGammaL fscFs) A.P Farm Fun Fok Fex A.Fo pl i0))
          (sysOpenCrFoPure i0 ⟨.AFile [], nl0⟩)) c := by
  iintro HΦ %c
  ispecialize HΦ $$ %c
  iapply (sysOpenK_mono_fupd k A.ns A.V A.M _ _ c) $$ HΦ
  iintro %VW %MW %r H
  iapply (sys_open_cr_arms_fresh (fsGammaL fscFs) fscFs A.V.cwi A.γ (procAddr A.j) A.pid
    (sysOpenIm A) A.v.toNat A.vom A.P A.Pmiss Farm Fun Fok Fex A.Fo A.Ft A.sts VW MW r pl i0 nl0 hpl) $$ H

/-- The EXISTS continuation shim (Rocq's second inline `iAssert`). -/
theorem sys_open_cr_post_exists (k : KCtx) (A : SysOpenArgs GF)
    (Farm Fun : Pfam GF (Aview → Nat → IProp GF))
    (Fok Fex : Pfam GF (Aview → Nat → Fname → Nat → IProp GF))
    (pl : List (BitVec 8)) (i0 : Nat) (a0 : Anode) (hpl : argPathOf (sysOpenIm A) A.v.toNat pl)
    (hnd : ∀ (ents : Std.ExtTreeMap Fname Nat compare) (nl : Nat), a0 ≠ ⟨.ADir ents, nl⟩) :
    (∀ c : CPU, sysOpenPostC (hlc := hlc) k A Farm Fun Fok Fex c) ⊢
      ∀ c : CPU, sysOpenPostP (hlc := hlc) k
        (sysOpenCrA A
          (sysOpenCrP (sysOpenCrExists (hlc := hlc) (fsGammaL fscFs) A.P Farm Fun Fok Fex pl i0) i0)
          (sysOpenCrPm (sysOpenCrExists (hlc := hlc) (fsGammaL fscFs) A.P Farm Fun Fok Fex pl i0))
          (sysOpenCrFoTag i0 a0 A.Fo)) c := by
  iintro HΦ %c
  ispecialize HΦ $$ %c
  iapply (sysOpenK_mono_fupd k A.ns A.V A.M _ _ c) $$ HΦ
  iintro %VW %MW %r H
  iapply (sys_open_cr_arms_exists (fsGammaL fscFs) fscFs A.V.cwi A.γ (procAddr A.j) A.pid
    (sysOpenIm A) A.v.toNat A.vom A.P A.Pmiss Farm Fun Fok Fex A.Fo A.Ft A.sts VW MW r pl i0 a0 hpl hnd) $$ H

end

end Xv6
