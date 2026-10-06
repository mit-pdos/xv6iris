/-
Weak: **the per-node EWP rules for the DISK THREAD** (M5 C4a).

Rocq: `iris/WeakEvDisk.v` @ xxvzwolszwmp (1cc222280).

## The Rocq header, in substance

Design: `claude-notes/design/weak-memory-m5.md`; the language is `WeakEvLang` §5 (`ediskStep`),
the device program is `VirtioProg.DM`.  `WeakEvLift` lifts one event of a HART; this file lifts
one event of the DISK, an ordinary weak-memory agent running `VirtioProg.virtioProg` node by
node at its own `Wstate`.

(A) THE DISK'S `Wstate` IS SYNTAX, NOT GHOST STATE: `dws` rides in `EDisk gen dp dws`, and
    `weakStateInterp` requires NOTHING of the disk's view (`wsBounded` and the φ conjunct
    quantify over harts only).  So a disk LOAD owes no φ payment, and a disk STORE owes only
    what a foreign append owes (`noViolationDma`, `wsBoundedMono`, `wlogWf` of the message);
    the C/D/S retarget of `wlatInterp` is left to the CLIENT (E).
(B) THE LATCH ABSORBER.  In Rocq the PLIC latch was an arm of the disk's step, enabled at every
    `dp`, and `ewp_edisk_latch` absorbed it once by an internal Löb over the plic state; every
    rule's continuation is quantified over the reached plic state `p0` with the witness
    `plicLatched p p0`, ▷-guarded, and invoked lazily at mask ⊤ after the step.
(C) READ ENABLEDNESS: `ewpDiskRead` takes a persistent, pure-concluding enabledness extractor.
(D) NO `DRet DWild` RULE (deliberate: a driver proof must make that node unreachable).
(E) `ewpDiskWrite` hands the client `wlatInterp img log` and demands
    `wlatInterp img (log ++ [⟨paZ pa, bs, some nDisk, ddevClass dws⟩])` back.

## Deviations from Rocq

1. THE LATCH ARM IS ABSENT (forced by `Weak/WeakEvLang.lean` deviation 2: in Lean the PLIC
   program itself samples the virtio level and latches it, so the latch is a step of the
   `EDev .plic` thread and `ediskStep` has seven arms).  Consequences, all statements otherwise
   Rocq's:
   - `ediskNolatch` IS `ediskStep` (the same seven arms); `ediskLatchArm` is `False`, so
     `ediskStepSplit` holds as stated.
   - `ewpEdiskLatch` keeps Rocq's statement (the `plicFrag p` premise, the `p0` quantifier, the
     `plicLatched p p0` witness, the ▷-guarded lazy continuation) but its proof needs no Löb:
     the one step is always the node's own arm, taken at `p0 = p`.
   - `plicLatched` is the reflexive-transitive closure of the Lean gateway
     `MachCSL.Plic.latch p virtioIrq` (total in Lean; Rocq's `plic_latch` was partial).
   The plic/virtio fragments are `devFragAt MachGS.era .plic p` / `.virtio v` (the Rocq
   prototype's `plic_frag`/`virtio_frag`, `MachCSL.Resources`).
2. `dev_interp` is the four-device `devInterpAt MachGS.era` (Rocq: uart ∗ plic ∗ virtio); the
   per-device accessor Rocq destructs inline is the Lean-only `ediskDevAcc`/`ediskDevAccRo`.
3. Statement shapes as `WeakGhost` deviation 9 (`P -∗ Q -∗ R` ↦ `P ∗ Q ⊢ R`); `EWP e @ ⊤` is
   `ewpTriv (hlc := hlc) (GF := GF) ⊤ e`; `pa_z` ↦ `paZ`, `img_z` ↦ `imgZ`, `tvs.*1/.*2` ↦
   `tvs.map Prod.fst/snd`, `S (length l)` ↦ `l.length + 1`, `gmap Arch.pa (bv 8)` ↦ `Mem`;
   `dvirtio`/`set_dvirtio` ↦ `WeakEvLang`'s Lean-only `dvirtio`/`setDvirtio`.
4. `ewg_dev_id` is `rfl` (structure eta).  `plic_latched_refl` (a `Reflexive` instance) is the
   theorem `plicLatchedRefl`.

**File-qualified names:** `WeakEvDisk.weakStateInterpLat` (duplicated with `WeakGhost`).

**Rocq → Lean name map.**  `edisk_nolatch` `ediskNolatch`, `edisk_latch_arm` `ediskLatchArm`,
`edisk_step_split` `ediskStepSplit`, `edisk_nolatch_step` `ediskNolatchStep`, `ewg_dev_id`
`ewgDevId`, `weak_state_interp_dev` `weakStateInterpDev`, `weak_state_interp_dev_ro`
`weakStateInterpDevRo`, `weak_state_interp_lat` `WeakEvDisk.weakStateInterpLat`,
`weak_state_interp_dma` `weakStateInterpDma`, `ewp_edisk` `ewpEdisk`, `plic_latched`
`plicLatched`, `plic_latched_refl` `plicLatchedRefl`, `ewp_edisk_latch` `ewpEdiskLatch`,
`ewp_disk_start` `ewpDiskStart`, `ewp_disk_read` `ewpDiskRead`, `ewp_disk_write` `ewpDiskWrite`,
`ewp_disk_fence` `ewpDiskFence`, `ewp_disk_commit` `ewpDiskCommit`, `ewp_disk_idle`
`ewpDiskIdle`.
Lean-only: `ediskDevIdx`, `ediskDevIdxGet`, `ediskDevIdxNe`, `ediskDevStatesSetSelf`,
`ediskDevAcc`, `ediskDevAccRo`.

**Dropped:** none.

**Statements checked** (by hand, against Rocq): all; the changed ones are the deviations above.
-/
import Weak.WeakEvLift

namespace Weak

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open LeanRV64D

/-! ## 1. The step relation, split at the latch -/

/-- The seven PROGRAM arms of the disk's step (deviation 1: all of `ediskStep`). -/
def ediskNolatch (gen : Nat) (dp : Option (DM Dres)) (dws : Wstate) (σ : WGState) (e' : EExpr)
    (σ' : WGState) : Prop :=
  ediskStep gen dp dws σ e' σ'

/-- The PLIC latch arm: absent in Lean (deviation 1). -/
def ediskLatchArm (_gen : Nat) (_dp : Option (DM Dres)) (_dws : Wstate) (_σ : WGState)
    (_e' : EExpr) (_σ' : WGState) : Prop :=
  False

theorem ediskStepSplit (gen : Nat) (dp : Option (DM Dres)) (dws : Wstate) (σ : WGState)
    (e' : EExpr) (σ' : WGState) :
    ediskStep gen dp dws σ e' σ' ↔
      ediskNolatch gen dp dws σ e' σ' ∨ ediskLatchArm gen dp dws σ e' σ' :=
  ⟨Or.inl, fun h => h.elim id False.elim⟩

theorem ediskNolatchStep (gen : Nat) (dp : Option (DM Dres)) (dws : Wstate) (σ : WGState)
    (e' : EExpr) (σ' : WGState) :
    ediskNolatch gen dp dws σ e' σ' → ediskStep gen dp dws σ e' σ' :=
  fun h => (ediskStepSplit gen dp dws σ e' σ').2 (Or.inl h)

/-- The record identity the fabric-reading arms need. -/
theorem ewgDevId (σ : WGState) : ewgDev σ σ.wgdev = σ := rfl

/-! ## 2. Opening `weakStateInterp` for a NON-HART author -/

/-- The index of a device in `DevId.all` (Lean-only). -/
def ediskDevIdx : DevId → Nat
  | .uart .uart0 => 0
  | .uart .uart1 => 1
  | .plic => 2
  | .virtio => 3

theorem ediskDevIdxGet (d : DevId) : DevId.all[ediskDevIdx d]? = some d := by
  cases d with
  | uart i => cases i <;> rfl
  | plic => rfl
  | virtio => rfl

theorem ediskDevIdxNe {k : Nat} {y : DevId} (hk : DevId.all[k]? = some y) (d : DevId)
    (hne : k ≠ ediskDevIdx d) : y ≠ d := by
  rintro rfl
  apply hne
  rcases k with _ | _ | _ | _ | k
  · simp [DevId.all] at hk; subst hk; rfl
  · simp [DevId.all] at hk; subst hk; rfl
  · simp [DevId.all] at hk; subst hk; rfl
  · simp [DevId.all] at hk; subst hk; rfl
  · simp [DevId.all] at hk

theorem ediskDevStatesSetSelf (ds : DevStates) (d : DevId) : ds.set d (ds.st d) = ds := by
  cases ds with
  | mk st =>
    simp only [DevStates.set, DevStates.mk.injEq]
    funext d'
    split
    · next h => subst h; rfl
    · rfl

section interp

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- One device's authoritative mirror out of the four-device interpretation (Lean-only). -/
theorem ediskDevAcc (ds : DevStates) (d : DevId) :
    devInterpAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) ds ⊢
      devAuthAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) d (ds.st d) ∗
      ∀ s' : DevSt d, devAuthAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) d s' -∗
        devInterpAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) (ds.set d s') := by
  have hget := ediskDevIdxGet d
  unfold devInterpAt
  iintro Hdev
  icases BigSepL.bigSepL_lookup_acc_impl
      (Φ := fun _ d' => devAuthAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) d' (ds.st d')) hget $$ Hdev
    with ⟨Hd, Hclose⟩
  iframe Hd
  iintro %s' Hs'
  iapply Hclose $$ %(fun _ d' => devAuthAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) d' ((ds.set d s').st d'))
  · imodintro
    iintro %k %y %hk %hne Hy
    have hy : y ≠ d := ediskDevIdxNe hk d hne
    show iprop(devAuthAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) y (ds.st y) ⊢
      devAuthAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) y ((ds.set d s').st y))
    rw [DevStates.set_other ds d y s' hy]
  · show iprop(devAuthAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) d s' ⊢
      devAuthAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) d ((ds.set d s').st d))
    rw [DevStates.set_same]

/-- ... closing at the same state (Lean-only). -/
theorem ediskDevAccRo (ds : DevStates) (d : DevId) :
    devInterpAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) ds ⊢
      devAuthAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) d (ds.st d) ∗
      (devAuthAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) d (ds.st d) -∗
        devInterpAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) ds) := by
  iintro H
  icases ediskDevAcc ds d $$ H with ⟨Hd, Hcl⟩
  iframe Hd
  iintro Hd
  ihave H := Hcl $$ %(ds.st d) Hd
  rw [ediskDevStatesSetSelf ds d]
  iexact H

theorem weakStateInterpDev (σ : WGState) :
    weakStateInterp (hlc := hlc) (GF := GF) σ ⊢
      devInterpAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) σ.wgdev ∗
      ∀ d' : DevStates, devInterpAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) d' -∗
        weakStateInterp (hlc := hlc) (GF := GF) (ewgDev σ d') := by
  unfold weakStateInterp
  iintro ⟨%Hpin, %Hbnd, %Hnv, %Hwf, Hgr, Hdev, Hlog, Hlat, Hws⟩
  iframe Hdev
  iintro %d' Hd
  dsimp only [ewgDev]
  isplitr
  · ipureintro; exact Hpin
  isplitr
  · ipureintro; exact Hbnd
  isplitr
  · ipureintro; exact Hnv
  isplitr
  · ipureintro; exact Hwf
  iframe Hgr Hd Hlog Hlat Hws

/-- A `devInterpAt` borrow that closes at σ itself. -/
theorem weakStateInterpDevRo (σ : WGState) :
    weakStateInterp (hlc := hlc) (GF := GF) σ ⊢
      devInterpAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) σ.wgdev ∗
      (devInterpAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) σ.wgdev -∗
        weakStateInterp (hlc := hlc) (GF := GF) σ) := by
  iintro H
  icases weakStateInterpDev σ $$ H with ⟨Hd, Hcl⟩
  iframe Hd
  iintro Hd
  iapply (show weakStateInterp (hlc := hlc) (GF := GF) (ewgDev σ σ.wgdev) ⊢
    weakStateInterp (hlc := hlc) (GF := GF) σ from .rfl)
  iapply Hcl $$ %σ.wgdev Hd

/-- THE READ-ONLY BORROW: the log authority and the latest-write map, handed out and taken back
AT THE SAME LOG. -/
theorem WeakEvDisk.weakStateInterpLat (σ : WGState) :
    weakStateInterp (hlc := hlc) (GF := GF) σ ⊢
      ⌜wlogWf σ.wglog⌝ ∗ wlogAuth (GF := GF) σ.wglog ∗ wlatInterp (GF := GF) σ.wgimg σ.wglog ∗
      (wlogAuth (GF := GF) σ.wglog -∗ wlatInterp (GF := GF) σ.wgimg σ.wglog -∗
        weakStateInterp (hlc := hlc) (GF := GF) σ) := by
  unfold weakStateInterp
  iintro ⟨%Hpin, %Hbnd, %Hnv, %Hwf, Hgr, Hdev, Hlog, Hlat, Hws⟩
  isplitr
  · ipureintro; exact Hwf
  iframe Hlog Hlat
  iintro Hlog Hlat
  isplitr
  · ipureintro; exact Hpin
  isplitr
  · ipureintro; exact Hbnd
  isplitr
  · ipureintro; exact Hnv
  isplitr
  · ipureintro; exact Hwf
  iframe Hgr Hdev Hlog Hlat Hws

/-- THE DMA APPEND.  `wsBounded` survives by `wsBoundedMono`, the φ conjunct by
`noViolationDma`, `wlogWf` by the append; the `wlatInterp` retarget is the CALLER's. -/
theorem weakStateInterpDma (σ : WGState) :
    weakStateInterp (hlc := hlc) (GF := GF) σ ⊢
      ⌜wlogWf σ.wglog⌝ ∗ wlogAuth (GF := GF) σ.wglog ∗ wlatInterp (GF := GF) σ.wgimg σ.wglog ∗
      (∀ ms : List Wmsg, ⌜wlogWf ms⌝ -∗
        wlogAuth (GF := GF) (σ.wglog ++ ms) -∗ wlatInterp (GF := GF) σ.wgimg (σ.wglog ++ ms) -∗
        weakStateInterp (hlc := hlc) (GF := GF) (ewgLog σ (σ.wglog ++ ms))) := by
  unfold weakStateInterp
  iintro ⟨%Hpin, %Hbnd, %Hnv, %Hwf, Hgr, Hdev, Hlog, Hlat, Hws⟩
  isplitr
  · ipureintro; exact Hwf
  iframe Hlog Hlat
  iintro %ms %Hms Hlog Hlat
  dsimp only [ewgLog]
  isplitr
  · ipureintro; exact Hpin
  isplitr
  · ipureintro
    intro c
    exact wsBoundedMono _ _ _ (Hbnd c) (by rw [List.length_append]; omega)
  isplitr
  · ipureintro; exact noViolationDma σ.wglog ms σ.wgws Hnv Hbnd
  isplitr
  · ipureintro
    intro m hm
    rcases List.mem_append.1 hm with h | h
    · exact Hwf m h
    · exact Hms m h
  iframe Hgr Hdev Hlog Hlat Hws

end interp

/-! ## 3. The core lifting rule — the twin of `WeakEvLift.ewpEcycle` -/

section core

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

theorem ewpEdisk (gen : Nat) (dp : Option (DM Dres)) (dws : Wstate) :
    gen = 0 →
    (∀ σ : WGState, weakStateInterp (hlc := hlc) (GF := GF) σ ={⊤,∅}=∗
      ⌜∃ e' σ', ediskStep gen dp dws σ e' σ'⌝ ∗
      ▷ (∀ e' σ', ⌜ediskStep gen dp dws σ e' σ'⌝ ={∅,⊤}=∗
          weakStateInterp (hlc := hlc) (GF := GF) σ' ∗ ewpTriv (hlc := hlc) (GF := GF) ⊤ e')) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (.EDisk gen dp dws) := by
  intro hgen
  iintro H
  unfold ewpTriv
  iapply wp_lift_step rfl
  iintro %σ %ns %obs %obs' %nt Hσ
  rw [weakStateInterpEq]
  icases weakStateInterpPin σ $$ Hσ with ⟨%Hpin, Hσ⟩
  have hlive : ethreadLive σ gen := ⟨Hpin.1, by rw [hgen]; exact Hpin.2⟩
  imod H $$ %σ Hσ with ⟨%Hred, Hk⟩
  imodintro
  isplitr
  · ipureintro
    obtain ⟨e', σ', hs⟩ := Hred
    exact ⟨[], e', σ', [], rfl, rfl, Or.inl ⟨hlive, hs⟩⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨_, rfl, harm⟩ := eprimStepDiskInv gen dp dws σ obs e₂ σ₂ eₜ Hstep
  rcases harm with ⟨_, hd⟩ | ⟨hnl, _⟩
  case inr => exact absurd hlive hnl
  imod Hk $$ %e₂ %σ₂ %hd with ⟨Hσ', HWP⟩
  imodintro
  rw [weakStateInterpEq]
  isplitl [Hσ']
  · iexact Hσ'
  isplitl [HWP]
  · iexact HWP
  · exact BigSepL.bigSepL_nil_intro

end core

/-! ## 4. THE LATCH ABSORBER (header (B); deviation 1: no latch arm, no Löb) -/

/-- Rocq `plic_latched`: the reflexive-transitive closure of one virtio latch. -/
def plicLatched : PlicState → PlicState → Prop :=
  rtc (fun p1 p2 => Plic.latch p1 virtioIrq = p2)

theorem plicLatchedRefl (p : PlicState) : plicLatched p p := rtc_refl p

section latch

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

theorem ewpEdiskLatch (gen : Nat) (dp : Option (DM Dres)) (dws : Wstate) (p : PlicState)
    (EN CONT : IProp GF) :
    gen = 0 →
    □ (∀ σ : WGState, EN -∗ weakStateInterp (hlc := hlc) (GF := GF) σ -∗
        ⌜∃ e' σ', ediskNolatch gen dp dws σ e' σ'⌝) ∗
    □ (∀ (p0 : PlicState) (σ : WGState) (e' : EExpr) (σ' : WGState),
        ⌜plicLatched p p0⌝ -∗ ⌜ediskNolatch gen dp dws σ e' σ'⌝ -∗
        devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .plic p0 -∗ EN -∗ CONT -∗
        weakStateInterp (hlc := hlc) (GF := GF) σ ={⊤}=∗
        weakStateInterp (hlc := hlc) (GF := GF) σ' ∗ ewpTriv (hlc := hlc) (GF := GF) ⊤ e') ∗
    devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .plic p ∗ EN ∗ ▷ CONT ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (.EDisk gen dp dws) := by
  intro hgen
  iintro ⟨#Hen, #Hmain, Hp, HEN, Hcont⟩
  iapply ewpEdisk gen dp dws hgen
  iintro %σ Hσ
  ihave %Hred := Hen $$ %σ HEN Hσ
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  isplitr
  · ipureintro
    obtain ⟨e0, σ0, hs⟩ := Hred
    exact ⟨e0, σ0, ediskNolatchStep gen dp dws σ e0 σ0 hs⟩
  inext
  iintro %e' %σ' %Hstep
  rcases (ediskStepSplit gen dp dws σ e' σ').1 Hstep with Hnl | Hl
  case inr => exact Hl.elim
  imod Hmask
  iapply Hmain $$ %p %σ %e' %σ' %(plicLatchedRefl p) %Hnl Hp HEN Hcont Hσ

end latch

/-! ## 5. The per-node rules (no rule for `DRet DWild`, header (D)) -/

section rules

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- 5a. START (`dp = none`): read the fabric, elaborate the program. -/
theorem ewpDiskStart (gen : Nat) (dws : Wstate) (v : VirtioState) (p : PlicState) :
    gen = 0 →
    devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .virtio v ∗
    devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .plic p ∗
    ▷ (∀ p0 : PlicState, ⌜plicLatched p p0⌝ -∗
        devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .plic p0 -∗
        devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .virtio v -∗
        ewpTriv (hlc := hlc) (GF := GF) ⊤ (.EDisk gen (some (virtioProg v)) dws)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (.EDisk gen none dws) := by
  intro hgen
  iintro ⟨Hv, Hp, Hcont⟩
  iapply ewpEdiskLatch gen none dws p (devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .virtio v)
    (iprop(∀ p0 : PlicState, ⌜plicLatched p p0⌝ -∗
        devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .plic p0 -∗
        devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .virtio v -∗
        ewpTriv (hlc := hlc) (GF := GF) ⊤ (.EDisk gen (some (virtioProg v)) dws))) hgen
  isplitr
  · imodintro
    iintro %σ _ _
    ipureintro
    exact ⟨_, _, Or.inl ⟨rfl, rfl, rfl⟩⟩
  isplitr
  · imodintro
    iintro %p0 %σ %e' %σ' %Hlt %Hstep Hp Hv Hcont Hσ
    unfold ediskNolatch ediskStep at Hstep
    rcases Hstep with ⟨-, rfl, hσ⟩ | ⟨_, _, _, _, _, ⟨⟩, -⟩ | ⟨_, _, _, ⟨⟩, -⟩ | ⟨_, ⟨⟩, -⟩ |
      ⟨_, ⟨⟩, -⟩ | ⟨_, ⟨⟩, -⟩ | ⟨⟨⟩, -⟩
    subst σ'
    icases weakStateInterpDevRo σ $$ Hσ with ⟨Hd, Hcl⟩
    icases ediskDevAccRo σ.wgdev .virtio $$ Hd with ⟨Hva, Hdcl⟩
    ihave %hv := devAgreeAt _ .virtio _ _ $$ [Hva Hv]
    · iframe Hva Hv
    subst hv
    unfold dvirtio
    imodintro
    isplitl [Hcl Hdcl Hva]
    · iapply Hcl
      iapply Hdcl $$ Hva
    · iapply Hcont $$ %p0 %Hlt Hp Hv
  · iframe Hp Hv Hcont

/-- 5b. THE DEVICE READ — the racy form, at `dws`. -/
theorem ewpDiskRead (gen : Nat) (dws : Wstate) (pa : PAddr) (n : Nat) (aq : Bool)
    (kk : List (BitVec 8) → DM Dres) (p : PlicState) (EN : IProp GF) :
    gen = 0 →
    □ (∀ (img : Mem) (log : List Wmsg),
        EN -∗ wlogLb (GF := GF) log -∗ wlatInterp (GF := GF) img log -∗
        ⌜∃ tvs : List (Nat × BitVec 8), tvs.length = n ∧
          readOk (imgZ img) log dws aq false (paZ pa) tvs⌝) ∗
    EN ∗ devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .plic p ∗
    ▷ (∀ (σ : WGState) (p0 : PlicState) (tvs : List (Nat × BitVec 8)),
        ⌜plicLatched p p0⌝ -∗ ⌜wlogWf σ.wglog⌝ -∗ wlogLb (GF := GF) σ.wglog -∗
        ⌜tvs.length = n⌝ -∗
        ⌜readOk (imgZ σ.wgimg) σ.wglog dws aq false (paZ pa) tvs⌝ -∗
        devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .plic p0 -∗ EN -∗
        wlatInterp (GF := GF) σ.wgimg σ.wglog ={⊤}=∗
        wlatInterp (GF := GF) σ.wgimg σ.wglog ∗
        ewpTriv (hlc := hlc) (GF := GF) ⊤
          (.EDisk gen (some (kk (tvs.map Prod.snd))) (loadPostRun dws aq (paZ pa) (tvs.map Prod.fst)))) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (.EDisk gen (some (DRead pa n aq kk)) dws) := by
  intro hgen
  iintro ⟨#Hen, HEN, Hp, Hcont⟩
  iapply ewpEdiskLatch gen (some (DRead pa n aq kk)) dws p EN
    (iprop(∀ (σ : WGState) (p0 : PlicState) (tvs : List (Nat × BitVec 8)),
        ⌜plicLatched p p0⌝ -∗ ⌜wlogWf σ.wglog⌝ -∗ wlogLb (GF := GF) σ.wglog -∗
        ⌜tvs.length = n⌝ -∗
        ⌜readOk (imgZ σ.wgimg) σ.wglog dws aq false (paZ pa) tvs⌝ -∗
        devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .plic p0 -∗ EN -∗
        wlatInterp (GF := GF) σ.wgimg σ.wglog ={⊤}=∗
        wlatInterp (GF := GF) σ.wgimg σ.wglog ∗
        ewpTriv (hlc := hlc) (GF := GF) ⊤
          (.EDisk gen (some (kk (tvs.map Prod.snd)))
            (loadPostRun dws aq (paZ pa) (tvs.map Prod.fst))))) hgen
  isplitr
  · imodintro
    iintro %σ HEN Hσ
    icases WeakEvDisk.weakStateInterpLat σ $$ Hσ with ⟨-, Hlog, Hlat, -⟩
    icases wlogSnapshot σ.wglog $$ Hlog with ⟨-, #Hlb⟩
    icases Hen $$ %σ.wgimg %σ.wglog HEN Hlb Hlat with %⟨tvs, hlen, hrd⟩
    ipureintro
    exact ⟨_, _, Or.inr (Or.inl ⟨pa, n, aq, kk, tvs, rfl, hlen, hrd, rfl, rfl⟩)⟩
  isplitr
  · imodintro
    iintro %p0 %σ %e' %σ' %Hlt %Hstep Hp HEN Hcont Hσ
    unfold ediskNolatch ediskStep at Hstep
    rcases Hstep with ⟨⟨⟩, -⟩ | ⟨_, _, _, _, tvs, ⟨⟩, hlen, hrd, rfl, hσ⟩ | ⟨_, _, _, ⟨⟩, -⟩ |
      ⟨_, ⟨⟩, -⟩ | ⟨_, ⟨⟩, -⟩ | ⟨_, ⟨⟩, -⟩ | ⟨⟨⟩, -⟩
    subst σ'
    icases WeakEvDisk.weakStateInterpLat σ $$ Hσ with ⟨%Hwf, Hlog, Hlat, Hcl⟩
    icases wlogSnapshot σ.wglog $$ Hlog with ⟨Hlog, #Hlb⟩
    imod Hcont $$ %σ %p0 %tvs %Hlt %Hwf Hlb %hlen %hrd Hp HEN Hlat with ⟨Hlat, Hwp⟩
    imodintro
    isplitl [Hcl Hlog Hlat]
    · iapply Hcl $$ Hlog Hlat
    · iexact Hwp
  · iframe Hp HEN Hcont

/-- 5c. THE DEVICE WRITE — the log append, at `dws`. -/
theorem ewpDiskWrite (gen : Nat) (dws : Wstate) (pa : PAddr) (bs : List (BitVec 8)) (kk : DM Dres)
    (p : PlicState) :
    gen = 0 →
    bs ≠ [] →
    paZ pa + (bs.length : Int) ≤ 18446744073709551616 →
    devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .plic p ∗
    ▷ (∀ (σ : WGState) (p0 : PlicState),
        ⌜plicLatched p p0⌝ -∗ ⌜wlogWf σ.wglog⌝ -∗ wlogLb (GF := GF) σ.wglog -∗
        devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .plic p0 -∗
        wlatInterp (GF := GF) σ.wgimg σ.wglog ={⊤}=∗
        wlatInterp (GF := GF) σ.wgimg (σ.wglog ++ [⟨paZ pa, bs, some nDisk, ddevClass dws⟩]) ∗
        ewpTriv (hlc := hlc) (GF := GF) ⊤
          (.EDisk gen (some kk) (storePostRun dws false (paZ pa) bs.length (σ.wglog.length + 1)))) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (.EDisk gen (some (DWrite pa bs kk)) dws) := by
  intro hgen hne hfit
  iintro ⟨Hp, Hcont⟩
  iapply ewpEdiskLatch gen (some (DWrite pa bs kk)) dws p iprop(emp)
    (iprop(∀ (σ : WGState) (p0 : PlicState),
        ⌜plicLatched p p0⌝ -∗ ⌜wlogWf σ.wglog⌝ -∗ wlogLb (GF := GF) σ.wglog -∗
        devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .plic p0 -∗
        wlatInterp (GF := GF) σ.wgimg σ.wglog ={⊤}=∗
        wlatInterp (GF := GF) σ.wgimg (σ.wglog ++ [⟨paZ pa, bs, some nDisk, ddevClass dws⟩]) ∗
        ewpTriv (hlc := hlc) (GF := GF) ⊤
          (.EDisk gen (some kk)
            (storePostRun dws false (paZ pa) bs.length (σ.wglog.length + 1))))) hgen
  isplitr
  · imodintro
    iintro %σ _ _
    ipureintro
    exact ⟨_, _, Or.inr (Or.inr (Or.inl ⟨pa, bs, kk, rfl, hne, rfl, rfl⟩))⟩
  isplitr
  · imodintro
    iintro %p0 %σ %e' %σ' %Hlt %Hstep Hp _ Hcont Hσ
    unfold ediskNolatch ediskStep at Hstep
    rcases Hstep with ⟨⟨⟩, -⟩ | ⟨_, _, _, _, _, ⟨⟩, -⟩ | ⟨_, _, _, ⟨⟩, -, rfl, rfl⟩ |
      ⟨_, ⟨⟩, -⟩ | ⟨_, ⟨⟩, -⟩ | ⟨_, ⟨⟩, -⟩ | ⟨⟨⟩, -⟩
    icases weakStateInterpDma σ $$ Hσ with ⟨%Hwf, Hlog, Hlat, Hcl⟩
    icases wlogSnapshot σ.wglog $$ Hlog with ⟨Hlog, #Hlb⟩
    imod wlogUpdate σ.wglog [⟨paZ pa, bs, some nDisk, ddevClass dws⟩] $$ Hlog with Hlog
    imod Hcont $$ %σ %p0 %Hlt %Hwf Hlb Hp Hlat with ⟨Hlat, Hwp⟩
    have hmwf : wlogWf [(⟨paZ pa, bs, some nDisk, ddevClass dws⟩ : Wmsg)] := by
      intro m hm
      rw [List.mem_singleton] at hm
      subst hm
      show 0 ≤ paZ pa ∧ paZ pa + (bs.length : Int) ≤ 18446744073709551616
      exact ⟨by unfold paZ; omega, hfit⟩
    imodintro
    isplitl [Hcl Hlog Hlat]
    · iapply Hcl $$ %_ %hmwf Hlog Hlat
    · iexact Hwp
  · iframe Hp Hcont

/-- 5d. THE DEVICE FENCE — pure, `fence rw,rw` at `dws`. -/
theorem ewpDiskFence (gen : Nat) (dws : Wstate) (kk : DM Dres) (p : PlicState) :
    gen = 0 →
    devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .plic p ∗
    ▷ (∀ p0 : PlicState, ⌜plicLatched p p0⌝ -∗
        devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .plic p0 -∗
        ewpTriv (hlc := hlc) (GF := GF) ⊤
          (.EDisk gen (some kk) (Weak.fencePost dws true true true true))) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (.EDisk gen (some (DFence kk)) dws) := by
  intro hgen
  iintro ⟨Hp, Hcont⟩
  iapply ewpEdiskLatch gen (some (DFence kk)) dws p iprop(emp)
    (iprop(∀ p0 : PlicState, ⌜plicLatched p p0⌝ -∗
        devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .plic p0 -∗
        ewpTriv (hlc := hlc) (GF := GF) ⊤
          (.EDisk gen (some kk) (Weak.fencePost dws true true true true)))) hgen
  isplitr
  · imodintro
    iintro %σ _ _
    ipureintro
    exact ⟨_, _, Or.inr (Or.inr (Or.inr (Or.inl ⟨kk, rfl, rfl, rfl⟩)))⟩
  isplitr
  · imodintro
    iintro %p0 %σ %e' %σ' %Hlt %Hstep Hp _ Hcont Hσ
    unfold ediskNolatch ediskStep at Hstep
    rcases Hstep with ⟨⟨⟩, -⟩ | ⟨_, _, _, _, _, ⟨⟩, -⟩ | ⟨_, _, _, ⟨⟩, -⟩ |
      ⟨_, ⟨⟩, rfl, hσ⟩ | ⟨_, ⟨⟩, -⟩ | ⟨_, ⟨⟩, -⟩ | ⟨⟨⟩, -⟩
    subst σ'
    imodintro
    iframe Hσ
    iapply Hcont $$ %p0 %Hlt Hp
  · iframe Hp Hcont

/-- 5e. THE COMMIT (`DRet (DDone δ)`): apply the burst's delta to the CURRENT fabric state. -/
theorem ewpDiskCommit (gen : Nat) (dws : Wstate) (delta : VirtioState → VirtioState)
    (v : VirtioState) (p : PlicState) :
    gen = 0 →
    devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .virtio v ∗
    devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .plic p ∗
    ▷ (∀ p0 : PlicState, ⌜plicLatched p p0⌝ -∗
        devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .plic p0 -∗
        devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .virtio (delta v) -∗
        ewpTriv (hlc := hlc) (GF := GF) ⊤ (.EDisk gen none dws)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (.EDisk gen (some (DRet (DDone delta))) dws) := by
  intro hgen
  iintro ⟨Hv, Hp, Hcont⟩
  iapply ewpEdiskLatch gen (some (DRet (DDone delta))) dws p
    (devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .virtio v)
    (iprop(∀ p0 : PlicState, ⌜plicLatched p p0⌝ -∗
        devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .plic p0 -∗
        devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .virtio (delta v) -∗
        ewpTriv (hlc := hlc) (GF := GF) ⊤ (.EDisk gen none dws))) hgen
  isplitr
  · imodintro
    iintro %σ _ _
    ipureintro
    exact ⟨_, _, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨delta, rfl, rfl, rfl⟩))))⟩
  isplitr
  · imodintro
    iintro %p0 %σ %e' %σ' %Hlt %Hstep Hp Hv Hcont Hσ
    unfold ediskNolatch ediskStep at Hstep
    rcases Hstep with ⟨⟨⟩, -⟩ | ⟨_, _, _, _, _, ⟨⟩, -⟩ | ⟨_, _, _, ⟨⟩, -⟩ |
      ⟨_, ⟨⟩, -⟩ | ⟨_, ⟨⟩, rfl, rfl⟩ | ⟨_, ⟨⟩, -⟩ | ⟨⟨⟩, -⟩
    icases weakStateInterpDev σ $$ Hσ with ⟨Hd, Hcl⟩
    icases ediskDevAcc σ.wgdev .virtio $$ Hd with ⟨Hva, Hdcl⟩
    ihave %hv := devAgreeAt _ .virtio _ _ $$ [Hva Hv]
    · iframe Hva Hv
    subst hv
    unfold dvirtio setDvirtio
    imod devUpdateAt _ .virtio _ _ (delta (σ.wgdev.st .virtio)) $$ [Hva Hv] with ⟨Hva, Hv⟩
    · iframe Hva Hv
    imodintro
    isplitl [Hcl Hdcl Hva]
    · iapply Hcl $$ %(σ.wgdev.set .virtio (delta (σ.wgdev.st .virtio)))
      iapply Hdcl $$ %(delta (σ.wgdev.st .virtio)) Hva
    · iapply Hcont $$ %p0 %Hlt Hp Hv
  · iframe Hp Hv Hcont

/-- 5f. IDLE (`DRet DIdle`): nothing was pending; back to the start. -/
theorem ewpDiskIdle (gen : Nat) (dws : Wstate) (p : PlicState) :
    gen = 0 →
    devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .plic p ∗
    ▷ (∀ p0 : PlicState, ⌜plicLatched p p0⌝ -∗
        devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .plic p0 -∗
        ewpTriv (hlc := hlc) (GF := GF) ⊤ (.EDisk gen none dws)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (.EDisk gen (some (DRet DIdle)) dws) := by
  intro hgen
  iintro ⟨Hp, Hcont⟩
  iapply ewpEdiskLatch gen (some (DRet DIdle)) dws p iprop(emp)
    (iprop(∀ p0 : PlicState, ⌜plicLatched p p0⌝ -∗
        devFragAt (hlc := hlc) (GF := GF) (MachGS.era (hlc := hlc) (GF := GF)) .plic p0 -∗
        ewpTriv (hlc := hlc) (GF := GF) ⊤ (.EDisk gen none dws))) hgen
  isplitr
  · imodintro
    iintro %σ _ _
    ipureintro
    exact ⟨_, _, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))))⟩
  isplitr
  · imodintro
    iintro %p0 %σ %e' %σ' %Hlt %Hstep Hp _ Hcont Hσ
    unfold ediskNolatch ediskStep at Hstep
    rcases Hstep with ⟨⟨⟩, -⟩ | ⟨_, _, _, _, _, ⟨⟩, -⟩ | ⟨_, _, _, ⟨⟩, -⟩ |
      ⟨_, ⟨⟩, -⟩ | ⟨_, ⟨⟩, -⟩ | ⟨_, ⟨⟩, -⟩ | ⟨-, rfl, hσ⟩
    subst σ'
    imodintro
    iframe Hσ
    iapply Hcont $$ %p0 %Hlt Hp
  · iframe Hp Hcont

end rules

end Weak
