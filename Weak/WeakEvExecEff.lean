/-
Weak: **the `execEff` → event-WP bridge** (spike M4-S1): the run predicate `epure` (`execEff`
with the world removed), its composition kit, its agreement with `execEff`, its reading as a
silent run of the event language, the derived later-free `EWP` rule, the owned-window run
`epurew` (S1b, run side), and the measured application to a real leaf (LUI + `tick_pc`).

Rocq: `iris/WeakEvExecEff.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`WeakEvLift` lifts ONE EVENT and batches consecutive SILENT events with the cursor stepper
`esil`.  The M4 retarget CONSUMES the tree's symbolic `execEff` mirrors instead; this file is the
consumption interface for the memory-free, device-free part of a run.
* §1 `epure D m t` is `execEff` with the RAM/MMIO read, RAM/MMIO write and barrier arms deleted
  (`none`) and the two register arms guarded by the footprint `r ∈ D` (as `esilNode`); `choose`
  is `none` on both sides.  The composition kit is `WeakEff`'s verbatim twin, plus `epureMono`.
* §2 `epureExecEff`: a successful `epure` IS an `execEff` run with an EMPTY trace, unchanged
  memory and devices; `execEffEpure` is the consumption form (functionality of `execEff`).
  Device-freedom is a property of the RUN, not of the state (no device state kills every access).
* §3 `epureEsilD`: `epure`'s recursion is the reflexive-transitive closure of `esilD D`.
* §4 THE DERIVED RULE, later-free (`ewpEvSilRtc` already discharges the per-node `▷`).  D3-2:
  a pure-register stretch can move `hartWs` (PARM's `step_assign`), so the rules own `hartWs` and
  hand back a `wsDepmove`.
* §5 S1b: `epurew`, the RAM arms re-enabled, emitting the `Weff` trace; agrees with `execEff`.
* §6 the measurement: the GPR footprint `Dgpr`, the `wX_bits` twins, the LUI `execute` leaf,
  `tick_pc`, their composition, and the `EWP` application `ewpEvLuiTail`.  (`sig_seip` is read
  by every instruction, ungated by `mstatus.MIE`: it must be in every footprint.)

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below).  Vocabulary as `WeakEff` deviation 1 and
   `WeakEvLift` deviations 1/4: `gset register` ↦ `List Register` (`D ⊆ D'` is `List.Subset`),
   `M X` ↦ `SailM X`, `mstate` ↦ `ExecSt` (`sregs`/`mem`/`mdev` ↦ `regs`/`mem`/`dev`),
   `set_reg` ↦ `ExecSt.setReg`, `register_lookup r rs` ↦ `rs r`, `Defs.bind`/`bind0`/`returnm`
   ↦ `>>=`/`>>= fun _ =>`/`pure`, `Interface.Ret y` ↦ `FreeM.pure y`, `tt` ↦ `()`,
   `P -∗ Q -∗ R` ↦ `P ∗ Q ⊢ R`, `EWP e @ ⊤` ↦ `ewpTriv ⊤ e`.
2. `epure`/`epurew` arms are lean-sail's `Outcome` constructors, listed exhaustively as in
   `WeakCert.execEff` (`.error` and `choose`/`readRam`/`writeRam` are `none`; `getCycleCount`
   answers `(0 : Nat)`).  `epurew`'s RAM arms are `execEff`'s: device test `mmioAcc req.pa n`
   (Rocq `dev_addr pa`), read `bmRead`, answer `.Ok (w, none)`; the write's value is
   `req.value : Option _` (`none` is stuck, as `execEff`), answer `.Ok (some true)`; the trace
   element is prepended by `Weff.cons`.
3. §6 GPR conventions (`Weak/ExecSC.lean`): Rocq's `if uint rd =? 0 then s else set_reg s
   (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)` ↦ `s.setGpr rd v`.  The footprint
   premise `∀ n : Z, R_bitvector_64 (gpr_of_Z n) ∈ D` is kept over the Lean-only
   `WeakEvExecEff.gprOfZ` (Rocq `WpGpr.gpr_of_Z`, same if-chain); `luival` (Rocq
   `WpMmodeLeafBase.luival`) is the Lean-only `WeakEvExecEff.luival`.  Both are FILE-QUALIFIED
   because their Rocq homes are SC files a later port may also translate.
4. `epure_wX_bits_at`: as `WeakLeafEffCommon.execEffWXBitsAt` (deviation 7 there): the premise is
   `wX (.Regno i.toNatInt) v = (writeReg r v' >>= fun _ => pure ())` over any register `r` with
   value `v'`.
5. `epure_returnM` restates `epureReturnm` (Lean has no `returnM`/`returnm` distinction, as
   `WeakLeafEffCommon.execEffReturnM`); kept for the name.
6. `epure_execute_UTYPE_LUI_gpr` / `epure_lui_tail` / `ewp_ev_lui_tail`: `tick_pc tt` ↦
   `tick_pc ()`; the post-state `let s1 := …` is kept as a `let`.

**Rocq → Lean name map.**  `epure` `epure`, `epure_returnm` `epureReturnm`, `epure_read_reg`
`epureReadReg`, `epure_write_reg` `epureWriteReg`, `epure_bind` `epureBind`, `epure_bind0`
`epureBind0`, `epure_mono` `epureMono`, `epure_exec_eff` `epureExecEff`, `exec_eff_epure`
`execEffEpure`, `epure_esilD` `epureEsilD`, `ewp_ev_epure` `ewpEvEpure`, `ewp_ev_exec_eff_pure`
`ewpEvExecEffPure`, `ewp_ev_exec_eff_cert` `ewpEvExecEffCert`, `epurew` `epurew`,
`epurew_exec_eff` `epurewExecEff`, `epure_epurew` `epureEpurew`, `Dgpr` `Dgpr`, `gpr_in_Dgpr`
`gprInDgpr`, `epure_returnM` `epureReturnM`, `epure_wX_bits_at` `epureWXBitsAt`,
`epure_wX_bits_gpr` `epureWXBitsGpr`, `epure_execute_UTYPE_LUI_gpr` `epureExecuteUTYPELUIGpr`,
`epure_tick_pc` `epureTickPc`, `epure_lui_tail` `epureLuiTail`, `ewp_ev_lui_tail`
`ewpEvLuiTail`.  Lean-only (deviation 3): `WeakEvExecEff.gprOfZ`, `WeakEvExecEff.luival`; the private
`iteMem` (an `if` of two members is a member; `gprInDgpr`'s case split).

**Dropped:** nothing (25 Rocq `Fixpoint`/`Definition`/`Lemma`/`Theorem`/`Corollary`s; Lean 25 +
2 Lean-only definitions + 1 private helper).

**Statements checked** (by hand, against Rocq): all; the changed ones are the deviations above.
-/
import Weak.WeakEff
import Weak.WeakEvLift
import Weak.ExecSC

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. `epure`: `execEff` with the world removed -/

/-- Arm for arm `WeakCert.execEff`, with the memory/device/barrier arms `none` and the two
register arms guarded by the footprint. -/
def epure {X : Type} (D : List Register) : SailM X → ExecSt → Option (X × ExecSt)
  | .pure x, s => some (x, s)
  | .impure (.error _) _, _ => none
  | .impure (.ok o) k, s =>
    match o, k with
    | .regRead r, k => if r ∈ D then epure D (k (s.regs r)) s else none
    | .regWrite r v, k => if r ∈ D then epure D (k PUnit.unit) (s.setReg r v) else none
    | .memRead .., _ => none
    | .memWrite .., _ => none
    | .barrier _, _ => none
    | .cacheOp _, k => epure D (k ()) s
    | .tlbi _, k => epure D (k ()) s
    | .translationStart _, k => epure D (k ()) s
    | .translationEnd _, k => epure D (k ()) s
    | .takeException _, k => epure D (k ()) s
    | .returnException _, k => epure D (k ()) s
    | .cycleCount, k => epure D (k ()) s
    | .getCycleCount, k => epure D (k (0 : Nat)) s
    | .message _, k => epure D (k ()) s
    | .instrAnnounce _ _, k => epure D (k ()) s
    | .branchAnnounce _ _, k => epure D (k ()) s
    | .choose _, _ => none
    | .readRam .., _ => none
    | .writeRam .., _ => none

theorem epureReturnm {X : Type} (D : List Register) (x : X) (t : ExecSt) :
    epure D (pure x : SailM X) t = some (x, t) := rfl

theorem epureReadReg (D : List Register) (r : Register) (t : ExecSt) :
    r ∈ D → epure D (readReg r) t = some (t.regs r, t) := by
  intro hD
  show (if r ∈ D then some (t.regs r, t) else none) = _
  rw [if_pos hD]

theorem epureWriteReg (D : List Register) (r : Register) (v : RegisterType r) (t : ExecSt) :
    r ∈ D → epure D (writeReg r v) t = some (PUnit.unit, t.setReg r v) := by
  intro hD
  show (if r ∈ D then some (PUnit.unit, t.setReg r v) else none) = _
  rw [if_pos hD]

theorem epureBind {X Y : Type} (D : List Register) (m : SailM X) (f : X → SailM Y) :
    ∀ t v t', epure D m t = some (v, t') → epure D (m >>= f) t = epure D (f v) t' := by
  induction m with
  | pure x =>
    intro t v t' h
    simp only [epure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | impure call k ih =>
    intro t v t' h
    cases call with
    | error e => simp [epure] at h
    | ok o =>
      show epure D (FreeM.impure (.ok o) (fun a => k a >>= f)) t = _
      cases o
      case regRead r =>
        by_cases hr : r ∈ D
        · simp only [epure, hr, ↓reduceIte] at h ⊢
          exact ih _ _ _ _ h
        · simp [epure, hr] at h
      case regWrite r w =>
        by_cases hr : r ∈ D
        · simp only [epure, hr, ↓reduceIte] at h ⊢
          exact ih _ _ _ _ h
        · simp [epure, hr] at h
      all_goals first
        | (simp [epure] at h; done)
        | (simp only [epure] at h ⊢; exact ih _ _ _ _ h)

theorem epureBind0 {Y : Type} (D : List Register) (m : SailM Unit) (n : SailM Y) (t : ExecSt)
    (u : Unit) (t' : ExecSt) :
    epure D m t = some (u, t') → epure D (m >>= fun _ => n) t = epure D n t' :=
  epureBind D m (fun _ => n) t u t'

/-- The footprint is MONOTONE: a bigger frame runs at least as far. -/
theorem epureMono {X : Type} (D D' : List Register) (m : SailM X) :
    D ⊆ D' → ∀ t r, epure D m t = some r → epure D' m t = some r := by
  intro hsub
  induction m with
  | pure x => intro t r h; exact h
  | impure call k ih =>
    intro t r h
    cases call with
    | error e => simp [epure] at h
    | ok o =>
      cases o
      case regRead q =>
        by_cases hr : q ∈ D
        · simp only [epure, hr, hsub hr, ↓reduceIte] at h ⊢
          exact ih _ _ _ h
        · simp [epure, hr] at h
      case regWrite q w =>
        by_cases hr : q ∈ D
        · simp only [epure, hr, hsub hr, ↓reduceIte] at h ⊢
          exact ih _ _ _ h
        · simp [epure, hr] at h
      all_goals first
        | (simp [epure] at h; done)
        | (simp only [epure] at h ⊢; exact ih _ _ _ h)

/-! ## 2. `epure` IS `execEff`, on the fragment where both are defined -/

theorem epureExecEff {X : Type} (D : List Register) (m : SailM X) :
    ∀ t x t', epure D m t = some (x, t') →
      execEff m t = some (x, t', []) ∧ t'.mem = t.mem ∧ t'.dev = t.dev := by
  induction m with
  | pure y =>
    intro t x t' h
    simp only [epure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩
  | impure call k ih =>
    intro t x t' h
    cases call with
    | error e => simp [epure] at h
    | ok o =>
      cases o
      case regRead r =>
        by_cases hr : r ∈ D
        · simp only [epure, hr, ↓reduceIte] at h
          exact ih _ _ _ _ h
        · simp [epure, hr] at h
      case regWrite r w =>
        by_cases hr : r ∈ D
        · simp only [epure, hr, ↓reduceIte] at h
          obtain ⟨h1, h2, h3⟩ := ih _ _ _ _ h
          exact ⟨h1, h2, h3⟩
        · simp [epure, hr] at h
      all_goals first
        | (simp [epure] at h; done)
        | (simp only [epure] at h; exact ih _ _ _ _ h)

/-- THE CONSUMPTION FORM: an `execEff` certificate and a non-stuck pure run agree. -/
theorem execEffEpure {X : Type} (D : List Register) (m : SailM X) (t : ExecSt) (x : X)
    (t' : ExecSt) (es : List Weff) (y : X) (t'' : ExecSt) :
    execEff m t = some (x, t', es) →
    epure D m t = some (y, t'') →
    x = y ∧ t' = t'' ∧ es = [] ∧ t'.mem = t.mem ∧ t'.dev = t.dev := by
  intro hee hep
  obtain ⟨hee', hmm, hmd⟩ := epureExecEff D m t y t'' hep
  rw [hee] at hee'
  simp only [Option.some.injEq, Prod.mk.injEq] at hee'
  obtain ⟨rfl, rfl, rfl⟩ := hee'
  exact ⟨rfl, rfl, rfl, hmm, hmd⟩

/-! ## 3. `epure` IS a silent run of the event language -/

theorem epureEsilD (D : List Register) (m : SailM Unit) :
    ∀ t y t', epure D m t = some (y, t') →
      rtc (esilD D) (m, t.regs) (FreeM.pure y, t'.regs) := by
  induction m with
  | pure y0 =>
    intro t y t' h
    simp only [epure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    cases y0; cases y
    exact rtc_refl _
  | impure call k ih =>
    intro t y t' h
    cases call with
    | error e => simp [epure] at h
    | ok o =>
      cases o
      case regRead r =>
        by_cases hr : r ∈ D
        · simp only [epure, hr, ↓reduceIte] at h
          exact rtc_l (y := (k (t.regs r), t.regs)) (by simp [esilD, esilNode, hr]) (ih _ _ _ _ h)
        · simp [epure, hr] at h
      case regWrite r w =>
        by_cases hr : r ∈ D
        · simp only [epure, hr, ↓reduceIte] at h
          exact rtc_l (y := (k PUnit.unit, t.regs.set r w)) (by simp [esilD, esilNode, hr])
            (ih _ _ _ _ h)
        · simp [epure, hr] at h
      all_goals first
        | (simp [epure] at h; done)
        | (simp only [epure] at h; exact rtc_l (by simp [esilD, esilNode]) (ih _ _ _ _ h))

/-! ## 4. THE DERIVED RULE (later-free; D3-2: owns `hartWs`) -/

section rule

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- The mid-monad form: the run ends at the monad's own `pure`. -/
theorem ewpEvEpure (gen : Nat) (c : CPU) (D : List Register) (m : SailM Unit) (t t' : ExecSt)
    (y : Unit) (ws : Wstate) :
    gen = 0 →
    epure D m t = some (y, t') →
    hartWs (GF := GF) c ws ∗ eregFrame (hlc := hlc) (GF := GF) c t.regs D ∗
      (∀ ws' : Wstate, ⌜wsDepmove ws ws'⌝ -∗ hartWs (GF := GF) c ws' -∗
          eregFrame (hlc := hlc) (GF := GF) c t'.regs D -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c (FreeM.pure y) none)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c m none) := by
  intro hgen hep
  exact ewpEvSilRtc gen c D (m, t.regs) (FreeM.pure y, t'.regs) ws hgen (epureEsilD D m t y t' hep)

/-- THE BOUNDARY FORM: the run lands back at the instruction boundary, no step, no later. -/
theorem ewpEvExecEffPure (gen : Nat) (c : CPU) (D : List Register) (m : SailM Unit)
    (t t' : ExecSt) (y : Unit) (ws : Wstate) :
    gen = 0 →
    epure D m t = some (y, t') →
    hartWs (GF := GF) c ws ∗ eregFrame (hlc := hlc) (GF := GF) c t.regs D ∗
      (∀ ws' : Wstate, ⌜wsDepmove ws ws'⌝ -∗ hartWs (GF := GF) c ws' -∗
          eregFrame (hlc := hlc) (GF := GF) c t'.regs D -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ELoop gen c)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c m none) := by
  intro hgen hep
  iintro ⟨Hws, Hrf, H⟩
  iapply ewpEvEpure gen c D m t t' y ws hgen hep
  iframe Hws Hrf
  iintro %ws' %hd Hws Hrf
  iapply ewpEvRet gen c y hgen
  iapply H $$ %ws' %hd Hws Hrf

/-- THE FORM STATED AGAINST AN `execEff` CERTIFICATE. -/
theorem ewpEvExecEffCert (gen : Nat) (c : CPU) (D : List Register) (m : SailM Unit)
    (t t' : ExecSt) (es : List Weff) (ws : Wstate) :
    gen = 0 →
    execEff m t = some ((), t', es) →
    (∃ y t'', epure D m t = some (y, t'')) →
    hartWs (GF := GF) c ws ∗ eregFrame (hlc := hlc) (GF := GF) c t.regs D ∗
      (∀ ws' : Wstate, ⌜wsDepmove ws ws'⌝ -∗ hartWs (GF := GF) c ws' -∗
          eregFrame (hlc := hlc) (GF := GF) c t'.regs D -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ELoop gen c)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c m none) := by
  intro hgen hee ⟨y, t'', hep⟩
  obtain ⟨_, ht, _, _, _⟩ := execEffEpure D m t () t' es y t'' hee hep
  subst ht
  exact ewpEvExecEffPure gen c D m t t' y ws hgen hep

end rule

/-! ## 5. S1b — THE OWNED WINDOW: the run side -/

/-- `epure` with the RAM arms re-enabled, emitting the `Weff` trace (device accesses stay
stuck). -/
def epurew {X : Type} (D : List Register) : SailM X → ExecSt → Option (X × ExecSt × List Weff)
  | .pure x, s => some (x, s, [])
  | .impure (.error _) _, _ => none
  | .impure (.ok o) k, s =>
    match o, k with
    | .regRead r, k => if r ∈ D then epurew D (k (s.regs r)) s else none
    | .regWrite r v, k => if r ∈ D then epurew D (k PUnit.unit) (s.setReg r v) else none
    | .memRead n _ req, k =>
      if mmioAcc req.pa n then none
      else
        match bmRead s.mem req.pa n with
        | some w =>
          Weff.cons (.WEread (classify req.access_kind) req.pa n) (epurew D (k (.Ok (w, none))) s)
        | none => none
    | .memWrite n _ req, k =>
      match req.value with
      | none => none
      | some w =>
        if mmioAcc req.pa n then none
        else
          Weff.cons (.WEwrite (classify req.access_kind) req.pa n w)
            (epurew D (k (.Ok (some true))) (s.setMem (bmWrite s.mem req.pa n w)))
    | .barrier b, k => Weff.cons (.WEbar b) (epurew D (k ()) s)
    | .cacheOp _, k => epurew D (k ()) s
    | .tlbi _, k => epurew D (k ()) s
    | .translationStart _, k => epurew D (k ()) s
    | .translationEnd _, k => epurew D (k ()) s
    | .takeException _, k => epurew D (k ()) s
    | .returnException _, k => epurew D (k ()) s
    | .cycleCount, k => epurew D (k ()) s
    | .getCycleCount, k => epurew D (k (0 : Nat)) s
    | .message _, k => epurew D (k ()) s
    | .instrAnnounce _ _, k => epurew D (k ()) s
    | .branchAnnounce _ _, k => epurew D (k ()) s
    | .choose _, _ => none
    | .readRam .., _ => none
    | .writeRam .., _ => none

/-- The windowed run IS the certificate run, trace included. -/
theorem epurewExecEff {X : Type} (D : List Register) (m : SailM X) :
    ∀ t x t' es, epurew D m t = some (x, t', es) →
      execEff m t = some (x, t', es) ∧ t'.dev = t.dev := by
  induction m with
  | pure y =>
    intro t x t' es h
    simp only [epurew, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | impure call k ih =>
    intro t x t' es h
    cases call with
    | error e => simp [epurew] at h
    | ok o =>
      cases o
      case regRead r =>
        by_cases hr : r ∈ D
        · simp only [epurew, hr, ↓reduceIte] at h
          exact ih _ _ _ _ _ h
        · simp [epurew, hr] at h
      case regWrite r w =>
        by_cases hr : r ∈ D
        · simp only [epurew, hr, ↓reduceIte] at h
          obtain ⟨h1, h2⟩ := ih _ _ _ _ _ h
          exact ⟨h1, h2⟩
        · simp [epurew, hr] at h
      case memRead n va req =>
        by_cases hm : mmioAcc req.pa n = true
        · simp [epurew, hm] at h
        · simp only [epurew, hm, Bool.false_eq_true, ↓reduceIte] at h
          simp only [execEff, hm, Bool.false_eq_true, ↓reduceIte]
          cases hrb : bmRead t.mem req.pa n with
          | none => simp [hrb] at h
          | some w =>
            simp only [hrb] at h ⊢
            obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
            obtain ⟨h1, h2⟩ := ih _ _ _ _ _ h0
            rw [h1]
            exact ⟨rfl, h2⟩
      case memWrite n va req =>
        cases hv : req.value with
        | none => simp [epurew, hv] at h
        | some w =>
          by_cases hm : mmioAcc req.pa n = true
          · simp [epurew, hv, hm] at h
          · simp only [epurew, hv, hm, Bool.false_eq_true, ↓reduceIte] at h
            simp only [execEff, hv, hm, Bool.false_eq_true, ↓reduceIte]
            obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
            obtain ⟨h1, h2⟩ := ih _ _ _ _ _ h0
            rw [h1]
            exact ⟨rfl, h2⟩
      case barrier b =>
        simp only [epurew] at h
        simp only [execEff]
        obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
        obtain ⟨h1, h2⟩ := ih _ _ _ _ _ h0
        rw [h1]
        exact ⟨rfl, h2⟩
      all_goals first
        | (simp [epurew] at h; done)
        | (simp only [epurew] at h; exact ih _ _ _ _ _ h)

/-- ... and the memory-free fragment of it is `epure`. -/
theorem epureEpurew {X : Type} (D : List Register) (m : SailM X) :
    ∀ t x t', epure D m t = some (x, t') → epurew D m t = some (x, t', []) := by
  induction m with
  | pure y =>
    intro t x t' h
    simp only [epure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | impure call k ih =>
    intro t x t' h
    cases call with
    | error e => simp [epure] at h
    | ok o =>
      cases o
      case regRead r =>
        by_cases hr : r ∈ D
        · simp only [epure, epurew, hr, ↓reduceIte] at h ⊢
          exact ih _ _ _ _ h
        · simp [epure, hr] at h
      case regWrite r w =>
        by_cases hr : r ∈ D
        · simp only [epure, epurew, hr, ↓reduceIte] at h ⊢
          exact ih _ _ _ _ h
        · simp [epure, hr] at h
      all_goals first
        | (simp [epure] at h; done)
        | (simp only [epure, epurew] at h ⊢; exact ih _ _ _ _ h)

/-! ## 6. THE MEASUREMENT — a real leaf's certificate, and the footprint -/

/-- Rocq `WpGpr.gpr_of_Z` (deviation 3). -/
def WeakEvExecEff.gprOfZ (n : Int) : Register :=
  if n = 1 then .x1 else if n = 2 then .x2
  else if n = 3 then .x3 else if n = 4 then .x4 else if n = 5 then .x5
  else if n = 6 then .x6 else if n = 7 then .x7 else if n = 8 then .x8
  else if n = 9 then .x9 else if n = 10 then .x10 else if n = 11 then .x11
  else if n = 12 then .x12 else if n = 13 then .x13 else if n = 14 then .x14
  else if n = 15 then .x15 else if n = 16 then .x16 else if n = 17 then .x17
  else if n = 18 then .x18 else if n = 19 then .x19 else if n = 20 then .x20
  else if n = 21 then .x21 else if n = 22 then .x22 else if n = 23 then .x23
  else if n = 24 then .x24 else if n = 25 then .x25 else if n = 26 then .x26
  else if n = 27 then .x27 else if n = 28 then .x28 else if n = 29 then .x29
  else if n = 30 then .x30 else .x31

/-- Rocq `WpMmodeLeafBase.luival` (deviation 3). -/
def WeakEvExecEff.luival (imm : BitVec 20) : BitVec 64 :=
  sign_extend (m := 64) (imm +++ 0x000#12)

/-- A concrete over-approximating footprint: the 31 architectural GPRs. -/
def Dgpr : List Register :=
  [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16,
   .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]

private theorem iteMem {p : Prop} [Decidable p] (a b : Register) (l : List Register) :
    a ∈ l → b ∈ l → (if p then a else b) ∈ l := by
  intro ha hb
  by_cases hp : p
  · rw [if_pos hp]; exact ha
  · rw [if_neg hp]; exact hb

theorem gprInDgpr (n : Int) : WeakEvExecEff.gprOfZ n ∈ Dgpr := by
  unfold WeakEvExecEff.gprOfZ
  repeat' apply iteMem
  all_goals simp [Dgpr]

theorem epureReturnM {X : Type} (D : List Register) (x : X) (s : ExecSt) :
    epure D (pure x : SailM X) s = some (x, s) := rfl

theorem epureWXBitsAt (D : List Register) (i : BitVec 5) (r : Register) (v' : RegisterType r)
    (s : ExecSt) (v : BitVec 64) :
    wX (.Regno (BitVec.toNatInt i) : regno) v = (writeReg r v' >>= fun _ => pure ()) →
    r ∈ D →
    epure D (wX_bits (.Regidx i : regidx) v) s = some ((), s.setReg r v') := by
  intro heq hD
  show epure D (wX (.Regno (BitVec.toNatInt i) : regno) v) s = _
  rw [heq, epureBind0 D _ _ s () _ (epureWriteReg D r v' s hD)]
  rfl

theorem epureWXBitsGpr (D : List Register) (i : BitVec 5) (v : BitVec 64) (s : ExecSt) :
    (∀ n : Int, WeakEvExecEff.gprOfZ n ∈ D) →
    epure D (wX_bits (.Regidx i) v) s = some ((), s.setGpr i v) := by
  intro HD
  rcases uxa_bv5_cases i with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact epureWXBitsAt D (1 : BitVec 5) .x1 v s v (by rfl) (HD 1)
  · exact epureWXBitsAt D (2 : BitVec 5) .x2 v s v (by rfl) (HD 2)
  · exact epureWXBitsAt D (3 : BitVec 5) .x3 v s v (by rfl) (HD 3)
  · exact epureWXBitsAt D (4 : BitVec 5) .x4 v s v (by rfl) (HD 4)
  · exact epureWXBitsAt D (5 : BitVec 5) .x5 v s v (by rfl) (HD 5)
  · exact epureWXBitsAt D (6 : BitVec 5) .x6 v s v (by rfl) (HD 6)
  · exact epureWXBitsAt D (7 : BitVec 5) .x7 v s v (by rfl) (HD 7)
  · exact epureWXBitsAt D (8 : BitVec 5) .x8 v s v (by rfl) (HD 8)
  · exact epureWXBitsAt D (9 : BitVec 5) .x9 v s v (by rfl) (HD 9)
  · exact epureWXBitsAt D (10 : BitVec 5) .x10 v s v (by rfl) (HD 10)
  · exact epureWXBitsAt D (11 : BitVec 5) .x11 v s v (by rfl) (HD 11)
  · exact epureWXBitsAt D (12 : BitVec 5) .x12 v s v (by rfl) (HD 12)
  · exact epureWXBitsAt D (13 : BitVec 5) .x13 v s v (by rfl) (HD 13)
  · exact epureWXBitsAt D (14 : BitVec 5) .x14 v s v (by rfl) (HD 14)
  · exact epureWXBitsAt D (15 : BitVec 5) .x15 v s v (by rfl) (HD 15)
  · exact epureWXBitsAt D (16 : BitVec 5) .x16 v s v (by rfl) (HD 16)
  · exact epureWXBitsAt D (17 : BitVec 5) .x17 v s v (by rfl) (HD 17)
  · exact epureWXBitsAt D (18 : BitVec 5) .x18 v s v (by rfl) (HD 18)
  · exact epureWXBitsAt D (19 : BitVec 5) .x19 v s v (by rfl) (HD 19)
  · exact epureWXBitsAt D (20 : BitVec 5) .x20 v s v (by rfl) (HD 20)
  · exact epureWXBitsAt D (21 : BitVec 5) .x21 v s v (by rfl) (HD 21)
  · exact epureWXBitsAt D (22 : BitVec 5) .x22 v s v (by rfl) (HD 22)
  · exact epureWXBitsAt D (23 : BitVec 5) .x23 v s v (by rfl) (HD 23)
  · exact epureWXBitsAt D (24 : BitVec 5) .x24 v s v (by rfl) (HD 24)
  · exact epureWXBitsAt D (25 : BitVec 5) .x25 v s v (by rfl) (HD 25)
  · exact epureWXBitsAt D (26 : BitVec 5) .x26 v s v (by rfl) (HD 26)
  · exact epureWXBitsAt D (27 : BitVec 5) .x27 v s v (by rfl) (HD 27)
  · exact epureWXBitsAt D (28 : BitVec 5) .x28 v s v (by rfl) (HD 28)
  · exact epureWXBitsAt D (29 : BitVec 5) .x29 v s v (by rfl) (HD 29)
  · exact epureWXBitsAt D (30 : BitVec 5) .x30 v s v (by rfl) (HD 30)
  · exact epureWXBitsAt D (31 : BitVec 5) .x31 v s v (by rfl) (HD 31)

/-- The LUI leaf's `execute` mirror, at an ARBITRARY `s`. -/
theorem epureExecuteUTYPELUIGpr (D : List Register) (rd : BitVec 5) (imm : BitVec 20)
    (s : ExecSt) :
    (∀ n : Int, WeakEvExecEff.gprOfZ n ∈ D) →
    epure D (execute (.UTYPE (imm, .Regidx rd, .LUI))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (WeakEvExecEff.luival imm)) := by
  intro HD
  show epure D (wX_bits (.Regidx rd) (WeakEvExecEff.luival imm) >>= fun _ => pure RETIRE_SUCCESS)
    s = _
  rw [epureBind0 D _ _ s () _ (epureWXBitsGpr D rd _ s HD)]
  rfl

/-- A piece of the REAL wrapper: `tick_pc`, register-only. -/
theorem epureTickPc (D : List Register) (s : ExecSt) :
    (Register.PC ∈ D) → (Register.nextPC ∈ D) →
    epure D (tick_pc ()) s = some ((), s.setReg .PC (s.regs .nextPC)) := by
  intro hPC hnPC
  show (if Register.nextPC ∈ D then
      (if Register.PC ∈ D then
        (if Register.PC ∈ D then some ((), s.setReg .PC (s.regs .nextPC)) else none)
        else none) else none) = _
  rw [if_pos hnPC, if_pos hPC, if_pos hPC]

theorem epureLuiTail (D : List Register) (rd : BitVec 5) (imm : BitVec 20) (s : ExecSt) :
    (∀ n : Int, WeakEvExecEff.gprOfZ n ∈ D) →
    (Register.PC ∈ D) → (Register.nextPC ∈ D) →
    epure D (execute (.UTYPE (imm, .Regidx rd, .LUI)) >>= fun _ => tick_pc ()) s =
      some ((),
        let s1 := s.setGpr rd (WeakEvExecEff.luival imm)
        s1.setReg .PC (s1.regs .nextPC)) := by
  intro HD hPC hnPC
  rw [epureBind D _ _ s _ _ (epureExecuteUTYPELUIGpr D rd imm s HD)]
  exact epureTickPc D _ hPC hnPC

section app

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- THE APPLICATION of the derived rule to a real leaf's certificate (`execute` then
`tick_pc`). -/
theorem ewpEvLuiTail (gen : Nat) (c : CPU) (D : List Register) (rd : BitVec 5)
    (imm : BitVec 20) (s : ExecSt) (ws : Wstate) :
    gen = 0 →
    (∀ n : Int, WeakEvExecEff.gprOfZ n ∈ D) →
    (Register.PC ∈ D) → (Register.nextPC ∈ D) →
    hartWs (GF := GF) c ws ∗ eregFrame (hlc := hlc) (GF := GF) c s.regs D ∗
      (∀ ws' : Wstate, ⌜wsDepmove ws ws'⌝ -∗ hartWs (GF := GF) c ws' -∗
          eregFrame (hlc := hlc) (GF := GF) c
            (let s1 := s.setGpr rd (WeakEvExecEff.luival imm)
             (s1.setReg .PC (s1.regs .nextPC))).regs D -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ELoop gen c)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤
      (ECycle gen c (execute (.UTYPE (imm, .Regidx rd, .LUI)) >>= fun _ => tick_pc ()) none) := by
  intro hgen HD hPC hnPC
  exact ewpEvExecEffPure gen c D _ s _ () ws hgen (epureLuiTail D rd imm s HD hPC hnPC)

end app

end Weak
