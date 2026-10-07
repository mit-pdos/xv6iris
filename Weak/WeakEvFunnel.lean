/-
Weak: **the event-tier instruction funnel** (M4-1, first slice): the split-footprint run predicate
`erun`, the dfrac-indexed register frame `eregFr` and its one-node rule / batched walk, the
one-fetch split, the derived rules `ewpEvOneFetch` / `ewpInstrPure`, the leaf-facing packaging,
and the LUI demonstration.

Rocq: `iris/WeakEvFunnel.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`WeakFunnel.wwpInstr` is the instruction-atomic tier's funnel (text + M-mode config + ONE
`execute` fact ↦ `WWP Loop`).  This file is its EVENT-TIER twin: text + register frame + ONE
whole-instruction RUN fact ↦ `EWP (ELoop gen c)`.
* §1 `erun Dr Dw m t`: `WeakEvExecEff.epurew` with the READ and WRITE footprints separated, plus
  its composition kit; a successful `erun` IS an `execEff` run (`erunExecEff`).
* §2 `eregFr c rs Dr q`: the register frame with the fraction a FUNCTION of the register, its
  one-node rule `ewpEvNode2` and batched walk `ewpEvWalk` (`WeakEvLift` §4's twins).
* §3 `erunSplitRead`: a run whose whole trace is ONE read is silent / read / silent.
* §4 `ewpEvOneFetch` (mid-cycle, ▷-free) and `ewpInstrPure` (instruction boundary, both ticks,
  exactly ONE ▷ — the one `ewpEloop` spends).
* §5 leaf-facing packaging: `winstrBytesEtextWord` (the fetch obligation from the resource every
  leaf already holds), frame adapters, `epureErun`.
* §6 the demonstration: the LUI tail through the kit, and the LUI leaf at the event tier.

FINDINGS (Rocq): (1) THE MIRROR GAP — `execEff` certificates do not transfer to `erun` (the
register arms are footprint-guarded and `erun` is stuck at a device access, where `execEff`
records nothing), so the `try_step` spine must be re-mirrored at `erun`; §1/§5 make that a
rename.  (2) `eregFrame` (all cells at `DFrac.own 1`) is too strong for a real footprint (the
config registers are held persistently / fractionally), hence the dfrac-indexed `eregFr`, of
which `eregFrame` is the `fun _ => own 1` instance (`eregFrFrame`).  (3) no invariant is held
across the instruction: the clock cells are hart-local and simply owned (`Dw`).

## Deviations from Rocq

1. NAMES / VOCABULARY: camelCase (map below); as `WeakEvLift` deviations 1/4 and `WeakEvExecEff`
   deviation 1: `gset register` ↦ `List Register` (`⊆` is `List.Subset`), `M X` ↦ `SailM X`,
   `mstate` ↦ `ExecSt`, `register_lookup r rs` ↦ `rs r`, `register_set` ↦ `RegFile.set`,
   `set_reg` ↦ `ExecSt.setReg`, `read_bytes` ↦ `bmRead`, `reg_pointsto_at` ↦ `regPointsTo`,
   `dfrac` ↦ `DFrac`, `P -∗ Q -∗ R` ↦ `P ∗ Q ⊢ R`, `EWP e @ ⊤` ↦ `ewpTriv ⊤ e`.  `erun`'s arms
   are lean-sail's `Outcome` constructors listed exhaustively (as `epurew`); the read arm's
   device test is Rocq's `dev_addr pa` (= `devAddr req.pa`, the event language's own test), its
   answer `.Ok (w, none)`, its trace element prepended by `Weff.cons`.
2. O2 — THE FETCH (`WeakEvLift` deviation 2).  `ewpEvOneFetch`/`ewpInstrPure` take
   `ak.akIfetch = true` (Rocq: `ak_coh ak = false ∧ ak_latest ak = false`); the fetch moves no
   view, so Rocq's `efetch_ws`/`efetch_ws_le` steps vanish from the proofs (statements unchanged:
   the continuation still gets some `ws' ⊒ ws`).  The demonstration's trace is
   `regonlyEs true pc = [.WEread WeakFetchEff.wakIfetch pc 4]` (`WeakLeafRegOnly`; Rocq
   `wak_plain`).
3. `erunSplitRead` also exists the request's VA width `va` (lean-sail requests are indexed by it,
   `WeakEvLift` deviation 5); `erunRead` takes it explicitly.
4. `eregFrPeel`: Rocq's `Dr ∖ {[r]}` ↦ `Dr.erase r` (a list footprint; the gset has no
   duplicates).
5. `ewpLuiLeafEv`: Rocq's `register_lookup (R_bitvector_64 (gpr_of_Z (uint rd))) (sregs s) =
   regval_into_reg (luival imm)` ↦ `s.gpr rd = WeakEvExecEff.luival imm` (`Weak/ExecSC.lean`
   GPR convention; the Rocq cell's type is not reducibly `BitVec 64` in Lean), `add_vec_int pc 4`
   ↦ `BitVec.addInt pc 4`.  `erunLuiTail`'s post-state is `WeakEvExecEff.epureLuiTail`'s.
6. `winstrEtextWord` keeps Rocq's unused argument `w`.  `winstrBytesEtextWord`'s word is typed
   `BitVec (8 * 4)` (defeq `BitVec 32`): with `BitVec 32`, `etextWord _ 4 w` elaborates with a
   silent `setWidth` (the width's numeral instance is still pending when `w` is checked).

Q7 (owner ruling, `notes/weak-port-q7-sfence.md` route (a), Lean-only): `epureErun` has an `instrAnnounce` case (`WeakEvExecEff.epure` stops at an sfence announce).

**Rocq → Lean name map.**  `erun` `erun`, `erun_returnm` `erunReturnm`, `erun_read_reg`
`erunReadReg`, `erun_write_reg` `erunWriteReg`, `erun_read` `erunRead`, `erun_bind` `erunBind`,
`erun_bind0` `erunBind0`, `erun_mono` `erunMono`, `erun_epurew` `erunEpurew`, `erun_exec_eff`
`erunExecEff`, `esil_node2` `esilNode2`, `esil2D` `esil2D`, `esil_node2_node` `esilNode2Node`,
`ereg_fr` `eregFr`, `ereg_fr_frame` `eregFrFrame`, `ereg_fr_ext` `eregFrExt`, `ereg_fr_agree`
`eregFrAgree`, `ereg_fr_update` `eregFrUpdate`, `esil_node2_agree` `esilNode2Agree`,
`ewp_ev_node2` `ewpEvNode2`, `ewp_ev_walk` `ewpEvWalk`, `erun_nil_walk` `erunNilWalk`,
`erun_split_read` `erunSplitRead`, `ewp_ev_one_fetch` `ewpEvOneFetch`, `ewp_instr_pure`
`ewpInstrPure`, `winstr_bytes_etext_word` `winstrBytesEtextWord`, `winstr_etext_word`
`winstrEtextWord`, `ereg_fr_peel` `eregFrPeel`, `ereg_fr_set_ne` `eregFrSetNe`, `epure_erun`
`epureErun`, `erun_lui_tail` `erunLuiTail`, `ewp_lui_leaf_ev` `ewpLuiLeafEv`.
Lean-only (file-qualified): `WeakEvFunnel.eregFrNotMem` (a full cell is not in a frame it is
separate from, for `eregFrUpdate`), `WeakEvFunnel.esilNode2Regs` (the register half Rocq inlines
in `ewp_ev_node2`), `WeakEvFunnel.winstrBytesFalse` (an error fetch result has no bytes).

**Dropped:** nothing (32 Rocq `Fixpoint`/`Definition`/`Lemma`/`Theorem`/`Corollary`s; Lean 32 +
3 Lean-only helpers).

**Statements checked** (by hand, against Rocq): all; the changed ones are the deviations above.
-/
import Weak.WeakEvExecEff
import Weak.WeakFunnel
import Weak.WeakLeafRegOnly

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. `erun`: `epurew` with the READ and WRITE footprints SEPARATED -/

def erun {X : Type} (Dr Dw : List Register) : SailM X → ExecSt → Option (X × ExecSt × List Weff)
  | .pure x, s => some (x, s, [])
  | .impure (.error _) _, _ => none
  | .impure (.ok o) k, s =>
    match o, k with
    | .regRead r, k => if r ∈ Dr then erun Dr Dw (k (s.regs r)) s else none
    | .regWrite r v, k => if r ∈ Dw then erun Dr Dw (k PUnit.unit) (s.setReg r v) else none
    | .memRead n _ req, k =>
      if devAddr req.pa then none
      else
        match bmRead s.mem req.pa n with
        | some w =>
          Weff.cons (.WEread (classify req.access_kind) req.pa n) (erun Dr Dw (k (.Ok (w, none))) s)
        | none => none
    | .memWrite .., _ => none
    | .barrier _, _ => none
    | .cacheOp _, k => erun Dr Dw (k ()) s
    | .tlbi _, k => erun Dr Dw (k ()) s
    | .translationStart _, k => erun Dr Dw (k ()) s
    | .translationEnd _, k => erun Dr Dw (k ()) s
    | .takeException _, k => erun Dr Dw (k ()) s
    | .returnException _, k => erun Dr Dw (k ()) s
    | .cycleCount, k => erun Dr Dw (k ()) s
    | .getCycleCount, k => erun Dr Dw (k (0 : Nat)) s
    | .message _, k => erun Dr Dw (k ()) s
    | .instrAnnounce _ _, k => erun Dr Dw (k ()) s
    | .branchAnnounce _ _, k => erun Dr Dw (k ()) s
    | .choose _, _ => none
    | .readRam .., _ => none
    | .writeRam .., _ => none

theorem erunReturnm {X : Type} (Dr Dw : List Register) (x : X) (t : ExecSt) :
    erun Dr Dw (pure x : SailM X) t = some (x, t, []) := rfl

theorem erunReadReg (Dr Dw : List Register) (r : Register) (t : ExecSt) :
    r ∈ Dr → erun Dr Dw (readReg r) t = some (t.regs r, t, []) := by
  intro hD
  show (if r ∈ Dr then some (t.regs r, t, []) else none) = _
  rw [if_pos hD]

theorem erunWriteReg (Dr Dw : List Register) (r : Register) (v : RegisterType r) (t : ExecSt) :
    r ∈ Dw → erun Dr Dw (writeReg r v) t = some (PUnit.unit, t.setReg r v, []) := by
  intro hD
  show (if r ∈ Dw then some (PUnit.unit, t.setReg r v, []) else none) = _
  rw [if_pos hD]

/-- The one memory arm: a RAM read, answered by the run's own byte map. -/
theorem erunRead {X : Type} (Dr Dw : List Register) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (K : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X)
    (t : ExecSt) (w : BitVec (8 * n)) (y : X) (t' : ExecSt) (es : List Weff) :
    devAddr req.pa = false →
    bmRead t.mem req.pa n = some w →
    erun Dr Dw (K (.Ok (w, none))) t = some (y, t', es) →
    erun Dr Dw (.impure (.ok (.memRead n va req)) K) t =
      some (y, t', .WEread (classify req.access_kind) req.pa n :: es) := by
  intro hd hrb hk
  simp [erun, hd, hrb, hk, Weff.cons]

theorem erunBind {X Y : Type} (Dr Dw : List Register) (m : SailM X) (f : X → SailM Y) :
    ∀ t v t' es, erun Dr Dw m t = some (v, t', es) →
      ∀ y t'' es', erun Dr Dw (f v) t' = some (y, t'', es') →
        erun Dr Dw (m >>= f) t = some (y, t'', es ++ es') := by
  induction m with
  | pure x =>
    intro t v t' es h y t'' es' hf
    simp only [erun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact hf
  | impure call k ih =>
    intro t v t' es h y t'' es' hf
    cases call with
    | error e => simp [erun] at h
    | ok o =>
      show erun Dr Dw (FreeM.impure (.ok o) (fun a => k a >>= f)) t = _
      cases o
      case regRead r =>
        by_cases hr : r ∈ Dr
        · simp only [erun, hr, ↓reduceIte] at h ⊢
          exact ih _ _ _ _ _ h _ _ _ hf
        · simp [erun, hr] at h
      case regWrite r w =>
        by_cases hr : r ∈ Dw
        · simp only [erun, hr, ↓reduceIte] at h ⊢
          exact ih _ _ _ _ _ h _ _ _ hf
        · simp [erun, hr] at h
      case memRead n va req =>
        by_cases hd : devAddr req.pa = true
        · simp [erun, hd] at h
        · cases hrb : bmRead t.mem req.pa n with
          | none => simp [erun, hd, hrb] at h
          | some w =>
            simp only [erun, hd, hrb, Bool.false_eq_true, ↓reduceIte] at h ⊢
            obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
            rw [ih _ _ _ _ _ h0 _ _ _ hf]
            rfl
      all_goals first
        | (simp [erun] at h; done)
        | (simp only [erun] at h ⊢; exact ih _ _ _ _ _ h _ _ _ hf)

theorem erunBind0 {Y : Type} (Dr Dw : List Register) (m : SailM Unit) (n : SailM Y) (t : ExecSt)
    (u : Unit) (t' : ExecSt) (es : List Weff) :
    erun Dr Dw m t = some (u, t', es) →
      ∀ y t'' es', erun Dr Dw n t' = some (y, t'', es') →
        erun Dr Dw (m >>= fun _ => n) t = some (y, t'', es ++ es') :=
  fun hm y t'' es' hn => erunBind Dr Dw m (fun _ => n) t u t' es hm y t'' es' hn

/-- MONOTONE in both footprints. -/
theorem erunMono {X : Type} (Dr Dr' Dw Dw' : List Register) (m : SailM X) :
    Dr ⊆ Dr' → Dw ⊆ Dw' → ∀ t r, erun Dr Dw m t = some r → erun Dr' Dw' m t = some r := by
  intro hsr hsw
  induction m with
  | pure x => intro t r h; exact h
  | impure call k ih =>
    intro t r h
    cases call with
    | error e => simp [erun] at h
    | ok o =>
      cases o
      case regRead q =>
        by_cases hr : q ∈ Dr
        · simp only [erun, hr, hsr hr, ↓reduceIte] at h ⊢
          exact ih _ _ _ h
        · simp [erun, hr] at h
      case regWrite q w =>
        by_cases hr : q ∈ Dw
        · simp only [erun, hr, hsw hr, ↓reduceIte] at h ⊢
          exact ih _ _ _ h
        · simp [erun, hr] at h
      case memRead n va req =>
        obtain ⟨x, t', es⟩ := r
        by_cases hd : devAddr req.pa = true
        · simp [erun, hd] at h
        · cases hrb : bmRead t.mem req.pa n with
          | none => simp [erun, hd, hrb] at h
          | some w =>
            simp only [erun, hd, hrb, Bool.false_eq_true, ↓reduceIte] at h ⊢
            obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
            rw [ih _ _ _ h0]
            rfl
      all_goals first
        | (simp [erun] at h; done)
        | (simp only [erun] at h ⊢; exact ih _ _ _ h)

/-- `erun` IS `epurew` at a common footprint, hence IS `execEff`. -/
theorem erunEpurew {X : Type} (Dr Dw : List Register) (m : SailM X) :
    Dw ⊆ Dr → ∀ t r, erun Dr Dw m t = some r → epurew Dr m t = some r := by
  intro hsub
  induction m with
  | pure x => intro t r h; exact h
  | impure call k ih =>
    intro t r h
    cases call with
    | error e => simp [erun] at h
    | ok o =>
      cases o
      case regRead q =>
        by_cases hr : q ∈ Dr
        · simp only [erun, epurew, hr, ↓reduceIte] at h ⊢
          exact ih _ _ _ h
        · simp [erun, hr] at h
      case regWrite q w =>
        by_cases hr : q ∈ Dw
        · simp only [erun, epurew, hr, hsub hr, ↓reduceIte] at h ⊢
          exact ih _ _ _ h
        · simp [erun, hr] at h
      case memRead n va req =>
        obtain ⟨x, t', es⟩ := r
        by_cases hd : devAddr req.pa = true
        · simp [erun, hd] at h
        · have hm : mmioAcc req.pa n = false := by simp [mmioAcc, hd]
          cases hrb : bmRead t.mem req.pa n with
          | none => simp [erun, hd, hrb] at h
          | some w =>
            simp only [erun, hd, hrb, Bool.false_eq_true, ↓reduceIte] at h
            simp only [epurew, hm, hrb, Bool.false_eq_true, ↓reduceIte]
            obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
            rw [ih _ _ _ h0]
            rfl
      all_goals first
        | (simp [erun] at h; done)
        | (simp only [erun, epurew] at h ⊢; exact ih _ _ _ h)

theorem erunExecEff {X : Type} (Dr Dw : List Register) (m : SailM X) (t : ExecSt) (y : X)
    (t' : ExecSt) (es : List Weff) :
    Dw ⊆ Dr → erun Dr Dw m t = some (y, t', es) →
      execEff m t = some (y, t', es) ∧ t'.dev = t.dev :=
  fun hsub hm => epurewExecEff Dr m t y t' es (erunEpurew Dr Dw m hsub t _ hm)

/-! ## 2. THE REGISTER FRAME, DFRAC-INDEXED, AND ITS ONE-NODE RULE -/

/-- `WeakEvLift.esilNode` with the WRITE guard moved to `Dw`. -/
def esilNode2 (Dr Dw : List Register) (rs : RegFile) : SailM Unit → Option (RegFile × SailM Unit)
  | .pure _ => none
  | .impure (.error _) _ => none
  | .impure (.ok o) k =>
    match o, k with
    | .regRead r, k => if r ∈ Dr then some (rs, k (rs r)) else none
    | .regWrite r v, k => if r ∈ Dw then some (rs.set r v, k PUnit.unit) else none
    | .instrAnnounce _ _, k => some (rs, k ())
    | .branchAnnounce _ _, k => some (rs, k ())
    | .cacheOp _, k => some (rs, k ())
    | .tlbi _, k => some (rs, k ())
    | .takeException _, k => some (rs, k ())
    | .returnException _, k => some (rs, k ())
    | .translationStart _, k => some (rs, k ())
    | .translationEnd _, k => some (rs, k ())
    | .cycleCount, k => some (rs, k ())
    | .message _, k => some (rs, k ())
    | .getCycleCount, k => some (rs, k (0 : Nat))
    | _, _ => none

def esil2D (Dr Dw : List Register) (x y : SailM Unit × RegFile) : Prop :=
  esilNode2 Dr Dw x.2 x.1 = some (y.2, y.1)

/-- At `Dw ⊆ Dr` the two node functions agree. -/
theorem esilNode2Node (Dr Dw : List Register) (rs : RegFile) (m : SailM Unit)
    (p : RegFile × SailM Unit) :
    Dw ⊆ Dr → esilNode2 Dr Dw rs m = some p → esilNode Dr rs m = some p := by
  intro hsub h
  match m, h with
  | .pure _, h => simp [esilNode2] at h
  | .impure (.error _) _, h => simp [esilNode2] at h
  | .impure (.ok o) k, h =>
    cases o with
    | regRead r =>
      simp only [esilNode2] at h
      simp only [esilNode]
      split at h
      · rename_i hr; rw [if_pos hr]; exact h
      · simp at h
    | regWrite r v =>
      simp only [esilNode2] at h
      simp only [esilNode]
      split at h
      · rename_i hr; rw [if_pos (hsub hr)]; exact h
      · simp at h
    | memRead => simp [esilNode2] at h
    | memWrite => simp [esilNode2] at h
    | readRam => simp [esilNode2] at h
    | writeRam => simp [esilNode2] at h
    | barrier => simp [esilNode2] at h
    | choose => simp [esilNode2] at h
    | _ =>
      simp only [esilNode2] at h
      simp only [esilNode]
      exact h

/-- `WeakEvLift.esilNodeAgree`'s twin. -/
theorem esilNode2Agree (Dr Dw : List Register) (rs1 rs2 : RegFile) (m m1 : SailM Unit)
    (rs1' : RegFile) :
    regAgreeOn Dr rs1 rs2 → esilNode2 Dr Dw rs1 m = some (rs1', m1) →
    ∃ rs2', esilNode2 Dr Dw rs2 m = some (rs2', m1) ∧ regAgreeOn Dr rs1' rs2' := by
  intro hag h
  match m, h with
  | .pure _, h => simp [esilNode2] at h
  | .impure (.error _) _, h => simp [esilNode2] at h
  | .impure (.ok o) k, h =>
    cases o with
    | regRead r =>
      simp only [esilNode2] at h ⊢
      split at h
      · rename_i hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rs2, ?_, hag⟩
        rw [if_pos hr, hag r hr]
      · simp at h
    | regWrite r v =>
      simp only [esilNode2] at h ⊢
      split at h
      · rename_i hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rs2.set r v, by rw [if_pos hr], fun r' hr' => ?_⟩
        by_cases he : r' = r
        · subst he; simp only [RegFile.set_same]
        · rw [RegFile.set_other _ _ _ _ he, RegFile.set_other _ _ _ _ he]; exact hag r' hr'
      · simp at h
    | memRead => simp [esilNode2] at h
    | memWrite => simp [esilNode2] at h
    | readRam => simp [esilNode2] at h
    | writeRam => simp [esilNode2] at h
    | barrier => simp [esilNode2] at h
    | choose => simp [esilNode2] at h
    | _ =>
      simp only [esilNode2, Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rs2, ⟨rfl, rfl⟩, hag⟩

section frame

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- THE FRAME: `WeakEvLift.eregFrame` with the fraction a FUNCTION of the register. -/
abbrev eregFr (c : CPU) (rs : RegFile) (Dr : List Register) (q : Register → DFrac) : IProp GF :=
  iprop([∗list] r ∈ Dr, regPointsTo (hlc := hlc) (GF := GF) c r (q r) (rs r))

theorem eregFrFrame (c : CPU) (rs : RegFile) (D : List Register) :
    eregFr (hlc := hlc) (GF := GF) c rs D (fun _ => DFrac.own 1) ⊣⊢
      eregFrame (hlc := hlc) (GF := GF) c rs D := .rfl

theorem eregFrExt (c : CPU) (rs rs' : RegFile) (D : List Register) (q : Register → DFrac) :
    regAgreeOn D rs rs' →
    eregFr (hlc := hlc) (GF := GF) c rs D q ⊣⊢ eregFr (hlc := hlc) (GF := GF) c rs' D q := by
  intro hag
  unfold eregFr
  rw [BigSepL.bigSepL_eq (Φ := fun _ r => regPointsTo (hlc := hlc) (GF := GF) c r (q r) (rs r))
    (Ψ := fun _ r => regPointsTo (hlc := hlc) (GF := GF) c r (q r) (rs' r))
    (fun {_ x} hk => congrArg (regPointsTo (hlc := hlc) (GF := GF) c x (q x))
      (hag x (List.mem_of_getElem? hk)))]
  exact .rfl

theorem eregFrAgree (c : CPU) (rs : RegFile) (D : List Register) (q : Register → DFrac)
    (rs0 : RegFile) :
    regInterp (hlc := hlc) (GF := GF) c rs0 ∗ eregFr (hlc := hlc) (GF := GF) c rs D q ⊢
      ⌜regAgreeOn D rs rs0⌝ := by
  unfold eregFr
  induction D with
  | nil => iintro -; ipureintro; intro r hr; simp at hr
  | cons r0 D ih =>
    iintro ⟨Hi, Hr0, Hrest⟩
    ihave ⟨%h0, Hi, Hr0⟩ := persistent_entails_right (reg_valid c rs0 r0 (q r0) (rs r0))
      $$ [Hi Hr0]
    · iframe Hi Hr0
    ihave %h1 := ih $$ [Hi Hrest]
    · iframe Hi Hrest
    ipureintro
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact h0.symm
    · exact h1 r hr

/-- A full cell is not in a frame it is separate from, when the frame would hold it in full
(Lean-only helper). -/
theorem WeakEvFunnel.eregFrNotMem (c : CPU) (rs : RegFile) (D : List Register)
    (q : Register → DFrac) (r : Register) (x : RegisterType r) :
    q r = DFrac.own 1 →
    regPointsTo (hlc := hlc) (GF := GF) c r (DFrac.own 1) x ∗
      eregFr (hlc := hlc) (GF := GF) c rs D q ⊢ ⌜r ∉ D⌝ := by
  intro hq
  unfold eregFr
  induction D with
  | nil => iintro -; ipureintro; simp
  | cons r0 D ih =>
    iintro ⟨Hx, Hr0, Hrest⟩
    by_cases he : r0 = r
    · subst he
      have hcv : regPointsTo (hlc := hlc) (GF := GF) c r0 (q r0) (rs r0) ⊢
          regPointsTo (hlc := hlc) (GF := GF) c r0 (DFrac.own 1) (rs r0) := by
        rw [hq]; try exact .rfl
      ihave Hr0 := hcv $$ Hr0
      ihave %hne := regPointsToNe (hlc := hlc) (GF := GF) c r0 r0 x (rs r0) $$ [Hx Hr0]
      · iframe Hx Hr0
      exact absurd rfl hne
    · ihave %hnm := ih $$ [Hx Hrest]
      · iframe Hx Hrest
      ipureintro
      simp only [List.mem_cons, not_or]
      exact ⟨fun h => he h.symm, hnm⟩

theorem eregFrUpdate (c : CPU) (rs : RegFile) (D : List Register) (q : Register → DFrac)
    (r : Register) (v : RegisterType r) (rs0 : RegFile) :
    r ∈ D → q r = DFrac.own 1 →
    regInterp (hlc := hlc) (GF := GF) c rs0 ∗ eregFr (hlc := hlc) (GF := GF) c rs D q ⊢
      |==> (regInterp (hlc := hlc) (GF := GF) c (rs0.set r v) ∗
        eregFr (hlc := hlc) (GF := GF) c (rs.set r v) D q) := by
  intro hrD hq
  induction D with
  | nil => simp at hrD
  | cons r0 D ih =>
    by_cases he : r0 = r
    · subst he
      have hcv : regPointsTo (hlc := hlc) (GF := GF) c r0 (q r0) (rs r0) ⊢
          regPointsTo (hlc := hlc) (GF := GF) c r0 (DFrac.own 1) (rs r0) := by
        rw [hq]; try exact .rfl
      iintro ⟨Hi, Hr, Hrest⟩
      ihave Hr := hcv $$ Hr
      ihave ⟨%hnm, Hr, Hrest⟩ := persistent_entails_right
        (WeakEvFunnel.eregFrNotMem (hlc := hlc) (GF := GF) c rs D q r0 (rs r0) hq) $$ [Hr Hrest]
      · iframe Hr Hrest
      imod reg_update c rs0 r0 (rs r0) v $$ [$Hi $Hr] with ⟨Hi, Hr⟩
      imodintro
      iframe Hi
      isplitl [Hr]
      · simp only [RegFile.set_same, hq]
        iexact Hr
      · iapply (eregFrExt (hlc := hlc) (GF := GF) c rs (rs.set r0 v) D q
          (fun r' hr' => (RegFile.set_other rs r0 r' v (fun h : r' = r0 => hnm (h ▸ hr'))).symm)).1
          $$ Hrest
    · have hD : r ∈ D := by
        rcases List.mem_cons.1 hrD with h | h
        · exact absurd h.symm he
        · exact h
      iintro ⟨Hi, Hr0, Hrest⟩
      imod (ih hD) $$ [$Hi $Hrest] with ⟨Hi, Hrest⟩
      imodintro
      iframe Hi
      isplitl [Hr0]
      · rw [RegFile.set_other _ _ _ _ he]
        iexact Hr0
      · iexact Hrest

/-- The register half of one node (Lean-only; Rocq inlines it in `ewp_ev_node2`). -/
theorem WeakEvFunnel.esilNode2Regs (c : CPU) (Dr Dw : List Register) (q : Register → DFrac)
    (rs rs0 rs1 rs2 : RegFile) (m m1 m2 : SailM Unit) :
    Dw ⊆ Dr → (∀ r, r ∈ Dw → q r = DFrac.own 1) →
    esilNode2 Dr Dw rs m = some (rs1, m1) → esilNode2 Dr Dw rs0 m = some (rs2, m2) →
    regInterp (hlc := hlc) (GF := GF) c rs0 ∗ eregFr (hlc := hlc) (GF := GF) c rs Dr q ⊢
      |==> (regInterp (hlc := hlc) (GF := GF) c rs2 ∗
        eregFr (hlc := hlc) (GF := GF) c rs1 Dr q) := by
  intro hsub hq h1 h2
  match m, h1, h2 with
  | .pure _, h1, _ => simp [esilNode2] at h1
  | .impure (.error _) _, h1, _ => simp [esilNode2] at h1
  | .impure (.ok o) k, h1, h2 =>
    cases o with
    | regWrite r v =>
      simp only [esilNode2] at h1 h2
      split at h1
      · rename_i hr
        rw [if_pos hr] at h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h1 h2
        obtain ⟨rfl, -⟩ := h1
        obtain ⟨rfl, -⟩ := h2
        exact eregFrUpdate c rs Dr q r v rs0 (hsub hr) (hq r hr)
      · simp at h1
    | regRead r =>
      simp only [esilNode2] at h1 h2
      split at h1
      · rename_i hr
        rw [if_pos hr] at h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h1 h2
        obtain ⟨rfl, -⟩ := h1
        obtain ⟨rfl, -⟩ := h2
        exact BIUpdate.intro
      · simp at h1
    | memRead => simp [esilNode2] at h1
    | memWrite => simp [esilNode2] at h1
    | readRam => simp [esilNode2] at h1
    | writeRam => simp [esilNode2] at h1
    | barrier => simp [esilNode2] at h1
    | choose => simp [esilNode2] at h1
    | _ =>
      simp only [esilNode2, Option.some.injEq, Prod.mk.injEq] at h1 h2
      obtain ⟨rfl, -⟩ := h1
      obtain ⟨rfl, -⟩ := h2
      exact BIUpdate.intro

/-- ONE node, at the split footprint (D3-2: owns the hart's view, hands back `wsDepmove`). -/
theorem ewpEvNode2 (gen : Nat) (c : CPU) (Dr Dw : List Register) (q : Register → DFrac)
    (rs : RegFile) (m m1 : SailM Unit) (rs1 : RegFile) (ws : Wstate) :
    gen = 0 → Dw ⊆ Dr → (∀ r, r ∈ Dw → q r = DFrac.own 1) →
    esilNode2 Dr Dw rs m = some (rs1, m1) →
    hartWs (GF := GF) c ws ∗ eregFr (hlc := hlc) (GF := GF) c rs Dr q ∗
      ▷ (∀ ws' : Wstate, ⌜wsDepmove ws ws'⌝ -∗ hartWs (GF := GF) c ws' -∗
          eregFr (hlc := hlc) (GF := GF) c rs1 Dr q -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c m1 none)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c m none) := by
  intro hgen hsub hq hnode
  iintro ⟨Hws, Hrf, H⟩
  iapply ewpEcycle gen c m none hgen
  iintro %σ Hσ
  icases weakStateInterpRmw σ c $$ Hσ with ⟨%Hbnd, %Hnv, %Hwf, Hri, Hlog, Hlat, Hwsa, Hcl⟩
  ihave ⟨%hag, Hri, Hrf⟩ := persistent_entails_right
    (eregFrAgree (hlc := hlc) (GF := GF) c rs Dr q (σ.wgregs c)) $$ [Hri Hrf]
  · iframe Hri Hrf
  ihave ⟨%hws, Hwsa, Hws⟩ := persistent_entails_right (hartWsAgree c (σ.wgws c) ws) $$ [Hwsa Hws]
  · iframe Hwsa Hws
  subst hws
  obtain ⟨rs2, hnode2, -⟩ := esilNode2Agree Dr Dw rs (σ.wgregs c) m m1 rs1 hag hnode
  have hnode2' := esilNode2Node Dr Dw (σ.wgregs c) m (rs2, m1) hsub hnode2
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  isplitr
  · ipureintro
    obtain ⟨σ1, hc, -⟩ := esilNodeEcycle gen σ c Dr m m1 rs2 hnode2'
    exact ⟨_, _, hc⟩
  inext
  iintro %e' %σ' %hcy
  imod Hmask
  obtain ⟨rfl, hσ'⟩ := esilNodeEcycleInv gen σ c Dr rs2 m1 m e' σ' hnode2' hcy
  have hdm := esilSigmaDepmove σ c rs2 σ' hσ'
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := esilSigmaShape σ c rs2 σ' hσ'
  have hEq := weakStateInterpCongr (hlc := hlc) (GF := GF)
    (ewgRegwslog σ c rs2 (σ'.wgws c) σ.wglog) σ' e1 e4.symm e3.symm e2 e5.symm e6.symm e7.symm
  imod WeakEvFunnel.esilNode2Regs c Dr Dw q rs (σ.wgregs c) rs1 rs2 m m1 m1 hsub hq hnode hnode2
    $$ [$Hri $Hrf] with ⟨Hri, Hrf⟩
  imod hartWsUpdate c (σ.wgws c) (σ.wgws c) (σ'.wgws c) $$ [$Hwsa $Hws] with ⟨Hwsa, Hws⟩
  imodintro
  isplitl [Hcl Hri Hlog Hlat Hwsa]
  · rw [← hEq]
    iapply Hcl $$ %rs2 %(σ'.wgws c) %σ.wglog %(Nat.le_refl _)
      %(esilSigmaBounded σ c rs2 σ' _ hσ' (Hbnd c))
      %(nvHartOfCohEq _ c _ _ (noViolationHart _ _ c Hnv) (fun a => wsDepmoveCoh _ _ a hdm))
      %(appNilOwn σ.wglog c) %Hwf Hri Hlog Hlat Hwsa
  · iapply H $$ %(σ'.wgws c) %hdm Hws Hrf

/-- THE BATCHED WALK — the induction, once. -/
theorem ewpEvWalk (gen : Nat) (c : CPU) (Dr Dw : List Register) (q : Register → DFrac)
    (x y : SailM Unit × RegFile) (ws : Wstate) :
    gen = 0 → Dw ⊆ Dr → (∀ r, r ∈ Dw → q r = DFrac.own 1) →
    rtc (esil2D Dr Dw) x y →
    hartWs (GF := GF) c ws ∗ eregFr (hlc := hlc) (GF := GF) c x.2 Dr q ∗
      (∀ ws' : Wstate, ⌜wsDepmove ws ws'⌝ -∗ hartWs (GF := GF) c ws' -∗
          eregFr (hlc := hlc) (GF := GF) c y.2 Dr q -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c y.1 none)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c x.1 none) := by
  intro hgen hsub hq hrtc
  revert ws
  refine rtc_ind_l (R := esil2D Dr Dw)
    (fun x => ∀ ws : Wstate,
      hartWs (GF := GF) c ws ∗ eregFr (hlc := hlc) (GF := GF) c x.2 Dr q ∗
        (∀ ws' : Wstate, ⌜wsDepmove ws ws'⌝ -∗ hartWs (GF := GF) c ws' -∗
          eregFr (hlc := hlc) (GF := GF) c y.2 Dr q -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c y.1 none)) ⊢
      ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c x.1 none)) y ?_ ?_ x hrtc
  · intro ws
    iintro ⟨Hws, Hrf, H⟩
    iapply H $$ %ws %(wsDepmoveRefl ws) Hws Hrf
  · intro x0 y0 hxy _ ih ws
    iintro ⟨Hws, Hrf, H⟩
    iapply ewpEvNode2 gen c Dr Dw q x0.2 x0.1 y0.1 y0.2 ws hgen hsub hq hxy
    iframe Hws Hrf
    inext
    iintro %ws1 %hd1 Hws Hrf
    iapply ih ws1
    iframe Hws Hrf
    iintro %ws2 %hd2 Hws Hrf
    iapply H $$ %ws2 %(wsDepmoveTrans hd1 hd2) Hws Hrf

end frame

/-! ## 3. THE SPLIT: a one-fetch run IS silent / read / silent -/

/-- The trace-free fragment: a silent stretch, the byte map untouched. -/
theorem erunNilWalk (Dr Dw : List Register) (m : SailM Unit) :
    ∀ t y t', erun Dr Dw m t = some (y, t', []) →
      rtc (esil2D Dr Dw) (m, t.regs) (FreeM.pure y, t'.regs) ∧
      t'.mem = t.mem ∧ t'.dev = t.dev := by
  induction m with
  | pure y0 =>
    intro t y t' h
    simp only [erun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    cases y0; cases y
    exact ⟨rtc_refl _, rfl, rfl⟩
  | impure call k ih =>
    intro t y t' h
    cases call with
    | error e => simp [erun] at h
    | ok o =>
      cases o
      case regRead r =>
        by_cases hr : r ∈ Dr
        · simp only [erun, hr, ↓reduceIte] at h
          obtain ⟨h1, h2, h3⟩ := ih _ _ _ _ h
          exact ⟨rtc_l (y := (k (t.regs r), t.regs)) (by simp [esil2D, esilNode2, hr]) h1, h2, h3⟩
        · simp [erun, hr] at h
      case regWrite r w =>
        by_cases hr : r ∈ Dw
        · simp only [erun, hr, ↓reduceIte] at h
          obtain ⟨h1, h2, h3⟩ := ih _ _ _ _ h
          exact ⟨rtc_l (y := (k PUnit.unit, t.regs.set r w)) (by simp [esil2D, esilNode2, hr]) h1,
            h2, h3⟩
        · simp [erun, hr] at h
      case memRead n va req =>
        exfalso
        by_cases hd : devAddr req.pa = true
        · simp [erun, hd] at h
        · cases hrb : bmRead t.mem req.pa n with
          | none => simp [erun, hd, hrb] at h
          | some w =>
            simp only [erun, hd, hrb, Bool.false_eq_true, ↓reduceIte] at h
            obtain ⟨es0, -, he⟩ := Weff.consEqSome.1 h
            simp at he
      all_goals first
        | (simp [erun] at h; done)
        | (simp only [erun] at h
           obtain ⟨h1, h2, h3⟩ := ih _ _ _ _ h
           exact ⟨rtc_l (by simp [esil2D, esilNode2]) h1, h2, h3⟩)

/-- THE SPLIT.  A run whose whole trace is ONE read decomposes into a silent stretch, the read
NODE, and a silent stretch to the monad's `pure` (deviation 3: the VA width is existential). -/
theorem erunSplitRead (Dr Dw : List Register) (m : SailM Unit) (t : ExecSt) (y : Unit)
    (t' : ExecSt) (ak : AkInfo) (pa : PAddr) (n : Nat) :
    erun Dr Dw m t = some (y, t', [.WEread ak pa n]) →
    ∃ (va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (K : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit)
      (t1 : ExecSt) (w : BitVec (8 * n)),
      rtc (esil2D Dr Dw) (m, t.regs) (.impure (.ok (.memRead n va req)) K, t1.regs) ∧
      t1.mem = t.mem ∧ t1.dev = t.dev ∧
      req.pa = pa ∧
      classify req.access_kind = ak ∧
      devAddr pa = false ∧
      bmRead t.mem pa n = some w ∧
      rtc (esil2D Dr Dw) (K (.Ok (w, none)), t1.regs) (FreeM.pure y, t'.regs) ∧
      t'.mem = t.mem ∧ t'.dev = t.dev := by
  induction m generalizing t with
  | pure y0 => intro h; simp [erun] at h
  | impure call k ih =>
    intro h
    cases call with
    | error e => simp [erun] at h
    | ok o =>
      cases o
      case memRead n' va req =>
        by_cases hd : devAddr req.pa = true
        · simp [erun, hd] at h
        · cases hrb : bmRead t.mem req.pa n' with
          | none => simp [erun, hd, hrb] at h
          | some w0 =>
            simp only [erun, hd, hrb, Bool.false_eq_true, ↓reduceIte] at h
            obtain ⟨es0, h0, he⟩ := Weff.consEqSome.1 h
            simp only [List.cons.injEq, Weff.WEread.injEq] at he
            obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := he
            obtain ⟨hpost, hmm, hmd⟩ := erunNilWalk Dr Dw _ t y t' h0
            exact ⟨va, req, k, t, w0, rtc_refl _, rfl, rfl, rfl, rfl, by simpa using hd, hrb,
              hpost, hmm, hmd⟩
      case regRead r =>
        by_cases hr : r ∈ Dr
        · simp only [erun, hr, ↓reduceIte] at h
          obtain ⟨va, req, K, t1, w, hpre, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ih _ _ h
          exact ⟨va, req, K, t1, w,
            rtc_l (y := (k (t.regs r), t.regs)) (by simp [esil2D, esilNode2, hr]) hpre,
            h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
        · simp [erun, hr] at h
      case regWrite r v =>
        by_cases hr : r ∈ Dw
        · simp only [erun, hr, ↓reduceIte] at h
          obtain ⟨va, req, K, t1, w, hpre, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ih _ _ h
          exact ⟨va, req, K, t1, w,
            rtc_l (y := (k PUnit.unit, t.regs.set r v)) (by simp [esil2D, esilNode2, hr]) hpre,
            h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
        · simp [erun, hr] at h
      all_goals first
        | (simp [erun] at h; done)
        | (simp only [erun] at h
           obtain ⟨va, req, K, t1, w, hpre, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ih _ _ h
           exact ⟨va, req, K, t1, w, rtc_l (by simp [esil2D, esilNode2]) hpre,
             h1, h2, h3, h4, h5, h6, h7, h8, h9⟩)

/-! ## 4. THE DERIVED RULE: ONE INSTRUCTION, ONE FETCH, NO OTHER EVENT -/

section rule

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- The mid-cycle form (▷-free; deviation 2: the fetch is an i-cache read). -/
theorem ewpEvOneFetch (gen : Nat) (c : CPU) (Dr Dw : List Register) (q : Register → DFrac)
    (m : SailM Unit) (t t' : ExecSt) (y : Unit) (ak : AkInfo) (pa : PAddr) (n : Nat)
    (w : BitVec (8 * n)) (ws : Wstate) :
    gen = 0 → Dw ⊆ Dr → (∀ r, r ∈ Dw → q r = DFrac.own 1) →
    erun Dr Dw m t = some (y, t', [.WEread ak pa n]) →
    bmRead t.mem pa n = some w →
    ak.akIfetch = true →
    etextWord (GF := GF) (paZ pa) n w ∗ eregFr (hlc := hlc) (GF := GF) c t.regs Dr q ∗
      hartWs (GF := GF) c ws ∗
      (∀ ws' : Wstate, ⌜wsLe ws ws'⌝ -∗
        eregFr (hlc := hlc) (GF := GF) c t'.regs Dr q -∗ hartWs (GF := GF) c ws' -∗
        ewpTriv (hlc := hlc) (GF := GF) ⊤ (ELoop gen c)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle gen c m none) := by
  intro hgen hsub hq hrun hw hif
  obtain ⟨va, req, K, t1, w0, hpre, hm1, hd1, hpa, hak, hdev, hrd, hpost, hmm, hmd⟩ :=
    erunSplitRead Dr Dw m t y t' ak pa n hrun
  have hww : w0 = w := by
    rw [hw] at hrd
    exact (Option.some.inj hrd).symm
  subst hww
  subst hpa
  subst hak
  iintro ⟨#Ht, Hrf, Hws, H⟩
  -- the silent stretch before the fetch
  iapply ewpEvWalk gen c Dr Dw q (m, t.regs) (.impure (.ok (.memRead n va req)) K, t1.regs) ws
    hgen hsub hq hpre
  iframe Hws Hrf
  iintro %ws1 %hd1' Hws Hrf
  -- THE FETCH
  iapply ewpEvFetch gen c n va req K w0 ws1 hgen hdev hif
  iframe Ht Hws
  inext
  iintro Hws
  -- the silent stretch after it, and the boundary
  iapply ewpEvWalk gen c Dr Dw q (K (.Ok (w0, none)), t1.regs) (FreeM.pure y, t'.regs) ws1
    hgen hsub hq hpost
  iframe Hws Hrf
  iintro %ws2 %hd2' Hws Hrf
  iapply ewpEvRet gen c y hgen
  iapply H $$ %ws2 %(wsLeTrans (wsDepmoveLe _ _ hd1') (wsDepmoveLe _ _ hd2')) Hrf Hws

/-- THE FUNNEL TWIN, at the instruction boundary; the certificate is owed for BOTH ticks. -/
theorem ewpInstrPure (gen : Nat) (c : CPU) (Dr Dw : List Register) (q : Register → DFrac)
    (t : ExecSt) (tp : Bool → ExecSt) (ak : AkInfo) (pa : PAddr) (n : Nat) (w : BitVec (8 * n))
    (ws : Wstate) :
    gen = 0 → Dw ⊆ Dr → (∀ r, r ∈ Dw → q r = DFrac.own 1) →
    (∀ tick : Bool, erun Dr Dw (riscvStep tick) t = some ((), tp tick, [.WEread ak pa n])) →
    bmRead t.mem pa n = some w →
    ak.akIfetch = true →
    etextWord (GF := GF) (paZ pa) n w ∗ eregFr (hlc := hlc) (GF := GF) c t.regs Dr q ∗
      hartWs (GF := GF) c ws ∗
      ▷ (∀ (tick : Bool) (ws' : Wstate), ⌜wsLe ws ws'⌝ -∗
          eregFr (hlc := hlc) (GF := GF) c (tp tick).regs Dr q -∗ hartWs (GF := GF) c ws' -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ELoop gen c)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ELoop gen c) := by
  intro hgen hsub hq hcert hw hif
  iintro ⟨#Ht, Hrf, Hws, H⟩
  iapply ewpEloop gen c ws hgen
  isplitl [Hws]
  · iexact Hws
  inext
  iintro %tick Hws
  iapply ewpEvOneFetch gen c Dr Dw q (riscvStep tick) t (tp tick) () ak pa n w (instrPost ws)
    hgen hsub hq (hcert tick) hw hif
  iframe Ht Hrf Hws
  iintro %ws' %hle Hrf Hws
  iapply H $$ %tick %ws' %(wsLeTrans (instrPostLe ws) hle) Hrf Hws

end rule

/-! ## 5. THE LEAF-FACING PACKAGING -/

section pack

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- THE TEXT: `WeakFunnel.winstrBytes` IS `etextWord` at the fetch window. -/
theorem winstrBytesEtextWord (pc : BitVec 64) (w : BitVec (8 * 4)) :
    winstrBytes (GF := GF) pc (.F_Base w) ⊢ etextWord (GF := GF) (paZ pc) 4 w := by
  unfold etextWord
  refine (show winstrBytes (GF := GF) pc (.F_Base w) ⊢
      iprop(□ winstrBytes (GF := GF) pc (.F_Base w)) by
    iintro #H; imodintro; iexact H).trans
    (BigSepL.bigSepL_intro fun i j hj => intuitionistically_elim.trans ?_)
  have hmem := List.mem_of_getElem? hj
  rw [List.mem_range'_1] at hmem
  have hj4 : j < 4 := by omega
  show winstrBytes (GF := GF) pc (.F_Base w) ⊢ etext (GF := GF) (WeakInterp.accAddr pc j) (nthByte w j)
  unfold winstrBytes
  iintro ⟨%hal, %hacc, %hram, %w0, %hok, H0, H1, H2, H3⟩
  obtain ⟨rfl, -⟩ := hok
  rw [← accWfByte pc 4 j hacc hj4]
  unfold etext
  obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  · iexact H0
  · iexact H1
  · iexact H2
  · iexact H3

/-- An error fetch result carries no bytes (Lean-only helper). -/
theorem WeakEvFunnel.winstrBytesFalse (pc : BitVec 64) (r : FetchResult) (Q : IProp GF) :
    (∀ w0 : BitVec 32, ¬ fetchWordOk r w0) → winstrBytes (GF := GF) pc r ⊢ Q := by
  intro h
  unfold winstrBytes
  iintro ⟨-, -, -, %w0, %hok, -⟩
  exact (h w0 hok).elim

/-- The `winstr` wrapper, for a caller that holds the funnel's own resource (the `F_Base` arm). -/
theorem winstrEtextWord (pc : BitVec 64) (i : instruction) (_w : BitVec 32) :
    winstr (GF := GF) pc false i ⊢ ∃ w' : BitVec 32, etextWord (GF := GF) (paZ pc) 4 w' := by
  unfold winstr
  iintro ⟨-, %r, %hrvc, Hb, -⟩
  cases r with
  | F_Base w' =>
    iexists w'
    iapply winstrBytesEtextWord (GF := GF) pc w'
    iexact Hb
  | F_RVC h => simp [fetchIsRvc] at hrvc
  | F_Ext_Error e =>
    iapply WeakEvFunnel.winstrBytesFalse (GF := GF) pc (.F_Ext_Error e) _
      (fun w0 h => by simp [fetchWordOk] at h)
    iexact Hb
  | F_Error e =>
    iapply WeakEvFunnel.winstrBytesFalse (GF := GF) pc (.F_Error e) _
      (fun w0 h => by simp [fetchWordOk] at h)
    iexact Hb

/-- THE REGISTER ADAPTER: a named cell peels out of the frame and back in (deviation 4). -/
theorem eregFrPeel (c : CPU) (rs : RegFile) (Dr : List Register) (q : Register → DFrac)
    (r : Register) :
    r ∈ Dr →
    (eregFr (hlc := hlc) (GF := GF) c rs Dr q ⊣⊢
      regPointsTo (hlc := hlc) (GF := GF) c r (q r) (rs r) ∗
        eregFr (hlc := hlc) (GF := GF) c rs (Dr.erase r) q) := by
  intro hr
  exact BiEntails.trans (BigSepL.bigSepL_perm (List.perm_cons_erase hr)) BigSepL.bigSepL_cons

/-- ... and the frame is INSENSITIVE to registers outside it. -/
theorem eregFrSetNe (c : CPU) (rs : RegFile) (Dr : List Register) (q : Register → DFrac)
    (r : Register) (v : RegisterType r) :
    r ∉ Dr →
    (eregFr (hlc := hlc) (GF := GF) c (rs.set r v) Dr q ⊣⊢
      eregFr (hlc := hlc) (GF := GF) c rs Dr q) := by
  intro hr
  apply eregFrExt
  intro r' hr'
  have hne : r' ≠ r := fun h => hr (h ▸ hr')
  exact RegFile.set_other rs r r' v hne

end pack

/-- THE CERTIFICATE BRIDGE: `WeakEvExecEff`'s memory-free `epure` IS an `erun` with an empty
trace. -/
theorem epureErun {X : Type} (D : List Register) (m : SailM X) :
    ∀ t y t', epure D m t = some (y, t') → erun D D m t = some (y, t', []) := by
  induction m with
  | pure y0 =>
    intro t y t' h
    simp only [epure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | impure call k ih =>
    intro t y t' h
    cases call with
    | error e => simp [epure] at h
    | ok o =>
      cases o
      case regRead r =>
        by_cases hr : r ∈ D
        · simp only [epure, erun, hr, ↓reduceIte] at h ⊢
          exact ih _ _ _ _ h
        · simp [epure, hr] at h
      case regWrite r w =>
        by_cases hr : r ∈ D
        · simp only [epure, erun, hr, ↓reduceIte] at h ⊢
          exact ih _ _ _ _ h
        · simp [epure, hr] at h
      case instrAnnounce n w =>
        cases hs : sfAnnB n w
        · simp only [epure, erun, hs, Bool.false_eq_true, ↓reduceIte] at h ⊢
          exact ih _ _ _ _ h
        · simp [epure, hs] at h
      all_goals first
        | (simp [epure] at h; done)
        | (simp only [epure, erun] at h ⊢; exact ih _ _ _ _ h)

/-! ## 6. THE DEMONSTRATION — a real boot-cone leaf, at the event tier -/

/-- 6a. The LUI leaf's post-fetch tail is an `erun` with an empty trace, by ONE `epureErun`. -/
theorem erunLuiTail (D : List Register) (rd : BitVec 5) (imm : BitVec 20) (s : ExecSt) :
    (∀ n : Int, WeakEvExecEff.gprOfZ n ∈ D) →
    (Register.PC ∈ D) → (Register.nextPC ∈ D) →
    erun D D (execute (.UTYPE (imm, .Regidx rd, .LUI)) >>= fun _ => tick_pc ()) s =
      some ((),
        (let s1 := s.setGpr rd (WeakEvExecEff.luival imm)
         s1.setReg .PC (s1.regs .nextPC)), []) := by
  intro HD hPC hnPC
  exact epureErun D _ s () _ (epureLuiTail D rd imm s HD hPC hnPC)

section demo

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- 6b. THE LEAF: `WeakLeafUtypeShift.wwp_lui_leaf` at the event tier (deviation 5). -/
theorem ewpLuiLeafEv (gen : Nat) (c : CPU) (Dr Dw : List Register) (q : Register → DFrac)
    (pc : BitVec 64) (w : BitVec 32) (rd : BitVec 5) (imm : BitVec 20)
    (t : ExecSt) (tp : Bool → ExecSt) (ws : Wstate) :
    gen = 0 → Dw ⊆ Dr → (∀ r, r ∈ Dw → q r = DFrac.own 1) →
    bmRead t.mem pc 4 = some w →
    (∀ tick : Bool, erun Dr Dw (riscvStep tick) t = some ((), tp tick, regonlyEs true pc)) →
    (∀ tick : Bool, (tp tick).gpr rd = WeakEvExecEff.luival imm) →
    (∀ tick : Bool, (tp tick).regs .PC = BitVec.addInt pc 4) →
    winstrBytes (GF := GF) pc (.F_Base w) ∗ eregFr (hlc := hlc) (GF := GF) c t.regs Dr q ∗
      hartWs (GF := GF) c ws ∗
      ▷ (∀ (tick : Bool) (ws' : Wstate), ⌜wsLe ws ws'⌝ -∗
          ⌜(tp tick).gpr rd = WeakEvExecEff.luival imm⌝ -∗
          ⌜(tp tick).regs .PC = BitVec.addInt pc 4⌝ -∗
          eregFr (hlc := hlc) (GF := GF) c (tp tick).regs Dr q -∗ hartWs (GF := GF) c ws' -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ELoop gen c)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ELoop gen c) := by
  intro hgen hsub hq hw hcert hrd hpc
  iintro ⟨#Hbs, Hrf, Hws, H⟩
  ihave #Ht := winstrBytesEtextWord (GF := GF) pc w $$ Hbs
  iapply ewpInstrPure gen c Dr Dw q t tp WeakFetchEff.wakIfetch pc 4 w ws hgen hsub hq hcert hw rfl
  iframe Ht Hrf Hws
  inext
  iintro %tick %ws' %hle Hrf Hws
  iapply H $$ %tick %ws' %hle %(hrd tick) %(hpc tick) Hrf Hws

end demo

end Weak
