/-
Weak: **the effect-trace toolkit** (M4-prep item (ii)): the composition kit for
the instrumented interpreter `execEff`, the memory frame of a quiet run, the
empty-memory detector, quiet traces and `wQQuiet`, and the four instruction
certificates generalised over write-free surroundings.

Rocq: `iris/WeakEff.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance.  `WeakCert` reduced a per-instruction step
certificate to ONE obligation, `wPEff tid es σ` ("the confined run succeeds with
effect trace `es`").  This file says how a leaf OBTAINS that fact without
mirroring the whole fetch/decode/execute chain at `execEff`:
* §2 THE COMPOSITION KIT: `execEffBindNil` / `execEffBind0Nil` are drop-in
  replacements for `execBindSome` / `execBind0Some` along register-only bind
  spines (every such step has an EMPTY trace); `execEffBind` is the general,
  trace-concatenating form.
* §3 THE MEMORY FRAME: a run whose trace touches no byte runs identically at
  ANY memory (`execEffMemFrame`).
* §4 THE EMPTY-MEMORY DETECTOR, the money lemma: `exec`'s RAM read arm fails on
  a missing byte and its write arm grows the domain, so one `exec` fact at the
  EMPTY memory ending with an empty domain gives the instrumented run at ANY
  memory, unchanged memory, QUIET trace (`execEffQuietOfEmpty`).  The decoder,
  every ALU/branch/control `execute` and the `try_step` wrapper are therefore
  free at `execEff`.
* §5 QUIET TRACES and `wQQuiet`: a quiet trace appends only byte-less messages
  (a zero-width write), so it changes no byte's latest write and only raises
  views -- what `wlatInterp` needs back (`wlatInterpWQQuiet`).
* §6 THE CERTIFICATES, GENERALISED: `WeakCert`'s certificates with the
  instruction's one access surrounded by ARBITRARY write-free traces.
* §7 A MEASURED MIRROR: the `try_step` wrapper at `execEff`.
Zero-width accesses are ADMITTED by `weffQuiet` (no argument over `exec` can
rule them out) and are harmless to every consumer.

**O2 (WeakCert header).**  Nothing here touches the trace pin: the
certificates are stated at `WeakCert.wPEff` (Rocq `wP_eff`), whose whole-window
form already carries the Lean-only `fetchPin s es` (WeakCert deviation 4), and
`wstepCertEff` consumes it; the per-byte `readPinned`/`fetchFresh` obligations
are `WeakCert.tracePin`'s, unused here.

**Deviations from Rocq.**
1. NAMES: the tree's camelCase (map below).  Vocabulary as `Weak/WeakCert.lean`
   deviation 1 (`n : N` ↦ `n : Nat`, `MState rs mm d` ↦ `⟨rs, mm, d⟩ : ExecSt`,
   `⊑` ↦ `≤`, `M X` ↦ `SailM X`, `Defs.bind m f` ↦ `m >>= f`,
   `Defs.bind0 m n` ↦ `m >>= fun _ => n`, `Defs.returnm` ↦ `pure`,
   `riscv_step` ↦ `riscvStep`).
2. `write_bytes_zero`: Lean's `bmWrite` takes `v : BitVec (8 * n)` (Rocq: any
   `bv w`).
3. MAPS: Rocq `mem s = ∅` is `s.mem = fun _ => none`; `dom (mem t') = ∅` is
   `∀ a, t'.mem a = none` (`BMap` is a function map, WeakCert deviation 2).
4. `Forall` predicates (`quietTrace`, `qmsgs`, `nowriteTrace`) are stated as
   `∀ x ∈ l, P x` (Rocq stdpp `Forall`; equivalent).
5. The memory frame is proved through the Lean-only `execEffMemFrameAux`
   (over an arbitrary `s` and `s.setMem mm2`), of which `execEffMemFrame` is the
   Rocq-shaped instance.  The bind kit is proved through the Lean-only bind
   EQUATION `execEffBindEq` (the `execEff` twin of `Exec.execBind`) and its
   continuation combinator `effThen`/`effThenCons` (Rocq proves each bind lemma
   by its own induction).
6. `wlat_interp_quiet_app` / `wlat_interp_wQ_quiet`: Rocq `⊢ P -∗ Q` is
   `P ⊢ Q` (the tree style), over `GF`/`WeakGS GF` (Rocq `riscvGS Σ, weakGS
   Σ`).  `qmsgs_not_writes_in` needs no resources and is outside the section.
7. `wcert_load_gen`/`wcert_amo_aq_gen`: Rocq's `ak_coh aka = false` is
   `aka.akIfetch = false`, as in `WeakCert.wcertLoad`/`wcertAmoAq` (O2: the
   only view-silent read kind of the Lean model is the i-cache fetch).
8. Stage B: the barrier effect is `wbarrierPost` (WeakCert deviation 5);
   `weffApplyNowriteRelp`/`wcertFenceGen` read its `wmWs` by `wbarrierPostWs`.
9. §7: the section `StepHartActiveEff`'s hypotheses are premises, and its
   `Let`s `s_a`/`s_tick`/`s_final` are `Weak/ExecLib.lean`'s
   `hartActiveSA`/`hartActiveSTick`/`hartActiveSFinal` (not redefined).
   `exec_eff_tick_pc` is `rfl` (as `ExecLib.execTickPc`); the hart-active
   mirror is closed by `simp` over `execEffBindEq` rather than replayed bind by
   bind (the Lean model's `try_step` has no `and_boolM`/`bind0`).

**Rocq → Lean name map.**  `read_bytes_zero` `readBytesZero`,
`write_bytes_zero` `writeBytesZero`, `exec_eff_returnm` `execEffReturnm`,
`exec_eff_instr_announce` `execEffInstrAnnounce`, `exec_eff_branch_announce`
`execEffBranchAnnounce`, `exec_eff_read_reg` `execEffReadReg`,
`exec_eff_write_reg` `execEffWriteReg`, `exec_eff_bind` `execEffBind`,
`exec_eff_bind_nil` `execEffBindNil`, `exec_eff_bind0_nil` `execEffBind0Nil`,
`exec_eff_bind_cons` `execEffBindCons`, `weff_quiet` `weffQuiet`,
`quiet_trace` `quietTrace`, `quiet_trace_nil` `quietTraceNil`,
`quiet_trace_cons_inv` `quietTraceConsInv`, `quiet_trace_app` `quietTraceApp`,
`quiet_trace_app_inv` `quietTraceAppInv`, `exec_eff_mem_frame`
`execEffMemFrame`, `exec_eff_empty_quiet` `execEffEmptyQuiet`,
`exec_eff_quiet_of_empty` `execEffQuietOfEmpty`, `qmsg` `qmsg`, `qmsgs`
`qmsgs`, `wwrite_msg_qmsg` `wwriteMsgQmsg`, `weff_apply_quiet_log`
`weffApplyQuietLog`, `weffs_quiet_log` `weffsQuietLog`, `wQ_quiet` `wQQuiet`,
`wcert_quiet` `wcertQuiet`, `qmsgs_not_writes_in` `qmsgsNotWritesIn`,
`wlat_interp_quiet_app` `wlatInterpQuietApp`, `wlat_interp_wQ_quiet`
`wlatInterpWQQuiet`, `weff_nowrite` `weffNowrite`, `nowrite_trace`
`nowriteTrace`, `nowrite_trace_cons_inv` `nowriteTraceConsInv`,
`weff_apply_nowrite_log` `weffApplyNowriteLog`, `weffs_nowrite_log`
`weffsNowriteLog`, `weff_apply_nowrite_relp` `weffApplyNowriteRelp`,
`weffs_nowrite_relp` `weffsNowriteRelp`, `flr_ws_le` `flrWsLe`,
`weffs_flr_mono` `weffsFlrMono`, `weffs_view_mono` `weffsViewMono`, `wQ_pure`
`wQPure`, `wQ_pure_quiet` `wQPureQuiet`, `wcert_nowrite` `wcertNowrite`,
`weffs_app` `weffsApp`, `wcert_fence_gen` `wcertFenceGen`, `wcert_store_gen`
`wcertStoreGen`, `wcert_load_gen` `wcertLoadGen`, `wcert_amo_aq_gen`
`wcertAmoAqGen`, `exec_eff_bind_Some` `execEffBindSome`, `exec_eff_tick_pc`
`execEffTickPc`, `s_a`/`s_tick`/`s_final` `hartActiveSA`/`hartActiveSTick`/
`hartActiveSFinal` (ExecLib, deviation 9), `exec_eff_riscv_step_hart_active`
`execEffRiscvStepHartActive`.  Lean-only: `effThen`, `effThenCons`,
`execEffBindEq`, `execEffMemFrameAux`.

**Dropped:** nothing -- every Rocq definition and lemma has a Lean twin (51
Rocq `Lemma`/`Definition`s + 3 `Let`s; Lean 51 + 4 Lean-only, the `Let`s
reused from ExecLib).

**Statements checked** (by hand, against Rocq): all; the changed ones are listed
under the deviations.
-/
import Weak.WeakCert
import Weak.ExecLib

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 0. Zero-width memory primitives -/

theorem readBytesZero (mm mm' : BMap) (pa : PAddr) (n : Nat) :
    n = 0 → bmRead mm pa n = bmRead mm' pa n := by
  rintro rfl; rfl

theorem writeBytesZero (mm : BMap) (pa : PAddr) (n : Nat) (v : BitVec (8 * n)) :
    n = 0 → bmWrite mm pa n v = mm := by
  rintro rfl; rfl

/-! ## 1. The trivial arms of `execEff` -/

theorem execEffReturnm {X : Type} (x : X) (s : ExecSt) :
    execEff (pure x : SailM X) s = some (x, s, []) := rfl

/-- The SYMBOLIC model's announcements are silent for the instrumented
interpreter too (empty trace). -/
theorem execEffInstrAnnounce {n : Nat} (w : BitVec n) (s : ExecSt) :
    execEff (LeanRV64D.Functions.instr_announce w) s = some ((), s, []) := rfl

theorem execEffBranchAnnounce (n : Nat) (a : BitVec n) (s : ExecSt) :
    execEff (LeanRV64D.Functions.branch_announce n a) s = some ((), s, []) := rfl

theorem execEffReadReg (r : Register) (s : ExecSt) :
    execEff (readReg r) s = some (s.regs r, s, []) := rfl

theorem execEffWriteReg (r : Register) (v : RegisterType r) (s : ExecSt) :
    execEff (writeReg r v) s = some (PUnit.unit, s.setReg r v, []) := rfl

/-! ## 2. THE COMPOSITION KIT -/

/-- Run a continuation after a successful instrumented run, concatenating the
traces (Lean helper, deviation 5). -/
def effThen {X Y : Type} (r : Option (X × ExecSt × List Weff))
    (g : X → ExecSt → Option (Y × ExecSt × List Weff)) : Option (Y × ExecSt × List Weff) :=
  match r with
  | some (x, s1, es) =>
    match g x s1 with
    | some (y, s2, es') => some (y, s2, es ++ es')
    | none => none
  | none => none

theorem effThenCons {X Y : Type} (e : Weff) (r : Option (X × ExecSt × List Weff))
    (g : X → ExecSt → Option (Y × ExecSt × List Weff)) :
    effThen (Weff.cons e r) g = Weff.cons e (effThen r g) := by
  rcases r with _ | ⟨x, s1, es⟩
  · rfl
  · cases hg : g x s1 with
    | none => simp [effThen, Weff.cons, hg]
    | some p =>
      obtain ⟨y, s2, es'⟩ := p
      simp [effThen, Weff.cons, hg]

/-- **The bind law** of the instrumented interpreter (Lean-only, the twin of
`Exec.execBind`). -/
theorem execEffBindEq {X Y : Type} (m : SailM X) (f : X → SailM Y) :
    ∀ s, execEff (m >>= f) s = effThen (execEff m s) (fun x s1 => execEff (f x) s1) := by
  induction m with
  | pure x =>
    intro s
    show execEff (f x) s = effThen (some (x, s, [])) _
    cases h : execEff (f x) s with
    | none => simp [effThen, h]
    | some p =>
      obtain ⟨y, s2, es'⟩ := p
      simp [effThen, h]
  | impure call k ih =>
    intro s
    cases call with
    | error e => rfl
    | ok o =>
      show execEff (FreeM.impure (.ok o) (fun v => k v >>= f)) s = _
      cases o
      case memRead n va req =>
        by_cases hm : mmioAcc req.pa n = true
        · simp only [execEff, hm, ↓reduceIte]
          cases devRead s.dev req.pa n with
          | none => rfl
          | some p =>
            obtain ⟨w, d'⟩ := p
            exact ih _ _
        · simp only [execEff, hm, Bool.false_eq_true, ↓reduceIte]
          cases bmRead s.mem req.pa n with
          | none => rfl
          | some w => exact (congrArg (Weff.cons _) (ih _ _)).trans (effThenCons _ _ _).symm
      case memWrite n va req =>
        cases hv : req.value with
        | none => simp only [execEff, hv]; rfl
        | some w =>
          by_cases hm : mmioAcc req.pa n = true
          · simp only [execEff, hv, hm, ↓reduceIte]
            cases devWrite s.dev req.pa n w with
            | none => rfl
            | some d' => exact ih _ _
          · simp only [execEff, hv, hm, Bool.false_eq_true, ↓reduceIte]
            exact (congrArg (Weff.cons _) (ih _ _)).trans (effThenCons _ _ _).symm
      case barrier b =>
        simp only [execEff]
        exact (congrArg (Weff.cons _) (ih _ _)).trans (effThenCons _ _ _).symm
      all_goals first | rfl | exact ih _ _ | (simp only [execEff]; exact ih _ _)

theorem execEffBind {X Y : Type} (m : SailM X) (f : X → SailM Y) :
    ∀ (s : ExecSt) (v : X) (st : ExecSt) (es : List Weff) (y : Y) (s' : ExecSt) (es' : List Weff),
      execEff m s = some (v, st, es) →
      execEff (f v) st = some (y, s', es') →
      execEff (m >>= f) s = some (y, s', es ++ es') := by
  intro s v st es y s' es' hm hf
  rw [execEffBindEq, hm]
  simp only [effThen, hf]

theorem execEffBindNil {X Y : Type} (m : SailM X) (f : X → SailM Y) (s : ExecSt) (v : X)
    (st : ExecSt) :
    execEff m s = some (v, st, []) → execEff (m >>= f) s = execEff (f v) st := by
  intro hm
  rw [execEffBindEq, hm]
  cases h : execEff (f v) st with
  | none => simp [effThen, h]
  | some p =>
    obtain ⟨y, s2, es'⟩ := p
    simp [effThen, h]

theorem execEffBind0Nil {Y : Type} (m : SailM Unit) (n : SailM Y) (s : ExecSt) (u : Unit)
    (st : ExecSt) :
    execEff m s = some (u, st, []) → execEff (m >>= fun _ => n) s = execEff n st :=
  execEffBindNil m (fun _ => n) s u st

/-- The bind form for the ONE step of an instruction that touches memory. -/
theorem execEffBindCons {X Y : Type} (m : SailM X) (f : X → SailM Y) (s : ExecSt) (v : X)
    (st : ExecSt) (e : Weff) (y : Y) (s' : ExecSt) (es' : List Weff) :
    execEff m s = some (v, st, [e]) →
    execEff (f v) st = some (y, s', es') →
    execEff (m >>= f) s = some (y, s', e :: es') :=
  fun hm hf => execEffBind m f s v st [e] y s' es' hm hf

/-! ## 3. QUIET TRACES, and THE MEMORY FRAME -/

def weffQuiet (e : Weff) : Prop :=
  match e with
  | .WEbar _ => True
  | .WEread _ _ n => n = 0
  | .WEwrite _ _ n _ => n = 0

def quietTrace (es : List Weff) : Prop := ∀ e, e ∈ es → weffQuiet e

theorem quietTraceNil : quietTrace [] := fun _ h => by simp at h

theorem quietTraceConsInv (e : Weff) (es : List Weff) :
    quietTrace (e :: es) → weffQuiet e ∧ quietTrace es :=
  fun h => List.forall_mem_cons.1 h

theorem quietTraceApp (es1 es2 : List Weff) :
    quietTrace es1 → quietTrace es2 → quietTrace (es1 ++ es2) := by
  intro h1 h2 e he
  rcases List.mem_append.1 he with h | h
  · exact h1 e h
  · exact h2 e h

theorem quietTraceAppInv (es1 es2 : List Weff) :
    quietTrace (es1 ++ es2) → quietTrace es1 ∧ quietTrace es2 :=
  fun h => ⟨fun e he => h e (List.mem_append_left _ he), fun e he => h e (List.mem_append_right _ he)⟩

/-- The memory frame over an arbitrary state (Lean-only, deviation 5). -/
theorem execEffMemFrameAux {X : Type} (m : SailM X) :
    ∀ (s : ExecSt) (x : X) (t' : ExecSt) (es : List Weff),
      execEff m s = some (x, t', es) → quietTrace es →
      t'.mem = s.mem ∧ ∀ mm2, execEff m (s.setMem mm2) = some (x, t'.setMem mm2, es) := by
  induction m with
  | pure y =>
    intro s x t' es h _
    simp only [execEff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, fun _ => rfl⟩
  | impure call k ih =>
    intro s x t' es h hq
    cases call with
    | error e => simp [execEff] at h
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [execEff] at h
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at h
          cases hdr : devRead s.dev req.pa n with
          | none => simp only [hdr] at h; cases h
          | some p =>
            obtain ⟨w0, d0⟩ := p
            simp only [hdr] at h
            obtain ⟨hm, hall⟩ := ih _ _ _ _ _ h hq
            refine ⟨hm, fun mm2 => ?_⟩
            simp only [execEff]
            rw [if_pos hd, show (s.setMem mm2).dev = s.dev from rfl, hdr]
            exact hall mm2
        · rw [if_neg hd] at h
          cases hrb : bmRead s.mem req.pa n with
          | none => simp only [hrb] at h; cases h
          | some w0 =>
            simp only [hrb] at h
            obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
            obtain ⟨hn, hq0⟩ := quietTraceConsInv _ _ hq
            obtain ⟨hm, hall⟩ := ih _ _ _ _ _ h0 hq0
            refine ⟨hm, fun mm2 => ?_⟩
            simp only [execEff]
            rw [if_neg hd, show (s.setMem mm2).mem = mm2 from rfl,
              readBytesZero mm2 s.mem req.pa n hn, hrb]
            exact Weff.consEqSome.2 ⟨es0, hall mm2, rfl⟩
      case memWrite n va req =>
        simp only [execEff] at h
        cases hv : req.value with
        | none => simp only [hv] at h; cases h
        | some w =>
          simp only [hv] at h
          by_cases hd : mmioAcc req.pa n = true
          · rw [if_pos hd] at h
            cases hdw : devWrite s.dev req.pa n w with
            | none => simp only [hdw] at h; cases h
            | some d0 =>
              simp only [hdw] at h
              obtain ⟨hm, hall⟩ := ih _ _ _ _ _ h hq
              refine ⟨hm, fun mm2 => ?_⟩
              simp only [execEff, hv]
              rw [if_pos hd, show (s.setMem mm2).dev = s.dev from rfl, hdw]
              exact hall mm2
          · rw [if_neg hd] at h
            obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
            obtain ⟨hn, hq0⟩ := quietTraceConsInv _ _ hq
            rw [writeBytesZero s.mem req.pa n w hn] at h0
            obtain ⟨hm, hall⟩ := ih _ _ _ _ _ h0 hq0
            refine ⟨hm, fun mm2 => ?_⟩
            simp only [execEff, hv]
            rw [if_neg hd, show (s.setMem mm2).mem = mm2 from rfl, writeBytesZero mm2 req.pa n w hn]
            exact Weff.consEqSome.2 ⟨es0, hall mm2, rfl⟩
      case barrier b =>
        simp only [execEff] at h
        obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
        obtain ⟨_, hq0⟩ := quietTraceConsInv _ _ hq
        obtain ⟨hm, hall⟩ := ih _ _ _ _ _ h0 hq0
        refine ⟨hm, fun mm2 => ?_⟩
        simp only [execEff]
        exact Weff.consEqSome.2 ⟨es0, hall mm2, rfl⟩
      all_goals first
        | (simp only [execEff, reduceCtorEq] at h; done)
        | (simp only [execEff] at h
           obtain ⟨hm, hall⟩ := ih _ _ _ _ _ h hq
           refine ⟨hm, fun mm2 => ?_⟩
           simp only [execEff]
           exact hall mm2)

/-- A quiet run does not look at memory and does not change it. -/
theorem execEffMemFrame {X : Type} (m : SailM X) :
    ∀ (rs : RegFile) (mm1 : BMap) (d : DevStates) (x : X) (t' : ExecSt) (es : List Weff),
      execEff m ⟨rs, mm1, d⟩ = some (x, t', es) → quietTrace es →
      t'.mem = mm1 ∧ ∀ mm2, execEff m ⟨rs, mm2, d⟩ = some (x, ⟨t'.regs, mm2, t'.dev⟩, es) :=
  fun _ _ _ x t' es h hq => execEffMemFrameAux m _ x t' es h hq

/-! ## 4. THE EMPTY-MEMORY DETECTOR -/

theorem execEffEmptyQuiet {X : Type} (m : SailM X) :
    ∀ (s : ExecSt) (x : X) (t' : ExecSt) (es : List Weff),
      execEff m s = some (x, t', es) →
      s.mem = (fun _ => none) → (∀ a, t'.mem a = none) →
      quietTrace es := by
  induction m with
  | pure y =>
    intro s x t' es h _ _
    simp only [execEff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    exact quietTraceNil
  | impure call k ih =>
    intro s x t' es h hms hdom
    cases call with
    | error e => simp [execEff] at h
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [execEff] at h
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at h
          cases hdr : devRead s.dev req.pa n with
          | none => simp only [hdr] at h; cases h
          | some p =>
            obtain ⟨w0, d0⟩ := p
            simp only [hdr] at h
            exact ih _ _ _ _ _ h hms hdom
        · rw [if_neg hd] at h
          cases hrb : bmRead s.mem req.pa n with
          | none => simp only [hrb] at h; cases h
          | some w0 =>
            simp only [hrb] at h
            obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
            have hn : n = 0 := by
              rcases Nat.eq_zero_or_pos n with h0 | hpos
              · exact h0
              · have hin := readBytesDom s.mem req.pa n w0 hrb 0 hpos
                rw [hms] at hin
                simp at hin
            exact List.forall_mem_cons.2 ⟨hn, ih _ _ _ _ _ h0 hms hdom⟩
      case memWrite n va req =>
        simp only [execEff] at h
        cases hv : req.value with
        | none => simp only [hv] at h; cases h
        | some w =>
          simp only [hv] at h
          by_cases hd : mmioAcc req.pa n = true
          · rw [if_pos hd] at h
            cases hdw : devWrite s.dev req.pa n w with
            | none => simp only [hdw] at h; cases h
            | some d0 =>
              simp only [hdw] at h
              exact ih _ _ _ _ _ h hms hdom
          · rw [if_neg hd] at h
            obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
            have hsub := execDomMono _ _ _ _ (execEffExec _ _ _ _ _ h0)
            have hn : n = 0 := by
              rcases Nat.eq_zero_or_pos n with hz | hpos
              · exact hz
              · have hin := hsub _ (writeBytesDom s.mem req.pa n w 0 hpos)
                rw [hdom] at hin
                simp at hin
            refine List.forall_mem_cons.2 ⟨hn, ih _ _ _ _ _ h0 ?_ hdom⟩
            show bmWrite s.mem req.pa n w = _
            rw [writeBytesZero _ _ _ _ hn, hms]
      case barrier b =>
        simp only [execEff] at h
        obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
        exact List.forall_mem_cons.2 ⟨trivial, ih _ _ _ _ _ h0 hms hdom⟩
      all_goals first
        | (simp only [execEff, reduceCtorEq] at h; done)
        | (simp only [execEff] at h; exact ih _ _ _ _ _ h hms hdom)

/-- THE MONEY LEMMA.  From ONE `exec` fact at the empty memory: the
instrumented run at ANY memory succeeds with the same value, the same registers
and device state, an UNCHANGED memory, and a QUIET trace. -/
theorem execEffQuietOfEmpty {X : Type} (m : SailM X) (rs : RegFile) (d : DevStates) (x : X)
    (t' : ExecSt) :
    exec m ⟨rs, fun _ => none, d⟩ = some (x, t') →
    (∀ a, t'.mem a = none) →
    ∃ es, quietTrace es ∧
      ∀ mm, execEff m ⟨rs, mm, d⟩ = some (x, ⟨t'.regs, mm, t'.dev⟩, es) := by
  intro hex hdom
  obtain ⟨es, hee⟩ := execExecEff m _ x t' hex
  have hq := execEffEmptyQuiet m _ x t' es hee rfl hdom
  exact ⟨es, hq, (execEffMemFrame m rs _ d x t' es hee hq).2⟩

/-! ## 5. WHAT A QUIET TRACE DOES TO THE STATE -/

def qmsg (m : Wmsg) : Prop := ∀ a, msgByte m a = none
def qmsgs (l : List Wmsg) : Prop := ∀ m, m ∈ l → qmsg m

theorem wwriteMsgQmsg (tid : Option Nat) (k : WmClass) (pa : PAddr) (n : Nat) (v : BitVec (8 * n)) :
    n = 0 → qmsg (wwriteMsg tid k pa n v) := by
  rintro rfl a
  simp [msgByte, wwriteMsg]

theorem weffApplyQuietLog (tid : Option Nat) (s : Wmstate) (e : Weff) :
    weffQuiet e → ∃ l, (weffApply tid s e).wmLog = s.wmLog ++ l ∧ qmsgs l := by
  cases e with
  | WEread ak pa n =>
    intro _
    exact ⟨[], by rw [weffApplyRead, wreadPostLog, List.append_nil], fun _ h => by simp at h⟩
  | WEwrite ak pa n v =>
    intro hq
    refine ⟨[wwriteMsg tid (wmClassOf ak s.wmWs) pa n v], rfl, fun m hm => ?_⟩
    simp only [List.mem_singleton] at hm
    subst hm
    exact wwriteMsgQmsg _ _ _ _ _ hq
  | WEbar b =>
    intro _
    exact ⟨[], by rw [List.append_nil]; rfl, fun _ h => by simp at h⟩

theorem weffsQuietLog (tid : Option Nat) (s : Wmstate) (es : List Weff) :
    quietTrace es → ∃ l, (weffs tid s es).wmLog = s.wmLog ++ l ∧ qmsgs l := by
  induction es generalizing s with
  | nil => intro _; exact ⟨[], by rw [List.append_nil]; rfl, fun _ h => by simp at h⟩
  | cons e es ih =>
    intro hq
    obtain ⟨he, hes⟩ := quietTraceConsInv _ _ hq
    obtain ⟨l1, hl1, hq1⟩ := weffApplyQuietLog tid s e he
    obtain ⟨l2, hl2, hq2⟩ := ih (weffApply tid s e) hes
    refine ⟨l1 ++ l2, by rw [weffsCons, hl2, hl1, List.append_assoc], fun m hm => ?_⟩
    rcases List.mem_append.1 hm with h | h
    · exact hq1 m h
    · exact hq2 m h

/-- The certificate-level `Q` of a memory-effect-free instruction. -/
def wQQuiet : Wmstate → Wmstate → Prop :=
  fun s s' =>
    s'.wmImg = s.wmImg ∧
    (∃ l, s'.wmLog = s.wmLog ++ l ∧ qmsgs l) ∧
    wsLe s.wmWs s'.wmWs

theorem wcertQuiet (cid : Nat) (pc : BitVec 64) (es : List Weff) :
    quietTrace es → wstepCert cid pc (wPEff (some cid) es) wQQuiet := by
  intro hq
  apply wstepCertEff
  intro s s' hi hl hws
  obtain ⟨l, hl', hql⟩ := weffsQuietLog (some cid) s es hq
  unfold wQQuiet
  exact ⟨hi, ⟨l, by rw [hl, hl'], hql⟩, by rw [hws]; exact weffsWsLe _ _ _⟩

theorem qmsgsNotWritesIn (log l : List Wmsg) (a : Int) :
    qmsgs l → ¬ writesIn (log ++ l) a log.length (log ++ l).length :=
  fun hq => notWritesInAppNew log l a (fun m hm => hq m hm a)

section quietInterp
variable {GF : BundledGFunctors} [WeakGS GF]

/-- A quiet append preserves the latest-write authority. -/
theorem wlatInterpQuietApp (img : GMapF PAddr (BitVec 8)) (log l : List Wmsg) :
    qmsgs l → wlatInterp (GF := GF) img log ⊢ wlatInterp img (log ++ l) := by
  intro hq
  unfold wlatInterp
  iintro ⟨%m, %mc, Hauth, %hag, Hc, %hagc⟩
  iexists m, mc
  iframe Hauth Hc
  isplit
  · ipureintro
    exact wlatAgreeApp _ _ _ _ hag (fun a _ => qmsgsNotWritesIn log l a hq)
  · ipureintro
    exact wcdsAgreeApp _ _ _ (fun a _ mg hmg => hq mg hmg a) hagc

/-- ...and at the shape a leaf meets it. -/
theorem wlatInterpWQQuiet (s s' : Wmstate) :
    wQQuiet s s' →
    wlatInterp (GF := GF) s.wmImg s.wmLog ⊢ wlatInterp s'.wmImg s'.wmLog := by
  rintro ⟨hi, ⟨l, hl, hql⟩, -⟩
  rw [hi, hl]
  exact wlatInterpQuietApp _ _ _ hql

end quietInterp

/-! ## 6. THE CERTIFICATES, GENERALISED OVER WRITE-FREE SURROUNDINGS -/

def weffNowrite (e : Weff) : Prop :=
  match e with
  | .WEwrite _ _ _ _ => False
  | _ => True

def nowriteTrace (es : List Weff) : Prop := ∀ e, e ∈ es → weffNowrite e

theorem nowriteTraceConsInv (e : Weff) (es : List Weff) :
    nowriteTrace (e :: es) → weffNowrite e ∧ nowriteTrace es :=
  fun h => List.forall_mem_cons.1 h

theorem weffApplyNowriteLog (tid : Option Nat) (s : Wmstate) (e : Weff) :
    weffNowrite e → (weffApply tid s e).wmLog = s.wmLog := by
  cases e with
  | WEread ak pa n => intro _; exact wreadPostLog _ _ _ _
  | WEwrite => intro h; exact h.elim
  | WEbar b => intro _; rfl

theorem weffsNowriteLog (tid : Option Nat) (s : Wmstate) (es : List Weff) :
    nowriteTrace es → (weffs tid s es).wmLog = s.wmLog := by
  induction es generalizing s with
  | nil => intro _; rfl
  | cons e es ih =>
    intro he
    obtain ⟨he1, he2⟩ := nowriteTraceConsInv _ _ he
    rw [weffsCons, ih _ he2]
    exact weffApplyNowriteLog tid s e he1

/-- `wRelp` is MONOTONE along a write-free suffix. -/
theorem weffApplyNowriteRelp (tid : Option Nat) (s : Wmstate) (e : Weff) :
    weffNowrite e → s.wmWs.wRelp = true → (weffApply tid s e).wmWs.wRelp = true := by
  cases e with
  | WEread ak pa n =>
    intro _ hr
    rw [weffApplyRead, WeakInstr.wreadPostRelp]
    exact hr
  | WEwrite => intro h; exact h.elim
  | WEbar b =>
    intro _ hr
    rw [weffApplyBar, wbarrierPostWs]
    cases b <;> simp [barrierPost, Weak.fencePost, hr]

theorem weffsNowriteRelp (tid : Option Nat) (s : Wmstate) (es : List Weff) :
    nowriteTrace es → s.wmWs.wRelp = true → (weffs tid s es).wmWs.wRelp = true := by
  induction es generalizing s with
  | nil => intro _ hr; exact hr
  | cons e es ih =>
    intro he hr
    obtain ⟨he1, he2⟩ := nowriteTraceConsInv _ _ he
    rw [weffsCons]
    exact ih _ he2 (weffApplyNowriteRelp tid s e he1 hr)

/-- The view side: a floor already reached is not lost. -/
theorem flrWsLe (ws ws' : Wstate) (a : Int) :
    wsLe ws ws' → flr (wsView ws) a ≤ flr (wsView ws') a :=
  fun h => (View.le_spec _ _).1 (wsView_mono _ _ h) a

theorem weffsFlrMono (tid : Option Nat) (s : Wmstate) (es : List Weff) (a : Int) :
    flr (wsView s.wmWs) a ≤ flr (wsView (weffs tid s es).wmWs) a :=
  flrWsLe _ _ _ (weffsWsLe _ _ _)

theorem weffsViewMono (tid : Option Nat) (s : Wmstate) (es : List Weff) (V : View) :
    V ≤ wsView s.wmWs → V ≤ wsView (weffs tid s es).wmWs :=
  fun hV => viewLeTrans hV (wsView_mono _ _ (weffsWsLe _ _ _))

/-! ### 6a. A memory-effect-free instruction (branch / jump / ALU) -/

def wQPure : Wmstate → Wmstate → Prop :=
  fun s s' => s'.wmImg = s.wmImg ∧ s'.wmLog = s.wmLog ∧ wsLe s.wmWs s'.wmWs

theorem wQPureQuiet (s s' : Wmstate) : wQPure s s' → wQQuiet s s' := by
  rintro ⟨hi, hl, hws⟩
  exact ⟨hi, ⟨[], by rw [List.append_nil]; exact hl, fun _ h => by simp at h⟩, hws⟩

theorem wcertNowrite (cid : Nat) (pc : BitVec 64) (es : List Weff) :
    nowriteTrace es → wstepCert cid pc (wPEff (some cid) es) wQPure := by
  intro hnw
  apply wstepCertEff
  intro s s' hi hl hws
  unfold wQPure
  exact ⟨hi, by rw [hl]; exact weffsNowriteLog (some cid) s es hnw,
    by rw [hws]; exact weffsWsLe _ _ _⟩

theorem weffsApp (tid : Option Nat) (s : Wmstate) (es1 es2 : List Weff) :
    weffs tid s (es1 ++ es2) = weffs tid (weffs tid s es1) es2 := by
  unfold weffs
  rw [List.foldl_append]

/-! ### 6b. `fence` with write-free surroundings -/

theorem wcertFenceGen (cid : Nat) (pc : BitVec 64) (pre post : List Weff) (b : barrier_kind) :
    nowriteTrace pre → nowriteTrace post →
    wstepCert cid pc (wPEff (some cid) (pre ++ .WEbar b :: post)) (wQFence b) := by
  intro _ hpost
  apply wstepCertEff
  intro s s' _ _ hws
  unfold wQFence wVFence
  rw [hws, weffsApp, weffsCons, weffApplyBar]
  refine ⟨wsLeTrans (barrierPostMono _ _ b (weffsWsLe _ _ _))
    (weffsWsLe _ (wbarrierPost (weffs (some cid) s pre) b) post), fun ha => ?_⟩
  apply weffsNowriteRelp _ _ _ hpost
  rw [wbarrierPostWs]
  exact WeakInstr.barrierPostRelp _ b ha

/-! ### 6c. The 4-byte STORE with write-free surroundings -/

theorem wcertStoreGen (cid : Nat) (pc : BitVec 64) (pre post : List Weff) (akw : AkInfo)
    (ea : PAddr) (v : BitVec 32) :
    nowriteTrace pre → nowriteTrace post →
    wstepCert cid pc (wPEff (some cid) (pre ++ .WEwrite akw ea 4 v :: post))
      (wQStore (some cid) ea v) := by
  intro hpre hpost
  apply wstepCertEff
  intro s s' hi hl hws
  have hle : wsLe s.wmWs s'.wmWs := by rw [hws]; exact weffsWsLe _ _ _
  have hl1 : (weffs (some cid) s pre).wmLog = s.wmLog := weffsNowriteLog _ _ _ hpre
  rw [weffsApp, weffsCons, weffApplyWrite] at hl hws
  rw [weffsNowriteLog _ _ _ hpost, wwritePostLog, hl1] at hl
  unfold wQStore wQStoreW wVStoreW
  refine ⟨hi, ⟨_, hl, fun hr => WeakInstr.wmClassOfRelp _ _ (weffsNowriteRelp _ _ _ hpre hr)⟩,
    hle, fun j hj => ?_⟩
  -- the floor reached at the store's own step survives the write-free tail
  have h2 := flrWsLe _ _ (WeakInterp.accAddr ea j)
    (weffsWsLe (some cid) (wwritePost (some cid) (weffs (some cid) s pre) akw ea 4 v) post)
  rw [← hws, wwritePostWs, flr_wsView, hl1] at h2
  have := storePostRunCoh (weffs (some cid) s pre).wmWs akw.akSync (paZ ea) 4
    (s.wmLog.length + 1) j hj
  simp only [WeakInterp.accAddr] at h2 ⊢
  omega

/-! ### 6d. The 4-byte plain LOAD with write-free surroundings -/

theorem wcertLoadGen (cid : Nat) (pc : BitVec 64) (pre post : List Weff) (akl : AkInfo)
    (ea : PAddr) :
    akl.akIfetch = false →
    nowriteTrace pre → nowriteTrace post →
    wstepCert cid pc (wPEff (some cid) (pre ++ .WEread akl ea 4 :: post)) (wQLoad ea) := by
  intro hcoh hpre hpost
  apply wstepCertEff
  intro s s' hi hl hws
  have hl1 : (weffs (some cid) s pre).wmLog = s.wmLog := weffsNowriteLog _ _ _ hpre
  rw [weffsApp, weffsCons, weffApplyRead] at hl hws
  rw [weffsNowriteLog _ _ _ hpost, wreadPostLog, hl1] at hl
  rw [cohTsLog _ s ea 4 hl1] at hws
  unfold wQLoad wQLoadW wVLoadW
  refine ⟨hi, hl, fun j hj => ?_⟩
  rw [hws, ← cohTsLookup s ea 4 j hj]
  refine viewLeTrans ?_ (wsView_mono _ _ (weffsWsLe _ _ post))
  rw [wreadPostWsWeak _ akl ea _ hcoh]
  exact loadPostRunGain (fun a t => viewByte a t) _ akl.akSync (paZ ea) (cohTs s ea 4) j
    (fun w a t => load_byte_gain w _ _ a t) (by rw [cohTsLength]; exact hj)

/-! ### 6e. `amoswap.w.aq` with write-free surroundings -/

theorem wcertAmoAqGen (cid : Nat) (pc : BitVec 64) (pre post : List Weff) (aka akw : AkInfo)
    (ea : PAddr) (v : BitVec 32) :
    aka.akIfetch = false → aka.akSync = true → akw.akLatest = true →
    nowriteTrace pre → nowriteTrace post →
    wstepCert cid pc
      (wPEff (some cid) (pre ++ .WEread aka ea 4 :: .WEwrite akw ea 4 v :: post))
      (wQAmoAq (some cid) ea v) := by
  intro hcoh hsync hlat hpre hpost
  apply wstepCertEff
  intro s s' hi hl hws
  have hle : wsLe s.wmWs s'.wmWs := by rw [hws]; exact weffsWsLe _ _ _
  have hl1 : (weffs (some cid) s pre).wmLog = s.wmLog := weffsNowriteLog _ _ _ hpre
  rw [weffsApp, weffsCons, weffsCons, weffApplyRead, weffApplyWrite] at hl hws
  rw [cohTsLog _ s ea 4 hl1] at hl hws
  rw [weffsNowriteLog _ _ _ hpost, wwritePostLog, wreadPostLog, hl1] at hl
  have hws2 : (wreadPost (weffs (some cid) s pre) aka ea (cohTs s ea 4)).wmWs =
      loadPostRun (weffs (some cid) s pre).wmWs true (paZ ea) (cohTs s ea 4) := by
    rw [wreadPostWsWeak _ aka ea _ hcoh, hsync]
  have hexcl : wmClassOf akw (wreadPost (weffs (some cid) s pre) aka ea (cohTs s ea 4)).wmWs =
      .WCexcl := by
    simp [wmClassOf, hlat]
  unfold wQAmoAq wQAmoAqW
  refine ⟨?_, ?_, by rw [hl, hexcl]⟩
  · unfold wQStoreW wVStoreW
    refine ⟨hi, ⟨_, hl, fun hr => WeakInstr.wmClassOfRelp _ _
      (by rw [WeakInstr.wreadPostRelp]; exact weffsNowriteRelp _ _ _ hpre hr)⟩, hle, fun j hj => ?_⟩
    have h2 := flrWsLe _ _ (WeakInterp.accAddr ea j)
      (weffsWsLe (some cid)
        (wwritePost (some cid) (wreadPost (weffs (some cid) s pre) aka ea (cohTs s ea 4)) akw ea 4 v)
        post)
    rw [← hws, wwritePostWs, flr_wsView, wreadPostLog, hl1] at h2
    have := storePostRunCoh (wreadPost (weffs (some cid) s pre) aka ea (cohTs s ea 4)).wmWs
      akw.akSync (paZ ea) 4 (s.wmLog.length + 1) j hj
    simp only [WeakInterp.accAddr] at h2 ⊢
    omega
  · unfold wVAmoAqW
    intro j hj
    rw [hws, ← cohTsLookup s ea 4 j hj]
    refine viewLeTrans ?_ (wsView_mono _ _ (weffsWsLe _ _ post))
    refine viewLeTrans ?_ (wsView_mono _ _ (wwritePostWsLe _ _ _ _ _ _))
    rw [hws2]
    exact loadPostRunGain (fun _ t => viewScl t) (weffs (some cid) s pre).wmWs true (paZ ea)
      (cohTs s ea 4) j (fun w a t => amo_acq_gain w _ a t) (by rw [cohTsLength]; exact hj)

/-! ## 7. A MEASURED MIRROR: the `try_step` wrapper at `execEff` -/

theorem execEffBindSome {X Y : Type} (m : SailM X) (f : X → SailM Y) (s : ExecSt) (v : X)
    (st : ExecSt) (es : List Weff) :
    execEff m s = some (v, st, es) →
    execEff (m >>= f) s =
      match execEff (f v) st with
      | some (y, s', es') => some (y, s', es ++ es')
      | none => none := by
  intro hm
  rw [execEffBindEq, hm]
  rfl

theorem execEffTickPc (s : ExecSt) :
    execEff (tick_pc ()) s = some ((), s.setReg .PC (s.regs .nextPC), []) := rfl

/-- Rocq `exec_eff_riscv_step_hart_active` (deviation 9): the whole trace of
the wrapper is `run_hart_active`'s. -/
theorem execEffRiscvStepHartActive (s sExec : ExecSt) (retval : BitVec 32) (b : Bool)
    (es : List Weff)
    (hsi : execEff (should_inc_minstret (s.regs .cur_privilege)) s = some (b, s, []))
    (hhartA : (hartActiveSA s b).regs .hart_state = .HART_ACTIVE ())
    (hha : execEff (run_hart_active 0) (hartActiveSA s b) =
      some (.Step_Execute (.Retire_Success (), retval), sExec, es))
    (hhartExec : sExec.regs .hart_state = .HART_ACTIVE ())
    (hmiExec : sExec.regs .minstret_increment = b) :
    execEff (riscvStep false) s = some ((), hartActiveSFinal sExec b, es) := by
  unfold hartActiveSA at hhartA hha
  unfold riscvStep try_step
  simp only [execEffBindEq, readReg, writeReg, PreSail.readReg, PreSail.writeReg, PreSail.emit,
    execEff, effThen, hsi, hhartA, hha, hhartExec, assert, PreSail.assert, hart_is_active,
    ↓reduceIte, execEffReturnm, execEffTickPc, get_config_rvfi, Bool.false_eq_true,
    List.nil_append, List.append_nil]
  have hmi : (sExec.setReg .PC (sExec.regs .nextPC)).regs .minstret_increment = b := by
    show (sExec.regs.set .PC (sExec.regs .nextPC)) .minstret_increment = b
    rw [RegFile.set_other _ _ _ _ (by decide)]
    exact hmiExec
  rw [hmi]
  cases b <;> simp only [execEffBindEq, execEff, effThen, ↓reduceIte, execEffReturnm,
    Bool.false_eq_true, List.append_nil] <;> rfl

end Weak
