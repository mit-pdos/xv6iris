/-
Weak: **the c.jr `wpd` from ANY register file that agrees with the reference state on the
step's UPWARD-EXPOSED read footprint** (both tick bits, every `ra`).

Rocq: `iris/AxEpiCjrFrame.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`AxEpiCjrSym.wpdCjrSym` starts at the reference file `(probeRegs pcJr).set .x1 ra`; the real
post-c.ldsp file differs (counters, nextPC, …).  Here the ledger facts are TRANSFERRED from the
reference state `t0` to any `rs` with `agreeOn A rs t0.regs`.
§1 AGREEMENT-TRACKING EVALUATORS `toPinAg` / `erdAg` / `epureAg`: the walk, `erd` and `epure`
carrying a set `A` of registers on which two states are known to agree: a read of `r` fails
unless `r ∈ A`; a write of `r` adds `r` (both runs write the same value).  So `A` at the start
needs only the registers READ BEFORE BEING WRITTEN.  Transfer (`*Sound`): a successful tracked
run on `t` gives the SAME untracked run (same continuation) on any `t'` agreeing on `A`, ending
in states agreeing on the final set.
§2 `CjrFrameFacts` (the ledger with tracked evaluators) ⇒ `AxEpiModelFacts` at any agreeing
state (`frameFactsTransfer`); `post` need only be local to a set `P` contained in the final
tracked set; `wpdCjrFrameGen`.
§3 the instance: `AJr`, the upward-exposed reads of c.jr (tick = false) at `tFrame ra mi mp`
(`minstret`, `mip` symbolic), every `ra` (the wrap-free twin trick of `AxEpiCjrSym`);
`wpdCjrFrame` (the caller matches `AJrFix`).
§4 tick = true: the ledger `AxCjrTickFacts` (after the fetch, `tickPostOk`: the tick's pin
reads, then `epure` to `.pure ()`), `wpdCjrStepOfLedgerTick`, its tracked twin
`CjrTickFrameFacts`, the instance at `tFrameT ra mi mc` (`minstret`, `mcycle` symbolic), and
`wpdCjrFrameTick` for both tick bits (row end `cjrFrameInv tick`, sanity
`cjrFrameInvReachesRet'`).

## Deviations from Rocq

1. THE TWO-PIN BOUNDARY (`AxEpiLedger` deviation 1, the CONVENTION).  Rocq `to_seip_ag` ↦
   `toPinAg`, the tracked `AxEpiLedger.toPin` (stops at a read of EITHER pin, fails at an
   sfence.vma announce); `seipAtAg` checks the `sig_meip` node and the `sig_seip` node after both
   meip answers (Lean-only `AxEpiCjrFrame.seipAfterAg`); `branchAtAg`/`branchAtTickAg`/
   `cjrtBranchAt` take the two answers `v' v`; `CjrFrameFacts` (`cf*`), `AxCjrTickFacts`
   (`ct*`), `CjrTickFrameFacts` (`cft*`) add the `…MeipDr`/`…MeipD` fields and have four branch
   fields `…00/01/10/11` (Rocq `…branch0/1`); `tickPostOkAg` walks to the tick's meip node and,
   per answer (Lean-only `AxEpiCjrFrame.tickAfterMeipAg`), to its seip node (as
   `AxEpiLedgerTick.tickPostOk`); `ledgerCjrtInv` has the meip-level `Pseip` disjunct and
   quantifies the seip node per meip answer; `wpdCjrStepOfLedgerTick` splits twice; the
   reaches lemmas take both pins `∉ Dr` / `∉ D` (Rocq only `sig_seip`); `regs_agree seip_reg`
   ↦ `regsAgree AxRunClose.pinReg`.
2. O2 STAGE C (`AxEpiLedger` deviation 3): the fetch is a pinned admin step at the SAME row
   position.  `fetchOkAg`/`fetchOkTickAg`/`cjrtFetchOk` check `akIfetch = true` (Rocq
   `negb ak_latest`; so `cjrtBranchOkNode` returns `akIfetch = true`); `Hgd` states
   `AxCjrWpd.fetchImgOk` (Rocq `fetch_gd_ok`); `Hflow`/`Hloc` are dropped; `RetS`/`RetP` and the
   post-fetch `tickTailInv` of `ledgerCjrtInv` sit at `kk` (Rocq `S kk`); the fetch step of
   `cjrtFetchReaches` is `AxEpiLedger.ledgerStep`'s fetch arm (same position).  Generic `hlc`
   (Rocq `HasNoLc`).
3. THE FOOTPRINTS (found with a tracer over the Lean model, checked by the ledgers): `AJr` has
   18 registers — Rocq's 19 minus `sig_meip`, which in Lean is a PIN (the walk stops there and
   the read is answered by `AxEpiLedger.ansMeip`, never from the file); `AJrT` = `AJr` plus the
   5 timer registers, as Rocq.
4. CONJUNCT ORDER: `fetchOkAg`/`tickRetOkAg` test `P ⊆ A3` BEFORE `post` (Rocq `post && …`),
   so that the kernel spine of a branch ends at the post leaf (`ax_epi_cjr_sym_kclose`).
5. TYPES (as `AxEpiLedger` deviation 4): `gset register` ↦ `List Register`, `{[r]} ∪ A` ↦
   `r :: A`, `bool_decide (P ⊆ A3)` ↦ `P.all (decide (· ∈ A3))`, `A ∖ {[…]}` ↦
   `List.filter`,
   `register_lookup r rs` ↦ `rs r`, `MState rs t0.mem t0.mdev` ↦ `⟨rs, t0.mem, t0.dev⟩`,
   `probe_mem`/`dev0_state` ↦ `probeMem`/`testDevs`, `Dr_noseip` ↦ `AxEpiProbe.drNopin`; the
   tracked results are right-nested `(m, t, A)` (Rocq `((m, t), A)`); `bv 1` answers ↦
   `BitVec 1`; the `dir` flag is gone (lean-sail `regRead`).
6. `vm_compute; reflexivity` ↦ `decide +kernel` (closed fields), `ax_epi_ledger_krfl` (the
   boundary walk with free words) and `AxEpiCjrSym`'s kernel-spine tactics (branches, the
   counters left symbolic as Rocq).  The tick branch has four post leaves (both tick pin
   answers per branch): Lean-only `AxEpiCjrFrame.kloopCore` / tactic `ax_epi_cjr_frame_kloop`
   cases on each, the `false` arm absurd by `HE`.  Rocq `cjr_frame_tac` ↦ tactic macro
   `ax_epi_cjr_frame_tac` (declared in §4, after the constants it unfolds; `branchFrameSym`
   spells it out, as Rocq).

**Rocq → Lean name map.**  `agree_on` `agreeOn`, `agree_on_sym` `agreeOnSym`, `agree_on_set`
`agreeOnSet`, `agree_on_set_reg` `agreeOnSetReg`, `to_seip_ag` `toPinAg`, `erd_ag` `erdAg`,
`epure_ag` `epureAg`, `to_seip_ag_sound` `toPinAgSound`, `erd_ag_sound` `erdAgSound`,
`epure_ag_sound` `epureAgSound`, `post_local` `postLocal`, `fetch_ok_ag` `fetchOkAg`,
`branch_ok_ag` `branchOkAg`, `seip_at_ag` `seipAtAg`, `branch_at_ag` `branchAtAg`,
`CjrFrameFacts` `CjrFrameFacts`, `fetch_ok_ag_transfer` `fetchOkAgTransfer`,
`branch_ok_ag_transfer` `branchOkAgTransfer`, `frame_facts_transfer` `frameFactsTransfer`,
`wpd_cjr_frame_gen` `wpdCjrFrameGen`, `A_jr` `AJr`, `P_pc` `PPc`, `post_ra_sym_local`
`postRaSymLocal`, `t_frame` `tFrame`, `branch_frame_sym` `branchFrameSym`, `epi_frame_cjr`
`epiFrameCjr`, `A_jr_fix` `AJrFix`, `agree_frame` `agreeFrame`, `cjr_frame_inv_reaches_ret`
`cjrFrameInvReachesRet`, `wpd_cjr_frame` `wpdCjrFrame`, `cjrt_fetch_ok` `cjrtFetchOk`,
`cjrt_branch_ok` `cjrtBranchOk`, `cjrt_branch_at` `cjrtBranchAt`, `AxCjrTickFacts`
`AxCjrTickFacts`, `cjrt_branch_ok_node` `cjrtBranchOkNode`, `ledger_cjrt_inv` `ledgerCjrtInv`,
`cjrt_fetch_reaches` `cjrtFetchReaches`, `cjrt_branch_reaches` `cjrtBranchReaches`,
`ledger_cjrt_inv_reaches_ret` `ledgerCjrtInvReachesRet`, `wpd_cjr_step_of_ledger_tick`
`wpdCjrStepOfLedgerTick`, `tick_ret_ok_ag` `tickRetOkAg`, `tick_post_ok_ag` `tickPostOkAg`,
`fetch_ok_tick_ag` `fetchOkTickAg`, `branch_ok_tick_ag` `branchOkTickAg`, `branch_at_tick_ag`
`branchAtTickAg`, `CjrTickFrameFacts` `CjrTickFrameFacts`, `tick_ret_ok_ag_transfer`
`tickRetOkAgTransfer`, `tick_post_ok_ag_transfer` `tickPostOkAgTransfer`,
`branch_ok_tick_ag_transfer` `branchOkTickAgTransfer`, `tick_frame_facts_transfer`
`tickFrameFactsTransfer`, `A_jr_t` `AJrT`, `cjr_frame_tac` tactic `ax_epi_cjr_frame_tac`,
`t_frame_t` `tFrameT`, `branch_frame_tick_sym` `branchFrameTickSym`, `epi_frame_cjr_tick`
`epiFrameCjrTick`, `A_jr_t_fix` `AJrTFix`, `agree_frame_t` `agreeFrameT`,
`cjr_frame_tick_inv_reaches_ret` `cjrFrameTickInvReachesRet`, `A_fix` `AFix`, `cjr_frame_inv`
`cjrFrameInv`, `cjr_frame_inv_reaches_ret'` `cjrFrameInvReachesRet'`, `wpd_cjr_frame_tick_gen`
`wpdCjrFrameTickGen`, `wpd_cjr_frame_tick` `wpdCjrFrameTick`.  None is in the duplicated-name
table.  Lean-only (file-qualified, `AxEpiCjrFrame.*`): `seipAfterAg`, `seipAfterAgTransfer`,
`seipAtAgTransfer`, `erdOfCjrtBranch`, `cjrtBranchAtEq`, `cjrtLedgerBranch`, `cjrtSeipReaches`,
`cjrtMeipReaches`, `tickAfterMeipAg`, `tickAfterMeipAgTransfer`, the meta `kloopCore` and the
tactic `ax_epi_cjr_frame_kloop`.

**Dropped:** nothing (Rocq 62 definitions/lemmas/records + the Ltac; Lean 62 + the macro,
+ 10 Lean-only helpers + the meta loop and its tactic).  **Not ported:** the `Print Assumptions` block (the
lint's axiom check covers it).  Builds in about 60 s.
-/
import Weak.AxEpiCjrSym
import Weak.AxEpiLedgerTick

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! # 1. Agreement-tracking evaluators -/

/-- Rocq `agree_on`. -/
def agreeOn (A : List Register) (rs rs' : RegFile) : Prop :=
  ∀ r, r ∈ A → rs r = rs' r

theorem agreeOnSym (A : List Register) (rs rs' : RegFile) : agreeOn A rs rs' → agreeOn A rs' rs :=
  fun H r Hr => (H r Hr).symm

theorem agreeOnSet (A : List Register) (rs rs' : RegFile) (r : Register) (v : RegisterType r) :
    agreeOn A rs rs' → agreeOn (r :: A) (rs.set r v) (rs'.set r v) := by
  intro H r0 Hr0
  by_cases he : r0 = r
  · subst he; simp only [RegFile.set_same]
  · rw [RegFile.set_other _ _ _ _ he, RegFile.set_other _ _ _ _ he]
    exact H r0 (List.mem_of_ne_of_mem he Hr0)

theorem agreeOnSetReg (A : List Register) (t t' : ExecSt) (r : Register) (v : RegisterType r) :
    agreeOn A t.regs t'.regs → agreeOn (r :: A) (t.setReg r v).regs (t'.setReg r v).regs :=
  agreeOnSet A t.regs t'.regs r v

/-- Rocq `to_seip_ag`, over `AxEpiLedger.toPin` (deviation 1): stops at a read of EITHER pin. -/
def toPinAg : List Register → SailM Unit → ExecSt → Option (SailM Unit × ExecSt × List Register)
  | _, .pure _, _ => none
  | _, .impure (.error _) _, _ => none
  | A, .impure (.ok o) k, t =>
    match o, k with
    | .regRead r, k =>
      if r = .sig_seip ∨ r = .sig_meip then some (.impure (.ok (.regRead r)) k, t, A)
      else if r ∈ A then toPinAg A (k (t.regs r)) t else none
    | .regWrite r v, k => toPinAg (r :: A) (k PUnit.unit) (t.setReg r v)
    | .instrAnnounce n w, k => if sfAnnB n w then none else toPinAg A (k ()) t
    | .branchAnnounce _ _, k => toPinAg A (k ()) t
    | .cacheOp _, k => toPinAg A (k ()) t
    | .tlbi _, k => toPinAg A (k ()) t
    | .takeException _, k => toPinAg A (k ()) t
    | .returnException _, k => toPinAg A (k ()) t
    | .translationStart _, k => toPinAg A (k ()) t
    | .translationEnd _, k => toPinAg A (k ()) t
    | .cycleCount, k => toPinAg A (k ()) t
    | .message _, k => toPinAg A (k ()) t
    | .getCycleCount, k => toPinAg A (k (0 : Nat)) t
    | _, _ => none

/-- Rocq `erd_ag`. -/
def erdAg (Dr Dw : List Register) :
    List Register → SailM Unit → ExecSt → Option (SailM Unit × ExecSt × List Register)
  | _, .pure _, _ => none
  | _, .impure (.error _) _, _ => none
  | A, .impure (.ok o) k, s =>
    match o, k with
    | .regRead r, k =>
      if r ∈ Dr then (if r ∈ A then erdAg Dr Dw A (k (s.regs r)) s else none) else none
    | .regWrite r v, k =>
      if r ∈ Dw then erdAg Dr Dw (r :: A) (k PUnit.unit) (s.setReg r v) else none
    | .memRead n va req, k =>
      if devAddr req.pa then none else some (.impure (.ok (.memRead n va req)) k, s, A)
    | .memWrite .., _ => none
    | .barrier _, _ => none
    | .cacheOp _, k => erdAg Dr Dw A (k ()) s
    | .tlbi _, k => erdAg Dr Dw A (k ()) s
    | .translationStart _, k => erdAg Dr Dw A (k ()) s
    | .translationEnd _, k => erdAg Dr Dw A (k ()) s
    | .takeException _, k => erdAg Dr Dw A (k ()) s
    | .returnException _, k => erdAg Dr Dw A (k ()) s
    | .cycleCount, k => erdAg Dr Dw A (k ()) s
    | .getCycleCount, k => erdAg Dr Dw A (k (0 : Nat)) s
    | .message _, k => erdAg Dr Dw A (k ()) s
    | .instrAnnounce n w, k => if sfAnnB n w then none else erdAg Dr Dw A (k ()) s
    | .branchAnnounce _ _, k => erdAg Dr Dw A (k ()) s
    | .choose _, _ => none
    | .readRam .., _ => none
    | .writeRam .., _ => none

/-- Rocq `epure_ag`. -/
def epureAg {X : Type} (D : List Register) :
    List Register → SailM X → ExecSt → Option (X × ExecSt × List Register)
  | A, .pure x, s => some (x, s, A)
  | _, .impure (.error _) _, _ => none
  | A, .impure (.ok o) k, s =>
    match o, k with
    | .regRead r, k =>
      if r ∈ D then (if r ∈ A then epureAg D A (k (s.regs r)) s else none) else none
    | .regWrite r v, k => if r ∈ D then epureAg D (r :: A) (k PUnit.unit) (s.setReg r v) else none
    | .memRead .., _ => none
    | .memWrite .., _ => none
    | .barrier _, _ => none
    | .cacheOp _, k => epureAg D A (k ()) s
    | .tlbi _, k => epureAg D A (k ()) s
    | .translationStart _, k => epureAg D A (k ()) s
    | .translationEnd _, k => epureAg D A (k ()) s
    | .takeException _, k => epureAg D A (k ()) s
    | .returnException _, k => epureAg D A (k ()) s
    | .cycleCount, k => epureAg D A (k ()) s
    | .getCycleCount, k => epureAg D A (k (0 : Nat)) s
    | .message _, k => epureAg D A (k ()) s
    | .instrAnnounce n w, k => if sfAnnB n w then none else epureAg D A (k ()) s
    | .branchAnnounce _ _, k => epureAg D A (k ()) s
    | .choose _, _ => none
    | .readRam .., _ => none
    | .writeRam .., _ => none

/-- Rocq `to_seip_ag_sound` (over `AxEpiLedger.toPin`). -/
theorem toPinAgSound (m : SailM Unit) :
    ∀ (A : List Register) (t t' : ExecSt) (m0 : SailM Unit) (t1 : ExecSt) (A1 : List Register),
      toPinAg A m t = some (m0, t1, A1) → agreeOn A t.regs t'.regs →
      ∃ t1', AxEpiLedger.toPin m t' = some (m0, t1') ∧ agreeOn A1 t1.regs t1'.regs := by
  induction m with
  | pure x =>
    intro A t t' m0 t1 A1 h
    simp [toPinAg] at h
  | impure call k ih =>
    intro A t t' m0 t1 A1 h hag
    cases call with
    | error e => simp [toPinAg] at h
    | ok o =>
      cases o
      case regRead r =>
        by_cases hr : r = .sig_seip ∨ r = .sig_meip
        · simp only [toPinAg, if_pos hr, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨t', by simp only [AxEpiLedger.toPin, if_pos hr], hag⟩
        · by_cases hA : r ∈ A
          · simp only [toPinAg, if_neg hr, if_pos hA] at h
            obtain ⟨t1', h1, h2⟩ := ih _ A t t' m0 t1 A1 h hag
            refine ⟨t1', ?_, h2⟩
            simp only [AxEpiLedger.toPin, if_neg hr]
            rw [← hag r hA]
            exact h1
          · simp only [toPinAg, if_neg hr, if_neg hA, reduceCtorEq] at h
      case regWrite r v =>
        simp only [toPinAg] at h
        obtain ⟨t1', h1, h2⟩ := ih _ (r :: A) _ (t'.setReg r v) m0 t1 A1 h
          (agreeOnSetReg A t t' r v hag)
        exact ⟨t1', by simp only [AxEpiLedger.toPin]; exact h1, h2⟩
      case instrAnnounce nw w =>
        cases hsw : sfAnnB nw w <;>
          simp only [toPinAg, hsw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
        obtain ⟨t1', h1, h2⟩ := ih _ A t t' m0 t1 A1 h hag
        exact ⟨t1', by simp only [AxEpiLedger.toPin, hsw, Bool.false_eq_true, ↓reduceIte]; exact h1,
          h2⟩
      all_goals first
        | (simp [toPinAg] at h; done)
        | (simp only [toPinAg] at h
           obtain ⟨t1', h1, h2⟩ := ih _ A t t' m0 t1 A1 h hag
           exact ⟨t1', by simp only [AxEpiLedger.toPin]; exact h1, h2⟩)

/-- Rocq `erd_ag_sound`. -/
theorem erdAgSound (Dr Dw : List Register) (m : SailM Unit) :
    ∀ (A : List Register) (t t' : ExecSt) (mf : SailM Unit) (t2 : ExecSt) (A2 : List Register),
      erdAg Dr Dw A m t = some (mf, t2, A2) → agreeOn A t.regs t'.regs →
      ∃ t2', erd Dr Dw m t' = some (mf, t2') ∧ agreeOn A2 t2.regs t2'.regs := by
  induction m with
  | pure x =>
    intro A t t' mf t2 A2 h
    simp [erdAg] at h
  | impure call k ih =>
    intro A t t' mf t2 A2 h hag
    cases call with
    | error e => simp [erdAg] at h
    | ok o =>
      cases o
      case regRead r =>
        by_cases hD : r ∈ Dr
        · by_cases hA : r ∈ A
          · simp only [erdAg, if_pos hD, if_pos hA] at h
            obtain ⟨t2', h1, h2⟩ := ih _ A t t' mf t2 A2 h hag
            refine ⟨t2', ?_, h2⟩
            simp only [erd, if_pos hD]
            rw [← hag r hA]
            exact h1
          · simp only [erdAg, if_pos hD, if_neg hA, reduceCtorEq] at h
        · simp only [erdAg, if_neg hD, reduceCtorEq] at h
      case regWrite r v =>
        by_cases hD : r ∈ Dw
        · simp only [erdAg, if_pos hD] at h
          obtain ⟨t2', h1, h2⟩ := ih _ (r :: A) _ (t'.setReg r v) mf t2 A2 h
            (agreeOnSetReg A t t' r v hag)
          exact ⟨t2', by simp only [erd, if_pos hD]; exact h1, h2⟩
        · simp only [erdAg, if_neg hD, reduceCtorEq] at h
      case memRead n va req =>
        by_cases hd : devAddr req.pa = true
        · simp [erdAg, hd] at h
        · simp only [erdAg, hd, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨t', by simp only [erd, hd, Bool.false_eq_true, ↓reduceIte], hag⟩
      case instrAnnounce nw w =>
        cases hsw : sfAnnB nw w <;>
          simp only [erdAg, hsw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
        obtain ⟨t2', h1, h2⟩ := ih _ A t t' mf t2 A2 h hag
        exact ⟨t2', by simp only [erd, hsw, Bool.false_eq_true, ↓reduceIte]; exact h1, h2⟩
      all_goals first
        | (simp [erdAg] at h; done)
        | (simp only [erdAg] at h
           obtain ⟨t2', h1, h2⟩ := ih _ A t t' mf t2 A2 h hag
           exact ⟨t2', by simp only [erd]; exact h1, h2⟩)

/-- Rocq `epure_ag_sound`. -/
theorem epureAgSound {X : Type} (D : List Register) (m : SailM X) :
    ∀ (A : List Register) (t t' : ExecSt) (x : X) (t3 : ExecSt) (A3 : List Register),
      epureAg D A m t = some (x, t3, A3) → agreeOn A t.regs t'.regs →
      ∃ t3', epure D m t' = some (x, t3') ∧ agreeOn A3 t3.regs t3'.regs := by
  induction m with
  | pure y =>
    intro A t t' x t3 A3 h hag
    simp only [epureAg, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨t', rfl, hag⟩
  | impure call k ih =>
    intro A t t' x t3 A3 h hag
    cases call with
    | error e => simp [epureAg] at h
    | ok o =>
      cases o
      case regRead r =>
        by_cases hD : r ∈ D
        · by_cases hA : r ∈ A
          · simp only [epureAg, if_pos hD, if_pos hA] at h
            obtain ⟨t3', h1, h2⟩ := ih _ A t t' x t3 A3 h hag
            refine ⟨t3', ?_, h2⟩
            simp only [epure, if_pos hD]
            rw [← hag r hA]
            exact h1
          · simp only [epureAg, if_pos hD, if_neg hA, reduceCtorEq] at h
        · simp only [epureAg, if_neg hD, reduceCtorEq] at h
      case regWrite r v =>
        by_cases hD : r ∈ D
        · simp only [epureAg, if_pos hD] at h
          obtain ⟨t3', h1, h2⟩ := ih _ (r :: A) _ (t'.setReg r v) x t3 A3 h
            (agreeOnSetReg A t t' r v hag)
          exact ⟨t3', by simp only [epure, if_pos hD]; exact h1, h2⟩
        · simp only [epureAg, if_neg hD, reduceCtorEq] at h
      case instrAnnounce nw w =>
        cases hsw : sfAnnB nw w <;>
          simp only [epureAg, hsw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
        obtain ⟨t3', h1, h2⟩ := ih _ A t t' x t3 A3 h hag
        exact ⟨t3', by simp only [epure, hsw, Bool.false_eq_true, ↓reduceIte]; exact h1, h2⟩
      all_goals first
        | (simp [epureAg] at h; done)
        | (simp only [epureAg] at h
           obtain ⟨t3', h1, h2⟩ := ih _ A t t' x t3 A3 h hag
           exact ⟨t3', by simp only [epure]; exact h1, h2⟩)

/-! # 2. The tracked ledger and its transfer -/

/-- Rocq `post_local`: `post` only looks at the registers in `P`. -/
def postLocal (P : List Register) (post : RegFile → Bool) : Prop :=
  ∀ rs rs', agreeOn P rs rs' → post rs = post rs'

/-- Rocq `fetch_ok_ag` (deviation 4: the subset test is checked BEFORE `post`). -/
def fetchOkAg (A D : List Register) (base : Int) (vs : List (BitVec 8)) (P : List Register)
    (post : RegFile → Bool) (mf : SailM Unit) (t2 : ExecSt) : Bool :=
  match mf with
  | .impure (.ok (.memRead n _ req)) KK =>
    !devAddr req.pa && (classify req.access_kind).akIfetch &&
    decide (paZ req.pa = base) && decide (vs.length = n) &&
    match epureAg D A (KK (.Ok (wordOfBytes n vs, none))) t2 with
    | some (_, t3, A3) => P.all (fun r => decide (r ∈ A3)) && post t3.regs
    | none => false
  | _ => false

/-- Rocq `branch_ok_ag`. -/
def branchOkAg (A Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (P : List Register) (post : RegFile → Bool) (m : SailM Unit) (t1 : ExecSt) : Bool :=
  match erdAg Dr Dw A m t1 with
  | some (mf, t2, A2) => fetchOkAg A2 D base vs P post mf t2
  | none => false

/-- (Lean-only) The tracked `AxEpiLedger.seipAfter`. -/
def AxEpiCjrFrame.seipAfterAg (A : List Register) (m0 : SailM Unit) (t0 : ExecSt)
    (v' : BitVec 1) : Bool :=
  match toPinAg A (AxEpiLedger.ansMeip m0 v') t0 with
  | some (m1, _, _) => isSeipNode m1
  | none => false

/-- Rocq `seip_at_ag` (the two-pin walk of `seipAt` / `seipAtTick`, deviation 1). -/
noncomputable def seipAtAg (A : List Register) (tick : Bool) (t : ExecSt) : Bool :=
  match toPinAg A (riscvStep tick) t with
  | some (m0, t0, A0) =>
    AxEpiLedger.isMeipNode m0 && AxEpiCjrFrame.seipAfterAg A0 m0 t0 0#1 &&
      AxEpiCjrFrame.seipAfterAg A0 m0 t0 1#1
  | none => false

/-- Rocq `branch_at_ag` (answers `v'` of `sig_meip`, `v` of `sig_seip`). -/
noncomputable def branchAtAg (A Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (P : List Register) (post : RegFile → Bool) (t : ExecSt) (v' v : BitVec 1) : Bool :=
  match toPinAg A (riscvStep false) t with
  | some (m0, t0, A0) =>
    match toPinAg A0 (AxEpiLedger.ansMeip m0 v') t0 with
    | some (m1, t1, A1) => branchOkAg A1 Dr Dw D base vs P post (ansSeip m1 v) t1
    | none => false
  | none => false

/-- THE TRACKED LEDGER (tick = false). -/
structure CjrFrameFacts (t : ExecSt) (A Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (P : List Register) (post : RegFile → Bool) : Prop where
  cfSeipDr : decide (Register.sig_seip ∈ Dr) = false
  cfMeipDr : decide (Register.sig_meip ∈ Dr) = false
  cfSeipD : decide (Register.sig_seip ∈ D) = false
  cfMeipD : decide (Register.sig_meip ∈ D) = false
  cfHead : isSeipNode (riscvStep false) = false
  cfToSeip : seipAtAg A false t = true
  cfBranch00 : branchAtAg A Dr Dw D base vs P post t 0#1 0#1 = true
  cfBranch01 : branchAtAg A Dr Dw D base vs P post t 0#1 1#1 = true
  cfBranch10 : branchAtAg A Dr Dw D base vs P post t 1#1 0#1 = true
  cfBranch11 : branchAtAg A Dr Dw D base vs P post t 1#1 1#1 = true

theorem fetchOkAgTransfer (A D : List Register) (base : Int) (vs : List (BitVec 8))
    (P : List Register) (post : RegFile → Bool) (mf : SailM Unit) (t2 t2' : ExecSt) :
    postLocal P post → fetchOkAg A D base vs P post mf t2 = true →
    agreeOn A t2.regs t2'.regs → fetchOk D base vs post mf t2' = true := by
  intro Hpl H Hag
  cases mf with
  | pure _ => exact absurd H Bool.false_ne_true
  | impure call KK =>
    cases call with
    | error _ => exact absurd H Bool.false_ne_true
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [fetchOkAg, Bool.and_eq_true] at H
        obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := H
        cases he : epureAg D A (KK (.Ok (wordOfBytes n vs, none))) t2 with
        | none => rw [he] at h5; exact absurd h5 Bool.false_ne_true
        | some p =>
          obtain ⟨x, t3, A3⟩ := p
          rw [he] at h5
          simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h5
          obtain ⟨hP, hp⟩ := h5
          obtain ⟨t3', he', hag3⟩ := epureAgSound D _ A t2 t2' x t3 A3 he Hag
          simp only [fetchOk, he', Bool.and_eq_true]
          refine ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, ?_⟩
          rw [← Hpl _ _ (fun r hr => hag3 r (hP r hr))]
          exact hp
      all_goals exact absurd H Bool.false_ne_true

theorem branchOkAgTransfer (A Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (P : List Register) (post : RegFile → Bool) (m : SailM Unit) (t1 t1' : ExecSt) :
    postLocal P post → branchOkAg A Dr Dw D base vs P post m t1 = true →
    agreeOn A t1.regs t1'.regs → branchOk Dr Dw D base vs post m t1' = true := by
  intro Hpl H Hag
  unfold branchOkAg at H
  unfold branchOk
  cases he : erdAg Dr Dw A m t1 with
  | none => rw [he] at H; exact absurd H Bool.false_ne_true
  | some p =>
    obtain ⟨mf, t2, A2⟩ := p
    rw [he] at H
    obtain ⟨t2', he', hag2⟩ := erdAgSound Dr Dw m A t1 t1' mf t2 A2 he Hag
    rw [he']
    exact fetchOkAgTransfer A2 D base vs P post mf t2 t2' Hpl H hag2

/-- (Lean-only) `AxEpiCjrFrame.seipAfterAg` transfers to `AxEpiLedger.seipAfter`. -/
theorem AxEpiCjrFrame.seipAfterAgTransfer (A : List Register) (m0 : SailM Unit)
    (t0 t0' : ExecSt) (v' : BitVec 1) :
    AxEpiCjrFrame.seipAfterAg A m0 t0 v' = true → agreeOn A t0.regs t0'.regs →
    AxEpiLedger.seipAfter m0 t0' v' = true := by
  intro H Hag
  unfold AxEpiCjrFrame.seipAfterAg at H
  unfold AxEpiLedger.seipAfter
  cases he : toPinAg A (AxEpiLedger.ansMeip m0 v') t0 with
  | none => rw [he] at H; exact absurd H Bool.false_ne_true
  | some p =>
    obtain ⟨m1, t1, A1⟩ := p
    rw [he] at H
    obtain ⟨t1', he', -⟩ := toPinAgSound _ A t0 t0' m1 t1 A1 he Hag
    rw [he']
    exact H

/-- (Lean-only) The common transfer of the two-pin boundary walk: from the tracked walk of
`riscvStep tick` at `t`, the untracked one at `t'` (and the agreement at the meip node). -/
theorem AxEpiCjrFrame.seipAtAgTransfer (A : List Register) (tick : Bool) (t t' : ExecSt)
    (H : seipAtAg A tick t = true) (Hag : agreeOn A t.regs t'.regs) :
    ∃ m0 t0 A0 t0', toPinAg A (riscvStep tick) t = some (m0, t0, A0) ∧
      AxEpiLedger.toPin (riscvStep tick) t' = some (m0, t0') ∧ agreeOn A0 t0.regs t0'.regs ∧
      (AxEpiLedger.isMeipNode m0 && AxEpiLedger.seipAfter m0 t0' 0#1 &&
        AxEpiLedger.seipAfter m0 t0' 1#1) = true := by
  unfold seipAtAg at H
  cases hts : toPinAg A (riscvStep tick) t with
  | none => rw [hts] at H; exact absurd H Bool.false_ne_true
  | some p =>
    obtain ⟨m0, t0, A0⟩ := p
    rw [hts] at H
    simp only [Bool.and_eq_true] at H
    obtain ⟨⟨hm, h0⟩, h1⟩ := H
    obtain ⟨t0', hts', hag0⟩ := toPinAgSound _ A t t' m0 t0 A0 hts Hag
    refine ⟨m0, t0, A0, t0', rfl, hts', hag0, ?_⟩
    simp only [Bool.and_eq_true]
    exact ⟨⟨hm, AxEpiCjrFrame.seipAfterAgTransfer A0 m0 t0 t0' 0#1 h0 hag0⟩,
      AxEpiCjrFrame.seipAfterAgTransfer A0 m0 t0 t0' 1#1 h1 hag0⟩

theorem frameFactsTransfer (t : ExecSt) (A Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (P : List Register) (post : RegFile → Bool) (t' : ExecSt) :
    CjrFrameFacts t A Dr Dw D base vs P post → postLocal P post →
    agreeOn A t.regs t'.regs → AxEpiModelFacts t' Dr Dw D base vs post := by
  intro F Hpl Hag
  obtain ⟨m0, t0, A0, t0', hts, hts', hag0, Hs⟩ :=
    AxEpiCjrFrame.seipAtAgTransfer A false t t' F.cfToSeip Hag
  have Hbr : ∀ v' v, branchAtAg A Dr Dw D base vs P post t v' v = true →
      branchAt Dr Dw D base vs post t' v' v = true := by
    intro v' v H
    unfold branchAtAg at H
    rw [hts] at H
    unfold branchAt
    rw [hts']
    simp only [] at H ⊢
    cases h2 : toPinAg A0 (AxEpiLedger.ansMeip m0 v') t0 with
    | none => rw [h2] at H; exact absurd H Bool.false_ne_true
    | some q =>
      obtain ⟨m1, t1, A1⟩ := q
      rw [h2] at H
      obtain ⟨t1', h2', hag1⟩ := toPinAgSound _ A0 t0 t0' m1 t1 A1 h2 hag0
      rw [h2']
      exact branchOkAgTransfer A1 Dr Dw D base vs P post _ t1 t1' Hpl H hag1
  exact {
    lfSeipDr := F.cfSeipDr
    lfMeipDr := F.cfMeipDr
    lfSeipD := F.cfSeipD
    lfMeipD := F.cfMeipD
    lfHead := F.cfHead
    lfToSeip := by unfold seipAt; rw [hts']; exact Hs
    lfBranch00 := Hbr _ _ F.cfBranch00
    lfBranch01 := Hbr _ _ F.cfBranch01
    lfBranch10 := Hbr _ _ F.cfBranch10
    lfBranch11 := Hbr _ _ F.cfBranch11 }

section frameGen
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- GENERIC FRAME: the whole-instruction `wpd` from any `rs` agreeing with the reference `t0`
on the tracked start set `A`. -/
theorem wpdCjrFrameGen (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch) (kk : Nat)
    (t0 : ExecSt) (A Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (P : List Register) (post : RegFile → Bool)
    (F : CjrFrameFacts t0 A Dr Dw D base vs P post) (Hpl : postLocal P post)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk base vs⌝)
    (rs : RegFile) (Hag : agreeOn A rs t0.regs) :
    ⊢ ((∀ s', ⌜RetS cpu post kk s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜AxEpiLedger.ledgerInv ⟨rs, t0.mem, t0.dev⟩ Dr Dw D vs cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) rs none ib, kk⟩ Φ :=
  wpdCjrStepOfLedger i Φ cpu ib kk ⟨rs, t0.mem, t0.dev⟩ _ _ _ _ _ _
    (frameFactsTransfer t0 A Dr Dw D base vs P post ⟨rs, t0.mem, t0.dev⟩ F Hpl
      (agreeOnSym _ _ _ Hag)) Hgd

end frameGen

/-! # 3. The c.jr instance (tick = false), every `ra` -/

/-- Rocq `A_jr`: the upward-exposed reads of `riscvStep false` for c.jr at `tWithRa ra`, both
pins excluded (deviation 3; found with a tracer, checked by `epiFrameCjr`). -/
def AJr : List Register :=
  [.minstret, .x1, .mseccfg, .elp, .htif_tohost_base, .pmpaddr_n, .pmpcfg_n, .pma_regions, .PC,
   .mstatus, .mie, .mip, .mideleg, .misa, .hart_state, .minstretcfg, .mcountinhibit,
   .cur_privilege]

/-- Rocq `P_pc`. -/
def PPc : List Register := [.PC]

theorem postRaSymLocal (ra : BitVec 64) : postLocal PPc (postRaSym ra) := by
  intro rs rs' H
  unfold postRaSym
  rw [H .PC (List.mem_singleton.2 rfl)]

/-- Rocq `t_frame`: the reference state, `minstret` and `mip` left symbolic. -/
def tFrame (ra mi mp : BitVec 64) : ExecSt :=
  ⟨(((probeRegs pcJr).set .x1 ra).set .minstret mi).set .mip mp, probeMem, testDevs⟩

open Lean Elab Tactic Meta in
/-- (Lean-only) Close every remaining post leaf `E a b` of the goal's kernel spine
(`AxEpiCjrSym.kspineGoal`): case on it, the `false` arm absurd by `he b : E b b = true` (the
kernel checking `a ≡ b`), the `true` arm continued, until the spine is `true`. -/
partial def AxEpiCjrFrame.kloopCore (g : MVarId) (he : Lean.Expr) : MetaM Unit := do
  let (g', leaf) ← AxEpiCjrSym.kspineGoal g
  g'.withContext do
    let gT ← instantiateMVars (← g'.getType)
    let some (_, W, _) := gT.eq? | throwError "kloop: the goal is not an equation"
    if W.isConstOf ``Bool.true then
      g'.assign (← mkEqRefl W)
      return
    let args := leaf.getAppArgs
    unless args.size ≥ 2 do throwError m!"kloop: unexpected leaf {leaf}"
    let b := args[args.size - 1]!
    let mk (c : Lean.Expr) : Lean.Expr := gT.replace fun e => if e == leaf then some c else none
    let bTy := mkConst ``Bool
    let motive ← withLocalDeclD `b bTy fun bb => do
      mkLambdaFVars #[bb] (← mkArrow (← mkEq leaf bb) (mk bb))
    let ff := mkConst ``Bool.false
    let tt := mkConst ``Bool.true
    let mF ← mkFreshExprSyntheticOpaqueMVar (← mkArrow (← mkEq leaf ff) (mk ff))
    let mT ← mkFreshExprSyntheticOpaqueMVar (← mkArrow (← mkEq leaf tt) (mk tt))
    let pf := mkApp (mkAppN (mkConst ``Bool.rec [Level.zero]) #[motive, mF, mT, leaf])
      (← mkEqRefl leaf)
    g'.assign pf
    let (hF, gF) ← mF.mvarId!.intro `h
    gF.withContext do
      let h := mkFVar hF
      let e1 := mkApp4 (mkConst ``Eq.symm [Level.one]) bTy leaf ff h
      let e2 := mkAppN (mkConst ``Eq.trans [Level.one]) #[bTy, ff, leaf, tt, e1, mkApp he b]
      let pfF := mkApp (mkConst ``Bool.false_ne_true) e2
      gF.assign (mkApp2 (mkConst ``False.elim [Level.zero]) (← gF.getType) pfF)
    let (_, gT') ← mT.mvarId!.intro `h
    AxEpiCjrFrame.kloopCore gT' he

open Lean Elab Tactic Meta in
/-- (Lean-only) `AxEpiCjrFrame.kloopCore` on the main goal. -/
elab "ax_epi_cjr_frame_kloop " t:term : tactic => do
  let g ← getMainGoal
  let he ← g.withContext (elabTerm t none)
  AxEpiCjrFrame.kloopCore g he
  replaceMainGoal []

set_option maxHeartbeats 1000000 in
theorem branchFrameSym (ra mi mp : BitVec 64) (v' v : BitVec 1) :
    branchAtAg AJr AxEpiProbe.drNopin DwAll DPost (pcJr : Int) cjrVs4 PPc (postRaSym ra)
      (tFrame ra mi mp) v' v = true := by
  unfold branchAtAg riscvStep Functions.try_step Functions.run_hart_active Functions.execute
  rw [executeJALRSEq]
  unfold postRaSym jalrTarget
  rw [tgtImm0]
  have HE : ∀ x, pcEqb x x = true := pcEqbRefl
  generalize pcEqb = E at HE ⊢
  generalize hA0 : b0S = A0
  generalize b1S = A1
  rcases bv1Cases v' with rfl | rfl <;> rcases bv1Cases v with rfl | rfl
  all_goals
    ax_epi_cjr_sym_kcases h0
    · exfalso; rw [← hA0, AxEpiCjrSym.b0SAligned] at h0; exact Bool.noConfusion h0
    · ax_epi_cjr_sym_kcases h1
      all_goals ax_epi_cjr_sym_kclose HE

theorem epiFrameCjr (ra mi mp : BitVec 64) :
    CjrFrameFacts (tFrame ra mi mp) AJr AxEpiProbe.drNopin DwAll DPost (pcJr : Int) cjrVs4 PPc
      (postRaSym ra) where
  cfSeipDr := by decide +kernel
  cfMeipDr := by decide +kernel
  cfSeipD := by decide +kernel
  cfMeipD := by decide +kernel
  cfHead := by decide +kernel
  cfToSeip := by ax_epi_ledger_krfl
  cfBranch00 := branchFrameSym ra mi mp _ _
  cfBranch01 := branchFrameSym ra mi mp _ _
  cfBranch10 := branchFrameSym ra mi mp _ _
  cfBranch11 := branchFrameSym ra mi mp _ _

/-- Rocq `A_jr_fix`: what the CALLER must match, `AJr` minus the two symbolic counters. -/
def AJrFix : List Register :=
  AJr.filter fun r => !decide (r = .minstret) && !decide (r = .mip)

theorem agreeFrame (A : List Register) (ra : BitVec 64) (rs : RegFile) :
    agreeOn (A.filter fun r => !decide (r = .minstret) && !decide (r = .mip)) rs
      ((probeRegs pcJr).set .x1 ra) →
    agreeOn A rs (tFrame ra (rs .minstret) (rs .mip)).regs := by
  intro H r Hr
  show rs r = ((((probeRegs pcJr).set .x1 ra).set .minstret (rs .minstret)).set .mip (rs .mip)) r
  by_cases h1 : r = .mip
  · subst h1; simp only [RegFile.set_same]
  · rw [RegFile.set_other _ _ _ _ h1]
    by_cases h2 : r = .minstret
    · subst h2; simp only [RegFile.set_same]
    · rw [RegFile.set_other _ _ _ _ h2]
      exact H r (List.mem_filter.2 ⟨Hr, by simp [h1, h2]⟩)

/-- SANITY: the row-end set at the real start state reaches `.pure ()`. -/
theorem cjrFrameInvReachesRet (ra : BitVec 64) (rs : RegFile) (cpu : CPU) (kk : Nat)
    (s1 : Athread) :
    agreeOn AJrFix rs ((probeRegs pcJr).set .x1 ra) →
    AxEpiLedger.ledgerInv ⟨rs, probeMem, testDevs⟩ AxEpiProbe.drNopin DwAll DPost cjrVs4 cpu kk
      s1 →
    ∃ t0 s', aeqv s1 t0 ∧ rtc (AxEpiLedger.ledgerStep cpu cjrVs4) t0 s' ∧
      RetS cpu (postRaSym ra) kk s' := by
  intro Hag H
  exact ledgerInvReachesRet _ _ _ _ (pcJr : Int) _ _ cpu kk s1
    (frameFactsTransfer _ _ _ _ _ _ _ _ _ ⟨rs, probeMem, testDevs⟩ (epiFrameCjr ra _ _)
      (postRaSymLocal ra) (agreeOnSym _ _ _ (agreeFrame AJr ra rs Hag))) H

section frameCjr
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- THE FRAMED c.jr `wpd` (tick = false): from any register file agreeing with
`(probeRegs pcJr).set .x1 ra` on `AJrFix`. -/
theorem wpdCjrFrame (ra : BitVec 64) (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
    (ib : Ibch) (kk : Nat)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk (pcJr : Int) cjrVs4⌝)
    (rs : RegFile) (Hag : agreeOn AJrFix rs ((probeRegs pcJr).set .x1 ra)) :
    ⊢ ((∀ s', ⌜RetS cpu (postRaSym ra) kk s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜AxEpiLedger.ledgerInv ⟨rs, probeMem, testDevs⟩ AxEpiProbe.drNopin DwAll DPost cjrVs4
            cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) rs none ib, kk⟩ Φ :=
  wpdCjrFrameGen i Φ cpu ib kk (tFrame ra _ _) _ _ _ _ _ _ _ _ (epiFrameCjr ra _ _)
    (postRaSymLocal ra) Hgd rs (agreeFrame AJr ra rs Hag)

end frameCjr

/-! # 4. tick = true: the c.jr ledger with `tick_clock`'s second pin reads

After the fetch, the continuation fed `vs` runs (`toPin`) to the tick's pin reads and, per
answer, `epure`s to `.pure ()` with `post` (`tickPostOk`).  No data load. -/

/-- Rocq `cjrt_fetch_ok`. -/
def cjrtFetchOk (D : List Register) (base : Int) (vs : List (BitVec 8)) (post : RegFile → Prop)
    (mf : SailM Unit) (t2 : ExecSt) : Prop :=
  match mf with
  | .impure (.ok (.memRead n _ req)) KK =>
    devAddr req.pa = false ∧ (classify req.access_kind).akIfetch = true ∧
    paZ req.pa = base ∧ vs.length = n ∧
    tickPostOk D post (KK (.Ok (wordOfBytes n vs, none))) t2
  | _ => False

/-- Rocq `cjrt_branch_ok`. -/
def cjrtBranchOk (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (post : RegFile → Prop) (m : SailM Unit) (t1 : ExecSt) : Prop :=
  match erd Dr Dw m t1 with
  | some (mf, t2) => cjrtFetchOk D base vs post mf t2
  | none => False

/-- Rocq `cjrt_branch_at` (answers `v'` of `sig_meip`, `v` of `sig_seip`). -/
noncomputable def cjrtBranchAt (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (post : RegFile → Prop) (t : ExecSt) (v' v : BitVec 1) : Prop :=
  match AxEpiLedger.toPin (riscvStep true) t with
  | some (m0, t0) =>
    match AxEpiLedger.toPin (AxEpiLedger.ansMeip m0 v') t0 with
    | some (m1, t1) => cjrtBranchOk Dr Dw D base vs post (ansSeip m1 v) t1
    | none => False
  | none => False

/-- Rocq `AxCjrTickFacts`. -/
structure AxCjrTickFacts (t : ExecSt) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (post : RegFile → Prop) : Prop where
  ctSeipDr : decide (Register.sig_seip ∈ Dr) = false
  ctMeipDr : decide (Register.sig_meip ∈ Dr) = false
  ctSeipD : decide (Register.sig_seip ∈ D) = false
  ctMeipD : decide (Register.sig_meip ∈ D) = false
  ctToSeip : seipAtTick t = true
  ctBranch00 : cjrtBranchAt Dr Dw D base vs post t 0#1 0#1
  ctBranch01 : cjrtBranchAt Dr Dw D base vs post t 0#1 1#1
  ctBranch10 : cjrtBranchAt Dr Dw D base vs post t 1#1 0#1
  ctBranch11 : cjrtBranchAt Dr Dw D base vs post t 1#1 1#1

theorem cjrtBranchOkNode (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (post : RegFile → Prop) (m : SailM Unit) (t1 : ExecSt) :
    cjrtBranchOk Dr Dw D base vs post m t1 →
    ∃ (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (t2 : ExecSt),
      erd Dr Dw m t1 = some (.impure (.ok (.memRead n va req)) KK, t2) ∧
      devAddr req.pa = false ∧ (classify req.access_kind).akIfetch = true ∧
      paZ req.pa = base ∧ vs.length = n ∧
      tickPostOk D post (KK (.Ok (wordOfBytes n vs, none))) t2 := by
  intro H
  unfold cjrtBranchOk at H
  cases he : erd Dr Dw m t1 with
  | none => rw [he] at H; exact H.elim
  | some p =>
    obtain ⟨mf, t2⟩ := p
    rw [he] at H
    cases mf with
    | pure _ => exact H.elim
    | impure call KK =>
      cases call with
      | error _ => exact H.elim
      | ok o =>
        cases o
        case memRead n va req =>
          obtain ⟨h1, h2, h3, h4, h5⟩ := H
          exact ⟨n, va, req, KK, t2, rfl, h1, h2, h3, h4, h5⟩
        all_goals exact H.elim

/-- (Lean-only) `cjrtBranchOk` gives the `erd` exit. -/
theorem AxEpiCjrFrame.erdOfCjrtBranch (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (post : RegFile → Prop) (m : SailM Unit) (t1 : ExecSt)
    (Hb : cjrtBranchOk Dr Dw D base vs post m t1) :
    ∃ q t2, erd Dr Dw m t1 = some (q, t2) := by
  obtain ⟨_, _, _, _, _, He, _⟩ := cjrtBranchOkNode _ _ _ _ _ _ _ _ Hb
  exact ⟨_, _, He⟩

/-- (Lean-only) `cjrtBranchAt` at the two computed pin nodes. -/
theorem AxEpiCjrFrame.cjrtBranchAtEq (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (post : RegFile → Prop) (t : ExecSt)
    (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt) (v' : BitVec 1)
    (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt) (v : BitVec 1)
    (Hts : AxEpiLedger.toPin (riscvStep true) t
      = some (.impure (.ok (.regRead Register.sig_meip)) km, t0))
    (Hts1 : AxEpiLedger.toPin (km v') t0
      = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1)) :
    cjrtBranchAt Dr Dw D base vs post t v' v = cjrtBranchOk Dr Dw D base vs post (k0 v) t1 := by
  unfold cjrtBranchAt
  rw [Hts]
  simp only []
  rw [AxEpiLedger.ansMeipNode, Hts1]
  simp only []
  rw [AxEpiLedger.ansSeipNode]

/-- (Lean-only) Every branch of a certified tick c.jr ledger. -/
theorem AxEpiCjrFrame.cjrtLedgerBranch (t : ExecSt) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (post : RegFile → Prop)
    (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt) (v' : BitVec 1)
    (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt) :
    AxCjrTickFacts t Dr Dw D base vs post →
    AxEpiLedger.toPin (riscvStep true) t
      = some (.impure (.ok (.regRead Register.sig_meip)) km, t0) →
    AxEpiLedger.toPin (km v') t0
      = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) →
    ∀ v, cjrtBranchOk Dr Dw D base vs post (k0 v) t1 := by
  intro L Hts Hts1 v
  rw [← AxEpiCjrFrame.cjrtBranchAtEq Dr Dw D base vs post t km t0 v' k0 t1 v Hts Hts1]
  rcases bv1Cases v' with rfl | rfl <;> rcases bv1Cases v with rfl | rfl
  · exact L.ctBranch00
  · exact L.ctBranch01
  · exact L.ctBranch10
  · exact L.ctBranch11

/-- Rocq `ledger_cjrt_inv`: the row-end invariant (tick = true) — the boundary split sets, or
the post-fetch tail's split sets (`tickTailInv`, at the SAME position `kk`, deviation 2). -/
def ledgerCjrtInv (t : ExecSt) (Dr Dw D : List Register) (vs : List (BitVec 8)) (cpu : CPU)
    (kk : Nat) (s1 : Athread) : Prop :=
  ∃ (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt) (ib0 : Ibch),
    AxEpiLedger.toPin (riscvStep true) t
      = some (.impure (.ok (.regRead Register.sig_meip)) km, t0) ∧
    (Pseip (AxEpiLedger.meipNode cpu km t0.regs ib0 kk) (AxEpiLedger.seipExit cpu km t0 kk) s1 ∨
     ∃ (v' : BitVec 1) (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt)
       (ib1 : Ibch),
       AxEpiLedger.toPin (km v') t0 = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) ∧
       (Pseip (seipNode cpu k0 t1.regs ib1 kk) (erdExit Dr Dw cpu k0 t1 kk) s1 ∨
        ∃ (v : BitVec 1) (n va : Nat)
          (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
          (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (t2 : ExecSt),
          erd Dr Dw (k0 v) t1 = some (.impure (.ok (.memRead n va req)) KK, t2) ∧
          tickTailInv D cpu (KK (.Ok (wordOfBytes n vs, none))) t2 kk s1))

theorem cjrtFetchReaches (D : List Register) (post : RegFile → Prop) (cpu : CPU)
    (vs : List (BitVec 8)) (kk n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (t2 : ExecSt)
    (ib2 : Ibch) :
    Register.sig_seip ∉ D → Register.sig_meip ∉ D →
    tickPostOk D post (KK (.Ok (wordOfBytes n vs, none))) t2 →
    ∃ s', rtc (ldStep cpu vs)
        ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) t2.regs none ib2, kk⟩ s' ∧
      RetP cpu post kk s' := by
  intro HD HDm Hok
  obtain ⟨s', Hr, Hs'⟩ := tailReachesStart D post cpu vs _ t2 ib2 kk HD HDm Hok
  exact ⟨s', rtc_l (.inl (.inr (.inr (.inl ⟨n, va, req, KK, t2.regs, ib2, ib2, kk, rfl, rfl⟩))))
    Hr, Hs'⟩

theorem cjrtBranchReaches (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (post : RegFile → Prop) (cpu : CPU) (kk : Nat) (m : SailM Unit) (t1 : ExecSt) (ib : Ibch) :
    Register.sig_seip ∉ Dr → Register.sig_meip ∉ Dr →
    Register.sig_seip ∉ D → Register.sig_meip ∉ D →
    cjrtBranchOk Dr Dw D base vs post m t1 →
    ∃ s', rtc (ldStep cpu vs) ⟨.PHart cpu m t1.regs none ib, kk⟩ s' ∧ RetP cpu post kk s' := by
  intro HDr HDrm HD HDm Hb
  obtain ⟨n, va, req, KK, t2, He, -, -, -, -, Hok⟩ := cjrtBranchOkNode _ _ _ _ _ _ _ _ Hb
  obtain ⟨ib2, -, -, Hr⟩ := erdGstep Dr Dw m HDr HDrm t1 ib _ _ He cpu kk
  obtain ⟨s', Hr', Hs'⟩ := cjrtFetchReaches D post cpu vs kk n va req KK t2 ib2 HD HDm Hok
  exact ⟨s', rtc_transitive (rtcGstepLdStep cpu vs _ _ Hr) Hr', Hs'⟩

/-- (Lean-only) From the boundary `sig_seip` node of a certified tick c.jr branch, `RetP`. -/
theorem AxEpiCjrFrame.cjrtSeipReaches (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (post : RegFile → Prop) (cpu : CPU) (kk : Nat)
    (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt) (ib1 : Ibch)
    (HDr : Register.sig_seip ∉ Dr) (HDrm : Register.sig_meip ∉ Dr)
    (HD : Register.sig_seip ∉ D) (HDm : Register.sig_meip ∉ D)
    (Hb : ∀ v, cjrtBranchOk Dr Dw D base vs post (k0 v) t1) :
    ∃ s', rtc (ldStep cpu vs) (seipNode cpu k0 t1.regs ib1 kk) s' ∧ RetP cpu post kk s' := by
  obtain ⟨s', Hr, Hs'⟩ := cjrtBranchReaches Dr Dw D base vs post cpu kk (k0 0#1) t1
    (ibRd ib1 Register.sig_seip) HDr HDrm HD HDm (Hb _)
  exact ⟨s', rtc_l (.inl (.inr (.inl ⟨k0, t1.regs, ib1, 0#1, _, kk, rfl, rfl⟩))) Hr, Hs'⟩

/-- (Lean-only) From the boundary `sig_meip` node of a certified tick c.jr ledger, `RetP`. -/
theorem AxEpiCjrFrame.cjrtMeipReaches (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (post : RegFile → Prop) (cpu : CPU) (kk : Nat)
    (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt) (ib0 : Ibch)
    (HDr : Register.sig_seip ∉ Dr) (HDrm : Register.sig_meip ∉ Dr)
    (HD : Register.sig_seip ∉ D) (HDm : Register.sig_meip ∉ D)
    (H : ∀ v', ∃ (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt),
      AxEpiLedger.toPin (km v') t0
        = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) ∧
      ∀ v, cjrtBranchOk Dr Dw D base vs post (k0 v) t1) :
    ∃ s', rtc (ldStep cpu vs) (AxEpiLedger.meipNode cpu km t0.regs ib0 kk) s' ∧
      RetP cpu post kk s' := by
  obtain ⟨k0, t1, Hts1, Hb⟩ := H 0#1
  obtain ⟨ib1, Hr⟩ := AxEpiLedger.toPinGstep _ t0 (ibRd ib0 Register.sig_meip) _ _ Hts1 cpu kk
  obtain ⟨s', Hr', Hs'⟩ := AxEpiCjrFrame.cjrtSeipReaches Dr Dw D base vs post cpu kk k0 t1 ib1
    HDr HDrm HD HDm Hb
  exact ⟨s', rtc_l (.inl (.inr (.inr (.inr ⟨km, t0.regs, ib0, 0#1, _, kk, rfl, rfl⟩))))
    (rtc_transitive (rtcGstepLdStep cpu vs _ _ Hr) Hr'), Hs'⟩

/-- SANITY (non-vacuity of the tick row-end premise). -/
theorem ledgerCjrtInvReachesRet (t : ExecSt) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (post : RegFile → Prop) (cpu : CPU) (kk : Nat) (s1 : Athread) :
    AxCjrTickFacts t Dr Dw D base vs post →
    ledgerCjrtInv t Dr Dw D vs cpu kk s1 →
    ∃ t0 s', aeqv s1 t0 ∧ rtc (ldStep cpu vs) t0 s' ∧ RetP cpu post kk s' := by
  intro L ⟨km, t0, ib0, Hts, Hc⟩
  have HDr := of_decide_eq_false L.ctSeipDr
  have HDrm := of_decide_eq_false L.ctMeipDr
  have HD := of_decide_eq_false L.ctSeipD
  have HDm := of_decide_eq_false L.ctMeipD
  have Hall : ∀ v', ∃ (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt),
      AxEpiLedger.toPin (km v') t0
        = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) ∧
      ∀ v, cjrtBranchOk Dr Dw D base vs post (k0 v) t1 := by
    intro v'
    obtain ⟨k0, t1, Hts1⟩ := AxEpiLedgerTick.seipAtTickNext t km t0 L.ctToSeip Hts v'
    exact ⟨k0, t1, Hts1,
      AxEpiCjrFrame.cjrtLedgerBranch t Dr Dw D base vs post km t0 v' k0 t1 L Hts Hts1⟩
  rcases Hc with Hc | ⟨v', k0, t1, ib1, Hts1, Hc⟩
  · obtain ⟨sm, Hrm, Hsm⟩ :=
      AxEpiCjrFrame.cjrtMeipReaches Dr Dw D base vs post cpu kk km t0 ib0 HDr HDrm HD HDm Hall
    rcases Hc with ⟨t', Ha, Htc⟩ | Ha | ⟨q, ⟨v', k0, t1, ib1, Hts1, rfl⟩, t', Ha, Htc⟩
    · exact ⟨t', sm, Ha, rtc_transitive (rtcGstepLdStep cpu vs _ _ (tc_rtc Htc)) Hrm, Hsm⟩
    · exact ⟨_, sm, Ha, Hrm, Hsm⟩
    · have Hb := AxEpiCjrFrame.cjrtLedgerBranch t Dr Dw D base vs post km t0 v' k0 t1 L Hts Hts1
      obtain ⟨s', Hr, Hs'⟩ := AxEpiCjrFrame.cjrtSeipReaches Dr Dw D base vs post cpu kk k0 t1
        ib1 HDr HDrm HD HDm Hb
      exact ⟨t', s', Ha, rtc_transitive (rtcGstepLdStep cpu vs _ _ (tc_rtc Htc)) Hr, Hs'⟩
  · have Hb := AxEpiCjrFrame.cjrtLedgerBranch t Dr Dw D base vs post km t0 v' k0 t1 L Hts Hts1
    obtain ⟨ss, Hrs, Hss⟩ := AxEpiCjrFrame.cjrtSeipReaches Dr Dw D base vs post cpu kk k0 t1
      ib1 HDr HDrm HD HDm Hb
    rcases Hc with Hc | ⟨v, n, va, req, KK, t2, He, Htail⟩
    · rcases Hc with ⟨t', Ha, Htc⟩ | Ha | ⟨q, ⟨v, qm, t2, ib2, He, rfl, -⟩, t', Ha, Htc⟩
      · exact ⟨t', ss, Ha, rtc_transitive (rtcGstepLdStep cpu vs _ _ (tc_rtc Htc)) Hrs, Hss⟩
      · exact ⟨_, ss, Ha, Hrs, Hss⟩
      · obtain ⟨n, va, req, KK, t2', He', -, -, -, -, Hok⟩ :=
          cjrtBranchOkNode _ _ _ _ _ _ _ _ (Hb v)
        rw [He, Option.some.injEq, Prod.mk.injEq] at He'
        obtain ⟨rfl, rfl⟩ := He'
        obtain ⟨s', Hr, Hs'⟩ := cjrtFetchReaches D post cpu vs kk n va req KK t2 ib2 HD HDm Hok
        exact ⟨t', s', Ha, rtc_transitive (rtcGstepLdStep cpu vs _ _ (tc_rtc Htc)) Hr, Hs'⟩
    · obtain ⟨n', va', req', KK', t2', He', -, -, -, -, Hok⟩ :=
        cjrtBranchOkNode _ _ _ _ _ _ _ _ (Hb v)
      rw [He, Option.some.injEq, Prod.mk.injEq] at He'
      obtain ⟨heq, rfl⟩ := He'
      cases heq
      exact tailReachesInv D post cpu vs _ t2 kk s1 HD HDm Hok Htail

section cjrtLedger
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- THE WHOLE-INSTRUCTION `wpd` OF c.jr AT `riscvStep true`, from any register file agreeing
with the ledger state's off the pins: boundary splits → fetch → `wpdTickTail` → `.pure ()`. -/
theorem wpdCjrStepOfLedgerTick (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch)
    (kk : Nat) (t : ExecSt) (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (post : RegFile → Prop) (L : AxCjrTickFacts t Dr Dw D base vs post)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk base vs⌝)
    (rs : RegFile) (Hag0 : regsAgree AxRunClose.pinReg t.regs rs) :
    ⊢ ((∀ s', ⌜RetP cpu post kk s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1, ⌜ledgerCjrtInv t Dr Dw D vs cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep true) rs none ib, kk⟩ Φ := by
  have HDr := of_decide_eq_false L.ctSeipDr
  have HDrm := of_decide_eq_false L.ctMeipDr
  have HD := of_decide_eq_false L.ctSeipD
  have HDm := of_decide_eq_false L.ctMeipD
  obtain ⟨km, t0, Hts⟩ := AxEpiLedgerTick.seipAtTickSpec t L.ctToSeip
  have Hnext := AxEpiLedgerTick.seipAtTickNext t km t0 L.ctToSeip Hts
  obtain ⟨ib0, Hr0⟩ := AxEpiLedger.toPinGstep _ t ib _ _ Hts cpu kk
  iintro R
  iapply (wpdOfSeipSplitRtc i Φ _ _ _ (AxEpiLedger.seipExit cpu km t0 kk)
    (aeqvOfAgree cpu (riscvStep true) rs t.regs none ib kk Hag0) Hr0
    (AxEpiLedger.meipN0Ok cpu km t0 ib0 kk Hnext))
  isplit
  · iintro %s2 %HQ
    obtain ⟨q, ⟨v', k0, t1, ib1, Hts1, rfl⟩, Hq⟩ := HQ
    have Hb := AxEpiCjrFrame.cjrtLedgerBranch t Dr Dw D base vs post km t0 v' k0 t1 L Hts Hts1
    iapply (AxEpiLedger.wpdOfSplitFrom i Φ s2 _ (erdExit Dr Dw cpu k0 t1 kk) (.inr (.inl Hq))
      (AxEpiLedger.seipN0Ok cpu k0 t1 ib1 kk Dr Dw HDr HDrm
        (fun v => AxEpiCjrFrame.erdOfCjrtBranch Dr Dw D base vs post _ t1 (Hb v))))
    isplit
    · iintro %s3 %HQ3
      obtain ⟨q3, ⟨v, qm, t2, ib2, He, rfl, -⟩, Hs3⟩ := HQ3
      obtain ⟨n, va, req, KK, t2', He', Hdev, Hfe, Hpa, Hlen, Hok⟩ :=
        cjrtBranchOkNode _ _ _ _ _ _ _ _ (Hb v)
      rw [He, Option.some.injEq, Prod.mk.injEq] at He'
      obtain ⟨rfl, rfl⟩ := He'
      subst Hpa
      obtain ⟨p3, k3⟩ := s3
      obtain ⟨hk, hp⟩ := Hs3
      simp only at hk hp
      subst k3
      match p3, hp with
      | .PHart c3 m3 rs3 fn3 ib3', hp =>
        obtain ⟨hc, hm, hf, hi, hag⟩ := hp
        subst c3 m3 fn3 ib3'
        iapply (wpdFetchStep Φ i cpu n va req KK ib2 kk vs t2.regs Hdev Hfe Hlen Hgd) $$ %rs3
          %(regsAgreeSym _ _ _ hag)
        iintro %rs' %Hag'
        iapply (wpdTickTail i Φ cpu _ t2 ib2 kk D post HD HDm Hok rs' Hag')
        isplit
        · icases R with ⟨R, -⟩
          iexact R
        · icases R with ⟨-, R⟩
          iintro %GD %s1 %Hs1 %Hlen1
          iapply R $$ %GD %s1
            %⟨km, t0, ib0, Hts, .inr ⟨v', k0, t1, ib1, Hts1, .inr ⟨v, n, va, req, KK, t2, He, Hs1⟩⟩⟩
            %Hlen1
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %Hs1 %Hlen1
      iapply R $$ %GD %s1 %⟨km, t0, ib0, Hts, .inr ⟨v', k0, t1, ib1, Hts1, .inl Hs1⟩⟩ %Hlen1
  · icases R with ⟨-, R⟩
    iintro %GD %s1 %Hs1 %Hlen1
    iapply R $$ %GD %s1 %⟨km, t0, ib0, Hts, .inl Hs1⟩ %Hlen1

end cjrtLedger

/-! ## The tracked tick ledger and its transfer -/

/-- Rocq `tick_ret_ok_ag` (deviation 4: the subset test before `post`). -/
def tickRetOkAg (A D P : List Register) (post : RegFile → Bool) (m : SailM Unit) (t : ExecSt) :
    Bool :=
  match epureAg D A m t with
  | some (_, s, A5) => P.all (fun r => decide (r ∈ A5)) && post s.regs
  | none => false

/-- (Lean-only) The tracked `AxEpiLedgerTick.tickAfterMeip`. -/
def AxEpiCjrFrame.tickAfterMeipAg (A D P : List Register) (post : RegFile → Bool)
    (m1 : SailM Unit) (t4 : ExecSt) (v' : BitVec 1) : Bool :=
  match toPinAg A (AxEpiLedger.ansMeip m1 v') t4 with
  | some (m2, t5, A5) =>
    isSeipNode m2 && tickRetOkAg A5 D P post (ansSeip m2 0#1) t5 &&
      tickRetOkAg A5 D P post (ansSeip m2 1#1) t5
  | none => false

/-- Rocq `tick_post_ok_ag` (the two tick pin nodes, deviation 1). -/
def tickPostOkAg (A D P : List Register) (post : RegFile → Bool) (m : SailM Unit) (t : ExecSt) :
    Bool :=
  match toPinAg A m t with
  | some (m1, t4, A4) =>
    AxEpiLedger.isMeipNode m1 && AxEpiCjrFrame.tickAfterMeipAg A4 D P post m1 t4 0#1 &&
      AxEpiCjrFrame.tickAfterMeipAg A4 D P post m1 t4 1#1
  | none => false

/-- Rocq `fetch_ok_tick_ag`. -/
def fetchOkTickAg (A D : List Register) (base : Int) (vs : List (BitVec 8)) (P : List Register)
    (post : RegFile → Bool) (mf : SailM Unit) (t2 : ExecSt) : Bool :=
  match mf with
  | .impure (.ok (.memRead n _ req)) KK =>
    !devAddr req.pa && (classify req.access_kind).akIfetch &&
    decide (paZ req.pa = base) && decide (vs.length = n) &&
    tickPostOkAg A D P post (KK (.Ok (wordOfBytes n vs, none))) t2
  | _ => false

/-- Rocq `branch_ok_tick_ag`. -/
def branchOkTickAg (A Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (P : List Register) (post : RegFile → Bool) (m : SailM Unit) (t1 : ExecSt) : Bool :=
  match erdAg Dr Dw A m t1 with
  | some (mf, t2, A2) => fetchOkTickAg A2 D base vs P post mf t2
  | none => false

/-- Rocq `branch_at_tick_ag`. -/
noncomputable def branchAtTickAg (A Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (P : List Register) (post : RegFile → Bool) (t : ExecSt) (v' v : BitVec 1) : Bool :=
  match toPinAg A (riscvStep true) t with
  | some (m0, t0, A0) =>
    match toPinAg A0 (AxEpiLedger.ansMeip m0 v') t0 with
    | some (m1, t1, A1) => branchOkTickAg A1 Dr Dw D base vs P post (ansSeip m1 v) t1
    | none => false
  | none => false

/-- Rocq `CjrTickFrameFacts`. -/
structure CjrTickFrameFacts (t : ExecSt) (A Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (P : List Register) (post : RegFile → Bool) : Prop where
  cftSeipDr : decide (Register.sig_seip ∈ Dr) = false
  cftMeipDr : decide (Register.sig_meip ∈ Dr) = false
  cftSeipD : decide (Register.sig_seip ∈ D) = false
  cftMeipD : decide (Register.sig_meip ∈ D) = false
  cftToSeip : seipAtAg A true t = true
  cftBranch00 : branchAtTickAg A Dr Dw D base vs P post t 0#1 0#1 = true
  cftBranch01 : branchAtTickAg A Dr Dw D base vs P post t 0#1 1#1 = true
  cftBranch10 : branchAtTickAg A Dr Dw D base vs P post t 1#1 0#1 = true
  cftBranch11 : branchAtTickAg A Dr Dw D base vs P post t 1#1 1#1 = true

theorem tickRetOkAgTransfer (A D P : List Register) (post : RegFile → Bool) (m : SailM Unit)
    (t t' : ExecSt) :
    postLocal P post → tickRetOkAg A D P post m t = true → agreeOn A t.regs t'.regs →
    tickRetOk D (fun rs => post rs = true) m t' := by
  intro Hpl H Hag
  unfold tickRetOkAg at H
  unfold tickRetOk
  cases he : epureAg D A m t with
  | none => rw [he] at H; exact absurd H Bool.false_ne_true
  | some p =>
    obtain ⟨x, s, A5⟩ := p
    rw [he] at H
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at H
    obtain ⟨hP, hp⟩ := H
    obtain ⟨s', he', hag5⟩ := epureAgSound D m A t t' x s A5 he Hag
    rw [he']
    have : post s'.regs = true := by
      rw [← Hpl _ _ (fun r hr => hag5 r (hP r hr))]
      exact hp
    exact this

/-- (Lean-only) `AxEpiCjrFrame.tickAfterMeipAg` transfers to `AxEpiLedgerTick.tickAfterMeip`. -/
theorem AxEpiCjrFrame.tickAfterMeipAgTransfer (A D P : List Register) (post : RegFile → Bool)
    (m1 : SailM Unit) (t4 t4' : ExecSt) (v' : BitVec 1) :
    postLocal P post → AxEpiCjrFrame.tickAfterMeipAg A D P post m1 t4 v' = true →
    agreeOn A t4.regs t4'.regs →
    AxEpiLedgerTick.tickAfterMeip D (fun rs => post rs = true) m1 t4' v' := by
  intro Hpl H Hag
  unfold AxEpiCjrFrame.tickAfterMeipAg at H
  unfold AxEpiLedgerTick.tickAfterMeip
  cases he : toPinAg A (AxEpiLedger.ansMeip m1 v') t4 with
  | none => rw [he] at H; exact absurd H Bool.false_ne_true
  | some p =>
    obtain ⟨m2, t5, A5⟩ := p
    rw [he] at H
    simp only [Bool.and_eq_true] at H
    obtain ⟨⟨hs, r0⟩, r1⟩ := H
    obtain ⟨t5', he', hag5⟩ := toPinAgSound _ A t4 t4' m2 t5 A5 he Hag
    rw [he']
    exact And.intro hs (And.intro (tickRetOkAgTransfer A5 D P post _ t5 t5' Hpl r0 hag5)
      (tickRetOkAgTransfer A5 D P post _ t5 t5' Hpl r1 hag5))

theorem tickPostOkAgTransfer (A D P : List Register) (post : RegFile → Bool) (m : SailM Unit)
    (t t' : ExecSt) :
    postLocal P post → tickPostOkAg A D P post m t = true → agreeOn A t.regs t'.regs →
    tickPostOk D (fun rs => post rs = true) m t' := by
  intro Hpl H Hag
  unfold tickPostOkAg at H
  unfold tickPostOk
  cases hts : toPinAg A m t with
  | none => rw [hts] at H; exact absurd H Bool.false_ne_true
  | some p =>
    obtain ⟨m1, t4, A4⟩ := p
    rw [hts] at H
    simp only [Bool.and_eq_true] at H
    obtain ⟨⟨hm, h0⟩, h1⟩ := H
    obtain ⟨t4', hts', hag4⟩ := toPinAgSound _ A t t' m1 t4 A4 hts Hag
    rw [hts']
    exact And.intro hm
      (And.intro (AxEpiCjrFrame.tickAfterMeipAgTransfer A4 D P post m1 t4 t4' 0#1 Hpl h0 hag4)
        (AxEpiCjrFrame.tickAfterMeipAgTransfer A4 D P post m1 t4 t4' 1#1 Hpl h1 hag4))

theorem branchOkTickAgTransfer (A Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (P : List Register) (post : RegFile → Bool) (m : SailM Unit) (t1 t1' : ExecSt) :
    postLocal P post → branchOkTickAg A Dr Dw D base vs P post m t1 = true →
    agreeOn A t1.regs t1'.regs →
    cjrtBranchOk Dr Dw D base vs (fun rs => post rs = true) m t1' := by
  intro Hpl H Hag
  unfold branchOkTickAg at H
  unfold cjrtBranchOk
  cases he : erdAg Dr Dw A m t1 with
  | none => rw [he] at H; exact absurd H Bool.false_ne_true
  | some p =>
    obtain ⟨mf, t2, A2⟩ := p
    rw [he] at H
    obtain ⟨t2', he', hag2⟩ := erdAgSound Dr Dw m A t1 t1' mf t2 A2 he Hag
    rw [he']
    show cjrtFetchOk D base vs _ mf t2'
    cases mf with
    | pure _ => exact absurd H Bool.false_ne_true
    | impure call KK =>
      cases call with
      | error _ => exact absurd H Bool.false_ne_true
      | ok o =>
        cases o
        case memRead n va req =>
          simp only [fetchOkTickAg, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at H
          obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := H
          exact ⟨h1, h2, h3, h4, tickPostOkAgTransfer A2 D P post _ t2 t2' Hpl h5 hag2⟩
        all_goals exact absurd H Bool.false_ne_true

theorem tickFrameFactsTransfer (t : ExecSt) (A Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (P : List Register) (post : RegFile → Bool) (t' : ExecSt) :
    CjrTickFrameFacts t A Dr Dw D base vs P post → postLocal P post →
    agreeOn A t.regs t'.regs → AxCjrTickFacts t' Dr Dw D base vs (fun rs => post rs = true) := by
  intro F Hpl Hag
  obtain ⟨m0, t0, A0, t0', hts, hts', hag0, Hs⟩ :=
    AxEpiCjrFrame.seipAtAgTransfer A true t t' F.cftToSeip Hag
  have Hbr : ∀ v' v, branchAtTickAg A Dr Dw D base vs P post t v' v = true →
      cjrtBranchAt Dr Dw D base vs (fun rs => post rs = true) t' v' v := by
    intro v' v H
    unfold branchAtTickAg at H
    rw [hts] at H
    unfold cjrtBranchAt
    rw [hts']
    simp only [] at H ⊢
    cases h2 : toPinAg A0 (AxEpiLedger.ansMeip m0 v') t0 with
    | none => rw [h2] at H; exact absurd H Bool.false_ne_true
    | some q =>
      obtain ⟨m1, t1, A1⟩ := q
      rw [h2] at H
      obtain ⟨t1', h2', hag1⟩ := toPinAgSound _ A0 t0 t0' m1 t1 A1 h2 hag0
      rw [h2']
      exact branchOkTickAgTransfer A1 Dr Dw D base vs P post _ t1 t1' Hpl H hag1
  exact {
    ctSeipDr := F.cftSeipDr
    ctMeipDr := F.cftMeipDr
    ctSeipD := F.cftSeipD
    ctMeipD := F.cftMeipD
    ctToSeip := by unfold seipAtTick; rw [hts']; exact Hs
    ctBranch00 := Hbr _ _ F.cftBranch00
    ctBranch01 := Hbr _ _ F.cftBranch01
    ctBranch10 := Hbr _ _ F.cftBranch10
    ctBranch11 := Hbr _ _ F.cftBranch11 }

/-! ## The c.jr tick instance -/

/-- Rocq `A_jr_t`: `AJr` plus the timer registers `tick_clock` reads first. -/
def AJrT : List Register := AJr ++ [.menvcfg, .mtimecmp, .mtime, .mcycle, .mcyclecfg]

/-- Rocq `t_frame_t`: `minstret` and `mcycle` symbolic (`mip`, `mtime` concrete, as Rocq). -/
def tFrameT (ra mi mc : BitVec 64) : ExecSt :=
  ⟨(((probeRegs pcJr).set .x1 ra).set .minstret mi).set .mcycle mc, probeMem, testDevs⟩

/-- Rocq `cjr_frame_tac`: the ra-symbolic branch tactic of `AxEpiCjrSym.branchSym` for the
tracked checkers (both tick bits), at the answers `v1` (`sig_meip`) and `v2` (`sig_seip`). -/
macro "ax_epi_cjr_frame_tac " v1:ident v2:ident : tactic => `(tactic| (
  (try unfold branchAtAg); (try unfold branchAtTickAg);
  unfold riscvStep Functions.try_step Functions.run_hart_active Functions.execute;
  rw [executeJALRSEq];
  unfold postRaSym jalrTarget;
  rw [tgtImm0];
  have HE : ∀ x, pcEqb x x = true := pcEqbRefl;
  generalize pcEqb = E at HE ⊢;
  generalize hA0 : b0S = A0;
  generalize b1S = A1;
  rcases bv1Cases $v1 with rfl | rfl <;> rcases bv1Cases $v2 with rfl | rfl;
  all_goals (
    ax_epi_cjr_sym_kcases h0;
    (exfalso; rw [← hA0, AxEpiCjrSym.b0SAligned] at h0; exact Bool.noConfusion h0);
    ax_epi_cjr_sym_kcases h1;
    all_goals ax_epi_cjr_frame_kloop HE)))

set_option maxHeartbeats 4000000 in
theorem branchFrameTickSym (ra mi mc : BitVec 64) (v' v : BitVec 1) :
    branchAtTickAg AJrT AxEpiProbe.drNopin DwAll DPost (pcJr : Int) cjrVs4 PPc (postRaSym ra)
      (tFrameT ra mi mc) v' v = true := by
  ax_epi_cjr_frame_tac v' v

theorem epiFrameCjrTick (ra mi mc : BitVec 64) :
    CjrTickFrameFacts (tFrameT ra mi mc) AJrT AxEpiProbe.drNopin DwAll DPost (pcJr : Int) cjrVs4
      PPc (postRaSym ra) where
  cftSeipDr := by decide +kernel
  cftMeipDr := by decide +kernel
  cftSeipD := by decide +kernel
  cftMeipD := by decide +kernel
  cftToSeip := by ax_epi_ledger_krfl
  cftBranch00 := branchFrameTickSym ra mi mc _ _
  cftBranch01 := branchFrameTickSym ra mi mc _ _
  cftBranch10 := branchFrameTickSym ra mi mc _ _
  cftBranch11 := branchFrameTickSym ra mi mc _ _

/-- Rocq `A_jr_t_fix`. -/
def AJrTFix : List Register :=
  AJrT.filter fun r => !decide (r = .minstret) && !decide (r = .mcycle)

theorem agreeFrameT (ra : BitVec 64) (rs : RegFile) :
    agreeOn AJrTFix rs ((probeRegs pcJr).set .x1 ra) →
    agreeOn AJrT rs (tFrameT ra (rs .minstret) (rs .mcycle)).regs := by
  intro H r Hr
  show rs r =
    ((((probeRegs pcJr).set .x1 ra).set .minstret (rs .minstret)).set .mcycle (rs .mcycle)) r
  by_cases h1 : r = .mcycle
  · subst h1; simp only [RegFile.set_same]
  · rw [RegFile.set_other _ _ _ _ h1]
    by_cases h2 : r = .minstret
    · subst h2; simp only [RegFile.set_same]
    · rw [RegFile.set_other _ _ _ _ h2]
      exact H r (List.mem_filter.2 ⟨Hr, by simp [h1, h2]⟩)

theorem cjrFrameTickInvReachesRet (ra : BitVec 64) (rs : RegFile) (cpu : CPU) (kk : Nat)
    (s1 : Athread) :
    agreeOn AJrTFix rs ((probeRegs pcJr).set .x1 ra) →
    ledgerCjrtInv ⟨rs, probeMem, testDevs⟩ AxEpiProbe.drNopin DwAll DPost cjrVs4 cpu kk s1 →
    ∃ t0 s', aeqv s1 t0 ∧ rtc (ldStep cpu cjrVs4) t0 s' ∧
      RetP cpu (fun rs3 => postRaSym ra rs3 = true) kk s' := by
  intro Hag H
  exact ledgerCjrtInvReachesRet _ _ _ _ (pcJr : Int) _ _ cpu kk s1
    (tickFrameFactsTransfer _ _ _ _ _ _ _ _ _ ⟨rs, probeMem, testDevs⟩ (epiFrameCjrTick ra _ _)
      (postRaSymLocal ra) (agreeOnSym _ _ _ (agreeFrameT ra rs Hag))) H

/-- Rocq `A_fix`: the per-tick agreement set. -/
def AFix (tick : Bool) : List Register := if tick then AJrTFix else AJrFix

/-- Rocq `cjr_frame_inv`: the per-tick row-end set. -/
noncomputable def cjrFrameInv (tick : Bool) (rs : RegFile) (cpu : CPU) (kk : Nat) (s1 : Athread) :
    Prop :=
  if tick then
    ledgerCjrtInv ⟨rs, probeMem, testDevs⟩ AxEpiProbe.drNopin DwAll DPost cjrVs4 cpu kk s1
  else
    AxEpiLedger.ledgerInv ⟨rs, probeMem, testDevs⟩ AxEpiProbe.drNopin DwAll DPost cjrVs4 cpu kk s1

theorem cjrFrameInvReachesRet' (tick : Bool) (ra : BitVec 64) (rs : RegFile) (cpu : CPU)
    (kk : Nat) (s1 : Athread) :
    agreeOn (AFix tick) rs ((probeRegs pcJr).set .x1 ra) →
    cjrFrameInv tick rs cpu kk s1 →
    ∃ t0 s', aeqv s1 t0 ∧ rtc (ldStep cpu cjrVs4) t0 s' ∧
      RetP cpu (fun rs3 => postRaSym ra rs3 = true) kk s' := by
  cases tick
  · intro Hag H
    obtain ⟨t0, s', Ha, Hr, Hs⟩ := cjrFrameInvReachesRet ra rs cpu kk s1 Hag H
    exact ⟨t0, s', Ha, rtc_subrel (fun _ _ h => .inl h) Hr, Hs⟩
  · intro Hag H
    exact cjrFrameTickInvReachesRet ra rs cpu kk s1 Hag H

section frameTick
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- GENERIC tick = true frame. -/
theorem wpdCjrFrameTickGen (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch)
    (kk : Nat) (t0 : ExecSt) (A Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (P : List Register) (post : RegFile → Bool)
    (F : CjrTickFrameFacts t0 A Dr Dw D base vs P post) (Hpl : postLocal P post)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk base vs⌝)
    (rs : RegFile) (Hag : agreeOn A rs t0.regs) :
    ⊢ ((∀ s', ⌜RetP cpu (fun rs3 => post rs3 = true) kk s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜ledgerCjrtInv ⟨rs, t0.mem, t0.dev⟩ Dr Dw D vs cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep true) rs none ib, kk⟩ Φ :=
  wpdCjrStepOfLedgerTick i Φ cpu ib kk ⟨rs, t0.mem, t0.dev⟩ _ _ _ _ _ _
    (tickFrameFactsTransfer t0 A Dr Dw D base vs P post ⟨rs, t0.mem, t0.dev⟩ F Hpl
      (agreeOnSym _ _ _ Hag)) Hgd rs (regsAgreeRefl _ _)

/-- THE FRAMED c.jr `wpd` FOR BOTH TICK BITS. -/
theorem wpdCjrFrameTick (ra : BitVec 64) (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
    (ib : Ibch) (kk : Nat)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk (pcJr : Int) cjrVs4⌝)
    (tick : Bool) (rs : RegFile) (Hag : agreeOn (AFix tick) rs ((probeRegs pcJr).set .x1 ra)) :
    ⊢ ((∀ s', ⌜RetP cpu (fun rs3 => postRaSym ra rs3 = true) kk s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1, ⌜cjrFrameInv tick rs cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep tick) rs none ib, kk⟩ Φ := by
  cases tick
  · simp only [cjrFrameInv, Bool.false_eq_true, ↓reduceIte]
    iintro R
    iapply (wpdCjrFrame ra i Φ cpu ib kk Hgd rs Hag)
    isplit
    · icases R with ⟨R, -⟩
      iintro %s' %Hs'
      iapply R $$ %s' %Hs'
    · icases R with ⟨-, R⟩
      iexact R
  · simp only [cjrFrameInv, ↓reduceIte]
    exact wpdCjrFrameTickGen i Φ cpu ib kk (tFrameT ra _ _) _ _ _ _ _ _ _ _
      (epiFrameCjrTick ra _ _) (postRaSymLocal ra) Hgd rs (agreeFrameT ra rs Hag)

end frameTick

end Weak
