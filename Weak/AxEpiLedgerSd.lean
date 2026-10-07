/-
Weak: **the whole-instruction `wpd` for the STORE `c.sdsp ra,8(sp)`** (`0xe406`) at the concrete
M-mode state `tAt pcSd`, the store twin of `AxEpiLedger`'s `c.ldsp` ledger (§5 there).

Rocq: `iris/AxEpiLedgerSd.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`pcSd = 0x80000000` is 4-aligned, so the model FETCHES 4 BYTES there (`sdVs` = the c.sdsp
halfword followed by the next one, c.ldsp); the fetch ledger lemmas are width-generic.

MODEL-SIDE CHAIN: boundary (`AxEpiLedger.toPin`, the two pin splits) → fetch (`erd` stops at the
RAM fetch) → post-fetch run to the FIRST RAM `memWrite` (`ewr`, the write twin of `erd`, bridged
by `ewrGstep`) → the write event (`wpdStoreStep`) → post-write `epure D` run to `.pure ()` with
`post`.  All model facts: `AxSdModelFacts`, closed by the kernel at the concrete state
(`epiLedgerCsdsp`).  The ledger also pins the STORED BYTES and the address.

§1/§3 GENERIC: `wpdStoreStep` — the write twin of `AxLdspWpd.wpdLoadStep`: at a plain RAM
`memWrite` node (not MMIO, not exclusive) whose row item `k` exists, the node's `wpd` follows
from a flow resource `F` delivering, for every graph, the write's annotation deposit
`storeFlow GD i k data` (the `Hflow` shape of `AxLockWpD.wpdWriteStepAll`; NOT wired to a
protocol here) and a continuation at the write's answer.  Clause (a) is EMPTY (the node's only
step is an `LStore`); clause (b) is `AStepWrite` only; clause (c) Löb over the wire; clause (d)
refuted by the row item.

HYPOTHESES KEPT (graph/protocol side): the fetch's `Hgd`, the store's row item existence `Hrow`
and the store flow resource `F`; the row-end obligation ONLY on the reachable set `ledgerSdInv`
(sanity: `ledgerSdInvReachesRet`).

## Deviations from Rocq

1. THE TWO-PIN BOUNDARY (`AxEpiLedger` deviation 1, the CONVENTION of its header): Rocq's
   single `to_seip` split is the `sig_meip` split then the `sig_seip` split.  `sdBranchAt`
   takes the two answers `v' v`; `AxSdModelFacts` has the fields `lsSeipDr`, `lsMeipDr`,
   `lsSeipD`, `lsMeipD`, `lsHead` (kept verbatim, unused), `lsToSeip` (= `seipAt`),
   `lsBranch00/01/10/11` (Rocq `ls_branch0/1`; first index = meip answer); `ledgerSdInv` has
   the meip-level `Pseip` disjunct and quantifies the seip node per meip answer; `sdStep`
   builds on `AxEpiLedger.ledgerStep` (which answers meip reads too).  `sdLedgerBranch` takes
   the two pin nodes.  Lean-only (file-qualified): `AxEpiLedgerSd.sdBranchAtEq`,
   `AxEpiLedgerSd.sdSeipReaches`, `AxEpiLedgerSd.sdMeipReaches`, `AxEpiLedgerSd.erdOfSdBranch`.
2. THE PINS (`AxRunClose` deviation 1): `ewrGstep`, `sdFetchReaches`, `sdBranchReaches`,
   `sdStoreReaches`, `wpdStoreThenRet`, `wpdFetchThenStore` take BOTH pins `∉ Dr` / `∉ D`;
   `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg`.
3. O2 STAGE C (`AxCjrWpd` deviation 1): the fetch is a pinned admin step at the SAME row
   position.  `sdFetchOk` checks `akIfetch = true` (Rocq `negb ak_latest`); `Hgd` states
   `AxCjrWpd.fetchImgOk` (Q8; Rocq `fetch_gd_ok`); the fetch's `Hflow`/`Hloc` are dropped.
   Positions: the store node, `Hrow`, the flow `F` and the pre-store `Pbefore` at `kk` (Rocq
   `S kk`); `RetS` and the post-store `Pbefore` at `kk + 1` (Rocq `S (S kk)`); `sdStep`'s fetch
   (inside `ledgerStep`) keeps `k`.  Q8: clause (b) of `wpdStoreStep` receives the image pin of
   the step label (unused: an `LStore` is not a fetch).
4. Q7 (`AxBoundaryWpd`'s ruling for `erd`): `ewr` returns `none` at an SFENCE.VMA announce
   (`ewrGstep` reads the sfence-freedom off it).  Arms not listed by Rocq (`barrier`, `choose`,
   `readRam`, `writeRam`, and a RAM `memRead`) fail, as Rocq's `_ => None`.
5. TYPES (as `AxEpiLedger` deviation 4): `mstate` ↦ `ExecSt`, `regstate` ↦ `RegFile`, `gset` ↦
   `List Register`, `bool_decide` ↦ `decide`, `Interface.WriteReq.t n` ↦
   `Mem_write_request n va …` (new bound `va`), `Interface.ReadReq.t n` ↦ `Mem_read_request n va
   …`; the WRITE's answer `inl None` ↦ `.Ok (some true)` (the lean-sail write answer,
   `pnodeStep`'s store arm); `N.to_nat n` ↦ `n`; `Ret tt` ↦ `.pure ()`; `S k` ↦ `k + 1`.  The
   write value is an `Option` in lean-sail: Rocq's `wbytes nw (WriteReq.value reqw) = data` ↦
   `reqw.value.map (WeakInterpProj.wbytes nw) = some data` (`sdStoreOk`, `sdStoreOkNode`,
   `wpdStoreStep`'s `Hdata`, `wpdStoreThenRet`, `wpdFetchThenStore`), and `storeNodePstep`
   exhibits the value `v` with `req.value = some v`.  `WPd … @ MaybeStuck; i {{ Φ }}` ↦
   `wpd .MaybeStuck i s Φ`; `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]`; `A -∗ B` ↦
   `⊢ A -∗ B`.
6. `vm_compute` ↦ `decide +kernel` for the closed boolean fields of `epiLedgerCsdsp`.
7. Lean-only helpers (file-qualified): `AxEpiLedgerSd.storeAstepInv` (the store node's only
   `astepProg` step, inline in Rocq's clause (b)), `AxEpiLedgerSd.storeNoRead` (clause (a)), and
   those of deviation 1.

**Rocq → Lean name map.**  `ewr` `ewr`, `ewr_gstep` `ewrGstep`, `sd_store_ok` `sdStoreOk`,
`sd_fetch_ok` `sdFetchOk`, `sd_branch_ok` `sdBranchOk`, `sd_branch_at` `sdBranchAt`,
`AxSdModelFacts` `AxSdModelFacts` (fields `ls*`), `sd_store_ok_node` `sdStoreOkNode`,
`sd_store_ok_shape` `sdStoreOkShape`, `sd_fetch_ok_node` `sdFetchOkNode`, `sd_fetch_ok_shape`
`sdFetchOkShape`, `sd_ledger_branch` `sdLedgerBranch`, `ledger_sd_inv` `ledgerSdInv`, `sd_step`
`sdStep`, `rtc_gstep_sd_step` `rtcGstepSdStep`, `sd_store_reaches` `sdStoreReaches`,
`sd_fetch_reaches` `sdFetchReaches`, `sd_branch_reaches` `sdBranchReaches`,
`ledger_sd_inv_reaches_ret` `ledgerSdInvReachesRet`, `store_node_pstep` `storeNodePstep`,
`store_row_ok` `storeRowOk`, `store_flow` `storeFlow`, `wpd_store_step` `wpdStoreStep`,
`wpd_store_then_ret` `wpdStoreThenRet`, `wpd_fetch_then_store` `wpdFetchThenStore`,
`wpd_csdsp_step_of_ledger` `wpdCsdspStepOfLedger`, `sd_vs` `sdVs`, `sd_addr` `sdAddr`,
`sd_data` `sdData`, `sd_post` `sdPost`, `epi_ledger_csdsp` `epiLedgerCsdsp`,
`wpd_csdsp_concrete` `wpdCsdspConcrete`.  None is in the duplicated-name table.

**Dropped:** nothing (Rocq 32 definitions/lemmas; Lean 32 + 6 Lean-only).  **Not ported:** the
`Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxEpiLedger

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! # 1. The write-stopping footprint evaluator -/

/-- `erd`'s arms, except: a RAM `memRead` FAILS (a store instruction's post-fetch segment reads
no memory) and a RAM `memWrite` STOPS and returns the node itself. -/
def ewr (Dr Dw : List Register) : SailM Unit → ExecSt → Option (SailM Unit × ExecSt)
  | .pure _, _ => none
  | .impure (.error _) _, _ => none
  | .impure (.ok o) k, s =>
    match o, k with
    | .regRead r, k => if r ∈ Dr then ewr Dr Dw (k (s.regs r)) s else none
    | .regWrite r v, k => if r ∈ Dw then ewr Dr Dw (k PUnit.unit) (s.setReg r v) else none
    | .memRead .., _ => none
    | .memWrite n va req, k =>
      if devAddr req.pa then none else some (.impure (.ok (.memWrite n va req)) k, s)
    | .barrier _, _ => none
    | .cacheOp _, k => ewr Dr Dw (k ()) s
    | .tlbi _, k => ewr Dr Dw (k ()) s
    | .translationStart _, k => ewr Dr Dw (k ()) s
    | .translationEnd _, k => ewr Dr Dw (k ()) s
    | .takeException _, k => ewr Dr Dw (k ()) s
    | .returnException _, k => ewr Dr Dw (k ()) s
    | .cycleCount, k => ewr Dr Dw (k ()) s
    | .getCycleCount, k => ewr Dr Dw (k (0 : Nat)) s
    | .message _, k => ewr Dr Dw (k ()) s
    -- Q7: an sfence.vma announce is the marker (a graph event): stop
    | .instrAnnounce n w, k => if sfAnnB n w then none else ewr Dr Dw (k ()) s
    | .branchAnnounce _ _, k => ewr Dr Dw (k ()) s
    | .choose _, _ => none
    | .readRam .., _ => none
    | .writeRam .., _ => none

/-- The bridge (twin of `AxBoundaryWpd.erdGstep`). -/
theorem ewrGstep (Dr Dw : List Register) (m : SailM Unit) :
    Register.sig_seip ∉ Dr → Register.sig_meip ∉ Dr →
    ∀ (t : ExecSt) (ib : Ibch) (q : SailM Unit) (t2 : ExecSt),
      ewr Dr Dw m t = some (q, t2) →
    ∀ (cpu : CPU) (kk : Nat), ∃ ib2,
      rtc gstep (⟨.PHart cpu m t.regs none ib, kk⟩ : Athread)
        ⟨.PHart cpu q t2.regs none ib2, kk⟩ := by
  intro hs hm
  induction m with
  | pure x =>
    intro t ib q t2 hex
    simp [ewr] at hex
  | impure call k ih =>
    intro t ib q t2 hex cpu kk
    cases call with
    | error e => simp [ewr] at hex
    | ok o =>
      cases o
      case regRead r =>
        by_cases hr : r ∈ Dr
        · simp only [ewr, hr, ↓reduceIte] at hex
          obtain ⟨ib2, hrun⟩ := ih _ t (ibRd ib r) _ _ hex cpu kk
          refine ⟨ib2, rtc_l ?_ hrun⟩
          refine gstepRd cpu r k t.regs ib kk ?_
          rintro (rfl | rfl)
          · exact hs hr
          · exact hm hr
        · simp [ewr, hr] at hex
      case regWrite r v =>
        by_cases hr : r ∈ Dw
        · simp only [ewr, hr, ↓reduceIte] at hex
          obtain ⟨ib2, hrun⟩ := ih _ _ ib _ _ hex cpu kk
          exact ⟨ib2, rtc_l (gstepWr cpu r v k t.regs ib kk) hrun⟩
        · simp [ewr, hr] at hex
      case memWrite n va req =>
        by_cases hd : devAddr req.pa = true
        · simp [ewr, hd] at hex
        · simp only [ewr, hd, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
            Prod.mk.injEq] at hex
          obtain ⟨rfl, rfl⟩ := hex
          exact ⟨ib, rtc_refl _⟩
      case instrAnnounce nw w =>
        cases hsw : sfAnnB nw w <;>
          simp only [ewr, hsw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hex
        obtain ⟨ib2, hrun⟩ := ih _ t (ibAnn (ibOfBvn w)) _ _ hex cpu kk
        exact ⟨ib2,
          rtc_l (gstepOfPnode cpu _ t.regs ib kk _ _ none (some (ibAnn (ibOfBvn w))) none
            ⟨(annLabelNot hsw).symm, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial rfl) hrun⟩
      all_goals first
        | (simp [ewr] at hex; done)
        | (simp only [ewr] at hex
           obtain ⟨ib2, hrun⟩ := ih _ t ib _ _ hex cpu kk
           exact ⟨ib2,
             rtc_l (gstepOfPnode cpu _ t.regs ib kk _ _ none none none
               ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial trivial) hrun⟩)

/-! # 2. The store ledger -/

/-- The `ewr`-returned node is a plain RAM store at `staddr` of the bytes `data`, and its
continuation (the write's answer) is `epure D` to a `post` state. -/
def sdStoreOk (D : List Register) (staddr : Int) (data : List (BitVec 8))
    (post : RegFile → Bool) (mw : SailM Unit) (tw : ExecSt) : Bool :=
  match mw with
  | .impure (.ok (.memWrite nw _ reqw)) KK =>
    !devAddr reqw.pa && !(classify reqw.access_kind).akLatest &&
    decide (paZ reqw.pa = staddr) &&
    decide (reqw.value.map (WeakInterpProj.wbytes nw) = some data) &&
    match epure D (KK (.Ok (some true))) tw with
    | some (_, t3) => post t3.regs
    | none => false
  | _ => false

def sdFetchOk (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8)) (staddr : Int)
    (data : List (BitVec 8)) (post : RegFile → Bool) (mf : SailM Unit) (t2 : ExecSt) : Bool :=
  match mf with
  | .impure (.ok (.memRead n _ req)) KKf =>
    !devAddr req.pa && (classify req.access_kind).akIfetch &&
    decide (paZ req.pa = base) && decide (vs.length = n) &&
    match ewr Dr Dw (KKf (.Ok (wordOfBytes n vs, none))) t2 with
    | some (mw, tw) => sdStoreOk D staddr data post mw tw
    | none => false
  | _ => false

def sdBranchOk (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8)) (staddr : Int)
    (data : List (BitVec 8)) (post : RegFile → Bool) (m : SailM Unit) (t1 : ExecSt) : Bool :=
  match erd Dr Dw m t1 with
  | some (mf, t2) => sdFetchOk Dr Dw D base vs staddr data post mf t2
  | none => false

/-- The branch for the answers `v'` (of `sig_meip`) and `v` (of `sig_seip`) (deviation 1). -/
noncomputable def sdBranchAt (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (staddr : Int) (data : List (BitVec 8)) (post : RegFile → Bool) (t : ExecSt)
    (v' v : BitVec 1) : Bool :=
  match AxEpiLedger.toPin (riscvStep false) t with
  | some (m0, t0) =>
    match AxEpiLedger.toPin (AxEpiLedger.ansMeip m0 v') t0 with
    | some (m1, t1) => sdBranchOk Dr Dw D base vs staddr data post (ansSeip m1 v) t1
    | none => false
  | none => false

/-- THE STORE LEDGER. -/
structure AxSdModelFacts (t : ExecSt) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (staddr : Int) (data : List (BitVec 8)) (post : RegFile → Bool) :
    Prop where
  lsSeipDr : decide (Register.sig_seip ∈ Dr) = false
  lsMeipDr : decide (Register.sig_meip ∈ Dr) = false
  lsSeipD : decide (Register.sig_seip ∈ D) = false
  lsMeipD : decide (Register.sig_meip ∈ D) = false
  lsHead : isSeipNode (riscvStep false) = false
  lsToSeip : seipAt t = true
  lsBranch00 : sdBranchAt Dr Dw D base vs staddr data post t 0#1 0#1 = true
  lsBranch01 : sdBranchAt Dr Dw D base vs staddr data post t 0#1 1#1 = true
  lsBranch10 : sdBranchAt Dr Dw D base vs staddr data post t 1#1 0#1 = true
  lsBranch11 : sdBranchAt Dr Dw D base vs staddr data post t 1#1 1#1 = true

/-! ## Pure bridges -/

theorem sdStoreOkNode (D : List Register) (staddr : Int) (data : List (BitVec 8))
    (post : RegFile → Bool) (nw va : Nat)
    (reqw : Mem_write_request nw va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (tw : ExecSt) :
    sdStoreOk D staddr data post (.impure (.ok (.memWrite nw va reqw)) KK) tw = true →
    devAddr reqw.pa = false ∧ (classify reqw.access_kind).akLatest = false ∧
    paZ reqw.pa = staddr ∧ reqw.value.map (WeakInterpProj.wbytes nw) = some data ∧
    ∃ t3 : ExecSt, epure D (KK (.Ok (some true))) tw = some ((), t3) ∧ post t3.regs = true := by
  intro H
  cases he : epure D (KK (.Ok (some true))) tw with
  | none => simp [sdStoreOk, he] at H
  | some p =>
    obtain ⟨⟨⟩, t3⟩ := p
    simp only [sdStoreOk, he, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at H
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := H
    exact ⟨h1, h2, h3, h4, t3, rfl, h5⟩

theorem sdStoreOkShape (D : List Register) (staddr : Int) (data : List (BitVec 8))
    (post : RegFile → Bool) (mw : SailM Unit) (tw : ExecSt) :
    sdStoreOk D staddr data post mw tw = true →
    ∃ (nw va : Nat) (reqw : Mem_write_request nw va Arch.pa Arch.translation Arch.arch_ak)
      (KK : Result (Option Bool) Arch.abort → SailM Unit),
      mw = .impure (.ok (.memWrite nw va reqw)) KK := by
  intro H
  cases mw with
  | pure _ => exact absurd H Bool.false_ne_true
  | impure call KK =>
    cases call with
    | error _ => exact absurd H Bool.false_ne_true
    | ok o =>
      cases o
      case memWrite nw va reqw => exact ⟨nw, va, reqw, KK, rfl⟩
      all_goals exact absurd H Bool.false_ne_true

theorem sdFetchOkNode (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (staddr : Int) (data : List (BitVec 8)) (post : RegFile → Bool) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KKf : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (t2 : ExecSt) :
    sdFetchOk Dr Dw D base vs staddr data post (.impure (.ok (.memRead n va req)) KKf) t2 = true →
    devAddr req.pa = false ∧ (classify req.access_kind).akIfetch = true ∧
    paZ req.pa = base ∧ vs.length = n ∧
    ∃ (mw : SailM Unit) (tw : ExecSt),
      ewr Dr Dw (KKf (.Ok (wordOfBytes n vs, none))) t2 = some (mw, tw) ∧
      sdStoreOk D staddr data post mw tw = true := by
  intro H
  cases he : ewr Dr Dw (KKf (.Ok (wordOfBytes n vs, none))) t2 with
  | none => simp [sdFetchOk, he] at H
  | some p =>
    obtain ⟨mw, tw⟩ := p
    simp only [sdFetchOk, he, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at H
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := H
    exact ⟨h1, h2, h3, h4, mw, tw, rfl, h5⟩

theorem sdFetchOkShape (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (staddr : Int) (data : List (BitVec 8)) (post : RegFile → Bool) (mf : SailM Unit)
    (t2 : ExecSt) :
    sdFetchOk Dr Dw D base vs staddr data post mf t2 = true →
    ∃ (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (KKf : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit),
      mf = .impure (.ok (.memRead n va req)) KKf := by
  intro H
  cases mf with
  | pure _ => exact absurd H Bool.false_ne_true
  | impure call KKf =>
    cases call with
    | error _ => exact absurd H Bool.false_ne_true
    | ok o =>
      cases o
      case memRead n va req => exact ⟨n, va, req, KKf, rfl⟩
      all_goals exact absurd H Bool.false_ne_true

/-- (Lean-only) `sdBranchAt` at the two computed pin nodes. -/
theorem AxEpiLedgerSd.sdBranchAtEq (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (staddr : Int) (data : List (BitVec 8)) (post : RegFile → Bool)
    (t : ExecSt) (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt)
    (v' : BitVec 1) (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt)
    (v : BitVec 1)
    (Hts : AxEpiLedger.toPin (riscvStep false) t
      = some (.impure (.ok (.regRead Register.sig_meip)) km, t0))
    (Hts1 : AxEpiLedger.toPin (km v') t0
      = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1)) :
    sdBranchAt Dr Dw D base vs staddr data post t v' v =
      sdBranchOk Dr Dw D base vs staddr data post (k0 v) t1 := by
  unfold sdBranchAt
  rw [Hts]
  simp only []
  rw [AxEpiLedger.ansMeipNode, Hts1]
  simp only []
  rw [AxEpiLedger.ansSeipNode]

theorem sdLedgerBranch (t : ExecSt) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (staddr : Int) (data : List (BitVec 8)) (post : RegFile → Bool)
    (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt) (v' : BitVec 1)
    (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt) :
    AxSdModelFacts t Dr Dw D base vs staddr data post →
    AxEpiLedger.toPin (riscvStep false) t
      = some (.impure (.ok (.regRead Register.sig_meip)) km, t0) →
    AxEpiLedger.toPin (km v') t0
      = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) →
    ∀ v, sdBranchOk Dr Dw D base vs staddr data post (k0 v) t1 = true := by
  intro L Hts Hts1 v
  rw [← AxEpiLedgerSd.sdBranchAtEq Dr Dw D base vs staddr data post t km t0 v' k0 t1 v Hts Hts1]
  rcases bv1Cases v' with rfl | rfl <;> rcases bv1Cases v with rfl | rfl
  · exact L.lsBranch00
  · exact L.lsBranch01
  · exact L.lsBranch10
  · exact L.lsBranch11

/-- THE ROW-END INVARIANT of the store: the two boundary sets, the set before the store node,
and the post-store `Pbefore` of the certified `.pure ()`. -/
def ledgerSdInv (t : ExecSt) (Dr Dw D : List Register) (vs : List (BitVec 8)) (cpu : CPU)
    (kk : Nat) (s1 : Athread) : Prop :=
  ∃ (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt) (ib0 : Ibch),
    AxEpiLedger.toPin (riscvStep false) t
      = some (.impure (.ok (.regRead Register.sig_meip)) km, t0) ∧
    (Pseip (AxEpiLedger.meipNode cpu km t0.regs ib0 kk) (AxEpiLedger.seipExit cpu km t0 kk) s1 ∨
     ∃ (v' : BitVec 1) (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt)
       (ib1 : Ibch),
       AxEpiLedger.toPin (km v') t0 = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) ∧
       (Pseip (seipNode cpu k0 t1.regs ib1 kk) (erdExit Dr Dw cpu k0 t1 kk) s1 ∨
        ∃ (v : BitVec 1) (n va : Nat)
          (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
          (KKf : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (t2 : ExecSt)
          (nw vaw : Nat) (reqw : Mem_write_request nw vaw Arch.pa Arch.translation Arch.arch_ak)
          (KK : Result (Option Bool) Arch.abort → SailM Unit) (tw : ExecSt) (ibW : Ibch),
          erd Dr Dw (k0 v) t1 = some (.impure (.ok (.memRead n va req)) KKf, t2) ∧
          ewr Dr Dw (KKf (.Ok (wordOfBytes n vs, none))) t2
            = some (.impure (.ok (.memWrite nw vaw reqw)) KK, tw) ∧
          (Pbefore ⟨.PHart cpu (.impure (.ok (.memWrite nw vaw reqw)) KK) tw.regs none ibW, kk⟩
              s1 ∨
           ∃ (t3 : ExecSt) (ib' : Ibch),
             epure D (KK (.Ok (some true))) tw = some ((), t3) ∧
             Pbefore ⟨.PHart cpu (.pure ()) t3.regs none ib', kk + 1⟩ s1)))

/-- The store's run relation: `AxEpiLedger.ledgerStep`, or a RAM write. -/
def sdStep (cpu : CPU) (vs : List (BitVec 8)) (s s' : Athread) : Prop :=
  AxEpiLedger.ledgerStep cpu vs s s' ∨
  (∃ (n va : Nat) (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
     (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib ib' : Ibch)
     (k : Nat),
     s = ⟨.PHart cpu (.impure (.ok (.memWrite n va req)) KK) rs none ib, k⟩ ∧
     s' = ⟨.PHart cpu (KK (.Ok (some true))) rs none ib', k + 1⟩)

theorem rtcGstepSdStep (cpu : CPU) (vs : List (BitVec 8)) (s s' : Athread) :
    rtc gstep s s' → rtc (sdStep cpu vs) s s' :=
  rtc_subrel (fun _ _ h => .inl (.inl h))

theorem sdStoreReaches (D : List Register) (staddr : Int) (data : List (BitVec 8))
    (post : RegFile → Bool) (cpu : CPU) (vs : List (BitVec 8)) (nw va : Nat)
    (reqw : Mem_write_request nw va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (tw : ExecSt) (ib : Ibch) (k : Nat) :
    Register.sig_seip ∉ D → Register.sig_meip ∉ D →
    sdStoreOk D staddr data post (.impure (.ok (.memWrite nw va reqw)) KK) tw = true →
    ∃ s', rtc (sdStep cpu vs)
        ⟨.PHart cpu (.impure (.ok (.memWrite nw va reqw)) KK) tw.regs none ib, k⟩ s' ∧
      RetS cpu post (k + 1) s' := by
  intro HD HDm H
  obtain ⟨-, -, -, -, t3, Hep, Hpost⟩ := sdStoreOkNode _ _ _ _ _ _ _ _ _ H
  obtain ⟨ib3, Hr⟩ := epureGstepRtc D HD HDm _ _ _ _ Hep cpu ib (k + 1)
  exact ⟨_, rtc_l (.inr ⟨nw, va, reqw, KK, tw.regs, ib, ib, k, rfl, rfl⟩)
    (rtcGstepSdStep cpu vs _ _ Hr), t3.regs, ib3, Hpost, aeqvHartRefl ..⟩

theorem sdFetchReaches (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (staddr : Int) (data : List (BitVec 8)) (post : RegFile → Bool) (cpu : CPU) (kk n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KKf : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (t2 : ExecSt)
    (ib2 : Ibch) :
    Register.sig_seip ∉ Dr → Register.sig_meip ∉ Dr →
    Register.sig_seip ∉ D → Register.sig_meip ∉ D →
    sdFetchOk Dr Dw D base vs staddr data post (.impure (.ok (.memRead n va req)) KKf) t2 = true →
    ∃ s', rtc (sdStep cpu vs)
        ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KKf) t2.regs none ib2, kk⟩ s' ∧
      RetS cpu post (kk + 1) s' := by
  intro HDr HDrm HD HDm H
  obtain ⟨-, -, -, -, mw, tw, He2, Hs⟩ := sdFetchOkNode _ _ _ _ _ _ _ _ _ _ _ _ _ H
  obtain ⟨nw, vaw, reqw, KK, rfl⟩ := sdStoreOkShape _ _ _ _ _ _ Hs
  obtain ⟨ibW, Hr⟩ := ewrGstep Dr Dw _ HDr HDrm t2 ib2 _ _ He2 cpu kk
  obtain ⟨s', Hr', Hs'⟩ := sdStoreReaches D staddr data post cpu vs nw vaw reqw KK tw ibW kk HD HDm Hs
  exact ⟨s', rtc_l (.inl (.inr (.inr (.inl ⟨n, va, req, KKf, t2.regs, ib2, ib2, kk, rfl, rfl⟩))))
    (rtc_transitive (rtcGstepSdStep cpu vs _ _ Hr) Hr'), Hs'⟩

theorem sdBranchReaches (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (staddr : Int) (data : List (BitVec 8)) (post : RegFile → Bool) (cpu : CPU) (kk : Nat)
    (m : SailM Unit) (t1 : ExecSt) (ib : Ibch) :
    Register.sig_seip ∉ Dr → Register.sig_meip ∉ Dr →
    Register.sig_seip ∉ D → Register.sig_meip ∉ D →
    sdBranchOk Dr Dw D base vs staddr data post m t1 = true →
    ∃ s', rtc (sdStep cpu vs) ⟨.PHart cpu m t1.regs none ib, kk⟩ s' ∧
      RetS cpu post (kk + 1) s' := by
  intro HDr HDrm HD HDm Hb
  unfold sdBranchOk at Hb
  cases he : erd Dr Dw m t1 with
  | none => rw [he] at Hb; exact absurd Hb Bool.false_ne_true
  | some p =>
    obtain ⟨mf, t2⟩ := p
    rw [he] at Hb
    obtain ⟨n, va, req, KKf, rfl⟩ := sdFetchOkShape _ _ _ _ _ _ _ _ _ _ Hb
    obtain ⟨ib2, -, -, Hr⟩ := erdGstep Dr Dw m HDr HDrm t1 ib _ _ he cpu kk
    obtain ⟨s', Hr', Hs'⟩ :=
      sdFetchReaches Dr Dw D base vs staddr data post cpu kk n va req KKf t2 ib2 HDr HDrm HD HDm Hb
    exact ⟨s', rtc_transitive (rtcGstepSdStep cpu vs _ _ Hr) Hr', Hs'⟩

/-- (Lean-only) From the `sig_seip` node of a certified store branch, `RetS` is reached. -/
theorem AxEpiLedgerSd.sdSeipReaches (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (staddr : Int) (data : List (BitVec 8)) (post : RegFile → Bool)
    (cpu : CPU) (kk : Nat) (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt)
    (ib1 : Ibch)
    (HDr : Register.sig_seip ∉ Dr) (HDrm : Register.sig_meip ∉ Dr)
    (HD : Register.sig_seip ∉ D) (HDm : Register.sig_meip ∉ D)
    (Hb : ∀ v, sdBranchOk Dr Dw D base vs staddr data post (k0 v) t1 = true) :
    ∃ s', rtc (sdStep cpu vs) (seipNode cpu k0 t1.regs ib1 kk) s' ∧
      RetS cpu post (kk + 1) s' := by
  obtain ⟨s', Hr, Hs'⟩ := sdBranchReaches Dr Dw D base vs staddr data post cpu kk (k0 0#1) t1
    (ibRd ib1 Register.sig_seip) HDr HDrm HD HDm (Hb _)
  exact ⟨s', rtc_l (.inl (.inr (.inl ⟨k0, t1.regs, ib1, 0#1, _, kk, rfl, rfl⟩))) Hr, Hs'⟩

/-- (Lean-only) From the `sig_meip` node of a certified store ledger, `RetS` is reached. -/
theorem AxEpiLedgerSd.sdMeipReaches (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (staddr : Int) (data : List (BitVec 8)) (post : RegFile → Bool)
    (cpu : CPU) (kk : Nat) (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt)
    (ib0 : Ibch)
    (HDr : Register.sig_seip ∉ Dr) (HDrm : Register.sig_meip ∉ Dr)
    (HD : Register.sig_seip ∉ D) (HDm : Register.sig_meip ∉ D)
    (H : ∀ v', ∃ (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt),
      AxEpiLedger.toPin (km v') t0
        = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) ∧
      ∀ v, sdBranchOk Dr Dw D base vs staddr data post (k0 v) t1 = true) :
    ∃ s', rtc (sdStep cpu vs) (AxEpiLedger.meipNode cpu km t0.regs ib0 kk) s' ∧
      RetS cpu post (kk + 1) s' := by
  obtain ⟨k0, t1, Hts1, Hb⟩ := H 0#1
  obtain ⟨ib1, Hr⟩ := AxEpiLedger.toPinGstep _ t0 (ibRd ib0 Register.sig_meip) _ _ Hts1 cpu kk
  obtain ⟨s', Hr', Hs'⟩ :=
    AxEpiLedgerSd.sdSeipReaches Dr Dw D base vs staddr data post cpu kk k0 t1 ib1 HDr HDrm HD
      HDm Hb
  exact ⟨s', rtc_l (.inl (.inr (.inr (.inr ⟨km, t0.regs, ib0, 0#1, _, kk, rfl, rfl⟩))))
    (rtc_transitive (rtcGstepSdStep cpu vs _ _ Hr) Hr'), Hs'⟩

/-- SANITY (non-vacuity of the store's row-end premise): every state of `ledgerSdInv` is `aeqv`
to a state that runs — `gstep`s, the pin answers, the fetch of `vs`, the RAM write — to a
`RetS` state with `post`. -/
theorem ledgerSdInvReachesRet (t : ExecSt) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (staddr : Int) (data : List (BitVec 8)) (post : RegFile → Bool)
    (cpu : CPU) (kk : Nat) (s1 : Athread) :
    AxSdModelFacts t Dr Dw D base vs staddr data post →
    ledgerSdInv t Dr Dw D vs cpu kk s1 →
    ∃ t0 s', aeqv s1 t0 ∧ rtc (sdStep cpu vs) t0 s' ∧ RetS cpu post (kk + 1) s' := by
  intro L ⟨km, t0, ib0, Hts, Hc⟩
  have HDr := of_decide_eq_false L.lsSeipDr
  have HDrm := of_decide_eq_false L.lsMeipDr
  have HD := of_decide_eq_false L.lsSeipD
  have HDm := of_decide_eq_false L.lsMeipD
  have Hall : ∀ v', ∃ (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt),
      AxEpiLedger.toPin (km v') t0
        = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) ∧
      ∀ v, sdBranchOk Dr Dw D base vs staddr data post (k0 v) t1 = true := by
    intro v'
    obtain ⟨k0, t1, Hts1⟩ := AxEpiLedger.seipAtNext t km t0 L.lsToSeip Hts v'
    exact ⟨k0, t1, Hts1, sdLedgerBranch t Dr Dw D base vs staddr data post km t0 v' k0 t1 L Hts
      Hts1⟩
  rcases Hc with Hc | ⟨v', k0, t1, ib1, Hts1, Hc⟩
  · obtain ⟨sm, Hrm, Hsm⟩ :=
      AxEpiLedgerSd.sdMeipReaches Dr Dw D base vs staddr data post cpu kk km t0 ib0 HDr HDrm HD
        HDm Hall
    rcases Hc with ⟨t', Ha, Htc⟩ | Ha | ⟨q, ⟨v', k0, t1, ib1, Hts1, rfl⟩, t', Ha, Htc⟩
    · exact ⟨t', sm, Ha, rtc_transitive (rtcGstepSdStep cpu vs _ _ (tc_rtc Htc)) Hrm, Hsm⟩
    · exact ⟨_, sm, Ha, Hrm, Hsm⟩
    · have Hb := sdLedgerBranch t Dr Dw D base vs staddr data post km t0 v' k0 t1 L Hts Hts1
      obtain ⟨s', Hr, Hs'⟩ := AxEpiLedgerSd.sdSeipReaches Dr Dw D base vs staddr data post cpu
        kk k0 t1 ib1 HDr HDrm HD HDm Hb
      exact ⟨t', s', Ha, rtc_transitive (rtcGstepSdStep cpu vs _ _ (tc_rtc Htc)) Hr, Hs'⟩
  · have Hb := sdLedgerBranch t Dr Dw D base vs staddr data post km t0 v' k0 t1 L Hts Hts1
    obtain ⟨ss, Hrs, Hss⟩ := AxEpiLedgerSd.sdSeipReaches Dr Dw D base vs staddr data post cpu kk
      k0 t1 ib1 HDr HDrm HD HDm Hb
    rcases Hc with Hc | ⟨v, n, va, req, KKf, t2, nw, vaw, reqw, KK, tw, ibW, He, He2, Hc⟩
    · rcases Hc with ⟨t', Ha, Htc⟩ | Ha | ⟨q, ⟨v, qm, t2, ib2, He, rfl, -⟩, t', Ha, Htc⟩
      · exact ⟨t', ss, Ha, rtc_transitive (rtcGstepSdStep cpu vs _ _ (tc_rtc Htc)) Hrs, Hss⟩
      · exact ⟨_, ss, Ha, Hrs, Hss⟩
      · have Hbv := Hb v
        unfold sdBranchOk at Hbv
        rw [He] at Hbv
        obtain ⟨n, va, req, KKf, rfl⟩ := sdFetchOkShape _ _ _ _ _ _ _ _ _ _ Hbv
        obtain ⟨s', Hr, Hs'⟩ :=
          sdFetchReaches Dr Dw D base vs staddr data post cpu kk n va req KKf t2 ib2 HDr HDrm HD
            HDm Hbv
        exact ⟨t', s', Ha, rtc_transitive (rtcGstepSdStep cpu vs _ _ (tc_rtc Htc)) Hr, Hs'⟩
    · have Hs : sdStoreOk D staddr data post (.impure (.ok (.memWrite nw vaw reqw)) KK) tw
          = true := by
        have Hbv := Hb v
        unfold sdBranchOk at Hbv
        rw [He] at Hbv
        obtain ⟨-, -, -, -, mw, tw', He2', Hs⟩ := sdFetchOkNode _ _ _ _ _ _ _ _ _ _ _ _ _ Hbv
        rw [He2, Option.some.injEq, Prod.mk.injEq] at He2'
        obtain ⟨rfl, rfl⟩ := He2'
        exact Hs
      rcases Hc with ⟨t', Ha, Htc⟩ | ⟨t3, ib', Hep, t', Ha, Htc⟩
      · obtain ⟨s', Hr, Hs'⟩ :=
          sdStoreReaches D staddr data post cpu vs nw vaw reqw KK tw ibW kk HD HDm Hs
        exact ⟨t', s', Ha, rtc_transitive (rtcGstepSdStep cpu vs _ _ (tc_rtc Htc)) Hr, Hs'⟩
      · obtain ⟨-, -, -, -, t3', Hep', Hpost⟩ := sdStoreOkNode _ _ _ _ _ _ _ _ _ Hs
        rw [Hep, Option.some.injEq, Prod.mk.injEq] at Hep'
        obtain ⟨-, rfl⟩ := Hep'
        exact ⟨t', _, Ha, rtcGstepSdStep cpu vs _ _ (tc_rtc Htc), t3.regs, ib', Hpost,
          aeqvHartRefl ..⟩

/-! # 3. GENERIC: THE DATA-STORE NODE -/

/-- The only program step of a plain RAM `memWrite` node. -/
theorem storeNodePstep (cpu : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) (d : Efab)
    (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    devAddr req.pa = false → (classify req.access_kind).akLatest = false →
    pstepProg (.PHart cpu (.impure (.ok (.memWrite n va req)) KK) rs none ib) d l p' d' →
    ∃ v, req.value = some v ∧
      l = LStore (classify req.access_kind).akSync (paZ req.pa) (WeakInterpProj.wbytes n v)
            (depsAsrc (depsOfIb ib.ibBits)) (depsVsrc (depsOfIb ib.ibBits)) ∧
      p' = .PHart cpu (KK (.Ok (some true))) rs none ib := by
  intro hdev hlat h
  cases p' with
  | PDisk _ => exact False.elim h
  | PHart c m' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hn, -⟩ := h
    simp only [pstepNode, pnodeStep, hdev, Bool.false_eq_true, ↓reduceIte] at hn
    cases hv : req.value with
    | none => simp only [hv] at hn
    | some v =>
      simp only [hv] at hn
      rcases hn with ⟨-, ⟨-, rfl, rfl, rfl, rfl, -, rfl, -⟩ | ⟨hl', -⟩⟩
      · exact ⟨v, rfl, rfl, rfl⟩
      · rw [hlat] at hl'; exact absurd hl' Bool.false_ne_true

/-- (Lean-only) The only `astepProg` step of a plain RAM `memWrite` node: the `AStepWrite` of
its `LStore`, to the write's answer at `k + 1`. -/
theorem AxEpiLedgerSd.storeAstepInv (row : List Lbl) (cpu : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat)
    (l : Wlabel) (s' : Athread) :
    devAddr req.pa = false → (classify req.access_kind).akLatest = false →
    AxOpsem.astepProg row ⟨.PHart cpu (.impure (.ok (.memWrite n va req)) KK) rs none ib, k⟩ l s' →
    ∃ v, req.value = some v ∧
      l = LStore (classify req.access_kind).akSync (paZ req.pa) (WeakInterpProj.wbytes n v)
            (depsAsrc (depsOfIb ib.ibBits)) (depsVsrc (depsOfIb ib.ibBits)) ∧
      s' = ⟨.PHart cpu (KK (.Ok (some true))) rs none ib, k + 1⟩ := by
  intro hdev hlat h
  cases h with
  | AStepAdmin _ _ d _ p' d' hadm hps =>
    obtain ⟨v, -, rfl, -⟩ := storeNodePstep cpu n va req KK rs ib d l p' d' hdev hlat hps
    exact (hadm : False).elim
  | AStepWrite _ _ d _ lb p' d' _ _ _ _ hps =>
    obtain ⟨v, hv, hl, rfl⟩ := storeNodePstep cpu n va req KK rs ib d l p' d' hdev hlat hps
    exact ⟨v, hv, hl, rfl⟩
  | AStepFence _ _ d _ lb p' d' _ hf _ hps =>
    obtain ⟨v, -, rfl, -⟩ := storeNodePstep cpu n va req KK rs ib d l p' d' hdev hlat hps
    simp [wlFence] at hf

/-- (Lean-only) No read step is available at a plain RAM `memWrite` node. -/
theorem AxEpiLedgerSd.storeNoRead (row : List Lbl) (cpu : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat)
    (id : AidentT) (K : List (BitVec 8) → Athread) :
    devAddr req.pa = false → (classify req.access_kind).akLatest = false →
    ¬ areadStep row ⟨.PHart cpu (.impure (.ok (.memWrite n va req)) KK) rs none ib, k⟩ id K := by
  rintro hdev hlat ⟨lb, -, -, hrd, HK⟩
  obtain ⟨l, d, d', hwl, -, hps, -⟩ :=
    HK (List.replicate (aidentN id) 0) List.length_replicate
  obtain ⟨v, -, rfl, -⟩ := storeNodePstep cpu n va req KK rs ib d l _ d' hdev hlat hps
  simp only [wlRd] at hwl
  simp [← hwl] at hrd

/-- (Lean-only) `sdBranchOk` gives the `erd` exit. -/
theorem AxEpiLedgerSd.erdOfSdBranch (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (staddr : Int) (data : List (BitVec 8)) (post : RegFile → Bool)
    (m : SailM Unit) (t1 : ExecSt)
    (Hb : sdBranchOk Dr Dw D base vs staddr data post m t1 = true) :
    ∃ q t2, erd Dr Dw m t1 = some (q, t2) := by
  unfold sdBranchOk at Hb
  cases he : erd Dr Dw m t1 with
  | none => rw [he] at Hb; exact absurd Hb Bool.false_ne_true
  | some p => exact ⟨p.1, p.2, rfl⟩

/-- The pure row fact: row item `k` exists. -/
def storeRowOk (GD : Gdexec) (i : Agent) (k : Nat) : Prop :=
  ∃ lb, (AxOpsem.grow GD i)[k]? = some lb

section store
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- The store's annotation deposit at `(i, k)` — the `Hflow` shape of
`AxLockWpD.wpdWriteStepAll` (deposit `R`, plus the graph's data at `(i, k)` being `data`). -/
def storeFlow (GD : Gdexec) (i : Agent) (k : Nat) (data : List (BitVec 8)) : IProp GF :=
  iprop(∀ na, naAtProgress GD i k na ∗ AxirisG.annotInterp na -∗ |==> ▷ |==>
    ∃ (R : IProp GF) (naUsed naUnused : Mea GF) (ls' : AxirisG.logTsT GF),
      naSplittingWf (Axpol.lobp GD (i, k)) na naUsed naUnused ∗
      flowEqDyn GD (i, k) (Axpol.sPol GD (i, k)) naUsed iprop(R ∗ ⌜graphData GD (i, k) = some data⌝) ∗
      AxirisG.annotInterp (PartialMap.union (PartialMap.union {[(i, k) := R]} naUnused) na) ∗
      AxirisG.localInterp GD i (k + 1) ls')

theorem wpdStoreStep (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat) (rs0 : RegFile)
    (data : List (BitVec 8))
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hdata : req.value.map (WeakInterpProj.wbytes n) = some data)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜storeRowOk GD i k⌝) :
    ⊢ ∀ rs, ⌜regsAgree AxRunClose.pinReg rs0 rs⌝ -∗
      (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
         storeFlow GD i k data) -∗
      (∀ rs', ⌜regsAgree AxRunClose.pinReg rs0 rs'⌝ -∗
         wpd .MaybeStuck i ⟨.PHart cpu (KK (.Ok (some true))) rs' none ib, k + 1⟩ Φ) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memWrite n va req)) KK) rs none ib, k⟩ Φ := by
  unfold storeFlow
  iloeb as IH
  iintro %rs %HP F C
  iapply (AxWpD.wpdMUnfoldStep rvwmoCatConsistent .MaybeStuck i _ Φ).2
  isplit
  · iapply (progressOblMaybestuck (GF := GF) i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
  ihave Hok := (Hrow GD Hc) $$ Hg
  icases Hok with %Hok
  obtain ⟨lb0, Hlb0⟩ := Hok
  isplit
  · -- (a) no read at a store node
    iintro %id %K %Hst
    exact (AxEpiLedgerSd.storeNoRead _ cpu n va req KK rs ib k id K Hdev Hlat Hst).elim
  isplit
  · -- (b) THE WRITE: `AStepWrite` only
    iintro %l %s' %Hst %Hpin
    obtain ⟨v, hv, rfl, rfl⟩ :=
      AxEpiLedgerSd.storeAstepInv _ cpu n va req KK rs ib k l s' Hdev Hlat Hst
    have hd : WeakInterpProj.wbytes n v = data := by
      rw [hv] at Hdata
      exact Option.some.inj Hdata
    subst hd
    simp only [wlWdata]
    unfold wpEvStep
    iintro %na Hpg
    ihave Hf := F $$ %GD %ls %Hc Hg Hloc
    imod Hf $$ %na Hpg with Hf
    imodintro
    inext
    imod Hf with ⟨%R, %nu, %nuu, %ls', Hs, Hfe, Hna, Hl⟩
    imodintro
    iexists (), R, nu, nuu, ls'
    isplitr
    · ipureintro
      trivial
    iframe Hs Hfe Hna Hl
    iapply C $$ %rs %HP
  isplit
  · -- (c) the PLIC wire: back to the store node, Löb
    iintro %s' %Hw
    obtain ⟨hk, hp⟩ := awireAeqv _ _ Hw
    obtain ⟨p', k'⟩ := s'
    simp only at hk hp
    subst hk
    match p', hp with
    | .PHart c m' rs' fn' ib', hp =>
      obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := hp
      unfold wpSkipStep
      iintro %na Hna
      imodintro
      inext
      imodintro
      iexists ls
      iframe Hna Hloc
      iapply IH $$ %rs' %(regsAgreeTrans _ _ _ _ HP (regsAgreeSym _ _ _ hag)) F C
  · -- (d) row end: the store item sits at `k`
    iintro %Heq
    have h1 := lookup_lt_Some Hlb0
    simp only at Heq
    omega

/-- Store node → post-store `epure` run → `.pure ()`. -/
theorem wpdStoreThenRet (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat) (sW : ExecSt)
    (D : List Register) (data : List (BitVec 8)) (sEnd : ExecSt)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hdata : req.value.map (WeakInterpProj.wbytes n) = some data)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜storeRowOk GD i k⌝)
    (Hseip : Register.sig_seip ∉ D) (Hmeip : Register.sig_meip ∉ D)
    (Hep : epure D (KK (.Ok (some true))) sW = some ((), sEnd)) :
    ⊢ ∀ s2, ⌜Qat ⟨.PHart cpu (.impure (.ok (.memWrite n va req)) KK) sW.regs none ib, k⟩ s2⌝ -∗
      (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
         storeFlow GD i k data) -∗
      ((∀ (ib' : Ibch) (s' : Athread),
          ⌜Qat ⟨.PHart cpu (.pure ()) sEnd.regs none ib', k + 1⟩ s'⌝ -∗
          wpd .MaybeStuck i s' Φ) ∧
       (∀ (ib' : Ibch) (GD : Gdexec) (s1 : Athread),
          ⌜Pbefore ⟨.PHart cpu (.pure ()) sEnd.regs none ib', k + 1⟩ s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i s2 Φ := by
  iintro %s2 %Hq F R
  obtain ⟨p2, k2⟩ := s2
  obtain ⟨hk, hp⟩ := Hq
  simp only at hk hp
  subst k2
  match p2, hp with
  | .PHart c2 m2 rs2 fn2 ib2, hp =>
    obtain ⟨hc, hm, hf, hi, hag⟩ := hp
    subst c2 m2 fn2 ib2
    iapply (wpdStoreStep Φ i cpu n va req KK ib k sW.regs data Hdev Hlat Hdata Hrow) $$
      %rs2 %(regsAgreeSym _ _ _ hag) F
    iintro %rs' %hag'
    obtain ⟨ib', Hrun⟩ := epureGstepRtc D Hseip Hmeip _ _ _ _ Hep cpu ib (k + 1)
    iapply (wpdRunTo Φ i _ _ Hrun) $$
      %⟨.PHart cpu (KK (.Ok (some true))) rs' none ib, k + 1⟩
      %⟨rfl, rfl, rfl, rfl, rfl, regsAgreeSym _ _ _ hag'⟩
    isplit
    · icases R with ⟨R, -⟩
      iintro %s3 %Hq3
      iapply R $$ %ib' %s3 %Hq3
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %Hb %Hend
      iapply R $$ %ib' %GD %s1 %Hb %Hend

/-- Fetch (any width, bytes `vs`) → pre-store `gstep` run → the store. -/
theorem wpdFetchThenStore (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KKf : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (vs : List (BitVec 8)) (rs0 rs : RegFile) (nw vaw : Nat)
    (reqw : Mem_write_request nw vaw Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (ibW : Ibch) (tw : ExecSt)
    (D : List Register) (data : List (BitVec 8)) (sEnd : ExecSt)
    (Hdev : devAddr req.pa = false) (Hfe : (classify req.access_kind).akIfetch = true)
    (Hlen : vs.length = n)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i k (paZ req.pa) vs⌝)
    (Hag : regsAgree AxRunClose.pinReg rs0 rs)
    (HrunPre : rtc gstep
      ⟨.PHart cpu (KKf (.Ok (wordOfBytes n vs, none))) rs0 none ib, k⟩
      ⟨.PHart cpu (.impure (.ok (.memWrite nw vaw reqw)) KK) tw.regs none ibW, k⟩)
    (Hdevw : devAddr reqw.pa = false) (Hlatw : (classify reqw.access_kind).akLatest = false)
    (Hdata : reqw.value.map (WeakInterpProj.wbytes nw) = some data)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜storeRowOk GD i k⌝)
    (Hseip : Register.sig_seip ∉ D) (Hmeip : Register.sig_meip ∉ D)
    (Hep : epure D (KK (.Ok (some true))) tw = some ((), sEnd)) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
         storeFlow GD i k data) -∗
      (((∀ (ib' : Ibch) (s' : Athread),
           ⌜Qat ⟨.PHart cpu (.pure ()) sEnd.regs none ib', k + 1⟩ s'⌝ -∗
           wpd .MaybeStuck i s' Φ) ∧
        (∀ (ib' : Ibch) (GD : Gdexec) (s1 : Athread),
           ⌜Pbefore ⟨.PHart cpu (.pure ()) sEnd.regs none ib', k + 1⟩ s1⌝ -∗
           ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) ∧
       (∀ (GD : Gdexec) (s1 : Athread),
          ⌜Pbefore ⟨.PHart cpu (.impure (.ok (.memWrite nw vaw reqw)) KK) tw.regs none ibW, k⟩
            s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KKf) rs none ib, k⟩ Φ := by
  iintro F R
  iapply (wpdFetchStep Φ i cpu n va req KKf ib k vs rs0 Hdev Hfe Hlen Hgd) $$ %rs %Hag
  iintro %rs' %hag
  iapply (wpdRunTo Φ i _ _ HrunPre) $$
    %⟨.PHart cpu (KKf (.Ok (wordOfBytes n vs, none))) rs' none ib, k⟩
    %⟨rfl, rfl, rfl, rfl, rfl, regsAgreeSym _ _ _ hag⟩
  isplit
  · icases R with ⟨R, -⟩
    iintro %s3 %Hq3
    iapply (wpdStoreThenRet Φ i cpu nw vaw reqw KK ibW k tw D data sEnd Hdevw Hlatw Hdata Hrow
      Hseip Hmeip Hep) $$ %s3 %Hq3 F R
  · icases R with ⟨-, R⟩
    iexact R

/-- THE WHOLE-INSTRUCTION `wpd` OF A DATA STORE FROM THE STORE LEDGER. -/
theorem wpdCsdspStepOfLedger (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch)
    (kk : Nat) (t : ExecSt) (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (staddr : Int) (data : List (BitVec 8)) (post : RegFile → Bool)
    (L : AxSdModelFacts t Dr Dw D base vs staddr data post)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk base vs⌝)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜storeRowOk GD i kk⌝) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i kk ls -∗
         storeFlow GD i kk data) -∗
      ((∀ s', ⌜RetS cpu post (kk + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1, ⌜ledgerSdInv t Dr Dw D vs cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) t.regs none ib, kk⟩ Φ := by
  have HDr := of_decide_eq_false L.lsSeipDr
  have HDrm := of_decide_eq_false L.lsMeipDr
  have HD := of_decide_eq_false L.lsSeipD
  have HDm := of_decide_eq_false L.lsMeipD
  obtain ⟨km, t0, Hts⟩ := AxEpiLedger.seipAtSpec t L.lsToSeip
  have Hnext := AxEpiLedger.seipAtNext t km t0 L.lsToSeip Hts
  obtain ⟨ib0, Hr0⟩ := AxEpiLedger.toPinGstep _ t ib _ _ Hts cpu kk
  iintro F R
  iapply (AxEpiLedger.wpdOfSplitFrom i Φ _ _ _
    (AxEpiLedger.pseipStart cpu _ t.regs ib kk _ (AxEpiLedger.seipExit cpu km t0 kk) Hr0)
    (AxEpiLedger.meipN0Ok cpu km t0 ib0 kk Hnext))
  isplit
  · iintro %s2 %HQ
    obtain ⟨q, ⟨v', k0, t1, ib1, Hts1, rfl⟩, Hq⟩ := HQ
    have Hb := sdLedgerBranch t Dr Dw D base vs staddr data post km t0 v' k0 t1 L Hts Hts1
    iapply (AxEpiLedger.wpdOfSplitFrom i Φ s2 _ (erdExit Dr Dw cpu k0 t1 kk) (.inr (.inl Hq))
      (AxEpiLedger.seipN0Ok cpu k0 t1 ib1 kk Dr Dw HDr HDrm
        (fun v => AxEpiLedgerSd.erdOfSdBranch Dr Dw D base vs staddr data post _ t1 (Hb v))))
    isplit
    · iintro %s3 %HQ3
      obtain ⟨q3, ⟨v, qm, t2, ib2, He, rfl, -⟩, Hs3⟩ := HQ3
      have Hbv := Hb v
      unfold sdBranchOk at Hbv
      rw [He] at Hbv
      obtain ⟨n, va, req, KKf, rfl⟩ := sdFetchOkShape _ _ _ _ _ _ _ _ _ _ Hbv
      obtain ⟨Hdev, Hfe, Hpa, Hlen, mw, tw, He2, Hs⟩ := sdFetchOkNode _ _ _ _ _ _ _ _ _ _ _ _ _ Hbv
      obtain ⟨nw, vaw, reqw, KK, rfl⟩ := sdStoreOkShape _ _ _ _ _ _ Hs
      obtain ⟨Hdevw, Hlatw, -, Hdataw, t3, Hep, Hpost⟩ := sdStoreOkNode _ _ _ _ _ _ _ _ _ Hs
      subst Hpa
      obtain ⟨p3, k3⟩ := s3
      obtain ⟨hk, hp⟩ := Hs3
      simp only at hk hp
      subst k3
      match p3, hp with
      | .PHart c3 m3 rs3 fn3 ib3', hp =>
        obtain ⟨hc, hm, hf, hi, hag⟩ := hp
        subst c3 m3 fn3 ib3'
        obtain ⟨ibW, HrunPre⟩ := ewrGstep Dr Dw _ HDr HDrm t2 ib2 _ _ He2 cpu kk
        iapply (wpdFetchThenStore Φ i cpu n va req KKf ib2 kk vs t2.regs rs3 nw vaw reqw KK ibW
          tw D data t3 Hdev Hfe Hlen Hgd (regsAgreeSym _ _ _ hag) HrunPre Hdevw Hlatw Hdataw
          Hrow HD HDm Hep) $$ F
        isplit
        · isplit
          · icases R with ⟨R, -⟩
            iintro %ib3 %s' %Hs'
            iapply R $$ %s' %⟨t3.regs, ib3, Hpost, Hs'⟩
          · icases R with ⟨-, R⟩
            iintro %ib3 %GD %s1 %Hs1 %Hlen1
            iapply R $$ %GD %s1
              %⟨km, t0, ib0, Hts, .inr ⟨v', k0, t1, ib1, Hts1,
                .inr ⟨v, n, va, req, KKf, t2, nw, vaw, reqw, KK, tw, ibW, He, He2,
                  .inr ⟨t3, ib3, Hep, Hs1⟩⟩⟩⟩ %Hlen1
        · icases R with ⟨-, R⟩
          iintro %GD %s1 %Hs1 %Hlen1
          iapply R $$ %GD %s1
            %⟨km, t0, ib0, Hts, .inr ⟨v', k0, t1, ib1, Hts1,
              .inr ⟨v, n, va, req, KKf, t2, nw, vaw, reqw, KK, tw, ibW, He, He2, .inl Hs1⟩⟩⟩
            %Hlen1
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %Hs1 %Hlen1
      iapply R $$ %GD %s1 %⟨km, t0, ib0, Hts, .inr ⟨v', k0, t1, ib1, Hts1, .inl Hs1⟩⟩ %Hlen1
  · icases R with ⟨-, R⟩
    iintro %GD %s1 %Hs1 %Hlen1
    iapply R $$ %GD %s1 %⟨km, t0, ib0, Hts, .inl Hs1⟩ %Hlen1

end store

/-! # 4. The concrete instance: c.sdsp ra,8(sp) at `pcSd` -/

/-- The 4-byte fetch at the 4-aligned `pcSd`: c.sdsp (`0xe406`) then c.ldsp (`0x60a2`),
little-endian. -/
def sdVs : List (BitVec 8) := [0x06#8, 0xe4#8, 0xa2#8, 0x60#8]

def sdAddr : Int := (spVal : Int) + 8

/-- The stored bytes: `raVal = 0x80000100`, 8 bytes little-endian. -/
def sdData : List (BitVec 8) :=
  [0x00#8, 0x01#8, 0x00#8, 0x80#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8]

/-- Post-store: the PC has advanced past the 2-byte instruction. -/
def sdPost (rs : RegFile) : Bool := decide ((rs .PC).toNat = pcSd + 2)

theorem epiLedgerCsdsp :
    AxSdModelFacts (tAt pcSd) AxEpiProbe.drNopin DwAll DPost (pcSd : Int) sdVs sdAddr sdData
      sdPost where
  lsSeipDr := by decide +kernel
  lsMeipDr := by decide +kernel
  lsSeipD := by decide +kernel
  lsMeipD := by decide +kernel
  lsHead := by decide +kernel
  lsToSeip := by decide +kernel
  lsBranch00 := by decide +kernel
  lsBranch01 := by decide +kernel
  lsBranch10 := by decide +kernel
  lsBranch11 := by decide +kernel

section sdConcrete
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem wpdCsdspConcrete (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch) (kk : Nat)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk (pcSd : Int) sdVs⌝)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜storeRowOk GD i kk⌝) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i kk ls -∗
         storeFlow GD i kk sdData) -∗
      ((∀ s', ⌜RetS cpu sdPost (kk + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜ledgerSdInv (tAt pcSd) AxEpiProbe.drNopin DwAll DPost sdVs cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ib, kk⟩ Φ :=
  wpdCsdspStepOfLedger i Φ cpu ib kk (tAt pcSd) _ _ _ _ _ _ _ _ epiLedgerCsdsp Hgd Hrow

end sdConcrete

end Weak
