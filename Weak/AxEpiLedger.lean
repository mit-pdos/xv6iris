/-
Weak: **THE FIRST WHOLE-INSTRUCTION `wpd` FOR A REAL `riscvStep`**: `c.jr ra` at a concrete
M-mode state (`tAt pcJr2`), from the instruction boundary `riscvStep false` to the monad's
`.pure ()`, with every model-side fact closed by the kernel; and the same for the data load
`c.ldsp ra,8(sp)` at `tAt pcLd`.

Rocq: `iris/AxEpiLedger.v` @ xxvzwolszwmp.

## The Rocq header, in substance

THE LEDGER (`AxEpiModelFacts`): the model facts the composition needs, each a closed boolean
equation on the concrete start state (pins outside the footprints, the boundary walk reaches the
pin read, and for EVERY answer of the pin reads `erd` reaches a RAM fetch node at `base` of
`vs.length` bytes whose continuation fed `vs` has an `epure D` certificate ending in `post`).  The
instruction bytes `vs` are a PARAMETER (in the axiomatic semantics the fetch value is the image's,
`Hgd`).  COMPOSITION `wpdCjrStepOfLedger`: boundary split(s) → fetch (`wpdFetchThenRunAgree`) →
post-fetch (`epureGstepRtc`) → `.pure ()`, registers satisfying `post`; the caller supplies the
continuation at `RetS` and the ROW-END obligation, stated only on the invariant `ledgerInv` the
proof actually uses.  Sanity: `ledgerInvReachesRet`.  §5 does the same for `c.ldsp`
(`AxLdModelFacts`, `ledgerLdInv`, `ledgerLdInvReachesRet`, `wpdCldspStepOfLedger`,
`epiLedgerCldsp`, `wpdCldspConcrete`).  OUT OF SCOPE (as Rocq): `riscvStep true` (the tick re-reads
the pins after the fetch).  NON-VACUITY: every branch is certified to REACH `.pure ()`.

## Deviations from Rocq

1. TWO WIRE-READ NODES AT THE BOUNDARY (Lean model).  Lean's `external_interrupts_pending` reads
   `sig_meip` and THEN `sig_seip` (`AxEpiProbe`'s finding), and `AxRunClose.nodeOk` excludes reads
   of BOTH pins, so Rocq's single `to_seip` prefix is not a `gstep` run in Lean.  The boundary is
   split TWICE: at the `sig_meip` node (Lean-only `AxEpiLedger.meipNode`, exit set
   `AxEpiLedger.seipExit` = the `sig_seip` nodes reached per answer `v'`) and then, from each exit,
   at the `sig_seip` node (`erdExit`, as Rocq), both via the Lean-only
   `AxEpiLedger.wpdOfSplitFrom` (`wpdOfSeipSplit` from any start in the invariant).  The walk is the
   Lean-only `AxEpiLedger.toPin` (stops at either pin, fails at an sfence.vma announce, Q7), with
   bridge `AxEpiLedger.toPinGstep` replacing Rocq's `to_seip_gstep`.  Consequently:
   `seipAt` checks the meip node and the seip node after BOTH meip answers; `branchAt` takes two
   answers `v' v`; the ledgers have four branch fields `lfBranch00/01/10/11` (`lgBranch..`; Rocq
   `lf_branch0/1`, first index = meip answer); `ledgerInv`/`ledgerLdInv` add the meip-level
   `Pseip` disjunct and quantify the seip node per meip answer; `AxEpiLedger.ledgerStep` has a
   fourth disjunct (answer a `sig_meip` read).  `lfHead`/`lgHead` are kept verbatim (unused).
2. THE PINS (`AxRunClose` deviation 1): the ledgers add `lfMeipDr`/`lfMeipD` (`lg..`);
   `ledgerFetchReaches` & co. take both `∉ D`; `DPost` removes BOTH pins (Rocq only `sig_seip`);
   the concrete instances use `AxEpiProbe.drNopin` for Rocq's `Dr_noseip`.
3. O2 STAGE C (`AxCjrWpd` deviation 1): the fetch is a pinned admin step at the SAME row position.
   `fetchOk`/`ldFetchOk` check `akIfetch = true` (Rocq `negb ak_latest`); `Hgd` states
   `AxCjrWpd.fetchImgOk` (Rocq `fetch_gd_ok`); `Hflow`/`Hloc` are dropped; positions: `RetS` and
   the post-fetch `Pbefore` at `kk` (Rocq `S kk`); load node, `Hrow`, the flow `F` at `kk` and
   `RetLd`/post-load at `kk + 1` (Rocq `S kk`, `S (S kk)`); `ledgerStep`'s fetch keeps `k`.
   `ldLoadOk` adds `akIfetch = false` (the Lean form of Rocq's `Hntext : ¬ ax_text ldaddr`, which
   is therefore dropped from `wpdCldspStepOfLedger`/`wpdCldspConcrete`); `wpdLoadThenRetN` takes
   `Hnf` for `Hntext`.
4. TYPES (as `AxCjrWpd` deviation 3): `mstate` ↦ `ExecSt`, `regstate` ↦ `RegFile`, `gset` ↦
   `List Register`, `bool_decide` ↦ `decide`, `Interface.ReadReq.t n` ↦ `Mem_read_request n va …`
   (new bound `va`), `inl (w, None)` ↦ `.Ok (w, none)`, `N.to_nat n` ↦ `n`, `Ret tt` ↦
   `.pure ()`, `bv 1` answers ↦ `BitVec 1` (`BV 1 0/1` ↦ `0#1/1#1`), `register_lookup r
   (register_set sig_seip v init_regstate)` ↦ `(zeroRegs.set .sig_seip v) r`; Rocq's `dir` flag is
   gone (lean-sail `regRead`).  Post-load predicates are `Int → RegFile → Prop` applied to
   `x.toNat` (Rocq `Z`, `bv_unsigned x`); `ldLoadReaches` uses the word `0`.
   `WPd … @ MaybeStuck; i {{ Φ }}` ↦ `wpd .MaybeStuck i s Φ`; `invGS_gen HasNoLc Σ` ↦
   `[InvGS_gen hlc GF]`; `A -∗ B` ↦ `⊢ A -∗ B`.
5. `vm_compute` ↦ `decide +kernel` for the closed boolean fields.  The load ledger's branch fields
   quantify over the loaded word, so they are proved through Lean-only boolean twins at ONE free
   64-bit word (`AxEpiLedger.ldLoadB/ldFetchB/ldBranchB/ldBranchAtB`, the node width checked `= 8`
   and the word `BitVec.cast` to it), checked by the kernel with the word free (tactic
   `ax_epi_ledger_krfl`, the `weak_adm_krfl` mechanism under a file-specific name), and the bridges
   `AxEpiLedger.ldLoadOfB/ldFetchOfB/ldBranchOfB/ldBranchAtOfB` (+ `ldPostB`/`ldPostOfB`).
6. Duplicated names file-qualified: `AxEpiLedger.ledgerInv`, `AxEpiLedger.ledgerStep`,
   `AxEpiLedger.ldVs`.  Other Lean-only helpers (file-qualified): `ansMeip`, `isMeipNode`,
   `isMeipNodeShape`, `ansSeipNode`, `ansMeipNode`, `seipAfter`, `seipAtSpec`, `seipAtNext`,
   `branchAtEq`, `ldBranchAtEq`, `seipReaches`, `meipReaches`, `ldSeipReaches`, `ldMeipReaches`,
   `n0OkMeipRead`, `pseipStart`, `meipN0Ok`, `seipN0Ok`, `erdOfBranch` (all `AxEpiLedger.*`).

**Rocq → Lean name map.**  `ans_seip` `ansSeip`, `fetch_ok` `fetchOk`, `branch_ok` `branchOk`,
`seip_at` `seipAt`, `branch_at` `branchAt`, `AxEpiModelFacts` `AxEpiModelFacts` (fields
`lfSeipDr`, `lfSeipD`, `lfHead`, `lfToSeip`, `lfBranch00..11`), `bv1_cases` `bv1Cases`,
`is_seip_node_shape` `isSeipNodeShape`, `fetch_ok_spec` `fetchOkSpec`, `to_seip_gstep`
`AxEpiLedger.toPinGstep` (deviation 1), `tc_gstep_at_k` `tcGstepAtK`, `pbefore_at_k`
`pbeforeAtK`, `pseip_erd_at_k` `pseipErdAtK`, `RetS` `RetS`, `aeqv_hart_refl` `aeqvHartRefl`,
`ledger_inv` `AxEpiLedger.ledgerInv`, `ledger_step` `AxEpiLedger.ledgerStep`,
`rtc_gstep_ledger_step` `rtcGstepLedgerStep`, `fetch_ok_mem` `fetchOkMem`, `ledger_branch`
`ledgerBranch`, `ledger_fetch_reaches` `ledgerFetchReaches`, `ledger_branch_reaches`
`ledgerBranchReaches`, `ledger_inv_reaches_ret` `ledgerInvReachesRet`,
`wpd_fetch_then_run_agree` `wpdFetchThenRunAgree`, `wpd_cjr_step_of_ledger`
`wpdCjrStepOfLedger`, `cjr_vs` `cjrVs`, `post_ra` `postRa`, `D_post` `DPost`, `epi_ledger_cjr`
`epiLedgerCjr`, `wpd_cjr_concrete` `wpdCjrConcrete`, `ld_load_ok` `ldLoadOk`, `ld_fetch_ok`
`ldFetchOk`, `ld_branch_ok` `ldBranchOk`, `ld_branch_at` `ldBranchAt`, `AxLdModelFacts`
`AxLdModelFacts` (`lg*`), `RetLd` `RetLd`, `ledger_ld_inv` `ledgerLdInv`, `ld_step` `ldStep`,
`rtc_gstep_ld_step` `rtcGstepLdStep`, `ld_load_ok_node` `ldLoadOkNode`, `ld_fetch_ok_node`
`ldFetchOkNode`, `ld_branch_ok_node` `ldBranchOkNode`, `ld_ledger_branch` `ldLedgerBranch`,
`ld_load_reaches` `ldLoadReaches`, `ld_fetch_reaches` `ldFetchReaches`, `ld_branch_reaches`
`ldBranchReaches`, `ledger_ld_inv_reaches_ret` `ledgerLdInvReachesRet`, `wpd_load_then_ret_n`
`wpdLoadThenRetN`, `wpd_fetch_then_load` `wpdFetchThenLoad`, `wpd_cldsp_step_of_ledger`
`wpdCldspStepOfLedger`, `ld_vs` `AxEpiLedger.ldVs`, `ld_addr` `ldAddr`, `ld_post` `ldPost`,
`epi_ledger_cldsp` `epiLedgerCldsp`, `wpd_cldsp_concrete` `wpdCldspConcrete`.

**Dropped:** nothing (Rocq 55 definitions/lemmas; Lean 55, `to_seip_gstep` restated over
`toPin`, + 33 Lean-only + the tactic).  **Not ported:** the `Print Assumptions` block (the lint's
axiom check covers it).
-/
import Weak.AxLdspWpd
import Weak.AxEpiProbe

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

open Lean Elab Tactic Meta in
/-- (Lean-only) Close `lhs = rhs` by KERNEL defeq: `Eq.refl lhs` as an auxiliary theorem
abstracted over the local context (the `WeakRvwmoAdm.weak_adm_krfl` mechanism, re-declared under
a file-specific name so this file need not import `WeakRvwmoAdm`). -/
elab "ax_epi_ledger_krfl" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    let some (_, lhs, _) := tgt.eq? | throwError "ax_epi_ledger_krfl: the goal is not an equation"
    let pf ← mkEqRefl lhs
    let aux ← mkAuxTheorem tgt pf
    g.assign aux
    replaceMainGoal []

/-! # 1. The computable checkers -/

/-- Answer the head `regRead` of `m0` as if `sig_seip` held `v`. -/
def ansSeip (m0 : SailM Unit) (v : BitVec 1) : SailM Unit :=
  match m0 with
  | .impure (.ok (.regRead r)) k => k ((zeroRegs.set Register.sig_seip v) r)
  | _ => m0

/-- (Lean-only) Answer the head `regRead` of `m0` as if `sig_meip` held `v`. -/
def AxEpiLedger.ansMeip (m0 : SailM Unit) (v : BitVec 1) : SailM Unit :=
  match m0 with
  | .impure (.ok (.regRead r)) k => k ((zeroRegs.set Register.sig_meip v) r)
  | _ => m0

/-- (Lean-only) Is `m` the `sig_meip` read node? -/
def AxEpiLedger.isMeipNode (m : SailM Unit) : Bool :=
  match m with
  | .impure (.ok (.regRead r)) _ => decide (r = .sig_meip)
  | _ => false

/-- (Lean-only) `toSeip`, stopping at the FIRST read of EITHER pin (and failing at an
sfence.vma announce, Q7): the prefix it walks is a `gstep` run (`AxEpiLedger.toPinGstep`). -/
def AxEpiLedger.toPin : SailM Unit → ExecSt → Option (SailM Unit × ExecSt)
  | .pure _, _ => none
  | .impure (.error _) _, _ => none
  | .impure (.ok o) k, t =>
    match o, k with
    | .regRead r, k =>
      if r = .sig_seip ∨ r = .sig_meip then some (.impure (.ok (.regRead r)) k, t)
      else AxEpiLedger.toPin (k (t.regs r)) t
    | .regWrite r v, k => AxEpiLedger.toPin (k PUnit.unit) (t.setReg r v)
    | .instrAnnounce n w, k => if sfAnnB n w then none else AxEpiLedger.toPin (k ()) t
    | .branchAnnounce _ _, k => AxEpiLedger.toPin (k ()) t
    | .cacheOp _, k => AxEpiLedger.toPin (k ()) t
    | .tlbi _, k => AxEpiLedger.toPin (k ()) t
    | .takeException _, k => AxEpiLedger.toPin (k ()) t
    | .returnException _, k => AxEpiLedger.toPin (k ()) t
    | .translationStart _, k => AxEpiLedger.toPin (k ()) t
    | .translationEnd _, k => AxEpiLedger.toPin (k ()) t
    | .cycleCount, k => AxEpiLedger.toPin (k ()) t
    | .message _, k => AxEpiLedger.toPin (k ()) t
    | .getCycleCount, k => AxEpiLedger.toPin (k (0 : Nat)) t
    | _, _ => none

/-- The `erd`-returned node is a RAM FETCH (`akIfetch`) at `base` of `vs.length` bytes, and the
post-fetch continuation fed `vs` is `epure D` to a `post` state. -/
def fetchOk (D : List Register) (base : Int) (vs : List (BitVec 8)) (post : RegFile → Bool)
    (mf : SailM Unit) (t2 : ExecSt) : Bool :=
  match mf with
  | .impure (.ok (.memRead n _ req)) KK =>
    !devAddr req.pa && (classify req.access_kind).akIfetch &&
    decide (paZ req.pa = base) && decide (vs.length = n) &&
    match epure D (KK (.Ok (wordOfBytes n vs, none))) t2 with
    | some (_, t3) => post t3.regs
    | none => false
  | _ => false

def branchOk (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (post : RegFile → Bool) (m : SailM Unit) (t1 : ExecSt) : Bool :=
  match erd Dr Dw m t1 with
  | some (mf, t2) => fetchOk D base vs post mf t2
  | none => false

/-- (Lean-only) After answering the `sig_meip` node `m0` with `v'`, the walk reaches the
`sig_seip` node. -/
def AxEpiLedger.seipAfter (m0 : SailM Unit) (t0 : ExecSt) (v' : BitVec 1) : Bool :=
  match AxEpiLedger.toPin (AxEpiLedger.ansMeip m0 v') t0 with
  | some (m1, _) => isSeipNode m1
  | none => false

/-- The boundary walk: the first pin read is `sig_meip`, and for BOTH of its answers the next
pin read is `sig_seip` (Lean: two wire-read nodes, deviation 1). -/
noncomputable def seipAt (t : ExecSt) : Bool :=
  match AxEpiLedger.toPin (riscvStep false) t with
  | some (m0, t0) =>
    AxEpiLedger.isMeipNode m0 && AxEpiLedger.seipAfter m0 t0 0#1 &&
      AxEpiLedger.seipAfter m0 t0 1#1
  | none => false

/-- The branch for the answers `v'` (of `sig_meip`) and `v` (of `sig_seip`). -/
noncomputable def branchAt (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (post : RegFile → Bool) (t : ExecSt) (v' v : BitVec 1) : Bool :=
  match AxEpiLedger.toPin (riscvStep false) t with
  | some (m0, t0) =>
    match AxEpiLedger.toPin (AxEpiLedger.ansMeip m0 v') t0 with
    | some (m1, t1) => branchOk Dr Dw D base vs post (ansSeip m1 v) t1
    | none => false
  | none => false

/-- THE LEDGER. -/
structure AxEpiModelFacts (t : ExecSt) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (post : RegFile → Bool) : Prop where
  lfSeipDr : decide (Register.sig_seip ∈ Dr) = false
  lfMeipDr : decide (Register.sig_meip ∈ Dr) = false
  lfSeipD : decide (Register.sig_seip ∈ D) = false
  lfMeipD : decide (Register.sig_meip ∈ D) = false
  lfHead : isSeipNode (riscvStep false) = false
  lfToSeip : seipAt t = true
  lfBranch00 : branchAt Dr Dw D base vs post t 0#1 0#1 = true
  lfBranch01 : branchAt Dr Dw D base vs post t 0#1 1#1 = true
  lfBranch10 : branchAt Dr Dw D base vs post t 1#1 0#1 = true
  lfBranch11 : branchAt Dr Dw D base vs post t 1#1 1#1 = true

/-! # 2. Pure bridges -/

theorem bv1Cases (v : BitVec 1) : v = 0#1 ∨ v = 1#1 := by
  bv_omega

theorem isSeipNodeShape (m0 : SailM Unit) :
    isSeipNode m0 = true →
    ∃ k0 : RegisterType Register.sig_seip → SailM Unit,
      m0 = .impure (.ok (.regRead Register.sig_seip)) k0 := by
  intro H
  cases m0 with
  | pure _ => exact absurd H Bool.false_ne_true
  | impure call k =>
    cases call with
    | error _ => exact absurd H Bool.false_ne_true
    | ok o =>
      cases o
      case regRead r =>
        simp only [isSeipNode, decide_eq_true_eq] at H
        subst H
        exact ⟨k, rfl⟩
      all_goals exact absurd H Bool.false_ne_true

/-- (Lean-only) `isSeipNodeShape` for the `sig_meip` node. -/
theorem AxEpiLedger.isMeipNodeShape (m0 : SailM Unit) :
    AxEpiLedger.isMeipNode m0 = true →
    ∃ km : RegisterType Register.sig_meip → SailM Unit,
      m0 = .impure (.ok (.regRead Register.sig_meip)) km := by
  intro H
  cases m0 with
  | pure _ => exact absurd H Bool.false_ne_true
  | impure call k =>
    cases call with
    | error _ => exact absurd H Bool.false_ne_true
    | ok o =>
      cases o
      case regRead r =>
        simp only [AxEpiLedger.isMeipNode, decide_eq_true_eq] at H
        subst H
        exact ⟨k, rfl⟩
      all_goals exact absurd H Bool.false_ne_true

/-- (Lean-only) Answering the `sig_seip` node. -/
theorem AxEpiLedger.ansSeipNode (k0 : RegisterType Register.sig_seip → SailM Unit)
    (v : BitVec 1) : ansSeip (.impure (.ok (.regRead Register.sig_seip)) k0) v = k0 v := by
  simp only [ansSeip, RegFile.set_same]

/-- (Lean-only) Answering the `sig_meip` node. -/
theorem AxEpiLedger.ansMeipNode (km : RegisterType Register.sig_meip → SailM Unit)
    (v : BitVec 1) :
    AxEpiLedger.ansMeip (.impure (.ok (.regRead Register.sig_meip)) km) v = km v := by
  simp only [AxEpiLedger.ansMeip, RegFile.set_same]

theorem fetchOkSpec (D : List Register) (base : Int) (vs : List (BitVec 8))
    (post : RegFile → Bool) (mf : SailM Unit) (t2 : ExecSt) :
    fetchOk D base vs post mf t2 = true →
    ∃ (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (t3 : ExecSt),
      mf = .impure (.ok (.memRead n va req)) KK ∧ devAddr req.pa = false ∧
      (classify req.access_kind).akIfetch = true ∧ paZ req.pa = base ∧ vs.length = n ∧
      epure D (KK (.Ok (wordOfBytes n vs, none))) t2 = some ((), t3) ∧
      post t3.regs = true := by
  intro H
  cases mf with
  | pure _ => exact absurd H Bool.false_ne_true
  | impure call KK =>
    cases call with
    | error _ => exact absurd H Bool.false_ne_true
    | ok o =>
      cases o
      case memRead n va req =>
        cases he : epure D (KK (.Ok (wordOfBytes n vs, none))) t2 with
        | none => simp [fetchOk, he] at H
        | some p =>
          obtain ⟨⟨⟩, t3⟩ := p
          simp only [fetchOk, he, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at H
          obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := H
          exact ⟨n, va, req, KK, t3, rfl, h1, h2, h3, h4, he, h5⟩
      all_goals exact absurd H Bool.false_ne_true

/-- The prefix bridge (Lean: over `AxEpiLedger.toPin`, deviation 1): a `toPin` run is a `gstep`
run to the pin node (mirror of `AxBoundaryWpd.erdGstep`). -/
theorem AxEpiLedger.toPinGstep (m : SailM Unit) :
    ∀ (t : ExecSt) (ib : Ibch) (m0 : SailM Unit) (t1 : ExecSt),
      AxEpiLedger.toPin m t = some (m0, t1) →
    ∀ (cpu : CPU) (kk : Nat), ∃ ib1,
      rtc gstep (⟨.PHart cpu m t.regs none ib, kk⟩ : Athread)
        ⟨.PHart cpu m0 t1.regs none ib1, kk⟩ := by
  induction m with
  | pure x =>
    intro t ib m0 t1 hex
    simp [AxEpiLedger.toPin] at hex
  | impure call k ih =>
    intro t ib m0 t1 hex cpu kk
    cases call with
    | error e => simp [AxEpiLedger.toPin] at hex
    | ok o =>
      cases o
      case regRead r =>
        by_cases hr : r = .sig_seip ∨ r = .sig_meip
        · simp only [AxEpiLedger.toPin, if_pos hr, Option.some.injEq, Prod.mk.injEq] at hex
          obtain ⟨rfl, rfl⟩ := hex
          exact ⟨ib, rtc_refl _⟩
        · simp only [AxEpiLedger.toPin, if_neg hr] at hex
          obtain ⟨ib1, hrun⟩ := ih _ t (ibRd ib r) _ _ hex cpu kk
          exact ⟨ib1, rtc_l (gstepRd cpu r k t.regs ib kk hr) hrun⟩
      case regWrite r v =>
        simp only [AxEpiLedger.toPin] at hex
        obtain ⟨ib1, hrun⟩ := ih _ _ ib _ _ hex cpu kk
        exact ⟨ib1, rtc_l (gstepWr cpu r v k t.regs ib kk) hrun⟩
      case instrAnnounce nw w =>
        cases hsw : sfAnnB nw w <;>
          simp only [AxEpiLedger.toPin, hsw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hex
        obtain ⟨ib1, hrun⟩ := ih _ t (ibAnn (ibOfBvn w)) _ _ hex cpu kk
        exact ⟨ib1,
          rtc_l (gstepOfPnode cpu _ t.regs ib kk _ _ none (some (ibAnn (ibOfBvn w))) none
            ⟨(annLabelNot hsw).symm, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial rfl) hrun⟩
      all_goals first
        | (simp [AxEpiLedger.toPin] at hex; done)
        | (simp only [AxEpiLedger.toPin] at hex
           obtain ⟨ib1, hrun⟩ := ih _ t ib _ _ hex cpu kk
           exact ⟨ib1,
             rtc_l (gstepOfPnode cpu _ t.regs ib kk _ _ none none none
               ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial trivial) hrun⟩)

theorem tcGstepAtK (s q : Athread) (h : tc gstep s q) : q.atK = s.atK := by
  induction h with
  | single h => exact h.2.1
  | tail _ h2 ih => exact h2.2.1.trans ih

theorem pbeforeAtK (q s : Athread) : Pbefore q s → s.atK = q.atK := by
  rintro ⟨t, ⟨hk, -⟩, htc⟩
  exact hk.trans (tcGstepAtK _ _ htc).symm

theorem pseipErdAtK (cpu : CPU) (k0 : RegisterType Register.sig_seip → SailM Unit)
    (rs1 : RegFile) (ib1 : Ibch) (kk : Nat) (Dr Dw : List Register) (t1 : ExecSt)
    (s : Athread) :
    Pseip (seipNode cpu k0 rs1 ib1 kk) (erdExit Dr Dw cpu k0 t1 kk) s → s.atK = kk := by
  rintro (H | H | ⟨q, ⟨v, qm, t2, ib2, -, rfl, -⟩, H⟩)
  · exact pbeforeAtK _ _ H
  · exact H.1
  · exact pbeforeAtK _ _ H

/-- The `.pure ()` set the whole instruction exits at. -/
def RetS (cpu : CPU) (post : RegFile → Bool) (k : Nat) (s : Athread) : Prop :=
  ∃ (rs3 : RegFile) (ib' : Ibch), post rs3 = true ∧
    Qat ⟨.PHart cpu (.pure ()) rs3 none ib', k⟩ s

theorem aeqvHartRefl (c : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (k : Nat) :
    aeqv ⟨.PHart c m rs fn ib, k⟩ ⟨.PHart c m rs fn ib, k⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl, regsAgreeRefl _ rs⟩

/-- (Lean-only) The `sig_meip` read node (the FIRST wire-read node of the Lean boundary). -/
def AxEpiLedger.meipNode (cpu : CPU) (km : RegisterType Register.sig_meip → SailM Unit)
    (rs : RegFile) (ib : Ibch) (kk : Nat) : Athread :=
  ⟨.PHart cpu (.impure (.ok (.regRead Register.sig_meip)) km) rs none ib, kk⟩

/-- (Lean-only) The exit set of the `sig_meip` split: the `sig_seip` nodes the walk reaches
after some answer `v'`. -/
def AxEpiLedger.seipExit (cpu : CPU) (km : RegisterType Register.sig_meip → SailM Unit)
    (t0 : ExecSt) (kk : Nat) (q : Athread) : Prop :=
  ∃ (v' : BitVec 1) (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt)
    (ib1 : Ibch),
    AxEpiLedger.toPin (km v') t0 = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) ∧
    q = seipNode cpu k0 t1.regs ib1 kk

/-- THE ROW-END INVARIANT: the union of the reachable-invariant sets on which the composition
actually demands `postLifting` — the `sig_meip` split's `Pseip`, the `sig_seip` split's `Pseip`
(per `sig_meip` answer), and the post-fetch `Pbefore` of the certified `.pure ()` node. -/
def AxEpiLedger.ledgerInv (t : ExecSt) (Dr Dw D : List Register) (vs : List (BitVec 8))
    (cpu : CPU) (kk : Nat) (s1 : Athread) : Prop :=
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
          (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit)
          (t2 t3 : ExecSt) (ib3 : Ibch),
          erd Dr Dw (k0 v) t1 = some (.impure (.ok (.memRead n va req)) KK, t2) ∧
          epure D (KK (.Ok (wordOfBytes n vs, none))) t2 = some ((), t3) ∧
          Pbefore ⟨.PHart cpu (.pure ()) t3.regs none ib3, kk⟩ s1))

/-- The abstract "run" relation for the sanity lemma: a `gstep`, OR answering a `sig_seip` read
with any `v`, OR performing a RAM fetch that returns the ledger's bytes `vs` (Lean: at the SAME
row position), OR (Lean-only) answering a `sig_meip` read with any `v`. -/
def AxEpiLedger.ledgerStep (cpu : CPU) (vs : List (BitVec 8)) (s s' : Athread) : Prop :=
  gstep s s' ∨
  (∃ (k0 : RegisterType Register.sig_seip → SailM Unit) (rs : RegFile) (ib : Ibch)
     (v : BitVec 1) (ib' : Ibch) (k : Nat),
     s = seipNode cpu k0 rs ib k ∧ s' = ⟨.PHart cpu (k0 v) rs none ib', k⟩) ∨
  (∃ (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
     (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
     (ib ib' : Ibch) (k : Nat),
     s = ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ ∧
     s' = ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs none ib', k⟩) ∨
  (∃ (km : RegisterType Register.sig_meip → SailM Unit) (rs : RegFile) (ib : Ibch)
     (v : BitVec 1) (ib' : Ibch) (k : Nat),
     s = AxEpiLedger.meipNode cpu km rs ib k ∧ s' = ⟨.PHart cpu (km v) rs none ib', k⟩)

theorem rtcGstepLedgerStep (cpu : CPU) (vs : List (BitVec 8)) (s s' : Athread) :
    rtc gstep s s' → rtc (AxEpiLedger.ledgerStep cpu vs) s s' :=
  rtc_subrel (fun _ _ h => .inl h)

theorem fetchOkMem (D : List Register) (base : Int) (vs : List (BitVec 8))
    (post : RegFile → Bool) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (t2 t3 : ExecSt) :
    fetchOk D base vs post (.impure (.ok (.memRead n va req)) KK) t2 = true →
    epure D (KK (.Ok (wordOfBytes n vs, none))) t2 = some ((), t3) →
    post t3.regs = true := by
  intro H Hep
  simp only [fetchOk, Hep, Bool.and_eq_true] at H
  exact H.2

/-- (Lean-only) The `seipAt` walk: the first pin node is the `sig_meip` read. -/
theorem AxEpiLedger.seipAtSpec (t : ExecSt) (H : seipAt t = true) :
    ∃ (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt),
      AxEpiLedger.toPin (riscvStep false) t
        = some (.impure (.ok (.regRead Register.sig_meip)) km, t0) := by
  unfold seipAt at H
  cases h : AxEpiLedger.toPin (riscvStep false) t with
  | none => rw [h] at H; exact absurd H Bool.false_ne_true
  | some p =>
    obtain ⟨m0, t0⟩ := p
    rw [h] at H
    simp only [Bool.and_eq_true] at H
    obtain ⟨km, rfl⟩ := AxEpiLedger.isMeipNodeShape m0 H.1.1
    exact ⟨km, t0, rfl⟩

/-- (Lean-only) The `seipAt` walk: after either `sig_meip` answer, the `sig_seip` node. -/
theorem AxEpiLedger.seipAtNext (t : ExecSt) (km : RegisterType Register.sig_meip → SailM Unit)
    (t0 : ExecSt) (H : seipAt t = true)
    (Hts : AxEpiLedger.toPin (riscvStep false) t
      = some (.impure (.ok (.regRead Register.sig_meip)) km, t0)) (v' : BitVec 1) :
    ∃ (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt),
      AxEpiLedger.toPin (km v') t0
        = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) := by
  unfold seipAt at H
  rw [Hts] at H
  simp only [Bool.and_eq_true] at H
  have Hv : AxEpiLedger.seipAfter (.impure (.ok (.regRead Register.sig_meip)) km) t0 v' = true := by
    rcases bv1Cases v' with rfl | rfl
    · exact H.1.2
    · exact H.2
  unfold AxEpiLedger.seipAfter at Hv
  rw [AxEpiLedger.ansMeipNode] at Hv
  cases h : AxEpiLedger.toPin (km v') t0 with
  | none => rw [h] at Hv; exact absurd Hv Bool.false_ne_true
  | some p =>
    obtain ⟨m1, t1⟩ := p
    rw [h] at Hv
    obtain ⟨k0, rfl⟩ := isSeipNodeShape m1 Hv
    exact ⟨k0, t1, rfl⟩

/-- (Lean-only) `branchAt` at the two computed pin nodes. -/
theorem AxEpiLedger.branchAtEq (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (post : RegFile → Bool) (t : ExecSt) (km : RegisterType Register.sig_meip → SailM Unit)
    (t0 : ExecSt) (v' : BitVec 1) (k0 : RegisterType Register.sig_seip → SailM Unit)
    (t1 : ExecSt) (v : BitVec 1)
    (Hts : AxEpiLedger.toPin (riscvStep false) t
      = some (.impure (.ok (.regRead Register.sig_meip)) km, t0))
    (Hts1 : AxEpiLedger.toPin (km v') t0
      = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1)) :
    branchAt Dr Dw D base vs post t v' v = branchOk Dr Dw D base vs post (k0 v) t1 := by
  unfold branchAt
  rw [Hts]
  simp only []
  rw [AxEpiLedger.ansMeipNode, Hts1]
  simp only []
  rw [AxEpiLedger.ansSeipNode]

theorem ledgerBranch (t : ExecSt) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (post : RegFile → Bool)
    (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt) (v' : BitVec 1)
    (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt) :
    AxEpiModelFacts t Dr Dw D base vs post →
    AxEpiLedger.toPin (riscvStep false) t
      = some (.impure (.ok (.regRead Register.sig_meip)) km, t0) →
    AxEpiLedger.toPin (km v') t0
      = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) →
    ∀ v, branchOk Dr Dw D base vs post (k0 v) t1 = true := by
  intro L Hts Hts1 v
  rw [← AxEpiLedger.branchAtEq Dr Dw D base vs post t km t0 v' k0 t1 v Hts Hts1]
  rcases bv1Cases v' with rfl | rfl <;> rcases bv1Cases v with rfl | rfl
  · exact L.lfBranch00
  · exact L.lfBranch01
  · exact L.lfBranch10
  · exact L.lfBranch11

/-- From an `erd`-exit fetch node of a certified branch, the fetch of `vs` and the `epure` tail
reach `RetS`. -/
theorem ledgerFetchReaches (D : List Register) (base : Int) (vs : List (BitVec 8))
    (post : RegFile → Bool) (cpu : CPU) (kk n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (t2 : ExecSt)
    (ib2 : Ibch) :
    Register.sig_seip ∉ D → Register.sig_meip ∉ D →
    fetchOk D base vs post (.impure (.ok (.memRead n va req)) KK) t2 = true →
    ∃ s', rtc (AxEpiLedger.ledgerStep cpu vs)
        ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) t2.regs none ib2, kk⟩ s' ∧
      RetS cpu post kk s' := by
  intro HD HDm Hf
  obtain ⟨n', va', req', KK', t3, heq, -, -, -, -, Hep, Hpost⟩ := fetchOkSpec _ _ _ _ _ _ Hf
  cases heq
  obtain ⟨ib3, Hr⟩ := epureGstepRtc D HD HDm _ _ _ _ Hep cpu ib2 kk
  refine ⟨_, rtc_l (.inr (.inr (.inl ⟨n, va, req, KK, t2.regs, ib2, ib2, kk, rfl, rfl⟩)))
    (rtcGstepLedgerStep cpu vs _ _ Hr), t3.regs, ib3, Hpost, aeqvHartRefl ..⟩

theorem ledgerBranchReaches (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (post : RegFile → Bool) (cpu : CPU) (kk : Nat) (m : SailM Unit) (t1 : ExecSt) (ib : Ibch) :
    Register.sig_seip ∉ Dr → Register.sig_meip ∉ Dr →
    Register.sig_seip ∉ D → Register.sig_meip ∉ D →
    branchOk Dr Dw D base vs post m t1 = true →
    ∃ s', rtc (AxEpiLedger.ledgerStep cpu vs) ⟨.PHart cpu m t1.regs none ib, kk⟩ s' ∧
      RetS cpu post kk s' := by
  intro HDr HDrm HD HDm Hb
  unfold branchOk at Hb
  cases he : erd Dr Dw m t1 with
  | none => rw [he] at Hb; exact absurd Hb Bool.false_ne_true
  | some p =>
    obtain ⟨qm, t2⟩ := p
    rw [he] at Hb
    obtain ⟨n, va, req, KK, t3, rfl, -⟩ := fetchOkSpec _ _ _ _ _ _ Hb
    obtain ⟨ib2, -, -, Hr⟩ := erdGstep Dr Dw m HDr HDrm t1 ib _ _ he cpu kk
    obtain ⟨s', Hr', Hs'⟩ := ledgerFetchReaches D base vs post cpu kk n va req KK t2 ib2 HD HDm Hb
    exact ⟨s', rtc_transitive (rtcGstepLedgerStep cpu vs _ _ Hr) Hr', Hs'⟩

/-- (Lean-only) From the `sig_seip` node of a certified branch, `RetS` is reached. -/
theorem AxEpiLedger.seipReaches (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (post : RegFile → Bool) (cpu : CPU) (kk : Nat)
    (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt) (ib1 : Ibch)
    (HDr : Register.sig_seip ∉ Dr) (HDrm : Register.sig_meip ∉ Dr)
    (HD : Register.sig_seip ∉ D) (HDm : Register.sig_meip ∉ D)
    (Hb : ∀ v, branchOk Dr Dw D base vs post (k0 v) t1 = true) :
    ∃ s', rtc (AxEpiLedger.ledgerStep cpu vs) (seipNode cpu k0 t1.regs ib1 kk) s' ∧
      RetS cpu post kk s' := by
  obtain ⟨s', Hr, Hs'⟩ := ledgerBranchReaches Dr Dw D base vs post cpu kk (k0 0#1) t1
    (ibRd ib1 Register.sig_seip) HDr HDrm HD HDm (Hb _)
  exact ⟨s', rtc_l (.inr (.inl ⟨k0, t1.regs, ib1, 0#1, _, kk, rfl, rfl⟩)) Hr, Hs'⟩

/-- (Lean-only) From the `sig_meip` node of a certified ledger, `RetS` is reached. -/
theorem AxEpiLedger.meipReaches (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (post : RegFile → Bool) (cpu : CPU) (kk : Nat)
    (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt) (ib0 : Ibch)
    (HDr : Register.sig_seip ∉ Dr) (HDrm : Register.sig_meip ∉ Dr)
    (HD : Register.sig_seip ∉ D) (HDm : Register.sig_meip ∉ D)
    (H : ∀ v', ∃ (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt),
      AxEpiLedger.toPin (km v') t0
        = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) ∧
      ∀ v, branchOk Dr Dw D base vs post (k0 v) t1 = true) :
    ∃ s', rtc (AxEpiLedger.ledgerStep cpu vs) (AxEpiLedger.meipNode cpu km t0.regs ib0 kk) s' ∧
      RetS cpu post kk s' := by
  obtain ⟨k0, t1, Hts1, Hb⟩ := H 0#1
  obtain ⟨ib1, Hr⟩ := AxEpiLedger.toPinGstep _ t0 (ibRd ib0 Register.sig_meip) _ _ Hts1 cpu kk
  obtain ⟨s', Hr', Hs'⟩ :=
    AxEpiLedger.seipReaches Dr Dw D base vs post cpu kk k0 t1 ib1 HDr HDrm HD HDm Hb
  exact ⟨s', rtc_l (.inr (.inr (.inr ⟨km, t0.regs, ib0, 0#1, _, kk, rfl, rfl⟩)))
    (rtc_transitive (rtcGstepLedgerStep cpu vs _ _ Hr) Hr'), Hs'⟩

/-- SANITY (non-vacuity of the row-end premise): every state of `ledgerInv` is `aeqv` to a
state that runs — by `gstep`s, answering the pin reads, and fetching `vs` — to a `RetS` state
with `post`. -/
theorem ledgerInvReachesRet (t : ExecSt) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (post : RegFile → Bool) (cpu : CPU) (kk : Nat) (s1 : Athread) :
    AxEpiModelFacts t Dr Dw D base vs post →
    AxEpiLedger.ledgerInv t Dr Dw D vs cpu kk s1 →
    ∃ t0 s', aeqv s1 t0 ∧ rtc (AxEpiLedger.ledgerStep cpu vs) t0 s' ∧ RetS cpu post kk s' := by
  intro L ⟨km, t0, ib0, Hts, Hc⟩
  have HDr := of_decide_eq_false L.lfSeipDr
  have HDrm := of_decide_eq_false L.lfMeipDr
  have HD := of_decide_eq_false L.lfSeipD
  have HDm := of_decide_eq_false L.lfMeipD
  have Hall : ∀ v', ∃ (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt),
      AxEpiLedger.toPin (km v') t0
        = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) ∧
      ∀ v, branchOk Dr Dw D base vs post (k0 v) t1 = true := by
    intro v'
    obtain ⟨k0, t1, Hts1⟩ := AxEpiLedger.seipAtNext t km t0 L.lfToSeip Hts v'
    exact ⟨k0, t1, Hts1, ledgerBranch t Dr Dw D base vs post km t0 v' k0 t1 L Hts Hts1⟩
  rcases Hc with Hc | ⟨v', k0, t1, ib1, Hts1, Hc⟩
  · obtain ⟨sm, Hrm, Hsm⟩ :=
      AxEpiLedger.meipReaches Dr Dw D base vs post cpu kk km t0 ib0 HDr HDrm HD HDm Hall
    rcases Hc with ⟨t', Ha, Htc⟩ | Ha | ⟨q, ⟨v', k0, t1, ib1, Hts1, rfl⟩, t', Ha, Htc⟩
    · exact ⟨t', sm, Ha, rtc_transitive (rtcGstepLedgerStep cpu vs _ _ (tc_rtc Htc)) Hrm, Hsm⟩
    · exact ⟨_, sm, Ha, Hrm, Hsm⟩
    · have Hb := ledgerBranch t Dr Dw D base vs post km t0 v' k0 t1 L Hts Hts1
      obtain ⟨s', Hr, Hs'⟩ :=
        AxEpiLedger.seipReaches Dr Dw D base vs post cpu kk k0 t1 ib1 HDr HDrm HD HDm Hb
      exact ⟨t', s', Ha, rtc_transitive (rtcGstepLedgerStep cpu vs _ _ (tc_rtc Htc)) Hr, Hs'⟩
  · have Hb := ledgerBranch t Dr Dw D base vs post km t0 v' k0 t1 L Hts Hts1
    obtain ⟨ss, Hrs, Hss⟩ :=
      AxEpiLedger.seipReaches Dr Dw D base vs post cpu kk k0 t1 ib1 HDr HDrm HD HDm Hb
    rcases Hc with Hc | ⟨v, n, va, req, KK, t2, t3, ib3, He, Hep, t', Ha, Htc⟩
    · rcases Hc with ⟨t', Ha, Htc⟩ | Ha | ⟨q, ⟨v, qm, t2, ib2, He, rfl, -⟩, t', Ha, Htc⟩
      · exact ⟨t', ss, Ha, rtc_transitive (rtcGstepLedgerStep cpu vs _ _ (tc_rtc Htc)) Hrs, Hss⟩
      · exact ⟨_, ss, Ha, Hrs, Hss⟩
      · have Hbv := Hb v
        unfold branchOk at Hbv
        rw [He] at Hbv
        obtain ⟨n, va, req, KK, t3, rfl, -⟩ := fetchOkSpec _ _ _ _ _ _ Hbv
        obtain ⟨s', Hr, Hs'⟩ :=
          ledgerFetchReaches D base vs post cpu kk n va req KK t2 ib2 HD HDm Hbv
        exact ⟨t', s', Ha, rtc_transitive (rtcGstepLedgerStep cpu vs _ _ (tc_rtc Htc)) Hr, Hs'⟩
    · have Hbv := Hb v
      unfold branchOk at Hbv
      rw [He] at Hbv
      exact ⟨t', _, Ha, rtcGstepLedgerStep cpu vs _ _ (tc_rtc Htc),
        t3.regs, ib3, fetchOkMem D base vs post n va req KK t2 t3 Hbv Hep, aeqvHartRefl ..⟩

/-! # 3. The composition -/

/-- (Lean-only) The `sig_meip` node's `n0Ok` (mirror of `n0OkSeipRead`). -/
theorem AxEpiLedger.n0OkMeipRead (cpu : CPU) (km : RegisterType Register.sig_meip → SailM Unit)
    (rs1 : RegFile) (ib1 : Ibch) (kk : Nat) (Qs : Athread → Prop) :
    (∀ v, ∃ q, Qs q ∧
       rtc gstep ⟨.PHart cpu (km v) rs1 none (ibRd ib1 Register.sig_meip), kk⟩ q) →
    n0Ok (AxEpiLedger.meipNode cpu km rs1 ib1 kk) Qs := by
  intro Hk p d l p' d' heq hst
  match p, p', heq, hst with
  | .PHart c m rs fn ib, .PHart c' m' rs' fn' ib', heq, hst =>
    obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := heq
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hn, -⟩ := hst
    obtain ⟨rfl, rfl, rfl, rfl, -, rfl, -⟩ := hn
    refine ⟨rfl, ?_⟩
    obtain ⟨q, hq, hr⟩ := Hk (rs Register.sig_meip)
    rcases rtc_inv hr with rfl | ⟨y, hy, hr'⟩
    · exact .inr ⟨_, hq, rfl, rfl, rfl, rfl, rfl, hag⟩
    · exact .inl ⟨q, hq,
        ⟨.PHart _ (km (rs Register.sig_meip)) rs1 none (ibRd ib Register.sig_meip), kk⟩,
        ⟨rfl, rfl, rfl, rfl, rfl, hag⟩, tcOfStepRtc hy hr'⟩
  | .PDisk _, _, heq, _ => exact (heq : False).elim
  | .PHart .., .PDisk _, _, hst => exact (hst : False).elim

/-- (Lean-only) A `gstep` prefix to the split node puts the start in the split invariant (the
start may BE the node). -/
theorem AxEpiLedger.pseipStart (c : CPU) (m : SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat)
    (n0 : Athread) (Qs : Athread → Prop) (Hr : rtc gstep ⟨.PHart c m rs none ib, k⟩ n0) :
    Pseip n0 Qs ⟨.PHart c m rs none ib, k⟩ := by
  rcases rtc_inv Hr with h | ⟨y, hy, hr⟩
  · subst h
    exact .inr (.inl (aeqvHartRefl ..))
  · exact .inl ⟨_, aeqvHartRefl .., tcOfStepRtc hy hr⟩

/-- (Lean-only) The `sig_meip` split's `n0Ok`, from the walk facts. -/
theorem AxEpiLedger.meipN0Ok (cpu : CPU) (km : RegisterType Register.sig_meip → SailM Unit)
    (t0 : ExecSt) (ib0 : Ibch) (kk : Nat)
    (H : ∀ v', ∃ (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt),
      AxEpiLedger.toPin (km v') t0
        = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1)) :
    n0Ok (AxEpiLedger.meipNode cpu km t0.regs ib0 kk) (AxEpiLedger.seipExit cpu km t0 kk) := by
  refine AxEpiLedger.n0OkMeipRead cpu km t0.regs ib0 kk _ (fun v' => ?_)
  obtain ⟨k0, t1, Hts1⟩ := H v'
  obtain ⟨ib1, hr⟩ := AxEpiLedger.toPinGstep _ t0 (ibRd ib0 Register.sig_meip) _ _ Hts1 cpu kk
  exact ⟨_, ⟨v', k0, t1, ib1, Hts1, rfl⟩, hr⟩

/-- (Lean-only) The `sig_seip` split's `n0Ok`, from the branch facts (inline in
`AxBoundaryWpd.wpdBoundaryErd`). -/
theorem AxEpiLedger.seipN0Ok (cpu : CPU) (k0 : RegisterType Register.sig_seip → SailM Unit)
    (t1 : ExecSt) (ib1 : Ibch) (kk : Nat) (Dr Dw : List Register)
    (HDr : Register.sig_seip ∉ Dr) (HDrm : Register.sig_meip ∉ Dr)
    (Herd : ∀ v, ∃ q t2, erd Dr Dw (k0 v) t1 = some (q, t2)) :
    n0Ok (seipNode cpu k0 t1.regs ib1 kk) (erdExit Dr Dw cpu k0 t1 kk) := by
  refine n0OkSeipRead cpu k0 t1.regs ib1 kk _ (fun v => ?_)
  obtain ⟨q, t2, he⟩ := Herd v
  obtain ⟨ib2, hq, -, hr⟩ :=
    erdGstep Dr Dw (k0 v) HDr HDrm t1 (ibRd ib1 Register.sig_seip) q t2 he cpu kk
  exact ⟨_, ⟨v, q, t2, ib2, he, rfl, hq⟩, hr⟩

/-- (Lean-only) `branchOk` gives the `erd` exit. -/
theorem AxEpiLedger.erdOfBranch (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (post : RegFile → Bool) (m : SailM Unit) (t1 : ExecSt)
    (Hb : branchOk Dr Dw D base vs post m t1 = true) :
    ∃ q t2, erd Dr Dw m t1 = some (q, t2) := by
  unfold branchOk at Hb
  cases he : erd Dr Dw m t1 with
  | none => rw [he] at Hb; exact absurd Hb Bool.false_ne_true
  | some p => exact ⟨p.1, p.2, rfl⟩

section ledger
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- (Lean-only) `AxBoundaryWpd.wpdOfSeipSplit` from ANY start in the split invariant (the inner
split starts at a state `aeqv` to its node). -/
theorem AxEpiLedger.wpdOfSplitFrom (i : Agent) (Φ : Athread → IProp GF) (s0 n0 : Athread)
    (Qs : Athread → Prop) (HP : Pseip n0 Qs s0) (Hn0 : n0Ok n0 Qs) :
    ⊢ ((∀ s2, ⌜QaS Qs s2⌝ -∗ wpd .MaybeStuck i s2 Φ) ∧
       (∀ (GD : Gdexec) s1, ⌜Pseip n0 Qs s1⌝ -∗ ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗
          postLifting Φ i s1)) -∗
      wpd .MaybeStuck i s0 Φ := by
  iintro R
  iapply (wpdOfClosedRun .MaybeStuck i (Pseip n0 Qs) (QaS Qs) Φ
    (fun s1 _ => (progressOblMaybestuck (GF := GF) i s1).2)
    (fun GD s1 id K h => pseipHnord i n0 Qs Hn0 GD s1 id K h)
    (fun GD s1 l s2 h1 h2 => pseipHclos n0 Qs Hn0 _ s1 l s2 h1 h2)
    (pseipHwire n0 Qs)) $$ %s0 %HP R

/-- `AxCjrWpd.wpdFetchThenRun`, started from any register file `rs` agreeing with the run's
`rs0` off the pins. -/
theorem wpdFetchThenRunAgree (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (vs : List (BitVec 8)) (rs0 rs : RegFile) (q : Athread)
    (Hdev : devAddr req.pa = false) (Hfe : (classify req.access_kind).akIfetch = true)
    (Hlen : vs.length = n)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i k (paZ req.pa) vs⌝)
    (Hag : regsAgree AxRunClose.pinReg rs0 rs)
    (Hrun : rtc gstep ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs0 none ib, k⟩ q) :
    ⊢ ((∀ s2, ⌜Qat q s2⌝ -∗ wpd .MaybeStuck i s2 Φ) ∧
       (∀ (GD : Gdexec) s1, ⌜Pbefore q s1⌝ -∗ ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗
          postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ Φ := by
  iintro R
  iapply (wpdFetchStep Φ i cpu n va req KK ib k vs rs0 Hdev Hfe Hlen Hgd) $$ %rs %Hag
  iintro %rs' %hag
  iapply (AxCjrWpd.wpdOfRunFrom i q
    ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs0 none ib, k⟩
    ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs' none ib, k⟩ Φ Hrun
    ⟨rfl, rfl, rfl, rfl, rfl, regsAgreeSym _ _ _ hag⟩) $$ R

/-- THE WHOLE-INSTRUCTION `wpd` FROM THE LEDGER. -/
theorem wpdCjrStepOfLedger (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch)
    (kk : Nat) (t : ExecSt) (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (post : RegFile → Bool) (L : AxEpiModelFacts t Dr Dw D base vs post)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk base vs⌝) :
    ⊢ ((∀ s', ⌜RetS cpu post kk s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1, ⌜AxEpiLedger.ledgerInv t Dr Dw D vs cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) t.regs none ib, kk⟩ Φ := by
  have HDr := of_decide_eq_false L.lfSeipDr
  have HDrm := of_decide_eq_false L.lfMeipDr
  have HD := of_decide_eq_false L.lfSeipD
  have HDm := of_decide_eq_false L.lfMeipD
  obtain ⟨km, t0, Hts⟩ := AxEpiLedger.seipAtSpec t L.lfToSeip
  have Hnext := AxEpiLedger.seipAtNext t km t0 L.lfToSeip Hts
  obtain ⟨ib0, Hr0⟩ := AxEpiLedger.toPinGstep _ t ib _ _ Hts cpu kk
  iintro R
  iapply (AxEpiLedger.wpdOfSplitFrom i Φ _ _ _
    (AxEpiLedger.pseipStart cpu _ t.regs ib kk _ (AxEpiLedger.seipExit cpu km t0 kk) Hr0)
    (AxEpiLedger.meipN0Ok cpu km t0 ib0 kk Hnext))
  isplit
  · iintro %s2 %HQ
    obtain ⟨q, ⟨v', k0, t1, ib1, Hts1, rfl⟩, Hq⟩ := HQ
    have Hb := ledgerBranch t Dr Dw D base vs post km t0 v' k0 t1 L Hts Hts1
    iapply (AxEpiLedger.wpdOfSplitFrom i Φ s2 _ (erdExit Dr Dw cpu k0 t1 kk) (.inr (.inl Hq))
      (AxEpiLedger.seipN0Ok cpu k0 t1 ib1 kk Dr Dw HDr HDrm
        (fun v => AxEpiLedger.erdOfBranch Dr Dw D base vs post _ t1 (Hb v))))
    isplit
    · iintro %s3 %HQ3
      obtain ⟨q3, ⟨v, qm, t2, ib2, He, rfl, -⟩, Hs3⟩ := HQ3
      have Hbv := Hb v
      unfold branchOk at Hbv
      rw [He] at Hbv
      obtain ⟨n, va, req, KK, t3, rfl, Hdev, Hfe, Hpa, Hlen, Hep, Hpost⟩ :=
        fetchOkSpec _ _ _ _ _ _ Hbv
      subst Hpa
      obtain ⟨p3, k3⟩ := s3
      obtain ⟨hk, hp⟩ := Hs3
      simp only at hk hp
      subst k3
      match p3, hp with
      | .PHart c3 m3 rs3 fn3 ib3', hp =>
        obtain ⟨hc, hm, hf, hi, hag⟩ := hp
        subst c3 m3 fn3 ib3'
        obtain ⟨ib3, Hrun⟩ := epureGstepRtc D HD HDm _ _ _ _ Hep cpu ib2 kk
        iapply (wpdFetchThenRunAgree Φ i cpu n va req KK ib2 kk vs t2.regs rs3 _ Hdev Hfe
          Hlen Hgd (regsAgreeSym _ _ _ hag) Hrun)
        isplit
        · icases R with ⟨R, -⟩
          iintro %s' %Hs'
          iapply R $$ %s' %⟨t3.regs, ib3, Hpost, Hs'⟩
        · icases R with ⟨-, R⟩
          iintro %GD %s1 %Hs1 %Hlen1
          iapply R $$ %GD %s1
            %⟨km, t0, ib0, Hts, .inr ⟨v', k0, t1, ib1, Hts1,
              .inr ⟨v, n, va, req, KK, t2, t3, ib3, He, Hep, Hs1⟩⟩⟩ %Hlen1
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %Hs1 %Hlen1
      iapply R $$ %GD %s1 %⟨km, t0, ib0, Hts, .inr ⟨v', k0, t1, ib1, Hts1, .inl Hs1⟩⟩ %Hlen1
  · icases R with ⟨-, R⟩
    iintro %GD %s1 %Hs1 %Hlen1
    iapply R $$ %GD %s1 %⟨km, t0, ib0, Hts, .inl Hs1⟩ %Hlen1

end ledger

/-! # 4. The concrete instance: c.jr ra at `pcJr2` -/

def cjrVs : List (BitVec 8) := [0x82#8, 0x80#8]

def postRa (rs : RegFile) : Bool := decide ((rs .PC).toNat = raVal)

/-- Rocq `(Dr_all ∪ Dw_all) ∖ {[sig_seip]}`; Lean removes BOTH pins (deviation 2). -/
noncomputable def DPost : List Register :=
  (DrAll ++ DwAll).eraseDups.filter fun r => !decide (r = .sig_seip) && !decide (r = .sig_meip)

theorem epiLedgerCjr :
    AxEpiModelFacts (tAt pcJr2) AxEpiProbe.drNopin DwAll DPost (pcJr2 : Int) cjrVs postRa where
  lfSeipDr := by decide +kernel
  lfMeipDr := by decide +kernel
  lfSeipD := by decide +kernel
  lfMeipD := by decide +kernel
  lfHead := by decide +kernel
  lfToSeip := by decide +kernel
  lfBranch00 := by decide +kernel
  lfBranch01 := by decide +kernel
  lfBranch10 := by decide +kernel
  lfBranch11 := by decide +kernel

section concrete
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem wpdCjrConcrete (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch) (kk : Nat)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk (pcJr2 : Int) cjrVs⌝) :
    ⊢ ((∀ s', ⌜RetS cpu postRa kk s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜AxEpiLedger.ledgerInv (tAt pcJr2) AxEpiProbe.drNopin DwAll DPost cjrVs cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) (probeRegs pcJr2) none ib, kk⟩ Φ :=
  wpdCjrStepOfLedger i Φ cpu ib kk (tAt pcJr2) _ _ _ _ _ _ epiLedgerCjr Hgd

end concrete

/-! # 5. The data load: c.ldsp ra,8(sp)

Same boundary + fetch as c.jr, then the post-fetch continuation is `erd` (no longer `epure`) to
the FIRST RAM read — the data load `memRead nl reql` at `ldaddr` — and the post-load continuation
has an `epure D` certificate for EVERY loaded word `x : BitVec (8 * nl)` (the value is
graph-chosen), ending at a register file satisfying `postLd x.toNat`. -/

def ldLoadOk (D : List Register) (ldaddr : Int) (postLd : Int → RegFile → Prop)
    (ml : SailM Unit) (tl : ExecSt) : Prop :=
  match ml with
  | .impure (.ok (.memRead nl _ reql)) KK =>
    devAddr reql.pa = false ∧ (classify reql.access_kind).akLatest = false ∧
    (classify reql.access_kind).akIfetch = false ∧
    paZ reql.pa = ldaddr ∧ 0 < nl ∧
    ∀ x : BitVec (8 * nl),
      match epure D (KK (.Ok (x, none))) tl with
      | some (_, s) => postLd (x.toNat : Int) s.regs
      | none => False
  | _ => False

def ldFetchOk (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8)) (ldaddr : Int)
    (postLd : Int → RegFile → Prop) (mf : SailM Unit) (t2 : ExecSt) : Prop :=
  match mf with
  | .impure (.ok (.memRead n _ req)) KKf =>
    devAddr req.pa = false ∧ (classify req.access_kind).akIfetch = true ∧
    paZ req.pa = base ∧ vs.length = n ∧
    match erd Dr Dw (KKf (.Ok (wordOfBytes n vs, none))) t2 with
    | some (ml, tl) => ldLoadOk D ldaddr postLd ml tl
    | none => False
  | _ => False

def ldBranchOk (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8)) (ldaddr : Int)
    (postLd : Int → RegFile → Prop) (m : SailM Unit) (t1 : ExecSt) : Prop :=
  match erd Dr Dw m t1 with
  | some (mf, t2) => ldFetchOk Dr Dw D base vs ldaddr postLd mf t2
  | none => False

def ldBranchAt (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8)) (ldaddr : Int)
    (postLd : Int → RegFile → Prop) (t : ExecSt) (v' v : BitVec 1) : Prop :=
  match AxEpiLedger.toPin (riscvStep false) t with
  | some (m0, t0) =>
    match AxEpiLedger.toPin (AxEpiLedger.ansMeip m0 v') t0 with
    | some (m1, t1) => ldBranchOk Dr Dw D base vs ldaddr postLd (ansSeip m1 v) t1
    | none => False
  | none => False

/-- THE LOAD LEDGER. -/
structure AxLdModelFacts (t : ExecSt) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (postLd : Int → RegFile → Prop) : Prop where
  lgSeipDr : decide (Register.sig_seip ∈ Dr) = false
  lgMeipDr : decide (Register.sig_meip ∈ Dr) = false
  lgSeipD : decide (Register.sig_seip ∈ D) = false
  lgMeipD : decide (Register.sig_meip ∈ D) = false
  lgHead : isSeipNode (riscvStep false) = false
  lgToSeip : seipAt t = true
  lgBranch00 : ldBranchAt Dr Dw D base vs ldaddr postLd t 0#1 0#1
  lgBranch01 : ldBranchAt Dr Dw D base vs ldaddr postLd t 0#1 1#1
  lgBranch10 : ldBranchAt Dr Dw D base vs ldaddr postLd t 1#1 0#1
  lgBranch11 : ldBranchAt Dr Dw D base vs ldaddr postLd t 1#1 1#1

/-- The `.pure ()` set of the load instruction: some loaded word `x`. -/
def RetLd (cpu : CPU) (postLd : Int → RegFile → Prop) (k : Nat) (s : Athread) : Prop :=
  ∃ (x : Int) (rs3 : RegFile) (ib' : Ibch), postLd x rs3 ∧
    Qat ⟨.PHart cpu (.pure ()) rs3 none ib', k⟩ s

/-- THE ROW-END INVARIANT of the load: the two boundary sets, the set before the data-load node,
and the post-load `Pbefore` of every certified `.pure ()`. -/
def ledgerLdInv (t : ExecSt) (Dr Dw D : List Register) (vs : List (BitVec 8)) (cpu : CPU)
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
          (nl val : Nat) (reql : Mem_read_request nl val Arch.pa Arch.translation Arch.arch_ak)
          (KK : Result (BitVec (8 * nl) × Option Bool) Arch.abort → SailM Unit) (tl : ExecSt)
          (ibLd : Ibch),
          erd Dr Dw (k0 v) t1 = some (.impure (.ok (.memRead n va req)) KKf, t2) ∧
          erd Dr Dw (KKf (.Ok (wordOfBytes n vs, none))) t2
            = some (.impure (.ok (.memRead nl val reql)) KK, tl) ∧
          (Pbefore ⟨.PHart cpu (.impure (.ok (.memRead nl val reql)) KK) tl.regs none ibLd, kk⟩
              s1 ∨
           ∃ (x : BitVec (8 * nl)) (sEnd : ExecSt) (ib' : Ibch),
             epure D (KK (.Ok (x, none))) tl = some ((), sEnd) ∧
             Pbefore ⟨.PHart cpu (.pure ()) sEnd.regs none ib', kk + 1⟩ s1)))

/-- The load's run relation: `ledgerStep`, or a data read returning ANY word. -/
def ldStep (cpu : CPU) (vs : List (BitVec 8)) (s s' : Athread) : Prop :=
  AxEpiLedger.ledgerStep cpu vs s s' ∨
  (∃ (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
     (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
     (ib ib' : Ibch) (k : Nat) (x : BitVec (8 * n)),
     s = ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ ∧
     s' = ⟨.PHart cpu (KK (.Ok (x, none))) rs none ib', k + 1⟩)

theorem rtcGstepLdStep (cpu : CPU) (vs : List (BitVec 8)) (s s' : Athread) :
    rtc gstep s s' → rtc (ldStep cpu vs) s s' :=
  rtc_subrel (fun _ _ h => .inl (.inl h))

theorem ldLoadOkNode (D : List Register) (ldaddr : Int) (postLd : Int → RegFile → Prop)
    (nl val : Nat) (reql : Mem_read_request nl val Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * nl) × Option Bool) Arch.abort → SailM Unit) (tl : ExecSt) :
    ldLoadOk D ldaddr postLd (.impure (.ok (.memRead nl val reql)) KK) tl →
    devAddr reql.pa = false ∧ (classify reql.access_kind).akLatest = false ∧
    (classify reql.access_kind).akIfetch = false ∧ paZ reql.pa = ldaddr ∧ 0 < nl ∧
    ∀ x : BitVec (8 * nl), ∃ sEnd : ExecSt,
      epure D (KK (.Ok (x, none))) tl = some ((), sEnd) ∧
      postLd (x.toNat : Int) sEnd.regs := by
  intro H
  simp only [ldLoadOk] at H
  obtain ⟨h1, h2, h3, h4, h5, Hx⟩ := H
  refine ⟨h1, h2, h3, h4, h5, fun x => ?_⟩
  have hx := Hx x
  cases he : epure D (KK (.Ok (x, none))) tl with
  | none => rw [he] at hx; exact hx.elim
  | some p =>
    obtain ⟨⟨⟩, sEnd⟩ := p
    rw [he] at hx
    exact ⟨sEnd, rfl, hx⟩

theorem ldFetchOkNode (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (ldaddr : Int) (postLd : Int → RegFile → Prop) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KKf : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (t2 : ExecSt) :
    ldFetchOk Dr Dw D base vs ldaddr postLd (.impure (.ok (.memRead n va req)) KKf) t2 →
    devAddr req.pa = false ∧ (classify req.access_kind).akIfetch = true ∧
    paZ req.pa = base ∧ vs.length = n ∧
    ∃ (nl val : Nat) (reql : Mem_read_request nl val Arch.pa Arch.translation Arch.arch_ak)
      (KK : Result (BitVec (8 * nl) × Option Bool) Arch.abort → SailM Unit) (tl : ExecSt),
      erd Dr Dw (KKf (.Ok (wordOfBytes n vs, none))) t2
        = some (.impure (.ok (.memRead nl val reql)) KK, tl) ∧
      ldLoadOk D ldaddr postLd (.impure (.ok (.memRead nl val reql)) KK) tl := by
  intro H
  simp only [ldFetchOk] at H
  obtain ⟨h1, h2, h3, h4, hl⟩ := H
  refine ⟨h1, h2, h3, h4, ?_⟩
  cases he : erd Dr Dw (KKf (.Ok (wordOfBytes n vs, none))) t2 with
  | none => rw [he] at hl; exact hl.elim
  | some p =>
    obtain ⟨ml, tl⟩ := p
    rw [he] at hl
    cases ml with
    | pure _ => exact (hl : False).elim
    | impure call KK =>
      cases call with
      | error _ => exact (hl : False).elim
      | ok o =>
        cases o
        case memRead nl val reql => exact ⟨nl, val, reql, KK, tl, rfl, hl⟩
        all_goals exact (hl : False).elim

theorem ldBranchOkNode (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (ldaddr : Int) (postLd : Int → RegFile → Prop) (m : SailM Unit) (t1 : ExecSt) :
    ldBranchOk Dr Dw D base vs ldaddr postLd m t1 →
    ∃ (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (KKf : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (t2 : ExecSt),
      erd Dr Dw m t1 = some (.impure (.ok (.memRead n va req)) KKf, t2) ∧
      ldFetchOk Dr Dw D base vs ldaddr postLd (.impure (.ok (.memRead n va req)) KKf) t2 := by
  intro H
  unfold ldBranchOk at H
  cases he : erd Dr Dw m t1 with
  | none => rw [he] at H; exact H.elim
  | some p =>
    obtain ⟨mf, t2⟩ := p
    rw [he] at H
    cases mf with
    | pure _ => exact (H : False).elim
    | impure call KKf =>
      cases call with
      | error _ => exact (H : False).elim
      | ok o =>
        cases o
        case memRead n va req => exact ⟨n, va, req, KKf, t2, rfl, H⟩
        all_goals exact (H : False).elim

/-- (Lean-only) `ldBranchAt` at the two computed pin nodes. -/
theorem AxEpiLedger.ldBranchAtEq (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (ldaddr : Int) (postLd : Int → RegFile → Prop) (t : ExecSt)
    (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt) (v' : BitVec 1)
    (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt) (v : BitVec 1)
    (Hts : AxEpiLedger.toPin (riscvStep false) t
      = some (.impure (.ok (.regRead Register.sig_meip)) km, t0))
    (Hts1 : AxEpiLedger.toPin (km v') t0
      = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1)) :
    ldBranchAt Dr Dw D base vs ldaddr postLd t v' v =
      ldBranchOk Dr Dw D base vs ldaddr postLd (k0 v) t1 := by
  unfold ldBranchAt
  rw [Hts]
  simp only []
  rw [AxEpiLedger.ansMeipNode, Hts1]
  simp only []
  rw [AxEpiLedger.ansSeipNode]

theorem ldLedgerBranch (t : ExecSt) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (postLd : Int → RegFile → Prop)
    (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt) (v' : BitVec 1)
    (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt) :
    AxLdModelFacts t Dr Dw D base vs ldaddr postLd →
    AxEpiLedger.toPin (riscvStep false) t
      = some (.impure (.ok (.regRead Register.sig_meip)) km, t0) →
    AxEpiLedger.toPin (km v') t0
      = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) →
    ∀ v, ldBranchOk Dr Dw D base vs ldaddr postLd (k0 v) t1 := by
  intro L Hts Hts1 v
  rw [← AxEpiLedger.ldBranchAtEq Dr Dw D base vs ldaddr postLd t km t0 v' k0 t1 v Hts Hts1]
  rcases bv1Cases v' with rfl | rfl <;> rcases bv1Cases v with rfl | rfl
  · exact L.lgBranch00
  · exact L.lgBranch01
  · exact L.lgBranch10
  · exact L.lgBranch11

theorem ldLoadReaches (D : List Register) (ldaddr : Int) (postLd : Int → RegFile → Prop)
    (cpu : CPU) (vs : List (BitVec 8)) (nl val : Nat)
    (reql : Mem_read_request nl val Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * nl) × Option Bool) Arch.abort → SailM Unit) (tl : ExecSt)
    (ib : Ibch) (k : Nat) :
    Register.sig_seip ∉ D → Register.sig_meip ∉ D →
    ldLoadOk D ldaddr postLd (.impure (.ok (.memRead nl val reql)) KK) tl →
    ∃ s', rtc (ldStep cpu vs)
        ⟨.PHart cpu (.impure (.ok (.memRead nl val reql)) KK) tl.regs none ib, k⟩ s' ∧
      RetLd cpu postLd (k + 1) s' := by
  intro HD HDm H
  obtain ⟨-, -, -, -, -, Hx⟩ := ldLoadOkNode _ _ _ _ _ _ _ _ H
  obtain ⟨sEnd, Hep, Hpost⟩ := Hx (BitVec.ofNat (8 * nl) 0)
  obtain ⟨ib3, Hr⟩ := epureGstepRtc D HD HDm _ _ _ _ Hep cpu ib (k + 1)
  exact ⟨_, rtc_l (.inr ⟨nl, val, reql, KK, tl.regs, ib, ib, k, _, rfl, rfl⟩)
    (rtcGstepLdStep cpu vs _ _ Hr), _, sEnd.regs, ib3, Hpost, aeqvHartRefl ..⟩

theorem ldFetchReaches (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (ldaddr : Int) (postLd : Int → RegFile → Prop) (cpu : CPU) (kk n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KKf : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (t2 : ExecSt)
    (ib2 : Ibch) :
    Register.sig_seip ∉ Dr → Register.sig_meip ∉ Dr →
    Register.sig_seip ∉ D → Register.sig_meip ∉ D →
    ldFetchOk Dr Dw D base vs ldaddr postLd (.impure (.ok (.memRead n va req)) KKf) t2 →
    ∃ s', rtc (ldStep cpu vs)
        ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KKf) t2.regs none ib2, kk⟩ s' ∧
      RetLd cpu postLd (kk + 1) s' := by
  intro HDr HDrm HD HDm H
  obtain ⟨-, -, -, -, nl, val, reql, KK, tl, He2, Hl⟩ := ldFetchOkNode _ _ _ _ _ _ _ _ _ _ _ _ H
  obtain ⟨ibLd, -, -, Hr⟩ := erdGstep Dr Dw _ HDr HDrm t2 ib2 _ _ He2 cpu kk
  obtain ⟨s', Hr', Hs'⟩ := ldLoadReaches D ldaddr postLd cpu vs nl val reql KK tl ibLd kk HD HDm Hl
  exact ⟨s', rtc_l (.inl (.inr (.inr (.inl ⟨n, va, req, KKf, t2.regs, ib2, ib2, kk, rfl, rfl⟩))))
    (rtc_transitive (rtcGstepLdStep cpu vs _ _ Hr) Hr'), Hs'⟩

theorem ldBranchReaches (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (ldaddr : Int) (postLd : Int → RegFile → Prop) (cpu : CPU) (kk : Nat) (m : SailM Unit)
    (t1 : ExecSt) (ib : Ibch) :
    Register.sig_seip ∉ Dr → Register.sig_meip ∉ Dr →
    Register.sig_seip ∉ D → Register.sig_meip ∉ D →
    ldBranchOk Dr Dw D base vs ldaddr postLd m t1 →
    ∃ s', rtc (ldStep cpu vs) ⟨.PHart cpu m t1.regs none ib, kk⟩ s' ∧
      RetLd cpu postLd (kk + 1) s' := by
  intro HDr HDrm HD HDm Hb
  obtain ⟨n, va, req, KKf, t2, He, Hf⟩ := ldBranchOkNode _ _ _ _ _ _ _ _ _ Hb
  obtain ⟨ib2, -, -, Hr⟩ := erdGstep Dr Dw m HDr HDrm t1 ib _ _ He cpu kk
  obtain ⟨s', Hr', Hs'⟩ :=
    ldFetchReaches Dr Dw D base vs ldaddr postLd cpu kk n va req KKf t2 ib2 HDr HDrm HD HDm Hf
  exact ⟨s', rtc_transitive (rtcGstepLdStep cpu vs _ _ Hr) Hr', Hs'⟩

/-- (Lean-only) From the `sig_seip` node of a certified load branch, `RetLd` is reached. -/
theorem AxEpiLedger.ldSeipReaches (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (postLd : Int → RegFile → Prop) (cpu : CPU)
    (kk : Nat) (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt) (ib1 : Ibch)
    (HDr : Register.sig_seip ∉ Dr) (HDrm : Register.sig_meip ∉ Dr)
    (HD : Register.sig_seip ∉ D) (HDm : Register.sig_meip ∉ D)
    (Hb : ∀ v, ldBranchOk Dr Dw D base vs ldaddr postLd (k0 v) t1) :
    ∃ s', rtc (ldStep cpu vs) (seipNode cpu k0 t1.regs ib1 kk) s' ∧
      RetLd cpu postLd (kk + 1) s' := by
  obtain ⟨s', Hr, Hs'⟩ := ldBranchReaches Dr Dw D base vs ldaddr postLd cpu kk (k0 0#1) t1
    (ibRd ib1 Register.sig_seip) HDr HDrm HD HDm (Hb _)
  exact ⟨s', rtc_l (.inl (.inr (.inl ⟨k0, t1.regs, ib1, 0#1, _, kk, rfl, rfl⟩))) Hr, Hs'⟩

/-- (Lean-only) From the `sig_meip` node of a certified load ledger, `RetLd` is reached. -/
theorem AxEpiLedger.ldMeipReaches (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (postLd : Int → RegFile → Prop) (cpu : CPU)
    (kk : Nat) (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt) (ib0 : Ibch)
    (HDr : Register.sig_seip ∉ Dr) (HDrm : Register.sig_meip ∉ Dr)
    (HD : Register.sig_seip ∉ D) (HDm : Register.sig_meip ∉ D)
    (H : ∀ v', ∃ (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt),
      AxEpiLedger.toPin (km v') t0
        = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) ∧
      ∀ v, ldBranchOk Dr Dw D base vs ldaddr postLd (k0 v) t1) :
    ∃ s', rtc (ldStep cpu vs) (AxEpiLedger.meipNode cpu km t0.regs ib0 kk) s' ∧
      RetLd cpu postLd (kk + 1) s' := by
  obtain ⟨k0, t1, Hts1, Hb⟩ := H 0#1
  obtain ⟨ib1, Hr⟩ := AxEpiLedger.toPinGstep _ t0 (ibRd ib0 Register.sig_meip) _ _ Hts1 cpu kk
  obtain ⟨s', Hr', Hs'⟩ :=
    AxEpiLedger.ldSeipReaches Dr Dw D base vs ldaddr postLd cpu kk k0 t1 ib1 HDr HDrm HD HDm Hb
  exact ⟨s', rtc_l (.inl (.inr (.inr (.inr ⟨km, t0.regs, ib0, 0#1, _, kk, rfl, rfl⟩))))
    (rtc_transitive (rtcGstepLdStep cpu vs _ _ Hr) Hr'), Hs'⟩

/-- SANITY (non-vacuity of the load's row-end premise): every state of `ledgerLdInv` is `aeqv`
to a state that runs — `gstep`s, the pin answers, the fetch of `vs`, a data load of some word —
to a `RetLd` state. -/
theorem ledgerLdInvReachesRet (t : ExecSt) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (postLd : Int → RegFile → Prop) (cpu : CPU)
    (kk : Nat) (s1 : Athread) :
    AxLdModelFacts t Dr Dw D base vs ldaddr postLd →
    ledgerLdInv t Dr Dw D vs cpu kk s1 →
    ∃ t0 s', aeqv s1 t0 ∧ rtc (ldStep cpu vs) t0 s' ∧ RetLd cpu postLd (kk + 1) s' := by
  intro L ⟨km, t0, ib0, Hts, Hc⟩
  have HDr := of_decide_eq_false L.lgSeipDr
  have HDrm := of_decide_eq_false L.lgMeipDr
  have HD := of_decide_eq_false L.lgSeipD
  have HDm := of_decide_eq_false L.lgMeipD
  have Hall : ∀ v', ∃ (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt),
      AxEpiLedger.toPin (km v') t0
        = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) ∧
      ∀ v, ldBranchOk Dr Dw D base vs ldaddr postLd (k0 v) t1 := by
    intro v'
    obtain ⟨k0, t1, Hts1⟩ := AxEpiLedger.seipAtNext t km t0 L.lgToSeip Hts v'
    exact ⟨k0, t1, Hts1, ldLedgerBranch t Dr Dw D base vs ldaddr postLd km t0 v' k0 t1 L Hts Hts1⟩
  rcases Hc with Hc | ⟨v', k0, t1, ib1, Hts1, Hc⟩
  · obtain ⟨sm, Hrm, Hsm⟩ :=
      AxEpiLedger.ldMeipReaches Dr Dw D base vs ldaddr postLd cpu kk km t0 ib0 HDr HDrm HD HDm
        Hall
    rcases Hc with ⟨t', Ha, Htc⟩ | Ha | ⟨q, ⟨v', k0, t1, ib1, Hts1, rfl⟩, t', Ha, Htc⟩
    · exact ⟨t', sm, Ha, rtc_transitive (rtcGstepLdStep cpu vs _ _ (tc_rtc Htc)) Hrm, Hsm⟩
    · exact ⟨_, sm, Ha, Hrm, Hsm⟩
    · have Hb := ldLedgerBranch t Dr Dw D base vs ldaddr postLd km t0 v' k0 t1 L Hts Hts1
      obtain ⟨s', Hr, Hs'⟩ := AxEpiLedger.ldSeipReaches Dr Dw D base vs ldaddr postLd cpu kk
        k0 t1 ib1 HDr HDrm HD HDm Hb
      exact ⟨t', s', Ha, rtc_transitive (rtcGstepLdStep cpu vs _ _ (tc_rtc Htc)) Hr, Hs'⟩
  · have Hb := ldLedgerBranch t Dr Dw D base vs ldaddr postLd km t0 v' k0 t1 L Hts Hts1
    obtain ⟨ss, Hrs, Hss⟩ := AxEpiLedger.ldSeipReaches Dr Dw D base vs ldaddr postLd cpu kk
      k0 t1 ib1 HDr HDrm HD HDm Hb
    rcases Hc with Hc | ⟨v, n, va, req, KKf, t2, nl, val, reql, KK, tl, ibLd, He, He2, Hc⟩
    · rcases Hc with ⟨t', Ha, Htc⟩ | Ha | ⟨q, ⟨v, qm, t2, ib2, He, rfl, -⟩, t', Ha, Htc⟩
      · exact ⟨t', ss, Ha, rtc_transitive (rtcGstepLdStep cpu vs _ _ (tc_rtc Htc)) Hrs, Hss⟩
      · exact ⟨_, ss, Ha, Hrs, Hss⟩
      · obtain ⟨n, va, req, KKf, t2', He', Hf⟩ := ldBranchOkNode _ _ _ _ _ _ _ _ _ (Hb v)
        rw [He, Option.some.injEq, Prod.mk.injEq] at He'
        obtain ⟨rfl, rfl⟩ := He'
        obtain ⟨s', Hr, Hs'⟩ :=
          ldFetchReaches Dr Dw D base vs ldaddr postLd cpu kk n va req KKf t2 ib2 HDr HDrm HD HDm
            Hf
        exact ⟨t', s', Ha, rtc_transitive (rtcGstepLdStep cpu vs _ _ (tc_rtc Htc)) Hr, Hs'⟩
    · have Hl : ldLoadOk D ldaddr postLd (.impure (.ok (.memRead nl val reql)) KK) tl := by
        have Hbv := Hb v
        unfold ldBranchOk at Hbv
        rw [He] at Hbv
        simp only [ldFetchOk] at Hbv
        rw [He2] at Hbv
        exact Hbv.2.2.2.2
      rcases Hc with ⟨t', Ha, Htc⟩ | ⟨x, sEnd, ib', Hep, t', Ha, Htc⟩
      · obtain ⟨s', Hr, Hs'⟩ := ldLoadReaches D ldaddr postLd cpu vs nl val reql KK tl ibLd kk HD
          HDm Hl
        exact ⟨t', s', Ha, rtc_transitive (rtcGstepLdStep cpu vs _ _ (tc_rtc Htc)) Hr, Hs'⟩
      · obtain ⟨-, -, -, -, -, Hx⟩ := ldLoadOkNode _ _ _ _ _ _ _ _ Hl
        obtain ⟨sEnd', Hep', Hpost⟩ := Hx x
        rw [Hep, Option.some.injEq, Prod.mk.injEq] at Hep'
        obtain ⟨-, rfl⟩ := Hep'
        exact ⟨t', _, Ha, rtcGstepLdStep cpu vs _ _ (tc_rtc Htc), _, sEnd.regs, ib', Hpost,
          aeqvHartRefl ..⟩

section ldLedger
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- `AxLdspWpd.wpdLoadThenRet`, generic in the load width `nl`, with the post-load certificate
for every word `x`. -/
theorem wpdLoadThenRetN (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (nl va : Nat)
    (req : Mem_read_request nl va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * nl) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (sLd : ExecSt) (D : List Register) (Rv : Gdexec → List (BitVec 8) → IProp GF)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hn : 0 < nl) (Hnf : (classify req.access_kind).akIfetch = false)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i k⌝)
    (Hseip : Register.sig_seip ∉ D) (Hmeip : Register.sig_meip ∉ D)
    (Hpost : ∀ x : BitVec (8 * nl), ∃ sEnd : ExecSt,
      epure D (KK (.Ok (x, none))) sLd = some ((), sEnd)) :
    ⊢ ∀ s2, ⌜Qat ⟨.PHart cpu (.impure (.ok (.memRead nl va req)) KK) sLd.regs none ib, k⟩ s2⌝ -∗
      (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
         ⌜graphValue GD (i, k) = some v⌝ -∗ loadFlow GD i k (Rv GD v)) -∗
      ((∀ (x : BitVec (8 * nl)) (sEnd : ExecSt) (ib' : Ibch) (s' : Athread),
          ⌜epure D (KK (.Ok (x, none))) sLd = some ((), sEnd)⌝ -∗
          ⌜Qat ⟨.PHart cpu (.pure ()) sEnd.regs none ib', k + 1⟩ s'⌝ -∗
          wpd .MaybeStuck i s' Φ) ∧
       (∀ (x : BitVec (8 * nl)) (sEnd : ExecSt) (ib' : Ibch) (GD : Gdexec) (s1 : Athread),
          ⌜epure D (KK (.Ok (x, none))) sLd = some ((), sEnd)⌝ -∗
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
    iapply (wpdLoadStep Φ i cpu nl va req KK ib k sLd.regs Rv Hdev Hlat Hn Hnf Hrow) $$
      %rs2 %(regsAgreeSym _ _ _ hag) F
    iintro %v %rs' %Hlv %hag'
    obtain ⟨sEnd, Hep⟩ := Hpost (wordOfBytes nl v)
    obtain ⟨ib', Hrun⟩ := epureGstepRtc D Hseip Hmeip _ _ _ _ Hep cpu ib (k + 1)
    iapply (wpdRunTo Φ i _ _ Hrun) $$
      %⟨.PHart cpu (KK (.Ok (wordOfBytes nl v, none))) rs' none ib, k + 1⟩
      %⟨rfl, rfl, rfl, rfl, rfl, regsAgreeSym _ _ _ hag'⟩
    isplit
    · icases R with ⟨R, -⟩
      iintro %s3 %Hq3
      iapply R $$ %(wordOfBytes nl v) %sEnd %ib' %s3 %Hep %Hq3
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %Hb %Hend
      iapply R $$ %(wordOfBytes nl v) %sEnd %ib' %GD %s1 %Hep %Hb %Hend

/-- Fetch (any width, bytes `vs`) → pre-load `gstep` run → data load. -/
theorem wpdFetchThenLoad (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KKf : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (vs : List (BitVec 8)) (rs0 rs : RegFile) (nl val : Nat)
    (reql : Mem_read_request nl val Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * nl) × Option Bool) Arch.abort → SailM Unit) (ibLd : Ibch)
    (tl : ExecSt) (D : List Register) (Rv : Gdexec → List (BitVec 8) → IProp GF)
    (Hdev : devAddr req.pa = false) (Hfe : (classify req.access_kind).akIfetch = true)
    (Hlen : vs.length = n)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i k (paZ req.pa) vs⌝)
    (Hag : regsAgree AxRunClose.pinReg rs0 rs)
    (HrunPre : rtc gstep
      ⟨.PHart cpu (KKf (.Ok (wordOfBytes n vs, none))) rs0 none ib, k⟩
      ⟨.PHart cpu (.impure (.ok (.memRead nl val reql)) KK) tl.regs none ibLd, k⟩)
    (Hdevl : devAddr reql.pa = false) (Hlatl : (classify reql.access_kind).akLatest = false)
    (Hn : 0 < nl) (Hnfl : (classify reql.access_kind).akIfetch = false)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i k⌝)
    (Hseip : Register.sig_seip ∉ D) (Hmeip : Register.sig_meip ∉ D)
    (Hpost : ∀ x : BitVec (8 * nl), ∃ sEnd : ExecSt,
      epure D (KK (.Ok (x, none))) tl = some ((), sEnd)) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
         ⌜graphValue GD (i, k) = some v⌝ -∗ loadFlow GD i k (Rv GD v)) -∗
      (((∀ (x : BitVec (8 * nl)) (sEnd : ExecSt) (ib' : Ibch) (s' : Athread),
           ⌜epure D (KK (.Ok (x, none))) tl = some ((), sEnd)⌝ -∗
           ⌜Qat ⟨.PHart cpu (.pure ()) sEnd.regs none ib', k + 1⟩ s'⌝ -∗
           wpd .MaybeStuck i s' Φ) ∧
        (∀ (x : BitVec (8 * nl)) (sEnd : ExecSt) (ib' : Ibch) (GD : Gdexec) (s1 : Athread),
           ⌜epure D (KK (.Ok (x, none))) tl = some ((), sEnd)⌝ -∗
           ⌜Pbefore ⟨.PHart cpu (.pure ()) sEnd.regs none ib', k + 1⟩ s1⌝ -∗
           ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) ∧
       (∀ (GD : Gdexec) (s1 : Athread),
          ⌜Pbefore ⟨.PHart cpu (.impure (.ok (.memRead nl val reql)) KK) tl.regs none ibLd, k⟩
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
    iapply (wpdLoadThenRetN Φ i cpu nl val reql KK ibLd k tl D Rv Hdevl Hlatl Hn Hnfl Hrow
      Hseip Hmeip Hpost) $$ %s3 %Hq3 F R
  · icases R with ⟨-, R⟩
    iexact R

/-- THE WHOLE-INSTRUCTION `wpd` OF A DATA LOAD FROM THE LOAD LEDGER. -/
theorem wpdCldspStepOfLedger (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch)
    (kk : Nat) (t : ExecSt) (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (ldaddr : Int) (postLd : Int → RegFile → Prop) (Rv : Gdexec → List (BitVec 8) → IProp GF)
    (L : AxLdModelFacts t Dr Dw D base vs ldaddr postLd)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk base vs⌝)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i kk⌝) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i kk ls -∗
         ⌜graphValue GD (i, kk) = some v⌝ -∗ loadFlow GD i kk (Rv GD v)) -∗
      ((∀ s', ⌜RetLd cpu postLd (kk + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1, ⌜ledgerLdInv t Dr Dw D vs cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) t.regs none ib, kk⟩ Φ := by
  have HDr := of_decide_eq_false L.lgSeipDr
  have HDrm := of_decide_eq_false L.lgMeipDr
  have HD := of_decide_eq_false L.lgSeipD
  have HDm := of_decide_eq_false L.lgMeipD
  obtain ⟨km, t0, Hts⟩ := AxEpiLedger.seipAtSpec t L.lgToSeip
  have Hnext := AxEpiLedger.seipAtNext t km t0 L.lgToSeip Hts
  obtain ⟨ib0, Hr0⟩ := AxEpiLedger.toPinGstep _ t ib _ _ Hts cpu kk
  iintro F R
  iapply (AxEpiLedger.wpdOfSplitFrom i Φ _ _ _
    (AxEpiLedger.pseipStart cpu _ t.regs ib kk _ (AxEpiLedger.seipExit cpu km t0 kk) Hr0)
    (AxEpiLedger.meipN0Ok cpu km t0 ib0 kk Hnext))
  isplit
  · iintro %s2 %HQ
    obtain ⟨q, ⟨v', k0, t1, ib1, Hts1, rfl⟩, Hq⟩ := HQ
    have Hb := ldLedgerBranch t Dr Dw D base vs ldaddr postLd km t0 v' k0 t1 L Hts Hts1
    have Herd : ∀ v, ∃ q t2, erd Dr Dw (k0 v) t1 = some (q, t2) := by
      intro v
      obtain ⟨_, _, _, _, _, He, _⟩ := ldBranchOkNode _ _ _ _ _ _ _ _ _ (Hb v)
      exact ⟨_, _, He⟩
    iapply (AxEpiLedger.wpdOfSplitFrom i Φ s2 _ (erdExit Dr Dw cpu k0 t1 kk) (.inr (.inl Hq))
      (AxEpiLedger.seipN0Ok cpu k0 t1 ib1 kk Dr Dw HDr HDrm Herd))
    isplit
    · iintro %s3 %HQ3
      obtain ⟨q3, ⟨v, qm, t2, ib2, He, rfl, -⟩, Hs3⟩ := HQ3
      obtain ⟨n, va, req, KKf, t2', He', Hf⟩ := ldBranchOkNode _ _ _ _ _ _ _ _ _ (Hb v)
      rw [He, Option.some.injEq, Prod.mk.injEq] at He'
      obtain ⟨rfl, rfl⟩ := He'
      obtain ⟨Hdev, Hfe, Hpa, Hlen, nl, val, reql, KK, tl, He2, Hl⟩ :=
        ldFetchOkNode _ _ _ _ _ _ _ _ _ _ _ _ Hf
      obtain ⟨Hdevl, Hlatl, Hnfl, Hpal, Hn, Hx⟩ := ldLoadOkNode _ _ _ _ _ _ _ _ Hl
      subst Hpa
      obtain ⟨p3, k3⟩ := s3
      obtain ⟨hk, hp⟩ := Hs3
      simp only at hk hp
      subst k3
      match p3, hp with
      | .PHart c3 m3 rs3 fn3 ib3', hp =>
        obtain ⟨hc, hm, hf, hi, hag⟩ := hp
        subst c3 m3 fn3 ib3'
        obtain ⟨ibLd, -, -, HrunPre⟩ := erdGstep Dr Dw _ HDr HDrm t2 ib2 _ _ He2 cpu kk
        have Hpost : ∀ x : BitVec (8 * nl), ∃ sEnd : ExecSt,
            epure D (KK (.Ok (x, none))) tl = some ((), sEnd) := by
          intro x
          obtain ⟨sEnd, Hep, -⟩ := Hx x
          exact ⟨sEnd, Hep⟩
        iapply (wpdFetchThenLoad Φ i cpu n va req KKf ib2 kk vs t2.regs rs3 nl val reql KK ibLd
          tl D Rv Hdev Hfe Hlen Hgd (regsAgreeSym _ _ _ hag) HrunPre Hdevl Hlatl Hn Hnfl
          Hrow HD HDm Hpost) $$ F
        isplit
        · isplit
          · icases R with ⟨R, -⟩
            iintro %x %sEnd %ib3 %s' %Hep %Hs'
            obtain ⟨sEnd', Hep', Hpost'⟩ := Hx x
            rw [Hep, Option.some.injEq, Prod.mk.injEq] at Hep'
            obtain ⟨-, rfl⟩ := Hep'
            iapply R $$ %s' %⟨_, sEnd.regs, ib3, Hpost', Hs'⟩
          · icases R with ⟨-, R⟩
            iintro %x %sEnd %ib3 %GD %s1 %Hep %Hs1 %Hlen1
            iapply R $$ %GD %s1
              %⟨km, t0, ib0, Hts, .inr ⟨v', k0, t1, ib1, Hts1,
                .inr ⟨v, n, va, req, KKf, t2, nl, val, reql, KK, tl, ibLd, He, He2,
                  .inr ⟨x, sEnd, ib3, Hep, Hs1⟩⟩⟩⟩ %Hlen1
        · icases R with ⟨-, R⟩
          iintro %GD %s1 %Hs1 %Hlen1
          iapply R $$ %GD %s1
            %⟨km, t0, ib0, Hts, .inr ⟨v', k0, t1, ib1, Hts1,
              .inr ⟨v, n, va, req, KKf, t2, nl, val, reql, KK, tl, ibLd, He, He2, .inl Hs1⟩⟩⟩
            %Hlen1
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %Hs1 %Hlen1
      iapply R $$ %GD %s1 %⟨km, t0, ib0, Hts, .inr ⟨v', k0, t1, ib1, Hts1, .inl Hs1⟩⟩ %Hlen1
  · icases R with ⟨-, R⟩
    iintro %GD %s1 %Hs1 %Hlen1
    iapply R $$ %GD %s1 %⟨km, t0, ib0, Hts, .inl Hs1⟩ %Hlen1

end ldLedger

/-! ## The concrete instance: c.ldsp ra,8(sp) at `pcLd`

The load ledger's branch facts quantify over the loaded word (`∀ x : BitVec (8 * nl)`), so they
are not closed booleans.  Lean-only route: the boolean twins `AxEpiLedger.ldLoadB` …
`AxEpiLedger.ldBranchAtB`, stated at ONE free 64-bit word `x` (cast to the node's width), are
checked by the kernel with `x` free (`ax_epi_ledger_krfl`; the evaluation never branches on
`x`), and the bridges `AxEpiLedger.ldLoadOfB` … `AxEpiLedger.ldBranchAtOfB` turn them into the
`Prop` fields. -/

def AxEpiLedger.ldVs : List (BitVec 8) := [0xa2#8, 0x60#8]

def ldAddr : Int := (spVal : Int) + 8

/-- Post-load predicate, for loaded word `x`: the PC has advanced past the 2-byte instruction.
(As in Rocq, `x1 = x` is not included.) -/
def ldPost (_x : Int) (rs : RegFile) : Prop := (rs .PC).toNat = pcLd + 2

/-- (Lean-only) The boolean twin of `ldLoadOk` at a 64-bit word `x`. -/
def AxEpiLedger.ldLoadB (D : List Register) (ldaddr : Int) (postB : RegFile → Bool)
    (ml : SailM Unit) (tl : ExecSt) (x : BitVec 64) : Bool :=
  match ml with
  | .impure (.ok (.memRead nl _ reql)) KK =>
    !devAddr reql.pa && !(classify reql.access_kind).akLatest &&
    !(classify reql.access_kind).akIfetch && decide (paZ reql.pa = ldaddr) &&
    (if h : nl = 8 then
      match epure D (KK (.Ok (x.cast (by omega), none))) tl with
      | some (_, s) => postB s.regs
      | none => false
    else false)
  | _ => false

/-- (Lean-only) The boolean twin of `ldFetchOk`. -/
def AxEpiLedger.ldFetchB (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (ldaddr : Int) (postB : RegFile → Bool) (mf : SailM Unit) (t2 : ExecSt) (x : BitVec 64) :
    Bool :=
  match mf with
  | .impure (.ok (.memRead n _ req)) KKf =>
    !devAddr req.pa && (classify req.access_kind).akIfetch &&
    decide (paZ req.pa = base) && decide (vs.length = n) &&
    match erd Dr Dw (KKf (.Ok (wordOfBytes n vs, none))) t2 with
    | some (ml, tl) => AxEpiLedger.ldLoadB D ldaddr postB ml tl x
    | none => false
  | _ => false

/-- (Lean-only) The boolean twin of `ldBranchOk`. -/
def AxEpiLedger.ldBranchB (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (ldaddr : Int) (postB : RegFile → Bool) (m : SailM Unit) (t1 : ExecSt) (x : BitVec 64) :
    Bool :=
  match erd Dr Dw m t1 with
  | some (mf, t2) => AxEpiLedger.ldFetchB Dr Dw D base vs ldaddr postB mf t2 x
  | none => false

/-- (Lean-only) The boolean twin of `ldBranchAt`. -/
noncomputable def AxEpiLedger.ldBranchAtB (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (postB : RegFile → Bool) (t : ExecSt) (v' v : BitVec 1)
    (x : BitVec 64) : Bool :=
  match AxEpiLedger.toPin (riscvStep false) t with
  | some (m0, t0) =>
    match AxEpiLedger.toPin (AxEpiLedger.ansMeip m0 v') t0 with
    | some (m1, t1) => AxEpiLedger.ldBranchB Dr Dw D base vs ldaddr postB (ansSeip m1 v) t1 x
    | none => false
  | none => false

theorem AxEpiLedger.ldLoadOfB (D : List Register) (ldaddr : Int) (postB : RegFile → Bool)
    (postLd : Int → RegFile → Prop) (Hp : ∀ z rs, postB rs = true → postLd z rs)
    (ml : SailM Unit) (tl : ExecSt)
    (H : ∀ x : BitVec 64, AxEpiLedger.ldLoadB D ldaddr postB ml tl x = true) :
    ldLoadOk D ldaddr postLd ml tl := by
  cases ml with
  | pure _ => exact absurd (H 0) Bool.false_ne_true
  | impure call KK =>
    cases call with
    | error _ => exact absurd (H 0) Bool.false_ne_true
    | ok o =>
      cases o
      case memRead nl va reql =>
        have h0 := H 0
        simp only [AxEpiLedger.ldLoadB, Bool.and_eq_true, Bool.not_eq_true',
          decide_eq_true_eq] at h0
        obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h0
        by_cases hn : nl = 8
        · subst hn
          simp only [ldLoadOk]
          refine ⟨h1, h2, h3, h4, by omega, fun x => ?_⟩
          have hx := H (x.cast (by omega))
          simp only [AxEpiLedger.ldLoadB, dite_true, BitVec.cast_eq,
            Bool.and_eq_true] at hx
          obtain ⟨-, hx⟩ := hx
          cases he : epure D (KK (.Ok (x, none))) tl with
          | none => rw [he] at hx; exact absurd hx Bool.false_ne_true
          | some p =>
            obtain ⟨u, s⟩ := p
            rw [he] at hx
            exact Hp _ _ hx
        · simp only [hn, dite_false] at h5
          exact absurd h5 Bool.false_ne_true
      all_goals exact absurd (H 0) Bool.false_ne_true

theorem AxEpiLedger.ldFetchOfB (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (ldaddr : Int) (postB : RegFile → Bool) (postLd : Int → RegFile → Prop)
    (Hp : ∀ z rs, postB rs = true → postLd z rs) (mf : SailM Unit) (t2 : ExecSt)
    (H : ∀ x : BitVec 64, AxEpiLedger.ldFetchB Dr Dw D base vs ldaddr postB mf t2 x = true) :
    ldFetchOk Dr Dw D base vs ldaddr postLd mf t2 := by
  cases mf with
  | pure _ => exact absurd (H 0) Bool.false_ne_true
  | impure call KKf =>
    cases call with
    | error _ => exact absurd (H 0) Bool.false_ne_true
    | ok o =>
      cases o
      case memRead n va req =>
        cases he : erd Dr Dw (KKf (.Ok (wordOfBytes n vs, none))) t2 with
        | none =>
          have h0 := H 0
          simp only [AxEpiLedger.ldFetchB, he, Bool.and_false] at h0
          exact absurd h0 Bool.false_ne_true
        | some p =>
          obtain ⟨ml, tl⟩ := p
          have h0 := H 0
          simp only [AxEpiLedger.ldFetchB, he, Bool.and_eq_true, Bool.not_eq_true',
            decide_eq_true_eq] at h0
          obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩ := h0
          simp only [ldFetchOk, he]
          refine ⟨h1, h2, h3, h4, AxEpiLedger.ldLoadOfB D ldaddr postB postLd Hp ml tl
            (fun x => ?_)⟩
          have hx := H x
          simp only [AxEpiLedger.ldFetchB, he, Bool.and_eq_true] at hx
          exact hx.2
      all_goals exact absurd (H 0) Bool.false_ne_true

theorem AxEpiLedger.ldBranchOfB (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (ldaddr : Int) (postB : RegFile → Bool) (postLd : Int → RegFile → Prop)
    (Hp : ∀ z rs, postB rs = true → postLd z rs) (m : SailM Unit) (t1 : ExecSt)
    (H : ∀ x : BitVec 64, AxEpiLedger.ldBranchB Dr Dw D base vs ldaddr postB m t1 x = true) :
    ldBranchOk Dr Dw D base vs ldaddr postLd m t1 := by
  unfold ldBranchOk
  cases he : erd Dr Dw m t1 with
  | none =>
    have h0 := H 0
    simp only [AxEpiLedger.ldBranchB, he] at h0
    exact absurd h0 Bool.false_ne_true
  | some p =>
    obtain ⟨mf, t2⟩ := p
    refine AxEpiLedger.ldFetchOfB Dr Dw D base vs ldaddr postB postLd Hp mf t2 (fun x => ?_)
    have hx := H x
    simp only [AxEpiLedger.ldBranchB, he] at hx
    exact hx

theorem AxEpiLedger.ldBranchAtOfB (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (postB : RegFile → Bool)
    (postLd : Int → RegFile → Prop) (Hp : ∀ z rs, postB rs = true → postLd z rs) (t : ExecSt)
    (v' v : BitVec 1)
    (H : ∀ x : BitVec 64, AxEpiLedger.ldBranchAtB Dr Dw D base vs ldaddr postB t v' v x = true) :
    ldBranchAt Dr Dw D base vs ldaddr postLd t v' v := by
  unfold ldBranchAt
  cases h1 : AxEpiLedger.toPin (riscvStep false) t with
  | none =>
    have h0 := H 0
    simp only [AxEpiLedger.ldBranchAtB, h1] at h0
    exact absurd h0 Bool.false_ne_true
  | some p =>
    obtain ⟨m0, t0⟩ := p
    dsimp only
    cases h2 : AxEpiLedger.toPin (AxEpiLedger.ansMeip m0 v') t0 with
    | none =>
      have h0 := H 0
      simp only [AxEpiLedger.ldBranchAtB, h1, h2] at h0
      exact absurd h0 Bool.false_ne_true
    | some p2 =>
      obtain ⟨m1, t1⟩ := p2
      dsimp only
      refine AxEpiLedger.ldBranchOfB Dr Dw D base vs ldaddr postB postLd Hp _ t1 (fun x => ?_)
      have hx := H x
      simp only [AxEpiLedger.ldBranchAtB, h1, h2] at hx
      exact hx

/-- (Lean-only) The boolean twin of `ldPost`. -/
def AxEpiLedger.ldPostB (rs : RegFile) : Bool := decide ((rs .PC).toNat = pcLd + 2)

theorem AxEpiLedger.ldPostOfB (z : Int) (rs : RegFile) :
    AxEpiLedger.ldPostB rs = true → ldPost z rs :=
  fun h => (of_decide_eq_true h : (rs .PC).toNat = pcLd + 2)

theorem epiLedgerCldsp :
    AxLdModelFacts (tAt pcLd) AxEpiProbe.drNopin DwAll DPost (pcLd : Int) AxEpiLedger.ldVs
      ldAddr ldPost where
  lgSeipDr := by decide +kernel
  lgMeipDr := by decide +kernel
  lgSeipD := by decide +kernel
  lgMeipD := by decide +kernel
  lgHead := by decide +kernel
  lgToSeip := by decide +kernel
  lgBranch00 := AxEpiLedger.ldBranchAtOfB _ _ _ _ _ _ AxEpiLedger.ldPostB _
    AxEpiLedger.ldPostOfB _ _ _ (by intro x; ax_epi_ledger_krfl)
  lgBranch01 := AxEpiLedger.ldBranchAtOfB _ _ _ _ _ _ AxEpiLedger.ldPostB _
    AxEpiLedger.ldPostOfB _ _ _ (by intro x; ax_epi_ledger_krfl)
  lgBranch10 := AxEpiLedger.ldBranchAtOfB _ _ _ _ _ _ AxEpiLedger.ldPostB _
    AxEpiLedger.ldPostOfB _ _ _ (by intro x; ax_epi_ledger_krfl)
  lgBranch11 := AxEpiLedger.ldBranchAtOfB _ _ _ _ _ _ AxEpiLedger.ldPostB _
    AxEpiLedger.ldPostOfB _ _ _ (by intro x; ax_epi_ledger_krfl)

section ldConcrete
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem wpdCldspConcrete (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch) (kk : Nat)
    (Rv : Gdexec → List (BitVec 8) → IProp GF)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢
        ⌜AxCjrWpd.fetchImgOk GD i kk (pcLd : Int) AxEpiLedger.ldVs⌝)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i kk⌝) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i kk ls -∗
         ⌜graphValue GD (i, kk) = some v⌝ -∗ loadFlow GD i kk (Rv GD v)) -∗
      ((∀ s', ⌜RetLd cpu ldPost (kk + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜ledgerLdInv (tAt pcLd) AxEpiProbe.drNopin DwAll DPost AxEpiLedger.ldVs cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) (probeRegs pcLd) none ib, kk⟩ Φ :=
  wpdCldspStepOfLedger i Φ cpu ib kk (tAt pcLd) _ _ _ _ _ _ _ Rv epiLedgerCldsp Hgd Hrow

end ldConcrete

end Weak
