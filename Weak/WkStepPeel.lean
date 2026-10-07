/-
Weak: **the peel and family of a WHOLE walking step** (walk-bridge §8, 6a: the whole-step layer
above `Weak/WkFetchPeel.lean`).  `WkFetchPeel` peels the S-mode `fetch ()` at the PC page's leaf
window; this file lifts that peel to a complete `riscvStep tick` whose FETCH walks the page table
and whose EXECUTE phase is window-free, builds the matching stale-mirror FAMILY (`execStale` of
the whole step per admissible leaf word), and closes the Q-half through `WeakStale` §10's
⇐-bridge: every weak outcome of the step is one admissible leaf word's mirror run, with the log
identity on top.

Rocq: `iris/WkStepPeel.v` @ xxvzwolszwmp (1266 lines; one Lean file, elaborates in a few seconds).

The Rocq header, in substance.  `riscvStep tick = try_step 0 false >>= fun _ => stepTick tick`;
every layer of `try_step` is register-only except `run_hart_active`, inside whose
`catch_early_return` the fetch sits under a `liftR`, behind the privilege read and
`dispatchInterrupt`.  §1 adds the two transports the composition needs: a register-only
(empty-trace) `execEff` sub-run IS its peel at any phase (`wstepOkRacyKOfEffNil` and its quiet
instances), and the converse of `WkFetchPeel.wstepOkRacyKCer` (`wstepOkRacyKROfKCer`), which lets
the post-fetch remainder of `run_hart_active` be owed as an ORDINARY `wstepOk` of its
`catch_early_return`.  §2 the tail interfaces; §3 the peel of `run_hart_active` and of the whole
step; §4 the step peel from `WkFetchPeel`'s premise bundle, the state-dependent premises owed at
the post-`minstret_increment`-write states `wmi σ b` for both flag values; §5 the family (the
fetch at the mirror with the walk's own mirror run, the window-free tail as one `execEff`
interface, the trace concatenation); §6 the ⇐-bridge.  SCOPE as Rocq: aligned (4-aligned, `F_Base`)
fetch only, window-free execute only, the interrupt arm gated off by a premise.  The note on what a
WRITING window-free execute would need (Rocq, after §5i) carries over unchanged: `traceStale`
forbids a RAM write before the racy read, so the TLB-hit shapes `[]` / `[excl-read]` would have to
go through the constant-family arm, which needs a per-shape constancy conjunct in
`wwalkExports`.  No graph-tier fact is used anywhere: the file lives at `wrun` / `execStale`.

**Deviations from Rocq.**
1. VOCABULARY as `Weak/WkFetchPeel.lean` deviation 1 (`SailME`, `liftM`, `SailME.run`, `readReg`,
   `σ.wmRegs r`, `⟨r, m, d⟩ : ExecSt`, `BMap`, `wflatMem`, `pa + BitVec.ofNat 64 j`, `nthByte`,
   `wsetReg`, …); `riscv_step` ↦ `riscvStep`, `set_reg s r v` ↦ `s.setReg r v`, `sregs`/`mdev` ↦
   `.regs`/`.dev`, `wflat_st` ↦ `wflatSt`, `is_Some (read_bytes m a n)` ↦ `(bmRead m a n).isSome =
   true` (as `WeakStale` §10), `HART_ACTIVE tt` ↦ `.HART_ACTIVE ()`, Rocq's right-associated `++`
   written with explicit parentheses (Lean's `++` is left-associative).  Statement-level `let`s the
   statements do not use (`a2`, `a1`) are dropped (as WkFetchPeel).
2. §0 EXTRACTION: Rocq extracts `rha_after_fetch` / `ts_after_rha` with `ltac:(… match … context
   [Defs.bind …] …)`.  Lean extracts them the same way, by the Lean-only metaprogram
   `WkStepPeel.extractCont` (the continuation of the first `Bind.bind` node at the named types in
   the model's own definition body) behind the term elaborators `wk_step_peel_rha%` /
   `wk_step_peel_ts%`, so they cannot drift from the model.  The Lean model's `run_hart_active`
   elaborates its interrupt `match` with a join point, and `try_step` has no `bind0`; the
   Lean-only equations `WkStepPeel.runHartActiveUnfold` / `WkStepPeel.tryStepUnfold` (with the
   hart-state dispatch `WkStepPeel.tsHart`) spell the register-only prefixes around the extracted
   continuations and are proved by `rfl`.
3. `wmstateEq` and `wstepOkRacyKOfEffNil` carry the sixth `Wmstate` field: `s1.wmItv = s2.wmItv` /
   `s2.wmItv = s.wmItv` (Stage B's instruction view; Rocq's `wmstate` has five fields).
4. `wstepOkRacyKQuiet`: Rocq's empty map `∅` is `fun _ => none` (`BMap` is a function map).
5. O2 (WkFetchPeel deviations 4–5): the text read is the i-cache read, trace element
   `.WEread WeakFetchEff.wakIfetch pa 4` (Rocq `WEread wak_plain pa 4`) in
   `execStaleFetchBytes4S`, `execStaleFetchS`, `execStaleStepOfWalk`, `wstepFamilyReady`,
   `wstepFamilyFetchwalk` (it is still unpinned, `akPins wakIfetch = false`, so it enters
   `traceStale` through the disjoint arm, as Rocq's); and the "text bytes pinned" premise of
   `wstepPeelFetchwalk` / `wstepOutcomeFetchwalk` is the FETCH pin
   `fetchPinned σ (WeakInterp.accAddr pa j)` (Rocq `pinned_read`), which is what
   `wfetchPeelKSelfcontained` / `wfetchPeelSelfcontained` demand.  The leaf window's access kind
   stays `wakPlain` (it is the walk's PTE read).
6. PROOF STRUCTURE: Rocq's `cbv`-and-`rewrite` mirror proofs (§5c–5e) are `simp` normalisation
   with `WeakWalkStale`'s `exec_stale_run`; the peel proofs (§3) are Rocq's `apply` chains, with
   `dsimp only` for the `cbv iota beta` steps.  The register facts past the pre-write are the
   Lean-only `WkStepPeel.wmiRegs` (Rocq `irrelevant_register_set … vm_compute`); the text-read
   prefix of the family's trace is the Lean-only `WkStepPeel.textTail`; the empty-trace
   impossibility is the Lean-only `WkStepPeel.consNeNil`.
7. Rocq §7's `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  `rha_after_fetch` `rhaAfterFetch`, `ts_after_rha` `tsAfterRha`,
`step_tick` `stepTick`, `riscv_step_unfold` `riscvStepUnfold`, `wmstate_eq` `wmstateEq`,
`wstep_ok_racy_k_of_eff_nil` `wstepOkRacyKOfEffNil`, `wstep_ok_racy_kR_of_k_cer`
`wstepOkRacyKROfKCer`, `wstep_ok_racy_kR_triv_of_wstep_ok` `wstepOkRacyKRTrivOfWstepOk`,
`wstep_ok_racy_k_triv_of_wstep_ok` `wstepOkRacyKTrivOfWstepOk`, `wstep_ok_racy_k_write_reg`
`wstepOkRacyKWriteReg`, `wstep_ok_racy_k_quiet` `wstepOkRacyKQuiet`, `wstep_ok_racy_k_quiet_flat`
`wstepOkRacyKQuietFlat`, `wmi` `wmi`, `wexec_tail` `wexecTail`, `wstep_post_tail`
`wstepPostTail`, `wstep_tick_tail` `wstepTickTail`, `wfetch_peel_k_at` `wfetchPeelKAt`,
`wrha_peel` `wrhaPeel`, `wstep_peel` `wstepPeel`, `wfetch_ready` `wfetchReady`,
`wstep_peel_fetchwalk` `wstepPeelFetchwalk`, `trace_off_win_app` `traceOffWinApp`,
`trace_stale_app` `traceStaleApp`, `execR_stale_of_cer` `execRStaleOfCer`,
`exec_stale_run_hart_active` `execStaleRunHartActive`, `exec_stale_riscv_step`
`execStaleRiscvStep`, `exec_stale_fetch_bytes_4_S` `execStaleFetchBytes4S`, `exec_stale_fetch_S`
`execStaleFetchS`, `wstep_tail_eff` `wstepTailEff`, `trace_off_win_app_l` `traceOffWinAppL`,
`trace_off_win_app_r` `traceOffWinAppR`, `exec_stale_step_of_walk` `execStaleStepOfWalk`,
`wstep_family_ready` `wstepFamilyReady`, `wflat_st_wmi` `wflatStWmi`, `wstep_family_fetchwalk`
`wstepFamilyFetchwalk`, `wstep_outcome_of_peel` `wstepOutcomeOfPeel`, `wstep_outcome_fetchwalk`
`wstepOutcomeFetchwalk`, `wexec_outcome_of_peel` `wexecOutcomeOfPeel` (none in the
duplicated-name table).  Lean-only (file-qualified): `WkStepPeel.extractCont` (+ the elaborators
`wk_step_peel_rha%` / `wk_step_peel_ts%`), `WkStepPeel.runHartActiveUnfold`, `WkStepPeel.tsHart`,
`WkStepPeel.tryStepUnfold`, `WkStepPeel.consNeNil`, `WkStepPeel.wmiRegs`, `WkStepPeel.textTail`.

**Dropped:** nothing.  38 Rocq declarations (`Definition`/`Lemma`): 38 ported + 7 Lean-only = 45
Lean declarations (plus the two term elaborators).

**Statements checked** (by hand, against Rocq): all; the changed ones are deviations 1, 3–5.
-/
import Weak.WkFetchPeel

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 0. THE TWO CONTINUATIONS THE STEP'S SEAMS EXPOSE -/

open Lean Meta Elab Term in
/-- Lean-only: the continuation `k` of the first `@Bind.bind _ _ α β _ k` node (pre-order) of
the body of `c` applied to `args`, with `α`/`β` the named types (Rocq's `ltac:(… match t with
context [Defs.bind … ?k] => exact k end)`). -/
def WkStepPeel.extractCont (c : Name) (args : Array Lean.Expr) (α β : Name) : TermElabM Lean.Expr := do
  let some ci := (← getEnv).find? c | throwError "WkStepPeel.extractCont: no constant {c}"
  let some v := ci.value? | throwError "WkStepPeel.extractCont: {c} has no value"
  let body := v.beta args
  let hit := body.find? fun e =>
    e.isAppOfArity ``Bind.bind 6 && (e.getArg! 2).isConstOf α && (e.getArg! 3).isConstOf β
  match hit with
  | some e =>
    let k := e.getArg! 5
    if k.hasLooseBVars then throwError "WkStepPeel.extractCont: the continuation is open"
    pure k
  | none => throwError "WkStepPeel.extractCont: no bind node of the requested shape"

open Lean Elab Term in
elab "wk_step_peel_rha%" : term =>
  WkStepPeel.extractCont ``run_hart_active #[mkNatLit 0] ``FetchResult ``Step

open Lean Elab Term in
elab "wk_step_peel_ts%" : term =>
  WkStepPeel.extractCont ``try_step #[mkNatLit 0, mkConst ``Bool.false] ``Step ``Bool

/-- Rocq `rha_after_fetch`: the fetch's continuation inside `run_hart_active 0`, EXTRACTED. -/
noncomputable def rhaAfterFetch : FetchResult → SailME Step Step := wk_step_peel_rha%

/-- Rocq `ts_after_rha`: `run_hart_active`'s continuation inside `try_step 0 false`, EXTRACTED. -/
noncomputable def tsAfterRha : Step → SailM Bool := wk_step_peel_ts%

/-- Rocq `step_tick`. -/
noncomputable def stepTick (tick : Bool) : SailM Unit := if tick then tick_clock () else pure ()

/-- Rocq `riscv_step_unfold`. -/
theorem riscvStepUnfold (tick : Bool) :
    riscvStep tick = (try_step 0 false >>= fun _ : Bool => stepTick tick) := rfl

/-- Lean-only: `run_hart_active 0`, its prefix spelled (the interrupt `match` and the join
point as the model elaborates them), its post-fetch remainder the extracted `rhaAfterFetch`
(proved by `rfl`, so it cannot drift from the model). -/
theorem WkStepPeel.runHartActiveUnfold :
    run_hart_active 0 = SailME.run
      ((liftM (readReg .cur_privilege) : SailME Step _) >>= fun p =>
        (liftM (dispatchInterrupt p) : SailME Step _) >>= fun o =>
          match o with
          | .some (intr, priv) =>
            (SailME.throw (Step.Step_Pending_Interrupt (intr, priv)) : SailME Step Unit) >>= fun _ =>
              (liftM (fetch ()) : SailME Step _) >>= rhaAfterFetch
          | none => (liftM (fetch ()) : SailME Step _) >>= rhaAfterFetch) := rfl

/-- Lean-only: the hart-state dispatch of `try_step` (the `step_val` producer). -/
noncomputable def WkStepPeel.tsHart : SailM Step :=
  readReg .hart_state >>= fun hs =>
    match hs with
    | .HART_WAITING (wr, instbits) => run_hart_waiting 0 wr instbits false
    | .HART_ACTIVE () => run_hart_active 0

/-- Lean-only: `try_step 0 false`, its register-only prefix spelled, its postlude the extracted
`tsAfterRha` (by `rfl`). -/
theorem WkStepPeel.tryStepUnfold :
    try_step 0 false =
      (readReg .cur_privilege >>= fun p =>
        should_inc_minstret p >>= fun b =>
          writeReg .minstret_increment b >>= fun _ =>
            WkStepPeel.tsHart >>= tsAfterRha) := rfl

/-! ## 1. THE TWO TRANSPORTS -/

/-- Rocq `wmstate_eq` (deviation: Lean's `Wmstate` has the sixth field `wmItv`). -/
theorem wmstateEq (s1 s2 : Wmstate) :
    s1.wmRegs = s2.wmRegs → s1.wmImg = s2.wmImg → s1.wmLog = s2.wmLog →
    s1.wmWs = s2.wmWs → s1.wmDev = s2.wmDev → s1.wmItv = s2.wmItv → s1 = s2 := by
  intro h1 h2 h3 h4 h5 h6
  cases s1
  cases s2
  simp only [Wmstate.mk.injEq]
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- Lean-only: a trace-emitting `execEff` arm never ends with the empty trace. -/
theorem WkStepPeel.consNeNil {X : Type} (e : Weff) (r : Option (X × ExecSt × List Weff)) (x : X)
    (t : ExecSt) : Weff.cons e r ≠ some (x, t, []) := by
  rcases r with _ | ⟨y, s', es⟩ <;> simp [Weff.cons]

/-- Rocq `wstep_ok_racy_k_of_eff_nil`: a REGISTER-ONLY (empty-trace) sub-run peels at any
phase, with its post-state read off its `execEff` fact (deviation: `s2.wmItv = s.wmItv`). -/
theorem wstepOkRacyKOfEffNil (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (D : PAddr → Nat → Prop) (W : Prop) {X : Type} (m : SailM X) :
    ∀ (b : Bool) (s s2 : Wmstate) (mm : BMap) (x : X) (t : ExecSt)
      (K : X → Wmstate → Bool → Prop),
      execEff m ⟨s.wmRegs, mm, s.wmDev⟩ = some (x, t, []) →
      s2.wmRegs = t.regs → s2.wmDev = t.dev →
      s2.wmImg = s.wmImg → s2.wmLog = s.wmLog → s2.wmWs = s.wmWs → s2.wmItv = s.wmItv →
      K x s2 b →
      wstepOkRacyK tid ra rn rak Φ D W b m s K := by
  induction m with
  | pure y =>
    intro b s s2 mm x t K hex hr hd hi hl hw hv hK
    simp only [execEff, Option.some.injEq, Prod.mk.injEq] at hex
    obtain ⟨rfl, rfl, -⟩ := hex
    have hs : s2 = s := wmstateEq s2 s hr hi hl hw hd hv
    subst hs
    exact hK
  | impure call k ih =>
    intro b s s2 mm x t K hex hr hd hi hl hw hv hK
    cases call with
    | error e => simp only [wstepOkRacyK]
    | ok o =>
      cases o
      case regWrite r v =>
        simp only [wstepOkRacyK]
        simp only [execEff] at hex
        exact ih _ b (wsetReg s r v) s2 mm x t K hex hr hd hi hl hw hv hK
      case memRead n va req =>
        simp only [wstepOkRacyK]
        simp only [execEff] at hex
        by_cases hm : mmioAcc req.pa n = true
        · rw [if_pos hm] at hex ⊢
          intro w d' hdr
          simp only [hdr] at hex
          exact ih _ b (wsetDev s d') s2 mm x t K hex hr hd hi hl hw hv hK
        · rw [if_neg hm] at hex
          split at hex
          · exact absurd hex (WkStepPeel.consNeNil _ _ _ _)
          · cases hex
      case memWrite n va req =>
        simp only [wstepOkRacyK]
        simp only [execEff] at hex
        cases hval : req.value with
        | none => simp only [hval, reduceCtorEq] at hex
        | some v =>
          simp only [hval] at hex ⊢
          by_cases hm : mmioAcc req.pa n = true
          · rw [if_pos hm] at hex ⊢
            intro d' hdw
            simp only [hdw] at hex
            exact ih _ b (wsetDev s d') s2 mm x t K hex hr hd hi hl hw hv hK
          · rw [if_neg hm] at hex
            exact absurd hex (WkStepPeel.consNeNil _ _ _ _)
      case barrier bk =>
        simp only [execEff] at hex
        exact absurd hex (WkStepPeel.consNeNil _ _ _ _)
      all_goals first
        | (simp only [execEff, reduceCtorEq] at hex; done)
        | (simp only [wstepOkRacyK]
           simp only [execEff] at hex
           exact ih _ b s s2 mm x t K hex hr hd hi hl hw hv hK)

/-- Rocq `wstep_ok_racy_kR_of_k_cer`: the CONVERSE of `wstepOkRacyKCer`. -/
theorem wstepOkRacyKROfKCer (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (D : PAddr → Nat → Prop) (W : Prop) (b : Bool) {X : Type}
    (m : SailME X X) (s : Wmstate) (K : X → Wmstate → Bool → Prop) :
    wstepOkRacyK tid ra rn rak Φ D W b (SailME.run m) s K →
    wstepOkRacyKR tid ra rn rak Φ D W b m s
      (fun v s' b' => K (match v with | .inl r => r | .inr y => y) s' b') := by
  intro h
  unfold wstepOkRacyKR
  change wstepOkRacyK tid ra rn rak Φ D W b (ExceptT.run m >>= _) s K at h
  rw [WkFetchPeel.wstepOkRacyKBindEq] at h
  refine WkFetchPeel.wstepOkRacyKMono tid ra rn rak Φ D W _ b s _ _ ?_ h
  intro v s' b' hv
  rcases v with (e | r) | x
  · exact True.intro
  · exact hv
  · exact hv

/-- Rocq `wstep_ok_racy_kR_triv_of_wstep_ok`. -/
theorem wstepOkRacyKRTrivOfWstepOk (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (b : Bool) {X : Type} (m : SailME X X) (s : Wmstate) :
    wstepOk tid (SailME.run m) s →
    wstepOkRacyKR tid ra rn rak Φ wDAny True b m s (fun _ _ _ => True) := fun h =>
  wstepOkRacyKROfKCer tid ra rn rak Φ wDAny True b m s (fun _ _ _ => True)
    ((wstepOkRacyKTriv tid ra rn rak Φ wDAny True b _ s).2
      (wstepOkRacyAnyOfWstepOk tid ra rn rak Φ b _ s h))

/-- Rocq `wstep_ok_racy_k_triv_of_wstep_ok`. -/
theorem wstepOkRacyKTrivOfWstepOk (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (b : Bool) {X : Type} (m : SailM X) (s : Wmstate) :
    wstepOk tid m s →
    wstepOkRacyK tid ra rn rak Φ wDAny True b m s (fun _ _ _ => True) := fun h =>
  (wstepOkRacyKTriv tid ra rn rak Φ wDAny True b m s).2
    (wstepOkRacyAnyOfWstepOk tid ra rn rak Φ b m s h)

/-- Rocq `wstep_ok_racy_k_write_reg`. -/
theorem wstepOkRacyKWriteReg (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (D : PAddr → Nat → Prop) (W : Prop) (b : Bool) (r : Register)
    (v : RegisterType r) (s : Wmstate) (K : Unit → Wmstate → Bool → Prop) :
    K () (wsetReg s r v) b →
    wstepOkRacyK tid ra rn rak Φ D W b (writeReg r v : SailM Unit) s K := id

/-- Rocq `wstep_ok_racy_k_quiet` (Rocq `∅` is the empty `BMap` `fun _ => none`). -/
theorem wstepOkRacyKQuiet (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (D : PAddr → Nat → Prop) (W : Prop) (b : Bool) {X : Type}
    (m : SailM X) (s : Wmstate) (x : X) (K : X → Wmstate → Bool → Prop) :
    execEff m ⟨s.wmRegs, fun _ => none, s.wmDev⟩ = some (x, ⟨s.wmRegs, fun _ => none, s.wmDev⟩, []) →
    K x s b →
    wstepOkRacyK tid ra rn rak Φ D W b m s K := fun hex hK =>
  wstepOkRacyKOfEffNil tid ra rn rak Φ D W m b s s _ x _ K hex rfl rfl rfl rfl rfl rfl hK

/-- Rocq `wstep_ok_racy_k_quiet_flat`. -/
theorem wstepOkRacyKQuietFlat (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (D : PAddr → Nat → Prop) (W : Prop) (b : Bool) {X : Type}
    (m : SailM X) (s : Wmstate) (x : X) (K : X → Wmstate → Bool → Prop) :
    execEff m (wflatSt s) = some (x, wflatSt s, []) →
    K x s b →
    wstepOkRacyK tid ra rn rak Φ D W b m s K := fun hex hK =>
  wstepOkRacyKOfEffNil tid ra rn rak Φ D W m b s s (wflatMem s.wmImg s.wmLog) x _ K hex
    rfl rfl rfl rfl rfl rfl hK

/-! ## 2. THE INTERFACES -/

/-- Rocq `wmi`: the post-`minstret_increment`-write state. -/
def wmi (σ : Wmstate) (b : Bool) : Wmstate := wsetReg σ .minstret_increment b

/-- Rocq `wexec_tail`. -/
def wexecTail (tid : Option Nat) (σ : Wmstate) : Prop :=
  ∀ (r : FetchResult) (s' : Wmstate), wrun tid (fetch ()) σ r s' →
    wstepOk tid (SailME.run (rhaAfterFetch r)) s'

/-- Rocq `wstep_post_tail`. -/
def wstepPostTail (tid : Option Nat) (σ : Wmstate) : Prop :=
  ∀ (sv : Step) (s' : Wmstate), wrun tid (run_hart_active 0) σ sv s' → wstepOk tid (tsAfterRha sv) s'

/-- Rocq `wstep_tick_tail`. -/
def wstepTickTail (tid : Option Nat) (σ : Wmstate) (tick : Bool) : Prop :=
  ∀ (x : Bool) (s' : Wmstate), wrun tid (try_step 0 false) σ x s' → wstepOk tid (stepTick tick) s'

/-- Rocq `wfetch_peel_k_at`: the fetch peel, in CPS form, as an interface. -/
def wfetchPeelKAt (tid : Option Nat) (la : PAddr) (Φ : (Nat → BitVec 8) → Prop) (σ : Wmstate) : Prop :=
  ∀ K : FetchResult → Wmstate → Bool → Prop,
    (∀ (r : FetchResult) (s' : Wmstate), wrun tid (fetch ()) σ r s' → ∀ b' : Bool, K r s' b') →
    wstepOkRacyK tid la 8 wakPlain Φ wDAny True true (fetch ()) σ K

/-! ## 3. THE PEEL OF `run_hart_active`, AND OF THE WHOLE STEP -/

/-- Rocq `wrha_peel`. -/
theorem wrhaPeel (tid : Option Nat) (σ : Wmstate) (la : PAddr) (Φ : (Nat → BitVec 8) → Prop) :
    σ.wmRegs .cur_privilege = .Supervisor →
    execEff (dispatchInterrupt .Supervisor) (wflatSt σ) = some (none, wflatSt σ, []) →
    wfetchPeelKAt tid la Φ σ →
    wexecTail tid σ →
    wstepOkRacy tid la 8 wakPlain Φ wDAny True true (run_hart_active 0) σ := by
  intro hpriv hdisp hfetch htail
  rw [← wstepOkRacyKTriv, WkStepPeel.runHartActiveUnfold]
  apply wstepOkRacyKCer
  -- the privilege read
  apply wstepOkRacyKRBind
  apply wstepOkRacyKRLiftR
  apply wstepOkRacyKReadReg
  try dsimp only
  rw [hpriv]
  -- the interrupt dispatch: register-only, and gated to `none`
  apply wstepOkRacyKRBind
  apply wstepOkRacyKRLiftR
  apply wstepOkRacyKQuietFlat _ _ _ _ _ _ _ _ _ σ none _ hdisp
  try dsimp only
  -- the seam
  apply wstepOkRacyKRBind
  apply wstepOkRacyKRLiftR
  apply hfetch
  intro r s' hrun b'
  exact wstepOkRacyKRTrivOfWstepOk tid la 8 wakPlain Φ b' (rhaAfterFetch r) s' (htail r s' hrun)

/-- Lean-only: a register other than `minstret_increment` survives the pre-write. -/
theorem WkStepPeel.wmiRegs (σ : Wmstate) (b : Bool) (r : Register) (h : r ≠ .minstret_increment) :
    (wmi σ b).wmRegs r = σ.wmRegs r :=
  RegFile.set_other _ _ _ _ h

/-- Rocq `wstep_peel`: THE WHOLE STEP. -/
theorem wstepPeel (tid : Option Nat) (σ : Wmstate) (la : PAddr) (Φ : (Nat → BitVec 8) → Prop)
    (tick : Bool) :
    σ.wmRegs .cur_privilege = .Supervisor →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    (∀ bmi : Bool, wstepOkRacy tid la 8 wakPlain Φ wDAny True true (run_hart_active 0) (wmi σ bmi)) →
    (∀ bmi : Bool, wstepPostTail tid (wmi σ bmi)) →
    wstepTickTail tid σ tick →
    wstepOkRacy tid la 8 wakPlain Φ wDAny True true (riscvStep tick) σ := by
  intro hpriv hhart hrha hpost htick
  rw [riscvStepUnfold]
  apply wstepOkRacyBind
  · rw [← wstepOkRacyKTriv, WkStepPeel.tryStepUnfold]
    -- the privilege read
    apply wstepOkRacyKBind
    apply wstepOkRacyKReadReg
    try dsimp only
    rw [hpriv]
    -- `should_inc_minstret`: register-only, and its answer is the funnel's
    apply wstepOkRacyKBind
    obtain ⟨bmi, hsi⟩ := execEffShouldIncMinstretSome .Supervisor (wflatSt σ)
    apply wstepOkRacyKQuietFlat _ _ _ _ _ _ _ _ _ σ bmi _ hsi
    try dsimp only
    -- the `minstret_increment` pre-write, and the hart-active gate after it
    apply wstepOkRacyKBind
    apply wstepOkRacyKWriteReg
    try dsimp only
    apply wstepOkRacyKBind
    unfold WkStepPeel.tsHart
    apply wstepOkRacyKBind
    apply wstepOkRacyKReadReg
    have hh : (wsetReg σ .minstret_increment bmi).wmRegs .hart_state = .HART_ACTIVE () :=
      (WkStepPeel.wmiRegs σ bmi .hart_state (by decide)).trans hhart
    try dsimp only
    rw [hh]
    try dsimp only
    -- `run_hart_active`, then the trap/retire postlude
    refine wstepOkRacyKOfRun _ _ _ _ _ _ _ _ _ _ _ (hrha bmi) ?_
    intro sv s'' hrun b'
    exact wstepOkRacyKTrivOfWstepOk tid la 8 wakPlain Φ b' (tsAfterRha sv) s'' (hpost bmi sv s'' hrun)
  · intro x s' hrun b'
    exact wstepOkRacyAnyOfWstepOk tid la 8 wakPlain Φ b' (stepTick tick) s' (htick x s' hrun)

/-! ## 4. THE STEP PEEL FROM THE FETCH-PEEL PREMISE BUNDLE -/

/-- Rocq `wfetch_ready`. -/
def wfetchReady (tid : Option Nat) (σ : Wmstate) (root : BitVec 44) (va pa p2 p1 w0 lw : BitVec 64)
    (region : PMA_Region) : Prop :=
  wwalkExports tid σ root va pa p2 p1 w0 lw ∧ wfetchGates tid σ va pa region

/-- Rocq `wstep_peel_fetchwalk` (the text pins are FETCH pins). -/
theorem wstepPeelFetchwalk (tid : Option Nat) (σ : Wmstate) (root : BitVec 44)
    (va pa p2 p1 w0 lw : BitVec 64) (region : PMA_Region) (w : BitVec 32) (tick : Bool) :
    let vpn := WeakKpt.svpnOf va
    let la := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)
    -- the step's own register gates, at σ
    σ.wmRegs .cur_privilege = .Supervisor →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    σ.wmRegs .PC = va →
    (∀ bmi : Bool, execEff (dispatchInterrupt .Supervisor) (wflatSt (wmi σ bmi)) =
      some (none, wflatSt (wmi σ bmi), [])) →
    -- the walk exports and the fetch's gates, at the post-write states
    (∀ bmi : Bool, wfetchReady tid (wmi σ bmi) root va pa p2 p1 w0 lw region) →
    -- the fetch's pure and log-shaped premises, at σ
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    raccDisj la 8 pa 4 →
    accWf pa 4 →
    (∀ j : Nat, j < 4 → paZ (pa + BitVec.ofNat 64 j) ≠ 0) →
    (∀ j : Nat, j < 4 → fetchPinned σ (WeakInterp.accAddr pa j)) →
    (∀ j : Nat, j < 4 → wflatMem σ.wmImg σ.wmLog (pa + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    is_aligned_paddr (.Physaddr pa) 4 = true →
    (override_PMA region.attributes .PBMT_PMA).executable = true →
    devAddr pa = false →
    -- the tails
    (∀ bmi : Bool, wexecTail tid (wmi σ bmi)) →
    (∀ bmi : Bool, wstepPostTail tid (wmi σ bmi)) →
    wstepTickTail tid σ tick →
    wstepOkRacy tid la 8 wakPlain (wwalkFilter w0 lw) wDAny True true (riscvStep tick) σ ∧
    wadmFilter σ wakPlain la 8 (wwalkFilter w0 lw) := by
  intro vpn la hpriv hhart hpc hdisp hready hal hdisj haccp hW0 hpin hbytes halign hexecp hdev
    hexec hpost htick
  have hpcb : ∀ bmi : Bool, (wmi σ bmi).wmRegs .PC = va := fun bmi =>
    (WkStepPeel.wmiRegs σ bmi .PC (by decide)).trans hpc
  have hprivb : ∀ bmi : Bool, (wmi σ bmi).wmRegs .cur_privilege = .Supervisor := fun bmi =>
    (WkStepPeel.wmiRegs σ bmi .cur_privilege (by decide)).trans hpriv
  have hfk : ∀ bmi : Bool, wfetchPeelKAt tid la (wwalkFilter w0 lw) (wmi σ bmi) := by
    intro bmi K hK
    obtain ⟨hexp, hgates⟩ := hready bmi
    exact (wfetchPeelKSelfcontained tid (wmi σ bmi) root va pa p2 p1 w0 lw region w K (hpcb bmi) hal
      hexp hdisj haccp hW0 hpin hbytes hgates halign hexecp hdev hK).1
  refine ⟨wstepPeel tid σ la (wwalkFilter w0 lw) tick hpriv hhart
    (fun bmi => wrhaPeel tid (wmi σ bmi) la _ (hprivb bmi) (hdisp bmi) (hfk bmi) (hexec bmi)) hpost htick, ?_⟩
  obtain ⟨hexp, hgates⟩ := hready false
  exact (wfetchPeelSelfcontained tid (wmi σ false) root va pa p2 p1 w0 lw region w (hpcb false) hal hexp
    hdisj haccp hW0 hpin hbytes hgates halign hexecp hdev).2

/-! ## 5. THE FAMILY — the whole step at the STALE MIRROR -/

/-- Rocq `trace_off_win_app`. -/
theorem traceOffWinApp (ra : PAddr) (rn : Nat) (es1 es2 : List Weff) :
    traceOffWin ra rn es1 → traceOffWin ra rn es2 → traceOffWin ra rn (es1 ++ es2) := by
  intro h1 h2 ak pa n hin hnp
  rcases List.mem_append.1 hin with hin | hin
  · exact h1 ak pa n hin hnp
  · exact h2 ak pa n hin hnp

/-- Rocq `trace_stale_app`. -/
theorem traceStaleApp (rak : AkInfo) (ra : PAddr) (rn : Nat) (es1 es2 : List Weff) :
    traceStale rak ra rn es1 → traceStale rak ra rn es2 → traceOffWin ra rn es2 →
    traceStale rak ra rn (es1 ++ es2) := by
  induction es1 with
  | nil => intro _ h2 _; exact h2
  | cons e es1 ih =>
    intro h1 h2 hoff
    cases e with
    | WEread ak pa n =>
      simp only [List.cons_append, traceStale] at h1 ⊢
      rcases h1 with ⟨hp, ht⟩ | ⟨hnp, hd, ht⟩ | ⟨hak, hpa, hn, ht⟩
      · exact Or.inl ⟨hp, ih ht h2 hoff⟩
      · exact Or.inr (Or.inl ⟨hnp, hd, ih ht h2 hoff⟩)
      · exact Or.inr (Or.inr ⟨hak, hpa, hn, traceOffWinApp ra rn es1 es2 ht hoff⟩)
    | WEwrite ak pa n v => simp only [traceStale] at h1
    | WEbar bk =>
      simp only [List.cons_append, traceStale] at h1 ⊢
      exact ih h1 h2 hoff

/-- Rocq `execR_stale_of_cer`: `catch_early_return`, backwards at the mirror. -/
theorem execRStaleOfCer (ra : PAddr) (rn : Nat) (u : BitVec (8 * rn)) {X : Type} (m : SailME X X)
    (s : ExecSt) (y : X) (t : ExecSt) (es : List Weff) :
    execStale ra rn u (SailME.run m) s = some (y, t, es) →
    ∃ v : X ⊕ X, execRStale ra rn u m s = some (v, t, es) ∧
      (match v with | .inl r => r | .inr r => r) = y := by
  intro h
  rw [execStaleCatchEarlyReturn] at h
  rcases he : execRStale ra rn u m s with _ | ⟨r | r, t0, es0⟩ <;> rw [he] at h
  · cases h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨.inl r, rfl, rfl⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨.inr r, rfl, rfl⟩

/-- Rocq `exec_stale_run_hart_active`. -/
theorem execStaleRunHartActive (la : PAddr) (u : BitVec (8 * 8)) (sa sf sx : ExecSt) (r : FetchResult)
    (sv : Step) (esf es1 : List Weff) :
    accWf la 8 →
    sa.regs .cur_privilege = .Supervisor →
    execEff (dispatchInterrupt .Supervisor) sa = some (none, sa, []) →
    execStale la 8 u (fetch ()) sa = some (r, sf, esf) →
    execEff (SailME.run (rhaAfterFetch r)) sf = some (sv, sx, es1) →
    traceOffWin la 8 es1 →
    execStale la 8 u (run_hart_active 0) sa = some (sv, sx, esf ++ es1) := by
  intro hacc hpriv hdisp hfetch htail hoff1
  have hts := execStaleOfExecEff la 8 u _ hacc sf sv sx es1 htail hoff1
  obtain ⟨vv, hvR, hvproj⟩ := execRStaleOfCer la 8 u (rhaAfterFetch r) sf sv sx es1 hts
  have hdisps := execStaleOfEffQuiet la 8 u _ sa sa none hacc hdisp
  rw [WkStepPeel.runHartActiveUnfold, execStaleCatchEarlyReturn]
  exec_stale_run [hpriv, hdisps, hfetch, hvR]
  rcases vv with rr | rr <;> simp only at hvproj <;> subst hvproj <;> rfl

/-- Rocq `exec_stale_riscv_step`: THE WHOLE STEP at the mirror. -/
theorem execStaleRiscvStep (la : PAddr) (u : BitVec (8 * 8)) (tick : Bool) (sg0 sx sy sfin : ExecSt)
    (bmi bb : Bool) (sv : Step) (esr es2 es3 : List Weff) :
    accWf la 8 →
    sg0.regs .cur_privilege = .Supervisor →
    execEff (should_inc_minstret .Supervisor) sg0 = some (bmi, sg0, []) →
    (sg0.setReg .minstret_increment bmi).regs .hart_state = .HART_ACTIVE () →
    execStale la 8 u (run_hart_active 0) (sg0.setReg .minstret_increment bmi) = some (sv, sx, esr) →
    execEff (tsAfterRha sv) sx = some (bb, sy, es2) →
    traceOffWin la 8 es2 →
    execEff (stepTick tick) sy = some ((), sfin, es3) →
    traceOffWin la 8 es3 →
    execStale la 8 u (riscvStep tick) sg0 = some ((), sfin, esr ++ (es2 ++ es3)) := by
  intro hacc hpriv hsi hhart hrha hpost hoff2 htick hoff3
  have hsis := execStaleOfEffQuiet la 8 u _ sg0 sg0 bmi hacc hsi
  have hposts := execStaleOfExecEff la 8 u _ hacc sx bb sy es2 hpost hoff2
  have hticks := execStaleOfExecEff la 8 u _ hacc sy () sfin es3 htick hoff3
  have htry : execStale la 8 u (try_step 0 false) sg0 = some (bb, sy, esr ++ es2) := by
    rw [WkStepPeel.tryStepUnfold]
    unfold WkStepPeel.tsHart
    exec_stale_run [hpriv, hsis, hhart, hrha, hposts]
  rw [riscvStepUnfold, execStaleBindSome la 8 u _ _ _ _ _ _ htry]
  simp only [hticks, List.append_assoc]

/-- Rocq `exec_stale_fetch_bytes_4_S` (O2: the text read is the i-cache read). -/
theorem execStaleFetchBytes4S (la : PAddr) (u : BitVec (8 * 8)) (va pa : BitVec 64) (w : BitVec 32)
    (s sg : ExecSt) (esw : List Weff) :
    accWf la 8 →
    accWf pa 4 →
    raccDisj la 8 pa 4 →
    execStale la 8 u (translateAddr (.Virtaddr va) (.InstructionFetch ())) s =
      some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sg, esw) →
    execEff (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr pa) 4 false false false) sg =
      some (.Ok w, sg, [.WEread WeakFetchEff.wakIfetch pa 4]) →
    execStale la 8 u (fetch_bytes va va 4) s =
      some (.FetchBytes_Success w, sg, esw ++ [.WEread WeakFetchEff.wakIfetch pa 4]) := by
  intro hacc haccp hdisj htr hmr
  have hoff : traceOffWin la 8 [.WEread WeakFetchEff.wakIfetch pa 4] :=
    traceOffWinOfAll _ _ _ fun ak pa0 n hin => by
      simp only [List.mem_singleton, Weff.WEread.injEq] at hin
      obtain ⟨rfl, rfl, rfl⟩ := hin
      exact ⟨haccp, hdisj⟩
  have hmrs := execStaleOfExecEff la 8 u _ hacc sg _ sg _ hmr hoff
  unfold fetch_bytes ext_fetch_check_pc
  rw [execStaleCatchEarlyReturn]
  exec_stale_run [htr, hmrs, Nat.reduceMul, BitVec.setWidth_eq]

/-- Rocq `exec_stale_fetch_S`: THE S-MODE FETCH AT THE MIRROR. -/
theorem execStaleFetchS (la : PAddr) (u : BitVec (8 * 8)) (va pa : BitVec 64) (w : BitVec 32)
    (s sg : ExecSt) (esw : List Weff) :
    accWf la 8 →
    accWf pa 4 →
    raccDisj la 8 pa 4 →
    s.regs .PC = va →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    isRVC (Sail.BitVec.extractLsb w 15 0) = false →
    execStale la 8 u (translateAddr (.Virtaddr va) (.InstructionFetch ())) s =
      some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sg, esw) →
    execEff (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr pa) 4 false false false) sg =
      some (.Ok w, sg, [.WEread WeakFetchEff.wakIfetch pa 4]) →
    execStale la 8 u (fetch ()) s =
      some (.F_Base w, sg, esw ++ [.WEread WeakFetchEff.wakIfetch pa 4]) := by
  intro hacc haccp hdisj hpc hval hnotRVC htr hmr
  have hzi := execStaleOfEffQuiet la 8 u _ s s true hacc (execEffCurrentlyEnabledZiccif s)
  have hfb := execStaleFetchBytes4S la u va pa w s sg esw hacc haccp hdisj htr hmr
  unfold fetch ext_fetch_check_pc get_config_rvfi
  rw [execStaleCatchEarlyReturn]
  exec_stale_run [hpc, bit0ClearOfAligned4 va hval, bit1ClearOfAligned4 va hval, hval, hzi, hfb,
    hnotRVC]

/-- Rocq `wstep_tail_eff`: the step's WINDOW-FREE tail, as one `execEff` interface. -/
def wstepTailEff (la : PAddr) (tick : Bool) (sf : ExecSt) (r : FetchResult) : Prop :=
  ∃ (sv : Step) (sx sy sfin : ExecSt) (bb : Bool) (es1 es2 es3 : List Weff),
    execEff (SailME.run (rhaAfterFetch r)) sf = some (sv, sx, es1) ∧
    execEff (tsAfterRha sv) sx = some (bb, sy, es2) ∧
    execEff (stepTick tick) sy = some ((), sfin, es3) ∧
    traceOffWin la 8 (es1 ++ (es2 ++ es3)) ∧
    traceStale wakPlain la 8 (es1 ++ (es2 ++ es3))

/-- Rocq `trace_off_win_app_l`. -/
theorem traceOffWinAppL (ra : PAddr) (rn : Nat) (es1 es2 : List Weff) :
    traceOffWin ra rn (es1 ++ es2) → traceOffWin ra rn es1 :=
  fun h ak pa n hin => h ak pa n (List.mem_append.2 (Or.inl hin))

/-- Rocq `trace_off_win_app_r`. -/
theorem traceOffWinAppR (ra : PAddr) (rn : Nat) (es1 es2 : List Weff) :
    traceOffWin ra rn (es1 ++ es2) → traceOffWin ra rn es2 :=
  fun h ak pa n hin => h ak pa n (List.mem_append.2 (Or.inr hin))

/-- Rocq `exec_stale_step_of_walk`: THE CORE ASSEMBLY, one whole step at the mirror from ONE
walk family member. -/
theorem execStaleStepOfWalk (la : PAddr) (u : BitVec (8 * 8)) (tick : Bool) (sg0 sg' : ExecSt)
    (bmi : Bool) (va pa : BitVec 64) (w : BitVec 32) (esw : List Weff) :
    accWf la 8 → accWf pa 4 → raccDisj la 8 pa 4 →
    sg0.regs .cur_privilege = .Supervisor →
    execEff (should_inc_minstret .Supervisor) sg0 = some (bmi, sg0, []) →
    (sg0.setReg .minstret_increment bmi).regs .cur_privilege = .Supervisor →
    (sg0.setReg .minstret_increment bmi).regs .PC = va →
    (sg0.setReg .minstret_increment bmi).regs .hart_state = .HART_ACTIVE () →
    execEff (dispatchInterrupt .Supervisor) (sg0.setReg .minstret_increment bmi) =
      some (none, sg0.setReg .minstret_increment bmi, []) →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    isRVC (Sail.BitVec.extractLsb w 15 0) = false →
    execStale la 8 u (translateAddr (.Virtaddr va) (.InstructionFetch ()))
        (sg0.setReg .minstret_increment bmi) =
      some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sg', esw) →
    execEff (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr pa) 4 false false false) sg' =
      some (.Ok w, sg', [.WEread WeakFetchEff.wakIfetch pa 4]) →
    wstepTailEff la tick sg' (.F_Base w) →
    ∃ (t' : ExecSt) (est : List Weff),
      execStale la 8 u (riscvStep tick) sg0 =
        some ((), t', esw ++ ([.WEread WeakFetchEff.wakIfetch pa 4] ++ est)) ∧
      traceOffWin la 8 est ∧ traceStale wakPlain la 8 est := by
  intro hacc haccp hdisj hpriv hsi hpriva hpc hhart hdisp hval hnotRVC htr hmr htail
  obtain ⟨sv, sx, sy, sfin, bb, es1, es2, es3, h1, h2, h3, hoff, hst⟩ := htail
  have hf := execStaleFetchS la u va pa w (sg0.setReg .minstret_increment bmi) sg' esw hacc haccp hdisj
    hpc hval hnotRVC htr hmr
  have hoff1 := traceOffWinAppL la 8 es1 (es2 ++ es3) hoff
  have hoff23 := traceOffWinAppR la 8 es1 (es2 ++ es3) hoff
  have hoff2 := traceOffWinAppL la 8 es2 es3 hoff23
  have hoff3 := traceOffWinAppR la 8 es2 es3 hoff23
  have hrha := execStaleRunHartActive la u (sg0.setReg .minstret_increment bmi) sg' sx (.F_Base w) sv
    (esw ++ [.WEread WeakFetchEff.wakIfetch pa 4]) es1 hacc hpriva hdisp hf h1 hoff1
  have hstep := execStaleRiscvStep la u tick sg0 sx sy sfin bmi bb sv _ es2 es3 hacc hpriv hsi hhart
    hrha h2 hoff2 h3 hoff3
  refine ⟨sfin, es1 ++ (es2 ++ es3), ?_, hoff, hst⟩
  rw [hstep]
  simp only [List.append_assoc]

/-- Rocq `wstep_family_ready`: the family-side interface, keyed on the mirror post-state. -/
def wstepFamilyReady (_tid : Option Nat) (σ : Wmstate) (la : PAddr) (va pa w0 lw : BitVec 64)
    (w : BitVec 32) (tick : Bool) : Prop :=
  ∀ (bmi : Bool) (u : BitVec (8 * 8)) (sg' : ExecSt) (esw : List Weff),
    wwalkFilter w0 lw (fun j : Nat => nthByte u j) →
    execStale la 8 u (translateAddr (.Virtaddr va) (.InstructionFetch ())) (wflatSt (wmi σ bmi)) =
      some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sg', esw) →
    execEff (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr pa) 4 false false false) sg' =
      some (.Ok w, sg', [.WEread WeakFetchEff.wakIfetch pa 4]) ∧
    wstepTailEff la tick sg' (.F_Base w)

/-- Rocq `wflat_st_wmi`. -/
theorem wflatStWmi (σ : Wmstate) (b : Bool) :
    wflatSt (wmi σ b) = (wflatSt σ).setReg .minstret_increment b := rfl

/-- Lean-only: the text read and a window-free tail, appended to a walk's trace. -/
theorem WkStepPeel.textTail (la pa : PAddr) (est : List Weff) :
    accWf pa 4 → raccDisj la 8 pa 4 → traceOffWin la 8 est → traceStale wakPlain la 8 est →
    traceStale wakPlain la 8 ([.WEread WeakFetchEff.wakIfetch pa 4] ++ est) ∧
    traceOffWin la 8 ([.WEread WeakFetchEff.wakIfetch pa 4] ++ est) := by
  intro haccp hdisj hoff hst
  have hsing : traceOffWin la 8 [.WEread WeakFetchEff.wakIfetch pa 4] :=
    traceOffWinOfAll _ _ _ fun ak pa0 n hin => by
      simp only [List.mem_singleton, Weff.WEread.injEq] at hin
      obtain ⟨rfl, rfl, rfl⟩ := hin
      exact ⟨haccp, hdisj⟩
  refine ⟨?_, traceOffWinApp _ _ _ _ hsing hoff⟩
  simp only [List.singleton_append, traceStale]
  exact Or.inr (Or.inl ⟨rfl, hdisj, hst⟩)

/-- Rocq `wstep_family_fetchwalk`: THE STEP FAMILY. -/
theorem wstepFamilyFetchwalk (tid : Option Nat) (σ : Wmstate) (root : BitVec 44)
    (va pa p2 p1 w0 lw : BitVec 64) (w : BitVec 32) (tick : Bool) :
    let vpn := WeakKpt.svpnOf va
    let la := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)
    σ.wmRegs .cur_privilege = .Supervisor →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    σ.wmRegs .PC = va →
    (∀ bmi : Bool, execEff (dispatchInterrupt .Supervisor) (wflatSt (wmi σ bmi)) =
      some (none, wflatSt (wmi σ bmi), [])) →
    (∀ bmi : Bool, wwalkExports tid (wmi σ bmi) root va pa p2 p1 w0 lw) →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    isRVC (Sail.BitVec.extractLsb w 15 0) = false →
    accWf pa 4 →
    raccDisj la 8 pa 4 →
    wstepFamilyReady tid σ la va pa w0 lw w tick →
    (∀ u : BitVec (8 * 8), wwalkFilter w0 lw (fun j : Nat => nthByte u j) →
      ∃ (y : Unit) (t' : ExecSt) (es : List Weff),
        execStale la 8 u (riscvStep tick) (wflatSt σ) = some (y, t', es) ∧
        traceStale wakPlain la 8 es) ∨
    (∀ u : BitVec (8 * 8), wwalkFilter w0 lw (fun j : Nat => nthByte u j) →
      ∃ (y : Unit) (t' : ExecSt) (es : List Weff),
        execStale la 8 u (riscvStep tick) (wflatSt σ) = some (y, t', es) ∧
        traceOffWin la 8 es) := by
  intro vpn la hpriv hhart hpc hdisp hexp hval hnotRVC haccp hdisj hready
  obtain ⟨bmi, hsi⟩ := execEffShouldIncMinstretSome .Supervisor (wflatSt σ)
  obtain ⟨-, -, -, -, hs0, -, hd2, hd1, -, harm, -⟩ := hexp bmi
  have hacc : accWf la 8 := ptSlotMemAccWf _ _ _ hs0
  -- the three register facts, past the `minstret_increment` pre-write
  have hpriva : ((wflatSt σ).setReg .minstret_increment bmi).regs .cur_privilege = .Supervisor :=
    (WkStepPeel.wmiRegs σ bmi .cur_privilege (by decide)).trans hpriv
  have hpca : ((wflatSt σ).setReg .minstret_increment bmi).regs .PC = va :=
    (WkStepPeel.wmiRegs σ bmi .PC (by decide)).trans hpc
  have hharta : ((wflatSt σ).setReg .minstret_increment bmi).regs .hart_state = .HART_ACTIVE () :=
    (WkStepPeel.wmiRegs σ bmi .hart_state (by decide)).trans hhart
  -- ONE family member, run through the whole step
  have hcore : ∀ (u : BitVec (8 * 8)) (sgm : ExecSt) (esm : List Weff),
      wwalkFilter w0 lw (fun j : Nat => nthByte u j) →
      execStale la 8 u (translateAddr (.Virtaddr va) (.InstructionFetch ())) (wflatSt (wmi σ bmi)) =
        some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sgm, esm) →
      ∃ (t' : ExecSt) (est : List Weff),
        execStale la 8 u (riscvStep tick) (wflatSt σ) =
          some ((), t', esm ++ ([.WEread WeakFetchEff.wakIfetch pa 4] ++ est)) ∧
        traceOffWin la 8 est ∧ traceStale wakPlain la 8 est := by
    intro u sgm esm hu hex
    obtain ⟨hmr, htail⟩ := hready bmi u sgm esm hu hex
    exact execStaleStepOfWalk la u tick (wflatSt σ) sgm bmi va pa w esm hacc haccp hdisj hpriv hsi hpriva
      hpca hharta (hdisp bmi) hval hnotRVC hex hmr htail
  rcases harm with hro | ⟨lw', wtr, -, hfam⟩
  · -- ---------- READ-ONLY: four stale-friendly shapes ----------
    left
    intro u hu
    obtain ⟨av, dv, rfl, hle⟩ := wwalkFilterInv w0 lw u hu
    obtain ⟨sgm, esm, hex, -, -, hes⟩ := hro av dv hle
    obtain ⟨t', est, hstep, hoffe, hste⟩ := hcore _ sgm esm hu hex
    obtain ⟨hf1, hf2⟩ := WkStepPeel.textTail la pa est haccp hdisj hoffe hste
    refine ⟨(), t', _, hstep, traceStaleApp _ _ _ _ _ ?_ hf1 hf2⟩
    refine traceStaleWalkShapes _ _ la lw esm hd2 hd1 ?_
    rcases hes with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · cases wtr with
    | true =>
      -- ---------- MISS write-back: the five-event walk ----------
      left
      intro u hu
      obtain ⟨av, dv, rfl, hle⟩ := wwalkFilterInv w0 lw u hu
      obtain ⟨sgm, esm, hex, -, -, hes⟩ := hfam av dv hle
      simp only [↓reduceIte] at hes
      obtain ⟨t', est, hstep, hoffe, hste⟩ := hcore _ sgm esm hu hex
      obtain ⟨hf1, hf2⟩ := WkStepPeel.textTail la pa est haccp hdisj hoffe hste
      exact ⟨(), t', _, hstep, traceStaleApp _ _ _ _ _
        (traceStaleWalkShapes _ _ la lw' esm hd2 hd1 (Or.inr (Or.inr (Or.inr (Or.inr hes))))) hf1 hf2⟩
    | false =>
      -- ---------- HIT write-back: the CONSTANT-family shape ----------
      right
      intro u hu
      obtain ⟨av, dv, rfl, hle⟩ := wwalkFilterInv w0 lw u hu
      obtain ⟨sgm, esm, hex, -, -, hes⟩ := hfam av dv hle
      simp only [Bool.false_eq_true, ↓reduceIte] at hes
      obtain ⟨t', est, hstep, hoffe, hste⟩ := hcore _ sgm esm hu hex
      obtain ⟨-, hf2⟩ := WkStepPeel.textTail la pa est haccp hdisj hoffe hste
      refine ⟨(), t', _, hstep, traceOffWinApp _ _ _ _ ?_ hf2⟩
      rw [hes]
      exact traceOffWinPinned _ _ _ (by walk_stale_trace)

/-! ## 6. THE Q-HALF: every outcome of the step matches a family member -/

/-- Rocq `wstep_outcome_of_peel` (Rocq's `is_Some (read_bytes …)` is `(bmRead …).isSome = true`). -/
theorem wstepOutcomeOfPeel (tid : Option Nat) (σ : Wmstate) (la : PAddr) (Φ : (Nat → BitVec 8) → Prop)
    (tick : Bool) :
    accWf la 8 →
    wlogWf σ.wmLog →
    (bmRead (wflatMem σ.wmImg σ.wmLog) la 8).isSome = true →
    wstepOkRacy tid la 8 wakPlain Φ wDAny True true (riscvStep tick) σ →
    wadmFilter σ wakPlain la 8 Φ →
    ((∀ u : BitVec (8 * 8), Φ (fun j : Nat => nthByte u j) →
        ∃ (y : Unit) (t' : ExecSt) (es : List Weff),
          execStale la 8 u (riscvStep tick) (wflatSt σ) = some (y, t', es) ∧
          traceStale wakPlain la 8 es) ∨
      (∀ u : BitVec (8 * 8), Φ (fun j : Nat => nthByte u j) →
        ∃ (y : Unit) (t' : ExecSt) (es : List Weff),
          execStale la 8 u (riscvStep tick) (wflatSt σ) = some (y, t', es) ∧
          traceOffWin la 8 es)) →
    ∀ (x : Unit) (s' : Wmstate), wrun tid (riscvStep tick) σ x s' →
      ∃ (u : BitVec (8 * 8)) (es : List Weff),
        wadm σ wakPlain la 8 u ∧ Φ (fun j : Nat => nthByte u j) ∧
        execStale la 8 u (riscvStep tick) (wflatSt σ) = some (x, wflatSt s', es) ∧
        wlogWf s'.wmLog ∧
        (∀ a : PAddr,
          wtraceWonly (fun (pa : PAddr) (n : Nat) => ∀ j : Nat, j < n → pa + BitVec.ofNat 64 j ≠ a) es →
          latestTs s'.wmLog (paZ a) = latestTs σ.wmLog (paZ a)) ∧
        s'.wmLog = σ.wmLog ++ wtraceMsgs tid σ.wmWs.wRelp es := by
  intro hacc hwf hrd hpeel hfilt hfam x s' hrun
  rcases hfam with hst | hoff
  · exact wrunExecStaleElimMsgs tid la 8 wakPlain Φ True _ hacc (by decide) akPinsPlain σ hpeel hwf hfilt
      hrd hst x s' hrun
  · exact wrunExecStaleElimConstMsgs tid la 8 wakPlain Φ True true _ hacc (by decide) akPinsPlain σ hpeel
      hwf hfilt hrd hoff x s' hrun

/-- Rocq `wstep_outcome_fetchwalk`: THE CAPSTONE (the text pins are FETCH pins). -/
theorem wstepOutcomeFetchwalk (tid : Option Nat) (σ : Wmstate) (root : BitVec 44)
    (va pa p2 p1 w0 lw : BitVec 64) (region : PMA_Region) (w : BitVec 32) (tick : Bool) :
    let vpn := WeakKpt.svpnOf va
    let la := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)
    -- the step's own register gates
    σ.wmRegs .cur_privilege = .Supervisor →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    σ.wmRegs .PC = va →
    (∀ bmi : Bool, execEff (dispatchInterrupt .Supervisor) (wflatSt (wmi σ bmi)) =
      some (none, wflatSt (wmi σ bmi), [])) →
    -- the walk exports and the fetch's gates
    (∀ bmi : Bool, wfetchReady tid (wmi σ bmi) root va pa p2 p1 w0 lw region) →
    -- the text window
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    isRVC (Sail.BitVec.extractLsb w 15 0) = false →
    raccDisj la 8 pa 4 →
    accWf pa 4 →
    (∀ j : Nat, j < 4 → paZ (pa + BitVec.ofNat 64 j) ≠ 0) →
    (∀ j : Nat, j < 4 → fetchPinned σ (WeakInterp.accAddr pa j)) →
    (∀ j : Nat, j < 4 → wflatMem σ.wmImg σ.wmLog (pa + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    is_aligned_paddr (.Physaddr pa) 4 = true →
    (override_PMA region.attributes .PBMT_PMA).executable = true →
    devAddr pa = false →
    -- the tails, on both sides of the bridge
    (∀ bmi : Bool, wexecTail tid (wmi σ bmi)) →
    (∀ bmi : Bool, wstepPostTail tid (wmi σ bmi)) →
    wstepTickTail tid σ tick →
    wstepFamilyReady tid σ la va pa w0 lw w tick →
    ∀ (x : Unit) (s' : Wmstate), wrun tid (riscvStep tick) σ x s' →
      ∃ (u : BitVec (8 * 8)) (es : List Weff),
        wadm σ wakPlain la 8 u ∧
        wwalkFilter w0 lw (fun j : Nat => nthByte u j) ∧
        execStale la 8 u (riscvStep tick) (wflatSt σ) = some (x, wflatSt s', es) ∧
        wlogWf s'.wmLog ∧
        (∀ a : PAddr,
          wtraceWonly (fun (pa0 : PAddr) (n : Nat) => ∀ j : Nat, j < n → pa0 + BitVec.ofNat 64 j ≠ a) es →
          latestTs s'.wmLog (paZ a) = latestTs σ.wmLog (paZ a)) ∧
        s'.wmLog = σ.wmLog ++ wtraceMsgs tid σ.wmWs.wRelp es := by
  intro vpn la hpriv hhart hpc hdisp hready hal hnotRVC hdisj haccp hW0 hpin hbytes halign hexecp hdev
    hexec hpost htick hfam
  obtain ⟨hexp0, -⟩ := hready false
  obtain ⟨-, hwf, -, -, hs0, -⟩ := hexp0
  have hacc : accWf la 8 := ptSlotMemAccWf _ _ _ hs0
  have hrd : (bmRead (wflatMem σ.wmImg σ.wmLog) la 8).isSome = true := by
    rw [bmRead_of_bytes (wflatMem σ.wmImg σ.wmLog) la 8 lw hs0.1]; rfl
  obtain ⟨hpeel, hfilt⟩ := wstepPeelFetchwalk tid σ root va pa p2 p1 w0 lw region w tick hpriv hhart hpc
    hdisp hready hal hdisj haccp hW0 hpin hbytes halign hexecp hdev hexec hpost htick
  exact wstepOutcomeOfPeel tid σ la (wwalkFilter w0 lw) tick hacc hwf hrd hpeel hfilt
    (wstepFamilyFetchwalk tid σ root va pa p2 p1 w0 lw w tick hpriv hhart hpc hdisp
      (fun bmi => (hready bmi).1) hal hnotRVC haccp hdisj hfam)

/-- Rocq `wexec_outcome_of_peel`: the FUNCTIONAL interpreter's outcomes at EVERY oracle. -/
theorem wexecOutcomeOfPeel (tid : Option Nat) (σ : Wmstate) (la : PAddr) (Φ : (Nat → BitVec 8) → Prop)
    (tick : Bool) :
    accWf la 8 →
    wlogWf σ.wmLog →
    (bmRead (wflatMem σ.wmImg σ.wmLog) la 8).isSome = true →
    wstepOkRacy tid la 8 wakPlain Φ wDAny True true (riscvStep tick) σ →
    wadmFilter σ wakPlain la 8 Φ →
    ((∀ u : BitVec (8 * 8), Φ (fun j : Nat => nthByte u j) →
        ∃ (y : Unit) (t' : ExecSt) (es : List Weff),
          execStale la 8 u (riscvStep tick) (wflatSt σ) = some (y, t', es) ∧
          traceStale wakPlain la 8 es) ∨
      (∀ u : BitVec (8 * 8), Φ (fun j : Nat => nthByte u j) →
        ∃ (y : Unit) (t' : ExecSt) (es : List Weff),
          execStale la 8 u (riscvStep tick) (wflatSt σ) = some (y, t', es) ∧
          traceOffWin la 8 es)) →
    ∀ (χ : List (List Nat)) (x : Unit) (s' : Wmstate) (χ' : List (List Nat)),
      wexec tid (riscvStep tick) χ σ = some (x, s', χ') →
      ∃ (u : BitVec (8 * 8)) (es : List Weff),
        wadm σ wakPlain la 8 u ∧ Φ (fun j : Nat => nthByte u j) ∧
        execStale la 8 u (riscvStep tick) (wflatSt σ) = some (x, wflatSt s', es) ∧
        wlogWf s'.wmLog ∧
        (∀ a : PAddr,
          wtraceWonly (fun (pa : PAddr) (n : Nat) => ∀ j : Nat, j < n → pa + BitVec.ofNat 64 j ≠ a) es →
          latestTs s'.wmLog (paZ a) = latestTs σ.wmLog (paZ a)) ∧
        s'.wmLog = σ.wmLog ++ wtraceMsgs tid σ.wmWs.wRelp es := by
  intro hacc hwf hrd hpeel hfilt hfam χ x s' χ' hex
  exact wstepOutcomeOfPeel tid σ la Φ tick hacc hwf hrd hpeel hfilt hfam x s'
    (wexecWrun tid (riscvStep tick) χ σ x s' χ' hex)

end Weak
