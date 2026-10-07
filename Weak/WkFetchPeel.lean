/-
Weak: **the peel of the S-mode FETCH** (walk-bridge §8, 6a first half): the peel of the WHOLE
`fetch ()` at the PC page's leaf window, from `WeakKptStale.wwalkPeelOfExports` (the peel of the
translation) and an ORDINARY-certified tail; its tail and gates discharged from the walk exports
and σ's registers; and the ONE fupd that turns the kernel-page-table resources into the bundles
the S-mode racy WP rule's site predicate is stated over.

Rocq: `iris/WkFetchPeel.v` @ xxvzwolszwmp (1892 lines; one Lean file, elaborates in ~3 s).

The Rocq header, in substance.  The fetch's translation sits under two early-return levels and a
`liftR`, so `WeakStale` §7's base-monad CPS kit cannot grab it directly: §1 is the CPS peel at the
early-return altitude (`wstepOkRacyKR`) with its bind / `liftR` / `catch_early_return` transports.
The pre-translation prefix is REGISTER-ONLY (PC reads, the closed `ext_fetch_check_pc` hook, the
alignment gates, `currentlyEnabled Ext_Ziccif`), so it peels at any phase from `PC = va` and the
4-alignment.  A 4-aligned fetch performs ONE translation and ONE 4-byte read; the 2-aligned arms
(two translations, two windows) are NOT covered (they need `WeakStale` §9's sequential kit).  After
the seam the fetch only READS kernel text, so the tail is an ordinary `wstepOk`, embedded and
phase-lifted (`wstepOkRacyAnyOfWstepOk`).  §2b is the tail's producer (a privilege-generic
`execEff` mirror of the read chain); §2 the peel from the exports bundle `wwalkExports` and the
tail obligation `wfetchTail`; §4 the tail discharged: `wwalkRunOutcome` lands every weak
translation run on a family member's `execStale` outcome (through `WeakStale` §10's ⇐-bridge),
so the text bytes keep their latest timestamp and contents; §5 the register-only gates from σ's
registers (the walk moves no register but `tlb`); §6 the fupd `wkptFetchPeelAt`, which re-emits
the absorption theorem's conclusion with `wwalkExports` / `wfetchGates` at the
post-`minstret_increment`-write states (`try_step` writes that flag before fetching) and the
region's `executable` (σ-level, hence uniform in the flag).  No graph-tier fact is used: the
file lives at the `wrun` / `execStale` level throughout.

**Deviations from Rocq.**
1. VOCABULARY as `Weak/WeakKptStale.lean` deviation 1, `Weak/WeakStale.lean` deviation 1 and
   `Weak/WeakEffSkel.lean` deviation 1: `Defs.monadR R exception X` ↦ `SailME R X`, `Defs.liftR`
   ↦ `liftM`, `Defs.catch_early_return` ↦ `SailME.run`, `Defs.returnR`/`returnm` ↦ `pure`,
   `Defs.read_reg` ↦ `readReg`, `register_lookup r (wm_regs σ)` ↦ `σ.wmRegs r`, `MState r m d` ↦
   `⟨r, m, d⟩ : ExecSt`, `gmap Arch.pa (bv 8)` ↦ `BMap`, `wflat img log !! a` ↦
   `wflatMem img log a`, `pa_add a j` ↦ `a + BitVec.ofNat 64 j`, `N.of_nat j < 4` ↦ `j < 4`,
   `nth_byte w j` (a 32-bit word) ↦ `nthByte (n := 4) w j`, `wset_reg σ (R_bool
   minstret_increment) bf` ↦ `wsetReg σ .minstret_increment bf`, `register_beq r tlb = false` ↦
   `r ≠ .tlb`, stdpp `Forall P es` ↦ `∀ e, e ∈ es → P e`, `vec_access_dec v 0` ↦ `v[0]!`,
   `eq_vec x 'b"1" = true` ↦ `(x == 1#1) = true`, `uint` ↦ `toNat`, `ram_base + ram_size` ↦
   `ramEnd`, `wak_excl` ↦ `wakExcl` (= `⟨false, true, false⟩`, as the absorption theorem spells
   it).  Statement-level `let`s that the statement does not use (`a2`, `a1` in §2/§4/§5) are
   dropped; `wwalkExports` keeps all four.
2. `wstepOkRacyKR` is not a second `Fixpoint` (as `WeakEffSkel` deviation 2 for `execREff`):
   Lean's `SailME R X` is `ExceptT (Error ⊕ R) SailM X`, so it is `wstepOkRacyK` of the
   `ExceptT` run, with `.error (.inr r)` the early return (`inl r`), `.ok x` the value (`inr x`)
   and a model exception (Rocq's `ExtraOutcome (inr _)`) owing `True`.  Its bind / `liftR` /
   `catch_early_return` rules are proved from the Lean-only `WkFetchPeel.wstepOkRacyKBindEq` (the
   base-monad bind rule as an EQUATION) and `WkFetchPeel.wstepOkRacyKMono` (monotonicity in `K`).
3. `hartSupports` is pure in Lean (`WeakFetchEff` deviation 4): `wstepOkRacyKHartSupportsZiccif`
   is stated on `pure (hartSupports .Ext_Ziccif)`.
4. O2 (`WeakFetchEff` deviation 2): the fetch's text read is the i-cache read `read_ram
   .Read_ifetch`, trace element `.WEread WeakFetchEff.wakIfetch pa 4` (Rocq `wak_plain`), so
   `execEffCheckedMemReadRamGen` / `execEffMemReadFetchGen` emit it, and `wstepOk` owes the FETCH
   pin `fetchPinned` (the instruction view covers the latest write) at it, not `pinned_read`.
5. Hence every premise "the four text bytes are pinned" is `fetchPinned σ (accAddr pa j)` in
   `wfetchTailRead`, `wfetchTailOfExports`, `wfetchPeelSelfcontained`, `wfetchPeelKSelfcontained`,
   `wfetchPeelOfRegs` and `wkptFetchPeelAt`; the σ → s' transport is the Lean-only
   `WkFetchPeel.fetchPinnedTsMono` with `wrunItvLe` (WeakInterp) (Rocq: `pinned_read_ts_mono` with
   `wrun_ws_le`).  `pinnedReadTsMono` keeps Rocq's statement (unused here).
6. `wwalkExports`' collapse field is for `rak.akIfetch = false` reads (`WeakKptStale` deviation
   4), which is what `wwalkPeelOfExports` demands and the absorption theorem exports.
7. §5: Rocq's `addr_is_ram pa ∧ addr_is_ram (pa_add pa 3)` ↦ `inRam pa 4` (`WeakFetchEff`
   deviation 8); `pma_allows_all regions` ↦ `regions = bootPMA` (`WeakKptStale` deviation 3), so
   `wfetchRegionOfRegs`' region is `ramRegion` (`matching_pma_ram`, `ramRegionExec`); `dev_addr pa
   = false` is `devAddrRam`.
8. §6 as `WeakKptStale` deviation 3: contexts `[MachGS hlc GF] [WeakGS GF] [WeakKpt.KptGS GF]`, an
   explicit `cpu`, `kmap_at (svpn_of va) ppn pc` ↦ `kmapAt (WeakKpt.svpnOf va) (kLeaf ppn pc 0#1
   0#1)`, `mk_pte ppn (kperm_flags pc)` ↦ `mkPte ppn pc.flags`, `P -∗ … ={E}=∗ R` ↦
   `P ∗ … ⊢ |={E}=> R`, the wand's `==∗` ↦ `-∗ |==>`; the conclusion's σ-level pieces are the
   absorption theorem's (statement-level `let`s inlined, as there).
9. PROOF STRUCTURE: Rocq's one-step-at-a-time peel of `fetch` (`apply`s of the §1 rules) ↦ `simp`
   normalisation with the Lean-only equations `WkFetchPeel.wstepOkRacyKBindEq`,
   `WkFetchPeel.wstepOkRacyKPure`, `WkFetchPeel.runLiftM`, split at `fetch_bytes` into the
   Lean-only `WkFetchPeel.fetchBytesPeel` (the seam and the tail) and
   `WkFetchPeel.fetchPeelOfBytes` (the register-only prefix).  Statements unchanged.
10. Rocq §3's `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  `wstep_ok_racy_kR` `wstepOkRacyKR`, `wstep_ok_racy_kR_bind`
`wstepOkRacyKRBind`, `wstep_ok_racy_kR_liftR` `wstepOkRacyKRLiftR`, `wstep_ok_racy_k_cer`
`wstepOkRacyKCer`, `wstep_ok_racy_kR_ret` `wstepOkRacyKRRet`, `wstep_ok_racy_kR_read_reg`
`wstepOkRacyKRReadReg`, `wstep_ok_racy_k_ret` `wstepOkRacyKRet`, `wstep_ok_racy_k_read_reg`
`wstepOkRacyKReadReg`, `wstep_ok_racy_k_hartSupports_Ziccif` `wstepOkRacyKHartSupportsZiccif`,
`wstep_ok_racy_k_currentlyEnabled_Ziccif` `wstepOkRacyKCurrentlyEnabledZiccif`,
`wstep_ok_racy_any_of_wstep_ok` `wstepOkRacyAnyOfWstepOk`, `avi0_mul4'` `avi0Mul4'`,
`exec_eff_checked_mem_read_ram_gen` `execEffCheckedMemReadRamGen`, `exec_eff_mem_read_fetch_gen`
`execEffMemReadFetchGen`, `wfetch_tail_read` `wfetchTailRead`, `wfetch_tail` `wfetchTail`,
`wwalk_exports` `wwalkExports`, `wfetch_peel_of_exports` `wfetchPeelOfExports`, `wfetch_peel_k`
`wfetchPeelK`, `pinned_read_ts_mono` `pinnedReadTsMono`, `wwalk_filter_inv` `wwalkFilterInv`,
`wtrace_wonly_of_evs` `wtraceWonlyOfEvs`, `wwalk_run_outcome` `wwalkRunOutcome`, `wfetch_gates`
`wfetchGates`, `wfetch_tail_of_exports` `wfetchTailOfExports`, `wfetch_peel_selfcontained`
`wfetchPeelSelfcontained`, `wfetch_peel_k_selfcontained` `wfetchPeelKSelfcontained`,
`exec_eff_pmpCheck_supervisor_grant_fetch` `execEffPmpCheckSupervisorGrantFetch`,
`wfetch_region_of_regs` `wfetchRegionOfRegs`, `wfetch_gates_of_region` `wfetchGatesOfRegion`,
`wfetch_gates_of_regs` `wfetchGatesOfRegs`, `wfetch_peel_of_regs` `wfetchPeelOfRegs`,
`wkpt_fetch_peel_at` `wkptFetchPeelAt` (none in the duplicated-name table).  Lean-only
(file-qualified): `WkFetchPeel.wstepOkRacyKMono`, `WkFetchPeel.wstepOkRacyKBindEq`,
`WkFetchPeel.wstepOkRacyKPure`, `WkFetchPeel.runLiftM`, `WkFetchPeel.fetchBytesPeel`,
`WkFetchPeel.fetchPeelOfBytes`, `WkFetchPeel.fetchPinnedTsMono`.

**Dropped:** `bindR_Ret`, `bindR_Next` (the `monadR` bind reductions: `ExceptT`'s bind is not a
`FreeM` node, as `Weak/Exec.lean`'s map records for their `RiscvTryStep` twins; the weak files that
mention them use those twins).  35 Rocq declarations (`Definition`/`Fixpoint`/`Lemma`, one
`Local`): 33 ported + 7 Lean-only = 40 Lean declarations.

**Statements checked** (by hand, against Rocq): all; the changed ones are deviations 2-8.
-/
import Weak.WeakKptStale
import Weak.WeakFetchEff

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. THE CPS PEEL AT THE EARLY-RETURN ALTITUDE -/

section KR

variable (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
  (Φ : (Nat → BitVec 8) → Prop) (D : PAddr → Nat → Prop) (W : Prop)

/-- Lean-only: monotonicity of the CPS peel in its continuation. -/
theorem WkFetchPeel.wstepOkRacyKMono {X : Type} (m : SailM X) :
    ∀ (b : Bool) (s : Wmstate) (K1 K2 : X → Wmstate → Bool → Prop),
      (∀ x s' b', K1 x s' b' → K2 x s' b') →
      wstepOkRacyK tid ra rn rak Φ D W b m s K1 → wstepOkRacyK tid ra rn rak Φ D W b m s K2 := by
  induction m with
  | pure y => intro b s K1 K2 hK h; exact hK _ _ _ h
  | impure call k ih =>
    intro b s K1 K2 hK hok
    cases call with
    | error e => simp only [wstepOkRacyK]
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [wstepOkRacyK] at hok ⊢
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hok ⊢
          exact fun w d' hdr => ih _ _ _ _ _ hK (hok w d' hdr)
        · rw [if_neg hd] at hok ⊢
          obtain ⟨hacc, hor⟩ := hok
          refine ⟨hacc, ?_⟩
          rcases hor with ⟨hdisj, hpin, hk⟩ | ⟨hb, hpa, hn, hak, hk⟩
          · exact Or.inl ⟨hdisj, hpin, fun w hw => ih _ _ _ _ _ hK (hk w hw)⟩
          · exact Or.inr ⟨hb, hpa, hn, hak, fun ts w hw hΦ => ih _ _ _ _ _ hK (hk ts w hw hΦ)⟩
      case memWrite n va req =>
        simp only [wstepOkRacyK] at hok ⊢
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at hok ⊢
          cases hv : req.value with
          | none => trivial
          | some v =>
            simp only [hv] at hok ⊢
            exact fun d' hdw => ih _ _ _ _ _ hK (hok d' hdw)
        · rw [if_neg hd] at hok ⊢
          obtain ⟨hb, hacc, hdisj, hk⟩ := hok
          refine ⟨hb, hacc, hdisj, ?_⟩
          cases hv : req.value with
          | none => trivial
          | some v =>
            simp only [hv] at hk ⊢
            exact ih _ _ _ _ _ hK hk
      all_goals first
        | (simp only [wstepOkRacyK] at hok ⊢; done)
        | (simp only [wstepOkRacyK] at hok ⊢
           exact ih _ _ _ _ _ hK hok)

/-- Lean-only: the CPS bind rule as an EQUATION (the base monad's `bind` is a `FreeM` bind, so
both sides unfold node for node). -/
theorem WkFetchPeel.wstepOkRacyKBindEq {X Y : Type} (m : SailM X) (f : X → SailM Y) :
    ∀ (b : Bool) (s : Wmstate) (K : Y → Wmstate → Bool → Prop),
      wstepOkRacyK tid ra rn rak Φ D W b (m >>= f) s K =
        wstepOkRacyK tid ra rn rak Φ D W b m s
          (fun x s' b' => wstepOkRacyK tid ra rn rak Φ D W b' (f x) s' K) := by
  induction m with
  | pure y => intro b s K; rfl
  | impure call k ih =>
    intro b s K
    rw [bindNext]
    cases call with
    | error e => simp only [wstepOkRacyK]
    | ok o =>
      cases o
      case memWrite n va req =>
        simp only [wstepOkRacyK]
        cases req.value <;> simp only [ih]
      all_goals simp only [wstepOkRacyK, ih]

/-- Lean-only: the CPS peel at a `pure` leaf (the `Pure.pure` spelling). -/
theorem WkFetchPeel.wstepOkRacyKPure {X : Type} (b : Bool) (y : X) (s : Wmstate)
    (K : X → Wmstate → Bool → Prop) :
    wstepOkRacyK tid ra rn rak Φ D W b (pure y : SailM X) s K = K y s b := rfl

/-- Rocq `wstep_ok_racy_kR` (deviation 2): the CPS peel of an early-return computation, as the
base-monad peel of its `ExceptT` run; the early return is `inl`, the value `inr`, a model
exception (Rocq's stuck `ExtraOutcome (inr _)`) owes nothing. -/
def wstepOkRacyKR {R X : Type} (b : Bool) (m : SailME R X) (s : Wmstate)
    (K : R ⊕ X → Wmstate → Bool → Prop) : Prop :=
  wstepOkRacyK tid ra rn rak Φ D W b (ExceptT.run m) s (fun v s' b' =>
    match v with
    | .ok x => K (.inr x) s' b'
    | .error (.inr r) => K (.inl r) s' b'
    | .error (.inl _) => True)

/-- Rocq `wstep_ok_racy_kR_bind`. -/
theorem wstepOkRacyKRBind (b : Bool) {R X Y : Type} (m : SailME R X) (f : X → SailME R Y)
    (s : Wmstate) (K : R ⊕ Y → Wmstate → Bool → Prop) :
    wstepOkRacyKR tid ra rn rak Φ D W b m s
      (fun v s' b' =>
        match v with
        | .inl r => K (.inl r) s' b'
        | .inr x => wstepOkRacyKR tid ra rn rak Φ D W b' (f x) s' K) →
    wstepOkRacyKR tid ra rn rak Φ D W b (m >>= f) s K := by
  intro h
  unfold wstepOkRacyKR at h ⊢
  rw [ExceptT.run_bind, WkFetchPeel.wstepOkRacyKBindEq]
  refine WkFetchPeel.wstepOkRacyKMono tid ra rn rak Φ D W _ b s _ _ ?_ h
  intro v s' b' hv
  rcases v with (e | r) | x
  · trivial
  · exact hv
  · exact hv

/-- Rocq `wstep_ok_racy_kR_liftR`. -/
theorem wstepOkRacyKRLiftR (b : Bool) {R X : Type} (m : SailM X) (s : Wmstate)
    (K : R ⊕ X → Wmstate → Bool → Prop) :
    wstepOkRacyK tid ra rn rak Φ D W b m s (fun x s' b' => K (.inr x) s' b') →
    wstepOkRacyKR tid ra rn rak Φ D W b (liftM m : SailME R X) s K := by
  intro h
  unfold wstepOkRacyKR
  have e : ExceptT.run (liftM m : SailME R X) = m >>= fun a => pure (Except.ok a) := rfl
  rw [e, WkFetchPeel.wstepOkRacyKBindEq]
  exact h

/-- Rocq `wstep_ok_racy_k_cer`. -/
theorem wstepOkRacyKCer (b : Bool) {X : Type} (m : SailME X X) (s : Wmstate)
    (K : X → Wmstate → Bool → Prop) :
    wstepOkRacyKR tid ra rn rak Φ D W b m s
      (fun v s' b' => K (match v with | .inl r => r | .inr y => y) s' b') →
    wstepOkRacyK tid ra rn rak Φ D W b (SailME.run m) s K := by
  intro h
  unfold wstepOkRacyKR at h
  show wstepOkRacyK tid ra rn rak Φ D W b (ExceptT.run m >>= _) s K
  rw [WkFetchPeel.wstepOkRacyKBindEq]
  refine WkFetchPeel.wstepOkRacyKMono tid ra rn rak Φ D W _ b s _ _ ?_ h
  intro v s' b' hv
  rcases v with (e | r) | x
  · exact True.intro
  · exact hv
  · exact hv

/-- Lean-only: the `ExceptT` run of a lifted base-monad computation. -/
theorem WkFetchPeel.runLiftM {R X : Type} (m : SailM X) :
    ExceptT.run (liftM m : SailME R X) = m >>= fun a => pure (Except.ok a) := rfl

/-- Rocq `wstep_ok_racy_kR_ret`. -/
theorem wstepOkRacyKRRet (b : Bool) {R X : Type} (x : X) (s : Wmstate)
    (K : R ⊕ X → Wmstate → Bool → Prop) :
    K (.inr x) s b → wstepOkRacyKR tid ra rn rak Φ D W b (pure x : SailME R X) s K := id

/-- Rocq `wstep_ok_racy_kR_read_reg`. -/
theorem wstepOkRacyKRReadReg (b : Bool) {R : Type} (r : Register) (s : Wmstate)
    (K : R ⊕ RegisterType r → Wmstate → Bool → Prop) :
    K (.inr (s.wmRegs r)) s b →
    wstepOkRacyKR tid ra rn rak Φ D W b (liftM (readReg r) : SailME R (RegisterType r)) s K := id

/-- Rocq `wstep_ok_racy_k_ret`. -/
theorem wstepOkRacyKRet (b : Bool) {X : Type} (x : X) (s : Wmstate)
    (K : X → Wmstate → Bool → Prop) :
    K x s b → wstepOkRacyK tid ra rn rak Φ D W b (pure x : SailM X) s K := id

/-- Rocq `wstep_ok_racy_k_read_reg`. -/
theorem wstepOkRacyKReadReg (b : Bool) (r : Register) (s : Wmstate)
    (K : RegisterType r → Wmstate → Bool → Prop) :
    K (s.wmRegs r) s b → wstepOkRacyK tid ra rn rak Φ D W b (readReg r) s K := id

/-- Rocq `wstep_ok_racy_k_hartSupports_Ziccif` (deviation 3: `hartSupports` is pure). -/
theorem wstepOkRacyKHartSupportsZiccif (b : Bool) (s : Wmstate) (K : Bool → Wmstate → Bool → Prop) :
    K true s b →
    wstepOkRacyK tid ra rn rak Φ D W b (pure (hartSupports .Ext_Ziccif) : SailM Bool) s K := by
  intro h
  rw [execEffHartSupportsZiccif]
  exact h

/-- Rocq `wstep_ok_racy_k_currentlyEnabled_Ziccif`. -/
theorem wstepOkRacyKCurrentlyEnabledZiccif (b : Bool) (s : Wmstate)
    (K : Bool → Wmstate → Bool → Prop) :
    K true s b → wstepOkRacyK tid ra rn rak Φ D W b (currentlyEnabled .Ext_Ziccif) s K := by
  intro h
  rw [currentlyEnabled]
  simp only [execEffHartSupportsZiccif]
  exact h

end KR

/-- Rocq `wstep_ok_racy_any_of_wstep_ok`: §4's embedding at EITHER phase. -/
theorem wstepOkRacyAnyOfWstepOk (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (b : Bool) {X : Type} (m : SailM X) (s : Wmstate) :
    wstepOk tid m s → wstepOkRacy tid ra rn rak Φ wDAny True b m s := by
  intro h
  cases b
  · exact wstepOkRacyFalseOfWstepOk tid ra rn rak Φ True m s h
  · exact wstepOkRacyPhaseMono tid ra rn rak Φ wDAny m s
      (wstepOkRacyFalseOfWstepOk tid ra rn rak Φ True m s h)

/-! ## 2b. THE TAIL'S PRODUCER: the S-mode instruction read, at `execEff` -/

/-- Rocq `avi0_mul4'` (a Rocq `Local` restatement). -/
theorem avi0Mul4' (a : BitVec 64) : Sail.BitVec.addInt a (0 * 4) = a := WeakFetchEff.avi0Mul4 a

/-- Rocq `exec_eff_checked_mem_read_ram_gen`: `execEffCheckedMemReadRam` at any privilege. -/
theorem execEffCheckedMemReadRamGen (priv : Privilege) (pbmt : page_based_mem_type) (addr : BitVec 64)
    (region : PMA_Region) (w : BitVec 32) (s : ExecSt)
    (hpmp : execEff (pmpCheck (.Physaddr addr) 4 (.InstructionFetch ()) priv) s = some (none, s, []))
    (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (halign : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hexec : (override_PMA region.attributes pbmt).executable = true)
    (hc : execEff (within_clint (.Physaddr addr) 4) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr addr) 4) s = some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr addr) 4) s = some (false, s, []))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 4 w) :
    execEff (checked_mem_read (.InstructionFetch ()) pbmt priv (.Physaddr addr) 4 false false false false) s =
      some (.Ok (w, default_meta), s, [.WEread WeakFetchEff.wakIfetch addr 4]) := by
  have hpma := execEffPmaCheckRam addr pbmt region s hmatch halign hexec
  have hmm := execEffWithinMmioReadableFalse addr 4 s hc hsig hh
  have hrr := WeakFetchEff.execEffReadRamIfetch4 addr w s hdev hb
  unfold checked_mem_read check_pma_with_pmp_priority
  rw [execEffCatchEarlyReturn]
  exec_eff_mem [hpma]
  exec_eff_mem [hpmp, hmm, hrr, read_kind_of_flags]
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, BitVec.setWidth_eq]
  congr
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
  bv_decide

/-- Rocq `exec_eff_mem_read_fetch_gen`: `execEffMemReadFetch` at any privilege. -/
theorem execEffMemReadFetchGen (priv : Privilege) (pbmt : page_based_mem_type) (addr : BitVec 64)
    (region : PMA_Region) (w : BitVec 32) (s : ExecSt)
    (hpmp : execEff (pmpCheck (.Physaddr addr) 4 (.InstructionFetch ()) priv) s = some (none, s, []))
    (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (halign : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hexec : (override_PMA region.attributes pbmt).executable = true)
    (hc : execEff (within_clint (.Physaddr addr) 4) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr addr) 4) s = some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr addr) 4) s = some (false, s, []))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 4 w)
    (hpriv : s.regs .cur_privilege = priv) :
    execEff (mem_read (.InstructionFetch ()) pbmt (.Physaddr addr) 4 false false false) s =
      some (.Ok w, s, [.WEread WeakFetchEff.wakIfetch addr 4]) := by
  have hck := execEffCheckedMemReadRamGen priv pbmt addr region w s hpmp hmatch halign hexec hc hsig hh hdev hb
  unfold mem_read mem_read_priv mem_read_priv_meta
  exec_eff_run [hpriv, execEffEffectivePrivilegeFetch, hck]
  first
  | rfl
  | simp only [Nat.reduceMul, BitVec.setWidth_eq]

/-- Rocq `wfetch_tail_read` (deviations 4–5): the tail's ORDINARY certificate, from the
FETCH pins of the four text bytes and the flat memory's contents at them. -/
theorem wfetchTailRead (tid : Option Nat) (s : Wmstate) (pa : BitVec 64) (region : PMA_Region)
    (w : BitVec 32) :
    wlogWf s.wmLog →
    accWf pa 4 →
    (∀ j : Nat, j < 4 → paZ (pa + BitVec.ofNat 64 j) ≠ 0) →
    (∀ j : Nat, j < 4 → fetchPinned s (WeakInterp.accAddr pa j)) →
    (∀ j : Nat, j < 4 → wflatMem s.wmImg s.wmLog (pa + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    (∀ mm : BMap,
      execEff (pmpCheck (.Physaddr pa) 4 (.InstructionFetch ()) .Supervisor) ⟨s.wmRegs, mm, s.wmDev⟩ =
        some (none, ⟨s.wmRegs, mm, s.wmDev⟩, []) ∧
      matching_pma_region (s.wmRegs .pma_regions) (.Physaddr pa) 4 = some region ∧
      execEff (within_clint (.Physaddr pa) 4) ⟨s.wmRegs, mm, s.wmDev⟩ =
        some (false, ⟨s.wmRegs, mm, s.wmDev⟩, []) ∧
      execEff (within_sig (.Physaddr pa) 4) ⟨s.wmRegs, mm, s.wmDev⟩ =
        some (false, ⟨s.wmRegs, mm, s.wmDev⟩, []) ∧
      execEff (within_htif_readable (.Physaddr pa) 4) ⟨s.wmRegs, mm, s.wmDev⟩ =
        some (false, ⟨s.wmRegs, mm, s.wmDev⟩, [])) →
    is_aligned_paddr (.Physaddr pa) 4 = true →
    (override_PMA region.attributes .PBMT_PMA).executable = true →
    devAddr pa = false →
    s.wmRegs .cur_privilege = .Supervisor →
    wstepOk tid (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr pa) 4 false false false) s := by
  intro hwf _hacc hW0 hpin hbytes hgates halign hexecp hdev hpriv
  obtain ⟨hpmp, hmatch, hc, hsig, hh⟩ := hgates (wmemRestrict s (accWin [pa] 4))
  have hbf : BytesAt ⟨s.wmRegs, wmemRestrict s (accWin [pa] 4), s.wmDev⟩ pa 4 w := fun j hj =>
    wmemRestrictLookup s _ _ _ (accWinIn [pa] 4 pa j (by simp) hj) (hbytes j hj)
  have hex := execEffMemReadFetchGen .Supervisor .PBMT_PMA pa region w
    ⟨s.wmRegs, wmemRestrict s (accWin [pa] 4), s.wmDev⟩ hpmp hmatch halign hexecp hc hsig hh hdev hbf hpriv
  refine (wstepEffConfinedPin tid _ s (wmemRestrict s (accWin [pa] 4)) (accWin [pa] 4) _ _ _ hwf ?_ ?_
    (wmemRestrictDom s _) (wmemRestrictSub s _) (wmemRestrictDom s _) hex).1
  · intro a ha
    obtain ⟨b, j, hb, hj, rfl⟩ := accWinInv _ _ _ ha
    simp only [List.mem_singleton] at hb
    subst hb
    exact hW0 j hj
  · refine ⟨fun ak pa0 n0 hin _ j hj => ?_, ⟨fun _ _ _ hin => by simp at hin, trivial⟩⟩
    simp only [List.mem_singleton, Weff.WEread.injEq] at hin
    obtain ⟨rfl, rfl, rfl⟩ := hin
    simp only [readPinned, WeakFetchEff.wakIfetch, ↓reduceIte]
    exact hpin j hj

/-! ## 2. THE FETCH PEEL -/

/-- Rocq `wfetch_tail`: at every state the weak translation run can reach, the outcome is the
walked `pa` and the instruction read at it is an ORDINARY `wstepOk`. -/
def wfetchTail (tid : Option Nat) (σ : Wmstate) (va pa : BitVec 64) : Prop :=
  ∀ x s', wrun tid (translateAddr (.Virtaddr va) (.InstructionFetch ())) σ x s' →
    x = .Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw) ∧
    wstepOk tid (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr pa) 4 false false false) s'

/-- Rocq `wwalk_exports` (deviation 6): `wwalkPeelOfExports`' premise set at
`acc := InstructionFetch ()`, plus the hoisted sregs footprint of the member that ran. -/
def wwalkExports (_tid : Option Nat) (σ : Wmstate) (root : BitVec 44) (va pa p2 p1 w0 lw : BitVec 64) :
    Prop :=
  let vpn := WeakKpt.svpnOf va
  let a2 := uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)
  let a1 := uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)
  let la := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)
  (∃ a d : BitVec 1, lw = pteSetAD w0 a d) ∧
  wlogWf σ.wmLog ∧
  WeakWalkEff.ptSlotMem (wflatSt σ) a2 p2 ∧
  WeakWalkEff.ptSlotMem (wflatSt σ) a1 p1 ∧
  WeakWalkEff.ptSlotMem (wflatSt σ) la lw ∧
  (∀ j : Nat, j < 8 →
    pinnedRead σ (WeakInterp.accAddr a2 j) ∧ pinnedRead σ (WeakInterp.accAddr a1 j)) ∧
  raccDisj la 8 a2 8 ∧
  raccDisj la 8 a1 8 ∧
  (∀ (rak : AkInfo) (wv : BitVec (8 * 8)), rak.akIfetch = false → wadm σ rak la 8 wv →
    (∃ a d : BitVec 1, wv = pteSetAD w0 a d) ∧ pteAdLe wv lw) ∧
  ( -- READ-ONLY
    (∀ av dv : BitVec 1, pteAdLe (pteSetAD w0 av dv) lw →
      ∃ (sg' : ExecSt) (es : List Weff),
        execStale la 8 (pteSetAD w0 av dv) (translateAddr (.Virtaddr va) (.InstructionFetch ())) (wflatSt σ) =
          some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sg', es) ∧
        sg'.mem = wflatMem σ.wmImg σ.wmLog ∧
        sg'.dev = σ.wmDev ∧
        (es = [] ∨
         es = [.WEread wakPlain a2 8, .WEread wakPlain a1 8, .WEread wakPlain la 8] ∨
         es = [.WEread wakExcl la 8] ∨
         es = [.WEread wakPlain a2 8, .WEread wakPlain a1 8, .WEread wakPlain la 8,
               .WEread wakExcl la 8])) ∨
    -- WRITE-BACK
    (∃ (lw' : BitVec 64) (wtr : Bool),
      update_PTE_Bits lw (.InstructionFetch ()) = some lw' ∧
      ∀ av dv : BitVec 1, pteAdLe (pteSetAD w0 av dv) lw →
        ∃ (sg' : ExecSt) (es : List Weff),
          execStale la 8 (pteSetAD w0 av dv) (translateAddr (.Virtaddr va) (.InstructionFetch ()))
              (wflatSt σ) =
            some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sg', es) ∧
          sg'.mem = bmWrite (wflatMem σ.wmImg σ.wmLog) la 8 lw' ∧
          sg'.dev = σ.wmDev ∧
          es = (if wtr then
                  [.WEread wakPlain a2 8, .WEread wakPlain a1 8, .WEread wakPlain la 8,
                   .WEread wakExcl la 8, .WEwrite wakExcl la 8 lw']
                else [.WEread wakExcl la 8, .WEwrite wakExcl la 8 lw']))) ∧
  -- THE SREGS FOOTPRINT of the member that ran
  (∀ (av dv : BitVec 1) (sg' : ExecSt) (es : List Weff),
    pteAdLe (pteSetAD w0 av dv) lw →
    execStale la 8 (pteSetAD w0 av dv) (translateAddr (.Virtaddr va) (.InstructionFetch ())) (wflatSt σ) =
      some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sg', es) →
    ∀ r : Register, r ≠ .tlb → sg'.regs r = σ.wmRegs r)

/-- Lean-only: the `fetch_bytes va va 4` peel, from the translation's peel and the tail. -/
theorem WkFetchPeel.fetchBytesPeel (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (σ : Wmstate) (va pa : BitVec 64) :
    wstepOkRacy tid ra rn rak Φ wDAny True true (translateAddr (.Virtaddr va) (.InstructionFetch ())) σ →
    wfetchTail tid σ va pa →
    wstepOkRacy tid ra rn rak Φ wDAny True true (fetch_bytes va va 4) σ := by
  intro hwalk htail
  rw [← wstepOkRacyKTriv]
  unfold fetch_bytes ext_fetch_check_pc
  simp only [SailME.run, PreSail.PreSailME.run, WkFetchPeel.wstepOkRacyKBindEq, ExceptT.run_bind,
    WkFetchPeel.runLiftM]
  -- THE SEAM
  refine wstepOkRacyKOfRun _ _ _ _ _ _ _ _ _ _ _ hwalk ?_
  intro x s' hrun b'
  obtain ⟨rfl, hmr⟩ := htail x s' hrun
  simp only [WkFetchPeel.wstepOkRacyKBindEq, WkFetchPeel.wstepOkRacyKPure, ExceptT.run_pure]
  -- the tail's ORDINARY certificate, embedded and phase-lifted
  refine wstepOkRacyKOfRun _ _ _ _ _ _ _ _ _ _ _ (wstepOkRacyAnyOfWstepOk _ _ _ _ _ _ _ _ hmr) ?_
  intro y s'' _ b''
  rcases y with bytes | ⟨exc, e⟩
  · simp only [WkFetchPeel.wstepOkRacyKPure, ExceptT.run_pure]
  · simp only [WkFetchPeel.wstepOkRacyKBindEq, ExceptT.run_bind, WkFetchPeel.wstepOkRacyKPure,
      ExceptT.run_pure, WkFetchPeel.runLiftM, assert, PreSail.assert]
    split
    · simp only [WkFetchPeel.wstepOkRacyKPure]
    · exact True.intro

/-- Lean-only: the 4-aligned fetch's register-only prefix, around the `fetch_bytes` peel. -/
theorem WkFetchPeel.fetchPeelOfBytes (tid : Option Nat) (ra : PAddr) (rn : Nat) (rak : AkInfo)
    (Φ : (Nat → BitVec 8) → Prop) (σ : Wmstate) (va : BitVec 64) :
    σ.wmRegs .PC = va → is_aligned_vaddr (.Virtaddr va) 4 = true →
    wstepOkRacy tid ra rn rak Φ wDAny True true (fetch_bytes va va 4) σ →
    wstepOkRacy tid ra rn rak Φ wDAny True true (fetch ()) σ := by
  intro hpc hal hfb
  rw [← wstepOkRacyKTriv]
  unfold fetch ext_fetch_check_pc get_config_rvfi
  simp only [SailME.run, PreSail.PreSailME.run, WkFetchPeel.wstepOkRacyKBindEq, ExceptT.run_bind,
    ExceptT.run_pure, WkFetchPeel.runLiftM, WkFetchPeel.wstepOkRacyKPure,
    readReg, PreSail.readReg, PreSail.emit, wstepOkRacyK, hpc, bit0ClearOfAligned4 va hal,
    bit1ClearOfAligned4 va hal, hal, Bool.false_eq_true, ↓reduceIte]
  apply wstepOkRacyKCurrentlyEnabledZiccif
  simp only [WkFetchPeel.wstepOkRacyKBindEq, ExceptT.run_bind, WkFetchPeel.runLiftM,
    WkFetchPeel.wstepOkRacyKPure, wstepOkRacyK, hpc, ↓reduceIte]
  refine wstepOkRacyKOfRun _ _ _ _ _ _ _ _ _ _ _ hfb ?_
  intro r s' _ b'
  rcases r with e | e | bytes
  all_goals simp only [WkFetchPeel.wstepOkRacyKBindEq, ExceptT.run_bind,
    ExceptT.run_pure, WkFetchPeel.runLiftM, WkFetchPeel.wstepOkRacyKPure, wstepOkRacyK]
  split <;> simp only [ExceptT.run_pure, WkFetchPeel.wstepOkRacyKPure]

/-- Rocq `wfetch_peel_of_exports`: the peel of the WHOLE `fetch ()` at the PC page's leaf
window, plus `wwalkPeelOfExports`' own filter side condition. -/
theorem wfetchPeelOfExports (tid : Option Nat) (σ : Wmstate) (root : BitVec 44) (va pa p2 p1 w0 lw : BitVec 64) :
    let vpn := WeakKpt.svpnOf va
    let la := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)
    σ.wmRegs .PC = va →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    wwalkExports tid σ root va pa p2 p1 w0 lw →
    wfetchTail tid σ va pa →
    wstepOkRacy tid la 8 wakPlain (wwalkFilter w0 lw) wDAny True true (fetch ()) σ ∧
    wadmFilter σ wakPlain la 8 (wwalkFilter w0 lw) := by
  intro vpn la hpc hal hexp htail
  unfold wwalkExports at hexp
  obtain ⟨hvar, hwf, hs2, hs1, hs0, hpin, hd2, hd1, hcoll, harm, -⟩ := hexp
  obtain ⟨hwalk, hfilt⟩ := wwalkPeelOfExports (.InstructionFetch ()) tid σ root va pa p2 p1 w0 lw hvar hwf
    hs2 hs1 hs0 hpin hd2 hd1 hcoll harm
  exact ⟨WkFetchPeel.fetchPeelOfBytes tid _ 8 wakPlain _ σ va hpc hal
    (WkFetchPeel.fetchBytesPeel tid _ 8 wakPlain _ σ va pa hwalk htail), hfilt⟩

/-- Rocq `wfetch_peel_k`: the CPS form. -/
theorem wfetchPeelK (tid : Option Nat) (σ : Wmstate) (root : BitVec 44) (va pa p2 p1 w0 lw : BitVec 64)
    (K : FetchResult → Wmstate → Bool → Prop) :
    let vpn := WeakKpt.svpnOf va
    let la := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)
    σ.wmRegs .PC = va →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    wwalkExports tid σ root va pa p2 p1 w0 lw →
    wfetchTail tid σ va pa →
    (∀ (r : FetchResult) (s' : Wmstate), wrun tid (fetch ()) σ r s' → ∀ b' : Bool, K r s' b') →
    wstepOkRacyK tid la 8 wakPlain (wwalkFilter w0 lw) wDAny True true (fetch ()) σ K ∧
    wadmFilter σ wakPlain la 8 (wwalkFilter w0 lw) := by
  intro vpn la hpc hal hexp htail hK
  obtain ⟨hpeel, hfilt⟩ := wfetchPeelOfExports tid σ root va pa p2 p1 w0 lw hpc hal hexp htail
  exact ⟨wstepOkRacyKOfRun _ _ _ _ _ _ _ _ _ _ _ hpeel hK, hfilt⟩

/-! ## 4. THE TAIL, DISCHARGED FROM THE WALK EXPORTS -/

/-- Rocq `pinned_read_ts_mono`. -/
theorem pinnedReadTsMono (s s' : Wmstate) (a : Int) :
    latestTs s'.wmLog a = latestTs s.wmLog a → wsLe s.wmWs s'.wmWs → pinnedRead s a → pinnedRead s' a := by
  intro hts hle hp
  unfold pinnedRead at hp ⊢
  rw [hts]
  have h1 := hle.1 a
  have h2 := hle.2.2.2.1
  omega

/-- Lean-only (O2): the FETCH pin transports along a run that misses the byte. -/
theorem WkFetchPeel.fetchPinnedTsMono (s s' : Wmstate) (a : Int) :
    latestTs s'.wmLog a = latestTs s.wmLog a → s.wmItv ≤ s'.wmItv → fetchPinned s a → fetchPinned s' a := by
  intro hts hle hp
  unfold fetchPinned at hp ⊢
  rw [hts]
  omega

/-- Rocq `wwalk_filter_inv`. -/
theorem wwalkFilterInv (w0 lw : BitVec 64) (u : BitVec (8 * 8)) :
    wwalkFilter w0 lw (fun j : Nat => nthByte u j) →
    ∃ av dv : BitVec 1, u = pteSetAD w0 av dv ∧ pteAdLe (pteSetAD w0 av dv) lw := by
  rintro ⟨wv, hbs, ⟨av, dv, hwv⟩, hle⟩
  have hweq : u = wv := bvEqOfBytes (n := 8) u wv (fun j _ => congrFun hbs j)
  refine ⟨av, dv, hweq.trans hwv, ?_⟩
  rw [← hwv]
  exact hle

/-- Rocq `wtrace_wonly_of_evs`. -/
theorem wtraceWonlyOfEvs (a2 a1 la : PAddr) (es : List Weff) (a : PAddr) :
    (∀ e, e ∈ es → wwalkEvOk a2 a1 la e) →
    (∀ j : Nat, j < 8 → la + BitVec.ofNat 64 j ≠ a) →
    wtraceWonly (fun (pa : PAddr) (n : Nat) => ∀ j : Nat, j < n → pa + BitVec.ofNat 64 j ≠ a) es := by
  intro hall hoff ak pa n v hin j hj
  obtain ⟨rfl, rfl⟩ := hall _ hin
  exact hoff j hj

/-- Rocq `wwalk_run_outcome`: THE OUTCOME OF THE WEAK TRANSLATION RUN. -/
theorem wwalkRunOutcome (tid : Option Nat) (σ : Wmstate) (root : BitVec 44) (va pa p2 p1 w0 lw : BitVec 64) :
    let vpn := WeakKpt.svpnOf va
    let la := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)
    wwalkExports tid σ root va pa p2 p1 w0 lw →
    ∀ x s', wrun tid (translateAddr (.Virtaddr va) (.InstructionFetch ())) σ x s' →
      x = .Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw) ∧
      wlogWf s'.wmLog ∧
      wsLe σ.wmWs s'.wmWs ∧
      s'.wmDev = σ.wmDev ∧
      (∀ a : PAddr, (∀ j : Nat, j < 8 → la + BitVec.ofNat 64 j ≠ a) →
        latestTs s'.wmLog (paZ a) = latestTs σ.wmLog (paZ a)) ∧
      (∀ a : PAddr, (∀ j : Nat, j < 8 → la + BitVec.ofNat 64 j ≠ a) →
        wflatMem s'.wmImg s'.wmLog a = wflatMem σ.wmImg σ.wmLog a) ∧
      (∀ r : Register, r ≠ .tlb → s'.wmRegs r = σ.wmRegs r) := by
  intro vpn la hexp x s' hrun
  unfold wwalkExports at hexp
  obtain ⟨hvar, hwf, hs2, hs1, hs0, hpin, hd2, hd1, hcoll, harm, hregs⟩ := hexp
  have hwf0 := ptSlotMemAccWf _ _ _ hs0
  obtain ⟨hpeel, hfilt⟩ := wwalkPeelOfExports (.InstructionFetch ()) tid σ root va pa p2 p1 w0 lw hvar hwf
    hs2 hs1 hs0 hpin hd2 hd1 hcoll harm
  have hrd : (bmRead (wflatMem σ.wmImg σ.wmLog) la 8).isSome = true := by
    rw [bmRead_of_bytes (wflatMem σ.wmImg σ.wmLog) la 8 lw hs0.1]; rfl
  -- ---- the member the run landed on, and everything it says ----
  have hcore : ∃ (sg' : ExecSt) (es : List Weff),
      x = .Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw) ∧
      wflatSt s' = sg' ∧
      sg'.dev = σ.wmDev ∧
      (sg'.mem = wflatMem σ.wmImg σ.wmLog ∨
        ∃ lw' : BitVec 64, sg'.mem = bmWrite (wflatMem σ.wmImg σ.wmLog) la 8 lw') ∧
      wlogWf s'.wmLog ∧
      (∀ e, e ∈ es → wwalkEvOk (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))
        (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) la e) ∧
      (∀ a : PAddr,
        wtraceWonly (fun (pa0 : PAddr) (n : Nat) => ∀ j : Nat, j < n → pa0 + BitVec.ofNat 64 j ≠ a) es →
        latestTs s'.wmLog (paZ a) = latestTs σ.wmLog (paZ a)) ∧
      (∀ r : Register, r ≠ .tlb → sg'.regs r = σ.wmRegs r) := by
    rcases harm with hro | ⟨lw', wtr, -, hfam⟩
    · -- ---------- READ-ONLY: four stale-friendly shapes ----------
      have hst : ∀ u : BitVec (8 * 8), wwalkFilter w0 lw (fun j : Nat => nthByte u j) →
          ∃ (y : Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit)) (t' : ExecSt)
            (es : List Weff),
            execStale la 8 u (translateAddr (.Virtaddr va) (.InstructionFetch ())) (wflatSt σ) =
              some (y, t', es) ∧ traceStale wakPlain la 8 es := by
        intro u hu
        obtain ⟨av, dv, rfl, hle⟩ := wwalkFilterInv w0 lw u hu
        obtain ⟨sgm, esm, hex, -, -, hes⟩ := hro av dv hle
        refine ⟨_, sgm, esm, hex, traceStaleWalkShapes _ _ la lw esm hd2 hd1 ?_⟩
        rcases hes with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      obtain ⟨u, es, -, hΦu, hexu, hwf', hlt⟩ := wrunExecStaleElim tid la 8 wakPlain (wwalkFilter w0 lw) True
        _ hwf0 (by decide) rfl σ hpeel hwf hfilt hrd hst x s' hrun
      obtain ⟨av, dv, rfl, hle⟩ := wwalkFilterInv w0 lw u hΦu
      obtain ⟨sgm, esm, hex, hmem, hmdev, hes⟩ := hro av dv hle
      rw [hex] at hexu
      simp only [Option.some.injEq, Prod.mk.injEq] at hexu
      obtain ⟨hx, hst', hes'⟩ := hexu
      refine ⟨sgm, es, hx.symm, hst'.symm, hmdev, Or.inl hmem, hwf', ?_, hlt, hregs av dv sgm esm hle hex⟩
      rw [← hes']
      rcases hes with rfl | rfl | rfl | rfl <;> (try simp only [la, vpn]) <;> wwalk_evs
    · cases wtr with
      | true =>
        -- ---------- MISS write-back: the five-event walk ----------
        have hst : ∀ u : BitVec (8 * 8), wwalkFilter w0 lw (fun j : Nat => nthByte u j) →
            ∃ (y : Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit)) (t' : ExecSt)
              (es : List Weff),
              execStale la 8 u (translateAddr (.Virtaddr va) (.InstructionFetch ())) (wflatSt σ) =
                some (y, t', es) ∧ traceStale wakPlain la 8 es := by
          intro u hu
          obtain ⟨av, dv, rfl, hle⟩ := wwalkFilterInv w0 lw u hu
          obtain ⟨sgm, esm, hex, -, -, hes⟩ := hfam av dv hle
          simp only [↓reduceIte] at hes
          exact ⟨_, sgm, esm, hex, traceStaleWalkShapes _ _ la lw' esm hd2 hd1
            (Or.inr (Or.inr (Or.inr (Or.inr hes))))⟩
        obtain ⟨u, es, -, hΦu, hexu, hwf', hlt⟩ := wrunExecStaleElim tid la 8 wakPlain (wwalkFilter w0 lw)
          True _ hwf0 (by decide) rfl σ hpeel hwf hfilt hrd hst x s' hrun
        obtain ⟨av, dv, rfl, hle⟩ := wwalkFilterInv w0 lw u hΦu
        obtain ⟨sgm, esm, hex, hmem, hmdev, hes⟩ := hfam av dv hle
        rw [hex] at hexu
        simp only [Option.some.injEq, Prod.mk.injEq] at hexu
        obtain ⟨hx, hst', hes'⟩ := hexu
        refine ⟨sgm, es, hx.symm, hst'.symm, hmdev, Or.inr ⟨lw', hmem⟩, hwf', ?_, hlt,
          hregs av dv sgm esm hle hex⟩
        rw [← hes', hes]
        try simp only [la, vpn]
        wwalk_evs
      | false =>
        -- ---------- HIT write-back: the CONSTANT family ----------
        have hst : ∀ u : BitVec (8 * 8), wwalkFilter w0 lw (fun j : Nat => nthByte u j) →
            ∃ (y : Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit)) (t' : ExecSt)
              (es : List Weff),
              execStale la 8 u (translateAddr (.Virtaddr va) (.InstructionFetch ())) (wflatSt σ) =
                some (y, t', es) ∧ traceOffWin la 8 es := by
          intro u hu
          obtain ⟨av, dv, rfl, hle⟩ := wwalkFilterInv w0 lw u hu
          obtain ⟨sgm, esm, hex, -, -, hes⟩ := hfam av dv hle
          simp only [Bool.false_eq_true, ↓reduceIte] at hes
          refine ⟨_, sgm, esm, hex, ?_⟩
          rw [hes]
          exact traceOffWinPinned _ _ _ (by walk_stale_trace)
        obtain ⟨u, es, -, hΦu, hexu, hwf', hlt⟩ := wrunExecStaleElimConst tid la 8 wakPlain
          (wwalkFilter w0 lw) True true _ hwf0 (by decide) rfl σ hpeel hwf hfilt hrd hst x s' hrun
        obtain ⟨av, dv, rfl, hle⟩ := wwalkFilterInv w0 lw u hΦu
        obtain ⟨sgm, esm, hex, hmem, hmdev, hes⟩ := hfam av dv hle
        rw [hex] at hexu
        simp only [Option.some.injEq, Prod.mk.injEq] at hexu
        obtain ⟨hx, hst', hes'⟩ := hexu
        refine ⟨sgm, es, hx.symm, hst'.symm, hmdev, Or.inr ⟨lw', hmem⟩, hwf', ?_, hlt,
          hregs av dv sgm esm hle hex⟩
        rw [← hes', hes]
        try simp only [la, vpn]
        wwalk_evs
  -- ---- and now the post-state facts the fetch's tail needs ----
  obtain ⟨sgm, es, hx, hsg, hmdev, hmem, hwf', hev, hlt, hrg⟩ := hcore
  refine ⟨hx, hwf', wrunWsLe tid _ σ x s' hrun, ?_, fun a hoff => hlt a (wtraceWonlyOfEvs _ _ la es a hev hoff),
    ?_, ?_⟩
  · rw [← wflatStDev s', hsg]; exact hmdev
  · intro a hoff
    rw [← wflatStMem s', hsg]
    rcases hmem with hmem | ⟨lw', hmem⟩
    · rw [hmem]
    · rw [hmem]
      exact writeBytesLookupNe _ _ _ _ _ (fun j hj heq => hoff j hj heq.symm)
  · intro r hr
    rw [← wflatStRegs s', hsg]
    exact hrg r hr

/-- Rocq `wfetch_gates`: the fetch's REGISTER-ONLY gates, at the post-translation states. -/
def wfetchGates (tid : Option Nat) (σ : Wmstate) (va pa : BitVec 64) (region : PMA_Region) : Prop :=
  ∀ x s', wrun tid (translateAddr (.Virtaddr va) (.InstructionFetch ())) σ x s' →
    (∀ mm : BMap,
      execEff (pmpCheck (.Physaddr pa) 4 (.InstructionFetch ()) .Supervisor) ⟨s'.wmRegs, mm, s'.wmDev⟩ =
        some (none, ⟨s'.wmRegs, mm, s'.wmDev⟩, []) ∧
      matching_pma_region (s'.wmRegs .pma_regions) (.Physaddr pa) 4 = some region ∧
      execEff (within_clint (.Physaddr pa) 4) ⟨s'.wmRegs, mm, s'.wmDev⟩ =
        some (false, ⟨s'.wmRegs, mm, s'.wmDev⟩, []) ∧
      execEff (within_sig (.Physaddr pa) 4) ⟨s'.wmRegs, mm, s'.wmDev⟩ =
        some (false, ⟨s'.wmRegs, mm, s'.wmDev⟩, []) ∧
      execEff (within_htif_readable (.Physaddr pa) 4) ⟨s'.wmRegs, mm, s'.wmDev⟩ =
        some (false, ⟨s'.wmRegs, mm, s'.wmDev⟩, [])) ∧
    s'.wmRegs .cur_privilege = .Supervisor

/-- Rocq `wfetch_tail_of_exports` (deviation 5: the text pins are FETCH pins). -/
theorem wfetchTailOfExports (tid : Option Nat) (σ : Wmstate) (root : BitVec 44) (va pa p2 p1 w0 lw : BitVec 64)
    (region : PMA_Region) (w : BitVec 32) :
    let vpn := WeakKpt.svpnOf va
    let la := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)
    wwalkExports tid σ root va pa p2 p1 w0 lw →
    raccDisj la 8 pa 4 →
    accWf pa 4 →
    (∀ j : Nat, j < 4 → paZ (pa + BitVec.ofNat 64 j) ≠ 0) →
    (∀ j : Nat, j < 4 → fetchPinned σ (WeakInterp.accAddr pa j)) →
    (∀ j : Nat, j < 4 → wflatMem σ.wmImg σ.wmLog (pa + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    wfetchGates tid σ va pa region →
    is_aligned_paddr (.Physaddr pa) 4 = true →
    (override_PMA region.attributes .PBMT_PMA).executable = true →
    devAddr pa = false →
    wfetchTail tid σ va pa := by
  intro vpn la hexp hdisj haccp hW0 hpin hbytes hgates halign hexecp hdev
  have hs0 : WeakWalkEff.ptSlotMem (wflatSt σ) la lw := by
    unfold wwalkExports at hexp
    exact hexp.2.2.2.2.1
  have hwf0 := ptSlotMemAccWf _ _ _ hs0
  -- the leaf window and the text window are byte-wise apart
  have hne : ∀ i j : Nat, i < 8 → j < 4 → la + BitVec.ofNat 64 i ≠ pa + BitVec.ofNat 64 j :=
    fun i j hi hj heq => paAddNeq pa la 4 8 j i haccp hwf0 hdisj hj hi heq.symm
  intro x s' hrun
  obtain ⟨hx, hwf', -, -, hlt, hmem, -⟩ := wwalkRunOutcome tid σ root va pa p2 p1 w0 lw hexp x s' hrun
  obtain ⟨hg, hpriv⟩ := hgates x s' hrun
  refine ⟨hx, wfetchTailRead tid s' pa region w hwf' haccp hW0 ?_ ?_ hg halign hexecp hdev hpriv⟩
  · -- the four text bytes are still FETCH-PINNED at `s'`
    intro j hj
    refine WkFetchPeel.fetchPinnedTsMono σ s' _ ?_ (wrunItvLe tid _ σ x s' hrun) (hpin j hj)
    rw [← accWfByte pa 4 j haccp hj]
    exact hlt _ (fun i hi => hne i j hi hj)
  · -- ... and still hold `w`
    intro j hj
    rw [hmem _ (fun i hi => hne i j hi hj)]
    exact hbytes j hj

/-- Rocq `wfetch_peel_selfcontained`: the fetch peel from the exports, the text pins and the
gates. -/
theorem wfetchPeelSelfcontained (tid : Option Nat) (σ : Wmstate) (root : BitVec 44)
    (va pa p2 p1 w0 lw : BitVec 64) (region : PMA_Region) (w : BitVec 32) :
    let vpn := WeakKpt.svpnOf va
    let la := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)
    σ.wmRegs .PC = va →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    wwalkExports tid σ root va pa p2 p1 w0 lw →
    raccDisj la 8 pa 4 →
    accWf pa 4 →
    (∀ j : Nat, j < 4 → paZ (pa + BitVec.ofNat 64 j) ≠ 0) →
    (∀ j : Nat, j < 4 → fetchPinned σ (WeakInterp.accAddr pa j)) →
    (∀ j : Nat, j < 4 → wflatMem σ.wmImg σ.wmLog (pa + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    wfetchGates tid σ va pa region →
    is_aligned_paddr (.Physaddr pa) 4 = true →
    (override_PMA region.attributes .PBMT_PMA).executable = true →
    devAddr pa = false →
    wstepOkRacy tid la 8 wakPlain (wwalkFilter w0 lw) wDAny True true (fetch ()) σ ∧
    wadmFilter σ wakPlain la 8 (wwalkFilter w0 lw) := by
  intro vpn la hpc hal hexp hdisj haccp hW0 hpin hbytes hgates halign hexecp hdev
  exact wfetchPeelOfExports tid σ root va pa p2 p1 w0 lw hpc hal hexp
    (wfetchTailOfExports tid σ root va pa p2 p1 w0 lw region w hexp hdisj haccp hW0 hpin hbytes hgates
      halign hexecp hdev)

/-- Rocq `wfetch_peel_k_selfcontained`: the CPS form, likewise self-contained. -/
theorem wfetchPeelKSelfcontained (tid : Option Nat) (σ : Wmstate) (root : BitVec 44)
    (va pa p2 p1 w0 lw : BitVec 64) (region : PMA_Region) (w : BitVec 32)
    (K : FetchResult → Wmstate → Bool → Prop) :
    let vpn := WeakKpt.svpnOf va
    let la := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)
    σ.wmRegs .PC = va →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    wwalkExports tid σ root va pa p2 p1 w0 lw →
    raccDisj la 8 pa 4 →
    accWf pa 4 →
    (∀ j : Nat, j < 4 → paZ (pa + BitVec.ofNat 64 j) ≠ 0) →
    (∀ j : Nat, j < 4 → fetchPinned σ (WeakInterp.accAddr pa j)) →
    (∀ j : Nat, j < 4 → wflatMem σ.wmImg σ.wmLog (pa + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    wfetchGates tid σ va pa region →
    is_aligned_paddr (.Physaddr pa) 4 = true →
    (override_PMA region.attributes .PBMT_PMA).executable = true →
    devAddr pa = false →
    (∀ (r : FetchResult) (s' : Wmstate), wrun tid (fetch ()) σ r s' → ∀ b' : Bool, K r s' b') →
    wstepOkRacyK tid la 8 wakPlain (wwalkFilter w0 lw) wDAny True true (fetch ()) σ K ∧
    wadmFilter σ wakPlain la 8 (wwalkFilter w0 lw) := by
  intro vpn la hpc hal hexp hdisj haccp hW0 hpin hbytes hgates halign hexecp hdev hK
  exact wfetchPeelK tid σ root va pa p2 p1 w0 lw K hpc hal hexp
    (wfetchTailOfExports tid σ root va pa p2 p1 w0 lw region w hexp hdisj haccp hW0 hpin hbytes hgates
      halign hexecp hdev) hK

/-! ## 5. THE GATES, FROM σ's REGISTERS -/

/-- Rocq `exec_eff_pmpCheck_supervisor_grant_fetch`: `execEffPmpCheckSupervisorGrantLoad`'s
script at `InstructionFetch ()` (the `X` bit for the `R` bit). -/
theorem execEffPmpCheckSupervisorGrantFetch (a : BitVec 64) (width : Nat) (s : ExecSt)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) a.toNat
      (to_bits (l := 64) width).toNat = .PMP_Match)
    (hX : (_get_Pmpcfg_ent_X (s.regs .pmpcfg_n)[0]! == 1#1) = true) :
    execEff (pmpCheck (.Physaddr a) width (.InstructionFetch ()) .Supervisor) s = some (none, s, []) := by
  have hA' : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[(0 : Int)]!) =
      .TOR := hA
  have hm := execEffPmpMatchAddrTORMatch a (to_bits (l := 64) width) _ (s.regs .pmpaddr_n)[0]!
    (zeros (n := 64)) s hA' hlt hr
  have hrd : execEff (pmpReadAddrReg (0 : Int).toNat) s = some ((s.regs .pmpaddr_n)[0]!, s, []) :=
    execEffPmpReadAddrReg 0 s
  have hrwx : execEff (pmpCheckRWX (s.regs .pmpcfg_n)[(0 : Int)]! (.InstructionFetch ())) s =
      some (true, s, []) := by
    unfold pmpCheckRWX
    have hX' : (_get_Pmpcfg_ent_X (s.regs .pmpcfg_n)[(0 : Int)]! == 1#1) = true := hX
    rw [hX']; rfl
  unfold pmpCheck
  rw [execEffCatchEarlyReturn]
  have hc : (sys_pmp_count == 0) = false := by decide
  simp only [hc, Bool.false_eq_true, ↓reduceIte]
  rw [execREffBindEq, WeakWalkEff.execREffForInFirstEarly _ _ s s none [] (by decide)]
  dsimp only
  rw [if_neg (by decide)]
  rw [execREffBindNil _ _ _ _ _ (wpeExecREffReturnmFwd _ s),
    execREffLiftRSeq _ _ _ _ _ (execEffReadReg .pmpcfg_n s),
    execREffBindNil _ _ _ _ _ (wpeExecREffReturnmFwd _ s),
    execREffLiftRSeq _ _ _ _ _ hrd, execREffLiftRSeq _ _ _ _ _ hm]
  dsimp only
  rw [execREffLiftRSeq _ _ _ _ _ hrwx]
  rfl

/-- Rocq `wfetch_region_of_regs` (deviation 7): the text word's region, from the PMA table
alone. -/
theorem wfetchRegionOfRegs (pa : BitVec 64) (regions : List PMA_Region) :
    inRam pa 4 →
    regions = bootPMA →
    ∃ region : PMA_Region,
      matching_pma_region regions (.Physaddr pa) 4 = some region ∧
      (override_PMA region.attributes .PBMT_PMA).executable = true := by
  intro hram hpma
  subst hpma
  exact ⟨ramRegion, matching_pma_ram pa 4 hram (by decide) (by decide), ramRegionExec⟩

/-- Rocq `wfetch_gates_of_region` (deviation 7): the gates at a given region. -/
theorem wfetchGatesOfRegion (tid : Option Nat) (σ : Wmstate) (root : BitVec 44) (va pa p2 p1 w0 lw : BitVec 64)
    (region : PMA_Region) :
    wwalkExports tid σ root va pa p2 p1 w0 lw →
    inRam pa 4 →
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (σ.wmRegs .pmpcfg_n)[0]!) = .TOR →
    zopz0zKzJ_u (zeros (n := 64)) (σ.wmRegs .pmpaddr_n)[0]! = false →
    (_get_Pmpcfg_ent_X (σ.wmRegs .pmpcfg_n)[0]! == 1#1) = true →
    ramEnd ≤ (σ.wmRegs .pmpaddr_n)[0]!.toNat * 4 →
    matching_pma_region (σ.wmRegs .pma_regions) (.Physaddr pa) 4 = some region →
    σ.wmRegs .htif_tohost_base = none →
    σ.wmRegs .cur_privilege = .Supervisor →
    wfetchGates tid σ va pa region := by
  intro hexp hram hA hlt hX hcov hmatch hhtif hpriv
  have hz : (zeros (n := 64)).toNat = 0 := rfl
  have h4 : (to_bits (l := 64) 4).toNat = 4 := by decide
  intro x s' hrun
  obtain ⟨-, -, -, -, -, -, hpres⟩ := wwalkRunOutcome tid σ root va pa p2 p1 w0 lw hexp x s' hrun
  have hpmpc : s'.wmRegs .pmpcfg_n = σ.wmRegs .pmpcfg_n := hpres _ (by decide)
  have hpmpa : s'.wmRegs .pmpaddr_n = σ.wmRegs .pmpaddr_n := hpres _ (by decide)
  have hpmar : s'.wmRegs .pma_regions = σ.wmRegs .pma_regions := hpres _ (by decide)
  have hhtif' : s'.wmRegs .htif_tohost_base = none := by rw [hpres _ (by decide)]; exact hhtif
  have hpriv' : s'.wmRegs .cur_privilege = .Supervisor := by rw [hpres _ (by decide)]; exact hpriv
  refine ⟨fun mm => ⟨?_, ?_, ?_, ?_, ?_⟩, hpriv'⟩
  · apply execEffPmpCheckSupervisorGrantFetch
    · show pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s'.wmRegs .pmpcfg_n)[0]!) = .TOR
      rw [hpmpc]; exact hA
    · show zopz0zKzJ_u (zeros (n := 64)) (s'.wmRegs .pmpaddr_n)[0]! = false
      rw [hpmpa]; exact hlt
    · show pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s'.wmRegs .pmpaddr_n)[0]!.toNat * 4) pa.toNat
        (to_bits (l := 64) 4).toNat = .PMP_Match
      rw [hpmpa, hz, h4]
      exact pmpRangeMatch_full _ _ _ _ (Nat.zero_le _) (by decide) (by have := hram.2; omega)
    · show (_get_Pmpcfg_ent_X (s'.wmRegs .pmpcfg_n)[0]! == 1#1) = true
      rw [hpmpc]; exact hX
  · rw [hpmar]; exact hmatch
  · rw [within_clint_ram pa 4 hram]; rfl
  · first
    | rfl
    | (simp only [within_sig, plat_have_sig, Functions.not]; rfl)
  · exact execEffWithinHtifFalse _ 4 _ hhtif'

/-- Rocq `wfetch_gates_of_regs`: the gates, region and all, from σ's registers. -/
theorem wfetchGatesOfRegs (tid : Option Nat) (σ : Wmstate) (root : BitVec 44) (va pa p2 p1 w0 lw : BitVec 64) :
    wwalkExports tid σ root va pa p2 p1 w0 lw →
    inRam pa 4 →
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (σ.wmRegs .pmpcfg_n)[0]!) = .TOR →
    zopz0zKzJ_u (zeros (n := 64)) (σ.wmRegs .pmpaddr_n)[0]! = false →
    (_get_Pmpcfg_ent_X (σ.wmRegs .pmpcfg_n)[0]! == 1#1) = true →
    ramEnd ≤ (σ.wmRegs .pmpaddr_n)[0]!.toNat * 4 →
    σ.wmRegs .pma_regions = bootPMA →
    σ.wmRegs .htif_tohost_base = none →
    σ.wmRegs .cur_privilege = .Supervisor →
    ∃ region : PMA_Region,
      wfetchGates tid σ va pa region ∧
      (override_PMA region.attributes .PBMT_PMA).executable = true := by
  intro hexp hram hA hlt hX hcov hall hhtif hpriv
  obtain ⟨region, hmatch, hexec⟩ := wfetchRegionOfRegs pa _ hram hall
  exact ⟨region, wfetchGatesOfRegion tid σ root va pa p2 p1 w0 lw region hexp hram hA hlt hX hcov hmatch
    hhtif hpriv, hexec⟩

/-- Rocq `wfetch_peel_of_regs`: THE CAPSTONE, FROM σ's REGISTERS. -/
theorem wfetchPeelOfRegs (tid : Option Nat) (σ : Wmstate) (root : BitVec 44) (va pa p2 p1 w0 lw : BitVec 64)
    (w : BitVec 32) :
    let vpn := WeakKpt.svpnOf va
    let la := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)
    σ.wmRegs .PC = va →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    wwalkExports tid σ root va pa p2 p1 w0 lw →
    is_aligned_paddr (.Physaddr pa) 4 = true →
    inRam pa 4 →
    accWf pa 4 →
    (∀ j : Nat, j < 4 → paZ (pa + BitVec.ofNat 64 j) ≠ 0) →
    (∀ j : Nat, j < 4 → fetchPinned σ (WeakInterp.accAddr pa j)) →
    (∀ j : Nat, j < 4 → wflatMem σ.wmImg σ.wmLog (pa + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (σ.wmRegs .pmpcfg_n)[0]!) = .TOR →
    zopz0zKzJ_u (zeros (n := 64)) (σ.wmRegs .pmpaddr_n)[0]! = false →
    (_get_Pmpcfg_ent_X (σ.wmRegs .pmpcfg_n)[0]! == 1#1) = true →
    ramEnd ≤ (σ.wmRegs .pmpaddr_n)[0]!.toNat * 4 →
    σ.wmRegs .pma_regions = bootPMA →
    σ.wmRegs .htif_tohost_base = none →
    σ.wmRegs .cur_privilege = .Supervisor →
    raccDisj la 8 pa 4 →
    wstepOkRacy tid la 8 wakPlain (wwalkFilter w0 lw) wDAny True true (fetch ()) σ ∧
    wadmFilter σ wakPlain la 8 (wwalkFilter w0 lw) := by
  intro vpn la hpc halv hexp halign hram haccp hW0 hpin hbytes hA hlt hX hcov hall hhtif hpriv hdisj
  obtain ⟨region, hgates, hexec⟩ := wfetchGatesOfRegs tid σ root va pa p2 p1 w0 lw hexp hram hA hlt hX hcov
    hall hhtif hpriv
  exact wfetchPeelSelfcontained tid σ root va pa p2 p1 w0 lw region w hpc halv hexp hdisj haccp hW0 hpin
    hbytes hgates halign hexec (devAddrRam pa 4 hram)

/-! ## 6. THE FUPD: the kernel page table's resources, turned into the fetch's bundles -/

section WkFetchFupd

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF] [WeakKpt.KptGS GF]

/-- Rocq `wkpt_fetch_peel_at` (deviations 7–8): `wtlbResPtTranslateAddrStaleAt` at
`acc := InstructionFetch ()`, re-emitted with the walk exports and the fetch's gates at the
post-`minstret_increment`-write states, and the region's `executable`. -/
theorem wkptFetchPeelAt (cpu : CPU) (root : BitVec 44) (T_kpt : Nat) (tid : Option Nat) (va pa : BitVec 64)
    (ppn : BitVec 44) (pc : KPerm) (σ : Wmstate) (E : CoPset) (w : BitVec 32) :
    (↑wkptN : CoPset) ⊆ E →
    (∀ (a d : BitVec 1) (mxr dosum : Bool),
      wpteCheckOk (.InstructionFetch ()) .Supervisor mxr dosum (pteSetAD (mkPte ppn pc.flags) a d)) →
    (∀ a d : BitVec 1, wpteValid (pteSetAD (mkPte ppn pc.flags) a d)) →
    (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false →
    zero_extend (m := 64) (ppn +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0) = pa →
    wlogWf σ.wmLog →
    σ.wmRegs .misa = misaC →
    σ.wmRegs .menvcfg = menvcfgS →
    σ.wmRegs .htif_tohost_base = none →
    σ.wmRegs .cur_privilege = .Supervisor →
    _get_Mstatus_SXL (σ.wmRegs .mstatus) = 2#2 →
    (∀ bf : Bool, execEff (effectivePrivilege (.InstructionFetch ()) (σ.wmRegs .mstatus) .Supervisor)
        ((wflatSt σ).setReg .minstret_increment bf) =
      some (.Supervisor, (wflatSt σ).setReg .minstret_increment bf, [])) →
    (∀ bf : Bool, execEff (is_shadow_stack_access (.InstructionFetch ()))
        ((wflatSt σ).setReg .minstret_increment bf) =
      some (false, (wflatSt σ).setReg .minstret_increment bf, [])) →
    σ.wmRegs .pma_regions = bootPMA →
    T_kpt ≤ σ.wmWs.wVrNew →
    -- the FETCH-side pure premises the absorption exports do not carry
    σ.wmRegs .PC = va →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    is_aligned_paddr (.Physaddr pa) 4 = true →
    inRam pa 4 →
    accWf pa 4 →
    (∀ j : Nat, j < 4 → paZ (pa + BitVec.ofNat 64 j) ≠ 0) →
    (∀ j : Nat, j < 4 → fetchPinned σ (WeakInterp.accAddr pa j)) →
    (∀ j : Nat, j < 4 →
      wflatMem σ.wmImg σ.wmLog (pa + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    -- the text fetch's PMP grant, at σ's registers
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (σ.wmRegs .pmpcfg_n)[0]!) = .TOR →
    zopz0zKzJ_u (zeros (n := 64)) (σ.wmRegs .pmpaddr_n)[0]! = false →
    (_get_Pmpcfg_ent_X (σ.wmRegs .pmpcfg_n)[0]! == 1#1) = true →
    ramEnd ≤ (σ.wmRegs .pmpaddr_n)[0]!.toNat * 4 →
    kmapAt (hlc := hlc) (WeakKpt.svpnOf va) (kLeaf ppn pc 0#1 0#1) ∗
      regInterp cpu σ.wmRegs ∗
      wlogAuth (GF := GF) σ.wmLog ∗
      wlatInterp (GF := GF) σ.wmImg σ.wmLog ∗
      wtlbResPt (hlc := hlc) (GF := GF) cpu root T_kpt ⊢
    |={E}=> ∃ (p2 p1 lw : BitVec 64) (region : PMA_Region),
      ⌜∃ a d : BitVec 1, lw = pteSetAD (mkPte ppn pc.flags) a d⌝ ∗
      ⌜WeakWalkEff.ptSlotMem (wflatSt σ)
          (uPteAddr root (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 26 18)) p2 ∧
        WeakWalkEff.ptSlotMem (wflatSt σ)
          (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 17 9)) p1 ∧
        WeakWalkEff.ptSlotMem (wflatSt σ)
          (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) lw⌝ ∗
      ⌜∀ j : Nat, j < 8 →
        pinnedRead σ (WeakInterp.accAddr
          (uPteAddr root (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 26 18)) j) ∧
        pinnedRead σ (WeakInterp.accAddr
          (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 17 9)) j)⌝ ∗
      ⌜raccDisj
          (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8
          (uPteAddr root (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 26 18)) 8 ∧
        raccDisj
          (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8
          (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 17 9)) 8⌝ ∗
      ⌜∀ (rak : AkInfo) (wv : BitVec (8 * 8)), rak.akIfetch = false →
        wadm σ rak
          (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8 wv →
        (∃ a d : BitVec 1, wv = pteSetAD (mkPte ppn pc.flags) a d) ∧ pteAdLe wv lw⌝ ∗
      ⌜∀ j : Nat, j < 8 → nvFree σ.wmLog (WeakInterp.accAddr
          (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) j)⌝ ∗
      -- the walk exports and the fetch's gates, at the post-flag-write states
      ⌜∀ bf : Bool, wwalkExports tid (wsetReg σ .minstret_increment bf) root va pa p2 p1 (mkPte ppn pc.flags) lw⌝ ∗
      ⌜∀ bf : Bool, wfetchGates tid (wsetReg σ .minstret_increment bf) va pa region⌝ ∗
      ⌜(override_PMA region.attributes .PBMT_PMA).executable = true⌝ ∗
      regInterp cpu σ.wmRegs ∗
      -- the REGISTER WAND, keyed on the member that ran and on the flag
      (∀ (bf : Bool) (av dv : BitVec 1) (sg' : ExecSt) (es : List Weff),
        ⌜pteAdLe (pteSetAD (mkPte ppn pc.flags) av dv) lw⌝ -∗
        ⌜execStale
            (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8
            (pteSetAD (mkPte ppn pc.flags) av dv) (translateAddr (.Virtaddr va) (.InstructionFetch ()))
            ((wflatSt σ).setReg .minstret_increment bf) =
          some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sg', es)⌝ -∗
        regInterp cpu (σ.wmRegs.set .minstret_increment bf) -∗
        |==> (regInterp cpu sg'.regs ∗ wtlbResPt (hlc := hlc) (GF := GF) cpu root T_kpt)) ∗
      ( -- READ-ONLY
        (⌜∀ av dv : BitVec 1, pteAdLe (pteSetAD (mkPte ppn pc.flags) av dv) lw → ∀ bf : Bool,
          ∃ (sg' : ExecSt) (es : List Weff),
            execStale
                (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8
                (pteSetAD (mkPte ppn pc.flags) av dv) (translateAddr (.Virtaddr va) (.InstructionFetch ()))
                ((wflatSt σ).setReg .minstret_increment bf) =
              some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sg', es) ∧
            sg'.mem = wflatMem σ.wmImg σ.wmLog ∧
            sg'.dev = σ.wmDev ∧
            (∀ r : Register, r ≠ .tlb →
              sg'.regs r = ((wflatSt σ).setReg .minstret_increment bf).regs r) ∧
            (es = [] ∨
             es = [.WEread wakPlain
                     (uPteAddr root (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 26 18)) 8,
                   .WEread wakPlain
                     (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 17 9)) 8,
                   .WEread wakPlain
                     (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8] ∨
             es = [.WEread ⟨false, true, false⟩
                     (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8] ∨
             es = [.WEread wakPlain
                     (uPteAddr root (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 26 18)) 8,
                   .WEread wakPlain
                     (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 17 9)) 8,
                   .WEread wakPlain
                     (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8,
                   .WEread ⟨false, true, false⟩
                     (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8])⌝ ∗
          wlogAuth (GF := GF) σ.wmLog ∗ wlatInterp (GF := GF) σ.wmImg σ.wmLog) ∨
        -- WRITE-BACK
        (∃ lw' : BitVec 64,
          ⌜update_PTE_Bits lw (.InstructionFetch ()) = some lw'⌝ ∗
          ⌜∃ wtr : Bool, ∀ av dv : BitVec 1, pteAdLe (pteSetAD (mkPte ppn pc.flags) av dv) lw → ∀ bf : Bool,
            ∃ (sg' : ExecSt) (es : List Weff),
              execStale
                  (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8
                  (pteSetAD (mkPte ppn pc.flags) av dv) (translateAddr (.Virtaddr va) (.InstructionFetch ()))
                  ((wflatSt σ).setReg .minstret_increment bf) =
                some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sg', es) ∧
              sg'.mem = bmWrite (wflatMem σ.wmImg σ.wmLog)
                  (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8 lw' ∧
              sg'.dev = σ.wmDev ∧
              (∀ r : Register, r ≠ .tlb →
                sg'.regs r = ((wflatSt σ).setReg .minstret_increment bf).regs r) ∧
              es = (if wtr then
                      [.WEread wakPlain
                         (uPteAddr root (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 26 18)) 8,
                       .WEread wakPlain
                         (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 17 9)) 8,
                       .WEread wakPlain
                         (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8,
                       .WEread ⟨false, true, false⟩
                         (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8,
                       .WEwrite ⟨false, true, false⟩
                         (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8 lw']
                    else
                      [.WEread ⟨false, true, false⟩
                         (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8,
                       .WEwrite ⟨false, true, false⟩
                         (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8 lw'])⌝ ∗
          wlogAuth (GF := GF) (σ.wmLog ++ [wwriteMsg tid .WCexcl
            (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8 lw']) ∗
          wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ [wwriteMsg tid .WCexcl
            (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8 lw']))) := by
  intro hE hchk hval hcanon hid4k hwlog hmisa hmenv hhtif hcp hsxl heff hss hpma hrcpt
    _hpcv _halv _halp hram _haccp _hnz _hpin _hbytes hA hlt hX hcov
  -- THE REGION IS σ-LEVEL, and so uniform in the flag
  obtain ⟨region, hmatch, hexecp⟩ := wfetchRegionOfRegs pa _ hram hpma
  have hregb : ∀ (bf : Bool) (r : Register), r ≠ .minstret_increment →
      (wsetReg σ .minstret_increment bf).wmRegs r = σ.wmRegs r :=
    fun bf r h => RegFile.set_other _ _ _ _ h
  have hAb : ∀ bf : Bool, pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A ((wsetReg σ .minstret_increment bf).wmRegs .pmpcfg_n)[0]!) = .TOR := by
    intro bf; rw [hregb bf _ (by decide)]; exact hA
  have hltb : ∀ bf : Bool,
      zopz0zKzJ_u (zeros (n := 64)) ((wsetReg σ .minstret_increment bf).wmRegs .pmpaddr_n)[0]! = false := by
    intro bf; rw [hregb bf _ (by decide)]; exact hlt
  have hXb : ∀ bf : Bool,
      (_get_Pmpcfg_ent_X ((wsetReg σ .minstret_increment bf).wmRegs .pmpcfg_n)[0]! == 1#1) = true := by
    intro bf; rw [hregb bf _ (by decide)]; exact hX
  have hcovb : ∀ bf : Bool, ramEnd ≤ ((wsetReg σ .minstret_increment bf).wmRegs .pmpaddr_n)[0]!.toNat * 4 := by
    intro bf; rw [hregb bf _ (by decide)]; exact hcov
  have hmatchb : ∀ bf : Bool, matching_pma_region ((wsetReg σ .minstret_increment bf).wmRegs .pma_regions)
      (.Physaddr pa) 4 = some region := by
    intro bf; rw [hregb bf _ (by decide)]; exact hmatch
  have hhtifb : ∀ bf : Bool, (wsetReg σ .minstret_increment bf).wmRegs .htif_tohost_base = none := by
    intro bf; rw [hregb bf _ (by decide)]; exact hhtif
  have hcpb : ∀ bf : Bool, (wsetReg σ .minstret_increment bf).wmRegs .cur_privilege = .Supervisor := by
    intro bf; rw [hregb bf _ (by decide)]; exact hcp
  iintro H
  imod (wtlbResPtTranslateAddrStaleAt (.InstructionFetch ()) cpu root T_kpt tid va pa ppn pc σ E hE hchk hval
    hcanon hid4k hwlog hmisa hmenv hhtif hcp hsxl heff hss hpma hrcpt) $$ H
    with ⟨%p2, %p1, %lw, %hvar, %hslots, %hpins, %hdj, %hcoll, %hnv, Hri, Hwand, Harm⟩
  obtain ⟨hs2, hs1, hs0⟩ := hslots
  obtain ⟨hd2, hd1⟩ := hdj
  have hgof : ∀ bf : Bool,
      wwalkExports tid (wsetReg σ .minstret_increment bf) root va pa p2 p1 (mkPte ppn pc.flags) lw →
      wfetchGates tid (wsetReg σ .minstret_increment bf) va pa region := fun bf hexpb =>
    wfetchGatesOfRegion tid _ root va pa p2 p1 _ lw region hexpb hram (hAb bf) (hltb bf) (hXb bf) (hcovb bf)
      (hmatchb bf) (hhtifb bf) (hcpb bf)
  icases Harm with (⟨%hro, Hlog, Hlat⟩ | ⟨%lw', %hupd, %hfam, Hlog, Hlat⟩)
  · have hexpb : ∀ bf : Bool, wwalkExports tid (wsetReg σ .minstret_increment bf) root va pa p2 p1 (mkPte ppn pc.flags) lw := by
      intro bf
      unfold wwalkExports
      refine ⟨hvar, hwlog, hs2, hs1, hs0, hpins, hd2, hd1, hcoll, Or.inl ?_, ?_⟩
      · intro av dv hle
        obtain ⟨sg', es, h1, h2, h3, -, h5⟩ := hro av dv hle bf
        exact ⟨sg', es, h1, h2, h3, h5⟩
      · intro av dv sg' es hle hrun r hr
        obtain ⟨sgx, esx, h1, -, -, h4, -⟩ := hro av dv hle bf
        have heq := hrun.symm.trans h1
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨-, rfl, -⟩ := heq
        exact h4 r hr
    imodintro
    iexists p2, p1, lw, region
    isplitr
    · ipureintro; exact hvar
    isplitr
    · ipureintro; exact ⟨hs2, hs1, hs0⟩
    isplitr
    · ipureintro; exact hpins
    isplitr
    · ipureintro; exact ⟨hd2, hd1⟩
    isplitr
    · ipureintro; exact hcoll
    isplitr
    · ipureintro; exact hnv
    isplitr
    · ipureintro; exact hexpb
    isplitr
    · ipureintro; exact fun bf => hgof bf (hexpb bf)
    isplitr
    · ipureintro; exact hexecp
    isplitl [Hri]
    · iexact Hri
    isplitl [Hwand]
    · iexact Hwand
    ileft
    isplitr
    · ipureintro; exact hro
    isplitl [Hlog]
    · iexact Hlog
    · iexact Hlat
  · obtain ⟨wtr, hfam'⟩ := hfam
    have hexpb : ∀ bf : Bool, wwalkExports tid (wsetReg σ .minstret_increment bf) root va pa p2 p1 (mkPte ppn pc.flags) lw := by
      intro bf
      unfold wwalkExports
      refine ⟨hvar, hwlog, hs2, hs1, hs0, hpins, hd2, hd1, hcoll, Or.inr ⟨lw', wtr, hupd, ?_⟩, ?_⟩
      · intro av dv hle
        obtain ⟨sg', es, h1, h2, h3, -, h5⟩ := hfam' av dv hle bf
        exact ⟨sg', es, h1, h2, h3, h5⟩
      · intro av dv sg' es hle hrun r hr
        obtain ⟨sgx, esx, h1, -, -, h4, -⟩ := hfam' av dv hle bf
        have heq := hrun.symm.trans h1
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨-, rfl, -⟩ := heq
        exact h4 r hr
    imodintro
    iexists p2, p1, lw, region
    isplitr
    · ipureintro; exact hvar
    isplitr
    · ipureintro; exact ⟨hs2, hs1, hs0⟩
    isplitr
    · ipureintro; exact hpins
    isplitr
    · ipureintro; exact ⟨hd2, hd1⟩
    isplitr
    · ipureintro; exact hcoll
    isplitr
    · ipureintro; exact hnv
    isplitr
    · ipureintro; exact hexpb
    isplitr
    · ipureintro; exact fun bf => hgof bf (hexpb bf)
    isplitr
    · ipureintro; exact hexecp
    isplitl [Hri]
    · iexact Hri
    isplitl [Hwand]
    · iexact Hwand
    iright
    iexists lw'
    isplitr
    · ipureintro; exact hupd
    isplitr
    · ipureintro; exact ⟨wtr, hfam'⟩
    isplitl [Hlog]
    · iexact Hlog
    · iexact Hlat

end WkFetchFupd

end Weak
