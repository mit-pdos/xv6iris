/-
Weak: **the tail obligations of a fetch-walking step** (walk-bridge §8, 6c: the pure half of the
capstone leaf).  `Weak/WkStepPeel.lean` assembles the peel, the family and the Q-half of a whole
`riscvStep tick` whose FETCH walks the page table, and leaves four obligations open — the ones
that mention the INSTRUCTION rather than the walk: `wexecTail`, `wstepPostTail`,
`wstepTickTail` (weak side, at `wmi σ bmi`) and `wstepFamilyReady` (mirror side).  This file
discharges all four for an instruction whose EXECUTE phase is REGISTER-ONLY, generically in the
instruction (`wexecRegonly`), so a concrete leaf instantiates rather than re-proves.  Everything
is pure `Prop`: no Iris.

Rocq: `iris/WkWalkTails.v` @ xxvzwolszwmp (1322 lines; one Lean file).

The Rocq header, in substance.  (a) THE FETCH'S OUTCOME (§5, `wfetchRunOutcome`):
`WkFetchPeel.wwalkRunOutcome` one level up — peel + a family of `execStale` runs of the whole
`fetch ()` (the text read supplied at each member's own post-state) + `WeakStale` §10's
⇐-bridge; out comes `F_Base w` and every register but `tlb`, every byte off the leaf window and
the device where σ left them, which transports the instruction's register-shaped premises.
(b) THE POSTLUDE (§8): `tsAfterRha sv` is total and quiet only on the RETIRE arm, so `sv` is
PINNED the same way one level up again (`wrhaPeel` + a family of `execStaleRunHartActive` runs +
the ⇐-bridge).  (c) THE TICK (§7): totality works (`stepTick false` is `pure`, `tick_clock` is
total, register-only and quiet).  The guarded `wstepFamilyReady` (its `∀ u` restricted to
filter-accepted words) is discharged outright in §9 (`wstepFamilyReadyOf`).  No graph-tier fact
is used anywhere: the file lives at `wrun` / `execEff` / `execStale`.

**Deviations from Rocq.**
1. VOCABULARY as `Weak/WkFetchPeel.lean` / `Weak/WkStepPeel.lean` deviation 1 (`σ.wmRegs r`,
   `t.regs`/`t.mem`/`t.dev`, `BMap`, `wflatMem`, `pa + BitVec.ofNat 64 j`, `nthByte (n := 4)`,
   `bmWrite` for `write_bytes`, `r ≠ .tlb` for `register_beq r tlb = false`, `.Retire_Success ()`
   for `RETIRE_SUCCESS`, `zero_extend (m := 32)` for `zero_extend' 32`, `SailME.run` for
   `Defs.catch_early_return`, `(x == y) = false` for `eq_vec x y = false`, `F .hart_state` …).
   Statement-level `let`s the statements do not use (`a2`, `a1`) are dropped.
2. `wfgateRegs` follows `WkFetchPeel` deviation 7: Rocq's `addr_is_ram pa ∧ addr_is_ram (pa_add
   pa 3)` ↦ `inRam pa 4`, `pma_allows_all regions` ↦ `regions = bootPMA`, the vector reads
   `(regs .pmpcfg_n)[0]!`, `uint` ↦ `toNat`, `ram_base + ram_size` ↦ `ramEnd` (8 conjuncts for
   Rocq's 9).  Consequently `wfgateRegsTransport` takes the same five register equations.
3. O2 (`WkFetchPeel` deviations 4–5): the text read is the i-cache read, trace element
   `.WEread WeakFetchEff.wakIfetch pa 4` (Rocq `WEread wak_plain pa 4`) in `execEffTextReadAt`,
   `wfetchMemberRun`, `wfetchFamily` and `wstepReadyAtMember`; it is unpinned (`akPins wakIfetch
   = false`), so it enters `traceStale` through the disjoint arm exactly as Rocq's.  The "text
   bytes pinned" conjunct of `wfetchSite` and the premise of `wfetchSiteWmi` are the FETCH pin
   `fetchPinned σ (WeakInterp.accAddr pa j)` (Rocq `pinned_read`), which is what
   `wfetchPeelKSelfcontained` / `wfetchPeelSelfcontained` demand.
4. `wtrace_wonly_reads` is in the duplicated-name table: `WkWalkTails.wtraceWonlyReads`.
5. PROOF STRUCTURE: Rocq's `cbn match`/`rewrite` chains over `rha_after_fetch` /
   `ts_after_rha` are `simp` normalisation as `WeakEffSkel.execEffHartActiveProgressBaseGen` /
   `execEffRiscvStepHartActive`; `vm_compute` register disequalities are `by decide`.  The
   Lean-only `WkWalkTails.textRead` packages the one-read trace facts.
6. Rocq §11's `Print Assumptions` commands are not declarations; Rocq's axiom-footprint remark on
   `wstep_tick_tail_of` (functional extensionality) has no Lean counterpart, the premise is kept.

**Rocq → Lean name map.**  `wstep_ok_of_eff_nil` `wstepOkOfEffNil`, `wstep_ok_of_eff_nil_flat`
`wstepOkOfEffNilFlat`, `wtrace_wonly_app` `wtraceWonlyApp`, `wtrace_wonly_reads`
`WkWalkTails.wtraceWonlyReads`, `wfgate_regs` `wfgateRegs`, `wfgate_regs_transport`
`wfgateRegsTransport`, `wfgate_regs_off_tlb` `wfgateRegsOffTlb`, `wfgates_at_of_regs`
`wfgatesAtOfRegs`, `exec_eff_text_read_at` `execEffTextReadAt`, `wfetch_member_run`
`wfetchMemberRun`, `wfetch_site` `wfetchSite`, `wexec_regonly` `wexecRegonly`, `winstr_site`
`winstrSite`, `wfetch_fam` `wfetchFam`, `wfetch_family` `wfetchFamily`, `wfetch_outcome_glue`
`wfetchOutcomeGlue`, `wfetch_peel_k_of_site` `wfetchPeelKOfSite`, `wfetch_run_outcome`
`wfetchRunOutcome`, `exec_eff_rha_after_fetch_base` `execEffRhaAfterFetchBase`,
`exec_eff_rha_after_fetch_regonly` `execEffRhaAfterFetchRegonly`, `wstep_ok_rha_after_fetch`
`wstepOkRhaAfterFetch`, `wexec_tail_of` `wexecTailOf`, `exec_eff_ts_after_rha_retire`
`execEffTsAfterRhaRetire`, `trace_off_win_nil` `traceOffWinNil`, `trace_stale_nil`
`traceStaleNil`, `wstep_tick_tail_of` `wstepTickTailOf`, `wstep_tick_tail_of_tick`
`wstepTickTailOfTick`, `wrha_fam_of_fetch_fam` `wrhaFamOfFetchFam`, `wrha_run_outcome`
`wrhaRunOutcome`, `wstep_post_tail_of` `wstepPostTailOf`, `wstep_tail_eff_at` `wstepTailEffAt`,
`wstep_ready_at_member` `wstepReadyAtMember`, `wwalk_member_of_exports` `wwalkMemberOfExports`,
`wstep_family_ready_of` `wstepFamilyReadyOf`, `register_lookup_wmi` `registerLookupWmi`,
`wfgate_regs_wmi` `wfgateRegsWmi`, `wfetch_site_wmi` `wfetchSiteWmi`, `winstr_site_wmi`
`winstrSiteWmi`.  Lean-only (file-qualified): `WkWalkTails.textRead`.

**Dropped:** nothing.  38 Rocq declarations (`Definition`/`Lemma`): 38 ported + 1 Lean-only.

**Statements checked** (by hand, against Rocq): all; the changed ones are deviations 1–3.
-/
import Weak.WkStepPeel
import Weak.WeakTickEff

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. AN EMPTY-TRACE `execEff` RUN IS AN ORDINARY CERTIFICATE -/

/-- Rocq `wstep_ok_of_eff_nil`. -/
theorem wstepOkOfEffNil (tid : Option Nat) {X : Type} (m : SailM X) :
    ∀ (s : Wmstate) (mm : BMap) (x : X) (t : ExecSt),
      execEff m ⟨s.wmRegs, mm, s.wmDev⟩ = some (x, t, []) → wstepOk tid m s := by
  induction m with
  | pure y => intro _ _ _ _ _; trivial
  | impure call k ih =>
    intro s mm x t hex
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regWrite r v =>
        simp only [wstepOk]
        simp only [execEff] at hex
        exact ih _ (wsetReg s r v) mm x t hex
      case memRead n va req =>
        simp only [wstepOk]
        simp only [execEff] at hex
        by_cases hm : mmioAcc req.pa n = true
        · rw [if_pos hm] at hex ⊢
          intro w d' hdr
          simp only [hdr] at hex
          exact ih _ (wsetDev s d') mm x t hex
        · rw [if_neg hm] at hex
          split at hex
          · exact absurd hex (WkStepPeel.consNeNil _ _ _ _)
          · cases hex
      case memWrite n va req =>
        simp only [wstepOk]
        simp only [execEff] at hex
        cases hval : req.value with
        | none => simp only [hval, reduceCtorEq] at hex
        | some v =>
          simp only [hval] at hex ⊢
          by_cases hm : mmioAcc req.pa n = true
          · rw [if_pos hm] at hex ⊢
            intro d' hdw
            simp only [hdw] at hex
            exact ih _ (wsetDev s d') mm x t hex
          · rw [if_neg hm] at hex
            exact absurd hex (WkStepPeel.consNeNil _ _ _ _)
      case barrier bk =>
        simp only [execEff] at hex
        exact absurd hex (WkStepPeel.consNeNil _ _ _ _)
      all_goals first
        | (simp only [execEff, reduceCtorEq] at hex; done)
        | (simp only [wstepOk]
           simp only [execEff] at hex
           exact ih _ s mm x t hex)

/-- Rocq `wstep_ok_of_eff_nil_flat`. -/
theorem wstepOkOfEffNilFlat (tid : Option Nat) {X : Type} (m : SailM X) (s : Wmstate) (x : X)
    (t : ExecSt) : execEff m (wflatSt s) = some (x, t, []) → wstepOk tid m s := fun hex =>
  wstepOkOfEffNil tid m s (wflatMem s.wmImg s.wmLog) x t hex

/-- Rocq `wtrace_wonly_app`. -/
theorem wtraceWonlyApp (A : PAddr → Nat → Prop) (es1 es2 : List Weff) :
    wtraceWonly A es1 → wtraceWonly A es2 → wtraceWonly A (es1 ++ es2) := by
  intro h1 h2 ak pa n v hin
  rcases List.mem_append.1 hin with hin | hin
  · exact h1 ak pa n v hin
  · exact h2 ak pa n v hin

/-- Rocq `wtrace_wonly_reads` (duplicated name). -/
theorem WkWalkTails.wtraceWonlyReads (A : PAddr → Nat → Prop) (ak : AkInfo) (pa : PAddr) (n : Nat) :
    wtraceWonly A [.WEread ak pa n] := by
  intro ak0 pa0 n0 v hin
  simp at hin

/-! ## 2. THE TEXT READ, AT AN ARBITRARY STATE WITH σ's GATE REGISTERS -/

/-- Rocq `wfgate_regs` (deviation 2). -/
def wfgateRegs (regs : RegFile) (pa : BitVec 64) : Prop :=
  inRam pa 4 ∧
  pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (regs .pmpcfg_n)[0]!) = .TOR ∧
  zopz0zKzJ_u (zeros (n := 64)) (regs .pmpaddr_n)[0]! = false ∧
  (_get_Pmpcfg_ent_X (regs .pmpcfg_n)[0]! == 1#1) = true ∧
  ramEnd ≤ (regs .pmpaddr_n)[0]!.toNat * 4 ∧
  regs .pma_regions = bootPMA ∧
  regs .htif_tohost_base = none ∧
  regs .cur_privilege = .Supervisor

/-- Rocq `wfgate_regs_transport`. -/
theorem wfgateRegsTransport (regs regs' : RegFile) (pa : BitVec 64) :
    wfgateRegs regs pa →
    regs' .pmpcfg_n = regs .pmpcfg_n →
    regs' .pmpaddr_n = regs .pmpaddr_n →
    regs' .pma_regions = regs .pma_regions →
    regs' .htif_tohost_base = regs .htif_tohost_base →
    regs' .cur_privilege = regs .cur_privilege →
    wfgateRegs regs' pa := by
  intro hg hc ha hm hh hp
  unfold wfgateRegs
  rw [hc, ha, hm, hh, hp]
  exact hg

/-- Rocq `wfgate_regs_off_tlb`. -/
theorem wfgateRegsOffTlb (regs regs' : RegFile) (pa : BitVec 64) :
    wfgateRegs regs pa → (∀ r : Register, r ≠ .tlb → regs' r = regs r) → wfgateRegs regs' pa :=
  fun hg hoff => wfgateRegsTransport regs regs' pa hg (hoff _ (by decide)) (hoff _ (by decide))
    (hoff _ (by decide)) (hoff _ (by decide)) (hoff _ (by decide))

/-- Rocq `wfgates_at_of_regs`: the gates themselves, at an arbitrary state. -/
theorem wfgatesAtOfRegs (t : ExecSt) (pa : BitVec 64) :
    wfgateRegs t.regs pa →
    ∃ region : PMA_Region,
      execEff (pmpCheck (.Physaddr pa) 4 (.InstructionFetch ()) .Supervisor) t = some (none, t, []) ∧
      matching_pma_region (t.regs .pma_regions) (.Physaddr pa) 4 = some region ∧
      execEff (within_clint (.Physaddr pa) 4) t = some (false, t, []) ∧
      execEff (within_sig (.Physaddr pa) 4) t = some (false, t, []) ∧
      execEff (within_htif_readable (.Physaddr pa) 4) t = some (false, t, []) ∧
      (override_PMA region.attributes .PBMT_PMA).executable = true := by
  intro ⟨hram, hA, hlt, hX, hcov, hall, hhtif, _hpriv⟩
  obtain ⟨region, hmatch, hexec⟩ := wfetchRegionOfRegs pa _ hram hall
  have hz : (zeros (n := 64)).toNat = 0 := rfl
  have h4 : (to_bits (l := 64) 4).toNat = 4 := by decide
  refine ⟨region, ?_, hmatch, ?_, ?_, execEffWithinHtifFalse _ 4 _ hhtif, hexec⟩
  · apply execEffPmpCheckSupervisorGrantFetch
    · exact hA
    · exact hlt
    · rw [hz, h4]
      exact pmpRangeMatch_full _ _ _ _ (Nat.zero_le _) (by decide) (by have := hram.2; omega)
    · exact hX
  · rw [within_clint_ram pa 4 hram]; rfl
  · first
    | rfl
    | (simp only [within_sig, plat_have_sig, Functions.not]; rfl)

/-- Rocq `exec_eff_text_read_at` (deviation 3: the i-cache read). -/
theorem execEffTextReadAt (t : ExecSt) (pa : BitVec 64) (w : BitVec 32) :
    wfgateRegs t.regs pa →
    is_aligned_paddr (.Physaddr pa) 4 = true →
    (∀ j : Nat, j < 4 → t.mem (pa + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    execEff (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr pa) 4 false false false) t =
      some (.Ok w, t, [.WEread WeakFetchEff.wakIfetch pa 4]) := by
  intro hg halign hbytes
  obtain ⟨region, hpmp, hmatch, hc, hsig, hh, hexec⟩ := wfgatesAtOfRegs t pa hg
  exact execEffMemReadFetchGen .Supervisor .PBMT_PMA pa region w t hpmp hmatch halign hexec hc hsig hh
    (devAddrRam pa 4 hg.1) hbytes hg.2.2.2.2.2.2.2

/-! ## 3. THE FETCH, AT ONE FAMILY MEMBER -/

/-- Rocq `wfetch_member_run`. -/
theorem wfetchMemberRun (s : Wmstate) (la : PAddr) (va pa : BitVec 64) (w : BitVec 32)
    (u : BitVec (8 * 8)) (sgm : ExecSt) (esm : List Weff) :
    accWf la 8 →
    accWf pa 4 →
    raccDisj la 8 pa 4 →
    s.wmRegs .PC = va →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    is_aligned_paddr (.Physaddr pa) 4 = true →
    isRVC (Sail.BitVec.extractLsb w 15 0) = false →
    wfgateRegs s.wmRegs pa →
    (∀ j : Nat, j < 4 → wflatMem s.wmImg s.wmLog (pa + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    execStale la 8 u (translateAddr (.Virtaddr va) (.InstructionFetch ())) (wflatSt s) =
      some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sgm, esm) →
    (sgm.mem = wflatMem s.wmImg s.wmLog ∨
     ∃ lw' : BitVec 64, sgm.mem = bmWrite (wflatMem s.wmImg s.wmLog) la 8 lw') →
    (∀ r : Register, r ≠ .tlb → sgm.regs r = s.wmRegs r) →
    execEff (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr pa) 4 false false false) sgm =
      some (.Ok w, sgm, [.WEread WeakFetchEff.wakIfetch pa 4]) ∧
    execStale la 8 u (fetch ()) (wflatSt s) =
      some (.F_Base w, sgm, esm ++ [.WEread WeakFetchEff.wakIfetch pa 4]) := by
  intro hacc haccp hdisj hpc halv halp hnotRVC hgates hbytes htr hmem hregs
  -- the leaf window and the text window are byte-wise apart
  have hne : ∀ i j : Nat, i < 8 → j < 4 → la + BitVec.ofNat 64 i ≠ pa + BitVec.ofNat 64 j :=
    fun i j hi hj heq => paAddNeq pa la 4 8 j i haccp hacc hdisj hj hi heq.symm
  -- the member holds the text word ...
  have hbm : ∀ j : Nat, j < 4 → sgm.mem (pa + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j) := by
    intro j hj
    rcases hmem with hmem | ⟨lw', hmem⟩ <;> rw [hmem]
    · exact hbytes j hj
    · rw [writeBytesLookupNe _ _ _ _ _ (fun i hi heq => hne i j hi hj heq.symm)]
      exact hbytes j hj
  -- ... and σ's gate registers
  have hgm : wfgateRegs sgm.regs pa := wfgateRegsOffTlb s.wmRegs sgm.regs pa hgates hregs
  have hmr := execEffTextReadAt sgm pa w hgm halp hbm
  exact ⟨hmr, execStaleFetchS la u va pa w (wflatSt s) sgm esm hacc haccp hdisj hpc halv hnotRVC htr hmr⟩

/-! ## 4. THE TWO SITE BUNDLES -/

/-- Rocq `wfetch_site` (deviation 3: the text pins are FETCH pins). -/
def wfetchSite (tid : Option Nat) (σ : Wmstate) (root : BitVec 44) (va pa p2 p1 w0 lw : BitVec 64)
    (w : BitVec 32) : Prop :=
  let vpn := WeakKpt.svpnOf va
  let la := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)
  σ.wmRegs .PC = va ∧
  is_aligned_vaddr (.Virtaddr va) 4 = true ∧
  is_aligned_paddr (.Physaddr pa) 4 = true ∧
  isRVC (Sail.BitVec.extractLsb w 15 0) = false ∧
  wwalkExports tid σ root va pa p2 p1 w0 lw ∧
  wfgateRegs σ.wmRegs pa ∧
  raccDisj la 8 pa 4 ∧
  accWf pa 4 ∧
  (∀ j : Nat, j < 4 → paZ (pa + BitVec.ofNat 64 j) ≠ 0) ∧
  (∀ j : Nat, j < 4 → fetchPinned σ (WeakInterp.accAddr pa j)) ∧
  (∀ j : Nat, j < 4 → wflatMem σ.wmImg σ.wmLog (pa + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j))

/-- Rocq `wexec_regonly`: `execute i` retires at EVERY state, emits nothing and moves only the
registers `F` admits. -/
def wexecRegonly (i : instruction) (F : Register → Bool) : Prop :=
  ∀ s : ExecSt, ∃ s' : ExecSt,
    execEff (execute i) s = some (.Retire_Success (), s', []) ∧
    ∀ r : Register, F r = false → s'.regs r = s.regs r

/-- Rocq `winstr_site`. -/
def winstrSite (σ : Wmstate) (w : BitVec 32) (i : instruction) (F : Register → Bool) : Prop :=
  (∀ t : ExecSt, (∀ r : Register, r ≠ .tlb → t.regs r = σ.wmRegs r) →
     execEff (ext_decode w) t = some (i, t, [])) ∧
  (σ.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false ∧
  wexecRegonly i F ∧
  F .hart_state = false ∧
  σ.wmRegs .hart_state = .HART_ACTIVE ()

/-! ## 5. THE FETCH FAMILY, AND THE FETCH'S RUN OUTCOME -/

/-- Rocq `wfetch_fam`. -/
def wfetchFam (σ : Wmstate) (la : PAddr) (pa : BitVec 64) (w : BitVec 32)
    (Φ : (Nat → BitVec 8) → Prop) (T : List Weff → Prop) : Prop :=
  ∀ u : BitVec (8 * 8), Φ (fun j : Nat => nthByte u j) →
    ∃ (sgm : ExecSt) (esm : List Weff),
      execStale la 8 u (fetch ()) (wflatSt σ) = some (.F_Base w, sgm, esm) ∧
      T esm ∧
      sgm.dev = σ.wmDev ∧
      (sgm.mem = wflatMem σ.wmImg σ.wmLog ∨
       ∃ lw' : BitVec 64, sgm.mem = bmWrite (wflatMem σ.wmImg σ.wmLog) la 8 lw') ∧
      (∀ r : Register, r ≠ .tlb → sgm.regs r = σ.wmRegs r) ∧
      (∀ a : PAddr, (∀ j : Nat, j < 8 → la + BitVec.ofNat 64 j ≠ a) →
        wtraceWonly (fun (pa0 : PAddr) (n : Nat) => ∀ j : Nat, j < n → pa0 + BitVec.ofNat 64 j ≠ a) esm)

/-- Lean-only: the one-read trace facts of the appended text read. -/
theorem WkWalkTails.textRead (la pa : PAddr) :
    accWf pa 4 → raccDisj la 8 pa 4 →
    traceOffWin la 8 [.WEread WeakFetchEff.wakIfetch pa 4] ∧
    traceStale wakPlain la 8 [.WEread WeakFetchEff.wakIfetch pa 4] ∧
    ∀ a : PAddr, wtraceWonly (fun (pa0 : PAddr) (n : Nat) => ∀ j : Nat, j < n → pa0 + BitVec.ofNat 64 j ≠ a)
      [.WEread WeakFetchEff.wakIfetch pa 4] := by
  intro haccp hdisj
  refine ⟨traceOffWinOfAll _ _ _ fun ak pa0 n hin => ?_, Or.inr (Or.inl ⟨rfl, hdisj, trivial⟩),
    fun a => WkWalkTails.wtraceWonlyReads _ _ _ _⟩
  simp only [List.mem_singleton, Weff.WEread.injEq] at hin
  obtain ⟨rfl, rfl, rfl⟩ := hin
  exact ⟨haccp, hdisj⟩

/-- Rocq `wfetch_family`: the absorption theorem's three ghost arms, each extended by the text
read. -/
theorem wfetchFamily (tid : Option Nat) (σ : Wmstate) (root : BitVec 44) (va pa p2 p1 w0 lw : BitVec 64)
    (w : BitVec 32) :
    let vpn := WeakKpt.svpnOf va
    let la := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)
    wfetchSite tid σ root va pa p2 p1 w0 lw w →
    wfetchFam σ la pa w (wwalkFilter w0 lw) (traceStale wakPlain la 8) ∨
    wfetchFam σ la pa w (wwalkFilter w0 lw) (traceOffWin la 8) := by
  intro vpn la hsite
  obtain ⟨hpc, halv, halp, hnotRVC, hexp, hgates, hdisj, haccp, -, -, hbytes⟩ := hsite
  obtain ⟨-, -, -, -, hs0, -, hd2, hd1, -, harm, hregs⟩ := hexp
  have hacc : accWf la 8 := ptSlotMemAccWf _ _ _ hs0
  obtain ⟨hrdoff, hrdst, hwoff⟩ := WkWalkTails.textRead la pa haccp hdisj
  rcases harm with hro | ⟨lw', wtr, -, hfam⟩
  · -- ---------- READ-ONLY: four stale-friendly shapes ----------
    left
    intro u hu
    obtain ⟨av, dv, rfl, hle⟩ := wwalkFilterInv w0 lw u hu
    obtain ⟨sgm, esm, hex, hmem, hmdev, hes⟩ := hro av dv hle
    have hrg := hregs av dv sgm esm hle hex
    obtain ⟨-, hf⟩ := wfetchMemberRun σ la va pa w _ sgm esm hacc haccp hdisj hpc halv halp hnotRVC hgates
      hbytes hex (Or.inl hmem) hrg
    have hev : ∀ e, e ∈ esm → wwalkEvOk (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))
        (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) la e := by
      rcases hes with rfl | rfl | rfl | rfl <;> (try simp only [la, vpn]) <;> wwalk_evs
    refine ⟨sgm, _, hf, traceStaleApp _ _ _ _ _ ?_ hrdst hrdoff, hmdev, Or.inl hmem, hrg,
      fun a hoff => wtraceWonlyApp _ _ _ (wtraceWonlyOfEvs _ _ la esm a hev hoff) (hwoff a)⟩
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
      obtain ⟨sgm, esm, hex, hmem, hmdev, hes⟩ := hfam av dv hle
      simp only [↓reduceIte] at hes
      have hrg := hregs av dv sgm esm hle hex
      obtain ⟨-, hf⟩ := wfetchMemberRun σ la va pa w _ sgm esm hacc haccp hdisj hpc halv halp hnotRVC
        hgates hbytes hex (Or.inr ⟨lw', hmem⟩) hrg
      have hev : ∀ e, e ∈ esm → wwalkEvOk (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))
        (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) la e := by
        rw [hes]; (try simp only [la, vpn]); wwalk_evs
      exact ⟨sgm, _, hf, traceStaleApp _ _ _ _ _
        (traceStaleWalkShapes _ _ la lw' esm hd2 hd1 (Or.inr (Or.inr (Or.inr (Or.inr hes))))) hrdst hrdoff,
        hmdev, Or.inr ⟨lw', hmem⟩, hrg,
        fun a hoff => wtraceWonlyApp _ _ _ (wtraceWonlyOfEvs _ _ la esm a hev hoff) (hwoff a)⟩
    | false =>
      -- ---------- HIT write-back: the CONSTANT family ----------
      right
      intro u hu
      obtain ⟨av, dv, rfl, hle⟩ := wwalkFilterInv w0 lw u hu
      obtain ⟨sgm, esm, hex, hmem, hmdev, hes⟩ := hfam av dv hle
      simp only [Bool.false_eq_true, ↓reduceIte] at hes
      have hrg := hregs av dv sgm esm hle hex
      obtain ⟨-, hf⟩ := wfetchMemberRun σ la va pa w _ sgm esm hacc haccp hdisj hpc halv halp hnotRVC
        hgates hbytes hex (Or.inr ⟨lw', hmem⟩) hrg
      have hev : ∀ e, e ∈ esm → wwalkEvOk (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))
        (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) la e := by
        rw [hes]; (try simp only [la, vpn]); wwalk_evs
      refine ⟨sgm, _, hf, traceOffWinApp _ _ _ _ ?_ hrdoff, hmdev, Or.inr ⟨lw', hmem⟩, hrg,
        fun a hoff => wtraceWonlyApp _ _ _ (wtraceWonlyOfEvs _ _ la esm a hev hoff) (hwoff a)⟩
      rw [hes]
      exact traceOffWinPinned _ _ _ (by walk_stale_trace)

/-- Rocq `wfetch_outcome_glue`. -/
theorem wfetchOutcomeGlue (_tid : Option Nat) (σ s' : Wmstate) (la : PAddr) (pa : BitVec 64) (w : BitVec 32)
    (Φ : (Nat → BitVec 8) → Prop) (T : List Weff → Prop) (u : BitVec (8 * 8)) (r : FetchResult)
    (es : List Weff) :
    wfetchFam σ la pa w Φ T →
    Φ (fun j : Nat => nthByte u j) →
    execStale la 8 u (fetch ()) (wflatSt σ) = some (r, wflatSt s', es) →
    wlogWf s'.wmLog →
    (∀ a : PAddr,
      wtraceWonly (fun (pa0 : PAddr) (n : Nat) => ∀ j : Nat, j < n → pa0 + BitVec.ofNat 64 j ≠ a) es →
      latestTs s'.wmLog (paZ a) = latestTs σ.wmLog (paZ a)) →
    wsLe σ.wmWs s'.wmWs →
    r = .F_Base w ∧
    wlogWf s'.wmLog ∧
    wsLe σ.wmWs s'.wmWs ∧
    s'.wmDev = σ.wmDev ∧
    (∀ a : PAddr, (∀ j : Nat, j < 8 → la + BitVec.ofNat 64 j ≠ a) →
      latestTs s'.wmLog (paZ a) = latestTs σ.wmLog (paZ a)) ∧
    (∀ a : PAddr, (∀ j : Nat, j < 8 → la + BitVec.ofNat 64 j ≠ a) →
      wflatMem s'.wmImg s'.wmLog a = wflatMem σ.wmImg σ.wmLog a) ∧
    (∀ r0 : Register, r0 ≠ .tlb → s'.wmRegs r0 = σ.wmRegs r0) := by
  intro hfam hΦu hexu hwf' hlt hle
  obtain ⟨sgm, esm, hex, -, hmdev, hmem, hrg, hwo⟩ := hfam u hΦu
  rw [hex] at hexu
  simp only [Option.some.injEq, Prod.mk.injEq] at hexu
  obtain ⟨hx, hsg, hes⟩ := hexu
  refine ⟨hx.symm, hwf', hle, ?_, fun a hoff => hlt a (hes ▸ hwo a hoff), ?_, ?_⟩
  · rw [← wflatStDev s', ← hsg]; exact hmdev
  · intro a hoff
    rw [← wflatStMem s', ← hsg]
    rcases hmem with hmem | ⟨lw', hmem⟩
    · rw [hmem]
    · rw [hmem]
      exact writeBytesLookupNe _ _ _ _ _ (fun j hj heq => hoff j hj heq.symm)
  · intro r0 hr
    rw [← wflatStRegs s', ← hsg]
    exact hrg r0 hr

/-- Rocq `wfetch_peel_k_of_site`: the fetch peel, CPS and plain, from the site bundle. -/
theorem wfetchPeelKOfSite (tid : Option Nat) (σ : Wmstate) (root : BitVec 44) (va pa p2 p1 w0 lw : BitVec 64)
    (w : BitVec 32) :
    let vpn := WeakKpt.svpnOf va
    let la := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)
    wfetchSite tid σ root va pa p2 p1 w0 lw w →
    wfetchPeelKAt tid la (wwalkFilter w0 lw) σ ∧
    wstepOkRacy tid la 8 wakPlain (wwalkFilter w0 lw) wDAny True true (fetch ()) σ ∧
    wadmFilter σ wakPlain la 8 (wwalkFilter w0 lw) := by
  intro vpn la hsite
  obtain ⟨hpc, halv, halp, _hnotRVC, hexp, hgates, hdisj, haccp, hW0, hpin, hbytes⟩ := hsite
  obtain ⟨hram, hA, hlt, hX, hcov, hall, hhtif, hpriv⟩ := hgates
  obtain ⟨region, hgt, hexecp⟩ :=
    wfetchGatesOfRegs tid σ root va pa p2 p1 w0 lw hexp hram hA hlt hX hcov hall hhtif hpriv
  refine ⟨fun K hK => ?_, wfetchPeelSelfcontained tid σ root va pa p2 p1 w0 lw region w hpc halv hexp hdisj
    haccp hW0 hpin hbytes hgt halp hexecp (devAddrRam pa 4 hram)⟩
  exact (wfetchPeelKSelfcontained tid σ root va pa p2 p1 w0 lw region w K hpc halv hexp hdisj haccp hW0 hpin
    hbytes hgt halp hexecp (devAddrRam pa 4 hram) hK).1

/-- Rocq `wfetch_run_outcome`: THE OUTCOME OF THE WEAK FETCH RUN. -/
theorem wfetchRunOutcome (tid : Option Nat) (σ : Wmstate) (root : BitVec 44) (va pa p2 p1 w0 lw : BitVec 64)
    (w : BitVec 32) :
    let vpn := WeakKpt.svpnOf va
    let la := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)
    wfetchSite tid σ root va pa p2 p1 w0 lw w →
    ∀ (r : FetchResult) (s' : Wmstate), wrun tid (fetch ()) σ r s' →
      r = .F_Base w ∧
      wlogWf s'.wmLog ∧
      wsLe σ.wmWs s'.wmWs ∧
      s'.wmDev = σ.wmDev ∧
      (∀ a : PAddr, (∀ j : Nat, j < 8 → la + BitVec.ofNat 64 j ≠ a) →
        latestTs s'.wmLog (paZ a) = latestTs σ.wmLog (paZ a)) ∧
      (∀ a : PAddr, (∀ j : Nat, j < 8 → la + BitVec.ofNat 64 j ≠ a) →
        wflatMem s'.wmImg s'.wmLog a = wflatMem σ.wmImg σ.wmLog a) ∧
      (∀ r0 : Register, r0 ≠ .tlb → s'.wmRegs r0 = σ.wmRegs r0) := by
  intro vpn la hsite r s' hrun
  have hexp := hsite.2.2.2.2.1
  obtain ⟨-, hwf, -, -, hs0, -⟩ := hexp
  have hacc : accWf la 8 := ptSlotMemAccWf _ _ _ hs0
  obtain ⟨-, hpeel, hfilt⟩ := wfetchPeelKOfSite tid σ root va pa p2 p1 w0 lw w hsite
  have hrd : (bmRead (wflatMem σ.wmImg σ.wmLog) la 8).isSome = true := by
    rw [bmRead_of_bytes (wflatMem σ.wmImg σ.wmLog) la 8 lw hs0.1]; rfl
  have hle := wrunWsLe tid _ σ r s' hrun
  rcases wfetchFamily tid σ root va pa p2 p1 w0 lw w hsite with hfam | hfam
  · obtain ⟨u, es, -, hΦu, hexu, hwf', hlt⟩ :=
      wrunExecStaleElim tid la 8 wakPlain (wwalkFilter w0 lw) True (fetch ()) hacc (by decide) akPinsPlain σ
        hpeel hwf hfilt hrd
        (fun u hu => by
          obtain ⟨sgm, esm, hex, ht, -⟩ := hfam u hu
          exact ⟨.F_Base w, sgm, esm, hex, ht⟩) r s' hrun
    exact wfetchOutcomeGlue tid σ s' la pa w _ _ u r es hfam hΦu hexu hwf' hlt hle
  · obtain ⟨u, es, -, hΦu, hexu, hwf', hlt⟩ :=
      wrunExecStaleElimConst tid la 8 wakPlain (wwalkFilter w0 lw) True true (fetch ()) hacc (by decide)
        akPinsPlain σ hpeel hwf hfilt hrd
        (fun u hu => by
          obtain ⟨sgm, esm, hex, ht, -⟩ := hfam u hu
          exact ⟨.F_Base w, sgm, esm, hex, ht⟩) r s' hrun
    exact wfetchOutcomeGlue tid σ s' la pa w _ _ u r es hfam hΦu hexu hwf' hlt hle

/-! ## 6. THE POST-FETCH REMAINDER, AND `wexecTail` -/

/-- Rocq `exec_eff_rha_after_fetch_base`: the remainder at `execEff`, at an arbitrary state. -/
theorem execEffRhaAfterFetchBase (s s_x : ExecSt) (w : BitVec 32) (i : instruction) (pc : BitVec 64)
    (resf : ExecutionResult) (es_x : List Weff) :
    execEff (ext_decode w) s = some (i, s, []) →
    (s.regs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    s.regs .PC = pc →
    execEff (execute i) (s.setReg .nextPC (BitVec.addInt pc 4)) = some (resf, s_x, es_x) →
    (match resf with | .ExecuteAs _ => False | _ => True) →
    execEff (SailME.run (rhaAfterFetch (.F_Base w))) s =
      some (.Step_Execute (resf, zero_extend (m := 32) w), s_x, es_x) := by
  intro hdec hlpad hpc hexec hnot
  unfold rhaAfterFetch ext_fetch_hook get_config_print_instr
  rw [execEffCatchEarlyReturn]
  simp (config := { decide := true }) only [execREffBindEq, execREffLiftR, execREffReturnR,
    readReg, writeReg, PreSail.readReg, PreSail.writeReg, PreSail.emit, execEff,
    ↓reduceIte, Bool.false_eq_true, execEffInstrAnnounce, hdec,
    execEffIsLandingPad, hlpad, hpc, hexec, Bool.false_and, List.nil_append, List.append_nil]
  cases resf <;> simp at hnot <;> simp [execREffReturnR, List.append_nil]

/-- Rocq `exec_eff_rha_after_fetch_regonly`. -/
theorem execEffRhaAfterFetchRegonly (s : ExecSt) (w : BitVec 32) (i : instruction) (F : Register → Bool) :
    execEff (ext_decode w) s = some (i, s, []) →
    (s.regs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    wexecRegonly i F →
    ∃ s_x : ExecSt,
      execEff (SailME.run (rhaAfterFetch (.F_Base w))) s =
        some (.Step_Execute (.Retire_Success (), zero_extend (m := 32) w), s_x, []) ∧
      ∀ r : Register, F r = false → r ≠ .nextPC → s_x.regs r = s.regs r := by
  intro hdec hlpad hex
  obtain ⟨s_x, hxeq, hxreg⟩ := hex (s.setReg .nextPC (BitVec.addInt (s.regs .PC) 4))
  refine ⟨s_x, execEffRhaAfterFetchBase s s_x w i _ _ [] hdec hlpad rfl hxeq trivial, ?_⟩
  intro r hF hne
  rw [hxreg r hF]
  exact RegFile.set_other _ _ _ _ hne

/-- Rocq `wstep_ok_rha_after_fetch`. -/
theorem wstepOkRhaAfterFetch (tid : Option Nat) (s : Wmstate) (w : BitVec 32) (i : instruction)
    (F : Register → Bool) :
    execEff (ext_decode w) (wflatSt s) = some (i, wflatSt s, []) →
    (s.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    wexecRegonly i F →
    wstepOk tid (SailME.run (rhaAfterFetch (.F_Base w))) s := by
  intro hdec hlpad hex
  obtain ⟨s_x, hxeq, -⟩ := execEffRhaAfterFetchRegonly (wflatSt s) w i F hdec hlpad hex
  exact wstepOkOfEffNilFlat tid _ s _ s_x hxeq

/-- Rocq `wexec_tail_of`: `wexecTail`, DISCHARGED. -/
theorem wexecTailOf (tid : Option Nat) (σ : Wmstate) (root : BitVec 44) (va pa p2 p1 w0 lw : BitVec 64)
    (w : BitVec 32) (i : instruction) (F : Register → Bool) :
    wfetchSite tid σ root va pa p2 p1 w0 lw w →
    winstrSite σ w i F →
    wexecTail tid σ := by
  intro hsite ⟨hdec, hlpad, hex, _, _⟩ r s' hrun
  obtain ⟨rfl, -, -, -, -, -, hrg⟩ := wfetchRunOutcome tid σ root va pa p2 p1 w0 lw w hsite r s' hrun
  refine wstepOkRhaAfterFetch tid s' w i F (hdec (wflatSt s') hrg) ?_ hex
  rw [hrg .elp (by decide)]
  exact hlpad

/-! ## 7. THE POSTLUDE AND THE TICK -/

/-- Rocq `exec_eff_ts_after_rha_retire`: on the RETIRE arm, with the hart active, the postlude
is total, register-only and quiet. -/
theorem execEffTsAfterRhaRetire (s : ExecSt) (ib : BitVec 32) :
    s.regs .hart_state = .HART_ACTIVE () →
    ∃ (bb : Bool) (t : ExecSt),
      execEff (tsAfterRha (.Step_Execute (.Retire_Success (), ib))) s = some (bb, t, []) := by
  intro hhart
  unfold tsAfterRha
  simp only [execEffBindEq, readReg, writeReg, PreSail.readReg, PreSail.writeReg, PreSail.emit,
    execEff, effThen, hhart, assert, PreSail.assert, hart_is_active,
    ↓reduceIte, execEffReturnm, execEffTickPc, get_config_rvfi, Bool.false_eq_true,
    List.nil_append]
  cases hmi : (s.setReg .PC (s.regs .nextPC)).regs .minstret_increment <;>
    simp only [execEffBindEq, execEff, effThen, ↓reduceIte, Bool.false_eq_true, execEffReturnm, List.nil_append] <;> exact ⟨_, _, rfl⟩

/-- Rocq `trace_off_win_nil`. -/
theorem traceOffWinNil (ra : PAddr) (rn : Nat) : traceOffWin ra rn [] := by
  intro ak pa n hin
  simp at hin

/-- Rocq `trace_stale_nil`. -/
theorem traceStaleNil (rak : AkInfo) (ra : PAddr) (rn : Nat) : traceStale rak ra rn [] := trivial

/-- Rocq `wstep_tick_tail_of`: the tick, by TOTALITY (the tick-`true` totality a premise). -/
theorem wstepTickTailOf (tid : Option Nat) (σ : Wmstate) (tick : Bool) :
    (tick = true → ∀ s : ExecSt, ∃ t : ExecSt, execEff (tick_clock ()) s = some ((), t, [])) →
    wstepTickTail tid σ tick := by
  intro htot x s' _
  cases tick with
  | true =>
    obtain ⟨t, heq⟩ := htot rfl (wflatSt s')
    exact wstepOkOfEffNilFlat tid _ s' () t heq
  | false => show wstepOk tid (pure ()) s'; trivial

/-- Rocq `wstep_tick_tail_of_tick`. -/
theorem wstepTickTailOfTick (tid : Option Nat) (σ : Wmstate) (tick : Bool) : wstepTickTail tid σ tick := by
  apply wstepTickTailOf
  intro _ s
  obtain ⟨c, t0, p, heq⟩ := execEffTickClock s
  exact ⟨_, heq⟩

/-! ## 8. `run_hart_active`'s OUTCOME, AND `wstepPostTail` -/

/-- Rocq `wrha_fam_of_fetch_fam`. -/
theorem wrhaFamOfFetchFam (σ : Wmstate) (la : PAddr) (pa : BitVec 64) (w : BitVec 32) (i : instruction)
    (F : Register → Bool) (Φ : (Nat → BitVec 8) → Prop) (T : List Weff → Prop) :
    accWf la 8 →
    σ.wmRegs .cur_privilege = .Supervisor →
    execEff (dispatchInterrupt .Supervisor) (wflatSt σ) = some (none, wflatSt σ, []) →
    winstrSite σ w i F →
    wfetchFam σ la pa w Φ T →
    ∀ u : BitVec (8 * 8), Φ (fun j : Nat => nthByte u j) →
      ∃ (sx : ExecSt) (es : List Weff),
        execStale la 8 u (run_hart_active 0) (wflatSt σ) =
          some (.Step_Execute (.Retire_Success (), zero_extend (m := 32) w), sx, es) ∧
        T es ∧
        sx.regs .hart_state = .HART_ACTIVE () := by
  intro hacc hpriv hdisp ⟨hdec, hlpad, hex, hF, hhart⟩ hfam u hu
  obtain ⟨sgm, esm, hexf, ht, -, -, hrg, -⟩ := hfam u hu
  have hlpadm : (sgm.regs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false := by
    rw [hrg .elp (by decide)]; exact hlpad
  obtain ⟨sx, hxeq, hxreg⟩ := execEffRhaAfterFetchRegonly sgm w i F (hdec sgm hrg) hlpadm hex
  refine ⟨sx, esm, ?_, ht, ?_⟩
  · have hr := execStaleRunHartActive la u (wflatSt σ) sgm sx (.F_Base w) _ esm [] hacc hpriv hdisp hexf hxeq
      (traceOffWinNil la 8)
    rw [List.append_nil] at hr
    exact hr
  · rw [hxreg .hart_state hF (by decide), hrg .hart_state (by decide)]
    exact hhart

/-- Rocq `wrha_run_outcome`: the ⇐-bridge PINS the step value. -/
theorem wrhaRunOutcome (tid : Option Nat) (σ : Wmstate) (root : BitVec 44) (va pa p2 p1 w0 lw : BitVec 64)
    (w : BitVec 32) (i : instruction) (F : Register → Bool) :
    wfetchSite tid σ root va pa p2 p1 w0 lw w →
    winstrSite σ w i F →
    execEff (dispatchInterrupt .Supervisor) (wflatSt σ) = some (none, wflatSt σ, []) →
    ∀ (sv : Step) (s' : Wmstate), wrun tid (run_hart_active 0) σ sv s' →
      sv = .Step_Execute (.Retire_Success (), zero_extend (m := 32) w) ∧
      s'.wmRegs .hart_state = .HART_ACTIVE () := by
  intro hsite hinstr hdisp sv s' hrun
  have hexp := hsite.2.2.2.2.1
  have hpriv : σ.wmRegs .cur_privilege = .Supervisor := hsite.2.2.2.2.2.1.2.2.2.2.2.2.2
  obtain ⟨-, hwf, -, -, hs0, -⟩ := hexp
  have hacc := ptSlotMemAccWf _ _ _ hs0
  obtain ⟨hfk, -, hfilt⟩ := wfetchPeelKOfSite tid σ root va pa p2 p1 w0 lw w hsite
  have hpeel := wrhaPeel tid σ _ (wwalkFilter w0 lw) hpriv hdisp hfk
    (wexecTailOf tid σ root va pa p2 p1 w0 lw w i F hsite hinstr)
  have hrd : (bmRead (wflatMem σ.wmImg σ.wmLog) (uPteAddr (uNextBase p1)
      (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8).isSome = true := by
    rw [bmRead_of_bytes (wflatMem σ.wmImg σ.wmLog) _ 8 lw hs0.1]; rfl
  rcases wfetchFamily tid σ root va pa p2 p1 w0 lw w hsite with hfam | hfam
  · have hrfam := wrhaFamOfFetchFam σ _ pa w i F _ _ hacc hpriv hdisp hinstr hfam
    obtain ⟨u, es, -, hΦu, hexu, -, -⟩ :=
      wrunExecStaleElim tid _ 8 wakPlain (wwalkFilter w0 lw) True (run_hart_active 0) hacc (by decide)
        akPinsPlain σ hpeel hwf hfilt hrd
        (fun u hu => by
          obtain ⟨sx, es, hex, ht, -⟩ := hrfam u hu
          exact ⟨_, sx, es, hex, ht⟩) sv s' hrun
    obtain ⟨sx, es', hex, -, hhart⟩ := hrfam u hΦu
    rw [hex] at hexu
    simp only [Option.some.injEq, Prod.mk.injEq] at hexu
    obtain ⟨hx, hsg, -⟩ := hexu
    refine ⟨hx.symm, ?_⟩
    rw [← wflatStRegs s', ← hsg]
    exact hhart
  · have hrfam := wrhaFamOfFetchFam σ _ pa w i F _ _ hacc hpriv hdisp hinstr hfam
    obtain ⟨u, es, -, hΦu, hexu, -, -⟩ :=
      wrunExecStaleElimConst tid _ 8 wakPlain (wwalkFilter w0 lw) True true (run_hart_active 0) hacc
        (by decide) akPinsPlain σ hpeel hwf hfilt hrd
        (fun u hu => by
          obtain ⟨sx, es, hex, ht, -⟩ := hrfam u hu
          exact ⟨_, sx, es, hex, ht⟩) sv s' hrun
    obtain ⟨sx, es', hex, -, hhart⟩ := hrfam u hΦu
    rw [hex] at hexu
    simp only [Option.some.injEq, Prod.mk.injEq] at hexu
    obtain ⟨hx, hsg, -⟩ := hexu
    refine ⟨hx.symm, ?_⟩
    rw [← wflatStRegs s', ← hsg]
    exact hhart

/-- Rocq `wstep_post_tail_of`: `wstepPostTail`, DISCHARGED by run inversion. -/
theorem wstepPostTailOf (tid : Option Nat) (σ : Wmstate) (root : BitVec 44) (va pa p2 p1 w0 lw : BitVec 64)
    (w : BitVec 32) (i : instruction) (F : Register → Bool) :
    wfetchSite tid σ root va pa p2 p1 w0 lw w →
    winstrSite σ w i F →
    execEff (dispatchInterrupt .Supervisor) (wflatSt σ) = some (none, wflatSt σ, []) →
    wstepPostTail tid σ := by
  intro hsite hinstr hdisp sv s' hrun
  obtain ⟨rfl, hhart⟩ := wrhaRunOutcome tid σ root va pa p2 p1 w0 lw w i F hsite hinstr hdisp sv s' hrun
  obtain ⟨bb, t, heq⟩ := execEffTsAfterRhaRetire (wflatSt s') (zero_extend (m := 32) w) hhart
  exact wstepOkOfEffNilFlat tid _ s' bb t heq

/-! ## 9. THE MIRROR SIDE: `wstepTailEff` AND `wstepFamilyReady` -/

/-- Rocq `wstep_tail_eff_at`: the window-free tail at a mirror state. -/
theorem wstepTailEffAt (la : PAddr) (tick : Bool) (sf : ExecSt) (w : BitVec 32) (i : instruction)
    (F : Register → Bool) :
    execEff (ext_decode w) sf = some (i, sf, []) →
    (sf.regs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    wexecRegonly i F →
    F .hart_state = false →
    sf.regs .hart_state = .HART_ACTIVE () →
    (tick = true → ∀ s : ExecSt, ∃ t : ExecSt, execEff (tick_clock ()) s = some ((), t, [])) →
    wstepTailEff la tick sf (.F_Base w) := by
  intro hdec hlpad hex hF hhart htot
  obtain ⟨sx, hxeq, hxreg⟩ := execEffRhaAfterFetchRegonly sf w i F hdec hlpad hex
  have hhx : sx.regs .hart_state = .HART_ACTIVE () := by
    rw [hxreg .hart_state hF (by decide)]; exact hhart
  obtain ⟨bb, sy, hpost⟩ := execEffTsAfterRhaRetire sx (zero_extend (m := 32) w) hhx
  have htk : ∃ sfin : ExecSt, execEff (stepTick tick) sy = some ((), sfin, []) := by
    cases tick with
    | true => exact htot rfl sy
    | false => exact ⟨sy, rfl⟩
  obtain ⟨sfin, htick⟩ := htk
  exact ⟨_, sx, sy, sfin, bb, [], [], [], hxeq, hpost, htick, traceOffWinNil la 8,
    traceStaleNil wakPlain la 8⟩

/-- Rocq `wstep_ready_at_member`: one member's post-state, described, is everything. -/
theorem wstepReadyAtMember (tid : Option Nat) (σ : Wmstate) (root : BitVec 44) (va pa p2 p1 w0 lw : BitVec 64)
    (w : BitVec 32) (i : instruction) (F : Register → Bool) (tick : Bool) :
    let vpn := WeakKpt.svpnOf va
    let la := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)
    wfetchSite tid σ root va pa p2 p1 w0 lw w →
    winstrSite σ w i F →
    (tick = true → ∀ s : ExecSt, ∃ t : ExecSt, execEff (tick_clock ()) s = some ((), t, [])) →
    ∀ (u : BitVec (8 * 8)) (sg' : ExecSt) (esw : List Weff),
      execStale la 8 u (translateAddr (.Virtaddr va) (.InstructionFetch ())) (wflatSt σ) =
        some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sg', esw) →
      (sg'.mem = wflatMem σ.wmImg σ.wmLog ∨
       ∃ lw' : BitVec 64, sg'.mem = bmWrite (wflatMem σ.wmImg σ.wmLog) la 8 lw') →
      (∀ r : Register, r ≠ .tlb → sg'.regs r = σ.wmRegs r) →
      execEff (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr pa) 4 false false false) sg' =
        some (.Ok w, sg', [.WEread WeakFetchEff.wakIfetch pa 4]) ∧
      wstepTailEff la tick sg' (.F_Base w) := by
  intro vpn la hsite hinstr htot u sg' esw heq hmem hrg
  obtain ⟨hpc, halv, halp, hnotRVC, hexp, hgates, hdisj, haccp, -, -, hbytes⟩ := hsite
  obtain ⟨hdec, hlpad, hex, hF, hhart⟩ := hinstr
  obtain ⟨-, -, -, -, hs0, -⟩ := hexp
  have hacc : accWf la 8 := ptSlotMemAccWf _ _ _ hs0
  obtain ⟨hmr, -⟩ := wfetchMemberRun σ la va pa w u sg' esw hacc haccp hdisj hpc halv halp hnotRVC hgates
    hbytes heq hmem hrg
  refine ⟨hmr, wstepTailEffAt la tick sg' w i F (hdec sg' hrg) ?_ hex hF ?_ htot⟩
  · rw [hrg .elp (by decide)]; exact hlpad
  · rw [hrg .hart_state (by decide)]; exact hhart

/-- Rocq `wwalk_member_of_exports`: the member description, from the exports. -/
theorem wwalkMemberOfExports (tid : Option Nat) (σ : Wmstate) (root : BitVec 44)
    (va pa p2 p1 w0 lw : BitVec 64) (av dv : BitVec 1) :
    let vpn := WeakKpt.svpnOf va
    let la := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)
    wwalkExports tid σ root va pa p2 p1 w0 lw →
    pteAdLe (pteSetAD w0 av dv) lw →
    ∃ (sgx : ExecSt) (esx : List Weff),
      execStale la 8 (pteSetAD w0 av dv) (translateAddr (.Virtaddr va) (.InstructionFetch ())) (wflatSt σ) =
        some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sgx, esx) ∧
      (sgx.mem = wflatMem σ.wmImg σ.wmLog ∨
       ∃ lw' : BitVec 64, sgx.mem = bmWrite (wflatMem σ.wmImg σ.wmLog) la 8 lw') ∧
      (∀ r : Register, r ≠ .tlb → sgx.regs r = σ.wmRegs r) := by
  intro vpn la hexp hle
  obtain ⟨-, -, -, -, -, -, -, -, -, harm, hregs⟩ := hexp
  rcases harm with hro | ⟨lw', wtr, -, hfam⟩
  · obtain ⟨sgx, esx, hex, hmem, -, -⟩ := hro av dv hle
    exact ⟨sgx, esx, hex, Or.inl hmem, hregs av dv sgx esx hle hex⟩
  · obtain ⟨sgx, esx, hex, hmem, -, -⟩ := hfam av dv hle
    exact ⟨sgx, esx, hex, Or.inr ⟨lw', hmem⟩, hregs av dv sgx esx hle hex⟩

/-- Rocq `wstep_family_ready_of`: `wstepFamilyReady`, DISCHARGED. -/
theorem wstepFamilyReadyOf (tid : Option Nat) (σ : Wmstate) (root : BitVec 44)
    (va pa p2 p1 w0 lw : BitVec 64) (w : BitVec 32) (i : instruction) (F : Register → Bool) (tick : Bool) :
    let vpn := WeakKpt.svpnOf va
    let la := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)
    (∀ bmi : Bool, wfetchSite tid (wmi σ bmi) root va pa p2 p1 w0 lw w) →
    (∀ bmi : Bool, winstrSite (wmi σ bmi) w i F) →
    (tick = true → ∀ s : ExecSt, ∃ t : ExecSt, execEff (tick_clock ()) s = some ((), t, [])) →
    wstepFamilyReady tid σ la va pa w0 lw w tick := by
  intro vpn la hsites hinstrs htot bmi u sg' esw hu heq
  obtain ⟨av, dv, rfl, hle⟩ := wwalkFilterInv w0 lw u hu
  have hsite := hsites bmi
  obtain ⟨sgx, esx, hex, hmem, hrg⟩ :=
    wwalkMemberOfExports tid (wmi σ bmi) root va pa p2 p1 w0 lw av dv hsite.2.2.2.2.1 hle
  rw [hex] at heq
  simp only [Option.some.injEq, Prod.mk.injEq] at heq
  obtain ⟨-, rfl, rfl⟩ := heq
  exact wstepReadyAtMember tid (wmi σ bmi) root va pa p2 p1 w0 lw w i F tick hsite (hinstrs bmi) htot
    (pteSetAD w0 av dv) sgx esx hex hmem hrg

/-! ## 10. THE `wmi` TRANSPORTS THE CAPSTONE WANTS -/

/-- Rocq `register_lookup_wmi`. -/
theorem registerLookupWmi (σ : Wmstate) (b : Bool) (r : Register) :
    r ≠ .minstret_increment → (wmi σ b).wmRegs r = σ.wmRegs r :=
  WkStepPeel.wmiRegs σ b r

/-- Rocq `wfgate_regs_wmi`. -/
theorem wfgateRegsWmi (σ : Wmstate) (b : Bool) (pa : BitVec 64) :
    wfgateRegs σ.wmRegs pa → wfgateRegs (wmi σ b).wmRegs pa := fun hg =>
  wfgateRegsTransport σ.wmRegs (wmi σ b).wmRegs pa hg (registerLookupWmi σ b _ (by decide))
    (registerLookupWmi σ b _ (by decide)) (registerLookupWmi σ b _ (by decide))
    (registerLookupWmi σ b _ (by decide)) (registerLookupWmi σ b _ (by decide))

/-- Rocq `wfetch_site_wmi` (deviation 3: the text pins are FETCH pins). -/
theorem wfetchSiteWmi (tid : Option Nat) (σ : Wmstate) (root : BitVec 44) (va pa p2 p1 w0 lw : BitVec 64)
    (w : BitVec 32) (b : Bool) :
    let vpn := WeakKpt.svpnOf va
    let la := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)
    wwalkExports tid (wmi σ b) root va pa p2 p1 w0 lw →
    σ.wmRegs .PC = va →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    is_aligned_paddr (.Physaddr pa) 4 = true →
    isRVC (Sail.BitVec.extractLsb w 15 0) = false →
    wfgateRegs σ.wmRegs pa →
    raccDisj la 8 pa 4 →
    accWf pa 4 →
    (∀ j : Nat, j < 4 → paZ (pa + BitVec.ofNat 64 j) ≠ 0) →
    (∀ j : Nat, j < 4 → fetchPinned σ (WeakInterp.accAddr pa j)) →
    (∀ j : Nat, j < 4 → wflatMem σ.wmImg σ.wmLog (pa + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    wfetchSite tid (wmi σ b) root va pa p2 p1 w0 lw w := by
  intro vpn la hexp hpc halv halp hnotRVC hgates hdisj haccp hW0 hpin hbytes
  exact ⟨(registerLookupWmi σ b .PC (by decide)).trans hpc, halv, halp, hnotRVC, hexp,
    wfgateRegsWmi σ b pa hgates, hdisj, haccp, hW0, hpin, hbytes⟩

/-- Rocq `winstr_site_wmi`: the decode premise owed off `tlb` AND off `minstret_increment`. -/
theorem winstrSiteWmi (σ : Wmstate) (b : Bool) (w : BitVec 32) (i : instruction) (F : Register → Bool) :
    (∀ t : ExecSt, (∀ r : Register, r ≠ .tlb → r ≠ .minstret_increment → t.regs r = σ.wmRegs r) →
      execEff (ext_decode w) t = some (i, t, [])) →
    (σ.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    wexecRegonly i F →
    F .hart_state = false →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    winstrSite (wmi σ b) w i F := by
  intro hdec hlpad hex hF hhart
  refine ⟨fun t hag => hdec t fun r hr hmi => (hag r hr).trans (registerLookupWmi σ b r hmi), ?_, hex, hF, ?_⟩
  · rw [registerLookupWmi σ b .elp (by decide)]; exact hlpad
  · rw [registerLookupWmi σ b .hart_state (by decide)]; exact hhart

end Weak
