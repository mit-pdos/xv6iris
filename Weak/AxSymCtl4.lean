/-
Weak: **THE FETCH'S READ COUNT at the S-mode kernel regime** (`AxSpineOk6.ctrlOkS`) and the
counting spine instance `spineCntS`.

Rocq: `iris/AxSymCtl4.v` @ xxvzwolszwmp.

## The Rocq header, in substance

The `execA` proofs of `AxSpineOk3`/`AxSpineOk4`/`AxSpineOk6` carry no read count, so the fetch
chain is REPLAYED at `AxSymCtl.cntA` (same scripts, the `execA` facts reused):
§1 the kit in the scripts' shape (`cARSeq`/`cARBindN`/`cASeq0'`/…, `cARUntilMT1`); `rf1`
   (exactly one graph read per successful path) and `cntAReadRamPlain` = 1.
§2 `cntCheckedMemRead{2,4,8}`, `cntReadPteS` = 1, `cntPtReadPteSlot` = 1,
   `cntMemReadFetch{2,4}S`.
§3 the Sv39 walk: `cntRecWalkLeaf` = 1, `cntRecWalkL1` = 2, `cntPtWalkUser` = 3,
   `cntTranslateTLBMissUser` = 3.
§4 `cntTranslateTLBHitPt` = 0; `cntTranslateAddrPtFront`; `cntTranslateAddrImg`: EXACT
   translation — TLB hit (`tlbHitv` of the pc's direct-mapped slot) ⇒ state unchanged, 0 reads;
   miss (empty or foreign slot) ⇒ slot filled (`AxSymCtl4.tlbFill`), 3 reads.
§5 `cntFetchRVC{4,2}SGen`: the fetch's count from the translation's.
§6 `fcntS rs pc`; `scFetchS` (the counting fetch field, for every regime state, with the page
   warm after the fetch: `tlbHitvFill`); `scTickS` (`tick_clock` keeps `tlb`;
   `AxSpineOk7.sptTickS` replayed with the stronger post `tickPost'`); `spineCntS` (premises: the
   three static satp facts only).

## Deviations from Rocq

1. O2 STAGE C COUNTS (`AxSymCtl` deviation 1, `AxSymCtlb` deviation 1).  `cntA` counts GRAPH
   reads only: the instruction fetch's RAM read (`Read_ifetch`, `AK_ifetch`) is the pinned admin
   step and counts 0; PTE reads (`Read_ttw`) and plain reads count 1.  Concretely:
   * `cntCheckedMemRead{2,4,8}` conclude `= AxSymCtl4.accCnt acc` (0 for `InstructionFetch`, 1
     otherwise; Rocq: 1 for every class, its model reading `Read_plain` always);
   * `cntMemReadFetch2S` / `cntMemReadFetch4S` conclude `= 0` (Rocq `= 1`);
   * `cntFetchRVC4SGen` / `cntFetchRVC2SGen` conclude `cntA (fetch ()) s = ntr` (Rocq `ntr + 1`);
   * `fcntS rs pc := if tlbHitv (rs .tlb) (svpnOf pc) then 0 else 3` (Rocq 1 / 4).  So
     `scFetchS`'s warm clause says the page counts 0 afterwards (Rocq 1).
   The walk counts (1/2/3), the TLB-hit 0 and the translation's 0/3 are Rocq's.  `rf1`'s read
   arm additionally demands `akIfetch = false` (the one read is a graph read).
2. THE PINS (`AxRunClose` deviation 1): `seip_reg` ↦ `AxRunClose.pinReg` (`rf1`, `rfFReadReg`).
   The Ltac `nseip` is dropped (pin tests decided, `AxSpineOk3` deviation 5).
3. THE PROOF METHOD.  Rocq replays each `execA` script step by step with `cAR_seq`/`cA_bindN`/….
   The kit is ported, but most Lean replays run one `simp` over the Lean-only UNCONDITIONAL bind
   rules `AxSymCtl4.cntABind` / `AxSymCtl4.cntARBind` (`cntA (m >>= f) s = cntA m s + match
   execA m s with …`) together with the `execA` kit and facts, exactly as the `AxSpineOk3/4`
   scripts (tactic `ax_sym_ctl4_run` = `AxSpineOk4.ax_spine4_run` with the count rules and the
   register-only callees at count 0, `AxSymCtl4.cnt<Callee>` = `cntARfF` instances).  The three
   Rocq `cmrN_*` sections are instances of the Lean-only `AxSymCtl4.cntCheckedMemRead` (as
   `AxSpineOk3` deviation 1); `read_pte`/`mem_read` go through `AxSymCtl4.cntMemReadPriv` /
   `AxSymCtl4.cntMemReadFetchOfChecked`, `fetch_bytes` through `AxSymCtl4.cntFetchBytesOk`.
4. SPELLING / SHAPES as `AxSpineOk3`/`AxSpineOk4`/`AxSpineOk6` (deviations 1–2/1–7/1–6): `mword`
   ↦ `BitVec`, `register_lookup r s.(sregs)` ↦ `s.regs r`, `vec_access_dec` ↦ `[·]!`,
   `vec_update_dec` ↦ `vectorUpdate`, `tlb_hash (__id 39)` ↦ `tlb_hash 39`, `mword_of_int 0` ↦
   `0#16`, `svpn_of` ↦ `WeakKpt.svpnOf`, `u_walk_entry` ↦ `uWalkEntry`, the PTE/slot/satp/front
   premises in those files' Lean shapes, `MState r m d` ↦ `⟨r, m, d⟩`.  Rocq's well-founded
   `Acc` argument of the level-0/1 walk lemmas is gone (Lean `pt_walk`, `AxSpineOk4` deviation 2).
   `cntAReadRamPlain` takes `BytesAt` (Rocq: an `exec` fact for `read_ram`; `execAReadRamPlain`'s
   shape) and drops `0 ≤ n`.  `cAR_untilMT_1` ↦ `cARUntilMT1` over `untilFuelM 1` (no measure).
5. `cntTranslateAddrImg`'s exact post-state uses `tlbHitv` / `AxSymCtl4.tlbFill` (Lean's
   `execATranslateAddrImg` only gives "unchanged or filled"; the exact `execA` equation is
   re-proved here from the `AxSpineOk4` pieces).  `tlb_fill`'s unused section variables
   `acc p` are not parameters.
6. Section variables (`σi T satp0`, `Hmode Hasid Hppn`) are explicit arguments; the Rocq
   section Ltacs `ev_step`/`ev_go`/`ev_use` are not redeclared (`AxSymEngine2.ax_sym2_ev_go`,
   `evFactUse`, `evFactQ` and the `AxSpineOk7` Lean-only kit, as `AxSpineOk7` deviation 2).
   `SpineCnt_S`'s Rocq `sc_pos` obligation is not a field (`AxSymCtlb` deviation 2).

**Rocq → Lean name map.**  `cAR_seq` `cARSeq`, `cAR_seq'` `cARSeq'`, `cA_seq0'` `cASeq0'`,
`rfF_read_reg` `rfFReadReg`, `cAR_seqN` `cARSeqN`, `cAR_bindN` `cARBindN`, `cAR_bind0`
`cARBind0`, `cA_bindN` `cABindN`, `cA_bind0` `cABind0`, `cA_seq0` `cASeq0`, `cAR_untilMT_1`
`cARUntilMT1`, `rf1` `rf1`, `cntA_rf1` `cntARf1`, `cntA_read_ram_plain` `cntAReadRamPlain`,
`cnt_checked_mem_read_{2,4,8}` `cntCheckedMemRead{2,4,8}`, `cnt_read_pte_S` `cntReadPteS`,
`cnt_pt_read_pte_slot` `cntPtReadPteSlot`, `cnt_mem_read_fetch_{2,4}_S` `cntMemReadFetch{2,4}S`,
`cnt_rec_walk_leaf` `cntRecWalkLeaf`, `cnt_rec_walk_l1` `cntRecWalkL1`, `cnt_pt_walk_user`
`cntPtWalkUser`, `cnt_translate_TLB_miss_user` `cntTranslateTLBMissUser`,
`cnt_translate_TLB_hit_pt` `cntTranslateTLBHitPt`, `cnt_translateAddr_pt_front`
`cntTranslateAddrPtFront`, `tlb_hitv` `tlbHitv`, `tlb_fill` `AxSymCtl4.tlbFill` (duplicated
name: also AxWalk3), `cnt_translateAddr_img` `cntTranslateAddrImg`, `tlb_hitv_fill`
`tlbHitvFill`, `cnt_fetch_RVC_{4,2}_S_gen` `cntFetchRVC{4,2}SGen`, `fcnt_S` `fcntS`,
`sc_fetch_S` `scFetchS`, `tick_post'` `tickPost'`, `sc_tick_S` `scTickS`, `tlb_hitv_ag`
`tlbHitvAg`, `SpineCnt_S` `spineCntS`.  Lean-only (file-qualified `AxSymCtl4.*`): `cntABind`,
`cntARBind`, `cntAReadRam`, `cntAReadRamIfetch`, `accCnt`, `cntAAssertTrue`,
`cntCheckedMemRead`, `cntMemReadPriv`, `cntMemReadFetchOfChecked`, `cntIte`, `cntPteIsInvalid`,
`cntCheckLeafPte`, `cntAddToTLB`, `cntLookupTLB`, `cntCheckPTEPermission`, `cntTlbGetPbmt`,
`cntEffectivePrivilege`, `cntIsShadowStackAccess`, `cntTranslationMode`, `cntGetSatp`,
`cntSatpModeWidthForwards`, `cntFetchBytesOk`, `cntCurrentlyEnabledZiccif`,
`cntCurrentlyEnabledZca`; tactic `ax_sym_ctl4_run`.

**Dropped:** the Ltacs `nseip`, `ev_step`, `ev_go`, `ev_use` (deviations 2, 6).  Rocq 39
definitions/lemmas + 4 Ltacs; Lean 39 + 24 Lean-only + 1 tactic.
**Not ported:** the `Print Assumptions` line (the lint's axiom check covers it).
-/
import Weak.AxSymCtlb
import Weak.AxSpineOk7

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 1. The counting kit, in the shape of the `execA` scripts -/

/-- (Lean-only) THE UNCONDITIONAL BIND RULE of the count: the head's reads, then (if the head
runs) the continuation's. -/
theorem AxSymCtl4.cntABind {X Y : Type} (m : SailM X) (f : X → SailM Y) :
    ∀ s, cntA (m >>= f) s = cntA m s +
      (match execA m s with
       | some (x, s1) => cntA (f x) s1
       | none => 0) := by
  induction m with
  | pure x =>
    intro s
    show cntA (f x) s = 0 + cntA (f x) s
    rw [Nat.zero_add]
  | impure call k ih =>
    intro s
    cases call with
    | error e => rfl
    | ok o =>
      show cntA (FreeM.impure (.ok o) (fun v => k v >>= f)) s = _
      cases o
      case regRead r =>
        by_cases hr : AxRunClose.pinReg r
        · simp only [cntA, execA, hr, ↓reduceIte]
        · simp only [cntA, execA, hr, ↓reduceIte]; exact ih _ _
      case regWrite r v' =>
        by_cases hr : AxRunClose.pinReg r
        · simp only [cntA, execA, hr, ↓reduceIte]
        · simp only [cntA, execA, hr, ↓reduceIte]; exact ih _ _
      case memRead n va req =>
        cases hm : ramOk req.pa req.access_kind n
        · simp only [cntA, execA, hm, Bool.false_eq_true, ↓reduceIte]
        · cases hb : bmRead s.mem req.pa n with
          | none => simp only [cntA, execA, hm, hb, ↓reduceIte]
          | some w =>
            cases hfe : (classify req.access_kind).akIfetch
            · simp only [cntA, execA, hm, hb, hfe, ↓reduceIte, Bool.false_eq_true]
              rw [ih]
              omega
            · simp only [cntA, execA, hm, hb, hfe, ↓reduceIte]
              exact ih _ _
      case instrAnnounce n w =>
        cases hs : sfAnnB n w
        · simp only [cntA, execA, hs, Bool.false_eq_true, ↓reduceIte]; exact ih _ _
        · simp only [cntA, execA, hs, ↓reduceIte]
      all_goals first | rfl | exact ih _ _

/-- (Lean-only) The unconditional bind rule in the early-return monad. -/
theorem AxSymCtl4.cntARBind {R X Y : Type} (m : SailME R Y) (f : Y → SailME R X) (s : ExecSt) :
    cntAR (m >>= f) s = cntAR m s +
      (match execAR m s with
       | some (.inr a, s') => cntAR (f a) s'
       | _ => 0) := by
  unfold cntAR execAR
  rw [ExceptT.run_bind, AxSymCtl4.cntABind]
  congr 1
  rcases execA (ExceptT.run m) s with _ | ⟨e | a, s'⟩
  · rfl
  · rcases e with e | r <;> rfl
  · rfl

/-- Rocq `cAR_seq`. -/
theorem cARSeq {R X Y : Type} (m : SailM Y) (f : Y → SailME R X) (s s' : ExecSt) (x : Y) :
    rfF m → execA m s = some (x, s') → cntAR (liftM m >>= f) s = cntAR (f x) s' := by
  intro hrf h
  rw [cntARLiftRSeq _ _ _ _ _ h, cntARfF _ hrf, Nat.zero_add]

/-- Rocq `cAR_seq'`. -/
theorem cARSeq' {R X Y : Type} (m : SailM Y) (f : Y → SailME R X) (s s' : ExecSt) (x : Y) :
    execA m s = some (x, s') → rfF m → cntAR (liftM m >>= f) s = cntAR (f x) s' :=
  fun h hrf => cARSeq m f s s' x hrf h

/-- Rocq `cA_seq0'`. -/
theorem cASeq0' {X Y : Type} (m : SailM X) (f : X → SailM Y) (s : ExecSt) (v : X) (st : ExecSt) :
    execA m s = some (v, st) → rfF m → cntA (m >>= f) s = cntA (f v) st := by
  intro h hrf
  rw [cntABindSome _ _ _ _ _ h, cntARfF _ hrf, Nat.zero_add]

/-- Rocq `rfF_read_reg`. -/
theorem rfFReadReg (r : Register) : ¬ AxRunClose.pinReg r → rfF (readReg r) :=
  fun h => ⟨h, fun _ => True.intro⟩

/-- Rocq `cAR_seqN`. -/
theorem cARSeqN {R X Y : Type} (m : SailM Y) (f : Y → SailME R X) (s s' : ExecSt) (x : Y) (c : Nat) :
    execA m s = some (x, s') → cntA m s = c → cntAR (liftM m >>= f) s = c + cntAR (f x) s' := by
  intro h hc
  rw [cntARLiftRSeq _ _ _ _ _ h, hc]

/-- Rocq `cAR_bindN`. -/
theorem cARBindN {R X Y : Type} (m : SailME R Y) (f : Y → SailME R X) (s : ExecSt) (a : Y)
    (s' : ExecSt) (c : Nat) :
    execAR m s = some (.inr a, s') → cntAR m s = c → cntAR (m >>= f) s = c + cntAR (f a) s' := by
  intro h hc
  rw [cntARBindSome _ _ _ _ _ h, hc]

/-- Rocq `cAR_bind0`. -/
theorem cARBind0 {R X Y : Type} (m : SailME R Y) (f : Y → SailME R X) (s : ExecSt) (a : Y)
    (s' : ExecSt) :
    execAR m s = some (.inr a, s') → cntAR m s = 0 → cntAR (m >>= f) s = cntAR (f a) s' := by
  intro h hc
  rw [cntARBindSome _ _ _ _ _ h, hc, Nat.zero_add]

/-- Rocq `cA_bindN`. -/
theorem cABindN {X Y : Type} (m : SailM X) (f : X → SailM Y) (s : ExecSt) (v : X) (st : ExecSt)
    (c : Nat) : execA m s = some (v, st) → cntA m s = c → cntA (m >>= f) s = c + cntA (f v) st := by
  intro h hc
  rw [cntABindSome _ _ _ _ _ h, hc]

/-- Rocq `cA_bind0`. -/
theorem cABind0 {X Y : Type} (m : SailM X) (f : X → SailM Y) (s : ExecSt) (v : X) (st : ExecSt) :
    execA m s = some (v, st) → cntA m s = 0 → cntA (m >>= f) s = cntA (f v) st := by
  intro h hc
  rw [cntABindSome _ _ _ _ _ h, hc, Nat.zero_add]

/-- Rocq `cA_seq0`. -/
theorem cASeq0 {X Y : Type} (m : SailM X) (f : X → SailM Y) (s : ExecSt) (v : X) (st : ExecSt) :
    rfF m → execA m s = some (v, st) → cntA (m >>= f) s = cntA (f v) st :=
  fun hrf h => cABind0 m f s v st h (cntARfF _ hrf s)

/-- Rocq `cAR_untilMT_1` (`AxSpineOk` deviation 5: lean-sail `untilFuelM 1`). -/
theorem cARUntilMT1 {R Vars : Type} (vars vars' : Vars) (cond : Vars → SailME R Bool)
    (body : Vars → SailME R Vars) (s s' : ExecSt) :
    execAR (body vars) s = some (.inr vars', s') →
    execAR (cond vars') s' = some (.inr true, s') →
    cntAR (untilFuelM 1 cond vars body) s = cntAR (body vars) s + cntAR (cond vars') s' := by
  intro hb hc
  unfold untilFuelM untilFuelM.go
  rw [cntARBindSome _ _ _ _ _ hb]
  simp only []
  rw [cntARBindSome _ _ _ _ _ hc]
  show _ + (_ + 0) = _
  rw [Nat.add_zero]

/-- Rocq `rf1` (deviations: lean-sail outcomes; the one read is a GRAPH read, `akIfetch = false`,
Stage C). Exactly one graph read on every successful path, register-only otherwise. -/
def rf1 {X : Type} : SailM X → Prop
  | .pure _ => False
  | .impure (.error _) _ => True
  | .impure (.ok o) k =>
    match o, k with
    | .regRead r, k => ¬ AxRunClose.pinReg r ∧ ∀ v, rf1 (k v)
    | .regWrite r _, k => ¬ AxRunClose.pinReg r ∧ rf1 (k PUnit.unit)
    | .memRead _ _ req, k => (classify req.access_kind).akIfetch = false ∧ ∀ v, rfF (k v)
    | .memWrite .., _ => True
    | .barrier _, _ => True
    | .cacheOp _, k => rf1 (k ())
    | .tlbi _, k => rf1 (k ())
    | .translationStart _, k => rf1 (k ())
    | .translationEnd _, k => rf1 (k ())
    | .takeException _, k => rf1 (k ())
    | .returnException _, k => rf1 (k ())
    | .cycleCount, k => rf1 (k ())
    | .getCycleCount, k => rf1 (k (0 : Nat))
    | .message _, k => rf1 (k ())
    | .instrAnnounce _ _, k => rf1 (k ())
    | .branchAnnounce _ _, k => rf1 (k ())
    | .choose _, _ => True
    | .readRam .., _ => True
    | .writeRam .., _ => True

/-- Rocq `cntA_rf1`. -/
theorem cntARf1 {X : Type} (m : SailM X) : ∀ s x s', rf1 m → execA m s = some (x, s') → cntA m s = 1 := by
  induction m with
  | pure y => intro _ _ _ hrf; exact hrf.elim
  | impure call k ih =>
    intro s x s' hrf h
    cases call with
    | error e => cases h
    | ok o =>
      cases o
      case regRead r =>
        simp only [execA, hrf.1, ↓reduceIte] at h
        simp only [cntA, hrf.1, ↓reduceIte]
        exact ih _ _ _ _ (hrf.2 _) h
      case regWrite r v =>
        simp only [execA, hrf.1, ↓reduceIte] at h
        simp only [cntA, hrf.1, ↓reduceIte]
        exact ih _ _ _ _ hrf.2 h
      case memRead n va req =>
        simp only [execA] at h
        split at h
        · rename_i hok
          split at h
          · rename_i w hrb
            simp only [cntA, hok, hrb, hrf.1, ↓reduceIte, Bool.false_eq_true]
            rw [cntARfF _ (hrf.2 _)]
          · cases h
        · cases h
      case instrAnnounce n w =>
        simp only [execA] at h
        split at h
        · cases h
        · rename_i hs
          have hs' : sfAnnB n w = false := by simpa using hs
          simp only [cntA, hs', Bool.false_eq_true, ↓reduceIte]
          exact ih _ _ _ _ hrf h
      case barrier => cases h
      case memWrite => cases h
      case choose => cases h
      case readRam => cases h
      case writeRam => cases h
      all_goals exact ih _ _ _ _ hrf h

/-- (Lean-only) A GRAPH RAM read kind (`Read_plain` / `Read_ttw`; Stage C: `Read_ifetch` counts 0)
counts exactly one read. -/
theorem AxSymCtl4.cntAReadRam (rk : read_kind) (addr : BitVec 64) (n : Nat) (w : BitVec (8 * n))
    (s : ExecSt) (hrk : rk = .Read_plain ∨ rk = .Read_ttw)
    (hdev : devAddr addr = false) (hwf : paZ addr + n ≤ 2 ^ 64) (hb : BytesAt s addr n w) :
    cntA (read_ram rk (.Physaddr addr) n false) s = 1 := by
  refine cntARf1 _ s _ s ?_
    (AxSpineOk3.execAReadRam rk addr n w s (by rcases hrk with h | h <;> simp [h]) hdev hwf hb)
  rcases hrk with rfl | rfl <;>
  · simp only [read_ram, PreSail.sail_mem_read, PreSail.emit]
    refine ⟨rfl, fun v => ?_⟩
    rcases v with ⟨x, y⟩ | a <;> trivial

/-- (Lean-only) The i-fetch RAM read counts 0 (Stage C: an admin step, no row item). -/
theorem AxSymCtl4.cntAReadRamIfetch (addr : BitVec 64) (n : Nat) (s : ExecSt) :
    cntA (read_ram .Read_ifetch (.Physaddr addr) n false) s = 0 := by
  simp only [read_ram, PreSail.sail_mem_read, PreSail.emit, AxSymCtl4.cntABind, execABind,
    cntAReturnm, execAReturnm, Nat.zero_add]
  simp only [cntA, execA, classify, akIfetch, ↓reduceIte]
  repeat' split
  all_goals first | rfl | (rename_i w _ _; rcases w with ⟨x, y⟩ <;> rfl)

/-- Rocq `cntA_read_ram_plain` (`execAReadRamPlain`'s premises). -/
theorem cntAReadRamPlain (addr : BitVec 64) (n : Nat) (w : BitVec (8 * n)) (s : ExecSt)
    (hdev : devAddr addr = false) (hwf : paZ addr + n ≤ 2 ^ 64) (hb : BytesAt s addr n w) :
    cntA (read_ram .Read_plain (.Physaddr addr) n false) s = 1 :=
  AxSymCtl4.cntAReadRam .Read_plain addr n w s (Or.inl rfl) hdev hwf hb

/-! # 2. `checked_mem_read` (widths 2/4/8), `read_pte`, the fetch's `mem_read` -/

/-- (Lean-only) The graph reads of one checked RAM piece by access class (Stage C): an
instruction fetch reads no graph item, every other class one. -/
def AxSymCtl4.accCnt (acc : MemoryAccessType mem_payload) : Nat :=
  match acc with
  | .InstructionFetch _ => 0
  | _ => 1

theorem AxSymCtl4.cntAAssertTrue (msg : String) (s : ExecSt) :
    cntA (assert true msg : SailM Unit) s = 0 := rfl

/-- (Lean-only) The common core of Rocq `cnt_checked_mem_read_{2,4,8}`. -/
theorem AxSymCtl4.cntCheckedMemRead (acc : MemoryAccessType mem_payload)
    (pbmt : page_based_mem_type) (addr : BitVec 64) (n : Nat) (s : ExecSt) (hn : vmemWidth n)
    (hcp : execA (check_pma_with_pmp_priority acc pbmt .Supervisor (.Physaddr addr) n false) s
      = some (.Ok pmaOkAligned, s))
    (hpmp : execA (pmpCheck (.Physaddr addr) n acc .Supervisor) s = some (none, s))
    (hmm : execA (within_mmio_readable (.Physaddr addr) n) s = some (false, s))
    (hdev : devAddr addr = false) (hwf : paZ addr + n ≤ 2 ^ 64)
    (w : BitVec (8 * n)) (hb : BytesAt s addr n w) :
    cntA (checked_mem_read acc pbmt .Supervisor (.Physaddr addr) n false false false false) s
      = AxSymCtl4.accCnt acc := by
  have hrr : ∀ rk, (rk = .Read_plain ∨ rk = .Read_ifetch ∨ rk = .Read_ttw) →
      execA (read_ram rk (.Physaddr addr) n false) s = some ((w, default_meta), s) :=
    fun rk hrk => AxSpineOk3.execAReadRam rk addr n w s hrk hdev hwf hb
  have hsp : ∀ g, execA (split_misaligned (.Physaddr addr) n g .CannotSplit) s
      = some (((1 : Int), (n : Int)), s) := fun _ => rfl
  have hspc : ∀ g, cntA (split_misaligned (.Physaddr addr) n g .CannotSplit) s = 0 := fun _ => rfl
  have hcpc := cntARfF _ (rfFCheckPmaWithPmpPriority acc pbmt .Supervisor (.Physaddr addr) n false) s
  have hpmpc := cntARfF _ (rfFPmpCheck (.Physaddr addr) n acc .Supervisor) s
  have hmmc := cntARfF _ (rfFWithinMmioReadable (.Physaddr addr) n) s
  have hrP := hrr _ (Or.inl rfl)
  have hrI := hrr _ (Or.inr (Or.inl rfl))
  have hrT := hrr _ (Or.inr (Or.inr rfl))
  have hcP := AxSymCtl4.cntAReadRam .Read_plain addr n w s (Or.inl rfl) hdev hwf hb
  have hcT := AxSymCtl4.cntAReadRam .Read_ttw addr n w s (Or.inr rfl) hdev hwf hb
  have hcI := AxSymCtl4.cntAReadRamIfetch addr n s
  rcases hn with rfl | rfl | rfl | rfl <;>
  · unfold checked_mem_read
    rw [cntACatchEarlyReturn]
    simp only [AxSymCtl4.cntARBind, execARBind, cntARLiftR, execARLiftR, hcp, hcpc,
      cntARReturnR, execARReturnRFwd, pmaOkAligned, hsp, hspc, untilFuelM,
      untilFuelM.go, misaligned_order, bits_of_physaddr, Int.reduceToNat, Int.reduceMul,
      Int.reduceAdd, Int.reduceSub, Int.cast_ofNat_Int,
      Int.zero_mul, addIntZero, execAAssertExpTrue, AxSymCtl4.cntAAssertTrue, Int.toNat_one,
      sys_misaligned_order_decreasing, ↓reduceIte, Bool.false_eq_true,
      Int.mul_one, Int.zero_mul, Nat.zero_add, Nat.add_zero]
    cases acc <;> (try (rename_i p; cases p)) <;>
    simp only [AxSymCtl4.cntARBind, execARBind, cntARLiftR, execARLiftR, cntARReturnR,
      execARReturnRFwd, read_kind_of_flags, execAReturnM, cntAReturnm, hpmp, hpmpc,
      hmm, hmmc, hrP, hrI, hrT, hcP, hcI, hcT, ↓reduceIte, Bool.false_eq_true, beq_self_eq_true,
      Nat.zero_add, Nat.add_zero, AxSymCtl4.accCnt]

/-- Rocq `cnt_checked_mem_read_2` (deviation: `= AxSymCtl4.accCnt acc`). -/
theorem cntCheckedMemRead2 (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type)
    (addr : BitVec 64) (s : ExecSt)
    (hcp : execA (check_pma_with_pmp_priority acc pbmt .Supervisor (.Physaddr addr) 2 false) s
      = some (.Ok pmaOkAligned, s))
    (hpmp : execA (pmpCheck (.Physaddr addr) 2 acc .Supervisor) s = some (none, s))
    (hmm : execA (within_mmio_readable (.Physaddr addr) 2) s = some (false, s))
    (hdev : devAddr addr = false) (hwf : paZ addr + 2 ≤ 2 ^ 64) (w : BitVec 16)
    (hb : BytesAt s addr 2 w) :
    cntA (checked_mem_read acc pbmt .Supervisor (.Physaddr addr) 2 false false false false) s
      = AxSymCtl4.accCnt acc :=
  AxSymCtl4.cntCheckedMemRead acc pbmt addr 2 s (by simp [vmemWidth]) hcp hpmp hmm hdev hwf w hb

/-- Rocq `cnt_checked_mem_read_4` (deviation: `= AxSymCtl4.accCnt acc`). -/
theorem cntCheckedMemRead4 (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type)
    (addr : BitVec 64) (s : ExecSt)
    (hcp : execA (check_pma_with_pmp_priority acc pbmt .Supervisor (.Physaddr addr) 4 false) s
      = some (.Ok pmaOkAligned, s))
    (hpmp : execA (pmpCheck (.Physaddr addr) 4 acc .Supervisor) s = some (none, s))
    (hmm : execA (within_mmio_readable (.Physaddr addr) 4) s = some (false, s))
    (hdev : devAddr addr = false) (hwf : paZ addr + 4 ≤ 2 ^ 64) (w : BitVec 32)
    (hb : BytesAt s addr 4 w) :
    cntA (checked_mem_read acc pbmt .Supervisor (.Physaddr addr) 4 false false false false) s
      = AxSymCtl4.accCnt acc :=
  AxSymCtl4.cntCheckedMemRead acc pbmt addr 4 s (by simp [vmemWidth]) hcp hpmp hmm hdev hwf w hb

/-- Rocq `cnt_checked_mem_read_8` (deviation: `= AxSymCtl4.accCnt acc`). -/
theorem cntCheckedMemRead8 (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type)
    (addr : BitVec 64) (s : ExecSt)
    (hcp : execA (check_pma_with_pmp_priority acc pbmt .Supervisor (.Physaddr addr) 8 false) s
      = some (.Ok pmaOkAligned, s))
    (hpmp : execA (pmpCheck (.Physaddr addr) 8 acc .Supervisor) s = some (none, s))
    (hmm : execA (within_mmio_readable (.Physaddr addr) 8) s = some (false, s))
    (hdev : devAddr addr = false) (hwf : paZ addr + 8 ≤ 2 ^ 64) (w : BitVec 64)
    (hb : BytesAt s addr 8 w) :
    cntA (checked_mem_read acc pbmt .Supervisor (.Physaddr addr) 8 false false false false) s
      = AxSymCtl4.accCnt acc :=
  AxSymCtl4.cntCheckedMemRead acc pbmt addr 8 s (by simp [vmemWidth]) hcp hpmp hmm hdev hwf w hb

/-- (Lean-only) `mem_read_priv` of a plain one-piece read counts its `checked_mem_read`. -/
theorem AxSymCtl4.cntMemReadPriv (acc : MemoryAccessType mem_payload)
    (pbmt : page_based_mem_type) (priv : Privilege) (addr : BitVec 64) (n : Nat)
    (w : BitVec (8 * n)) (s : ExecSt) (c : Nat)
    (h : execA (checked_mem_read acc pbmt priv (.Physaddr addr) n false false false false) s =
      some (.Ok (w, default_meta), s))
    (hc : cntA (checked_mem_read acc pbmt priv (.Physaddr addr) n false false false false) s = c) :
    cntA (mem_read_priv acc pbmt priv (.Physaddr addr) n false false false) s = c := by
  unfold mem_read_priv mem_read_priv_meta
  simp only [AxSymCtl4.cntABind, execABind, h, hc, cntAReturnm, execAReturnM, Nat.add_zero]

/-- Rocq `cnt_read_pte_S`. -/
theorem cntReadPteS (addr : BitVec 64) (region : PMA_Region) (w : BitVec 64) (s : ExecSt)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) addr.toNat
      (to_bits (l := 64) 8).toNat = .PMP_Match)
    (hR : (_get_Pmpcfg_ent_R (s.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 8 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 8 = true)
    (hpte : (override_PMA region.attributes .PBMT_PMA).supports_pte_read = true)
    (hc : exec (within_clint (.Physaddr addr) 8) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr addr) 8) s = some (false, s))
    (hh : exec (within_htif_readable (.Physaddr addr) 8) s = some (false, s))
    (hdev : devAddr addr = false) (hwf : paZ addr + 8 ≤ 2 ^ 64) (hb : BytesAt s addr 8 w) :
    cntA (read_pte (.Physaddr addr) 8) s = 1 := by
  have hpma := execPmaCheckRamPte addr .PBMT_PMA region false s hm hal hpte
  have hcp : exec (check_pma_with_pmp_priority (.Load .PageTableEntry) .PBMT_PMA .Supervisor
      (.Physaddr addr) 8 false) s = some (.Ok pmaOkAligned, s) := by
    unfold check_pma_with_pmp_priority
    exec_run [hpma]
  to_a hcp
  have hpmp := execPmpCheckSupervisorGrantLoad addr 8 s hA hlt hr hR
  to_a hpmp
  have hmm := execAMmioFalse addr 8 s hc hsig hh
  have hchk := execACheckedMemRead8 _ _ addr s hcp hpmp hmm hdev hwf w hb
  have hchkc := cntCheckedMemRead8 _ _ addr s hcp hpmp hmm hdev hwf w hb
  unfold read_pte
  exact AxSymCtl4.cntMemReadPriv _ _ _ addr 8 w s 1 hchk hchkc

/-- Rocq `cnt_pt_read_pte_slot` (`execAPtReadPteSlot`'s premises). -/
theorem cntPtReadPteSlot (sg : ExecSt) (a w : BitVec 64) (region : PMA_Region)
    (hslot : WeakWalkEff.ptSlotMem sg a w)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (sg.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (sg.regs .pmpaddr_n)[0]! = false)
    (hR : (_get_Pmpcfg_ent_R (sg.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hcov : ramEnd ≤ (sg.regs .pmpaddr_n)[0]!.toNat * 4)
    (hm : matching_pma_region (sg.regs .pma_regions) (.Physaddr a) 8 = some region)
    (hpte : (override_PMA region.attributes .PBMT_PMA).supports_pte_read = true)
    (hhtif : sg.regs .htif_tohost_base = none) :
    cntA (read_pte (.Physaddr a) 8) sg = 1 := by
  obtain ⟨hb, hram, hal⟩ := hslot
  have hz : (zeros (n := 64)).toNat = 0 := rfl
  have h8 : (to_bits (l := 64) 8).toNat = 8 := by decide
  have hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((sg.regs .pmpaddr_n)[0]!.toNat * 4) a.toNat
      (to_bits (l := 64) 8).toNat = .PMP_Match := by
    rw [hz, h8]
    exact pmpRangeMatch_full _ _ _ _ (Nat.zero_le _) (by decide) (by have := hram.2; omega)
  have hwf : paZ a + 8 ≤ 2 ^ 64 := by
    have := hram.2
    unfold ramEnd at this
    unfold paZ
    omega
  exact cntReadPteS a region w sg hA hlt hr hR hm hal hpte (execWithinClintRam a 8 sg hram)
    (execWithinSigFalse a 8 sg) (execWithinHtifNone a 8 sg hhtif) (devAddrRam a 8 hram) hwf hb

/-- (Lean-only) The fetch's `mem_read` counts its `checked_mem_read`, in S-mode. -/
theorem AxSymCtl4.cntMemReadFetchOfChecked (pbmt : page_based_mem_type) (pa : BitVec 64)
    (n : Nat) (w : BitVec (8 * n)) (s : ExecSt) (c : Nat) (hcp : s.regs .cur_privilege = .Supervisor)
    (h : execA (checked_mem_read (.InstructionFetch ()) pbmt .Supervisor (.Physaddr pa) n false false
      false false) s = some (.Ok (w, default_meta), s))
    (hc : cntA (checked_mem_read (.InstructionFetch ()) pbmt .Supervisor (.Physaddr pa) n false false
      false false) s = c) :
    cntA (mem_read (.InstructionFetch ()) pbmt (.Physaddr pa) n false false false) s = c := by
  have hep := execEffectivePrivilegeFetch (s.regs .mstatus) (s.regs .cur_privilege) s
  to_a hep
  have hm : ¬ AxRunClose.pinReg .mstatus := by simp [AxRunClose.pinReg]
  have hcu : ¬ AxRunClose.pinReg .cur_privilege := by simp [AxRunClose.pinReg]
  unfold mem_read
  rw [cASeq0' _ _ _ _ _ (execAReadReg .mstatus s hm) (rfFReadReg _ hm),
    cASeq0' _ _ _ _ _ (execAReadReg .cur_privilege s hcu) (rfFReadReg _ hcu),
    cASeq0' _ _ _ _ _ hep (rfFEffectivePrivilege _ _ _), hcp]
  exact AxSymCtl4.cntMemReadPriv _ _ _ pa n w s c h hc

/-- Rocq `cnt_mem_read_fetch_2_S` (Stage C: the i-fetch read counts 0; Rocq 1). -/
theorem cntMemReadFetch2S (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (w : BitVec 16) (s : ExecSt)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) addr.toNat
      (to_bits (l := 64) 2).toNat = .PMP_Match)
    (hX : (_get_Pmpcfg_ent_X (s.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 2 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 2 = true)
    (hx : (override_PMA region.attributes pbmt).executable = true)
    (hc : exec (within_clint (.Physaddr addr) 2) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr addr) 2) s = some (false, s))
    (hh : exec (within_htif_readable (.Physaddr addr) 2) s = some (false, s))
    (hdev : devAddr addr = false) (hwf : paZ addr + 2 ≤ 2 ^ 64) (hb : BytesAt s addr 2 w)
    (hpriv : s.regs .cur_privilege = .Supervisor) :
    cntA (mem_read (.InstructionFetch ()) pbmt (.Physaddr addr) 2 false false false) s = 0 := by
  have hpma := execPmaCheckRam2 addr pbmt region s hm hal hx
  have hcp : exec (check_pma_with_pmp_priority (.InstructionFetch ()) pbmt .Supervisor
      (.Physaddr addr) 2 false) s = some (.Ok pmaOkAligned, s) := by
    unfold check_pma_with_pmp_priority
    exec_run [hpma]
  to_a hcp
  have hpmp := execPmpCheckSupervisorGrant addr 2 s hA hlt hr hX
  to_a hpmp
  have hmm := execAMmioFalse addr 2 s hc hsig hh
  exact AxSymCtl4.cntMemReadFetchOfChecked pbmt addr 2 w s 0 hpriv
    (execACheckedMemRead2 _ _ addr s hcp hpmp hmm hdev hwf w hb)
    (cntCheckedMemRead2 _ _ addr s hcp hpmp hmm hdev hwf w hb)

/-- Rocq `cnt_mem_read_fetch_4_S` (Stage C: the i-fetch read counts 0; Rocq 1). -/
theorem cntMemReadFetch4S (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (w : BitVec 32) (s : ExecSt)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) addr.toNat
      (to_bits (l := 64) 4).toNat = .PMP_Match)
    (hX : (_get_Pmpcfg_ent_X (s.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hx : (override_PMA region.attributes pbmt).executable = true)
    (hc : exec (within_clint (.Physaddr addr) 4) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr addr) 4) s = some (false, s))
    (hh : exec (within_htif_readable (.Physaddr addr) 4) s = some (false, s))
    (hdev : devAddr addr = false) (hwf : paZ addr + 4 ≤ 2 ^ 64) (hb : BytesAt s addr 4 w)
    (hpriv : s.regs .cur_privilege = .Supervisor) :
    cntA (mem_read (.InstructionFetch ()) pbmt (.Physaddr addr) 4 false false false) s = 0 := by
  have hpma := execPmaCheckRam addr pbmt region s hm hal hx
  have hcp : exec (check_pma_with_pmp_priority (.InstructionFetch ()) pbmt .Supervisor
      (.Physaddr addr) 4 false) s = some (.Ok pmaOkAligned, s) := by
    unfold check_pma_with_pmp_priority
    exec_run [hpma]
  to_a hcp
  have hpmp := execPmpCheckSupervisorGrant addr 4 s hA hlt hr hX
  to_a hpmp
  have hmm := execAMmioFalse addr 4 s hc hsig hh
  exact AxSymCtl4.cntMemReadFetchOfChecked pbmt addr 4 w s 0 hpriv
    (execACheckedMemRead4 _ _ addr s hcp hpmp hmm hdev hwf w hb)
    (cntCheckedMemRead4 _ _ addr s hcp hpmp hmm hdev hwf w hb)

/-! # 3. The Sv39 walk: EXACTLY three reads (replay of `AxSpineOk4`) -/

/-- (Lean-only) `cntA` of an `if` is the `if` of the counts. -/
theorem AxSymCtl4.cntIte {X : Type} (c : Prop) [Decidable c] (a b : SailM X) (s : ExecSt) :
    cntA (if c then a else b) s = if c then cntA a s else cntA b s := by
  split <;> rfl

/-! (Lean-only) the register-only callees count 0 (`cntARfF` instances, for the simp set). -/
theorem AxSymCtl4.cntPteIsInvalid (f : BitVec 8) (e : BitVec 10) (s : ExecSt) :
    cntA (pte_is_invalid f e) s = 0 := cntARfF _ (rfFPteIsInvalid _ _) s
theorem AxSymCtl4.cntCheckLeafPte (sv : Nat) (vpn : BitVec (sv - 12))
    (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr sum : Bool)
    (pte : BitVec (if (sv = 32 : Bool) then 32 else 64)) (pa : physaddr) (lvl : Nat) (x : Unit)
    (s : ExecSt) : cntA (check_leaf_pte sv vpn acc p mxr sum pte pa lvl x) s = 0 :=
  cntARfF _ (rfFCheckLeafPte _ _ _ _ _ _ _ _ _ _) s
theorem AxSymCtl4.cntAddToTLB (w : Nat) (asid : BitVec 16) (vpn : BitVec (w - 12))
    (ppn : BitVec (if (w = 32 : Bool) then 22 else 44))
    (pte : BitVec (if (w = 32 : Bool) then 32 else 64)) (pa : physaddr) (lvl : Nat) (g : Bool)
    (s : ExecSt) : cntA (add_to_TLB w asid vpn ppn pte pa lvl g) s = 0 :=
  cntARfF _ (rfFAddToTLB _ _ _ _ _ _ _ _) s
theorem AxSymCtl4.cntLookupTLB (w : Nat) (asid : BitVec 16) (vpn : BitVec (w - 12)) (s : ExecSt) :
    cntA (lookup_TLB w asid vpn) s = 0 := cntARfF _ (rfFLookupTLB _ _ _) s
theorem AxSymCtl4.cntCheckPTEPermission (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr sum : Bool) (f : BitVec 8) (e : BitVec 10) (x : Unit) (s : ExecSt) :
    cntA (check_PTE_permission acc p mxr sum f e x) s = 0 :=
  cntARfF _ (rfFCheckPTEPermission _ _ _ _ _ _ _) s
theorem AxSymCtl4.cntTlbGetPbmt (ent : TLB_Entry) (s : ExecSt) : cntA (tlb_get_pbmt ent) s = 0 :=
  cntARfF _ (rfFTlbGetPbmt _) s

/-- (Lean-only) Rocq's `cbn`/`rewrite cA_bindN` steps: `ax_spine4_run` with the count's bind
rules. -/
syntax "ax_sym_ctl4_run" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| ax_sym_ctl4_run) => `(tactic| ax_spine4_run [AxSymCtl4.cntABind,
      AxSymCtl4.cntARBind, cntARLiftR, cntA, cntAReturnm, cntARReturnR, Nat.zero_add,
      Nat.add_zero, AxSymCtl4.cntIte, AxSymCtl4.cntPteIsInvalid, AxSymCtl4.cntCheckLeafPte,
      AxSymCtl4.cntAddToTLB, AxSymCtl4.cntLookupTLB, AxSymCtl4.cntCheckPTEPermission,
      AxSymCtl4.cntTlbGetPbmt])
  | `(tactic| ax_sym_ctl4_run [$ls,*]) => `(tactic| ax_spine4_run [AxSymCtl4.cntABind,
      AxSymCtl4.cntARBind, cntARLiftR, cntA, cntAReturnm, cntARReturnR, Nat.zero_add,
      Nat.add_zero, AxSymCtl4.cntIte, AxSymCtl4.cntPteIsInvalid, AxSymCtl4.cntCheckLeafPte,
      AxSymCtl4.cntAddToTLB, AxSymCtl4.cntLookupTLB, AxSymCtl4.cntCheckPTEPermission,
      AxSymCtl4.cntTlbGetPbmt, $ls,*])

set_option simprocs false in
/-- Rocq `cnt_rec_walk_leaf` (`AxSpineOk4` deviation 2: level 0 of Lean's `pt_walk`). -/
theorem cntRecWalkLeaf (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (pte1 pte0 : BitVec 64)
    (h0i : pteValid pte0) (h0nl : pteLeaf pte0) (hchk0 : pteCheckOk acc p mxr dosum pte0)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE pte0) == 1#1) = false)
    (g : Bool) (menvcfg0 : BitVec 64) (s : ExecSt)
    (hmisa : s.regs .misa = misaC)
    (hrd0 : execA (read_pte (.Physaddr (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok pte0, s))
    (hrd0c : cntA (read_pte (.Physaddr (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s = 1)
    (hmenv : s.regs .menvcfg = menvcfg0) (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true) :
    cntA (pt_walk 39 vpn acc p mxr dosum (uNextBase pte1) 0 g ()) s = 1 := by
  rw [pt_walk]
  ax_sym_ctl4_run
  erw [hrd0c, hrd0]
  ax_sym_ctl4_run
  erw [h0iA pte0 h0i s]
  ax_sym_ctl4_run [Functions.not, AxSpineOk4.execAIte]
  erw [execACheckLeafPteLeaf0 vpn acc p mxr dosum pte0 h0i h0nl hchk0 h0N _ menvcfg0 s hmisa hmenv
    hpbmte]
  rfl

set_option simprocs false in
/-- Rocq `cnt_rec_walk_l1` (`AxSpineOk4` deviation 2): level 1, two reads. -/
theorem cntRecWalkL1 (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (pte2 pte1 pte0 : BitVec 64)
    (h1i : pteValid pte1) (h1nl : ptePtr pte1)
    (h0i : pteValid pte0) (h0nl : pteLeaf pte0) (hchk0 : pteCheckOk acc p mxr dosum pte0)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE pte0) == 1#1) = false)
    (g : Bool) (menvcfg0 : BitVec 64) (s : ExecSt)
    (hmisa : s.regs .misa = misaC)
    (hrd1 : execA (read_pte (.Physaddr (uPteAddr (uNextBase pte2) (Sail.BitVec.extractLsb vpn 17 9))) 8) s =
      some (.Ok pte1, s))
    (hrd1c : cntA (read_pte (.Physaddr (uPteAddr (uNextBase pte2) (Sail.BitVec.extractLsb vpn 17 9))) 8) s = 1)
    (hrd0 : execA (read_pte (.Physaddr (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok pte0, s))
    (hrd0c : cntA (read_pte (.Physaddr (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s = 1)
    (hmenv : s.regs .menvcfg = menvcfg0) (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true) :
    cntA (pt_walk 39 vpn acc p mxr dosum (uNextBase pte2) 1 g ()) s = 2 := by
  rw [pt_walk]
  ax_sym_ctl4_run
  erw [hrd1c, hrd1]
  ax_sym_ctl4_run
  erw [h1iA pte1 h1i s]
  ax_sym_ctl4_run [Functions.not, AxSpineOk4.execAIte]
  erw [h1nl]
  ax_sym_ctl4_run [AxSpineOk4.execAIte]
  erw [cntRecWalkLeaf vpn acc p mxr dosum pte1 pte0 h0i h0nl hchk0 h0N _ menvcfg0 s hmisa hrd0 hrd0c
    hmenv hpbmte]

set_option simprocs false in
/-- Rocq `cnt_pt_walk_user`: the full three-level walk, three reads. -/
theorem cntPtWalkUser (vpn : BitVec 27) (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (root : BitVec 44) (pte2 pte1 pte0 : BitVec 64)
    (h2i : pteValid pte2) (h2nl : ptePtr pte2) (h1i : pteValid pte1) (h1nl : ptePtr pte1)
    (h0i : pteValid pte0) (h0nl : pteLeaf pte0) (hchk0 : pteCheckOk acc p mxr dosum pte0)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE pte0) == 1#1) = false)
    (menvcfg0 : BitVec 64) (s : ExecSt)
    (hmisa : s.regs .misa = misaC)
    (hrd2 : execA (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s =
      some (.Ok pte2, s))
    (hrd2c : cntA (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s = 1)
    (hrd1 : execA (read_pte (.Physaddr (uPteAddr (uNextBase pte2) (Sail.BitVec.extractLsb vpn 17 9))) 8) s =
      some (.Ok pte1, s))
    (hrd1c : cntA (read_pte (.Physaddr (uPteAddr (uNextBase pte2) (Sail.BitVec.extractLsb vpn 17 9))) 8) s = 1)
    (hrd0 : execA (read_pte (.Physaddr (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok pte0, s))
    (hrd0c : cntA (read_pte (.Physaddr (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s = 1)
    (hmenv : s.regs .menvcfg = menvcfg0) (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true) :
    cntA (pt_walk 39 vpn acc p mxr dosum root 2 false ()) s = 3 := by
  rw [pt_walk]
  ax_sym_ctl4_run
  erw [hrd2c, hrd2]
  ax_sym_ctl4_run
  erw [h2iA pte2 h2i s]
  ax_sym_ctl4_run [Functions.not, AxSpineOk4.execAIte]
  erw [h2nl]
  ax_sym_ctl4_run [AxSpineOk4.execAIte]
  erw [cntRecWalkL1 vpn acc p mxr dosum pte2 pte1 pte0 h1i h1nl h0i h0nl hchk0 h0N _ menvcfg0 s hmisa
    hrd1 hrd1c hrd0 hrd0c hmenv hpbmte]

/-- Rocq `cnt_translate_TLB_miss_user`: three reads. -/
theorem cntTranslateTLBMissUser (vpn : BitVec 27) (root : BitVec 44) (pte2 pte1 pte0 : BitVec 64)
    (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (h2i : pteValid pte2) (h2nl : ptePtr pte2) (h1i : pteValid pte1) (h1nl : ptePtr pte1)
    (h0i : pteValid pte0) (h0nl : pteLeaf pte0) (hchk0 : pteCheckOk acc p mxr dosum pte0)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE pte0) == 1#1) = false)
    (asid : BitVec 16) (menvcfg0 : BitVec 64) (s : ExecSt)
    (hmisa : s.regs .misa = misaC) (hnoupd : update_PTE_Bits pte0 acc = none)
    (hrd2 : execA (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s =
      some (.Ok pte2, s))
    (hrd2c : cntA (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s = 1)
    (hrd1 : execA (read_pte (.Physaddr (uPteAddr (uNextBase pte2) (Sail.BitVec.extractLsb vpn 17 9))) 8) s =
      some (.Ok pte1, s))
    (hrd1c : cntA (read_pte (.Physaddr (uPteAddr (uNextBase pte2) (Sail.BitVec.extractLsb vpn 17 9))) 8) s = 1)
    (hrd0 : execA (read_pte (.Physaddr (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok pte0, s))
    (hrd0c : cntA (read_pte (.Physaddr (uPteAddr (uNextBase pte1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s = 1)
    (hmenv : s.regs .menvcfg = menvcfg0) (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true) :
    cntA (translate_TLB_miss 39 asid root vpn acc p mxr dosum ()) s = 3 := by
  unfold translate_TLB_miss
  ax_sym_ctl4_run
  erw [cntPtWalkUser vpn acc p mxr dosum root pte2 pte1 pte0 h2i h2nl h1i h1nl h0i h0nl hchk0 h0N
    menvcfg0 s hmisa hrd2 hrd2c hrd1 hrd1c hrd0 hrd0c hmenv hpbmte,
    execAPtWalkUser vpn acc p mxr dosum root pte2 pte1 pte0 h2i h2nl h1i h1nl h0i h0nl hchk0 h0N
    menvcfg0 s hmisa hrd2 hrd1 hrd0 hmenv hpbmte]
  unfold uWalkOut update_and_write_pte
  ax_sym_ctl4_run
  erw [hnoupd]
  ax_sym_ctl4_run
  erw [execAAddToTLBUser]
  rfl

/-! # 4. The translation: 0 reads on a TLB HIT, 3 on a MISS -/

/-- Rocq `cnt_translate_TLB_hit_pt`. -/
theorem cntTranslateTLBHitPt (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (vpn : BitVec 27) (p2 p1 q0 : BitVec 64) (asid : BitVec 16) (idx : Nat) (s : ExecSt)
    (hchk : pteCheckOk acc p mxr dosum q0) (hupd : update_PTE_Bits q0 acc = none)
    (hpb : ptePbmt0 q0) :
    cntA (translate_TLB_hit 39 asid vpn acc p mxr dosum () idx (uWalkEntry vpn p2 p1 q0 asid)) s = 0 := by
  unfold translate_TLB_hit
  simp only [tlbGetPteUwe, tlbGetPpnUwe]
  ax_sym_ctl4_run
  erw [hchk0A acc p mxr dosum q0 hchk s]
  unfold update_and_write_pte
  ax_sym_ctl4_run
  erw [hupd]
  ax_sym_ctl4_run
  split <;> rfl

/-! (Lean-only) more register-only callees at count 0. -/
theorem AxSymCtl4.cntEffectivePrivilege (acc : MemoryAccessType mem_payload) (ms : BitVec 64)
    (p : Privilege) (s : ExecSt) : cntA (effectivePrivilege acc ms p) s = 0 :=
  cntARfF _ (rfFEffectivePrivilege _ _ _) s
theorem AxSymCtl4.cntIsShadowStackAccess (acc : MemoryAccessType mem_payload) (s : ExecSt) :
    cntA (is_shadow_stack_access acc) s = 0 := cntARfF _ (rfFIsShadowStackAccess _) s
theorem AxSymCtl4.cntTranslationMode (p : Privilege) (s : ExecSt) :
    cntA (translationMode p) s = 0 := cntARfF _ (rfFTranslationMode _) s
theorem AxSymCtl4.cntGetSatp (w : Nat) (s : ExecSt) : cntA (get_satp w) s = 0 :=
  cntARfF _ (rfFGetSatp _) s
theorem AxSymCtl4.cntSatpModeWidthForwards (m : SATPMode) (s : ExecSt) :
    cntA (satp_mode_width_forwards m) s = 0 := cntARfF _ (rfFSatpModeWidthForwards _) s

/-- Rocq `cnt_translateAddr_pt_front` (`AxSpineOk4` deviation 7's premise shapes). -/
theorem cntTranslateAddrPtFront (acc : MemoryAccessType mem_payload) (p : Privilege)
    (vpn : BitVec 27) (root ppnv : BitVec 44) (satp0 va pa : BitVec 64) (s s' : ExecSt) (c : Nat)
    (heff : exec (effectivePrivilege acc (s.regs .mstatus) p) s = some (p, s))
    (hss : exec (is_shadow_stack_access acc) s = some (false, s))
    (hcp : s.regs .cur_privilege = p)
    (htm : exec (translationMode p) s = some (.Sv39, s))
    (hsatp : s.regs .satp = satp0)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = root)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hcanon : (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false)
    (hvpn : BitVec.setWidth 27 (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb va 38 0) 38
      Functions.pagesize_bits) = vpn)
    (htr : ∀ mxr dosum, execA (translate 39 0#16 root vpn acc p mxr dosum ()) s =
      some (.Ok (ppnv, .PBMT_PMA, ()), s'))
    (htrc : ∀ mxr dosum, cntA (translate 39 0#16 root vpn acc p mxr dosum ()) s = c) :
    cntA (translateAddr (.Virtaddr va) acc) s = c := by
  have heffA := execAOfRfF _ (rfFEffectivePrivilege _ _ _) s _ heff
  have hssA := execAOfRfF _ (rfFIsShadowStackAccess _) s _ hss
  have htmA := execAOfRfF _ (rfFTranslationMode _) s _ htm
  have hw : execA (satp_mode_width_forwards .Sv39) s = some (39, s) := rfl
  have hgs : execA (get_satp 39) s = some (satp0, s) := by
    unfold get_satp
    ax_spine4_run [hsatp]
    show some (BitVec.setWidth 64 satp0, s) = _
    rw [BitVec.setWidth_eq]
  unfold translateAddr
  rw [cntACatchEarlyReturn]
  ax_sym_ctl4_run [hcp, heffA, htmA, hssA, hw, Int.reduceToNat, Int.reduceSub, hgs, bits_of_virtaddr,
    AxSymCtl4.cntEffectivePrivilege, AxSymCtl4.cntIsShadowStackAccess, AxSymCtl4.cntTranslationMode,
    AxSymCtl4.cntGetSatp, AxSymCtl4.cntSatpModeWidthForwards]
  erw [hgs]
  ax_sym_ctl4_run [hcanon]
  erw [hasid, hppn, hvpn, htrc, htr]
  ax_sym_ctl4_run
  erw [AxSymCtl4.cntGetSatp 39 s, Nat.zero_add]

/-- Rocq `tlb_hitv`: the pc's direct-mapped slot holds an entry matching its Sv39 page (ASID 0). -/
def tlbHitv (tlbvec : Vector (Option TLB_Entry) (2 ^ 6)) (vpn : BitVec 27) : Bool :=
  match tlbvec[tlb_hash 39 vpn]! with
  | some ent => match_TLB_Entry ent 0#16 (sign_extend (m := 57 - 12) vpn)
  | none => false

/-- Rocq `tlb_fill` (duplicated name: file-qualified). -/
def AxSymCtl4.tlbFill (σ : ExecSt) (tlbvec : Vector (Option TLB_Entry) (2 ^ 6)) (vpn : BitVec 27)
    (p2 p1 w : BitVec 64) : ExecSt :=
  σ.setReg .tlb (vectorUpdate tlbvec (tlb_hash 39 vpn) (some (uWalkEntry vpn p2 p1 w 0#16)))

/-- Rocq `cnt_translateAddr_img`: THE TRANSLATION, EXACTLY — TLB hit ⇒ state unchanged, 0
reads; miss ⇒ the slot is filled, 3 reads (the three PTE slots).  (Premises as
`execATranslateAddrImg`; the Rocq section variables `acc p` are arguments.) -/
theorem cntTranslateAddrImg (acc : MemoryAccessType mem_payload) (p : Privilege)
    (rootPpn : BitVec 44) (va w pa satp0 : BitVec 64) (t : PTree)
    (tlbvec : Vector (Option TLB_Entry) (2 ^ 6)) (p2 p1 : BitVec 64) (σ : ExecSt) :
    let vpn := WeakKpt.svpnOf va
    (∀ (mxr dosum : Bool), pteCheckOk acc p mxr dosum w) →
    update_PTE_Bits w acc = none →
    (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false →
    zero_extend (m := 64) (ppn0 w +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0) = pa →
    ptePbmt0 w →
    t.base = rootPpn →
    AxPtProt.ptreeMaps t vpn p2 p1 w →
    tlbExact t tlbvec →
    WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr2 t vpn) p2 →
    WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr1 p2 vpn) p1 →
    WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr0 p1 vpn) w →
    σ.regs .misa = misaC →
    σ.regs .menvcfg = menvcfgS →
    σ.regs .htif_tohost_base = none →
    σ.regs .cur_privilege = p →
    exec (translationMode p) σ = some (.Sv39, σ) →
    exec (effectivePrivilege acc (σ.regs .mstatus) p) σ = some (p, σ) →
    exec (is_shadow_stack_access acc) σ = some (false, σ) →
    σ.regs .satp = satp0 →
    BitVec.setWidth 44 (satp_to_ppn satp0) = rootPpn →
    zero_extend (m := 16) (satp_to_asid satp0) = 0#16 →
    σ.regs .tlb = tlbvec →
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (σ.regs .pmpcfg_n)[0]!) = .TOR →
    zopz0zKzJ_u (zeros (n := 64)) (σ.regs .pmpaddr_n)[0]! = false →
    (_get_Pmpcfg_ent_R (σ.regs .pmpcfg_n)[0]! == 1#1) = true →
    ramEnd ≤ (σ.regs .pmpaddr_n)[0]!.toNat * 4 →
    WeakKpt.pmaAllowsPteRead (σ.regs .pma_regions) →
    execA (translateAddr (.Virtaddr va) acc) σ =
        some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw),
          if tlbHitv tlbvec vpn then σ else AxSymCtl4.tlbFill σ tlbvec vpn p2 p1 w) ∧
      cntA (translateAddr (.Virtaddr va) acc) σ = if tlbHitv tlbvec vpn then 0 else 3 := by
  intro vpn hchk hupd hcanon hout hpb hbase hmaps htlbok hsm2 hsm1 hsm0 hmisa hmenv hhtif hcp htm
    heff hss hsatp hppn hasid htlb hA hord hR hcov hpmar
  obtain ⟨c1, c0, -, -, -, -, -, -, -, hv2, hn2, hv1, hn1, hv0, hl0, hnap, -⟩ := id hmaps
  have ha2 : AxPtProt.ptAddr2 t vpn = uPteAddr rootPpn (Sail.BitVec.extractLsb vpn 26 18) := by
    unfold AxPtProt.ptAddr2; rw [hbase]; rfl
  have hsm2' : WeakWalkEff.ptSlotMem σ (uPteAddr rootPpn (Sail.BitVec.extractLsb vpn 26 18)) p2 :=
    ha2 ▸ hsm2
  obtain ⟨region2, hm2, hs2⟩ := hpmar _ hsm2'.2.1
  obtain ⟨region1, hm1, hs1⟩ := hpmar _ hsm1.2.1
  obtain ⟨region0, hm0r, hs0⟩ := hpmar _ hsm0.2.1
  have hrd2 := execAPtReadPteSlot σ _ p2 region2 hsm2' hA hord hR hcov hm2 hs2 hhtif
  have hrd1 := execAPtReadPteSlot σ (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) p1
    region1 hsm1 hA hord hR hcov hm1 hs1 hhtif
  have hrd0 := execAPtReadPteSlot σ (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) w
    region0 hsm0 hA hord hR hcov hm0r hs0 hhtif
  have hrd2c := cntPtReadPteSlot σ _ p2 region2 hsm2' hA hord hR hcov hm2 hs2 hhtif
  have hrd1c := cntPtReadPteSlot σ (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) p1
    region1 hsm1 hA hord hR hcov hm1 hs1 hhtif
  have hrd0c := cntPtReadPteSlot σ (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) w
    region0 hsm0 hA hord hR hcov hm0r hs0 hhtif
  have hpbmte : (_get_MEnvcfg_PBMTE menvcfgS == 0#1) = true := by decide
  -- the miss path, shared by the empty and the foreign slot
  have hmiss : execA (lookup_TLB 39 0#16 vpn) σ = some (none, σ) →
      execA (translateAddr (.Virtaddr va) acc) σ =
          some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), AxSymCtl4.tlbFill σ tlbvec vpn p2 p1 w) ∧
        cntA (translateAddr (.Virtaddr va) acc) σ = 3 := by
    intro hlk
    have htr : ∀ mxr dosum, execA (translate 39 0#16 rootPpn vpn acc p mxr dosum ()) σ =
        some (.Ok (ppn0 w, .PBMT_PMA, ()), AxSymCtl4.tlbFill σ tlbvec vpn p2 p1 w) := by
      intro mxr dosum
      unfold translate
      rw [execABindSome _ _ _ _ _ hlk]
      unfold AxSymCtl4.tlbFill
      rw [← htlb]
      exact execATranslateTLBMissUser vpn rootPpn p2 p1 w acc p mxr dosum hv2 hn2 hv1 hn1 hv0 hl0
        (hchk mxr dosum) hnap 0#16 menvcfgS σ hmisa hupd hrd2 hrd1 hrd0 hmenv hpbmte
    refine ⟨execATranslateAddrPtFront acc p vpn rootPpn (ppn0 w) satp0 va pa σ _ heff hss hcp htm
      hsatp hppn hasid hcanon rfl htr hout, ?_⟩
    refine cntTranslateAddrPtFront acc p vpn rootPpn (ppn0 w) satp0 va pa σ _ 3 heff hss hcp htm
      hsatp hppn hasid hcanon rfl htr (fun mxr dosum => ?_)
    unfold translate
    rw [cASeq0' _ _ _ _ _ hlk (rfFLookupTLB _ _ _)]
    exact cntTranslateTLBMissUser vpn rootPpn p2 p1 w acc p mxr dosum hv2 hn2 hv1 hn1 hv0 hl0
      (hchk mxr dosum) hnap 0#16 menvcfgS σ hmisa hupd hrd2 hrd2c hrd1 hrd1c hrd0 hrd0c hmenv hpbmte
  unfold tlbHitv
  cases hslot : tlbvec[tlb_hash 39 vpn]! with
  | none =>
    have hlk := execLookupTLBMiss vpn 0#16 tlbvec σ htlb hslot
    to_a hlk
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact hmiss hlk
  | some ent =>
    obtain ⟨vpn0, q2, q1, q0, hm0, -, hent⟩ := htlbok vpn ent hslot
    by_cases hne : vpn0 = vpn
    · rw [hne] at hm0 hent
      obtain ⟨h2, h1, h0⟩ := AxPtProt.ptreeMapsDet t vpn q2 q1 q0 p2 p1 w hm0 hmaps
      rw [h2, h1, h0] at hent
      subst hent
      have hlk := execLookupTLBHitEnt vpn 0#16 tlbvec _ σ htlb hslot
        (WeakKpt.uweMatchSelf vpn p2 p1 w 0#16)
      to_a hlk
      simp only [WeakKpt.uweMatchSelf, ↓reduceIte]
      have htr : ∀ mxr dosum, execA (translate 39 0#16 rootPpn vpn acc p mxr dosum ()) σ =
          some (.Ok (ppn0 w, .PBMT_PMA, ()), σ) := by
        intro mxr dosum
        unfold translate
        rw [execABindSome _ _ _ _ _ hlk]
        exact execATranslateTLBHitPt acc p mxr dosum vpn p2 p1 w 0#16 (tlb_hash 39 vpn) σ
          (hchk mxr dosum) hupd hpb
      refine ⟨execATranslateAddrPtFront acc p vpn rootPpn (ppn0 w) satp0 va pa σ _ heff hss hcp htm
        hsatp hppn hasid hcanon rfl htr hout, ?_⟩
      refine cntTranslateAddrPtFront acc p vpn rootPpn (ppn0 w) satp0 va pa σ _ 0 heff hss hcp htm
        hsatp hppn hasid hcanon rfl htr (fun mxr dosum => ?_)
      unfold translate
      rw [cASeq0' _ _ _ _ _ hlk (rfFLookupTLB _ _ _)]
      exact cntTranslateTLBHitPt acc p mxr dosum vpn p2 p1 w 0#16 (tlb_hash 39 vpn) σ
        (hchk mxr dosum) hupd hpb
    · have hmo : match_TLB_Entry ent 0#16 (sign_extend (m := 57 - 12) vpn) = false := by
        rw [hent]; exact WeakWalkEff.uweMatchOther vpn0 vpn q2 q1 q0 0#16 hne
      have hlk := execLookupTLBNomatchS vpn 0#16 ent tlbvec σ htlb hslot hmo
      to_a hlk
      simp only [hmo, Bool.false_eq_true, ↓reduceIte]
      exact hmiss hlk

/-- Rocq `tlb_hitv_fill`: after a miss the filled slot hits. -/
theorem tlbHitvFill (tlbvec : Vector (Option TLB_Entry) (2 ^ 6)) (vpn : BitVec 27) (p2 p1 w : BitVec 64) :
    tlbHitv (vectorUpdate tlbvec (tlb_hash 39 vpn) (some (uWalkEntry vpn p2 p1 w 0#16))) vpn = true := by
  unfold tlbHitv
  rw [AxPtProt.vecUpdSame _ _ _ (AxPtProt.tlbHashLt vpn)]
  exact WeakKpt.uweMatchSelf vpn p2 p1 w 0#16

/-! # 5. THE FETCH: translation reads + the instruction read (Stage C: the instruction read
counts 0, so the fetch counts exactly the translation's reads; Rocq `ntr + 1`) -/

/-- (Lean-only) `fetch_bytes` counts the translation's reads plus its `mem_read`'s. -/
theorem AxSymCtl4.cntFetchBytesOk (fs gs pa : BitVec 64) (n : Nat) (pbmt : page_based_mem_type)
    (w : BitVec (8 * n)) (s s1 : ExecSt) (ntr c : Nat)
    (htr : execA (translateAddr (.Virtaddr gs) (.InstructionFetch ())) s
      = some (.Ok (.Physaddr pa, pbmt, ()), s1))
    (htrc : cntA (translateAddr (.Virtaddr gs) (.InstructionFetch ())) s = ntr)
    (hmr : execA (mem_read (.InstructionFetch ()) pbmt (.Physaddr pa) n false false false) s1
      = some (.Ok w, s1))
    (hmrc : cntA (mem_read (.InstructionFetch ()) pbmt (.Physaddr pa) n false false false) s1 = c) :
    cntA (fetch_bytes fs gs n) s = ntr + c := by
  unfold fetch_bytes ext_fetch_check_pc
  rw [cntACatchEarlyReturn]
  simp (config := { decide := true }) only [AxSymCtl4.cntARBind, execARBind, cntARLiftR,
    execARLiftR, execARReturnRFwd, cntARReturnR, htr, htrc, hmr, hmrc, Nat.add_zero]

theorem AxSymCtl4.cntCurrentlyEnabledZiccif (s : ExecSt) : cntA (currentlyEnabled .Ext_Ziccif) s = 0 :=
  cntARfF _ rfFCurrentlyEnabledZiccif s
theorem AxSymCtl4.cntCurrentlyEnabledZca (s : ExecSt) : cntA (currentlyEnabled .Ext_Zca) s = 0 :=
  cntARfF _ rfFCurrentlyEnabledZca s

/-- Rocq `cnt_fetch_RVC_4_S_gen` (Stage C: `= ntr`, Rocq `ntr + 1`). -/
theorem cntFetchRVC4SGen (va pa : BitVec 64) (w : BitVec 32) (s s1 : ExecSt)
    (region : PMA_Region) (ntr : Nat) (hpc : s.regs .PC = va)
    (hvalign : is_aligned_vaddr (.Virtaddr va) 4 = true)
    (htr : execA (translateAddr (.Virtaddr va) (.InstructionFetch ())) s
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1))
    (htrc : cntA (translateAddr (.Virtaddr va) (.InstructionFetch ())) s = ntr)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s1.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s1.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s1.regs .pmpaddr_n)[0]!.toNat * 4) pa.toNat
      (to_bits (l := 64) 4).toNat = .PMP_Match)
    (hX : (_get_Pmpcfg_ent_X (s1.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hm : matching_pma_region (s1.regs .pma_regions) (.Physaddr pa) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr pa) 4 = true)
    (hx : (override_PMA region.attributes .PBMT_PMA).executable = true)
    (hc : exec (within_clint (.Physaddr pa) 4) s1 = some (false, s1))
    (hsig : exec (within_sig (.Physaddr pa) 4) s1 = some (false, s1))
    (hh : exec (within_htif_readable (.Physaddr pa) 4) s1 = some (false, s1))
    (hdev : devAddr pa = false) (hwf : paZ pa + 4 ≤ 2 ^ 64) (hb : BytesAt s1 pa 4 w)
    (hpriv : s1.regs .cur_privilege = .Supervisor)
    (hrvc : isRVC (Sail.BitVec.extractLsb w 15 0) = true) :
    cntA (fetch ()) s = ntr := by
  have hmr := execAMemReadFetch4S .PBMT_PMA pa region w s1 hA hlt hr hX hm hal hx hc hsig hh hdev hwf
    hb hpriv
  have hmrc := cntMemReadFetch4S .PBMT_PMA pa region w s1 hA hlt hr hX hm hal hx hc hsig hh hdev hwf
    hb hpriv
  have hfb := AxSpineOk3.execAFetchBytesOk va va pa 4 .PBMT_PMA w s s1 htr hmr
  have hfbc := AxSymCtl4.cntFetchBytesOk va va pa 4 .PBMT_PMA w s s1 ntr 0 htr htrc hmr hmrc
  unfold fetch ext_fetch_check_pc get_config_rvfi
  rw [cntACatchEarlyReturn]
  simp (config := { decide := true }) only [AxSymCtl4.cntARBind, execARBind, cntARLiftR,
    execARLiftR, execARReturnRFwd, cntARReturnR, readReg, PreSail.readReg, PreSail.emit, execA,
    cntA, hpc, bit0ClearOfAligned4 va hvalign, bit1ClearOfAligned4 va hvalign, hvalign,
    execACurrentlyEnabledZiccif, AxSymCtl4.cntCurrentlyEnabledZiccif, hfb, hfbc, hrvc, ↓reduceIte,
    Bool.false_eq_true, Functions.not, Nat.reduceMul, BitVec.setWidth_eq, Nat.add_zero,
    Nat.zero_add]

/-- Rocq `cnt_fetch_RVC_2_S_gen` (Stage C: `= ntr`, Rocq `ntr + 1`). -/
theorem cntFetchRVC2SGen (va pa : BitVec 64) (h : BitVec 16) (s s1 : ExecSt)
    (region : PMA_Region) (ntr : Nat) (hpc : s.regs .PC = va)
    (hmisaC : (_get_Misa_C (s.regs .misa) == 1#1) = true)
    (hbit0 : (Sail.BitVec.access va 0 != 0#1) = false)
    (hbit1 : (Sail.BitVec.access va 1 != 0#1) = true)
    (hvalign4 : is_aligned_vaddr (.Virtaddr va) 4 = false)
    (htr : execA (translateAddr (.Virtaddr va) (.InstructionFetch ())) s
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1))
    (htrc : cntA (translateAddr (.Virtaddr va) (.InstructionFetch ())) s = ntr)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s1.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s1.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s1.regs .pmpaddr_n)[0]!.toNat * 4) pa.toNat
      (to_bits (l := 64) 2).toNat = .PMP_Match)
    (hX : (_get_Pmpcfg_ent_X (s1.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hm : matching_pma_region (s1.regs .pma_regions) (.Physaddr pa) 2 = some region)
    (hal : is_aligned_paddr (.Physaddr pa) 2 = true)
    (hx : (override_PMA region.attributes .PBMT_PMA).executable = true)
    (hc : exec (within_clint (.Physaddr pa) 2) s1 = some (false, s1))
    (hsig : exec (within_sig (.Physaddr pa) 2) s1 = some (false, s1))
    (hh : exec (within_htif_readable (.Physaddr pa) 2) s1 = some (false, s1))
    (hdev : devAddr pa = false) (hwf : paZ pa + 2 ≤ 2 ^ 64) (hb : BytesAt s1 pa 2 h)
    (hpriv : s1.regs .cur_privilege = .Supervisor) (hrvc : isRVC h = true) :
    cntA (fetch ()) s = ntr := by
  have hmr := execAMemReadFetch2S .PBMT_PMA pa region h s1 hA hlt hr hX hm hal hx hc hsig hh hdev hwf
    hb hpriv
  have hmrc := cntMemReadFetch2S .PBMT_PMA pa region h s1 hA hlt hr hX hm hal hx hc hsig hh hdev hwf
    hb hpriv
  have hfb := AxSpineOk3.execAFetchBytesOk va va pa 2 .PBMT_PMA h s s1 htr hmr
  have hfbc := AxSymCtl4.cntFetchBytesOk va va pa 2 .PBMT_PMA h s s1 ntr 0 htr htrc hmr hmrc
  have hzca := execACurrentlyEnabledZca s hmisaC
  unfold fetch ext_fetch_check_pc get_config_rvfi
  rw [cntACatchEarlyReturn]
  simp (config := { decide := true }) only [AxSymCtl4.cntARBind, execARBind, cntARLiftR,
    execARLiftR, execARReturnRFwd, cntARReturnR, readReg, PreSail.readReg, PreSail.emit, execA,
    cntA, hpc, hbit0, hbit1, hvalign4, hzca, AxSymCtl4.cntCurrentlyEnabledZca, hfb, hfbc, hrvc,
    ↓reduceIte, Bool.false_eq_true, Functions.not, Nat.reduceMul, BitVec.setWidth_eq, Nat.add_zero,
    Nat.zero_add]

/-! # 6. THE COUNTING SPINE AT THE S-MODE KERNEL REGIME: `spineCntS`

`fcntS rs pc`: the fetch's GRAPH reads — 0 on a TLB HIT, 3 on a MISS (the three PTE reads; the
instruction read is the pinned admin step, Stage C).  Rocq: 1 / 4.  The hit test `tlbHitv` reads
only the `tlb` register. -/

/-- Rocq `fcnt_S` (Stage C: 0 / 3; Rocq 1 / 4). -/
def fcntS (rs : RegFile) (pc : BitVec 64) : Nat :=
  if tlbHitv (rs .tlb) (WeakKpt.svpnOf pc) then 0 else 3

section spineS
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)

/-- Rocq `sc_fetch_S`: THE COUNTING FETCH FIELD. -/
theorem scFetchS (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (t : ExecSt) (pc : BitVec 64) (h : BitVec 16) :
    ctrlOkS T satp0 t.regs → t.regs .PC = pc → textAtS σi T pc h →
    ∃ t1, tlbFrame t t1 ∧ ctrlOkS T satp0 t1.regs ∧ warm fcntS t1.regs pc ∧
      ∀ b, EvB (imgS σi) (fun _ _ => False)
        (fun b' r t' => b = b' + fcntS t.regs pc ∧ r = .F_RVC h ∧ t' = t1) (fetch ()) t b := by
  intro hc hPC ⟨p2, p1, w, pa, hmaps, hs2, hs1, hs0, hchk, hupd, hpb, hcanon, hout, hb0, hRVC, hal⟩
  let σ : ExecSt := ⟨t.regs, σi.mem, t.dev⟩
  have hc0 := hc
  obtain ⟨hpriv, -, hmisa, hmenv, hhtif, -, hpma, hms, -, -, hsatp, htlbx, hA, hord, -, hR, hcov⟩ :=
    hc0
  obtain ⟨-, hSXL, -⟩ := hms
  have htm := execTranslationModeSSv39 satp0 σ hSXL hsatp hmode
  have heff := execEffectivePrivilegeFetch (σ.regs .mstatus) .Supervisor σ
  have hss := execIsShadowStackFetch σ
  have hpmar : WeakKpt.pmaAllowsPteRead (σ.regs .pma_regions) := by
    show WeakKpt.pmaAllowsPteRead (t.regs .pma_regions)
    rw [hpma]; exact WeakKpt.pmaAllowsBootPteRead
  have hs2' : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr2 T (WeakKpt.svpnOf pc)) p2 := hs2
  have hs1' : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr1 p2 (WeakKpt.svpnOf pc)) p1 := hs1
  have hs0' : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf pc)) w := hs0
  obtain ⟨htr, htrc⟩ := cntTranslateAddrImg (.InstructionFetch ()) .Supervisor T.base pc w pa
    satp0 T (σ.regs .tlb) p2 p1 σ hchk hupd hcanon hout hpb rfl hmaps htlbx hs2' hs1' hs0' hmisa
    hmenv hhtif hpriv htm heff hss hsatp hppn hasid rfl hA hord hR hcov hpmar
  -- the fetch, for whichever post-translation state
  have key : ∀ σ', execA (translateAddr (.Virtaddr pc) (.InstructionFetch ())) σ =
        some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), σ') →
      ctrlOkS T satp0 σ'.regs → σ'.mem = σi.mem →
      execA (fetch ()) σ = some (.F_RVC h, σ') ∧
        cntA (fetch ()) σ = cntA (translateAddr (.Virtaddr pc) (.InstructionFetch ())) σ := by
    intro σ' htr' hc' hmem'
    have hc'0 := hc'
    obtain ⟨hpriv', -, -, -, -, -, -, -, -, -, -, -, hA', hord', hX', -, -⟩ := hc'0
    cases hal4 : is_aligned_vaddr (.Virtaddr pc) 4
    · rw [hal4] at hal
      simp only [Bool.false_eq_true, ↓reduceIte] at hal
      obtain ⟨hb1, hram, halp, hbytes⟩ := hal
      obtain ⟨region, hrange, hm, hx, hcl, hsig, hh, hdev, hwf⟩ :=
        ramFetchFacts T satp0 σ' pa 2 hc' (by decide) (by decide) (by decide) hram
      have hmC : (_get_Misa_C (σ.regs .misa) == 1#1) = true := by
        show (_get_Misa_C (t.regs .misa) == 1#1) = true
        rw [hmisa]; decide
      have hb' : BytesAt σ' pa 2 h := by intro j hj; rw [hmem']; exact hbytes j hj
      exact ⟨execAFetchRVC2SGen pc pa h σ σ' region hPC hmC hb0 hb1 hal4 htr' hA' hord' hrange hX' hm
          halp hx hcl hsig hh hdev hwf hb' hpriv' hRVC,
        cntFetchRVC2SGen pc pa h σ σ' region _ hPC hmC hb0 hb1 hal4 htr' rfl hA' hord' hrange hX' hm
          halp hx hcl hsig hh hdev hwf hb' hpriv' hRVC⟩
    · rw [hal4] at hal
      simp only [↓reduceIte] at hal
      obtain ⟨w32, hlow, hram, halp, hbytes⟩ := hal
      obtain ⟨region, hrange, hm, hx, hcl, hsig, hh, hdev, hwf⟩ :=
        ramFetchFacts T satp0 σ' pa 4 hc' (by decide) (by decide) (by decide) hram
      subst hlow
      have hb' : BytesAt σ' pa 4 w32 := by intro j hj; rw [hmem']; exact hbytes j hj
      exact ⟨execAFetchRVC4SGen pc pa w32 σ σ' region hPC hal4 htr' hA' hord' hrange hX' hm halp hx
          hcl hsig hh hdev hwf hb' hpriv' hRVC,
        cntFetchRVC4SGen pc pa w32 σ σ' region _ hPC hal4 htr' rfl hA' hord' hrange hX' hm halp hx
          hcl hsig hh hdev hwf hb' hpriv' hRVC⟩
  -- the post-translation state, by the hit test
  have hfill : ctrlOkS T satp0
      (AxSymCtl4.tlbFill σ (σ.regs .tlb) (WeakKpt.svpnOf pc) p2 p1 w).regs :=
    ctrlOkSTlbFill T satp0 t.regs _ p2 p1 w _ hc hmaps rfl
  cases hhit : tlbHitv (σ.regs .tlb) (WeakKpt.svpnOf pc)
  · rw [hhit] at htr htrc
    simp only [Bool.false_eq_true, ↓reduceIte] at htr htrc
    obtain ⟨hf, hfc⟩ := key _ htr hfill rfl
    refine ⟨⟨(AxSymCtl4.tlbFill σ (σ.regs .tlb) (WeakKpt.svpnOf pc) p2 p1 w).regs, t.mem, t.dev⟩,
      Or.inr ⟨_, rfl⟩, hfill, ?_, fun b => ?_⟩
    · intro pc' hpc'
      unfold fcntS
      rw [hpc']
      simp only [AxSymCtl4.tlbFill, ExecSt.setReg_regs, RegFile.set_same, tlbHitvFill, ↓reduceIte]
    · have hE := execAEvB (fetch ()) σ _ _ hf t rfl b
      refine EvBMono (imgS σi) _ _ _ _ (fetch ()) t b (fun _ _ hf => hf) ?_ hE
      rintro b' x ⟨r', m', d'⟩ ⟨hb, rfl, hr, hm1, hd1⟩
      refine ⟨?_, rfl, ?_⟩
      · rw [hb, hfc, htrc]
        show b' + 3 = b' + (if tlbHitv (t.regs .tlb) (WeakKpt.svpnOf pc) then 0 else 3)
        rw [show tlbHitv (t.regs .tlb) (WeakKpt.svpnOf pc) = false from hhit]
        rfl
      · simp only at hr hm1 hd1; subst hr hm1 hd1; rfl
  · rw [hhit] at htr htrc
    simp only [↓reduceIte] at htr htrc
    obtain ⟨hf, hfc⟩ := key _ htr hc rfl
    refine ⟨⟨t.regs, t.mem, t.dev⟩, Or.inl rfl, hc, ?_, fun b => ?_⟩
    · intro pc' hpc'
      unfold fcntS
      rw [hpc']
      show (if tlbHitv (t.regs .tlb) (WeakKpt.svpnOf pc) then 0 else 3) = 0
      rw [show tlbHitv (t.regs .tlb) (WeakKpt.svpnOf pc) = true from hhit]
      rfl
    · have hE := execAEvB (fetch ()) σ _ _ hf t rfl b
      refine EvBMono (imgS σi) _ _ _ _ (fetch ()) t b (fun _ _ hf => hf) ?_ hE
      rintro b' x ⟨r', m', d'⟩ ⟨hb, rfl, hr, hm1, hd1⟩
      refine ⟨?_, rfl, ?_⟩
      · rw [hb, hfc, htrc]
        show b' + 0 = b' + (if tlbHitv (t.regs .tlb) (WeakKpt.svpnOf pc) then 0 else 3)
        rw [show tlbHitv (t.regs .tlb) (WeakKpt.svpnOf pc) = true from hhit]
        rfl
      · simp only at hr hm1 hd1; subst hr hm1 hd1; rfl

/-- Rocq `tick_post'`: `tick_clock` writes only `mcycle`, `mtime`, `mip` — the `tlb` too is
kept. -/
theorem tickPost' (t t' : ExecSt) :
    (∀ r : Register, r ≠ .mcycle → r ≠ .mtime → r ≠ .mip → t'.regs r = t.regs r) →
    ctrlOkS T satp0 t.regs → ctrlOkS T satp0 t'.regs ∧ keepRegs t.regs t'.regs ∧
      t'.regs .tlb = t.regs .tlb := by
  intro hag hc
  obtain ⟨h1, h2⟩ := tickPost T satp0 t t' hag hc
  exact ⟨h1, h2, hag _ (by decide) (by decide) (by decide)⟩

/-- Rocq `sc_tick_S` (`AxSpineOk7.sptTickS` replayed with the stronger post). -/
theorem scTickS (t : ExecSt) : ctrlOkS T satp0 t.regs →
    EvA (imgS σi) (fun _ _ => False)
      (fun _ t' => ctrlOkS T satp0 t'.regs ∧ keepRegs t.regs t'.regs ∧ t'.regs .tlb = t.regs .tlb)
      (tick_clock ()) t := by
  intro hc
  unfold tick_clock clint_dispatch read_mip external_interrupts_pending
  ax_sym2_ev_go
  obtain ⟨b, hb⟩ := execShouldIncMcycleSome (t.regs .cur_privilege) t
  refine AxSymEngine2.evFactUse (EvAOfRfF _ _ (AxSpineOk7.rfFShouldIncMcycle _) t b t hb) ?_
  cases b
  all_goals ax_sym2_ev_go
  all_goals refine AxSymEngine2.evFactUse (AxSpineOk7.evSstc _ _) ?_
  all_goals repeat' (ax_sym2_ev_go; first
    | (refine AxSpineOk7.evFactReadPin (Or.inr rfl) fun _ => ?_)
    | (refine AxSpineOk7.evFactReadPin (Or.inl rfl) fun _ => ?_)
    | (refine AxSymEngine2.evFactQ (AxSpineOk7.evCurS _ _) ?_; rintro _ _ ⟨rfl, rfl⟩)
    | (rw [AxSpineOk7.csrMip])
    | split)
  all_goals refine .evRet _ _ ?_
  all_goals refine tickPost' T satp0 t _ ?_ hc
  all_goals intro r h1 h2 h3
  all_goals simp only [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ h1,
    RegFile.set_other _ _ _ _ h2, RegFile.set_other _ _ _ _ h3]

/-- Rocq `tlb_hitv_ag`. -/
theorem tlbHitvAg (rs rs' : RegFile) (pc : BitVec 64) :
    rs' .tlb = rs .tlb → fcntS rs' pc = fcntS rs pc := by
  intro h
  unfold fcntS
  rw [h]

end spineS

/-- Rocq `SpineCnt_S`: THE COUNTING SPINE AT THE S-MODE KERNEL REGIME (premises: only the three
static facts about the kernel satp, as `spineOkTS`; Rocq's `sc_pos` field is not a field in
Lean, `AxSymCtlb` deviation 2). -/
theorem spineCntS (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base) :
    SpineCnt (imgS σi) (ctrlOkS T satp0) (textAtS σi T) fcntS :=
  ⟨spineOkTS σi T satp0 hmode hasid hppn, scFetchS σi T satp0 hmode hasid hppn,
    tlbHitvAg, scTickS σi T satp0⟩

end Weak
