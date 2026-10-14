/-
Weak: **W9a (B) B5 — r1, THE SAIL FETCH VALUE CHAIN** (plan `notes/weak-allocproc-plan.md` rev 52
§D Q-B5-FETCH, §C W9a (B) "(B5) assembly"; ruling [OWN.81]).  Lean-only (no Rocq source).

`PinFetchVal.faB Ann P m st` is a B1-style (`PinDataflow.dfB`) all-paths predicate on a Sail tree
whose STATE `st` is the list of the instruction-fetch reads made so far, in order (`FRd`: physical
address, width, the value answered).  Along every path of `m`:
* an instruction-fetch memory read is a RAM read (`devAddr pa = false`, an obligation) and appends
  `⟨paZ pa, n, w⟩` for EVERY answer `w`; any other memory read continues for every answer;
* a register read is answered by any value W-SCO's boot filter `Rboot` admits, a register write
  writes an `Rboot`-admitted value;
* an `instrAnnounce n w` node is the END: it owes `Ann st n w`;
* every other node continues for every answer, a failure is stuck (`True`), `.pure x` owes `P x st`.

The headline `faCycle` is the theorem about the Sail text (`model/Lean_RV64D/LeanRV64D/Fetch.lean:
233-288`, `Step.lean:330-404`): every cycle `riscvStep tick`, started with no fetch read, announces
(if it announces at all) bits that are the fetch reads' values in one of Sail's FOUR arm shapes
(`FetchShape`): a 4-byte read announced whole (`F_Base w`, `isRVC w[15:0]` false) or by its low
halfword (`F_RVC w[15:0]`), a 2-byte read announced compressed (`F_RVC h`), or two 2-byte reads
announced as one word (`F_Base (ihi ++ ilo)`, `isRVC ilo` false).  The PRECISION points: the
fetch's PMA check (`pmaCheck`, `Mem.lean:263`) answers `Ok` for an instruction fetch only at an
ALIGNED physical address (`mag_pma_check`, `Pma.lean:398`: a misaligned instruction fetch is the
model's `internal_error`), so the read is never split (`split_misaligned` at `CannotSplit`), and
only in RAM under the boot PMA table (W-SCO's `pmaFetchRam`), so it is no MMIO read.  No claim is
made about the ADDRESSES beyond their being the reads' own (`fetchPaR2`, r2, is a separate item).

The run form `faRunAnn` / `fetchAnnOfRun`: along a hart's `pstepHw` run from `riscvStep tick`
(boot-admitted register file) to its announce node, the run's `LIFetch` labels ARE the state, so the
announced bits are the run's own i-cache read values in an arm shape.

Every helper is `Weak.PinFetchVal.*`.
-/
import Weak.SailCycleOrderCycle
import Weak.PinDataflowGlue

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinFetchVal
open SailCycleOrderK SailCycleOrderFp

/-! ## 1. The predicate -/

/-- One instruction-fetch read: physical address, width in bytes, the value answered. -/
structure FRd where
  pa : Int
  n : Nat
  v : BitVec (8 * n)

/-- **THE FETCH-VALUE PREDICATE** (header). -/
def faB {X : Type} (Ann : List FRd → (n : Nat) → BitVec n → Prop) (P : X → List FRd → Prop) :
    SailM X → List FRd → Prop
  | .pure x, st => P x st
  | .impure (.error _) _, _ => True
  | .impure (.ok o) k, st =>
    match o, k with
    | .memRead n _ req, k =>
        if (classify req.access_kind).akIfetch = true then
          devAddr req.pa = false ∧
            ∀ w : BitVec (8 * n), faB Ann P (k (.Ok (w, none))) (st ++ [⟨paZ req.pa, n, w⟩])
        else ∀ w : BitVec (8 * n), faB Ann P (k (.Ok (w, none))) st
    | .instrAnnounce n w, _ => Ann st n w
    | .regRead r, k => ∀ v, Rboot r v → faB Ann P (k v) st
    | .regWrite r v, k => Rboot r v ∧ ∀ u, faB Ann P (k u) st
    | .barrier _, k => ∀ v, faB Ann P (k v) st
    | .memWrite .., k => ∀ v, faB Ann P (k v) st
    | .branchAnnounce .., k => ∀ v, faB Ann P (k v) st
    | .cacheOp _, k => ∀ v, faB Ann P (k v) st
    | .tlbi _, k => ∀ v, faB Ann P (k v) st
    | .takeException _, k => ∀ v, faB Ann P (k v) st
    | .returnException _, k => ∀ v, faB Ann P (k v) st
    | .translationStart _, k => ∀ v, faB Ann P (k v) st
    | .translationEnd _, k => ∀ v, faB Ann P (k v) st
    | .cycleCount, k => ∀ v, faB Ann P (k v) st
    | .getCycleCount, k => ∀ v, faB Ann P (k v) st
    | .message _, k => ∀ v, faB Ann P (k v) st
    | .choose _, k => ∀ v, faB Ann P (k v) st
    | .readRam .., k => ∀ v, faB Ann P (k v) st
    | .writeRam .., k => ∀ v, faB Ann P (k v) st

variable {Ann : List FRd → (n : Nat) → BitVec n → Prop}

/-! ## 2. The kit: bind, monotonicity, the footprint lift -/

theorem faBind {X Y : Type} (Q : X → List FRd → Prop) (P : Y → List FRd → Prop) (m : SailM X)
    (f : X → SailM Y) :
    ∀ st, faB Ann Q m st → (∀ x st', Q x st' → faB Ann P (f x) st') → faB Ann P (m >>= f) st := by
  induction m with
  | pure y => intro st hm hf; exact hf y st hm
  | impure call k ih =>
    intro st hm hf
    cases call with
    | error e => trivial
    | ok o =>
      show faB Ann P (FreeM.impure (.ok o) (fun v => k v >>= f)) st
      cases o
      case memRead n va req =>
        simp only [faB] at hm ⊢
        split
        · rename_i h
          rw [if_pos h] at hm
          exact ⟨hm.1, fun w => ih _ _ (hm.2 w) hf⟩
        · rename_i h
          rw [if_neg h] at hm
          exact fun w => ih _ _ (hm w) hf
      case instrAnnounce => exact hm
      case regRead => exact fun v hv => ih v _ (hm v hv) hf
      case regWrite => exact ⟨hm.1, fun u => ih u _ (hm.2 u) hf⟩
      all_goals exact fun v => ih v _ (hm v) hf

theorem faMono {X : Type} (P P' : X → List FRd → Prop) (hP : ∀ x st, P x st → P' x st) :
    ∀ (m : SailM X) st, faB Ann P m st → faB Ann P' m st := by
  intro m
  induction m with
  | pure y => exact fun st h => hP y st h
  | impure call k ih =>
    intro st hm
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [faB] at hm ⊢
        split
        · rename_i h
          rw [if_pos h] at hm
          exact ⟨hm.1, fun w => ih _ _ (hm.2 w)⟩
        · rename_i h
          rw [if_neg h] at hm
          exact fun w => ih _ _ (hm w)
      case instrAnnounce => exact hm
      case regRead => exact fun v hv => ih v _ (hm v hv)
      case regWrite => exact ⟨hm.1, fun u => ih u _ (hm.2 u)⟩
      all_goals exact fun v => ih v _ (hm v)

theorem faPure {X : Type} (P : X → List FRd → Prop) (x : X) (st : List FRd) :
    P x st → faB Ann P (pure x : SailM X) st := fun h => h

/-- **The footprint lift**: a strict footprint tree (no fetch read, no announce) keeps the state. -/
theorem faOfFp {X : Type} (S : X → Prop) :
    ∀ (m : SailM X) st, fp S m → faB Ann (fun x st' => S x ∧ st' = st) m st := by
  intro m
  induction m with
  | pure y => intro st h; exact ⟨h, rfl⟩
  | impure call k ih =>
    intro st hm
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case memRead n va req =>
        obtain ⟨hk, hm⟩ := hm
        have hk' : (classify req.access_kind).akIfetch = false := hk
        simp only [faB, hk', Bool.false_eq_true, ↓reduceIte]
        exact fun w => ih _ _ (hm _)
      case instrAnnounce => exact hm.elim
      case barrier => exact fun v => ih v _ hm.2
      case regRead => exact fun v hv => ih v _ (hm v hv)
      case regWrite => exact ⟨hm.1, fun u => ih u _ (hm.2 u)⟩
      all_goals exact fun v => ih v _ (hm v)

/-- A strict-footprint head of a bind. -/
theorem faFpBind {X Y : Type} (S : X → Prop) (P : Y → List FRd → Prop) (m : SailM X)
    (f : X → SailM Y) (st : List FRd) (hm : fp S m) (hf : ∀ x, S x → faB Ann P (f x) st) :
    faB Ann P (m >>= f) st :=
  faBind _ P m f st (faOfFp S m st hm) (fun x _ h => h.2 ▸ hf x h.1)

/-- A strict-footprint tree with a post. -/
theorem faFp {X : Type} (S : X → Prop) (P : X → List FRd → Prop) (m : SailM X) (st : List FRd)
    (hm : fp S m) (hP : ∀ x, S x → P x st) : faB Ann P m st :=
  faMono _ P (fun x st' (h : S x ∧ st' = st) => h.2 ▸ hP x h.1) m st (faOfFp S m st hm)

/-! ## 3. The read leaf -/

/-- **The i-cache read** (`read_ram Read_ifetch`): one fetch read at a RAM address, appended. -/
theorem faReadRam (pa : BitVec 64) (n : Nat) (st : List FRd) (hd : devAddr pa = false) :
    faB Ann (fun r st' => st' = st ++ [⟨paZ pa, n, r.1⟩])
      (read_ram .Read_ifetch (.Physaddr pa) n false) st := by
  simp only [read_ram, PreSail.sail_mem_read, PreSail.emit, pure_bind]
  show faB Ann _ (FreeM.impure (Except.ok (Outcome.memRead n 64 _)) _) st
  simp only [faB]
  split
  · exact ⟨hd, fun w => rfl⟩
  · rename_i h; exact absurd rfl h

/-! ## 4. The fetch's PMA precision: RAM, never split -/

set_option maxHeartbeats 40000000 in
/-- A misaligned instruction fetch is the model's `internal_error` (`Pma.lean:330`): no path
returns. -/
@[fp_reg] theorem fpPmaMisalignedExceptionIF (pma : PMA) :
    fp (fun _ => False) (pma_misaligned_exception pma (.InstructionFetch ())) := by
  fp_walk_v

set_option maxHeartbeats 40000000 in
/-- `mag_pma_check` of an instruction fetch answers `Ok` only unsplit (aligned). -/
@[fp_reg] theorem fpMagPmaCheckIF (pma : PMA) (paddr : physaddr) (width : Nat) :
    fp (fun r => ∀ s g, r = .Ok (s, g) → s = .CannotSplit)
      (mag_pma_check pma (.InstructionFetch ()) paddr width) := by
  unfold mag_pma_check
  fp_walk_v
  all_goals first
    | contradiction
    | (rename_i h; injection h with h; injection h with h; exact h.symm)
    | trace_state

set_option maxHeartbeats 40000000 in
/-- The PMA check of an instruction fetch answers `Ok` only in RAM and unsplit. -/
@[fp_reg] theorem fpPmaCheckIFS (pa : physaddr) (w : Nat) (pbmt : page_based_mem_type) (rc : Bool) :
    fp (fun r => ∀ i, r = .Ok i → 0x80000000 ≤ (bits_of_physaddr pa).toNat ∧
        i.splittable = .CannotSplit)
      (pmaCheck pa w (.InstructionFetch ()) pbmt rc) := by
  unfold pmaCheck
  fp_walk_v
  all_goals first
    | (apply pmaClose <;> assumption)
    | (rename_i ha _ hi; injection hi with hi; subst hi; exact ha _ _ rfl)

set_option maxHeartbeats 40000000 in
/-- The PMA-with-PMP check of an instruction fetch: `Ok` only in RAM and unsplit. -/
@[fp_reg] theorem fpCheckPmaIFS (pbmt : page_based_mem_type) (priv : Privilege) (pa : physaddr)
    (w : Nat) (rc : Bool) :
    fp (fun r => ∀ i, r = .Ok i → 0x80000000 ≤ (bits_of_physaddr pa).toNat ∧
        i.splittable = .CannotSplit)
      (check_pma_with_pmp_priority (.InstructionFetch ()) pbmt priv pa w rc) := by
  unfold check_pma_with_pmp_priority
  fp_walk_v
  all_goals (rename_i ha _ hi; injection hi with hi; subst hi)
  · exact (ha _ rfl).1
  · exact (ha _ rfl).2

set_option maxHeartbeats 40000000 in
/-- An unsplittable access is one access of the whole width. -/
theorem fpSplitCannot (pa : physaddr) (w : Nat) (e : Nat) :
    fp (fun p => p = (1, (w : Int))) (split_misaligned pa w e .CannotSplit) := by
  unfold split_misaligned
  fp_walk_v

/-! ## 5. The read chain: `checked_mem_read` → `mem_read` → `fetch_bytes` -/

/-- The loop's one-chunk assembly is the chunk (width 4). -/
theorem cmrVal4 (v : BitVec 32) :
    BitVec.setWidth 32 (BitVec.setWidth 32 (BitVec.setWidth 32 (Sail.BitVec.updateSubrange
      (BitVec.setWidth 32 (zeros (n := 32))) 31 0 (BitVec.setWidth 32 v)))) = v := by
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', zeros]
  bv_decide

set_option maxHeartbeats 40000000 in
/-- **`checked_mem_read` of an instruction fetch** (width 4): `Ok d` only after ONE fetch read at
`pa` answering `d`. -/
theorem faCheckedMemRead4 (pbmt : page_based_mem_type) (priv : Privilege) (pa : physaddr)
    (st : List FRd) :
    faB Ann (fun r st' => ∀ d m, r = .Ok (d, m) → st' = st ++ [⟨paZ (bits_of_physaddr pa), 4, d⟩])
      (checked_mem_read (.InstructionFetch ()) pbmt priv pa 4 false false false false) st := by
  simp only [checked_mem_read, SailME.run, PreSail.PreSailME.run, ExceptT.run_bind, run_liftM,
    bind_assoc, pure_bind, ExceptT.run_pure]
  refine faFpBind _ _ _ _ st (fpCheckPmaIFS pbmt priv pa 4 false) (fun r hr => ?_)
  cases r with
  | Err e =>
    simp only [run_SailME_throw, pure_bind]
    intro d m h; cases h
  | Ok info =>
    obtain ⟨hram, hsp⟩ := hr info rfl
    simp only [ExceptT.run_pure, pure_bind, hsp]
    rw [bind_assoc]
    refine faFpBind _ _ _ _ st (fpSplitCannot pa 4 _) (fun p hp => ?_)
    subst hp
    simp only [untilFuelM, misaligned_order, sys_misaligned_order_decreasing,
      Bool.false_eq_true, ↓reduceIte]
    rw [show Int.toNat 1 = 0 + 1 from rfl]
    simp only [untilFuelM.go, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind,
      ]
    refine faFpBind _ _ _ _ st (by fp_walk : fpT (assert true "loop dummy assert")) (fun _ _ => ?_)
    refine faFpBind _ _ _ _ st (fpPmpCheck _ _ _ _) (fun o _ => ?_)
    have hr0 : 0x80000000 ≤ (bits_of_physaddr (physaddr.Physaddr
        (BitVec.addInt (bits_of_physaddr pa) (↑(Int.toNat 0) * ↑4)))).toNat := ramShift0 pa _ hram
    have hd0 : devAddr (BitVec.addInt (bits_of_physaddr pa) (↑(Int.toNat 0) * ↑4)) = false :=
      devShift0 pa _ hram
    cases o with
    | some e =>
      simp only []
      intro d m h; cases h
    | none =>
      simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, 
        ]
      refine faFpBind _ _ _ _ st (fpWithinMmioRam _ _ hr0) (fun b hb => ?_)
      subst hb
      simp only [Bool.false_eq_true, ↓reduceIte, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
      refine faBind _ _ _ _ st (faReadRam _ _ st hd0) (fun r st' hst => ?_)
      subst hst
      have hc : (Int.toNat 0 == (1 - 1 : Int).toNat) = true := by decide
      simp only [hc, ↓reduceIte, pure_bind, ExceptT.run_pure]
      intro d m h
      injection h with h
      injection h with h
      subst h
      rw [SailCycleOrderFp.addInt0]
      obtain ⟨v, u⟩ := r
      show st ++ [⟨paZ (bits_of_physaddr pa), 4, v⟩] = st ++ [⟨paZ (bits_of_physaddr pa), 4,
        BitVec.setWidth 32 (BitVec.setWidth 32 (BitVec.setWidth 32 (Sail.BitVec.updateSubrange
          (BitVec.setWidth 32 (zeros (n := 32))) 31 0 (BitVec.setWidth 32 v))))⟩]
      exact congrArg (fun z : BitVec 32 => st ++ [(⟨paZ (bits_of_physaddr pa), 4, z⟩ : FRd)])
        (cmrVal4 v).symm

set_option maxHeartbeats 40000000 in
/-- **`mem_read` of an instruction fetch** (width 4). -/
theorem faMemRead4 (pbmt : page_based_mem_type) (pa : physaddr) (st : List FRd) :
    faB Ann (fun r st' => ∀ d, r = .Ok d → st' = st ++ [⟨paZ (bits_of_physaddr pa), 4, d⟩])
      (mem_read (.InstructionFetch ()) pbmt pa 4 false false false) st := by
  simp only [mem_read, mem_read_priv, mem_read_priv_meta, bind_assoc, pure_bind]
  refine faFpBind _ _ _ _ st (by fp_walk : fpT (readReg Register.mstatus)) (fun a _ => ?_)
  refine faFpBind _ _ _ _ st (by fp_walk : fpT (readReg Register.cur_privilege)) (fun b _ => ?_)
  refine faFpBind _ _ _ _ st (fpEffectivePrivilege _ _ _) (fun p _ => ?_)
  refine faBind _ _ _ _ st (faCheckedMemRead4 pbmt p pa st) (fun r st' h => ?_)
  intro d hd
  cases r with
  | Ok q =>
    obtain ⟨d', m⟩ := q
    simp only [MemoryOpResult_drop_meta] at hd
    injection hd with hd
    subst hd
    exact h _ m rfl
  | Err e => simp [MemoryOpResult_drop_meta] at hd

set_option maxHeartbeats 40000000 in
/-- **`fetch_bytes`** (width 4): `FetchBytes_Success b` only after ONE fetch read answering `b`. -/
theorem faFetchBytes4 (fs gs : BitVec 64) (st : List FRd) :
    faB Ann (fun r st' => ∀ b, r = .FetchBytes_Success b → ∃ a, st' = st ++ [⟨a, 4, b⟩])
      (fetch_bytes fs gs 4) st := by
  simp only [fetch_bytes, ext_fetch_check_pc, SailME.run, PreSail.PreSailME.run, ExceptT.run_bind,
    run_liftM, bind_assoc, pure_bind]
  refine faFpBind _ _ _ _ st (fpTranslateAddr _ _) (fun r _ => ?_)
  cases r with
  | Err e =>
    simp only [run_SailME_throw, pure_bind]
    intro b hb; cases hb
  | Ok q =>
    obtain ⟨paddr, pbmt, u⟩ := q
    simp only [ExceptT.run_pure, pure_bind, bind_assoc]
    refine faBind _ _ _ _ st (faMemRead4 pbmt paddr st) (fun r st' h => ?_)
    cases r with
    | Err q =>
      obtain ⟨ea, e⟩ := q
      simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, ExceptT.run_pure]
      refine faFpBind _ _ _ _ st' (by fp_walk : fpT (assert (ea == paddr) "postlude/fetch.sail:44.30-44.31"))
        (fun _ _ => ?_)
      intro b hb; cases hb
    | Ok bytes =>
      simp only [ExceptT.run_pure, pure_bind]
      intro b hb
      injection hb with hb
      subst hb
      have e : (BitVec.setWidth (4 * 8) bytes : BitVec 32) = (bytes : BitVec 32) :=
        BitVec.setWidth_eq (bytes : BitVec 32)
      exact ⟨_, (h bytes rfl).trans (congrArg (fun z : BitVec 32 =>
        st ++ [(⟨paZ (bits_of_physaddr paddr), 4, z⟩ : FRd)]) e.symm)⟩

/-- The loop's one-chunk assembly is the chunk (width 2). -/
theorem cmrVal2 (v : BitVec 16) :
    BitVec.setWidth 16 (BitVec.setWidth 16 (BitVec.setWidth 16 (Sail.BitVec.updateSubrange
      (BitVec.setWidth 16 (zeros (n := 16))) 15 0 (BitVec.setWidth 16 v)))) = v := by
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', zeros]
  bv_decide

set_option maxHeartbeats 40000000 in
/-- **`checked_mem_read` of an instruction fetch** (width 2): `Ok d` only after ONE fetch read at
`pa` answering `d`. -/
theorem faCheckedMemRead2 (pbmt : page_based_mem_type) (priv : Privilege) (pa : physaddr)
    (st : List FRd) :
    faB Ann (fun r st' => ∀ d m, r = .Ok (d, m) → st' = st ++ [⟨paZ (bits_of_physaddr pa), 2, d⟩])
      (checked_mem_read (.InstructionFetch ()) pbmt priv pa 2 false false false false) st := by
  simp only [checked_mem_read, SailME.run, PreSail.PreSailME.run, ExceptT.run_bind, run_liftM,
    bind_assoc, pure_bind, ExceptT.run_pure]
  refine faFpBind _ _ _ _ st (fpCheckPmaIFS pbmt priv pa 2 false) (fun r hr => ?_)
  cases r with
  | Err e =>
    simp only [run_SailME_throw, pure_bind]
    intro d m h; cases h
  | Ok info =>
    obtain ⟨hram, hsp⟩ := hr info rfl
    simp only [ExceptT.run_pure, pure_bind, hsp]
    rw [bind_assoc]
    refine faFpBind _ _ _ _ st (fpSplitCannot pa 2 _) (fun p hp => ?_)
    subst hp
    simp only [untilFuelM, misaligned_order, sys_misaligned_order_decreasing,
      Bool.false_eq_true, ↓reduceIte]
    rw [show Int.toNat 1 = 0 + 1 from rfl]
    simp only [untilFuelM.go, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind,
      ]
    refine faFpBind _ _ _ _ st (by fp_walk : fpT (assert true "loop dummy assert")) (fun _ _ => ?_)
    refine faFpBind _ _ _ _ st (fpPmpCheck _ _ _ _) (fun o _ => ?_)
    have hr0 : 0x80000000 ≤ (bits_of_physaddr (physaddr.Physaddr
        (BitVec.addInt (bits_of_physaddr pa) (↑(Int.toNat 0) * ↑2)))).toNat := ramShift0 pa _ hram
    have hd0 : devAddr (BitVec.addInt (bits_of_physaddr pa) (↑(Int.toNat 0) * ↑2)) = false :=
      devShift0 pa _ hram
    cases o with
    | some e =>
      simp only []
      intro d m h; cases h
    | none =>
      simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, 
        ]
      refine faFpBind _ _ _ _ st (fpWithinMmioRam _ _ hr0) (fun b hb => ?_)
      subst hb
      simp only [Bool.false_eq_true, ↓reduceIte, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
      refine faBind _ _ _ _ st (faReadRam _ _ st hd0) (fun r st' hst => ?_)
      subst hst
      have hc : (Int.toNat 0 == (1 - 1 : Int).toNat) = true := by decide
      simp only [hc, ↓reduceIte, pure_bind, ExceptT.run_pure]
      intro d m h
      injection h with h
      injection h with h
      subst h
      rw [SailCycleOrderFp.addInt0]
      obtain ⟨v, u⟩ := r
      show st ++ [⟨paZ (bits_of_physaddr pa), 2, v⟩] = st ++ [⟨paZ (bits_of_physaddr pa), 2,
        BitVec.setWidth 16 (BitVec.setWidth 16 (BitVec.setWidth 16 (Sail.BitVec.updateSubrange
          (BitVec.setWidth 16 (zeros (n := 16))) 15 0 (BitVec.setWidth 16 v))))⟩]
      exact congrArg (fun z : BitVec 16 => st ++ [(⟨paZ (bits_of_physaddr pa), 2, z⟩ : FRd)])
        (cmrVal2 v).symm

set_option maxHeartbeats 40000000 in
/-- **`mem_read` of an instruction fetch** (width 2). -/
theorem faMemRead2 (pbmt : page_based_mem_type) (pa : physaddr) (st : List FRd) :
    faB Ann (fun r st' => ∀ d, r = .Ok d → st' = st ++ [⟨paZ (bits_of_physaddr pa), 2, d⟩])
      (mem_read (.InstructionFetch ()) pbmt pa 2 false false false) st := by
  simp only [mem_read, mem_read_priv, mem_read_priv_meta, bind_assoc, pure_bind]
  refine faFpBind _ _ _ _ st (by fp_walk : fpT (readReg Register.mstatus)) (fun a _ => ?_)
  refine faFpBind _ _ _ _ st (by fp_walk : fpT (readReg Register.cur_privilege)) (fun b _ => ?_)
  refine faFpBind _ _ _ _ st (fpEffectivePrivilege _ _ _) (fun p _ => ?_)
  refine faBind _ _ _ _ st (faCheckedMemRead2 pbmt p pa st) (fun r st' h => ?_)
  intro d hd
  cases r with
  | Ok q =>
    obtain ⟨d', m⟩ := q
    simp only [MemoryOpResult_drop_meta] at hd
    injection hd with hd
    subst hd
    exact h _ m rfl
  | Err e => simp [MemoryOpResult_drop_meta] at hd

set_option maxHeartbeats 40000000 in
/-- **`fetch_bytes`** (width 2): `FetchBytes_Success b` only after ONE fetch read answering `b`. -/
theorem faFetchBytes2 (fs gs : BitVec 64) (st : List FRd) :
    faB Ann (fun r st' => ∀ b, r = .FetchBytes_Success b → ∃ a, st' = st ++ [⟨a, 2, b⟩])
      (fetch_bytes fs gs 2) st := by
  simp only [fetch_bytes, ext_fetch_check_pc, SailME.run, PreSail.PreSailME.run, ExceptT.run_bind,
    run_liftM, bind_assoc, pure_bind]
  refine faFpBind _ _ _ _ st (fpTranslateAddr _ _) (fun r _ => ?_)
  cases r with
  | Err e =>
    simp only [run_SailME_throw, pure_bind]
    intro b hb; cases hb
  | Ok q =>
    obtain ⟨paddr, pbmt, u⟩ := q
    simp only [ExceptT.run_pure, pure_bind, bind_assoc]
    refine faBind _ _ _ _ st (faMemRead2 pbmt paddr st) (fun r st' h => ?_)
    cases r with
    | Err q =>
      obtain ⟨ea, e⟩ := q
      simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, ExceptT.run_pure]
      refine faFpBind _ _ _ _ st' (by fp_walk : fpT (assert (ea == paddr) "postlude/fetch.sail:44.30-44.31"))
        (fun _ _ => ?_)
      intro b hb; cases hb
    | Ok bytes =>
      simp only [ExceptT.run_pure, pure_bind]
      intro b hb
      injection hb with hb
      subst hb
      have e : (BitVec.setWidth (2 * 8) bytes : BitVec 16) = (bytes : BitVec 16) :=
        BitVec.setWidth_eq (bytes : BitVec 16)
      exact ⟨_, (h bytes rfl).trans (congrArg (fun z : BitVec 16 =>
        st ++ [(⟨paZ (bits_of_physaddr paddr), 2, z⟩ : FRd)]) e.symm)⟩

/-! ## 6. The fetch: Sail's four arms -/

/-- Sail's four fetch arms, with the reads' addresses (`Fetch.lean:253-288`): one 4-byte read,
one 2-byte read, two 2-byte reads. -/
inductive FetchShape where
  | s4 (a : Int) (v : BitVec 32)
  | s2 (a : Int) (v : BitVec 16)
  | s22 (a1 a2 : Int) (lo hi : BitVec 16)

/-- The shape's fetch reads, in order. -/
def FetchShape.reads : FetchShape → List FRd
  | .s4 a v => [⟨a, 4, v⟩]
  | .s2 a v => [⟨a, 2, v⟩]
  | .s22 a1 a2 lo hi => [⟨a1, 2, lo⟩, ⟨a2, 2, hi⟩]

/-- **The announced bits of a shape** (`run_hart_active`'s two announces, `Step.lean:335-404`):
a 4-byte read is announced whole when its low halfword is not compressed (`F_Base w`), else by
that halfword (`F_RVC w[15:0]`); a 2-byte read only compressed (`F_RVC h`); two 2-byte reads as
`hi ++ lo` when `lo` is not compressed (`F_Base`). -/
def FetchShape.ann : FetchShape → (n : Nat) → BitVec n → Prop
  | .s4 _ v, n, w =>
      ((⟨n, w⟩ : Σ k, BitVec k) = ⟨32, v⟩ ∧ isRVC (Sail.BitVec.extractLsb v 15 0) = false) ∨
      ((⟨n, w⟩ : Σ k, BitVec k) = ⟨16, Sail.BitVec.extractLsb v 15 0⟩ ∧
        isRVC (Sail.BitVec.extractLsb v 15 0) = true)
  | .s2 _ v, n, w => (⟨n, w⟩ : Σ k, BitVec k) = ⟨16, v⟩ ∧ isRVC v = true
  | .s22 _ _ lo hi, n, w => (⟨n, w⟩ : Σ k, BitVec k) = ⟨32, hi ++ lo⟩ ∧ isRVC lo = false

/-- **THE ANNOUNCE OBLIGATION** of a cycle started with no fetch read: the reads so far are one
shape's, announced as that shape announces. -/
def annOk (st : List FRd) (n : Nat) (w : BitVec n) : Prop :=
  ∃ sh : FetchShape, st = sh.reads ∧ sh.ann n w

/-- The fetch's post: a returned word is a shape's announce over the reads appended. -/
def fetchPost (st : List FRd) (fr : FetchResult) (st' : List FRd) : Prop :=
  match fr with
  | .F_Base w => ∃ sh : FetchShape, st' = st ++ sh.reads ∧ sh.ann 32 w
  | .F_RVC h => ∃ sh : FetchShape, st' = st ++ sh.reads ∧ sh.ann 16 h
  | _ => True

theorem fpReadReg (r : Register) : fpT (readReg r) := by fp_walk

/-- The model's early-return block, run. -/
theorem faRunE {X : Type} (P : X → List FRd → Prop)
    (m : SailM (Except (Sail.Error exception ⊕ X) X)) (st : List FRd)
    (h : faB Ann (fun r st' => match r with
      | .ok x => P x st'
      | .error (.inr x) => P x st'
      | .error (.inl _) => True) m st) :
    faB Ann P (m >>= fun r => match r with
      | .error (.inr e) => pure e
      | .error (.inl e) => throw e
      | .ok e => pure e) st := by
  refine faBind _ P _ _ st h (fun r st' hr => ?_)
  rcases r with (e | e) | e
  · exact trivial
  · exact hr
  · exact hr

theorem runIte {ε X : Type} (c : Prop) [Decidable c] (a b : ExceptT ε SailM X) :
    ExceptT.run (if c then a else b) = if c then ExceptT.run a else ExceptT.run b := by
  split <;> rfl

theorem iteBind {X Y : Type} (c : Prop) [Decidable c] (a b : SailM X) (f : X → SailM Y) :
    ((if c then a else b) >>= f) = if c then a >>= f else b >>= f := by
  split <;> rfl

/-- The fetch's post at the early-return layer. -/
def fetchPostE (st : List FRd) :
    Except (Sail.Error exception ⊕ FetchResult) FetchResult → List FRd → Prop
  | .ok x, st' => fetchPost st x st'
  | .error (.inr x), st' => fetchPost st x st'
  | .error (.inl _), _ => True

theorem faOkLeaf (st st' : List FRd) (x : FetchResult) (h : fetchPost st x st') :
    faB Ann (fetchPostE st) (pure (.ok x)) st' := h

theorem leafS4Base (st : List FRd) (a : Int) (v : BitVec 32)
    (h : ¬ isRVC (Sail.BitVec.extractLsb v 15 0) = true) :
    fetchPost st (.F_Base v) (st ++ [⟨a, 4, v⟩]) :=
  ⟨.s4 a v, rfl, Or.inl ⟨rfl, by simpa only [Bool.not_eq_true] using h⟩⟩

theorem leafS4Rvc (st : List FRd) (a : Int) (v : BitVec 32)
    (h : isRVC (Sail.BitVec.extractLsb v 15 0) = true) :
    fetchPost st (.F_RVC (Sail.BitVec.extractLsb v 15 0)) (st ++ [⟨a, 4, v⟩]) :=
  ⟨.s4 a v, rfl, Or.inr ⟨rfl, h⟩⟩

theorem leafS2 (st : List FRd) (a : Int) (v : BitVec 16) (h : isRVC v = true) :
    fetchPost st (.F_RVC v) (st ++ [⟨a, 2, v⟩]) :=
  ⟨.s2 a v, rfl, rfl, h⟩

theorem leafS22 (st : List FRd) (a1 a2 : Int) (lo hi : BitVec 16) (h : ¬ isRVC lo = true) :
    fetchPost st (.F_Base (hi ++ lo)) (st ++ [⟨a1, 2, lo⟩] ++ [⟨a2, 2, hi⟩]) :=
  ⟨.s22 a1 a2 lo hi, List.append_assoc _ _ _, rfl, by simpa only [Bool.not_eq_true] using h⟩

theorem faFB4 {Y : Type} (P : Y → List FRd → Prop) (fs gs : BitVec 64) (st : List FRd)
    (f : FetchBytes_Result 4 → SailM Y)
    (h : ∀ r st', (∀ b, r = .FetchBytes_Success b → ∃ a, st' = st ++ [⟨a, 4, b⟩]) →
      faB Ann P (f r) st') :
    faB Ann P (fetch_bytes fs gs 4 >>= f) st :=
  faBind _ _ _ _ st (faFetchBytes4 fs gs st) h

theorem faFB2 {Y : Type} (P : Y → List FRd → Prop) (fs gs : BitVec 64) (st : List FRd)
    (f : FetchBytes_Result 2 → SailM Y)
    (h : ∀ r st', (∀ b, r = .FetchBytes_Success b → ∃ a, st' = st ++ [⟨a, 2, b⟩]) →
      faB Ann P (f r) st') :
    faB Ann P (fetch_bytes fs gs 2 >>= f) st :=
  faBind _ _ _ _ st (faFetchBytes2 fs gs st) h

/-- One step of the fetch walk. -/
macro "fa_fetch_step" : tactic => `(tactic| first
  | (simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, ExceptT.run_pure, bindCont_ok,
      bindCont_error, runIte, iteBind, Bool.false_eq_true, ↓reduceIte])
  | (refine faOkLeaf _ _ _ ?_
     first
      | trivial
      | exact leafS4Base _ _ _ (by assumption)
      | exact leafS4Rvc _ _ _ (by assumption)
      | exact leafS2 _ _ _ (by assumption)
      | exact leafS22 _ _ _ _ _ (by assumption))
  | split
  | (refine faFpBind _ _ _ _ _ (fpReadReg _) (fun _ _ => ?_))
  | (refine faFpBind _ _ _ _ _ (fpCurrentlyEnabled _) (fun _ _ => ?_))
  | (apply faFB4
     intro r st' hr
     cases r
     all_goals (try (obtain ⟨_, ha⟩ := hr _ rfl; subst ha)))
  | (apply faFB2
     intro r st' hr
     cases r
     all_goals (try (obtain ⟨_, ha⟩ := hr _ rfl; subst ha))))

set_option maxHeartbeats 40000000 in
/-- **THE FETCH** (header): `fetch ()` returns a word only as one of Sail's four arms over the
fetch reads it makes. -/
theorem faFetch (st : List FRd) : faB Ann (fetchPost st) (fetch ()) st := by
  simp only [fetch, ext_fetch_check_pc, get_config_rvfi, SailME.run, PreSail.PreSailME.run,
    ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, Bool.false_eq_true, ↓reduceIte]
  refine faFpBind _ _ _ _ st (fpReadReg _) (fun _ _ => ?_)
  refine faFpBind _ _ _ _ st (fpReadReg _) (fun _ _ => ?_)
  refine faFpBind _ _ _ _ st (fpReadReg _) (fun pc0 _ => ?_)
  refine faBind (fetchPostE st) _ _ _ st ?_ ?_
  rotate_left
  · intro r st' hr
    rcases r with (e | e) | e
    · exact trivial
    · exact hr
    · exact hr
  repeat' fa_fetch_step

/-! ## 7. The cycle -/

/-- After the step body: `ucFinish`, then the optional tick (footprints: no fetch read, no
announce). -/
theorem faFinishTick (tick : Bool) (s : Step) (st : List FRd) :
    faB annOk (fun _ _ => True)
      (ucFinish s >>= fun _ => if tick then tick_clock () else pure ()) st := by
  refine faFpBind _ _ _ _ st (fpFinish s) (fun _ _ => ?_)
  split
  · exact faFp _ _ _ st fpTickClock (fun _ _ => trivial)
  · exact trivial

/-- The announce node of a returned word, from the fetch's post. -/
theorem faAnnOfPost {Y : Type} (n : Nat) (w : BitVec n) (k : Unit → SailM Y)
    (P : Y → List FRd → Prop) (st : List FRd)
    (h : ∃ sh : FetchShape, st = [] ++ sh.reads ∧ sh.ann n w) :
    faB annOk P (instr_announce w >>= k) st := by
  show faB annOk P (FreeM.impure (.ok (.instrAnnounce n w)) _) st
  obtain ⟨sh, hs, ha⟩ := h
  exact ⟨sh, by simpa using hs, ha⟩

set_option maxHeartbeats 40000000 in
/-- **r1 AT THE TREE (header)**: every Sail cycle, started with no fetch read, announces (if at
all) the bits of one of Sail's four fetch arms over the fetch reads it made, and every fetch
read is a RAM read. -/
theorem faCycle (tick : Bool) : faB annOk (fun _ _ => True) (riscvStep tick) [] := by
  unfold riscvStep
  rw [uc_tryStep_eq]
  simp only [bind_assoc]
  refine faFpBind _ _ _ _ [] fpPrelude (fun hs _ => ?_)
  cases hs with
  | HART_WAITING p =>
    obtain ⟨wr, ib⟩ := p
    simp only [ucBody]
    refine faFpBind _ _ _ _ [] (fpWaiting wr ib) (fun s _ => ?_)
    exact faFinishTick tick s []
  | HART_ACTIVE u =>
    simp only [ucBody]
    rw [uc_runHartActive_eq]
    simp only [bind_assoc]
    refine faFpBind _ _ _ _ [] fpDispatch (fun o _ => ?_)
    cases o with
    | some ip =>
      simp only [pure_bind]
      exact faFinishTick tick _ []
    | none =>
      simp only [bind_assoc]
      refine faBind _ _ _ _ [] (faFetch []) (fun fr st h => ?_)
      cases fr with
      | F_Ext_Error e =>
        simp only [ucAfterFetch, ext_fetch_hook, pure_bind]
        exact faFinishTick tick _ st
      | F_Error p =>
        obtain ⟨e, a⟩ := p
        simp only [ucAfterFetch, ext_fetch_hook, pure_bind]
        exact faFinishTick tick _ st
      | F_RVC hw =>
        simp only [ucAfterFetch, ext_fetch_hook, bind_assoc]
        exact faAnnOfPost 16 hw _ _ st h
      | F_Base w =>
        simp only [ucAfterFetch, ext_fetch_hook, bind_assoc]
        exact faAnnOfPost 32 w _ _ st h

/-! ## 8. Along the hart's real steps -/

open PinDataflow (RbootAll rbootAllSet)

/-- The instruction-fetch labels of a label list, in order: address and byte values. -/
def fetchLbls : List Wlabel → List (Int × List (BitVec 8))
  | [] => []
  | .LIFetch base tvs :: ls => (base, tvs.map Prod.snd) :: fetchLbls ls
  | _ :: ls => fetchLbls ls

/-- A read's address and bytes. -/
def frdView (r : FRd) : Int × List (BitVec 8) := (r.pa, (List.range r.n).map (fun j => nthByte r.v j))

theorem fetchLblsCons (l : Wlabel) (ls : List Wlabel) :
    fetchLbls (l :: ls) = fetchLbls [l] ++ fetchLbls ls := by
  cases l <;> rfl

theorem tvsView {n : Nat} (w : BitVec (8 * n)) (tvs : List (Nat × BitVec 8)) (hl : tvs.length = n)
    (hb : ∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w j)) :
    tvs.map Prod.snd = (List.range n).map (fun j => nthByte w j) := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < n
  · rw [hb j hj, List.getElem?_map, List.getElem?_range hj]; rfl
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

/-- The conclusion of one step: the new tree's state, the fetch labels appended. -/
def faStepOk (P : Unit → List FRd → Prop) (st : List FRd) (l : Wlabel) (m' : SailM Unit)
    (rs' : RegFile) : Prop :=
  ∃ st', faB Ann P m' st' ∧ st'.map frdView = st.map frdView ++ fetchLbls [l] ∧ RbootAll rs'

theorem faStay (P : Unit → List FRd → Prop) (st : List FRd) (l : Wlabel) (m' : SailM Unit)
    (rs : RegFile) (hf : faB Ann P m' st) (hrb : RbootAll rs) (hl : fetchLbls [l] = []) :
    faStepOk (Ann := Ann) P st l m' rs :=
  ⟨st, hf, by rw [hl, List.append_nil], hrb⟩

/-- **One Sail node** (header). -/
theorem faNodeStep (P : Unit → List FRd → Prop) (m : SailM Unit) (rs : RegFile) (ib : Ibch)
    (d : DevStates) (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) (st : List FRd)
    (hstep : pnodeStep m rs ib d l m' ors fn' d' oib obar) (hann : ibnAnn m = false)
    (hf : faB Ann P m st) (hrb : RbootAll rs) : faStepOk (Ann := Ann) P st l m' (ors.getD rs) := by
  match m, hstep with
  | .pure _, _ => simp [ibnAnn] at hann
  | .impure (.error _) _, h => exact h.elim
  | .impure (.ok o) k, h =>
    cases o with
    | regRead r =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact faStay P st _ _ rs (hf (rs r) (hrb r)) hrb rfl
    | regWrite r v =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      refine faStay P st _ _ _ (hf.2 ()) (rbootAllSet rs r v hrb hf.1) ?_
      unfold erwLabel; split <;> rfl
    | memRead n va req =>
      simp only [pnodeStep] at h
      simp only [faB] at hf
      split at h
      · rename_i hd
        obtain ⟨w, -, rfl, rfl, rfl, -, rfl, -⟩ := h
        split at hf
        · exact absurd hf.1 (by rw [hd]; decide)
        · exact faStay P st _ _ rs (hf w) hrb rfl
      · rcases h with ⟨hk, w, tvs, hl, hb, rfl, rfl, rfl, -, -, rfl, -⟩ |
          ⟨hk, ⟨-, w, tvs, -, -, rfl, rfl, rfl, -, -, rfl, -⟩ |
            ⟨-, w, tvs, -, -, rfl, rfl, rfl, -, -, rfl, -⟩⟩
        · rw [if_pos hk] at hf
          refine ⟨_, hf.2 w, ?_, hrb⟩
          simp only [List.map_append, List.map_cons, List.map_nil, fetchLbls, frdView,
            tvsView w tvs hl hb]
        · rw [if_neg (by rw [hk]; decide)] at hf
          exact faStay P st _ _ rs (hf w) hrb rfl
        · rw [if_neg (by rw [hk]; decide)] at hf
          exact faStay P st _ _ rs (hf w) hrb rfl
    | memWrite n va req =>
      simp only [pnodeStep] at h
      split at h
      · split at h
        · obtain ⟨-, rfl, rfl, rfl, -, rfl, -⟩ := h
          exact faStay P st _ _ rs (hf _) hrb rfl
        · exact h.elim
      · split at h
        · obtain ⟨-, h⟩ := h
          rcases h with ⟨-, rfl, rfl, rfl, -, -, rfl, -⟩ |
            ⟨-, ⟨rfl, rfl, rfl, -, -, rfl, -⟩ | ⟨rfl, rfl, rfl, -, -, rfl, -⟩⟩
          · exact faStay P st _ _ rs (hf _) hrb rfl
          · exact faStay P st _ _ rs (hf _) hrb rfl
          · exact faStay P st _ _ rs hf hrb rfl
        · exact h.elim
    | barrier b =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      refine faStay P st _ _ rs (hf ()) hrb ?_
      unfold ebarLabel; split <;> rfl
    | instrAnnounce n w => simp [ibnAnn] at hann
    | choose s =>
      obtain ⟨ch, rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact faStay P st _ _ rs (hf ch) hrb rfl
    | readRam => exact h.elim
    | writeRam => exact h.elim
    | getCycleCount =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact faStay P st _ _ rs (hf _) hrb rfl
    | branchAnnounce =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact faStay P st _ _ rs (hf _) hrb rfl
    | cacheOp =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact faStay P st _ _ rs (hf _) hrb rfl
    | tlbi =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact faStay P st _ _ rs (hf _) hrb rfl
    | takeException =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact faStay P st _ _ rs (hf _) hrb rfl
    | returnException =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact faStay P st _ _ rs (hf _) hrb rfl
    | translationStart =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact faStay P st _ _ rs (hf _) hrb rfl
    | translationEnd =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact faStay P st _ _ rs (hf _) hrb rfl
    | cycleCount =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact faStay P st _ _ rs (hf _) hrb rfl
    | message =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact faStay P st _ _ rs (hf _) hrb rfl

/-- **One hart step** (header): a node, a parked fence, or a PLIC wire write. -/
theorem faHwStep (P : Unit → List FRd → Prop) (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (l : Wlabel) (rds : List Nat)
    (ws : List Register) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : Efab) (oib : Option Ibch)
    (obar : Option barrier_kind) (st : List FRd)
    (hstep : pstepHw cpu m rs fn ib d l rds ws false m' ors fn' d' oib obar)
    (hf : faB Ann P m st) (hrb : RbootAll rs) : faStepOk (Ann := Ann) P st l m' (ors.getD rs) := by
  rcases hstep with ⟨-, ⟨H, -⟩, -, -, hann⟩ | ⟨pr, pw, sr, sw, rfl, ⟨H, -⟩, -, -, -⟩ | ⟨H, -, -, -⟩
  · exact faNodeStep P m rs ib _ l m' ors fn' _ oib obar st H hann.symm hf hrb
  · obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := H
    exact faStay P st _ _ rs hf hrb rfl
  · obtain ⟨mm, b, k, -, rfl, rfl, -, -, rfl, -, rfl⟩ := H
    refine faStay P st _ _ _ hf ?_ rfl
    unfold pinSet
    split
    · exact rbootAllSet rs _ _ hrb trivial
    · exact rbootAllSet rs _ _ hrb trivial

/-- **The run** (header): along a hart run with no boundary or announce step, the state grows by
the run's fetch labels. -/
theorem faPhrun (P : Unit → List FRd → Prop) (cpu : CPU) (ls : List Wlabel) (rds : List Nat)
    (ws : List Register) (ann : Bool) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (m' : SailM Unit)
    (rs' : RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (ib' : Ibch) (d' : Efab) :
    phrun cpu ls rds ws ann m rs fn ib d m' rs' fn' ib' d' → ann = false →
    ∀ st, faB Ann P m st → RbootAll rs →
    ∃ st', faB Ann P m' st' ∧ st'.map frdView = st.map frdView ++ fetchLbls ls ∧ RbootAll rs' := by
  intro h
  induction h with
  | nil m rs fn ib d =>
    intro _ st hf hrb
    exact ⟨st, hf, by simp [fetchLbls], hrb⟩
  | @more l ls rds rds' ws ws' ann ann' m rs fn ib d m1 ors fn1 oib obar d1 m2 rs2 fn2 ib2 d2
      hstep _ ih =>
    intro hann st hf hrb
    rw [Bool.or_eq_false_iff] at hann
    obtain ⟨ha1, ha2⟩ := hann
    subst ha1
    obtain ⟨st1, hf1, hv1, hrb1⟩ :=
      faHwStep P cpu m rs fn ib d l rds ws m1 ors fn1 d1 oib obar st hstep hf hrb
    obtain ⟨st2, hf2, hv2, hrb2⟩ := ih ha2 st1 hf1 hrb1
    refine ⟨st2, hf2, ?_, hrb2⟩
    rw [hv2, hv1, fetchLblsCons l ls, List.append_assoc]

/-- **r1, THE RUN FORM (header)**: a hart run from a cycle start `riscvStep tick` (boot-admitted
register file) to an announce node, with no boundary or announce step before it, announces the
bits of one of Sail's four fetch arms over the run's OWN instruction-fetch labels. -/
theorem fetchAnnOfRun (cpu : CPU) (tick : Bool) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (ls : List Wlabel)
    (n : Nat) (w : BitVec n) (k : Unit → SailM Unit) (rs2 : RegFile)
    (fn2 : Option (Bool × Bool × Bool × Bool)) (ib2 : Ibch) (d2 : Efab) :
    RbootAll rs →
    pevrun ls (.PHart cpu (riscvStep tick) rs fn ib) d
      (.PHart cpu (.impure (.ok (.instrAnnounce n w)) k) rs2 fn2 ib2) d2 →
    Wlabel.LInstr ∉ ls → Wlabel.LFence false false false false ∉ ls →
    ∃ sh : FetchShape, sh.reads.map frdView = fetchLbls ls ∧ sh.ann n w := by
  intro hrb hrun hni hnf
  obtain ⟨rds, ws, ann, hh⟩ := pevrunPhrun ls _ d _ d2 hrun cpu _ rs fn ib _ rs2 fn2 ib2 rfl rfl
  have ha := phrunNoInstr cpu ls rds ws ann _ rs fn ib d _ rs2 fn2 ib2 d2 hh hni hnf
  obtain ⟨st, hf, hv, -⟩ := faPhrun (Ann := annOk) (fun _ _ => True) cpu ls rds ws ann _ rs fn ib d
    _ rs2 fn2 ib2 d2 hh ha [] (faCycle tick) hrb
  obtain ⟨sh, rfl, hann⟩ := hf
  exact ⟨sh, by simpa using hv, hann⟩

end PinFetchVal
end Weak