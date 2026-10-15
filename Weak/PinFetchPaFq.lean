/-
Weak: **r2 glue (C) — THE FETCH'S ADDRESSES: `fqB` on `fetch ()`** (`PROGRESS-r2glue.md`).
Lean-only.

`fqB c D pc P m i` is an all-paths predicate on a Sail tree whose state `i` counts the
instruction-fetch reads made so far:
* a register read is answered by any value the fetch translation's filter `tvRk c` admits, `PC`
  by `pc` (both justified at the product with the cycle predicate by the MIRROR: `PC` is
  protected before the fetch, `satp`/`tlb` kept by the predicate's own writes);
* a register write writes a `tvRk c`-admitted value;
* an instruction-fetch read is a RAM read AT `pc + 2i` (an obligation) and counts; any other read
  is answered by a value the answer filter `D` admits (the walks' PTE slots, `tvAns`);
* there is no announce; every other node continues for every answer.
The headline `fqFetch`: `fetch ()` (`Fetch.lean:233-288`), started with no fetch read at
`PC = pc` in a kernel-text page, makes its `k`-th fetch read at `pc + 2k` — the translation of `PC`
and of `PC + 2` is the identity (`tvTranslateAddrFetch`, configurations `c1`/`c2`, one register
filter for both: `TCfg.vs`).  Every helper is `Weak.PinFetchPa.*`.
-/
import Weak.PinFetchPaCy
import Weak.PinFetchPaAddr
import Weak.PinFetchVal
import Weak.PinCycRunMem

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinFetchPa
open SailCycleOrderK SailCycleOrderFp PinFetchPaFp
open PinCycRunFp (pfB pfProt pfRegOk pfW)

/-! ## 1. The predicate and its kit -/

/-- **THE FETCH-ADDRESS PREDICATE** (header). -/
def fqB (c : TCfg) (D : BitVec 64 → (n : Nat) → BitVec (8 * n) → Prop) (pc : Int) {X : Type}
    (P : X → Nat → Prop) : SailM X → Nat → Prop
  | .pure x, i => P x i
  | .impure (.error _) _, _ => True
  | .impure (.ok o) k, i =>
    match o, k with
    | .memRead n _ req, k =>
        ((classify req.access_kind).akIfetch = true → devAddr req.pa = false ∧
          paZ req.pa = pc + 2 * (i : Int) ∧ ∀ w : BitVec (8 * n), fqB c D pc P (k (.Ok (w, none))) (i + 1)) ∧
        ((classify req.access_kind).akIfetch = false →
          ∀ w : BitVec (8 * n), D req.pa n w → fqB c D pc P (k (.Ok (w, none))) i)
    | .instrAnnounce .., _ => False
    | .regRead r, k => ∀ v, tvRk c r v →
        (∀ h : r = .PC, cast (congrArg RegisterType h) v = BitVec.ofInt 64 pc) → fqB c D pc P (k v) i
    | .regWrite r v, k => tvRk c r v ∧ ∀ u, fqB c D pc P (k u) i
    | .barrier _, k => ∀ v, fqB c D pc P (k v) i
    | .memWrite .., k => ∀ v, fqB c D pc P (k v) i
    | .branchAnnounce .., k => ∀ v, fqB c D pc P (k v) i
    | .cacheOp _, k => ∀ v, fqB c D pc P (k v) i
    | .tlbi _, k => ∀ v, fqB c D pc P (k v) i
    | .takeException _, k => ∀ v, fqB c D pc P (k v) i
    | .returnException _, k => ∀ v, fqB c D pc P (k v) i
    | .translationStart _, k => ∀ v, fqB c D pc P (k v) i
    | .translationEnd _, k => ∀ v, fqB c D pc P (k v) i
    | .cycleCount, k => ∀ v, fqB c D pc P (k v) i
    | .getCycleCount, k => ∀ v, fqB c D pc P (k v) i
    | .message _, k => ∀ v, fqB c D pc P (k v) i
    | .choose _, k => ∀ v, fqB c D pc P (k v) i
    | .readRam .., k => ∀ v, fqB c D pc P (k v) i
    | .writeRam .., k => ∀ v, fqB c D pc P (k v) i

section kit
variable {c : TCfg} {D : BitVec 64 → (n : Nat) → BitVec (8 * n) → Prop} {pc : Int}

theorem fqBind {X Y : Type} (Q : X → Nat → Prop) (P : Y → Nat → Prop) (m : SailM X)
    (f : X → SailM Y) :
    ∀ i, fqB c D pc Q m i → (∀ x i', Q x i' → fqB c D pc P (f x) i') → fqB c D pc P (m >>= f) i := by
  induction m with
  | pure y => intro i hm hf; exact hf y i hm
  | impure call k ih =>
    intro i hm hf
    cases call with
    | error e => trivial
    | ok o =>
      show fqB c D pc P (FreeM.impure (.ok o) (fun v => k v >>= f)) i
      cases o
      case memRead =>
        exact ⟨fun h => ⟨(hm.1 h).1, (hm.1 h).2.1, fun w => ih _ _ ((hm.1 h).2.2 w) hf⟩,
          fun h w hd => ih _ _ (hm.2 h w hd) hf⟩
      case instrAnnounce => exact hm
      case regRead => exact fun v hv hp => ih v _ (hm v hv hp) hf
      case regWrite => exact ⟨hm.1, fun u => ih u _ (hm.2 u) hf⟩
      all_goals exact fun v => ih v _ (hm v) hf

theorem fqMono {X : Type} (P P' : X → Nat → Prop) (hP : ∀ x i, P x i → P' x i) :
    ∀ (m : SailM X) i, fqB c D pc P m i → fqB c D pc P' m i := by
  intro m
  induction m with
  | pure y => exact fun i h => hP y i h
  | impure call k ih =>
    intro i hm
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case memRead =>
        exact ⟨fun h => ⟨(hm.1 h).1, (hm.1 h).2.1, fun w => ih _ _ ((hm.1 h).2.2 w)⟩,
          fun h w hd => ih _ _ (hm.2 h w hd)⟩
      case instrAnnounce => exact hm
      case regRead => exact fun v hv hp => ih v _ (hm v hv hp)
      case regWrite => exact ⟨hm.1, fun u => ih u _ (hm.2 u)⟩
      all_goals exact fun v => ih v _ (hm v)

/-- **The `xf` lift**: no fetch read, no `satp`/`tlb` write — the count kept. -/
theorem fqOfXf {X : Type} (S : X → Prop) :
    ∀ (m : SailM X) i, xf S m → fqB c D pc (fun x i' => S x ∧ i' = i) m i := by
  intro m
  induction m with
  | pure y => intro i h; exact ⟨h, rfl⟩
  | impure call k ih =>
    intro i hm
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case memRead n va req =>
        obtain ⟨hif, hk⟩ := hm
        refine ⟨fun h2 => ?_, fun _ w _ => ih _ i (hk _)⟩
        exact absurd h2 (by simp only [PinFetchPaFp.ifOk] at hif; simp [classify, hif])
      case instrAnnounce => exact hm.elim
      case barrier => exact fun v => ih v i hm.2
      case regRead r => exact fun v hv _ => ih v i (hm v hv.1)
      case regWrite r v => exact ⟨tvRkOfW c r v hm.1, fun u => ih u i (hm.2 u)⟩
      all_goals exact fun v => ih v i (hm v)

theorem fqXfBind {X Y : Type} (S : X → Prop) (P : Y → Nat → Prop) (m : SailM X) (f : X → SailM Y)
    (i : Nat) (hm : xf S m) (hf : ∀ x, S x → fqB c D pc P (f x) i) : fqB c D pc P (m >>= f) i :=
  fqBind _ P m f i (fqOfXf S m i hm) (fun x i' h => h.2 ▸ hf x h.1)

/-- **The translation lift**: the fetch translation's value predicate at a configuration `c'`
whose register filter is `c`'s (`TCfg.vs`), and w1's strict frame footprint (no fetch read). -/
theorem fqOfTvPf (c' : TCfg) (hR : ∀ r v, tvRk c r v → tvRk c' r v) (hW : ∀ r v, tvRk c' r v → tvRk c r v)
    (hD : ∀ pa n w, D pa n w → tvAns c' pa n w) {X : Type} (P S : X → Prop) :
    ∀ (m : SailM X) i, tvB c' P m → pfB false S m → fqB c D pc (fun x i' => P x ∧ S x ∧ i' = i) m i := by
  intro m
  induction m with
  | pure y => intro i h hp; exact ⟨h, hp, rfl⟩
  | impure call k ih =>
    intro i ht hp
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case memRead n va req =>
        obtain ⟨hif, hk⟩ := hp
        refine ⟨fun h2 => ?_, fun _ w hd => ih _ i (ht w (hD _ _ _ hd)) (hk _)⟩
        exact absurd h2 (by simp only [PinCycRunFp.ifOk] at hif; simp [classify, hif])
      case instrAnnounce => exact hp.elim
      case barrier => exact fun v => ih v i (ht v) hp.2
      case regRead r => exact fun v hv _ => ih v i (ht v (hR r v hv)) (hp v hv.1)
      case regWrite r v => exact ⟨hW r v ht.1, fun u => ih u i (ht.2 u) (hp.2 u)⟩
      all_goals exact fun v => ih v i (ht v) (hp v)

/-- A `PC` read answers `pc`. -/
theorem fqReadPC {Y : Type} (P : Y → Nat → Prop) (f : BitVec 64 → SailM Y) (i : Nat)
    (h : fqB c D pc P (f (BitVec.ofInt 64 pc)) i) : fqB c D pc P (readReg .PC >>= f) i := by
  intro v _ hpc
  have e : v = BitVec.ofInt 64 pc := hpc rfl
  subst e
  exact h

end kit

/-- W-SCO's strict footprint with a post, and the `satp`/`tlb`-free footprint, make an `xf` fact
with the post. -/
theorem xfOfFpXfT {X : Type} (S : X → Prop) :
    ∀ m : SailM X, SailCycleOrderFp.fp S m → xfT m → xf S m := by
  intro m
  induction m with
  | pure x => intro h _; exact h
  | impure call k ih =>
    intro hp hx
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case memRead => exact ⟨hx.1, fun v => ih _ (hp.2 v) (hx.2 v)⟩
      case barrier => exact ⟨hx.1, ih _ hp.2 hx.2⟩
      case instrAnnounce => exact hx.elim
      case regRead => exact fun v hv => ih v (hp v hv) (hx v hv)
      case regWrite => exact ⟨hx.1, fun u => ih u (hp.2 u) (hx.2 u)⟩
      all_goals exact fun v => ih v (hp v) (hx v)

/-! ## 2. The i-cache read chain -/

section chain
variable {c : TCfg} {D : BitVec 64 → (n : Nat) → BitVec (8 * n) → Prop} {pc : Int}

/-- **The i-cache read** at `pc + 2i`. -/
theorem fqReadRamIF (pa : BitVec 64) (n : Nat) (i : Nat) (hd : devAddr pa = false)
    (ha : paZ pa = pc + 2 * (i : Int)) :
    fqB c D pc (fun _ i' => i' = i + 1) (read_ram .Read_ifetch (.Physaddr pa) n false) i := by
  simp only [read_ram, PreSail.sail_mem_read, PreSail.emit, pure_bind]
  show fqB c D pc _ (FreeM.impure (Except.ok (Outcome.memRead n 64 _)) _) i
  refine ⟨fun _ => ⟨hd, ha, fun w => rfl⟩, fun h => ?_⟩
  simp only [classifyIfetch] at h
  cases h

set_option maxHeartbeats 40000000 in
/-- **`checked_mem_read` of an instruction fetch** at `pa = pc + 2i`: `Ok` only after ONE read. -/
theorem fqCheckedMemReadIF (pbmt : page_based_mem_type) (priv : Privilege) (pa : physaddr) (w : Nat)
    (i : Nat) (ha : paZ (bits_of_physaddr pa) = pc + 2 * (i : Int)) :
    fqB c D pc (fun r i' => ∀ d m, r = .Ok (d, m) → i' = i + 1)
      (checked_mem_read (.InstructionFetch ()) pbmt priv pa w false false false false) i := by
  simp only [checked_mem_read, SailME.run, PreSail.PreSailME.run, ExceptT.run_bind, run_liftM,
    bind_assoc, pure_bind, ExceptT.run_pure]
  refine fqXfBind _ _ _ _ i (xfOfFpXfT _ _ (PinFetchVal.fpCheckPmaIFS pbmt priv pa w false)
    (xfCheckPmaPmp _ _ _ _ _ _)) (fun r hr => ?_)
  cases r with
  | Err e =>
    simp only [run_SailME_throw, pure_bind]
    intro d m h; cases h
  | Ok info =>
    obtain ⟨hram, hsp⟩ := hr info rfl
    simp only [ExceptT.run_pure, pure_bind, hsp]
    rw [bind_assoc]
    refine fqXfBind _ _ _ _ i (xfOfFpXfT _ _ (PinFetchVal.fpSplitCannot pa w _)
      (by unfold split_misaligned; xf_walk)) (fun p hp => ?_)
    subst hp
    simp only [untilFuelM, misaligned_order, sys_misaligned_order_decreasing,
      Bool.false_eq_true, ↓reduceIte]
    rw [show Int.toNat 1 = 0 + 1 from rfl]
    simp only [untilFuelM.go, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
    refine fqXfBind _ _ _ _ i (by xf_walk : xfT (assert true "loop dummy assert")) (fun _ _ => ?_)
    refine fqXfBind _ _ _ _ i (xfPmpCheck _ _ _ _) (fun o _ => ?_)
    have hr0 := ramShift0 pa (w : Int) hram
    have hd0 := devShift0 pa (w : Int) hram
    cases o with
    | some e =>
      simp only []
      intro d m h; cases h
    | none =>
      simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
      refine fqXfBind _ _ _ _ i (xfWithinMmioRam _ _ hr0) (fun b hb => ?_)
      subst hb
      simp only [Bool.false_eq_true, ↓reduceIte, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
      refine fqBind _ _ _ _ i (fqReadRamIF _ _ i hd0 (by rw [addInt0]; exact ha)) (fun r i' hi => ?_)
      subst hi
      have hc : (Int.toNat 0 == (1 - 1 : Int).toNat) = true := by decide
      simp only [hc, ↓reduceIte, pure_bind, ExceptT.run_pure]
      intro d m _; rfl

set_option maxHeartbeats 40000000 in
/-- **`mem_read` of an instruction fetch** at `pa = pc + 2i`. -/
theorem fqMemReadIF (pbmt : page_based_mem_type) (pa : physaddr) (w : Nat) (i : Nat)
    (ha : paZ (bits_of_physaddr pa) = pc + 2 * (i : Int)) :
    fqB c D pc (fun r i' => ∀ d, r = .Ok d → i' = i + 1)
      (mem_read (.InstructionFetch ()) pbmt pa w false false false) i := by
  simp only [mem_read, mem_read_priv, mem_read_priv_meta, bind_assoc, pure_bind]
  refine fqXfBind _ _ _ _ i (by xf_walk : xfT (readReg Register.mstatus)) (fun a _ => ?_)
  refine fqXfBind _ _ _ _ i (by xf_walk : xfT (readReg Register.cur_privilege)) (fun b _ => ?_)
  refine fqXfBind _ _ _ _ i (xfEffectivePrivilege _ _ _) (fun p _ => ?_)
  refine fqBind _ _ _ _ i (fqCheckedMemReadIF pbmt p pa w i ha) (fun r i' h => ?_)
  intro d hd
  cases r with
  | Ok q =>
    obtain ⟨d', m⟩ := q
    exact h _ m rfl
  | Err e => simp [MemoryOpResult_drop_meta] at hd

/-- A fetch configuration for `gs` under the register filter `c` and the answer filter `D`. -/
def fqCfg (c : TCfg) (D : BitVec 64 → (n : Nat) → BitVec (8 * n) → Prop) (gs : BitVec 64)
    (c' : TCfg) : Prop :=
  c'.ram ∧ c'.b.toNat < 2 ^ 31 ∧ gs.toNat < 2 ^ 38 ∧ c'.vpn = vpnOf gs ∧
  (∀ r v, tvRk c r v → tvRk c' r v) ∧ (∀ r v, tvRk c' r v → tvRk c r v) ∧
  (∀ pa n w, D pa n w → tvAns c' pa n w)

set_option maxHeartbeats 40000000 in
/-- **`fetch_bytes`** at a granule `gs = pc + 2i` of a kernel-text page: `Success` only after ONE
fetch read, at `pc + 2i`. -/
theorem fqFetchBytes (fs gs : BitVec 64) (w : Nat) (i : Nat) (c' : TCfg) (hc : fqCfg c D gs c')
    (hgs : (gs.toNat : Int) = pc + 2 * (i : Int)) :
    fqB c D pc (fun r i' => ∀ b, r = .FetchBytes_Success b → i' = i + 1) (fetch_bytes fs gs w) i := by
  obtain ⟨hr, hb, hlt, hv, hR, hW, hD⟩ := hc
  simp only [fetch_bytes, ext_fetch_check_pc, SailME.run, PreSail.PreSailME.run, ExceptT.run_bind,
    run_liftM, bind_assoc, pure_bind]
  refine fqBind _ _ _ _ i (fqOfTvPf c' hR hW hD _ _ _ i (tvTranslateAddrFetch c' hr hb gs hlt hv)
    (PinCycRunFp.pfTranslateAddr _ _)) (fun r i' hr' => ?_)
  obtain ⟨hpa, -, hi⟩ := hr'
  subst i'
  cases r with
  | Err e =>
    simp only [run_SailME_throw, pure_bind]
    intro b hb; cases hb
  | Ok q =>
    obtain ⟨paddr, pbmt, u⟩ := q
    obtain rfl := hpa _ _ _ rfl
    simp only [ExceptT.run_pure, pure_bind, bind_assoc]
    refine fqBind _ _ _ _ i (fqMemReadIF pbmt _ w i (by simpa [paZ, bits_of_physaddr] using hgs))
      (fun r i' h => ?_)
    cases r with
    | Err q =>
      obtain ⟨ea, e⟩ := q
      simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, ExceptT.run_pure]
      refine fqXfBind _ _ _ _ i' (by xf_walk : xfT (assert (ea == physaddr.Physaddr gs) "postlude/fetch.sail:44.30-44.31"))
        (fun _ _ => ?_)
      intro b hb; cases hb
    | Ok bytes =>
      simp only [ExceptT.run_pure, pure_bind]
      intro b _
      exact h bytes rfl

end chain

end PinFetchPa
end Weak
