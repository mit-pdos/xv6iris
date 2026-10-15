/-
Weak: **W11-C2′ (a3) relArmed — the fetch under `amB`** (`PROGRESS-relArmed.md`).  Lean-only.

* §1 the relaxed `zfB` footprint of `fetch ()` (`zfFetch`, the `zfB` twin of w1's `pfFetch`): no
  protected register write, no plain RAM store (the page walk's A/D write-back is exclusive),
  never `F_Ext_Error`;
* §2 the product `amOfFaZf`: W5's fetch-value predicate (`PinFetchVal.faB`) × the relaxed
  footprint ⇒ `amB`, the value post read on the logged reads (the twin of w1's `cyOfFaPf`);
* §3 `amFetch`: from an empty log, `fetch ()` under `amB` returns the arm `fetchShapeOk pc`
  names over its log, keeps the AMO bit and never lowers the flag.

Every helper is `Weak.PinRelArmFetch.*` / `Weak.PinRelArm.*`.
-/
import Weak.PinRelArmCy

namespace Weak
open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
namespace PinRelArmFp
open SailCycleOrderK

/-! ## 1. The relaxed `zfB` footprint of `fetch ()` -/

set_option maxHeartbeats 4000000 in
@[zf_reg] theorem PinRelArmFetch.zfReadRamB (rk : read_kind) (pa : physaddr) (w : Nat) (m : Bool) :
    zfB true (fun _ => True) (read_ram rk pa w m) := by
  unfold read_ram
  zf_walk

set_option maxHeartbeats 8000000 in
@[zf_reg] theorem PinRelArmFetch.zfCheckedMemReadB (acc : MemoryAccessType mem_payload)
    (pbmt : page_based_mem_type) (priv : Privilege) (pa : physaddr) (w : Nat) (aq rl res m : Bool) :
    zfB true (fun _ => True) (checked_mem_read acc pbmt priv pa w aq rl res m) := by
  unfold checked_mem_read
  zf_walk

set_option maxHeartbeats 8000000 in
@[zf_reg] theorem PinRelArmFetch.zfMemReadB (acc : MemoryAccessType mem_payload)
    (pbmt : page_based_mem_type) (pa : physaddr) (w : Nat) (aq rl res : Bool) :
    zfB true (fun _ => True) (mem_read acc pbmt pa w aq rl res) := by
  unfold mem_read mem_read_priv mem_read_priv_meta
  zf_walk

set_option maxHeartbeats 8000000 in
@[zf_reg] theorem PinRelArmFetch.zfFetchBytes (fs gs : BitVec 64) (w : Nat) :
    zfB true PinCycRunFp.PinCycRunFetch.fbOk (fetch_bytes fs gs w) := by
  simp only [fetch_bytes, ext_fetch_check_pc, SailME.run, PreSail.PreSailME.run, ExceptT.run_bind,
    run_liftM, bind_assoc, pure_bind]
  refine zfBBindQ true _ _ _ _ (zfRelax _ _ (zfTranslateAddr _ _)) (fun r _ => ?_)
  cases r with
  | Err e =>
    simp only [run_SailME_throw, pure_bind]
    exact trivial
  | Ok q =>
    obtain ⟨paddr, pbmt, u⟩ := q
    simp only [ExceptT.run_pure, pure_bind, bind_assoc]
    refine zfBBindQ true _ _ _ _ (PinRelArmFetch.zfMemReadB _ _ _ _ _ _ _) (fun r _ => ?_)
    cases r with
    | Err q =>
      obtain ⟨ea, e⟩ := q
      simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, ExceptT.run_pure]
      refine zfBBindQ true _ _ _ _
        (zfRelax _ _ (by zf_walk : zfT (assert (ea == paddr) "postlude/fetch.sail:44.30-44.31")))
        (fun _ _ => ?_)
      exact trivial
    | Ok bytes =>
      simp only [ExceptT.run_pure, pure_bind]
      exact trivial

theorem PinRelArmFetch.zfReadReg (r : Register) : zfT (readReg r) := by zf_walk

/-- One step of the fetch walk (W5's `fa_fetch_step`, for `zfB`). -/
macro "zf_fetch_step" : tactic => `(tactic| first
  | (simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, ExceptT.run_pure,
      PinFetchVal.runIte, PinFetchVal.iteBind, Bool.false_eq_true, ↓reduceIte])
  | exact trivial
  | split
  | (refine zfBBindQ true _ _ _ _ (zfRelax _ _ (PinRelArmFetch.zfReadReg _)) (fun _ _ => ?_))
  | (refine zfBBindQ true _ _ _ _ (zfRelax _ _ (zfCurrentlyEnabled _)) (fun _ _ => ?_))
  | (refine zfBBindQ true _ _ _ _ (PinRelArmFetch.zfFetchBytes _ _ _) (fun r hr => ?_)
     cases r
     all_goals try (exact (hr : False).elim)))

set_option maxHeartbeats 40000000 in
/-- **THE FETCH'S FRAME** (header): `fetch ()` writes no protected register (`zfProt`), every
written value is `Rboot`-admitted, and the answer is never `F_Ext_Error`. -/
theorem PinRelArmFetch.zfFetch : zfB true PinCycRunFp.PinCycRunFetch.frOk (fetch ()) := by
  simp only [fetch, ext_fetch_check_pc, get_config_rvfi, SailME.run, PreSail.PreSailME.run,
    ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, Bool.false_eq_true, ↓reduceIte]
  refine zfBBindQ true _ _ _ _ (zfRelax _ _ (PinRelArmFetch.zfReadReg _)) (fun _ _ => ?_)
  refine zfBBindQ true _ _ _ _ (zfRelax _ _ (PinRelArmFetch.zfReadReg _)) (fun _ _ => ?_)
  refine zfBBindQ true _ _ _ _ (zfRelax _ _ (PinRelArmFetch.zfReadReg _)) (fun _ _ => ?_)
  refine zfBBindQ true PinCycRunFp.PinCycRunFetch.frOkE _ _ _ ?_ ?_
  rotate_left
  · intro r hr
    rcases r with (e | e) | e
    · exact trivial
    · exact hr
    · exact hr
  repeat' zf_fetch_step

end PinRelArmFp

/-! ## 2. The product: W5's value chain × the relaxed footprint ⇒ `amB` -/

namespace PinRelArm
open SailCycleOrderK PinCycRun PinFetchVal PinRelArmFp

/-- The fetch's frame under `amB`: the AMO bit kept, the flag never lowered, the log invariant
kept. -/
def amFr (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (st st' : AmSt) : Prop :=
  st'.amo = st.amo ∧ (st.armed = true → st'.armed = true) ∧
  (PinCycRunFetch.logOk A Aa st.fe → PinCycRunFetch.logOk A Aa st'.fe)

theorem amFrRefl (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (st : AmSt) : amFr A Aa st st :=
  ⟨rfl, id, id⟩

theorem amFrTrans (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (s1 s2 s3 : AmSt)
    (h1 : amFr A Aa s1 s2) (h2 : amFr A Aa s2 s3) : amFr A Aa s1 s3 :=
  ⟨h2.1.trans h1.1, fun h => h2.2.1 (h1.2.1 h), fun h => h2.2.2 (h1.2.2 h)⟩

set_option maxHeartbeats 4000000 in
/-- **THE PRODUCT** (header): W5's fetch-value predicate (no announce) × the relaxed `zfB`
footprint, started with no AMO announced, give `amB`. -/
theorem amOfFaZf {X : Type} (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop)
    (P : X → List FRd → Prop) (Pf : X → Prop) (Q : X → AmSt → Prop) :
    ∀ (m : SailM X) (st : AmSt),
      faB (fun _ _ _ => False) P m (st.fe.map PinCycRunFetch.feView) → zfB true Pf m →
      st.amo = false →
      (∀ x st', P x (st'.fe.map PinCycRunFetch.feView) → Pf x → amFr A Aa st st' → Q x st') →
      amB A Aa Q m st := by
  intro m
  induction m with
  | pure x =>
    intro st hfa hp _ hq
    exact hq x st hfa hp (amFrRefl A Aa st)
  | impure call k ih =>
    intro st hfa hp ha hq
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead r => exact fun v hb _ => ih v st (hfa v hb) (hp v hb) ha hq
      case regWrite r v =>
        exact fun _ => ⟨hfa.1, zfDref r hp.1.2, fun u => ih u st (hfa.2 u) (hp.2 u) ha hq⟩
      case memRead n va req =>
        refine ⟨fun hdev hif hA w hw => ?_, fun h w => ?_⟩
        · have hfa' := hfa
          simp only [faB, hif, ↓reduceIte] at hfa'
          have hv : (amFe st (paZ req.pa) n w).fe.map PinCycRunFetch.feView =
              st.fe.map PinCycRunFetch.feView ++ [⟨paZ req.pa, n, w⟩] := by
            simp [amFe, PinCycRunFetch.feView]
          have hfr : amFr A Aa st (amFe st (paZ req.pa) n w) :=
            ⟨rfl, id, fun hl => PinCycRunFetch.logOkSnoc A Aa st.fe _ n w hl hA hw⟩
          exact ih _ (amFe st (paZ req.pa) n w) (hv ▸ hfa'.2 w) (hp.2 _) ha
            (fun x st' e1 e2 e3 => hq x st' e1 e2 (amFrTrans A Aa _ _ _ hfr e3))
        · cases hif : (classify req.access_kind).akIfetch with
          | true =>
            have hfa' := hfa
            simp only [faB, hif, ↓reduceIte] at hfa'
            exact absurd (h hfa'.1) (by rw [hif]; decide)
          | false =>
            have hfa' := hfa
            simp only [faB, hif, Bool.false_eq_true, ↓reduceIte] at hfa'
            exact ih _ st (hfa' w) (hp.2 _) ha hq
      case memWrite n va req =>
        obtain ⟨hw, hk⟩ := hp
        refine ⟨fun _ => ih _ st (hfa _) (hk _) ha hq, fun h1 h2 => ?_, fun _ _ => ?_⟩
        · rcases hw with h | h
          · rw [h1] at h; cases h
          · rw [h2] at h; cases h
        · have e : { st with armed := st.armed && !st.amo } = st := by
            cases st; simp only at ha ⊢; rw [ha]; simp
          rw [e]
          exact ih _ st (hfa _) (hk _) ha hq
      case instrAnnounce => exact hfa.elim
      case barrier b =>
        exact ih _ _ (hfa ()) hp.2 ha (fun x st' e1 e2 e3 => hq x st' e1 e2
          ⟨e3.1, fun h => e3.2.1 (armBarMono b _ h), e3.2.2⟩)
      case getCycleCount => exact ih _ st (hfa _) (hp _) ha hq
      all_goals exact fun v => ih v st (hfa v) (hp v) ha hq

/-! ## 3. The fetch -/

/-- The fetch's post under `amB` at `pc`: the arm of the log, the AMO bit kept, the flag never
lowered, every logged byte `kA`-admitted. -/
def fetchPostAm (pc : Int) (st : AmSt) (fr : FetchResult) (st' : AmSt) : Prop :=
  fetchShapeOk pc fr st'.fe ∧ st'.amo = st.amo ∧ (st.armed = true → st'.armed = true) ∧
  (∀ e, e ∈ st'.fe → ∀ j, j < e.n → kA (e.a + (j : Int)) (nthByte e.w j))

/-- **THE FETCH UNDER `amB`** (header). -/
theorem amFetch (pc : Int) (st : AmSt) (hfe : st.fe = []) (ha : st.amo = false) :
    amB kA (kAa pc) (fetchPostAm pc st) (fetch ()) st := by
  have hv : st.fe.map PinCycRunFetch.feView = [] := by rw [hfe]; rfl
  refine amOfFaZf kA (kAa pc) (fetchPost []) _ _ (fetch ()) st
    (hv ▸ faFetch (Ann := fun _ _ _ => False) []) PinRelArmFp.PinRelArmFetch.zfFetch ha ?_
  intro fr st' h1 h2 h3
  obtain ⟨hamo, harm, hlog⟩ := h3
  have hl : PinCycRunFetch.logOk kA (kAa pc) st'.fe :=
    hlog (by rw [hfe]; intro k e he; simp at he)
  refine ⟨PinCycRunFetch.shapeOk kA pc fr st'.fe h1 h2 hl, hamo, harm, ?_⟩
  intro e he j hj
  obtain ⟨k, hk⟩ := List.getElem?_of_mem he
  exact (hl k e hk).2 j hj

end PinRelArm

end Weak
