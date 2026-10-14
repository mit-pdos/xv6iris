/-
Weak: **W9a (B) B5 cycRun — r1 AT THE CYCLE, `fetchCyR1` from W5's value chain** (plan
`notes/weak-allocproc-plan.md` rev 52 §C W9a (B) "(B5) assembly"; Q-B5-CYCLE C1).  Lean-only.

`fetchCyR1 pc` (`PinCycRunCyc3.lean`) is discharged from two walks of the SAME Sail text
`fetch ()` (`model/Lean_RV64D/LeanRV64D/Fetch.lean:233-288`):
* W5's value chain `PinFetchVal.faFetch` — a returned `F_Base`/`F_RVC` word is one of Sail's four
  arm shapes over the fetch reads made (`fetchPost`);
* the relaxed frame footprint `pfFetch` (`pfB true`, this file) — `fetch ()` writes no protected
  register and never answers `F_Ext_Error` (`ext_fetch_check_pc` is `none`,
  `AddrChecks.lean:205`).
The product `cyOfFaPf` turns the two into the cycle predicate `cyB`; the fetch reads'
addresses are the oracle `kAa pc` (`pc + 2k`, `fetchOkR2`'s clause (i)), so the shapes are the
ones `fetchShapeOk pc` names.

Every helper is `Weak.PinCycRunFetch.*`.
-/
import Weak.PinCycRunExec3
import Weak.PinFetchVal

namespace Weak
open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
namespace PinCycRunFp
open SailCycleOrderK

/-! ## 1. The relaxed frame footprint of `fetch ()` -/

set_option maxHeartbeats 4000000 in
@[pf_reg] theorem PinCycRunFetch.pfReadRamB (rk : read_kind) (pa : physaddr) (w : Nat) (m : Bool) :
    pfB true (fun _ => True) (read_ram rk pa w m) := by
  unfold read_ram
  pf_walk

set_option maxHeartbeats 8000000 in
@[pf_reg] theorem PinCycRunFetch.pfCheckedMemReadB (acc : MemoryAccessType mem_payload)
    (pbmt : page_based_mem_type) (priv : Privilege) (pa : physaddr) (w : Nat) (aq rl res m : Bool) :
    pfB true (fun _ => True) (checked_mem_read acc pbmt priv pa w aq rl res m) := by
  unfold checked_mem_read
  pf_walk

set_option maxHeartbeats 8000000 in
@[pf_reg] theorem PinCycRunFetch.pfMemReadB (acc : MemoryAccessType mem_payload)
    (pbmt : page_based_mem_type) (pa : physaddr) (w : Nat) (aq rl res : Bool) :
    pfB true (fun _ => True) (mem_read acc pbmt pa w aq rl res) := by
  unfold mem_read mem_read_priv mem_read_priv_meta
  pf_walk

/-- `fetch_bytes` never answers an extension error (`ext_fetch_check_pc` is `none`). -/
def PinCycRunFetch.fbOk {w : Nat} (r : FetchBytes_Result w) : Prop :=
  match r with
  | .FetchBytes_Ext_Error _ => False
  | _ => True

set_option maxHeartbeats 8000000 in
@[pf_reg] theorem PinCycRunFetch.pfFetchBytes (fs gs : BitVec 64) (w : Nat) :
    pfB true PinCycRunFetch.fbOk (fetch_bytes fs gs w) := by
  simp only [fetch_bytes, ext_fetch_check_pc, SailME.run, PreSail.PreSailME.run, ExceptT.run_bind,
    run_liftM, bind_assoc, pure_bind]
  refine pfBBindQ true _ _ _ _ (pfRelax _ _ (pfTranslateAddr _ _)) (fun r _ => ?_)
  cases r with
  | Err e =>
    simp only [run_SailME_throw, pure_bind]
    exact trivial
  | Ok q =>
    obtain ⟨paddr, pbmt, u⟩ := q
    simp only [ExceptT.run_pure, pure_bind, bind_assoc]
    refine pfBBindQ true _ _ _ _ (PinCycRunFetch.pfMemReadB _ _ _ _ _ _ _) (fun r _ => ?_)
    cases r with
    | Err q =>
      obtain ⟨ea, e⟩ := q
      simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, ExceptT.run_pure]
      refine pfBBindQ true _ _ _ _
        (pfRelax _ _ (by pf_walk : pfT (assert (ea == paddr) "postlude/fetch.sail:44.30-44.31")))
        (fun _ _ => ?_)
      exact trivial
    | Ok bytes =>
      simp only [ExceptT.run_pure, pure_bind]
      exact trivial

/-- `fetch ()` never answers an extension error. -/
def PinCycRunFetch.frOk (r : FetchResult) : Prop :=
  match r with
  | .F_Ext_Error _ => False
  | _ => True

theorem PinCycRunFetch.pfReadReg (r : Register) : pfT (readReg r) := by pf_walk

/-- The same at the early-return layer. -/
def PinCycRunFetch.frOkE : Except (Sail.Error exception ⊕ FetchResult) FetchResult → Prop
  | .ok x => PinCycRunFetch.frOk x
  | .error (.inr x) => PinCycRunFetch.frOk x
  | .error (.inl _) => True

/-- One step of the fetch walk (W5's `fa_fetch_step`, for `pfB`). -/
macro "pf_fetch_step" : tactic => `(tactic| first
  | (simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, ExceptT.run_pure,
      PinFetchVal.runIte, PinFetchVal.iteBind, Bool.false_eq_true, ↓reduceIte])
  | exact trivial
  | split
  | (refine pfBBindQ true _ _ _ _ (pfRelax _ _ (PinCycRunFetch.pfReadReg _)) (fun _ _ => ?_))
  | (refine pfBBindQ true _ _ _ _ (pfRelax _ _ (pfCurrentlyEnabled _)) (fun _ _ => ?_))
  | (refine pfBBindQ true _ _ _ _ (PinCycRunFetch.pfFetchBytes _ _ _) (fun r hr => ?_)
     cases r
     all_goals try (exact (hr : False).elim)))

set_option maxHeartbeats 40000000 in
/-- **THE FETCH'S FRAME** (header): `fetch ()` writes no protected register (`pfProt`), every
written value is `Rboot`-admitted, and the answer is never `F_Ext_Error`. -/
theorem PinCycRunFetch.pfFetch : pfB true PinCycRunFetch.frOk (fetch ()) := by
  simp only [fetch, ext_fetch_check_pc, get_config_rvfi, SailME.run, PreSail.PreSailME.run,
    ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, Bool.false_eq_true, ↓reduceIte]
  refine pfBBindQ true _ _ _ _ (pfRelax _ _ (PinCycRunFetch.pfReadReg _)) (fun _ _ => ?_)
  refine pfBBindQ true _ _ _ _ (pfRelax _ _ (PinCycRunFetch.pfReadReg _)) (fun _ _ => ?_)
  refine pfBBindQ true _ _ _ _ (pfRelax _ _ (PinCycRunFetch.pfReadReg _)) (fun _ _ => ?_)
  refine pfBBindQ true PinCycRunFetch.frOkE _ _ _ ?_ ?_
  rotate_left
  · intro r hr
    rcases r with (e | e) | e
    · exact trivial
    · exact hr
    · exact hr
  repeat' pf_fetch_step

end PinCycRunFp

/-! ## 2. The product: W5's value chain × the frame footprint ⇒ the cycle predicate -/

namespace PinCycRun
open SailCycleOrderK PinDataflow PinFetchVal
open PinCycRunFp (pfB pfProt pfRegOk pfW)

/-- A logged fetch read as W5's `FRd`. -/
def PinCycRunFetch.feView (e : FeEnt) : FRd := ⟨e.a, e.n, e.w⟩

/-- The fetch log's invariant: the `k`-th read is at an oracle address, its bytes `A`-admitted. -/
def PinCycRunFetch.logOk (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (fe : List FeEnt) :
    Prop :=
  ∀ (k : Nat) (e : FeEnt), fe[k]? = some e → Aa k e.a ∧ ∀ j, j < e.n → A (e.a + (j : Int)) (nthByte e.w j)

theorem PinCycRunFetch.logOkSnoc (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop)
    (fe : List FeEnt) (a : Int) (n : Nat) (w : BitVec (8 * n)) (h : PinCycRunFetch.logOk A Aa fe)
    (ha : Aa fe.length a) (hA : ∀ j, j < n → A (a + (j : Int)) (nthByte w j)) :
    PinCycRunFetch.logOk A Aa (fe ++ [⟨a, n, w⟩]) := by
  intro k e hk
  by_cases hl : k < fe.length
  · rw [List.getElem?_append_left hl] at hk
    exact h k e hk
  · rw [List.getElem?_append_right (by omega)] at hk
    have hk0 : k - fe.length = 0 := by
      cases e' : k - fe.length with
      | zero => rfl
      | succ m => rw [e'] at hk; simp at hk
    rw [hk0] at hk
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    have : k = fe.length := by omega
    subst this
    exact ⟨ha, hA⟩

/-- The fetch's frame relative to the cycle's state `st`. -/
def PinCycRunFetch.feFrame (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (st st' : CySt) :
    Prop :=
  (∀ r, pfProt r = true → st'.rv r = st.rv r) ∧ RbootAll st'.rv ∧ st'.an = st.an ∧
  st'.d.ro = st.d.ro ∧ st'.d.n = st.d.n ∧ st'.d.ok = st.d.ok ∧
  (PinCycRunFetch.logOk A Aa st.fe → PinCycRunFetch.logOk A Aa st'.fe)

theorem PinCycRunFetch.feFrameRefl (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (st : CySt)
    (h : RbootAll st.rv) : PinCycRunFetch.feFrame A Aa st st :=
  ⟨fun _ _ => rfl, h, rfl, rfl, rfl, rfl, id⟩

theorem PinCycRunFetch.feFrameTrans (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop)
    (s1 s2 s3 : CySt) (h1 : PinCycRunFetch.feFrame A Aa s1 s2)
    (h2 : PinCycRunFetch.feFrame A Aa s2 s3) : PinCycRunFetch.feFrame A Aa s1 s3 := by
  obtain ⟨a1, -, c1, d1, e1, f1, g1⟩ := h1
  obtain ⟨a2, b2, c2, d2, e2, f2, g2⟩ := h2
  exact ⟨fun r h => (a2 r h).trans (a1 r h), b2, c2.trans c1, d2.trans d1, e2.trans e1,
    f2.trans f1, fun h => g2 (g1 h)⟩

section prod
variable (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (S : Register → Bool)
  (T : CySt → (r : Register) → RegisterType r → Prop)

set_option maxHeartbeats 4000000 in
/-- **THE PRODUCT** (header): along every path, W5's fetch-value predicate (no announce) and the
relaxed frame footprint give the cycle predicate, with the value post read on the logged reads. -/
theorem PinCycRunFetch.cyOfFaPf {X : Type} (hS : ∀ r, S r = true → pfProt r = true)
    (P : X → List FRd → Prop) (Pf : X → Prop) (Q : X → CySt → Prop) :
    ∀ (m : SailM X) (st : CySt),
      faB (fun _ _ _ => False) P m (st.fe.map PinCycRunFetch.feView) → pfB true Pf m →
      RbootAll st.rv → depsRd st.d.ro = none → depsRd2 st.d.ro = none →
      (∀ x st', P x (st'.fe.map PinCycRunFetch.feView) → Pf x →
        PinCycRunFetch.feFrame A Aa st st' → Q x st') →
      cyB A Aa S T Q m st := by
  intro m
  induction m with
  | pure x =>
    intro st hfa hp hrb _ _ hq
    exact hq x st hfa hp (PinCycRunFetch.feFrameRefl A Aa st hrb)
  | impure call k ih =>
    intro st hfa hp hrb h1 h2 hq
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead r =>
        intro v hv
        have hb := PinCycRun.rdRboot st r v hrb hv
        exact ih v (cyRd st r) (hfa v hb) (hp v hb) hrb h1 h2 (fun x st' e1 e2 e3 =>
          hq x st' e1 e2 (PinCycRunFetch.feFrameTrans A Aa _ _ _
            (PinCycRunFetch.feFrameRefl A Aa st hrb) e3))
      case regWrite r v =>
        obtain ⟨⟨hb, hok⟩, hk⟩ := hp
        have hpf : pfProt r = false := by simpa [pfRegOk] using hok
        refine ⟨fun hs => absurd (hS r hs) (by rw [hpf]; decide), fun _ => ⟨hb, fun u => ?_⟩⟩
        have hrb' : RbootAll (cyWr st r v).rv := rbootAllSet _ r v hrb hb
        obtain ⟨en, eok⟩ := PinCycRun.dfWrNoDest st.d r h1 h2
        have hfr : PinCycRunFetch.feFrame A Aa st (cyWr st r v) := by
          refine ⟨fun r' h' => ?_, hrb', rfl, rfl, en, eok, id⟩
          have e : r' ≠ r := by rintro rfl; rw [hpf] at h'; cases h'
          exact RegFile.set_other _ _ _ _ e
        exact ih u (cyWr st r v) (hfa.2 u) (hk u) hrb' h1 h2 (fun x st' e1 e2 e3 =>
          hq x st' e1 e2 (PinCycRunFetch.feFrameTrans A Aa _ _ _ hfr e3))
      case memRead n va req =>
        refine ⟨fun hdev hif ha w hA => ?_, fun h w => ?_⟩
        · have hfa' := hfa
          simp only [faB, hif, ↓reduceIte] at hfa'
          have hv : (cyFe st (paZ req.pa) n w).fe.map PinCycRunFetch.feView =
              st.fe.map PinCycRunFetch.feView ++ [⟨paZ req.pa, n, w⟩] := by
            simp [cyFe, PinCycRunFetch.feView]
          have hfr : PinCycRunFetch.feFrame A Aa st (cyFe st (paZ req.pa) n w) :=
            ⟨fun _ _ => rfl, hrb, rfl, rfl, rfl, rfl, fun hl =>
              PinCycRunFetch.logOkSnoc A Aa st.fe _ n w hl ha hA⟩
          exact ih _ (cyFe st (paZ req.pa) n w) (hv ▸ hfa'.2 w) (hp.2 _) hrb h1 h2
            (fun x st' e1 e2 e3 => hq x st' e1 e2 (PinCycRunFetch.feFrameTrans A Aa _ _ _ hfr e3))
        · cases hif : (classify req.access_kind).akIfetch with
          | true =>
            have hfa' := hfa
            simp only [faB, hif, ↓reduceIte] at hfa'
            exact absurd (h hfa'.1) (by rw [hif]; decide)
          | false =>
            have hfa' := hfa
            simp only [faB, hif, Bool.false_eq_true, ↓reduceIte] at hfa'
            exact ih _ st (hfa' w) (hp.2 _) hrb h1 h2 hq
      case instrAnnounce => exact hfa.elim
      case barrier b => exact fun v => ih v st (hfa v) hp.2 hrb h1 h2 hq
      case getCycleCount => exact ih _ st (hfa _) (hp _) hrb h1 h2 hq
      all_goals exact fun v => ih v st (hfa v) (hp v) hrb h1 h2 hq

end prod


end PinCycRun

end Weak
