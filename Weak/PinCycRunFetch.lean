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

/-! ## 3. The shapes at `pc`, and `fetchCyR1` -/

theorem PinCycRunFetch.feViewEq (e : FeEnt) (a : Int) (n : Nat) (v : BitVec (8 * n))
    (h : PinCycRunFetch.feView e = ⟨a, n, v⟩) : e = ⟨a, n, v⟩ := by
  obtain ⟨a', n', w'⟩ := e
  simp only [PinCycRunFetch.feView, FRd.mk.injEq] at h
  obtain ⟨rfl, rfl, h⟩ := h
  rw [eq_of_heq h]

theorem PinCycRunFetch.view1 (fe : List FeEnt) (a : Int) (n : Nat) (v : BitVec (8 * n))
    (h : fe.map PinCycRunFetch.feView = [⟨a, n, v⟩]) : fe = [⟨a, n, v⟩] := by
  rcases fe with _ | ⟨e, _ | ⟨e', fe⟩⟩
  · simp at h
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    rw [PinCycRunFetch.feViewEq e a n v h]
  · simp at h

theorem PinCycRunFetch.view2 (fe : List FeEnt) (a1 a2 : Int) (lo hi : BitVec 16)
    (h : fe.map PinCycRunFetch.feView = [⟨a1, 2, lo⟩, ⟨a2, 2, hi⟩]) :
    fe = [⟨a1, 2, lo⟩, ⟨a2, 2, hi⟩] := by
  rcases fe with _ | ⟨e, _ | ⟨e', _ | ⟨e'', fe⟩⟩⟩
  · simp at h
  · simp at h
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    rw [PinCycRunFetch.feViewEq e a1 2 lo h.1, PinCycRunFetch.feViewEq e' a2 2 hi h.2]
  · simp at h

theorem PinCycRunFetch.logAt (A : Int → BitVec 8 → Prop) (pc : Int) (fe : List FeEnt) (k : Nat)
    (e : FeEnt) (hl : PinCycRunFetch.logOk A (kAa pc) fe) (he : fe[k]? = some e) :
    e.a = pc + 2 * (k : Int) := (hl k e he).1

set_option maxHeartbeats 4000000 in
/-- The value post at `pc`: W5's shape over the log, with the oracle's addresses, is the arm
`fetchShapeOk pc` names. -/
theorem PinCycRunFetch.shapeOk (A : Int → BitVec 8 → Prop) (pc : Int) (fr : FetchResult)
    (fe : List FeEnt) (hv : fetchPost [] fr (fe.map PinCycRunFetch.feView))
    (hok : PinCycRunFp.PinCycRunFetch.frOk fr) (hl : PinCycRunFetch.logOk A (kAa pc) fe) :
    fetchShapeOk pc fr fe := by
  cases fr with
  | F_Base w =>
    obtain ⟨sh, hsh, hann⟩ := hv
    rw [List.nil_append] at hsh
    cases sh with
    | s4 a v =>
      simp only [FetchShape.ann] at hann
      rcases hann with ⟨h, hr⟩ | ⟨h, _⟩
      · obtain rfl : w = v := eq_of_heq (Sigma.mk.inj h).2
        have hfe := PinCycRunFetch.view1 fe a 4 w hsh
        have ha := PinCycRunFetch.logAt A pc fe 0 _ hl (by rw [hfe]; rfl)
        obtain rfl : a = pc := by simpa using ha
        exact Or.inl ⟨hfe, hr⟩
      · exact absurd (Sigma.mk.inj h).1 (by decide)
    | s2 a v =>
      simp only [FetchShape.ann] at hann
      exact absurd (Sigma.mk.inj hann.1).1 (by decide)
    | s22 a1 a2 lo hi =>
      simp only [FetchShape.ann] at hann
      obtain ⟨h, hr⟩ := hann
      obtain rfl : w = hi ++ lo := eq_of_heq (Sigma.mk.inj h).2
      have hfe := PinCycRunFetch.view2 fe a1 a2 lo hi hsh
      have h1 := PinCycRunFetch.logAt A pc fe 0 _ hl (by rw [hfe]; rfl)
      have h2 := PinCycRunFetch.logAt A pc fe 1 _ hl (by rw [hfe]; rfl)
      obtain rfl : a1 = pc := by simpa using h1
      obtain rfl : a2 = a1 + 2 := by simpa using h2
      exact Or.inr ⟨lo, hi, hfe, rfl, hr⟩
  | F_RVC h =>
    obtain ⟨sh, hsh, hann⟩ := hv
    rw [List.nil_append] at hsh
    cases sh with
    | s4 a v =>
      simp only [FetchShape.ann] at hann
      rcases hann with ⟨h', _⟩ | ⟨h', hr⟩
      · exact absurd (Sigma.mk.inj h').1 (by decide)
      · obtain rfl : h = Sail.BitVec.extractLsb v 15 0 := eq_of_heq (Sigma.mk.inj h').2
        have hfe := PinCycRunFetch.view1 fe a 4 v hsh
        have ha := PinCycRunFetch.logAt A pc fe 0 _ hl (by rw [hfe]; rfl)
        obtain rfl : a = pc := by simpa using ha
        exact Or.inl ⟨v, hfe, rfl, hr⟩
    | s2 a v =>
      simp only [FetchShape.ann] at hann
      obtain ⟨h', hr⟩ := hann
      obtain rfl : h = v := eq_of_heq (Sigma.mk.inj h').2
      have hfe := PinCycRunFetch.view1 fe a 2 h hsh
      have ha := PinCycRunFetch.logAt A pc fe 0 _ hl (by rw [hfe]; rfl)
      obtain rfl : a = pc := by simpa using ha
      exact Or.inr ⟨hfe, hr⟩
    | s22 a1 a2 lo hi =>
      simp only [FetchShape.ann] at hann
      exact absurd (Sigma.mk.inj hann.1).1 (by decide)
  | F_Error e => trivial
  | F_Ext_Error e => exact hok.elim

/-- **r1 AT THE CYCLE, DISCHARGED** (header): `fetchCyR1 pc` holds at every `pc`, from W5's
`faFetch` and the frame footprint `pfFetch`. -/
theorem PinCycRunFetch.fetchCyR1Of (pc : Int) : fetchCyR1 pc := by
  intro T st hfe _ _ _ hrb hro
  have hS : ∀ r, cyS r = true → pfProt r = true := by
    intro r hr
    simp only [cyS, Bool.or_eq_true, decide_eq_true_eq] at hr
    rcases hr with rfl | rfl <;> rfl
  have hv : st.fe.map PinCycRunFetch.feView = [] := by rw [hfe]; rfl
  refine PinCycRunFetch.cyOfFaPf kA (kAa pc) cyS T hS (fetchPost []) _ _ (fetch ()) st
    (hv ▸ faFetch (Ann := fun _ _ _ => False) []) PinCycRunFp.PinCycRunFetch.pfFetch hrb
    (by rw [hro]; rfl) (by rw [hro]; rfl) ?_
  intro fr st' h1 h2 h3
  obtain ⟨hp, hrb', han, hro', hn, hok, hlog⟩ := h3
  have hl : PinCycRunFetch.logOk kA (kAa pc) st'.fe :=
    hlog (by rw [hfe]; intro k e he; simp at he)
  refine ⟨hp, hrb', han, hro', hn, hok, ?_, PinCycRunFetch.shapeOk kA pc fr st'.fe h1 h2 hl⟩
  intro e he j hj
  obtain ⟨k, hk⟩ := List.getElem?_of_mem he
  exact (hl k e hk).2 j hj




open KernelPinsDef PinWalkTab
open WeakRvwmoPinBridge3 (preach)
open WeakRvwmoPinBridge4 (walkOwn)

/-- **`cycRun` FROM `hartConf`, r1 discharged** (header): `cycRunOfHartConfE` with
`fetchCyR1Of`; the premises left are the run obligations `fetchOkR2` (r2) / `dataOkR` /
`excRetR` and the walk start. -/
theorem cycRunOfHartConfF (G : Gexec) (i : Nat) (row : List Lbl) (p0 : Pexv6) (dv : Nat → Efab)
    (em : Hemission) (pcL : Int) (w : Pin) (own : Bool)
    (hcf : hartConf i row p0 dv em) (hm : (pcL, w) ∈ pinsW9a) (hw : walkOwn w = some own)
    (hft : kFetchText em)
    (hfetch : ∀ s n l, preach own (pinStart pcL) s n → pstep own s = some l → l ≠ [] →
      fetchOkRF p0 (dv 0) em s.psPc)
    (hdata : ∀ s n l, preach own (pinStart pcL) s n → pstep own s = some l → l ≠ [] →
      dataOkRF p0 (dv 0) em s.psPc)
    (hexc : ∀ s n l, preach own (pinStart pcL) s n → pstep own s = some l → l ≠ [] →
      excRetR G i p0 (dv 0) em s.psPc)
    (base rest : List Eitem) (hes : em.emItems = base ++ rest)
    (hstart : ∀ p d, prunJ (base.map Prod.fst) p0 (dv 0) p d →
      ∃ (cpu : CPU) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch),
        p = .PHart cpu (.pure ()) rs fn ib ∧ kInv (pinStart pcL).psPc rs) :
    ∃ (mid rest' : List Eitem) (s : PState) (n : Nat) (p' : Pexv6) (d' : Efab),
      rest = mid ++ rest' ∧ cycRun G i em own base (pinStart pcL) mid s ∧
      preach own (pinStart pcL) s n ∧ walkBd p0 (dv 0) em (base ++ mid) s.psPc p' d' ∧
      cycStop G i p0 (dv 0) em own (base ++ mid) s rest' :=
  cycRunOfHartConfE G i row p0 dv em pcL w own hcf hm hw hft
    (fun _ _ _ _ _ _ => PinCycRunFetch.fetchCyR1Of _) hfetch hdata hexc base rest hes hstart


/-! ## 4. The walk start as a REALIZATION INTERFACE (provisional, FAITHFUL; Q-START (a))

The walk-start premise does not follow from `hartConf` (an `hemit` run from an arbitrary `p0`)
nor from the load's cycle certificate (word, role, address only). Its content is the program
logic's: at every kernel instruction the WP proof holds the configuration bundle (`ctrlOkSI`,
`Weak/AxIntr.lean:84`: priv `S`, `hart_state` active, `misa = misaC`, `menvcfg = menvcfgS`,
`htif_tohost_base = none`, `elp` not `LP_EXPECTED`, `pma_regions = bootPMA`, `mstatus.TVM = 0`
inside `sconfMsFacts`), plus `mseccfg = 0`. `walkStartRealized` is that fact at the load's
boundary, an interface of `RvwmoXv6Adequacy.syncRealized`'s kind, which W11-F's composition
supplies from the certified run. -/

/-- The configuration bundle the walk needs (`kCfg` and the two boot-pinned registers of
`Rboot`); field by field a projection of `ctrlOkSI` + `mseccfg = 0`. -/
def wpCfgAt (rs : RegFile) : Prop :=
  kCfg rs ∧ rs .pma_regions = bootPMA ∧ rs .htif_tohost_base = none

/-- **THE WALK START, REALIZED (INTERFACE, header; W11-F's obligation)**: along the hart's run of
the emission prefix `base` (ending with the load's cycle), the hart is at a cycle boundary whose
`PC` is the walk start `pc` and whose registers hold the configuration bundle. -/
def walkStartRealized (p0 : Pexv6) (d0 : Efab) (base : List Eitem) (pc : Int) : Prop :=
  ∀ p d, prunJ (base.map Prod.fst) p0 d0 p d →
    ∃ (cpu : CPU) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch),
      p = .PHart cpu (.pure ()) rs fn ib ∧ rs .PC = BitVec.ofInt 64 pc ∧ wpCfgAt rs

theorem PinCycRunFetch.rbootAllOf (rs : RegFile) (h1 : rs .pma_regions = bootPMA)
    (h2 : rs .htif_tohost_base = none) : RbootAll rs := by
  intro r
  cases r <;> first | exact h1 | exact h2 | trivial

theorem PinCycRunFetch.kInvOfCfg (pc : Int) (rs : RegFile) (hpc : rs .PC = BitVec.ofInt 64 pc)
    (h : wpCfgAt rs) : kInv pc rs :=
  ⟨hpc, h.1, PinCycRunFetch.rbootAllOf rs h.2.1 h.2.2⟩

/-- **`cycRun` FROM `hartConf`, walk start realized** (header): `cycRunOfHartConfF` with the
walk-start premise replaced by the interface `walkStartRealized`; left: `fetchOkR2` (r2),
`dataOkR`, `excRetR` (owner questions). -/
theorem cycRunOfHartConfW (G : Gexec) (i : Nat) (row : List Lbl) (p0 : Pexv6) (dv : Nat → Efab)
    (em : Hemission) (pcL : Int) (w : Pin) (own : Bool)
    (hcf : hartConf i row p0 dv em) (hm : (pcL, w) ∈ pinsW9a) (hw : walkOwn w = some own)
    (hft : kFetchText em)
    (hfetch : ∀ s n l, preach own (pinStart pcL) s n → pstep own s = some l → l ≠ [] →
      fetchOkRF p0 (dv 0) em s.psPc)
    (hdata : ∀ s n l, preach own (pinStart pcL) s n → pstep own s = some l → l ≠ [] →
      dataOkRF p0 (dv 0) em s.psPc)
    (hexc : ∀ s n l, preach own (pinStart pcL) s n → pstep own s = some l → l ≠ [] →
      excRetR G i p0 (dv 0) em s.psPc)
    (base rest : List Eitem) (hes : em.emItems = base ++ rest)
    (hreal : walkStartRealized p0 (dv 0) base (pinStart pcL).psPc) :
    ∃ (mid rest' : List Eitem) (s : PState) (n : Nat) (p' : Pexv6) (d' : Efab),
      rest = mid ++ rest' ∧ cycRun G i em own base (pinStart pcL) mid s ∧
      preach own (pinStart pcL) s n ∧ walkBd p0 (dv 0) em (base ++ mid) s.psPc p' d' ∧
      cycStop G i p0 (dv 0) em own (base ++ mid) s rest' :=
  cycRunOfHartConfF G i row p0 dv em pcL w own hcf hm hw hft hfetch hdata hexc base rest hes
    (fun p d hr => by
      obtain ⟨cpu, rs, fn, ib, hp, hpc, hc⟩ := hreal p d hr
      exact ⟨cpu, rs, fn, ib, hp, PinCycRunFetch.kInvOfCfg _ rs hpc hc⟩)

end PinCycRun

end Weak
