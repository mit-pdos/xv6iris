/-
Weak: **allocproc route P, row P-W6 on the S-R walk — THE VIEW-READ LOAD ROW** (cell a′ of
`notes/twin-machine-conformance.md`; `PROGRESS-PW6.md` design check "LOADS ARE STALE").  Lean-only, no Rocq
twin.  A PRIMED TWIN: nothing registered imports this file.

**Spec first.**  RVWMO's load value axiom: each byte of a load returns the store that is gmo-latest among the
stores to that byte gmo-before the load and the hart's po-earlier stores to it.  So every non-forwarded byte's
source is gmo-before the load and NO store to that byte lies gmo-between its source and the load: all the
bytes of one load are read at ONE cut (the load's gmo point) — the per-byte single-copy shape of RVWMO, for
every load (aligned or not); a byte whose source is a po-earlier own store gmo-AFTER the load is forwarded.

The S-R walk (`SbOrdR.enbR`) realizes a plain load STALE, at GF's timestamps (`SbOrdR.srGate`: sources landed,
view domination `SbDom.DomInv`), not at the member-latest byte.  MachCSL's plain read (`evStep`'s third
`memRead` disjunct) reads every byte of the footprint at ONE landing view `tvn` with `tv ≤ tvn ≤ ltop` and the
coherence floors `≤ tvn`, forwarding from the hart's buffer (`MState.readFwd`); an own LANDED entry is visible
at every view (`HEnt.visibleP`).  This file is the row for that read:

  §1  **`byteFwdAt`**: MachCSL's `byteFwd` at ANY view `tvn` is the twin's forwarded byte, else TsoMem's
      reading of the twin's projected history at `tvn` (`HEnt.visible`: at or below `tvn`, or own) — the
      landed-top row `SbRealP.byteFwdTop` at `tvn = ltop`; **`byteFwdAtSca`**: at a single-copy cut
      (`PfRunShape.scaByte`: `t` visible at `tvn`, no later write to the byte visible) it is the twin's byte
      at `t` (`PfStepTsoMem.histOfFind`).
  §2  `rmemPLoadAt` (the state map after a read at any `tvn ≤ ltop`), the cut **`ViewCut`** and the row
      **`evLoadViewP`**: given the cut, MachCSL's plain read at `tvn` answers the twin's bytes, `rmemP` kept.
  §3  **`viewCutOf`** — WHERE THE CUT COMES FROM: `tvn := max T (max tv cohMax)` is a cut when (a) every
      non-forwarded byte's source is visible at `T` (or own) and every later write to the byte is above `T`
      (THE GF CUT, the load value axiom above: `T` the walk's landed prefix at the load's gmo point), (b) the
      hart's floor `tv` and every coherence floor of the footprint are below every such later write (THE
      FLOOR DOMINATION, `R-view`: MachCSL's floors dominated as the twin's are, `SbDom.DomInv`), (c) no such
      later write is the hart's own (coherence CoWR/CoRW).

The matrix cell a′ (load at a STALE cut): EQUAL — RVWMO itself reads a load at one gmo cut, so MachCSL's
single `tvn` is not stronger (it would be stronger only for a load whose bytes are read at DIFFERENT gmo
points, which RVWMO's load value axiom never allows).  (a)/(c) are GF facts; (b) is the `R-view` conjunct of
`SimRelP`, whose preservation is the next item.

Spec: FAITHFUL (proof organisation; no new named input — (a)–(c) are the row's premises, all discharged
from GF / the walk invariant).  Lean-only helpers `SbRealPView.*`.
-/
import Weak.SbRealPHart

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D
open Lbl PfStepTsoMem SbRealP

namespace SbRealPView

/-! # 1. The plain read's byte at any view -/

/-- **A history with no own PENDING entry reads as its landed view** (TsoMem's `HEnt.visible` over landing
positions). -/
theorem readPNoOwn (lp : LandPos) (h : Agent) (tv : Nat) : ∀ H : Hist,
    (∀ e ∈ H, lp e.t = none → e.tid ≠ h) →
    Hist.readP lp h tv H = ((Hist.lview lp H).find? (HEnt.visible h tv)).map HEnt.v
  | [], _ => rfl
  | e :: H, hH => by
    have ih := readPNoOwn lp h tv H (fun x hx => hH x (List.mem_cons_of_mem _ hx))
    unfold Hist.readP at ih ⊢
    cases hl : lp e.t with
    | none =>
      rw [Hist.lview_cons_pending lp e H hl, List.find?_cons]
      have : HEnt.visibleP lp h tv e = false := by
        simp [HEnt.visibleP, hl, hH e List.mem_cons_self hl]
      rw [this]; exact ih
    | some q =>
      rw [Hist.lview_cons_landed lp e H hl, List.find?_cons, List.find?_cons]
      have : HEnt.visibleP lp h tv e = HEnt.visible h tv ⟨q, e.tid, e.v⟩ := by
        simp [HEnt.visibleP, HEnt.visible, hl]
      rw [this]
      cases HEnt.visible h tv ⟨q, e.tid, e.v⟩
      · exact ih
      · rfl

/-- **THE PLAIN LOAD'S BYTE AT ANY VIEW** (route P's `MState.byteFwd` at `tvn`): the hart's youngest covering
pending store's byte (the twin's `SbCand.fwdByte`), else TsoMem's reading of the twin's projected history at
`tvn`. -/
theorem byteFwdAt (img : Image) (c : SbCand.CandS) (σ : MState) (hR : rmemP img c σ) (cpu : CPU)
    (tvn : Nat) (a : PAddr) (ha : inRam a 1) :
    σ.byteFwd cpu tvn a =
      (SbCand.fwdByte (c.sb (hartAgent cpu)) (paZ a)).or
        (((TsoOfPf.histOf img c.ms.msLog (paZ a)).find? (HEnt.visible (hartAgent cpu) tvn)).map HEnt.v) := by
  obtain ⟨himg, hlog, hlogB, hH, hsb, hoth, hresv, hnd, hok⟩ := hR
  obtain ⟨H, hm, hl⟩ := lviewSomeInv (hH.1 a ha)
  have hhist := (hok.1 a H hm)
  have hord := hok.2.2.2.2.2.2.2.1
  let P : HEnt → Bool := fun e => decide (e.tid = hartAgent cpu) && (σ.sb cpu).any (fun p => p.1 == e.t)
  have hown : ∀ x ∈ H, P x = true → ∃ (k' : Nat) (p' : Nat × Nat) (e' : SbEnt),
      (σ.sb cpu)[k']? = some p' ∧ p'.1 = x.t ∧
      (c.sb (hartAgent cpu))[k']? = some e' ∧ memStamp σ.mem a x.t = msgByte e'.msg (paZ a) ∧
      (msgByte e'.msg (paZ a)).isSome := by
    intro x hx hP
    simp only [P, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at hP
    obtain ⟨-, p', hp', hpt⟩ := hP
    obtain ⟨k', hk'⟩ := idxOfMem hp'
    obtain ⟨e', he', hr⟩ := forall2GetL (hsb cpu) hk'
    have hms := hr.2.2.2 a
    refine ⟨k', p', e', hk', hpt, he', by rw [← hpt]; exact hms, ?_⟩
    rw [← hms]
    unfold memStamp; rw [hm, Option.bind_some]
    exact stampByteSome.2 ⟨x, hx, hpt.symm⟩
  have hcov : ∀ (k' : Nat) (p' : Nat × Nat) (e' : SbEnt), (σ.sb cpu)[k']? = some p' →
      (c.sb (hartAgent cpu))[k']? = some e' →
      (msgByte e'.msg (paZ a)).isSome → ∃ x ∈ H, x.t = p'.1 ∧ P x = true := by
    intro k' p' e' hk' he' hs
    obtain ⟨b, hb, hr⟩ := forall2GetL (hsb cpu) hk'
    rw [he'] at hb; obtain rfl := Option.some.inj hb
    have hms := hr.2.2.2 a
    rw [← hms] at hs
    unfold memStamp at hs; rw [hm, Option.bind_some] at hs
    obtain ⟨x, hx, hxt⟩ := stampByteSome.1 hs
    have hpm := List.mem_of_getElem? hk'
    obtain ⟨-, -, hp3, -⟩ := (hok.2.2.2.2.2.2.1 cpu p'.1).1 ⟨p'.2, hpm⟩
    refine ⟨x, hx, hxt, ?_⟩
    have hxa : x.tid = hartAgent cpu := by
      rcases (hhist.2 x hx).2 with h0 | hya
      · have := (hok.2.2.2.2.2.2.1 cpu p'.1).1 ⟨p'.2, hpm⟩; omega
      · rw [hxt, hp3] at hya; exact (Option.some.inj hya).symm
    simp only [P, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq]
    exact ⟨hxa, p', hpm, hxt.symm⟩
  unfold MState.byteFwd
  rw [hm, Option.bind_some]
  cases hf : H.find? P with
  | none =>
    have hnone : ∀ e ∈ c.sb (hartAgent cpu), msgByte e.msg (paZ a) = none := by
      intro e he
      obtain ⟨k', hk'⟩ := idxOfMem he
      obtain ⟨p', hp', -⟩ := forall2Get (hsb cpu) hk'
      cases hs : msgByte e.msg (paZ a) with
      | none => rfl
      | some v =>
        obtain ⟨x, hx, -, hP⟩ := hcov k' p' e hp' hk' (by rw [hs]; rfl)
        rw [List.find?_eq_none] at hf
        exact absurd hP (hf x hx)
    show Hist.readP σ.lp (hartAgent cpu) tvn H = _
    rw [fwdByteNone _ _ hnone, Option.none_or, readPNoOwn σ.lp (hartAgent cpu) tvn H ?_, hl]
    intro x hx hlx hxa
    have := (σ.okP_own_pending hok cpu a H hm x hx hxa).2 hlx
    rw [List.find?_eq_none] at hf
    exact hf x hx (by simp only [P, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hxa, this⟩)
  | some y =>
    obtain ⟨hPy, as0, bs, hHy, has⟩ := List.find?_eq_some_iff_append.1 hf
    have hyH : y ∈ H := by rw [hHy]; simp
    obtain ⟨k', p', e', hk', hpt, he', hms, hs⟩ := hown y hyH hPy
    have hmax : ∀ k'' e'', k' < k'' → (c.sb (hartAgent cpu))[k'']? = some e'' →
        msgByte e''.msg (paZ a) = none := by
      intro k'' e'' hlt he''
      cases hs'' : msgByte e''.msg (paZ a) with
      | none => rfl
      | some v =>
        exfalso
        obtain ⟨p'', hp'', -⟩ := forall2Get (hsb cpu) he''
        obtain ⟨x, hx, hxt, hPx⟩ := hcov k'' p'' e'' hp'' he'' (by rw [hs'']; rfl)
        have hgt := (pairwiseGet (hord cpu) hk' hp'' hlt).1
        have hxbs : x ∈ bs := by
          rw [hHy] at hx
          rcases List.mem_append.1 hx with hx | hx
          · have := has x hx; rw [hPx] at this; cases this
          · rcases List.mem_cons.1 hx with rfl | hx
            · omega
            · exact hx
        have hco : coAbove σ.lp y x := by
          have hpw := hhist.1
          rw [hHy, List.pairwise_append] at hpw
          exact List.rel_of_pairwise_cons hpw.2.1 hxbs
        have hpend : ∀ z ∈ H, P z = true → σ.lp z.t = none := fun z hz hPz => by
          simp only [P, Bool.and_eq_true, decide_eq_true_eq] at hPz
          exact (σ.okP_own_pending hok cpu a H hm z hz hPz.1).1 hPz.2
        unfold coAbove at hco
        rw [hpend y hyH hPy, hpend x hx hPx] at hco
        omega
    rw [fwdByteMax _ _ k' e' he' hs hmax, ← hms]
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
    have hfirst : H.find? (fun e => e.t == y.t) = some y := by
      rw [List.find?_eq_some_iff_append]
      refine ⟨by simp, as0, bs, hHy, fun z hz => ?_⟩
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
      intro hzt
      have hzH : z ∈ H := by rw [hHy]; simp [hz]
      have hPz : P z = true := by
        simp only [P, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq]
        simp only [P, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at hPy
        obtain ⟨hya, q, hq, hqt⟩ := hPy
        refine ⟨?_, q, hq, by rw [hqt, hzt]⟩
        rcases (hhist.2 z hzH).2 with h0 | hza
        · obtain ⟨h1, -⟩ := sbStampBound hok hq; omega
        · rcases (hhist.2 y hyH).2 with h0 | hya'
          · obtain ⟨h1, -⟩ := sbStampBound hok hq; omega
          · rw [hzt, hya'] at hza; rw [← hya]; exact (Option.some.inj hza).symm
      have := has z hz; rw [hPz] at this; cases this
    unfold memStamp
    rw [hm, Option.bind_some]
    unfold stampByte
    rw [hfirst]
    rfl

/-- Every twin log message has an author (`R-log`). -/
theorem logAuthored (img : Image) (c : SbCand.CandS) (σ : MState) (hR : rmemP img c σ) :
    ∀ m ∈ c.ms.msLog, m.wmTid.isSome := by
  intro m hm
  have h1 : m.wmTid ∈ c.ms.msLog.map Wmsg.wmTid := List.mem_map_of_mem hm
  rw [hR.2.1] at h1
  obtain ⟨x, -, hx⟩ := List.mem_map.1 h1
  rw [← hx]; rfl

/-- **… AT A SINGLE-COPY CUT** (`scaByte`): the twin's byte at the source `t`, when not forwarded. -/
theorem byteFwdAtSca (img : Image) (c : SbCand.CandS) (σ : MState) (hR : rmemP img c σ) (cpu : CPU)
    (tvn : Nat) (a : PAddr) (ha : inRam a 1) (t : Nat) (v : BitVec 8)
    (hnf : SbCand.fwdByte (c.sb (hartAgent cpu)) (paZ a) = none)
    (hv : logByte img c.ms.msLog t (paZ a) = some v)
    (hs : scaByte img c.ms.msLog (hartAgent cpu) tvn (paZ a) t) :
    σ.byteFwd cpu tvn a = some v := by
  rw [byteFwdAt img c σ hR cpu tvn a ha, hnf, Option.none_or,
    histOfFind img c.ms.msLog (hartAgent cpu) tvn (paZ a) t v (logAuthored img c σ hR) hv hs]
  rfl

/-! # 2. The row -/

/-- **THE STATE MAP AFTER A PLAIN READ AT ANY VIEW `tvn ≤ ltop`**: only the read side moves. -/
theorem rmemPLoadAt (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (pa : PAddr) (n tvn : Nat)
    (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) (hR : rmemP img c σ) (htv : tvn ≤ σ.ltop) :
    rmemP img (SbCand.nextE c (hartAgent cpu) (LLoad aq base ts vs)) (σ.afterLoad cpu pa n tvn) := by
  obtain ⟨himg, hlog, hlogB, hH, hsb, hoth, hresv, hnd, hok⟩ := hR
  exact ⟨himg, hlog, hlogB, hH, hsb, hoth, hresv, hnd, σ.okP_afterLoad cpu pa n tvn htv hok⟩

/-- **THE VIEW CUT** of a plain read of `w` at `pa .. pa+n-1` by hart `cpu` at view `tvn`: the view bounds of
`evStep`'s plain-read arm, and every byte forwarded with `w`'s byte or not forwarded and read at a single-copy
cut from a source `t` holding `w`'s byte. -/
def ViewCut (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (pa : PAddr) (n : Nat)
    (w : BitVec (8 * n)) (tvn : Nat) : Prop :=
  σ.tv cpu ≤ tvn ∧ tvn ≤ σ.ltop ∧ (σ.hr cpu).cohOk pa n tvn ∧
  ∀ j, j < n →
    SbCand.fwdByte (c.sb (hartAgent cpu)) (paZ (pa + BitVec.ofNat 64 j)) = some (nthByte w j) ∨
    (SbCand.fwdByte (c.sb (hartAgent cpu)) (paZ (pa + BitVec.ofNat 64 j)) = none ∧
      ∃ t, logByte img c.ms.msLog t (paZ (pa + BitVec.ofNat 64 j)) = some (nthByte w j) ∧
        scaByte img c.ms.msLog (hartAgent cpu) tvn (paZ (pa + BitVec.ofNat 64 j)) t)

/-- **THE VIEW-READ LOAD ROW** [a′]: a plain RAM read whose bytes are the twin's forwarded-or-cut bytes is
MachCSL's plain read at the cut `tvn`; only the read side moves. -/
theorem evLoadViewP (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak) (w : BitVec (8 * n))
    (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) (tvn : Nat)
    (hR : rmemP img c σ) (hram : ramBytes req.pa n) (hpl : akPlain req.access_kind = true)
    (hcut : ViewCut img c σ cpu req.pa n w tvn) :
    evStep cpu (.memRead n va req) σ (.Ok (w, none)) (σ.afterLoad cpu req.pa n tvn) ∧
      rmemP img (SbCand.nextE c (hartAgent cpu) (LLoad aq base ts vs)) (σ.afterLoad cpu req.pa n tvn) := by
  obtain ⟨h1, h2, h3, hby⟩ := hcut
  refine ⟨.inr (.inr (.inl ⟨hram, hpl, tvn, w, h1, h2, h3, fun j hj => ?_, rfl, rfl⟩)),
    rmemPLoadAt img c σ cpu req.pa n tvn aq base ts vs hR h2⟩
  rcases hby j hj with hf | ⟨hnf, t, hv, hs⟩
  · rw [byteFwdAt img c σ hR cpu tvn _ (hram j hj), hf]; rfl
  · exact byteFwdAtSca img c σ hR cpu tvn _ (hram j hj) t _ hnf hv hs

/-! # 3. Where the cut comes from -/

/-- The largest coherence floor of the footprint. -/
def cohMax (hr : HRead) (pa : PAddr) (n : Nat) : Nat :=
  (List.range n).foldr (fun j m => max (hr.coh (pa + BitVec.ofNat 64 j)) m) 0

theorem cohFoldGe (hr : HRead) (pa : PAddr) (j : Nat) : ∀ l : List Nat, j ∈ l →
    hr.coh (pa + BitVec.ofNat 64 j) ≤ l.foldr (fun j m => max (hr.coh (pa + BitVec.ofNat 64 j)) m) 0
  | [], h => absurd h List.not_mem_nil
  | x :: l, h => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (cohFoldGe hr pa j l h) (Nat.le_max_right _ _)

theorem cohFoldLe (hr : HRead) (pa : PAddr) (L : Nat) : ∀ l : List Nat,
    (∀ i ∈ l, hr.coh (pa + BitVec.ofNat 64 i) ≤ L) →
    l.foldr (fun j m => max (hr.coh (pa + BitVec.ofNat 64 j)) m) 0 ≤ L
  | [], _ => Nat.zero_le _
  | x :: l, h => by
    simp only [List.foldr_cons]
    have h1 := h x List.mem_cons_self
    have h2 := cohFoldLe hr pa L l (fun i hi => h i (List.mem_cons_of_mem _ hi))
    omega

theorem cohLeMax (hr : HRead) (pa : PAddr) (n j : Nat) (h : j < n) :
    hr.coh (pa + BitVec.ofNat 64 j) ≤ cohMax hr pa n :=
  cohFoldGe hr pa j _ (List.mem_range.2 h)

theorem cohMaxLe (hr : HRead) (pa : PAddr) (L : Nat) (hb : ∀ a, hr.coh a ≤ L) (n : Nat) : cohMax hr pa n ≤ L :=
  cohFoldLe hr pa L _ (fun i _ => hb _)

/-- **WHERE THE CUT COMES FROM**: `tvn := max T (max tv cohMax)` is a view cut, given (a) the GF cut `T` (each
non-forwarded byte's source visible at `T` or own, every later write to the byte above `T`), (b) the floor
domination (`tv` and every coherence floor of the footprint below every such later write), (c) no such later
write is own. -/
theorem viewCutOf (img : Image) (c : SbCand.CandS) (σ : MState) (hR : rmemP img c σ) (cpu : CPU)
    (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (T : Nat) (hT : T ≤ σ.ltop)
    (hby : ∀ j, j < n →
      SbCand.fwdByte (c.sb (hartAgent cpu)) (paZ (pa + BitVec.ofNat 64 j)) = some (nthByte w j) ∨
      (SbCand.fwdByte (c.sb (hartAgent cpu)) (paZ (pa + BitVec.ofNat 64 j)) = none ∧
        ∃ t, logByte img c.ms.msLog t (paZ (pa + BitVec.ofNat 64 j)) = some (nthByte w j) ∧
          scaVis c.ms.msLog (hartAgent cpu) T t ∧
          ∀ t', t < t' → (logByte img c.ms.msLog t' (paZ (pa + BitVec.ofNat 64 j))).isSome →
            T < t' ∧ σ.tv cpu < t' ∧ (∀ i, i < n → (σ.hr cpu).coh (pa + BitVec.ofNat 64 i) < t') ∧
            ¬ (0 < t' ∧ ∃ m, c.ms.msLog[t' - 1]? = some m ∧ m.wmTid = some (hartAgent cpu)))) :
    ViewCut img c σ cpu pa n w (max T (max (σ.tv cpu) (cohMax (σ.hr cpu) pa n))) := by
  obtain ⟨a1, -, a3⟩ := hR.2.2.2.2.2.2.2.2.2.2.1 cpu
  have hcm := cohMaxLe (σ.hr cpu) pa σ.ltop a3.2 n
  refine ⟨by omega, by omega, fun j hj => ?_, fun j hj => ?_⟩
  · have := cohLeMax (σ.hr cpu) pa n j hj; omega
  · rcases hby j hj with hf | ⟨hnf, t, hv, hvis, hlater⟩
    · exact .inl hf
    · refine .inr ⟨hnf, t, hv, ⟨by rw [hv]; rfl, ?_, fun t' htt' hs' hvis' => ?_⟩⟩
      · rcases hvis with h | h
        · exact .inl (by omega)
        · exact .inr h
      · obtain ⟨b1, b2, b3, b4⟩ := hlater t' htt' hs'
        rcases hvis' with h | h
        · -- `t'` is above every term of the max
          have hcmt : cohMax (σ.hr cpu) pa n ≤ t' - 1 :=
            cohFoldLe (σ.hr cpu) pa (t' - 1) _ (fun i hi => by have := b3 i (List.mem_range.1 hi); omega)
          omega
        · exact b4 h

/-! # 4. The realizing plain read of the S-R walk -/

/-- **THE S-R WALK'S PER-BYTE CUT, in twin terms** at the load's base: every byte of the label (timestamp `t`,
value `v`) forwarded with its value, or not forwarded with its source `t` holding its value, visible at the GF cut `T` (or own), every later
write to the byte above `T`, above the hart's floor and every coherence floor of the footprint, and not own —
`viewCutOf`'s (a)–(c). -/
def CutBytes (c : SbCand.CandS) (σ : MState) (cpu : CPU) (pa : PAddr) (n : Nat) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) (T : Nat) : Prop :=
  ∀ j t v, j < n → ts[j]? = some t → vs[j]? = some v →
    SbCand.fwdByte (c.sb (hartAgent cpu)) (accAddr base j) = some v ∨
    (SbCand.fwdByte (c.sb (hartAgent cpu)) (accAddr base j) = none ∧
      logByte c.ms.msImg c.ms.msLog t (accAddr base j) = some v ∧
        scaVis c.ms.msLog (hartAgent cpu) T t ∧
        ∀ t', t < t' → (logByte c.ms.msImg c.ms.msLog t' (accAddr base j)).isSome →
          T < t' ∧ σ.tv cpu < t' ∧ (∀ i, i < n → (σ.hr cpu).coh (pa + BitVec.ofNat 64 i) < t') ∧
          ¬ (0 < t' ∧ ∃ m, c.ms.msLog[t' - 1]? = some m ∧ m.wmTid = some (hartAgent cpu)))

/-- **THE REALIZING PLAIN READ OF THE S-R WALK** [a′]: the pf node step of a plain RAM read with label `LLoad`
whose bytes pass the S-R walk's per-byte cut at a GF cut `T ≤ ltop` is MachCSL's plain read at the view
`max T (max tv cohMax)` (`evLoadViewP`). -/
theorem loadLblPR (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k : (Outcome.memRead (Register := Register) (RegisterType := RegisterType) n va req).ret → SailM Unit)
    (rs : RegFile) (ib : Ibch) (d : DevStates) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) (aq lat : Bool) (base : Int) (tvs : List (Nat × BitVec 8))
    (asrc : List Dsrc)
    (hst : pnodeStep (.impure (.ok (.memRead n va req)) k) rs ib d (.LLoad aq lat base tvs asrc) m' ors fn'
      d' oib obar)
    (hR : rmemP img c σ) (hram : devAddr req.pa = false → ramBytes req.pa n) (T : Nat) (hT : T ≤ σ.ltop)
    (ts : List Nat) (hts : ts.length = n) (hcut : CutBytes c σ cpu req.pa n base ts (tvs.map Prod.snd) T) :
    ∃ (w : BitVec (8 * n)) (tvn : Nat), m' = k (.Ok (w, none)) ∧
      evStep cpu (.memRead n va req) σ (.Ok (w, none)) (σ.afterLoad cpu req.pa n tvn) ∧
      rmemP img (SbCand.nextE c (hartAgent cpu) (LLoad aq base ts (tvs.map Prod.snd)))
        (σ.afterLoad cpu req.pa n tvn) := by
  simp only [pnodeStep] at hst
  split at hst
  · obtain ⟨w, -, h, -⟩ := hst; cases h
  · rename_i hda
    have hda' : devAddr req.pa = false := by simpa using hda
    rcases hst with ⟨-, w, tvs', -, -, h, -⟩ | ⟨hif, ⟨hlat, w, tvs', hlen, hb, hl, hm, -⟩ | ⟨-, w, tvs', -, -, h, -⟩⟩
    · cases h
    · injection hl with h1 h2 h3 h4 h5
      subst h3 h4
      have hram' := hram hda'
      have hnw := noWrapOfRam req.pa n hram'
      have hpl : akPlain req.access_kind = true := by
        have h1 : akIfetch req.access_kind = false := hif
        have h2 : akExcl req.access_kind = false := hlat
        simp [akPlain, h1, h2]
      have himg : c.ms.msImg = img := hR.1
      have hvc := viewCutOf img c σ hR cpu req.pa n w T hT (fun j hj => by
        rw [paZAddJ req.pa n j hnw hj, ← himg]
        obtain ⟨t, htj⟩ : ∃ t, ts[j]? = some t := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        rcases hcut j t (nthByte w j) hj htj (hb j hj) with h | ⟨h1, h2, h3, h4⟩
        · exact .inl h
        · exact .inr ⟨h1, t, h2, h3, h4⟩)
      exact ⟨w, _, hm, evLoadViewP img c σ cpu n va req w aq (paZ req.pa) ts _ _ hR hram'
        hpl hvc⟩
    · cases h

#print axioms Weak.SbRealPView.loadLblPR
#print axioms Weak.SbRealPView.evLoadViewP
#print axioms Weak.SbRealPView.viewCutOf

end SbRealPView

end Weak
