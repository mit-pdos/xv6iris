/-
Weak: **`dataOkR` (4b) — `cyDB` along the hart's real steps** (w1's `PinCycRun.cyNodeStep` /
`cyHartStep` / `cyRun`, `Weak/PinCycRun.lean:220-627`, adapted to the filters): along an in-cycle
run (`irun`) from a tree under `cyDB` at a matched state, if every register read of the run is
`G`-admitted (`atRegRead`), every RAM-read label `D`-admitted (`labD`), every device read too, and
every fetch label admitted as w1's (`feAdm`), then either the run passed an EXCEPTION's cause write
(a stop node, with the stop post) or it ends at a tree still under `cyDB` at a matched state
(`PROGRESS-dataOk.md`).  Lean-only.  Every helper is `Weak.PinDataOk.*`.
-/
import Weak.PinDataOkCy

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open Wlabel

namespace PinDataOk
open SailCycleOrderK PinCycRun PinDataflow

/-- The answer filter on a label's address and bytes. -/
def labD (D : BitVec 64 → (n : Nat) → BitVec (8 * n) → Prop) : Wlabel → Prop
  | .LLoad _ _ a tvs _ => ∀ (pa : BitVec 64) (n : Nat) (w : BitVec (8 * n)), paZ pa = a →
      tvs.map Prod.snd = (List.range n).map (fun j => nthByte w j) → D pa n w
  | .LExLoad _ a tvs _ => ∀ (pa : BitVec 64) (n : Nat) (w : BitVec (8 * n)), paZ pa = a →
      tvs.map Prod.snd = (List.range n).map (fun j => nthByte w j) → D pa n w
  | .LIFetch a tvs => ∀ (pa : BitVec 64) (n : Nat) (w : BitVec (8 * n)), paZ pa = a →
      tvs.map Prod.snd = (List.range n).map (fun j => nthByte w j) → D pa n w
  | _ => True

theorem labDOfAnsOk (c : DCfg) (l : Wlabel) (h : labAnsOkD c l) : labD (dAns c) l := by
  cases l <;> first | exact h | trivial

/-- The hart is at an EXCEPTION's cause write, with the stop post. -/
def cyDStopAt (T : CySt → (r : Register) → RegisterType r → Prop) (st : CySt) (m : SailM Unit) : Prop :=
  ∃ (r : Register) (v : RegisterType r) (k : Unit → SailM Unit),
    m = .impure (.ok (.regWrite r v)) k ∧ cyS r = true ∧ causeBit r v = false ∧ T st r v

section run
variable {G : (r : Register) → RegisterType r → Prop} {D : BitVec 64 → (n : Nat) → BitVec (8 * n) → Prop}
  {A : Int → BitVec 8 → Prop} {Aa : Nat → Int → Prop} {T : CySt → (r : Register) → RegisterType r → Prop}
  {P : Unit → CySt → Prop}

/-- One step's conclusion off a stop. -/
def cyDStepOk (G : (r : Register) → RegisterType r → Prop) (D : BitVec 64 → (n : Nat) → BitVec (8 * n) → Prop)
    (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (T : CySt → (r : Register) → RegisterType r → Prop)
    (P : Unit → CySt → Prop) (st : CySt) (l : Wlabel) (m' : SailM Unit) (ib' : Ibch) (rs' : RegFile) : Prop :=
  ∃ st', cyDB G D A Aa T P m' st' ∧ cyMatch st' rs' ib' ∧ st'.fe.length = st.fe.length + (feLabs [l]).length

theorem cyDStay (st : CySt) (l : Wlabel) (m' : SailM Unit) (ib : Ibch) (rs : RegFile)
    (hcy : cyDB G D A Aa T P m' st) (hm : cyMatch st rs ib) (hfe : isFeLab l = false) :
    cyDStepOk G D A Aa T P st l m' ib rs :=
  ⟨st, hcy, hm, by simp [feLabs, hfe]⟩

/-- A label's bytes in the `labD` form. -/
theorem labDOf {pa : BitVec 64} {n : Nat} {w : BitVec (8 * n)} {tvs : List (Nat × BitVec 8)}
    (hl : tvs.length = n) (hb : ∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w j))
    (h : ∀ (pa' : BitVec 64) (n' : Nat) (w' : BitVec (8 * n')), paZ pa' = paZ pa →
      tvs.map Prod.snd = (List.range n').map (fun j => nthByte w' j) → D pa' n' w') : D pa n w :=
  h pa n w rfl (PinFetchVal.tvsView w tvs hl hb)

set_option maxHeartbeats 4000000 in
/-- **One Sail node.** -/
theorem cyDNodeStep (m : SailM Unit) (rs : RegFile) (ib : Ibch) (dd : DevStates) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (dd' : DevStates)
    (oib : Option Ibch) (obar : Option barrier_kind) (st : CySt)
    (hstep : pnodeStep m rs ib dd l m' ors fn' dd' oib obar) (hpure : ∀ x, m ≠ .pure x)
    (hcy : cyDB G D A Aa T P m st) (hm : cyMatch st rs ib) (hA : feAdm A Aa st.fe.length l)
    (hG : ∀ r k, m = .impure (.ok (.regRead r)) k → G r (rs r)) (hL : labD D l)
    (hdev : ∀ pa n w, devAddr pa = true → D pa n w) :
    cyDStopAt T st m ∨ cyDStepOk G D A Aa T P st l m' (oib.getD ib) (ors.getD rs) := by
  obtain ⟨hag, hrb, hrbv, hro, hrds, han⟩ := hm
  match m, hstep with
  | .pure x, _ => exact absurd rfl (hpure x)
  | .impure (.error _) _, h => exact h.elim
  | .impure (.ok o) k, h =>
    cases o with
    | regRead r =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      have hv : PinCycRun.rdOk st r (rs r) := fun hw => hag r hw
      refine ⟨cyRd st r, hcy (rs r) hv (hG r k rfl), ⟨hag, hrb, hrbv, ?_, ?_, ?_⟩, by simp [feLabs, isFeLab, cyRd]⟩
      · show st.d.ro = depsOfIb (ibRd ib r).ibBits
        rw [ibRdBits]; exact hro
      · show dfRdsAdd st.d.rds (eregNum r) = (ibRd ib r).ibRds
        rw [hrds]; exact (dfRdsAddIb ib (eregNum r)).symm
      · show st.an = (ibRd ib r).ibBits.isSome
        rw [ibRdBits]; exact han
    | regWrite r v =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      by_cases hst : cyS r = true ∧ causeBit r v = false
      · exact Or.inl ⟨r, v, k, rfl, hst.1, hst.2, hcy.1 hst.1 hst.2⟩
      · right
        have hor : cyS r = false ∨ causeBit r v = true := by
          cases h1 : cyS r <;> cases h2 : causeBit r v <;> simp_all
        obtain ⟨hrv, hk⟩ := hcy.2 hor
        refine ⟨cyWr st r v, hk (), ⟨PinCycRun.agreeSet rs st.rv r v hag,
          rbootAllSet rs r v hrb hrv, rbootAllSet st.rv r v hrbv hrv, hro, hrds, han⟩, ?_⟩
        have : isFeLab (erwLabel (erwOf (depsOfIb ib.ibBits) ib.ibRds r)) = false := by
          unfold erwLabel; split <;> rfl
        simp [feLabs, this, cyWr]
    | memRead n va req =>
      simp only [pnodeStep] at h
      split at h
      · rename_i hdv
        obtain ⟨w, -, rfl, rfl, rfl, -, rfl, -⟩ := h
        right
        exact cyDStay st _ _ ib rs
          (hcy.2 (fun h' => absurd (hdv.symm.trans h') (by decide)) _ (hdev _ n w hdv))
          ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
      · rename_i hdv
        have hdev' : devAddr req.pa = false := by simpa using hdv
        rcases h with ⟨hif, w, tvs, hlen, hb, rfl, rfl, rfl, -, -, rfl, -⟩ |
          ⟨hif, ⟨-, w, tvs, hlen, hb, rfl, rfl, rfl, -, -, rfl, -⟩ |
            ⟨-, w, tvs, hlen, hb, rfl, rfl, rfl, -, -, rfl, -⟩⟩
        · right
          have hel : ∀ j (hj : j < tvs.length), (tvs[j]'hj).2 = nthByte w j := by
            intro j hj
            have h2 := hb j (by rw [← hlen]; exact hj)
            simp only [List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some,
              Option.some.injEq] at h2
            exact h2
          have hAw : ∀ j, j < n → A (paZ req.pa + (j : Int)) (nthByte w j) := by
            intro j hj
            have hj' : j < tvs.length := by rw [hlen]; exact hj
            rw [← hel j hj']; exact (hA _ tvs rfl).2 j hj'
          exact ⟨cyFe st (paZ req.pa) n w, hcy.1 hdev' hif (hA _ tvs rfl).1 w hAw (labDOf hlen hb hL),
            ⟨hag, hrb, hrbv, hro, hrds, han⟩, by simp [feLabs, isFeLab, cyFe]⟩
        · right
          exact cyDStay st _ _ ib rs (hcy.2 (fun _ => hif) _ (labDOf hlen hb hL))
            ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
        · right
          exact cyDStay st _ _ ib rs (hcy.2 (fun _ => hif) _ (labDOf hlen hb hL))
            ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | memWrite n va req =>
      simp only [pnodeStep] at h
      right
      split at h
      · split at h
        · obtain ⟨-, rfl, rfl, rfl, -, rfl, -⟩ := h
          exact cyDStay st _ _ ib rs hcy ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
        · exact h.elim
      · split at h
        · obtain ⟨-, h⟩ := h
          rcases h with ⟨-, rfl, rfl, rfl, -, -, rfl, -⟩ |
            ⟨-, ⟨rfl, rfl, rfl, -, -, rfl, -⟩ | ⟨rfl, rfl, rfl, -, -, rfl, -⟩⟩
          · exact cyDStay st _ _ ib rs hcy ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
          · exact cyDStay st _ _ ib rs hcy ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
          · exact cyDStay st _ _ ib rs hcy ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
        · exact h.elim
    | barrier b =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      refine cyDStay st _ _ ib rs (hcy ()) ⟨hag, hrb, hrbv, hro, hrds, han⟩ ?_
      unfold ebarLabel
      split <;> rfl
    | instrAnnounce n w =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      obtain ⟨han0, hk⟩ := hcy
      refine ⟨cyAnn st n w, hk (), ⟨hag, hrb, hrbv, rfl, rfl, rfl⟩, ?_⟩
      have : isFeLab (annLabel n w) = false := by unfold annLabel; split <;> rfl
      simp [feLabs, this, cyAnn]
    | choose s =>
      obtain ⟨ch, rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      exact cyDStay st _ _ ib rs (hcy ch) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | readRam => exact h.elim
    | writeRam => exact h.elim
    | getCycleCount =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      exact cyDStay st _ _ ib rs hcy ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | branchAnnounce =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      exact cyDStay st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | cacheOp =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      exact cyDStay st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | tlbi =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      exact cyDStay st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | takeException =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      exact cyDStay st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | returnException =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      exact cyDStay st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | translationStart =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      exact cyDStay st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | translationEnd =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      exact cyDStay st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | cycleCount =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      exact cyDStay st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | message =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      right
      exact cyDStay st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl

/-- **One hart step**: a Sail node, a parked fence firing, or a PLIC wire write. -/
theorem cyDHartStep (cpu : CPU) (m : SailM Unit) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool))
    (ib : Ibch) (d : Efab) (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : Efab) (oib : Option Ibch)
    (obar : Option barrier_kind) (st : CySt)
    (hstep : pstepHart cpu m rs fn ib d l m' ors fn' d' oib obar) (hpure : ∀ x, m ≠ .pure x)
    (hcy : cyDB G D A Aa T P m st) (hm : cyMatch st rs ib) (hA : feAdm A Aa st.fe.length l)
    (hG : ∀ r k, m = .impure (.ok (.regRead r)) k → G r (rs r)) (hL : labD D l)
    (hdev : ∀ pa n w, devAddr pa = true → D pa n w) :
    cyDStopAt T st m ∨ cyDStepOk G D A Aa T P st l m' (oib.getD ib) (ors.getD rs) := by
  rcases hstep with ⟨H, hd⟩ | H
  · cases fn with
    | some f =>
      obtain ⟨pr, pw, sr, sw⟩ := f
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := H
      exact Or.inr (cyDStay st _ _ ib rs hcy hm rfl)
    | none => exact cyDNodeStep m rs ib d.efDev l m' ors fn' d'.efDev oib obar st H hpure hcy hm hA hG hL hdev
  · obtain ⟨mm, b, k, -, rfl, rfl, -, -, rfl, -, rfl⟩ := H
    right
    obtain ⟨hag, hrb, hrbv, hro, hrds, han⟩ := hm
    refine cyDStay st _ _ ib _ hcy ⟨?_, ?_, hrbv, hro, hrds, han⟩ rfl
    · show ∀ r, wireReg r = false → (pinSet rs mm b) r = st.rv r
      unfold pinSet
      split
      · exact PinCycRun.agreeSetWire rs st.rv _ _ rfl hag
      · exact PinCycRun.agreeSetWire rs st.rv _ _ rfl hag
    · show RbootAll (pinSet rs mm b)
      unfold pinSet
      split
      · exact rbootAllSet rs _ _ hrb trivial
      · exact rbootAllSet rs _ _ hrb trivial

/-- The premises of a run at a prefix: the reads, the labels, the fetch admission. -/
def runPrem (G : (r : Register) → RegisterType r → Prop) (D : BitVec 64 → (n : Nat) → BitVec (8 * n) → Prop)
    (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (k0 : Nat) (p1 : Pexv6) (ls1 : List Wlabel)
    (l : Wlabel) : Prop :=
  atRegRead p1 G ∧ labD D l ∧ feAdm A Aa (k0 + (feLabs ls1).length) l

/-- **THE RUN** (header). -/
theorem cyDRun :
    ∀ (ls : List Wlabel) (p : Pexv6) (d : Efab) (p' : Pexv6) (d' : Efab), irun ls p d p' d' →
    ∀ (cpu : CPU) (m : SailM Unit) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool))
      (ib : Ibch) (st : CySt), p = .PHart cpu m rs fn ib → cyDB G D A Aa T P m st → cyMatch st rs ib →
      (∀ ls1 l ls2 pm dm, ls = ls1 ++ l :: ls2 → irun ls1 p d pm dm → runPrem G D A Aa st.fe.length pm ls1 l) →
      (∀ pa n w, devAddr pa = true → D pa n w) →
      (∃ (ls1 ls2 : List Wlabel) (m1 : SailM Unit) (rs1 : RegFile) (fn1 : Option (Bool × Bool × Bool × Bool))
          (ib1 : Ibch) (d1 : Efab) (st1 : CySt),
        ls = ls1 ++ ls2 ∧ irun ls1 p d (.PHart cpu m1 rs1 fn1 ib1) d1 ∧ cyDStopAt T st1 m1 ∧
          cyMatch st1 rs1 ib1) ∨
      (∃ (m1 : SailM Unit) (rs1 : RegFile) (fn1 : Option (Bool × Bool × Bool × Bool)) (ib1 : Ibch) (st1 : CySt),
        p' = .PHart cpu m1 rs1 fn1 ib1 ∧ cyDB G D A Aa T P m1 st1 ∧ cyMatch st1 rs1 ib1) := by
  intro ls p d p' d' h
  induction h with
  | nil p d =>
    intro cpu m rs fn ib st hp hcy hm _ _
    subst hp
    exact Or.inr ⟨m, rs, fn, ib, st, rfl, hcy, hm⟩
  | @more l ls cpu c k rs fn ib d p1 d1 p2 d2 hstep hrest ih =>
    intro cpu' m rs' fn' ib' st hp hcy hm hP hdev
    injection hp with e1 e2 e3 e4 e5
    subst e1 e2 e3 e4 e5
    cases p1 with
    | PDisk dp => exact (show False from hstep).elim
    | PHart cpu1 m1 rs1 fn1 ib1 =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hh⟩ := hstep
    have hst : pstepEv (.PHart cpu1 (.impure c k) rs fn ib) d l
        (.PHart cpu1 m1 (ors.getD rs) fn1 (oib.getD ib)) d1 :=
      ⟨rfl, ors, oib, obar, rfl, rfl, hh⟩
    obtain ⟨hG0, hL0, hA0⟩ := hP [] l ls _ d rfl (irun.nil _ _)
    have hA0' : feAdm A Aa st.fe.length l := by simpa [feLabs] using hA0
    rcases cyDHartStep cpu1 _ rs fn ib d l m1 ors fn1 d1 oib obar st hh (fun x e => by cases e) hcy hm hA0'
        (fun r k' e => hG0 cpu1 r k' rs fn ib (by rw [e])) hL0 hdev with hstop | ⟨st', hcy', hm', hlen⟩
    · exact Or.inl ⟨[], l :: ls, _, rs, fn, ib, d, st, rfl, irun.nil _ _, hstop, hm⟩
    · rcases ih cpu1 m1 (ors.getD rs) fn1 (oib.getD ib) st' rfl hcy' hm'
          (fun ls1 l' ls2 pm dm e hir1 => by
            obtain ⟨g1, g2, g3⟩ := hP (l :: ls1) l' ls2 pm dm (by rw [e]; rfl) (irun.more hst hir1)
            refine ⟨g1, g2, ?_⟩
            rw [hlen, Nat.add_assoc, ← List.length_append]
            have e2 : feLabs [l] ++ feLabs ls1 = feLabs (l :: ls1) := by
              simp only [feLabs, List.filter_cons, List.filter_nil]
              split <;> rfl
            rw [e2]; exact g3) hdev with
        ⟨ls1, ls2, mm, rr, ff, ii, dd, st1, rfl, r1, hs, hmm⟩ |
        ⟨mm, rr, ff, ii, st1, rfl, hc, hmm⟩
      · exact Or.inl ⟨l :: ls1, ls2, mm, rr, ff, ii, dd, st1, rfl, irun.more hst r1, hs, hmm⟩
      · exact Or.inr ⟨mm, rr, ff, ii, st1, rfl, hc, hmm⟩
  | @jump ls p d e p2 d2 _ ih =>
    intro cpu m rs fn ib st hp hcy hm hP hdev
    rcases ih cpu m rs fn ib st hp hcy hm (fun ls1 l ls2 pm dm h hir => hP ls1 l ls2 pm dm h (.jump hir))
        hdev with ⟨ls1, ls2, m1, rs1, fn1, ib1, d1, st1, h1, h2, h3, h4⟩ | h
    · exact Or.inl ⟨ls1, ls2, m1, rs1, fn1, ib1, d1, st1, h1, .jump h2, h3, h4⟩
    · exact Or.inr h

end run

end PinDataOk
end Weak
