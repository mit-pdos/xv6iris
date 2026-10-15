/-
Weak: **r2 glue (C) — `cyFB` along the hart's real steps** (`PROGRESS-r2glue.md`).  Lean-only.

`cyFRun` (w1's `PinCycRun.cyRun` / our `PinDataOk.cyDRun`, for `cyFB`): along an in-cycle run
(`irun`) from a tree under `cyFB` at a matched state, if every RAM-read label is `D`-admitted
(`labD`) and every device read too, then every instruction-fetch label of the run is at the
address the obligation names: the `k`-th fetch label (`k` = the fetch labels before it) satisfies
`Aa (|fe| + k)`.  Every helper is `Weak.PinFetchPa.*`.
-/
import Weak.PinFetchPaCyc
import Weak.PinDataOkRun

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open Wlabel

namespace PinFetchPa
open SailCycleOrderK PinCycRun PinDataflow
open PinDataOk (labD labDOf)

section run
variable {D : BitVec 64 → (n : Nat) → BitVec (8 * n) → Prop} {Aa : Nat → Int → Prop}
  {P : Unit → CySt → Prop}

/-- One step's conclusion: the label's fetch obligation, and a matched state for the new tree. -/
def cyFStepOk (D : BitVec 64 → (n : Nat) → BitVec (8 * n) → Prop) (Aa : Nat → Int → Prop)
    (P : Unit → CySt → Prop) (st : CySt) (l : Wlabel) (m' : SailM Unit) (ib' : Ibch) (rs' : RegFile) :
    Prop :=
  (∀ a tvs, l = LIFetch a tvs → Aa st.fe.length a) ∧
  ∃ st', cyFB D Aa P m' st' ∧ cyMatch st' rs' ib' ∧ st'.fe.length = st.fe.length + (feLabs [l]).length

theorem cyFStay (st : CySt) (l : Wlabel) (m' : SailM Unit) (ib : Ibch) (rs : RegFile)
    (hcy : cyFB D Aa P m' st) (hm : cyMatch st rs ib) (hfe : isFeLab l = false) :
    cyFStepOk D Aa P st l m' ib rs :=
  ⟨fun a tvs e => (by subst e; cases hfe), st, hcy, hm, by simp [feLabs, hfe]⟩

set_option maxHeartbeats 4000000 in
/-- **One Sail node.** -/
theorem cyFNodeStep (m : SailM Unit) (rs : RegFile) (ib : Ibch) (dd : DevStates) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (dd' : DevStates)
    (oib : Option Ibch) (obar : Option barrier_kind) (st : CySt)
    (hstep : pnodeStep m rs ib dd l m' ors fn' dd' oib obar) (hpure : ∀ x, m ≠ .pure x)
    (hcy : cyFB D Aa P m st) (hm : cyMatch st rs ib) (hL : labD D l)
    (hdev : ∀ pa n w, devAddr pa = true → D pa n w) :
    cyFStepOk D Aa P st l m' (oib.getD ib) (ors.getD rs) := by
  obtain ⟨hag, hrb, hrbv, hro, hrds, han⟩ := hm
  match m, hstep with
  | .pure x, _ => exact absurd rfl (hpure x)
  | .impure (.error _) _, h => exact h.elim
  | .impure (.ok o) k, h =>
    cases o with
    | regRead r =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      have hv : PinCycRun.rdOk st r (rs r) := fun hw => hag r hw
      refine ⟨fun a tvs e => (by cases e), cyRd st r, hcy (rs r) hv, ⟨hag, hrb, hrbv, ?_, ?_, ?_⟩,
        by simp [feLabs, isFeLab, cyRd]⟩
      · show st.d.ro = depsOfIb (ibRd ib r).ibBits
        rw [ibRdBits]; exact hro
      · show dfRdsAdd st.d.rds (eregNum r) = (ibRd ib r).ibRds
        rw [hrds]; exact (dfRdsAddIb ib (eregNum r)).symm
      · show st.an = (ibRd ib r).ibBits.isSome
        rw [ibRdBits]; exact han
    | regWrite r v =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      obtain ⟨hrv, hk⟩ := hcy
      have hfl : isFeLab (erwLabel (erwOf (depsOfIb ib.ibBits) ib.ibRds r)) = false := by
        unfold erwLabel; split <;> rfl
      refine ⟨fun a tvs e => (by rw [e] at hfl; cases hfl), cyWr st r v, hk (),
        ⟨PinCycRun.agreeSet rs st.rv r v hag, rbootAllSet rs r v hrb hrv,
          rbootAllSet st.rv r v hrbv hrv, hro, hrds, han⟩, ?_⟩
      simp [feLabs, hfl, cyWr]
    | memRead n va req =>
      simp only [pnodeStep] at h
      split at h
      · rename_i hdv
        obtain ⟨w, -, rfl, rfl, rfl, -, rfl, -⟩ := h
        exact cyFStay st _ _ ib rs
          (hcy.2 (fun h' => absurd (hdv.symm.trans h') (by decide)) _ (hdev _ n w hdv))
          ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
      · rename_i hdv
        have hdev' : devAddr req.pa = false := by simpa using hdv
        rcases h with ⟨hif, w, tvs, hlen, hb, rfl, rfl, rfl, -, -, rfl, -⟩ |
          ⟨hif, ⟨-, w, tvs, hlen, hb, rfl, rfl, rfl, -, -, rfl, -⟩ |
            ⟨-, w, tvs, hlen, hb, rfl, rfl, rfl, -, -, rfl, -⟩⟩
        · obtain ⟨ha, hk⟩ := hcy.1 hdev' hif
          refine ⟨fun a tvs' e => ?_, cyFe st (paZ req.pa) n w, hk w (labDOf hlen hb hL),
            ⟨hag, hrb, hrbv, hro, hrds, han⟩, by simp [feLabs, isFeLab, cyFe]⟩
          injection e with e
          rw [← e]; exact ha
        · exact cyFStay st _ _ ib rs (hcy.2 (fun _ => hif) _ (labDOf hlen hb hL))
            ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
        · exact cyFStay st _ _ ib rs (hcy.2 (fun _ => hif) _ (labDOf hlen hb hL))
            ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | memWrite n va req =>
      simp only [pnodeStep] at h
      split at h
      · split at h
        · obtain ⟨-, rfl, rfl, rfl, -, rfl, -⟩ := h
          exact cyFStay st _ _ ib rs hcy ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
        · exact h.elim
      · split at h
        · obtain ⟨-, h⟩ := h
          rcases h with ⟨-, rfl, rfl, rfl, -, -, rfl, -⟩ |
            ⟨-, ⟨rfl, rfl, rfl, -, -, rfl, -⟩ | ⟨rfl, rfl, rfl, -, -, rfl, -⟩⟩
          · exact cyFStay st _ _ ib rs hcy ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
          · exact cyFStay st _ _ ib rs hcy ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
          · exact cyFStay st _ _ ib rs hcy ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
        · exact h.elim
    | barrier b =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      refine cyFStay st _ _ ib rs (hcy ()) ⟨hag, hrb, hrbv, hro, hrds, han⟩ ?_
      unfold ebarLabel
      split <;> rfl
    | instrAnnounce n w =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      obtain ⟨han0, hk⟩ := hcy
      have hfl : isFeLab (annLabel n w) = false := by unfold annLabel; split <;> rfl
      refine ⟨fun a tvs e => (by rw [e] at hfl; cases hfl), cyAnn st n w, hk (),
        ⟨hag, hrb, hrbv, rfl, rfl, rfl⟩, ?_⟩
      simp [feLabs, hfl, cyAnn]
    | choose s =>
      obtain ⟨ch, rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact cyFStay st _ _ ib rs (hcy ch) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | readRam => exact h.elim
    | writeRam => exact h.elim
    | getCycleCount =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact cyFStay st _ _ ib rs hcy ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | branchAnnounce =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact cyFStay st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | cacheOp =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact cyFStay st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | tlbi =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact cyFStay st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | takeException =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact cyFStay st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | returnException =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact cyFStay st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | translationStart =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact cyFStay st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | translationEnd =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact cyFStay st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | cycleCount =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact cyFStay st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl
    | message =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact cyFStay st _ _ ib rs (hcy _) ⟨hag, hrb, hrbv, hro, hrds, han⟩ rfl

/-- **One hart step**: a Sail node, a parked fence firing, or a PLIC wire write. -/
theorem cyFHartStep (cpu : CPU) (m : SailM Unit) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool))
    (ib : Ibch) (d : Efab) (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : Efab) (oib : Option Ibch)
    (obar : Option barrier_kind) (st : CySt)
    (hstep : pstepHart cpu m rs fn ib d l m' ors fn' d' oib obar) (hpure : ∀ x, m ≠ .pure x)
    (hcy : cyFB D Aa P m st) (hm : cyMatch st rs ib) (hL : labD D l)
    (hdev : ∀ pa n w, devAddr pa = true → D pa n w) :
    cyFStepOk D Aa P st l m' (oib.getD ib) (ors.getD rs) := by
  rcases hstep with ⟨H, hd⟩ | H
  · cases fn with
    | some f =>
      obtain ⟨pr, pw, sr, sw⟩ := f
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := H
      exact cyFStay st _ _ ib rs hcy hm rfl
    | none => exact cyFNodeStep m rs ib d.efDev l m' ors fn' d'.efDev oib obar st H hpure hcy hm hL hdev
  · obtain ⟨mm, b, k, -, rfl, rfl, -, -, rfl, -, rfl⟩ := H
    obtain ⟨hag, hrb, hrbv, hro, hrds, han⟩ := hm
    refine cyFStay st _ _ ib _ hcy ⟨?_, ?_, hrbv, hro, hrds, han⟩ rfl
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

/-- **THE RUN** (header): every fetch label of an in-cycle run meets the obligation. -/
theorem cyFRun :
    ∀ (ls : List Wlabel) (p : Pexv6) (d : Efab) (p' : Pexv6) (d' : Efab), irun ls p d p' d' →
    ∀ (cpu : CPU) (m : SailM Unit) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool))
      (ib : Ibch) (st : CySt), p = .PHart cpu m rs fn ib → cyFB D Aa P m st → cyMatch st rs ib →
      (∀ l ∈ ls, labD D l) → (∀ pa n w, devAddr pa = true → D pa n w) →
      ∀ (ls1 : List Wlabel) (a : Int) (tvs : List (Nat × BitVec 8)) (ls2 : List Wlabel),
        ls = ls1 ++ LIFetch a tvs :: ls2 → Aa (st.fe.length + (feLabs ls1).length) a := by
  intro ls p d p' d' h
  induction h with
  | nil p d =>
    intro _ _ _ _ _ _ _ _ _ _ _ ls1 a tvs ls2 e
    cases ls1 <;> cases e
  | @more l ls cpu c k rs fn ib d p1 d1 p2 d2 hstep hrest ih =>
    intro cpu' m rs' fn' ib' st hp hcy hm hL hdev ls1 a tvs ls2 e
    injection hp with e1 e2 e3 e4 e5
    subst e1 e2 e3 e4 e5
    cases p1 with
    | PDisk dp => exact (show False from hstep).elim
    | PHart cpu1 m1 rs1 fn1 ib1 =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hh⟩ := hstep
    obtain ⟨hA, st', hcy', hm', hlen⟩ := cyFHartStep cpu1 _ rs fn ib d l m1 ors fn1 d1 oib obar st hh
      (fun x e => by cases e) hcy hm (hL l List.mem_cons_self) hdev
    cases ls1 with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at e
      obtain ⟨rfl, -⟩ := e
      simpa [feLabs] using hA a tvs rfl
    | cons l' ls1' =>
      simp only [List.cons_append, List.cons.injEq] at e
      obtain ⟨rfl, e⟩ := e
      have := ih cpu1 m1 (ors.getD rs) fn1 (oib.getD ib) st' rfl hcy' hm'
        (fun l'' hl'' => hL l'' (List.mem_cons_of_mem _ hl'')) hdev ls1' a tvs ls2 e
      rw [hlen, Nat.add_assoc, ← List.length_append] at this
      have e2 : feLabs [l] ++ feLabs ls1' = feLabs (l :: ls1') := by
        simp only [feLabs, List.filter_cons, List.filter_nil]
        split <;> rfl
      rw [e2] at this
      exact this
  | @jump ls p d e p2 d2 _ ih =>
    intro cpu m rs fn ib st hp hcy hm hL hdev ls1 a tvs ls2 he
    exact ih cpu m rs fn ib st hp hcy hm hL hdev ls1 a tvs ls2 he

end run

end PinFetchPa
end Weak
