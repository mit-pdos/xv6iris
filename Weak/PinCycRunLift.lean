/-
Weak: **W9a (B) B5 cycRun — lifting footprints into the cycle predicate** ([OWN.85] Q-B5-CYCLE
= C1; report `PROGRESS-cycRun.md`).  Lean-only.

The cycle predicate `PinCycRun.cyB` (`Weak/PinCycRun.lean`) answers register reads from its
mirror; a footprint answers them by every `Rboot`-admitted value, so a footprint fact covers the
mirror's path whenever the mirror is `Rboot`-admitted.  Three lifts:
* `cyOfPfDf`: a `pfB` footprint (no protected write, `Weak/PinCycRunFp.lean`) together with B1's
  dataflow fact `dfB` of the same tree — the post sees the footprint's post, the protected mirror
  KEPT (`cyFrame`), the log and the announce flag kept, and the dataflow post at the dataflow
  state the path reached;
* `cyOfPf`: the same without a dataflow post;
* `cyOfFp`: a W-SCO strict footprint `fp` (any `Rboot` write, `Weak/SailCycleOrderFp.lean`) for a
  tree whose stop nodes (cause writes) owe a stop post that holds at every state with the same log
  — the trap paths before the fetch.

Every helper is `Weak.PinCycRun.*`.
-/
import Weak.PinCycRun
import Weak.PinCycRunFp
import Weak.SailCycleOrderFp

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinCycRun
open SailCycleOrderK PinDataflow
open PinCycRunFp (pfB pfProt pfRegOk pfW)

/-- The FRAME of a lifted piece: the protected mirror kept, the mirror `Rboot`-admitted, the log
and the announce flag kept. -/
def cyFrame (st st' : CySt) : Prop :=
  (∀ r, pfProt r = true → st'.rv r = st.rv r) ∧ RbootAll st'.rv ∧ st'.fe = st.fe ∧ st'.an = st.an

theorem cyFrameRefl (st : CySt) (h : RbootAll st.rv) : cyFrame st st :=
  ⟨fun _ _ => rfl, h, rfl, rfl⟩

theorem cyFrameTrans (s1 s2 s3 : CySt) : cyFrame s1 s2 → cyFrame s2 s3 → cyFrame s1 s3 := by
  rintro ⟨a1, -, c1, d1⟩ ⟨a2, b2, c2, d2⟩
  exact ⟨fun r h => (a2 r h).trans (a1 r h), b2, c2.trans c1, d2.trans d1⟩

theorem PinCycRun.rbootWire (r : Register) (v : RegisterType r) (h : wireReg r = true) :
    Rboot r v := by
  unfold wireReg at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with rfl | rfl <;> trivial

theorem PinCycRun.rdRboot (st : CySt) (r : Register) (v : RegisterType r) (hrb : RbootAll st.rv)
    (h : rdOk st r v) : Rboot r v := by
  cases hw : wireReg r
  · rw [h hw]; exact hrb r
  · exact PinCycRun.rbootWire r v hw

theorem PinCycRun.frameRd (st : CySt) (r : Register) (hrb : RbootAll st.rv) :
    cyFrame st (cyRd st r) := cyFrameRefl _ hrb

theorem PinCycRun.frameWr (st : CySt) (r : Register) (v : RegisterType r) (hrb : RbootAll st.rv)
    (hp : pfProt r = false) (hv : Rboot r v) : cyFrame st (cyWr st r v) := by
  refine ⟨fun r' h' => ?_, rbootAllSet _ r v hrb hv, rfl, rfl⟩
  have e : r' ≠ r := by rintro rfl; rw [hp] at h'; cases h'
  exact RegFile.set_other _ _ _ _ e

section lift
variable (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (S : Register → Bool)
  (T : CySt → (r : Register) → RegisterType r → Prop)

/-- **THE `pfB` LIFT, with B1's dataflow** (header). -/
theorem cyOfPfDf {X : Type} (hS : ∀ r, S r = true → pfProt r = true) (P : X → Prop)
    (Pd : X → DfSt → Prop) (Q : X → CySt → Prop) :
    ∀ (m : SailM X) (st : CySt), pfB false P m → dfB Pd m st.d → RbootAll st.rv →
      (∀ x st', P x → cyFrame st st' → Pd x st'.d → Q x st') → cyB A Aa S T Q m st := by
  intro m
  induction m with
  | pure x => intro st hp hd hrb hq; exact hq x st hp (cyFrameRefl st hrb) hd
  | impure call k ih =>
    intro st hp hd hrb hq
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead r =>
        intro v hv
        have hb := PinCycRun.rdRboot st r v hrb hv
        exact ih v (cyRd st r) (hp v hb) (hd v hb) hrb (fun x st' h1 h2 h3 =>
          hq x st' h1 (cyFrameTrans _ _ _ (PinCycRun.frameRd st r hrb) h2) h3)
      case regWrite r v =>
        obtain ⟨⟨hb, hok⟩, hk⟩ := hp
        have hpf : pfProt r = false := by simpa [pfRegOk] using hok
        refine ⟨fun hs => absurd (hS r hs) (by rw [hpf]; decide), fun _ => ⟨hb, fun u => ?_⟩⟩
        have hrb' : RbootAll (cyWr st r v).rv := rbootAllSet _ r v hrb hb
        exact ih u (cyWr st r v) (hk u) (hd.2 u) hrb' (fun x st' h1 h2 h3 =>
          hq x st' h1 (cyFrameTrans _ _ _ (PinCycRun.frameWr st r v hrb hpf hb) h2) h3)
      case memRead n va req =>
        obtain ⟨hif, hk⟩ := hp
        refine ⟨fun _ h2 => ?_, fun _ w => ih _ st (hk _) (hd _) hrb hq⟩
        exact absurd h2 (by simp only [PinCycRunFp.ifOk] at hif; simp [classify, hif])
      case instrAnnounce => exact hp.elim
      case barrier b => exact fun v => ih v st hp.2 (hd v) hrb hq
      case getCycleCount => exact ih _ st (hp _) (hd _) hrb hq
      all_goals exact fun v => ih v st (hp v) (hd v) hrb hq

/-- B1's dataflow predicate with the trivial post holds of every `Rboot`-writing tree. -/
theorem PinCycRun.dfTrue {X : Type} (P : X → Prop) :
    ∀ (m : SailM X) (d : DfSt), pfB false P m → dfB (fun _ _ => True) m d := by
  intro m
  induction m with
  | pure x => intro _ _; trivial
  | impure call k ih =>
    intro d hp
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead r => exact fun v hv => ih v _ (hp v hv)
      case regWrite r v => exact ⟨hp.1.1, fun u => ih u _ (hp.2 u)⟩
      case memRead => exact fun v => ih v _ (hp.2 v)
      case instrAnnounce => exact hp.elim
      case barrier => exact fun v => ih v _ hp.2
      all_goals exact fun v => ih v _ (hp v)

/-- **THE `pfB` LIFT** (header): the post sees the footprint's post and the frame. -/
theorem cyOfPf {X : Type} (hS : ∀ r, S r = true → pfProt r = true) (P : X → Prop)
    (Q : X → CySt → Prop) (m : SailM X) (st : CySt) (hp : pfB false P m) (hrb : RbootAll st.rv)
    (hq : ∀ x st', P x → cyFrame st st' → Q x st') : cyB A Aa S T Q m st :=
  cyOfPfDf A Aa S T hS P (fun _ _ => True) Q m st hp (PinCycRun.dfTrue P m st.d hp) hrb
    (fun x st' h1 h2 _ => hq x st' h1 h2)

/-- **THE `fp` LIFT** (header): a W-SCO strict footprint whose stop nodes owe a stop post that
holds at every state with the starting log and announce flag. -/
theorem cyOfFp {X : Type} (P : X → Prop) (Q : X → CySt → Prop) :
    ∀ (m : SailM X) (st : CySt), SailCycleOrderFp.fp P m → RbootAll st.rv →
      (∀ x st', P x → st'.fe = st.fe → st'.an = st.an → RbootAll st'.rv → Q x st') →
      (∀ st' r v, st'.fe = st.fe → st'.an = st.an → S r = true → T st' r v) →
      cyB A Aa S T Q m st := by
  intro m
  induction m with
  | pure x => intro st hp hrb hq _; exact hq x st hp rfl rfl hrb
  | impure call k ih =>
    intro st hp hrb hq hT
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead r =>
        intro v hv
        exact ih v (cyRd st r) (hp v (PinCycRun.rdRboot st r v hrb hv)) hrb hq hT
      case regWrite r v =>
        obtain ⟨hb, hk⟩ := hp
        refine ⟨fun hs => hT st r v rfl rfl hs, fun _ => ⟨hb, fun u => ?_⟩⟩
        exact ih u (cyWr st r v) (hk u) (rbootAllSet _ r v hrb hb) hq hT
      case memRead n va req =>
        obtain ⟨hif, hk⟩ := hp
        refine ⟨fun _ h2 => ?_, fun _ w => ih _ st (hk _) hrb hq hT⟩
        exact absurd h2 (by simp only [SailCycleOrderFp.ifOk] at hif; simp [classify, hif])
      case instrAnnounce => exact hp.elim
      case barrier b => exact fun v => ih v st hp.2 hrb hq hT
      case getCycleCount => exact ih _ st (hp _) hrb hq hT
      all_goals exact fun v => ih v st (hp v) hrb hq hT

end lift

end PinCycRun
end Weak
