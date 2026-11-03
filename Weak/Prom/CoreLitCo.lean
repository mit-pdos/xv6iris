/-
Weak/Prom: **row 22, the coherence tests, proved IN THE LOGIC** (stage S2; plan rev 7 §5 row 22 "CoWW, CoWR, CoRW,
CoRR, CoRR2 … coherence-violating … FORBIDDEN (rules 1, 2 and load value axiom)", §8 S2).

Programs (RefTests.lean, x = 0x1000): `Lit.coWW`, `Lit.coWR0`, `Lit.coWR`, `Lit.coRW1`, `Lit.coRW2`, `Lit.coRR`,
`Lit.coRR2`.  Each `lit_` theorem states the coherence-violating outcome of the row as forbidden over every valid
run (for CoWW and CoRW2, every valid run in which the storing harts finished, A0 (i)); for CoWW it states the
repository's full verdict (`x = 2` finally).  The relation to the repository's `exists (not …)` conditions:
* CoWW `exists (not x=2)`: `lit_coWW` — when H0 finished, `x = 2` (the 4-byte final value);
* CoWR0 `exists (not (x7=1 ∧ x=1))`: `lit_coWR0` — the load never returns the image's 0 (the only other value
  of x is 1, H0's store, so x7 = 1; x = 1 is then the only write);
* CoWR (HAND) `~exists (x=1 ∧ x7=2)`: `lit_coWR`, exactly;
* CoRW1 `exists (not (x5=0 ∧ x=1))`: `lit_coRW1` — the load never returns its own po-later store's 1;
* CoRW2: `lit_coRW2` — when H1 finished, not (x5 = 1 ∧ x = 1) (H1 read H0's store, yet its own store is
  co-before it);
* CoRR: `lit_coRR` — not (x5 = 1 ∧ x7 = 0);
* CoRR2 (SLR §2.3): `lit_coRR2` — the two readers cannot see the two stores in opposite orders.
The harts are CoreLitH.lean's coherence harts (`hWWc`, `hWRc`, `hRWc`, `hRRc`, `hW`, `hLW`): the order facts come
from COH (`cohBelow`) and from the coherence floor in `loadOk`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreLitF

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal FenceSet)
open Weak.Prom.Ref.Lit (X Y Z)
open PLabel

/-! ## CoWW -/

def QsCoWW : Nat → Trace → Prop
  | 0 => qWW (X : Int) (X : Int) (toBytes 1 4) (toBytes 2 4) [.DReg 6] [.DReg 5] [.DReg 6] [.DReg 7]
  | _ => q0

/-- **ROW 22, CoWW: FORBIDDEN, in the logic** (rule 1): in every valid run in which H0 finished, `x = 2` finally. -/
theorem lit_coWW : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.coWW) () (progs Weak.Prom.Ref.Lit.coWW) M run →
    run.done litDone 0 () → finalMem (testImg Weak.Prom.Ref.Lit.coWW) M X 4 = 2 := by
  intro M run hrun hd0
  obtain ⟨hi, hQ, _, hpart, hwf, _, _⟩ := kitAdeq (π := Proto.triv) QsCoWW
    (fun h _ => match h with | 0 => wwDone M 0 (X : Int) (X : Int) (toBytes 1 4) (toBytes 2 4) | _ => True) trivial
    (fun h => match h with | 0 => trivial | _ + 1 => rfl)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, _, hrd⟩ := progs_get hp
      match h with
      | 0 =>
        exact hWWc_hart _ M 0 p 4 X 1 2 6 5 7 (by rw [hpr]; rfl) hpc hq (by decide) (by decide)
          (by rw [hrd 5 (by decide) (by decide)]; rfl) (by rw [hrd 7 (by decide) (by decide)]; rfl)
          (by rw [hrd 6 (by decide) (by decide)]; rfl) (by decide) (by decide)
      | n + 1 =>
        have hl : (progs Weak.Prom.Ref.Lit.coWW).length = 1 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  obtain ⟨t0, t1, h0, h01, hm0, hm1⟩ := hi 0 () hd0
  have hout : ∀ h, 1 ≤ h → memEv (run.trace h) = [] := fun h hh => by
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩; exact hQ (k + 1)
  -- the second store's entry is at `t1`
  have hin1 : (LStore false false (X : Int) (toBytes 2 4) [.DReg 6] [.DReg 7], some t1) ∈ memEv (run.trace 0) := by
    obtain ⟨h, hh, e, he, het, hlw⟩ := writer_cases hpart hwf 1 hout hm1
    match h, hh with
    | 0, _ =>
      rcases qWW_writer (hQ 0) he het with rfl | ⟨rfl, _⟩
      · simp only [labelWrite, Option.some.injEq, Prod.mk.injEq] at hlw
        exact absurd hlw.2 (by decide)
      · rw [show t1 - 1 + 1 = t1 by omega] at he; exact he
  rw [finalMem_of_bytes (d := toBytes 2 4) (by decide) (fun k hk => ?_)]
  · decide
  · have hb : ∀ m : PMsg, m.pa = (X : Int) → m.data = toBytes 2 4 →
        m.byteAt ((X : Int) + (k : Int)) = (toBytes 2 4)[k]? := by
      intro m hpa hd
      rw [byteAt_pd hpa hd]
      have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> decide
    have hs : ((toBytes 2 4)[k]?).isSome = true := by
      rw [List.getElem?_eq_getElem (by rw [toBytes_length]; exact hk)]; rfl
    rw [lastByte_eq_of hm1 (by rw [hb _ rfl rfl]; exact hs) ?_]
    · rw [hb _ rfl rfl]
    · intro k' m' hk' hm'
      cases hc : (m'.byteAt ((X : Int) + (k : Int))).isSome with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨h, hh, e, he, het, _⟩ := writer_cases hpart hwf 1 hout hm'
        match h, hh with
        | 0, _ =>
          have := qWW_ts_le (hQ 0) (by decide) hin1 he het
          omega

/-! ## CoWR0 -/

def QsCoWR0 (M : List PMsg) : Nat → Trace → Prop
  | 0 => qWR M (X : Int) (X : Int) 4 (toBytes 1 4) [.DReg 6] [.DReg 5] [.DReg 6]
  | _ => q0

/-- **ROW 22, CoWR0: FORBIDDEN, in the logic** (rule 2 / load value axiom): a load never returns a value
co-before the hart's own po-earlier store (here, the image's 0). -/
theorem lit_coWR0 : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.coWR0) () (progs Weak.Prom.Ref.Lit.coWR0) M run →
    ¬ run.obsLoad 0 0 = some 0 := by
  intro M run hrun ho
  obtain ⟨_, hQ, hnc, hpart, hwf, himg, _⟩ := kitAdeq (π := Proto.triv) (QsCoWR0 M) (fun _ _ => True) trivial
    (fun h => match h with | 0 => trivial | _ + 1 => rfl)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, _, hrd⟩ := progs_get hp
      match h with
      | 0 =>
        exact hWRc_hart _ M 0 p 4 X 1 6 7 5 true (by rw [hpr]; rfl) hpc hq (by decide) (by decide)
          (by rw [hrd 6 (by decide) (by decide)]; rfl) (by rw [hrd 5 (by decide) (by decide)]; rfl)
          (by decide) (by decide)
      | n + 1 =>
        have hl : (progs Weak.Prom.Ref.Lit.coWR0).length = 1 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  have hout : ∀ h, 1 ≤ h → memEv (run.trace h) = [] := fun h hh => by
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩; exact hQ (k + 1)
  obtain ⟨s1, b1, t0, hr1, hv1, ht0, hin0, hord⟩ := qWR_out hwf (by decide) (hQ 0) ho
  rw [himg] at hr1
  have hs1 : s1 = 0 := src_img0 hr1 (bv_of_toNat hv1 (by decide)) (fun k m hm hb => by
    obtain ⟨h, hh, e, he, het, hlw⟩ := writer_cases hpart hwf 1 hout hm
    match h, hh with
    | 0, _ =>
      rw [qWR_writer (hQ 0) he het] at hlw
      obtain ⟨hpa, hd⟩ := lw_st hlw; rw [byteAt_some_of hpa hd (v := 1) (by decide)] at hb; cases hb)
  subst hs1
  exact hord hnc (st_writes hwf hin0 ht0 (by decide) ht0 (Nat.le_refl _))

/-! ## CoWR (HAND, doublewords) -/

def QsCoWR (M : List PMsg) : Nat → Trace → Prop
  | 0 => qWR M (X : Int) (X : Int) 8 (toBytes 1 8) [.DReg 6] [.DReg 5] [.DReg 6]
  | 1 => qS (X : Int) (toBytes 2 8) [.DReg 6] [.DReg 5]
  | _ => q0

/-- **ROW 22, CoWR (repo `HAND/CoWR`): FORBIDDEN, in the logic** (rules 1, 2): not (x = 1 finally and H0's load
returns H1's 2): H0's load reads above its own store, so H1's store is co-after H0's. -/
theorem lit_coWR : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.coWR) () (progs Weak.Prom.Ref.Lit.coWR) M run →
    ¬ (finalMem (testImg Weak.Prom.Ref.Lit.coWR) M X 8 = 1 ∧ run.obsLoad 0 0 = some 2) := by
  intro M run hrun
  obtain ⟨_, hQ, hnc, hpart, hwf, himg, _⟩ := kitAdeq (π := Proto.triv) (QsCoWR M) (fun _ _ => True) trivial
    (fun h => match h with | 0 => trivial | 1 => trivial | _ + 2 => rfl)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, _, hrd⟩ := progs_get hp
      match h with
      | 0 =>
        exact hWRc_hart _ M 0 p 8 X 1 6 7 5 true (by rw [hpr]; rfl) hpc hq (by decide) (by decide)
          (by rw [hrd 6 (by decide) (by decide)]; rfl) (by rw [hrd 5 (by decide) (by decide)]; rfl)
          (by decide) (by decide)
      | 1 =>
        exact hW_hart _ M 1 p 8 X 2 6 5 (by rw [hpr]; rfl) hpc hq (by decide)
          (by rw [hrd 6 (by decide) (by decide)]; rfl) (by rw [hrd 5 (by decide) (by decide)]; rfl)
          (by decide) (by decide)
      | n + 2 =>
        have hl : (progs Weak.Prom.Ref.Lit.coWR).length = 2 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  rintro ⟨hf, ho⟩
  have hout : ∀ h, 2 ≤ h → memEv (run.trace h) = [] := fun h hh => by
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 2 := ⟨h - 2, by omega⟩; exact hQ (k + 2)
  obtain ⟨s1, b1, t0, hr1, hv1, ht0, hin0, hord⟩ := qWR_out hwf (by decide) (hQ 0) ho
  rw [himg] at hr1
  obtain ⟨m0, hm0, hpa0, hd0⟩ := st_msg hwf hin0
  -- `s1` is H1's store
  obtain ⟨k1, m1, rfl, hm1, hb1⟩ := src_of_val hr1 rfl (by rw [bv_of_toNat hv1 (by decide)]; decide)
  have hcov1 : (m1.byteAt (X : Int)).isSome = true := by rw [hb1]; rfl
  have hk1v : ((m1.byteAt (X : Int)).map BitVec.toNat).getD 0 = 2 := by
    rw [hb1, bv_of_toNat hv1 (by decide)]; rfl
  -- `t0 < k1 + 1`: no write to x in `(s1, t0]`
  have hlt : t0 < k1 + 1 := by
    rcases Nat.lt_or_ge (k1 + 1) t0 with h | h
    · exact absurd (st_writes hwf hin0 ht0 (by decide) h (Nat.le_refl _)) (hord hnc)
    · rcases Nat.lt_or_ge t0 (k1 + 1) with h' | h'
      · exact h'
      · have : t0 = k1 + 1 := by omega
        subst this
        simp only [Nat.add_sub_cancel] at hm0
        rw [hm0] at hm1; cases hm1
        rw [byteAt_some_of hpa0 hd0 (v := 1) (by decide)] at hb1
        rw [bv_of_toNat hv1 (by decide)] at hb1; cases hb1
  -- the final value 1 makes H0's store the last write to x
  have hl := finalMem_b0 hf (by decide)
  have := last_order hl (by decide) hm1 hcov1 (by rw [hk1v]; decide) (j := t0 - 1) (fun k m hm hc hv => by
    obtain ⟨h, hh, e, he, het, hlw⟩ := writer_cases hpart hwf 2 hout hm
    match h, hh with
    | 0, _ =>
      have := qWR_st_uniq (hQ 0) he het hin0 rfl
      omega
    | 1, _ =>
      rw [qS_writer (hQ 1) he het] at hlw
      obtain ⟨hpa, hd⟩ := lw_st hlw
      rw [byteAt_some_of hpa hd (v := 2) (by decide)] at hv; cases hv)
  omega

/-! ## CoRW1 -/

def QsCoRW1 : Nat → Trace → Prop
  | 0 => qLW (X : Int) (X : Int) 4 (toBytes 1 4) [.DReg 6] [.DReg 6] [.DReg 7]
  | _ => q0

/-- **ROW 22, CoRW1: FORBIDDEN, in the logic** (rule 1 / COH): a load never returns its own po-later store. -/
theorem lit_coRW1 : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.coRW1) () (progs Weak.Prom.Ref.Lit.coRW1) M run →
    ¬ run.obsLoad 0 0 = some 1 := by
  intro M run hrun ho
  obtain ⟨_, hQ, _, hpart, hwf, himg, _⟩ := kitAdeq (π := Proto.triv) QsCoRW1
    (fun h _ => match h with | 0 => wDone M 0 (X : Int) (toBytes 1 4) | _ => True) trivial
    (fun h => match h with | 0 => trivial | _ + 1 => rfl)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, _, hrd⟩ := progs_get hp
      match h with
      | 0 =>
        exact hRWc_hart _ M 0 p 4 X 1 6 5 7 true (by rw [hpr]; rfl) hpc hq (by decide) (by decide) (by decide)
          (by rw [hrd 6 (by decide) (by decide)]; rfl) (by rw [hrd 7 (by decide) (by decide)]; rfl)
          (by decide) (by decide)
      | n + 1 =>
        have hl : (progs Weak.Prom.Ref.Lit.coRW1).length = 1 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  have hout : ∀ h, 1 ≤ h → memEv (run.trace h) = [] := fun h hh => by
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩; exact hQ (k + 1)
  obtain ⟨s0, b0, hr0, hv0, hlt⟩ := qLW_out hwf (by decide) (hQ 0) ho
  rw [himg] at hr0
  obtain ⟨k, m, rfl, hm, _⟩ := src_of_val hr0 rfl (by rw [bv_of_toNat hv0 (by decide)]; decide)
  obtain ⟨h, hh, e, he, het, _⟩ := writer_cases hpart hwf 1 hout hm
  match h, hh with
  | 0, _ =>
    obtain ⟨rfl, _⟩ := qLW_writer (hQ 0) he het
    have := hlt _ he
    omega

/-! ## CoRW2 -/

def QsCoRW2 : Nat → Trace → Prop
  | 0 => qS (X : Int) (toBytes 1 4) [.DReg 6] [.DReg 5]
  | 1 => qLW (X : Int) (X : Int) 4 (toBytes 2 4) [.DReg 6] [.DReg 6] [.DReg 7]
  | _ => q0

/-- **ROW 22, CoRW2: FORBIDDEN, in the logic** (rules 1, 2): when H1 finished, not (H1 read H0's 1 and `x = 1`
finally): H1's store is above the source it read, so H0's store cannot be co-last. -/
theorem lit_coRW2 : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.coRW2) () (progs Weak.Prom.Ref.Lit.coRW2) M run →
    run.done litDone 1 () →
    ¬ (run.obsLoad 1 0 = some 1 ∧ finalMem (testImg Weak.Prom.Ref.Lit.coRW2) M X 4 = 1) := by
  intro M run hrun hd1
  obtain ⟨hi, hQ, _, hpart, hwf, himg, _⟩ := kitAdeq (π := Proto.triv) QsCoRW2
    (fun h _ => match h with | 1 => wDone M 1 (X : Int) (toBytes 2 4) | _ => True) trivial
    (fun h => match h with | 0 => trivial | 1 => trivial | _ + 2 => rfl)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, _, hrd⟩ := progs_get hp
      match h with
      | 0 =>
        exact hW_hart _ M 0 p 4 X 1 6 5 (by rw [hpr]; rfl) hpc hq (by decide)
          (by rw [hrd 6 (by decide) (by decide)]; rfl) (by rw [hrd 5 (by decide) (by decide)]; rfl)
          (by decide) (by decide)
      | 1 =>
        exact hRWc_hart _ M 1 p 4 X 2 6 5 7 true (by rw [hpr]; rfl) hpc hq (by decide) (by decide) (by decide)
          (by rw [hrd 6 (by decide) (by decide)]; rfl) (by rw [hrd 7 (by decide) (by decide)]; rfl)
          (by decide) (by decide)
      | n + 2 =>
        have hl : (progs Weak.Prom.Ref.Lit.coRW2).length = 2 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  rintro ⟨ho, hf⟩
  have hout : ∀ h, 2 ≤ h → memEv (run.trace h) = [] := fun h hh => by
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 2 := ⟨h - 2, by omega⟩; exact hQ (k + 2)
  obtain ⟨t1, ht1, hm1⟩ := hi 1 () hd1
  obtain ⟨s0, b0, hr0, hv0, hlt⟩ := qLW_out hwf (by decide) (hQ 1) ho
  rw [himg] at hr0
  -- H1's store entry is at `t1`, above `s0`
  have hin1 : (LStore false false (X : Int) (toBytes 2 4) [.DReg 6] [.DReg 7], some t1) ∈ memEv (run.trace 1) := by
    obtain ⟨h, hh, e, he, het, hlw⟩ := writer_cases hpart hwf 2 hout hm1
    match h, hh with
    | 0, _ =>
      rw [qS_writer (hQ 0) he het] at hlw
      simp only [labelWrite, Option.some.injEq, Prod.mk.injEq] at hlw
      exact absurd hlw.2 (by decide)
    | 1, _ =>
      obtain ⟨rfl, _⟩ := qLW_writer (hQ 1) he het
      rw [show t1 - 1 + 1 = t1 by omega] at he; exact he
  have hs01 := hlt t1 hin1
  -- `s0` is H0's store, the only message holding 1 at x
  obtain ⟨k0, m0, rfl, hm0, hb0⟩ := src_of_val hr0 rfl (by rw [bv_of_toNat hv0 (by decide)]; decide)
  have hl := finalMem_b0 hf (by decide)
  have := last_order hl (by decide) hm1 (by rw [byteAt_some_of rfl rfl (v := 2) (by decide)]; rfl)
    (by rw [byteAt_some_of rfl rfl (v := 2) (by decide)]; decide) (j := k0) (fun k m hm hc hv => by
    obtain ⟨h, hh, e, he, het, hlw⟩ := writer_cases hpart hwf 2 hout hm
    match h, hh with
    | 0, _ =>
      obtain ⟨h0', hh0', e0, he0, het0, _⟩ := writer_cases hpart hwf 2 hout hm0
      match h0', hh0' with
      | 0, _ =>
        have := qS_uniq (hQ 0) he het he0 het0
        omega
      | 1, _ =>
        obtain ⟨rfl, _⟩ := qLW_writer (hQ 1) he0 het0
        have := hlt _ he0
        omega
    | 1, _ =>
      obtain ⟨rfl, _⟩ := qLW_writer (hQ 1) he het
      obtain ⟨hpa, hd⟩ := lw_st hlw
      rw [byteAt_some_of hpa hd (v := 2) (by decide)] at hv; cases hv)
  omega

/-! ## CoRR -/

def QsCoRR (M : List PMsg) : Nat → Trace → Prop
  | 0 => qS (X : Int) (toBytes 1 4) [.DReg 6] [.DReg 5]
  | 1 => qRR M (X : Int) (X : Int) 4 [.DReg 6] [.DReg 6]
  | _ => q0

/-- **ROW 22, CoRR: FORBIDDEN, in the logic** (rule 2 / load value axiom): two po-ordered loads of x cannot see
H0's 1 and then the image's 0. -/
theorem lit_coRR : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.coRR) () (progs Weak.Prom.Ref.Lit.coRR) M run →
    ¬ (run.obsLoad 1 0 = some 1 ∧ run.obsLoad 1 1 = some 0) := by
  intro M run hrun
  obtain ⟨_, hQ, hnc, hpart, hwf, himg, _⟩ := kitAdeq (π := Proto.triv) (QsCoRR M) (fun _ _ => True) trivial
    (fun h => match h with | 0 => trivial | 1 => trivial | _ + 2 => rfl)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, _, hrd⟩ := progs_get hp
      match h with
      | 0 =>
        exact hW_hart _ M 0 p 4 X 1 6 5 (by rw [hpr]; rfl) hpc hq (by decide)
          (by rw [hrd 6 (by decide) (by decide)]; rfl) (by rw [hrd 5 (by decide) (by decide)]; rfl)
          (by decide) (by decide)
      | 1 =>
        exact hRRc_hart _ M 1 p 4 X 6 5 7 true (by rw [hpr]; rfl) hpc hq (by decide) (by decide) (by decide)
          (by rw [hrd 6 (by decide) (by decide)]; rfl) (by decide) (by decide)
      | n + 2 =>
        have hl : (progs Weak.Prom.Ref.Lit.coRR).length = 2 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  rintro ⟨ho0, ho1⟩
  have hout : ∀ h, 2 ≤ h → memEv (run.trace h) = [] := fun h hh => by
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 2 := ⟨h - 2, by omega⟩; exact hQ (k + 2)
  obtain ⟨s0, s1, b0, b1, hr0, hv0, hr1, hv1, hord⟩ := qRR_out hwf (by decide) (hQ 1) ho0 ho1
  rw [himg] at hr0 hr1
  have hs1 : s1 = 0 := src_img0 hr1 (bv_of_toNat hv1 (by decide)) (fun k m hm hb => by
    obtain ⟨h, hh, e, he, het, hlw⟩ := writer_cases hpart hwf 2 hout hm
    match h, hh with
    | 0, _ =>
      rw [qS_writer (hQ 0) he het] at hlw
      obtain ⟨hpa, hd⟩ := lw_st hlw; rw [byteAt_some_of hpa hd (v := 1) (by decide)] at hb; cases hb
    | 1, _ => rw [qRR_nots (hQ 1) he] at het; cases het)
  subst hs1
  obtain ⟨k0, m0, rfl, hm0, hb0⟩ := src_of_val hr0 rfl (by rw [bv_of_toNat hv0 (by decide)]; decide)
  exact hord hnc (writesIn_of hm0 (by rw [hb0]; rfl) (by omega) (Nat.le_refl _))

/-! ## CoRR2 (SLR §2.3, four harts) -/

def QsCoRR2 (M : List PMsg) : Nat → Trace → Prop
  | 0 => qS (X : Int) (toBytes 1 4) [.DReg 6] [.DReg 5]
  | 1 => qS (X : Int) (toBytes 2 4) [.DReg 6] [.DReg 5]
  | 2 => qRR M (X : Int) (X : Int) 4 [.DReg 6] [.DReg 6]
  | 3 => qRR M (X : Int) (X : Int) 4 [.DReg 6] [.DReg 6]
  | _ => q0

/-- **ROW 22, CoRR2: FORBIDDEN, in the logic** (coherence, SLR §2.3): with `x := 1 ‖ x := 2`, one reader cannot see
1 then 2 while the other sees 2 then 1. -/
theorem lit_coRR2 : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.coRR2) () (progs Weak.Prom.Ref.Lit.coRR2) M run →
    ¬ (run.obsLoad 2 0 = some 1 ∧ run.obsLoad 2 1 = some 2 ∧ run.obsLoad 3 0 = some 2 ∧ run.obsLoad 3 1 = some 1) := by
  intro M run hrun
  obtain ⟨_, hQ, hnc, hpart, hwf, himg, _⟩ := kitAdeq (π := Proto.triv) (QsCoRR2 M) (fun _ _ => True) trivial
    (fun h => match h with | 0 => trivial | 1 => trivial | 2 => trivial | 3 => trivial | _ + 4 => rfl)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, hlen, hrd⟩ := progs_get hp
      match h with
      | 0 =>
        exact hLW_hart _ M 0 p 4 X 1 6 5 (by rw [hpr]; rfl) hpc hq (by decide) (by rw [hlen]; decide) (by decide)
          (by rw [hrd 6 (by decide) (by decide)]; rfl) (by decide) (by decide)
      | 1 =>
        exact hLW_hart _ M 1 p 4 X 2 6 5 (by rw [hpr]; rfl) hpc hq (by decide) (by rw [hlen]; decide) (by decide)
          (by rw [hrd 6 (by decide) (by decide)]; rfl) (by decide) (by decide)
      | 2 =>
        exact hRRc_hart _ M 2 p 4 X 6 10 11 true (by rw [hpr]; rfl) hpc hq (by decide) (by decide) (by decide)
          (by rw [hrd 6 (by decide) (by decide)]; rfl) (by decide) (by decide)
      | 3 =>
        exact hRRc_hart _ M 3 p 4 X 6 10 11 true (by rw [hpr]; rfl) hpc hq (by decide) (by decide) (by decide)
          (by rw [hrd 6 (by decide) (by decide)]; rfl) (by decide) (by decide)
      | n + 4 =>
        have hl : (progs Weak.Prom.Ref.Lit.coRR2).length = 4 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  rintro ⟨ha, hb, hc, hd⟩
  have hout : ∀ h, 4 ≤ h → memEv (run.trace h) = [] := fun h hh => by
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 4 := ⟨h - 4, by omega⟩; exact hQ (k + 4)
  obtain ⟨sa, sb, ba, bb, hra, hva, hrb, hvb, hord2⟩ := qRR_out hwf (by decide) (hQ 2) ha hb
  obtain ⟨sc, sd, bc, bd, hrc, hvc, hrd', hvd, hord3⟩ := qRR_out hwf (by decide) (hQ 3) hc hd
  rw [himg] at hra hrb hrc hrd'
  -- a message holding `v ∈ {1, 2}` at x is the store of hart `v - 1`; one timestamp per hart
  have hsrc : ∀ (s : Nat) (b : BitVec 8) (v : Nat), memByte (testImg Weak.Prom.Ref.Lit.coRR2) M s (X : Int) = some b →
      b.toNat = v % 256 → (v = 1 ∨ v = 2) →
      ∃ e ∈ memEv (run.trace (v - 1)), e.2 = some s ∧ 0 < s ∧ M[s - 1]? ≠ none := by
    intro s b v hr hv hv12
    obtain ⟨k, m, rfl, hm, hbm⟩ := src_of_val hr rfl (by
      rw [bv_of_toNat hv (by rcases hv12 with rfl | rfl <;> decide)]; rcases hv12 with rfl | rfl <;> decide)
    obtain ⟨h, hh, e, he, het, hlw⟩ := writer_cases hpart hwf 4 hout hm
    match h, hh with
    | 0, _ =>
      rw [qS_writer (hQ 0) he het] at hlw
      obtain ⟨hpa, hd⟩ := lw_st hlw
      rw [byteAt_some_of hpa hd (v := 1) (by decide)] at hbm
      cases hbm
      have : v = 1 := by
        rcases hv12 with rfl | rfl
        · rfl
        · simp at hv
      subst this
      exact ⟨e, he, het, by omega, by simp [hm]⟩
    | 1, _ =>
      rw [qS_writer (hQ 1) he het] at hlw
      obtain ⟨hpa, hd⟩ := lw_st hlw
      rw [byteAt_some_of hpa hd (v := 2) (by decide)] at hbm
      cases hbm
      have : v = 2 := by
        rcases hv12 with rfl | rfl
        · simp at hv
        · rfl
      subst this
      exact ⟨e, he, het, by omega, by simp [hm]⟩
    | 2, _ => rw [qRR_nots (hQ 2) he] at het; cases het
    | 3, _ => rw [qRR_nots (hQ 3) he] at het; cases het
  obtain ⟨ea, hea, heta, hsa, _⟩ := hsrc sa ba 1 hra hva (.inl rfl)
  obtain ⟨eb, heb, hetb, hsb, _⟩ := hsrc sb bb 2 hrb hvb (.inr rfl)
  obtain ⟨ec, hec, hetc, hsc, _⟩ := hsrc sc bc 2 hrc hvc (.inr rfl)
  obtain ⟨ed, hed, hetd, hsd, _⟩ := hsrc sd bd 1 hrd' hvd (.inl rfl)
  have had := qS_uniq (hQ 0) hea heta hed hetd
  have hbc := qS_uniq (hQ 1) heb hetb hec hetc
  subst had hbc
  -- the writes are at `sa` (x := 1) and `sb` (x := 2); each reader orders them oppositely
  have hwa : writesIn M (X : Int) sb sa → False := hord2 hnc
  have hwb : writesIn M (X : Int) sa sb → False := hord3 hnc
  have hma : ∃ m, M[sa - 1]? = some m ∧ (m.byteAt (X : Int)).isSome = true := by
    obtain ⟨k, m, hk, hm, hbm⟩ := src_of_val hra rfl (by rw [bv_of_toNat hva (by decide)]; decide)
    exact ⟨m, by rw [hk]; simpa using hm, by rw [hbm]; rfl⟩
  have hmb : ∃ m, M[sb - 1]? = some m ∧ (m.byteAt (X : Int)).isSome = true := by
    obtain ⟨k, m, hk, hm, hbm⟩ := src_of_val hrb rfl (by rw [bv_of_toNat hvb (by decide)]; decide)
    exact ⟨m, by rw [hk]; simpa using hm, by rw [hbm]; rfl⟩
  obtain ⟨ma, hma, hca⟩ := hma
  obtain ⟨mb, hmb, hcb⟩ := hmb
  rcases Nat.lt_trichotomy sa sb with h | h | h
  · exact hwb (writesIn_of (k := sb - 1) hmb hcb (by omega) (by omega))
  · subst h
    obtain ⟨k, m, hk, hm, hbm⟩ := src_of_val hra rfl (by rw [bv_of_toNat hva (by decide)]; decide)
    obtain ⟨k', m', hk', hm', hbm'⟩ := src_of_val hrb rfl (by rw [bv_of_toNat hvb (by decide)]; decide)
    rw [hk] at hk'; cases hk'; rw [hm] at hm'; cases hm'; rw [hbm] at hbm'; cases hbm'
    rw [bv_of_toNat hva (by decide)] at hvb; simp at hvb
  · exact hwa (writesIn_of (k := sa - 1) hma hca (by omega) (by omega))

end Weak.Prom.PF

#print axioms Weak.Prom.PF.lit_coWW
#print axioms Weak.Prom.PF.lit_coWR0
#print axioms Weak.Prom.PF.lit_coWR
#print axioms Weak.Prom.PF.lit_coRW1
#print axioms Weak.Prom.PF.lit_coRW2
#print axioms Weak.Prom.PF.lit_coRR
#print axioms Weak.Prom.PF.lit_coRR2
