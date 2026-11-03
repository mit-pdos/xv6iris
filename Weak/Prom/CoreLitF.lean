/-
Weak/Prom: **rows 13, 21′, 24, 25 (fences and multi-copy atomicity), proved IN THE LOGIC** (stage S2; plan rev 7 §5
rows 13, 21, 24, 25, §8 S2).

Programs (RefTests.lean): `Lit.sbFF` (row 13, repo `SB+fence.rw.rws`), `Lit.isa2F` (row 24, repo
`SAFE/ISA2+fence.rw.rws`), `Lit.wrcF` (row 24, repo `SAFE/WRC+fence.rw.rws`), `Lit.iriwF` (row 25, repo
`SAFE/IRIW+fence.r.rws`), `Lit.w22F` (row 21′, repo `SAFE/2+2W+fence.w.ws`).  Every hart is one of the generic
harts of CoreLitH.lean (its Ψ and its order fact from one fence / EXT / coherence view fact); the contradictions use
A0's exports (ii), (iii), (v) only, and (i) for row 21′ (both harts finished: their stores are in `M`).
* SB+F: `st x @t0; fence; ld y` reads 0 ⇒ no write to y in `(0, t0]` ⇒ `t1 > t0` (H1's `st y`); symmetrically
  `t0 > t1`.
* ISA2+F, WRC+F: a timestamp chain `tx < ty ≤ s_y < tz = s_z` (or `tx = s_x < ty = s_y`) through the harts'
  fences; the last load's pre-view is above `tx`, so it cannot read the image at x.  Multi-copy atomicity is the
  single global timestamp order of machine v2.
* IRIW+F: each reader's fence puts the other store above its first read: `ty > tx` and `tx > ty`.
* 2+2W+F: the fences give `t0x < t0y`, `t1y < t1x`; the final values make `t0x` the last write to x and `t1y` the
  last to y (`lastByte`), so `t1x < t0x` and `t0y < t1y`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreLitH

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal FenceSet)
open Weak.Prom.Ref.Lit (X Y Z)
open PLabel

/-- `b.toNat = n % 256` for a literal `n < 256` gives the byte. -/
theorem bv_of_toNat {b : BitVec 8} {n : Nat} (h : b.toNat = n % 256) (hn : n < 256) : b = BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq; rw [h, Nat.mod_eq_of_lt hn]; simp [Nat.mod_eq_of_lt hn]

/-- A load byte read as 0 at `a` comes from the image, when no message holds 0 there. -/
theorem src_img0 {img : Image} {M : List PMsg} {s : Nat} {a : Int} {b : BitVec 8} (hr : memByte img M s a = some b)
    (hb : b = 0) (hno : ∀ (k : Nat) (m : PMsg), M[k]? = some m → m.byteAt a ≠ some 0) : s = 0 := by
  cases s with
  | zero => rfl
  | succ k =>
    obtain ⟨m, hm, hmb⟩ := memByte_succ hr
    exact absurd (by rw [hmb, hb]) (hno k m hm)

/-- A store entry's message at `t` writes byte `a` (decided on its base and data): a write in `(lo, hi]`. -/
theorem st_writes {P D : Type} {run : PFRun P D} {M : List PMsg} (hwf : run.traceWf M) {h : Nat} {a0 : Int}
    {d : List (BitVec 8)} {as0 vs0 : List Dsrc} {t lo hi : Nat} {a : Int}
    (he : (LStore false false a0 d as0 vs0, some t) ∈ memEv (run.trace h)) (ht : 0 < t)
    (hb : ((if a0 ≤ a then d[(a - a0).toNat]? else none)).isSome = true) (h1 : lo < t) (h2 : t ≤ hi) :
    writesIn M a lo hi := by
  obtain ⟨m, hm, hpa, hd⟩ := st_msg hwf he
  refine writesIn_of (k := t - 1) hm ?_ (by omega) (by omega)
  rw [byteAt_pd hpa hd]; exact hb

/-! ## Row 13, SB+fence.rw.rws -/

def QsSB (M : List PMsg) : Nat → Trace → Prop
  | 0 => qWR M (X : Int) (Y : Int) 4 (toBytes 1 4) [.DReg 6] [.DReg 5] [.DReg 8]
  | 1 => qWR M (Y : Int) (X : Int) 4 (toBytes 1 4) [.DReg 6] [.DReg 5] [.DReg 8]
  | _ => q0

/-- **ROW 13, SB+fence.rw.rw ×2: FORBIDDEN, in the logic** (plan §5 row 13, rule 4).  Not both loads return 0. -/
theorem lit_sbFF : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.sbFF) () (progs Weak.Prom.Ref.Lit.sbFF) M run →
    ¬ (run.obsLoad 0 0 = some 0 ∧ run.obsLoad 1 0 = some 0) := by
  intro M run hrun
  obtain ⟨_, hQ, hnc, hpart, hwf, himg, _⟩ := kitAdeq (π := Proto.triv) (QsSB M) (fun _ _ => True) trivial
    (fun h => match h with | 0 => trivial | 1 => trivial | _ + 2 => rfl)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, _, hrd⟩ := progs_get hp
      match h with
      | 0 =>
        exact hWR_hart _ M 0 p 4 X Y 1 6 8 7 5 true true true (by rw [hpr]; rfl) hpc hq (by decide) (by decide)
          (by rw [hrd 6 (by decide) (by decide)]; rfl) (by rw [hrd 8 (by decide) (by decide)]; rfl)
          (by rw [hrd 5 (by decide) (by decide)]; rfl) (by decide) (by decide) (by decide) (by decide)
      | 1 =>
        exact hWR_hart _ M 1 p 4 Y X 1 6 8 7 5 true true true (by rw [hpr]; rfl) hpc hq (by decide) (by decide)
          (by rw [hrd 6 (by decide) (by decide)]; rfl) (by rw [hrd 8 (by decide) (by decide)]; rfl)
          (by rw [hrd 5 (by decide) (by decide)]; rfl) (by decide) (by decide) (by decide) (by decide)
      | n + 2 =>
        have hl : (progs Weak.Prom.Ref.Lit.sbFF).length = 2 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  rintro ⟨ho0, ho1⟩
  obtain ⟨s0, b0, t0, hr0, hv0, ht0, hin0, hord0⟩ := qWR_out hwf (by decide) (hQ 0) ho0
  obtain ⟨s1, b1, t1, hr1, hv1, ht1, hin1, hord1⟩ := qWR_out hwf (by decide) (hQ 1) ho1
  rw [himg] at hr0 hr1
  have hout : ∀ h, 2 ≤ h → memEv (run.trace h) = [] := fun h hh => by
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 2 := ⟨h - 2, by omega⟩; exact hQ (k + 2)
  have hno : ∀ (a : Int), (a = X ∨ a = Y) → ∀ (k : Nat) (m : PMsg), M[k]? = some m → m.byteAt a ≠ some 0 := by
    intro a ha k m hm hb
    obtain ⟨h, hh, e, he, het, hlw⟩ := writer_cases hpart hwf 2 hout hm
    match h, hh with
    | 0, _ =>
      rw [qWR_writer (hQ 0) he het] at hlw
      obtain ⟨hpa, hd⟩ := lw_st hlw
      rcases ha with rfl | rfl
      · rw [byteAt_some_of hpa hd (v := 1) (by decide)] at hb; cases hb
      · rw [byteAt_none_of hpa hd (by decide)] at hb; cases hb
    | 1, _ =>
      rw [qWR_writer (hQ 1) he het] at hlw
      obtain ⟨hpa, hd⟩ := lw_st hlw
      rcases ha with rfl | rfl
      · rw [byteAt_none_of hpa hd (by decide)] at hb; cases hb
      · rw [byteAt_some_of hpa hd (v := 1) (by decide)] at hb; cases hb
  have hs0 := src_img0 hr0 (bv_of_toNat hv0 (by decide)) (hno _ (.inr rfl))
  have hs1 := src_img0 hr1 (bv_of_toNat hv1 (by decide)) (hno _ (.inl rfl))
  subst hs0 hs1
  rcases Nat.lt_or_ge t0 t1 with h01 | h01
  · exact hord1 hnc (st_writes hwf hin0 ht0 (by decide) ht0 (by omega))
  · exact hord0 hnc (st_writes hwf hin1 ht1 (by decide) ht1 h01)

/-! ## Row 24, ISA2+fence.rw.rws -/

def QsISA2 (M : List PMsg) : Nat → Trace → Prop
  | 0 => qWW (X : Int) (Y : Int) (toBytes 1 4) (toBytes 1 4) [.DReg 6] [.DReg 5] [.DReg 7] [.DReg 5]
  | 1 => qLW (Y : Int) (Z : Int) 4 (toBytes 1 4) [.DReg 6] [.DReg 8] [.DReg 7]
  | 2 => qRR M (Z : Int) (X : Int) 4 [.DReg 6] [.DReg 8]
  | _ => q0

/-- **ROW 24, ISA2+fence.rw.rws: FORBIDDEN, in the logic** (plan §5 row 24, rule 4, multi-copy atomicity). -/
theorem lit_isa2F : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.isa2F) () (progs Weak.Prom.Ref.Lit.isa2F) M run →
    ¬ (run.obsLoad 1 0 = some 1 ∧ run.obsLoad 2 0 = some 1 ∧ run.obsLoad 2 1 = some 0) := by
  intro M run hrun
  obtain ⟨_, hQ, hnc, hpart, hwf, himg, _⟩ := kitAdeq (π := Proto.triv) (QsISA2 M)
    (fun h _ => match h with | 0 => wwDone M 0 (X : Int) (Y : Int) (toBytes 1 4) (toBytes 1 4) | _ => True) trivial
    (fun h => match h with | 0 => trivial | 1 => trivial | 2 => trivial | _ + 3 => rfl)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, _, hrd⟩ := progs_get hp
      match h with
      | 0 =>
        exact hWW_hart _ M 0 p 4 X Y 1 1 6 7 5 5 true true (by rw [hpr]; rfl) hpc hq (by decide)
          (by rw [hrd 5 (by decide) (by decide)]; rfl) (by rw [hrd 5 (by decide) (by decide)]; rfl)
          (by rw [hrd 6 (by decide) (by decide)]; rfl) (by rw [hrd 7 (by decide) (by decide)]; rfl)
          (by decide) (by decide) (by decide) (by decide)
      | 1 =>
        exact hRW_hart _ M 1 p 4 Y Z 1 6 8 5 7 true true true (by rw [hpr]; rfl) hpc hq (by decide) (by decide)
          (by decide) (by rw [hrd 6 (by decide) (by decide)]; rfl) (by rw [hrd 8 (by decide) (by decide)]; rfl)
          (by rw [hrd 7 (by decide) (by decide)]; rfl) (by decide) (by decide) (by decide) (by decide)
      | 2 =>
        exact hRR_hart _ M 2 p 4 Z X 6 8 5 7 true true true (by rw [hpr]; rfl) hpc hq (by decide) (by decide)
          (by decide) (by rw [hrd 6 (by decide) (by decide)]; rfl) (by rw [hrd 8 (by decide) (by decide)]; rfl)
          (by decide) (by decide) (by decide) (by decide)
      | n + 3 =>
        have hl : (progs Weak.Prom.Ref.Lit.isa2F).length = 3 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  rintro ⟨ho1, ho2, ho3⟩
  have hout : ∀ h, 3 ≤ h → memEv (run.trace h) = [] := fun h hh => by
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 3 := ⟨h - 3, by omega⟩; exact hQ (k + 3)
  obtain ⟨sy, by0, hry, hvy, hsy⟩ := qLW_out hwf (by decide) (hQ 1) ho1
  obtain ⟨sz, sx, bz, bx, hrz, hvz, hrx, hvx, hord⟩ := qRR_out hwf (by decide) (hQ 2) ho2 ho3
  rw [himg] at hry hrz hrx
  -- `sz`: H1's `st z` (the only write of 1 to z), above `sy`
  obtain ⟨kz, mz, rfl, hmz, hbz⟩ := src_of_val hrz rfl (by rw [bv_of_toNat hvz (by decide)]; decide)
  obtain ⟨hz, hhz, ez, hez, hetz, hlwz⟩ := writer_cases hpart hwf 3 hout hmz
  have hyz : sy < kz + 1 := by
    match hz, hhz with
    | 0, _ =>
      rcases qWW_writer (hQ 0) hez hetz with rfl | ⟨rfl, _⟩ <;> obtain ⟨hpa, hd⟩ := lw_st hlwz <;>
        rw [byteAt_none_of hpa hd (by decide)] at hbz <;> cases hbz
    | 1, _ =>
      obtain ⟨rfl, _⟩ := qLW_writer (hQ 1) hez hetz
      exact hsy _ hez
    | 2, _ => rw [qRR_nots (hQ 2) hez] at hetz; cases hetz
  -- `sy`: H0's `st y`, above H0's `st x`
  obtain ⟨ky, my, rfl, hmy, hby⟩ := src_of_val hry rfl (by rw [bv_of_toNat hvy (by decide)]; decide)
  obtain ⟨hy, hhy, ey, hey, hety, hlwy⟩ := writer_cases hpart hwf 3 hout hmy
  obtain ⟨tx, htx, hinx, hxy⟩ : ∃ tx, 0 < tx ∧
      (LStore false false (X : Int) (toBytes 1 4) [.DReg 6] [.DReg 5], some tx) ∈ memEv (run.trace 0) ∧
      tx < ky + 1 := by
    match hy, hhy with
    | 0, _ =>
      rcases qWW_writer (hQ 0) hey hety with rfl | ⟨rfl, t0, ht0, hin, hlt⟩
      · obtain ⟨hpa, hd⟩ := lw_st hlwy; rw [byteAt_none_of hpa hd (by decide)] at hby; cases hby
      · exact ⟨t0, ht0, hin, hlt⟩
    | 1, _ =>
      obtain ⟨rfl, _⟩ := qLW_writer (hQ 1) hey hety
      obtain ⟨hpa, hd⟩ := lw_st hlwy; rw [byteAt_none_of hpa hd (by decide)] at hby; cases hby
    | 2, _ => rw [qRR_nots (hQ 2) hey] at hety; cases hety
  -- `sx = 0`: no message holds 0 at x
  have hsx : sx = 0 := src_img0 hrx (bv_of_toNat hvx (by decide)) (fun k m hm hb => by
    obtain ⟨h, hh, e, he, het, hlw⟩ := writer_cases hpart hwf 3 hout hm
    match h, hh with
    | 0, _ =>
      rcases qWW_writer (hQ 0) he het with rfl | ⟨rfl, _⟩ <;> obtain ⟨hpa, hd⟩ := lw_st hlw
      · rw [byteAt_some_of hpa hd (v := 1) (by decide)] at hb; cases hb
      · rw [byteAt_none_of hpa hd (by decide)] at hb; cases hb
    | 1, _ =>
      obtain ⟨rfl, _⟩ := qLW_writer (hQ 1) he het
      obtain ⟨hpa, hd⟩ := lw_st hlw; rw [byteAt_none_of hpa hd (by decide)] at hb; cases hb
    | 2, _ => rw [qRR_nots (hQ 2) he] at het; cases het)
  subst hsx
  exact hord hnc (st_writes hwf hinx htx (by decide) htx (by omega))

/-! ## Row 24, WRC+fence.rw.rws -/

def QsWRC (M : List PMsg) : Nat → Trace → Prop
  | 0 => qS (X : Int) (toBytes 1 4) [.DReg 6] [.DReg 5]
  | 1 => qLW (X : Int) (Y : Int) 4 (toBytes 1 4) [.DReg 6] [.DReg 8] [.DReg 7]
  | 2 => qRR M (Y : Int) (X : Int) 4 [.DReg 6] [.DReg 8]
  | _ => q0

/-- **ROW 24, WRC+fence.rw.rws: FORBIDDEN, in the logic** (plan §5 row 24, rule 4, multi-copy atomicity). -/
theorem lit_wrcF : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.wrcF) () (progs Weak.Prom.Ref.Lit.wrcF) M run →
    ¬ (run.obsLoad 1 0 = some 1 ∧ run.obsLoad 2 0 = some 1 ∧ run.obsLoad 2 1 = some 0) := by
  intro M run hrun
  obtain ⟨_, hQ, hnc, hpart, hwf, himg, _⟩ := kitAdeq (π := Proto.triv) (QsWRC M) (fun _ _ => True) trivial
    (fun h => match h with | 0 => trivial | 1 => trivial | 2 => trivial | _ + 3 => rfl)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, _, hrd⟩ := progs_get hp
      match h with
      | 0 =>
        exact hW_hart _ M 0 p 4 X 1 6 5 (by rw [hpr]; rfl) hpc hq (by decide)
          (by rw [hrd 6 (by decide) (by decide)]; rfl) (by rw [hrd 5 (by decide) (by decide)]; rfl)
          (by decide) (by decide)
      | 1 =>
        exact hRW_hart _ M 1 p 4 X Y 1 6 8 5 7 true true true (by rw [hpr]; rfl) hpc hq (by decide) (by decide)
          (by decide) (by rw [hrd 6 (by decide) (by decide)]; rfl) (by rw [hrd 8 (by decide) (by decide)]; rfl)
          (by rw [hrd 7 (by decide) (by decide)]; rfl) (by decide) (by decide) (by decide) (by decide)
      | 2 =>
        exact hRR_hart _ M 2 p 4 Y X 6 8 5 7 true true true (by rw [hpr]; rfl) hpc hq (by decide) (by decide)
          (by decide) (by rw [hrd 6 (by decide) (by decide)]; rfl) (by rw [hrd 8 (by decide) (by decide)]; rfl)
          (by decide) (by decide) (by decide) (by decide)
      | n + 3 =>
        have hl : (progs Weak.Prom.Ref.Lit.wrcF).length = 3 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  rintro ⟨ho1, ho2, ho3⟩
  have hout : ∀ h, 3 ≤ h → memEv (run.trace h) = [] := fun h hh => by
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 3 := ⟨h - 3, by omega⟩; exact hQ (k + 3)
  obtain ⟨sx1, bx1, hrx1, hvx1, hsx1⟩ := qLW_out hwf (by decide) (hQ 1) ho1
  obtain ⟨sy, sx, by0, bx, hry, hvy, hrx, hvx, hord⟩ := qRR_out hwf (by decide) (hQ 2) ho2 ho3
  rw [himg] at hrx1 hry hrx
  -- `sy`: H1's `st y`, above `sx1`
  obtain ⟨ky, my, rfl, hmy, hby⟩ := src_of_val hry rfl (by rw [bv_of_toNat hvy (by decide)]; decide)
  obtain ⟨hy, hhy, ey, hey, hety, hlwy⟩ := writer_cases hpart hwf 3 hout hmy
  have hxy : sx1 < ky + 1 := by
    match hy, hhy with
    | 0, _ =>
      rw [qS_writer (hQ 0) hey hety] at hlwy
      obtain ⟨hpa, hd⟩ := lw_st hlwy; rw [byteAt_none_of hpa hd (by decide)] at hby; cases hby
    | 1, _ =>
      obtain ⟨rfl, _⟩ := qLW_writer (hQ 1) hey hety
      exact hsx1 _ hey
    | 2, _ => rw [qRR_nots (hQ 2) hey] at hety; cases hety
  -- `sx1`: H0's `st x`
  obtain ⟨kx, mx, rfl, hmx, hbx⟩ := src_of_val hrx1 rfl (by rw [bv_of_toNat hvx1 (by decide)]; decide)
  obtain ⟨hx, hhx, ex, hex, hetx, hlwx⟩ := writer_cases hpart hwf 3 hout hmx
  have hinx : (LStore false false (X : Int) (toBytes 1 4) [.DReg 6] [.DReg 5], some (kx + 1)) ∈
      memEv (run.trace 0) := by
    match hx, hhx with
    | 0, _ => rw [← qS_writer (hQ 0) hex hetx]; exact hex
    | 1, _ =>
      obtain ⟨rfl, _⟩ := qLW_writer (hQ 1) hex hetx
      obtain ⟨hpa, hd⟩ := lw_st hlwx; rw [byteAt_none_of hpa hd (by decide)] at hbx; cases hbx
    | 2, _ => rw [qRR_nots (hQ 2) hex] at hetx; cases hetx
  have hsx : sx = 0 := src_img0 hrx (bv_of_toNat hvx (by decide)) (fun k m hm hb => by
    obtain ⟨h, hh, e, he, het, hlw⟩ := writer_cases hpart hwf 3 hout hm
    match h, hh with
    | 0, _ =>
      rw [qS_writer (hQ 0) he het] at hlw
      obtain ⟨hpa, hd⟩ := lw_st hlw; rw [byteAt_some_of hpa hd (v := 1) (by decide)] at hb; cases hb
    | 1, _ =>
      obtain ⟨rfl, _⟩ := qLW_writer (hQ 1) he het
      obtain ⟨hpa, hd⟩ := lw_st hlw; rw [byteAt_none_of hpa hd (by decide)] at hb; cases hb
    | 2, _ => rw [qRR_nots (hQ 2) he] at het; cases het)
  subst hsx
  exact hord hnc (st_writes hwf hinx (by omega) (by decide) (by omega) (by omega))

/-! ## Row 25, IRIW+fence.r.rws -/

def QsIRIW (M : List PMsg) : Nat → Trace → Prop
  | 0 => qS (X : Int) (toBytes 1 4) [.DReg 6] [.DReg 5]
  | 1 => qRR M (X : Int) (Y : Int) 4 [.DReg 6] [.DReg 8]
  | 2 => qS (Y : Int) (toBytes 1 4) [.DReg 6] [.DReg 5]
  | 3 => qRR M (Y : Int) (X : Int) 4 [.DReg 6] [.DReg 8]
  | _ => q0

/-- **ROW 25, IRIW+fence.r.rws: FORBIDDEN, in the logic** (plan §5 row 25, rule 4, multi-copy atomicity): the two
readers cannot disagree on the order of the two independent stores. -/
theorem lit_iriwF : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.iriwF) () (progs Weak.Prom.Ref.Lit.iriwF) M run →
    ¬ (run.obsLoad 1 0 = some 1 ∧ run.obsLoad 1 1 = some 0 ∧ run.obsLoad 3 0 = some 1 ∧ run.obsLoad 3 1 = some 0) := by
  intro M run hrun
  obtain ⟨_, hQ, hnc, hpart, hwf, himg, _⟩ := kitAdeq (π := Proto.triv) (QsIRIW M) (fun _ _ => True) trivial
    (fun h => match h with | 0 => trivial | 1 => trivial | 2 => trivial | 3 => trivial | _ + 4 => rfl)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, _, hrd⟩ := progs_get hp
      match h with
      | 0 =>
        exact hW_hart _ M 0 p 4 X 1 6 5 (by rw [hpr]; rfl) hpc hq (by decide)
          (by rw [hrd 6 (by decide) (by decide)]; rfl) (by rw [hrd 5 (by decide) (by decide)]; rfl)
          (by decide) (by decide)
      | 1 =>
        exact hRR_hart _ M 1 p 4 X Y 6 8 5 7 true false true (by rw [hpr]; rfl) hpc hq (by decide) (by decide)
          (by decide) (by rw [hrd 6 (by decide) (by decide)]; rfl) (by rw [hrd 8 (by decide) (by decide)]; rfl)
          (by decide) (by decide) (by decide) (by decide)
      | 2 =>
        exact hW_hart _ M 2 p 4 Y 1 6 5 (by rw [hpr]; rfl) hpc hq (by decide)
          (by rw [hrd 6 (by decide) (by decide)]; rfl) (by rw [hrd 5 (by decide) (by decide)]; rfl)
          (by decide) (by decide)
      | 3 =>
        exact hRR_hart _ M 3 p 4 Y X 6 8 5 7 true false true (by rw [hpr]; rfl) hpc hq (by decide) (by decide)
          (by decide) (by rw [hrd 6 (by decide) (by decide)]; rfl) (by rw [hrd 8 (by decide) (by decide)]; rfl)
          (by decide) (by decide) (by decide) (by decide)
      | n + 4 =>
        have hl : (progs Weak.Prom.Ref.Lit.iriwF).length = 4 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  rintro ⟨ho1, ho2, ho3, ho4⟩
  have hout : ∀ h, 4 ≤ h → memEv (run.trace h) = [] := fun h hh => by
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 4 := ⟨h - 4, by omega⟩; exact hQ (k + 4)
  obtain ⟨sx, sy, bx, by0, hrx, hvx, hry, hvy, hord1⟩ := qRR_out hwf (by decide) (hQ 1) ho1 ho2
  obtain ⟨sy', sx', by', bx', hry', hvy', hrx', hvx', hord3⟩ := qRR_out hwf (by decide) (hQ 3) ho3 ho4
  rw [himg] at hrx hry hry' hrx'
  -- a message holding 1 at `a` is the one-store hart's store; none holds 0 at x or y
  have hsrc : ∀ (k : Nat) (m : PMsg), M[k]? = some m → ∀ (b : BitVec 8),
      (m.byteAt (X : Int) = some b → b = 1 ∧
        (LStore false false (X : Int) (toBytes 1 4) [.DReg 6] [.DReg 5], some (k + 1)) ∈ memEv (run.trace 0)) ∧
      (m.byteAt (Y : Int) = some b → b = 1 ∧
        (LStore false false (Y : Int) (toBytes 1 4) [.DReg 6] [.DReg 5], some (k + 1)) ∈ memEv (run.trace 2)) := by
    intro k m hm b
    obtain ⟨h, hh, e, he, het, hlw⟩ := writer_cases hpart hwf 4 hout hm
    match h, hh with
    | 0, _ =>
      have hee := qS_writer (hQ 0) he het
      rw [hee] at hlw he
      obtain ⟨hpa, hd⟩ := lw_st hlw
      refine ⟨fun hb => ⟨?_, he⟩, fun hb => ?_⟩
      · rw [byteAt_some_of hpa hd (v := 1) (by decide)] at hb; cases hb; rfl
      · rw [byteAt_none_of hpa hd (by decide)] at hb; cases hb
    | 1, _ => rw [qRR_nots (hQ 1) he] at het; cases het
    | 2, _ =>
      have hee := qS_writer (hQ 2) he het
      rw [hee] at hlw he
      obtain ⟨hpa, hd⟩ := lw_st hlw
      refine ⟨fun hb => ?_, fun hb => ⟨?_, he⟩⟩
      · rw [byteAt_none_of hpa hd (by decide)] at hb; cases hb
      · rw [byteAt_some_of hpa hd (v := 1) (by decide)] at hb; cases hb; rfl
    | 3, _ => rw [qRR_nots (hQ 3) he] at het; cases het
  obtain ⟨kx, mx, rfl, hmx, hbx⟩ := src_of_val hrx rfl (by rw [bv_of_toNat hvx (by decide)]; decide)
  obtain ⟨ky, my, rfl, hmy, hby⟩ := src_of_val hry' rfl (by rw [bv_of_toNat hvy' (by decide)]; decide)
  have hinx := ((hsrc kx mx hmx bx).1 hbx).2
  have hiny := ((hsrc ky my hmy by').2 hby).2
  have hsy : sy = 0 := src_img0 hry (bv_of_toNat hvy (by decide)) (fun k m hm hb => by
    have := ((hsrc k m hm 0).2 hb).1; cases this)
  have hsx : sx' = 0 := src_img0 hrx' (bv_of_toNat hvx' (by decide)) (fun k m hm hb => by
    have := ((hsrc k m hm 0).1 hb).1; cases this)
  subst hsy hsx
  rcases Nat.lt_or_ge kx ky with hlt | hge
  · exact hord3 hnc (st_writes hwf hinx (by omega) (by decide) (by omega) (by omega))
  · exact hord1 hnc (st_writes hwf hiny (by omega) (by decide) (by omega) (by omega))

/-! ## Row 21′, 2+2W+fence.w.ws -/

def QsW22 : Nat → Trace → Prop
  | 0 => qWW (X : Int) (Y : Int) (toBytes 2 4) (toBytes 1 4) [.DReg 6] [.DReg 5] [.DReg 8] [.DReg 7]
  | 1 => qWW (Y : Int) (X : Int) (toBytes 2 4) (toBytes 1 4) [.DReg 6] [.DReg 5] [.DReg 8] [.DReg 7]
  | _ => q0

/-- The H0/H1 stores of row 21′: a message writing x (resp. y) is one of the two harts' stores. -/
theorem w22_writer {run : PFRun LP Unit} {M : List PMsg}
    (hpart : ∀ t, 1 ≤ t → t ≤ M.length → exU (fun h => t ∈ run.fulfils h ∧ tidAt M t = some h))
    (hwf : run.traceWf M) (hQ : ∀ h, QsW22 h (memEv (run.trace h))) {k : Nat} {m : PMsg} (hm : M[k]? = some m)
    {a : Int} (hc : (m.byteAt a).isSome = true) (ha : a = (X : Int) ∨ a = (Y : Int)) :
    (a = (X : Int) → ((m.byteAt a).map BitVec.toNat).getD 0 = 2 →
      (LStore false false (X : Int) (toBytes 2 4) [.DReg 6] [.DReg 5], some (k + 1)) ∈ memEv (run.trace 0)) ∧
    (a = (Y : Int) → ((m.byteAt a).map BitVec.toNat).getD 0 = 2 →
      (LStore false false (Y : Int) (toBytes 2 4) [.DReg 6] [.DReg 5], some (k + 1)) ∈ memEv (run.trace 1)) := by
  have hout : ∀ h, 2 ≤ h → memEv (run.trace h) = [] := fun h hh => by
    obtain ⟨j, rfl⟩ : ∃ j, h = j + 2 := ⟨h - 2, by omega⟩; exact hQ (j + 2)
  obtain ⟨h, hh, e, he, het, hlw⟩ := writer_cases hpart hwf 2 hout hm
  match h, hh with
  | 0, _ =>
    rcases qWW_writer (hQ 0) he het with rfl | ⟨rfl, _⟩ <;> obtain ⟨hpa, hd⟩ := lw_st hlw
    · refine ⟨fun _ _ => he, fun hay hv => ?_⟩
      subst hay; rw [byteAt_none_of hpa hd (by decide)] at hc; cases hc
    · refine ⟨fun hax hv => ?_, fun hay hv => ?_⟩
      · subst hax; rw [byteAt_none_of hpa hd (by decide)] at hc; cases hc
      · subst hay; rw [byteAt_some_of hpa hd (v := 1) (by decide)] at hv; cases hv
  | 1, _ =>
    rcases qWW_writer (hQ 1) he het with rfl | ⟨rfl, _⟩ <;> obtain ⟨hpa, hd⟩ := lw_st hlw
    · refine ⟨fun hax hv => ?_, fun _ _ => he⟩
      subst hax; rw [byteAt_none_of hpa hd (by decide)] at hc; cases hc
    · refine ⟨fun hax hv => ?_, fun hay hv => ?_⟩
      · subst hax; rw [byteAt_some_of hpa hd (v := 1) (by decide)] at hv; cases hv
      · subst hay; rw [byteAt_none_of hpa hd (by decide)] at hc; cases hc

/-- **ROW 21′, 2+2W+fence.w.ws: FORBIDDEN, in the logic** (plan §5 row 21, rule 4): in every valid run in which both
harts finished, not both final values are 2 (A0 (i) gives each finished hart's stores in `M`, in order). -/
theorem lit_w22F : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.w22F) () (progs Weak.Prom.Ref.Lit.w22F) M run →
    run.done litDone 0 () → run.done litDone 1 () →
    ¬ (finalMem (testImg Weak.Prom.Ref.Lit.w22F) M X 4 = 2 ∧ finalMem (testImg Weak.Prom.Ref.Lit.w22F) M Y 4 = 2) := by
  intro M run hrun hd0 hd1
  obtain ⟨hi, hQ, _, hpart, hwf, _, _⟩ := kitAdeq (π := Proto.triv) QsW22
    (fun h _ => match h with
      | 0 => wwDone M 0 (X : Int) (Y : Int) (toBytes 2 4) (toBytes 1 4)
      | 1 => wwDone M 1 (Y : Int) (X : Int) (toBytes 2 4) (toBytes 1 4)
      | _ => True) trivial
    (fun h => match h with | 0 => trivial | 1 => trivial | _ + 2 => rfl)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, _, hrd⟩ := progs_get hp
      match h with
      | 0 =>
        exact hWW_hart _ M 0 p 4 X Y 2 1 6 8 5 7 false false (by rw [hpr]; rfl) hpc hq (by decide)
          (by rw [hrd 5 (by decide) (by decide)]; rfl) (by rw [hrd 7 (by decide) (by decide)]; rfl)
          (by rw [hrd 6 (by decide) (by decide)]; rfl) (by rw [hrd 8 (by decide) (by decide)]; rfl)
          (by decide) (by decide) (by decide) (by decide)
      | 1 =>
        exact hWW_hart _ M 1 p 4 Y X 2 1 6 8 5 7 false false (by rw [hpr]; rfl) hpc hq (by decide)
          (by rw [hrd 5 (by decide) (by decide)]; rfl) (by rw [hrd 7 (by decide) (by decide)]; rfl)
          (by rw [hrd 6 (by decide) (by decide)]; rfl) (by rw [hrd 8 (by decide) (by decide)]; rfl)
          (by decide) (by decide) (by decide) (by decide)
      | n + 2 =>
        have hl : (progs Weak.Prom.Ref.Lit.w22F).length = 2 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  rintro ⟨hfx, hfy⟩
  obtain ⟨t0x, t0y, h0x, h0xy, hm0x, hm0y⟩ := hi 0 () hd0
  obtain ⟨t1y, t1x, h1y, h1yx, hm1y, hm1x⟩ := hi 1 () hd1
  have hlx := finalMem_b0 hfx (by decide)
  have hly := finalMem_b0 hfy (by decide)
  -- the store holding 2 at x is H0's first store, at `t0x`; the one holding 2 at y is H1's, at `t1y`
  have hux : ∀ (k : Nat) (m : PMsg), M[k]? = some m → (m.byteAt (X : Int)).isSome = true →
      ((m.byteAt (X : Int)).map BitVec.toNat).getD 0 = 2 % 256 → k = t0x - 1 := by
    intro k m hm hc hv
    have e1 := (w22_writer hpart hwf hQ hm hc (.inl rfl)).1 rfl hv
    have e2 := (w22_writer hpart hwf hQ hm0x (by rw [byteAt_some_of rfl rfl (v := 2) (by decide)]; rfl)
      (.inl rfl)).1 rfl (by rw [byteAt_some_of rfl rfl (v := 2) (by decide)]; rfl)
    have := qWW_first (hQ 0) (by decide) e1 e2
    omega
  have huy : ∀ (k : Nat) (m : PMsg), M[k]? = some m → (m.byteAt (Y : Int)).isSome = true →
      ((m.byteAt (Y : Int)).map BitVec.toNat).getD 0 = 2 % 256 → k = t1y - 1 := by
    intro k m hm hc hv
    have e1 := (w22_writer hpart hwf hQ hm hc (.inr rfl)).2 rfl hv
    have e2 := (w22_writer hpart hwf hQ hm1y (by rw [byteAt_some_of rfl rfl (v := 2) (by decide)]; rfl)
      (.inr rfl)).2 rfl (by rw [byteAt_some_of rfl rfl (v := 2) (by decide)]; rfl)
    have := qWW_first (hQ 1) (by decide) e1 e2
    omega
  have hx := last_order hlx (by decide) hm1x (by rw [byteAt_some_of rfl rfl (v := 1) (by decide)]; rfl)
    (by rw [byteAt_some_of rfl rfl (v := 1) (by decide)]; decide) hux
  have hy := last_order hly (by decide) hm0y (by rw [byteAt_some_of rfl rfl (v := 1) (by decide)]; rfl)
    (by rw [byteAt_some_of rfl rfl (v := 1) (by decide)]; decide) huy
  omega

end Weak.Prom.PF

#print axioms Weak.Prom.PF.lit_sbFF
#print axioms Weak.Prom.PF.lit_isa2F
#print axioms Weak.Prom.PF.lit_wrcF
#print axioms Weak.Prom.PF.lit_iriwF
#print axioms Weak.Prom.PF.lit_w22F
