/-
Weak/Prom: **row 18, addrpo (manual `litmus:addrdatarfi_no`), proved IN THE LOGIC** (stage S2; plan rev 7 §5 row 18
"FORBIDDEN (manual, rule 13) — vcap from addr", §8 S2).

`Lit.addrpo` (RefTests.lean, x = 0x1000, y = 0x2000, z = 0x3000): H0 `lw a0,0(s0); fence rw,rw; sw s2,0(s1)`
(s0 = x, s1 = y, s2 = z) ‖ H1 `li t1,1; lw a1,0(s1); lw a2,0(a1); sw t1,0(s0)` (s0 = x, s1 = y); outcome
`a0 = 1 ∧ a1 = z` FORBIDDEN.
* H0 (`hRW_hart`): `s_x < ty` (rule 4).
* H1 (`addrpo1_hart`): the second load's ADDRESS is the first load's value; rule 13 (the address capture `vcap ⊔= va`,
  `loadRun`) puts every source the first load read below the capture view, which every later store's pre-view
  contains (`stPreA ≥ vcap`): every byte source of `lw a1,(y)` is below `tx`.  The second load's address is a
  loaded value: when it is misaligned the hart is stuck (`wpK_stuckLd`, MaybeStuck), so Ψ needs no case for it.
* Contradiction: `a0 = 1` makes `s_x` H1's `st x`, `a1 = z` makes byte 1 of `lw a1,(y)` (0x30) H0's `st y`
  (byte 0 of z is 0, the image's value, so the byte-1 source is the identifying one); then `ty < tx = s_x < ty`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreLitP

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal FenceSet AmoOp)
open Weak.Prom.Ref.Lit (X Y Z)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

theorem bytesAll_forall {P : Nat → Prop} : ∀ (a : Int) (l : List (Nat × BitVec 8)),
    bytesAll (fun _ u _ => P u) a l → ∀ tv ∈ l, P tv.1
  | _, [], _, _, h => by cases h
  | a, (t, v) :: r, ⟨h1, h2⟩, tv, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact h1
    · exact bytesAll_forall (a + 1) r h2 tv h

section rule

variable {V : Type}
variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [InvGS_gen hlc GF]
variable {γ : GName} {π : Proto} {w : HW LP Unit V} {Q : Trace → Prop} {Φ : V → IProp GF}

/-- A load at a misaligned address is stuck (no label; MaybeStuck). -/
theorem wpK_stuckLd {s : LP} {sz rd rs1 off : Nat} {sgn : Bool} {ws : PState} {pr : GSet Nat} {ev : Trace}
    (hag : LitAg w s) (hd : w.pdone s = none) (hq : s.q = []) (hp : s.prog[s.pc]? = some (.load sz sgn rd rs1 off))
    (ha : aligned ((s.rd rs1 + off) % two64) sz = false) :
    lh γ π w Q ws pr ev ⊢ wpK γ π w Q s Φ := by
  iintro ⟨%τ, Hst, %_⟩
  iapply (wpH_stuck hd (fun l s' hs => by
    rw [hag l s'] at hs
    unfold litNext at hs
    rw [hq] at hs
    simp [hp, instrNext, ha] at hs))
  iexact Hst

end rule

/-- H1's Ψ: `ld y`, a load at the loaded address, then `st x` above every byte source of `ld y`. -/
def qAd1 : Trace → Prop :=
  q3 (isLd (Y : Int) 4 [.DReg 9]) (fun _ e1 => ∃ b : Nat, isLd (b : Int) 4 [.DReg 11] e1)
    (fun e0 _ e2 => isSt (X : Int) (toBytes 1 4) [.DReg 8] [.DReg 6] e2 ∧ ∀ tv ∈ tvsOf e0, tv.1 < tsOf e2)

section hart

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [InvGS_gen hlc GF]

/-- **Row 18's H1 in the logic** (rule 13). -/
theorem addrpo1_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP)
    (hprog : s0.prog = [.alui .add 6 0 1, .load 4 true 11 9 0, .load 4 true 12 11 0, .store 4 6 8 0])
    (hpc : s0.pc = 0) (hq : s0.q = []) (hlen : s0.regs.length = 32) (h8 : s0.rd 8 = X) (h9 : s0.rd 9 = Y) :
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩ (ΨK M qAd1) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  have hw := litW_lit img M h
  have hag := litAg_lit (V := Unit) litDone img M h
  iapply (wpK_start (by trivial))
  iintro %γ %P0 Hl
  iapply (wpK_alui hw (hag s0) hq (by rw [hprog, hpc]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e16 : s1.rd 6 = 1 := li_val hs1 (by decide) (by rw [hlen]; decide) (by decide)
  have e18 : s1.rd 8 = X := by rw [LPstep_rd hs1 8 (.inl (by decide)), h8]
  have e19 : s1.rd 9 = Y := by rw [LPstep_rd hs1 9 (.inl (by decide)), h9]
  iapply (wpK_ld (sz := 4) (sgn := true) (rd := 11) (rs1 := 9) (off := 0) (base := (Y : Int)) hw (hag s1) hq1
    (by rw [hP1, hc1]; rfl) (alg_of e19 (by decide) (by decide)) (base_of e19 (by decide)))
  iframe Hl
  inext
  iintro %tvs1 %hl1 %_
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ⟨tvs1, rfl, hl1⟩⟩
  iintro %s2 %hs2 Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have hp2 : s2.prog[s2.pc]? = some (.load 4 true 12 11 0) := by rw [hP2, hc2]; rfl
  have e26 : s2.rd 6 = 1 := by rw [LPstep_rd hs2 6 (.inl (by decide)), e16]
  have e28 : s2.rd 8 = X := by rw [LPstep_rd hs2 8 (.inl (by decide)), e18]
  -- the second load's address is the loaded value: stuck unless aligned
  by_cases hal' : aligned ((s2.rd 11 + 0) % two64) 4 = false
  · iapply (wpK_stuckLd (hag s2) (litDone_pc (by rw [hP2, hc2]; decide)) hq2 hp2 hal')
    iexact Hl
  have hal : aligned ((s2.rd 11 + 0) % two64) 4 = true := by simpa using hal'
  iapply (wpK_ld (sz := 4) (sgn := true) (rd := 12) (rs1 := 11) (off := 0)
    (base := (((s2.rd 11 + 0) % two64 : Nat) : Int)) hw (hag s2) hq2 hp2 hal rfl)
  iframe Hl
  inext
  iintro %tvs2 %hl2 %_
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ⟨⟨tvs1, rfl, hl1⟩, ⟨_, tvs2, rfl, hl2⟩⟩⟩
  iintro %s3 %hs3 Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  have e36 : s3.rd 6 = 1 := by rw [LPstep_rd hs3 6 (.inl (by decide)), e26]
  have e38 : s3.rd 8 = X := by rw [LPstep_rd hs3 8 (.inl (by decide)), e28]
  iapply (wpK_sw (sz := 4) (rs2 := 6) (rs1 := 8) (off := 0) (base := (X : Int)) hw (hag s3) hq3
    (by rw [hP3, hc3]; rfl) (alg_of e38 (by decide) (by decide)) (base_of e38 (by decide)))
  iframe Hl
  inext
  iintro %tx %_ %_ %_ %hx
  -- rule 13: every byte source of the first load is below the capture view, below the store's pre-view
  have hall : ∀ tv ∈ tvs1, tv.1 < tx := by
    have hb := loadRun_ldv (instrR (regWP psInit 6 (srcR 0))) false false
      (srcsView (instrR (regWP psInit 6 (srcR 0))) (srcR 9)) (Y : Int) tvs1
    have hb' : bytesAll (fun _ u _ => u ≤ (loadRun (instrR (regWP psInit 6 (srcR 0))) false false
        (srcsView (instrR (regWP psInit 6 (srcR 0))) (srcR 9)) (Y : Int) tvs1).wLdv) (Y : Int) tvs1 :=
      bytesAll_mono (fun x u v h => by rwa [fwdView_empty rfl] at h) _ _ hb
    intro tv htv
    have h1 := bytesAll_forall (P := fun u => u ≤ _) _ _ hb' tv htv
    simp [stPreA, stPre, regWL] at hx h1
    omega
  imodintro
  isplitr
  · ipureintro
    exact ⟨0, grd_intro ⟨⟨tvs1, rfl, hl1⟩, ⟨_, tvs2, rfl, hl2⟩, ⟨tx, by omega, by simp only [e36]; rfl⟩, hall⟩⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro %s4 %hs4 Hl
  obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4 hP3 (by rw [hc3])
  iapply (wpK_fin hq4 (by rw [hP4, hc4]; simp))
  iexact Hl

end hart

def QsAd (M : List PMsg) : Nat → Trace → Prop
  | 0 => qLW (X : Int) (Y : Int) 4 (toBytes Z 4) [.DReg 8] [.DReg 9] [.DReg 18]
  | 1 => qAd1
  | _ => q0

/-- H1's timestamped entry is its store, above every byte source of its FIRST memory entry (`ld y`). -/
theorem qAd1_writer {ev : Trace} {e : PEv} {t : Nat} (hQ : qAd1 ev) (he : e ∈ ev) (ht : e.2 = some t) :
    e = (LStore false false (X : Int) (toBytes 1 4) [.DReg 8] [.DReg 6], some t) ∧
      ∃ tvs0 r, ev = (LLoad false false (Y : Int) tvs0 [.DReg 9], none) :: r ∧ tvs0.length = 4 ∧
        ∀ tv ∈ tvs0, tv.1 < t := by
  rcases q3_cases hQ with rfl | ⟨e0, rfl, ⟨_, rfl, _⟩⟩ | ⟨e0, e1, rfl, ⟨_, rfl, _⟩, ⟨_, _, rfl, _⟩⟩ |
      ⟨e0, e1, e2, rfl, ⟨tvs0, rfl, hl0⟩, ⟨_, _, rfl, _⟩, ⟨t2, _, rfl⟩, hall⟩
  · cases he
  · rw [List.mem_singleton] at he; subst he; cases ht
  · rcases List.mem_cons.1 he with rfl | he
    · cases ht
    · rw [List.mem_singleton] at he; subst he; cases ht
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · cases ht
    · cases ht
    · cases ht; exact ⟨rfl, tvs0, _, rfl, hl0, hall⟩

/-- **ROW 18, addrpo (manual `litmus:addrdatarfi_no`): FORBIDDEN, in the logic** (plan §5 row 18, rules 4, 13). -/
theorem lit_addrpo : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.addrpo) () (progs Weak.Prom.Ref.Lit.addrpo) M run →
    ¬ (run.obsLoad 0 0 = some 1 ∧ run.obsLoad 1 0 = some Z) := by
  intro M run hrun
  obtain ⟨_, hQ, hnc, hpart, hwf, himg, _⟩ := kitAdeq (π := Proto.triv) (QsAd M) (fun _ _ => True) trivial
    (fun h => match h with | 0 => trivial | 1 => trivial | _ + 2 => rfl)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, hlen, hrd⟩ := progs_get hp
      match h with
      | 0 =>
        exact hRW_hart _ M 0 p 4 X Y Z 8 9 10 18 true true true (by rw [hpr]; rfl) hpc hq (by decide) (by decide)
          (by decide) (by rw [hrd 8 (by decide) (by decide)]; rfl) (by rw [hrd 9 (by decide) (by decide)]; rfl)
          (by rw [hrd 18 (by decide) (by decide)]; rfl) (by decide) (by decide) (by decide) (by decide)
      | 1 =>
        exact addrpo1_hart _ M 1 p (by rw [hpr]; rfl) hpc hq hlen (by rw [hrd 8 (by decide) (by decide)]; rfl)
          (by rw [hrd 9 (by decide) (by decide)]; rfl)
      | n + 2 =>
        have hl : (progs Weak.Prom.Ref.Lit.addrpo).length = 2 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  rintro ⟨ho0, ho1⟩
  have hout : ∀ h, 2 ≤ h → memEv (run.trace h) = [] := fun h hh => by
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 2 := ⟨h - 2, by omega⟩; exact hQ (k + 2)
  -- H0: its load's source `sx` (value 1) is below its `st y`
  obtain ⟨sx, bx, hrx, hvx, hsx⟩ := qLW_out hwf (by decide) (hQ 0) ho0
  rw [himg] at hrx
  obtain ⟨kx, mx, rfl, hmx, hbx⟩ := src_of_val hrx rfl (by rw [bv_of_toNat hvx (by decide)]; decide)
  -- `sx` is H1's `st x`, above every byte source of H1's first load
  obtain ⟨tvs0, r, hev, hl0, hall⟩ : ∃ tvs0 r, memEv (run.trace 1) =
      (LLoad false false (Y : Int) tvs0 [.DReg 9], none) :: r ∧ tvs0.length = 4 ∧ ∀ tv ∈ tvs0, tv.1 < kx + 1 := by
    obtain ⟨h, hh, e, he, het, hlw⟩ := writer_cases hpart hwf 2 hout hmx
    match h, hh with
    | 0, _ =>
      obtain ⟨rfl, _⟩ := qLW_writer (hQ 0) he het
      obtain ⟨hpa, hd⟩ := lw_st hlw; rw [byteAt_none_of hpa hd (by decide)] at hbx; cases hbx
    | 1, _ => exact (qAd1_writer (hQ 1) he het).2
  -- H1's first load returned z: its byte 1 (0x30) is H0's `st y`
  rw [obsLoad_memEv, hev] at ho1
  simp only [loadsOf, List.filterMap_cons, loadLikeTvs, List.getElem?_cons_zero, Option.map_some,
    Option.some.injEq] at ho1
  obtain ⟨⟨u0, b0⟩, ⟨u1, b1⟩, ⟨u2, b2⟩, ⟨u3, b3⟩, rfl⟩ : ∃ p0 p1 p2 p3, tvs0 = [p0, p1, p2, p3] := by
    match tvs0, hl0 with
    | [p0, p1, p2, p3], _ => exact ⟨p0, p1, p2, p3, rfl⟩
  simp only [obsOf, List.foldr_cons, List.foldr_nil] at ho1
  have hb1 : b1 = 0x30 := by
    apply BitVec.eq_of_toNat_eq
    have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt
    simp only [Z] at ho1
    show b1.toNat = 0x30
    omega
  have hm1 : (LLoad false false (Y : Int) [(u0, b0), (u1, b1), (u2, b2), (u3, b3)] [.DReg 9], (none : Option Nat)) ∈
      memEv (run.trace 1) := by rw [hev]; simp
  have hrd1 := (kit_read hwf hm1 rfl).2.1
  rw [himg, hb1] at hrd1
  obtain ⟨k1, m1, rfl, hm1', hb1'⟩ := src_of_val hrd1 rfl (by decide)
  obtain ⟨h, hh, e, he, het, hlw⟩ := writer_cases hpart hwf 2 hout hm1'
  match h, hh with
  | 0, _ =>
    obtain ⟨rfl, _⟩ := qLW_writer (hQ 0) he het
    have h1 := hsx _ he
    have h2 := hall (k1 + 1, 0x30) (by rw [hb1]; simp)
    omega
  | 1, _ =>
    obtain ⟨rfl, _⟩ := qAd1_writer (hQ 1) he het
    obtain ⟨hpa, hd⟩ := lw_st hlw; rw [byteAt_none_of hpa hd (by decide)] at hb1'; cases hb1'

end Weak.Prom.PF

#print axioms Weak.Prom.PF.lit_addrpo
