/-
Weak/Prom: **rows 37 (LR;SC-fail;SC) and 32 (mixed-size single-copy atomicity), proved IN THE LOGIC** (stage S2;
plan rev 7 §5 rows 32, 37, §8 S2).

* Row 37, `Lit.lrScSc` = `lr.w a0,(x); sc.w a1,a2,(x); sc.w a3,a4,(x)`, outcome `a1 = 1 ∧ a3 = 0` FORBIDDEN
  (zalrsc.adoc: "Regardless of success or failure, executing an SC.W instruction invalidates any reservation held by
  this hart").  The outcome is on FINAL REGISTERS, so the hart's value is its final program state (`litFin`), and the
  verdict is A0's export (i): every finished hart's postcondition holds.  The hart proves it with the SC rule
  (`wpK_sc`): the first SC's every branch ends with `LExFail` (M16, `wRes := none`), so the second SC's success
  branch needs a reservation the state does not hold, and only its failure branch (`a3 := 1`) is live.
* Row 32, `Lit.mixSca` = A `sb 1,(x)` ‖ B `sh 0x0202,(x)` ‖ C `lh a0,(x)`, outcome `a0 = 0x0201 ∧` final byte
  `x = 0x02` FORBIDDEN (load value axiom + single-copy atomicity).  C's Ψ records the single read point of its two
  non-forwarded bytes (M9, `loadOk_sp2`: no write to byte 0 between byte 0's and byte 1's sources); byte 0 read A's
  store, byte 1 read B's, and B is co-last at x, so B's write to x lies in that window.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreLitA

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal FenceSet AmoOp)
open Weak.Prom.Ref.Lit (X Y Z)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## Row 37, LR;SC-fail;SC -/

/-- A litmus hart's value is its final program state (its final registers, `Mach.Cert.regOf`). -/
def litFin (s : LP) : Option LP := if s.q = [] ∧ s.prog.length ≤ s.pc then some s else none

theorem litW_fin (img : Image) (M : List PMsg) (h : Nat) : LitW (⟨litStep, litFin, img, M, h⟩ : HW LP Unit LP) := by
  refine ⟨fun s _ => litAg_lit _ _ _ _ s, fun s hs => ?_⟩
  show litFin s = none
  unfold litFin
  rw [if_neg]
  rintro ⟨hq, hp⟩
  rcases hs with hs | hs
  · exact hs hq
  · omega

section hart

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [InvGS_gen hlc GF]

/-- **Row 37's hart in the logic**: after `lr; sc` every branch has cleared the reservation, so the second `sc`
fails: at the end `a3 = 1`. -/
theorem lrScSc_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP) (a : Nat)
    (hprog : s0.prog = [.lr 4 false false 10 8, .sc 4 false false 11 12 8, .sc 4 false false 13 14 8])
    (hpc : s0.pc = 0) (hq : s0.q = []) (hlen : s0.regs.length = 32) (ha : s0.rd 8 = a) (hA : aligned a 4 = true)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a := by assumption) :   -- MachFix-R-b5
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litFin, img, M, h⟩ (ΨK M (fun _ => True)) s0
      (fun v => iprop(⌜∃ V, grd Proto.triv img M V (¬ (v.rd 11 = 1 ∧ v.rd 13 = 0))⌝)) := by
  have hw := litW_fin img M h
  have hag := litAg_lit (V := LP) litFin img M h
  iapply (wpK_start (by trivial))
  iintro %γ %P0 Hl
  iapply (wpK_lr (base := (a : Int)) hw (hag s0) hq (by rw [hprog, hpc]; rfl) (by rw [ha]; exact hA) (by rw [ha]))
  iframe Hl
  inext
  iintro %tvs %_ %_
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro trivial⟩
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e1 : s1.rd 8 = a := by rw [LPstep_rd hs1 8 (.inl (by decide)), ha]
  -- the second SC, from any state whose reservation is cleared
  have tail : ∀ (s2 : LP) (ws2 : PState) (pr2 : GSet Nat) (ev2 : Trace), s2.prog = s0.prog → s2.pc = 2 →
      s2.q = [] → s2.regs.length = 32 → s2.rd 8 = a →
      lh (GF := GF) γ Proto.triv ⟨litStep, litFin, img, M, h⟩ (fun _ => True) ws2 pr2 ev2 ∗ ⌜ws2.wRes = none⌝ ⊢
        wpK γ Proto.triv ⟨litStep, litFin, img, M, h⟩ (fun _ => True) s2
          (fun v => iprop(⌜∃ V, grd Proto.triv img M V (¬ (v.rd 11 = 1 ∧ v.rd 13 = 0))⌝)) := by
    intro s2 ws2 pr2 ev2 hP2 hc2 hq2 hl2 e2
    iintro ⟨Hl, %hres⟩
    iapply (wpK_sc (base := (a : Int)) hw (hag s2) hq2 (by rw [hP2, hprog, hc2]; rfl) (by rw [e2]; exact hA)
      (by rw [e2]))
    iframe Hl
    inext
    isplit
    · iintro %ts %R %hR
      rw [hres] at hR; cases hR
    · iintro %s3 %hs3 Hl
      obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 (hP2.trans hprog) (by rw [hc2])
      have e3 : s3.rd 13 = 1 := by rw [LPstep_rd_eq hs3 (by decide) (by rw [hl2]; decide)]; rfl
      iapply (wpK_end (v := s3) (hag s3) hq3 (by rw [hP3, hc3]; simp)
        (by show litFin s3 = some s3; unfold litFin; rw [if_pos ⟨hq3, by rw [hP3, hc3]; simp⟩]))
      iframe Hl
      imodintro
      ipureintro
      exact ⟨0, grd_intro (fun ⟨_, h13⟩ => by rw [e3] at h13; cases h13)⟩
  iapply (wpK_sc (base := (a : Int)) hw (hag s1) hq1 (by rw [hP1, hc1]; rfl) (by rw [e1]; exact hA) (by rw [e1]))
  iframe Hl
  inext
  isplit
  · iintro %ts %R %_ %_ %_ %_ %_ %_ %_
    imodintro
    isplitr
    · ipureintro; exact ⟨0, grd_intro trivial⟩
    isplitr
    · ipureintro; exact grd_intro trivial
    iintro %s2 %hs2 Hl
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
    iapply (tail s2 _ _ _ (by rw [hP2, hprog]) hc2 hq2 (by rw [LPstep_len hs2, LPstep_len hs1, hlen])
      (by rw [LPstep_rd hs2 8 (.inl (by decide)), e1]))
    iframe Hl
    ipureintro
    simp [regWL]
  · iintro %s2 %hs2 Hl
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
    iapply (tail s2 _ _ _ (by rw [hP2, hprog]) hc2 hq2 (by rw [LPstep_len hs2, LPstep_len hs1, hlen])
      (by rw [LPstep_rd hs2 8 (.inl (by decide)), e1]))
    iframe Hl
    ipureintro
    simp [regWL]

end hart

/-- **ROW 37, LR;SC-fail;SC: FORBIDDEN, in the logic** (plan §5 row 37, M16 `LExFail` clears `wRes`): in every valid
run, a finished hart's final registers are not `a1 = 1 ∧ a3 = 0`. -/
theorem lit_lrScSc : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.lrScSc) () (progs Weak.Prom.Ref.Lit.lrScSc) M run →
    ∀ s, run.done litFin 0 s → ¬ (s.rd 11 = 1 ∧ s.rd 13 = 0) := by
  intro M run hrun
  have hnoinv := Own.lit_noInvalT hrun   -- MachFix-R-b5
  obtain ⟨hi, _⟩ := kitAdeq (π := Proto.triv) (pdone := litFin)
    (fun h => match h with | 0 => fun _ => True | _ => q0)
    (fun h v => match h with | 0 => ¬ (v.rd 11 = 1 ∧ v.rd 13 = 0) | _ => True) trivial
    (fun h => match h with | 0 => trivial | _ + 1 => rfl)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, hlen, hrd⟩ := progs_get hp
      match h with
      | 0 =>
        exact lrScSc_hart _ M 0 p X (by rw [hpr]; rfl) hpc hq hlen (by rw [hrd 8 (by decide) (by decide)]; rfl)
          (by decide)
      | n + 1 =>
        have hl : (progs Weak.Prom.Ref.Lit.lrScSc).length = 1 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  intro s hd
  exact hi 0 s hd

/-! ## Row 32, mixed-size SCA -/

/-- A two-byte load whose bytes come from one read point: no write to byte 0 between their sources. -/
def qL2 (M : List PMsg) (a : Int) (p : Nat) : Trace → Prop :=
  q1 (fun e => isLd a 2 [.DReg p] e ∧
    (noCmo M → ∀ t0 v0 t1 v1, tvsOf e = [(t0, v0), (t1, v1)] → ¬ writesIn M a t0 t1))

section hart

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [InvGS_gen hlc GF]

/-- **Row 32's reader in the logic**: `lh d,(p)` proves `qL2` (M9: the single read point of non-forwarded bytes). -/
theorem hL2_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP) (a d p : Nat) (sg : Bool)
    (hprog : s0.prog = [.load 2 sg d p 0]) (hpc : s0.pc = 0) (hq : s0.q = []) (hp0 : p ≠ 0)
    (ha : s0.rd p = a) (hal : a < two64) (hA : aligned a 2 = true)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a := by assumption) :   -- MachFix-R-b5
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩ (ΨK M (qL2 M a p)) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  have hw := litW_lit img M h
  have hag := litAg_lit (V := Unit) litDone img M h
  iapply (wpK_start (by trivial))
  iintro %γ %P0 Hl
  iapply (wpK_ld (sz := 2) (sgn := sg) (rd := d) (rs1 := p) (off := 0) (base := (a : Int)) hw (hag s0) hq
    (by rw [hprog, hpc]; rfl) (alg_of ha hal hA) (base_of ha hal))
  iframe Hl
  inext
  iintro %tvs %hl %hlo
  imodintro
  isplitr
  · ipureintro
    refine ⟨0, grd_intro ⟨⟨tvs, by rw [srcR_pos hp0], hl⟩, fun hnc t0 v0 t1 v1 htv => ?_⟩⟩
    change tvs = _ at htv
    subst htv
    exact loadOk_sp2 hnc hlo (fwdHit_empty lookupEmpty) (fwdHit_empty lookupEmpty)
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  iapply (wpK_fin hq1 (by rw [hP1, hc1]; simp))
  iexact Hl

end hart

def QsSca (M : List PMsg) : Nat → Trace → Prop
  | 0 => qS (X : Int) (toBytes 1 1) [.DReg 8] [.DReg 5]
  | 1 => qS (X : Int) (toBytes 0x0202 2) [.DReg 8] [.DReg 5]
  | 2 => qL2 M (X : Int) 8
  | _ => q0

/-- **ROW 32, mixed-size SCA: FORBIDDEN, in the logic** (plan §5 row 32, M9 single read point): not (C reads
`0x0201` and the final byte at x is `0x02`). -/
theorem lit_mixSca : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.mixSca) () (progs Weak.Prom.Ref.Lit.mixSca) M run →
    ¬ (run.obsLoad 2 0 = some 0x0201 ∧ finalMem (testImg Weak.Prom.Ref.Lit.mixSca) M X 1 = 2) := by
  intro M run hrun
  have hnoinv := Own.lit_noInvalT hrun   -- MachFix-R-b5
  obtain ⟨_, hQ, hnc, hpart, hwf, himg, _⟩ := kitAdeq (π := Proto.triv) (QsSca M) (fun _ _ => True) trivial
    (fun h => match h with | 0 => trivial | 1 => trivial | 2 => trivial | _ + 3 => rfl)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, _, hrd⟩ := progs_get hp
      match h with
      | 0 =>
        exact hW_hart _ M 0 p 1 X 1 8 5 (by rw [hpr]; rfl) hpc hq (by decide)
          (by rw [hrd 8 (by decide) (by decide)]; rfl) (by rw [hrd 5 (by decide) (by decide)]; rfl)
          (by decide) (by decide)
      | 1 =>
        exact hW_hart _ M 1 p 2 X 0x0202 8 5 (by rw [hpr]; rfl) hpc hq (by decide)
          (by rw [hrd 8 (by decide) (by decide)]; rfl) (by rw [hrd 5 (by decide) (by decide)]; rfl)
          (by decide) (by decide)
      | 2 =>
        exact hL2_hart _ M 2 p X 10 8 true (by rw [hpr]; rfl) hpc hq (by decide)
          (by rw [hrd 8 (by decide) (by decide)]; rfl) (by decide) (by decide)
      | n + 3 =>
        have hl : (progs Weak.Prom.Ref.Lit.mixSca).length = 3 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  rintro ⟨ho, hf⟩
  have hout : ∀ h, 3 ≤ h → memEv (run.trace h) = [] := fun h hh => by
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 3 := ⟨h - 3, by omega⟩; exact hQ (k + 3)
  -- C's answers: byte 0 from A's store, byte 1 from B's
  rw [obsLoad_memEv] at ho
  rcases q1_cases (hQ 2) with hev | ⟨e, hev, ⟨tvs, rfl, hl⟩, hsp⟩
  · rw [hev] at ho; simp [loadsOf] at ho
  obtain ⟨⟨t0, v0⟩, ⟨t1, v1⟩, rfl⟩ : ∃ p q, tvs = [p, q] := by
    match tvs, hl with
    | [p, q], _ => exact ⟨p, q, rfl⟩
  have hm : (LLoad false false (X : Int) [(t0, v0), (t1, v1)] [.DReg 8], (none : Option Nat)) ∈ memEv (run.trace 2) := by
    rw [hev]; simp
  have hrd := kit_read hwf hm rfl
  rw [himg] at hrd
  obtain ⟨hr0, hr1, _⟩ := hrd
  rw [hev] at ho
  simp only [loadsOf, List.filterMap_cons, loadLikeTvs, List.filterMap_nil, List.getElem?_cons_zero,
    Option.map_some, Option.some.injEq, obsOf, List.foldr_cons, List.foldr_nil] at ho
  have hv0 : v0 = 1 := by
    apply BitVec.eq_of_toNat_eq; have := v0.isLt; have := v1.isLt; simp; omega
  have hv1 : v1 = 2 := by
    apply BitVec.eq_of_toNat_eq; have := v0.isLt; have := v1.isLt; simp; omega
  subst hv0 hv1
  obtain ⟨kA, mA, rfl, hmA, hbA⟩ := src_of_val hr0 rfl (by decide)
  obtain ⟨kB, mB, rfl, hmB, hbB⟩ := src_of_val hr1 rfl (by decide)
  have hWA := writer_cases hpart hwf 3 hout hmA
  have hWB := writer_cases hpart hwf 3 hout hmB
  -- A's message (kA) is A's store; B's message (kB) is B's store
  obtain ⟨eA, heA, hetA⟩ : ∃ e ∈ memEv (run.trace 0), e.2 = some (kA + 1) := by
    obtain ⟨h, hh, e, he, het, hlw⟩ := hWA
    match h, hh with
    | 0, _ => exact ⟨e, he, het⟩
    | 1, _ =>
      rw [qS_writer (hQ 1) he het] at hlw
      obtain ⟨hpa, hd⟩ := lw_st hlw; rw [byteAt_some_of hpa hd (v := 2) (by decide)] at hbA; cases hbA
    | 2, _ =>
      rcases q1_cases (hQ 2) with hev' | ⟨e', hev', ⟨_, rfl, _⟩, _⟩
      · rw [hev'] at he; cases he
      · rw [hev', List.mem_singleton] at he; subst he; cases het
  obtain ⟨eB, heB, hetB⟩ : ∃ e ∈ memEv (run.trace 1), e.2 = some (kB + 1) := by
    obtain ⟨h, hh, e, he, het, hlw⟩ := hWB
    match h, hh with
    | 0, _ =>
      rw [qS_writer (hQ 0) he het] at hlw
      obtain ⟨hpa, hd⟩ := lw_st hlw; rw [byteAt_none_of hpa hd (by decide)] at hbB; cases hbB
    | 1, _ => exact ⟨e, he, het⟩
    | 2, _ =>
      rcases q1_cases (hQ 2) with hev' | ⟨e', hev', ⟨_, rfl, _⟩, _⟩
      · rw [hev'] at he; cases he
      · rw [hev', List.mem_singleton] at he; subst he; cases het
  -- B's message writes byte x with 2; it is the last write to x
  obtain ⟨mB', hmB', hpaB, hdB⟩ := st_msg hwf (by rw [← qS_writer (hQ 1) heB hetB]; exact heB)
  simp only [Nat.add_sub_cancel] at hmB'
  rw [hmB] at hmB'; cases hmB'
  have hcovB : (mB.byteAt (X : Int)) = some 2 := byteAt_some_of hpaB hdB (by decide)
  have hl := finalMem_b0 hf (by decide)
  have hlt := last_order hl (by decide) hmA (by rw [hbA]; rfl) (by rw [hbA]; decide) (j := kB) (fun k m hm hc hv => by
    obtain ⟨h, hh, e, he, het, hlw⟩ := writer_cases hpart hwf 3 hout hm
    match h, hh with
    | 0, _ =>
      rw [qS_writer (hQ 0) he het] at hlw
      obtain ⟨hpa, hd⟩ := lw_st hlw; rw [byteAt_some_of hpa hd (v := 1) (by decide)] at hv; cases hv
    | 1, _ => have := qS_uniq (hQ 1) he het heB hetB; omega
    | 2, _ =>
      rcases q1_cases (hQ 2) with hev' | ⟨e', hev', ⟨_, rfl, _⟩, _⟩
      · rw [hev'] at he; cases he
      · rw [hev', List.mem_singleton] at he; subst he; cases het)
  exact hsp hnc (kA + 1) 1 (kB + 1) 2 rfl (writesIn_of hmB (by rw [hcovB]; rfl) (by omega) (Nat.le_refl _))

end Weak.Prom.PF

#print axioms Weak.Prom.PF.lit_lrScSc
#print axioms Weak.Prom.PF.lit_mixSca
