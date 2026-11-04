/-
Weak/Prom: **G4 target (4) on track (a): free mode walks hart 1's text** (stage S4a part 4; S4a part 2's FREE MODE,
OwnAWp.lean `dfree`: after a DEAD read every later fulfil of a non-dead message is free).

`p4h_free`: from any `pc ∈ 1..14` with the address registers, `a4 = 1`, and `a5 = 1` at the two AMOs, hart 1 runs
the rest of its text in free mode: each fulfil hands back `fulT` through `dfree` and its message's class (an L1 AMO
write, an L2 AMO write, a field store, an L2 release — never dead), each obligation is discharged by `dshot`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAPipeLib

namespace Weak.Prom.OA.P

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y Z)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-- The postcondition. -/
abbrev Φ4 {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] (g : AGN) (M : List PMsg) :
    Unit → IProp GF := fun _ => iprop(⌜∃ V, grd Proto.triv img4 M V True⌝ ∨ dshot g)

/-- The states free mode walks. -/
def frS4 (s : LP) : Prop :=
  s.prog = b4h ∧ s.q = [] ∧ 1 ≤ s.pc ∧ s.pc ≤ 14 ∧ s.rd 9 = X ∧ s.rd 11 = Y ∧ s.rd 12 = Z ∧ s.rd 14 = 1 ∧
    s.regs.length = 32 ∧ (s.pc = 2 ∨ s.pc = 6 → s.rd 15 = 1)

theorem alg_L1 {s : LP} (h : s.rd 12 = Z) : aligned (s.rd 12) 4 = true := by rw [h]; decide
theorem alg_L2 {s : LP} (h : s.rd 9 = X) : aligned (s.rd 9) 4 = true := by rw [h]; decide

theorem amo_msg1 {s : LP} {tvs : List (Nat × BitVec 8)} (h15 : s.rd 15 = 1) :
    amoD .swap 4 (s.rd 15) tvs = toBytes 1 4 := by rw [amoD_swap, h15]

/-- `mv a5,a4` with `a4 = 1` sets `a5 = 1`. -/
theorem mv_15 {s s' : LP} {pc : Nat} (h : LPstep s s' pc 15 (Weak.Prom.Ref.aluOp .add (s.rd 0) (s.rd 14))) (h14 : s.rd 14 = 1)
    (hl : s.regs.length = 32) : s'.rd 15 = 1 := by
  have e := LPstep_rd_eq h (by decide) (by omega)
  have h0 : s.rd 0 = 0 := rfl
  rw [e, h0, h14]; decide

section free

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]

/-- **FREE MODE RUNS THE REST OF HART 1's TEXT** (see the header). -/
theorem p4h_free (g : AGN) (M : List PMsg) (hdd : g.dd = dd4 M) :
    ⊢ ∀ (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace), ⌜frS4 s⌝ -∗ dfree (GF := GF) g -∗ dshot g -∗
      lhA g Proto.triv (w4 M 1) (qs4 1) ws pr ev -∗ wpKA g Proto.triv (w4 M 1) qs4 s (Φ4 g M) := by
  have hw := litW_x xs4 img4 M 1
  iloeb as IH
  iintro %s %ws %pr %ev %hs #Hf #Hd Hl
  obtain ⟨hprog, hq, hpc1, hpc14, h9, h11, h12, h14, hlen, h15⟩ := hs
  have hX := p4h_at hprog
  have hpc : s.pc = 1 ∨ s.pc = 2 ∨ s.pc = 3 ∨ s.pc = 4 ∨ s.pc = 5 ∨ s.pc = 6 ∨ s.pc = 7 ∨ s.pc = 8 ∨
      s.pc = 9 ∨ s.pc = 10 ∨ s.pc = 11 ∨ s.pc = 12 ∨ s.pc = 13 ∨ s.pc = 14 := by omega
  have hfr : ∀ s' : LP, ∀ pc rd v, LPstep s s' pc rd v → rd ≠ 9 → rd ≠ 11 → rd ≠ 12 → rd ≠ 14 → 1 ≤ pc →
      pc ≤ 14 → (pc = 2 ∨ pc = 6 → s'.rd 15 = 1) → frS4 s' :=
    fun s' pc rd v hs h1 h2 h3 h4 h5 h6 h7 =>
      ⟨hs.1.trans hprog, hs.2.2.1, by rw [hs.2.1]; exact h5, by rw [hs.2.1]; exact h6,
        by rw [LPstep_rd hs 9 (.inl (Ne.symm h1)), h9], by rw [LPstep_rd hs 11 (.inl (Ne.symm h2)), h11],
        by rw [LPstep_rd hs 12 (.inl (Ne.symm h3)), h12], by rw [LPstep_rd hs 14 (.inl (Ne.symm h4)), h14],
        hs.2.2.2.1.trans hlen, by rw [hs.2.1]; exact h7⟩
  rcases hpc with hpc | hpc | hpc | hpc | hpc | hpc | hpc | hpc | hpc | hpc | hpc | hpc | hpc | hpc
  · -- `mv a5,a4`
    iapply (C.wpKA_alu hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (by decide))
    iframe Hl
    inext
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by decide) (by decide) (by omega)
      (by omega) (fun _ => mv_15 hs' h14 hlen)) Hf Hd Hl
  · -- `amoswap.w.aq a5,a5,(a2)`
    iapply (wpKA_amo (base := L1) hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
      (alg_L1 h12) (by rw [h12]))
    iframe Hl
    inext
    iintro %tvs %ts %_ %_ %hmsg %_ %_ %_ %_ _ _
    rw [amo_msg1 (h15 (.inl hpc))] at hmsg
    imodintro
    isplitr
    · iright; iexact Hd
    isplitr
    · unfold fulT; iright; iframe Hf; ipureintro
      rw [hdd]; exact notDd_of hmsg (by rw [kind_a1]; decide)
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by decide) (by decide) (by omega)
      (by omega) (fun h => by omega)) Hf Hd Hl
  · -- `sext.w a5,a5`
    iapply (wpKA_addiw (Xs := xs4) hw (xAg_x xs4 img4 M 1 s) hq hX (by rw [hpc]; rfl) (by decide))
    iframe Hl
    inext
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by decide) (by decide) (by omega)
      (by omega) (fun h => by omega)) Hf Hd Hl
  · -- `bnez a5,1`
    iapply (wpKA_brx (Xs := xs4) hw (xAg_x xs4 img4 M 1 s) hq hX (by rw [hpc]; rfl) (by rw [hprog]; decide))
    iframe Hl
    inext
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by decide) (by decide)
      (by split <;> omega) (by split <;> omega) (fun h => absurd h (by split <;> omega))) Hf Hd Hl
  · -- `mv a5,a4`
    iapply (C.wpKA_alu hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (by decide))
    iframe Hl
    inext
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by decide) (by decide) (by omega)
      (by omega) (fun _ => mv_15 hs' h14 hlen)) Hf Hd Hl
  · -- `amoswap.w.aq a5,a5,(s1)`
    iapply (wpKA_amo (base := Lk) hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
      (alg_L2 h9) (by rw [h9]))
    iframe Hl
    inext
    iintro %tvs %ts %_ %_ %hmsg %_ %_ %_ %_ _ _
    rw [amo_msg1 (h15 (.inr hpc))] at hmsg
    imodintro
    isplitr
    · iright; iexact Hd
    isplitr
    · unfold fulT; iright; iframe Hf; ipureintro
      rw [hdd]; exact notDd_of hmsg (by rw [kind_a2]; decide)
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by decide) (by decide) (by omega)
      (by omega) (fun h => by omega)) Hf Hd Hl
  · -- `sext.w a5,a5`
    iapply (wpKA_addiw (Xs := xs4) hw (xAg_x xs4 img4 M 1 s) hq hX (by rw [hpc]; rfl) (by decide))
    iframe Hl
    inext
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by decide) (by decide) (by omega)
      (by omega) (fun h => by omega)) Hf Hd Hl
  · -- `bnez a5,5`
    iapply (wpKA_brx (Xs := xs4) hw (xAg_x xs4 img4 M 1 s) hq hX (by rw [hpc]; rfl) (by rw [hprog]; decide))
    iframe Hl
    inext
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by decide) (by decide)
      (by split <;> omega) (by split <;> omega) (fun h => absurd h (by split <;> omega))) Hf Hd Hl
  · -- `ld t2,(a1)`
    iapply (wpKA_ld (sz := 8) (sgn := true) (rd := 7) (rs1 := 11) (off := 0) (base := Ct) hw
      (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_of h11 (by decide) (by decide))
      (base_of h11 (by decide)))
    iframe Hl
    inext
    iintro %tvs %_ %_ _ _
    imodintro
    isplitr
    · iright; iexact Hd
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by decide) (by decide) (by omega)
      (by omega) (fun h => by omega)) Hf Hd Hl
  · -- `addi t2,t2,1`
    iapply (wpKA_alui hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (by decide))
    iframe Hl
    inext
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by decide) (by decide) (by omega)
      (by omega) (fun h => by omega)) Hf Hd Hl
  · -- `sd t2,(a1)`
    iapply (wpKA_sw (sz := 8) (rs2 := 7) (rs1 := 11) (off := 0) (base := Ct) hw
      (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_of h11 (by decide) (by decide))
      (base_of h11 (by decide)))
    iframe Hl
    inext
    iintro %ts %_ %hmsg %_ %_ _ _
    imodintro
    isplitr
    · iright; iexact Hd
    isplitr
    · unfold fulT; iright; iframe Hf; ipureintro
      rw [hdd]; exact notDd_of hmsg (by rw [kind_cm (toBytes_length _ _) (by exact (by decide : 1 < 2))]; decide)
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by decide) (by decide) (by omega)
      (by omega) (fun h => by omega)) Hf Hd Hl
  · -- `fence rw,w`
    iapply (wpKA_fence hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl))
    iframe Hl
    inext
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by decide) (by decide) (by omega)
      (by omega) (fun h => by omega)) Hf Hd Hl
  · -- `sw zero,0(s1)`
    iapply (wpKA_sw (sz := 4) (rs2 := 0) (rs1 := 9) (off := 0) (base := Lk) hw
      (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_of h9 (by decide) (by decide))
      (base_of h9 (by decide)))
    iframe Hl
    inext
    iintro %ts %_ %hmsg %_ %_ _ _
    imodintro
    isplitr
    · iright; iexact Hd
    isplitr
    · unfold fulT; iright; iframe Hf; ipureintro
      rw [hdd]; exact notDd_of hmsg (by rw [show toBytes (s.rd 0) 4 = toBytes 0 4 from rfl, kind_r2]; decide)
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by decide) (by decide) (by omega)
      (by omega) (fun h => by omega)) Hf Hd Hl
  · -- the end
    have hend : s.prog.length ≤ s.pc := by rw [hprog, hpc]; decide
    iapply (wpKA_end (v := ()) (litAg_xn hq (fun x hx => by rw [hX, hpc] at hx; cases hx)) hq hend
      (by show litDone s = some (); unfold litDone; rw [if_pos ⟨hq, hend⟩]))
    iframe Hl
    imodintro
    iright; iexact Hd

end free

end Weak.Prom.OA.P
