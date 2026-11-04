/-
Weak/Prom: **G4 target (1a) on track (a): FREE MODE runs the rest of the text** (stage S4a part 2; OwnAWp.lean
`dfree`, `fulT`).

Once the run is doomed by a DEAD witness (free mode), every remaining obligation of the hart is discharged by
`dshot`, and every fulfil by `dfree` and the fact that the text only writes LOCK messages (4 bytes at `Lk`, `excl`)
and COUNTER messages (8 bytes at `Ct`, `plain`), which are not dead (OwnALockDefs.lean).  `lk_free` walks the whole
loop (Löb induction over the program states with `pc ∈ 1..7`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnALockLib
import Weak.Prom.MachNota

namespace Weak.Prom.OA

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-- The image of the test (every byte 0). -/
abbrev imgL : Image := testImg t1a

theorem imgL_zero (a : Int) : imgL a = some 0 := by
  simp [imgL, testImg, Test.imgF, t1a, bv8]

/-- Hart `h`'s world. -/
abbrev wL (M : List PMsg) (h : Nat) : HW LP Unit Unit := xW xs1a imgL M h

/-- The postcondition. -/
abbrev ΦL {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] (g : AGN) (M : List PMsg) :
    Unit → IProp GF := fun _ => iprop(⌜∃ V, grd Proto.triv imgL M V True⌝ ∨ dshot g)

/-- A lock message written by the text is not dead. -/
theorem lm_notDd {M : List PMsg} {ts h : Nat} {d : List (BitVec 8)} (hh : h < 2) (hd : d.length = 4)
    (hm : M[ts - 1]? = some ⟨Lk, d, some h, .excl⟩) : ¬ (1 ≤ ts ∧ isDd M ts = true) := by
  rintro ⟨h1, hD⟩
  have hmt : msgAt M ts = some ⟨Lk, d, some h, .excl⟩ := by
    obtain ⟨k, rfl⟩ : ∃ k, ts = k + 1 := ⟨ts - 1, by omega⟩
    simpa [msgAt] using hm
  have : isL M ts = true := by
    rw [isL, clsB_of hmt]; simp only [decide_eq_true_eq]
    refine ⟨rfl, hd, rfl, ?_⟩
    simp only [Option.some.injEq]; omega
  simp [isDd, this] at hD

/-- A counter message written by the text is not dead. -/
theorem cm_notDd {M : List PMsg} {ts h : Nat} {d : List (BitVec 8)} (hh : h < 2) (hd : d.length = 8)
    (hm : M[ts - 1]? = some ⟨Ct, d, some h, .plain⟩) : ¬ (1 ≤ ts ∧ isDd M ts = true) := by
  rintro ⟨h1, hD⟩
  have hmt : msgAt M ts = some ⟨Ct, d, some h, .plain⟩ := by
    obtain ⟨k, rfl⟩ : ∃ k, ts = k + 1 := ⟨ts - 1, by omega⟩
    simpa [msgAt] using hm
  have : isC M ts = true := by
    rw [isC, clsB_of hmt]; simp only [decide_eq_true_eq]
    refine ⟨rfl, hd, rfl, ?_⟩
    simp only [Option.some.injEq]; omega
  simp [isDd, this] at hD

/-- The dead predicate of the spinlock tests (timestamp `0` is the image, never a witness). -/
def ddL (M : List PMsg) (t : Nat) : Prop := 1 ≤ t ∧ isDd M t = true

/-- The program states free mode walks: the text, nothing queued, `pc ∈ 1..7`, the address registers. -/
def frS (s : LP) : Prop :=
  s.prog = b1a ∧ s.q = [] ∧ 1 ≤ s.pc ∧ s.pc ≤ 7 ∧ s.rd 10 = X ∧ s.rd 11 = Y

theorem p1a_at {s : LP} (h : s.prog = b1a) : xOf xs1a s.prog = some p1a := by rw [h]; exact xOf_1a

section free

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- **FREE MODE RUNS THE REST OF THE TEXT** (see the header). -/
theorem lk_free (g : AGN) (M : List PMsg) (h : Nat) (hh : h < 2) (hdd : g.dd = ddL M) :
    ⊢ ∀ (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace), ⌜frS s⌝ -∗ dfree (GF := GF) g -∗ dshot g -∗
      lhA g Proto.triv (wL M h) (qsLk M h) ws pr ev -∗ wpKA g Proto.triv (wL M h) (qsLk M) s (ΦL g M) := by
  have hw := litW_x xs1a imgL M h
  iloeb as IH
  iintro %s %ws %pr %ev %hs #Hf #Hd Hl
  obtain ⟨hprog, hq, hpc1, hpc7, h10, h11⟩ := hs
  have hX := p1a_at hprog
  have hpc : s.pc = 1 ∨ s.pc = 2 ∨ s.pc = 3 ∨ s.pc = 4 ∨ s.pc = 5 ∨ s.pc = 6 ∨ s.pc = 7 := by omega
  have hfr : ∀ s' : LP, ∀ pc rd v, LPstep s s' pc rd v → rd ≠ 10 → rd ≠ 11 → 1 ≤ pc → pc ≤ 7 → frS s' :=
    fun s' pc rd v hs h1 h2 h3 h4 =>
      ⟨hs.1.trans hprog, hs.2.2.1, by rw [hs.2.1]; exact h3, by rw [hs.2.1]; exact h4,
        by rw [LPstep_rd hs 10 (.inl (Ne.symm h1)), h10], by rw [LPstep_rd hs 11 (.inl (Ne.symm h2)), h11]⟩
  rcases hpc with hpc | hpc | hpc | hpc | hpc | hpc | hpc
  · -- `amoswap.w.aq t0,t0,(a0)`
    iapply (wpKA_amo (base := Lk) hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
      (by rw [h10]; decide) (by rw [h10]))
    iframe Hl
    inext
    iintro %tvs %ts %_ %_ %hmsg %_ %_ %_ %_ _ _
    imodintro
    isplitr
    · iright; iexact Hd
    isplitr
    · unfold fulT; iright; iframe Hf; ipureintro
      rw [hdd]; exact lm_notDd hh (by rw [amoD_swap]; exact toBytes_length _ _) hmsg
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by omega) (by omega)) Hf Hd Hl
  · -- `bnez t0, again`
    iapply (wpKA_brx (Xs := xs1a) hw (xAg_x xs1a imgL M h s) hq hX (by rw [hpc]; rfl) (by rw [hprog]; decide))
    iframe Hl
    inext
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by split <;> omega)
      (by split <;> omega)) Hf Hd Hl
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
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by omega) (by omega)) Hf Hd Hl
  · -- `addi t2,t2,1`
    iapply (wpKA_alui hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (by decide))
    iframe Hl
    inext
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by omega) (by omega)) Hf Hd Hl
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
      rw [hdd]; exact cm_notDd hh (toBytes_length _ _) hmsg
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by omega) (by omega)) Hf Hd Hl
  · -- `amoswap.w.rl x0,x0,(a0)`
    iapply (wpKA_amo (base := Lk) hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
      (by rw [h10]; decide) (by rw [h10]))
    iframe Hl
    inext
    iintro %tvs %ts %_ %_ %hmsg %_ %_ %_ %_ _ _
    imodintro
    isplitr
    · iright; iexact Hd
    isplitr
    · unfold fulT; iright; iframe Hf; ipureintro
      rw [hdd]; exact lm_notDd hh (by rw [amoD_swap]; exact toBytes_length _ _) hmsg
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by omega) (by omega)) Hf Hd Hl
  · -- the end
    have hend : s.prog.length ≤ s.pc := by rw [hprog, hpc]; decide
    iapply (wpKA_end (v := ()) (litAg_xn hq (fun x hx => by rw [hX, hpc] at hx; cases hx)) hq hend
      (by show litDone s = some (); unfold litDone; rw [if_pos ⟨hq, hend⟩]))
    iframe Hl
    imodintro
    iright; iexact Hd

end free

end Weak.Prom.OA
