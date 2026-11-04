/-
Weak/Prom: **G4 target (1c) on track (a): the register-register ALU rule, the text's helpers and FREE MODE**
(stage S4a part 3; plan rev 7 §4 G4 (1c); OwnAWp.lean `dfree`, `fulT`).

* `wpKA_alu` — `op rd, rs1, rs2` (xv6's `mv a5,a4` is `c.mv` = `add a5,x0,a4`): `LRegW rd (rs1 ++ rs2)`, `LInstr`
  (MachLitmus.lean's table; `litNext_alu`).
* `lk_free1c` — once the run is doomed by a DEAD witness, free mode walks the rest of (1c)'s text: every fulfil is of
  a lock message (the AMO's `excl` write, the release's `plain` `sw`), a cpu-field message or a counter message,
  none of which is dead (OwnALock1cDefs.lean).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnALock1cLib

namespace Weak.Prom.OA.C

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp)
open Weak.Prom.Ref.Lit (X Y)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

section kit

variable {V : Type} {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [InvGS_gen hlc GF]
variable {g : AGN} {π : Proto} {w : HW LP Unit V} {Qs : Nat → Trace → Prop} {Φ : V → IProp GF}

/-- **REGISTER-REGISTER ALU instruction** `op rd, rs1, rs2` (`rd ≠ x0`; `mv rd, rs` = `c.mv` = `add rd, x0, rs`):
`LRegW rd (rs1 ++ rs2)`, `LInstr` (the last with a fupd at its pre-state's frontier). -/
theorem wpKA_alu (hw : LitW w) {s : LP} {op : Weak.Prom.Ref.Alu} {rd rs1 rs2 : Nat} {ws : PState} {pr : GSet Nat}
    {ev : Trace} (hag : LitAg w s) (hq : s.q = []) (hp : s.prog[s.pc]? = some (.alu op rd rs1 rs2)) (hrd : rd ≠ 0) :
    lhA g π w (Qs w.h) ws pr ev ∗
    ▷ (∀ s', ⌜LPstep s s' (s.pc + 1) rd (aluOp op (s.rd rs1) (s.rd rs2))⌝ -∗
        frontA g π w.img w.M (regWP ws rd (srcR rs1 ++ srcR rs2)) -∗
        £ 1 -∗ |={⊤}=> (lhA g π w (Qs w.h) (instrR (regWP ws rd (srcR rs1 ++ srcR rs2))) pr ev -∗
          wpKA g π w Qs s' Φ))
    ⊢ wpKA g π w Qs s Φ := by
  iintro ⟨Hl, Hk⟩
  iapply (wpKA_q1 (k := { s with regs := s.wr rd (aluOp op (s.rd rs1) (s.rd rs2)), pc := s.pc + 1, q := [LInstr] })
    (l0 := LRegW rd (srcR rs1 ++ srcR rs2)) (ws1 := regWP ws rd (srcR rs1 ++ srcR rs2)) rfl
    (hw.2 s (.inr (pc_lt hp)))
    (fun l s' hs => litNext_alu hq hp hrd ((hag l s').1 hs)) rfl)
  iframe Hl
  inext
  iintro _ _
  imodintro
  iintro Hl
  iapply (wpKA_drainA hw [LInstr] _
    { s with regs := s.wr rd (aluOp op (s.rd rs1) (s.rd rs2)), pc := s.pc + 1, q := [] }
    _ (by simp) (by simp [quietL]) rfl rfl)
  iframe Hl
  inext
  simp only [List.dropLast, qPosts, qPost]
  iintro Hf Hc
  iapply Hk $$ %_ %(LPstep_wr s rd _ _) Hf Hc

end kit

/-! ## Helpers -/

theorem alg_pc {s : LP} (h : s.rd 9 = X) : aligned ((s.rd 9 + 16) % two64) 8 = true := by rw [h]; decide

theorem base_pc {s : LP} (h : s.rd 9 = X) : (((s.rd 9 + 16) % two64 : Nat) : Int) = Pc := by rw [h]; decide

/-- A store entry away from the counter is no counter entry. -/
theorem st_nonC {b : Int} (hb : b ≠ Ct) (d : List (BitVec 8)) (a c : List Dsrc) (ts : Nat) :
    (∀ tv, ¬ isCLd (LStore false false b d a c, some ts) tv) ∧
      (∀ t, ¬ isCSt (LStore false false b d a c, some ts) t) := by
  refine ⟨fun _ ⟨_, h⟩ => ?_, fun _ ⟨_, _, _, h⟩ => ?_⟩
  · cases h
  · injection h with h1 _
    injection h1 with _ _ h3
    exact hb h3

theorem Pc_ne_Ct : Pc ≠ Ct := by simp [Pc, Lk, Ct, X, Y]
theorem Lk_ne_Ct : Lk ≠ Ct := by simp [Lk, Ct, X, Y]

/-- The program states free mode walks: the text, nothing queued, `pc ∈ 1..12`, the address registers. -/
def frS1c (s : LP) : Prop :=
  s.prog = b1c ∧ s.q = [] ∧ 1 ≤ s.pc ∧ s.pc ≤ 12 ∧ s.rd 9 = X ∧ s.rd 11 = Y

section free

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- **FREE MODE RUNS THE REST OF (1c)'s TEXT** (see the header). -/
theorem lk_free1c (g : AGN) (M : List PMsg) (h : Nat) (hh : h < 2) (hdd : g.dd = ddL M) :
    ⊢ ∀ (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace), ⌜frS1c s⌝ -∗ dfree (GF := GF) g -∗ dshot g -∗
      lhA g Proto.triv (wL1c M h) (qsLk M h) ws pr ev -∗ wpKA g Proto.triv (wL1c M h) (qsLk M) s (ΦL g M) := by
  have hw := litW_x xs1c imgL M h
  iloeb as IH
  iintro %s %ws %pr %ev %hs #Hf #Hd Hl
  obtain ⟨hprog, hq, hpc1, hpc12, h9, h11⟩ := hs
  have hX := p1c_at hprog
  have hpc : s.pc = 1 ∨ s.pc = 2 ∨ s.pc = 3 ∨ s.pc = 4 ∨ s.pc = 5 ∨ s.pc = 6 ∨ s.pc = 7 ∨ s.pc = 8 ∨
      s.pc = 9 ∨ s.pc = 10 ∨ s.pc = 11 ∨ s.pc = 12 := by omega
  have hfr : ∀ s' : LP, ∀ pc rd v, LPstep s s' pc rd v → rd ≠ 9 → rd ≠ 11 → 1 ≤ pc → pc ≤ 12 → frS1c s' :=
    fun s' pc rd v hs h1 h2 h3 h4 =>
      ⟨hs.1.trans hprog, hs.2.2.1, by rw [hs.2.1]; exact h3, by rw [hs.2.1]; exact h4,
        by rw [LPstep_rd hs 9 (.inl (Ne.symm h1)), h9], by rw [LPstep_rd hs 11 (.inl (Ne.symm h2)), h11]⟩
  rcases hpc with hpc | hpc | hpc | hpc | hpc | hpc | hpc | hpc | hpc | hpc | hpc | hpc
  · -- `mv a5,a4`
    iapply (wpKA_alu hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (by decide))
    iframe Hl
    inext
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by omega) (by omega)) Hf Hd Hl
  · -- `amoswap.w.aq a5,a5,(s1)`
    iapply (wpKA_amo (base := Lk) hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
      (by rw [h9]; decide) (by rw [h9]))
    iframe Hl
    inext
    iintro %tvs %ts %_ %_ %hmsg %_ %_ %_ %_ _ _
    imodintro
    isplitr
    · iright; iexact Hd
    isplitr
    · unfold fulT; iright; iframe Hf; ipureintro
      rw [hdd]; exact lm_notDd hh (by rw [amoD_swap]; exact toBytes_length _ _) (.inl rfl) hmsg
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by omega) (by omega)) Hf Hd Hl
  · -- `sext.w a5,a5`
    iapply (wpKA_addiw (Xs := xs1c) hw (xAg_x xs1c imgL M h s) hq hX (by rw [hpc]; rfl) (by decide))
    iframe Hl
    inext
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by omega) (by omega)) Hf Hd Hl
  · -- `bnez a5, again`
    iapply (wpKA_brx (Xs := xs1c) hw (xAg_x xs1c imgL M h s) hq hX (by rw [hpc]; rfl) (by rw [hprog]; decide))
    iframe Hl
    inext
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by split <;> omega)
      (by split <;> omega)) Hf Hd Hl
  · -- `sd a0,16(s1)`
    iapply (wpKA_sw (sz := 8) (rs2 := 10) (rs1 := 9) (off := 16) (base := Pc) hw
      (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_pc h9) (base_pc h9))
    iframe Hl
    inext
    iintro %ts %_ %hmsg %_ %_ _ _
    imodintro
    isplitr
    · iright; iexact Hd
    isplitr
    · unfold fulT; iright; iframe Hf; ipureintro
      rw [hdd]; exact pm_notDd hh (toBytes_length _ _) hmsg
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by omega) (by omega)) Hf Hd Hl
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
  · -- `sd zero,16(s1)`
    iapply (wpKA_sw (sz := 8) (rs2 := 0) (rs1 := 9) (off := 16) (base := Pc) hw
      (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_pc h9) (base_pc h9))
    iframe Hl
    inext
    iintro %ts %_ %hmsg %_ %_ _ _
    imodintro
    isplitr
    · iright; iexact Hd
    isplitr
    · unfold fulT; iright; iframe Hf; ipureintro
      rw [hdd]; exact pm_notDd hh (toBytes_length _ _) hmsg
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by omega) (by omega)) Hf Hd Hl
  · -- `fence rw,w`
    iapply (wpKA_fence hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl))
    iframe Hl
    inext
    iintro %s' %hs' _ _
    imodintro
    iintro Hl
    iapply IH $$ %s' %_ %_ %_ %(hfr s' _ _ _ hs' (by decide) (by decide) (by omega) (by omega)) Hf Hd Hl
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
      rw [hdd]; exact lm_notDd hh (toBytes_length _ _) (.inr rfl) hmsg
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

end Weak.Prom.OA.C
