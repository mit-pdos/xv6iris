/-
Weak/Prom: **E-b4 — the Iris layer** (stage E-b4; plan rev 7 §4 "the client state interpretation").

* `XX M γ σ` — THE STATE INTERPRETATION: `∃ S ls, ⌜Inv M σ S ls⌝` and half of every hart's record `ls h`; the hart
  owns the other half (`gl (γ h) (ls h)`).
* `xstep` — the only Iris reasoning a hart step needs: a pure step lemma about `Inv` becomes a ghost update.
* `agentX`, `finalX`, `inv_init` — the agent obligation (OwnBE4Agent.lean), the final extraction, the initial state.
* `wpX_alu` — the register-register ALU rule (`mv a5,a4`), a new rule over B-0's kit.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnBE4Steps6

namespace Weak.Prom.OB.E4

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Own (OSt upd upd_eq upd_ne agentStep authorAt fulO hstepO_pstep hstepO_quiet)
open Weak.Prom.Own.X (xOW XP xlit)
open Weak.Prom.OA (XI xOf xNext xStep xNext_q xNext_plain Lk Ct)
open Weak.Prom.PF (quietL qPost qPosts LPstep LPstep_wr instrR quiet_regWL pc_lt memEv Trace PEv)
open Weak.Prom.OA.E2 (noLd)
open Weak.Prom.OA.E4 (q7 img7 xs7)
open Weak.Prom.Ref (Instr two64 aluOp)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The initial state -/

def S0 : PS := ⟨1, .dead, some 0, 0, 0, fun _ => False, fun _ => False, fun _ => 0, fun _ _ => 0⟩
def l00 : Loc := ⟨1, .D0, 0, 0, none, 0, 0, false, false⟩
def lA0 : Loc := ⟨1, .W, 0, 0, none, 0, 0, false, false⟩
def ls0 : Nat → Loc := fun h => if h = 0 then l00 else lA0

theorem inv_init (M : List PMsg) : Inv M σT0 S0 ls0 := by
  refine ⟨fun a t ht => absurd ht notElemOfEmpty, .inl ⟨?_, ?_⟩⟩
  · constructor
    · intro t h; exact h.elim
    · intro t h; exact h.elim
    · intro t a h; exact h.elim
    · exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · exact .inl rfl
    · intro t m h1 h2; simp [σT0, S0] at h1 h2; omega
    · intro _; exact ⟨rfl, rfl⟩
    · intro e; cases e
    · intro h u e; rcases e with e | e <;> cases e
    · intro e; exact absurd rfl e
    · exact ⟨fun _ => Nat.le_refl _, fun e => (by rcases e with e | e <;> cases e), fun e => (by cases e)⟩
    · intro h u e; cases e
    · intro h u e; cases e
    · intro i hi e; rcases hi with rfl | rfl <;> cases e
    · intro e; cases e
    · intro h u e; rcases e with e | e <;> cases e
    · intro h ts t0 a1; exact absurd rfl a1
    · intro h t0 a1; exact absurd rfl a1
    · intro t m h1 h2; simp [σT0] at h2; omega
    · intro k hk; exact absurd rfl hk
    · intro i k hi hk; exact absurd rfl hk
    · refine ⟨rfl, ⟨Nat.le_refl _, by decide⟩, ⟨fun _ => rfl, fun _ => .inl rfl⟩, .inl (.inl rfl),
        fun e => (by rcases e with e | e <;> cases e), fun e => (by cases e), fun e => (by cases e),
        fun e => (by cases e), rfl⟩
    · intro i hi
      have e : ls0 i = lA0 := by simp [ls0]; omega
      rw [e]
      exact ⟨.inl rfl, .inl rfl, fun e => absurd rfl e, fun e => (by rcases e with e | e <;> cases e),
        fun e => absurd rfl e⟩
  · refine ⟨fun e h => (by cases h), fun _ => ⟨Weak.Prom.OA.E4.q7_noLd Weak.Prom.OA.E2.noLd_nil,
      Weak.Prom.OA.E4.q7_noLd Weak.Prom.OA.E2.noLd_nil⟩, fun i tvs hi hl => ?_⟩
    have e : ls0 i = lA0 := by simp [ls0]; omega
    rw [e] at hl; cases hl

/-! ## 2. The ghost bundle -/

section gf
open Iris COFE Auth HeapView

noncomputable def ebGF : BundledGFunctors := fun n =>
  match n with
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF CoPsetDisjL, by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨GhostVarF Loc, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

instance : WsatGpreS ebGF where
  inv := { τ := 0, transp := by unfold ebGF; rfl }
  enabled := { τ := 1, transp := by unfold ebGF; rfl }
  disabled := { τ := 2, transp := by unfold ebGF; rfl }

instance : LcGpreS ebGF where
  lc_elem := { τ := 3, transp := by unfold ebGF; rfl }

instance : InvGpreS ebGF where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance

instance : GhostVarG ebGF Loc where
  elemG := { τ := 4, transp := by unfold ebGF; rfl }

end gf

/-! ## 3. The state interpretation -/

section si

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF Loc]

/-- Half of a hart's record. -/
def gl (γ : GName) (l : Loc) : IProp GF := ghost_var γ (.own (1 : Qp).half) l

/-- **THE STATE INTERPRETATION**. -/
abbrev XX (M : List PMsg) (γ : Nat → GName) (σ : TSt (List Nat)) : IProp GF :=
  iprop(∃ S ls, ⌜Inv M σ S ls⌝ ∗ gl (γ 0) (ls 0) ∗ gl (γ 1) (ls 1) ∗ gl (γ 2) (ls 2))

/-- **THE STEP**: a pure step lemma about `Inv` is a ghost update of the hart's record. -/
theorem xstep {M : List PMsg} {γ : Nat → GName} {σ σ' : TSt (List Nat)} {h : Nat} (hh : h < 3) {l : Loc}
    {Q : Loc → Prop} (hs : ∀ S ls, Inv M σ S ls → ls h = l → ∃ S' l', Q l' ∧ Inv M σ' S' (upd ls h l')) [InvGS_gen hlc GF] :
    ⊢ XX M γ σ -∗ gl (γ h) l -∗ |={⊤}=> ∃ l', ⌜Q l'⌝ ∗ XX (GF := GF) M γ σ' ∗ gl (γ h) l' := by
  iintro ⟨%S, %ls, %hI, H0, H1, H2⟩ Hl
  unfold gl
  rcases (by omega : h = 0 ∨ h = 1 ∨ h = 2) with rfl | rfl | rfl
  · ihave %e := ghost_var_agree (γ 0) _ _ _ _ $$ Hl H0
    obtain ⟨S', l', hq, hI'⟩ := hs S ls hI e.symm
    imod ghost_var_update_halves l' (γ 0) _ _ $$ Hl H0 with ⟨Hl, H0⟩
    imodintro
    iexists l'
    isplitr
    · ipureintro; exact hq
    isplitl [H0 H1 H2]
    · iexists S', upd ls 0 l'
      rw [upd_eq, upd_ne _ _ (by decide : (1 : Nat) ≠ 0), upd_ne _ _ (by decide : (2 : Nat) ≠ 0)]
      unfold gl; iframe; ipureintro; exact hI'
    · iexact Hl
  · ihave %e := ghost_var_agree (γ 1) _ _ _ _ $$ Hl H1
    obtain ⟨S', l', hq, hI'⟩ := hs S ls hI e.symm
    imod ghost_var_update_halves l' (γ 1) _ _ $$ Hl H1 with ⟨Hl, H1⟩
    imodintro
    iexists l'
    isplitr
    · ipureintro; exact hq
    isplitl [H0 H1 H2]
    · iexists S', upd ls 1 l'
      rw [upd_eq, upd_ne _ _ (by decide : (0 : Nat) ≠ 1), upd_ne _ _ (by decide : (2 : Nat) ≠ 1)]
      unfold gl; iframe; ipureintro; exact hI'
    · iexact Hl
  · ihave %e := ghost_var_agree (γ 2) _ _ _ _ $$ Hl H2
    obtain ⟨S', l', hq, hI'⟩ := hs S ls hI e.symm
    imod ghost_var_update_halves l' (γ 2) _ _ $$ Hl H2 with ⟨Hl, H2⟩
    imodintro
    iexists l'
    isplitr
    · ipureintro; exact hq
    isplitl [H0 H1 H2]
    · iexists S', upd ls 2 l'
      rw [upd_eq, upd_ne _ _ (by decide : (0 : Nat) ≠ 2), upd_ne _ _ (by decide : (1 : Nat) ≠ 2)]
      unfold gl; iframe; ipureintro; exact hI'
    · iexact Hl

/-- A step that keeps the hart's record. -/
theorem xstepS {M : List PMsg} {γ : Nat → GName} {σ σ' : TSt (List Nat)} {h : Nat} (hh : h < 3) {l : Loc}
    (hs : ∀ S ls, Inv M σ S ls → ls h = l → ∃ S', Inv M σ' S' ls) [InvGS_gen hlc GF] :
    ⊢ XX M γ σ -∗ gl (γ h) l -∗ |={⊤}=> XX (GF := GF) M γ σ' ∗ gl (γ h) l := by
  iintro HX Hl
  imod xstep (hlc := hlc) (GF := GF) (σ' := σ') (Q := fun l' => l' = l) hh (fun S ls hI hl => by
    obtain ⟨S', hI'⟩ := hs S ls hI hl
    exact ⟨S', l, rfl, by rw [← hl, upd_same]; exact hI'⟩) $$ HX Hl with ⟨%l', %e, HX, Hl⟩
  subst e
  imodintro; iframe

/-- **THE AGENT OBLIGATION** in Iris. -/
theorem agentX {M : List PMsg} {γ : Nat → GName} [InvGS_gen hlc GF] :
    ⊢ □ (∀ σ o', ⌜agentStep (xOW xs7 img7 M) σ.o o'⌝ -∗ XX (GF := GF) M γ σ -∗ |={⊤}=> XX M γ ⟨o', σ.tr⟩) := by
  iintro !>
  iintro %σ %o' %ha ⟨%S, %ls, %hI, H0, H1, H2⟩
  obtain ⟨S', hI'⟩ := agentOk hI ha
  imodintro
  iexists S', ls
  iframe; ipureintro; exact hI'

/-- **THE FINAL EXTRACTION**. -/
theorem finalX {M : List PMsg} {γ : Nat → GName} [InvGS_gen hlc GF] :
    ⊢ ∀ σ, ⌜σ.o.n = M.length ∧ ∀ h, σ.o.pr h = ∅⌝ -∗ XX (GF := GF) M γ σ -∗
      |={⊤,∅}=> ⌜∀ h, h < 3 → q7 M (σ.tr h)⌝ := by
  iintro %σ %hf ⟨%S, %ls, %hI, -, -, -⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro _
  ipureintro
  exact inv_final hI hf.2

end si

/-! ## 4. A new kit rule -/

section alu

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF]
variable {Xs : List (List XI)} {X' : TSt (List Nat) → IProp GF} {img : Image} {M : List PMsg} {h : Nat}

/-- **REGISTER-REGISTER ALU instruction** `op rd, rs1, rs2` (`mv a5,a4` = `add a5,x0,a4`), `rd ≠ x0`. -/
theorem wpX_alu {s : LP} {op : Weak.Prom.Ref.Alu} {rd rs1 rs2 : Nat} {ws : PState} (hq : s.q = []) (hpl : XP Xs s)
    (hp : s.prog[s.pc]? = some (.alu op rd rs1 rs2)) (hrd : rd ≠ 0) :
    (∀ s', ⌜LPstep s s' (s.pc + 1) rd (aluOp op (s.rd rs1) (s.rd rs2))⌝ -∗
        wpX (hlc := hlc) Xs X' img M h s' (instrR (PF.regWP ws rd (srcR rs1 ++ srcR rs2))))
    ⊢ wpX Xs X' img M h s ws := by
  iintro Hk
  iapply (wpX_quietI (fun l s' hs => Weak.Prom.PF.litNext_alu hq hp hrd (xlit hq hpl hs)) rfl (by simp [quietL]) rfl)
  simp only [qPosts, qPost]
  iapply Hk
  ipureintro
  exact LPstep_wr s rd _ _

end alu

end Weak.Prom.OB.E4
