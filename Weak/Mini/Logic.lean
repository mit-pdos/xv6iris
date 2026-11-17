/-
Weak/Mini: **MiniLogic — the weakest precondition over MiniMach** (mini plan rev 4 §2 L3; owner ruling [OWN.P18]:
"I still want the semantics and the logic. Just want them minimial").  The full stack's template is
`Weak/Prom/CoreWp.lean` (the ownership-free core, plan rev 7 §2), cut down to what F and the TRIVIAL PROTOCOL need:
no protocol family, no `Valid`, no guard `⟦V⟧`, no forward-bank knowledge, no promise set in the hart's state.

## The hart language (one iris-lean thread per hart)

The thread's expression is `HE.run w f`: the hart's front-end state `f` (pc, registers, queued labels) with its WORLD
`w` = (program, final log `M` — the prophecy parameter —, hart index); or `HE.ret f` once the hart is FINISHED
(`mDone`: nothing queued, no instruction at `pc`).  One primitive step (`hstep`) is ONE MiniMach state step of the
hart against the fixed final log `M`: a label its front end emits (`mNext`) with the memory half (`mMem`, for some
promise sets — the logic does not track promises: the partition is a machine fact, `Run.lean`); or the step to the
value when the hart is finished.  The language state is the hart's exact `(ws, τ)`: its memory state and its trace.
Promise steps are not hart steps.

## Resources and the state interpretation

* `hartSt γ ws τ`: one half of a ghost variable holding `(ws, τ)`.  The state interpretation `hartInterp` holds the
  other half and the TRACE INVARIANT `Ψ τ` (plan rev 7 §2 [R2.6] with the trivial protocol: no guard).
* Every step gives one `▷` and `£ 1` (`numLatersPerStep := 0`); stuckness is `MaybeStuck` (a store can only fulfil
  a message of `M`, so "can always step" is meaningless).
* `wpH γ w Ψ f Φ` is iris-lean's `WP` of the thread; `wp P M h Ψ f Φ` its closed form at the hart's initial memory
  state `msInit` and the empty trace, for every ghost name.
* `wpH_lift` is the ONE lifting lemma; every leaf rule (`Rules.lean`) is proved from it and never unfolds `WP`.
Imports: `Weak.Mini.Run` (→ `Mach`, `Prog`, `Val`) and iris-lean only (plan §2 import discipline).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.Run
import Iris.ProgramLogic.Lifting
import Iris.Instances.Lib.GhostVar

namespace Weak.Mini.Logic

open Weak.Mini Weak.Mini.Mach
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The hart language -/

/-- THE HART'S WORLD: the program, the final log (the prophecy `M`), the hart index. -/
structure HW where
  P : MProg
  M : List MMsg
  h : Nat

/-- A FINISHED hart: nothing queued and no instruction at `pc` (then `mNext` admits no label). -/
def mDone (P : MProg) (h : Nat) (f : MFront) : Prop := f.q = [] ∧ (P.prog h)[f.pc]? = none

/-- The thread expression: a running hart, or a finished hart with its final front-end state. -/
inductive HE where
  | run (w : HW) (f : MFront)
  | ret (f : MFront)

/-- The language state: the hart's exact memory state and its trace. -/
abbrev HSt : Type := MSt × Trace

/-- ONE HART STEP: one MiniMach state step against the final log, appending the trace entry; or the step to the
value of a finished hart. -/
inductive hstep : HE × HSt → List Unit → HE × HSt × List HE → Prop
  | lab (w : HW) (f : MFront) (ws : MSt) (τ : Trace) (l : MLab) (ots : Option Nat) (f' : MFront) (ws' : MSt)
      (pr pr' : List Nat) :
      mNext w.P w.h f l = some f' → mMem w.P w.M w.h pr ws l ots ws' pr' →
      hstep (.run w f, (ws, τ)) [] (.run w f', (ws', τ ++ [(l, ots)]), [])
  | fin (w : HW) (f : MFront) (σ : HSt) : mDone w.P w.h f → hstep (.run w f, σ) [] (.ret f, σ, [])

instance : PrimStep HE HSt (List Unit) := ⟨hstep⟩

/-- The value of an expression. -/
def HE.toV : HE → Option MFront
  | .ret f => some f
  | .run _ _ => none

instance : ToVal HE MFront where
  toVal := HE.toV
  ofVal f := .ret f
  coe_of_toVal_eq_some {e v} h := by
    cases e with
    | run => cases h
    | ret v' => cases h; rfl
  toVal_coe _ := rfl

instance : Language HE HSt Unit MFront where
  val_stuck h := by cases h <;> rfl

/-! ## 2. Resources, state interpretation, wp -/

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt]

/-- `hartSt γ ws τ`: the hart's exact memory state and trace (one half). -/
def hartSt (γ : GName) (ws : MSt) (τ : Trace) : IProp GF := ghost_var γ (.own (1 : Qp).half) ((ws, τ) : HSt)

/-- The state interpretation of hart `γ`'s thread: the other half and the trace invariant. -/
def hartInterp (γ : GName) (Ψ : Trace → Prop) (σ : HSt) : IProp GF :=
  iprop(ghost_var γ (.own (1 : Qp).half) σ ∗ ⌜Ψ σ.2⌝)

/-- The iris-lean `IrisGS` of one hart's thread: one `▷` and `£ 1` per step. -/
@[reducible] def hartGS [InvGS_gen hlc GF] (γ : GName) (Ψ : Trace → Prop) : IrisGS_gen hlc HE GF where
  toStateInterp := ⟨fun σ _ _ _ => hartInterp γ Ψ σ⟩
  invGS := inferInstance
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by iintro $

theorem stateI_eq [InvGS_gen hlc GF] (γ : GName) (Ψ : Trace → Prop) (σ : HSt) (ns : Nat) (obs : List Unit)
    (nt : Nat) : @stateInterp HSt Unit GF (hartGS (hlc := hlc) γ Ψ).toStateInterp σ ns obs nt = hartInterp γ Ψ σ :=
  rfl

/-- **`wpH γ w Ψ f Φ`**: the hart wp at front-end state `f` (iris-lean's `WP` of the thread). -/
def wpH [InvGS_gen hlc GF] (γ : GName) (w : HW) (Ψ : Trace → Prop) (f : MFront) (Φ : MFront → IProp GF) :
    IProp GF :=
  letI : IrisGS_gen hlc HE GF := hartGS γ Ψ
  WP (HE.run w f) @ Stuckness.MaybeStuck; ⊤ {{ Φ }}

/-- **`wp P M h Ψ f Φ`**: hart `h` of `P`, run against the final log `M` from front-end state `f`, the initial
memory state `msInit` and the empty trace, keeps `Ψ` of its trace at every step and, if it finishes in `f'`,
ends in `Φ f'`. -/
def wp [InvGS_gen hlc GF] (P : MProg) (M : List MMsg) (h : Nat) (Ψ : Trace → Prop) (f : MFront)
    (Φ : MFront → IProp GF) : IProp GF :=
  iprop(∀ (γ : GName), hartSt γ msInit [] -∗ wpH γ ⟨P, M, h⟩ Ψ f Φ)

/-! ## 3. The lifting lemma -/

section lift

variable [InvGS_gen hlc GF]

/-- **THE LIFTING LEMMA**: from `hartSt`, the hart may take any step its front end and the memory half allow
(one `▷`); on a label step the client is handed the trace invariant of the current trace, proves it of the new
trace and continues from the new `hartSt`; on the value step (a finished hart) it proves `Φ f`. -/
theorem wpH_lift {γ : GName} {w : HW} {Ψ : Trace → Prop} {f : MFront} {Φ : MFront → IProp GF} {ws : MSt}
    {τ : Trace} :
    hartSt γ ws τ ∗
    ▷ ((⌜mDone w.P w.h f⌝ -∗ hartSt γ ws τ -∗ |={⊤}=> Φ f) ∧
       (∀ l ots f' ws' pr pr', ⌜mNext w.P w.h f l = some f'⌝ -∗ ⌜mMem w.P w.M w.h pr ws l ots ws' pr'⌝ -∗
          ⌜Ψ τ⌝ -∗ |={⊤}=> ⌜Ψ (τ ++ [(l, ots)])⌝ ∗ (hartSt γ ws' (τ ++ [(l, ots)]) -∗ wpH γ w Ψ f' Φ)))
    ⊢ wpH γ w Ψ f Φ := by
  letI : IrisGS_gen hlc HE GF := hartGS γ Ψ
  show _ ⊢ WP (HE.run w f) @ Stuckness.MaybeStuck; ⊤ {{ Φ }}
  iintro ⟨Hst, Hk⟩
  iapply wp_lift_step (rfl : toVal (HE.run w f : HE) = none)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rw [stateI_eq]
  unfold hartInterp
  icases Hσ with ⟨Hγ, %Hf⟩
  unfold hartSt
  ihave %Heq := ghost_var_agree γ _ _ _ _ $$ Hγ Hst
  subst Heq
  iapply fupd_mask_intro Iris.Std.LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro; trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  change hstep _ _ _ at Hstep
  cases Hstep with
  | lab _ _ _ _ l ots f' ws' pr pr' hn hm =>
    icases Hk with ⟨-, Hk⟩
    imod Hclose
    imod Hk $$ %l %ots %f' %ws' %pr %pr' %hn %hm %Hf with ⟨%Hok, Hk⟩
    imod ghost_var_update_halves ((ws', τ ++ [(l, ots)]) : HSt) γ _ _ $$ Hγ Hst with ⟨Hγ, Hst⟩
    imodintro
    rw [stateI_eq]
    unfold hartInterp
    isplitl [Hγ]
    · iframe Hγ
      ipureintro
      exact Hok
    isplitl [Hk Hst]
    · dsimp only [wpH]
      iapply Hk
      iexact Hst
    · exact BigSepL.bigSepL_nil_intro
  | fin _ _ _ hd =>
    icases Hk with ⟨Hk, -⟩
    imod Hclose
    imod Hk $$ %hd Hst with Hv
    imodintro
    rw [stateI_eq]
    unfold hartInterp
    isplitl [Hγ]
    · iframe Hγ
      ipureintro
      exact Hf
    isplitl [Hv]
    · iapply (wp_value_fupd' (v := f)).2
      imodintro
      iexact Hv
    · exact BigSepL.bigSepL_nil_intro

end lift

end Weak.Mini.Logic
