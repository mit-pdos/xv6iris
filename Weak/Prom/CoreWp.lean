/-
Weak/Prom: **the ownership-free core: the weakest precondition `wpPF`** (stage S2; plan rev 7 §2 "Resources",
"wp shape", "The iProp form ⟦V⟧ᵢ"; §7 compatibility with MachCSL's `wpHart_lift`).

## The hart language

Per-hart adequacy (plan §2: "Per-hart Iris adequacy is sequential, with one thread per hart, over its state-phase
run") runs one iris-lean `Language` thread per hart.  The thread's expression is `HExpr.run w s`: the hart's
program state `s` together with its WORLD `w : HW` — the program half `pstep`, the value map `pdone`, the image, the
final memory `M` (the prophecy parameter of §2) and the hart index.  One primitive step (`hstep`) is ONE machine-v2
state step of the hart against the fixed log `M` (`memStep`), labelled by ONE `PLabel` its program half emits (for
Sail, one memory or dependency event: MachCSL's granularity), with the fabric values quantified (`anyFab`); or the
step to the value `v` when `pdone s = some v`.  The language state is the hart's exact `(ws, P, τ)`: its
`PState`, its remaining promise set and its machine trace (plan §2 [R4.5]).  Promise steps are not hart steps.

## Resources and the state interpretation

* `hartSt γ ws P τ` (plan §2): one half of a ghost variable holding `(ws, P, τ)`; exclusive.  The state
  interpretation `hartInterp` holds the other half and the PURE STEP INVARIANT `hartFacts`: the guarded trace
  invariant `∃ V, ⟦V⟧⌜Ψ τ⌝` (plan §2 [R2.6]) and `protoOk t` for every fulfilled `t` (plan §2 FULFIL).
* Every step gives exactly one `▷` and `£ 1` (`numLatersPerStep := 0`), as MachCSL's `wpHart_lift`
  (MachCSL/Wp.lean:432–435).  Stuckness is `MaybeStuck` (plan §2: "In regime A a store can only fulfil an existing
  promise, so 'can always step' is meaningless").
* `wpH γ π w Ψ s Φ` is iris-lean's `WP` of the thread.  `wpPF π w Ψ s Φ` (the plan's `wpPF π M h s Ψ Φ`) is its
  closed form at the hart's initial state: for every ghost name and the initial promise set (every own message of
  `M`), `hartSt γ psInit P0 [] -∗ wpH γ π w Ψ s Φ`.
* `wpH_lift` is the ONE lifting lemma (the shape of `wpHart_lift`); every leaf rule (CoreRules.lean) is proved from
  it and never unfolds `WP`.

## ⟦·⟧ᵢ (plan §2 [R2.4])

`validUpTo π img M V` is the persistent fact `⌜Valid π img M V⌝`; `grdI V P := □ (validUpTo V -∗ P)`.  The core
produces `validUpTo` only from `Valid` itself (a track's schedule ghost will, §3); its rules are below.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreFwd
import Iris.ProgramLogic.Lifting
import Iris.Instances.Lib.GhostVar

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The hart language -/

/-- THE HART'S WORLD: program half, value map, image, final memory (the prophecy `M`), hart index. -/
structure HW (P D V : Type) where
  pstep : P → D → PLabel → P → D → Prop
  pdone : P → Option V
  img : Image
  M : List PMsg
  h : Nat

/-- The thread expression: a running hart, or a hart that reached a value. -/
inductive HExpr (P D V : Type) where
  | run (w : HW P D V) (s : P)
  | ret (v : V)

/-- The language state: the hart's exact `PState`, its remaining promise set, its machine trace. -/
abbrev HSt : Type := PState × GSet Nat × Trace

variable {P D V : Type}

/-- ONE HART STEP (plan §2 "wp shape"): one machine-v2 state step against `M` with the label the program half
emits (any fabric values), appending the trace entry; or the step to the hart's value. -/
inductive hstep : HExpr P D V × HSt → List Unit → HExpr P D V × HSt × List (HExpr P D V) → Prop
  | lab (w : HW P D V) (s : P) (ws : PState) (pr : GSet Nat) (τ : Trace) (l : PLabel) (ots : Option Nat)
      (s' : P) (ws' : PState) (pr' : GSet Nat) (d d' : D) :
      w.pstep s d l s' d' → memStep w.img w.M w.h pr ws l ots ws' pr' →
      hstep (.run w s, (ws, pr, τ)) [] (.run w s', (ws', pr', τ ++ [(l, ots)]), [])
  | fin (w : HW P D V) (s : P) (σ : HSt) (v : V) :
      w.pdone s = some v → hstep (.run w s, σ) [] (.ret v, σ, [])

instance : PrimStep (HExpr P D V) HSt (List Unit) := ⟨hstep⟩

/-- The value of an expression. -/
def HExpr.toV : HExpr P D V → Option V
  | .ret v => some v
  | .run _ _ => none

instance : ToVal (HExpr P D V) V where
  toVal := HExpr.toV
  ofVal v := .ret v
  coe_of_toVal_eq_some {e v} h := by
    cases e with
    | run => cases h
    | ret v' => cases h; rfl
  toVal_coe _ := rfl

instance : Language (HExpr P D V) HSt Unit V where
  val_stuck h := by cases h <;> rfl

/-! ## 2. Resources and the state interpretation -/

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt]

/-- `hartSt γ ws P τ` (plan §2): the hart's exact state, promise set and trace; exclusive (one half). -/
def hartSt (γ : GName) (ws : PState) (pr : GSet Nat) (τ : Trace) : IProp GF :=
  ghost_var γ (.own (1 : Qp).half) ((ws, pr, τ) : HSt)

/-- THE PURE STEP INVARIANT: the guarded trace invariant (plan §2 [R2.6]), `protoOk` of every fulfil, and the
forward-bank knowledge (FK) with the fetch-view bound (FI) of CoreFwd.lean (plan §2 "Forwarded reads"). -/
def hartFacts (π : Proto) (img : Image) (M : List PMsg) (Ψ : Trace → Prop) (σ : HSt) : Prop :=
  (∃ V, grd π img M V (Ψ σ.2.2)) ∧ (∀ e ∈ σ.2.2, ∀ t, e.2 = some t → protoOk π img M t) ∧
  fetchInv σ.1 ∧ fwdKnow π img M σ.1 σ.2.2

/-- The state interpretation of hart `γ`'s thread. -/
def hartInterp (γ : GName) (π : Proto) (img : Image) (M : List PMsg) (Ψ : Trace → Prop) (σ : HSt) : IProp GF :=
  iprop(ghost_var γ (.own (1 : Qp).half) σ ∗ ⌜hartFacts π img M Ψ σ⌝)

/-- The iris-lean `IrisGS` of one hart's thread: one `▷` and `£ 1` per step. -/
@[reducible] def pfIrisGS [InvGS_gen hlc GF] (γ : GName) (π : Proto) (img : Image) (M : List PMsg) (Ψ : Trace → Prop) :
    IrisGS_gen hlc (HExpr P D V) GF where
  toStateInterp := ⟨fun σ _ _ _ => hartInterp γ π img M Ψ σ⟩
  invGS := inferInstance
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by iintro $

theorem pfStateI_eq [InvGS_gen hlc GF] (γ : GName) (π : Proto) (img : Image) (M : List PMsg)
    (Ψ : Trace → Prop) (σ : HSt) (ns : Nat) (obs : List Unit) (nt : Nat) :
    @stateInterp HSt Unit GF (pfIrisGS (P := P) (D := D) (V := V) γ π img M Ψ).toStateInterp σ ns obs nt =
      hartInterp γ π img M Ψ σ := rfl

/-- **`wpH γ π w Ψ s Φ`**: the hart wp at program state `s` (iris-lean's `WP` of the thread). -/
def wpH [InvGS_gen hlc GF] (γ : GName) (π : Proto) (w : HW P D V) (Ψ : Trace → Prop) (s : P)
    (Φ : V → IProp GF) : IProp GF :=
  letI : IrisGS_gen hlc (HExpr P D V) GF := pfIrisGS γ π w.img w.M Ψ
  WP (HExpr.run w s) @ Stuckness.MaybeStuck; ⊤ {{ Φ }}

/-- **`wpPF π w Ψ s Φ`** (plan §0/§2 `wpPF π M h s Ψ Φ`): the hart wp from its initial state — `psInit`, every
own message of `M` promised, the empty trace. -/
def wpPF [InvGS_gen hlc GF] (π : Proto) (w : HW P D V) (Ψ : Trace → Prop) (s : P) (Φ : V → IProp GF) :
    IProp GF :=
  iprop(∀ (γ : GName) (P0 : GSet Nat), ⌜∀ t, t ∈ P0 ↔ 0 < t ∧ ownTs w.M w.h t⌝ -∗
    hartSt γ psInit P0 [] -∗ wpH γ π w Ψ s Φ)

/-- The obligation of one step (plan §2): the guarded trace invariant of the new trace, and the fulfil's protocol
fact at its own pre-view, `⟦pv⟧ proto(M[t])` with `pv = fulPv ws l` (EXT gives `pv < t`, hence `protoOk t`; the
forward bank records it for forwarded reads). -/
def stepOk (π : Proto) (img : Image) (M : List PMsg) (Ψ : Trace → Prop) (ws : PState) (τ : Trace) (l : PLabel)
    (ots : Option Nat) : Prop :=
  (∃ V, grd π img M V (Ψ (τ ++ [(l, ots)]))) ∧
    ∀ t, ots = some t → ∀ m, msgAt M t = some m → grd π img M (fulPv ws l) (π.okMsg m)

/-! ## 3. The lifting lemma -/

section lift

variable [InvGS_gen hlc GF]

/-- **THE LIFTING LEMMA, with the state's facts** (plan §7: the statement shape of `wpHart_lift`, with the Prom
state interpretation): from `hartSt`, the hart may take any step its program half and machine v2 allow; one `▷`
for the step, `£ 1` for the continuation.  On a label step the client is handed the current step invariant
(`hartFacts`, e.g. the forward-bank knowledge), proves `stepOk` and continues from the new `hartSt`; on the value
step it proves `Φ v`. -/
theorem wpH_liftF {γ : GName} {π : Proto} {w : HW P D V} {Ψ : Trace → Prop} {s : P} {Φ : V → IProp GF}
    {ws : PState} {pr : GSet Nat} {τ : Trace} :
    hartSt γ ws pr τ ∗
    ▷ ((∀ v, ⌜w.pdone s = some v⌝ -∗ hartSt γ ws pr τ -∗ |={⊤}=> Φ v) ∧
       (∀ l ots s' ws' pr', ⌜anyFab w.pstep s () l s' ()⌝ -∗ ⌜memStep w.img w.M w.h pr ws l ots ws' pr'⌝ -∗
          ⌜hartFacts π w.img w.M Ψ (ws, pr, τ)⌝ -∗ £ 1 -∗ |={⊤}=> ⌜stepOk π w.img w.M Ψ ws τ l ots⌝ ∗
            (hartSt γ ws' pr' (τ ++ [(l, ots)]) -∗ wpH γ π w Ψ s' Φ)))
    ⊢ wpH γ π w Ψ s Φ := by
  letI : IrisGS_gen hlc (HExpr P D V) GF := pfIrisGS γ π w.img w.M Ψ
  show _ ⊢ WP (HExpr.run w s) @ Stuckness.MaybeStuck; ⊤ {{ Φ }}
  iintro ⟨Hst, Hk⟩
  iapply wp_lift_step (rfl : toVal (HExpr.run w s : HExpr P D V) = none)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rw [pfStateI_eq]
  unfold hartInterp
  icases Hσ with ⟨Hγ, %Hf⟩
  unfold hartSt
  ihave %Heq := ghost_var_agree γ _ _ _ _ $$ Hγ Hst
  subst Heq
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro; trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  change hstep _ _ _ at Hstep
  cases Hstep with
  | lab _ _ _ _ _ l ots s' ws' pr' d d' hp hm =>
    icases Hk with ⟨-, Hk⟩
    imod Hclose
    imod Hk $$ %l %ots %s' %ws' %pr' %⟨d, d', hp⟩ %hm %Hf Hcred with ⟨%Hok, Hk⟩
    imod ghost_var_update_halves ((ws', pr', τ ++ [(l, ots)]) : HSt) γ _ _ $$ Hγ Hst with ⟨Hγ, Hst⟩
    imodintro
    rw [pfStateI_eq]
    unfold hartInterp
    isplitl [Hγ]
    · iframe Hγ
      ipureintro
      have hfk := fwd_step hm Hf.2.2.1 Hf.2.2.2 Hok.2
      refine ⟨Hok.1, fun e he t het => ?_, hfk.1, hfk.2⟩
      rcases List.mem_append.1 he with he | he
      · exact Hf.2.1 e he t het
      · rw [List.mem_singleton] at he; subst he
        simp only at het; subst het
        exact protoOk_of_grd (fulPv_lt hm) (Hok.2 t rfl)
    isplitl [Hk Hst]
    · dsimp only [wpH]
      iapply Hk
      iexact Hst
    · exact BigSepL.bigSepL_nil_intro
  | fin _ _ _ v hv =>
    icases Hk with ⟨Hk, -⟩
    imod Hclose
    imod Hk $$ %v %hv Hst with Hv
    imodintro
    rw [pfStateI_eq]
    unfold hartInterp
    isplitl [Hγ]
    · iframe Hγ
      ipureintro
      exact Hf
    isplitl [Hv]
    · iapply (wp_value_fupd' (v := v)).2
      imodintro
      iexact Hv
    · exact BigSepL.bigSepL_nil_intro

/-- **THE LIFTING LEMMA** (the client does not need the state's facts). -/
theorem wpH_lift {γ : GName} {π : Proto} {w : HW P D V} {Ψ : Trace → Prop} {s : P} {Φ : V → IProp GF}
    {ws : PState} {pr : GSet Nat} {τ : Trace} :
    hartSt γ ws pr τ ∗
    ▷ ((∀ v, ⌜w.pdone s = some v⌝ -∗ hartSt γ ws pr τ -∗ |={⊤}=> Φ v) ∧
       (∀ l ots s' ws' pr', ⌜anyFab w.pstep s () l s' ()⌝ -∗ ⌜memStep w.img w.M w.h pr ws l ots ws' pr'⌝ -∗
          £ 1 -∗ |={⊤}=> ⌜stepOk π w.img w.M Ψ ws τ l ots⌝ ∗
            (hartSt γ ws' pr' (τ ++ [(l, ots)]) -∗ wpH γ π w Ψ s' Φ)))
    ⊢ wpH γ π w Ψ s Φ := by
  iintro ⟨Hst, Hk⟩
  iapply wpH_liftF
  iframe Hst
  inext
  isplit
  · icases Hk with ⟨Hk, -⟩
    iexact Hk
  · icases Hk with ⟨-, Hk⟩
    iintro %l %ots %s' %ws' %pr' %hp %hm %_ Hc
    iapply Hk $$ %l %ots %s' %ws' %pr' %hp %hm Hc

/-- A hart in a state with no step and no value is safe (MaybeStuck). -/
theorem wpH_stuck {γ : GName} {π : Proto} {w : HW P D V} {Ψ : Trace → Prop} {s : P} {Φ : V → IProp GF}
    {ws : PState} {pr : GSet Nat} {τ : Trace}
    (hd : w.pdone s = none) (hns : ∀ l s', ¬ anyFab w.pstep s () l s' ()) :
    hartSt γ ws pr τ ⊢ wpH γ π w Ψ s Φ := by
  iintro Hst
  iapply wpH_lift
  iframe Hst
  inext
  isplit
  · iintro %v %hv
    rw [hd] at hv; cases hv
  · iintro %l %ots %s' %ws' %pr' %hp
    exact absurd hp (hns l s')

end lift

/-! ## 4. ⟦·⟧ᵢ (plan §2 [R2.4]) -/

/-- `validUpTo π img M V`: the persistent fact that every message up to `V` meets its protocol. -/
def validUpTo (π : Proto) (img : Image) (M : List PMsg) (V : Nat) : IProp GF := iprop(⌜Valid π img M V⌝)

/-- `⟦V⟧ᵢ P := □ (validUpTo V -∗ P)` (plan §2 [R2.4]), for persistent `P`. -/
def grdI (π : Proto) (img : Image) (M : List PMsg) (V : Nat) (Q : IProp GF) : IProp GF :=
  iprop(□ (validUpTo π img M V -∗ Q))

section grdI

variable {π : Proto} {img : Image} {M : List PMsg}

/-- `⟦V⟧φ ⊢ ⟦V⟧ᵢ ⌜φ⌝`. -/
theorem grdI_of_grd {V : Nat} {φ : Prop} (h : grd π img M V φ) : ⊢@{IProp GF} grdI π img M V iprop(⌜φ⌝) := by
  unfold grdI validUpTo
  imodintro
  iintro %hv
  ipureintro
  exact h hv

/-- Monotonicity in `V`. -/
theorem grdI_mono {V V' : Nat} {Q : IProp GF} (hV : V ≤ V') : grdI π img M V Q ⊢ grdI π img M V' Q := by
  unfold grdI validUpTo
  iintro #H
  imodintro
  iintro %hv
  iapply H
  ipureintro
  exact hv.mono hV

/-- `⟦V⟧ᵢ P ∗ ⟦V'⟧ᵢ Q ⊢ ⟦max V V'⟧ᵢ (P ∗ Q)`. -/
theorem grdI_sep {V V' : Nat} {Q R : IProp GF} :
    grdI π img M V Q ∗ grdI π img M V' R ⊢ grdI π img M (max V V') iprop(Q ∗ R) := by
  unfold grdI validUpTo
  iintro ⟨#H1, #H2⟩
  imodintro
  iintro %hv
  isplitl
  · iapply H1; ipureintro; exact hv.mono (Nat.le_max_left _ _)
  · iapply H2; ipureintro; exact hv.mono (Nat.le_max_right _ _)

/-- `⟦V⟧ᵢ P ∗ validUpTo V ⊢ P`. -/
theorem grdI_elim {V : Nat} {Q : IProp GF} : grdI π img M V Q ∗ validUpTo π img M V ⊢ Q := by
  unfold grdI
  iintro ⟨#H, Hv⟩
  iapply H
  iexact Hv

end grdI

end Weak.Prom.PF
