/-
MachCSL: **the short-circuit elimination theorem** (lane AND-ELIM).

The lean-sail backend compiles Sail's short-circuit `&`/`|` to Lean's
`(← a) && (← b)`, which Lean hoists: `b` always runs.  When `b` is read-only
and total (`SailRO`), the eager program is its short-circuit form with extra,
discarded register reads (`SailStut`, `MachCSL/SailStut.lean`).  This file
proves, once, that the program logic cannot tell them apart in the direction
proofs consume:

* `hartWP_stut` (the simulation, by Löb induction over the operational
  semantics): `SailStut m₀ m → hartWP gen cpu m₀ ⊢ hartWP gen cpu m`.  A
  discarded read is one more hart step that leaves the machine state as it
  was, so the eager hart can always follow the short-circuit one (it has one
  more later to spend); a dead generation's corpse self-loop is followed by
  the corpse self-loop.
* `wpHart_stut`, **`swp_stut`**: `SailStut m₀ m → swp cpu m₀ Φ ⊢ swp cpu m Φ`.
* the shapes the backend emits (`swp_and_elim`, `swp_or_elim`,
  `swp_and_bind_elim`, `swp_or_bind_elim`, `swp_and3_elim`) and the generic
  discard (`swp_irrel`, `swp_seq_ro`): rewrite the goal to the short-circuit
  form before stepping, and the right operand's registers leave the footprint.
* the walker form: `swp_runRW_stut` (walk the short-circuit program, conclude
  for the eager one) and the walk-up-to-discards predicate `URunSc` with its
  bind toolkit and consumer `swp_URunSc`, so a walk fact can be stated for the
  model's own (eager) program with a footprint that omits the discarded reads.

**Only one direction.**  `swp cpu m Φ ⊢ swp cpu m₀ Φ` is not derivable: the
eager program takes more steps, and a weakest precondition cannot give back
the later a step consumed.  The direction here is the one every proof uses
(the goal is the model's eager program).
-/
import MachCSL.SailStut
import MachCSL.URunRW

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## The simulation -/

section sim
variable {hlc : HasLC} {GF : BundledGFunctors} [MachFixedGS hlc GF]

/-- The simulation's statement (its own Löb induction hypothesis). -/
def stutSim (gen : Nat) (cpu : CPU) : IProp GF :=
  iprop(∀ (m₀ m : SailM Unit), ⌜SailStut m₀ m⌝ → hartWP gen cpu m₀ -∗ hartWP gen cpu m)

/-- `hartWP`, unfolded one step (the `wp.pre` of a hart, at this language's
one later per step). -/
theorem hartWP_unfold_ev (gen : Nat) (cpu : CPU) (m : SailM Unit) :
    hartWP (GF := GF) gen cpu m ⊢ ∀ (σ₁ : GState) (ns : Nat) (obs obs' : List Obs) (nt : Nat),
      stateInterp σ₁ ns (obs ++ obs') nt ={⊤,∅}=∗
      ⌜PrimStep.Reducible (Expr.hart gen cpu m, σ₁)⌝ ∗
      ∀ (e₂ : Expr) (σ₂ : GState) (eₜ : List Expr),
        ⌜PrimStep.primStep (Expr.hart gen cpu m, σ₁) obs (e₂, σ₂, eₜ)⌝ -∗ £ 1 -∗
        |={∅}=> ▷ |={∅}=> |={∅,⊤}=> stateInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
          WP e₂ @ Stuckness.NotStuck; ⊤ {{ _v, True }} ∗
          [∗list] ef ∈ eₜ, WP ef @ Stuckness.NotStuck; ⊤ {{ IrisGS_gen.forkPost Expr GState Obs }} := by
  unfold hartWP
  exact wp_unfold.1

/-- The state interpretation after a silent hart step that kept the state. -/
theorem stut_si (g : GState) (σ : MState) (hσ : σ = g.m) (ns nt : Nat) (obs' : List Obs) :
    stateInterp g ns ([] ++ obs') nt ⊢@{IProp GF}
      stateInterp { g with m := σ } (ns + 1) obs' (nt + ([] : List Expr).length) := by
  subst hσ; exact .rfl

/-- The corpse step's state interpretation. -/
theorem stut_si' (g : GState) (ns nt : Nat) (obs' : List Obs) :
    stateInterp g ns ([] ++ obs') nt ⊢@{IProp GF}
      stateInterp g (ns + 1) obs' (nt + ([] : List Expr).length) := .rfl

/-- The step's tail: the short-circuit side's continuation, taken over by
the eager side through the induction hypothesis (under the step's later). -/
theorem stut_tail (gen : Nat) (cpu : CPU) (m₀ m : SailM Unit) (h : SailStut m₀ m) (S L : IProp GF) :
    ▷ stutSim gen cpu ∗ (|={∅}=> ▷ |={∅}=> |={∅,⊤}=> S ∗
        WP (Expr.hart gen cpu m₀) @ Stuckness.NotStuck; ⊤ {{ _v, True }} ∗ L) ⊢
      |={∅}=> ▷ |={∅,⊤}=> S ∗ WP (Expr.hart gen cpu m) @ Stuckness.NotStuck; ⊤ {{ _v, True }} ∗ L := by
  unfold stutSim hartWP
  iintro ⟨IH, H⟩
  imod H
  imodintro
  inext
  imod H
  imod H with ⟨HS, HW, HL⟩
  imodintro
  iframe HS HL
  iapply IH $$ %m₀ %m %h HW

/-- An inserted read: the eager side takes it (the state stays), then goes on
as the short-circuit side. -/
theorem hartWP_stut_read (gen : Nat) (cpu : CPU) (m₀ : SailM Unit) (r : Register)
    (k : RegisterType r → SailM Unit) (hk : ∀ v, SailStut m₀ (k v)) :
    ▷ stutSim gen cpu ∗ hartWP gen cpu m₀ ⊢@{IProp GF}
      hartWP gen cpu (FreeM.impure (.ok (.regRead r)) k) := by
  unfold stutSim hartWP
  iintro ⟨IH, H⟩
  iapply wp_lift_step rfl
  iintro %g %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro
    by_cases hl : threadLive g gen
    · exact ⟨[], _, _, [], primStep_hart_live hl (Or.inl ⟨g.m.regs cpu r, rfl, rfl, rfl⟩)⟩
    · exact ⟨[], _, _, [], primStep_hart_dead hl⟩
  inext
  iintro %e₂ %g₂ %eₜ %Hstep _
  obtain ⟨rfl, rfl, h⟩ := primStep_hart_inv Hstep
  imod Hclose
  imodintro
  rcases h with ⟨_, m', σ', rfl, hs, rfl⟩ | ⟨_, rfl, rfl⟩
  · unfold hartStep at hs
    rcases hs with ⟨v, rfl, -, rfl⟩ | ⟨hb, _⟩
    · isplitl [Hσ]
      · iapply stut_si g g.m rfl
        iexact Hσ
      isplit
      · iapply IH $$ %m₀ %(k v) %(hk v) H
      · exact BigSepL.bigSepL_nil_intro
    · exact hb.elim
  · isplitl [Hσ]
    · iapply stut_si'
      iexact Hσ
    isplit
    · iapply IH $$ %m₀ %_ %(SailStut.read r k hk) H
    · exact BigSepL.bigSepL_nil_intro

/-- A shared event: both sides take it; the eager side's successor is
matched by the short-circuit side's successor on the same answer (or the
same retry, when the event is blocked; or the corpse self-loop). -/
theorem hartWP_stut_step (gen : Nat) (cpu : CPU) (o : Outcome Register RegisterType)
    (k₀ k : o.ret → SailM Unit) (hk : ∀ v, SailStut (k₀ v) (k v)) :
    ▷ stutSim gen cpu ∗ hartWP gen cpu (FreeM.impure (.ok o) k₀) ⊢@{IProp GF}
      hartWP gen cpu (FreeM.impure (.ok o) k) := by
  conv => rhs; unfold hartWP
  iintro ⟨IH, H⟩
  ihave H := hartWP_unfold_ev gen cpu _ $$ H
  iapply wp_lift_step_fupd rfl
  iintro %g %ns %obs %obs' %nt Hσ
  imod H $$ %g %ns %obs %obs' %nt Hσ with ⟨%Hred, H⟩
  imodintro
  isplit
  · ipureintro
    obtain ⟨_, _, _, _, hst⟩ := Hred
    obtain ⟨rfl, rfl, h⟩ := primStep_hart_inv hst
    rcases h with ⟨hl, m', σ', rfl, hs, rfl⟩ | ⟨hnl, rfl, rfl⟩
    · unfold hartStep at hs
      rcases hs with ⟨v, rfl, hev⟩ | ⟨hb, rfl⟩
      · exact ⟨[], _, _, [], primStep_hart_live hl (Or.inl ⟨v, rfl, hev⟩)⟩
      · exact ⟨[], _, _, [], primStep_hart_live hl (Or.inr ⟨hb, rfl⟩)⟩
    · exact ⟨[], _, _, [], primStep_hart_dead hnl⟩
  iintro %e₂ %g₂ %eₜ %Hstep Hcred
  obtain ⟨rfl, rfl, h⟩ := primStep_hart_inv Hstep
  rcases h with ⟨hl, m', σ', rfl, hs, rfl⟩ | ⟨hnl, rfl, rfl⟩
  · unfold hartStep at hs
    rcases hs with ⟨v, rfl, hev⟩ | ⟨hb, rfl⟩
    · iapply stut_tail gen cpu (k₀ v) (k v) (hk v)
      isplitl [IH]
      · iexact IH
      iapply H $$ %_ %_ %_ %(primStep_hart_live hl (Or.inl ⟨v, rfl, hev⟩)) Hcred
    · iapply stut_tail gen cpu _ _ (SailStut.step o k₀ k hk)
      isplitl [IH]
      · iexact IH
      iapply H $$ %_ %_ %_ %(primStep_hart_live hl (Or.inr ⟨hb, rfl⟩)) Hcred
  · iapply stut_tail gen cpu _ _ (SailStut.step o k₀ k hk)
    isplitl [IH]
    · iexact IH
    iapply H $$ %_ %_ %_ %(primStep_hart_dead hnl) Hcred

/-- **The simulation**, by Löb induction. -/
theorem stutSim_holds (gen : Nat) (cpu : CPU) : ⊢@{IProp GF} stutSim gen cpu := by
  iloeb as IH
  conv => rhs; unfold stutSim
  iintro %m₀ %m %h H
  cases h with
  | refl => iexact H
  | read r k hk =>
    iapply hartWP_stut_read gen cpu _ r k hk
    isplitl []
    · iexact IH
    · iexact H
  | step o k₀ k hk =>
    iapply hartWP_stut_step gen cpu o k₀ k hk
    isplitl []
    · iexact IH
    · iexact H

/-- **The simulation**: a hart running the eager program is safe whenever it
is safe running the short-circuit one. -/
theorem hartWP_stut {m₀ m : SailM Unit} (h : SailStut m₀ m) (gen : Nat) (cpu : CPU) :
    hartWP (GF := GF) gen cpu m₀ ⊢ hartWP gen cpu m := by
  iintro H
  ihave IH := stutSim_holds (GF := GF) gen cpu
  unfold stutSim
  iapply IH $$ %m₀ %m %h H

end sim

/-! ## The program logic -/

section swp
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

theorem wpHart_stut {m₀ m : SailM Unit} (h : SailStut m₀ m) (cpu : CPU) :
    wpHart (GF := GF) cpu m₀ ⊢ wpHart cpu m := by
  unfold wpHart
  iintro H #Hc
  iapply hartWP_stut h
  iapply H $$ Hc

/-- **The elimination theorem**: the eager program is proved by its
short-circuit form. -/
theorem swp_stut {X : Type} {m₀ m : SailM X} (h : SailStut m₀ m) (cpu : CPU) (Φ : X → IProp GF) :
    swp cpu m₀ Φ ⊢ swp cpu m Φ := by
  unfold swp
  iintro H %C %hC Hk
  iapply wpHart_stut (h.ctx hC)
  iapply H $$ %C %hC Hk

/-- A read-only total computation whose answer is not used. -/
theorem swp_irrel (cpu : CPU) {X Y : Type} {b : SailM Y} (hb : SailRO b) {k : Y → SailM X}
    {m : SailM X} (hk : ∀ y, k y = m) (Φ : X → IProp GF) :
    swp cpu m Φ ⊢ swp cpu (b >>= k) Φ :=
  swp_stut (SailStut.irrel hb hk) cpu Φ

/-- A sequenced read-only total computation. -/
theorem swp_seq_ro (cpu : CPU) {X Y : Type} {b : SailM Y} (hb : SailRO b) (m : SailM X)
    (Φ : X → IProp GF) : swp cpu m Φ ⊢ swp cpu (b >>= fun _ => m) Φ :=
  swp_stut (SailStut.seq hb) cpu Φ

/-- **`p && (← b)`**, `b` read-only and total. -/
theorem swp_and_elim (cpu : CPU) {X : Type} (p : Bool) {b : SailM Bool} (hb : SailRO b)
    (k : Bool → SailM X) (Φ : X → IProp GF) :
    swp cpu (if p then b >>= k else k false) Φ ⊢ swp cpu (b >>= fun y => k (p && y)) Φ :=
  swp_stut (SailStut.and p hb k) cpu Φ

/-- **`p || (← b)`**, `b` read-only and total. -/
theorem swp_or_elim (cpu : CPU) {X : Type} (p : Bool) {b : SailM Bool} (hb : SailRO b)
    (k : Bool → SailM X) (Φ : X → IProp GF) :
    swp cpu (if p then k true else b >>= k) Φ ⊢ swp cpu (b >>= fun y => k (p || y)) Φ :=
  swp_stut (SailStut.or p hb k) cpu Φ

/-- **`(← a) && (← b)`**, `b` read-only and total. -/
theorem swp_and_bind_elim (cpu : CPU) {X : Type} (a : SailM Bool) {b : SailM Bool} (hb : SailRO b)
    (k : Bool → SailM X) (Φ : X → IProp GF) :
    swp cpu (a >>= fun x => if x then b >>= k else k false) Φ ⊢
      swp cpu (a >>= fun x => b >>= fun y => k (x && y)) Φ :=
  swp_stut (SailStut.and_bind a hb k) cpu Φ

/-- **`(← a) || (← b)`**, `b` read-only and total. -/
theorem swp_or_bind_elim (cpu : CPU) {X : Type} (a : SailM Bool) {b : SailM Bool} (hb : SailRO b)
    (k : Bool → SailM X) (Φ : X → IProp GF) :
    swp cpu (a >>= fun x => if x then k true else b >>= k) Φ ⊢
      swp cpu (a >>= fun x => b >>= fun y => k (x || y)) Φ :=
  swp_stut (SailStut.or_bind a hb k) cpu Φ

/-- **`(← a) && (P && ((← b) && (← c)))`**, `b`, `c` read-only and total. -/
theorem swp_and3_elim (cpu : CPU) {X : Type} (a : SailM Bool) (P : Bool) {b c : SailM Bool}
    (hb : SailRO b) (hc : SailRO c) (k : Bool → SailM X) (Φ : X → IProp GF) :
    swp cpu (a >>= fun x => if x && P then b >>= fun y => if y then c >>= k else k false else k false) Φ ⊢
      swp cpu (a >>= fun x => b >>= fun y => c >>= fun z => k (x && (P && (y && z)))) Φ :=
  swp_stut (SailStut.and3 a P hb hc k) cpu Φ

end swp

/-! ## The walker form -/

/-- **A walk up to discarded reads**: some short-circuit form of `m` walks,
from `s`, to `res orc` for every oracle.  The footprint `D` need not read the
registers of the discarded operands. -/
def URunSc (D : UFoot) (s : UWSt) {X : Type} (m : SailM X) (res : UOrc → Option (X × UWSt × UOrc)) :
    Prop :=
  ∃ m₀, SailStut m₀ m ∧ ∀ orc, runRW D orc s m₀ = res orc

namespace URunSc

variable {D : UFoot} {s : UWSt}

/-- A plain walk. -/
theorem of_runRW {X : Type} {m : SailM X} {res : UOrc → Option (X × UWSt × UOrc)}
    (h : ∀ orc, runRW D orc s m = res orc) : URunSc D s m res :=
  ⟨m, .refl m, h⟩

/-- A walk of a short-circuit form. -/
theorem of_stut {X : Type} {m₀ m : SailM X} {res : UOrc → Option (X × UWSt × UOrc)}
    (hS : SailStut m₀ m) (h : ∀ orc, runRW D orc s m₀ = res orc) : URunSc D s m res :=
  ⟨m₀, hS, h⟩

/-- Rewrite the program by a short-circuit step. -/
theorem stut {X : Type} {m₁ m : SailM X} {res : UOrc → Option (X × UWSt × UOrc)}
    (hS : ∀ m₀, SailStut m₀ m₁ → SailStut m₀ m) (h : URunSc D s m₁ res) : URunSc D s m res :=
  let ⟨m₀, h₀, hw⟩ := h
  ⟨m₀, hS m₀ h₀, hw⟩

/-- **The bind law** (`runRW_bind`, up to discards): a first part landing
at a fixed answer and state, the oracle moved by `g`. -/
theorem bind {X Y : Type} {m : SailM X} {f : X → SailM Y} {x : X} {s' : UWSt} {g : UOrc → UOrc}
    {res : UOrc → Option (Y × UWSt × UOrc)}
    (hm : URunSc D s m (fun orc => some (x, s', g orc))) (hf : URunSc D s' (f x) res) :
    URunSc D s (m >>= f) (fun orc => res (g orc)) := by
  classical
  obtain ⟨m₀, hm₀, hw⟩ := hm
  obtain ⟨f₀, hf₀, hfw⟩ := hf
  refine ⟨m₀ >>= fun y => if y = x then f₀ else f y, SailStut.bind hm₀ fun y => ?_, fun orc => ?_⟩
  · by_cases hy : y = x
    · subst hy; rw [if_pos rfl]; exact hf₀
    · rw [if_neg hy]; exact .refl _
  · rw [runRW_bind, hw]
    show runRW D (g orc) s' (if x = x then f₀ else f x) = res (g orc)
    rw [if_pos rfl, hfw]

end URunSc

section walk
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable {cpu : CPU} {ξ : CtxId} {D : UFoot} (RF : URegFrame GF cpu D) (BF : UByteFrame GF ξ)

/-- **`swp_runRW` through a short-circuit form**: walk `m₀`, conclude for
the eager `m`. -/
theorem swp_runRW_stut {X : Type} {m₀ m : SailM X} (hS : SailStut m₀ m) (s : UWSt)
    (hok : ∀ orc, (runRW D orc s m₀).isSome = true) (Φ : X → IProp GF) :
    uFr RF BF s ∗ uPost RF BF s m₀ Φ ⊢ swp cpu m Φ :=
  (swp_runRW RF BF m₀ s hok Φ).trans (swp_stut hS cpu Φ)

/-- **The consumer of a walk up to discards.** -/
theorem swp_URunSc {X : Type} {m : SailM X} {s : UWSt} {res : UOrc → Option (X × UWSt × UOrc)}
    (h : URunSc D s m res) (hok : ∀ orc, (res orc).isSome = true) (Φ : X → IProp GF) :
    uFr RF BF s ∗ (∀ (orc : UOrc) (x : X) (s' : UWSt) (orc' : UOrc), ⌜res orc = some (x, s', orc')⌝ -∗
      RF.F s'.file -∗ BF.B s'.mm -∗ ownCtx cpu ξ -∗ uResvTok cpu s'.rv -∗ Φ x) ⊢ swp cpu m Φ := by
  obtain ⟨m₀, hS, hw⟩ := h
  refine .trans ?_ (swp_runRW_stut RF BF hS s (fun orc => (hw orc) ▸ hok orc) Φ)
  unfold uPost
  iintro ⟨Hfr, HP⟩
  iframe Hfr
  iintro %orc %x %s' %orc' %hr
  iapply HP $$ %orc %x %s' %orc' %((hw orc).symm.trans hr)

end walk

end MachCSL
