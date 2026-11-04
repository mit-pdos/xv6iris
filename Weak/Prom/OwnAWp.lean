/-
Weak/Prom: **track (a), the concurrent weakest precondition `wpA`** (stage S4a; plan rev 7 §3 "Frontier elimination,
restated", "Resource part, an invariant access, pre-allocated", R-a1, R-a5; §2 "wp shape", "⟦·⟧ᵢ").

One iris-lean thread per hart of the concurrent language (OwnALang.lean), all in ONE Iris world, so Iris invariants
are shared and opened per hart step along the chosen schedule ("Invariants and points-to … Iris invariants are opened
per hart step along the chosen schedule, so the step index is the schedule's step count", plan §3).

## Ghost state (names `AGN`, allocated once at adequacy start, plan R-a5)

* `hartA g h ws P τ` — hart `h`'s exact state (plan §2 `hartSt`), half of a ghost variable (the state
  interpretation holds the other half).
* `pend g t` / `shot g t` — THE PER-MESSAGE ONE-SHOT, one per `t ∈ 1..|M|` (pre-allocated, plan §3 "At adequacy
  start (M is a parameter, so |M| is known), for every index t in 1..|M|").  `pend g t` is exclusive, `shot g t`
  persistent, `pend ∗ shot ⊢ False` (`pend_shot`), and `pend g t ==∗ shot g t` (`shoot`).  The lifting lemma
  REQUIRES `shot g t` at the fulfil of `t`, so the only way to fulfil `t` is to have shot its `pend` — wherever the
  program proof put it (e.g. inside a deposit invariant `inv N (pend t ∨ (shot t ∗ R))`: the author must take
  `pend t` out, shoot it and deposit `R` in the same step; plan §3 "The deposit … happens at t's fulfil").
* `dpend g` / `dshot g` and `doomInv g M` — THE DOOM BOX, the mechanism for R-a1 (plan §3: "The read rule must
  therefore return 'v, or ⟦·⟧-doomed until my release'").  A hart holding `pend s` for a message `s` may surrender
  it for good (`doom`): `s` can then never be fulfilled, so the run is not valid, and the persistent `dshot g`
  discharges every later obligation (Ψ, Φ, protocol facts) of every hart.  Adequacy eliminates it: in a valid run
  every `t` is fulfilled, hence shot, so the box cannot hold any `pend s` (`adequacyA`, OwnAAdeq.lean).

## The frontier rule (plan §3 "Frontier elimination, restated")

`frontA g π img M ws`: at every step the hart is handed, for its PRE-state `ws`,
* `□ ∀ t ≤ min (WF ws) |M|, shot g t` — "stage ≥ WF(h)" (the guard `fOk`) and every fulfilled `t` is shot (state
  interpretation): the plan's `stage ≥ d(t) ⊢ deposited_t` for release-class `t`;
* `⌜Valid π img M (WF ws)⌝ ∨ dshot g` — the PURE part `⟦s⟧φ ∗ ⌜s ≤ WF(ws)⌝ ⊢ φ` (`stage ≥ V ⊢ validUpTo V`:
  every `t ≤ V` fulfilled, each with its recorded `protoOk`).
The post-state's frontier is not offered: it may contain the step's own fulfil `t`, whose protocol fact is being
proved by this step.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnASched
import Iris.ProgramLogic.Lifting
import Iris.Instances.Lib.GhostVar
import Iris.Instances.Lib.Invariants

namespace Weak.Prom.OA

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

variable {P D V : Type} {hlc : HasLC}

/-! ## 1. Ghost names and resources -/

/-- The ghost names of track (a), allocated once at adequacy start. -/
structure AGN where
  /-- hart state ghosts, one per hart of the domain -/
  hn : List GName
  /-- message one-shots: `mn[t-1]` for `t ∈ 1..|M|` -/
  mn : List GName
  /-- the doom one-shot -/
  dn : GName

/-- The doom box's namespace. -/
def doomN : Namespace := ndot nroot "promDoom"

section res

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool]

/-- `hartA g h ws P τ` (plan §2 `hartSt h ws P τ`): hart `h` of the domain, its exact state; exclusive. -/
def hartA (g : AGN) (h : Nat) (ws : PState) (pr : GSet Nat) (τ : Trace) : IProp GF :=
  iprop(⌜h < g.hn.length⌝ ∗ ghost_var (g.hn.getD h 0) (.own (1 : Qp).half) ((ws, pr, τ) : HSt))

/-- The exclusive half of message `t`'s one-shot (plan §3, `dep_t`/`notYet_t`). -/
def pend (g : AGN) (t : Nat) : IProp GF := ghost_var (g.mn.getD (t - 1) 0) (.own 1) false

/-- The persistent "fulfilled" fact of message `t` (plan §3 `deposited_t`'s source). -/
def shot (g : AGN) (t : Nat) : IProp GF := ghost_var (g.mn.getD (t - 1) 0) .discard true

/-- The doom one-shot, not yet shot. -/
def dpend (g : AGN) : IProp GF := ghost_var g.dn (.own 1) false

/-- The doom one-shot, shot: this branch is not part of any valid run. -/
def dshot (g : AGN) : IProp GF := ghost_var g.dn .discard true

/-- THE DOOM BOX (plan R-a1): an invariant holding `dpend`, or `dshot` with some surrendered `pend s`. -/
def doomInv [InvGS_gen hlc GF] (g : AGN) (M : List PMsg) : IProp GF :=
  inv doomN iprop(dpend g ∨ (dshot g ∗ ∃ s, ⌜1 ≤ s ∧ s ≤ M.length⌝ ∗ pend g s))

instance [InvGS_gen hlc GF] (g : AGN) (M : List PMsg) : Persistent (doomInv (GF := GF) g M) := by
  unfold doomInv; infer_instance
instance (g : AGN) (t : Nat) : Persistent (shot (GF := GF) g t) := by unfold shot; infer_instance
instance (g : AGN) : Persistent (dshot (GF := GF) g) := by unfold dshot; infer_instance
instance (g : AGN) (t : Nat) : Timeless (shot (GF := GF) g t) := by unfold shot; infer_instance
instance (g : AGN) (t : Nat) : Timeless (pend (GF := GF) g t) := by unfold pend; infer_instance
instance (g : AGN) : Timeless (dshot (GF := GF) g) := by unfold dshot; infer_instance
instance (g : AGN) : Timeless (dpend (GF := GF) g) := by unfold dpend; infer_instance

/-- `pend ∗ shot ⊢ False`. -/
theorem pend_shot (g : AGN) (t : Nat) : pend (GF := GF) g t ∗ shot g t ⊢ False := by
  unfold pend shot
  iintro ⟨H1, H2⟩
  ihave %h := ghost_var_valid_2 $$ H1 H2
  exact absurd h.2 (by decide)

/-- `dpend ∗ dshot ⊢ False`. -/
theorem dpend_dshot (g : AGN) : dpend (GF := GF) g ∗ dshot g ⊢ False := by
  unfold dpend dshot
  iintro ⟨H1, H2⟩
  ihave %h := ghost_var_valid_2 $$ H1 H2
  exact absurd h.2 (by decide)

/-- SHOOT the one-shot of `t` (the fulfil's obligation). -/
theorem shoot (g : AGN) (t : Nat) : pend (GF := GF) g t ⊢ |==> shot g t := by
  unfold pend shot
  iintro H
  imod ghost_var_update true _ false $$ H with H
  iapply ghost_var_persist $$ H

/-- **DOOM** (plan R-a1): surrender `pend s` to the doom box; this branch's every later obligation is then
discharged by the persistent `dshot g` (no valid run fulfils `s`). -/
theorem doom [InvGS_gen hlc GF] {E : CoPset} (hE : ↑doomN ⊆ E) (g : AGN) (M : List PMsg) (s : Nat)
    (hs : 1 ≤ s ∧ s ≤ M.length) : doomInv (GF := GF) g M ∗ pend g s ⊢ |={E}=> dshot g := by
  iintro ⟨#Hinv, Hp⟩
  unfold doomInv
  unfold dshot
  imod inv_acc_timeless hE $$ Hinv with ⟨Hb, Hclose⟩
  icases Hb with (Hd | ⟨#Hs, Hrest⟩)
  · unfold dpend
    imod ghost_var_update true _ false $$ Hd with Hd
    imod ghost_var_persist $$ Hd with #Hd
    imod Hclose $$ [Hp] with -
    · iright
      isplitr [Hp]
      · iexact Hd
      · iexists s; iframe Hp; ipureintro; exact hs
    imodintro
    iexact Hd
  · imod Hclose $$ [Hrest] with -
    · iright; iframe Hs; iexact Hrest
    imodintro
    iexact Hs

end res

/-! ## 2. The state interpretation -/

section si

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool]

/-- The pure facts of every hart of the domain (plan §2: the guarded trace invariant at every prefix, `protoOk` of
every fulfil, the forward-bank knowledge (FK) and fetch bound (FI) of CoreFwd.lean), and PO-img. -/
def cFacts (π : Proto) (img : Image) (M : List PMsg) (Ψ : Nat → Trace → Prop) (n : Nat) (σ : CSt) : Prop :=
  π.okImg img ∧ ∀ h, h < n →
    (∀ k, ∃ V, grd π img M V (Ψ h ((σ h).2.2.take k))) ∧
    (∀ e ∈ (σ h).2.2, ∀ t, e.2 = some t → protoOk π img M t) ∧
    fetchInv (σ h).1 ∧ fwdKnow π img M (σ h).1 (σ h).2.2

/-- THE STATE INTERPRETATION of the concurrent language. -/
def stA (g : AGN) (π : Proto) (img : Image) (M : List PMsg) (Ψ : Nat → Trace → Prop) (σ : CSt) : IProp GF :=
  iprop(([∗list] k ↦ γ ∈ g.hn, ghost_var γ (.own (1 : Qp).half) (σ k)) ∗
    ⌜∀ k, g.hn.length ≤ k → (σ k).2.2 = []⌝ ∗
    ⌜∀ k, fOk M σ k⌝ ∗
    □ (∀ t, ⌜1 ≤ t ∧ t ≤ M.length ∧ fulAt σ t⌝ → shot g t) ∗
    (⌜cFacts π img M Ψ g.hn.length σ⌝ ∨ dshot g))

/-- The iris-lean `IrisGS` of the concurrent language: one `▷` and `£ 1` per step. -/
@[reducible] def aIrisGS [InvGS_gen hlc GF] (g : AGN) (π : Proto) (img : Image) (M : List PMsg)
    (Ψ : Nat → Trace → Prop) : IrisGS_gen hlc (CExpr P D V) GF where
  toStateInterp := ⟨fun σ _ _ _ => stA g π img M Ψ σ⟩
  invGS := inferInstance
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by iintro $

theorem aStateI_eq [InvGS_gen hlc GF] (g : AGN) (π : Proto) (img : Image) (M : List PMsg)
    (Ψ : Nat → Trace → Prop) (σ : CSt) (ns : Nat) (obs : List Unit) (nt : Nat) :
    @stateInterp CSt Unit GF (aIrisGS (P := P) (D := D) (V := V) g π img M Ψ).toStateInterp σ ns obs nt =
      stA g π img M Ψ σ := rfl

/-- **`wpA g π w Ψ s Φ`**: hart `w.h`'s weakest precondition at program state `s` (iris-lean's `WP` of its
thread in the concurrent language). -/
def wpA [InvGS_gen hlc GF] (g : AGN) (π : Proto) (w : HW P D V) (Ψ : Nat → Trace → Prop) (s : P)
    (Φ : V → IProp GF) : IProp GF :=
  letI : IrisGS_gen hlc (CExpr P D V) GF := aIrisGS g π w.img w.M Ψ
  WP (CExpr.run w s) @ Stuckness.MaybeStuck; ⊤ {{ Φ }}

/-- THE FRONTIER RULE at pre-state `ws` (plan §3): every `t ≤ WF(ws)` is shot, and `Valid(WF(ws))` (or doom). -/
def frontA (g : AGN) (π : Proto) (img : Image) (M : List PMsg) (ws : PState) : IProp GF :=
  iprop(□ (∀ t, ⌜1 ≤ t ∧ t ≤ M.length ∧ t ≤ wfr ws⌝ → shot g t) ∗ (⌜Valid π img M (wfr ws)⌝ ∨ dshot g))

instance (g : AGN) (π : Proto) (img : Image) (M : List PMsg) (ws : PState) :
    Persistent (frontA (GF := GF) g π img M ws) := by unfold frontA; infer_instance

end si

/-! ## 3. Pure lemmas of the state interpretation -/

/-- `Valid` from `protoOk` of every timestamp up to `V` (strong induction, as `validInduction`). -/
theorem valid_of_protoOk {π : Proto} {img : Image} {M : List PMsg} {V : Nat} (himg : π.okImg img)
    (hp : ∀ t, 1 ≤ t → t ≤ min V M.length → protoOk π img M t) : Valid π img M V := by
  have key : ∀ k, k ≤ min V M.length → Valid π img M k := by
    intro k
    induction k with
    | zero => intro _; exact ⟨himg, fun t h1 h2 => by omega⟩
    | succ k ih =>
      intro hk
      refine ⟨himg, fun t h1 h2 m hm => ?_⟩
      by_cases ht : t ≤ k
      · exact (ih (by omega)).2 t h1 (by omega) m hm
      · have : t = k + 1 := by omega
        subst this
        exact hp (k + 1) h1 hk m hm (by simpa using ih (by omega))
  have := key (min V M.length) (Nat.le_refl _)
  exact ⟨this.1, fun t h1 h2 m hm => this.2 t h1 (by omega) m hm⟩

/-- The frontier's pure part: the claim `fOk` and the facts give `Valid(WF)`. -/
theorem valid_front {π : Proto} {img : Image} {M : List PMsg} {Ψ : Nat → Trace → Prop} {n : Nat} {σ : CSt}
    {h : Nat} (hf : cFacts π img M Ψ n σ) (hout : ∀ k, n ≤ k → (σ k).2.2 = []) (hok : fOk M σ h) :
    Valid π img M (wfr (σ h).1) := by
  refine valid_of_protoOk hf.1 (fun t h1 h2 => ?_)
  obtain ⟨k, e, he, het⟩ := hok t h1 (by omega) (by omega)
  have hk : k < n := by
    apply Classical.byContradiction; intro hk
    rw [hout k (by omega)] at he; cases he
  exact (hf.2 k hk).2.1 e he t het

/-- `cFacts` survive a step that proves `stepOk`. -/
theorem cFacts_step {π : Proto} {img : Image} {M : List PMsg} {Ψ : Nat → Trace → Prop} {n : Nat} {σ : CSt}
    {h : Nat} {l : PLabel} {ots : Option Nat} {ws' : PState} {pr' : GSet Nat}
    (hf : cFacts π img M Ψ n σ) (hh : h < n)
    (hm : memStep img M h (σ h).2.1 (σ h).1 l ots ws' pr')
    (hok : stepOk π img M (Ψ h) (σ h).1 (σ h).2.2 l ots) :
    cFacts π img M Ψ n (updS σ h (ws', pr', (σ h).2.2 ++ [(l, ots)])) := by
  refine ⟨hf.1, fun k hk => ?_⟩
  by_cases e : k = h
  · subst e
    rw [updS_self]
    obtain ⟨hΨ, hp, hfi, hfk⟩ := hf.2 k hk
    have hfw := fwd_step hm hfi hfk hok.2
    refine ⟨fun j => ?_, fun e he t het => ?_, hfw.1, hfw.2⟩
    · by_cases hj : j ≤ (σ k).2.2.length
      · rw [List.take_append_of_le_length hj]; exact hΨ j
      · rw [List.take_of_length_le (by simp; omega)]; exact hok.1
    · rcases List.mem_append.1 he with he | he
      · exact hp e he t het
      · rw [List.mem_singleton] at he; subst he
        simp only at het; subst het
        exact protoOk_of_grd (fulPv_lt hm) (hok.2 t rfl)
  · rw [updS_ne σ _ e]; exact hf.2 k hk

/-- `hartFacts` (CoreWp.lean) of one hart from `cFacts`. -/
theorem hartFacts_of {π : Proto} {img : Image} {M : List PMsg} {Ψ : Nat → Trace → Prop} {n : Nat} {σ : CSt}
    {h : Nat} (hf : cFacts π img M Ψ n σ) (hh : h < n) : hartFacts π img M (Ψ h) (σ h) := by
  obtain ⟨hΨ, hp, hfi, hfk⟩ := hf.2 h hh
  obtain ⟨V, hV⟩ := hΨ (σ h).2.2.length
  rw [List.take_length] at hV
  exact ⟨⟨V, hV⟩, hp, hfi, hfk⟩

/-- The claim of every other hart survives a step. -/
theorem fOk_updS {M : List PMsg} {σ : CSt} {h k : Nat} {ws' : PState} {pr' : GSet Nat} {e : PEv}
    (hok : fOk M σ k) (hk : k ≠ h) : fOk M (updS σ h (ws', pr', (σ h).2.2 ++ [e])) k := by
  unfold fOk
  rw [updS_ne σ _ hk]
  exact stageGe_updS hok

/-- A newly fulfilled timestamp is the step's. -/
theorem fulAt_updS_inv {σ : CSt} {h : Nat} {ws' : PState} {pr' : GSet Nat} {l : PLabel} {ots : Option Nat}
    {t : Nat} (hf : fulAt (updS σ h (ws', pr', (σ h).2.2 ++ [(l, ots)])) t) : fulAt σ t ∨ ots = some t := by
  obtain ⟨k, e, he, het⟩ := hf
  by_cases hk : k = h
  · subst hk
    rw [updS_self] at he
    rcases List.mem_append.1 he with he | he
    · exact .inl ⟨k, e, he, het⟩
    · rw [List.mem_singleton] at he; subst he; exact .inr het
  · rw [updS_ne σ _ hk] at he; exact .inl ⟨k, e, he, het⟩

/-! ## 4. The lifting lemma -/

section lift

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [InvGS_gen hlc GF]

/-- Access to one hart's ghost in the state interpretation's big separating conjunction. -/
theorem harts_acc (hn : List GName) (σ : CSt) (h : Nat) (hh : h < hn.length) :
    ([∗list] k ↦ γ ∈ hn, ghost_var (GF := GF) γ (.own (1 : Qp).half) (σ k)) ⊢
      ghost_var (hn.getD h 0) (.own (1 : Qp).half) (σ h) ∗
      ∀ x, ghost_var (hn.getD h 0) (.own (1 : Qp).half) x -∗
        [∗list] k ↦ γ ∈ hn, ghost_var γ (.own (1 : Qp).half) (updS σ h x k) := by
  have hget : hn[h]? = some (hn.getD h 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hh]; rfl
  iintro H
  icases BigSepL.bigSepL_lookup_acc_impl (Φ := fun k γ => ghost_var (GF := GF) γ (.own (1 : Qp).half) (σ k)) hget
    $$ H with ⟨Hc, Hclose⟩
  iframe Hc
  iintro %x Hx
  iapply Hclose $$ %(fun k γ => ghost_var (GF := GF) γ (.own (1 : Qp).half) (updS σ h x k))
  · imodintro
    iintro %j %y %_ %hne Hy
    dsimp only
    rw [updS_ne σ x hne]
    iexact Hy
  · dsimp only
    rw [updS_self]
    iexact Hx

/-- **THE LIFTING LEMMA of track (a)** (plan §7: the statement shape of `wpHart_lift`): from `hartA`, the hart may
take any step its program half and machine v2 allow; one `▷` for the step, `£ 1` for the continuation.  On a label
step the client is handed the pre-state facts (`hartFacts`, or doom) and THE FRONTIER RULE at the pre-state
(`frontA`), and returns the step's obligation `stepOk` (or doom), `shot g t` for a fulfil at `t`, and the
continuation.  On the value step it proves `Φ v`. -/
theorem wpA_lift {g : AGN} {π : Proto} {w : HW P D V} {Ψ : Nat → Trace → Prop} {s : P} {Φ : V → IProp GF}
    {ws : PState} {pr : GSet Nat} {τ : Trace} :
    hartA g w.h ws pr τ ∗
    ▷ ((∀ v, ⌜w.pdone s = some v⌝ -∗ hartA g w.h ws pr τ -∗ |={⊤}=> Φ v) ∧
       (∀ l ots s' ws' pr', ⌜anyFab w.pstep s () l s' ()⌝ -∗ ⌜memStep w.img w.M w.h pr ws l ots ws' pr'⌝ -∗
          (⌜hartFacts π w.img w.M (Ψ w.h) (ws, pr, τ)⌝ ∨ dshot g) -∗ frontA g π w.img w.M ws -∗ £ 1 -∗
          |={⊤}=> (⌜stepOk π w.img w.M (Ψ w.h) ws τ l ots⌝ ∨ dshot g) ∗ (∀ t, ⌜ots = some t⌝ → shot g t) ∗
            (hartA g w.h ws' pr' (τ ++ [(l, ots)]) -∗ wpA g π w Ψ s' Φ)))
    ⊢ wpA g π w Ψ s Φ := by
  letI : IrisGS_gen hlc (CExpr P D V) GF := aIrisGS g π w.img w.M Ψ
  show _ ⊢ WP (CExpr.run w s) @ Stuckness.MaybeStuck; ⊤ {{ Φ }}
  iintro ⟨Hst, Hk⟩
  unfold hartA
  icases Hst with ⟨%hh, Hst⟩
  iapply wp_lift_step (rfl : toVal (CExpr.run w s : CExpr P D V) = none)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rw [aStateI_eq]
  unfold stA
  icases Hσ with ⟨Hbig, %Hout, %Hok, #Hshots, #Hfacts⟩
  icases harts_acc (GF := GF) g.hn σ₁ w.h hh $$ Hbig with ⟨Hγ, Hclose⟩
  ihave %Heq := ghost_var_agree _ _ _ _ _ $$ Hγ Hst
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  isplit
  · ipureintro; trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  change cstep _ _ _ at Hstep
  cases Hstep with
  | lab _ _ _ l ots s' ws' pr' d d' hp hm hfok =>
    have hτ : (σ₁ w.h).2.2 = τ := by rw [Heq]
    rw [Heq] at hm
    icases Hk with ⟨-, Hk⟩
    imod Hmask
    -- the pre-state facts and the frontier
    ihave Hpre : (⌜hartFacts π w.img w.M (Ψ w.h) (ws, pr, τ)⌝ ∨ dshot g) $$ []
    · icases Hfacts with (%Hf | #Hd)
      · ileft; ipureintro; have := hartFacts_of Hf hh; rw [Heq] at this; exact this
      · iright; iexact Hd
    ihave Hfront : frontA g π w.img w.M ws $$ []
    · unfold frontA
      isplitl []
      · imodintro
        iintro %t %ht
        iapply Hshots
        ipureintro
        refine ⟨ht.1, ht.2.1, ?_⟩
        have := Hok w.h t ht.1 ht.2.1
        rw [Heq] at this
        exact this ht.2.2
      · icases Hfacts with (%Hf | #Hd)
        · ileft; ipureintro
          have := valid_front Hf Hout (Hok w.h)
          rw [Heq] at this; exact this
        · iright; iexact Hd
    imod Hk $$ %l %ots %s' %ws' %pr' %⟨d, d', hp⟩ %hm Hpre Hfront Hcred with ⟨Hstep, #Hsh, Hk⟩
    imod ghost_var_update_halves ((ws', pr', τ ++ [(l, ots)]) : HSt) _ _ _ $$ Hγ Hst with ⟨Hγ, Hst⟩
    imodintro
    rw [aStateI_eq]
    unfold stA
    have hout' : ∀ k, g.hn.length ≤ k →
        (updS σ₁ w.h (ws', pr', (σ₁ w.h).2.2 ++ [(l, ots)]) k).2.2 = [] := by
      intro k hk
      rw [updS_ne σ₁ _ (by omega)]; exact Hout k hk
    have hok' : ∀ k, fOk w.M (updS σ₁ w.h (ws', pr', (σ₁ w.h).2.2 ++ [(l, ots)])) k := by
      intro k
      by_cases hk : k = w.h
      · subst hk; exact hfok
      · exact fOk_updS (Hok k) hk
    isplitl [Hγ Hclose Hstep]
    · isplitl [Hγ Hclose]
      · rw [hτ]; iapply Hclose $$ Hγ
      isplitr
      · ipureintro; exact hout'
      isplitr
      · ipureintro; exact hok'
      isplitr [Hstep]
      · imodintro
        iintro %t %ht
        rcases fulAt_updS_inv ht.2.2 with hf | hf
        · iapply Hshots; ipureintro; exact ⟨ht.1, ht.2.1, hf⟩
        · iapply Hsh; ipureintro; exact hf
      · icases Hstep with (%Hs | #Hd)
        · icases Hfacts with (%Hf | #Hd)
          · ileft; ipureintro
            have := cFacts_step (l := l) (ots := ots) (ws' := ws') (pr' := pr') Hf hh
              (by rw [Heq]; exact hm) (by rw [Heq]; exact Hs)
            exact this
          · iright; iexact Hd
        · iright; iexact Hd
    isplitl [Hk Hst]
    · dsimp only [wpA]
      iapply Hk
      iframe Hst
      ipureintro; exact hh
    · exact BigSepL.bigSepL_nil_intro
  | fin _ _ _ v hv =>
    icases Hk with ⟨Hk, -⟩
    imod Hmask
    imod Hk $$ %v %hv [Hst] with Hv
    · iframe Hst; ipureintro; exact hh
    imodintro
    rw [aStateI_eq]
    unfold stA
    isplitl [Hγ Hclose]
    · isplitl [Hγ Hclose]
      · ihave H := Hclose $$ Hγ
        rw [updS_same]
        iexact H
      iframe Hshots Hfacts
      ipureintro; exact ⟨Hout, Hok⟩
    isplitl [Hv]
    · iapply (wp_value_fupd' (v := v)).2
      imodintro
      iexact Hv
    · exact BigSepL.bigSepL_nil_intro

end lift

end Weak.Prom.OA
