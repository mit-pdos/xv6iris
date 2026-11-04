/-
Weak/Prom: **no havoc run, outstanding own promises included** (HavocProm, 2026-11-04; owner ruling [OWN.P10],
~/dev/weak-orch/promising/context.md item 17: "a run in which a hart reaches a Sail error while one of its own
promises is still outstanding also counts as havoc (any outcome) — WEAKER, sound; proofs must show no error is
reachable in such runs too"; MachHavoc.lean `havocRun`/`havocs`; plan rev 7 §0 A0).

## Why CoreHavoc.lean's premises are not enough

`adequacyH`'s per-hart wps finish an error node with `⟦V⟧ False` for SOME `V`.  On a valid run that is refuted by
`Valid π img M |M|` (A0 (iv)).  On a havoc run of [OWN.P10] the erroring hart's own promise `t` is never
fulfilled, so `protoOk t` is never established and `Valid` may fail from `t` on: a hart that refutes its error
branch only by a guard covering its own unfulfilled promise proves nothing about such a run.  Concretely (LB
shape, π: `x = 42` and `y = 1` violate the protocol): A `r := y; if r = 1 then error`; B `r := x; if r = 42 then
y := 1`.  A promises `x = 42`, B reads it and writes `y = 1`, A reads `y = 1` and errors with its promise
outstanding — a havoc run (after the error A "may do anything", including that store; RVWMO allows the LB
cycle), while both harts' wps hold (each refutes its branch by `⟦t⟧ False` with `t ≥` A's promise).

## The obligation here

`wpPFH` is `wpPF` whose postcondition may name the hart's ghost name `γ`; `ΦHP` returns the hart's state
`hartSt γ ws pr τ` with `QE`: at a value `some v` the A0 postcondition, at an error node (`none`, CoreHavoc.lean
`pdoneE`) `errOk pr` — `⟦V⟧ False` with `V` BELOW EVERY OWN OUTSTANDING PROMISE (`∀ t ∈ pr, V < t`).  On a
valid run `pr = ∅` and this is CoreHavoc.lean's obligation (`wpPF_of_wpPFH`: the same hart proofs feed
`adequacyH`).

## `noHavoc_of_adequacyHP`

No havoc run exists.  Proof: every reachable configuration separates (`reach_soloD`, the promises-first
factorization `sim` of MachFactor.lean needs no `noPromises`); every message that no agent still promises was
fulfilled by its author (`solo_fulfils`), whose step invariant gives its `protoOk`; so `Valid` holds below the
least outstanding timestamp `t₀` (`valid_of_protoOk`).  `t₀`'s author is at an error node (`promsAtErr`) and its
`errOk` guard is `< t₀`: contradiction.  With no outstanding promise at all, any erroring hart's guard is
refuted by `Valid` at every `V`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreHavoc

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Iris.ProgramLogic.Language Iris.ProgramLogic.Language.Notation

variable {P D V : Type}

/-! ## 1. Every reachable configuration separates -/

/-- The state phase of any run from `pmInit` (MachSolo.lean `validRun_statePhase` without `noPromises`). -/
theorem reach_statePhase {pstep : P → D → PLabel → P → D → Prop} {img : Image} {d0 : D}
    {ps : List P} {evs : List PEvt} {cfg : PCfg P D} (hrun : pmSteps pstep (pmInit img d0 ps) evs cfg) :
    ∃ c0 : PCfg P D, c0.pcImg = img ∧ c0.pcLog = cfg.pcLog ∧ c0.pcDev = d0 ∧
      (∀ i p, ps[i]? = some p → ∃ ag, c0.pcAgs[i]? = some ag ∧ ag.paSt = p ∧ ag.paWs = psInit ∧
        ∀ t, t ∈ ag.paProm ↔ 0 < t ∧ ownTs cfg.pcLog i t) ∧
      pmSteps pstep c0 (evs.filter PEvt.isSt) cfg := by
  have hwf := pmSteps_wf hrun (pmInit_wf img d0 ps)
  have hlen := pmSteps_len hrun
  obtain ⟨c0', hp, himg, hlog, hdev, hlen', hags⟩ := promsRun (pstep := pstep) cfg.pcLog
    (pmInit img d0 ps) (fun m hm => by rw [← hlen]; exact hwf.2 m hm)
  have hfr : FRel cfg.pcLog (pmInit img d0 ps) c0' := by
    refine ⟨himg, by rw [hlog]; rfl, hdev, List.nil_prefix, hlen', fun i ag hi => ?_⟩
    obtain ⟨ag', h1, h2, h3, h4⟩ := hags i ag hi
    exact ⟨ag', h1, h2, h3, fun t => by rw [h4 t]; rfl⟩
  obtain ⟨c'', hs, hfr''⟩ := sim hrun (pmInit_wf img d0 ps) rfl hfr
  have he := FRel_final hfr'' rfl
  subst he
  refine ⟨c0', himg, by rw [hlog]; rfl, hdev, fun i p hpi => ?_, hs⟩
  have hi : (pmInit img d0 ps).pcAgs[i]? = some ⟨p, psInit, ∅⟩ := by
    simp only [pmInit, List.getElem?_map, hpi, Option.map_some]
  obtain ⟨ag', h1, h2, h3, h4⟩ := hags i _ hi
  refine ⟨ag', h1, h2, h3, fun t => ?_⟩
  rw [h4 t]
  simp only [pmInit, List.length_nil, List.nil_append]
  constructor
  · rintro (h | h)
    · exact absurd h notElemOfEmpty
    · exact h
  · exact .inr

/-- EVERY REACHABLE CONFIGURATION SEPARATES, any fabric (CoreRun.lean `validRun_soloD` without `noPromises`). -/
theorem reach_soloD {pstep : P → D → PLabel → P → D → Prop} {img : Image} {d0 : D} {ps : List P}
    {evs : List PEvt} {cfg : PCfg P D} (h : pmSteps pstep (pmInit img d0 ps) evs cfg) :
    ∀ hh p, ps[hh]? = some p → ∃ ag, cfg.pcAgs[hh]? = some ag ∧ ∃ P0 : GSet Nat,
      (∀ t, t ∈ P0 ↔ 0 < t ∧ ownTs cfg.pcLog hh t) ∧
      soloSteps (anyFab pstep) img cfg.pcLog hh (p, psInit, P0) (traceOf hh evs) (ag.paSt, ag.paWs, ag.paProm) := by
  intro hh p hp
  obtain ⟨c0, himg, hlog, _, hags, hs⟩ := reach_statePhase h
  obtain ⟨ag0, h1, h2, h3, h4⟩ := hags hh p hp
  obtain ⟨ag'', k1, k2⟩ := sepD hs (filter_isSt evs) hlog hh ag0 h1
  refine ⟨ag'', k1, ag0.paProm, h4, ?_⟩
  rw [himg, h2, h3, traceOf_filter] at k2
  exact k2

/-! ## 2. Bounded `Valid` and least elements -/

/-- `Valid` up to `V` from `protoOk` of every timestamp `1 ≤ t ≤ V` (CoreDefs.lean `validInduction`, bounded). -/
theorem valid_of_protoOk {π : Proto} {img : Image} {M : List PMsg} (himg : PO_img π img) :
    ∀ V, (∀ t, 1 ≤ t → t ≤ V → protoOk π img M t) → Valid π img M V := by
  intro V
  induction V with
  | zero => intro _; exact ⟨himg, fun t h1 h2 => by omega⟩
  | succ V ih =>
    intro hp
    have hV := ih (fun t h1 h2 => hp t h1 (by omega))
    refine ⟨himg, fun t h1 h2 m hm => ?_⟩
    by_cases ht : t ≤ V
    · exact hV.2 t h1 (by omega) m hm
    · have htV : t = V + 1 := by omega
      subst htV
      exact hp (V + 1) h1 (Nat.le_refl _) m hm (by simpa using hV)

/-- A least witness (classical). -/
theorem nat_least {p : Nat → Prop} : ∀ n k, k ≤ n → p k → ∃ j, p j ∧ ∀ m, m < j → ¬ p m := by
  intro n
  induction n with
  | zero => intro k hk hp; exact ⟨k, hp, fun m hm _ => by omega⟩
  | succ n ih =>
    intro k hk hp
    by_cases h : ∃ m, m < k ∧ p m
    · obtain ⟨m, hm, hpm⟩ := h
      exact ih m (by omega) hpm
    · exact ⟨k, hp, fun m hm hpm => h ⟨m, hm, hpm⟩⟩

/-! ## 3. The hart wp with its state in the postcondition -/

section wp

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt]

/-- `wpPFH`: `wpPF` (CoreWp.lean) whose postcondition may name the hart's ghost name. -/
def wpPFH [InvGS_gen hlc GF] (π : Proto) (w : HW P D V) (Ψ : Trace → Prop) (s : P)
    (Φ : GName → V → IProp GF) : IProp GF :=
  iprop(∀ (γ : GName) (P0 : GSet Nat), ⌜∀ t, t ∈ P0 ↔ 0 < t ∧ ownTs w.M w.h t⌝ -∗
    hartSt γ psInit P0 [] -∗ wpH γ π w Ψ s (Φ γ))

/-- The postcondition "the hart's state, whose promise set meets `Q v`". -/
def postQ (Q : V → GSet Nat → Prop) : GName → V → IProp GF :=
  fun γ v => iprop(∃ (ws : PState) (pr : GSet Nat) (τ : Trace), hartSt γ ws pr τ ∗ ⌜Q v pr⌝)

end wp

/-- THE ERROR OBLIGATION ([OWN.P10]): `⟦V⟧ False` with `V` below every own outstanding promise. -/
def errOk (π : Proto) (img : Image) (M : List PMsg) (pr : GSet Nat) : Prop :=
  ∃ V, (∀ t, t ∈ pr → V < t) ∧ grd π img M V False

/-- The postcondition with error nodes (`pdoneE`): A0's at a value, `errOk` at an error node. -/
def QE (π : Proto) (img : Image) (M : List PMsg) (Φ : Nat → V → Prop) (h : Nat) : Option V → GSet Nat → Prop
  | some v, _ => ∃ V, grd π img M V (Φ h v)
  | none, pr => errOk π img M pr

/-- The hart postcondition of `noHavoc_of_adequacyHP`. -/
abbrev ΦHP {GF : BundledGFunctors} [GhostVarG GF HSt] (π : Proto) (img : Image) (M : List PMsg)
    (Φ : Nat → V → Prop) (h : Nat) : GName → Option V → IProp GF :=
  postQ (QE π img M Φ h)

section adeq

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGpreS GF] [GhostVarG GF HSt]

/-- `wpPFH` with `ΦHP` gives CoreHavoc.lean's per-hart premise (`errOk` drops its bound). -/
theorem wpPF_of_wpPFH [InvGS_gen hlc GF] {π : Proto} {w : HW P D (Option V)} {Ψ : Trace → Prop} {s : P}
    {Φ : Nat → V → Prop} {h : Nat} :
    wpPFH π w Ψ s (ΦHP (GF := GF) π w.img w.M Φ h) ⊢
      wpPF π w Ψ s (fun v => iprop(⌜∃ V, grd π w.img w.M V (ΦE Φ h v)⌝)) := by
  have key : ∀ (γ : GName) (v : Option V), ΦHP (GF := GF) π w.img w.M Φ h γ v ⊢
      iprop(⌜∃ V, grd π w.img w.M V (ΦE Φ h v)⌝) := by
    intro γ v
    unfold ΦHP postQ
    iintro ⟨%ws, %pr, %τ, -, %hq⟩
    ipureintro
    cases v with
    | none => obtain ⟨V', _, hg⟩ := hq; exact ⟨V', hg⟩
    | some v => exact hq
  unfold wpPFH wpPF
  iintro H %γ %P0 %hP0 Hst
  ihave Hw := H $$ %γ %P0 %hP0 Hst
  dsimp only [wpH]
  letI : IrisGS_gen hlc (HExpr P D (Option V)) GF := pfIrisGS γ π w.img w.M Ψ
  iapply (wp_mono (key γ))
  iexact Hw

/-- **PER-HART ADEQUACY, with the hart's state in the postcondition** (CoreAdeq.lean `hart_adequate`): after any
thread run, the step invariant holds, and a reached value meets `Q` together with the hart's FINAL promise set. -/
theorem hart_adequateP {π : Proto} {w : HW P D V} {Ψ : Trace → Prop} {s0 : P} {Q : V → GSet Nat → Prop}
    {P0 : GSet Nat}
    (hP0 : ∀ t, t ∈ P0 ↔ 0 < t ∧ ownTs w.M w.h t) (hΨ0 : Ψ [])
    (hwp : ∀ [InvGS_gen hlc GF], ⊢@{IProp GF} wpPFH π w Ψ s0 (postQ Q))
    {n : Nat} {κs : List Unit} {es : List (HExpr P D V)} {σ : HSt}
    (hsteps : NSteps n ([HExpr.run w s0], (psInit, P0, [])) κs (es, σ)) :
    hartFacts π w.img w.M Ψ σ ∧ ∀ v, es = [HExpr.ret v] → Q v σ.2.1 := by
  refine wp_strong_adequacy_gen (hlc := hlc) (GF := GF) Stuckness.MaybeStuck [HExpr.run w s0]
    (psInit, P0, []) n κs es σ _ (fun _ => 0) ?_ hsteps
  intro Hinv
  have hw := @hwp Hinv
  iintro
  imod ghost_var_alloc ((psInit, P0, []) : HSt) with ⟨%γ, H⟩
  have hs := ghost_var_split (GF := GF) γ ((psInit, P0, []) : HSt) (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hs
  ihave ⟨H1, H2⟩ := hs $$ H
  imodintro
  iexists (fun σ _ _ _ => hartInterp (GF := GF) γ π w.img w.M Ψ σ), [postQ (GF := GF) Q γ],
    (fun _ => iprop(True)), (fun _ _ _ _ => fupd_intro)
  dsimp only
  isplitl [H1]
  · unfold hartInterp
    iframe H1
    ipureintro
    exact ⟨⟨0, fun _ => hΨ0⟩, fun e he => (by cases he), Nat.le_refl _,
      fun a tf vf h => (by rw [show psInit.wFwd = ∅ from rfl, lookupEmpty] at h; cases h)⟩
  isplitl [H2]
  · iapply BigSepL2.bigSepL2_singleton.2
    ihave Hw := hw
    unfold wpPFH
    ihave Hw := Hw $$ %γ %P0 %hP0
    unfold hartSt
    ihave Hw := Hw $$ H2
    dsimp only [wpH]
    iexact Hw
  iintro %es' %t2' %Heq %Hlen %_ Hσ Hpost _
  unfold hartInterp
  icases Hσ with ⟨Hγ, %Hf⟩
  obtain ⟨e, rfl⟩ : ∃ e, es' = [e] := List.length_eq_one_iff.1 (by simpa using Hlen)
  ihave Hpost := BigSepL2.bigSepL2_singleton.1 $$ Hpost
  cases e with
  | run w' s' =>
    iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
    ipureintro
    refine ⟨Hf, fun v hv => ?_⟩
    rw [Heq] at hv
    simp at hv
  | ret v0 =>
    dsimp only [ToVal.toVal, HExpr.toV, Option.elim]
    try unfold postQ
    icases Hpost with ⟨%ws, %pr, %τ, Hst, %Hq⟩
    unfold hartSt
    ihave %Hag := ghost_var_agree γ _ _ _ _ $$ Hγ Hst
    iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
    ipureintro
    refine ⟨Hf, fun v hv => ?_⟩
    rw [Heq] at hv
    simp only [List.cons_append, List.nil_append, List.cons.injEq, HExpr.ret.injEq] at hv
    rw [← hv.1, Hag]; exact Hq

/-- **NO HAVOC RUN** ([OWN.P10]; MachHavoc.lean `havocs`, `forbiddenH_iff`): if every final memory admits the
per-hart wps with error nodes (`pdoneE`) and the bounded error obligation (`ΦHP`/`errOk`), no run reaches an error
node with every outstanding promise at an error node — in particular no valid run reaches one, and no run in which
a hart errs with its own promise outstanding exists. -/
theorem noHavoc_of_adequacyHP {pstep : P → D → PLabel → P → D → Prop} {perr : P → Prop}
    {pdone : P → Option V} {img : Image} {d0 : D} {ps : List P}
    (π : Proto) (Φ : Nat → V → Prop) (Ψ : Nat → Trace → Prop)
    (himg : PO_img π img) (hΨ0 : ∀ h, Ψ h [])
    (hwp : ∀ M, ∀ h p, ps[h]? = some p → ∀ [InvGS_gen hlc GF],
      ⊢@{IProp GF} wpPFH π ⟨pstep, pdoneE perr pdone, img, M, h⟩ (Ψ h) p (ΦHP π img M Φ h)) :
    ¬ havocs pstep perr img d0 ps := by
  rintro ⟨evs, cfg, hrun, hpa, ⟨ie, age, hage, hpe⟩⟩
  have hlen : cfg.pcAgs.length = ps.length := by rw [pmSteps_len hrun]; simp [pmInit]
  have hdom : ∀ (i : Nat) (ag : PAgent P), cfg.pcAgs[i]? = some ag → ∃ p, ps[i]? = some p := by
    intro i ag hag
    have hil : i < ps.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hag).1
    exact ⟨_, List.getElem?_eq_getElem hil⟩
  -- the step invariant of every hart of the domain at the end of its solo run
  have hfacts : ∀ i p, ps[i]? = some p → ∃ ag, cfg.pcAgs[i]? = some ag ∧ ∃ P0 : GSet Nat,
      (∀ t, t ∈ P0 ↔ 0 < t ∧ ownTs cfg.pcLog i t) ∧
      (∀ t, t ∈ (traceOf i evs).filterMap (fun e => e.2) ↔ t ∈ P0 ∧ t ∉ ag.paProm) ∧
      ∀ e ∈ traceOf i evs, ∀ t, e.2 = some t → protoOk π img cfg.pcLog t := by
    intro i p hp
    obtain ⟨ag, hag, P0, hP0, hs⟩ := reach_soloD hrun i p hp
    obtain ⟨_, hm, _⟩ := solo_fulfils hs
    have hn := solo_nsteps (w := ⟨pstep, pdoneE perr pdone, img, cfg.pcLog, i⟩) hs [] 0 [] _ (.refl _)
    have := hart_adequateP (hlc := hlc) (GF := GF) (w := ⟨pstep, pdoneE perr pdone, img, cfg.pcLog, i⟩)
      (Q := QE π img cfg.pcLog Φ i) hP0 (hΨ0 i) (fun {_} => hwp cfg.pcLog i p hp) hn
    refine ⟨ag, hag, P0, hP0, hm, fun e he t het => this.1.2.1 e (by simpa using he) t het⟩
  -- an erroring hart's bounded guard
  have herr : ∀ (i : Nat) (ag : PAgent P), cfg.pcAgs[i]? = some ag → perr ag.paSt → errOk π img cfg.pcLog ag.paProm := by
    intro i ag hag hpe
    obtain ⟨p, hp⟩ := hdom i ag hag
    obtain ⟨ag', hag', P0, hP0, hs⟩ := reach_soloD hrun i p hp
    rw [hag] at hag'; cases hag'
    have hfin : hstep (HExpr.run (⟨pstep, pdoneE perr pdone, img, cfg.pcLog, i⟩ : HW P D (Option V)) ag.paSt,
        ((ag.paWs, ag.paProm, [] ++ traceOf i evs) : HSt)) [] (HExpr.ret none, _, []) :=
      .fin _ _ _ none (pdoneE_err hpe)
    have hS : Language.Step
        ([HExpr.run (⟨pstep, pdoneE perr pdone, img, cfg.pcLog, i⟩ : HW P D (Option V)) ag.paSt],
          ((ag.paWs, ag.paProm, [] ++ traceOf i evs) : HSt)) []
        ([HExpr.ret none], ((ag.paWs, ag.paProm, [] ++ traceOf i evs) : HSt)) := by
      simpa using Language.Step.atomic
        (Λ := (inferInstance : Language (HExpr P D (Option V)) HSt Unit (Option V))) hfin [] []
    have hn := solo_nsteps (w := ⟨pstep, pdoneE perr pdone, img, cfg.pcLog, i⟩) hs [] 1 [] _
      (by simpa using NSteps.cons hS (.refl _))
    have := hart_adequateP (hlc := hlc) (GF := GF) (w := ⟨pstep, pdoneE perr pdone, img, cfg.pcLog, i⟩)
      (Q := QE π img cfg.pcLog Φ i) hP0 (hΨ0 i) (fun {_} => hwp cfg.pcLog i p hp) hn
    exact this.2 none rfl
  -- a timestamp no agent still promises meets its protocol (its author fulfilled it)
  have hok : ∀ t, (∀ (i : Nat) (ag : PAgent P), cfg.pcAgs[i]? = some ag → t ∉ ag.paProm) → protoOk π img cfg.pcLog t := by
    intro t hno m hm
    cases t with
    | zero => cases hm
    | succ k =>
      have hmk : cfg.pcLog[k]? = some m := hm
      have hwf := pmSteps_wf hrun (pmInit_wf img d0 ps)
      obtain ⟨_, i, hti, hil⟩ := hwf.2 m (List.mem_of_getElem? hmk)
      rw [hlen] at hil
      obtain ⟨p, hp⟩ : ∃ p, ps[i]? = some p := ⟨_, List.getElem?_eq_getElem hil⟩
      obtain ⟨ag, hag, P0, hP0, hm', hpk⟩ := hfacts i p hp
      have hin : k + 1 ∈ (traceOf i evs).filterMap (fun e => e.2) :=
        (hm' (k + 1)).2 ⟨(hP0 (k + 1)).2 ⟨by omega, m, by simpa using hmk, hti⟩, hno i ag hag⟩
      obtain ⟨e, he, het⟩ := List.mem_filterMap.1 hin
      exact hpk e he (k + 1) het m hm
  by_cases hex : ∃ t, ∃ (i : Nat) (ag : PAgent P), cfg.pcAgs[i]? = some ag ∧ t ∈ ag.paProm
  · -- the author of the least outstanding timestamp is at an error node; its guard is below it
    obtain ⟨t1, ht1⟩ := hex
    obtain ⟨t0, ⟨i0, ag0, hag0, ht0⟩, hmin⟩ := nat_least
      (p := fun t => ∃ (i : Nat) (ag : PAgent P), cfg.pcAgs[i]? = some ag ∧ t ∈ ag.paProm) t1 t1 (Nat.le_refl _) ht1
    obtain ⟨V', hlt, hg⟩ := herr i0 ag0 hag0 (hpa i0 ag0 t0 hag0 ht0)
    have hV := hlt t0 ht0
    refine hg (valid_of_protoOk himg V' (fun t _ h2 => hok t (fun i ag hag ht => ?_)))
    exact hmin t (by omega) ⟨i, ag, hag, ht⟩
  · -- no outstanding promise: the erroring hart's guard is refuted at every `V`
    obtain ⟨V', _, hg⟩ := herr ie age hage hpe
    exact hg (valid_of_protoOk himg V' (fun t _ _ => hok t (fun i ag hag ht => hex ⟨t, i, ag, hag, ht⟩)))

end adeq

end Weak.Prom.PF
