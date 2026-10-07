/-
Weak: **concrete models of surface v2's abstract condition `Cond`** (`AxLeafS4`), and which
surface laws each one satisfies (AxSL tier).

Rocq: `iris/AxCondM.v` @ xxvzwolszwmp.

## The Rocq header, in substance

(P) `AxCondM.condP C := ⌜C⌝` (pure): every surface-v2 law holds, including the gate
(`condPGate`, `condPGate3`).  The cost: the protocol's load rules would have to hand the
continuation the graph value of an owned read in PHASE 1 — exactly what the demonic-read design
refuses; so at `condP` the leaves are real but the load/AMO rules are not provable from
`prot_inv`.
(A) `condA i C` (annotation-backed): a list `L` of (event, pure fact) pairs of hart `i`, the
fragments `e ↦ₐ ⌜φ_e⌝` for them, and `⌜(∧ φ_e) → C⌝`.  A load's flow produces `condA i φ`
from the fragment it allocates for its own event (`condAFrag`), and the row-end post READS IT
BACK (`condARb`, via `annotAgree` at `postLifting`).  Proved: `condAAnd`, `condAMono`,
`condAIntro`, `condAFrag`, `condARb`, `condATrue`.  NOT satisfied: `Cond_pers` (a fragment is
exclusive, and at `postLifting` only a fragment relates `na !! e` to a known proposition, under
`==∗` only — so an annotation-backed `Cond` is AFFINE; surface v3 = `AxCondM3` uses a gate that
RETURNS the condition), and `Cond_gate` (`condAGateTrivializes`: a fragment of `⌜False⌝`
proves every gated goal — a phase-1 use of a phase-2 fact).  The missing adequacy fact is named,
not proved: `condGateAdequacy`.  §ga2: the instance premises (`annEq` for `condA`, graph
agreement for AxCondM2/3) hold at the tier-A instance `axGA2`.

## Deviations from Rocq

1. NAMES: camelCase (map below).  `CondP` is a duplicated Rocq name (also `AxLeafS4`), so it is
   `AxCondM.condP`; no other name of this file is in `notes/weak-port-dupnames.json`.
   Lean-only helper (file-qualified): `AxCondM.keepPers` (use a persistent consequence of a
   hypothesis without consuming it — Rocq's `iAssert (…)%I as "#H"` with a persistent goal).
2. `Forall P L` ↦ `∀ p ∈ L, P p`; `bool_decide (e.1 = i)` ↦ `if e.1 = i`; `dom na` ↦
   `(FiniteMap.dom_set na : GSet Geid)`; `na !! e` ↦ `get? na e`; `from_option` ↦
   `AxWp.fromOption`; `e ↦ₐ P` ↦ `AxAnnot.annotOwn e P`; `WPd s @ MaybeStuck; i {{ Φ }}` ↦
   `wpd .MaybeStuck i s Φ`.
3. SECTION VARIABLES: definitions/lemmas take only what they use (AxWp deviation 6):
   `condP`/`condA`/`fragFacts` and their laws need no `InvGS_gen`/`Axpol`; `condPRb`/`condARb`
   take `[AxirisG GF]` (for `postLifting`).  `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for
   any `hlc` in `condGateAdequacy` (strictly more general).  The section hypothesis `ann_eq` is an
   explicit argument of `condARb` (its only user), `i` an explicit argument of every `condA`
   declaration.  `GF : BundledGFunctors.{0,0,0}` wherever `AxannotGS` appears (AxWp
   deviation 3).
4. `CondP_pers` (a Rocq `Lemma … : Persistent _`) is an `instance condPPers`.
5. STATEMENT SHAPES: wand chains `A -∗ B -∗ C` ↦ `⊢ A -∗ B -∗ C` (AxWp deviation 7).
   `condAGateTrivializes`'s Rocq premise `∀ C, CondA C -∗ … -∗ W` (an `iProp` coerced to Prop)
   is `∀ C, ⊢ condA i C -∗ … -∗ W`.
6. §ga2 (O2 STAGE C): `axGA2` has no text parameter `T` (AxTierA2 deviation 2), so the section
   parameter `T` is gone; the Rocq `Local Instance ga2_inst` is replaced by naming
   `axGA2 GD0 N obSt0 obStInterp0 nm` explicitly (`(self := …)`), as AxTierA2 does.  The unused
   section contexts (`invGS_gen`, `axannotG`, `axpol`) are not taken.

**Rocq → Lean name map.**  `CondP` `AxCondM.condP`, `CondP_pers` `condPPers`, `CondP_and`
`condPAnd`, `CondP_mono` `condPMono`, `CondP_intro` `condPIntro`, `CondP_rb` `condPRb`,
`CondP_gate` `condPGate`, `CondP_gate3` `condPGate3`, `CondA` `condA`, `CondA_intro`
`condAIntro`, `CondA_true` `condATrue`, `CondA_frag` `condAFrag`, `CondA_mono` `condAMono`,
`CondA_and` `condAAnd`, `frag_facts` `fragFacts`, `frag_facts_of` `fragFactsOf`,
`frag_facts_bag` `fragFactsBag`, `CondA_rb` `condARb`, `CondA_gate_trivializes`
`condAGateTrivializes`, `cond_gate_adequacy` `condGateAdequacy`, `ann_eq_ga2_M` `annEqGa2M`,
`Hagree_ga2` `hagreeGa2`.  Lean-only: `AxCondM.keepPers`, instance `AxCondM.fragFactsPersistent`.

**Dropped:** `ga2_inst` (a local instance; deviation 6) and the three `Print Assumptions` lines
(the lint's axiom check covers them).
-/
import Weak.AxTierA2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-- Lean-only: a persistent consequence of `R` and `P`, keeping `P`. -/
theorem AxCondM.keepPers {GF : BundledGFunctors} {R P Q : IProp GF} [Persistent Q]
    (h : ⊢ R -∗ P -∗ Q) : ⊢ R -∗ P -∗ Q ∗ P := by
  iintro HR HP
  iapply persistent_and_sep_mp
  isplit
  · iapply h $$ HR HP
  · iexact HP

/-! # 1. The pure model -/

section condP
variable {GF : BundledGFunctors}

/-- Rocq `CondP`: the pure model. -/
def AxCondM.condP (C : Prop) : IProp GF := iprop(⌜C⌝)

instance condPPers (C : Prop) : Persistent (AxCondM.condP (GF := GF) C) := by
  unfold AxCondM.condP; infer_instance

theorem condPAnd (C1 C2 : Prop) :
    ⊢ AxCondM.condP (GF := GF) C1 -∗ AxCondM.condP C2 -∗ AxCondM.condP (C1 ∧ C2) := by
  unfold AxCondM.condP
  iintro %H1 %H2
  ipureintro
  exact ⟨H1, H2⟩

theorem condPMono (C1 C2 : Prop) (Himp : C1 → C2) :
    ⊢ AxCondM.condP (GF := GF) C1 -∗ AxCondM.condP C2 := by
  unfold AxCondM.condP
  iintro %H1
  ipureintro
  exact Himp H1

theorem condPIntro (C : Prop) : (iprop(⌜C⌝) : IProp GF) ⊢ AxCondM.condP C := .rfl

theorem condPRb [AxirisG GF] (i : Agent) (C : Prop) (Φ : Athread → IProp GF) (s : Athread) :
    ⊢ AxCondM.condP C -∗ postLifting (fun s' => iprop(⌜C⌝ -∗ Φ s')) i s -∗
      postLifting Φ i s := by
  unfold AxCondM.condP postLifting
  iintro %HC H %na Hna
  imod H $$ %na Hna with ⟨Hna, H⟩
  imodintro
  iframe Hna
  iintro Hm
  ihave H := H $$ Hm
  inext
  imod H
  imodintro
  iapply H
  ipureintro
  exact HC

/-- THE GATE, for ANY goal `W` (in particular any WPd). -/
theorem condPGate (C : Prop) (W : IProp GF) :
    ⊢ AxCondM.condP C -∗ (⌜C⌝ -∗ W) -∗ W := by
  unfold AxCondM.condP
  iintro %HC H
  iapply H
  ipureintro
  exact HC

theorem condPGate3 (C : Prop) (W : IProp GF) :
    ⊢ AxCondM.condP C -∗ (⌜C⌝ -∗ AxCondM.condP C -∗ W) -∗ W := by
  unfold AxCondM.condP
  iintro %HC H
  iapply H
  · ipureintro
    exact HC
  · ipureintro
    exact HC

end condP

/-! # 2. The annotation-backed model -/

section condA
variable {GF : BundledGFunctors.{0,0,0}} [AxannotGS GF]

/-- Rocq `CondA`: fragments of hart `i`'s events whose pure contents imply `C`. -/
def condA (i : Agent) (C : Prop) : IProp GF :=
  iprop(∃ L : List (Geid × Prop),
    ⌜∀ p ∈ L, p.1.1 = i⌝ ∗ ⌜(∀ p ∈ L, p.2) → C⌝ ∗
    [∗list] p ∈ L, AxAnnot.annotOwn p.1 iprop(⌜p.2⌝))

theorem condAIntro (i : Agent) (C : Prop) : (iprop(⌜C⌝) : IProp GF) ⊢ condA i C := by
  unfold condA
  iintro %HC
  iexists []
  isplitr
  · ipureintro
    intro p hp
    cases hp
  · isplitr
    · ipureintro
      intro _
      exact HC
    · iapply BigSepL.bigSepL_nil.2
      itrivial

theorem condATrue (i : Agent) : ⊢ condA (GF := GF) i True := by
  iapply condAIntro
  ipureintro
  trivial

theorem condAFrag (i : Agent) (e : Geid) (φ : Prop) (He : e.1 = i) :
    AxAnnot.annotOwn (GF := GF) e iprop(⌜φ⌝) ⊢ condA i φ := by
  unfold condA
  iintro H
  iexists [(e, φ)]
  isplitr
  · ipureintro
    intro p hp
    rw [List.mem_singleton.1 hp]
    exact He
  · isplitr
    · ipureintro
      intro HF
      exact HF (e, φ) (List.mem_singleton.2 rfl)
    · iapply BigSepL.bigSepL_singleton.2
      iexact H

theorem condAMono (i : Agent) (C1 C2 : Prop) (Himp : C1 → C2) :
    ⊢ condA (GF := GF) i C1 -∗ condA i C2 := by
  unfold condA
  iintro ⟨%L, %Hi, %HC, H⟩
  iexists L
  isplitr
  · ipureintro
    exact Hi
  · isplitr
    · ipureintro
      intro HF
      exact Himp (HC HF)
    · iexact H

theorem condAAnd (i : Agent) (C1 C2 : Prop) :
    ⊢ condA (GF := GF) i C1 -∗ condA i C2 -∗ condA i (C1 ∧ C2) := by
  unfold condA
  iintro ⟨%L1, %Hi1, %HC1, H1⟩ ⟨%L2, %Hi2, %HC2, H2⟩
  iexists L1 ++ L2
  isplitr
  · ipureintro
    intro p hp
    rcases List.mem_append.1 hp with h | h
    · exact Hi1 p h
    · exact Hi2 p h
  · isplitr
    · ipureintro
      intro HF
      exact ⟨HC1 (fun p hp => HF p (List.mem_append.2 (.inl hp))),
        HC2 (fun p hp => HF p (List.mem_append.2 (.inr hp)))⟩
    · iapply BigSepL.bigSepL_append.2
      isplitl [H1]
      · iexact H1
      · iexact H2

/-- Rocq `frag_facts`: the fragments' persistent consequences at an annotation map. -/
def fragFacts (na : Mea GF) (L : List (Geid × Prop)) : IProp GF :=
  iprop([∗list] p ∈ L, ⌜p.1 ∈ (FiniteMap.dom_set na : GSet Geid)⌝ ∗
    AxWp.fromOption (fun P' => iprop(▷ □ (P' -∗ ⌜p.2⌝))) iprop(emp) (get? na p.1))

instance AxCondM.fragFactsPersistent (na : Mea GF) (L : List (Geid × Prop)) :
    Persistent (fragFacts na L) := by
  unfold fragFacts; infer_instance

theorem fragFactsOf (na : Mea GF) (L : List (Geid × Prop)) :
    ⊢ AxAnnot.annotInterp na -∗ ([∗list] p ∈ L, AxAnnot.annotOwn p.1 iprop(⌜p.2⌝)) -∗
      fragFacts na L := by
  induction L with
  | nil =>
    iintro _ _
    unfold fragFacts
    iapply BigSepL.bigSepL_nil.2
    itrivial
  | cons p L IH =>
    iintro Hna HL
    unfold fragFacts at IH ⊢
    iapply BigSepL.bigSepL_cons.2
    icases BigSepL.bigSepL_cons.1 $$ HL with ⟨Hp, HL⟩
    iapply persistent_and_sep_mp
    isplit
    · iapply annotAgree na p.1 iprop(⌜p.2⌝) $$ Hna Hp
    · iapply IH $$ Hna HL

theorem fragFactsBag (i : Agent) (na : Mea GF) (L : List (Geid × Prop))
    (Hi : ∀ p ∈ L, p.1.1 = i) :
    ⊢ fragFacts na L -∗
      ([∗map] e ↦ R ∈ na, if e.1 = i then R else iprop(True)) -∗ ▷ ⌜∀ p ∈ L, p.2⌝ := by
  induction L with
  | nil =>
    iintro _ _
    inext
    ipureintro
    intro p hp
    cases hp
  | cons p L IH =>
    unfold fragFacts at IH ⊢
    iintro #HL Hbag
    icases BigSepL.bigSepL_cons.1 $$ HL with ⟨⟨%Hd, #Hw⟩, #HL'⟩
    have Hp : p.1.1 = i := Hi p (List.mem_cons_self ..)
    have Hi' : ∀ q ∈ L, q.1.1 = i := fun q hq => Hi q (List.mem_cons_of_mem _ hq)
    obtain ⟨P', HP'⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 Hd)
    have Hlk : ([∗map] e ↦ R ∈ na, if e.1 = i then R else iprop(True)) ⊢ P' :=
      (BigSepM.bigSepM_lookup (Φ := fun e R => if e.1 = i then R else iprop(True)) HP').trans
        (by simp only [Hp, ↓reduceIte]; exact .rfl)
    iapply (show iprop(▷ ⌜p.2⌝ ∧ ▷ ⌜∀ q ∈ L, q.2⌝) ⊢ iprop(▷ ⌜∀ q ∈ p :: L, q.2⌝) from
      later_and.2.trans (later_mono (pure_and.1.trans (pure_mono (fun ⟨h1, h2⟩ q hq => by
        rcases List.mem_cons.1 hq with rfl | h
        · exact h1
        · exact h2 q h)))))
    isplit
    · have Hw2 : AxWp.fromOption (fun P' => iprop(▷ □ (P' -∗ ⌜p.2⌝))) iprop(emp)
          (get? na p.1) ⊢ iprop(▷ □ (P' -∗ ⌜p.2⌝)) := by
        rw [HP']; exact .rfl
      ihave HP := Hlk $$ Hbag
      ihave Hw' := Hw2 $$ Hw
      inext
      iapply Hw' $$ HP
    · iapply (IH Hi') $$ HL' Hbag

/-- THE READBACK LAW (surface v2's `Cond_rb`). -/
theorem condARb [AxirisG GF] (i : Agent)
    (annEq : ∀ m, AxirisG.annotInterp m ⊣⊢ AxAnnot.annotInterp (GF := GF) m)
    (C : Prop) (Φ : Athread → IProp GF) (s : Athread) :
    ⊢ condA i C -∗ postLifting (fun s' => iprop(⌜C⌝ -∗ Φ s')) i s -∗ postLifting Φ i s := by
  unfold condA postLifting
  iintro ⟨%L, %Hi, %HC, HL⟩ H %na Hna
  ihave Hna := (annEq na).1 $$ Hna
  icases AxCondM.keepPers (show ⊢ iprop([∗list] p ∈ L, AxAnnot.annotOwn p.1 iprop(⌜p.2⌝)) -∗
      AxAnnot.annotInterp na -∗ fragFacts na L from by
        iintro HL Hna
        iapply fragFactsOf na L $$ Hna HL) $$ HL Hna with ⟨#HF, Hna⟩
  ihave Hna := (annEq na).2 $$ Hna
  imod H $$ %na Hna with ⟨Hna, H⟩
  imodintro
  iframe Hna
  iintro Hbag
  icases AxCondM.keepPers (fragFactsBag i na L Hi) $$ HF Hbag with ⟨#HFL, Hbag⟩
  ihave H := H $$ Hbag
  inext
  icases HFL with %HFL
  imod H
  imodintro
  iapply H
  ipureintro
  exact HC HFL

/-- THE GATE at `condA` trivializes the gated goal: a fragment of `⌜False⌝` proves ANY goal the
gate is applied to. -/
theorem condAGateTrivializes (i : Agent) (W : IProp GF) (e : Geid) (He : e.1 = i)
    (Hgate : ∀ C, ⊢ condA i C -∗ (⌜C⌝ -∗ W) -∗ W) :
    AxAnnot.annotOwn e iprop(⌜False⌝) ⊢ W := by
  iintro Hf
  ihave Hc := condAFrag i e False He $$ Hf
  iapply (Hgate False) $$ Hc
  iintro %h
  exact h.elim

end condA

/-- THE MISSING ADEQUACY FACT behind `Cond_gate` at `condA` (NOT proved; stated so it can be
named): at a data-access boundary `s` of hart `i` (predicate `gateAt`), the WPd that may assume
the pure content of the hart's fragments is no stronger than the plain WPd. -/
def condGateAdequacy {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF]
    [AxirisG GF] [Axpol] [AxannotGS GF] (i : Agent) (gateAt : Athread → Prop)
    (Φ : Athread → IProp GF) : Prop :=
  ∀ s C, gateAt s →
    iprop(condA i C ∗ (⌜C⌝ -∗ condA i C -∗ wpd .MaybeStuck i s Φ)) ⊢ wpd .MaybeStuck i s Φ

/-! ## The instance premises hold at the tier-A instance `axGA2` -/

section ga2
variable {GF : BundledGFunctors.{0,0,0}} [AxannotGS GF]
variable (GD0 : Gdexec) (N obSt0 : Type)
  (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N)

theorem annEqGa2M :
    ∀ m, AxirisG.annotInterp (self := axGA2 GD0 N obSt0 obStInterp0 nm) m ⊣⊢
      AxAnnot.annotInterp m :=
  fun _ => .rfl

theorem hagreeGa2 :
    ∀ GD GD', rvwmoCatConsistent GD → rvwmoCatConsistent GD' →
      ⊢ AxirisG.gconstInterp (self := axGA2 GD0 N obSt0 obStInterp0 nm) GD -∗
        AxirisG.gconstInterp (self := axGA2 GD0 N obSt0 obStInterp0 nm) GD' -∗ ⌜GD = GD'⌝ := by
  intro GD GD' _ _
  show ⊢ iprop(⌜GD = GD0⌝) -∗ iprop(⌜GD' = GD0⌝) -∗ ⌜GD = GD'⌝
  iintro %h1 %h2
  ipureintro
  rw [h1, h2]

end ga2

end Weak
