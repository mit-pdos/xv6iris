/-
Weak/Prom: **track (a), THE CONCURRENT ADEQUACY `adequacyA`** (stage S4a; plan rev 7 §2 "A0 is per hart, so the
tracks need more" [R2.s11]: "Each track therefore needs its own concurrent adequacy over the schedule it chooses
(§3, §4), with the shared ghost state allocated once.  A0 is a corollary of it for ownership-free programs"; §3
R-a2, R-a5).

```
theorem adequacyA (π) (Φ : Hart → Val → Prop) (Ψ : Hart → List PEv → Prop) :
    PO_img π img → (∀ h, Ψ h []) →
    (∀ Iris world, ∀ names g, ∀ initial promise sets,
       doomInv g M -∗ (every hart's hartA at its initial state) -∗ (every pend g t) ={⊤}=∗
       [∗ list] h ↦ p ∈ ps, wpA g π ⟨pstep, pdone, img, M, h⟩ Ψ p (fun v => ⌜∃ V, ⟦V⟧ Φ h v⌝ ∨ dshot g)) →
    PF.validRun pstep img d0 ps M run →
      (i) ∧ (ii) ∧ (iii) ∧ (iii') ∧ (iv) ∧ (v)        -- A0's exports (vi is `adExact_all`)
```

* The shared ghost state is allocated ONCE, at adequacy start (plan R-a5): one hart ghost per hart, one one-shot
  `pend g t` per `t ∈ 1..|M|` (a big separating conjunction over the M-indexed family), the doom one-shot and the
  doom box `doomInv`.  The client's premise receives them and may allocate its own invariants first (`={⊤}=∗`),
  e.g. the deposit slots of OwnALib.lean, before handing every hart its wp.
* Proof: the schedule lemma (OwnASched.lean `sched`) turns the valid run into an execution of the guarded
  concurrent language; `wp_strong_adequacy_gen` gives the state interpretation at its end.  There every
  timestamp is fulfilled (the partition), hence shot, so the doom box holds no `pend s`: it still holds `dpend`,
  which contradicts `dshot` — the facts `cFacts` hold.  They give `Valid π img M |M|` (iv), the trace part (ii) and,
  through the value step appended to the schedule, the termination part (i).
* `[Inhabited P]` is a technical side condition (the configuration of the schedule is a function over all hart
  indices); every program-state type of the tree is inhabited.
No named assumption.  No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAWp
import Iris.ProgramLogic.Adequacy

namespace Weak.Prom.OA

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Iris.ProgramLogic.Language Iris.ProgramLogic.Language.Notation

variable {P D V : Type} {hlc : HasLC}

/-! ## 1. Big-separating-conjunction plumbing -/

section bigop

variable {GF : BundledGFunctors}

/-- A big separating conjunction whose body ignores the elements depends only on the length. -/
theorem bsl_len {A B : Type} : ∀ (l1 : List A) (l2 : List B) (G : Nat → IProp GF), l1.length = l2.length →
    ([∗list] k ↦ _x ∈ l1, G k) ⊢ [∗list] k ↦ _x ∈ l2, G k
  | [], [], _, _ => .rfl
  | _ :: l1, _ :: l2, G, h => by
    refine (BigSepL.bigSepL_cons).1.trans (Entails.trans ?_ (BigSepL.bigSepL_cons).2)
    exact sep_mono .rfl (bsl_len l1 l2 (fun k => G (k + 1)) (by simpa using h))
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-- A big separating conjunction over a list, as a pairwise one over two maps of it. -/
theorem bsl2_map {A B C : Type} (E : A → B) (Q : A → C) : ∀ (l : List A) (R : Nat → B → C → IProp GF),
    ([∗list] k ↦ a ∈ l, R k (E a) (Q a)) ⊢ [∗list] k ↦ e;q ∈ l.map E;l.map Q, R k e q
  | [], _ => .rfl
  | a :: l, R => by
    refine (BigSepL.bigSepL_cons).1.trans (Entails.trans ?_ (BigSepL2.bigSepL2_cons).2)
    exact sep_mono .rfl (bsl2_map E Q l (fun k => R (k + 1)))

end bigop

/-! ## 2. Allocation (plan R-a5) -/

section alloc

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool]

/-- `n` hart ghosts, both halves. -/
theorem harts_alloc : ∀ (n : Nat) (f : Nat → HSt), ⊢@{IProp GF} |==> ∃ hn : List GName, ⌜hn.length = n⌝ ∗
    ([∗list] k ↦ γ ∈ hn, ghost_var γ (.own (1 : Qp).half) (f k)) ∗
    ([∗list] k ↦ γ ∈ hn, ghost_var γ (.own (1 : Qp).half) (f k))
  | 0, _ => by
    iapply bupd_intro
    iexists []
    isplitr
    · ipureintro; rfl
    isplitl <;> exact BigSepL.bigSepL_nil.2
  | n + 1, f => by
    have ih := harts_alloc n (fun k => f (k + 1))
    iintro
    imod ghost_var_alloc (f 0) with ⟨%γ, H⟩
    have hs := ghost_var_split (GF := GF) γ (f 0) (1 : Qp).half (1 : Qp).half
    rw [Qp.half_add_half] at hs
    ihave ⟨H1, H2⟩ := hs $$ H
    imod ih with ⟨%hn, %hl, K1, K2⟩
    imodintro
    iexists γ :: hn
    isplitr
    · ipureintro; simp [hl]
    isplitl [H1 K1]
    · iapply (BigSepL.bigSepL_cons).2; iframe H1; iexact K1
    · iapply (BigSepL.bigSepL_cons).2; iframe H2; iexact K2

/-- `m` message one-shots (plan §3: "for every index t in 1..|M|"). -/
theorem pends_alloc : ∀ (m : Nat), ⊢@{IProp GF} |==> ∃ mn : List GName, ⌜mn.length = m⌝ ∗
    [∗list] k ↦ γ ∈ mn, ghost_var γ (.own 1) false
  | 0 => by
    iapply bupd_intro
    iexists []
    isplitr
    · ipureintro; rfl
    exact BigSepL.bigSepL_nil.2
  | m + 1 => by
    have ih := pends_alloc m
    iintro
    imod ghost_var_alloc false with ⟨%γ, H⟩
    imod ih with ⟨%mn, %hl, K⟩
    imodintro
    iexists γ :: mn
    isplitr
    · ipureintro; simp [hl]
    iapply (BigSepL.bigSepL_cons).2; iframe H; iexact K

theorem getD_of_get? {l : List GName} {k : Nat} {γ : GName} (h : l[k]? = some γ) : l.getD k 0 = γ := by
  rw [List.getD_eq_getElem?_getD, h]; rfl

end alloc

/-! ## 3. The core: from any execution to the final facts -/

section core

variable {GF : BundledGFunctors} [InvGpreS GF] [GhostVarG GF HSt] [GhostVarG GF Bool]
variable {pstep : P → D → PLabel → P → D → Prop} {pdone : P → Option V} {img : Image} {M : List PMsg}
  {ps : List P}

/-- The client premise of the concurrent adequacy (see the header). -/
def wpPremise (hlc : HasLC) (GF : BundledGFunctors) [InvGpreS GF] [GhostVarG GF HSt] [GhostVarG GF Bool]
    (pstep : P → D → PLabel → P → D → Prop) (pdone : P → Option V) (img : Image) (M : List PMsg) (ps : List P)
    (π : Proto) (Φ : Nat → V → Prop) (Ψ : Nat → Trace → Prop) (Dd : Nat → Prop) : Prop :=
  ∀ [InvGS_gen hlc GF] (g : AGN) (P0 : Nat → GSet Nat), g.hn.length = ps.length → g.mn.length = M.length →
    g.dd = Dd →
    (∀ h, h < ps.length → ∀ t, t ∈ P0 h ↔ 0 < t ∧ ownTs M h t) →
    ⊢@{IProp GF} doomInv g M -∗ ([∗list] k ↦ _x ∈ g.hn, hartA g k psInit (P0 k) []) -∗
      ([∗list] k ↦ _x ∈ g.mn, pend g (k + 1)) ={⊤}=∗
      [∗list] k ↦ p ∈ ps, wpA g π (hw pstep pdone img M k) Ψ p
        (fun v => iprop(⌜∃ V, grd π img M V (Φ k v)⌝ ∨ dshot g))

/-- The initial shared state. -/
def σInit (n : Nat) (P0 : Nat → GSet Nat) : CSt := fun h => if h < n then (psInit, P0 h, []) else (psInit, ∅, [])

/-- The initial thread pool. -/
def esInit [Inhabited P] (pstep : P → D → PLabel → P → D → Prop) (pdone : P → Option V) (img : Image)
    (M : List PMsg) (ps : List P) : List (CExpr P D V) :=
  (List.range ps.length).map (fun k => CExpr.run (hw pstep pdone img M k) (ps.getD k default))

/-- **THE ADEQUACY CORE**: after any execution of the concurrent language from the initial configuration that
ends with every timestamp fulfilled, the facts hold and every value reached meets its (guarded) postcondition. -/
theorem adeq_core [Inhabited P] {π : Proto} {Φ : Nat → V → Prop} {Ψ : Nat → Trace → Prop} {Dd : Nat → Prop}
    (himg : PO_img π img)
    (hΨ0 : ∀ h, Ψ h []) (hwp : wpPremise hlc GF pstep pdone img M ps π Φ Ψ Dd) (P0 : Nat → GSet Nat)
    (hP0 : ∀ h, h < ps.length → ∀ t, t ∈ P0 h ↔ 0 < t ∧ ownTs M h t)
    {k : Nat} {es2 : List (CExpr P D V)} {σ2 : CSt}
    (hsteps : NSteps k (esInit pstep pdone img M ps, σInit ps.length P0) [] (es2, σ2))
    (hall : ∀ t, 1 ≤ t → t ≤ M.length → fulAt σ2 t) (hsel : Nat) :
    cFacts π img M Ψ ps.length σ2 ∧
      (hsel < ps.length → ∀ v, es2[hsel]? = some (CExpr.ret v) → ∃ V, grd π img M V (Φ hsel v)) := by
  refine wp_strong_adequacy_gen (hlc := hlc) (GF := GF) Stuckness.MaybeStuck (esInit pstep pdone img M ps)
    (σInit ps.length P0) k [] es2 σ2 _ (fun _ => 0) ?_ hsteps
  intro Hinv
  iintro
  imod harts_alloc (GF := GF) ps.length (σInit ps.length P0) with ⟨%hn, %hlen, H1, H2⟩
  imod pends_alloc (GF := GF) M.length with ⟨%mn, %hmlen, Hp⟩
  imod ghost_var_alloc (GF := GF) false with ⟨%dn, Hd⟩
  imod ghost_var_alloc (GF := GF) false with ⟨%fn, Hfn⟩
  imod inv_alloc doomN ⊤ iprop((dpend (GF := GF) ⟨hn, mn, dn, fn, Dd⟩ ∗ dfpend ⟨hn, mn, dn, fn, Dd⟩) ∨
      (dshot ⟨hn, mn, dn, fn, Dd⟩ ∗ ∃ s, ⌜1 ≤ s ∧ s ≤ M.length⌝ ∗ pend ⟨hn, mn, dn, fn, Dd⟩ s ∗
        (dfpend ⟨hn, mn, dn, fn, Dd⟩ ∨ (dfree ⟨hn, mn, dn, fn, Dd⟩ ∗ ⌜(⟨hn, mn, dn, fn, Dd⟩ : AGN).dd s⌝))))
      $$ [Hd Hfn] with #Hdoom
  · inext; ileft; unfold dpend dfpend; iframe Hd Hfn
  ihave #Hdoom' : doomInv (GF := GF) ⟨hn, mn, dn, fn, Dd⟩ M $$ []
  · unfold doomInv; iexact Hdoom
  have hwp' := @hwp Hinv ⟨hn, mn, dn, fn, Dd⟩ P0 hlen hmlen rfl hP0
  ihave Hw := hwp'
  imod Hw $$ Hdoom' [H2] [Hp] with Hwps
  · iapply BigSepL.bigSepL_mono (Φ := fun k γ => ghost_var (GF := GF) γ (.own (1 : Qp).half) (σInit ps.length P0 k))
      ?_ $$ H2
    intro j γ hj
    have hjl : j < hn.length := (List.getElem?_eq_some_iff.1 hj).1
    have hjp : j < ps.length := by rw [← hlen]; exact hjl
    unfold hartA
    iintro H
    isplitr
    · ipureintro; exact hjl
    · simp only [σInit, if_pos hjp]
      rw [getD_of_get? hj]; iexact H
  · iapply BigSepL.bigSepL_mono (Φ := fun k γ => ghost_var (GF := GF) γ (.own 1) false) ?_ $$ Hp
    intro j γ hj
    unfold pend
    simp only [Nat.add_sub_cancel]
    rw [getD_of_get? hj]
  imodintro
  iexists (fun σ _ _ _ => stA (GF := GF) ⟨hn, mn, dn, fn, Dd⟩ π img M Ψ σ),
    (List.range ps.length).map (fun k => fun v => iprop(⌜∃ V, grd π img M V (Φ k v)⌝ ∨ dshot (GF := GF) ⟨hn, mn, dn, fn, Dd⟩)),
    (fun _ => iprop(True)), (fun _ _ _ _ => fupd_intro)
  dsimp only
  isplitl [H1]
  · -- the initial state interpretation
    unfold stA
    iframe H1
    isplitr
    · ipureintro
      intro j hj
      dsimp only at hj
      have hj' : ¬ j < ps.length := by omega
      simp only [σInit, if_neg hj']
    isplitr
    · ipureintro
      intro j t h1 _ h3
      have : wfr (σInit ps.length P0 j).1 = 0 := by
        unfold σInit; split <;> rfl
      omega
    isplitr
    · imodintro
      iintro %t %ht
      exfalso
      obtain ⟨j, e, he, _⟩ := ht.2.2
      unfold σInit at he; split at he <;> cases he
    · ileft; ipureintro
      refine ⟨himg, fun j hj0 => ?_⟩
      have hj : j < ps.length := by dsimp only at hj0; omega
      refine ⟨fun _ => ⟨0, fun _ => ?_⟩, ?_, ?_, ?_⟩
      · simp only [σInit, if_pos hj, List.take_nil]; exact hΨ0 j
      · simp only [σInit, if_pos hj]; intro e he; cases he
      · simp only [σInit, if_pos hj]; exact Nat.le_refl _
      · simp only [σInit, if_pos hj]
        intro a tf vf h
        rw [show psInit.wFwd = ∅ from rfl, lookupEmpty] at h; cases h
  isplitl [Hwps]
  · -- the thread pool's wps
    unfold esInit
    iapply bsl2_map (E := fun k => CExpr.run (hw pstep pdone img M k) (ps.getD k default))
      (Q := fun k => fun v => iprop(⌜∃ V, grd π img M V (Φ k v)⌝ ∨ dshot (GF := GF) ⟨hn, mn, dn, fn, Dd⟩))
    iapply BigSepL.bigSepL_mono (Φ := fun j _ => wpA (GF := GF) ⟨hn, mn, dn, fn, Dd⟩ π (hw pstep pdone img M j) Ψ
      (ps.getD j default) (fun v => iprop(⌜∃ V, grd π img M V (Φ j v)⌝ ∨ dshot (GF := GF) ⟨hn, mn, dn, fn, Dd⟩))) ?_
    · intro j i hj
      have : i = j := by
        have hjl := (List.getElem?_eq_some_iff.1 hj).1
        rw [List.length_range] at hjl
        simp only [List.getElem?_range hjl, Option.some.injEq] at hj
        exact hj.symm
      subst this
      dsimp only [wpA]
      exact .rfl
    iapply bsl_len ps (List.range ps.length) _ (by simp)
    iapply BigSepL.bigSepL_mono (Φ := fun j p => wpA (GF := GF) ⟨hn, mn, dn, fn, Dd⟩ π (hw pstep pdone img M j) Ψ p
      (fun v => iprop(⌜∃ V, grd π img M V (Φ j v)⌝ ∨ dshot (GF := GF) ⟨hn, mn, dn, fn, Dd⟩))) ?_ $$ Hwps
    intro j p hj
    rw [List.getD_eq_getElem?_getD, hj]
    exact .rfl
  -- the end
  iintro %es' %t2' %Heq %Hlen %_ Hσ Hpost _
  unfold stA
  icases Hσ with ⟨_, %Hout, %Hok, #Hshots, #Hfacts⟩
  imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hdoom with ⟨Hb, -⟩
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  icases Hb with (⟨Hd, Hdf⟩ | ⟨Hds, %s, %hs, Hps, Hmode⟩)
  · icases Hfacts with (%Hf | #Hds)
    · -- not doomed: the facts, and the selected value's postcondition
      have Hf' : cFacts π img M Ψ ps.length σ2 := by have := Hf; simp only at this; rw [hlen] at this; exact this
      by_cases hs : hsel < ps.length
      · cases hq : es2[hsel]? with
        | none => ipureintro; exact ⟨Hf', fun _ v hv => by cases hv⟩
        | some e =>
          cases e with
          | run w0 s0 => ipureintro; exact ⟨Hf', fun _ v hv => by cases hv⟩
          | ret v =>
            have h1 : es'[hsel]? = some (CExpr.ret v) := by
              rw [Heq, List.getElem?_append_left (by rw [Hlen]; simp [esInit]; exact hs)] at hq; exact hq
            have h2 : ((List.range ps.length).map (fun k => fun v => iprop(⌜∃ V, grd π img M V (Φ k v)⌝ ∨
                dshot (GF := GF) ⟨hn, mn, dn, fn, Dd⟩)))[hsel]? =
                some (fun v => iprop(⌜∃ V, grd π img M V (Φ hsel v)⌝ ∨ dshot (GF := GF) ⟨hn, mn, dn, fn, Dd⟩)) := by
              rw [List.getElem?_map, List.getElem?_range hs]; rfl
            ihave Hp := BigSepL2.bigSepL2_lookup h1 h2 $$ Hpost
            dsimp only [ToVal.toVal, CExpr.toV, Option.elim]
            icases Hp with (%Hg | #Hds)
            · ipureintro
              exact ⟨Hf', fun _ v' hv' => by cases hv'; exact Hg⟩
            · iexfalso
              iapply dpend_dshot
              iframe Hd Hds
      · ipureintro; exact ⟨Hf', fun h => absurd h hs⟩
    · iexfalso
      iapply dpend_dshot
      iframe Hd Hds
  · iexfalso
    ihave #Hfs := Hshots $$ %s %⟨hs.1, hs.2, hall s hs.1 hs.2⟩
    unfold fulT
    icases Hfs with (#Hsh | ⟨#Hfr, %hnd⟩)
    · iapply pend_shot
      iframe Hps Hsh
    · icases Hmode with (Hdf | ⟨_, %hdd⟩)
      · iapply dfpend_dfree; iframe Hdf Hfr
      · exact absurd hdd hnd


end core

/-! ## 4. The concurrent adequacy -/

section main

/-- An execution followed by one more step. -/
theorem nsteps_snoc {Λ : Type} [Language Λ CSt Unit V] {ρ3 : List Λ × CSt} :
    ∀ {k : Nat} {ρ1 ρ2 : List Λ × CSt} {κs : List Unit}, NSteps k ρ1 κs ρ2 → Language.Step ρ2 [] ρ3 →
      NSteps (k + 1) ρ1 κs ρ3 := by
  intro k ρ1 ρ2 κs h hs
  induction h with
  | refl ρ => simpa using NSteps.cons hs (.refl _)
  | cons hab _ ih => exact NSteps.cons hab (ih hs)

/-- `Valid` at the end of an execution in which every timestamp is fulfilled. -/
theorem valid_fin {π : Proto} {img : Image} {M : List PMsg} {Ψ : Nat → Trace → Prop} {n : Nat} {σ : CSt}
    (hf : cFacts π img M Ψ n σ) (hout : ∀ k, n ≤ k → (σ k).2.2 = [])
    (hall : ∀ t, 1 ≤ t → t ≤ M.length → fulAt σ t) : Valid π img M M.length := by
  refine valid_of_protoOk hf.1 (fun t h1 h2 => ?_)
  obtain ⟨k, e, he, het⟩ := hall t h1 (by omega)
  have hk : k < n := by
    apply Classical.byContradiction; intro hk
    rw [hout k (by omega)] at he; cases he
  exact (hf.2 k hk).2.1 e he t het

variable {GF : BundledGFunctors} [InvGpreS GF] [GhostVarG GF HSt] [GhostVarG GF Bool]

/-- **THE CONCURRENT ADEQUACY OF TRACK (a)** (plan §2 [R2.s11], §3; header).  Exports: (i) termination, (ii) the
trace part at every prefix of every hart, (iii) the partition (both parts), (iv) `Valid`, (v) `traceWf`. -/
theorem adequacyA [Inhabited P] {pstep : P → D → PLabel → P → D → Prop} {pdone : P → Option V} {img : Image}
    {d0 : D} {ps : List P} {M : List PMsg} {run : PFRun P D}
    (π : Proto) (Φ : Nat → V → Prop) (Ψ : Nat → Trace → Prop) (Dd : Nat → Prop) :
    PO_img π img →
    (∀ h, Ψ h []) →
    wpPremise hlc GF pstep pdone img M ps π Φ Ψ Dd →
    PF.validRun pstep img d0 ps M run →
      (∀ h v, run.done pdone h v → Φ h v)
    ∧ (∀ h k, Ψ h ((run.trace h).take k))
    ∧ (∀ t, 1 ≤ t → t ≤ M.length → exU (fun h => t ∈ run.fulfils h ∧ tidAt M t = some h))
    ∧ (∀ h, (run.fulfils h).Nodup)
    ∧ Valid π img M M.length
    ∧ run.traceWf M := by
  intro himg hΨ0 hwp hrun
  obtain ⟨hpart, hnd⟩ := validRun_partition hrun
  have htwf := validRun_traceWf hrun
  obtain ⟨hv, hM⟩ := hrun
  have hlen := validRun_len hv
  -- every hart's solo run (chosen)
  have hex : ∀ h, ∃ q : PAgent P × GSet Nat, h < ps.length → run.cfg.pcAgs[h]? = some q.1 ∧
      (∀ t, t ∈ q.2 ↔ 0 < t ∧ ownTs M h t) ∧
      soloSteps (anyFab pstep) img M h (ps.getD h default, psInit, q.2) (run.trace h)
        (q.1.paSt, q.1.paWs, q.1.paProm) := by
    intro h
    by_cases hh : h < ps.length
    · obtain ⟨ag, hag, P0, hP0, hs⟩ := validRun_soloD hv h (ps.getD h default)
        (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hh]; rfl)
      rw [hM] at hP0 hs
      exact ⟨(ag, P0), fun _ => ⟨hag, hP0, hs⟩⟩
    · exact ⟨(⟨default, psInit, ∅⟩, ∅), fun h' => absurd h' hh⟩
  let Q := fun h => Classical.choose (hex h)
  have hQ : ∀ h, h < ps.length → _ := fun h => Classical.choose_spec (hex h)
  let x : Nat → P × PState × GSet Nat := fun h => (ps.getD h default, psInit, (Q h).2)
  let y : Nat → P × PState × GSet Nat := fun h => ((Q h).1.paSt, (Q h).1.paWs, (Q h).1.paProm)
  let tr : Nat → Trace := fun h => run.trace h
  have hdom : ∀ h, run.trace h ≠ [] → h < ps.length := by
    intro h hne
    apply Classical.byContradiction; intro hh
    exact hne (validRun_traceNone hv (List.getElem?_eq_none (by omega)))
  have hpart' : ∀ t, 1 ≤ t → t ≤ M.length → ∃ h, h < ps.length ∧ ∃ e ∈ tr h, e.2 = some t := by
    intro t h1 h2
    obtain ⟨h, ⟨hin, _⟩, _⟩ := hpart t h1 h2
    unfold PFRun.fulfils fulfilsOf at hin
    obtain ⟨e, he, het⟩ := List.mem_filterMap.1 hin
    exact ⟨h, hdom h (fun h0 => by unfold PFRun.trace at h0; rw [h0] at he; cases he), e, he, het⟩
  obtain ⟨k, hk⟩ := sched (pdone := pdone) ps.length x y tr (fun h hh => (hQ h hh).2.2) hpart'
  have hσ2 : ∀ h, h < ps.length → ((cfgOf pstep pdone img M ps.length y tr).2 h).2.2 = run.trace h := by
    intro h hh; simp [cfgOf, hh, tr]
  have hall : ∀ t, 1 ≤ t → t ≤ M.length → fulAt (cfgOf pstep pdone img M ps.length y tr).2 t := by
    intro t h1 h2
    obtain ⟨h, hh, e, he, het⟩ := hpart' t h1 h2
    exact ⟨h, e, by rw [hσ2 h hh]; exact he, het⟩
  have hout : ∀ j, ps.length ≤ j → ((cfgOf pstep pdone img M ps.length y tr).2 j).2.2 = [] := by
    intro j hj; simp [cfgOf, show ¬ j < ps.length by omega]
  have hk0 : NSteps k (esInit pstep pdone img M ps, σInit ps.length (fun h => (Q h).2)) []
      (cfgOf pstep pdone img M ps.length y tr) := hk
  obtain ⟨hF, _⟩ := adeq_core (hlc := hlc) (GF := GF) himg hΨ0 hwp (fun h => (Q h).2)
    (fun h hh => (hQ h hh).2.1) hk0 hall 0
  have hValid := valid_fin hF hout hall
  refine ⟨fun h v hd => ?_, fun h j => ?_, hpart, hnd, hValid, htwf⟩
  · -- (i)
    obtain ⟨ag, hag, hdv⟩ := hd
    have hh : h < ps.length := by
      rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hag).1
    have hq1 : (Q h).1 = ag := (Option.some.inj (hag.symm.trans (hQ h hh).1)).symm
    have hfin : cstep (CExpr.run (hw pstep pdone img M h) (y h).1, (cfgOf pstep pdone img M ps.length y tr).2) []
        (CExpr.ret v, (cfgOf pstep pdone img M ps.length y tr).2, []) :=
      .fin _ _ _ v (by show pdone (Q h).1.paSt = some v; rw [hq1]; exact hdv)
    obtain ⟨t₁, t₂, h1, h2⟩ := map_range_split (fun j => CExpr.run (hw pstep pdone img M j) (y j).1)
      (fun j => if j = h then CExpr.ret v else CExpr.run (hw pstep pdone img M j) (y j).1) h
      (fun j hj => by simp [hj]) ps.length hh
    have hS := Language.Step.atomic (Λ := (inferInstance : Language (CExpr P D V) CSt Unit V)) hfin t₁ t₂
    simp only [List.append_nil] at hS
    have e1 : cfgOf pstep pdone img M ps.length y tr =
        (t₁ ++ CExpr.run (hw pstep pdone img M h) (y h).1 :: t₂, (cfgOf pstep pdone img M ps.length y tr).2) := by
      rw [← h1]; rfl
    rw [← e1] at hS
    have hk1 := nsteps_snoc hk0 hS
    have hsel : (t₁ ++ CExpr.ret v :: t₂)[h]? = some (CExpr.ret v) := by
      have := congrArg (fun l => l[h]?) h2
      simp only at this
      rw [List.getElem?_map, List.getElem?_range hh] at this
      simp only [Option.map_some, if_true] at this
      exact this.symm.trans (by rfl) |>.symm ▸ rfl
    obtain ⟨_, hfv⟩ := adeq_core (hlc := hlc) (GF := GF) himg hΨ0 hwp (fun h => (Q h).2)
      (fun h hh => (hQ h hh).2.1) hk1 hall h
    obtain ⟨V', hg⟩ := hfv hh v hsel
    exact grd_elim hValid hg
  · -- (ii)
    by_cases hh : h < ps.length
    · obtain ⟨V', hg⟩ := (hF.2 h hh).1 j
      dsimp only at hg
      simp only [if_pos hh] at hg
      exact grd_elim hValid hg
    · unfold PFRun.trace
      rw [validRun_traceNone hv (List.getElem?_eq_none (by omega))]
      simpa using hΨ0 h

end main

end Weak.Prom.OA

#print axioms Weak.Prom.OA.adequacyA
