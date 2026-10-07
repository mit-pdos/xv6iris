/-
Weak: **constraint F, GENERAL** — the processing order for gated phase 2 EXISTS for every
consistent graph, every real ctrl-gate structure and every DEFERRAL-SAFE policy, in particular
every `flowDev2`-bounded (deviation-2) policy; so `adequacyOrdG` needs no order premise:
`adequacyOrdGDS` / `adequacyOrdGDev2` (AxSL tier).

Rocq: `iris/AxDefer3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

THE ORDER (`Lcanon`): sort `gxGmo` by the rank `grank e = N·gkey e + goff e`, where
`gkey e` = max gmo position over `e` and its gate sources `gsrc e` (a deferred read is moved to
just after its latest source) and `goff e` = 0 if `e` is not deferred (`gkey e = gpos e`), else
`e.2 + 1` (deferred events sharing a key — all on one hart — stay in PROGRAM order, so a
deferred source precedes the deferred reads it gates).  (`LcanonGdefer`: on `AxDefer2.gdefer`
it is exactly `AxDefer2.Lproc`.)

THE POLICY CRITERION (`polDS GD gsrc e' e`, for every handout `e'` to `e`, sPol or lobp):
  `gmoLt e' e ∧ ∀ s ∈ gsrc e', gmoLt s e ∨ (s ∈ gsrc e ∧ gpo e' e)`
— every gate guarding `e'` either has its sources gmo-before the recipient, or also guards the
recipient, which is po-after `e'`.  `AxDefer2.naiveGatedRefuted` shows the criterion is not an
artifact.

THE GATE PROPERTIES assumed of `gsrc`: `AxDefer2.gateReal` (sources are po-earlier reads; a
gated WRITE carries the ctrl dep edge — riscv.cat rule 11) and `gateMono` (po-later events are
guarded by at least the same gates).

DEV-2 (`dev2DS`): `flowDev2 GD e' e → polDS GD gsrc e' e`.  The key step `flowGate`: along a
`gobCatFlow` chain out of a gated event, either the chain stays on the hart po-forward (the
gates carry over, `gateMono`) or it passes a write of that hart po-after the gate, which rule 11
puts gmo-after the gate's sources.

## Deviations from Rocq

1. Vocabulary as `AxDefer`/`AxDefer2` deviation 1 (`list_to_set` ↦ `LawfulSet.ofList`,
   `elements` ↦ `FiniteSet.toList`, `≡ₚ` ↦ `List.Perm`, `StronglySorted` ↦ `List.Pairwise`,
   `merge_sort R` ↦ `List.mergeSort` over the `decide`d relation, `vm_compute` ↦
   `decide +kernel`, `S k` ↦ `k + 1`, `|={⊤}[∅]▷=>^n` ↦ `|={⊤}[∅]▷=>^[n]`, wand chains
   `⊢ A -∗ B -∗ C`).
2. Rocq's instances `rank_le_dec`/`rank_le_total`/`rank_le_trans` (stdpp `RelDecision`/
   `Total`/`Transitive`) ↦ a `DecidableRel` instance `rankLeDec` and theorems `rankLeTotal`/
   `rankLeTrans`.
3. Section `canon`'s and `dev2`'s `Context`s are explicit arguments, in the order Rocq's
   section closing gives them (only the hypotheses each proof uses).  Rocq's `gpo` is
   `WeakRvwmoGraph.gpo`.
4. `flowGate` is proved by induction from the LAST step (Lean's `tc` is tail-built, see
   `MachCSL.Rel`); same statement.
5. Section `final` binds `[InvGS_gen hlc GF]` for any `hlc` (Rocq: `HasNoLc`), as
   `AxDefer.adequacyOrdG`.
6. `LcanonGdefer` is not one `vm_compute`: `List.mergeSort` is well-founded recursion and
   does not reduce in the kernel.  It is proved by uniqueness of sorted permutations
   (`List.Perm.eq_of_pairwise`): `Lproc` is rank-sorted and the ranks of `gdefer`'s events are
   distinct (both `decide +kernel`).  Same statement.
7. Lean-only helpers (file-qualified): `AxDefer3.natMaxEq` (`Nat.max` is `max`, for `omega`),
   `AxDefer3.rankSortSorted` (the sortedness half of `rank_sort_before`'s proof).

**Rocq → Lean name map.**  `StronglySorted_lookup'` `stronglySortedLookup'`, `rank_le`
`rankLe`, `rank_le_dec` `rankLeDec`, `rank_le_total` `rankLeTotal`, `rank_le_trans`
`rankLeTrans`, `rank_sort` `rankSort`, `rank_sort_perm` `rankSortPerm`, `rank_sort_before`
`rankSortBefore`, `order_of_rank` `orderOfRank`, `foldr_max_ge_init` `foldrMaxGeInit`,
`foldr_max_ge_elem` `foldrMaxGeElem`, `foldr_max_attained` `foldrMaxAttained`, `foldr_max_le`
`foldrMaxLe`, `gkey` `gkey`, `gkey_ge_self` `gkeyGeSelf`, `gkey_ge_src` `gkeyGeSrc`,
`gkey_attained` `gkeyAttained`, `gkey_le` `gkeyLe`, `gN` `AxDefer3.gN` (dup), `goff` `goff`,
`grank` `AxDefer3.grank` (dup), `goff_lt` `goffLt`, `grank_lt` `grankLt`, `gpo_irrefl'`
`gpoIrrefl'`, `gpo_trans'` `gpoTrans'`, `canon_gate` `canonGate`, `pol_DS` `polDS`,
`canon_pol` `canonPol`, `Lcanon` `Lcanon`, `Lcanon_gdefer` `LcanonGdefer`, `gate_mono`
`gateMono`, `gate_real_src_gmo` `gateRealSrcGmo`, `Lcanon_ok` `LcanonOk`, `gis_w_glbl`
`AxDefer3.gisWGlbl` (dup), `gate_w` `gateW`, `deps_gpo` `depsGpo`, `grf_src_w` `grfSrcW`,
`flow_step` `flowStep`, `flow_gmo` `flowGmo`, `flow_gate` `flowGate`, `dev2_DS` `dev2DS`,
`adequacy_ord_G_DS` `adequacyOrdGDS`, `adequacy_ord_G_dev2` `adequacyOrdGDev2`.

**Dropped:** only the `Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxDefer2
import Weak.AxTierA3

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. AN ORDER FROM A RANK -/

theorem stronglySortedLookup' {A : Type _} (R : A → A → Prop) (l : List A) (i j : Nat) (x y : A) :
    List.Pairwise R l → l[i]? = some x → l[j]? = some y → i < j → R x y :=
  stronglySortedLookupElim R l i j x y

def rankLe (ρ : Geid → Nat) (x y : Geid) : Prop := ρ x ≤ ρ y

instance rankLeDec (ρ : Geid → Nat) : DecidableRel (rankLe ρ) :=
  fun x y => Nat.decLe (ρ x) (ρ y)

theorem rankLeTotal (ρ : Geid → Nat) (x y : Geid) : rankLe ρ x y ∨ rankLe ρ y x := by
  unfold rankLe; omega

theorem rankLeTrans (ρ : Geid → Nat) (x y z : Geid) :
    rankLe ρ x y → rankLe ρ y z → rankLe ρ x z := by
  unfold rankLe; omega

def rankSort (ρ : Geid → Nat) (l : List Geid) : List Geid :=
  l.mergeSort fun x y => decide (rankLe ρ x y)

theorem rankSortPerm (ρ : Geid → Nat) (l : List Geid) : (rankSort ρ l).Perm l :=
  merge_sort_Permutation

/-- Lean-only: `rankSort` is sorted by rank. -/
theorem AxDefer3.rankSortSorted (ρ : Geid → Nat) (l : List Geid) :
    List.Pairwise (fun a b => decide (rankLe ρ a b) = true) (rankSort ρ l) :=
  StronglySorted_merge_sort
    (fun a b c h1 h2 => decide_eq_true
      (rankLeTrans ρ a b c (of_decide_eq_true h1) (of_decide_eq_true h2)))
    (fun a b => by
      rcases rankLeTotal ρ a b with h | h <;> simp [h])

theorem rankSortBefore (ρ : Geid → Nat) (l : List Geid) (n : Nat) (e e' : Geid) :
    l.Nodup → (rankSort ρ l)[n]? = some e → e' ∈ l → ρ e' < ρ e →
    e' ∈ takeL (rankSort ρ l) n := by
  intro _ Hn He' Hlt
  have Hs := AxDefer3.rankSortSorted ρ l
  have He'L : e' ∈ rankSort ρ l := (rankSortPerm ρ l).mem_iff.2 He'
  obtain ⟨j, Hj⟩ := elem_of_list_lookup_1 He'L
  unfold takeL
  rw [elemOfListToSet]
  by_cases hjn : j < n
  · exact AxAdequacy.memTakeOfLookup Hj hjn
  · exfalso
    by_cases hje : j = n
    · subst hje
      rw [Hn] at Hj
      cases Hj
      omega
    · have Hr := stronglySortedLookup' _ _ n j e e' Hs Hn Hj (by omega)
      have := of_decide_eq_true Hr
      unfold rankLe at this
      omega

theorem orderOfRank [Axpol] (GD : Gdexec) (Hnd : GD.gdG.gxGmo.Nodup)
    (ρ : Geid → Nat) (gsrc : Geid → GSet Geid)
    (Hg : ∀ e r, e ∈ GD.gdG.gxGmo → r ∈ gsrc e → r ∈ GD.gdG.gxGmo ∧ ρ r < ρ e)
    (Hp : ∀ e e', e ∈ GD.gdG.gxGmo → e' ∈ Axpol.sPol GD e ∪ Axpol.lobp GD e →
            e' ∈ GD.gdG.gxGmo ∧ ρ e' < ρ e) :
    (rankSort ρ GD.gdG.gxGmo).Perm GD.gdG.gxGmo ∧
    gsrcBefore (rankSort ρ GD.gdG.gxGmo) gsrc ∧
    axpolWfL GD (rankSort ρ GD.gdG.gxGmo) := by
  refine ⟨rankSortPerm _ _, ?_, ?_⟩
  · intro n e Hn r Hr
    have He : e ∈ GD.gdG.gxGmo := (rankSortPerm ρ _).mem_iff.1 (elem_of_list_lookup_2 Hn)
    obtain ⟨Hr', Hlt⟩ := Hg e r He Hr
    exact rankSortBefore ρ _ n e r Hnd Hn Hr' Hlt
  · intro n e Hn
    have He : e ∈ GD.gdG.gxGmo := (rankSortPerm ρ _).mem_iff.1 (elem_of_list_lookup_2 Hn)
    refine ⟨fun e' He' => ?_, fun e' He' => ?_⟩
    · obtain ⟨Hin, Hlt⟩ := Hp e e' He (elemOfUnionL He')
      exact rankSortBefore ρ _ n e e' Hnd Hn Hin Hlt
    · obtain ⟨Hin, Hlt⟩ := Hp e e' He (elemOfUnionR He')
      exact rankSortBefore ρ _ n e e' Hnd Hn Hin Hlt

/-! # 2. THE CANONICAL RANK -/

/-- Lean-only: `Nat.max` is the `max` that `omega` reads. -/
theorem AxDefer3.natMaxEq (a b : Nat) : Nat.max a b = max a b := rfl

theorem foldrMaxGeInit (b : Nat) (l : List Nat) : b ≤ l.foldr Nat.max b := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons y l ih => simp only [List.foldr_cons, AxDefer3.natMaxEq]; omega

theorem foldrMaxGeElem (b : Nat) (l : List Nat) (x : Nat) : x ∈ l → x ≤ l.foldr Nat.max b := by
  induction l with
  | nil => intro h; cases h
  | cons y l ih =>
    intro h
    simp only [List.foldr_cons, AxDefer3.natMaxEq]
    rcases List.mem_cons.1 h with rfl | hx
    · omega
    · have := ih hx; omega

theorem foldrMaxAttained (b : Nat) (l : List Nat) : l.foldr Nat.max b = b ∨ l.foldr Nat.max b ∈ l := by
  induction l with
  | nil => exact .inl rfl
  | cons y l ih =>
    simp only [List.foldr_cons, AxDefer3.natMaxEq]
    by_cases hy : l.foldr Nat.max b ≤ y
    · rw [Nat.max_eq_left hy]; exact .inr List.mem_cons_self
    · rw [Nat.max_eq_right (by omega)]
      rcases ih with h | h
      · exact .inl h
      · exact .inr (List.mem_cons_of_mem _ h)

theorem foldrMaxLe (b : Nat) (l : List Nat) (k : Nat) :
    b ≤ k → (∀ x, x ∈ l → x ≤ k) → l.foldr Nat.max b ≤ k := by
  intro Hb Hl
  induction l with
  | nil => exact Hb
  | cons y l ih =>
    simp only [List.foldr_cons, AxDefer3.natMaxEq]
    have h1 := Hl y List.mem_cons_self
    have h2 := ih fun x hx => Hl x (List.mem_cons_of_mem _ hx)
    omega

section canon

def gkey (G : Gexec) (gsrc : Geid → GSet Geid) (e : Geid) : Nat :=
  ((FiniteSet.toList (gsrc e)).map (gpos G)).foldr Nat.max (gpos G e)

theorem gkeyGeSelf (G : Gexec) (gsrc : Geid → GSet Geid) (e : Geid) : gpos G e ≤ gkey G gsrc e :=
  foldrMaxGeInit _ _

theorem gkeyGeSrc (G : Gexec) (gsrc : Geid → GSet Geid) (e r : Geid) :
    r ∈ gsrc e → gpos G r ≤ gkey G gsrc e := by
  intro Hr
  exact foldrMaxGeElem _ _ _ (List.mem_map.2 ⟨r, elemOfElements.2 Hr, rfl⟩)

theorem gkeyAttained (G : Gexec) (gsrc : Geid → GSet Geid) (e : Geid) :
    gkey G gsrc e = gpos G e ∨ ∃ s, s ∈ gsrc e ∧ gkey G gsrc e = gpos G s := by
  rcases foldrMaxAttained (gpos G e) ((FiniteSet.toList (gsrc e)).map (gpos G)) with H | H
  · exact .inl H
  · obtain ⟨s, Hin, Hs⟩ := List.mem_map.1 H
    exact .inr ⟨s, elemOfElements.1 Hin, Hs.symm⟩

theorem gkeyLe (G : Gexec) (gsrc : Geid → GSet Geid) (e : Geid) (k : Nat) :
    gpos G e ≤ k → (∀ r, r ∈ gsrc e → gpos G r ≤ k) → gkey G gsrc e ≤ k := by
  intro H1 H2
  refine foldrMaxLe _ _ _ H1 fun x hx => ?_
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
  exact H2 r (elemOfElements.1 hr)

def AxDefer3.gN (G : Gexec) : Nat := (G.gxGmo.map Prod.snd).foldr Nat.max 0 + 2

def goff (G : Gexec) (gsrc : Geid → GSet Geid) (e : Geid) : Nat :=
  if gpos G e < gkey G gsrc e then e.2 + 1 else 0

def AxDefer3.grank (G : Gexec) (gsrc : Geid → GSet Geid) (e : Geid) : Nat :=
  AxDefer3.gN G * gkey G gsrc e + goff G gsrc e

theorem goffLt (G : Gexec) (gsrc : Geid → GSet Geid) (e : Geid) :
    e ∈ G.gxGmo → goff G gsrc e < AxDefer3.gN G := by
  intro He
  have h : e.2 ≤ (G.gxGmo.map Prod.snd).foldr Nat.max 0 :=
    foldrMaxGeElem _ _ _ (List.mem_map.2 ⟨e, He, rfl⟩)
  unfold goff AxDefer3.gN
  split <;> omega

theorem grankLt (G : Gexec) (gsrc : Geid → GSet Geid) (e1 e2 : Geid) : e1 ∈ G.gxGmo →
    (gkey G gsrc e1 < gkey G gsrc e2 ∨
      (gkey G gsrc e1 = gkey G gsrc e2 ∧ goff G gsrc e1 < goff G gsrc e2)) →
    AxDefer3.grank G gsrc e1 < AxDefer3.grank G gsrc e2 := by
  intro He1 H
  unfold AxDefer3.grank
  rcases H with Hk | ⟨Hk, Ho⟩
  · have Ho := goffLt G gsrc e1 He1
    have Hm : AxDefer3.gN G * (gkey G gsrc e1 + 1) ≤ AxDefer3.gN G * gkey G gsrc e2 :=
      Nat.mul_le_mul_left _ Hk
    rw [Nat.mul_succ] at Hm
    omega
  · rw [Hk]; omega

theorem gpoIrrefl' (G : Gexec) (e : Geid) : ¬ WeakRvwmoGraph.gpo G e e := by
  rintro ⟨_, H, _⟩
  omega

theorem gpoTrans' (G : Gexec) (e1 e2 e3 : Geid) :
    WeakRvwmoGraph.gpo G e1 e2 → WeakRvwmoGraph.gpo G e2 e3 → WeakRvwmoGraph.gpo G e1 e3 := by
  rintro ⟨H1, H2, H3, _⟩ ⟨H4, H5, _, H6⟩
  exact ⟨H1.trans H4, by omega, H3, H6⟩

/-- Gate edges go up in rank. -/
theorem canonGate (G : Gexec) (gsrc : Geid → GSet Geid) (Hnd : G.gxGmo.Nodup)
    (Hpo : ∀ e r, r ∈ gsrc e → WeakRvwmoGraph.gpo G r e)
    (Hmono : ∀ e1 e2, WeakRvwmoGraph.gpo G e1 e2 → gsrc e1 ⊆ gsrc e2)
    (HsrcGmo : ∀ e r, r ∈ gsrc e → r ∈ G.gxGmo) (e r : Geid) :
    e ∈ G.gxGmo → r ∈ gsrc e → AxDefer3.grank G gsrc r < AxDefer3.grank G gsrc e := by
  intro He Hr
  have Hre := Hpo e r Hr
  have HrGmo := HsrcGmo e r Hr
  have Hk : gkey G gsrc r ≤ gkey G gsrc e :=
    gkeyLe G gsrc r _ (gkeyGeSrc G gsrc e r Hr)
      fun s Hs => gkeyGeSrc G gsrc e s (Hmono r e Hre s Hs)
  apply grankLt G gsrc r e HrGmo
  by_cases hlt : gkey G gsrc r < gkey G gsrc e
  · exact .inl hlt
  · right
    have Hkeq : gkey G gsrc r = gkey G gsrc e := by omega
    refine ⟨Hkeq, ?_⟩
    have Hdef : gpos G e < gkey G gsrc e := by
      by_cases hn : gpos G e < gkey G gsrc e
      · exact hn
      · exfalso
        have Hs := gkeyGeSelf G gsrc e
        have Hke : gkey G gsrc e = gpos G e := by omega
        rcases gkeyAttained G gsrc r with Ha | ⟨s, Hs', Ha⟩
        · have : r = e := gposInj G r e Hnd HrGmo He (by omega)
          subst this
          exact gpoIrrefl' G r Hre
        · have : s = e := gposInj G s e Hnd (HsrcGmo r s Hs') He (by omega)
          subst this
          exact gpoIrrefl' G s (gpoTrans' G s r s (Hpo r s Hs') Hre)
    obtain ⟨_, Hlt, _⟩ := Hre
    unfold goff
    rw [if_pos Hdef]
    split <;> omega

/-- The deferral-safe policy criterion. -/
def polDS (G : Gexec) (gsrc : Geid → GSet Geid) (e' e : Geid) : Prop :=
  gmoLt G e' e ∧ ∀ s, s ∈ gsrc e' → gmoLt G s e ∨ (s ∈ gsrc e ∧ WeakRvwmoGraph.gpo G e' e)

/-- Deferral-safe handouts go up in rank. -/
theorem canonPol (G : Gexec) (gsrc : Geid → GSet Geid) (Hnd : G.gxGmo.Nodup)
    (Hpo : ∀ e r, r ∈ gsrc e → WeakRvwmoGraph.gpo G r e)
    (HsrcGmo : ∀ e r, r ∈ gsrc e → r ∈ G.gxGmo) (e e' : Geid) :
    polDS G gsrc e' e → AxDefer3.grank G gsrc e' < AxDefer3.grank G gsrc e := by
  rintro ⟨⟨He', He, Hpos⟩, HDS⟩
  have Hk : gkey G gsrc e' ≤ gkey G gsrc e := by
    have := gkeyGeSelf G gsrc e
    refine gkeyLe G gsrc e' _ (by omega) fun s Hs => ?_
    rcases HDS s Hs with ⟨_, _, Hsl⟩ | ⟨Hs2, _⟩
    · omega
    · exact gkeyGeSrc G gsrc e s Hs2
  apply grankLt G gsrc e' e He'
  by_cases hlt : gkey G gsrc e' < gkey G gsrc e
  · exact .inl hlt
  · right
    have Hkeq : gkey G gsrc e' = gkey G gsrc e := by omega
    refine ⟨Hkeq, ?_⟩
    have Hse := gkeyGeSelf G gsrc e
    rcases gkeyAttained G gsrc e' with Ha | ⟨s, Hs, Ha⟩
    · omega
    · rcases HDS s Hs with ⟨_, _, Hsl⟩ | ⟨Hse', Hpo'⟩
      · omega
      · have Hdef : gpos G e < gkey G gsrc e := by
          by_cases hn : gpos G e < gkey G gsrc e
          · exact hn
          · exfalso
            have : s = e := gposInj G s e Hnd (HsrcGmo e' s Hs) He (by omega)
            subst this
            exact gpoIrrefl' G s (Hpo s s Hse')
        obtain ⟨_, Hlt2, _⟩ := Hpo'
        unfold goff
        rw [if_pos Hdef]
        split <;> omega

end canon

def Lcanon (GD : Gdexec) (gsrc : Geid → GSet Geid) : List Geid :=
  rankSort (AxDefer3.grank GD.gdG gsrc) GD.gdG.gxGmo

theorem LcanonGdefer : Lcanon gdefer gsrcD = Lproc := by
  have Hinj : ∀ a, a ∈ Lproc → ∀ b, b ∈ Lproc →
      AxDefer3.grank gdefer.gdG gsrcD a = AxDefer3.grank gdefer.gdG gsrcD b → a = b := by
    decide +kernel
  have Hsorted : List.Pairwise
      (fun a b => decide (rankLe (AxDefer3.grank gdefer.gdG gsrcD) a b) = true) Lproc := by
    decide +kernel
  refine List.Perm.eq_of_pairwise (fun a b ha hb hab hba => ?_)
    (AxDefer3.rankSortSorted _ _) Hsorted ((rankSortPerm _ _).trans LprocPerm.symm)
  have ha' : a ∈ Lproc := ((rankSortPerm _ _).trans LprocPerm.symm).mem_iff.1 ha
  have h1 := of_decide_eq_true hab
  have h2 := of_decide_eq_true hba
  unfold rankLe at h1 h2
  exact Hinj a ha' b hb (by omega)

/-- `gateMono`: a po-later event is guarded by at least the same gates. -/
def gateMono (GD : Gdexec) (gsrc : Geid → GSet Geid) : Prop :=
  ∀ e1 e2, WeakRvwmoGraph.gpo GD.gdG e1 e2 → gsrc e1 ⊆ gsrc e2

theorem gateRealSrcGmo (GD : Gdexec) (gsrc : Geid → GSet Geid) :
    rvwmoCatConsistent GD → gateReal GD gsrc →
    ∀ e r, r ∈ gsrc e → r ∈ GD.gdG.gxGmo := by
  intro Hcons Hreal e r Hr
  obtain ⟨_, Hrd, _⟩ := Hreal e r Hr
  exact gwfMemGmo _ _ Hcons.1 (WeakRvwmoGraph.glblIsRGmem _ _ Hrd)

/-- THE ORDER EXISTS for every deferral-safe policy. -/
theorem LcanonOk [Axpol] (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (gsrc : Geid → GSet Geid) (Hreal : gateReal GD gsrc) (Hmono : gateMono GD gsrc)
    (HDS : ∀ e e', e' ∈ Axpol.sPol GD e ∪ Axpol.lobp GD e → polDS GD.gdG gsrc e' e) :
    (Lcanon GD gsrc).Perm GD.gdG.gxGmo ∧ gsrcBefore (Lcanon GD gsrc) gsrc ∧
    axpolWfL GD (Lcanon GD gsrc) := by
  have Hnd := Hcons.1.1
  have Hsg := gateRealSrcGmo GD gsrc Hcons Hreal
  have Hpo : ∀ e r, r ∈ gsrc e → WeakRvwmoGraph.gpo GD.gdG r e := fun e r Hr => (Hreal e r Hr).1
  apply orderOfRank GD Hnd
  · intro e r He Hr
    exact ⟨Hsg e r Hr, canonGate GD.gdG gsrc Hnd Hpo Hmono Hsg e r He Hr⟩
  · intro e e' _ Hin
    have Hds := HDS e e' Hin
    exact ⟨Hds.1.1, canonPol GD.gdG gsrc Hnd Hpo Hsg e e' Hds⟩

/-! # 3. DEV-2 HANDOUTS ARE DEFERRAL-SAFE -/

section dev2

theorem AxDefer3.gisWGlbl (GD : Gdexec) (e : Geid) : gisW GD.gdG e = true → glblIs GD.gdG e lbIsW := by
  unfold gisW
  cases hl : gxLbl GD.gdG e with
  | none => intro h; cases h
  | some l => intro h; exact ⟨l, hl, h⟩

/-- Rule 11: a gated write is gmo-after the gate's sources. -/
theorem gateW (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (gsrc : Geid → GSet Geid)
    (Hreal : gateReal GD gsrc) (w r : Geid) :
    r ∈ gsrc w → gisW GD.gdG w = true → gmoLt GD.gdG r w := by
  intro Hr Hw
  obtain ⟨_, _, Hdep⟩ := Hreal w r Hr
  exact Hcons.2.2.2.2.2 (r, w) (Hdep (AxDefer3.gisWGlbl GD w Hw))

theorem depsGpo (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (x y : Geid) :
    gdepsRel GD x y → WeakRvwmoGraph.gpo GD.gdG x y ∧ gisW GD.gdG y = true := by
  intro Hd
  obtain ⟨H1, H2, ⟨l1, Hl1, _⟩, ⟨l2, Hl2, Hw⟩⟩ := Hcons.2.2.2.2.1 (x, y) Hd
  refine ⟨⟨H1, H2, by simp [Hl1], by simp [Hl2]⟩, ?_⟩
  simp only [gisW, Hl2]
  exact Hw

theorem grfSrcW (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (m y : Geid) :
    WeakRvwmoAcyc.grf GD.gdG m y →
    gisW GD.gdG m = true ∧ (gmoLt GD.gdG m y ∨ WeakRvwmoGraph.gpo GD.gdG m y) := by
  rintro ⟨a, t, v, Hrd, Hwa⟩
  refine ⟨((gwritesElemOf _ _).1 (gwriteAtGwrites _ _ _ Hwa)).2, ?_⟩
  have Hval := (Hcons.2.2.1 y a t v Hrd).1
  cases t with
  | zero => simp [gwriteAt] at Hwa
  | succ t =>
    obtain ⟨w, Hw, _, Hvis⟩ := Hval
    rw [Hwa] at Hw
    cases Hw
    exact Hvis

/-- One `gobrCatFlow` step out of `x`: `x` is a write, or the step is po-forward, or it passes a
po-later write of `x`'s hart that is gmo-before the target (rule 12, non-forwarded). -/
theorem flowStep (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (x y : Geid) :
    gobrCatFlow GD x y →
    gisW GD.gdG x = true ∨ WeakRvwmoGraph.gpo GD.gdG x y ∨
      ∃ m, WeakRvwmoGraph.gpo GD.gdG x m ∧ gisW GD.gdG m = true ∧ gmoLt GD.gdG m y := by
  rintro ((H | H) | H | H | H | ⟨_, H⟩)
  · exact .inr (.inl (gppoCat6Gpo _ _ _ H))
  · obtain ⟨Hag, m, Hd, Hrf⟩ := H
    obtain ⟨Hxm, Hmw⟩ := depsGpo GD Hcons x m Hd
    rcases (grfSrcW GD Hcons m y Hrf).2 with Hlt | Hmy
    · exact .inr (.inr ⟨m, Hxm, Hmw, Hlt⟩)
    · exact .inr (.inl (gpoTrans' _ _ _ _ Hxm Hmy))
  · exact .inr (.inl (depsGpo GD Hcons x y H).1)
  · exact .inl (grfSrcW GD Hcons x y H.1).1
  · obtain ⟨a, v, v', Hw, _⟩ := H
    exact .inl (WeakRvwmoGraph.gwritesByteGisW _ _ _ _ Hw)
  · exact .inl H

theorem flowGmo (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (x y : Geid) :
    gobCatFlow GD x y → gmoLt GD.gdG x y :=
  fun H => obCatSubGmo GD x y Hcons (gobCatFlowSub GD x y H)

/-- THE KEY STEP. -/
theorem flowGate (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (gsrc : Geid → GSet Geid)
    (Hreal : gateReal GD gsrc) (Hmono : gateMono GD gsrc) (x e : Geid) :
    gobCatFlow GD x e →
    ∀ s, s ∈ gsrc x → gmoLt GD.gdG s e ∨ (s ∈ gsrc e ∧ WeakRvwmoGraph.gpo GD.gdG x e) := by
  intro Hf
  induction Hf with
  | single H =>
    rename_i y
    have Hxe := flowGmo GD Hcons _ _ (tc_once H)
    intro s Hs
    rcases flowStep GD Hcons x y H with Hw | Hpo | ⟨m, Hxm, Hmw, Hmy⟩
    · exact .inl (gmoLtTrans _ _ _ _ (gateW GD Hcons gsrc Hreal x s Hs Hw) Hxe)
    · exact .inr ⟨Hmono x y Hpo s Hs, Hpo⟩
    · exact .inl (gmoLtTrans _ _ _ _ (gateW GD Hcons gsrc Hreal m s (Hmono x m Hxm s Hs) Hmw) Hmy)
  | tail Hrest H IH =>
    rename_i u y
    have Huy := flowGmo GD Hcons _ _ (tc_once H)
    intro s Hs
    rcases IH s Hs with Hl | ⟨Hin, Hxu⟩
    · exact .inl (gmoLtTrans _ _ _ _ Hl Huy)
    · rcases flowStep GD Hcons u y H with Hw | Hpo | ⟨m, Hum, Hmw, Hmy⟩
      · exact .inl (gmoLtTrans _ _ _ _ (gateW GD Hcons gsrc Hreal u s Hin Hw) Huy)
      · exact .inr ⟨Hmono u y Hpo s Hin, gpoTrans' _ _ _ _ Hxu Hpo⟩
      · exact .inl (gmoLtTrans _ _ _ _
          (gateW GD Hcons gsrc Hreal m s (Hmono u m Hum s Hin) Hmw) Hmy)

/-- DEV-2 IS DEFERRAL-SAFE. -/
theorem dev2DS (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (gsrc : Geid → GSet Geid)
    (Hreal : gateReal GD gsrc) (Hmono : gateMono GD gsrc) (e' e : Geid) :
    flowDev2 GD e' e → polDS GD.gdG gsrc e' e := by
  intro Hf
  refine ⟨flowDev2Gmo GD Hcons e' e Hf, fun s Hs => ?_⟩
  rcases Hf with Hf | ⟨⟨Hpo, _⟩, _⟩
  · exact flowGate GD Hcons gsrc Hreal Hmono e' e Hf s Hs
  · exact .inr ⟨Hmono e' e Hpo s Hs, Hpo⟩

end dev2

/-! # 4. GATED PHASE 2 WITHOUT AN ORDER PREMISE -/

section final
variable [Axpol]
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF]

theorem adequacyOrdGDS (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (gsrc : Geid → GSet Geid) (φ : Geid → Prop)
    (Hreal : gateReal GD gsrc) (Hmono : gateMono GD gsrc)
    (HDS : ∀ e e', e' ∈ Axpol.sPol GD e ∪ Axpol.lobp GD e → polDS GD.gdG gsrc e' e)
    (na : Mea GF) (ea : Sra GF)
    (Hpure : gateSrcPure na gsrc φ)
    (HdomEq : (FiniteMap.dom_set ea : GSet Geid) = FiniteMap.dom_set na)
    (Hdom : (LawfulSet.ofList GD.gdG.gxGmo : GSet Geid) ⊆ FiniteMap.dom_set na)
    (HeaLob : ∀ e0 gm, get? ea e0 = some gm → (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0)
    (σ0 : AxirisG.obSt GF) :
    ⊢ ordEaTodoG GD gsrc φ ea na (Lcanon GD gsrc) 0 -∗
      AxirisG.obStInterp GD σ0 ∅ -∗
      |={⊤}[∅]▷=>^[GD.gdG.gxGmo.length]
        ∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList GD.gdG.gxGmo) ∗
          ([∗set] e0 ∈ (LawfulSet.ofList GD.gdG.gxGmo : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? na e0)) ∗
          ⌜∀ e, e ∈ GD.gdG.gxGmo → gateOk gsrc φ e⌝ := by
  obtain ⟨Hperm, Hbef, Hpol⟩ := LcanonOk GD Hcons gsrc Hreal Hmono HDS
  have HsetL : (LawfulSet.ofList (Lcanon GD gsrc) : GSet Geid) = LawfulSet.ofList GD.gdG.gxGmo :=
    setEq.2 fun x => by rw [elemOfListToSet, elemOfListToSet]; exact Hperm.mem_iff
  have HdomL : (LawfulSet.ofList (Lcanon GD gsrc) : GSet Geid) ⊆ FiniteMap.dom_set na := by
    rw [HsetL]; exact Hdom
  have h := adequacyOrdG GD Hcons (Lcanon GD gsrc) Hperm Hpol gsrc φ Hbef na ea Hpure HdomEq
    HdomL HeaLob σ0
  rw [Hperm.length_eq, HsetL] at h
  have hpost :
      iprop(∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList GD.gdG.gxGmo) ∗
          ([∗set] e0 ∈ (LawfulSet.ofList GD.gdG.gxGmo : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? na e0)) ∗
          ⌜∀ e, e ∈ Lcanon GD gsrc → gateOk gsrc φ e⌝) ⊢
      iprop(∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList GD.gdG.gxGmo) ∗
          ([∗set] e0 ∈ (LawfulSet.ofList GD.gdG.gxGmo : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? na e0)) ∗
          ⌜∀ e, e ∈ GD.gdG.gxGmo → gateOk gsrc φ e⌝) := by
    iintro ⟨%σ, Hob, Hbag, %Hall⟩
    iexists σ
    isplitl [Hob]
    · iexact Hob
    isplitl [Hbag]
    · iexact Hbag
    · ipureintro
      exact fun e He => Hall e (Hperm.mem_iff.2 He)
  iintro Htodo Hob
  iapply (AxDefer.stepFupdNMono (n := GD.gdG.gxGmo.length) hpost)
  iapply h $$ Htodo Hob

/-- DEV-2 UNDER DEFERRED READS: any `flowDev2`-bounded policy. -/
theorem adequacyOrdGDev2 (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (gsrc : Geid → GSet Geid) (φ : Geid → Prop)
    (Hreal : gateReal GD gsrc) (Hmono : gateMono GD gsrc)
    (HsPol : ∀ e e', e' ∈ Axpol.sPol GD e → flowDev2 GD e' e)
    (Hlobp : ∀ e e', e' ∈ Axpol.lobp GD e → flowDev2 GD e' e)
    (na : Mea GF) (ea : Sra GF)
    (Hpure : gateSrcPure na gsrc φ)
    (HdomEq : (FiniteMap.dom_set ea : GSet Geid) = FiniteMap.dom_set na)
    (Hdom : (LawfulSet.ofList GD.gdG.gxGmo : GSet Geid) ⊆ FiniteMap.dom_set na)
    (HeaLob : ∀ e0 gm, get? ea e0 = some gm → (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0)
    (σ0 : AxirisG.obSt GF) :
    ⊢ ordEaTodoG GD gsrc φ ea na (Lcanon GD gsrc) 0 -∗
      AxirisG.obStInterp GD σ0 ∅ -∗
      |={⊤}[∅]▷=>^[GD.gdG.gxGmo.length]
        ∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList GD.gdG.gxGmo) ∗
          ([∗set] e0 ∈ (LawfulSet.ofList GD.gdG.gxGmo : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? na e0)) ∗
          ⌜∀ e, e ∈ GD.gdG.gxGmo → gateOk gsrc φ e⌝ :=
  adequacyOrdGDS GD Hcons gsrc φ Hreal Hmono
    (fun e e' Hin => by
      rcases elemOfUnion.1 Hin with Hin | Hin
      · exact dev2DS GD Hcons gsrc Hreal Hmono e' e (HsPol e e' Hin)
      · exact dev2DS GD Hcons gsrc Hreal Hmono e' e (Hlobp e e' Hin))
    na ea Hpure HdomEq Hdom HeaLob σ0

end final

end Weak
