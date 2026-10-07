/-
Weak: **THE n-BYTE LIFT of `AxProtGate`'s owned-read machinery** (LB/AxSL rev 7): `tokn` glues `n`
single-byte `tokTie` resources; the byte-general owned-write notions carry the writer's value
explicitly; one `flowEqDyn`-level read step combines `n` independent per-byte pure derivations
(`bigSepL_impl` + `bigSepL_pure_1`), the single `obStInterp` transition performed once; the WP read
rules (label-witnessed and ownership-witnessed); the n-byte WRITE side (`writenHist`, one appended
entry per byte) and its WP rule; the `skelAxirisG` instances.

Rocq: `iris/AxProtBytes.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`AxProtGate` is single-byte (its `rdat`/`wdat`).  The graph model is per-byte (`greadsByte` /
`gwritesByte`), so the owned-read side lifts by PER-BYTE COMPOSITION.  KEY FACT: the read step of
`obStInterp` (`protInvReadStep`) is address- and byte-count-independent, and `protInv` is
persistent, so the coverage wand can be used once per byte.  The owned-write notions
(`ownedLastWriteb`/`ownedForwardedWriteb`/`ownedExpectedWriteb`) take the VALUE `v` as an argument
(an n-byte store may be the writer for several bytes of an n-byte load, at different values), and
need only `rvwmoCatConsistent`.  FINDINGS: (1) closed — `readnValueAgreePure` reconciles the label's
value list with the ownership list (`greadsByteDet` byte by byte), `wpReadOwnedTokn` uses the
ownership list; (2) the write side is done here by `writenHist` (no existential per byte, so
`bigSepL_sep` splits snapshot and tie); (3) the n-byte GATE composition (`naOf'`-style) is not
attempted (Rocq leaves it open).

**Fetches.** Graph events only (Stage C); nothing here mentions fetches.

## Deviations from Rocq

1. NAMES: camelCase (map below); no name of this file is in the dup table.  Lean-only helpers are
   file-qualified `AxProtBytes.*`.
2. CONTEXTS (as `AxProtGate` deviation 4): the section context (`γ`, `Hob_eq`, `GD`, `Hcons`,
   `rdatn`, `HrdatnSpec`) becomes explicit arguments in that order, each declaration taking exactly
   the ones it uses (Rocq's automatic section-variable inclusion / `Proof using`); `[Axpol]` is an
   instance binder of the WP rules; `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc`.
3. VOCABULARY: `Hs !! j` ↦ `Hs[j]?`, `Z.of_nat j` ↦ `(j : Int)`, `last` ↦ `List.getLast?`, `.*1`/`.*2`
   ↦ `List.map Prod.fst`/`Prod.snd`, `Forall2` ↦ `List.Forall₂`, `imap` ↦ `List.mapIdx`, `dom` ↦
   `FiniteMap.dom_set`, `list_to_set` ↦ `LawfulSet.ofList`, `<[(i,k):=P]> na` ↦ `insert na (i, k) P`,
   `gpo` ↦ `WeakRvwmoGraph.gpo`.  The TOTAL lookups `Hs !!! j`/`Vs !!! j` (stdpp `Inhabited`
   defaults) ↦ `Hs.getD j []`/`Vs.getD j 0` (explicit defaults; only in-range indices matter).
4. STATEMENT SHAPES (as `AxProtGate` deviation 5): wand chains `⊢ A -∗ B -∗ C`; the flow lemmas
   `(([∗map] …) -∗ X) ⊢ flowEqDyn …`.
5. §6 `Skel`: Rocq's `T : Z → Prop` oracle parameter of `skel_axirisG` is gone (Stage C); the
   instance is passed explicitly, `(axG := skelAxirisG γg Φp)`.  Rocq's `Local Instance
   skel_axirisGn_inst` is not a declaration here (the lemmas name the instance).
6. Lean-only helpers: `AxProtBytes.covIntuit` (the coverage wand family is persistent — Rocq gets it
   from `wand_persistent` over `Plain ⌜φ⌝`; IProp has no `BIPlainly`, so it is proved via
   `∀ _ : φ`), `AxProtBytes.writenHistLookupInv` (inversion of `writenHistLookup`).

**Rocq → Lean name map.**  `tokn` `tokn`, `tokn_nil` `toknNil`, `owned_last_writeb`
`ownedLastWriteb`, `owned_forwarded_writeb` `ownedForwardedWriteb`, `owned_expected_writeb`
`ownedExpectedWriteb`, `owned_forwarded_writeb_uniq` `ownedForwardedWritebUniq`,
`owned_last_writeb_uniq` `ownedLastWritebUniq`, `owned_expected_writeb_uniq`
`ownedExpectedWritebUniq`, `greads_byte_owned_expected_writeb` `greadsByteOwnedExpectedWriteb`,
`greads_byte_owned_expected_writeb_none` `greadsByteOwnedExpectedWritebNone`,
`owned_read_expectedb` `ownedReadExpectedb`, `readn_pure_facts` `readnPureFacts`,
`flow_eq_owned_readn_fwd` `flowEqOwnedReadnFwd`, `wp_read_owned_tokn_fwd` `wpReadOwnedToknFwd`,
`readn_value_agree_pure` `readnValueAgreePure`, `readn_value_agree` `readnValueAgree`,
`wp_read_owned_tokn` `wpReadOwnedTokn`, `writen_hist` `writenHist`, `writen_hist_lookup`
`writenHistLookup`, `writen_hist_length` `writenHistLength`, `tok_tie_after_write_snap`
`tokTieAfterWriteSnap`, `big_sepL_reindex` `bigSepLReindex`, `flow_eq_owned_writen_chain_snap`
`flowEqOwnedWritenChainSnap`, `wp_write_owned_tokn` `wpWriteOwnedTokn`,
`annot_alloc_at_progress_skeln` `annotAllocAtProgressSkeln`, `wp_read_owned_tokn_fwd_skel`
`wpReadOwnedToknFwdSkel`, `wp_read_owned_tokn_skel` `wpReadOwnedToknSkel`,
`wp_write_owned_tokn_skel` `wpWriteOwnedToknSkel`.

**Not ported:** the section `Let`s `Hwf`/`Hnd_gmo` (inlined as `Hcons.1`/`Hcons.1.1`), the
`Local Instance skel_axirisGn_inst` (deviation 5) and the `Print Assumptions` audits.
-/
import Weak.AxProtGate

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. THE ASSEMBLY -/

/-! ## 1.1 The n-byte token -/

section tokn

variable {GF : BundledGFunctors} [AxlogG GF Hent]

/-- The n-byte token: byte `a + j` carries the `j`-th history's `tokTie`. -/
def tokn (γ : GName) (GD : Gdexec) (a : Int) (Hs : List (List Hent)) (S : GMapF Geid Qp) :
    IProp GF :=
  iprop([∗list] j ↦ H ∈ Hs, tokTie GD γ (a + (j : Int)) H S)

theorem toknNil (γ : GName) (GD : Gdexec) (a : Int) (S : GMapF Geid Qp) :
    ⊢ tokn (GF := GF) γ GD a [] S := by
  unfold tokn
  exact BigSepL.bigSepL_nil.2

end tokn

/-! ## 1.2 The byte-general owned-write notions (value explicit) -/

def ownedLastWriteb (GD : Gdexec) (a : Int) (r w : Geid) (v : BitVec 8) : Prop :=
  gwritesByte GD.gdG w a v ∧ gmoLt GD.gdG w r ∧
  (∀ w' v', gwritesByte GD.gdG w' a v' → gmoLt GD.gdG w' r → gwix GD.gdG w' ≤ gwix GD.gdG w)

def ownedForwardedWriteb (GD : Gdexec) (a : Int) (r w : Geid) (v : BitVec 8) : Prop :=
  gwritesByte GD.gdG w a v ∧ WeakRvwmoGraph.gpo GD.gdG w r ∧
  ¬ gmoLt GD.gdG w r ∧
  (∀ w' v', gwritesByte GD.gdG w' a v' → WeakRvwmoGraph.gpo GD.gdG w w' →
    WeakRvwmoGraph.gpo GD.gdG w' r → False)

def ownedExpectedWriteb (GD : Gdexec) (a : Int) (r w : Geid) (v : BitVec 8) : Prop :=
  ownedForwardedWriteb GD a r w v ∨
  (ownedLastWriteb GD a r w v ∧ ¬ ∃ w' v', ownedForwardedWriteb GD a r w' v')

theorem ownedForwardedWritebUniq (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (r : Geid)
    (a : Int) (w1 w2 : Geid) (v1 v2 : BitVec 8) (Hrd : ∃ t v, greadsByte GD.gdG r a t v) :
    ownedForwardedWriteb GD a r w1 v1 → ownedForwardedWriteb GD a r w2 v2 → w1 = w2 ∧ v1 = v2 := by
  intro ⟨Hwb1, Hpo1, Hnmo1, Hni1⟩ ⟨Hwb2, Hpo2, Hnmo2, Hni2⟩
  obtain ⟨t, vr, Hrd⟩ := Hrd
  obtain ⟨Hrf1, Heqv1⟩ := ownForwardCat' GD a w1 r v1 t vr Hcons Hpo1 Hwb1 Hrd Hnmo1 Hni1
  obtain ⟨Hrf2, Heqv2⟩ := ownForwardCat' GD a w2 r v2 t vr Hcons Hpo2 Hwb2 Hrd Hnmo2 Hni2
  exact ⟨grfAtDet _ a w1 w2 r Hrf1 Hrf2, Heqv1.symm.trans Heqv2⟩

theorem ownedLastWritebUniq (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (a : Int)
    (r w1 w2 : Geid) (v1 v2 : BitVec 8) :
    ownedLastWriteb GD a r w1 v1 → ownedLastWriteb GD a r w2 v2 → w1 = w2 ∧ v1 = v2 := by
  intro ⟨Hwb1, Hmo1, Hmax1⟩ ⟨Hwb2, Hmo2, Hmax2⟩
  have Hw1w := gwritesByteGwrites _ _ _ _ Hcons.1 Hwb1
  have Hw2w := gwritesByteGwrites _ _ _ _ Hcons.1 Hwb2
  have h12 := Hmax2 w1 v1 Hwb1 Hmo1
  have h21 := Hmax1 w2 v2 Hwb2 Hmo2
  have Hw12 : w1 = w2 := gwixInj _ _ _ Hcons.1.1 Hw1w Hw2w (by omega)
  subst Hw12
  exact ⟨rfl, gwritesByteDet _ _ _ _ _ Hwb1 Hwb2⟩

theorem ownedExpectedWritebUniq (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (r : Geid)
    (a : Int) (w1 w2 : Geid) (v1 v2 : BitVec 8) (Hrd : ∃ t v, greadsByte GD.gdG r a t v) :
    ownedExpectedWriteb GD a r w1 v1 → ownedExpectedWriteb GD a r w2 v2 → w1 = w2 ∧ v1 = v2 := by
  rintro (Hf1 | ⟨Ho1, Hno1⟩) (Hf2 | ⟨Ho2, Hno2⟩)
  · exact ownedForwardedWritebUniq GD Hcons r a w1 w2 v1 v2 Hrd Hf1 Hf2
  · exact absurd ⟨w1, v1, Hf1⟩ Hno2
  · exact absurd ⟨w2, v2, Hf2⟩ Hno1
  · exact ownedLastWritebUniq GD Hcons a r w1 w2 v1 v2 Ho1 Ho2

/-- THE KEY GRAPH LEMMA: any rf-source `wl` of `r` at byte `a` is `ownedExpectedWriteb` for the
read's own value. -/
theorem greadsByteOwnedExpectedWriteb (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (r : Geid)
    (a : Int) (t : Nat) (v : BitVec 8) (wl : Geid)
    (Hgb : greadsByte GD.gdG r a t v) (Hwrat : gwriteAt GD.gdG t = some wl) :
    ownedExpectedWriteb GD a r wl v := by
  have Hwix := (gwriteAtInv GD.gdG t wl Hcons.1.1 Hwrat).2
  have ⟨_, Hppo, Hgv, _⟩ := Hcons
  have Hrule1 : ∀ e1 e2, gppo1 GD.gdG e1 e2 → gmoLt GD.gdG e1 e2 :=
    fun e1 e2 h => Hppo e1 e2 (Or.inl (Or.inl h))
  obtain ⟨Hsrc, Hmaxg⟩ := Hgv r a t v Hgb
  cases t with
  | zero => simp [gwriteAt] at Hwrat
  | succ t' =>
    obtain ⟨w0, Hwat0, Hwb0, Hvis0⟩ := Hsrc
    have hw : w0 = wl := Option.some.inj (Hwat0.symm.trans Hwrat)
    rw [hw] at Hwb0 Hvis0
    by_cases Hmo : gmoLt GD.gdG wl r
    · refine Or.inr ⟨⟨Hwb0, Hmo, fun w' v' Hwb' Hmo' => ?_⟩, ?_⟩
      · rw [Hwix]; exact Hmaxg w' v' Hwb' (Or.inl Hmo')
      · rintro ⟨w1, v1, Hwb1, Hpo1, Hnmo1, Hnoint1⟩
        have Hrfw1 := (ownForwardCat' GD a w1 r v1 (t' + 1) v Hcons Hpo1 Hwb1 Hgb Hnmo1 Hnoint1).1
        have Hrfwl : grfAt GD.gdG a wl r := ⟨t' + 1, v, Hgb, Hwrat⟩
        have Heqw := grfAtDet _ a w1 wl r Hrfw1 Hrfwl
        rw [Heqw] at Hnmo1
        exact Hnmo1 Hmo
    · refine Or.inl ?_
      rcases Hvis0 with Hmo0 | Hpo0
      · exact absurd Hmo0 Hmo
      refine ⟨Hwb0, Hpo0, Hmo, ?_⟩
      intro w' v' Hwb' Hpo1 Hpo2
      have Hmo1 : gmoLt GD.gdG wl w' :=
        Hrule1 _ _ ⟨Hpo1, a, Or.inl ⟨v, Hwb0⟩, v', Hwb'⟩
      have Hle := Hmaxg w' v' Hwb' (Or.inr Hpo2)
      rw [← Hwix] at Hle
      have Hww := gwritesByteGwrites _ _ _ _ Hcons.1 Hwb0
      have Hw'w := gwritesByteGwrites _ _ _ _ Hcons.1 Hwb'
      obtain ⟨_, _, Hgpos⟩ := Hmo1
      have := (gwixGposLt GD.gdG wl w' Hcons.1.1 Hww Hw'w).2 Hgpos
      omega

theorem greadsByteOwnedExpectedWritebNone (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (r : Geid) (a : Int) (v : BitVec 8) (wl : Geid) (vl : BitVec 8) :
    greadsByte GD.gdG r a 0 v → ¬ ownedExpectedWriteb GD a r wl vl := by
  intro Hgb Hexp
  have ⟨_, _, Hgv, _⟩ := Hcons
  obtain ⟨_, Hmaxg⟩ := Hgv r a 0 v Hgb
  rcases Hexp with ⟨Hwb, Hpo, _, _⟩ | ⟨⟨Hwb, Hmo, _⟩, _⟩
  · have Hpos := WeakRvwmoGraph.gwixPos _ _ (gwritesByteGwrites _ _ _ _ Hcons.1 Hwb)
    have Hle := Hmaxg wl vl Hwb (Or.inr Hpo)
    omega
  · have Hpos := WeakRvwmoGraph.gwixPos _ _ (gwritesByteGwrites _ _ _ _ Hcons.1 Hwb)
    have Hle := Hmaxg wl vl Hwb (Or.inl Hmo)
    omega

/-! # 2. THE GHOST-LEVEL, SINGLE-BYTE STEP -/

section ghost

variable {GF : BundledGFunctors} [AxlogG GF Hent]

theorem ownedReadExpectedb (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (r : Geid)
    (a : Int) (Hl : List Hent) (S : GMapF Geid Qp) (wl : Geid) (vl : BitVec 8)
    (Hwr : ∀ p, p ∈ Hl → gwritesByte GD.gdG p.1 a p.2)
    (Hch : chainWith (gmoLt GD.gdG) (Hl.map Prod.fst))
    (Hown : ∀ w v, gwritesByte GD.gdG w a v → WeakRvwmoGraph.gpo GD.gdG w r →
      w ∈ Hl.map Prod.fst)
    (Hlast : Hl.getLast? = some (wl, vl))
    (Hrd : ∃ t v, greadsByte GD.gdG r a t v)
    (Hcase : (∃ e, e ∈ (FiniteMap.dom_set S : GSet Geid) ∧ gmoLt GD.gdG e r)
      ∨
      (wl ∈ (FiniteMap.dom_set S : GSet Geid) ∧
       (∀ e, e ∈ (FiniteMap.dom_set S : GSet Geid) → ¬ gmoLt GD.gdG e r) ∧
       WeakRvwmoGraph.gpo GD.gdG wl r ∧
       (∀ w' v', gwritesByte GD.gdG w' a v' →
         WeakRvwmoGraph.gpo GD.gdG wl w' → WeakRvwmoGraph.gpo GD.gdG w' r → False))) :
    ⊢ tokTie (GF := GF) GD γ a Hl S -∗
      (∀ w v, ⌜gwritesByte GD.gdG w a v⌝ -∗ ⌜gmoLt GD.gdG w r⌝ -∗
        ∃ H', ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap γ a H') -∗
      ⌜ownedExpectedWriteb GD a r wl vl ∧ ∃ t, greadsByte GD.gdG r a t vl⌝ := by
  iintro Htie Hcov
  ihave %hres := ownedReadRule GD a r γ Hl S wl vl Hcons Hwr Hch Hown Hlast Hrd Hcase $$
    [$Htie $Hcov]
  obtain ⟨⟨t, v, Hgb, Hwrat⟩, Hval⟩ := hres
  have Heqv : v = vl := Hval t v Hgb
  subst Heqv
  ipureintro
  exact ⟨greadsByteOwnedExpectedWriteb GD Hcons r a t v wl Hgb Hwrat, t, Hgb⟩

/-- Lean-only: the per-byte coverage family is persistent (Rocq: `wand_persistent` over the
plain `⌜φ⌝`; here via `∀ _ : φ`). -/
theorem AxProtBytes.covIntuit (γ : GName) (GD : Gdexec) (a : Int) (r : Geid) :
    iprop(∀ (j : Nat) (w : Geid) (v : BitVec 8), ⌜gwritesByte GD.gdG w (a + (j : Int)) v⌝ -∗
        ⌜gmoLt GD.gdG w r⌝ -∗
        ∃ H' : List Hent, ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap (GF := GF) γ (a + (j : Int)) H') ⊢
      iprop(□ ∀ (j : Nat) (w : Geid) (v : BitVec 8), ⌜gwritesByte GD.gdG w (a + (j : Int)) v⌝ -∗
        ⌜gmoLt GD.gdG w r⌝ -∗
        ∃ H' : List Hent, ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap (GF := GF) γ (a + (j : Int)) H') := by
  iintro H
  ihave H2 : ∀ (j : Nat) (w : Geid) (v : BitVec 8),
      ∀ (_ : gwritesByte GD.gdG w (a + (j : Int)) v), ∀ (_ : gmoLt GD.gdG w r),
        ∃ H' : List Hent, ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap (GF := GF) γ (a + (j : Int)) H'
    $$ [H]
  · iintro %j %w %v %hq %hr
    ihave H3 := H $$ %j %w %v %hq %hr
    iexact H3
  icases H2 with #H2
  imodintro
  iintro %j %w %v %hq %hr
  ihave H3 := H2 $$ %j %w %v %hq %hr
  iexact H3

/-! # 3. THE n-BYTE COMBINATION -/

theorem readnPureFacts (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (a : Int)
    (Hs : List (List Hent)) (S : GMapF Geid Qp) (r : Geid)
    (Hwr : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ p, p ∈ H → gwritesByte GD.gdG p.1 (a + (j : Int)) p.2)
    (Hch : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H → chainWith (gmoLt GD.gdG) (H.map Prod.fst))
    (Hown : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ w v, gwritesByte GD.gdG w (a + (j : Int)) v → WeakRvwmoGraph.gpo GD.gdG w r →
        w ∈ H.map Prod.fst)
    (Hrd : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H → ∃ t v, greadsByte GD.gdG r (a + (j : Int)) t v)
    (Hcase : ∀ (j : Nat) (H : List Hent) wl vl, Hs[j]? = some H → H.getLast? = some (wl, vl) →
      (∃ e, e ∈ (FiniteMap.dom_set S : GSet Geid) ∧ gmoLt GD.gdG e r)
      ∨
      (wl ∈ (FiniteMap.dom_set S : GSet Geid) ∧
       (∀ e, e ∈ (FiniteMap.dom_set S : GSet Geid) → ¬ gmoLt GD.gdG e r) ∧
       WeakRvwmoGraph.gpo GD.gdG wl r ∧
       (∀ w' v', gwritesByte GD.gdG w' (a + (j : Int)) v' →
         WeakRvwmoGraph.gpo GD.gdG wl w' → WeakRvwmoGraph.gpo GD.gdG w' r → False))) :
    ⊢ (∀ (j : Nat) (w : Geid) (v : BitVec 8), ⌜gwritesByte GD.gdG w (a + (j : Int)) v⌝ -∗
        ⌜gmoLt GD.gdG w r⌝ -∗
        ∃ H' : List Hent, ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap (GF := GF) γ (a + (j : Int)) H') -∗
      tokn γ GD a Hs S -∗
      ⌜∀ (j : Nat) (H : List Hent), Hs[j]? = some H → ∀ wl vl, H.getLast? = some (wl, vl) →
        ownedExpectedWriteb GD (a + (j : Int)) r wl vl ∧
        ∃ t, greadsByte GD.gdG r (a + (j : Int)) t vl⌝ := by
  iintro Hcov Htoks
  ihave Hcov := AxProtBytes.covIntuit γ GD a r $$ Hcov
  icases Hcov with #Hcov
  unfold tokn
  ihave Hres : [∗list] j ↦ H ∈ Hs,
      (⌜∀ wl vl, H.getLast? = some (wl, vl) →
        ownedExpectedWriteb GD (a + (j : Int)) r wl vl ∧
        ∃ t, greadsByte GD.gdG r (a + (j : Int)) t vl⌝ : IProp GF) $$ [Htoks]
  · iapply BigSepL.bigSepL_impl (Ψ := fun (j : Nat) (H : List Hent) => (iprop(⌜∀ wl vl, H.getLast? = some (wl, vl) →
        ownedExpectedWriteb GD (a + (j : Int)) r wl vl ∧
        ∃ t, greadsByte GD.gdG r (a + (j : Int)) t vl⌝) : IProp GF)) $$ Htoks
    imodintro
    iintro %j %H %Hj Htie
    by_cases hne : ∃ wl vl, H.getLast? = some (wl, vl)
    · obtain ⟨wl, vl, hl⟩ := hne
      ihave Hc := Hcov $$ %j
      ihave %hexp := ownedReadExpectedb γ GD Hcons r (a + (j : Int)) H S wl vl (Hwr j H Hj)
        (Hch j H Hj) (Hown j H Hj) hl (Hrd j H Hj) (Hcase j H wl vl Hj hl) $$ Htie Hc
      ipureintro
      intro wl' vl' hl'
      rw [hl, Option.some.injEq, Prod.mk.injEq] at hl'
      obtain ⟨rfl, rfl⟩ := hl'
      exact hexp
    · iclear Htie
      ipureintro
      intro wl vl hl
      exact absurd ⟨wl, vl, hl⟩ hne
  ihave %HPall := BigSepL.bigSepL_pure_intro (φ := fun (j : Nat) (H : List Hent) => ∀ wl vl,
      H.getLast? = some (wl, vl) →
        ownedExpectedWriteb GD (a + (j : Int)) r wl vl ∧
        ∃ t, greadsByte GD.gdG r (a + (j : Int)) t vl) $$ Hres
  ipureintro
  intro j H Hj wl vl Hl0
  exact HPall j H Hj wl vl Hl0

end ghost

/-! # 4. THE FLOW EQUATION (n-byte `flowEqDyn`) -/

section flowRead

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [axG : AxirisG GF]
  [AxlogG GF Hent]

theorem flowEqOwnedReadnFwd (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (r : Geid) (a : Int) (Hs : List (List Hent)) (S : GMapF Geid Qp)
    (sOb0 : GSet Geid) (flowIn : Mea GF)
    (Hrgmo : r ∈ GD.gdG.gxGmo) (Hnw : gisW GD.gdG r = false)
    (Hwr : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ p, p ∈ H → gwritesByte GD.gdG p.1 (a + (j : Int)) p.2)
    (Hch : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H → chainWith (gmoLt GD.gdG) (H.map Prod.fst))
    (Hown : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ w v, gwritesByte GD.gdG w (a + (j : Int)) v → WeakRvwmoGraph.gpo GD.gdG w r →
        w ∈ H.map Prod.fst)
    (Hrd : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H → ∃ t v, greadsByte GD.gdG r (a + (j : Int)) t v)
    (Hcase : ∀ (j : Nat) (H : List Hent) wl vl, Hs[j]? = some H → H.getLast? = some (wl, vl) →
      (∃ e, e ∈ (FiniteMap.dom_set S : GSet Geid) ∧ gmoLt GD.gdG e r)
      ∨
      (wl ∈ (FiniteMap.dom_set S : GSet Geid) ∧
       (∀ e, e ∈ (FiniteMap.dom_set S : GSet Geid) → ¬ gmoLt GD.gdG e r) ∧
       WeakRvwmoGraph.gpo GD.gdG wl r ∧
       (∀ w' v', gwritesByte GD.gdG w' (a + (j : Int)) v' →
         WeakRvwmoGraph.gpo GD.gdG wl w' → WeakRvwmoGraph.gpo GD.gdG w' r → False)))
    (Hpref : (LawfulSet.ofList (gmoPrefix GD.gdG r) : GSet Geid) ⊆ sOb0) :
    iprop(([∗map] Rin ∈ flowIn, Rin) -∗ tokn γ GD a Hs S) ⊢
      flowEqDyn GD r sOb0 flowIn
        iprop(⌜∀ (j : Nat) (H : List Hent), Hs[j]? = some H → ∀ wl vl, H.getLast? = some (wl, vl) →
          ownedExpectedWriteb GD (a + (j : Int)) r wl vl ∧
          ∃ t, greadsByte GD.gdG r (a + (j : Int)) t vl⌝) := by
  unfold flowEqDyn
  iintro Hflowin %σ %sOb %Hsub %Hnin Hob Hflow
  ihave Hob := (Hob_eq GD σ sOb).1 $$ Hob
  icases Hob with #Hob
  ihave Htoks := Hflowin $$ Hflow
  ihave Hcovall : ∀ (j : Nat) (w : Geid) (v : BitVec 8),
      ⌜gwritesByte GD.gdG w (a + (j : Int)) v⌝ -∗ ⌜gmoLt GD.gdG w r⌝ -∗
      ∃ H' : List Hent, ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap (GF := GF) γ (a + (j : Int)) H' $$ []
  · iintro %j %w %v %hwb %hmo
    ihave Hspec := protInvPrefixCovMem γ GD sOb r (a + (j : Int)) Hcons.1 Hrgmo
      (subseteqTrans Hpref Hsub) $$ Hob
    ihave Hs2 := Hspec $$ %w %v %hwb %hmo
    iexact Hs2
  ihave %HPall := readnPureFacts γ GD Hcons a Hs S r Hwr Hch Hown Hrd Hcase $$ Hcovall Htoks
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ
  isplitl []
  · iapply (Hob_eq GD σ (({r} : GSet Geid) ∪ sOb)).2
    iapply protInvReadStep γ GD sOb r Hnin Hnw
    iexact Hob
  · ipureintro
    exact HPall

end flowRead

/-! # 5. THE WP RULE (label-witnessed); 5b the reconciliation; 5c the corrected WP rule -/

/-- 5b: the label's value list and the ownership-derived list agree. -/
theorem readnValueAgreePure (GD : Gdexec) (rdatn : Geid → Int × List (Nat × BitVec 8))
    (HrdatnSpec : ∀ r, gisW GD.gdG r = false →
      graphValue GD r = some ((rdatn r).2.map Prod.snd) ∧
      ∀ (j : Nat) t v, (rdatn r).2[j]? = some (t, v) →
        greadsByte GD.gdG r ((rdatn r).1 + (j : Int)) t v)
    (r : Geid) (Hs : List (List Hent)) (Vs : List (BitVec 8))
    (Hvals : List.Forall₂ (fun H v => ∃ wl, H.getLast? = some (wl, v)) Hs Vs)
    (Hlen : (rdatn r).2.length = Hs.length)
    (Hnw : gisW GD.gdG r = false)
    (HPall : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H → ∀ wl vl, H.getLast? = some (wl, vl) →
      ownedExpectedWriteb GD ((rdatn r).1 + (j : Int)) r wl vl ∧
      ∃ t, greadsByte GD.gdG r ((rdatn r).1 + (j : Int)) t vl) :
    graphValue GD r = some Vs := by
  obtain ⟨Hgv, Hconn⟩ := HrdatnSpec r Hnw
  have HlenV : Hs.length = Vs.length := Hvals.length_eq
  have Heq : (rdatn r).2.map Prod.snd = Vs := by
    apply List.ext_getElem?
    intro j
    by_cases Hlt : j < Hs.length
    · have Hlt' : j < (rdatn r).2.length := by omega
      have HjH : Hs[j]? = some Hs[j] := List.getElem?_eq_getElem Hlt
      obtain ⟨v, HjV, wl, Hlast⟩ := Forall2_lookup_l Hvals HjH
      have Hjrd : (rdatn r).2[j]? = some (rdatn r).2[j] := List.getElem?_eq_getElem Hlt'
      have Hgb2 := Hconn j _ _ Hjrd
      obtain ⟨_, t, Hgb1⟩ := HPall j _ HjH wl v Hlast
      have Heqv := (greadsByteDet GD.gdG r _ _ _ _ _ Hgb1 Hgb2).2
      rw [List.getElem?_map, Hjrd, HjV, Option.map_some, Heqv]
      rfl
    · have Hge1 : ((rdatn r).2.map Prod.snd).length ≤ j := by
        rw [List.length_map]; omega
      have Hge2 : Vs.length ≤ j := by omega
      rw [List.getElem?_eq_none Hge1, List.getElem?_eq_none Hge2]
  rw [Hgv, Heq]

section wpRead

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [axG : AxirisG GF]
  [AxlogG GF Hent]

theorem wpReadOwnedToknFwd [Axpol] (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (rdatn : Geid → Int × List (Nat × BitVec 8))
    (HrdatnSpec : ∀ r, gisW GD.gdG r = false →
      graphValue GD r = some ((rdatn r).2.map Prod.snd) ∧
      ∀ (j : Nat) t v, (rdatn r).2[j]? = some (t, v) →
        greadsByte GD.gdG r ((rdatn r).1 + (j : Int)) t v)
    (i : Agent) (k k'0 : Nat) (ls' : AxirisG.logTsT GF)
    (Hs : List (List Hent)) (S : GMapF Geid Qp) (Ψ : List (BitVec 8) → IProp GF)
    (Hrgmo : (i, k) ∈ GD.gdG.gxGmo) (Hnw : gisW GD.gdG (i, k) = false)
    (Hlen : (rdatn (i, k)).2.length = Hs.length)
    (Hwr : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ p, p ∈ H → gwritesByte GD.gdG p.1 ((rdatn (i, k)).1 + (j : Int)) p.2)
    (Hch : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H → chainWith (gmoLt GD.gdG) (H.map Prod.fst))
    (Hown : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ w v, gwritesByte GD.gdG w ((rdatn (i, k)).1 + (j : Int)) v →
        WeakRvwmoGraph.gpo GD.gdG w (i, k) → w ∈ H.map Prod.fst)
    (Hrd : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∃ t v, greadsByte GD.gdG (i, k) ((rdatn (i, k)).1 + (j : Int)) t v)
    (Hcase : ∀ (j : Nat) (H : List Hent) wl vl, Hs[j]? = some H → H.getLast? = some (wl, vl) →
      (∃ e, e ∈ (FiniteMap.dom_set S : GSet Geid) ∧ gmoLt GD.gdG e (i, k))
      ∨
      (wl ∈ (FiniteMap.dom_set S : GSet Geid) ∧
       (∀ e, e ∈ (FiniteMap.dom_set S : GSet Geid) → ¬ gmoLt GD.gdG e (i, k)) ∧
       WeakRvwmoGraph.gpo GD.gdG wl (i, k) ∧
       (∀ w' v', gwritesByte GD.gdG w' ((rdatn (i, k)).1 + (j : Int)) v' →
         WeakRvwmoGraph.gpo GD.gdG wl w' → WeakRvwmoGraph.gpo GD.gdG w' (i, k) → False)))
    (Hpref : (LawfulSet.ofList (gmoPrefix GD.gdG (i, k)) : GSet Geid) ⊆ Axpol.sPol GD (i, k))
    (Hnalloc : ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
       AxirisG.annotInterp (insert na (i, k)
         iprop(⌜∀ (j : Nat) (H : List Hent), Hs[j]? = some H → ∀ wl vl, H.getLast? = some (wl, vl) →
           ownedExpectedWriteb GD ((rdatn (i, k)).1 + (j : Int)) (i, k) wl vl ∧
           ∃ t, greadsByte GD.gdG (i, k) ((rdatn (i, k)).1 + (j : Int)) t vl⌝))) :
    ⊢ tokn γ GD (rdatn (i, k)).1 Hs S -∗
      AxirisG.localInterp GD i k'0 ls' -∗
      (∀ v : List (BitVec 8), ⌜v.length = Hs.length⌝ -∗ Ψ v) -∗
      wpEvStep GD i k (fun v : List (BitVec 8) => v.length = Hs.length)
        (fun v => graphValue GD (i, k) = some v) (fun _ => k'0) Ψ := by
  have Hlen' : ((rdatn (i, k)).2.map Prod.snd).length = Hs.length := by
    rw [List.length_map]; exact Hlen
  have hpost : iprop(⌜∀ (j : Nat) (H : List Hent), Hs[j]? = some H → ∀ wl vl, H.getLast? = some (wl, vl) →
        ownedExpectedWriteb GD ((rdatn (i, k)).1 + (j : Int)) (i, k) wl vl ∧
        ∃ t, greadsByte GD.gdG (i, k) ((rdatn (i, k)).1 + (j : Int)) t vl⌝ : IProp GF) ⊢
      iprop(⌜∀ (j : Nat) (H : List Hent), Hs[j]? = some H → ∀ wl vl, H.getLast? = some (wl, vl) →
        ownedExpectedWriteb GD ((rdatn (i, k)).1 + (j : Int)) (i, k) wl vl ∧
        ∃ t, greadsByte GD.gdG (i, k) ((rdatn (i, k)).1 + (j : Int)) t vl⌝ ∗
        ⌜graphValue GD (i, k) = some ((rdatn (i, k)).2.map Prod.snd)⌝) := by
    iintro %hp
    isplitl []
    · ipureintro
      exact hp
    · ipureintro
      exact (HrdatnSpec (i, k) Hnw).1
  have hw : tokn (GF := GF) γ GD (rdatn (i, k)).1 Hs S ⊢
      iprop(([∗map] Rin ∈ (∅ : Mea GF), Rin) -∗ tokn γ GD (rdatn (i, k)).1 Hs S) := by
    iintro Ht _
    iexact Ht
  have Hfeq := (hw.trans (flowEqOwnedReadnFwd γ Hob_eq GD Hcons (i, k) (rdatn (i, k)).1 Hs S
    (Axpol.sPol GD (i, k)) ∅ Hrgmo Hnw Hwr Hch Hown Hrd Hcase Hpref)).trans
    (AxProtCov3.flowEqDynPost GD (i, k) _ _ _ _ hpost)
  have Hn' : ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
      AxirisG.annotInterp (PartialMap.union (PartialMap.union
        {[(i, k) := iprop(⌜∀ (j : Nat) (H : List Hent), Hs[j]? = some H → ∀ wl vl, H.getLast? = some (wl, vl) →
          ownedExpectedWriteb GD ((rdatn (i, k)).1 + (j : Int)) (i, k) wl vl ∧
          ∃ t, greadsByte GD.gdG (i, k) ((rdatn (i, k)).1 + (j : Int)) t vl⌝)]}
        (∅ : Mea GF)) na) := by
    simp only [AxProtGate.annotInsertEq]
    exact Hnalloc
  iintro Htie Hloc Hcont
  ihave Hfeq := Hfeq $$ Htie
  unfold wpEvStep
  iintro %na Hpg
  ihave Hn := Hn'
  imod Hn $$ %na Hpg with Hna'
  imodintro
  inext
  imodintro
  iexists ((rdatn (i, k)).2.map Prod.snd),
    iprop(⌜∀ (j : Nat) (H : List Hent), Hs[j]? = some H → ∀ wl vl, H.getLast? = some (wl, vl) →
      ownedExpectedWriteb GD ((rdatn (i, k)).1 + (j : Int)) (i, k) wl vl ∧
      ∃ t, greadsByte GD.gdG (i, k) ((rdatn (i, k)).1 + (j : Int)) t vl⌝),
    (∅ : Mea GF), (∅ : Mea GF), ls'
  isplitr
  · ipureintro
    exact Hlen'
  isplitr
  · iapply AxProtGate.naSplittingWfEmpty
  iframe Hfeq Hna' Hloc
  iapply Hcont
  ipureintro
  exact Hlen'

end wpRead

section agree

variable {GF : BundledGFunctors} [AxlogG GF Hent]

theorem readnValueAgree (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (rdatn : Geid → Int × List (Nat × BitVec 8))
    (HrdatnSpec : ∀ r, gisW GD.gdG r = false →
      graphValue GD r = some ((rdatn r).2.map Prod.snd) ∧
      ∀ (j : Nat) t v, (rdatn r).2[j]? = some (t, v) →
        greadsByte GD.gdG r ((rdatn r).1 + (j : Int)) t v)
    (r : Geid) (Hs : List (List Hent)) (Vs : List (BitVec 8)) (S : GMapF Geid Qp)
    (Hvals : List.Forall₂ (fun H v => ∃ wl, H.getLast? = some (wl, v)) Hs Vs)
    (Hlen : (rdatn r).2.length = Hs.length) (Hnw : gisW GD.gdG r = false)
    (Hwr : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ p, p ∈ H → gwritesByte GD.gdG p.1 ((rdatn r).1 + (j : Int)) p.2)
    (Hch : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H → chainWith (gmoLt GD.gdG) (H.map Prod.fst))
    (Hown : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ w v, gwritesByte GD.gdG w ((rdatn r).1 + (j : Int)) v →
        WeakRvwmoGraph.gpo GD.gdG w r → w ∈ H.map Prod.fst)
    (Hrd : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∃ t v, greadsByte GD.gdG r ((rdatn r).1 + (j : Int)) t v)
    (Hcase : ∀ (j : Nat) (H : List Hent) wl vl, Hs[j]? = some H → H.getLast? = some (wl, vl) →
      (∃ e, e ∈ (FiniteMap.dom_set S : GSet Geid) ∧ gmoLt GD.gdG e r)
      ∨
      (wl ∈ (FiniteMap.dom_set S : GSet Geid) ∧
       (∀ e, e ∈ (FiniteMap.dom_set S : GSet Geid) → ¬ gmoLt GD.gdG e r) ∧
       WeakRvwmoGraph.gpo GD.gdG wl r ∧
       (∀ w' v', gwritesByte GD.gdG w' ((rdatn r).1 + (j : Int)) v' →
         WeakRvwmoGraph.gpo GD.gdG wl w' → WeakRvwmoGraph.gpo GD.gdG w' r → False))) :
    ⊢ (∀ (j : Nat) (w : Geid) (v : BitVec 8),
        ⌜gwritesByte GD.gdG w ((rdatn r).1 + (j : Int)) v⌝ -∗ ⌜gmoLt GD.gdG w r⌝ -∗
        ∃ H' : List Hent, ⌜w ∈ H'.map Prod.fst⌝ ∗
          histSnap (GF := GF) γ ((rdatn r).1 + (j : Int)) H') -∗
      tokn γ GD (rdatn r).1 Hs S -∗
      ⌜graphValue GD r = some Vs⌝ := by
  iintro Hcov Htoks
  ihave %HPall := readnPureFacts γ GD Hcons (rdatn r).1 Hs S r Hwr Hch Hown Hrd Hcase $$
    Hcov Htoks
  ipureintro
  exact readnValueAgreePure GD rdatn HrdatnSpec r Hs Vs Hvals Hlen Hnw HPall

end agree

section wpRead2

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [axG : AxirisG GF]
  [AxlogG GF Hent]

theorem wpReadOwnedTokn [Axpol] (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (rdatn : Geid → Int × List (Nat × BitVec 8))
    (HrdatnSpec : ∀ r, gisW GD.gdG r = false →
      graphValue GD r = some ((rdatn r).2.map Prod.snd) ∧
      ∀ (j : Nat) t v, (rdatn r).2[j]? = some (t, v) →
        greadsByte GD.gdG r ((rdatn r).1 + (j : Int)) t v)
    (i : Agent) (k k'0 : Nat) (ls' : AxirisG.logTsT GF)
    (Hs : List (List Hent)) (Vs : List (BitVec 8)) (S : GMapF Geid Qp)
    (Ψ : List (BitVec 8) → IProp GF)
    (Hrgmo : (i, k) ∈ GD.gdG.gxGmo) (Hnw : gisW GD.gdG (i, k) = false)
    (Hlen : (rdatn (i, k)).2.length = Hs.length)
    (Hvals : List.Forall₂ (fun H v => ∃ wl, H.getLast? = some (wl, v)) Hs Vs)
    (Hwr : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ p, p ∈ H → gwritesByte GD.gdG p.1 ((rdatn (i, k)).1 + (j : Int)) p.2)
    (Hch : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H → chainWith (gmoLt GD.gdG) (H.map Prod.fst))
    (Hown : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ w v, gwritesByte GD.gdG w ((rdatn (i, k)).1 + (j : Int)) v →
        WeakRvwmoGraph.gpo GD.gdG w (i, k) → w ∈ H.map Prod.fst)
    (Hrd : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∃ t v, greadsByte GD.gdG (i, k) ((rdatn (i, k)).1 + (j : Int)) t v)
    (Hcase : ∀ (j : Nat) (H : List Hent) wl vl, Hs[j]? = some H → H.getLast? = some (wl, vl) →
      (∃ e, e ∈ (FiniteMap.dom_set S : GSet Geid) ∧ gmoLt GD.gdG e (i, k))
      ∨
      (wl ∈ (FiniteMap.dom_set S : GSet Geid) ∧
       (∀ e, e ∈ (FiniteMap.dom_set S : GSet Geid) → ¬ gmoLt GD.gdG e (i, k)) ∧
       WeakRvwmoGraph.gpo GD.gdG wl (i, k) ∧
       (∀ w' v', gwritesByte GD.gdG w' ((rdatn (i, k)).1 + (j : Int)) v' →
         WeakRvwmoGraph.gpo GD.gdG wl w' → WeakRvwmoGraph.gpo GD.gdG w' (i, k) → False)))
    (Hpref : (LawfulSet.ofList (gmoPrefix GD.gdG (i, k)) : GSet Geid) ⊆ Axpol.sPol GD (i, k))
    (Hnalloc : ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
       AxirisG.annotInterp (insert na (i, k)
         iprop(⌜∀ (j : Nat) (H : List Hent), Hs[j]? = some H → ∀ wl vl, H.getLast? = some (wl, vl) →
           ownedExpectedWriteb GD ((rdatn (i, k)).1 + (j : Int)) (i, k) wl vl ∧
           ∃ t, greadsByte GD.gdG (i, k) ((rdatn (i, k)).1 + (j : Int)) t vl⌝))) :
    ⊢ tokn γ GD (rdatn (i, k)).1 Hs S -∗
      AxirisG.localInterp GD i k'0 ls' -∗
      (∀ v : List (BitVec 8), ⌜v.length = Hs.length⌝ -∗ Ψ v) -∗
      wpEvStep GD i k (fun v : List (BitVec 8) => v.length = Hs.length)
        (fun v => graphValue GD (i, k) = some v) (fun _ => k'0) Ψ := by
  have Hlen' : Vs.length = Hs.length := Hvals.length_eq.symm
  have hpost : iprop(⌜∀ (j : Nat) (H : List Hent), Hs[j]? = some H → ∀ wl vl, H.getLast? = some (wl, vl) →
        ownedExpectedWriteb GD ((rdatn (i, k)).1 + (j : Int)) (i, k) wl vl ∧
        ∃ t, greadsByte GD.gdG (i, k) ((rdatn (i, k)).1 + (j : Int)) t vl⌝ : IProp GF) ⊢
      iprop(⌜∀ (j : Nat) (H : List Hent), Hs[j]? = some H → ∀ wl vl, H.getLast? = some (wl, vl) →
        ownedExpectedWriteb GD ((rdatn (i, k)).1 + (j : Int)) (i, k) wl vl ∧
        ∃ t, greadsByte GD.gdG (i, k) ((rdatn (i, k)).1 + (j : Int)) t vl⌝ ∗
        ⌜graphValue GD (i, k) = some Vs⌝) := by
    iintro %hp
    isplitl []
    · ipureintro
      exact hp
    · ipureintro
      exact readnValueAgreePure GD rdatn HrdatnSpec (i, k) Hs Vs Hvals Hlen Hnw hp
  have hw : tokn (GF := GF) γ GD (rdatn (i, k)).1 Hs S ⊢
      iprop(([∗map] Rin ∈ (∅ : Mea GF), Rin) -∗ tokn γ GD (rdatn (i, k)).1 Hs S) := by
    iintro Ht _
    iexact Ht
  have Hfeq := (hw.trans (flowEqOwnedReadnFwd γ Hob_eq GD Hcons (i, k) (rdatn (i, k)).1 Hs S
    (Axpol.sPol GD (i, k)) ∅ Hrgmo Hnw Hwr Hch Hown Hrd Hcase Hpref)).trans
    (AxProtCov3.flowEqDynPost GD (i, k) _ _ _ _ hpost)
  have Hn' : ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
      AxirisG.annotInterp (PartialMap.union (PartialMap.union
        {[(i, k) := iprop(⌜∀ (j : Nat) (H : List Hent), Hs[j]? = some H → ∀ wl vl, H.getLast? = some (wl, vl) →
          ownedExpectedWriteb GD ((rdatn (i, k)).1 + (j : Int)) (i, k) wl vl ∧
          ∃ t, greadsByte GD.gdG (i, k) ((rdatn (i, k)).1 + (j : Int)) t vl⌝)]}
        (∅ : Mea GF)) na) := by
    simp only [AxProtGate.annotInsertEq]
    exact Hnalloc
  iintro Htie Hloc Hcont
  ihave Hfeq := Hfeq $$ Htie
  unfold wpEvStep
  iintro %na Hpg
  ihave Hn := Hn'
  imod Hn $$ %na Hpg with Hna'
  imodintro
  inext
  imodintro
  iexists Vs,
    iprop(⌜∀ (j : Nat) (H : List Hent), Hs[j]? = some H → ∀ wl vl, H.getLast? = some (wl, vl) →
      ownedExpectedWriteb GD ((rdatn (i, k)).1 + (j : Int)) (i, k) wl vl ∧
      ∃ t, greadsByte GD.gdG (i, k) ((rdatn (i, k)).1 + (j : Int)) t vl⌝),
    (∅ : Mea GF), (∅ : Mea GF), ls'
  isplitr
  · ipureintro
    exact Hlen'
  isplitr
  · iapply AxProtGate.naSplittingWfEmpty
  iframe Hfeq Hna' Hloc
  iapply Hcont
  ipureintro
  exact Hlen'

end wpRead2

/-! # 6. THE n-BYTE WRITE SIDE -/

/-- Byte `j`'s history with `w`'s own entry `(w, Vs !!! j)` appended. -/
def writenHist (w : Geid) (Vs : List (BitVec 8)) (Hs : List (List Hent)) : List (List Hent) :=
  Hs.mapIdx fun j H => H ++ [(w, Vs.getD j 0)]

theorem writenHistLookup (w : Geid) (Vs : List (BitVec 8)) (Hs : List (List Hent)) (j : Nat)
    (Hb0 : List Hent) :
    Hs[j]? = some Hb0 → (writenHist w Vs Hs)[j]? = some (Hb0 ++ [(w, Vs.getD j 0)]) := by
  intro HHs0
  simp only [writenHist, List.getElem?_mapIdx, HHs0, Option.map_some]

theorem writenHistLength (w : Geid) (Vs : List (BitVec 8)) (Hs : List (List Hent)) :
    (writenHist w Vs Hs).length = Hs.length := by
  simp only [writenHist, List.length_mapIdx]

/-- Lean-only: inversion of `writenHistLookup`. -/
theorem AxProtBytes.writenHistLookupInv (w : Geid) (Vs : List (BitVec 8))
    (Hs : List (List Hent)) (j : Nat) (H' : List Hent) :
    (writenHist w Vs Hs)[j]? = some H' →
      ∃ H0, Hs[j]? = some H0 ∧ H' = H0 ++ [(w, Vs.getD j 0)] := by
  intro h
  simp only [writenHist, List.getElem?_mapIdx] at h
  cases h0 : Hs[j]? with
  | none => rw [h0] at h; cases h
  | some H0 =>
    rw [h0, Option.map_some, Option.some.injEq] at h
    exact ⟨H0, rfl, h.symm⟩

section write

variable {GF : BundledGFunctors} [AxlogG GF Hent]

theorem tokTieAfterWriteSnap (γ : GName) (GD : Gdexec) (a' : Int) (Hl : List Hent) (w : Geid)
    (v : BitVec 8) :
    histAuth (GF := GF) γ a' 1 Hl ⊢
      |==> (histSnap γ a' (Hl ++ [(w, v)]) ∗ tokTie GD γ a' (Hl ++ [(w, v)]) {[w := (1 : Qp)]}) := by
  iintro Ha
  imod tokTieAfterWrite GD γ a' Hl w v $$ Ha with Htie
  unfold tokTie
  icases Htie with ⟨Htok, %htie⟩
  icases tokSnap γ a' (Hl ++ [(w, v)]) {[w := (1 : Qp)]} w 1 lookupSingleton $$ Htok
    with ⟨Htok, #Hs⟩
  imodintro
  isplitl []
  · iexact Hs
  · isplitl [Htok]
    · iexact Htok
    · ipureintro
      exact htie

theorem bigSepLReindex {A B : Type _} (Φ : Nat → IProp GF) (l : List A) (l' : List B) :
    l.length = l'.length →
    iprop([∗list] j ↦ _x ∈ l, Φ j) ⊢ iprop([∗list] j ↦ _x ∈ l', Φ j) := by
  induction l generalizing l' Φ with
  | nil =>
    cases l' with
    | nil => intro _; exact .rfl
    | cons y l' => intro h; simp at h
  | cons x l ih =>
    cases l' with
    | nil => intro h; simp at h
    | cons y l' =>
      intro h
      have h' : l.length = l'.length := by simpa using h
      exact (BigSepL.bigSepL_cons (Φ := fun j (_ : A) => Φ j)).1.trans
        ((BI.sep_mono .rfl (ih (fun j => Φ (j + 1)) l' h')).trans
          (BigSepL.bigSepL_cons (Φ := fun j (_ : B) => Φ j)).2)

end write

section flowWrite

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [axG : AxirisG GF]
  [AxlogG GF Hent]

theorem flowEqOwnedWritenChainSnap (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (w : Geid) (a : Int) (Hs : List (List Hent)) (Vs : List (BitVec 8))
    (sOb0 : GSet Geid) (flowIn : Mea GF) (data : List (BitVec 8))
    (Hlen : Hs.length = Vs.length)
    (Hisw : gisW GD.gdG w = true)
    (Hcompl : ∀ a' v', gwritesByte GD.gdG w a' v' →
      ∃ j : Nat, Vs[j]? = some v' ∧ a' = a + (j : Int))
    (Hgd : graphData GD w = some data) :
    iprop(([∗map] Rin ∈ flowIn, Rin) -∗
        [∗list] j ↦ H ∈ Hs, histAuth γ (a + (j : Int)) 1 H) ⊢
      flowEqDyn GD w sOb0 flowIn
        iprop((tokn γ GD a (writenHist w Vs Hs) {[w := (1 : Qp)]} ∗
          ([∗list] j ↦ H' ∈ writenHist w Vs Hs, histSnap γ (a + (j : Int)) H')) ∗
          ⌜graphData GD w = some data⌝) := by
  have hmono : iprop([∗list] j ↦ H ∈ Hs, histAuth (GF := GF) γ (a + (j : Int)) 1 H) ⊢
      iprop([∗list] j ↦ _H ∈ Hs, histAuth (GF := GF) γ (a + (j : Int)) 1 (Hs.getD j [])) :=
    BigSepL.bigSepL_mono fun {j _} hk => by
      rw [List.getD_eq_getElem?_getD, hk, Option.getD_some]
  have hre := bigSepLReindex (fun j => histAuth (GF := GF) γ (a + (j : Int)) 1 (Hs.getD j []))
    Hs (writenHist w Vs Hs) (writenHistLength w Vs Hs).symm
  have hstep : iprop([∗list] j ↦ _H ∈ writenHist w Vs Hs,
        histAuth (GF := GF) γ (a + (j : Int)) 1 (Hs.getD j [])) ⊢
      iprop(|==> [∗list] j ↦ H' ∈ writenHist w Vs Hs,
        histSnap (GF := GF) γ (a + (j : Int)) H' ∗
          tokTie GD γ (a + (j : Int)) H' {[w := (1 : Qp)]}) := by
    refine (BigSepL.bigSepL_mono fun {j H'} hk => ?_).trans (BigSepL.bigSepL_bupd _ _)
    obtain ⟨H0, h0, rfl⟩ := AxProtBytes.writenHistLookupInv w Vs Hs j H' hk
    rw [List.getD_eq_getElem?_getD, h0, Option.getD_some]
    exact tokTieAfterWriteSnap γ GD (a + (j : Int)) H0 w (Vs.getD j 0)
  unfold flowEqDyn
  iintro Hflowin %σ %sOb %Hsub %Hnin Hob Hflow
  ihave Hob := (Hob_eq GD σ sOb).1 $$ Hob
  icases Hob with #Hob
  ihave Hauths := Hflowin $$ Hflow
  ihave Hst := (hmono.trans (hre.trans hstep)) $$ Hauths
  imod Hst
  icases BigSepL.bigSepL_sep_eqv.1 $$ Hst with ⟨Hsnaps, Htoks⟩
  icases Hsnaps with #Hsnaps
  ihave Hown : ΦpOwn (GF := GF) γ GD w $$ []
  · rw [AxProt.ΦpOwnW γ GD w Hisw]
    unfold ΦOwn
    iintro %a' %v' %Hwb'
    obtain ⟨j, HVj, rfl⟩ := Hcompl a' v' Hwb'
    have Hjlt : j < Hs.length := by
      rw [Hlen]; exact (List.getElem?_eq_some_iff.1 HVj).1
    have HHs0 : Hs[j]? = some Hs[j] := List.getElem?_eq_getElem Hjlt
    have Heqv : Vs.getD j 0 = v' := by
      rw [List.getD_eq_getElem?_getD, HVj, Option.getD_some]
    have Hj0 := writenHistLookup w Vs Hs j _ HHs0
    rw [Heqv] at Hj0
    ihave Hsn := BigSepL.bigSepL_lookup (Φ := fun (j : Nat) (H' : List Hent) => histSnap (GF := GF) γ (a + (j : Int)) H')
      Hj0 $$ Hsnaps
    iexists (Hs[j] ++ [(w, v')])
    isplitl []
    · iexact Hsn
    · ipureintro
      exact List.getLast?_concat
  icases Hown with #Hown
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ
  isplitl []
  · iapply (Hob_eq GD σ (({w} : GSet Geid) ∪ sOb)).2
    iapply (protInvInsert γ GD w sOb Hnin).2
    isplitl []
    · iexact Hown
    · iexact Hob
  · isplitl [Htoks]
    · isplitl [Htoks]
      · unfold tokn
        iexact Htoks
      · iexact Hsnaps
    · ipureintro
      exact Hgd

/-! # 7. THE n-BYTE WRITE WP RULE -/

theorem wpWriteOwnedTokn [Axpol] (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (i : Agent) (k k'0 : Nat) (ls' : AxirisG.logTsT GF) (a : Int)
    (Hs : List (List Hent)) (Vs : List (BitVec 8)) (data : List (BitVec 8))
    (Ψ : Unit → IProp GF)
    (Hlen : Hs.length = Vs.length)
    (Hisw : gisW GD.gdG (i, k) = true)
    (Hcompl : ∀ a' v', gwritesByte GD.gdG (i, k) a' v' →
      ∃ j : Nat, Vs[j]? = some v' ∧ a' = a + (j : Int))
    (Hgd : graphData GD (i, k) = some data)
    (Hnalloc : ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
       AxirisG.annotInterp (insert na (i, k)
         iprop(tokn γ GD a (writenHist (i, k) Vs Hs) {[(i, k) := (1 : Qp)]} ∗
           ([∗list] j ↦ H' ∈ writenHist (i, k) Vs Hs, histSnap γ (a + (j : Int)) H')))) :
    ⊢ ([∗list] j ↦ H ∈ Hs, histAuth γ (a + (j : Int)) 1 H) -∗
      AxirisG.localInterp GD i k'0 ls' -∗
      Ψ () -∗
      wpEvStep GD i k (fun _ : Unit => True) (fun _ : Unit => graphData GD (i, k) = some data)
        (fun _ => k'0) Ψ := by
  have hw : iprop([∗list] j ↦ H ∈ Hs, histAuth (GF := GF) γ (a + (j : Int)) 1 H) ⊢
      iprop(([∗map] Rin ∈ (∅ : Mea GF), Rin) -∗
        [∗list] j ↦ H ∈ Hs, histAuth (GF := GF) γ (a + (j : Int)) 1 H) := by
    iintro Ht _
    iexact Ht
  have Hfeq := hw.trans (flowEqOwnedWritenChainSnap γ Hob_eq GD (i, k) a Hs Vs
    (Axpol.sPol GD (i, k)) ∅ data Hlen Hisw Hcompl Hgd)
  have Hn' : ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗ AxirisG.annotInterp na ==∗
      AxirisG.annotInterp (PartialMap.union (PartialMap.union
        {[(i, k) := iprop(tokn γ GD a (writenHist (i, k) Vs Hs) {[(i, k) := (1 : Qp)]} ∗
          ([∗list] j ↦ H' ∈ writenHist (i, k) Vs Hs, histSnap γ (a + (j : Int)) H'))]}
        (∅ : Mea GF)) na) := by
    simp only [AxProtGate.annotInsertEq]
    exact Hnalloc
  iintro Hauths Hloc HΨ
  ihave Hfeq := Hfeq $$ Hauths
  unfold wpEvStep
  iintro %na Hpg
  ihave Hn := Hn'
  imod Hn $$ %na Hpg with Hna'
  imodintro
  inext
  imodintro
  iexists (), iprop(tokn γ GD a (writenHist (i, k) Vs Hs) {[(i, k) := (1 : Qp)]} ∗
      ([∗list] j ↦ H' ∈ writenHist (i, k) Vs Hs, histSnap γ (a + (j : Int)) H')),
    (∅ : Mea GF), (∅ : Mea GF), ls'
  isplitr
  · ipureintro
    trivial
  isplitr
  · iapply AxProtGate.naSplittingWfEmpty
  iframe Hfeq Hna' Hloc HΨ

end flowWrite

/-! # 6 (Rocq's second §6). AT THE CONCRETE `skelAxirisG` INSTANCE -/

section skelN

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxannotGS GF] [AxgraphG GF]
  [AxlogG GF Hent] (γg : GName) (Φp : Gdexec → Geid → IProp GF)

theorem annotAllocAtProgressSkeln (GD : Gdexec) (i : Agent) (k : Nat) (P : IProp GF) :
    ⊢ ∀ na : Mea GF, naAtProgress GD i k na ∗
        AxirisG.annotInterp (self := skelAxirisG γg Φp) na ==∗
      AxirisG.annotInterp (self := skelAxirisG γg Φp) (insert na (i, k) P) :=
  annotAllocAtProgressSkel γg Φp GD i k P

theorem wpReadOwnedToknFwdSkel [Axpol] (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : @AxirisG.obSt GF (skelAxirisG γg Φp)) (s : GSet Geid),
      AxirisG.obStInterp (self := skelAxirisG γg Φp) GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (rdatn : Geid → Int × List (Nat × BitVec 8))
    (HrdatnSpec : ∀ r, gisW GD.gdG r = false →
      graphValue GD r = some ((rdatn r).2.map Prod.snd) ∧
      ∀ (j : Nat) t v, (rdatn r).2[j]? = some (t, v) →
        greadsByte GD.gdG r ((rdatn r).1 + (j : Int)) t v)
    (i : Agent) (k k'0 : Nat) (ls' : @AxirisG.logTsT GF (skelAxirisG γg Φp))
    (Hs : List (List Hent)) (S : GMapF Geid Qp) (Ψ : List (BitVec 8) → IProp GF)
    (Hrgmo : (i, k) ∈ GD.gdG.gxGmo) (Hnw : gisW GD.gdG (i, k) = false)
    (Hlen : (rdatn (i, k)).2.length = Hs.length)
    (Hwr : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ p, p ∈ H → gwritesByte GD.gdG p.1 ((rdatn (i, k)).1 + (j : Int)) p.2)
    (Hch : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H → chainWith (gmoLt GD.gdG) (H.map Prod.fst))
    (Hown : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ w v, gwritesByte GD.gdG w ((rdatn (i, k)).1 + (j : Int)) v →
        WeakRvwmoGraph.gpo GD.gdG w (i, k) → w ∈ H.map Prod.fst)
    (Hrd : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∃ t v, greadsByte GD.gdG (i, k) ((rdatn (i, k)).1 + (j : Int)) t v)
    (Hcase : ∀ (j : Nat) (H : List Hent) wl vl, Hs[j]? = some H → H.getLast? = some (wl, vl) →
      (∃ e, e ∈ (FiniteMap.dom_set S : GSet Geid) ∧ gmoLt GD.gdG e (i, k))
      ∨
      (wl ∈ (FiniteMap.dom_set S : GSet Geid) ∧
       (∀ e, e ∈ (FiniteMap.dom_set S : GSet Geid) → ¬ gmoLt GD.gdG e (i, k)) ∧
       WeakRvwmoGraph.gpo GD.gdG wl (i, k) ∧
       (∀ w' v', gwritesByte GD.gdG w' ((rdatn (i, k)).1 + (j : Int)) v' →
         WeakRvwmoGraph.gpo GD.gdG wl w' → WeakRvwmoGraph.gpo GD.gdG w' (i, k) → False)))
    (Hpref : (LawfulSet.ofList (gmoPrefix GD.gdG (i, k)) : GSet Geid) ⊆ Axpol.sPol GD (i, k)) :
    ⊢ tokn γ GD (rdatn (i, k)).1 Hs S -∗
      AxirisG.localInterp (self := skelAxirisG γg Φp) GD i k'0 ls' -∗
      (∀ v : List (BitVec 8), ⌜v.length = Hs.length⌝ -∗ Ψ v) -∗
      @wpEvStep hlc GF _ (skelAxirisG γg Φp) _ (List (BitVec 8)) GD i k
        (fun v : List (BitVec 8) => v.length = Hs.length)
        (fun v => graphValue GD (i, k) = some v) (fun _ => k'0) Ψ :=
  wpReadOwnedToknFwd (axG := skelAxirisG γg Φp) γ Hob_eq GD Hcons rdatn HrdatnSpec
    i k k'0 ls' Hs S Ψ Hrgmo Hnw Hlen Hwr Hch Hown Hrd Hcase Hpref
    (annotAllocAtProgressSkeln γg Φp GD i k _)

theorem wpReadOwnedToknSkel [Axpol] (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : @AxirisG.obSt GF (skelAxirisG γg Φp)) (s : GSet Geid),
      AxirisG.obStInterp (self := skelAxirisG γg Φp) GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (rdatn : Geid → Int × List (Nat × BitVec 8))
    (HrdatnSpec : ∀ r, gisW GD.gdG r = false →
      graphValue GD r = some ((rdatn r).2.map Prod.snd) ∧
      ∀ (j : Nat) t v, (rdatn r).2[j]? = some (t, v) →
        greadsByte GD.gdG r ((rdatn r).1 + (j : Int)) t v)
    (i : Agent) (k k'0 : Nat) (ls' : @AxirisG.logTsT GF (skelAxirisG γg Φp))
    (Hs : List (List Hent)) (Vs : List (BitVec 8)) (S : GMapF Geid Qp)
    (Ψ : List (BitVec 8) → IProp GF)
    (Hrgmo : (i, k) ∈ GD.gdG.gxGmo) (Hnw : gisW GD.gdG (i, k) = false)
    (Hlen : (rdatn (i, k)).2.length = Hs.length)
    (Hvals : List.Forall₂ (fun H v => ∃ wl, H.getLast? = some (wl, v)) Hs Vs)
    (Hwr : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ p, p ∈ H → gwritesByte GD.gdG p.1 ((rdatn (i, k)).1 + (j : Int)) p.2)
    (Hch : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H → chainWith (gmoLt GD.gdG) (H.map Prod.fst))
    (Hown : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ w v, gwritesByte GD.gdG w ((rdatn (i, k)).1 + (j : Int)) v →
        WeakRvwmoGraph.gpo GD.gdG w (i, k) → w ∈ H.map Prod.fst)
    (Hrd : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∃ t v, greadsByte GD.gdG (i, k) ((rdatn (i, k)).1 + (j : Int)) t v)
    (Hcase : ∀ (j : Nat) (H : List Hent) wl vl, Hs[j]? = some H → H.getLast? = some (wl, vl) →
      (∃ e, e ∈ (FiniteMap.dom_set S : GSet Geid) ∧ gmoLt GD.gdG e (i, k))
      ∨
      (wl ∈ (FiniteMap.dom_set S : GSet Geid) ∧
       (∀ e, e ∈ (FiniteMap.dom_set S : GSet Geid) → ¬ gmoLt GD.gdG e (i, k)) ∧
       WeakRvwmoGraph.gpo GD.gdG wl (i, k) ∧
       (∀ w' v', gwritesByte GD.gdG w' ((rdatn (i, k)).1 + (j : Int)) v' →
         WeakRvwmoGraph.gpo GD.gdG wl w' → WeakRvwmoGraph.gpo GD.gdG w' (i, k) → False)))
    (Hpref : (LawfulSet.ofList (gmoPrefix GD.gdG (i, k)) : GSet Geid) ⊆ Axpol.sPol GD (i, k)) :
    ⊢ tokn γ GD (rdatn (i, k)).1 Hs S -∗
      AxirisG.localInterp (self := skelAxirisG γg Φp) GD i k'0 ls' -∗
      (∀ v : List (BitVec 8), ⌜v.length = Hs.length⌝ -∗ Ψ v) -∗
      @wpEvStep hlc GF _ (skelAxirisG γg Φp) _ (List (BitVec 8)) GD i k
        (fun v : List (BitVec 8) => v.length = Hs.length)
        (fun v => graphValue GD (i, k) = some v) (fun _ => k'0) Ψ :=
  wpReadOwnedTokn (axG := skelAxirisG γg Φp) γ Hob_eq GD Hcons rdatn HrdatnSpec
    i k k'0 ls' Hs Vs S Ψ Hrgmo Hnw Hlen Hvals Hwr Hch Hown Hrd Hcase Hpref
    (annotAllocAtProgressSkeln γg Φp GD i k _)

theorem wpWriteOwnedToknSkel [Axpol] (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : @AxirisG.obSt GF (skelAxirisG γg Φp)) (s : GSet Geid),
      AxirisG.obStInterp (self := skelAxirisG γg Φp) GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (i : Agent) (k k'0 : Nat) (ls' : @AxirisG.logTsT GF (skelAxirisG γg Φp))
    (a : Int) (Hs : List (List Hent)) (Vs : List (BitVec 8)) (data : List (BitVec 8))
    (Ψ : Unit → IProp GF)
    (Hlen : Hs.length = Vs.length)
    (Hisw : gisW GD.gdG (i, k) = true)
    (Hcompl : ∀ a' v', gwritesByte GD.gdG (i, k) a' v' →
      ∃ j : Nat, Vs[j]? = some v' ∧ a' = a + (j : Int))
    (Hgd : graphData GD (i, k) = some data) :
    ⊢ ([∗list] j ↦ H ∈ Hs, histAuth γ (a + (j : Int)) 1 H) -∗
      AxirisG.localInterp (self := skelAxirisG γg Φp) GD i k'0 ls' -∗
      Ψ () -∗
      @wpEvStep hlc GF _ (skelAxirisG γg Φp) _ Unit GD i k (fun _ : Unit => True)
        (fun _ : Unit => graphData GD (i, k) = some data) (fun _ => k'0) Ψ :=
  wpWriteOwnedTokn (axG := skelAxirisG γg Φp) γ Hob_eq GD i k k'0 ls' a Hs Vs data Ψ
    Hlen Hisw Hcompl Hgd (annotAllocAtProgressSkeln γg Φp GD i k _)

end skelN

end Weak
