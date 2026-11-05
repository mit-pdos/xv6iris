/-
Weak/Prom: **SchedAD — the concurrent wp `wpAV` over E-c's A/D variant and its lifting lemma** (owner ruling
[OWN.P14]; G4-review3.md §5 A-2; plan rev 7 §3 "Frontier elimination, restated", "The three rules, now consistent",
"Why A/D messages are excluded"; OwnAWp.lean is the v2 original, whose ghost state is REUSED unchanged).

Ghost state: OwnAWp.lean's `AGN`, `hartA`, `pend`/`shot`, `doomInv`, `fulT` and the frontier rule `frontA`,
unchanged.  The differences, all from plan §3 rev 5:
* the state interpretation `stAV` keeps the claim `fOkV` (`stage` over NON-A/D timestamps) of every hart;
* the persistent shot table covers every fulfilled timestamp AND every A/D timestamp: A/D messages carry no
  obligation ("A/D writes carry no obligation (their validity is PO-ad, §2 (iv))"), so their one-shots are shot at
  adequacy start (OwnAAdAdeq.lean) and no client ever holds their `pend`;
* `stAV` records the two pure facts about the parameter `M` that the plan's second rule needs, `PO_adV` and
  `adExactV` ("the concurrent adequacy takes it as a pure fact about its parameter M at the start … together with
  its premises PO-img and PO-ad, exactly as A0 does").  `valid_frontV` is that rule, `stage ≥ V ⊢ validUpTo V`: a
  non-A/D `t ≤ WF` is fulfilled with its recorded `protoOk`; an A/D `t` is valid by PO-ad from `Valid(t−1)`
  "whether or not it has been fulfilled yet".
* `wpAV_lift`: as `wpA_lift` for a v2 label (handed `memStepV` of the variant, fetch arm included; the fulfil
  obligation `fulT g t` is asked only for a NON-A/D `t`), plus an A/D arm: the hart's own A/D update is never
  blocked — no frontier guard, no obligation, `ws` and the trace unchanged, the promise consumed.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAAdSched

namespace Weak.Prom.OAd

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.OA
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

variable {P D V : Type} {hlc : HasLC}

/-! ## 1. Pure lemmas -/

/-- The variant's fetch view is below the fetch sources (CoreFwd.lean `fetchView_le`). -/
theorem fetchViewV_le (log : List PMsg) (i : Nat) (prom : GSet Nat) :
    ∀ (base : Int) (tvs : List (Nat × BitVec 8)), Ad.fetchViewV log i prom base tvs ≤ bytesMax (fun _ t => t) base tvs
  | _, [] => Nat.le_refl _
  | a, (t, _) :: r => by
    have ih := fetchViewV_le log i prom (a + 1) r
    unfold Ad.fetchViewV at ih ⊢
    simp only [bytesMax]
    split <;> omega

/-- `stage ≥ WF ⊢ Valid(WF)` over the variant (plan §3 second rule, `ValidInduction` bounded at `WF`). -/
theorem valid_frontV {π : Proto} {img : Image} {M : List PMsg} {Ψ : Nat → Trace → Prop} {n : Nat} {σ : CSt}
    {h : Nat} (hf : cFacts π img M Ψ n σ) (hout : ∀ k, n ≤ k → (σ k).2.2 = []) (hok : fOkV M σ h)
    (had : PO_adV π img M) (hex : adExactV img M) : Valid π img M (wfr (σ h).1) := by
  refine valid_of_protoOk hf.1 (fun t h1 h2 => ?_)
  by_cases hat : Ad.adAt M t
  · exact protoOk_ad had hex h1 (by omega) hat
  · obtain ⟨k, e, he, het⟩ := hok t h1 (by omega) (by omega) hat
    have hk : k < n := by
      apply Classical.byContradiction; intro hk
      rw [hout k (by omega)] at he; cases he
    exact (hf.2 k hk).2.1 e he t het

/-- `cFacts` survive a v2-label step of the variant (the fetch arm with `fetchViewV`). -/
theorem cFactsV_step {π : Proto} {img : Image} {M : List PMsg} {Ψ : Nat → Trace → Prop} {n : Nat} {σ : CSt}
    {h : Nat} {l : PLabel} {ots : Option Nat} {ws' : PState} {pr' : GSet Nat}
    (hf : cFacts π img M Ψ n σ) (hh : h < n)
    (hm : Ad.memStepV img M h (σ h).2.1 (σ h).1 (.v l) ots ws' pr')
    (hok : stepOk π img M (Ψ h) (σ h).1 (σ h).2.2 l ots) :
    cFacts π img M Ψ n (updS σ h (ws', pr', (σ h).2.2 ++ [(l, ots)])) := by
  by_cases hfe : Nfr.F.isFetch l
  · obtain ⟨b, tvs, rfl⟩ := hfe
    obtain ⟨_, rfl, rfl, rfl⟩ := Ad.memStepV_fetch_inv hm
    refine ⟨hf.1, fun k hk => ?_⟩
    by_cases e : k = h
    · subst e
      rw [updS_self]
      obtain ⟨hΨ, hp, hfi, hfk⟩ := hf.2 k hk
      have hv := fetchViewV_le M k (σ k).2.1 b tvs
      refine ⟨fun j => ?_, fun e he t het => ?_, ?_, ?_⟩
      · by_cases hj : j ≤ (σ k).2.2.length
        · rw [List.take_append_of_le_length hj]; exact hΨ j
        · rw [List.take_of_length_le (by simp; omega)]; exact hok.1
      · rcases List.mem_append.1 he with he | he
        · exact hp e he t het
        · rw [List.mem_singleton] at he; subst he; cases het
      · unfold fetchInv at hfi ⊢; simp only [Ad.fetchPostV]; omega
      · exact fwdKnow_keep (ws := (σ k).1) rfl (plainFloor_of (Nat.le_refl _) (by simp only [Ad.fetchPostV]; omega)) hfk
    · rw [updS_ne σ _ e]; exact hf.2 k hk
  · exact cFacts_step hf hh (Ad.memStepV_v_inv hm hfe) hok

/-- An A/D step keeps `cFacts` (it changes neither `ws` nor the trace). -/
theorem cFacts_keep {π : Proto} {img : Image} {M : List PMsg} {Ψ : Nat → Trace → Prop} {n : Nat} {σ : CSt}
    {h : Nat} {pr' : GSet Nat} (hf : cFacts π img M Ψ n σ) :
    cFacts π img M Ψ n (updS σ h ((σ h).1, pr', (σ h).2.2)) := by
  refine ⟨hf.1, fun k hk => ?_⟩
  by_cases e : k = h
  · subst e; rw [updS_self]; exact hf.2 k hk
  · rw [updS_ne σ _ e]; exact hf.2 k hk

/-- An A/D step keeps every hart's frontier claim. -/
theorem fOkV_keep {M : List PMsg} {σ : CSt} {h k : Nat} {pr' : GSet Nat} (hok : fOkV M σ k) :
    fOkV M (updS σ h ((σ h).1, pr', (σ h).2.2)) k := by
  unfold fOkV
  have e : (updS σ h ((σ h).1, pr', (σ h).2.2) k).1 = (σ k).1 := by
    by_cases hk : k = h
    · subst hk; rw [updS_self]
    · rw [updS_ne σ _ hk]
  rw [e]
  exact fun t h1 h2 h3 h4 => fulAt_updS_keep.2 (hok t h1 h2 h3 h4)

/-- The claim of every other hart survives a v2-label step. -/
theorem fOkV_updS {M : List PMsg} {σ : CSt} {h k : Nat} {ws' : PState} {pr' : GSet Nat} {e : PEv}
    (hok : fOkV M σ k) (hk : k ≠ h) : fOkV M (updS σ h (ws', pr', (σ h).2.2 ++ [e])) k := by
  unfold fOkV
  rw [updS_ne σ _ hk]
  exact stageGeV_updS hok

/-! ## 2. The state interpretation, the wp -/

section si

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool]

/-- THE STATE INTERPRETATION over the variant (OwnAWp.lean `stA`; see the header for the three differences). -/
def stAV (g : AGN) (π : Proto) (img : Image) (M : List PMsg) (Ψ : Nat → Trace → Prop) (σ : CSt) : IProp GF :=
  iprop(([∗list] k ↦ γ ∈ g.hn, ghost_var γ (.own (1 : Qp).half) (σ k)) ∗
    ⌜∀ k, g.hn.length ≤ k → (σ k).2.2 = []⌝ ∗
    ⌜∀ k, fOkV M σ k⌝ ∗
    □ (∀ t, ⌜1 ≤ t ∧ t ≤ M.length ∧ (fulAt σ t ∨ Ad.adAt M t)⌝ → fulT g t) ∗
    ⌜PO_adV π img M ∧ adExactV img M⌝ ∗
    (⌜cFacts π img M Ψ g.hn.length σ⌝ ∨ dshot g))

/-- The iris-lean `IrisGS` of the variant's concurrent language: one `▷` and `£ 1` per step. -/
@[reducible] def aIrisGSV [InvGS_gen hlc GF] (g : AGN) (π : Proto) (img : Image) (M : List PMsg)
    (Ψ : Nat → Trace → Prop) : IrisGS_gen hlc (CExprV P D V) GF where
  toStateInterp := ⟨fun σ _ _ _ => stAV g π img M Ψ σ⟩
  invGS := inferInstance
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by iintro $

theorem aStateIV_eq [InvGS_gen hlc GF] (g : AGN) (π : Proto) (img : Image) (M : List PMsg)
    (Ψ : Nat → Trace → Prop) (σ : CSt) (ns : Nat) (obs : List Unit) (nt : Nat) :
    @stateInterp CSt Unit GF (aIrisGSV (P := P) (D := D) (V := V) g π img M Ψ).toStateInterp σ ns obs nt =
      stAV g π img M Ψ σ := rfl

/-- **`wpAV g π w Ψ s Φ`**: hart `w.h`'s weakest precondition over the variant. -/
def wpAV [InvGS_gen hlc GF] (g : AGN) (π : Proto) (w : HWV P D V) (Ψ : Nat → Trace → Prop) (s : P)
    (Φ : V → IProp GF) : IProp GF :=
  letI : IrisGS_gen hlc (CExprV P D V) GF := aIrisGSV g π w.img w.M Ψ
  WP (CExprV.run w s) @ Stuckness.MaybeStuck; ⊤ {{ Φ }}

end si

/-! ## 3. The lifting lemma -/

section lift

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [InvGS_gen hlc GF]

/-- **THE LIFTING LEMMA over the variant** (OwnAWp.lean `wpA_lift` plus the A/D arm).  A v2-label step: the
client is handed the pre-state facts and THE FRONTIER RULE at the pre-state, returns `stepOk`, `fulT g t` for a
fulfil of a NON-A/D `t`, and the continuation.  An A/D update: the client only continues (no guard, no
obligation; `ws` and the trace unchanged, the promise consumed).  The value step proves `Φ v`. -/
theorem wpAV_lift {g : AGN} {π : Proto} {w : HWV P D V} {Ψ : Nat → Trace → Prop} {s : P} {Φ : V → IProp GF}
    {ws : PState} {pr : GSet Nat} {τ : Trace} :
    hartA g w.h ws pr τ ∗
    ▷ ((∀ v, ⌜w.pdone s = some v⌝ -∗ hartA g w.h ws pr τ -∗ |={⊤}=> Φ v) ∧
       ((∀ l ots s' ws' pr', ⌜∃ d d', w.pstep s d (.v l) s' d'⌝ -∗
          ⌜Ad.memStepV w.img w.M w.h pr ws (.v l) ots ws' pr'⌝ -∗
          (⌜hartFacts π w.img w.M (Ψ w.h) (ws, pr, τ)⌝ ∨ dshot g) -∗ frontA g π w.img w.M ws -∗ £ 1 -∗
          |={⊤}=> (⌜stepOk π w.img w.M (Ψ w.h) ws τ l ots⌝ ∨ dshot g) ∗
            (∀ t, ⌜ots = some t ∧ ¬ Ad.adAt w.M t⌝ → fulT g t) ∗
            (hartA g w.h ws' pr' (τ ++ [(l, ots)]) -∗ wpAV g π w Ψ s' Φ)) ∧
        (∀ b tvs data ots s' pr', ⌜∃ d d', w.pstep s d (.ad b tvs data) s' d'⌝ -∗
          ⌜Ad.memStepV w.img w.M w.h pr ws (.ad b tvs data) ots ws pr'⌝ -∗ £ 1 -∗
          |={⊤}=> (hartA g w.h ws pr' τ -∗ wpAV g π w Ψ s' Φ))))
    ⊢ wpAV g π w Ψ s Φ := by
  letI : IrisGS_gen hlc (CExprV P D V) GF := aIrisGSV g π w.img w.M Ψ
  show _ ⊢ WP (CExprV.run w s) @ Stuckness.MaybeStuck; ⊤ {{ Φ }}
  iintro ⟨Hst, Hk⟩
  unfold hartA
  icases Hst with ⟨%hh, Hst⟩
  iapply wp_lift_step (rfl : toVal (CExprV.run w s : CExprV P D V) = none)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rw [aStateIV_eq]
  unfold stAV
  icases Hσ with ⟨Hbig, %Hout, %Hok, #Hshots, %Had, #Hfacts⟩
  icases harts_acc (GF := GF) g.hn σ₁ w.h hh $$ Hbig with ⟨Hγ, Hclose⟩
  ihave %Heq := ghost_var_agree _ _ _ _ _ $$ Hγ Hst
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  isplit
  · ipureintro; trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  change cstepV _ _ _ at Hstep
  cases Hstep with
  | lab _ _ _ l ots s' ws' pr' d d' hp hm hfok =>
    have hτ : (σ₁ w.h).2.2 = τ := by rw [Heq]
    rw [Heq] at hm
    icases Hk with ⟨-, Hk⟩
    icases Hk with ⟨Hk, -⟩
    imod Hmask
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
        by_cases hat : Ad.adAt w.M t
        · exact .inr hat
        · have := Hok w.h t ht.1 ht.2.1
          rw [Heq] at this
          exact .inl (this ht.2.2 hat)
      · icases Hfacts with (%Hf | #Hd)
        · ileft; ipureintro
          have := valid_frontV Hf Hout (Hok w.h) Had.1 Had.2
          rw [Heq] at this; exact this
        · iright; iexact Hd
    imod Hk $$ %l %ots %s' %ws' %pr' %⟨d, d', hp⟩ %hm Hpre Hfront Hcred with ⟨Hstep, #Hsh, Hk⟩
    imod ghost_var_update_halves ((ws', pr', τ ++ [(l, ots)]) : HSt) _ _ _ $$ Hγ Hst with ⟨Hγ, Hst⟩
    imodintro
    rw [aStateIV_eq]
    unfold stAV
    have hout' : ∀ k, g.hn.length ≤ k →
        (updS σ₁ w.h (ws', pr', (σ₁ w.h).2.2 ++ [(l, ots)]) k).2.2 = [] := by
      intro k hk
      rw [updS_ne σ₁ _ (by omega)]; exact Hout k hk
    have hok' : ∀ k, fOkV w.M (updS σ₁ w.h (ws', pr', (σ₁ w.h).2.2 ++ [(l, ots)])) k := by
      intro k
      by_cases hk : k = w.h
      · subst hk; exact hfok
      · exact fOkV_updS (Hok k) hk
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
        rcases ht.2.2 with ht' | hat
        · rcases fulAt_updS_inv ht' with hf | hf
          · iapply Hshots; ipureintro; exact ⟨ht.1, ht.2.1, .inl hf⟩
          · by_cases hat : Ad.adAt w.M t
            · iapply Hshots; ipureintro; exact ⟨ht.1, ht.2.1, .inr hat⟩
            · iapply Hsh; ipureintro; exact ⟨hf, hat⟩
        · iapply Hshots; ipureintro; exact ⟨ht.1, ht.2.1, .inr hat⟩
      isplitr
      · ipureintro; exact Had
      · icases Hstep with (%Hs | #Hd)
        · icases Hfacts with (%Hf | #Hd)
          · ileft; ipureintro
            exact cFactsV_step (l := l) (ots := ots) (ws' := ws') (pr' := pr') Hf hh
              (by rw [Heq]; exact hm) (by rw [Heq]; exact Hs)
          · iright; iexact Hd
        · iright; iexact Hd
    isplitl [Hk Hst]
    · dsimp only [wpAV]
      iapply Hk
      iframe Hst
      ipureintro; exact hh
    · exact BigSepL.bigSepL_nil_intro
  | ad _ _ _ b tvs data ots s' pr' d d' hp hm =>
    rw [Heq] at hm
    have e2 : (((σ₁ w.h).1, pr', (σ₁ w.h).2.2) : HSt) = (ws, pr', τ) := by rw [Heq]
    icases Hk with ⟨-, Hk⟩
    icases Hk with ⟨-, Hk⟩
    imod Hmask
    imod Hk $$ %b %tvs %data %ots %s' %pr' %⟨d, d', hp⟩ %hm Hcred with Hk
    imod ghost_var_update_halves ((ws, pr', τ) : HSt) _ _ _ $$ Hγ Hst with ⟨Hγ, Hst⟩
    imodintro
    rw [aStateIV_eq]
    unfold stAV
    have hout' : ∀ k, g.hn.length ≤ k → (updS σ₁ w.h ((σ₁ w.h).1, pr', (σ₁ w.h).2.2) k).2.2 = [] := by
      intro k hk
      rw [updS_ne σ₁ _ (by omega)]; exact Hout k hk
    have hok' : ∀ k, fOkV w.M (updS σ₁ w.h ((σ₁ w.h).1, pr', (σ₁ w.h).2.2)) k := fun k => fOkV_keep (Hok k)
    isplitl [Hγ Hclose]
    · isplitl [Hγ Hclose]
      · rw [e2]; iapply Hclose $$ Hγ
      isplitr
      · ipureintro; exact hout'
      isplitr
      · ipureintro; exact hok'
      isplitr
      · imodintro
        iintro %t %ht
        iapply Hshots; ipureintro
        exact ⟨ht.1, ht.2.1, ht.2.2.imp_left fulAt_updS_keep.1⟩
      isplitr
      · ipureintro; exact Had
      · icases Hfacts with (%Hf | #Hd)
        · ileft; ipureintro; exact cFacts_keep Hf
        · iright; iexact Hd
    isplitl [Hk Hst]
    · dsimp only [wpAV]
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
    rw [aStateIV_eq]
    unfold stAV
    isplitl [Hγ Hclose]
    · isplitl [Hγ Hclose]
      · ihave H := Hclose $$ Hγ
        rw [updS_same]
        iexact H
      iframe Hshots Hfacts
      ipureintro; exact ⟨Hout, Hok, Had⟩
    isplitl [Hv]
    · iapply (wp_value_fupd' (v := v)).2
      imodintro
      iexact Hv
    · exact BigSepL.bigSepL_nil_intro

end lift

end Weak.Prom.OAd
