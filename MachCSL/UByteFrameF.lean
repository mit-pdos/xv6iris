/-
MachCSL: **the byte frame with a per-address fraction** (W8 (f3-utext)
[OWN.89] (W-R)): the user tier's walker map once the open epoch's custody
holds half of the read-only bytes (the user text, the page-table slots).

`ubOwnF ξ D fr mm` owns every address `a` of `D` at the fraction `fr a`
(`DFrac.own 1` or a half), its byte the map's.  Reads hand out a HALF of any
owned window (`ubFrameF_accR`: a full byte is split, its other half kept
aside); writes need the window in full (`ubFrameF_acc`: every byte of a
window off the read-only bytes is owned in full).
-/
import MachCSL.UByteFrame

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std
open Sail

section iris
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- The read-only fraction (three quarters: the open epoch's custody holds
the last quarter). -/
abbrev dqRO : DFrac := DFrac.own Qp.threeQuarters

/-- What a full byte keeps aside from a reader. -/
abbrev dqRest : DFrac := DFrac.own Qp.quarter

theorem qp_tq_add_q : Qp.threeQuarters + Qp.quarter = 1 := Subtype.ext (by grind)

/-- A full context byte is a reader's three quarters and a quarter. -/
theorem ctxByte_halve (ξ : CtxId) (a : PAddr) (b : BitVec 8) :
    ctxByte (GF := GF) ξ a (DFrac.own 1) b ⊣⊢ ctxByte ξ a dqRO b ∗ ctxByte ξ a dqRest b := by
  constructor
  · iintro H
    icases ctxByte_cases_np ξ a (DFrac.own 1) b $$ H with ⟨%hnp, %e, %He, Hpt, %hev, #Hkey⟩
    have h := (Fractional.fractional (Φ := fun q => iprop(a ↦ₕ{DFrac.own q} (e :: He)))
      Qp.threeQuarters Qp.quarter)
    rw [qp_tq_add_q] at h
    icases h.1 $$ Hpt with ⟨H1, H2⟩
    isplitl [H1]
    · unfold ctxByte; iexists e, He; iframe H1 Hkey; ipureintro; exact ⟨hev, hnp⟩
    · unfold ctxByte; iexists e, He; iframe H2 Hkey; ipureintro; exact ⟨hev, hnp⟩
  · iintro ⟨H1, H2⟩
    icases ctxByte_cases_np ξ a dqRO b $$ H1 with ⟨%hnp, %e, %He, Hpt1, %hev, #Hkey⟩
    icases ctxByte_cases_np ξ a dqRest b $$ H2 with ⟨%hnp, %e', %He', Hpt2, %_, _⟩
    ihave %hag := pointsTo_agree $$ [Hpt1 Hpt2]
    · iframe Hpt1 Hpt2
    rw [← hag]
    have h := pointsTo_combine (GF := GF) (L := PAddr) (V := Hist) (H := MemF)
      (l := a) (dq₁ := DFrac.own Qp.threeQuarters) (dq₂ := DFrac.own Qp.quarter)
      (v₁ := e :: He) (v₂ := e :: He)
    rw [DFrac.op_own, qp_tq_add_q] at h
    icases h $$ [Hpt1 Hpt2] with ⟨Hpt, _⟩
    · iframe Hpt1 Hpt2
    unfold ctxByte
    iexists e, He
    iframe Hpt Hkey
    ipureintro; exact ⟨hev, hnp⟩

/-- The fraction a half-label gives. -/
def ubFr (hf : PAddr → Bool) (a : PAddr) : DFrac := if hf a then dqRO else DFrac.own 1

/-- **The owned bytes of `D`**, each at its fraction: a half where `hf`
says, in full elsewhere. -/
def ubOwnF (ξ : CtxId) (D : List PAddr) (hf : PAddr → Bool) (mm : BMap) : IProp GF :=
  iprop([∗list] a ∈ D, ∃ b : BitVec 8, ⌜mm a = some b⌝ ∗ ctxByte ξ a (ubFr hf a) b)

theorem ubOwnF_app (ξ : CtxId) (D₁ D₂ : List PAddr) (hf : PAddr → Bool) (mm : BMap) :
    ubOwnF (GF := GF) ξ (D₁ ++ D₂) hf mm ⊣⊢ iprop(ubOwnF ξ D₁ hf mm ∗ ubOwnF ξ D₂ hf mm) := by
  unfold ubOwnF; exact BigSepL.bigSepL_append

theorem ubOwnF_perm (ξ : CtxId) (D₁ D₂ : List PAddr) (hf : PAddr → Bool) (mm : BMap) (h : D₁.Perm D₂) :
    ubOwnF (GF := GF) ξ D₁ hf mm ⊣⊢ ubOwnF ξ D₂ hf mm := by
  unfold ubOwnF; exact BigSepL.bigSepL_perm h

theorem ubOwnF_congr (ξ : CtxId) (D : List PAddr) (hf : PAddr → Bool) (mm mm' : BMap)
    (h : ∀ a ∈ D, mm' a = mm a) : ubOwnF (GF := GF) ξ D hf mm ⊢ ubOwnF ξ D hf mm' := by
  unfold ubOwnF
  apply BigSepL.bigSepL_mono
  intro k a hk
  rw [h a (List.mem_of_getElem? hk)]

/-- Where no byte is a half, the bytes are `ubOwn`'s. -/
theorem ubOwnF_full (ξ : CtxId) (D : List PAddr) (hf : PAddr → Bool) (mm : BMap)
    (h : ∀ a ∈ D, hf a = false) : ubOwnF (GF := GF) ξ D hf mm ⊣⊢ ubOwn ξ D mm := by
  unfold ubOwnF ubOwn
  constructor <;>
  · apply BigSepL.bigSepL_mono
    intro k a hk
    simp only [ubFr, h a (List.mem_of_getElem? hk), Bool.false_eq_true, if_false]
    exact .rfl

/-- What a full byte keeps aside when a reader takes half. -/
def ubRest (ξ : CtxId) (hf : PAddr → Bool) (mm : BMap) (a : PAddr) : IProp GF :=
  if hf a then iprop(emp) else iprop(∃ b : BitVec 8, ⌜mm a = some b⌝ ∗ ctxByte ξ a dqRest b)

theorem ubOwnF_byte_halves (ξ : CtxId) (hf : PAddr → Bool) (mm : BMap) (a : PAddr) :
    iprop(∃ b : BitVec 8, ⌜mm a = some b⌝ ∗ ctxByte (GF := GF) ξ a (ubFr hf a) b) ⊣⊢
      iprop((∃ b : BitVec 8, ⌜mm a = some b⌝ ∗ ctxByte ξ a dqRO b) ∗ ubRest ξ hf mm a) := by
  unfold ubRest ubFr
  cases h : hf a with
  | true =>
    simp only [if_true]
    constructor
    · iintro H; iframe H
    · iintro ⟨H, _⟩; iexact H
  | false =>
    simp only [Bool.false_eq_true, if_false]
    constructor
    · iintro ⟨%b, %hb, H⟩
      icases (ctxByte_halve ξ a b).1 $$ H with ⟨H1, H2⟩
      isplitl [H1]
      · iexists b; iframe H1; ipureintro; exact hb
      · iexists b; iframe H2; ipureintro; exact hb
    · iintro ⟨⟨%b, %hb, H1⟩, ⟨%b', %hb', H2⟩⟩
      rw [hb] at hb'
      obtain rfl := Option.some.inj hb'
      iexists b
      isplitr
      · ipureintro; exact hb
      iapply (ctxByte_halve ξ a b).2
      iframe

/-- **Half of every byte of `D`**, the rest aside. -/
theorem ubOwnF_halves (ξ : CtxId) (D : List PAddr) (hf : PAddr → Bool) (mm : BMap) :
    ubOwnF (GF := GF) ξ D hf mm ⊣⊢
      iprop(ubOwnF ξ D (fun _ => true) mm ∗ [∗list] a ∈ D, ubRest ξ hf mm a) := by
  unfold ubOwnF
  have hpt : ∀ a, iprop(∃ b : BitVec 8, ⌜mm a = some b⌝ ∗ ctxByte (GF := GF) ξ a (ubFr hf a) b) ⊣⊢
      iprop((∃ b : BitVec 8, ⌜mm a = some b⌝ ∗ ctxByte ξ a (ubFr (fun _ => true) a) b) ∗ ubRest ξ hf mm a) :=
    fun a => ubOwnF_byte_halves ξ hf mm a
  refine (⟨BigSepL.bigSepL_mono fun {_ a} _ => (hpt a).1, BigSepL.bigSepL_mono fun {_ a} _ => (hpt a).2⟩ :
    _ ⊣⊢ _).trans BigSepL.bigSepL_sep_eqv

/-- The all-half bytes of a readable window are a half `ctxBytes` word. -/
theorem ubOwnF_win_half (ξ : CtxId) (pa : PAddr) (n : Nat) (mm : BMap) (w : BitVec (8 * n))
    (hr : bmRead mm pa n = some w) :
    ubOwnF (GF := GF) ξ (ubWin pa n) (fun _ => true) mm ⊣⊢ ctxBytes ξ pa n dqRO w := by
  unfold ubOwnF ubWin ctxBytes
  rw [BigSepL.bigSepL_map]
  constructor
  · apply BigSepL.bigSepL_mono
    intro k j hk
    have hj : j < n := List.mem_range.1 (List.mem_of_getElem? hk)
    have hs := bmRead_spec mm pa n w hr j hj
    simp only [ubFr, if_true]
    iintro ⟨%b, %hb, H⟩
    rw [hs] at hb
    obtain rfl := Option.some.inj hb
    iexact H
  · apply BigSepL.bigSepL_mono
    intro k j hk
    have hj : j < n := List.mem_range.1 (List.mem_of_getElem? hk)
    have hs := bmRead_spec mm pa n w hr j hj
    simp only [ubFr, if_true]
    iintro H
    iexists nthByte w j
    iframe H
    ipureintro; exact hs

/-- **The byte frame with half-labels** over the addresses `D` (the map's
domain exactly `D`). -/
def ubFrameFB (ξ : CtxId) (D : List PAddr) (hf : PAddr → Bool) (mm : BMap) : IProp GF :=
  iprop(⌜D.Nodup ∧ ∀ a, (mm a).isSome = true ↔ a ∈ D⌝ ∗ ubOwnF ξ D hf mm)

/-- **A read of an owned window**: half of each byte, at the map's value. -/
theorem ubFrameFB_accR (ξ : CtxId) (D : List PAddr) (hf : PAddr → Bool) (mm : BMap) (pa : PAddr) (n : Nat)
    (hn : n < 2 ^ 64) (ho : bmOwned mm pa n = true) :
    ubFrameFB (GF := GF) ξ D hf mm ⊢ ∃ (dq : DFrac) (w : BitVec (8 * n)), ⌜bmRead mm pa n = some w⌝ ∗
      ctxBytes ξ pa n dq w ∗ (ctxBytes ξ pa n dq w -∗ ubFrameFB ξ D hf mm) := by
  obtain ⟨w, hw⟩ := bmRead_of_owned mm pa n ho
  unfold ubFrameFB
  iintro ⟨%⟨hnd, hdom⟩, H⟩
  have hsub : ∀ a ∈ ubWin pa n, a ∈ D := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := (ubWin_mem pa n a).1 ha
    exact (hdom _).1 ((bmOwned_iff mm pa n).1 ho j hj)
  have hp := ub_perm_win D pa n (by omega) hnd hsub
  icases (ubOwnF_perm ξ _ _ hf mm hp).1 $$ H with H
  icases (ubOwnF_app ξ _ _ hf mm).1 $$ H with ⟨Hw, Hr⟩
  icases (ubOwnF_halves ξ _ hf mm).1 $$ Hw with ⟨Hh, Hrest⟩
  ihave Hb := (ubOwnF_win_half ξ pa n mm w hw).1 $$ Hh
  iexists dqRO, w
  isplitr
  · ipureintro; exact hw
  iframe Hb
  iintro Hb
  isplitr
  · ipureintro; exact ⟨hnd, hdom⟩
  iapply (ubOwnF_perm ξ _ _ hf mm hp).2
  iapply (ubOwnF_app ξ _ _ hf mm).2
  iframe Hr
  iapply (ubOwnF_halves ξ _ hf mm).2
  iframe Hrest
  iapply (ubOwnF_win_half ξ pa n mm w hw).2 $$ Hb

/-- **A write of an owned window off the half bytes**: the window in full,
taken back at any value. -/
theorem ubFrameFB_acc (ξ : CtxId) (D : List PAddr) (hf : PAddr → Bool) (mm : BMap) (pa : PAddr) (n : Nat)
    (hn : n < 2 ^ 64) (ho : bmOwned mm pa n = true) (hfull : ∀ j, j < n → hf (pa + BitVec.ofNat 64 j) = false) :
    ubFrameFB (GF := GF) ξ D hf mm ⊢ ∃ w : BitVec (8 * n), ⌜bmRead mm pa n = some w⌝ ∗
      ctxBytes ξ pa n (DFrac.own 1) w ∗
      ∀ w' : BitVec (8 * n), ctxBytes ξ pa n (DFrac.own 1) w' -∗ ubFrameFB ξ D hf (bmWrite mm pa n w') := by
  obtain ⟨w, hw⟩ := bmRead_of_owned mm pa n ho
  unfold ubFrameFB
  iintro ⟨%⟨hnd, hdom⟩, H⟩
  have hsub : ∀ a ∈ ubWin pa n, a ∈ D := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := (ubWin_mem pa n a).1 ha
    exact (hdom _).1 ((bmOwned_iff mm pa n).1 ho j hj)
  have hfw : ∀ a ∈ ubWin pa n, hf a = false := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := (ubWin_mem pa n a).1 ha
    exact hfull j hj
  have hp := ub_perm_win D pa n (by omega) hnd hsub
  icases (ubOwnF_perm ξ _ _ hf mm hp).1 $$ H with H
  icases (ubOwnF_app ξ _ _ hf mm).1 $$ H with ⟨Hw, Hr⟩
  ihave Hw := (ubOwnF_full ξ _ hf mm hfw).1 $$ Hw
  ihave Hb := ubOwn_win ξ pa n mm w hw $$ Hw
  iexists w
  isplitr
  · ipureintro; exact hw
  iframe Hb
  iintro %w' Hb
  isplitr
  · ipureintro
    refine ⟨hnd, fun a => ?_⟩
    rw [bmWrite_isSome mm pa n w' (by omega) ho a]
    exact hdom a
  iapply (ubOwnF_perm ξ _ _ hf _ hp).2
  iapply (ubOwnF_app ξ _ _ hf _).2
  isplitl [Hb]
  · iapply (ubOwnF_full ξ _ hf _ hfw).2
    iapply ubOwn_of_win ξ pa n (by omega) mm w' $$ Hb
  · iapply ubOwnF_congr ξ _ hf mm _ ?_ $$ Hr
    intro a ha
    simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at ha
    exact bmWrite_other mm pa n w' a ha.2

/-! ## Association lists at the labels' fractions -/

/-- An association list of bytes, each at its label's fraction. -/
def ubOwnAF (ξ : CtxId) (hf : PAddr → Bool) (A : List (PAddr × BitVec 8)) : IProp GF :=
  iprop([∗list] p ∈ A, ctxByte ξ p.1 (ubFr hf p.1) p.2)

theorem ubOwnAF_app (ξ : CtxId) (hf : PAddr → Bool) (A₁ A₂ : List (PAddr × BitVec 8)) :
    ubOwnAF (GF := GF) ξ hf (A₁ ++ A₂) ⊣⊢ iprop(ubOwnAF ξ hf A₁ ∗ ubOwnAF ξ hf A₂) := by
  unfold ubOwnAF; exact BigSepL.bigSepL_append

theorem ubOwnAF_flatMap {X : Type} (ξ : CtxId) (hf : PAddr → Bool) (l : List X) (f : X → List (PAddr × BitVec 8)) :
    ubOwnAF (GF := GF) ξ hf (l.flatMap f) = iprop([∗list] x ∈ l, ubOwnAF ξ hf (f x)) := by
  unfold ubOwnAF; exact BigSepL.bigSepL_flatMap f

/-- A list at one fraction, which is every element's label fraction, is the
labelled list. -/
theorem ubOwnAF_of_const (ξ : CtxId) (hf : PAddr → Bool) (A : List (PAddr × BitVec 8)) (dq : DFrac)
    (h : ∀ p ∈ A, ubFr hf p.1 = dq) :
    ubOwnAF (GF := GF) ξ hf A ⊣⊢ [∗list] p ∈ A, ctxByte ξ p.1 dq p.2 := by
  unfold ubOwnAF
  constructor <;>
  · apply BigSepL.bigSepL_mono
    intro k p hk
    rw [h p (List.mem_of_getElem? hk)]

/-- **The labelled list is the frame's bytes**, at any map holding it. -/
theorem ubOwnAF_own (ξ : CtxId) (hf : PAddr → Bool) (A : List (PAddr × BitVec 8)) (mm : BMap)
    (h : ∀ p ∈ A, mm p.1 = some p.2) :
    ubOwnAF (GF := GF) ξ hf A ⊢ ubOwnF ξ (A.map Prod.fst) hf mm := by
  unfold ubOwnAF ubOwnF
  rw [BigSepL.bigSepL_map]
  apply BigSepL.bigSepL_mono
  intro k p hk
  iintro H
  iexists p.2
  iframe H
  ipureintro; exact h p (List.mem_of_getElem? hk)

theorem ubOwnF_ownAF (ξ : CtxId) (hf : PAddr → Bool) (A : List (PAddr × BitVec 8)) (mm : BMap)
    (h : ∀ p ∈ A, mm p.1 = some p.2) :
    ubOwnF (GF := GF) ξ (A.map Prod.fst) hf mm ⊢ ubOwnAF ξ hf A := by
  unfold ubOwnAF ubOwnF
  rw [BigSepL.bigSepL_map]
  apply BigSepL.bigSepL_mono
  intro k p hk
  iintro ⟨%b, %hb, H⟩
  rw [h p (List.mem_of_getElem? hk)] at hb
  obtain rfl := Option.some.inj hb
  iexact H

/-- Two label fractions together are more than the whole. -/
theorem ubFr_op_invalid (hf : PAddr → Bool) (a a' : PAddr) : ¬ ✓ (ubFr hf a • ubFr hf a') := by
  unfold ubFr dqRO
  intro h
  have key : ∀ q q' : Qp, (q = Qp.threeQuarters ∨ q = 1) → (q' = Qp.threeQuarters ∨ q' = 1) →
      ¬ ✓ (DFrac.own q • DFrac.own q') := by
    intro q q' hq hq' hv
    rw [DFrac.op_own] at hv
    have hv' : (q + q').val ≤ 1 := DFrac.valid_own.1 hv
    rcases hq with rfl | rfl <;> rcases hq' with rfl | rfl <;> simp at hv' <;> grind
  cases ha : hf a <;> cases ha' : hf a' <;> simp only [ha, ha', if_true, Bool.false_eq_true, if_false] at h <;>
    first
    | exact key _ _ (Or.inl rfl) (Or.inl rfl) h
    | exact key _ _ (Or.inl rfl) (Or.inr rfl) h
    | exact key _ _ (Or.inr rfl) (Or.inl rfl) h
    | exact key _ _ (Or.inr rfl) (Or.inr rfl) h

theorem ubOwnAF_nodup' (ξ : CtxId) (hf : PAddr → Bool) : ∀ A : List (PAddr × BitVec 8),
    iprop([∗list] p ∈ A, ctxByte (GF := GF) ξ p.1 (ubFr hf p.1) p.2) ⊢ ⌜(A.map Prod.fst).Nodup⌝
  | [] => by iintro _; ipureintro; exact List.nodup_nil
  | p :: A => by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hp, H⟩
    ihave %hnd := ubOwnAF_nodup' ξ hf A $$ H
    ihave %hni : ⌜p.1 ∉ A.map Prod.fst⌝ $$ [Hp H]
    · by_cases ha : p.1 ∈ A.map Prod.fst
      · obtain ⟨q, hq, hqe⟩ := List.mem_map.1 ha
        icases BigSepL.bigSepL_mem_acc (Φ := fun q : PAddr × BitVec 8 => ctxByte ξ q.1 (ubFr hf q.1) q.2) hq
          $$ H with ⟨Hq, -⟩
        icases ctxByte_cases_np ξ _ _ _ $$ Hp with ⟨%hnp, %e, %He, Hpt, -, -⟩
        icases ctxByte_cases_np ξ _ _ _ $$ Hq with ⟨%hnp, %e', %He', Hpt', -, -⟩
        ihave %hne := pointsTo_frac_ne (ubFr_op_invalid hf p.1 q.1) $$ Hpt Hpt'
        exact (hne hqe.symm).elim
      · ipureintro; exact ha
    ipureintro
    rw [List.map_cons]
    exact List.nodup_cons.2 ⟨hni, hnd⟩

/-- **A labelled list has distinct addresses** (every label fraction is more
than half). -/
theorem ubOwnAF_nodup (ξ : CtxId) (hf : PAddr → Bool) (A : List (PAddr × BitVec 8)) :
    ubOwnAF (GF := GF) ξ hf A ⊢ ⌜(A.map Prod.fst).Nodup⌝ := by
  unfold ubOwnAF; exact ubOwnAF_nodup' ξ hf A

/-- Two label fractions (of any labels) together are more than the whole. -/
theorem ubFr_op_invalid2 (hf hf' : PAddr → Bool) (a a' : PAddr) : ¬ ✓ (ubFr hf a • ubFr hf' a') := by
  unfold ubFr dqRO
  intro h
  have key : ∀ q q' : Qp, (q = Qp.threeQuarters ∨ q = 1) → (q' = Qp.threeQuarters ∨ q' = 1) →
      ¬ ✓ (DFrac.own q • DFrac.own q') := by
    intro q q' hq hq' hv
    rw [DFrac.op_own] at hv
    have hv' : (q + q').val ≤ 1 := DFrac.valid_own.1 hv
    rcases hq with rfl | rfl <;> rcases hq' with rfl | rfl <;> simp at hv' <;> grind
  cases ha : hf a <;> cases ha' : hf' a' <;> simp only [ha, ha', if_true, Bool.false_eq_true, if_false] at h <;>
    first
    | exact key _ _ (Or.inl rfl) (Or.inl rfl) h
    | exact key _ _ (Or.inl rfl) (Or.inr rfl) h
    | exact key _ _ (Or.inr rfl) (Or.inl rfl) h
    | exact key _ _ (Or.inr rfl) (Or.inr rfl) h

/-- **Two labelled lists, under any labels, have disjoint addresses.** -/
theorem ubOwnAF_disj (ξ : CtxId) (hf hf' : PAddr → Bool) (A B : List (PAddr × BitVec 8)) :
    ubOwnAF (GF := GF) ξ hf A ∗ ubOwnAF ξ hf' B ⊢
      ⌜∀ a ∈ A.map Prod.fst, ∀ b ∈ B.map Prod.fst, a ≠ b⌝ ∗ ubOwnAF ξ hf A ∗ ubOwnAF ξ hf' B := by
  iintro ⟨HA, HB⟩
  ihave %h : ⌜∀ a ∈ A.map Prod.fst, ∀ b ∈ B.map Prod.fst, a ≠ b⌝ $$ [HA HB]
  · by_cases hx : ∃ a ∈ A.map Prod.fst, ∃ b ∈ B.map Prod.fst, a = b
    · obtain ⟨a, ha, b, hb, rfl⟩ := hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
      obtain ⟨q, hq, hqe⟩ := List.mem_map.1 hb
      unfold ubOwnAF
      icases BigSepL.bigSepL_mem_acc (Φ := fun q : PAddr × BitVec 8 => ctxByte ξ q.1 (ubFr hf q.1) q.2) hp
        $$ HA with ⟨Hp, -⟩
      icases BigSepL.bigSepL_mem_acc (Φ := fun q : PAddr × BitVec 8 => ctxByte ξ q.1 (ubFr hf' q.1) q.2) hq
        $$ HB with ⟨Hq, -⟩
      icases ctxByte_cases_np ξ _ _ _ $$ Hp with ⟨%hnp, %e, %He, Hpt, -, -⟩
      icases ctxByte_cases_np ξ _ _ _ $$ Hq with ⟨%hnp, %e', %He', Hpt', -, -⟩
      ihave %hne := pointsTo_frac_ne (ubFr_op_invalid2 hf hf' p.1 q.1) $$ Hpt Hpt'
      exact (hne hqe.symm).elim
    · ipureintro
      intro a ha b hb e
      exact hx ⟨a, ha, b, hb, e⟩
  iframe HA HB
  ipureintro; exact h

/-- Relabel a list where the two labels agree. -/
theorem ubOwnAF_relabel (ξ : CtxId) (hf hf' : PAddr → Bool) (A : List (PAddr × BitVec 8))
    (h : ∀ p ∈ A, hf p.1 = hf' p.1) : ubOwnAF (GF := GF) ξ hf A ⊣⊢ ubOwnAF ξ hf' A := by
  unfold ubOwnAF
  constructor <;>
  · apply BigSepL.bigSepL_mono
    intro k p hk
    simp only [ubFr, h p (List.mem_of_getElem? hk)]
    exact .rfl

end iris

end MachCSL
