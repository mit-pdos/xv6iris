/-
Weak/Prom: **E-a4: THE LOCK LIFECYCLE ON TRACK (a), DEAD SET EMPTY — PROVED** (stage E-a4; owner ruling [OWN.P14],
context.md item 21; G4-review3.md §5 A-3″, §6 item 1; plan rev 7 §3 "Lock birth and deferred deposits", R-a4, R-a5).

`own_e4`: in every valid run of `t7` — two lifetimes of ONE lock at ONE address: hart 0 kfrees, initlocks
(`sw zero`), initialises and publishes it, waits for both acquirers' done bytes, closes it like `pipeclose`
(xv6's acquire + release — the release a `sw zero` like its births), then kfrees it again (THE DEATH) and
initlocks it again (A SECOND BIRTH at the same address); harts 1 and 2 run xv6's acquire/release around
`ld; addi; sd` in each lifetime — every hart's memory-event trace satisfies `q7`: per critical section, the load
read (every byte) the latest text-shaped field store below the store (1c), and every field load reads a good
store (never the image, never kfree's junk) (4).  Through `adequacyA` at `Dd := fun _ => False`, protocol `π7`.
THE SETUP (per-byte owners from boot): the flag bytes' messages to their slots (publication, done) or `lkJunk`;
the lock word's messages BY AUTHOR (each hart's lock-shaped words: its part, of the empty lifetime born at 0),
its junk (the first one to the death slot of that empty lifetime); the field's and the cpu field's bags; the
shape-only birth slots over every plain zero word at the lock address; one participation one-shot and one claim
token per (hart, round).  0 named inputs; finite runs (S3d separate, [OWN.P4]).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAE4H0

namespace Weak.Prom.OA.E4

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y Z)
open Weak.Prom.OA.P (L1 J SV bSlot dshotD dpendD ownGF4 saveds_alloc dps_alloc filter_nodup)
open Weak.Prom.OA.E
open Weak.Prom.OA.EP (tL1 tL2 isL2O isCO cB)
open Weak.Prom.OA.E2
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

section setup

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]

theorem L2O_nL1 {M : List PMsg} {t : Nat} (h : isL2O M t = true) : tL1 M t = false := by
  simp only [isL2O, Bool.and_eq_true, Bool.not_eq_true'] at h; exact h.2

/-- The initial resources of hart 0 (round 1, the empty lifetime born at 0 behind it). -/
def H0i (g : AGN) (M : List PMsg) (sv : SV) (ek : Nat → Nat → GName) : IProp GF :=
  iprop(([∗list] d ∈ (rng M).filter (isD M 0), dSl g ek 0 d) ∗ dM ek 0 ∗ prt g M sv.tk 0 0 0 ∗
    prt g M sv.tk 1 0 0 ∗ prt g M sv.tk 2 0 0 ∗ ([∗list] t ∈ jB M 0 0, pend g t) ∗ ([∗list] t ∈ cB M 0, pend g t) ∗
    pPts5 g M 0 ∗ dep7 M sv 0 ∗ ([∗list] k' ∈ (List.range 3).filter (fun k' => decide (1 ≤ k')), eP ek 0 k') ∗
    ([∗list] t ∈ tkF M 1 1, token (sv.tk t)) ∗ ([∗list] t ∈ tkF M 2 1, token (sv.tk t)))

/-- The initial resources of acquirer `h`. -/
def Ai (ak ek : Nat → Nat → GName) (h : Nat) : IProp GF :=
  iprop([∗list] k' ∈ (List.range 3).filter (fun k' => decide (1 ≤ k')), eP ek h k' ∗ token (ak h k'))

theorem cut0 (F : Nat → IProp GF) (q : Nat → Bool) (l : List Nat) :
    ([∗list] t ∈ l, F t) ⊢ ([∗list] t ∈ l.filter q, F t) ∗ [∗list] t ∈ l.filter (fun t => !q t), F t :=
  bsl_filter_split F q l

theorem cut (F : Nat → IProp GF) (p q : Nat → Bool) (l : List Nat) :
    ([∗list] t ∈ l.filter p, F t) ⊢ ([∗list] t ∈ l.filter (fun t => p t && q t), F t) ∗
      [∗list] t ∈ l.filter (fun t => p t && !q t), F t :=
  bsl_cut F p q _ _ (fun _ => rfl) (fun _ => rfl) l

/-- A family of one-shots `ek h k'` over the rounds: round 0's, and the rest. -/
theorem ep_split (e : Nat → GName) :
    ([∗list] t ∈ List.range 3, ghost_var (GF := GF) (e t) (.own 1) false) ⊢
      ghost_var (e 0) (.own 1) false ∗ [∗list] k' ∈ (List.range 3).filter (fun k' => decide (1 ≤ k')),
        ghost_var (e k') (.own 1) false := by
  rw [show List.range 3 = [0, 1, 2] from rfl, show List.filter (fun k' => decide (1 ≤ k')) [0, 1, 2] = [1, 2] from rfl]
  iintro H
  icases (BigSepL.bigSepL_cons).1 $$ H with ⟨H0, H⟩
  iframe H0; iexact H

set_option maxHeartbeats 4000000 in
/-- **THE SETUP, PER-BYTE OWNERS** (see the header). -/
theorem setup7 (g : AGN) (M : List PMsg) (hm : g.mn.length = M.length) :
    doomInv (GF := GF) g M ∗ ([∗list] k ↦ _x ∈ g.mn, pend g (k + 1)) ⊢
      |={⊤}=> ∃ sv ak ek, ctx7 g M sv ak ek ∗ H0i g M sv ek ∗ Ai ak ek 1 ∗ Ai ak ek 2 := by
  iintro ⟨#Hdoom, Hp⟩
  have h0 : ([∗list] k ↦ _x ∈ g.mn, pend (GF := GF) g (k + 1)) ⊢ [∗list] t ∈ rng M, pend g t := by
    have := bsl_range (pend (GF := GF) g) g.mn 1; rw [hm] at this; exact this
  ihave Hp := h0 $$ Hp
  imod toks_alloc (GF := GF) (rng M) (nodup_rng M) with ⟨%tk, Ht⟩
  imod saveds_alloc (GF := GF) ((rng M).filter (zw M)) (filter_nodup M _) with ⟨%σ, Hs⟩
  imod dps_alloc (GF := GF) ((rng M).filter (zw M)) (filter_nodup M _) with ⟨%δ, Hd⟩
  imod dps_alloc (GF := GF) (List.range 3) List.nodup_range with ⟨%e0, E0⟩
  imod dps_alloc (GF := GF) (List.range 3) List.nodup_range with ⟨%e1, E1⟩
  imod dps_alloc (GF := GF) (List.range 3) List.nodup_range with ⟨%e2, E2⟩
  imod toks_alloc (GF := GF) (List.range 3) List.nodup_range with ⟨%a1, A1⟩
  imod toks_alloc (GF := GF) (List.range 3) List.nodup_range with ⟨%a2, A2⟩
  let sv : SV := ⟨tk, σ, δ⟩
  let ek : Nat → Nat → GName := fun h => if h = 0 then e0 else if h = 1 then e1 else e2
  let ak : Nat → Nat → GName := fun h => if h = 1 then a1 else a2
  -- the `pend`s: the flag word, the lock word by author, the field, the cpu field
  ihave ⟨HF, HN⟩ := cut0 (pend (GF := GF) g) (tL1 M) (rng M) $$ Hp
  ihave ⟨HF0, HF⟩ := cut (pend (GF := GF) g) (tL1 M) (fB 0 M) (rng M) $$ HF
  ihave ⟨HF1, HF⟩ := cut (pend (GF := GF) g) _ (fB 1 M) (rng M) $$ HF
  ihave ⟨HF2, HFJ⟩ := cut (pend (GF := GF) g) _ (fB 2 M) (rng M) $$ HF
  ihave ⟨HO, HN⟩ := cut (pend (GF := GF) g) _ (isL2O M) (rng M) $$ HN
  ihave ⟨HA, HO⟩ := cut (pend (GF := GF) g) _ (isA2 M) (rng M) $$ HO
  ihave ⟨HR, HJ⟩ := cut (pend (GF := GF) g) _ (isR2 M) (rng M) $$ HO
  ihave ⟨HA0, HA⟩ := cut (pend (GF := GF) g) _ (byH M 0) (rng M) $$ HA
  ihave ⟨HA1, HA2⟩ := cut (pend (GF := GF) g) _ (byH M 1) (rng M) $$ HA
  ihave ⟨HR0, HR⟩ := cut (pend (GF := GF) g) _ (byH M 0) (rng M) $$ HR
  ihave ⟨HR1, HR2⟩ := cut (pend (GF := GF) g) _ (byH M 1) (rng M) $$ HR
  ihave ⟨HC, HN⟩ := cut (pend (GF := GF) g) _ (isCO M) (rng M) $$ HN
  ihave ⟨HP, -⟩ := cut (pend (GF := GF) g) _ (isPO M) (rng M) $$ HN
  -- the tokens: the lock-shaped words by author, the done bytes (hart 0's claims)
  ihave ⟨TF, TN⟩ := cut0 (fun t => token (GF := GF) (tk t)) (tL1 M) (rng M) $$ Ht
  ihave ⟨TF1, TF⟩ := cut (fun t => token (GF := GF) (tk t)) (tL1 M) (fB 1 M) (rng M) $$ TF
  ihave ⟨TF2, -⟩ := cut (fun t => token (GF := GF) (tk t)) _ (fB 2 M) (rng M) $$ TF
  ihave ⟨TL, -⟩ := cut (fun t => token (GF := GF) (tk t)) _ (fun t => isA2 M t || isR2 M t) (rng M) $$ TN
  ihave ⟨TL0, TL⟩ := cut (fun t => token (GF := GF) (tk t)) _ (byH M 0) (rng M) $$ TL
  ihave ⟨TL1, TL2⟩ := cut (fun t => token (GF := GF) (tk t)) _ (byH M 1) (rng M) $$ TL
  -- the junk: the death of the empty lifetime born at 0, and beyond it
  ihave ⟨HD, HJ⟩ := cut (pend (GF := GF) g) _ (noJ M 0) (rng M) $$ HJ
  ihave ⟨E00, E0⟩ := ep_split e0 $$ E0
  ihave ⟨E10, E1⟩ := ep_split e1 $$ E1
  ihave ⟨E20, E2⟩ := ep_split e2 $$ E2
  have c0 : ghost_var (GF := GF) (e0 0) (.own 1) false ∗ ghost_var (e1 0) (.own 1) false ∗
      ghost_var (e2 0) (.own 1) false ⊢ eP ek 0 0 ∗ eP ek 1 0 ∗ eP ek 2 0 := by unfold eP; exact .rfl
  imod dM_alloc (GF := GF) ek 0 $$ [E00 E10 E20] with #HdM
  · iapply c0; iframe E00 E10 E20
  -- the invariants
  imod bsl_fupd (G := fun t => pSl (GF := GF) g M sv ak ek t) (fun t => by
    iintro Hp; unfold pSl; iapply inv_alloc; inext; ileft; iexact Hp) _ $$ HF0 with #HF0
  imod bsl_fupd (G := fun t => nSl (GF := GF) g M sv.tk ek 1 t) (fun t => by
    iintro Hp; unfold nSl; iapply inv_alloc; inext; ileft; iexact Hp) _ $$ HF1 with #HF1
  imod bsl_fupd (G := fun t => nSl (GF := GF) g M sv.tk ek 2 t) (fun t => by
    iintro Hp; unfold nSl; iapply inv_alloc; inext; ileft; iexact Hp) _ $$ HF2 with #HF2
  imod bsl_fupd (G := fun t => lkJunk (GF := GF) g t) (fun t => junk_alloc g t) _ $$ HFJ with #HFJ
  imod bsl_fupd (G := fun d => dSl (GF := GF) g ek 0 d) (fun d => by
    iintro Hp; unfold dSl; iapply inv_alloc; inext; ileft; iexact Hp) _ $$ HD with #HD
  imod bsl_fupd (F := fun t => ghost_var (GF := GF) (δ t) (.own 1) false) (G := fun t => bSlot (GF := GF) M sv t)
    (fun t => by iintro Hp; unfold bSlot; iapply inv_alloc; inext; ileft; unfold dpendD; iexact Hp) _ $$ Hd with #Hbs
  imodintro
  iexists sv; iexists ak; iexists ek
  have mo : ∀ (F : Nat → IProp GF) (p q : Nat → Bool), (∀ t, 1 ≤ t → q t = true → p t = true) →
      ([∗list] t ∈ (rng M).filter p, F t) ⊢ [∗list] t ∈ (rng M).filter q, F t := fun F p q hpq => by
    have : ∀ (l : List Nat), (∀ t ∈ l, 1 ≤ t) → ([∗list] t ∈ l.filter p, F t) ⊢ [∗list] t ∈ l.filter q, F t := by
      intro l hl
      have e : l.filter q = (l.filter p).filter q := by
        rw [List.filter_filter]; exact List.filter_congr (fun t ht => by
          cases hq : q t
          · simp
          · simp [hpq t (hl t ht) hq])
      rw [e]; exact (bsl_filter_split F q _).trans (by iintro ⟨H, -⟩; iexact H)
    exact this (rng M) (fun t ht => rng_ge ht)
  isplitr
  · unfold ctx7
    iframe Hdoom Hbs
    isplitr
    · iapply mo _ _ (fB 0 M) (fun t _ h => by simp [h, fB_L1 (by decide) h]) $$ HF0
    isplitr
    · iapply mo _ _ (fB 1 M) (fun t _ h => by simp [h, fB_L1 (by decide) h, fB_ne (o := 1) (o' := 0) (by decide) h])
        $$ HF1
    isplitr
    · iapply mo _ _ (fB 2 M) (fun t _ h => by
        simp [h, fB_L1 (by decide) h, fB_ne (o := 2) (o' := 0) (by decide) h, fB_ne (o := 2) (o' := 1) (by decide) h])
        $$ HF2
    · iapply mo _ _ (fJ7 M) (fun t _ h => by simp only [fJ7, Bool.and_eq_true, Bool.not_eq_true'] at h; simp [h]) $$ HFJ
  have pA : ∀ h, (∀ t, 1 ≤ t → (decide (0 < t) && decide (t ≠ 0) && isA2 M t && byH M h t) = true →
      (!tL1 M t && isL2O M t && isA2 M t) = true) := fun h t _ ht => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht; simp [ht.1.2, L2O_nL1 (A2_L2O ht.1.2), A2_L2O ht.1.2]
  have pR : ∀ h, (∀ t, 1 ≤ t → (decide (0 < t) && isR2 M t && byH M h t && bey M 0 t) = true →
      (!tL1 M t && isL2O M t && !isA2 M t && isR2 M t) = true) := fun h t _ ht => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    simp [ht.1.1.2, L2O_nL1 (R2_L2O ht.1.1.2), R2_L2O ht.1.1.2, R2_A2 ht.1.1.2]
  have pL : ∀ h, (∀ t, 1 ≤ t → (decide (0 < t) && decide (t ≠ 0) && (isA2 M t || isR2 M t) && byH M h t) = true →
      (!tL1 M t && (isA2 M t || isR2 M t)) = true) := fun h t _ ht => by
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at ht
    rcases ht.1.2 with h1 | h1
    · simp [h1, L2O_nL1 (A2_L2O h1)]
    · simp [h1, L2O_nL1 (R2_L2O h1)]
  have ePk : ∀ (e : Nat → GName) (h : Nat), (∀ k, ek h k = e k) →
      ([∗list] k' ∈ (List.range 3).filter (fun k' => decide (1 ≤ k')), ghost_var (GF := GF) (e k') (.own 1) false) ⊢
        [∗list] k' ∈ (List.range 3).filter (fun k' => decide (1 ≤ k')), eP ek h k' := fun e h he => by
    rw [show List.filter (fun k' => decide (1 ≤ k')) (List.range 3) = [1, 2] from rfl]
    apply BigSepL.bigSepL_mono; intro _ x _; unfold eP; rw [he]
  isplitl [HA0 HA1 HA2 HR0 HR1 HR2 TL0 TL1 TL2 HJ HC HP Hs E0 TF1 TF2]
  · unfold H0i
    iframe HdM
    isplitl []
    · iapply mo (fun d => dSl (GF := GF) g ek 0 d) _ (isD M 0) (fun t _ ht => by
        simp only [isD, inW, isJ2, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ht
        simp [ht, L2O_nL1 ht.2.1.1]) $$ HD
    isplitl [HA0 HR0 TL0]
    · unfold prt obg bgA bgL rB
      isplitl [HA0 TL0]
      · isplitl [HA0]
        · iapply mo _ _ _ (fun t h1 ht => by have := pA 0 t h1 ht; simp at ht this ⊢; simp [this, ht]) $$ HA0
        · iapply mo _ _ _ (fun t h1 ht => by have := pL 0 t h1 ht; simp at ht this ⊢; simp [this, ht]) $$ TL0
      · iapply mo _ _ _ (fun t h1 ht => by have := pR 0 t h1 ht; simp at ht this ⊢; simp [this, ht]) $$ HR0
    isplitl [HA1 HR1 TL1]
    · unfold prt obg bgA bgL rB
      isplitl [HA1 TL1]
      · isplitl [HA1]
        · iapply mo _ _ _ (fun t h1 ht => by
            have := pA 1 t h1 ht; simp at ht this ⊢; simp [this, ht, byH_ne (by decide : 1 ≠ 0) ht.2]) $$ HA1
        · iapply mo _ _ _ (fun t h1 ht => by
            have := pL 1 t h1 ht; simp at ht this ⊢; simp [this, ht, byH_ne (by decide : 1 ≠ 0) ht.2]) $$ TL1
      · iapply mo _ _ _ (fun t h1 ht => by
          have := pR 1 t h1 ht; simp at ht this ⊢; simp [this, ht, byH_ne (by decide : 1 ≠ 0) ht.1.2]) $$ HR1
    isplitl [HA2 HR2 TL2]
    · unfold prt obg bgA bgL rB
      isplitl [HA2 TL2]
      · isplitl [HA2]
        · iapply mo _ _ _ (fun t h1 ht => by
            have := pA 2 t h1 ht; simp at ht this ⊢
            simp [this, byH_ne (by decide : 2 ≠ 0) ht.2, byH_ne (by decide : 2 ≠ 1) ht.2]) $$ HA2
        · iapply mo _ _ _ (fun t h1 ht => by
            have := pL 2 t h1 ht; simp at ht this ⊢
            simp [this, byH_ne (by decide : 2 ≠ 0) ht.2, byH_ne (by decide : 2 ≠ 1) ht.2]) $$ TL2
      · iapply mo _ _ _ (fun t h1 ht => by
          have := pR 2 t h1 ht; simp at ht this ⊢
          simp [this, byH_ne (by decide : 2 ≠ 0) ht.1.2, byH_ne (by decide : 2 ≠ 1) ht.1.2]) $$ HR2
    isplitl [HJ]
    · unfold jB
      iapply mo _ _ _ (fun t h1 ht => by
        have hJ : isJ2 M t = true := by simp only [Bool.and_eq_true] at ht; exact ht.1.2
        have hb : bey M 0 t = true := by simp only [Bool.and_eq_true] at ht; exact ht.2
        simp only [isJ2, Bool.and_eq_true, Bool.not_eq_true'] at hJ
        simp only [bey, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hb
        simp [hJ.1.1, hJ.1.2, hJ.2, hb.2, L2O_nL1 hJ.1.1]) $$ HJ
    isplitl [HC]
    · unfold cB
      iapply mo _ _ _ (fun t h1 ht => by
        have hC : isCO M t = true := by simp only [Bool.and_eq_true] at ht; exact ht.2
        have hC' := hC; simp only [isCO, Bool.and_eq_true, Bool.not_eq_true'] at hC'
        simp [hC, hC'.1.2, isL2O, hC'.2]) $$ HC
    isplitl [HP]
    · unfold pPts5 pB
      iapply mo _ _ _ (fun t h1 ht => by
        have hP : isPO M t = true := by simp only [Bool.and_eq_true] at ht; exact ht.2
        have hP' := hP; simp only [isPO, Bool.and_eq_true, Bool.not_eq_true'] at hP'
        simp [hP, hP'.1.1.2, isL2O, hP'.1.2, hP'.2]) $$ HP
    isplitl [Hs]
    · unfold dep7
      iapply mo (fun t => saved_prop_own (GF := GF) (sv.σ t) (.own 1) iprop(True)) _ _
        (fun t h1 ht => by simp only [Bool.and_eq_true, decide_eq_true_eq] at ht; exact ht.2)
        $$ [Hs]
      rw [show (rng M).filter (zw M) = (rng M).filter (zw M) from rfl]; iexact Hs
    isplitl [E0]
    · iapply ePk e0 0 (fun _ => rfl) $$ E0
    isplitl [TF1]
    · unfold tkF
      iapply mo _ _ _ (fun t h1 ht => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht; simp [ht.1, fB_L1 (by decide) ht.1]) $$ TF1
    · unfold tkF
      iapply mo _ _ _ (fun t h1 ht => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
        simp [ht.1, fB_L1 (by decide) ht.1, fB_ne (o := 2) (o' := 1) (by decide) ht.1]) $$ TF2
  isplitl [E1 A1]
  · unfold Ai
    iapply (BigSepL.bigSepL_sep_eqv_symm).1
    iframe
    isplitl [E1]
    · iapply ePk e1 1 (fun _ => rfl) $$ E1
    · rw [show List.range 3 = [0, 1, 2] from rfl,
        show List.filter (fun k' => decide (1 ≤ k')) [0, 1, 2] = [1, 2] from rfl]
      icases (BigSepL.bigSepL_cons).1 $$ A1 with ⟨-, A1⟩
      iapply BigSepL.bigSepL_mono (Φ := fun _ t => token (GF := GF) (a1 t)) ?_ $$ A1
      intro _ _ _; exact .rfl
  · unfold Ai
    iapply (BigSepL.bigSepL_sep_eqv_symm).1
    isplitl [E2]
    · iapply ePk e2 2 (fun _ => rfl) $$ E2
    · rw [show List.range 3 = [0, 1, 2] from rfl,
        show List.filter (fun k' => decide (1 ≤ k')) [0, 1, 2] = [1, 2] from rfl]
      icases (BigSepL.bigSepL_cons).1 $$ A2 with ⟨-, A2⟩
      iapply BigSepL.bigSepL_mono (Φ := fun _ t => token (GF := GF) (a2 t)) ?_ $$ A2
      intro _ _ _; exact .rfl

end setup

/-! ## The verdict -/

/-- THE ADEQUACY PREMISE at `Dd := fun _ => False` (no dead set). -/
theorem premise7 (M : List PMsg) (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :
    wpPremise .hasLC ownGF4 (xStep xs7) litDone img7 M (progs t7) π7 (fun _ _ => True)
      (fun h => ΨK M (qs7 M h)) (fun _ => False) := by
  intro Hinv g P0 hn hm hdd hP0
  obtain ⟨p0', p1, p2, hps⟩ : ∃ p0 p1 p2 : LP, progs t7 = [p0, p1, p2] := ⟨_, _, _, rfl⟩
  obtain ⟨hpr0, hpc0, hq0, hl0, hrd0⟩ := progs_get (show (progs t7)[0]? = some p0' by rw [hps]; rfl)
  obtain ⟨hpr1, hpc1, hq1, hl1, hrd1⟩ := progs_get (show (progs t7)[1]? = some p1 by rw [hps]; rfl)
  obtain ⟨hpr2, hpc2, hq2, hl2, hrd2⟩ := progs_get (show (progs t7)[2]? = some p2 by rw [hps]; rfl)
  obtain ⟨γ0, γ1, γ2, hgn⟩ : ∃ a b c, g.hn = [a, b, c] := by
    match h : g.hn, (show g.hn.length = 3 by rw [hn, hps]; rfl) with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  rw [hps]
  iintro #Hdoom Hh Hp
  imod setup7 g M hm $$ [Hp] with ⟨%sv, %ak, %ek, #Hctx, H0, Ha1, Ha2⟩
  · iframe Hdoom Hp
  have fI0 : fI psInit := fun a tf vf h => by
    rw [show psInit.wFwd = ∅ from rfl, lookupEmpty] at h; cases h
  have st : ∀ h, hartA (GF := ownGF4) g h psInit (P0 h) [] ⊢ lhA g π7 (w7 M h) (qs7 M h) psInit (P0 h) [] :=
    fun h => lhA_start (GF := ownGF4) (g := g) (π := π7) (w := w7 M h) (Qs := qs7 M) (P0 := P0 h)
      (by by_cases e : h = 0
          · simp only [qs7, if_pos e]; exact noLd_nil
          · simp only [qs7, if_neg e]; exact q7_noLd noLd_nil)
  rw [hgn]
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H0h, Hh⟩
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H1h, Hh⟩
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H2h, -⟩
  imodintro
  iapply (BigSepL.bigSepL_cons).2
  have k0 : ctx7 (GF := ownGF4) g M sv ak ek ∗ H0i g M sv ek ∗ hartA g 0 psInit (P0 0) [] ⊢
      wpA (hlc := .hasLC) g π7 (hw (xStep xs7) litDone img7 M 0) (fun h => ΨK M (qs7 M h)) p0'
        (fun v => iprop(⌜∃ V, grd π7 img7 M V ((fun (_ : Nat) (_ : Unit) => True) 0 v)⌝ ∨ dshot g)) := by
    show _ ⊢ wpKA g π7 (w7 M 0) (qs7 M) p0' (Φ7 g M)
    iintro ⟨#Hc, H0, Hl⟩
    ihave Hr := h0R (GF := ownGF4) g M sv ak ek hdd hnoinv 2 1 rfl (by decide) (by decide)
    unfold H0i
    icases H0 with ⟨HD, HdM, P0', P1, P2, HJ, HC, HP, Hdep, He, T1, T2⟩
    iapply Hr $$ %p0' %psInit %(P0 0) %([] : Trace) %0 %0 %0 %0 %0 %0 %0 %0
      %⟨hpr0, hq0, hpc0, ⟨hl0, by rw [hrd0 9 (by decide) (by decide)]; rfl, by rw [hrd0 11 (by decide) (by decide)]; rfl,
        by rw [hrd0 12 (by decide) (by decide)]; rfl, by rw [hrd0 13 (by decide) (by decide)]; rfl,
        by rw [hrd0 28 (by decide) (by decide)]; rfl⟩, fI0, Nat.le_refl _, Nat.zero_le _, Nat.le_refl _, Nat.zero_le _,
        Nat.le_refl _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
      Hc HD HdM P0' P1 P2 HJ HC HP Hdep He T1 T2 [] [Hl]
    · unfold QE7; ileft; ipureintro; exact ⟨0, grd_intro (by simp only [qs7]; exact noLd_nil)⟩
    · iapply st 0; iexact Hl
  isplitl [H0h H0]
  · iapply k0; iframe Hctx H0 H0h
  have ka : ∀ (h : Nat) (p : LP), (h = 1 ∨ h = 2) → p.prog = bA → p.pc = 0 → p.q = [] → p.regs.length = 32 →
      (∀ r, 0 < r → r < 32 → p.rd r = ((((t7.regs0[h]?).getD []).lookup r).getD 0) % two64) →
      ctx7 (GF := ownGF4) g M sv ak ek ∗ Ai ak ek h ∗ hartA g h psInit (P0 h) [] ⊢
        wpA (hlc := .hasLC) g π7 (hw (xStep xs7) litDone img7 M h) (fun h => ΨK M (qs7 M h)) p
          (fun v => iprop(⌜∃ V, grd π7 img7 M V ((fun (_ : Nat) (_ : Unit) => True) h v)⌝ ∨ dshot g)) :=
    fun h p hh a1 a2 a3 a4 a5 => by
      show _ ⊢ wpKA g π7 (w7 M h) (qs7 M) p (Φ7 g M)
      iintro ⟨#Hc, Ha, Hl⟩
      ihave Hr := acqR (GF := ownGF4) g M sv ak ek h hh hdd hnoinv 2 1 rfl (by decide) (by decide)
      have hrk : RKa h 1 p := by
        rcases hh with rfl | rfl <;>
        exact ⟨a4, by rw [a5 9 (by decide) (by decide)]; rfl, by rw [a5 11 (by decide) (by decide)]; rfl,
          by rw [a5 12 (by decide) (by decide)]; rfl, by rw [a5 13 (by decide) (by decide)]; rfl,
          by rw [a5 16 (by decide) (by decide)]; rfl, by rw [a5 28 (by decide) (by decide)]; rfl⟩
      unfold Ai
      iapply Hr $$ %p %psInit %(P0 h) %([] : Trace) %⟨a1, a3, a2, hrk, fI0⟩ Hc Ha [] [Hl]
      · have : h ≠ 0 := by omega
        unfold QE7; ileft; ipureintro
        exact ⟨0, grd_intro (by simp only [qs7, if_neg this]; exact q7_noLd noLd_nil)⟩
      · iapply st h; iexact Hl
  iapply (BigSepL.bigSepL_cons).2
  isplitl [H1h Ha1]
  · iapply ka 1 p1 (.inl rfl) hpr1 hpc1 hq1 hl1 hrd1; iframe Hctx Ha1 H1h
  iapply (BigSepL.bigSepL_cons).2
  isplitl [H2h Ha2]
  · iapply ka 2 p2 (.inr rfl) hpr2 hpc2 hq2 hl2 hrd2; iframe Hctx Ha2 H2h
  iapply (BigSepL.bigSepL_nil).2
  itrivial

/-- **E-a4: THE LOCK LIFECYCLE ON TRACK (a), DEAD SET EMPTY** (see the header): every hart's memory-event trace of
every valid run of `t7` satisfies `q7` — per critical section mutual exclusion and "the field never reads junk or
the image", across the lock's two lifetimes.  0 named inputs; finite runs (S3d separate, [OWN.P4]). -/
theorem own_e4 (M : List PMsg) (run : PFRun LP Unit)
    (hrun : PF.validRun (xStep xs7) img7 () (progs t7) M run) : ∀ h, q7 M (memEv (run.trace h)) := by
  have hnoinv := x_noInvalT hrun
  obtain ⟨_, hΨ, _⟩ := adequacyA (hlc := .hasLC) (GF := ownGF4) π7 (fun _ _ => True)
    (fun h => ΨK M (qs7 M h)) (fun _ => False) trivial
    (fun h => ⟨by by_cases e : h = 0
                  · simp only [qs7, if_pos e]; exact noLd_nil
                  · simp only [qs7, if_neg e]; exact q7_noLd noLd_nil, wrOk_nil M⟩)
    (premise7 M hnoinv) hrun
  intro h
  have hq := (hΨ h (run.trace h).length).1
  rw [List.take_length] at hq
  by_cases e : h = 0
  · simp only [qs7, if_pos e] at hq; exact q7_noLd hq
  · simpa only [qs7, if_neg e] using hq

#print axioms own_e4

end Weak.Prom.OA.E4
