/-
Weak/Prom: **E-a: G4 (4) WITH THE DEAD SET EMPTY, PROVED — the pipealloc shape, per-byte owners from boot**
(stage E-a; G4-review.md §6 condition 1; plan rev 7 §4 G4 (4), §3 "Lock birth and deferred deposits", R-a4, R-a5).

`own_pipeE`: the statement of `own_pipe` (OwnAPipe.lean) — every field load of every hart reads hart 0's
initialisation 5 — proved through `adequacyA` at `Dd := fun _ => False` (no free mode, no dead invariant), with the
protocol `π4`.
THE SETUP (`p_setupE`, plan R-a5, per-byte owners): every message touching the field goes to hart 0's points-to of
the field, every message touching the L2 word (not L1) to hart 0's L2 bag with its claim token (hart 0 owns the page
at boot: the junk, the birth, and hart 1's FUTURE acquire AMOs and release — ownership of the word moves to hart 1
through the publication); L1 is the boot lock: hart 1's acquire AMOs to hart 1, hart 0's release words to their
slots (their claim tokens to hart 1), anything else touching L1 to `lkJunk`; the rest stays with the boot owner,
unused.  The saved-proposition birth slots and their deposit one-shots are (4)'s.
0 named inputs; finite runs (S3d separate, [OWN.P4]).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAEPipeH1

namespace Weak.Prom.OA.EP

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y Z)
open Weak.Prom.OA.P (L1 t4 xs4 img4 w4 isK bth bagK SV bSlot dpendD dep0 tk1 q4 qs4 q4_nil ownGF4 saveds_alloc
  dps_alloc filter_nodup bagK0 progs_4 q4_of_memEv)
open Weak.Prom.OA.E
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

section setup

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]

theorem k3_not2 {M : List PMsg} {t : Nat} (h : isK M 3 t = true) : isK M 2 t = false := by
  unfold isK at h ⊢; simp only [decide_eq_true_eq] at h; simp [h]

/-- **THE SETUP OF (4), PER-BYTE OWNERS** (see the header). -/
theorem p_setupE (g : AGN) (M : List PMsg) (hm : g.mn.length = M.length) :
    doomInv (GF := GF) g M ∗ ([∗list] k ↦ _x ∈ g.mn, pend g (k + 1)) ⊢
      |={⊤}=> ∃ sv, pCtxE g M sv ∗ (dep0 M sv ∗ cPtsP g M 0 ∗ zBagE g M sv 0 0) ∗
        (([∗list] t ∈ bagK M 2 0, pend g t) ∗ tk1 M sv) := by
  iintro ⟨#Hdoom, Hp⟩
  have h0 : ([∗list] k ↦ _x ∈ g.mn, pend (GF := GF) g (k + 1)) ⊢ [∗list] t ∈ rng M, pend g t := by
    have := bsl_range (pend (GF := GF) g) g.mn 1; rw [hm] at this; exact this
  ihave Hp := h0 $$ Hp
  imod toks_alloc (GF := GF) (rng M) (nodup_rng M) with ⟨%tk, Ht⟩
  imod saveds_alloc (GF := GF) ((rng M).filter (bth M)) (filter_nodup M _) with ⟨%σ, Hs⟩
  imod dps_alloc (GF := GF) ((rng M).filter (bth M)) (filter_nodup M _) with ⟨%δ, Hd⟩
  have hK : ∀ t, (isK M 2 t = true ∨ isK M 3 t = true) → isCO M t = false ∧ isL2O M t = false := fun t h => by
    have := k23_L1 h; simp [isCO, isL2O, this.1]
  -- the `pend`s, peeled by owners
  ihave ⟨HC, Hp⟩ := bsl_filter_split (pend (GF := GF) g) (isCO M) (rng M) $$ Hp
  ihave ⟨HZ, Hp⟩ := bsl_peel (pend (GF := GF) g) (isL2O M) (fun t => !isCO M t)
    (fun t h => by unfold isL2O at h; simp only [Bool.and_eq_true] at h; simp [isCO, h.1]) (rng M) $$ Hp
  ihave ⟨HA1, Hp⟩ := bsl_peel (pend (GF := GF) g) (isK M 2) (fun t => !isCO M t && !isL2O M t)
    (fun t h => by simp [(hK t (.inl h)).1, (hK t (.inl h)).2]) (rng M) $$ Hp
  ihave ⟨HR1, Hp⟩ := bsl_peel (pend (GF := GF) g) (isK M 3) (fun t => !isCO M t && !isL2O M t && !isK M 2 t)
    (fun t h => by simp [(hK t (.inr h)).1, (hK t (.inr h)).2, k3_not2 h]) (rng M) $$ Hp
  ihave ⟨HJ, -⟩ := bsl_peel (pend (GF := GF) g) (junk1 M)
    (fun t => !isCO M t && !isL2O M t && !isK M 2 t && !isK M 3 t)
    (fun t h => by
      unfold junk1 at h; simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      simp [isCO, isL2O, h.1.1, h.1.2, h.2]) (rng M) $$ Hp
  -- the tokens: L1 releases' (hart 1's claims) and the L2 word's (with its bag)
  ihave ⟨HT3, Ht⟩ := bsl_filter_split (fun t => token (GF := GF) (tk t)) (isK M 3) (rng M) $$ Ht
  ihave HTZ := bsl_filter_mono (fun t => token (GF := GF) (tk t)) _ (isL2O M) (fun t h => by
    cases h3 : isK M 3 t
    · rfl
    · rw [(hK t (.inr h3)).2] at h; cases h) (rng M) $$ Ht
  -- the invariants
  imod bsl_fupd (G := fun t => l1SlotE (GF := GF) g M ⟨tk, σ, δ⟩ t) (fun t => by
    iintro Hp; unfold l1SlotE; iapply inv_alloc; inext; ileft; iexact Hp) _ $$ HR1 with #Hl1
  imod bsl_fupd (G := fun t => lkJunk (GF := GF) g t) (fun t => junk_alloc g t) _ $$ HJ with #Hjs
  imod bsl_fupd (F := fun t => ghost_var (GF := GF) (δ t) (.own 1) false)
    (G := fun t => bSlot (GF := GF) M ⟨tk, σ, δ⟩ t) (fun t => by
    iintro Hp; unfold bSlot; iapply inv_alloc; inext; ileft; unfold dpendD; iexact Hp) _ $$ Hd with #Hbs
  imodintro
  iexists ⟨tk, σ, δ⟩
  isplitr
  · unfold pCtxE; iframe Hdoom Hl1 Hbs Hjs
  have ez : zB M 0 0 = (rng M).filter (isL2O M) := by
    unfold zB; refine List.filter_congr (fun t ht => ?_); have := rng_ge ht
    simp [show 0 < t by omega, show t ≠ 0 by omega]
  have ec : cB M 0 = (rng M).filter (isCO M) := by
    unfold cB; refine List.filter_congr (fun t ht => ?_); have := rng_ge ht; simp [show 0 < t by omega]
  isplitl [Hs HC HZ HTZ]
  · unfold dep0 cPtsP zBagE
    rw [ez, ec]
    iframe Hs HC HZ HTZ
    ipureintro; exact .inl rfl
  · unfold tk1
    rw [bagK0]
    iframe HA1 HT3

end setup

/-! ## The verdict -/

/-- THE ADEQUACY PREMISE at `Dd := fun _ => False` (no dead set). -/
theorem p_premiseE (M : List PMsg) (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :
    wpPremise .hasLC ownGF4 (xStep xs4) litDone img4 M (progs t4) π4 (fun _ _ => True)
      (fun h => ΨK M (qs4 h)) (fun _ => False) := by
  intro Hinv g P0 hn hm hdd hP0
  obtain ⟨p0, p1, hps⟩ := progs_4
  have hg0 : (progs t4)[0]? = some p0 := by rw [hps]; rfl
  have hg1 : (progs t4)[1]? = some p1 := by rw [hps]; rfl
  obtain ⟨hpr0, hpc0, hq0, hl0, hrd0⟩ := progs_get hg0
  obtain ⟨hpr1, hpc1, hq1, hl1, hrd1⟩ := progs_get hg1
  have hlen : g.hn.length = 2 := by rw [hn, hps]; rfl
  obtain ⟨γ0, γ1, hgn⟩ : ∃ a b, g.hn = [a, b] := by
    match h : g.hn, hlen with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  rw [hps]
  iintro #Hdoom Hh Hp
  imod p_setupE g M hm $$ [Hp] with ⟨%sv, #Hctx, ⟨Hdep, Hc, Hz⟩, ⟨HbA, Htk⟩⟩
  · iframe Hdoom Hp
  have k0 := h0_hartE (GF := ownGF4) g M sv p0 (P0 := P0 0) hpr0 hpc0 hq0 hl0
    (by rw [hrd0 9 (by decide) (by decide)]; rfl) (by rw [hrd0 11 (by decide) (by decide)]; rfl)
    (by rw [hrd0 12 (by decide) (by decide)]; rfl)
  have k1 := h1_hartE (GF := ownGF4) g M sv hdd p1 (P0 := P0 1) hpr1 hpc1 hq1 hl1
    (by rw [hrd1 9 (by decide) (by decide)]; rfl) (by rw [hrd1 11 (by decide) (by decide)]; rfl)
    (by rw [hrd1 12 (by decide) (by decide)]; rfl) hnoinv
  have k0' : pCtxE (GF := ownGF4) g M sv ∗ dep0 M sv ∗ cPtsP g M 0 ∗ zBagE g M sv 0 0 ∗
      lhA g π4 (w4 M 0) (qs4 0) psInit (P0 0) [] ⊢
      wpA (hlc := .hasLC) g π4 (hw (xStep xs4) litDone img4 M 0) (fun h => ΨK M (qs4 h)) p0
        (fun v => iprop(⌜∃ V, grd π4 img4 M V ((fun (_ : Nat) (_ : Unit) => True) 0 v)⌝ ∨ dshot g)) := k0
  have k1' : pCtxE (GF := ownGF4) g M sv ∗ ([∗list] t ∈ bagK M 2 0, pend g t) ∗ tk1 M sv ∗
      lhA g π4 (w4 M 1) (qs4 1) psInit (P0 1) [] ⊢
      wpA (hlc := .hasLC) g π4 (hw (xStep xs4) litDone img4 M (0 + 1)) (fun h => ΨK M (qs4 h)) p1
        (fun v => iprop(⌜∃ V, grd π4 img4 M V ((fun (_ : Nat) (_ : Unit) => True) (0 + 1) v)⌝ ∨
          dshot g)) := k1
  rw [hgn]
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H0, Hh⟩
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H1, -⟩
  imodintro
  have s0 := lhA_start (GF := ownGF4) (g := g) (π := π4) (w := w4 M 0) (Qs := qs4) (P0 := P0 0) q4_nil
  have s1 := lhA_start (GF := ownGF4) (g := g) (π := π4) (w := w4 M 1) (Qs := qs4) (P0 := P0 (0 + 1)) q4_nil
  iapply (BigSepL.bigSepL_cons).2
  isplitl [H0 Hdep Hc Hz]
  · iapply k0'
    iframe Hctx Hdep Hc Hz
    iapply s0
    iexact H0
  iapply (BigSepL.bigSepL_cons).2
  isplitl [H1 HbA Htk]
  · iapply k1'
    iframe Hctx HbA Htk
    iapply s1
    iexact H1
  iapply (BigSepL.bigSepL_nil).2
  itrivial

/-- **E-a: G4 TARGET (4) WITH THE DEAD SET EMPTY** — the statement of `own_pipe` (OwnAPipe.lean): every field load
of every hart reads `toBytes 5 8` (never the image, never `kfree`'s junk); proved through `adequacyA` at
`Dd := fun _ => False`, the per-byte owners of OwnAEPipeDefs.lean, the protocol `π4`.  0 named inputs. -/
theorem own_pipeE (M : List PMsg) (run : PFRun LP Unit)
    (hrun : PF.validRun (xStep xs4) img4 () (progs t4) M run) :
    ∀ h, ∀ e ∈ run.trace h, ∀ tvs, isCLd e tvs → tvs.map Prod.snd = toBytes 5 8 := by
  have hnoinv := x_noInvalT hrun
  obtain ⟨_, hΨ, _⟩ := adequacyA (hlc := .hasLC) (GF := ownGF4) π4 (fun _ _ => True)
    (fun h => ΨK M (qs4 h)) (fun _ => False) trivial (fun h => ⟨q4_nil, wrOk_nil M⟩) (p_premiseE M hnoinv) hrun
  intro h
  have hq := (hΨ h (run.trace h).length).1
  rw [List.take_length] at hq
  exact q4_of_memEv hq

#print axioms own_pipeE

end Weak.Prom.OA.EP
