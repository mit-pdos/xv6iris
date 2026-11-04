/-
Weak/Prom: **E-a2: THE CONTENDED RUNTIME-BORN LOCK ON TRACK (a), DEAD SET EMPTY — PROVED** (stage E-a2; owner ruling
[OWN.P13], context.md item 20; G4-review2.md §6 A-3′; plan rev 7 §4 G4 (1c)+(4), §3 "Lock birth and deferred
deposits", "Acquire", "Atomicity", R-a4, R-a5).

`own_e2`: in every valid run of `t5` — hart 0 runs (4)'s pipealloc text (kfree junk, INITLOCK `sw zero` over the
junk, field init, publication), harts 1 and 2 wait for the publication and then BOTH run (1c)'s xv6
acquire/release text on the lock born at runtime, around `ld; addi; sd` of the field — every hart's trace satisfies
`q5`: (1c)'s mutual exclusion per byte (`qLk3`: the critical section's load read, in every byte, the latest
text-shaped field store of ANY hart below its store) and (4)'s "the field never reads junk or the image" (`qGd`).
Proved through `adequacyA` at `Dd := fun _ => False` (no free mode, no dead invariant), protocol `π4`.
THE SETUP (`setup5`, per-byte owners from boot): the field's, the cpu field's and the L2 word's messages (pend; the
L2 ones with claim tokens; any shape or author) to hart 0; the word at `Z`'s to its slots or `lkJunk`; one boot
token per (hart, timestamp) `ak h t`, each hart its own — the right to claim its part of any lock born at `t`.
0 named inputs; finite runs (S3d separate, [OWN.P4]).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAE2H1

namespace Weak.Prom.OA.E2

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y Z)
open Weak.Prom.OA.P (L1 SV bSlot bth dpendD dep0 ownGF4 saveds_alloc dps_alloc filter_nodup)
open Weak.Prom.OA.E
open Weak.Prom.OA.EP (tL1 tL2 isL2O isCO cB zB zBagE π4 tL1_of)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

section setup

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]

theorem fPub_L1 {M : List PMsg} {t : Nat} (h : fPub M t = true) : tL1 M t = true := by
  obtain ⟨m, hm, hp, hl⟩ := clsB_iff.1 h
  exact tL1_of hm (j := 0) (by decide) (by rw [← hp, byteAt_off rfl, List.getElem?_eq_getElem (by omega)]; rfl)

/-- **THE SETUP, PER-BYTE OWNERS** (see the header). -/
theorem setup5 (g : AGN) (M : List PMsg) (hm : g.mn.length = M.length) :
    doomInv (GF := GF) g M ∗ ([∗list] k ↦ _x ∈ g.mn, pend g (k + 1)) ⊢
      |={⊤}=> ∃ sv ak, ctx5 g M sv ak ∗
        (dep0 M sv ∗ ([∗list] t ∈ cB M 0, pend g t) ∗ pPts5 g M 0 ∗ zBagE g M sv 0 0) ∗
        ([∗list] t ∈ rng M, token (ak 1 t)) ∗ ([∗list] t ∈ rng M, token (ak 2 t)) := by
  iintro ⟨#Hdoom, Hp⟩
  have h0 : ([∗list] k ↦ _x ∈ g.mn, pend (GF := GF) g (k + 1)) ⊢ [∗list] t ∈ rng M, pend g t := by
    have := bsl_range (pend (GF := GF) g) g.mn 1; rw [hm] at this; exact this
  ihave Hp := h0 $$ Hp
  imod toks_alloc (GF := GF) (rng M) (nodup_rng M) with ⟨%tk, Ht⟩
  imod saveds_alloc (GF := GF) ((rng M).filter (bth M)) (filter_nodup M _) with ⟨%σ, Hs⟩
  imod dps_alloc (GF := GF) ((rng M).filter (bth M)) (filter_nodup M _) with ⟨%δ, Hd⟩
  imod toks_alloc (GF := GF) (rng M) (nodup_rng M) with ⟨%a1, Ha1⟩
  imod toks_alloc (GF := GF) (rng M) (nodup_rng M) with ⟨%a2, Ha2⟩
  -- the `pend`s, peeled by owners
  ihave ⟨HC, Hp⟩ := bsl_filter_split (pend (GF := GF) g) (isCO M) (rng M) $$ Hp
  ihave ⟨HP, Hp⟩ := bsl_peel (pend (GF := GF) g) (isPO M) (fun t => !isCO M t)
    (fun t h => by unfold isPO at h; simp only [Bool.and_eq_true, Bool.not_eq_true'] at h; simp [h.2]) (rng M) $$ Hp
  ihave ⟨HZ, Hp⟩ := bsl_peel (pend (GF := GF) g) (isL2O M) (fun t => !isCO M t && !isPO M t)
    (fun t h => by
      unfold isL2O at h; simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      simp [isCO, isPO, h.1]) (rng M) $$ Hp
  ihave ⟨HF, Hp⟩ := bsl_peel (pend (GF := GF) g) (fPub M) (fun t => !isCO M t && !isPO M t && !isL2O M t)
    (fun t h => by simp [isCO, isPO, isL2O, fPub_L1 h]) (rng M) $$ Hp
  ihave ⟨HJ, -⟩ := bsl_peel (pend (GF := GF) g) (fJ M)
    (fun t => !isCO M t && !isPO M t && !isL2O M t && !fPub M t)
    (fun t h => by
      unfold fJ at h; simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      simp [isCO, isPO, isL2O, h.1, h.2]) (rng M) $$ Hp
  ihave ⟨HTZ, -⟩ := bsl_filter_split (fun t => token (GF := GF) (tk t)) (isL2O M) (rng M) $$ Ht
  -- the invariants
  let sv : SV := ⟨tk, σ, δ⟩
  let ak : Nat → Nat → GName := fun h => if h = 1 then a1 else if h = 2 then a2 else tk
  imod bsl_fupd (G := fun t => fSlot5 (GF := GF) g M sv ak t) (fun t => by
    iintro Hp; unfold fSlot5; iapply inv_alloc; inext; ileft; iexact Hp) _ $$ HF with #Hfs
  imod bsl_fupd (G := fun t => lkJunk (GF := GF) g t) (fun t => junk_alloc g t) _ $$ HJ with #Hjs
  imod bsl_fupd (F := fun t => ghost_var (GF := GF) (δ t) (.own 1) false) (G := fun t => bSlot (GF := GF) M sv t)
    (fun t => by iintro Hp; unfold bSlot; iapply inv_alloc; inext; ileft; unfold dpendD; iexact Hp) _ $$ Hd with #Hbs
  imodintro
  iexists sv; iexists ak
  isplitr
  · unfold ctx5; iframe Hdoom Hfs Hjs Hbs
  have ez : zB M 0 0 = (rng M).filter (isL2O M) := by
    unfold zB; refine List.filter_congr (fun t ht => ?_); have := rng_ge ht
    simp [show 0 < t by omega, show t ≠ 0 by omega]
  have ec : cB M 0 = (rng M).filter (isCO M) := by
    unfold cB; refine List.filter_congr (fun t ht => ?_); have := rng_ge ht; simp [show 0 < t by omega]
  have ep : pB M 0 = (rng M).filter (isPO M) := by
    unfold pB; refine List.filter_congr (fun t ht => ?_); have := rng_ge ht; simp [show 0 < t by omega]
  isplitl [Hs HC HP HZ HTZ]
  · unfold dep0 pPts5 zBagE
    rw [ez, ec, ep]
    iframe Hs HC HP HZ HTZ
  isplitl [Ha1]
  · iapply BigSepL.bigSepL_mono (Φ := fun _ t => token (GF := GF) (a1 t)) ?_ $$ Ha1
    intro _ _ _; exact .rfl
  · iapply BigSepL.bigSepL_mono (Φ := fun _ t => token (GF := GF) (a2 t)) ?_ $$ Ha2
    intro _ _ _; exact .rfl

end setup

/-! ## The verdict -/

/-- THE ADEQUACY PREMISE at `Dd := fun _ => False` (no dead set). -/
theorem premise5 (M : List PMsg) (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :
    wpPremise .hasLC ownGF4 (xStep xs5) litDone img5 M (progs t5) π4 (fun _ _ => True)
      (fun h => ΨK M (qs5 M h)) (fun _ => False) := by
  intro Hinv g P0 hn hm hdd hP0
  obtain ⟨p0, p1, p2, hps⟩ : ∃ p0 p1 p2 : LP, progs t5 = [p0, p1, p2] := ⟨_, _, _, rfl⟩
  obtain ⟨hpr0, hpc0, hq0, hl0, hrd0⟩ := progs_get (show (progs t5)[0]? = some p0 by rw [hps]; rfl)
  obtain ⟨hpr1, hpc1, hq1, hl1, hrd1⟩ := progs_get (show (progs t5)[1]? = some p1 by rw [hps]; rfl)
  obtain ⟨hpr2, hpc2, hq2, hl2, hrd2⟩ := progs_get (show (progs t5)[2]? = some p2 by rw [hps]; rfl)
  obtain ⟨γ0, γ1, γ2, hgn⟩ : ∃ a b c, g.hn = [a, b, c] := by
    match h : g.hn, (show g.hn.length = 3 by rw [hn, hps]; rfl) with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  rw [hps]
  iintro #Hdoom Hh Hp
  imod setup5 g M hm $$ [Hp] with ⟨%sv, %ak, #Hctx, ⟨Hdep, Hc, Hpp, Hz⟩, Ha1, Ha2⟩
  · iframe Hdoom Hp
  have k0 := h0_hart5 (GF := ownGF4) g M sv ak p0 (P0 := P0 0) hpr0 hpc0 hq0 hl0
    (by rw [hrd0 9 (by decide) (by decide)]; rfl) (by rw [hrd0 11 (by decide) (by decide)]; rfl)
    (by rw [hrd0 12 (by decide) (by decide)]; rfl)
  have k0' : ctx5 (GF := ownGF4) g M sv ak ∗ dep0 M sv ∗ ([∗list] t ∈ cB M 0, pend g t) ∗ pPts5 g M 0 ∗
      zBagE g M sv 0 0 ∗ lhA g π4 (w5 M 0) (qs5 M 0) psInit (P0 0) [] ⊢
      wpA (hlc := .hasLC) g π4 (hw (xStep xs5) litDone img5 M 0) (fun h => ΨK M (qs5 M h)) p0
        (fun v => iprop(⌜∃ V, grd π4 img5 M V ((fun (_ : Nat) (_ : Unit) => True) 0 v)⌝ ∨ dshot g)) := k0
  have kh : ∀ (h : Nat) (p : LP), h < 3 → h ≠ 0 → p.prog = b5h → p.pc = 0 → p.q = [] → p.regs.length = 32 →
      p.rd 9 = X → p.rd 11 = Y → p.rd 12 = Z →
      ctx5 (GF := ownGF4) g M sv ak ∗ ([∗list] t ∈ rng M, token (ak h t)) ∗
        lhA g π4 (w5 M h) (qs5 M h) psInit (P0 h) [] ⊢
        wpA (hlc := .hasLC) g π4 (hw (xStep xs5) litDone img5 M h) (fun h => ΨK M (qs5 M h)) p
          (fun v => iprop(⌜∃ V, grd π4 img5 M V ((fun (_ : Nat) (_ : Unit) => True) h v)⌝ ∨ dshot g)) :=
    fun h p hh hh0 a1 a2 a3 a4 a5 a6 a7 => by
      show _ ⊢ wpKA g π4 (w5 M h) (qs5 M) p (Φ5 g M)
      iintro ⟨#Hc, Ha, Hl⟩
      ihave Hloop := floop5 (GF := ownGF4) g M sv ak h hh hh0 hdd hnoinv
      iapply Hloop $$ %p %_ %_ %_ %⟨a1, a3, a2, a5, a6, a7, a4⟩ %⟨rfl, noC_nil⟩ Hc Ha Hl
  rw [hgn]
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H0, Hh⟩
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H1, Hh⟩
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H2, -⟩
  imodintro
  have st : ∀ h, hartA (GF := ownGF4) g h psInit (P0 h) [] ⊢ lhA g π4 (w5 M h) (qs5 M h) psInit (P0 h) [] :=
    fun h => lhA_start (GF := ownGF4) (g := g) (π := π4) (w := w5 M h) (Qs := qs5 M) (P0 := P0 h) (q5_noLd noLd_nil)
  iapply (BigSepL.bigSepL_cons).2
  isplitl [H0 Hdep Hc Hpp Hz]
  · iapply k0'; iframe Hctx Hdep Hc Hpp Hz; iapply st 0; iexact H0
  iapply (BigSepL.bigSepL_cons).2
  isplitl [H1 Ha1]
  · iapply kh 1 p1 (by decide) (by decide) hpr1 hpc1 hq1 hl1 (by rw [hrd1 9 (by decide) (by decide)]; rfl)
      (by rw [hrd1 11 (by decide) (by decide)]; rfl) (by rw [hrd1 12 (by decide) (by decide)]; rfl)
    iframe Hctx Ha1; iapply st 1; iexact H1
  iapply (BigSepL.bigSepL_cons).2
  isplitl [H2 Ha2]
  · iapply kh 2 p2 (by decide) (by decide) hpr2 hpc2 hq2 hl2 (by rw [hrd2 9 (by decide) (by decide)]; rfl)
      (by rw [hrd2 11 (by decide) (by decide)]; rfl) (by rw [hrd2 12 (by decide) (by decide)]; rfl)
    iframe Hctx Ha2; iapply st 2; iexact H2
  iapply (BigSepL.bigSepL_nil).2
  itrivial

/-- **E-a2: THE CONTENDED RUNTIME-BORN LOCK ON TRACK (a), DEAD SET EMPTY** (see the header): every hart's trace of
every valid run of `t5` satisfies (1c)'s per-byte mutual exclusion `qLk3` (both acquirers) and (4)'s
"the field never reads junk or the image" `qGd`.  0 named inputs; finite runs (S3d separate, [OWN.P4]). -/
theorem own_e2 (M : List PMsg) (run : PFRun LP Unit)
    (hrun : PF.validRun (xStep xs5) img5 () (progs t5) M run) : ∀ h, q5 M (run.trace h) := by
  have hnoinv := x_noInvalT hrun
  obtain ⟨_, hΨ, _⟩ := adequacyA (hlc := .hasLC) (GF := ownGF4) π4 (fun _ _ => True)
    (fun h => ΨK M (qs5 M h)) (fun _ => False) trivial (fun h => ⟨q5_noLd noLd_nil, wrOk_nil M⟩)
    (premise5 M hnoinv) hrun
  intro h
  have hq := (hΨ h (run.trace h).length).1
  rw [List.take_length] at hq
  exact q5_of_memEv hq

#print axioms own_e2

end Weak.Prom.OA.E2
