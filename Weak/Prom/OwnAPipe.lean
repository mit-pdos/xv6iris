/-
Weak/Prom: **G4 target (4) on track (a), PROVED: a lock BORN BY PLAIN STORES over junk and PUBLISHED THROUGH ANOTHER
LOCK, with γ allocated at runtime** (stage S4a part 4; plan rev 7 §4 "Gate G4" (4); §3 "Lock birth and deferred
deposits", "The rev-4 design: per-t one-shot saved propositions", R-a4, R-a5).

`own_pipe`: in every valid run of the pipealloc test `t4` (OwnAPipeDefs.lean) on machine v2, every field load of
every hart reads hart 0's initialisation 5 — never the image's 0, never `kfree`'s junk `J`, and not the critical
section's own later store.  Hart 1 reaches the field only through two acquires: L1 (born held by hart 0, released
by a plain release-class store) and L2 (BORN AT RUNTIME by hart 0's plain `sw zero` over junk).

THE SETUP (`p_setup`, plan R-a5: "Pre-allocating |M| invariants, saved-proposition slots and `rOf_t` slots at
adequacy start needs a big-separating-conjunction allocation over an M-indexed family"): one claim token per
timestamp; one SAVED PROPOSITION `σ t ↦ True` and one deposit one-shot per birth-class timestamp (the full saved
proposition to hart 0, the author); the `pend`s by class: the field's to its points-to (hart 0), hart 1's AMO writes
and L2 releases to hart 1, hart 0's L1 releases to their L1 slots, hart 0's L2 words to hart 0, the rest to dead
invariants; the birth slots hold their deposit one-shots.
0 named inputs; the runs are finite (a hart may stop anywhere in a spin loop; the prefix lemma S3d is separate,
[OWN.P4]).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAPipeH0

namespace Weak.Prom.OA.P

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y Z)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

theorem kind_le (m : PMsg) : kind m ≤ 6 := by unfold kind; repeat (first | split | omega)

theorem knd_le (M : List PMsg) (t : Nat) : knd M t ≤ 6 := by
  unfold knd; split
  · exact kind_le _
  · omega

theorem bagK0 (M : List PMsg) (k : Nat) : bagK M k 0 = (rng M).filter (isK M k) := by
  unfold bagK
  refine List.filter_congr (fun t ht => ?_)
  have := rng_ge ht
  simp [show 0 < t by omega]

theorem bagKX0 (M : List PMsg) (k : Nat) : bagKX M k 0 0 = (rng M).filter (isK M k) := by
  unfold bagKX
  refine List.filter_congr (fun t ht => ?_)
  have := rng_ge ht
  simp [show 0 < t by omega, show t ≠ 0 by omega]

section setup

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]

/-- THE SEVEN-CLASS PARTITION of a list of timestamps (by `knd`). -/
theorem bsl_part7 (F : Nat → IProp GF) (M : List PMsg) : ∀ l : List Nat,
    ([∗list] t ∈ l, F t) ⊢ ([∗list] t ∈ l.filter (isK M 0), F t) ∗ ([∗list] t ∈ l.filter (isK M 1), F t) ∗
      ([∗list] t ∈ l.filter (isK M 2), F t) ∗ ([∗list] t ∈ l.filter (isK M 3), F t) ∗
      ([∗list] t ∈ l.filter (isK M 4), F t) ∗ ([∗list] t ∈ l.filter (isK M 5), F t) ∗
      ([∗list] t ∈ l.filter (isK M 6), F t)
  | [] => by
    iintro _
    simp only [List.filter_nil]
    isplitr; · exact BigSepL.bigSepL_nil.2
    isplitr; · exact BigSepL.bigSepL_nil.2
    isplitr; · exact BigSepL.bigSepL_nil.2
    isplitr; · exact BigSepL.bigSepL_nil.2
    isplitr; · exact BigSepL.bigSepL_nil.2
    isplitr; · exact BigSepL.bigSepL_nil.2
    exact BigSepL.bigSepL_nil.2
  | a :: l => by
    have ih := bsl_part7 F M l
    iintro H
    icases (BigSepL.bigSepL_cons).1 $$ H with ⟨Ha, H⟩
    icases ih $$ H with ⟨H0, H1, H2, H3, H4, H5, H6⟩
    have ha := knd_le M a
    rcases (by omega : knd M a = 0 ∨ knd M a = 1 ∨ knd M a = 2 ∨ knd M a = 3 ∨ knd M a = 4 ∨ knd M a = 5 ∨
      knd M a = 6) with h | h | h | h | h | h | h <;>
      simp only [List.filter_cons, isK, h, decide_true, decide_false, if_true, Bool.false_eq_true, if_false,
        show ¬ ((0 : Nat) = 1) by decide, show ¬ ((0 : Nat) = 2) by decide, show ¬ ((0 : Nat) = 3) by decide,
        show ¬ ((0 : Nat) = 4) by decide, show ¬ ((0 : Nat) = 5) by decide, show ¬ ((0 : Nat) = 6) by decide,
        show ¬ ((1 : Nat) = 0) by decide, show ¬ ((1 : Nat) = 2) by decide, show ¬ ((1 : Nat) = 3) by decide,
        show ¬ ((1 : Nat) = 4) by decide, show ¬ ((1 : Nat) = 5) by decide, show ¬ ((1 : Nat) = 6) by decide,
        show ¬ ((2 : Nat) = 0) by decide, show ¬ ((2 : Nat) = 1) by decide, show ¬ ((2 : Nat) = 3) by decide,
        show ¬ ((2 : Nat) = 4) by decide, show ¬ ((2 : Nat) = 5) by decide, show ¬ ((2 : Nat) = 6) by decide,
        show ¬ ((3 : Nat) = 0) by decide, show ¬ ((3 : Nat) = 1) by decide, show ¬ ((3 : Nat) = 2) by decide,
        show ¬ ((3 : Nat) = 4) by decide, show ¬ ((3 : Nat) = 5) by decide, show ¬ ((3 : Nat) = 6) by decide,
        show ¬ ((4 : Nat) = 0) by decide, show ¬ ((4 : Nat) = 1) by decide, show ¬ ((4 : Nat) = 2) by decide,
        show ¬ ((4 : Nat) = 3) by decide, show ¬ ((4 : Nat) = 5) by decide, show ¬ ((4 : Nat) = 6) by decide,
        show ¬ ((5 : Nat) = 0) by decide, show ¬ ((5 : Nat) = 1) by decide, show ¬ ((5 : Nat) = 2) by decide,
        show ¬ ((5 : Nat) = 3) by decide, show ¬ ((5 : Nat) = 4) by decide, show ¬ ((5 : Nat) = 6) by decide,
        show ¬ ((6 : Nat) = 0) by decide, show ¬ ((6 : Nat) = 1) by decide, show ¬ ((6 : Nat) = 2) by decide,
        show ¬ ((6 : Nat) = 3) by decide, show ¬ ((6 : Nat) = 4) by decide, show ¬ ((6 : Nat) = 5) by decide]
    · iframe H1 H2 H3 H4 H5 H6; iapply (BigSepL.bigSepL_cons).2; iframe Ha H0
    · iframe H0 H2 H3 H4 H5 H6; iapply (BigSepL.bigSepL_cons).2; iframe Ha H1
    · iframe H0 H1 H3 H4 H5 H6; iapply (BigSepL.bigSepL_cons).2; iframe Ha H2
    · iframe H0 H1 H2 H4 H5 H6; iapply (BigSepL.bigSepL_cons).2; iframe Ha H3
    · iframe H0 H1 H2 H3 H5 H6; iapply (BigSepL.bigSepL_cons).2; iframe Ha H4
    · iframe H0 H1 H2 H3 H4 H6; iapply (BigSepL.bigSepL_cons).2; iframe Ha H5
    · iframe H0 H1 H2 H3 H4 H5; iapply (BigSepL.bigSepL_cons).2; iframe Ha H6

/-- One full saved proposition `True` per element (plan R-a5, σ_t). -/
theorem saveds_alloc : ∀ (l : List Nat), l.Nodup →
    ⊢@{IProp GF} |==> ∃ σ : Nat → GName, [∗list] t ∈ l, saved_prop_own (σ t) (.own 1) iprop(True)
  | [], _ => by
    iapply bupd_intro
    iexists (fun _ => 0)
    exact BigSepL.bigSepL_nil.2
  | a :: l, hnd => by
    have ih := saveds_alloc l (List.nodup_cons.1 hnd).2
    iintro
    imod saved_prop_alloc (GF := GF) iprop(True) (.own 1) DFrac.valid_own_one with ⟨%γ, Hγ⟩
    imod ih with ⟨%σ', Hl⟩
    imodintro
    iexists (fun t => if t = a then γ else σ' t)
    iapply (BigSepL.bigSepL_cons).2
    isplitl [Hγ]
    · simp only [if_true]; iexact Hγ
    · iapply BigSepL.bigSepL_mono (Φ := fun _ t => saved_prop_own (σ' t) (.own 1) iprop(True)) ?_ $$ Hl
      intro k x hx
      have hxa : x ≠ a := fun e => (List.nodup_cons.1 hnd).1 (e ▸ List.mem_of_getElem? hx)
      simp only [if_neg hxa]; exact .rfl

/-- One deposit one-shot per element (plan §3 `deposited_t`). -/
theorem dps_alloc : ∀ (l : List Nat), l.Nodup →
    ⊢@{IProp GF} |==> ∃ δ : Nat → GName, [∗list] t ∈ l, ghost_var (δ t) (.own 1) false
  | [], _ => by
    iapply bupd_intro
    iexists (fun _ => 0)
    exact BigSepL.bigSepL_nil.2
  | a :: l, hnd => by
    have ih := dps_alloc l (List.nodup_cons.1 hnd).2
    iintro
    imod ghost_var_alloc (GF := GF) false with ⟨%γ, Hγ⟩
    imod ih with ⟨%δ', Hl⟩
    imodintro
    iexists (fun t => if t = a then γ else δ' t)
    iapply (BigSepL.bigSepL_cons).2
    isplitl [Hγ]
    · simp only [if_true]; iexact Hγ
    · iapply BigSepL.bigSepL_mono (Φ := fun _ t => ghost_var (GF := GF) (δ' t) (.own 1) false) ?_ $$ Hl
      intro k x hx
      have hxa : x ≠ a := fun e => (List.nodup_cons.1 hnd).1 (e ▸ List.mem_of_getElem? hx)
      simp only [if_neg hxa]; exact .rfl

theorem filter_nodup (M : List PMsg) (p : Nat → Bool) : ((rng M).filter p).Nodup :=
  (nodup_rng M).filter p

/-- **THE SETUP** of (4) (see the header). -/
theorem p_setup (g : AGN) (M : List PMsg) (hm : g.mn.length = M.length) :
    doomInv (GF := GF) g M ∗ ([∗list] k ↦ _x ∈ g.mn, pend g (k + 1)) ⊢
      |={⊤}=> ∃ sv, pCtx g M sv ∗
        (dep0 M sv ∗ cPts g M 0 ∗ zBag g M 0) ∗
        (([∗list] t ∈ bagK M 2 0, pend g t) ∗ tk1 M sv ∗ ob2 g M sv 0 0 ∗ r2Bag g M) := by
  iintro ⟨#Hdoom, Hp⟩
  have h0 : ([∗list] k ↦ _x ∈ g.mn, pend (GF := GF) g (k + 1)) ⊢ [∗list] t ∈ rng M, pend g t := by
    have := bsl_range (pend (GF := GF) g) g.mn 1; rw [hm] at this; exact this
  ihave Hp := h0 $$ Hp
  imod toks_alloc (GF := GF) (rng M) (nodup_rng M) with ⟨%tk, Ht⟩
  imod saveds_alloc (GF := GF) ((rng M).filter (bth M)) (filter_nodup M _) with ⟨%σ, Hs⟩
  imod dps_alloc (GF := GF) ((rng M).filter (bth M)) (filter_nodup M _) with ⟨%δ, Hd⟩
  icases bsl_part7 (pend g) M (rng M) $$ Hp with ⟨HD, HC, HA1, HR1, HA2, HR2, HZ⟩
  -- tokens: hart 1's L1 claims (class 3) and its L2 AMO writes (class 4)
  icases bsl_part7 (fun t => token (GF := GF) (tk t)) M (rng M) $$ Ht with ⟨-, -, -, HT3, HT4, -, -⟩
  -- the invariants
  imod bsl_fupd (G := fun t => l1Slot (GF := GF) g M ⟨tk, σ, δ⟩ t) (fun t => by
    iintro Hp; unfold l1Slot; iapply inv_alloc; inext; ileft; iexact Hp) _ $$ HR1 with #Hl1
  imod bsl_fupd (G := fun t => deadInv (GF := GF) g t) (fun t => dead_alloc g t) _ $$ HD with #Hdd
  imod bsl_fupd (F := fun t => ghost_var (GF := GF) (δ t) (.own 1) false)
    (G := fun t => bSlot (GF := GF) M ⟨tk, σ, δ⟩ t) (fun t => by
    iintro Hp; unfold bSlot; iapply inv_alloc; inext; ileft; unfold dpendD; iexact Hp) _ $$ Hd with #Hbs
  imodintro
  iexists ⟨tk, σ, δ⟩
  isplitr
  · unfold pCtx; iframe Hdoom Hl1 Hbs Hdd
  isplitl [Hs HC HZ]
  · unfold dep0 cPts zBag
    rw [cBag_K, bagK0, bagK0]
    iframe Hs HC HZ
    ipureintro; exact .inl rfl
  · unfold tk1 ob2 r2Bag
    rw [bagK0, bagK0, bagKX0]
    iframe HA1 HT3 HA2 HT4 HR2

end setup

/-! ## The verdict -/

theorem progs_4 : ∃ p0 p1 : LP, progs t4 = [p0, p1] := ⟨_, _, rfl⟩

/-- THE ADEQUACY PREMISE for (4). -/
theorem p_premise (M : List PMsg)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a := by assumption) :   -- [rebase-repair] MachFix-R-b5: `vi = 0`
    wpPremise .hasLC ownGF4 (xStep xs4) litDone img4 M (progs t4) Proto.triv (fun _ _ => True)
      (fun h => ΨK M (qs4 h)) (dd4 M) := by
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
  imod p_setup g M hm $$ [Hp] with ⟨%sv, #Hctx, ⟨Hdep, Hc, Hz⟩, ⟨HbA, Htk, Hob, Hr2⟩⟩
  · iframe Hdoom Hp
  have k0 := h0_hart (GF := ownGF4) g M sv p0 (P0 := P0 0) hpr0 hpc0 hq0 hl0
    (by rw [hrd0 9 (by decide) (by decide)]; rfl) (by rw [hrd0 11 (by decide) (by decide)]; rfl)
    (by rw [hrd0 12 (by decide) (by decide)]; rfl)
  have k1 := h1_hart (GF := ownGF4) g M sv hdd p1 (P0 := P0 1) hpr1 hpc1 hq1 hl1
    (by rw [hrd1 9 (by decide) (by decide)]; rfl) (by rw [hrd1 11 (by decide) (by decide)]; rfl)
    (by rw [hrd1 12 (by decide) (by decide)]; rfl)
  have k0' : pCtx (GF := ownGF4) g M sv ∗ dep0 M sv ∗ cPts g M 0 ∗ zBag g M 0 ∗
      lhA g Proto.triv (w4 M 0) (qs4 0) psInit (P0 0) [] ⊢
      wpA (hlc := .hasLC) g Proto.triv (hw (xStep xs4) litDone img4 M 0) (fun h => ΨK M (qs4 h)) p0
        (fun v => iprop(⌜∃ V, grd Proto.triv img4 M V ((fun (_ : Nat) (_ : Unit) => True) 0 v)⌝ ∨ dshot g)) := k0
  have k1' : pCtx (GF := ownGF4) g M sv ∗ ([∗list] t ∈ bagK M 2 0, pend g t) ∗ tk1 M sv ∗ ob2 g M sv 0 0 ∗
      r2Bag g M ∗ lhA g Proto.triv (w4 M 1) (qs4 1) psInit (P0 1) [] ⊢
      wpA (hlc := .hasLC) g Proto.triv (hw (xStep xs4) litDone img4 M (0 + 1)) (fun h => ΨK M (qs4 h)) p1
        (fun v => iprop(⌜∃ V, grd Proto.triv img4 M V ((fun (_ : Nat) (_ : Unit) => True) (0 + 1) v)⌝ ∨
          dshot g)) := k1
  rw [hgn]
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H0, Hh⟩
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H1, -⟩
  imodintro
  have s0 := lhA_start (GF := ownGF4) (g := g) (π := Proto.triv) (w := w4 M 0) (Qs := qs4) (P0 := P0 0) q4_nil
  have s1 := lhA_start (GF := ownGF4) (g := g) (π := Proto.triv) (w := w4 M 1) (Qs := qs4) (P0 := P0 (0 + 1))
    q4_nil
  iapply (BigSepL.bigSepL_cons).2
  isplitl [H0 Hdep Hc Hz]
  · iapply k0'
    iframe Hctx Hdep Hc Hz
    iapply s0
    iexact H0
  iapply (BigSepL.bigSepL_cons).2
  isplitl [H1 HbA Htk Hob Hr2]
  · iapply k1'
    iframe Hctx HbA Htk Hob Hr2
    iapply s1
    iexact H1
  iapply (BigSepL.bigSepL_nil).2
  itrivial

theorem q4_of_memEv {τ : Trace} (h : q4 (memEv τ)) : q4 τ := by
  intro e he tvs hl
  refine h e (List.mem_filter.2 ⟨he, ?_⟩) tvs hl
  obtain ⟨_, rfl⟩ := hl; rfl

/-- **G4 TARGET (4) ON TRACK (a): A LOCK BORN BY PLAIN STORES OVER JUNK, PUBLISHED THROUGH ANOTHER LOCK, ITS
GHOST NAME ALLOCATED AT RUNTIME** (plan §4 G4 (4); see the header).  Over every final memory `M` and every valid run
of machine v2 of the pipealloc test `t4` (hart 0: `li t1,J; sw t1,0(s1); sd t1,0(a1); sw zero,0(s1); li t2,5;
sd t2,0(a1); fence rw,w; sw zero,0(a2)`; hart 1: xv6's acquire of L1, xv6's acquire of L2,
`ld t2,(a1); addi t2,t2,1; sd t2,(a1)`, xv6's release of L2), every field load of every hart's trace reads
`toBytes 5 8` — hart 0's initialisation, not the image, not the junk.  The proof moves the field's points-to from
hart 0 into L2's pre-allocated SAVED-PROPOSITION slot at hart 0's next release-class write (the DEFERRED DEPOSIT of
the plain birth), naming the lock's runtime ghost name `γ`; the handle reaches hart 1 through L1's release slot;
hart 1's L2 read lies above the birth (R-a4) and its AMO, the first L2 write after the birth, claims the slot.
0 named inputs; finite runs (the prefix lemma S3d is separate, [OWN.P4]). -/
theorem own_pipe (M : List PMsg) (run : PFRun LP Unit)
    (hrun : PF.validRun (xStep xs4) img4 () (progs t4) M run) :
    ∀ h, ∀ e ∈ run.trace h, ∀ tvs, isCLd e tvs → tvs.map Prod.snd = toBytes 5 8 := by
  have hnoinv := x_noInvalT hrun   -- [rebase-repair] MachFix-R-b5: the front end issues no CMO (`vi = 0`)
  obtain ⟨_, hΨ, _⟩ := adequacyA (hlc := .hasLC) (GF := ownGF4) Proto.triv (fun _ _ => True)
    (fun h => ΨK M (qs4 h)) (dd4 M) trivial (fun h => ⟨q4_nil, wrOk_nil M⟩) (p_premise M) hrun
  intro h
  have hq := (hΨ h (run.trace h).length).1
  rw [List.take_length] at hq
  exact q4_of_memEv hq

#print axioms own_pipe

end Weak.Prom.OA.P
