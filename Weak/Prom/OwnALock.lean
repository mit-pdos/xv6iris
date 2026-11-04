/-
Weak/Prom: **G4 target (1a) on track (a): THE SPINLOCK WITH A MUTUAL-EXCLUSION CLIENT, proved** (stage S4a part 2;
plan rev 7 §4 G4 (1a): the manual's Example 1, mm-explanatory.adoc:700–712; §3 "Acquire", "Atomicity", "The
deposit", "Opening", R-a1).

`own_lock1a`: in every valid run of two harts running `p1a` (OwnALockDefs.lean) on machine v2 through the loop front
end (OwnAFront.lean), each hart's trace satisfies `qLk`: if it has a counter load and a counter store at `ts`, every
byte of the load was read from the LATEST counter message below `ts` (or the image) — no counter write of anybody
lies between the critical section's read and its write.  `own_lock1a_excl`: hence two harts' critical sections are
ordered — the later store's critical section read a counter message at or after the earlier store.

The proof (one Löb induction per hart over the spin loop, OwnALock.lean `lk_loop`):
* the acquiring AMO at `ts` fulfils its own acquire message (its `pend` is in the hart's own-message bag);
* at the next step the frontier covers `ts` (aq: `vwNew ≥ ts`), and `lk_acq` (OwnALockAcq.lean) shows the AMO read
  `1` (held: loop) or `0` and CLAIMS `Rs s0` from the slot of its read source `s0` (the image or a release), whose
  claim token is the token of `nxtL M s0 = ts` — the AMO whose read source is `s0` is unique (`exclOk`);
* the critical section and the release (OwnALockCS.lean): the owned read, the store moving the counter's points-to,
  the release-class AMO depositing `Rs r` into release `r`'s slot;
* a read of a dead message puts the run in FREE MODE (OwnALockFree.lean).
Setup (`lk_setup`, plan R-a5): every message's `pend` and a token per message, classified by content.
0 named inputs.  The runs are finite (plan §4: the G4 statements are over finite runs; a hart may stop anywhere in
its spin loop; the prefix lemma S3d is separate, [OWN.P4]).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnALockAcq
import Weak.Prom.OwnAMP

namespace Weak.Prom.OA

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

section loop

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- The hart's state at the loop head. -/
def lhS (s : LP) : Prop :=
  s.prog = b1a ∧ s.q = [] ∧ s.pc = 1 ∧ s.rd 5 = 1 ∧ s.rd 10 = X ∧ s.rd 11 = Y ∧ s.regs.length = 32

/-- **THE SPIN LOOP** (Löb induction at the loop head `again:`). -/
theorem lk_loop (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2) (hdd : g.dd = ddL M)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a := by assumption) :   -- MachFix-R-b5: `vi = 0`
    ⊢ ∀ (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo : Nat), ⌜lhS s⌝ -∗
      ⌜lo ≤ coh ws Lk ∧ noC ev⌝ -∗ lkCtx (GF := GF) g M tk -∗ obag g M tk h lo 0 -∗
      lhA g Proto.triv (wL M h) (qsLk M h) ws pr ev -∗ wpKA g Proto.triv (wL M h) (qsLk M) s (ΦL g M) := by
  have hw := litW_x xs1a imgL M h
  iloeb as IH
  iintro %s %ws %pr %ev %lo %hs %hl0 #Hctx Hbag Hl
  obtain ⟨hprog, hq, hpc, h5, h10, h11, hlen⟩ := hs
  obtain ⟨hlo, hnoC⟩ := hl0
  have hX := p1a_at hprog
  iapply (wpKA_amo (base := Lk) hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
    (by rw [h10]; decide) (by rw [h10]))
  iframe Hl
  inext
  iintro %tvs %ts %hlen4 %_ %hmsg %hlo1 %hex %hcoh %_ _ _
  have hd1 : amoD .swap 4 (s.rd 5) tvs = toBytes 1 4 := by rw [amoD_swap, h5]
  have hlenD : (amoD .swap 4 (s.rd 5) tvs).length = 4 := by rw [hd1]; rfl
  rw [hd1] at hmsg
  rw [hlenD] at hcoh
  have hcohB : ∀ j : Nat, j < 4 → coh (loadRun ws true false (srcsView ws (srcR 10)) Lk tvs) (Lk + j) < ts :=
    fun j hj => cohBelow_at hcoh hj
  have hc0 : coh (loadRun ws true false (srcsView ws (srcR 10)) Lk tvs) Lk < ts := by
    simpa using hcohB 0 (by decide)
  have hcm := (loadRun_mono ws true false (srcsView ws (srcR 10)) Lk tvs).2.2.2.2.2.2.2.2.2.2.1 Lk
  have hts1 : 1 ≤ ts := by omega
  obtain ⟨hA, hbyH⟩ := isA_of_msg hh hts1 hmsg
  have hmt : msgAt M ts = some ⟨Lk, toBytes 1 4, some h, .excl⟩ := by
    obtain ⟨k, rfl⟩ : ∃ k, ts = k + 1 := ⟨ts - 1, by omega⟩
    simpa [msgAt] using hmsg
  have htsM := msgAt_le hmt
  have hlots : lo < ts := by omega
  -- the acquire message's `pend` and token
  unfold obag
  icases Hbag with ⟨HbA, HbL⟩
  unfold bagA
  icases bsl_filter_take (pend g) (fun t => decide (lo < t) && decide (t ≠ 0) && isA M t && byH M h t)
    (fun t => decide (lo < t) && decide (t ≠ ts) && isA M t && byH M h t) ts (by simp [hlots, hA, hbyH]; omega)
    (fun t ht => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
      exact ⟨⟨⟨⟨ht.1.1.1, by omega⟩, ht.1.2⟩, ht.2⟩, ht.1.1.2⟩) (rng M) (mem_rng.2 htsM) (nodup_rng M)
    $$ HbA with ⟨Hp, HbA⟩
  unfold bagL
  icases bsl_filter_take (fun t => token (tk t))
    (fun t => decide (lo < t) && decide (t ≠ 0) && (isA M t || isR M t) && byH M h t)
    (fun t => decide (lo < t) && decide (t ≠ ts) && (isA M t || isR M t) && byH M h t) ts
    (by simp [hlots, hA, hbyH]; omega)
    (fun t ht => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
      exact ⟨⟨⟨⟨ht.1.1.1, by omega⟩, ht.1.2⟩, ht.2⟩, ht.1.1.2⟩) (rng M) (mem_rng.2 htsM) (nodup_rng M)
    $$ HbL with ⟨Ht, HbL⟩
  imod shoot $$ Hp with #Hsh
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨⟨0, grd_intro (qLk_noC (noC_snoc hnoC (rmw_nonC _ _ _ _ _ _ _)))⟩, grd_intro trivial⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s1 %hs1 #Hfr _
  -- the frontier covers `ts` (aq: `vwNew ≥ ts`)
  have hts_f : ts ≤ wfr (qPosts (amoPost (storeRun (loadRun ws true false (srcsView ws (srcR 10)) Lk tvs) false
      (srcsView ws (srcR 10)) ts Lk (amoD .swap 4 (s.rd 5) tvs).length ts) true ts)
      (regWL 5 [.DLdRes] ++ [LInstr]).dropLast) := by
    show ts ≤ stFloor _
    unfold stFloor
    simp only [regWL, show (5 : Nat) ≠ 0 by decide, if_false, List.singleton_append, List.dropLast, qPosts, qPost,
      regWP_vwNew, amoPost_vwNew, if_true]
    omega
  have hsrc : bytesAll (fun x u _ => u ≤ coh (loadRun ws true false (srcsView ws (srcR 10)) Lk tvs) x) Lk tvs :=
    bytesAll_mono (fun _ _ _ hh => hh.2) _ _
      (loadBytes_coh true (ldPre ws true false (srcsView ws (srcR 10))) ws Lk tvs).2
  have hwts : wrB M Lk ts := by
    refine ⟨_, hmt, ?_⟩
    have := byteAt_off (m := ⟨Lk, toBytes 1 4, some h, .excl⟩) (p := Lk) (k := 0) rfl
    rw [show Lk + ((0 : Nat) : Int) = Lk by simp] at this
    rw [this]; rfl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e10 : s1.rd 10 = X := by rw [LPstep_rd hs1 10 (.inl (by decide)), h10]
  have e11 : s1.rd 11 = Y := by rw [LPstep_rd hs1 11 (.inl (by decide)), h11]
  have hlen1 : s1.regs.length = 32 := hs1.2.2.2.1.trans hlen
  have e5 := LPstep_rd_eq hs1 (by decide) (by omega)
  have hcs0 := storeRun_coh0 (loadRun ws true false (srcsView ws (srcR 10)) Lk tvs) false (srcsView ws (srcR 10))
    ts Lk (amoD .swap 4 (s.rd 5) tvs).length ts (by rw [hlenD]; decide)
  have hcs : ts ≤ coh (instrR (ctrlP (qPosts (amoPost (storeRun (loadRun ws true false (srcsView ws (srcR 10)) Lk tvs)
      false (srcsView ws (srcR 10)) ts Lk (amoD .swap 4 (s.rd 5) tvs).length ts) true ts)
      (regWL 5 [.DLdRes] ++ [LInstr])) (srcR 5 ++ srcR 0))) Lk := hcs0
  imod lk_acq g M tk h hdd (π := Proto.triv) (ws := ws) hlen4 hlo1 hex hsrc hcohB hlo hts_f hwts
    $$ [HbA HbL Ht] with (⟨#Hf, #Hd⟩ | ⟨Hbag, %hv⟩ | ⟨Hbag, %hv, %lw, %hlw, Hc⟩)
  · iframe Hctx Hfr Ht; unfold obag bagA bagL; iframe HbA HbL
  all_goals imodintro
  all_goals iintro Hl
  · -- free mode
    ihave Hfree := lk_free (GF := GF) g M h hh hdd
    have hfr : frS s1 := ⟨hP1, hq1, by rw [hc1]; decide, by rw [hc1]; decide, e10, e11⟩
    iapply Hfree $$ %s1 %_ %_ %_ %hfr Hf Hd Hl
  · -- held: back to the loop head
    have e5' : s1.rd 5 = 1 := by rw [e5, hv]; decide
    iapply (wpKA_brx (Xs := xs1a) hw (xAg_x xs1a imgL M h s1) hq1 (p1a_at hP1) (by rw [hc1]; rfl)
      (by rw [hP1]; decide))
    iframe Hl
    inext
    iintro %s2 %hs2 _ _
    imodintro
    iintro Hl
    have hbr : (if Weak.Prom.Ref.brEval .ne (s1.rd 5) (s1.rd 0) then 1 else s1.pc + 1) = 1 := by
      rw [e5']; rfl
    rw [hbr] at hs2
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 rfl
    have hls : lhS s2 := ⟨hP2, hq2, hc2, by rw [LPstep_rd hs2 5 (.inr rfl), e5'],
      by rw [LPstep_rd hs2 10 (.inr rfl), e10], by rw [LPstep_rd hs2 11 (.inr rfl), e11],
      hs2.2.2.2.1.trans hlen1⟩
    iapply IH $$ %s2 %_ %_ %_ %ts %hls %⟨hcs, noC_snoc hnoC (rmw_nonC _ _ _ _ _ _ _)⟩ Hctx [Hbag] Hl
    unfold obag bagA bagL
    icases Hbag with ⟨HbA, HbL⟩
    isplitl [HbA]
    · iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
        exact ⟨⟨⟨by omega, by omega⟩, ht.1.2⟩, ht.2⟩) (rng M) $$ HbA
    · iapply bsl_filter_mono (fun t => token (tk t)) _ _ (fun t ht => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
        exact ⟨⟨⟨by omega, by omega⟩, ht.1.2⟩, ht.2⟩) (rng M) $$ HbL
  · -- acquired: the critical section
    have e5' : s1.rd 5 = 0 := by rw [e5, hv]; decide
    iapply (wpKA_brx (Xs := xs1a) hw (xAg_x xs1a imgL M h s1) hq1 (p1a_at hP1) (by rw [hc1]; rfl)
      (by rw [hP1]; decide))
    iframe Hl
    inext
    iintro %s2 %hs2 _ _
    imodintro
    iintro Hl
    have hbr : (if Weak.Prom.Ref.brEval .ne (s1.rd 5) (s1.rd 0) then 1 else s1.pc + 1) = 3 := by
      rw [e5', hc1]; rfl
    rw [hbr] at hs2
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 rfl
    have hvr : lw ≤ (instrR (ctrlP (qPosts (amoPost (storeRun (loadRun ws true false (srcsView ws (srcR 10)) Lk tvs)
        false (srcsView ws (srcR 10)) ts Lk (amoD .swap 4 (s.rd 5) tvs).length ts) true ts) (regWL 5 [.DLdRes] ++ [LInstr]))
        (srcR 5 ++ srcR 0))).wVrNew := by
      simp only [regWL, show (5 : Nat) ≠ 0 by decide, if_false, List.singleton_append, qPosts, qPost,
        instrR_vrNew, ctrlP_vrNew, regWP_vrNew, amoPost_vrNew, if_true]
      omega
    iapply (lk_cs g M tk h hh hdd s2 _ _ _ ts lw
      ⟨hP2, hq2, hc2, by rw [LPstep_rd hs2 10 (.inr rfl), e10], by rw [LPstep_rd hs2 11 (.inr rfl), e11]⟩
      hcs hvr (noC_snoc hnoC (rmw_nonC _ _ _ _ _ _ _)))
    iframe Hctx Hc Hl
    unfold obag bagA bagL
    icases Hbag with ⟨HbA, HbL⟩
    isplitl [HbA]
    · iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
        exact ⟨⟨⟨by omega, by omega⟩, ht.1.2⟩, ht.2⟩) (rng M) $$ HbA
    · iapply bsl_filter_mono (fun t => token (tk t)) _ _ (fun t ht => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
        exact ⟨⟨⟨by omega, by omega⟩, ht.1.2⟩, ht.2⟩) (rng M) $$ HbL

end loop

/-! ## The hart, the setup -/

section hart

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- **A HART** of (1a): `li t0, 1`, then the spin loop. -/
theorem lk_hart (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2) (hdd : g.dd = ddL M)
    (s0 : LP) {P0 : GSet Nat} (hprog : s0.prog = b1a) (hpc : s0.pc = 0) (hq : s0.q = [])
    (hlen : s0.regs.length = 32) (h10 : s0.rd 10 = X) (h11 : s0.rd 11 = Y)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a := by assumption) :   -- MachFix-R-b5: `vi = 0`
    lkCtx (GF := GF) g M tk ∗ obag g M tk h 0 0 ∗ lhA g Proto.triv (wL M h) (qsLk M h) psInit P0 [] ⊢
      wpKA g Proto.triv (wL M h) (qsLk M) s0 (ΦL g M) := by
  have hw := litW_x xs1a imgL M h
  iintro ⟨#Hctx, Hbag, Hl⟩
  iapply (wpKA_alui hw (litAg_x hq (p1a_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
    (by decide))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hls : lhS s1 := ⟨hP1, hq1, hc1, li_val hs1 (by decide) (by omega) (by decide),
    by rw [LPstep_rd hs1 10 (.inl (by decide)), h10], by rw [LPstep_rd hs1 11 (.inl (by decide)), h11],
    hs1.2.2.2.1.trans hlen⟩
  ihave Hloop := lk_loop (GF := GF) g M tk h hh hdd
  iapply Hloop $$ %s1 %_ %_ %_ %0 %hls %⟨Nat.zero_le _, noC_nil⟩ Hctx Hbag Hl

/-- One exclusive token per element of a list. -/
theorem toks_alloc : ∀ (l : List Nat), l.Nodup →
    ⊢@{IProp GF} |==> ∃ tk : Nat → GName, [∗list] t ∈ l, token (tk t)
  | [], _ => by
    iapply bupd_intro
    iexists (fun _ => 0)
    exact BigSepL.bigSepL_nil.2
  | a :: l, hnd => by
    have ih := toks_alloc l (List.nodup_cons.1 hnd).2
    iintro
    imod token_alloc with ⟨%γ, Hγ⟩
    imod ih with ⟨%tk', Hl⟩
    imodintro
    iexists (fun t => if t = a then γ else tk' t)
    iapply (BigSepL.bigSepL_cons).2
    isplitl [Hγ]
    · simp only [if_true]; iexact Hγ
    · iapply BigSepL.bigSepL_mono (Φ := fun _ t => token (tk' t)) ?_ $$ Hl
      intro k x hx
      have hxa : x ≠ a := fun e => (List.nodup_cons.1 hnd).1 (e ▸ List.mem_of_getElem? hx)
      simp only [if_neg hxa]; exact .rfl

/-- A release slot. -/
theorem rSlot_alloc (g : AGN) (M : List PMsg) (tk : Nat → GName) (r : Nat) :
    pend (GF := GF) g r ⊢ |={⊤}=> rSlot g M tk r := by
  iintro Hp
  unfold rSlot
  iapply inv_alloc
  inext; ileft; iexact Hp

/-- Hart `h`'s acquire messages. -/
def pA (M : List PMsg) (h t : Nat) : Bool := decide (0 < t) && decide (t ≠ 0) && isA M t && byH M h t
/-- Hart `h`'s lock messages. -/
def pL (M : List PMsg) (h t : Nat) : Bool := decide (0 < t) && decide (t ≠ 0) && (isA M t || isR M t) && byH M h t

theorem byH_01 {M : List PMsg} {t : Nat} (h0 : byH M 0 t = true) : byH M 1 t = false := by
  simp only [byH, decide_eq_true_eq] at h0
  simp [byH, h0]

theorem pA_10 {M : List PMsg} {t : Nat} (h1 : pA M 1 t = true) : pA M 0 t = false := by
  unfold pA at h1 ⊢
  cases h0 : byH M 0 t
  · simp
  · have := byH_01 h0
    rw [this] at h1; simp at h1

theorem pL_10 {M : List PMsg} {t : Nat} (h1 : pL M 1 t = true) : pL M 0 t = false := by
  unfold pL at h1 ⊢
  cases h0 : byH M 0 t
  · simp
  · have := byH_01 h0
    rw [this] at h1; simp at h1

theorem isA_01 {M : List PMsg} {t : Nat} (hA : isA M t = true) : byH M 0 t = true ∨ byH M 1 t = true := by
  obtain ⟨m, hm, ⟨_, _, _, ht⟩, _⟩ := clsB_iff.1 hA
  simp only [byH, tidAt, hm, Option.bind_some, decide_eq_true_eq]
  exact ht

theorem isR_A {M : List PMsg} {t : Nat} (hR : isR M t = true) : isA M t = false := by
  cases h : isA M t
  · rfl
  · rw [isA_R h] at hR; cases hR

theorem isC_A {M : List PMsg} {t : Nat} (hC : isC M t = true) : isA M t = false ∧ isR M t = false := by
  have hL := isC_L hC
  refine ⟨?_, ?_⟩
  · cases h : isA M t
    · rfl
    · rw [isA_L h] at hL; cases hL
  · cases h : isR M t
    · rfl
    · rw [isR_L h] at hL; cases hL

/-- **THE SETUP** (plan §3 "At adequacy start … for every index t in 1..|M|", R-a5): one token per message; acquire
messages' `pend`s to their authors' bags, release messages' to their slots, counter messages' to the counter's
points-to in the image's slot (the lock is born unlocked), the rest to dead invariants. -/
theorem lk_setup (g : AGN) (M : List PMsg) (hm : g.mn.length = M.length) :
    doomInv (GF := GF) g M ∗ ([∗list] k ↦ _x ∈ g.mn, pend g (k + 1)) ⊢
      |={⊤}=> ∃ tk, lkCtx g M tk ∗ obag g M tk 0 0 0 ∗ obag g M tk 1 0 0 := by
  iintro ⟨#Hdoom, Hp⟩
  have h0 : ([∗list] k ↦ _x ∈ g.mn, pend (GF := GF) g (k + 1)) ⊢ [∗list] t ∈ rng M, pend g t := by
    have := bsl_range (pend (GF := GF) g) g.mn 1; rw [hm] at this; exact this
  ihave Hp := h0 $$ Hp
  imod toks_alloc (GF := GF) (rng M) (nodup_rng M) with ⟨%tk, Ht⟩
  -- pends
  have s1 := bsl_filter_split (pend (GF := GF) g) (pA M 0) (rng M)
  have s2 := bsl_filter_split (pend (GF := GF) g) (pA M 1) ((rng M).filter (fun t => !pA M 0 t))
  rw [filter_filter_of (r := pA M 1) (fun t => by
      cases h1 : pA M 1 t
      · simp
      · rw [pA_10 h1]; rfl)] at s2
  rw [filter_filter_of (r := fun t => !pA M 0 t && !pA M 1 t) (fun t => rfl)] at s2
  have s3 := bsl_filter_split (pend (GF := GF) g) (isR M) ((rng M).filter (fun t => !pA M 0 t && !pA M 1 t))
  rw [filter_filter_of (r := isR M) (fun t => by
      cases hR : isR M t
      · simp
      · have e0 : pA M 0 t = false := by simp [pA, isR_A hR]
        have e1 : pA M 1 t = false := by simp [pA, isR_A hR]
        rw [e0, e1]; rfl)] at s3
  rw [filter_filter_of (r := fun t => !pA M 0 t && !pA M 1 t && !isR M t) (fun t => rfl)] at s3
  have s4 := bsl_filter_split (pend (GF := GF) g) (isC M)
    ((rng M).filter (fun t => !pA M 0 t && !pA M 1 t && !isR M t))
  rw [filter_filter_of (r := isC M) (fun t => by
      cases hC : isC M t
      · simp
      · have e0 : pA M 0 t = false := by simp [pA, (isC_A hC).1]
        have e1 : pA M 1 t = false := by simp [pA, (isC_A hC).1]
        rw [e0, e1, (isC_A hC).2]; rfl)] at s4
  rw [filter_filter_of (r := fun t => !pA M 0 t && !pA M 1 t && !isR M t && !isC M t) (fun t => rfl)] at s4
  ihave ⟨HA0, Hp⟩ := s1 $$ Hp
  ihave ⟨HA1, Hp⟩ := s2 $$ Hp
  ihave ⟨HR, Hp⟩ := s3 $$ Hp
  ihave ⟨HC, Hp⟩ := s4 $$ Hp
  ihave HJ := bsl_filter_mono (pend (GF := GF) g) _ (isJ M) (fun t hJ => by
    have hA : isA M t = false := by
      cases h : isA M t
      · rfl
      · unfold isJ isDd at hJ; rw [h, isA_L h] at hJ; simp at hJ
    have hR : isR M t = false := by
      cases h : isR M t
      · rfl
      · unfold isJ isDd at hJ; rw [h, isR_L h] at hJ; simp at hJ
    have hC : isC M t = false := by
      cases h : isC M t
      · rfl
      · unfold isJ isDd at hJ; rw [isC_L h, h] at hJ; simp at hJ
    have e0 : pA M 0 t = false := by simp [pA, hA]
    have e1 : pA M 1 t = false := by simp [pA, hA]
    rw [e0, e1, hR, hC]; rfl) (rng M) $$ Hp
  -- tokens
  have t1 := bsl_filter_split (fun t => token (GF := GF) (tk t)) (pL M 0) (rng M)
  ihave ⟨HL0, Ht⟩ := t1 $$ Ht
  ihave HL1 := bsl_filter_mono (fun t => token (GF := GF) (tk t)) _ (pL M 1) (fun t h1 => by
    rw [pL_10 h1]; rfl) (rng M) $$ Ht
  -- the invariants
  imod bsl_fupd (G := fun r => rSlot (GF := GF) g M tk r) (fun r => rSlot_alloc g M tk r) _ $$ HR with #Hrs
  imod bsl_fupd (G := fun t => deadInv (GF := GF) g t) (fun t => dead_alloc g t) _ $$ HJ with #Hdd
  imod inv_alloc (ndot lkN 0) ⊤ iprop(Rs (GF := GF) g M 0 ∨ nxtTok M tk 0) $$ [HC] with #Hi
  · inext; ileft; unfold Rs cPts; iexists 0
    isplitr
    · ipureintro; exact Nat.le_refl _
    isplitr
    · ipureintro; exact .inl rfl
    have hc0 : cBag M 0 = (rng M).filter (isC M) := by
      unfold cBag; refine List.filter_congr (fun t ht => ?_); have := rng_ge ht; simp [show 0 < t by omega]
    rw [hc0]; iexact HC
  imodintro
  iexists tk
  isplitr [HA0 HA1 HL0 HL1]
  · unfold lkCtx iSlot
    iframe Hdoom Hi Hrs Hdd
  have eA : ∀ h, bagA M h 0 0 = (rng M).filter (pA M h) := fun _ => rfl
  have eL : ∀ h, bagL M h 0 0 = (rng M).filter (pL M h) := fun _ => rfl
  isplitl [HA0 HL0]
  · unfold obag; rw [eA, eL]; iframe HA0 HL0
  · unfold obag; rw [eA, eL]; iframe HA1 HL1

end hart

/-! ## The verdict -/

theorem progs_1a : ∃ p0 p1 : LP, progs t1a = [p0, p1] := ⟨_, _, rfl⟩

/-- THE ADEQUACY PREMISE for (1a). -/
theorem lk_premise (M : List PMsg)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a := by assumption) :   -- MachFix-R-b5: `vi = 0`
    wpPremise .hasLC ownGF (xStep xs1a) litDone imgL M (progs t1a) Proto.triv (fun _ _ => True)
      (fun h => ΨK M (qsLk M h)) (ddL M) := by
  intro Hinv g P0 hn hm hdd hP0
  obtain ⟨p0, p1, hps⟩ := progs_1a
  have hg0 : (progs t1a)[0]? = some p0 := by rw [hps]; rfl
  have hg1 : (progs t1a)[1]? = some p1 := by rw [hps]; rfl
  obtain ⟨hpr0, hpc0, hq0, hl0, hrd0⟩ := progs_get hg0
  obtain ⟨hpr1, hpc1, hq1, hl1, hrd1⟩ := progs_get hg1
  have hlen : g.hn.length = 2 := by rw [hn, hps]; rfl
  obtain ⟨γ0, γ1, hgn⟩ : ∃ a b, g.hn = [a, b] := by
    match h : g.hn, hlen with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  rw [hps]
  iintro #Hdoom Hh Hp
  imod lk_setup g M hm $$ [Hp] with ⟨%tk, #Hctx, Hb0, Hb1⟩
  · iframe Hdoom Hp
  have k0 := lk_hart (GF := ownGF) g M tk 0 (by decide) hdd p0 (P0 := P0 0) hpr0 hpc0 hq0 hl0
    (by rw [hrd0 10 (by decide) (by decide)]; rfl) (by rw [hrd0 11 (by decide) (by decide)]; rfl)
  have k1 := lk_hart (GF := ownGF) g M tk 1 (by decide) hdd p1 (P0 := P0 1) hpr1 hpc1 hq1 hl1
    (by rw [hrd1 10 (by decide) (by decide)]; rfl) (by rw [hrd1 11 (by decide) (by decide)]; rfl)
  have k0' : lkCtx (GF := ownGF) g M tk ∗ obag g M tk 0 0 0 ∗
      lhA g Proto.triv (wL M 0) (qsLk M 0) psInit (P0 0) [] ⊢
      wpA (hlc := .hasLC) g Proto.triv (hw (xStep xs1a) litDone imgL M 0) (fun h => ΨK M (qsLk M h)) p0
        (fun v => iprop(⌜∃ V, grd Proto.triv imgL M V ((fun (_ : Nat) (_ : Unit) => True) 0 v)⌝ ∨ dshot g)) := k0
  have k1' : lkCtx (GF := ownGF) g M tk ∗ obag g M tk 1 0 0 ∗
      lhA g Proto.triv (wL M 1) (qsLk M 1) psInit (P0 1) [] ⊢
      wpA (hlc := .hasLC) g Proto.triv (hw (xStep xs1a) litDone imgL M (0 + 1)) (fun h => ΨK M (qsLk M h)) p1
        (fun v => iprop(⌜∃ V, grd Proto.triv imgL M V ((fun (_ : Nat) (_ : Unit) => True) (0 + 1) v)⌝ ∨
          dshot g)) := k1
  rw [hgn]
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H0, Hh⟩
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H1, -⟩
  imodintro
  have s0 := lhA_start (GF := ownGF) (g := g) (π := Proto.triv) (w := wL M 0) (Qs := qsLk M) (P0 := P0 0)
    (qLk_noC noC_nil)
  have s1 := lhA_start (GF := ownGF) (g := g) (π := Proto.triv) (w := wL M 1) (Qs := qsLk M) (P0 := P0 (0 + 1))
    (qLk_noC noC_nil)
  iapply (BigSepL.bigSepL_cons).2
  isplitl [H0 Hb0]
  · iapply k0'
    iframe Hctx Hb0
    iapply s0
    iexact H0
  iapply (BigSepL.bigSepL_cons).2
  isplitl [H1 Hb1]
  · iapply k1'
    iframe Hctx Hb1
    iapply s1
    iexact H1
  iapply (BigSepL.bigSepL_nil).2
  itrivial

/-- `qLk` of the memory entries is `qLk` of the trace (counter loads and stores are memory entries). -/
theorem qLk_of_memEv {M : List PMsg} {τ : Trace} (h : qLk M (memEv τ)) : qLk M τ := by
  intro tvs ts h1 h2
  obtain ⟨e1, h1, hl⟩ := h1
  obtain ⟨e2, h2, hs⟩ := h2
  refine h tvs ts ⟨e1, List.mem_filter.2 ⟨h1, ?_⟩, hl⟩ ⟨e2, List.mem_filter.2 ⟨h2, ?_⟩, hs⟩
  · obtain ⟨_, rfl⟩ := hl; rfl
  · obtain ⟨_, _, _, rfl⟩ := hs; rfl

/-- **G4 TARGET (1a) ON TRACK (a): THE SPINLOCK (the manual's Example 1) WITH A MUTUAL-EXCLUSION CLIENT** (plan §4 G4
(1a)).  Over every final memory `M` and every valid run of machine v2 of two harts running `p1a`
(`li t0,1; again: amoswap.w.aq t0,t0,(a0); bnez t0,again; ld t2,(a1); addi t2,t2,1; sd t2,(a1);
amoswap.w.rl x0,x0,(a0)`), each hart's trace satisfies `qLk`: its critical section's load read, in every byte, the
latest counter message below its store (or the initial memory) — no counter write by anybody lies in between.
Proved in the logic (OwnALock*.lean): the lock's resource (the counter's points-to) moves through the release slots
and the image's slot, claimed by the unique AMO reading each release.  0 named inputs; finite runs (a hart may stop
anywhere in its spin loop; the prefix lemma S3d is separate, [OWN.P4]). -/
theorem own_lock1a (M : List PMsg) (run : PFRun LP Unit)
    (hrun : PF.validRun (xStep xs1a) imgL () (progs t1a) M run) : ∀ h, qLk M (run.trace h) := by
  have hnoinv := x_noInvalT hrun   -- MachFix-R-b5: the front end issues no CMO (`vi = 0`)
  obtain ⟨_, hΨ, _⟩ := adequacyA (hlc := .hasLC) (GF := ownGF) Proto.triv (fun _ _ => True)
    (fun h => ΨK M (qsLk M h)) (ddL M) trivial (fun h => ⟨qLk_noC noC_nil, wrOk_nil M⟩) (lk_premise M) hrun
  intro h
  have hq := (hΨ h (run.trace h).length).1
  rw [List.take_length] at hq
  exact qLk_of_memEv hq

/-- **MUTUAL EXCLUSION, ordered**: if hart `h`'s critical section loaded `tvs` and stored at `ts`, every counter
message `ts0 < ts` (another critical section's store, or any) is at or below the load's source in every byte — the
critical section that stores later READ the earlier one's write or a later one. -/
theorem own_lock1a_excl (M : List PMsg) (run : PFRun LP Unit)
    (hrun : PF.validRun (xStep xs1a) imgL () (progs t1a) M run) (h : Nat) (tvs : List (Nat × BitVec 8))
    (ts ts0 : Nat) (hl : ∃ e ∈ run.trace h, isCLd e tvs) (hs : ∃ e ∈ run.trace h, isCSt e ts)
    (hc : isC M ts0 = true) (hlt : ts0 < ts) : ∀ p ∈ tvs, ts0 ≤ p.1 := by
  obtain ⟨lw, hall, _, _, hno⟩ := own_lock1a M run hrun h tvs ts hl hs
  intro p hp
  rw [hall p hp]
  apply Classical.byContradiction; intro hne
  have := hno ts0 (by omega) hlt
  rw [hc] at this; cases this

#print axioms own_lock1a
#print axioms own_lock1a_excl

end Weak.Prom.OA
