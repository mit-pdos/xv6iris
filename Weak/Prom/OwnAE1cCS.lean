/-
Weak/Prom: **E-a, G4 (1c) with the dead set empty — the critical section, the cpu field, the plain release**
(stage E-a; copies of OwnALock1cCS.lean over `π1c` and the per-byte owners of OwnAE1cDefs.lean).

What changes from the original:
* the counter READ (`lk_cs1E`, R-a1): a byte above the owned latest write `lw` came from a message touching the
  counter.  Either the points-to holds its `pend` (ANY such message the lock does not own: ordinary doom, the
  reader keeps every other resource, plan R-a1), or the message also touches the lock word — then `π1c` refutes it
  under the guard, `⟦t⟧ False` (`straddle_grd`).  No dead set, no free mode: the hart runs on with all its resources
  in every branch;
* every store proves `π1c.okMsg` of its message (`ok_ct`, `ok_pc`, `ok_lk`);
* the trace invariant is carried GUARDED (`QE`: `⟦V⟧ qLk` or doom).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAE1cDefs

namespace Weak.Prom.OA.EC

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y)
open Weak.Prom.OA.C (Pc p1c b1c t1c xs1c xOf_1c p1c_at wL1c msgAt_of alg_pc base_pc st_nonC Pc_ne_Ct Lk_ne_Ct
  st_coh st_coh0 st_vwOld st_vrNew)
open Weak.Prom.OA.E
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

section cs

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- The postcondition. -/
abbrev ΦE (g : AGN) (M : List PMsg) : Unit → IProp GF := fun _ => iprop(⌜∃ V, grd π1c imgL M V True⌝ ∨ dshot g)

/-- The guarded trace invariant (plan §2 "⟦V⟧"), or doom. -/
def QE (g : AGN) (M : List PMsg) (ev : Trace) : IProp GF := iprop(⌜∃ V, grd π1c imgL M V (qLk M ev)⌝ ∨ dshot g)

instance (g : AGN) (M : List PMsg) (ev : Trace) : Persistent (QE (GF := GF) g M ev) := by unfold QE; infer_instance

theorem gq_snoc {M : List PMsg} {ev : Trace} {e : PEv} (he : (∀ tvs, ¬ isCLd e tvs) ∧ (∀ ts, ¬ isCSt e ts))
    (h : ∃ V, grd π1c imgL M V (qLk M ev)) : ∃ V, grd π1c imgL M V (qLk M (ev ++ [e])) :=
  let ⟨V, hV⟩ := h; ⟨V, grd_imp (fun q => qLk_snoc q he) hV⟩

/-- **THE RELEASE** (`pc = 11`, `sw zero,0(s1)`, plain, release-class through the fence) and the end: the deposit. -/
theorem lk_relE (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo lw sp : Nat)
    (hs : s.prog = b1c ∧ s.q = [] ∧ s.pc = 11 ∧ s.rd 9 = X ∧ s.rd 11 = Y)
    (hlo : lo ≤ coh ws Lk) (hvw : lw ≤ ws.wVwNew) (hsp : sp ≤ ws.wVwNew) :
    lkCtxE (GF := GF) g M tk ∗ C.obag g M tk h lo 0 ∗ cPtsE g M lw ∗ pPtsE g M sp ∗ QE g M ev ∗
      lhA g π1c (wL1c M h) (qsLk M h) ws pr ev ⊢ wpKA g π1c (wL1c M h) (qsLk M) s (ΦE g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11⟩ := hs
  have hw := litW_x xs1c imgL M h
  have hX := p1c_at hprog
  iintro ⟨#Hctx, Hbag, Hc, Hpp, #HQ, Hl⟩
  iapply (wpKA_sw (sz := 4) (rs2 := 0) (rs1 := 9) (off := 0) (base := Lk) hw
    (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_of h9 (by decide) (by decide))
    (base_of h9 (by decide)))
  iframe Hl
  inext
  iintro %r %_ %hmsg %hcoh %hext _ _
  have hd0 : toBytes (s.rd 0) 4 = toBytes 0 4 := rfl
  rw [hd0] at hmsg hcoh
  have hc0 : coh ws Lk < r := by
    have := cohBelow_at (j := 0) hcoh (by decide)
    simpa using this
  have hr1 : 1 ≤ r := by omega
  obtain ⟨hR, hbyH⟩ := C.isR_of_msg hh hr1 hmsg
  have hmr := msgAt_of hr1 hmsg
  have hrM : r ≤ M.length := (msgAt_le hmr).2
  have hlor : lo < r := by omega
  -- RELEASE-CLASS (plan §3): the plain store's pre-view contains `vwNew ≥` the counter and cpu stores
  have hvr : ws.wVwNew < r := by
    have := (PF.stPreA_ge ws false false (srcsView ws (srcR 9)) (srcsView ws (srcR 0))).2.2.2.1
    omega
  unfold C.obag
  icases Hbag with ⟨-, HbL⟩
  unfold C.bagL
  icases bsl_filter_take (fun t => token (tk t))
    (fun t => decide (lo < t) && decide (t ≠ 0) && (C.isA M t || C.isR M t) && byH M h t) (fun _ => false) r
    (by simp [hlor, show r ≠ 0 by omega, hR, hbyH]) (fun _ h => by cases h) (rng M) (mem_rng.2 ⟨hr1, hrM⟩)
    (nodup_rng M) $$ HbL with ⟨Ht, -⟩
  unfold lkCtxE
  icases Hctx with ⟨-, -, Hrs, -⟩
  ihave #Hslot := bsl_mem (F := fun r => rSlotE g M tk r) (List.mem_filter.2 ⟨mem_rng.2 ⟨hr1, hrM⟩, hR⟩) $$ Hrs
  unfold rSlotE
  imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hslot with ⟨Hb, Hclose⟩
  icases Hb with (Hp | ⟨_, Ht', _⟩)
  rotate_left
  · iexfalso; iapply token_exclusive; iframe Ht Ht'
  imod shoot $$ Hp with #Hsh
  ihave Hpr := pPtsE_mono (GF := GF) g M (s := sp) (s' := r) (by omega) $$ Hpp
  imod Hclose $$ [Ht Hc Hpr] with -
  · iright; iframe Hsh Ht; ileft; unfold RsE; iframe Hpr; iexists lw; iframe Hc; ipureintro; omega
  imodintro
  isplitl []
  · unfold QE
    icases HQ with (%hQ | #Hd)
    · ileft; ipureintro; exact ⟨gq_snoc (st_nonC Lk_ne_Ct _ _ _ _) hQ, grd_intro (ok_lk (toBytes_length 0 4))⟩
    · iright; iexact Hd
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s' %hs' _ _
  imodintro
  iintro Hl
  obtain ⟨hP', hc', hq'⟩ := LPstep_at hs' hprog (by rw [hpc])
  have hend : s'.prog.length ≤ s'.pc := by rw [hP', hc']; decide
  iapply (wpKA_end (v := ()) (litAg_xn hq' (fun x hx => by rw [p1c_at hP', hc'] at hx; cases hx)) hq' hend
    (by show litDone s' = some (); unfold litDone; rw [if_pos ⟨hq', hend⟩]))
  iframe Hl
  imodintro
  ileft; ipureintro; exact ⟨0, grd_intro trivial⟩

/-- `pc = 10`: `fence rw,w` raises `vwNew` to `vrOld ⊔ vwOld`. -/
theorem lk_fenceE (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo lw sp : Nat)
    (hs : s.prog = b1c ∧ s.q = [] ∧ s.pc = 10 ∧ s.rd 9 = X ∧ s.rd 11 = Y)
    (hlo : lo ≤ coh ws Lk) (hvw : lw ≤ ws.wVwOld) (hsp : sp ≤ ws.wVwOld) :
    lkCtxE (GF := GF) g M tk ∗ C.obag g M tk h lo 0 ∗ cPtsE g M lw ∗ pPtsE g M sp ∗ QE g M ev ∗
      lhA g π1c (wL1c M h) (qsLk M h) ws pr ev ⊢ wpKA g π1c (wL1c M h) (qsLk M) s (ΦE g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11⟩ := hs
  have hw := litW_x xs1c imgL M h
  have hX := p1c_at hprog
  iintro ⟨#Hctx, Hbag, Hc, Hpp, #HQ, Hl⟩
  iapply (wpKA_fence hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hvw' : lw ≤ (instrR (fencePost ws true true false true)).wVwNew := by
    simp only [instrR_vwNew, fence_vwNew, ite_true]; omega
  have hsp' : sp ≤ (instrR (fencePost ws true true false true)).wVwNew := by
    simp only [instrR_vwNew, fence_vwNew, ite_true]; omega
  iapply (lk_relE g M tk h hh s1 (instrR (fencePost ws true true false true)) _ ev lo lw sp
    ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 9 (.inr rfl), h9], by rw [LPstep_rd hs1 11 (.inr rfl), h11]⟩
    hlo hvw' hsp')
  iframe Hctx Hbag Hc Hpp HQ Hl

/-- `pc = 9`: `sd zero,16(s1)`: its `pend` is in the cpu field's bag. -/
theorem lk_cpu0E (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo lw sp : Nat)
    (hs : s.prog = b1c ∧ s.q = [] ∧ s.pc = 9 ∧ s.rd 9 = X ∧ s.rd 11 = Y)
    (hlo : lo ≤ coh ws Lk) (hvw : lw ≤ ws.wVwOld) (hsp : sp ≤ coh ws Pc) :
    lkCtxE (GF := GF) g M tk ∗ C.obag g M tk h lo 0 ∗ cPtsE g M lw ∗ QE g M ev ∗
      lhA g π1c (wL1c M h) (qsLk M h) ws pr ev ∗ pPtsE g M sp ⊢
      wpKA g π1c (wL1c M h) (qsLk M) s (ΦE g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11⟩ := hs
  have hw := litW_x xs1c imgL M h
  have hX := p1c_at hprog
  iintro ⟨#Hctx, Hbag, Hc, #HQ, Hl, Hpp⟩
  iapply (wpKA_sw (sz := 8) (rs2 := 0) (rs1 := 9) (off := 16) (base := Pc) hw
    (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_pc h9) (base_pc h9))
  iframe Hl
  inext
  iintro %ts %_ %hmsg %hcoh %_ _ _
  rw [toBytes_length] at hcoh
  have hc0 : coh ws Pc < ts := by
    have := cohBelow_at (j := 0) hcoh (by decide)
    simpa using this
  have hts1 : 1 ≤ ts := by omega
  have hP := P_PT (toBytes_length _ _) hts1 hmsg
  have htsM := msgAt_le (msgAt_of hts1 hmsg)
  icases pPtsE_take (GF := GF) g M (by omega : sp < ts) hP htsM $$ Hpp with ⟨Hpd, Hpp⟩
  imod shoot $$ Hpd with #Hsh
  imodintro
  isplitl []
  · unfold QE
    icases HQ with (%hQ | #Hd)
    · ileft; ipureintro; exact ⟨gq_snoc (st_nonC Pc_ne_Ct _ _ _ _) hQ, grd_intro ok_pc⟩
    · iright; iexact Hd
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hvo := st_vwOld ws (srcsView ws (srcR 9)) (max (srcsView ws (srcR 9)) (srcsView ws (srcR 0))) Pc
    (toBytes (s.rd 0) 8).length ts
  iapply (lk_fenceE g M tk h hh s1 _ _ _ lo lw ts
    ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 9 (.inr rfl), h9], by rw [LPstep_rd hs1 11 (.inr rfl), h11]⟩
    (Nat.le_trans hlo (st_coh _ _ _ _ _ _ Lk)) (by rw [hvo]; omega) (by rw [hvo]; omega))
  iframe Hctx Hbag Hc Hpp Hl
  unfold QE
  icases HQ with (%hQ | #Hd)
  · ileft; ipureintro; exact gq_snoc (st_nonC Pc_ne_Ct _ _ _ _) hQ
  · iright; iexact Hd

/-- The BAD mode after a counter read above `lw`: doomed (the reader surrendered the `pend` of `ex`, plan R-a1), or
the guarded refutation `⟦ex⟧ False` (a lock-owned message). -/
def badE (g : AGN) (M : List PMsg) (ex : Nat) : IProp GF := iprop(dshot g ∨ ⌜grd π1c imgL M ex False⌝)

instance (g : AGN) (M : List PMsg) (ex : Nat) : Persistent (badE (GF := GF) g M ex) := by
  unfold badE; infer_instance

/-- `pc = 7..8`: `addi t2,t2,1; sd t2,(a1)`, then the rest.  `ex` is the message of a bad read (`0`: clean). -/
theorem lk_cs2E (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev0 : Trace) (tvs1 : List (Nat × BitVec 8)) (lo lw ex sp : Nat)
    (hs : s.prog = b1c ∧ s.q = [] ∧ s.pc = 7 ∧ s.rd 9 = X ∧ s.rd 11 = Y)
    (hlo : lo ≤ coh ws Lk) (hsp : sp ≤ coh ws Pc) (hnoC : noC ev0) (hlw : lw = 0 ∨ isC M lw = true) :
    lkCtxE (GF := GF) g M tk ∗ C.obag g M tk h lo 0 ∗ pPtsE g M sp ∗ ([∗list] t ∈ cBagXE M lw ex, pend g t) ∗
      (⌜ex = 0 ∧ (∀ p ∈ tvs1, p.1 = lw) ∧ lw ≤ coh ws Ct⌝ ∨
        (badE g M ex ∗ ⌜lw < ex ∧ ∃ j : Nat, j < 8 ∧ ex ≤ coh ws (Ct + j)⌝)) ∗
      lhA g π1c (wL1c M h) (qsLk M h) ws pr (ev0 ++ [(LLoad false false Ct tvs1 (srcR 11), none)]) ⊢
      wpKA g π1c (wL1c M h) (qsLk M) s (ΦE g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11⟩ := hs
  have hw := litW_x xs1c imgL M h
  have hX := p1c_at hprog
  iintro ⟨#Hctx, Hbag, Hpp, Hb, Hmode, Hl⟩
  -- `addi t2,t2,1`
  iapply (wpKA_alui hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e11 : s1.rd 11 = Y := by rw [LPstep_rd hs1 11 (.inl (by decide)), h11]
  have e9 : s1.rd 9 = X := by rw [LPstep_rd hs1 9 (.inl (by decide)), h9]
  -- `sd t2,(a1)`
  iapply (wpKA_sw (sz := 8) (rs2 := 7) (rs1 := 11) (off := 0) (base := Ct) hw
    (litAg_x hq1 (p1c_at hP1) (by rw [hc1]; rfl) rfl) hq1 (by rw [hP1, hc1]; rfl)
    (alg_of e11 (by decide) (by decide)) (base_of e11 (by decide)))
  iframe Hl
  inext
  iintro %ts %_ %hmsg %hcoh %_ _ _
  rw [toBytes_length] at hcoh
  have hcj : ∀ j : Nat, j < 8 → coh ws (Ct + j) < ts := fun j hj => by
    have h := cohBelow_at hcoh hj; exact h
  have hts1 : 1 ≤ ts := by have := hcj 0 (by decide); omega
  have hC := isC_of_msg hh (toBytes_length _ _) hts1 hmsg
  have hCT := C_CT hC
  have hmt : msgAt M ts = some ⟨Ct, toBytes (s1.rd 7) 8, some h, .plain⟩ := msgAt_of hts1 hmsg
  have htsM := msgAt_le hmt
  -- take `pend ts` out of the bag; the rest, minus any gap, is the bag above `ts`
  ihave HQ : |={⊤}=> QE g M (ev0 ++ [(LLoad false false Ct tvs1 (srcR 11), none)] ++
      [(LStore false false Ct (toBytes (s1.rd 7) 8) (srcR 11) (srcR 7), some ts)]) ∗ shot g ts ∗
      ([∗list] t ∈ cBagE M ts, pend g t) $$ [Hb Hmode]
  · icases Hmode with (%hcl | ⟨#Hbad, %hra⟩)
    · obtain ⟨rfl, hall, hlc⟩ := hcl
      have hlts : lw < ts := by have := hcj 0 (by decide); simp at this; omega
      unfold cBagXE
      icases bsl_filter_take (pend g) (fun t => decide (lw < t) && decide (t ≠ 0) && isCT M t)
        (fun t => decide (lw < t) && decide (t ≠ ts) && isCT M t) ts (by simp [hlts, hCT]; omega)
        (fun t ht => by simp at ht; exact ⟨by simp [ht.1.1, ht.2]; omega, ht.1.2⟩) (rng M)
        (mem_rng.2 htsM) (nodup_rng M) $$ Hb with ⟨Hp, Hb⟩
      imod shoot $$ Hp with #Hsh
      by_cases hg : ∃ u, lw < u ∧ u < ts ∧ isC M u = true
      · -- a counter message between the read and the write: its `pend` is held, doom (plan R-a1)
        obtain ⟨u, hu1, hu2, hu3⟩ := hg
        have huM : 1 ≤ u ∧ u ≤ M.length := by
          obtain ⟨m, hm, _⟩ := clsB_iff.1 hu3; exact msgAt_le hm
        icases bsl_filter_take (pend g) (fun t => decide (lw < t) && decide (t ≠ ts) && isCT M t)
          (fun t => decide (lw < t) && decide (t ≠ ts) && decide (t ≠ u) && isCT M t) u
          (by simp [hu1, C_CT hu3]; omega)
          (fun t ht => by simp at ht; exact ⟨by simp [ht.1.1.1, ht.1.1.2, ht.2], ht.1.2⟩) (rng M)
          (mem_rng.2 huM) (nodup_rng M) $$ Hb with ⟨Hu, Hb⟩
        unfold lkCtxE
        icases Hctx with ⟨Hdoom, -⟩
        imod doom (E := ⊤) CoPset.subseteq_top g M u huM $$ [Hdoom Hu] with #Hd
        · iframe Hdoom Hu
        imodintro
        isplitr
        · unfold QE; iright; iexact Hd
        iframe Hsh
        unfold cBagE
        iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
          exact ⟨⟨⟨by omega, by omega⟩, by omega⟩, ht.2⟩) (rng M) $$ Hb
      · have hl : latestC M lw ts := ⟨hlw, hlts, fun u h1 h2 => by
          cases h3 : isC M u
          · rfl
          · exact absurd ⟨u, h1, h2, h3⟩ hg⟩
        imodintro
        isplitr
        · unfold QE; ileft; ipureintro; exact ⟨0, grd_intro (qLk_pair hnoC hall hl)⟩
        iframe Hsh
        unfold cBagE
        iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
          exact ⟨⟨by omega, by omega⟩, ht.2⟩) (rng M) $$ Hb
    · obtain ⟨hlex, j, hj, hexc⟩ := hra
      have hext : ex < ts := Nat.lt_of_le_of_lt hexc (hcj j hj)
      unfold cBagXE
      icases bsl_filter_take (pend g) (fun t => decide (lw < t) && decide (t ≠ ex) && isCT M t)
        (fun t => decide (lw < t) && decide (t ≠ ex) && decide (t ≠ ts) && isCT M t) ts
        (by simp [hCT]; omega)
        (fun t ht => by simp at ht; exact ⟨by simp [ht.1.1.1, ht.1.1.2, ht.2], ht.1.2⟩) (rng M)
        (mem_rng.2 htsM) (nodup_rng M) $$ Hb with ⟨Hp, Hb⟩
      imod shoot $$ Hp with #Hsh
      imodintro
      isplitr
      · unfold QE badE
        icases Hbad with (#Hd | %hgf)
        · iright; iexact Hd
        · ileft; ipureintro; exact ⟨ex, fun hv => (hgf hv).elim⟩
      iframe Hsh
      unfold cBagE
      iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
        exact ⟨⟨⟨by omega, by omega⟩, by omega⟩, ht.2⟩) (rng M) $$ Hb
  imod HQ with ⟨#HQ, #Hsh, Hb⟩
  imodintro
  isplitl []
  · unfold QE
    icases HQ with (%hQ | #Hd)
    · ileft; ipureintro; exact ⟨hQ, grd_intro ok_ct⟩
    · iright; iexact Hd
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s2 %hs2 _ _
  imodintro
  iintro Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have e11' : s2.rd 11 = Y := by rw [LPstep_rd hs2 11 (.inr rfl), e11]
  have e9' : s2.rd 9 = X := by rw [LPstep_rd hs2 9 (.inr rfl), e9]
  have hst := storeRun_mono (instrR (regWP ws 7 (srcR 7))) false (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 11))
    (max (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 11)) (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 7)))
    Ct (toBytes (s1.rd 7) 8).length ts
  have hlo' : lo ≤ coh (instrR (acqPost (storeRun (instrR (regWP ws 7 (srcR 7))) false
      (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 11))
      (max (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 11)) (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 7)))
      Ct (toBytes (s1.rd 7) 8).length ts) false ts)) Lk := by
    have := hst.2.2.2.2.2.2.2.2.2.1 Lk
    have e : coh (instrR (regWP ws 7 (srcR 7))) Lk = coh ws Lk := rfl
    rw [acqPost_false]; simp only [instrR_coh]; omega
  have hvw' : ts ≤ (instrR (acqPost (storeRun (instrR (regWP ws 7 (srcR 7))) false
      (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 11))
      (max (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 11)) (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 7)))
      Ct (toBytes (s1.rd 7) 8).length ts) false ts)).wVwOld := by
    rw [acqPost_false, instrR_vwOld, hst.2.2.1]; omega
  have hsp' : sp ≤ coh (instrR (acqPost (storeRun (instrR (regWP ws 7 (srcR 7))) false
      (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 11))
      (max (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 11)) (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 7)))
      Ct (toBytes (s1.rd 7) 8).length ts) false ts)) Pc := by
    have := hst.2.2.2.2.2.2.2.2.2.1 Pc
    have e : coh (instrR (regWP ws 7 (srcR 7))) Pc = coh ws Pc := rfl
    rw [acqPost_false]; simp only [instrR_coh]; omega
  iapply (lk_cpu0E g M tk h hh s2 _ _ _ lo ts sp ⟨hP2, hq2, by rw [hc2], e9', e11'⟩ hlo' hvw' hsp')
  iframe Hctx Hbag HQ Hl Hpp
  unfold cPtsE
  iframe Hb
  ipureintro; exact .inr hC

/-- **THE CRITICAL SECTION'S LOAD** (`pc = 6`, `ld t2,(a1)`, plan R-a1): the owned read of the counter, per byte. -/
theorem lk_cs1E (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo lw sp : Nat)
    (hs : s.prog = b1c ∧ s.q = [] ∧ s.pc = 6 ∧ s.rd 9 = X ∧ s.rd 11 = Y)
    (hlo : lo ≤ coh ws Lk) (hsp : sp ≤ coh ws Pc) (hvr : lw ≤ ws.wVrNew) (hnoC : noC ev)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :
    lkCtxE (GF := GF) g M tk ∗ C.obag g M tk h lo 0 ∗ cPtsE g M lw ∗ pPtsE g M sp ∗
      lhA g π1c (wL1c M h) (qsLk M h) ws pr ev ⊢ wpKA g π1c (wL1c M h) (qsLk M) s (ΦE g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11⟩ := hs
  have hw := litW_x xs1c imgL M h
  have hX := p1c_at hprog
  iintro ⟨#Hctx, Hbag, Hc, Hpp, Hl⟩
  unfold cPtsE
  icases Hc with ⟨%hlw, Hb⟩
  rw [cBagE_X]
  iapply (wpKA_ld (sz := 8) (sgn := true) (rd := 7) (rs1 := 11) (off := 0) (base := Ct) hw
    (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_of h11 (by decide) (by decide))
    (base_of h11 (by decide)))
  iframe Hl
  inext
  iintro %tvs1 %hl1 %hlo1 _ _
  have hvp : lw ≤ ldPre ws false false (srcsView ws (srcR 11)) :=
    Nat.le_trans hvr (PF.ldPre_ge ws false false (srcsView ws (srcR 11))).2.1
  have hcases := cld_cases (img := imgL) hlw hvp 0 tvs1 (by rw [hl1]; decide)
    (by have := loadOk_weak hlo1; simpa using this)
  have hcohj := (loadBytes_coh false (ldPre ws false false (srcsView ws (srcR 11))) ws Ct tvs1).2
  -- THE MODE after the read: clean, or bad (doomed / guarded-false), one message excluded from the bag
  ihave Hmode : |={⊤}=> ∃ ex, ([∗list] t ∈ cBagXE M lw ex, pend g t) ∗
      (⌜ex = 0 ∧ (∀ p ∈ tvs1, p.1 = lw) ∧
          lw ≤ coh (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1) Ct⌝ ∨
        (badE g M ex ∗ ⌜lw < ex ∧ ∃ j : Nat, j < 8 ∧
          ex ≤ coh (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1) (Ct + j)⌝)) $$ [Hb]
  · rcases hcases with hall | ⟨j, t, v, hj, hlt, hwt⟩ | ⟨ti, hti, j, hj, hc⟩
    · obtain ⟨t0, v0, r0, rfl⟩ := tvs_cons hl1 (by decide)
      have h0 := loadRun_coh0 ws false false (srcsView ws (srcR 11)) Ct t0 v0 r0
      have ht0 : t0 = lw := hall (t0, v0) (List.mem_cons_self ..)
      imodintro; iexists 0; iframe Hb; ileft; ipureintro
      exact ⟨rfl, hall, by rw [← ht0]; exact h0⟩
    · have hj8 : j < 8 := by rw [← hl1]; exact (List.getElem?_eq_some_iff.1 hj).1
      have htM : 1 ≤ t ∧ t ≤ M.length := by obtain ⟨m, hm, _⟩ := hwt; exact msgAt_le hm
      have hcoh : t ≤ coh (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1) (Ct + j) :=
        (bytesAll_get hcohj hj).2
      have hwt' : wrB M (Ct + j) t := by simpa using hwt
      rcases wrC_cases hj8 hwt' with hCT | ⟨m, hm, hL, hb⟩
      · -- the points-to holds its `pend`: doom (plan R-a1), every other resource kept
        unfold cBagXE
        icases bsl_filter_take (pend g) (fun t => decide (lw < t) && decide (t ≠ 0) && isCT M t)
          (fun x => decide (lw < x) && decide (x ≠ t) && isCT M x) t (by simp [hlt, hCT]; omega)
          (fun x hx => by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
            exact ⟨⟨⟨hx.1.1, by omega⟩, hx.2⟩, hx.1.2⟩) (rng M) (mem_rng.2 htM) (nodup_rng M)
          $$ Hb with ⟨Hp, Hb⟩
        unfold lkCtxE
        icases Hctx with ⟨Hdoom, -⟩
        imod doom (E := ⊤) CoPset.subseteq_top g M t htM $$ [Hdoom Hp] with #Hd
        · iframe Hdoom Hp
        imodintro; iexists t; iframe Hb; iright; isplitl []
        · unfold badE; ileft; iexact Hd
        · ipureintro; exact ⟨hlt, j, hj8, hcoh⟩
      · -- the lock owns it: THE GUARD refutes it (`⟦t⟧ False`), every resource kept
        imodintro; iexists t; isplitl [Hb]
        · unfold cBagXE
          iapply bsl_filter_mono (pend g) _ _ (fun x hx => by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
            exact ⟨⟨hx.1.1, by omega⟩, hx.2⟩) (rng M) $$ Hb
        iright; isplitl []
        · unfold badE; iright; ipureintro; exact straddle_grd hm hL hj8 hb
        · ipureintro; exact ⟨hlt, j, hj8, hcoh⟩
    · exact absurd hc (hnoinv _ _)
  imod Hmode with ⟨%ex, Hb, Hm⟩
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨0, grd_intro (qLk_ld hnoC (fun ts ⟨_, _, _, h⟩ => by cases h))⟩
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e11 : s1.rd 11 = Y := by rw [LPstep_rd hs1 11 (.inl (by decide)), h11]
  have e9 : s1.rd 9 = X := by rw [LPstep_rd hs1 9 (.inl (by decide)), h9]
  have hlo' : lo ≤ coh (qPosts (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1)
      (regWL 7 [.DLdRes] ++ [LInstr])) Lk := by
    have := (loadRun_mono ws false false (srcsView ws (srcR 11)) Ct tvs1).2.2.2.2.2.2.2.2.2.2.1 Lk
    exact Nat.le_trans hlo this
  have hq7 : ∀ a, coh (qPosts (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1)
      (regWL 7 [.DLdRes] ++ [LInstr])) a = coh (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1) a :=
    fun a => rfl
  have hsp' : sp ≤ coh (qPosts (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1)
      (regWL 7 [.DLdRes] ++ [LInstr])) Pc := by
    have := (loadRun_mono ws false false (srcsView ws (srcR 11)) Ct tvs1).2.2.2.2.2.2.2.2.2.2.1 Pc
    exact Nat.le_trans hsp this
  iapply (lk_cs2E g M tk h hh s1 _ _ ev tvs1 lo lw ex sp ⟨hP1, hq1, by rw [hc1], e9, e11⟩ hlo' hsp' hnoC hlw)
  iframe Hctx Hbag Hpp Hb Hl
  simp only [hq7]
  iexact Hm

/-- **`pc = 5`: `sd a0,16(s1)`** (xv6 `lk->cpu = mycpu()`): its `pend` is in the claimed cpu bag. -/
theorem lk_cpu1E (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hh : h < 2)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo lw s0 : Nat)
    (hs : s.prog = b1c ∧ s.q = [] ∧ s.pc = 5 ∧ s.rd 9 = X ∧ s.rd 11 = Y)
    (hlo : lo ≤ coh ws Lk) (hvr : lw ≤ ws.wVrNew) (hs0 : s0 ≤ ws.wVwNew) (hnoC : noC ev)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :
    lkCtxE (GF := GF) g M tk ∗ C.obag g M tk h lo 0 ∗ cPtsE g M lw ∗ pPtsE g M s0 ∗
      lhA g π1c (wL1c M h) (qsLk M h) ws pr ev ⊢ wpKA g π1c (wL1c M h) (qsLk M) s (ΦE g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11⟩ := hs
  have hw := litW_x xs1c imgL M h
  have hX := p1c_at hprog
  iintro ⟨#Hctx, Hbag, Hc, Hpp, Hl⟩
  iapply (wpKA_sw (sz := 8) (rs2 := 10) (rs1 := 9) (off := 16) (base := Pc) hw
    (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_pc h9) (base_pc h9))
  iframe Hl
  inext
  iintro %ts %_ %hmsg %_ %hext _ _
  have hpre := (PF.stPreA_ge ws false false (srcsView ws (srcR 9)) (srcsView ws (srcR 10))).2.2.2.1
  have hts1 : 1 ≤ ts := by omega
  have hP := P_PT (toBytes_length _ _) hts1 hmsg
  have htsM := msgAt_le (msgAt_of hts1 hmsg)
  icases pPtsE_take (GF := GF) g M (by omega : s0 < ts) hP htsM $$ Hpp with ⟨Hpd, Hpp⟩
  imod shoot $$ Hpd with #Hsh
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨⟨0, grd_intro (qLk_noC (noC_snoc hnoC (st_nonC Pc_ne_Ct _ _ _ _)))⟩, grd_intro ok_pc⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hvr' := st_vrNew ws (srcsView ws (srcR 9)) (max (srcsView ws (srcR 9)) (srcsView ws (srcR 10))) Pc
    (toBytes (s.rd 10) 8).length ts
  iapply (lk_cs1E g M tk h hh s1 _ _ _ lo lw ts
    ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 9 (.inr rfl), h9], by rw [LPstep_rd hs1 11 (.inr rfl), h11]⟩
    (Nat.le_trans hlo (st_coh _ _ _ _ _ _ Lk))
    (st_coh0 _ _ _ _ (toBytes (s.rd 10) 8).length _ (by rw [toBytes_length]; decide))
    (by rw [hvr']; exact hvr) (noC_snoc hnoC (st_nonC Pc_ne_Ct _ _ _ _)) hnoinv)
  iframe Hctx Hbag Hc Hpp Hl

end cs

end Weak.Prom.OA.EC
