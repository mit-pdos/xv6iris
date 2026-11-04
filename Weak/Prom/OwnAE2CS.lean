/-
Weak/Prom: **E-a2 — an acquirer's critical section, cpu field and plain release on the runtime-born lock** (stage
E-a2; OwnAE1cCS.lean's steps — (1c)'s text, `pc` shifted by 3 — over the owners of OwnAE2Defs.lean and the protocol
`lkB5 b` built at initlock).

* the field READ (`cs1_5`, R-a1): a byte above the owned latest write came from a message touching the field —
  in the points-to's bag (ordinary doom; every other resource kept) or touching a lock word (`π4` refutes it under
  the guard, `⟦t⟧ False`);
* the field STORE (`cs2_5`) moves the points-to; `latestC3` or doom;
* the RELEASE (`rel5`, release-class through `fence rw,w`): the deposit in its slot — `rSlot5 r` is in `lkB5 b`
  because `r` lies above the hart's floor, above the birth.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAE2H0

namespace Weak.Prom.OA.E2

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y Z)
open Weak.Prom.OA.P (L1 SV bthAt msgAt_of)
open Weak.Prom.OA.C (Pc alg_pc base_pc st_nonC Pc_ne_Ct Lk_ne_Ct st_coh st_coh0 st_vwOld st_vrNew)
open Weak.Prom.OA.E
open Weak.Prom.OA.EP (isCO cB cBX cB_X c_cls straddle4_grd ok4_lk ok4_ct π4)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-- `cld_cases` (OwnALockLib.lean) for a latest write that is a text-shaped field store of any hart. -/
theorem cld3 {img : Image} {M : List PMsg} {vpre lw : Nat} (hlwm : isC3 M lw = true) (hv : lw ≤ vpre) :
    ∀ (k : Nat) (tvs : List (Nat × BitVec 8)), k + tvs.length ≤ 8 →
      bytesAll (fun a t v => memByte img M t a = some v ∧
        ((∃ fl, vpre ≤ fl ∧ ¬ writesIn M a t fl) ∨ (∃ fl, vpre ≤ fl ∧ invalRead M a t fl))) (Ct + k) tvs →
      (∀ p ∈ tvs, p.1 = lw) ∨
      (∃ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) ∧ lw < t ∧ wrB M (Ct + k + j) t) ∨
      (∃ ti, lw < ti ∧ ∃ j : Nat, j < 8 ∧ cmoAt M isInvalK ti (Ct + j)) := by
  intro k tvs
  induction tvs generalizing k with
  | nil => intro _ _; exact .inl (by simp)
  | cons tv r ih =>
    obtain ⟨t, v⟩ := tv
    intro hlen ⟨⟨hb, hr⟩, hrest⟩
    have hk : k < 8 := by simp at hlen; omega
    have hlwm' : lw = 0 ∨ ∃ m, msgAt M lw = some m ∧ (m.byteAt (Ct + k)).isSome = true ∧ notCmo m.cls = true := by
      obtain ⟨m, hm, h1, h2, h3, _⟩ := clsB_iff.1 hlwm
      refine .inr ⟨m, hm, ?_, by rw [h3]; rfl⟩
      rw [← h1, byteAt_off rfl, List.getElem?_eq_getElem (by omega)]; rfl
    have hsrc : t = lw ∨ (lw < t ∧ wrB M (Ct + k) t) ∨ (∃ ti, lw < ti ∧ cmoAt M isInvalK ti (Ct + k)) := by
      rcases hr with ⟨fl, hfl, h⟩ | ⟨fl, hfl, h⟩
      · exact src_ge_lw hlwm' (by omega) hb (.inl h)
      · exact src_ge_lw hlwm' (by omega) hb (.inr h)
    rcases hsrc with heq | ⟨hlt, hw⟩ | ⟨ti, hti, hc⟩
    · rcases ih (k + 1) (by simp at hlen; omega)
        (by rw [(by omega : Ct + ((k + 1 : Nat) : Int) = Ct + k + 1)]; exact hrest) with h | ⟨j, t', v', hj, hlt', hw'⟩ | hci
      · refine .inl (fun p hp => ?_)
        rcases List.mem_cons.1 hp with rfl | hp
        · exact heq
        · exact h p hp
      · refine .inr (.inl ⟨j + 1, t', v', by simpa using hj, hlt', ?_⟩)
        rw [show Ct + k + ((j + 1 : Nat) : Int) = Ct + ((k + 1 : Nat) : Int) + j by omega]; exact hw'
      · exact .inr (.inr hci)
    · exact .inr (.inl ⟨0, t, v, rfl, hlt, by simpa using hw⟩)
    · exact .inr (.inr ⟨ti, hti, k, hk, hc⟩)

theorem ok4_pc {d : List (BitVec 8)} {tid : Option Nat} {c : PClass} (hd : d.length = 8) :
    π4.okMsg ⟨Pc, d, tid, c⟩ :=
  ⟨(fun ht => by rw [tchB_far (.inr (by simp [Pc, Lk, X]))] at ht; cases ht),
   (fun ht => by rw [tchB_far (.inl (by simp [hd, Pc, Lk, L1, X, Z]))] at ht; cases ht)⟩

section cs

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]

/-- The guarded trace invariant, or doom. -/
def QE5 (g : AGN) (M : List PMsg) (ev : Trace) : IProp GF := iprop(⌜∃ V, grd π4 img5 M V (q5 M ev)⌝ ∨ dshot g)

instance (g : AGN) (M : List PMsg) (ev : Trace) : Persistent (QE5 (GF := GF) g M ev) := by
  unfold QE5; infer_instance

theorem gq5_snoc {M : List PMsg} {ev : Trace} {e : PEv} (he : (∀ tvs, ¬ isCLd e tvs) ∧ (∀ ts, ¬ isCSt e ts))
    (h : ∃ V, grd π4 img5 M V (q5 M ev)) : ∃ V, grd π4 img5 M V (q5 M (ev ++ [e])) :=
  let ⟨V, hV⟩ := h; ⟨V, grd_imp (fun q => q5_snoc q he) hV⟩

/-- **THE RELEASE** (`pc = 14`, `sw zero,0(s1)`, release-class through the fence) and the end: the deposit. -/
theorem rel5 (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) (h : Nat) (hh : h < 3) (b : Nat)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo lw sp : Nat)
    (hs : s.prog = b5h ∧ s.q = [] ∧ s.pc = 14 ∧ s.rd 9 = X ∧ s.rd 11 = Y)
    (hbl : b ≤ lo) (hlo : lo ≤ coh ws Lk) (hvw : lw ≤ ws.wVwNew) (hsp : sp ≤ ws.wVwNew) :
    ctx5 (GF := GF) g M sv ak ∗ lkB5 g M sv ak b ∗ obg g M sv.tk h lo 0 ∗ cPts5 g M lw ∗ pPts5 g M sp ∗
      QE5 g M ev ∗ lhA g π4 (w5 M h) (qs5 M h) ws pr ev ⊢ wpKA g π4 (w5 M h) (qs5 M) s (Φ5 g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11⟩ := hs
  have hw := litW_x xs5 img5 M h
  iintro ⟨#Hctx, #Hlk, Hbag, Hc, Hpp, #HQ, Hl⟩
  iapply (wpKA_sw (sz := 4) (rs2 := 0) (rs1 := 9) (off := 0) (base := Lk) hw
    (litAg_x hq (p5h_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_of h9 (by decide) (by decide))
    (base_of h9 (by decide)))
  iframe Hl
  inext
  iintro %r %_ %hmsg %hcoh %hext _ _
  have hd0 : toBytes (s.rd 0) 4 = toBytes 0 4 := rfl
  rw [hd0] at hmsg hcoh
  have hc0 : coh ws Lk < r := by have := cohBelow_at (j := 0) hcoh (by decide); simpa using this
  have hmr := msgAt_of (by omega) hmsg
  obtain ⟨hR, hbyH⟩ := R2_of hh hmr
  have hrM := msgAt_le hmr
  have hvr : ws.wVwNew < r := by
    have := (PF.stPreA_ge ws false false (srcsView ws (srcR 9)) (srcsView ws (srcR 0))).2.2.2.1
    omega
  unfold obg
  icases Hbag with ⟨-, HbL⟩
  unfold bgL
  icases bsl_filter_take (fun t => token (sv.tk t))
    (fun t => decide (lo < t) && decide (t ≠ 0) && (isA2 M t || isR2 M t) && byH M h t) (fun _ => false) r
    (by simp [show lo < r by omega, show r ≠ 0 by omega, hR, hbyH]) (fun _ h => by cases h) (rng M)
    (mem_rng.2 hrM) (nodup_rng M) $$ HbL with ⟨Ht, -⟩
  unfold lkB5
  icases Hlk with ⟨Hrs, -⟩
  ihave #Hslot := bsl_mem (F := fun r => rSlot5 g M sv.tk r)
    (List.mem_filter.2 ⟨mem_rng.2 hrM, by simp [hR]; omega⟩) $$ Hrs
  unfold rSlot5
  imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hslot with ⟨Hb, Hclose⟩
  icases Hb with (Hp | ⟨_, Ht', _⟩)
  rotate_left
  · iexfalso; iapply token_exclusive; iframe Ht Ht'
  imod shoot $$ Hp with #Hsh
  ihave Hpr := pPts5_mono (GF := GF) g M (s := sp) (s' := r) (by omega) $$ Hpp
  imod Hclose $$ [Ht Hc Hpr] with -
  · iright; iframe Hsh Ht; ileft; unfold Rs5; iframe Hpr; iexists lw; iframe Hc; ipureintro; omega
  imodintro
  isplitl []
  · unfold QE5
    icases HQ with (%hQ | #Hd)
    · ileft; ipureintro; exact ⟨gq5_snoc (st_nonC Lk_ne_Ct _ _ _ _) hQ, grd_intro (ok4_lk (toBytes_length 0 4))⟩
    · iright; iexact Hd
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s' %hs' _ _
  imodintro
  iintro Hl
  obtain ⟨hP', hc', hq'⟩ := LPstep_at hs' hprog (by rw [hpc])
  have hend : s'.prog.length ≤ s'.pc := by rw [hP', hc']; decide
  iapply (wpKA_end (v := ()) (litAg_xn hq' (fun x hx => by rw [p5h_at hP', hc'] at hx; cases hx)) hq' hend
    (by show litDone s' = some (); unfold litDone; rw [if_pos ⟨hq', hend⟩]))
  iframe Hl
  imodintro
  ileft; ipureintro; exact ⟨0, grd_intro trivial⟩

/-- `pc = 12..13`: `sd zero,16(s1)` (its `pend` from the cpu field's bag), `fence rw,w`, then the release. -/
theorem cpu0_5 (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) (h : Nat) (hh : h < 3) (b : Nat)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo lw sp : Nat)
    (hs : s.prog = b5h ∧ s.q = [] ∧ s.pc = 12 ∧ s.rd 9 = X ∧ s.rd 11 = Y)
    (hbl : b ≤ lo) (hlo : lo ≤ coh ws Lk) (hvw : lw ≤ ws.wVwOld) (hsp : sp ≤ coh ws Pc) :
    ctx5 (GF := GF) g M sv ak ∗ lkB5 g M sv ak b ∗ obg g M sv.tk h lo 0 ∗ cPts5 g M lw ∗ pPts5 g M sp ∗
      QE5 g M ev ∗ lhA g π4 (w5 M h) (qs5 M h) ws pr ev ⊢ wpKA g π4 (w5 M h) (qs5 M) s (Φ5 g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11⟩ := hs
  have hw := litW_x xs5 img5 M h
  iintro ⟨#Hctx, #Hlk, Hbag, Hc, Hpp, #HQ, Hl⟩
  iapply (wpKA_sw (sz := 8) (rs2 := 0) (rs1 := 9) (off := 16) (base := Pc) hw
    (litAg_x hq (p5h_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_pc h9) (base_pc h9))
  iframe Hl
  inext
  iintro %ts %_ %hmsg %hcoh %_ _ _
  rw [toBytes_length] at hcoh
  have hc0 : coh ws Pc < ts := by have := cohBelow_at (j := 0) hcoh (by decide); simpa using this
  have hmt := msgAt_of (by omega) hmsg
  icases pPts5_take (GF := GF) g M (by omega : sp < ts) (PO_of (toBytes_length _ _) hmt) (msgAt_le hmt) $$ Hpp
    with ⟨Hpd, Hpp⟩
  imod shoot $$ Hpd with #Hsh
  imodintro
  isplitl []
  · unfold QE5
    icases HQ with (%hQ | #Hd)
    · ileft; ipureintro; exact ⟨gq5_snoc (st_nonC Pc_ne_Ct _ _ _ _) hQ, grd_intro (ok4_pc (toBytes_length _ _))⟩
    · iright; iexact Hd
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hvo := st_vwOld ws (srcsView ws (srcR 9)) (max (srcsView ws (srcR 9)) (srcsView ws (srcR 0))) Pc
    (toBytes (s.rd 0) 8).length ts
  have hlo' := Nat.le_trans hlo (st_coh ws (srcsView ws (srcR 9)) (max (srcsView ws (srcR 9)) (srcsView ws (srcR 0)))
    Pc (toBytes (s.rd 0) 8).length ts Lk)
  -- `fence rw,w`
  iapply (wpKA_fence hw (litAg_x hq1 (p5h_at hP1) (by rw [hc1]; rfl) rfl) hq1 (by rw [hP1, hc1]; rfl))
  iframe Hl
  inext
  iintro %s2 %hs2 _ _
  imodintro
  iintro Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  iapply (rel5 g M sv ak h hh b s2 (instrR (fencePost (instrR (acqPost (storeRun ws false (srcsView ws (srcR 9))
    (max (srcsView ws (srcR 9)) (srcsView ws (srcR 0))) Pc (toBytes (s.rd 0) 8).length ts) false ts)) true true false
    true)) _ _ lo lw ts ⟨hP2, hq2, hc2, by rw [LPstep_rd hs2 9 (.inr rfl),
    LPstep_rd hs1 9 (.inr rfl), h9], by rw [LPstep_rd hs2 11 (.inr rfl), LPstep_rd hs1 11 (.inr rfl), h11]⟩ hbl hlo'
    (by simp only [instrR_vwNew, fence_vwNew, ite_true]; rw [hvo]; omega)
    (by simp only [instrR_vwNew, fence_vwNew, ite_true]; rw [hvo]; omega))
  iframe Hctx Hlk Hbag Hc Hpp Hl
  unfold QE5
  icases HQ with (%hQ | #Hd)
  · ileft; ipureintro; exact gq5_snoc (st_nonC Pc_ne_Ct _ _ _ _) hQ
  · iright; iexact Hd

/-- The BAD mode after a field read above `lw`: doomed, or the guarded refutation `⟦ex⟧ False`. -/
def bad5 (g : AGN) (M : List PMsg) (ex : Nat) : IProp GF := iprop(dshot g ∨ ⌜grd π4 img5 M ex False⌝)

instance (g : AGN) (M : List PMsg) (ex : Nat) : Persistent (bad5 (GF := GF) g M ex) := by
  unfold bad5; infer_instance

/-- `pc = 10..11`: `addi t2,t2,1; sd t2,(a1)`, then the rest.  `ex` is the message of a bad read (`0`: clean). -/
theorem cs2_5 (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) (h : Nat) (hh : h < 3) (hh0 : h ≠ 0)
    (b : Nat) (s : LP) (ws : PState) (pr : GSet Nat) (ev0 : Trace) (tvs1 : List (Nat × BitVec 8)) (lo lw ex sp : Nat)
    (hs : s.prog = b5h ∧ s.q = [] ∧ s.pc = 10 ∧ s.rd 9 = X ∧ s.rd 11 = Y)
    (hbl : b ≤ lo) (hlo : lo ≤ coh ws Lk) (hsp : sp ≤ coh ws Pc) (hnoC : noC ev0) (hlw : gd M lw) :
    ctx5 (GF := GF) g M sv ak ∗ lkB5 g M sv ak b ∗ obg g M sv.tk h lo 0 ∗ pPts5 g M sp ∗
      ([∗list] t ∈ cBX M lw ex, pend g t) ∗
      (⌜ex = 0 ∧ (∀ p ∈ tvs1, p.1 = lw) ∧ lw ≤ coh ws Ct⌝ ∨
        (bad5 g M ex ∗ ⌜lw < ex ∧ ∃ j : Nat, j < 8 ∧ ex ≤ coh ws (Ct + j)⌝)) ∗
      lhA g π4 (w5 M h) (qs5 M h) ws pr (ev0 ++ [(LLoad false false Ct tvs1 (srcR 11), none)]) ⊢
      wpKA g π4 (w5 M h) (qs5 M) s (Φ5 g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11⟩ := hs
  have hw := litW_x xs5 img5 M h
  iintro ⟨#Hctx, #Hlk, Hbag, Hpp, Hb, Hmode, Hl⟩
  -- `addi t2,t2,1`
  iapply (wpKA_alui hw (litAg_x hq (p5h_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (by decide))
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
    (litAg_x hq1 (p5h_at hP1) (by rw [hc1]; rfl) rfl) hq1 (by rw [hP1, hc1]; rfl)
    (alg_of e11 (by decide) (by decide)) (base_of e11 (by decide)))
  iframe Hl
  inext
  iintro %ts %_ %hmsg %hcoh %_ _ _
  rw [toBytes_length] at hcoh
  have hcj : ∀ j : Nat, j < 8 → coh ws (Ct + j) < ts := fun j hj => by have h := cohBelow_at hcoh hj; exact h
  have hmt := msgAt_of (by have := hcj 0 (by decide); omega) hmsg
  have hC := C3_of hh (toBytes_length _ _) hmt
  have hCO := C3_CO hC
  have htsM := msgAt_le hmt
  ihave HQ : |={⊤}=> QE5 g M (ev0 ++ [(LLoad false false Ct tvs1 (srcR 11), none)] ++
      [(LStore false false Ct (toBytes (s1.rd 7) 8) (srcR 11) (srcR 7), some ts)]) ∗ shot g ts ∗
      ([∗list] t ∈ cB M ts, pend g t) $$ [Hb Hmode]
  · icases Hmode with (%hcl | ⟨#Hbad, %hra⟩)
    · obtain ⟨rfl, hall, hlc⟩ := hcl
      have hlts : lw < ts := by have := hcj 0 (by decide); simp at this; omega
      unfold cBX
      icases bsl_filter_take (pend g) (fun t => decide (lw < t) && decide (t ≠ 0) && isCO M t)
        (fun t => decide (lw < t) && decide (t ≠ ts) && isCO M t) ts (by simp [hlts, hCO]; omega)
        (fun t ht => by simp at ht; exact ⟨by simp [ht.1.1, ht.2]; omega, ht.1.2⟩) (rng M)
        (mem_rng.2 htsM) (nodup_rng M) $$ Hb with ⟨Hp, Hb⟩
      imod shoot $$ Hp with #Hsh
      by_cases hg : ∃ u, lw < u ∧ u < ts ∧ isC3 M u = true
      · -- a field store between the read and the write: its `pend` is held, doom (plan R-a1)
        obtain ⟨u, hu1, hu2, hu3⟩ := hg
        have huM : 1 ≤ u ∧ u ≤ M.length := by obtain ⟨m, hm, _⟩ := clsB_iff.1 hu3; exact msgAt_le hm
        icases bsl_filter_take (pend g) (fun t => decide (lw < t) && decide (t ≠ ts) && isCO M t)
          (fun t => decide (lw < t) && decide (t ≠ ts) && decide (t ≠ u) && isCO M t) u
          (by simp [hu1, C3_CO hu3]; omega)
          (fun t ht => by simp at ht; exact ⟨by simp [ht.1.1.1, ht.1.1.2, ht.2], ht.1.2⟩) (rng M)
          (mem_rng.2 huM) (nodup_rng M) $$ Hb with ⟨Hu, Hb⟩
        unfold ctx5
        icases Hctx with ⟨Hdoom, -⟩
        imod doom (E := ⊤) CoPset.subseteq_top g M u huM $$ [Hdoom Hu] with #Hd
        · iframe Hdoom Hu
        imodintro
        isplitr
        · unfold QE5; iright; iexact Hd
        iframe Hsh
        unfold cB
        iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
          exact ⟨⟨⟨by omega, by omega⟩, by omega⟩, ht.2⟩) (rng M) $$ Hb
      · have hl : latestC3 M lw ts := ⟨hlw.1, hlts, fun u h1 h2 => by
          cases h3 : isC3 M u
          · rfl
          · exact absurd ⟨u, h1, h2, h3⟩ hg⟩
        imodintro
        isplitr
        · unfold QE5; ileft; ipureintro; exact ⟨0, grd_intro (q5_pair hnoC hall hl hlw)⟩
        iframe Hsh
        unfold cB
        iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
          exact ⟨⟨by omega, by omega⟩, ht.2⟩) (rng M) $$ Hb
    · obtain ⟨hlex, j, hj, hexc⟩ := hra
      have hext : ex < ts := Nat.lt_of_le_of_lt hexc (hcj j hj)
      unfold cBX
      icases bsl_filter_take (pend g) (fun t => decide (lw < t) && decide (t ≠ ex) && isCO M t)
        (fun t => decide (lw < t) && decide (t ≠ ex) && decide (t ≠ ts) && isCO M t) ts
        (by simp [hCO]; omega)
        (fun t ht => by simp at ht; exact ⟨by simp [ht.1.1.1, ht.1.1.2, ht.2], ht.1.2⟩) (rng M)
        (mem_rng.2 htsM) (nodup_rng M) $$ Hb with ⟨Hp, Hb⟩
      imod shoot $$ Hp with #Hsh
      imodintro
      isplitr
      · unfold QE5 bad5
        icases Hbad with (#Hd | %hgf)
        · iright; iexact Hd
        · ileft; ipureintro; exact ⟨ex, fun hv => (hgf hv).elim⟩
      iframe Hsh
      unfold cB
      iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
        exact ⟨⟨⟨by omega, by omega⟩, by omega⟩, ht.2⟩) (rng M) $$ Hb
  imod HQ with ⟨#HQ, #Hsh, Hb⟩
  imodintro
  isplitl []
  · unfold QE5
    icases HQ with (%hQ | #Hd)
    · ileft; ipureintro; exact ⟨hQ, grd_intro (ok4_ct (toBytes_length _ _))⟩
    · iright; iexact Hd
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s2 %hs2 _ _
  imodintro
  iintro Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have hst := storeRun_mono (instrR (regWP ws 7 (srcR 7))) false (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 11))
    (max (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 11)) (srcsView (instrR (regWP ws 7 (srcR 7))) (srcR 7)))
    Ct (toBytes (s1.rd 7) 8).length ts
  have hgd : gd M ts := ⟨hC, .inr (by simp [tidAt, hmt]; omega)⟩
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
  iapply (cpu0_5 g M sv ak h hh b s2 _ _ _ lo ts sp ⟨hP2, hq2, by rw [hc2], by rw [LPstep_rd hs2 9 (.inr rfl), e9],
    by rw [LPstep_rd hs2 11 (.inr rfl), e11]⟩ hbl hlo' hvw' hsp')
  iframe Hctx Hlk Hbag HQ Hl Hpp
  unfold cPts5
  iframe Hb
  ipureintro; exact hgd

/-- **THE CRITICAL SECTION'S LOAD** (`pc = 9`, `ld t2,(a1)`, plan R-a1): the owned read of the field, per byte. -/
theorem cs1_5 (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) (h : Nat) (hh : h < 3) (hh0 : h ≠ 0)
    (b : Nat) (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo lw sp : Nat)
    (hs : s.prog = b5h ∧ s.q = [] ∧ s.pc = 9 ∧ s.rd 9 = X ∧ s.rd 11 = Y)
    (hbl : b ≤ lo) (hlo : lo ≤ coh ws Lk) (hsp : sp ≤ coh ws Pc) (hvr : lw ≤ ws.wVrNew) (hnoC : noC ev)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :
    ctx5 (GF := GF) g M sv ak ∗ lkB5 g M sv ak b ∗ obg g M sv.tk h lo 0 ∗ cPts5 g M lw ∗ pPts5 g M sp ∗
      lhA g π4 (w5 M h) (qs5 M h) ws pr ev ⊢ wpKA g π4 (w5 M h) (qs5 M) s (Φ5 g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11⟩ := hs
  have hw := litW_x xs5 img5 M h
  iintro ⟨#Hctx, #Hlk, Hbag, Hc, Hpp, Hl⟩
  unfold cPts5
  icases Hc with ⟨%hlw, Hb⟩
  rw [cB_X]
  iapply (wpKA_ld (sz := 8) (sgn := true) (rd := 7) (rs1 := 11) (off := 0) (base := Ct) hw
    (litAg_x hq (p5h_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
    (alg_of h11 (by decide) (by decide)) (base_of h11 (by decide)))
  iframe Hl
  inext
  iintro %tvs1 %hl1 %hlo1 _ _
  have hvp : lw ≤ ldPre ws false false (srcsView ws (srcR 11)) :=
    Nat.le_trans hvr (PF.ldPre_ge ws false false (srcsView ws (srcR 11))).2.1
  have hcases := cld3 (img := img5) hlw.1 hvp 0 tvs1 (by rw [hl1]; decide)
    (by have := loadOk_weak hlo1; simpa using this)
  have hcohj := (loadBytes_coh false (ldPre ws false false (srcsView ws (srcR 11))) ws Ct tvs1).2
  -- THE MODE after the read: clean, or bad (doomed / guarded-false); and the load's obligation
  ihave Hmode : |={⊤}=> ∃ ex, ([∗list] t ∈ cBX M lw ex, pend g t) ∗
      QE5 g M (ev ++ [(LLoad false false Ct tvs1 (srcR 11), none)]) ∗
      (⌜ex = 0 ∧ (∀ p ∈ tvs1, p.1 = lw) ∧
          lw ≤ coh (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1) Ct⌝ ∨
        (bad5 g M ex ∗ ⌜lw < ex ∧ ∃ j : Nat, j < 8 ∧
          ex ≤ coh (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1) (Ct + j)⌝)) $$ [Hb]
  · rcases hcases with hall | ⟨j, t, v, hj, hlt, hwt⟩ | ⟨ti, hti, j, hj, hc⟩
    · obtain ⟨t0, v0, r0, rfl⟩ := tvs_cons hl1 (by decide)
      have h0 := loadRun_coh0 ws false false (srcsView ws (srcR 11)) Ct t0 v0 r0
      have ht0 : t0 = lw := hall (t0, v0) (List.mem_cons_self ..)
      imodintro; iexists 0; iframe Hb
      isplitr
      · unfold QE5; ileft; ipureintro
        exact ⟨0, grd_intro (q5_ld hnoC (fun p hp => by rw [hall p hp]; exact hlw))⟩
      ileft; ipureintro
      exact ⟨rfl, hall, by rw [← ht0]; exact h0⟩
    · have hj8 : j < 8 := by rw [← hl1]; exact (List.getElem?_eq_some_iff.1 hj).1
      have htM : 1 ≤ t ∧ t ≤ M.length := by obtain ⟨m, hm, _⟩ := hwt; exact msgAt_le hm
      have hcoh : t ≤ coh (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1) (Ct + j) :=
        (bytesAll_get hcohj hj).2
      obtain ⟨m, hm, hb⟩ := hwt
      rcases c_cls hm hj8 (by simpa using hb) with hCO | hL
      · -- the points-to holds its `pend`: doom (plan R-a1), every other resource kept
        unfold cBX
        icases bsl_filter_take (pend g) (fun t => decide (lw < t) && decide (t ≠ 0) && isCO M t)
          (fun x => decide (lw < x) && decide (x ≠ t) && isCO M x) t (by simp [hlt, hCO]; omega)
          (fun x hx => by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
            exact ⟨⟨⟨hx.1.1, by omega⟩, hx.2⟩, hx.1.2⟩) (rng M) (mem_rng.2 htM) (nodup_rng M)
          $$ Hb with ⟨Hp, Hb⟩
        unfold ctx5
        icases Hctx with ⟨Hdoom, -⟩
        imod doom (E := ⊤) CoPset.subseteq_top g M t htM $$ [Hdoom Hp] with #Hd
        · iframe Hdoom Hp
        imodintro; iexists t; iframe Hb
        isplitr
        · unfold QE5; iright; iexact Hd
        iright; isplitl []
        · unfold bad5; ileft; iexact Hd
        · ipureintro; exact ⟨hlt, j, hj8, hcoh⟩
      · -- a lock word owns it: THE GUARD refutes it (`⟦t⟧ False`), every resource kept
        have hgf := straddle4_grd (img := img5) hm hL hj8 (by simpa using hb)
        imodintro; iexists t; isplitl [Hb]
        · unfold cBX
          iapply bsl_filter_mono (pend g) _ _ (fun x hx => by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
            exact ⟨⟨hx.1.1, by omega⟩, hx.2⟩) (rng M) $$ Hb
        isplitr
        · unfold QE5; ileft; ipureintro; exact ⟨t, fun hv => (hgf hv).elim⟩
        iright; isplitl []
        · unfold bad5; iright; ipureintro; exact hgf
        · ipureintro; exact ⟨hlt, j, hj8, hcoh⟩
    · exact absurd hc (hnoinv _ _)
  imod Hmode with ⟨%ex, Hb, #HQ, Hm⟩
  imodintro
  isplitr
  · unfold QE5
    icases HQ with (%hQ | #Hd)
    · ileft; ipureintro; exact hQ
    · iright; iexact Hd
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hmono := (loadRun_mono ws false false (srcsView ws (srcR 11)) Ct tvs1).2.2.2.2.2.2.2.2.2.2.1
  have hq7 : ∀ a, coh (qPosts (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1)
      (regWL 7 [.DLdRes] ++ [LInstr])) a = coh (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1) a :=
    fun a => rfl
  iapply (cs2_5 g M sv ak h hh hh0 b s1 _ _ ev tvs1 lo lw ex sp ⟨hP1, hq1, by rw [hc1],
    by rw [LPstep_rd hs1 9 (.inl (by decide)), h9], by rw [LPstep_rd hs1 11 (.inl (by decide)), h11]⟩ hbl
    (by rw [hq7]; exact Nat.le_trans hlo (hmono Lk)) (by rw [hq7]; exact Nat.le_trans hsp (hmono Pc)) hnoC hlw)
  iframe Hctx Hlk Hbag Hpp Hb Hl
  simp only [hq7]
  iexact Hm

/-- **`pc = 8`: `sd a0,16(s1)`** (xv6 `lk->cpu = mycpu()`): its `pend` is in the claimed cpu bag. -/
theorem cpu1_5 (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) (h : Nat) (hh : h < 3) (hh0 : h ≠ 0)
    (b : Nat) (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lo lw s0 : Nat)
    (hs : s.prog = b5h ∧ s.q = [] ∧ s.pc = 8 ∧ s.rd 9 = X ∧ s.rd 11 = Y)
    (hbl : b ≤ lo) (hlo : lo ≤ coh ws Lk) (hvr : lw ≤ ws.wVrNew) (hs0 : s0 ≤ ws.wVwNew) (hnoC : noC ev)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :
    ctx5 (GF := GF) g M sv ak ∗ lkB5 g M sv ak b ∗ obg g M sv.tk h lo 0 ∗ cPts5 g M lw ∗ pPts5 g M s0 ∗
      lhA g π4 (w5 M h) (qs5 M h) ws pr ev ⊢ wpKA g π4 (w5 M h) (qs5 M) s (Φ5 g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11⟩ := hs
  have hw := litW_x xs5 img5 M h
  iintro ⟨#Hctx, #Hlk, Hbag, Hc, Hpp, Hl⟩
  iapply (wpKA_sw (sz := 8) (rs2 := 10) (rs1 := 9) (off := 16) (base := Pc) hw
    (litAg_x hq (p5h_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_pc h9) (base_pc h9))
  iframe Hl
  inext
  iintro %ts %_ %hmsg %_ %hext _ _
  have hpre := (PF.stPreA_ge ws false false (srcsView ws (srcR 9)) (srcsView ws (srcR 10))).2.2.2.1
  have hmt := msgAt_of (by omega) hmsg
  icases pPts5_take (GF := GF) g M (by omega : s0 < ts) (PO_of (toBytes_length _ _) hmt) (msgAt_le hmt) $$ Hpp
    with ⟨Hpd, Hpp⟩
  imod shoot $$ Hpd with #Hsh
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨⟨0, grd_intro (q5_noLd (noC_noLd (noC_snoc hnoC (st_nonC Pc_ne_Ct _ _ _ _))))⟩,
      grd_intro (ok4_pc (toBytes_length _ _))⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hvr' := st_vrNew ws (srcsView ws (srcR 9)) (max (srcsView ws (srcR 9)) (srcsView ws (srcR 10))) Pc
    (toBytes (s.rd 10) 8).length ts
  iapply (cs1_5 g M sv ak h hh hh0 b s1 _ _ _ lo lw ts
    ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 9 (.inr rfl), h9], by rw [LPstep_rd hs1 11 (.inr rfl), h11]⟩ hbl
    (Nat.le_trans hlo (st_coh _ _ _ _ _ _ Lk))
    (st_coh0 _ _ _ _ (toBytes (s.rd 10) 8).length _ (by rw [toBytes_length]; decide))
    (by rw [hvr']; exact hvr) (noC_snoc hnoC (st_nonC Pc_ne_Ct _ _ _ _)) hnoinv)
  iframe Hctx Hlk Hbag Hc Hpp Hl

end cs

end Weak.Prom.OA.E2
