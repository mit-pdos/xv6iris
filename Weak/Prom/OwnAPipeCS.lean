/-
Weak/Prom: **G4 target (4) on track (a): hart 1's critical section under L2 and xv6's release of L2** (stage S4a
part 4; plan rev 7 §4 G4 (4); §3 "Points-to", R-a1).

From `pc = 9` with the field's points-to `cPts c` claimed from L2 (`c` hart 0's initialisation, holding 5, below the
view):
* `ld t2,(a1)` (`h1_cld`) — THE OWNED READ (`cld_cases`): every byte from `c` (THE VERDICT: the value is 5), or a
  field message above `c` (its `pend` is in the bag: R-a1 doom, the write floor keeps the later store's `pend`), or
  dead (free mode);
* `addi`, `sd t2,(a1)` (`h1_cst`) — the store's `pend` from the bag (above the floor and not the surrendered one);
* `fence rw,w`, `sw zero,0(s1)` (`h1_rel`) — the release: its `pend` is hart 1's own (no later acquirer of L2 in this
  test, so nothing is deposited; the deposit at a release-class store is (1c)'s `lk_rel1c` and L1's `l1_deposit`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAPipeFree

namespace Weak.Prom.OA.P

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y Z)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-- The values of bytes all read from `lw`. -/
theorem vals_of_src {img : Image} {M : List PMsg} {x : Int} {lw : Nat} {mw : PMsg}
    (hmw : msgAt M lw = some mw) (hpa : mw.pa = x) :
    ∀ (k : Nat) (tvs : List (Nat × BitVec 8)), k + tvs.length ≤ mw.data.length →
      bytesAll (fun a t v => memByte img M t a = some v) (x + k) tvs → (∀ p ∈ tvs, p.1 = lw) →
      tvs.map Prod.snd = (mw.data.drop k).take tvs.length := by
  intro k tvs
  induction tvs generalizing k with
  | nil => intro _ _ _; simp
  | cons tv r ih =>
    obtain ⟨t, v⟩ := tv
    intro hlen ⟨hb, hrest⟩ hall
    have hk : k < mw.data.length := by simp at hlen; omega
    have heq : t = lw := hall (t, v) (List.mem_cons_self ..)
    have ih' := ih (k + 1) (by simp at hlen; omega)
      (by rw [(by omega : x + ((k + 1 : Nat) : Int) = x + k + 1)]; exact hrest)
      (fun p hp => hall p (List.mem_cons_of_mem _ hp))
    rw [heq] at hb
    obtain ⟨kk, hkk⟩ : ∃ kk, lw = kk + 1 := by
      cases lw with
      | zero => cases hmw
      | succ k => exact ⟨k, rfl⟩
    rw [hkk] at hb hmw
    simp only [msgAt] at hmw
    simp only [memByte, hmw, Option.bind_some] at hb
    rw [← hpa, byteAt_off rfl, List.getElem?_eq_getElem hk] at hb
    have hv' : mw.data[k] = v := Option.some.inj hb
    simp only [List.map_cons, List.length_cons]
    rw [List.drop_eq_getElem_cons hk, List.take_succ_cons, hv', ih']

theorem notCLd_ld_other {a : Int} (ha : a ≠ Ct) {tvs0 : List (Nat × BitVec 8)} {s : List Dsrc}
    (tvs : List (Nat × BitVec 8)) :
    isCLd (LLoad false false a tvs0 s, none) tvs → tvs.map Prod.snd = toBytes 5 8 := by
  rintro ⟨_, h⟩; injection h with h1; injection h1 with _ _ h3; exact absurd h3 ha

section cs

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]

/-- `pc = 13`: **xv6's release of L2** `sw zero,0(s1)` (its `pend` is hart 1's own), then the end. -/
theorem h1_rel (g : AGN) (M : List PMsg) (sv : SV) (hdd : g.dd = dd4 M)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace)
    (hs : s.prog = b4h ∧ s.q = [] ∧ s.pc = 13 ∧ s.rd 9 = X) :
    pCtx (GF := GF) g M sv ∗ r2Bag g M ∗ (⌜q4 ev⌝ ∨ dshot g) ∗
      lhA g Proto.triv (w4 M 1) (qs4 1) ws pr ev ⊢
      wpKA g Proto.triv (w4 M 1) qs4 s (Φ4 g M) := by
  obtain ⟨hprog, hq, hpc, h9⟩ := hs
  have hw := litW_x xs4 img4 M 1
  have hX := p4h_at hprog
  iintro ⟨#Hctx, Hr2, HQ, Hl⟩
  iapply (wpKA_sw (sz := 4) (rs2 := 0) (rs1 := 9) (off := 0) (base := Lk) hw
    (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_of h9 (by decide) (by decide))
    (base_of h9 (by decide)))
  iframe Hl
  inext
  iintro %r %_ %hmsg %hcoh %_ _ _
  have hd0 : toBytes (s.rd 0) 4 = toBytes 0 4 := rfl
  rw [hd0] at hmsg hcoh
  have hc0 : coh ws Lk < r := by
    have := cohBelow_at (j := 0) hcoh (by decide)
    simpa using this
  have hr1 : 1 ≤ r := by omega
  have hmr := msgAt_of hr1 hmsg
  have hk : knd M r = 5 := by rw [knd_of hmr]; exact kind_r2
  unfold r2Bag bagK
  icases bsl_filter_take (pend g) (fun t => decide (0 < t) && isK M 5 t) (fun _ => false) r
    (by simp [isK, hk]; omega) (fun _ h => by cases h) (rng M) (mem_rng.2 (msgAt_le hmr)) (nodup_rng M)
    $$ Hr2 with ⟨Hp, -⟩
  imod shoot $$ Hp with #Hsh
  imodintro
  isplitl [HQ]
  · icases HQ with (%hQ | #Hd)
    · ileft; ipureintro
      exact ⟨⟨0, grd_intro (q4_snoc hQ (notCLd_st))⟩, grd_intro trivial⟩
    · iright; iexact Hd
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s' %hs' _ _
  imodintro
  iintro Hl
  obtain ⟨hP', hc', hq'⟩ := LPstep_at hs' hprog (by rw [hpc])
  have hend : s'.prog.length ≤ s'.pc := by rw [hP', hc']; decide
  iapply (wpKA_end (v := ()) (litAg_xn hq' (fun x hx => by rw [p4h_at hP', hc'] at hx; cases hx)) hq' hend
    (by show litDone s' = some (); unfold litDone; rw [if_pos ⟨hq', hend⟩]))
  iframe Hl
  imodintro
  ileft; ipureintro; exact ⟨0, grd_intro trivial⟩

/-- `pc = 12`: `fence rw,w`. -/
theorem h1_fence (g : AGN) (M : List PMsg) (sv : SV) (hdd : g.dd = dd4 M)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace)
    (hs : s.prog = b4h ∧ s.q = [] ∧ s.pc = 12 ∧ s.rd 9 = X) :
    pCtx (GF := GF) g M sv ∗ r2Bag g M ∗ (⌜q4 ev⌝ ∨ dshot g) ∗
      lhA g Proto.triv (w4 M 1) (qs4 1) ws pr ev ⊢
      wpKA g Proto.triv (w4 M 1) qs4 s (Φ4 g M) := by
  obtain ⟨hprog, hq, hpc, h9⟩ := hs
  have hw := litW_x xs4 img4 M 1
  have hX := p4h_at hprog
  iintro ⟨#Hctx, Hr2, HQ, Hl⟩
  iapply (wpKA_fence hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  iapply (h1_rel g M sv hdd s1 _ _ ev ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 9 (.inr rfl), h9]⟩)
  iframe Hctx Hr2 HQ Hl

/-- `pc = 11`: `sd t2,(a1)`: its `pend` is in the bag (above the floor `lw`, not the surrendered `ex`). -/
theorem h1_cst (g : AGN) (M : List PMsg) (sv : SV) (hdd : g.dd = dd4 M)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lw ex : Nat)
    (hs : s.prog = b4h ∧ s.q = [] ∧ s.pc = 11 ∧ s.rd 9 = X ∧ s.rd 11 = Y)
    (hmd : (ex = 0 ∧ lw ≤ coh ws Ct) ∨ (lw < ex ∧ ∃ j : Nat, j < 8 ∧ ex ≤ coh ws (Ct + j))) :
    pCtx (GF := GF) g M sv ∗ r2Bag g M ∗ ([∗list] t ∈ cBagX M lw ex, pend g t) ∗ (⌜q4 ev⌝ ∨ dshot g) ∗
      lhA g Proto.triv (w4 M 1) (qs4 1) ws pr ev ⊢
      wpKA g Proto.triv (w4 M 1) qs4 s (Φ4 g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11⟩ := hs
  have hw := litW_x xs4 img4 M 1
  have hX := p4h_at hprog
  iintro ⟨#Hctx, Hr2, Hb, #HQ, Hl⟩
  iapply (wpKA_sw (sz := 8) (rs2 := 7) (rs1 := 11) (off := 0) (base := Ct) hw
    (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_of h11 (by decide) (by decide))
    (base_of h11 (by decide)))
  iframe Hl
  inext
  iintro %ts %_ %hmsg %hcoh %_ _ _
  rw [toBytes_length] at hcoh
  have hcj : ∀ j : Nat, j < 8 → coh ws (Ct + j) < ts := fun j hj => cohBelow_at hcoh hj
  have hts1 : 1 ≤ ts := by have := hcj 0 (by decide); omega
  have hC := isC_of_msg (by decide : 1 < 2) (toBytes_length _ _) hts1 hmsg
  have htsM := msgAt_le (msgAt_of hts1 hmsg)
  have hlts : lw < ts := by
    rcases hmd with ⟨_, hle⟩ | ⟨hlt, j, hj, hle⟩
    · have := hcj 0 (by decide); simp at this; omega
    · have := hcj j hj; omega
  have hexts : ts ≠ ex := by
    rcases hmd with ⟨rfl, _⟩ | ⟨_, j, hj, hle⟩
    · omega
    · have := hcj j hj; omega
  unfold cBagX
  icases bsl_filter_take (pend g) (fun t => decide (lw < t) && decide (t ≠ ex) && isC M t) (fun _ => false) ts
    (by simp [hlts, hC, hexts]) (fun _ h => by cases h) (rng M) (mem_rng.2 htsM) (nodup_rng M) $$ Hb
    with ⟨Hp, -⟩
  imod shoot $$ Hp with #Hsh
  imodintro
  isplitr
  · icases HQ with (%hQ | #Hd)
    · ileft; ipureintro
      exact ⟨⟨0, grd_intro (q4_snoc hQ (notCLd_st))⟩, grd_intro trivial⟩
    · iright; iexact Hd
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  iapply (h1_fence g M sv hdd s1 _ _ _ ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 9 (.inr rfl), h9]⟩)
  iframe Hctx Hr2 Hl
  icases HQ with (%hQ | #Hd)
  · ileft; ipureintro; exact q4_snoc hQ notCLd_st
  · iright; iexact Hd

/-- `pc = 10`: `addi t2,t2,1`. -/
theorem h1_addi (g : AGN) (M : List PMsg) (sv : SV) (hdd : g.dd = dd4 M)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (lw ex : Nat)
    (hs : s.prog = b4h ∧ s.q = [] ∧ s.pc = 10 ∧ s.rd 9 = X ∧ s.rd 11 = Y)
    (hmd : (ex = 0 ∧ lw ≤ coh ws Ct) ∨ (lw < ex ∧ ∃ j : Nat, j < 8 ∧ ex ≤ coh ws (Ct + j))) :
    pCtx (GF := GF) g M sv ∗ r2Bag g M ∗ ([∗list] t ∈ cBagX M lw ex, pend g t) ∗ (⌜q4 ev⌝ ∨ dshot g) ∗
      lhA g Proto.triv (w4 M 1) (qs4 1) ws pr ev ⊢
      wpKA g Proto.triv (w4 M 1) qs4 s (Φ4 g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11⟩ := hs
  have hw := litW_x xs4 img4 M 1
  have hX := p4h_at hprog
  iintro ⟨#Hctx, Hr2, Hb, HQ, Hl⟩
  iapply (wpKA_alui hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  iapply (h1_cst g M sv hdd s1 (instrR (regWP ws 7 (srcR 7))) _ ev lw ex
    ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 9 (.inl (by decide)), h9], by rw [LPstep_rd hs1 11 (.inl (by decide)), h11]⟩
    hmd)
  iframe Hctx Hr2 Hb HQ Hl

/-- **THE CRITICAL SECTION'S LOAD** (`pc = 9`, `ld t2,(a1)`): the owned read of the field (plan R-a1); the verdict's
obligation (the value is 5) is discharged here. -/
theorem h1_cld (g : AGN) (M : List PMsg) (sv : SV) (hdd : g.dd = dd4 M)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace) (c : Nat)
    (hs : s.prog = b4h ∧ s.q = [] ∧ s.pc = 9 ∧ s.rd 9 = X ∧ s.rd 11 = Y ∧ s.rd 12 = Z ∧ s.rd 14 = 1 ∧
      s.regs.length = 32)
    (hc5 : cAt5 M c) (hvr : c ≤ ws.wVrNew) (hq4 : q4 ev)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a := by assumption) :   -- [rebase-repair] MachFix-R-b5: `vi = 0`
    pCtx (GF := GF) g M sv ∗ r2Bag g M ∗ cPts g M c ∗ lhA g Proto.triv (w4 M 1) (qs4 1) ws pr ev ⊢
      wpKA g Proto.triv (w4 M 1) qs4 s (Φ4 g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11, h12, h14, hlen⟩ := hs
  have hw := litW_x xs4 img4 M 1
  have hX := p4h_at hprog
  iintro ⟨#Hctx, Hr2, Hc, Hl⟩
  unfold cPts
  icases Hc with ⟨%hlw, Hb⟩
  rw [cBag_X]
  iapply (wpKA_ld (sz := 8) (sgn := true) (rd := 7) (rs1 := 11) (off := 0) (base := Ct) hw
    (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_of h11 (by decide) (by decide))
    (base_of h11 (by decide)))
  iframe Hl
  inext
  iintro %tvs1 %hl1 %hlo1 _ _
  have hvp : c ≤ ldPre ws false false (srcsView ws (srcR 11)) :=
    Nat.le_trans hvr (PF.ldPre_ge ws false false (srcsView ws (srcR 11))).2.1
  have hwk := loadOk_weak hlo1
  have hcases := cld_cases (img := img4) hlw hvp 0 tvs1 (by rw [hl1]; decide) (by simpa using hwk)
  have hcohj := (loadBytes_coh false (ldPre ws false false (srcsView ws (srcR 11))) ws Ct tvs1).2
  -- THE MODE after the read: clean (value 5), R-a1 (doomed, one bag message out), or free
  ihave Hmode : |={⊤}=> (∃ ex, ([∗list] t ∈ cBagX M c ex, pend g t) ∗
      ((⌜ex = 0 ∧ tvs1.map Prod.snd = toBytes 5 8 ∧
          c ≤ coh (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1) Ct⌝) ∨
        (dshot g ∗ ⌜c < ex ∧ ∃ j : Nat, j < 8 ∧
          ex ≤ coh (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1) (Ct + j)⌝))) ∨
      (dfree g ∗ dshot g) $$ [Hb]
  · rcases hcases with hall | ⟨j, t, v, hj, hlt, hwt⟩ | ⟨ti, hti, j, hj, hc⟩
    · obtain ⟨t0, v0, r0, rfl⟩ := tvs_cons hl1 (by decide)
      have h0 := loadRun_coh0 ws false false (srcsView ws (srcR 11)) Ct t0 v0 r0
      have ht0 : t0 = c := hall (t0, v0) (List.mem_cons_self ..)
      have hval := vals_of_src (img := img4) hc5 rfl 0 ((t0, v0) :: r0)
        (by rw [hl1, toBytes_length]; decide) (by
          have := bytesAll_mono (fun _ _ _ hh => hh.1) _ _ hwk
          simpa using this) hall
      have hv5 : ((t0, v0) :: r0).map Prod.snd = toBytes 5 8 := by
        rw [hval, hl1]; rfl
      imodintro; ileft; iexists 0; iframe Hb; ileft; ipureintro
      exact ⟨rfl, hv5, by rw [← ht0]; exact h0⟩
    · have hj8 : j < 8 := by rw [← hl1]; exact (List.getElem?_eq_some_iff.1 hj).1
      have htM : 1 ≤ t ∧ t ≤ M.length := by obtain ⟨m, hm, _⟩ := hwt; exact msgAt_le hm
      have hcoh : t ≤ coh (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1) (Ct + j) :=
        (bytesAll_get hcohj hj).2
      have hwt' : wrB M (Ct + j) t := by simpa using hwt
      obtain ⟨m, hm, hb⟩ := hwt'
      rcases kind_C hj8 hb with hk | hk
      · have hC : isC M t = true := isC_knd.2 (by rw [knd_of hm]; exact hk)
        unfold cBagX
        icases bsl_filter_take (pend g) (fun t => decide (c < t) && decide (t ≠ 0) && isC M t)
          (fun x => decide (c < x) && decide (x ≠ t) && isC M x) t (by simp [hlt, hC]; omega)
          (fun x hx => by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
            exact ⟨⟨⟨hx.1.1, by omega⟩, hx.2⟩, hx.1.2⟩) (rng M) (mem_rng.2 htM) (nodup_rng M)
          $$ Hb with ⟨Hp, Hb⟩
        unfold pCtx
        icases Hctx with ⟨Hdoom, -⟩
        imod doom (E := ⊤) CoPset.subseteq_top g M t htM $$ [Hdoom Hp] with #Hd
        · iframe Hdoom Hp
        imodintro; ileft; iexists t; iframe Hb; iright; iframe Hd; ipureintro
        exact ⟨hlt, j, hj8, hcoh⟩
      · imod pCtx_read_dead g M sv hdd htM (by rw [knd_of hm]; exact hk) $$ Hctx with ⟨#Hf, #Hd⟩
        imodintro; iright; iframe Hf Hd
    · obtain ⟨hk, hle⟩ := cmo_knd (by omega) hc
      imod pCtx_read_dead g M sv hdd ⟨by omega, hle⟩ hk $$ Hctx with ⟨#Hf, #Hd⟩
      imodintro; iright; iframe Hf Hd
  imod Hmode with Hmode
  icases Hmode with (⟨%ex, Hb, (%hcl | ⟨#Hd, %hra⟩)⟩ | ⟨#Hf, #Hd⟩)
  · -- clean: the value is 5
    obtain ⟨rfl, hv5, hcc⟩ := hcl
    imodintro
    isplitr
    · ileft; ipureintro
      exact ⟨0, grd_intro (q4_snoc hq4 (fun tvs ⟨_, h⟩ => by cases h; exact hv5))⟩
    iintro %s1 %hs1 _ _
    imodintro
    iintro Hl
    obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
    iapply (h1_addi g M sv hdd s1 (qPosts (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1)
        (regWL 7 [.DLdRes] ++ [LInstr])) _ _ c 0
      ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 9 (.inl (by decide)), h9], by rw [LPstep_rd hs1 11 (.inl (by decide)), h11]⟩
      (.inl ⟨rfl, hcc⟩))
    iframe Hctx Hr2 Hb Hl
    ileft; ipureintro
    exact q4_snoc hq4 (fun tvs ⟨_, h⟩ => by cases h; exact hv5)
  · -- R-a1: doomed
    obtain ⟨hcex, j, hj, hexc⟩ := hra
    imodintro
    isplitr
    · iright; iexact Hd
    iintro %s1 %hs1 _ _
    imodintro
    iintro Hl
    obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
    iapply (h1_addi g M sv hdd s1 (qPosts (loadRun ws false false (srcsView ws (srcR 11)) Ct tvs1)
        (regWL 7 [.DLdRes] ++ [LInstr])) _ _ c ex
      ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 9 (.inl (by decide)), h9], by rw [LPstep_rd hs1 11 (.inl (by decide)), h11]⟩
      (.inr ⟨hcex, j, hj, hexc⟩))
    iframe Hctx Hr2 Hb Hl
    iright; iexact Hd
  · -- free mode
    imodintro
    isplitr
    · iright; iexact Hd
    iintro %s1 %hs1 _ _
    imodintro
    iintro Hl
    obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
    ihave Hfree := p4h_free (GF := GF) g M hdd
    have hfr : frS4 s1 := ⟨hP1, hq1, by rw [hc1]; decide, by rw [hc1]; decide,
      by rw [LPstep_rd hs1 9 (.inl (by decide)), h9], by rw [LPstep_rd hs1 11 (.inl (by decide)), h11],
      by rw [LPstep_rd hs1 12 (.inl (by decide)), h12], by rw [LPstep_rd hs1 14 (.inl (by decide)), h14],
      hs1.2.2.2.1.trans hlen, fun h => by omega⟩
    iapply Hfree $$ %s1 %_ %_ %_ %hfr Hf Hd Hl

end cs

end Weak.Prom.OA.P
