/-
Weak/Prom: **E-a2 — hart 0 (pipealloc, (4)'s text verbatim)** (stage E-a2; OwnAEPipeH0.lean's steps over the owners
of OwnAE2Defs.lean).

Hart 0 is the BOOT OWNER of the field, the cpu field and the L2 word (`kalloc`'s page): its junk stores, the birth `b`
and the field's initialisation `c` take their `pend`s from its own bags.  AT THE BIRTH (`initlock`, a plain store) it
allocates the lock's ghost name `γ` and RE-SPLITS the L2 word's bag above `b` into the lock's protocol `lkB5 b`
(`resplit5`).  At the publication `f` (release-class through `fence rw,w`) it deposits the field's points-to and the
cpu field's bag (naming `γ`) in `b`'s saved-proposition slot (the deferred deposit) and the PERSISTENT handle with
`lkB5 b` in `f`'s slot.  Every store proves `π4.okMsg` outright.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAE2Lock

namespace Weak.Prom.OA.E2

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y Z)
open Weak.Prom.OA.P (L1 J p4o b4o SV bSlot bth bthAt isLockAt cAt5 dep0 bslot_deposit msgAt_of kind_bt)
open Weak.Prom.OA.E
open Weak.Prom.OA.EP (isL2O cB zBagE lk_L2O zBag_take0 ok4_lk ok4_l1 ok4_ct π4)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-- The postcondition. -/
abbrev Φ5 {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] (g : AGN) (M : List PMsg) :
    Unit → IProp GF := fun _ => iprop(⌜∃ V, grd π4 img5 M V True⌝ ∨ dshot g)

theorem noLd_nil : noLd [] := fun _ h => by cases h

section h0

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]

/-- `pc = 7`: THE PUBLICATION `sw zero,0(a2)` (release-class) with the deferred deposit of the birth and the deposit
of the handle, then the end. -/
theorem h0_pub5 (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) (s3 : LP) (ws : PState)
    (pr : GSet Nat) (ev : Trace) (γ : GName) (b c : Nat) (hs : s3.prog = b4o ∧ s3.q = [] ∧ s3.pc = 7 ∧ s3.rd 12 = Z)
    (hb : bthAt M Lk b) (hmc : cAt5 M c) (hC : isC3 M c = true) (hbw : b ≤ ws.wVwNew) (hcw : c ≤ ws.wVwNew)
    (hq : noLd ev) :
    ctx5 (GF := GF) g M sv ak ∗ lkB5 g M sv ak b ∗ saved_prop_own (sv.σ b) (.own 1) iprop(True) ∗
      ([∗list] t ∈ cB M c, pend g t) ∗ pPts5 g M 0 ∗ token γ ∗ lhA g π4 (w5 M 0) (qs5 M 0) ws pr ev ⊢
      wpKA g π4 (w5 M 0) (qs5 M) s3 (Φ5 g M) := by
  obtain ⟨hP3, hq3, hc3, g12⟩ := hs
  have hw := litW_x xs5 img5 M 0
  iintro ⟨#Hctx, #Hlk, Hsv, Hc, Hpp, Hγ, Hl⟩
  -- `sw zero,0(a2)`: THE PUBLICATION
  iapply (wpKA_sw (sz := 4) (rs2 := 0) (rs1 := 12) (off := 0) (base := L1) hw
    (litAg_x hq3 (p5o_at hP3) (by rw [hc3]; rfl) rfl) hq3 (by rw [hP3, hc3]; rfl) (alg_of g12 (by decide) (by decide))
    (base_of g12 (by decide)))
  iframe Hl
  inext
  iintro %r %_ %hmsg' %_ %hext _ Hcr
  have hd0 : toBytes (s3.rd 0) 4 = toBytes 0 4 := rfl
  rw [hd0] at hmsg'
  -- RELEASE-CLASS (plan §3): the plain store's pre-view contains `vwNew` (raised by the fence)
  have hvr := (PF.stPreA_ge ws false false (srcsView ws (srcR 12)) (srcsView ws (srcR 0))).2.2.2.1
  have hr1 : 1 ≤ r := by omega
  have hmr := msgAt_of hr1 hmsg'
  have hrM := msgAt_le hmr
  have hbM : b ∈ (rng M).filter (bth M) := by
    obtain ⟨m, hm, hp, hd, hcl, ht⟩ := hb
    refine List.mem_filter.2 ⟨mem_rng.2 (msgAt_le hm), ?_⟩
    obtain ⟨pa, dd, tid, cl⟩ := m; simp only at hp hd hcl ht; subst hp hd hcl ht
    unfold bth; rw [hm]; simp [kind_bt]
  unfold ctx5
  icases Hctx with ⟨-, Hfs, -, Hbs⟩
  ihave #Hbsl := bsl_mem (F := fun t => bSlot M sv t) hbM $$ Hbs
  ihave #Hfsl := bsl_mem (F := fun t => fSlot5 g M sv ak t)
    (List.mem_filter.2 ⟨mem_rng.2 hrM, by rw [fPub, clsB_of hmr]; exact decide_eq_true ⟨rfl, rfl⟩⟩) $$ Hfs
  -- (a) THE DEFERRED DEPOSIT of the birth `b`: the resource names the runtime `γ`
  imod bslot_deposit M sv b iprop(Rb5 g M c ∗ token γ) $$ [Hsv Hc Hpp Hγ Hcr] with ⟨#Hds, #HsQ⟩
  · iframe Hbsl Hsv Hcr Hγ; unfold Rb5 cPts5; iframe Hc Hpp; ipureintro; exact ⟨hC, .inl hmc⟩
  -- (b) THE PUBLICATION: the persistent handle and the lock's protocol
  imod fdeposit5 g M sv ak r $$ [] with #Hsh
  · iframe Hfsl
    unfold Pub5
    iexists γ; iexists b; iexists c
    isplitr
    · ipureintro; exact ⟨by omega, by omega, hmc⟩
    iframe Hlk
    unfold isLockAt
    iframe Hds HsQ Hbsl
    ipureintro; exact hb
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨⟨0, grd_intro (q5_noLd (noLd_snoc hq noLd_st))⟩,
      grd_intro (ok4_l1 (toBytes_length _ _))⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s' %hs' _ _
  imodintro
  iintro Hl
  obtain ⟨hP', hc', hq'⟩ := LPstep_at hs' hP3 (by rw [hc3])
  have hend : s'.prog.length ≤ s'.pc := by rw [hP', hc']; decide
  iapply (wpKA_end (v := ()) (litAg_xn hq' (fun x hx => by rw [p5o_at hP', hc'] at hx; cases hx)) hq' hend
    (by show litDone s' = some (); unfold litDone; rw [if_pos ⟨hq', hend⟩]))
  iframe Hl
  imodintro
  ileft; ipureintro; exact ⟨0, grd_intro trivial⟩

/-- `pc = 4..7`: `li t2,5; sd t2,0(a1)` (the field's initialisation `c`), `fence rw,w`, and THE PUBLICATION
`sw zero,0(a2)` (release-class) with the deferred deposit of the birth and the deposit of the handle, then the end. -/
theorem h0_tail5 (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) (s : LP) (ws : PState)
    (pr : GSet Nat) (ev : Trace) (γ : GName) (b lw : Nat)
    (hs : s.prog = b4o ∧ s.q = [] ∧ s.pc = 4 ∧ s.rd 11 = Y ∧ s.rd 12 = Z ∧ s.regs.length = 32)
    (hb : bthAt M Lk b) (hbw : b ≤ ws.wVwOld) (hlw : lw ≤ coh ws Ct) (hq : noLd ev) :
    ctx5 (GF := GF) g M sv ak ∗ lkB5 g M sv ak b ∗ saved_prop_own (sv.σ b) (.own 1) iprop(True) ∗
      ([∗list] t ∈ cB M lw, pend g t) ∗ pPts5 g M 0 ∗ token γ ∗ lhA g π4 (w5 M 0) (qs5 M 0) ws pr ev ⊢
      wpKA g π4 (w5 M 0) (qs5 M) s (Φ5 g M) := by
  obtain ⟨hprog, hq0, hpc, h11, h12, hlen⟩ := hs
  have hw := litW_x xs5 img5 M 0
  iintro ⟨#Hctx, #Hlk, Hsv, Hc, Hpp, Hγ, Hl⟩
  -- `li t2,5`
  iapply (wpKA_alui hw (litAg_x hq0 (p5o_at hprog) (by rw [hpc]; rfl) rfl) hq0 (by rw [hprog, hpc]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e11 : s1.rd 11 = Y := by rw [LPstep_rd hs1 11 (.inl (by decide)), h11]
  have e12 : s1.rd 12 = Z := by rw [LPstep_rd hs1 12 (.inl (by decide)), h12]
  have e7 : s1.rd 7 = 5 := li_val hs1 (by decide) (by omega) (by decide)
  -- `sd t2,0(a1)`: the initialisation `c`
  iapply (wpKA_sw (sz := 8) (rs2 := 7) (rs1 := 11) (off := 0) (base := Ct) hw
    (litAg_x hq1 (p5o_at hP1) (by rw [hc1]; rfl) rfl) hq1 (by rw [hP1, hc1]; rfl)
    (alg_of e11 (by decide) (by decide)) (base_of e11 (by decide)))
  iframe Hl
  inext
  iintro %c %_ %hmsg %hcoh %_ _ _
  rw [e7] at hmsg hcoh
  rw [toBytes_length] at hcoh
  have hc0 : coh (instrR (regWP ws 7 (srcR 0))) Ct < c := by
    have := cohBelow_at (j := 0) hcoh (by decide); simpa using this
  have hc1' : 1 ≤ c := by omega
  have hmc := msgAt_of hc1' hmsg
  have hC := C3_of (by decide : 0 < 3) (toBytes_length _ _) hmc
  icases cB_take (GF := GF) g M (by exact Nat.lt_of_le_of_lt hlw hc0 : lw < c) (C3_CO hC) (msgAt_le hmc) $$ Hc
    with ⟨Hp, Hc⟩
  imod shoot $$ Hp with #Hsh
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨⟨0, grd_intro (q5_noLd (noLd_snoc hq noLd_st))⟩, grd_intro (ok4_ct (toBytes_length _ _))⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s2 %hs2 _ _
  imodintro
  iintro Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have f12 : s2.rd 12 = Z := by rw [LPstep_rd hs2 12 (.inr rfl), e12]
  have hvw := C.st_vwOld (instrR (regWP ws 7 (srcR 0))) (srcsView (instrR (regWP ws 7 (srcR 0))) (srcR 11))
    (max (srcsView (instrR (regWP ws 7 (srcR 0))) (srcR 11)) (srcsView (instrR (regWP ws 7 (srcR 0))) (srcR 7))) Ct
    (toBytes (s1.rd 7) 8).length c
  have hbw' : b ≤ ws.wVwOld := hbw
  -- `fence rw,w`
  iapply (wpKA_fence hw (litAg_x hq2 (p5o_at hP2) (by rw [hc2]; rfl) rfl) hq2 (by rw [hP2, hc2]; rfl))
  iframe Hl
  inext
  iintro %s3 %hs3 _ _
  imodintro
  iintro Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  have g12 : s3.rd 12 = Z := by rw [LPstep_rd hs3 12 (.inr rfl), f12]
  have hcw : c ≤ (instrR (fencePost (instrR (acqPost (storeRun (instrR (regWP ws 7 (srcR 0))) false
      (srcsView (instrR (regWP ws 7 (srcR 0))) (srcR 11)) (max (srcsView (instrR (regWP ws 7 (srcR 0))) (srcR 11))
        (srcsView (instrR (regWP ws 7 (srcR 0))) (srcR 7))) Ct (toBytes (s1.rd 7) 8).length c) false c)) true true
          false true)).wVwNew := by
    simp only [instrR_vwNew, fence_vwNew, ite_true]; rw [hvw]
    have : (instrR (regWP ws 7 (srcR 0))).wVwOld = ws.wVwOld := rfl
    omega
  have hbw2 : b ≤ (instrR (fencePost (instrR (acqPost (storeRun (instrR (regWP ws 7 (srcR 0))) false
      (srcsView (instrR (regWP ws 7 (srcR 0))) (srcR 11)) (max (srcsView (instrR (regWP ws 7 (srcR 0))) (srcR 11))
        (srcsView (instrR (regWP ws 7 (srcR 0))) (srcR 7))) Ct (toBytes (s1.rd 7) 8).length c) false c)) true true
          false true)).wVwNew := by
    simp only [instrR_vwNew, fence_vwNew, ite_true]; rw [hvw]
    have : (instrR (regWP ws 7 (srcR 0))).wVwOld = ws.wVwOld := rfl
    omega
  iapply (h0_pub5 g M sv ak s3 _ _ _ γ b c ⟨hP3, hq3, hc3, g12⟩ hb hmc hC hbw2 hcw (noLd_snoc hq noLd_st))
  iframe Hctx Hlk Hsv Hc Hpp Hγ Hl

/-- `pc = 3`: INITLOCK `sw zero,0(s1)`: L2 is BORN by a plain store `b`; `γ` is allocated, and THE L2 WORD'S BAG
ABOVE `b` IS RE-SPLIT into the lock's protocol (`resplit5`). -/
theorem h0_birth5 (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) (s : LP) (ws : PState)
    (pr : GSet Nat) (ev : Trace) (lo lw : Nat) (hs : s.prog = b4o ∧ s.q = [] ∧ s.pc = 3 ∧ s.rd 9 = X ∧
      s.rd 11 = Y ∧ s.rd 12 = Z ∧ s.regs.length = 32) (hlo : lo ≤ coh ws Lk) (hlw : lw ≤ coh ws Ct) (hq : noLd ev) :
    ctx5 (GF := GF) g M sv ak ∗ dep0 M sv ∗ ([∗list] t ∈ cB M lw, pend g t) ∗ pPts5 g M 0 ∗ zBagE g M sv lo 0 ∗
      lhA g π4 (w5 M 0) (qs5 M 0) ws pr ev ⊢ wpKA g π4 (w5 M 0) (qs5 M) s (Φ5 g M) := by
  obtain ⟨hprog, hq0, hpc, h9, h11, h12, hlen⟩ := hs
  have hw := litW_x xs5 img5 M 0
  iintro ⟨#Hctx, Hdep, Hc, Hpp, Hz, Hl⟩
  iapply (wpKA_sw (sz := 4) (rs2 := 0) (rs1 := 9) (off := 0) (base := Lk) hw
    (litAg_x hq0 (p5o_at hprog) (by rw [hpc]; rfl) rfl) hq0 (by rw [hprog, hpc]; rfl) (alg_of h9 (by decide) (by decide))
    (base_of h9 (by decide)))
  iframe Hl
  inext
  iintro %b %_ %hmsg %hcoh %_ _ _
  have hd0 : toBytes (s.rd 0) 4 = toBytes 0 4 := rfl
  rw [hd0] at hmsg hcoh
  have hc0 : coh ws Lk < b := by have := cohBelow_at (j := 0) hcoh (by decide); simpa using this
  have hmb := msgAt_of (by omega) hmsg
  have hbM := msgAt_le hmb
  have hbth : bthAt M Lk b := ⟨_, hmb, rfl, rfl, rfl, rfl⟩
  have hbL : b ∈ (rng M).filter (bth M) := by
    refine List.mem_filter.2 ⟨mem_rng.2 hbM, ?_⟩
    unfold bth; rw [hmb]; simp [kind_bt]
  icases zBag_take0 (GF := GF) g M sv (by omega : lo < b) (lk_L2O (toBytes_length 0 4) hmb) hbM $$ Hz with ⟨Hp, Hz⟩
  imod shoot $$ Hp with #Hsh
  -- THE RE-SPLIT: the L2 word's bag above `b` becomes the lock's protocol
  imod resplit5 g M sv ak b $$ Hz with #Hlk
  unfold dep0
  icases bsl_filter_take (fun t => saved_prop_own (GF := GF) (sv.σ t) (.own 1) iprop(True)) (bth M) (fun _ => false)
    b (List.mem_filter.1 hbL).2 (fun _ h => by cases h) (rng M) (mem_rng.2 hbM) (nodup_rng M) $$ Hdep
    with ⟨Hsv, -⟩
  -- INITLOCK ALLOCATES THE LOCK'S GHOST NAME (after adequacy start)
  imod token_alloc with ⟨%γ, Hγ⟩
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨⟨0, grd_intro (q5_noLd (noLd_snoc hq noLd_st))⟩, grd_intro (ok4_lk (toBytes_length _ _))⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hvw := C.st_vwOld ws (srcsView ws (srcR 9)) (max (srcsView ws (srcR 9)) (srcsView ws (srcR 0))) Lk
    (toBytes (s.rd 0) 4).length b
  have hcC := C.st_coh ws (srcsView ws (srcR 9)) (max (srcsView ws (srcR 9)) (srcsView ws (srcR 0))) Lk
    (toBytes (s.rd 0) 4).length b Ct
  iapply (h0_tail5 g M sv ak s1 _ _ _ γ b lw ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 11 (.inr rfl), h11],
    by rw [LPstep_rd hs1 12 (.inr rfl), h12], hs1.2.2.2.1.trans hlen⟩ hbth (by rw [hvw]; omega) (by omega)
    (noLd_snoc hq noLd_st))
  iframe Hctx Hlk Hsv Hc Hpp Hγ Hl

/-- `pc = 2`: `sd t1,0(a1)`: `kfree`'s junk in the field. -/
theorem h0_sdj5 (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) (s : LP) (ws : PState)
    (pr : GSet Nat) (ev : Trace) (lo lw : Nat) (hs : s.prog = b4o ∧ s.q = [] ∧ s.pc = 2 ∧ s.rd 9 = X ∧
      s.rd 11 = Y ∧ s.rd 12 = Z ∧ s.regs.length = 32) (hlo : lo ≤ coh ws Lk) (hlw : lw ≤ coh ws Ct) (hq : noLd ev) :
    ctx5 (GF := GF) g M sv ak ∗ dep0 M sv ∗ ([∗list] t ∈ cB M lw, pend g t) ∗ pPts5 g M 0 ∗ zBagE g M sv lo 0 ∗
      lhA g π4 (w5 M 0) (qs5 M 0) ws pr ev ⊢ wpKA g π4 (w5 M 0) (qs5 M) s (Φ5 g M) := by
  obtain ⟨hprog, hq0, hpc, h9, h11, h12, hlen⟩ := hs
  have hw := litW_x xs5 img5 M 0
  iintro ⟨#Hctx, Hdep, Hc, Hpp, Hz, Hl⟩
  iapply (wpKA_sw (sz := 8) (rs2 := 6) (rs1 := 11) (off := 0) (base := Ct) hw
    (litAg_x hq0 (p5o_at hprog) (by rw [hpc]; rfl) rfl) hq0 (by rw [hprog, hpc]; rfl)
    (alg_of h11 (by decide) (by decide)) (base_of h11 (by decide)))
  iframe Hl
  inext
  iintro %ts %_ %hmsg %hcoh %_ _ _
  rw [toBytes_length] at hcoh
  have hc0 : coh ws Ct < ts := by have := cohBelow_at (j := 0) hcoh (by decide); simpa using this
  have hmt := msgAt_of (by omega) hmsg
  icases cB_take (GF := GF) g M (by omega : lw < ts) (C3_CO (C3_of (by decide : 0 < 3) (toBytes_length _ _) hmt))
    (msgAt_le hmt) $$ Hc with ⟨Hp, Hc⟩
  imod shoot $$ Hp with #Hsh
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨⟨0, grd_intro (q5_noLd (noLd_snoc hq noLd_st))⟩, grd_intro (ok4_ct (toBytes_length _ _))⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hc0' := C.st_coh0 ws (srcsView ws (srcR 11)) (max (srcsView ws (srcR 11)) (srcsView ws (srcR 6))) Ct
    (toBytes (s.rd 6) 8).length ts (by rw [toBytes_length]; decide)
  have hcL := C.st_coh ws (srcsView ws (srcR 11)) (max (srcsView ws (srcR 11)) (srcsView ws (srcR 6))) Ct
    (toBytes (s.rd 6) 8).length ts Lk
  iapply (h0_birth5 g M sv ak s1 _ _ _ lo ts ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 9 (.inr rfl), h9],
    by rw [LPstep_rd hs1 11 (.inr rfl), h11], by rw [LPstep_rd hs1 12 (.inr rfl), h12], hs1.2.2.2.1.trans hlen⟩
    (by omega) hc0' (noLd_snoc hq noLd_st))
  iframe Hctx Hdep Hc Hpp Hz Hl

/-- **HART 0** (`pc = 0..1`: `li t1,J; sw t1,0(s1)` — `kfree`'s junk in the lock word), then the rest. -/
theorem h0_hart5 (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName)
    (s0 : LP) {P0 : GSet Nat} (hprog : s0.prog = b4o) (hpc : s0.pc = 0) (hq : s0.q = [])
    (hlen : s0.regs.length = 32) (h9 : s0.rd 9 = X) (h11 : s0.rd 11 = Y) (h12 : s0.rd 12 = Z) :
    ctx5 (GF := GF) g M sv ak ∗ dep0 M sv ∗ ([∗list] t ∈ cB M 0, pend g t) ∗ pPts5 g M 0 ∗ zBagE g M sv 0 0 ∗
      lhA g π4 (w5 M 0) (qs5 M 0) psInit P0 [] ⊢
      wpKA g π4 (w5 M 0) (qs5 M) s0 (Φ5 g M) := by
  have hw := litW_x xs5 img5 M 0
  iintro ⟨#Hctx, Hdep, Hc, Hpp, Hz, Hl⟩
  iapply (wpKA_alui hw (litAg_x hq (p5o_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have e9 : s1.rd 9 = X := by rw [LPstep_rd hs1 9 (.inl (by decide)), h9]
  have e6 : s1.rd 6 = J := li_val hs1 (by decide) (by omega) (by decide)
  iapply (wpKA_sw (sz := 4) (rs2 := 6) (rs1 := 9) (off := 0) (base := Lk) hw
    (litAg_x hq1 (p5o_at hP1) (by rw [hc1]; rfl) rfl) hq1 (by rw [hP1, hc1]; rfl) (alg_of e9 (by decide) (by decide))
    (base_of e9 (by decide)))
  iframe Hl
  inext
  iintro %j %_ %hmsg %hcoh %_ _ _
  rw [e6] at hmsg hcoh
  have hj1 : 1 ≤ j := by have := cohBelow_at (j := 0) hcoh (by decide); simp at this; omega
  have hmj := msgAt_of hj1 hmsg
  icases zBag_take0 (GF := GF) g M sv (by omega : 0 < j) (lk_L2O (toBytes_length J 4) hmj) (msgAt_le hmj) $$ Hz
    with ⟨Hp, Hz⟩
  imod shoot $$ Hp with #Hsh
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨⟨0, grd_intro (q5_noLd (noLd_snoc noLd_nil noLd_st))⟩,
      grd_intro (ok4_lk (toBytes_length _ _))⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s2 %hs2 _ _
  imodintro
  iintro Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have hc0' := C.st_coh0 (instrR (regWP psInit 6 (srcR 0))) (srcsView (instrR (regWP psInit 6 (srcR 0))) (srcR 9))
    (max (srcsView (instrR (regWP psInit 6 (srcR 0))) (srcR 9)) (srcsView (instrR (regWP psInit 6 (srcR 0))) (srcR 6)))
    Lk (toBytes (s1.rd 6) 4).length j (by rw [toBytes_length]; decide)
  iapply (h0_sdj5 g M sv ak s2 _ _ _ j 0 ⟨hP2, hq2, hc2, by rw [LPstep_rd hs2 9 (.inr rfl), e9],
    by rw [LPstep_rd hs2 11 (.inr rfl), LPstep_rd hs1 11 (.inl (by decide)), h11],
    by rw [LPstep_rd hs2 12 (.inr rfl), LPstep_rd hs1 12 (.inl (by decide)), h12],
    hs2.2.2.2.1.trans (hs1.2.2.2.1.trans hlen)⟩ hc0' (Nat.zero_le _) (noLd_snoc noLd_nil noLd_st))
  iframe Hctx Hdep Hc Hpp Hz Hl

end h0

end Weak.Prom.OA.E2
