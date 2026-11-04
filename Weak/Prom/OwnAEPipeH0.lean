/-
Weak/Prom: **E-a, G4 (4) with the dead set empty — hart 0 (pipealloc)** (stage E-a; the text and the steps of
OwnAPipeH0.lean over `π4` and the per-byte owners of OwnAEPipeDefs.lean).

Hart 0 is the BOOT OWNER of the field and the L2 word: its junk stores (`kfree`), the birth `b` (initlock, a plain
store; `γ` allocated at the step) and the field's initialisation `c` take their `pend`s from its own bags — the
L2 word's bag holds EVERY later L2 message, any author (hart 1's included).  At the L1 release (release-class) it
deposits the field's points-to (naming `γ`) in `b`'s saved-proposition slot and the L2 word's bag above `b` with the
handle in L1's slot (`Pub1E`): the ownership of the L2 word moves to the next acquirer through the publication.
Every store proves `π4.okMsg` outright.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAEPipeDefs

namespace Weak.Prom.OA.EP

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y Z)
open Weak.Prom.OA.P (L1 J p4o p4h b4o b4h t4 xs4 p4o_at p4h_at img4 w4 kind knd isK bth knd_of kind_jk kind_bt
  kind_r1 bagK SV bSlot bthAt isLockAt cAt5 q4 qs4 q4_nil q4_snoc notCLd_st ownGF4 bslot_deposit msgAt_of dep0
  z0P a1P r1P a2P r2P)
open Weak.Prom.OA.E
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-- The postcondition. -/
abbrev Φ4E {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] (g : AGN) (M : List PMsg) :
    Unit → IProp GF := fun _ => iprop(⌜∃ V, grd π4 img4 M V True⌝ ∨ dshot g)

section h0

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]

/-- Hart 0's L2 word bag: take `ts`'s `pend` (its token is not needed), the bag above `ts` remains. -/
theorem zBag_take0 (g : AGN) (M : List PMsg) (sv : SV) {lo ts : Nat} (hlt : lo < ts) (hk : isL2O M ts = true)
    (htM : 1 ≤ ts ∧ ts ≤ M.length) : zBagE (GF := GF) g M sv lo 0 ⊢ pend g ts ∗ zBagE g M sv ts 0 := by
  iintro Hz
  icases zBag_takeE g M sv hlt hk htM $$ Hz with ⟨⟨Hp, -⟩, Hz⟩
  iframe Hp
  iapply zBag_up g M sv (Nat.le_of_lt hlt) (Nat.le_refl _) $$ Hz

/-- `pc = 7`: **THE L1 RELEASE** `sw zero,0(a2)` (release-class) with the DEFERRED DEPOSIT of the birth `b` and
L1's deposit, then the end. -/
theorem h0_relE (g : AGN) (M : List PMsg) (sv : SV) (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace)
    (γ : GName) (b c : Nat) (hs : s.prog = b4o ∧ s.q = [] ∧ s.pc = 7 ∧ s.rd 12 = Z)
    (hb : bthAt M Lk b) (hc5 : cAt5 M c) (hbw : b ≤ ws.wVwNew) (hcw : c ≤ ws.wVwNew) (hq4 : q4 ev) :
    pCtxE (GF := GF) g M sv ∗ saved_prop_own (sv.σ b) (.own 1) iprop(True) ∗ cPtsP g M c ∗ token γ ∗ zBagE g M sv b 0 ∗
      lhA g π4 (w4 M 0) (qs4 0) ws pr ev ⊢
      wpKA g π4 (w4 M 0) qs4 s (Φ4E g M) := by
  obtain ⟨hprog, hq, hpc, h12⟩ := hs
  have hw := litW_x xs4 img4 M 0
  have hX := p4o_at hprog
  iintro ⟨#Hctx, Hsv, Hc, Hγ, Hz, Hl⟩
  iapply (wpKA_sw (sz := 4) (rs2 := 0) (rs1 := 12) (off := 0) (base := L1) hw
    (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_of h12 (by decide) (by decide))
    (base_of h12 (by decide)))
  iframe Hl
  inext
  iintro %r %_ %hmsg %hcoh %hext _ Hcr
  have hd0 : toBytes (s.rd 0) 4 = toBytes 0 4 := rfl
  rw [hd0] at hmsg hcoh
  -- RELEASE-CLASS (plan §3): the plain store's pre-view contains `vwNew` (raised by the fence)
  have hvr : ws.wVwNew < r := by
    have := (PF.stPreA_ge ws false false (srcsView ws (srcR 12)) (srcsView ws (srcR 0))).2.2.2.1
    omega
  have hr1 : 1 ≤ r := by omega
  have hmr := msgAt_of hr1 hmsg
  have hk3 : knd M r = 3 := by rw [knd_of hmr]; exact kind_r1
  have hrM := msgAt_le hmr
  have hbM : b ∈ (rng M).filter (bth M) := by
    obtain ⟨m, hm, hp, hd, hc, ht⟩ := hb
    refine List.mem_filter.2 ⟨mem_rng.2 (msgAt_le hm), ?_⟩
    unfold bth; rw [hm]
    have hz : z0P m := ⟨hp, by rw [hd]; rfl, hc, ht⟩
    have hk : kind m = 6 := by
      unfold kind
      have e1 : ¬ cmP m := fun h => by have := h.1.symm.trans hp; simp [Lk, Ct, X, Y] at this
      have e2 : ¬ a1P m := fun h => by have := h.1.symm.trans hp; simp [Lk, L1, X, Z] at this
      have e3 : ¬ r1P m := fun h => by have := h.1.symm.trans hp; simp [Lk, L1, X, Z] at this
      have e4 : ¬ a2P m := fun h => by have := h.2.2.2.symm.trans ht; simp at this
      have e5 : ¬ r2P m := fun h => by have := h.2.2.2.symm.trans ht; simp at this
      rw [if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg e5, if_pos hz]
    simp [hk, hd]
  unfold pCtxE
  icases Hctx with ⟨-, Hl1, Hbs, -⟩
  ihave #Hbsl := bsl_mem (F := fun t => bSlot M sv t) hbM $$ Hbs
  ihave #Hl1s := bsl_mem (F := fun t => l1SlotE g M sv t)
    (List.mem_filter.2 ⟨mem_rng.2 hrM, by simp [isK, hk3]⟩) $$ Hl1
  -- (a) THE DEFERRED DEPOSIT of the birth `b`: the resource names the runtime `γ`
  imod bslot_deposit M sv b iprop(cPtsP g M c ∗ token γ) $$ [Hsv Hc Hγ Hcr] with ⟨#Hds, #HsQ⟩
  · iframe Hbsl Hsv Hcr; iframe Hc Hγ
  -- (b) L1's deposit: the handle
  imod l1_depositE g M sv r $$ [Hz] with #Hsh
  · iframe Hl1s
    unfold Pub1E
    iexists γ; iexists b; iexists c
    isplitr
    · ipureintro; exact ⟨by omega, by omega, hc5⟩
    iframe Hz
    unfold isLockAt
    iframe Hds HsQ Hbsl
    ipureintro; exact hb
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨⟨0, grd_intro (q4_snoc hq4 notCLd_st)⟩, grd_intro (ok4_l1 (toBytes_length _ _))⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s' %hs' _ _
  imodintro
  iintro Hl
  obtain ⟨hP', hc', hq'⟩ := LPstep_at hs' hprog (by rw [hpc])
  have hend : s'.prog.length ≤ s'.pc := by rw [hP', hc']; decide
  iapply (wpKA_end (v := ()) (litAg_xn hq' (fun x hx => by rw [p4o_at hP', hc'] at hx; cases hx)) hq' hend
    (by show litDone s' = some (); unfold litDone; rw [if_pos ⟨hq', hend⟩]))
  iframe Hl
  imodintro
  ileft; ipureintro; exact ⟨0, grd_intro trivial⟩

/-- `pc = 6`: `fence rw,w`: raises `vwNew` to `vrOld ⊔ vwOld`. -/
theorem h0_fenceE (g : AGN) (M : List PMsg) (sv : SV) (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace)
    (γ : GName) (b c : Nat) (hs : s.prog = b4o ∧ s.q = [] ∧ s.pc = 6 ∧ s.rd 12 = Z)
    (hb : bthAt M Lk b) (hc5 : cAt5 M c) (hbw : b ≤ ws.wVwOld) (hcw : c ≤ ws.wVwOld) (hq4 : q4 ev) :
    pCtxE (GF := GF) g M sv ∗ saved_prop_own (sv.σ b) (.own 1) iprop(True) ∗ cPtsP g M c ∗ token γ ∗ zBagE g M sv b 0 ∗
      lhA g π4 (w4 M 0) (qs4 0) ws pr ev ⊢
      wpKA g π4 (w4 M 0) qs4 s (Φ4E g M) := by
  obtain ⟨hprog, hq, hpc, h12⟩ := hs
  have hw := litW_x xs4 img4 M 0
  have hX := p4o_at hprog
  iintro ⟨#Hctx, Hsv, Hc, Hγ, Hz, Hl⟩
  iapply (wpKA_fence hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hbw' : b ≤ (instrR (fencePost ws true true false true)).wVwNew := by
    simp only [instrR_vwNew, fence_vwNew, ite_true]; omega
  have hcw' : c ≤ (instrR (fencePost ws true true false true)).wVwNew := by
    simp only [instrR_vwNew, fence_vwNew, ite_true]; omega
  iapply (h0_relE g M sv s1 _ _ ev γ b c ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 12 (.inr rfl), h12]⟩ hb hc5 hbw' hcw'
    hq4)
  iframe Hctx Hsv Hc Hγ Hz Hl

/-- `pc = 5`: `sd t2,0(a1)` (`t2 = 5`): the field's initialisation `c` moves the points-to. -/
theorem h0_sdcE (g : AGN) (M : List PMsg) (sv : SV) (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace)
    (γ : GName) (b lw : Nat) (hs : s.prog = b4o ∧ s.q = [] ∧ s.pc = 5 ∧ s.rd 11 = Y ∧ s.rd 12 = Z ∧ s.rd 7 = 5)
    (hb : bthAt M Lk b) (hbw : b ≤ ws.wVwOld) (hlw : lw ≤ coh ws Ct) (hq4 : q4 ev) :
    pCtxE (GF := GF) g M sv ∗ saved_prop_own (sv.σ b) (.own 1) iprop(True) ∗ cPtsP g M lw ∗ token γ ∗
      zBagE g M sv b 0 ∗ lhA g π4 (w4 M 0) (qs4 0) ws pr ev ⊢
      wpKA g π4 (w4 M 0) qs4 s (Φ4E g M) := by
  obtain ⟨hprog, hq, hpc, h11, h12, h7⟩ := hs
  have hw := litW_x xs4 img4 M 0
  have hX := p4o_at hprog
  iintro ⟨#Hctx, Hsv, Hc, Hγ, Hz, Hl⟩
  iapply (wpKA_sw (sz := 8) (rs2 := 7) (rs1 := 11) (off := 0) (base := Ct) hw
    (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_of h11 (by decide) (by decide))
    (base_of h11 (by decide)))
  iframe Hl
  inext
  iintro %ts %_ %hmsg %hcoh %_ _ _
  rw [h7] at hmsg hcoh
  rw [toBytes_length] at hcoh
  have hc0 : coh ws Ct < ts := by have := cohBelow_at (j := 0) hcoh (by decide); simpa using this
  have hts1 : 1 ≤ ts := by omega
  have hC := isC_of_msg (by decide : 0 < 2) (toBytes_length _ _) hts1 hmsg
  have hmt := msgAt_of hts1 hmsg
  have htsM := msgAt_le hmt
  icases cPtsP_take (GF := GF) g M (by omega : lw < ts) hC htsM $$ Hc with ⟨Hp, Hc⟩
  imod shoot $$ Hp with #Hsh
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨⟨0, grd_intro (q4_snoc hq4 notCLd_st)⟩, grd_intro (ok4_ct (toBytes_length _ _))⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hvw := C.st_vwOld ws (srcsView ws (srcR 11)) (max (srcsView ws (srcR 11)) (srcsView ws (srcR 7))) Ct
    (toBytes (s.rd 7) 8).length ts
  iapply (h0_fenceE g M sv s1 _ _ _ γ b ts ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 12 (.inr rfl), h12]⟩ hb hmt
    (by rw [hvw]; omega) (by rw [hvw]; omega) (q4_snoc hq4 notCLd_st))
  iframe Hctx Hsv Hc Hγ Hz Hl

/-- `pc = 4`: `li t2,5`. -/
theorem h0_li5E (g : AGN) (M : List PMsg) (sv : SV) (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace)
    (γ : GName) (b lw : Nat) (hs : s.prog = b4o ∧ s.q = [] ∧ s.pc = 4 ∧ s.rd 11 = Y ∧ s.rd 12 = Z ∧
      s.regs.length = 32)
    (hb : bthAt M Lk b) (hbw : b ≤ ws.wVwOld) (hlw : lw ≤ coh ws Ct) (hq4 : q4 ev) :
    pCtxE (GF := GF) g M sv ∗ saved_prop_own (sv.σ b) (.own 1) iprop(True) ∗ cPtsP g M lw ∗ token γ ∗
      zBagE g M sv b 0 ∗ lhA g π4 (w4 M 0) (qs4 0) ws pr ev ⊢
      wpKA g π4 (w4 M 0) qs4 s (Φ4E g M) := by
  obtain ⟨hprog, hq, hpc, h11, h12, hlen⟩ := hs
  have hw := litW_x xs4 img4 M 0
  have hX := p4o_at hprog
  iintro ⟨#Hctx, Hsv, Hc, Hγ, Hz, Hl⟩
  iapply (wpKA_alui hw (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  iapply (h0_sdcE g M sv s1 (instrR (regWP ws 7 (srcR 0))) _ ev γ b lw ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 11 (.inl (by decide)), h11],
    by rw [LPstep_rd hs1 12 (.inl (by decide)), h12], li_val hs1 (by decide) (by omega) (by decide)⟩ hb hbw hlw hq4)
  iframe Hctx Hsv Hc Hγ Hz Hl

/-- `pc = 3`: **INITLOCK** `sw zero,0(s1)`: L2 is BORN by a plain store `b`; the lock's ghost name `γ` is
allocated HERE, at runtime. -/
theorem h0_birthE (g : AGN) (M : List PMsg) (sv : SV) (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace)
    (lo lw : Nat) (hs : s.prog = b4o ∧ s.q = [] ∧ s.pc = 3 ∧ s.rd 9 = X ∧ s.rd 11 = Y ∧ s.rd 12 = Z ∧
      s.regs.length = 32)
    (hlo : lo ≤ coh ws Lk) (hlw : lw ≤ coh ws Ct) (hq4 : q4 ev) :
    pCtxE (GF := GF) g M sv ∗ dep0 M sv ∗ cPtsP g M lw ∗ zBagE g M sv lo 0 ∗
      lhA g π4 (w4 M 0) (qs4 0) ws pr ev ⊢
      wpKA g π4 (w4 M 0) qs4 s (Φ4E g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11, h12, hlen⟩ := hs
  have hw := litW_x xs4 img4 M 0
  have hX := p4o_at hprog
  iintro ⟨#Hctx, Hdep, Hc, Hz, Hl⟩
  iapply (wpKA_sw (sz := 4) (rs2 := 0) (rs1 := 9) (off := 0) (base := Lk) hw
    (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_of h9 (by decide) (by decide))
    (base_of h9 (by decide)))
  iframe Hl
  inext
  iintro %b %_ %hmsg %hcoh %_ _ _
  have hd0 : toBytes (s.rd 0) 4 = toBytes 0 4 := rfl
  rw [hd0] at hmsg hcoh
  have hc0 : coh ws Lk < b := by have := cohBelow_at (j := 0) hcoh (by decide); simpa using this
  have hb1 : 1 ≤ b := by omega
  have hmb := msgAt_of hb1 hmsg
  have hk6 : knd M b = 6 := by rw [knd_of hmb]; exact kind_bt
  have hbM := msgAt_le hmb
  have hbth : bthAt M Lk b := ⟨_, hmb, rfl, rfl, rfl, rfl⟩
  have hbL : b ∈ (rng M).filter (bth M) := by
    refine List.mem_filter.2 ⟨mem_rng.2 hbM, ?_⟩
    unfold bth; rw [hmb]; simp [kind_bt]
  icases zBag_take0 (GF := GF) g M sv (by omega : lo < b) (lk_L2O (toBytes_length 0 4) hmb) hbM $$ Hz with ⟨Hp, Hz⟩
  imod shoot $$ Hp with #Hsh
  -- the deposit right of `b`
  unfold dep0
  icases bsl_filter_take (fun t => saved_prop_own (GF := GF) (sv.σ t) (.own 1) iprop(True)) (bth M) (fun _ => false)
    b (List.mem_filter.1 hbL).2 (fun _ h => by cases h) (rng M) (mem_rng.2 hbM) (nodup_rng M) $$ Hdep
    with ⟨Hsv, -⟩
  -- INITLOCK ALLOCATES THE LOCK'S GHOST NAME (after adequacy start)
  imod token_alloc with ⟨%γ, Hγ⟩
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨⟨0, grd_intro (q4_snoc hq4 notCLd_st)⟩, grd_intro (ok4_lk (toBytes_length _ _))⟩
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
  iapply (h0_li5E g M sv s1 _ _ _ γ b lw ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 11 (.inr rfl), h11],
    by rw [LPstep_rd hs1 12 (.inr rfl), h12], hs1.2.2.2.1.trans hlen⟩ hbth (by rw [hvw]; omega) (by omega)
    (q4_snoc hq4 notCLd_st))
  iframe Hctx Hsv Hc Hγ Hz Hl

/-- `pc = 2`: `sd t1,0(a1)`: `kfree`'s junk in the field. -/
theorem h0_sdjE (g : AGN) (M : List PMsg) (sv : SV) (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace)
    (lo lw : Nat) (hs : s.prog = b4o ∧ s.q = [] ∧ s.pc = 2 ∧ s.rd 9 = X ∧ s.rd 11 = Y ∧ s.rd 12 = Z ∧
      s.regs.length = 32)
    (hlo : lo ≤ coh ws Lk) (hlw : lw ≤ coh ws Ct) (hq4 : q4 ev) :
    pCtxE (GF := GF) g M sv ∗ dep0 M sv ∗ cPtsP g M lw ∗ zBagE g M sv lo 0 ∗
      lhA g π4 (w4 M 0) (qs4 0) ws pr ev ⊢
      wpKA g π4 (w4 M 0) qs4 s (Φ4E g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11, h12, hlen⟩ := hs
  have hw := litW_x xs4 img4 M 0
  have hX := p4o_at hprog
  iintro ⟨#Hctx, Hdep, Hc, Hz, Hl⟩
  iapply (wpKA_sw (sz := 8) (rs2 := 6) (rs1 := 11) (off := 0) (base := Ct) hw
    (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_of h11 (by decide) (by decide))
    (base_of h11 (by decide)))
  iframe Hl
  inext
  iintro %ts %_ %hmsg %hcoh %_ _ _
  rw [toBytes_length] at hcoh
  have hc0 : coh ws Ct < ts := by have := cohBelow_at (j := 0) hcoh (by decide); simpa using this
  have hts1 : 1 ≤ ts := by omega
  have hC := isC_of_msg (by decide : 0 < 2) (toBytes_length _ _) hts1 hmsg
  have htsM := msgAt_le (msgAt_of hts1 hmsg)
  icases cPtsP_take (GF := GF) g M (by omega : lw < ts) hC htsM $$ Hc with ⟨Hp, Hc⟩
  imod shoot $$ Hp with #Hsh
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨⟨0, grd_intro (q4_snoc hq4 notCLd_st)⟩, grd_intro (ok4_ct (toBytes_length _ _))⟩
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
  iapply (h0_birthE g M sv s1 _ _ _ lo ts ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 9 (.inr rfl), h9],
    by rw [LPstep_rd hs1 11 (.inr rfl), h11], by rw [LPstep_rd hs1 12 (.inr rfl), h12], hs1.2.2.2.1.trans hlen⟩
    (by omega) hc0' (q4_snoc hq4 notCLd_st))
  iframe Hctx Hdep Hc Hz Hl

/-- `pc = 1`: `sw t1,0(s1)`: `kfree`'s junk in the lock word (a plain message of hart 0 below the birth). -/
theorem h0_swjE (g : AGN) (M : List PMsg) (sv : SV) (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace)
    (lo lw : Nat) (hs : s.prog = b4o ∧ s.q = [] ∧ s.pc = 1 ∧ s.rd 9 = X ∧ s.rd 11 = Y ∧ s.rd 12 = Z ∧
      s.rd 6 = J ∧ s.regs.length = 32)
    (hlo : lo ≤ coh ws Lk) (hlw : lw ≤ coh ws Ct) (hq4 : q4 ev) :
    pCtxE (GF := GF) g M sv ∗ dep0 M sv ∗ cPtsP g M lw ∗ zBagE g M sv lo 0 ∗
      lhA g π4 (w4 M 0) (qs4 0) ws pr ev ⊢
      wpKA g π4 (w4 M 0) qs4 s (Φ4E g M) := by
  obtain ⟨hprog, hq, hpc, h9, h11, h12, h6, hlen⟩ := hs
  have hw := litW_x xs4 img4 M 0
  have hX := p4o_at hprog
  iintro ⟨#Hctx, Hdep, Hc, Hz, Hl⟩
  iapply (wpKA_sw (sz := 4) (rs2 := 6) (rs1 := 9) (off := 0) (base := Lk) hw
    (litAg_x hq hX (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (alg_of h9 (by decide) (by decide))
    (base_of h9 (by decide)))
  iframe Hl
  inext
  iintro %j %_ %hmsg %hcoh %_ _ _
  rw [h6] at hmsg hcoh
  have hc0 : coh ws Lk < j := by have := cohBelow_at (j := 0) hcoh (by decide); simpa using this
  have hj1 : 1 ≤ j := by omega
  have hmj := msgAt_of hj1 hmsg
  have hk6 : knd M j = 6 := by rw [knd_of hmj]; exact kind_jk
  have hjM := msgAt_le hmj
  icases zBag_take0 (GF := GF) g M sv (by omega : lo < j) (lk_L2O (toBytes_length J 4) hmj) hjM $$ Hz with ⟨Hp, Hz⟩
  imod shoot $$ Hp with #Hsh
  imodintro
  isplitr
  · ileft; ipureintro
    exact ⟨⟨0, grd_intro (q4_snoc hq4 notCLd_st)⟩, grd_intro (ok4_lk (toBytes_length _ _))⟩
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hc0' := C.st_coh0 ws (srcsView ws (srcR 9)) (max (srcsView ws (srcR 9)) (srcsView ws (srcR 6))) Lk
    (toBytes (s.rd 6) 4).length j (by rw [toBytes_length]; decide)
  have hcC := C.st_coh ws (srcsView ws (srcR 9)) (max (srcsView ws (srcR 9)) (srcsView ws (srcR 6))) Lk
    (toBytes (s.rd 6) 4).length j Ct
  iapply (h0_sdjE g M sv s1 _ _ _ j lw ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 9 (.inr rfl), h9],
    by rw [LPstep_rd hs1 11 (.inr rfl), h11], by rw [LPstep_rd hs1 12 (.inr rfl), h12], hs1.2.2.2.1.trans hlen⟩
    hc0' (by omega) (q4_snoc hq4 notCLd_st))
  iframe Hctx Hdep Hc Hz Hl

/-- **HART 0** (pipealloc). -/
theorem h0_hartE (g : AGN) (M : List PMsg) (sv : SV)
    (s0 : LP) {P0 : GSet Nat} (hprog : s0.prog = b4o) (hpc : s0.pc = 0) (hq : s0.q = [])
    (hlen : s0.regs.length = 32) (h9 : s0.rd 9 = X) (h11 : s0.rd 11 = Y) (h12 : s0.rd 12 = Z) :
    pCtxE (GF := GF) g M sv ∗ dep0 M sv ∗ cPtsP g M 0 ∗ zBagE g M sv 0 0 ∗
      lhA g π4 (w4 M 0) (qs4 0) psInit P0 [] ⊢
      wpKA g π4 (w4 M 0) qs4 s0 (Φ4E g M) := by
  have hw := litW_x xs4 img4 M 0
  iintro ⟨#Hctx, Hdep, Hc, Hz, Hl⟩
  iapply (wpKA_alui hw (litAg_x hq (p4o_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl)
    (by decide))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  iapply (h0_swjE g M sv s1 _ _ _ 0 0 ⟨hP1, hq1, hc1, by rw [LPstep_rd hs1 9 (.inl (by decide)), h9],
    by rw [LPstep_rd hs1 11 (.inl (by decide)), h11], by rw [LPstep_rd hs1 12 (.inl (by decide)), h12],
    li_val hs1 (by decide) (by omega) (by decide), hs1.2.2.2.1.trans hlen⟩ (Nat.zero_le _) (Nat.zero_le _) q4_nil)
  iframe Hctx Hdep Hc Hz Hl

end h0

end Weak.Prom.OA.EP
