/-
Weak/Prom: **E-a4 — hart 0's round: kfree (the DEATH of the previous lifetime), initlock (a BIRTH and the
windowed re-split), publication** (stage E-a4; `pc = 0..7` of `p0`).

* `sw t1,0(s1)` — `kfree`'s junk in the lock word: either the DEATH of the previous lifetime (its slot `dSl`,
  fulfilled with the death mark built at the previous closing release) or junk beyond it (the page owner's
  remainder `jB`).  In round 1 the "previous lifetime" is the empty one born at timestamp 0.
* `sd t1,0(a1)` — junk in the field (the points-to's bag).
* `sw zero,0(s1)` — INITLOCK `b'`: a plain zero word, taken from hart 0's OWN PART (a release-shaped word beyond the
  old window — the junk just written lies between); every hart's part (hart 0's own, and the acquirers' parts
  RETURNED through their done bytes) and the junk beyond the old window feed the RE-SPLIT `resplit7` at `b'`.
* `li t2,5; sd t2,0(a1)` — the field's initialisation `c`; `fence rw,w; sb a3,0(a2)` — THE PUBLICATION of round `k`
  (release-class): the deferred deposit of `b'`'s resource in its shape-only birth slot, and the persistent
  handle + protocol `lkB b' k` in the publication's slot.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAE4H1

namespace Weak.Prom.OA.E4

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y Z)
open Weak.Prom.OA.P (L1 J SV bSlot dshotD dpendD msgAt_of cAt5 bslot_deposit)
open Weak.Prom.OA.C (Pc st_nonC Lk_ne_Ct)
open Weak.Prom.OA.E
open Weak.Prom.OA.EP (tL1 tL2 isL2O isCO cB lk_L2O)
open Weak.Prom.OA.E2
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-- Hart 0's registers in round `k`. -/
def RK0 (k : Nat) (s : LP) : Prop :=
  s.regs.length = 32 ∧ s.rd 9 = X ∧ s.rd 11 = Y ∧ s.rd 12 = Z ∧ s.rd 13 = k ∧ s.rd 28 = 3

theorem RK0_step {k : Nat} {s s' : LP} {pc rd v : Nat} (hr : RK0 k s) (hs : LPstep s s' pc rd v)
    (hrd : rd = 0 ∨ rd = 5 ∨ rd = 6 ∨ rd = 7 ∨ rd = 14 ∨ rd = 15) : RK0 k s' := by
  obtain ⟨h0, h9, h11, h12, h13, h28⟩ := hr
  have e : ∀ r, (r = 9 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 28) → s'.rd r = s.rd r :=
    fun r hr' => LPstep_rd hs r (by omega)
  exact ⟨hs.2.2.2.1.trans h0, by rw [e 9 (by omega), h9], by rw [e 11 (by omega), h11], by rw [e 12 (by omega), h12],
    by rw [e 13 (by omega), h13], by rw [e 28 (by omega), h28]⟩

theorem p0_at {s : LP} (h : s.prog = b0) : xOf xs7 s.prog = some p0 := by rw [h]; exact xOf_p0

/-- The page owner's kfree junk word is lock-word junk. -/
theorem J2_of {M : List PMsg} {t : Nat} {c : PClass} (hm : msgAt M t = some ⟨Lk, toBytes J 4, some 0, c⟩) :
    isJ2 M t = true := by
  have hO := lk_L2O (toBytes_length J 4) hm
  have hA : isA2 M t = false := by
    rw [isA2, clsB_of hm]; simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; right
    rintro ⟨_, h⟩; exact absurd h (by decide)
  have hR : isR2 M t = false := by
    rw [isR2, clsB_of hm]; simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; right
    rintro ⟨_, h⟩; exact absurd h (by decide)
  simp [isJ2, hO, hA, hR]

section h0

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]

/-- **THE BIRTH from the page owner's own part**: a release-shaped word beyond the old window. -/
theorem prt_birth (g : AGN) (M : List PMsg) (tk : Nat → GName) {bp lo b' : Nat} (hlo : lo < b')
    (hR : isR2 M b' = true) (hby : byH M 0 b' = true) (hbM : 1 ≤ b' ∧ b' ≤ M.length)
    (hbey : ∀ t, b' ≤ t → bey M bp t = true) :
    prt (GF := GF) g M tk 0 bp lo ⊢ pend g b' ∗ fpt g M tk 0 b' := by
  unfold prt fpt rB rA
  iintro ⟨Ho, Hr⟩
  icases bsl_filter_take (pend g) (fun t => decide (lo < t) && isR2 M t && byH M 0 t && bey M bp t)
    (fun t => decide (b' < t) && isR2 M t && byH M 0 t) b' (by simp [hR, hby, hbey b' (Nat.le_refl _)]; omega)
    (fun t ht => by simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
                    exact ⟨⟨⟨⟨by omega, ht.1.2⟩, ht.2⟩, hbey t (by omega)⟩, by omega⟩)
    (rng M) (mem_rng.2 hbM) (nodup_rng M) $$ Hr with ⟨Hp, Hr⟩
  iframe Hp Hr
  iapply obg_up g M tk (Nat.le_of_lt hlo) (Nat.zero_le _) $$ Ho

/-- Hart 0's deposit rights above `lo`: the full saved proposition of every plain zero word at the lock address. -/
def dep7 (M : List PMsg) (sv : SV) (lo : Nat) : IProp GF :=
  iprop([∗list] t ∈ (rng M).filter (fun t => decide (lo < t) && zw M t), saved_prop_own (sv.σ t) (.own 1) iprop(True))

set_option maxHeartbeats 4000000 in
/-- **HART 0, `pc = 0..7`** (see the header). -/
theorem h0A (g : AGN) (M : List PMsg) (sv : SV) (ak ek : Nat → Nat → GName) (hdd : g.dd = fun _ => False)
    (k bp lo0 b1 lo1 b2 lo2 lw sp : Nat) (hk : 1 ≤ k ∧ k < 3) (R : IProp GF)
    (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace)
    (hs : s.prog = b0 ∧ s.q = [] ∧ s.pc = 0 ∧ RK0 k s ∧ fI ws ∧ bp ≤ lo0 ∧ lo0 ≤ coh ws Lk ∧ b1 ≤ lo1 ∧
      lo1 ≤ ws.wVwNew ∧ b2 ≤ lo2 ∧ lo2 ≤ ws.wVwNew ∧ lw ≤ ws.wVwNew ∧ sp ≤ coh ws Pc ∧ sp ≤ ws.wVwOld) :
    ctx7 (GF := GF) g M sv ak ek ∗ ([∗list] d ∈ (rng M).filter (isD M bp), dSl g ek (k - 1) d) ∗ dM ek (k - 1) ∗
      prt g M sv.tk 0 bp lo0 ∗ prt g M sv.tk 1 b1 lo1 ∗ prt g M sv.tk 2 b2 lo2 ∗ ([∗list] t ∈ jB M bp bp, pend g t) ∗
      ([∗list] t ∈ cB M lw, pend g t) ∗ pPts5 g M sp ∗ dep7 M sv bp ∗ QE7 g M 0 ev ∗ R ∗
      (∀ (s' : LP) (ws' : PState) (pr' : GSet Nat) (ev' : Trace) (b' c sp' p : Nat),
        ⌜s'.prog = b0 ∧ s'.q = [] ∧ s'.pc = 8 ∧ RK0 k s' ∧ fI ws' ∧ wsM ws ws' ∧ b' < p ∧ c < p ∧ sp' < p ∧
          p ≤ ws'.wVwOld ∧ (∀ j : Nat, j < 4 → b' ≤ coh ws' (Lk + j)) ∧ zw M b' = true⌝ -∗
        lkB g M sv.tk ak ek b' k -∗ hdl M sv b' (Rb7 g M c sp') -∗ prt g M sv.tk 0 b' b' -∗
        ([∗list] t ∈ jB M b' b', pend g t) -∗ dep7 M sv b' -∗ QE7 g M 0 ev' -∗ R -∗
        lhA g π7 (w7 M 0) (qs7 M 0) ws' pr' ev' -∗ wpKA g π7 (w7 M 0) (qs7 M) s' (Φ7 g M)) ∗
      lhA g π7 (w7 M 0) (qs7 M 0) ws pr ev ⊢ wpKA g π7 (w7 M 0) (qs7 M) s (Φ7 g M) := by
  obtain ⟨hprog, hq, hpc, hrk, hfi, hbl0, hlo0, hb1, hlo1, hb2, hlo2, hlw, hsp, hspo⟩ := hs
  have hw := litW_x xs7 img7 M 0
  iintro ⟨#Hctx, #Hds, #HdM, P0, P1, P2, HJ, HC, HP, Hdep, #HQ, HR, HK, Hl⟩
  -- `li t1,J`
  iapply (wpKA_alui hw (litAg_x hq (p0_at hprog) (by rw [hpc]; rfl) rfl) hq (by rw [hprog, hpc]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hrk1 := RK0_step hrk hs1 (by omega)
  have e6 : s1.rd 6 = J := li_val hs1 (by decide) (by rw [hrk.1]; decide) (by decide)
  -- `sw t1,0(s1)`: kfree's junk in the lock word — THE DEATH of the previous lifetime, or beyond it
  iapply (wpKA_sw (sz := 4) (rs2 := 6) (rs1 := 9) (off := 0) (base := Lk) hw
    (litAg_x hq1 (p0_at hP1) (by rw [hc1]; rfl) rfl) hq1 (by rw [hP1, hc1]; rfl)
    (alg_of hrk1.2.1 (by decide) (by decide)) (base_of hrk1.2.1 (by decide)))
  iframe Hl
  inext
  iintro %j %_ %hmsg %hcoh %hext _ _
  rw [e6] at hmsg
  rw [toBytes_length] at hcoh
  have hv1 : (instrR (regWP ws 6 (srcR 0))).wVwNew = ws.wVwNew := rfl
  have hcL1 : coh (instrR (regWP ws 6 (srcR 0))) Lk = coh ws Lk := rfl
  have hj0 : coh (instrR (regWP ws 6 (srcR 0))) Lk < j := by
    have := cohBelow_at (j := 0) hcoh (by decide); simpa using this
  have hjv : (instrR (regWP ws 6 (srcR 0))).wVwNew < j := Nat.lt_of_le_of_lt (PF.stPreA_ge _ false false _ _).2.2.2.1 hext
  have hmj := msgAt_of (by omega) hmsg
  have hjM := msgAt_le hmj
  have hJ := J2_of hmj
  have hbj : bp < j := by have : coh (instrR (regWP ws 6 (srcR 0))) Lk = coh ws Lk := rfl; omega
  ihave HJ' : |={⊤}=> shot g j ∗ [∗list] t ∈ (rng M).filter (fun t => decide (j < t) && isJ2 M t && bey M bp t),
      pend g t $$ [HJ]
  · cases hn : noJ M bp j
    · unfold jB
      icases bsl_filter_take (pend g) (fun t => decide (bp < t) && isJ2 M t && bey M bp t)
        (fun t => decide (j < t) && isJ2 M t && bey M bp t) j (by simp [hbj, hJ, bey, hn])
        (fun t ht => by simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; exact ⟨⟨⟨by omega, ht.1.2⟩, ht.2⟩,
          by omega⟩) (rng M) (mem_rng.2 hjM) (nodup_rng M) $$ HJ with ⟨Hp, HJ⟩
      imod shoot $$ Hp with #Hsh
      imodintro; iframe Hsh HJ
    · ihave #Hsl := bsl_mem (F := fun d => dSl g ek (k - 1) d)
        (List.mem_filter.2 ⟨mem_rng.2 hjM, by simp [isD, inW, hbj, hn, hJ]⟩) $$ Hds
      imod slot_dep (N := ndot dN7 j) g j (dM ek (k - 1)) $$ [] with #Hsh
      · unfold dSl; iframe Hsl HdM
      imodintro; iframe Hsh
      unfold jB
      iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; exact ⟨⟨by omega, ht.1.2⟩, ht.2⟩) (rng M) $$ HJ
  imod HJ' with ⟨#Hsh, HJ⟩
  have hnc := st_nonC Lk_ne_Ct (toBytes (s1.rd 6) 4) (srcR 9) (srcR 6) j
  ihave #HQ1 := QE7_snoc g M hnc.1 hnc.2 $$ HQ
  imodintro
  isplitr
  · iapply QE7_st g M hnc.1 hnc.2 (ok7_lk (toBytes_length _ 4)) $$ HQ
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s2 %hs2 _ _
  imodintro
  iintro Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have hrk2 := RK0_step hrk1 hs2 (by omega)
  obtain ⟨f2, m2, e2, c2, -⟩ := wsSt_props (instrR (regWP ws 6 (srcR 0))) 9 6 Lk (toBytes (s1.rd 6) 4).length j
    (fI_rw hfi _ _)
  -- `sd t1,0(a1)`: kfree's junk in the field
  iapply (wpKA_sw (sz := 8) (rs2 := 6) (rs1 := 11) (off := 0) (base := Ct) hw
    (litAg_x hq2 (p0_at hP2) (by rw [hc2]; rfl) rfl) hq2 (by rw [hP2, hc2]; rfl)
    (alg_of hrk2.2.2.1 (by decide) (by decide)) (base_of hrk2.2.2.1 (by decide)))
  iframe Hl
  inext
  iintro %jc %_ %hmsg %_ %hext _ _
  have hjcv : (wsSt (instrR (regWP ws 6 (srcR 0))) 9 6 Lk (toBytes (s1.rd 6) 4).length j).wVwNew < jc :=
    Nat.lt_of_le_of_lt (PF.stPreA_ge _ false false _ _).2.2.2.1 hext
  have hmc := msgAt_of (by omega) hmsg
  have hvw2 : ws.wVwNew ≤ (wsSt (instrR (regWP ws 6 (srcR 0))) 9 6 Lk (toBytes (s1.rd 6) 4).length j).wVwNew :=
    m2.2.2.2.2
  icases cB_take (GF := GF) g M (by omega : lw < jc) (C3_CO (C3_of (by decide : 0 < 3) (toBytes_length _ _) hmc))
    (msgAt_le hmc) $$ HC with ⟨Hp, HC⟩
  imod shoot $$ Hp with #Hsh
  have hnl : ∀ tvs, ¬ isCLd (LStore false false Ct (toBytes (s2.rd 6) 8) (srcR 11) (srcR 6), some jc) tvs :=
    fun _ ⟨_, h⟩ => by cases h
  ihave #HQ2 := QE7_snoc0 g M hnl $$ HQ1
  imodintro
  isplitr
  · iapply QE7_ob g M (ok7_far (toBytes_length _ _) (.inl rfl)) $$ HQ2
  isplitr
  · unfold fulT; ileft; iexact Hsh
  iintro %s3 %hs3 _ _
  imodintro
  iintro Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  have hrk3 := RK0_step hrk2 hs3 (by omega)
  obtain ⟨f3, m3, e3, c3, -⟩ := wsSt_props (wsSt (instrR (regWP ws 6 (srcR 0))) 9 6 Lk (toBytes (s1.rd 6) 4).length j)
    11 6 Ct (toBytes (s2.rd 6) 8).length jc f2
  -- INITLOCK `sw zero,0(s1)`: THE BIRTH `b'`, from hart 0's own part; THE RE-SPLIT
  iapply (wpKA_sw (sz := 4) (rs2 := 0) (rs1 := 9) (off := 0) (base := Lk) hw
    (litAg_x hq3 (p0_at hP3) (by rw [hc3]; rfl) rfl) hq3 (by rw [hP3, hc3]; rfl)
    (alg_of hrk3.2.1 (by decide) (by decide)) (base_of hrk3.2.1 (by decide)))
  iframe Hl
  inext
  iintro %b' %_ %hmsg %hcoh %_ _ _
  have hd0 : toBytes (s3.rd 0) 4 = toBytes 0 4 := rfl
  rw [hd0] at hmsg hcoh
  have hjb : j < b' := by
    have h1 : coh (wsSt (wsSt (instrR (regWP ws 6 (srcR 0))) 9 6 Lk (toBytes (s1.rd 6) 4).length j) 11 6 Ct
      (toBytes (s2.rd 6) 8).length jc) (Lk + ((0 : Nat) : Int)) < b' := cohBelow_at (j := 0) hcoh (by decide)
    have h2 := c2 (by rw [toBytes_length]; decide)
    have h3 := m3.1 Lk
    rw [show Lk + ((0 : Nat) : Int) = Lk from by simp] at h1; omega
  have hmb := msgAt_of (by omega) hmsg
  have hbM := msgAt_le hmb
  obtain ⟨hRb, hby0⟩ := R2_of (by decide : 0 < 3) hmb
  have hzb : zw M b' = true := by rw [zw, clsB_of hmb]; exact decide_eq_true ⟨rfl, rfl, rfl⟩
  have hbeyt : ∀ t, b' < t → bey M bp t = true := fun t ht => bey_of hbj (by omega) hJ
  icases prt_birth g M sv.tk (by omega : lo0 < b') hRb hby0 hbM (fun t ht => bey_of hbj (by omega) hJ) $$ P0
    with ⟨Hpb, F0⟩
  imod shoot $$ Hpb with #Hshb
  have hb1j : b1 < j := by omega
  have hb2j : b2 < j := by omega
  ihave F1 := prt_fpt g M sv.tk (h := 1) (by omega : lo1 ≤ b') (fun t ht => bey_of hb1j (by omega) hJ) $$ P1
  ihave F2 := prt_fpt g M sv.tk (h := 2) (by omega : lo2 ≤ b') (fun t ht => bey_of hb2j (by omega) hJ) $$ P2
  ihave HJA : [∗list] t ∈ jA M b', pend g t $$ [HJ]
  · unfold jA
    iapply bsl_filter_mono (pend g) _ _ (fun t ht => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; exact ⟨⟨by omega, ht.2⟩, hbeyt t ht.1⟩) (rng M) $$ HJ
  imod resplit7 g M sv.tk ak ek b' k $$ [F0 F1 F2 HJA] with ⟨#Hlk, P0, HJ⟩
  · iframe F0 F1 F2 HJA
  unfold dep7
  icases bsl_filter_take (fun t => saved_prop_own (GF := GF) (sv.σ t) (.own 1) iprop(True))
    (fun t => decide (bp < t) && zw M t) (fun t => decide (b' < t) && zw M t) b' (by simp [hzb]; omega)
    (fun t ht => by simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; exact ⟨⟨by omega, ht.2⟩, by omega⟩)
    (rng M) (mem_rng.2 hbM) (nodup_rng M) $$ Hdep with ⟨Hσ, Hdep⟩
  have hnc := st_nonC Lk_ne_Ct (toBytes (s3.rd 0) 4) (srcR 9) (srcR 0) b'
  ihave #HQ3 := QE7_snoc g M hnc.1 hnc.2 $$ HQ2
  imodintro
  isplitr
  · iapply QE7_ob g M (ok7_lk (toBytes_length _ 4)) $$ HQ3
  isplitr
  · unfold fulT; ileft; iexact Hshb
  iintro %s4 %hs4 _ _
  imodintro
  iintro Hl
  obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4 hP3 (by rw [hc3])
  have hrk4 := RK0_step hrk3 hs4 (by omega)
  obtain ⟨f4, m4, e4, -, c4⟩ := wsSt_props (wsSt (wsSt (instrR (regWP ws 6 (srcR 0))) 9 6 Lk
    (toBytes (s1.rd 6) 4).length j) 11 6 Ct (toBytes (s2.rd 6) 8).length jc) 9 0 Lk (toBytes (s3.rd 0) 4).length b' f3
  -- `li t2,5`
  iapply (wpKA_alui hw (litAg_x hq4 (p0_at hP4) (by rw [hc4]; rfl) rfl) hq4 (by rw [hP4, hc4]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s5 %hs5 _ _
  imodintro
  iintro Hl
  obtain ⟨hP5, hc5, hq5⟩ := LPstep_at hs5 hP4 (by rw [hc4])
  have hrk5 := RK0_step hrk4 hs5 (by omega)
  have e7 : s5.rd 7 = 5 := li_val hs5 (by decide) (by rw [hrk4.1]; decide) (by decide)
  -- `sd t2,0(a1)`: the field's initialisation `c`
  iapply (wpKA_sw (sz := 8) (rs2 := 7) (rs1 := 11) (off := 0) (base := Ct) hw
    (litAg_x hq5 (p0_at hP5) (by rw [hc5]; rfl) rfl) hq5 (by rw [hP5, hc5]; rfl)
    (alg_of hrk5.2.2.1 (by decide) (by decide)) (base_of hrk5.2.2.1 (by decide)))
  iframe Hl
  inext
  iintro %c %_ %hmsg %hcoh %_ _ _
  rw [e7] at hmsg hcoh
  have hjcc : jc < c := by
    have h1 : coh (instrR (regWP (wsSt (wsSt (wsSt (instrR (regWP ws 6 (srcR 0))) 9 6 Lk (toBytes (s1.rd 6) 4).length j)
      11 6 Ct (toBytes (s2.rd 6) 8).length jc) 9 0 Lk (toBytes (s3.rd 0) 4).length b') 7 (srcR 0)))
      (Ct + ((0 : Nat) : Int)) < c := cohBelow_at (j := 0) hcoh (by decide)
    have h2 := c3 (by rw [toBytes_length]; decide)
    have h3 := m4.1 Ct
    rw [show Ct + ((0 : Nat) : Int) = Ct from by simp] at h1
    have : coh (instrR (regWP (wsSt (wsSt (wsSt (instrR (regWP ws 6 (srcR 0))) 9 6 Lk (toBytes (s1.rd 6) 4).length j)
      11 6 Ct (toBytes (s2.rd 6) 8).length jc) 9 0 Lk (toBytes (s3.rd 0) 4).length b') 7 (srcR 0))) Ct =
      coh (wsSt (wsSt (wsSt (instrR (regWP ws 6 (srcR 0))) 9 6 Lk (toBytes (s1.rd 6) 4).length j)
      11 6 Ct (toBytes (s2.rd 6) 8).length jc) 9 0 Lk (toBytes (s3.rd 0) 4).length b') Ct := rfl
    omega
  have hmc5 := msgAt_of (by omega) hmsg
  have hC5 := C3_of (by decide : 0 < 3) (toBytes_length _ _) hmc5
  icases cB_take (GF := GF) g M hjcc (C3_CO hC5) (msgAt_le hmc5) $$ HC with ⟨Hp, HC⟩
  imod shoot $$ Hp with #Hshc
  have hnl5 : ∀ tvs, ¬ isCLd (LStore false false Ct (toBytes (s5.rd 7) 8) (srcR 11) (srcR 7), some c) tvs :=
    fun _ ⟨_, h⟩ => by cases h
  ihave #HQ5 := QE7_snoc0 g M hnl5 $$ HQ3
  imodintro
  isplitr
  · iapply QE7_ob g M (ok7_far (toBytes_length _ _) (.inl rfl)) $$ HQ5
  isplitr
  · unfold fulT; ileft; iexact Hshc
  iintro %s6 %hs6 _ _
  imodintro
  iintro Hl
  obtain ⟨hP6, hc6, hq6⟩ := LPstep_at hs6 hP5 (by rw [hc5])
  have hrk6 := RK0_step hrk5 hs6 (by omega)
  obtain ⟨f6, m6, e6, -, -⟩ := wsSt_props (instrR (regWP (wsSt (wsSt (wsSt (instrR (regWP ws 6 (srcR 0))) 9 6 Lk
    (toBytes (s1.rd 6) 4).length j) 11 6 Ct (toBytes (s2.rd 6) 8).length jc) 9 0 Lk (toBytes (s3.rd 0) 4).length b')
    7 (srcR 0))) 11 7 Ct (toBytes (s5.rd 7) 8).length c (fI_rw f4 _ _)
  -- `fence rw,w`
  iapply (wpKA_fence hw (litAg_x hq6 (p0_at hP6) (by rw [hc6]; rfl) rfl) hq6 (by rw [hP6, hc6]; rfl))
  iframe Hl
  inext
  iintro %s7 %hs7 _ _
  imodintro
  iintro Hl
  obtain ⟨hP7, hc7, hq7⟩ := LPstep_at hs7 hP6 (by rw [hc6])
  have hrk7 := RK0_step hrk6 hs7 (by omega)
  have hZ0 : (Z + 0) % two64 = Z := by simp [Z, two64]
  -- `sb a3,0(a2)`: THE PUBLICATION of round `k`
  iapply (wpKA_sw (sz := 1) (rs2 := 13) (rs1 := 12) (off := 0) (base := (Z : Int) + ((0 : Nat) : Int)) hw
    (litAg_x hq7 (p0_at hP7) (by rw [hc7]; rfl) rfl) hq7 (by rw [hP7, hc7]; rfl)
    (by rw [hrk7.2.2.2.1]; simp [aligned, Nat.mod_one]) (by rw [hrk7.2.2.2.1, hZ0]; omega))
  iframe Hl
  inext
  iintro %p %_ %hmsg %_ %hext _ Hcr
  have hWS := wsSt (instrR (regWP (wsSt (wsSt (wsSt (instrR (regWP ws 6 (srcR 0))) 9 6 Lk (toBytes (s1.rd 6) 4).length j)
    11 6 Ct (toBytes (s2.rd 6) 8).length jc) 9 0 Lk (toBytes (s3.rd 0) 4).length b') 7 (srcR 0))) 11 7 Ct
    (toBytes (s5.rd 7) 8).length c
  have hpf : (instrR (fencePost (wsSt (instrR (regWP (wsSt (wsSt (wsSt (instrR (regWP ws 6 (srcR 0))) 9 6 Lk
      (toBytes (s1.rd 6) 4).length j) 11 6 Ct (toBytes (s2.rd 6) 8).length jc) 9 0 Lk (toBytes (s3.rd 0) 4).length b')
      7 (srcR 0))) 11 7 Ct (toBytes (s5.rd 7) 8).length c) true true false true)).wVwNew < p :=
    Nat.lt_of_le_of_lt (PF.stPreA_ge _ false false _ _).2.2.2.1 hext
  have hvo6 : max (max b' sp) c ≤ (instrR (fencePost (wsSt (instrR (regWP (wsSt (wsSt (wsSt (instrR (regWP ws 6
      (srcR 0))) 9 6 Lk (toBytes (s1.rd 6) 4).length j) 11 6 Ct (toBytes (s2.rd 6) 8).length jc) 9 0 Lk
      (toBytes (s3.rd 0) 4).length b') 7 (srcR 0))) 11 7 Ct (toBytes (s5.rd 7) 8).length c) true true false
      true)).wVwNew := by
    simp only [instrR_vwNew, fence_vwNew, ite_true]; rw [e6]
    have h1 : (instrR (regWP (wsSt (wsSt (wsSt (instrR (regWP ws 6 (srcR 0))) 9 6 Lk (toBytes (s1.rd 6) 4).length j)
      11 6 Ct (toBytes (s2.rd 6) 8).length jc) 9 0 Lk (toBytes (s3.rd 0) 4).length b') 7 (srcR 0))).wVwOld =
      (wsSt (wsSt (wsSt (instrR (regWP ws 6 (srcR 0))) 9 6 Lk (toBytes (s1.rd 6) 4).length j)
      11 6 Ct (toBytes (s2.rd 6) 8).length jc) 9 0 Lk (toBytes (s3.rd 0) 4).length b').wVwOld := rfl
    have h2 := m3.2.2.1; have h3 := m2.2.2.1
    have h4 : (instrR (regWP ws 6 (srcR 0))).wVwOld = ws.wVwOld := rfl
    rw [h1, e4]; omega
  have hmp := msgAt_of (by omega) hmsg
  have hpM := msgAt_le hmp
  have hfp := fB_of (o := 0) (toBytes_length _ _) hmp
  have hval : val7 M p = k := by
    have h13 : s7.rd 13 = k := hrk7.2.2.2.2.1
    simp [val7, hmp, toBytes, Weak.Prom.Ref.byteList, bv8, h13]; omega
  unfold ctx7
  icases Hctx with ⟨Hdoom, Hps, Hn1, Hn2, Hfj, Hbs⟩
  ihave #Hbsl := bsl_mem (F := fun t => bSlot M sv t) (List.mem_filter.2 ⟨mem_rng.2 hbM, hzb⟩) $$ Hbs
  ihave #Hpsl := bsl_mem (F := fun t => pSl g M sv ak ek t) (List.mem_filter.2 ⟨mem_rng.2 hpM, hfp⟩) $$ Hps
  -- (a) THE DEFERRED DEPOSIT of the birth `b'` (shape-only birth slot)
  imod bslot_deposit M sv b' (Rb7 g M c sp) $$ [Hσ HC HP Hcr] with ⟨#Hds, #HsQ⟩
  · iframe Hbsl Hσ Hcr; unfold Rb7 cPts5; iframe HC HP; ipureintro; exact ⟨hC5, .inl hmc5⟩
  -- (b) THE PUBLICATION: the handle and the protocol of the lock born at `b'` in round `k`
  imod slot_dep (N := ndot pN7 p) g p (Pub7 g M sv ak ek p) $$ [] with #Hshp
  · unfold pSl; iframe Hpsl
    unfold Pub7; iexists b'; iexists c; iexists sp
    isplitr
    · ipureintro; exact ⟨by omega, by omega, by omega, hmc5⟩
    rw [hval]; iframe Hlk; unfold hdl; iframe Hds HsQ Hbsl; ipureintro; exact hzb
  have hnc := st_nonC (b := (Z : Int) + ((0 : Nat) : Int)) (by simp [Z, Ct, Y]) (toBytes (s7.rd 13) 1) (srcR 12)
    (srcR 13) p
  ihave #HQ7 := QE7_snoc g M hnc.1 hnc.2 $$ HQ5
  imodintro
  isplitr
  · iapply QE7_ob g M (ok7_z (o := 0) (by decide) (toBytes_length _ 1)) $$ HQ7
  isplitr
  · unfold fulT; ileft; iexact Hshp
  iintro %s8 %hs8 _ _
  imodintro
  iintro Hl
  obtain ⟨hP8, hc8, hq8⟩ := LPstep_at hs8 hP7 (by rw [hc7])
  obtain ⟨f8, m8, e8, -, -⟩ := wsSt_props (instrR (fencePost (wsSt (instrR (regWP (wsSt (wsSt (wsSt (instrR (regWP ws 6
      (srcR 0))) 9 6 Lk (toBytes (s1.rd 6) 4).length j) 11 6 Ct (toBytes (s2.rd 6) 8).length jc) 9 0 Lk
      (toBytes (s3.rd 0) 4).length b') 7 (srcR 0))) 11 7 Ct (toBytes (s5.rd 7) 8).length c) true true false true))
    12 13 ((Z : Int) + ((0 : Nat) : Int)) (toBytes (s7.rd 13) 1).length p (fI_fn f6 _ _ _ _)
  have k3 := wsM_trans (wsM_trans (wsM_trans (wsM_rw ws 6 (srcR 0)) m2) m3) m4
  have k5 := wsM_trans (wsM_trans (wsM_rw _ 7 (srcR 0)) m6) (wsM_trans (wsM_fn _ true true false true) m8)
  iapply HK $$ %s8 %_ %_ %_ %b' %c %sp %p %⟨hP8, hq8, hc8, RK0_step hrk7 hs8 (by omega), f8, wsM_trans k3 k5,
    by omega, by omega, by omega, by rw [e8]; omega,
    fun j hj => Nat.le_trans (c4 j (by rw [toBytes_length]; exact hj)) (k5.1 _), hzb⟩
    [] [] P0 HJ Hdep HQ7 HR Hl
  · iexact Hlk
  · unfold hdl; iframe Hds HsQ Hbsl; ipureintro; exact hzb

theorem prt_out (g : AGN) (M : List PMsg) (tk : Nat → GName) (h b lo : Nat) :
    prt (GF := GF) g M tk h b lo ⊢ obg g M tk h lo 0 ∗ [∗list] t ∈ rB M h b lo, pend g t := by unfold prt; exact .rfl
theorem prt_in (g : AGN) (M : List PMsg) (tk : Nat → GName) (h b lo : Nat) :
    obg (GF := GF) g M tk h lo 0 ∗ ([∗list] t ∈ rB M h b lo, pend g t) ⊢ prt g M tk h b lo := by unfold prt; exact .rfl

theorem ep_take (ek : Nat → Nat → GName) (k : Nat) (hk : k < 3) :
    ([∗list] k' ∈ (List.range 3).filter (fun k' => decide (k ≤ k')), eP (GF := GF) ek 0 k') ⊢
      eP ek 0 k ∗ [∗list] k' ∈ (List.range 3).filter (fun k' => decide (k + 1 ≤ k')), eP ek 0 k' :=
  bsl_filter_take (fun k' => eP (GF := GF) ek 0 k') _ _ k (by simp)
    (fun t ht => by simp at ht ⊢; omega) (List.range 3) (List.mem_range.2 hk) List.nodup_range

theorem lkB_dsl (g : AGN) (M : List PMsg) (tk : Nat → GName) (ak ek : Nat → Nat → GName) (b k : Nat) :
    lkB (GF := GF) g M tk ak ek b k ⊢ [∗list] d ∈ (rng M).filter (isD M b), dSl g ek k d := by
  unfold lkB; iintro ⟨-, H, -⟩; iexact H

theorem tkF_take (tk : Nat → GName) (M : List PMsg) {o k t : Nat} (hf : fB o M t = true) (hv : val7 M t = k)
    (htM : 1 ≤ t ∧ t ≤ M.length) : ([∗list] t ∈ tkF M o k, token (GF := GF) (tk t)) ⊢
      token (tk t) ∗ [∗list] t ∈ tkF M o (k + 1), token (tk t) := by
  unfold tkF
  exact bsl_filter_take (fun t => token (tk t)) _ _ t (by simp [hf, hv])
    (fun u hu => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hu ⊢
      exact ⟨⟨hu.1, by omega⟩, fun e => by subst e; omega⟩)
    (rng M) (mem_rng.2 htM) (nodup_rng M)

/-- Claim a done byte read below the frontier: the acquirer's returned part and participation. -/
theorem done_claim (g : AGN) (M : List PMsg) (sv : SV) (ak ek : Nat → Nat → GName) (hdd : g.dd = fun _ => False)
    {ws : PState} {o k t : Nat} (ho : o = 1 ∨ o = 2) (htM : 1 ≤ t ∧ t ≤ M.length) (ht : t ≤ wfr ws)
    (hc : (fB o M t = true ∧ val7 M t = k) ∨ fJ7 M t = true) :
    ctx7 (GF := GF) g M sv ak ek ∗ frontA g π7 img7 M ws ∗ ([∗list] t ∈ tkF M o k, token (sv.tk t)) ⊢
      |={⊤}=> ([∗list] t ∈ tkF M o (k + 1), token (sv.tk t)) ∗
        ∃ b lo, ⌜b ≤ lo ∧ lo < t⌝ ∗ prt g M sv.tk o b lo ∗ eP ek o k := by
  iintro ⟨#Hctx, #Hfr, Htk⟩
  rcases hc with ⟨hf, hv⟩ | hJ
  · unfold ctx7
    icases Hctx with ⟨Hdoom, -, Hn1, Hn2, -⟩
    imod frontS g M hdd (π := π7) (img := img7) t ⟨htM.1, htM.2, ht⟩ $$ [] with #Hsh
    · iframe Hdoom Hfr
    icases tkF_take sv.tk M hf hv htM $$ Htk with ⟨Ht, Htk⟩
    ihave #Hns : nSl g M sv.tk ek o t $$ []
    · rcases ho with rfl | rfl
      · iapply bsl_mem (F := fun t => nSl g M sv.tk ek 1 t) (List.mem_filter.2 ⟨mem_rng.2 htM, hf⟩) $$ Hn1
      · iapply bsl_mem (F := fun t => nSl g M sv.tk ek 2 t) (List.mem_filter.2 ⟨mem_rng.2 htM, hf⟩) $$ Hn2
    imod nclaim7 g M sv.tk ek o t $$ [Ht] with HD
    · iframe Hns Hsh Ht
    unfold Dn7; rw [hv]; iframe Htk; iexact HD
  · imod fj_front g M sv ak ek hdd (π := π7) (img := img7) htM ht hJ $$ [] with %hf
    · iframe Hctx Hfr
    exact hf.elim

set_option maxHeartbeats 4000000 in
/-- **HART 0's ROUNDS** (induction on the rounds left): kfree, initlock and publication (`h0A`), the two done
bytes (the acquirers' parts and participations RETURNED), pipeclose: xv6's acquire, the death mark, xv6's release
DEPOSITING THE DEATH MARK (the resource kept for the next kfree), the next round. -/
theorem h0R (g : AGN) (M : List PMsg) (sv : SV) (ak ek : Nat → Nat → GName) (hdd : g.dd = fun _ => False)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :
    ∀ n k, k + n = 3 → 1 ≤ k → 0 < n → ⊢ ∀ (s : LP) (ws : PState) (pr : GSet Nat) (ev : Trace)
      (bp lo0 b1 lo1 b2 lo2 lw sp : Nat),
      ⌜s.prog = b0 ∧ s.q = [] ∧ s.pc = 0 ∧ RK0 k s ∧ fI ws ∧ bp ≤ lo0 ∧ lo0 ≤ coh ws Lk ∧ b1 ≤ lo1 ∧
        lo1 ≤ ws.wVwNew ∧ b2 ≤ lo2 ∧ lo2 ≤ ws.wVwNew ∧ lw ≤ ws.wVwNew ∧ sp ≤ coh ws Pc ∧ sp ≤ ws.wVwOld⌝ -∗
      ctx7 (GF := GF) g M sv ak ek -∗ ([∗list] d ∈ (rng M).filter (isD M bp), dSl g ek (k - 1) d) -∗
      dM ek (k - 1) -∗ prt g M sv.tk 0 bp lo0 -∗ prt g M sv.tk 1 b1 lo1 -∗ prt g M sv.tk 2 b2 lo2 -∗
      ([∗list] t ∈ jB M bp bp, pend g t) -∗ ([∗list] t ∈ cB M lw, pend g t) -∗ pPts5 g M sp -∗ dep7 M sv bp -∗
      ([∗list] k' ∈ (List.range 3).filter (fun k' => decide (k ≤ k')), eP ek 0 k') -∗
      ([∗list] t ∈ tkF M 1 k, token (sv.tk t)) -∗ ([∗list] t ∈ tkF M 2 k, token (sv.tk t)) -∗ QE7 g M 0 ev -∗
      lhA g π7 (w7 M 0) (qs7 M 0) ws pr ev -∗ wpKA g π7 (w7 M 0) (qs7 M) s (Φ7 g M) := by
  intro n
  induction n with
  | zero => intro k hk h1 h0; omega
  | succ n IH =>
  intro k hkn hk1 _
  have hw := litW_x xs7 img7 M 0
  iintro %s %ws %pr %ev %bp %lo0 %b1 %lo1 %b2 %lo2 %lw %sp %hs #Hctx #Hds #HdM P0 P1 P2 HJ HC HP Hdep He T1 T2 #HQ Hl
  iapply (h0A g M sv ak ek hdd k bp lo0 b1 lo1 b2 lo2 lw sp ⟨hk1, by omega⟩
    iprop(([∗list] k' ∈ (List.range 3).filter (fun k' => decide (k ≤ k')), eP ek 0 k') ∗
      ([∗list] t ∈ tkF M 1 k, token (sv.tk t)) ∗ ([∗list] t ∈ tkF M 2 k, token (sv.tk t))) s ws pr ev hs)
  iframe Hctx Hds HdM P0 P1 P2 HJ HC HP Hdep HQ Hl
  isplitl [He T1 T2]
  · iframe He T1 T2
  iintro %s1 %ws1 %pr1 %ev1 %b %c %sp' %p %⟨hP1, hq1, hc1, hrk1, hfi1, hmo1, hbp, hcp, hsp, hpw, hbc, hzb⟩
    #Hlk #Hl7 P0 HJ Hdep #HQ1 ⟨He, T1, T2⟩ Hl
  -- the two done bytes
  ihave Hw1 := waitG (GF := GF) g M 0 p0 xOf_p0 8 1 k (by decide) ⟨by omega, by omega⟩ rfl rfl (by decide) (RK0 k)
    (fun s hs => ⟨hs.2.2.2.1, hs.2.2.2.2.1, hs.1⟩) (fun s s' pc rd v hr hs hrd => RK0_step hr hs (by omega)) hnoinv
    iprop(prt g M sv.tk 0 b b ∗ ([∗list] t ∈ jB M b b, pend g t) ∗ dep7 M sv b ∗
      ([∗list] k' ∈ (List.range 3).filter (fun k' => decide (k ≤ k')), eP ek 0 k') ∗
      ([∗list] t ∈ tkF M 1 k, token (sv.tk t)) ∗ ([∗list] t ∈ tkF M 2 k, token (sv.tk t))) ws1
  iapply Hw1 $$ %s1 %ws1 %pr1 %ev1 %⟨hP1, hq1, hc1, hrk1, hfi1, wsM_refl _⟩ HQ1 [P0 HJ Hdep He T1 T2] [] Hl
  · iframe P0 HJ Hdep He T1 T2
  iintro %s2 %ws2 %pr2 %ev2 %t1 %⟨hP2, hq2, hc2, hrk2, hfi2, hmo2, ht11, ht1M, ht1v, hcl1⟩ #HQ2 R Hl
  ihave Hw2 := waitG (GF := GF) g M 0 p0 xOf_p0 10 2 k (by decide) ⟨by omega, by omega⟩ rfl rfl (by decide) (RK0 k)
    (fun s hs => ⟨hs.2.2.2.1, hs.2.2.2.2.1, hs.1⟩) (fun s s' pc rd v hr hs hrd => RK0_step hr hs (by omega)) hnoinv
    iprop(prt g M sv.tk 0 b b ∗ ([∗list] t ∈ jB M b b, pend g t) ∗ dep7 M sv b ∗
      ([∗list] k' ∈ (List.range 3).filter (fun k' => decide (k ≤ k')), eP ek 0 k') ∗
      ([∗list] t ∈ tkF M 1 k, token (sv.tk t)) ∗ ([∗list] t ∈ tkF M 2 k, token (sv.tk t))) ws2
  iapply Hw2 $$ %s2 %ws2 %pr2 %ev2 %⟨hP2, hq2, hc2, hrk2, hfi2, wsM_refl _⟩ HQ2 R [] Hl
  iintro %s3 %ws3 %pr3 %ev3 %t2 %⟨hP3, hq3, hc3, hrk3, hfi3, hmo3, ht21, ht2M, ht2v, hcl2⟩ #HQ3
    ⟨P0, HJ, Hdep, He, T1, T2⟩ Hl
  -- `fence rw,rw`: both done bytes below the frontier
  iapply (wpKA_fence hw (litAg_x hq3 (p0_at hP3) (by rw [hc3]; rfl) rfl) hq3 (by rw [hP3, hc3]; rfl))
  iframe Hl
  inext
  iintro %s4 %hs4 #Hfr _
  obtain ⟨hP4, hc4, hq4⟩ := LPstep_at hs4 hP3 (by rw [hc3])
  have hrk4 := RK0_step hrk3 hs4 (by omega)
  have hvf : max ws3.wVrOld ws3.wVwOld ≤ wfr (fencePost ws3 true true true true) := by
    refine Nat.le_trans ?_ (wfr_ge_vwNew _); simp only [fence_vwNew, ite_true]; omega
  have ht1f : t1 ≤ max ws3.wVrOld ws3.wVwOld := by have := hmo3.2.1; have := hmo3.2.2.1; omega
  imod done_claim g M sv ak ek hdd (ws := fencePost ws3 true true true true) (o := 1) (.inl rfl) ⟨ht11, ht1M⟩
    (Nat.le_trans ht1f hvf) hcl1 $$ [T1]
    with ⟨T1, %b1', %lo1', %hl1, P1, E1⟩
  · iframe Hctx Hfr T1
  imod done_claim g M sv ak ek hdd (ws := fencePost ws3 true true true true) (o := 2) (.inr rfl) ⟨ht21, ht2M⟩
    (Nat.le_trans ht2v hvf) hcl2 $$ [T2]
    with ⟨T2, %b2', %lo2', %hl2, P2, E2⟩
  · iframe Hctx Hfr T2
  imodintro
  iintro Hl
  -- `li a4,1`
  iapply (wpKA_alui hw (litAg_x hq4 (p0_at hP4) (by rw [hc4]; rfl) rfl) hq4 (by rw [hP4, hc4]; rfl) (by decide))
  iframe Hl
  inext
  iintro %s5 %hs5 _ _
  imodintro
  iintro Hl
  obtain ⟨hP5, hc5, hq5⟩ := LPstep_at hs5 hP4 (by rw [hc4])
  have hrk5 := RK0_step hrk4 hs5 (by omega)
  have h14 : s5.rd 14 = 1 := li_val hs5 (by decide) (by rw [hrk4.1]; decide) (by decide)
  have hm5 := wsM_trans (wsM_trans (wsM_trans hmo2 hmo3) (wsM_fn ws3 true true true true)) (wsM_rw _ 14 (srcR 0))
  have hv5 : max ws3.wVrOld ws3.wVwOld ≤ (instrR (regWP (instrR (fencePost ws3 true true true true)) 14
      (srcR 0))).wVrNew ∧ max ws3.wVrOld ws3.wVwOld ≤ (instrR (regWP (instrR (fencePost ws3 true true true true)) 14
      (srcR 0))).wVwNew := by
    simp only [instrR_vrNew, regWP_vrNew, instrR_vwNew, regWP_vwNew, fence_vrNew, fence_vwNew, ite_true]; omega
  have hpw3 : p ≤ ws3.wVwOld := Nat.le_trans hpw (Nat.le_trans hmo2.2.2.1 hmo3.2.2.1)
  icases prt_out g M sv.tk 0 b b $$ P0 with ⟨Ho0, Hr0⟩
  icases ep_take ek k (by omega) $$ He with ⟨E0, He⟩
  -- pipeclose: XV6's ACQUIRE
  ihave Hloop := loopG (GF := GF) g M sv ak ek 0 (by decide) hdd hnoinv p0 xOf_p0 14 rfl rfl rfl rfl (by decide)
    (fun s => RK0 k s ∧ s.rd 14 = 1) (fun s hs => ⟨hs.1.2.1, hs.2, hs.1.1⟩)
    (fun s s' pc rd v hr hs hrd => ⟨RK0_step hr.1 hs (by omega), by rw [LPstep_rd hs 14 (by omega), hr.2]⟩)
    b k c sp' p hzb hcp hsp
    iprop(([∗list] t ∈ jB M b b, pend g t) ∗ dep7 M sv b ∗
      ([∗list] k' ∈ (List.range 3).filter (fun k' => decide (k + 1 ≤ k')), eP ek 0 k') ∗
      ([∗list] t ∈ tkF M 1 (k + 1), token (sv.tk t)) ∗ ([∗list] t ∈ tkF M 2 (k + 1), token (sv.tk t)) ∗
      prt g M sv.tk 1 b1' lo1' ∗ prt g M sv.tk 2 b2' lo2' ∗ eP ek 1 k ∗ eP ek 2 k)
    (instrR (regWP (instrR (fencePost ws3 true true true true)) 14 (srcR 0)))
  have hlo5 : b ≤ max (instrR (regWP (instrR (fencePost ws3 true true true true)) 14 (srcR 0))).wVrNew
      (coh (instrR (regWP (instrR (fencePost ws3 true true true true)) 14 (srcR 0))) Lk) := by
    have h0 := hbc 0 (by decide); rw [show Lk + ((0 : Nat) : Int) = Lk from by simp] at h0
    have := hm5.1 Lk; omega
  iapply Hloop $$ %s5 %(instrR (regWP (instrR (fencePost ws3 true true true true)) 14 (srcR 0))) %_ %_ %b
    %⟨hP5, hq5, hc5, ⟨hrk5, h14⟩, fI_rw (fI_fn hfi3 _ _ _ _) _ _, wsM_refl _,
      by omega, by omega, fun j hj => by have := hbc j hj; have := hm5.1 (Lk + j); omega, Nat.le_refl _, hlo5⟩
    Hctx Hlk Hl7 Ho0 Hr0 E0 HQ3 [HJ Hdep He T1 T2 P1 P2 E1 E2] [] Hl
  · iframe HJ Hdep He T1 T2 P1 P2 E1 E2
  iintro %s6 %ws6 %pr6 %ev6 %ts %lw2 %sq %⟨hP6, hq6, hc6, ⟨hrk6, -⟩, hfi6, hmo6, hbts, hcts, -, -, -, hlww, hsqw⟩
    Ho0 Hr0 E0 HC HP #HQ6 ⟨HJ, Hdep, He, T1, T2, P1, P2, E1, E2⟩ Hl
  -- THE DEATH MARK of round `k`: every participation given up
  iapply wpKA_fupd
  imod dM_alloc ek k $$ [E0 E1 E2] with #HdM'
  · iframe E0 E1 E2
  imodintro
  -- `sd a0,16(s1)`
  iapply (cpu1G g M 0 p0 xOf_p0 18 rfl (RK0 k) (fun s hs => hs.2.1) (fun s s' pc v hr hs => RK0_step hr hs (by omega))
    iprop(obg g M sv.tk 0 ts 0 ∗ ([∗list] t ∈ rB M 0 b ts, pend g t) ∗ cPts5 g M lw2 ∗ ([∗list] t ∈ jB M b b, pend g t) ∗
      dep7 M sv b ∗ ([∗list] k' ∈ (List.range 3).filter (fun k' => decide (k + 1 ≤ k')), eP ek 0 k') ∗
      ([∗list] t ∈ tkF M 1 (k + 1), token (sv.tk t)) ∗ ([∗list] t ∈ tkF M 2 (k + 1), token (sv.tk t)) ∗
      prt g M sv.tk 1 b1' lo1' ∗ prt g M sv.tk 2 b2' lo2')
    ws6 s6 ws6 pr6 ev6 sq ⟨hP6, hq6, hc6, hrk6, hfi6, wsM_refl _, hsqw⟩)
  iframe HP HQ6 Hl
  isplitl [Ho0 Hr0 HC HJ Hdep He T1 T2 P1 P2]
  · iframe Ho0 Hr0 HC HJ Hdep He T1 T2 P1 P2
  iintro %s7 %ws7 %pr7 %ev7 %ts1 %⟨hP7, hq7, hc7, hrk7, hfi7, hmo7, hts1P, -⟩ HP #HQ7
    ⟨Ho0, Hr0, HC, HJ, Hdep, He, T1, T2, P1, P2⟩ Hl
  have hts7 : ts ≤ coh ws7 Lk := by
    have := hcts 0 (by decide); rw [show Lk + ((0 : Nat) : Int) = Lk from by simp] at this
    exact Nat.le_trans this (hmo7.1 Lk)
  -- xv6's RELEASE, DEPOSITING THE DEATH MARK
  iapply (relG g M sv ak ek 0 (by decide) p0 xOf_p0 19 rfl rfl rfl (RK0 k) (fun s hs => hs.2.1)
    (fun s s' pc v hr hs => RK0_step hr hs (by omega))
    iprop(([∗list] t ∈ jB M b b, pend g t) ∗ dep7 M sv b ∗
      ([∗list] k' ∈ (List.range 3).filter (fun k' => decide (k + 1 ≤ k')), eP ek 0 k') ∗
      ([∗list] t ∈ tkF M 1 (k + 1), token (sv.tk t)) ∗ ([∗list] t ∈ tkF M 2 (k + 1), token (sv.tk t)) ∗
      prt g M sv.tk 1 b1' lo1' ∗ prt g M sv.tk 2 b2' lo2')
    ws7 true b k s7 ws7 pr7 ev7 ts lw2 ts1
    ⟨hP7, hq7, hc7, hrk7, hfi7, wsM_refl _, hbts, hts7, (fun h => by cases h), hts1P⟩)
  iframe Hctx Hlk Ho0 Hr0 HC HP HQ7 Hl
  isplitr
  · iright; iframe HdM'; ipureintro; rfl
  isplitl [HJ Hdep He T1 T2 P1 P2]
  · iframe HJ Hdep He T1 T2 P1 P2
  iintro %s8 %ws8 %pr8 %ev8 %r %tc %⟨hP8, hq8, hc8, hrk8, hfi8, hmo8, hbr, hrL, -, htcP, htcw⟩ Ho0 Hr0
    (%hf | ⟨-, HC, HP⟩) #HQ8 ⟨HJ, Hdep, He, T1, T2, P1, P2⟩ Hl
  · cases hf
  -- the next round
  iapply (roundG g M 0 p0 xOf_p0 22 rfl rfl rfl
    iprop(obg g M sv.tk 0 r 0 ∗ ([∗list] t ∈ rB M 0 b r, pend g t) ∗ cPts5 g M lw2 ∗ pPts5 g M tc ∗
      ([∗list] t ∈ jB M b b, pend g t) ∗ dep7 M sv b ∗
      ([∗list] k' ∈ (List.range 3).filter (fun k' => decide (k + 1 ≤ k')), eP ek 0 k') ∗
      ([∗list] t ∈ tkF M 1 (k + 1), token (sv.tk t)) ∗ ([∗list] t ∈ tkF M 2 (k + 1), token (sv.tk t)) ∗
      prt g M sv.tk 1 b1' lo1' ∗ prt g M sv.tk 2 b2' lo2')
    s8 ws8 pr8 ev8 k ⟨hP8, hq8, hc8, hrk8.2.2.2.2.1, hrk8.2.2.2.2.2, hrk8.1, by omega, hfi8⟩)
  iframe Hl
  isplitl [Ho0 Hr0 HC HP HJ Hdep He T1 T2 P1 P2]
  · iframe Ho0 Hr0 HC HP HJ Hdep He T1 T2 P1 P2
  iintro %s9 %ws9 %⟨hk', hP9, hq9, hc9, h13, hreg, hl9, hfi9, hmo9⟩
    ⟨Ho0, Hr0, HC, HP, HJ, Hdep, He, T1, T2, P1, P2⟩ Hl
  have hvw9 : max ws3.wVrOld ws3.wVwOld ≤ ws9.wVwNew := Nat.le_trans hv5.2 (Nat.le_trans hmo6.2.2.2.2
    (Nat.le_trans hmo7.2.2.2.2 (Nat.le_trans hmo8.2.2.2.2 hmo9.2.2.2.2)))
  have hlw9 : lw2 ≤ ws9.wVwNew := Nat.le_trans hlww (Nat.le_trans hmo7.2.2.2.2 (Nat.le_trans hmo8.2.2.2.2
    hmo9.2.2.2.2))
  ihave Hn := IH (k + 1) (by omega) (by omega) (by omega)
  simp only [Nat.add_sub_cancel]
  unfold cPts5
  icases HC with ⟨-, HC⟩
  iapply Hn $$ %s9 %ws9 %_ %_ %b %r %b1' %lo1' %b2' %lo2' %lw2 %tc
    %⟨hP9, hq9, hc9, ⟨hl9, by rw [hreg 9 (by decide)]; exact hrk8.2.1, by rw [hreg 11 (by decide)]; exact hrk8.2.2.1,
      by rw [hreg 12 (by decide)]; exact hrk8.2.2.2.1, h13, by rw [hreg 28 (by decide)]; exact hrk8.2.2.2.2.2⟩, hfi9,
      by omega, Nat.le_trans hrL (hmo9.1 Lk),
      hl1.1, by omega, hl2.1, by omega, hlw9, Nat.le_trans htcP (hmo9.1 Pc), Nat.le_trans htcw hmo9.2.2.1⟩
    Hctx [] HdM' [Ho0 Hr0] P1 P2 HJ HC HP Hdep He T1 T2 HQ8 Hl
  · iapply lkB_dsl g M sv.tk ak ek b k $$ Hlk
  · iapply prt_in g M sv.tk 0 b r $$ [Ho0 Hr0]; iframe Ho0 Hr0

end h0

end Weak.Prom.OA.E4
