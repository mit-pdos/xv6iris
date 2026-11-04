/-
Weak/Prom: **G4 target (1b), the manual's Example 2 spinlock with a counter client, PROVED on track (b)** (stage
S4b part 3, tag S4b3; plan rev 7 §4 "Gate G4" (1b): `amoswap.w; fence r,rw` / `fence rw,w; amoswap.w x0,x0,(a0)`).

Test `lk1bT` (real litmus front end; counter `c` = 0x1000 (8 bytes), lock word `lk` = 0x2000 (4 bytes), image 0),
both harts run
`amoswap.w x5,x6,(x10); fence r,rw; bne x5,x0,END; ld x7,(x11); addi x7,x7,1; sd x7,(x11); fence rw,w;
 amoswap.w x0,x0,(x10)` (x6 = 1).  Forward branches only: a failed acquire gives up (finite runs; the prefix lemma
S3d is separate).  Verdict as (1a): if both harts acquired (x5 = 0), their final x7 differ.

THE RUN SHAPE: NF_R with the PRE-STATE RELEASE CLASS (NfrPre.lean, finding of S4b3).  With plan §3's class the
release `fence rw,w; amoswap.w x0,x0` is not always release-class (its read half may return another hart's later
attempt), and the plan's (b1-def) deferred deposit is vacuous here (the release AMO is the hart's last write).  With
`relClassPre` the release IS always in place (`relClassPre_fW_amo`: `fence rw,w` raised `vwNew` to
`vrOld ⊔ vwOld` and a non-aq read half leaves `vwNew` alone), so the deposit is (1a)'s in-place deposit.
The acquire `amoswap.w` (no aq) is ordered before the critical section by `fence r,rw` and M0 (iv) (`amoPost`:
`vrOld ⊔= ts`, Machine.lean), which gives the critical section's floors `ts ≤ vrNew, vwNew` (`fRRW_floor`).

The protocol (LkS, THE (b1) PULL, the AMO leaf, the counter clauses) is (1a)'s, unchanged (OwnLockDefs …
OwnLockSteps2.lean: every step lemma is stated for any release class `rc` of the fulfil fact `fulO`).  The Iris
layer is (1a)'s (OwnLock.lean: ghost state, `Xf`, `KB` … `KG`), re-run instruction by instruction through the
Pre kit (OwnKitPre.lean).  0 named inputs; PO-fetch (`lit_fetchBoundedPre`) and `invalFree` (`lit_invalFree`, R-b5:
drops with the machine fix) per program.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnLock
import Weak.Prom.OwnKitPre

namespace Weak.Prom.Own.Pre.Lk1b

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Own (OSt OW fulO rmwOk litOW litDoneR litDoneR_end take_msg upd upd_eq upd_ne agentStep doneOf σ0)
open Weak.Prom.Own.Lk
open Weak.Prom.Nfr (invalFree)
open Weak.Prom.Own.MP (wrA au wrA_of_memByte)
open Weak.Prom.Own.MPL (XRec loadOk_byte val8 rd_regs fwdView_psInit bytesAll_get)
open Weak.Prom.PF (LPstep LPstep_at LPstep_rd LPstep_rd_eq ldVal instrR amoD)
open Weak.Prom.Ref (Instr Test two64)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The test, machine facts -/

/-- One hart's program (both harts run it): the manual's Example 2 lock around the counter. -/
def lk1bProg : List Instr :=
  [Weak.Prom.Ref.Lit.amoswapW false false 5 6 10, Weak.Prom.Ref.Lit.fRRW, .br .ne 5 0 8, Weak.Prom.Ref.Lit.ld 7 11,
   .alui .add 7 7 1, Weak.Prom.Ref.Lit.sd 7 11, Weak.Prom.Ref.Lit.fRWW, Weak.Prom.Ref.Lit.amoswapW false false 0 0 10]

/-- G4 (1b): two harts, the manual's Example 2 lock around a counter. -/
def lk1bT : Test :=
  { harts := [lk1bProg, lk1bProg]
    regs0 := [lkRegs0, lkRegs0]
    img := []
    cond := Weak.Prom.Ref.Lit.mpFF.cond }

theorem lk1bImg : testImg lk1bT = lkImg := rfl

theorem loadBytes_vwNew (vpre : Nat) : ∀ (ws : PState) (a : Int) (tvs : List (Nat × BitVec 8)),
    (loadBytes false vpre ws a tvs).wVwNew = ws.wVwNew
  | _, _, [] => rfl
  | ws, a, (t, _) :: r => by
    simp only [loadBytes]
    rw [loadBytes_vwNew vpre _ (a + 1) r]
    rfl

/-- **THE (1b) RELEASE IS ALWAYS IN PLACE**: a non-aq AMO whose state has `vrOld ⊔ vwOld ≤ vwNew` (directly after
`fence rw,w`) is `relClassPre` (its pre-view contains `vwNew`, which a non-aq read half leaves alone). -/
theorem relClassPre_fW_amo (ws : PState) (rl : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (d : List (BitVec 8))
    (asrc vsrc : List Dsrc) (h : max ws.wVrOld ws.wVwOld ≤ ws.wVwNew) :
    Nfr.Pre.relClassPre ws (LRmw false rl base tvs d asrc vsrc) := by
  refine ⟨_, rfl, ?_⟩
  have e : (loadRun ws false false (srcsView ws asrc) base tvs).wVwNew = ws.wVwNew :=
    loadBytes_vwNew _ ws base tvs
  simp only [stPre]
  rw [e]
  omega

/-- After `fence rw,w`: `vrOld ⊔ vwOld ≤ vwNew`. -/
theorem fRWW_post (ws : PState) :
    max (instrR (fencePost ws true true false true)).wVrOld (instrR (fencePost ws true true false true)).wVwOld ≤
      (instrR (fencePost ws true true false true)).wVwNew := by
  simp only [instrR, fencePost, if_true, if_false]
  omega

/-- After `fence r,rw`: both new-floors are at least `vrOld`. -/
theorem fRRW_floor (ws : PState) :
    ws.wVrOld ≤ (instrR (fencePost ws true false true true)).wVrNew ∧
      ws.wVrOld ≤ (instrR (fencePost ws true false true true)).wVwNew := by
  simp only [instrR, fencePost, if_true, if_false]
  omega

/-- PO-FETCH for every litmus test, for the pre-state release class. -/
theorem lit_fetchBoundedPre {img : Image} {ps : List LP} {evs : List PEvt} {cfg : PCfg LP Unit}
    (hv : validRun litStep img () ps evs cfg) (hps : ∀ p ∈ ps, p.q = []) :
    Nfr.Pre.fetchBounded litStep img ps cfg.pcLog evs := by
  apply Nfr.Pre.fetchBounded_ofImg
  intro hh e he base tvs hl
  rcases Nat.lt_or_ge hh ps.length with hlt | hge
  · obtain ⟨ag, _, P0, _, hs⟩ := validRun_solo hv hh _ (List.getElem?_eq_getElem hlt)
    have hq : qOk ps[hh].q := by rw [hps _ (List.getElem_mem hlt)]; exact qOk_nil
    exact absurd hl ((Own.solo_nf hs hq e he).1 base tvs)
  · rw [PF.validRun_traceNone hv (List.getElem?_eq_none hge)] at he
    cases he

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF MG]

/-- Before `fence r,rw` (after the acquire AMO): as `KB`, with the AMO's `ts ≤ vrOld` (M0 (iv)). -/
def KB0 (γc γm : GName) (k ts : Nat) (ws : PState) : IProp GF :=
  iprop(Rg γm ∨ ∃ cr, hv γm (.pr 1 none none) ∗ hv γc (.xr cr) ∗
    ⌜cr.hold = some k ∧ cr.tstar < ts ∧ cr.tstart ≤ ts ∧ ts ≤ ws.wVrOld⌝)

/-! ## 2. The generic hart -/

section hart

variable [InvGS_gen hlc GF] (M : List PMsg) (γc γm γo : GName) (k ko : Nat) (X : OSt (List Nat) → IProp GF)

/-- The hart's knowledge at its end: it did not acquire, or it is a rogue, or its read is recorded (or marked). -/
def KG (x5 x7 : Nat) : IProp GF :=
  iprop(⌜x5 ≠ 0⌝ ∨ (∃ rd mk, hv γm (.pr 3 rd mk)) ∨
    (∃ rd mk, hv γm (.pr 2 rd mk) ∗ ⌜mk ≠ none ∨ ∃ v, rd = some v ∧ x7 = (v + 1) % two64⌝))

theorem hG (hX : ∀ σ, (X σ ⊢ Xf M γc γm γo k ko σ) ∧ (Xf M γc γm γo k ko σ ⊢ X σ)) (s : LP) (ws : PState)
    (hP : s.prog.length ≤ s.pc) (hq : s.q = []) :
    KG γm (s.rd 5) (s.rd 7) ⊢ wpT (hlc := hlc) X lkImg M k s ws (fun _ => iprop(True)) := by
  iintro H
  iapply (wpT_end hq hP)
  iintro %σ %_ HX
  ihave HX := (hX σ).1 $$ HX
  icases HX with ⟨%g, Hc, Hm, Ho, %hok, Hb⟩
  have hsp : ∀ (hk : specH s.regs g k), hv γc (.xr g.cr) ∗ hv γm (Pg g k) ∗ hv γo (Pg g ko) ∗
      Rbox γc g.spoil g.ls g.cr ⊢ |={⊤}=> X { σ with done := upd σ.done k (some s.regs) } ∗ iprop(True) := by
    intro hk
    iintro ⟨Hc, Hm, Ho, Hb⟩
    imodintro
    isplitl
    · iapply (hX _).2
      iexists g
      iframe
      ipureintro; exact lk_fin hok hk
    · ipureintro; trivial
  unfold KG
  icases H with (%h5 | ⟨%rd, %mk, Hmy⟩ | ⟨%rd, %mk, Hmy, %hrd⟩)
  · iapply (hsp (.inl (by rw [rd_regs s 5 (by omega)]; exact h5)))
    iframe
  · unfold hv
    ihave %e := ghost_var_agree γm _ _ _ _ $$ Hmy Hm
    obtain ⟨e1, _, _⟩ := pr_inj e
    have hb := (hok.spoil (hok.ph3 k e1.symm)).1
    iapply (hsp (.inr (.inl hb)))
    unfold hv; iframe
  · unfold hv
    ihave %e := ghost_var_agree γm _ _ _ _ $$ Hmy Hm
    obtain ⟨_, e2, e3⟩ := pr_inj e
    have hk : specH s.regs g k := by
      rcases hrd with hm | ⟨v, hv1, hv2⟩
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 hm
        exact .inr (.inl (hok.mk_bad k t (by rw [← e3, ht])))
      · exact .inr (.inr ⟨v, by rw [← e2, hv1], by rw [rd_regs s 7 (by omega)]; exact hv2⟩)
    iapply (hsp hk)
    unfold hv; iframe

end hart

section hart2

variable [InvGS_gen hlc GF] (M : List PMsg) (γc γm γo : GName) (k ko : Nat) (X : OSt (List Nat) → IProp GF)

/-- **THE RELEASE** `amoswap.w x0,x0,(x10)` directly after `fence rw,w` (always `relClassPre`: in place): THE
DEPOSIT. -/
theorem hF (hX : ∀ σ, (X σ ⊢ Xf M γc γm γo k ko σ) ∧ (Xf M γc γm γo k ko σ ⊢ X σ)) (hko : ko ≠ k)
    (s : LP) (ws : PState) (hprog : s.prog = lk1bProg) (hpc : s.pc = 7) (hq : s.q = [])
    (h10 : s.rd 10 = Weak.Prom.Ref.Lit.Y) (hfw : max ws.wVrOld ws.wVwOld ≤ ws.wVwNew) :
    KF (GF := GF) γc γm k (s.rd 7) ⊢ wpT (hlc := hlc) X lkImg M k s ws (fun _ => iprop(True)) := by
  iintro H
  iapply (wpT_amo (op := .swap) (sz := 4) (aq := false) (rl := false) (rd := 0) (rs2 := 0) (rs1 := 10) hq
    (by rw [hprog, hpc]; rfl) (by rw [h10]; decide))
  inext
  iintro %σ %tvs %ts %σ' %hl4 %hful %hrmw HX _
  have hrc := relClassPre_fW_amo ws false ((s.rd 10 : Nat) : Int) tvs (amoD .swap 4 (s.rd 0) tvs) (srcR 10) (srcR 0)
    hfw
  have hM : M[ts - 1]? = some (relMsg k) := by
    have := (take_msg hrmw.2.1).1
    have hb : ((s.rd 10 : Nat) : Int) = Lw := by rw [h10]; rfl
    have hd : amoD .swap 4 (s.rd 0) tvs = toBytes 0 4 := by rw [PF.amoD_swap]; simp [LP.rd]
    rw [hb, hd] at this; exact this
  ihave HX := (hX σ).1 $$ HX
  icases HX with ⟨%g, Hc, Hm, Ho, %hok, Hb⟩
  have cont : ∀ s', LPstep s s' (s.pc + 1) 0 (Weak.Prom.Ref.sext 4 (ofBytes (tvs.map Prod.snd))) →
      KG (GF := GF) γm (s'.rd 5) (s'.rd 7) ⊢ wpT (hlc := hlc) X lkImg M k s' (PF.qPosts (amoPost (storeRun
        (loadRun ws false false (srcsView ws (srcR 10)) ((s.rd 10 : Nat) : Int) tvs) false (srcsView ws (srcR 10)) ts
        ((s.rd 10 : Nat) : Int) (amoD .swap 4 (s.rd 0) tvs).length ts) false ts) (regWL 0 [.DLdRes] ++ [LInstr]))
        (fun _ => iprop(True)) := by
    intro s' hs'
    obtain ⟨hP', hc', hq'⟩ := LPstep_at hs' hprog (by rw [hpc])
    exact hG M γc γm γo k ko X hX s' _ (by rw [hP', hc']; exact Nat.le_refl _) hq'
  unfold KF Rg
  icases H with (⟨%rd, %mk, Hmy⟩ | ⟨%cr, %rd, %mk, Hmy, Hcr, %hcr⟩)
  · -- a rogue: spoiled mode
    unfold hv
    ihave %e := ghost_var_agree γm _ _ _ _ $$ Hmy Hm
    obtain ⟨e1, _, _⟩ := pr_inj e
    have hsp := hok.ph3 k e1.symm
    imodintro
    isplitl [Hc Hm Ho Hb]
    · iapply (hX σ').2
      iexists g; unfold hv; iframe; ipureintro; exact lk_relS hok hsp hrc hful
    iintro %s' %hs'
    iapply (cont s' hs')
    unfold KG hv
    iright; ileft; iexists rd, mk; iexact Hmy
  · unfold hv
    ihave %e := ghost_var_agree γm _ _ _ _ $$ Hmy Hm
    obtain ⟨e1, e2, e3⟩ := pr_inj e
    ihave %ec := ghost_var_agree γc _ _ _ _ $$ Hcr Hc
    obtain rfl := xr_inj ec
    by_cases hsp : g.spoil = true
    · -- spoiled: turn rogue
      have hok1 := lk_toRogue (h := k) (lk_relS hok hsp hrc hful) hsp
      imod ghost_var_update_halves (MG.pr 3 rd mk) γm _ _ $$ Hmy Hm with ⟨Hmy, Hm⟩
      imodintro
      isplitl [Hc Hm Ho Hb]
      · iapply (hX σ').2
        iexists { g with ph := upd g.ph k 3 }
        have e4 : Pg { g with ph := upd g.ph k 3 } k = MG.pr 3 rd mk := by simp [Pg, upd, e2, e3]
        have e5 : Pg { g with ph := upd g.ph k 3 } ko = Pg g ko :=
          Pg_other hko (upd_other _ _ _) (fun _ _ => rfl) (fun _ _ => rfl)
        rw [e4, e5]
        unfold hv
        iframe; ipureintro; exact hok1
      iintro %s' %hs'
      iapply (cont s' hs')
      unfold KG hv
      iright; ileft; iexists rd, mk; iexact Hmy
    · have hsp' : g.spoil = false := by simpa using hsp
      obtain ⟨u, hown⟩ := owned_of_ph1 (hok.lock hsp') e1.symm
      have hok' := lk_rel hok hsp' hown hrc hful hM
      imod ghost_var_update_halves (MG.xr { g.cr with hold := none, tstart := ts }) γc _ _ $$ Hcr Hc with ⟨Hcr, Hc⟩
      imod ghost_var_update_halves (MG.pr 2 rd mk) γm _ _ $$ Hmy Hm with ⟨Hmy, Hm⟩
      imodintro
      isplitl [Hc Hm Ho Hcr]
      · iapply (hX σ').2
        iexists relG g k ts
        have e4 : Pg (relG g k ts) k = MG.pr 2 rd mk := by simp [Pg, relG, upd, e2, e3]
        have e5 : Pg (relG g k ts) ko = Pg g ko :=
          Pg_other hko (upd_other _ _ _) (fun _ _ => rfl) (fun _ _ => rfl)
        have e6 : Rbox (GF := GF) γc (relG g k ts).spoil (relG g k ts).ls (relG g k ts).cr =
            hv γc (.xr { g.cr with hold := none, tstart := ts }) := by simp [relG, hsp', Rbox]
        have e7 : (relG g k ts).cr = { g.cr with hold := none, tstart := ts } := rfl
        rw [e4, e5, e6, e7]
        unfold hv
        iframe; ipureintro; exact hok'
      iintro %s' %hs'
      iapply (cont s' hs')
      unfold KG hv
      iright; iright; iexists rd, mk; iframe Hmy
      ipureintro
      rw [LPstep_rd hs' 7 (.inr rfl)]; exact hcr.2

/-- `fence rw,w`: it raises `vwNew` to `vrOld ⊔ vwOld`, so the release AMO after it is in place. -/
theorem hF0 (hX : ∀ σ, (X σ ⊢ Xf M γc γm γo k ko σ) ∧ (Xf M γc γm γo k ko σ ⊢ X σ)) (hko : ko ≠ k)
    (s : LP) (ws : PState) (hprog : s.prog = lk1bProg) (hpc : s.pc = 6) (hq : s.q = [])
    (h10 : s.rd 10 = Weak.Prom.Ref.Lit.Y) :
    KF (GF := GF) γc γm k (s.rd 7) ⊢ wpT (hlc := hlc) X lkImg M k s ws (fun _ => iprop(True)) := by
  iintro H
  iapply (wpT_fence (f := ⟨true, true, false, false, false, true, false, false⟩) hq (by rw [hprog, hpc]; rfl))
  iintro %s' %hs'
  obtain ⟨hP', hc', hq'⟩ := LPstep_at hs' hprog (by rw [hpc])
  rw [show s.rd 7 = s'.rd 7 from (LPstep_rd hs' 7 (.inr rfl)).symm]
  iapply (hF M γc γm γo k ko X hX hko s' _ hP' hc' hq' (by rw [LPstep_rd hs' 10 (.inr rfl), h10]) (fRWW_post ws))
  iexact H

/-- **THE COUNTER STORE** `sd x7,(x11)`: the holder's message becomes the counter's latest (`lk_sdc`). -/
theorem hE (hX : ∀ σ, (X σ ⊢ Xf M γc γm γo k ko σ) ∧ (Xf M γc γm γo k ko σ ⊢ X σ)) (hko : ko ≠ k) (hk2 : k < 2)
    (s : LP) (ws : PState) (ts : Nat) (hprog : s.prog = lk1bProg) (hpc : s.pc = 5) (hq : s.q = [])
    (h10 : s.rd 10 = Weak.Prom.Ref.Lit.Y) (h11 : s.rd 11 = Weak.Prom.Ref.Lit.X) :
    KE (GF := GF) γc γm k (s.rd 7) ts ws ⊢ wpT (hlc := hlc) X lkImg M k s ws (fun _ => iprop(True)) := by
  iintro H
  iapply (wpT_sd (sz := 8) (rs2 := 7) (rs1 := 11) (off := 0) hq (by rw [hprog, hpc]; rfl) (by rw [h11]; decide))
  inext
  iintro %σ %ts' %σ' %hful %hmsg %hcoh %hext HX _
  have hb : (((s.rd 11 + 0) % two64 : Nat) : Int) = C := by rw [h11]; decide
  have hM : M[ts' - 1]? = some (cMsg k (s.rd 7)) := by
    have := (take_msg hmsg).1; rw [hb] at this; exact this
  have hvw : ws.wVwNew < ts' := by
    have := (PF.stPreA_ge ws false false (srcsView ws (srcR 11)) (srcsView ws (srcR 7))).2.2.2.1; omega
  have hcj : ∀ j : Nat, j < 8 → coh ws (C + j) < ts' := by
    rw [hb] at hcoh
    intro j hj; exact cohBelow_get hcoh j (by simp [toBytes, Weak.Prom.Ref.byteList]; omega)
  have cont : ∀ s', LPstep s s' (s.pc + 1) 0 0 → KF (GF := GF) γc γm k (s'.rd 7) ⊢
      wpT (hlc := hlc) X lkImg M k s' (instrR (storeRun ws false (srcsView ws (srcR 11))
        (max (srcsView ws (srcR 11)) (srcsView ws (srcR 7))) (((s.rd 11 + 0) % two64 : Nat) : Int)
        (toBytes (s.rd 7) 8).length ts')) (fun _ => iprop(True)) := by
    intro s' hs'
    obtain ⟨hP', hc', hq'⟩ := LPstep_at hs' hprog (by rw [hpc])
    exact hF0 M γc γm γo k ko X hX hko s' _ hP' hc' hq' (by rw [LPstep_rd hs' 10 (.inr rfl), h10])
  ihave HX := (hX σ).1 $$ HX
  icases HX with ⟨%g, Hc, Hm, Ho, %hok, Hb⟩
  unfold KE Rg
  icases H with (⟨%rd, %mk, Hmy⟩ | ⟨%cr, %mk, Hmy, Hcr, %hcr⟩)
  · unfold hv
    ihave %e := ghost_var_agree γm _ _ _ _ $$ Hmy Hm
    obtain ⟨e1, _, _⟩ := pr_inj e
    have hsp := hok.ph3 k e1.symm
    imodintro
    isplitl [Hc Hm Ho Hb]
    · iapply (hX σ').2
      iexists g; unfold hv; iframe; ipureintro; exact lk_sdcS hok hsp hful hM
    iintro %s' %hs'
    iapply (cont s' hs')
    unfold KF Rg hv
    ileft; iexists rd, mk; iexact Hmy
  · unfold hv
    ihave %e := ghost_var_agree γm _ _ _ _ $$ Hmy Hm
    obtain ⟨e1, e2, e3⟩ := pr_inj e
    ihave %ec := ghost_var_agree γc _ _ _ _ $$ Hcr Hc
    obtain rfl := xr_inj ec
    obtain ⟨hh, htst0, htsr, hvw0, hmk1, hmk2⟩ := hcr
    by_cases hsp : g.spoil = true
    · have hok1 := lk_toRogue (h := k) (lk_sdcS hok hsp hful hM) hsp
      imod ghost_var_update_halves (MG.pr 3 none mk) γm _ _ $$ Hmy Hm with ⟨Hmy, Hm⟩
      imodintro
      isplitl [Hc Hm Ho Hb]
      · iapply (hX σ').2
        iexists { g with ph := upd g.ph k 3 }
        have e4 : Pg { g with ph := upd g.ph k 3 } k = MG.pr 3 none mk := by simp [Pg, upd, e2, e3]
        have e5 : Pg { g with ph := upd g.ph k 3 } ko = Pg g ko :=
          Pg_other hko (upd_other _ _ _) (fun _ _ => rfl) (fun _ _ => rfl)
        rw [e4, e5]
        unfold hv
        iframe; ipureintro; exact hok1
      iintro %s' %hs'
      iapply (cont s' hs')
      unfold KF Rg hv
      ileft; iexists none, mk; iexact Hmy
    · have hsp' : g.spoil = false := by simpa using hsp
      have hL := hok.lock hsp'
      obtain ⟨u, hown⟩ := owned_of_ph1 hL e1.symm
      have hu : g.cr.tstart = u := by have hls := hL.ls_ok; rw [hown] at hls; exact hls.1.2.2.2.2.2
      have hmk : ∀ m, g.mark k = some m → m < ts' := by
        intro m hm; rw [← e3] at hm; obtain ⟨j, hj, hle⟩ := hmk2 m hm; have := hcj j hj; omega
      have hrd : g.bad = false → s.rd 7 = (g.cr.v % two64 + 1) % two64 ∧ g.rds k = none := by
        intro hbf
        cases hmkc : mk with
        | none =>
          obtain ⟨hv1, hv2⟩ := hmk1 hmkc
          refine ⟨by rw [hv1]; simp only [two64]; omega, e2.symm⟩
        | some m =>
          have := hok.mk_bad k m (by rw [← e3, hmkc]); rw [hbf] at this; cases this
      obtain ⟨g', hok', hsp'', hls', hph', hmk', hcr', hbad', hrds1, hrds2⟩ :=
        lk_sdc hok hk2 hsp' hown hful hM (by rw [← hu]; omega) (by omega) hmk hrd
      have eR : Rbox (GF := GF) γc g'.spoil g'.ls g'.cr = iprop(True) := by rw [hsp'', hls', hown]; rfl
      imod ghost_var_update_halves (MG.xr g'.cr) γc _ _ $$ Hcr Hc with ⟨Hcr, Hc⟩
      have hh' : g'.cr.hold = some k := by rw [hcr']; exact hh
      by_cases hbt : g.bad = true
      · have hrk : g'.rds k = none := by rw [hrds2 hbt, ← e2]
        cases hmkc : mk with
        | none =>
          -- a `bad` the hart did not cause: record a witness mark
          have hok'' := lk_markBad (h := k) (m := 0) hok' (by rw [hbad']; exact hbt)
            (by rw [hmk', ← e3, hmkc])
          imod ghost_var_update_halves (MG.pr 1 none (some 0)) γm _ _ $$ Hmy Hm with ⟨Hmy, Hm⟩
          imodintro
          isplitl [Hc Hm Ho]
          · iapply (hX σ').2
            iexists { g' with mark := upd g'.mark k (some 0) }
            have e4 : Pg { g' with mark := upd g'.mark k (some 0) } k = MG.pr 1 none (some 0) := by
              simp [Pg, upd, hph', hrk, e1]
            have e5 : Pg { g' with mark := upd g'.mark k (some 0) } ko = Pg g ko :=
              Pg_other hko (fun a _ => by simp [hph']) (fun a ha => by
                show g'.rds a = g.rds a; rw [hrds2 hbt]) (fun a ha => by
                show upd g'.mark k (some 0) a = g.mark a; rw [upd_ne _ _ ha, hmk'])
            have eR' : Rbox (GF := GF) γc ({ g' with mark := upd g'.mark k (some 0) } : LkS).spoil
                ({ g' with mark := upd g'.mark k (some 0) } : LkS).ls ({ g' with mark := upd g'.mark k (some 0) } : LkS).cr
                = iprop(True) := eR
            rw [eR', e4, e5]
            unfold hv
            iframe; ipureintro; exact ⟨hok'', trivial⟩
          iintro %s' %hs'
          iapply (cont s' hs')
          unfold KF Rg hv
          iright; iexists g'.cr, none, some 0; iframe Hmy Hcr
          ipureintro; exact ⟨hh', .inl (by simp)⟩
        | some m =>
          imodintro
          isplitl [Hc Hm Ho]
          · iapply (hX σ').2
            iexists g'
            have e4 : Pg g' k = Pg g k := by simp [Pg, hph', hrds2 hbt, hmk']
            have e5 : Pg g' ko = Pg g ko :=
              Pg_other hko (fun a _ => by rw [hph']) (fun a _ => by rw [hrds2 hbt]) (fun a _ => by rw [hmk'])
            rw [eR, e4, e5]
            unfold hv
            iframe; ipureintro; exact ⟨hok', trivial⟩
          iintro %s' %hs'
          iapply (cont s' hs')
          unfold KF Rg hv
          iright; iexists g'.cr, none, some m; iframe Hmy Hcr
          ipureintro; exact ⟨hh', .inl (by simp)⟩
      · have hbf : g.bad = false := by simpa using hbt
        have hmkn : mk = none := by
          cases hmkc : mk with
          | none => rfl
          | some m => have := hok.mk_bad k m (by rw [← e3, hmkc]); rw [hbf] at this; cases this
        subst hmkn
        obtain ⟨hv1, _⟩ := hmk1 rfl
        have hrk : g'.rds k = some g.cr.v := by rw [hrds1 hbf]; simp [upd]
        imod ghost_var_update_halves (MG.pr 1 (some g.cr.v) none) γm _ _ $$ Hmy Hm with ⟨Hmy, Hm⟩
        imodintro
        isplitl [Hc Hm Ho]
        · iapply (hX σ').2
          iexists g'
          have e4 : Pg g' k = MG.pr 1 (some g.cr.v) none := by simp [Pg, hph', hrk, hmk', ← e1, ← e3]
          have e5 : Pg g' ko = Pg g ko :=
            Pg_other hko (fun a _ => by rw [hph']) (fun a ha => by rw [hrds1 hbf]; exact upd_ne _ _ ha)
              (fun a _ => by rw [hmk'])
          rw [eR, e4, e5]
          unfold hv
          iframe; ipureintro; exact ⟨hok', trivial⟩
        iintro %s' %hs'
        iapply (cont s' hs')
        unfold KF Rg hv
        iright; iexists g'.cr, some g.cr.v, none; iframe Hmy Hcr
        ipureintro
        refine ⟨hh', .inr ⟨g.cr.v, rfl, ?_⟩⟩
        rw [LPstep_rd hs' 7 (.inr rfl)]; exact hv1

/-- `addi x7,x7,1`. -/
theorem hD (hX : ∀ σ, (X σ ⊢ Xf M γc γm γo k ko σ) ∧ (Xf M γc γm γo k ko σ ⊢ X σ)) (hko : ko ≠ k) (hk2 : k < 2)
    (s : LP) (ws : PState) (ts : Nat) (hprog : s.prog = lk1bProg) (hpc : s.pc = 4) (hq : s.q = [])
    (h10 : s.rd 10 = Weak.Prom.Ref.Lit.Y) (h11 : s.rd 11 = Weak.Prom.Ref.Lit.X) (hlen : s.regs.length = 32) :
    KC (GF := GF) γc γm k (s.rd 7) ts ws ⊢ wpT (hlc := hlc) X lkImg M k s ws (fun _ => iprop(True)) := by
  iintro H
  iapply (wpT_alui (op := .add) (rd := 7) (rs1 := 7) (imm := 1) hq (by rw [hprog, hpc]; rfl) (by decide))
  iintro %s' %hs'
  obtain ⟨hP', hc', hq'⟩ := LPstep_at hs' hprog (by rw [hpc])
  have e7 : s'.rd 7 = (s.rd 7 + 1) % two64 := by
    rw [LPstep_rd_eq hs' (by decide) (by omega)]; simp [Weak.Prom.Ref.aluOp]
  iapply (hE M γc γm γo k ko X hX hko hk2 s' _ ts hP' hc' hq' (by rw [LPstep_rd hs' 10 (.inl (by decide)), h10])
    (by rw [LPstep_rd hs' 11 (.inl (by decide)), h11]))
  unfold KC KE
  icases H with (Hr | ⟨%cr, %mk, Hmy, Hcr, %hc⟩)
  · ileft; iexact Hr
  · iright; iexists cr, mk; iframe; ipureintro
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hc
    exact ⟨a1, a2, a3, a4, fun hm => ⟨by rw [e7, (a5 hm).1], (a5 hm).2⟩, a6⟩

/-- **THE OWNED READ** `ld x7,(x11)` (`lk_ldc`). -/
theorem hC (hinv : invalFree M) (hX : ∀ σ, (X σ ⊢ Xf M γc γm γo k ko σ) ∧ (Xf M γc γm γo k ko σ ⊢ X σ))
    (hko : ko ≠ k) (hk2 : k < 2) (s : LP) (ws : PState) (ts : Nat) (hprog : s.prog = lk1bProg) (hpc : s.pc = 3)
    (hq : s.q = []) (h10 : s.rd 10 = Weak.Prom.Ref.Lit.Y) (h11 : s.rd 11 = Weak.Prom.Ref.Lit.X)
    (hlen : s.regs.length = 32) :
    KB (GF := GF) γc γm k ts ws ⊢ wpT (hlc := hlc) X lkImg M k s ws (fun _ => iprop(True)) := by
  iintro H
  iapply (wpT_ld (sz := 8) (sgn := true) (rd := 7) (rs1 := 11) (off := 0) hq (by rw [hprog, hpc]; rfl)
    (by rw [h11]; decide))
  inext
  iintro %σ %tvs %hl8 %hlo HX _
  have hb : (((s.rd 11 + 0) % two64 : Nat) : Int) = C := by rw [h11]; decide
  rw [hb] at hlo ⊢
  have hP : ws.wVrNew ≤ ldPre ws false false (srcsView ws (srcR 11)) := (PF.ldPre_ge ws false false _).2.1
  have hw3 : (PF.qPosts (loadRun ws false false (srcsView ws (srcR 11)) C tvs) (regWL 7 [.DLdRes] ++ [LInstr])).wVwNew =
      ws.wVwNew := by
    simp [PF.qPosts, PF.qPost, regWL, PF.regWP, instrR, ((PF.loadRun_mono ws false false (srcsView ws (srcR 11)) C tvs).2.2.2.2.2.2.2.2.2.2.2 rfl).2]
  have hc3 : ∀ x, coh (PF.qPosts (loadRun ws false false (srcsView ws (srcR 11)) C tvs) (regWL 7 [.DLdRes] ++ [LInstr])) x =
      coh (loadRun ws false false (srcsView ws (srcR 11)) C tvs) x := fun x => rfl
  have cont : ∀ s3, LPstep s s3 (s.pc + 1) 7 (ldVal true 8 tvs) →
      KC (GF := GF) γc γm k (val8 tvs) ts
        (PF.qPosts (loadRun ws false false (srcsView ws (srcR 11)) C tvs) (regWL 7 [.DLdRes] ++ [LInstr])) ⊢
      wpT (hlc := hlc) X lkImg M k s3
        (PF.qPosts (loadRun ws false false (srcsView ws (srcR 11)) C tvs) (regWL 7 [.DLdRes] ++ [LInstr]))
        (fun _ => iprop(True)) := by
    intro s3 hs3
    obtain ⟨hP3, hc3', hq3⟩ := LPstep_at hs3 hprog (by rw [hpc])
    have e7 : s3.rd 7 = val8 tvs := LPstep_rd_eq hs3 (by decide) (by omega)
    rw [← e7]
    exact hD M γc γm γo k ko X hX hko hk2 s3 _ ts hP3 hc3' hq3 (by rw [LPstep_rd hs3 10 (.inl (by decide)), h10])
      (by rw [LPstep_rd hs3 11 (.inl (by decide)), h11]) (by rw [hs3.2.2.2.1, hlen])
  unfold KB Rg
  icases H with (⟨%rd, %mk, Hmy⟩ | ⟨%cr, Hmy, Hcr, %hcr⟩)
  · imodintro
    iframe HX
    iintro %s3 %hs3
    iapply (cont s3 hs3)
    unfold KC Rg
    ileft; iexists rd, mk; iexact Hmy
  · ihave HX := (hX σ).1 $$ HX
    icases HX with ⟨%g, Hc, Hm, Ho, %hok, Hb⟩
    unfold hv
    ihave %e := ghost_var_agree γm _ _ _ _ $$ Hmy Hm
    obtain ⟨e1, e2, e3⟩ := pr_inj e
    ihave %ec := ghost_var_agree γc _ _ _ _ $$ Hcr Hc
    obtain rfl := xr_inj ec
    obtain ⟨hh, htst, htsr, hvr, hvw⟩ := hcr
    by_cases hsp : g.spoil = true
    · have hok1 := lk_toRogue (h := k) hok hsp
      imod ghost_var_update_halves (MG.pr 3 none none) γm _ _ $$ Hmy Hm with ⟨Hmy, Hm⟩
      imodintro
      isplitl [Hc Hm Ho Hb]
      · iapply (hX σ).2
        iexists { g with ph := upd g.ph k 3 }
        have e4 : Pg { g with ph := upd g.ph k 3 } k = MG.pr 3 none none := by simp [Pg, upd, ← e2, ← e3]
        have e5 : Pg { g with ph := upd g.ph k 3 } ko = Pg g ko :=
          Pg_other hko (upd_other _ _ _) (fun _ _ => rfl) (fun _ _ => rfl)
        rw [e4, e5]
        unfold hv
        iframe; ipureintro; exact hok1
      iintro %s3 %hs3
      iapply (cont s3 hs3)
      unfold KC Rg hv
      ileft; iexists none, none; iexact Hmy
    · have hsp' : g.spoil = false := by simpa using hsp
      obtain ⟨u, hown⟩ := owned_of_ph1 (hok.lock hsp') e1.symm
      have hby : ∀ (j : Nat) t b, tvs[j]? = some (t, b) → memByte lkImg M t (C + j) = some b ∧ t ≤ σ.n ∧
          ¬ writesIn (M.take σ.n) (C + j) t (ldPre ws false false (srcsView ws (srcR 11))) :=
        fun j t b h => loadOk_byte hinv hlo h
      rcases lk_ldc hok hsp' hown e3.symm (by omega) hl8 hby with hgood |
          ⟨j, t, b, hj, htb, g', hok', hbad', hsp'', hls', hcr', hph', hrds', hmk'⟩
      · by_cases hbt : g.bad = true
        · have hok1 := lk_markBad (h := k) (m := 0) hok hbt e3.symm
          imod ghost_var_update_halves (MG.pr 1 none (some 0)) γm _ _ $$ Hmy Hm with ⟨Hmy, Hm⟩
          imodintro
          isplitl [Hc Hm Ho Hb]
          · iapply (hX σ).2
            iexists { g with mark := upd g.mark k (some 0) }
            have e4 : Pg { g with mark := upd g.mark k (some 0) } k = MG.pr 1 none (some 0) := by
              simp [Pg, upd, ← e1, ← e2]
            have e5 : Pg { g with mark := upd g.mark k (some 0) } ko = Pg g ko :=
              Pg_other hko (fun _ _ => rfl) (fun _ _ => rfl) (upd_other _ _ _)
            rw [e4, e5]
            unfold hv
            iframe; ipureintro; exact hok1
          iintro %s3 %hs3
          iapply (cont s3 hs3)
          unfold KC Rg hv
          iright; iexists g.cr, some 0; iframe Hmy Hcr
          ipureintro
          refine ⟨hh, htsr, htst, by rw [hw3]; exact hvw, fun e => (by cases e), fun m hm => ⟨0, by omega, ?_⟩⟩
          cases hm; exact Nat.zero_le _
        · have hbf : g.bad = false := by simpa using hbt
          have hcnt := hok.cnt hbf
          have hc2 : g.cnt ≤ 2 := by have := hcnt.cnt_def; split at this <;> split at this <;> omega
          have hv8 : val8 tvs = g.cr.v := val8_small hgood (by rw [hcnt.v_cnt]; exact hc2)
          imodintro
          isplitl [Hc Hm Ho Hb]
          · iapply (hX σ).2
            iexists g; unfold hv; iframe; ipureintro; exact hok
          iintro %s3 %hs3
          iapply (cont s3 hs3)
          unfold KC Rg hv
          iright; iexists g.cr, none; iframe Hmy Hcr
          ipureintro
          exact ⟨hh, htsr, htst, by rw [hw3]; exact hvw, fun _ => ⟨hv8, by rw [hcnt.v_cnt]; exact hc2⟩,
            fun m hm => by cases hm⟩
      · imod ghost_var_update_halves (MG.pr 1 none (some t)) γm _ _ $$ Hmy Hm with ⟨Hmy, Hm⟩
        imodintro
        isplitl [Hc Hm Ho Hb]
        · iapply (hX σ).2
          iexists g'
          have e4 : Pg g' k = MG.pr 1 none (some t) := by simp [Pg, hph', hrds', hmk', upd, ← e1, ← e2]
          have e5 : Pg g' ko = Pg g ko :=
            Pg_other hko (fun a _ => by rw [hph']) (fun a _ => by rw [hrds']) (fun a ha => by rw [hmk']; exact upd_ne _ _ ha)
          have eR : Rbox (GF := GF) γc g'.spoil g'.ls g'.cr = Rbox γc g.spoil g.ls g.cr := by rw [hsp'', hls', hcr', hsp']
          rw [e4, e5, eR, hcr']
          unfold hv
          iframe; ipureintro; exact hok'
        iintro %s3 %hs3
        iapply (cont s3 hs3)
        unfold KC Rg hv
        iright; iexists g.cr, some t; iframe Hmy Hcr
        ipureintro
        refine ⟨hh, htsr, htst, by rw [hw3]; exact hvw, fun e => (by cases e), fun m hm => ⟨j, hj, ?_⟩⟩
        cases hm; rw [hc3]; exact loadRun_coh_j htb

/-- `bne x5,x0,END`. -/
theorem hB (hinv : invalFree M) (hX : ∀ σ, (X σ ⊢ Xf M γc γm γo k ko σ) ∧ (Xf M γc γm γo k ko σ ⊢ X σ))
    (hko : ko ≠ k) (hk2 : k < 2) (s : LP) (ws : PState) (ts : Nat) (hprog : s.prog = lk1bProg) (hpc : s.pc = 2)
    (hq : s.q = []) (h10 : s.rd 10 = Weak.Prom.Ref.Lit.Y) (h11 : s.rd 11 = Weak.Prom.Ref.Lit.X)
    (hlen : s.regs.length = 32) :
    (⌜s.rd 5 ≠ 0⌝ ∨ KB (GF := GF) γc γm k ts ws) ⊢ wpT (hlc := hlc) X lkImg M k s ws (fun _ => iprop(True)) := by
  iintro H
  iapply (wpT_br (c := .ne) (rs1 := 5) (rs2 := 0) (tgt := 8) hq (by rw [hprog, hpc]; rfl)
    (by rw [hpc, hprog]; decide))
  iintro %s2 %hs2
  have hpc2 := hs2.2.1
  have e5 : s2.rd 5 = s.rd 5 := LPstep_rd hs2 5 (.inr rfl)
  by_cases hx : s.rd 5 = 0
  · have hbr : Weak.Prom.Ref.brEval .ne (s.rd 5) (s.rd 0) = false := by rw [hx]; rfl
    have hp2 : s2.pc = 3 := by rw [hpc2, hbr, hpc]; rfl
    obtain ⟨hP2, _, hq2⟩ := LPstep_at hs2 hprog rfl
    iapply (hC M γc γm γo k ko X hinv hX hko hk2 s2 _ ts hP2 hp2 hq2 (by rw [LPstep_rd hs2 10 (.inr rfl), h10])
      (by rw [LPstep_rd hs2 11 (.inr rfl), h11]) (by rw [hs2.2.2.2.1, hlen]))
    icases H with (%h | HK)
    · exact absurd hx h
    · iapply (KB_congr (ws := ws) (ws' := instrR (PF.ctrlP ws (srcR 5 ++ srcR 0))) rfl rfl)
      iexact HK
  · have h0 : s.rd 0 = 0 := rfl
    have hbr : Weak.Prom.Ref.brEval .ne (s.rd 5) (s.rd 0) = true := by simp [Weak.Prom.Ref.brEval, h0, hx]
    have hp2 : s2.pc = 8 := by rw [hpc2, hbr]; rfl
    obtain ⟨hP2, _, hq2⟩ := LPstep_at hs2 hprog rfl
    iapply (hG M γc γm γo k ko X hX s2 _ (by rw [hP2, hp2]; exact Nat.le_refl _) hq2)
    unfold KG
    ileft; ipureintro; rw [e5]; exact hx

/-- `fence r,rw`: it raises both new-floors to `vrOld ≥ ts` (the acquire AMO's M0 (iv)): `KB0` becomes `KB`. -/
theorem hA1 (hinv : invalFree M) (hX : ∀ σ, (X σ ⊢ Xf M γc γm γo k ko σ) ∧ (Xf M γc γm γo k ko σ ⊢ X σ))
    (hko : ko ≠ k) (hk2 : k < 2) (s : LP) (ws : PState) (ts : Nat) (hprog : s.prog = lk1bProg) (hpc : s.pc = 1)
    (hq : s.q = []) (h10 : s.rd 10 = Weak.Prom.Ref.Lit.Y) (h11 : s.rd 11 = Weak.Prom.Ref.Lit.X)
    (hlen : s.regs.length = 32) :
    (⌜s.rd 5 ≠ 0⌝ ∨ KB0 (GF := GF) γc γm k ts ws) ⊢ wpT (hlc := hlc) X lkImg M k s ws (fun _ => iprop(True)) := by
  iintro H
  iapply (wpT_fence (f := ⟨true, false, false, false, true, true, false, false⟩) hq (by rw [hprog, hpc]; rfl))
  iintro %s' %hs'
  obtain ⟨hP', hc', hq'⟩ := LPstep_at hs' hprog (by rw [hpc])
  have e5 : s'.rd 5 = s.rd 5 := LPstep_rd hs' 5 (.inr rfl)
  iapply (hB M γc γm γo k ko X hinv hX hko hk2 s' _ ts hP' hc' hq' (by rw [LPstep_rd hs' 10 (.inr rfl), h10])
    (by rw [LPstep_rd hs' 11 (.inr rfl), h11]) (by rw [hs'.2.2.2.1, hlen]))
  have hfl := fRRW_floor ws
  unfold KB0 KB
  icases H with (%h5 | Hr | ⟨%cr, Hm, Hc, %hc⟩)
  · ileft; ipureintro; rw [e5]; exact h5
  · iright; ileft; iexact Hr
  · iright; iright; iexists cr; iframe; ipureintro
    obtain ⟨a1, a2, a3, a4⟩ := hc
    exact ⟨a1, a2, a3, Nat.le_trans a4 hfl.1, Nat.le_trans a4 hfl.2⟩

/-- **THE ACQUIRE** `amoswap.w x5,x6,(x10)` (no aq; in place: `relClassPre` from `psInit`): THE AMO LEAF
(`lk_acq`). -/
theorem hA (hinv : invalFree M) (hX : ∀ σ, (X σ ⊢ Xf M γc γm γo k ko σ) ∧ (Xf M γc γm γo k ko σ ⊢ X σ))
    (hko : ko ≠ k) (hk2 : k < 2) (s : LP) (hprog : s.prog = lk1bProg) (hpc : s.pc = 0) (hq : s.q = [])
    (h6 : s.rd 6 = 1) (h10 : s.rd 10 = Weak.Prom.Ref.Lit.Y) (h11 : s.rd 11 = Weak.Prom.Ref.Lit.X)
    (hlen : s.regs.length = 32) :
    hv (GF := GF) γm (.pr 0 none none) ⊢ wpT (hlc := hlc) X lkImg M k s psInit (fun _ => iprop(True)) := by
  iintro Hmy
  iapply (wpT_amo (op := .swap) (sz := 4) (aq := false) (rl := false) (rd := 5) (rs2 := 6) (rs1 := 10) hq
    (by rw [hprog, hpc]; rfl) (by rw [h10]; decide))
  inext
  iintro %σ %tvs %ts %σ' %hl4 %hful %hrmw HX _
  have hb : ((s.rd 10 : Nat) : Int) = Lw := by rw [h10]; rfl
  have hd : amoD .swap 4 (s.rd 6) tvs = toBytes 1 4 := by rw [PF.amoD_swap, h6]
  rw [hb, hd] at hrmw hful
  rw [hb, hd]
  obtain ⟨_, hmsg, hlo, hex, hcoh, _⟩ := hrmw
  have hM : M[ts - 1]? = some (acqMsg k) := (take_msg hmsg).1
  ihave HX := (hX σ).1 $$ HX
  icases HX with ⟨%g, Hc, Hm, Ho, %hok, Hb⟩
  unfold hv
  ihave %e := ghost_var_agree γm _ _ _ _ $$ Hmy Hm
  obtain ⟨e1, e2, e3⟩ := pr_inj e
  obtain ⟨⟨t0, b0⟩, rest, rfl⟩ : ∃ tb r, tvs = tb :: r := by
    cases tvs with
    | nil => simp at hl4
    | cons tb r => exact ⟨tb, r, rfl⟩
  have hl3 : rest.length = 3 := by simp at hl4; omega
  obtain ⟨hmb, ht0n, _⟩ := loadOk_byte (j := 0) hinv hlo rfl
  have hmb' : memByte lkImg M t0 Lw = some b0 := by simpa using hmb
  obtain ⟨_, _, _, htsn, _, _, _⟩ := ful_facts hok.pr hful
  have ht0 : t0 < ts := by
    have h1 := (PF.loadRun_b0 psInit false false (srcsView psInit (srcR 10)) Lw t0 b0 rest).2.2.2.1
    have h2 := PF.cohBelow_b0 hcoh (by simp [toBytes, Weak.Prom.Ref.byteList])
    omega
  have hwin : ∀ t, t0 < t → t < ts → wrL M t → au M t = some k := by
    intro t h1 h2 hw
    obtain ⟨m, hm, hbm⟩ := hw
    have hex0 : ¬ writesInBy (M.take σ'.n) (fun tid => tid ≠ some k) Lw t0 (ts - 1) := hex.1
    have hau : au M t = m.tid := by simp [au, hm]
    rw [hau]
    exact Classical.byContradiction fun hne => hex0 ⟨t, h1, by omega, m,
      by rw [List.getElem?_take, if_pos (by omega)]; exact hm, hbm, hne⟩
  -- the continuation (the branch), with the knowledge of the leaf
  let ws1 := PF.qPosts (amoPost (storeRun (loadRun psInit false false (srcsView psInit (srcR 10)) Lw ((t0, b0) :: rest))
    false (srcsView psInit (srcR 10)) ts Lw (toBytes 1 4).length ts) false ts) (regWL 5 [.DLdRes] ++ [LInstr])
  have hv1 : ts ≤ ws1.wVrOld := by
    show ts ≤ (amoPost (storeRun (loadRun psInit false false (srcsView psInit (srcR 10)) Lw ((t0, b0) :: rest))
      false (srcsView psInit (srcR 10)) ts Lw (toBytes 1 4).length ts) false ts).wVrOld
    simp only [amoPost]; omega
  have cont : ∀ s', LPstep s s' (s.pc + 1) 5 (Weak.Prom.Ref.sext 4 (ofBytes (((t0, b0) :: rest).map Prod.snd))) →
      (⌜s'.rd 5 ≠ 0⌝ ∨ KB0 (GF := GF) γc γm k ts ws1) ⊢ wpT (hlc := hlc) X lkImg M k s' ws1 (fun _ => iprop(True)) := by
    intro s' hs'
    obtain ⟨hP', hc', hq'⟩ := LPstep_at hs' hprog (by rw [hpc])
    exact hA1 M γc γm γo k ko X hinv hX hko hk2 s' ws1 ts hP' hc' hq' (by rw [LPstep_rd hs' 10 (.inl (by decide)), h10])
      (by rw [LPstep_rd hs' 11 (.inl (by decide)), h11]) (by rw [hs'.2.2.2.1, hlen])
  have hx5 : ∀ s', LPstep s s' (s.pc + 1) 5 (Weak.Prom.Ref.sext 4 (ofBytes (((t0, b0) :: rest).map Prod.snd))) →
      b0 ≠ 0 → s'.rd 5 ≠ 0 := by
    intro s' hs' hb0 h0
    rw [LPstep_rd_eq hs' (by decide) (by omega)] at h0
    exact hb0 (amo_x5 hl3 h0)
  rcases lk_acq hok (lkImg_zero Lw) e1.symm hful hM hmb' ht0 hwin with
      ⟨hb0, g', hok', hph', hrds', hmk', hsp', hcase'⟩ | ⟨g', hok', hsp', hph', hrds', hmk', hcr'⟩ |
      ⟨hb0, hspf, u, g', hok', hsp', hls', hph', hrds', hmk', hu, hhold, hts', htst, _, _, hcase'⟩
  · -- GIVE UP
    have e4 : Pg g' k = MG.pr 2 none none := by simp [Pg, hph', hrds', hmk', upd, ← e2, ← e3]
    have e5 : Pg g' ko = Pg g ko :=
      Pg_other hko (fun a ha => by rw [hph']; exact upd_ne _ _ ha) (fun a _ => by rw [hrds']) (fun a _ => by rw [hmk'])
    imod ghost_var_update_halves (MG.pr 2 none none) γm _ _ $$ Hmy Hm with ⟨Hmy, Hm⟩
    rcases hcase' with ⟨hls', hcr'⟩ | ⟨hspf, hfree, u', hpl⟩
    · imodintro
      isplitl [Hc Hm Ho Hb]
      · iapply (hX σ').2
        iexists g'
        have eR : Rbox (GF := GF) γc g'.spoil g'.ls g'.cr = Rbox γc g.spoil g.ls g.cr := by rw [hsp', hls', hcr']
        rw [e4, e5, eR, hcr']
        unfold hv
        iframe; ipureintro; exact hok'
      iintro %s' %hs'
      iapply (cont s' hs')
      ileft; ipureintro; exact hx5 s' hs' hb0
    · have eB : Rbox (GF := GF) γc g.spoil g.ls g.cr = hv γc (.xr g.cr) := by rw [hspf, hfree]; rfl
      rw [eB]
      unfold hv
      imod ghost_var_update_halves (MG.xr g'.cr) γc _ _ $$ Hc Hb with ⟨Hc, Hb⟩
      imodintro
      isplitl [Hc Hm Ho Hb]
      · iapply (hX σ').2
        iexists g'
        have eR : Rbox (GF := GF) γc g'.spoil g'.ls g'.cr = hv γc (.xr g'.cr) := by rw [hsp', hspf, hpl]; rfl
        rw [e4, e5, eR]
        unfold hv
        iframe; ipureintro; exact hok'
      iintro %s' %hs'
      iapply (cont s' hs')
      ileft; ipureintro; exact hx5 s' hs' hb0
  · -- A ROGUE
    have e4 : Pg g' k = MG.pr 3 none none := by simp [Pg, hph', hrds', hmk', upd, ← e2, ← e3]
    have e5 : Pg g' ko = Pg g ko :=
      Pg_other hko (fun a ha => by rw [hph']; exact upd_ne _ _ ha) (fun a _ => by rw [hrds']) (fun a _ => by rw [hmk'])
    imod ghost_var_update_halves (MG.pr 3 none none) γm _ _ $$ Hmy Hm with ⟨Hmy, Hm⟩
    imodintro
    isplitl [Hc Hm Ho]
    · iapply (hX σ').2
      iexists g'
      have eR : Rbox (GF := GF) γc g'.spoil g'.ls g'.cr = iprop(True) := by rw [hsp']; rfl
      rw [e4, e5, eR, hcr']
      unfold hv
      iframe; ipureintro; exact ⟨hok', trivial⟩
    iintro %s' %hs'
    iapply (cont s' hs')
    iright
    unfold KB0 Rg hv
    ileft; iexists none, none; iexact Hmy
  · -- THE LOCK IS TAKEN: R moves to the hart
    have e4 : Pg g' k = MG.pr 1 none none := by simp [Pg, hph', hrds', hmk', upd, ← e2, ← e3]
    have e5 : Pg g' ko = Pg g ko :=
      Pg_other hko (fun a ha => by rw [hph']; exact upd_ne _ _ ha) (fun a _ => by rw [hrds']) (fun a _ => by rw [hmk'])
    imod ghost_var_update_halves (MG.pr 1 none none) γm _ _ $$ Hmy Hm with ⟨Hmy, Hm⟩
    have eR : Rbox (GF := GF) γc g'.spoil g'.ls g'.cr = iprop(True) := by rw [hsp', hls']; rfl
    rcases hcase' with ⟨hpl, hcr'⟩ | ⟨hfree, hcr'⟩
    · have eB : Rbox (GF := GF) γc g.spoil g.ls g.cr = hv γc (.xr g.cr) := by rw [hspf, hpl]; rfl
      rw [eB]
      imodintro
      isplitl [Hc Hm Ho]
      · iapply (hX σ').2
        iexists g'
        rw [e4, e5, eR, hcr']
        unfold hv
        iframe; ipureintro; exact ⟨hok', trivial⟩
      iintro %s' %hs'
      iapply (cont s' hs')
      iright
      unfold KB0 Rg hv
      iright; iexists g'.cr; rw [hcr']; iframe Hmy Hb
      ipureintro
      rw [← hcr']
      exact ⟨hhold, by omega, by omega, hv1⟩
    · have eB : Rbox (GF := GF) γc g.spoil g.ls g.cr = hv γc (.xr g.cr) := by rw [hspf, hfree]; rfl
      rw [eB]
      unfold hv
      imod ghost_var_update_halves (MG.xr g'.cr) γc _ _ $$ Hc Hb with ⟨Hc, Hb⟩
      imodintro
      isplitl [Hc Hm Ho]
      · iapply (hX σ').2
        iexists g'
        rw [e4, e5, eR]
        unfold hv
        iframe; ipureintro; exact ⟨hok', trivial⟩
      iintro %s' %hs'
      iapply (cont s' hs')
      iright
      unfold KB0 Rg hv
      iright; iexists g'.cr; iframe Hmy Hb
      ipureintro
      exact ⟨hhold, by omega, by omega, hv1⟩

end hart2

/-! ## 3. The verdict -/

/-- Both harts' initial program state. -/
def q0 : LP := ⟨lk1bProg, 0, (List.range 32).map (fun r => ((lkRegs0.lookup r).getD 0) % two64), []⟩

theorem progs_lk1bT : progs lk1bT = [q0, q0] := rfl

/-- **G4 TARGET (1b) ON TRACK (b): THE MANUAL'S EXAMPLE 2 SPINLOCK** (`amoswap.w; fence r,rw` /
`fence rw,w; amoswap.w x0,x0,(a0)`) around a counter (`ld; addi; sd`).  In every valid machine-v2 run of `lk1bT`, if
both harts finished and both acquired (x5 = 0), their final x7 (counter value + 1) differ: the critical sections are
mutually exclusive.  Proved in track (b)'s logic over NF_R with the pre-state release class (NfrPre.lean), with
(1a)'s (b1) pull, AMO leaf and in-place deposit (header). -/
theorem g4_lock1b {evs : List PEvt} {cfg : PCfg LP Unit} (hvr : validRun litStep (testImg lk1bT) () (progs lk1bT) evs cfg)
    {r0 r1 : List Nat} (h0 : doneOf (litOW lkImg cfg.pcLog) (progs lk1bT).length cfg 0 = some r0)
    (h1 : doneOf (litOW lkImg cfg.pcLog) (progs lk1bT).length cfg 1 = some r1) : lkSpec r0 r1 := by
  have hps : ∀ p ∈ progs lk1bT, p.q = [] := by
    rw [progs_lk1bT]; intro p hp; simp at hp; rw [hp]; rfl
  have hinv := lit_invalFree hvr hps
  rw [lk1bImg] at hvr
  have key := ownAdequacy (hlc := HasLC.hasLC) (GF := lkGF) (w := litOW lkImg cfg.pcLog) (ps := progs lk1bT)
    (fun done => ∀ r0 r1, done 0 = some r0 → done 1 = some r1 → lkSpec r0 r1) (fun {_} => by
      iintro
      imod ghost_var_alloc (MG.xr ⟨none, 0, 0, 0⟩) with ⟨%γc, Hc⟩
      imod ghost_var_alloc (MG.pr 0 none none) with ⟨%γ0, H0⟩
      imod ghost_var_alloc (MG.pr 0 none none) with ⟨%γ1, H1⟩
      have s1 := ghost_var_split (GF := lkGF) γc (MG.xr ⟨none, 0, 0, 0⟩) (1 : Qp).half (1 : Qp).half
      have s2 := ghost_var_split (GF := lkGF) γ0 (MG.pr 0 none none) (1 : Qp).half (1 : Qp).half
      have s3 := ghost_var_split (GF := lkGF) γ1 (MG.pr 0 none none) (1 : Qp).half (1 : Qp).half
      rw [Qp.half_add_half] at s1 s2 s3
      ihave ⟨Hc1, Hc2⟩ := s1 $$ Hc
      ihave ⟨H01, H02⟩ := s2 $$ H0
      ihave ⟨H11, H12⟩ := s3 $$ H1
      imodintro
      iexists Xl cfg.pcLog γc γ0 γ1
      isplitl [Hc1 Hc2 H01 H11]
      · iexists g0
        have eR : Rbox (GF := lkGF) γc g0.spoil g0.ls g0.cr = hv γc (.xr ⟨none, 0, 0, 0⟩) := rfl
        have ec : (g0.cr : XRec) = ⟨none, 0, 0, 0⟩ := rfl
        have ep : ∀ j, Pg g0 j = MG.pr 0 none none := fun _ => rfl
        rw [eR, ep 0, ep 1, ec]
        unfold hv
        iframe
        ipureintro; exact lk_init (M := cfg.pcLog) lkImg_zero
      isplitr
      · iapply lk_agentI
      isplitl [H02 H12]
      · rw [progs_lk1bT]
        simp only [hartsFrom]
        iapply BigSepL.bigSepL_cons.2
        isplitl [H02]
        · ihave H := hA (hlc := HasLC.hasLC) cfg.pcLog γc γ0 γ1 0 1 (Xl cfg.pcLog γc γ0 γ1) hinv
            (fun σ => ⟨.rfl, .rfl⟩) (by decide) (by decide) q0 rfl rfl rfl (by decide) (by decide) (by decide)
            (by decide) $$ [H02]
          · unfold hv; iexact H02
          iapply H
        iapply BigSepL.bigSepL_cons.2
        isplitl [H12]
        · ihave H := hA (hlc := HasLC.hasLC) cfg.pcLog γc γ1 γ0 1 0 (Xl cfg.pcLog γc γ0 γ1) hinv
            (fun σ => ⟨(Xl_swap cfg.pcLog γc γ0 γ1 σ).1, (Xl_swap cfg.pcLog γc γ0 γ1 σ).2⟩) (by decide) (by decide)
            q0 rfl rfl rfl (by decide) (by decide) (by decide) (by decide) $$ [H12]
          · unfold hv; iexact H12
          iapply H
        exact BigSepL.bigSepL_nil_intro
      · iapply lk_finalI) hvr rfl (lit_fetchBoundedPre hvr hps) hinv
  exact key r0 r1 h0 h1

/-- **G4 (1b), on the final configuration**: if both harts ran their whole program and both acquired the lock, their
final x7 differ. -/
theorem g4_lock1b_regs {evs : List PEvt} {cfg : PCfg LP Unit} (hvr : validRun litStep (testImg lk1bT) () (progs lk1bT) evs cfg)
    {a0 a1 : PAgent LP} (ha0 : cfg.pcAgs[0]? = some a0) (ha1 : cfg.pcAgs[1]? = some a1)
    (hd0 : a0.paSt.q = [] ∧ a0.paSt.prog.length ≤ a0.paSt.pc) (hd1 : a1.paSt.q = [] ∧ a1.paSt.prog.length ≤ a1.paSt.pc) :
    a0.paSt.rd 5 = 0 → a1.paSt.rd 5 = 0 → a0.paSt.rd 7 ≠ a1.paSt.rd 7 := by
  have h := g4_lock1b hvr (r0 := a0.paSt.regs) (r1 := a1.paSt.regs)
    (by simp only [doneOf, show (0 : Nat) < (progs lk1bT).length by rw [progs_lk1bT]; decide, if_true, ha0,
      Option.bind_some]; exact litDoneR_end hd0.1 hd0.2)
    (by simp only [doneOf, show (1 : Nat) < (progs lk1bT).length by rw [progs_lk1bT]; decide, if_true, ha1,
      Option.bind_some]; exact litDoneR_end hd1.1 hd1.2)
  unfold lkSpec at h
  rw [rd_regs _ 5 (by omega), rd_regs _ 5 (by omega), rd_regs _ 7 (by omega), rd_regs _ 7 (by omega)] at h
  exact h

end Weak.Prom.Own.Pre.Lk1b
