/-
Weak/Prom: **G4 target (2) on track (a): MP WITH OWNERSHIP TRANSFER, proved** (stage S4a; plan rev 7 §4 G4 (2),
§3 "Resource part", "The deposit", "Opening", R-a1).

`own_mp`: in every valid run of `mpOwnT` (OwnAMPDefs.lean), if H1's flag load returns 1 then its x load returns 42.

The proof moves x's points-to `xPts` (OwnAMPDefs.lean) from H0 to H1 through the flag message's deposit slot:
* H0: `sd x` fulfils an x-message `ts` — it takes `pend ts` out of x's bag and shoots it, so `xPts g M ts`;
  `fence rw,w` raises the store floor `vwNew ≥ vwOld ≥ ts`; `sd flag` (release-class by plan §3's definition) fulfils
  a flag message `tf > pv ≥ ts` (EXT) and DEPOSITS `xPts g M ts` with `ts < tf` into slot `tf` (`slot_deposit`).
* H1: `ld flag` reads byte 0 from some `s0` with value 1, so `s0 ≥ 1`; `fence r,rw` raises `vwNew, vrNew ≥ vrOld ≥
  s0`; at the next step THE FRONTIER RULE gives `shot g s0`.  If `s0` is a flag message, H1 CLAIMS the slot with
  its token (`slot_claim`): it now holds `xPts g M lw` with `lw < s0 ≤ vrNew`.  Otherwise `s0` is dead and fulfilled:
  doom.  `ld x`'s pre-view is `≥ vrNew > lw`, so THE OWNED READ (`load_owned`) gives 42, or a byte read from an
  x-message above `lw` (its `pend` is in the bag: doom) or from a dead message (doom).
No Ψ fact is read off the program text afterwards: the outcome is H1's guarded trace invariant (adequacy (ii)).
The run is finite (plan §4 G4 statements are over finite runs; the prefix lemma S3d is separate, [OWN.P4]).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAMPDefs

namespace Weak.Prom.OA

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The trace invariants -/

/-- H1's invariant: if its first load returned 1, its second returned 42. -/
def q1MP (ev : Trace) : Prop :=
  ∀ a b, (loadsOf ev)[0]? = some a → (loadsOf ev)[1]? = some b → obsOf a = 1 → obsOf b = 42

def qsMP : Nat → Trace → Prop
  | 1 => q1MP
  | _ => fun _ => True

theorem qsMP_nil : ∀ h, qsMP h [] := by
  intro h
  match h with
  | 1 => intro a b ha; cases ha
  | 0 => trivial
  | _ + 2 => trivial

/-- The image of the test (every byte 0). -/
abbrev imgMP : Image := testImg mpOwnT

/-- Hart `h`'s world. -/
abbrev wMP (M : List PMsg) (h : Nat) : HW LP Unit Unit := ⟨litStep, litDone, imgMP, M, h⟩

/-- Take a later x-message out of x's bag; the rest is the bag above it. -/
theorem xBag_take {GF : BundledGFunctors} (F : Nat → IProp GF) (M : List PMsg) {lw ts : Nat}
    (hx : msgAt M ts = some xMsg) (hlw : lw < ts) :
    ([∗list] t ∈ xBag M lw, F t) ⊢ F ts ∗ [∗list] t ∈ xBag M ts, F t := by
  unfold xBag
  exact bsl_filter_take F _ _ ts (by simp [isX, hx]; omega)
    (fun t ht => by simp at ht; exact ⟨by simp [ht.2]; omega, by omega⟩)
    (rng M) (mem_rng.2 (msgAt_le hx)) (List.nodup_range' ..)

section harts

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

theorem wfr_ge_vwNew (ws : PState) : ws.wVwNew ≤ wfr ws := by
  show ws.wVwNew ≤ stFloor ws; unfold stFloor; omega

/-- **H0, the writer**: deposits x's points-to into the flag message's slot. -/
theorem mp_h0 (g : AGN) (M : List PMsg) (γc : GName) (s0 : LP) {P0 : GSet Nat}
    (hprog : s0.prog = [Weak.Prom.Ref.Lit.sd 5 6, Weak.Prom.Ref.Lit.fRWW, Weak.Prom.Ref.Lit.sd 7 8])
    (hpc : s0.pc = 0) (hq : s0.q = []) (h5 : s0.rd 5 = 42) (h6 : s0.rd 6 = X) (h7 : s0.rd 7 = 1)
    (h8 : s0.rd 8 = Y) :
    mpCtx (GF := GF) g M γc ∗ xPts g M 0 ∗ lhA g Proto.triv (wMP M 0) (qsMP 0) psInit P0 [] ⊢
      wpKA g Proto.triv (wMP M 0) qsMP s0
        (fun _ => iprop(⌜∃ V, grd Proto.triv imgMP M V True⌝ ∨ dshot g)) := by
  have hw := litW_lit imgMP M 0
  have hag := litAg_lit (V := Unit) litDone imgMP M 0
  iintro ⟨#Hctx, Hx, Hl⟩
  -- `sd x5,(x6)`
  iapply (wpKA_sw (sz := 8) (rs2 := 5) (rs1 := 6) (off := 0) (base := (X : Int)) hw (hag s0) hq
    (by rw [hprog, hpc]; rfl) (alg_of h6 (by decide) (by decide)) (base_of h6 (by decide)))
  iframe Hl
  inext
  iintro %ts %_ %hmsg %_ %hext _ _
  rw [h5] at hmsg
  have hts1 : 1 ≤ ts := by omega
  have hmx : msgAt M ts = some xMsg := by
    obtain ⟨k, rfl⟩ : ∃ k, ts = k + 1 := ⟨ts - 1, by omega⟩
    simpa [msgAt, xMsg] using hmsg
  have htsM : ts ≤ M.length := (msgAt_le hmx).2
  unfold xPts
  icases Hx with ⟨_, Hbag⟩
  icases xBag_take (pend g) M hmx (by omega : 0 < ts) $$ Hbag with ⟨Hp, Hbag⟩
  imod shoot $$ Hp with #Hsh
  imodintro
  isplitr
  · ileft; ipureintro; exact ⟨⟨0, grd_intro trivial⟩, grd_intro trivial⟩
  iframe Hsh
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  -- `fence rw,w`
  iapply (wpKA_fence (f := ⟨true, true, false, false, false, true, false, false⟩) hw (hag s1) hq1
    (by rw [hP1, hc1]; rfl))
  iframe Hl
  inext
  iintro %s2 %hs2 _ _
  imodintro
  iintro Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have e7 : s2.rd 7 = 1 := by rw [LPstep_rd hs2 7 (.inr rfl), LPstep_rd hs1 7 (.inr rfl), h7]
  have e8 : s2.rd 8 = Y := by rw [LPstep_rd hs2 8 (.inr rfl), LPstep_rd hs1 8 (.inr rfl), h8]
  -- `sd x7,(x8)`: the release-class flag store deposits x's points-to
  iapply (wpKA_sw (sz := 8) (rs2 := 7) (rs1 := 8) (off := 0) (base := (Y : Int)) hw (hag s2) hq2
    (by rw [hP2, hc2]; rfl) (alg_of e8 (by decide) (by decide)) (base_of e8 (by decide)))
  iframe Hl
  inext
  iintro %tf %_ %hmsgf %_ %hextf _ Hc
  rw [e7] at hmsgf
  have htf1 : 1 ≤ tf := by omega
  have hmf : msgAt M tf = some fMsg := by
    obtain ⟨k, rfl⟩ : ∃ k, tf = k + 1 := ⟨tf - 1, by omega⟩
    simpa [msgAt, fMsg] using hmsgf
  have htfM : tf ≤ M.length := (msgAt_le hmf).2
  -- EXT: the flag message is above the x message (`fence rw,w` raised `vwNew` to `vwOld ≥ ts`)
  have hlt : ts < tf := by
    have key : ∀ ws : PState, ts ≤ ws.wVwNew →
        stPreA ws false false (srcsView ws (srcR 8)) (srcsView ws (srcR 7)) < tf → ts < tf :=
      fun ws h1 h2 => by have := (PF.stPreA_ge ws false false (srcsView ws (srcR 8)) (srcsView ws (srcR 7))).2.2.2.1; omega
    refine key _ ?_ hextf
    have hvo := (storeRun_mono psInit false (srcsView psInit (srcR 6))
      (max (srcsView psInit (srcR 6)) (srcsView psInit (srcR 5))) (X : Int) (toBytes (s0.rd 5) 8).length ts).2.2.1
    dsimp only
    simp only [instrR_vwNew, fence_vwNew, instrR_vwOld, instrR_vrOld, acqPost_false, hvo, ite_true]
    omega
  ihave #Hslot : slotInv g tf (fR g M tf) γc $$ []
  · unfold mpCtx
    icases Hctx with ⟨_, Hs, _⟩
    iapply bsl_mem (F := fun t => slotInv g t (fR g M t) γc)
      (List.mem_filter.2 ⟨mem_rng.2 ⟨htf1, htfM⟩, by simp [isF, hmf]⟩) $$ Hs
  imod slot_deposit g tf (fR g M tf) γc $$ [Hslot Hbag Hc] with #Hshf
  · iframe Hslot Hc
    unfold fR xPts
    iexists ts
    iframe Hbag
    ipureintro; exact ⟨⟨hts1, hlt⟩, fun _ => hmx⟩
  imodintro
  isplitr
  · ileft; ipureintro; exact ⟨⟨0, grd_intro trivial⟩, grd_intro trivial⟩
  iframe Hshf
  iintro %s3 %hs3 _ _
  imodintro
  iintro Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  have hend : s3.prog.length ≤ s3.pc := by rw [hP3, hc3]; simp
  iapply (wpKA_end (v := ()) (hag s3) hq3 hend
    (by show litDone s3 = some (); unfold litDone; rw [if_pos ⟨hq3, hend⟩]))
  iframe Hl
  imodintro
  ileft; ipureintro; exact ⟨0, grd_intro trivial⟩


theorem obsOf_map (tvs : List (Nat × BitVec 8)) :
    obsOf tvs = (tvs.map Prod.snd).foldr (fun b acc => b.toNat + 256 * acc) 0 := by
  induction tvs with
  | nil => rfl
  | cons tv r ih => simp [obsOf, List.foldr] at *; rw [← ih]

theorem obs_42 {tvs : List (Nat × BitVec 8)} (h : tvs.map Prod.snd = toBytes 42 8) : obsOf tvs = 42 := by
  rw [obsOf_map, h]; decide

theorem obs_one {t : Nat} {v : BitVec 8} {r : List (Nat × BitVec 8)} (h : obsOf ((t, v) :: r) = 1) : v = 1 := by
  have hv := v.isLt
  have : v.toNat + 256 * obsOf r = 1 := h
  apply BitVec.eq_of_toNat_eq
  show v.toNat = 1
  omega

theorem q1_one (tvs : List (Nat × BitVec 8)) (l : PLabel) (hl : loadLikeTvs l = some tvs) :
    q1MP [(l, none)] := by
  intro a b _ hb
  simp [loadsOf, hl] at hb

theorem imgMP_Y : imgMP (Y : Int) = some 0 := by decide

/-- **H1's tail** (`ld x7,(x8)`, then the end), from whatever the fence step obtained: nothing to prove (the flag
was not 1), doom, or x's points-to with its latest write below the load floor `vrNew`. -/
theorem mp_h1_tail (g : AGN) (M : List PMsg) (γc : GName) (s2 : LP) (ws : PState) {pr : GSet Nat}
    (tvs0 : List (Nat × BitVec 8)) (hprog : s2.prog = [Weak.Prom.Ref.Lit.ld 5 6, Weak.Prom.Ref.Lit.fRRW,
      Weak.Prom.Ref.Lit.ld 7 8]) (hpc : s2.pc = 2) (hq : s2.q = []) (h8 : s2.rd 8 = X) :
    mpCtx (GF := GF) g M γc ∗
      (⌜obsOf tvs0 ≠ 1⌝ ∨ dshot g ∨ ∃ lw, ⌜1 ≤ lw ∧ lw ≤ ws.wVrNew⌝ ∗ xPts g M lw) ∗
      lhA g Proto.triv (wMP M 1) (qsMP 1) ws pr [(LLoad false false (Y : Int) tvs0 (srcR 6), none)] ⊢
      wpKA g Proto.triv (wMP M 1) qsMP s2 (fun _ => iprop(⌜∃ V, grd Proto.triv imgMP M V True⌝ ∨ dshot g)) := by
  have hw := litW_lit imgMP M 1
  have hag := litAg_lit (V := Unit) litDone imgMP M 1
  iintro ⟨#Hctx, HG, Hl⟩
  iapply (wpKA_ld (sz := 8) (sgn := true) (rd := 7) (rs1 := 8) (off := 0) (base := (X : Int)) hw (hag s2) hq
    (by rw [hprog, hpc]; rfl) (alg_of h8 (by decide) (by decide)) (base_of h8 (by decide)))
  iframe Hl
  inext
  iintro %tvs1 %hl1 %hlo1 _ _
  have hobl : obsOf tvs1 = 42 → qsMP 1 ([(LLoad false false (Y : Int) tvs0 (srcR 6), none)] ++
      [(LLoad false false (X : Int) tvs1 (srcR 8), none)]) := by
    intro h42 a b ha hb _
    simp [loadsOf, loadLikeTvs] at ha hb
    rw [← hb]; exact h42
  ihave Hr : |={⊤}=> (⌜∃ V, grd Proto.triv imgMP M V (qsMP 1 ([(LLoad false false (Y : Int) tvs0 (srcR 6), none)] ++
      [(LLoad false false (X : Int) tvs1 (srcR 8), none)]))⌝ ∨ dshot g) $$ [HG]
  · icases HG with (%hne | #Hd | ⟨%lw, %hlw, Hx⟩)
    · imodintro; ileft; ipureintro
      refine ⟨0, grd_intro ?_⟩
      intro a b ha _ h1
      simp [loadsOf, loadLikeTvs] at ha
      rw [← ha] at h1; exact absurd h1 hne
    · imodintro; iright; iexact Hd
    · unfold xPts
      icases Hx with ⟨%hmx, Hbag⟩
      have hmw := hmx hlw.1
      have hvp : lw ≤ ldPre ws false false (srcsView ws (srcR 8)) := by
        have := (PF.ldPre_ge ws false false (srcsView ws (srcR 8)))
        unfold ldPre; omega
      have hown := load_owned (ws := ws) hlw.1 hmw rfl rfl hvp 0 tvs1 (by rw [hl1]; decide)
        (by have := loadOk_weak hlo1; simpa [xMsg] using this)
      rcases hown with hval | ⟨s, hs, m, hm, j, hj, htj⟩
      · imodintro; ileft; ipureintro
        refine ⟨0, grd_intro (hobl (obs_42 ?_))⟩
        rw [hval, hl1]; rfl
      · by_cases hmX : m = xMsg
        · subst hmX
          icases xBag_take (pend g) M hm hs $$ Hbag with ⟨Hp, -⟩
          unfold mpCtx
          icases Hctx with ⟨Hdoom, -, -⟩
          imod doom (E := ⊤) CoPset.subseteq_top g M s (msgAt_le hm) $$ [Hdoom Hp] with #Hd
          · iframe Hdoom Hp
          imodintro; iright; iexact Hd
        · have hmF : m ≠ fMsg := by
            intro e; subst e; exact fMsg_not_X j (by rw [hl1] at hj; omega) htj
          have hD : isD M s = true := by
            simp [isD, isX, isF, hm, hmX, hmF]
          unfold mpCtx
          icases Hctx with ⟨Hdoom, -, Hdd⟩
          ihave #Hds := bsl_mem (F := fun t => deadInv g t)
            (List.mem_filter.2 ⟨mem_rng.2 (msgAt_le hm), hD⟩) $$ Hdd
          imod dead_doom g M s (msgAt_le hm) $$ [Hdoom Hds] with #Hd
          · iframe Hdoom Hds
          imodintro; iright; iexact Hd
  imod Hr with Hr
  imodintro
  iframe Hr
  iintro %s3 %hs3 _ _
  imodintro
  iintro Hl
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hprog (by rw [hpc])
  have hend : s3.prog.length ≤ s3.pc := by rw [hP3, hc3]; simp
  iapply (wpKA_end (v := ()) (hag s3) hq3 hend
    (by show litDone s3 = some (); unfold litDone; rw [if_pos ⟨hq3, hend⟩]))
  iframe Hl
  imodintro
  ileft; ipureintro; exact ⟨0, grd_intro trivial⟩


theorem frontA_shot {g : AGN} {π : Proto} {img : Image} {M : List PMsg} {ws : PState} (t : Nat) :
    frontA (GF := GF) g π img M ws ⊢ ⌜1 ≤ t ∧ t ≤ M.length ∧ t ≤ wfr ws⌝ -∗ shot g t := by
  unfold frontA
  iintro ⟨#H, _⟩ %h
  iapply H
  ipureintro; exact h

/-- **H1, the reader**: claims x's points-to from the flag message's slot, then reads x. -/
theorem mp_h1 (g : AGN) (M : List PMsg) (γc : GName) (s0 : LP) {P0 : GSet Nat}
    (hprog : s0.prog = [Weak.Prom.Ref.Lit.ld 5 6, Weak.Prom.Ref.Lit.fRRW, Weak.Prom.Ref.Lit.ld 7 8])
    (hpc : s0.pc = 0) (hq : s0.q = []) (h6 : s0.rd 6 = Y) (h8 : s0.rd 8 = X) :
    mpCtx (GF := GF) g M γc ∗ token γc ∗ lhA g Proto.triv (wMP M 1) (qsMP 1) psInit P0 [] ⊢
      wpKA g Proto.triv (wMP M 1) qsMP s0 (fun _ => iprop(⌜∃ V, grd Proto.triv imgMP M V True⌝ ∨ dshot g)) := by
  have hw := litW_lit imgMP M 1
  have hag := litAg_lit (V := Unit) litDone imgMP M 1
  iintro ⟨#Hctx, Htok, Hl⟩
  -- `ld x5,(x6)` (the flag)
  iapply (wpKA_ld (sz := 8) (sgn := true) (rd := 5) (rs1 := 6) (off := 0) (base := (Y : Int)) hw (hag s0) hq
    (by rw [hprog, hpc]; rfl) (alg_of h6 (by decide) (by decide)) (base_of h6 (by decide)))
  iframe Hl
  inext
  iintro %tvs0 %hl0 %hlo0 _ _
  imodintro
  isplitr
  · ileft; ipureintro; exact ⟨0, grd_intro (q1_one tvs0 _ rfl)⟩
  iintro %s1 %hs1 _ _
  imodintro
  iintro Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  -- `fence r,rw`: at the next step, the frontier covers the flag message read
  iapply (wpKA_fence (f := ⟨true, false, false, false, true, true, false, false⟩) hw (hag s1) hq1
    (by rw [hP1, hc1]; rfl))
  iframe Hl
  inext
  iintro %s2 %hs2 #Hfr Hc
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have e8 : s2.rd 8 = X := by rw [LPstep_rd hs2 8 (.inr rfl), LPstep_rd hs1 8 (.inl (by decide)), h8]
  ihave HG : |={⊤}=> (⌜obsOf tvs0 ≠ 1⌝ ∨ dshot g ∨ ∃ lw, ⌜1 ≤ lw ∧ lw ≤ (instrR (fencePost
      (qPosts (loadRun psInit false false (srcsView psInit (srcR 6)) (Y : Int) tvs0) (regWL 5 [.DLdRes] ++ [LInstr]))
      true false true true)).wVrNew⌝ ∗ xPts g M lw) $$ [Htok Hc]
  · by_cases hv : obsOf tvs0 = 1
    · obtain ⟨t0, v0, r0, rfl⟩ := tvs_cons hl0 (by decide)
      have hv0 := obs_one hv
      have hb := (loadOk_b0 hlo0).1
      obtain ⟨k, m, ht0, hmk, hby⟩ := src_of_val hb imgMP_Y (by rw [hv0]; decide)
      have hmt : msgAt M t0 = some m := by rw [ht0]; exact hmk
      -- `vrOld ≥ t0` after the load (X4); `fence r,rw` raises both floors to it
      have hro : t0 ≤ (qPosts (loadRun psInit false false (srcsView psInit (srcR 6)) (Y : Int) ((t0, v0) :: r0))
          (regWL 5 [.DLdRes] ++ [LInstr])).wVrOld := by
        have := (loadRun_b0 psInit false false (srcsView psInit (srcR 6)) (Y : Int) t0 v0 r0).2.1
        rw [fwdView_empty rfl] at this
        simp only [regWL, qPosts, qPost, regWP_vrOld, instrR_vrOld, show (5 : Nat) ≠ 0 by decide, if_false,
          List.singleton_append]
        omega
      have hfl : t0 ≤ wfr (fencePost (qPosts (loadRun psInit false false (srcsView psInit (srcR 6)) (Y : Int)
          ((t0, v0) :: r0)) (regWL 5 [.DLdRes] ++ [LInstr])) true false true true) := by
        refine Nat.le_trans ?_ (wfr_ge_vwNew _)
        simp only [fence_vwNew, ite_true]
        omega
      have hvr : t0 ≤ (instrR (fencePost (qPosts (loadRun psInit false false (srcsView psInit (srcR 6)) (Y : Int)
          ((t0, v0) :: r0)) (regWL 5 [.DLdRes] ++ [LInstr])) true false true true)).wVrNew := by
        simp only [instrR_vrNew, fence_vrNew, ite_true]
        omega
      ihave #Hsh := frontA_shot t0 $$ Hfr %⟨(msgAt_le hmt).1, (msgAt_le hmt).2, hfl⟩
      unfold mpCtx
      icases Hctx with ⟨_, Hs, Hdd⟩
      by_cases hf : m = fMsg
      · -- a flag message: claim the slot
        subst hf
        ihave #Hslot := bsl_mem (F := fun t => slotInv g t (fR g M t) γc)
          (List.mem_filter.2 ⟨mem_rng.2 (msgAt_le hmt), by simp [isF, hmt]⟩) $$ Hs
        imod slot_claim g t0 (fR g M t0) γc $$ [Hslot Hsh Htok Hc] with HR
        · iframe Hslot Hsh Htok Hc
        unfold fR
        icases HR with ⟨%lw, %hlw, Hx⟩
        imodintro
        iright; iright
        iexists lw
        iframe Hx
        ipureintro; exact ⟨hlw.1, by omega⟩
      · -- any other message holding 1 at the flag is dead: doom
        have hmX : m ≠ xMsg := by intro e; subst e; rw [xMsg_byte_Y] at hby; cases hby
        have hD : isD M t0 = true := by simp [isD, isX, isF, hmt, hmX, hf]
        ihave #Hds := bsl_mem (F := fun t => deadInv g t)
          (List.mem_filter.2 ⟨mem_rng.2 (msgAt_le hmt), hD⟩) $$ Hdd
        imod dead_shot g t0 $$ [Hds Hsh] with #Hd
        · iframe Hds Hsh
        imodintro
        iright; ileft; iexact Hd
    · imodintro; ileft; ipureintro; exact hv
  imod HG with HG
  imodintro
  dsimp only [List.nil_append]
  iintro Hl
  iapply (mp_h1_tail g M γc s2 _ tvs0 hP2 hc2 hq2 e8)
  iframe Hctx HG
  iexact Hl

end harts

/-! ## 2. The closed functor bundle -/

section gf
open Iris COFE Auth HeapView

/-- The functors of track (a)'s MP proof: invariants (0–2), later credits (3), hart ghosts (4), one-shots (5),
the claim token (6). -/
noncomputable def ownGF : BundledGFunctors := fun n =>
  match n with
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF CoPsetDisjL, by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨GhostVarF HSt, by infer_instance⟩
  | 5 => ⟨GhostVarF Bool, by infer_instance⟩
  | 6 => ⟨TokenF, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

instance : WsatGpreS ownGF where
  inv := { τ := 0, transp := by unfold ownGF; rfl }
  enabled := { τ := 1, transp := by unfold ownGF; rfl }
  disabled := { τ := 2, transp := by unfold ownGF; rfl }

instance : LcGpreS ownGF where
  lc_elem := { τ := 3, transp := by unfold ownGF; rfl }

instance : InvGpreS ownGF where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance

instance : GhostVarG ownGF HSt where
  elemG := { τ := 4, transp := by unfold ownGF; rfl }

instance : GhostVarG ownGF Bool where
  elemG := { τ := 5, transp := by unfold ownGF; rfl }

instance : TokenG ownGF where
  elemG := { τ := 6, transp := by unfold ownGF; rfl }

end gf

/-! ## 3. The verdict -/

theorem progs_mpOwn : ∃ p0 p1 : LP, progs mpOwnT = [p0, p1] := ⟨_, _, rfl⟩

/-- The two harts' wps, in the shape of the adequacy premise. -/
theorem mp_assemble [InvGS ownGF] (g : AGN) (M : List PMsg) (γc : GName) (p0 p1 : LP) {P0 : Nat → GSet Nat}
    (hpr0 : p0.prog = [Weak.Prom.Ref.Lit.sd 5 6, Weak.Prom.Ref.Lit.fRWW, Weak.Prom.Ref.Lit.sd 7 8])
    (hpc0 : p0.pc = 0) (hq0 : p0.q = []) (h5 : p0.rd 5 = 42) (h6 : p0.rd 6 = X) (h7 : p0.rd 7 = 1)
    (h8 : p0.rd 8 = Y)
    (hpr1 : p1.prog = [Weak.Prom.Ref.Lit.ld 5 6, Weak.Prom.Ref.Lit.fRRW, Weak.Prom.Ref.Lit.ld 7 8])
    (hpc1 : p1.pc = 0) (hq1 : p1.q = []) (h6' : p1.rd 6 = Y) (h8' : p1.rd 8 = X) :
    mpCtx (GF := ownGF) g M γc ∗ xPts g M 0 ∗ token γc ∗ hartA g 0 psInit (P0 0) [] ∗
      hartA g (0 + 1) psInit (P0 (0 + 1)) [] ⊢
    [∗list] k ↦ p ∈ [p0, p1], wpA (hlc := .hasLC) g Proto.triv (hw litStep litDone imgMP M k)
      (fun h => ΨK M (qsMP h)) p
      (fun v => iprop(⌜∃ V, grd Proto.triv imgMP M V ((fun (_ : Nat) (_ : Unit) => True) k v)⌝ ∨ dshot g)) := by
  have k0 := mp_h0 (GF := ownGF) g M γc p0 (P0 := P0 0) hpr0 hpc0 hq0 h5 h6 h7 h8
  have k1 := mp_h1 (GF := ownGF) g M γc p1 (P0 := P0 1) hpr1 hpc1 hq1 h6' h8'
  have s0 := lhA_start (GF := ownGF) (g := g) (π := Proto.triv) (w := wMP M 0) (Qs := qsMP) (P0 := P0 0) (qsMP_nil 0)
  have s1 := lhA_start (GF := ownGF) (g := g) (π := Proto.triv) (w := wMP M 1) (Qs := qsMP) (P0 := P0 1) (qsMP_nil 1)
  have k0' : mpCtx (GF := ownGF) g M γc ∗ xPts g M 0 ∗ lhA g Proto.triv (wMP M 0) (qsMP 0) psInit (P0 0) [] ⊢
      wpA (hlc := .hasLC) g Proto.triv (hw litStep litDone imgMP M 0) (fun h => ΨK M (qsMP h)) p0
        (fun v => iprop(⌜∃ V, grd Proto.triv imgMP M V ((fun (_ : Nat) (_ : Unit) => True) 0 v)⌝ ∨ dshot g)) := k0
  have k1' : mpCtx (GF := ownGF) g M γc ∗ token γc ∗ lhA g Proto.triv (wMP M 1) (qsMP 1) psInit (P0 1) [] ⊢
      wpA (hlc := .hasLC) g Proto.triv (hw litStep litDone imgMP M (0 + 1)) (fun h => ΨK M (qsMP h)) p1
        (fun v => iprop(⌜∃ V, grd Proto.triv imgMP M V ((fun (_ : Nat) (_ : Unit) => True) (0 + 1) v)⌝ ∨
          dshot g)) := k1
  have s1' : hartA (GF := ownGF) g (0 + 1) psInit (P0 (0 + 1)) [] ⊢
      lhA g Proto.triv (wMP M 1) (qsMP 1) psInit (P0 1) [] := s1
  iintro ⟨#Hctx, Hx, Ht, H0, H1⟩
  iapply (BigSepL.bigSepL_cons).2
  isplitl [Hx H0]
  · iapply k0'
    iframe Hctx Hx
    iapply s0
    iexact H0
  iapply (BigSepL.bigSepL_cons).2
  isplitl [Ht H1]
  · iapply k1'
    iframe Hctx Ht
    iapply s1'
    iexact H1
  iapply (BigSepL.bigSepL_nil).2
  itrivial

/-- THE ADEQUACY PREMISE for MP with ownership: the setup (OwnAMPDefs.lean `mp_setup`), H0's and H1's proofs. -/
theorem mp_premise (M : List PMsg) :
    wpPremise .hasLC ownGF litStep litDone imgMP M (progs mpOwnT) Proto.triv (fun _ _ => True)
      (fun h => ΨK M (qsMP h)) := by
  intro Hinv g P0 hn hm hP0
  obtain ⟨p0, p1, hps⟩ := progs_mpOwn
  have hg0 : (progs mpOwnT)[0]? = some p0 := by rw [hps]; rfl
  have hg1 : (progs mpOwnT)[1]? = some p1 := by rw [hps]; rfl
  obtain ⟨hpr0, hpc0, hq0, _, hrd0⟩ := progs_get hg0
  obtain ⟨hpr1, hpc1, hq1, _, hrd1⟩ := progs_get hg1
  have hlen : g.hn.length = 2 := by rw [hn, hps]; rfl
  obtain ⟨γ0, γ1, hgn⟩ : ∃ a b, g.hn = [a, b] := by
    match h : g.hn, hlen with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  rw [hps]
  iintro #Hdoom Hh Hp
  imod mp_setup g M hm $$ [Hp] with ⟨%γc, #Hctx, Hx, Htok⟩
  · iframe Hdoom Hp
  rw [hgn]
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H0, Hh⟩
  icases (BigSepL.bigSepL_cons).1 $$ Hh with ⟨H1, -⟩
  imodintro
  iapply (mp_assemble g M γc p0 p1 (P0 := P0) hpr0 hpc0 hq0 (by rw [hrd0 5 (by decide) (by decide)]; rfl)
    (by rw [hrd0 6 (by decide) (by decide)]; rfl) (by rw [hrd0 7 (by decide) (by decide)]; rfl)
    (by rw [hrd0 8 (by decide) (by decide)]; rfl) hpr1 hpc1 hq1 (by rw [hrd1 6 (by decide) (by decide)]; rfl)
    (by rw [hrd1 8 (by decide) (by decide)]; rfl))
  iframe Hctx Hx Htok H0 H1

/-- **G4 TARGET (2) ON TRACK (a): MP WITH OWNERSHIP TRANSFER** (plan §4 G4 (2)).  Over every final memory and every
valid run of machine v2 of `mpOwnT` (`sd x; fence rw,w; sd flag` ‖ `ld flag; fence r,rw; ld x`): if H1's flag load
returned 1, its x load returned 42.  Proved in the logic by moving x's points-to from H0 to H1 through the flag
message's deposit slot (see the header); 0 named inputs; finite runs (the prefix lemma S3d is separate, [OWN.P4]). -/
theorem own_mp (M : List PMsg) (run : PFRun LP Unit)
    (hrun : PF.validRun litStep imgMP () (progs mpOwnT) M run) :
    ∀ b, run.obsLoad 1 0 = some 1 → run.obsLoad 1 1 = some b → b = 42 := by
  obtain ⟨_, hΨ, _⟩ := adequacyA (hlc := .hasLC) (GF := ownGF) Proto.triv (fun _ _ => True)
    (fun h => ΨK M (qsMP h)) trivial (fun h => ⟨qsMP_nil h, wrOk_nil M⟩) (mp_premise M) hrun
  intro b h0 h1
  have hq := (hΨ 1 (run.trace 1).length).1
  rw [List.take_length] at hq
  unfold PFRun.obsLoad at h0 h1
  rw [← loadsOf_memEv] at h0 h1
  obtain ⟨a, ha, ha1⟩ := Option.map_eq_some_iff.1 h0
  obtain ⟨b', hb, hb1⟩ := Option.map_eq_some_iff.1 h1
  rw [← hb1]
  exact hq a b' ha hb ha1

#print axioms own_mp

end Weak.Prom.OA
