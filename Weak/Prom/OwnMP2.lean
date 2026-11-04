/-
Weak/Prom: **G4 target (2′), MP-ownership with a WRITING receiver, proved on track (b)** (stage S4b part 2; plan
rev 7 §4 "Gate G4" (2′)).  Test, verdict and the finding on (b2-pull): OwnMP2Defs.lean header.

The proof is MPL's (OwnMPL.lean) for H0 and for H1's flag read and claim; H1's `sd 2` after `fence r,rw` is
release-class (`relClass_fRW`: the fence raises `vwNew` to `vrOld`, and H1 has no earlier store), so it is appended
IN PLACE: as the holder, H1's message becomes x's latest (`h1_st_own`); without the claim (flag ≠ 1 or a dead
message) x is spoiled (`h1_st_spoil`).  At the end of a valid run no x-message after the holder's is pending, so H1's
2 is the last write to x (`mp2Ok_final`).  0 named inputs; finite runs (prefix lemma S3d separate).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnMP2Defs
import Weak.Prom.OwnMPL
import Weak.Prom.OwnLitSide
import Weak.Prom.CoreKitQ
import Iris.Instances.Lib.GhostVar
import Iris.Instances.Lib.Token
import Iris.Instances.Lib.WSat
import Iris.Instances.Lib.LaterCredits
import Iris.Algebra.Auth

namespace Weak.Prom.Own.MP2

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Mach Weak.Prom.Mach.Cert Weak.Prom.Own
open Weak.Prom.Own.MP (wrA au wrA_of_memByte)
open Weak.Prom.Own.MPL (X Y xMsg fMsg wrX wrF xVal XRec relPrG loadOk_byte val8 val8_b0 relClass_fW fwdView_psInit rd_regs)
open Weak.Prom.PF (LPstep LPstep_at LPstep_rd LPstep_rd_eq ldVal instrR)
open Weak.Prom.Ref (Instr Test two64)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. Ghost state -/

/-- The ghost-variable contents of the proof. -/
inductive MG where
  | xr (r : XRec)
  | fl (f : Option Nat)
  | b3 (bad own1 sp : Bool)

section gf
open Iris COFE Auth HeapView

/-- The functor bundle: invariants (0–2), later credits (3), the ghost variables (4), the claim token (5). -/
noncomputable def mp2GF : BundledGFunctors := fun n =>
  match n with
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF CoPsetDisjL, by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨GhostVarF MG, by infer_instance⟩
  | 5 => ⟨TokenF, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

instance : WsatGpreS mp2GF where
  inv := { τ := 0, transp := by unfold mp2GF; rfl }
  enabled := { τ := 1, transp := by unfold mp2GF; rfl }
  disabled := { τ := 2, transp := by unfold mp2GF; rfl }

instance : LcGpreS mp2GF where
  lc_elem := { τ := 3, transp := by unfold mp2GF; rfl }

instance : InvGpreS mp2GF where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance

instance : GhostVarG mp2GF MG where
  elemG := { τ := 4, transp := by unfold mp2GF; rfl }

instance : TokenG mp2GF where
  elemG := { τ := 5, transp := by unfold mp2GF; rfl }

end gf

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF MG] [TokenG GF]

/-- One half of a ghost variable. -/
def hv (γ : GName) (m : MG) : IProp GF := ghost_var γ (.own (1 : Qp).half) m

/-- FLAG'S RELEASE CELL: after the release `r`, x's points-to (holder `none`) or, once claimed, the claim token. -/
def depP (γx γc : GName) : Option Nat → IProp GF
  | none => iprop(True)
  | some r => iprop((∃ tsx, ⌜tsx < r ∧ 1 ≤ tsx⌝ ∗ hv γx (.xr ⟨none, r, tsx, 42⟩)) ∨ token γc)

/-- THE OWNERSHIP STATE INTERPRETATION of the proof. -/
abbrev Xm (M : List PMsg) (γx γf γb γc : GName) (σ : OSt (List Nat)) : IProp GF :=
  iprop(∃ (D : Nat → Prop) (rec : XRec) (f : Option Nat) (bad own1 sp : Bool),
    hv γx (.xr rec) ∗ hv γf (.fl f) ∗ hv γb (.b3 bad own1 sp) ∗ ⌜mp2Ok mp2Img M σ D rec f bad sp own1⌝ ∗
      depP γx γc f)

theorem rec_inj {a b : XRec} (h : MG.xr a = MG.xr b) : a = b := by cases h; rfl
theorem fl_inj {a b : Option Nat} (h : MG.fl a = MG.fl b) : a = b := by cases h; rfl
theorem b3_inj {a b c a' b' c' : Bool} (h : MG.b3 a b c = MG.b3 a' b' c') : a = a' ∧ b = b' ∧ c = c' := by
  cases h; exact ⟨rfl, rfl, rfl⟩

/-! ## 2. Machine facts of the two harts -/

/-- A plain store after `fence r,rw` by a hart with no earlier store is release-class (plan §3): the fence raises
`vwNew` to `vrOld`, and `vwOld = 0`. -/
theorem relClass_fRW (ws : PState) (pr pw sr sw : Bool) (hpr : pr = true) (hsw : sw = true) (hw : ws.wVwOld = 0)
    (a : Int) (d : List (BitVec 8)) (asrc vsrc : List Dsrc) :
    relClass (instrR (fencePost ws pr pw sr sw)) (LStore false false a d asrc vsrc) := by
  subst hpr hsw
  refine ⟨_, rfl, ?_⟩
  simp only [wrState, stPreA, stPre, fencePost, instrR, if_true, Bool.false_eq_true, if_false, hw]
  omega

/-! ## 3. H0: `sd x5,(x6); fence rw,w; sd x7,(x8)` -/

section h0

variable [InvGS_gen hlc GF] (M : List PMsg) (γx γf γb γc : GName)

theorem h0_end (s3 : LP) (ws : PState) (hP : s3.prog.length ≤ s3.pc) (hq : s3.q = []) :
    ⊢ wpT (hlc := hlc) (GF := GF) (Xm M γx γf γb γc) mp2Img M 0 s3 ws (fun _ => iprop(True)) := by
  iapply (wpT_end hq hP)
  iintro %σ %_ HX
  icases HX with ⟨%D, %rec, %f, %bad, %own1, %sp, Hxa, Hfa, Hba, %hok, Hdep⟩
  imodintro
  isplitl
  · iexists D, rec, f, bad, own1, sp
    iframe
    ipureintro; exact h0_fin2 hok
  · ipureintro; trivial

/-- **H0, the writer**: x's store in place, then the release in place with THE DEPOSIT. -/
theorem mp_h0 (s0 : LP)
    (hprog : s0.prog = [Weak.Prom.Ref.Lit.sd 5 6, Weak.Prom.Ref.Lit.fRWW, Weak.Prom.Ref.Lit.sd 7 8])
    (hpc : s0.pc = 0) (hq : s0.q = []) (h5 : s0.rd 5 = 42) (h6 : s0.rd 6 = Weak.Prom.Ref.Lit.X) (h7 : s0.rd 7 = 1)
    (h8 : s0.rd 8 = Weak.Prom.Ref.Lit.Y) :
    hv γx (.xr ⟨some 0, 0, 0, 0⟩) ∗ hv γf (.fl none) ⊢
      wpT (hlc := hlc) (GF := GF) (Xm M γx γf γb γc) mp2Img M 0 s0 psInit (fun _ => iprop(True)) := by
  iintro ⟨Hx, Hf⟩
  -- `sd x5,(x6)`: release-class (first write), in place
  iapply (wpT_sd (sz := 8) (rs2 := 5) (rs1 := 6) (off := 0) hq (by rw [hprog, hpc]; rfl) (by rw [h6]; decide))
  inext
  iintro %σa %ts %σa' %hful %hmsg %_ %_ HX _
  have hb : (((s0.rd 6 + 0) % two64 : Nat) : Int) = X := by rw [h6]; decide
  rcases hful with ⟨hnr, _, _⟩ | ⟨_, hn, _, rfl, rfl⟩
  · exact absurd (MP.relClass_store0 rfl rfl _ _ _ _ _ _) hnr
  have hM : M[σa.n]? = some xMsg := by
    have := (take_msg hmsg).1
    rw [hb, h5] at this
    simpa [xMsg] using this
  icases HX with ⟨%D, %rec, %f, %bad, %own1, %sp, Hxa, Hfa, Hba, %hok, Hdep⟩
  unfold hv
  ihave %e1 := ghost_var_agree γx _ _ _ _ $$ Hx Hxa
  ihave %e2 := ghost_var_agree γf _ _ _ _ $$ Hf Hfa
  obtain rfl := rec_inj e1
  obtain rfl := fl_inj e2
  rw [relPrG (fun t ht => (hok.1 0 t ht).2.1)]
  imod ghost_var_update_halves (MG.xr ⟨some 0, 0, σa.n + 1, 42⟩) γx _ _ $$ Hx Hxa with ⟨Hx, Hxa⟩
  imodintro
  isplitl [Hxa Hfa Hba Hdep]
  · iexists D, ⟨some 0, 0, σa.n + 1, 42⟩, none, bad, own1, sp
    unfold hv
    iframe Hxa Hfa Hba Hdep
    ipureintro; exact h0_x2 hok hM
  iintro %s1 %hs1
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  -- `fence rw,w`
  iapply (wpT_fence hq1 (by rw [hP1, hc1]; rfl))
  iintro %s2 %hs2
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have e7 : s2.rd 7 = 1 := by rw [LPstep_rd hs2 7 (.inr rfl), LPstep_rd hs1 7 (.inr rfl), h7]
  have e8 : s2.rd 8 = Weak.Prom.Ref.Lit.Y := by rw [LPstep_rd hs2 8 (.inr rfl), LPstep_rd hs1 8 (.inr rfl), h8]
  -- `sd x7,(x8)`: release-class after `fence rw,w`, in place: THE DEPOSIT
  iapply (wpT_sd (sz := 8) (rs2 := 7) (rs1 := 8) (off := 0) hq2 (by rw [hP2, hc2]; rfl) (by rw [e8]; decide))
  inext
  iintro %σb %tf %σb' %hful %hmsg %_ %_ HX _
  have hbf : (((s2.rd 8 + 0) % two64 : Nat) : Int) = Y := by rw [e8]; decide
  rcases hful with ⟨hnr, _, _⟩ | ⟨_, hn, _, rfl, rfl⟩
  · exact absurd (relClass_fW _ _ _ _ _ rfl rfl rfl _ _ _ _) hnr
  have hMf : M[σb.n]? = some fMsg := by
    have := (take_msg hmsg).1
    rw [hbf, e7] at this
    simpa [fMsg] using this
  icases HX with ⟨%D, %rec, %f, %bad, %own1, %sp, Hxa, Hfa, Hba, %hok, Hdep⟩
  unfold hv
  ihave %e1 := ghost_var_agree γx _ _ _ _ $$ Hx Hxa
  ihave %e2 := ghost_var_agree γf _ _ _ _ $$ Hf Hfa
  obtain rfl := rec_inj e1
  obtain rfl := fl_inj e2
  obtain ⟨hlt, hok'⟩ := h0_f2 hok hMf
  rw [relPrG (fun t ht => (hok.1 0 t ht).2.1)]
  imod ghost_var_update_halves (MG.xr ⟨none, σb.n + 1, σa.n + 1, 42⟩) γx _ _ $$ Hx Hxa with ⟨Hx, Hxa⟩
  imod ghost_var_update_halves (MG.fl (some (σb.n + 1))) γf _ _ $$ Hf Hfa with ⟨Hf, Hfa⟩
  imodintro
  isplitl [Hx Hxa Hfa Hba]
  · iexists D, ⟨none, σb.n + 1, σa.n + 1, 42⟩, some (σb.n + 1), bad, own1, sp
    unfold hv
    iframe Hxa Hfa Hba
    isplitr
    · ipureintro; exact hok'
    · unfold depP
      ileft
      iexists σa.n + 1
      unfold hv
      iframe Hx
      ipureintro; exact ⟨hlt, by omega⟩
  iintro %s3 %hs3
  obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hP2 (by rw [hc2])
  iapply (h0_end M γx γf γb γc s3 _ (by rw [hP3, hc3]; exact Nat.le_refl _) hq3)

end h0

/-! ## 4. H1: `ld x5,(x6); fence r,rw; sd x9,(x8)` -/

/-- H1's knowledge after reading flag (register value `v5`): `x5 ≠ 1`; or a dead message was read; or H1 claimed
x's points-to (holder H1). -/
def K1 (γx γb : GName) (v5 : Nat) : IProp GF :=
  iprop((⌜v5 ≠ 1⌝ ∗ hv γb (.b3 false false false)) ∨ hv γb (.b3 true false false) ∨
    (∃ nc tsx, hv γx (.xr ⟨some 1, nc, tsx, 42⟩) ∗ hv γb (.b3 false false false)))

section h1

variable [InvGS_gen hlc GF] (M : List PMsg) (γx γf γb γc : GName)

theorem h1_end2 (s3 : LP) (ws : PState) (hP : s3.prog.length ≤ s3.pc) (hq : s3.q = []) :
    (∃ bad own1 sp, hv γb (.b3 bad own1 sp) ∗ ⌜s3.rd 5 ≠ 1 ∨ bad = true ∨ own1 = true⌝) ⊢
      wpT (hlc := hlc) (GF := GF) (Xm M γx γf γb γc) mp2Img M 1 s3 ws (fun _ => iprop(True)) := by
  iintro ⟨%bad', %own1', %sp', Hb, %hk⟩
  iapply (wpT_end hq hP)
  iintro %σ %_ HX
  icases HX with ⟨%D, %rec, %f, %bad, %own1, %sp, Hxa, Hfa, Hba, %hok, Hdep⟩
  unfold hv
  ihave %e := ghost_var_agree γb _ _ _ _ $$ Hb Hba
  obtain ⟨rfl, rfl, rfl⟩ := b3_inj e
  imodintro
  isplitl [Hxa Hfa Hba Hdep]
  · iexists D, rec, f, bad', own1', sp'
    unfold hv
    iframe
    ipureintro
    refine h1_fin2 hok ?_
    rw [rd_regs s3 5 (by omega)]
    exact hk
  · ipureintro; trivial

/-- H1's `sd x9,(x8)` (release-class after `fence r,rw`, in place), then the end. -/
theorem h1_st (s2 : LP) (ws1 : PState) (hw0 : ws1.wVwOld = 0)
    (hprog : s2.prog = [Weak.Prom.Ref.Lit.ld 5 6, Weak.Prom.Ref.Lit.fRRW, Weak.Prom.Ref.Lit.sd 9 8])
    (hpc : s2.pc = 2) (hq : s2.q = []) (h8 : s2.rd 8 = Weak.Prom.Ref.Lit.X) (h9 : s2.rd 9 = 2) :
    K1 γx γb (s2.rd 5) ⊢
      wpT (hlc := hlc) (GF := GF) (Xm M γx γf γb γc) mp2Img M 1 s2 (instrR (fencePost ws1 true false true true))
        (fun _ => iprop(True)) := by
  iintro H
  iapply (wpT_sd (sz := 8) (rs2 := 9) (rs1 := 8) (off := 0) hq (by rw [hprog, hpc]; rfl) (by rw [h8]; decide))
  inext
  iintro %σ %ts %σ' %hful %hmsg %_ %_ HX _
  have hb : (((s2.rd 8 + 0) % two64 : Nat) : Int) = X := by rw [h8]; decide
  rcases hful with ⟨hnr, _, _⟩ | ⟨_, hn, _, rfl, rfl⟩
  · exact absurd (relClass_fRW ws1 _ _ _ _ rfl rfl hw0 _ _ _ _) hnr
  have hM : M[σ.n]? = some x2Msg := by
    have := (take_msg hmsg).1
    rw [hb, h9] at this
    simpa [x2Msg] using this
  icases HX with ⟨%D, %rec, %f, %bad, %own1, %sp, Hxa, Hfa, Hba, %hok, Hdep⟩
  rw [relPrG (fun t ht => (hok.1 1 t ht).2.1)]
  unfold K1
  icases H with (⟨%hne, Hb⟩ | Hb | ⟨%nc, %tsx, Hx, Hb⟩)
  · -- not the holder (flag ≠ 1): x is spoiled
    unfold hv
    ihave %e := ghost_var_agree γb _ _ _ _ $$ Hb Hba
    obtain ⟨rfl, rfl, rfl⟩ := b3_inj e
    imod ghost_var_update_halves (MG.b3 false false true) γb _ _ $$ Hb Hba with ⟨Hb, Hba⟩
    imodintro
    isplitl [Hxa Hfa Hba Hdep]
    · iexists D, rec, f, false, false, true
      unfold hv
      iframe
      ipureintro; exact h1_st_spoil hok rfl hM
    iintro %s3 %hs3
    obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hprog (by rw [hpc])
    iapply (h1_end2 M γx γf γb γc s3 _ (by rw [hP3, hc3]; exact Nat.le_refl _) hq3)
    iexists false, false, true
    unfold hv
    iframe Hb
    ipureintro
    left; rw [LPstep_rd hs3 5 (.inr rfl)]; exact hne
  · -- a dead message was read: x is spoiled, `bad`
    unfold hv
    ihave %e := ghost_var_agree γb _ _ _ _ $$ Hb Hba
    obtain ⟨rfl, rfl, rfl⟩ := b3_inj e
    imod ghost_var_update_halves (MG.b3 true false true) γb _ _ $$ Hb Hba with ⟨Hb, Hba⟩
    imodintro
    isplitl [Hxa Hfa Hba Hdep]
    · iexists D, rec, f, true, false, true
      unfold hv
      iframe
      ipureintro; exact h1_st_spoil hok rfl hM
    iintro %s3 %hs3
    obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hprog (by rw [hpc])
    iapply (h1_end2 M γx γf γb γc s3 _ (by rw [hP3, hc3]; exact Nat.le_refl _) hq3)
    iexists true, false, true
    unfold hv
    iframe Hb
    ipureintro
    right; left; rfl
  · -- the holder writes: x's points-to now says 2, `own1`
    unfold hv
    ihave %e1 := ghost_var_agree γx _ _ _ _ $$ Hx Hxa
    obtain rfl := rec_inj e1
    ihave %e := ghost_var_agree γb _ _ _ _ $$ Hb Hba
    obtain ⟨rfl, rfl, rfl⟩ := b3_inj e
    imod ghost_var_update_halves (MG.xr ⟨some 1, nc, σ.n + 1, 2⟩) γx _ _ $$ Hx Hxa with ⟨Hx, Hxa⟩
    imod ghost_var_update_halves (MG.b3 false true false) γb _ _ $$ Hb Hba with ⟨Hb, Hba⟩
    imodintro
    isplitl [Hxa Hfa Hba Hdep]
    · iexists D, ⟨some 1, nc, σ.n + 1, 2⟩, f, false, true, false
      unfold hv
      iframe
      ipureintro; exact h1_st_own hok rfl hM
    iintro %s3 %hs3
    obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hprog (by rw [hpc])
    iapply (h1_end2 M γx γf γb γc s3 _ (by rw [hP3, hc3]; exact Nat.le_refl _) hq3)
    iexists false, true, false
    unfold hv
    iframe Hb
    ipureintro
    right; right; rfl

/-- **H1, the claimant and writer**: reads flag, CLAIMS x's points-to from the release cell (or meets the image or a
dead message), `fence r,rw`, then `h1_st`. -/
theorem mp2_h1 (hinv : invalFree M) (s0 : LP)
    (hprog : s0.prog = [Weak.Prom.Ref.Lit.ld 5 6, Weak.Prom.Ref.Lit.fRRW, Weak.Prom.Ref.Lit.sd 9 8])
    (hpc : s0.pc = 0) (hq : s0.q = []) (h6 : s0.rd 6 = Weak.Prom.Ref.Lit.Y) (h8 : s0.rd 8 = Weak.Prom.Ref.Lit.X)
    (h9 : s0.rd 9 = 2) (hlen : s0.regs.length = 32) :
    token γc ∗ hv γb (.b3 false false false) ⊢
      wpT (hlc := hlc) (GF := GF) (Xm M γx γf γb γc) mp2Img M 1 s0 psInit (fun _ => iprop(True)) := by
  iintro ⟨Htok, Hb⟩
  iapply (wpT_ld (sz := 8) (sgn := true) (rd := 5) (rs1 := 6) (off := 0) hq (by rw [hprog, hpc]; rfl)
    (by rw [h6]; decide))
  inext
  iintro %σ %tvs %hl8 %hlo HX _
  have hb : (((s0.rd 6 + 0) % two64 : Nat) : Int) = Y := by rw [h6]; decide
  rw [hb] at hlo ⊢
  obtain ⟨⟨t0, b0⟩, rest, rfl⟩ : ∃ tb r, tvs = tb :: r := by
    cases tvs with
    | nil => simp at hl8
    | cons tb r => exact ⟨tb, r, rfl⟩
  obtain ⟨hmb, htn, _⟩ := loadOk_byte (j := 0) hinv hlo rfl
  have cont : ∀ s1, LPstep s0 s1 (s0.pc + 1) 5 (ldVal true 8 ((t0, b0) :: rest)) →
      K1 (GF := GF) γx γb (val8 ((t0, b0) :: rest)) ⊢
      wpT (hlc := hlc) (GF := GF) (Xm M γx γf γb γc) mp2Img M 1 s1
        (PF.qPosts (loadRun psInit false false (srcsView psInit (srcR 6)) Y ((t0, b0) :: rest))
          (regWL 5 [.DLdRes] ++ [LInstr])) (fun _ => iprop(True)) := by
    intro s1 hs1
    obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
    have e5 : s1.rd 5 = val8 ((t0, b0) :: rest) := LPstep_rd_eq hs1 (by omega) (by omega)
    have hw0 : (PF.qPosts (loadRun psInit false false (srcsView psInit (srcR 6)) Y ((t0, b0) :: rest))
        (regWL 5 [.DLdRes] ++ [LInstr])).wVwOld = 0 := by
      simp [PF.qPosts, PF.qPost, regWL, PF.regWP, instrR, (PF.loadRun_mono psInit false false _ Y _).2.2.1, psInit]
    iintro H
    iapply (wpT_fence hq1 (by rw [hP1, hc1]; rfl))
    iintro %s2 %hs2
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
    iapply (h1_st M γx γf γb γc s2 _ hw0 hP2 hc2 hq2
      (by rw [LPstep_rd hs2 8 (.inr rfl), LPstep_rd hs1 8 (.inl (by omega)), h8])
      (by rw [LPstep_rd hs2 9 (.inr rfl), LPstep_rd hs1 9 (.inl (by omega)), h9]))
    rw [LPstep_rd hs2 5 (.inr rfl), e5]
    iexact H
  by_cases ht0 : t0 = 0
  · subst ht0
    have hb0 : b0 = 0 := by
      simp only [memByte, mp2Img_zero, Option.some.injEq] at hmb; exact hmb.symm
    imodintro
    iframe HX
    iintro %s1 %hs1
    iapply (cont s1 hs1)
    unfold K1
    ileft
    iframe Hb
    ipureintro
    intro h1; have := val8_b0 h1; rw [hb0] at this; exact absurd this (by decide)
  · icases HX with ⟨%D, %rec, %f, %bad, %own1, %sp, Hxa, Hfa, Hba, %hok, Hdep⟩
    have hwF : wrF M t0 := ⟨0, by omega, wrA_of_memByte (by omega) hmb⟩
    rcases hok.2.2.2.2.1 t0 (by omega) htn hwF with hD | hft
    · unfold hv
      ihave %e2 := ghost_var_agree γb _ _ _ _ $$ Hb Hba
      obtain ⟨rfl, rfl, rfl⟩ := b3_inj e2
      imod ghost_var_update_halves (MG.b3 true false false) γb _ _ $$ Hb Hba with ⟨Hb, Hba⟩
      imodintro
      isplitl [Hxa Hfa Hba Hdep]
      · iexists D, rec, f, true, false, false
        unfold hv
        iframe
        ipureintro; exact mp2Ok_setBad hok hD
      iintro %s1 %hs1
      iapply (cont s1 hs1)
      unfold K1
      iright; ileft
      unfold hv
      iexact Hb
    · subst hft
      unfold depP
      icases Hdep with (⟨%tsx, %htsx, Hxr⟩ | Htok')
      · unfold hv
        ihave %e1 := ghost_var_agree γx _ _ _ _ $$ Hxr Hxa
        obtain rfl := rec_inj e1
        ihave %e2 := ghost_var_agree γb _ _ _ _ $$ Hb Hba
        obtain ⟨rfl, rfl, rfl⟩ := b3_inj e2
        imod ghost_var_update_halves (MG.xr ⟨some 1, σ.n, tsx, 42⟩) γx _ _ $$ Hxr Hxa with ⟨Hxr, Hxa⟩
        imodintro
        isplitl [Hxa Hfa Hba Htok]
        · iexists D, ⟨some 1, σ.n, tsx, 42⟩, some t0, false, false, false
          unfold hv
          iframe Hxa Hfa Hba
          isplitr
          · ipureintro; exact h1_claim2 hok
          · unfold depP
            iright
            iexact Htok
        iintro %s1 %hs1
        iapply (cont s1 hs1)
        unfold K1
        iright; iright
        iexists σ.n, tsx
        unfold hv
        iframe Hxr Hb
      · iexfalso
        iapply token_exclusive γc
        iframe Htok Htok'

end h1

/-! ## 5. The agent obligation, the end, the verdict -/

section top

variable [InvGS_gen hlc GF] (M : List PMsg) (γx γf γb γc : GName)

theorem mp2_agent :
    ⊢ □ (∀ σ σ', ⌜agentStep (litOW mp2Img M) σ σ'⌝ -∗ Xm (GF := GF) M γx γf γb γc σ -∗
      |={⊤}=> Xm M γx γf γb γc σ') := by
  imodintro
  iintro %σ %σ' %ha HX
  icases HX with ⟨%D, %rec, %f, %bad, %own1, %sp, Hxa, Hfa, Hba, %hok, Hdep⟩
  obtain ⟨D', hok'⟩ := mp2Ok_agent hok ha
  imodintro
  iexists D', rec, f, bad, own1, sp
  iframe
  ipureintro; exact hok'

theorem mp2_final :
    ⊢ ∀ σ, ⌜σ.n = (litOW mp2Img M).M.length ∧ ∀ h, σ.pr h = ∅⌝ -∗ Xm (GF := GF) M γx γf γb γc σ -∗
      |={⊤,∅}=> ⌜∀ g, σ.done 1 = some g → (g[5]?).getD 0 = 1 → lastX2 mp2Img M⌝ := by
  iintro %σ %hfin HX
  icases HX with ⟨%D, %rec, %f, %bad, %own1, %sp, -, -, -, %hok, -⟩
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  ipureintro
  exact mp2Ok_final hok hfin.1 hfin.2

end top

def q0 : LP := ⟨mp2T.prog 0, 0, (List.range 32).map (fun r => ((([(5, 42), (6, Weak.Prom.Ref.Lit.X), (7, 1),
  (8, Weak.Prom.Ref.Lit.Y)] : List (Nat × Nat)).lookup r).getD 0) % two64), []⟩
def q1 : LP := ⟨mp2T.prog 1, 0, (List.range 32).map (fun r => ((([(6, Weak.Prom.Ref.Lit.Y), (8, Weak.Prom.Ref.Lit.X),
  (9, 2)] : List (Nat × Nat)).lookup r).getD 0) % two64), []⟩

theorem progs_mp2T : progs mp2T = [q0, q1] := rfl

/-- **G4 TARGET (2′) ON TRACK (b)**: in every valid machine-v2 run of `mp2T`, if H1 finished with `x5 = 1`, then H1's
`sd 2` is the last write to x in the final memory: x's points-to moved from H0 to H1 through flag's in-place release
and H1 wrote with it. -/
theorem g4_mp2 {evs : List PEvt} {cfg : PCfg LP Unit} (hvr : validRun litStep mp2Img () (progs mp2T) evs cfg)
    {g : List Nat} (hg : doneOf (litOW mp2Img cfg.pcLog) (progs mp2T).length cfg 1 = some g)
    (h5 : (g[5]?).getD 0 = 1) : lastX2 mp2Img cfg.pcLog := by
  have hps : ∀ p ∈ progs mp2T, p.q = [] := by
    rw [progs_mp2T]; intro p hp; simp at hp; rcases hp with rfl | rfl <;> rfl
  have hinv := lit_invalFree hvr hps
  have key := ownAdequacy (hlc := HasLC.hasLC) (GF := mp2GF) (w := litOW mp2Img cfg.pcLog) (ps := progs mp2T)
    (fun done => ∀ g, done 1 = some g → (g[5]?).getD 0 = 1 → lastX2 mp2Img cfg.pcLog) (fun {_} => by
      iintro
      imod ghost_var_alloc (MG.xr ⟨some 0, 0, 0, 0⟩) with ⟨%γx, Hx⟩
      imod ghost_var_alloc (MG.fl none) with ⟨%γf, Hf⟩
      imod ghost_var_alloc (MG.b3 false false false) with ⟨%γb, Hb⟩
      imod token_alloc with ⟨%γc, Htok⟩
      have s1 := ghost_var_split (GF := mp2GF) γx (MG.xr ⟨some 0, 0, 0, 0⟩) (1 : Qp).half (1 : Qp).half
      have s2 := ghost_var_split (GF := mp2GF) γf (MG.fl none) (1 : Qp).half (1 : Qp).half
      have s3 := ghost_var_split (GF := mp2GF) γb (MG.b3 false false false) (1 : Qp).half (1 : Qp).half
      rw [Qp.half_add_half] at s1 s2 s3
      ihave ⟨Hx1, Hx2⟩ := s1 $$ Hx
      ihave ⟨Hf1, Hf2⟩ := s2 $$ Hf
      ihave ⟨Hb1, Hb2⟩ := s3 $$ Hb
      imodintro
      iexists Xm cfg.pcLog γx γf γb γc
      isplitl [Hx1 Hf1 Hb1]
      · iexists (fun _ => False), ⟨some 0, 0, 0, 0⟩, none, false, false, false
        unfold hv depP
        iframe Hx1 Hf1 Hb1
        ipureintro; exact ⟨mp2Ok_init mp2Img_zero, trivial⟩
      isplitr
      · iapply mp2_agent
      isplitl [Hx2 Hf2 Hb2 Htok]
      · rw [progs_mp2T]
        simp only [hartsFrom]
        iapply BigSepL.bigSepL_cons.2
        isplitl [Hx2 Hf2]
        · ihave H := mp_h0 (hlc := HasLC.hasLC) cfg.pcLog γx γf γb γc q0 rfl rfl rfl (by decide) (by decide)
            (by decide) (by decide) $$ [Hx2 Hf2]
          · unfold hv; iframe Hx2 Hf2
          iapply H
        iapply BigSepL.bigSepL_cons.2
        isplitl [Hb2 Htok]
        · ihave H := mp2_h1 (hlc := HasLC.hasLC) cfg.pcLog γx γf γb γc hinv q1 rfl rfl rfl (by decide) (by decide)
            (by decide) (by decide) $$ [Hb2 Htok]
          · unfold hv; iframe Hb2 Htok
          iapply H
        exact BigSepL.bigSepL_nil_intro
      · iapply mp2_final) hvr rfl (lit_fetchBounded hvr hps) hinv
  exact key g hg h5

end Weak.Prom.Own.MP2
