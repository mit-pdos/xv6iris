/-
Weak/Prom: **G4 target (2), MP with ownership transfer, on track (b) through the REAL litmus program half** (stage
S4b part 2; plan rev 7 §4 "Gate G4" (2)).  Removes part 1's fidelity caveats for (2) (OwnMP.lean ran a label-level
program half with 1-byte accesses and image 0): here the program half is `litStep`, the accesses are the plan's
8-byte `sd`/`ld`, the image is the test's, and the verdict is about H1's final registers.

The proof is part 1's (OwnMP.lean header), instruction by instruction through the kit (OwnKit.lean):
* H0 `sd x5,(x6)` is its first write, so release-class (`vrOld = vwOld = 0`): appended in place, it becomes x's
  latest message (`h0_x`); `fence rw,w`; `sd x7,(x8)` is release-class (`relClass_fW`): appended in place, H0
  DEPOSITS x's points-to into flag's release cell (`h0_f`);
* H1 `ld x5,(x6)`: byte 0 of the flag answer is the image (value 0, so `x5 ≠ 1`), a dead message (`bad`), or the
  release, from which H1, the designated claimant, CLAIMS x's points-to (`h1_claim`); its view bound is the read's
  post-view `vrOld`; `fence r,rw` lifts it to the load floor `vrNew`; `ld x7,(x8)`: every byte is x's latest
  message's byte (`x7 = 42`) or a later, pending x-message (`bad`, `mpOk_markX`).
`g4_mpOwnL`: in EVERY valid machine-v2 run of `mpT`, if H1 finished with registers `g` then `g[5] = 1 → g[7] = 42`
(`g4_mpOwnL_regs`: stated on the final configuration).  Through `ownAdequacy` (NF_R) with PO-fetch (MachFix-R-b5: no `invalFree` premise)
discharged for every litmus test (OwnLitSide.lean).  0 named inputs; finite runs (prefix lemma S3d separate).
Also G4 (5) for this state interpretation (`g4_noDoubleClaimL`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnMPLDefs
import Weak.Prom.OwnLitSide
import Weak.Prom.CoreKitQ
import Iris.Instances.Lib.GhostVar
import Iris.Instances.Lib.Token
import Iris.Instances.Lib.WSat
import Iris.Instances.Lib.LaterCredits
import Iris.Algebra.Auth

namespace Weak.Prom.Own.MPL

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Mach Weak.Prom.Mach.Cert Weak.Prom.Own
open Weak.Prom.Own.MP (wrA au wrA_of_memByte)
open Weak.Prom.PF (LPstep LPstep_at LPstep_rd LPstep_rd_eq ldVal instrR)
open Weak.Prom.Ref (Instr Test two64)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. Ghost state -/

/-- The ghost-variable contents of the proof. -/
inductive MG where
  | xr (r : XRec)
  | fl (f : Option Nat)
  | bd (b : Bool)

section gf
open Iris COFE Auth HeapView

/-- The functor bundle: invariants (0–2), later credits (3), the ghost variables (4), the claim token (5). -/
noncomputable def mplGF : BundledGFunctors := fun n =>
  match n with
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF CoPsetDisjL, by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨GhostVarF MG, by infer_instance⟩
  | 5 => ⟨TokenF, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

instance : WsatGpreS mplGF where
  inv := { τ := 0, transp := by unfold mplGF; rfl }
  enabled := { τ := 1, transp := by unfold mplGF; rfl }
  disabled := { τ := 2, transp := by unfold mplGF; rfl }

instance : LcGpreS mplGF where
  lc_elem := { τ := 3, transp := by unfold mplGF; rfl }

instance : InvGpreS mplGF where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance

instance : GhostVarG mplGF MG where
  elemG := { τ := 4, transp := by unfold mplGF; rfl }

instance : TokenG mplGF where
  elemG := { τ := 5, transp := by unfold mplGF; rfl }

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
  iprop(∃ (D : Nat → Prop) (rec : XRec) (f : Option Nat) (bad : Bool),
    hv γx (.xr rec) ∗ hv γf (.fl f) ∗ hv γb (.bd bad) ∗ ⌜mpOk mpImg M σ D rec f bad⌝ ∗ depP γx γc f)

theorem rec_inj {a b : XRec} (h : MG.xr a = MG.xr b) : a = b := by cases h; rfl
theorem fl_inj {a b : Option Nat} (h : MG.fl a = MG.fl b) : a = b := by cases h; rfl
theorem bd_inj {a b : Bool} (h : MG.bd a = MG.bd b) : a = b := by cases h; rfl

/-! ## 2. Machine facts of the two harts -/

/-- A plain store directly after `fence rw,w` (and the instruction boundary) is release-class (plan §3). -/
theorem relClass_fW (ws : PState) (pr pw sr sw : Bool) (hpr : pr = true) (hpw : pw = true) (hsw : sw = true)
    (a : Int) (d : List (BitVec 8)) (asrc vsrc : List Dsrc) :
    relClass (instrR (fencePost ws pr pw sr sw)) (LStore false false a d asrc vsrc) := by
  subst hpr hpw hsw
  refine ⟨_, rfl, ?_⟩
  simp only [wrState, stPreA, stPre, fencePost, instrR, if_true, Bool.false_eq_true, if_false]
  omega

theorem fwdView_psInit (a : Int) (t : Nat) : fwdView psInit false a t = t := by
  simp [fwdView, psInit, lookupEmpty]

theorem rd_regs (s : LP) (r : Nat) (hr : r ≠ 0) : (s.regs[r]?).getD 0 = s.rd r := by
  simp [LP.rd, hr]

/-! ## 3. H0: `sd x5,(x6); fence rw,w; sd x7,(x8)` -/

section h0

variable [InvGS_gen hlc GF] (M : List PMsg) (γx γf γb γc : GName)

theorem h0_end (s3 : LP) (ws : PState) (hP : s3.prog.length ≤ s3.pc) (hq : s3.q = []) :
    ⊢ wpT (hlc := hlc) (GF := GF) (Xm M γx γf γb γc) mpImg M 0 s3 ws (fun _ => iprop(True)) := by
  iapply (wpT_end hq hP)
  iintro %σ %_ HX
  icases HX with ⟨%D, %rec, %f, %bad, Hxa, Hfa, Hba, %hok, Hdep⟩
  imodintro
  isplitl
  · iexists D, rec, f, bad
    iframe
    ipureintro; exact h0_fin hok
  · ipureintro; trivial

/-- **H0, the writer**: x's store in place, then the release in place with THE DEPOSIT. -/
theorem mp_h0 (s0 : LP)
    (hprog : s0.prog = [Weak.Prom.Ref.Lit.sd 5 6, Weak.Prom.Ref.Lit.fRWW, Weak.Prom.Ref.Lit.sd 7 8])
    (hpc : s0.pc = 0) (hq : s0.q = []) (h5 : s0.rd 5 = 42) (h6 : s0.rd 6 = Weak.Prom.Ref.Lit.X) (h7 : s0.rd 7 = 1)
    (h8 : s0.rd 8 = Weak.Prom.Ref.Lit.Y) :
    hv γx (.xr ⟨some 0, 0, 0, 0⟩) ∗ hv γf (.fl none) ⊢
      wpT (hlc := hlc) (GF := GF) (Xm M γx γf γb γc) mpImg M 0 s0 psInit (fun _ => iprop(True)) := by
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
  icases HX with ⟨%D, %rec, %f, %bad, Hxa, Hfa, Hba, %hok, Hdep⟩
  unfold hv
  ihave %e1 := ghost_var_agree γx _ _ _ _ $$ Hx Hxa
  ihave %e2 := ghost_var_agree γf _ _ _ _ $$ Hf Hfa
  obtain rfl := rec_inj e1
  obtain rfl := fl_inj e2
  rw [relPrG (fun t ht => (hok.1 0 t ht).2.1)]
  imod ghost_var_update_halves (MG.xr ⟨some 0, 0, σa.n + 1, 42⟩) γx _ _ $$ Hx Hxa with ⟨Hx, Hxa⟩
  imodintro
  isplitl [Hxa Hfa Hba Hdep]
  · iexists D, ⟨some 0, 0, σa.n + 1, 42⟩, none, bad
    unfold hv
    iframe Hxa Hfa Hba Hdep
    ipureintro; exact h0_x hok hM
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
  icases HX with ⟨%D, %rec, %f, %bad, Hxa, Hfa, Hba, %hok, Hdep⟩
  unfold hv
  ihave %e1 := ghost_var_agree γx _ _ _ _ $$ Hx Hxa
  ihave %e2 := ghost_var_agree γf _ _ _ _ $$ Hf Hfa
  obtain rfl := rec_inj e1
  obtain rfl := fl_inj e2
  obtain ⟨hlt, hok'⟩ := h0_f hok hMf
  rw [relPrG (fun t ht => (hok.1 0 t ht).2.1)]
  imod ghost_var_update_halves (MG.xr ⟨none, σb.n + 1, σa.n + 1, 42⟩) γx _ _ $$ Hx Hxa with ⟨Hx, Hxa⟩
  imod ghost_var_update_halves (MG.fl (some (σb.n + 1))) γf _ _ $$ Hf Hfa with ⟨Hf, Hfa⟩
  imodintro
  isplitl [Hx Hxa Hfa Hba]
  · iexists D, ⟨none, σb.n + 1, σa.n + 1, 42⟩, some (σb.n + 1), bad
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

/-! ## 4. H1: `ld x5,(x6); fence r,rw; ld x7,(x8)` -/

/-- H1's knowledge after reading flag (register value `v5`), with view bound `B`: `x5 ≠ 1`; or a dead message was
read; or H1 claimed x's points-to (holder H1) with its latest x-message `tsx ≤ B`. -/
def K1 (γx γb : GName) (v5 B : Nat) : IProp GF :=
  iprop((⌜v5 ≠ 1⌝ ∗ hv γb (.bd false)) ∨ hv γb (.bd true) ∨
    (∃ nc tsx, ⌜1 ≤ tsx ∧ tsx ≤ B⌝ ∗ hv γx (.xr ⟨some 1, nc, tsx, 42⟩) ∗ hv γb (.bd false)))

theorem K1_mono (γx γb : GName) (v5 : Nat) {B B' : Nat} (h : B ≤ B') :
    K1 (GF := GF) γx γb v5 B ⊢ K1 γx γb v5 B' := by
  unfold K1
  iintro (H | H | ⟨%nc, %tsx, %hk, Hx, Hb⟩)
  · ileft; iexact H
  · iright; ileft; iexact H
  · iright; iright
    iexists nc, tsx
    iframe Hx Hb
    ipureintro; exact ⟨hk.1, by omega⟩

section h1

variable [InvGS_gen hlc GF] (M : List PMsg) (γx γf γb γc : GName)

theorem h1_end (s3 : LP) (ws : PState) (hP : s3.prog.length ≤ s3.pc) (hq : s3.q = []) :
    (⌜s3.rd 5 = 1 → s3.rd 7 = 42⌝ ∗ hv γb (.bd false)) ∨ hv γb (.bd true) ⊢
      wpT (hlc := hlc) (GF := GF) (Xm M γx γf γb γc) mpImg M 1 s3 ws (fun _ => iprop(True)) := by
  iintro H
  iapply (wpT_end hq hP)
  iintro %σ %_ HX
  icases HX with ⟨%D, %rec, %f, %bad, Hxa, Hfa, Hba, %hok, Hdep⟩
  unfold hv
  icases H with (⟨%hsp, Hb⟩ | Hb)
  · imodintro
    isplitl
    · iexists D, rec, f, bad
      unfold hv
      iframe
      ipureintro
      refine h1_fin hok (.inl ?_)
      unfold mpSpec
      rw [rd_regs s3 5 (by omega), rd_regs s3 7 (by omega)]
      exact hsp
    · ipureintro; trivial
  · ihave %e := ghost_var_agree γb _ _ _ _ $$ Hb Hba
    obtain rfl := bd_inj e
    imodintro
    isplitl [Hxa Hfa Hba Hdep]
    · iexists D, rec, f, true
      unfold hv
      iframe
      ipureintro; exact h1_fin hok (.inr rfl)
    · ipureintro; trivial

/-- H1's `ld x7,(x8)` (then the end), from the knowledge after the fence. -/
theorem h1_x (hinv : invalFree M) (s2 : LP) (ws2 : PState)
    (hprog : s2.prog = [Weak.Prom.Ref.Lit.ld 5 6, Weak.Prom.Ref.Lit.fRRW, Weak.Prom.Ref.Lit.ld 7 8])
    (hpc : s2.pc = 2) (hq : s2.q = []) (h8 : s2.rd 8 = Weak.Prom.Ref.Lit.X) (hlen : s2.regs.length = 32) :
    K1 γx γb (s2.rd 5) ws2.wVrNew ⊢
      wpT (hlc := hlc) (GF := GF) (Xm M γx γf γb γc) mpImg M 1 s2 ws2 (fun _ => iprop(True)) := by
  iintro H
  iapply (wpT_ld (sz := 8) (sgn := true) (rd := 7) (rs1 := 8) (off := 0) hq (by rw [hprog, hpc]; rfl)
    (by rw [h8]; decide))
  inext
  iintro %σ %tvs %hl8 %hlo HX _
  have hb : (((s2.rd 8 + 0) % two64 : Nat) : Int) = X := by rw [h8]; decide
  rw [hb] at hlo ⊢
  have hpre : ws2.wVrNew ≤ ldPre ws2 false false (srcsView ws2 (srcR 8)) := (PF.ldPre_ge ws2 false false _).2.1
  unfold K1
  icases H with (⟨%hne, Hb⟩ | Hb | ⟨%nc, %tsx, %hk, Hx, Hb⟩)
  · imodintro
    iframe HX
    iintro %s3 %hs3
    obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hprog (by rw [hpc])
    iapply (h1_end M γx γf γb γc s3 _ (by rw [hP3, hc3]; exact Nat.le_refl _) hq3)
    ileft
    iframe Hb
    ipureintro
    intro h5
    rw [LPstep_rd hs3 5 (.inl (by omega))] at h5
    exact absurd h5 hne
  · imodintro
    iframe HX
    iintro %s3 %hs3
    obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hprog (by rw [hpc])
    iapply (h1_end M γx γf γb γc s3 _ (by rw [hP3, hc3]; exact Nat.le_refl _) hq3)
    iright
    iexact Hb
  · icases HX with ⟨%D, %rec, %f, %bad, Hxa, Hfa, Hba, %hok, Hdep⟩
    unfold hv
    ihave %e1 := ghost_var_agree γx _ _ _ _ $$ Hx Hxa
    obtain rfl := rec_inj e1
    obtain ⟨hk1, hk2⟩ := hk
    by_cases hex : ∃ j t b, j < 8 ∧ tvs[j]? = some (t, b) ∧ (toBytes 42 8)[j]? ≠ some b
    · -- some byte is not x's latest message's: it read a later, pending x-message — `bad`
      obtain ⟨j, t, b, hj, htb, hne⟩ := hex
      obtain ⟨hmb, htn, hnw⟩ := loadOk_byte hinv hlo htb
      rcases x_byte hok hk1 hj hmb htn (P := ldPre ws2 false false (srcsView ws2 (srcR 8))) (by simp only; omega)
          hnw with h | ⟨h1, h2⟩
      · exact absurd h hne
      obtain ⟨D', hok'⟩ := mpOk_markX hok h1 htn h2
      ihave %e2 := ghost_var_agree γb _ _ _ _ $$ Hb Hba
      obtain rfl := bd_inj e2
      imod ghost_var_update_halves (MG.bd true) γb _ _ $$ Hb Hba with ⟨Hb, Hba⟩
      imodintro
      isplitl [Hxa Hfa Hba Hdep]
      · iexists D', ⟨some 1, nc, tsx, 42⟩, f, true
        unfold hv
        iframe
        ipureintro; exact hok'
      iintro %s3 %hs3
      obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hprog (by rw [hpc])
      iapply (h1_end M γx γf γb γc s3 _ (by rw [hP3, hc3]; exact Nat.le_refl _) hq3)
      iright
      unfold hv
      iexact Hb
    · -- every byte is x's latest message's: `x7 = 42`
      have hall : tvs.map Prod.snd = toBytes 42 8 :=
        map_snd_of (by rw [hl8]; rfl) (fun j hj t b htb =>
          Classical.byContradiction fun hne => hex ⟨j, t, b, by simpa [toBytes, Weak.Prom.Ref.byteList] using hj,
            htb, hne⟩)
      imodintro
      isplitl [Hxa Hfa Hba Hdep]
      · iexists D, ⟨some 1, nc, tsx, 42⟩, f, bad
        unfold hv
        iframe
        ipureintro; exact hok
      iintro %s3 %hs3
      obtain ⟨hP3, hc3, hq3⟩ := LPstep_at hs3 hprog (by rw [hpc])
      iapply (h1_end M γx γf γb γc s3 _ (by rw [hP3, hc3]; exact Nat.le_refl _) hq3)
      ileft
      unfold hv
      iframe Hb
      ipureintro
      intro _
      rw [LPstep_rd_eq hs3 (by omega) (by omega)]
      exact val8_42 hall

/-- **H1, the claimant**: reads flag, CLAIMS x's points-to from the release cell (or meets the image or a dead
message), `fence r,rw`, then `h1_x`. -/
theorem mp_h1 (hinv : invalFree M) (s0 : LP)
    (hprog : s0.prog = [Weak.Prom.Ref.Lit.ld 5 6, Weak.Prom.Ref.Lit.fRRW, Weak.Prom.Ref.Lit.ld 7 8])
    (hpc : s0.pc = 0) (hq : s0.q = []) (h6 : s0.rd 6 = Weak.Prom.Ref.Lit.Y) (h8 : s0.rd 8 = Weak.Prom.Ref.Lit.X)
    (hlen : s0.regs.length = 32) :
    token γc ∗ hv γb (.bd false) ⊢
      wpT (hlc := hlc) (GF := GF) (Xm M γx γf γb γc) mpImg M 1 s0 psInit (fun _ => iprop(True)) := by
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
  have hvr : t0 ≤ (loadRun psInit false false (srcsView psInit (srcR 6)) Y ((t0, b0) :: rest)).wVrOld := by
    have := (PF.loadRun_b0 psInit false false (srcsView psInit (srcR 6)) Y t0 b0 rest).2.1
    rw [fwdView_psInit] at this; omega
  -- the rest of the hart from the knowledge `K1` with the read's post-view as bound
  have cont : ∀ s1, LPstep s0 s1 (s0.pc + 1) 5 (ldVal true 8 ((t0, b0) :: rest)) →
      K1 (GF := GF) γx γb (val8 ((t0, b0) :: rest))
        (loadRun psInit false false (srcsView psInit (srcR 6)) Y ((t0, b0) :: rest)).wVrOld ⊢
      wpT (hlc := hlc) (GF := GF) (Xm M γx γf γb γc) mpImg M 1 s1
        (PF.qPosts (loadRun psInit false false (srcsView psInit (srcR 6)) Y ((t0, b0) :: rest))
          (regWL 5 [.DLdRes] ++ [LInstr])) (fun _ => iprop(True)) := by
    intro s1 hs1
    obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
    have e5 : s1.rd 5 = val8 ((t0, b0) :: rest) := LPstep_rd_eq hs1 (by omega) (by omega)
    iintro H
    iapply (wpT_fence hq1 (by rw [hP1, hc1]; rfl))
    iintro %s2 %hs2
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
    have hB : (loadRun psInit false false (srcsView psInit (srcR 6)) Y ((t0, b0) :: rest)).wVrOld ≤
        (instrR (fencePost (PF.qPosts (loadRun psInit false false (srcsView psInit (srcR 6)) Y ((t0, b0) :: rest))
          (regWL 5 [.DLdRes] ++ [LInstr])) true false true true)).wVrNew := by
      simp [PF.qPosts, PF.qPost, regWL, PF.regWP, instrR, fencePost]
    iapply (h1_x M γx γf γb γc hinv s2 (instrR (fencePost (PF.qPosts (loadRun psInit false false
      (srcsView psInit (srcR 6)) Y ((t0, b0) :: rest)) (regWL 5 [.DLdRes] ++ [LInstr])) true false true true))
      hP2 hc2 hq2
      (by rw [LPstep_rd hs2 8 (.inr rfl), LPstep_rd hs1 8 (.inl (by omega)), h8])
      (by rw [hs2.2.2.2.1, hs1.2.2.2.1, hlen]))
    rw [LPstep_rd hs2 5 (.inr rfl), e5]
    iapply (K1_mono γx γb _ hB)
    iexact H
  by_cases ht0 : t0 = 0
  · -- flag read from the image: value 0, so `x5 ≠ 1`
    subst ht0
    have hb0 : b0 = 0 := by
      simp only [memByte, mpImg_zero, Option.some.injEq] at hmb; exact hmb.symm
    imodintro
    iframe HX
    iintro %s1 %hs1
    iapply (cont s1 hs1)
    unfold K1
    ileft
    iframe Hb
    ipureintro
    intro h1; have := val8_b0 h1; rw [hb0] at this; exact absurd this (by decide)
  · icases HX with ⟨%D, %rec, %f, %bad, Hxa, Hfa, Hba, %hok, Hdep⟩
    have hwF : wrF M t0 := ⟨0, by omega, wrA_of_memByte (by omega) hmb⟩
    rcases hok.2.2.2.2.1 t0 (by omega) htn hwF with hD | hft
    · -- a dead flag message: `bad`
      unfold hv
      ihave %e2 := ghost_var_agree γb _ _ _ _ $$ Hb Hba
      obtain rfl := bd_inj e2
      imod ghost_var_update_halves (MG.bd true) γb _ _ $$ Hb Hba with ⟨Hb, Hba⟩
      imodintro
      isplitl [Hxa Hfa Hba Hdep]
      · iexists D, rec, f, true
        unfold hv
        iframe
        ipureintro; exact mpOk_setBad hok hD
      iintro %s1 %hs1
      iapply (cont s1 hs1)
      unfold K1
      iright; ileft
      unfold hv
      iexact Hb
    · -- the release: CLAIM x's points-to
      subst hft
      unfold depP
      icases Hdep with (⟨%tsx, %htsx, Hxr⟩ | Htok')
      · unfold hv
        ihave %e1 := ghost_var_agree γx _ _ _ _ $$ Hxr Hxa
        obtain rfl := rec_inj e1
        imod ghost_var_update_halves (MG.xr ⟨some 1, σ.n, tsx, 42⟩) γx _ _ $$ Hxr Hxa with ⟨Hxr, Hxa⟩
        imodintro
        isplitl [Hxa Hfa Hba Htok]
        · iexists D, ⟨some 1, σ.n, tsx, 42⟩, some t0, bad
          unfold hv
          iframe Hxa Hfa Hba
          isplitr
          · ipureintro; exact h1_claim hok
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
        ipureintro
        exact ⟨htsx.2, by omega⟩
      · iexfalso
        iapply token_exclusive γc
        iframe Htok Htok'

end h1

/-! ## 5. The agent obligation, the start and the end -/

section top

variable [InvGS_gen hlc GF] (M : List PMsg) (γx γf γb γc : GName)

theorem mp_agent :
    ⊢ □ (∀ σ σ', ⌜agentStep (litOW mpImg M) σ σ'⌝ -∗ Xm (GF := GF) M γx γf γb γc σ -∗
      |={⊤}=> Xm M γx γf γb γc σ') := by
  imodintro
  iintro %σ %σ' %ha HX
  icases HX with ⟨%D, %rec, %f, %bad, Hxa, Hfa, Hba, %hok, Hdep⟩
  obtain ⟨D', hok'⟩ := mpOk_agent hok ha
  imodintro
  iexists D', rec, f, bad
  iframe
  ipureintro; exact hok'

theorem mp_final :
    ⊢ ∀ σ, ⌜σ.n = (litOW mpImg M).M.length ∧ ∀ h, σ.pr h = ∅⌝ -∗ Xm (GF := GF) M γx γf γb γc σ -∗
      |={⊤,∅}=> ⌜∀ g, σ.done 1 = some g → mpSpec g⌝ := by
  iintro %σ %hfin HX
  icases HX with ⟨%D, %rec, %f, %bad, -, -, -, %hok, -⟩
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  ipureintro
  exact mpOk_final hok hfin.2

end top

/-! ## 6. G4 target (2) -/

/-- H0's initial program state. -/
def p0 : LP := ⟨mpT.prog 0, 0, (List.range 32).map (fun r => ((([(5, 42), (6, Weak.Prom.Ref.Lit.X), (7, 1),
  (8, Weak.Prom.Ref.Lit.Y)] : List (Nat × Nat)).lookup r).getD 0) % two64), []⟩
/-- H1's initial program state. -/
def p1 : LP := ⟨mpT.prog 1, 0, (List.range 32).map (fun r => ((([(6, Weak.Prom.Ref.Lit.Y), (8, Weak.Prom.Ref.Lit.X)] :
  List (Nat × Nat)).lookup r).getD 0) % two64), []⟩

theorem progs_mpT : progs mpT = [p0, p1] := rfl

/-- **G4 TARGET (2) ON TRACK (b), REAL FRONT END.**  In every valid machine-v2 run of `mpT` (litmus program half,
8-byte accesses, the test's image), if H1 finished with registers `g`, then `g[5] = 1 → g[7] = 42`.  Proved in
track (b)'s logic: x's points-to moves from H0 to H1 through flag's in-place release (header). -/
theorem g4_mpOwnL {evs : List PEvt} {cfg : PCfg LP Unit} (hvr : validRun litStep mpImg () (progs mpT) evs cfg)
    {g : List Nat} (hg : doneOf (litOW mpImg cfg.pcLog) (progs mpT).length cfg 1 = some g) : mpSpec g := by
  have hps : ∀ p ∈ progs mpT, p.q = [] := by
    rw [progs_mpT]; intro p hp; simp at hp; rcases hp with rfl | rfl <;> rfl
  have hinv := lit_invalFree hvr hps
  have key := ownAdequacy (hlc := HasLC.hasLC) (GF := mplGF) (w := litOW mpImg cfg.pcLog) (ps := progs mpT)
    (fun done => ∀ g, done 1 = some g → mpSpec g) (fun {_} => by
      iintro
      imod ghost_var_alloc (MG.xr ⟨some 0, 0, 0, 0⟩) with ⟨%γx, Hx⟩
      imod ghost_var_alloc (MG.fl none) with ⟨%γf, Hf⟩
      imod ghost_var_alloc (MG.bd false) with ⟨%γb, Hb⟩
      imod token_alloc with ⟨%γc, Htok⟩
      have s1 := ghost_var_split (GF := mplGF) γx (MG.xr ⟨some 0, 0, 0, 0⟩) (1 : Qp).half (1 : Qp).half
      have s2 := ghost_var_split (GF := mplGF) γf (MG.fl none) (1 : Qp).half (1 : Qp).half
      have s3 := ghost_var_split (GF := mplGF) γb (MG.bd false) (1 : Qp).half (1 : Qp).half
      rw [Qp.half_add_half] at s1 s2 s3
      ihave ⟨Hx1, Hx2⟩ := s1 $$ Hx
      ihave ⟨Hf1, Hf2⟩ := s2 $$ Hf
      ihave ⟨Hb1, Hb2⟩ := s3 $$ Hb
      imodintro
      iexists Xm cfg.pcLog γx γf γb γc
      isplitl [Hx1 Hf1 Hb1]
      · iexists (fun _ => False), ⟨some 0, 0, 0, 0⟩, none, false
        unfold hv depP
        iframe Hx1 Hf1 Hb1
        ipureintro; exact ⟨mpOk_init mpImg_zero, trivial⟩
      isplitr
      · iapply mp_agent
      isplitl [Hx2 Hf2 Hb2 Htok]
      · rw [progs_mpT]
        simp only [hartsFrom]
        iapply BigSepL.bigSepL_cons.2
        isplitl [Hx2 Hf2]
        · ihave H := mp_h0 (hlc := HasLC.hasLC) cfg.pcLog γx γf γb γc p0 rfl rfl rfl (by decide) (by decide)
            (by decide) (by decide) $$ [Hx2 Hf2]
          · unfold hv; iframe Hx2 Hf2
          iapply H
        iapply BigSepL.bigSepL_cons.2
        isplitl [Hb2 Htok]
        · ihave H := mp_h1 (hlc := HasLC.hasLC) cfg.pcLog γx γf γb γc hinv p1 rfl rfl rfl (by decide) (by decide)
            (by decide) $$ [Hb2 Htok]
          · unfold hv; iframe Hb2 Htok
          iapply H
        exact BigSepL.bigSepL_nil_intro
      · iapply mp_final) hvr rfl (lit_fetchBounded hvr hps)   -- MachFix-R-b5: `ownAdequacy` has no `invalFree` premise
  exact key g hg

/-- **G4 (2), on the final configuration**: in every valid run of `mpT`, if H1 ran its whole program, its final
`x5 = 1` implies its final `x7 = 42`. -/
theorem g4_mpOwnL_regs {evs : List PEvt} {cfg : PCfg LP Unit} (hvr : validRun litStep mpImg () (progs mpT) evs cfg)
    {ag : PAgent LP} (hag : cfg.pcAgs[1]? = some ag) (hd : ag.paSt.q = [] ∧ ag.paSt.prog.length ≤ ag.paSt.pc) :
    ag.paSt.rd 5 = 1 → ag.paSt.rd 7 = 42 := by
  have h := g4_mpOwnL hvr (g := ag.paSt.regs) (by
    simp only [doneOf, show (1 : Nat) < (progs mpT).length by rw [progs_mpT]; decide, if_true, hag,
      Option.bind_some]
    exact litDoneR_end hd.1 hd.2)
  unfold mpSpec at h
  rw [rd_regs _ 5 (by omega), rd_regs _ 7 (by omega)] at h
  exact h

/-! ## 7. G4 target (5) for this state interpretation -/

section neg

variable [InvGS_gen hlc GF]

/-- Three halves of one ghost variable are contradictory. -/
theorem hv_three (γ : GName) (a b c : MG) : hv (GF := GF) γ a ∗ hv γ b ∗ hv γ c ⊢ False := by
  unfold hv
  iintro ⟨H1, H2, H3⟩
  ihave %e := ghost_var_agree γ _ _ _ _ $$ H1 H2
  subst e
  ihave H12 := (Fractional.fractional (Φ := fun q : Qp => ghost_var (GF := GF) γ (.own q) a)
    (1 : Qp).half (1 : Qp).half).2 $$ [H1 H2]
  · iframe H1 H2
  rw [Qp.half_add_half]
  ihave %hv := ghost_var_valid_2 γ _ _ _ _ $$ H12 H3
  exact absurd (DFrac.valid_own_op hv.1) (by simp)

/-- **G4 TARGET (5) ON TRACK (b), REAL FRONT END**: besides the state interpretation's own half, at most ONE thread
holds a half of x's ghost variable — two plain readers of flag's release cannot both obtain x's points-to. -/
theorem g4_noDoubleClaimL (M : List PMsg) (γx γf γb γc : GName) (σ : OSt (List Nat)) (a b : MG) :
    Xm (GF := GF) M γx γf γb γc σ ∗ hv γx a ∗ hv γx b ⊢ False := by
  iintro ⟨HX, Ha, Hb⟩
  icases HX with ⟨%D, %rec, %f, %bad, Hxa, -, -, -, -⟩
  iapply hv_three γx
  iframe Hxa Ha Hb

end neg

end Weak.Prom.Own.MPL
