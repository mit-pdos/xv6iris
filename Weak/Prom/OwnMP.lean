/-
Weak/Prom: **G4 target (2), MP with ownership transfer, proved on track (b)** (stage S4b; plan rev 7 §4 "Gate G4"
(2): "MP with ownership transfer (`sd x; fence rw,w; sd flag` / `ld flag; fence r,rw; ld x`), proving that x's
points-to moves").

The ownership state interpretation `Xmp` (OwnMPDefs.lean `mpOk` + ghost state):
* x's POINTS-TO is the half `hv γx (rec ⟨hold, tstart, tstar, v⟩)` of a ghost variable whose other half is in `Xmp`;
  the holder H0 starts with it (`some 0`); H0's store `st x 1` updates it (plan §4 "Points-to (b)": the latest
  x-message in the prefix is the holder's, every later one is backed or dead);
* H0's `st flag 1` after `fence rw,w` is release-class, so it is appended IN PLACE (`hstepO.rel`) and at that very
  step H0 DEPOSITS its points-to (with holder `none`) into flag's release cell `depP` inside `Xmp` — no reader can
  have read the flag message before (plan §4 "releases in place");
* H1, the designated claimant (it owns the claim token `γc`), reads the flag message: it is the cell's release, or
  dead; from the release it TAKES the points-to and becomes the holder (`h1_claim`): the points-to has MOVED;
* H1's `ld x` after `fence r,rw` then returns the latest x-message (value 1) or a dead / non-fulfillable message,
  which sets `bad`; at the end of a valid run no message is dead (`mpOk_final`).
`g4_mpOwn`: in every valid run of the test (machine v2), if H1 finished then H1 read flag = 1 ⇒ x = 1.  Through
`ownAdequacy` (OwnWp.lean) and the NF_R lemma; PO-fetch discharged for the program (it fetches nothing).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnMPDefs
import Iris.Instances.Lib.GhostVar
import Iris.Instances.Lib.Token
import Iris.Instances.Lib.WSat
import Iris.Instances.Lib.LaterCredits
import Iris.Algebra.Auth

namespace Weak.Prom.Own.MP

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Own
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
noncomputable def mpGF : BundledGFunctors := fun n =>
  match n with
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF CoPsetDisjL, by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨GhostVarF MG, by infer_instance⟩
  | 5 => ⟨TokenF, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

instance : WsatGpreS mpGF where
  inv := { τ := 0, transp := by unfold mpGF; rfl }
  enabled := { τ := 1, transp := by unfold mpGF; rfl }
  disabled := { τ := 2, transp := by unfold mpGF; rfl }

instance : LcGpreS mpGF where
  lc_elem := { τ := 3, transp := by unfold mpGF; rfl }

instance : InvGpreS mpGF where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance

instance : GhostVarG mpGF MG where
  elemG := { τ := 4, transp := by unfold mpGF; rfl }

instance : TokenG mpGF where
  elemG := { τ := 5, transp := by unfold mpGF; rfl }

end gf

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF MG] [TokenG GF]

/-- One half of a ghost variable. -/
def hv (γ : GName) (m : MG) : IProp GF := ghost_var γ (.own (1 : Qp).half) m

/-- FLAG'S RELEASE CELL: after the release `r`, x's points-to (holder `none`) or, once claimed, the claim token. -/
def depP (γx γc : GName) : Option Nat → IProp GF
  | none => iprop(True)
  | some r => iprop((∃ tsx, ⌜tsx < r ∧ 1 ≤ tsx⌝ ∗ hv γx (.xr ⟨none, r, tsx, 1⟩)) ∨ token γc)

/-- THE OWNERSHIP STATE INTERPRETATION of the proof. -/
abbrev Xmp (M : List PMsg) (γx γf γb γc : GName) (σ : OSt (List (BitVec 8))) : IProp GF :=
  iprop(∃ (D : Nat → Prop) (rec : XRec) (f : Option Nat) (bad : Bool),
    hv γx (.xr rec) ∗ hv γf (.fl f) ∗ hv γb (.bd bad) ∗ ⌜mpOk mpImg M σ D rec f bad⌝ ∗ depP γx γc f)

theorem rec_inj {a b : XRec} (h : MG.xr a = MG.xr b) : a = b := by cases h; rfl
theorem fl_inj {a b : Option Nat} (h : MG.fl a = MG.fl b) : a = b := by cases h; rfl
theorem bd_inj {a b : Bool} (h : MG.bd a = MG.bd b) : a = b := by cases h; rfl

theorem hstep_nil {M : List PMsg} {h : Nat} {σ σ' : OSt (List (BitVec 8))} {g : List (BitVec 8)}
    {ws ws' : PState} {l : PLabel} {ots : Option Nat} {s' : TP}
    (hs : hstepO (mpW M) h σ ⟨[], g⟩ ws l ots s' ws' σ') : False := by
  cases hs with
  | plain => rename_i _ _ hp _; exact tp_nil hp
  | rel => rename_i _ _ _ _ hp _; exact tp_nil hp

theorem tsx_pos {M : List PMsg} {t : Nat} (h : memByte mpImg M t X = some 1) : 1 ≤ t := by
  rcases Nat.eq_zero_or_pos t with e | e
  · subst e; simp [memByte, mpImg] at h
  · exact e

theorem mpOk_setBad {img : Image} {M : List PMsg} {σ : OSt (List (BitVec 8))} {D : Nat → Prop} {rec : XRec}
    {f : Option Nat} {bad : Bool} {t : Nat} (hok : mpOk img M σ D rec f bad) (ht : D t) :
    mpOk img M σ D rec f true := by
  obtain ⟨hpr, hD, _, hx, hdis, hcell, hf, _⟩ := hok
  exact ⟨hpr, hD, fun _ => ⟨t, ht⟩, hx, hdis, hcell, hf, fun _ _ => .inr rfl⟩

theorem fwdView_psInit (a : Int) (t : Nat) : fwdView psInit false a t = t := by
  simp [fwdView, psInit, lookupEmpty]

/-! ## 2. H0: `st x 1; fence rw,w; st flag 1` -/

section h0

variable [InvGS_gen hlc GF] (M : List PMsg) (γx γf γb γc : GName)

theorem h0_p3 (ws : PState) (τ : List (PLabel × Option Nat)) :
    ⊢ wpO (hlc := hlc) (GF := GF) (Xmp M γx γf γb γc) (.hart (mpW M) 0 ⟨[], []⟩ ws τ) (fun _ => iprop(True)) := by
  iapply wpO_hart_lift
  inext
  isplit
  · iintro %v %σ %hd %_ HX
    icases HX with ⟨%D, %rec, %f, %bad, Hxa, Hfa, Hba, %hok, Hdep⟩
    imodintro
    isplitl
    · iexists D, rec, f, bad
      iframe
      ipureintro
      exact h0_fin hok
    · ipureintro; trivial
  · iintro %σ %l %ots %s' %ws' %σ' %hs
    exact absurd hs (fun h => hstep_nil h)

theorem h0_p2 (ws1 : PState) (τ : List (PLabel × Option Nat)) (tsx : Nat) :
    hv γx (.xr ⟨some 0, 0, tsx, 1⟩) ∗ hv γf (.fl none) ⊢
      wpO (hlc := hlc) (GF := GF) (Xmp M γx γf γb γc)
        (.hart (mpW M) 0 ⟨[.st F 1], []⟩ (fencePost ws1 true true false true) τ) (fun _ => iprop(True)) := by
  iintro ⟨Hx, Hf⟩
  iapply wpO_hart_lift
  inext
  isplit
  · iintro %v %σ %hd
    simp [mpW, tpDone] at hd
  · iintro %σ %l %ots %s' %ws' %σ' %hs HX _
    icases HX with ⟨%D, %rec, %f, %bad, Hxa, Hfa, Hba, %hok, Hdep⟩
    unfold hv
    ihave %e1 := ghost_var_agree γx _ _ _ _ $$ Hx Hxa
    ihave %e2 := ghost_var_agree γf _ _ _ _ $$ Hf Hfa
    obtain rfl := rec_inj e1
    obtain rfl := fl_inj e2
    have htsx : 1 ≤ tsx := tsx_pos hok.2.2.2.1.2.1
    obtain ⟨rfl, r, rfl, hlt, hok'⟩ := h0_st2 hok hs
    imod ghost_var_update_halves (MG.xr ⟨none, r, tsx, 1⟩) γx _ _ $$ Hx Hxa with ⟨Hx, Hxa⟩
    imod ghost_var_update_halves (MG.fl (some r)) γf _ _ $$ Hf Hfa with ⟨Hf, Hfa⟩
    imodintro
    isplitl [Hx Hxa Hfa Hba]
    · iexists D, ⟨none, r, tsx, 1⟩, some r, bad
      unfold hv
      iframe Hxa Hfa Hba
      isplitr
      · ipureintro; exact hok'
      · unfold depP
        ileft
        iexists tsx
        unfold hv
        iframe Hx
        ipureintro; exact ⟨hlt, htsx⟩
    · iapply h0_p3

theorem h0_p1 (ws1 : PState) (τ : List (PLabel × Option Nat)) (tsx : Nat) :
    hv γx (.xr ⟨some 0, 0, tsx, 1⟩) ∗ hv γf (.fl none) ⊢
      wpO (hlc := hlc) (GF := GF) (Xmp M γx γf γb γc)
        (.hart (mpW M) 0 ⟨[.fence true true false true, .st F 1], []⟩ ws1 τ) (fun _ => iprop(True)) := by
  iintro H
  iapply wpO_hart_lift
  inext
  isplit
  · iintro %v %σ %hd
    simp [mpW, tpDone] at hd
  · iintro %σ %l %ots %s' %ws' %σ' %hs HX _
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hstep_fence rfl hs
    imodintro
    iframe HX
    iapply h0_p2
    iexact H

theorem h0_wp :
    hv γx (.xr ⟨some 0, 0, 0, 0⟩) ∗ hv γf (.fl none) ⊢
      wpO (hlc := hlc) (GF := GF) (Xmp M γx γf γb γc) (.hart (mpW M) 0 ⟨h0Code, []⟩ psInit []) (fun _ => iprop(True)) := by
  iintro ⟨Hx, Hf⟩
  iapply wpO_hart_lift
  inext
  isplit
  · iintro %v %σ %hd
    simp [mpW, tpDone, h0Code] at hd
  · iintro %σ %l %ots %s' %ws' %σ' %hs HX _
    icases HX with ⟨%D, %rec, %f, %bad, Hxa, Hfa, Hba, %hok, Hdep⟩
    unfold hv
    ihave %e1 := ghost_var_agree γx _ _ _ _ $$ Hx Hxa
    ihave %e2 := ghost_var_agree γf _ _ _ _ $$ Hf Hfa
    obtain rfl := rec_inj e1
    obtain rfl := fl_inj e2
    obtain ⟨rfl, ts, rfl, hok'⟩ := h0_st1 hok hs
    imod ghost_var_update_halves (MG.xr ⟨some 0, 0, ts, 1⟩) γx _ _ $$ Hx Hxa with ⟨Hx, Hxa⟩
    imodintro
    isplitl [Hxa Hfa Hba Hdep]
    · iexists D, ⟨some 0, 0, ts, 1⟩, none, bad
      unfold hv
      iframe Hxa Hfa Hba Hdep
      ipureintro; exact hok'
    · iapply h0_p1
      unfold hv
      iframe Hx Hf

end h0

/-! ## 3. H1: `ld flag; fence r,rw; ld x` -/

/-- H1's knowledge after reading flag (value `v1`), with view bound `B`: flag was not 1; or a dead message was read;
or H1 claimed x's points-to (holder H1) with `tstar ≤ B`. -/
def K1 (γx γb : GName) (v1 : BitVec 8) (B : Nat) : IProp GF :=
  iprop((⌜v1 ≠ 1⌝ ∗ hv γb (.bd false)) ∨ hv γb (.bd true) ∨
    (∃ nc tsx, ⌜1 ≤ tsx ∧ tsx ≤ B ∧ v1 = 1⌝ ∗ hv γx (.xr ⟨some 1, nc, tsx, 1⟩) ∗ hv γb (.bd false)))


section h1

variable [InvGS_gen hlc GF] (M : List PMsg) (γx γf γb γc : GName)

theorem h1_p3 (ws : PState) (τ : List (PLabel × Option Nat)) (g : List (BitVec 8)) :
    (⌜mpSpec g⌝ ∗ hv γb (.bd false)) ∨ hv γb (.bd true) ⊢
      wpO (hlc := hlc) (GF := GF) (Xmp M γx γf γb γc) (.hart (mpW M) 1 ⟨[], g⟩ ws τ) (fun _ => iprop(True)) := by
  iintro H
  iapply wpO_hart_lift
  inext
  isplit
  · iintro %v %σ %hd %_ HX
    simp only [mpW, tpDone, if_true, Option.some.injEq] at hd
    subst hd
    icases HX with ⟨%D, %rec, %f, %bad, Hxa, Hfa, Hba, %hok, Hdep⟩
    unfold hv
    icases H with (⟨%hsp, Hb⟩ | Hb)
    · imodintro
      isplitl
      · iexists D, rec, f, bad
        unfold hv
        iframe
        ipureintro; exact h1_fin hok (.inl hsp)
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
  · iintro %σ %l %ots %s' %ws' %σ' %hs
    exact absurd hs (fun h => hstep_nil h)

theorem h1_p2 (hinv : invalFree M) (ws2 : PState) (τ : List (PLabel × Option Nat)) (v1 : BitVec 8) :
    K1 γx γb v1 ws2.wVrNew ⊢
      wpO (hlc := hlc) (GF := GF) (Xmp M γx γf γb γc) (.hart (mpW M) 1 ⟨[.ld X], [v1]⟩ ws2 τ)
        (fun _ => iprop(True)) := by
  iintro H
  iapply wpO_hart_lift
  inext
  isplit
  · iintro %v %σ %hd
    simp [mpW, tpDone] at hd
  · iintro %σ %l %ots %s' %ws' %σ' %hs HX _
    obtain ⟨t, v, rfl, rfl, rfl, rfl, hmb, htn, hnw, _⟩ := hstep_ld rfl hinv hs
    have hpre : ws2.wVrNew ≤ ldPre ws2 false false 0 := by simp only [ldPre]; omega
    unfold K1
    icases H with (⟨%hne, Hb⟩ | Hb | ⟨%nc, %tsx, %hk, Hx, Hb⟩)
    · imodintro
      iframe HX
      iapply h1_p3
      ileft
      iframe Hb
      ipureintro
      intro h0; simp at h0; exact absurd h0 hne
    · imodintro
      iframe HX
      iapply h1_p3
      iright
      iexact Hb
    · icases HX with ⟨%D, %rec, %f, %bad, Hxa, Hfa, Hba, %hok, Hdep⟩
      unfold hv
      ihave %e1 := ghost_var_agree γx _ _ _ _ $$ Hx Hxa
      obtain rfl := rec_inj e1
      obtain ⟨hk1, hk2, hk3⟩ := hk
      rcases h1_rdx hok hk1 hmb htn (P := ldPre ws2 false false 0) (by omega) hnw with hv1 | ⟨D', hok'⟩
      · imodintro
        isplitl [Hxa Hfa Hba Hdep]
        · iexists D, ⟨some 1, nc, tsx, 1⟩, f, bad
          unfold hv
          iframe
          ipureintro; exact hok
        · iapply h1_p3
          ileft
          unfold hv
          iframe Hb
          ipureintro
          intro _; simp [hv1]
      · ihave %e2 := ghost_var_agree γb _ _ _ _ $$ Hb Hba
        obtain rfl := bd_inj e2
        imod ghost_var_update_halves (MG.bd true) γb _ _ $$ Hb Hba with ⟨Hb, Hba⟩
        imodintro
        isplitl [Hxa Hfa Hba Hdep]
        · iexists D', ⟨some 1, nc, tsx, 1⟩, f, true
          unfold hv
          iframe
          ipureintro; exact hok'
        · iapply h1_p3
          iright
          unfold hv
          iexact Hb

theorem h1_p1 (hinv : invalFree M) (ws1 : PState) (τ : List (PLabel × Option Nat)) (v1 : BitVec 8) :
    K1 γx γb v1 ws1.wVrOld ⊢
      wpO (hlc := hlc) (GF := GF) (Xmp M γx γf γb γc)
        (.hart (mpW M) 1 ⟨[.fence true false true true, .ld X], [v1]⟩ ws1 τ) (fun _ => iprop(True)) := by
  iintro H
  iapply wpO_hart_lift
  inext
  isplit
  · iintro %v %σ %hd
    simp [mpW, tpDone] at hd
  · iintro %σ %l %ots %s' %ws' %σ' %hs HX _
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hstep_fence rfl hs
    imodintro
    iframe HX
    iapply h1_p2 (hinv := hinv)
    have hb : ws1.wVrOld ≤ (fencePost ws1 true false true true).wVrNew := by
      simp only [fencePost, if_true, if_false, Bool.false_eq_true]; omega
    unfold K1
    icases H with (H | H | ⟨%nc, %tsx, %hk, Hx, Hb⟩)
    · ileft; iexact H
    · iright; ileft; iexact H
    · iright; iright
      iexists nc, tsx
      iframe Hx Hb
      ipureintro
      exact ⟨hk.1, by omega, hk.2.2⟩

theorem h1_wp (hinv : invalFree M) :
    token γc ∗ hv γb (.bd false) ⊢
      wpO (hlc := hlc) (GF := GF) (Xmp M γx γf γb γc) (.hart (mpW M) 1 ⟨h1Code, []⟩ psInit []) (fun _ => iprop(True)) := by
  iintro ⟨Htok, Hb⟩
  iapply wpO_hart_lift
  inext
  isplit
  · iintro %v %σ %hd
    simp [mpW, tpDone, h1Code] at hd
  · iintro %σ %l %ots %s' %ws' %σ' %hs HX _
    obtain ⟨t, v, rfl, rfl, rfl, rfl, hmb, htn, _, hfv⟩ := hstep_ld rfl hinv hs
    rw [fwdView_psInit] at hfv
    rcases Nat.eq_zero_or_pos t with ht0 | ht0
    · -- flag read from the image: value 0
      subst ht0
      have hv0 : v = 0 := by simp [mpW, memByte, mpImg] at hmb; exact hmb.symm
      imodintro
      iframe HX
      simp only [List.nil_append]
      iapply h1_p1 (hinv := hinv)
      unfold K1
      ileft
      iframe Hb
      ipureintro
      rw [hv0]; decide
    · icases HX with ⟨%D, %rec, %f, %bad, Hxa, Hfa, Hba, %hok, Hdep⟩
      have hwF : wrA M t F := wrA_of_memByte ht0 hmb
      rcases hok.2.2.2.2.2.1 t ht0 htn hwF with hD | hft
      · -- a dead flag message
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
        · simp only [List.nil_append]
          iapply h1_p1 (hinv := hinv)
          unfold K1
          iright; ileft
          unfold hv
          iexact Hb
      · -- the release: CLAIM x's points-to
        subst hft
        obtain ⟨_, _, hmsg⟩ := hok.2.2.2.2.2.2.1 t rfl
        have hv1 : v = 1 := by
          have : memByte mpImg M t F = some 1 := by
            cases t with
            | zero => omega
            | succ k =>
              have hk : M[k]? = some ⟨F, [1], some 0, .plain⟩ := by simpa using hmsg
              simp [memByte, hk, PMsg.byteAt, F]
          exact memByte_inj hmb this
        unfold depP
        icases Hdep with (⟨%tsx, %htsx, Hxr⟩ | Htok')
        · unfold hv
          ihave %e1 := ghost_var_agree γx _ _ _ _ $$ Hxr Hxa
          obtain rfl := rec_inj e1
          imod ghost_var_update_halves (MG.xr ⟨some 1, σ'.n, tsx, 1⟩) γx _ _ $$ Hxr Hxa with ⟨Hxr, Hxa⟩
          imodintro
          isplitl [Hxa Hfa Hba Htok]
          · iexists D, ⟨some 1, σ'.n, tsx, 1⟩, some t, bad
            unfold hv
            iframe Hxa Hfa Hba
            isplitr
            · ipureintro; exact h1_claim hok
            · unfold depP
              iright
              iexact Htok
          · simp only [List.nil_append]
            iapply h1_p1 (hinv := hinv)
            unfold K1
            iright; iright
            iexists σ'.n, tsx
            unfold hv
            iframe Hxr Hb
            ipureintro
            exact ⟨htsx.2, by omega, hv1⟩
        · iexfalso
          iapply token_exclusive γc
          iframe Htok Htok'

end h1

/-! ## 4. The agent obligation, the start and the end -/

section top

variable [InvGS_gen hlc GF] (M : List PMsg) (γx γf γb γc : GName)

theorem mp_agent :
    ⊢ □ (∀ σ σ', ⌜agentStep (mpW M) σ σ'⌝ -∗ Xmp (GF := GF) M γx γf γb γc σ -∗ |={⊤}=> Xmp M γx γf γb γc σ') := by
  imodintro
  iintro %σ %σ' %ha HX
  icases HX with ⟨%D, %rec, %f, %bad, Hxa, Hfa, Hba, %hok, Hdep⟩
  obtain ⟨D', hok'⟩ := mpOk_agent hok ha
  imodintro
  iexists D', rec, f, bad
  iframe
  ipureintro; exact hok'

theorem mp_final :
    ⊢ ∀ σ, ⌜σ.n = (mpW M).M.length ∧ ∀ h, σ.pr h = ∅⌝ -∗ Xmp (GF := GF) M γx γf γb γc σ -∗
      |={⊤,∅}=> ⌜∀ g, σ.done 1 = some g → mpSpec g⌝ := by
  unfold Xmp
  iintro %σ %hfin HX
  icases HX with ⟨%D, %rec, %f, %bad, -, -, -, %hok, -⟩
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  ipureintro
  exact mpOk_final hok hfin.2

theorem Xmp_intro {D : Nat → Prop} {rec : XRec} {f : Option Nat} {bad : Bool} {σ : OSt (List (BitVec 8))}
    (hok : mpOk mpImg M σ D rec f bad) :
    hv γx (.xr rec) ∗ hv γf (.fl f) ∗ hv γb (.bd bad) ∗ depP γx γc f ⊢ Xmp (GF := GF) M γx γf γb γc σ := by
  unfold Xmp
  iintro ⟨H1, H2, H3, H4⟩
  iexists D, rec, f, bad
  iframe
  ipureintro; exact hok

theorem mpOk_init : mpOk mpImg M σ0 (fun _ => False) ⟨some 0, 0, 0, 0⟩ none false := by
  refine ⟨fun a t ht => absurd ht notElemOfEmpty, fun t ht => False.elim ht, fun h => (by cases h),
    ⟨Nat.le_refl _, rfl, Nat.le_refl _, fun t h1 h2 _ => (by simp [σ0] at h2; omega)⟩,
    fun t ht => False.elim ht, fun t h1 h2 _ => (by simp [σ0] at h2; omega), fun r hr => (by cases hr),
    fun g hg => (by simp [σ0] at hg)⟩

end top

/-! ## 5. The machine-level side conditions -/

theorem solo_tp {M : List PMsg} {h : Nat} :
    ∀ {x y : TP × PState × GSet Nat} {τ : List (PLabel × Option Nat)},
      soloSteps tpStep mpImg M h x τ y → ∀ e ∈ τ, ∃ s s', tpNext s e.1 = some s' := by
  intro x y τ hs
  induction hs with
  | refl => intro e he; cases he
  | step x l ots p' ws' prom' tr y hp _ _ ih =>
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨_, _, hp⟩
    · exact ih e he

theorem tpNext_fetch {s s' : TP} {b : Int} {tvs : List (Nat × BitVec 8)} (h : tpNext s (LIFetch b tvs) = some s') :
    False := by
  unfold tpNext at h; split at h <;> simp_all

theorem tpNext_write {s s' : TP} {l : PLabel} (h : tpNext s l = some s') :
    ∀ ws, wrPre ws l ≠ none → ∃ a d, l = LStore false false a d [] [] := by
  intro ws hw
  unfold tpNext at h
  split at h
  · split at h
    · rename_i hh; obtain ⟨h1, h2, _, _, h5, h6⟩ := hh; subst h1 h2 h5 h6; exact ⟨_, _, rfl⟩
    · cases h
  · exact absurd rfl hw
  · exact absurd rfl hw
  · cases h

theorem mp_fetch {evs : List PEvt} {cfg : PCfg TP Unit} (hv : validRun tpStep mpImg () mpProgs evs cfg) :
    fetchBounded tpStep mpImg mpProgs cfg.pcLog evs := by
  apply fetchBounded_ofImg
  intro hh e he base tvs hl
  rcases Nat.lt_or_ge hh 2 with hlt | hge
  · obtain ⟨ag, _, P0, _, hs⟩ := validRun_solo hv hh _ (List.getElem?_eq_getElem (by simpa [mpProgs] using hlt))
    obtain ⟨s, s', hn⟩ := solo_tp hs e he
    rw [hl] at hn
    exact (tpNext_fetch hn).elim
  · rw [PF.validRun_traceNone hv (List.getElem?_eq_none (by simpa [mpProgs] using hge))] at he
    cases he

theorem mp_invalFree {evs : List PEvt} {cfg : PCfg TP Unit} (hv : validRun tpStep mpImg () mpProgs evs cfg) :
    invalFree cfg.pcLog := by
  intro t a hc
  obtain ⟨m, k, len, hm, hcls, _⟩ := hc
  have hm1 : cfg.pcLog[(t - 1 + 1) - 1]? = some m := by simpa using hm
  have hwf := pmSteps_wf hv.1 (pmInit_wf mpImg () mpProgs)
  obtain ⟨_, i, hti, hil⟩ := hwf.2 m (List.mem_of_getElem? hm)
  rw [PF.validRun_len hv] at hil
  obtain ⟨ag, hag, P0, hP0, hs⟩ := validRun_solo hv i _ (List.getElem?_eq_getElem hil)
  have hin : t - 1 + 1 ∈ P0 := (hP0 _).2 ⟨by omega, m, hm1, hti⟩
  have hout : t - 1 + 1 ∉ ag.paProm := by rw [hv.2 i ag hag]; exact notElemOfEmpty
  obtain ⟨z, _, l, p', ws', prom', _, hp, hmm⟩ := solo_fulfil hs hin hout
  obtain ⟨a', d', rfl⟩ := tpNext_write hp z.2.1 (by
    obtain ⟨pv, hpv, _⟩ := (memStep_write hmm).1; rw [hpv]; simp)
  cases hmm with
  | store _ _ _ _ _ _ _ _ hmsg _ _ =>
    rw [hm1] at hmsg; cases hmsg; simp [stClass] at hcls

/-! ## 6. G4 target (2) -/

/-- **G4 TARGET (2) ON TRACK (b): MP WITH OWNERSHIP TRANSFER.**  In every valid run of machine v2 of
`H0 = st x 1; fence rw,w; st flag 1` ‖ `H1 = ld flag; fence r,rw; ld x` (bytes, image 0), if H1 finished with
answers `g`, then `g[0] = 1 → g[1] = 1`.  Proved in track (b)'s logic: x's points-to moves from H0 to H1 through
flag's in-place release (OwnMP.lean header). -/
theorem g4_mpOwn {evs : List PEvt} {cfg : PCfg TP Unit} (hvr : validRun tpStep mpImg () mpProgs evs cfg)
    {g : List (BitVec 8)} (hg : doneOf (mpW cfg.pcLog) mpProgs.length cfg 1 = some g) : mpSpec g := by
  have key := ownAdequacy (hlc := HasLC.hasLC) (GF := mpGF) (w := mpW cfg.pcLog) (ps := mpProgs)
    (fun done => ∀ g, done 1 = some g → mpSpec g) (fun {_} => by
      iintro
      imod ghost_var_alloc (MG.xr ⟨some 0, 0, 0, 0⟩) with ⟨%γx, Hx⟩
      imod ghost_var_alloc (MG.fl none) with ⟨%γf, Hf⟩
      imod ghost_var_alloc (MG.bd false) with ⟨%γb, Hb⟩
      imod token_alloc with ⟨%γc, Htok⟩
      have s1 := ghost_var_split (GF := mpGF) γx (MG.xr ⟨some 0, 0, 0, 0⟩) (1 : Qp).half (1 : Qp).half
      have s2 := ghost_var_split (GF := mpGF) γf (MG.fl none) (1 : Qp).half (1 : Qp).half
      have s3 := ghost_var_split (GF := mpGF) γb (MG.bd false) (1 : Qp).half (1 : Qp).half
      rw [Qp.half_add_half] at s1 s2 s3
      ihave ⟨Hx1, Hx2⟩ := s1 $$ Hx
      ihave ⟨Hf1, Hf2⟩ := s2 $$ Hf
      ihave ⟨Hb1, Hb2⟩ := s3 $$ Hb
      imodintro
      iexists Xmp cfg.pcLog γx γf γb γc
      isplitl [Hx1 Hf1 Hb1]
      · iapply Xmp_intro (hok := mpOk_init (M := cfg.pcLog))
        unfold hv depP
        iframe Hx1 Hf1 Hb1
      isplitr
      · iapply mp_agent
      isplitl [Hx2 Hf2 Hb2 Htok]
      · simp only [hartsFrom, mpProgs]
        iapply BigSepL.bigSepL_cons.2
        isplitl [Hx2 Hf2]
        · iapply h0_wp
          unfold hv
          iframe Hx2 Hf2
        iapply BigSepL.bigSepL_cons.2
        isplitl [Hb2 Htok]
        · iapply h1_wp (hinv := mp_invalFree hvr)
          unfold hv
          iframe Hb2 Htok
        exact BigSepL.bigSepL_nil_intro
      · iapply mp_final) hvr rfl (mp_fetch hvr) (mp_invalFree hvr)
  exact key g hg


/-! ## 7. G4 target (5): the deposit is claimed at most once -/

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

/-- **G4 TARGET (5) ON TRACK (b)**: two plain readers of flag's release cannot both obtain the exclusive deposit
`R` (x's points-to): in every state, besides the state interpretation's own half, at most ONE thread holds a half of
x's ghost variable — so a second claim is impossible.  (A reader obtains `R` only by swapping in the unique claim
token `γc`, `token_exclusive`; and, unlike track (a), no reader can read the release before its deposit, because the
release is appended in place, plan §4.) -/
theorem g4_noDoubleClaim (M : List PMsg) (γx γf γb γc : GName) (σ : OSt (List (BitVec 8))) (a b : MG) :
    Xmp (GF := GF) M γx γf γb γc σ ∗ hv γx a ∗ hv γx b ⊢ False := by
  iintro ⟨HX, Ha, Hb⟩
  icases HX with ⟨%D, %rec, %f, %bad, Hxa, -, -, -, -⟩
  iapply hv_three γx
  iframe Hxa Ha Hb

end neg

end Weak.Prom.Own.MP
