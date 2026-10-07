/-
Weak: **constraint B at the X level: every X leaf gets an INTERRUPT ARM, and the ABSORBING
composition (the WPd twin of the SC tier's `WpIntrInv.wp_exec_step_intr`).**

Rocq: `iris/AxIntr4.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 `TrapK i cpu ctrlOk Φ rs`: the interrupt continuation — "from the trap-entry state
(`TrapPost`: PC = stvecBase(stvec), sepc = pc, mstatus = trapMs elp ms, scause = interrupt
cause, stval = 0, priv = S, GPRs unchanged, regime holds at SIE = 0), the handler's WPd".
`XGprWriteI`: `AxReuseProbe2.XGprWrite` with the continuation `C ∧ TrapK` (∧, not ∗: exactly one
of the two arms runs, so both may share the caller's resources).  `XGprWriteIHolds`: from
`SpineOkI` + the bridge's instance premises.  `XGprWriteSI`: AT THE SIE-AGNOSTIC S-MODE REGIME
(the `AxSpineOk8.XGprWriteS` twin; premises identical).  `XGprWriteIOff`: when SIE = 0 at the
boundary, `TrapK` is free (the SIE = 0 statement is recovered).
§2 THE ABSORBING ENGINE.  `intrAbsorbD`: the persistent handler contract (the
`IntrDefs.intr_handler_spec` analogue): from ANY trap-entry state, given (under ▷) the WPd of
the interrupted code at any `Resumed` state (regime, PC = the interrupted pc, same GPRs), the
handler's WPd.  `XGprWriteAbsorb`: `intrAbsorbD` + the plain continuation `C` ⊢ WPd — by Löb
over the boundary register file, so an ARBITRARY number of back-to-back interrupts is absorbed;
the client never sees the trap arm.
§3 CONTROL: `XCtlΦI` / `XCtlΦIHolds` (the `AxSymCtl2.XCtlΦ` twin, compressed text),
`ctlRegimeSI`, and the c.ret leaf `XCretSI` at the SIE-agnostic S-mode regime (+
`XCretSIAbsorb`).

## Deviations from Rocq

1. All of `AxIntr3`/`AxSymCtl2`/`AxReuseProbe2`'s spelling deviations (`register_lookup r rs`
   ↦ `rs r`, `seip_reg` ↦ `AxRunClose.pinReg`, `gpr r rs` ↦ `uxaXget rs r`, `Z.eqb (uint r)
   (uint rd)` ↦ `r = rd`, `set_reg … (R_bitvector_64 (gpr_of_Z (uint rd)))` ↦ `ExecSt.setGpr rd`,
   `add_vec_int pc (if is_rvc then 2 else 4)` ↦ `pc + instrLen is_rvc` (as `XGprWrite`),
   `zeros' 12` ↦ `zeros (n := 12)`, `zero_extend' 5 'b"00"` ↦ `zero_extend (m := 5) 0b00#2`).
2. `Resumed`'s GPR clause `∀ z, register_lookup (R_bitvector_64 (gpr_of_Z z)) rs' = … rs` ↦
   `∀ z : BitVec 5, uxaXget rs' z = uxaXget rs z` (as `TrapPost`, `AxIntr3` deviation 2); the
   absorbing lemmas' `Hg0` premises likewise.
3. O2 STAGE C (as `AxSymEngine3`/`AxSymCtl2` deviation 1, `AxSpineOk8` deviation 4): the
   section premise `Hloc` is DROPPED everywhere; the remaining premises are `Htext Hflow`.
4. The invariant instance is `InvGS_gen hlc GF` for any `hlc` (Rocq `HasNoLc`), as
   `AxSpineOk5`/`AxSymCtl2`.  Section variables are explicit arguments (each declaration takes
   those it uses); the `CO`/`TX` notations are unfolded.
5. The satp premises take `AxIntr3.spineOkIS`'s shapes (`8#4`, `zero_extend (m := 16)
   (satp_to_asid satp0) = 0#16`, `BitVec.setWidth 44 (satp_to_ppn satp0) = T.base`).
6. `ctlRegimeSI` replays `AxSymCtl2.ctlRegimeS` (`execCurrentlyEnabledZca`, `cEZicfilpFalseS`;
   Rocq `vm_compute` ↦ `decide`).

**Rocq → Lean name map.**  `TrapPost_agree` `trapPostAgree`, `Resumed` `Resumed`, `TrapK`
`TrapK`, `X_gpr_write_I` `XGprWriteI`, `intr_absorb_d` `intrAbsorbD`, `X_gpr_write_I_holds`
`XGprWriteIHolds`, `X_gpr_write_I_off` `XGprWriteIOff`, `X_gpr_write_SI` `XGprWriteSI`,
`X_gpr_write_absorb_gen` `XGprWriteAbsorbGen`, `X_gpr_write_absorb` `XGprWriteAbsorb`,
`X_ctlΦ_I` `XCtlΦI`, `X_ctlΦ_I_holds` `XCtlΦIHolds`, `ctl_regime_SI` `ctlRegimeSI`, `X_ctl_SI`
`XCtlSI`, `X_cret_SI` `XCretSI`, `X_cret_SI_absorb_gen` `XCretSIAbsorbGen`, `X_cret_SI_absorb`
`XCretSIAbsorb`.  None is in the duplicated-name table.  Lean-only: none.

**Dropped:** the Ltac `nseipI` (`AxSymEngine2.notPin` instead).  Rocq 17 definitions/lemmas +
1 Ltac; Lean 17.  **Not ported:** the `Print Assumptions` lines (the lint's axiom check covers
them).
-/
import Weak.AxIntr3

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `TrapPost_agree`: `TrapPost` at the boundary file the bridge hands back (agrees off the
pins). -/
theorem trapPostAgree (ctrlOk : RegFile → Prop) (rs a b : RegFile) :
    (∀ x y, ctrlOk x → regsAgree AxRunClose.pinReg y x → ctrlOk y) →
    TrapPost ctrlOk rs a → regsAgree AxRunClose.pinReg b a → TrapPost ctrlOk rs b := by
  rintro Hs ⟨Hon, Hc, ip, H1, H2, H3, H4, H5, H6, H7⟩ Hag
  refine ⟨Hon, Hs _ _ Hc Hag, ip, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))]; exact H1
  · rw [Hag .sepc (AxSymEngine2.notPin _ (by decide) (by decide))]; exact H2
  · rw [Hag .mstatus (AxSymEngine2.notPin _ (by decide) (by decide))]; exact H3
  · rw [Hag .scause (AxSymEngine2.notPin _ (by decide) (by decide))]; exact H4
  · rw [Hag .stval (AxSymEngine2.notPin _ (by decide) (by decide))]; exact H5
  · rw [Hag .cur_privilege (AxSymEngine2.notPin _ (by decide) (by decide))]; exact H6
  · intro z; rw [AxSymEngine2.uxaXgetAgree _ _ Hag z]; exact H7 z

/-- Rocq `Resumed` (deviation 2). -/
def Resumed (ctrlOk : RegFile → Prop) (rs rs' : RegFile) : Prop :=
  ctrlOk rs' ∧ rs' .PC = rs .PC ∧ ∀ z : BitVec 5, uxaXget rs' z = uxaXget rs z

section defs
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- Rocq `TrapK`: the interrupt continuation. -/
def TrapK (i : Agent) (cpu : CPU) (ctrlOk : RegFile → Prop) (Φ : Athread → IProp GF)
    (rs : RegFile) : IProp GF :=
  iprop(∀ (s' : Athread) (rs' : RegFile) (k' : Nat),
    ⌜RetX cpu rs' k' s'⌝ -∗ ⌜TrapPost ctrlOk rs rs'⌝ -∗ wpd .MaybeStuck i s' Φ)

/-- Rocq `X_gpr_write_I`: the GPR-write X, SIE-agnostic (`AxReuseProbe2.XGprWrite` + the
interrupt arm). -/
def XGprWriteI (i : Agent) (cpu : CPU) (ctrlOk : RegFile → Prop)
    (textOk : BitVec 64 → Bool → instruction → Prop) : Prop :=
  ∀ (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (ins : instruction) (rd : BitVec 5) (wval : BitVec 64),
    RetX cpu rs k s → ctrlOk rs → rs .PC = pc →
    textOk pc is_rvc ins → rd.toNat ≠ 0 →
    (∀ s_pc : ExecSt,
       s_pc.regs .nextPC = pc + instrLen is_rvc →
       gprAgree s_pc.regs rs →
       exec (execute ins) s_pc = some (RETIRE_SUCCESS, s_pc.setGpr rd wval)) →
    ⊢ ((∀ (s' : Athread) (rs' : RegFile) (k' : Nat),
         ⌜RetX cpu rs' k' s'⌝ -∗ ⌜ctrlOk rs'⌝ -∗
         ⌜rs' .PC = pc + instrLen is_rvc⌝ -∗
         ⌜∀ r : BitVec 5, r.toNat ≠ 0 →
            uxaXget rs' r = if r = rd then wval else uxaXget rs r⌝ -∗
         wpd .MaybeStuck i s' (Φ0 (GF := GF)))
       ∧ TrapK i cpu ctrlOk (Φ0 (GF := GF)) rs) -∗
      wpd .MaybeStuck i s (Φ0 (GF := GF))

/-- Rocq `intr_absorb_d`: the persistent handler contract. -/
def intrAbsorbD (i : Agent) (cpu : CPU) (ctrlOk : RegFile → Prop) (Φ : Athread → IProp GF) :
    IProp GF :=
  iprop(□ ∀ (rs : RegFile) (s' : Athread) (rs' : RegFile) (k' : Nat),
    ⌜RetX cpu rs' k' s'⌝ -∗ ⌜TrapPost ctrlOk rs rs'⌝ -∗
    ▷ (∀ (s'' : Athread) (rs'' : RegFile) (k'' : Nat),
        ⌜RetX cpu rs'' k'' s''⌝ -∗ ⌜Resumed ctrlOk rs rs''⌝ -∗ wpd .MaybeStuck i s'' Φ) -∗
    wpd .MaybeStuck i s' Φ)

end defs

/-! # 1. X_gpr_write with the interrupt arm -/

section xI
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (img : Image) (i : Agent) (cpu : CPU)
variable (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
variable (Hsp : SpineOkI img ctrlOk textAt)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)

include Hsp Htext Hflow in
/-- Rocq `X_gpr_write_I_holds`. -/
theorem XGprWriteIHolds : XGprWriteI (GF := GF) i cpu ctrlOk (textOkD img ctrlOk textAt) := by
  unfold XGprWriteI
  intro s rs k pc is_rvc ins rd wval HRet Hctrl HPC Htx Hrd Hcert
  have e : is_rvc = true := Htx.1
  subst e
  iintro C
  iapply (wpdInstrOfEvA img i Φ0 cpu (postLiftingΦ0 i) Htext Hflow
    (fun _ t' => Good ctrlOk rs pc rd wval t'.regs ∨ TrapPost ctrlOk rs t'.regs) rs k s HRet
    (spineCertI img ctrlOk textAt Hsp rs pc ins rd wval Hctrl HPC Htx Hrd
      (fun s_pc h1 h2 => Hcert s_pc h1 h2)))
  iintro %t' %rs' %ib' %k' %HG %Hag
  have HRet' : RetX cpu rs' k' ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ :=
    ⟨ib', rfl, rfl, rfl, rfl, rfl, regsAgreeRefl _ _⟩
  rcases HG with ⟨Hc, Hpc, Hg⟩ | HT
  · have Hc' : ctrlOk rs' := Hsp.spiSeip _ _ Hc Hag
    have Hpc' : rs' .PC = pc + instrLen true :=
      (Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))).trans Hpc
    have Hg' : ∀ r : BitVec 5, r.toNat ≠ 0 →
        uxaXget rs' r = if r = rd then wval else uxaXget rs r :=
      fun r Hr => (AxSymEngine2.uxaXgetAgree _ _ Hag r).trans (Hg r Hr)
    icases C with ⟨C, -⟩
    iapply C $$ %_ %rs' %k' %HRet' %Hc' %Hpc' %Hg'
  · have HT' : TrapPost ctrlOk rs rs' :=
      trapPostAgree ctrlOk rs _ _ (fun x y hx hy => Hsp.spiSeip x y hx hy) HT Hag
    icases C with ⟨-, T⟩
    unfold TrapK
    iapply T $$ %_ %rs' %k' %HRet' %HT'

end xI

/-- Rocq `X_gpr_write_I_off`: at SIE = 0 the interrupt arm is free. -/
theorem XGprWriteIOff {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF]
    [Axpol] (i : Agent) (cpu : CPU) (ctrlOk : RegFile → Prop) (Φ : Athread → IProp GF)
    (rs : RegFile) :
    ¬ intrOn rs → ⊢ TrapK i cpu ctrlOk Φ rs := by
  intro Hoff
  unfold TrapK
  iintro %s' %rs' %k' %_ %HT
  exact (trapPostOff ctrlOk rs rs' Hoff HT).elim

/-- Rocq `X_gpr_write_SI`: AT THE SIE-AGNOSTIC S-MODE REGIME (deviations 3–5). -/
theorem XGprWriteSI {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF]
    [Axpol] (σi : ExecSt) (T : PTree) (satp0 : BitVec 64) (i : Agent) (cpu : CPU)
    (Hm : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (Ha : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (Hp : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (Htext : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i (imgS σi)⌝)
    (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
      (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
         imgBytes (imgS σi) base n = some vs) →
      AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k) :
    XGprWriteI (GF := GF) i cpu (ctrlOkSI T satp0)
      (textOkD (imgS σi) (ctrlOkSI T satp0) (textAtS σi T)) :=
  XGprWriteIHolds (imgS σi) i cpu _ _ (spineOkIS σi T satp0 Hm Ha Hp) Htext Hflow

/-! # 2. The absorbing engine -/

section absorb
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (i : Agent) (cpu : CPU) (ctrlOk : RegFile → Prop)
  (textOk : BitVec 64 → Bool → instruction → Prop)
variable (HX : XGprWriteI (GF := GF) i cpu ctrlOk textOk)

include HX in
/-- Rocq `X_gpr_write_absorb_gen`: the Löb core — any boundary file `rs` with the GPRs / PC of
`rs0`. -/
theorem XGprWriteAbsorbGen (rs0 : RegFile) (pc : BitVec 64) (is_rvc : Bool)
    (ins : instruction) (rd : BitVec 5) (wval : BitVec 64) :
    textOk pc is_rvc ins → rd.toNat ≠ 0 →
    (∀ s_pc : ExecSt,
       s_pc.regs .nextPC = pc + instrLen is_rvc →
       gprAgree s_pc.regs rs0 →
       exec (execute ins) s_pc = some (RETIRE_SUCCESS, s_pc.setGpr rd wval)) →
    ⊢ intrAbsorbD i cpu ctrlOk (Φ0 (GF := GF)) -∗
      (∀ (s' : Athread) (rs' : RegFile) (k' : Nat),
         ⌜RetX cpu rs' k' s'⌝ -∗ ⌜ctrlOk rs'⌝ -∗
         ⌜rs' .PC = pc + instrLen is_rvc⌝ -∗
         ⌜∀ r : BitVec 5, r.toNat ≠ 0 →
            uxaXget rs' r = if r = rd then wval else uxaXget rs0 r⌝ -∗
         wpd .MaybeStuck i s' (Φ0 (GF := GF))) -∗
      ∀ (s : Athread) (rs : RegFile) (k : Nat),
        ⌜RetX cpu rs k s⌝ -∗ ⌜ctrlOk rs⌝ -∗ ⌜rs .PC = pc⌝ -∗
        ⌜∀ z : BitVec 5, uxaXget rs z = uxaXget rs0 z⌝ -∗
        wpd .MaybeStuck i s (Φ0 (GF := GF)) := by
  intro Htx Hrd Hcert
  unfold intrAbsorbD
  iintro #H C
  iloeb as IH
  iintro %s %rs %k %HRet %Hctrl %HPC %Hg0
  have Hcert' : ∀ s_pc : ExecSt,
      s_pc.regs .nextPC = pc + instrLen is_rvc →
      gprAgree s_pc.regs rs →
      exec (execute ins) s_pc = some (RETIRE_SUCCESS, s_pc.setGpr rd wval) :=
    fun s_pc Hn Hag => Hcert s_pc Hn (fun r Hr => (Hag r Hr).trans (Hg0 r))
  iapply (HX s rs k pc is_rvc ins rd wval HRet Hctrl HPC Htx Hrd Hcert')
  isplit
  · iintro %s' %rs' %k' %HR %Hc %Hpc %Hg
    have Hg' : ∀ r : BitVec 5, r.toNat ≠ 0 →
        uxaXget rs' r = if r = rd then wval else uxaXget rs0 r := by
      intro r Hr
      rw [Hg r Hr]
      split
      · rfl
      · exact Hg0 r
    iapply C $$ %s' %rs' %k' %HR %Hc %Hpc %Hg'
  · unfold TrapK
    iintro %s' %rs' %k' %HR %HT
    iapply H $$ %rs %s' %rs' %k' %HR %HT
    inext
    iintro %s'' %rs'' %k'' %HR'' %HRes
    obtain ⟨Hc'', Hpc'', Hg''⟩ := HRes
    have HPC'' : rs'' .PC = pc := Hpc''.trans HPC
    have Hg0'' : ∀ z : BitVec 5, uxaXget rs'' z = uxaXget rs0 z :=
      fun z => (Hg'' z).trans (Hg0 z)
    iapply IH $$ C %s'' %rs'' %k'' %HR'' %Hc'' %HPC'' %Hg0''

include HX in
/-- Rocq `X_gpr_write_absorb`: an SIE-AGNOSTIC gpr-write leaf — the caller supplies only the
plain continuation and the (persistent) handler contract; any number of interrupts taken at this
instruction is absorbed. -/
theorem XGprWriteAbsorb (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (ins : instruction) (rd : BitVec 5) (wval : BitVec 64) :
    RetX cpu rs k s → ctrlOk rs → rs .PC = pc →
    textOk pc is_rvc ins → rd.toNat ≠ 0 →
    (∀ s_pc : ExecSt,
       s_pc.regs .nextPC = pc + instrLen is_rvc →
       gprAgree s_pc.regs rs →
       exec (execute ins) s_pc = some (RETIRE_SUCCESS, s_pc.setGpr rd wval)) →
    ⊢ intrAbsorbD i cpu ctrlOk (Φ0 (GF := GF)) -∗
      (∀ (s' : Athread) (rs' : RegFile) (k' : Nat),
         ⌜RetX cpu rs' k' s'⌝ -∗ ⌜ctrlOk rs'⌝ -∗
         ⌜rs' .PC = pc + instrLen is_rvc⌝ -∗
         ⌜∀ r : BitVec 5, r.toNat ≠ 0 →
            uxaXget rs' r = if r = rd then wval else uxaXget rs r⌝ -∗
         wpd .MaybeStuck i s' (Φ0 (GF := GF))) -∗
      wpd .MaybeStuck i s (Φ0 (GF := GF)) := by
  intro HRet Hctrl HPC Htx Hrd Hcert
  have HA := XGprWriteAbsorbGen i cpu ctrlOk textOk HX rs pc is_rvc ins rd wval Htx Hrd Hcert
  unfold intrAbsorbD at HA ⊢
  iintro #H C
  have Hg0 : ∀ z : BitVec 5, uxaXget rs z = uxaXget rs z := fun _ => rfl
  iapply HA $$ H C %s %rs %k %HRet %Hctrl %HPC %Hg0

end absorb

/-! # 3. Control transfers with the interrupt arm; c.ret -/

/-- Rocq `X_ctlΦ_I`. -/
def XCtlΦI {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
    (i : Agent) (cpu : CPU) (ctrlOk : RegFile → Prop)
    (textOk : BitVec 64 → Bool → instruction → Prop) (G : Gdexec → Prop)
    (Φ : Athread → IProp GF) : Prop :=
  ∀ (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (ins : instruction) (ot : Option (BitVec 64)) (ow : Option (BitVec 5 × BitVec 64)),
    RetX cpu rs k s → ctrlOk rs → rs .PC = pc →
    textOk pc is_rvc ins → owOk ow → CertC ctrlOk rs pc is_rvc ins ot ow →
    (∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) →
    ⊢ (XPost i cpu ctrlOk Φ rs (tgtOf ot pc is_rvc) ow ∧ TrapK i cpu ctrlOk Φ rs) -∗
      wpd .MaybeStuck i s Φ

section xctlI
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (img : Image) (i : Agent) (cpu : CPU)
variable (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
variable (Hsp : SpineOkI img ctrlOk textAt)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)

include Hsp Htext Hflow in
/-- Rocq `X_ctlΦ_I_holds`. -/
theorem XCtlΦIHolds (G : Gdexec → Prop)
    (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
    (Φ : Athread → IProp GF)
    (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s) :
    XCtlΦI i cpu ctrlOk (textOkCtl img ctrlOk textAt no4) G Φ := by
  unfold XCtlΦI
  intro s rs k pc is_rvc ins ot ow HRet Hctrl HPC Htx How Hcert Hb
  iintro C
  iapply (wpdInstrOfEvA3 img i Φ cpu G HG Hmid Htext Hflow
    (fun _ t' => GoodC ctrlOk is_rvc rs pc ot ow t'.regs ∨ TrapPost ctrlOk rs t'.regs)
    rs k s HRet Hb
    (spineCertCI img ctrlOk textAt Hsp rs pc is_rvc ins ot ow Hctrl HPC Htx How Hcert))
  iintro %t' %rs' %ib' %k' %HG %Hag
  have HRet' : RetX cpu rs' k' ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ :=
    ⟨ib', rfl, rfl, rfl, rfl, rfl, regsAgreeRefl _ _⟩
  rcases HG with ⟨Hc, Hpc, Hg⟩ | HT
  · have Hc' : ctrlOk rs' := Hsp.spiSeip _ _ Hc Hag
    have Hpc' : rs' .PC = tgtOf ot pc is_rvc :=
      (Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))).trans Hpc
    have Hg' : ∀ r : BitVec 5, r.toNat ≠ 0 → uxaXget rs' r = gprPost ow rs r :=
      fun r Hr => (AxSymEngine2.uxaXgetAgree _ _ Hag r).trans (Hg r Hr)
    icases C with ⟨C, -⟩
    unfold XPost
    iapply C $$ %_ %rs' %k' %HRet' %Hc' %Hpc' %Hg'
  · have HT' : TrapPost ctrlOk rs rs' :=
      trapPostAgree ctrlOk rs _ _ (fun x y hx hy => Hsp.spiSeip x y hx hy) HT Hag
    icases C with ⟨-, T⟩
    unfold TrapK
    iapply T $$ %_ %rs' %k' %HRet' %HT'

end xctlI

/-- Rocq `ctl_regime_SI` (deviation 6). -/
theorem ctlRegimeSI (T : PTree) (satp0 : BitVec 64) : ctlRegime (ctrlOkSI T satp0) := by
  intro s hc
  refine ⟨execCurrentlyEnabledZca s (by rw [hc.2.2.1]; decide), cEZicfilpFalseS s hc.1 ?_⟩
  rw [hc.2.2.2.1]
  decide

section cretS
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64) (i : Agent) (cpu : CPU)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
  (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
  (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i (imgS σi)⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes (imgS σi) base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
variable (G : Gdexec → Prop)
  (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
  (Φ : Athread → IProp GF)
  (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
    ⊢ postLifting Φ i s)

include hmode hasid hppn Htext Hflow HG Hmid in
/-- Rocq `X_ctl_SI`. -/
theorem XCtlSI :
    XCtlΦI i cpu (ctrlOkSI T satp0)
      (textOkCtl (imgS σi) (ctrlOkSI T satp0) (textAtS σi T) no4) G Φ :=
  XCtlΦIHolds (imgS σi) i cpu _ _ (spineOkIS σi T satp0 hmode hasid hppn) Htext Hflow G HG Φ Hmid

include hmode hasid hppn Htext Hflow HG Hmid in
/-- Rocq `X_cret_SI`: c.ret (= c.jr ra = jalr x0, 0(ra)) AT THE SIE-AGNOSTIC S-MODE REGIME:
either PC := ra with bit 0 cleared (no GPR change), or the trap arm. -/
theorem XCretSI (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) :
    RetX cpu rs k s → ctrlOkSI T satp0 rs → rs .PC = pc →
    textOkCtl (imgS σi) (ctrlOkSI T satp0) (textAtS σi T) no4 pc true
      (.JALR (zeros (n := 12), ra, zreg)) →
    (∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) →
    ⊢ (XPost i cpu (ctrlOkSI T satp0) Φ rs (jalrTgt (zeros (n := 12)) (uxaXget rs ra5c)) none ∧
        TrapK i cpu (ctrlOkSI T satp0) Φ rs) -∗
      wpd .MaybeStuck i s Φ := by
  intro HRet Hc HPC Htx Hb
  have HX := XCtlSI σi T satp0 i cpu hmode hasid hppn Htext Hflow G HG Φ Hmid
    s rs k pc true _ (some _) _ HRet Hc HPC Htx (owOkLink _ _)
    (certJALR (ctrlOkSI T satp0) (ctlRegimeSI T satp0) rs pc true (zeros (n := 12)) ra5c
      (zero_extend (m := 5) 0b00#2) (by decide)) Hb
  rw [linkOwZero _ _ (by decide)] at HX
  exact HX

end cretS

/-! ### c.ret, ABSORBING form (post `Φ0`): the caller supplies only the plain continuation and
the persistent handler contract. -/

section cretAbsorb
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64) (i : Agent) (cpu : CPU)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
  (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
  (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i (imgS σi)⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes (imgS σi) base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)

include hmode hasid hppn Htext Hflow in
/-- Rocq `X_cret_SI_absorb_gen`. -/
theorem XCretSIAbsorbGen (rs0 : RegFile) (pc : BitVec 64) :
    textOkCtl (imgS σi) (ctrlOkSI T satp0) (textAtS σi T) no4 pc true
      (.JALR (zeros (n := 12), ra, zreg)) →
    ⊢ intrAbsorbD i cpu (ctrlOkSI T satp0) (Φ0 (GF := GF)) -∗
      XPost i cpu (ctrlOkSI T satp0) (Φ0 (GF := GF)) rs0
        (jalrTgt (zeros (n := 12)) (uxaXget rs0 ra5c)) none -∗
      ∀ (s : Athread) (rs : RegFile) (k : Nat),
        ⌜RetX cpu rs k s⌝ -∗ ⌜ctrlOkSI T satp0 rs⌝ -∗ ⌜rs .PC = pc⌝ -∗
        ⌜∀ z : BitVec 5, uxaXget rs z = uxaXget rs0 z⌝ -∗
        wpd .MaybeStuck i s (Φ0 (GF := GF)) := by
  intro Htx
  unfold intrAbsorbD
  iintro #H C
  iloeb as IH
  iintro %s %rs %k %HRet %Hc %HPC %Hg0
  have Hra : uxaXget rs ra5c = uxaXget rs0 ra5c := Hg0 ra5c
  iapply (XCretSI σi T satp0 i cpu hmode hasid hppn Htext Hflow (fun _ => True)
    (fun _ _ => BI.pure_intro trivial) Φ0 (fun _ s1 _ _ _ => postLiftingΦ0 i s1)
    s rs k pc HRet Hc HPC Htx (fun _ s1 _ _ _ => postLiftingΦ0 i s1))
  isplit
  · unfold XPost
    iintro %s' %rs' %k' %HR %Hc' %Hpc' %Hg'
    have Hpc'' : rs' .PC = jalrTgt (zeros (n := 12)) (uxaXget rs0 ra5c) := by
      rw [Hpc', Hra]
    have Hg'' : ∀ r : BitVec 5, r.toNat ≠ 0 → uxaXget rs' r = gprPost none rs0 r :=
      fun r Hr => (Hg' r Hr).trans (Hg0 r)
    iapply C $$ %s' %rs' %k' %HR %Hc' %Hpc'' %Hg''
  · unfold TrapK
    iintro %s' %rs' %k' %HR %HT
    iapply H $$ %rs %s' %rs' %k' %HR %HT
    inext
    iintro %s'' %rs'' %k'' %HR'' %HRes
    obtain ⟨Hc'', Hpc'', Hg''⟩ := HRes
    have HPC'' : rs'' .PC = pc := Hpc''.trans HPC
    have Hg0'' : ∀ z : BitVec 5, uxaXget rs'' z = uxaXget rs0 z :=
      fun z => (Hg'' z).trans (Hg0 z)
    iapply IH $$ C %s'' %rs'' %k'' %HR'' %Hc'' %HPC'' %Hg0''

include hmode hasid hppn Htext Hflow in
/-- Rocq `X_cret_SI_absorb`. -/
theorem XCretSIAbsorb (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) :
    RetX cpu rs k s → ctrlOkSI T satp0 rs → rs .PC = pc →
    textOkCtl (imgS σi) (ctrlOkSI T satp0) (textAtS σi T) no4 pc true
      (.JALR (zeros (n := 12), ra, zreg)) →
    ⊢ intrAbsorbD i cpu (ctrlOkSI T satp0) (Φ0 (GF := GF)) -∗
      XPost i cpu (ctrlOkSI T satp0) (Φ0 (GF := GF)) rs
        (jalrTgt (zeros (n := 12)) (uxaXget rs ra5c)) none -∗
      wpd .MaybeStuck i s (Φ0 (GF := GF)) := by
  intro HRet Hc HPC Htx
  have HA := XCretSIAbsorbGen σi T satp0 i cpu hmode hasid hppn Htext Hflow rs pc Htx
  unfold intrAbsorbD at HA ⊢
  iintro #H C
  have Hg0 : ∀ z : BitVec 5, uxaXget rs z = uxaXget rs z := fun _ => rfl
  iapply HA $$ H C %s %rs %k %HRet %Hc %HPC %Hg0

end cretAbsorb

end Weak
