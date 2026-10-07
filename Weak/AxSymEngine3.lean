/-
Weak: **the symbolic WPd engine X, slice 2** (builds on `AxSymEngine` / `AxSymEngine2`; nothing
existing is edited) — part 1 of 2 (§1–§4; §5–§6 are the Lean-only split `Weak.AxSymEngine3b`).

Rocq: `iris/AxSymEngine3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 THE 4-BYTE ARM.  `EvAHartActiveBase` (EvA twin of the SC base-arm progress lemma),
`SpineFetch4` (the `F_Base` fetch field — the only NEW instruction-independent fact; every other
`SpineOk` field is shared), `textOkD4` / `textOkDB` (both arms), `spineCert4` /
`AxSymEngine3.spineCertB`.
§2 THE BRIDGE WITH FINE ROW-END PREMISES (`wpdOfEvA3`, `wpdInstrOfEvA3`, model-generic `…3M`
over `M : Gdexec → Prop`): slice 1's `Hend` ("every `postLifting Φ` is free", true only for
`Φ = True`) is REPLACED by `Hmid` (Φ at MID-INSTRUCTION row ends, under a gconst-derivable graph
fact `G`) and a per-call boundary premise `Hb` (Φ at the START boundary if the row ends there).
§3 `XGprWriteΦ` (X for ANY Φ) and `XGprWriteΦHolds` (BOTH arms); `XGprWriteHoldsB`: slice 1's X
statement, now incl. `is_rvc = false`.
§4 Leaves over any Φ: `wpGprWriteDΦ` (either arm), `wpCmvDΦ`, `wpCaddiwDΦ`, `wpAddDΦ` (4-byte
add); the boundary-indexed REAL post `ΦRet cpu P` (`ΦRetMid`: Hmid PROVED for it); real leaves
`wpCmvDRealB`, `wpAddDReal` (4-byte, Φ0) and `wpCmvDRealPost` (c.mv with post `ΦRet cpu P`).
(§5 instance premises at `axGA2` / the ledger instance, §6 non-vacuity: `Weak.AxSymEngine3b`.)
STILL CONDITIONAL ON: `SpineOk` + `SpineFetch4` (∀-state, per regime) and `textFixed GD0 i img`.

## Deviations from Rocq

1. O2 STAGE C (as `AxSymEngine` deviation 1 / `AxSymEngine2` deviation 1): the section premise
   `Hloc` (local-interp advance at a fetch) is DROPPED from §2–§4 (the bridge's fetch is a pinned
   admin step at the same row position); premises are `G HG Hmid Htext Hflow` after
   `img i Φ cpu`.  `wpdMreadNode3M` continues at `AxSymEngine.rdNext req k` (Rocq `S k`) and is
   proved from the Lean-only `AxSymEngine3.wpdImgFetch3M` / `wpdImgRead3M` (the
   `AxSymEngine.wpdImgFetch`/`wpdImgRead` scripts with the row-end clause from `Hmid`).
2. Q7 (as `AxSymEngine2` deviation 3): the 4-byte arm announces the 32-bit word and `EvA.evIa`
   needs `sfAnnB 32 w = false`; `EvAHartActiveBase` takes it as a premise and `textOkD4` carries
   it as an extra conjunct (after `textAt4 pc w`).
3. LEAN-SAIL: the base arm's landing-pad test is a pure `&&` (Rocq `and_boolM`); with the lpad
   answer `false` the `is_lpad_instruction` conjunct of `textOkD4` is unused (kept).  `isNext m`
   is `m = .impure (.ok _) _` (Rocq `Next`).  Rocq's Ltacs `ev_step3`/`ev_go3`/`ev_use3`/`lk3`/
   `silent_ps3` ↦ `AxSymEngine2`'s kit (`ax_sym2_ev_go`, `evRUse`, the Lean-only
   `AxSymEngine3.evRAnn32`) and `AxSymEngine.silentPs`.
4. Types/registers as `AxSymEngine2` deviations 5–6 (`incr : Bool → Int`, GPR clauses over
   `uxaXget` at `BitVec 5`, `Z.eqb (uint r) (uint rd)` ↦ `r = rd`, `regs_agree seip_reg` ↦
   `regsAgree AxRunClose.pinReg`).  `XGprWriteΦ` and the §4 leaves state the next pc as
   `pc + instrLen is_rvc` (as `AxReuseProbe2.XGprWrite`; Rocq `add_vec_int pc (if …)`, defeq per
   arm); `GoodN` keeps `BitVec.addInt pc (incr is_rvc)`.
5. As `AxReuseProbe2` deviations 2–4: the SC hart `cid` explicit, `rget cid m r`, `m.set rd v`,
   `MachCSL.rdOk`, `wpNext` continuation indexed by the hart, `[InvGS_gen hlc GF]` for any
   `hlc`; `GenId` dropped.  Rocq's §2 `Definition …3 := …3M rvwmo_cat_consistent` ↦ theorems
   restating the `…3M` lemma at `rvwmoCatConsistent` (with `wpd`).  Rocq's section `Let TX`/`XP`
   are inlined.
6. Q12 (`AxEpiChainSdLd` deviation 5): `wpdOfClosedRunGM`'s closure premise takes the step's
   boot-image pin; `wpdAdminNode3M` / `wpdRetNode3M` ignore it (statements unchanged).

**Rocq → Lean name map.**  `EvA_hart_active_base` `EvAHartActiveBase`, `SpineFetch4`
`SpineFetch4`, `text_ok_d4` `textOkD4`, `text_ok_dB` `textOkDB`, `incr` `incr`, `GoodN` `GoodN`,
`GoodN_true` `GoodNTrue`, `spine_cert4` `spineCert4`, `spine_certB` `AxSymEngine3.spineCertB`
(duplicated with AxSpinE), `is_next` `isNext`, `mid_state` `midState`, `wpd_admin_node3(M)`
`wpdAdminNode3(M)`, `wpd_mread_node3(M)` `wpdMreadNode3(M)`, `wpd_of_EvA3(M)` `wpdOfEvA3(M)`,
`wpd_ret_node3(M)` `wpdRetNode3(M)`, `wpd_instr_of_EvA3(M)` `wpdInstrOfEvA3(M)`,
`X_gpr_writeΦ` `XGprWriteΦ`, `X_gpr_writeΦ_holds` `XGprWriteΦHolds`, `X_gpr_write_holdsB`
`XGprWriteHoldsB`, `Φ_ret` `ΦRet`, `Φ_ret_mid` `ΦRetMid`, `Φ_ret_boundary` `ΦRetBoundary`,
`Goal_dΦ` `goalDΦ`, `Goal_dΦ_Φ0` `goalDΦΦ0`, `wp_gpr_write_dΦ` `wpGprWriteDΦ`, `wp_cmv_dΦ`
`wpCmvDΦ`, `wp_caddiw_dΦ` `wpCaddiwDΦ`, `wp_add_dΦ` `wpAddDΦ`, `wp_cmv_d_realB` `wpCmvDRealB`,
`wp_add_d_real` `wpAddDReal`, `wp_cmv_d_real_post` `wpCmvDRealPost`.  Lean-only
(file-qualified): `AxSymEngine3.evRAnn32`, `AxSymEngine3.wpdImgFetch3M`,
`AxSymEngine3.wpdImgRead3M`, `AxSymEngine3.wpdSilentNode3M`.

**Dropped:** nothing (this part: Rocq 36 definitions/lemmas + 5 Ltacs; Lean 36 + 4 Lean-only).
**Not ported:** the `Print Assumptions`/`Check` lines (the lint's axiom check covers them).
-/
import Weak.AxSymEngine2
import Weak.AxEpiChainSdLd

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 1. The 4-byte (`F_Base`) arm -/

/-- (Lean-only) A 32-bit announce of a non-sfence word, in the early-return monad. -/
theorem AxSymEngine3.evRAnn32 {img : Image} {QE : Sail.Error exception → ExecSt → Prop}
    {R X : Type} {Q : Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {w : BitVec 32} {f : Unit → SailME R X} {t : ExecSt} (hw : sfAnnB 32 w = false)
    (H : EvA img QE Q (ExceptT.run (f ())) t) :
    EvA img QE Q (ExceptT.run (liftM (instr_announce w : SailM Unit) >>= f)) t :=
  EvAFactLift img QE (fun _ t' => t' = t) Q _ f t (.evIa 32 w _ t hw (.evRet _ _ rfl))
    (fun _ _ h => by subst h; exact H)

section baseArm
variable (img : Image)

/-- The EvA twin of the SC base-arm progress lemma (state-preserving fetch). -/
theorem EvAHartActiveBase (t : ExecSt) (w : BitVec 32) (ins : instruction) (pc : BitVec 64)
    (Qx : ExecSt → Prop) (hw : sfAnnB 32 w = false) :
    EvA img (fun _ _ => False) (fun r t' => r = none ∧ t' = t)
      (dispatchInterrupt (t.regs .cur_privilege)) t →
    EvA img (fun _ _ => False) (fun r t' => r = .F_Base w ∧ t' = t) (fetch ()) t →
    EvA img (fun _ _ => False) (fun x t' => x = ins ∧ t' = t) (ext_decode w) t →
    EvA img (fun _ _ => False) (fun x t' => x = false ∧ t' = t) (is_landing_pad_expected ()) t →
    t.regs .PC = pc →
    EvA img (fun _ _ => False) (fun x t' => x = RETIRE_SUCCESS ∧ Qx t') (execute ins)
      (t.setReg .nextPC (BitVec.addInt pc 4)) →
    EvA img (fun _ _ => False)
      (fun x t' => x = .Step_Execute (RETIRE_SUCCESS, zero_extend (m := 32) w) ∧ Qx t')
      (run_hart_active 0) t := by
  intro Hdisp Hfetch Hdec Hlpad HPC Hexec
  subst HPC
  unfold run_hart_active
  apply EvACatchEarlyReturn
  ax_sym2_ev_go
  refine AxSymEngine2.evRUse Hdisp ?_
  ax_sym2_ev_go
  refine AxSymEngine2.evRUse Hfetch ?_
  ax_sym2_ev_go
  refine AxSymEngine3.evRAnn32 hw ?_
  ax_sym2_ev_go
  refine AxSymEngine2.evRUse Hdec ?_
  ax_sym2_ev_go
  refine AxSymEngine2.evRUse Hlpad ?_
  ax_sym2_ev_go
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  ax_sym2_ev_go
  refine EvAFactLift img _ _ _ _ _ _ Hexec ?_
  rintro _ t' ⟨rfl, hq⟩
  ax_sym2_ev_go
  exact .evRet _ _ ⟨rfl, hq⟩

end baseArm

/-- The 4-byte fetch field: the instruction-independent twin of `SpineOk.spFetch` for `F_Base`. -/
def SpineFetch4 (img : Image) (ctrlOk : RegFile → Prop) (textAt4 : BitVec 64 → BitVec 32 → Prop) :
    Prop :=
  ∀ (t : ExecSt) pc w, ctrlOk t.regs → t.regs .PC = pc → textAt4 pc w →
    EvA img (fun _ _ => False) (fun r t' => r = .F_Base w ∧ t' = t) (fetch ()) t

/-- The WPd reading of `instr pc false ins` (deviation 1: the word is not an sfence word). -/
def textOkD4 (img : Image) (ctrlOk : RegFile → Prop) (textAt4 : BitVec 64 → BitVec 32 → Prop)
    (pc : BitVec 64) (is_rvc : Bool) (ins : instruction) : Prop :=
  is_rvc = false ∧ ∃ w, textAt4 pc w ∧ sfAnnB 32 w = false ∧
    (∀ t : ExecSt, ctrlOk t.regs →
      EvA img (fun _ _ => False) (fun x t' => x = ins ∧ t' = t) (ext_decode w) t) ∧
    is_lpad_instruction ins = false ∧
    rf0 (execute ins)

/-- BOTH arms. -/
def textOkDB (img : Image) (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
    (textAt4 : BitVec 64 → BitVec 32 → Prop) (pc : BitVec 64) (is_rvc : Bool)
    (ins : instruction) : Prop :=
  if is_rvc then textOkD img ctrlOk textAt pc true ins
  else textOkD4 img ctrlOk textAt4 pc false ins

def incr (is_rvc : Bool) : Int := if is_rvc then 2 else 4

def GoodN (ctrlOk : RegFile → Prop) (is_rvc : Bool) (rs : RegFile) (pc : BitVec 64)
    (rd : BitVec 5) (wval : BitVec 64) (rs' : RegFile) : Prop :=
  ctrlOk rs' ∧ rs' .PC = BitVec.addInt pc (incr is_rvc) ∧
    ∀ r : BitVec 5, r.toNat ≠ 0 → uxaXget rs' r = if r = rd then wval else uxaXget rs r

theorem GoodNTrue (ctrlOk : RegFile → Prop) (rs : RegFile) (pc : BitVec 64) (rd : BitVec 5)
    (wval : BitVec 64) (rs' : RegFile) :
    Good ctrlOk rs pc rd wval rs' ↔ GoodN ctrlOk true rs pc rd wval rs' := Iff.rfl

section regime4
variable (img : Image)

/-- `spineCert` for the 4-byte arm (same script; the run of `run_hart_active` is
`EvAHartActiveBase`). -/
theorem spineCert4 (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
    (textAt4 : BitVec 64 → BitVec 32 → Prop)
    (Hsp : SpineOk img ctrlOk textAt) (Hf4 : SpineFetch4 img ctrlOk textAt4)
    (rs : RegFile) (pc : BitVec 64) (ins : instruction) (rd : BitVec 5) (wval : BitVec 64) :
    ctrlOk rs → rs .PC = pc → textOkD4 img ctrlOk textAt4 pc false ins → rd.toNat ≠ 0 →
    (∀ s_pc : ExecSt,
       s_pc.regs .nextPC = BitVec.addInt pc 4 →
       gprAgree s_pc.regs rs →
       exec (execute ins) s_pc = some (RETIRE_SUCCESS, s_pc.setGpr rd wval)) →
    ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
      EvA img (fun _ _ => False) (fun _ t' => GoodN ctrlOk false rs pc rd wval t'.regs)
        (riscvStep tick) t := by
  intro Hct HPC ⟨_, w, Hat, Hsf, Hdec, _, Hrf⟩ Hrd Hcert tick t Hag
  have Hct_t : ctrlOk t.regs := Hsp.spSeip _ _ Hct Hag
  have HPC_t : t.regs .PC = pc := by
    rw [Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))]; exact HPC
  obtain ⟨b, Hb⟩ := Hsp.spInc t Hct_t
  have Hct_a : ctrlOk (t.setReg .minstret_increment b).regs :=
    Hsp.spFrame _ _ _ (Or.inr (Or.inr (Or.inl rfl))) Hct_t
  have HPC_a : (t.setReg .minstret_increment b).regs .PC = pc := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC_t
  have Hgag : gprAgree ((t.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).regs rs := by
    intro r _
    simp only [ExecSt.setReg_regs]
    rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide), AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]
    exact AxSymEngine2.uxaXgetAgree _ _ Hag r
  have Hexec : EvA img (fun _ _ => False)
      (fun x t' => x = RETIRE_SUCCESS ∧
        t' = ((t.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setGpr rd wval)
      (execute ins) ((t.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)) :=
    rf0EvA img _ _ Hrf _ _ _ (Hcert _ (by simp only [ExecSt.setReg_regs, RegFile.set_same]) Hgag)
  have Hrun := EvAHartActiveBase img (t.setReg .minstret_increment b) w ins pc
    (fun t' => t' = ((t.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setGpr rd wval)
    Hsf (Hsp.spDisp _ Hct_a) (Hf4 _ pc w Hct_a HPC_a Hat) (Hdec _ Hct_a) (Hsp.spLpad _ Hct_a)
    HPC_a Hexec
  refine EvARiscvStep img tick t (fun t' => GoodN ctrlOk false rs pc rd wval t'.regs) _ ?_ ?_
  · have HT := EvATryStepActive img t b (zero_extend (m := 32) w)
      (fun t' => t' = ((t.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setGpr rd wval)
      (fun t' => GoodN ctrlOk false rs pc rd wval t'.regs) Hb (Hsp.spHart _ Hct_a) Hrun ?_
    · exact EvAMono img _ _ _ _ _ t (fun _ _ h => h) (fun _ _ h => h.2) HT
    · rintro _ rfl
      have Hx := AxSymEngine2.setGprRegsNe
        ((t.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)) rd wval
      refine ⟨?_, ?_, ?_⟩
      · rw [Hx _ (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide)]
        exact Hsp.spHart _ Hct_a
      · rw [Hx _ (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide), RegFile.set_same]
      · have Hct_x := AxSymEngine2.ctrlOkSetGpr ctrlOk Hsp.spFrame
          ((t.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)) rd wval
          (Hsp.spFrame _ _ _ (Or.inr (Or.inl rfl)) Hct_a)
        refine ⟨?_, ?_, ?_⟩
        · unfold tfinal
          cases b
          · exact Hsp.spFrame _ _ _ (Or.inl rfl) Hct_x
          · exact Hsp.spFrame _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
              (Hsp.spFrame _ _ _ (Or.inl rfl) Hct_x)
        · unfold tfinal incr
          cases b <;> simp only [ExecSt.setReg_regs, Bool.false_eq_true, ↓reduceIte] <;>
            (try rw [RegFile.set_other _ _ _ _ (by decide)]) <;>
            rw [RegFile.set_same, Hx _ (by decide)] <;>
            simp only [ExecSt.setReg_regs, RegFile.set_same]
        · intro r Hr
          have e : uxaXget (tfinal b (((t.setReg .minstret_increment b).setReg .nextPC
              (BitVec.addInt pc 4)).setGpr rd wval)).regs r =
              ((((t.setReg .minstret_increment b).setReg .nextPC
                (BitVec.addInt pc 4)).setGpr rd wval)).gpr r := by
            unfold tfinal ExecSt.gpr
            cases b <;> simp only [ExecSt.setReg_regs, Bool.false_eq_true, ↓reduceIte] <;>
              (try rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]) <;>
              rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]
          rw [e]
          by_cases E : r = rd
          · subst E
            simp only [if_true]
            exact AxFetch3c.gprSetGprSame _ r wval Hrd
          · simp only [E, if_false]
            rw [AxFetch3c.gprSetGprNe _ rd r wval E]
            exact Hgag r Hr
  · intro t' HG
    cases tick with
    | false => exact HG
    | true =>
      refine EvAMono img _ _ _ _ _ t' (fun _ _ h => h) ?_ (Hsp.spTick t' HG.1)
      rintro _ t'' ⟨Hc, Hk1, Hk2⟩
      obtain ⟨-, HG2, HG3⟩ := HG
      exact ⟨Hc, Hk1.trans HG2, fun r Hr => (Hk2 r).trans (HG3 r Hr)⟩

/-- Both arms at once. -/
theorem AxSymEngine3.spineCertB (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
    (textAt4 : BitVec 64 → BitVec 32 → Prop)
    (Hsp : SpineOk img ctrlOk textAt) (Hf4 : SpineFetch4 img ctrlOk textAt4)
    (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (ins : instruction) (rd : BitVec 5)
    (wval : BitVec 64) :
    ctrlOk rs → rs .PC = pc → textOkDB img ctrlOk textAt textAt4 pc is_rvc ins → rd.toNat ≠ 0 →
    (∀ s_pc : ExecSt,
       s_pc.regs .nextPC = BitVec.addInt pc (if is_rvc then 2 else 4) →
       gprAgree s_pc.regs rs →
       exec (execute ins) s_pc = some (RETIRE_SUCCESS, s_pc.setGpr rd wval)) →
    ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
      EvA img (fun _ _ => False) (fun _ t' => GoodN ctrlOk is_rvc rs pc rd wval t'.regs)
        (riscvStep tick) t := by
  cases is_rvc <;> intro Hct HPC Htx Hrd Hcert tick t Hag
  · exact spineCert4 img ctrlOk textAt textAt4 Hsp Hf4 rs pc ins rd wval Hct HPC Htx Hrd
      Hcert tick t Hag
  · exact spineCert img ctrlOk textAt Hsp rs pc ins rd wval Hct HPC Htx Hrd Hcert tick t Hag

end regime4


/-! # 2. THE BRIDGE with FINE row-end premises (replaces `Hend`) -/

/-- A model-tree node with an outcome (Rocq `Next`). -/
def isNext {X : Type} (m : SailM X) : Prop :=
  match m with
  | .impure (.ok _) _ => True
  | _ => False

def midState (s : Athread) : Prop :=
  match s.atP with
  | .PHart _ m _ _ _ => isNext m
  | _ => False

section bridge3
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (M : Gdexec → Prop)
variable (img : Image) (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
variable (G : Gdexec → Prop) (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
  ⊢ postLifting Φ i s)
variable (Htext : ∀ GD, M GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, M GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)

include HG Hmid in
theorem wpdAdminNode3M (m : SailM Unit) (Hm : isNext m) (kk : Nat) (A : RegFile → Prop)
    (N : Athread → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hps : ∀ rs ib d l p' d', A rs → pstepProg (.PHart cpu m rs none ib) d l p' d' →
       lbAdmin true l ∧ N ⟨p', kk⟩) :
    ∀ rs ib, A rs →
    ⊢ (∀ s2, ⌜N s2⌝ -∗ wpdM M .MaybeStuck i s2 Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu m rs none ib, kk⟩ Φ := by
  intro rs ib HAr
  let P : Athread → Prop := fun s => ∃ rs1 ib1, s = ⟨.PHart cpu m rs1 none ib1, kk⟩ ∧ A rs1
  have Hnord : ∀ GD s1 id K, G GD → P s1 → ¬ areadStep (AxOpsem.grow GD i) s1 id K := by
    rintro GD s1 id K - ⟨rs1, ib1, rfl, HA1⟩ ⟨lb, -, -, Hrd, HK⟩
    obtain ⟨l, d, d', Hl, -, Hp, -⟩ := HK (List.replicate (aidentN id) 0) List.length_replicate
    obtain ⟨Had, -⟩ := Hps _ _ _ _ _ _ HA1 Hp
    rw [← Hl, lbAdminRd l Had] at Hrd
    cases Hrd
  have Hclos : ∀ GD s1 l s2, G GD → P s1 → AxOpsem.astepProg (AxOpsem.grow GD i) s1 l s2 →
      WeakAxRealize.fetchPin GD.gdG.gxImg l →
      wlWdata l = none ∧ s2.atK = s1.atK ∧ (P s2 ∨ N s2) := by
    rintro GD s1 l s2 - ⟨rs1, ib1, rfl, HA1⟩ Hst -
    obtain ⟨d, d', Hp⟩ := astepProgPstep _ _ _ _ Hst
    obtain ⟨Had, HN⟩ := Hps _ _ _ _ _ _ HA1 Hp
    have Hk := astepProgAdminK' _ _ _ _ Hst Had
    refine ⟨AxRunClose.lbAdminWdata l Had, Hk, .inr ?_⟩
    obtain ⟨p2, k2⟩ := s2
    simp only at Hk
    subst Hk
    exact HN
  have Hwire : ∀ s1 s2, P s1 → awire s1 s2 → P s2 ∨ N s2 := by
    rintro s1 s2 ⟨rs1, ib1, rfl, HA1⟩ Hw
    obtain ⟨hk, hp⟩ := awireAeqv _ _ Hw
    obtain ⟨p2, k2⟩ := s2
    simp only at hk hp
    subst hk
    cases p2 with
    | PDisk _ => exact hp.elim
    | PHart c m2 rs2 fn2 ib2 =>
      obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := hp
      exact .inl ⟨rs2, ib2, rfl, HA rs1 rs2 HA1 hag⟩
  iintro C
  iapply (wpdOfClosedRunGM M i G P N Φ HG Hnord Hclos Hwire) $$
    %⟨.PHart cpu m rs none ib, kk⟩ %⟨rs, ib, rfl, HAr⟩
  isplit
  · iexact C
  · iintro %GD %s1 %HGD %HP1 %Heq
    obtain ⟨rs1, ib1, rfl, -⟩ := HP1
    iapply (Hmid GD _ HGD (by exact Hm) Heq)

include HG Hmid Htext in
/-- (Lean-only, as `AxSymEngine.wpdImgFetch`) an image FETCH, fine row-end form. -/
theorem AxSymEngine3.wpdImgFetch3M (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (vs : List (BitVec 8)) (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hdev : devAddr req.pa = false) (Hfe : (classify req.access_kind).akIfetch = true)
    (Hvs : imgBytes img (paZ req.pa) n = some vs) :
    ⊢ ∀ rs, ⌜A rs⌝ -∗
      (∀ rs', ⌜A rs'⌝ -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs' none ib, k⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ Φ := by
  obtain ⟨Hlen, Himgj⟩ := imgBytesSpec img _ n vs Hvs
  iloeb as IH
  iintro %rs %HP C
  iapply (AxWpD.wpdMUnfoldStep M .MaybeStuck i _ Φ).2
  isplit
  · iapply (progressOblMaybestuck (GF := GF) i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
  ihave Hok := (Htext GD Hc) $$ Hg
  icases Hok with %Hok
  ihave HGD := (HG GD Hc) $$ Hg
  icases HGD with %HGD
  have Himg : ∀ j : Nat, j < vs.length → GD.gdG.gxImg (paZ req.pa + j) = vs[j]? := by
    intro j hj
    have h1 := Himgj j (by omega)
    rw [List.getElem?_eq_getElem hj] at h1 ⊢
    exact Hok.1 _ _ h1
  isplit
  · iintro %id %K %Hst
    exact (AxCjrWpd.fetchNoRead _ cpu n va req KK rs ib k id K Hdev Hfe Hst).elim
  isplit
  · iintro %l %s' %Hst %Hpin
    obtain ⟨tvs, hlen, rfl, rfl⟩ := AxCjrWpd.fetchAstepInv _ cpu n va req KK rs ib k l s' Hdev Hfe Hst
    rw [AxCjrWpd.pinnedBytes _ _ tvs vs (by omega) Himg Hpin]
    simp only [wlWdata]
    unfold wpSkipStep
    iintro %na Hna
    imodintro
    inext
    imodintro
    iexists ls
    iframe Hna Hloc
    iapply C $$ %rs %HP
  isplit
  · iintro %s' %Hw
    obtain ⟨hk, hp⟩ := awireAeqv _ _ Hw
    obtain ⟨p', k'⟩ := s'
    simp only at hk hp
    subst hk
    match p', hp with
    | .PHart c m' rs' fn' ib', hp =>
      obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := hp
      unfold wpSkipStep
      iintro %na Hna
      imodintro
      inext
      imodintro
      iexists ls
      iframe Hna Hloc
      iapply IH $$ %rs' %(HA rs rs' HP hag) C
  · iintro %Heq
    iapply (Hmid GD _ HGD (by exact trivial) Heq)

include HG Hmid Htext Hflow in
/-- (Lean-only, as `AxSymEngine.wpdImgRead`) an image GRAPH READ, fine row-end form. -/
theorem AxSymEngine3.wpdImgRead3M (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (vs : List (BitVec 8)) (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hnf : (classify req.access_kind).akIfetch = false)
    (Hvs : imgBytes img (paZ req.pa) n = some vs) :
    ⊢ ∀ rs, ⌜A rs⌝ -∗
      (∀ rs', ⌜A rs'⌝ -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs' none ib, k + 1⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ Φ := by
  iloeb as IH
  iintro %rs %HP C
  iapply (AxWpD.wpdMUnfoldStep M .MaybeStuck i _ Φ).2
  isplit
  · iapply (progressOblMaybestuck (GF := GF) i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
  ihave Hok := (Htext GD Hc) $$ Hg
  icases Hok with %Hok
  ihave HGD := (HG GD Hc) $$ Hg
  icases HGD with %HGD
  isplit
  · iintro %id %K %Hst
    obtain ⟨lb, Hlb, Hid, -, HK⟩ := Hst
    simp only at Hlb
    subst Hid
    obtain ⟨l0, d0, d0', Hl0, -, Hps0, -⟩ :=
      HK (List.replicate (aidentN (aident lb)) 0) List.length_replicate
    obtain ⟨tvs0, Htl0, rfl, -⟩ :=
      AxLdspWpd.loadStepInv cpu n va req KK rs ib d0 _ _ d0' Hdev Hlat Hnf Hps0
    simp only [wlRd, Htl0] at Hl0
    obtain ⟨Hidlb, Hgv⟩ := Hok.2 k lb _ _ _ vs Hlb Hl0.symm Hvs
    have Hadv0 : aidentAdvRd (aident lb) = 1 := by rw [Hidlb]; rfl
    simp only [Hadv0, ↓reduceIte]
    iintro %v %Hv %Hlenv
    obtain ⟨l, d, d', -, Hrv, Hps, Hk'⟩ := HK v Hlenv
    obtain ⟨tvs, Htl, rfl, Hp'⟩ :=
      AxLdspWpd.loadStepInv cpu n va req KK rs ib d _ _ d' Hdev Hlat Hnf Hps
    simp only [wlRvals] at Hrv
    subst Hrv
    have hvs : tvs.map Prod.snd = vs := by
      rw [Hgv] at Hv
      exact (Option.some.inj Hv).symm
    rw [Hadv0] at Hk'
    have hKv : K (tvs.map Prod.snd) =
        ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs none ib, k + 1⟩ := by
      cases hK : K (tvs.map Prod.snd) with
      | AThread p' k' =>
        rw [hK] at Hp' Hk'
        simp only at Hp' Hk'
        rw [Hp', Hk', hvs]
    rw [hKv]
    unfold wpEvStep
    iintro %na Hpg
    ihave Hf := (BI.wand_intro (Hflow GD ls k Hc ⟨lb, _, _, _, vs, Hlb, Hidlb, Hvs⟩)) $$ Hg Hloc
    unfold fetchFlow
    imod Hf $$ %na Hpg with Hf
    imodintro
    inext
    imod Hf with ⟨%R, %nu, %nuu, %ls', Hs, Hfe, Hna, Hl⟩
    imodintro
    iexists (), R, nu, nuu, ls'
    isplitr
    · ipureintro
      trivial
    iframe Hs Hna Hl
    isplitl [Hfe]
    · iapply (flowEqDynMono GD (i, k) _ nu R
        iprop(R ∗ ⌜graphValue GD (i, k) = some (tvs.map Prod.snd)⌝))
      · inext
        iintro HR
        iframe HR
        ipureintro
        exact Hv
      · iexact Hfe
    · iapply C $$ %rs %HP
  isplit
  · iintro %l %s' %Hst %Hpin
    have hfalse : False := by
      obtain ⟨d, d', hps⟩ := astepProgPstep _ _ _ _ Hst
      obtain ⟨tvs, -, hl, -⟩ :=
        AxLdspWpd.loadStepInv cpu n va req KK rs ib d l _ d' Hdev Hlat Hnf hps
      subst hl
      cases Hst with
      | AStepAdmin _ _ _ _ _ _ hadm _ => exact hadm
      | AStepWrite _ _ _ _ _ _ _ _ hwr _ _ _ => simp [wlWr] at hwr
      | AStepFence _ _ _ _ _ _ _ _ hf _ _ => simp [wlFence] at hf
    exact hfalse.elim
  isplit
  · iintro %s' %Hw
    obtain ⟨hk, hp⟩ := awireAeqv _ _ Hw
    obtain ⟨p', k'⟩ := s'
    simp only at hk hp
    subst hk
    match p', hp with
    | .PHart c m' rs' fn' ib', hp =>
      obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := hp
      unfold wpSkipStep
      iintro %na Hna
      imodintro
      inext
      imodintro
      iexists ls
      iframe Hna Hloc
      iapply IH $$ %rs' %(HA rs rs' HP hag) C
  · iintro %Heq
    iapply (Hmid GD _ HGD (by exact trivial) Heq)

include HG Hmid Htext Hflow in
/-- A plain RAM read of image bytes, fine row-end form (a fetch at `k`, a graph read to
`k + 1`, as `wpdMreadNode`). -/
theorem wpdMreadNode3M (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (vs : List (BitVec 8)) (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hvs : imgBytes img (paZ req.pa) n = some vs) :
    ⊢ ∀ rs, ⌜A rs⌝ -∗
      (∀ rs', ⌜A rs'⌝ -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs' none ib,
           AxSymEngine.rdNext req k⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ Φ := by
  cases hfe : (classify req.access_kind).akIfetch with
  | true =>
    have e : AxSymEngine.rdNext req k = k := by simp only [AxSymEngine.rdNext, hfe, ↓reduceIte]
    rw [e]
    exact AxSymEngine3.wpdImgFetch3M M img i Φ cpu G HG Hmid Htext n va req KK ib k vs A HA Hdev
      hfe Hvs
  | false =>
    have e : AxSymEngine.rdNext req k = k + 1 := by
      simp only [AxSymEngine.rdNext, hfe, Bool.false_eq_true, ↓reduceIte]
    rw [e]
    exact AxSymEngine3.wpdImgRead3M M img i Φ cpu G HG Hmid Htext Hflow n va req KK ib k vs A HA
      Hdev Hlat hfe Hvs

include HG Hmid in
/-- (Lean-only, as `AxSymEngine.wpdSilentNode`) a silent node, fine row-end form. -/
theorem AxSymEngine3.wpdSilentNode3M (m m1 : SailM Unit) (Hm : isNext m) (kk : Nat) (t : ExecSt)
    (H : ∀ rs ib d l m' ors fn' d' oib obar, pnodeStep m rs ib d l m' ors fn' d' oib obar →
      lbAdmin true l ∧ m' = m1 ∧ ors = none ∧ fn' = none) :
    ∀ rs ib, regsAgree AxRunClose.pinReg rs t.regs →
    ⊢ (∀ rs1 ib1, ⌜regsAgree AxRunClose.pinReg rs1 t.regs⌝ -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu m1 rs1 none ib1, kk⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu m rs none ib, kk⟩ Φ := by
  intro rs ib Hag
  iintro C
  iapply (wpdAdminNode3M M i Φ cpu G HG Hmid m Hm kk
    (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
    (fun s2 => ∃ rs1 ib1, s2 = ⟨.PHart cpu m1 rs1 none ib1, kk⟩ ∧
      regsAgree AxRunClose.pinReg rs1 t.regs)
    (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) ?_ rs ib Hag)
  · intro rs1 ib1 d l p' d' HA1 Hp
    obtain ⟨Had, ib2, rfl⟩ := AxSymEngine.silentPs cpu m m1 H rs1 ib1 d l p' d' Hp
    exact ⟨Had, rs1, ib2, rfl, HA1⟩
  · iintro %s2 %HN
    obtain ⟨rs1, ib1, rfl, HA1⟩ := HN
    iapply C $$ %rs1 %ib1 %HA1

include HG Hmid Htext Hflow in
/-- THE BRIDGE, fine row-end form. -/
theorem wpdOfEvA3M (Q : Unit → ExecSt → Prop) (m : SailM Unit) (t : ExecSt) :
    EvA img (fun _ _ => False) Q m t →
    ∀ rs ib k, regsAgree AxRunClose.pinReg rs t.regs →
    ⊢ (∀ t' rs' ib' k', ⌜Q () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu m rs none ib, k⟩ Φ := by
  intro H
  induction H with
  | evRet x t HQ =>
    intro rs ib kk Hag
    iintro C
    iapply C $$ %t %rs %ib %kk %HQ %Hag
  | evExt e k t he => exact he.elim
  | evRd r k t _ _ IHs IHn =>
    intro rs ib kk Hag
    iintro C
    iapply (wpdAdminNode3M M i Φ cpu G HG Hmid _ ?_ kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun s2 => ∃ rs1 ib1, s2 = ⟨.PHart cpu (k (rs1 r)) rs1 none ib1, kk⟩ ∧
        regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs1 ib1 d l p' d' HA1 Hp
      obtain ⟨rfl, rfl⟩ := pstepRdInv cpu r k rs1 ib1 d l p' d' Hp
      exact ⟨trivial, rs1, _, rfl, HA1⟩
    · iintro %s2 %HN
      obtain ⟨rs1, ib1, rfl, HA1⟩ := HN
      by_cases Hs : AxRunClose.pinReg r
      · iapply (IHs Hs (rs1 r) rs1 ib1 kk HA1) $$ C
      · have h := IHn Hs rs1 ib1 kk HA1
        rw [← HA1 r Hs] at h
        iapply h $$ C
  | evWr r v k t Hr _ IH =>
    intro rs ib kk Hag
    iintro C
    iapply (wpdAdminNode3M M i Φ cpu G HG Hmid _ ?_ kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun s2 => ∃ rs1 ib1, s2 = ⟨.PHart cpu (k PUnit.unit) (rs1.set r v) none ib1, kk⟩ ∧
        regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs1 ib1 d l p' d' HA1 Hp
      obtain ⟨Hl, rfl⟩ := pstepWrInv cpu r v k rs1 ib1 d l p' d' Hp
      exact ⟨Hl, rs1, ib1, rfl, HA1⟩
    · iintro %s2 %HN
      obtain ⟨rs1, ib1, rfl, HA1⟩ := HN
      iapply (IH (rs1.set r v) ib1 kk (regsAgreeSet _ _ _ r v HA1)) $$ C
  | evMrd n va req k t vs Hdev Hlat Hvs _ IH =>
    intro rs ib kk Hag
    iintro C
    iapply (wpdMreadNode3M M img i Φ cpu G HG Hmid Htext Hflow n va req k ib kk vs
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hvs) $$ %rs %Hag
    iintro %rs' %HA'
    iapply (IH rs' ib _ HA') $$ C
  | evIa n w k t Hsf _ IH =>
    intro rs ib kk Hag
    iintro C
    iapply (AxSymEngine3.wpdSilentNode3M M i Φ cpu G HG Hmid _ (k ()) ?_ kk t ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs ib d l m' ors fn' d' oib obar h
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := h
      rw [annLabelNot Hsf]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · iintro %rs1 %ib1 %HA1
      iapply (IH rs1 ib1 kk HA1) $$ C
  | evBa _ _ k t _ IH | evCo _ k t _ IH | evTl _ k t _ IH | evTe _ k t _ IH | evRx _ k t _ IH
  | evTs _ k t _ IH | evTx _ k t _ IH | evCc k t _ IH | evMsg _ k t _ IH | evGcc k t _ IH =>
    intro rs ib kk Hag
    iintro C
    iapply (AxSymEngine3.wpdSilentNode3M M i Φ cpu G HG Hmid _ _ ?_ kk t ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs ib d l m' ors fn' d' oib obar h
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := h
      exact ⟨trivial, rfl, rfl, rfl⟩
    · iintro %rs1 %ib1 %HA1
      iapply (IH rs1 ib1 kk HA1) $$ C

include HG in
/-- The instruction boundary, with the boundary's own row-end premise `Hb`. -/
theorem wpdRetNode3M (rs : RegFile) (k : Nat) (s : Athread) (Hs : RetX cpu rs k s)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) :
    ⊢ (∀ s2, ⌜RetNext cpu rs k s2⌝ -∗ wpdM M .MaybeStuck i s2 Φ) -∗
      wpdM M .MaybeStuck i s Φ := by
  have Hnord : ∀ GD s1 id K, G GD → RetX cpu rs k s1 → ¬ areadStep (AxOpsem.grow GD i) s1 id K := by
    rintro GD s1 id K - HP ⟨lb, -, -, Hrd, HK⟩
    obtain ⟨rs1, ib1, rfl, -⟩ := retxShape cpu rs k s1 HP
    obtain ⟨l, d, d', Hl, -, Hps, -⟩ := HK (List.replicate (aidentN id) 0) List.length_replicate
    obtain ⟨rfl, -⟩ := retPstepInv _ _ _ _ _ _ _ Hps
    rw [← Hl] at Hrd
    simp [wlRd] at Hrd
  have Hclos : ∀ GD s1 l s2, G GD → RetX cpu rs k s1 →
      AxOpsem.astepProg (AxOpsem.grow GD i) s1 l s2 → WeakAxRealize.fetchPin GD.gdG.gxImg l →
      wlWdata l = none ∧ s2.atK = s1.atK ∧ (RetX cpu rs k s2 ∨ RetNext cpu rs k s2) := by
    rintro GD s1 l s2 - HP Hst -
    obtain ⟨rs1, ib1, rfl, Hag⟩ := retxShape cpu rs k s1 HP
    obtain ⟨d, d', Hps⟩ := astepProgPstep _ _ _ _ Hst
    obtain ⟨tick, rfl⟩ := astepProgRetShape _ cpu rs1 ib1 k l s2 Hst
    obtain ⟨rfl, -⟩ := retPstepInv _ _ _ _ _ _ _ Hps
    exact ⟨rfl, rfl, .inr ⟨tick, rs1, regsAgreeSym _ _ _ Hag, rfl⟩⟩
  have Hwire : ∀ s1 s2, RetX cpu rs k s1 → awire s1 s2 →
      RetX cpu rs k s2 ∨ RetNext cpu rs k s2 := by
    rintro s1 s2 ⟨ib', Hq⟩ Hw
    exact .inl ⟨ib', aeqvTrans _ _ _ (awireAeqv _ _ Hw) Hq⟩
  iintro Hcont
  iapply (wpdOfClosedRunGM M i G (RetX cpu rs k) (RetNext cpu rs k) Φ HG Hnord Hclos Hwire) $$
    %s %Hs
  isplit
  · iexact Hcont
  · iintro %GD %s1 %HGD %HP %Heq
    iapply (Hb GD s1 HGD HP Heq)

include HG Hmid Htext Hflow in
/-- ONE INSTRUCTION from a `.pure ()` boundary, fine row-end form. -/
theorem wpdInstrOfEvA3M (Q : Unit → ExecSt → Prop) (rs : RegFile) (k : Nat) (s : Athread)
    (Hs : RetX cpu rs k s)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1)
    (Hcert : ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
       EvA img (fun _ _ => False) Q (riscvStep tick) t) :
    ⊢ (∀ t' rs' ib' k', ⌜Q () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM M .MaybeStuck i s Φ := by
  iintro C
  iapply (wpdRetNode3M M i Φ cpu G HG rs k s Hs Hb)
  iintro %s2 %HN
  obtain ⟨tick, rs', Hag, rfl⟩ := HN
  iapply (wpdOfEvA3M M img i Φ cpu G HG Hmid Htext Hflow Q _ ⟨rs', fun _ => none, testDevs⟩
    (Hcert tick ⟨rs', fun _ => none, testDevs⟩ (regsAgreeSym _ _ _ Hag)) rs' ibNone k
    (regsAgreeRefl _ _)) $$ C

end bridge3


/-! ### The riscv.cat instances under the Rocq names (`…3M` at `rvwmoCatConsistent`) -/

section bridge3Cat
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (img : Image) (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
variable (G : Gdexec → Prop)
  (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
  ⊢ postLifting Φ i s)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)

include HG Hmid in
theorem wpdAdminNode3 (m : SailM Unit) (Hm : isNext m) (kk : Nat) (A : RegFile → Prop)
    (N : Athread → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hps : ∀ rs ib d l p' d', A rs → pstepProg (.PHart cpu m rs none ib) d l p' d' →
       lbAdmin true l ∧ N ⟨p', kk⟩) :
    ∀ rs ib, A rs →
    ⊢ (∀ s2, ⌜N s2⌝ -∗ wpd .MaybeStuck i s2 Φ) -∗
      wpd .MaybeStuck i ⟨.PHart cpu m rs none ib, kk⟩ Φ :=
  wpdAdminNode3M rvwmoCatConsistent i Φ cpu G HG Hmid m Hm kk A N HA Hps

include HG Hmid Htext Hflow in
theorem wpdMreadNode3 (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (vs : List (BitVec 8)) (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hvs : imgBytes img (paZ req.pa) n = some vs) :
    ⊢ ∀ rs, ⌜A rs⌝ -∗
      (∀ rs', ⌜A rs'⌝ -∗
         wpd .MaybeStuck i ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs' none ib,
           AxSymEngine.rdNext req k⟩ Φ) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ Φ :=
  wpdMreadNode3M rvwmoCatConsistent img i Φ cpu G HG Hmid Htext Hflow n va req KK ib k vs A HA
    Hdev Hlat Hvs

include HG Hmid Htext Hflow in
theorem wpdOfEvA3 (Q : Unit → ExecSt → Prop) (m : SailM Unit) (t : ExecSt)
    (H : EvA img (fun _ _ => False) Q m t) :
    ∀ rs ib k, regsAgree AxRunClose.pinReg rs t.regs →
    ⊢ (∀ t' rs' ib' k', ⌜Q () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         wpd .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpd .MaybeStuck i ⟨.PHart cpu m rs none ib, k⟩ Φ :=
  wpdOfEvA3M rvwmoCatConsistent img i Φ cpu G HG Hmid Htext Hflow Q m t H

include HG in
theorem wpdRetNode3 (rs : RegFile) (k : Nat) (s : Athread) (Hs : RetX cpu rs k s)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) :
    ⊢ (∀ s2, ⌜RetNext cpu rs k s2⌝ -∗ wpd .MaybeStuck i s2 Φ) -∗
      wpd .MaybeStuck i s Φ :=
  wpdRetNode3M rvwmoCatConsistent i Φ cpu G HG rs k s Hs Hb

include HG Hmid Htext Hflow in
theorem wpdInstrOfEvA3 (Q : Unit → ExecSt → Prop) (rs : RegFile) (k : Nat) (s : Athread)
    (Hs : RetX cpu rs k s)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1)
    (Hcert : ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
       EvA img (fun _ _ => False) Q (riscvStep tick) t) :
    ⊢ (∀ t' rs' ib' k', ⌜Q () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         wpd .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpd .MaybeStuck i s Φ :=
  wpdInstrOfEvA3M rvwmoCatConsistent img i Φ cpu G HG Hmid Htext Hflow Q rs k s Hs Hb Hcert

end bridge3Cat


/-! # 3. X for BOTH arms and ANY post `Φ` with the fine row-end premises -/

section xgenDef
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- `AxReuseProbe2.XGprWrite` with `Φ0` generalised to `Φ`: the START-boundary row-end obligation
is an explicit premise. -/
def XGprWriteΦ (i : Agent) (cpu : CPU) (ctrlOk : RegFile → Prop)
    (textOk : BitVec 64 → Bool → instruction → Prop) (G : Gdexec → Prop)
    (Φ : Athread → IProp GF) : Prop :=
  ∀ (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (ins : instruction) (rd : BitVec 5) (wval : BitVec 64),
    RetX cpu rs k s → ctrlOk rs → rs .PC = pc →
    textOk pc is_rvc ins → rd.toNat ≠ 0 →
    (∀ s_pc : ExecSt,
       s_pc.regs .nextPC = pc + instrLen is_rvc →
       gprAgree s_pc.regs rs →
       exec (execute ins) s_pc = some (RETIRE_SUCCESS, s_pc.setGpr rd wval)) →
    (∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) →
    ⊢ (∀ s' rs' k',
         ⌜RetX cpu rs' k' s'⌝ -∗ ⌜ctrlOk rs'⌝ -∗
         ⌜rs' .PC = pc + instrLen is_rvc⌝ -∗
         ⌜∀ r : BitVec 5, r.toNat ≠ 0 →
            uxaXget rs' r = if r = rd then wval else uxaXget rs r⌝ -∗
         wpd .MaybeStuck i s' Φ) -∗
       wpd .MaybeStuck i s Φ

end xgenDef

section xgen
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (img : Image) (i : Agent) (cpu : CPU)
variable (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
  (textAt4 : BitVec 64 → BitVec 32 → Prop)
variable (Hsp : SpineOk img ctrlOk textAt) (Hf4 : SpineFetch4 img ctrlOk textAt4)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)

include Hsp Hf4 Htext Hflow in
theorem XGprWriteΦHolds (G : Gdexec → Prop)
    (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
    (Φ : Athread → IProp GF)
    (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s) :
    XGprWriteΦ i cpu ctrlOk (textOkDB img ctrlOk textAt textAt4) G Φ := by
  unfold XGprWriteΦ
  intro s rs k pc is_rvc ins rd wval HRet Hctrl HPC Htx Hrd Hcert Hb
  have Hcert' : ∀ s_pc : ExecSt,
      s_pc.regs .nextPC = BitVec.addInt pc (if is_rvc then 2 else 4) →
      gprAgree s_pc.regs rs →
      exec (execute ins) s_pc = some (RETIRE_SUCCESS, s_pc.setGpr rd wval) := by
    intro s_pc h1 h2
    exact Hcert s_pc (by cases is_rvc <;> exact h1) h2
  iintro C
  iapply (wpdInstrOfEvA3 img i Φ cpu G HG Hmid Htext Hflow
    (fun _ t' => GoodN ctrlOk is_rvc rs pc rd wval t'.regs) rs k s HRet Hb
    (AxSymEngine3.spineCertB img ctrlOk textAt textAt4 Hsp Hf4 rs pc is_rvc ins rd wval Hctrl
      HPC Htx Hrd Hcert'))
  iintro %t' %rs' %ib' %k' %HG %Hag
  obtain ⟨Hc, Hpc, Hg⟩ := HG
  have HRet' : RetX cpu rs' k' ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ :=
    ⟨ib', rfl, rfl, rfl, rfl, rfl, regsAgreeRefl _ _⟩
  have Hc' : ctrlOk rs' := Hsp.spSeip _ _ Hc Hag
  have Hpc' : rs' .PC = pc + instrLen is_rvc :=
    (Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))).trans
      (by cases is_rvc <;> exact Hpc)
  have Hg' : ∀ r : BitVec 5, r.toNat ≠ 0 →
      uxaXget rs' r = if r = rd then wval else uxaXget rs r :=
    fun r Hr => (AxSymEngine2.uxaXgetAgree _ _ Hag r).trans (Hg r Hr)
  iapply C $$ %_ %rs' %k' %HRet' %Hc' %Hpc' %Hg'

include Hsp Hf4 Htext Hflow in
/-- Slice 1's X, now for BOTH arms (`is_rvc = false` included). -/
theorem XGprWriteHoldsB : XGprWrite (GF := GF) i cpu ctrlOk (textOkDB img ctrlOk textAt textAt4) := by
  intro s rs k pc is_rvc ins rd wval HRet Hctrl HPC Htx Hrd Hcert
  exact XGprWriteΦHolds img i cpu ctrlOk textAt textAt4 Hsp Hf4 Htext Hflow (fun _ => True)
    (fun _ _ => BI.pure_intro trivial) Φ0 (fun _ s _ _ _ => postLiftingΦ0 i s)
    s rs k pc is_rvc ins rd wval HRet Hctrl HPC Htx Hrd Hcert
    (fun _ s1 _ _ _ => postLiftingΦ0 i s1)

end xgen

/-! # 4. The leaves over any `Φ`; the 4-byte `add` leaf; a REAL post -/

/-- The boundary-indexed post: at every `.pure ()` boundary the registers satisfy `P`. -/
def ΦRet {GF : BundledGFunctors} (cpu : CPU) (P : RegFile → Prop) : Athread → IProp GF :=
  fun s => iprop(⌜∀ rs k, RetX cpu rs k s → P rs⌝)

theorem ΦRetMid {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF]
    (i : Agent) (cpu : CPU) (P : RegFile → Prop) (G : Gdexec → Prop) :
    ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting (ΦRet (GF := GF) cpu P) i s := by
  intro GD s _ Hm _
  refine postLiftingTrue _ i s ?_
  unfold ΦRet
  refine BI.pure_intro ?_
  intro rs k HR
  obtain ⟨rs1, ib1, rfl, -⟩ := retxShape cpu rs k s HR
  exact Hm.elim

/-- At a boundary the post is `P` of the (pin-insensitive) registers. -/
theorem ΦRetBoundary {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF]
    (i : Agent) (cpu : CPU) (P : RegFile → Prop) (rs : RegFile) (k : Nat) (s1 : Athread) :
    (∀ rs', regsAgree AxRunClose.pinReg rs' rs → P rs') → RetX cpu rs k s1 →
      ⊢ postLifting (ΦRet (GF := GF) cpu P) i s1 := by
  intro HP HR
  refine postLiftingTrue _ i s1 ?_
  unfold ΦRet
  refine BI.pure_intro ?_
  intro rs' k' HR'
  apply HP
  obtain ⟨rs1, ib1, rfl, Hag1⟩ := retxShape cpu rs k s1 HR
  obtain ⟨rs2, ib2, E, Hag2⟩ := retxShape cpu rs' k' _ HR'
  cases E
  exact regsAgreeTrans _ _ _ _ (regsAgreeSym _ _ _ Hag2) Hag1

section leaves
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64)]
variable (i : Agent) (cid cpu : CPU) (γm γp : GName)
variable (ctrlOk : RegFile → Prop) (textOk : BitVec 64 → Bool → instruction → Prop)
variable (G : Gdexec → Prop)

/-- `AxReuseProbe2.goalD` with `Φ0` ↦ `Φ`. -/
def goalDΦ (Φ : Athread → IProp GF) : IProp GF :=
  iprop(∀ s m pc, ⌜cur cid cpu ctrlOk m pc s⌝ -∗ ghost_var γm (.own (1 : Qp).half) m -∗
    ghost_var γp (.own (1 : Qp).half) pc -∗ wpd .MaybeStuck i s Φ)

theorem goalDΦΦ0 : goalDΦ (GF := GF) i cid cpu γm γp ctrlOk Φ0 ⊣⊢ goalD i cid cpu γm γp ctrlOk := .rfl

/-- `AxReuseProbe2.wpGprWriteD` for either arm and any `Φ`; the new premise `Hb`. -/
theorem wpGprWriteDΦ (Φ : Athread → IProp GF) (HX : XGprWriteΦ i cpu ctrlOk textOk G Φ)
    (is_rvc : Bool) (pc : BitVec 64) (rd rsa rsb : BitVec 5) (base : instruction)
    (wval : BitVec 64) (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64)
    (Hb : ∀ GD s1 rs k, G GD → RetX cpu rs k s1 → ctrlOk rs → gprRel cid m rs →
       rs .PC = pc → s1.atK = (AxOpsem.grow GD i).length → ⊢ postLifting Φ i s1) :
    rd.toNat ≠ 0 →
    MachCSL.rdOk rd →
    (∀ s_pc : ExecSt,
       s_pc.regs .nextPC = pc + instrLen is_rvc →
       s_pc.gpr rsa = rget cid m rsa →
       s_pc.gpr rsb = rget cid m rsb →
       exec (execute base) s_pc = some (RETIRE_SUCCESS, s_pc.setGpr rd wval)) →
    ⊢ sieCapD (GF := GF) γm cid m n b p -∗
      pcIsD (GF := GF) γp pc -∗
      instrD (GF := GF) textOk pc is_rvc base -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCapD γm cpu' (m.set rd wval) n b p -∗
        pcIsD γp (pc + instrLen is_rvc) -∗
        goalDΦ i cid cpu γm γp ctrlOk Φ)) -∗
      goalDΦ i cid cpu γm γp ctrlOk Φ := by
  intro Hrd Hrdok Hbexec
  unfold sieCapD pcIsD instrD
  iintro ⟨%Hb0, Hm⟩ Hp %Htext Hcont
  subst Hb0
  ihave Hcont := wpNext_off p cid _ $$ Hcont
  unfold goalDΦ
  iintro %s %m' %pc' %Hcur Hm' Hp'
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2
  obtain ⟨rs, k, HRet, Hctrl, Hrel, HPC⟩ := Hcur
  have Hsrc : ∀ (s_pc : ExecSt) (r : BitVec 5), gprAgree s_pc.regs rs →
      s_pc.gpr r = rget cid m r := by
    intro s_pc r Hag
    rw [← Hrel r]
    show uxaXget s_pc.regs r = uxaXget rs r
    by_cases h0 : r.toNat = 0
    · rw [AxReuseProbe2.uxaXgetZero _ r h0, AxReuseProbe2.uxaXgetZero _ r h0]
    · exact Hag r h0
  have HXi := HX s rs k pc is_rvc base rd wval HRet Hctrl HPC Htext Hrd
    (fun s_pc Hnpc Hag => Hbexec s_pc Hnpc (Hsrc s_pc rsa Hag) (Hsrc s_pc rsb Hag))
    (fun GD s1 HG HR Heq => Hb GD s1 rs k HG HR Hctrl Hrel HPC Heq)
  iapply HXi
  iintro %s' %rs' %k' %HRet' %Hctrl' %HPC' %Hgpr
  iapply bupdWpd
  imod ghost_var_update_halves (m.set rd wval) γm m m $$ Hm Hm' with ⟨Hm, Hm'⟩
  imod ghost_var_update_halves (pc + instrLen is_rvc) γp pc pc $$ Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  have Hcur' : cur cid cpu ctrlOk (m.set rd wval) (pc + instrLen is_rvc) s' :=
    ⟨rs', k', HRet', Hctrl', gprRelUpd cid m rs rs' rd wval Hrel Hrd Hrdok.2.2 Hgpr, HPC'⟩
  iapply Hcont $$ [Hm] Hp %s' %(m.set rd wval) %(pc + instrLen is_rvc) %Hcur' Hm' Hp'
  isplitr
  · ipureintro; rfl
  · iexact Hm

/-- c.mv over any `Φ`. -/
theorem wpCmvDΦ (Φ : Athread → IProp GF) (HX : XGprWriteΦ i cpu ctrlOk textOk G Φ)
    (pc : BitVec 64) (rd rs2 : BitVec 5) (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64)
    (Hb : ∀ GD s1 rs k, G GD → RetX cpu rs k s1 → ctrlOk rs → gprRel cid m rs →
       rs .PC = pc → s1.atK = (AxOpsem.grow GD i).length → ⊢ postLifting Φ i s1) :
    rd.toNat ≠ 0 →
    MachCSL.rdOk rd →
    ⊢ sieCapD (GF := GF) γm cid m n b p -∗
      pcIsD (GF := GF) γp pc -∗
      instrD (GF := GF) textOk pc true (.RTYPE (.Regidx rs2, zreg, .Regidx rd, .ADD)) -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCapD γm cpu' (m.set rd (0#64 + rget cid m rs2)) n b p -∗
        pcIsD γp (pc + 2#64) -∗
        goalDΦ i cid cpu γm γp ctrlOk Φ)) -∗
      goalDΦ i cid cpu γm γp ctrlOk Φ := by
  intro Hrd Hrdok
  refine wpGprWriteDΦ i cid cpu γm γp ctrlOk textOk G Φ HX true pc rd rs2 rs2
    (.RTYPE (.Regidx rs2, zreg, .Regidx rd, .ADD)) (0#64 + rget cid m rs2) m n b p Hb Hrd Hrdok ?_
  intro s_pc _ Hva _
  show exec (execute_RTYPE (.Regidx rs2) (.Regidx 0#5) (.Regidx rd) .ADD) s_pc = _
  rw [execExecuteRTYPEADDGpr rs2 0#5 rd s_pc]
  unfold gprRdVal
  rw [Hva]
  rfl

/-- c.addiw over any `Φ`. -/
theorem wpCaddiwDΦ (Φ : Athread → IProp GF) (HX : XGprWriteΦ i cpu ctrlOk textOk G Φ)
    (pc : BitVec 64) (rd : BitVec 5) (imm : BitVec 6) (m : RegMap) (n : Nat) (b : Bool)
    (p : BitVec 64)
    (Hb : ∀ GD s1 rs k, G GD → RetX cpu rs k s1 → ctrlOk rs → gprRel cid m rs →
       rs .PC = pc → s1.atK = (AxOpsem.grow GD i).length → ⊢ postLifting Φ i s1) :
    rd.toNat ≠ 0 →
    MachCSL.rdOk rd →
    ⊢ sieCapD (GF := GF) γm cid m n b p -∗
      pcIsD (GF := GF) γp pc -∗
      instrD (GF := GF) textOk pc true (.ADDIW (sign_extend (m := 12) imm, .Regidx rd, .Regidx rd)) -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCapD γm cpu' (m.set rd (sign_extend (m := 64) (Sail.BitVec.extractLsb
          (rget cid m rd + sign_extend (m := 64) (sign_extend (m := 12) imm)) 31 0))) n b p -∗
        pcIsD γp (pc + 2#64) -∗
        goalDΦ i cid cpu γm γp ctrlOk Φ)) -∗
      goalDΦ i cid cpu γm γp ctrlOk Φ := by
  intro Hrd Hrdok
  refine wpGprWriteDΦ i cid cpu γm γp ctrlOk textOk G Φ HX true pc rd rd rd
    (.ADDIW (sign_extend (m := 12) imm, .Regidx rd, .Regidx rd)) _ m n b p Hb Hrd Hrdok ?_
  intro s_pc _ Hva _
  rw [execExecuteADDIWGpr rd rd (sign_extend (m := 12) imm) s_pc]
  unfold gprAddiwVal
  rw [Hva]

/-- THE 4-BYTE LEAF: `add rd, rs1, rs2` (RTYPE ADD, `F_Base` arm, pc+4). -/
theorem wpAddDΦ (Φ : Athread → IProp GF) (HX : XGprWriteΦ i cpu ctrlOk textOk G Φ)
    (pc : BitVec 64) (rd rs1 rs2 : BitVec 5) (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64)
    (Hb : ∀ GD s1 rs k, G GD → RetX cpu rs k s1 → ctrlOk rs → gprRel cid m rs →
       rs .PC = pc → s1.atK = (AxOpsem.grow GD i).length → ⊢ postLifting Φ i s1) :
    rd.toNat ≠ 0 →
    MachCSL.rdOk rd →
    ⊢ sieCapD (GF := GF) γm cid m n b p -∗
      pcIsD (GF := GF) γp pc -∗
      instrD (GF := GF) textOk pc false (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .ADD)) -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCapD γm cpu' (m.set rd (rget cid m rs1 + rget cid m rs2)) n b p -∗
        pcIsD γp (pc + instrLen false) -∗
        goalDΦ i cid cpu γm γp ctrlOk Φ)) -∗
      goalDΦ i cid cpu γm γp ctrlOk Φ := by
  intro Hrd Hrdok
  refine wpGprWriteDΦ i cid cpu γm γp ctrlOk textOk G Φ HX false pc rd rs1 rs2
    (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .ADD)) (rget cid m rs1 + rget cid m rs2)
    m n b p Hb Hrd Hrdok ?_
  intro s_pc _ Hva Hvb
  show exec (execute_RTYPE (.Regidx rs2) (.Regidx rs1) (.Regidx rd) .ADD) s_pc = _
  rw [execExecuteRTYPEADDGpr rs2 rs1 rd s_pc]
  unfold gprRdVal
  rw [Hva, Hvb]

end leaves

/-! The REAL leaves: X discharged, at the engine's instance premises. -/

section real
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64)]
variable (img : Image) (i : Agent) (cid cpu : CPU) (γm γp : GName)
variable (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
  (textAt4 : BitVec 64 → BitVec 32 → Prop)
variable (Hsp : SpineOk img ctrlOk textAt) (Hf4 : SpineFetch4 img ctrlOk textAt4)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)

include Hsp Hf4 Htext Hflow in
/-- Slice 1's c.mv leaf through the both-arm engine. -/
theorem wpCmvDRealB (pc : BitVec 64) (rd rs2 : BitVec 5)
    (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) :
    rd.toNat ≠ 0 →
    MachCSL.rdOk rd →
    ⊢ sieCapD (GF := GF) γm cid m n b p -∗
      pcIsD (GF := GF) γp pc -∗
      instrD (GF := GF) (textOkDB img ctrlOk textAt textAt4) pc true
        (.RTYPE (.Regidx rs2, zreg, .Regidx rd, .ADD)) -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCapD γm cpu' (m.set rd (0#64 + rget cid m rs2)) n b p -∗
        pcIsD γp (pc + 2#64) -∗
        goalD i cid cpu γm γp ctrlOk)) -∗
      goalD i cid cpu γm γp ctrlOk :=
  wpCmvD i cid cpu γm γp ctrlOk (textOkDB img ctrlOk textAt textAt4)
    (XGprWriteHoldsB img i cpu ctrlOk textAt textAt4 Hsp Hf4 Htext Hflow) pc rd rs2 m n b p

include Hsp Hf4 Htext Hflow in
/-- The 4-byte add leaf at `Φ0`. -/
theorem wpAddDReal (pc : BitVec 64) (rd rs1 rs2 : BitVec 5)
    (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) :
    rd.toNat ≠ 0 →
    MachCSL.rdOk rd →
    ⊢ sieCapD (GF := GF) γm cid m n b p -∗
      pcIsD (GF := GF) γp pc -∗
      instrD (GF := GF) (textOkDB img ctrlOk textAt textAt4) pc false
        (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .ADD)) -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCapD γm cpu' (m.set rd (rget cid m rs1 + rget cid m rs2)) n b p -∗
        pcIsD γp (pc + instrLen false) -∗
        goalD i cid cpu γm γp ctrlOk)) -∗
      goalD i cid cpu γm γp ctrlOk :=
  wpAddDΦ i cid cpu γm γp ctrlOk (textOkDB img ctrlOk textAt textAt4) (fun _ => True) Φ0
    (XGprWriteΦHolds img i cpu ctrlOk textAt textAt4 Hsp Hf4 Htext Hflow (fun _ => True)
      (fun _ _ => BI.pure_intro trivial) Φ0 (fun _ s _ _ _ => postLiftingΦ0 i s))
    pc rd rs1 rs2 m n b p (fun _ s1 _ _ _ _ _ _ _ _ => postLiftingΦ0 i s1)

include Hsp Hf4 Htext Hflow in
/-- c.mv with a REAL post `ΦRet P`; the one extra obligation is `P` at THIS instruction's own
boundary. -/
theorem wpCmvDRealPost (P : RegFile → Prop) (pc : BitVec 64) (rd rs2 : BitVec 5)
    (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64)
    (HPb : ∀ rs rs', ctrlOk rs → gprRel cid m rs → rs .PC = pc →
       regsAgree AxRunClose.pinReg rs' rs → P rs') :
    rd.toNat ≠ 0 →
    MachCSL.rdOk rd →
    ⊢ sieCapD (GF := GF) γm cid m n b p -∗
      pcIsD (GF := GF) γp pc -∗
      instrD (GF := GF) (textOkDB img ctrlOk textAt textAt4) pc true
        (.RTYPE (.Regidx rs2, zreg, .Regidx rd, .ADD)) -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCapD γm cpu' (m.set rd (0#64 + rget cid m rs2)) n b p -∗
        pcIsD γp (pc + 2#64) -∗
        goalDΦ i cid cpu γm γp ctrlOk (ΦRet cpu P))) -∗
      goalDΦ i cid cpu γm γp ctrlOk (ΦRet cpu P) :=
  wpCmvDΦ i cid cpu γm γp ctrlOk (textOkDB img ctrlOk textAt textAt4) (fun _ => True)
    (ΦRet cpu P)
    (XGprWriteΦHolds img i cpu ctrlOk textAt textAt4 Hsp Hf4 Htext Hflow (fun _ => True)
      (fun _ _ => BI.pure_intro trivial) (ΦRet cpu P) (ΦRetMid i cpu P _))
    pc rd rs2 m n b p
    (fun _ s1 rs k _ HR Hc Hrel HPC _ =>
      ΦRetBoundary i cpu P rs k s1 (fun rs' Hag => HPb rs rs' Hc Hrel HPC Hag) HR)

end real

end Weak
