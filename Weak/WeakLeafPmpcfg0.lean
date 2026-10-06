/-
Weak: **the csrw-pmpcfg0 leaf on `WeakFunnelCfg.wwpInstrConfig`** (M4).

Rocq: `iris/WeakLeafPmpcfg0.v` @ xxvzwolszwmp.

The Rocq header, in substance.  The second CONFIG-WRITING csrw leaf (the weak
twin of `WpGprCsrwC.wp_csrw_pmpcfg0_raw`): `csrw pmpcfg0` (0x3a0) writes the
`pmpcfg_n` cell the plain funnel HOLDS across the step, so -- like
`WeakLeafCsrw.wwpCsrwMstatusLeaf` -- it goes through the config-variant funnel
`WeakFunnelCfg.wwpInstrConfig`, which surrenders `cur_privilege` / `mstatus` /
`pmpcfg_n` into the callback at FULL ownership.  Everything else is the
register-only recipe: a certificate at `WeakLeafRegOnly.wcertRegonly` /
`wQPure` over the fetch-only trace `regonlyEs al4 pc`, so no memory arms
appear anywhere and the leaf is alignment-generic (`al4` a parameter).
* §1 the `execEff` mirrors of the csrw-pmpcfg0 `execute` cone, at the empty
  trace.  The SC VALUE plumbing (`ExecSC9.pmpWriteCfgVal` / `pmpCfgStep` /
  `pmpcfg0Final`) is reused; the CSR-generic `doCSR`/`execute_CSRReg` spine is
  `WeakLeafCsrw` §1f's, the check dispatcher `WeakLeafRegOnly` §3's.
* §2 the leaf `wwpCsrwPmpcfg0Leaf`: statement = `wp_csrw_pmpcfg0_raw` under
  the porting-table swaps plus the alignment bit `al4`, driven through
  `wwpInstrConfig`.

**Deviations from Rocq.**
1. VOCABULARY: as `Weak/WeakLeafCsrw.lean` deviation 1 (`register_lookup r
   s.(sregs)` ↦ `s.regs r`, `mword n` ↦ `BitVec n`, `set_reg` ↦
   `ExecSt.setReg`, `uint` ↦ `.toNat`, the x0-guarded GPR read ↦ `s.gpr rs1`,
   `csr_pmpcfg0` ↦ the literal `0x3A0#12`, …).
2. The SC pieces Rocq reuses from `WpGprCsrwA`/`WpGprCsrwC` that the Lean tree
   lacks (`ExecSC9` ported only `pmpWriteCfg_val`/`pmp_cfg_step`/
   `pmpcfg0_final`) are defined here, Lean-only and file-qualified:
   `WeakLeafPmpcfg0.pmpcfg0Readback` (indices as `Nat`),
   `WeakLeafPmpcfg0.pmpcfg0Vecupd`, `WeakLeafPmpcfg0.pmpcfgWritten`,
   `WeakLeafPmpcfg0.pmpCfgStepOnSet`, `WeakLeafPmpcfg0.pmpcfg0FinalSet`.
3. §1b: Rocq's Ltac `do_cfg_step_eff` unrolls `foreach_ZM_up'` eight times;
   Lean's loop is lean-sail's `IntRange` `forIn`, run by the Lean-only
   invariant rule `WeakLeafPmpcfg0.execEffForInInv` (the `execEff` twin of
   `ExecSC9.execForInInv`, trace `[]`), whose per-index body obligation is
   what `do_cfg_step_eff` proved.  The Ltac itself is not ported.
4. §1d: Lean's `write_CSR` arm is MachCSL's `write_CSR_pmpcfg0` equation (no
   `skip_csr_false_clauses_eff` peel; as `WeakLeafCsrw` deviation 3).
5. THE LEAF: as `WeakLeafCsrw` deviation 5 (config interface of
   `WeakFunnelCfg`, owner decision Q3: `hwConfig cpu ⊢ clockCells cpu -∗ …`,
   the continuation also receives `clockCells cpu`; `WWP Loop` ↦ `wwpTriv ⊤
   (WExpr.loop gen cpu)`; the operand cell is `gpr cpu rs1 (DFrac.own 1)
   rs1v`).  The certificate's fetch obligation `fetchPin` (O2) is discharged
   from `winstrTextPinned` via `WeakAcquire.fetchPinOfText` with the
   Lean-only `WeakLeafPmpcfg0.fetchInWindowRegonly`/`fetchFreshRegonly`.
6. Rocq §3's `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  `exec_eff_pmpWriteCfg` `execEffPmpWriteCfg`,
`exec_eff_pmpWriteCfgReg_0` `execEffPmpWriteCfgReg0`, `exec_eff_pmpReadCfgReg_0`
`execEffPmpReadCfgReg0`, `exec_eff_write_CSR_pmpcfg0` `execEffWriteCSRPmpcfg0`,
`exec_eff_csr_id_write_callback_pmpcfg0` `execEffCsrIdWriteCallbackPmpcfg0`,
`exec_eff_check_CSR_result_csrw_pmpcfg0` `execEffCheckCSRResultCsrwPmpcfg0`,
`exec_eff_execute_csrw_pmpcfg0` `execEffExecuteCsrwPmpcfg0`,
`wwp_csrw_pmpcfg0_leaf` `wwpCsrwPmpcfg0Leaf` (none in the duplicated-name
table); `do_cfg_step_eff` (Ltac) not ported (deviation 3).  Lean-only
(file-qualified): deviation 2's five, `WeakLeafPmpcfg0.execEffForInInv`,
`WeakLeafPmpcfg0.execEffAt` (the shared core of the leaf's confined and flat
runs), `WeakLeafPmpcfg0.fetchInWindowRegonly`,
`WeakLeafPmpcfg0.fetchFreshRegonly`, `WeakLeafPmpcfg0.execEffItePure`.  GPR-cell agreement is
`WeakLeafLw4.gprValid`, the GPR frame `WeakLeafCsrw.gprSetRegNe` (reused).

**Dropped:** nothing (8 Rocq `Lemma`s + 1 `Ltac`; Lean 8 theorems + 10
Lean-only).
-/
import Weak.WeakLeafCsrw
import Weak.WeakLeafRegOnly
import Weak.ExecSC9

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 0. The SC value plumbing the Lean tree lacks (deviation 2) -/

/-- Rocq `WpGprCsrwA.pmpcfg0_readback` (Lean-only here): the value `pmpReadCfgReg 0`
returns. -/
def WeakLeafPmpcfg0.pmpcfg0Readback (cfg : Vector (BitVec 8) 64) : BitVec 64 :=
  cfg[7]! ++ (cfg[6]! ++ (cfg[5]! ++ (cfg[4]! ++ (cfg[3]! ++ (cfg[2]! ++ (cfg[1]! ++ cfg[0]!))))))

/-- Rocq `WpGprCsrwA.pmpcfg0_vecupd` (Lean-only here). -/
def WeakLeafPmpcfg0.pmpcfg0Vecupd (v : BitVec 64) (cfg : Vector (BitVec 8) 64) (i : Nat) :
    Vector (BitVec 8) 64 :=
  vectorUpdate cfg i (pmpWriteCfgVal cfg[i]! (Sail.BitVec.extractLsb v (8 * i + 7) (8 * i)))

/-- Rocq `WpGprCsrwC.pmpcfg_written` (Lean-only here): the pmpcfg vector after
`csrw pmpcfg0, v`. -/
def WeakLeafPmpcfg0.pmpcfgWritten (v : BitVec 64) (cfg : RegisterType .pmpcfg_n) :
    RegisterType .pmpcfg_n :=
  WeakLeafPmpcfg0.pmpcfg0Vecupd v (WeakLeafPmpcfg0.pmpcfg0Vecupd v (WeakLeafPmpcfg0.pmpcfg0Vecupd v
    (WeakLeafPmpcfg0.pmpcfg0Vecupd v (WeakLeafPmpcfg0.pmpcfg0Vecupd v (WeakLeafPmpcfg0.pmpcfg0Vecupd v
      (WeakLeafPmpcfg0.pmpcfg0Vecupd v (WeakLeafPmpcfg0.pmpcfg0Vecupd v cfg 0) 1) 2) 3) 4) 5) 6) 7

/-- Rocq `WpGprCsrwA.pmp_cfg_step_on_set` (Lean-only here). -/
theorem WeakLeafPmpcfg0.pmpCfgStepOnSet (v : BitVec 64) (s : ExecSt) (X : Vector (BitVec 8) 64)
    (i : Nat) :
    pmpCfgStep v (s.setReg .pmpcfg_n X) i =
      s.setReg .pmpcfg_n (WeakLeafPmpcfg0.pmpcfg0Vecupd v X i) := by
  unfold pmpCfgStep WeakLeafPmpcfg0.pmpcfg0Vecupd
  simp only [ExecSt.setReg_regs, RegFile.set_same, ExecSt.setReg_setReg_same]

/-- Rocq `WpGprCsrwC.pmpcfg0_final_set` (Lean-only here). -/
theorem WeakLeafPmpcfg0.pmpcfg0FinalSet (v : BitVec 64) (s : ExecSt) :
    pmpcfg0Final v s = s.setReg .pmpcfg_n (WeakLeafPmpcfg0.pmpcfgWritten v (s.regs .pmpcfg_n)) := by
  have h0 : pmpCfgStep v s 0 =
      s.setReg .pmpcfg_n (WeakLeafPmpcfg0.pmpcfg0Vecupd v (s.regs .pmpcfg_n) 0) := rfl
  unfold pmpcfg0Final WeakLeafPmpcfg0.pmpcfgWritten
  rw [h0]
  simp only [WeakLeafPmpcfg0.pmpCfgStepOnSet]

/-! ## 1. THE `execEff` MIRROR OF THE csrw-pmpcfg0 CONE (trace `[]`) -/

/-! ### 1a. The per-byte write -/

/-- A pure two-way branch at the empty trace (Lean-only). -/
theorem WeakLeafPmpcfg0.execEffItePure {X : Type} (c : Prop) [Decidable c] (a b : X) (s : ExecSt) :
    execEff (if c then (pure a : SailM X) else pure b) s = some (if c then a else b, s, []) := by
  split <;> rfl

/-- Rocq `exec_eff_pmpWriteCfg`. -/
theorem execEffPmpWriteCfg (cfg v : BitVec 8) (s : ExecSt) :
    execEff (pmpWriteCfg cfg v) s = some (pmpWriteCfgVal cfg v, s, []) := by
  unfold pmpWriteCfg pmpWriteCfgVal
  cases hl : pmpLocked cfg
  · cases hw : ((_get_Pmpcfg_ent_W (Mk_Pmpcfg_ent (v &&& 0x9F#8)) == 1#1) &&
        (_get_Pmpcfg_ent_R (Mk_Pmpcfg_ent (v &&& 0x9F#8)) == 0#1)) <;>
    exec_eff_steps [hw, pmp_write_only_reserved_behavior, WeakLeafPmpcfg0.execEffItePure] <;> rfl
  · rfl

/-! ### 1b. The 8-iteration loop (deviation 3) -/

/-- The `execEff` twin of `ExecSC9.execForInInv`: a unit-state loop (step 1)
with a state invariant, every body run at the empty trace (Lean-only). -/
theorem WeakLeafPmpcfg0.execEffForInInv (range : IntRange) (hstep : range.step = 1)
    (f : Int → Unit → SailM (ForInStep Unit))
    (P : Int → ExecSt → Prop) (s : ExecSt) (hP0 : P range.start s) (hle : range.start ≤ range.stop + 1)
    (hf : ∀ i st, i ∈ range → P i st →
      ∃ st', execEff (f i ()) st = some (.yield (), st', []) ∧ P (i + 1) st') :
    ∃ st', execEff (forIn range () f) s = some ((), st', []) ∧ P (range.stop + 1) st' := by
  show ∃ st', execEff (IntRange.forIn'.loop range (fun a _ b => f a b) () range.start (by simp)) s = _ ∧ _
  suffices H : ∀ (n : Nat) (i : Int) (hs : (i - range.start) % range.step = 0) (st : ExecSt),
      (range.stop - i + 1).toNat = n → range.start ≤ i → i ≤ range.stop + 1 → P i st →
      ∃ st', execEff (IntRange.forIn'.loop range (fun a _ b => f a b) () i hs) st = some ((), st', []) ∧
        P (range.stop + 1) st' from
    H _ _ _ s rfl (Int.le_refl _) hle hP0
  intro n
  induction n with
  | zero =>
    intro i hs st hn hge hi hP
    rw [IntRange.loop_unfold]
    have hni : ¬ i ∈ range := by
      intro h
      simp only [Membership.mem, hstep, show (1 : Int) > 0 from by decide, ite_true] at h
      have := Int.toNat_eq_zero.mp hn
      omega
    simp only [dif_neg hni]
    have : i = range.stop + 1 := by
      have := Int.toNat_eq_zero.mp hn
      omega
    subst this
    exact ⟨st, rfl, hP⟩
  | succ n ih =>
    intro i hs st hn hge hi hP
    rw [IntRange.loop_unfold]
    by_cases h : i ∈ range
    · simp only [dif_pos h]
      obtain ⟨st', he, hP'⟩ := hf i st h hP
      rw [execEffBindNil _ _ _ _ _ he]
      simp only [Membership.mem, hstep, show (1 : Int) > 0 from by decide, ite_true] at h
      have hn' : (range.stop - (i + range.step) + 1).toNat = n := by
        rw [hstep]
        omega
      have hi' : i + range.step ≤ range.stop + 1 := by rw [hstep]; omega
      exact ih _ _ st' hn' (by rw [hstep]; omega) hi' (by rw [hstep]; exact hP')
    · simp only [dif_neg h]
      have : i = range.stop + 1 := by
        simp only [Membership.mem, hstep, show (1 : Int) > 0 from by decide, ite_true] at h
        omega
      subst this
      exact ⟨st, rfl, hP⟩

/-- Rocq `exec_eff_pmpWriteCfgReg_0`. -/
theorem execEffPmpWriteCfgReg0 (v : BitVec 64) (s : ExecSt) :
    execEff (pmpWriteCfgReg 0 v) s = some ((), pmpcfg0Final v s, []) := by
  unfold pmpWriteCfgReg
  exec_eff_steps
  generalize hx : execEff (forIn (m := SailM) (_ : IntRange) () _) s = x
  obtain ⟨st', hex, hst⟩ : ∃ st', x = some ((), st', []) ∧ st' = pmpCfgUpto v s ((7 : Int) + 1).toNat :=
    hx ▸ WeakLeafPmpcfg0.execEffForInInv _ rfl _ (fun i st => st = pmpCfgUpto v s i.toNat) s rfl
      (by decide) (fun i st hi hP => by
      subst hP
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
        simp only [Membership.mem, show (1 : Int) > 0 from by decide, ite_true] at hi
        omega
      rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · exec_eff_steps [execEffPmpWriteCfg]
        exact ⟨_, rfl, rfl⟩)
  rw [hex, hst]
  rfl

/-! ### 1c. The read-back -/

/-- Rocq `exec_eff_pmpReadCfgReg_0`. -/
theorem execEffPmpReadCfgReg0 (s : ExecSt) :
    execEff (pmpReadCfgReg 0) s =
      some (WeakLeafPmpcfg0.pmpcfg0Readback (s.regs .pmpcfg_n), s, []) := by
  unfold pmpReadCfgReg
  exec_eff_steps
  rfl

/-! ### 1d. `write_CSR` / check / callback, for pmpcfg0 -/

/-- Rocq `exec_eff_write_CSR_pmpcfg0` (deviation 4). -/
theorem execEffWriteCSRPmpcfg0 (v : BitVec 64) (s : ExecSt) :
    execEff (write_CSR 0x3A0#12 v) s =
      some (.Ok (WeakLeafPmpcfg0.pmpcfg0Readback ((pmpcfg0Final v s).regs .pmpcfg_n)),
        pmpcfg0Final v s, []) := by
  rw [write_CSR_pmpcfg0, execEffBind0Nil _ _ _ _ _ (execEffPmpWriteCfgReg0 v s),
    execEffBindNil _ _ _ _ _ (execEffPmpReadCfgReg0 _)]
  rfl

/-- Rocq `exec_eff_csr_id_write_callback_pmpcfg0`. -/
theorem execEffCsrIdWriteCallbackPmpcfg0 (d : BitVec 64) (s : ExecSt) :
    execEff (csr_id_write_callback 0x3A0#12 d) s = some ((), s, []) := rfl

/-- Rocq `exec_eff_check_CSR_result_csrw_pmpcfg0`: pmpcfg0 is a PURE-check CSR. -/
theorem execEffCheckCSRResultCsrwPmpcfg0 (s : ExecSt) :
    execEff (check_CSR_result 0x3A0#12 .Machine .CSRWrite) s = some (.CSR_Check_OK (), s, []) :=
  execEffCheckCSRResultCsrwPure 0x3A0#12 s rfl (by decide) rfl rfl

/-! ### 1e. The end-to-end pmpcfg0 execute, trace `[]` -/

/-- Rocq `exec_eff_execute_csrw_pmpcfg0` (deviation 1). -/
theorem execEffExecuteCsrwPmpcfg0 (rs1 : BitVec 5) (s : ExecSt) :
    rs1.toNat ≠ 0 →
    s.regs .cur_privilege = .Machine →
    execEff (execute (.CSRReg (0x3A0#12, .Regidx rs1, zreg, .CSRRW))) s =
      some (RETIRE_SUCCESS, pmpcfg0Final (s.gpr rs1) s, []) := by
  intro _ hpriv
  show execEff (execute_CSRReg 0x3A0#12 (.Regidx rs1) zreg .CSRRW) s = _
  exact execEffExecuteCsrwGprP .Machine 0x3A0#12 rs1 s _ _ hpriv
    (execEffCheckCSRResultCsrwPmpcfg0 s) (by decide) (by decide) (by decide)
    (execEffWriteCSRPmpcfg0 _ s) (execEffCsrIdWriteCallbackPmpcfg0 _ _)

/-! ## 2. THE LEAF -/

/-- The csrw-pmpcfg0 `execute` at a pre-written state (Lean-only; the shared
core of the leaf's confined and flat runs). -/
theorem WeakLeafPmpcfg0.execEffAt (s0 : ExecSt) (b : Bool) (x : BitVec 64) (rs1 : BitVec 5)
    (pmpcfg0 : RegisterType .pmpcfg_n) (rs1v : BitVec 64) (hrs1 : rs1.toNat ≠ 0)
    (hpriv : s0.regs .cur_privilege = .Machine) (hcfg : s0.regs .pmpcfg_n = pmpcfg0)
    (hg : s0.gpr rs1 = rs1v) :
    execEff (execute (.CSRReg (0x3A0#12, .Regidx rs1, zreg, .CSRRW)))
        ((s0.setReg .minstret_increment b).setReg .nextPC x) =
      some (RETIRE_SUCCESS, ((s0.setReg .minstret_increment b).setReg .nextPC x).setReg .pmpcfg_n
        (WeakLeafPmpcfg0.pmpcfgWritten rs1v pmpcfg0), []) := by
  have hpriv' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .cur_privilege = .Machine := by
    leaf_peel .cur_privilege; exact hpriv
  have hcfg' : ((s0.setReg .minstret_increment b).setReg .nextPC x).regs .pmpcfg_n = pmpcfg0 := by
    leaf_peel .pmpcfg_n; exact hcfg
  have hg' : ((s0.setReg .minstret_increment b).setReg .nextPC x).gpr rs1 = rs1v := by
    rw [WeakLeafCsrw.gprSetRegNe _ _ _ _ (by decide), WeakLeafCsrw.gprSetRegNe _ _ _ _ (by decide)]
    exact hg
  have h := execEffExecuteCsrwPmpcfg0 rs1 _ hrs1 hpriv'
  rw [hg', WeakLeafPmpcfg0.pmpcfg0FinalSet, hcfg'] at h
  exact h

/-- The register-only trace's i-cache reads lie in the text window (Lean-only). -/
theorem WeakLeafPmpcfg0.fetchInWindowRegonly (al4 : Bool) (pc : BitVec 64) (hacc : accWf pc 4) :
    fetchInWindow pc (regonlyEs al4 pc) := by
  intro ak pa n hin _ j hj
  obtain ⟨j', hj', he⟩ := weffsTouchRegonly al4 pc _ hacc ⟨_, hin, j, hj, rfl⟩
  exact ⟨j', hj', he⟩

/-- The register-only trace is fetch-fresh (Lean-only; it has no writes). -/
theorem WeakLeafPmpcfg0.fetchFreshRegonly (al4 : Bool) (pc : BitVec 64) :
    fetchFresh (regonlyEs al4 pc) := by
  cases al4 <;> simp [regonlyEs, fetchFresh, weffWrites]

section leaf
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wwp_csrw_pmpcfg0_leaf` (deviation 5). -/
theorem wwpCsrwPmpcfg0Leaf (al4 : Bool) (gen : Nat) (cpu : CPU) (pc : BitVec 64) (w : BitVec 32)
    (rs1 : BitVec 5) (ms0 rs1v npc0 : BitVec 64) (pmpcfg0 : RegisterType .pmpcfg_n)
    (D : Register → Bool) (dst : ExecSt) (ws : Wstate) :
    gen = 0 →
    pmpAllowsAll pmpcfg0 →
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = al4 →
    rs1.toNat ≠ 0 →
    (_get_Mstatus_MIE ms0 == 1#1) = false →
    (_get_Mstatus_MPRV ms0 == 1#1) = false →
    -- the decode, in the two shapes its two consumers ask for
    (∀ t : ExecSt,
      privMSU (t.regs .cur_privilege) = true →
      (_get_Misa_C (t.regs .misa) == 1#1) = true →
      (_get_Misa_A (t.regs .misa) == 1#1) = true →
      t.regs .misa = misaC →
      cfgOk t →
      exec (decodeFetch (.F_Base w)) t = some (.CSRReg (0x3A0#12, .Regidx rs1, zreg, .CSRRW), t)) →
    (∀ f : RegFile,
      f .cur_privilege = .Machine →
      f .misa = misaC →
      f .mseccfg = 0#64 →
      ∀ r, D r = true → f r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (.CSRReg (0x3A0#12, .Regidx rs1, zreg, .CSRRW), dst) →
    hwConfig (GF := GF) cpu ⊢
      clockCells cpu -∗
      Register.hart_state ↦ᵣ[cpu] HartState.HART_ACTIVE () -∗
      Register.cur_privilege ↦ᵣ[cpu] Privilege.Machine -∗
      Register.mstatus ↦ᵣ[cpu] ms0 -∗
      Register.pmpcfg_n ↦ᵣ[cpu] pmpcfg0 -∗
      Register.PC ↦ᵣ[cpu] pc -∗
      Register.nextPC ↦ᵣ[cpu] npc0 -∗
      gpr cpu rs1 (DFrac.own 1) rs1v -∗
      winstrBytes pc (.F_Base w) -∗
      hartWs cpu ws -∗
      (∀ ws' : Wstate,
        ⌜wsLe ws ws'⌝ -∗
        Register.hart_state ↦ᵣ[cpu] HartState.HART_ACTIVE () -∗
        Register.cur_privilege ↦ᵣ[cpu] Privilege.Machine -∗
        Register.mstatus ↦ᵣ[cpu] ms0 -∗
        Register.pmpcfg_n ↦ᵣ[cpu] WeakLeafPmpcfg0.pmpcfgWritten rs1v pmpcfg0 -∗
        clockCells cpu -∗
        pcIs cpu (BitVec.addInt pc 4) -∗
        gpr cpu rs1 (DFrac.own 1) rs1v -∗
        hartWs cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hpmp hal2 hal4 hrs1 hmie hmprv hdecf hagree hDmi hgood hdec
  iintro #Hhw Hclk Hhs Hpriv Hms0 Hpmpc Hpc Hnpc Hrs1c #Hbs Hhws Hcont
  ihave %haccpc := winstrBytesAccWf pc (.F_Base w) $$ Hbs
  have hacc0 : accWf pc 0 := by unfold accWf at haccpc ⊢; omega
  have hwd : winstrDec (.F_Base w) (.CSRReg (0x3A0#12, .Regidx rs1, zreg, .CSRRW)) :=
    fun t h1 h2 h3 h4 h5 => hdecf t h1 h2 h3 h4 h5
  ihave #Hi := winstrIntro pc false (.CSRReg (0x3A0#12, .Regidx rs1, zreg, .CSRRW)) (.F_Base w)
    rfl rfl hwd $$ Hbs
  -- the funnel: certificate = nowrite at the fetch-only trace
  iapply wwpInstrConfig gen cpu pc false (.CSRReg (0x3A0#12, .Regidx rs1, zreg, .CSRRW)) pmpcfg0 ms0
    (wPEff (some cpu.val) (regonlyEs al4 pc))
    (wQFr wQPure (some cpu.val) (regonlyEs al4 pc))
    hgen haccpc hpmp hmie hmprv
    (wstepCertFr cpu.val pc _ _ (wcertRegonly al4 cpu.val pc))
    $$ Hhw Hclk Hhs Hpriv Hms0 Hpmpc Hpc Hi
  unfold wwpCbConfig wmstateNorg
  iintro %σ %b %mt %ip %Lpc %hcfg %Lms Hpriv Hms Hpmpc Hlat Hreg ⟨%hbnd, %hnv, %hwf, Hdev, Hlog, Hwsa⟩
    Hmt Hip
  ihave ⟨%hws, Hwsa, Hhws⟩ := persistent_entails_right (hartWsAgree cpu σ.wmWs ws) $$ [Hwsa Hhws]
  · iframe Hwsa Hhws
  obtain ⟨Lpriv, Lhart, Lmisa, Lsec, Lpmpc, Lpma, Lhtif, LmisaS, LmIE, -, -, Lelp⟩ := hcfg
  icases keepPure (winstrFlat σ pc _ hwf) $$ Hlat Hbs with ⟨%hfok, Hlat, -⟩
  icases keepPure (winstrTextPinned σ pc _ hwf) $$ Hlat Hbs with ⟨%htp, Hlat, -⟩
  icases keepPure (winstrUnwritten σ pc _ hwf) $$ Hlat Hbs with ⟨%hunw, Hlat, -⟩
  obtain ⟨-, hram, w', hwok, htext0⟩ := hfok
  obtain ⟨hww, hnotRVC⟩ := hwok
  subst hww
  have LmisaC : (_get_Misa_C (σ.wmRegs .misa) == 1#1) = true := by rw [Lmisa]; decide
  -- the operand register the funnel does not read
  icases keepPure (WeakLeafLw4.gprValid cpu _ rs1 _ rs1v hrs1) $$ Hreg Hrs1c
    with ⟨%Lrs1, Hreg, Hrs1c⟩
  have Lrs1f : (wflatSt σ).gpr rs1 = rs1v := by
    rw [← WeakLeafCsrw.gprSetRegNe (wflatSt σ) .minstret_increment b rs1 (by decide)]
    exact Lrs1
  -- premise (c): the execute mirror, at the CONFINED state
  have hc : ∀ b' : Bool, ∃ sExec : ExecSt,
      execEff (execute (.CSRReg (0x3A0#12, .Regidx rs1, zreg, .CSRRW)))
        (((⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt).setReg
          .minstret_increment b').setReg .nextPC (BitVec.addInt pc 4)) =
        some (.Retire_Success (), sExec, []) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b' ∧
      bmDomSub sExec.mem (wwin pc pc 0) := by
    intro b'
    obtain ⟨F1, F2, F3, -, -⟩ := csrwSexecFactsR .pmpcfg_n
      (⟨σ.wmRegs, wmemRestrict σ (wwin pc pc 0), σ.wmDev⟩ : ExecSt) b' (BitVec.addInt pc 4)
      (WeakLeafPmpcfg0.pmpcfgWritten rs1v pmpcfg0) (by decide) (by decide) (by decide)
    refine ⟨_, WeakLeafPmpcfg0.execEffAt _ b' _ rs1 pmpcfg0 rs1v hrs1 Lpriv Lpmpc Lrs1f, ?_, F2, ?_⟩
    · rw [F1]; exact Lhart
    · rw [F3]; exact wmemRestrictDom σ _
  -- the certificate's precondition
  have HP : wPEff (some cpu.val) (regonlyEs al4 pc) σ :=
    wPEffOfLeafRegonly al4 cpu.val σ (wwin pc pc 0) pc w
      (.CSRReg (0x3A0#12, .Regidx rs1, zreg, .CSRRW)) D dst hwf
      (wwinNonzero pc pc 0 (fun j hj => WeakLeafWin.inRamByte pc 4 j hram hj) (win0Absurd _))
      (wwinPinned σ pc pc 0 haccpc hacc0 (fun j hj => (htp j hj).1) (win0Absurd _))
      (fetchPinOfText σ pc _ (WeakLeafPmpcfg0.fetchInWindowRegonly al4 pc haccpc)
        (WeakLeafPmpcfg0.fetchFreshRegonly al4 pc) (fun j hj => (htp j hj).2))
      Lpc Lpriv (by rw [Lpmpc]; exact hpmp) Lpma Lhtif Lhart LmisaS LmisaC LmIE Lelp hal2 hal4 hram
      (wwinConfText σ pc pc 0 w htext0) hnotRVC (hagree σ.wmRegs Lpriv Lmisa Lsec) hDmi hgood hdec
      rfl hc
  -- the run at the FLAT state
  have Hef := WeakLeafPmpcfg0.execEffAt (wflatSt σ) b (BitVec.addInt pc 4) rs1 pmpcfg0 rs1v hrs1
    Lpriv Lpmpc Lrs1f
  obtain ⟨-, -, -, G4, G5⟩ := csrwSexecFactsR .pmpcfg_n (wflatSt σ) b (BitVec.addInt pc 4)
    (WeakLeafPmpcfg0.pmpcfgWritten rs1v pmpcfg0) (by decide) (by decide) (by decide)
  -- the two register writes the `execute` performs
  imod (wand_intro (reg_update cpu ((wflatSt σ).setReg .minstret_increment b).regs .nextPC npc0
    (BitVec.addInt pc 4))) $$ Hreg Hnpc with ⟨Hreg, Hnpc⟩
  imod (wand_intro (reg_update cpu
    ((((wflatSt σ).setReg .minstret_increment b).regs).set .nextPC (BitVec.addInt pc 4)) .pmpcfg_n
    pmpcfg0 (WeakLeafPmpcfg0.pmpcfgWritten rs1v pmpcfg0))) $$ Hreg Hpmpc with ⟨Hreg, Hpmpc⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact HP
  iexists ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setReg
    .pmpcfg_n (WeakLeafPmpcfg0.pmpcfgWritten rs1v pmpcfg0))
  isplitr
  · ipureintro; exact execEffExec _ _ _ _ _ Hef
  isplitl [Hreg]
  · rw [show ((((wflatSt σ).setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)).setReg
        .pmpcfg_n (WeakLeafPmpcfg0.pmpcfgWritten rs1v pmpcfg0)).regs =
        ((((wflatSt σ).setReg .minstret_increment b).regs.set .nextPC (BitVec.addInt pc 4)).set
        .pmpcfg_n (WeakLeafPmpcfg0.pmpcfgWritten rs1v pmpcfg0)) from rfl]
    iexact Hreg
  isplitl [Hmt Hip]
  · iexists mt, ip
    iframe Hmt Hip
  inext
  rw [G5]
  iintro %tick %σ' %t %_hstep %hdevt %hpost %hQ Hhs Hclk HPC
  obtain ⟨-, hdevs', -, -, -, -, hwf', hbnd'⟩ := hpost
  obtain ⟨⟨hQi, hQl, hQw⟩, hQeff⟩ := hQ
  have hdev : σ'.wmDev = σ.wmDev := by rw [hdevs', hdevt]; exact G4
  imod Hclose
  imod hartWsUpdate cpu σ.wmWs ws σ'.wmWs $$ [$Hwsa $Hhws] with ⟨Hwsa, Hhws⟩
  imodintro
  isplitl [Hlat]
  · rw [hQi, hQl]; iexact Hlat
  isplitl [Hdev Hlog Hwsa]
  · isplitr
    · ipureintro; exact hbnd'
    isplitr
    · ipureintro
      refine nvHartOfWQEffUnwritten cpu σ σ' _ hQeff hnv (fun a ha => ?_)
      obtain ⟨j, hj, rfl⟩ := weffsTouchRegonly al4 pc a haccpc ha
      rw [hQl]
      exact hunw j hj
    isplitr
    · ipureintro; exact hwf'
    rw [hdev, hQl]
    iframe Hdev Hlog Hwsa
  · iapply Hcont $$ %σ'.wmWs %(by rw [hws]; exact hQw) Hhs Hpriv Hms Hpmpc Hclk [HPC Hnpc] Hrs1c Hhws
    unfold pcIs
    iframe HPC Hnpc

end leaf

end Weak
