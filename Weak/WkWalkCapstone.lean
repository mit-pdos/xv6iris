/-
Weak: **THE WALK-BRIDGE VALIDATION CAPSTONE** (walk-bridge §8, 6c: one whole WP leaf for a
FETCH-WALKING S-mode instruction).

Rocq: `iris/WkWalkCapstone.v` @ xxvzwolszwmp (1390 lines; one Lean file, elaborates in ~3 s).

The Rocq header, in substance.  Everything below `WkWalkRule` is pure, everything above it is
resources; this file is where they meet.  It threads `WkFetchPeel` §6's fupd (`wkptFetchPeelAt`)
into a `wwalkSite`-shaped site predicate, drives `WkWalkRule.wpWwalkStep`, and re-establishes the
successor's state interpretation, for `addi rd, rs1, imm` (`rd ≠ x0`) executed at a KERNEL VIRTUAL
ADDRESS `va` mapped executable by the kernel page table, where the fetch may TLB-miss, walk the
three levels and CAS the leaf PTE's A-bit back.  (a) THE SITE is established inside the rule's
σ-callback from the fupd's pure exports, the leaf's register-owned gates and `WkWalkTails`' four
tail dischargers; the rule fixes `(la, Φ)` before the callback while the fupd MINTS `p2 p1 lw`, so
the leaf takes them as parameters and the caller's σ-callback pins them (three `ptSlotMem` facts,
collapsed by `ptSlotMemInj`); the PMA region is not σ-recoverable, so `wsiteAddi` quantifies it.
(b) THE GHOST SIDE: the fupd hands back `regInterp`, a register wand across the hidden `tlb`
update and the read-only / write-back disjunction carrying the log authorities; the continuation
rebuilds the successor's mirror run concretely (§§2-5: walk member, text read, ADDI execute, retire
postlude, clock tick) and pins `wflatSt σ'` against it (`execStale` is a function).  THE TWO
RECORDED DEBTS (Rocq, unchanged): the φ stand-in `∀ a, nvFree σ.wmLog a` and the rule's vestigial
PC-window pin are σ-callback conjuncts (`wwalkScn`), not resource obligations.  No graph-tier fact
is used: the file lives at `wrun` / `execEff` / `execStale`.

**Deviations from Rocq.**
1. VOCABULARY as `Weak/WkStepPeel.lean` / `Weak/WkWalkTails.lean` deviation 1 and
   `Weak/WkEntryNew.lean` deviation 1: `register_lookup r (wm_regs σ)` ↦ `σ.wmRegs r`, `sregs`/`mdev`
   ↦ `.regs`/`.dev`, `set_reg` ↦ `ExecSt.setReg`, the GPR write `set_reg (R_bitvector_64 (gpr_of_Z
   (uint rd))) (regval_into_reg v)` ↦ `ExecSt.setGpr rd v`, `add_vec_int` ↦ `BitVec.addInt`,
   `uint rd <> 0` ↦ `rd.toNat ≠ 0`, `zeros' 64` ↦ `0#64`, `eq_vec x 'b"1"` ↦ `(x == 1#1)`, `'b"10"`
   ↦ `2#2`, `MISA_C`/`MENVCFG_S` ↦ `misaC`/`menvcfgS`, `HART_ACTIVE tt` ↦ `.HART_ACTIVE ()`,
   `gpr_file m` ↦ `gprFile cpu m` over a `RegMap` (`<[Regidx rd := v]> m` ↦ `m.set rd v`,
   `m !!! Regidx rs1` ↦ the x0-safe `m.get rs1`), `GEN`/`CID` ↦ explicit `gen`/`cpu`,
   `fin_to_nat cpu_id` ↦ `cpu.val`, `WWP Loop` ↦ `wwpTriv ⊤ (WExpr.loop gen cpu)`,
   `kmap_at (svpn_of va) ppn kpc` ↦ `kmapAt (WeakKpt.svpnOf va) (kLeaf ppn kpc 0#1 0#1)`,
   `mk_pte ppn (kperm_flags kpc)` ↦ `mkPte ppn kpc.flags`, `bs !! pa_add pa j` ↦
   `get? bs (pa + BitVec.ofNat 64 j)`, `hart_ws` ↦ `hartWs`, `nv_free log (a : Z)` ↦
   `nvFree log (a : Int)`, `P -∗ … -∗ R` ↦ `P ∗ … ⊢ R`, `={⊤}=∗` ↦ `|={⊤}=>`.  Rocq's §1
   `Section` hypotheses are explicit arguments; `and_vec mie (not_vec mideleg) = zeros' 64` ↦
   `mie &&& ~~~mideleg = 0#64`; the two gate lemmas are stated on the Lean model's inline shape
   (as `WeakFetchEff.execEffMIEFalse`).
2. O2 (WkFetchPeel deviations 4-5): the text read appended to the walk's trace is
   `.WEread WeakFetchEff.wakIfetch pa 4` (Rocq `WEread wak_plain pa 4`) in `execStaleStepAddi`,
   `tstaleIdWalkRo`/`Wb`, `wtraceMsgsWalkRoApp`/`WbApp`, `tstaleIdOfShape`, `memberOk`; it is an
   unpinned read off the window, so `tstaleId` and `wtraceMsgs` see it exactly as Rocq's.
3. THE TEXT PINS.  The fetch pin at `pa` that `wkptFetchPeelAt` / `wwalkSite` / `wfetchSiteWmi`
   require is `fetchPinned σ (accAddr pa j)` (Rocq `pinned_read`), SUPPLIED by the leaf from
   `wkernelText` (`WeakInstr.wkernelTextFetchPinned`); it is not a caller obligation.  The rule's
   vestigial PC-window pin (`wwalkScn`'s last conjunct, still a σ-callback conjunct as in Rocq) is
   `pinnedRead ∧ fetchPinned` at `va`, because Lean `wpWwalkStep`'s σ-callback returns that
   conjunction (WkWalkRule deviation 2).
4. `fGpr rd` admits every GPR (`r ∈ uxaGprs`), not only `rd`'s cell: the Lean ADDI execute is
   `setGpr rd` (WkEntryEff deviation 5), whose frame lemma `WeakLeafWin.setGprRegsNe` is over the
   non-GPRs.  The classifier is only ever used to keep `hart_state` (`fGprHartState`, `fGprTlb`
   as Rocq).
5. THE DECODE PREMISE: Rocq's `goodb0 D_s (ext_decode w) dstateS` / `exec (ext_decode w) dstateS`
   with `WpDecodeBridge.D_s`/`dstateS`/`agree_s` (no Lean twins) ↦ the Lean-only stand-ins
   `WkWalkCapstone.dS` (the domain of `WkWalkCapstone.drefS` = `WkEntryNew.drefS0`:
   `cur_privilege`, `misa`, `menvcfg`), `WkWalkCapstone.dstateS` and `WkWalkCapstone.agreeS`, as
   `WkEntryEff` deviation 4 does for `dstateM`.
6. §7 CONFIGURATION (WkFetchPeel deviation 7): `pma_allows_all pmar0` ↦ `pmar0 = bootPMA`;
   `addr_is_ram pa ∧ addr_is_ram (pa_add pa 3)` ↦ `inRam pa 4`; `vec_access_dec v 0` ↦ `v[0]!`,
   `uint` ↦ `toNat`, `ram_base + ram_size` ↦ `ramEnd`.  Contexts `[MachGS hlc GF] [WeakGS GF]
   [WeakKpt.KptGS GF]` (WkFetchPeel deviation 8).
7. PROOF STRUCTURE: Rocq's inline `iAssert` / `reg_valid_dq` / `reg_update` blocks ↦ the Lean-only
   `WkWalkCapstone.scfgFacts` (config reads), `WkWalkCapstone.textFlat` (text bytes),
   `WkWalkCapstone.memberOk` (the bundle the two ghost arms converge on),
   `WkWalkCapstone.postRegs` / `WkWalkCapstone.addiRegs` (the register moves) with
   `WkWalkCapstone.finOf` / `WkWalkCapstone.addiFinEq` (the post-state, by `rfl`).  `tstaleId`
   spells its read and barrier arms separately (same function).
8. Rocq §8's `Print Assumptions` commands are not declarations (the CI axiom audit; the leaf's
   axioms are `propext`/`Classical.choice`/`Quot.sound` plus upstream `bv_decide` certificates).

**Carried premises.**  None beyond Rocq's own: the σ-callback record `wwalkScn` (Rocq
`wwalk_scn`: three slot pins, the φ stand-in, the vestigial PC pin) is Rocq's statement.  No
graph-tier fetch-inertness premise is introduced.

**Rocq → Lean name map.**  `exec_eff_mIE_S_true` `execEffMIESTrue`, `exec_eff_sIE_S_false`
`execEffSIESFalse`, `exec_eff_getPendingSet_supervisor_none` `execEffGetPendingSetSupervisorNone`,
`exec_eff_dispatchInterrupt_supervisor_none` `execEffDispatchInterruptSupervisorNone`, `tstale_id`
`tstaleId`, `exec_eff_of_exec_stale_id` `execEffOfExecStaleId`, `tstale_id_app_reads`
`tstaleIdAppReads`, `ts_tick_pc` `tsTickPc`, `ts_post` `tsPost`, `exec_eff_ts_after_rha_retire_at`
`execEffTsAfterRhaRetireAt`, `F_gpr` `fGpr`, `F_gpr_hart_state` `fGprHartState`, `F_gpr_tlb`
`fGprTlb`, `wexec_regonly_addi` `wexecRegonlyAddi`, `gpr_addi_val_off` `gprAddiValOff`, `addi_sx`
`addiSx`, `addi_fin` `addiFin`, `reg_at_wmi` `regAtWmi`, `exec_stale_step_addi`
`execStaleStepAddi`, `pt_slot_mem_inj` `ptSlotMemInj`, `wsite_addi` `wsiteAddi`, `wwalk_cert_addi`
`wwalkCertAddi`, `wsite_addi_adm_filter` `wsiteAddiAdmFilter`, `tstale_id_walk_ro`
`tstaleIdWalkRo`, `tstale_id_walk_wb` `tstaleIdWalkWb`, `wtrace_msgs_walk_ro_app`
`wtraceMsgsWalkRoApp`, `wtrace_msgs_walk_wb_app` `wtraceMsgsWalkWbApp`, `nv_hart_of_free`
`nvHartOfFree`, `wwalk_shape` `wwalkShape`, `wwalk_member_full` `wwalkMemberFull`,
`tstale_id_of_shape` `tstaleIdOfShape`, `mdev_addi_fin` `mdevAddiFin`, `addi_sx'` `addiSx'`,
`scfg_cells` `scfgCells`, `wwalk_scn` `wwalkScn`, `wwp_walk_addi` `wwpWalkAddi` (none in the
duplicated-name table).  Lean-only (file-qualified): `WkWalkCapstone.drefS`, `WkWalkCapstone.dS`,
`WkWalkCapstone.dstateS`, `WkWalkCapstone.agreeS`, `WkWalkCapstone.memberOk`,
`WkWalkCapstone.finOf`, `WkWalkCapstone.addiFinEq`, `WkWalkCapstone.scfgFacts`,
`WkWalkCapstone.textFlat`, `WkWalkCapstone.postRegs`, `WkWalkCapstone.addiRegs`.

**Dropped:** nothing.  36 Rocq declarations (`Definition`/`Fixpoint`/`Lemma`): 36 ported + 11
Lean-only = 47 Lean declarations.

**Statements checked** (by hand, against Rocq): all; the changed ones are deviations 1-6.
-/
import Weak.WkWalkRule
import Weak.WkWalkTails
import Weak.WeakLeafItype
import Weak.WeakInstr

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. THE S-MODE INTERRUPT GATE, AT `execEff` -/

section SIntrEff
variable (s : ExecSt)

/-- Rocq `exec_eff_mIE_S_true` (the Lean model's inline shape, as `WeakFetchEff.execEffMIEFalse`):
at `Supervisor` the M-destined gate is TRUE. -/
theorem execEffMIESTrue :
    execEff ((if (Privilege.Supervisor == Privilege.Machine) = true then
        (readReg .mstatus >>= fun w => pure (_get_Mstatus_MIE w == 1#1)) else pure false) >>=
      fun b => (pure (b || ((Privilege.Supervisor == Privilege.Supervisor) ||
        (Privilege.Supervisor == Privilege.User))) : SailM Bool)) s = some (true, s, []) := by
  exec_eff_run
  rfl

/-- Rocq `exec_eff_sIE_S_false` (the Lean model's inline shape). -/
theorem execEffSIESFalse (hSIE : (_get_Mstatus_SIE (s.regs .mstatus) == 1#1) = false) :
    execEff ((if (Privilege.Supervisor == Privilege.Supervisor) = true then
        (readReg .mstatus >>= fun w => pure (_get_Mstatus_SIE w == 1#1)) else pure false) >>=
      fun b => (pure (b || (Privilege.Supervisor == Privilege.User)) : SailM Bool)) s =
      some (false, s, []) := by
  exec_eff_run [hSIE]
  rfl

/-- Rocq `exec_eff_getPendingSet_supervisor_none`. -/
theorem execEffGetPendingSetSupervisorNone
    (hmisaS : (_get_Misa_S (s.regs .misa) == 1#1) = true)
    (hSIE : (_get_Mstatus_SIE (s.regs .mstatus) == 1#1) = false)
    (hand0 : s.regs .mie &&& ~~~(s.regs .mideleg) = 0#64) :
    execEff (getPendingSet .Supervisor) s = some (none, s, []) := by
  obtain ⟨mipv, hmip⟩ := execEffReadMipSome s hmisaS
  have h1 : (Privilege.Supervisor == Privilege.Machine) = false := rfl
  have h2 : (Privilege.Supervisor == Privilege.Supervisor) = true := rfl
  have h3 : (Privilege.Supervisor == Privilege.User) = false := rfl
  have hpm : ∀ x : BitVec 64,
      (x &&& (s.regs .mie &&& ~~~(s.regs .mideleg)) != zeros (n := 64)) = false := by
    intro x; rw [hand0]; simp [zeros]
  unfold getPendingSet
  exec_eff_run [execEffCESTrue s hmisaS, hmip, h1, h2, h3, hSIE, hpm, Bool.or_false,
    Bool.false_or, Bool.or_true]

/-- Rocq `exec_eff_dispatchInterrupt_supervisor_none`. -/
theorem execEffDispatchInterruptSupervisorNone
    (hmisaS : (_get_Misa_S (s.regs .misa) == 1#1) = true)
    (hSIE : (_get_Mstatus_SIE (s.regs .mstatus) == 1#1) = false)
    (hand0 : s.regs .mie &&& ~~~(s.regs .mideleg) = 0#64) :
    execEff (dispatchInterrupt .Supervisor) s = some (none, s, []) :=
  execEffDispatchInterruptNone _ s (execEffGetPendingSetSupervisorNone s hmisaS hSIE hand0)

end SIntrEff

/-! ## 2. THE MIRROR AT THE COHERENT WORD IS THE ORDINARY ONE -/

/-- Rocq `tstale_id`: up to the first RAM write the patch is the identity; after it, the rest
of the trace is window-free. -/
def tstaleId (ra : PAddr) (rn : Nat) : List Weff → Prop
  | [] => True
  | .WEwrite _ _ _ _ :: es' => traceOffWin ra rn es'
  | .WEread _ _ _ :: es' => tstaleId ra rn es'
  | .WEbar _ :: es' => tstaleId ra rn es'

/-- Rocq `exec_eff_of_exec_stale_id`. -/
theorem execEffOfExecStaleId (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) {X : Type} (m : SailM X) :
    accWf ra rn →
    ∀ s x t es, bmWrite s.mem ra rn w = s.mem →
      execStale ra rn w m s = some (x, t, es) → tstaleId ra rn es →
      execEff m s = some (x, t, es) := by
  intro hracc
  induction m with
  | pure y => intro s x t es _ h _; exact h
  | impure call k ih =>
    intro s x t es hid h hts
    cases call with
    | error e => simp [execStale] at h
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [execStale] at h
        simp only [execEff]
        by_cases hd : mmioAcc req.pa n = true
        · rw [if_pos hd] at h ⊢
          cases hdr : devRead s.dev req.pa n with
          | none => simp only [hdr] at h; cases h
          | some p =>
            obtain ⟨w0, d0⟩ := p
            simp only [hdr] at h ⊢
            exact ih _ _ _ _ _ hid h hts
        · rw [if_neg hd] at h ⊢
          have hsm : staleMem ra rn w (classify req.access_kind) s = s.mem := by
            cases hpin : akPins (classify req.access_kind) with
            | true => exact staleMemPins _ _ _ _ _ hpin
            | false => rw [staleMemUnpinned _ _ _ _ _ hpin]; exact hid
          rw [hsm] at h
          cases hrb : bmRead s.mem req.pa n with
          | none => simp only [hrb] at h; cases h
          | some v0 =>
            simp only [hrb] at h ⊢
            obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
            exact Weff.consEqSome.2 ⟨es0, ih _ _ _ _ _ hid h0 hts, rfl⟩
      case memWrite n va req =>
        simp only [execStale] at h
        simp only [execEff]
        cases hv : req.value with
        | none => simp only [hv] at h; cases h
        | some v =>
          simp only [hv] at h ⊢
          by_cases hd : mmioAcc req.pa n = true
          · rw [if_pos hd] at h ⊢
            cases hdw : devWrite s.dev req.pa n v with
            | none => simp only [hdw] at h; cases h
            | some d0 =>
              simp only [hdw] at h ⊢
              exact ih _ _ _ _ _ hid h hts
          · -- the RAM write may break the identity: from here the landed transfer takes over
            rw [if_neg hd] at h ⊢
            obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
            exact Weff.consEqSome.2 ⟨es0, execEffOfExecStale ra rn w _ hracc _ _ _ _ h0 hts, rfl⟩
      case barrier b =>
        simp only [execStale] at h
        simp only [execEff]
        obtain ⟨es0, h0, rfl⟩ := Weff.consEqSome.1 h
        exact Weff.consEqSome.2 ⟨es0, ih _ _ _ _ _ hid h0 hts, rfl⟩
      all_goals first
        | (simp only [execStale, reduceCtorEq] at h; done)
        | (simp only [execStale] at h; simp only [execEff]; exact ih _ _ _ _ _ hid h hts)

/-- Rocq `tstale_id_app_reads`. -/
theorem tstaleIdAppReads (ra : PAddr) (rn : Nat) (es1 es2 : List Weff) :
    (∀ (ak : AkInfo) (pa : PAddr) (n : Nat) (v : BitVec (8 * n)), Weff.WEwrite ak pa n v ∈ es1 → False) →
    tstaleId ra rn es2 →
    tstaleId ra rn (es1 ++ es2) := by
  induction es1 with
  | nil => intro _ h2; exact h2
  | cons e es1 ih =>
    intro hno h2
    cases e with
    | WEread ak pa n =>
      exact ih (fun ak' pa' n' v' hin => hno ak' pa' n' v' (List.mem_cons_of_mem _ hin)) h2
    | WEwrite ak pa n v => exact (hno ak pa n v List.mem_cons_self).elim
    | WEbar b =>
      exact ih (fun ak' pa' n' v' hin => hno ak' pa' n' v' (List.mem_cons_of_mem _ hin)) h2

/-! ## 3. THE RETIRE POSTLUDE, WITH ITS STATE PINNED -/

/-- Rocq `ts_tick_pc`. -/
def tsTickPc (s : ExecSt) : ExecSt := s.setReg .PC (s.regs .nextPC)

/-- Rocq `ts_post`. -/
def tsPost (s : ExecSt) : ExecSt :=
  if s.regs .minstret_increment then
    (tsTickPc s).setReg .minstret (BitVec.addInt ((tsTickPc s).regs .minstret) 1)
  else tsTickPc s

/-- Rocq `exec_eff_ts_after_rha_retire_at`. -/
theorem execEffTsAfterRhaRetireAt (s : ExecSt) (ib : BitVec 32) :
    s.regs .hart_state = .HART_ACTIVE () →
    execEff (tsAfterRha (.Step_Execute (.Retire_Success (), ib))) s = some (false, tsPost s, []) := by
  intro hhart
  have hmi : (s.setReg .PC (s.regs .nextPC)).regs .minstret_increment = s.regs .minstret_increment := by
    rw [ExecSt.setReg_regs]; exact RegFile.set_other _ _ _ _ (by decide)
  unfold tsAfterRha
  simp only [execEffBindEq, readReg, writeReg, PreSail.readReg, PreSail.writeReg, PreSail.emit,
    execEff, effThen, hhart, assert, PreSail.assert, hart_is_active,
    ↓reduceIte, execEffReturnm, execEffTickPc, get_config_rvfi, Bool.false_eq_true,
    List.nil_append, hmi]
  unfold tsPost tsTickPc
  cases hb : s.regs .minstret_increment <;>
    simp only [execEffBindEq, execEff, effThen, ↓reduceIte, Bool.false_eq_true, execEffReturnm,
      List.nil_append] <;> rfl

/-! ## 4. THE INSTRUCTION: `addi rd, rs1, imm` -/

/-- Rocq `F_gpr` (deviation 6): the classifier admits the GPRs. -/
def fGpr (_rd : BitVec 5) : Register → Bool := fun r => decide (r ∈ uxaGprs)

/-- Rocq `F_gpr_hart_state`. -/
theorem fGprHartState (rd : BitVec 5) : fGpr rd .hart_state = false := by unfold fGpr; decide

/-- Rocq `F_gpr_tlb`. -/
theorem fGprTlb (rd : BitVec 5) : fGpr rd .tlb = false := by unfold fGpr; decide

/-- Rocq `wexec_regonly_addi`. -/
theorem wexecRegonlyAddi (rs1 rd : BitVec 5) (imm : BitVec 12) :
    rd.toNat ≠ 0 →
    wexecRegonly (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI)) (fGpr rd) := by
  intro _ s
  refine ⟨_, execEffExecuteITYPEADDIGpr rs1 rd imm s, fun r hF => ?_⟩
  exact WeakLeafWin.setGprRegsNe s rd _ r (of_decide_eq_false hF)

/-- Rocq `gpr_addi_val_off`: the ADDI's result after the `nextPC` pre-write, from the x0-safe
source read. -/
theorem gprAddiValOff (rs1 : BitVec 5) (imm : BitVec 12) (t : ExecSt) (npc v : BitVec 64) :
    t.gpr rs1 = v →
    gprAddiVal rs1 imm (t.setReg .nextPC npc) = v + sign_extend (m := 64) imm := by
  intro hv
  unfold gprAddiVal
  rw [WeakLeafLw4.gprSetNe t .nextPC npc rs1 (by decide), hv]

/-! ## 5. THE WHOLE STEP AT THE MIRROR, WITH ITS POST-STATE SPELLED OUT -/

/-- Rocq `addi_sx`. -/
def addiSx (sg : ExecSt) (va : BitVec 64) (rs1 rd : BitVec 5) (imm : BitVec 12) : ExecSt :=
  (sg.setReg .nextPC (BitVec.addInt va 4)).setGpr rd
    (gprAddiVal rs1 imm (sg.setReg .nextPC (BitVec.addInt va 4)))

/-- Rocq `addi_fin`. -/
def addiFin (sg : ExecSt) (va : BitVec 64) (rs1 rd : BitVec 5) (imm : BitVec 12) (tick : Bool)
    (c t p : BitVec 64) : ExecSt :=
  if tick then
    (((tsPost (addiSx sg va rs1 rd imm)).setReg .mcycle c).setReg .mtime t).setReg .mip p
  else tsPost (addiSx sg va rs1 rd imm)

/-- Rocq `reg_at_wmi`. -/
theorem regAtWmi (σ : Wmstate) (b : Bool) (r : Register) :
    r ≠ .minstret_increment → (wflatSt (wmi σ b)).regs r = σ.wmRegs r :=
  WkStepPeel.wmiRegs σ b r

/-- Rocq `exec_stale_step_addi`. -/
theorem execStaleStepAddi (σ : Wmstate) (la : PAddr) (va pa : BitVec 64) (w : BitVec 32)
    (rs1 rd : BitVec 5) (imm : BitVec 12) (bmi tick : Bool) (u : BitVec (8 * 8)) (sgx : ExecSt)
    (esx : List Weff) :
    accWf la 8 → accWf pa 4 → raccDisj la 8 pa 4 →
    σ.wmRegs .cur_privilege = .Supervisor →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    σ.wmRegs .PC = va →
    (σ.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    rd.toNat ≠ 0 →
    execEff (should_inc_minstret .Supervisor) (wflatSt σ) = some (bmi, wflatSt σ, []) →
    execEff (dispatchInterrupt .Supervisor) (wflatSt (wmi σ bmi)) =
      some (none, wflatSt (wmi σ bmi), []) →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    isRVC (Sail.BitVec.extractLsb w 15 0) = false →
    (∀ t : ExecSt, (∀ r : Register, r ≠ .tlb → t.regs r = (wmi σ bmi).wmRegs r) →
      execEff (ext_decode w) t = some (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI), t, [])) →
    execStale la 8 u (translateAddr (.Virtaddr va) (.InstructionFetch ())) (wflatSt (wmi σ bmi)) =
      some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sgx, esx) →
    execEff (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr pa) 4 false false false) sgx =
      some (.Ok w, sgx, [.WEread WeakFetchEff.wakIfetch pa 4]) →
    (∀ r : Register, r ≠ .tlb → sgx.regs r = (wmi σ bmi).wmRegs r) →
    ∃ c t p : BitVec 64,
      execStale la 8 u (riscvStep tick) (wflatSt σ) =
        some ((), addiFin sgx va rs1 rd imm tick c t p,
          esx ++ [.WEread WeakFetchEff.wakIfetch pa 4]) := by
  intro hacc haccp hdisj hpriv hhart hpc help hrd hsi hdisp hval hnotRVC hdec htr hmr hrg
  have hpcA : (wflatSt (wmi σ bmi)).regs .PC = va := (regAtWmi σ bmi .PC (by decide)).trans hpc
  have hprivA : (wflatSt (wmi σ bmi)).regs .cur_privilege = .Supervisor :=
    (regAtWmi σ bmi .cur_privilege (by decide)).trans hpriv
  have hhartA : (wflatSt (wmi σ bmi)).regs .hart_state = .HART_ACTIVE () :=
    (regAtWmi σ bmi .hart_state (by decide)).trans hhart
  -- the fetch: the walk member, extended by the text read
  have hf := execStaleFetchS la u va pa w (wflatSt (wmi σ bmi)) sgx esx hacc haccp hdisj hpcA hval
    hnotRVC htr hmr
  -- the post-fetch remainder, at the walk's post-state
  have helpx : (sgx.regs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false := by
    rw [hrg .elp (by decide), WkStepPeel.wmiRegs σ bmi .elp (by decide)]; exact help
  have hpcX : sgx.regs .PC = va := by
    rw [hrg .PC (by decide), WkStepPeel.wmiRegs σ bmi .PC (by decide)]; exact hpc
  have hex := execEffExecuteITYPEADDIGpr rs1 rd imm (sgx.setReg .nextPC (BitVec.addInt va 4))
  have hrha1 := execEffRhaAfterFetchBase sgx (addiSx sgx va rs1 rd imm) w
    (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI)) va RETIRE_SUCCESS [] (hdec sgx hrg) helpx hpcX hex
    trivial
  have hrha : execStale la 8 u (run_hart_active 0) ((wflatSt σ).setReg .minstret_increment bmi) =
      some (.Step_Execute (RETIRE_SUCCESS, zero_extend (m := 32) w), addiSx sgx va rs1 rd imm,
        esx ++ [.WEread WeakFetchEff.wakIfetch pa 4]) := by
    have h := execStaleRunHartActive la u (wflatSt (wmi σ bmi)) sgx (addiSx sgx va rs1 rd imm)
      (.F_Base w) _ (esx ++ [.WEread WeakFetchEff.wakIfetch pa 4]) [] hacc hprivA hdisp hf hrha1
      (traceOffWinNil la 8)
    rw [List.append_nil] at h
    exact h
  -- the retire postlude
  have hhartX : (addiSx sgx va rs1 rd imm).regs .hart_state = .HART_ACTIVE () := by
    unfold addiSx
    rw [WeakLeafWin.setGprRegsNe _ _ _ _ (by decide), ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide),
      hrg .hart_state (by decide), WkStepPeel.wmiRegs σ bmi .hart_state (by decide)]
    exact hhart
  have hts := execEffTsAfterRhaRetireAt (addiSx sgx va rs1 rd imm) (zero_extend (m := 32) w) hhartX
  have hpriv0 : (wflatSt σ).regs .cur_privilege = .Supervisor := hpriv
  cases tick with
  | true =>
    obtain ⟨c, t, p, htk⟩ := execEffTickClock (tsPost (addiSx sgx va rs1 rd imm))
    refine ⟨c, t, p, ?_⟩
    have hstep := execStaleRiscvStep la u true (wflatSt σ) (addiSx sgx va rs1 rd imm)
      (tsPost (addiSx sgx va rs1 rd imm)) (addiFin sgx va rs1 rd imm true c t p) bmi false
      (.Step_Execute (RETIRE_SUCCESS, zero_extend (m := 32) w))
      (esx ++ [.WEread WeakFetchEff.wakIfetch pa 4]) [] [] hacc hpriv0 hsi hhartA hrha hts
      (traceOffWinNil la 8) htk (traceOffWinNil la 8)
    rw [hstep, List.append_nil, List.append_nil]
  | false =>
    refine ⟨0#64, 0#64, 0#64, ?_⟩
    have hstep := execStaleRiscvStep la u false (wflatSt σ) (addiSx sgx va rs1 rd imm)
      (tsPost (addiSx sgx va rs1 rd imm)) (tsPost (addiSx sgx va rs1 rd imm)) bmi false
      (.Step_Execute (RETIRE_SUCCESS, zero_extend (m := 32) w))
      (esx ++ [.WEread WeakFetchEff.wakIfetch pa 4]) [] [] hacc hpriv0 hsi hhartA hrha hts
      (traceOffWinNil la 8) rfl (traceOffWinNil la 8)
    rw [hstep, List.append_nil, List.append_nil]
    rfl

/-! ## 6. THE SITE PREDICATE AND ITS CERTIFICATE -/

/-- Rocq `pt_slot_mem_inj`. -/
theorem ptSlotMemInj (sg : ExecSt) (a w1 w2 : BitVec 64) :
    WeakWalkEff.ptSlotMem sg a w1 → WeakWalkEff.ptSlotMem sg a w2 → w1 = w2 := by
  intro h1 h2
  apply bvEqOfBytes (n := 8) w1 w2
  intro j hj
  have e1 := h1.1 j hj
  rw [h2.1 j hj] at e1
  exact (Option.some.inj e1).symm

/-- Rocq `wsite_addi`: the region is minted and not σ-recoverable, hence existential. -/
def wsiteAddi (tid : Option Nat) (root : BitVec 44) (va pa p2 p1 w0 lw : BitVec 64) (w : BitVec 32)
    (σ : Wmstate) : Prop :=
  ∃ region : PMA_Region, ∀ tick : Bool, wwalkSite tid root va pa p2 p1 w0 lw region w σ tick

/-- Rocq `wwalk_cert_addi`. -/
theorem wwalkCertAddi (cid : Nat) (root : BitVec 44) (va pa p2 p1 w0 lw : BitVec 64) (w : BitVec 32) :
    wwalkCert cid va (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0))
      (wwalkFilter w0 lw) (wsiteAddi (some cid) root va pa p2 p1 w0 lw w) (fun _ _ => True) := by
  intro σ tick hpc hacc hpin hP
  obtain ⟨region, hsite⟩ := hP
  exact wpWwalkStepCertOfPeel cid root va pa p2 p1 w0 lw region w
    (fun σ0 => ∀ t : Bool, wwalkSite (some cid) root va pa p2 p1 w0 lw region w σ0 t)
    (fun _ _ => True) (fun _ t H => H t) (fun _ _ _ _ _ _ _ => trivial) σ tick hpc hacc hpin hsite

/-- Rocq `wsite_addi_adm_filter`. -/
theorem wsiteAddiAdmFilter (cid : Nat) (root : BitVec 44) (va pa p2 p1 w0 lw : BitVec 64)
    (w : BitVec 32) (σ : Wmstate) :
    σ.wmRegs .PC = va →
    wsiteAddi (some cid) root va pa p2 p1 w0 lw w σ →
    wadmFilter σ wakPlain (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8
      (wwalkFilter w0 lw) := by
  intro hpc hP
  obtain ⟨region, hsite⟩ := hP
  exact wwalkSiteAdmFilter cid root va pa p2 p1 w0 lw region w σ false hpc (hsite false)

/-- Rocq `tstale_id_walk_ro` (deviation 4: the text read is the i-cache read). -/
theorem tstaleIdWalkRo (la a2 a1 : PAddr) (pa : BitVec 64) (esx : List Weff) :
    (esx = [] ∨
     esx = [.WEread wakPlain a2 8, .WEread wakPlain a1 8, .WEread wakPlain la 8] ∨
     esx = [.WEread wakExcl la 8] ∨
     esx = [.WEread wakPlain a2 8, .WEread wakPlain a1 8, .WEread wakPlain la 8,
            .WEread wakExcl la 8]) →
    tstaleId la 8 (esx ++ [.WEread WeakFetchEff.wakIfetch pa 4]) := by
  intro h
  rcases h with rfl | rfl | rfl | rfl <;> trivial

/-- Rocq `tstale_id_walk_wb`. -/
theorem tstaleIdWalkWb (la a2 a1 : PAddr) (pa : BitVec 64) (lw' : BitVec 64) (wtr : Bool)
    (esx : List Weff) :
    raccDisj la 8 pa 4 → accWf pa 4 →
    esx = (if wtr then
            [.WEread wakPlain a2 8, .WEread wakPlain a1 8, .WEread wakPlain la 8,
             .WEread wakExcl la 8, .WEwrite wakExcl la 8 lw']
          else [.WEread wakExcl la 8, .WEwrite wakExcl la 8 lw']) →
    tstaleId la 8 (esx ++ [.WEread WeakFetchEff.wakIfetch pa 4]) := by
  intro hdisj haccp hes
  have hoff : traceOffWin la 8 [.WEread WeakFetchEff.wakIfetch pa 4] :=
    (WkWalkTails.textRead la pa haccp hdisj).1
  subst hes
  cases wtr <;> exact hoff

/-- Rocq `wtrace_msgs_walk_ro_app`. -/
theorem wtraceMsgsWalkRoApp (tid : Option Nat) (rp : Bool) (a2 a1 la : PAddr) (pa : BitVec 64)
    (esx : List Weff) :
    (esx = [] ∨
     esx = [.WEread wakPlain a2 8, .WEread wakPlain a1 8, .WEread wakPlain la 8] ∨
     esx = [.WEread wakExcl la 8] ∨
     esx = [.WEread wakPlain a2 8, .WEread wakPlain a1 8, .WEread wakPlain la 8,
            .WEread wakExcl la 8]) →
    wtraceMsgs tid rp (esx ++ [.WEread WeakFetchEff.wakIfetch pa 4]) = [] := by
  intro h
  rcases h with rfl | rfl | rfl | rfl <;> rfl

/-- Rocq `wtrace_msgs_walk_wb_app`. -/
theorem wtraceMsgsWalkWbApp (tid : Option Nat) (rp : Bool) (a2 a1 la : PAddr) (pa : BitVec 64)
    (lw' : BitVec 64) (wtr : Bool) (esx : List Weff) :
    esx = (if wtr then
            [.WEread wakPlain a2 8, .WEread wakPlain a1 8, .WEread wakPlain la 8,
             .WEread wakExcl la 8, .WEwrite wakExcl la 8 lw']
          else [.WEread wakExcl la 8, .WEwrite wakExcl la 8 lw']) →
    wtraceMsgs tid rp (esx ++ [.WEread WeakFetchEff.wakIfetch pa 4]) =
      [wwriteMsg tid .WCexcl la 8 lw'] := by
  intro h
  subst h
  cases wtr <;> rfl

/-- Rocq `nv_hart_of_free`: the φ-stand-in's payment. -/
theorem nvHartOfFree (log ms : List Wmsg) (c : CPU) (ws : Wstate) :
    (∀ a : Int, nvFree log a) →
    (∀ m : Wmsg, m ∈ ms → m.wmTid = some c.val) →
    nvHart (log ++ ms) c ws := by
  intro hfree hown
  exact nvHartAppOwn log ms c ws (fun a => hfree a c (coh ws a)) hown

/-- Rocq `wwalk_shape`: the walk's six trace shapes. -/
def wwalkShape (a2 a1 la : PAddr) (esx : List Weff) : Prop :=
  (esx = [] ∨
   esx = [.WEread wakPlain a2 8, .WEread wakPlain a1 8, .WEread wakPlain la 8] ∨
   esx = [.WEread wakExcl la 8] ∨
   esx = [.WEread wakPlain a2 8, .WEread wakPlain a1 8, .WEread wakPlain la 8,
          .WEread wakExcl la 8]) ∨
  (∃ (lw' : BitVec 64) (wtr : Bool),
    esx = (if wtr then
            [.WEread wakPlain a2 8, .WEread wakPlain a1 8, .WEread wakPlain la 8,
             .WEread wakExcl la 8, .WEwrite wakExcl la 8 lw']
          else [.WEread wakExcl la 8, .WEwrite wakExcl la 8 lw']))

/-- Rocq `wwalk_member_full`: the member, with its device and its trace shape. -/
theorem wwalkMemberFull (tid : Option Nat) (σ : Wmstate) (root : BitVec 44)
    (va pa p2 p1 w0 lw : BitVec 64) (av dv : BitVec 1) :
    let vpn := WeakKpt.svpnOf va
    let a2 := uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)
    let a1 := uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)
    let la := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)
    wwalkExports tid σ root va pa p2 p1 w0 lw →
    pteAdLe (pteSetAD w0 av dv) lw →
    ∃ (sgx : ExecSt) (esx : List Weff),
      execStale la 8 (pteSetAD w0 av dv) (translateAddr (.Virtaddr va) (.InstructionFetch ()))
          (wflatSt σ) =
        some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sgx, esx) ∧
      (sgx.mem = wflatMem σ.wmImg σ.wmLog ∨
       ∃ lw' : BitVec 64, sgx.mem = bmWrite (wflatMem σ.wmImg σ.wmLog) la 8 lw') ∧
      sgx.dev = σ.wmDev ∧
      (∀ r : Register, r ≠ .tlb → sgx.regs r = σ.wmRegs r) ∧
      wwalkShape a2 a1 la esx := by
  intro vpn a2 a1 la hexp hle
  obtain ⟨-, -, -, -, -, -, -, -, -, harm, hregs⟩ := hexp
  rcases harm with hro | ⟨lw', wtr, -, hfam⟩
  · obtain ⟨sgx, esx, hex, hmem, hmdev, hes⟩ := hro av dv hle
    exact ⟨sgx, esx, hex, Or.inl hmem, hmdev, hregs av dv sgx esx hle hex, Or.inl hes⟩
  · obtain ⟨sgx, esx, hex, hmem, hmdev, hes⟩ := hfam av dv hle
    exact ⟨sgx, esx, hex, Or.inr ⟨lw', hmem⟩, hmdev, hregs av dv sgx esx hle hex,
      Or.inr ⟨lw', wtr, hes⟩⟩

/-- Rocq `tstale_id_of_shape`. -/
theorem tstaleIdOfShape (a2 a1 la : PAddr) (pa : BitVec 64) (esx : List Weff) :
    raccDisj la 8 pa 4 → accWf pa 4 →
    wwalkShape a2 a1 la esx →
    tstaleId la 8 (esx ++ [.WEread WeakFetchEff.wakIfetch pa 4]) := by
  intro hdisj haccp h
  rcases h with hro | ⟨lw', wtr, hes⟩
  · exact tstaleIdWalkRo la a2 a1 pa esx hro
  · exact tstaleIdWalkWb la a2 a1 pa lw' wtr esx hdisj haccp hes

/-- Rocq `mdev_addi_fin`: the device does not move along the ADDI's register chain. -/
theorem mdevAddiFin (sg : ExecSt) (va : BitVec 64) (rs1 rd : BitVec 5) (imm : BitVec 12) (tick : Bool)
    (c t p : BitVec 64) :
    (addiFin sg va rs1 rd imm tick c t p).dev = sg.dev := by
  have hsx : (addiSx sg va rs1 rd imm).dev = sg.dev := by
    unfold addiSx
    rw [WeakLeafWin.setGprDev]
    rfl
  have hpost : (tsPost (addiSx sg va rs1 rd imm)).dev = sg.dev := by
    unfold tsPost tsTickPc
    split <;> exact hsx
  unfold addiFin
  cases tick
  · exact hpost
  · exact hpost

/-- Rocq `addi_sx'`: the post-execute state, with the destination value named. -/
def addiSx' (sg : ExecSt) (va : BitVec 64) (rd : BitVec 5) (x : BitVec 64) : ExecSt :=
  (sg.setReg .nextPC (BitVec.addInt va 4)).setGpr rd x

/-! ## 7. THE LEAF: `addi rd, rs1, imm` AT A FETCH-WALKING S-MODE PC -/

/-! ### 7a. The S-mode decode reference state (deviation 7) -/

/-- Rocq `WpDecodeBridge.D_s`'s reference values (Lean-only stand-in, the domain of the
supervisor-mode decode read set; `WkEntryNew.drefS0`'s map). -/
def WkWalkCapstone.drefS : (r : Register) → Option (RegisterType r)
  | .cur_privilege => some Privilege.Supervisor
  | .misa => some misaC
  | .menvcfg => some menvcfgS
  | _ => none

/-- Rocq `WpDecodeBridge.D_s` (Lean-only stand-in): the S-mode decode read set. -/
def WkWalkCapstone.dS (r : Register) : Bool := (WkWalkCapstone.drefS r).isSome

/-- Rocq `WpDecodeBridge.dstateS` (Lean-only stand-in, as `WkEntryEff.dstateM`): the
supervisor-mode reference state. -/
def WkWalkCapstone.dstateS : ExecSt :=
  ⟨((zeroRegs.set .cur_privilege .Supervisor).set .misa misaC).set .menvcfg menvcfgS,
    fun _ => none, testDevs⟩

/-- Rocq `WpDecodeBridge.agree_s` (Lean-only stand-in). -/
theorem WkWalkCapstone.agreeS (rs : RegFile) :
    rs .cur_privilege = .Supervisor → rs .menvcfg = menvcfgS → rs .misa = misaC →
    ∀ r, WkWalkCapstone.dS r = true → rs r = WkWalkCapstone.dstateS.regs r := by
  intro h1 h2 h3 r hr
  unfold WkWalkCapstone.dS WkWalkCapstone.drefS at hr
  split at hr
  · rw [h1]; rfl
  · rw [h3]; rfl
  · rw [h2]; rfl
  · simp at hr

/-! ### 7b. The caller's σ-obligation record -/

/-- Rocq `wwalk_scn` (deviation 3: the vestigial PC-window pin is `pinnedRead ∧ fetchPinned`). -/
def wwalkScn (root : BitVec 44) (va p2 p1 lw : BitVec 64) (σ : Wmstate) : Prop :=
  WeakWalkEff.ptSlotMem (wflatSt σ) (uPteAddr root (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 26 18)) p2 ∧
  WeakWalkEff.ptSlotMem (wflatSt σ)
    (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 17 9)) p1 ∧
  WeakWalkEff.ptSlotMem (wflatSt σ)
    (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) lw ∧
  (∀ a : Int, nvFree σ.wmLog a) ∧
  (∀ j : Nat, j < 4 →
    pinnedRead σ (WeakInterp.accAddr va j) ∧ fetchPinned σ (WeakInterp.accAddr va j))

/-- Lean-only: the member the two ghost arms converge on, with everything the continuation
reads off it. -/
def WkWalkCapstone.memberOk (tid : Option Nat) (σ : Wmstate) (bmi : Bool) (la : PAddr) (va pa : BitVec 64)
    (u : BitVec 64) (msgs : List Wmsg) (sgx : ExecSt) (esx : List Weff) : Prop :=
  execStale la 8 u (translateAddr (.Virtaddr va) (.InstructionFetch ()))
      ((wflatSt σ).setReg .minstret_increment bmi) =
    some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sgx, esx) ∧
  (sgx.mem = wflatMem σ.wmImg σ.wmLog ∨
   ∃ lw' : BitVec 64, sgx.mem = bmWrite (wflatMem σ.wmImg σ.wmLog) la 8 lw') ∧
  sgx.dev = σ.wmDev ∧
  (∀ r : Register, r ≠ .tlb → sgx.regs r = ((wflatSt σ).setReg .minstret_increment bmi).regs r) ∧
  wtraceMsgs tid σ.wmWs.wRelp (esx ++ [.WEread WeakFetchEff.wakIfetch pa 4]) = msgs ∧
  (∀ mm : Wmsg, mm ∈ msgs → mm.wmTid = tid) ∧
  tstaleId la 8 (esx ++ [.WEread WeakFetchEff.wakIfetch pa 4])

/-- Lean-only: the post-tick state of the retire postlude. -/
def WkWalkCapstone.finOf (s : ExecSt) (tick : Bool) (c t p : BitVec 64) : ExecSt :=
  if tick then (((tsPost s).setReg .mcycle c).setReg .mtime t).setReg .mip p else tsPost s

theorem WkWalkCapstone.addiFinEq (sg : ExecSt) (va : BitVec 64) (rs1 rd : BitVec 5) (imm : BitVec 12)
    (tick : Bool) (c t p : BitVec 64) :
    addiFin sg va rs1 rd imm tick c t p = WkWalkCapstone.finOf (addiSx sg va rs1 rd imm) tick c t p := rfl

section leaf
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `scfg_cells`: the S-mode configuration cells the leaf reads and hands back unchanged. -/
def scfgCells (cpu : CPU) (dq : DFrac) (mstatus0 mie0 mideleg0 : BitVec 64)
    (pmpcfg0 : RegisterType .pmpcfg_n) (pmpaddr0 : RegisterType .pmpaddr_n)
    (pmar0 : RegisterType .pma_regions) (elp0 : RegisterType .elp) : IProp GF :=
  iprop(Register.cur_privilege ↦ᵣ[cpu]{dq} Privilege.Supervisor ∗
    Register.hart_state ↦ᵣ[cpu]{dq} HartState.HART_ACTIVE () ∗
    Register.misa ↦ᵣ[cpu]{dq} misaC ∗
    Register.menvcfg ↦ᵣ[cpu]{dq} menvcfgS ∗
    Register.mstatus ↦ᵣ[cpu]{dq} mstatus0 ∗
    Register.htif_tohost_base ↦ᵣ[cpu]{dq} (none : RegisterType .htif_tohost_base) ∗
    Register.pma_regions ↦ᵣ[cpu]{dq} pmar0 ∗
    Register.pmpcfg_n ↦ᵣ[cpu]{dq} pmpcfg0 ∗
    Register.pmpaddr_n ↦ᵣ[cpu]{dq} pmpaddr0 ∗
    Register.elp ↦ᵣ[cpu]{dq} elp0 ∗
    Register.mie ↦ᵣ[cpu]{dq} mie0 ∗
    Register.mideleg ↦ᵣ[cpu]{dq} mideleg0)

/-- Lean-only: the register reads of `scfgCells` (Rocq's `reg_valid_dq` block). -/
theorem WkWalkCapstone.scfgFacts (cpu : CPU) (f : RegFile) (dq : DFrac) (mstatus0 mie0 mideleg0 : BitVec 64)
    (pmpcfg0 : RegisterType .pmpcfg_n) (pmpaddr0 : RegisterType .pmpaddr_n)
    (pmar0 : RegisterType .pma_regions) (elp0 : RegisterType .elp) :
    regInterp (hlc := hlc) (GF := GF) cpu f ⊢
      scfgCells (GF := GF) cpu dq mstatus0 mie0 mideleg0 pmpcfg0 pmpaddr0 pmar0 elp0 -∗
      ⌜f .cur_privilege = .Supervisor ∧ f .hart_state = .HART_ACTIVE () ∧ f .misa = misaC ∧
        f .menvcfg = menvcfgS ∧ f .mstatus = mstatus0 ∧ f .htif_tohost_base = none ∧
        f .pma_regions = pmar0 ∧ f .pmpcfg_n = pmpcfg0 ∧ f .pmpaddr_n = pmpaddr0 ∧ f .elp = elp0 ∧
        f .mie = mie0 ∧ f .mideleg = mideleg0⌝ := by
  iintro Hr Hc
  unfold scfgCells
  icases Hc with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12⟩
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr H1 with ⟨%E1, Hr, -⟩
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr H2 with ⟨%E2, Hr, -⟩
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr H3 with ⟨%E3, Hr, -⟩
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr H4 with ⟨%E4, Hr, -⟩
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr H5 with ⟨%E5, Hr, -⟩
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr H6 with ⟨%E6, Hr, -⟩
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr H7 with ⟨%E7, Hr, -⟩
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr H8 with ⟨%E8, Hr, -⟩
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr H9 with ⟨%E9, Hr, -⟩
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr H10 with ⟨%E10, Hr, -⟩
  icases keepPure (wand_intro (reg_valid cpu f _ _ _)) $$ Hr H11 with ⟨%E11, Hr, -⟩
  ihave %E12 := wand_intro (reg_valid cpu f _ _ _) $$ Hr H12
  ipureintro
  exact ⟨E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12⟩

/-- Lean-only: the text window's flat bytes off the kernel text (Rocq's `bi.pure_forall` block
over `wkernel_text_flat`). -/
theorem WkWalkCapstone.textFlat [WeakGS GF] (σ : Wmstate) (bs : GMapF PAddr (BitVec 8)) (a : PAddr) (n : Nat)
    (b : Nat → BitVec 8) :
    wlogWf σ.wmLog →
    (∀ j, j < n → get? bs (a + BitVec.ofNat 64 j) = some (b j)) →
    wlatInterp (GF := GF) σ.wmImg σ.wmLog ⊢
      wkernelText (GF := GF) bs -∗
        ⌜∀ j : Nat, j < n → wflatMem σ.wmImg σ.wmLog (a + BitVec.ofNat 64 j) = some (b j)⌝ := by
  intro hwf hdom
  apply wand_intro
  by_cases hall : ∀ j : Nat, j < n → wflatMem σ.wmImg σ.wmLog (a + BitVec.ofNat 64 j) = some (b j)
  · exact pure_intro hall
  · have hex : ∃ j, j < n ∧ ¬ wflatMem σ.wmImg σ.wmLog (a + BitVec.ofNat 64 j) = some (b j) := by
      apply Classical.byContradiction
      intro hne
      exact hall fun j hj => Classical.byContradiction fun hp => hne ⟨j, hj, hp⟩
    obtain ⟨j, hj, hnp⟩ := hex
    refine (wand_elim (wkernelTextFlat σ bs _ (b j) hwf (hdom j hj))).trans (pure_mono fun h => ?_)
    exact absurd h.1 hnp

/-- Lean-only: the retire postlude's and the clock tick's register writes (Rocq's inline
`reg_update`s). -/
theorem WkWalkCapstone.postRegs (cpu : CPU) (s : ExecSt) (tick : Bool) (c t p pc0 m0 c0 t0 p0 : BitVec 64) :
    regInterp (hlc := hlc) (GF := GF) cpu s.regs ⊢
      Register.PC ↦ᵣ[cpu] pc0 -∗ Register.minstret ↦ᵣ[cpu] m0 -∗ Register.mcycle ↦ᵣ[cpu] c0 -∗
      Register.mtime ↦ᵣ[cpu] t0 -∗ Register.mip ↦ᵣ[cpu] p0 -∗
        |==> (regInterp cpu (WkWalkCapstone.finOf s tick c t p).regs ∗
          Register.PC ↦ᵣ[cpu] (s.regs .nextPC) ∗
          (∃ v : BitVec 64, Register.minstret ↦ᵣ[cpu] v) ∗
          (∃ v : BitVec 64, Register.mcycle ↦ᵣ[cpu] v) ∗
          (∃ v : BitVec 64, Register.mtime ↦ᵣ[cpu] v) ∗
          (∃ v : BitVec 64, Register.mip ↦ᵣ[cpu] v)) := by
  iintro Hr Hpc Hm Hc Ht Hp
  imod (wand_intro (reg_update cpu _ .PC pc0 (s.regs .nextPC))) $$ Hr Hpc with ⟨Hr, Hpc⟩
  have hmi : (tsTickPc s).regs .minstret_increment = s.regs .minstret_increment := by
    unfold tsTickPc; rw [ExecSt.setReg_regs]; exact RegFile.set_other _ _ _ _ (by decide)
  have htp : (tsTickPc s).regs = s.regs.set .PC (s.regs .nextPC) := rfl
  ihave Hpost : (|==> (regInterp (hlc := hlc) (GF := GF) cpu (tsPost s).regs ∗
      ∃ v : BitVec 64, Register.minstret ↦ᵣ[cpu] v)) $$ [Hr Hm]
  · cases hb : s.regs .minstret_increment
    · have he : tsPost s = tsTickPc s := by unfold tsPost; rw [hb]; rfl
      rw [he, htp]
      imodintro
      iframe Hr
      iexists m0
      iexact Hm
    · have he : tsPost s = (tsTickPc s).setReg .minstret
          (BitVec.addInt ((tsTickPc s).regs .minstret) 1) := by unfold tsPost; rw [hb]; rfl
      rw [he, ExecSt.setReg_regs, htp]
      imod (wand_intro (reg_update cpu _ .minstret m0
        (BitVec.addInt ((s.regs.set .PC (s.regs .nextPC)) .minstret) 1))) $$ Hr Hm with ⟨Hr, Hm⟩
      imodintro
      iframe Hr
      iexists _
      iexact Hm
  imod Hpost with ⟨Hr, Hm⟩
  cases tick
  · rw [show WkWalkCapstone.finOf s false c t p = tsPost s from rfl]
    imodintro
    iframe Hr Hpc Hm
    isplitl [Hc]
    · iexists c0; iexact Hc
    isplitl [Ht]
    · iexists t0; iexact Ht
    · iexists p0; iexact Hp
  · imod (wand_intro (reg_update cpu _ .mcycle c0 c)) $$ Hr Hc with ⟨Hr, Hc⟩
    imod (wand_intro (reg_update cpu _ .mtime t0 t)) $$ Hr Ht with ⟨Hr, Ht⟩
    imod (wand_intro (reg_update cpu _ .mip p0 p)) $$ Hr Hp with ⟨Hr, Hp⟩
    rw [show (WkWalkCapstone.finOf s true c t p).regs =
      (((tsPost s).regs.set .mcycle c).set .mtime t).set .mip p from rfl]
    imodintro
    iframe Hr Hpc Hm
    isplitl [Hc]
    · iexists c; iexact Hc
    isplitl [Ht]
    · iexists t; iexact Ht
    · iexists p; iexact Hp

/-- Lean-only: the ADDI's register moves past the walk (the `nextPC` pre-write, the destination
write, then `postRegs`). -/
theorem WkWalkCapstone.addiRegs (cpu : CPU) (sg : ExecSt) (va : BitVec 64) (rd : BitVec 5) (x : BitVec 64)
    (m : RegMap) (tick : Bool) (c t p pc0 npc0 m0 c0 t0 p0 : BitVec 64) (hrd : rd.toNat ≠ 0) :
    regInterp (hlc := hlc) (GF := GF) cpu sg.regs ⊢
      Register.PC ↦ᵣ[cpu] pc0 -∗ Register.nextPC ↦ᵣ[cpu] npc0 -∗ gprFile cpu m -∗
      Register.minstret ↦ᵣ[cpu] m0 -∗ Register.mcycle ↦ᵣ[cpu] c0 -∗
      Register.mtime ↦ᵣ[cpu] t0 -∗ Register.mip ↦ᵣ[cpu] p0 -∗
        |==> (regInterp cpu (WkWalkCapstone.finOf (addiSx' sg va rd x) tick c t p).regs ∗
          Register.PC ↦ᵣ[cpu] BitVec.addInt va 4 ∗
          Register.nextPC ↦ᵣ[cpu] BitVec.addInt va 4 ∗
          gprFile cpu (m.set rd x) ∗
          (∃ v : BitVec 64, Register.minstret ↦ᵣ[cpu] v) ∗
          (∃ v : BitVec 64, Register.mcycle ↦ᵣ[cpu] v) ∗
          (∃ v : BitVec 64, Register.mtime ↦ᵣ[cpu] v) ∗
          (∃ v : BitVec 64, Register.mip ↦ᵣ[cpu] v)) := by
  iintro Hr Hpc Hnpc Hgf Hm Hc Ht Hp
  imod (wand_intro (reg_update cpu _ .nextPC npc0 (BitVec.addInt va 4))) $$ Hr Hnpc with ⟨Hr, Hnpc⟩
  ieval (rewrite [← ExecSt.setReg_regs]) at Hr
  imod WeakLeafItype.gprFileWrite cpu (sg.setReg .nextPC (BitVec.addInt va 4)) m rd x hrd $$ Hr Hgf
    with ⟨Hr, Hgf⟩
  imod WkWalkCapstone.postRegs cpu ((sg.setReg .nextPC (BitVec.addInt va 4)).setGpr rd x) tick c t p
    pc0 m0 c0 t0 p0 $$ Hr Hpc Hm Hc Ht Hp with ⟨Hr, Hpc, Hm, Hc, Ht, Hp⟩
  have hnpc : ((sg.setReg .nextPC (BitVec.addInt va 4)).setGpr rd x).regs .nextPC = BitVec.addInt va 4 := by
    rw [WeakLeafWin.setGprRegsNe _ _ _ _ (by decide), ExecSt.setReg_regs, RegFile.set_same]
  ieval (rewrite [hnpc]) at Hpc
  rw [show addiSx' sg va rd x = (sg.setReg .nextPC (BitVec.addInt va 4)).setGpr rd x from rfl]
  imodintro
  iframe Hr Hpc Hnpc Hgf Hm Hc Ht Hp

end leaf

section capstone
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF] [WeakKpt.KptGS GF]

/-- Rocq `wwp_walk_addi`: THE CAPSTONE.  `addi rd, rs1, imm` at a kernel virtual address whose
fetch may TLB-miss, walk the three levels and CAS the leaf PTE's A-bit back. -/
theorem wwpWalkAddi (gen : Nat) (cpu : CPU) (root : BitVec 44) (T_kpt : Nat) (va pa : BitVec 64)
    (ppn : BitVec 44) (kpc : KPerm) (p2 p1 lw : BitVec 64) (imm : BitVec 12) (rs1 rd : BitVec 5)
    (w : BitVec 32) (m : RegMap) (ws : Wstate) (bs : GMapF PAddr (BitVec 8)) (dq : DFrac)
    (npc0 : BitVec 64) (mi0 : Bool) (mst0 mc0 mt0 mp0 mstatus0 mie0 mideleg0 : BitVec 64)
    (pmpcfg0 : RegisterType .pmpcfg_n) (pmpaddr0 : RegisterType .pmpaddr_n)
    (pmar0 : RegisterType .pma_regions) (elp0 : RegisterType .elp) :
    gen = 0 →
    rd.toNat ≠ 0 →
    -- the decode, in the σ-free reference-state form
    goodb0 WkWalkCapstone.dS (ext_decode w) WkWalkCapstone.dstateS = true →
    exec (ext_decode w) WkWalkCapstone.dstateS =
      some (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI), WkWalkCapstone.dstateS) →
    -- the page-table geometry
    (∀ (a d : BitVec 1) (mxr dosum : Bool),
      wpteCheckOk (.InstructionFetch ()) .Supervisor mxr dosum (pteSetAD (mkPte ppn kpc.flags) a d)) →
    (∀ a d : BitVec 1, wpteValid (pteSetAD (mkPte ppn kpc.flags) a d)) →
    (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false →
    zero_extend (m := 64) (ppn +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0) = pa →
    accWf va 4 →
    accWf (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8 →
    accWf pa 4 →
    raccDisj (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8 pa 4 →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    is_aligned_paddr (.Physaddr pa) 4 = true →
    inRam pa 4 →
    (∀ j : Nat, j < 4 → paZ (pa + BitVec.ofNat 64 j) ≠ 0) →
    isRVC (Sail.BitVec.extractLsb w 15 0) = false →
    -- the configuration values
    _get_Mstatus_SXL mstatus0 = 2#2 →
    (_get_Mstatus_SIE mstatus0 == 1#1) = false →
    mie0 &&& ~~~mideleg0 = 0#64 →
    (elp0 == landing_pad_bits_backwards .LP_EXPECTED) = false →
    pmar0 = bootPMA →
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A pmpcfg0[0]!) = .TOR →
    zopz0zKzJ_u (zeros (n := 64)) pmpaddr0[0]! = false →
    (_get_Pmpcfg_ent_X pmpcfg0[0]! == 1#1) = true →
    ramEnd ≤ pmpaddr0[0]!.toNat * 4 →
    T_kpt ≤ ws.wVrNew →
    -- the resources
    kmapAt (hlc := hlc) (WeakKpt.svpnOf va) (kLeaf ppn kpc 0#1 0#1) ∗
      wtlbResPt (hlc := hlc) (GF := GF) cpu root T_kpt ∗
      Register.PC ↦ᵣ[cpu] va ∗
      Register.nextPC ↦ᵣ[cpu] npc0 ∗
      gprFile (hlc := hlc) (GF := GF) cpu m ∗
      Register.minstret_increment ↦ᵣ[cpu] mi0 ∗
      Register.minstret ↦ᵣ[cpu] mst0 ∗
      Register.mcycle ↦ᵣ[cpu] mc0 ∗
      Register.mtime ↦ᵣ[cpu] mt0 ∗
      Register.mip ↦ᵣ[cpu] mp0 ∗
      scfgCells (GF := GF) cpu dq mstatus0 mie0 mideleg0 pmpcfg0 pmpaddr0 pmar0 elp0 ∗
      wkernelText (GF := GF) bs ∗
      ⌜∀ j : Nat, j < 4 → get? bs (pa + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)⌝ ∗
      hartWs (GF := GF) cpu ws ∗
      (∀ σ : Wmstate, wmstateInterp (hlc := hlc) (GF := GF) cpu σ ={⊤}=∗
        ⌜wwalkScn root va p2 p1 lw σ⌝ ∗ wmstateInterp (hlc := hlc) (GF := GF) cpu σ) ∗
      (∀ ws' : Wstate, ⌜wsLe ws ws'⌝ -∗
        (Register.PC ↦ᵣ[cpu] BitVec.addInt va 4 ∗
         Register.nextPC ↦ᵣ[cpu] BitVec.addInt va 4 ∗
         gprFile (hlc := hlc) (GF := GF) cpu (m.set rd (m.get rs1 + sign_extend (m := 64) imm)) ∗
         (∃ b : Bool, Register.minstret_increment ↦ᵣ[cpu] b) ∗
         (∃ v : BitVec 64, Register.minstret ↦ᵣ[cpu] v) ∗
         (∃ v : BitVec 64, Register.mcycle ↦ᵣ[cpu] v) ∗
         (∃ v : BitVec 64, Register.mtime ↦ᵣ[cpu] v) ∗
         (∃ v : BitVec 64, Register.mip ↦ᵣ[cpu] v) ∗
         wtlbResPt (hlc := hlc) (GF := GF) cpu root T_kpt ∗
         scfgCells (GF := GF) cpu dq mstatus0 mie0 mideleg0 pmpcfg0 pmpaddr0 pmar0 elp0) -∗
        hartWs (GF := GF) cpu ws' -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) ⊢
    wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hgen hrd hgood hdecd hchk hval hcanon hid4k haccva haccla haccpa hdisj halv halp hram hW0
    hnotRVC hSXL hSIE hand0 help0 hall hA hord hX hcov hT
  iintro ⟨Hkmap, Hres, Hpc, Hnpc, Hgf, Hmi, Hmst, Hmc, Hmt, Hmip, Hcfg, #Htext, %hbs, Hhws, Hcb, Hcont⟩
  iapply wpWwalkStep gen cpu va
    (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0))
    (wwalkFilter (mkPte ppn kpc.flags) lw)
    (wsiteAddi (some cpu.val) root va pa p2 p1 (mkPte ppn kpc.flags) lw w) (fun _ _ => True)
    hgen haccva haccla (wwalkCertAddi cpu.val root va pa p2 p1 (mkPte ppn kpc.flags) lw w)
  iintro %σ Hσ
  -- the caller's scenario, at σ
  imod Hcb $$ %σ Hσ with ⟨%hscn, Hσ⟩
  obtain ⟨hs2, hs1, hs0, hnvfree, hpinva⟩ := hscn
  iunfold wmstateInterp at Hσ
  icases Hσ with ⟨%hbnd, %hnvh, %hwf, Hreg, Hdev, Hlog, Hlat, Hwsa⟩
  -- every register the step reads
  icases keepPure (WkWalkCapstone.scfgFacts cpu σ.wmRegs dq mstatus0 mie0 mideleg0 pmpcfg0 pmpaddr0
    pmar0 elp0) $$ Hreg Hcfg with ⟨%hcf, Hreg, Hcfg⟩
  obtain ⟨lpriv, lhart, lmisa, lmenv, lmstatus, lhtif, lpma, lpmpc, lpmpa, lelp, lmie, lmdl⟩ := hcf
  icases keepPure (wand_intro (reg_valid cpu σ.wmRegs .PC _ va)) $$ Hreg Hpc with ⟨%lpc, Hreg, Hpc⟩
  icases keepPure (wand_intro (hartWsAgree cpu σ.wmWs ws)) $$ Hwsa Hhws with ⟨%hwseq, Hwsa, Hhws⟩
  -- the source operand, off the register file
  icases keepPure (WeakLeafItype.gprFileValue cpu σ.wmRegs m rs1) $$ Hreg Hgf with ⟨%hrv, Hreg, Hgf⟩
  -- the text window
  icases keepPure (WkWalkCapstone.textFlat σ bs pa 4 (nthByte (n := 4) w) hwf hbs) $$ Hlat Htext
    with ⟨%hbytes, Hlat, -⟩
  icases keepPure (wkernelTextFetchPinned σ bs pa 4 haccpa (fun j hj => ⟨_, hbs j hj⟩) hwf) $$ Hlat Htext
    with ⟨%hpinpa, Hlat, -⟩
  -- the fupd's register-shaped premises, at σ
  have lsxl : _get_Mstatus_SXL (σ.wmRegs .mstatus) = 2#2 := by rw [lmstatus]; exact hSXL
  have lall : σ.wmRegs .pma_regions = bootPMA := lpma.trans hall
  have lA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (σ.wmRegs .pmpcfg_n)[0]!) = .TOR := by
    rw [lpmpc]; exact hA
  have lord : zopz0zKzJ_u (zeros (n := 64)) (σ.wmRegs .pmpaddr_n)[0]! = false := by
    rw [lpmpa]; exact hord
  have lX : (_get_Pmpcfg_ent_X (σ.wmRegs .pmpcfg_n)[0]! == 1#1) = true := by rw [lpmpc]; exact hX
  have lcov : ramEnd ≤ (σ.wmRegs .pmpaddr_n)[0]!.toNat * 4 := by rw [lpmpa]; exact hcov
  have lT : T_kpt ≤ σ.wmWs.wVrNew := by rw [← hwseq]; exact hT
  -- THE FUPD
  imod wkptFetchPeelAt cpu root T_kpt (some cpu.val) va pa ppn kpc σ ⊤ w CoPset.subseteq_top hchk hval
    hcanon hid4k hwf lmisa lmenv lhtif lpriv lsxl
    (fun bf => execEffEffectivePrivilegeFetch _ _ _) (fun bf => execEffIsShadowStackFetch _)
    lall lT lpc halv halp hram haccpa hW0 hpinpa hbytes lA lord lX lcov
    $$ [$Hkmap $Hreg $Hlog $Hlat $Hres]
    with ⟨%p2', %p1', %lw', %region, %hvar, %hslots, %_hpins, %_hdj, %_hcoll, %_hnvf8, %hexpb,
      %hgatesb, %hexecp, Hreg, Hwand, Harm⟩
  -- the minted slot words collapse onto the parameters
  obtain ⟨hs2', hs1', hs0'⟩ := hslots
  obtain rfl : p2 = p2' := ptSlotMemInj _ _ _ _ hs2 hs2'
  obtain rfl : p1 = p1' := ptSlotMemInj _ _ _ _ hs1 hs1'
  obtain rfl : lw = lw' := ptSlotMemInj _ _ _ _ hs0 hs0'
  -- ================= THE SITE =================
  have hgates : wfgateRegs σ.wmRegs pa := by
    unfold wfgateRegs
    rw [lpmpc, lpmpa, lpma, lhtif, lpriv]
    exact ⟨hram, hA, hord, hX, hcov, hall, rfl, rfl⟩
  have hdecbr : ∀ t : ExecSt,
      (∀ r : Register, r ≠ .tlb → r ≠ .minstret_increment → t.regs r = σ.wmRegs r) →
      execEff (ext_decode w) t = some (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI), t, []) := by
    intro t hag
    refine execEffDecodeBridge WkWalkCapstone.dS (ext_decode w) WkWalkCapstone.dstateS t _ ?_ hgood hdecd
    apply WkWalkCapstone.agreeS
    · rw [hag _ (by decide) (by decide)]; exact lpriv
    · rw [hag _ (by decide) (by decide)]; exact lmenv
    · rw [hag _ (by decide) (by decide)]; exact lmisa
  have hinstr : ∀ b : Bool, winstrSite (wmi σ b) w (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI))
      (fGpr rd) := fun b =>
    winstrSiteWmi σ b w _ (fGpr rd) hdecbr (by rw [lelp]; exact help0)
      (wexecRegonlyAddi rs1 rd imm hrd) (fGprHartState rd) lhart
  have hfsite : ∀ b : Bool, wfetchSite (some cpu.val) (wmi σ b) root va pa p2 p1 (mkPte ppn kpc.flags)
      lw w := fun b =>
    wfetchSiteWmi (some cpu.val) σ root va pa p2 p1 (mkPte ppn kpc.flags) lw w b (hexpb b) lpc halv halp
      hnotRVC hgates hdisj haccpa hW0 hpinpa hbytes
  have hdisp : ∀ b : Bool, execEff (dispatchInterrupt .Supervisor) (wflatSt (wmi σ b)) =
      some (none, wflatSt (wmi σ b), []) := by
    intro b
    apply execEffDispatchInterruptSupervisorNone
    · rw [regAtWmi σ b .misa (by decide), lmisa]; decide
    · rw [regAtWmi σ b .mstatus (by decide), lmstatus]; exact hSIE
    · rw [regAtWmi σ b .mie (by decide), regAtWmi σ b .mideleg (by decide), lmie, lmdl]; exact hand0
  have htot : ∀ s : ExecSt, ∃ t : ExecSt, execEff (tick_clock ()) s = some ((), t, []) := by
    intro s
    obtain ⟨c, t, p, heq⟩ := execEffTickClock s
    exact ⟨_, heq⟩
  have hP : wsiteAddi (some cpu.val) root va pa p2 p1 (mkPte ppn kpc.flags) lw w σ := by
    refine ⟨region, fun tick => ?_⟩
    exact ⟨lpriv, lhart, hdisp, fun b => ⟨hexpb b, hgatesb b⟩, halv, hnotRVC, hdisj, haccpa, hW0, hpinpa,
      hbytes, halp, hexecp, devAddrRam pa 4 hram,
      fun b => wexecTailOf (some cpu.val) (wmi σ b) root va pa p2 p1 (mkPte ppn kpc.flags) lw w _
        (fGpr rd) (hfsite b) (hinstr b),
      fun b => wstepPostTailOf (some cpu.val) (wmi σ b) root va pa p2 p1 (mkPte ppn kpc.flags) lw w _
        (fGpr rd) (hfsite b) (hinstr b) (hdisp b),
      wstepTickTailOfTick (some cpu.val) σ tick,
      wstepFamilyReadyOf (some cpu.val) σ root va pa p2 p1 (mkPte ppn kpc.flags) lw w _ (fGpr rd) tick
        hfsite hinstr (fun _ => htot)⟩
  have lelpv : (σ.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false := by
    rw [lelp]; exact help0
  -- ================= THE RULE'S σ-OUTPUTS =================
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact lpc
  isplitr
  · ipureintro; exact hpinva
  isplitr
  · ipureintro; exact hP
  isplitr
  · ipureintro
    exact wsiteAddiAdmFilter cpu.val root va pa p2 p1 (mkPte ppn kpc.flags) lw w σ lpc hP
  isplitr
  · ipureintro
    rw [bmRead_of_bytes (wflatMem σ.wmImg σ.wmLog) _ 8 lw hs0.1]; rfl
  isplitr
  · -- REDUCIBILITY: the family member at the COHERENT word, transferred back to `execEff` by §2
    -- (the patch is the identity there) and then to `exec`
    obtain ⟨bmi, hsi⟩ := execEffShouldIncMinstretSome .Supervisor (wflatSt σ)
    obtain ⟨av0, dv0, hlweq⟩ := hvar
    have hle0 : pteAdLe (pteSetAD (mkPte ppn kpc.flags) av0 dv0) lw := by
      rw [← hlweq]; exact pteAdLeRefl _
    obtain ⟨sgx, esx, hexm, hmemx, -, hrgx, hshape⟩ := wwalkMemberFull (some cpu.val) (wmi σ bmi) root
      va pa p2 p1 (mkPte ppn kpc.flags) lw av0 dv0 (hexpb bmi) hle0
    obtain ⟨hmr, -⟩ := wstepReadyAtMember (some cpu.val) (wmi σ bmi) root va pa p2 p1 (mkPte ppn kpc.flags)
      lw w _ (fGpr rd) false (hfsite bmi) (hinstr bmi) (fun _ => htot)
      (pteSetAD (mkPte ppn kpc.flags) av0 dv0) sgx esx hexm hmemx hrgx
    obtain ⟨c, t, p, hstep⟩ := execStaleStepAddi σ _ va pa w rs1 rd imm bmi false
      (pteSetAD (mkPte ppn kpc.flags) av0 dv0) sgx esx haccla haccpa hdisj lpriv lhart lpc lelpv hrd hsi
      (hdisp bmi) halv hnotRVC (hinstr bmi).1 hexm hmr hrgx
    have hid : bmWrite (wflatSt σ).mem
        (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8
        (pteSetAD (mkPte ppn kpc.flags) av0 dv0) = (wflatSt σ).mem := by
      rw [← hlweq]; exact writeBytesId _ _ 8 lw hs0.1
    iexists addiFin sgx va rs1 rd imm false c t p
    ipureintro
    exact execEffExec _ _ _ _ _ (execEffOfExecStaleId _ 8 _ (riscvStep false) haccla (wflatSt σ) () _ _
      hid hstep (tstaleIdOfShape _ _ _ pa esx hdisj haccpa hshape))
  -- ================= THE CONTINUATION =================
  inext
  iintro %tick %σ' %u %es %_hadm %hΦu %hex %_hlat %hlog %hpost %_hQ
  obtain ⟨himg', -, hwsle, hwf', hbnd'⟩ := hpost
  obtain ⟨bmi, hsi⟩ := execEffShouldIncMinstretSome .Supervisor (wflatSt σ)
  obtain ⟨av, dv, huw, hle⟩ := wwalkFilterInv (mkPte ppn kpc.flags) lw u hΦu
  -- the two ghost arms converge: one member, one message list
  ihave Hbdl : (|==> ∃ (msgs : List Wmsg) (sgx : ExecSt) (esx : List Weff),
      ⌜WkWalkCapstone.memberOk (some cpu.val) σ bmi
        (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) va pa
        (pteSetAD (mkPte ppn kpc.flags) av dv) msgs sgx esx⌝ ∗
      wlogAuth (GF := GF) (σ.wmLog ++ msgs) ∗ wlatInterp (GF := GF) σ.wmImg (σ.wmLog ++ msgs)) $$ [Harm]
  · icases Harm with (⟨%hro, Hlogr, Hlatr⟩ | ⟨%lw'', %_hupd, %hfam, Hlogr, Hlatr⟩)
    · obtain ⟨sgx, esx, hexm, hmemx, hmdevx, hrgx, hesx⟩ := hro av dv hle bmi
      imodintro
      iexists [], sgx, esx
      rw [List.append_nil]
      iframe Hlogr Hlatr
      ipureintro
      exact ⟨hexm, Or.inl hmemx, hmdevx, hrgx, wtraceMsgsWalkRoApp _ _ _ _ _ pa esx hesx,
        fun mm hin => absurd hin List.not_mem_nil, tstaleIdOfShape _ _ _ pa esx hdisj haccpa (Or.inl hesx)⟩
    · obtain ⟨wtr, hfam⟩ := hfam
      obtain ⟨sgx, esx, hexm, hmemx, hmdevx, hrgx, hesx⟩ := hfam av dv hle bmi
      imodintro
      iexists [wwriteMsg (some cpu.val) .WCexcl
        (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb (WeakKpt.svpnOf va) 8 0)) 8 lw''], sgx, esx
      iframe Hlogr Hlatr
      ipureintro
      exact ⟨hexm, Or.inr ⟨lw'', hmemx⟩, hmdevx, hrgx, wtraceMsgsWalkWbApp _ _ _ _ _ pa lw'' wtr esx hesx,
        fun mm hin => by rw [List.mem_singleton] at hin; subst hin; rfl,
        tstaleIdOfShape _ _ _ pa esx hdisj haccpa (Or.inr ⟨lw'', wtr, hesx⟩)⟩
  imod Hbdl with ⟨%msgs, %sgx, %esx, %hmo, Hlog, Hlat⟩
  obtain ⟨hexm, hmemx, hmdevx, hrgx, hmsgs, hown, _htsid⟩ := hmo
  -- the text read at the member, and the whole step, concretely
  obtain ⟨hmr, -⟩ := wstepReadyAtMember (some cpu.val) (wmi σ bmi) root va pa p2 p1 (mkPte ppn kpc.flags)
    lw w _ (fGpr rd) tick (hfsite bmi) (hinstr bmi) (fun _ => htot)
    (pteSetAD (mkPte ppn kpc.flags) av dv) sgx esx hexm hmemx hrgx
  obtain ⟨c, t, p, hstep⟩ := execStaleStepAddi σ _ va pa w rs1 rd imm bmi tick
    (pteSetAD (mkPte ppn kpc.flags) av dv) sgx esx haccla haccpa hdisj lpriv lhart lpc lelpv hrd hsi
    (hdisp bmi) halv hnotRVC (hinstr bmi).1 hexm hmr hrgx
  -- `execStale` is a function: the successor is that state
  rw [huw, hstep] at hex
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hex
  obtain ⟨hfin, hes⟩ := hex
  have hregs' : σ'.wmRegs = (addiFin sgx va rs1 rd imm tick c t p).regs := by
    rw [hfin]; rfl
  have hdev' : σ'.wmDev = σ.wmDev := by
    rw [← wflatStDev σ', ← hfin, mdevAddiFin]; exact hmdevx
  have hlog' : σ'.wmLog = σ.wmLog ++ msgs := by rw [hlog, ← hes, hmsgs]
  -- the destination value, at the member's registers
  have hgx : sgx.gpr rs1 = m.get rs1 := by
    rw [← hrv]
    unfold ExecSt.gpr
    apply uxaXget_congr
    intro r hr
    have hrt : r ≠ .tlb := by rintro rfl; exact absurd hr (by decide)
    have hrm : r ≠ .minstret_increment := by rintro rfl; exact absurd hr (by decide)
    rw [hrgx r hrt]
    exact regAtWmi σ bmi r hrm
  have hav := gprAddiValOff rs1 imm sgx (BitVec.addInt va 4) _ hgx
  have hfineq : addiFin sgx va rs1 rd imm tick c t p =
      WkWalkCapstone.finOf (addiSx' sgx va rd (m.get rs1 + sign_extend (m := 64) imm)) tick c t p := by
    rw [WkWalkCapstone.addiFinEq]
    unfold addiSx addiSx'
    rw [hav]
  -- THE REGISTER MOVES
  imod (wand_intro (reg_update cpu σ.wmRegs .minstret_increment mi0 bmi)) $$ Hreg Hmi with ⟨Hreg, Hmi⟩
  imod Hwand $$ %bmi %av %dv %sgx %esx %hle %hexm Hreg with ⟨Hreg, Hres⟩
  imod WkWalkCapstone.addiRegs cpu sgx va rd (m.get rs1 + sign_extend (m := 64) imm) m tick c t p va npc0
    mst0 mc0 mt0 mp0 hrd $$ Hreg Hpc Hnpc Hgf Hmst Hmc Hmt Hmip
    with ⟨Hreg, Hpc, Hnpc, Hgf, Hmst, Hmc, Hmt, Hmip⟩
  -- the hart's weak state, and the interpretation at σ'
  imod (hartWsUpdate cpu σ.wmWs ws σ'.wmWs) $$ [$Hwsa $Hhws] with ⟨Hwsa, Hhws⟩
  imod Hclose
  imodintro
  isplitl [Hreg Hdev Hlog Hlat Hwsa]
  · iunfold wmstateInterp
    isplitr
    · ipureintro; exact hbnd'
    isplitr
    · ipureintro; rw [hlog']; exact nvHartOfFree _ _ _ _ hnvfree hown
    isplitr
    · ipureintro; exact hwf'
    rw [hregs', hfineq, hdev', hlog', himg']
    iframe Hreg Hdev Hlog Hlat Hwsa
  · have hwsle' : wsLe ws σ'.wmWs := by rw [hwseq]; exact hwsle
    iapply Hcont $$ %σ'.wmWs %hwsle' [Hpc Hnpc Hgf Hmi Hmst Hmc Hmt Hmip Hres Hcfg] Hhws
    iframe Hpc Hnpc Hgf Hmst Hmc Hmt Hmip Hres Hcfg
    iexists bmi
    iexact Hmi

end capstone

end Weak
