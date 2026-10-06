/-
Weak: interrupt dispatch, `run_hart_active`, the TLB.

Rocq: `iris/RiscvTryStep.v` (`exec_dispatchInterrupt_none`,
`exec_getPendingSet_machine_none`, `exec_is_landing_pad`, `exec_hart_active_progress`),
`iris/SmodeCore.v` (`exec_getPendingSet_supervisor_none`,
`exec_hart_active_progress_*_gen`), `iris/SmodePte.v` (`exec_lookup_TLB_*`),
`iris/Pt4kWalk.v` (`exec_lookup_TLB_hit_ent`), `iris/PtTreeAdue.v` (`pt_fill_ent`,
`exec_add_to_TLB_pt`) @ xxvzwolszwmp.

**Conventions (all `Weak/ExecSC*.lean` files; the deviations every statement shares).**
Statements are about `Weak.exec` over the LEAN model (sail-riscv `070832a1`,
`-D SYMBOLIC`: announce events silent), not Rocq's `exec` over the Coq model.
* GPRs: Rocq `if uint i =? 0 then zero_reg else register_lookup (R_bitvector_64
  (gpr_of_Z (uint i))) s.(sregs)` ↦ `s.gpr i`; Rocq `if uint rd =? 0 then s else
  set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)` ↦
  `s.setGpr rd v` (`Weak/ExecSC.lean`).  Where Rocq has a `uint rd ≠ 0` premise and a
  plain `set_reg`, the premise is kept and the result is `setGpr` (equal under it).
* Spelling: `register_lookup r s.(sregs)` ↦ `s.regs r`; `eq_vec x 'b"1" = b` ↦
  `(x == 1#1) = b`; `vec_access_dec v i` ↦ `v[i]!`; `vec_update_dec v i x` ↦
  `vectorUpdate v i x`; `uint x` ↦ `x.toNat`; `Z` widths/indices ↦ `Nat`;
  `mword n` ↦ `BitVec n`; `tt` ↦ `()`; `zeros' n` ↦ `zeros (n := n)`.
* Memory: `dev_addr pa = false` ↦ `devAddr pa = false`; Rocq's byte window
  `∀ j < n, s.(mem) !! pa_add pa j = Some (nth_byte w j)` ↦ `BytesAt s pa n w`;
  `MState s.(sregs) (write_bytes s.(mem) pa n v) s.(mdev)` ↦
  `s.setMem (bmWrite s.mem pa n v)`.  An ifetch is a RAM read in `exec`
  (`Weak/Exec.lean`), so the fetch facts read the byte map (`AK_ifetch` plays no role).
* `hartSupports` is pure in Lean: Rocq `exec (hartSupports X) s = Some (true, s)` ↦
  `hartSupports .X = true`; Rocq's fuelled `_rec_currentlyEnabled` facts are stated on
  `currentlyEnabled`.  Rocq loops (`foreach_ZM_up'`, `untilMT`) ↦ lean-sail's `IntRange`
  `forIn` and `untilFuelM`.
* Rocq section hypotheses become theorem premises; section `Let`s become `def`s or are
  inlined; premise bundles that several statements share are `structure`s
  (`FetchM4`, `FetchM2`, `FetchS`, `MemM8`, `AmoS4`), each field a Rocq hypothesis.

**Deviations from Rocq.**
1. `exec_dispatchInterrupt_none` is stated at any privilege.
2. `exec_hart_active_progress*`: the next PC is `BitVec.addInt pc 4/2` (Rocq
   `add_vec_int`); the landing-pad premise is `(s_f.regs .elp ==
   landing_pad_bits_backwards .LP_EXPECTED) = false`.
3. `exec_getPendingSet_machine_none`: the section's `cES`/`HecES`/`HcEStrue` are kept
   as premises (Lean's `getPendingSet` does not need them).

**Name map (Rocq → Lean).**  RiscvTryStep: `exec_dispatchInterrupt_none` ↦
`execDispatchInterruptNone`, `exec_getPendingSet_machine_none` ↦
`execGetPendingSetMachineNone`, `exec_is_landing_pad` ↦ `execIsLandingPad`,
`exec_hart_active_progress` ↦ `execHartActiveProgress`.  SmodeCore:
`exec_getPendingSet_supervisor_none` ↦ `execGetPendingSetSupervisorNone`,
`exec_hart_active_progress_base_gen` ↦ `execHartActiveProgressBaseGen`,
`exec_hart_active_progress_RVC_gen` ↦ `execHartActiveProgressRVCGen`.  SmodePte:
`exec_lookup_TLB_miss` ↦ `execLookupTLBMiss`, `exec_lookup_TLB_nomatch_s` ↦
`execLookupTLBNomatchS`.  Pt4kWalk: `exec_lookup_TLB_hit_ent` ↦
`execLookupTLBHitEnt`.  PtTreeAdue: `pt_fill_ent` ↦ `ptFillEnt`,
`exec_add_to_TLB_pt` ↦ `execAddToTLBPt`.

**Dropped**: none of the names the weak tier uses.
-/
import Weak.ExecSC5

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. Interrupt dispatch (Rocq `RiscvTryStep`, `SmodeCore`) -/

/-- Rocq `RiscvTryStep.exec_dispatchInterrupt_none` (at any privilege). -/
theorem execDispatchInterruptNone (p : Privilege) (s : ExecSt)
    (h : exec (getPendingSet p) s = some (none, s)) : exec (dispatchInterrupt p) s = some (none, s) := by
  unfold dispatchInterrupt
  simp only [execBind, h, execReturnm]

/-- Rocq `RiscvTryStep.exec_getPendingSet_machine_none` (section `ExecPending`'s premises). -/
theorem execGetPendingSetMachineNone (s : ExecSt) (cES : Bool)
    (hecES : exec (currentlyEnabled .Ext_S) s = some (cES, s)) (_hcES : cES = true)
    (hmIE : (_get_Mstatus_MIE (s.regs .mstatus) == 1#1) = false) :
    exec (getPendingSet .Machine) s = some (none, s) := by
  have hext : ∃ v, exec (external_interrupts_pending ()) s = some (v, s) := by
    unfold external_interrupts_pending
    cases cES <;> exec_run [hecES] <;> exact ⟨_, rfl⟩
  obtain ⟨v, hv⟩ := hext
  unfold getPendingSet read_mip
  have hmm : (Privilege.Machine == Privilege.Machine) = true := rfl
  have hms : (Privilege.Machine == Privilege.Supervisor) = false := rfl
  have hmu : (Privilege.Machine == Privilege.User) = false := rfl
  cases cES <;> exec_run [hecES, hv, hmm, hms, hmu, hmIE, Bool.or_false, Bool.false_or]

/-- Rocq `SmodeCore.exec_getPendingSet_supervisor_none`. -/
theorem execGetPendingSetSupervisorNone (s : ExecSt) (mie_v mideleg_v mstatus_v : BitVec 64)
    (hES : exec (currentlyEnabled .Ext_S) s = some (true, s)) (hmie : s.regs .mie = mie_v)
    (hmdl : s.regs .mideleg = mideleg_v) (hms : s.regs .mstatus = mstatus_v)
    (hand0 : mie_v &&& ~~~mideleg_v = 0#64)
    (hSIE : (_get_Mstatus_SIE mstatus_v == 1#1) = false) :
    exec (getPendingSet .Supervisor) s = some (none, s) := by
  have hext : ∃ v, exec (external_interrupts_pending ()) s = some (v, s) := by
    unfold external_interrupts_pending
    exec_run [hES]
    exact ⟨_, rfl⟩
  obtain ⟨v, hv⟩ := hext
  have hpm : ∀ x : BitVec 64, (x &&& (mie_v &&& ~~~mideleg_v) != zeros (n := 64)) = false := by
    intro x; rw [hand0]; simp [zeros]
  unfold getPendingSet read_mip
  have h1 : (Privilege.Supervisor == Privilege.Machine) = false := rfl
  have h2 : (Privilege.Supervisor == Privilege.Supervisor) = true := rfl
  have h3 : (Privilege.Supervisor == Privilege.User) = false := rfl
  exec_run [hES, hv, h1, h2, h3, hmie, hmdl, hms, hSIE, hpm, Bool.or_false, Bool.false_or, Bool.or_true]

/-- Rocq `RiscvTryStep.exec_is_landing_pad`. -/
theorem execIsLandingPad (s : ExecSt) :
    exec (is_landing_pad_expected ()) s =
      some (s.regs .elp == landing_pad_bits_backwards .LP_EXPECTED, s) := rfl

/-! ## 2. `run_hart_active` (Rocq `RiscvTryStep.exec_hart_active_progress`,
`SmodeCore.exec_hart_active_progress_*_gen`) -/

/-- Rocq `SmodeCore.exec_hart_active_progress_base_gen`. -/
theorem execHartActiveProgressBaseGen (priv : Privilege) (s s_f s_x : ExecSt) (w : BitVec 32)
    (instr : instruction) (pc : BitVec 64) (resf : ExecutionResult)
    (hpriv : s.regs .cur_privilege = priv) (hdisp : exec (dispatchInterrupt priv) s = some (none, s))
    (hfetch : exec (fetch ()) s = some (.F_Base w, s_f)) (hdec : exec (ext_decode w) s_f = some (instr, s_f))
    (hlpad : (s_f.regs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false)
    (_hnotlpad : is_lpad_instruction instr = false) (hpc : s_f.regs .PC = pc)
    (hexec : exec (execute instr) (s_f.setReg .nextPC (BitVec.addInt pc 4)) = some (resf, s_x))
    (hnot : match resf with | .ExecuteAs _ => False | _ => True) :
    exec (run_hart_active 0) s = some (.Step_Execute (resf, zero_extend (m := 32) w), s_x) := by
  unfold run_hart_active ext_fetch_hook get_config_print_instr
  rw [execCatchEarlyReturn]
  exec_run [hpriv, hdisp, hfetch, execInstrAnnounce, hdec, execIsLandingPad, hlpad, hpc, hexec]
  cases resf <;> simp at hnot <;> rfl

/-- Rocq `RiscvTryStep.exec_hart_active_progress` (section `HartActiveProgress`, Machine). -/
theorem execHartActiveProgress (s s_f s_x : ExecSt) (w : BitVec 32) (instr : instruction) (pc : BitVec 64)
    (resf : ExecutionResult) (hpriv : s.regs .cur_privilege = .Machine)
    (hdisp : exec (dispatchInterrupt .Machine) s = some (none, s))
    (hfetch : exec (fetch ()) s = some (.F_Base w, s_f)) (hdec : exec (ext_decode w) s_f = some (instr, s_f))
    (hlpad : (s_f.regs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false)
    (hnotlpad : is_lpad_instruction instr = false) (hpc : s_f.regs .PC = pc)
    (hexec : exec (execute instr) (s_f.setReg .nextPC (BitVec.addInt pc 4)) = some (resf, s_x))
    (hnot : match resf with | .ExecuteAs _ => False | _ => True) :
    exec (run_hart_active 0) s = some (.Step_Execute (resf, zero_extend (m := 32) w), s_x) :=
  execHartActiveProgressBaseGen .Machine s s_f s_x w instr pc resf hpriv hdisp hfetch hdec hlpad hnotlpad hpc
    hexec hnot

/-- Rocq `SmodeCore.exec_hart_active_progress_RVC_gen`. -/
theorem execHartActiveProgressRVCGen (priv : Privilege) (s s_f s_x : ExecSt) (h : BitVec 16)
    (instr other : instruction) (pc : BitVec 64) (resf : ExecutionResult)
    (hpriv : s.regs .cur_privilege = priv) (hdisp : exec (dispatchInterrupt priv) s = some (none, s))
    (hfetch : exec (fetch ()) s = some (.F_RVC h, s_f))
    (hdec : exec (ext_decode_compressed h) s_f = some (instr, s_f))
    (hlpad : (s_f.regs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false) (hpc : s_f.regs .PC = pc)
    (hzca : exec (currentlyEnabled .Ext_Zca) s_f = some (true, s_f))
    (hexec : exec (execute instr) (s_f.setReg .nextPC (BitVec.addInt pc 2)) =
      some (.ExecuteAs other, s_f.setReg .nextPC (BitVec.addInt pc 2)))
    (hother : exec (execute other) (s_f.setReg .nextPC (BitVec.addInt pc 2)) = some (resf, s_x)) :
    exec (run_hart_active 0) s = some (.Step_Execute (resf, zero_extend (m := 32) h), s_x) := by
  unfold run_hart_active ext_fetch_hook get_config_print_instr
  rw [execCatchEarlyReturn]
  exec_run [hpriv, hdisp, hfetch, execInstrAnnounce, hdec, execIsLandingPad, hlpad, hzca, hpc, hexec, hother]

/-! ## 3. The TLB (Rocq `SmodePte`, `Pt4kWalk`, `PtTreeAdue`) -/

/-- Rocq `SmodePte.exec_lookup_TLB_miss`. -/
theorem execLookupTLBMiss (vpn : BitVec 27) (asid : BitVec 16) (tlbvec : Vector (Option TLB_Entry) 64)
    (s : ExecSt) (htlb : s.regs .tlb = tlbvec) (hnone : tlbvec[tlb_hash 39 vpn]! = none) :
    exec (lookup_TLB 39 asid vpn) s = some (none, s) := by
  unfold lookup_TLB
  exec_run [htlb]
  rw [hnone]
  rfl

/-- Rocq `SmodePte.exec_lookup_TLB_nomatch_s`. -/
theorem execLookupTLBNomatchS (vpn : BitVec 27) (asid : BitVec 16) (ent' : TLB_Entry)
    (tlbvec : Vector (Option TLB_Entry) 64) (s : ExecSt) (htlb : s.regs .tlb = tlbvec)
    (hsome : tlbvec[tlb_hash 39 vpn]! = some ent')
    (hm : match_TLB_Entry ent' asid (sign_extend (m := 57 - 12) vpn) = false) :
    exec (lookup_TLB 39 asid vpn) s = some (none, s) := by
  unfold lookup_TLB
  exec_run [htlb]
  rw [hsome]
  show exec (if match_TLB_Entry ent' asid (sign_extend (m := 57 - 12) vpn) = true then
    pure (some (tlb_hash 39 vpn, ent')) else pure none) s = _
  rw [hm]; rfl

/-- Rocq `Pt4kWalk.exec_lookup_TLB_hit_ent`. -/
theorem execLookupTLBHitEnt (vpn : BitVec 27) (asid : BitVec 16) (tlbvec : Vector (Option TLB_Entry) 64)
    (ent : TLB_Entry) (s : ExecSt) (htlb : s.regs .tlb = tlbvec) (hsome : tlbvec[tlb_hash 39 vpn]! = some ent)
    (hm : match_TLB_Entry ent asid (sign_extend (m := 57 - 12) vpn) = true) :
    exec (lookup_TLB 39 asid vpn) s = some (some (tlb_hash 39 vpn, ent), s) := by
  unfold lookup_TLB
  exec_run [htlb]
  rw [hsome]
  show exec (if match_TLB_Entry ent asid (sign_extend (m := 57 - 12) vpn) = true then
    pure (some (tlb_hash 39 vpn, ent)) else pure none) s = _
  rw [hm]; rfl

/-- Rocq `PtTreeAdue.pt_fill_ent`: the entry a level-0 `add_to_TLB` installs. -/
def ptFillEnt (asid : BitVec 16) (vpn : BitVec 27) (pp : BitVec 44) (pte : BitVec 64) (ptea : physaddr)
    (g : Bool) : TLB_Entry :=
  { asid := asid
    global := g
    pte := zero_extend (m := 64) pte
    pteAddr := ptea
    levelMask := zero_extend (m := 57 - 12) (ones (n := 0))
    vpn := sign_extend (m := 57 - 12) (vpn &&& ~~~(zero_extend (m := 27) (ones (n := 0))))
    ppn := zero_extend (m := 44) (pp &&& ~~~(zero_extend (m := 44) (ones (n := 0)))) }

/-- Rocq `PtTreeAdue.exec_add_to_TLB_pt`. -/
theorem execAddToTLBPt (asid : BitVec 16) (vpn : BitVec 27) (pp : BitVec 44) (pte : BitVec 64) (ptea : physaddr)
    (g : Bool) (s : ExecSt) :
    exec (add_to_TLB 39 asid vpn pp pte ptea 0 g) s =
      some ((), s.setReg .tlb (vectorUpdate (s.regs .tlb) (tlb_hash 39 vpn) (some (ptFillEnt asid vpn pp pte ptea g)))) := by
  unfold add_to_TLB
  exec_run
  rfl

end Weak
