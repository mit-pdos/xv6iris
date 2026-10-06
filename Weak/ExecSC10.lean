/-
Weak: the S-mode `amoswap.w.aq` over an abstract translation.

Rocq: `iris/WpSmodePtLock.v` (section `ExecAmoGS4walkPt`) @ xxvzwolszwmp.

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
1. Rocq's `a8` (`sign_extend (subrange ea 63 0)`) is `ea = s.gpr rs1 + zeros`; the
   translation premise is at `ea`.
2. The physical-word premises at the post-translation state `s'` are the structure
   `AmoS4` (one field per Rocq hypothesis `Hcp' … Hbytes`).
3. The stored value is `sign_extend (m := 32) (trunc (m := 32) (s'.gpr rs2))` and the
   loaded value written to `rd` is `sign_extend (m := 64) w` (Rocq's `autocast`s).

**Name map (Rocq → Lean).**  `exec_execute_AMOSWAP_4_gpr_S_walk_pt` ↦
`execExecuteAMOSWAP4GprSWalkPt`.  Lean-only: `AmoS4`, `execMemReadAmo4S`,
`execMemWriteValueAmo4S` (Rocq's `exec_mem_read_amo_4_S` /
`exec_mem_write_value_amo_4_S` of `WpAmo.v`, at the `AmoS4` premises).

**Dropped**: none.
-/
import Weak.ExecSC9

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. The S-mode `amoswap.w.aq` over an abstract translation (Rocq `WpSmodePtLock`
section `ExecAmoGS4walkPt`) -/

/-- The S-mode `amoswap.w.aq` premises at the physical word `pa` (state `s'`, after
the translation): PMP entry 0 grants R/W, PMA RAM with AMO swap, the bytes. -/
structure AmoS4 (pa : BitVec 64) (region : PMA_Region) (w : BitVec 32) (s' : ExecSt) : Prop where
  hcp : s'.regs .cur_privilege = .Supervisor
  hmprv : (_get_Mstatus_MPRV (s'.regs .mstatus) == 1#1) = false
  hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s'.regs .pmpcfg_n)[0]!) = .TOR
  hord : zopz0zKzJ_u (zeros (n := 64)) (s'.regs .pmpaddr_n)[0]! = false
  hrange : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s'.regs .pmpaddr_n)[0]!.toNat * 4) pa.toNat
    (to_bits (l := 64) 4).toNat = .PMP_Match
  hR : (_get_Pmpcfg_ent_R (s'.regs .pmpcfg_n)[0]! == 1#1) = true
  hW : (_get_Pmpcfg_ent_W (s'.regs .pmpcfg_n)[0]! == 1#1) = true
  hmatch : matching_pma_region (s'.regs .pma_regions) (.Physaddr pa) 4 = some region
  hpalign : is_aligned_paddr (.Physaddr pa) 4 = true
  hread : (override_PMA region.attributes .PBMT_PMA).readable = true
  hwrite : (override_PMA region.attributes .PBMT_PMA).writable = true
  hamo : pma_allows_atomic_op (override_PMA region.attributes .PBMT_PMA).atomic_support .AMOSWAP 4 = true
  hc : exec (within_clint (.Physaddr pa) 4) s' = some (false, s')
  hsig : exec (within_sig (.Physaddr pa) 4) s' = some (false, s')
  hhr : exec (within_htif_readable (.Physaddr pa) 4) s' = some (false, s')
  hhw : exec (within_htif_writable (.Physaddr pa) 4) s' = some (false, s')
  hdev : devAddr pa = false
  hb : BytesAt s' pa 4 w

theorem execMemReadAmo4S (pa : BitVec 64) (region : PMA_Region) (w : BitVec 32) (s' : ExecSt)
    (H : AmoS4 pa region w s') :
    exec (mem_read (.Atomic (.AMOSWAP, true, false, .Data, .Data)) .PBMT_PMA (.Physaddr pa) 4 true false true) s' =
      some (.Ok w, s') := by
  have hck := execCheckedMemReadRamAmo4S .PBMT_PMA pa region w s' H.hA H.hord H.hrange H.hR H.hW H.hmatch H.hpalign
    H.hread H.hwrite H.hamo H.hc H.hsig H.hhr H.hdev H.hb
  unfold mem_read
  exec_run [H.hcp, execEffectivePrivilegeAmoS _ true false s' H.hmprv,
    execMemReadPriv _ _ _ _ _ _ _ _ w s' (by decide) hck]
  simp only [Nat.reduceMul, BitVec.setWidth_eq]

theorem execMemWriteValueAmo4S (pa : BitVec 64) (region : PMA_Region) (w : BitVec 32) (s' : ExecSt)
    (H : AmoS4 pa region w s') (d : BitVec 32) :
    exec (mem_write_value (.Physaddr pa) 4 d (.Atomic (.AMOSWAP, true, false, .Data, .Data)) .PBMT_PMA false false true)
      s' = some (.Ok true, s'.setMem (bmWrite s'.mem pa 4 d)) :=
  execMemWriteValueRam _ .PBMT_PMA .Supervisor pa 4 d false false true s'
    (by rw [H.hcp]; exact execEffectivePrivilegeAmoS _ true false s' H.hmprv)
    (execCheckedMemWriteRam _ .PBMT_PMA .Supervisor pa 4 d false false true .Write_RISCV_conditional s'
      (by simp [vmemWidth]) (Or.inr ⟨rfl, rfl, rfl, rfl⟩)
      (execPmaCheckRamAmo4 pa .PBMT_PMA region true false s' H.hmatch H.hpalign H.hread H.hwrite H.hamo)
      (execPmpCheckSupervisorGrantAmo pa 4 true false s' H.hA H.hord H.hrange H.hR H.hW)
      (execWithinMmioWritableFalse pa 4 s' H.hc H.hsig H.hhw) H.hdev)

set_option simprocs false in
/-- Rocq `WpSmodePtLock.exec_execute_AMOSWAP_4_gpr_S_walk_pt`. -/
theorem execExecuteAMOSWAP4GprSWalkPt (rs2 rs1 rd : BitVec 5) (region : PMA_Region) (w : BitVec 32)
    (s s' : ExecSt) (pa : BitVec 64) (_hrd : rd.toNat ≠ 0)
    (htea : exec (transform_effective_address (.Virtaddr (s.gpr rs1 + zeros (n := 64)))
      (.Atomic (.AMOSWAP, true, false, .Data, .Data))) s = some (.Virtaddr (s.gpr rs1 + zeros (n := 64)), s))
    (halign : is_aligned_vaddr (.Virtaddr (s.gpr rs1 + zeros (n := 64))) 4 = true)
    (htr : exec (translateAddr (.Virtaddr (s.gpr rs1 + zeros (n := 64))) (.Atomic (.AMOSWAP, true, false, .Data, .Data)))
      s = some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), s'))
    (H : AmoS4 pa region w s') :
    exec (execute (.AMO (.AMOSWAP, true, false, .Regidx rs2, .Regidx rs1, 4, .Regidx rd))) s =
      some (RETIRE_SUCCESS, (s'.setMem (bmWrite s'.mem pa 4
        (sign_extend (m := 32) (trunc (m := 32) (s'.gpr rs2))))).setGpr rd (sign_extend (m := 64) w)) := by
  have hea := execMemWriteEaAmo4 .PBMT_PMA pa region (s'.regs .mstatus) s' H.hA H.hord H.hrange H.hR H.hW H.hmatch
    H.hpalign H.hread H.hwrite H.hamo rfl H.hmprv H.hcp
  have hgta : exec (get_transformed_data_addr (.Regidx rs1) (zeros (n := 64))
      (.Atomic (.AMOSWAP, true, false, .Data, .Data)) 4) s =
      some (.Ext_DataAddr_OK (.Virtaddr (s.gpr rs1 + zeros (n := 64))), s) := by
    unfold get_transformed_data_addr
    exec_run [execExtDataGetAddrGpr, htea]
  show exec (execute_AMO .AMOSWAP true false (.Regidx rs2) (.Regidx rs1) 4 (.Regidx rd)) s = _
  unfold execute_AMO
  rw [execCatchEarlyReturn]
  exec_run [hgta, halign, Functions.not, htr, hea]
  erw [execMemReadAmo4S pa region w s' H]
  exec_run [execRXBitsGpr]
  erw [execMemWriteValueAmo4S pa region w s' H]
  exec_run [execWXBitsGpr]
  have e : BitVec.setWidth (4 * 8) w = w := BitVec.setWidth_eq w
  rw [e]
  rfl

end Weak
