/-
Weak: **the `_entry` boot chain's weak-tier pure layer** (M4 batch 4).

Rocq: `iris/WkEntryEff.v` @ xxvzwolszwmp.

The Rocq header, in substance.  For a REGISTER-ONLY instruction the weak leaf's whole price is
the `execute`'s `execEff` mirror at the EMPTY trace; with it the certificate is
`WeakEff.wcertNowrite` at the fetch-only trace and the `wPEff` obligation is the matching
fetch-arm recipe (`WeakFetchEff.wPEffOfLeafBase`, `WeakFetchRvc.wPEffOfLeafRvc4`,
`WeakFetch2.wPEffOfLeafBase2`/`wPEffOfLeafRvc2`) at `es_x := []`, whose premise (c) the mirror
discharges at every `b` because it is state-generic.  This file holds the pure half: the
image-coverage seam (§0), literal dischargers (§1), the seven register-only `execEff` mirrors
(§2), and the `_entry` chain's per-instruction static facts (§3: image bytes, decodes at the
reference state `dstateM`, `goodb0`/RVC/landing-pad facts).  The Iris half is `WkEntryNew`.

**Deviations from Rocq.**
1. Vocabulary as `Weak/WeakFetchEff.lean` deviation 1 (`register_lookup r rs` ↦ `rs r` over a
   `RegFile`, `eq_vec x 'b"1" = true` ↦ `(x == 1#1) = true`, `tt` ↦ `()`, `set_reg` ↦
   `ExecSt.setReg`, `uint` ↦ `toNat`, `subrange_vec_dec w 15 0` ↦ `Sail.BitVec.extractLsb w 15 0`,
   `pa_add a j` ↦ `a + BitVec.ofNat 64 j`, `nth_byte w j` ↦ `nthByte (n := 4) w j`); `MISA_C` ↦
   `ExecSC2.misaC`.
2. `acc_wf_of_leb` / `addr_is_ram_of_leb`: the Boolean premises are `decide` of the Lean
   propositions; `addr_is_ram a` ↦ `inRam a 1` (`Weak/WeakLeafWin.lean` deviation 2).
3. THE IMAGE.  Rocq's `KernelInstrs.kernel_bytes` (a `Z`-keyed map) ↦ the Lean-only
   `WkEntryEff.kernelBytes A` = the tracked byte `KernelSitesDef.kbyte A` inside
   `[textLo, textHi)`, `none` outside; `kb_word_at` ↦ `WkEntryEff.kbWordAt A = BitVec.ofNat 32
   (kw A)` (`kw` is the same 4-byte little-endian sum, 0 outside the text as Rocq's `kb_byte`
   default).  `wkb_covers` is over `GMapF PAddr (BitVec 8)` with `mword_of_int A` ↦
   `BitVec.ofInt 64 A`.  `KernelSyms._entry` is the Lean `MachCSL.KernelSyms.«_entry»`
   (`0x80000000`, a `Nat`, cast to `Int`).
4. THE REFERENCE STATE.  Rocq `WpDecodeBridge.dstateM` / `D_m` have no Lean `ExecSt` twin
   (MachCSL.DecodeBridge works with the reference MAP `drefM`): `WkEntryEff.dstateM` is
   `ExecLib.zeroRegs` with `cur_privilege := Machine`, `misa := misaC` (so `mseccfg = 0`), the
   empty byte map and `ExecLib.testDevs` (Rocq `dev0_state`); `WkEntryEff.dM r =
   (drefM r).isSome` (the same three registers as Rocq's `D_m`).  `agree_m_regs` is proved
   directly (Rocq routes through `agree_m`).
5. §2 mirrors follow the `Weak/ExecSC.lean` GPR convention: Rocq's
   `if uint rd =? 0 then s else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) v` and, under a
   `uint rd ≠ 0` premise, the plain `set_reg`, are both `s.setGpr rd v` (premise kept);
   `gpr_of_Z`/`zero_reg` reads are `s.gpr`.  `RETIRE_SUCCESS` is the model's constant.  The
   `jump_to` guards are `(BitVec.access t 0 == 0#1) = true` and `bit_to_bool (BitVec.access t 1)
   = false` (`ExecLib` deviation 1).  The CSR-check mirror holds state-generically in Lean too:
   `check_CSR csrCsrr Machine CSRRead` computes to `pure true` (mhartid is accessible, no
   stateen gate), so the statement is Rocq's.
6. DRIFT (the Lean kernel image): the `ld` word is `0x3e813103` (`ld sp, 1000(sp)`; Rocq
   `0x20813103`, imm 520) -- `WkEntryEff.wLd`, and with it `kbE1`/`decE1`/`lpadE1`, are at the
   Lean image's word.  The other seven words and all eight offsets are Rocq's.
7. Proofs: Rocq's `vm_compute` ↦ `decide +kernel` (Boolean / `Option (BitVec 8)` / `BitVec`
   facts) and `kernel_rfl` (the `exec … = some (…, dstateM)` decodes: `ExecSt` has no
   `DecidableEq`).  The compressed expansions' `goodb0` facts are `rfl` (Lean's
   `execute (.C_* …)` is `pure (.ExecuteAs …)`).
8. Tactics (file-qualified names; Rocq `WkEntryNew` defines its own): `ram_lit` ↦
   `wk_entry_ram_lit`, `ram_win` ↦ `wk_entry_ram_win`, `kb_win` ↦ `wk_entry_kb_win` (Rocq's helper
   `kb_byte` is its per-byte `decide +kernel`, not a separate tactic).

**Rocq → Lean name map.**  §0: `wkb_covers` `wkbCovers`, `wkb_window` `wkbWindow`.  §1:
`acc_wf_of_leb` `accWfOfLeb`, `addr_is_ram_of_leb` `addrIsRamOfLeb`, `D_m_mi` `dMMi`,
`agree_m_regs` `agreeMRegs`, `misaC/A/M_of_val` `misaC/A/MOfVal`.  §2: `exec_eff_get_arch_pc`
`execEffGetArchPc`, `exec_eff_set_next_pc` `WkEntryEff.execEffSetNextPc` (duplicated name),
`exec_eff_rX_bits_x0` `WkEntryEff.execEffRXBitsX0` (duplicated name), `exec_eff_jump_to`
`execEffJumpTo`, `exec_eff_execute_UTYPE_AUIPC_gpr` `execEffExecuteUTYPEAUIPCGpr`,
`exec_eff_execute_UTYPE_LUI_gpr` `execEffExecuteUTYPELUIGpr`, `exec_eff_execute_ITYPE_ADDI_gpr`
`execEffExecuteITYPEADDIGpr`, `exec_eff_execute_RTYPE_ADD_gpr` `execEffExecuteRTYPEADDGpr`,
`exec_eff_execute_MUL_gpr` `execEffExecuteMULGpr`, `exec_eff_execute_JAL_gpr`
`execEffExecuteJALGpr`, `exec_eff_check_CSR_result_csrr` `WkEntryEff.execEffCheckCSRResultCsrr`,
`exec_eff_read_CSR_csrr` `WkEntryEff.execEffReadCSRCsrr`, `exec_eff_csr_id_read_callback_csrr`
`WkEntryEff.execEffCsrIdReadCallbackCsrr` (all three duplicated names),
`exec_eff_execute_CSRReg_gpr` `execEffExecuteCSRRegGpr`.  §3: `w_e2/4/6` `wE2/4/6`,
`kb_e0..7` `kbE0..7`, `sub_e2/4/6` `subE2/4/6`, `rvc_e2/4/6` `rvcE2/4/6`,
`nrvc_e0/1/3/5/7` `nrvcE0/1/3/5/7`, `dec_e0..7` `decE0..7`, `good_e0..7` `goodE0..7`,
`D_none` `dNone`, `good_exp_e2/4/6` `goodExpE2/4/6`, `lpad_e0..7` `lpadE0..7`,
`lpad_i0_e2/4/6` `lpadI0E2/4/6`; tactics per deviation 8.
Lean-only stand-ins for Rocq definitions of other (SC) files, file-qualified: `WkEntryEff.`
`kernelBytes` (`KernelInstrs.kernel_bytes`), `kbWordAt` (`KernelText.kb_word_at`), `dstateM`,
`dM` (`WpDecodeBridge`), `luival` (`WpMmodeLeafBase`), `gprMulVal` (`WpMmodeMul.gpr_mul_val`),
`wAuipc`/`immAuipc`/`iAuipc`/`wLd`/`immLd`/`iLd` (`WpDecode`), `rdClui`, `hAddi`/`immCaddi`/
`rsdCaddi`, `hAdd`/`rsdCadd`/`rs2Cadd`, `wMul`/`iMulRs2`/`iMulRs1`/`iMulRd`, `wJal`/`iJal`/
`immJal` (`CodeEntryAux`).  Reused: `ExecLib.hLui`/`immClui`/`wCsrr`/`csrCsrr`/`iRdCsrr`/
`mulopMul`, `ExecSC.auipcOff`/`gprAddiVal`/`gprRdVal`, `ExecSC7.regidxNeZreg`.

**Dropped:** none (Rocq 80 declarations incl. 4 Ltacs; Lean 79 + 26 Lean-only definitions:
`kb_byte` is folded into `wk_entry_kb_win`, deviation 8).
-/
import Weak.WeakFetch2
import Weak.WeakLeafEffCommon
import Weak.WeakEffSkel
import Weak.ExecSC2
import Weak.ExecSC7
import Weak.ExecLib
import Weak.KernelSitesDef

namespace Weak

open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 0. The weak kernel-image coverage predicate -/

/-- Rocq `KernelInstrs.kernel_bytes !! A` (Lean-only stand-in, deviation 3): the tracked
image byte at `A`, `none` outside the text. -/
def WkEntryEff.kernelBytes (A : Int) : Option (BitVec 8) :=
  if textLo ≤ A ∧ A < textHi then some (BitVec.ofNat 8 (kbyte A)) else none

section cover
open Iris.Std

/-- Rocq `wkb_covers` (deviation 3). -/
def wkbCovers (kbs : GMapF PAddr (BitVec 8)) : Prop :=
  ∀ (A : Int) (b : BitVec 8), WkEntryEff.kernelBytes A = some b →
    get? kbs (BitVec.ofInt 64 A) = some b

/-- Rocq `wkb_window`: a 4-byte window of the image, transported to the `PAddr` map. -/
theorem wkbWindow (kbs : GMapF PAddr (BitVec 8)) (A : Int) (w : BitVec 32) :
    wkbCovers kbs →
    (∀ j : Nat, j < 4 → WkEntryEff.kernelBytes (A + (j : Int)) = some (nthByte (n := 4) w j)) →
    ∀ j : Nat, j < 4 →
      get? kbs (BitVec.ofInt 64 A + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j) := by
  intro hcov hb j hj
  have e : BitVec.ofInt 64 A + BitVec.ofNat 64 j = BitVec.ofInt 64 (A + (j : Int)) := by
    rw [BitVec.ofInt_add, BitVec.ofInt_natCast]
  rw [e]
  exact hcov _ _ (hb j hj)

end cover

/-! ## 1. Literal dischargers -/

/-- Rocq `acc_wf_of_leb` (deviation 2). -/
theorem accWfOfLeb (a : PAddr) (n : Nat) :
    decide (paZ a + (n : Int) ≤ 18446744073709551616) = true → accWf a n := by
  intro h; unfold accWf; exact of_decide_eq_true h

/-- Rocq `addr_is_ram_of_leb` (deviation 2). -/
theorem addrIsRamOfLeb (a : PAddr) :
    (decide (ramBase ≤ a.toNat) && decide (a.toNat + 1 ≤ ramEnd)) = true → inRam a 1 := by
  intro h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-- Rocq `ram_lit` (Lean-only name `wk_entry_ram_lit`: Rocq `WkEntryNew` has its own). -/
macro "wk_entry_ram_lit" : tactic => `(tactic| (apply addrIsRamOfLeb; decide +kernel))

/-- Rocq `ram_win`: RAM facts for a 4-byte window at a concrete address. -/
macro "wk_entry_ram_win" : tactic =>
  `(tactic| (intro j hj; rcases j with _ | _ | _ | _ | j <;>
    first | (exfalso; omega) | wk_entry_ram_lit))

example : ∀ j : Nat, j < 4 → inRam (0x80000000#64 + BitVec.ofNat 64 j) 1 := by wk_entry_ram_win

/-- Rocq `WpDecodeBridge.dstateM` (Lean-only stand-in, deviation 4): the machine-mode
reference state -- `cur_privilege = Machine`, `misa = MISA_C`, every other register at its
default (so `mseccfg = 0`), the empty byte map, a closed device fabric. -/
def WkEntryEff.dstateM : ExecSt :=
  ⟨(zeroRegs.set .cur_privilege .Machine).set .misa misaC, fun _ => none, testDevs⟩

/-- Rocq `WpDecodeBridge.D_m` (deviation 4): the machine-mode decode read set, the domain of
`MachCSL.drefM`. -/
def WkEntryEff.dM (r : Register) : Bool := (drefM r).isSome

/-- Rocq `D_m_mi`. -/
theorem dMMi : WkEntryEff.dM .minstret_increment = false := rfl

/-- Rocq `agree_m_regs`. -/
theorem agreeMRegs (rs : RegFile) :
    rs .cur_privilege = .Machine → rs .mseccfg = 0#64 → rs .misa = misaC →
    ∀ r, WkEntryEff.dM r = true → rs r = WkEntryEff.dstateM.regs r := by
  intro h1 h2 h3 r hr
  unfold WkEntryEff.dM drefM at hr
  split at hr
  · rw [h1]; rfl
  · rw [h3]; rfl
  · rw [h2]; rfl
  · simp at hr

/-- Rocq `misaC_of_val`. -/
theorem misaCOfVal (rs : RegFile) (h : rs .misa = misaC) :
    (_get_Misa_C (rs .misa) == 1#1) = true := by
  rw [h]; decide

/-- Rocq `misaA_of_val`. -/
theorem misaAOfVal (rs : RegFile) (h : rs .misa = misaC) :
    (_get_Misa_A (rs .misa) == 1#1) = true := by
  rw [h]; decide

/-- Rocq `misaM_of_val`. -/
theorem misaMOfVal (rs : RegFile) (h : rs .misa = misaC) :
    (_get_Misa_M (rs .misa) == 1#1) = true := by
  rw [h]; decide

/-! ## 2a. The tiny self-run helpers -/

/-- Rocq `exec_eff_get_arch_pc`. -/
theorem execEffGetArchPc (s : ExecSt) :
    execEff (get_arch_pc ()) s = some (s.regs .PC, s, []) := rfl

/-- Rocq `exec_eff_set_next_pc` (duplicated name): the branch announcement is silent. -/
theorem WkEntryEff.execEffSetNextPc (target : BitVec 64) (s : ExecSt) :
    execEff (set_next_pc target) s = some ((), s.setReg .nextPC target, []) := rfl

/-- Rocq `exec_eff_rX_bits_x0` (duplicated name). -/
theorem WkEntryEff.execEffRXBitsX0 (i : BitVec 5) (s : ExecSt) (h : i.toNat = 0) :
    execEff (rX_bits (.Regidx i)) s = some (zero_reg, s, []) := by
  have hi : i = 0#5 := BitVec.eq_of_toNat_eq h
  subst hi
  rfl

/-! ## 2b. `jump_to` -/

/-- Rocq `exec_eff_jump_to`: the `execEff` mirror of `ExecLib.execJumpTo`. -/
theorem execEffJumpTo (target : BitVec 64) (s : ExecSt)
    (halign : (BitVec.access target 0 == 0#1) = true)
    (hbit1 : bit_to_bool (BitVec.access target 1) = false) :
    execEff (jump_to target) s = some (RETIRE_SUCCESS, s.setReg .nextPC target, []) := by
  unfold jump_to
  rw [execEffCatchEarlyReturn]
  simp only [ext_control_check_pc, execREffBindEq, execREffReturnR, execREffLiftR, assert,
    PreSail.assert, halign, ↓reduceIte, execEffReturnm, hbit1, Bool.false_eq_true,
    WkEntryEff.execEffSetNextPc, List.append_nil]

/-! ## 2c. AUIPC / LUI -/

/-- Rocq `WpMmodeLeafBase.luival` (Lean-only stand-in; `WeakEvExecEff.luival` is the same
term, not imported here). -/
def WkEntryEff.luival (imm : BitVec 20) : BitVec 64 := sign_extend (m := 64) (imm +++ 0x000#12)

/-- Rocq `exec_eff_execute_UTYPE_AUIPC_gpr` (deviation 5). -/
theorem execEffExecuteUTYPEAUIPCGpr (rd : BitVec 5) (imm : BitVec 20) (s : ExecSt) :
    execEff (execute (.UTYPE (imm, .Regidx rd, .AUIPC))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (s.regs .PC + auipcOff imm), []) := by
  show execEff (execute_UTYPE imm (.Regidx rd) .AUIPC) s = _
  unfold execute_UTYPE auipcOff get_arch_pc
  exec_eff_steps [execEffWXBitsGpr]

/-- Rocq `exec_eff_execute_UTYPE_LUI_gpr` (deviation 5). -/
theorem execEffExecuteUTYPELUIGpr (rd : BitVec 5) (imm : BitVec 20) (s : ExecSt) :
    execEff (execute (.UTYPE (imm, .Regidx rd, .LUI))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (WkEntryEff.luival imm), []) := by
  show execEff (execute_UTYPE imm (.Regidx rd) .LUI) s = _
  unfold execute_UTYPE WkEntryEff.luival
  exec_eff_steps [execEffWXBitsGpr]

/-! ## 2d. ADDI -/

/-- Rocq `exec_eff_execute_ITYPE_ADDI_gpr` (deviation 5). -/
theorem execEffExecuteITYPEADDIGpr (rs1 rd : BitVec 5) (imm : BitVec 12) (s : ExecSt) :
    execEff (execute (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (gprAddiVal rs1 imm s), []) := by
  show execEff (execute_ITYPE imm (.Regidx rs1) (.Regidx rd) .ADDI) s = _
  unfold execute_ITYPE gprAddiVal
  exec_eff_steps [execEffRXBitsGpr, execEffWXBitsGpr]

/-! ## 2e. RTYPE ADD -/

/-- Rocq `exec_eff_execute_RTYPE_ADD_gpr` (deviation 5). -/
theorem execEffExecuteRTYPEADDGpr (rs2 rs1 rd : BitVec 5) (s : ExecSt) :
    execEff (execute (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .ADD))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (gprRdVal rs2 rs1 s), []) := by
  show execEff (execute_RTYPE (.Regidx rs2) (.Regidx rs1) (.Regidx rd) .ADD) s = _
  unfold execute_RTYPE gprRdVal
  exec_eff_steps [execEffRXBitsGpr, execEffWXBitsGpr]

/-! ## 2f. MUL -/

/-- Rocq `WpMmodeMul.gpr_mul_val` (Lean-only stand-in). -/
def WkEntryEff.gprMulVal (rs2 rs1 : BitVec 5) (s : ExecSt) : BitVec 64 :=
  mult_to_bits_half (l := 64) mulopMul.signed_rs1 mulopMul.signed_rs2 (s.gpr rs1) (s.gpr rs2)
    mulopMul.result_part

/-- Rocq `exec_eff_execute_MUL_gpr` (deviation 5). -/
theorem execEffExecuteMULGpr (rs2 rs1 rd : BitVec 5) (s : ExecSt) (_hrd : rd.toNat ≠ 0) :
    execEff (execute (.MUL (.Regidx rs2, .Regidx rs1, .Regidx rd, mulopMul))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (WkEntryEff.gprMulVal rs2 rs1 s), []) := by
  show execEff (execute_MUL (.Regidx rs2) (.Regidx rs1) (.Regidx rd) mulopMul) s = _
  unfold execute_MUL WkEntryEff.gprMulVal
  exec_eff_steps [execEffRXBitsGpr, execEffWXBitsGpr]
  rfl

/-! ## 2g. JAL -/

/-- Rocq `exec_eff_execute_JAL_gpr` (deviation 5). -/
theorem execEffExecuteJALGpr (imm : BitVec 21) (rd : BitVec 5) (s : ExecSt) (_hrd : rd.toNat ≠ 0)
    (halign : (BitVec.access (s.regs .PC + sign_extend (m := 64) imm) 0 == 0#1) = true)
    (hbit1 : bit_to_bool (BitVec.access (s.regs .PC + sign_extend (m := 64) imm) 1) = false) :
    execEff (execute (.JAL (imm, .Regidx rd))) s =
      some (RETIRE_SUCCESS,
        (s.setReg .nextPC (s.regs .PC + sign_extend (m := 64) imm)).setGpr rd (s.regs .nextPC),
        []) := by
  show execEff (execute_JAL imm (.Regidx rd)) s = _
  unfold execute_JAL get_next_pc
  exec_eff_steps [execEffJumpTo _ s halign hbit1, RETIRE_SUCCESS, execEffWXBitsGpr]

/-! ## 2h. CSRRS a1, mhartid -/

/-- Rocq `exec_eff_check_CSR_result_csrr` (duplicated name). -/
theorem WkEntryEff.execEffCheckCSRResultCsrr (s : ExecSt) :
    execEff (check_CSR_result csrCsrr .Machine .CSRRead) s = some (.CSR_Check_OK (), s, []) := by
  have h : check_CSR csrCsrr .Machine .CSRRead = pure true := by csr_dispatch_eq
  unfold check_CSR_result
  rw [h]
  rfl

/-- Rocq `exec_eff_read_CSR_csrr` (duplicated name). -/
theorem WkEntryEff.execEffReadCSRCsrr (s : ExecSt) :
    execEff (read_CSR csrCsrr) s = some (s.regs .mhartid, s, []) := by
  have e : read_CSR csrCsrr = readReg .mhartid := by csr_dispatch_eq
  rw [e]; rfl

/-- Rocq `exec_eff_csr_id_read_callback_csrr` (duplicated name). -/
theorem WkEntryEff.execEffCsrIdReadCallbackCsrr (s : ExecSt) (d : BitVec 64) :
    execEff (csr_id_read_callback csrCsrr d) s = some ((), s, []) := by
  have e : csr_id_read_callback csrCsrr d = pure () := by csr_dispatch_eq
  rw [e]; rfl

/-- Rocq `exec_eff_execute_CSRReg_gpr` (deviation 5). -/
theorem execEffExecuteCSRRegGpr (rd : BitVec 5) (s : ExecSt) (hrd : rd.toNat ≠ 0)
    (hpriv : s.regs .cur_privilege = .Machine) :
    execEff (execute (.CSRReg (csrCsrr, zreg, .Regidx rd, .CSRRS))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (s.regs .mhartid), []) := by
  have hz : (regidx.Regidx rd == zreg) = false := regidxNeZreg rd hrd
  have hx0 : execEff (rX_bits zreg) s = some (zero_reg, s, []) :=
    WkEntryEff.execEffRXBitsX0 _ s rfl
  have hzz : (zreg == zreg) = true := rfl
  show execEff (execute_CSRReg csrCsrr zreg (.Regidx rd) .CSRRS) s = _
  unfold execute_CSRReg doCSR
  exec_eff_steps [hz, hx0, hpriv, csr_access_type, WkEntryEff.execEffCheckCSRResultCsrr,
    ext_check_CSR, WkEntryEff.execEffReadCSRCsrr, hzz, WkEntryEff.execEffCsrIdReadCallbackCsrr,
    execEffWXBitsGpr]

/-! ## 3. THE `_entry` CHAIN'S STATIC FACTS

The words and operand fields of the eight `_entry` instructions (Rocq `WpDecode`,
`CodeEntryAux`, `ExecCommon`, `KernelText`; Lean-only stand-ins, file-qualified). -/

/-- Rocq `KernelText.kb_word_at`: the 4-byte little-endian fetch window at `A`. -/
def WkEntryEff.kbWordAt (A : Int) : BitVec 32 := BitVec.ofNat 32 (kw A)

/-- Rocq `w_auipc`: `auipc sp, 0xa`. -/
def WkEntryEff.wAuipc : BitVec 32 := 0x0000a117#32
/-- Rocq `imm_auipc`. -/
def WkEntryEff.immAuipc : BitVec 20 := WkEntryEff.wAuipc.extractLsb' 12 20
/-- Rocq `i_auipc`. -/
def WkEntryEff.iAuipc : BitVec 5 := WkEntryEff.wAuipc.extractLsb' 7 5

/-- Rocq `w_ld`: `ld sp, 1000(sp)` (drift: Rocq `0x20813103`, imm 520; deviation 6). -/
def WkEntryEff.wLd : BitVec 32 := 0x3e813103#32
/-- Rocq `imm_ld`. -/
def WkEntryEff.immLd : BitVec 12 := WkEntryEff.wLd.extractLsb' 20 12
/-- Rocq `i_ld`. -/
def WkEntryEff.iLd : BitVec 5 := WkEntryEff.wLd.extractLsb' 7 5

/-- Rocq `rd_clui` (of `ExecLib.hLui`, `c.lui a0, 1`). -/
def WkEntryEff.rdClui : regidx := .Regidx (hLui.extractLsb' 7 5)

/-- Rocq `h_addi`: `c.addi a1, 1`. -/
def WkEntryEff.hAddi : BitVec 16 := 0x0585#16
/-- Rocq `imm_caddi`. -/
def WkEntryEff.immCaddi : BitVec 6 :=
  WkEntryEff.hAddi.extractLsb' 12 1 ++ WkEntryEff.hAddi.extractLsb' 2 5
/-- Rocq `rsd_caddi`. -/
def WkEntryEff.rsdCaddi : regidx := .Regidx (WkEntryEff.hAddi.extractLsb' 7 5)

/-- Rocq `h_add`: `c.add sp, a0`. -/
def WkEntryEff.hAdd : BitVec 16 := 0x912a#16
/-- Rocq `rsd_cadd`. -/
def WkEntryEff.rsdCadd : regidx := .Regidx (WkEntryEff.hAdd.extractLsb' 7 5)
/-- Rocq `rs2_cadd`. -/
def WkEntryEff.rs2Cadd : regidx := .Regidx (WkEntryEff.hAdd.extractLsb' 2 5)

/-- Rocq `w_mul`: `mul a0, a0, a1`. -/
def WkEntryEff.wMul : BitVec 32 := 0x02b50533#32
/-- Rocq `i_mul_rs2`. -/
def WkEntryEff.iMulRs2 : BitVec 5 := WkEntryEff.wMul.extractLsb' 20 5
/-- Rocq `i_mul_rs1`. -/
def WkEntryEff.iMulRs1 : BitVec 5 := WkEntryEff.wMul.extractLsb' 15 5
/-- Rocq `i_mul_rd`. -/
def WkEntryEff.iMulRd : BitVec 5 := WkEntryEff.wMul.extractLsb' 7 5

/-- Rocq `w_jal`: `jal ra, start`. -/
def WkEntryEff.wJal : BitVec 32 := 0x042000ef#32
/-- Rocq `i_jal`. -/
def WkEntryEff.iJal : BitVec 5 := WkEntryEff.wJal.extractLsb' 7 5
/-- Rocq `imm_jal`. -/
def WkEntryEff.immJal : BitVec 21 :=
  WkEntryEff.wJal.extractLsb' 31 1 ++ WkEntryEff.wJal.extractLsb' 12 8 ++
    WkEntryEff.wJal.extractLsb' 20 1 ++ WkEntryEff.wJal.extractLsb' 21 10 ++ 0#1

open WkEntryEff in
/-- Rocq `w_e2`: the containing word of `c.lui` (its 32-bit window). -/
def wE2 : BitVec 32 := kbWordAt ((KernelSyms.«_entry» : Int) + 0x8)
open WkEntryEff in
/-- Rocq `w_e4`. -/
def wE4 : BitVec 32 := kbWordAt ((KernelSyms.«_entry» : Int) + 0xe)
open WkEntryEff in
/-- Rocq `w_e6`. -/
def wE6 : BitVec 32 := kbWordAt ((KernelSyms.«_entry» : Int) + 0x14)

/-! ### 3a. The image bytes, per instruction word -/

/-- Rocq `kb_win` (Lean-only name; Rocq `kb_byte` is its per-byte `decide +kernel`). -/
macro "wk_entry_kb_win" : tactic =>
  `(tactic| (intro j hj; rcases j with _ | _ | _ | _ | j <;>
    first | (exfalso; omega) | decide +kernel))

open WkEntryEff in
/-- Rocq `kb_e0`. -/
theorem kbE0 : ∀ j : Nat, j < 4 →
    kernelBytes ((KernelSyms.«_entry» : Int) + 0x0 + (j : Int)) = some (nthByte (n := 4) wAuipc j) := by
  wk_entry_kb_win

open WkEntryEff in
/-- Rocq `kb_e1`. -/
theorem kbE1 : ∀ j : Nat, j < 4 →
    kernelBytes ((KernelSyms.«_entry» : Int) + 0x4 + (j : Int)) = some (nthByte (n := 4) wLd j) := by
  wk_entry_kb_win

open WkEntryEff in
/-- Rocq `kb_e2`. -/
theorem kbE2 : ∀ j : Nat, j < 4 →
    kernelBytes ((KernelSyms.«_entry» : Int) + 0x8 + (j : Int)) = some (nthByte (n := 4) wE2 j) := by
  wk_entry_kb_win

open WkEntryEff in
/-- Rocq `kb_e3`. -/
theorem kbE3 : ∀ j : Nat, j < 4 →
    kernelBytes ((KernelSyms.«_entry» : Int) + 0xa + (j : Int)) = some (nthByte (n := 4) wCsrr j) := by
  wk_entry_kb_win

open WkEntryEff in
/-- Rocq `kb_e4`. -/
theorem kbE4 : ∀ j : Nat, j < 4 →
    kernelBytes ((KernelSyms.«_entry» : Int) + 0xe + (j : Int)) = some (nthByte (n := 4) wE4 j) := by
  wk_entry_kb_win

open WkEntryEff in
/-- Rocq `kb_e5`. -/
theorem kbE5 : ∀ j : Nat, j < 4 →
    kernelBytes ((KernelSyms.«_entry» : Int) + 0x10 + (j : Int)) = some (nthByte (n := 4) wMul j) := by
  wk_entry_kb_win

open WkEntryEff in
/-- Rocq `kb_e6`. -/
theorem kbE6 : ∀ j : Nat, j < 4 →
    kernelBytes ((KernelSyms.«_entry» : Int) + 0x14 + (j : Int)) = some (nthByte (n := 4) wE6 j) := by
  wk_entry_kb_win

open WkEntryEff in
/-- Rocq `kb_e7`. -/
theorem kbE7 : ∀ j : Nat, j < 4 →
    kernelBytes ((KernelSyms.«_entry» : Int) + 0x16 + (j : Int)) = some (nthByte (n := 4) wJal j) := by
  wk_entry_kb_win

/-! ### 3b. The RVC halfword extraction / classification facts -/

/-- Rocq `sub_e2`. -/
theorem subE2 : Sail.BitVec.extractLsb wE2 15 0 = hLui := by decide +kernel
/-- Rocq `rvc_e2`. -/
theorem rvcE2 : isRVC hLui = true := by decide +kernel
/-- Rocq `sub_e4`. -/
theorem subE4 : Sail.BitVec.extractLsb wE4 15 0 = WkEntryEff.hAddi := by decide +kernel
/-- Rocq `rvc_e4`. -/
theorem rvcE4 : isRVC WkEntryEff.hAddi = true := by decide +kernel
/-- Rocq `sub_e6`. -/
theorem subE6 : Sail.BitVec.extractLsb wE6 15 0 = WkEntryEff.hAdd := by decide +kernel
/-- Rocq `rvc_e6`. -/
theorem rvcE6 : isRVC WkEntryEff.hAdd = true := by decide +kernel

/-- Rocq `nrvc_e0`. -/
theorem nrvcE0 : isRVC (Sail.BitVec.extractLsb WkEntryEff.wAuipc 15 0) = false := by decide +kernel
/-- Rocq `nrvc_e1`. -/
theorem nrvcE1 : isRVC (Sail.BitVec.extractLsb WkEntryEff.wLd 15 0) = false := by decide +kernel
/-- Rocq `nrvc_e3`. -/
theorem nrvcE3 : isRVC (Sail.BitVec.extractLsb wCsrr 15 0) = false := by decide +kernel
/-- Rocq `nrvc_e5`. -/
theorem nrvcE5 : isRVC (Sail.BitVec.extractLsb WkEntryEff.wMul 15 0) = false := by decide +kernel
/-- Rocq `nrvc_e7`. -/
theorem nrvcE7 : isRVC (Sail.BitVec.extractLsb WkEntryEff.wJal 15 0) = false := by decide +kernel

/-! ### 3c. The decodes and read-set witnesses at `dstateM` -/

section dec
open WkEntryEff

/-- Rocq `dec_e0`. -/
theorem decE0 : exec (ext_decode wAuipc) dstateM =
    some (.UTYPE (immAuipc, .Regidx iAuipc, .AUIPC), dstateM) := by kernel_rfl
/-- Rocq `good_e0`. -/
theorem goodE0 : goodb0 dM (ext_decode wAuipc) dstateM = true := by decide +kernel

/-- Rocq `dec_e1`. -/
theorem decE1 : exec (ext_decode wLd) dstateM =
    some (.LOAD (immLd, .Regidx iLd, .Regidx iLd, false, 8), dstateM) := by kernel_rfl
/-- Rocq `good_e1`. -/
theorem goodE1 : goodb0 dM (ext_decode wLd) dstateM = true := by decide +kernel

/-- Rocq `dec_e2`. -/
theorem decE2 : exec (ext_decode_compressed hLui) dstateM =
    some (.C_LUI (immClui, rdClui), dstateM) := by kernel_rfl
/-- Rocq `good_e2`. -/
theorem goodE2 : goodb0 dM (ext_decode_compressed hLui) dstateM = true := by decide +kernel

/-- Rocq `dec_e3`. -/
theorem decE3 : exec (ext_decode wCsrr) dstateM =
    some (.CSRReg (csrCsrr, zreg, .Regidx iRdCsrr, .CSRRS), dstateM) := by kernel_rfl
/-- Rocq `good_e3`. -/
theorem goodE3 : goodb0 dM (ext_decode wCsrr) dstateM = true := by decide +kernel

/-- Rocq `dec_e4`. -/
theorem decE4 : exec (ext_decode_compressed hAddi) dstateM =
    some (.C_ADDI (immCaddi, rsdCaddi), dstateM) := by kernel_rfl
/-- Rocq `good_e4`. -/
theorem goodE4 : goodb0 dM (ext_decode_compressed hAddi) dstateM = true := by decide +kernel

/-- Rocq `dec_e5`. -/
theorem decE5 : exec (ext_decode wMul) dstateM =
    some (.MUL (.Regidx iMulRs2, .Regidx iMulRs1, .Regidx iMulRd, mulopMul), dstateM) := by
  kernel_rfl
/-- Rocq `good_e5`. -/
theorem goodE5 : goodb0 dM (ext_decode wMul) dstateM = true := by decide +kernel

/-- Rocq `dec_e6`. -/
theorem decE6 : exec (ext_decode_compressed hAdd) dstateM =
    some (.C_ADD (rsdCadd, rs2Cadd), dstateM) := by kernel_rfl
/-- Rocq `good_e6`. -/
theorem goodE6 : goodb0 dM (ext_decode_compressed hAdd) dstateM = true := by decide +kernel

/-- Rocq `dec_e7`. -/
theorem decE7 : exec (ext_decode wJal) dstateM =
    some (.JAL (immJal, .Regidx iJal), dstateM) := by kernel_rfl
/-- Rocq `good_e7`. -/
theorem goodE7 : goodb0 dM (ext_decode wJal) dstateM = true := by decide +kernel

/-! ### 3d. The RVC expansions' `goodb0` witnesses (no register is read) -/

/-- Rocq `D_none`. -/
def dNone (_ : Register) : Bool := false

/-- Rocq `good_exp_e2`. -/
theorem goodExpE2 : ∀ s : ExecSt, goodb0 dNone (execute (.C_LUI (immClui, rdClui))) s = true :=
  fun _ => rfl
/-- Rocq `good_exp_e4`. -/
theorem goodExpE4 : ∀ s : ExecSt, goodb0 dNone (execute (.C_ADDI (immCaddi, rsdCaddi))) s = true :=
  fun _ => rfl
/-- Rocq `good_exp_e6`. -/
theorem goodExpE6 : ∀ s : ExecSt, goodb0 dNone (execute (.C_ADD (rsdCadd, rs2Cadd))) s = true :=
  fun _ => rfl

/-! ### 3e. Landing-pad facts -/

/-- Rocq `lpad_e0`. -/
theorem lpadE0 : is_lpad_instruction (.UTYPE (immAuipc, .Regidx iAuipc, .AUIPC)) = false := by
  decide +kernel
/-- Rocq `lpad_e1`. -/
theorem lpadE1 : is_lpad_instruction (.LOAD (immLd, .Regidx iLd, .Regidx iLd, false, 8)) = false := by
  decide +kernel
/-- Rocq `lpad_e2`. -/
theorem lpadE2 : is_lpad_instruction (.UTYPE (sign_extend (m := 20) immClui, rdClui, .LUI)) = false := by
  decide +kernel
/-- Rocq `lpad_e3`. -/
theorem lpadE3 : is_lpad_instruction (.CSRReg (csrCsrr, zreg, .Regidx iRdCsrr, .CSRRS)) = false := by
  decide +kernel
/-- Rocq `lpad_e4`. -/
theorem lpadE4 :
    is_lpad_instruction (.ITYPE (sign_extend (m := 12) immCaddi, rsdCaddi, rsdCaddi, .ADDI)) = false := by
  decide +kernel
/-- Rocq `lpad_e5`. -/
theorem lpadE5 :
    is_lpad_instruction (.MUL (.Regidx iMulRs2, .Regidx iMulRs1, .Regidx iMulRd, mulopMul)) = false := by
  decide +kernel
/-- Rocq `lpad_e6`. -/
theorem lpadE6 : is_lpad_instruction (.RTYPE (rs2Cadd, rsdCadd, rsdCadd, .ADD)) = false := by
  decide +kernel
/-- Rocq `lpad_e7`. -/
theorem lpadE7 : is_lpad_instruction (.JAL (immJal, .Regidx iJal)) = false := by decide +kernel

/-! ### 3f. The compressed instructions' own lpad facts -/

/-- Rocq `lpad_i0_e2`. -/
theorem lpadI0E2 : is_lpad_instruction (.C_LUI (immClui, rdClui)) = false := by decide +kernel
/-- Rocq `lpad_i0_e4`. -/
theorem lpadI0E4 : is_lpad_instruction (.C_ADDI (immCaddi, rsdCaddi)) = false := by decide +kernel
/-- Rocq `lpad_i0_e6`. -/
theorem lpadI0E6 : is_lpad_instruction (.C_ADD (rsdCadd, rs2Cadd)) = false := by decide +kernel

end dec

end Weak
