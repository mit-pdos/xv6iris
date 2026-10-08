/-
Weak: **the two CSR instructions of xv6's real `push_off` / `pop_off` at the S-mode data regime:
read footprints (`rfF`) and SC `exec` facts.**

  `q0a` = `csrrci a5,sstatus,2`  (push_off + 0x0a, intr_off)
  `p0c` = `csrr   a5,sstatus`    (pop_off + 0x0c, intr_get)

§1 `rfF` of both instructions: the CSR-address dispatches (`read_CSR` / `write_CSR` /
   `is_CSR_accessible` / …) at `sstatus` are discharged by their `rfl`/kernel dispatch
   equations, then `rff_auto`.
§2 the SC `exec` facts at every regime state: csrrci with SIE = 0 is IDEMPOTENT on mstatus
   (`AxSpinPOc.legalizeSieClearIdem` from `ctrlOkS`'s mstatus facts), so both instructions only
   write a5 := `sstatusRead mstatus` — a value that is NOT a function of the GPRs.

Rocq: `iris/AxSpinPOc.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. HEAD-PEELING (Rocq §1's `rfF_ifF*` + Ltacs `vmr`/`rpeel`): lean-sail's CSR dispatches are
   `match`es on the 12-bit address, not `if eq_vec` chains; at `css` they reduce by
   `csr_dispatch_eq` (`rfl` / kernel `rfl`) — `read_CSR_sstatus` / `write_CSR_sstatus`
   (MachCSL.WpCsrS) and local `have`s for `is_CSR_accessible` / `stateen_allows_CSR_access` /
   `is_CSR_exception_virtual`.  The generic `rfF_ifF`/`rfF_ifT`/`rfF_ifF4`/`rfF_ifF16` are still
   ported (statements over `SailM`; Rocq `Defs.monad E X`).  The Ltacs `vmr`, `rpeel`, `nzc` are
   not ported (decided facts are `by decide` / `rfl`).  `write_CSR`'s `legalize_mstatus` (≈13
   nested `currentlyEnabled` binds) goes through Lean-only callee lemmas and a local walker
   (`ax_spin_poc_lm`, raised `maxHeartbeats`); a plain `rff_auto` there times out.
2. `rfF_and_boolM` DROPPED: lean-sail's `check_CSR` is a nested `if (← …)` (no `and_boolM`
   combinator; `AxSpineOk` precedent); no other Rocq file uses it.
3. `cb_read_ss` / `cb_write_ss`: `= pure ()` (Rocq `returnM tt`), by kernel `rfl`.
4. `css_eq`: Lean has no `csr_sstatus` constant; stated as `css = 0x100#12` (the address
   ExecSC7's sstatus lemmas use).
5. `exec_q0a` / `exec_p0c`: Rocq `set_reg s (R_bitvector_64 (gpr_of_Z 15)) (regval_into_reg …)`
   ↦ `s.setGpr 15#5 …`, `sstatus_read` ↦ `sstatusRead`, `register_lookup mstatus s.(sregs)` ↦
   `s.regs .mstatus`, `ptree` ↦ `PTree`.  They instantiate ExecSC7 `execExecuteCsrrciSstatus` /
   `execExecuteCsrrSstatus` (which take the platform `misa` and a nominal `MPP`, from `ctrlOkS`).
   Rocq's `WpGprCsrwC.legalize_sie_clear_idem` has no Lean counterpart: Lean-only
   `AxSpinPOc.legalizeSieClearIdem` (bit-blasted, `bv_decide`, after rewriting the `ExtStatus`
   decoder away so no enum reaches `bv_decide`).
6. `rfF_wX_any` / `rfF_p0c`: via AxSpinE7d `rfFOfRf0` and AxSymEngine2 `rf0WXBits`/`rf0RXBits`.

**Rocq → Lean name map.**  `rfF_ifF` `rfFIfF`, `rfF_ifT` `rfFIfT`, `rfF_ifF4` `rfFIfF4`,
`rfF_ifF16` `rfFIfF16`, `css` `css`, `rfF_cE_H` `rfFCEH`, `rfF_cE_S` `rfFCES`,
`rfF_check_CSR_priv_ss` `rfFCheckCSRPrivSs`, `rfF_is_CSR_accessible_ss` `rfFIsCSRAccessibleSs`,
`rfF_stateen_ss` `rfFStateenSs`, `rfF_check_CSR_ss` `rfFCheckCSRSs`, `rfF_check_CSR_result_ss`
`rfFCheckCSRResultSs`, `rfF_read_CSR_ss` `rfFReadCSRSs`, `rfF_write_CSR_ss` `rfFWriteCSRSs`,
`cb_read_ss` `cbReadSs`, `cb_write_ss` `cbWriteSs`, `rfF_wX_any` `rfFWXAny`, `rfF_doCSR_ss`
`rfFDoCSRSs`, `rfF_q0a` `rfFQ0a`, `rfF_p0c` `rfFP0c`, `css_eq` `cssEq`, `exec_q0a` `execQ0a`,
`exec_p0c` `execP0c` (none in the duplicated-name table).  Lean-only (file-qualified):
`AxSpinPOc.legalizeSieClearIdem`, `AxSpinPOc.mppNominal`, the `rfF` callees
`AxSpinPOc.rfFCEU`/`rfFVms`/`rfFHaveNom`/`rfFLowest`/`rfFLegalizeMstatus`.

**Dropped:** `rfF_and_boolM` (deviation 2); Ltacs `vmr`/`rpeel`/`nzc` (deviation 1); the
`Print Assumptions` lines (the lint's axiom check covers them).  Rocq 24 lemmas/definitions;
Lean 23 + 7 Lean-only.
-/
import Weak.AxSpinPO
import Weak.AxSpinE7d
import Weak.AxSpineOk6
import Weak.ExecSC7

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. Read footprints -/

/-- Rocq `rfF_ifF`. -/
theorem rfFIfF {X : Type} (g : Bool) (A B : SailM X) : g = false → rfF B → rfF (if g then A else B) := by
  intro h; subst h; exact id
/-- Rocq `rfF_ifT`. -/
theorem rfFIfT {X : Type} (g : Bool) (A B : SailM X) : g = true → rfF A → rfF (if g then A else B) := by
  intro h; subst h; exact id
/-- Rocq `rfF_ifF4`. -/
theorem rfFIfF4 {X : Type} (g1 g2 g3 g4 : Bool) (A1 A2 A3 A4 B : SailM X) :
    g1 = false → g2 = false → g3 = false → g4 = false → rfF B →
    rfF (if g1 then A1 else if g2 then A2 else if g3 then A3 else if g4 then A4 else B) := by
  intro h1 h2 h3 h4; subst h1 h2 h3 h4; exact id
/-- Rocq `rfF_ifF16`. -/
theorem rfFIfF16 {X : Type}
    (g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 : Bool)
    (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 B : SailM X) :
    g1 = false → g2 = false → g3 = false → g4 = false → g5 = false → g6 = false → g7 = false →
    g8 = false → g9 = false → g10 = false → g11 = false → g12 = false → g13 = false →
    g14 = false → g15 = false → g16 = false → rfF B →
    rfF (if g1 then A1 else if g2 then A2 else if g3 then A3 else if g4 then A4 else
         if g5 then A5 else if g6 then A6 else if g7 then A7 else if g8 then A8 else
         if g9 then A9 else if g10 then A10 else if g11 then A11 else if g12 then A12 else
         if g13 then A13 else if g14 then A14 else if g15 then A15 else if g16 then A16 else B) := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  exact id

/-- Rocq `css`: the `sstatus` CSR address. -/
def css : BitVec 12 := 256#12

/-- Rocq `rfF_cE_H`. -/
theorem rfFCEH : rfF (currentlyEnabled .Ext_H) := by rff_auto
/-- Rocq `rfF_cE_S`. -/
theorem rfFCES : rfF (currentlyEnabled .Ext_S) := by rff_auto

/-- Rocq `rfF_check_CSR_priv_ss`. -/
theorem rfFCheckCSRPrivSs (p : Privilege) : rfF (check_CSR_priv css p) := by
  unfold check_CSR_priv
  refine rfFBind _ _ ?_ (fun _ => trivial)
  unfold privLevel_to_CSR_privbits
  cases p
  case Supervisor => exact rfFBind _ _ rfFCEH (fun b => by cases b <;> exact trivial)
  all_goals exact trivial

/-- Rocq `rfF_is_CSR_accessible_ss`. -/
theorem rfFIsCSRAccessibleSs (p : Privilege) (acc : CSRAccessType) :
    rfF (is_CSR_accessible css p acc) := by
  have e : is_CSR_accessible css p acc = currentlyEnabled .Ext_S := by
    cases p <;> cases acc <;> csr_dispatch_eq
  rw [e]; exact rfFCES

/-- Rocq `rfF_stateen_ss`. -/
theorem rfFStateenSs (p : Privilege) (acc : CSRAccessType) :
    rfF (stateen_allows_CSR_access css p acc) := by
  have e : stateen_allows_CSR_access css p acc = pure true := by
    cases p <;> cases acc <;> csr_dispatch_eq
  rw [e]; exact trivial

/-- Rocq `rfF_check_CSR_ss`. -/
theorem rfFCheckCSRSs (p : Privilege) (acc : CSRAccessType) : rfF (check_CSR css p acc) := by
  unfold check_CSR
  refine rfFBind _ _ (rfFCheckCSRPrivSs p) (fun b => ?_)
  refine AxSpineOk2.rfFIte _ _ _ ?_ trivial
  refine AxSpineOk2.rfFIte _ _ _ ?_ trivial
  exact rfFBind _ _ (rfFIsCSRAccessibleSs p acc)
    (fun _ => AxSpineOk2.rfFIte _ _ _ (rfFStateenSs p acc) trivial)

/-- Rocq `rfF_check_CSR_result_ss`. -/
theorem rfFCheckCSRResultSs (p : Privilege) (acc : CSRAccessType) :
    rfF (check_CSR_result css p acc) := by
  have e : is_CSR_exception_virtual css p acc = check_CSR css .Supervisor acc := by
    cases p <;> cases acc <;> csr_dispatch_eq
  unfold check_CSR_result
  rw [e]
  refine rfFBind _ _ (rfFCheckCSRSs p acc) (fun b => ?_)
  refine AxSpineOk2.rfFIte _ _ _ trivial ?_
  dsimp only
  refine AxSpineOk2.rfFIte _ _ _ ?_ ?_
  · exact rfFBind _ _ (rfFCheckCSRSs _ acc) (fun _ => AxSpineOk2.rfFIte _ _ _ trivial trivial)
  · exact rfFBind _ _ trivial (fun _ => AxSpineOk2.rfFIte _ _ _ trivial trivial)

/-- Rocq `rfF_read_CSR_ss`. -/
theorem rfFReadCSRSs : rfF (read_CSR css) := by
  have e : read_CSR css = (readReg Register.mstatus >>= fun x =>
      pure (Sail.BitVec.extractLsb (lower_mstatus x) 63 0)) := read_CSR_sstatus
  rw [e]
  exact rfFBind _ _ ⟨AxSymEngine2.notPin _ (by decide) (by decide), fun _ => trivial⟩ (fun _ => trivial)

theorem AxSpinPOc.rfFCEU : rfF (currentlyEnabled .Ext_U) := by rff_auto
theorem AxSpinPOc.rfFVms : rfF (virtual_memory_supported ()) := by rff_auto
theorem AxSpinPOc.rfFHaveNom (x : BitVec 2) : rfF (have_nominal_privLevel x) := by rff_auto
theorem AxSpinPOc.rfFLowest : rfF (lowest_supported_privLevel ()) := by rff_auto

/-- `legalize_mstatus` through its callees (deviation 1). -/
local macro "ax_spin_poc_lm" : tactic => `(tactic| repeat (first
      | with_reducible exact rfFCES
      | with_reducible exact AxSpinPOc.rfFCEU
      | with_reducible exact AxSpinPOc.rfFVms
      | with_reducible exact AxSpinPOc.rfFHaveNom _
      | with_reducible exact AxSpinPOc.rfFLowest
      | with_reducible exact AxSpineOk2.rfFPure _
      | (with_reducible apply rfFBind <;> try intro _)
      | with_reducible apply AxSpineOk2.rfFIte))

set_option maxHeartbeats 2000000 in
theorem AxSpinPOc.rfFLegalizeMstatus (o v : BitVec 64) : rfF (legalize_mstatus o v) := by
  unfold legalize_mstatus
  dsimp only
  ax_spin_poc_lm

/-- Rocq `rfF_write_CSR_ss`. -/
theorem rfFWriteCSRSs (v : BitVec 64) : rfF (write_CSR css v) := by
  have e := write_CSR_sstatus v
  rw [show css = 0x100#12 from rfl, e]
  refine rfFBind _ _ ⟨AxSymEngine2.notPin _ (by decide) (by decide), fun _ => trivial⟩ (fun o => ?_)
  refine rfFBind _ _ (by unfold legalize_sstatus; exact AxSpinPOc.rfFLegalizeMstatus _ _) (fun n => ?_)
  refine rfFBind0 _ _ ⟨AxSymEngine2.notPin _ (by decide) (by decide), trivial⟩ ?_
  exact rfFBind _ _ ⟨AxSymEngine2.notPin _ (by decide) (by decide), fun _ => trivial⟩ (fun _ => trivial)

/-- Rocq `cb_read_ss`. -/
theorem cbReadSs (d : BitVec 64) : csr_id_read_callback css d = pure () := by csr_dispatch_eq
/-- Rocq `cb_write_ss`. -/
theorem cbWriteSs (d : BitVec 64) : csr_id_write_callback css d = pure () := by csr_dispatch_eq

/-- Rocq `rfF_wX_any`. -/
theorem rfFWXAny (rd : regidx) (v : BitVec 64) : rfF (wX_bits rd v) := by
  cases rd
  exact rfFOfRf0 _ (rf0WXBits _ _)

/-- Rocq `rfF_doCSR_ss`. -/
theorem rfFDoCSRSs (v : BitVec 64) (rd : regidx) (op : csrop) (acc : CSRAccessType) :
    rfF (doCSR css v rd op acc) := by
  unfold doCSR
  refine rfFBind _ _ ⟨AxSymEngine2.notPin _ (by decide) (by decide), fun _ => trivial⟩ (fun p => ?_)
  refine rfFBind _ _ (rfFCheckCSRResultSs p acc) (fun c => ?_)
  rcases c with ⟨⟩ | ⟨⟩ | ⟨⟩
  · refine rfFBind _ _ ⟨AxSymEngine2.notPin _ (by decide) (by decide), fun _ => trivial⟩ (fun p2 => ?_)
    refine AxSpineOk2.rfFIte _ _ _ trivial ?_
    refine rfFBind _ _ (AxSpineOk2.rfFIte _ _ _ rfFReadCSRSs trivial) (fun rv => ?_)
    refine rfFBind _ _ (show rfF (pure rv : SailM (BitVec 64)) from trivial) (fun dv => ?_)
    refine AxSpineOk2.rfFIte _ _ _ ?_ ?_
    · rw [cbReadSs]
      exact rfFBind0 _ _ trivial (rfFBind0 _ _ (rfFWXAny _ _) trivial)
    · refine rfFBind _ _ (rfFWriteCSRSs _) (fun r => ?_)
      rcases r with fv | ⟨⟩
      · dsimp only
        rw [cbWriteSs]
        exact rfFBind0 _ _ (rfFWXAny _ _) (rfFBind0 _ _ trivial trivial)
      · exact trivial
  · exact trivial
  · exact trivial

/-- Rocq `rfF_q0a`. -/
theorem rfFQ0a : rfF (execute q0a) := by
  show rfF (execute_CSRImm css 2#5 (.Regidx 15#5) .CSRRC)
  unfold execute_CSRImm
  exact rfFDoCSRSs _ _ _ _

/-- Rocq `rfF_p0c`. -/
theorem rfFP0c : rfF (execute p0c) := by
  show rfF (execute_CSRReg css zreg (.Regidx 15#5) .CSRRS)
  unfold execute_CSRReg
  exact rfFBind _ _ (rfFOfRf0 _ (rf0RXBits _)) (fun _ => rfFDoCSRSs _ _ _ _)

/-! # 2. SC `exec` facts at the regime -/

/-- Rocq `css_eq` (deviation 4). -/
theorem cssEq : css = 0x100#12 := rfl

/-- (Lean-only, deviation 5) a nominal `MPP` as the bit-slice ExecSC7 takes. -/
theorem AxSpinPOc.mppNominal (m : BitVec 64) (h : haveNomVal (_get_Mstatus_MPP m) = true) :
    BitVec.extractLsb' 11 2 m ≠ 2#2 := by
  intro he
  rw [show _get_Mstatus_MPP m = 2#2 from mpp_of_extract m _ he] at h
  exact absurd h (by decide)

/-- (Lean-only, deviation 5) Rocq `WpGprCsrwC.legalize_sie_clear_idem`: with SIE already 0 and
the extension states off, `csrrci sstatus, 2`'s legalised write is the identity. -/
theorem AxSpinPOc.legalizeSieClearIdem (m : BitVec 64)
    (hSIE : (_get_Mstatus_SIE m == 1#1) = false)
    (hXS : _get_Mstatus_XS m = extStatus_map_forwards .Off)
    (hFS : _get_Mstatus_FS m = extStatus_map_forwards .Off)
    (hVS : _get_Mstatus_VS m = extStatus_map_forwards .Off)
    (hSD : _get_Mstatus_SD m = 0#1)
    (hMPP : haveNomVal (_get_Mstatus_MPP m) = true) :
    legalizeSstatusVal m (sstatusWriteVal m 2#5) = m := by
  have eOff : extStatus_map_forwards .Off = 0#2 := rfl
  have eD : ∀ x : BitVec 2, (extStatus_map_backwards x == .Dirty) = (x == 3#2) := by decide
  have eB : ∀ b : Bool, bool_to_bit b = BitVec.ofBool b := by decide
  have eN : ∀ x : BitVec 2, haveNomVal x = (x != 2#2) := by decide
  rw [eOff] at hXS hFS hVS
  rw [eN] at hMPP
  unfold legalizeSstatusVal mstatusLegalize sstatusWriteVal sstatusRead lift_sstatus lower_mstatus
  simp only [eD, eB, eOff, legalize_extStatus, plat_mstatus_legal_fs, plat_mstatus_legal_vs,
    Mk_Sstatus, Mk_Mstatus]
  simp only [_update_Mstatus_SIE, _update_Mstatus_MIE, _update_Mstatus_SPIE, _update_Mstatus_MPIE,
    _update_Mstatus_SPP, _update_Mstatus_MPP, _update_Mstatus_VS, _update_Mstatus_FS,
    _update_Mstatus_XS, _update_Mstatus_MPRV, _update_Mstatus_SUM, _update_Mstatus_MXR,
    _update_Mstatus_TVM, _update_Mstatus_TW, _update_Mstatus_TSR, _update_Mstatus_SPELP,
    _update_Mstatus_MPELP, _update_Mstatus_UXL, _update_Mstatus_SD,
    _get_Mstatus_SIE, _get_Mstatus_MIE, _get_Mstatus_SPIE, _get_Mstatus_MPIE,
    _get_Mstatus_SPP, _get_Mstatus_MPP, _get_Mstatus_VS, _get_Mstatus_FS,
    _get_Mstatus_XS, _get_Mstatus_MPRV, _get_Mstatus_SUM, _get_Mstatus_MXR,
    _get_Mstatus_TVM, _get_Mstatus_TW, _get_Mstatus_TSR, _get_Mstatus_SPELP,
    _get_Mstatus_MPELP, _get_Mstatus_UXL, _get_Mstatus_SD,
    _update_Sstatus_SIE, _update_Sstatus_SPIE, _update_Sstatus_SPP, _update_Sstatus_VS,
    _update_Sstatus_FS, _update_Sstatus_XS, _update_Sstatus_SUM, _update_Sstatus_MXR,
    _update_Sstatus_SPELP, _update_Sstatus_UXL, _update_Sstatus_SD,
    _get_Sstatus_SIE, _get_Sstatus_SPIE, _get_Sstatus_SPP, _get_Sstatus_VS,
    _get_Sstatus_FS, _get_Sstatus_XS, _get_Sstatus_SUM, _get_Sstatus_MXR,
    _get_Sstatus_SPELP, _get_Sstatus_UXL,
    Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', Sail.BitVec.extractLsb,
    BitVec.extractLsb, zero_extend, Sail.BitVec.zeroExtend, zeros] at hSIE hXS hFS hVS hSD hMPP ⊢
  bv_decide

/-- Rocq `exec_q0a`: csrrci a5,sstatus,2 at a regime state writes a5 := the S-view of mstatus,
nothing else changes (SIE already 0). -/
theorem execQ0a (T : PTree) (satp0 : BitVec 64) (s : ExecSt) (h : ctrlOkS T satp0 s.regs) :
    exec (execute q0a) s = some (RETIRE_SUCCESS, s.setGpr 15#5 (sstatusRead (s.regs .mstatus))) := by
  obtain ⟨hpriv, _, hmisa, _, _, _, _, hms, hSIE, _⟩ := h
  obtain ⟨_, _, _, _, hXS, hFS, hVS, hSD, hMPP, _⟩ := hms
  exact execExecuteCsrrciSstatus 2#5 15#5 (s.regs .mstatus) s hpriv rfl hmisa (by decide) (by decide)
    (AxSpinPOc.mppNominal _ hMPP)
    (AxSpinPOc.legalizeSieClearIdem _ hSIE hXS hFS hVS hSD hMPP)

/-- Rocq `exec_p0c`: csrr a5,sstatus at a regime state writes a5 := the S-view of mstatus. -/
theorem execP0c (T : PTree) (satp0 : BitVec 64) (s : ExecSt) (h : ctrlOkS T satp0 s.regs) :
    exec (execute p0c) s = some (RETIRE_SUCCESS, s.setGpr 15#5 (sstatusRead (s.regs .mstatus))) := by
  obtain ⟨hpriv, _, hmisa, _⟩ := h
  have hS : (_get_Misa_S (s.regs .misa) == 1#1) = true := by rw [hmisa]; decide
  exact execExecuteCsrrSstatus 15#5 (s.regs .mstatus) s hpriv rfl hS (by decide)

end Weak
