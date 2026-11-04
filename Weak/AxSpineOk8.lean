/-
Weak: **NON-VACUITY of the S-mode regime** at `AxSmodeProbe`'s concrete SUPERVISOR state (Sv39
over a real 3-level table, cold TLB), and X at the S-mode kernel regime.

Rocq: `iris/AxSpineOk8.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 `nvSCtrlOk`: the regime predicate `ctrlOkS T satp` HOLDS at the probe's register file (for ANY
tree `T`: the TLB is cold), and the satp constant satisfies `spineOkTS`'s three static premises
for the probe's root (`nvSSatpMode`/`nvSSatpAsid`/`nvSRootVal`).  So `spineOkTS`'s ∀-statement is
not about an empty regime.  §2 `nvSCert`: at the probe state with the text word replaced by
`c.mv a0, ra` (0x8506) — VA = PA 0x80000000, 4-aligned: the fetch reads 4 bytes through the
COLD-TLB walk (3 PTE reads + fill) — `AxSymEngine.wpdInstrOfEvA`'s certificate premise for the
REAL `riscvStep`, BOTH ticks, all pin answers (post: PC + 2, a0 = ra), by the boolean checker
`evb` (`evbSound`).  §3 `XGprWriteS`: X at the S-mode regime, from `spineOkTS`.
NOT DONE (as Rocq): a concrete tree for the probe table with `textAtS` at 0x80000000.

## Deviations from Rocq

1. SPELLING (as `AxSpineOk6`/`AxSpineOk7` deviation 1): `mstate` ↦ `ExecSt`, `register_lookup r
   rs` ↦ `rs r`, `mword n` ↦ `BitVec n`, `w64` ↦ `AxEpiProbe.w64`, `s_regs`/`s_at`/`s_pc`/
   `s_satp`/`s_root` ↦ `sRegs`/`sAt`/`sPc`/`AxSmodeProbe.sSatp`/`AxSmodeProbe.sRoot`,
   `dev0_state` ↦ the probe's own device state (`sAt`'s `testDevs`); the gmap inserts of `nvS_t`
   are a function update of the byte map; `'b"1000"` ↦ `8#4`; the satp facts take `AxSpineOk4`
   deviation 7's shapes (`zero_extend (m := 16) (satp_to_asid _) = 0#16`, the root
   `BitVec.setWidth 44 (satp_to_ppn _)`); `bool_decide (x = y)` ↦ `x == y`.
2. `vm_compute` ↦ `decide +kernel`; the Ltac `vr` is dropped (each conjunct is decided).
   `nvSTlbCold`: the 64-way case split on the hash is replaced by "the reset TLB vector is
   `Vector.replicate 64 none`", so every `[_]!` lookup is `none`.
3. Pins (O2/`AxRunClose`): `evb` answers both pins (both 0, then both 1), so "all seip answers"
   reads "all pin answers".
4. `XGprWriteS` (Rocq `X_gpr_write_S`): Rocq's `Hloc` premise is DROPPED (Stage C: Lean
   `XGprWriteHoldsT` takes only `Hsp Htext Hflow`; `AxSymEngine` deviation); the invariant
   instance is `InvGS_gen hlc GF` for any `hlc` (as `AxSpineOk5`; Rocq `HasNoLc`).  Section
   variables are explicit arguments.

**Rocq → Lean name map.**  `nvS_rs` `nvSRs`, `nvS_satp` `nvSSatp`, `nvS_tlb_cold` `nvSTlbCold`,
`nvS_ctrl_ok` `nvSCtrlOk`, `nvS_satp_mode` `nvSSatpMode`, `nvS_satp_asid` `nvSSatpAsid`,
`nvS_root` `nvSRoot`, `nvS_root_val` `nvSRootVal`, `nvS_t` `nvST`, `nvS_img` `nvSImg`,
`nvS_fetch` `nvSFetch`, `nvS_step0_triv` `nvSStep0Triv`, `nvS_post` `nvSPost`, `nvS_step_false`
`nvSStepFalse`, `nvS_step_true` `nvSStepTrue`, `nvS_cert` `nvSCert`, `X_gpr_write_S`
`XGprWriteS`.  None is in the duplicated-name table.  Lean-only: none.

**Dropped:** the Ltac `vr` (deviation 2); the `Print Assumptions` lines (the lint's axiom check
covers them).  Rocq 17 definitions/lemmas, Lean 17.
-/
import Weak.AxSmodeProbe
import Weak.AxSpineOk7

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. The regime holds at the probe state -/

/-- Rocq `nvS_rs`. -/
def nvSRs : RegFile := sRegs sPc

/-- Rocq `nvS_satp`. -/
def nvSSatp : BitVec 64 := AxEpiProbe.w64 AxSmodeProbe.sSatp

/-- Rocq `nvS_tlb_cold`: the probe's TLB is cold, so it is exact for any tree. -/
theorem nvSTlbCold (T : PTree) : tlbExact T (nvSRs .tlb) := by
  intro vpn' ent hget
  exfalso
  have h : nvSRs .tlb = Vector.replicate 64 none := rfl
  rw [h] at hget
  by_cases hi : tlb_hash 39 vpn' < 64
  · rw [getElem!_pos (Vector.replicate 64 (none : Option TLB_Entry)) (tlb_hash 39 vpn') hi, Vector.getElem_replicate] at hget
    cases hget
  · rw [getElem!_neg (Vector.replicate 64 (none : Option TLB_Entry)) (tlb_hash 39 vpn') hi] at hget
    cases hget

/-- Rocq `nvS_ctrl_ok`. -/
theorem nvSCtrlOk (T : PTree) : ctrlOkS T nvSSatp nvSRs := by
  unfold ctrlOkS AxSpineOk6.pmpOk AxSpineOk6.sconfMsFacts
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_,
    nvSTlbCold T, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | decide +kernel | rfl

/-- Rocq `nvS_satp_mode`. -/
theorem nvSSatpMode : _get_Satp64_Mode (Mk_Satp64 nvSSatp) = 8#4 := by decide +kernel

/-- Rocq `nvS_satp_asid`. -/
theorem nvSSatpAsid : zero_extend (m := 16) (satp_to_asid nvSSatp) = 0#16 := by decide +kernel

/-- Rocq `nvS_root`. -/
def nvSRoot : BitVec 44 := BitVec.setWidth 44 (satp_to_ppn nvSSatp)

/-- Rocq `nvS_root_val`. -/
theorem nvSRootVal : nvSRoot.toNat = AxSmodeProbe.sRoot := by decide +kernel

/-! # 2. The concrete S-mode certificate -/

/-- Rocq `nvS_t`: the probe state with `c.mv a0, ra` (0x8506) at `sPc`. -/
def nvST : ExecSt :=
  ⟨nvSRs,
   fun a => if a = AxEpiProbe.w64 sPc then some 0x06#8
     else if a = AxEpiProbe.w64 (sPc + 1) then some 0x85#8
     else (sAt sPc).mem a,
   (sAt sPc).dev⟩

/-- Rocq `nvS_img`. -/
def nvSImg : Image := imgOf nvST

/-- Rocq `nvS_fetch`: the fetch alone (cold TLB ⇒ the walk runs), `F_RVC 0x8506`. -/
theorem nvSFetch : evb nvSImg (fun r _ => match r with
      | .F_RVC h => h == 0x8506#16
      | _ => false)
    (fetch ()) nvST = true := by decide +kernel

/-- Rocq `nvS_step0_triv`. -/
theorem nvSStep0Triv : evb nvSImg (fun _ _ => true) (riscvStep false) nvST = true := by
  decide +kernel

/-- Rocq `nvS_post`: PC advanced by 2, a0 := ra. -/
def nvSPost (_ : Unit) (t' : ExecSt) : Bool :=
  (t'.regs .PC == AxEpiProbe.w64 (sPc + 2)) && (t'.regs .x10 == nvSRs .x1)

/-- Rocq `nvS_step_false`. -/
theorem nvSStepFalse : evb nvSImg nvSPost (riscvStep false) nvST = true := by decide +kernel

/-- Rocq `nvS_step_true`. -/
theorem nvSStepTrue : evb nvSImg nvSPost (riscvStep true) nvST = true := by decide +kernel

/-- Rocq `nvS_cert`. -/
theorem nvSCert (tick : Bool) :
    EvA nvSImg (fun _ _ => False) (fun x t' => nvSPost x t' = true) (riscvStep tick) nvST := by
  apply evbSound
  cases tick
  · exact nvSStepFalse
  · exact nvSStepTrue

/-! # 3. X and the real leaves AT THE S-MODE KERNEL REGIME -/

/-- Rocq `X_gpr_write_S` (deviation 4). -/
theorem XGprWriteS {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
    (σi : ExecSt) (T : PTree) (satp0 : BitVec 64) (i : Agent) (cpu : CPU)
    (Hm : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (Ha : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (Hp : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (Htext : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i (imgS σi)⌝)
    (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
      (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
         imgBytes (imgS σi) base n = some vs) →
      AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k) :
    XGprWrite (GF := GF) i cpu (ctrlOkS T satp0)
      (textOkD (imgS σi) (ctrlOkS T satp0) (textAtS σi T)) :=
  XGprWriteHoldsT (imgS σi) i cpu (ctrlOkS T satp0) (textAtS σi T)
    (spineOkTS σi T satp0 Hm Ha Hp) Htext Hflow

end Weak
