/-
Weak: **the spinlock plan, PHASE 5 item (4), part 4** — THE SYMBOLIC ARBITRARY-VA FETCH CHAIN
of a whole `riscvStep` at the S-mode kernel regime.

Rocq: `iris/AxSpinVA4.v` @ xxvzwolszwmp.

## What this file proves

THEOREM `chainFetchMapped4` / `chainFetchMapped2`: at EVERY state `t` of the interrupts-off
S-mode regime `ctrlOkS T satp0` (Sv39, kernel satp, the TLB holding only exact walk entries of
the image tree `T`), with PC = an ARBITRARY VA `va` that is canonical, 2-aligned, mapped by `T`
to a leaf `w` that grants supervisor fetch with A preset, whose page-table slots are image bytes
of `σi` and whose translated pa is RAM (aligned as the fetch width), the step's label CHAIN from
the boundary is, for BOTH ticks and EVERY pin answer,
    `walkKeys T tlb (svpnOf va) p2 p1 ++ [.ENf (paZ pa, n)]`
— nothing (TLB hit) or EXACTLY the three Sv39 slot reads (TLB miss / foreign slot), then the
fetch of `n` = 4 (4-aligned VA) or 2 bytes at the translated pa, which (deviation 1) has NO image
bytes.  The chain ends at the fetch.  `firstLabelMapped4`: the i = 0 case at the boundary node.

PIECES: `FMemReadFetchEnd` (the fetch's RAM read ENDS the chain; register-only PMA/PMP/MMIO
prefix from the regime: `fetchEnd4` / `fetchEnd2`), `FFetch4` / `FFetch2` (the model's `fetch`
up to the read, translation abstract), `FDisp` (the demonic pin reads of `dispatchInterrupt`,
`none` at SIE = 0), `FRiscvStepFetch` (the `try_step` / `run_hart_active` prefix),
`FTranslateFetch` (`AxSpinVA3.FTranslateAddrImg` at the fetch).

HONEST SCOPE / EXCLUDED (as Rocq): the FAULT arms (misaligned, non-canonical, unmapped,
non-executable / A-clear leaf, PMA/PMP-denied fetch), the post-fault stvec chain and the
data-side symbolic chain; the generic machinery (`AxSpinVA`) and the evaluator (`fstep`) cover
them at any concrete state.

## Deviations from Rocq

1. O2 STAGE C (`AxSpinVA` deviation 1, Q13).  A fetch is no chain key: a fetch whose bytes are
   in the image is the pinned administrative step `FEC.fcIf` that CONTINUES the chain with the
   image word (into decode / execute, of which this file claims nothing), and only a fetch with
   NO image bytes ends the chain, with the key `ekey.ENf (paZ pa, n)` (`FEC.fcNf`).  So Rocq's
   end key `ERd (false, uint pa, n)` is `.ENf (paZ pa, n)` throughout (`FMemReadFetchEnd`,
   `fetchEnd4/2`, `FTranslateFetch`'s `Hend`, `chainFetchMapped4/2`, `firstLabelMapped4`), and
   each of them takes the extra premise `imgBytes img (paZ pa) n = none` (at the theorems:
   `imgBytes (imgOf σi) (paZ pa) n = none`).  At a VA whose fetch IS in the image (e.g. kernel
   text) the step's chain is the walk keys followed by the decoded instruction's own keys; the
   walk prefix of that case is the Lean-only `AxSpinVA4.fetchMappedImg4` (at `fetch ()`, the
   result `F_RVC`/`F_Base` of the image word handed to the continuation; 4-aligned VA).
2. THE PINS (`AxRunClose` deviation 1): Rocq `¬ seip_reg r` ↦ `¬ AxRunClose.pinReg r`; the Lean
   `read_mip` reads `sig_meip` then `sig_seip`, both answered demonically in `FDisp` (as
   `AxSpineOk7.sptDispS`).
3. SPELLING (as `AxSpinVA3` deviation 1, `AxSpineOk6` deviation 1/4): `mstate` ↦ `ExecSt`,
   `register_lookup r t.(sregs)` ↦ `t.regs .r`, `set_reg t (R_bool minstret_increment) b` ↦
   `t.setReg .minstret_increment b`, `img_of` ↦ `imgOf`, `uint` ↦ `paZ`,
   `addr_is_ram pa ∧ addr_is_ram (pa_add pa k)` ↦ `inRam pa (k + 1)`, `eq_vec x 'b"1" = true` ↦
   `(x == 1#1) = true`, `neq_vec (access_vec_dec va i) 'b"0"` ↦ `Sail.BitVec.access va i != 0#1`,
   `pt_slot_mem` ↦ `WeakWalkEff.ptSlotMem`, `pte_check_ok` ↦ `pteCheckOk`, `pte_pbmt0` ↦
   `ptePbmt0`, `PPN_of_PTE` ↦ `ppn0`, `AThread p k` ↦ `⟨p, k⟩`, `Interface.Ret tt` ↦ `.pure ()`,
   `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg`; the satp hypotheses `Hmode Hasid Hppn`
   take `AxSpineOk4` deviation 7's shapes and are explicit arguments (with `σi T satp0`).
4. `FMemReadFetchEnd`: Rocq `0 < n` ↦ `vmemWidth n` (the `checked_mem_read` width split,
   `AxSpinVA3` deviation 3); its PMA/PMP/MMIO facts are at `tm μ t` as `AxSpinVA3`.
5. The Lean `fetch` (lean-sail model) tests `PC[0]`, then `PC[1]` with `Ext_Zca`, then the
   4-alignment with `Ext_Ziccif`; `FFetch2`'s 2-aligned arm needs `misa.C` (as Rocq).  The step
   prefix `try_step` has no `ext_pre_step_hook` effect.
6. TACTICS: Rocq `nseip4` / `g_step` / `g_go` / `f_useX` ↦ the `AxSpinVA3` kit, the Lean-only
   lemmas `AxSpinVA4.fFactWrite` / `fFactReadPin` / `fRWrite` and the tactic `ax_spin_va4_go`.

**Rocq → Lean name map.**  `FEC_write_reg` `FECWriteReg`, `F_mem_read_fetch_end`
`FMemReadFetchEnd`, `fetch_end_4` `fetchEnd4`, `fetch_end_2` `fetchEnd2`, `F_fetch_4` `FFetch4`,
`F_fetch_2` `FFetch2`, `F_disp` `FDisp`, `ctrl_ok_S_minstret_inc` `ctrlOkSMinstretInc`,
`F_riscv_step_fetch` `FRiscvStepFetch`, `fetchable` `fetchable`, `F_translate_fetch`
`FTranslateFetch`, `chain_fetch_mapped_4` `chainFetchMapped4`, `chain_fetch_mapped_2`
`chainFetchMapped2`, `first_label_mapped_4` `firstLabelMapped4`.  None is in the
duplicated-name table.  Lean-only (file-qualified): kit `AxSpinVA4.fFactWrite`,
`AxSpinVA4.fFactReadPin`, `AxSpinVA4.fRWrite`, tactic `ax_spin_va4_go`; the `ENf` read nodes
`AxSpinVA4.fReadRamFetchNf`, `AxSpinVA4.fCheckedMemReadFetchNf`; the in-image case (§5)
`AxSpinVA4.fReadRamFetchGo`, `AxSpinVA4.fCheckedMemReadFetchGo`, `AxSpinVA4.fMemReadFetchGo`,
`AxSpinVA4.fetchRes`, `AxSpinVA4.fetchGo4`, `AxSpinVA4.fetchGoAt4`, `AxSpinVA4.fetchMappedImg4`.

**Dropped:** none (Rocq 1 definition + 13 lemmas; Lean the same 14, + 12 Lean-only + 1 tactic).  **Not ported:** the
Ltacs (deviation 6) and the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxSpinVA3
import Weak.AxSpineOk7

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 0. The kit additions -/

section kit
variable {img : Image}

local notation "FC" => FEC img

/-- Rocq `FEC_write_reg`. -/
theorem FECWriteReg (img : Image) (QE : List ekey → Sail.Error exception → ExecSt → Prop)
    (Q : List ekey → Unit → ExecSt → Prop) (r : Register) (v : RegisterType r) (Ks : List ekey)
    (t : ExecSt) :
    ¬ AxRunClose.pinReg r → Q Ks () (t.setReg r v) →
    FEC img QE Q Ks (writeReg r v : SailM Unit) t :=
  fun hr hq => .fcWr Ks r v _ t hr (.fcRet _ _ _ hq)

theorem AxSpinVA4.fFactWrite {Y : Type} {QE : List ekey → Sail.Error exception → ExecSt → Prop}
    {Q : List ekey → Y → ExecSt → Prop} {r : Register} {v : RegisterType r}
    {f : PUnit → SailM Y} {Ks : List ekey} {t : ExecSt}
    (hr : ¬ AxRunClose.pinReg r) (H : FC QE Q Ks (f PUnit.unit) (t.setReg r v)) :
    FC QE Q Ks (writeReg r v >>= f) t :=
  FECBind img QE Q _ f Ks t (.fcWr Ks r v _ t hr (.fcRet _ _ _ H))

/-- A demonic pin read. -/
theorem AxSpinVA4.fFactReadPin {Y : Type} {QE : List ekey → Sail.Error exception → ExecSt → Prop}
    {Q : List ekey → Y → ExecSt → Prop} {r : Register} {f : RegisterType r → SailM Y}
    {Ks : List ekey} {t : ExecSt}
    (hr : AxRunClose.pinReg r) (H : ∀ v, FC QE Q Ks (f v) t) :
    FC QE Q Ks (readReg r >>= f) t :=
  FECBind img QE Q _ f Ks t (.fcRd Ks r _ t (fun _ v => .fcRet _ _ _ (H v)) (fun hn => absurd hr hn))

theorem AxSpinVA4.fRWrite {R X : Type} {QE : List ekey → Sail.Error exception → ExecSt → Prop}
    {Q : List ekey → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {r : Register} {v : RegisterType r} {f : PUnit → SailME R X} {Ks : List ekey} {t : ExecSt}
    (hr : ¬ AxRunClose.pinReg r) (H : FC QE Q Ks (ExceptT.run (f PUnit.unit)) (t.setReg r v)) :
    FC QE Q Ks (ExceptT.run (liftM (writeReg r v) >>= f)) t :=
  AxSpinVA3.fRLift (P := fun Ks' _ t' => Ks' = Ks ∧ t' = t.setReg r v)
    (FECWriteReg img _ _ r v Ks t hr ⟨rfl, rfl⟩)
    (fun _ _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact H)

end kit

/-- (Lean-only) Rocq `g_go`: `ax_spin_va3_go` plus non-pin writes and the model's constant
configuration tests. -/
macro "ax_spin_va4_go" : tactic => `(tactic| repeat (first
  | ((with_reducible refine AxSpinVA3.fRRead ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | ((with_reducible refine AxSpinVA4.fRWrite ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | with_reducible refine AxSpinVA3.fRPureBind ?_
  | with_reducible refine AxSpinVA3.fRAssoc ?_
  | with_reducible refine AxSpinVA3.fFactAssoc ?_
  | ((with_reducible refine AxSpinVA3.fFactRead ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | ((with_reducible refine AxSpinVA4.fFactWrite ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | with_reducible refine AxSpinVA3.fFactPure ?_
  | (simp (config := { decide := true }) only [↓reduceIte, Bool.false_eq_true,
      get_config_print_instr, get_config_rvfi, ext_fetch_hook, ext_fetch_check_pc])))

/-! # 1. The fetch read ENDS the chain -/

section reads
variable (img : Image)

local notation "FC" => FEC img

/-- (Lean-only) The fetch's RAM read with no image bytes: the chain's `ENf` end. -/
theorem AxSpinVA4.fReadRamFetchNf (w : Nat) (QE : List ekey → Sail.Error exception → ExecSt → Prop)
    (Q : List ekey → (BitVec (8 * w) × Unit) → ExecSt → Prop) (pa : BitVec 64) (t : ExecSt) :
    devAddr pa = false → imgBytes img (paZ pa) w = none →
    FC QE Q [.ENf (paZ pa, w)] (read_ram .Read_ifetch (.Physaddr pa) w false) t := by
  intro hdev hv
  simp only [read_ram, PreSail.sail_mem_read, PreSail.emit, pure_bind]
  exact FEC.fcNf (img := img) w 64
    { access_kind := .AK_ifetch (), va := none, pa := pa, translation := (), size := w,
      tag := false } _ t hdev rfl hv

section cmr
variable (μ : ExecSt) (pbmt : page_based_mem_type) (w : Nat) (pa : BitVec 64) (t : ExecSt)
variable (Hw : vmemWidth w)
  (Hcp : execA (check_pma_with_pmp_priority (.InstructionFetch ()) pbmt .Supervisor (.Physaddr pa)
    w false) (tm μ t) = some (.Ok pmaOkAligned, tm μ t))
  (Hpmp : execA (pmpCheck (.Physaddr pa) w (.InstructionFetch ()) .Supervisor) (tm μ t)
    = some (none, tm μ t))
  (Hmmio : execA (within_mmio_readable (.Physaddr pa) w) (tm μ t) = some (false, tm μ t))
  (Hdev : devAddr pa = false)

include Hw Hcp Hpmp Hmmio Hdev in
/-- (Lean-only) `checked_mem_read` of a fetch with no image bytes: the `ENf` end. -/
theorem AxSpinVA4.fCheckedMemReadFetchNf
    (Q : List ekey → Result (BitVec (8 * w) × Unit) (physaddr × ExceptionType) → ExecSt → Prop) :
    imgBytes img (paZ pa) w = none →
    FC (fun _ _ _ => False) Q [.ENf (paZ pa, w)]
      (checked_mem_read (.InstructionFetch ()) pbmt .Supervisor (.Physaddr pa) w false false false
        false) t := by
  intro hv
  unfold checked_mem_read
  apply FECCatchEarlyReturn
  refine AxSpinVA3.fRAssoc ?_
  refine AxSpinVA3.fRUse (μ := μ) (rfFCheckPmaWithPmpPriority _ _ _ _ _ _) Hcp ?_
  refine AxSpinVA3.fRPureBind ?_
  refine AxSpinVA3.fRUse (μ := μ) (a := ((1 : Int), (w : Int))) (rfFSplitMisaligned _ _ _ _) rfl ?_
  simp only [misaligned_order, sys_misaligned_order_decreasing, ↓reduceIte, Bool.false_eq_true,
    Int.reduceSub, Int.toNat_zero]
  rcases Hw with rfl | rfl | rfl | rfl
  all_goals
    try simp only [read_kind_of_flags]
    first
      | refine AxSpinVA3.fRUse (μ := μ) (rfFReadKindOfFlags _ _ _) rfl ?_
      | refine AxSpinVA3.fRPureBind ?_
    refine AxSpinVA3.fRAssoc ?_
    refine AxSpinVA3.fRBind _ _ _ _ _ _ ?_
    refine FECUntilMT1 img _ _ _ _ _ _ _ ?_
    refine AxSpinVA3.fRUse (μ := μ) (by trivial) rfl ?_
    simp only [bits_of_physaddr, Int.cast_ofNat_Int, Int.zero_mul, addIntZero, Int.toNat_one,
      Int.mul_one]
    refine AxSpinVA3.fRUse (μ := μ) (rfFPmpCheck _ _ _ _) Hpmp ?_
    dsimp only
    refine AxSpinVA3.fRUse (μ := μ) (rfFWithinMmioReadable _ _) Hmmio ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine AxSpinVA3.fRAssoc ?_
    refine AxSpinVA3.fRLift (P := fun _ _ _ => False)
      (AxSpinVA4.fReadRamFetchNf img _ _ _ pa t Hdev hv) (fun _ _ _ h => h.elim)
end cmr

/-- Rocq `F_mem_read_fetch_end` (deviations 1, 4). -/
theorem FMemReadFetchEnd (μ : ExecSt) (n : Nat) (pbmt : page_based_mem_type) (addr : BitVec 64)
    (Q : List ekey → Result (BitVec (8 * n)) (physaddr × ExceptionType) → ExecSt → Prop)
    (t : ExecSt) :
    vmemWidth n →
    execA (check_pma_with_pmp_priority (.InstructionFetch ()) pbmt .Supervisor (.Physaddr addr) n
      false) (tm μ t) = some (.Ok pmaOkAligned, tm μ t) →
    execA (pmpCheck (.Physaddr addr) n (.InstructionFetch ()) .Supervisor) (tm μ t)
      = some (none, tm μ t) →
    execA (within_mmio_readable (.Physaddr addr) n) (tm μ t) = some (false, tm μ t) →
    devAddr addr = false →
    imgBytes img (paZ addr) n = none →
    t.regs .cur_privilege = .Supervisor →
    FC (fun _ _ _ => False) Q [.ENf (paZ addr, n)]
      (mem_read (.InstructionFetch ()) pbmt (.Physaddr addr) n false false false) t := by
  intro Hn Hcp Hpmp Hmmio Hdev Hv Hpriv
  have Hep := execEffectivePrivilegeFetch ((tm μ t).regs .mstatus) ((tm μ t).regs .cur_privilege)
    (tm μ t)
  to_a Hep
  unfold mem_read
  ax_spin_va4_go
  refine AxSpinVA3.fFactUse (μ := μ) (rfFEffectivePrivilege _ _ _) Hep ?_
  rw [show (tm μ t).regs .cur_privilege = .Supervisor from Hpriv]
  unfold mem_read_priv mem_read_priv_meta
  dsimp only
  refine AxSpinVA3.fFactAssoc ?_
  exact AxSpinVA3.fFact (P := fun _ _ _ => False)
    (AxSpinVA4.fCheckedMemReadFetchNf img μ pbmt n addr t Hn Hcp Hpmp Hmmio Hdev _ Hv)
    (fun _ _ _ h => h.elim)

end reads

/-- The register-only facts of the fetch read, from the regime (Rocq `fetch_end_4`). -/
theorem fetchEnd4 (img : Image) (T : PTree) (satp0 : BitVec 64) (pa : BitVec 64)
    (Q : List ekey → Result (BitVec (8 * 4)) (physaddr × ExceptionType) → ExecSt → Prop)
    (t : ExecSt) :
    ctrlOkS T satp0 t.regs → inRam pa 4 → is_aligned_paddr (.Physaddr pa) 4 = true →
    imgBytes img (paZ pa) 4 = none →
    FEC img (fun _ _ _ => False) Q [.ENf (paZ pa, 4)]
      (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr pa) 4 false false false) t := by
  intro Hc Hram Halp Hv
  have Hc0 := Hc
  obtain ⟨Hpriv, -, -, -, -, -, -, -, -, -, -, -, HA, Hord, HX, -, -⟩ := Hc0
  obtain ⟨region, Hrange, Hm, Hx, Hcl, Hsig, Hh, Hdev, -⟩ :=
    ramFetchFacts T satp0 (tm t t) pa 4 Hc (by decide) (by decide) (by decide) Hram
  have Hpma := execPmaCheckRam pa .PBMT_PMA region (tm t t) Hm Halp Hx
  have Hcp : exec (check_pma_with_pmp_priority (.InstructionFetch ()) .PBMT_PMA .Supervisor
      (.Physaddr pa) 4 false) (tm t t) = some (.Ok pmaOkAligned, tm t t) := by
    unfold check_pma_with_pmp_priority
    exec_run [Hpma]
  to_a Hcp
  have Hpmp := execPmpCheckSupervisorGrant pa 4 (tm t t) HA Hord Hrange HX
  to_a Hpmp
  have Hmmio := execAMmioFalse pa 4 (tm t t) Hcl Hsig Hh
  exact FMemReadFetchEnd img t 4 .PBMT_PMA pa Q t (by simp [vmemWidth]) Hcp Hpmp Hmmio Hdev Hv
    Hpriv

/-- Rocq `fetch_end_2`. -/
theorem fetchEnd2 (img : Image) (T : PTree) (satp0 : BitVec 64) (pa : BitVec 64)
    (Q : List ekey → Result (BitVec (8 * 2)) (physaddr × ExceptionType) → ExecSt → Prop)
    (t : ExecSt) :
    ctrlOkS T satp0 t.regs → inRam pa 2 → is_aligned_paddr (.Physaddr pa) 2 = true →
    imgBytes img (paZ pa) 2 = none →
    FEC img (fun _ _ _ => False) Q [.ENf (paZ pa, 2)]
      (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr pa) 2 false false false) t := by
  intro Hc Hram Halp Hv
  have Hc0 := Hc
  obtain ⟨Hpriv, -, -, -, -, -, -, -, -, -, -, -, HA, Hord, HX, -, -⟩ := Hc0
  obtain ⟨region, Hrange, Hm, Hx, Hcl, Hsig, Hh, Hdev, -⟩ :=
    ramFetchFacts T satp0 (tm t t) pa 2 Hc (by decide) (by decide) (by decide) Hram
  have Hpma := execPmaCheckRam2 pa .PBMT_PMA region (tm t t) Hm Halp Hx
  have Hcp : exec (check_pma_with_pmp_priority (.InstructionFetch ()) .PBMT_PMA .Supervisor
      (.Physaddr pa) 2 false) (tm t t) = some (.Ok pmaOkAligned, tm t t) := by
    unfold check_pma_with_pmp_priority
    exec_run [Hpma]
  to_a Hcp
  have Hpmp := execPmpCheckSupervisorGrant pa 2 (tm t t) HA Hord Hrange HX
  to_a Hpmp
  have Hmmio := execAMmioFalse pa 2 (tm t t) Hcl Hsig Hh
  exact FMemReadFetchEnd img t 2 .PBMT_PMA pa Q t (by simp [vmemWidth]) Hcp Hpmp Hmmio Hdev Hv
    Hpriv

/-! # 2. `fetch`, translation abstract -/

/-- Rocq `F_fetch_4`. -/
theorem FFetch4 (img : Image) (va pa : BitVec 64) (Ktr : List ekey)
    (Q : List ekey → FetchResult → ExecSt → Prop) (t : ExecSt) :
    t.regs .PC = va →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    FEC img (fun _ _ _ => False)
      (fun Ks' r t' => r = .Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw) ∧
        ∀ Q' : List ekey → Result (BitVec (8 * 4)) (physaddr × ExceptionType) → ExecSt → Prop,
          FEC img (fun _ _ _ => False) Q' Ks'
            (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr pa) 4 false false false) t')
      Ktr (translateAddr (.Virtaddr va) (.InstructionFetch ())) t →
    FEC img (fun _ _ _ => False) Q Ktr (fetch ()) t := by
  intro HPC Hal Htr
  subst HPC
  have Hb0 := bit0ClearOfAligned4 _ Hal
  have Hb1 := bit1ClearOfAligned4 _ Hal
  have Hzi := execACurrentlyEnabledZiccif (tm t t)
  unfold fetch
  apply FECCatchEarlyReturn
  ax_spin_va4_go
  simp only [Hb0, Bool.false_eq_true, ↓reduceIte]
  ax_spin_va4_go
  simp only [Hb1, Bool.false_eq_true, ↓reduceIte]
  ax_spin_va4_go
  simp only [Hal, ↓reduceIte]
  ax_spin_va4_go
  refine AxSpinVA3.fRUse (μ := t) rfFCurrentlyEnabledZiccif Hzi ?_
  ax_spin_va4_go
  refine AxSpinVA3.fRLift (P := fun _ _ _ => False) ?_ (fun _ _ _ h => h.elim)
  unfold fetch_bytes
  apply FECCatchEarlyReturn
  ax_spin_va4_go
  refine AxSpinVA3.fRLift Htr ?_
  rintro Ks' r t' ⟨rfl, Hmr⟩
  ax_spin_va4_go
  exact AxSpinVA3.fRLift (P := fun _ _ _ => False) (Hmr _) (fun _ _ _ h => h.elim)

/-- Rocq `F_fetch_2` (bit facts as premises). -/
theorem FFetch2 (img : Image) (va pa : BitVec 64) (Ktr : List ekey)
    (Q : List ekey → FetchResult → ExecSt → Prop) (t : ExecSt) :
    t.regs .PC = va →
    (_get_Misa_C (t.regs .misa) == 1#1) = true →
    (Sail.BitVec.access va 0 != 0#1) = false →
    (Sail.BitVec.access va 1 != 0#1) = true →
    is_aligned_vaddr (.Virtaddr va) 4 = false →
    FEC img (fun _ _ _ => False)
      (fun Ks' r t' => r = .Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw) ∧
        ∀ Q' : List ekey → Result (BitVec (8 * 2)) (physaddr × ExceptionType) → ExecSt → Prop,
          FEC img (fun _ _ _ => False) Q' Ks'
            (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr pa) 2 false false false) t')
      Ktr (translateAddr (.Virtaddr va) (.InstructionFetch ())) t →
    FEC img (fun _ _ _ => False) Q Ktr (fetch ()) t := by
  intro HPC HmisaC Hb0 Hb1 Hal4 Htr
  subst HPC
  have Hzca := execACurrentlyEnabledZca (tm t t) HmisaC
  unfold fetch
  apply FECCatchEarlyReturn
  ax_spin_va4_go
  simp only [Hb0, Bool.false_eq_true, ↓reduceIte]
  ax_spin_va4_go
  simp only [Hb1, ↓reduceIte]
  ax_spin_va4_go
  refine AxSpinVA3.fRUse (μ := t) rfFCurrentlyEnabledZca Hzca ?_
  ax_spin_va4_go
  simp only [Hal4, Bool.false_eq_true, ↓reduceIte]
  ax_spin_va4_go
  refine AxSpinVA3.fRLift (P := fun _ _ _ => False) ?_ (fun _ _ _ h => h.elim)
  unfold fetch_bytes
  apply FECCatchEarlyReturn
  ax_spin_va4_go
  refine AxSpinVA3.fRLift Htr ?_
  rintro Ks' r t' ⟨rfl, Hmr⟩
  ax_spin_va4_go
  exact AxSpinVA3.fRLift (P := fun _ _ _ => False) (Hmr _) (fun _ _ _ h => h.elim)

/-! # 3. The dispatch and the step prefix -/

/-- `dispatchInterrupt` at the regime: the demonic pin reads, `none`, no label (Rocq `F_disp`,
port of `AxSpineOk7.sptDispS`). -/
theorem FDisp (img : Image) (T : PTree) (satp0 : BitVec 64)
    (Q : List ekey → Option (InterruptType × Privilege) → ExecSt → Prop) (Ks : List ekey)
    (t : ExecSt) :
    ctrlOkS T satp0 t.regs → Q Ks none t →
    FEC img (fun _ _ _ => False) Q Ks (dispatchInterrupt (t.regs .cur_privilege)) t := by
  intro Hc HQ
  obtain ⟨Hpriv, -, Hmisa, -, -, -, -, -, HSIE, Hand0, -⟩ := Hc
  have HS := execCurrentlyEnabledS (tm t t)
  to_a HS
  have hS : (_get_Misa_S ((tm t t).regs .misa) == 1#1) = true := by
    show (_get_Misa_S (t.regs .misa) == 1#1) = true
    rw [Hmisa]; decide
  rw [hS] at HS
  rw [Hpriv]
  unfold dispatchInterrupt getPendingSet read_mip external_interrupts_pending
  ax_spin_va4_go
  refine AxSpinVA3.fFactUse (μ := t) AxSpineOk7.rfFCurrentlyEnabledS HS ?_
  ax_spin_va4_go
  refine AxSpinVA4.fFactReadPin (Or.inr rfl) fun vm => ?_
  ax_spin_va4_go
  refine AxSpinVA3.fFactUse (μ := t) AxSpineOk7.rfFCurrentlyEnabledS HS ?_
  ax_spin_va4_go
  refine AxSpinVA4.fFactReadPin (Or.inl rfl) fun vs => ?_
  ax_spin_va4_go
  have hz : (zeros : BitVec 64) = 0#64 := rfl
  simp (config := { decide := true }) only [Hand0, HSIE, hz, BitVec.and_zero, bne_self_eq_false,
    Bool.and_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  ax_spin_va4_go
  exact .fcRet _ _ _ HQ

/-- Rocq `ctrl_ok_S_minstret_inc`. -/
theorem ctrlOkSMinstretInc (T : PTree) (satp0 : BitVec 64) (t : ExecSt) (b : Bool) :
    ctrlOkS T satp0 t.regs → ctrlOkS T satp0 (t.setReg .minstret_increment b).regs := by
  intro Hc
  refine ctrlOkSAgree T satp0 t.regs _ (fun r Hin => ?_) Hc
  rw [ExecSt.setReg_regs]
  refine RegFile.set_other _ _ _ _ ?_
  intro He
  subst He
  exact absurd Hin (by decide)

/-- The step prefix (Rocq `F_riscv_step_fetch`): `try_step` → `run_hart_active` → dispatch
(`none`) → `fetch`, at the state where `minstret_increment` has been written. -/
theorem FRiscvStepFetch (img : Image) (T : PTree) (satp0 : BitVec 64) (tick : Bool)
    (Ks : List ekey) (Qf : List ekey → Unit → ExecSt → Prop) (t : ExecSt) :
    ctrlOkS T satp0 t.regs →
    (∀ b : Bool, FEC img (fun _ _ _ => False) (fun _ _ _ => False) Ks (fetch ())
      (t.setReg .minstret_increment b)) →
    FEC img QT Qf Ks (riscvStep tick) t := by
  intro Hc Hf
  unfold riscvStep
  refine AxSpinVA3.fFact (P := fun _ _ _ => False) ?_ (fun _ _ _ h => h.elim)
  unfold try_step
  dsimp only
  ax_spin_va4_go
  obtain ⟨b, Hb⟩ := execShouldIncMinstretSome (t.regs .cur_privilege) (tm t t)
  to_a Hb
  refine AxSpinVA3.fFactUse (μ := t) (rfFShouldIncMinstret _) Hb ?_
  ax_spin_va4_go
  have Hc1 := ctrlOkSMinstretInc T satp0 t b Hc
  have Hha : (t.setReg .minstret_increment b).regs .hart_state = .HART_ACTIVE () := Hc1.2.1
  refine AxSpinVA3.fFact (P := fun _ _ _ => False) ?_ (fun _ _ _ h => h.elim)
  ax_spin_va4_go
  rw [Hha]
  dsimp only
  unfold run_hart_active
  apply FECCatchEarlyReturn
  ax_spin_va4_go
  refine AxSpinVA3.fRLift (P := fun Ks' r t' => Ks' = Ks ∧ r = none ∧
      t' = t.setReg .minstret_increment b)
    (FDisp img T satp0 _ Ks _ Hc1 ⟨rfl, rfl, rfl⟩) ?_
  rintro Ks' r t' ⟨rfl, rfl, rfl⟩
  ax_spin_va4_go
  exact AxSpinVA3.fRLift (P := fun _ _ _ => False) (Hf b) (fun _ _ _ h => h.elim)

/-! # 4. THE THEOREM -/

/-- Rocq `fetchable`: the translation premises of a mapped, fetchable VA. -/
def fetchable (σi : ExecSt) (T : PTree) (va w pa p2 p1 : BitVec 64) : Prop :=
  AxPtProt.ptreeMaps T (WeakKpt.svpnOf va) p2 p1 w ∧
  WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr2 T (WeakKpt.svpnOf va)) p2 ∧
  WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr1 p2 (WeakKpt.svpnOf va)) p1 ∧
  WeakWalkEff.ptSlotMem σi (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf va)) w ∧
  (∀ mxr do_sum : Bool, pteCheckOk (.InstructionFetch ()) .Supervisor mxr do_sum w) ∧
  update_PTE_Bits w (.InstructionFetch ()) = none ∧
  ptePbmt0 w ∧
  (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false ∧
  zero_extend (m := 64) (ppn0 w +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0) = pa

section thm
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
  (Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
  (Hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
  (Hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)

include Hmode Hasid Hppn in
/-- Rocq `F_translate_fetch` (deviation 1: the end key is `ENf`). -/
theorem FTranslateFetch (va w pa p2 p1 : BitVec 64) (nb : Nat) (t1 : ExecSt) :
    ctrlOkS T satp0 t1.regs → fetchable σi T va w pa p2 p1 →
    (∀ (t' : ExecSt)
       (Q' : List ekey → Result (BitVec (8 * nb)) (physaddr × ExceptionType) → ExecSt → Prop),
       ctrlOkS T satp0 t'.regs →
       FEC (imgOf σi) (fun _ _ _ => False) Q' [.ENf (paZ pa, nb)]
         (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr pa) nb false false false) t') →
    FEC (imgOf σi) (fun _ _ _ => False)
      (fun Ks' r t' => r = .Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw) ∧
        ∀ Q' : List ekey → Result (BitVec (8 * nb)) (physaddr × ExceptionType) → ExecSt → Prop,
          FEC (imgOf σi) (fun _ _ _ => False) Q' Ks'
            (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr pa) nb false false false) t')
      (walkKeys T (t1.regs .tlb) (WeakKpt.svpnOf va) p2 p1 ++ [.ENf (paZ pa, nb)])
      (translateAddr (.Virtaddr va) (.InstructionFetch ())) t1 := by
  intro Hc ⟨Hmaps, Hs2, Hs1, Hs0, Hchk, Hupd, Hpb, Hcanon, Hout⟩ Hend
  have Hc0 := Hc
  obtain ⟨Hpriv, -, Hmisa, Hmenv, Hhtif, -, Hpma, Hms, -, -, Hsatp, Htlbx, Hpmp⟩ := Hc0
  obtain ⟨-, HSXL, -⟩ := Hms
  refine FTranslateAddrImg σi (.InstructionFetch ()) .Supervisor T.base va w pa satp0 T p2 p1 _ _ t1
    Hchk Hupd Hcanon Hout Hpb rfl Hmaps Htlbx Hs2 Hs1 Hs0 Hmisa Hmenv Hhtif Hpriv
    (execTranslationModeSSv39 satp0 (tm σi t1) HSXL Hsatp Hmode)
    (execEffectivePrivilegeFetch _ .Supervisor (tm σi t1))
    (execIsShadowStackFetch (tm σi t1)) Hsatp Hppn Hasid Hpmp Hpma (by simp) ?_ ?_
  · intro _
    exact ⟨rfl, fun Q' => Hend t1 Q' Hc⟩
  · intro _
    refine ⟨rfl, fun Q' => Hend _ Q' ?_⟩
    exact ctrlOkSTlbFill T satp0 t1.regs _ p2 p1 w (WeakKpt.svpnOf va) Hc Hmaps rfl

include Hmode Hasid Hppn in
/-- THE ARBITRARY-VA FETCH CHAIN, 4-aligned VA (Rocq `chain_fetch_mapped_4`; deviation 1). -/
theorem chainFetchMapped4 (t : ExecSt) (va w pa p2 p1 : BitVec 64) :
    ctrlOkS T satp0 t.regs → t.regs .PC = va →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    fetchable σi T va w pa p2 p1 →
    inRam pa 4 → is_aligned_paddr (.Physaddr pa) 4 = true →
    imgBytes (imgOf σi) (paZ pa) 4 = none →
    BFEC (imgOf σi) 1
      (walkKeys T (t.regs .tlb) (WeakKpt.svpnOf va) p2 p1 ++ [.ENf (paZ pa, 4)]) t := by
  intro Hc HPC Hal Hfa Hram Halp Hv tick
  refine FRiscvStepFetch _ T satp0 tick _ _ t Hc ?_
  intro b
  have Hc1 := ctrlOkSMinstretInc T satp0 t b Hc
  have Htlb : (t.setReg .minstret_increment b).regs .tlb = t.regs .tlb := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]
  have HPC1 : (t.setReg .minstret_increment b).regs .PC = va := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC
  refine FFetch4 _ va pa _ _ _ HPC1 Hal ?_
  rw [← Htlb]
  refine FTranslateFetch σi T satp0 Hmode Hasid Hppn va w pa p2 p1 4 _ Hc1 Hfa ?_
  intro t' Q' Hc'
  exact fetchEnd4 _ T satp0 pa Q' t' Hc' Hram Halp Hv

include Hmode Hasid Hppn in
/-- ... and 2-aligned, not 4-aligned (Rocq `chain_fetch_mapped_2`; bit facts as premises). -/
theorem chainFetchMapped2 (t : ExecSt) (va w pa p2 p1 : BitVec 64) :
    ctrlOkS T satp0 t.regs → t.regs .PC = va →
    (Sail.BitVec.access va 0 != 0#1) = false →
    (Sail.BitVec.access va 1 != 0#1) = true →
    is_aligned_vaddr (.Virtaddr va) 4 = false →
    fetchable σi T va w pa p2 p1 →
    inRam pa 2 → is_aligned_paddr (.Physaddr pa) 2 = true →
    imgBytes (imgOf σi) (paZ pa) 2 = none →
    BFEC (imgOf σi) 1
      (walkKeys T (t.regs .tlb) (WeakKpt.svpnOf va) p2 p1 ++ [.ENf (paZ pa, 2)]) t := by
  intro Hc HPC Hb0 Hb1 Hal4 Hfa Hram Halp Hv tick
  refine FRiscvStepFetch _ T satp0 tick _ _ t Hc ?_
  intro b
  have Hc1 := ctrlOkSMinstretInc T satp0 t b Hc
  have Htlb : (t.setReg .minstret_increment b).regs .tlb = t.regs .tlb := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]
  have HPC1 : (t.setReg .minstret_increment b).regs .PC = va := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC
  have HmC : (_get_Misa_C ((t.setReg .minstret_increment b).regs .misa) == 1#1) = true := by
    rw [Hc1.2.2.1]; decide
  refine FFetch2 _ va pa _ _ _ HPC1 HmC Hb0 Hb1 Hal4 ?_
  rw [← Htlb]
  refine FTranslateFetch σi T satp0 Hmode Hasid Hppn va w pa p2 p1 2 _ Hc1 Hfa ?_
  intro t' Q' Hc'
  exact fetchEnd2 _ T satp0 pa Q' t' Hc' Hram Halp Hv

include Hmode Hasid Hppn in
/-- THE FIRST LABEL at the boundary node (i = 0 of the chain; Rocq `first_label_mapped_4`): the
fetch end (`ENf`, deviation 1) on a TLB hit, the root-slot walker read on a miss. -/
theorem firstLabelMapped4 (t : ExecSt) (va w pa p2 p1 : BitVec 64) (cpu : CPU) (rs : RegFile)
    (ib : Ibch) (k : Nat) :
    ctrlOkS T satp0 t.regs → t.regs .PC = va →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    fetchable σi T va w pa p2 p1 →
    inRam pa 4 → is_aligned_paddr (.Physaddr pa) 4 = true →
    imgBytes (imgOf σi) (paZ pa) 4 = none →
    regsAgree AxRunClose.pinReg rs t.regs →
    firstEv (WeakAxRealize.fetchPin (imgOf σi))
      (FOf (Eq (if tlbHitb (t.regs .tlb) (WeakKpt.svpnOf va) then .ENf (paZ pa, 4)
        else wkey (AxPtProt.ptAddr2 T (WeakKpt.svpnOf va)))))
      ⟨.PHart cpu (.pure ()) rs none ib, k⟩ := by
  intro Hc HPC Hal Hfa Hram Halp Hv Hag
  refine chainFirst (imgOf σi) _ _ 0 _ _ k
    (hthrBoundary (imgOf σi) _ _ t cpu rs ib
      (chainFetchMapped4 σi T satp0 Hmode Hasid Hppn t va w pa p2 p1 Hc HPC Hal Hfa Hram Halp Hv)
      Hag) (.irRefl _) ?_
  unfold walkKeys
  cases tlbHitb (t.regs .tlb) (WeakKpt.svpnOf va) <;> rfl

end thm

/-! # 5. (Lean-only, deviation 1) the in-image fetch: the walk prefix -/

section img
variable (img : Image)

local notation "FC" => FEC img

/-- (Lean-only) The fetch's RAM read with image bytes: the pinned administrative step,
continuing with the image word. -/
theorem AxSpinVA4.fReadRamFetchGo (w : Nat)
    (QE : List ekey → Sail.Error exception → ExecSt → Prop)
    (Q : List ekey → (BitVec (8 * w) × Unit) → ExecSt → Prop) (pa : BitVec 64) (Ks : List ekey)
    (vs : List (BitVec 8)) (t : ExecSt) :
    devAddr pa = false → imgBytes img (paZ pa) w = some vs →
    Q Ks (rrv w vs, default_meta) t →
    FC QE Q Ks (read_ram .Read_ifetch (.Physaddr pa) w false) t := by
  intro hdev hv hq
  simp only [read_ram, PreSail.sail_mem_read, PreSail.emit, pure_bind]
  exact FEC.fcIf (img := img) Ks w 64
    { access_kind := .AK_ifetch (), va := none, pa := pa, translation := (), size := w,
      tag := false } _ t vs hdev rfl hv (.fcRet _ _ _ hq)

section cmr
variable (μ : ExecSt) (pbmt : page_based_mem_type) (w : Nat) (pa : BitVec 64) (t : ExecSt)
variable (Hw : vmemWidth w)
  (Hcp : execA (check_pma_with_pmp_priority (.InstructionFetch ()) pbmt .Supervisor (.Physaddr pa)
    w false) (tm μ t) = some (.Ok pmaOkAligned, tm μ t))
  (Hpmp : execA (pmpCheck (.Physaddr pa) w (.InstructionFetch ()) .Supervisor) (tm μ t)
    = some (none, tm μ t))
  (Hmmio : execA (within_mmio_readable (.Physaddr pa) w) (tm μ t) = some (false, tm μ t))
  (Hdev : devAddr pa = false)

include Hw Hcp Hpmp Hmmio Hdev in
/-- (Lean-only) `checked_mem_read` of a fetch with image bytes (`FCheckedMemReadGo` at the
fetch): no key, the image word. -/
theorem AxSpinVA4.fCheckedMemReadFetchGo
    (Q : List ekey → Result (BitVec (8 * w) × Unit) (physaddr × ExceptionType) → ExecSt → Prop)
    (Ks : List ekey) (vs : List (BitVec 8)) :
    imgBytes img (paZ pa) w = some vs →
    Q Ks (.Ok (rrv w vs, default_meta)) t →
    FC (fun _ _ _ => False) Q Ks
      (checked_mem_read (.InstructionFetch ()) pbmt .Supervisor (.Physaddr pa) w false false false
        false) t := by
  intro hv hq
  unfold checked_mem_read
  apply FECCatchEarlyReturn
  refine AxSpinVA3.fRAssoc ?_
  refine AxSpinVA3.fRUse (μ := μ) (rfFCheckPmaWithPmpPriority _ _ _ _ _ _) Hcp ?_
  refine AxSpinVA3.fRPureBind ?_
  refine AxSpinVA3.fRUse (μ := μ) (a := ((1 : Int), (w : Int))) (rfFSplitMisaligned _ _ _ _) rfl ?_
  simp only [misaligned_order, sys_misaligned_order_decreasing, ↓reduceIte, Bool.false_eq_true,
    Int.reduceSub, Int.toNat_zero]
  rcases Hw with rfl | rfl | rfl | rfl
  all_goals
    try simp only [read_kind_of_flags]
    first
      | refine AxSpinVA3.fRUse (μ := μ) (rfFReadKindOfFlags _ _ _) rfl ?_
      | refine AxSpinVA3.fRPureBind ?_
    refine AxSpinVA3.fRAssoc ?_
    refine AxSpinVA3.fRBind _ _ _ _ _ _ ?_
    refine FECUntilMT1 img _ _ _ _ _ _ _ ?_
    refine AxSpinVA3.fRUse (μ := μ) (by trivial) rfl ?_
    simp only [bits_of_physaddr, Int.cast_ofNat_Int, Int.zero_mul, addIntZero, Int.toNat_one,
      Int.mul_one]
    refine AxSpinVA3.fRUse (μ := μ) (rfFPmpCheck _ _ _ _) Hpmp ?_
    dsimp only
    refine AxSpinVA3.fRUse (μ := μ) (rfFWithinMmioReadable _ _) Hmmio ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine AxSpinVA3.fRAssoc ?_
    refine AxSpinVA3.fRLift
      (P := fun Ks' x t' => Ks' = Ks ∧ x = (rrv _ vs, default_meta) ∧ t' = t)
      (AxSpinVA4.fReadRamFetchGo img _ _ _ pa Ks vs t Hdev hv ⟨rfl, rfl, rfl⟩) ?_
    rintro Ks' x t' ⟨rfl, rfl, rfl⟩
    refine AxSpinVA3.fRPureBind ?_
    refine AxSpinVA3.fRPure ?_
    refine AxSpinVA3.fRPure ⟨rfl, ?_⟩
    refine AxSpinVA3.fRPureBind ?_
    refine AxSpinVA3.fRPure ?_
    refine AxDataX.substArg (fun v => Q _ v _) ?_ hq
    simp only [Result.Ok.injEq, Prod.mk.injEq, and_true, Nat.reduceMul, Int.reduceMul,
      Int.reduceAdd, Int.reduceSub, Int.reduceToNat, BitVec.setWidth_eq]
    try simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.updateSubrange]
    try bv_decide
end cmr

/-- (Lean-only) The fetch's `mem_read` with image bytes (`FMemReadFetchEnd`'s in-image twin). -/
theorem AxSpinVA4.fMemReadFetchGo (μ : ExecSt) (n : Nat) (pbmt : page_based_mem_type)
    (addr : BitVec 64)
    (Q : List ekey → Result (BitVec (8 * n)) (physaddr × ExceptionType) → ExecSt → Prop)
    (Ks : List ekey) (vs : List (BitVec 8)) (t : ExecSt) :
    vmemWidth n →
    execA (check_pma_with_pmp_priority (.InstructionFetch ()) pbmt .Supervisor (.Physaddr addr) n
      false) (tm μ t) = some (.Ok pmaOkAligned, tm μ t) →
    execA (pmpCheck (.Physaddr addr) n (.InstructionFetch ()) .Supervisor) (tm μ t)
      = some (none, tm μ t) →
    execA (within_mmio_readable (.Physaddr addr) n) (tm μ t) = some (false, tm μ t) →
    devAddr addr = false →
    imgBytes img (paZ addr) n = some vs →
    t.regs .cur_privilege = .Supervisor →
    Q Ks (.Ok (rrv n vs)) t →
    FC (fun _ _ _ => False) Q Ks
      (mem_read (.InstructionFetch ()) pbmt (.Physaddr addr) n false false false) t := by
  intro Hn Hcp Hpmp Hmmio Hdev Hv Hpriv HQ
  have Hep := execEffectivePrivilegeFetch ((tm μ t).regs .mstatus) ((tm μ t).regs .cur_privilege)
    (tm μ t)
  to_a Hep
  unfold mem_read
  ax_spin_va4_go
  refine AxSpinVA3.fFactUse (μ := μ) (rfFEffectivePrivilege _ _ _) Hep ?_
  rw [show (tm μ t).regs .cur_privilege = .Supervisor from Hpriv]
  unfold mem_read_priv mem_read_priv_meta
  dsimp only
  refine AxSpinVA3.fFactAssoc ?_
  refine AxSpinVA3.fFact (P := fun Ks' x t' => Ks' = Ks ∧ x = .Ok (rrv n vs, default_meta) ∧
      t' = t)
    (AxSpinVA4.fCheckedMemReadFetchGo img μ pbmt n addr t Hn Hcp Hpmp Hmmio Hdev _ Ks vs Hv
      ⟨rfl, rfl, rfl⟩) ?_
  rintro Ks' x t' ⟨rfl, rfl, rfl⟩
  exact .fcRet _ _ _ HQ

end img

/-- (Lean-only) The fetch result of a fetched 4-byte word. -/
def AxSpinVA4.fetchRes (w : BitVec 32) : FetchResult :=
  if isRVC (Sail.BitVec.extractLsb w 15 0) then .F_RVC (Sail.BitVec.extractLsb w 15 0)
  else .F_Base w

/-- (Lean-only) `FFetch4` with the fetch IN the image: the chain is the translation's, the
result the image word's (no key for the fetch). -/
theorem AxSpinVA4.fetchGo4 (img : Image) (va pa : BitVec 64) (vs : List (BitVec 8))
    (Ktr : List ekey) (Q : List ekey → FetchResult → ExecSt → Prop) (t : ExecSt) :
    t.regs .PC = va →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    FEC img (fun _ _ _ => False)
      (fun Ks' r t' => r = .Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw) ∧
        Q Ks' (AxSpinVA4.fetchRes (rrv 4 vs)) t' ∧
        ∀ Q' : List ekey → Result (BitVec (8 * 4)) (physaddr × ExceptionType) → ExecSt → Prop,
          Q' Ks' (.Ok (rrv 4 vs)) t' →
          FEC img (fun _ _ _ => False) Q' Ks'
            (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr pa) 4 false false false) t')
      Ktr (translateAddr (.Virtaddr va) (.InstructionFetch ())) t →
    FEC img (fun _ _ _ => False) Q Ktr (fetch ()) t := by
  intro HPC Hal Htr
  subst HPC
  have Hb0 := bit0ClearOfAligned4 _ Hal
  have Hb1 := bit1ClearOfAligned4 _ Hal
  have Hzi := execACurrentlyEnabledZiccif (tm t t)
  unfold fetch
  apply FECCatchEarlyReturn
  ax_spin_va4_go
  simp only [Hb0, Bool.false_eq_true, ↓reduceIte]
  ax_spin_va4_go
  simp only [Hb1, Bool.false_eq_true, ↓reduceIte]
  ax_spin_va4_go
  simp only [Hal, ↓reduceIte]
  ax_spin_va4_go
  refine AxSpinVA3.fRUse (μ := t) rfFCurrentlyEnabledZiccif Hzi ?_
  ax_spin_va4_go
  refine AxSpinVA3.fRLift (P := fun Ks' x t' => x = .FetchBytes_Success (rrv 4 vs) ∧
      Q Ks' (AxSpinVA4.fetchRes (rrv 4 vs)) t') ?_ ?_
  · unfold fetch_bytes
    apply FECCatchEarlyReturn
    ax_spin_va4_go
    refine AxSpinVA3.fRLift Htr ?_
    rintro Ks' r t' ⟨rfl, HQ, Hmr⟩
    ax_spin_va4_go
    refine AxSpinVA3.fRLift (P := fun Ks'' x t'' => Ks'' = Ks' ∧ x = .Ok (rrv 4 vs) ∧ t'' = t')
      (Hmr _ ⟨rfl, rfl, rfl⟩) ?_
    rintro Ks'' x t'' ⟨rfl, rfl, rfl⟩
    ax_spin_va4_go
    exact .fcRet _ _ _ ⟨rfl, HQ⟩
  · rintro Ks' x t' ⟨rfl, HQ⟩
    ax_spin_va4_go
    unfold AxSpinVA4.fetchRes at HQ
    cases h : isRVC (Sail.BitVec.extractLsb (rrv 4 vs) 15 0) <;>
      simp only [h, Bool.false_eq_true, ↓reduceIte] at HQ ⊢ <;> exact .fcRet _ _ _ HQ

/-- (Lean-only) the in-image fetch read from the regime (`fetchEnd4`'s twin). -/
theorem AxSpinVA4.fetchGoAt4 (img : Image) (T : PTree) (satp0 : BitVec 64) (pa : BitVec 64)
    (Q : List ekey → Result (BitVec (8 * 4)) (physaddr × ExceptionType) → ExecSt → Prop)
    (Ks : List ekey) (vs : List (BitVec 8)) (t : ExecSt) :
    ctrlOkS T satp0 t.regs → inRam pa 4 → is_aligned_paddr (.Physaddr pa) 4 = true →
    imgBytes img (paZ pa) 4 = some vs → Q Ks (.Ok (rrv 4 vs)) t →
    FEC img (fun _ _ _ => False) Q Ks
      (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr pa) 4 false false false) t := by
  intro Hc Hram Halp Hv HQ
  have Hc0 := Hc
  obtain ⟨Hpriv, -, -, -, -, -, -, -, -, -, -, -, HA, Hord, HX, -, -⟩ := Hc0
  obtain ⟨region, Hrange, Hm, Hx, Hcl, Hsig, Hh, Hdev, -⟩ :=
    ramFetchFacts T satp0 (tm t t) pa 4 Hc (by decide) (by decide) (by decide) Hram
  have Hpma := execPmaCheckRam pa .PBMT_PMA region (tm t t) Hm Halp Hx
  have Hcp : exec (check_pma_with_pmp_priority (.InstructionFetch ()) .PBMT_PMA .Supervisor
      (.Physaddr pa) 4 false) (tm t t) = some (.Ok pmaOkAligned, tm t t) := by
    unfold check_pma_with_pmp_priority
    exec_run [Hpma]
  to_a Hcp
  have Hpmp := execPmpCheckSupervisorGrant pa 4 (tm t t) HA Hord Hrange HX
  to_a Hpmp
  have Hmmio := execAMmioFalse pa 4 (tm t t) Hcl Hsig Hh
  exact AxSpinVA4.fMemReadFetchGo img t 4 .PBMT_PMA pa Q Ks vs t (by simp [vmemWidth]) Hcp Hpmp
    Hmmio Hdev Hv Hpriv HQ

/-- (Lean-only, deviation 1) THE IN-IMAGE CASE of `chainFetchMapped4`, at `fetch ()`: a 4-aligned
mapped VA whose fetch IS in the image — the chain gains exactly `walkKeys` (the fetch is the
pinned administrative step, no key), and the continuation gets the image word's fetch result at
a regime state that differs from `t` at most in the TLB. -/
theorem AxSpinVA4.fetchMappedImg4 (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (Hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (Hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (t : ExecSt) (va w pa p2 p1 : BitVec 64) (vs : List (BitVec 8)) (Ks : List ekey)
    (Q : List ekey → FetchResult → ExecSt → Prop) :
    ctrlOkS T satp0 t.regs → t.regs .PC = va →
    is_aligned_vaddr (.Virtaddr va) 4 = true →
    fetchable σi T va w pa p2 p1 →
    inRam pa 4 → is_aligned_paddr (.Physaddr pa) 4 = true →
    imgBytes (imgOf σi) (paZ pa) 4 = some vs → Ks ≠ [] →
    (∀ t' : ExecSt, ctrlOkS T satp0 t'.regs → (∀ r, r ≠ .tlb → t'.regs r = t.regs r) →
      t'.mem = t.mem → t'.dev = t.dev → Q Ks (AxSpinVA4.fetchRes (rrv 4 vs)) t') →
    FEC (imgOf σi) (fun _ _ _ => False) Q
      (walkKeys T (t.regs .tlb) (WeakKpt.svpnOf va) p2 p1 ++ Ks) (fetch ()) t := by
  intro Hc HPC Hal ⟨Hmaps, Hs2, Hs1, Hs0, Hchk, Hupd, Hpb, Hcanon, Hout⟩ Hram Halp Hv HKs HQ
  have Hc0 := Hc
  obtain ⟨Hpriv, -, Hmisa, Hmenv, Hhtif, -, Hpma, Hms, -, -, Hsatp, Htlbx, Hpmp⟩ := Hc0
  obtain ⟨-, HSXL, -⟩ := Hms
  refine AxSpinVA4.fetchGo4 _ va pa vs _ Q t HPC Hal ?_
  refine FTranslateAddrImg σi (.InstructionFetch ()) .Supervisor T.base va w pa satp0 T p2 p1 _ _ t
    Hchk Hupd Hcanon Hout Hpb rfl Hmaps Htlbx Hs2 Hs1 Hs0 Hmisa Hmenv Hhtif Hpriv
    (execTranslationModeSSv39 satp0 (tm σi t) HSXL Hsatp Hmode)
    (execEffectivePrivilegeFetch _ .Supervisor (tm σi t))
    (execIsShadowStackFetch (tm σi t)) Hsatp Hppn Hasid Hpmp Hpma HKs ?_ ?_
  · intro _
    exact ⟨rfl, HQ t Hc (fun _ _ => rfl) rfl rfl,
      fun Q' hq => AxSpinVA4.fetchGoAt4 _ T satp0 pa Q' Ks vs t Hc Hram Halp Hv hq⟩
  · intro _
    have Hc' := ctrlOkSTlbFill T satp0 t.regs _ p2 p1 w (WeakKpt.svpnOf va) Hc Hmaps rfl
    refine ⟨rfl, HQ _ Hc' (fun r hr => ?_) rfl rfl,
      fun Q' hq => AxSpinVA4.fetchGoAt4 _ T satp0 pa Q' Ks vs _ Hc' Hram Halp Hv hq⟩
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ hr]

end Weak
