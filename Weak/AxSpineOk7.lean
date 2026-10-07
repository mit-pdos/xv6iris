/-
Weak: **the remaining `SpineOkT` fields at the S-mode kernel regime, and the assembled
`spineOkTS`.**

Rocq: `iris/AxSpineOk7.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`EvAOfRfF`: a register-only (`rfF`) tree with an SC `exec` fact is an `EvA` fact at ANY image (no
memory node on any branch).  The cheap fields (`sptSeipS`/`sptHartS`/`sptFrameS`: `ctrlOkS` only
reads `ctrlRegs`, none of which is a pin or `ctrlFree`; `sptIncS`/`sptZcaS`: SC exec lemmas +
`rfF`; `sptLpadS`: `AxSymEngine2.spLpadOf`); `sptDispS`: `dispatchInterrupt Supervisor` replayed
in `EvA` with the demonic pin reads (`read_mip` → `external_interrupts_pending`): SIE = 0 kills
the S arm, `mie ∧ ¬mideleg = 0` zeroes the M arm, whatever the pins answer; `sptTickS`:
`tick_clock` writes only `mcycle`, `mtime`, `mip` (`tickPost`).  `spineOkTS`: every `SpineOkT`
field at `imgS σi` / `ctrlOkS T satp0` / `textAtS σi T`, from the three static satp facts.

## Deviations from Rocq

1. All of `AxSpineOk6`'s spelling deviations (`mstate` ↦ `ExecSt`, `register_lookup r rs` ↦
   `rs r`, `register_set` ↦ `RegFile.set`, `eq_vec` ↦ `==`, the `satp0` hypotheses in
   `AxSpineOk4` deviation 7's shapes); `seip_reg` ↦ `AxRunClose.pinReg` (`ctrlRegsNotSeip`
   excludes both pins; the Lean model's `read_mip` reads `sig_meip` then `sig_seip`, both
   answered demonically in `sptDispS`/`sptTickS`).
2. TACTICS: Rocq's Ltacs `nseip`, `rfEvA`, `ev_step`, `ev_go`, `ev_use`, `ne_solve`, `tick_fin`
   are not redeclared: `AxSymEngine2`'s kit (`ax_sym2_ev_go`, `evFactUse`, `evFactQ`) plus the
   Lean-only `AxSpineOk7.evFactReadPin` (demonic pin read), `AxSpineOk7.evCurS`/`evSstc`
   (`EvAOfRfF` instances) and `AxSpineOk7.csrMip` (`csr_name_write_callback "mip" v = pure ()`,
   by evaluation — Rocq's `vm_compute` of `csr_name_map_backwards`).  `and_boolM`/`or_boolM`
   do not exist in the Lean model (plain `&&`/`||`).
3. `EvAOfRfF`: lean-sail's `choose`/`readRam`/`writeRam` (allowed by `rfF`) are discharged by
   `exec` being stuck there; failure nodes likewise.
4. `ctrlRegsNotFree`: the GPR disjunct of `ctrlFree` is `r ∈ uxaGprs` (`AxSymEngine2`
   deviation 5), decided over the two lists.
5. Lean `tick_clock`'s `clint_dispatch` also writes `mip` from `stimecmp` under Sstc/STCE and
   re-reads both pins; the post is unchanged (only `mcycle`/`mtime`/`mip` written).
6. Section variables `σi T satp0` are explicit arguments (each declaration takes those it uses);
   the `fields` section's `img`/`ctrl_ok`/`EvM` notations are unfolded.

**Rocq → Lean name map.**  `EvA_of_rfF` `EvAOfRfF`, `ctrl_regs_not_seip` `ctrlRegsNotSeip`,
`spt_seip_S` `sptSeipS`, `spt_hart_S` `sptHartS`, `ctrl_regs_not_free` `ctrlRegsNotFree`,
`spt_frame_S` `sptFrameS`, `spt_inc_S` `sptIncS`, `spt_zca_S` `sptZcaS`, `spt_lpad_S`
`sptLpadS`, `spt_disp_S` `sptDispS`, `tick_post` `tickPost`, `spt_tick_S` `sptTickS`,
`SpineOkT_S` `spineOkTS`.  None is in the duplicated-name table.  Lean-only (file-qualified):
`AxSpineOk7.rfFCurrentlyEnabledS`, `AxSpineOk7.rfFCurrentlyEnabledSstc`,
`AxSpineOk7.rfFShouldIncMcycle`, `AxSpineOk7.csrMip`, `AxSpineOk7.evCurS`, `AxSpineOk7.evSstc`,
`AxSpineOk7.evFactReadPin`.

**Dropped:** the Ltacs (deviation 2).  Rocq 13 lemmas + 7 Ltacs; Lean 13 + 7 Lean-only.
**Not ported:** the `Print Assumptions` line (the lint's axiom check covers it).
-/
import Weak.AxSpineOk6
import Weak.ExecSC7

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- Rocq `EvA_of_rfF`: a register-only (`rfF`) tree with an SC `exec` fact is an `EvA` fact at
ANY image. -/
theorem EvAOfRfF (img : Image) {X : Type} (m : SailM X) :
    rfF m → ∀ t x t', exec m t = some (x, t') →
      EvA img (fun (_ : Sail.Error exception) _ => False) (fun x' t'' => x' = x ∧ t'' = t') m t := by
  induction m with
  | pure y =>
    intro _ t x t' he
    simp only [exec, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact .evRet _ _ ⟨rfl, rfl⟩
  | impure call k ih =>
    intro hrf t x t' he
    cases call with
    | error e => cases he
    | ok o =>
      cases o
      case regRead r =>
        obtain ⟨hp, hk⟩ := hrf
        exact .evRd r k t (fun h => absurd h hp) (fun _ => ih _ (hk _) t x t' he)
      case regWrite r v =>
        obtain ⟨hp, hk⟩ := hrf
        exact .evWr r v k t hp (ih _ hk _ x t' he)
      case instrAnnounce n w =>
        obtain ⟨hp, hk⟩ := hrf
        exact .evIa n w k t hp (ih _ hk t x t' he)
      case branchAnnounce n a => exact .evBa n a k t (ih _ hrf t x t' he)
      case cacheOp c => exact .evCo c k t (ih _ hrf t x t' he)
      case tlbi c => exact .evTl c k t (ih _ hrf t x t' he)
      case takeException c => exact .evTe c k t (ih _ hrf t x t' he)
      case returnException c => exact .evRx c k t (ih _ hrf t x t' he)
      case translationStart c => exact .evTs c k t (ih _ hrf t x t' he)
      case translationEnd c => exact .evTx c k t (ih _ hrf t x t' he)
      case cycleCount => exact .evCc k t (ih _ hrf t x t' he)
      case message c => exact .evMsg c k t (ih _ hrf t x t' he)
      case getCycleCount => exact .evGcc k t (ih _ hrf t x t' he)
      case memRead => exact hrf.elim
      case memWrite => exact hrf.elim
      case barrier => exact hrf.elim
      case choose => cases he
      case readRam => cases he
      case writeRam => cases he

/-! ### (Lean-only) callee footprints and `EvA` facts -/

theorem AxSpineOk7.rfFCurrentlyEnabledS : rfF (currentlyEnabled .Ext_S) := by rff_auto
theorem AxSpineOk7.rfFCurrentlyEnabledSstc : rfF (currentlyEnabled .Ext_Sstc) := by rff_auto
theorem AxSpineOk7.rfFShouldIncMcycle (p : Privilege) : rfF (should_inc_mcycle p) := by rff_auto

theorem AxSpineOk7.csrMip (v : BitVec 64) : csr_name_write_callback "mip" v = pure () := rfl

theorem AxSpineOk7.evCurS (img : Image) (s : ExecSt) :
    EvA img (fun (_ : Sail.Error exception) _ => False)
      (fun x t' => x = (_get_Misa_S (s.regs .misa) == 1#1) ∧ t' = s) (currentlyEnabled .Ext_S) s :=
  EvAOfRfF img _ AxSpineOk7.rfFCurrentlyEnabledS s _ s (execCurrentlyEnabledS s)

theorem AxSpineOk7.evSstc (img : Image) (s : ExecSt) :
    EvA img (fun (_ : Sail.Error exception) _ => False)
      (fun x t' => x = true ∧ t' = s) (currentlyEnabled .Ext_Sstc) s :=
  EvAOfRfF img _ AxSpineOk7.rfFCurrentlyEnabledSstc s _ s (execCurrentlyEnabledSstc s)

/-- (Lean-only) a demonic pin read (Rocq: `ev_rd` with the pin arm). -/
theorem AxSpineOk7.evFactReadPin {img : Image} {QE : Sail.Error exception → ExecSt → Prop}
    {Y : Type} {Q : Y → ExecSt → Prop} {r : Register} {f : RegisterType r → SailM Y} {t : ExecSt}
    (hr : AxRunClose.pinReg r) (H : ∀ v, EvA img QE Q (f v) t) :
    EvA img QE Q (readReg r >>= f) t :=
  EvABind img QE Q _ f t (.evRd r _ t (fun _ v => .evRet _ _ (H v)) (fun hn => absurd hr hn))

section fields
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)

/-- Rocq `ctrl_regs_not_seip`. -/
theorem ctrlRegsNotSeip (r : Register) : r ∈ ctrlRegs → ¬ AxRunClose.pinReg r := by
  intro hin hp
  rcases hp with rfl | rfl <;> exact absurd hin (by decide)

/-- Rocq `spt_seip_S`. -/
theorem sptSeipS (rs rs' : RegFile) :
    ctrlOkS T satp0 rs → regsAgree AxRunClose.pinReg rs' rs → ctrlOkS T satp0 rs' :=
  fun hc hag => ctrlOkSAgree T satp0 rs rs' (fun r hin => hag r (ctrlRegsNotSeip r hin)) hc

/-- Rocq `spt_hart_S`. -/
theorem sptHartS (rs : RegFile) : ctrlOkS T satp0 rs → rs .hart_state = .HART_ACTIVE () :=
  fun hc => hc.2.1

/-- Rocq `ctrl_regs_not_free`. -/
theorem ctrlRegsNotFree (r r' : Register) : ctrlFree r → r' ∈ ctrlRegs → r' ≠ r := by
  intro hf hin e
  subst e
  rcases hf with rfl | rfl | rfl | rfl | hg
  · exact absurd hin (by decide)
  · exact absurd hin (by decide)
  · exact absurd hin (by decide)
  · exact absurd hin (by decide)
  · have h : ∀ x ∈ ctrlRegs, x ∉ uxaGprs := by decide
    exact h _ hin hg

/-- Rocq `spt_frame_S`. -/
theorem sptFrameS (rs : RegFile) (r : Register) (v : RegisterType r) :
    ctrlFree r → ctrlOkS T satp0 rs → ctrlOkS T satp0 (rs.set r v) :=
  fun hf hc => ctrlOkSAgree T satp0 rs _
    (fun r' hin => RegFile.set_other _ _ _ _ (ctrlRegsNotFree r r' hf hin)) hc

/-- Rocq `spt_inc_S`. -/
theorem sptIncS (t : ExecSt) : ctrlOkS T satp0 t.regs → ∃ b,
    EvA (imgS σi) (fun _ _ => False) (fun x t' => x = b ∧ t' = t)
      (should_inc_minstret (t.regs .cur_privilege)) t := by
  intro _
  obtain ⟨b, hb⟩ := execShouldIncMinstretSome (t.regs .cur_privilege) t
  exact ⟨b, EvAOfRfF _ _ (rfFShouldIncMinstret _) t b t hb⟩

/-- Rocq `spt_zca_S`. -/
theorem sptZcaS (t : ExecSt) : ctrlOkS T satp0 t.regs →
    EvA (imgS σi) (fun _ _ => False) (fun x t' => x = true ∧ t' = t)
      (currentlyEnabled .Ext_Zca) t := by
  intro hc
  have hm : (_get_Misa_C (t.regs .misa) == 1#1) = true := by
    rw [hc.2.2.1]; decide
  exact EvAOfRfF _ _ rfFCurrentlyEnabledZca t true t (execCurrentlyEnabledZca t hm)

/-- Rocq `spt_lpad_S`. -/
theorem sptLpadS (t : ExecSt) : ctrlOkS T satp0 t.regs →
    EvA (imgS σi) (fun _ _ => False) (fun x t' => x = false ∧ t' = t)
      (is_landing_pad_expected ()) t :=
  spLpadOf (imgS σi) (ctrlOkS T satp0) (fun _ hc => hc.2.2.2.2.2.1) t

/-- Rocq `spt_disp_S`. -/
theorem sptDispS (t : ExecSt) : ctrlOkS T satp0 t.regs →
    EvA (imgS σi) (fun _ _ => False) (fun r t' => r = none ∧ t' = t)
      (dispatchInterrupt (t.regs .cur_privilege)) t := by
  intro hc
  obtain ⟨hpriv, -, hmisa, -, -, -, -, -, hSIE, hand0, -⟩ := hc
  have hS : (_get_Misa_S (t.regs .misa) == 1#1) = true := by rw [hmisa]; decide
  have HSA : EvA (imgS σi) (fun _ _ => False) (fun x t' => x = true ∧ t' = t)
      (currentlyEnabled .Ext_S) t := by
    have h := AxSpineOk7.evCurS (imgS σi) t
    rwa [hS] at h
  rw [hpriv]
  unfold dispatchInterrupt getPendingSet read_mip external_interrupts_pending
  ax_sym2_ev_go
  refine AxSymEngine2.evFactUse HSA ?_
  ax_sym2_ev_go
  refine AxSpineOk7.evFactReadPin (Or.inr rfl) fun vm => ?_
  ax_sym2_ev_go
  refine AxSymEngine2.evFactUse HSA ?_
  ax_sym2_ev_go
  refine AxSpineOk7.evFactReadPin (Or.inl rfl) fun vs => ?_
  ax_sym2_ev_go
  have hz : (zeros : BitVec 64) = 0#64 := rfl
  simp (config := { decide := true }) only [hand0, hSIE, hz, BitVec.and_zero, bne_self_eq_false,
    Bool.and_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  ax_sym2_ev_go
  exact .evRet _ _ ⟨rfl, rfl⟩

/-- Rocq `tick_post`: `tick_clock` writes only `mcycle`, `mtime`, `mip`. -/
theorem tickPost (t t' : ExecSt) :
    (∀ r : Register, r ≠ .mcycle → r ≠ .mtime → r ≠ .mip → t'.regs r = t.regs r) →
    ctrlOkS T satp0 t.regs → ctrlOkS T satp0 t'.regs ∧ keepRegs t.regs t'.regs := by
  intro hag hc
  have hc1 : ∀ r ∈ ctrlRegs, r ≠ .mcycle ∧ r ≠ .mtime ∧ r ≠ .mip := by decide
  have hg1 : ∀ r ∈ uxaGprs, r ≠ .mcycle ∧ r ≠ .mtime ∧ r ≠ .mip := by decide
  refine ⟨ctrlOkSAgree T satp0 t.regs t'.regs (fun r hin => ?_) hc, ?_, fun z => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hc1 r hin
    exact hag r h1 h2 h3
  · exact hag _ (by decide) (by decide) (by decide)
  · refine uxaXget_congr t.regs t'.regs (fun r hr => ?_) z
    obtain ⟨h1, h2, h3⟩ := hg1 r hr
    exact hag r h1 h2 h3

/-- Rocq `spt_tick_S`. -/
theorem sptTickS (t : ExecSt) : ctrlOkS T satp0 t.regs →
    EvA (imgS σi) (fun _ _ => False)
      (fun _ t' => ctrlOkS T satp0 t'.regs ∧ keepRegs t.regs t'.regs) (tick_clock ()) t := by
  intro hc
  unfold tick_clock clint_dispatch read_mip external_interrupts_pending
  ax_sym2_ev_go
  obtain ⟨b, hb⟩ := execShouldIncMcycleSome (t.regs .cur_privilege) t
  refine AxSymEngine2.evFactUse (EvAOfRfF _ _ (AxSpineOk7.rfFShouldIncMcycle _) t b t hb) ?_
  cases b
  all_goals ax_sym2_ev_go
  all_goals refine AxSymEngine2.evFactUse (AxSpineOk7.evSstc _ _) ?_
  all_goals repeat' (ax_sym2_ev_go; first
    | (refine AxSpineOk7.evFactReadPin (Or.inr rfl) fun _ => ?_)
    | (refine AxSpineOk7.evFactReadPin (Or.inl rfl) fun _ => ?_)
    | (refine AxSymEngine2.evFactQ (AxSpineOk7.evCurS _ _) ?_; rintro _ _ ⟨rfl, rfl⟩)
    | (rw [AxSpineOk7.csrMip])
    | split)
  all_goals refine .evRet _ _ ?_
  all_goals refine tickPost T satp0 t _ ?_ hc
  all_goals intro r h1 h2 h3
  all_goals simp only [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ h1,
    RegFile.set_other _ _ _ _ h2, RegFile.set_other _ _ _ _ h3]

end fields

/-- Rocq `SpineOkT_S`: THE SPINE AT THE S-MODE KERNEL REGIME — every `SpineOkT` field, for all
states of the regime, from the three static facts about the kernel satp constant. -/
theorem spineOkTS (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base) :
    SpineOkT (imgS σi) (ctrlOkS T satp0) (textAtS σi T) :=
  ⟨sptSeipS T satp0, sptHartS T satp0, sptFrameS T satp0, sptIncS σi T satp0,
    sptDispS σi T satp0, sptFetchS σi T satp0 hmode hasid hppn, sptLpadS σi T satp0,
    sptZcaS σi T satp0, sptTickS σi T satp0⟩

end Weak
