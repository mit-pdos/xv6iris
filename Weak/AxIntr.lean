/-
Weak: **constraint B (SIE = 1) for the X engine's S-mode spine — the SIE-agnostic regime
`ctrlOkSI`, its `SpineOkT` fields, and the tick frame.**  PURE (no Iris).

Rocq: `iris/AxIntr.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 THE REGIME.  `ctrlOkSI T satp0` = `AxSpineOk6.ctrlOkS` with the SIE = 0 conjunct replaced by
`sieOk`: SIE = 0 OR stvec is in DIRECT mode (xv6: kernelvec, installed by trapinithart).  sie /
sip / mideleg are pinned as in the SC regime (`mie ∧ ¬mideleg = 0`: nothing is M-destined).
`ctrlOkSSI`: the old regime is included; `ctrlOkSIS`: at SIE = 0 it is exactly the old regime.
§2 the `SpineOkT` fields at `ctrlOkSI` (fetch / seip / hart / frame / inc / lpad / zca — the
`AxSpineOk6`/`AxSpineOk7` scripts replayed) and the tick field in the STRONGER `tickFrame` form:
every register except mcycle / mtime / mip is untouched (`sptTickFrame`, no regime needed).
The Rocq header also announces §3–§5 (split dispatch, trap arm, `SpineOkI`, `spine_cert_I`);
those live in `AxIntr2`–`AxIntr5`, not in this file.

## Deviations from Rocq

1. All of `AxSpineOk6`/`AxSpineOk7`'s spelling deviations (`mstate` ↦ `ExecSt`,
   `register_lookup r rs` ↦ `rs r`, `register_set` ↦ `RegFile.set`, `eq_vec x y = b` ↦
   `(x == y) = b`, the `satp0` hypotheses in `AxSpineOk4` deviation 7's shapes,
   `pma_allows_all` ↦ `rs .pma_regions = bootPMA`, `IntrDefs.sconf_ms_facts` ↦
   `AxSpineOk6.sconfMsFacts`, `pmp_ok` ↦ `AxSpineOk6.pmpOk`); `seip_reg` ↦ `AxRunClose.pinReg`
   (both pins: `ctrlRegsINotSeip` excludes `sig_meip` and `sig_seip`).
2. `ramFetchFactsI` takes `AxSpineOk6.ramFetchFacts`'s Lean shape (`AxSpineOk6` deviation 4):
   `inRam pa n` for `addr_is_ram pa ∧ addr_is_ram (pa_add pa k)`, no `k`, width bound
   `0 < n ≤ 16` (Rocq `1 ≤ n ≤ 4096`; the uses are n = 2, 4).
3. TACTICS: the Ltacs `nseip`, `ev_step`, `ev_go`, `ev_use` (section `tickI`) are not
   redeclared: `sptTickFrame` replays `AxSpineOk7.sptTickS`'s script (`ax_sym2_ev_go`,
   `AxSymEngine2.evFactUse`/`evFactQ`, `AxSpineOk7.evFactReadPin`/`evSstc`/`evCurS`/`csrMip`).
   Lean `tick_clock`'s `clint_dispatch` also writes `mip` from `stimecmp` and re-reads both pins
   (`AxSpineOk7` deviation 5); the frame (only mcycle / mtime / mip written) is unchanged.
4. `ctrlRegsINotFree`: the GPR disjunct of `ctrlFree` is `r ∈ uxaGprs` (`AxSymEngine2`
   deviation 5), decided over the two lists.
5. Section variables `σi T satp0` and hypotheses `Hmode Hasid Hppn` are explicit arguments (each
   declaration takes those it uses); the `img`/`ctrl_ok`/`EvM` notations are unfolded; the
   `tickI` section's `img` is an explicit argument of `sptTickFrame`.

**Rocq → Lean name map.**  `intr_on` `intrOn`, `stvec_direct` `AxIntr.stvecDirect`
(file-qualified: `MachCSL.stvecDirect` exists), `sie_ok` `sieOk`, `ctrl_regs_I` `ctrlRegsI`,
`ctrl_ok_SI` `ctrlOkSI`, `ctrl_ok_S_SI` `ctrlOkSSI`, `ctrl_ok_SI_S` `ctrlOkSIS`,
`ctrl_ok_SI_agree` `ctrlOkSIAgree`, `ram_fetch_facts_I` `ramFetchFactsI`, `ctrl_ok_SI_tlb_fill`
`ctrlOkSITlbFill`, `spt_fetch_SI` `sptFetchSI`, `ctrl_regs_I_not_seip` `ctrlRegsINotSeip`,
`spt_seip_SI` `sptSeipSI`, `spt_hart_SI` `sptHartSI`, `ctrl_regs_I_not_free`
`ctrlRegsINotFree`, `spt_frame_SI` `sptFrameSI`, `spt_inc_SI` `sptIncSI`, `spt_zca_SI`
`sptZcaSI`, `spt_lpad_SI` `sptLpadSI`, `tick_frame` `tickFrame`, `tick_frame_keep`
`tickFrameKeep`, `tick_frame_ctrl` `tickFrameCtrl`, `spt_tick_frame` `sptTickFrame`.  None is
in the duplicated-name table.

**Dropped:** the Ltacs (deviation 3).  Rocq 23 definitions/lemmas + 4 Ltacs; Lean 23.
**Not ported:** the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxSpineOk7

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. The SIE-agnostic regime -/

/-- Rocq `intr_on`: S-mode interrupts are enabled (SIE = 1). -/
def intrOn (rs : RegFile) : Prop :=
  (_get_Mstatus_SIE (rs .mstatus) == 1#1) = true

/-- Rocq `stvec_direct`: stvec is in DIRECT mode. -/
def AxIntr.stvecDirect (rs : RegFile) : Prop :=
  trapVectorMode_forwards (_get_Mtvec_Mode (rs .stvec)) = .TV_Direct

/-- Rocq `sie_ok`: SIE = 0, or stvec is in direct mode. -/
def sieOk (rs : RegFile) : Prop :=
  (_get_Mstatus_SIE (rs .mstatus) == 1#1) = false ∨ AxIntr.stvecDirect rs

/-- Rocq `ctrl_regs_I`. -/
def ctrlRegsI : List Register := ctrlRegs ++ [.stvec]

section regimeI
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)

/-- Rocq `ctrl_ok_SI`: the S-mode kernel regime, SIE-agnostic. -/
def ctrlOkSI (rs : RegFile) : Prop :=
  rs .cur_privilege = .Supervisor ∧
  rs .hart_state = .HART_ACTIVE () ∧
  rs .misa = misaC ∧
  rs .menvcfg = menvcfgS ∧
  rs .htif_tohost_base = none ∧
  (rs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false ∧
  rs .pma_regions = bootPMA ∧
  AxSpineOk6.sconfMsFacts (rs .mstatus) ∧
  sieOk rs ∧
  (rs .mie &&& ~~~(rs .mideleg)) = 0#64 ∧
  rs .satp = satp0 ∧
  tlbExact T (rs .tlb) ∧
  AxSpineOk6.pmpOk rs

/-- Rocq `ctrl_ok_S_SI`: the old (SIE = 0) regime is included. -/
theorem ctrlOkSSI (rs : RegFile) : ctrlOkS T satp0 rs → ctrlOkSI T satp0 rs := by
  intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, Or.inl h9, h10, h11, h12, h13⟩

/-- Rocq `ctrl_ok_SI_S`: at SIE = 0 it is exactly the old regime. -/
theorem ctrlOkSIS (rs : RegFile) : ctrlOkSI T satp0 rs → ¬ intrOn rs → ctrlOkS T satp0 rs := by
  intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, _, h10, h11, h12, h13⟩ hn
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, Bool.eq_false_iff.mpr hn, h10, h11, h12, h13⟩

/-- Rocq `ctrl_ok_SI_agree`. -/
theorem ctrlOkSIAgree (rs rs' : RegFile) :
    (∀ r, r ∈ ctrlRegsI → rs' r = rs r) → ctrlOkSI T satp0 rs → ctrlOkSI T satp0 rs' := by
  intro hag hc
  unfold ctrlOkSI AxSpineOk6.pmpOk sieOk AxIntr.stvecDirect at hc ⊢
  rw [hag .cur_privilege (by simp [ctrlRegsI, ctrlRegs]),
    hag .hart_state (by simp [ctrlRegsI, ctrlRegs]),
    hag .misa (by simp [ctrlRegsI, ctrlRegs]), hag .menvcfg (by simp [ctrlRegsI, ctrlRegs]),
    hag .htif_tohost_base (by simp [ctrlRegsI, ctrlRegs]),
    hag .elp (by simp [ctrlRegsI, ctrlRegs]),
    hag .pma_regions (by simp [ctrlRegsI, ctrlRegs]),
    hag .mstatus (by simp [ctrlRegsI, ctrlRegs]),
    hag .stvec (by simp [ctrlRegsI, ctrlRegs]),
    hag .mie (by simp [ctrlRegsI, ctrlRegs]), hag .mideleg (by simp [ctrlRegsI, ctrlRegs]),
    hag .satp (by simp [ctrlRegsI, ctrlRegs]), hag .tlb (by simp [ctrlRegsI, ctrlRegs]),
    hag .pmpcfg_n (by simp [ctrlRegsI, ctrlRegs]),
    hag .pmpaddr_n (by simp [ctrlRegsI, ctrlRegs])]
  exact hc

/-! # 2. The `SpineOkT` fields at `ctrlOkSI` -/

/-- Rocq `ram_fetch_facts_I` (deviation 2). -/
theorem ramFetchFactsI (s : ExecSt) (pa : BitVec 64) (n : Nat) :
    ctrlOkSI T satp0 s.regs → 0 < n → n ≤ 16 → (to_bits (l := 64) n).toNat = n →
    inRam pa n →
    ∃ region,
      pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) pa.toNat
        (to_bits (l := 64) n).toNat = .PMP_Match ∧
      matching_pma_region (s.regs .pma_regions) (.Physaddr pa) n = some region ∧
      (override_PMA region.attributes .PBMT_PMA).executable = true ∧
      exec (within_clint (.Physaddr pa) n) s = some (false, s) ∧
      exec (within_sig (.Physaddr pa) n) s = some (false, s) ∧
      exec (within_htif_readable (.Physaddr pa) n) s = some (false, s) ∧
      devAddr pa = false ∧ paZ pa + n ≤ 2 ^ 64 := by
  intro hc hn hn16 hu hram
  obtain ⟨-, -, -, -, hhtif, -, hpma, -, -, -, -, -, -, -, -, -, hcov⟩ := hc
  refine ⟨ramRegion, ?_, ?_, ramRegionExec, execWithinClintRam pa n s hram,
    execWithinSigFalse pa n s, execWithinHtifNone pa n s hhtif, devAddrRam pa n hram, ?_⟩
  · have hz : (zeros (n := 64)).toNat = 0 := rfl
    rw [hz, hu]
    exact pmpRangeMatch_full _ _ _ _ (Nat.zero_le _) hn (by have := hram.2; omega)
  · rw [hpma]; exact matching_pma_ram pa n hram hn hn16
  · have := hram.2
    unfold ramEnd at this
    unfold paZ
    omega

/-- Rocq `ctrl_ok_SI_tlb_fill`. -/
theorem ctrlOkSITlbFill (rs : RegFile)
    (v : Vector (Option TLB_Entry) (2 ^ 6)) (p2 p1 w : BitVec 64) (vpn : BitVec 27) :
    ctrlOkSI T satp0 rs → AxPtProt.ptreeMaps T vpn p2 p1 w → rs .tlb = v →
    ctrlOkSI T satp0 (rs.set .tlb (vectorUpdate v (tlb_hash 39 vpn)
      (some (uWalkEntry vpn p2 p1 w 0#16)))) := by
  intro hc hmaps hv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hc
  unfold ctrlOkSI AxSpineOk6.pmpOk sieOk AxIntr.stvecDirect at *
  simp (disch := decide) only [RegFile.set_same, RegFile.set_other]
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_, h13⟩
  exact tlbExactFill T v vpn p2 p1 w hmaps (hv ▸ h12)

/-- Rocq `spt_fetch_SI`: THE FETCH FIELD at the SIE-agnostic regime (`sptFetchS`'s script). -/
theorem sptFetchSI
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (t : ExecSt) (pc : BitVec 64) (h : BitVec 16) :
    ctrlOkSI T satp0 t.regs → t.regs .PC = pc → textAtS σi T pc h →
    ∃ t1, tlbFrame t t1 ∧ ctrlOkSI T satp0 t1.regs ∧
      EvA (imgS σi) (fun _ _ => False) (fun r t' => r = .F_RVC h ∧ t' = t1) (fetch ()) t := by
  intro hc hPC ⟨p2, p1, w, pa, hmaps, hs2, hs1, hs0, hchk, hupd, hpb, hcanon, hout, hb0, hRVC, hal⟩
  let σ : ExecSt := ⟨t.regs, σi.mem, t.dev⟩
  have hc0 := hc
  obtain ⟨hpriv, -, hmisa, hmenv, hhtif, -, hpma, hms, -, -, hsatp, htlbx, hA, hord, -, hR, hcov⟩ :=
    hc0
  obtain ⟨-, hSXL, -⟩ := hms
  have htm := execTranslationModeSSv39 satp0 σ hSXL hsatp hmode
  have heff := execEffectivePrivilegeFetch (σ.regs .mstatus) .Supervisor σ
  have hss := execIsShadowStackFetch σ
  have hpmar : WeakKpt.pmaAllowsPteRead (σ.regs .pma_regions) := by
    show WeakKpt.pmaAllowsPteRead (t.regs .pma_regions)
    rw [hpma]; exact WeakKpt.pmaAllowsBootPteRead
  have hs2' : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr2 T (WeakKpt.svpnOf pc)) p2 := hs2
  have hs1' : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr1 p2 (WeakKpt.svpnOf pc)) p1 := hs1
  have hs0' : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf pc)) w := hs0
  obtain ⟨σ', htr, hσ'⟩ := execATranslateAddrImg (.InstructionFetch ()) .Supervisor T.base pc w pa
    satp0 T (σ.regs .tlb) p2 p1 σ hchk hupd hcanon hout hpb rfl hmaps htlbx hs2' hs1' hs0' hmisa
    hmenv hhtif hpriv htm heff hss hsatp hppn hasid rfl hA hord hR hcov hpmar
  have hc' : ctrlOkSI T satp0 σ'.regs := by
    rcases hσ' with rfl | rfl
    · exact hc
    · exact ctrlOkSITlbFill T satp0 t.regs _ p2 p1 w _ hc hmaps rfl
  have hmem' : σ'.mem = σi.mem := by rcases hσ' with rfl | rfl <;> rfl
  have hc'0 := hc'
  obtain ⟨hpriv', -, -, -, -, -, -, -, -, -, -, -, hA', hord', hX', -, -⟩ := hc'0
  have hf : execA (fetch ()) σ = some (.F_RVC h, σ') := by
    cases hal4 : is_aligned_vaddr (.Virtaddr pc) 4
    · rw [hal4] at hal
      simp only [Bool.false_eq_true, ↓reduceIte] at hal
      obtain ⟨hb1, hram, halp, hbytes⟩ := hal
      obtain ⟨region, hrange, hm, hx, hcl, hsig, hh, hdev, hwf⟩ :=
        ramFetchFactsI T satp0 σ' pa 2 hc' (by decide) (by decide) (by decide) hram
      have hmC : (_get_Misa_C (σ.regs .misa) == 1#1) = true := by
        show (_get_Misa_C (t.regs .misa) == 1#1) = true
        rw [hmisa]; decide
      exact execAFetchRVC2SGen pc pa h σ σ' region hPC hmC hb0 hb1 hal4 htr hA' hord' hrange hX' hm
        halp hx hcl hsig hh hdev hwf (by intro j hj; rw [hmem']; exact hbytes j hj) hpriv' hRVC
    · rw [hal4] at hal
      simp only [↓reduceIte] at hal
      obtain ⟨w32, hlow, hram, halp, hbytes⟩ := hal
      obtain ⟨region, hrange, hm, hx, hcl, hsig, hh, hdev, hwf⟩ :=
        ramFetchFactsI T satp0 σ' pa 4 hc' (by decide) (by decide) (by decide) hram
      subst hlow
      exact execAFetchRVC4SGen pc pa w32 σ σ' region hPC hal4 htr hA' hord' hrange hX' hm halp hx
        hcl hsig hh hdev hwf (by intro j hj; rw [hmem']; exact hbytes j hj) hpriv' hRVC
  refine ⟨⟨σ'.regs, t.mem, t.dev⟩, ?_, hc', ?_⟩
  · rcases hσ' with rfl | rfl
    · left; rfl
    · right; exact ⟨_, rfl⟩
  · have hE := execAEvA (fetch ()) σ _ σ' hf t rfl
    refine EvAMono (imgS σi) _ _ _ _ (fetch ()) t (fun _ _ hf => hf) ?_ hE
    rintro x ⟨r', m', d'⟩ ⟨rfl, hr, hm1, hd1⟩
    exact ⟨rfl, by simp only at hr hm1 hd1; subst hr hm1 hd1; rfl⟩

/-- Rocq `ctrl_regs_I_not_seip`. -/
theorem ctrlRegsINotSeip (r : Register) : r ∈ ctrlRegsI → ¬ AxRunClose.pinReg r := by
  intro hin hp
  rcases hp with rfl | rfl <;> exact absurd hin (by decide)

/-- Rocq `spt_seip_SI`. -/
theorem sptSeipSI (rs rs' : RegFile) :
    ctrlOkSI T satp0 rs → regsAgree AxRunClose.pinReg rs' rs → ctrlOkSI T satp0 rs' :=
  fun hc hag => ctrlOkSIAgree T satp0 rs rs' (fun r hin => hag r (ctrlRegsINotSeip r hin)) hc

/-- Rocq `spt_hart_SI`. -/
theorem sptHartSI (rs : RegFile) : ctrlOkSI T satp0 rs → rs .hart_state = .HART_ACTIVE () :=
  fun hc => hc.2.1

/-- Rocq `ctrl_regs_I_not_free`. -/
theorem ctrlRegsINotFree (r r' : Register) : ctrlFree r → r' ∈ ctrlRegsI → r' ≠ r := by
  intro hf hin e
  subst e
  rcases hf with rfl | rfl | rfl | rfl | hg
  · exact absurd hin (by decide)
  · exact absurd hin (by decide)
  · exact absurd hin (by decide)
  · exact absurd hin (by decide)
  · have h : ∀ x ∈ ctrlRegsI, x ∉ uxaGprs := by decide
    exact h _ hin hg

/-- Rocq `spt_frame_SI`. -/
theorem sptFrameSI (rs : RegFile) (r : Register) (v : RegisterType r) :
    ctrlFree r → ctrlOkSI T satp0 rs → ctrlOkSI T satp0 (rs.set r v) :=
  fun hf hc => ctrlOkSIAgree T satp0 rs _
    (fun r' hin => RegFile.set_other _ _ _ _ (ctrlRegsINotFree r r' hf hin)) hc

/-- Rocq `spt_inc_SI`. -/
theorem sptIncSI (t : ExecSt) : ctrlOkSI T satp0 t.regs → ∃ b,
    EvA (imgS σi) (fun _ _ => False) (fun x t' => x = b ∧ t' = t)
      (should_inc_minstret (t.regs .cur_privilege)) t := by
  intro _
  obtain ⟨b, hb⟩ := execShouldIncMinstretSome (t.regs .cur_privilege) t
  exact ⟨b, EvAOfRfF _ _ (rfFShouldIncMinstret _) t b t hb⟩

/-- Rocq `spt_zca_SI`. -/
theorem sptZcaSI (t : ExecSt) : ctrlOkSI T satp0 t.regs →
    EvA (imgS σi) (fun _ _ => False) (fun x t' => x = true ∧ t' = t)
      (currentlyEnabled .Ext_Zca) t := by
  intro hc
  have hm : (_get_Misa_C (t.regs .misa) == 1#1) = true := by
    rw [hc.2.2.1]; decide
  exact EvAOfRfF _ _ rfFCurrentlyEnabledZca t true t (execCurrentlyEnabledZca t hm)

/-- Rocq `spt_lpad_SI`. -/
theorem sptLpadSI (t : ExecSt) : ctrlOkSI T satp0 t.regs →
    EvA (imgS σi) (fun _ _ => False) (fun x t' => x = false ∧ t' = t)
      (is_landing_pad_expected ()) t :=
  spLpadOf (imgS σi) (ctrlOkSI T satp0) (fun _ hc => hc.2.2.2.2.2.1) t

end regimeI

/-! # The tick frame -/

/-- Rocq `tick_frame`: everything but mcycle / mtime / mip is untouched. -/
def tickFrame (t t' : ExecSt) : Prop :=
  ∀ r : Register, r ≠ .mcycle → r ≠ .mtime → r ≠ .mip → t'.regs r = t.regs r

/-- Rocq `tick_frame_keep`. -/
theorem tickFrameKeep (t t' : ExecSt) : tickFrame t t' → keepRegs t.regs t'.regs := by
  intro hag
  have hg1 : ∀ r ∈ uxaGprs, r ≠ .mcycle ∧ r ≠ .mtime ∧ r ≠ .mip := by decide
  refine ⟨hag _ (by decide) (by decide) (by decide), fun z => ?_⟩
  refine uxaXget_congr t.regs t'.regs (fun r hr => ?_) z
  obtain ⟨h1, h2, h3⟩ := hg1 r hr
  exact hag r h1 h2 h3

/-- Rocq `tick_frame_ctrl`. -/
theorem tickFrameCtrl (T : PTree) (satp0 : BitVec 64) (t t' : ExecSt) :
    tickFrame t t' → ctrlOkSI T satp0 t.regs → ctrlOkSI T satp0 t'.regs := by
  intro hag hc
  have hc1 : ∀ r ∈ ctrlRegsI, r ≠ .mcycle ∧ r ≠ .mtime ∧ r ≠ .mip := by decide
  refine ctrlOkSIAgree T satp0 t.regs t'.regs (fun r hin => ?_) hc
  obtain ⟨h1, h2, h3⟩ := hc1 r hin
  exact hag r h1 h2 h3

/-- Rocq `spt_tick_frame`: `sptTickS`'s script, with the frame as the post (no regime needed). -/
theorem sptTickFrame (img : Image) (t : ExecSt) :
    EvA img (fun _ _ => False) (fun _ t' => tickFrame t t') (tick_clock ()) t := by
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
  all_goals intro r h1 h2 h3
  all_goals simp only [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ h1,
    RegFile.set_other _ _ _ _ h2, RegFile.set_other _ _ _ _ h3]

end Weak
