/-
Weak: **the demonic walk's register-only premises from the S-mode regime, and NON-VACUITY at
`AxSmodeProbe`'s state** (task item 6).

Rocq: `iris/AxWalk4.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 `pteRdOkOfRegs` / `pteXOkOfRegs`: the register-only facts of a walker PTE read / of the Svadu
write-back (PMA `supports_pte_read` / `supports_pte_write` — `pmaCheck` ignores the reservation
flag at `PageTableEntry` accesses —, PMP R / W, not MMIO) from `AxSpineOk6.pmpOk`, `pmpW`, the
platform PMA table, no HTIF, and the slot being RAM.  NO MEMORY CONTENT is used: the walker
values come from the graph.

§2 the probe instances (cold TLB, Sv39, `AxSymCtl3.pT`, the data page of AxDataX8):
`nvWalkPreset`: `PTranslateTLBMissNoupd` with all premises discharged, the three PTE reads
DEMONIC and pinned by the protocol-shaped pin `nvPin` (q2 = pP2, q1 = pP1, leaf in the class),
leaf class = the image word `dW` (A/D preset: the image-read special case); `nvWalkAd`:
`PTranslateTLBMiss` (both branches) with the leaf class {A-clear word `dWc`, its write-back
`dWa`} ⊆ `pteSetAD dW` (`nvClassVar`); on the `dWc` branch the fused Svadu RMW occurs at row
position 3 (menvcfg.ADUE = 1 at the probe, `nvAdue`).  The continuation is the INFORMATIVE post:
the exact walker event list with positions, the PPN, the TLB fill.

## Deviations from Rocq

1. SPELLING as `AxWalk3` deviation 1 (`mstate` ↦ `ExecSt`, `uint` ↦ `paZ` / `toNat`,
   `register_lookup r t.(sregs)` ↦ `t.regs .r`, `vec_access_dec v 0` ↦ `v[0]!`, `CS d b r` ↦
   `⟨d, b, r⟩`, `img_of` ↦ `imgOf`, `nvS_*` ↦ `nvS*`, `MENVCFG_S` ↦ `menvcfgS`, `w64` ↦
   `AxEpiProbe.w64`, `mword_of_int 0` ↦ `0`, `autocast (PPN_of_PTE q)` ↦ `ppn0 q`,
   `pte_set_ad` ↦ `pteSetAD`, `Z_to_bv 1 z` ↦ `z#1`, `eq_vec x 'b"1" = true` ↦
   `(x == 1#1) = true`, `grow GD 0 !! k` ↦ `(AxOpsem.grow GD 0)[k]?`, `eq dW` ↦ `Eq dW`).
2. Section `regs`'s hypotheses: `pt_slot_mem` ↦ `WeakWalkEff.ptSlotMem` (Lean: bytes, `inRam a 8`,
   aligned; Rocq's two `addr_is_ram` conjuncts are `inRam a 8`), `pmp_ok` ↦ `AxSpineOk6.pmpOk`,
   `pma_allows_all (pma_regions)` ↦ `t.regs .pma_regions = bootPMA` (`AxSpineOk6` deviation 2: the
   region is `ramRegion`, its PTE read/write bits by `rfl`).  `slotRange` / `pteRdOkOfRegs` /
   `pteXOkOfRegs` take the section variables explicitly in the order `wok μ t a w σs`, then the
   hypotheses they use.
3. `execAMmioWFalse` proves the `within_mmio_writable` fact through `ExecSC4.
   execWithinMmioWritableFalse` + `AxDataX3.execWithinHtifWNone` (Rocq unfolds `or_boolM` /
   `and_boolM`, which the Lean model does not have).
4. `vm_compute` / `vr8` ↦ `decide +kernel` / `ax_epi_ledger_krfl`.
5. `PTranslateTLBMiss`'s continuations are stated on Lean's left-nested appends of walker events;
   `QPreset`/`QAd` read them as the literal lists (closed by `rfl`).

**Rocq → Lean name map.**  `execA_mmio_w_false` `execAMmioWFalse`, `slot_range` `slotRange`,
`slot_not_mmio_facts` `slotNotMmioFacts`, `pte_rd_ok_of_regs` `pteRdOkOfRegs`, `pte_x_ok_of_regs`
`pteXOkOfRegs`, `wa2/1/0` `wa2/1/0`, `wa2/1/0_eq` `wa2Eq/wa1Eq/wa0Eq`, `nv_wok` `nvWok`, `Gnr`
`Gnr`, `posR_Gnr` `posRGnr`, `nv_ctrl` `nvCtrl`, `nv_rd_ok` `nvRdOk`, `nv_pin` `nvPin`,
`Q_preset` `QPreset`, `nv_walk_preset` `nvWalkPreset`, `dWc` `dWc`, `dWa` `dWa`, `nv_P0` `nvP0`,
`nv_upd_c` `nvUpdC`, `nv_upd_a` `nvUpdA`, `nv_class_var` `nvClassVar`, `nv_adue` `nvAdue`, `Gad`
`Gad`, `posR_Gad` `posRGad`, `posX_Gad3` `posXGad3`, `nv_x_ok` `nvXOk`, `Q_ad` `QAd`,
`nv_walk_ad` `nvWalkAd`.  None is in the duplicated-name table.

**Dropped:** none (the `Print Assumptions` lines are not ported).  Rocq 32 definitions/lemmas,
Lean 32.
-/
import Weak.AxWalk3
import Weak.AxDataX8

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. The register-only premises from the regime -/

/-- Rocq `execA_mmio_w_false` (deviation 3). -/
theorem execAMmioWFalse (addr : BitVec 64) (n : Nat) (s : ExecSt) :
    exec (within_clint (.Physaddr addr) n) s = some (false, s) →
    exec (within_sig (.Physaddr addr) n) s = some (false, s) →
    s.regs .htif_tohost_base = none →
    execA (within_mmio_writable (.Physaddr addr) n) s = some (false, s) := by
  intro hc hsig hn
  have hmm := execWithinMmioWritableFalse addr n s hc hsig
    (AxDataX3.execWithinHtifWNone addr n s hn)
  to_a hmm
  exact hmm

section regs
variable (wok : Int → Nat → Prop) (μ t : ExecSt) (a w : BitVec 64) (σs : ExecSt)
variable (Hsm : WeakWalkEff.ptSlotMem σs a w) (Hpmp : AxSpineOk6.pmpOk t.regs)
  (Hpma : t.regs .pma_regions = bootPMA) (Hhtif : t.regs .htif_tohost_base = none)
  (Hwok : wok (paZ a) 8)

include Hsm Hpmp in
/-- Rocq `slot_range`. -/
theorem slotRange :
    pmpRangeMatch ((zeros (n := 64)).toNat * 4) (((tm μ t).regs .pmpaddr_n)[0]!.toNat * 4)
      a.toNat (to_bits (l := 64) 8).toNat = .PMP_Match := by
  obtain ⟨-, hram, -⟩ := Hsm
  obtain ⟨-, -, -, -, hcov⟩ := Hpmp
  have hz : (zeros (n := 64)).toNat = 0 := rfl
  have h8 : (to_bits (l := 64) 8).toNat = 8 := by decide
  rw [hz, h8]
  have h2 := hram.2
  have hcov' : ramEnd ≤ ((tm μ t).regs .pmpaddr_n)[0]!.toNat * 4 := hcov
  exact pmpRangeMatch_full _ _ _ _ (Nat.zero_le _) (by omega) (by omega)

include Hsm Hhtif in
/-- Rocq `slot_not_mmio_facts`. -/
theorem slotNotMmioFacts :
    exec (within_clint (.Physaddr a) 8) (tm μ t) = some (false, tm μ t) ∧
    exec (within_sig (.Physaddr a) 8) (tm μ t) = some (false, tm μ t) ∧
    exec (within_htif_readable (.Physaddr a) 8) (tm μ t) = some (false, tm μ t) ∧
    devAddr a = false := by
  obtain ⟨-, hram, -⟩ := Hsm
  exact ⟨execWithinClintRam a 8 _ hram, execWithinSigFalse a 8 _,
    execWithinHtifNone a 8 (tm μ t) Hhtif, devAddrRam a 8 hram⟩

include Hsm Hpmp Hpma Hhtif Hwok in
/-- Rocq `pte_rd_ok_of_regs`. -/
theorem pteRdOkOfRegs : pteRdOk wok μ t a := by
  have hrange := slotRange μ t a w σs Hsm Hpmp
  obtain ⟨hc, hsig, hh, hdev⟩ := slotNotMmioFacts μ t a w σs Hsm Hhtif
  obtain ⟨-, hram, hal⟩ := Hsm
  obtain ⟨hA, hord, -, hR, -⟩ := Hpmp
  have hm : matching_pma_region ((tm μ t).regs .pma_regions) (.Physaddr a) 8 = some ramRegion := by
    show matching_pma_region (t.regs .pma_regions) _ _ = _
    rw [Hpma]
    exact matching_pma_ram a 8 hram (by omega) (by omega)
  have hpm := execPmaCheckRamPte a .PBMT_PMA ramRegion false (tm μ t) hm hal rfl
  have hcp : exec (check_pma_with_pmp_priority (.Load .PageTableEntry) .PBMT_PMA .Supervisor
      (.Physaddr a) 8 false) (tm μ t) = some (.Ok pmaOkAligned, tm μ t) := by
    unfold check_pma_with_pmp_priority
    rw [execBindSome _ _ _ _ _ hpm]
    rfl
  to_a hcp
  have hp := execPmpCheckSupervisorGrantLoad a 8 (tm μ t) hA hord hrange hR
  to_a hp
  exact ⟨hcp, hp, execAMmioFalse a 8 (tm μ t) hc hsig hh, hdev, Hwok⟩

variable (HW : pmpW t.regs)

include Hsm Hpmp Hpma Hhtif Hwok HW in
/-- Rocq `pte_x_ok_of_regs`. -/
theorem pteXOkOfRegs : pteXOk wok μ t a := by
  have hrange := slotRange μ t a w σs Hsm Hpmp
  obtain ⟨hc, hsig, hh, hdev⟩ := slotNotMmioFacts μ t a w σs Hsm Hhtif
  obtain ⟨-, hram, hal⟩ := Hsm
  obtain ⟨hA, hord, -, hR, -⟩ := Hpmp
  have hm : matching_pma_region ((tm μ t).regs .pma_regions) (.Physaddr a) 8 = some ramRegion := by
    show matching_pma_region (t.regs .pma_regions) _ _ = _
    rw [Hpma]
    exact matching_pma_ram a 8 hram (by omega) (by omega)
  have hpm := execPmaCheckRamPte a .PBMT_PMA ramRegion true (tm μ t) hm hal rfl
  have hcp : exec (check_pma_with_pmp_priority (.Load .PageTableEntry) .PBMT_PMA .Supervisor
      (.Physaddr a) 8 true) (tm μ t) = some (.Ok pmaOkAligned, tm μ t) := by
    unfold check_pma_with_pmp_priority
    rw [execBindSome _ _ _ _ _ hpm]
    rfl
  to_a hcp
  have hpmw := execPmaCheckRamWpteRoc a .PBMT_PMA ramRegion true (tm μ t) hm hal rfl
  have hcpw : exec (check_pma_with_pmp_priority (.Store .PageTableEntry) .PBMT_PMA .Supervisor
      (.Physaddr a) 8 true) (tm μ t) = some (.Ok pmaOkAligned, tm μ t) := by
    unfold check_pma_with_pmp_priority
    rw [execBindSome _ _ _ _ _ hpmw]
    rfl
  to_a hcpw
  have hp := execPmpCheckSupervisorGrantLoad a 8 (tm μ t) hA hord hrange hR
  to_a hp
  have hpw := execPmpCheckSupervisorGrantWpte a 8 (tm μ t) hA hord hrange HW
  to_a hpw
  exact ⟨hcp, hp, execAMmioFalse a 8 (tm μ t) hc hsig hh, hcpw, hpw,
    execAMmioWFalse a 8 (tm μ t) hc hsig Hhtif, hdev, Hwok⟩

end regs

/-! # 2. NON-VACUITY at the probe -/

/-- Rocq `wa2`. -/
def wa2 : BitVec 64 := waddr2 dvpn nvSRoot
/-- Rocq `wa1`. -/
def wa1 : BitVec 64 := waddr1 dvpn pP2
/-- Rocq `wa0`. -/
def wa0 : BitVec 64 := waddr0 dvpn pP1

/-- Rocq `wa2_eq`. -/
theorem wa2Eq : wa2 = AxPtProt.ptAddr2 pT dvpn := rfl
/-- Rocq `wa1_eq`. -/
theorem wa1Eq : wa1 = AxPtProt.ptAddr1 pP2 dvpn := rfl
/-- Rocq `wa0_eq`. -/
theorem wa0Eq : wa0 = AxPtProt.ptAddr0 pP1 dvpn := rfl

/-- Rocq `nv_wok`: the PT region of the walk, the three slots. -/
def nvWok (a : Int) (n : Nat) : Prop := n = 8 ∧ (a = paZ wa2 ∨ a = paZ wa1 ∨ a = paZ wa0)

/-- Rocq `Gnr`: a row for hart 0 with no fused RMW anywhere (the preset walk). -/
def Gnr (GD : Gdexec) : Prop :=
  ∀ (k : Nat) (lb : Lbl), (AxOpsem.grow GD 0)[k]? = some lb → ∀ (aq rl : Bool) (b : Int) (n : Nat),
    aident lb ≠ .IRmw aq rl b n

/-- Rocq `posR_Gnr`. -/
theorem posRGnr (D : Int → Nat → Prop) (k : Nat) : posR Gnr 0 D k :=
  fun _ HG lb aq rl base m Hl Hid _ => HG k lb Hl aq rl base m Hid

/-- Rocq `nv_ctrl`. -/
theorem nvCtrl : ctrlOkS pT nvSSatp nvSRs := nvSCtrlOk pT

/-- Rocq `nv_rd_ok`. -/
theorem nvRdOk (a w : BitVec 64) :
    WeakWalkEff.ptSlotMem nvST a w → nvWok (paZ a) 8 → pteRdOk nvWok nvST nvST a := by
  intro Hsm Hw
  obtain ⟨-, -, -, -, Hhtif, -, Hpma, -, -, -, -, -, Hpmp⟩ := nvCtrl
  exact pteRdOkOfRegs nvWok nvST nvST a w nvST Hsm Hpmp Hpma Hhtif Hw

/-- Rocq `nv_pin`: THE PROTOCOL-SHAPED PIN (AxPtProt §INTERFACE (a)), per slot. -/
def nvPin (P0 : BitVec 64 → Prop) (_k : Nat) (a : Int) (vs : List (BitVec 8)) : Prop :=
  (a = paZ wa2 → rrv 8 vs = pP2) ∧ (a = paZ wa1 → rrv 8 vs = pP1) ∧
    (a = paZ wa0 → P0 (rrv 8 vs))

/-- Rocq `Q_preset`: the informative post of the preset walk — exactly three walker events at
row positions 0, 1, 2 (in the slots wa2 / wa1 / wa0, words pinned), the PPN of the leaf, the TLB
filled with the READ leaf. -/
def QPreset (ws : List (Nat × Wev)) (_s : Cst) (k : Nat)
    (x : Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit)) (t : ExecSt) : Prop :=
  ∃ vs2 vs1 vs0 : List (BitVec 8),
    ws = [(0, .WRd (paZ wa2) vs2), (1, .WRd (paZ wa1) vs1), (2, .WRd (paZ wa0) vs0)] ∧
    rrv 8 vs2 = pP2 ∧ rrv 8 vs1 = pP1 ∧ rrv 8 vs0 = dW ∧ k = 3 ∧
    x = .Ok (ppn0 dW, .PBMT_PMA, ()) ∧
    t = AxWalk3.tlbFill dvpn pP2 pP1 nvST 0 dW

/-- Rocq `nv_walk_preset`. -/
theorem nvWalkPreset :
    CertWP (imgOf nvST) (fun _ _ => False) nvWok .DKLd (posR Gnr 0) (posX Gnr 0) (nvPin (Eq dW))
      (fun _ _ _ => True) (fun _ _ _ _ _ => False) QPreset [] ⟨.CPend, .BInf, false⟩ 0
      (translate_TLB_miss 39 0 nvSRoot dvpn (.Load .Data) .Supervisor false false ()) nvST := by
  obtain ⟨_, _, -, -, -, -, -, -, -, Hv2, Hn2, Hv1, Hn1, Hv0, Hl0, Hnap, -⟩ := dTMaps
  obtain ⟨-, -, Hmisa, Hmenv, -⟩ := nvCtrl
  have Hchk : pteCheckOk (.Load .Data) .Supervisor false false dW := by
    intro s
    ax_epi_ledger_krfl
  have Hupd : update_PTE_Bits dW (.Load .Data) = none := by decide +kernel
  exact PTranslateTLBMissNoupd (img := imgOf nvST) (dok := fun _ _ => False) (wok := nvWok)
    (kind := .DKLd) (pR := posR Gnr 0) (pX := posX Gnr 0) (wpin := nvPin (Eq dW))
    (xpin := fun _ _ _ => True) (μ := nvST) (vpn := dvpn) (root := nvSRoot) (p2 := pP2)
    (p1 := pP1) (P0 := Eq dW) (acc := .Load .Data) (p := .Supervisor) (mxr := false)
    (do_sum := false) (H2i := Hv2) (H2nl := Hn2) (H1i := Hv1) (H1nl := Hn1)
    (H0i := fun q hq => hq ▸ Hv0) (H0nl := fun q hq => hq ▸ Hl0)
    (Hchk0 := fun q hq => hq ▸ Hchk) (H0N := fun q hq => hq ▸ Hnap)
    0 menvcfgS QPreset [] .CPend .BInf false 0 nvST Hmisa Hmenv (by decide)
    (nvRdOk _ pP2 dTSlot2 ⟨rfl, Or.inl rfl⟩)
    (nvRdOk _ pP1 dTSlot1 ⟨rfl, Or.inr (Or.inl rfl)⟩)
    (nvRdOk _ dW dTSlot0 ⟨rfl, Or.inr (Or.inr rfl)⟩)
    (posRGnr _ _) (posRGnr _ _) (posRGnr _ _)
    (fun _ _ h => h.1 rfl) (fun _ _ h => h.2.1 rfl) (fun _ _ h => h.2.2 rfl)
    (fun q hq => hq ▸ Hupd)
    (fun vs2 vs1 vs0 _ _ _ h2 h1 h0 => by
      rw [← h0]
      exact ⟨vs2, vs1, vs0, rfl, h2, h1, h0.symm, rfl, rfl, rfl⟩)

/-- Rocq `dWc`: the A/D-CLEAR leaf. -/
def dWc : BitVec 64 := AxEpiProbe.w64 (pteLeafNoad 0x80001)
/-- Rocq `dWa`: its Svadu write-back (A set). -/
def dWa : BitVec 64 := AxEpiProbe.w64 ((0x80001 <<< 10) ||| 0x4F)
/-- Rocq `nv_P0`: the leaf class {A-clear word, its write-back}. -/
def nvP0 (q : BitVec 64) : Prop := q = dWc ∨ q = dWa

/-- Rocq `nv_upd_c`. -/
theorem nvUpdC : update_PTE_Bits dWc (.Load .Data) = some dWa := by decide +kernel
/-- Rocq `nv_upd_a`. -/
theorem nvUpdA : update_PTE_Bits dWa (.Load .Data) = none := by decide +kernel

/-- Rocq `nv_class_var`: both class members are A/D variants of the probe's canonical leaf `dW`
(the protocol's leaf class). -/
theorem nvClassVar (q : BitVec 64) : nvP0 q → ∃ a d : BitVec 1, q = pteSetAD dW a d := by
  rintro (rfl | rfl)
  · exact ⟨0#1, 0#1, by decide +kernel⟩
  · exact ⟨1#1, 0#1, by decide +kernel⟩

/-- Rocq `nv_adue`. -/
theorem nvAdue : (_get_MEnvcfg_ADUE menvcfgS == 1#1) = true := by decide +kernel

/-- Rocq `Gad`: hart 0's row — the fused RMW item sits at position 3 and nowhere else. -/
def Gad (GD : Gdexec) : Prop :=
  (∀ (k : Nat) (lb : Lbl), k ≠ 3 → (AxOpsem.grow GD 0)[k]? = some lb →
    ∀ (aq rl : Bool) (b : Int) (n : Nat), aident lb ≠ .IRmw aq rl b n) ∧
  (∀ lb : Lbl, (AxOpsem.grow GD 0)[3]? = some lb →
    ∃ (aq rl : Bool) (b : Int) (n : Nat), aident lb = .IRmw aq rl b n)

/-- Rocq `posR_Gad`. -/
theorem posRGad (D : Int → Nat → Prop) (k : Nat) : k ≠ 3 → posR Gad 0 D k :=
  fun Hk _ HG lb aq rl base m Hl Hid _ => HG.1 k lb Hk Hl aq rl base m Hid

/-- Rocq `posX_Gad3`. -/
theorem posXGad3 (D : Int → Nat → Prop) : posX Gad 0 D 3 := by
  intro _ HG lb aq base m Hl Hid _
  obtain ⟨_, _, _, _, Hr⟩ := HG.2 lb Hl
  rw [Hid] at Hr
  cases Hr

/-- Rocq `nv_x_ok`. -/
theorem nvXOk : pteXOk nvWok nvST nvST wa0 := by
  obtain ⟨-, -, -, -, Hhtif, -, Hpma, -, -, -, -, -, Hpmp⟩ := nvCtrl
  exact pteXOkOfRegs nvWok nvST nvST wa0 dW nvST dTSlot0 Hpmp Hpma Hhtif
    ⟨rfl, Or.inr (Or.inr rfl)⟩ nvPmpW

/-- Rocq `Q_ad`. -/
def QAd (ws : List (Nat × Wev)) (_s : Cst) (k : Nat)
    (x : Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit)) (_t : ExecSt) :
    Prop :=
  (∃ q0, nvP0 q0 ∧ x = .Ok (ppn0 q0, .PBMT_PMA, ())) ∧
  ((k = 3 ∧ ws.map Prod.fst = [0, 1, 2]) ∨
   (k = 4 ∧ ws.map Prod.fst = [0, 1, 2, 3, 3] ∧
     ∃ rvs wvs, ws[4]? = some (3, .WRmw (paZ wa0) rvs wvs) ∧ nvP0 (rrv 8 rvs)))

/-- Rocq `nv_walk_ad`. -/
theorem nvWalkAd :
    CertWP (imgOf nvST) (fun _ _ => False) nvWok .DKLd (posR Gad 0) (posX Gad 0) (nvPin nvP0)
      (fun _ _ vs => rrv 8 vs = dWc)
      (fun _ _ _ _ _ => False) QAd [] ⟨.CPend, .BInf, false⟩ 0
      (translate_TLB_miss 39 0 nvSRoot dvpn (.Load .Data) .Supervisor false false ()) nvST := by
  obtain ⟨_, _, -, -, -, -, -, -, -, Hv2, Hn2, Hv1, Hn1, -⟩ := dTMaps
  obtain ⟨-, -, Hmisa, Hmenv, -⟩ := nvCtrl
  have H0i : ∀ q, nvP0 q → pteValid q := by
    rintro q (rfl | rfl) s <;> ax_epi_ledger_krfl
  have H0nl : ∀ q, nvP0 q → pteLeaf q := by
    rintro q (rfl | rfl) <;> (unfold pteLeaf; decide +kernel)
  have Hchk0 : ∀ q, nvP0 q → pteCheckOk (.Load .Data) .Supervisor false false q := by
    rintro q (rfl | rfl) s <;> ax_epi_ledger_krfl
  have H0N : ∀ q, nvP0 q → (_get_PTE_Ext_N (ext_bits_of_PTE q) == 1#1) = false := by
    rintro q (rfl | rfl) <;> decide +kernel
  exact PTranslateTLBMiss (img := imgOf nvST) (dok := fun _ _ => False) (wok := nvWok)
    (kind := .DKLd) (pR := posR Gad 0) (pX := posX Gad 0) (wpin := nvPin nvP0)
    (xpin := fun _ _ vs => rrv 8 vs = dWc) (μ := nvST) (vpn := dvpn) (root := nvSRoot)
    (p2 := pP2) (p1 := pP1) (P0 := nvP0) (acc := .Load .Data) (p := .Supervisor) (mxr := false)
    (do_sum := false) (H2i := Hv2) (H2nl := Hn2) (H1i := Hv1) (H1nl := Hn1) (H0i := H0i)
    (H0nl := H0nl) (Hchk0 := Hchk0) (H0N := H0N)
    0 menvcfgS QAd [] .CPend .BInf false 0 nvST Hmisa Hmenv (by decide) nvAdue
    (nvRdOk _ pP2 dTSlot2 ⟨rfl, Or.inl rfl⟩)
    (nvRdOk _ pP1 dTSlot1 ⟨rfl, Or.inr (Or.inl rfl)⟩)
    (nvRdOk _ dW dTSlot0 ⟨rfl, Or.inr (Or.inr rfl)⟩)
    nvXOk
    (posRGad _ _ (by decide)) (posRGad _ _ (by decide)) (posRGad _ _ (by decide))
    (posXGad3 _)
    (fun _ h => by cases h)
    (fun _ _ h => h.1 rfl) (fun _ _ h => h.2.1 rfl) (fun _ _ h => h.2.2 rfl)
    (fun vs _ hc => by
      have hc' : rrv 8 vs = dWc := hc
      rw [hc']
      exact ⟨Or.inl rfl, dWa, nvUpdC⟩)
    (fun _ _ vs0 _ _ _ _ _ HP0 _ => ⟨⟨rrv 8 vs0, HP0, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩)
    (fun _ _ vs0 _ vs w' _ _ _ _ _ _ _ _ HP0 _ HP _ _ _ _ =>
      ⟨⟨rrv 8 vs0, HP0, rfl⟩, Or.inr ⟨rfl, rfl, vs, AxDataX.wrb 8 w', rfl, HP⟩⟩)

end Weak
