/-
Weak: **PHASE 5, stage 2: CERTIFICATE (a) for `AxSpinE8.wpdMycpu` (NON-VACUITY)** — one concrete
instance at which the premises of `wpdMycpu` hold, restated under O2 Stage C / Q20' Option V.

Rocq: `iris/AxSpinE8f.v` @ xxvzwolszwmp.

## The Rocq header, in substance

THE INSTANCE.  Memory `σ8` = `AxSpinE8d.mem1` (the spike's image: mycpu's real bytes, the Sv39
table root 0x80010 / L1 0x80011 / L0 0x80012, plus the return-site bytes at 0x80000000; it does
NOT hold the stack bytes, so `textFixed` does not pin the reloads); table `tT` (VA = PA pages
0x80000 and 0x80001), `satp8`; entry `AxSpinE8d.rsE` (the register file after a real COLD run of
mycpu: warm TLB with the exact `uWalkEntry` entries of both pages, PC := mycpu); graph `GT8` =
`graphOfSc` of hart 0's row `AxSpinE8d.rowM` (interleaving = the row, no deps; consistency by
`graphOfScCatT` + `catTAd`); layout `L8` (hart 0, stack bytes 0x80000ff0..0x80000fff, read-only =
text and the three table pages, lock word / nextpid at 0x80003000 / 0x80003100, unused); call
k = 0, ret = 0x80000000, Pra = 0x80000ff8, Ps0 = 0x80000ff0, Ψ = True.  `wpdMycpuPremises`:
every pure premise in one statement; `HΨmid8`: the post premise; Rocq `cert_a`: `wpd_mycpu`
APPLIED at the instance.  `hinj8` (canonical `Hinj`: a canonical VA translating to 0x80000000
under `tT` IS 0x80000000) and `hstv8` (VA 0 is unmapped).  Everything closed by kernel
computation on the literal forms.

## THE FINDING (Lean only): `wpdMycpu` is VACUOUS in this tree

`AxSpinE8f.mycpuTextFalse : ∀ σi T, ¬ mycpuText σi T`.  KERNEL DRIFT (`AxSpinE7` deviation 1)
moved `mycpu` to 0x8000195c, so its two 4-byte words (`auipc` at `pcm 0x0e` = 0x8000196a, `addi`
at `pcm 0x12` = 0x8000196e) sit at pcs that are 2 mod 4 (Rocq: 0x800018f4 / 0x800018f8, 4-aligned),
while `textAt4S` (AxDataX6, the only 4-byte text predicate `textOkB`/`tokB` accept) demands
`is_aligned_vaddr pc 4 = true`.  So `AxSpinE8.wpdMycpu`'s premise `Htxt : mycpuText σi T` is
unsatisfiable and the theorem holds vacuously — and so does every caller that supplies `Htxt`
(AxSpinHd*, AxSpinPO3, AxSpinAp, …, per their own `mycpuText` premises).  Rocq's `Htxt8` and
`cert_a` are therefore FALSE / unprovable here and are DROPPED (deviation 1); the other twelve
(compressed) text facts DO hold at the instance (`AxSpinE8f.Htxt8Rvc`), and every OTHER premise
of `wpdMycpu` holds (`AxSpinE8f.wpdMycpuPremises`).  The fix is upstream (owner question): a
2-aligned 4-byte text predicate / `textOkB` arm (the two-halfword fetch of WeakFetch2) for
AxSpinE7's `tok0e`/`tok12` and the `mycpuText` definition.

## Deviations from Rocq

1. O2 STAGE C / Q20' (Option V) and THE FINDING:
   * the instance is E8d's Stage C restatement (E8d deviation 1): `mem1` holds `ld a1,-8(sp)` at
     the return site (Rocq: two `c.nop`), the row `rowM` has 5 items (Rocq 19: the fetches are
     administrative), `il8` lists 5 positions (Rocq 19); `growG` is the 5-item graph row
     (`rowM` with the reads' sources filled in);
   * `Hrow8` is the Stage C `RowMycpu 0 … (paZ Pra8) (paZ Ps08)` (no `pret`/`nret`);
   * `wpd_mycpu_premises` ↦ `AxSpinE8f.wpdMycpuPremises` over the LEAN `wpdMycpu`'s premises:
     the `mycpuText` conjunct is removed (unsatisfiable, see the finding), Rocq's `Hinj`/`Hstv`
     conjuncts are replaced by the Option V pins `Hval` (`AxSpinE8f.hval8`: the reload's graph
     value at (0, 0+2) is `stBytes 8 ret8`) and `Hret` (`AxSpinE8f.hret8`);
   * `Htxt8` DROPPED (false: `mycpuTextFalse`), replaced by `Htxt8Rvc` (its twelve true
     conjuncts); `cert_a` DROPPED (it is `wpdMycpu` applied, which needs `Htxt8`; Rocq's other
     residual hypothesis `va_first_read` is gone in Lean anyway).  Neither has a downstream user
     (grep of the Rocq tree).
2. `hinj8`, `hstv8`, `stvec8`, `stv8` are TRUE and ported, but have no consumer under Q20'
   (`wpdMycpu` dropped `Hinj`/`Hstv`/`stv`).  `hinj8` uses `AxSpinE8e.svpnUnsigned`/`zShift39`/
   `lo11Unsigned` as Rocq does.
3. TYPES / SPELLING: `uint` ↦ `paZ` (or `toNat`); `mword_of_int s : mword 44` ↦
   `BitVec.ofNat 44 s`; `Z.eqb (uint j) n` ↦ `j.toNat = n`; `autocast (satp_to_ppn …) = pt_base`
   ↦ `BitVec.setWidth 44 (satp_to_ppn …) = tT.base`; `rd32` takes the PA (a `BitVec 64`) and reads
   `σ8.mem` (Rocq: a `Z`, read through `img_S`); `slot8`'s two RAM checks (`a`, `a+7`) ↦ Lean
   `ptSlotMem`'s single `inRam a 8`; `ram_ok_z` is over `inRam`; `stk8` = `LawfulSet.ofList
   (clRange 0x80000ff0 16)` (Rocq `list_to_set (seqZ …)`); `text8`/`ro8` are `Int` ranges;
   `cl_range_bound` is `inClr`'s forward half; Rocq's notation `GD8` ↦ `abbrev AxSpinE8f.GD8`;
   `register_lookup r rsE` ↦ `rsE .r`; the `let`s `sp0`/`va_ra`/`va_s0` ↦ `AxSpinE8.vaRa rsE` /
   `vaS0 rsE`.
4. PROOFS: `vm_compute`/`vr`/`byt`/`eqf` ↦ `decide +kernel` / `ax_epi_ledger_krfl`; `tlbE` is the
   plain projection `rsE .tlb` (Rocq froze it by `Eval vm_compute`; `tlbEEq` is `rfl`) and
   `tlbExact8`'s 64-case split ↦ the Lean-only checker `AxSpinE8f.tlbChk` (+ `entEqB`:
   `TLB_Entry` derives only `BEq`) decided by the kernel; the Ltacs `txt_common`/`txt2`/`data_tac`
   ↦ the Lean-only lemmas `textAtT4`/`textAtT2`/`dataD` (+ macro `ax_spin_e8f_txt2`); `txt4`/
   `bytes8` not needed; `Hw8_8`/`no_rmw8_8` enumerate the row's members; `Hfix8`'s second half
   via `AxSpinE8f.readsOffImg` (no row read hits image bytes).  `Print Assumptions` not ported.
5. SECTION: `HΨmid8` takes `GF`/`AxannotGS`/`Xv6G` and `nm` explicitly; the local instances
   `f8_pol`/`f8_G` are inlined as `AxSpinX2.xG L8 GT8 nm` (no `hlc`: `postLifting` needs none).

**Rocq → Lean name map** (all file-qualified `AxSpinE8f.*`; `ram_ok_z` and `slot8` are in the
duplicated-name table).  `σ8` `σ8`, `L0leaf` `L0leaf`, `L1leaf` `L1leaf`, `P2` `P2`, `P1` `P1`,
`tT0` `tT0`, `tT1` `tT1`, `tT` `tT`, `satp8` `satp8`, `Hmode8` `Hmode8`, `Hasid8` `Hasid8`,
`Hppn8` `Hppn8`, `vpnD` `vpnD`, `vpnT` `vpnT`, `mapsD` `mapsD`, `mapsT` `mapsT`, `ram_ok_z`
`ramOkZ`, `slot8` `slot8`, `slot2D/1D/0D/2T/1T/0T` same, `rd32` `rd32`, `img8` `img8`, `il8`
`il8`, `GT8` `GT8`, `GT8_inputs` `GT8Inputs`, `Hcons8` `Hcons8`, `growG` `growG`, `grow8`
`grow8`, `Hrow8` `Hrow8`, `row_forall` `rowForall`, `Hw8_8` `Hw8_8`, `no_rmw8_8` `noRmw8_8`,
`Hfix8` `Hfix8`, `stk8` `stk8`, `text8` `text8`, `ro8` `ro8`, `L8` `L8`, `cl_range_bound`
`clRangeBound`, `priv8` `priv8`, `XO8` `XO8`, `lwb8` `lwb8`, `HL8` `HL8`, `tlbE` `tlbE`,
`tlbE_eq` `tlbEEq`, `tlb_exact8` `tlbExact8`, `Hc08` `Hc08`, `HPC08` `HPC08`, `Hhit08` `Hhit08`,
`stvec8` `stvec8`, `Pra8` `Pra8`, `Ps08` `Ps08`, `va_ra8` `vaRa8`, `va_s08` `vaS08`, `HdaS_ra8`
`HdaSRa8`, `HdaL_ra8` `HdaLRa8`, `HdaS_s08` `HdaSS08`, `HdaL_s08` `HdaLS08`, `Hh_ra8` `HhRa8`,
`Hh_s08` `HhS08`, `uPra8` `uPra8`, `uPs08` `uPs08`, `Hpr_ra8` `HprRa8`, `Hpr_s08` `HprS08`,
`Hnt_ra8` `HntRa8`, `Hnt_s08` `HntS08`, `Hslots8` `Hslots8`, `ret8` `ret8`, `stv8` `stv8`,
`uint9_inj` `uint9Inj`, `pte_valid_0` `pteValid0`, `canon_eq` `canonEq`, `fetch_pa_unsigned`
`fetchPaUnsigned`, `hinj8` `hinj8`, `hstv8` `hstv8`, `wpd_mycpu_premises` `wpdMycpuPremises`,
`HΨmid8` `HΨmid8`.  Lean-only: `GD8` (Rocq notation), `mycpuTextFalse`, `Htxt8Rvc`, `chkT`,
`textAtT4`, `textAtT2`, `readsOffImg`, `entEqB`, `entEqBSound`, `tlbChk`, `tlbChkSound`, `dataD`,
`chkDS`, `chkDL`, `paRa8`, `paS08`, `hval8`, `hret8` (+ macro `ax_spin_e8f_txt2`).

**Dropped:** `Htxt8` (FALSE in this tree: `mycpuTextFalse`) and `cert_a` (needs `Htxt8`) —
deviation 1; the local instances `f8_pol`/`f8_G` (inlined); the Ltacs (deviation 4).  Rocq 82
definitions/lemmas + 2 instances; Lean 80 ported + 18 Lean-only (+ 1 macro).
-/
import Weak.AxSpinE8d
import Weak.AxSpinE8e

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. Memory, page table, satp -/

/-- Rocq `σ8`. -/
def AxSpinE8f.σ8 : ExecSt := ⟨AxSpinSpikeRun.spikeRegs0, AxSpinE8d.mem1, testDevs⟩

/-- Rocq `L0leaf`. -/
def AxSpinE8f.L0leaf : BitVec 64 := AxSpinSpikeRun.w64 (AxSpinSpikeRun.pteLeaf 0x80000)
/-- Rocq `L1leaf`. -/
def AxSpinE8f.L1leaf : BitVec 64 := AxSpinSpikeRun.w64 (AxSpinSpikeRun.pteLeaf 0x80001)
/-- Rocq `P2`. -/
def AxSpinE8f.P2 : BitVec 64 := AxSpinSpikeRun.w64 (AxSpinSpikeRun.pteNl AxSpinSpikeRun.sL1)
/-- Rocq `P1`. -/
def AxSpinE8f.P1 : BitVec 64 := AxSpinSpikeRun.w64 (AxSpinSpikeRun.pteNl AxSpinSpikeRun.sL0)

/-- Rocq `tT0`. -/
def AxSpinE8f.tT0 : PTree :=
  .node (BitVec.ofNat 44 AxSpinSpikeRun.sL0)
    (fun j => if j.toNat = 0 then AxSpinE8f.L0leaf else if j.toNat = 1 then AxSpinE8f.L1leaf
      else AxSpinSpikeRun.w64 0)
    (fun _ => none)
/-- Rocq `tT1`. -/
def AxSpinE8f.tT1 : PTree :=
  .node (BitVec.ofNat 44 AxSpinSpikeRun.sL1)
    (fun j => if j.toNat = 0 then AxSpinE8f.P1 else AxSpinSpikeRun.w64 0)
    (fun j => if j.toNat = 0 then some AxSpinE8f.tT0 else none)
/-- Rocq `tT`. -/
def AxSpinE8f.tT : PTree :=
  .node (BitVec.ofNat 44 AxSpinSpikeRun.sRoot)
    (fun j => if j.toNat = 2 then AxSpinE8f.P2 else AxSpinSpikeRun.w64 0)
    (fun j => if j.toNat = 2 then some AxSpinE8f.tT1 else none)
/-- Rocq `satp8`. -/
def AxSpinE8f.satp8 : BitVec 64 := AxSpinSpikeRun.w64 AxSpinSpikeRun.sSatp

theorem AxSpinE8f.Hmode8 : _get_Satp64_Mode (Mk_Satp64 AxSpinE8f.satp8) = 8#4 := by
  decide +kernel
theorem AxSpinE8f.Hasid8 : zero_extend (m := 16) (satp_to_asid AxSpinE8f.satp8) = 0#16 := by
  decide +kernel
theorem AxSpinE8f.Hppn8 : BitVec.setWidth 44 (satp_to_ppn AxSpinE8f.satp8) = AxSpinE8f.tT.base := by
  decide +kernel

/-- Rocq `vpnD`: the stack / return page. -/
def AxSpinE8f.vpnD : BitVec 27 := WeakKpt.svpnOf (AxSpinSpikeRun.w64 0x80000000)
/-- Rocq `vpnT`: mycpu's page. -/
def AxSpinE8f.vpnT : BitVec 27 := WeakKpt.svpnOf (AxSpinSpikeRun.w64 0x80001000)

theorem AxSpinE8f.mapsD :
    AxPtProt.ptreeMaps AxSpinE8f.tT AxSpinE8f.vpnD AxSpinE8f.P2 AxSpinE8f.P1 AxSpinE8f.L0leaf := by
  unfold AxPtProt.ptreeMaps pteValid ptePtr pteLeaf AxPtProt.pteNoNapot ptePbmt0
  refine ⟨AxSpinE8f.tT1, AxSpinE8f.tT0, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro s; ax_epi_ledger_krfl)
    | decide +kernel
    | ax_epi_ledger_krfl

theorem AxSpinE8f.mapsT :
    AxPtProt.ptreeMaps AxSpinE8f.tT AxSpinE8f.vpnT AxSpinE8f.P2 AxSpinE8f.P1 AxSpinE8f.L1leaf := by
  unfold AxPtProt.ptreeMaps pteValid ptePtr pteLeaf AxPtProt.pteNoNapot ptePbmt0
  refine ⟨AxSpinE8f.tT1, AxSpinE8f.tT0, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro s; ax_epi_ledger_krfl)
    | decide +kernel
    | ax_epi_ledger_krfl

/-- Rocq `ram_ok_z` (duplicated name). -/
theorem AxSpinE8f.ramOkZ (a : BitVec 64) (n : Nat) :
    (decide (ramBase ≤ a.toNat) && decide (a.toNat + n ≤ ramEnd)) = true → inRam a n := by
  intro H
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at H
  exact H

/-- Rocq `slot8` (duplicated name). -/
theorem AxSpinE8f.slot8 (a w : BitVec 64) :
    (∀ j : Nat, j < 8 → AxSpinE8f.σ8.mem (a + BitVec.ofNat 64 j) = some (nthByte (n := 8) w j)) →
    inRam a 8 → is_aligned_paddr (.Physaddr a) 8 = true →
    WeakWalkEff.ptSlotMem AxSpinE8f.σ8 a w :=
  fun Hb H1 H2 => ⟨Hb, H1, H2⟩

theorem AxSpinE8f.slot2D :
    WeakWalkEff.ptSlotMem AxSpinE8f.σ8 (AxPtProt.ptAddr2 AxSpinE8f.tT AxSpinE8f.vpnD) AxSpinE8f.P2 :=
  AxSpinE8f.slot8 _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem AxSpinE8f.slot1D :
    WeakWalkEff.ptSlotMem AxSpinE8f.σ8 (AxPtProt.ptAddr1 AxSpinE8f.P2 AxSpinE8f.vpnD) AxSpinE8f.P1 :=
  AxSpinE8f.slot8 _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem AxSpinE8f.slot0D :
    WeakWalkEff.ptSlotMem AxSpinE8f.σ8 (AxPtProt.ptAddr0 AxSpinE8f.P1 AxSpinE8f.vpnD)
      AxSpinE8f.L0leaf :=
  AxSpinE8f.slot8 _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem AxSpinE8f.slot2T :
    WeakWalkEff.ptSlotMem AxSpinE8f.σ8 (AxPtProt.ptAddr2 AxSpinE8f.tT AxSpinE8f.vpnT) AxSpinE8f.P2 :=
  AxSpinE8f.slot8 _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem AxSpinE8f.slot1T :
    WeakWalkEff.ptSlotMem AxSpinE8f.σ8 (AxPtProt.ptAddr1 AxSpinE8f.P2 AxSpinE8f.vpnT) AxSpinE8f.P1 :=
  AxSpinE8f.slot8 _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem AxSpinE8f.slot0T :
    WeakWalkEff.ptSlotMem AxSpinE8f.σ8 (AxPtProt.ptAddr0 AxSpinE8f.P1 AxSpinE8f.vpnT)
      AxSpinE8f.L1leaf :=
  AxSpinE8f.slot8 _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! # 2. `mycpuText` -/

/-- Rocq `rd32`: the little-endian 4-byte word at `a` in `σ8` (deviation 3). -/
def AxSpinE8f.rd32 (a : BitVec 64) : BitVec 32 :=
  let b := fun j : Nat => (AxSpinE8f.σ8.mem (a + BitVec.ofNat 64 j)).getD 0#8
  b 3 ++ b 2 ++ b 1 ++ b 0

/-- (Lean-only) the leaf's fetch checks. -/
theorem AxSpinE8f.chkT : ∀ mxr dosum : Bool,
    pteCheckOk (.InstructionFetch ()) .Supervisor mxr dosum AxSpinE8f.L1leaf := by
  intro mxr dosum s
  cases mxr <;> cases dosum <;> ax_epi_ledger_krfl

/-- (Lean-only, Rocq `txt2`, the 4-aligned arm) `textAtS` on mycpu's page. -/
theorem AxSpinE8f.textAtT4 (pc : BitVec 64) (h : BitVec 16)
    (H : WeakKpt.svpnOf pc = AxSpinE8f.vpnT ∧
      (pc != sign_extend (m := 64) (Sail.BitVec.extractLsb pc 38 0)) = false ∧
      (Sail.BitVec.access pc 0 != 0#1) = false ∧ isRVC h = true ∧
      is_aligned_vaddr (.Virtaddr pc) 4 = true ∧
      Sail.BitVec.extractLsb (AxSpinE8f.rd32 (AxSpinE6.fetchPa AxSpinE8f.L1leaf pc)) 15 0 = h ∧
      inRam (AxSpinE6.fetchPa AxSpinE8f.L1leaf pc) 4 ∧
      is_aligned_paddr (.Physaddr (AxSpinE6.fetchPa AxSpinE8f.L1leaf pc)) 4 = true ∧
      (∀ j, j < 4 → AxSpinE8f.σ8.mem (AxSpinE6.fetchPa AxSpinE8f.L1leaf pc + BitVec.ofNat 64 j) =
        some (nthByte (n := 4) (AxSpinE8f.rd32 (AxSpinE6.fetchPa AxSpinE8f.L1leaf pc)) j))) :
    textAtS AxSpinE8f.σ8 AxSpinE8f.tT pc h := by
  obtain ⟨hv, hc, hb0, hrvc, hal, hlo, hr, ha, hb⟩ := H
  unfold textAtS
  rw [hv]
  exact ⟨AxSpinE8f.P2, AxSpinE8f.P1, AxSpinE8f.L1leaf, AxSpinE6.fetchPa AxSpinE8f.L1leaf pc,
    AxSpinE8f.mapsT, AxSpinE8f.slot2T, AxSpinE8f.slot1T, AxSpinE8f.slot0T, AxSpinE8f.chkT,
    by decide +kernel, by unfold ptePbmt0; decide +kernel, hc, rfl, hb0, hrvc,
    by rw [if_pos hal]; exact ⟨_, hlo, hr, ha, hb⟩⟩

/-- (Lean-only, Rocq `txt2`, the 2-aligned arm) `textAtS` on mycpu's page. -/
theorem AxSpinE8f.textAtT2 (pc : BitVec 64) (h : BitVec 16)
    (H : WeakKpt.svpnOf pc = AxSpinE8f.vpnT ∧
      (pc != sign_extend (m := 64) (Sail.BitVec.extractLsb pc 38 0)) = false ∧
      (Sail.BitVec.access pc 0 != 0#1) = false ∧ isRVC h = true ∧
      is_aligned_vaddr (.Virtaddr pc) 4 = false ∧
      (Sail.BitVec.access pc 1 != 0#1) = true ∧
      inRam (AxSpinE6.fetchPa AxSpinE8f.L1leaf pc) 2 ∧
      is_aligned_paddr (.Physaddr (AxSpinE6.fetchPa AxSpinE8f.L1leaf pc)) 2 = true ∧
      (∀ j, j < 2 → AxSpinE8f.σ8.mem (AxSpinE6.fetchPa AxSpinE8f.L1leaf pc + BitVec.ofNat 64 j) =
        some (nthByte (n := 2) h j))) :
    textAtS AxSpinE8f.σ8 AxSpinE8f.tT pc h := by
  obtain ⟨hv, hc, hb0, hrvc, hal, h1, hr, ha, hb⟩ := H
  unfold textAtS
  rw [hv]
  exact ⟨AxSpinE8f.P2, AxSpinE8f.P1, AxSpinE8f.L1leaf, AxSpinE6.fetchPa AxSpinE8f.L1leaf pc,
    AxSpinE8f.mapsT, AxSpinE8f.slot2T, AxSpinE8f.slot1T, AxSpinE8f.slot0T, AxSpinE8f.chkT,
    by decide +kernel, by unfold ptePbmt0; decide +kernel, hc, rfl, hb0, hrvc,
    by rw [if_neg (by rw [hal]; decide)]; exact ⟨h1, hr, ha, hb⟩⟩

/-- (Lean-only, Rocq `txt2`) -/
local macro "ax_spin_e8f_txt2" : tactic => `(tactic|
  first
  | exact AxSpinE8f.textAtT4 _ _ (by decide +kernel)
  | exact AxSpinE8f.textAtT2 _ _ (by decide +kernel))

/-- (Lean-only, deviation 1) the twelve COMPRESSED words of `mycpuText` hold at the instance. -/
theorem AxSpinE8f.Htxt8Rvc :
    textAtS AxSpinE8f.σ8 AxSpinE8f.tT (pcm 0x00) (AxSpinE7.hw 0x1141) ∧
    textAtS AxSpinE8f.σ8 AxSpinE8f.tT (pcm 0x02) (AxSpinE7.hw 0xe406) ∧
    textAtS AxSpinE8f.σ8 AxSpinE8f.tT (pcm 0x04) (AxSpinE7.hw 0xe022) ∧
    textAtS AxSpinE8f.σ8 AxSpinE8f.tT (pcm 0x06) (AxSpinE7.hw 0x0800) ∧
    textAtS AxSpinE8f.σ8 AxSpinE8f.tT (pcm 0x08) (AxSpinE7.hw 0x8792) ∧
    textAtS AxSpinE8f.σ8 AxSpinE8f.tT (pcm 0x0a) (AxSpinE7.hw 0x2781) ∧
    textAtS AxSpinE8f.σ8 AxSpinE8f.tT (pcm 0x0c) (AxSpinE7.hw 0x079e) ∧
    textAtS AxSpinE8f.σ8 AxSpinE8f.tT (pcm 0x16) (AxSpinE7.hw 0x953e) ∧
    textAtS AxSpinE8f.σ8 AxSpinE8f.tT (pcm 0x18) (AxSpinE7.hw 0x60a2) ∧
    textAtS AxSpinE8f.σ8 AxSpinE8f.tT (pcm 0x1a) (AxSpinE7.hw 0x6402) ∧
    textAtS AxSpinE8f.σ8 AxSpinE8f.tT (pcm 0x1c) (AxSpinE7.hw 0x0141) ∧
    textAtS AxSpinE8f.σ8 AxSpinE8f.tT (pcm 0x1e) (AxSpinE7.hw 0x8082) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ax_spin_e8f_txt2

/-- (Lean-only, THE FINDING, deviation 1) `mycpuText` is UNSATISFIABLE in this tree: the two
4-byte words sit at `pcm 0x0e` = 0x8000196a and `pcm 0x12` = 0x8000196e (kernel drift: `mycpu` =
0x8000195c), which are 2 mod 4, while `textAt4S` demands `is_aligned_vaddr pc 4`. -/
theorem AxSpinE8f.mycpuTextFalse (σi : ExecSt) (T : PTree) : ¬ mycpuText σi T := by
  intro H
  obtain ⟨-, -, -, -, -, -, -, ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, Hal, -⟩, -⟩ := H
  exact absurd Hal (by decide +kernel)

/-! # 3. The graph -/

/-- Rocq `img8`. -/
def AxSpinE8f.img8 (a : Int) : BitVec 8 := (imgS AxSpinE8f.σ8 a).getD 0#8
/-- Rocq `il8` (deviation 1: the row's 5 memory items). -/
def AxSpinE8f.il8 : List Geid := (List.range 5).map fun k => (0, k)
/-- Rocq `GT8`. -/
def AxSpinE8f.GT8 : GdexecT := graphOfSc AxSpinE8f.img8 [AxSpinE8d.rowM] AxSpinE8f.il8 []
/-- Rocq's notation `GD8`. -/
abbrev AxSpinE8f.GD8 : Gdexec := gtAdGd AxSpinE8f.GT8

theorem AxSpinE8f.GT8Inputs : scInputsOkB [AxSpinE8d.rowM] AxSpinE8f.il8 [] = true := by
  decide +kernel

theorem AxSpinE8f.Hcons8 : rvwmoCatConsistent AxSpinE8f.GD8 :=
  catTAd _ (graphOfScCatT _ _ _ _ AxSpinE8f.GT8Inputs)

/-- Rocq `growG` (frozen, as Rocq's `Eval vm_compute`): the graph's row of hart 0 — `rowM`
with the reads' sources filled in. -/
def AxSpinE8f.growG : List Lbl :=
  [.LStore false 0x80000ff8 (AxSpinE8d.b8 AxSpinE8d.retOn) .WCplain,
   .LStore false 0x80000ff0 (AxSpinE8d.b8 0) .WCplain,
   .LLoad false 0x80000ff8 [1, 1, 1, 1, 1, 1, 1, 1] (AxSpinE8d.b8 AxSpinE8d.retOn),
   .LLoad false 0x80000ff0 [2, 2, 2, 2, 2, 2, 2, 2] (AxSpinE8d.b8 0),
   .LLoad false 0x80000ff8 [1, 1, 1, 1, 1, 1, 1, 1] (AxSpinE8d.b8 AxSpinE8d.retOn)]

theorem AxSpinE8f.grow8 : AxOpsem.grow AxSpinE8f.GD8 0 = AxSpinE8f.growG := by decide +kernel

/-- Rocq `Pra8`. -/
def AxSpinE8f.Pra8 : BitVec 64 := AxSpinSpikeRun.w64 0x80000ff8
/-- Rocq `Ps08`. -/
def AxSpinE8f.Ps08 : BitVec 64 := AxSpinSpikeRun.w64 0x80000ff0

theorem AxSpinE8f.uPra8 : paZ AxSpinE8f.Pra8 = 0x80000ff8 := by decide +kernel
theorem AxSpinE8f.uPs08 : paZ AxSpinE8f.Ps08 = 0x80000ff0 := by decide +kernel

theorem AxSpinE8f.Hrow8 :
    RowMycpu 0 (AxOpsem.grow AxSpinE8f.GD8 0) (paZ AxSpinE8f.Pra8) (paZ AxSpinE8f.Ps08) := by
  rw [AxSpinE8f.grow8, AxSpinE8f.uPra8, AxSpinE8f.uPs08]
  refine ⟨by decide, ?_⟩
  intro j hj
  match j, hj with
  | 0, _ => exact ⟨_, rfl, _, _, rfl, rfl⟩
  | 1, _ => exact ⟨_, rfl, _, _, rfl, rfl⟩
  | 2, _ => exact ⟨_, rfl, false, rfl⟩
  | 3, _ => exact ⟨_, rfl, false, rfl⟩

/-- Rocq `row_forall`. -/
theorem AxSpinE8f.rowForall (P : Lbl → Prop) (row : List Lbl) :
    (∀ x, x ∈ row → P x) → ∀ (k : Nat) (lb : Lbl), row[k]? = some lb → P lb :=
  fun H _ _ Hk => H _ (List.mem_of_getElem? Hk)

theorem AxSpinE8f.Hw8_8 : rowW8 (AxOpsem.grow AxSpinE8f.GD8 0) := by
  unfold rowW8
  rw [AxSpinE8f.grow8]
  intro k lb rl b m Hk
  refine AxSpinE8f.rowForall (fun lb => ∀ rl b m, aidentWr (aident lb) = some (rl, b, m) → m ≤ 8)
    _ ?_ k lb Hk rl b m
  intro x Hx rl b m H
  simp only [AxSpinE8f.growG, List.mem_cons, List.not_mem_nil, or_false] at Hx
  rcases Hx with rfl | rfl | rfl | rfl | rfl <;>
    simp only [aident, aidentWr, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at H
  · obtain ⟨-, -, rfl⟩ := H; decide
  · obtain ⟨-, -, rfl⟩ := H; decide

theorem AxSpinE8f.noRmw8_8 (pa : Int) : noRmw8 (AxOpsem.grow AxSpinE8f.GD8 0) pa := by
  unfold noRmw8
  rw [AxSpinE8f.grow8]
  intro k lb aq rl n Hk
  refine AxSpinE8f.rowForall (fun lb => ∀ aq rl n, aident lb = .IRmw aq rl pa n → n ≠ 8)
    _ ?_ k lb Hk aq rl n
  intro x Hx aq rl n H
  simp only [AxSpinE8f.growG, List.mem_cons, List.not_mem_nil, or_false] at Hx
  rcases Hx with rfl | rfl | rfl | rfl | rfl <;> simp only [aident, reduceCtorEq] at H

/-- (Lean-only) no read of the row reads image bytes (the stack is not in the image). -/
theorem AxSpinE8f.readsOffImg : AxSpinE8f.growG.all (fun lb =>
    match aidentRd (aident lb) with
    | some (_, base, n) => (imgBytes (imgS AxSpinE8f.σ8) base n).isNone
    | none => true) = true := by decide +kernel

/-- Rocq `Hfix8`: the image (WITHOUT the stack bytes) fixes every read of it. -/
theorem AxSpinE8f.Hfix8 : textFixed AxSpinE8f.GD8 0 (imgS AxSpinE8f.σ8) := by
  refine ⟨?_, ?_⟩
  · intro a b Hb
    show some (AxSpinE8f.img8 a) = some b
    unfold AxSpinE8f.img8
    rw [Hb]
    rfl
  · intro k lb aq base n vs Hlb Hrd Hvs
    rw [AxSpinE8f.grow8] at Hlb
    have H := List.all_eq_true.1 AxSpinE8f.readsOffImg lb (List.mem_of_getElem? Hlb)
    rw [Hrd] at H
    dsimp only at H
    rw [Hvs] at H
    cases H

/-! # 4. The layout -/

/-- Rocq `stk8`. -/
def AxSpinE8f.stk8 : GSet Int := LawfulSet.ofList (clRange 0x80000ff0 16)
/-- Rocq `text8`. -/
def AxSpinE8f.text8 (a : Int) : Prop :=
  (0x80001000 ≤ a ∧ a < 0x80002000) ∨ (0x80000000 ≤ a ∧ a < 0x80000004)
/-- Rocq `ro8`. -/
def AxSpinE8f.ro8 (a : Int) : Prop := AxSpinE8f.text8 a ∨ (0x80010000 ≤ a ∧ a < 0x80013000)
/-- Rocq `L8`. -/
def AxSpinE8f.L8 : Xlay where
  xlLk := 0x80003000
  xlNp := 0x80003100
  xlHarts := [0]
  xlStk := fun j => if j = 0 then AxSpinE8f.stk8 else ∅
  xlCpuf := fun _ => ∅
  xlRo := AxSpinE8f.ro8
  xlText := AxSpinE8f.text8

/-- Rocq `cl_range_bound`. -/
theorem AxSpinE8f.clRangeBound (b : Int) (n : Nat) (a : Int) :
    a ∈ clRange b n → b ≤ a ∧ a < b + (n : Int) := (inClr a b n).1

theorem AxSpinE8f.priv8 (a : Int) (j : Agent) :
    priv AxSpinE8f.L8 a j → j = 0 ∧ 0x80000ff0 ≤ a ∧ a < 0x80001000 := by
  rintro ⟨Hj, Ha⟩
  have Hj' : j ∈ [0] := Hj
  rw [List.mem_singleton] at Hj'
  subst Hj'
  refine ⟨rfl, ?_⟩
  rcases Ha with Ha | Ha
  · have Ha' : a ∈ AxSpinE8f.stk8 := by simpa [AxSpinE8f.L8] using Ha
    have := AxSpinE8f.clRangeBound _ _ _ (LawfulSet.mem_ofList.2 Ha')
    omega
  · exact (notElemOfEmpty Ha).elim

theorem AxSpinE8f.XO8 (a : Int) :
    a ∈ XO AxSpinE8f.L8 →
      (0x80003010 ≤ a ∧ a < 0x80003018) ∨ (0x80003100 ≤ a ∧ a < 0x80003104) := by
  unfold XO
  rw [elemOfUnion, ← LawfulSet.mem_ofList, ← LawfulSet.mem_ofList]
  rintro (Ha | Ha)
  · have := AxSpinE8f.clRangeBound _ _ _ Ha
    simp only [AxSpinE8f.L8] at this
    omega
  · have := AxSpinE8f.clRangeBound _ _ _ Ha
    simp only [AxSpinE8f.L8] at this
    omega

theorem AxSpinE8f.lwb8 (a : Int) : a ∈ lwb AxSpinE8f.L8 → 0x80003000 ≤ a ∧ a < 0x80003004 := by
  intro Ha
  have := AxSpinE8f.clRangeBound _ _ _ Ha
  simp only [AxSpinE8f.L8] at this
  omega

theorem AxSpinE8f.HL8 : xlayOk AxSpinE8f.L8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold lwb clb npb
    simp only [AxSpinE8f.L8]
    decide +kernel
  · intro a j Hp
    obtain ⟨-, Ha⟩ := AxSpinE8f.priv8 a j Hp
    refine ⟨fun H => ?_, fun H => ?_⟩
    · have := AxSpinE8f.lwb8 a H
      omega
    · have := AxSpinE8f.XO8 a H
      omega
  · intro a j1 j2 H1 H2
    rw [(AxSpinE8f.priv8 a j1 H1).1, (AxSpinE8f.priv8 a j2 H2).1]
  · intro a j Hro Hw
    have Hro' : AxSpinE8f.ro8 a := Hro
    unfold AxSpinE8f.ro8 AxSpinE8f.text8 at Hro'
    rcases Hw with Hw | Hw | Hw
    · have := AxSpinE8f.lwb8 a Hw
      omega
    · have := AxSpinE8f.XO8 a Hw
      omega
    · have := AxSpinE8f.priv8 a j Hw
      omega
  · decide
  · intro i Hi
    have Hi' : i ∈ [0] := Hi
    rw [List.mem_singleton] at Hi'
    subst Hi'
    decide

/-! # 5. The entry state `rsE` (a drive result: kernel evaluation only) -/

/-- Rocq `tlbE` (Rocq froze it by `Eval vm_compute`; here it is the plain projection, deviation
4). -/
noncomputable def AxSpinE8f.tlbE : Vector (Option TLB_Entry) (2 ^ 6) := AxSpinE8d.rsE .tlb

theorem AxSpinE8f.tlbEEq : AxSpinE8d.rsE .tlb = AxSpinE8f.tlbE := rfl

/-- (Lean-only, deviation 4) field-wise boolean equality of TLB entries (`TLB_Entry` derives
only `BEq`). -/
def AxSpinE8f.entEqB (a b : TLB_Entry) : Bool :=
  a.asid == b.asid && a.global == b.global && a.vpn == b.vpn && a.levelMask == b.levelMask &&
    a.ppn == b.ppn && a.pte == b.pte &&
    (match a.pteAddr, b.pteAddr with | .Physaddr x, .Physaddr y => x == y)

theorem AxSpinE8f.entEqBSound (a b : TLB_Entry) : AxSpinE8f.entEqB a b = true → a = b := by
  obtain ⟨a1, a2, a3, a4, a5, a6, ⟨a7⟩⟩ := a
  obtain ⟨b1, b2, b3, b4, b5, b6, ⟨b7⟩⟩ := b
  simp only [AxSpinE8f.entEqB, Bool.and_eq_true, beq_iff_eq]
  rintro ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
  rfl

/-- (Lean-only, deviation 4) the TLB checker: every filled slot holds the exact walk entry of
page `vpnD` or `vpnT` at that page's hash. -/
def AxSpinE8f.tlbChk (v : Vector (Option TLB_Entry) (2 ^ 6)) : Bool :=
  (List.range 64).all fun j =>
    match v[j]! with
    | none => true
    | some ent =>
      (tlb_hash 39 AxSpinE8f.vpnD == j &&
        AxSpinE8f.entEqB ent (uWalkEntry AxSpinE8f.vpnD AxSpinE8f.P2 AxSpinE8f.P1 AxSpinE8f.L0leaf 0#16)) ||
      (tlb_hash 39 AxSpinE8f.vpnT == j &&
        AxSpinE8f.entEqB ent (uWalkEntry AxSpinE8f.vpnT AxSpinE8f.P2 AxSpinE8f.P1 AxSpinE8f.L1leaf 0#16))

theorem AxSpinE8f.tlbChkSound (v : Vector (Option TLB_Entry) (2 ^ 6)) :
    AxSpinE8f.tlbChk v = true → tlbExact AxSpinE8f.tT v := by
  intro H vpn' ent hget
  have hj : tlb_hash 39 vpn' < 64 := AxPtProt.tlbHashLt vpn'
  have H1 := List.all_eq_true.1 H (tlb_hash 39 vpn') (List.mem_range.2 hj)
  rw [hget] at H1
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at H1
  rcases H1 with ⟨hh, he⟩ | ⟨hh, he⟩
  · exact ⟨_, _, _, _, AxSpinE8f.mapsD, hh, AxSpinE8f.entEqBSound _ _ he⟩
  · exact ⟨_, _, _, _, AxSpinE8f.mapsT, hh, AxSpinE8f.entEqBSound _ _ he⟩

set_option maxHeartbeats 0 in
theorem AxSpinE8f.tlbExact8 : tlbExact AxSpinE8f.tT (AxSpinE8d.rsE .tlb) :=
  AxSpinE8f.tlbChkSound _ (by decide +kernel)

set_option maxHeartbeats 0 in
theorem AxSpinE8f.Hc08 : ctrlOkSW AxSpinE8f.tT AxSpinE8f.satp8 AxSpinE8d.rsE := by
  unfold ctrlOkSW ctrlOkS AxSpineOk6.pmpOk AxSpineOk6.sconfMsFacts pmpW
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_,
    AxSpinE8f.tlbExact8, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals first | decide +kernel | ax_epi_ledger_krfl

set_option maxHeartbeats 0 in
theorem AxSpinE8f.HPC08 : AxSpinE8d.rsE .PC = pcm 0x00 := by decide +kernel
set_option maxHeartbeats 0 in
theorem AxSpinE8f.Hhit08 : hitW AxSpinE8d.rsE (pcm 0x00) := by unfold hitW; decide +kernel
set_option maxHeartbeats 0 in
theorem AxSpinE8f.stvec8 : AxSpinE8d.rsE .stvec = AxSpinSpikeRun.w64 0 := by decide +kernel

/-! # 6. The two stack slots -/

set_option maxHeartbeats 0 in
theorem AxSpinE8f.vaRa8 : AxSpinE8.vaRa AxSpinE8d.rsE = AxSpinE8f.Pra8 := by decide +kernel
set_option maxHeartbeats 0 in
theorem AxSpinE8f.vaS08 : AxSpinE8.vaS0 AxSpinE8d.rsE = AxSpinE8f.Ps08 := by decide +kernel

/-- (Lean-only, Rocq `data_tac`) `dataAtS` on the stack page. -/
theorem AxSpinE8f.dataD (acc : MemoryAccessType mem_payload) (va : BitVec 64)
    (Hchk : ∀ mxr dosum : Bool, pteCheckOk acc .Supervisor mxr dosum AxSpinE8f.L0leaf)
    (H : WeakKpt.svpnOf va = AxSpinE8f.vpnD ∧ update_PTE_Bits AxSpinE8f.L0leaf acc = none ∧
      (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false ∧
      inRam (AxSpinE6.fetchPa AxSpinE8f.L0leaf va) 8 ∧
      is_aligned_vaddr (.Virtaddr va) 8 = true ∧
      is_aligned_paddr (.Physaddr (AxSpinE6.fetchPa AxSpinE8f.L0leaf va)) 8 = true) :
    dataAtS AxSpinE8f.σ8 AxSpinE8f.tT acc va 8 (AxSpinE6.fetchPa AxSpinE8f.L0leaf va) := by
  obtain ⟨hv, hu, hc, hr, ha, hp⟩ := H
  unfold dataAtS
  rw [hv]
  exact ⟨AxSpinE8f.P2, AxSpinE8f.P1, AxSpinE8f.L0leaf, AxSpinE8f.mapsD, AxSpinE8f.slot2D,
    AxSpinE8f.slot1D, AxSpinE8f.slot0D, Hchk, hu, by unfold ptePbmt0; decide +kernel, hc, rfl,
    hr, ha, hp⟩

theorem AxSpinE8f.chkDS : ∀ mxr dosum : Bool,
    pteCheckOk (.Store .Data) .Supervisor mxr dosum AxSpinE8f.L0leaf := by
  intro mxr dosum s
  cases mxr <;> cases dosum <;> ax_epi_ledger_krfl
theorem AxSpinE8f.chkDL : ∀ mxr dosum : Bool,
    pteCheckOk (.Load .Data) .Supervisor mxr dosum AxSpinE8f.L0leaf := by
  intro mxr dosum s
  cases mxr <;> cases dosum <;> ax_epi_ledger_krfl

theorem AxSpinE8f.paRa8 : AxSpinE6.fetchPa AxSpinE8f.L0leaf AxSpinE8f.Pra8 = AxSpinE8f.Pra8 := by
  decide +kernel
theorem AxSpinE8f.paS08 : AxSpinE6.fetchPa AxSpinE8f.L0leaf AxSpinE8f.Ps08 = AxSpinE8f.Ps08 := by
  decide +kernel

theorem AxSpinE8f.HdaSRa8 :
    dataAtS AxSpinE8f.σ8 AxSpinE8f.tT (.Store .Data) (AxSpinE8.vaRa AxSpinE8d.rsE) 8 AxSpinE8f.Pra8 := by
  rw [AxSpinE8f.vaRa8, ← AxSpinE8f.paRa8]
  exact AxSpinE8f.dataD _ _ AxSpinE8f.chkDS (by decide +kernel)
theorem AxSpinE8f.HdaLRa8 :
    dataAtS AxSpinE8f.σ8 AxSpinE8f.tT (.Load .Data) (AxSpinE8.vaRa AxSpinE8d.rsE) 8 AxSpinE8f.Pra8 := by
  rw [AxSpinE8f.vaRa8, ← AxSpinE8f.paRa8]
  exact AxSpinE8f.dataD _ _ AxSpinE8f.chkDL (by decide +kernel)
theorem AxSpinE8f.HdaSS08 :
    dataAtS AxSpinE8f.σ8 AxSpinE8f.tT (.Store .Data) (AxSpinE8.vaS0 AxSpinE8d.rsE) 8 AxSpinE8f.Ps08 := by
  rw [AxSpinE8f.vaS08, ← AxSpinE8f.paS08]
  exact AxSpinE8f.dataD _ _ AxSpinE8f.chkDS (by decide +kernel)
theorem AxSpinE8f.HdaLS08 :
    dataAtS AxSpinE8f.σ8 AxSpinE8f.tT (.Load .Data) (AxSpinE8.vaS0 AxSpinE8d.rsE) 8 AxSpinE8f.Ps08 := by
  rw [AxSpinE8f.vaS08, ← AxSpinE8f.paS08]
  exact AxSpinE8f.dataD _ _ AxSpinE8f.chkDL (by decide +kernel)

set_option maxHeartbeats 0 in
theorem AxSpinE8f.HhRa8 : hitW AxSpinE8d.rsE (AxSpinE8.vaRa AxSpinE8d.rsE) := by
  rw [AxSpinE8f.vaRa8]; unfold hitW; decide +kernel
set_option maxHeartbeats 0 in
theorem AxSpinE8f.HhS08 : hitW AxSpinE8d.rsE (AxSpinE8.vaS0 AxSpinE8d.rsE) := by
  rw [AxSpinE8f.vaS08]; unfold hitW; decide +kernel

theorem AxSpinE8f.HprRa8 : ∀ j : Nat, j < 8 → priv AxSpinE8f.L8 (paZ AxSpinE8f.Pra8 + (j : Int)) 0 := by
  intro j hj
  rw [AxSpinE8f.uPra8]
  refine ⟨List.mem_singleton.2 rfl, Or.inl ?_⟩
  show _ ∈ (if (0 : Agent) = 0 then AxSpinE8f.stk8 else ∅)
  rw [if_pos rfl]
  exact LawfulSet.mem_ofList.1 ((inClr _ _ _).2 (by omega))
theorem AxSpinE8f.HprS08 : ∀ j : Nat, j < 8 → priv AxSpinE8f.L8 (paZ AxSpinE8f.Ps08 + (j : Int)) 0 := by
  intro j hj
  rw [AxSpinE8f.uPs08]
  refine ⟨List.mem_singleton.2 rfl, Or.inl ?_⟩
  show _ ∈ (if (0 : Agent) = 0 then AxSpinE8f.stk8 else ∅)
  rw [if_pos rfl]
  exact LawfulSet.mem_ofList.1 ((inClr _ _ _).2 (by omega))
theorem AxSpinE8f.HntRa8 : ¬ AxSpinE8f.L8.xlText (paZ AxSpinE8f.Pra8) := by
  rw [AxSpinE8f.uPra8]
  show ¬ AxSpinE8f.text8 _
  unfold AxSpinE8f.text8
  omega
theorem AxSpinE8f.HntS08 : ¬ AxSpinE8f.L8.xlText (paZ AxSpinE8f.Ps08) := by
  rw [AxSpinE8f.uPs08]
  show ¬ AxSpinE8f.text8 _
  unfold AxSpinE8f.text8
  omega
theorem AxSpinE8f.Hslots8 :
    paZ AxSpinE8f.Ps08 + 8 ≤ paZ AxSpinE8f.Pra8 ∨ paZ AxSpinE8f.Pra8 + 8 ≤ paZ AxSpinE8f.Ps08 := by
  rw [AxSpinE8f.uPra8, AxSpinE8f.uPs08]
  omega

/-! # 7. The return page: CANONICAL `Hinj`, `Hstv` (no consumer under Q20', deviation 2) -/

/-- Rocq `ret8`. -/
def AxSpinE8f.ret8 : BitVec 64 := AxSpinSpikeRun.w64 0x80000000
/-- Rocq `stv8`. -/
def AxSpinE8f.stv8 : BitVec 64 := AxSpinSpikeRun.w64 0

theorem AxSpinE8f.uint9Inj (x y : BitVec 9) : x.toNat = y.toNat → x = y := BitVec.eq_of_toNat_eq

theorem AxSpinE8f.pteValid0 : ¬ pteValid (AxSpinSpikeRun.w64 0) := by
  intro H
  have h1 := congrArg (Option.map Prod.fst) (H AxSpinE8f.σ8)
  have h2 : (exec (pte_is_invalid (Mk_PTE_Flags (Sail.BitVec.extractLsb (AxSpinSpikeRun.w64 0) 7 0))
      (ext_bits_of_PTE (AxSpinSpikeRun.w64 0))) AxSpinE8f.σ8).map Prod.fst = some true := by
    decide +kernel
  rw [h1] at h2
  cases h2

/-- Rocq `canon_eq`: a canonical VA is the sign extension of its low 39 bits. -/
theorem AxSpinE8f.canonEq (v : BitVec 64) :
    vaCanon v → v = sign_extend (m := 64) (Sail.BitVec.extractLsb v 38 0) := by
  unfold vaCanon
  intro H
  simpa [bne_iff_ne] using H

/-- Rocq `fetch_pa_unsigned`. -/
theorem AxSpinE8f.fetchPaUnsigned (pte v : BitVec 64) :
    ((AxSpinE6.fetchPa pte v).toNat : Int) = ((ppn0 pte).toNat : Int) * 4096 +
      (v.toNat : Int) % 4096 := by
  have hlo := lo11Unsigned v
  have hlt := (Sail.BitVec.extractLsb v 11 0).isLt
  have hp := (ppn0 pte).isLt
  unfold AxSpinE6.fetchPa
  show (((BitVec.setWidth 64 (ppn0 pte ++ Sail.BitVec.extractLsb v 11 0)).toNat : Nat) : Int) = _
  rw [BitVec.toNat_setWidth, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt hlt,
    Nat.shiftLeft_eq]
  omega

/-- Rocq `hinj8`: a canonical VA translating to 0x80000000 under `tT` IS 0x80000000. -/
theorem AxSpinE8f.hinj8 : ∀ v p2 p1 pte, vaCanon v →
    AxPtProt.ptreeMaps AxSpinE8f.tT (WeakKpt.svpnOf v) p2 p1 pte →
    paZ (AxSpinE6.fetchPa pte v) = 0x80000000 → v = AxSpinE8f.ret8 := by
  rintro v p2 p1 pte Hcv ⟨c1, c0, Hk2, Hk1, -, -, He0, -, -, -, -, -, -, Hv0, -⟩ Hpa
  simp only [AxSpinE8f.tT, PTree.kids] at Hk2
  by_cases E2 : (AxPtProt.vpnIdx 2 (WeakKpt.svpnOf v)).toNat = 2
  · rw [if_pos E2] at Hk2
    cases Hk2
    simp only [AxSpinE8f.tT1, PTree.kids] at Hk1
    by_cases E1 : (AxPtProt.vpnIdx 1 (WeakKpt.svpnOf v)).toNat = 0
    · rw [if_pos E1] at Hk1
      cases Hk1
      simp only [AxSpinE8f.tT0, PTree.ents] at He0
      have Hlo := Int.emod_nonneg (v.toNat : Int) (show (4096 : Int) ≠ 0 by decide)
      have Hlo' := Int.emod_lt_of_pos (v.toNat : Int) (show (0 : Int) < 4096 by decide)
      have Hpa' : ((AxSpinE6.fetchPa pte v).toNat : Int) = 0x80000000 := Hpa
      rw [AxSpinE8f.fetchPaUnsigned] at Hpa'
      by_cases E0 : (AxPtProt.vpnIdx 0 (WeakKpt.svpnOf v)).toNat = 0
      · rw [if_pos E0] at He0
        subst He0
        have Hp : ((ppn0 AxSpinE8f.L0leaf).toNat : Int) = 524288 := by decide +kernel
        rw [Hp] at Hpa'
        have Hv : WeakKpt.svpnOf v = AxSpinE8f.vpnD := by
          apply AxPtProt.vpnIdxInj <;> apply AxSpinE8f.uint9Inj
          · rw [E2]; decide +kernel
          · rw [E1]; decide +kernel
          · rw [E0]; decide +kernel
        have Hv' : ((WeakKpt.svpnOf v).toNat : Int) = (AxSpinE8f.vpnD.toNat : Int) := by rw [Hv]
        rw [svpnUnsigned, zShift39] at Hv'
        have HvD : ((AxSpinE8f.vpnD.toNat : Nat) : Int) = 524288 := by decide +kernel
        rw [HvD] at Hv'
        have Hm : (v.toNat : Int) % 549755813888 = 2147483648 := by omega
        rw [AxSpinE8f.canonEq v Hcv]
        have Hs : Sail.BitVec.extractLsb v 38 0 = Sail.BitVec.extractLsb AxSpinE8f.ret8 38 0 := by
          apply BitVec.eq_of_toNat_eq
          have h1 : ((Sail.BitVec.extractLsb v 38 0).toNat : Int) = (v.toNat : Int) % 549755813888 := by
            simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb'_toNat,
              Nat.shiftRight_eq_div_pow]
            omega
          have h2 : ((Sail.BitVec.extractLsb AxSpinE8f.ret8 38 0).toNat : Int) = 2147483648 := by
            decide +kernel
          omega
        rw [Hs]
        decide +kernel
      · rw [if_neg E0] at He0
        by_cases E0' : (AxPtProt.vpnIdx 0 (WeakKpt.svpnOf v)).toNat = 1
        · rw [if_pos E0'] at He0
          subst He0
          have Hp : ((ppn0 AxSpinE8f.L1leaf).toNat : Int) = 524289 := by decide +kernel
          rw [Hp] at Hpa'
          omega
        · rw [if_neg E0'] at He0
          subst He0
          exact absurd Hv0 AxSpinE8f.pteValid0
    · rw [if_neg E1] at Hk1
      cases Hk1
  · rw [if_neg E2] at Hk2
    cases Hk2

/-- Rocq `hstv8`: VA 0 (the trap vector) is unmapped. -/
theorem AxSpinE8f.hstv8 : ∀ p2 p1 pte,
    AxPtProt.ptreeMaps AxSpinE8f.tT (WeakKpt.svpnOf AxSpinE8f.stv8) p2 p1 pte →
    paZ (AxSpinE6.fetchPa pte AxSpinE8f.stv8) ≠ 0x80000000 := by
  rintro p2 p1 pte ⟨c1, c0, Hk2, -⟩
  simp only [AxSpinE8f.tT, PTree.kids] at Hk2
  rw [if_neg (by decide +kernel)] at Hk2
  cases Hk2

/-- (Lean-only, deviation 1) the Q20' value pin `Hval` at the instance. -/
theorem AxSpinE8f.hval8 :
    graphValue AxSpinE8f.GD8 (0, 0 + 2) = some (stBytes 8 AxSpinE8f.ret8) := by decide +kernel

/-- (Lean-only, deviation 1) `Hret`: the return address is 2-aligned. -/
theorem AxSpinE8f.hret8 : jalrTgt 0#12 AxSpinE8f.ret8 = AxSpinE8f.ret8 := by decide +kernel

/-! # 8. ALL PURE PREMISES AT ONCE (deviation 1: except `mycpuText`) -/

/-- Rocq `wpd_mycpu_premises`, restated for the Lean `wpdMycpu` (deviation 1): every pure
premise holds at the instance EXCEPT `Htxt : mycpuText σ8 tT`, which is unsatisfiable in this
tree (`AxSpinE8f.mycpuTextFalse`; its twelve compressed conjuncts hold, `AxSpinE8f.Htxt8Rvc`).
Rocq's `Hinj`/`Hstv` conjuncts (premises dropped from `wpdMycpu` by Q20') are replaced by the
Option V pins `Hval`/`Hret`; `hinj8`/`hstv8` are still proved above. -/
theorem AxSpinE8f.wpdMycpuPremises :
    xlayOk AxSpinE8f.L8 ∧ rvwmoCatConsistent AxSpinE8f.GD8 ∧
    _get_Satp64_Mode (Mk_Satp64 AxSpinE8f.satp8) = 8#4 ∧
    zero_extend (m := 16) (satp_to_asid AxSpinE8f.satp8) = 0#16 ∧
    BitVec.setWidth 44 (satp_to_ppn AxSpinE8f.satp8) = AxSpinE8f.tT.base ∧
    textFixed AxSpinE8f.GD8 0 (imgS AxSpinE8f.σ8) ∧
    (RowMycpu 0 (AxOpsem.grow AxSpinE8f.GD8 0) (paZ AxSpinE8f.Pra8) (paZ AxSpinE8f.Ps08) ∧
     rowW8 (AxOpsem.grow AxSpinE8f.GD8 0) ∧
     noRmw8 (AxOpsem.grow AxSpinE8f.GD8 0) (paZ AxSpinE8f.Pra8) ∧
     noRmw8 (AxOpsem.grow AxSpinE8f.GD8 0) (paZ AxSpinE8f.Ps08) ∧
     ctrlOkSW AxSpinE8f.tT AxSpinE8f.satp8 AxSpinE8d.rsE ∧ AxSpinE8d.rsE .PC = pcm 0x00 ∧
     hitW AxSpinE8d.rsE (pcm 0x00) ∧
     dataAtS AxSpinE8f.σ8 AxSpinE8f.tT (.Store .Data) (AxSpinE8.vaRa AxSpinE8d.rsE) 8 AxSpinE8f.Pra8 ∧
     dataAtS AxSpinE8f.σ8 AxSpinE8f.tT (.Load .Data) (AxSpinE8.vaRa AxSpinE8d.rsE) 8 AxSpinE8f.Pra8 ∧
     hitW AxSpinE8d.rsE (AxSpinE8.vaRa AxSpinE8d.rsE) ∧
     dataAtS AxSpinE8f.σ8 AxSpinE8f.tT (.Store .Data) (AxSpinE8.vaS0 AxSpinE8d.rsE) 8 AxSpinE8f.Ps08 ∧
     dataAtS AxSpinE8f.σ8 AxSpinE8f.tT (.Load .Data) (AxSpinE8.vaS0 AxSpinE8d.rsE) 8 AxSpinE8f.Ps08 ∧
     hitW AxSpinE8d.rsE (AxSpinE8.vaS0 AxSpinE8d.rsE) ∧
     (∀ j : Nat, j < 8 → priv AxSpinE8f.L8 (paZ AxSpinE8f.Pra8 + (j : Int)) 0) ∧
     ¬ AxSpinE8f.L8.xlText (paZ AxSpinE8f.Pra8) ∧
     (∀ j : Nat, j < 8 → priv AxSpinE8f.L8 (paZ AxSpinE8f.Ps08 + (j : Int)) 0) ∧
     ¬ AxSpinE8f.L8.xlText (paZ AxSpinE8f.Ps08) ∧
     (paZ AxSpinE8f.Ps08 + 8 ≤ paZ AxSpinE8f.Pra8 ∨ paZ AxSpinE8f.Pra8 + 8 ≤ paZ AxSpinE8f.Ps08) ∧
     graphValue AxSpinE8f.GD8 (0, 0 + 2) = some (stBytes 8 AxSpinE8f.ret8) ∧
     jalrTgt 0#12 AxSpinE8f.ret8 = AxSpinE8f.ret8) :=
  ⟨AxSpinE8f.HL8, AxSpinE8f.Hcons8, AxSpinE8f.Hmode8, AxSpinE8f.Hasid8, AxSpinE8f.Hppn8,
    AxSpinE8f.Hfix8, AxSpinE8f.Hrow8, AxSpinE8f.Hw8_8, AxSpinE8f.noRmw8_8 _,
    AxSpinE8f.noRmw8_8 _, AxSpinE8f.Hc08, AxSpinE8f.HPC08, AxSpinE8f.Hhit08, AxSpinE8f.HdaSRa8,
    AxSpinE8f.HdaLRa8, AxSpinE8f.HhRa8, AxSpinE8f.HdaSS08, AxSpinE8f.HdaLS08, AxSpinE8f.HhS08,
    AxSpinE8f.HprRa8, AxSpinE8f.HntRa8, AxSpinE8f.HprS08, AxSpinE8f.HntS08, AxSpinE8f.Hslots8,
    AxSpinE8f.hval8, AxSpinE8f.hret8⟩

/-! # 9. The post premise (`cert_a` DROPPED, deviation 1) -/

/-- Rocq `HΨmid8`. -/
theorem AxSpinE8f.HΨmid8 {GF : BundledGFunctors.{0,0,0}} [AxannotGS GF] [AxSpinX.Xv6G GF] (nm : Xv6N) :
    ∀ s, midState s → s.atK = (AxOpsem.grow AxSpinE8f.GD8 0).length →
      ⊢ @postLifting GF (AxSpinX2.xG AxSpinE8f.L8 AxSpinE8f.GT8 nm) (fun _ => iprop(True)) 0 s := by
  intro s _ _
  letI : AxirisG GF := AxSpinX2.xG AxSpinE8f.L8 AxSpinE8f.GT8 nm
  exact postLiftingTrue _ 0 s .rfl

end Weak
