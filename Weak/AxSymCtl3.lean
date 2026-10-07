/-
Weak: the CONCRETE page-table tree of `AxSmodeProbe` and the symbolic S-mode chain applied at
its state (slice-2a's open item).

Rocq: `iris/AxSymCtl3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 `pT`: the `PTree` describing the probe's 3-level Sv39 table (root ppn 0x80010 = `nvSRoot`,
L1 0x80011, L0 0x80012; VA = PA text page 0x80000000, data page 0x80001000).  `pTBase`, `pTMaps`
(the walk of `svpnOf 0x80000000` through the tree), `pTSlot2/1/0` (the three slots are bytes of
`nvST`'s memory).
§2 `pTTextAt`: `textAtS nvST pT (w64 sPc) 0x8506` — the symbolic fetch field's premise HOLDS at
the probe's text.  No padding twin is needed: `nvST` keeps the probe's bytes 0x81 0x00 at
sPc+2/+3, so the 4-byte fetch at the 4-aligned pc reads the word 0x00818506.
§3 `pTTextOk`: `textOkD` for `c.mv a0, ra` at sPc, for ALL regime states.
§4 `wpdCmvProbe`: `XGprWriteS` at the probe's boundary state with EVERY premise discharged
except the instance premises Htext/Hflow; `wpdCmvProbeGa2`: those discharged at `axGA2` (real
`protInv`, instance `blkGa2`) from the one graph fact `textFixed GD0 i (imgS nvST)`.
§5 `gpT`: a SMALL CONCRETE 1-hart graph whose hart-0 row is EXACTLY the cold-TLB fetch's graph
events (the root[2], L1[0], L0[0] walk reads, 8 B each; image = `imgS nvST`): `gpTTextFixed`,
`gpTCat` (rvwmoCatConsistent, by the checker), `gpTRowLen`.  `wpdCmvProbeGpT`: the symbolic
chain at the probe's state at `blkGa2 gpT` with the real `protInv` — NO premise left.
CAVEATS (as Rocq): the post is `Φ0` (= True; the register content is delivered to the
CONTINUATION, still an open WPd premise), so this is a PIPELINE MILESTONE (every symbolic premise
is satisfiable at a real S-mode state and a real consistent graph), not a closed program proof;
X does not report the row position, so nothing ties the WPd run to the row end.

Note: Rocq AxSymCtl3 does not import AxSymCtl (no `wpdBlockClosed`/budget content here); the
Q14 provisional rule does not arise.

## Deviations from Rocq

1. SPELLING (as `AxSpineOk8` deviation 1): `mword n` ↦ `BitVec n`, `w64` ↦ `AxEpiProbe.w64`,
   `s_pc`/`s_l1`/`s_l0`/`s_root` ↦ `sPc`/`AxSmodeProbe.sL1`/`sL0`/`sRoot`, `mword_of_int` ↦
   `BitVec.ofNat 44`, `Z.eqb (uint j) j0` ↦ `j.toNat = j0`, `autocast (satp_to_ppn …)` ↦
   `BitVec.setWidth 44 (satp_to_ppn …)` (as `XGprWriteS`'s `Hp`), `register_lookup PC rs` ↦
   `rs .PC`, `add_vec_int` ↦ `BitVec.addInt`, `regval_into_reg (blk_w1 …)` ↦ `blkW1 …`,
   `Z.eqb (uint r) (uint a05)` ↦ `r = a05`, `gpr` ↦ `AxSymEngine3.gpr`, `default [] o` ↦
   `o.getD []`.  `vm_compute` ↦ `decide +kernel` / kernel `Eq.refl` (`ax_epi_ledger_krfl`); the
   Ltacs `vr`/`byt`/`bytes8` are dropped.
2. `AxSymCtl3.ramOkZ` / `slotOf`: Lean's `ptSlotMem` asks `inRam a 8` (Rocq: `addr_is_ram a`
   and `addr_is_ram (a + 7)`), so `ramOkZ` concludes `inRam a n` from the boolean range test
   `ramBase ≤ a ∧ a + n ≤ ramEnd`, and `slotOf` takes one range premise (`inRam a 8`) in place
   of Rocq's two.
3. `exec_decode_pH` (Rocq: `rvc_oneshot`) goes through the decoder's READ-ONLY WALK
   (`MachCSL.runRead`, kernel-evaluated) at the reference map `MachCSL.drefMisa` (the decode
   of 0x8506 reads only `misa`) and `execOfRunRead`, so it takes `s.regs .misa = misaC` (Rocq:
   the C bit of misa; `ctrlOkS` fixes the whole register).  `rfFDecodePH` is `rff_auto` after
   pruning the decoder's pattern tests on the literal (`simp (decide := true) [↓reduceIte]`;
   `maxRecDepth 200000`, about 20 s).
4. Stage C (`AxSymEngine` deviation; `notes/weak-port-o2-stageC.md`): Rocq's `Hloc` section
   premise is DROPPED (`XGprWriteS` takes only `Htext`/`Hflow`).  The FETCH is not a graph
   event: `prow` is the three walker reads only (Rocq: + the 4-byte fetch at 0x80000000), so
   `gpT`'s gmo is `[(0,0); (0,1); (0,2)]` and `gpTRowLen` is 3 (Rocq 4).
5. Rocq's `Local Instance probe_ga2_inst` / `gpT_inst` (`AxGA2 GD TX gname unit prot_inv γ`) are
   not declared: Lean's `axGA2` has no `TX` parameter and the instance is `AxSymEngine3b`'s
   reducible `blkGa2 GD γ` (passed with `@`); the `TX` binder is dropped.  Instances:
   `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` (any `hlc`), section variables explicit.

**Rocq → Lean name map.**  `ent_at` `entAt`, `pT0` `pT0`, `pT1` `pT1`, `pT` `pT`, `pvpn`
`pvpn`, `pP2` `pP2`, `pP1` `pP1`, `pW` `pW`, `pT_base` `pTBase`, `pT_maps` `pTMaps`,
`ram_ok_z` `AxSymCtl3.ramOkZ` (duplicated name), `slot_of` `slotOf`, `pT_slot2/1/0`
`pTSlot2/1/0`, `pH` `pH`, `pW32` `pW32`, `pT_text_at` `pTTextAt`, `pI0` `pI0`,
`rfF_decode_pH` `rfFDecodePH`, `exec_decode_pH` `execDecodePH`, `rfF_execute_pI0`
`rfFExecutePI0`, `pT_text_ok` `pTTextOk`, `nvS_pc` `nvSPc`, `wpd_cmv_probe` `wpdCmvProbe`,
`wpd_cmv_probe_ga2` `wpdCmvProbeGa2`, `pT_img` `pTImg`, `pa2/pa1/pa0` `pa2/pa1/pa0`, `rdI`
`rdI`, `prow` `prow`, `gpT` `gpT`, `gpT_row_len` `gpTRowLen`, `gpT_text_fixed` `gpTTextFixed`,
`gpT_cat` `gpTCat`, `wpd_cmv_probe_gpT` `wpdCmvProbeGpT`.  Lean-only (file-qualified):
`AxSymCtl3.pcNext` (`w64 sPc + instrLen true = addInt (w64 sPc) 2`, X's PC form to Rocq's),
`AxSymCtl3.rowItem` (one row item of `gpT` for `gpTTextFixed`).

**Dropped:** the Ltacs `vr`/`byt`/`bytes8` and the local instances `probe_ga2_inst`/`gpT_inst`
(deviations 1, 5); the `Print Assumptions`/`Check` lines (the lint's axiom check covers them).
Rocq 37 definitions/lemmas (+ 2 local instances); Lean 37 + 2 Lean-only.
-/
import Weak.AxSpineOk8
import Weak.AxSymEngine3b
import Weak.AxGraphDec

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. The concrete tree -/

def entAt (j0 : Nat) (w : Nat) : BitVec 9 → BitVec 64 :=
  fun j => if j.toNat = j0 then AxEpiProbe.w64 w else AxEpiProbe.w64 0

def pT0 : PTree :=
  .node (BitVec.ofNat 44 AxSmodeProbe.sL0)
    (fun j => if j.toNat = 0 then AxEpiProbe.w64 (AxSmodeProbe.pteLeaf 0x80000)
      else if j.toNat = 1 then AxEpiProbe.w64 (AxSmodeProbe.pteLeaf 0x80001) else AxEpiProbe.w64 0)
    (fun _ => none)

def pT1 : PTree :=
  .node (BitVec.ofNat 44 AxSmodeProbe.sL1) (entAt 0 (AxSmodeProbe.pteNl AxSmodeProbe.sL0))
    (fun j => if j.toNat = 0 then some pT0 else none)

def pT : PTree :=
  .node nvSRoot (entAt 2 (AxSmodeProbe.pteNl AxSmodeProbe.sL1))
    (fun j => if j.toNat = 2 then some pT1 else none)

def pvpn : BitVec 27 := WeakKpt.svpnOf (AxEpiProbe.w64 sPc)
def pP2 : BitVec 64 := AxEpiProbe.w64 (AxSmodeProbe.pteNl AxSmodeProbe.sL1)
def pP1 : BitVec 64 := AxEpiProbe.w64 (AxSmodeProbe.pteNl AxSmodeProbe.sL0)
def pW : BitVec 64 := AxEpiProbe.w64 (AxSmodeProbe.pteLeaf 0x80000)

theorem pTBase : BitVec.setWidth 44 (satp_to_ppn nvSSatp) = pT.base := rfl

theorem pTMaps : AxPtProt.ptreeMaps pT pvpn pP2 pP1 pW := by
  unfold AxPtProt.ptreeMaps pteValid ptePtr pteLeaf AxPtProt.pteNoNapot ptePbmt0
  refine ⟨pT1, pT0, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro s; ax_epi_ledger_krfl)
    | decide +kernel
    | ax_epi_ledger_krfl

/-- Rocq `ram_ok_z` (deviation 2). -/
theorem AxSymCtl3.ramOkZ (a : BitVec 64) (n : Nat) :
    (decide (ramBase ≤ a.toNat) && decide (a.toNat + n ≤ ramEnd)) = true → inRam a n := by
  intro H
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at H
  exact H

/-- Rocq `slot_of` (deviation 2). -/
theorem slotOf (a w : BitVec 64) :
    (∀ j : Nat, j < 8 → nvST.mem (a + BitVec.ofNat 64 j) = some (nthByte (n := 8) w j)) →
    inRam a 8 →
    is_aligned_paddr (.Physaddr a) 8 = true →
    WeakWalkEff.ptSlotMem nvST a w :=
  fun Hb H1 H2 => ⟨Hb, H1, H2⟩

theorem pTSlot2 : WeakWalkEff.ptSlotMem nvST (AxPtProt.ptAddr2 pT pvpn) pP2 :=
  slotOf _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem pTSlot1 : WeakWalkEff.ptSlotMem nvST (AxPtProt.ptAddr1 pP2 pvpn) pP1 :=
  slotOf _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem pTSlot0 : WeakWalkEff.ptSlotMem nvST (AxPtProt.ptAddr0 pP1 pvpn) pW :=
  slotOf _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! # 2. `textAtS` at the probe's text -/

def pH : BitVec 16 := 0x8506#16
def pW32 : BitVec 32 := 0x00818506#32

theorem pTTextAt : textAtS nvST pT (AxEpiProbe.w64 sPc) pH := by
  refine ⟨pP2, pP1, pW, AxEpiProbe.w64 sPc, pTMaps, pTSlot2, pTSlot1, pTSlot0, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro mxr dosum s
    cases mxr <;> cases dosum <;> ax_epi_ledger_krfl
  · decide +kernel
  · unfold ptePbmt0; decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [if_pos (show is_aligned_vaddr (.Virtaddr (AxEpiProbe.w64 sPc)) 4 = true by decide +kernel)]
    refine ⟨pW32, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
    unfold BytesAt
    decide +kernel

/-! # 3. `textOkD` for `c.mv a0, ra` at the probe's pc, ∀ regime states -/

def pI0 : instruction := .C_MV (.Regidx a05, .Regidx ra5)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem rfFDecodePH : rfF (ext_decode_compressed pH) := by
  unfold pH ext_decode_compressed encdec_compressed_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

theorem execDecodePH (s : ExecSt) : s.regs .misa = misaC →
    exec (ext_decode_compressed pH) s = some (pI0, s) := by
  intro H
  have hw : runRead drefMisa (ext_decode_compressed pH) = some (pI0, true) := by
    ax_epi_ledger_krfl
  refine execOfRunRead drefMisa _ s _ true ?_ hw
  intro r v hv
  unfold drefMisa at hv
  split at hv <;> simp only [Option.some.injEq, reduceCtorEq] at hv
  subst hv
  exact H

theorem rfFExecutePI0 : rfF (execute pI0) := by
  show rfF (pure (execute_C_MV (.Regidx a05) (.Regidx ra5)))
  exact True.intro

theorem pTTextOk :
    textOkD (imgS nvST) (ctrlOkS pT nvSSatp) (textAtS nvST pT) (AxEpiProbe.w64 sPc) true ICmv := by
  refine ⟨rfl, pH, pI0, pTTextAt, ?_, ?_, ?_⟩
  · intro t Hc
    exact EvAOfRfF _ _ rfFDecodePH t pI0 t (execDecodePH t Hc.2.2.1)
  · intro t
    exact EvAOfRfF _ _ rfFExecutePI0 t _ t (execExecuteCMV (.Regidx a05) (.Regidx ra5) t)
  · exact rf0ExecuteRTYPEADD ra5 0#5 a05

/-! # 4. The symbolic S-mode chain at the probe's state -/

theorem nvSPc : nvSRs .PC = AxEpiProbe.w64 sPc := by decide +kernel

theorem AxSymCtl3.pcNext : AxEpiProbe.w64 sPc + instrLen true = BitVec.addInt (AxEpiProbe.w64 sPc) 2 := by
  decide +kernel

/-- `c.mv a0, ra` at the probe's S-mode boundary through the SYMBOLIC engine: regime, text,
decode, exec certificate all discharged. -/
theorem wpdCmvProbe {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
    (i : Agent) (cpu : CPU)
    (Htext : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i (imgS nvST)⌝)
    (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
      (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
         imgBytes (imgS nvST) base n = some vs) →
      AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
    (s : Athread) (k : Nat) :
    RetX cpu nvSRs k s →
    ⊢ (∀ s' rs' k', ⌜RetX cpu rs' k' s'⌝ -∗ ⌜ctrlOkS pT nvSSatp rs'⌝ -∗
         ⌜rs' .PC = BitVec.addInt (AxEpiProbe.w64 sPc) 2⌝ -∗
         ⌜∀ r : BitVec 5, r.toNat ≠ 0 →
            AxSymEngine3.gpr r rs' = if r = a05 then blkW1 nvSRs else AxSymEngine3.gpr r nvSRs⌝ -∗
         wpd .MaybeStuck i s' (Φ0 (GF := GF))) -∗
       wpd .MaybeStuck i s (Φ0 (GF := GF)) := by
  intro HR
  have HX := XGprWriteS nvST pT nvSSatp i cpu nvSSatpMode nvSSatpAsid pTBase Htext Hflow
  have h := HX s nvSRs k (AxEpiProbe.w64 sPc) true ICmv a05 (blkW1 nvSRs) HR (nvSCtrlOk pT)
    nvSPc pTTextOk (by decide) (fun s_pc _ Hag => certCmv nvSRs s_pc Hag)
  iintro C
  iapply h
  iintro %s' %rs' %k' %HR' %Hc' %HPC' %Hg'
  have HPC2 : rs' .PC = BitVec.addInt (AxEpiProbe.w64 sPc) 2 := HPC'.trans AxSymCtl3.pcNext
  iapply C $$ %s' %rs' %k' %HR' %Hc' %HPC2 %Hg'

/-- The instance premises discharged at `axGA2` with the real protocol `protInv`
(`blkGa2`): only the graph fact `textFixed` remains. -/
theorem wpdCmvProbeGa2 {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF]
    [AxannotGS GF] [pol : Axpol] [AxlogG GF Hent]
    (GD0 : Gdexec) (γ : GName) (i : Agent) (cpu : CPU) (Hfix : textFixed GD0 i (imgS nvST))
    (s : Athread) (k : Nat) :
    RetX cpu nvSRs k s →
    ⊢ (∀ s' rs' k', ⌜RetX cpu rs' k' s'⌝ -∗ ⌜ctrlOkS pT nvSSatp rs'⌝ -∗
         ⌜rs' .PC = BitVec.addInt (AxEpiProbe.w64 sPc) 2⌝ -∗
         ⌜∀ r : BitVec 5, r.toNat ≠ 0 →
            AxSymEngine3.gpr r rs' = if r = a05 then blkW1 nvSRs else AxSymEngine3.gpr r nvSRs⌝ -∗
         @wpd hlc GF _ (blkGa2 GD0 γ) pol .MaybeStuck i s' (Φ0 (GF := GF))) -∗
       @wpd hlc GF _ (blkGa2 GD0 γ) pol .MaybeStuck i s (Φ0 (GF := GF)) :=
  @wpdCmvProbe hlc GF _ (blkGa2 GD0 γ) pol i cpu
    (HtextGa2 GD0 GName Unit _ γ (imgS nvST) i Hfix)
    (fun GD ls k hc hx => HflowGa2 GD0 GName Unit _ γ (imgS nvST) i
      (fun GD σ s e Hnin Hnw => protInvReadStep γ GD s e Hnin Hnw) GD ls k hc hx)
    s k

/-! # 5. A SMALL CONCRETE GRAPH discharging `textFixed`

Hart 0's row is EXACTLY the cold-TLB fetch's graph events at the probe: the three walk reads
(root[2], L1[0], L0[0], 8 bytes each; the fetch itself is a pinned admin step, deviation 4) —
every value = the image's bytes; the graph's image IS `imgS nvST`. -/

def pTImg : Image := imgS nvST
def pa2 : Int := AxSmodeProbe.sRoot * 4096 + 2 * 8
def pa1 : Int := AxSmodeProbe.sL1 * 4096
def pa0 : Int := AxSmodeProbe.sL0 * 4096
def rdI (a : Int) (n : Nat) : List (BitVec 8) := (imgBytes pTImg a n).getD []

def prow : List Lbl :=
  [ Lbl.LLoad false pa2 (List.replicate 8 0) (rdI pa2 8),
    Lbl.LLoad false pa1 (List.replicate 8 0) (rdI pa1 8),
    Lbl.LLoad false pa0 (List.replicate 8 0) (rdI pa0 8) ]

def gpT : Gdexec := ⟨⟨pTImg, [prow], [(0, 0), (0, 1), (0, 2)]⟩, []⟩

theorem gpTRowLen : (AxOpsem.grow gpT 0).length = 3 := rfl

/-- (Lean-only helper) one walk-read row item at base `b`. -/
theorem AxSymCtl3.rowItem (k : Nat) (b : Int) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat)
    (vs : List (BitVec 8))
    (Hk : (AxOpsem.grow gpT 0)[k]? = some (Lbl.LLoad false b (List.replicate 8 0) (rdI b 8)))
    (Hgv : graphValue gpT (0, k) = some (rdI b 8))
    (Hlen : (rdI b 8).length = 8) (Himg : imgBytes pTImg b 8 = some (rdI b 8))
    (Hlb : (AxOpsem.grow gpT 0)[k]? = some lb) (Hrd : aidentRd (aident lb) = some (aq, base, n))
    (Hvs : imgBytes pTImg base n = some vs) :
    aident lb = .IRead aq base n ∧ graphValue gpT (0, k) = some vs := by
  rw [Hk] at Hlb
  cases Hlb
  simp only [aident, aidentRd, Option.some.injEq, Prod.mk.injEq] at Hrd
  obtain ⟨rfl, rfl, rfl⟩ := Hrd
  refine ⟨rfl, ?_⟩
  rw [Hlen, Himg] at Hvs
  rw [Hgv, Hvs]

theorem gpTTextFixed : textFixed gpT 0 pTImg := by
  refine ⟨fun _ _ H => H, ?_⟩
  intro k lb aq base n vs Hlb Hrd Hvs
  match k with
  | 0 =>
    exact AxSymCtl3.rowItem 0 pa2 lb aq base n vs rfl (by decide +kernel) (by decide +kernel)
      (by decide +kernel) Hlb Hrd Hvs
  | 1 =>
    exact AxSymCtl3.rowItem 1 pa1 lb aq base n vs rfl (by decide +kernel) (by decide +kernel)
      (by decide +kernel) Hlb Hrd Hvs
  | 2 =>
    exact AxSymCtl3.rowItem 2 pa0 lb aq base n vs rfl (by decide +kernel) (by decide +kernel)
      (by decide +kernel) Hlb Hrd Hvs
  | k + 3 =>
    have h : (AxOpsem.grow gpT 0)[k + 3]? = none := by
      show prow[k + 3]? = none
      simp [prow]
    rw [h] at Hlb
    cases Hlb

theorem gpTCat : rvwmoCatConsistent gpT := catConsistentBSound _ (by decide +kernel)

/-- The capstone: the symbolic chain at the probe's state, at the real Tier-A instance over the
concrete graph `gpT`, NO premise left. -/
theorem wpdCmvProbeGpT {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF]
    [AxannotGS GF] [pol : Axpol] [AxlogG GF Hent] (γ : GName) (cpu : CPU) (s : Athread) (k : Nat) :
    RetX cpu nvSRs k s →
    ⊢ (∀ s' rs' k', ⌜RetX cpu rs' k' s'⌝ -∗ ⌜ctrlOkS pT nvSSatp rs'⌝ -∗
         ⌜rs' .PC = BitVec.addInt (AxEpiProbe.w64 sPc) 2⌝ -∗
         ⌜∀ r : BitVec 5, r.toNat ≠ 0 →
            AxSymEngine3.gpr r rs' = if r = a05 then blkW1 nvSRs else AxSymEngine3.gpr r nvSRs⌝ -∗
         @wpd hlc GF _ (blkGa2 gpT γ) pol .MaybeStuck 0 s' (Φ0 (GF := GF))) -∗
       @wpd hlc GF _ (blkGa2 gpT γ) pol .MaybeStuck 0 s (Φ0 (GF := GF)) :=
  wpdCmvProbeGa2 gpT γ 0 cpu gpTTextFixed s k

end Weak
