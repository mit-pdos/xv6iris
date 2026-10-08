/-
Weak: **the spinlock plan, PHASE 5 item (4), part 5** — NON-VACUITY of the symbolic
arbitrary-VA fetch chain (`AxSpinVA4`) at the REAL probe state, and its agreement with the
evaluator.

Rocq: `iris/AxSpinVA5.v` @ xxvzwolszwmp.

## What this file proves

§1 `symPinned` / `symOther`: the symbolic fetch chain at `AxSpineOk8.nvST` (Sv39, cold TLB, the
probe tree `AxSymCtl3.pT`, kernel satp) for TWO VAs of the mapped text page — the pinned
0x80000000 and the OTHER mapped text address 0x80000004 — every premise discharged (closed
statements).  Both fetches are IN the image (deviation 1), so they go through the Lean-only
`AxSpinVA4.fetchMappedImg4`: the chain gains exactly the walk keys and the continuation gets the
decoded fetch result (`F_RVC 0x8506` = `c.mv a0, ra`, resp. `F_RVC 0x0001` = `c.nop`).
Lean-only `AxSpinVA5.symNoImg`: `chainFetchMapped4` ITSELF instantiated at the probe state, at the
mapped text address 0x80000008 that has NO image bytes (chain `walkKeys ++ [.ENf (0x80000008, 4)]`).
§2 `symEqEvalPinned` / `symEqEvalOther` (+ `AxSpinVA5.symEqEvalNoImg`): the symbolic chain,
computed by the kernel, EQUALS `AxSpinVA.fstep`'s chain on the real `riscvStep` (both ticks, all
pin answers); `symPinnedExplicit` / `symOtherExplicit`: the explicit cold-TLB chain [root slot;
L1 slot; L0 slot].  Lean-only `AxSpinVA5.symPinnedStep` / `symOtherStep`: the whole-step chain
`BFEC … 1 walkKeys` from the evaluator (`fstepSound`).
§3 `samePageDiverge`: SYMBOLIC — two fetchable VAs of ONE page produce the SAME walker keys and
differ exactly at the fetch key whenever their pas differ.

## Deviations from Rocq

1. O2 STAGE C (`AxSpinVA` deviation 1, Q13; `AxSpinVA4` deviation 1).  A fetch is no chain key:
   Rocq's end key `ERd (false, uint pa, 4)` exists in Lean only for a fetch with NO image bytes
   (`.ENf (paZ pa, 4)`, `chainFetchMapped4`'s premise `imgBytes … = none`).  The probe's text
   bytes at 0x80000000 (06 85 81 00) and 0x80000004 (01 00 01 00) ARE image bytes, so
   `chainFetchMapped4` does not apply there.  Hence:
   - `symPinned` / `symOther` are restated at `fetch ()` through `AxSpinVA4.fetchMappedImg4`:
     for every nonempty continuation chain `Ks` and every continuation `Q` that holds at the
     regime states differing from the start at most in the TLB with the DECODED fetch result,
     `FEC (imgOf nvST) False Q (walkKeys … ++ Ks) (fetch ()) t`.  The decoded instructions
     (`c.mv a0, ra`, `c.nop`) are register-only, so they add no key; the whole-step chain is
     the walk keys alone (Lean-only `AxSpinVA5.symPinnedStep` / `symOtherStep`, BFEC at
     budget 1, the chain ENDING at the L0 walker read).
   - `symEqEvalPinned` / `symEqEvalOther` / `symPinnedExplicit` / `symOtherExplicit`: the chain
     is `walkKeys …` (3 keys), not `walkKeys … ++ [fetch]` (4 keys).
   - Lean-only `AxSpinVA5.va8` / `nvST8` / `nvST8Ctrl` / `pTFetchable8` / `symNoImg` /
     `symEqEvalNoImg` / `symNoImgExplicit` keep the file's purpose — `chainFetchMapped4` is
     NON-VACUOUS at the real probe state — at a mapped text VA without image bytes; that chain
     has Rocq's 4-key shape with the end key `.ENf (0x80000008, 4)`.
   - `samePageDiverge`: the fetch keys are `.ENf (paZ pa, n)` (the Lean fetch end key);
     `uint pa ≠ uint pa'` ↦ `paZ pa ≠ paZ pa'`.
2. SPELLING (as `AxSpinVA4` deviation 3, `AxSpineOk8` deviation 1): `mstate` ↦ `ExecSt`,
   `w64` ↦ `AxEpiProbe.w64`, `s_pc` ↦ `sPc`, `nvS_t` ↦ `nvST`, `img_of` ↦ `imgOf`, `uint` ↦
   `paZ`, `svpn_of` ↦ `WeakKpt.svpnOf`, `register_lookup tlb t.(sregs)` ↦ `t.regs .tlb`,
   `set_reg (set_reg t PC v) nextPC v` ↦ `(t.setReg .PC v).setReg .nextPC v`,
   `ctrl_ok_S_agree` ↦ `ctrlOkSAgree` (over `ctrlRegs`), `ptree_maps_det` ↦
   `AxPtProt.ptreeMapsDet`, `ram_ok_z` ↦ `AxSymCtl3.ramOkZ`, `vec (option TLB_Entry) (2^6)` ↦
   `Vector (Option TLB_Entry) (2 ^ 6)`.  `vm_compute` ↦ `decide +kernel` / `ax_epi_ledger_krfl`;
   the Ltac `vr5` is dropped.

**Rocq → Lean name map.**  `pT_fetchable0` `pTFetchable0`, `va4` `va4`, `svpn_va4` `svpnVa4`,
`pT_fetchable4` `pTFetchable4`, `nvS_t4` `nvST4`, `nvS_t4_ctrl` `nvST4Ctrl`, `sym_pinned`
`symPinned`, `sym_other` `symOther`, `sym_eq_eval_pinned` `symEqEvalPinned`, `sym_eq_eval_other`
`symEqEvalOther`, `sym_pinned_explicit` `symPinnedExplicit`, `sym_other_explicit`
`symOtherExplicit`, `same_page_diverge` `samePageDiverge`.  None is in the duplicated-name table.
Lean-only (file-qualified, deviation 1): `AxSpinVA5.ctrlOfPcMove` (the regime survives a PC
move; `nvST4Ctrl` and `nvST8Ctrl` are its instances), `AxSpinVA5.symPinnedStep`,
`AxSpinVA5.symOtherStep`, `AxSpinVA5.va8`, `AxSpinVA5.svpnVa8`, `AxSpinVA5.pTFetchable8`,
`AxSpinVA5.nvST8`, `AxSpinVA5.nvST8Ctrl`, `AxSpinVA5.symNoImg`, `AxSpinVA5.symEqEvalNoImg`,
`AxSpinVA5.symNoImgExplicit`.

**Dropped:** none (Rocq 2 definitions + 11 lemmas = 13 decls; Lean the same 13 + 11 Lean-only).  **Not ported:** the Ltac `vr5` and the `Print Assumptions` lines (the
lint's axiom check covers them).
-/
import Weak.AxSpinVA4
import Weak.AxSymCtl3

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. The instances -/

theorem pTFetchable0 :
    fetchable nvST pT (AxEpiProbe.w64 sPc) pW (AxEpiProbe.w64 sPc) pP2 pP1 := by
  refine ⟨pTMaps, pTSlot2, pTSlot1, pTSlot0, ?_, ?_, ?_, ?_, ?_⟩
  · intro mxr dosum s
    cases mxr <;> cases dosum <;> ax_epi_ledger_krfl
  · decide +kernel
  · unfold ptePbmt0; decide +kernel
  · decide +kernel
  · decide +kernel

/-- Rocq `va4`. -/
def va4 : BitVec 64 := AxEpiProbe.w64 (sPc + 4)

theorem svpnVa4 : WeakKpt.svpnOf va4 = pvpn := by decide +kernel

theorem pTFetchable4 : fetchable nvST pT va4 pW va4 pP2 pP1 := by
  unfold fetchable
  rw [svpnVa4]
  refine ⟨pTMaps, pTSlot2, pTSlot1, pTSlot0, ?_, ?_, ?_, ?_, ?_⟩
  · intro mxr dosum s
    cases mxr <;> cases dosum <;> ax_epi_ledger_krfl
  · decide +kernel
  · unfold ptePbmt0; decide +kernel
  · decide +kernel
  · decide +kernel

/-- Rocq `nvS_t4`: the probe state at PC = nextPC = `va4`. -/
def nvST4 : ExecSt := (nvST.setReg .PC va4).setReg .nextPC va4

/-- The regime is unaffected by a PC move. -/
theorem AxSpinVA5.ctrlOfPcMove (v : BitVec 64) :
    ctrlOkS pT nvSSatp ((nvST.setReg .PC v).setReg .nextPC v).regs := by
  refine ctrlOkSAgree pT nvSSatp nvST.regs _ ?_ (nvSCtrlOk pT)
  intro r hr
  have h1 : r ≠ .nextPC := by rintro rfl; revert hr; decide
  have h2 : r ≠ .PC := by rintro rfl; revert hr; decide
  rw [ExecSt.setReg_regs, ExecSt.setReg_regs, RegFile.set_other _ _ _ _ h1,
    RegFile.set_other _ _ _ _ h2]

theorem nvST4Ctrl : ctrlOkS pT nvSSatp nvST4.regs := AxSpinVA5.ctrlOfPcMove va4

/-- Rocq `sym_pinned` (deviation 1): the fetch at the pinned 0x80000000 is IN the image — the
chain gains exactly the (cold-TLB) walk keys, then continues with `c.mv a0, ra`'s fetch result. -/
theorem symPinned (Ks : List ekey) (Q : List ekey → FetchResult → ExecSt → Prop) :
    Ks ≠ [] →
    (∀ t' : ExecSt, ctrlOkS pT nvSSatp t'.regs → (∀ r, r ≠ .tlb → t'.regs r = nvST.regs r) →
      t'.mem = nvST.mem → t'.dev = nvST.dev → Q Ks (.F_RVC pH) t') →
    FEC (imgOf nvST) (fun _ _ _ => False) Q
      (walkKeys pT (nvST.regs .tlb) (WeakKpt.svpnOf (AxEpiProbe.w64 sPc)) pP2 pP1 ++ Ks)
      (fetch ()) nvST := by
  intro HKs HQ
  have hres : AxSpinVA4.fetchRes (rrv 4 [0x06#8, 0x85#8, 0x81#8, 0x00#8]) = .F_RVC pH := by
    have h1 : isRVC (Sail.BitVec.extractLsb (rrv 4 [0x06#8, 0x85#8, 0x81#8, 0x00#8]) 15 0)
        = true := by decide +kernel
    have h2 : Sail.BitVec.extractLsb (rrv 4 [0x06#8, 0x85#8, 0x81#8, 0x00#8]) 15 0 = pH := by
      decide +kernel
    unfold AxSpinVA4.fetchRes
    rw [if_pos h1, h2]
  refine AxSpinVA4.fetchMappedImg4 nvST pT nvSSatp nvSSatpMode nvSSatpAsid pTBase nvST
    (AxEpiProbe.w64 sPc) pW (AxEpiProbe.w64 sPc) pP2 pP1 [0x06#8, 0x85#8, 0x81#8, 0x00#8] Ks Q
    (nvSCtrlOk pT) rfl (by decide +kernel) pTFetchable0
    (AxSymCtl3.ramOkZ _ _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) HKs ?_
  intro t' Hc Hr Hm Hd
  rw [hres]
  exact HQ t' Hc Hr Hm Hd

/-- Rocq `sym_other` (deviation 1): the OTHER mapped text address 0x80000004, also in the image
(`c.nop`). -/
theorem symOther (Ks : List ekey) (Q : List ekey → FetchResult → ExecSt → Prop) :
    Ks ≠ [] →
    (∀ t' : ExecSt, ctrlOkS pT nvSSatp t'.regs → (∀ r, r ≠ .tlb → t'.regs r = nvST4.regs r) →
      t'.mem = nvST4.mem → t'.dev = nvST4.dev → Q Ks (.F_RVC 0x0001#16) t') →
    FEC (imgOf nvST) (fun _ _ _ => False) Q
      (walkKeys pT (nvST4.regs .tlb) (WeakKpt.svpnOf va4) pP2 pP1 ++ Ks) (fetch ()) nvST4 := by
  intro HKs HQ
  have hres : AxSpinVA4.fetchRes (rrv 4 [0x01#8, 0x00#8, 0x01#8, 0x00#8]) = .F_RVC 0x0001#16 := by
    have h1 : isRVC (Sail.BitVec.extractLsb (rrv 4 [0x01#8, 0x00#8, 0x01#8, 0x00#8]) 15 0)
        = true := by decide +kernel
    have h2 : Sail.BitVec.extractLsb (rrv 4 [0x01#8, 0x00#8, 0x01#8, 0x00#8]) 15 0
        = 0x0001#16 := by decide +kernel
    unfold AxSpinVA4.fetchRes
    rw [if_pos h1, h2]
  refine AxSpinVA4.fetchMappedImg4 nvST pT nvSSatp nvSSatpMode nvSSatpAsid pTBase nvST4
    va4 pW va4 pP2 pP1 [0x01#8, 0x00#8, 0x01#8, 0x00#8] Ks Q
    nvST4Ctrl rfl (by decide +kernel) pTFetchable4
    (AxSymCtl3.ramOkZ _ _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) HKs ?_
  intro t' Hc Hr Hm Hd
  rw [hres]
  exact HQ t' Hc Hr Hm Hd

/-! ## (Lean-only, deviation 1) `chainFetchMapped4` itself, at a mapped text VA with no image
bytes -/

def AxSpinVA5.va8 : BitVec 64 := AxEpiProbe.w64 (sPc + 8)

theorem AxSpinVA5.svpnVa8 : WeakKpt.svpnOf AxSpinVA5.va8 = pvpn := by decide +kernel

theorem AxSpinVA5.pTFetchable8 :
    fetchable nvST pT AxSpinVA5.va8 pW AxSpinVA5.va8 pP2 pP1 := by
  unfold fetchable
  rw [AxSpinVA5.svpnVa8]
  refine ⟨pTMaps, pTSlot2, pTSlot1, pTSlot0, ?_, ?_, ?_, ?_, ?_⟩
  · intro mxr dosum s
    cases mxr <;> cases dosum <;> ax_epi_ledger_krfl
  · decide +kernel
  · unfold ptePbmt0; decide +kernel
  · decide +kernel
  · decide +kernel

def AxSpinVA5.nvST8 : ExecSt := (nvST.setReg .PC AxSpinVA5.va8).setReg .nextPC AxSpinVA5.va8

theorem AxSpinVA5.nvST8Ctrl : ctrlOkS pT nvSSatp AxSpinVA5.nvST8.regs :=
  AxSpinVA5.ctrlOfPcMove AxSpinVA5.va8

/-- (Lean-only) `chainFetchMapped4` at the probe state, every premise discharged: the mapped
text VA 0x80000008 has no image bytes, so the chain is the walk keys then `.ENf`. -/
theorem AxSpinVA5.symNoImg :
    BFEC (imgOf nvST) 1
      (walkKeys pT (AxSpinVA5.nvST8.regs .tlb) (WeakKpt.svpnOf AxSpinVA5.va8) pP2 pP1
        ++ [.ENf (paZ AxSpinVA5.va8, 4)]) AxSpinVA5.nvST8 :=
  chainFetchMapped4 nvST pT nvSSatp nvSSatpMode nvSSatpAsid pTBase AxSpinVA5.nvST8
    AxSpinVA5.va8 pW AxSpinVA5.va8 pP2 pP1 AxSpinVA5.nvST8Ctrl rfl (by decide +kernel)
    AxSpinVA5.pTFetchable8 (AxSymCtl3.ramOkZ _ _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel)

/-! # 2. Agreement with the evaluator on the real `riscvStep` -/

/-- Rocq `sym_eq_eval_pinned` (deviation 1: no fetch key). -/
theorem symEqEvalPinned :
    fstep (imgOf nvST) 2 4 nvST =
      some (walkKeys pT (nvST.regs .tlb) (WeakKpt.svpnOf (AxEpiProbe.w64 sPc)) pP2 pP1) := by
  decide +kernel

/-- Rocq `sym_eq_eval_other` (deviation 1: no fetch key). -/
theorem symEqEvalOther :
    fstep (imgOf nvST) 2 4 nvST4 =
      some (walkKeys pT (nvST4.regs .tlb) (WeakKpt.svpnOf va4) pP2 pP1) := by
  decide +kernel

/-- (Lean-only) the evaluator at the no-image VA: Rocq's 4-key shape, end key `.ENf`. -/
theorem AxSpinVA5.symEqEvalNoImg :
    fstep (imgOf nvST) 2 4 AxSpinVA5.nvST8 =
      some (walkKeys pT (AxSpinVA5.nvST8.regs .tlb) (WeakKpt.svpnOf AxSpinVA5.va8) pP2 pP1
        ++ [.ENf (paZ AxSpinVA5.va8, 4)]) := by
  decide +kernel

/-- (Lean-only) the whole step at the pinned VA: the chain is the walk keys (budget 1). -/
theorem AxSpinVA5.symPinnedStep :
    BFEC (imgOf nvST) 1
      (walkKeys pT (nvST.regs .tlb) (WeakKpt.svpnOf (AxEpiProbe.w64 sPc)) pP2 pP1) nvST :=
  fstepSound (imgOf nvST) 1 4 nvST _ (by decide +kernel)

/-- (Lean-only) the whole step at the other VA. -/
theorem AxSpinVA5.symOtherStep :
    BFEC (imgOf nvST) 1 (walkKeys pT (nvST4.regs .tlb) (WeakKpt.svpnOf va4) pP2 pP1) nvST4 :=
  fstepSound (imgOf nvST) 1 4 nvST4 _ (by decide +kernel)

/-- Rocq `sym_pinned_explicit` (deviation 1): cold TLB — root slot, L1 slot, L0 slot. -/
theorem symPinnedExplicit :
    walkKeys pT (nvST.regs .tlb) (WeakKpt.svpnOf (AxEpiProbe.w64 sPc)) pP2 pP1 =
      [.ERd (false, 0x80010010, 8), .ERd (false, 0x80011000, 8), .ERd (false, 0x80012000, 8)] := by
  decide +kernel

/-- Rocq `sym_other_explicit` (deviation 1). -/
theorem symOtherExplicit :
    walkKeys pT (nvST4.regs .tlb) (WeakKpt.svpnOf va4) pP2 pP1 =
      [.ERd (false, 0x80010010, 8), .ERd (false, 0x80011000, 8), .ERd (false, 0x80012000, 8)] := by
  decide +kernel

/-- (Lean-only) the no-image chain, explicitly. -/
theorem AxSpinVA5.symNoImgExplicit :
    walkKeys pT (AxSpinVA5.nvST8.regs .tlb) (WeakKpt.svpnOf AxSpinVA5.va8) pP2 pP1
        ++ [.ENf (paZ AxSpinVA5.va8, 4)] =
      [.ERd (false, 0x80010010, 8), .ERd (false, 0x80011000, 8), .ERd (false, 0x80012000, 8),
       .ENf (0x80000008, 4)] := by
  decide +kernel

/-! # 3. Same page ⇒ same walk, the fetch is the first differing label -/

/-- Rocq `same_page_diverge` (deviation 1: the fetch keys are `.ENf`). -/
theorem samePageDiverge (σi : ExecSt) (T : PTree) (tlbv : Vector (Option TLB_Entry) (2 ^ 6))
    (va va' w w' pa pa' p2 p1 p2' p1' : BitVec 64) (n n' : Nat) :
    WeakKpt.svpnOf va = WeakKpt.svpnOf va' →
    fetchable σi T va w pa p2 p1 → fetchable σi T va' w' pa' p2' p1' →
    paZ pa ≠ paZ pa' →
    walkKeys T tlbv (WeakKpt.svpnOf va) p2 p1 = walkKeys T tlbv (WeakKpt.svpnOf va') p2' p1' ∧
    ekey.ENf (paZ pa, n) ≠ ekey.ENf (paZ pa', n') := by
  intro Hv ⟨Hm, _⟩ ⟨Hm', _⟩ Hne
  rw [← Hv] at Hm'
  obtain ⟨rfl, rfl, -⟩ := AxPtProt.ptreeMapsDet T _ _ _ _ _ _ _ Hm Hm'
  refine ⟨by rw [Hv], ?_⟩
  intro h
  simp only [ekey.ENf.injEq, Prod.mk.injEq] at h
  exact Hne h.1

end Weak
