/-
Weak: **PHASE 5, stage 3: the LONG-PATH PROLOGUE + THE CALL of xv6's REAL `holding`** as a
positional CPS WPd at the joint instance Ixv6.

Rocq: `iris/AxSpinHd9.v` @ xxvzwolszwmp.

## The Rocq header, in substance (as restated under Stage C)

holding + 0x08 … + 0x16 (c.addi sp,-32; three spills; c.addi4spn; THE `lk->cpu` LOAD through
the caller's leaf `XLd`; c.mv s1,a5; jal mycpu), then `wpdMycpu` (AxSpinE8) COMPOSED AT THE
INNER ROW POSITION `k + 5` (its continuation lands at `k + 9`), then `holdEpi` (AxSpinHd8) to
the boundary after the c.ret at the EXACT position `k + 12`.

`holdPro` (for `RowHolding k row true …`): from the boundary at `k + 1` (PC = holding + 0x08,
i.e. after c.bnez TAKEN) to WPd at `k + 12` given the caller's continuation with:
a0 = `hres (0 + vcpu) (mycpuRet tp)` (= seqz (lk->cpu − mycpu())) where `vcpu` is the
`lk->cpu` read's graph value (symbolic), sp restored, ra/s0/s1 = the reloaded words, every GPR
other than ra/sp/s0/s1/a0/a5 kept, the spills' row data, the reloads' graph values, the
caller's `lk->cpu` output `Ocpu vcpu` and the FIVE reload annotations (holding's three,
mycpu's two — mycpu's ra spill holds holding + 0x1a, its s0 spill holding's frame pointer).

GRAPH-VALUE PINNING (Q20', provisional Option V): both returns are pinned by the ra reloads'
GRAPH VALUES — mycpu's (`(i, k + 7)` = holding + 0x1a) and holding's (`(i, k + 9)` = `ret`).

## Stage 2 P-FORM (Lean-only; notes/weak-lb-thm2-stage2.md §B, §C row `AxSpinHd9/HdA/HdC`)

`holdProP` is `holdPro`'s script on `RowHoldingP` (AxSpinHd8) with a `by_cases` on
`LEN ≤ position` at `k + 1 .. k + 5`, composing `AxSpinE8.wpdMycpuP` at `k + 5` and
`AxSpinHd8.holdEpiP` at `k + 9`; the ends at `k + 1 .. k + 11` are the windowed, resource-free
hook (window `[k+1, k+11]`, passed down to both callees)
  `HΨend : ∀ k', klo ≤ k' → k' ≤ khi → (grow (gtAdGd GT) i).length ≤ k' → ∀ pr : Pexv6,
     ⊢ wpdM … .MaybeStuck i ⟨pr, k'⟩ Ψ`
and the end at `k + 12` (the callers' designated-cut boundary) is the continuation's second
conjunct (iProp `∧`), which RECEIVES the `lk->cpu` output `Ocpu vcpu` (the caller's deposit),
every graph value and the five reload annotations.  Pins guarded: `k + 7 < LEN →` (`Hvalm`),
`k + 9 < LEN →` (`Hval`).  `holdPro` keeps its exact statement as the corollary.

## P1 GATE FORM (Lean-only; notes/weak-lb-thm2-pins.md §P1)

`AxSpinHd9.holdProGr` is the shared gated core: `holdProP`'s premises with `Hvalm`/`Hval`
replaced by `AxSpinT2i.Gate GT i (k + 7) (stBytes 8 (pch 0x1a))` (fed to `wpdMycpuG`: mycpu's ra
is holding + 0x1a from holding's own `jal`, so mycpu's return pin is gone) and
`AxSpinT2i.Gate GT i (k + 9) (stBytes 8 ret)` (fed to `AxSpinHd8.holdEpiGr`); main continuation
prefixed by `⌜k + 12 < LEN⌝ -∗`.  `holdProP` = core ∘ `gateOfPinG` (statement unchanged).

## P1 VALUE HOOK (Lean-only; the shape is AxSpinE8's header "P1 VALUE HOOK")

`AxSpinHd9.holdProGr`'s hook (window `[k + 1, k + 11]`) takes `AxSpinE8.EndRl GT i [(k + 7,
  some (stBytes 8 (pch 0x1a))), (k + 9,
    some (stBytes 8 ret))] k'` before `∀ pr` (its two gates; handed on to
`wpdMycpuG` / `AxSpinHd8.holdEpiGr`), and the core gains `stBytes 8 ret ≠ stBytes 8 (gprVal rs r1)
→ k + 9 < LEN → graphValue (i, k + 9) = some (stBytes 8 ret)` after `Hret` (passed to
`holdEpiGr`; `holdProP`: its guarded pin).  `holdProP`/`holdPro` unchanged.

## Deviations from Rocq

1. O2 STAGE C / Q20' (provisional Option V; as `AxSpinE8.wpdMycpu` and `AxSpinHd8.holdEpi`):
   * Positions: start boundary `k + 1` (Rocq `k+3`); spills `k+1/2/3` (Rocq `k+5/7/9`);
     `lk->cpu` leaf at `k + 4` (Rocq `k+11`, value at Rocq `k+12`); mycpu at `k + 5` (Rocq
     `k+15`), its spills `k+5/6` (Rocq `k+17/19`), reloads `k+7/8` (Rocq `k+28/30`); holding's
     reloads `k+9/10/11` (Rocq `k+36/38/40`); continuation `k + 12` (Rocq `k+43`).
   * `RowHolding` has no `pretm`/`pret`/`nret` (AxSpinHd8 deviation 1), so `holdPro` drops
     these parameters.  Rocq's return-page premises `Hinjm`/`Hstvm`/`Hinj`/`Hstv`, the section
     context `stv` and the Sail premise `va_first_read` are DROPPED; NEW premises
     `Hvalm : graphValue (gtAdGd GT) (i, k + 7) = some (stBytes 8 (pch 0x1a))` (mycpu's return,
     fed to `wpdMycpu`'s `Hval`), `Hval : graphValue (gtAdGd GT) (i, k + 9) = some (stBytes 8 ret)`
     and `Hret : jalrTgt 0#12 ret = ret` (fed to `holdEpi`).  mycpu's `Hret` is decided at the
     literal `pch 0x1a`.
   * Rocq's `Hfw`/`Hnw` assertions are not built: `AxSpinE6.XxSt` has no `Hnw` premise
     (AxSpinE6 deviation 3).
2. KERNEL DRIFT (AxSpinHd5 / protocol AxSpinHd entry): the `jal ra,mycpu` immediate is `3412`
   (Rocq `imm3374 = 3374`); the Rocq name `imm3374` is ported as `AxSpinHd9.immJal`.
   `frame_cancel_32` (Rocq `KernelRvcDecode`, MISSING by design) is ported here as the
   file-qualified `AxSpinHd9.frameCancel32` (as `AxSpinE8.frameCancel16`).
3. TYPES / SPELLING (as AxSpinHd8 deviation 2): `uint P` ↦ `paZ P`; `gpr_val` ↦ `gprVal`;
   `register_lookup PC rs` ↦ `rs .PC`; `uint r ≠ n` ↦ `r.toNat ≠ n`; `add_vec zero_reg x` ↦
   `0#64 + x`; `(i,k) ↦ₐ P` ↦ `AxAnnot.annotOwn (i, k) P`; `mword_of_int 16 : mword 12` ↦
   `16#12`.  The `let`s: `a0v` is `gprVal rs AxSpinE8.r10`, `hsp1` / `s0m` are the Lean-only
   abbrevs `AxSpinHd9.hsp1 rs` / `AxSpinHd9.s0m rs`, `va_ra`/`va_s0`/`va_s1`/`va_ram`/`va_s0m`
   are inlined.  The proof uses the literals `8#5` / `0#5` for `rS0` / `rz`.
4. INSTANCES / SECTION (as AxSpinHd8 deviation 3): `[InvGS_gen hlc GF]` (any `hlc`); the local
   instances `h9_pol`/`h9_G` are inlined as `xv6Pol GT` / `AxSpinX2.xG L GT nm`; section
   variables are explicit arguments in AxSpinE6's order (+ `Htxm Htxh`).
5. TACTICS: `pcs`/`nz`/`vm_compute` ↦ `decide`; `zsimp` ↦ the file-local macro
   `ax_spin_hd9_zsimp` (= AxSpinHd8's); `lia` ↦ `omega`; `zq` subsumed.  `Print Assumptions`
   is not ported (the lint's axiom check covers it).

**Rocq → Lean name map.**  `rS0` `AxSpinHd9.rS0`, `rz` `AxSpinHd9.rz` (duplicated names:
file-qualified), `imm3374` `AxSpinHd9.immJal` (deviation 2), `link_ow_nz` `linkOwNz`,
`hold_pro` `holdPro`; from KernelRvcDecode `frame_cancel_32` `AxSpinHd9.frameCancel32`.
Lean-only (file-qualified): `AxSpinHd9.hsp1`, `AxSpinHd9.s0m`, `AxSpinHd9.holdProGr` (P1); stage-2 P-form (unqualified, grepped
unique): `holdProP`.

**Dropped:** nothing.  Rocq 5 definitions/lemmas (+ 2 local instances, inlined); Lean 5 + 1
ported from KernelRvcDecode + 2 Lean-only (+ 1 local macro).
-/
import Weak.AxSpinHd2
import Weak.AxSpinHd3
import Weak.AxSpinHd6c
import Weak.AxSpinHd7
import Weak.AxSpinHd8

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `rS0` (= `8#5`, s0). -/
def AxSpinHd9.rS0 : BitVec 5 := zero_extend (m := 5) (1#1 +++ 0#3)
/-- Rocq `rz` (= `0#5`, x0). -/
def AxSpinHd9.rz : BitVec 5 := zero_extend (m := 5) 0b00#2
/-- Rocq `imm3374` (deviation 2: the drifted `jal ra,mycpu` immediate `3412`). -/
def AxSpinHd9.immJal : BitVec 21 := 3412#21

/-- Rocq `link_ow_nz`. -/
theorem linkOwNz (rd : BitVec 5) (v : BitVec 64) : rd.toNat ≠ 0 → linkOw rd v = some (rd, v) := by
  intro E
  unfold linkOw
  rw [if_neg E]

/-- Rocq `KernelRvcDecode.frame_cancel_32` (deviation 2). -/
theorem AxSpinHd9.frameCancel32 (X : BitVec 64) :
    (X + sign_extend (m := 64) (sign_extend (m := 12) (32#6))) +
      sign_extend (m := 64) (caddi16spImm 2#6) = X := by
  rw [BitVec.add_assoc,
    show sign_extend (m := 64) (sign_extend (m := 12) (32#6)) +
      sign_extend (m := 64) (caddi16spImm 2#6) = 0#64 by decide]
  exact BitVec.add_zero X

/-- (Lean-only) Rocq's `let hsp1`: sp after `c.addi sp,-32`. -/
abbrev AxSpinHd9.hsp1 (rs : RegFile) : BitVec 64 :=
  gprVal rs AxSpinE8.r2 + sign_extend (m := 64) (sign_extend (m := 12) (32#6))
/-- (Lean-only) Rocq's `let s0m`: holding's frame pointer (after `c.addi4spn s0,sp,32`). -/
abbrev AxSpinHd9.s0m (rs : RegFile) : BitVec 64 :=
  AxSpinHd9.hsp1 rs + sign_extend (m := 64) (caddi4spnImm 8#8)

/-- (Rocq `zsimp`) evaluate the closed `upd` tests. -/
local macro "ax_spin_hd9_zsimp" loc:(ppSpace Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := decide) only [AxSpinE8.updSame, AxSpinE8.updOther, AxSpinE8.updZero]
    $[$loc]?)

section pro
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]
variable (L : Xlay) (GT : GdexecT) (nm : Xv6N)
variable (HL : xlayOk L) (Hcons : rvwmoCatConsistent (gtAdGd GT))
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
variable (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
variable (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (i : Agent) (cpu : CPU)
variable (Hfix : textFixed (gtAdGd GT) i (imgS σi))
variable (Htxm : mycpuText σi T) (Htxh : holdingText σi T)
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

set_option maxHeartbeats 4000000 in
include HL Hcons hmode hasid hppn Hfix Htxm Htxh HΨmid in
/-- (Lean-only, P1) THE GATED CORE of `holdProP`: its script with the two ra pins replaced by the
reload GATES `AxSpinT2i.Gate GT i (k + 7) (stBytes 8 (pch 0x1a))` (mycpu's, fed to
`wpdMycpuG` — mycpu's ra is holding + 0x1a, set by holding's `jal`) and
`AxSpinT2i.Gate GT i (k + 9) (stBytes 8 ret)` (holding's own, fed to `AxSpinHd8.holdEpiGr`; `ret`
still a parameter), the main continuation additionally RECEIVING `k + 12 < LEN`. -/
theorem AxSpinHd9.holdProGr (k : Nat) (rs : RegFile) (ib : Ibch) (ret : BitVec 64) (plk pcl : Int)
    (Pra Ps0 Ps1 Pram Ps0m : BitVec 64) (Ocpu : List (BitVec 8) → IProp GF) :
    -- the row
    RowHoldingP k (AxOpsem.grow (gtAdGd GT) i) true plk pcl (paZ Pra) (paZ Ps0) (paZ Ps1)
      (paZ Pram) (paZ Ps0m) →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pram) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0m) →
    slotsDisj [paZ Pra, paZ Ps0, paZ Ps1, paZ Pram, paZ Ps0m] →
    -- the boundary state
    ctrlOkSW T satp0 rs → rs .PC = pch 0x08 → hitW rs (pch 0) → hitW rs (pcm 0) →
    hitW rs (gprVal rs AxSpinE8.r10 + sign_extend (m := 64) (16#12)) →
    -- the five stack slots
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm24) 8 Pra →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm24) 8 Pra →
    hitW rs (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm24) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm16) 8 Ps0 →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm16) 8 Ps0 →
    hitW rs (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm16) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm8) 8 Ps1 →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm8) 8 Ps1 →
    hitW rs (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm8) →
    dataAtS σi T (.Store .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs) + sign_extend (m := 64) AxSpinE8.immRa) 8 Pram →
    dataAtS σi T (.Load .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs) + sign_extend (m := 64) AxSpinE8.immRa) 8 Pram →
    hitW rs (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs) + sign_extend (m := 64) AxSpinE8.immRa) →
    dataAtS σi T (.Store .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs) + sign_extend (m := 64) AxSpinE8.immS0) 8 Ps0m →
    dataAtS σi T (.Load .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs) + sign_extend (m := 64) AxSpinE8.immS0) 8 Ps0m →
    hitW rs (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs) + sign_extend (m := 64) AxSpinE8.immS0) →
    (∀ j : Nat, j < 8 → priv L (paZ Pra + (j : Int)) i) → ¬ L.xlText (paZ Pra) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0 + (j : Int)) i) → ¬ L.xlText (paZ Ps0) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps1 + (j : Int)) i) → ¬ L.xlText (paZ Ps1) →
    (∀ j : Nat, j < 8 → priv L (paZ Pram + (j : Int)) i) → ¬ L.xlText (paZ Pram) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0m + (j : Int)) i) → ¬ L.xlText (paZ Ps0m) →
    -- the two return addresses (P1: the ra reload GATES; mycpu's against holding + 0x1a)
    AxSpinT2i.Gate GT i (k + 7) (stBytes 8 (pch 0x1a)) →
    AxSpinT2i.Gate GT i (k + 9) (stBytes 8 ret) → jalrTgt 0#12 ret = ret →
    -- (P1 VALUE HOOK) a `ret` that is not the spill's: the guarded pin (`holdProP`'s)
    (stBytes 8 ret ≠ stBytes 8 (gprVal rs AxSpinE8.r1) →
      k + 9 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, k + 9) = some (stBytes 8 ret)) →
    -- the row-end hook (stage 2, design §B / Q-S2-2), over the window [k + 1, k + 11]
    -- (P1 VALUE HOOK)
    (∀ k' : Nat, k + 1 ≤ k' → k' ≤ k + 11 → (AxOpsem.grow (gtAdGd GT) i).length ≤ k' →
      AxSpinE8.EndRl GT i [(k + 7, some (stBytes 8 (pch 0x1a))), (k + 9, some (stBytes 8 ret))] k' →
      ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    ⊢ XLd (hlc := hlc) L GT nm T satp0 i cpu Ψ (k + 4) (pch 0x12) 10#5 15#5 16#12 8
        (gprVal rs AxSpinE8.r10) Ocpu -∗
      ((⌜k + 12 < (AxOpsem.grow (gtAdGd GT) i).length⌝ -∗
        ∀ (vcpu vram vs0m vra vs0 vs1 : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = ret ∧ rs' .tlb = rs .tlb ∧
          gprVal rs' AxSpinE8.r10 =
            hres (0#64 + ldRes false 8 vcpu) (AxSpinE8.mycpuRet (gprVal rs AxSpinE8.r4)) ∧
          gprVal rs' AxSpinE8.r2 = gprVal rs AxSpinE8.r2 ∧
          vcpu.length = 8 ∧ vram.length = 8 ∧ vs0m.length = 8 ∧
          vra.length = 8 ∧ vs0.length = 8 ∧ vs1.length = 8 ∧
          gprVal rs' AxSpinE8.r1 = ldRes false 8 vra ∧ gprVal rs' AxSpinE8.r8 = ldRes false 8 vs0 ∧
          gprVal rs' AxSpinHd8.r9 = ldRes false 8 vs1 ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
            r.toNat ≠ 10 → r.toNat ≠ 15 → gprVal rs' r = gprVal rs r) ∧
          graphValue (gtAdGd GT) (i, k + 4) = some vcpu ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 2) = some (stBytes 8 (gprVal rs AxSpinE8.r8)) ∧
          graphData (gtAdGd GT) (i, k + 3) = some (stBytes 8 (gprVal rs AxSpinHd8.r9)) ∧
          graphData (gtAdGd GT) (i, k + 5) = some (stBytes 8 (pch 0x1a)) ∧
          graphData (gtAdGd GT) (i, k + 6) = some (stBytes 8 (AxSpinHd9.s0m rs)) ∧
          graphValue (gtAdGd GT) (i, k + 7) = some vram ∧
          graphValue (gtAdGd GT) (i, k + 8) = some vs0m ∧
          graphValue (gtAdGd GT) (i, k + 9) = some vra ∧
          graphValue (gtAdGd GT) (i, k + 10) = some vs0 ∧
          graphValue (gtAdGd GT) (i, k + 11) = some vs1⌝ -∗
        Ocpu vcpu -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 7)
          iprop(⌜RLfact GT i (paZ Pram) (k + 7) (stBytes 8 (pch 0x1a))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 8)
          iprop(⌜RLfact GT i (paZ Ps0m) (k + 8) (stBytes 8 (AxSpinHd9.s0m rs))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 9)
          iprop(⌜RLfact GT i (paZ Pra) (k + 9) (stBytes 8 (gprVal rs AxSpinE8.r1))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 10)
          iprop(⌜RLfact GT i (paZ Ps0) (k + 10) (stBytes 8 (gprVal rs AxSpinE8.r8))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 11)
          iprop(⌜RLfact GT i (paZ Ps1) (k + 11) (stBytes 8 (gprVal rs AxSpinHd8.r9))⌝) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 12⟩ Ψ) ∧
      (∀ (vcpu vram vs0m vra vs0 vs1 : List (BitVec 8)) (pr : Pexv6),
        ⌜(AxOpsem.grow (gtAdGd GT) i).length = k + 12 ∧
          vcpu.length = 8 ∧ vram.length = 8 ∧ vs0m.length = 8 ∧
          vra.length = 8 ∧ vs0.length = 8 ∧ vs1.length = 8 ∧
          graphValue (gtAdGd GT) (i, k + 4) = some vcpu ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 2) = some (stBytes 8 (gprVal rs AxSpinE8.r8)) ∧
          graphData (gtAdGd GT) (i, k + 3) = some (stBytes 8 (gprVal rs AxSpinHd8.r9)) ∧
          graphData (gtAdGd GT) (i, k + 5) = some (stBytes 8 (pch 0x1a)) ∧
          graphData (gtAdGd GT) (i, k + 6) = some (stBytes 8 (AxSpinHd9.s0m rs)) ∧
          graphValue (gtAdGd GT) (i, k + 7) = some vram ∧
          graphValue (gtAdGd GT) (i, k + 8) = some vs0m ∧
          graphValue (gtAdGd GT) (i, k + 9) = some vra ∧
          graphValue (gtAdGd GT) (i, k + 10) = some vs0 ∧
          graphValue (gtAdGd GT) (i, k + 11) = some vs1⌝ -∗
        Ocpu vcpu -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 7)
          iprop(⌜RLfact GT i (paZ Pram) (k + 7) (stBytes 8 (pch 0x1a))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 8)
          iprop(⌜RLfact GT i (paZ Ps0m) (k + 8) (stBytes 8 (AxSpinHd9.s0m rs))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 9)
          iprop(⌜RLfact GT i (paZ Pra) (k + 9) (stBytes 8 (gprVal rs AxSpinE8.r1))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 10)
          iprop(⌜RLfact GT i (paZ Ps0) (k + 10) (stBytes 8 (gprVal rs AxSpinE8.r8))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 11)
          iprop(⌜RLfact GT i (paZ Ps1) (k + 11) (stBytes 8 (gprVal rs AxSpinHd8.r9))⌝) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k + 12⟩ Ψ)) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs none ib, k + 1⟩ Ψ := by
  intro HR Hw8 Hnr_ra Hnr_s0 Hnr_s1 Hnr_ram Hnr_s0m HD Hc0 HPC0 Hhit0 Hhm0 Hhlc
    HdaS_ra HdaL_ra Hh_ra HdaS_s0 HdaL_s0 Hh_s0 HdaS_s1 HdaL_s1 Hh_s1
    HdaS_ram HdaL_ram Hh_ram HdaS_s0m HdaL_s0m Hh_s0m
    Hpr_ra Hnt_ra Hpr_s0 Hnt_s0 Hpr_s1 Hnt_s1 Hpr_ram Hnt_ram Hpr_s0m Hnt_s0m Hvalm Hval Hret HsP HΨend
  unfold XLd
  iintro Hcpu C
  have HR' := HR
  obtain ⟨_, _, HRm⟩ := HR'
  -- row end at k + 1
  by_cases E1 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 1
  · iclear Hcpu
    iclear C
    iapply (HΨend _ (by omega) (by omega) (by omega) (by ax_spin_e8_endrl) _)
  have XR := XxReg L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XS := XxSt L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  -- ---- 0x08: c.addi sp,-32 (k+1) ----
  iapply (XR _ rs (k + 1) (pch 0x08) true h08 _ _ (retxRefl cpu rs (k + 1) ib) Hc0 HPC0
    (hitWSvpn rs (pch 0x08) (pch 0) (by decide) Hhit0) (htok08 σi T satp0 Htxh)
    (AxSpinE8.owOkSome 2#5 _ (by decide)) rfFH08
    (certAddi _ rs (pch 0x08) true 2#5 2#5 _ (by decide)) (by omega))
  iintro %rs1 %ib1 %HG1
  have HF1 := stepRegs T satp0 _ rs _ _ _ _ _ rs1 (fun _ => rfl) HG1
  have HPC1 : rs1 .PC = pch 0x0a := by rw [gbPc T satp0 _ _ _ _ _ _ HG1]; decide
  have Htl1 : rs1 .tlb = rs .tlb := gbTlb T satp0 _ _ _ _ _ _ HG1
  -- ---- 0x0a: c.sdsp ra,24(sp) (spill at k+1) ----
  iapply (XS _ rs1 (k + 1) (pch 0x0a) true AxSpinHd8.imm24 1#5 2#5
    (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm24) Pra
    (retxRefl cpu rs1 (k + 1) ib1) (gbCtrl T satp0 _ _ _ _ _ _ HG1) HPC1
    (hitWSvpn rs1 (pch 0x0a) (pch 0) (by decide) (hitWAgree rs rs1 _ Htl1 Hhit0))
    (htok0a σi T satp0 Htxh) (by rw [HF1]; ax_spin_hd9_zsimp <;> rfl) HdaS_ra
    (hitWAgree rs rs1 _ Htl1 Hh_ra) Hpr_ra Hw8 (by omega))
  iintro %rs2 %ib2 %HG2 %Hgd1
  -- row end at k + 2
  by_cases E2 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 1 + 1
  · iclear Hcpu
    iclear C
    iapply (HΨend _ (by omega) (by omega) (by omega) (by ax_spin_e8_endrl) _)
  have HF2 := stepRegs0 T satp0 _ rs1 _ _ _ rs2 HF1 HG2
  have HPC2 : rs2 .PC = pch 0x0c := by rw [gbPc T satp0 _ _ _ _ _ _ HG2]; decide
  have Htl2 : rs2 .tlb = rs .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG2).trans Htl1
  -- ---- 0x0c: c.sdsp s0,16(sp) (spill at k+2) ----
  iapply (XS _ rs2 (k + 2) (pch 0x0c) true AxSpinHd8.imm16 8#5 2#5
    (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm16) Ps0
    (retxRefl cpu rs2 (k + 2) ib2) (gbCtrl T satp0 _ _ _ _ _ _ HG2) HPC2
    (hitWSvpn rs2 (pch 0x0c) (pch 0) (by decide) (hitWAgree rs rs2 _ Htl2 Hhit0))
    (htok0c σi T satp0 Htxh) (by rw [HF2]; ax_spin_hd9_zsimp <;> rfl) HdaS_s0
    (hitWAgree rs rs2 _ Htl2 Hh_s0) Hpr_s0 Hw8 (by omega))
  iintro %rs3 %ib3 %HG3 %Hgd2
  -- row end at k + 3
  by_cases E3 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 2 + 1
  · iclear Hcpu
    iclear C
    iapply (HΨend _ (by omega) (by omega) (by omega) (by ax_spin_e8_endrl) _)
  have HF3 := stepRegs0 T satp0 _ rs2 _ _ _ rs3 HF2 HG3
  have HPC3 : rs3 .PC = pch 0x0e := by rw [gbPc T satp0 _ _ _ _ _ _ HG3]; decide
  have Htl3 : rs3 .tlb = rs .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG3).trans Htl2
  -- ---- 0x0e: c.sdsp s1,8(sp) (spill at k+3) ----
  iapply (XS _ rs3 (k + 3) (pch 0x0e) true AxSpinHd8.imm8 9#5 2#5
    (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm8) Ps1
    (retxRefl cpu rs3 (k + 3) ib3) (gbCtrl T satp0 _ _ _ _ _ _ HG3) HPC3
    (hitWSvpn rs3 (pch 0x0e) (pch 0) (by decide) (hitWAgree rs rs3 _ Htl3 Hhit0))
    (htok0e σi T satp0 Htxh) (by rw [HF3]; ax_spin_hd9_zsimp <;> rfl) HdaS_s1
    (hitWAgree rs rs3 _ Htl3 Hh_s1) Hpr_s1 Hw8 (by omega))
  iintro %rs4 %ib4 %HG4 %Hgd3
  -- row end at k + 4
  by_cases E4 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 3 + 1
  · iclear Hcpu
    iclear C
    iapply (HΨend _ (by omega) (by omega) (by omega) (by ax_spin_e8_endrl) _)
  have HF4 := stepRegs0 T satp0 _ rs3 _ _ _ rs4 HF3 HG4
  have HPC4 : rs4 .PC = pch 0x10 := by rw [gbPc T satp0 _ _ _ _ _ _ HG4]; decide
  have Htl4 : rs4 .tlb = rs .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG4).trans Htl3
  -- ---- 0x10: c.addi4spn s0,sp,32 (k+4) ----
  have Hc5 := certAddi (ctrlOkSW T satp0) rs4 (pch 0x10) true 2#5 8#5 (caddi4spnImm 8#8)
    (by decide)
  simp only [HF4] at Hc5
  ax_spin_hd9_zsimp at Hc5
  iapply (XR _ rs4 (k + 4) (pch 0x10) true h10 _ _ (retxRefl cpu rs4 (k + 4) ib4)
    (gbCtrl T satp0 _ _ _ _ _ _ HG4) HPC4
    (hitWSvpn rs4 (pch 0x10) (pch 0) (by decide) (hitWAgree rs rs4 _ Htl4 Hhit0))
    (htok10 σi T satp0 Htxh) (AxSpinE8.owOkSome 8#5 _ (by decide)) rfFH10 Hc5 (by omega))
  iintro %rs5 %ib5 %HG5
  have HF5 := stepRegs T satp0 _ rs4 _ _ _ _ _ rs5 HF4 HG5
  have HPC5 : rs5 .PC = pch 0x12 := by rw [gbPc T satp0 _ _ _ _ _ _ HG5]; decide
  have Htl5 : rs5 .tlb = rs .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG5).trans Htl4
  -- ---- 0x12: c.ld a5,16(a0) — lk->cpu, THROUGH THE CALLER'S LEAF (k+4) ----
  have Hpre : RetX cpu rs5 (k + 4) ⟨.PHart cpu (.pure ()) rs5 none ib5, k + 4⟩ ∧
      ctrlOkSW T satp0 rs5 ∧ rs5 .PC = pch 0x12 ∧ hitW rs5 (pch 0x12) ∧
      gprVal rs5 10#5 = gprVal rs AxSpinE8.r10 ∧
      hitW rs5 (gprVal rs AxSpinE8.r10 + sign_extend (m := 64) (16#12)) ∧
      k + 4 + 1 ≤ (AxOpsem.grow (gtAdGd GT) i).length :=
    ⟨retxRefl cpu rs5 (k + 4) ib5, gbCtrl T satp0 _ _ _ _ _ _ HG5, HPC5,
      hitWSvpn rs5 (pch 0x12) (pch 0) (by decide) (hitWAgree rs rs5 _ Htl5 Hhit0),
      by rw [HF5]; ax_spin_hd9_zsimp, hitWAgree rs rs5 _ Htl5 Hhlc, by omega⟩
  iapply Hcpu $$ %(⟨.PHart cpu (.pure ()) rs5 none ib5, k + 4⟩ : Athread) %rs5 %Hpre
  iintro %vcpu %rs6 %ib6 %Hlvcpu %HG6 %Hgv4 Ho
  -- row end at k + 5
  by_cases E5 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 4 + 1
  · iclear Ho
    iclear C
    iapply (HΨend _ (by omega) (by omega) (by omega) (by ax_spin_e8_endrl) _)
  have HF6 := stepRegs T satp0 _ rs5 _ _ _ _ _ rs6 HF5 HG6
  have HPC6 : rs6 .PC = pch 0x14 := by rw [gbPc T satp0 _ _ _ _ _ _ HG6]; decide
  have Htl6 : rs6 .tlb = rs .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG6).trans Htl5
  -- ---- 0x14: c.mv s1,a5 (k+5) ----
  have Hc7 := certAdd (ctrlOkSW T satp0) rs6 (pch 0x14) true 15#5 0#5 9#5 (by decide)
  simp only [HF6] at Hc7
  ax_spin_hd9_zsimp at Hc7
  iapply (XR _ rs6 (k + 5) (pch 0x14) true h14 _ _ (retxRefl cpu rs6 (k + 5) ib6)
    (gbCtrl T satp0 _ _ _ _ _ _ HG6) HPC6
    (hitWSvpn rs6 (pch 0x14) (pch 0) (by decide) (hitWAgree rs rs6 _ Htl6 Hhit0))
    (htok14 σi T satp0 Htxh) (AxSpinE8.owOkSome 9#5 _ (by decide)) rfFH14 Hc7 (by omega))
  iintro %rs7 %ib7 %HG7
  have HF7 := stepRegs T satp0 _ rs6 _ _ _ _ _ rs7 HF6 HG7
  have HPC7 : rs7 .PC = pch 0x16 := by rw [gbPc T satp0 _ _ _ _ _ _ HG7]; decide
  have Htl7 : rs7 .tlb = rs .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG7).trans Htl6
  -- ---- 0x16: jal ra,mycpu (k+5) ----
  have Hcj := certJAL (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs7 (pch 0x16) false
    3412#21 1#5 (by decide)
  rw [linkOwNz 1#5 _ (by decide)] at Hcj
  iapply (XR _ rs7 (k + 5) (pch 0x16) false h16 _ _ (retxRefl cpu rs7 (k + 5) ib7)
    (gbCtrl T satp0 _ _ _ _ _ _ HG7) HPC7
    (hitWSvpn rs7 (pch 0x16) (pch 0) (by decide) (hitWAgree rs rs7 _ Htl7 Hhit0))
    (htok16 σi T satp0 Htxh) (AxSpinE8.owOkSome 1#5 _ (by decide)) rfFH16 Hcj (by omega))
  iintro %rs8 %ib8 %HG8
  have HF8 := stepRegs T satp0 _ rs7 _ _ _ _ _ rs8 HF7 HG8
  have HPC8 : rs8 .PC = pcm 0 := by rw [gbPc T satp0 _ _ _ _ _ _ HG8]; decide
  have Htl8 : rs8 .tlb = rs .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG8).trans Htl7
  -- ---- THE CALL: wpdMycpu at the inner row position k+5 ----
  have Hsp8 : gprVal rs8 AxSpinE8.r2 = AxSpinHd9.hsp1 rs := by
    rw [HF8]; ax_spin_hd9_zsimp
  have Hra8 : gprVal rs8 AxSpinE8.r1 = pch 0x1a := by
    rw [HF8]; ax_spin_hd9_zsimp; decide
  have Hs08 : gprVal rs8 AxSpinE8.r8 = AxSpinHd9.s0m rs := by
    rw [HF8]; ax_spin_hd9_zsimp
  have Hs18 : gprVal rs8 AxSpinHd8.r9 = 0#64 + ldRes false 8 vcpu := by
    rw [HF8]; ax_spin_hd9_zsimp
  have Htp8 : gprVal rs8 AxSpinE8.r4 = gprVal rs AxSpinE8.r4 := by
    rw [HF8]; ax_spin_hd9_zsimp
  have Hkeep8 : ∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
      r.toNat ≠ 15 → gprVal rs8 r = gprVal rs r := by
    intro r Hr1 Hr2 Hr8 Hr9 Hr15
    rw [HF8]
    by_cases E0 : r.toNat = 0
    · rw [AxSpinE8.updZero _ _ _ _ E0, AxSpinE8.gprValZero rs r E0]
    · have n1 : r ≠ 1#5 := fun h => Hr1 (by rw [h]; rfl)
      have n2 : r ≠ 2#5 := fun h => Hr2 (by rw [h]; rfl)
      have n8 : r ≠ 8#5 := fun h => Hr8 (by rw [h]; rfl)
      have n9 : r ≠ 9#5 := fun h => Hr9 (by rw [h]; rfl)
      have n15 : r ≠ 15#5 := fun h => Hr15 (by rw [h]; rfl)
      simp (disch := assumption) only [AxSpinE8.updOther]
  have WM := wpdMycpuG L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Ψ HΨmid
    (k + 5) rs8 ib8 Pram Ps0m HRm Hw8 Hnr_ram Hnr_s0m (gbCtrl T satp0 _ _ _ _ _ _ HG8)
    HPC8 (hitWAgree rs rs8 _ Htl8 Hhm0)
    (by unfold AxSpinE8.vaRa; rw [Hsp8]; exact HdaS_ram)
    (by unfold AxSpinE8.vaRa; rw [Hsp8]; exact HdaL_ram)
    (by unfold AxSpinE8.vaRa; rw [Hsp8]; exact hitWAgree rs rs8 _ Htl8 Hh_ram)
    (by unfold AxSpinE8.vaS0; rw [Hsp8]; exact HdaS_s0m)
    (by unfold AxSpinE8.vaS0; rw [Hsp8]; exact HdaL_s0m)
    (by unfold AxSpinE8.vaS0; rw [Hsp8]; exact hitWAgree rs rs8 _ Htl8 Hh_s0m)
    Hpr_ram Hnt_ram Hpr_s0m Hnt_s0m (slotsDisjAt _ 4 3 _ _ HD (by decide) rfl rfl)
    (by rw [Hra8, show k + 5 + 2 = k + 7 by omega]; exact Hvalm) (by rw [Hra8]; decide)
    (fun k' h1 h2 h3 hv pr => HΨend k' (by omega) (by omega) h3 (by
      rw [Hra8, show k + 5 + 2 = k + 7 by omega] at hv
      ax_spin_e8_endrl_split
      exact AxSpinE8.endRlHead hv ‹_›) pr)
  rw [Hra8, Hs08, show k + 5 + 1 = k + 6 by omega, show k + 5 + 2 = k + 7 by omega,
    show k + 5 + 3 = k + 8 by omega, show k + 5 + 4 = k + 9 by omega] at WM
  iapply WM
  iintro %vram %vs0m %rs9 %ib9 %⟨Hc9, HPC9, Htl9, Ha09, Hsp9, Hlvram, Hlvs0m, Hr19, Hr89, Hkeep9,
    Hgd5, Hgd6, Hgv7, Hgv8⟩ H7 H8
  -- ---- the EPILOGUE ----
  have Hgd1' : graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs AxSpinE8.r1)) := by
    rw [Hgd1, HF1]; ax_spin_hd9_zsimp
  have Hgd2' : graphData (gtAdGd GT) (i, k + 2) = some (stBytes 8 (gprVal rs AxSpinE8.r8)) := by
    rw [Hgd2, HF2]; ax_spin_hd9_zsimp
  have Hgd3' : graphData (gtAdGd GT) (i, k + 3) = some (stBytes 8 (gprVal rs AxSpinHd8.r9)) := by
    rw [Hgd3, HF3]; ax_spin_hd9_zsimp
  have Htl9' : rs9 .tlb = rs .tlb := Htl9.trans Htl8
  have Hsp9' : gprVal rs9 AxSpinE8.r2 = AxSpinHd9.hsp1 rs := Hsp9.trans Hsp8
  iapply (AxSpinHd8.holdEpiGr L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxh Ψ HΨmid
    k rs9 ib9 ret plk pcl Pra Ps0 Ps1 Pram Ps0m (AxSpinHd9.hsp1 rs)
    (gprVal rs AxSpinE8.r1) (gprVal rs AxSpinE8.r8) (gprVal rs AxSpinHd8.r9)
    HR Hnr_ra Hnr_s0 Hnr_s1 HD Hgd1' Hgd2' Hgd3' Hc9 HPC9 (hitWAgree rs rs9 _ Htl9' Hhit0) Hsp9'
    HdaL_ra (hitWAgree rs rs9 _ Htl9' Hh_ra) HdaL_s0 (hitWAgree rs rs9 _ Htl9' Hh_s0)
    HdaL_s1 (hitWAgree rs rs9 _ Htl9' Hh_s1)
    Hpr_ra Hnt_ra Hpr_s0 Hnt_s0 Hpr_s1 Hnt_s1 Hval Hret HsP
    (fun k' h1 h2 h3 hv pr => HΨend k' (by omega) (by omega) h3 (by
      ax_spin_e8_endrl_split
      exact AxSpinE8.endRlHead hv ‹_›) pr))
  isplit
  · icases C with ⟨C, -⟩
    iintro %Hlt %vra %vs0 %vs1 %rs' %ib' %⟨Hc', HPC', Htl', Ha0', Hsp', Hlvra, Hlvs0, Hlvs1, Hr1',
      Hr8', Hr9', Hkeep', Hgv9, Hgv10, Hgv11⟩ H9 H10 H11
    iapply C $$ %Hlt %vcpu %vram %vs0m %vra %vs0 %vs1 %rs' %ib' [] Ho H7 H8 H9 H10 H11
    ipureintro
    refine ⟨Hc', HPC', Htl'.trans Htl9', ?_, ?_, Hlvcpu, Hlvram, Hlvs0m, Hlvra, Hlvs0, Hlvs1,
      Hr1', Hr8', Hr9', ?_, Hgv4, Hgd1', Hgd2', Hgd3', Hgd5, Hgd6, Hgv7, Hgv8, Hgv9, Hgv10, Hgv11⟩
    · -- a0 = seqz (lk->cpu − mycpu())
      rw [Ha0', Ha09, Htp8,
        Hkeep9 AxSpinHd8.r9 (by decide) (by decide) (by decide) (by decide) (by decide), Hs18]
    · -- sp restored
      rw [Hsp']
      exact AxSpinHd9.frameCancel32 _
    · -- every other GPR kept
      intro r Hr1 Hr2 Hr8 Hr9 Hr10 Hr15
      rw [Hkeep' r Hr1 Hr2 Hr8 Hr9 Hr10, Hkeep9 r Hr1 Hr2 Hr8 Hr10 Hr15,
        Hkeep8 r Hr1 Hr2 Hr8 Hr9 Hr15]
  · -- the END CONTINUATION at k + 12
    iintro %vra %vs0 %vs1 %pr %⟨Hl12, Hlvra, Hlvs0, Hlvs1, Hgv9, Hgv10, Hgv11⟩ H9 H10 H11
    icases C with ⟨-, C⟩
    iapply C $$ %vcpu %vram %vs0m %vra %vs0 %vs1 %pr [] Ho H7 H8 H9 H10 H11
    ipureintro
    exact ⟨Hl12, Hlvcpu, Hlvram, Hlvs0m, Hlvra, Hlvs0, Hlvs1, Hgv4, Hgd1', Hgd2', Hgd3', Hgd5,
      Hgd6, Hgv7, Hgv8, Hgv9, Hgv10, Hgv11⟩

set_option maxHeartbeats 4000000 in
include HL Hcons hmode hasid hppn Hfix Htxm Htxh HΨmid in
/-- (Lean-only, stage 2) THE P-FORM of `holdPro` on a PREFIX row (`RowHoldingP`; the pins
`Hvalm`/`Hval` guarded by `k + 7 < LEN` / `k + 9 < LEN`): a `by_cases` on `LEN ≤ position` at each
row position `k + 1 .. k + 5` here, mycpu's `k + 5 .. k + 9` inside `AxSpinE8.wpdMycpuP`, the
epilogue's `k + 9 .. k + 12` inside `AxSpinHd8.holdEpiP`.  Ends at `k + 1 .. k + 11` are the
WINDOWED, RESOURCE-FREE hook `HΨend`; the end at `k + 12` (before c.addi16sp; the caller's
designated-cut boundary) is the continuation's second conjunct, which RECEIVES the `lk->cpu`
output `Ocpu vcpu` (the caller's deposit), every graph value and the five reload annotations.
P1: the corollary of the gated core `AxSpinHd9.holdProGr` via `AxSpinT2i.gateOfPinG`. -/
theorem holdProP (k : Nat) (rs : RegFile) (ib : Ibch) (ret : BitVec 64) (plk pcl : Int)
    (Pra Ps0 Ps1 Pram Ps0m : BitVec 64) (Ocpu : List (BitVec 8) → IProp GF) :
    -- the row
    RowHoldingP k (AxOpsem.grow (gtAdGd GT) i) true plk pcl (paZ Pra) (paZ Ps0) (paZ Ps1)
      (paZ Pram) (paZ Ps0m) →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pram) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0m) →
    slotsDisj [paZ Pra, paZ Ps0, paZ Ps1, paZ Pram, paZ Ps0m] →
    -- the boundary state
    ctrlOkSW T satp0 rs → rs .PC = pch 0x08 → hitW rs (pch 0) → hitW rs (pcm 0) →
    hitW rs (gprVal rs AxSpinE8.r10 + sign_extend (m := 64) (16#12)) →
    -- the five stack slots
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm24) 8 Pra →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm24) 8 Pra →
    hitW rs (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm24) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm16) 8 Ps0 →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm16) 8 Ps0 →
    hitW rs (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm16) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm8) 8 Ps1 →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm8) 8 Ps1 →
    hitW rs (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm8) →
    dataAtS σi T (.Store .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs) + sign_extend (m := 64) AxSpinE8.immRa) 8 Pram →
    dataAtS σi T (.Load .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs) + sign_extend (m := 64) AxSpinE8.immRa) 8 Pram →
    hitW rs (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs) + sign_extend (m := 64) AxSpinE8.immRa) →
    dataAtS σi T (.Store .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs) + sign_extend (m := 64) AxSpinE8.immS0) 8 Ps0m →
    dataAtS σi T (.Load .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs) + sign_extend (m := 64) AxSpinE8.immS0) 8 Ps0m →
    hitW rs (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs) + sign_extend (m := 64) AxSpinE8.immS0) →
    (∀ j : Nat, j < 8 → priv L (paZ Pra + (j : Int)) i) → ¬ L.xlText (paZ Pra) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0 + (j : Int)) i) → ¬ L.xlText (paZ Ps0) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps1 + (j : Int)) i) → ¬ L.xlText (paZ Ps1) →
    (∀ j : Nat, j < 8 → priv L (paZ Pram + (j : Int)) i) → ¬ L.xlText (paZ Pram) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0m + (j : Int)) i) → ¬ L.xlText (paZ Ps0m) →
    -- the two return addresses (Q20': the ra reloads' graph values; deviation 1)
    (k + 7 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, k + 7) = some (stBytes 8 (pch 0x1a))) →
    (k + 9 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, k + 9) = some (stBytes 8 ret)) → jalrTgt 0#12 ret = ret →
    -- the row-end hook (stage 2, design §B / Q-S2-2), over the window [k + 1, k + 11]
    (∀ k' : Nat, k + 1 ≤ k' → k' ≤ k + 11 → (AxOpsem.grow (gtAdGd GT) i).length ≤ k' →
      ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    ⊢ XLd (hlc := hlc) L GT nm T satp0 i cpu Ψ (k + 4) (pch 0x12) 10#5 15#5 16#12 8
        (gprVal rs AxSpinE8.r10) Ocpu -∗
      ((∀ (vcpu vram vs0m vra vs0 vs1 : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = ret ∧ rs' .tlb = rs .tlb ∧
          gprVal rs' AxSpinE8.r10 =
            hres (0#64 + ldRes false 8 vcpu) (AxSpinE8.mycpuRet (gprVal rs AxSpinE8.r4)) ∧
          gprVal rs' AxSpinE8.r2 = gprVal rs AxSpinE8.r2 ∧
          vcpu.length = 8 ∧ vram.length = 8 ∧ vs0m.length = 8 ∧
          vra.length = 8 ∧ vs0.length = 8 ∧ vs1.length = 8 ∧
          gprVal rs' AxSpinE8.r1 = ldRes false 8 vra ∧ gprVal rs' AxSpinE8.r8 = ldRes false 8 vs0 ∧
          gprVal rs' AxSpinHd8.r9 = ldRes false 8 vs1 ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
            r.toNat ≠ 10 → r.toNat ≠ 15 → gprVal rs' r = gprVal rs r) ∧
          graphValue (gtAdGd GT) (i, k + 4) = some vcpu ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 2) = some (stBytes 8 (gprVal rs AxSpinE8.r8)) ∧
          graphData (gtAdGd GT) (i, k + 3) = some (stBytes 8 (gprVal rs AxSpinHd8.r9)) ∧
          graphData (gtAdGd GT) (i, k + 5) = some (stBytes 8 (pch 0x1a)) ∧
          graphData (gtAdGd GT) (i, k + 6) = some (stBytes 8 (AxSpinHd9.s0m rs)) ∧
          graphValue (gtAdGd GT) (i, k + 7) = some vram ∧
          graphValue (gtAdGd GT) (i, k + 8) = some vs0m ∧
          graphValue (gtAdGd GT) (i, k + 9) = some vra ∧
          graphValue (gtAdGd GT) (i, k + 10) = some vs0 ∧
          graphValue (gtAdGd GT) (i, k + 11) = some vs1⌝ -∗
        Ocpu vcpu -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 7)
          iprop(⌜RLfact GT i (paZ Pram) (k + 7) (stBytes 8 (pch 0x1a))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 8)
          iprop(⌜RLfact GT i (paZ Ps0m) (k + 8) (stBytes 8 (AxSpinHd9.s0m rs))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 9)
          iprop(⌜RLfact GT i (paZ Pra) (k + 9) (stBytes 8 (gprVal rs AxSpinE8.r1))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 10)
          iprop(⌜RLfact GT i (paZ Ps0) (k + 10) (stBytes 8 (gprVal rs AxSpinE8.r8))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 11)
          iprop(⌜RLfact GT i (paZ Ps1) (k + 11) (stBytes 8 (gprVal rs AxSpinHd8.r9))⌝) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 12⟩ Ψ) ∧
      (∀ (vcpu vram vs0m vra vs0 vs1 : List (BitVec 8)) (pr : Pexv6),
        ⌜(AxOpsem.grow (gtAdGd GT) i).length = k + 12 ∧
          vcpu.length = 8 ∧ vram.length = 8 ∧ vs0m.length = 8 ∧
          vra.length = 8 ∧ vs0.length = 8 ∧ vs1.length = 8 ∧
          graphValue (gtAdGd GT) (i, k + 4) = some vcpu ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 2) = some (stBytes 8 (gprVal rs AxSpinE8.r8)) ∧
          graphData (gtAdGd GT) (i, k + 3) = some (stBytes 8 (gprVal rs AxSpinHd8.r9)) ∧
          graphData (gtAdGd GT) (i, k + 5) = some (stBytes 8 (pch 0x1a)) ∧
          graphData (gtAdGd GT) (i, k + 6) = some (stBytes 8 (AxSpinHd9.s0m rs)) ∧
          graphValue (gtAdGd GT) (i, k + 7) = some vram ∧
          graphValue (gtAdGd GT) (i, k + 8) = some vs0m ∧
          graphValue (gtAdGd GT) (i, k + 9) = some vra ∧
          graphValue (gtAdGd GT) (i, k + 10) = some vs0 ∧
          graphValue (gtAdGd GT) (i, k + 11) = some vs1⌝ -∗
        Ocpu vcpu -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 7)
          iprop(⌜RLfact GT i (paZ Pram) (k + 7) (stBytes 8 (pch 0x1a))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 8)
          iprop(⌜RLfact GT i (paZ Ps0m) (k + 8) (stBytes 8 (AxSpinHd9.s0m rs))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 9)
          iprop(⌜RLfact GT i (paZ Pra) (k + 9) (stBytes 8 (gprVal rs AxSpinE8.r1))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 10)
          iprop(⌜RLfact GT i (paZ Ps0) (k + 10) (stBytes 8 (gprVal rs AxSpinE8.r8))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 11)
          iprop(⌜RLfact GT i (paZ Ps1) (k + 11) (stBytes 8 (gprVal rs AxSpinHd8.r9))⌝) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k + 12⟩ Ψ)) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs none ib, k + 1⟩ Ψ := by
  intro HR Hw8 Hnr_ra Hnr_s0 Hnr_s1 Hnr_ram Hnr_s0m HD Hc0 HPC0 Hhit0 Hhm0 Hhlc
    HdaS_ra HdaL_ra Hh_ra HdaS_s0 HdaL_s0 Hh_s0 HdaS_s1 HdaL_s1 Hh_s1
    HdaS_ram HdaL_ram Hh_ram HdaS_s0m HdaL_s0m Hh_s0m
    Hpr_ra Hnt_ra Hpr_s0 Hnt_s0 Hpr_s1 Hnt_s1 Hpr_ram Hnt_ram Hpr_s0m Hnt_s0m Hvalm Hval Hret HΨend
  iintro Hcpu C
  iapply (AxSpinHd9.holdProGr L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxh Ψ
    HΨmid k rs ib ret plk pcl Pra Ps0 Ps1 Pram Ps0m Ocpu HR Hw8 Hnr_ra Hnr_s0 Hnr_s1 Hnr_ram
    Hnr_s0m HD Hc0 HPC0 Hhit0 Hhm0 Hhlc
    HdaS_ra HdaL_ra Hh_ra HdaS_s0 HdaL_s0 Hh_s0 HdaS_s1 HdaL_s1 Hh_s1
    HdaS_ram HdaL_ram Hh_ram HdaS_s0m HdaL_s0m Hh_s0m
    Hpr_ra Hnt_ra Hpr_s0 Hnt_s0 Hpr_s1 Hnt_s1 Hpr_ram Hnt_ram Hpr_s0m Hnt_s0m
    (AxSpinT2i.gateOfPinG Hvalm) (AxSpinT2i.gateOfPinG Hval) Hret (fun _ => Hval)
    (fun k' h1 h2 h3 _ => HΨend k' h1 h2 h3)) $$ Hcpu
  isplit
  · icases C with ⟨C, -⟩
    iintro %-
    iexact C
  · icases C with ⟨-, C⟩
    iexact C

include HL Hcons hmode hasid hppn Hfix Htxm Htxh HΨmid in
/-- Rocq `hold_pro` (deviation 1: Stage C positions; `Hvalm`/`Hval`/`Hret` replace the
return-fetch pins `Hinjm`/`Hstvm`/`Hinj`/`Hstv`/`va_first_read`).  Stage 2: the full-row
corollary of `holdProP` (hook and end continuation vacuous: `k + 12 < LEN`). -/
theorem holdPro (k : Nat) (rs : RegFile) (ib : Ibch) (ret : BitVec 64) (plk pcl : Int)
    (Pra Ps0 Ps1 Pram Ps0m : BitVec 64) (Ocpu : List (BitVec 8) → IProp GF) :
    -- the row
    RowHolding k (AxOpsem.grow (gtAdGd GT) i) true plk pcl (paZ Pra) (paZ Ps0) (paZ Ps1)
      (paZ Pram) (paZ Ps0m) →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pram) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0m) →
    slotsDisj [paZ Pra, paZ Ps0, paZ Ps1, paZ Pram, paZ Ps0m] →
    -- the boundary state
    ctrlOkSW T satp0 rs → rs .PC = pch 0x08 → hitW rs (pch 0) → hitW rs (pcm 0) →
    hitW rs (gprVal rs AxSpinE8.r10 + sign_extend (m := 64) (16#12)) →
    -- the five stack slots
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm24) 8 Pra →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm24) 8 Pra →
    hitW rs (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm24) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm16) 8 Ps0 →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm16) 8 Ps0 →
    hitW rs (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm16) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm8) 8 Ps1 →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm8) 8 Ps1 →
    hitW rs (AxSpinHd9.hsp1 rs + sign_extend (m := 64) AxSpinHd8.imm8) →
    dataAtS σi T (.Store .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs) + sign_extend (m := 64) AxSpinE8.immRa) 8 Pram →
    dataAtS σi T (.Load .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs) + sign_extend (m := 64) AxSpinE8.immRa) 8 Pram →
    hitW rs (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs) + sign_extend (m := 64) AxSpinE8.immRa) →
    dataAtS σi T (.Store .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs) + sign_extend (m := 64) AxSpinE8.immS0) 8 Ps0m →
    dataAtS σi T (.Load .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs) + sign_extend (m := 64) AxSpinE8.immS0) 8 Ps0m →
    hitW rs (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs) + sign_extend (m := 64) AxSpinE8.immS0) →
    (∀ j : Nat, j < 8 → priv L (paZ Pra + (j : Int)) i) → ¬ L.xlText (paZ Pra) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0 + (j : Int)) i) → ¬ L.xlText (paZ Ps0) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps1 + (j : Int)) i) → ¬ L.xlText (paZ Ps1) →
    (∀ j : Nat, j < 8 → priv L (paZ Pram + (j : Int)) i) → ¬ L.xlText (paZ Pram) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0m + (j : Int)) i) → ¬ L.xlText (paZ Ps0m) →
    -- the two return addresses (Q20': the ra reloads' graph values; deviation 1)
    graphValue (gtAdGd GT) (i, k + 7) = some (stBytes 8 (pch 0x1a)) →
    graphValue (gtAdGd GT) (i, k + 9) = some (stBytes 8 ret) → jalrTgt 0#12 ret = ret →
    ⊢ XLd (hlc := hlc) L GT nm T satp0 i cpu Ψ (k + 4) (pch 0x12) 10#5 15#5 16#12 8
        (gprVal rs AxSpinE8.r10) Ocpu -∗
      (∀ (vcpu vram vs0m vra vs0 vs1 : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = ret ∧ rs' .tlb = rs .tlb ∧
          gprVal rs' AxSpinE8.r10 =
            hres (0#64 + ldRes false 8 vcpu) (AxSpinE8.mycpuRet (gprVal rs AxSpinE8.r4)) ∧
          gprVal rs' AxSpinE8.r2 = gprVal rs AxSpinE8.r2 ∧
          vcpu.length = 8 ∧ vram.length = 8 ∧ vs0m.length = 8 ∧
          vra.length = 8 ∧ vs0.length = 8 ∧ vs1.length = 8 ∧
          gprVal rs' AxSpinE8.r1 = ldRes false 8 vra ∧ gprVal rs' AxSpinE8.r8 = ldRes false 8 vs0 ∧
          gprVal rs' AxSpinHd8.r9 = ldRes false 8 vs1 ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
            r.toNat ≠ 10 → r.toNat ≠ 15 → gprVal rs' r = gprVal rs r) ∧
          graphValue (gtAdGd GT) (i, k + 4) = some vcpu ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 2) = some (stBytes 8 (gprVal rs AxSpinE8.r8)) ∧
          graphData (gtAdGd GT) (i, k + 3) = some (stBytes 8 (gprVal rs AxSpinHd8.r9)) ∧
          graphData (gtAdGd GT) (i, k + 5) = some (stBytes 8 (pch 0x1a)) ∧
          graphData (gtAdGd GT) (i, k + 6) = some (stBytes 8 (AxSpinHd9.s0m rs)) ∧
          graphValue (gtAdGd GT) (i, k + 7) = some vram ∧
          graphValue (gtAdGd GT) (i, k + 8) = some vs0m ∧
          graphValue (gtAdGd GT) (i, k + 9) = some vra ∧
          graphValue (gtAdGd GT) (i, k + 10) = some vs0 ∧
          graphValue (gtAdGd GT) (i, k + 11) = some vs1⌝ -∗
        Ocpu vcpu -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 7)
          iprop(⌜RLfact GT i (paZ Pram) (k + 7) (stBytes 8 (pch 0x1a))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 8)
          iprop(⌜RLfact GT i (paZ Ps0m) (k + 8) (stBytes 8 (AxSpinHd9.s0m rs))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 9)
          iprop(⌜RLfact GT i (paZ Pra) (k + 9) (stBytes 8 (gprVal rs AxSpinE8.r1))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 10)
          iprop(⌜RLfact GT i (paZ Ps0) (k + 10) (stBytes 8 (gprVal rs AxSpinE8.r8))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 11)
          iprop(⌜RLfact GT i (paZ Ps1) (k + 11) (stBytes 8 (gprVal rs AxSpinHd8.r9))⌝) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 12⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs none ib, k + 1⟩ Ψ := by
  intro HR Hw8 Hnr_ra Hnr_s0 Hnr_s1 Hnr_ram Hnr_s0m HD Hc0 HPC0 Hhit0 Hhm0 Hhlc
    HdaS_ra HdaL_ra Hh_ra HdaS_s0 HdaL_s0 Hh_s0 HdaS_s1 HdaL_s1 Hh_s1
    HdaS_ram HdaL_ram Hh_ram HdaS_s0m HdaL_s0m Hh_s0m
    Hpr_ra Hnt_ra Hpr_s0 Hnt_s0 Hpr_s1 Hnt_s1 Hpr_ram Hnt_ram Hpr_s0m Hnt_s0m Hvalm Hval Hret
  have Hlen : k + 12 < (AxOpsem.grow (gtAdGd GT) i).length := HR.2.1
  iintro Hcpu C
  iapply (holdProP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxh Ψ HΨmid
    k rs ib ret plk pcl Pra Ps0 Ps1 Pram Ps0m Ocpu
    (AxSpinHd8.rowHoldingPOfFull _ _ _ _ _ _ _ _ _ _ HR) Hw8 Hnr_ra Hnr_s0 Hnr_s1 Hnr_ram
    Hnr_s0m HD Hc0 HPC0 Hhit0 Hhm0 Hhlc
    HdaS_ra HdaL_ra Hh_ra HdaS_s0 HdaL_s0 Hh_s0 HdaS_s1 HdaL_s1 Hh_s1
    HdaS_ram HdaL_ram Hh_ram HdaS_s0m HdaL_s0m Hh_s0m
    Hpr_ra Hnt_ra Hpr_s0 Hnt_s0 Hpr_s1 Hnt_s1 Hpr_ram Hnt_ram Hpr_s0m Hnt_s0m
    (fun _ => Hvalm) (fun _ => Hval) Hret (fun _ _ _ h3 => absurd h3 (by omega))) $$ Hcpu
  isplit
  · iexact C
  · iintro %vcpu %vram %vs0m %vra %vs0 %vs1 %pr %Hp
    exact absurd Hp.1 (by omega)
end pro

end Weak
