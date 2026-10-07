/-
Weak: **memmove's copy loop under WEAK memory, INTERRUPTIBLE** -- the five S-mode leaves of
memmove's forward byte-copy loop stated in `wpNext` form as `Prop`s over `wsrun` / `cobj`
(`wscaddiSpec`, `wslbu1Spec`, `wssb1Spec`, `wsbneTakenSpec`, `wsbneFallSpec`), the objective
byte buffer `wbuf`, and the loop theorem `wmmLoop` proved over the leaves by induction on the
remaining count.

Rocq: `iris/WkMemmoveLoop.v` @ xxvzwolszwmp.

The Rocq header, in substance.  `WeakSmodeFrame` showed that an objective frame survives three
`wpNext` crossings; this file asks the same on the smallest piece of real kernel code with a
LOOP -- memmove's forward byte copy (`ProofMemmove`'s `memmove_fwd_loop`), five instructions at
`memmove+0x18..+0x24`:

    +0x18  c.addi a1,1        cursor++            (source)
    +0x1a  c.addi a4,1        cursor++            (destination)
    +0x1c  lbu   a3,-1(a1)    the byte
    +0x20  sb    a3,-1(a4)    the byte
    +0x24  bne   a5,a1        back to +0x18 unless done

FOUR QUESTIONS AND THEIR ANSWERS.  (1) The loop invariant is stated objectively: the two
buffers are `[∗list]`s of `cobj ξ (… ↦w …)`, no hart, no `Wstate`.  (2) The byte-buffer frame
composes: both buffers are peeled per iteration by `wbufCons` (the `[∗list]` cons, no lemma about
lists and `cobj` needed).  (3) The 1-byte store owes nothing: `wssb1Spec` is objective-in /
objective-out with no released timestamp -- a private write publishes nothing.  (4) NO FENCE is
needed anywhere: the proof contains no fence, no view arithmetic, no timestamp and no `Wstate`.

THE LEAVES ARE HYPOTHESES, NOT AXIOMS (`WeakSmodeFrame`'s discipline): the S-mode weak funnel does
not exist yet, so the five leaves are `Prop`s taken as premises of `wmmLoop`, which is a real
theorem and adds nothing to the trusted base.  They are FILE-BASED (each takes the whole register
file inside `wsrun` and hands it back, as their SC twins do).

**Deviations from Rocq.**

1. VOCABULARY: `Weak/WeakSmodeFrame.lean` deviation 1 (`mword n` ↦ `BitVec n`, `uint x <> 0` ↦
   `x.toNat ≠ 0`, `add_vec_int` ↦ `BitVec.addInt`, `add_vec a b` ↦ `a + b`, `sign_extend' n x` ↦
   `sign_extend (m := n) x`, `zero_extend' 64 v` ↦ `zero_extend (m := 64) v`,
   `regval_into_reg v` ↦ `v`, `pc_is` ↦ `pcIs cpu`, `m !!! Regidx r` ↦ `m.get r`,
   `<[Regidx rd := v]> m` ↦ `m.set rd v`, `regfile` ↦ `RegMap`, `winstr_m` ↦ `winstrM`,
   `WWP Loop` ↦ `wwpTriv ⊤ (WExpr.loop gen cpu)`, `wp_next` ↦ `MachCSL.wpNext`, `zero_reg` ↦
   `0#64`, `dfrac` ↦ `DFrac`).  Further: `pa_z` ↦ `paZ`, `↦w{dq}` ↦ `wpt _ dq _`, `pa_add p j` ↦
   `p + BitVec.ofNat 64 j`, `seq off rem` ↦ `List.range' off rem`, `bv 8` ↦ `BitVec 8`,
   `neq_vec x y` ↦ `x != y`, `mword_of_int k : mword n` ↦ `k#n` (literals) /
   `BitVec.ofNat 64 len` (`Z.of_nat len`), `trunc8 w` (WpSconfMem) ↦ `BitVec.extractLsb' 0 8 w`
   (the Lean SC memmove proof's form), `Virtaddr` ↦ `.Virtaddr`.
2. HARTS EXPLICIT (`WeakSmodeFrame` deviation 2): each spec's first binder is the current hart
   `cpu0`; `wp_next b p (fun CID => K)` ↦ `wpNext b p cpu0 (fun cpu => K cpu)`.  In `wmmLoop`,
   Rocq's anchor `CIDh` is `cpuh` and the iteration's entry hart `CID0` is `cpu0`;
   `(CID0 : CPU) = (CIDh : CPU)` ↦ `cpu0 = cpuh`.  Rocq's `wp_next_chain` ltac is the composed pin
   fact (`WeakSmodeFrame` deviation 5).  `GenId` ↦ explicit `gen : Nat`.
3. CONTEXT: `{!riscvGS Σ, !weakGS Σ}` ↦ `{hlc} [MachGS hlc GF] [WeakGS GF]`.  The section
   hypotheses `Hcaddi Hlbu Hsb Hbne_t Hbne_f` are explicit premises of `wmmLoop` (after `gen`).
4. STATEMENT SHAPES (the `WeakSmodeFrame` convention): `wmmLoop`'s Rocq `P -∗ Q -∗ … -∗ R` is
   `P ⊢ Q -∗ … -∗ R`; the specs keep Rocq's `⊢ (… -∗ …)`.  `wmmLoop`'s `∀ rem off m CID0` is
   kept after the hypotheses `Hlen64`, as in Rocq.
5. KERNEL ADDRESS: Rocq `KernelSyms.memmove` ↦ the Lean image's `MachCSL.KernelSyms.«memmove»`
   (`Xv6.KernelImage`, 0x80000d78); `mmpc off` is `BitVec.ofInt 64 (memmove + off)` as in Rocq.
6. Rocq `Local` lemma `seq_cons` (a duplicated name, WeakBridge) is `WkMemmoveLoop.seqCons`
   (by `rfl`).  Lean-only helpers, file-qualified: `WkMemmoveLoop.getSetEq` / `getSetNe` (the
   `upd_eq` / `upd_ne` of `RegMap.get` over `RegMap.set`), `WkMemmoveLoop.trunc8Zext8` (Rocq
   `WpSconfMem.trunc8_zext8`, not in the Lean tree in this vocabulary),
   `WkMemmoveLoop.paAddStep` / `paAddBack1` / `paAddCmpBound` (Rocq `ByteCursor`'s
   `pa_add_step` / `pa_add_back1` / `pa_add_cmp_bound`, at the immediates used here), and
   `WkMemmoveLoop.wbufFold` (`wbufCons` right-to-left, curried), `WkMemmoveLoop.wbufNil` (the
   empty buffer at two byte functions -- Rocq gets it by conversion; a Lean `.rfl` makes the
   kernel time out), and the pc / alignment facts `WkMemmoveLoop.pc1a` / `pc1c` / `pc20` /
   `pc24` / `pc28` / `pcBack18` / `alBack18` (`decide +kernel`; Rocq's inline `vm_compute`s).

**Rocq → Lean name map.**  `seq_cons` `WkMemmoveLoop.seqCons`, `wscaddi_spec` `wscaddiSpec`,
`wslbu1_spec` `wslbu1Spec`, `wssb1_spec` `wssb1Spec`, `wsbne_taken_spec` `wsbneTakenSpec`,
`wsbne_fall_spec` `wsbneFallSpec`, `mmpc` `mmpc`, `wbuf` `wbuf`, `wbuf_cons` `wbufCons`,
`wmm_loop` `wmmLoop`.

**Dropped:** nothing (Rocq 10 declarations; Lean 10 + 15 helpers).
-/
import Weak.WeakSmodeFrame
import Xv6.KernelImage

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `seq_cons` (`ProofMemmove`'s own list lemma). -/
theorem WkMemmoveLoop.seqCons (start len : Nat) :
    List.range' start (len + 1) = start :: List.range' (start + 1) len := rfl

/-! ## 1. The five leaves, in `wpNext` form over `wsrun` / `cobj` -/

section leafSpecs
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wscaddi_spec`: `c.addi rd, imm` -- register-only, touches no `cobj`.
SC: `wp_caddi_s_sconf`. -/
def wscaddiSpec (gen : Nat) : Prop :=
  ∀ (cpu0 : CPU) (ξ : CtxId) (b : Bool) (p : BitVec 64)
    (pc : BitVec 64) (rd : BitVec 5) (imm : BitVec 6) (m : RegMap),
  rd.toNat ≠ 0 →
  ⊢ wsrun (GF := GF) cpu0 ξ m -∗
      pcIs cpu0 pc -∗
      winstrM (GF := GF) pc true
        (.ITYPE (sign_extend (m := 12) imm, .Regidx rd, .Regidx rd, .ADDI)) -∗
      wpNext b p cpu0 (fun cpu =>
        iprop(wsrun cpu ξ (m.set rd (m.get rd + sign_extend (m := 64) (sign_extend (m := 12) imm))) -∗
          pcIs cpu (BitVec.addInt pc 2) -∗
          wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu))) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu0)

/-- Rocq `wslbu1_spec`: `lbu rd, imm(rs1)` -- ONE byte, from a cell the context owns.
SC: `wp_lbu_s_sconf`. -/
def wslbu1Spec (gen : Nat) : Prop :=
  ∀ (cpu0 : CPU) (ξ : CtxId) (b : Bool) (p : BitVec 64)
    (pc : BitVec 64) (rd rs1 : BitVec 5) (imm : BitVec 12) (m : RegMap)
    (v : BitVec 8) (dq : DFrac),
  rd.toNat ≠ 0 →
  ⊢ wsrun (GF := GF) cpu0 ξ m -∗
      pcIs cpu0 pc -∗
      winstrM (GF := GF) pc false (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 1)) -∗
      cobj ξ (wpt (GF := GF) (paZ (m.get rs1 + sign_extend (m := 64) imm)) dq v) -∗
      wpNext b p cpu0 (fun cpu =>
        iprop(wsrun cpu ξ (m.set rd (zero_extend (m := 64) v)) -∗
          pcIs cpu (BitVec.addInt pc 4) -∗
          cobj ξ (wpt (GF := GF) (paZ (m.get rs1 + sign_extend (m := 64) imm)) dq v) -∗
          wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu))) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu0)

/-- Rocq `wssb1_spec`: `sb rs2, imm(rs1)` -- ONE byte, into a cell the context owns
EXCLUSIVELY.  No released timestamp, no floor, no frozen payload: a private write publishes
nothing.  SC: `wp_sb_s_sconf`. -/
def wssb1Spec (gen : Nat) : Prop :=
  ∀ (cpu0 : CPU) (ξ : CtxId) (b : Bool) (p : BitVec 64)
    (pc : BitVec 64) (rs2 rs1 : BitVec 5) (imm : BitVec 12) (m : RegMap)
    (vold : BitVec 8),
  ⊢ wsrun (GF := GF) cpu0 ξ m -∗
      pcIs cpu0 pc -∗
      winstrM (GF := GF) pc false (.STORE (imm, .Regidx rs2, .Regidx rs1, 1)) -∗
      cobj ξ (wpt (GF := GF) (paZ (m.get rs1 + sign_extend (m := 64) imm)) (DFrac.own 1) vold) -∗
      wpNext b p cpu0 (fun cpu =>
        iprop(wsrun cpu ξ m -∗
          pcIs cpu (BitVec.addInt pc 4) -∗
          cobj ξ (wpt (GF := GF) (paZ (m.get rs1 + sign_extend (m := 64) imm)) (DFrac.own 1)
            (BitVec.extractLsb' 0 8 (m.get rs2))) -∗
          wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu))) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu0)

/-- Rocq `wsbne_taken_spec`: `bne rs1, rs2, imm`, TAKEN -- a backward branch, so the
continuation is guarded.  SC: `wp_bne_taken_s_sconf`. -/
def wsbneTakenSpec (gen : Nat) : Prop :=
  ∀ (cpu0 : CPU) (ξ : CtxId) (b : Bool) (p : BitVec 64)
    (pc : BitVec 64) (imm : BitVec 13) (rs1 rs2 : BitVec 5) (m : RegMap),
  (m.get rs2 != m.get rs1) = true →
  is_aligned_vaddr (.Virtaddr (pc + sign_extend (m := 64) imm)) 2 = true →
  ⊢ wsrun (GF := GF) cpu0 ξ m -∗
      pcIs cpu0 pc -∗
      winstrM (GF := GF) pc false (.BTYPE (imm, .Regidx rs2, .Regidx rs1, .BNE)) -∗
      ▷ wpNext b p cpu0 (fun cpu =>
        iprop(wsrun cpu ξ m -∗
          pcIs cpu (pc + sign_extend (m := 64) imm) -∗
          wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu))) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu0)

/-- Rocq `wsbne_fall_spec`: `bne rs1, rs2, imm`, FALLING THROUGH.
SC: `wp_bne_fall_s_sconf`. -/
def wsbneFallSpec (gen : Nat) : Prop :=
  ∀ (cpu0 : CPU) (ξ : CtxId) (b : Bool) (p : BitVec 64)
    (pc : BitVec 64) (imm : BitVec 13) (rs1 rs2 : BitVec 5) (m : RegMap),
  (m.get rs2 != m.get rs1) = false →
  ⊢ wsrun (GF := GF) cpu0 ξ m -∗
      pcIs cpu0 pc -∗
      winstrM (GF := GF) pc false (.BTYPE (imm, .Regidx rs2, .Regidx rs1, .BNE)) -∗
      wpNext b p cpu0 (fun cpu =>
        iprop(wsrun cpu ξ m -∗
          pcIs cpu (BitVec.addInt pc 4) -∗
          wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu))) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu0)

end leafSpecs

/-! ## 2. THE LOOP

`ProofMemmove`'s loop statement under the swaps, and its proof structure: induction on `rem`, two
harts kept apart (`cpuh` anchors the caller's `wpNext` and is fixed; `cpu0` is the iteration's
entry hart and changes at every recursive step, with `hchain` threading "still traces back to
`cpuh`").  WHAT IS NOT HERE is the point: no `Wstate`, no `wsLe`, no `vwpHold`, no timestamp,
no fence.  The untouched tails of both buffers cross five `wpNext` binders unmentioned. -/

/-- Rocq `mmpc`: an offset into memmove, at the Lean image's address. -/
def mmpc (off : Int) : BitVec 64 :=
  BitVec.ofInt 64 ((KernelSyms.«memmove» : Int) + off)

/-! The loop's pc arithmetic, at the Lean image's address (Lean-only, kernel-checked). -/
theorem WkMemmoveLoop.pc1a : BitVec.addInt (mmpc 0x18) 2 = mmpc 0x1a := by decide +kernel
theorem WkMemmoveLoop.pc1c : BitVec.addInt (mmpc 0x1a) 2 = mmpc 0x1c := by decide +kernel
theorem WkMemmoveLoop.pc20 : BitVec.addInt (mmpc 0x1c) 4 = mmpc 0x20 := by decide +kernel
theorem WkMemmoveLoop.pc24 : BitVec.addInt (mmpc 0x20) 4 = mmpc 0x24 := by decide +kernel
theorem WkMemmoveLoop.pc28 : BitVec.addInt (mmpc 0x24) 4 = mmpc 0x28 := by decide +kernel
theorem WkMemmoveLoop.pcBack18 : mmpc 0x24 + sign_extend (m := 64) (0x1ff4#13) = mmpc 0x18 := by
  decide +kernel
theorem WkMemmoveLoop.alBack18 :
    is_aligned_vaddr (.Virtaddr (mmpc 0x24 + sign_extend (m := 64) (0x1ff4#13))) 2 = true := by
  decide +kernel

/-- Rocq `upd_eq` for `RegMap.get` (Lean-only). -/
theorem WkMemmoveLoop.getSetEq (m : RegMap) (i : BitVec 5) (v : BitVec 64) (h : i ≠ 0#5) :
    (m.set i v).get i = v := by
  simp [RegMap.get, RegMap.set, h]

/-- Rocq `upd_ne` for `RegMap.get` (Lean-only). -/
theorem WkMemmoveLoop.getSetNe (m : RegMap) (i j : BitVec 5) (v : BitVec 64) (h : j ≠ i) :
    (m.set i v).get j = m.get j := by
  simp [RegMap.get, RegMap.set, h]

/-- Rocq `WpSconfMem.trunc8_zext8` (Lean-only here). -/
theorem WkMemmoveLoop.trunc8Zext8 (b : BitVec 8) :
    BitVec.extractLsb' 0 8 (zero_extend (m := 64) b) = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth,
    Nat.shiftRight_zero, Nat.reducePow]
  have := b.isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Rocq `ByteCursor.pa_add_step` at `c.addi …,1` (Lean-only). -/
theorem WkMemmoveLoop.paAddStep (p : BitVec 64) (j : Nat) :
    (p + BitVec.ofNat 64 j) + sign_extend (m := 64) (sign_extend (m := 12) (1#6))
      = p + BitVec.ofNat 64 (j + 1) := by
  rw [show sign_extend (m := 64) (sign_extend (m := 12) (1#6)) = BitVec.ofNat 64 1 by decide +kernel,
    BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Rocq `ByteCursor.pa_add_back1` at `-1(…)` (Lean-only). -/
theorem WkMemmoveLoop.paAddBack1 (p : BitVec 64) (j : Nat) :
    (p + BitVec.ofNat 64 (j + 1)) + sign_extend (m := 64) (0xfff#12)
      = p + BitVec.ofNat 64 j := by
  rw [BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_assoc,
    show BitVec.ofNat 64 1 + sign_extend (m := 64) (0xfff#12) = 0#64 by decide +kernel,
    BitVec.add_zero]

/-- Rocq `ByteCursor.pa_add_cmp_bound`, with `neq_vec_comm` folded in (Lean-only). -/
theorem WkMemmoveLoop.paAddCmpBound (p : BitVec 64) (len j : Nat) (hlen : (len : Int) < 2 ^ 64)
    (hj : j < len) :
    (BitVec.ofNat 64 len + p != p + BitVec.ofNat 64 (j + 1)) = !(Nat.beq (j + 1) len) := by
  by_cases he : j + 1 = len
  · subst he
    simp [Nat.beq_refl, BitVec.add_comm]
  · have hb : Nat.beq (j + 1) len = false := by
      cases h : Nat.beq (j + 1) len
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) he
    rw [hb]
    simp only [Bool.not_false, bne_iff_ne, ne_eq]
    intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
    have := p.isLt
    omega

section loop
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wbuf`: the byte buffer, objectively -- Iris's `[∗list]`, unchanged, with `cobj`
applied per byte. -/
def wbuf (ξ : CtxId) (p : BitVec 64) (off rem : Nat) (bs : Nat → BitVec 8) : IProp GF :=
  iprop([∗list] j ∈ List.range' off rem,
    cobj ξ (wpt (GF := GF) (paZ (p + BitVec.ofNat 64 j)) (DFrac.own 1) (bs j)))

/-- Rocq `wbuf_cons`. -/
theorem wbufCons (ξ : CtxId) (p : BitVec 64) (off rem : Nat) (bs : Nat → BitVec 8) :
    wbuf (GF := GF) ξ p off (rem + 1) bs
      ⊣⊢ cobj ξ (wpt (GF := GF) (paZ (p + BitVec.ofNat 64 off)) (DFrac.own 1) (bs off)) ∗
        wbuf ξ p (off + 1) rem bs := by
  unfold wbuf
  rw [WkMemmoveLoop.seqCons]
  exact BigSepL.bigSepL_cons

/-- `wbufCons` right-to-left, curried (Lean-only). -/
theorem WkMemmoveLoop.wbufFold (ξ : CtxId) (p : BitVec 64) (off rem : Nat)
    (bs : Nat → BitVec 8) :
    cobj ξ (wpt (GF := GF) (paZ (p + BitVec.ofNat 64 off)) (DFrac.own 1) (bs off)) ⊢
      wbuf ξ p (off + 1) rem bs -∗ wbuf ξ p off (rem + 1) bs := by
  iintro H1 H2
  iapply (wbufCons ξ p off rem bs).mpr
  isplitl [H1]
  · iexact H1
  · iexact H2

/-- The empty buffer is the same proposition at any byte function (Lean-only; Rocq: conversion). -/
theorem WkMemmoveLoop.wbufNil (ξ : CtxId) (p : BitVec 64) (off : Nat) (bs bs' : Nat → BitVec 8) :
    wbuf (GF := GF) ξ p off 0 bs ⊢ wbuf ξ p off 0 bs' := by
  unfold wbuf
  rw [show List.range' off 0 = [] from rfl]
  exact BigSepL.bigSepL_nil.mp.trans BigSepL.bigSepL_nil.mpr

set_option maxHeartbeats 1000000 in
/-- Rocq `wmm_loop`. -/
theorem wmmLoop (gen : Nat)
    (Hcaddi : wscaddiSpec (hlc := hlc) (GF := GF) gen)
    (Hlbu : wslbu1Spec (hlc := hlc) (GF := GF) gen)
    (Hsb : wssb1Spec (hlc := hlc) (GF := GF) gen)
    (HbneT : wsbneTakenSpec (hlc := hlc) (GF := GF) gen)
    (HbneF : wsbneFallSpec (hlc := hlc) (GF := GF) gen)
    (ξ : CtxId) (pSrc pDst : BitVec 64) (len : Nat) (srcBytes dstOlds : Nat → BitVec 8)
    (b : Bool) (pcur : BitVec 64) (cpuh : CPU) :
    (len : Int) < 2 ^ 64 →
    ∀ (rem off : Nat) (m : RegMap) (cpu0 : CPU),
    (b = false ∨ pcur = 0#64 → cpu0 = cpuh) →
    off + rem = len → 1 ≤ rem →
    m.get 11#5 = pSrc + BitVec.ofNat 64 off →
    m.get 14#5 = pDst + BitVec.ofNat 64 off →
    m.get 15#5 = BitVec.ofNat 64 len + pSrc →
    wsrun (GF := GF) cpu0 ξ m ⊢
      pcIs cpu0 (mmpc 0x18) -∗
      winstrM (GF := GF) (mmpc 0x18) true
        (.ITYPE (sign_extend (m := 12) (1#6), .Regidx 11#5, .Regidx 11#5, .ADDI)) -∗
      winstrM (GF := GF) (mmpc 0x1a) true
        (.ITYPE (sign_extend (m := 12) (1#6), .Regidx 14#5, .Regidx 14#5, .ADDI)) -∗
      winstrM (GF := GF) (mmpc 0x1c) false (.LOAD (0xfff#12, .Regidx 11#5, .Regidx 13#5, false, 1)) -∗
      winstrM (GF := GF) (mmpc 0x20) false (.STORE (0xfff#12, .Regidx 13#5, .Regidx 14#5, 1)) -∗
      winstrM (GF := GF) (mmpc 0x24) false (.BTYPE (0x1ff4#13, .Regidx 15#5, .Regidx 11#5, .BNE)) -∗
      wbuf ξ pSrc off rem srcBytes -∗
      wbuf ξ pDst off rem dstOlds -∗
      wpNext b pcur cpuh (fun cpu =>
        iprop(∀ mf : RegMap,
          wsrun cpu ξ mf -∗
          pcIs cpu (mmpc 0x28) -∗
          wbuf ξ pSrc off rem srcBytes -∗
          wbuf ξ pDst off rem srcBytes -∗
          ⌜mf.get 10#5 = m.get 10#5⌝ -∗
          wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu))) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu0) := by
  intro hlen rem
  induction rem with
  | zero => intro off m cpu0 _ _ hrem; omega
  | succ rem' ih =>
  intro off m cpu0 hchain hsum _ ha1 ha4 ha5
  iintro Hrun Hpc #Hi18 #Hi1a #Hi1c #Hi20 #Hi24 Hsrc Hdst Hcont
  -- peel the byte at `off` off both buffers
  icases (wbufCons ξ pSrc off rem' srcBytes).mp $$ Hsrc with ⟨Hs0, Hsrc⟩
  icases (wbufCons ξ pDst off rem' dstOlds).mp $$ Hdst with ⟨Hd0, Hdst⟩
  -- ---- +0x18: c.addi a1,1 ----
  have L1 := Hcaddi cpu0 ξ b pcur (mmpc 0x18) 11#5 1#6 m (by decide)
  rw [ha1, WkMemmoveLoop.paAddStep,
    WkMemmoveLoop.pc1a] at L1
  iapply L1 $$ Hrun Hpc Hi18
  unfold wpNext
  iintro %cpu1 %hs1 Hrun Hpc
  -- ---- +0x1a: c.addi a4,1 ----
  have hm1a4 : (m.set 11#5 (pSrc + BitVec.ofNat 64 (off + 1))).get 14#5
      = pDst + BitVec.ofNat 64 off := by
    rw [WkMemmoveLoop.getSetNe _ _ _ _ (by decide), ha4]
  have L2 := Hcaddi cpu1 ξ b pcur (mmpc 0x1a) 14#5 1#6
    (m.set 11#5 (pSrc + BitVec.ofNat 64 (off + 1))) (by decide)
  rw [hm1a4, WkMemmoveLoop.paAddStep,
    WkMemmoveLoop.pc1c] at L2
  iapply L2 $$ Hrun Hpc Hi1a
  unfold wpNext
  iintro %cpu2 %hs2 Hrun Hpc
  -- ---- +0x1c: lbu a3,-1(a1) ----
  have ha12 : ((m.set 11#5 (pSrc + BitVec.ofNat 64 (off + 1))).set 14#5
      (pDst + BitVec.ofNat 64 (off + 1))).get 11#5 = pSrc + BitVec.ofNat 64 (off + 1) := by
    rw [WkMemmoveLoop.getSetNe _ _ _ _ (by decide), WkMemmoveLoop.getSetEq _ _ _ (by decide)]
  have L3 := Hlbu cpu2 ξ b pcur (mmpc 0x1c) 13#5 11#5 0xfff#12
    ((m.set 11#5 (pSrc + BitVec.ofNat 64 (off + 1))).set 14#5 (pDst + BitVec.ofNat 64 (off + 1)))
    (srcBytes off) (DFrac.own 1) (by decide)
  rw [ha12, WkMemmoveLoop.paAddBack1,
    WkMemmoveLoop.pc20] at L3
  iapply L3 $$ Hrun Hpc Hi1c Hs0
  unfold wpNext
  iintro %cpu3 %hs3 Hrun Hpc Hs0
  -- ---- +0x20: sb a3,-1(a4) ----
  have ha3v : (((m.set 11#5 (pSrc + BitVec.ofNat 64 (off + 1))).set 14#5
      (pDst + BitVec.ofNat 64 (off + 1))).set 13#5 (zero_extend (m := 64) (srcBytes off))).get 13#5
      = zero_extend (m := 64) (srcBytes off) :=
    WkMemmoveLoop.getSetEq _ _ _ (by decide)
  have ha4v : (((m.set 11#5 (pSrc + BitVec.ofNat 64 (off + 1))).set 14#5
      (pDst + BitVec.ofNat 64 (off + 1))).set 13#5 (zero_extend (m := 64) (srcBytes off))).get 14#5
      = pDst + BitVec.ofNat 64 (off + 1) := by
    rw [WkMemmoveLoop.getSetNe _ _ _ _ (by decide), WkMemmoveLoop.getSetEq _ _ _ (by decide)]
  have L4 := Hsb cpu3 ξ b pcur (mmpc 0x20) 13#5 14#5 0xfff#12
    (((m.set 11#5 (pSrc + BitVec.ofNat 64 (off + 1))).set 14#5
      (pDst + BitVec.ofNat 64 (off + 1))).set 13#5 (zero_extend (m := 64) (srcBytes off)))
    (dstOlds off)
  rw [ha4v, ha3v, WkMemmoveLoop.paAddBack1, WkMemmoveLoop.trunc8Zext8,
    WkMemmoveLoop.pc24] at L4
  iapply L4 $$ Hrun Hpc Hi20 Hd0
  unfold wpNext
  iintro %cpu4 %hs4 Hrun Hpc Hd0
  -- ---- +0x24: bne a5,a1 ----
  have ha13 : (((m.set 11#5 (pSrc + BitVec.ofNat 64 (off + 1))).set 14#5
      (pDst + BitVec.ofNat 64 (off + 1))).set 13#5 (zero_extend (m := 64) (srcBytes off))).get 11#5
      = pSrc + BitVec.ofNat 64 (off + 1) := by
    rw [WkMemmoveLoop.getSetNe _ _ _ _ (by decide), ha12]
  have ha53 : (((m.set 11#5 (pSrc + BitVec.ofNat 64 (off + 1))).set 14#5
      (pDst + BitVec.ofNat 64 (off + 1))).set 13#5 (zero_extend (m := 64) (srcBytes off))).get 15#5
      = BitVec.ofNat 64 len + pSrc := by
    rw [WkMemmoveLoop.getSetNe _ _ _ _ (by decide), WkMemmoveLoop.getSetNe _ _ _ _ (by decide),
      WkMemmoveLoop.getSetNe _ _ _ _ (by decide), ha5]
  have hcmp : ((((m.set 11#5 (pSrc + BitVec.ofNat 64 (off + 1))).set 14#5
      (pDst + BitVec.ofNat 64 (off + 1))).set 13#5 (zero_extend (m := 64) (srcBytes off))).get 15#5
      != (((m.set 11#5 (pSrc + BitVec.ofNat 64 (off + 1))).set 14#5
      (pDst + BitVec.ofNat 64 (off + 1))).set 13#5 (zero_extend (m := 64) (srcBytes off))).get 11#5)
      = !(Nat.beq (off + 1) len) := by
    rw [ha13, ha53]
    exact WkMemmoveLoop.paAddCmpBound pSrc len off hlen (by omega)
  have ha0eq : (((m.set 11#5 (pSrc + BitVec.ofNat 64 (off + 1))).set 14#5
      (pDst + BitVec.ofNat 64 (off + 1))).set 13#5 (zero_extend (m := 64) (srcBytes off))).get 10#5
      = m.get 10#5 := by
    rw [WkMemmoveLoop.getSetNe _ _ _ _ (by decide), WkMemmoveLoop.getSetNe _ _ _ _ (by decide),
      WkMemmoveLoop.getSetNe _ _ _ _ (by decide)]
  cases rem' with
  | zero =>
    -- last byte: the cursor has reached a5, so the bne falls through
    have hbt : Nat.beq (off + 1) len = true := by
      rw [show len = off + 1 by omega]; exact Nat.beq_refl _
    have hfall := hcmp
    rw [hbt] at hfall
    have L5 := HbneF cpu4 ξ b pcur (mmpc 0x24) 0x1ff4#13 11#5 15#5 _ hfall
    rw [WkMemmoveLoop.pc28] at L5
    iapply L5 $$ Hrun Hpc Hi24
    unfold wpNext
    iintro %cpu5 %hs5 Hrun Hpc
    ihave Hsrc := WkMemmoveLoop.wbufFold ξ pSrc off 0 srcBytes $$ Hs0 Hsrc
    -- the empty tail is the same proposition at any byte function
    ihave Hdst := WkMemmoveLoop.wbufNil ξ pDst (off + 1) dstOlds srcBytes $$ Hdst
    ihave Hdst := WkMemmoveLoop.wbufFold ξ pDst off 0 srcBytes $$ Hd0 Hdst
    iapply Hcont $$ %cpu5
      %(fun h => (hs5 h).trans ((hs4 h).trans ((hs3 h).trans ((hs2 h).trans
        ((hs1 h).trans (hchain h))))))
      %_ Hrun Hpc Hsrc Hdst %ha0eq
  | succ rem'' =>
    -- more bytes: the bne is taken back to +0x18
    have htaken := hcmp
    have hb : Nat.beq (off + 1) len = false := by
      cases h : Nat.beq (off + 1) len
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) (by omega)
    rw [hb] at htaken
    have L5 := HbneT cpu4 ξ b pcur (mmpc 0x24) 0x1ff4#13 11#5 15#5 _ htaken WkMemmoveLoop.alBack18
    rw [WkMemmoveLoop.pcBack18] at L5
    iapply L5 $$ Hrun Hpc Hi24
    inext
    unfold wpNext
    iintro %cpu5 %hs5 Hrun Hpc
    have hchain' : b = false ∨ pcur = 0#64 → cpu5 = cpuh := fun h =>
      (hs5 h).trans ((hs4 h).trans ((hs3 h).trans ((hs2 h).trans ((hs1 h).trans (hchain h)))))
    iapply (ih (off + 1) _ cpu5 hchain' (by omega) (by omega) ha13 ha4v ha53) $$
      Hrun Hpc Hi18 Hi1a Hi1c Hi20 Hi24 Hsrc Hdst
    unfold wpNext
    iintro %cpur %hsr %mf Hrun Hpc Hsrc Hdst %ha0f
    ihave Hsrc := WkMemmoveLoop.wbufFold ξ pSrc off (rem'' + 1) srcBytes $$ Hs0 Hsrc
    ihave Hdst := WkMemmoveLoop.wbufFold ξ pDst off (rem'' + 1) srcBytes $$ Hd0 Hdst
    iapply Hcont $$ %cpur %hsr %mf Hrun Hpc Hsrc Hdst %(ha0f.trans ha0eq)

end loop

end Weak
