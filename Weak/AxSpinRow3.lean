/-
Weak: **spinlock plan, ROW-PINNED leaves, part 3** — xv6's `release` with the s1-EXACTNESS
obligation removed from the callee slot (`releaseWpd6`), the exact map `ex6` that the GROWTH
LAW (AxSpinRow2) makes valid, and the formal account of what stays open (`wCret6`) (AxSL tier).

Rocq: `iris/AxSpinRow3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 `ex6`: release's exact map under the growth law (`exAt`):
     [0x00, 0x0c]: ra, s0, s1, a0 (as AxRelease5's `exRel`);
     [0x16, 0x1e]: s1 — NOT at 0x10 / 0x12: s1 ENTERS the map at the row-pinned
                   `sd zero,16(s1)` (+0x12), by `exOkGrowStore` (`p612`);
   `ex6Rel10Empty`: nothing (beyond the always-exact sp / tp) at holding's return point
   release+0x10 — so `holdRetOk6`: holding's epilogue c.ret (ANY exact map at holding+0x2a) can
   land there; exactly what `holdRetCannotJustifyS1` (AxSpinCtl) refuted for `exRel`.  The pure
   parts of the instruction facts at the words the change touches: `p610` (c.beqz control arm),
   `p612` (sd, grown map), `p616` (fence), `p61a` (sw, grown map).  `p606`: the c.sdsp s1 spill
   still needs s1 exact at release+0x06 (RESIDUALS).
§2 `instr6` / `instrW6`: `instr5` on control words; on a store / AMO whose base is not sp,
   `instr4` at the GROWN map `exAt Ex pc base`; `instr4` otherwise (so every non-store slot of
   `releaseWpd5` is reused by conversion).  `wSdlk6` / `wSwfin6`: the two lock-word store slots
   over `wpStoreRow` (base s1 NOT exact; the sp-based case of the slot's ∀ rs1 goes to the old
   leaf).  Their OFF arm is the section premise `HoffLk` (a store whose LOGICAL address is lk /
   lk+16 of an openable lock has `offBase` at its start) — dischargeable by row pinning, NOT a
   gate.  `releaseWpd6` = `wpReleaseGen` at `instrW6` with the SAME slots as `releaseWpd5`,
   sd / sw now the row leaves.  WHAT IT BUYS: the `rli_12` / `rli_1a` facts hold at an exact map
   with s1 ∉ Ex(+0x10), so the callee slot `w_hold` no longer has to return s1 exact.
§3 WHAT STAYS λ-BOUND, AND WHY: the c.ret slot is ∀ return target; any c.ret leaf on surface v4
   must establish `cur4` at the target, i.e. `Ex L ⊆ Ex pc`, a UNIFORMITY requirement refuted
   for `ex6` AND for `exRel` (`cretSlotUniformEx6` / `cretSlotUniformExRel`).  So
   `wpCretRow` discharges the c.ret LEAF, but the ∀-target SLOT shape needs a caller-indexed
   (cursor) release spec.  Also λ-bound as before: `w_hold`, `w_pop`, `stack_own_slots`, the
   cpu-ownership resources, the kernel text and the `rli_*` facts (in `instrW6` form).
RESIDUALS (Rocq): `relEntryS1NeedsExact` PERSISTS (`p606`).

KERNEL CROSS-CHECK (Xv6/KernelImage.lean, release = 0x80000ce0): +0x06 `c.sdsp s1,8(sp)`
(0xe426), +0x10 `c.beqz a0,+28` (0xcd11), +0x12 `sd zero,16(s1)` (0x0004b823), +0x16
`fence rw,w` (0x0310000f), +0x1a `sw zero,0(s1)` (0x0004a023), +0x2a `c.ret` (0x8082) — the
ASTs this file states, NO DRIFT (pinned by the Lean-only `AxSpinRow3.relWords`, `decide +kernel`
on `Xv6.Kernel.textTree`, and `AxSpinRow3.storeDecode`, `rfl` on the decoder over `drefM`).

## Deviations from Rocq

1. THE INTERFACE IS AxLeafS5's LEAN ONE (as AxRelease4 / AxSpinCtl3 deviation 1): `wSdlk6` /
   `wSwfin6` are stated in the Lean SLOT shape (`wp_s_sd_zero_lkcpu_release_gen` /
   `wp_s_sw_zero_release_gen` over `AxRelease4.kctxW4`, generic in `is_rvc`), as AxRelease4's
   `wSdlk4` / `wSwfin4` (the sp-based case delegates to them); the lock rules are AxRelease4's
   `sdlkRule` / `swlkRule` (AxRelease4 deviation 3: no `lock_finisher` / `Out`).  `HoffLk` is
   over Lean's `lockOpenable γ lk s R D` (extra name `s`).  `releaseWpd6` reuses AxSpinCtl3's
   Lean slots unchanged: `AxSpinCtl3.wJalSlot`, `AxSpinCtl3.wBranchSlot` (its logically-TAKEN
   half `wBrTaken` is TAKEN AS A PREMISE here, a binder of `releaseWpd6`, stated at `instrW6` —
   defeq to AxSpinCtl3's at a branch), `AxSpinCtl3.wEpilogue5` (c.ret = the λ-bound `wCret6`,
   Rocq `w_cret`, stated at `instrW6`).
2. `instrW6` = Rocq's `instrW6` plus AxRelease4's pure `AxRelease4.instrX` (as `instrW5`,
   AxSpinCtl3 deviation 2), so it is definitionally `instrW4` on non-control non-row words and
   `instrW5` on control words.  `rowBase`'s `Z.eqb (uint b) 2` ↦ `b.toNat = 2`.
3. `cretSlotUniform*`: Rocq `ret_pc` ↦ `jumpPc` (the target of the Lean c.ret slot `wCret6`,
   AxRelease4 deviation 4).
4. TYPES / SPELLING as AxSpinCtl3 deviation 4: `mword_of_int k : mword n` ↦ `k#n`, `uint r = k`
   ↦ `r.toNat = k`, `vm_compute` / `rofs` / `lia` ↦ `decide +kernel` + `omega` over `relOff`;
   `s1r` := `AxSpinCtl.r5 9`; the Ltac `uint_c` and the section notations are inlined.
5. `releaseWpd6` is a theorem stated by `type_of%` of the partial application (Rocq
   `Definition release_wpd6 := λ …`).
6. FINDING (Q22, Lean only): this tree's release has its three 4-byte lock words at
   release+0x12 / +0x16 / +0x1a = 0x80000cf2 / cf6 / cfa, which are 2 mod 4, while `insAt3`'s
   `textAt4S` demands a 4-aligned pc (Rocq's build: 4-aligned).  `AxSpinRow3.relStoreTextFalse`:
   `insAt3` is FALSE at those pcs, so the `rli_12` / `rli_16` / `rli_1a` facts (in `instrW4` /
   `instrW5` / `instrW6` form) are unsatisfiable and `releaseWpd4/5/6` are vacuous on the real
   image until the Q22 rework (2-aligned 4-byte text) lands.  The pure parts (`p612` / `p616` /
   `p61a`) are unaffected.
7. INLINED allocpid (AxSpinCtl deviation 2b): the Rocq RESIDUALS' "release's c.sdsp s1 at
   +0x06 spills allocpid's LOADED pid" does not hold in this tree — release is entered with
   allocproc's s1 as acquire+0x2e restored it (`AxSpinCtl.d3RelSpillDataSrc`).  `p606` (a fact
   about `ex6`) is unchanged; no statement here uses allocpid or graph positions, so Stage C
   does not touch this file otherwise.

**Rocq → Lean name map.**  `Ex6` `ex6`, `s1r` `s1r`, `Ex6_rel10_empty` `ex6Rel10Empty`,
`Ex6_rel12_empty` `ex6Rel12Empty`, `hold_ret_ok6` `holdRetOk6`, `Ex_rel_vs_Ex6` `exRelVsEx6`,
`p6_12` `p612`, `p6_16` `p616`, `p6_1a` `p61a`, `p6_10` `p610`, `p6_06` `p606`, `ret_pc_rel16`
`retPcRel16`, `cret_slot_uniform_Ex6` `cretSlotUniformEx6`, `cret_slot_uniform_Ex_rel`
`cretSlotUniformExRel`, `row_base` `rowBase`, `instr6` `instr6`, `instr6_store` `instr6Store`,
`instrW6` `instrW6`, `w_sdlk6` `wSdlk6`, `w_swfin6` `wSwfin6`, `release_wpd6` `releaseWpd6`;
section premise `Hoff_lk` `HoffLk`; λ-bound `w_cret` `wCret6`.  None is in the duplicated-name
table.  Lean-only (file-qualified): `AxSpinRow3.s1rToNat`, `relWords`, `storeDecode`, `relStoreTextFalse`,
`instrW6Sp`, `instrW6Row`, `baseOf`; premise `wBrTaken` (AxSpinCtl3's).

Build: ~2.8 s (VM).

**Dropped:** nothing (Rocq 21 definitions/lemmas; Lean 21 + 7 Lean-only).  **Not ported:** the
Ltacs `uint_c` / `off` / `on_` (inlined), the section notations, the `Check` / `Print
Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxSpinCtl3
import Weak.AxSpinRow2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

/-! # 1. The exact map `ex6` -/

/-- Rocq `Ex6`. -/
def ex6 (pc : BitVec 64) (r : BitVec 5) : Prop :=
  (0 ≤ relOff pc ∧ relOff pc ≤ 12 ∧ (r.toNat = 1 ∨ r.toNat = 8 ∨ r.toNat = 9 ∨ r.toNat = 10)) ∨
  (22 ≤ relOff pc ∧ relOff pc ≤ 30 ∧ r.toNat = 9)

/-- Rocq `s1r`. -/
def s1r : BitVec 5 := AxSpinCtl.r5 9

theorem ex6Rel10Empty (r : BitVec 5) : ¬ ex6 (relAt 0x10) r := by
  have h : relOff (relAt 0x10) = 16 := by decide +kernel
  unfold ex6
  rw [h]
  omega

theorem ex6Rel12Empty (r : BitVec 5) : ¬ ex6 (relAt 0x12) r := by
  have h : relOff (relAt 0x12) = 18 := by decide +kernel
  unfold ex6
  rw [h]
  omega

/-- holding's c.ret (at holding+0x2a, ANY exact map there) can land at release+0x10 under
`ex6` — the obligation `holdRetCannotJustifyS1` refuted for `exRel`. -/
theorem holdRetOk6 (Exh : BitVec 64 → BitVec 5 → Prop) :
    ∀ r, ex6 (relAt 0x10) r → Exh (holdAt 0x2a) r :=
  fun r H => (ex6Rel10Empty r H).elim

/-- ... while `exRel` needs s1 there. -/
theorem exRelVsEx6 : exRel (relAt 0x10) s1r ∧ ¬ ex6 (relAt 0x10) s1r :=
  ⟨exRelS110, ex6Rel10Empty _⟩

theorem AxSpinRow3.s1rToNat : s1r.toNat = 9 := by decide +kernel

/-- +0x12 `sd zero,16(s1)` at the GROWN map: base exact, data x0, and the successor's s1
justified by the growth law. -/
theorem p612 :
    exBase (exAt ex6 (relAt 0x12) s1r) (relAt 0x12) false
      (.STORE (16#12, zreg, .Regidx s1r, 8)) ∧
    exOk (exAt ex6 (relAt 0x12) s1r) (relAt 0x12) false
      (.STORE (16#12, zreg, .Regidx s1r, 8)) := by
  refine ⟨⟨Or.inr (Or.inr ⟨rfl, rfl⟩), Or.inr ⟨rfl, rfl⟩⟩, ?_⟩
  have hne : relAt 0x12 + instrLen false ≠ relAt 0x12 := by decide +kernel
  refine (exOkGrowStore ex6 (relAt 0x12) false _ s1r hne).2 ?_
  intro r Hr
  right
  have h : relOff (relAt 0x12 + instrLen false) = 22 := by decide +kernel
  unfold ex6 at Hr
  rw [h] at Hr
  rcases Hr with ⟨_, h2, _⟩ | ⟨_, _, h9⟩
  · omega
  · exact BitVec.eq_of_toNat_eq (by rw [h9, AxSpinRow3.s1rToNat])

/-- +0x16 `fence rw,w`: s1 stays. -/
theorem p616 :
    exOk ex6 (relAt 0x16) false (.FENCE (0#4, 3#4, 1#4, zreg, zreg)) := by
  intro r Hr
  show ex6 (relAt 0x16) r
  have h1 : relOff (relAt 0x16 + instrLen false) = 26 := by decide +kernel
  have h0 : relOff (relAt 0x16) = 22 := by decide +kernel
  unfold ex6 at Hr ⊢
  rw [h1] at Hr
  rw [h0]
  omega

/-- +0x1a `sw zero,0(s1)`: s1 already exact (the grown map adds nothing new). -/
theorem p61a :
    exBase (exAt ex6 (relAt 0x1a) s1r) (relAt 0x1a) false
      (.STORE (0#12, zreg, .Regidx s1r, 4)) ∧
    exOk (exAt ex6 (relAt 0x1a) s1r) (relAt 0x1a) false
      (.STORE (0#12, zreg, .Regidx s1r, 4)) := by
  refine ⟨⟨Or.inr (Or.inr ⟨rfl, rfl⟩), Or.inr ⟨rfl, rfl⟩⟩, ?_⟩
  intro r Hr
  show exAt ex6 (relAt 0x1a) s1r (relAt 0x1a) r
  rcases Hr with Hr | ⟨E, _⟩
  · left
    have h1 : relOff (relAt 0x1a + instrLen false) = 30 := by decide +kernel
    have h0 : relOff (relAt 0x1a) = 26 := by decide +kernel
    unfold ex6 at Hr ⊢
    rw [h1] at Hr
    rw [h0]
    omega
  · exact absurd E (by decide +kernel)

/-- +0x10 c.beqz: the control arm's exact-map part at `ex6` (both successors have an EMPTY
exact set). -/
theorem p610 : ctlOk5 armedR ex6 (relAt 0x10) true cbeqz10 := by
  have hc : cbeqz10 = .BTYPE (sign_extend (m := 13) (14#8 +++ 0b0#1), .Regidx 0#5,
      .Regidx 10#5, .BEQ) := rfl
  rw [hc]
  unfold ctlOk5
  have h12 : relOff (BitVec.addInt (relAt 0x10) (incr true)) = 18 := by decide +kernel
  have h2c : relOff (relAt 0x10 + sign_extend (m := 64)
      (sign_extend (m := 13) (14#8 +++ 0b0#1) : BitVec 13)) = 44 := by decide +kernel
  refine ⟨by decide +kernel, by unfold armedR; decide +kernel, by unfold armedR; decide +kernel,
    ?_, ?_, ?_, ?_⟩
  · intro r H
    exfalso
    unfold ex6 at H
    omega
  · intro r H
    exfalso
    unfold ex6 at H
    omega
  · intro h
    injection h with h
    exact absurd (congrArg BitVec.toNat h) (by decide)
  · intro h
    injection h with h
    exact absurd (congrArg BitVec.toNat h) (by decide)

/-- +0x06 c.sdsp s1: s1 must STILL be exact at release's entry (the data of a compressed
store) — `relEntryS1NeedsExact` persists. -/
theorem p606 : ex6 (relAt 0x06) s1r := by
  unfold ex6 relOff relAt AxSpinCtl.w64 s1r AxSpinCtl.r5 Xv6.releaseAddr
  decide +kernel

/-- THE ∀-TARGET c.ret SLOT NEEDS A UNIFORM MAP: witness target release+0x16 (s1 exact there,
not at +0x2a). -/
theorem retPcRel16 : jumpPc (relAt 0x16) = relAt 0x16 := by decide +kernel

theorem cretSlotUniformEx6 : ¬ (∀ v r, ex6 (jumpPc v) r → ex6 (relAt 0x2a) r) := by
  intro H
  have H1 := H (relAt 0x16) s1r
  rw [retPcRel16] at H1
  have Hin : ex6 (relAt 0x16) s1r := by
    unfold ex6 relOff relAt AxSpinCtl.w64 s1r AxSpinCtl.r5 Xv6.releaseAddr
    decide +kernel
  have H2 := H1 Hin
  revert H2
  unfold ex6 relOff relAt AxSpinCtl.w64 s1r AxSpinCtl.r5 Xv6.releaseAddr
  decide +kernel

theorem cretSlotUniformExRel : ¬ (∀ v r, exRel (jumpPc v) r → exRel (relAt 0x2a) r) := by
  intro H
  have H1 := H (relAt 0x16) s1r
  rw [retPcRel16] at H1
  have Hin : exRel (relAt 0x16) s1r := by
    unfold exRel relOff relAt AxSpinCtl.w64 s1r AxSpinCtl.r5 Xv6.releaseAddr
    decide +kernel
  have H2 := H1 Hin
  revert H2
  unfold exRel relOff relAt AxSpinCtl.w64 s1r AxSpinCtl.r5 Xv6.releaseAddr
  decide +kernel

/-! ## Kernel cross-check (Lean-only) -/

/-- (Lean-only) the image holds, at the release offsets this file states, exactly these words:
+0x06 `0xe426`, +0x10 `0xcd11`, +0x12 `0x0004b823`, +0x16 `0x0310000f`, +0x1a `0x0004a023`,
+0x2a `0x8082`. -/
theorem AxSpinRow3.relWords :
    ([(relAt 0x06, 2, 0xe426), (relAt 0x10, 2, 0xcd11), (relAt 0x12, 4, 0x0004b823),
      (relAt 0x16, 4, 0x0310000f), (relAt 0x1a, 4, 0x0004a023), (relAt 0x2a, 2, 0x8082)] :
        List (BitVec 64 × Nat × Nat)).all
      (fun p => match Xv6.Kernel.textTree.find? p.1.toNat with
        | some k => Nat.beq k.width p.2.1 && Nat.beq k.enc p.2.2
        | none => false) = true := by
  decide +kernel

/-- (Lean-only) the three 4-byte lock words decode to the ASTs of `p612` / `p616` / `p61a`. -/
theorem AxSpinRow3.storeDecode :
    (∃ i0, Xv6.textDecodeWith drefM (relAt 0x12) =
      some (false, .STORE (16#12, .Regidx 0#5, .Regidx 9#5, 8), i0)) ∧
    (∃ i0, Xv6.textDecodeWith drefM (relAt 0x16) =
      some (false, .FENCE (0#4, 3#4, 1#4, .Regidx 0#5, .Regidx 0#5), i0)) ∧
    (∃ i0, Xv6.textDecodeWith drefM (relAt 0x1a) =
      some (false, .STORE (0#12, .Regidx 0#5, .Regidx 9#5, 4), i0)) :=
  ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- (Lean-only, deviation 6 — Q22) the three 4-byte lock words sit at pcs that are 2 mod 4, so
`insAt3` (whose `textAt4S` demands a 4-aligned pc) is FALSE there. -/
theorem AxSpinRow3.relStoreTextFalse (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (ins : instruction) :
    ¬ insAt3 σi T satp0 (relAt 0x12) ins ∧ ¬ insAt3 σi T satp0 (relAt 0x16) ins ∧
    ¬ insAt3 σi T satp0 (relAt 0x1a) ins := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rintro ⟨_, ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, Hal, _⟩, _⟩
    exact absurd Hal (by decide +kernel)

/-! # 2. `instr6` and `releaseWpd6` -/

/-- (Lean-only) a base register, unless it is sp. -/
def AxSpinRow3.baseOf (b : BitVec 5) : Option (BitVec 5) := if b.toNat = 2 then none else some b

/-- Rocq `row_base`: the base register of a store / AMO, unless it is sp. -/
def rowBase (ins : instruction) : Option (BitVec 5) :=
  match ins with
  | .STORE (_, _, .Regidx b, _) => AxSpinRow3.baseOf b
  | .AMO (_, _, _, _, .Regidx b, _, _) => AxSpinRow3.baseOf b
  | _ => none

section instr6Def
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- Rocq `instr6`. -/
def instr6 (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (Armed : BitVec 64 → Prop) (Ex : BitVec 64 → BitVec 5 → Prop) (Dead : BitVec 64 → Prop)
    (pc : BitVec 64) (is_rvc : Bool) (ins : instruction) : IProp GF :=
  if isCtl ins then instr5 (GF := GF) σi T satp0 Armed Ex Dead pc is_rvc ins
  else match rowBase ins with
    | some b => instr4 (GF := GF) σi T satp0 Armed (exAt Ex pc b) pc is_rvc ins
    | none => instr4 (GF := GF) σi T satp0 Armed Ex pc is_rvc ins

theorem instr6Store (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (Armed : BitVec 64 → Prop) (Ex : BitVec 64 → BitVec 5 → Prop) (Dead : BitVec 64 → Prop)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (r2 : regidx) (rs1 : BitVec 5) (w : Int) :
    instr6 (GF := GF) σi T satp0 Armed Ex Dead pc is_rvc (.STORE (imm, r2, .Regidx rs1, w)) =
      if rs1.toNat = 2 then instr4 (GF := GF) σi T satp0 Armed Ex pc is_rvc (.STORE (imm, r2, .Regidx rs1, w))
      else instr4 (GF := GF) σi T satp0 Armed (exAt Ex pc rs1) pc is_rvc
        (.STORE (imm, r2, .Regidx rs1, w)) := by
  unfold instr6
  rw [show isCtl (.STORE (imm, r2, .Regidx rs1, w)) = false from rfl, if_neg Bool.false_ne_true,
    show rowBase (.STORE (imm, r2, .Regidx rs1, w)) = AxSpinRow3.baseOf rs1 from rfl]
  by_cases h : rs1.toNat = 2
  · rw [if_pos h, show AxSpinRow3.baseOf rs1 = none from if_pos h]
  · rw [if_neg h, show AxSpinRow3.baseOf rs1 = some rs1 from if_neg h]

end instr6Def

section WPdRelease6
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64 × Bool)] [GhostVarG GF Nat]
variable (i : Agent) (cid cpu : CPU) (γm γp γn : GName)
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
  (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
  (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (Ex : BitVec 64 → BitVec 5 → Prop)
variable (Cond : Prop → IProp GF)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i (imgS σi)⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes (imgS σi) base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
variable (Hloc : ∀ GD ls k, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢
    |==> ∃ ls', AxirisG.localInterp GD i (k + 1) ls')
variable (G : Gdexec → Prop)
  (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (dreg damo : Int → Nat → Prop)
variable (Hdmap : ∀ (acc : MemoryAccessType mem_payload) (va : BitVec 64) (w : Nat),
  dreg (paZ va) w ∨ damo (paZ va) w → dataAtS σi T acc va w va)

/- the stack and the owned words (as AxRelease4) -/
variable (stackOwn : PAddr → Nat → IProp GF)
variable (SFPush : ∀ sp0 n k, k ≤ n → stackOwn sp0 n ⊢ stackOwn sp0 k ∗ stackOwn (paStk sp0 k) (n - k))
variable (SFPop : ∀ sp1 n k, stackOwn (paStk sp1 k) n ∗ stackOwn sp1 k ⊢ stackOwn sp1 (n + k))
variable (wpt : PAddr → DFrac → BitVec 64 → IProp GF)
variable (ldRule : ∀ pa dq v, ⊢ wpt pa dq v -∗
  ⌜dreg (paZ pa) 8⌝ ∗
  Fld (dk3 (paZ pa) 8) i (fun _ vs => iprop(wpt pa dq v ∗ Cond (ldRes false 8 vs = v))))
variable (stRule : ∀ pa vold vnew, ⊢ wpt pa (.own 1) vold -∗
  ⌜dreg (paZ pa) 8⌝ ∗
  Fst (dk3 (paZ pa) 8) i (fun _ data => iprop(⌜data = stBytes 8 vnew⌝ -∗ wpt pa (.own 1) vnew)))
variable (CondAnd : ∀ C1 C2, ⊢ Cond C1 -∗ Cond C2 -∗ Cond (C1 ∧ C2))
variable (HnoRmwReg : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n → ¬ dreg base n⌝)

/- the lock resources and the two protocol STORE rules (as AxRelease4) -/
variable {Pay : Type _} (payAt : Pay → IProp GF) (payOk : Pay → Prop)
variable (lockOpenable : GName → BitVec 64 → String → Pay → IProp GF → IProp GF)
  (hlo : ∀ γ lk s R D, Persistent (lockOpenable γ lk s R D))
variable (lockedCore lockedPre : GName → CPU → IProp GF) (lockCtxHeld : IProp GF)
variable (held : CPU → List String → IProp GF)
variable (sdlkRule : ∀ (c0 : CPU) (_cl : WmClass) (γl : GName) (lk : BitVec 64) (s : String)
    (R : Pay) (Dc : IProp GF) (Pd : List (BitVec 8) → Prop),
  (∀ data, Pd data → data = stBytes 8 0#64) →
  ⊢ lockOpenable γl lk s R Dc -∗ lockedCore γl c0 -∗
    ⌜dreg (paZ (lk + 16#64)) 8⌝ ∗
    FstM rvwmoCatConsistent (dk3 (paZ (lk + 16#64)) 8) i
      (fun _ data => iprop(⌜Pd data⌝ -∗ lockedPre γl c0)))
variable (swlkRule : ∀ (c0 : CPU) (cl : WmClass) (γl : GName) (lk : BitVec 64) (s : String)
    (R : Pay) (Dc : IProp GF) (ks : List String) (Pd : List (BitVec 8) → Prop),
  (∀ data, Pd data → data = stBytes 4 0#64) → cl = .WCrel → payOk R →
  ⊢ lockOpenable γl lk s R Dc -∗ lockedPre γl c0 -∗ payAt R -∗ lockCtxHeld -∗ held c0 ks -∗
    ⌜dreg (paZ lk) 4⌝ ∗
    FstM rvwmoCatConsistent (dk3 (paZ lk) 4) i
      (fun _ data => iprop(⌜Pd data⌝ -∗ held c0 (ks.filter (fun x => x ≠ s)) ∗ ⌜s ∈ ks⌝)))
variable (kt : IProp GF) [Persistent kt]

/- the panic arms and their refuted-landing obligation (D4) -/
variable (Dead : BitVec 64 → Prop)
variable (Hdead : ∀ pt, Dead pt → ⊢ refGoal4 i cid cpu γm γp γn T satp0 Ex Cond pt)

/- THE OFF ARM of the two lock-word stores (row pinning; NOT a gate) -/
variable (HoffLk : ∀ (γl : GName) (lk : BitVec 64) (s : String) (R : Pay) (Dc : IProp GF)
    (m : RegMap) (pc : BitVec 64) (rs1 : BitVec 5) (imm : BitVec 12),
  rget cid m rs1 + sign_extend (m := 64) imm = lk + 16#64 ∨
    rget cid m rs1 + sign_extend (m := 64) imm = lk →
  lockOpenable γl lk s R Dc ⊢ ⌜offBase (hlc := hlc) (GF := GF) i cpu T satp0 pc rs1 (rget cid m rs1)⌝)

/-- Rocq `instrW6` (+ deviation 2). -/
def instrW6 (pc : BitVec 64) (is_rvc : Bool) (ins : instruction) : IProp GF :=
  iprop(instr6 (GF := GF) σi T satp0 armedR Ex Dead pc is_rvc ins ∗ ⌜AxRelease4.instrX ins is_rvc⌝)

omit [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64 × Bool)] [GhostVarG GF Nat] in
/-- (Lean-only) an sp-based store: `instrW6` IS `instrW4`. -/
theorem AxSpinRow3.instrW6Sp (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (r2 : regidx)
    (rs1 : BitVec 5) (w : Int) (h : rs1.toNat = 2) :
    instrW6 (GF := GF) σi T satp0 Ex Dead pc is_rvc (.STORE (imm, r2, .Regidx rs1, w)) =
      instrW4 (GF := GF) σi T satp0 Ex pc is_rvc (.STORE (imm, r2, .Regidx rs1, w)) := by
  unfold instrW6 instrW4
  rw [instr6Store, if_pos h]

omit [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64 × Bool)] [GhostVarG GF Nat] in
/-- (Lean-only) a store whose base is not sp: `instr4` at the GROWN map. -/
theorem AxSpinRow3.instrW6Row (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (r2 : regidx)
    (rs1 : BitVec 5) (w : Int) (h : ¬ rs1.toNat = 2) :
    instrW6 (GF := GF) σi T satp0 Ex Dead pc is_rvc (.STORE (imm, r2, .Regidx rs1, w)) =
      iprop(instr4 (GF := GF) σi T satp0 armedR (exAt Ex pc rs1) pc is_rvc
          (.STORE (imm, r2, .Regidx rs1, w)) ∗
        ⌜AxRelease4.instrX (.STORE (imm, r2, .Regidx rs1, w)) is_rvc⌝) := by
  unfold instrW6
  rw [instr6Store, if_neg h]

include hmode hasid hppn Htext Hflow Hloc HG Hdmap sdlkRule hlo HoffLk in
/-- Rocq `w_sdlk6`: release+0x12, `sd zero,16(s1)`, base NOT exact (the
`wp_s_sd_zero_lkcpu_release_gen` slot at `instrW6`). -/
theorem wSdlk6 (c : CPU) (k : KCtx) (hsie : k.sie = false) (pc : BitVec 64) (is_rvc : Bool)
    (imm : BitVec 12) (rs1 : BitVec 5) (γ : GName) (lk : BitVec 64) (s : String) (R : Pay)
    (D : IProp GF) [Timeless D] (Tc : IProp GF) (hrefute : ⊢ Tc -∗ D -∗ (False : IProp GF))
    (haddr : k.rget c rs1 + BitVec.signExtend 64 imm = lk + 16#64) :
    instrW6 σi T satp0 Ex Dead pc is_rvc (instruction.STORE (imm, regidx.Regidx 0#5, regidx.Regidx rs1, 8)) ∗
      AxRelease4.kctxW4 γm γn stackOwn held kt c k ∗ pcW4 γp c pc ∗ lockOpenable γ lk s R D ∗ Tc ∗
      lockedCore γ c ∗
      wpNext k.sie k.proc c (fun cpu' =>
        iprop(AxRelease4.kctxW4 γm γn stackOwn held kt cpu' k -∗ pcW4 γp cpu' (pc + instrLen is_rvc) -∗
          (lockedPre γ c ∗ Tc) -∗ goalW4 i cid cpu γm γp γn T satp0 Ex Cond cpu'))
      ⊢ goalW4 i cid cpu γm γp γn T satp0 Ex Cond c := by
  by_cases hsp : rs1.toNat = 2
  · rw [AxSpinRow3.instrW6Sp σi T satp0 Ex Dead pc is_rvc imm _ rs1 8 hsp]
    exact wSdlk4 (i := i) (cid := cid) (cpu := cpu) (γm := γm) (γp := γp) (γn := γn) (σi := σi)
      (T := T) (satp0 := satp0) (hmode := hmode) (hasid := hasid) (hppn := hppn) (Ex := Ex)
      (Cond := Cond) (Htext := Htext) (Hflow := Hflow) (Hloc := Hloc) (G := G) (HG := HG)
      (dreg := dreg) (damo := damo) (Hdmap := Hdmap) (stackOwn := stackOwn)
      (lockOpenable := lockOpenable) (lockedCore := lockedCore) (lockedPre := lockedPre)
      (held := held) (sdlkRule := sdlkRule) (kt := kt)
      c k hsie pc is_rvc imm rs1 γ lk s R D Tc hrefute haddr
  rw [AxSpinRow3.instrW6Row σi T satp0 Ex Dead pc is_rvc imm _ rs1 8 hsp]
  have _ : Persistent (lockOpenable γ lk s R D) := hlo γ lk s R D
  cases is_rvc
  · dsimp only [instrLen]
    unfold AxRelease4.kctxW4 capW4 pcW4 goalW4
    iintro ⟨⟨Hi, %_⟩, ⟨Hs, Hheld, #Hkt⟩, Hp, #Hlo, HT, Hlc, Hcont⟩
    ihave %Hi4 := instr4Nrvc σi T satp0 armedR (exAt Ex pc rs1) pc _ $$ Hi
    have hb : rs1 ≠ 4#5 := fun h => Hi4.2.2.2.1.1 imm 0#5 rs1 8 rfl (by rw [h])
    have hpa : rget cid k.regs rs1 + sign_extend (m := 64) imm = lk + 16#64 := by
      rw [AxCondM4.rgetCpu cid c k.regs rs1 hb]; exact haddr
    ihave %Hoff := HoffLk γ lk s R D k.regs pc rs1 imm (Or.inl hpa) $$ Hlo
    have Hrule : ∀ cl : WmClass, ⊢ ⌜armedR pc → cl = .WCrel⌝ -∗
        iprop(lockOpenable γ lk s R D ∗ lockedCore γ c) -∗
        ⌜dreg (paZ (rget cid k.regs rs1 + sign_extend (m := 64) imm)) 8⌝ ∗
        FstM rvwmoCatConsistent (dk3 (paZ (rget cid k.regs rs1 + sign_extend (m := 64) imm)) 8) i
          (fun _ data => iprop(⌜(exactAt (exAt Ex pc rs1) pc 0#5 → data = stBytes 8 (rget cid k.regs 0#5)) ∧
            ((0#5 : BitVec 5).toNat = 0 → data = stBytes 8 0#64)⌝ -∗ lockedPre γ c)) := by
      intro cl
      rw [hpa]
      iintro _ ⟨Hlo, Hlc⟩
      iapply (sdlkRule c cl γ lk s R D
        (fun data => (exactAt (exAt Ex pc rs1) pc 0#5 → data = stBytes 8 (rget cid k.regs 0#5)) ∧
          ((0#5 : BitVec 5).toNat = 0 → data = stBytes 8 0#64))
        (fun _ h => h.2 rfl)) $$ Hlo Hlc
    have HS := wpStoreRow i cid cpu γm γp γn σi T satp0 hmode hasid hppn armedR Ex stackOwn Cond
      Htext Hflow Hloc G HG dreg damo Hdmap pc 0#5 rs1 imm 8 k.regs k.avail k.sie k.proc
      iprop(lockOpenable γ lk s R D ∗ lockedCore γ c) (lockedPre γ c)
      Hoff (Or.inr (Or.inr (Or.inr rfl))) ⟨by decide, by decide⟩ Hrule
    unfold cap4 at HS
    unfold cap4
    ihave Hi := (show ⊢ instr4 (GF := GF) σi T satp0 armedR (exAt Ex pc rs1) pc false
        (instruction.STORE (imm, regidx.Regidx 0#5, regidx.Regidx rs1, 8)) from by
      unfold instr4; exact pure_intro ⟨.inl ⟨rfl, Hi4.1, Hi4.2.1⟩, Hi4.2.2.1, Hi4.2.2.2.1,
        Hi4.2.2.2.2.1, Hi4.2.2.2.2.2⟩)
    ihave Hk := AxSymMem3.wpNextSelf k.sie k.proc c _ $$ Hcont
    iapply HS $$ Hs Hp Hi [Hlc]
    · isplitl []
      · iexact Hlo
      · iexact Hlc
    iapply wpNext_intro
    iintro %_ Hs' Hp' Hpost
    iapply Hk $$ [Hs' Hheld] Hp' [Hpost HT]
    · isplitl [Hs']
      · iexact Hs'
      · isplitl [Hheld]
        · iexact Hheld
        · iexact Hkt
    · isplitl [Hpost]
      · iexact Hpost
      · iexact HT
  · iintro ⟨⟨-, %Hw⟩, -⟩
    exact absurd (Hw.1 (Or.inl ⟨imm, rs1, 8, rfl⟩)) (by decide)

include hmode hasid hppn Htext Hflow Hloc HG Hdmap swlkRule hlo HoffLk in
/-- Rocq `w_swfin6`: release+0x1a, `sw zero,0(s1)` — THE RELEASE STORE, base NOT exact (the
`wp_s_sw_zero_release_gen` slot at `instrW6`). -/
theorem wSwfin6 (c : CPU) (k : KCtx) (hsie : k.sie = false) (pc : BitVec 64) (is_rvc : Bool)
    (imm : BitVec 12) (rs1 : BitVec 5) (γ : GName) (lk : BitVec 64) (s : String) (R : Pay)
    (hR : payOk R) (D : IProp GF) [Timeless D] (Tc : IProp GF)
    (hrefute : ⊢ Tc -∗ D -∗ (False : IProp GF))
    (haddr : k.rget c rs1 + BitVec.signExtend 64 imm = lk) :
    instrW6 σi T satp0 Ex Dead pc is_rvc (instruction.STORE (imm, regidx.Regidx 0#5, regidx.Regidx rs1, 4)) ∗
      AxRelease4.kctxW4 γm γn stackOwn held kt c k ∗ pcW4 γp c pc ∗ lockOpenable γ lk s R D ∗ Tc ∗
      lockedPre γ c ∗ lockCtxHeld ∗ payAt R ∗
      wpNext k.sie k.proc c (fun cpu' =>
        iprop(AxRelease4.kctxW4 γm γn stackOwn held kt cpu' (k.withLocks (k.locks.filter (fun x => x ≠ s))) -∗
          pcW4 γp cpu' (pc + instrLen is_rvc) -∗ ⌜s ∈ k.locks⌝ -∗ Tc -∗
          goalW4 i cid cpu γm γp γn T satp0 Ex Cond cpu'))
      ⊢ goalW4 i cid cpu γm γp γn T satp0 Ex Cond c := by
  by_cases hsp : rs1.toNat = 2
  · rw [AxSpinRow3.instrW6Sp σi T satp0 Ex Dead pc is_rvc imm _ rs1 4 hsp]
    exact wSwfin4 (i := i) (cid := cid) (cpu := cpu) (γm := γm) (γp := γp) (γn := γn) (σi := σi)
      (T := T) (satp0 := satp0) (hmode := hmode) (hasid := hasid) (hppn := hppn) (Ex := Ex)
      (Cond := Cond) (Htext := Htext) (Hflow := Hflow) (Hloc := Hloc) (G := G) (HG := HG)
      (dreg := dreg) (damo := damo) (Hdmap := Hdmap) (stackOwn := stackOwn) (payAt := payAt)
      (payOk := payOk) (lockOpenable := lockOpenable) (lockedPre := lockedPre)
      (lockCtxHeld := lockCtxHeld) (held := held) (swlkRule := swlkRule) (kt := kt)
      c k hsie pc is_rvc imm rs1 γ lk s R hR D Tc hrefute haddr
  rw [AxSpinRow3.instrW6Row σi T satp0 Ex Dead pc is_rvc imm _ rs1 4 hsp]
  have _ : Persistent (lockOpenable γ lk s R D) := hlo γ lk s R D
  cases is_rvc
  · dsimp only [instrLen]
    unfold AxRelease4.kctxW4 capW4 pcW4 goalW4
    dsimp only [KCtx.withLocks]
    iintro ⟨⟨Hi, %_⟩, ⟨Hs, Hheld, #Hkt⟩, Hp, #Hlo, HT, Hlp, Hctx, HR, Hcont⟩
    ihave %Hi4 := instr4Nrvc σi T satp0 armedR (exAt Ex pc rs1) pc _ $$ Hi
    have hb : rs1 ≠ 4#5 := fun h => Hi4.2.2.2.1.1 imm 0#5 rs1 4 rfl (by rw [h])
    have hpa : rget cid k.regs rs1 + sign_extend (m := 64) imm = lk := by
      rw [AxCondM4.rgetCpu cid c k.regs rs1 hb]; exact haddr
    have Harm : armedR pc := Hi4.2.2.1 ⟨imm, rs1, rfl⟩
    ihave %Hoff := HoffLk γ lk s R D k.regs pc rs1 imm (Or.inr hpa) $$ Hlo
    have Hrule : ∀ cl : WmClass, ⊢ ⌜armedR pc → cl = .WCrel⌝ -∗
        iprop(lockOpenable γ lk s R D ∗ lockedPre γ c ∗ payAt R ∗ lockCtxHeld ∗ held c k.locks) -∗
        ⌜dreg (paZ (rget cid k.regs rs1 + sign_extend (m := 64) imm)) 4⌝ ∗
        FstM rvwmoCatConsistent (dk3 (paZ (rget cid k.regs rs1 + sign_extend (m := 64) imm)) 4) i
          (fun _ data => iprop(⌜(exactAt (exAt Ex pc rs1) pc 0#5 → data = stBytes 4 (rget cid k.regs 0#5)) ∧
            ((0#5 : BitVec 5).toNat = 0 → data = stBytes 4 0#64)⌝ -∗
            held c (k.locks.filter (fun x => x ≠ s)) ∗ ⌜s ∈ k.locks⌝)) := by
      intro cl
      rw [hpa]
      iintro %Hc ⟨Hlo, Hlp, HR, Hctx, Hh⟩
      iapply (swlkRule c cl γ lk s R D k.locks
        (fun data => (exactAt (exAt Ex pc rs1) pc 0#5 → data = stBytes 4 (rget cid k.regs 0#5)) ∧
          ((0#5 : BitVec 5).toNat = 0 → data = stBytes 4 0#64))
        (fun _ h => h.2 rfl) (Hc Harm) hR) $$ Hlo Hlp HR Hctx Hh
    have HS := wpStoreRow i cid cpu γm γp γn σi T satp0 hmode hasid hppn armedR Ex stackOwn Cond
      Htext Hflow Hloc G HG dreg damo Hdmap pc 0#5 rs1 imm 4 k.regs k.avail k.sie k.proc
      iprop(lockOpenable γ lk s R D ∗ lockedPre γ c ∗ payAt R ∗ lockCtxHeld ∗ held c k.locks)
      iprop(held c (k.locks.filter (fun x => x ≠ s)) ∗ ⌜s ∈ k.locks⌝)
      Hoff (Or.inr (Or.inr (Or.inl rfl))) ⟨by decide, by decide⟩ Hrule
    unfold cap4 at HS
    unfold cap4
    ihave Hi := (show ⊢ instr4 (GF := GF) σi T satp0 armedR (exAt Ex pc rs1) pc false
        (instruction.STORE (imm, regidx.Regidx 0#5, regidx.Regidx rs1, 4)) from by
      unfold instr4; exact pure_intro ⟨.inl ⟨rfl, Hi4.1, Hi4.2.1⟩, Hi4.2.2.1, Hi4.2.2.2.1,
        Hi4.2.2.2.2.1, Hi4.2.2.2.2.2⟩)
    ihave Hk := AxSymMem3.wpNextSelf k.sie k.proc c _ $$ Hcont
    iapply HS $$ Hs Hp Hi [Hlp HR Hctx Hheld]
    · isplitl []
      · iexact Hlo
      · isplitl [Hlp]
        · iexact Hlp
        · isplitl [HR]
          · iexact HR
          · isplitl [Hctx]
            · iexact Hctx
            · iexact Hheld
    iapply wpNext_intro
    iintro %_ Hs' Hp' ⟨Hh', %hmem⟩
    iapply Hk $$ [Hs' Hh'] Hp' [] HT
    · isplitl [Hs']
      · iexact Hs'
      · isplitl [Hh']
        · iexact Hh'
        · iexact Hkt
    · ipureintro
      exact hmem
  · iintro ⟨⟨-, %Hw⟩, -⟩
    exact absurd (Hw.1 (Or.inl ⟨imm, rs1, 4, rfl⟩)) (by decide)

/- the logically-TAKEN half of the Lean branch slot (AxSpinCtl3's premise, at `instrW6`) -/
variable (wBrTaken : ∀ (c : CPU) (k : KCtx) (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 13)
    (rs1 rs2 : BitVec 5) (_hrs1 : rs1 ≠ 0#5) (op : bop),
  bcond op (k.rget c rs1) (k.rget c rs2) = true →
  instrW6 σi T satp0 Ex Dead pc is_rvc (instruction.BTYPE (imm, regidx.Regidx rs2, regidx.Regidx rs1, op)) ∗
    AxRelease4.kctxW4 γm γn stackOwn held kt c k ∗ pcW4 γp c pc ∗
    wpNext k.sie k.proc c (fun cpu' =>
      iprop(AxRelease4.kctxW4 γm γn stackOwn held kt cpu' k -∗
        pcW4 γp cpu' (if bcond op (k.rget cpu' rs1) (k.rget cpu' rs2) then pc + BitVec.signExtend 64 imm
          else pc + instrLen is_rvc) -∗ goalW4 i cid cpu γm γp γn T satp0 Ex Cond cpu'))
    ⊢ goalW4 i cid cpu γm γp γn T satp0 Ex Cond c)

/- Rocq's `stack_own_slots` and `w_cret` (λ-bound), the latter at `instrW6` -/
variable (stackOwnSlots : ∀ (sp : PAddr) (n : Nat), stackOwn sp n ⊣⊢
  [∗list] j ∈ List.range' 1 n, ∃ w : BitVec 64, wpt (paStk sp j) (DFrac.own 1) w)
variable (wCret6 : ∀ (c0 : CPU) (p pc : BitVec 64) (ra : BitVec 5) (m : RegMap) (n : Nat) (b : Bool),
  ra.toNat ≠ 0 →
  ⊢ capW4 γm γn stackOwn c0 m n b p -∗ pcW4 γp c0 pc -∗
    instrW6 σi T satp0 Ex Dead pc true (.JALR (0#12, .Regidx ra, zreg)) -∗
    wpNext b p c0 (fun c1 => iprop(
      capW4 γm γn stackOwn c1 m n b p -∗ pcW4 γp c1 (jumpPc (rget c0 m ra)) -∗
      goalW4 i cid cpu γm γp γn T satp0 Ex Cond c1)) -∗
    goalW4 i cid cpu γm γp γn T satp0 Ex Cond c0)

include hmode hasid hppn Htext Hflow Hloc HG Hdmap SFPush SFPop stRule ldRule CondAnd HnoRmwReg
  hlo sdlkRule swlkRule stackOwnSlots wCret6 Hdead wBrTaken HoffLk in
/-- **THE REPLAY with the two lock-word stores ROW-PINNED** (Rocq `release_wpd6`): AxLeafS5's
`wpReleaseGen` at `goalW4` / `kctxW4` / `pcW4` / `instrW6`, the slots of `releaseWpd5` passed
unchanged (by conversion of `instrW6`), `wp_s_sd_zero_lkcpu_release_gen` := `wSdlk6`,
`wp_s_sw_zero_release_gen` := `wSwfin6` (base s1 NOT exact; off arm `HoffLk`). -/
theorem releaseWpd6 :
    type_of% (AxLeafS5.wpReleaseGen (GF := GF) (Pay := Pay)
      (Goal := goalW4 i cid cpu γm γp γn T satp0 Ex Cond)
      (kctx := AxRelease4.kctxW4 γm γn stackOwn held kt) (pcIs := pcW4 γp)
      (instr := instrW6 σi T satp0 Ex Dead)
      (kernelText := kt) (hkt := inferInstance) (frame4 := AxRelease4.frameW4 wpt)
      (payAt := payAt) (payOk := payOk) (lockOpenable := lockOpenable) (hlo := hlo)
      (lockedCore := lockedCore) (lockedPre := lockedPre) (lockCtxHeld := lockCtxHeld)
      (kctx_kernelText := AxRelease4.kctxW4Kt γm γn stackOwn held kt)
      (wp_prologue4s1 := AxRelease4.wPrologue4 (i := i) (cid := cid) (cpu := cpu) (γm := γm)
        (γp := γp) (γn := γn) (σi := σi) (T := T) (satp0 := satp0) (hmode := hmode)
        (hasid := hasid) (hppn := hppn) (Ex := Ex) (Cond := Cond) (Htext := Htext) (Hflow := Hflow)
        (Hloc := Hloc) (G := G) (HG := HG) (dreg := dreg) (damo := damo) (Hdmap := Hdmap)
        (stackOwn := stackOwn) (SFPush := SFPush) (wpt := wpt) (stRule := stRule) (held := held)
        (kt := kt) (stackOwnSlots := stackOwnSlots))
      (wp_epilogue4s1_gen := AxSpinCtl3.wEpilogue5 (i := i) (cid := cid) (cpu := cpu) (γm := γm)
        (γp := γp) (γn := γn) (σi := σi) (T := T) (satp0 := satp0) (hmode := hmode)
        (hasid := hasid) (hppn := hppn) (Ex := Ex) (Cond := Cond) (Htext := Htext) (Hflow := Hflow)
        (Hloc := Hloc) (G := G) (HG := HG) (dreg := dreg) (damo := damo) (Hdmap := Hdmap)
        (stackOwn := stackOwn) (SFPop := SFPop) (wpt := wpt) (ldRule := ldRule)
        (CondAnd := CondAnd) (HnoRmwReg := HnoRmwReg) (held := held) (kt := kt) (Dead := Dead)
        (stackOwnSlots := stackOwnSlots) (wCret5 := wCret6))
      (wp_s_add := AxRelease4.wAdd4 (i := i) (cid := cid) (cpu := cpu) (γm := γm) (γp := γp)
        (γn := γn) (σi := σi) (T := T) (satp0 := satp0) (hmode := hmode) (hasid := hasid)
        (hppn := hppn) (Ex := Ex) (Cond := Cond) (Htext := Htext) (Hflow := Hflow)
        (stackOwn := stackOwn) (held := held) (kt := kt))
      (wp_s_jal := AxSpinCtl3.wJalSlot (i := i) (cid := cid) (cpu := cpu) (γm := γm) (γp := γp)
        (γn := γn) (σi := σi) (T := T) (satp0 := satp0) (hmode := hmode) (hasid := hasid)
        (hppn := hppn) (Ex := Ex) (Cond := Cond) (Htext := Htext) (Hflow := Hflow) (G := G)
        (HG := HG) (stackOwn := stackOwn) (held := held) (kt := kt) (Dead := Dead))
      (wp_s_branch := AxSpinCtl3.wBranchSlot (i := i) (cid := cid) (cpu := cpu) (γm := γm)
        (γp := γp) (γn := γn) (σi := σi) (T := T) (satp0 := satp0) (hmode := hmode)
        (hasid := hasid) (hppn := hppn) (Ex := Ex) (Cond := Cond) (Htext := Htext) (Hflow := Hflow)
        (G := G) (HG := HG) (stackOwn := stackOwn) (held := held) (kt := kt) (Dead := Dead)
        (Hdead := Hdead) (wBrTaken := wBrTaken))
      (wp_s_fence_rw_w := wFence4 (i := i) (cid := cid) (cpu := cpu) (γm := γm) (γp := γp)
        (γn := γn) (σi := σi) (T := T) (satp0 := satp0) (hmode := hmode) (hasid := hasid)
        (hppn := hppn) (Ex := Ex) (Cond := Cond) (Htext := Htext) (Hflow := Hflow) (Hloc := Hloc)
        (G := G) (HG := HG) (stackOwn := stackOwn) (held := held) (kt := kt))
      (wp_s_sd_zero_lkcpu_release_gen := wSdlk6 (i := i) (cid := cid) (cpu := cpu) (γm := γm)
        (γp := γp) (γn := γn) (σi := σi) (T := T) (satp0 := satp0) (hmode := hmode)
        (hasid := hasid) (hppn := hppn) (Ex := Ex) (Cond := Cond) (Htext := Htext) (Hflow := Hflow)
        (Hloc := Hloc) (G := G) (HG := HG) (dreg := dreg) (damo := damo) (Hdmap := Hdmap)
        (stackOwn := stackOwn) (lockOpenable := lockOpenable) (hlo := hlo)
        (lockedCore := lockedCore) (lockedPre := lockedPre) (held := held) (sdlkRule := sdlkRule)
        (kt := kt) (Dead := Dead) (HoffLk := HoffLk))
      (wp_s_sw_zero_release_gen := wSwfin6 (i := i) (cid := cid) (cpu := cpu) (γm := γm)
        (γp := γp) (γn := γn) (σi := σi) (T := T) (satp0 := satp0) (hmode := hmode)
        (hasid := hasid) (hppn := hppn) (Ex := Ex) (Cond := Cond) (Htext := Htext) (Hflow := Hflow)
        (Hloc := Hloc) (G := G) (HG := HG) (dreg := dreg) (damo := damo) (Hdmap := Hdmap)
        (stackOwn := stackOwn) (payAt := payAt) (payOk := payOk) (lockOpenable := lockOpenable)
        (hlo := hlo) (lockedPre := lockedPre) (lockCtxHeld := lockCtxHeld) (held := held)
        (swlkRule := swlkRule) (kt := kt) (Dead := Dead) (HoffLk := HoffLk))) :=
  AxLeafS5.wpReleaseGen (GF := GF) (Pay := Pay)
    (Goal := goalW4 i cid cpu γm γp γn T satp0 Ex Cond)
    (kctx := AxRelease4.kctxW4 γm γn stackOwn held kt) (pcIs := pcW4 γp)
    (instr := instrW6 σi T satp0 Ex Dead)
    (kernelText := kt) (hkt := inferInstance) (frame4 := AxRelease4.frameW4 wpt)
    (payAt := payAt) (payOk := payOk) (lockOpenable := lockOpenable) (hlo := hlo)
    (lockedCore := lockedCore) (lockedPre := lockedPre) (lockCtxHeld := lockCtxHeld)
    (kctx_kernelText := AxRelease4.kctxW4Kt γm γn stackOwn held kt)
    (wp_prologue4s1 := AxRelease4.wPrologue4 (i := i) (cid := cid) (cpu := cpu) (γm := γm)
      (γp := γp) (γn := γn) (σi := σi) (T := T) (satp0 := satp0) (hmode := hmode)
      (hasid := hasid) (hppn := hppn) (Ex := Ex) (Cond := Cond) (Htext := Htext) (Hflow := Hflow)
      (Hloc := Hloc) (G := G) (HG := HG) (dreg := dreg) (damo := damo) (Hdmap := Hdmap)
      (stackOwn := stackOwn) (SFPush := SFPush) (wpt := wpt) (stRule := stRule) (held := held)
      (kt := kt) (stackOwnSlots := stackOwnSlots))
    (wp_epilogue4s1_gen := AxSpinCtl3.wEpilogue5 (i := i) (cid := cid) (cpu := cpu) (γm := γm)
      (γp := γp) (γn := γn) (σi := σi) (T := T) (satp0 := satp0) (hmode := hmode)
      (hasid := hasid) (hppn := hppn) (Ex := Ex) (Cond := Cond) (Htext := Htext) (Hflow := Hflow)
      (Hloc := Hloc) (G := G) (HG := HG) (dreg := dreg) (damo := damo) (Hdmap := Hdmap)
      (stackOwn := stackOwn) (SFPop := SFPop) (wpt := wpt) (ldRule := ldRule)
      (CondAnd := CondAnd) (HnoRmwReg := HnoRmwReg) (held := held) (kt := kt) (Dead := Dead)
      (stackOwnSlots := stackOwnSlots) (wCret5 := wCret6))
    (wp_s_add := AxRelease4.wAdd4 (i := i) (cid := cid) (cpu := cpu) (γm := γm) (γp := γp)
      (γn := γn) (σi := σi) (T := T) (satp0 := satp0) (hmode := hmode) (hasid := hasid)
      (hppn := hppn) (Ex := Ex) (Cond := Cond) (Htext := Htext) (Hflow := Hflow)
      (stackOwn := stackOwn) (held := held) (kt := kt))
    (wp_s_jal := AxSpinCtl3.wJalSlot (i := i) (cid := cid) (cpu := cpu) (γm := γm) (γp := γp)
      (γn := γn) (σi := σi) (T := T) (satp0 := satp0) (hmode := hmode) (hasid := hasid)
      (hppn := hppn) (Ex := Ex) (Cond := Cond) (Htext := Htext) (Hflow := Hflow) (G := G)
      (HG := HG) (stackOwn := stackOwn) (held := held) (kt := kt) (Dead := Dead))
    (wp_s_branch := AxSpinCtl3.wBranchSlot (i := i) (cid := cid) (cpu := cpu) (γm := γm)
      (γp := γp) (γn := γn) (σi := σi) (T := T) (satp0 := satp0) (hmode := hmode)
      (hasid := hasid) (hppn := hppn) (Ex := Ex) (Cond := Cond) (Htext := Htext) (Hflow := Hflow)
      (G := G) (HG := HG) (stackOwn := stackOwn) (held := held) (kt := kt) (Dead := Dead)
      (Hdead := Hdead) (wBrTaken := wBrTaken))
    (wp_s_fence_rw_w := wFence4 (i := i) (cid := cid) (cpu := cpu) (γm := γm) (γp := γp)
      (γn := γn) (σi := σi) (T := T) (satp0 := satp0) (hmode := hmode) (hasid := hasid)
      (hppn := hppn) (Ex := Ex) (Cond := Cond) (Htext := Htext) (Hflow := Hflow) (Hloc := Hloc)
      (G := G) (HG := HG) (stackOwn := stackOwn) (held := held) (kt := kt))
    (wp_s_sd_zero_lkcpu_release_gen := wSdlk6 (i := i) (cid := cid) (cpu := cpu) (γm := γm)
      (γp := γp) (γn := γn) (σi := σi) (T := T) (satp0 := satp0) (hmode := hmode)
      (hasid := hasid) (hppn := hppn) (Ex := Ex) (Cond := Cond) (Htext := Htext) (Hflow := Hflow)
      (Hloc := Hloc) (G := G) (HG := HG) (dreg := dreg) (damo := damo) (Hdmap := Hdmap)
      (stackOwn := stackOwn) (lockOpenable := lockOpenable) (hlo := hlo)
      (lockedCore := lockedCore) (lockedPre := lockedPre) (held := held) (sdlkRule := sdlkRule)
      (kt := kt) (Dead := Dead) (HoffLk := HoffLk))
    (wp_s_sw_zero_release_gen := wSwfin6 (i := i) (cid := cid) (cpu := cpu) (γm := γm)
      (γp := γp) (γn := γn) (σi := σi) (T := T) (satp0 := satp0) (hmode := hmode)
      (hasid := hasid) (hppn := hppn) (Ex := Ex) (Cond := Cond) (Htext := Htext) (Hflow := Hflow)
      (Hloc := Hloc) (G := G) (HG := HG) (dreg := dreg) (damo := damo) (Hdmap := Hdmap)
      (stackOwn := stackOwn) (payAt := payAt) (payOk := payOk) (lockOpenable := lockOpenable)
      (hlo := hlo) (lockedPre := lockedPre) (lockCtxHeld := lockCtxHeld) (held := held)
      (swlkRule := swlkRule) (kt := kt) (Dead := Dead) (HoffLk := HoffLk))

end WPdRelease6

end Weak
