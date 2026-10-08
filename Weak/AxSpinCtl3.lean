/-
Weak: **xv6's `release` replayed on SURFACE v4 with the CONTROL SLOTS discharged by the
Phase-3 control leaves** (`AxSpinCtl2`) (AxSL tier).

Rocq: `iris/AxSpinCtl3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`release_wpd5` = `AxLeafS5.wp_release_gen_sconf` (the replayed release proof text) at
`GoalW4` / `capW4` / `pcW4` (AxRelease4's) and the NEW instruction fact `instrW5` =
`AxSpinCtl2.instr5` (`instr4` on every non-control word — the nine real slots of
`release_wpd4` are passed UNCHANGED — the control arm on jal / c.beqz / c.ret).  Why not
`release_wpd4`: its `rli_10` premise is ⌜False⌝ (`AxSpinCtl.instr4Rli10False`), so it is
vacuous.  SLOTS NOW REAL (11 of 14): the nine of `release_wpd4`, `w_jal5` (jal holding / jal
pop_off, `AxSpinCtl2.wpJalC5`: static target, exact link) and `w_cbeqz5` (c.beqz a0,panic at
release+0x10, `AxSpinCtl2.wpBrFallC5`: proceeds on the PHYSICAL a0; a physically-taken branch
has a REFUTED condition and lands at the panic arm `Dead` = release+0x2c, discharged by the
section premise `Hdead : ∀ p, Dead p → ⊢ refGoal4 … p`; no `Cond_gate`).  STILL λ-BOUND:
`w_cret` (ra after the c.ldsp reload is not exact, `AxSpinCtl.retRaNotExact`), `w_hold` (the
D3 address gate, `AxSpinCtl.holdRetCannotJustifyS1`), `w_pop`, the stack/cpu-ownership
resources and lemmas, the kernel text and its 20 `rli_*` facts (now in `instr5` form; the pure
part of the control ones is satisfiable on the real bytes: `rli0cCtlSat` / `rli10CtlSat` /
`rli1eCtlSat` / `rli34CtlSat`).  `RefGoal4_pure`: at the pure condition model `Cond C := ⌜C⌝`
the refuted-landing obligation holds outright.

KERNEL CROSS-CHECK (Xv6/KernelImage.lean, release = 0x80000ce0): +0x0c `jal holding`
(0xf07ff0ef, imm 2096902 = −238 → 0x80000bf2), +0x10 `c.beqz a0,+28` (0xcd11, target
+0x2c = 0x80000d0c, the panic arm `auipc a0`), +0x1e `jal pop_off` (0xf9bff0ef, imm 2097050 →
0x80000c98), +0x34 `jal unreachable` (0xb4dff0ef, imm **2095948** = −1204 → 0x80000860).  The
first three agree with Rocq; +0x34 DRIFTS (Rocq `rli34_ctl_sat` at imm 2095970) — recomputed
against this image and pinned by the Lean-only `AxSpinCtl3.jalDecode` (`rfl` on the decoder
over `drefM`) and `AxSpinCtl3.jalTargets` (`decide +kernel` against `KernelSyms`).  No
`AxSpinSpike` graph positions or `allocpid` facts are used here, so Stage C / the inlined
allocpid do not touch this file.

## Deviations from Rocq

1. THE INTERFACE IS AxLeafS5's LEAN ONE (AxLeafS5 deviation 1, AxRelease4 deviation 1): the
   control slots are `wp_s_jal` / `wp_s_branch` over `AxRelease4.kctxW4`, and the c.ret is
   bundled into the frame epilogue `wp_epilogue4s1_gen`.  So
   - `wJal5` / `wCbeqz5` are ported AS STATED (Rocq's slot shape at an arbitrary resuming
     hart `c0`, over `capW4` / `pcW4` / `instrW5`), and the Lean slots are filled by the
     Lean-only `AxSpinCtl3.wJalSlot` (any width, from `wpJalC5`) and `AxSpinCtl3.wBranchSlot`;
   - THE BRANCH SLOT IS GENERIC IN THE DIRECTION in Lean (its continuation lands at `if bcond
     op (k.rget cpu' rs1) (k.rget cpu' rs2) then target else fall`), while Rocq's c.beqz slot
     is the logically-FALLING branch only (`w_cbeqz5`'s premise `rget m rd1 ≠ 0`).  A
     logically-TAKEN branch that physically falls has a refuted condition at the fall-through,
     which is not `Dead` — no premise-free leaf covers it.  So `wBranchSlot` is REAL on the
     logically-falling half (`wpBrFallC5`, Rocq's `w_cbeqz5` content, generic in op / width /
     operands) and takes the logically-TAKEN half as the section premise `wBrTaken` (the Lean
     slot restricted to `bcond … = true`; no Rocq counterpart, never used by the release text,
     which steps the branch at `bcond_beq_one`).  `wBrTaken` is a binder of `releaseWpd5`;
   - `AxSpinCtl3.wEpilogue5` = AxRelease4's `wEpilogue4` at `instrW5` (the c.ret word is a
     CONTROL word, so `instrW5` there is the control arm, not `instrW4`): the c.ldsp ×3 /
     c.addi16sp leaves REAL, the c.ret the λ-bound `wCret5` (Rocq `w_cret` at `instrW5`).
2. `instrW5` = Rocq's `instr5 armedR Ex Dead` plus AxRelease4's pure `instrX` (AxRelease4
   deviation 2), so that on non-control words it is DEFINITIONALLY `instrW4`
   (`AxSpinCtl3.instrW5Off`) and AxRelease4's fillers are passed unchanged (Rocq: "`instr5`
   reduces to `instr4` on them").
3. O2 STAGE C: the control leaves take no `Hloc` (AxSpinCtl2 deviation 1); `Hloc` remains a
   section premise for the data leaves of AxRelease4.
4. TYPES / SPELLING as AxSpinCtl2 deviation 2 / AxRelease4 deviation 4: `CpuId` contexts ↦
   explicit harts; `<[Regidx rd := regval_into_reg (add_vec_int pc 4)]> m` ↦ `m.set rd
   (BitVec.addInt pc 4)`; `eq_vec (rget m rd1) zero_reg = false` ↦ `(rget c0 m rd1 == zero_reg)
   = false`; `mword_of_int z : mword 21` ↦ `z#21`; `vm_compute` ↦ `decide +kernel`, `lia` ↦
   `omega` over `relOff`; `Dead` / `Hdead` are section variables (explicit arguments).  The
   Ltacs `nArmed` / `exrel_none` / `off` / `on_` are inlined.
5. `releaseWpd5` is a theorem stated by `type_of%` of the partial application (Rocq
   `Definition release_wpd5 := λ …`), as AxRelease4's `releaseWpd4`.

**Rocq → Lean name map.**  `DeadR` `deadR`, `rli0c_ctl_sat` `rli0cCtlSat`, `rli1e_ctl_sat`
`rli1eCtlSat`, `rli34_ctl_sat` `rli34CtlSat`, `rli10_ctl_sat` `rli10CtlSat`, `RefGoal4_pure`
`refGoal4Pure`, `instrW5` `instrW5` (deviation 2), `w_jal5` `wJal5`, `w_cbeqz5` `wCbeqz5`,
`release_wpd5` `releaseWpd5`; section parameters unchanged from AxRelease4 plus `Dead`, `Hdead`;
λ-bound `w_cret` ↦ `wCret5`.  None is in the duplicated-name table.  Lean-only (file-qualified):
`AxSpinCtl3.addIntIncr`, `lvRget`, `bcondEq`, `instrW5Off`, `jalDecode`, `jalTargets`,
`wJalSlot`, `wBranchSlot` (+ premise `wBrTaken`), `wEpilogue5`.

Build: ~2.9 s (VM).

**Dropped:** nothing (Rocq 10 definitions/lemmas; Lean 10 + 9 Lean-only).  **Not ported:** the
Ltacs (inlined), the section notations (`GoalW` / `capW` / `pcW`: written out), the `Check` /
`Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxSpinCtl
import Weak.AxSpinCtl2
import Weak.AxRelease4

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

/-! # 1. The pure part of the control `rli_*` facts on the REAL release words -/

/-- Rocq `DeadR`: the panic arm release+0x2c. -/
def deadR (pc : BitVec 64) : Prop := pc = relAt 0x2c

/-- (Lean-only) the kernel cross-check: the three `jal ra` words of release decode, in this
image, to the immediates used below (+0x34: 2095948, Rocq 2095970). -/
theorem AxSpinCtl3.jalDecode :
    (∃ i0, Xv6.textDecodeWith drefM (relAt 0xc) =
      some (false, .JAL (2096902#21, .Regidx 1#5), i0)) ∧
    (∃ i0, Xv6.textDecodeWith drefM (relAt 0x1e) =
      some (false, .JAL (2097050#21, .Regidx 1#5), i0)) ∧
    (∃ i0, Xv6.textDecodeWith drefM (relAt 0x34) =
      some (false, .JAL (2095948#21, .Regidx 1#5), i0)) :=
  ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- (Lean-only) the jal targets are holding / pop_off / unreachable. -/
theorem AxSpinCtl3.jalTargets :
    relAt 0xc + sign_extend (m := 64) (2096902#21 : BitVec 21) = holdAt 0 ∧
    relAt 0x1e + sign_extend (m := 64) (2097050#21 : BitVec 21) =
      AxSpinCtl.w64 (KernelSyms.«pop_off» : Int) ∧
    relAt 0x34 + sign_extend (m := 64) (2095948#21 : BitVec 21) =
      AxSpinCtl.w64 (KernelSyms.«unreachable» : Int) := by
  decide +kernel

theorem rli0cCtlSat :
    ctlOk5 armedR exRel (relAt 0xc) false (.JAL (2096902#21, .Regidx 1#5)) := by
  unfold ctlOk5
  refine ⟨by decide +kernel, by unfold armedR; decide +kernel, ?_⟩
  intro r H
  exfalso
  have h : relOff (relAt 0xc + sign_extend (m := 64) (2096902#21 : BitVec 21)) < 0 := by
    decide +kernel
  unfold exRel at H
  omega

theorem rli1eCtlSat :
    ctlOk5 armedR exRel (relAt 0x1e) false (.JAL (2097050#21, .Regidx 1#5)) := by
  unfold ctlOk5
  refine ⟨by decide +kernel, by unfold armedR; decide +kernel, ?_⟩
  intro r H
  exfalso
  have h : relOff (relAt 0x1e + sign_extend (m := 64) (2097050#21 : BitVec 21)) < 0 := by
    decide +kernel
  unfold exRel at H
  omega

theorem rli34CtlSat :
    ctlOk5 armedR exRel (relAt 0x34) false (.JAL (2095948#21, .Regidx 1#5)) := by
  unfold ctlOk5
  refine ⟨by decide +kernel, by unfold armedR; decide +kernel, ?_⟩
  intro r H
  exfalso
  have h : relOff (relAt 0x34 + sign_extend (m := 64) (2095948#21 : BitVec 21)) < 0 := by
    decide +kernel
  unfold exRel at H
  omega

theorem rli10CtlSat :
    ctlOk5 armedR exRel (relAt 0x10) true cbeqz10 ∧ deadOk deadR exRel (relAt 0x10) cbeqz10 := by
  have hc : cbeqz10 = .BTYPE (sign_extend (m := 13) (14#8 +++ 0b0#1), .Regidx 0#5,
      .Regidx 10#5, .BEQ) := rfl
  rw [hc]
  unfold ctlOk5 deadOk
  have h10 : relOff (relAt 0x10) = 16 := by decide +kernel
  have h12 : relOff (BitVec.addInt (relAt 0x10) (incr true)) = 18 := by decide +kernel
  have h2c : relOff (relAt 0x10 + sign_extend (m := 64)
      (sign_extend (m := 13) (14#8 +++ 0b0#1) : BitVec 13)) = 44 := by decide +kernel
  refine ⟨⟨by decide +kernel, by unfold armedR; decide +kernel, by unfold armedR; decide +kernel,
    ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro r H
    exfalso
    unfold exRel at H
    omega
  · intro r H
    unfold exRel at H ⊢
    omega
  · intro h
    injection h with h
    exact absurd (congrArg BitVec.toNat h) (by decide)
  · intro h
    injection h with h
    exact absurd (congrArg BitVec.toNat h) (by decide)
  · left
    unfold deadR
    decide +kernel

/-! # 2. `refGoal4` at the pure condition model -/

section refgoalPure
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64 × Bool)] [GhostVarG GF Nat]

/-- Rocq `RefGoal4_pure`: at `Cond C := ⌜C⌝` the refuted-landing obligation holds outright. -/
theorem refGoal4Pure (i : Agent) (cid cpu : CPU) (γm γp γn : GName) (T : PTree)
    (satp0 : BitVec 64) (Ex : BitVec 64 → BitVec 5 → Prop) (pt : BitVec 64) :
    ⊢ refGoal4 (GF := GF) i cid cpu γm γp γn T satp0 Ex (fun C => iprop(⌜C⌝)) pt := by
  unfold refGoal4
  iintro %s %m %n %r %C %_ %HnC _ _ _ %HC
  exact (HnC HC).elim

end refgoalPure

/-! # 3. Pure bridges (Lean-only) -/

theorem AxSpinCtl3.addIntIncr (pc : BitVec 64) (is_rvc : Bool) :
    BitVec.addInt pc (incr is_rvc) = pc + instrLen is_rvc := by
  cases is_rvc <;> rfl

theorem AxSpinCtl3.lvRget (c : CPU) (m : RegMap) (r : BitVec 5) :
    AxSpinCtl2.lv c m r = rget c m r := by
  unfold AxSpinCtl2.lv
  split
  · rename_i h
    have h0 : r = 0#5 := BitVec.eq_of_toNat_eq (by simpa using h)
    subst h0
    rw [rget_zero]
    rfl
  · rfl

theorem AxSpinCtl3.bcondEq (op : bop) (a b : BitVec 64) :
    AxSymCtl2.bcond op a b = bcond op a b := by
  cases op <;>
    simp only [AxSymCtl2.bcond, bcond, zopz0zI_s_eq, zopz0zKzJ_s_eq, zopz0zI_u_eq, zopz0zKzJ_u_eq]

/-! # 4. The replay with the control slots real -/

section WPdRelease5
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

/-- Rocq `instrW5` (+ deviation 2). -/
def instrW5 (pc : BitVec 64) (is_rvc : Bool) (ins : instruction) : IProp GF :=
  iprop(instr5 (GF := GF) σi T satp0 armedR Ex Dead pc is_rvc ins ∗ ⌜AxRelease4.instrX ins is_rvc⌝)

omit [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64 × Bool)] [GhostVarG GF Nat] in
/-- (Lean-only) on a non-control word `instrW5` IS `instrW4`. -/
theorem AxSpinCtl3.instrW5Off (pc : BitVec 64) (is_rvc : Bool) (ins : instruction)
    (h : isCtl ins = false) :
    instrW5 (GF := GF) σi T satp0 Ex Dead pc is_rvc ins = instrW4 (GF := GF) σi T satp0 Ex pc is_rvc ins := by
  unfold instrW5 instrW4 instr5
  rw [h]
  rfl

include hmode hasid hppn Htext Hflow HG in
/-- Rocq `w_jal5`: `jal rd, imm` at an arbitrary resuming hart. -/
theorem wJal5 (c0 : CPU) (p pc : BitVec 64) (rd : BitVec 5) (imm : BitVec 21)
    (m : RegMap) (n : Nat) (b : Bool) :
    rd.toNat ≠ 0 → MachCSL.rdOk rd →
    (BitVec.access (pc + sign_extend (m := 64) imm) 0 == 0#1) = true →
    ⊢ capW4 γm γn stackOwn c0 m n b p -∗ pcW4 γp c0 pc -∗
      instrW5 σi T satp0 Ex Dead pc false (.JAL (imm, .Regidx rd)) -∗
      wpNext b p c0 (fun c1 => iprop(
        capW4 γm γn stackOwn c1 (m.set rd (BitVec.addInt pc 4)) n b p -∗
        pcW4 γp c1 (pc + sign_extend (m := 64) imm) -∗
        goalW4 i cid cpu γm γp γn T satp0 Ex Cond c1)) -∗
      goalW4 i cid cpu γm γp γn T satp0 Ex Cond c0 := by
  intro Hrd Hrdok _
  have L := wpJalC5 i cid cpu γm γp γn σi T satp0 hmode hasid hppn armedR Ex stackOwn Cond
    Htext Hflow G HG pc false imm rd m n b p Hrd Hrdok
  have hi : incr false = 4 := rfl
  rw [hi] at L
  unfold cap4 at L
  unfold capW4 pcW4 goalW4 instrW5 instr5 cap4
  simp only [isCtl, ↓reduceIte]
  iintro Hc Hp ⟨%Hi, %_⟩ Hk
  ihave Hk := AxSymMem3.wpNextSelf b p c0 _ $$ Hk
  iapply L $$ Hc Hp %Hi.1
  iapply wpNext_intro
  iintro %_
  iexact Hk

include hmode hasid hppn Htext Hflow HG Hdead in
/-- Rocq `w_cbeqz5`: `c.beqz rs', imm` whose LOGICAL value is ≠ 0 (falls through), at an
arbitrary resuming hart. -/
theorem wCbeqz5 (c0 : CPU) (p pc : BitVec 64) (imm8 : BitVec 8) (rs : cregidx) (rd1 : BitVec 5)
    (m : RegMap) (n : Nat) (b : Bool) :
    creg2reg_idx rs = .Regidx rd1 → rd1.toNat ≠ 0 →
    (rget c0 m rd1 == zero_reg) = false →
    ⊢ capW4 γm γn stackOwn c0 m n b p -∗ pcW4 γp c0 pc -∗
      instrW5 σi T satp0 Ex Dead pc true
        (.BTYPE (sign_extend (m := 13) (imm8 +++ 0b0#1), zreg, creg2reg_idx rs, .BEQ)) -∗
      wpNext b p c0 (fun c1 => iprop(
        capW4 γm γn stackOwn c1 m n b p -∗ pcW4 γp c1 (BitVec.addInt pc 2) -∗
        goalW4 i cid cpu γm γp γn T satp0 Ex Cond c1)) -∗
      goalW4 i cid cpu γm γp γn T satp0 Ex Cond c0 := by
  intro Hrs Hrd1 Hne
  rw [Hrs, AxRelease4.zregEq]
  unfold capW4 pcW4 goalW4 instrW5 instr5
  simp only [isCtl, ↓reduceIte]
  iintro Hc Hp ⟨%Hi, %_⟩ Hk
  obtain ⟨⟨_, ⟨_, _, _, _, _, hn1, _⟩⟩, _⟩ := id Hi
  have Hntp : rd1 ≠ 4#5 := fun h => hn1 (by rw [h])
  have Hf : AxSymCtl2.bcond .BEQ (AxSpinCtl2.lv cid m rd1) (AxSpinCtl2.lv cid m 0#5) = false := by
    rw [AxSpinCtl3.lvRget, AxSpinCtl3.lvRget, AxCondM4.rgetCpu cid c0 m rd1 Hntp, rget_zero]
    exact Hne
  have L := wpBrFallC5 i cid cpu γm γp γn σi T satp0 hmode hasid hppn armedR Ex stackOwn Cond
    Htext Hflow G HG Dead Hdead pc true (sign_extend (m := 13) (imm8 +++ 0b0#1)) 0#5 rd1 .BEQ
    m n b p Hf
  have hi : incr true = 2 := rfl
  rw [hi] at L
  unfold cap4 at L
  unfold cap4
  ihave Hk := AxSymMem3.wpNextSelf b p c0 _ $$ Hk
  iapply L $$ Hc Hp %Hi
  iapply wpNext_intro
  iintro %_
  iexact Hk

/-! ## The Lean slots (deviation 1) -/

include hmode hasid hppn Htext Hflow HG in
/-- (Lean-only) The `wp_s_jal` slot, REAL: `wpJalC5` at the context's fields (either width). -/
theorem AxSpinCtl3.wJalSlot (c : CPU) (k : KCtx) (pc : BitVec 64) (is_rvc : Bool)
    (imm : BitVec 21) (rd : BitVec 5) (hrd : MachCSL.rdOk rd) :
    instrW5 σi T satp0 Ex Dead pc is_rvc (instruction.JAL (imm, regidx.Regidx rd)) ∗
      AxRelease4.kctxW4 γm γn stackOwn held kt c k ∗ pcW4 γp c pc ∗
      wpNext k.sie k.proc c (fun cpu' =>
        iprop(AxRelease4.kctxW4 γm γn stackOwn held kt cpu' (k.setReg rd (pc + instrLen is_rvc)) -∗
          pcW4 γp cpu' (pc + BitVec.signExtend 64 imm) -∗ goalW4 i cid cpu γm γp γn T satp0 Ex Cond cpu'))
      ⊢ goalW4 i cid cpu γm γp γn T satp0 Ex Cond c := by
  have Hrd : rd.toNat ≠ 0 := fun h => hrd.1 (BitVec.eq_of_toNat_eq (by simpa using h))
  have L := wpJalC5 i cid cpu γm γp γn σi T satp0 hmode hasid hppn armedR Ex stackOwn Cond
    Htext Hflow G HG pc is_rvc imm rd k.regs k.avail k.sie k.proc Hrd hrd
  rw [AxSpinCtl3.addIntIncr, show sign_extend (m := 64) imm = BitVec.signExtend 64 imm from rfl] at L
  unfold cap4 at L
  unfold instrW5 instr5 AxRelease4.kctxW4 capW4 pcW4 goalW4 cap4
  simp only [isCtl, ↓reduceIte, KCtx.setReg_regs, KCtx.setReg_avail, KCtx.setReg_sie,
    KCtx.setReg_locks]
  iintro ⟨⟨%Hi, %_⟩, ⟨Hs, Hheld, #Hkt⟩, Hp, Hcont⟩
  ihave Hk := AxSymMem3.wpNextSelf k.sie k.proc c _ $$ Hcont
  iapply L $$ Hs Hp %Hi.1
  iapply wpNext_intro
  iintro %_ Hs' Hp'
  iapply Hk $$ [Hs' Hheld] Hp'
  isplitl [Hs']
  · iexact Hs'
  · isplitl [Hheld]
    · iexact Hheld
    · iexact Hkt

/- the logically-TAKEN half of the Lean branch slot (deviation 1; no Rocq counterpart) -/
variable (wBrTaken : ∀ (c : CPU) (k : KCtx) (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 13)
    (rs1 rs2 : BitVec 5) (_hrs1 : rs1 ≠ 0#5) (op : bop),
  bcond op (k.rget c rs1) (k.rget c rs2) = true →
  instrW5 σi T satp0 Ex Dead pc is_rvc (instruction.BTYPE (imm, regidx.Regidx rs2, regidx.Regidx rs1, op)) ∗
    AxRelease4.kctxW4 γm γn stackOwn held kt c k ∗ pcW4 γp c pc ∗
    wpNext k.sie k.proc c (fun cpu' =>
      iprop(AxRelease4.kctxW4 γm γn stackOwn held kt cpu' k -∗
        pcW4 γp cpu' (if bcond op (k.rget cpu' rs1) (k.rget cpu' rs2) then pc + BitVec.signExtend 64 imm
          else pc + instrLen is_rvc) -∗ goalW4 i cid cpu γm γp γn T satp0 Ex Cond cpu'))
    ⊢ goalW4 i cid cpu γm γp γn T satp0 Ex Cond c)

include hmode hasid hppn Htext Hflow HG Hdead wBrTaken in
/-- (Lean-only) The `wp_s_branch` slot: REAL on the logically-falling half (`wpBrFallC5`, Rocq
`w_cbeqz5`'s content, any op / width / operands), the logically-taken half `wBrTaken`. -/
theorem AxSpinCtl3.wBranchSlot (c : CPU) (k : KCtx) (pc : BitVec 64) (is_rvc : Bool)
    (imm : BitVec 13) (rs1 rs2 : BitVec 5) (hrs1 : rs1 ≠ 0#5) (op : bop) :
    instrW5 σi T satp0 Ex Dead pc is_rvc (instruction.BTYPE (imm, regidx.Regidx rs2, regidx.Regidx rs1, op)) ∗
      AxRelease4.kctxW4 γm γn stackOwn held kt c k ∗ pcW4 γp c pc ∗
      wpNext k.sie k.proc c (fun cpu' =>
        iprop(AxRelease4.kctxW4 γm γn stackOwn held kt cpu' k -∗
          pcW4 γp cpu' (if bcond op (k.rget cpu' rs1) (k.rget cpu' rs2) then pc + BitVec.signExtend 64 imm
            else pc + instrLen is_rvc) -∗ goalW4 i cid cpu γm γp γn T satp0 Ex Cond cpu'))
      ⊢ goalW4 i cid cpu γm γp γn T satp0 Ex Cond c := by
  cases hb : bcond op (k.rget c rs1) (k.rget c rs2)
  · unfold instrW5 instr5 AxRelease4.kctxW4 capW4 pcW4 goalW4
    simp only [isCtl, ↓reduceIte]
    iintro ⟨⟨%Hi, %_⟩, ⟨Hs, Hheld, #Hkt⟩, Hp, Hcont⟩
    obtain ⟨⟨_, ⟨_, _, _, _, _, hn1, hn2⟩⟩, _⟩ := id Hi
    have h1 : rs1 ≠ 4#5 := fun h => hn1 (by rw [h])
    have h2 : rs2 ≠ 4#5 := fun h => hn2 (by rw [h])
    have Hf : AxSymCtl2.bcond op (AxSpinCtl2.lv cid k.regs rs1) (AxSpinCtl2.lv cid k.regs rs2) =
        false := by
      rw [AxSpinCtl3.lvRget, AxSpinCtl3.lvRget, AxSpinCtl3.bcondEq,
        AxCondM4.rgetCpu cid c _ _ h1, AxCondM4.rgetCpu cid c _ _ h2]
      exact hb
    have L := wpBrFallC5 i cid cpu γm γp γn σi T satp0 hmode hasid hppn armedR Ex stackOwn Cond
      Htext Hflow G HG Dead Hdead pc is_rvc imm rs2 rs1 op k.regs k.avail k.sie k.proc Hf
    rw [AxSpinCtl3.addIntIncr] at L
    unfold cap4 at L
    unfold cap4
    ihave Hk := AxSymMem3.wpNextSelf k.sie k.proc c _ $$ Hcont
    iapply L $$ Hs Hp %Hi
    iapply wpNext_intro
    iintro %_ Hs' Hp'
    iapply Hk $$ [Hs' Hheld] [Hp']
    · isplitl [Hs']
      · iexact Hs'
      · isplitl [Hheld]
        · iexact Hheld
        · iexact Hkt
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      iexact Hp'
  · exact wBrTaken c k pc is_rvc imm rs1 rs2 hrs1 op hb

/- Rocq's `stack_own_slots` and `w_cret` (λ-bound), the latter at `instrW5` -/
variable (stackOwnSlots : ∀ (sp : PAddr) (n : Nat), stackOwn sp n ⊣⊢
  [∗list] j ∈ List.range' 1 n, ∃ w : BitVec 64, wpt (paStk sp j) (DFrac.own 1) w)
variable (wCret5 : ∀ (c0 : CPU) (p pc : BitVec 64) (ra : BitVec 5) (m : RegMap) (n : Nat) (b : Bool),
  ra.toNat ≠ 0 →
  ⊢ capW4 γm γn stackOwn c0 m n b p -∗ pcW4 γp c0 pc -∗
    instrW5 σi T satp0 Ex Dead pc true (.JALR (0#12, .Regidx ra, zreg)) -∗
    wpNext b p c0 (fun c1 => iprop(
      capW4 γm γn stackOwn c1 m n b p -∗ pcW4 γp c1 (jumpPc (rget c0 m ra)) -∗
      goalW4 i cid cpu γm γp γn T satp0 Ex Cond c1)) -∗
    goalW4 i cid cpu γm γp γn T satp0 Ex Cond c0)

include hmode hasid hppn Htext Hflow Hloc HG Hdmap SFPop ldRule CondAnd HnoRmwReg stackOwnSlots
  wCret5 in
/-- (Lean-only, deviation 1) The `wp_epilogue4s1_gen` slot at `instrW5`: AxRelease4's
`wEpilogue4` (c.ldsp ×3, c.addi16sp REAL) with the c.ret the λ-bound `wCret5`. -/
theorem AxSpinCtl3.wEpilogue5 (c : CPU) (k : KCtx) (pc : BitVec 64) (hK : 4 ≤ k.avail)
    (R : RegMap) (hR2 : R 2#5 = k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64) (ra s0 s1 : BitVec 64) :
    instrW5 σi T satp0 Ex Dead pc true (instruction.LOAD (24#12, regidx.Regidx 2#5, regidx.Regidx 1#5, false, 8)) ∗
    instrW5 σi T satp0 Ex Dead (pc + 2#64) true (instruction.LOAD (16#12, regidx.Regidx 2#5, regidx.Regidx 8#5, false, 8)) ∗
    instrW5 σi T satp0 Ex Dead (pc + 4#64) true (instruction.LOAD (8#12, regidx.Regidx 2#5, regidx.Regidx 9#5, false, 8)) ∗
    instrW5 σi T satp0 Ex Dead (pc + 6#64) true (instruction.ITYPE (32#12, regidx.Regidx 2#5, regidx.Regidx 2#5, iop.ADDI)) ∗
    instrW5 σi T satp0 Ex Dead (pc + 8#64) true (instruction.JALR (0#12, regidx.Regidx 1#5, regidx.Regidx 0#5)) ∗
    AxRelease4.kctxW4 γm γn stackOwn held kt c ((k.pushed 4).withRegs R) ∗ pcW4 γp c pc ∗
    AxRelease4.frameW4 wpt (k.regs 2#5) ra s0 s1 ∗
    wpNext k.sie k.proc c (fun cpu' =>
        iprop(AxRelease4.kctxW4 γm γn stackOwn held kt cpu'
            (k.withRegs ((((R.set 1#5 ra).set 8#5 s0).set 9#5 s1).set 2#5 (k.regs 2#5))) -∗
          pcW4 γp cpu' (jumpPc ra) -∗ goalW4 i cid cpu γm γp γn T satp0 Ex Cond cpu'))
    ⊢ goalW4 i cid cpu γm γp γn T satp0 Ex Cond c := by
  rw [AxSpinCtl3.instrW5Off σi T satp0 Ex Dead pc true
      (instruction.LOAD (24#12, regidx.Regidx 2#5, regidx.Regidx 1#5, false, 8)) rfl,
    AxSpinCtl3.instrW5Off σi T satp0 Ex Dead (pc + 2#64) true
      (instruction.LOAD (16#12, regidx.Regidx 2#5, regidx.Regidx 8#5, false, 8)) rfl,
    AxSpinCtl3.instrW5Off σi T satp0 Ex Dead (pc + 4#64) true
      (instruction.LOAD (8#12, regidx.Regidx 2#5, regidx.Regidx 9#5, false, 8)) rfl,
    AxSpinCtl3.instrW5Off σi T satp0 Ex Dead (pc + 6#64) true
      (instruction.ITYPE (32#12, regidx.Regidx 2#5, regidx.Regidx 2#5, iop.ADDI)) rfl]
  have e4 : pc + 2#64 + 2#64 = pc + 4#64 := by bv_decide
  have e6 : pc + 2#64 + 2#64 + 2#64 = pc + 6#64 := by bv_decide
  have e8 : pc + 2#64 + 2#64 + 2#64 + 2#64 = pc + 8#64 := by bv_decide
  rw [← e4, ← e6, ← e8]
  have ha : ∀ (m : RegMap) (u : BitVec 6) (j : Nat), m 2#5 = R 2#5 →
      0xFFFFFFFFFFFFFFE0#64 + zero_extend (m := 64) (u +++ 0b000#3) = -(8#64 * BitVec.ofNat 64 j) →
      m 2#5 + zero_extend (m := 64) (u +++ 0b000#3) = paStk (k.regs 2#5) j := by
    intro m u j hm h; rw [hm, hR2, AxRelease4.paStkAdd, BitVec.add_assoc, h]
  have ze24 : zero_extend (m := 12) ((3#6 : BitVec 6) +++ 0b000#3) = 24#12 := by decide
  have ze16 : zero_extend (m := 12) ((2#6 : BitVec 6) +++ 0b000#3) = 16#12 := by decide
  have ze8 : zero_extend (m := 12) ((1#6 : BitVec 6) +++ 0b000#3) = 8#12 := by decide
  have h1 : (R.set 1#5 ra) 2#5 = R 2#5 := RegMap.set_other _ _ _ _ (by decide)
  have h8 : ((R.set 1#5 ra).set 8#5 s0) 2#5 = R 2#5 := by
    rw [RegMap.set_other _ _ _ _ (by decide)]; exact h1
  have h9 : (((R.set 1#5 ra).set 8#5 s0).set 9#5 s1) 2#5 = R 2#5 := by
    rw [RegMap.set_other _ _ _ _ (by decide)]; exact h8
  unfold AxRelease4.kctxW4 AxRelease4.frameW4
  simp only [KCtx.withRegs_regs, KCtx.withRegs_avail, KCtx.withRegs_sie, KCtx.withRegs_proc,
    KCtx.withRegs_locks, KCtx.pushed_avail, KCtx.pushed_sie, KCtx.pushed_proc, KCtx.pushed_locks]
  iintro ⟨Hi0, Hi2, Hi4, Hi6, Hi8, ⟨Hc, Hheld, #Hkt⟩, Hp, ⟨Hw1, Hw2, Hw3, Hw4⟩, Hcont⟩
  icases AxRelease4.capW4Sie γm γn stackOwn c _ _ _ _ $$ Hc with ⟨%hsie, Hc⟩
  ihave Hk := AxSymMem3.wpNextSelf k.sie k.proc c _ $$ Hcont
  -- c.ldsp ra,24(sp)
  have L1 := AxRelease4.wCldspAt i cid cpu γm γp γn σi T satp0 hmode hasid hppn Ex Cond Htext
    Hflow Hloc G HG dreg damo Hdmap stackOwn wpt ldRule CondAnd HnoRmwReg c k.proc pc 3#6 1#5
    R (k.avail - 4) ra k.sie (.own 1) (paStk (k.regs 2#5) 1) (ha R 3#6 1 rfl (by decide))
    (by decide) (by decide)
  rw [ze24, AxRelease4.spEq] at L1
  iapply L1 $$ Hc Hp Hi0 Hw1
  iapply wpNext_intro_pin
  iintro %c1 %hc1
  rw [hc1 (Or.inl hsie)]
  iintro Hc Hp Hw1
  -- c.ldsp s0,16(sp)
  have L2 := AxRelease4.wCldspAt i cid cpu γm γp γn σi T satp0 hmode hasid hppn Ex Cond Htext
    Hflow Hloc G HG dreg damo Hdmap stackOwn wpt ldRule CondAnd HnoRmwReg c k.proc (pc + 2#64)
    2#6 8#5 (R.set 1#5 ra) (k.avail - 4) s0 k.sie (.own 1) (paStk (k.regs 2#5) 2)
    (ha _ 2#6 2 h1 (by decide)) (by decide) (by decide)
  rw [ze16, AxRelease4.spEq] at L2
  iapply L2 $$ Hc Hp Hi2 Hw2
  iapply wpNext_intro_pin
  iintro %c2 %hc2
  rw [hc2 (Or.inl hsie)]
  iintro Hc Hp Hw2
  -- c.ldsp s1,8(sp)
  have L3 := AxRelease4.wCldspAt i cid cpu γm γp γn σi T satp0 hmode hasid hppn Ex Cond Htext
    Hflow Hloc G HG dreg damo Hdmap stackOwn wpt ldRule CondAnd HnoRmwReg c k.proc
    (pc + 2#64 + 2#64) 1#6 9#5 ((R.set 1#5 ra).set 8#5 s0) (k.avail - 4) s1 k.sie (.own 1)
    (paStk (k.regs 2#5) 3) (ha _ 1#6 3 h8 (by decide)) (by decide) (by decide)
  rw [ze8, AxRelease4.spEq] at L3
  iapply L3 $$ Hc Hp Hi4 Hw3
  iapply wpNext_intro_pin
  iintro %c3 %hc3
  rw [hc3 (Or.inl hsie)]
  iintro Hc Hp Hw3
  -- c.addi16sp sp,32
  have hc16 : caddi16spImm 2#6 = 32#12 := by decide
  have L4 := AxRelease4.wC16At i cid cpu γm γp γn σi T satp0 hmode hasid hppn Ex Cond Htext Hflow
    stackOwn SFPop c k.proc (pc + 2#64 + 2#64 + 2#64) 2#6 (((R.set 1#5 ra).set 8#5 s0).set 9#5 s1)
    (k.avail - 4) 4 k.sie (k.regs 2#5) k.avail
    (by rw [h9, hR2, hc16, BitVec.add_assoc,
      show (0xFFFFFFFFFFFFFFE0#64 : BitVec 64) + sign_extend (m := 64) (32#12 : BitVec 12) = 0#64
        from by decide, BitVec.add_zero])
    (Nat.sub_add_cancel hK)
    (by rw [h9, hR2, AxRelease4.paStkAdd]; exact congrArg (k.regs 2#5 + ·) (by decide))
  rw [hc16, AxRelease4.spEq] at L4
  iapply L4 $$ Hc Hp Hi6 [Hw1 Hw2 Hw3 Hw4]
  · iapply (stackOwnSlots (k.regs 2#5) 4).2
    iapply (AxRelease4.slots4 _).2
    isplitl [Hw1]
    · iexists ra
      iexact Hw1
    · isplitl [Hw2]
      · iexists s0
        iexact Hw2
      · isplitl [Hw3]
        · iexists s1
          iexact Hw3
        · isplitl [Hw4]
          · iexact Hw4
          · iempintro
  iapply wpNext_intro_pin
  iintro %c4 %hc4
  rw [hc4 (Or.inl hsie)]
  iintro Hc Hp
  -- c.ret (λ-bound, at `instrW5`)
  have hra : rget c ((((R.set 1#5 ra).set 8#5 s0).set 9#5 s1).set 2#5 (k.regs 2#5)) 1#5 = ra := by
    rw [rget_ne c _ 1#5 (by decide) (by decide), RegMap.set_other _ _ _ _ (by decide),
      RegMap.set_other _ _ _ _ (by decide), RegMap.set_other _ _ _ _ (by decide), RegMap.set_same]
  have L5 := wCret5 c k.proc (pc + 2#64 + 2#64 + 2#64 + 2#64) 1#5
    ((((R.set 1#5 ra).set 8#5 s0).set 9#5 s1).set 2#5 (k.regs 2#5)) k.avail k.sie (by decide)
  rw [hra, AxRelease4.zregEq] at L5
  iapply L5 $$ Hc Hp Hi8
  iapply wpNext_intro_pin
  iintro %c5 %hc5
  rw [hc5 (Or.inl hsie)]
  iintro Hc Hp
  iapply Hk $$ [Hc Hheld] Hp
  isplitl [Hc]
  · iexact Hc
  · isplitl [Hheld]
    · iexact Hheld
    · iexact Hkt

include hmode hasid hppn Htext Hflow Hloc HG Hdmap SFPush SFPop stRule ldRule CondAnd HnoRmwReg
  hlo sdlkRule swlkRule stackOwnSlots wCret5 Hdead wBrTaken in
/-- **THE REPLAY with the control slots jal / c.beqz REAL** (Rocq `release_wpd5`): AxLeafS5's
`wpReleaseGen` at `goalW4` / `kctxW4` / `pcW4` / `instrW5`, the nine slots of `releaseWpd4`
passed unchanged, `wp_s_jal` := `AxSpinCtl3.wJalSlot`, `wp_s_branch` :=
`AxSpinCtl3.wBranchSlot` (its logically-taken half `wBrTaken` λ-bound, deviation 1), the
epilogue `AxSpinCtl3.wEpilogue5` (c.ret = the λ-bound `wCret5`); NO `Cond_gate`. -/
theorem releaseWpd5 :
    type_of% (AxLeafS5.wpReleaseGen (GF := GF) (Pay := Pay)
      (Goal := goalW4 i cid cpu γm γp γn T satp0 Ex Cond)
      (kctx := AxRelease4.kctxW4 γm γn stackOwn held kt) (pcIs := pcW4 γp)
      (instr := instrW5 σi T satp0 Ex Dead)
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
        (stackOwnSlots := stackOwnSlots) (wCret5 := wCret5))
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
      (wp_s_sd_zero_lkcpu_release_gen := wSdlk4 (i := i) (cid := cid) (cpu := cpu) (γm := γm)
        (γp := γp) (γn := γn) (σi := σi) (T := T) (satp0 := satp0) (hmode := hmode)
        (hasid := hasid) (hppn := hppn) (Ex := Ex) (Cond := Cond) (Htext := Htext) (Hflow := Hflow)
        (Hloc := Hloc) (G := G) (HG := HG) (dreg := dreg) (damo := damo) (Hdmap := Hdmap)
        (stackOwn := stackOwn) (lockOpenable := lockOpenable) (lockedCore := lockedCore)
        (lockedPre := lockedPre) (held := held) (sdlkRule := sdlkRule) (kt := kt))
      (wp_s_sw_zero_release_gen := wSwfin4 (i := i) (cid := cid) (cpu := cpu) (γm := γm)
        (γp := γp) (γn := γn) (σi := σi) (T := T) (satp0 := satp0) (hmode := hmode)
        (hasid := hasid) (hppn := hppn) (Ex := Ex) (Cond := Cond) (Htext := Htext) (Hflow := Hflow)
        (Hloc := Hloc) (G := G) (HG := HG) (dreg := dreg) (damo := damo) (Hdmap := Hdmap)
        (stackOwn := stackOwn) (payAt := payAt) (payOk := payOk) (lockOpenable := lockOpenable)
        (lockedPre := lockedPre) (lockCtxHeld := lockCtxHeld) (held := held)
        (swlkRule := swlkRule) (kt := kt))) :=
  AxLeafS5.wpReleaseGen (GF := GF) (Pay := Pay)
    (Goal := goalW4 i cid cpu γm γp γn T satp0 Ex Cond)
    (kctx := AxRelease4.kctxW4 γm γn stackOwn held kt) (pcIs := pcW4 γp)
    (instr := instrW5 σi T satp0 Ex Dead)
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
      (stackOwnSlots := stackOwnSlots) (wCret5 := wCret5))
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
    (wp_s_sd_zero_lkcpu_release_gen := wSdlk4 (i := i) (cid := cid) (cpu := cpu) (γm := γm)
      (γp := γp) (γn := γn) (σi := σi) (T := T) (satp0 := satp0) (hmode := hmode)
      (hasid := hasid) (hppn := hppn) (Ex := Ex) (Cond := Cond) (Htext := Htext) (Hflow := Hflow)
      (Hloc := Hloc) (G := G) (HG := HG) (dreg := dreg) (damo := damo) (Hdmap := Hdmap)
      (stackOwn := stackOwn) (lockOpenable := lockOpenable) (lockedCore := lockedCore)
      (lockedPre := lockedPre) (held := held) (sdlkRule := sdlkRule) (kt := kt))
    (wp_s_sw_zero_release_gen := wSwfin4 (i := i) (cid := cid) (cpu := cpu) (γm := γm)
      (γp := γp) (γn := γn) (σi := σi) (T := T) (satp0 := satp0) (hmode := hmode)
      (hasid := hasid) (hppn := hppn) (Ex := Ex) (Cond := Cond) (Htext := Htext) (Hflow := Hflow)
      (Hloc := Hloc) (G := G) (HG := HG) (dreg := dreg) (damo := damo) (Hdmap := Hdmap)
      (stackOwn := stackOwn) (payAt := payAt) (payOk := payOk) (lockOpenable := lockOpenable)
      (lockedPre := lockedPre) (lockCtxHeld := lockCtxHeld) (held := held)
      (swlkRule := swlkRule) (kt := kt))

end WPdRelease5

end Weak
