/-
Weak: **REPLAY of xv6's `release` proof text over an ABSTRACT leaf interface** (the
AxReuseProbe method, as for `cpuid`), and its instantiation with the WPd leaves of `AxLeafS4`.

Rocq: `iris/AxLeafS5.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 `AbsRelease`: the EXACT interface the proof text of `ProofRelease.wp_release_gen_sconf` relies
on, as section parameters: the goal `Goal` (hart-indexed, standing for `WP Loop`); the resources
(`sie_cap_gpr`, `pc_is`, `instr`, `kernel_text` (persistent), `stack_own`, `word_pointsto`, the
lock resources `locked` / `locked_pre` / `lock_openable` (persistent) / `lock_finisher`,
`cpu_own` / `arm_pay`); the 12 leaf statements it applies (copied, `WP Loop` := `Goal`); the two
CALLEE specs (holding, pop_off: their spec bodies with the same substitution); the stack and
cpu-ownership lemmas; the text lemmas `rli_*`.  `wp_next` and every pure fact are the REAL ones.
The release body is restated with the same substitution and the proof is PASTED from
ProofRelease.v (only the callee names lose their module prefix).  §2 `release_faithful`:
instantiating the interface with the real SC resources and leaves gives back the real body.
§3 instantiation at the WPd surface (`AxLeafS4`): `Goal` := `Goal2` (ambient hart), `sie_cap_gpr`
:= `sie_cap2`, `pc_is` := `pc_is2`, `instr` := `instr2`, the `fence rw,w` slot filled by the REAL
WPd leaf `AxLeafS4.wp_fence_c`; every other slot stays λ-bound (premised).

## Deviations from Rocq

1. THE PROOF TEXT IS THE LEAN TREE'S (owner ruling Q17, as `AxReuseProbe` / `AxSymMem3`
   deviation 5).  The Lean tree has no `wp_release_gen_sconf` (Rocq's text over `sie_cap_gpr` /
   `cpu_own` / `lock_finisher`); its counterpart is `Xv6.release_gen_proof : RELEASE_GEN`
   (`Xv6/ProofRelease.lean`: `lockOpenable γ lk s R D`, the credential `Tc` refuting the dead
   branch `D`), a different text over a different leaf layer: one `kctx cpu k` context resource
   (registers, interrupt bit, stack budget, held locks, the kernel image) in place of
   `sie_cap_gpr` / `kernel_text`, the frame macros `wp_prologue4s1` / `wp_epilogue4s1_gen` with
   a `frame4s1` resource between them (in place of the push / three c.sdsp / c.addi4spn and the
   three c.ldsp / pop / c.ret leaves with `stack_own` / `word_pointsto` / `stack_own_slots`), the
   generic leaves `wp_s_add` (c.mv), `wp_s_jal` (both calls), `wp_s_branch` (c.beqz), the lock
   leaves `wp_s_sd_zero_lkcpu_release_gen` / `wp_s_sw_zero_release_gen` (in place of
   `wp_sd_zero_lkcpu_lockopen_s_sconf` / `wp_sw_zero_lockfin_s_sconf`; no `lock_finisher` /
   `Out`: the Lean word clear deposits the payload `R curCtx` itself), `locked_cases` (the held
   token splits into `lockedCore` ∗ `lockCtxHeld`), the arm `popArm` (Rocq `cpu_own` / `arm_pay`
   and `cpu_own_transport`: the Lean `pop_off` spec carries the interrupt state in `kctx`), and
   instruction facts from the kernel text by `text_instr` (no `rli_*` catalogue).  So §1
   abstracts THAT interface (section `AbsRelease`): `Goal : CPU → IProp GF` (for `wpLoop`),
   `kctx`, `pcIs`, `instr`, `kernelText` (persistent), `frame4` (for `frame4s1`); the lock
   resources `lockOpenable` (persistent) / `locked` / `lockedCore` / `lockedPre` / `lockCtxHeld`;
   the payload type `Pay` with `payAt` (for `R curCtx`) and `payOk` (for `CtxMorph R`, a class
   that needs `MachGS`); `armP cpu reen p` (for `popArm cpu k reen`, which depends on `k` only
   through `k.proc`); the leaf statements with their tree names, `wpLoop` := `Goal`; the text
   lemma as `textInstr` (AxReuseProbe finding (2): `k_code`'s fast path is keyed on the literal
   `text_instr`).  `wpNext`, `KCtx` and everything pure are the REAL ones.  Persistence of
   `kernelText` / `lockOpenable` is an explicit binder (`hkt`, `hlo`; a local instance in the
   proof), so that §3 can leave them λ-bound.
2. EDITS to the pasted text of `release_gen_proof` (beyond `wpLoop` := `Goal`):
   `text_instr` ↦ `textInstr`; `HO.wp_holding_locked_gen (hlc := hlc) (GF := GF)` /
   `PO.wp_pop_off (hlc := hlc) (GF := GF)` ↦ the slots `wp_holding_locked_gen` / `wp_pop_off`,
   unfolding `holdBody` / `popBody` (Rocq's "callee names lose their module prefix"); `popArm cpu
   k' reen` ↦ `armP cpu reen k'.proc` and the `unfold popArm` before `iframe Harm` is dropped
   (`k_norm` rewrites `k'.proc` to `k.proc`); the word-clear step passes `hR` (the `payOk R`
   evidence, Lean's instance argument `[CtxMorph R]`); the fence step drops the `0#5 0#5`
   arguments (deviation 3); and, the slots being later-free (deviation 3), `k_step` ↦
   `ax_leafs5_kstep` (the same expansion without `inext_goal`) and the two `inext`s after the
   frame macros are dropped.  mcslrec (2) [OWN.82] (a1): the word-clear slot takes the
   release-site premise `_hrel : pc = release+0x1a` and the text passes `rfl` (the tree's text
   takes the leaf's `pc ∈ MachFixedGS.relPcs` out of `kctx` by `Xv6.kctx_relPcsEq`; §2 does the
   same in `releaseFaithful`; the WPd instantiations fill the slot by `relLeafOfFree`).
3. THE SLOTS ARE LATER-FREE (Rocq's shape: the Rocq SC leaves have no later).  Every Lean SC
   leaf the text applies exposes a `▷` before its continuation (`wp_prologue4s1`'s `▷ (…)`, the
   others' `▷ wpNext …`); a WPd leaf cannot absorb it (`goal2` is a `wpd`, `▷ wpd ⊢ wpd` does not
   hold; the WPd leaves, e.g. `AxLeafS4.wpFenceC` over `AxCert4.XFenceM`, have no later before
   their continuation; cf. AxSymMem3's `XGprWriteL`).  So the slots are stated without it, which
   makes them WEAKER than the Lean leaves: §2 instantiates each from its Lean leaf by
   `later_intro`, and §3 (and the downstream instantiations AxCondM4 / AxRelease4 / AxSpinCtl3 /
   AxSpinRow3) can fill them with WPd leaves.  The fence slot is moreover stated at `rs = rd =
   x0` (Rocq's `wp_fence_s_sconf` shape, `FENCE (0, 3, 1, x0, x0)`; Lean's leaf is generic in
   `rs rd`).
4. §3 (Rocq `GoalW` / `capW` / `pcW` / `release_wpd`): `goalW _ := goal2 … cid …` (the ambient
   SC hart, as Rocq), `pcW _ := pcIs2 γp`, and `capW` ↦ `kctxW γm γn kt c k := sieCap2 γm γn c
   k.regs k.avail k.sie k.proc ∗ kt` (the Lean interface's `kctx`: `sie_cap2`'s mirror of
   `k`'s fields plus the kernel text `kt`, as `AxSymMem3.kctxC`).  REAL slots: the fence
   (`AxLeafS5.wpFenceW`, from `AxLeafS4.wpFenceC` at `m := k.regs`, `n := k.avail`, `b :=
   k.sie`, `p := k.proc`) and, Lean-only, `kctx_kernelText` (`AxLeafS5.kctxWKt`).  Every other
   slot and resource stays λ-bound: `releaseWpd` is stated by `type_of%` of the partial
   application (as Rocq's `Definition release_wpd := λ …`), the remaining slots being binders of
   its type.  Rocq's `GenId` / `CpuId` contexts have no counterpart (the hart is explicit).
5. KERNEL DRIFT (checked against `Xv6/KernelImage.lean`, `release` = 0x80000ce0): the 17 words the
   proof steps through (+0x00…+0x2a) have Rocq's layout and immediates (`jal holding` 2096902,
   `c.beqz` 14·2, `sd zero,16(s1)`, `fence rw,w`, `sw zero,0(s1)`, `jal pop_off` 2097050, …);
   the panic tail differs (Lean `addi a0,a0,876` at +0x30, Rocq 948; Lean `jal unreachable`
   0x80000860 at +0x34, Rocq `rli_34`'s 2095970) — neither text steps it (the branch is not
   taken), and the Lean text derives every fact from the image by `textInstr`.

**Rocq → Lean name map** (all under `Weak.AxLeafS5.`).  `AbsRelease` → section `AbsRelease`;
`hold_body` `holdBody`; `pop_body` `popBody`; `wp_release_gen_sconf_body` `wpReleaseGenBody`;
`wp_release_gen_sconf` `wpReleaseGen`; `release_faithful` `releaseFaithful`; `GoalW` `goalW`;
`capW` `kctxW` (deviation 4); `pcW` `pcW`; `release_wpd` `releaseWpd`.  Section parameters
(deviation 1): `Goal` `Goal`; `sie_cap_gpr` + `kernel_text` ↦ `kctx` + `kernelText`; `pc_is`
`pcIs`; `instr` `instr`; `stack_own` / `word_pointsto` / `stack_own_slots` ↦ `frame4`;
`lock_openable` `lockOpenable`; `locked` `locked`; `locked_pre` `lockedPre`; `lock_finisher` ↦
none; `cpu_own` / `arm_pay` / `cpu_own_transport` ↦ `armP`; the leaves ↦ `wp_prologue4s1`,
`wp_s_add`, `wp_s_jal`, `wp_s_branch`, `wp_s_sd_zero_lkcpu_release_gen`, `wp_s_fence_rw_w`,
`wp_s_sw_zero_release_gen`, `wp_epilogue4s1_gen`; `wp_holding_lockinv_locked_s_sconf`
`wp_holding_locked_gen`; `wp_pop_off_sconf` `wp_pop_off`; `rli_*` ↦ `textInstr`; new
`kctx_kernelText`, `kctx_wf`, `locked_cases`, `lockedCore`, `lockCtxHeld`, `Pay`/`payAt`/`payOk`.
None of the Rocq names is in `notes/weak-port-dupnames.json`.  Lean-only (file-qualified):
`AxLeafS5.wpFenceW`, `AxLeafS5.kctxWKt`, the tactic `ax_leafs5_kstep` (deviation 2).

Build: the whole file elaborates in ~3.6 s (VM).

**Dropped:** nothing (Rocq 9 definitions/lemmas, Lean 9 + 2 Lean-only).  **Not ported:** the
`Check` / `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxLeafS4
import Xv6.ProofRelease

namespace Weak

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D LeanRV64D.Functions
open Xv6 (releaseAddr holdingAddr popOffAddr textDecodeWith release_br_ffffffffffffffb8
  release_br_ffffffffffffff12)

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

namespace AxLeafS5

/-- `k_step rule from code HT $$ pat` for a slot WITHOUT a later before its continuation
(deviation 3): `MachCSL`'s `k_step` expansion without its `inext_goal` (iris-lean's `inext` fails
on a goal that is not a later). -/
syntax "ax_leafs5_kstep" term:max " from " term:max ident " $$ " specPat : tactic
syntax "ax_leafs5_kstep" term:max " from " term:max ident " $$ " specPat " with " "[" term,* "]" : tactic

set_option hygiene false in
macro_rules
  | `(tactic| ax_leafs5_kstep $rule:term from $code:term $ht:ident $$ $pat:specPat) =>
    `(tactic| ax_leafs5_kstep $rule:term from $code:term $ht:ident $$ $pat:specPat with [])
  | `(tactic| ax_leafs5_kstep $rule:term from $code:term $ht:ident $$ $pat:specPat with [$extra,*]) =>
    `(tactic| (k_iapply $rule:term $$ $pat:specPat
               rotate_right 1
               k_code $code:term $ht:ident
               iframe #
               k_norm_goal [hsie, $extra,*]
               iframe
               first
                 | k_next_off
                 | (k_norm [$extra,*]; iframe; k_next_off)
               try (case hs => k_norm)))

/-! ## 1. The abstract interface `AbsRelease` -/

section AbsRelease

variable {GF : BundledGFunctors}

-- the abstract logic surface
variable (Goal : CPU → IProp GF)
variable (kctx : CPU → KCtx → IProp GF)
variable (pcIs : CPU → BitVec 64 → IProp GF)
variable (instr : BitVec 64 → Bool → instruction → IProp GF)
variable (kernelText : IProp GF) (hkt : Persistent kernelText)
variable (frame4 : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → IProp GF)
variable {Pay : Type _} (payAt : Pay → IProp GF) (payOk : Pay → Prop)
variable (lockOpenable : GName → BitVec 64 → String → Pay → IProp GF → IProp GF)
  (hlo : ∀ γ lk s R D, Persistent (lockOpenable γ lk s R D))
variable (locked lockedCore lockedPre : GName → CPU → IProp GF) (lockCtxHeld : IProp GF)
variable (armP : CPU → Bool → BitVec 64 → IProp GF)

-- the leaf specs the proof applies (statements copied, `wpLoop` := `Goal`, no `▷` before the
-- continuations: deviation 3)
variable (kctx_kernelText : ∀ (cpu : CPU) (k : KCtx), kctx cpu k ⊢ kernelText ∗ kctx cpu k)
variable (kctx_wf : ∀ (cpu : CPU) (k : KCtx), kctx cpu k ⊢ ⌜k.wf⌝ ∗ kctx cpu k)
variable (textInstr : ∀ (pc : BitVec 64) (rvc : Bool) (i i₀ : instruction),
    textDecodeWith drefM pc = some (rvc, i, i₀) → textDecodeWith drefS pc = some (rvc, i, i₀) →
    kernelText ⊢ instr pc rvc i)
variable (locked_cases : ∀ (γ : GName) (c : CPU), locked γ c ⊢ lockedCore γ c ∗ lockCtxHeld)
variable (wp_prologue4s1 : ∀ (cpu : CPU) (k : KCtx) (_hsie : k.sie = false) (pc : BitVec 64)
    (_hK : 4 ≤ k.avail),
    instr pc true (instruction.ITYPE (4064#12, regidx.Regidx 2#5, regidx.Regidx 2#5, iop.ADDI)) ∗
    instr (pc + 2#64) true (instruction.STORE (24#12, regidx.Regidx 1#5, regidx.Regidx 2#5, 8)) ∗
    instr (pc + 4#64) true (instruction.STORE (16#12, regidx.Regidx 8#5, regidx.Regidx 2#5, 8)) ∗
    instr (pc + 6#64) true (instruction.STORE (8#12, regidx.Regidx 9#5, regidx.Regidx 2#5, 8)) ∗
    instr (pc + 8#64) true (instruction.ITYPE (32#12, regidx.Regidx 2#5, regidx.Regidx 8#5, iop.ADDI)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    (kctx cpu ((k.pushed 4).withRegs
          ((k.regs.set 2#5 (k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64)).set 8#5 (k.regs 2#5))) -∗
        pcIs cpu (pc + 10#64) -∗
        frame4 (k.regs 2#5) (k.regs 1#5) (k.regs 8#5) (k.regs 9#5) -∗ Goal cpu)
    ⊢ Goal cpu)
variable (wp_epilogue4s1_gen : ∀ (cpu : CPU) (k : KCtx) (pc : BitVec 64) (_hK : 4 ≤ k.avail)
    (R : RegMap) (_hR2 : R 2#5 = k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64) (ra s0 s1 : BitVec 64),
    instr pc true (instruction.LOAD (24#12, regidx.Regidx 2#5, regidx.Regidx 1#5, false, 8)) ∗
    instr (pc + 2#64) true (instruction.LOAD (16#12, regidx.Regidx 2#5, regidx.Regidx 8#5, false, 8)) ∗
    instr (pc + 4#64) true (instruction.LOAD (8#12, regidx.Regidx 2#5, regidx.Regidx 9#5, false, 8)) ∗
    instr (pc + 6#64) true (instruction.ITYPE (32#12, regidx.Regidx 2#5, regidx.Regidx 2#5, iop.ADDI)) ∗
    instr (pc + 8#64) true (instruction.JALR (0#12, regidx.Regidx 1#5, regidx.Regidx 0#5)) ∗
    kctx cpu ((k.pushed 4).withRegs R) ∗ pcIs cpu pc ∗ frame4 (k.regs 2#5) ra s0 s1 ∗
    wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.withRegs ((((R.set 1#5 ra).set 8#5 s0).set 9#5 s1).set 2#5 (k.regs 2#5))) -∗
          pcIs cpu' (jumpPc ra) -∗ Goal cpu'))
    ⊢ Goal cpu)
variable (wp_s_add : ∀ (cpu : CPU) (k : KCtx) (pc : BitVec 64) (is_rvc : Bool) (rd rs1 rs2 : BitVec 5)
    (_hrd : MachCSL.rdOk rd),
    instr pc is_rvc (instruction.RTYPE (regidx.Regidx rs2, regidx.Regidx rs1, regidx.Regidx rd, rop.ADD)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.setReg rd (k.rget cpu' rs1 + k.rget cpu' rs2)) -∗
        pcIs cpu' (pc + instrLen is_rvc) -∗ Goal cpu'))
    ⊢ Goal cpu)
variable (wp_s_jal : ∀ (cpu : CPU) (k : KCtx) (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 21)
    (rd : BitVec 5) (_hrd : MachCSL.rdOk rd),
    instr pc is_rvc (instruction.JAL (imm, regidx.Regidx rd)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.setReg rd (pc + instrLen is_rvc)) -∗
          pcIs cpu' (pc + BitVec.signExtend 64 imm) -∗ Goal cpu'))
    ⊢ Goal cpu)
variable (wp_s_branch : ∀ (cpu : CPU) (k : KCtx) (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 13)
    (rs1 rs2 : BitVec 5) (_hrs1 : rs1 ≠ 0#5) (op : bop),
    instr pc is_rvc (instruction.BTYPE (imm, regidx.Regidx rs2, regidx.Regidx rs1, op)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' k -∗
          pcIs cpu' (if bcond op (k.rget cpu' rs1) (k.rget cpu' rs2) then pc + BitVec.signExtend 64 imm
            else pc + instrLen is_rvc) -∗ Goal cpu'))
    ⊢ Goal cpu)
/- the fence slot at Rocq's `rs = rd = x0` (deviation 3) -/
variable (wp_s_fence_rw_w : ∀ (cpu : CPU) (k : KCtx) (pc : BitVec 64) (is_rvc : Bool),
    instr pc is_rvc (instruction.FENCE (0#4, 3#4, 1#4, regidx.Regidx 0#5, regidx.Regidx 0#5)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' k -∗ pcIs cpu' (pc + instrLen is_rvc) -∗ Goal cpu'))
    ⊢ Goal cpu)
variable (wp_s_sd_zero_lkcpu_release_gen : ∀ (cpu : CPU) (k : KCtx) (_hsie : k.sie = false)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (rs1 : BitVec 5)
    (γ : GName) (lk : BitVec 64) (s : String) (R : Pay)
    (D : IProp GF) [Timeless D] (Tc : IProp GF) (_hrefute : ⊢ Tc -∗ D -∗ (False : IProp GF))
    (_haddr : k.rget cpu rs1 + BitVec.signExtend 64 imm = lk + 16#64),
    instr pc is_rvc (instruction.STORE (imm, regidx.Regidx 0#5, regidx.Regidx rs1, 8)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗ lockOpenable γ lk s R D ∗ Tc ∗ lockedCore γ cpu ∗
    wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' k -∗ pcIs cpu' (pc + instrLen is_rvc) -∗ (lockedPre γ cpu ∗ Tc) -∗ Goal cpu'))
    ⊢ Goal cpu)
variable (wp_s_sw_zero_release_gen : ∀ (cpu : CPU) (k : KCtx) (_hsie : k.sie = false)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (rs1 : BitVec 5)
    (γ : GName) (lk : BitVec 64) (s : String) (R : Pay) (_hR : payOk R)
    (D : IProp GF) [Timeless D] (Tc : IProp GF) (_hrefute : ⊢ Tc -∗ D -∗ (False : IProp GF))
    (_haddr : k.rget cpu rs1 + BitVec.signExtend 64 imm = lk) (_hrel : pc = KA.«release» + 0x1a#64),
    instr pc is_rvc (instruction.STORE (imm, regidx.Regidx 0#5, regidx.Regidx rs1, 4)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗ lockOpenable γ lk s R D ∗ Tc ∗ lockedPre γ cpu ∗ lockCtxHeld ∗
    payAt R ∗
    wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.withLocks (k.locks.filter (fun x => x ≠ s))) -∗
          pcIs cpu' (pc + instrLen is_rvc) -∗ ⌜s ∈ k.locks⌝ -∗ Tc -∗ Goal cpu'))
    ⊢ Goal cpu)

/-- (Lean-only, mcslrec (2) [OWN.82]) A release-store slot stated WITHOUT the release-site
premise `_hrel` fills the slot (the premise dropped): what the WPd instantiations (AxCondM4 /
AxRelease4 / AxSpinCtl3 / AxSpinRow3), whose leaves do not need it, pass. -/
theorem relLeafOfFree {Goal : CPU → IProp GF} {kctx : CPU → KCtx → IProp GF}
    {pcIs : CPU → BitVec 64 → IProp GF} {instr : BitVec 64 → Bool → instruction → IProp GF}
    {payAt : Pay → IProp GF} {payOk : Pay → Prop}
    {lockOpenable : GName → BitVec 64 → String → Pay → IProp GF → IProp GF}
    {lockedPre : GName → CPU → IProp GF} {lockCtxHeld : IProp GF}
    (h : ∀ (cpu : CPU) (k : KCtx) (_hsie : k.sie = false)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (rs1 : BitVec 5)
    (γ : GName) (lk : BitVec 64) (s : String) (R : Pay) (_hR : payOk R)
    (D : IProp GF) [Timeless D] (Tc : IProp GF) (_hrefute : ⊢ Tc -∗ D -∗ (False : IProp GF))
    (_haddr : k.rget cpu rs1 + BitVec.signExtend 64 imm = lk),
    instr pc is_rvc (instruction.STORE (imm, regidx.Regidx 0#5, regidx.Regidx rs1, 4)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗ lockOpenable γ lk s R D ∗ Tc ∗ lockedPre γ cpu ∗ lockCtxHeld ∗
    payAt R ∗
    wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.withLocks (k.locks.filter (fun x => x ≠ s))) -∗
          pcIs cpu' (pc + instrLen is_rvc) -∗ ⌜s ∈ k.locks⌝ -∗ Tc -∗ Goal cpu'))
    ⊢ Goal cpu) :
    ∀ (cpu : CPU) (k : KCtx) (_hsie : k.sie = false)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (rs1 : BitVec 5)
    (γ : GName) (lk : BitVec 64) (s : String) (R : Pay) (_hR : payOk R)
    (D : IProp GF) [Timeless D] (Tc : IProp GF) (_hrefute : ⊢ Tc -∗ D -∗ (False : IProp GF))
    (_haddr : k.rget cpu rs1 + BitVec.signExtend 64 imm = lk) (_hrel : pc = KA.«release» + 0x1a#64),
    instr pc is_rvc (instruction.STORE (imm, regidx.Regidx 0#5, regidx.Regidx rs1, 4)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗ lockOpenable γ lk s R D ∗ Tc ∗ lockedPre γ cpu ∗ lockCtxHeld ∗
    payAt R ∗
    wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.withLocks (k.locks.filter (fun x => x ≠ s))) -∗
          pcIs cpu' (pc + instrLen is_rvc) -∗ ⌜s ∈ k.locks⌝ -∗ Tc -∗ Goal cpu'))
    ⊢ Goal cpu :=
  fun cpu k hsie pc is_rvc imm rs1 γ lk s R hR D _ Tc hrefute haddr _ =>
    h cpu k hsie pc is_rvc imm rs1 γ lk s R hR D Tc hrefute haddr

/-- The callee `holding` (Rocq `hold_body`): `Xv6.wp_holding_locked_gen_body` with `wpLoop` :=
`Goal`, resources abstract. -/
def holdBody (cpu : CPU) (k : KCtx) (γ : GName) (s : String) (R : Pay)
    (D : IProp GF) [Timeless D] (Tc : IProp GF) (_hrefute : ⊢ Tc -∗ D -∗ (False : IProp GF))
    (_hsie : k.sie = false) (_hK : 6 ≤ k.avail) : Prop :=
  kctx cpu k ∗ pcIs cpu holdingAddr ∗ lockOpenable γ (k.regs 10#5) s R D ∗ Tc ∗
  locked γ cpu ∗
  (∀ R' : RegMap, kctx cpu (k.withRegs R') -∗ pcIs cpu (jumpPc (k.regs 1#5)) -∗
    ⌜calleeSaved k.regs R' ∧ R' 10#5 = 1#64⌝ -∗ locked γ cpu -∗ Tc -∗ Goal cpu)
  ⊢ Goal cpu

/-- The callee `pop_off` (Rocq `pop_body`): `Xv6.wp_pop_off_body` with `wpLoop` := `Goal`, the
arm `popArm cpu k reen` := `armP cpu reen k.proc`. -/
def popBody (cpu : CPU) (k : KCtx) (_hsie : k.sie = false)
    (_hnoff : 1 ≤ k.noff) (_hK : 4 ≤ k.avail) (_hlks : k.locks.length ≤ k.noff - 1)
    (reen : Bool) (_hreen : reen = (decide (k.noff = 1) && k.intena))
    (_hon : reen = true → k.tier = .kpt ∧ trapRes true + 2 ≤ k.avail) : Prop :=
  kctx cpu k ∗ pcIs cpu popOffAddr ∗ armP cpu reen k.proc ∗
  wpNext (k.popExit reen).sie k.proc cpu (fun cpu' => iprop(∀ R' : RegMap,
    kctx cpu' ((k.popExit reen).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    ⌜calleeSaved k.regs R'⌝ -∗ Goal cpu'))
  ⊢ Goal cpu

-- the callee specs (SpecHolding / SpecPopoff bodies)
variable (wp_holding_locked_gen : ∀ (cpu : CPU) (k : KCtx) (γ : GName) (s : String) (R : Pay)
    (D : IProp GF) [Timeless D] (Tc : IProp GF) (hrefute : ⊢ Tc -∗ D -∗ (False : IProp GF))
    (hsie : k.sie = false) (hK : 6 ≤ k.avail),
    holdBody Goal kctx pcIs lockOpenable locked cpu k γ s R D Tc hrefute hsie hK)
variable (wp_pop_off : ∀ (cpu : CPU) (k : KCtx) (hsie : k.sie = false)
    (hnoff : 1 ≤ k.noff) (hK : 4 ≤ k.avail) (hlks : k.locks.length ≤ k.noff - 1)
    (reen : Bool) (hreen : reen = (decide (k.noff = 1) && k.intena))
    (hon : reen = true → k.tier = .kpt ∧ trapRes true + 2 ≤ k.avail),
    popBody Goal kctx pcIs armP cpu k hsie hnoff hK hlks reen hreen hon)

/-- The release body (Rocq `wp_release_gen_sconf_body`): `Xv6.wp_release_gen_body` with `wpLoop`
:= `Goal`, resources abstract. -/
def wpReleaseGenBody (cpu : CPU) (k : KCtx) (γ : GName) (s : String) (R : Pay) (_hR : payOk R)
    (D : IProp GF) [Timeless D] (Tc : IProp GF) (_hrefute : ⊢ Tc -∗ D -∗ (False : IProp GF))
    (_hsie : k.sie = false)
    (_hnoff : 1 ≤ k.noff) (_hK : 10 ≤ k.avail)
    (reen : Bool) (_hreen : reen = (decide (k.noff = 1) && k.intena))
    (_hon : reen = true → k.tier = .kpt ∧ trapRes true + 6 ≤ k.avail) : Prop :=
  kctx cpu k ∗ pcIs cpu releaseAddr ∗ lockOpenable γ (k.regs 10#5) s R D ∗ Tc ∗
  locked γ cpu ∗ payAt R ∗ armP cpu reen k.proc ∗
  wpNext (k.popExit reen).sie k.proc cpu (fun cpu' => iprop(∀ R' : RegMap,
    kctx cpu' (((k.popExit reen).withRegs R').withLocks (k.locks.filter (fun x => x ≠ s))) -∗
    pcIs cpu' (jumpPc (k.regs 1#5)) -∗ ⌜calleeSaved k.regs R'⌝ -∗ Tc -∗ Goal cpu'))
  ⊢ Goal cpu

/- ================= `Xv6/ProofRelease.lean`'s `release_gen_proof` text =================
   (pasted; the edits are listed in the header, deviation 2) -/
include hkt hlo kctx_kernelText kctx_wf textInstr locked_cases wp_prologue4s1 wp_epilogue4s1_gen
  wp_s_add wp_s_jal wp_s_branch wp_s_fence_rw_w wp_s_sd_zero_lkcpu_release_gen
  wp_s_sw_zero_release_gen wp_holding_locked_gen wp_pop_off in
set_option maxHeartbeats 4000000 in
/-- **`release` over the abstract leaves** (Rocq `wp_release_gen_sconf`). -/
theorem wpReleaseGen (cpu : CPU) (k : KCtx) (γ : GName) (s : String) (R : Pay) (hR : payOk R)
    (D : IProp GF) [Timeless D] (Tc : IProp GF) (hrefute : ⊢ Tc -∗ D -∗ (False : IProp GF))
    (hsie : k.sie = false) (hnoff : 1 ≤ k.noff) (hK : 10 ≤ k.avail)
    (reen : Bool) (hreen : reen = (decide (k.noff = 1) && k.intena))
    (hon : reen = true → k.tier = .kpt ∧ trapRes true + 6 ≤ k.avail) :
    wpReleaseGenBody Goal kctx pcIs payAt payOk lockOpenable locked armP cpu k γ s R hR D Tc
      hrefute hsie hnoff hK reen hreen hon := by
  unfold wpReleaseGenBody
  iintro ⟨Hk, Hpc, #Hlk, Hcred, Hlocked, HR, Harm, HΦ⟩
  icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
  icases kctx_wf _ _ $$ Hk with ⟨%hwf, Hk⟩
  simp only [releaseAddr]
  k_norm
  -- prologue
  iapply (wp_prologue4s1 cpu k hsie KA.«release» (by omega))
  k_code (textInstr _ _ _ _ rfl rfl) Htext
  k_norm
  iframe
  iintro Hk Hpc Hframe
  -- mv s1,a0
  ax_leafs5_kstep (wp_s_add cpu _ (KA.«release» + 0xa#64) true 9#5 0#5 10#5 (by decide)) from (textInstr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  -- jal holding
  ax_leafs5_kstep (wp_s_jal cpu _ (KA.«release» + 0xc#64) false 2096902#21 1#5 (by decide)) from (textInstr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [release_br_ffffffffffffff12]
  iintro Hk Hpc
  have hho : ∀ (k' : KCtx) (hsie' : k'.sie = false) (hK' : 6 ≤ k'.avail),
      kctx cpu k' ∗ pcIs cpu KA.«holding» ∗ lockOpenable γ (k'.regs 10#5) s R D ∗ Tc ∗
      locked γ cpu ∗
      (∀ R' : RegMap, kctx cpu (k'.withRegs R') -∗ pcIs cpu (jumpPc (k'.regs 1#5)) -∗
        ⌜calleeSaved k'.regs R' ∧ R' 10#5 = 1#64⌝ -∗ locked γ cpu -∗ Tc -∗ Goal cpu) ⊢ Goal cpu := by
    intro k' hsie' hK'
    have h := wp_holding_locked_gen cpu k' γ s R D Tc hrefute hsie' hK'
    unfold holdBody at h
    simp only [holdingAddr] at h
    exact h
  iapply (hho _ ?hs ?hK) $$ [- $Hk $Hpc $Hcred $Hlocked]
  rotate_right 1
  k_norm
  iframe #
  case hs => k_norm
  case hK => k_norm; omega
  iintro %R2 Hk Hpc %⟨hcs2, h10⟩ Hlocked Hcred
  have hret1 : jumpPc (KA.«release» + 0x10#64) = (KA.«release» + 0x10#64) := by decide
  k_norm [hret1]
  k_norm at hcs2
  have h29 : R2 9#5 = k.regs 10#5 := by
    have := hcs2.2.2.1
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true] at this
    exact this
  -- beqz a0, panic: not taken (holding answered 1)
  ax_leafs5_kstep (wp_s_branch cpu _ (KA.«release» + 0x10#64) true 28#13 10#5 0#5 (by decide) bop.BEQ) from (textInstr _ _ _ _ rfl rfl) Htext
    $$ [- $Hk $Hpc] with [h10, bcond_beq_one]
  iintro Hk Hpc
  icases locked_cases γ cpu $$ Hlocked with ⟨Hlc, Hheld⟩
  -- sd zero,16(s1): lk->cpu = 0
  ax_leafs5_kstep (wp_s_sd_zero_lkcpu_release_gen cpu _ ?hs (KA.«release» + 0x12#64) false 16#12 9#5 γ (k.regs 10#5) s R D Tc hrefute ?haddr) from (textInstr _ _ _ _ rfl rfl) Htext
    $$ [- $Hk $Hpc $Hcred $Hlc]
  case haddr => k_norm [h29]
  iintro Hk Hpc ⟨Hlp, Hcred⟩
  -- fence rw,w
  ax_leafs5_kstep (wp_s_fence_rw_w cpu _ (KA.«release» + 0x16#64) false) from (textInstr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  -- sw zero,0(s1): the lock is free
  ax_leafs5_kstep (wp_s_sw_zero_release_gen cpu _ ?hs (KA.«release» + 0x1a#64) false 0#12 9#5 γ (k.regs 10#5) s R hR D Tc hrefute ?haddr rfl) from (textInstr _ _ _ _ rfl rfl) Htext
    $$ [- $Hk $Hpc $Hcred $Hlp $Hheld $HR]
  case haddr => k_norm [h29]
  iintro Hk Hpc %hmem Hcred
  -- jal pop_off
  ax_leafs5_kstep (wp_s_jal cpu _ (KA.«release» + 0x1e#64) false 2097050#21 1#5 (by decide)) from (textInstr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [release_br_ffffffffffffffb8]
  iintro Hk Hpc
  have hpo : ∀ (k' : KCtx) (hsie' : k'.sie = false) (hnoff' : 1 ≤ k'.noff)
      (hK' : 4 ≤ k'.avail) (hlks' : k'.locks.length ≤ k'.noff - 1)
      (reen : Bool) (hreen : reen = (decide (k'.noff = 1) && k'.intena))
      (hon' : reen = true → k'.tier = .kpt ∧ trapRes true + 2 ≤ k'.avail),
      kctx cpu k' ∗ pcIs cpu KA.«pop_off» ∗ armP cpu reen k'.proc ∗
      wpNext (k'.popExit reen).sie k'.proc cpu (fun cpu' => iprop(∀ R' : RegMap,
        kctx cpu' ((k'.popExit reen).withRegs R') -∗ pcIs cpu' (jumpPc (k'.regs 1#5)) -∗
        ⌜calleeSaved k'.regs R'⌝ -∗ Goal cpu')) ⊢ Goal cpu := by
    intro k' hsie' hnoff' hK' hlks' reen hreen hon'
    have h := wp_pop_off cpu k' hsie' hnoff' hK' hlks' reen hreen hon'
    unfold popBody at h
    simp only [popOffAddr] at h
    exact h
  have hflt : (k.locks.filter (fun x => x ≠ s)).length < k.locks.length := by
    rw [List.length_filter_lt_length_iff_exists]
    exact ⟨s, hmem, by simp⟩
  iapply (hpo _ ?hs ?hn ?hK ?hl reen ?hr ?ho) $$ [- $Hk $Hpc]
  rotate_right 1
  case hs => k_norm
  case hn => k_norm; omega
  case hK => k_norm; omega
  case hl => k_norm; have := hwf.2.2.2.1; omega
  case hr => k_norm; exact hreen
  case ho => k_norm; intro h; obtain ⟨ht, hav⟩ := hon h; exact ⟨ht, by omega⟩
  k_norm
  iframe Harm
  iapply wpNext_intro_pin
  iintro %c1 %hp1 %R3 Hk Hpc %hcs3
  have hret2 : jumpPc (KA.«release» + 0x22#64) = (KA.«release» + 0x22#64) := by decide
  k_norm [hret2]
  k_norm at hcs3
  -- epilogue, at either index
  have h32 : R3 2#5 = k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64 := by
    have := hcs3.1
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false] at this
    rw [this]
    have h22 := hcs2.1
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true] at h22
    exact h22
  have hav4 : 4 ≤ ((k.popExit reen).withLocks (k.locks.filter (fun x => x ≠ s))).avail := by
    k_norm
    cases reen
    · simp; omega
    · have := (hon rfl).2; simp; omega
  iapply (wp_epilogue4s1_gen c1 ((k.popExit reen).withLocks (k.locks.filter (fun x => x ≠ s)))
    (KA.«release» + 0x22#64) hav4 R3 (by k_norm; exact h32) (k.regs 1#5) (k.regs 8#5) (k.regs 9#5))
    $$ [- $Hk $Hpc]
  k_code (textInstr _ _ _ _ rfl rfl) Htext
  k_norm
  iframe
  k_norm
  ihave HΦ1 := wpNext_shift _ _ cpu c1 _ hp1 $$ HΦ
  iapply wpNext_mono _ _ _ _ _ $$ HΦ1
  iintro %cpu' HK Hk Hpc
  k_norm
  iapply HK $$ %_ Hk Hpc [] Hcred
  ipureintro
  obtain ⟨c3_2, c3_8, c3_9, c3_18, c3_19, c3_20, c3_21, c3_22, c3_23, c3_24, c3_25, c3_26, c3_27⟩ := hcs3
  obtain ⟨c2_2, c2_8, c2_9, c2_18, c2_19, c2_20, c2_21, c2_22, c2_23, c2_24, c2_25, c2_26, c2_27⟩ := hcs2
  simp only [RegMap.set_apply, BitVec.reduceEq, ite_false] at c3_18 c3_19 c3_20 c3_21 c3_22 c3_23 c3_24 c3_25 c3_26 c3_27
  simp only [RegMap.set_apply, BitVec.reduceEq, ite_false] at c2_18 c2_19 c2_20 c2_21 c2_22 c2_23 c2_24 c2_25 c2_26 c2_27
  unfold calleeSaved
  simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true, _root_.true_and]
  exact ⟨c3_18.trans c2_18, c3_19.trans c2_19, c3_20.trans c2_20, c3_21.trans c2_21, c3_22.trans c2_22,
    c3_23.trans c2_23, c3_24.trans c2_24, c3_25.trans c2_25, c3_26.trans c2_26, c3_27.trans c2_27⟩

end AbsRelease

/-! ## 2. Faithfulness: the real SC leaves instantiate `AbsRelease` (the callee specs are
hypotheses, as Rocq's `Hhold` / `Hpop`) -/

set_option maxHeartbeats 1000000 in
/-- **The abstraction is not a strawman** (Rocq `release_faithful`): with the real resources and
leaves, the replay is the real `Xv6.RELEASE_GEN`. -/
theorem releaseFaithful (HO : Xv6.HOLDING) (PO : Xv6.POPOFF) : Xv6.RELEASE_GEN := ⟨
  fun {hlc GF} _ _ cpu k γ s R _ D _ Tc hrefute hsie hnoff hK reen hreen hon =>
    wpReleaseGen (GF := GF) (Pay := MachCSL.CtxId → IProp GF) (Goal := fun c => wpLoop c) (kctx := fun c k => MachCSL.kctx c k)
      (pcIs := fun c pc => MachCSL.pcIs c pc) (instr := fun pc rvc i => MachCSL.instr pc rvc i)
      (kernelText := Xv6.kernelText) (hkt := inferInstance) (frame4 := frame4s1)
      (payAt := fun R => R curCtx) (payOk := fun R => CtxMorph R)
      (lockOpenable := fun γ lk s R D => MachCSL.lockOpenable γ lk s R D)
      (hlo := fun _ _ _ _ _ => inferInstance)
      (locked := fun γ c => MachCSL.locked γ c) (lockedCore := fun γ c => MachCSL.lockedCore γ c)
      (lockedPre := fun γ c => MachCSL.lockedPre γ c) (lockCtxHeld := MachCSL.lockCtxHeld)
      (armP := fun c r p => if r then sieArm c true p else emp)
      (kctx_kernelText := fun c k => Xv6.kctx_kernelText (lent := false) c k)
      (kctx_wf := fun c k => MachCSL.kctx_wf (lent := false) c k)
      (textInstr := fun pc rvc i i₀ hM hS => Xv6.text_instr pc rvc i i₀ hM hS)
      (locked_cases := fun γ c => MachCSL.locked_cases γ c)
      (wp_prologue4s1 := fun c k hs pc hk =>
        (sep_mono_right (sep_mono_right (sep_mono_right (sep_mono_right (sep_mono_right (sep_mono_right (sep_mono_right (later_intro)))))))).trans
          (MachCSL.wp_prologue4s1 (lent := false) c k hs pc hk))
      (wp_epilogue4s1_gen := fun c k pc hk R hR2 ra s0 s1 =>
        (sep_mono_right (sep_mono_right (sep_mono_right (sep_mono_right (sep_mono_right (sep_mono_right (sep_mono_right (sep_mono_right (later_intro))))))))).trans
          (MachCSL.wp_epilogue4s1_gen (lent := false) c k pc hk R hR2 ra s0 s1))
      (wp_s_add := fun c k pc rvc rd rs1 rs2 hrd =>
        (sep_mono_right (sep_mono_right (sep_mono_right (later_intro)))).trans
          (MachCSL.wp_s_add (lent := false) c k pc rvc rd rs1 rs2 hrd))
      (wp_s_jal := fun c k pc rvc imm rd hrd =>
        (sep_mono_right (sep_mono_right (sep_mono_right (later_intro)))).trans
          (MachCSL.wp_s_jal (lent := false) c k pc rvc imm rd hrd))
      (wp_s_branch := fun c k pc rvc imm rs1 rs2 h op =>
        (sep_mono_right (sep_mono_right (sep_mono_right (later_intro)))).trans
          (MachCSL.wp_s_branch (lent := false) c k pc rvc imm rs1 rs2 h op))
      (wp_s_fence_rw_w := fun c k pc rvc =>
        (sep_mono_right (sep_mono_right (sep_mono_right later_intro))).trans
          (MachCSL.wp_s_fence_rw_w (lent := false) c k pc rvc 0#5 0#5))
      (wp_s_sd_zero_lkcpu_release_gen := fun c k hs pc rvc imm rs1 γ lk s R D _ Tc hr ha =>
        (sep_mono_right (sep_mono_right (sep_mono_right (sep_mono_right (sep_mono_right (sep_mono_right (later_intro))))))).trans
          (MachCSL.wp_s_sd_zero_lkcpu_release_gen (lent := false) c k hs pc rvc imm rs1 γ lk s R D Tc hr ha))
      (wp_s_sw_zero_release_gen := fun c k hs pc rvc imm rs1 γ lk s R hR D _ Tc hr ha hpc => by
        haveI : CtxMorph R := hR
        subst hpc
        iintro ⟨Hi, Hk, Hrest⟩
        icases Xv6.kctx_relPcsEq (lent := false) c k $$ Hk with ⟨%hpcs, Hk⟩
        iapply (sep_mono_right (sep_mono_right (sep_mono_right (sep_mono_right (sep_mono_right (sep_mono_right (sep_mono_right (sep_mono_right (later_intro))))))))).trans
          (MachCSL.wp_s_sw_zero_release_gen (lent := false) c k hs _ rvc imm rs1 γ lk s R D Tc hr ha
            (Xv6.xv6RelPc_release hpcs))
        iframe Hi Hk Hrest)
      (wp_holding_locked_gen := fun c k γ s R D _ Tc hr hs hk =>
        HO.wp_holding_locked_gen (hlc := hlc) (GF := GF) c k γ s R D Tc hr hs hk)
      (wp_pop_off := fun c k hs hn hk hl reen hreen hon =>
        PO.wp_pop_off (hlc := hlc) (GF := GF) c k hs hn hk hl reen hreen hon)
      cpu k γ s R inferInstance D Tc hrefute hsie hnoff hK reen hreen hon⟩

/-! ## 3. Instantiation at the WPd surface (`AxLeafS4`)

The replayed proof with `Goal` := `goal2` at the ambient SC hart, `kctx` := `kctxW` (`sieCap2`'s
mirror of the context's fields, plus the kernel text), `pcIs` := `pcIs2`, `instr` := `instr2`; the
`fence rw,w` slot filled by the REAL WPd leaf `AxLeafS4.wpFenceC` (`wpFenceW`), the kernel-text
projection by `kctxWKt`.  Every other slot stays λ-bound (PREMISED): the lock-protocol leaves (D2:
their data steps are `AxLeafS4.wpSdC` / `wpSwC` once the protocol supplies `st8Rule` / `st4Rule`
for the lock word), the frame macros and register leaves (compressed leaves, the ctrl gate), the
callees `holding` / `pop_off` (their own replays), `kctx_wf`, `locked_cases`, the text lemma, and
the resources themselves. -/

section WPdRelease
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64)] [GhostVarG GF Nat]
variable (i : Agent) (cid cpu : CPU) (γm γp γn : GName)
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
  (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
  (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (Cond : Prop → IProp GF) [∀ C, Persistent (Cond C)]
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
variable (kt : IProp GF) [Persistent kt]

/-- Rocq `GoalW`: the WPd goal does not depend on the resuming hart (AxReuseProbe2): it is the
ambient hart's `goal2`. -/
def goalW (_c : CPU) : IProp GF := goal2 i cid cpu γm γp γn T satp0 Cond

/-- Rocq `capW`, at the Lean interface's `kctx` (deviation 4): `sieCap2` of the context's
fields, with the kernel text. -/
def kctxW (c : CPU) (k : KCtx) : IProp GF :=
  iprop(sieCap2 (GF := GF) γm γn c k.regs k.avail k.sie k.proc ∗ kt)

/-- Rocq `pcW`. -/
def pcW (_c : CPU) (pc : BitVec 64) : IProp GF := pcIs2 (GF := GF) γp pc

omit [InvGS_gen hlc GF] [AxirisG GF] [Axpol] [GhostVarG GF (BitVec 64)] in
/-- (Lean-only) The kernel text sits in the context (the `kctx_kernelText` slot, REAL). -/
theorem kctxWKt (c : CPU) (k : KCtx) :
    kctxW γm γn kt c k ⊢ kt ∗ kctxW γm γn kt c k := by
  unfold kctxW
  iintro ⟨Hs, #Hkt⟩
  isplitl []
  · iexact Hkt
  · isplitl
    · iexact Hs
    · iexact Hkt

include hmode hasid hppn Htext Hflow Hloc HG in
/-- (Lean-only) The fence slot at this surface, REAL: `AxLeafS4.wpFenceC` at the context's
fields. -/
theorem wpFenceW (c : CPU) (k : KCtx) (pc : BitVec 64) (is_rvc : Bool) :
    instr2 (GF := GF) σi T satp0 pc is_rvc
        (instruction.FENCE (0#4, 3#4, 1#4, regidx.Regidx 0#5, regidx.Regidx 0#5)) ∗
      kctxW γm γn kt c k ∗ pcW (GF := GF) γp c pc ∗
      wpNext k.sie k.proc c (fun cpu' =>
        iprop(kctxW γm γn kt cpu' k -∗ pcW γp cpu' (pc + instrLen is_rvc) -∗
          goalW i cid cpu γm γp γn T satp0 Cond cpu'))
      ⊢ goalW i cid cpu γm γp γn T satp0 Cond c := by
  cases is_rvc
  · dsimp only [instrLen]
    have HF := wpFenceC (GF := GF) i cid cpu γm γp γn σi T satp0 hmode hasid hppn Cond Htext Hflow
      Hloc G HG pc k.regs k.avail k.sie k.proc
    unfold sieCap2 at HF
    unfold kctxW pcW goalW sieCap2
    iintro ⟨Hi, ⟨Hs, #Hkt⟩, Hp, Hcont⟩
    ihave Hk := AxSymMem3.wpNextSelf k.sie k.proc c _ $$ Hcont
    iapply HF $$ Hs Hp Hi
    iapply wpNext_intro_pin
    iintro %c' %_ Hs' Hp'
    iapply Hk $$ [Hs'] Hp'
    isplitl [Hs']
    · iexact Hs'
    · iexact Hkt
  · unfold instr2
    iintro ⟨%Hins, -⟩
    exact absurd Hins.1 (by decide)

include hmode hasid hppn Htext Hflow Hloc HG in
/-- **The release proof at the WPd surface** (Rocq `release_wpd`), the fence slot and the
kernel-text projection REAL, every other slot and resource λ-bound (the binders of this type). -/
theorem releaseWpd {Pay : Type _} :
    type_of% (wpReleaseGen (GF := GF) (Pay := Pay) (Goal := goalW i cid cpu γm γp γn T satp0 Cond)
      (kctx := kctxW γm γn kt) (pcIs := pcW γp) (instr := instr2 σi T satp0)
      (kernelText := kt) (hkt := inferInstance)
      (kctx_kernelText := kctxWKt γm γn kt)
      (wp_s_fence_rw_w := wpFenceW i cid cpu γm γp γn σi T satp0 hmode hasid hppn Cond
        Htext Hflow Hloc G HG kt)) :=
  wpReleaseGen (GF := GF) (Pay := Pay) (Goal := goalW i cid cpu γm γp γn T satp0 Cond)
    (kctx := kctxW γm γn kt) (pcIs := pcW γp) (instr := instr2 σi T satp0)
    (kernelText := kt) (hkt := inferInstance)
    (kctx_kernelText := kctxWKt γm γn kt)
    (wp_s_fence_rw_w := wpFenceW i cid cpu γm γp γn σi T satp0 hmode hasid hppn Cond
      Htext Hflow Hloc G HG kt)

end WPdRelease

end AxLeafS5

end Weak
