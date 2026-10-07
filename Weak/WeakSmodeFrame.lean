/-
Weak: **does the framing story survive hart migration?** -- the ambient S-mode bundle `wsrun`,
three S-mode leaves stated in `wpNext` form as `Prop`s (`wsld8Spec`, `wsaddiSpec`, `wssd8Spec`),
a three-instruction function `wwpBump` proved over them while carrying an arbitrary objective
frame `cobj ξ F` that no leaf mentions, and the control (§5): a hart-indexed assertion is
re-bound under `wpNext`'s binder, `cobj ξ F` is not.

Rocq: `iris/WeakSmodeFrame.v` @ xxvzwolszwmp.

The Rocq header, in substance.  `WeakCtx` claims that indexing objective ownership by an
execution CONTEXT rather than by a hart makes it survive `wpNext` -- the S-mode step
continuation that quantifies the resuming hart -- with no plumbing, by the ordinary Iris frame
rule.  THE LEAVES ARE HYPOTHESES, NOT AXIOMS: the weak port is M-mode only, so the S-mode leaves
are stated as `Prop`s and taken as premises of the function proof, which makes it a real theorem
("given leaves of this shape, this proof goes through and this frame survives") and adds nothing
to the trusted base.  WHAT IS MEASURED: in `wwpBump` the frame `F` is named exactly twice -- once
in, once out -- and the proof does nothing to it: it crosses three `wpNext` binders untouched.
THE ONE THING THIS DOES NOT SHOW: whether an S-mode weak leaf of this shape is PROVABLE; the store
leaf is stated for an exclusively owned cell and carries no released timestamp, so a publishing
`c.sd` still owes the `T` that `WeakLeafM.wwpSd8TorRvc` hands back (open question).

(The Rocq section comments -- §2's "two things changed and both are forced", §4's reading of the
proof -- are kept in substance on the declarations below.)

**Deviations from Rocq.**

1. VOCABULARY: `Weak/WeakLeafM.lean` deviation 1 (`mword n` ↦ `BitVec n`, `uint x <> 0` ↦
   `x.toNat ≠ 0`, `add_vec_int` ↦ `BitVec.addInt`, `add_vec a (sign_extend' 64 imm)` ↦
   `a + sign_extend (m := 64) imm`, `regval_into_reg v` ↦ `v`, `pc_is` ↦ `pcIs cpu`,
   `gpr_file m` ↦ `MachCSL.gprFile cpu m`, `m !!! Regidx r` ↦ `m.get r`, `<[Regidx rd := v]> m`
   ↦ `m.set rd v`, `regfile` ↦ `RegMap`, `Arch.pa` ↦ `PAddr`, `dfrac` ↦ `DFrac`, `DfracOwn 1` ↦
   `DFrac.own 1`, `WWP Loop` ↦ `wwpTriv ⊤ (WExpr.loop gen cpu)`, `wp_next` ↦ `MachCSL.wpNext`,
   `coh_lb` ↦ `cohLb`, `gname` ↦ `GName`, `Z` ↦ `Int`, `nat` ↦ `Nat`).
2. `CpuId` IS NOT A CLASS IN LEAN (`Weak/WeakCtx.lean` deviation 5): every hart is explicit.
   Rocq's ambient `CID0` is the explicit `cpu0` (first binder of each spec, where `CID0` sat;
   a section argument of `wwpBump`), and `wp_next b p (fun CID : CpuId => K)` is
   `wpNext b p cpu0 (fun cpu => K cpu)` -- the current hart, implicit in Rocq, is `wpNext`'s
   explicit third argument.  `wsrun` takes its hart first, as `wrunning`.  `GenId` ↦ explicit
   `gen : Nat` (a parameter of the three spec `def`s and of `wwpBump`).
3. CONTEXT: Rocq `{!riscvGS Σ, !weakGS Σ}` is `{hlc} [MachGS hlc GF] [WeakGS GF]` (§§1-3);
   §5's `{!weakGS Σ}` is `[WeakGS GF]`.
4. STATEMENT SHAPES (the `WeakLeafM` convention): `wwpBump`'s Rocq `P -∗ Q -∗ … -∗ R` is
   `P ⊢ Q -∗ … -∗ R`; the specs keep Rocq's `⊢ (… -∗ …)`.  The section hypotheses
   `Hld Hadd Hsd` are explicit premises of `wwpBump` (after `gen cpu0`, as the Rocq section
   closes them).  `wsrunOpen` / `wsrunClose` are `⊢`-entailments (`P -∗ Q -∗ R -∗ S` is
   `P ∗ Q ∗ R ⊢ S`, the `WeakCtx` convention).
5. RESUMED HART PINS: Rocq's `wp_next_chain` ltac is the unfolded `wpNext` continuation applied
   to the composed pin facts (`fun h => (h3 h).trans ((h2 h).trans (h1 h))`), i.e. `wpNext_at`.
6. §5 THE CONTROL.  With no `CpuId` class, `hartFloor` takes its hart explicitly, so Rocq's
   A (`hart_indexed_rebinds`: the implicit and the explicit spellings of the binder's hart agree)
   is the Lean `rfl` between the two explicit spellings `fun cpu => hartFloor … cpu` -- the
   rebinding Rocq demonstrates by elaboration is VISIBLE in the Lean term.  Rocq's B
   (`hart_indexed_not_the_callers_frame`) is a `Fail reflexivity. Abort.` -- no declaration; the
   Lean twin is an `example` checking with `fail_if_success` that `rfl` does NOT close it.
   Section variables `F b p ξ a t γ0` become explicit arguments in Lean's variable order.

**Rocq → Lean name map.**  `wsrun` `wsrun`, `wsrun_open` `wsrunOpen`, `wsrun_close`
`wsrunClose`, `wsld8_spec` `wsld8Spec`, `wsaddi_spec` `wsaddiSpec`, `wssd8_spec` `wssd8Spec`,
`wwp_bump` `wwpBump`, `hart_floor` `hartFloor`, `hart_indexed_rebinds` `hartIndexedRebinds`,
`cobj_survives` `cobjSurvives` (+ the aborted `hart_indexed_not_the_callers_frame` as an
`example`).  None is in the duplicated-name table.

**Dropped:** nothing (Rocq 10 declarations + 1 aborted; Lean 10 + 1 `example`).
-/
import Weak.WeakCtx
import Weak.WeakWord8
import Weak.WeakLeafM

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 1. The ambient S-mode bundle

In the real port this is the S-mode `sie_cap_gpr` bundle plus one conjunct (`sconf` is where
the view token belongs in S-mode); here it is cut down to the two parts the experiment turns on.
THE SHAPE IS THE POINT: the hart is the argument `wpNext`'s binder re-binds, so inside it `wsrun`
is at the RESUMING hart and its `hartWs` follows; `ξ` is a plain argument, so it does not. -/

section bundle
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wsrun`. -/
def wsrun (cpu : CPU) (ξ : CtxId) (m : RegMap) : IProp GF :=
  iprop(gprFile cpu m ∗ wrunning cpu ξ)

/-- Rocq `wsrun_open`. -/
theorem wsrunOpen (cpu : CPU) (ξ : CtxId) (m : RegMap) :
    wsrun (GF := GF) cpu ξ m ⊢ gprFile cpu m ∗ ∃ ws, hartWs cpu ws ∗ ctxRun cpu ξ ws := by
  unfold wsrun
  iintro ⟨H1, H⟩
  iframe H1
  iapply wrunningOpen cpu ξ $$ H

/-- Rocq `wsrun_close`. -/
theorem wsrunClose (cpu : CPU) (ξ : CtxId) (m : RegMap) (ws : Wstate) :
    gprFile (GF := GF) cpu m ∗ hartWs cpu ws ∗ ctxRun cpu ξ ws ⊢ wsrun cpu ξ m := by
  unfold wsrun
  iintro ⟨H1, H2, H3⟩
  iframe H1
  iapply wrunningClose cpu ξ ws
  iframe H2 H3

end bundle

/-! ## 2. Three S-mode leaves, in `wpNext` form

Compared with their M-mode twins in `WeakLeafM`, two things changed and both are forced.
(1) `hartWs cpu ws` and the `∀ ws', ⌜wsLe ws ws'⌝` pair became `wsrun cpu ξ m`: `ws'` is the
RESUMING hart's wstate, and `wsLe ws ws'` is FALSE across a migration, so the monotonicity has to
be internal to the context (`wrunningStep`, `wrunningResume`).  (2) `vwpHold F ws` became
`cobj ξ R`: `vwpHold F ws` names a wstate and cannot even be written in the continuation; `cobj ξ R`
names neither a hart nor a wstate, so it is spelled identically on both sides of the binder. -/

section leafSpecs
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wsld8_spec`: `ld rd, imm(rs1)` -- 8 bytes, from a cell the context owns. -/
def wsld8Spec (gen : Nat) : Prop :=
  ∀ (cpu0 : CPU) (ξ : CtxId) (b : Bool) (p : BitVec 64) (cmp : Bool)
    (pc : BitVec 64) (rd rs1 : BitVec 5) (imm : BitVec 12) (m : RegMap)
    (ea : PAddr) (v : BitVec 64) (dq : DFrac),
  rd.toNat ≠ 0 →
  m.get rs1 + sign_extend (m := 64) imm = ea →
  ⊢ wsrun (GF := GF) cpu0 ξ m -∗
      pcIs cpu0 pc -∗
      winstrM (GF := GF) pc cmp (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)) -∗
      cobj ξ (wpt8 (GF := GF) ea dq v) -∗
      wpNext b p cpu0 (fun cpu =>
        iprop(wsrun cpu ξ (m.set rd v) -∗
          pcIs cpu (BitVec.addInt pc (if cmp then 2 else 4)) -∗
          cobj ξ (wpt8 (GF := GF) ea dq v) -∗
          wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu))) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu0)

/-- Rocq `wsaddi_spec`: `addi rd, rs1, imm` -- register-only, so it touches no `cobj` at all. -/
def wsaddiSpec (gen : Nat) : Prop :=
  ∀ (cpu0 : CPU) (ξ : CtxId) (b : Bool) (p : BitVec 64) (cmp : Bool)
    (pc : BitVec 64) (rd rs1 : BitVec 5) (imm : BitVec 12) (m : RegMap),
  rd.toNat ≠ 0 →
  ⊢ wsrun (GF := GF) cpu0 ξ m -∗
      pcIs cpu0 pc -∗
      winstrM (GF := GF) pc cmp (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI)) -∗
      wpNext b p cpu0 (fun cpu =>
        iprop(wsrun cpu ξ (m.set rd (m.get rs1 + sign_extend (m := 64) imm)) -∗
          pcIs cpu (BitVec.addInt pc (if cmp then 2 else 4)) -∗
          wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu))) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu0)

/-- Rocq `wssd8_spec`: `sd rs2, imm(rs1)` -- 8 bytes, into a cell the context owns
EXCLUSIVELY.  No released timestamp, and there should not be: a store to your own cell
publishes nothing, so it is objective in and objective out, which is why it fits the `wpNext`
shape unchanged while `WeakLeafM.wwpSd8TorRvc` does not. -/
def wssd8Spec (gen : Nat) : Prop :=
  ∀ (cpu0 : CPU) (ξ : CtxId) (b : Bool) (p : BitVec 64) (cmp : Bool)
    (pc : BitVec 64) (rs2 rs1 : BitVec 5) (imm : BitVec 12) (m : RegMap)
    (ea : PAddr) (vold : BitVec 64),
  rs1.toNat ≠ 0 →
  rs2.toNat ≠ 0 →
  m.get rs1 + sign_extend (m := 64) imm = ea →
  ⊢ wsrun (GF := GF) cpu0 ξ m -∗
      pcIs cpu0 pc -∗
      winstrM (GF := GF) pc cmp (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)) -∗
      cobj ξ (wpt8 (GF := GF) ea (DFrac.own 1) vold) -∗
      wpNext b p cpu0 (fun cpu =>
        iprop(wsrun cpu ξ m -∗
          pcIs cpu (BitVec.addInt pc (if cmp then 2 else 4)) -∗
          cobj ξ (wpt8 (GF := GF) ea (DFrac.own 1) (m.get rs2)) -∗
          wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu))) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu0)

end leafSpecs

/-! ## 3. THE FUNCTION

    ld   rV, immX(rX)      ; rV := *X
    addi rV, rV, immI
    sd   rV, immY(rY)      ; *Y := rV

Three instructions, three `wpNext` crossings, at a GENERIC `b` -- every one may migrate.  The
caller holds the cells at `X` and `Y` (named, because the instructions touch them) and `F`, an
ARBITRARY `VProp`, which is the thing under test.

§4 of the Rocq file, read off the proof: `HF` appears exactly twice, in the opening `iintro` and
in the closing `iapply`; it crosses three `wpNext` binders and is never passed to a leaf,
converted, weakened or mentioned in a side condition -- possible only because `cobj ξ F` is the
SAME PROPOSITION inside and outside the binder.  What had to go in: `wsrun cpu ξ m` (the leaf
steps the machine and moves the context's floor with it) and the two touched cells.  The SC
precedent is `CpuOwn.cpu_own_transport` at every migration point -- correct for a genuinely
per-hart resource; `WeakCtx`'s content is that objective memory ownership is not one. -/

section framing
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wwp_bump`. -/
theorem wwpBump (gen : Nat) (cpu0 : CPU)
    (Hld : wsld8Spec (hlc := hlc) (GF := GF) gen)
    (Hadd : wsaddiSpec (hlc := hlc) (GF := GF) gen)
    (Hsd : wssd8Spec (hlc := hlc) (GF := GF) gen)
    (ξ : CtxId) (F : VProp GF)
    (b : Bool) (p : BitVec 64) (pc : BitVec 64) (m : RegMap)
    (rV rX rY : BitVec 5) (immX immI immY : BitVec 12)
    (eaX eaY : PAddr) (vX vY : BitVec 64) (dqX : DFrac)
    (m1 m2 : RegMap) :
    rV.toNat ≠ 0 →
    rX.toNat ≠ 0 →
    rY.toNat ≠ 0 →
    m1 = m.set rV vX →
    m2 = m1.set rV (m1.get rV + sign_extend (m := 64) immI) →
    m.get rX + sign_extend (m := 64) immX = eaX →
    m2.get rY + sign_extend (m := 64) immY = eaY →
    wsrun (GF := GF) cpu0 ξ m ⊢
      pcIs cpu0 pc -∗
      winstrM (GF := GF) pc false (.LOAD (immX, .Regidx rX, .Regidx rV, false, 8)) -∗
      winstrM (GF := GF) (BitVec.addInt pc 4) false
        (.ITYPE (immI, .Regidx rV, .Regidx rV, .ADDI)) -∗
      winstrM (GF := GF) (BitVec.addInt (BitVec.addInt pc 4) 4) false
        (.STORE (immY, .Regidx rV, .Regidx rY, 8)) -∗
      cobj ξ (wpt8 (GF := GF) eaX dqX vX) -∗
      cobj ξ (wpt8 (GF := GF) eaY (DFrac.own 1) vY) -∗
      cobj ξ F -∗
      wpNext b p cpu0 (fun cpu =>
        iprop(wsrun cpu ξ m2 -∗
          pcIs cpu (BitVec.addInt (BitVec.addInt (BitVec.addInt pc 4) 4) 4) -∗
          cobj ξ (wpt8 (GF := GF) eaX dqX vX) -∗
          cobj ξ (wpt8 (GF := GF) eaY (DFrac.own 1) (m2.get rV)) -∗
          cobj ξ F -∗
          wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu))) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu0) := by
  intro hnzV hnzX hnzY hm1 hm2 heaX heaY
  subst hm1 hm2
  iintro Hrun Hpc #Hi0 #Hi1 #Hi2 HX HY HF Hcont
  -- 1. the load.  `HY` and `HF` are simply not mentioned.
  iapply (Hld cpu0 ξ b p false pc rV rX immX m eaX vX dqX hnzV heaX) $$ Hrun Hpc Hi0 HX
  unfold wpNext
  iintro %cpu1 %hpin1 Hrun Hpc HX
  simp only [Bool.false_eq_true, ↓reduceIte]
  -- We are now on hart `cpu1`, which need not be `cpu0`.  `HY` and `HF` are spelled exactly as
  -- they were, because `cobj` mentions `ξ` and not the hart.
  -- 2. the register-only step.
  iapply (Hadd cpu1 ξ b p false (BitVec.addInt pc 4) rV rV immI (m.set rV vX) hnzV) $$
    Hrun Hpc Hi1
  unfold wpNext
  iintro %cpu2 %hpin2 Hrun Hpc
  simp only [Bool.false_eq_true, ↓reduceIte]
  -- 3. the store.
  iapply (Hsd cpu2 ξ b p false (BitVec.addInt (BitVec.addInt pc 4) 4) rV rY immY _ eaY vY
    hnzY hnzV heaY) $$ Hrun Hpc Hi2 HY
  unfold wpNext
  iintro %cpu3 %hpin3 Hrun Hpc HY
  simp only [Bool.false_eq_true, ↓reduceIte]
  -- discharge our own `wpNext` at whatever hart we ended on.
  -- (`unfold wpNext` above also unfolded `Hcont`: it is `wpNext_at`'s body.)
  iapply Hcont $$ %cpu3 %(fun h => (hpin3 h).trans ((hpin2 h).trans (hpin1 h)))
    Hrun Hpc HX HY HF

end framing

/-! ## 5. THE CONTROL, MACHINE-CHECKED

`hartFloor` is the smallest thing with the deleted hart-indexed layer's indexing: an `IProp`
whose definition mentions the hart, and inside `wpNext`'s binder that is the RESUMING hart.
`cobj`'s context is a plain argument and cannot be captured this way.  The hart-indexed ghost
name `γ0` is a bare variable: what is tested is the INDEX, not the resource. -/

section control
variable {GF : BundledGFunctors} [WeakGS GF]
variable (F : VProp GF) (b : Bool) (p : BitVec 64) (ξ : CtxId)
variable (a : Int) (t : Nat)
variable (γ0 : CPU → GName)

/-- Rocq `hart_floor` (deviation 6: the hart is explicit). -/
def hartFloor (cpu : CPU) : IProp GF :=
  cohLb (γ0 cpu) a t

/-- Rocq `hart_indexed_rebinds`: under the binder, a hart-indexed assertion means the RESUMING
hart's (deviation 6). -/
theorem hartIndexedRebinds (cpu0 : CPU) :
    wpNext b p cpu0 (fun cpu => hartFloor (GF := GF) a t γ0 cpu)
      = wpNext b p cpu0 (fun cpu => hartFloor (GF := GF) a t γ0 cpu) := rfl

/- Rocq `hart_indexed_not_the_callers_frame` (`Fail reflexivity. Abort.`): the caller's
assertion (at `cpu0`) and the one the continuation demands are different propositions, and the
only bridge needs BOTH harts' authorities in one step, which migrating denies.  Checked here:
`rfl` does NOT identify them. -/
example (cpu0 : CPU) : True := by
  fail_if_success
    have : wpNext b p cpu0 (fun cpu => hartFloor (GF := GF) a t γ0 cpu)
        = wpNext b p cpu0 (fun _ => hartFloor (GF := GF) a t γ0 cpu0) := rfl
  trivial

/-- Rocq `cobj_survives`: `cobj ξ F` is literally the same term on both sides of the binder,
which is all the Iris frame rule ever needed. -/
theorem cobjSurvives (cpu0 : CPU) :
    wpNext b p cpu0 (fun _ => cobj ξ F) = wpNext b p cpu0 (fun _ => cobj ξ F) := rfl

end control

end Weak
