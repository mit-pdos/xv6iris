/-
Weak: **xv6's `release` replayed on SURFACE v4 (`AxRelease`) with the register / frame leaves
and the three lock-word leaves REAL, and NO `CondGate3` anywhere** (AxSL tier).

Rocq: `iris/AxRelease4.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`release_wpd4` = `AxLeafS5.wp_release_gen_sconf` (the pasted release proof text over the
abstract interface) at `GoalW4` (ambient hart's `goal4`) / `capW4` (`cap4` with free stack :=
the interface's `stack_own`) / `pcW4` (`pcIs4 armedR`) / `instrW4` (`instr4 armedR Ex`), NINE
slots REAL: `c.addi sp,-32` (`w_push4`), `c.sdsp` ×3 (`w_csdsp4`), `c.addi4spn` (`w_c4spn4`),
`c.mv` (`w_cmv4`), `sd zero,16(s1)` (`w_sdlk4`), `fence rw,w` (`w_fence4`), `sw zero,0(s1)` at
class WCrel (`w_swfin4`), `c.ldsp` ×3 (`w_cldsp4`), `c.addi16sp` (`w_c16_4`) — the store / AMO
leaves take their base from the exact map `Ex`, so no `Cond_gate`.  λ-BOUND: the kernel text,
`cpu_own`, `arm_pay`, the control slots `w_jal` / `w_cbeqz` / `w_cret`, the callees `w_hold` /
`w_pop`, `stack_own_slots`, `cpu_own_transport`, the 20 text facts `rli_*`.  Section premises:
the bridge's `Htext Hflow Hloc HG`, `Hdmap`, the stack laws `SF_push` / `SF_pop`, the stack-word
rules `ld_rule` / `st_rule` + `Cond_and` + `HnoRmw_reg`, the lock rules `sdlk_rule` / `swlk_rule`
(discharged at a concrete instance in AxRelease3), the exact map `Ex` (AxRelease5's `Ex_rel`).

## Deviations from Rocq

1. THE INTERFACE IS AxLeafS5's LEAN ONE (AxLeafS5 deviation 1, AxCondM4 deviation 1): the
   replayed text is `Xv6.release_gen_proof`, over `kctx` / `KCtx`, the frame macros
   `wp_prologue4s1` / `wp_epilogue4s1_gen` with a `frame4` resource, the generic `wp_s_add`, and
   later-free slots (AxLeafS5 deviation 3).  So:
   - Rocq `capW4` (kept, for the Rocq-shaped leaves) is wrapped in the Lean-only
     `AxRelease4.kctxW4 c k := capW4 … c k.regs k.avail k.sie k.proc ∗ held c k.locks ∗ kt`
     (`held`: the hart's held-lock set, AxCondM4 deviation 1; `kt`: the kernel text, whose
     projection slot is REAL, `AxRelease4.kctxW4Kt`);
   - the six Rocq frame / register leaves are ported AS STATED (`wPush4` `wCsdsp4` `wC4spn4`
     `wCmv4` `wCldsp4` `wC164`, at an arbitrary resuming hart `c0`) and COMPOSED into the Lean
     slots: `AxRelease4.wPrologue4` = push; c.sdsp ra/s0/s1; c.addi4spn (the `wp_prologue4s1`
     slot), `AxRelease4.wAdd4` = `wCmv4` (the `wp_s_add` slot), `AxRelease4.wEpilogue4` =
     c.ldsp ra/s0/s1; c.addi16sp; c.ret (the `wp_epilogue4s1_gen` slot), with `frame4 :=
     AxRelease4.frameW4 wpt` (the owned words at `paStk sp 1..3` and a free one at `paStk sp 4`,
     `frame4s1`'s layout).  Rocq's λ-bound `stack_own_slots` (`stackOwnSlots`, opening /
     closing the four pushed slots) and `w_cret` (`wCret4`, Rocq's `wp_cret_s_sconf` slot shape
     at surface v4 — the Lean epilogue macro bundles the `c.ret`) are section premises of the
     two frame fillers, hence binders of `releaseWpd4`;
   - the lock leaves `wSdlk4` / `wFence4` / `wSwfin4` are stated in the slot shape (as
     AxCondM4's `wSdlk3` / `wFence3` / `wSwfin3`, over AxRelease's gate-free `wpStoreC4` /
     `wpFenceC4`); Rocq's refutation premises `⊢ locked γl h0 -∗ Dc -∗ False` are the slots'
     credential `Tc` / `hrefute`.
   REMAINING λ-BOUND (binders of `releaseWpd4`'s type): `locked`, `armP` (Rocq `cpu_own` /
   `arm_pay` / `cpu_own_transport`), `kctx_wf`, `textInstr` (Rocq `rli_*`), `locked_cases`,
   `wp_s_jal` (`w_jal`), `wp_s_branch` (`w_cbeqz`), `wp_holding_locked_gen` / `wp_pop_off`
   (`w_hold` / `w_pop`); `stackOwnSlots`, `wCret4` (above).
2. `instrW4` = Rocq's `instr4 armedR Ex` plus the pure `AxRelease4.instrX`: a store of `x0` /
   `fence rw,w` is 4-byte (AxCondM4 deviation 2) and an `add` is a `c.mv` (compressed, first
   source `x0`) — the Lean slots are generic in `is_rvc` / `rs1` where Rocq's leaves are not.  It
   only strengthens the λ-bound `textInstr`; it holds at the words the text steps (release+0xa
   `c.mv s1,a0`, +0x12/+0x16/+0x1a 4-byte), not at every pc of the image — as `instr4`'s own
   `isSwz → armedR` (and Rocq's `release_wpd4`, whose `rli_10` is ⌜False⌝, AxSpinCtl §3).
3. THE LOCK RULES (AxCondM4 deviation 1): `sdlkRule` / `swlkRule` are AxCondM4's shapes (`locked`
   ↦ `lockedCore`; `lk + 16#64` = `AxRelease3.lockCpu lk`; `swlkRule`'s output is the held set
   without `s` and `⌜s ∈ ks⌝`, no `lock_finisher` / `Out`).  THE BRIDGE from Rocq's shape:
   `AxRelease4.swlkRuleOfFinisher` derives `swlkRule` from Rocq's `swlk_rule` (abstract
   `lockFinisher γ lk R Dc Out E`, Rocq's mask `⊤ ∖ ↑minstretN` a parameter `E`, Q3) and
   `finHeld` — THE LOCK PROTOCOL MUST NAME THE HELD LOCK: from the handle (which names `s`),
   `lockCtxHeld` and `held c ks`, mint the finisher whose `Out` is `held c (ks.filter (· ≠ s)) ∗
   ⌜s ∈ ks⌝`.  At AxRelease3's instance (`rlLockFinisher := Out`, the caller pre-pays) this is
   satisfiable: `AxRelease4.rlRulesHeld` gives BOTH rules at `rlAxirisG γb` / `lockAxpol` with
   the handle naming its lock (`AxRelease4.rlLockOpenableN γb sL := ⌜s = sL⌝ ∗ rlLockOpenable`,
   as AxRelease3 pins `lk = L0`), the held context an exclusive token (`AxRelease4.rlCtxHeld γh`)
   and the held set complete for `sL` (`AxRelease4.rlHeld`: `emp` if `sL ∈ ks`, else the same
   token).  HONESTY: one lock name; the held set is a model, not the SC tree's `lockSetAt`.
4. TYPES / SPELLING as AxCondM4 deviation 3 / AxRelease deviation 3: Rocq's `CpuId` contexts ↦
   explicit harts (`cid` ambient; `c0` / `c` resuming), `GenId` dropped; `rget (CID:=CID0) m r`
   ↦ `rget c0 m r` (moved to `cid` off tp by `AxCondM4.rgetCpu`, tp excluded by `srcOk`);
   `wp_next_off` / `on_` ↦ `AxSymMem3.wpNextSelf` / `wpNext_intro`; `ret_pc` ↦ `jumpPc`;
   `zeros' 12` ↦ `0#12`; `seq 1 n` ↦ `List.range' 1 n`; `Arch.pa` ↦ `PAddr`; `cap4`'s free
   stack `SF` and the pushed slots are both `stackOwn` (Rocq passes `stack_own` twice).  The
   iProp-valued premises are `⊢` entailments.
5. `releaseWpd4` is a theorem stated by `type_of%` of the partial application (Rocq
   `Definition release_wpd4 := λ …`).

**Rocq → Lean name map.**  `GoalW4` `goalW4`, `capW4` `capW4`, `pcW4` `pcW4`, `instrW4`
`instrW4` (deviation 2), `w_push4` `wPush4`, `w_csdsp4` `wCsdsp4`, `w_c4spn4` `wC4spn4`, `w_cmv4`
`wCmv4`, `w_cldsp4` `wCldsp4`, `w_c16_4` `wC164`, `w_sdlk4` `wSdlk4`, `w_fence4` `wFence4`,
`w_swfin4` `wSwfin4`, `release_wpd4` `releaseWpd4`; section parameters `stack_own` `stackOwn`,
`SF_push` `SFPush`, `SF_pop` `SFPop`, `ld_rule` `ldRule`, `st_rule` `stRule`, `Cond_and`
`CondAnd`, `HnoRmw_reg` `HnoRmwReg`, `locked_pre` `lockedPre`, `lock_openable` `lockOpenable`,
`Hlo` `hlo`, `sdlk_rule` `sdlkRule`, `swlk_rule` `swlkRule` (deviation 3); λ-bound
`stack_own_slots` `stackOwnSlots`, `w_cret` `wCret4`.  None is in the duplicated-name table.
Lean-only (file-qualified): `AxRelease4.instrX`, `kctxW4`, `frameW4`, `kctxW4Kt`, `paStkAdd`,
`spEq`, `zregEq`, `slots4`, `capW4Sie`, `wCsdspAt`, `wCldspAt`, `wC16At`, `wAdd4`, `wPrologue4`,
`wEpilogue4`, `swlkRuleOfFinisher`, `rlLockOpenableN` (+ `rlLockOpenableNPers`), `rlCtxHeld`,
`rlHeld`, `rlFinHeld`, `rlRulesHeld`.

Build: ~4.5 s (VM).

**Dropped:** nothing (Rocq 14 definitions/lemmas; Lean 14 + 22 Lean-only).  **Not ported:** the
Ltacs `off` / `on_`, the `Notation STORE_LEAF` (inlined), the `Check` / `Print Assumptions`
lines (the lint's axiom check covers them).
-/
import Weak.AxCondM4
import Weak.AxRelease
import Weak.AxRelease3

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- (Lean-only, deviation 2) the two text facts the generic slots need beyond `instr4`: a
store of `x0` / `fence rw,w` is 4-byte, and an `add` of the text is a `c.mv` (compressed,
first source `x0`). -/
def AxRelease4.instrX (ins : instruction) (is_rvc : Bool) : Prop :=
  (AxCondM4.zeroStOrFence ins → is_rvc = false) ∧
  (∀ rs2 rs1 rd : BitVec 5,
    ins = .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .ADD) → is_rvc = true ∧ rs1 = 0#5)

section WPdRelease4
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

/- the stack: the release interface's `stack_own` IS the free-stack resource of `cap4`; its
push / pop laws; the owned words `wpt` with their protocol rules -/
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

/- the lock resources (AxLeafS5's interface, as AxCondM4) and the two protocol STORE rules
(AxCondM4's shapes; `swlkRule` from Rocq's finisher shape: `AxRelease4.swlkRuleOfFinisher`) -/
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

/-- Rocq `GoalW4`: the ambient hart's `goal4`. -/
def goalW4 (_c : CPU) : IProp GF := goal4 i cid cpu γm γp γn T satp0 Ex Cond

/-- Rocq `capW4`: `cap4` with the free stack := `stackOwn`. -/
def capW4 (c0 : CPU) (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) : IProp GF :=
  cap4 (GF := GF) γm γn stackOwn c0 m n b p

/-- Rocq `pcW4`. -/
def pcW4 (_c : CPU) (pc : BitVec 64) : IProp GF := pcIs4 (GF := GF) γp armedR pc

/-- Rocq `instrW4` (+ deviation 2). -/
def instrW4 (pc : BitVec 64) (is_rvc : Bool) (ins : instruction) : IProp GF :=
  iprop(instr4 (GF := GF) σi T satp0 armedR Ex pc is_rvc ins ∗ ⌜AxRelease4.instrX ins is_rvc⌝)

/-- (Lean-only, deviation 1) the Lean interface's `kctx` at surface v4: `capW4` of the context's
fields, the held-lock set, the kernel text. -/
def AxRelease4.kctxW4 (c : CPU) (k : KCtx) : IProp GF :=
  iprop(capW4 (GF := GF) γm γn stackOwn c k.regs k.avail k.sie k.proc ∗ held c k.locks ∗ kt)

/-- (Lean-only, deviation 1) the frame resource between the prologue and the epilogue
(`frame4s1`'s shape over the owned words `wpt`). -/
def AxRelease4.frameW4 (sp ra s0 s1 : BitVec 64) : IProp GF :=
  iprop(wpt (paStk sp 1) (.own 1) ra ∗ wpt (paStk sp 2) (.own 1) s0 ∗
    wpt (paStk sp 3) (.own 1) s1 ∗ ∃ w : BitVec 64, wpt (paStk sp 4) (.own 1) w)

omit [InvGS_gen hlc GF] [AxirisG GF] [Axpol] [GhostVarG GF (BitVec 64 × Bool)] in
/-- (Lean-only) The kernel text sits in the context (the `kctx_kernelText` slot, REAL). -/
theorem AxRelease4.kctxW4Kt (c : CPU) (k : KCtx) :
    AxRelease4.kctxW4 γm γn stackOwn held kt c k ⊢ kt ∗ AxRelease4.kctxW4 γm γn stackOwn held kt c k := by
  unfold AxRelease4.kctxW4
  iintro ⟨Hs, Hh, #Hkt⟩
  isplitl []
  · iexact Hkt
  · isplitl [Hs]
    · iexact Hs
    · isplitl [Hh]
      · iexact Hh
      · iexact Hkt

/-! ## The register / frame leaves at an arbitrary resuming hart (Rocq's slot shape) -/

include hmode hasid hppn Htext Hflow SFPush in
/-- Rocq `w_push4`: `c.addi sp, -imm`. -/
theorem wPush4 (c0 : CPU) (p pc : BitVec 64) (imm : BitVec 6) (m : RegMap) (n k : Nat) (b : Bool) :
    k ≤ n → m 2#5 + sign_extend (m := 64) (sign_extend (m := 12) imm) = paStk (m 2#5) k →
    ⊢ capW4 γm γn stackOwn c0 m n b p -∗ pcW4 γp c0 pc -∗
      instrW4 σi T satp0 Ex pc true (.ITYPE (sign_extend (m := 12) imm, .Regidx 2#5, .Regidx 2#5, .ADDI)) -∗
      wpNext b p c0 (fun c1 => iprop(
        capW4 γm γn stackOwn c1
          (m.set 2#5 (m 2#5 + sign_extend (m := 64) (sign_extend (m := 12) imm))) (n - k) b p -∗
        stackOwn (m 2#5) k -∗ pcW4 γp c1 (pc + 2#64) -∗
        goalW4 i cid cpu γm γp γn T satp0 Ex Cond c1)) -∗
      goalW4 i cid cpu γm γp γn T satp0 Ex Cond c0 := by
  intro Hk Hw
  have L := wpCaddiSpPushC4 i cid cpu γm γp γn σi T satp0 hmode hasid hppn armedR Ex stackOwn
    Cond Htext Hflow stackOwn SFPush pc imm m n k b p Hk Hw
  unfold cap4 at L
  unfold capW4 pcW4 goalW4 instrW4 cap4
  iintro Hc Hp ⟨Hi, %_⟩ Hk
  ihave Hk := AxSymMem3.wpNextSelf b p c0 _ $$ Hk
  iapply L $$ Hc Hp Hi
  iapply wpNext_intro
  iintro %_
  iexact Hk

include hmode hasid hppn Htext Hflow Hloc HG Hdmap stRule in
/-- Rocq `w_csdsp4`: `c.sdsp rs2, uimm(sp)`. -/
theorem wCsdsp4 (c0 : CPU) (p pc : BitVec 64) (uimm : BitVec 6) (rs2 : BitVec 5)
    (m : RegMap) (n : Nat) (vold : BitVec 64) (b : Bool) :
    ⊢ capW4 γm γn stackOwn c0 m n b p -∗ pcW4 γp c0 pc -∗
      instrW4 σi T satp0 Ex pc true
        (.STORE (zero_extend (m := 12) (uimm +++ 0b000#3), .Regidx rs2, sp, 8)) -∗
      wpt (m 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3)) (.own 1) vold -∗
      wpNext b p c0 (fun c1 => iprop(
        capW4 γm γn stackOwn c1 m n b p -∗ pcW4 γp c1 (pc + 2#64) -∗
        wpt (m 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3)) (.own 1) (rget c0 m rs2) -∗
        goalW4 i cid cpu γm γp γn T satp0 Ex Cond c1)) -∗
      goalW4 i cid cpu γm γp γn T satp0 Ex Cond c0 := by
  have L := wpCsdspC4 i cid cpu γm γp γn σi T satp0 hmode hasid hppn armedR Ex stackOwn Cond
    Htext Hflow Hloc G HG dreg damo Hdmap wpt stRule pc uimm rs2 m n vold b p
  unfold cap4 instr4 at L
  unfold capW4 pcW4 goalW4 instrW4 cap4 instr4
  iintro Hc Hp ⟨%Hi, %_⟩ Hw Hk
  have hs : regidx.Regidx rs2 ≠ regidx.Regidx 4#5 := Hi.2.2.1.2
  have hne : rs2 ≠ 4#5 := fun h => hs (by rw [h])
  rw [AxCondM4.rgetCpu c0 cid m rs2 hne]
  ihave Hk := AxSymMem3.wpNextSelf b p c0 _ $$ Hk
  iapply L $$ Hc Hp %Hi Hw
  iapply wpNext_intro
  iintro %_
  iexact Hk

include hmode hasid hppn Htext Hflow in
/-- Rocq `w_c4spn4`: `c.addi4spn rd', sp, nzimm`. -/
theorem wC4spn4 (c0 : CPU) (p pc : BitVec 64) (rdc : cregidx) (nzimm : BitVec 8) (rd : BitVec 5)
    (m : RegMap) (n : Nat) (b : Bool) :
    creg2reg_idx rdc = .Regidx rd → rd.toNat ≠ 0 → MachCSL.rdOk rd →
    ⊢ capW4 γm γn stackOwn c0 m n b p -∗ pcW4 γp c0 pc -∗
      instrW4 σi T satp0 Ex pc true (.ITYPE (caddi4spnImm nzimm, sp, .Regidx rd, .ADDI)) -∗
      wpNext b p c0 (fun c1 => iprop(
        capW4 γm γn stackOwn c1
          (m.set rd (m 2#5 + sign_extend (m := 64) (caddi4spnImm nzimm))) n b p -∗
        pcW4 γp c1 (pc + 2#64) -∗ goalW4 i cid cpu γm γp γn T satp0 Ex Cond c1)) -∗
      goalW4 i cid cpu γm γp γn T satp0 Ex Cond c0 := by
  intro Hc Hrd Hrdok
  have L := wpCaddi4spnC4 i cid cpu γm γp γn σi T satp0 hmode hasid hppn armedR Ex stackOwn
    Cond Htext Hflow pc rdc nzimm rd m n b p Hc Hrd Hrdok
  unfold cap4 at L
  unfold capW4 pcW4 goalW4 instrW4 cap4
  iintro Hc Hp ⟨Hi, %_⟩ Hk
  ihave Hk := AxSymMem3.wpNextSelf b p c0 _ $$ Hk
  iapply L $$ Hc Hp Hi
  iapply wpNext_intro
  iintro %_
  iexact Hk

include hmode hasid hppn Htext Hflow in
/-- Rocq `w_cmv4`: `c.mv rd, rs2`. -/
theorem wCmv4 (c0 : CPU) (p pc : BitVec 64) (rd rs2 : BitVec 5) (m : RegMap) (n : Nat) (b : Bool) :
    rd.toNat ≠ 0 → MachCSL.rdOk rd →
    ⊢ capW4 γm γn stackOwn c0 m n b p -∗ pcW4 γp c0 pc -∗
      instrW4 σi T satp0 Ex pc true (.RTYPE (.Regidx rs2, zreg, .Regidx rd, .ADD)) -∗
      wpNext b p c0 (fun c1 => iprop(
        capW4 γm γn stackOwn c1 (m.set rd (0#64 + rget c0 m rs2)) n b p -∗
        pcW4 γp c1 (pc + 2#64) -∗ goalW4 i cid cpu γm γp γn T satp0 Ex Cond c1)) -∗
      goalW4 i cid cpu γm γp γn T satp0 Ex Cond c0 := by
  intro Hrd Hrdok
  have L := wpCmvC4 i cid cpu γm γp γn σi T satp0 hmode hasid hppn armedR Ex stackOwn Cond
    Htext Hflow pc rd rs2 m n b p Hrd Hrdok
  unfold cap4 instr4 at L
  unfold capW4 pcW4 goalW4 instrW4 cap4 instr4
  iintro Hc Hp ⟨%Hi, %_⟩ Hk
  have hs : regidx.Regidx rs2 ≠ regidx.Regidx 4#5 := Hi.2.2.1.2
  have hne : rs2 ≠ 4#5 := fun h => hs (by rw [h])
  rw [AxCondM4.rgetCpu c0 cid m rs2 hne]
  ihave Hk := AxSymMem3.wpNextSelf b p c0 _ $$ Hk
  iapply L $$ Hc Hp %Hi
  iapply wpNext_intro
  iintro %_
  iexact Hk

include hmode hasid hppn Htext Hflow Hloc HG Hdmap ldRule CondAnd HnoRmwReg in
/-- Rocq `w_cldsp4`: `c.ldsp rd, uimm(sp)`. -/
theorem wCldsp4 (c0 : CPU) (p pc : BitVec 64) (uimm : BitVec 6) (rd : BitVec 5)
    (m : RegMap) (n : Nat) (v : BitVec 64) (b : Bool) {dqm : DFrac} :
    rd.toNat ≠ 0 → MachCSL.rdOk rd →
    ⊢ capW4 γm γn stackOwn c0 m n b p -∗ pcW4 γp c0 pc -∗
      instrW4 σi T satp0 Ex pc true
        (.LOAD (zero_extend (m := 12) (uimm +++ 0b000#3), sp, .Regidx rd, false, 8)) -∗
      wpt (m 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3)) dqm v -∗
      wpNext b p c0 (fun c1 => iprop(
        capW4 γm γn stackOwn c1 (m.set rd v) n b p -∗ pcW4 γp c1 (pc + 2#64) -∗
        wpt (m 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3)) dqm v -∗
        goalW4 i cid cpu γm γp γn T satp0 Ex Cond c1)) -∗
      goalW4 i cid cpu γm γp γn T satp0 Ex Cond c0 := by
  intro Hrd Hrdok
  have L := wpCldspC4 i cid cpu γm γp γn σi T satp0 hmode hasid hppn armedR Ex stackOwn Cond
    Htext Hflow Hloc G HG dreg damo Hdmap wpt ldRule CondAnd HnoRmwReg pc uimm rd m n v b p
    (dqm := dqm) Hrd Hrdok
  unfold cap4 at L
  unfold capW4 pcW4 goalW4 instrW4 cap4
  iintro Hc Hp ⟨Hi, %_⟩ Hw Hk
  ihave Hk := AxSymMem3.wpNextSelf b p c0 _ $$ Hk
  iapply L $$ Hc Hp Hi Hw
  iapply wpNext_intro
  iintro %_
  iexact Hk

include hmode hasid hppn Htext Hflow SFPop in
/-- Rocq `w_c16_4`: `c.addi16sp sp, imm`. -/
theorem wC164 (c0 : CPU) (p pc : BitVec 64) (imm6 : BitVec 6) (m : RegMap) (n k : Nat) (b : Bool) :
    m 2#5 = paStk (m 2#5 + sign_extend (m := 64) (caddi16spImm imm6)) k →
    ⊢ capW4 γm γn stackOwn c0 m n b p -∗ pcW4 γp c0 pc -∗
      instrW4 σi T satp0 Ex pc true (.ITYPE (caddi16spImm imm6, sp, sp, .ADDI)) -∗
      stackOwn (m 2#5 + sign_extend (m := 64) (caddi16spImm imm6)) k -∗
      wpNext b p c0 (fun c1 => iprop(
        capW4 γm γn stackOwn c1
          (m.set 2#5 (m 2#5 + sign_extend (m := 64) (caddi16spImm imm6))) (n + k) b p -∗
        pcW4 γp c1 (pc + 2#64) -∗ goalW4 i cid cpu γm γp γn T satp0 Ex Cond c1)) -∗
      goalW4 i cid cpu γm γp γn T satp0 Ex Cond c0 := by
  intro Hw
  have L := wpCaddi16spPopC4 i cid cpu γm γp γn σi T satp0 hmode hasid hppn armedR Ex stackOwn
    Cond Htext Hflow stackOwn SFPop pc imm6 m n k b p Hw
  unfold cap4 at L
  unfold capW4 pcW4 goalW4 instrW4 cap4
  iintro Hc Hp ⟨Hi, %_⟩ Hs Hk
  ihave Hk := AxSymMem3.wpNextSelf b p c0 _ $$ Hk
  iapply L $$ Hc Hp Hi Hs
  iapply wpNext_intro
  iintro %_
  iexact Hk

/-! ## The interface slots (AxLeafS5's shape, later-free) -/

include hmode hasid hppn Htext Hflow Hloc HG Hdmap sdlkRule in
/-- Rocq `w_sdlk4`: release+0x12, `sd zero,16(s1)` — the owner clears `lk->cpu` (the
`wp_s_sd_zero_lkcpu_release_gen` slot); NO gate: s1 is exact (`instr4`'s `exBase`). -/
theorem wSdlk4 (c : CPU) (k : KCtx) (_hsie : k.sie = false) (pc : BitVec 64) (is_rvc : Bool)
    (imm : BitVec 12) (rs1 : BitVec 5) (γ : GName) (lk : BitVec 64) (s : String) (R : Pay)
    (D : IProp GF) [Timeless D] (Tc : IProp GF) (_hrefute : ⊢ Tc -∗ D -∗ (False : IProp GF))
    (haddr : k.rget c rs1 + BitVec.signExtend 64 imm = lk + 16#64) :
    instrW4 σi T satp0 Ex pc is_rvc (instruction.STORE (imm, regidx.Regidx 0#5, regidx.Regidx rs1, 8)) ∗
      AxRelease4.kctxW4 γm γn stackOwn held kt c k ∗ pcW4 γp c pc ∗ lockOpenable γ lk s R D ∗ Tc ∗
      lockedCore γ c ∗
      wpNext k.sie k.proc c (fun cpu' =>
        iprop(AxRelease4.kctxW4 γm γn stackOwn held kt cpu' k -∗ pcW4 γp cpu' (pc + instrLen is_rvc) -∗
          (lockedPre γ c ∗ Tc) -∗ goalW4 i cid cpu γm γp γn T satp0 Ex Cond cpu'))
      ⊢ goalW4 i cid cpu γm γp γn T satp0 Ex Cond c := by
  cases is_rvc
  · dsimp only [instrLen]
    unfold instrW4 AxRelease4.kctxW4 capW4 pcW4 goalW4
    iintro ⟨⟨Hi, %_⟩, ⟨Hs, Hheld, #Hkt⟩, Hp, Hlo, HT, Hlc, Hcont⟩
    ihave %Hi4 := instr4Nrvc σi T satp0 armedR Ex pc _ $$ Hi
    have hb : rs1 ≠ 4#5 := fun h => Hi4.2.2.2.1.1 imm 0#5 rs1 8 rfl (by rw [h])
    have hpa : rget cid k.regs rs1 + sign_extend (m := 64) imm = lk + 16#64 := by
      rw [AxCondM4.rgetCpu cid c k.regs rs1 hb]; exact haddr
    have Hrule : ∀ cl : WmClass, ⊢ ⌜armedR pc → cl = .WCrel⌝ -∗
        iprop(lockOpenable γ lk s R D ∗ lockedCore γ c) -∗
        ⌜dreg (paZ (rget cid k.regs rs1 + sign_extend (m := 64) imm)) 8⌝ ∗
        FstM rvwmoCatConsistent (dk3 (paZ (rget cid k.regs rs1 + sign_extend (m := 64) imm)) 8) i
          (fun _ data => iprop(⌜(exactAt Ex pc 0#5 → data = stBytes 8 (rget cid k.regs 0#5)) ∧
            ((0#5 : BitVec 5).toNat = 0 → data = stBytes 8 0#64)⌝ -∗ lockedPre γ c)) := by
      intro cl
      rw [hpa]
      iintro _ ⟨Hlo, Hlc⟩
      iapply (sdlkRule c cl γ lk s R D
        (fun data => (exactAt Ex pc 0#5 → data = stBytes 8 (rget cid k.regs 0#5)) ∧
          ((0#5 : BitVec 5).toNat = 0 → data = stBytes 8 0#64))
        (fun _ h => h.2 rfl)) $$ Hlo Hlc
    have HS := wpStoreC4 i cid cpu γm γp γn σi T satp0 hmode hasid hppn armedR Ex stackOwn Cond
      Htext Hflow Hloc G HG dreg damo Hdmap pc 0#5 rs1 imm 8 k.regs k.avail k.sie k.proc
      iprop(lockOpenable γ lk s R D ∗ lockedCore γ c) (lockedPre γ c)
      (Or.inr (Or.inr (Or.inr rfl))) ⟨by decide, by decide⟩ Hrule
    unfold cap4 at HS
    unfold cap4
    ihave Hi := (show ⊢ instr4 (GF := GF) σi T satp0 armedR Ex pc false
        (instruction.STORE (imm, regidx.Regidx 0#5, regidx.Regidx rs1, 8)) from by
      unfold instr4; exact pure_intro ⟨.inl ⟨rfl, Hi4.1, Hi4.2.1⟩, Hi4.2.2.1, Hi4.2.2.2.1,
        Hi4.2.2.2.2.1, Hi4.2.2.2.2.2⟩)
    ihave Hk := AxSymMem3.wpNextSelf k.sie k.proc c _ $$ Hcont
    iapply HS $$ Hs Hp Hi [Hlo Hlc]
    · isplitl [Hlo]
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
  · unfold instrW4
    iintro ⟨⟨-, %Hw⟩, -⟩
    exact absurd (Hw.1 (Or.inl ⟨imm, rs1, 8, rfl⟩)) (by decide)

include hmode hasid hppn Htext Hflow Hloc HG in
/-- Rocq `w_fence4`: release+0x16, `fence rw,w` — arms the flag (the `wp_s_fence_rw_w`
slot). -/
theorem wFence4 (c : CPU) (k : KCtx) (pc : BitVec 64) (is_rvc : Bool) :
    instrW4 σi T satp0 Ex pc is_rvc
        (instruction.FENCE (0#4, 3#4, 1#4, regidx.Regidx 0#5, regidx.Regidx 0#5)) ∗
      AxRelease4.kctxW4 γm γn stackOwn held kt c k ∗ pcW4 γp c pc ∗
      wpNext k.sie k.proc c (fun cpu' =>
        iprop(AxRelease4.kctxW4 γm γn stackOwn held kt cpu' k -∗ pcW4 γp cpu' (pc + instrLen is_rvc) -∗
          goalW4 i cid cpu γm γp γn T satp0 Ex Cond cpu'))
      ⊢ goalW4 i cid cpu γm γp γn T satp0 Ex Cond c := by
  cases is_rvc
  · dsimp only [instrLen]
    have HF := wpFenceC4 i cid cpu γm γp γn σi T satp0 hmode hasid hppn armedR Ex stackOwn Cond
      Htext Hflow Hloc G HG pc k.regs k.avail k.sie k.proc
    unfold cap4 fenceRwWIns at HF
    unfold instrW4 AxRelease4.kctxW4 capW4 pcW4 goalW4 cap4
    iintro ⟨⟨Hi, %_⟩, ⟨Hs, Hheld, #Hkt⟩, Hp, Hcont⟩
    ihave Hk := AxSymMem3.wpNextSelf k.sie k.proc c _ $$ Hcont
    iapply HF $$ Hs Hp Hi
    iapply wpNext_intro
    iintro %_ Hs' Hp'
    iapply Hk $$ [Hs' Hheld] Hp'
    isplitl [Hs']
    · iexact Hs'
    · isplitl [Hheld]
      · iexact Hheld
      · iexact Hkt
  · unfold instrW4
    iintro ⟨⟨-, %Hw⟩, -⟩
    exact absurd (Hw.1 (Or.inr rfl)) (by decide)

include hmode hasid hppn Htext Hflow Hloc HG Hdmap swlkRule in
/-- Rocq `w_swfin4`: release+0x1a, `sw zero,0(s1)` — THE RELEASE STORE (class `WCrel`; the
`wp_s_sw_zero_release_gen` slot). -/
theorem wSwfin4 (c : CPU) (k : KCtx) (_hsie : k.sie = false) (pc : BitVec 64) (is_rvc : Bool)
    (imm : BitVec 12) (rs1 : BitVec 5) (γ : GName) (lk : BitVec 64) (s : String) (R : Pay)
    (hR : payOk R) (D : IProp GF) [Timeless D] (Tc : IProp GF)
    (_hrefute : ⊢ Tc -∗ D -∗ (False : IProp GF))
    (haddr : k.rget c rs1 + BitVec.signExtend 64 imm = lk) :
    instrW4 σi T satp0 Ex pc is_rvc (instruction.STORE (imm, regidx.Regidx 0#5, regidx.Regidx rs1, 4)) ∗
      AxRelease4.kctxW4 γm γn stackOwn held kt c k ∗ pcW4 γp c pc ∗ lockOpenable γ lk s R D ∗ Tc ∗
      lockedPre γ c ∗ lockCtxHeld ∗ payAt R ∗
      wpNext k.sie k.proc c (fun cpu' =>
        iprop(AxRelease4.kctxW4 γm γn stackOwn held kt cpu' (k.withLocks (k.locks.filter (fun x => x ≠ s))) -∗
          pcW4 γp cpu' (pc + instrLen is_rvc) -∗ ⌜s ∈ k.locks⌝ -∗ Tc -∗
          goalW4 i cid cpu γm γp γn T satp0 Ex Cond cpu'))
      ⊢ goalW4 i cid cpu γm γp γn T satp0 Ex Cond c := by
  cases is_rvc
  · dsimp only [instrLen]
    unfold instrW4 AxRelease4.kctxW4 capW4 pcW4 goalW4
    dsimp only [KCtx.withLocks]
    iintro ⟨⟨Hi, %_⟩, ⟨Hs, Hheld, #Hkt⟩, Hp, Hlo, HT, Hlp, Hctx, HR, Hcont⟩
    ihave %Hi4 := instr4Nrvc σi T satp0 armedR Ex pc _ $$ Hi
    have hb : rs1 ≠ 4#5 := fun h => Hi4.2.2.2.1.1 imm 0#5 rs1 4 rfl (by rw [h])
    have hpa : rget cid k.regs rs1 + sign_extend (m := 64) imm = lk := by
      rw [AxCondM4.rgetCpu cid c k.regs rs1 hb]; exact haddr
    have Harm : armedR pc := Hi4.2.2.1 ⟨imm, rs1, rfl⟩
    have Hrule : ∀ cl : WmClass, ⊢ ⌜armedR pc → cl = .WCrel⌝ -∗
        iprop(lockOpenable γ lk s R D ∗ lockedPre γ c ∗ payAt R ∗ lockCtxHeld ∗ held c k.locks) -∗
        ⌜dreg (paZ (rget cid k.regs rs1 + sign_extend (m := 64) imm)) 4⌝ ∗
        FstM rvwmoCatConsistent (dk3 (paZ (rget cid k.regs rs1 + sign_extend (m := 64) imm)) 4) i
          (fun _ data => iprop(⌜(exactAt Ex pc 0#5 → data = stBytes 4 (rget cid k.regs 0#5)) ∧
            ((0#5 : BitVec 5).toNat = 0 → data = stBytes 4 0#64)⌝ -∗
            held c (k.locks.filter (fun x => x ≠ s)) ∗ ⌜s ∈ k.locks⌝)) := by
      intro cl
      rw [hpa]
      iintro %Hc ⟨Hlo, Hlp, HR, Hctx, Hh⟩
      iapply (swlkRule c cl γ lk s R D k.locks
        (fun data => (exactAt Ex pc 0#5 → data = stBytes 4 (rget cid k.regs 0#5)) ∧
          ((0#5 : BitVec 5).toNat = 0 → data = stBytes 4 0#64))
        (fun _ h => h.2 rfl) (Hc Harm) hR) $$ Hlo Hlp HR Hctx Hh
    have HS := wpStoreC4 i cid cpu γm γp γn σi T satp0 hmode hasid hppn armedR Ex stackOwn Cond
      Htext Hflow Hloc G HG dreg damo Hdmap pc 0#5 rs1 imm 4 k.regs k.avail k.sie k.proc
      iprop(lockOpenable γ lk s R D ∗ lockedPre γ c ∗ payAt R ∗ lockCtxHeld ∗ held c k.locks)
      iprop(held c (k.locks.filter (fun x => x ≠ s)) ∗ ⌜s ∈ k.locks⌝)
      (Or.inr (Or.inr (Or.inl rfl))) ⟨by decide, by decide⟩ Hrule
    unfold cap4 at HS
    unfold cap4
    ihave Hi := (show ⊢ instr4 (GF := GF) σi T satp0 armedR Ex pc false
        (instruction.STORE (imm, regidx.Regidx 0#5, regidx.Regidx rs1, 4)) from by
      unfold instr4; exact pure_intro ⟨.inl ⟨rfl, Hi4.1, Hi4.2.1⟩, Hi4.2.2.1, Hi4.2.2.2.1,
        Hi4.2.2.2.2.1, Hi4.2.2.2.2.2⟩)
    ihave Hk := AxSymMem3.wpNextSelf k.sie k.proc c _ $$ Hcont
    iapply HS $$ Hs Hp Hi [Hlo Hlp HR Hctx Hheld]
    · isplitl [Hlo]
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
  · unfold instrW4
    iintro ⟨⟨-, %Hw⟩, -⟩
    exact absurd (Hw.1 (Or.inl ⟨imm, rs1, 4, rfl⟩)) (by decide)

include hmode hasid hppn Htext Hflow in
/-- (Lean-only, deviation 1) The `wp_s_add` slot, REAL: Rocq's `w_cmv4` (`c.mv rd, rs2` =
`add rd, x0, rs2`; `instrW4`'s `add` fact, deviation 2, rules out the other shapes). -/
theorem AxRelease4.wAdd4 (c : CPU) (k : KCtx) (pc : BitVec 64) (is_rvc : Bool) (rd rs1 rs2 : BitVec 5)
    (hrd : MachCSL.rdOk rd) :
    instrW4 σi T satp0 Ex pc is_rvc
        (instruction.RTYPE (regidx.Regidx rs2, regidx.Regidx rs1, regidx.Regidx rd, rop.ADD)) ∗
      AxRelease4.kctxW4 γm γn stackOwn held kt c k ∗ pcW4 γp c pc ∗
      wpNext k.sie k.proc c (fun cpu' =>
        iprop(AxRelease4.kctxW4 γm γn stackOwn held kt cpu' (k.setReg rd (k.rget cpu' rs1 + k.rget cpu' rs2)) -∗
        pcW4 γp cpu' (pc + instrLen is_rvc) -∗ goalW4 i cid cpu γm γp γn T satp0 Ex Cond cpu'))
      ⊢ goalW4 i cid cpu γm γp γn T satp0 Ex Cond c := by
  unfold instrW4
  iintro ⟨⟨Hi, %Hx⟩, Hk, Hp, Hcont⟩
  obtain ⟨rfl, rfl⟩ := Hx.2 rs2 rs1 rd rfl
  have Hrd : rd.toNat ≠ 0 := fun h => hrd.1 (BitVec.eq_of_toNat_eq (by simpa using h))
  have L := wpCmvC4 i cid cpu γm γp γn σi T satp0 hmode hasid hppn armedR Ex stackOwn Cond
    Htext Hflow pc rd rs2 k.regs k.avail k.sie k.proc Hrd hrd
  unfold cap4 instr4 at L
  unfold AxRelease4.kctxW4 capW4 pcW4 goalW4 cap4 instr4
  icases Hi with %Hi
  have hs : regidx.Regidx rs2 ≠ regidx.Regidx 4#5 := Hi.2.2.1.2
  have hne : rs2 ≠ 4#5 := fun h => hs (by rw [h])
  have h0 : ∀ c' : CPU, k.rget c' 0#5 = 0#64 := fun c' => rget_zero c' k.regs
  have h2 : ∀ c' : CPU, k.rget c' rs2 = rget cid k.regs rs2 :=
    fun c' => AxCondM4.rgetCpu c' cid k.regs rs2 hne
  simp only [h0, h2, KCtx.setReg_regs, KCtx.setReg_avail, KCtx.setReg_sie,
    KCtx.setReg_locks]
  dsimp only [instrLen]
  icases Hk with ⟨Hs, Hheld, #Hkt⟩
  ihave Hk := AxSymMem3.wpNextSelf k.sie k.proc c _ $$ Hcont
  iapply L $$ Hs Hp %Hi
  iapply wpNext_intro
  iintro %_ Hs' Hp'
  iapply Hk $$ [Hs' Hheld] Hp'
  isplitl [Hs']
  · iexact Hs'
  · isplitl [Hheld]
    · iexact Hheld
    · iexact Hkt

/-! ## The frame macros (Lean-only slots; Rocq's push / c.sdsp / c.addi4spn and c.ldsp /
c.addi16sp leaves REAL, `c.ret` and `stack_own_slots` λ-bound) -/

/- Rocq's `stack_own_slots` (λ-bound in `release_wpd4`) and the `c.ret` slot `w_cret` at
surface v4 (λ-bound in `release_wpd4`; the Lean epilogue macro bundles it) -/
variable (stackOwnSlots : ∀ (sp : PAddr) (n : Nat), stackOwn sp n ⊣⊢
  [∗list] j ∈ List.range' 1 n, ∃ w : BitVec 64, wpt (paStk sp j) (DFrac.own 1) w)
variable (wCret4 : ∀ (c0 : CPU) (p pc : BitVec 64) (ra : BitVec 5) (m : RegMap) (n : Nat) (b : Bool),
  ra.toNat ≠ 0 →
  ⊢ capW4 γm γn stackOwn c0 m n b p -∗ pcW4 γp c0 pc -∗
    instrW4 σi T satp0 Ex pc true (.JALR (0#12, .Regidx ra, zreg)) -∗
    wpNext b p c0 (fun c1 => iprop(
      capW4 γm γn stackOwn c1 m n b p -∗ pcW4 γp c1 (jumpPc (rget c0 m ra)) -∗
      goalW4 i cid cpu γm γp γn T satp0 Ex Cond c1)) -∗
    goalW4 i cid cpu γm γp γn T satp0 Ex Cond c0)

theorem AxRelease4.paStkAdd (x : PAddr) (j : Nat) :
    paStk x j = x + -(8#64 * BitVec.ofNat 64 j) := by
  unfold paStk; exact BitVec.sub_eq_add_neg _ _

theorem AxRelease4.spEq : sp = regidx.Regidx 2#5 := rfl
theorem AxRelease4.zregEq : zreg = regidx.Regidx 0#5 := rfl

omit [InvGS_gen hlc GF] [AxirisG GF] [Axpol] [GhostVarG GF RegMap]
  [GhostVarG GF (BitVec 64 × Bool)] [GhostVarG GF Nat] in
/-- (Lean-only) four stack slots, unrolled. -/
theorem AxRelease4.slots4 (Φ : Nat → IProp GF) :
    ([∗list] j ∈ List.range' 1 4, Φ j) ⊣⊢ Φ 1 ∗ Φ 2 ∗ Φ 3 ∗ Φ 4 ∗ emp :=
  ⟨.rfl, .rfl⟩

omit [InvGS_gen hlc GF] [AxirisG GF] [Axpol] [GhostVarG GF (BitVec 64 × Bool)] in
/-- (Lean-only) `cap4`'s interrupt bit is off. -/
theorem AxRelease4.capW4Sie (c0 : CPU) (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) :
    capW4 γm γn stackOwn c0 m n b p ⊢ ⌜b = false⌝ ∗ capW4 γm γn stackOwn c0 m n b p := by
  unfold capW4 cap4
  iintro ⟨%hb, H⟩
  isplitr
  · ipureintro; exact hb
  · isplitr
    · ipureintro; exact hb
    · iexact H

include hmode hasid hppn Htext Hflow Hloc HG Hdmap stRule in
/-- (Lean-only) `wCsdsp4` at a named slot address. -/
theorem AxRelease4.wCsdspAt (c0 : CPU) (p pc : BitVec 64) (uimm : BitVec 6) (rs2 : BitVec 5)
    (m : RegMap) (n : Nat) (vold : BitVec 64) (b : Bool) (a : PAddr)
    (ha : m 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3) = a) :
    ⊢ capW4 γm γn stackOwn c0 m n b p -∗ pcW4 γp c0 pc -∗
      instrW4 σi T satp0 Ex pc true
        (.STORE (zero_extend (m := 12) (uimm +++ 0b000#3), .Regidx rs2, sp, 8)) -∗
      wpt a (.own 1) vold -∗
      wpNext b p c0 (fun c1 => iprop(
        capW4 γm γn stackOwn c1 m n b p -∗ pcW4 γp c1 (pc + 2#64) -∗
        wpt a (.own 1) (rget c0 m rs2) -∗ goalW4 i cid cpu γm γp γn T satp0 Ex Cond c1)) -∗
      goalW4 i cid cpu γm γp γn T satp0 Ex Cond c0 := by
  subst ha
  exact wCsdsp4 i cid cpu γm γp γn σi T satp0 hmode hasid hppn Ex Cond Htext Hflow Hloc G HG
    dreg damo Hdmap stackOwn wpt stRule c0 p pc uimm rs2 m n vold b

include hmode hasid hppn Htext Hflow Hloc HG Hdmap ldRule CondAnd HnoRmwReg in
/-- (Lean-only) `wCldsp4` at a named slot address. -/
theorem AxRelease4.wCldspAt (c0 : CPU) (p pc : BitVec 64) (uimm : BitVec 6) (rd : BitVec 5)
    (m : RegMap) (n : Nat) (v : BitVec 64) (b : Bool) (dqm : DFrac) (a : PAddr)
    (ha : m 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3) = a) :
    rd.toNat ≠ 0 → MachCSL.rdOk rd →
    ⊢ capW4 γm γn stackOwn c0 m n b p -∗ pcW4 γp c0 pc -∗
      instrW4 σi T satp0 Ex pc true
        (.LOAD (zero_extend (m := 12) (uimm +++ 0b000#3), sp, .Regidx rd, false, 8)) -∗
      wpt a dqm v -∗
      wpNext b p c0 (fun c1 => iprop(
        capW4 γm γn stackOwn c1 (m.set rd v) n b p -∗ pcW4 γp c1 (pc + 2#64) -∗
        wpt a dqm v -∗ goalW4 i cid cpu γm γp γn T satp0 Ex Cond c1)) -∗
      goalW4 i cid cpu γm γp γn T satp0 Ex Cond c0 := by
  subst ha
  exact wCldsp4 i cid cpu γm γp γn σi T satp0 hmode hasid hppn Ex Cond Htext Hflow Hloc G HG
    dreg damo Hdmap stackOwn wpt ldRule CondAnd HnoRmwReg c0 p pc uimm rd m n v b (dqm := dqm)

include hmode hasid hppn Htext Hflow SFPop in
/-- (Lean-only) `wC164` at a named new stack pointer and budget. -/
theorem AxRelease4.wC16At (c0 : CPU) (p pc : BitVec 64) (imm6 : BitVec 6) (m : RegMap) (n k : Nat)
    (b : Bool) (a : PAddr) (n' : Nat)
    (ha : m 2#5 + sign_extend (m := 64) (caddi16spImm imm6) = a) (hn : n + k = n') :
    m 2#5 = paStk a k →
    ⊢ capW4 γm γn stackOwn c0 m n b p -∗ pcW4 γp c0 pc -∗
      instrW4 σi T satp0 Ex pc true (.ITYPE (caddi16spImm imm6, sp, sp, .ADDI)) -∗
      stackOwn a k -∗
      wpNext b p c0 (fun c1 => iprop(
        capW4 γm γn stackOwn c1 (m.set 2#5 a) n' b p -∗
        pcW4 γp c1 (pc + 2#64) -∗ goalW4 i cid cpu γm γp γn T satp0 Ex Cond c1)) -∗
      goalW4 i cid cpu γm γp γn T satp0 Ex Cond c0 := by
  subst ha hn
  exact wC164 i cid cpu γm γp γn σi T satp0 hmode hasid hppn Ex Cond Htext Hflow stackOwn SFPop
    c0 p pc imm6 m n k b

include hmode hasid hppn Htext Hflow Hloc HG Hdmap SFPush stRule stackOwnSlots in
/-- (Lean-only, deviation 1) The `wp_prologue4s1` slot, REAL: Rocq's `w_push4`, `w_csdsp4` ×3,
`w_c4spn4` in sequence (`c.addi sp,-32; c.sdsp ra,24(sp); c.sdsp s0,16(sp); c.sdsp s1,8(sp);
c.addi4spn s0,sp,32`), the four pushed slots opened by `stack_own_slots`. -/
theorem AxRelease4.wPrologue4 (c : CPU) (k : KCtx) (hsie : k.sie = false) (pc : BitVec 64)
    (hK : 4 ≤ k.avail) :
    instrW4 σi T satp0 Ex pc true (instruction.ITYPE (4064#12, regidx.Regidx 2#5, regidx.Regidx 2#5, iop.ADDI)) ∗
    instrW4 σi T satp0 Ex (pc + 2#64) true (instruction.STORE (24#12, regidx.Regidx 1#5, regidx.Regidx 2#5, 8)) ∗
    instrW4 σi T satp0 Ex (pc + 4#64) true (instruction.STORE (16#12, regidx.Regidx 8#5, regidx.Regidx 2#5, 8)) ∗
    instrW4 σi T satp0 Ex (pc + 6#64) true (instruction.STORE (8#12, regidx.Regidx 9#5, regidx.Regidx 2#5, 8)) ∗
    instrW4 σi T satp0 Ex (pc + 8#64) true (instruction.ITYPE (32#12, regidx.Regidx 2#5, regidx.Regidx 8#5, iop.ADDI)) ∗
    AxRelease4.kctxW4 γm γn stackOwn held kt c k ∗ pcW4 γp c pc ∗
    (AxRelease4.kctxW4 γm γn stackOwn held kt c ((k.pushed 4).withRegs
          ((k.regs.set 2#5 (k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64)).set 8#5 (k.regs 2#5))) -∗
        pcW4 γp c (pc + 10#64) -∗
        AxRelease4.frameW4 wpt (k.regs 2#5) (k.regs 1#5) (k.regs 8#5) (k.regs 9#5) -∗
        goalW4 i cid cpu γm γp γn T satp0 Ex Cond c)
    ⊢ goalW4 i cid cpu γm γp γn T satp0 Ex Cond c := by
  have e4 : pc + 2#64 + 2#64 = pc + 4#64 := by bv_decide
  have e6 : pc + 2#64 + 2#64 + 2#64 = pc + 6#64 := by bv_decide
  have e8 : pc + 2#64 + 2#64 + 2#64 + 2#64 = pc + 8#64 := by bv_decide
  have e10 : pc + 2#64 + 2#64 + 2#64 + 2#64 + 2#64 = pc + 10#64 := by bv_decide
  rw [← e4, ← e6, ← e8, ← e10]
  have c64 : sign_extend (m := 64) (sign_extend (m := 12) (32#6 : BitVec 6)) =
      0xFFFFFFFFFFFFFFE0#64 := by decide
  have c12 : sign_extend (m := 12) (32#6 : BitVec 6) = 4064#12 := by decide
  have hw1 : k.regs 2#5 + sign_extend (m := 64) (sign_extend (m := 12) (32#6 : BitVec 6)) =
      paStk (k.regs 2#5) 4 := by
    rw [c64, AxRelease4.paStkAdd]; exact congrArg (k.regs 2#5 + ·) (by decide)
  have L1 := wPush4 i cid cpu γm γp γn σi T satp0 hmode hasid hppn Ex Cond Htext Hflow stackOwn
    SFPush c k.proc pc 32#6 k.regs k.avail 4 k.sie hK hw1
  rw [c64, c12] at L1
  have hv : ∀ r : BitVec 5, r ≠ 0#5 → r ≠ 4#5 → r ≠ 2#5 →
      rget c (k.regs.set 2#5 (k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64)) r = k.regs r :=
    fun r h0 h4 h2 => by rw [rget_ne c _ r h0 h4, RegMap.set_other _ _ _ _ h2]
  have ha : ∀ (u : BitVec 6) (j : Nat),
      0xFFFFFFFFFFFFFFE0#64 + zero_extend (m := 64) (u +++ 0b000#3) = -(8#64 * BitVec.ofNat 64 j) →
      (k.regs.set 2#5 (k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64)) 2#5 +
        zero_extend (m := 64) (u +++ 0b000#3) = paStk (k.regs 2#5) j := by
    intro u j h; rw [RegMap.set_same, AxRelease4.paStkAdd, BitVec.add_assoc, h]
  have ze24 : zero_extend (m := 12) ((3#6 : BitVec 6) +++ 0b000#3) = 24#12 := by decide
  have ze16 : zero_extend (m := 12) ((2#6 : BitVec 6) +++ 0b000#3) = 16#12 := by decide
  have ze8 : zero_extend (m := 12) ((1#6 : BitVec 6) +++ 0b000#3) = 8#12 := by decide
  unfold AxRelease4.kctxW4 AxRelease4.frameW4
  simp only [KCtx.withRegs_regs, KCtx.withRegs_avail, KCtx.withRegs_sie, KCtx.withRegs_proc,
    KCtx.withRegs_locks, KCtx.pushed_avail, KCtx.pushed_sie, KCtx.pushed_proc, KCtx.pushed_locks]
  iintro ⟨Hi0, Hi2, Hi4, Hi6, Hi8, ⟨Hc, Hheld, #Hkt⟩, Hp, Hcont⟩
  -- c.addi sp,-32
  iapply L1 $$ Hc Hp Hi0
  iapply wpNext_intro_pin
  iintro %c1 %hc1
  rw [hc1 (Or.inl hsie)]
  iintro Hc Hs Hp
  ihave Hs := (stackOwnSlots (k.regs 2#5) 4).1 $$ Hs
  ihave Hs := (AxRelease4.slots4 _).1 $$ Hs
  icases Hs with ⟨⟨%w1, Hw1⟩, ⟨%w2, Hw2⟩, ⟨%w3, Hw3⟩, Hw4, -⟩
  -- c.sdsp ra,24(sp)
  have L2 := AxRelease4.wCsdspAt i cid cpu γm γp γn σi T satp0 hmode hasid hppn Ex Cond Htext
    Hflow Hloc G HG dreg damo Hdmap stackOwn wpt stRule c k.proc (pc + 2#64) 3#6 1#5
    (k.regs.set 2#5 (k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64)) (k.avail - 4) w1 k.sie
    (paStk (k.regs 2#5) 1) (ha 3#6 1 (by decide))
  rw [ze24, AxRelease4.spEq, hv 1#5 (by decide) (by decide) (by decide)] at L2
  iapply L2 $$ Hc Hp Hi2 Hw1
  iapply wpNext_intro_pin
  iintro %c2 %hc2
  rw [hc2 (Or.inl hsie)]
  iintro Hc Hp Hw1
  -- c.sdsp s0,16(sp)
  have L3 := AxRelease4.wCsdspAt i cid cpu γm γp γn σi T satp0 hmode hasid hppn Ex Cond Htext
    Hflow Hloc G HG dreg damo Hdmap stackOwn wpt stRule c k.proc (pc + 2#64 + 2#64) 2#6 8#5
    (k.regs.set 2#5 (k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64)) (k.avail - 4) w2 k.sie
    (paStk (k.regs 2#5) 2) (ha 2#6 2 (by decide))
  rw [ze16, AxRelease4.spEq, hv 8#5 (by decide) (by decide) (by decide)] at L3
  iapply L3 $$ Hc Hp Hi4 Hw2
  iapply wpNext_intro_pin
  iintro %c3 %hc3
  rw [hc3 (Or.inl hsie)]
  iintro Hc Hp Hw2
  -- c.sdsp s1,8(sp)
  have L4 := AxRelease4.wCsdspAt i cid cpu γm γp γn σi T satp0 hmode hasid hppn Ex Cond Htext
    Hflow Hloc G HG dreg damo Hdmap stackOwn wpt stRule c k.proc (pc + 2#64 + 2#64 + 2#64) 1#6 9#5
    (k.regs.set 2#5 (k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64)) (k.avail - 4) w3 k.sie
    (paStk (k.regs 2#5) 3) (ha 1#6 3 (by decide))
  rw [ze8, AxRelease4.spEq, hv 9#5 (by decide) (by decide) (by decide)] at L4
  iapply L4 $$ Hc Hp Hi6 Hw3
  iapply wpNext_intro_pin
  iintro %c4 %hc4
  rw [hc4 (Or.inl hsie)]
  iintro Hc Hp Hw3
  -- c.addi4spn s0,sp,32
  have L5 := wC4spn4 i cid cpu γm γp γn σi T satp0 hmode hasid hppn Ex Cond Htext Hflow stackOwn
    c k.proc (pc + 2#64 + 2#64 + 2#64 + 2#64) (cregidx.Cregidx 0#3) 8#8 8#5
    (k.regs.set 2#5 (k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64)) (k.avail - 4) k.sie rfl (by decide)
    (by decide)
  have c4 : caddi4spnImm 8#8 = 32#12 := by decide
  have hm5 : (k.regs.set 2#5 (k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64)).set 8#5
      ((k.regs.set 2#5 (k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64)) 2#5 + sign_extend (m := 64) (32#12 : BitVec 12)) =
      (k.regs.set 2#5 (k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64)).set 8#5 (k.regs 2#5) := by
    rw [RegMap.set_same, BitVec.add_assoc,
      show (0xFFFFFFFFFFFFFFE0#64 : BitVec 64) + sign_extend (m := 64) (32#12 : BitVec 12) = 0#64
        from by decide, BitVec.add_zero]
  rw [c4, AxRelease4.spEq, hm5] at L5
  iapply L5 $$ Hc Hp Hi8
  iapply wpNext_intro_pin
  iintro %c5 %hc5
  rw [hc5 (Or.inl hsie)]
  iintro Hc Hp
  iapply Hcont $$ [Hc Hheld] Hp [Hw1 Hw2 Hw3 Hw4]
  · isplitl [Hc]
    · iexact Hc
    · isplitl [Hheld]
      · iexact Hheld
      · iexact Hkt
  · isplitl [Hw1]
    · iexact Hw1
    · isplitl [Hw2]
      · iexact Hw2
      · isplitl [Hw3]
        · iexact Hw3
        · iexact Hw4

include hmode hasid hppn Htext Hflow Hloc HG Hdmap SFPop ldRule CondAnd HnoRmwReg stackOwnSlots
  wCret4 in
/-- (Lean-only, deviation 1) The `wp_epilogue4s1_gen` slot, REAL up to `c.ret`: Rocq's `w_cldsp4`
×3 and `w_c16_4` in sequence (`c.ldsp ra,24(sp); c.ldsp s0,16(sp); c.ldsp s1,8(sp);
c.addi16sp sp,32`, the four slots closed by `stack_own_slots`), then the λ-bound `c.ret` slot
`wCret4` (Rocq `w_cret`, λ-bound in `release_wpd4`). -/
theorem AxRelease4.wEpilogue4 (c : CPU) (k : KCtx) (pc : BitVec 64) (hK : 4 ≤ k.avail)
    (R : RegMap) (hR2 : R 2#5 = k.regs 2#5 + 0xFFFFFFFFFFFFFFE0#64) (ra s0 s1 : BitVec 64) :
    instrW4 σi T satp0 Ex pc true (instruction.LOAD (24#12, regidx.Regidx 2#5, regidx.Regidx 1#5, false, 8)) ∗
    instrW4 σi T satp0 Ex (pc + 2#64) true (instruction.LOAD (16#12, regidx.Regidx 2#5, regidx.Regidx 8#5, false, 8)) ∗
    instrW4 σi T satp0 Ex (pc + 4#64) true (instruction.LOAD (8#12, regidx.Regidx 2#5, regidx.Regidx 9#5, false, 8)) ∗
    instrW4 σi T satp0 Ex (pc + 6#64) true (instruction.ITYPE (32#12, regidx.Regidx 2#5, regidx.Regidx 2#5, iop.ADDI)) ∗
    instrW4 σi T satp0 Ex (pc + 8#64) true (instruction.JALR (0#12, regidx.Regidx 1#5, regidx.Regidx 0#5)) ∗
    AxRelease4.kctxW4 γm γn stackOwn held kt c ((k.pushed 4).withRegs R) ∗ pcW4 γp c pc ∗
    AxRelease4.frameW4 wpt (k.regs 2#5) ra s0 s1 ∗
    wpNext k.sie k.proc c (fun cpu' =>
        iprop(AxRelease4.kctxW4 γm γn stackOwn held kt cpu'
            (k.withRegs ((((R.set 1#5 ra).set 8#5 s0).set 9#5 s1).set 2#5 (k.regs 2#5))) -∗
          pcW4 γp cpu' (jumpPc ra) -∗ goalW4 i cid cpu γm γp γn T satp0 Ex Cond cpu'))
    ⊢ goalW4 i cid cpu γm γp γn T satp0 Ex Cond c := by
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
  -- c.ret (λ-bound)
  have hra : rget c ((((R.set 1#5 ra).set 8#5 s0).set 9#5 s1).set 2#5 (k.regs 2#5)) 1#5 = ra := by
    rw [rget_ne c _ 1#5 (by decide) (by decide), RegMap.set_other _ _ _ _ (by decide),
      RegMap.set_other _ _ _ _ (by decide), RegMap.set_other _ _ _ _ (by decide), RegMap.set_same]
  have L5 := wCret4 c k.proc (pc + 2#64 + 2#64 + 2#64 + 2#64) 1#5
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
  hlo sdlkRule swlkRule stackOwnSlots wCret4 in
/-- **THE REPLAY on surface v4** (Rocq `release_wpd4`): AxLeafS5's `wpReleaseGen` at `goalW4` /
`kctxW4` / `pcW4` / `instrW4` (NO `CondGate3` anywhere), the slots REAL: the frame prologue
(push, c.sdsp ×3, c.addi4spn), `c.mv` (`wp_s_add`), `sd zero,16(s1)`, `fence rw,w`,
`sw zero,0(s1)` (WCrel), the frame epilogue (c.ldsp ×3, c.addi16sp; `c.ret` = the λ-bound
`wCret4`) and the kernel-text projection; λ-bound (binders of this type): `locked`, `armP`,
`kctx_wf`, `textInstr`, `locked_cases`, `wp_s_jal`, `wp_s_branch`, the callees. -/
theorem releaseWpd4 :
    type_of% (AxLeafS5.wpReleaseGen (GF := GF) (Pay := Pay)
      (Goal := goalW4 i cid cpu γm γp γn T satp0 Ex Cond)
      (kctx := AxRelease4.kctxW4 γm γn stackOwn held kt) (pcIs := pcW4 γp)
      (instr := instrW4 σi T satp0 Ex)
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
      (wp_epilogue4s1_gen := AxRelease4.wEpilogue4 (i := i) (cid := cid) (cpu := cpu) (γm := γm)
        (γp := γp) (γn := γn) (σi := σi) (T := T) (satp0 := satp0) (hmode := hmode)
        (hasid := hasid) (hppn := hppn) (Ex := Ex) (Cond := Cond) (Htext := Htext) (Hflow := Hflow)
        (Hloc := Hloc) (G := G) (HG := HG) (dreg := dreg) (damo := damo) (Hdmap := Hdmap)
        (stackOwn := stackOwn) (SFPop := SFPop) (wpt := wpt) (ldRule := ldRule)
        (CondAnd := CondAnd) (HnoRmwReg := HnoRmwReg) (held := held) (kt := kt)
        (stackOwnSlots := stackOwnSlots) (wCret4 := wCret4))
      (wp_s_add := AxRelease4.wAdd4 (i := i) (cid := cid) (cpu := cpu) (γm := γm) (γp := γp)
        (γn := γn) (σi := σi) (T := T) (satp0 := satp0) (hmode := hmode) (hasid := hasid)
        (hppn := hppn) (Ex := Ex) (Cond := Cond) (Htext := Htext) (Hflow := Hflow)
        (stackOwn := stackOwn) (held := held) (kt := kt))
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
    (instr := instrW4 σi T satp0 Ex)
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
    (wp_epilogue4s1_gen := AxRelease4.wEpilogue4 (i := i) (cid := cid) (cpu := cpu) (γm := γm)
      (γp := γp) (γn := γn) (σi := σi) (T := T) (satp0 := satp0) (hmode := hmode)
      (hasid := hasid) (hppn := hppn) (Ex := Ex) (Cond := Cond) (Htext := Htext) (Hflow := Hflow)
      (Hloc := Hloc) (G := G) (HG := HG) (dreg := dreg) (damo := damo) (Hdmap := Hdmap)
      (stackOwn := stackOwn) (SFPop := SFPop) (wpt := wpt) (ldRule := ldRule)
      (CondAnd := CondAnd) (HnoRmwReg := HnoRmwReg) (held := held) (kt := kt)
      (stackOwnSlots := stackOwnSlots) (wCret4 := wCret4))
    (wp_s_add := AxRelease4.wAdd4 (i := i) (cid := cid) (cpu := cpu) (γm := γm) (γp := γp)
      (γn := γn) (σi := σi) (T := T) (satp0 := satp0) (hmode := hmode) (hasid := hasid)
      (hppn := hppn) (Ex := Ex) (Cond := Cond) (Htext := Htext) (Hflow := Hflow)
      (stackOwn := stackOwn) (held := held) (kt := kt))
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

end WPdRelease4

/-! ## The lock-protocol bridge (deviation 3): Rocq's finisher-shaped `swlk_rule` ⇒ the Lean
interface's held-set-shaped `swlkRule`, when the protocol NAMES THE HELD LOCK -/

section bridge
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- (Lean-only) **THE BRIDGE.**  Rocq's `swlk_rule` (the release store's output is the
finisher's `Out`, `lock_finisher γ lk R Dc Out E` an abstract resource) gives AxCondM4's /
AxRelease4's `swlkRule` (the output is the held set without `s`, and `s ∈ ks`) as soon as the
lock protocol NAMES THE HELD LOCK: `finHeld` — from the lock's handle (which names `s`), the
held context and the hart's held set, the finisher whose `Out` is "`s` removed, `s` was held"
can be minted. -/
theorem AxRelease4.swlkRuleOfFinisher (i : Agent) (dreg : Int → Nat → Prop) {Pay : Type _}
    (payAt : Pay → IProp GF) (payOk : Pay → Prop)
    (lockOpenable : GName → BitVec 64 → String → Pay → IProp GF → IProp GF)
    (hlo : ∀ γ lk s R D, Persistent (lockOpenable γ lk s R D))
    (lockedPre : GName → CPU → IProp GF) (lockCtxHeld : IProp GF)
    (held : CPU → List String → IProp GF)
    (lockFinisher : GName → BitVec 64 → Pay → IProp GF → IProp GF → CoPset → IProp GF) (E : CoPset)
    (swlkRuleR : ∀ (c0 : CPU) (cl : WmClass) (γl : GName) (lk : BitVec 64) (s : String) (R : Pay)
        (Dc Out : IProp GF) (Pd : List (BitVec 8) → Prop),
      (∀ data, Pd data → data = stBytes 4 0#64) → cl = .WCrel →
      ⊢ lockOpenable γl lk s R Dc -∗ lockedPre γl c0 -∗ payAt R -∗ lockFinisher γl lk R Dc Out E -∗
        ⌜dreg (paZ lk) 4⌝ ∗
        FstM rvwmoCatConsistent (dk3 (paZ lk) 4) i (fun _ data => iprop(⌜Pd data⌝ -∗ Out)))
    (finHeld : ∀ (c0 : CPU) (γl : GName) (lk : BitVec 64) (s : String) (R : Pay) (Dc : IProp GF)
        (ks : List String), payOk R →
      ⊢ lockOpenable γl lk s R Dc -∗ lockCtxHeld -∗ held c0 ks -∗
        lockFinisher γl lk R Dc iprop(held c0 (ks.filter (fun x => x ≠ s)) ∗ ⌜s ∈ ks⌝) E) :
    ∀ (c0 : CPU) (cl : WmClass) (γl : GName) (lk : BitVec 64) (s : String) (R : Pay) (Dc : IProp GF)
      (ks : List String) (Pd : List (BitVec 8) → Prop),
    (∀ data, Pd data → data = stBytes 4 0#64) → cl = .WCrel → payOk R →
    ⊢ lockOpenable γl lk s R Dc -∗ lockedPre γl c0 -∗ payAt R -∗ lockCtxHeld -∗ held c0 ks -∗
      ⌜dreg (paZ lk) 4⌝ ∗
      FstM rvwmoCatConsistent (dk3 (paZ lk) 4) i
        (fun _ data => iprop(⌜Pd data⌝ -∗ held c0 (ks.filter (fun x => x ≠ s)) ∗ ⌜s ∈ ks⌝)) := by
  intro c0 cl γl lk s R Dc ks Pd hPd hcl hR
  haveI := hlo γl lk s R Dc
  iintro #Hlo Hlp HR Hctx Hh
  ihave Hfin := finHeld c0 γl lk s R Dc ks hR $$ Hlo Hctx Hh
  iapply (swlkRuleR c0 cl γl lk s R Dc _ Pd hPd hcl) $$ Hlo Hlp HR Hfin

end bridge

/-! ## The bridge at AxRelease3's concrete instance: a lock protocol that names its lock -/

section rlinst
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
variable [GhostVarG GF (CPU × Bool)] [GhostVarG GF Unit]
variable (γb γh : GName) (sL : String)

/-- (Lean-only) AxRelease3's handle, NAMING its lock `sL` (as it pins `lk = L0`). -/
def AxRelease4.rlLockOpenableN (γ : GName) (lk : BitVec 64) (s : String) (R D : IProp GF) :
    IProp GF :=
  iprop(⌜s = sL⌝ ∗ rlLockOpenable γb γ lk R D)

instance AxRelease4.rlLockOpenableNPers (γ : GName) (lk : BitVec 64) (s : String)
    (R D : IProp GF) : Persistent (AxRelease4.rlLockOpenableN γb sL γ lk s R D) := by
  unfold AxRelease4.rlLockOpenableN
  infer_instance

/-- (Lean-only) The held context: an exclusive token. -/
def AxRelease4.rlCtxHeld : IProp GF := ghost_var γh (DFrac.own 1) ()

/-- (Lean-only) The hart's held set: complete for `sL` — "`sL` is not held" is the same
exclusive token, so it cannot coexist with the held context. -/
def AxRelease4.rlHeld (_c : CPU) (ks : List String) : IProp GF :=
  if sL ∈ ks then iprop(emp) else ghost_var γh (DFrac.own 1) ()

/-- (Lean-only) `finHeld` at the instance (finisher := `Out`, AxRelease3's `rlLockFinisher`):
the held context and the held set give "`sL` removed" and "`sL` was held". -/
theorem AxRelease4.rlFinHeld (E : CoPset) (c0 : CPU) (γl : GName) (lk : BitVec 64) (s : String)
    (R Dc : IProp GF) (ks : List String) (_hR : True) :
    ⊢ AxRelease4.rlLockOpenableN γb sL γl lk s R Dc -∗ AxRelease4.rlCtxHeld γh -∗
      AxRelease4.rlHeld γh sL c0 ks -∗
      rlLockFinisher γl lk R Dc
        iprop(AxRelease4.rlHeld γh sL c0 (ks.filter (fun x => x ≠ s)) ∗ ⌜s ∈ ks⌝) E := by
  unfold AxRelease4.rlLockOpenableN AxRelease4.rlCtxHeld AxRelease4.rlHeld rlLockFinisher
  iintro ⟨%hs, -⟩ Ht Hh
  subst hs
  by_cases hm : s ∈ ks
  · have hf : s ∉ ks.filter (fun x => x ≠ s) := by simp
    rw [if_pos hm, if_neg hf]
    isplitl [Ht]
    · iexact Ht
    · ipureintro; exact hm
  · rw [if_neg hm]
    ihave %hv := ghost_var_valid_2 _ _ _ _ _ $$ Ht Hh
    exact absurd (DFrac.valid_own_op hv.1) (by simp)

/-- (Lean-only) **AxRelease4's two lock rules at AxRelease3's instance** (`i := 0`, `dreg :=
rlDreg`, ONE `AxirisG` = `rlAxirisG γb`, ONE policy `lockAxpol`, `Pay := IProp GF`, `payAt :=
id`, `lockedCore := rlLocked`): `sdlkRule` from `rlSdlkRule`; `swlkRule` from `rlSwlkRule`
through the bridge `AxRelease4.swlkRuleOfFinisher` (finisher := `Out`, `finHeld` :=
`AxRelease4.rlFinHeld`).  So the held-set shape is jointly satisfiable with the real hand-off. -/
theorem AxRelease4.rlRulesHeld :
    (∀ (c0 : CPU) (_cl : WmClass) (γl : GName) (lk : BitVec 64) (s : String) (R Dc : IProp GF)
        (Pd : List (BitVec 8) → Prop), (∀ data, Pd data → data = stBytes 8 0#64) →
      ⊢ AxRelease4.rlLockOpenableN γb sL γl lk s R Dc -∗ rlLocked γl c0 -∗
        ⌜rlDreg (paZ (lk + 16#64)) 8⌝ ∗
        @FstM hlc GF _ (rlAxirisG γb) lockAxpol rvwmoCatConsistent (dk3 (paZ (lk + 16#64)) 8) 0
          (fun _ data => iprop(⌜Pd data⌝ -∗ rlLockedPre γl c0))) ∧
    (∀ (c0 : CPU) (cl : WmClass) (γl : GName) (lk : BitVec 64) (s : String) (R Dc : IProp GF)
        (ks : List String) (Pd : List (BitVec 8) → Prop),
      (∀ data, Pd data → data = stBytes 4 0#64) → cl = .WCrel → True →
      ⊢ AxRelease4.rlLockOpenableN γb sL γl lk s R Dc -∗ rlLockedPre γl c0 -∗ R -∗
        AxRelease4.rlCtxHeld γh -∗ AxRelease4.rlHeld γh sL c0 ks -∗
        ⌜rlDreg (paZ lk) 4⌝ ∗
        @FstM hlc GF _ (rlAxirisG γb) lockAxpol rvwmoCatConsistent (dk3 (paZ lk) 4) 0
          (fun _ data => iprop(⌜Pd data⌝ -∗
            AxRelease4.rlHeld γh sL c0 (ks.filter (fun x => x ≠ s)) ∗ ⌜s ∈ ks⌝))) := by
  refine ⟨fun c0 cl γl lk s R Dc Pd hPd => ?_, fun c0 cl γl lk s R Dc ks Pd hPd hcl hR => ?_⟩
  · unfold AxRelease4.rlLockOpenableN
    have H := rlSdlkRule (hlc := hlc) γb c0 cl γl lk R Dc Pd hPd
    unfold AxRelease3.lockCpu at H
    iintro ⟨%_, #Hlo⟩ Hl
    iapply H $$ Hlo Hl
  · exact @AxRelease4.swlkRuleOfFinisher hlc GF _ (rlAxirisG γb) lockAxpol 0 rlDreg (IProp GF)
      (fun R => R) (fun _ => True) (AxRelease4.rlLockOpenableN γb sL)
      (fun γ lk s R D => AxRelease4.rlLockOpenableNPers γb sL γ lk s R D) rlLockedPre
      (AxRelease4.rlCtxHeld γh) (AxRelease4.rlHeld γh sL) rlLockFinisher ⊤
      (fun c0 cl γl lk s R Dc Out Pd hPd hcl => by
        unfold AxRelease4.rlLockOpenableN
        iintro ⟨%_, #Hlo⟩ Hlp HR Hfin
        iapply (rlSwlkRule (hlc := hlc) γb c0 cl γl lk R Dc Out ⊤ Pd hPd hcl) $$ Hlo Hlp HR Hfin)
      (fun c0 γl lk s R Dc ks hR => AxRelease4.rlFinHeld γb γh sL ⊤ c0 γl lk s R Dc ks hR)
      c0 cl γl lk s R Dc ks Pd hPd hcl hR

end rlinst

end Weak
