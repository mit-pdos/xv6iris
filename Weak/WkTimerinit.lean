/-
Weak: **the weak `timerinit()`** -- xv6's `timerinit()` (21 instructions, KernelInstrs indices
9..29) as ONE `wwpTriv` theorem, composed entirely from the SC-shaped leaves: `WeakLeafO`'s
`_run` wrappers over `WkTimerinitAux`'s per-instruction `winstrM` tokens.

Rocq: `iris/WkTimerinit.v` @ xxvzwolszwmp.

The Rocq header, in substance.  This file demonstrates STEP-SITE PARITY: every instruction is
one `iapply` naming the wrapper and one `iintro` naming the resources back, plus the register-map
bookkeeping its SC twin also does.  The decode preamble is `WkTimerinitAux.wstiNN` (one `ihave`);
the `wstate` threading is gone -- the hart's view rides inside `whartRun cpu ξ q c`, and the frame
is OBJECTIVE (`cobj ξ`), so it stays in the Iris context across a step.  The two stack slots are
the one place weak memory is visible, and only at the stores: `wwpSd8TorRvcRun` is the RELEASE
store and hands back a timestamp, the floor token and the frozen payload; a private stack slot
publishes nothing, so this chain instantiates `R := ⌜True⌝` and drops both outputs.  The two
`c.sdsp`/`c.ldsp` pairs are CELL-based (base `sp` plus the data/destination register, extracted
from the whole `gprFile` with `gprFile_acc_2` and folded back after); every other instruction is
FILE-based.

**Deviations from Rocq.**
1. VOCABULARY: `Weak/WeakLeafM.lean` / `Weak/WeakLeafO.lean` / `Weak/WkTimerinitAux.lean`
   deviation 1 (`mword n` ↦ `BitVec n`, `sign_extend' n` ↦ `sign_extend (m := n)`, `regfile` ↦
   `MachCSL.RegMap` with `RegMap.set`, `gpr_file` ↦ `MachCSL.gprFile cpu`, `pc_is` ↦ `pcIs cpu`,
   `ret_pc` ↦ `WeakLeafMret.retPc`, `luival` ↦ `WkEntryEff.luival`, `menvcfg_legalized` ↦
   `WeakLeafCsrw2.menvcfgLegalized`, `stimecmp_legalized` ↦ `stimecmpLegalized`, `wstack_own_phys`
   ↦ `wstackOwnPhys cpu`, `pa_stk` ↦ `paStk`, `WWP Loop` ↦ `wwpTriv ⊤ (WExpr.loop gen cpu)` with
   the generation explicit and `gen = 0` the premise for Rocq `gen_id = 0`).
2. THE CONFIGURATION (owner decision Q3, the CSR-in-mConf consequence): Rocq's separate cells
   `menvcfg ↦ᵣ menv0`, `mcounteren ↦ᵣ mcen0`, `stimecmp ↦ᵣ stimecmp0`, `pmpcfg_n ↦ᵣ{q} pmpcfg1`,
   `pmpaddr_n ↦ᵣ{q} pmpaddrs` are fields of the `mConf` config `c` inside `whartRun cpu ξ 1 c`
   (Rocq's `pmpcfg_n` slot is `clockCells cpu`, as in WeakLeafM); `menv0`/`mcen0`/`stimecmp0` are
   `c.menvcfg`/`c.mcounteren`/`c.stimecmp`, and the three CSR writes come back inside the final
   config `WkTimerinit.tiConfOut c tv`.  The bundle is at the FULL fraction `1` (Rocq: any `q`):
   the csrw menvcfg / mcounteren / stimecmp wrappers write `mConf` and take `whartRun cpu ξ 1`
   (WeakLeafO deviation 3).  NOTE for the caller: Rocq `WkStartNew` applies `wwp_timerinit` at
   `q = 1/2`; its Lean port must call this at `1`.  `MConf.mok c` is an extra premise (every
   WeakLeafO wrapper takes it).
3. RAM premises: Rocq `∀ j < 8, addr_is_ram (pa_add ea j)` ↦ `inRam ea 8` (WeakLeafM deviation 6).
4. THE SC VOCABULARY (`WpTimerinit`'s `ti_sp1`, `ti_ea_ra`, `ti_ea_s0`, `ti_s0v`, `ti_bit63`,
   `ti_menv1`, `ti_mcen1`, `ti_interval`, `ti_deadline`, `ti_sp_restore`, `ti_m1` … `ti_mout`, and
   `WpMmodeLeafBase.cli_wval`, `sext6_12_64`): no Lean twin (`notes/weak-port-map.md`), restated
   here file-qualified (`WkTimerinit.*`, §0).  `sext6_12_64` and `add_vec_zero_l` are used at
   closed immediates only, so they are `decide +kernel` facts in the proof.
5. REGISTER-MAP LEMMAS over `RegMap` (Rocq: `regfile` with `functional_extensionality`);
   `gpr_file_reinsert_acc` is `MachCSL.gprFile_acc` (already value-generic) and takes Lean's
   `i ≠ 0#5` (the file does not own `x0`).  The cell-based steps need no `gpr_pt_nz` conversion
   (Lean's file cells ARE `gpr cpu i (DFrac.own 1) _`).
6. Ltacs: `ti_reg_neq` ↦ `decide`; `ti_look` + `ti_unfold` ↦ the macro `wk_ti_look`; `vm_refl` ↦
   `decide +kernel`.  Rocq's `iEval (change … with ti_mNN …)` ↦ `rw [show … = tiMNN … from rfl]`
   on the proof-mode goal; Rocq's `iEval (rewrite L…)` ↦ `rw [L…]`.
7. The stack is split and rebundled through the Lean-only `WkTimerinit.stackSplit` /
   `stackRebuild` (Rocq inlines the same `cobj_mono`/`cobj_sep`/`cobj_exist` script); the stores
   and loads are stated at the slot addresses `paStk sp0 1` / `paStk sp0 2` (= `tiEaRa sp0` /
   `tiEaS0 sp0`, `WkTimerinit.eaRaStk` / `eaS0Stk`), so no slot hypothesis is rewritten.

**Rocq → Lean name map.**  `wwp_timerinit` `wwpTimerinit`; `regfile_upd2_id`
`WkTimerinit.regfileUpd2Id`, `regfile_upd2_id'` `WkTimerinit.regfileUpd2Id'`,
`regfile_upd_drop_outer` `WkTimerinit.regfileUpdDropOuter`, `regfile_upd_drop_outer'`
`WkTimerinit.regfileUpdDropOuter'`, `gpr_file_reinsert_acc` `WkTimerinit.gprFileReinsertAcc`,
`stack_2_intro_ent` `WkTimerinit.stack2IntroEnt`; Ltacs `ti_reg_neq` (`decide`), `ti_look`
`wk_ti_look`.  None is in the duplicated-name table.  Lean-only (file-qualified): the SC stand-ins
`WkTimerinit.tiSp1 tiEaRa tiEaS0 tiS0v tiBit63 tiMenv1 tiMcen1 tiInterval tiDeadline cliWval
tiSpRestore tiM1 tiM12 tiM13 tiM14 tiM15 tiM16 tiM18 tiM19 tiM21 tiM22 tiM23 tiM24 tiM26 tiM27
tiMout`, the configs `tiC17 tiC20 tiConfOut`, and `eaRaStk eaS0Stk cobjTrue stackSplit
stackRebuild`.

**Dropped:** the Ltacs `vm_refl`, `ti_unfold` (deviation 6).  Rocq: 7 lemmas + 4 Ltacs; Lean: the
7 theorems, 1 macro, and the Lean-only declarations above.
-/
import Weak.WkTimerinitAux
import Weak.WeakLeafO2
import Weak.WkStackOwn
import Weak.WkGprAcc

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open WkTimerinitAux

/-! ## 0. The `WpTimerinit` vocabulary (Lean-only stand-ins, deviation 4) -/

/-- Rocq `WpMmodeLeafBase.cli_wval`: the value a `c.li rd, imm6` writes. -/
def WkTimerinit.cliWval (imm6 : BitVec 6) : BitVec 64 := sign_extend (m := 64) imm6
/-- Rocq `ti_sp1`: `sp` after the prologue `c.addi` (`sp0 - 16`). -/
def WkTimerinit.tiSp1 (sp0 : BitVec 64) : BitVec 64 := sp0 + sign_extend (m := 64) i9
/-- Rocq `ti_ea_ra`: the `ra` stack slot. -/
def WkTimerinit.tiEaRa (sp0 : BitVec 64) : BitVec 64 :=
  WkTimerinit.tiSp1 sp0 + sign_extend (m := 64) (zero_extend (m := 12) (u10 +++ 0b000#3))
/-- Rocq `ti_ea_s0`: the `s0` stack slot. -/
def WkTimerinit.tiEaS0 (sp0 : BitVec 64) : BitVec 64 :=
  WkTimerinit.tiSp1 sp0 + sign_extend (m := 64) (zero_extend (m := 12) (u11 +++ 0b000#3))
/-- Rocq `ti_s0v`: `s0` after `c.addi4spn` (`sp1 + 16`). -/
def WkTimerinit.tiS0v (sp0 : BitVec 64) : BitVec 64 :=
  WkTimerinit.tiSp1 sp0 + sign_extend (m := 64) (caddi4spnImm nz12)
/-- Rocq `ti_bit63`. -/
def WkTimerinit.tiBit63 : BitVec 64 := 0x8000000000000000#64
/-- Rocq `ti_menv1`. -/
def WkTimerinit.tiMenv1 (menv0 : BitVec 64) : BitVec 64 := menv0 ||| WkTimerinit.tiBit63
/-- Rocq `ti_mcen1`. -/
def WkTimerinit.tiMcen1 (mcen0 : BitVec 32) : BitVec 64 :=
  zero_extend (m := 64) mcen0 ||| sign_extend (m := 64) i19
/-- Rocq `ti_interval`. -/
def WkTimerinit.tiInterval : BitVec 64 := 1000000#64
/-- Rocq `ti_deadline`. -/
def WkTimerinit.tiDeadline (mtime0 : BitVec 64) : BitVec 64 := mtime0 + WkTimerinit.tiInterval

open WkTimerinit

/-- Rocq `ti_sp_restore`. -/
theorem WkTimerinit.tiSpRestore (sp0 : BitVec 64) : tiSp1 sp0 + sign_extend (m := 64) i28 = sp0 := by
  unfold tiSp1
  rw [BitVec.add_assoc,
    show sign_extend (m := 64) i9 + sign_extend (m := 64) i28 = 0#64 by decide +kernel,
    BitVec.add_zero]

/-- The `ra` slot is the first stack slot below `sp0`. -/
theorem WkTimerinit.eaRaStk (sp0 : BitVec 64) : tiEaRa sp0 = paStk sp0 1 := by
  unfold tiEaRa tiSp1 paStk
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  exact congrArg (sp0 + ·) (by decide +kernel)

/-- The `s0` slot is the second stack slot below `sp0`. -/
theorem WkTimerinit.eaS0Stk (sp0 : BitVec 64) : tiEaS0 sp0 = paStk sp0 2 := by
  unfold tiEaS0 tiSp1 paStk
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  exact congrArg (sp0 + ·) (by decide +kernel)

/-! ### The register file after each write (Rocq `ti_m*`) -/

/-- Rocq `ti_m1`. -/
def WkTimerinit.tiM1 (m : RegMap) (sp0 : BitVec 64) : RegMap := m.set cspRs1 (tiSp1 sp0)
/-- Rocq `ti_m12`. -/
def WkTimerinit.tiM12 (m : RegMap) (sp0 : BitVec 64) : RegMap :=
  (tiM1 m sp0).set tiS0 (tiS0v sp0)
/-- Rocq `ti_m13`. -/
def WkTimerinit.tiM13 (m : RegMap) (sp0 menv0 : BitVec 64) : RegMap :=
  (tiM12 m sp0).set tiA5 menv0
/-- Rocq `ti_m14`. -/
def WkTimerinit.tiM14 (m : RegMap) (sp0 menv0 : BitVec 64) : RegMap :=
  (tiM13 m sp0 menv0).set tiA4 (cliWval i14)
/-- Rocq `ti_m15`. -/
def WkTimerinit.tiM15 (m : RegMap) (sp0 menv0 : BitVec 64) : RegMap :=
  (tiM14 m sp0 menv0).set tiA4 tiBit63
/-- Rocq `ti_m16`. -/
def WkTimerinit.tiM16 (m : RegMap) (sp0 menv0 : BitVec 64) : RegMap :=
  (tiM15 m sp0 menv0).set tiA5 (tiMenv1 menv0)
/-- Rocq `ti_m18`. -/
def WkTimerinit.tiM18 (m : RegMap) (sp0 menv0 : BitVec 64) (mcen0 : BitVec 32) : RegMap :=
  (tiM16 m sp0 menv0).set tiA5 (zero_extend (m := 64) mcen0)
/-- Rocq `ti_m19`. -/
def WkTimerinit.tiM19 (m : RegMap) (sp0 menv0 : BitVec 64) (mcen0 : BitVec 32) : RegMap :=
  (tiM18 m sp0 menv0 mcen0).set tiA5 (tiMcen1 mcen0)
/-- Rocq `ti_m21`. -/
def WkTimerinit.tiM21 (m : RegMap) (sp0 menv0 : BitVec 64) (mcen0 : BitVec 32)
    (mtime0 : BitVec 64) : RegMap :=
  (tiM19 m sp0 menv0 mcen0).set tiA5 mtime0
/-- Rocq `ti_m22`. -/
def WkTimerinit.tiM22 (m : RegMap) (sp0 menv0 : BitVec 64) (mcen0 : BitVec 32)
    (mtime0 : BitVec 64) : RegMap :=
  (tiM21 m sp0 menv0 mcen0 mtime0).set tiA4 (WkEntryEff.luival i22)
/-- Rocq `ti_m23`. -/
def WkTimerinit.tiM23 (m : RegMap) (sp0 menv0 : BitVec 64) (mcen0 : BitVec 32)
    (mtime0 : BitVec 64) : RegMap :=
  (tiM22 m sp0 menv0 mcen0 mtime0).set tiA4 tiInterval
/-- Rocq `ti_m24`. -/
def WkTimerinit.tiM24 (m : RegMap) (sp0 menv0 : BitVec 64) (mcen0 : BitVec 32)
    (mtime0 : BitVec 64) : RegMap :=
  (tiM23 m sp0 menv0 mcen0 mtime0).set tiA5 (tiDeadline mtime0)
/-- Rocq `ti_m26`. -/
def WkTimerinit.tiM26 (m : RegMap) (sp0 menv0 : BitVec 64) (mcen0 : BitVec 32)
    (mtime0 ra0 : BitVec 64) : RegMap :=
  (tiM24 m sp0 menv0 mcen0 mtime0).set tiRa ra0
/-- Rocq `ti_m27`. -/
def WkTimerinit.tiM27 (m : RegMap) (sp0 menv0 : BitVec 64) (mcen0 : BitVec 32)
    (mtime0 ra0 s00 : BitVec 64) : RegMap :=
  (tiM26 m sp0 menv0 mcen0 mtime0 ra0).set tiS0 s00
/-- Rocq `ti_mout`: the FINAL file (sp/ra/s0 restored, a4 = the interval, a5 = the deadline). -/
def WkTimerinit.tiMout (m : RegMap) (sp0 menv0 : BitVec 64) (mcen0 : BitVec 32)
    (mtime0 ra0 s00 : BitVec 64) : RegMap :=
  (tiM27 m sp0 menv0 mcen0 mtime0 ra0 s00).set cspRs1 sp0

/-! ### The configuration after each CSR write (deviation 2) -/

/-- After `csrw menvcfg, a5`. -/
def WkTimerinit.tiC17 (c : MConf) : MConf :=
  { c with menvcfg := WeakLeafCsrw2.menvcfgLegalized c.menvcfg (tiMenv1 c.menvcfg) }
/-- After `csrw mcounteren, a5`. -/
def WkTimerinit.tiC20 (c : MConf) : MConf :=
  { tiC17 c with mcounteren := legalize_mcounteren (tiC17 c).mcounteren (tiMcen1 c.mcounteren) }
/-- After `csrw stimecmp, a5`: the config `timerinit()` returns. -/
def WkTimerinit.tiConfOut (c : MConf) (tv : BitVec 64) : MConf :=
  { tiC20 c with stimecmp := stimecmpLegalized (tiC20 c).stimecmp (tiDeadline tv) }

/-! ## 1. Register-map lemmas (deviation 5) -/

/-- Rocq `regfile_upd2_id`. -/
theorem WkTimerinit.regfileUpd2Id (f : RegMap) (i j : BitVec 5) (_hij : i ≠ j) :
    (f.set j (f j)).set i (f i) = f := by
  rw [RegMap.set_self, RegMap.set_self]

/-- Rocq `regfile_upd2_id'`. -/
theorem WkTimerinit.regfileUpd2Id' (f : RegMap) (i j : BitVec 5) (vi vj : BitVec 64)
    (hij : i ≠ j) (hi : f i = vi) (hj : f j = vj) : (f.set j vj).set i vi = f := by
  subst hi hj
  exact WkTimerinit.regfileUpd2Id f i j hij

/-- Rocq `regfile_upd_drop_outer`. -/
theorem WkTimerinit.regfileUpdDropOuter (f : RegMap) (i j : BitVec 5) (vj : BitVec 64)
    (hij : i ≠ j) : (f.set j vj).set i (f i) = f.set j vj := by
  funext k
  by_cases hk : k = i
  · subst hk
    rw [RegMap.set_same, RegMap.set_other _ _ _ _ hij]
  · rw [RegMap.set_other _ _ _ _ hk]

/-- Rocq `regfile_upd_drop_outer'`. -/
theorem WkTimerinit.regfileUpdDropOuter' (f : RegMap) (i j : BitVec 5) (vi vj : BitVec 64)
    (hij : i ≠ j) (hi : f i = vi) : (f.set j vj).set i vi = f.set j vj := by
  subst hi
  exact WkTimerinit.regfileUpdDropOuter f i j vj hij

/-- Total lookups over the `tiM*` insert chains (Rocq `ti_unfold; ti_look`). -/
macro "wk_ti_look" : tactic =>
  `(tactic| (simp (disch := decide +kernel) only [WkTimerinit.tiM1, WkTimerinit.tiM12,
      WkTimerinit.tiM13, WkTimerinit.tiM14, WkTimerinit.tiM15, WkTimerinit.tiM16, WkTimerinit.tiM18,
      WkTimerinit.tiM19, WkTimerinit.tiM21, WkTimerinit.tiM22, WkTimerinit.tiM23,
      WkTimerinit.tiM24, WkTimerinit.tiM26, WkTimerinit.tiM27, WkTimerinit.tiMout,
      RegMap.get_ne, RegMap.set_same, RegMap.set_other]; done))

section gprReinsert
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- Rocq `gpr_file_reinsert_acc` (deviation 5): `MachCSL.gprFile_acc`. -/
theorem WkTimerinit.gprFileReinsertAcc (cpu : CPU) (f : RegMap) (i : BitVec 5) (hi : i ≠ 0#5) :
    gprFile (GF := GF) cpu f ⊢
      gpr cpu i (DFrac.own 1) (f i) ∗ ∀ w, gpr cpu i (DFrac.own 1) w -∗ gprFile cpu (f.set i w) :=
  gprFile_acc cpu f i hi

end gprReinsert

/-! ## 2. The stack frame (deviation 7) -/

section stack
variable {GF : BundledGFunctors} [WeakGS GF]

/-- Rocq `stack_2_intro_ent`. -/
theorem WkTimerinit.stack2IntroEnt (cpu : CPU) (sp : PAddr) (w1 w2 : BitVec 64) :
    iprop(wpt8Own (GF := GF) cpu (paStk sp 1) w1 ∗ wpt8Own cpu (paStk sp 2) w2) ⊢
      wstackOwnPhys cpu sp 2 := by
  iintro ⟨H1, H2⟩
  iapply wstackOwnPhys_2_intro cpu sp w1 w2 $$ H1 H2

/-- The private payload of the two release stores. -/
theorem WkTimerinit.cobjTrue (ξ : CtxId) : ⊢ cobj (GF := GF) ξ (iprop(⌜True⌝) : VProp GF) := by
  iapply (cobjPure (GF := GF) ξ True).2
  ipureintro
  trivial

/-- Split the top two slots off the objective stack. -/
theorem WkTimerinit.stackSplit (ξ : CtxId) (cpu : CPU) (sp0 : PAddr) (n : Nat) (hn : 2 ≤ n) :
    cobj (GF := GF) ξ (wstackOwnPhys cpu sp0 n) ⊢
      ∃ w1 w2 : BitVec 64, cobj ξ (wpt8Own cpu (paStk sp0 1) w1) ∗
        cobj ξ (wpt8Own cpu (paStk sp0 2) w2) ∗ cobj ξ (wstackOwnPhys cpu (paStk sp0 2) (n - 2)) := by
  iintro H
  icases cobjMono ξ _ _ (wstackOwnPhys_split_1 cpu sp0 2 n hn) $$ H with H
  icases (cobjSep ξ _ _).1 $$ H with ⟨Htop, Hdeep⟩
  icases cobjMono ξ _ _ (wstackOwnPhys_2_elim cpu sp0) $$ Htop with Htop
  icases (cobjExist ξ _).1 $$ Htop with ⟨%w1, Htop⟩
  icases (cobjExist ξ _).1 $$ Htop with ⟨%w2, Htop⟩
  icases (cobjSep ξ _ _).1 $$ Htop with ⟨H1, H2⟩
  iexists w1, w2
  isplitl [H1]
  · iexact H1
  isplitl [H2]
  · iexact H2
  · iexact Hdeep

/-- Put the top two slots back. -/
theorem WkTimerinit.stackRebuild (ξ : CtxId) (cpu : CPU) (sp0 : PAddr) (n : Nat) (hn : 2 ≤ n)
    (w1 w2 : BitVec 64) :
    cobj (GF := GF) ξ (wpt8Own cpu (paStk sp0 1) w1) ⊢
      cobj ξ (wpt8Own cpu (paStk sp0 2) w2) -∗
      cobj ξ (wstackOwnPhys cpu (paStk sp0 2) (n - 2)) -∗
      cobj ξ (wstackOwnPhys cpu sp0 n) := by
  iintro H1 H2 Hdeep
  iapply cobjMono ξ _ _ (wstackOwnPhys_split_2 cpu sp0 2 n hn)
  iapply (cobjSep ξ _ _).2
  isplitl [H1 H2]
  · iapply cobjMono ξ _ _ (WkTimerinit.stack2IntroEnt (GF := GF) cpu sp0 w1 w2)
    iapply (cobjSep ξ _ _).2
    isplitl [H1]
    · iexact H1
    · iexact H2
  · iexact Hdeep

end stack

/-! ## 3. THE THEOREM -/

section timerinit
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- Rocq `wwp_timerinit` (deviations 1-3): the whole-function spec. -/
theorem wwpTimerinit (gen : Nat) (cpu : CPU) (ξ : CtxId) (c : MConf) (m : RegMap)
    (sp0 ra0 s00 : BitVec 64) (n : Nat) (kbs : GMapF PAddr (BitVec 8)) :
    2 ≤ n →
    gen = 0 →
    MConf.mok c →
    pmpAllowsAll c.pmpcfg →
    pmpTor0Grants c.pmpcfg c.pmpaddr (tiEaRa sp0) 8 →
    pmpTor0Grants c.pmpcfg c.pmpaddr (tiEaS0 sp0) 8 →
    wkbCovers kbs →
    m cspRs1 = sp0 →
    m tiRa = ra0 →
    m tiS0 = s00 →
    inRam (tiEaRa sp0) 8 →
    inRam (tiEaS0 sp0) 8 →
    whartRun (GF := GF) cpu ξ 1 c ⊢
      clockCells cpu -∗
      pcIs cpu tiPc9 -∗
      gprFile cpu m -∗
      cobj ξ (wstackOwnPhys (GF := GF) cpu sp0 n) -∗
      wkernelText (GF := GF) kbs -∗
      (∀ tv : BitVec 64,
        whartRun cpu ξ 1 (tiConfOut c tv) -∗
        clockCells cpu -∗
        pcIs cpu (WeakLeafMret.retPc ra0) -∗
        gprFile cpu (tiMout m sp0 c.menvcfg c.mcounteren tv ra0 s00) -∗
        cobj ξ (wstackOwnPhys (GF := GF) cpu sp0 n) -∗
        wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu)) -∗
      wwpTriv (hlc := hlc) (GF := GF) ⊤ (WExpr.loop gen cpu) := by
  intro hn2 hgid hmok hpmp htorRa htorS0 hcov hsp hra hs0 hramRa hramS0
  iintro Hrun Hclk Hpc Hfile Hstk #Htext Hcont
  -- ---- split off the top two stack slots, OBJECTIVELY ----
  icases WkTimerinit.stackSplit ξ cpu sp0 n hn2 $$ Hstk with ⟨%voldRa, %voldS0, Hstkra, Hstks0, Hdeep⟩
  have hpra := eaRaStk sp0
  have hps0 := eaS0Stk sp0
  have htorRa' : pmpTor0Grants c.pmpcfg c.pmpaddr (paStk sp0 1) 8 := hpra ▸ htorRa
  have htorS0' : pmpTor0Grants c.pmpcfg c.pmpaddr (paStk sp0 2) 8 := hps0 ▸ htorS0
  have hramRa' : inRam (paStk sp0 1) 8 := hpra ▸ hramRa
  have hramS0' : inRam (paStk sp0 2) 8 := hps0 ▸ hramS0
  -- closed-value bridges
  have hb63 : shift_bits_left (cliWval i14)
      (Sail.BitVec.extractLsb sh15 (Functions.log2_xlen -i 1) 0) = tiBit63 := by decide +kernel
  have hival : WkEntryEff.luival i22 + sign_extend (m := 64) i23 = tiInterval := by decide +kernel
  have hs9 : sign_extend (m := 64) (sign_extend (m := 12) i9) = sign_extend (m := 64) i9 := by
    decide +kernel
  have hs14 : sign_extend (m := 64) (sign_extend (m := 12) i14) = cliWval i14 := by decide +kernel
  have hs28 : sign_extend (m := 64) (sign_extend (m := 12) i28) = sign_extend (m := 64) i28 := by
    decide +kernel
  have hcli : ∀ M : RegMap, M.get cliRs1 = 0#64 := fun M => by
    unfold RegMap.get; rw [if_pos (show cliRs1 = 0#5 by decide)]
  -- ==================================================================
  -- ---- 9. c.addi sp, -16 ----
  ihave #Hi9 := wsti9 (GF := GF) kbs hcov $$ Htext
  iapply wwpAddiRun gen cpu ξ tiPc9 true cspRs1 cspRs1 (sign_extend (m := 12) i9) m c 1 hgid hmok
    hpmp (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi9
  iintro Hrun Hclk Hpc Hfile
  rw [RegMap.get_ne m cspRs1 (by decide +kernel), hsp, hs9,
    show m.set cspRs1 (sp0 + sign_extend (m := 64) i9) = tiM1 m sp0 from rfl,
    show BitVec.addInt tiPc9 (if true then 2 else 4) = tiPc10 by decide +kernel]
  -- ---- 10. c.sdsp ra, 8(sp)  (RELEASE store) ----
  have Lsp1 : tiM1 m sp0 cspRs1 = tiSp1 sp0 := by wk_ti_look
  have Lra1 : tiM1 m sp0 tiRa = ra0 := by rw [← hra]; wk_ti_look
  have Ls01 : tiM1 m sp0 tiS0 = s00 := by rw [← hs0]; wk_ti_look
  ihave #Hi10 := wsti10 (GF := GF) kbs hcov $$ Htext
  icases gprFile_acc_2 cpu (tiM1 m sp0) cspRs1 tiRa (by decide +kernel) (by decide +kernel) (by decide +kernel) $$ Hfile
    with ⟨Hspc, Hrac, Hfacc⟩
  rw [Lsp1, Lra1]
  ihave HR := WkTimerinit.cobjTrue (GF := GF) ξ
  iapply wwpSd8TorRvcRun gen cpu ξ tiPc10 cspRs1 tiRa (zero_extend (m := 12) (u10 +++ 0b000#3))
    (paStk sp0 1) voldRa iprop(⌜True⌝) 1 c (tiSp1 sp0) ra0 hgid hmok hpmp htorRa' (by decide +kernel)
    (by decide +kernel) hpra hramRa' $$ Hrun Hclk Hpc Hspc Hrac Hi10 Hstkra HR
  iintro %T10 - Hrun Hclk Hpc Hspc Hrac Hstkra -
  ihave Hfile := Hfacc $$ %(tiSp1 sp0) %ra0 Hspc Hrac
  rw [WkTimerinit.regfileUpd2Id' (tiM1 m sp0) cspRs1 tiRa _ _ (by decide +kernel) Lsp1 Lra1,
    show BitVec.addInt tiPc10 2 = tiPc11 by decide +kernel]
  -- ---- 11. c.sdsp s0, 0(sp)  (RELEASE store) ----
  ihave #Hi11 := wsti11 (GF := GF) kbs hcov $$ Htext
  icases gprFile_acc_2 cpu (tiM1 m sp0) cspRs1 tiS0 (by decide +kernel) (by decide +kernel) (by decide +kernel) $$ Hfile
    with ⟨Hspc, Hs0c, Hfacc⟩
  rw [Lsp1, Ls01]
  ihave HR := WkTimerinit.cobjTrue (GF := GF) ξ
  iapply wwpSd8TorRvcRun gen cpu ξ tiPc11 cspRs1 tiS0 (zero_extend (m := 12) (u11 +++ 0b000#3))
    (paStk sp0 2) voldS0 iprop(⌜True⌝) 1 c (tiSp1 sp0) s00 hgid hmok hpmp htorS0' (by decide +kernel)
    (by decide +kernel) hps0 hramS0' $$ Hrun Hclk Hpc Hspc Hs0c Hi11 Hstks0 HR
  iintro %T11 - Hrun Hclk Hpc Hspc Hs0c Hstks0 -
  ihave Hfile := Hfacc $$ %(tiSp1 sp0) %s00 Hspc Hs0c
  rw [WkTimerinit.regfileUpd2Id' (tiM1 m sp0) cspRs1 tiS0 _ _ (by decide +kernel) Lsp1 Ls01,
    show BitVec.addInt tiPc11 2 = tiPc12 by decide +kernel]
  -- ---- 12. c.addi4spn s0, sp, 16 ----
  ihave #Hi12 := wsti12 (GF := GF) kbs hcov $$ Htext
  iapply wwpAddiRun gen cpu ξ tiPc12 true cspRs1 tiS0 (caddi4spnImm nz12) (tiM1 m sp0) c 1
    hgid hmok hpmp (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi12
  iintro Hrun Hclk Hpc Hfile
  rw [RegMap.get_ne (tiM1 m sp0) cspRs1 (by decide +kernel), Lsp1,
    show (tiM1 m sp0).set tiS0 (tiSp1 sp0 + sign_extend (m := 64) (caddi4spnImm nz12)) =
      tiM12 m sp0 from rfl,
    show BitVec.addInt tiPc12 (if true then 2 else 4) = tiPc13 by decide +kernel]
  -- ---- 13. csrr a5, menvcfg ----
  ihave #Hi13 := wsti13 (GF := GF) kbs hcov $$ Htext
  icases gprFile_acc cpu (tiM12 m sp0) tiA5 (by decide +kernel) $$ Hfile with ⟨Ha5c, Hfins⟩
  iapply wwpCsrrMenvcfgRun gen cpu ξ tiPc13 tiA5 (tiM12 m sp0 tiA5) c 1 hgid hmok hpmp (by decide +kernel)
    $$ Hrun Hclk Hpc Ha5c Hi13
  iintro Hrun Hclk Hpc Ha5c
  ihave Hfile := Hfins $$ %(c.menvcfg) Ha5c
  rw [show (tiM12 m sp0).set tiA5 c.menvcfg = tiM13 m sp0 c.menvcfg from rfl,
    show BitVec.addInt tiPc13 4 = tiPc14 by decide +kernel]
  -- ---- 14. c.li a4, -1 ----
  ihave #Hi14 := wsti14 (GF := GF) kbs hcov $$ Htext
  iapply wwpAddiRun gen cpu ξ tiPc14 true cliRs1 tiA4 (sign_extend (m := 12) i14)
    (tiM13 m sp0 c.menvcfg) c 1 hgid hmok hpmp (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi14
  iintro Hrun Hclk Hpc Hfile
  rw [hcli, BitVec.zero_add, hs14,
    show (tiM13 m sp0 c.menvcfg).set tiA4 (cliWval i14) = tiM14 m sp0 c.menvcfg from rfl,
    show BitVec.addInt tiPc14 (if true then 2 else 4) = tiPc15 by decide +kernel]
  -- ---- 15. c.slli a4, 63 ----
  have L15a4 : (tiM14 m sp0 c.menvcfg).get tiA4 = cliWval i14 := by wk_ti_look
  ihave #Hi15 := wsti15 (GF := GF) kbs hcov $$ Htext
  iapply wwpSlliRvcRun gen cpu ξ tiPc15 tiA4 tiA4 sh15 (tiM14 m sp0 c.menvcfg) c 1 hgid hmok hpmp
    (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi15
  iintro Hrun Hclk Hpc Hfile
  rw [L15a4, hb63,
    show (tiM14 m sp0 c.menvcfg).set tiA4 tiBit63 = tiM15 m sp0 c.menvcfg from rfl,
    show BitVec.addInt tiPc15 2 = tiPc16 by decide +kernel]
  -- ---- 16. c.or a5, a4 ----
  have L16a5 : (tiM15 m sp0 c.menvcfg).get tiA5 = c.menvcfg := by wk_ti_look
  have L16a4 : (tiM15 m sp0 c.menvcfg).get tiA4 = tiBit63 := by wk_ti_look
  ihave #Hi16 := wsti16 (GF := GF) kbs hcov $$ Htext
  iapply wwpOrRvcRun gen cpu ξ tiPc16 tiA4 tiA5 tiA5 (tiM15 m sp0 c.menvcfg) c 1 hgid hmok hpmp
    (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi16
  iintro Hrun Hclk Hpc Hfile
  rw [L16a5, L16a4,
    show (tiM15 m sp0 c.menvcfg).set tiA5 (c.menvcfg ||| tiBit63) = tiM16 m sp0 c.menvcfg from rfl,
    show BitVec.addInt tiPc16 2 = tiPc17 by decide +kernel]
  -- ---- 17. csrw menvcfg, a5 ----
  have L17a5 : tiM16 m sp0 c.menvcfg tiA5 = tiMenv1 c.menvcfg := by wk_ti_look
  ihave #Hi17 := wsti17 (GF := GF) kbs hcov $$ Htext
  icases gprFile_lookup_acc cpu (tiM16 m sp0 c.menvcfg) tiA5 (by decide +kernel) $$ Hfile with ⟨Ha5c, Hfb⟩
  rw [L17a5]
  iapply wwpCsrwMenvcfgRun gen cpu ξ tiPc17 tiA5 (tiMenv1 c.menvcfg) c hgid hmok hpmp (by decide +kernel)
    $$ Hrun Hclk Hpc Ha5c Hi17
  iintro Hrun Hclk Hpc Ha5c
  ihave Hfile := Hfb $$ Ha5c
  rw [show ({ c with menvcfg := WeakLeafCsrw2.menvcfgLegalized c.menvcfg (tiMenv1 c.menvcfg) } :
      MConf) = tiC17 c from rfl,
    show BitVec.addInt tiPc17 4 = tiPc18 by decide +kernel]
  -- ---- 18. csrr a5, mcounteren ----
  ihave #Hi18 := wsti18 (GF := GF) kbs hcov $$ Htext
  icases gprFile_acc cpu (tiM16 m sp0 c.menvcfg) tiA5 (by decide +kernel) $$ Hfile with ⟨Ha5c, Hfins⟩
  iapply wwpCsrrMcounterenRun gen cpu ξ tiPc18 tiA5 (tiM16 m sp0 c.menvcfg tiA5) (tiC17 c) 1 hgid
    hmok hpmp (by decide +kernel) $$ Hrun Hclk Hpc Ha5c Hi18
  iintro Hrun Hclk Hpc Ha5c
  ihave Hfile := Hfins $$ %(zero_extend (m := 64) (tiC17 c).mcounteren) Ha5c
  rw [show (tiM16 m sp0 c.menvcfg).set tiA5 (zero_extend (m := 64) (tiC17 c).mcounteren) =
      tiM18 m sp0 c.menvcfg c.mcounteren from rfl,
    show BitVec.addInt tiPc18 4 = tiPc19 by decide +kernel]
  -- ---- 19. ori a5, a5, 2 ----
  have L19a5 : (tiM18 m sp0 c.menvcfg c.mcounteren).get tiA5 = zero_extend (m := 64) c.mcounteren :=
    by wk_ti_look
  ihave #Hi19 := wsti19 (GF := GF) kbs hcov $$ Htext
  iapply wwpOriRun gen cpu ξ tiPc19 tiA5 tiA5 i19 (tiM18 m sp0 c.menvcfg c.mcounteren) (tiC17 c) 1
    hgid hmok hpmp (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi19
  iintro Hrun Hclk Hpc Hfile
  rw [L19a5,
    show (tiM18 m sp0 c.menvcfg c.mcounteren).set tiA5
        (zero_extend (m := 64) c.mcounteren ||| sign_extend (m := 64) i19) =
      tiM19 m sp0 c.menvcfg c.mcounteren from rfl,
    show BitVec.addInt tiPc19 4 = tiPc20 by decide +kernel]
  -- ---- 20. csrw mcounteren, a5 ----
  have L20a5 : tiM19 m sp0 c.menvcfg c.mcounteren tiA5 = tiMcen1 c.mcounteren := by wk_ti_look
  ihave #Hi20 := wsti20 (GF := GF) kbs hcov $$ Htext
  icases gprFile_lookup_acc cpu (tiM19 m sp0 c.menvcfg c.mcounteren) tiA5 (by decide +kernel) $$ Hfile
    with ⟨Ha5c, Hfb⟩
  rw [L20a5]
  iapply wwpCsrwMcounterenRun gen cpu ξ tiPc20 tiA5 (tiMcen1 c.mcounteren) (tiC17 c) hgid hmok hpmp
    (by decide +kernel) $$ Hrun Hclk Hpc Ha5c Hi20
  iintro Hrun Hclk Hpc Ha5c
  ihave Hfile := Hfb $$ Ha5c
  rw [show ({ tiC17 c with
        mcounteren := legalize_mcounteren (tiC17 c).mcounteren (tiMcen1 c.mcounteren) } : MConf) =
      tiC20 c from rfl,
    show BitVec.addInt tiPc20 4 = tiPc21 by decide +kernel]
  -- ---- 21. csrr a5, time  (the read value `tv` is the leaf's own ∀) ----
  ihave #Hi21 := wsti21 (GF := GF) kbs hcov $$ Htext
  icases gprFile_acc cpu (tiM19 m sp0 c.menvcfg c.mcounteren) tiA5 (by decide +kernel) $$ Hfile
    with ⟨Ha5c, Hfins⟩
  iapply wwpCsrrTimeRun gen cpu ξ tiPc21 tiA5 (tiM19 m sp0 c.menvcfg c.mcounteren tiA5) (tiC20 c) 1
    hgid hmok hpmp (by decide +kernel) $$ Hrun Hclk Hpc Ha5c Hi21
  iintro %tv Hrun Hclk Hpc Ha5c
  ihave Hfile := Hfins $$ %tv Ha5c
  rw [show (tiM19 m sp0 c.menvcfg c.mcounteren).set tiA5 tv =
      tiM21 m sp0 c.menvcfg c.mcounteren tv from rfl,
    show BitVec.addInt tiPc21 4 = tiPc22 by decide +kernel]
  -- ---- 22. lui a4, 0xf4 ----
  ihave #Hi22 := wsti22 (GF := GF) kbs hcov $$ Htext
  iapply wwpLuiRun gen cpu ξ tiPc22 false tiA4 i22 (tiM21 m sp0 c.menvcfg c.mcounteren tv) (tiC20 c)
    1 hgid hmok hpmp (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi22
  iintro Hrun Hclk Hpc Hfile
  rw [show (tiM21 m sp0 c.menvcfg c.mcounteren tv).set tiA4 (WkEntryEff.luival i22) =
      tiM22 m sp0 c.menvcfg c.mcounteren tv from rfl,
    show BitVec.addInt tiPc22 (if false then 2 else 4) = tiPc23 by decide +kernel]
  -- ---- 23. addi a4, a4, 576 ----
  have L23a4 : (tiM22 m sp0 c.menvcfg c.mcounteren tv).get tiA4 = WkEntryEff.luival i22 := by
    wk_ti_look
  ihave #Hi23 := wsti23 (GF := GF) kbs hcov $$ Htext
  iapply wwpAddiRun gen cpu ξ tiPc23 false tiA4 tiA4 i23 (tiM22 m sp0 c.menvcfg c.mcounteren tv)
    (tiC20 c) 1 hgid hmok hpmp (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi23
  iintro Hrun Hclk Hpc Hfile
  rw [L23a4, hival,
    show (tiM22 m sp0 c.menvcfg c.mcounteren tv).set tiA4 tiInterval =
      tiM23 m sp0 c.menvcfg c.mcounteren tv from rfl,
    show BitVec.addInt tiPc23 (if false then 2 else 4) = tiPc24 by decide +kernel]
  -- ---- 24. c.add a5, a4 ----
  have L24a5 : (tiM23 m sp0 c.menvcfg c.mcounteren tv).get tiA5 = tv := by wk_ti_look
  have L24a4 : (tiM23 m sp0 c.menvcfg c.mcounteren tv).get tiA4 = tiInterval := by wk_ti_look
  ihave #Hi24 := wsti24 (GF := GF) kbs hcov $$ Htext
  iapply wwpAddRvcRun gen cpu ξ tiPc24 tiA4 tiA5 tiA5 (tiM23 m sp0 c.menvcfg c.mcounteren tv)
    (tiC20 c) 1 hgid hmok hpmp (by decide +kernel) $$ Hrun Hclk Hpc Hfile Hi24
  iintro Hrun Hclk Hpc Hfile
  rw [L24a5, L24a4,
    show (tiM23 m sp0 c.menvcfg c.mcounteren tv).set tiA5 (tv + tiInterval) =
      tiM24 m sp0 c.menvcfg c.mcounteren tv from rfl,
    show BitVec.addInt tiPc24 2 = tiPc25 by decide +kernel]
  -- ---- 25. csrw stimecmp, a5 ----
  have L25a5 : tiM24 m sp0 c.menvcfg c.mcounteren tv tiA5 = tiDeadline tv := by wk_ti_look
  ihave #Hi25 := wsti25 (GF := GF) kbs hcov $$ Htext
  icases gprFile_lookup_acc cpu (tiM24 m sp0 c.menvcfg c.mcounteren tv) tiA5 (by decide +kernel) $$ Hfile
    with ⟨Ha5c, Hfb⟩
  rw [L25a5]
  iapply wwpCsrwStimecmpRun gen cpu ξ tiPc25 tiA5 (tiDeadline tv) (tiC20 c) hgid hmok hpmp
    (by decide +kernel) $$ Hrun Hclk Hpc Ha5c Hi25
  iintro Hrun Hclk Hpc Ha5c
  ihave Hfile := Hfb $$ Ha5c
  rw [show ({ tiC20 c with stimecmp := stimecmpLegalized (tiC20 c).stimecmp (tiDeadline tv) } :
      MConf) = tiConfOut c tv from rfl,
    show BitVec.addInt tiPc25 4 = tiPc26 by decide +kernel]
  -- ---- 26. c.ldsp ra, 8(sp) ----
  have L26sp : tiM24 m sp0 c.menvcfg c.mcounteren tv cspRs1 = tiSp1 sp0 := by wk_ti_look
  ihave #Hi26 := wsti26 (GF := GF) kbs hcov $$ Htext
  icases gprFile_acc_2 cpu (tiM24 m sp0 c.menvcfg c.mcounteren tv) cspRs1 tiRa (by decide +kernel)
    (by decide +kernel) (by decide +kernel) $$ Hfile with ⟨Hspc, Hrac, Hfacc⟩
  rw [L26sp]
  iapply wwpLd8TorRvcRunOwn gen cpu ξ tiPc26 cspRs1 tiRa (zero_extend (m := 12) (u10 +++ 0b000#3))
    (paStk sp0 1) ra0 1 (tiConfOut c tv) (tiSp1 sp0) (tiM24 m sp0 c.menvcfg c.mcounteren tv tiRa)
    hgid hmok hpmp htorRa' (by decide +kernel) (by decide +kernel) hpra hramRa'
    $$ Hrun Hclk Hpc Hspc Hrac Hi26 Hstkra
  iintro Hrun Hclk Hpc Hspc Hrac Hstkra
  ihave Hfile := Hfacc $$ %(tiSp1 sp0) %ra0 Hspc Hrac
  rw [WkTimerinit.regfileUpdDropOuter' (tiM24 m sp0 c.menvcfg c.mcounteren tv) cspRs1 tiRa _ _
      (by decide +kernel) L26sp,
    show (tiM24 m sp0 c.menvcfg c.mcounteren tv).set tiRa ra0 =
      tiM26 m sp0 c.menvcfg c.mcounteren tv ra0 from rfl,
    show BitVec.addInt tiPc26 2 = tiPc27 by decide +kernel]
  -- ---- 27. c.ldsp s0, 0(sp) ----
  have L27sp : tiM26 m sp0 c.menvcfg c.mcounteren tv ra0 cspRs1 = tiSp1 sp0 := by wk_ti_look
  ihave #Hi27 := wsti27 (GF := GF) kbs hcov $$ Htext
  icases gprFile_acc_2 cpu (tiM26 m sp0 c.menvcfg c.mcounteren tv ra0) cspRs1 tiS0 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) $$ Hfile with ⟨Hspc, Hs0c, Hfacc⟩
  rw [L27sp]
  iapply wwpLd8TorRvcRunOwn gen cpu ξ tiPc27 cspRs1 tiS0 (zero_extend (m := 12) (u11 +++ 0b000#3))
    (paStk sp0 2) s00 1 (tiConfOut c tv) (tiSp1 sp0)
    (tiM26 m sp0 c.menvcfg c.mcounteren tv ra0 tiS0)
    hgid hmok hpmp htorS0' (by decide +kernel) (by decide +kernel) hps0 hramS0'
    $$ Hrun Hclk Hpc Hspc Hs0c Hi27 Hstks0
  iintro Hrun Hclk Hpc Hspc Hs0c Hstks0
  ihave Hfile := Hfacc $$ %(tiSp1 sp0) %s00 Hspc Hs0c
  rw [WkTimerinit.regfileUpdDropOuter' (tiM26 m sp0 c.menvcfg c.mcounteren tv ra0) cspRs1 tiS0 _ _
      (by decide +kernel) L27sp,
    show (tiM26 m sp0 c.menvcfg c.mcounteren tv ra0).set tiS0 s00 =
      tiM27 m sp0 c.menvcfg c.mcounteren tv ra0 s00 from rfl,
    show BitVec.addInt tiPc27 2 = tiPc28 by decide +kernel]
  -- ---- 28. c.addi sp, 16 ----
  have L28sp : (tiM27 m sp0 c.menvcfg c.mcounteren tv ra0 s00).get cspRs1 = tiSp1 sp0 := by
    wk_ti_look
  ihave #Hi28 := wsti28 (GF := GF) kbs hcov $$ Htext
  iapply wwpAddiRun gen cpu ξ tiPc28 true cspRs1 cspRs1 (sign_extend (m := 12) i28)
    (tiM27 m sp0 c.menvcfg c.mcounteren tv ra0 s00) (tiConfOut c tv) 1 hgid hmok hpmp (by decide +kernel)
    $$ Hrun Hclk Hpc Hfile Hi28
  iintro Hrun Hclk Hpc Hfile
  rw [L28sp, hs28, WkTimerinit.tiSpRestore,
    show (tiM27 m sp0 c.menvcfg c.mcounteren tv ra0 s00).set cspRs1 sp0 =
      tiMout m sp0 c.menvcfg c.mcounteren tv ra0 s00 from rfl,
    show BitVec.addInt tiPc28 (if true then 2 else 4) = tiPc29 by decide +kernel]
  -- ---- 29. c.ret ----
  have L29ra : tiMout m sp0 c.menvcfg c.mcounteren tv ra0 s00 tiRa = ra0 := by wk_ti_look
  ihave #Hi29 := wsti29 (GF := GF) kbs hcov $$ Htext
  icases gprFile_lookup_acc cpu (tiMout m sp0 c.menvcfg c.mcounteren tv ra0 s00) tiRa (by decide +kernel)
    $$ Hfile with ⟨Hrac, Hfb⟩
  rw [L29ra]
  iapply wwpCjrRvcRun gen cpu ξ tiPc29 tiRa ra0 (tiConfOut c tv) 1 hgid hmok hpmp (by decide +kernel)
    $$ Hrun Hclk Hpc Hrac Hi29
  iintro Hrun Hclk Hpc Hrac
  ihave Hfile := Hfb $$ Hrac
  -- ---- re-bundle the frame and return ----
  ihave Hstk := WkTimerinit.stackRebuild ξ cpu sp0 n hn2 ra0 s00 $$ Hstkra Hstks0 Hdeep
  iapply Hcont $$ %tv Hrun Hclk Hpc Hfile Hstk

end timerinit

end Weak
