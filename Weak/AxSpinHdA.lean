/-
Weak: **PHASE 5, stage 3: THE THEOREM `wpdHolding`** — xv6's REAL `holding(lk)` (the 21
instructions of `AxSpinHd.holdingText` at `KernelSyms.holding`, which CALLS the real `mycpu`) as a
POSITIONAL, CALLER-INDEXED CPS WPd at the joint instance Ixv6, interrupts off (`ctrlOkSW`: S-mode,
SIE = 0), WARM TLB.

Rocq: `iris/AxSpinHdA.v` @ xxvzwolszwmp.

## The Rocq header, in substance (as restated under Stage C)

`RowHolding k row hb …` (AxSpinHd8): holding's piece of hart `i`'s row from position `k`; `hb` is
the CFG path, fixed by the ROW VALUE of the lw of `lk->locked` at `k` (`hb` = "locked ≠ 0",
c.bnez's direction).  THE THEOREM (`wpdHolding`), for every `k`, `hb` and every row with
`RowHolding k row hb …`:

    WPd (boundary at k, regs rs0) {{Ψ}}
    ⇐  XLd k (holding+0x00) … 4 a0 Olk                         (lw lk->locked leaf)
       ∗ (if hb then XLd (k+4) (holding+0x12) … 8 a0 Ocpu ∗ KLong   (ld lk->cpu leaf)
          else KShort)

SHORT (`KShort`, locked = 0): ∀ vlk rs' ib', ⌜regime ∧ PC rs' = ret ∧ TLB kept ∧ a0 = 0 ∧
a5 = sext32 vlk ∧ the lw's graph value (k) = vlk ∧ every other GPR kept⌝ -∗ Olk vlk -∗ WPd
(boundary at k+1).
LONG (`KLong`, locked ≠ 0): ∀ vlk vcpu vram vs0m vra vs0 vs1 rs' ib', ⌜regime ∧ PC rs' = ret ∧ TLB
kept ∧ a0 = seqz ((0 + vcpu) − mycpuRet tp) ∧ sp restored ∧ ra/s0/s1 = the RELOADED words ∧ every
GPR but ra/sp/s0/s1/a0/a5 kept ∧ the spills' row data ∧ every read's graph value⌝ -∗ Olk vlk -∗
Ocpu vcpu -∗ the FIVE reload annotations -∗ WPd (boundary at k+12).
The continuation is at the EXACT position (`k + 1` / `k + 12`).  mycpu is COMPOSED at the inner
row position `k + 5` (`AxSpinE8.wpdMycpu`, via `AxSpinHd9.holdPro`).  The two shared loads are
CALLER-INDEXED SLOTS (`AxSpinHd7.XLd`): the caller supplies the read rule its protocol position
allows; values are SYMBOLIC (graph values).

GRAPH-VALUE PINNING (Q20', provisional Option V; the Rocq "TEMPORARY ASSUMPTION — ROW PINNING",
owner decision 2026-10-03): the row cannot pin control flow under Stage C.  On the LONG path both
returns are pinned by the ra reloads' GRAPH VALUES (mycpu's at `(i, k + 7)` = holding + 0x1a,
holding's at `(i, k + 9)` = `ret`, + `jalrTgt 0#12 ret = ret`), exactly as `AxSpinHd9.holdPro`
takes them; on the SHORT path there is no reload — the c.ret jumps to the ENTRY ra, and the pin is
`jalrTgt 0#12 (gprVal rs0 ra) = ret`.  The theorem proves nothing about a graph whose reload values
differ.

## Deviations from Rocq

1. O2 STAGE C / Q20' (provisional Option V; as `AxSpinHd8.holdEpi` / `AxSpinHd9.holdPro`):
   * Positions: lw leaf at `k` (Rocq `k`, value at Rocq `k+1` ↦ Lean `k`); c.bnez, c.li, c.ret
     consume no row item; SHORT continuation `k + 1` (Rocq `k+5`); LONG `holdPro` from `k + 1`
     (Rocq `k+3`), `lk->cpu` leaf at `k + 4` (Rocq `k+11`, value Rocq `k+12`), spills' data
     `k+1/2/3` (Rocq `k+5/7/9`), mycpu's spills `k+5/6` (Rocq `k+17/19`), reloads `k+7/8` (Rocq
     `k+28/30`), holding's reloads `k+9/10/11` (Rocq `k+36/38/40`), continuation `k + 12` (Rocq
     `k+43`) — in `KShort`, `KLong` and `wpdHolding`.
   * `RowHolding` has no `pretm`/`pret`/`nret` (AxSpinHd8 deviation 1), so `wpdHolding` drops
     these parameters.  Rocq's return-page premises (`Hinjm`/`Hstvm`/`Hinj`/`Hstv`), the section
     context `stv` and the Sail premise `va_first_read` are DROPPED; NEW premise (the pin, one
     hypothesis split on `hb`): `if hb then graphValue (gtAdGd GT) (i, k + 7) = some (stBytes 8
     (pch 0x1a)) ∧ graphValue (gtAdGd GT) (i, k + 9) = some (stBytes 8 ret) ∧ jalrTgt 0#12 ret =
     ret else jalrTgt 0#12 (gprVal rs0 AxSpinE8.r1) = ret` (the long arm is `holdPro`'s
     `Hvalm`/`Hval`/`Hret`; the short arm replaces Rocq's pinned return fetch at `k+5`, since the
     Lean c.ret leaf `AxSpinE6.XxRet` continues at `PC = jalrTgt 0 ra` with no stuck branch).
2. TYPES / SPELLING (as AxSpinHd8 deviation 2 / AxSpinHd9 deviation 3): `uint P` ↦ `paZ P`;
   `gpr_val` ↦ `gprVal`; `register_lookup PC rs` ↦ `rs .PC`; `uint r ≠ n` ↦ `r.toNat ≠ n`;
   `add_vec zero_reg x` ↦ `0#64 + x`; `(i,k) ↦ₐ P` ↦ `AxAnnot.annotOwn (i, k) P`;
   `mword_of_int n : mword 12` ↦ `n#12`; `r15` ↦ `15#5`; Rocq `if hb then … else …` in iProp and
   Prop ↦ Lean `if hb then … else …`.  The `let`s: `a0v` is `gprVal rs0 AxSpinE8.r10`, `hsp1` /
   `s0m` are AxSpinHd9's Lean-only abbrevs `AxSpinHd9.hsp1 rs0` / `AxSpinHd9.s0m rs0`,
   `va_ra`…`va_s0m` are inlined (as in `holdPro`).
3. INSTANCES / SECTION (as AxSpinHd9 deviation 4): `[InvGS_gen hlc GF]` (any `hlc`); the local
   instances `hA_pol`/`hA_G` are inlined as `xv6Pol GT` / `AxSpinX2.xG L GT nm`; `KShort`/`KLong`
   take the section context they use as explicit leading arguments (`L GT nm T satp0 i cpu Ψ`, as
   `AxSpinHd7.XLd`); the theorem's section variables are explicit arguments in AxSpinE6's order
   (+ `Htxm Htxh`).
4. TACTICS: `pcs`/`nz`/`vm_compute` ↦ `decide`; `zsimp` ↦ the file-local macro
   `ax_spin_hda_zsimp` (= AxSpinHd9's); `lia` ↦ `omega`; `zq` subsumed.  The proof case-splits
   `hb` first (Lean `if` in iProp does not reduce under the proof mode) and runs the common lw /
   c.bnez prefix in both arms.  `Print Assumptions` is not ported (the lint's axiom check covers
   it).

**Rocq → Lean name map.**  `imm13` `AxSpinHdA.imm13`, `c7` `AxSpinHdA.c7` (short generic names:
file-qualified; not in the duplicated-name table), `KShort` `KShort`, `KLong` `KLong`,
`wpd_holding` `wpdHolding`.  No Lean-only declarations (+ 1 local macro).

**Dropped:** nothing.  Rocq 5 definitions/lemmas (+ 2 local instances, inlined); Lean 5.
-/
import Weak.AxSpinHd2
import Weak.AxSpinHd2b
import Weak.AxSpinHd2c
import Weak.AxSpinHd6
import Weak.AxSpinHd6b
import Weak.AxSpinHd9

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `imm13`: c.bnez's branch offset (+6). -/
def AxSpinHdA.imm13 : BitVec 13 := sign_extend (m := 13) (3#8 +++ 0b0#1)
/-- Rocq `c7`: compressed register 7 (`a5`). -/
def AxSpinHdA.c7 : BitVec 5 := creg5 (.Cregidx 7#3)

/-- (Rocq `zsimp`) evaluate the closed `upd` tests. -/
local macro "ax_spin_hda_zsimp" loc:(ppSpace Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := decide) only [AxSpinE8.updSame, AxSpinE8.updOther, AxSpinE8.updZero]
    $[$loc]?)

section konts
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

/-- Rocq `KShort`: the SHORT continuation (locked = 0: return 0 at `k + 1`; deviation 1). -/
def KShort (L : Xlay) (GT : GdexecT) (nm : Xv6N) (T : PTree) (satp0 : BitVec 64) (i : Agent)
    (cpu : CPU) (Ψ : Athread → IProp GF) (k : Nat) (rs0 : RegFile) (ret : BitVec 64)
    (Olk : List (BitVec 8) → IProp GF) : IProp GF :=
  iprop(∀ (vlk : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
    ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = ret ∧ rs' .tlb = rs0 .tlb ∧
      gprVal rs' AxSpinE8.r10 = 0#64 ∧ gprVal rs' 15#5 = ldRes false 4 vlk ∧ vlk.length = 4 ∧
      graphValue (gtAdGd GT) (i, k) = some vlk ∧
      (∀ r : BitVec 5, r.toNat ≠ 10 → r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r)⌝ -∗
    Olk vlk -∗
    @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
      ⟨.PHart cpu (.pure ()) rs' none ib', k + 1⟩ Ψ)

/-- Rocq `KLong`: the LONG continuation (locked ≠ 0: return seqz (lk->cpu − mycpu()) at
`k + 12`; deviation 1). -/
def KLong (L : Xlay) (GT : GdexecT) (nm : Xv6N) (T : PTree) (satp0 : BitVec 64) (i : Agent)
    (cpu : CPU) (Ψ : Athread → IProp GF) (k : Nat) (rs0 : RegFile) (ret : BitVec 64)
    (Pra Ps0 Ps1 Pram Ps0m : BitVec 64) (Olk Ocpu : List (BitVec 8) → IProp GF) : IProp GF :=
  iprop(∀ (vlk vcpu vram vs0m vra vs0 vs1 : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
    ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = ret ∧ rs' .tlb = rs0 .tlb ∧
      gprVal rs' AxSpinE8.r10 =
        hres (0#64 + ldRes false 8 vcpu) (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4)) ∧
      gprVal rs' AxSpinE8.r2 = gprVal rs0 AxSpinE8.r2 ∧
      vlk.length = 4 ∧ vcpu.length = 8 ∧ vram.length = 8 ∧ vs0m.length = 8 ∧
      vra.length = 8 ∧ vs0.length = 8 ∧ vs1.length = 8 ∧
      gprVal rs' AxSpinE8.r1 = ldRes false 8 vra ∧ gprVal rs' AxSpinE8.r8 = ldRes false 8 vs0 ∧
      gprVal rs' AxSpinHd8.r9 = ldRes false 8 vs1 ∧
      (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
        r.toNat ≠ 10 → r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
      graphValue (gtAdGd GT) (i, k) = some vlk ∧ graphValue (gtAdGd GT) (i, k + 4) = some vcpu ∧
      graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
      graphData (gtAdGd GT) (i, k + 2) = some (stBytes 8 (gprVal rs0 AxSpinE8.r8)) ∧
      graphData (gtAdGd GT) (i, k + 3) = some (stBytes 8 (gprVal rs0 AxSpinHd8.r9)) ∧
      graphData (gtAdGd GT) (i, k + 5) = some (stBytes 8 (pch 0x1a)) ∧
      graphData (gtAdGd GT) (i, k + 6) = some (stBytes 8 (AxSpinHd9.s0m rs0)) ∧
      graphValue (gtAdGd GT) (i, k + 7) = some vram ∧
      graphValue (gtAdGd GT) (i, k + 8) = some vs0m ∧
      graphValue (gtAdGd GT) (i, k + 9) = some vra ∧
      graphValue (gtAdGd GT) (i, k + 10) = some vs0 ∧
      graphValue (gtAdGd GT) (i, k + 11) = some vs1⌝ -∗
    Olk vlk -∗ Ocpu vcpu -∗
    AxAnnot.annotOwn (GF := GF) (i, k + 7)
      iprop(⌜RLfact GT i (paZ Pram) (k + 7) (stBytes 8 (pch 0x1a))⌝) -∗
    AxAnnot.annotOwn (GF := GF) (i, k + 8)
      iprop(⌜RLfact GT i (paZ Ps0m) (k + 8) (stBytes 8 (AxSpinHd9.s0m rs0))⌝) -∗
    AxAnnot.annotOwn (GF := GF) (i, k + 9)
      iprop(⌜RLfact GT i (paZ Pra) (k + 9) (stBytes 8 (gprVal rs0 AxSpinE8.r1))⌝) -∗
    AxAnnot.annotOwn (GF := GF) (i, k + 10)
      iprop(⌜RLfact GT i (paZ Ps0) (k + 10) (stBytes 8 (gprVal rs0 AxSpinE8.r8))⌝) -∗
    AxAnnot.annotOwn (GF := GF) (i, k + 11)
      iprop(⌜RLfact GT i (paZ Ps1) (k + 11) (stBytes 8 (gprVal rs0 AxSpinHd8.r9))⌝) -∗
    @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
      ⟨.PHart cpu (.pure ()) rs' none ib', k + 12⟩ Ψ)

end konts

section hold
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
/-- Rocq `wpd_holding` (deviation 1: Stage C positions; the graph-value pin replaces the
return-fetch pins `Hinjm`/`Hstvm`/`Hinj`/`Hstv`/`va_first_read`). -/
theorem wpdHolding (k : Nat) (rs0 : RegFile) (ib0 : Ibch) (hb : Bool) (ret : BitVec 64)
    (plk pcl : Int) (Pra Ps0 Ps1 Pram Ps0m : BitVec 64)
    (Olk Ocpu : List (BitVec 8) → IProp GF) :
    -- the row
    RowHolding k (AxOpsem.grow (gtAdGd GT) i) hb plk pcl (paZ Pra) (paZ Ps0) (paZ Ps1)
      (paZ Pram) (paZ Ps0m) →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pram) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0m) →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = pch 0 → hitW rs0 (pch 0) → hitW rs0 (pcm 0) →
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) →
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) →
    -- the five stack slots
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm24) 8 Pra →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm24) 8 Pra →
    hitW rs0 (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm24) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm16) 8 Ps0 →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm16) 8 Ps0 →
    hitW rs0 (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm16) →
    dataAtS σi T (.Store .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm8) 8 Ps1 →
    dataAtS σi T (.Load .Data) (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm8) 8 Ps1 →
    hitW rs0 (AxSpinHd9.hsp1 rs0 + sign_extend (m := 64) AxSpinHd8.imm8) →
    dataAtS σi T (.Store .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immRa) 8 Pram →
    dataAtS σi T (.Load .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immRa) 8 Pram →
    hitW rs0 (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immRa) →
    dataAtS σi T (.Store .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immS0) 8 Ps0m →
    dataAtS σi T (.Load .Data)
      (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immS0) 8 Ps0m →
    hitW rs0 (AxSpinE8.sp1Of (AxSpinHd9.hsp1 rs0) + sign_extend (m := 64) AxSpinE8.immS0) →
    (∀ j : Nat, j < 8 → priv L (paZ Pra + (j : Int)) i) → ¬ L.xlText (paZ Pra) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0 + (j : Int)) i) → ¬ L.xlText (paZ Ps0) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps1 + (j : Int)) i) → ¬ L.xlText (paZ Ps1) →
    (∀ j : Nat, j < 8 → priv L (paZ Pram + (j : Int)) i) → ¬ L.xlText (paZ Pram) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0m + (j : Int)) i) → ¬ L.xlText (paZ Ps0m) →
    slotsDisj [paZ Pra, paZ Ps0, paZ Ps1, paZ Pram, paZ Ps0m] →
    -- the return addresses (Q20': graph-value pins; deviation 1)
    (if hb then
        graphValue (gtAdGd GT) (i, k + 7) = some (stBytes 8 (pch 0x1a)) ∧
        graphValue (gtAdGd GT) (i, k + 9) = some (stBytes 8 ret) ∧ jalrTgt 0#12 ret = ret
      else jalrTgt 0#12 (gprVal rs0 AxSpinE8.r1) = ret) →
    -- the caller's two load leaves and continuation
    ⊢ XLd (hlc := hlc) L GT nm T satp0 i cpu Ψ k (pch 0x00) 10#5 15#5 0#12 4
        (gprVal rs0 AxSpinE8.r10) Olk -∗
      (if hb then
          XLd (hlc := hlc) L GT nm T satp0 i cpu Ψ (k + 4) (pch 0x12) 10#5 15#5 16#12 8
            (gprVal rs0 AxSpinE8.r10) Ocpu ∗
          KLong (hlc := hlc) L GT nm T satp0 i cpu Ψ k rs0 ret Pra Ps0 Ps1 Pram Ps0m Olk Ocpu
        else KShort (hlc := hlc) L GT nm T satp0 i cpu Ψ k rs0 ret Olk) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hw8 Hnr_ra Hnr_s0 Hnr_s1 Hnr_ram Hnr_s0m Hc0 HPC0 Hhit0 Hhm0 Hhlk Hhlc
    HdaS_ra HdaL_ra Hh_ra HdaS_s0 HdaL_s0 Hh_s0 HdaS_s1 HdaL_s1 Hh_s1
    HdaS_ram HdaL_ram Hh_ram HdaS_s0m HdaL_s0m Hh_s0m
    Hpr_ra Hnt_ra Hpr_s0 Hnt_s0 Hpr_s1 Hnt_s1 Hpr_ram Hnt_ram Hpr_s0m Hnt_s0m HD Hpin
  have XR := XxReg L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XT := XxRet L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  obtain ⟨Hbr, HRp⟩ := HR
  have Hlen1 : k + 1 < (AxOpsem.grow (gtAdGd GT) i).length := by
    cases hb
    · exact HRp.1
    · have := HRp.1
      omega
  cases hb <;> simp only [↓reduceIte, Bool.false_eq_true] at Hpin HRp ⊢ <;>
    unfold XLd <;> iintro Hlk C
  all_goals
    -- ---- 0x00: c.lw a5,0(a0) — lk->locked, THROUGH THE CALLER'S LEAF (k) ----
    have Hpre : RetX cpu rs0 k ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ ∧
        ctrlOkSW T satp0 rs0 ∧ rs0 .PC = pch 0x00 ∧ hitW rs0 (pch 0x00) ∧
        gprVal rs0 10#5 = gprVal rs0 AxSpinE8.r10 ∧
        hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) ∧
        k + 1 ≤ (AxOpsem.grow (gtAdGd GT) i).length :=
      ⟨retxRefl cpu rs0 k ib0, Hc0, HPC0, Hhit0, rfl, Hhlk, by omega⟩
    iapply Hlk $$ %(⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ : Athread) %rs0 %Hpre
    iintro %vlk %rs1 %ib1 %Hlvlk %HG1 %Hgv1 Ho
    have HF1 := stepRegs T satp0 _ rs0 _ _ _ _ _ rs1 (fun _ => rfl) HG1
    have HPC1 : rs1 .PC = pch 0x02 := by rw [gbPc T satp0 _ _ _ _ _ _ HG1]; decide
    have Htl1 : rs1 .tlb = rs0 .tlb := gbTlb T satp0 _ _ _ _ _ _ HG1
    -- the row value of the lw fixes the branch
    have Hhb := Hbr
    obtain ⟨lb, vs, Hlb, Hv, Hhb⟩ := Hhb
    have Hv' : lblValue lb = some vlk := by
      rw [graphValue, AxWp.growLookup _ _ _ _ Hlb] at Hgv1
      exact Hgv1
    rw [Hv] at Hv'
    rw [Option.some.inj Hv'] at Hhb
    -- ---- 0x02: c.bnez a5,+6 (k+1) ----
    have Hcb := certBTYPE (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs1 (pch 0x02) true
      AxSpinHdA.imm13 0#5 AxSpinHdA.c7 .BNE (by decide)
    have Hg7 : gval AxSpinHdA.c7 rs1 = ldRes false 4 vlk := by
      rw [show AxSpinHdA.c7 = 15#5 by decide]
      unfold gval
      rw [if_neg (by decide)]
      show gprVal rs1 15#5 = _
      rw [HF1]
      ax_spin_hda_zsimp
    have Hg0 : gval 0#5 rs1 = 0#64 := by
      unfold gval
      rw [if_pos (by decide)]
      rfl
    simp only [brOt, Hg7, Hg0] at Hcb
    iapply (XR _ rs1 (k + 1) (pch 0x02) true h02 _ none (retxRefl cpu rs1 (k + 1) ib1)
      (gbCtrl T satp0 _ _ _ _ _ _ HG1) HPC1
      (hitWSvpn rs1 (pch 0x02) (pch 0) (by decide) (hitWAgree rs0 rs1 _ Htl1 Hhit0))
      (htok02 σi T satp0 Htxh) trivial rfFH02 Hcb Hlen1)
    iintro %rs2 %ib2 %HG2
    have HF2 := stepRegs0 T satp0 _ rs1 _ _ _ rs2 HF1 HG2
    have Htl2 : rs2 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG2).trans Htl1
    have HPC2 := gbPc T satp0 _ _ _ _ _ _ HG2
    simp only [AxSymCtl2.bcond, ← Hhb, ↓reduceIte, Bool.false_eq_true] at HPC2
  · -- ===== SHORT path: c.li a0,0; c.ret — the return at k+1 =====
    replace HPC2 : rs2 .PC = pch 0x04 := by rw [HPC2]; decide
    -- ---- 0x04: c.li a0,0 (k+1) ----
    have Hc := certAddi (ctrlOkSW T satp0) rs2 (pch 0x04) true 0#5 10#5
      (sign_extend (m := 12) (0#6)) (by decide)
    simp only [HF2] at Hc
    ax_spin_hda_zsimp at Hc
    iapply (XR _ rs2 (k + 1) (pch 0x04) true h04 _ _ (retxRefl cpu rs2 (k + 1) ib2)
      (gbCtrl T satp0 _ _ _ _ _ _ HG2) HPC2
      (hitWSvpn rs2 (pch 0x04) (pch 0) (by decide) (hitWAgree rs0 rs2 _ Htl2 Hhit0))
      (htok04 σi T satp0 Htxh) (AxSpinE8.owOkSome 10#5 _ (by decide)) rfFH04 Hc Hlen1)
    iintro %rs3 %ib3 %HG3
    have HF3 := stepRegs T satp0 _ rs2 _ _ _ _ _ rs3 HF2 HG3
    have HPC3 : rs3 .PC = pch 0x06 := by rw [gbPc T satp0 _ _ _ _ _ _ HG3]; decide
    have Htl3 : rs3 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG3).trans Htl2
    -- ---- 0x06: c.ret (k+1; Q20': no stuck branch, the target is the entry ra) ----
    iapply (XT _ rs3 (k + 1) (pch 0x06) (retxRefl cpu rs3 (k + 1) ib3)
      (gbCtrl T satp0 _ _ _ _ _ _ HG3) HPC3
      (hitWSvpn rs3 (pch 0x06) (pch 0) (by decide) (hitWAgree rs0 rs3 _ Htl3 Hhit0))
      (htok06 σi T satp0 Htxh) rfFH06 Hlen1)
    iintro %rs' %ib' %HGr
    have HFr := stepRegs0 T satp0 _ rs3 _ _ _ rs' HF3 HGr
    unfold KShort
    iapply C $$ %vlk %rs' %ib' [] Ho
    ipureintro
    refine ⟨gbCtrl T satp0 _ _ _ _ _ _ HGr, ?_, (gbTlb T satp0 _ _ _ _ _ _ HGr).trans Htl3, ?_, ?_,
      Hlvlk, Hgv1, ?_⟩
    · -- PC = ret: the c.ret target is the entry ra, pinned by `Hpin`
      rw [gbPc T satp0 _ _ _ _ _ _ HGr]
      show jalrTgt 0#12 (gprVal rs3 1#5) = ret
      rw [HF3]
      ax_spin_hda_zsimp
      exact Hpin
    · -- a0 = 0
      rw [HFr]
      ax_spin_hda_zsimp
      decide
    · -- a5 = sext32 vlk
      rw [HFr]
      ax_spin_hda_zsimp
    · -- every other GPR kept
      intro r Hr10 Hr15
      rw [HFr]
      by_cases E0 : r.toNat = 0
      · rw [AxSpinE8.updZero _ _ _ _ E0, AxSpinE8.gprValZero rs0 r E0]
      · have n10 : r ≠ 10#5 := fun h => Hr10 (by rw [h]; rfl)
        have n15 : r ≠ 15#5 := fun h => Hr15 (by rw [h]; rfl)
        simp (disch := assumption) only [AxSpinE8.updOther]
  · -- ===== LONG path: holding+0x08 … the call … the return at k+12 =====
    replace HPC2 : rs2 .PC = pch 0x08 := by rw [HPC2]; decide
    obtain ⟨Hvalm, Hval, Hret⟩ := Hpin
    icases C with ⟨Hcpu, C⟩
    have Hkeep2 : ∀ r : BitVec 5, r.toNat ≠ 15 → gprVal rs2 r = gprVal rs0 r := by
      intro r Hr
      rw [HF2]
      by_cases E0 : r.toNat = 0
      · rw [AxSpinE8.updZero _ _ _ _ E0, AxSpinE8.gprValZero rs0 r E0]
      · have n15 : r ≠ 15#5 := fun h => Hr (by rw [h]; rfl)
        simp (disch := assumption) only [AxSpinE8.updOther]
    have Hsp2 : gprVal rs2 AxSpinE8.r2 = gprVal rs0 AxSpinE8.r2 := Hkeep2 _ (by decide)
    have Ha02 : gprVal rs2 AxSpinE8.r10 = gprVal rs0 AxSpinE8.r10 := Hkeep2 _ (by decide)
    have Hr12 : gprVal rs2 AxSpinE8.r1 = gprVal rs0 AxSpinE8.r1 := Hkeep2 _ (by decide)
    have Hr82 : gprVal rs2 AxSpinE8.r8 = gprVal rs0 AxSpinE8.r8 := Hkeep2 _ (by decide)
    have Hr92 : gprVal rs2 AxSpinHd8.r9 = gprVal rs0 AxSpinHd8.r9 := Hkeep2 _ (by decide)
    have Hr42 : gprVal rs2 AxSpinE8.r4 = gprVal rs0 AxSpinE8.r4 := Hkeep2 _ (by decide)
    have Hhsp : AxSpinHd9.hsp1 rs2 = AxSpinHd9.hsp1 rs0 := by
      unfold AxSpinHd9.hsp1
      rw [Hsp2]
    have Hs0m : AxSpinHd9.s0m rs2 = AxSpinHd9.s0m rs0 := by
      unfold AxSpinHd9.s0m
      rw [Hhsp]
    have HP := holdPro L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxh Ψ HΨmid
      k rs2 ib2 ret plk pcl Pra Ps0 Ps1 Pram Ps0m Ocpu
    rw [Hs0m, Hhsp, Hsp2, Ha02, Hr12, Hr82, Hr92, Hr42] at HP
    unfold XLd at HP
    iapply (HP ⟨Hbr, HRp⟩ Hw8 Hnr_ra Hnr_s0 Hnr_s1 Hnr_ram Hnr_s0m HD
      (gbCtrl T satp0 _ _ _ _ _ _ HG2) HPC2
      (hitWAgree rs0 rs2 _ Htl2 Hhit0) (hitWAgree rs0 rs2 _ Htl2 Hhm0)
      (hitWAgree rs0 rs2 _ Htl2 Hhlc)
      HdaS_ra HdaL_ra (hitWAgree rs0 rs2 _ Htl2 Hh_ra)
      HdaS_s0 HdaL_s0 (hitWAgree rs0 rs2 _ Htl2 Hh_s0)
      HdaS_s1 HdaL_s1 (hitWAgree rs0 rs2 _ Htl2 Hh_s1)
      HdaS_ram HdaL_ram (hitWAgree rs0 rs2 _ Htl2 Hh_ram)
      HdaS_s0m HdaL_s0m (hitWAgree rs0 rs2 _ Htl2 Hh_s0m)
      Hpr_ra Hnt_ra Hpr_s0 Hnt_s0 Hpr_s1 Hnt_s1 Hpr_ram Hnt_ram Hpr_s0m Hnt_s0m
      Hvalm Hval Hret) $$ Hcpu
    iintro %vcpu %vram %vs0m %vra %vs0 %vs1 %rs' %ib' %⟨Hc', HPC', Htl', Ha0', Hsp', Hlvcpu,
      Hlvram, Hlvs0m, Hlvra, Hlvs0, Hlvs1, Hr1', Hr8', Hr9', Hkeep', Hgv4, Hgd1, Hgd2, Hgd3, Hgd5,
      Hgd6, Hgv7, Hgv8, Hgv9, Hgv10, Hgv11⟩ Hc H7 H8 H9 H10 H11
    unfold KLong
    iapply C $$ %vlk %vcpu %vram %vs0m %vra %vs0 %vs1 %rs' %ib' [] Ho Hc H7 H8 H9 H10 H11
    ipureintro
    refine ⟨Hc', HPC', Htl'.trans Htl2, Ha0', Hsp', Hlvlk, Hlvcpu, Hlvram, Hlvs0m, Hlvra, Hlvs0,
      Hlvs1, Hr1', Hr8', Hr9', ?_, Hgv1, Hgv4, Hgd1, Hgd2, Hgd3, Hgd5, Hgd6, Hgv7, Hgv8, Hgv9,
      Hgv10, Hgv11⟩
    intro r Hr1 Hr2 Hr8 Hr9 Hr10 Hr15
    rw [Hkeep' r Hr1 Hr2 Hr8 Hr9 Hr10 Hr15, Hkeep2 r Hr15]

end hold

end Weak
