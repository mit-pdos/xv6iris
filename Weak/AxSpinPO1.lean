/-
Weak: **PHASE 5, stage 5: push_off's HEAD** — xv6's REAL `push_off` from its entry to the
data-dependent branch `if(c->noff == 0)` (`+ 0x00 … + 0x16`: frame; the three callee-saved
spills; `s0 := frame`; `csrrci a5,sstatus,2` (intr_off); `s1 := a5`; `jal mycpu`;
`lw a5,120(a0)` (noff); `c.beqz a5`) as a POSITIONAL CPS WPd at the joint instance Ixv6,
interrupts off (`ctrlOkSW`: S-mode, SIE = 0 — csrrci then only READS sstatus, see AxSpinPOc),
WARM TLB.  Composed with `AxSpinE8.wpdMycpu` at the inner position `k + 3`.

Rocq: `iris/AxSpinPO1.v` @ xxvzwolszwmp.

## The Rocq header, in substance (as restated under Stage C)

`wpdPoHead k b`: for every `k`, every branch bit `b` (`b` = "noff == 0") and every row matching
`AxSpinPOr.poHead …` at `k` (8 items under Stage C: the three spills at `k .. k+2`; mycpu's four
events at `k+3 .. k+6`; the `noff` load at `k+7`) whose `noff` load's graph value makes the
branch take arm `b`:
  WPd (boundary at k, regs rs0) {{Ψ}}
  ⇐ (∀ vn m rs' ib',
       ⌜regime ∧ PC = (if b then + 0x2c else + 0x18) ∧ TLB kept ∧ a0 = mycpuRet tp ∧
        sp = spo sp0 ∧ s1 = sstatusRead m with m's SIE = 0 ∧ a5 = the noff load ∧ every other
        GPR but ra / s0 kept ∧ the three spills' row data = ra0 / s00 / s10's bytes ∧ the noff
        load's graph value = vn ∧ (noff == 0) = b⌝
       -∗ WPd (boundary at k + 8, regs rs') {{Ψ}})
— the branch is `AxSpinPOx.XxPin` (Option V: the continuation is called on the arm `b` pinned
by the noff load's GRAPH VALUE; no stuck branch).
§1 premise bundles `AxSpinPO1.slot8` / `fld4` (translation both ways, warm TLB, privacy, not
   text) and the bit lemma `ienaZero` (the intena value computed from an SIE = 0 sstatus is 0).
PREMISES (beyond AxSpinE8's style): the entry is at SIE = 0 (the plan's "interrupts off
throughout"); mycpu's slots / noff field bundles; the value pins (deviation 1).

GRAPH-VALUE PINNING (Q20', provisional Option V, `notes/weak-port-q20-offrow.md` §C.2 item 4;
Rocq: "TEMPORARY ASSUMPTION — ROW PINNING", owner decision 2026-10-03).  `poHead` fixes which
row positions are loads / stores and the data base addresses; mycpu's RETURN (to
`push_off + 0x14`) is pinned by its ra reload's GRAPH VALUE (`Hval14`), and the ARM of the
`beqz` by the noff load's GRAPH VALUE (`Hvb`).  The theorem proves nothing about a graph whose
values differ; the follow-up ROW-INTEGRITY theorem is to discharge the value pins.  Ownership is
load-bearing for data values.

## Stage 2 P-FORM (Lean-only; notes/weak-lb-thm2-stage2.md §B, §C, Q-S2-1/2; as AxSpinE8)

`wpdPoHeadP` is `wpdPoHead` on a PREFIX row: `RowShP k row (poHead …)`, no length premise,
`Hval14` GUARDED (`k + 5 < LEN → …`; `Hvb` is already value-conditional — vacuous at an absent
position), and the WINDOWED, RESOURCE-FREE row-end hook
  `HΨend : ∀ k', k ≤ k' → k' ≤ k + 8 → (grow (gtAdGd GT) i).length ≤ k' →
     ∀ pr : Pexv6, ⊢ wpdM … .MaybeStuck i ⟨pr, k'⟩ Ψ`.
One `by_cases` per row position (`k` … `k + 3`, `k + 7`, `k + 8`); mycpu (`[k + 3, k + 7]`)
is `AxSpinE8.wpdMycpuP`, handed the sub-window of the hook.  push_off has no designated cut.
The noff load (+ 0x14, row position `k + 7`, reads the boot image) runs the CONDITIONAL GENESIS
leaf `AxSpinPO3.xxLd4C` instead of `XxLd4`; the continuation's last wand is
`∀ _ : AxSpinLd4P.noWrBefore row (k + 7) (paZ Pn) 4, (i, k + 7) ↦ₐ ⌜genFact4 GT i (paZ Pn) (k + 7)⌝`
(see AxSpinPO3's header for why it is conditional).  The continuation is reached only when
`k + 8 < LEN`.  `wpdPoHead` keeps its exact statement and is the corollary (hook vacuous under
`k + 8 < LEN`; annotation dropped).

## Deviations from Rocq

1. O2 STAGE C / Q20' (provisional Option V; protocol "Cross-file facts" Q20', AxSpinPOr,
   AxSpinPOx (XxPin Option V), AxSpinPO3 (wpdPoTail pins), AxSpinE8 (Hval/Hret) entries):
   * the row shape is `poHead (paZ Pra) (paZ Ps0) (paZ Ps1) (paZ Pmra) (paZ Pms0) (paZ Pn)`
     (AxSpinPOr deviation 1: no fetch items); the parameters `p14` (mycpu's return fetch) and
     `pb` (the arm target's fetch) are DROPPED ("Stage C: no row item pins a fetch").
   * POSITIONS (AxSpinPOr Stage C windows; a fetch consumes no row item): the spills at `k`,
     `k + 1`, `k + 2` (Rocq `k + 2 / 4 / 6`, row data), the register-only `c.addi4spn`,
     `csrrci`, `c.mv`, `jal` at `k + 3`, mycpu at `k + 3` (Rocq `k + 11`), its continuation at
     `k + 7` (Rocq `k + 29`), the `noff` load at `k + 7` (Rocq `k + 30`, graph value), the
     `c.beqz` at `k + 8` and the continuation at `k + 8` (Rocq `k + 32`).
   * Rocq's premise "row item `k + 32` is the PINNED fetch of the arm's target"
     (`∃ lb aq, row !! (k+32) = Some lb ∧ aident_rd … = Some (aq, pb, 4)`) is REPLACED by the
     length premise `k + 8 < row.length` (the boundary after the `beqz` needs a next row item,
     `XxPin`'s `k < LEN`).
   * the two `fpin` premises (`fpin T stv (ppo 0x14) p14`, `fpin T stv nxt pb`), the section
     context `stv` and the Sail premise `va_first_read` are DROPPED; NEW value pins (Q20'):
     `Hval14 : graphValue (gtAdGd GT) (i, k + 5) = some (stBytes 8 (AxSpinPO.ppo 0x14))`
     (mycpu's ra reload — `AxSpinE8.wpdMycpu`'s `Hval` at `k + 3`; its `Hret` is decided at the
     literal) and `Hvb : ∀ vn, graphValue (gtAdGd GT) (i, k + 7) = some vn →
     (ldRes false 4 vn == zero_reg) = b` (the noff load's value picks the arm; Rocq's
     "the other arm is row-stuck" becomes a plain case on the value, `AxSpinPOx` deviation 3).
     The continuation's conjunct `(ldRes false 4 vn == zero_reg) = b` is kept (now from `Hvb`).
2. `land1_tb0` (Rocq bit lemma `Z.land y 1 = Z.b2z (Z.testbit y 0)`) is DROPPED: its only use is
   Rocq's `iena_zero` proof (no other weak file uses it), and `ienaZero` is proved by
   `bv_decide` (the `Int` bitwise API it states is Mathlib's).
3. TYPES / SPELLING (as AxSpinPO3 deviation 3): `uint P` ↦ `paZ P`; `gpr_val` ↦ `gprVal`;
   `register_lookup PC rs` ↦ `rs .PC`; `uint r ≠ n` ↦ `r.toNat ≠ n`; `eq_vec a b` ↦ `a == b`;
   `eq_vec (_get_Mstatus_SIE m) 'b"1" = false` ↦ `(_get_Mstatus_SIE m == 1#1) = false`;
   `register_lookup mstatus rs5` ↦ `rs5 .mstatus`; `sstatus_read` ↦ `sstatusRead`;
   `and_vec` ↦ `&&&`; `subrange_vec_dec v (log2_xlen - 1) 0` ↦
   `Sail.BitVec.extractLsb v (Functions.log2_xlen -i 1) 0`; `ppo_2c_18` is stated as Rocq;
   the `let`s are inlined: `spb` ↦ `spo (gprVal rs0 AxSpinE8.r2)`, `tp` ↦
   `gprVal rs0 AxSpinE8.r4`, `nxt` ↦ `if b then AxSpinPO.ppo 0x2c else AxSpinPO.ppo 0x18`;
   `add_vec (sp1_of spb) (sign_extend' 64 imm_ra)` ↦ `AxSpinE8.sp1Of … + sign_extend (m := 64)
   AxSpinE8.immRa`; `imm24/16/8` ↦ `AxSpinPO3.imm24/16/8`; `Interface.Ret tt` ↦ `.pure ()`.
4. INSTANCES / SECTION (as AxSpinPO3 deviation 4): `[InvGS_gen hlc GF]` (any `hlc`); the local
   instances `ph_pol`/`ph_G` are inlined as `xv6Pol GT` / `AxSpinX2.xG L GT nm`; section
   variables are explicit arguments in AxSpinE6's order (+ `Htxm Htxp`).
5. TACTICS: `pcs`/`nz`/`zq` ↦ `decide`; `zsimp` ↦ the file-local macro `ax_spin_po1_zsimp`
   (= AxSpinE8's); `lia` ↦ `omega`.  The proof uses literal register indices (`8#5`, `15#5`,
   `0#5`) where Rocq uses `rS0` / `rc7` / `rz` (equal by `rfl`).  The trailing
   `Print Assumptions` is not ported.

**Rocq → Lean name map.**  `slot8` `AxSpinPO1.slot8` (duplicated name: file-qualified), `fld4`
`fld4`, `iena` `iena`, `iena_zero` `ienaZero`, `ppo_2c_18` `ppo2c18`, `rS0` `AxSpinPO1.rS0`
(duplicated), `rc7` `rc7`, `rz` `AxSpinPO1.rz` (duplicated), `spo` `spo`, `wpd_po_head`
`wpdPoHead`.  The local instances `ph_pol`, `ph_G` are inlined (deviation 4).  Lean-only
(stage 2, grepped unique): `wpdPoHeadP` (+ 1 local macro).

**Dropped:** `land1_tb0` (deviation 2).  Rocq 11 definitions/lemmas + 2 local instances;
Lean 10.
-/
import Weak.AxSpinPO3
import Weak.AxSpinPOm
import Weak.AxSpinPOt1
import Weak.AxSpinE8
import Weak.AxSpinRowP
import Weak.AxSpinLd4P

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. Premise bundles, bit lemma -/

/-- Rocq `slot8` (duplicated name: file-qualified): an 8-byte private stack slot. -/
def AxSpinPO1.slot8 (σi : ExecSt) (T : PTree) (L : Xlay) (i : Agent) (rs : RegFile)
    (va P : BitVec 64) : Prop :=
  dataAtS σi T (.Store .Data) va 8 P ∧ dataAtS σi T (.Load .Data) va 8 P ∧ hitW rs va ∧
  (∀ j : Nat, j < 8 → priv L (paZ P + (j : Int)) i) ∧ ¬ L.xlText (paZ P)

/-- Rocq `fld4`: a 4-byte private cpu field. -/
def fld4 (σi : ExecSt) (T : PTree) (L : Xlay) (i : Agent) (rs : RegFile) (va P : BitVec 64) :
    Prop :=
  dataAtS σi T (.Store .Data) va 4 P ∧ dataAtS σi T (.Load .Data) va 4 P ∧ hitW rs va ∧
  (∀ j : Nat, j < 4 → priv L (paZ P + (j : Int)) i) ∧ ¬ L.xlText (paZ P)

/-- Rocq `iena`: the intena value push_off computes, `(sstatus >> 1) & 1`. -/
def iena (v : BitVec 64) : BitVec 64 :=
  shift_bits_right v (Sail.BitVec.extractLsb (1#6) (Functions.log2_xlen -i 1) 0) &&&
    sign_extend (m := 64) (sign_extend (m := 12) (1#6))

/-- Rocq `iena_zero` (deviation 2: by `bv_decide`). -/
theorem ienaZero (m : BitVec 64) :
    (_get_Mstatus_SIE m == 1#1) = false → iena (sstatusRead m) = 0#64 := by
  intro hSIE
  have e1 : ∀ v : BitVec 64, iena v = (v >>> 1) &&& 1#64 := by
    intro v
    unfold iena shift_bits_right
    rw [BitVec.ushiftRight_eq',
      show (Sail.BitVec.extractLsb (1#6) (Functions.log2_xlen -i 1) 0).toNat = 1 by decide,
      show sign_extend (m := 64) (sign_extend (m := 12) (1#6)) = 1#64 by decide]
  rw [e1]
  unfold sstatusRead lower_mstatus
  simp only [Mk_Sstatus,
    _update_Sstatus_SIE, _update_Sstatus_SPIE, _update_Sstatus_SPP, _update_Sstatus_VS,
    _update_Sstatus_FS, _update_Sstatus_XS, _update_Sstatus_SUM, _update_Sstatus_MXR,
    _update_Sstatus_SPELP, _update_Sstatus_UXL, _update_Sstatus_SD,
    _get_Mstatus_SIE, _get_Mstatus_SPIE, _get_Mstatus_SPP, _get_Mstatus_VS,
    _get_Mstatus_FS, _get_Mstatus_XS, _get_Mstatus_SUM, _get_Mstatus_MXR,
    _get_Mstatus_SPELP, _get_Mstatus_UXL, _get_Mstatus_SD,
    Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', Sail.BitVec.extractLsb,
    BitVec.extractLsb, zeros] at hSIE ⊢
  bv_decide

/-- Rocq `ppo_2c_18`. -/
theorem ppo2c18 : AxSpinPO.ppo 0x2c ≠ AxSpinPO.ppo 0x18 := by decide

/-- Rocq `rS0` (duplicated name): `s0`. -/
def AxSpinPO1.rS0 : BitVec 5 := zero_extend (m := 5) (1#1 +++ 0#3)
/-- Rocq `rc7`: `a5`. -/
def rc7 : BitVec 5 := zero_extend (m := 5) (1#1 +++ 7#3)
/-- Rocq `rz` (duplicated name): `zero`. -/
def AxSpinPO1.rz : BitVec 5 := zero_extend (m := 5) 0b00#2
/-- Rocq `spo`: push_off's frame, `sp0 - 32`. -/
def spo (sp0 : BitVec 64) : BitVec 64 := sp0 + sign_extend (m := 64) (sign_extend (m := 12) (32#6))

/-- (Rocq `zsimp`) evaluate the closed `upd` tests. -/
local macro "ax_spin_po1_zsimp" loc:(ppSpace Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := decide) only [AxSpinE8.updSame, AxSpinE8.updOther, AxSpinE8.updZero]
    $[$loc]?)

/-! # 2. THE HEAD -/

section pohead
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
variable (Htxm : mycpuText σi T) (Htxp : pushOffText σi T)
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

set_option maxHeartbeats 1600000 in
include HL Hcons hmode hasid hppn Hfix Htxm Htxp HΨmid in
/-- (Lean-only, stage 2) THE P-FORM of `wpdPoHead` on a PREFIX row (`RowShP`; mycpu's return pin
guarded by position): at each row position of the head window a `by_cases` on
`LEN ≤ position`; the row-end case is the WINDOWED hook `HΨend` over `[k, k + 8]` (mycpu's
sub-window `[k + 3, k + 7]` is handed on to `wpdMycpuP`).  The noff load runs the conditional
genesis leaf `AxSpinPO3.xxLd4C` (its `genFact4` annotation is handed on).  The continuation is
reached only when `k + 8 < LEN`. -/
theorem wpdPoHeadP (k : Nat) (b : Bool) (rs0 : RegFile) (ib0 : Ibch)
    (Pra Ps0 Ps1 Pmra Pms0 Pn : BitVec 64) :
    -- the row
    RowShP k (AxOpsem.grow (gtAdGd GT) i)
      (poHead (paZ Pra) (paZ Ps0) (paZ Ps1) (paZ Pmra) (paZ Pms0) (paZ Pn)) →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pmra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pms0) →
    noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = AxSpinPO.ppo 0 → hitW rs0 (AxSpinPO.ppo 0) →
    hitW rs0 (pcm 0) →
    -- the slots and the noff field
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm24) Pra →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm16) Ps0 →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm8) Ps1 →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immRa) Pmra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immS0) Pms0 →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) Pn →
    dj (paZ Pms0) 8 (paZ Pmra) 8 →
    -- the value pins (Q20': mycpu's ra reload and the noff load; deviation 1)
    (k + 5 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, k + 5) = some (stBytes 8 (AxSpinPO.ppo 0x14))) →
    (∀ vn, graphValue (gtAdGd GT) (i, k + 7) = some vn → (ldRes false 4 vn == zero_reg) = b) →
    -- the row-end hook (stage 2, design §B / Q-S2-2; windowed)
    (∀ k' : Nat, k ≤ k' → k' ≤ k + 8 → (AxOpsem.grow (gtAdGd GT) i).length ≤ k' →
      ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    ⊢ (∀ (vn : List (BitVec 8)) (m : BitVec 64) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧
          rs' .PC = (if b then AxSpinPO.ppo 0x2c else AxSpinPO.ppo 0x18) ∧
          rs' .tlb = rs0 .tlb ∧
          gprVal rs' AxSpinE8.r10 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) ∧
          gprVal rs' AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) ∧
          gprVal rs' AxSpinPOr.r9 = sstatusRead m ∧ (_get_Mstatus_SIE m == 1#1) = false ∧
          vn.length = 4 ∧ gprVal rs' AxSpinE8.r15 = ldRes false 4 vn ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
            r.toNat ≠ 10 → r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
          graphData (gtAdGd GT) (i, k) = some (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs0 AxSpinE8.r8)) ∧
          graphData (gtAdGd GT) (i, k + 2) = some (stBytes 8 (gprVal rs0 AxSpinPOr.r9)) ∧
          graphValue (gtAdGd GT) (i, k + 7) = some vn ∧ (ldRes false 4 vn == zero_reg) = b⌝ -∗
        (∀ _ : AxSpinLd4P.noWrBefore (AxOpsem.grow (gtAdGd GT) i) (k + 7) (paZ Pn) 4,
          AxAnnot.annotOwn (GF := GF) (i, k + 7)
            iprop(⌜AxSpinLd4P.genFact4 GT i (paZ Pn) (k + 7)⌝)) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 8⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hw8 Hnr_mra Hnr_ms0 Hnrn Hc0 HPC0 Hhit0 HhitM
    ⟨HdaS_ra, _, Hh_ra, Hpr_ra, _⟩ ⟨HdaS_s0, _, Hh_s0, Hpr_s0, _⟩ ⟨HdaS_s1, _, Hh_s1, Hpr_s1, _⟩
    ⟨HdaS_mra, HdaL_mra, Hh_mra, Hpr_mra, Hnt_mra⟩ ⟨HdaS_ms0, HdaL_ms0, Hh_ms0, Hpr_ms0, Hnt_ms0⟩
    ⟨_, HdaL_n, Hh_n, Hpr_n, Hnt_n⟩ Hdm Hval14 Hvb HΨend
  iintro C
  -- row end at k
  by_cases E0 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k
  · iclear C
    iapply (HΨend _ (by omega) (by omega) (by omega) _)
  obtain ⟨T00, T02, T04, T06, T08, T0a, T0e, T10, T14, T16, -⟩ := Htxp
  have XR := XxReg L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XS := XxSt L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XM := XxRegm L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XL4 := AxSpinPO3.xxLd4C L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XP := XxPin L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have WM := wpdMycpuP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Ψ HΨmid
  -- ---- + 0x00: c.addi sp,-32 (row position k) ----
  iapply (XR _ rs0 k (AxSpinPO.ppo 0x00) true q00 none
    (some (2#5, spo (gprVal rs0 AxSpinE8.r2)))
    (retxRefl cpu rs0 k ib0) Hc0 HPC0
    (hitWSvpn rs0 (AxSpinPO.ppo 0x00) (AxSpinPO.ppo 0) (by decide) Hhit0)
    (tw1101 σi T satp0 _ T00) (AxSpinE8.owOkSome 2#5 _ (by decide))
    (rfFOfRf0 _ (rf0Addi _ _ _))
    (certAddi _ rs0 (AxSpinPO.ppo 0x00) true 2#5 2#5 _ (by decide)) (by omega))
  iintro %rs1 %ib1 %HG1
  have HF1 := stepRegs T satp0 _ rs0 _ _ _ _ _ rs1 (fun _ => rfl) HG1
  have HPC1 : rs1 .PC = AxSpinPO.ppo 0x02 := by rw [gbPc T satp0 _ _ _ _ _ _ HG1]; decide
  have Htl1 : rs1 .tlb = rs0 .tlb := gbTlb T satp0 _ _ _ _ _ _ HG1
  have Esp1 : gprVal rs1 AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) := by
    rw [HF1]; ax_spin_po1_zsimp
  -- ---- + 0x02: c.sdsp ra,24(sp) (spill at k) ----
  iapply (XS _ rs1 k (AxSpinPO.ppo 0x02) true AxSpinPO3.imm24 1#5 2#5
    (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm24) Pra
    (retxRefl cpu rs1 k ib1) (gbCtrl T satp0 _ _ _ _ _ _ HG1) HPC1
    (hitWSvpn rs1 (AxSpinPO.ppo 0x02) (AxSpinPO.ppo 0) (by decide)
      (hitWAgree rs0 rs1 _ Htl1 Hhit0))
    (twEc06 σi T satp0 _ T02) (by rw [Esp1]) HdaS_ra
    (hitWAgree rs0 rs1 _ Htl1 Hh_ra) Hpr_ra Hw8 (by omega))
  iintro %rs2 %ib2 %HG2 %Hgd0
  have HF2 := stepRegs0 T satp0 _ rs1 _ _ _ rs2 HF1 HG2
  have HPC2 : rs2 .PC = AxSpinPO.ppo 0x04 := by rw [gbPc T satp0 _ _ _ _ _ _ HG2]; decide
  have Htl2 : rs2 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG2).trans Htl1
  have Esp2 : gprVal rs2 AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) := by
    rw [HF2]; ax_spin_po1_zsimp
  -- row end at k + 1
  by_cases E1 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 1
  · iclear C
    iapply (HΨend _ (by omega) (by omega) (by omega) _)
  -- ---- + 0x04: c.sdsp s0,16(sp) (spill at k+1) ----
  iapply (XS _ rs2 (k + 1) (AxSpinPO.ppo 0x04) true AxSpinPO3.imm16 8#5 2#5
    (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm16) Ps0
    (retxRefl cpu rs2 (k + 1) ib2) (gbCtrl T satp0 _ _ _ _ _ _ HG2) HPC2
    (hitWSvpn rs2 (AxSpinPO.ppo 0x04) (AxSpinPO.ppo 0) (by decide)
      (hitWAgree rs0 rs2 _ Htl2 Hhit0))
    (twE822 σi T satp0 _ T04) (by rw [Esp2]) HdaS_s0
    (hitWAgree rs0 rs2 _ Htl2 Hh_s0) Hpr_s0 Hw8 (by omega))
  iintro %rs3 %ib3 %HG3 %Hgd1
  have HF3 := stepRegs0 T satp0 _ rs2 _ _ _ rs3 HF2 HG3
  have HPC3 : rs3 .PC = AxSpinPO.ppo 0x06 := by rw [gbPc T satp0 _ _ _ _ _ _ HG3]; decide
  have Htl3 : rs3 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG3).trans Htl2
  have Esp3 : gprVal rs3 AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) := by
    rw [HF3]; ax_spin_po1_zsimp
  -- row end at k + 2
  by_cases E2 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 2
  · iclear C
    iapply (HΨend _ (by omega) (by omega) (by omega) _)
  -- ---- + 0x06: c.sdsp s1,8(sp) (spill at k+2) ----
  iapply (XS _ rs3 (k + 2) (AxSpinPO.ppo 0x06) true AxSpinPO3.imm8 9#5 2#5
    (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm8) Ps1
    (retxRefl cpu rs3 (k + 2) ib3) (gbCtrl T satp0 _ _ _ _ _ _ HG3) HPC3
    (hitWSvpn rs3 (AxSpinPO.ppo 0x06) (AxSpinPO.ppo 0) (by decide)
      (hitWAgree rs0 rs3 _ Htl3 Hhit0))
    (twE426 σi T satp0 _ T06) (by rw [Esp3]) HdaS_s1
    (hitWAgree rs0 rs3 _ Htl3 Hh_s1) Hpr_s1 Hw8 (by omega))
  iintro %rs4 %ib4 %HG4 %Hgd2
  have HF4 := stepRegs0 T satp0 _ rs3 _ _ _ rs4 HF3 HG4
  have HPC4 : rs4 .PC = AxSpinPO.ppo 0x08 := by rw [gbPc T satp0 _ _ _ _ _ _ HG4]; decide
  have Htl4 : rs4 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG4).trans Htl3
  -- row end at k + 3
  by_cases E3 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 3
  · iclear C
    iapply (HΨend _ (by omega) (by omega) (by omega) _)
  -- ---- + 0x08: c.addi4spn s0,sp,32 (k+3) ----
  have Hc5 := certAddi (ctrlOkSW T satp0) rs4 (AxSpinPO.ppo 0x08) true 2#5 8#5
    (caddi4spnImm 8#8) (by decide)
  simp only [HF4] at Hc5
  ax_spin_po1_zsimp at Hc5
  iapply (XR _ rs4 (k + 3) (AxSpinPO.ppo 0x08) true q08 _ _
    (retxRefl cpu rs4 (k + 3) ib4) (gbCtrl T satp0 _ _ _ _ _ _ HG4) HPC4
    (hitWSvpn rs4 (AxSpinPO.ppo 0x08) (AxSpinPO.ppo 0) (by decide)
      (hitWAgree rs0 rs4 _ Htl4 Hhit0))
    (tw1000 σi T satp0 _ T08) (AxSpinE8.owOkSome 8#5 _ (by decide))
    (rfFOfRf0 _ (rf0Addi _ _ _)) Hc5 (by omega))
  iintro %rs5 %ib5 %HG5
  have HF5 := stepRegs T satp0 _ rs4 _ _ _ _ _ rs5 HF4 HG5
  have HPC5 : rs5 .PC = AxSpinPO.ppo 0x0a := by rw [gbPc T satp0 _ _ _ _ _ _ HG5]; decide
  have Htl5 : rs5 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG5).trans Htl4
  -- ---- + 0x0a: csrrci a5,sstatus,2 — intr_off (SIE already 0: a READ) (k+3) ----
  have HSIE : (_get_Mstatus_SIE (rs5 .mstatus) == 1#1) = false := by
    obtain ⟨⟨-, -, -, -, -, -, -, -, H, -⟩, -⟩ := gbCtrl T satp0 _ _ _ _ _ _ HG5
    exact H
  iapply (XM _ rs5 (k + 3) (AxSpinPO.ppo 0x0a) false q0a none
    (some (15#5, sstatusRead (rs5 .mstatus)))
    (retxRefl cpu rs5 (k + 3) ib5) (gbCtrl T satp0 _ _ _ _ _ _ HG5) HPC5
    (hitWSvpn rs5 (AxSpinPO.ppo 0x0a) (AxSpinPO.ppo 0) (by decide)
      (hitWAgree rs0 rs5 _ Htl5 Hhit0))
    (tw4Q0a σi T satp0 _ T0a) (AxSpinE8.owOkSome 15#5 _ (by decide))
    (CertBmQ0a σi T satp0 dok0 .DKSt rs5 (AxSpinPO.ppo 0x0a) .CPend false) (by omega))
  iintro %rs6 %ib6 %HG6
  have HF6 := stepRegs T satp0 _ rs5 _ _ _ _ _ rs6 HF5 HG6
  have HPC6 : rs6 .PC = AxSpinPO.ppo 0x0e := by rw [gbPc T satp0 _ _ _ _ _ _ HG6]; decide
  have Htl6 : rs6 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG6).trans Htl5
  -- ---- + 0x0e: c.mv s1,a5 (k+3) ----
  have Hc7 := certAdd (ctrlOkSW T satp0) rs6 (AxSpinPO.ppo 0x0e) true 15#5 0#5 9#5 (by decide)
  simp only [HF6] at Hc7
  ax_spin_po1_zsimp at Hc7
  iapply (XR _ rs6 (k + 3) (AxSpinPO.ppo 0x0e) true q0e _ _
    (retxRefl cpu rs6 (k + 3) ib6) (gbCtrl T satp0 _ _ _ _ _ _ HG6) HPC6
    (hitWSvpn rs6 (AxSpinPO.ppo 0x0e) (AxSpinPO.ppo 0) (by decide)
      (hitWAgree rs0 rs6 _ Htl6 Hhit0))
    (tw84be σi T satp0 _ T0e) (AxSpinE8.owOkSome 9#5 _ (by decide))
    (rfFOfRf0 _ (rf0Add _ _ _)) Hc7 (by omega))
  iintro %rs7 %ib7 %HG7
  have HF7 := stepRegs T satp0 _ rs6 _ _ _ _ _ rs7 HF6 HG7
  have HPC7 : rs7 .PC = AxSpinPO.ppo 0x10 := by rw [gbPc T satp0 _ _ _ _ _ _ HG7]; decide
  have Htl7 : rs7 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG7).trans Htl6
  -- ---- + 0x10: jal ra,mycpu (k+3) ----
  have Hcj : CertC (ctrlOkSW T satp0) rs7 (AxSpinPO.ppo 0x10) false q10 (some (pcm 0))
      (some (1#5, BitVec.addInt (AxSpinPO.ppo 0x10) (incr false))) := by
    have h := certJAL (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs7 (AxSpinPO.ppo 0x10)
      false 3374#21 1#5 (by decide)
    rw [show AxSpinPO.ppo 0x10 + sign_extend (m := 64) 3374#21 = pcm 0 by decide] at h
    rw [show linkOw 1#5 (BitVec.addInt (AxSpinPO.ppo 0x10) (incr false)) =
      some (1#5, BitVec.addInt (AxSpinPO.ppo 0x10) (incr false)) by
        unfold linkOw; rw [if_neg (by decide)]] at h
    exact h
  iapply (XR _ rs7 (k + 3) (AxSpinPO.ppo 0x10) false q10 (some (pcm 0))
    (some (1#5, BitVec.addInt (AxSpinPO.ppo 0x10) (incr false)))
    (retxRefl cpu rs7 (k + 3) ib7) (gbCtrl T satp0 _ _ _ _ _ _ HG7) HPC7
    (hitWSvpn rs7 (AxSpinPO.ppo 0x10) (AxSpinPO.ppo 0) (by decide)
      (hitWAgree rs0 rs7 _ Htl7 Hhit0))
    (tw4Q10 σi T satp0 _ T10) (AxSpinE8.owOkSome 1#5 _ (by decide))
    (AxSpinPOx.rfFJal 3374#21 (.Regidx 1#5)) Hcj (by omega))
  iintro %rs8 %ib8 %HG8
  have HF8 := stepRegs T satp0 _ rs7 _ _ _ _ _ rs8 HF7 HG8
  have HPC8 : rs8 .PC = pcm 0 := gbPc T satp0 _ _ _ _ _ _ HG8
  have Htl8 : rs8 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG8).trans Htl7
  have Esp8 : gprVal rs8 AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) := by
    rw [HF8]; ax_spin_po1_zsimp
  have Etp8 : gprVal rs8 AxSpinE8.r4 = gprVal rs0 AxSpinE8.r4 := by
    rw [HF8]; ax_spin_po1_zsimp
  have Evra : AxSpinE8.vaRa rs8 =
      AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immRa := by
    unfold AxSpinE8.vaRa; rw [Esp8]
  have Evs0 : AxSpinE8.vaS0 rs8 =
      AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immS0 := by
    unfold AxSpinE8.vaS0; rw [Esp8]
  -- ---- mycpu, at k+3 ----
  have HRm0 : RowShP (k + 3) (AxOpsem.grow (gtAdGd GT) i) (mycSh (paZ Pmra) (paZ Pms0)) :=
    rowShPAppR (s1 := [.RS (paZ Pra) 8, .RS (paZ Ps0) 8, .RS (paZ Ps1) 8])
      (rowShPAppL (s2 := [.RL (paZ Pn) 4]) HR)
  have HRm : RowMycpuP (k + 3) (AxOpsem.grow (gtAdGd GT) i) (paZ Pmra) (paZ Pms0) :=
    AxSpinPO3.rowMycpuPOf (k + 3) _ _ _ HRm0
  have WM' := WM (k + 3) rs8 ib8 (AxSpinPO.ppo 0x14) Pmra Pms0 HRm Hw8 Hnr_mra Hnr_ms0
    (gbCtrl T satp0 _ _ _ _ _ _ HG8) HPC8 (hitWAgree rs0 rs8 _ Htl8 HhitM)
    (by rw [Evra]; exact HdaS_mra) (by rw [Evra]; exact HdaL_mra)
    (by rw [Evra]; exact hitWAgree rs0 rs8 _ Htl8 Hh_mra)
    (by rw [Evs0]; exact HdaS_ms0) (by rw [Evs0]; exact HdaL_ms0)
    (by rw [Evs0]; exact hitWAgree rs0 rs8 _ Htl8 Hh_ms0)
    Hpr_mra Hnt_mra Hpr_ms0 Hnt_ms0 (by unfold dj at Hdm; omega)
    (fun h => by rw [show k + 3 + 2 = k + 5 by omega]; exact Hval14 (by omega)) (by decide)
    (fun k' h1 h2 h3 => HΨend k' (by omega) (by omega) h3)
  rw [show k + 3 + 4 = k + 7 by omega] at WM'
  iapply WM'
  iintro %vmra %vms0 %rs9 %ib9 %HM - -
  obtain ⟨Hc9, HPC9, Htl9', Ha09, Hsp9, -, -, -, -, Hkeep9, -, -, -, -⟩ := HM
  have Htl9 : rs9 .tlb = rs0 .tlb := Htl9'.trans Htl8
  have Ea09 : gprVal rs9 10#5 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) := by
    rw [← Etp8]; exact Ha09
  -- row end at k + 7
  by_cases E7 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 7
  · iclear C
    iapply (HΨend _ (by omega) (by omega) (by omega) _)
  -- ---- + 0x14: lw a5,120(a0) — noff (k+7; conditional genesis leaf) ----
  iapply (XL4 _ rs9 (k + 7) (AxSpinPO.ppo 0x14) true i120 10#5 15#5
    (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) Pn
    (retxRefl cpu rs9 (k + 7) ib9) Hc9 HPC9
    (hitWSvpn rs9 (AxSpinPO.ppo 0x14) (AxSpinPO.ppo 0) (by decide)
      (hitWAgree rs0 rs9 _ Htl9 Hhit0))
    (tw5d3c σi T satp0 _ T14) (by decide) (by rw [Ea09]) HdaL_n
    (hitWAgree rs0 rs9 _ Htl9 Hh_n) Hnt_n Hnrn (by omega) Hpr_n)
  iintro %vn %rs10 %ib10 %Hlvn %HG10 %Hgv7 Hgen
  have HF10 := stepRegs T satp0 _ rs9 _ _ _ _ _ rs10 (fun _ => rfl) HG10
  have HPC10 : rs10 .PC = AxSpinPO.ppo 0x16 := by rw [gbPc T satp0 _ _ _ _ _ _ HG10]; decide
  have Htl10 : rs10 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG10).trans Htl9
  -- row end at k + 8
  by_cases E8 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 8
  · iclear C
    iclear Hgen
    iapply (HΨend _ (by omega) (by omega) (by omega) _)
  -- ---- + 0x16: c.beqz a5 — the noff load's VALUE picks the arm (k+8) ----
  have Hb : (ldRes false 4 vn == zero_reg) = b := Hvb vn Hgv7
  have Hcb := certBTYPE (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs10
    (AxSpinPO.ppo 0x16) true (sign_extend (m := 13) (11#8 +++ 0b0#1)) 0#5 15#5 .BEQ (by decide)
  have Htgt : tgtOf (brOt .BEQ 15#5 0#5 rs10
      (AxSpinPO.ppo 0x16 + sign_extend (m := 64) (sign_extend (m := 13) (11#8 +++ 0b0#1))))
      (AxSpinPO.ppo 0x16) true = (if b then AxSpinPO.ppo 0x2c else AxSpinPO.ppo 0x18) := by
    have Ea5 : gval 15#5 rs10 = ldRes false 4 vn := by
      unfold gval
      rw [if_neg (by decide)]
      show gprVal rs10 15#5 = _
      rw [HF10]
      ax_spin_po1_zsimp
    have Ez : gval 0#5 rs10 = zero_reg := by
      unfold gval
      rw [if_pos (by decide)]
    unfold tgtOf brOt AxSymCtl2.bcond
    rw [Ea5, Ez, Hb]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> decide
  iapply (XP _ rs10 (k + 8) (AxSpinPO.ppo 0x16) true q16 _ none
    (if b then AxSpinPO.ppo 0x2c else AxSpinPO.ppo 0x18)
    (retxRefl cpu rs10 (k + 8) ib10) (gbCtrl T satp0 _ _ _ _ _ _ HG10) HPC10
    (hitWSvpn rs10 (AxSpinPO.ppo 0x16) (AxSpinPO.ppo 0) (by decide)
      (hitWAgree rs0 rs10 _ Htl10 Hhit0))
    (twCb99 σi T satp0 _ T16) trivial (rfFBtype _ _ _ _) Hcb (by omega) Htgt)
  iintro %rs' %ib' %HGP
  obtain ⟨HGr, Htg⟩ := HGP
  have HFr := stepRegs0 T satp0 _ rs10 _ _ _ rs' HF10 HGr
  iapply C $$ %vn %(rs5 .mstatus) %rs' %ib' [] Hgen
  ipureintro
  refine ⟨gbCtrl T satp0 _ _ _ _ _ _ HGr, ?_, (gbTlb T satp0 _ _ _ _ _ _ HGr).trans Htl10, ?_,
    ?_, ?_, HSIE, Hlvn, ?_, ?_, ?_, ?_, ?_, Hgv7, Hb⟩
  · -- PC = the arm's target
    rw [gbPc T satp0 _ _ _ _ _ _ HGr]
    exact Htg
  · -- a0 = mycpuRet tp
    rw [HFr]
    ax_spin_po1_zsimp
    exact Ea09
  · -- sp = the frame
    rw [HFr]
    ax_spin_po1_zsimp
    exact Hsp9.trans Esp8
  · -- s1 = sstatusRead m
    rw [HFr]
    ax_spin_po1_zsimp
    rw [Hkeep9 9#5 (by decide) (by decide) (by decide) (by decide) (by decide), HF8]
    ax_spin_po1_zsimp
    exact BitVec.zero_add _
  · -- a5 = the noff load
    rw [HFr]
    ax_spin_po1_zsimp
  · -- every other GPR kept
    intro r Hr1 Hr2 Hr8 Hr9 Hr10 Hr15
    rw [HFr]
    by_cases E0 : r.toNat = 0
    · rw [AxSpinE8.updZero _ _ _ _ E0, AxSpinE8.gprValZero rs0 r E0]
    · have n1 : r ≠ 1#5 := fun h => Hr1 (by rw [h]; rfl)
      have n2 : r ≠ 2#5 := fun h => Hr2 (by rw [h]; rfl)
      have n8 : r ≠ 8#5 := fun h => Hr8 (by rw [h]; rfl)
      have n9 : r ≠ 9#5 := fun h => Hr9 (by rw [h]; rfl)
      have n15 : r ≠ 15#5 := fun h => Hr15 (by rw [h]; rfl)
      simp (disch := assumption) only [AxSpinE8.updOther]
      rw [Hkeep9 r Hr1 Hr2 Hr8 Hr10 Hr15, HF8]
      simp (disch := assumption) only [AxSpinE8.updOther]
  · -- the three spills' row data
    rw [Hgd0, HF1]
    ax_spin_po1_zsimp
  · rw [Hgd1, HF2]
    ax_spin_po1_zsimp
  · rw [Hgd2, HF3]
    ax_spin_po1_zsimp


set_option maxHeartbeats 1600000 in
include HL Hcons hmode hasid hppn Hfix Htxm Htxp HΨmid in
/-- Rocq `wpd_po_head` (deviation 1: Stage C positions; value pins `Hval14`/`Hvb` replace the
`fpin` premises; the arm-fetch row premise becomes `k + 8 < row.length`).  Stage 2: the
full-row corollary of `wpdPoHeadP` (hook vacuous under `k + 8 < LEN`; the genesis annotation is
dropped). -/
theorem wpdPoHead (k : Nat) (b : Bool) (rs0 : RegFile) (ib0 : Ibch)
    (Pra Ps0 Ps1 Pmra Pms0 Pn : BitVec 64) :
    -- the row
    RowSh k (AxOpsem.grow (gtAdGd GT) i)
      (poHead (paZ Pra) (paZ Ps0) (paZ Ps1) (paZ Pmra) (paZ Pms0) (paZ Pn)) →
    k + 8 < (AxOpsem.grow (gtAdGd GT) i).length →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pmra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pms0) →
    noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = AxSpinPO.ppo 0 → hitW rs0 (AxSpinPO.ppo 0) →
    hitW rs0 (pcm 0) →
    -- the slots and the noff field
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm24) Pra →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm16) Ps0 →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm8) Ps1 →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immRa) Pmra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinE8.immS0) Pms0 →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) Pn →
    dj (paZ Pms0) 8 (paZ Pmra) 8 →
    -- the value pins (Q20': mycpu's ra reload and the noff load; deviation 1)
    graphValue (gtAdGd GT) (i, k + 5) = some (stBytes 8 (AxSpinPO.ppo 0x14)) →
    (∀ vn, graphValue (gtAdGd GT) (i, k + 7) = some vn → (ldRes false 4 vn == zero_reg) = b) →
    ⊢ (∀ (vn : List (BitVec 8)) (m : BitVec 64) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧
          rs' .PC = (if b then AxSpinPO.ppo 0x2c else AxSpinPO.ppo 0x18) ∧
          rs' .tlb = rs0 .tlb ∧
          gprVal rs' AxSpinE8.r10 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) ∧
          gprVal rs' AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) ∧
          gprVal rs' AxSpinPOr.r9 = sstatusRead m ∧ (_get_Mstatus_SIE m == 1#1) = false ∧
          vn.length = 4 ∧ gprVal rs' AxSpinE8.r15 = ldRes false 4 vn ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
            r.toNat ≠ 10 → r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
          graphData (gtAdGd GT) (i, k) = some (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs0 AxSpinE8.r8)) ∧
          graphData (gtAdGd GT) (i, k + 2) = some (stBytes 8 (gprVal rs0 AxSpinPOr.r9)) ∧
          graphValue (gtAdGd GT) (i, k + 7) = some vn ∧ (ldRes false 4 vn == zero_reg) = b⌝ -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 8⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hlen Hw8 Hnr_mra Hnr_ms0 Hnrn Hc0 HPC0 Hhit0 HhitM Bra Bs0 Bs1 Bmra Bms0 Bn Hdm
    Hval14 Hvb
  iintro C
  iapply (wpdPoHeadP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxp Ψ HΨmid
    k b rs0 ib0 Pra Ps0 Ps1 Pmra Pms0 Pn (rowShPOfSh HR) Hw8 Hnr_mra Hnr_ms0 Hnrn Hc0 HPC0 Hhit0
    HhitM Bra Bs0 Bs1 Bmra Bms0 Bn Hdm (fun _ => Hval14) Hvb
    (fun _ _ h2 h3 => absurd h3 (by omega)))
  iintro %vn %m %rs' %ib' %Hf -
  iapply C $$ %vn %m %rs' %ib' %Hf

end pohead

end Weak
