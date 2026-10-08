/-
Weak: **THE SPIN LOOP of xv6's REAL `acquire` on the positional engine** — `wpdSpin`: the four
instructions at `acquire + 0x1a … + 0x22` (`c.mv a5,a4`; `amoswap.w.aq a5,a5,(s1)`; `sext.w a5`;
`c.bnez a5,+0x1a`), iterated `n + 1` times (`n` failed spins, then the claim), as a POSITIONAL
CPS WPd at the joint instance Ixv6 (`AxSpinX2.xG L GT nm` / `xv6Pol GT`), interrupts off
(`ctrlOkSW`), warm TLB.

Lean-only (Theorem 2 design `notes/weak-lb-thm2-design.md` §C.1 first paragraph, §D row
`AxSpinAq1`; no Rocq source: Rocq stopped before a positional `wpd_acquire`).

## What is proved

Row (AxSpinAqr, Stage C, stride 1): iteration `j` of the loop has exactly ONE row item, the fused
RMW at `u + j`; `c.mv`, `sext.w` and `c.bnez` are register-only (`XxReg`, no row item).  With
`u` = the boundary after `holding`'s return (`aqKh`), the claim RMW is at `u + n` (`aqKA`) and the
loop exits at the boundary `u + (n + 1)` (`aqKm`, mycpu's first event) with `PC = acquire + 0x24`
(`jal mycpu`).

`wpdSpin u j n rs0 …` (any `j ≤ n`), from the boundary at `u + j`, `PC = acquire + 0x1a`:

    isLock … RPid -∗ notheld i -∗ KSpin … u n rs0 -∗ WPd ⟨rs0, u + j⟩

`AxSpinAq1.KSpin … u n rs0` = for every final register file `rs'`: ⌜regime ∧ PC = acquire + 0x24 ∧
TLB kept ∧ a5 = 0 ∧ every other GPR kept ∧ the claim's graph value at `(i, u + n)` is
`AxSpinX4.z4`⌝ -∗ `(i, u+n) ↦ₐ locked … i (i, u+n)` -∗ `(i, u+n) ↦ₐ RCpu … (i, u+n)` -∗
`(i, u+n) ↦ₐ RNp … (i, u+n)` -∗ WPd (boundary `u + (n + 1)`).  `wpdSpinAq` is `wpdSpin 0 n` at
`u = aqKh k b hb` (claim at `aqKA`, continuation at `aqKm`, both definitional) — the form
`AxSpinAq2.wpdAcquire` composes after `holdingFromAcquire'` and before `wpdMycpu`.

## How

Induction on the number of remaining iterations (`AxSpinAq1.spinLoop`, the `AxSpinAp9.scanLoop`
pattern).  Each iteration: `XxReg` (c.mv a5,a4; `certAdd`) → `XxAmoswap` (`AxSpinAm3`) with the
write flow `AxSpinAmX.fstAcqNh … .WCexcl (OAcq L GT nm i LK R2) (u+j) (u+j+1)` (`AxSpinAmX`,
drawn from `isLock` ∗
`notheld i`) → `XxReg` (sext.w; `certAddiw`, value `sxw0 (amoLdv 4 rvs)`) → `XxReg` (c.bnez a5;
`certBTYPE`).  The branch direction is `aqFail rvs` of the RMW's PINNED graph value `rvs`, and
`spinVals` says it is `decide (j < n)` — no new pin.  A failed iteration (`j < n`, so
`rvs ≠ z4`) gets `notheld i` back from `OAcq` and loops (PC back to + 0x1a, boundary
`u + (j + 1)`); the last one (`j = n`, so `rvs = z4`, by `AxSpinAq1.aqFailOfLow` + the row's
lock-value disjunct) gets the claim pre-split as `(i,kA) ↦ₐ LK ∗ (i,kA) ↦ₐ (RCpu ∗ RNp)`
(`FstAcqNh`'s split premise is `RPid`'s definition), and the second fragment is split by
`wpdAnnotSplit` (`AxSpinH5`, via `AxSpinAq1.annotSplitX`) into the `RCpu` handle (for acquire's
`c.sd a0,16(s1)` and release) and the `RNp` handle (for `wpdAllocpidCs`'s anchor).

Text: `acquireText σi T` (`AxSpinAq`; satisfiable — `AxSpinTextCerts.acquireTextOf`), its
conjuncts at + 0x1a / + 0x1c / + 0x20 / + 0x22 through `twa87ba` / `tokAmo` (`Wa1c` is
`wAmoA`) / `twa2781` / `twaFfe5` (`AxSpinAqt2`, `AxSpinAm`).  KERNEL CROSS-CHECK: these four
words (0x87ba, 0x0cf4a7af, 0x2781, 0xffe5 at acquire = 0x80000c58 + 0x1a / 0x1c / 0x20 / 0x22,
i.e. 0x80000c72 / c74 / c78 / c7a) are entries of `AxSpinAq.aqCode`, tied to
`Xv6/KernelImage.lean` by `AxSpinAq.aqCodeImg`; the back-edge `+0x22 + imm = +0x1a` is
`AxSpinAq1.backEdge` (decide).

## Premises / honesty

* ROW PREMISE `AxSpinAq1.spinRmw row u n lk` (as `AxSpinAmX.fstAcqNh` takes it): for every
  `j ≤ n` the label at `u + j` is acquire's
  `LRmw true false lk [t,t,t,t] rvs o4 WCexcl` (timestamps, the written word `o4` = c.li's 1,
  class `WCexcl` — the class the hardware stamps on a fused RMW, `AxClsStep.pclsEv` /
  `AxCert.wclsRmw`, and the one `AxSpinRl1.rowClsHonest` demands; Rocq's `wpd_acquireX` /
  `FstAcq_nh` say `WCplain`, which no honest graph has — the flow is class-generic,
  `AxSpinAmX.fstAcqNh`) and `rvs = z4 ∨ rvs`'s low byte ≠ 0 (the lock word is only ever
  0 / 1 — a graph fact the flow does not derive; `FstAcqNh` needs it for the failure case).
  It implies AxSpinAqr's `RowSpin` (`AxSpinAq1.rowSpinOfRmw`).  `spinVals row u n` (AxSpinAqr) fixes the
  loop count.  `u + (n + 1) < LEN`: the boundary after the claim runs two register-only
  instructions (`XxReg` needs `k < LEN`), as `RowAcquire`'s length conjunct gives.
* Option V (Q20'): control flow is decided by graph VALUES (the RMW reads); the theorem proves
  nothing about a hart whose loop count or lock address is diverted.  Ownership is load-bearing
  for the claim's handles (`locked`, `RCpu`, `RNp` come out of the lock invariant through
  `fxClaim`).
* The written word (a5 = a4 = 1) plays no role: the row label pins `o4`; `a4` is therefore not a
  premise (it is kept: every GPR but a5 is preserved).

## Deviations

RMW class (2026-10-08, found by AxSpinT2a): the RMW labels are stated at `WCexcl` (was
`WCplain`, inherited from Rocq's `wpd_acquireX`); API names and argument order unchanged.
Otherwise none from the design.  (Design wording "`XxAmoswap` with `FstAcqNh … (OAcq LK RP)`":
`OAcq`'s second component is `RCpu ∗ RNp`, i.e. `RP` unfolded, so the split is one `wpdAnnotSplit`.)

**Reused** (by name): `XxReg`, `AxSpinE6.ctlRegimeSW` (AxSpinE6); `XxAmoswap`, `AxSpinAm3.XAmo`
(AxSpinAm3); `AxSpinAmX.fstAcqNh` (AxSpinAmX, class-generic `FstAcqNh`), `OAcq` (AxSpinAm4);
`wpdAnnotSplit` (AxSpinH5); `RowSpin`, `spinVals`,
`aqKh`/`aqKm`/`aqKA` (AxSpinAqr); `acquireText`, `aqFail`, `sxw0`, `a1a`, `a22`, `Wa1c`
(AxSpinAq); `twa87ba`/`twa2781`/`twaFfe5` (AxSpinAqt2); `tokAmo`, `AxSpinAm.amoswapAcqAst`
(AxSpinAm); `certAdd`/`certAddiw` (AxSpinE7), `certBTYPE`/`brOt` (AxSymCtl2); `retxRefl`,
`gbCtrl`/`gbPc`/`gbTlb`, `stepRegs`/`stepRegs0`, `hitWSvpn`, `AxSpinE8.upd*` (AxSpinE8);
`hitWAgree` (AxSpinE); `rfFOfRf0`/`rf0Add`/`rfFIns0a` (AxSpinE7d), `AxSpinAp6.rfFBtype`;
`AxSpinHdA.c7`; `wordOfBytesByte`, `AxWp.growLookup`.

**Lean-only declarations** (all file-qualified except the two theorems the design names):
`AxSpinAq1.spinRmw`, `AxSpinAq1.rowSpinOfRmw`, `AxSpinAq1.lwbAll`, `AxSpinAq1.imm22`,
`AxSpinAq1.backEdge`, `AxSpinAq1.aqFailZ4`, `AxSpinAq1.sxw0Z4`, `AxSpinAq1.sxw0Low`,
`AxSpinAq1.aqFailOfLow`, `AxSpinAq1.keep15`, `AxSpinAq1.tok1a`/`tok1c`/`tok20`/`tok22`,
`AxSpinAq1.rfF1a`/`rfF22`, `AxSpinAq1.oAcqClaim`, `AxSpinAq1.oAcqFail`, `AxSpinAq1.annotSplitX`,
`AxSpinAq1.KSpin`, `AxSpinAq1.spinLoop`, `wpdSpin`, `wpdSpinAq` (+ 1 local macro).
-/
import Weak.AxSpinAqr
import Weak.AxSpinAqt2
import Weak.AxSpinAmX
import Weak.AxSpinH5
import Weak.AxSpinHdA
import Weak.AxSpinAp6

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- (Rocq `zsimp`) evaluate the closed `upd` tests. -/
local macro "ax_spin_aq1_zsimp" loc:(ppSpace Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := decide) only [AxSpinE8.updSame, AxSpinE8.updOther, AxSpinE8.updZero]
    $[$loc]?)

/-! # 1. Pure facts -/

/-- The loop's row premise: iteration `j`'s RMW label (acquire's shape) and the lock-value
disjunct (`FstAcqNh`'s premises), for every `j ≤ n`. -/
def AxSpinAq1.spinRmw (row : List Lbl) (u n : Nat) (lk : Int) : Prop :=
  ∀ j, j ≤ n → ∃ (t : Nat) (rvs : List (BitVec 8)),
    row[u + j]? = some (.LRmw true false lk [t, t, t, t] rvs AxSpinX4.o4 .WCexcl) ∧
    (rvs = AxSpinX4.z4 ∨ ∃ b0', rvs[0]? = some b0' ∧ b0' ≠ b0)

/-- The label premise implies AxSpinAqr's `RowSpin`. -/
theorem AxSpinAq1.rowSpinOfRmw (row : List Lbl) (u n : Nat) (lk : Int) :
    AxSpinAq1.spinRmw row u n lk → RowSpin u n row lk := by
  intro H j hj
  obtain ⟨t, rvs, Hl, -⟩ := H j hj
  refine ⟨_, Hl, ?_⟩
  simp only [aident, AxSpinX4.o4, wbytesLength]

theorem AxSpinAq1.lwbAll (L : Xlay) : ∀ a, L.xlLk ≤ a ∧ a < L.xlLk + 4 → a ∈ lwb L := by
  rintro a ⟨h1, h2⟩
  unfold lwb clRange
  exact List.mem_map.2 ⟨(a - L.xlLk).toNat, List.mem_range.2 (by omega), by omega⟩

/-- `c.bnez a5,+0x1a`'s branch offset (−8). -/
def AxSpinAq1.imm22 : BitVec 13 := sign_extend (m := 13) (252#8 +++ 0b0#1)

/-- The back-edge: `+0x22 + imm = +0x1a`. -/
theorem AxSpinAq1.backEdge :
    AxSpinHdB.pac 0x22 + sign_extend (m := 64) AxSpinAq1.imm22 = AxSpinHdB.pac 0x1a := by
  decide

theorem AxSpinAq1.aqFailZ4 : aqFail AxSpinX4.z4 = false := by decide +kernel

theorem AxSpinAq1.sxw0Z4 : sxw0 (amoLdv 4 AxSpinX4.z4) = 0#64 := by decide +kernel

/-- A 32-bit word with a nonzero low byte is nonzero after `sext.w` of its sign extension. -/
theorem AxSpinAq1.sxw0Low (w : BitVec 32) :
    w.extractLsb' 0 8 ≠ 0#8 → (sxw0 (sign_extend (m := 64) w) != 0#64) = true := by
  unfold sxw0 sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb
  intro h
  bv_decide

/-- A read whose low byte is nonzero FAILS the spin test. -/
theorem AxSpinAq1.aqFailOfLow (vs : List (BitVec 8)) (b : BitVec 8) :
    vs.length = 4 → vs[0]? = some b → b ≠ b0 → aqFail vs = true := by
  intro hl h0 hb
  have hby : nthByte (n := 4) (wordOfBytes 4 vs) 0 = b := by
    rw [wordOfBytesByte 4 vs 0 hl (by decide)]
    simp [List.getD_eq_getElem?_getD, h0]
  unfold nthByte at hby
  exact AxSpinAq1.sxw0Low (wordOfBytes 4 vs) (by rw [hby]; exact hb)

/-- One GPR write to a5: every other GPR is kept. -/
theorem AxSpinAq1.keep15 (rs rs' rs0 : RegFile) (v : BitVec 64) :
    (∀ r, gprVal rs' r = AxSpinE8.upd (gprVal rs) 15#5 v r) →
    (∀ r : BitVec 5, r.toNat ≠ 15 → gprVal rs r = gprVal rs0 r) →
    ∀ r : BitVec 5, r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r := by
  intro HF Hk r hr
  rw [HF r]
  by_cases E0 : r.toNat = 0
  · rw [AxSpinE8.updZero _ _ _ _ E0, AxSpinE8.gprValZero rs0 r E0]
  · rw [AxSpinE8.updOther _ _ _ _ E0 (fun h => hr (by rw [h]; rfl))]
    exact Hk r hr

section toks
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)

theorem AxSpinAq1.tok1a (Htxt : acquireText σi T) :
    textOkB σi T satp0 (AxSpinHdB.pac 0x1a) true a1a :=
  twa87ba σi T satp0 _ Htxt.2.2.2.2.2.2.2.2.2.2.2.1

theorem AxSpinAq1.tok1c (Htxt : acquireText σi T) :
    textOkB σi T satp0 (AxSpinHdB.pac 0x1c) false AxSpinAm.amoswapAcqAst :=
  tokAmo σi T satp0 _ Htxt.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem AxSpinAq1.tok20 (Htxt : acquireText σi T) :
    textOkB σi T satp0 (AxSpinHdB.pac 0x20) true ins0a :=
  twa2781 σi T satp0 _ Htxt.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem AxSpinAq1.tok22 (Htxt : acquireText σi T) :
    textOkB σi T satp0 (AxSpinHdB.pac 0x22) true a22 :=
  twaFfe5 σi T satp0 _ Htxt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

end toks

theorem AxSpinAq1.rfF1a : rfF (execute a1a) := rfFOfRf0 _ (rf0Add _ _ _)
theorem AxSpinAq1.rfF22 : rfF (execute a22) := AxSpinAp6.rfFBtype _ _ _ _

/-! # 2. `OAcq` read off the row; the annotation split at Ixv6 -/

section bridges
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

/-- The claim (read bytes `z4`): `OAcq` is the two pre-split fragments. -/
theorem AxSpinAq1.oAcqClaim (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent) (kA t : Nat)
    (R1 R2 : IProp GF) (w : List (BitVec 8)) :
    (AxOpsem.grow (gtAdGd GT) i)[kA]? =
      some (Lbl.LRmw true false L.xlLk [t, t, t, t] AxSpinX4.z4 AxSpinX4.o4 .WCexcl) →
    OAcq L GT nm i R1 R2 kA w ⊢
      iprop(AxAnnot.annotOwn (i, kA) R1 ∗ AxAnnot.annotOwn (i, kA) R2) := by
  intro h
  simp only [OAcq, h]
  rw [if_pos trivial]

/-- A failed spin (read bytes `≠ z4`): `OAcq` hands `notheld` back. -/
theorem AxSpinAq1.oAcqFail (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent) (kA t : Nat)
    (rvs : List (BitVec 8)) (R1 R2 : IProp GF) (w : List (BitVec 8)) :
    (AxOpsem.grow (gtAdGd GT) i)[kA]? =
      some (Lbl.LRmw true false L.xlLk [t, t, t, t] rvs AxSpinX4.o4 .WCexcl) →
    rvs ≠ AxSpinX4.z4 →
    OAcq L GT nm i R1 R2 kA w ⊢ notheld nm.xnReg L.xlLk i := by
  intro h hne
  simp only [OAcq, h]
  rw [if_neg hne]

/-- `wpdAnnotSplit` (AxSpinH5) at Ixv6, in the `wpdM` form of the positional leaves. -/
theorem AxSpinAq1.annotSplitX (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent)
    (Ψ : Athread → IProp GF) (s : Athread) (e : Geid) (P Q : IProp GF) :
    ⊢ AxAnnot.annotOwn e iprop(P ∗ Q) -∗
      (AxAnnot.annotOwn e P -∗ AxAnnot.annotOwn e Q -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ :=
  wpdAnnotSplit (hlc := hlc) (pol := xv6Pol GT) (gtAdGd GT) Xv6N Unit (protXv6 L) nm i Ψ s e P Q

/-- THE LOOP'S CONTINUATION: the claim at `(i, u + n)`, the exit boundary `u + (n + 1)`,
`PC = acquire + 0x24`, a5 = 0, every other GPR of the entry state `rs0` kept. -/
def AxSpinAq1.KSpin (L : Xlay) (GT : GdexecT) (nm : Xv6N) (T : PTree) (satp0 : BitVec 64)
    (i : Agent) (cpu : CPU) (Ψ : Athread → IProp GF) (u n : Nat) (rs0 : RegFile) : IProp GF :=
  iprop(∀ (rs' : RegFile) (ib' : Ibch),
    ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = AxSpinHdB.pac 0x24 ∧ rs' .tlb = rs0 .tlb ∧
      gprVal rs' 15#5 = 0#64 ∧ (∀ r : BitVec 5, r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
      graphValue (gtAdGd GT) (i, u + n) = some AxSpinX4.z4⌝ -∗
    AxAnnot.annotOwn (GF := GF) (i, u + n) (locked nm.xnReg L.xlLk i (i, u + n)) -∗
    AxAnnot.annotOwn (GF := GF) (i, u + n) (RCpu L nm.xnH (gtAdGd GT) (i, u + n)) -∗
    AxAnnot.annotOwn (GF := GF) (i, u + n) (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, u + n)) -∗
    @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
      ⟨.PHart cpu (.pure ()) rs' none ib', u + (n + 1)⟩ Ψ)

end bridges

/-! # 3. THE LOOP -/

section spin
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
variable (Htxt : acquireText σi T)
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

set_option maxHeartbeats 4000000 in
include HL Hcons hmode hasid hppn Hfix Htxt HΨmid in
/-- The loop by induction on the remaining iterations `m` (iteration `j`, `j + m = n + 1`). -/
theorem AxSpinAq1.spinLoop (u n : Nat) (rs0 : RegFile) (Pl : BitVec 64)
    (Hrmw : AxSpinAq1.spinRmw (AxOpsem.grow (gtAdGd GT) i) u n L.xlLk)
    (Hvals : spinVals (AxOpsem.grow (gtAdGd GT) i) u n)
    (Hlen : u + (n + 1) < (AxOpsem.grow (gtAdGd GT) i).length)
    (Hpl : paZ Pl = L.xlLk) (Hntx : ¬ L.xlText (paZ Pl))
    (Hda : dataAtS σi T (accAmo true) (gprVal rs0 9#5) 4 Pl)
    (Hhit : hitW rs0 (AxSpinHdB.pac 0x1a)) (Hhv : hitW rs0 (gprVal rs0 9#5)) :
    ∀ m j, j + m = n + 1 → 0 < m → ∀ (rs : RegFile) (ib : Ibch),
      ctrlOkSW T satp0 rs → rs .PC = AxSpinHdB.pac 0x1a → rs .tlb = rs0 .tlb →
      (∀ r : BitVec 5, r.toNat ≠ 15 → gprVal rs r = gprVal rs0 r) →
      ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
        notheld nm.xnReg L.xlLk i -∗
        AxSpinAq1.KSpin (hlc := hlc) L GT nm T satp0 i cpu Ψ u n rs0 -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs none ib, u + j⟩ Ψ := by
  intro m
  induction m with
  | zero => intro j _ h; omega
  | succ m ih =>
  intro j hjm _ rs ib Hc HPC Htl Hkeep
  have hj : j ≤ n := by omega
  obtain ⟨t, rvs, Hlb, Hcase⟩ := Hrmw j hj
  have Hfail : aqFail rvs = decide (j < n) := by
    obtain ⟨lb', vs', Hlb', Hv', Hf⟩ := Hvals j hj
    rw [Hlb] at Hlb'
    cases Hlb'
    simp only [lblValue, Option.some.injEq] at Hv'
    subst Hv'
    exact Hf
  have XR := XxReg (hlc := hlc) (GF := GF) L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu
    Hfix Ψ HΨmid
  -- the acquire write flow at the RMW `(i, u + j)`, drawn from `isLock` ∗ `notheld`
  have FA : ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      notheld nm.xnReg L.xlLk i -∗
      @FstRmwW hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent
        (dokAtP (paZ Pl) 4) i
        (OAcq L GT nm i (locked nm.xnReg L.xlLk i (i, u + j))
          iprop(RCpu L nm.xnH (gtAdGd GT) (i, u + j) ∗
            RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, u + j)))
        (u + j) (u + j + 1) := by
    rw [Hpl]
    exact AxSpinAmX.fstAcqNh (hlc := hlc) L GT nm HL Hcons i (u + j) t rvs .WCexcl _ _ (u + j)
      (u + j + 1) Hlb Hcase
      (AxSpinAq1.lwbAll L) (fun k' _ hk _ _ => by omega) (by unfold RPid; exact .rfl)
  have XA := XxAmoswap (hlc := hlc) L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ
    HΨmid (u + j) (AxSpinHdB.pac 0x1c) 15#5 9#5 15#5 (gprVal rs0 9#5) Pl
    (OAcq L GT nm i (locked nm.xnReg L.xlLk i (i, u + j))
      iprop(RCpu L nm.xnH (gtAdGd GT) (i, u + j) ∗
        RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, u + j)))
    (AxSpinAq1.tok1c σi T satp0 Htxt) (by decide) Hda Hntx
    (by
      intro lb aq m' Hl Hid
      rw [Hlb] at Hl
      cases Hl
      simp [aident] at Hid)
  unfold AxSpinAm3.XAmo at XA
  iintro #Hil Hnh K
  -- ---- + 0x1a: c.mv a5,a4 (row u + j) ----
  iapply (XR _ rs (u + j) (AxSpinHdB.pac 0x1a) true a1a none
    (some (15#5, gprVal rs 0#5 + gprVal rs 14#5))
    (retxRefl cpu rs (u + j) ib) Hc HPC (hitWAgree rs0 rs _ Htl Hhit)
    (AxSpinAq1.tok1a σi T satp0 Htxt) (AxSpinE8.owOkSome 15#5 _ (by decide)) AxSpinAq1.rfF1a
    (certAdd _ rs (AxSpinHdB.pac 0x1a) true 14#5 0#5 15#5 (by decide)) (by omega))
  iintro %rs1 %ib1 %HG1
  have HF1 := stepRegs T satp0 _ rs _ _ _ _ _ rs1 (fun _ => rfl) HG1
  have Hk1 := AxSpinAq1.keep15 rs rs1 rs0 _ HF1 Hkeep
  have HPC1 : rs1 .PC = AxSpinHdB.pac 0x1c := by rw [gbPc T satp0 _ _ _ _ _ _ HG1]; decide
  have Htl1 : rs1 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG1).trans Htl
  -- ---- + 0x1c: amoswap.w.aq a5,a5,(s1) — THE RMW (row u + j) ----
  ihave F := FA $$ Hil Hnh
  ihave X := XA $$ F
  have Hpre : RetX cpu rs1 (u + j) ⟨.PHart cpu (.pure ()) rs1 none ib1, u + j⟩ ∧
      ctrlOkSW T satp0 rs1 ∧ rs1 .PC = AxSpinHdB.pac 0x1c ∧ hitW rs1 (AxSpinHdB.pac 0x1c) ∧
      gprVal rs1 9#5 = gprVal rs0 9#5 ∧ hitW rs1 (gprVal rs0 9#5) ∧
      u + j + 1 ≤ (AxOpsem.grow (gtAdGd GT) i).length :=
    ⟨retxRefl cpu rs1 (u + j) ib1, gbCtrl T satp0 _ _ _ _ _ _ HG1, HPC1,
      hitWSvpn rs1 (AxSpinHdB.pac 0x1c) (AxSpinHdB.pac 0x1a) (by decide)
        (hitWAgree rs0 rs1 _ Htl1 Hhit),
      Hk1 9#5 (by decide), hitWAgree rs0 rs1 _ Htl1 Hhv, by omega⟩
  iapply X $$ %(⟨.PHart cpu (.pure ()) rs1 none ib1, u + j⟩ : Athread) %rs1 %Hpre
  iintro %rvs' %rs2 %ib2 %Hl4 %HG2 %Hrow2 HO
  have Hrv : rvs = rvs' := by
    obtain ⟨aq2, rl2, ts2, wvs2, cls2, Hl2, -⟩ := Hrow2
    rw [Hlb] at Hl2
    obtain ⟨-, -, -, -, h5, -⟩ := Lbl.LRmw.inj (Option.some.inj Hl2)
    exact h5
  subst Hrv
  have HF2 := stepRegs T satp0 _ rs1 _ _ _ _ _ rs2 (fun _ => rfl) HG2
  have Hk2 := AxSpinAq1.keep15 rs1 rs2 rs0 _ HF2 Hk1
  have E15b : gprVal rs2 15#5 = amoLdv 4 rvs := by
    rw [HF2]
    ax_spin_aq1_zsimp
  have HPC2 : rs2 .PC = AxSpinHdB.pac 0x20 := by rw [gbPc T satp0 _ _ _ _ _ _ HG2]; decide
  have Htl2 : rs2 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG2).trans Htl1
  rw [show u + j + 1 = u + (j + 1) by omega]
  -- ---- + 0x20: sext.w a5 (row u + (j + 1)) ----
  iapply (XR _ rs2 (u + (j + 1)) (AxSpinHdB.pac 0x20) true ins0a none _
    (retxRefl cpu rs2 (u + (j + 1)) ib2) (gbCtrl T satp0 _ _ _ _ _ _ HG2) HPC2
    (hitWSvpn rs2 (AxSpinHdB.pac 0x20) (AxSpinHdB.pac 0x1a) (by decide)
      (hitWAgree rs0 rs2 _ Htl2 Hhit))
    (AxSpinAq1.tok20 σi T satp0 Htxt) (AxSpinE8.owOkSome 15#5 _ (by decide)) rfFIns0a
    (certAddiw _ rs2 (AxSpinHdB.pac 0x20) true 15#5 15#5 (sign_extend (m := 12) (0#6))
      (by decide))
    (by omega))
  iintro %rs3 %ib3 %HG3
  have HF3 := stepRegs T satp0 _ rs2 _ _ _ _ _ rs3 (fun _ => rfl) HG3
  have Hk3 := AxSpinAq1.keep15 rs2 rs3 rs0 _ HF3 Hk2
  have E15 : gprVal rs3 15#5 = sxw0 (amoLdv 4 rvs) := by
    rw [HF3]
    ax_spin_aq1_zsimp
    rw [E15b]
    rfl
  have HPC3 : rs3 .PC = AxSpinHdB.pac 0x22 := by rw [gbPc T satp0 _ _ _ _ _ _ HG3]; decide
  have Htl3 : rs3 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG3).trans Htl2
  -- ---- + 0x22: c.bnez a5,+0x1a — direction = `aqFail rvs` = `decide (j < n)` ----
  have Hcb := certBTYPE (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs3
    (AxSpinHdB.pac 0x22) true AxSpinAq1.imm22 0#5 AxSpinHdA.c7 .BNE (by decide)
  have Hbr : AxSymCtl2.bcond .BNE (gval AxSpinHdA.c7 rs3) (gval 0#5 rs3) = decide (j < n) := by
    have Hg7 : gval AxSpinHdA.c7 rs3 = sxw0 (amoLdv 4 rvs) := by
      rw [show AxSpinHdA.c7 = 15#5 by decide]
      unfold gval
      rw [if_neg (by decide)]
      exact E15
    have Hg0 : gval 0#5 rs3 = 0#64 := by
      unfold gval
      rw [if_pos (by decide)]
      rfl
    unfold AxSymCtl2.bcond
    rw [Hg7, Hg0]
    exact Hfail
  have Hhit3 : hitW rs3 (AxSpinHdB.pac 0x22) :=
    hitWSvpn rs3 (AxSpinHdB.pac 0x22) (AxSpinHdB.pac 0x1a) (by decide)
      (hitWAgree rs0 rs3 _ Htl3 Hhit)
  cases m with
  | zero =>
    -- ===== j = n: the CLAIM; the branch falls through to + 0x24 =====
    obtain rfl : j = n := by omega
    have Eot : brOt .BNE AxSpinHdA.c7 0#5 rs3
        (AxSpinHdB.pac 0x22 + sign_extend (m := 64) AxSpinAq1.imm22) = none := by
      unfold brOt
      rw [Hbr, if_neg (by simp)]
    rw [Eot] at Hcb
    have Hz : rvs = AxSpinX4.z4 := by
      rcases Hcase with h | ⟨b, hb, hne⟩
      · exact h
      · exfalso
        have h := AxSpinAq1.aqFailOfLow rvs b Hl4 hb hne
        rw [Hfail] at h
        simp at h
    subst Hz
    iapply (XR _ rs3 (u + (j + 1)) (AxSpinHdB.pac 0x22) true a22 none none
      (retxRefl cpu rs3 (u + (j + 1)) ib3) (gbCtrl T satp0 _ _ _ _ _ _ HG3) HPC3 Hhit3
      (AxSpinAq1.tok22 σi T satp0 Htxt) trivial AxSpinAq1.rfF22 Hcb (by omega))
    iintro %rs4 %ib4 %HG4
    have HF4 := stepRegs0 T satp0 (gprVal rs3) rs3 _ _ _ rs4 (fun _ => rfl) HG4
    ihave HO := (AxSpinAq1.oAcqClaim L GT nm i (u + j) t _ _ _ Hlb) $$ HO
    icases HO with ⟨HLK, HR2⟩
    iapply (AxSpinAq1.annotSplitX L GT nm i Ψ _ (i, u + j) _ _) $$ HR2
    iintro HCpu HNp
    unfold AxSpinAq1.KSpin
    iapply K $$ %rs4 %ib4 [] HLK HCpu HNp
    ipureintro
    refine ⟨gbCtrl T satp0 _ _ _ _ _ _ HG4, ?_, (gbTlb T satp0 _ _ _ _ _ _ HG4).trans Htl3, ?_,
      fun r hr => (HF4 r).trans (Hk3 r hr), ?_⟩
    · rw [gbPc T satp0 _ _ _ _ _ _ HG4]
      decide
    · rw [HF4, E15]
      exact AxSpinAq1.sxw0Z4
    · rw [graphValue, AxWp.growLookup _ _ _ _ Hlb]
      rfl
  | succ m' =>
    -- ===== j < n: a FAILED spin; back to + 0x1a with `notheld` =====
    have hjn : j < n := by omega
    have Eot : brOt .BNE AxSpinHdA.c7 0#5 rs3
        (AxSpinHdB.pac 0x22 + sign_extend (m := 64) AxSpinAq1.imm22) =
        some (AxSpinHdB.pac 0x1a) := by
      unfold brOt
      rw [Hbr, if_pos (decide_eq_true hjn)]
      exact congrArg some AxSpinAq1.backEdge
    rw [Eot] at Hcb
    have Hnz : rvs ≠ AxSpinX4.z4 := by
      intro h
      subst h
      rw [AxSpinAq1.aqFailZ4] at Hfail
      simp at Hfail
      omega
    iapply (XR _ rs3 (u + (j + 1)) (AxSpinHdB.pac 0x22) true a22 (some (AxSpinHdB.pac 0x1a)) none
      (retxRefl cpu rs3 (u + (j + 1)) ib3) (gbCtrl T satp0 _ _ _ _ _ _ HG3) HPC3 Hhit3
      (AxSpinAq1.tok22 σi T satp0 Htxt) trivial AxSpinAq1.rfF22 Hcb (by omega))
    iintro %rs4 %ib4 %HG4
    have HF4 := stepRegs0 T satp0 (gprVal rs3) rs3 _ _ _ rs4 (fun _ => rfl) HG4
    ihave Hnh := (AxSpinAq1.oAcqFail L GT nm i (u + j) t rvs _ _ _ Hlb Hnz) $$ HO
    iapply (ih (j + 1) (by omega) (by omega) rs4 ib4 (gbCtrl T satp0 _ _ _ _ _ _ HG4)
      (gbPc T satp0 _ _ _ _ _ _ HG4) ((gbTlb T satp0 _ _ _ _ _ _ HG4).trans Htl3)
      (fun r hr => (HF4 r).trans (Hk3 r hr))) $$ Hil Hnh K

include HL Hcons hmode hasid hppn Hfix Htxt HΨmid in
/-- THE SPIN LOOP of `acquire` (+ 0x1a … + 0x22), from iteration `j ≤ n` at the boundary
`u + j`: `n − j` more failed spins (each hands `notheld i` back), then the claim at `u + n`,
exit at `u + (n + 1)` with `PC = acquire + 0x24`; the claim's `locked` / `RCpu` / `RNp`
fragments at `(i, u + n)` go to `KSpin`. -/
theorem wpdSpin (u j n : Nat) (rs0 : RegFile) (ib0 : Ibch) (Pl : BitVec 64) :
    -- the row
    AxSpinAq1.spinRmw (AxOpsem.grow (gtAdGd GT) i) u n L.xlLk →
    spinVals (AxOpsem.grow (gtAdGd GT) i) u n →
    u + (n + 1) < (AxOpsem.grow (gtAdGd GT) i).length →
    j ≤ n →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = AxSpinHdB.pac 0x1a → hitW rs0 (AxSpinHdB.pac 0x1a) →
    -- the lock word (`s1 = lk`)
    paZ Pl = L.xlLk → ¬ L.xlText (paZ Pl) →
    dataAtS σi T (accAmo true) (gprVal rs0 9#5) 4 Pl → hitW rs0 (gprVal rs0 9#5) →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      notheld nm.xnReg L.xlLk i -∗
      AxSpinAq1.KSpin (hlc := hlc) L GT nm T satp0 i cpu Ψ u n rs0 -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, u + j⟩ Ψ := by
  intro Hrmw Hvals Hlen hj Hc HPC Hhit Hpl Hntx Hda Hhv
  exact AxSpinAq1.spinLoop L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxt Ψ HΨmid
    u n rs0 Pl Hrmw Hvals Hlen Hpl Hntx Hda Hhit Hhv (n + 1 - j) j (by omega) (by omega) rs0 ib0
    Hc HPC rfl (fun _ _ => rfl)

include HL Hcons hmode hasid hppn Hfix Htxt HΨmid in
/-- `wpdSpin 0 n` at acquire's row position `u = aqKh k b hb` (the boundary after `holding`'s
return): the claim is at `aqKA k b hb n`, the continuation at `aqKm k b hb n` (both
definitionally `aqKh + n` / `aqKh + (n + 1)`, AxSpinAqr). -/
theorem wpdSpinAq (k : Nat) (b hb : Bool) (n : Nat) (rs0 : RegFile) (ib0 : Ibch)
    (Pl : BitVec 64) :
    AxSpinAq1.spinRmw (AxOpsem.grow (gtAdGd GT) i) (aqKh k b hb) n L.xlLk →
    spinVals (AxOpsem.grow (gtAdGd GT) i) (aqKh k b hb) n →
    aqKm k b hb n < (AxOpsem.grow (gtAdGd GT) i).length →
    ctrlOkSW T satp0 rs0 → rs0 .PC = AxSpinHdB.pac 0x1a → hitW rs0 (AxSpinHdB.pac 0x1a) →
    paZ Pl = L.xlLk → ¬ L.xlText (paZ Pl) →
    dataAtS σi T (accAmo true) (gprVal rs0 9#5) 4 Pl → hitW rs0 (gprVal rs0 9#5) →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      notheld nm.xnReg L.xlLk i -∗
      AxSpinAq1.KSpin (hlc := hlc) L GT nm T satp0 i cpu Ψ (aqKh k b hb) n rs0 -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, aqKh k b hb⟩ Ψ := by
  intro Hrmw Hvals Hlen Hc HPC Hhit Hpl Hntx Hda Hhv
  exact wpdSpin L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxt Ψ HΨmid
    (aqKh k b hb) 0 n rs0 ib0 Pl Hrmw Hvals Hlen (Nat.zero_le _) Hc HPC Hhit Hpl Hntx Hda Hhv

end spin

end Weak
