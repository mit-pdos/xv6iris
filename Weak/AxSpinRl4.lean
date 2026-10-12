/-
Weak: **xv6's REAL `release`, positional WPd, part 1** — the TEXT of `release` (release =
0x80000ce0) for the positional engine, the per-word `textOkB` tokens it lacked, a non-vacuity
certificate for the text premise, and THE HEAD `wpdRelHead` (release + 0x00 … + 0x1a: the three
spills, `jal holding` composed with `AxSpinHdC.holdingFromRelease'`, the falling `c.beqz`, the
lk->cpu store, the fence and the releasing store) — Theorem 2 design
(`notes/weak-lb-thm2-design.md` §C.2, §D row `AxSpinRl4`).  NEW Lean file (no Rocq source:
Rocq's `AxSpinRs`/`AxSpinRl*` were never written).  `AxSpinRl4b.wpdRelease` composes the head
with `jal pop_off` / `AxSpinPO6.wpdPopOff` and the epilogue.

## What this file provides

§1 THE WORDS / ASTs and `releaseText σi T` (17 conjuncts, `textAtS` / `textAt4S` at
   `AxSpinHdB.prl off`).  KERNEL CROSS-CHECK (`Xv6/KernelImage.lean`, release = 0x80000ce0):
   `AxSpinRl4.relCodeImg` (`decide +kernel` on `Xv6.Kernel.textTree`) — every
   (offset, width, encoding) of `AxSpinRl4.relCode` is this tree's instruction, and
   `AxSpinRl4.relCodeContig` — the 17 instructions are contiguous from + 0x00 to + 0x2c (the
   panic arm, never executed on a covered row):
```
  + 0x00 c.addi sp,-32   0x1101   + 0x10 c.beqz a0,+28  0xcd11      + 0x22 c.ldsp ra,24(sp) 0x60e2
  + 0x02 c.sdsp ra,24    0xec06   + 0x12 sd zero,16(s1) 0x0004b823  + 0x24 c.ldsp s0,16(sp) 0x6442
  + 0x04 c.sdsp s0,16    0xe822   + 0x16 fence rw,w     0x0310000f  + 0x26 c.ldsp s1,8(sp)  0x64a2
  + 0x06 c.sdsp s1,8     0xe426   + 0x1a sw zero,0(s1)  0x0004a023  + 0x28 c.addi16sp 32    0x6105
  + 0x08 c.addi4spn s0   0x1000   + 0x1e jal pop_off    0xf9bff0ef  + 0x2a c.ret            0x8082
  + 0x0a c.mv s1,a0      0x84aa
  + 0x0c jal holding     0xf07ff0ef
```
   The jal targets (as AxSpinCtl3's kernel cross-check `jalDecode`/`jalTargets`, re-checked
   here at the positional pc names, `decide +kernel`): + 0x0c → holding = `pch 0` (imm
   2096902), + 0x1e → pop_off = `ppp 0` (imm 2097050) — `AxSpinRl4.jalTgts`; the decodes are
   the kernel walks `AxSpinRl4.walk0cM`/`walk1eM`.
§2 TOKENS (`textOkB`, generic in the pc) for the six words no earlier file tokenised:
   `twrCd11` (c.beqz a0, compressed, `tokR`), `tw4R0c` / `tw4R1e` (the two jals), `tw4R12`
   (sd zero,16(s1)), `tw4R16` (fence rw,w), `tw4R1a` (sw zero,0(s1)) — 4-byte, `tokB` with the
   decoder's kernel walks on `drefM` / `WkEntryNew.drefS0` (the AxSpinAqd recipe).  The other
   eleven words are push_off's / acquire's / pop_off's (`tw1101`, `twEc06`, `twE822`, `twE426`,
   `tw1000` (AxSpinPOt1), `twa84aa` (AxSpinAqt1), `tw60e2`, `tw6442` (AxSpinPOt2), `tw64a2`,
   `tw6105`, `tw8082` (AxSpinPOt3)).
§3 NON-VACUITY of `releaseText`: `AxSpinRl4.releaseTextOf` — the 17 conjuncts HOLD at the image
   `AxSpinRl4.σRel` (= `AxSpinTextCerts.σK`'s construction, the REAL kernel bytes read off
   `Xv6.Kernel.textTree` by `AxSpinTextCerts.kByte`, overlaid on [0x80000ce0, 0x80000d0c)) and
   the page map `AxSpinE8f.tT` (page 0x80000, VA = PA).
§4 THE HEAD `wpdRelHead`: for every `k`, `c` and every row with `RowRelease k c …`
   (AxSpinRl1), from the entry state (PC = release + 0x00) at row position `k`:
     + 0x00 c.addi sp,-32 (XxReg) → three spills at k, k+1, k+2 (XxSt) → c.addi4spn, c.mv s1,a0,
     jal holding (XxReg, link = release + 0x10) → `holdingFromRelease'` at `relKh k` (the
     holder's path; the claim `kc`'s `locked` drawn by `FldMWLkheld`; acquire's lk->cpu store at
     `kw` read back by `FldMCpuOwn`) → c.beqz a0 FALLS (XxReg; the value pin below) →
     `XxSdCpuRel` at `relKc k` (value 0; the lk->cpu handle is `OOwn`'s) → `XxFenceRel` at
     `relKf k` → `XxSwRelRel` at `relKw k` (anchors: holding's `OHeld` deposit at `relKh k`,
     the sd's deposit at `relKc k`, the caller's nextpid write at `ks`)
   and continues at `relKp k` (PC = release + 0x1e, the `jal pop_off`) with sp = release's
   frame, s1 = the lock address, every GPR but ra/sp/s0/s1/a0/a5 kept, the spills' row data,
   and the deposited `(i, relKw k) ↦ₐ notheld i`.

## Stage 2 P-FORM (Lean-only; notes/weak-lb-thm2-stage2.md §A–§C row `AxSpinRl4/4b`, Q-S2-1/2/9)

§5 `RowReleaseP k c hb row …` = `RowShXP k row (relSh c …)` (AxSpinT2f; the window matched at
   every PRESENT position) ∧ `relKh k < LEN → lkBranch row (relKh k) hb` (holding's lw fixes the
   branch bit when present) ∧ `hb = false → LEN ≤ relKh k + 1` (the `rlS` GATE, T2f's
   `t2GateOk .rlS`: a row whose lock word read 0 ends at the cut).  No length conjunct.  NOTE: the
   stage-1 conjunct `lkBranch (relKh k) true` of `RowRelease` is GONE — release now handles
   `hb = false` through the `rlS` arm.  Projections `AxSpinRl4.rowRelPOfFull` (`RowRelease →
   RowReleaseP … true`), `relPHead`, `relPHolding` (via `AxSpinRl4.rowHoldingPOf`, the prefix
   `rowHoldingOf` for either branch), `relPLk`, `relPCpu`, `relPFence`, `relPPop`, `relPNowr`
   (`rowReleaseNowr` once the positions up to the reload are present); `AxSpinRl4.gvLt` (a graph
   value is at a present position); `AxSpinRl4.xxSwRelRelP` (`XxSwRelRel` with its three row facts
   and the length bound as premises instead of `RowRelease`).
§6 `wpdRelHeadP`: `wpdRelHead`'s script, one `by_cases` per row position (`k`, `k+1`, `k+2`,
   `relKh k`, holding's window inside `holdingFromReleaseP`, `relKh k + 12`, `relKf k`,
   `relKw k`).  Row ends:
   * the WINDOWED, RESOURCE-FREE hook (exact merged form, AxSpinE8 / PO4 / HdA / PO6 headers)
     `HΨend : ∀ k', k ≤ k' → k' ≤ relKw k → (hb = false → k' ≠ relKh k + 1) → k' ≠ relKh k + 12 →
        LEN ≤ k' → ∀ pr, ⊢ wpdM … ⟨pr, k'⟩ Ψ`;
   * the two DESIGNATED CUTS of release (T2f `cutPos .rlS` / `.rlL`), EXCLUDED from the hook, as
     RESOURCE-CARRYING premises for `AxSpinT2h` to supply:
     `KrlS : hb = false → ⊢ (i, ks) ↦ₐ RNp -∗ KShortEnd … (relKh k) (OHeld … ∗ (i, kw)-handle)`
     (holding's short arm, `AxSpinHdC.holdingFromReleaseP`'s `rlS` end: the lw value, `OHeld`'s
     ⌜bytes ≠ 0⌝ deposit — `AxSpinT2g.heldNonzero` — and the unused lk->cpu handle; also used on
     the short arm's NON-end continuation, which the gate forces to `LEN = relKh k + 1`);
     `KrlL : hb = true → ∀ rs, tp rs = tp rs0 → a0 rs = a0 rs0 → ⊢ (i, ks) ↦ₐ RNp -∗
        KLongEnd … (relKh k) rs … (OHeld …) (OOwn … (relKh k + 4) …)` (the long arm's end: both
     load outputs incl. `OOwn`'s readback ⌜bytes read = val's bytes⌝ — `AxSpinT2g.ownIsMine` —
     and the five reload annotations, at EVERY holding entry state `rs` with release's tp / a0;
     also used on `KLong` when the row ends exactly there).
   The rlL gate is the guarded pin `relKh k + 12 < LEN → graphValue (i, relKh k + 4) = some
   (stBytes 8 (mycpuRet tp))` (T2f `t2GateOk .rlL`; stage 1's unguarded `Hvcpu`).  Every other pin
   and row item premise is GUARDED by its position (`relKh k + 7/9/11 < LEN`, `relKh k < LEN →
   row[kc]? / row[kw]?`, `relKw k < LEN → row[relKw k]? / row[ks]?`).
`wpdRelHead` keeps its exact name and statement and is now the corollary (`hb = true`; hook and
both arms vacuous under `relKe k c < LEN`; pins unguarded).

## P1 GATE FORM (Lean-only; notes/weak-lb-thm2-pins.md §P1)

`wpdRelHeadG` = `wpdRelHeadP` with holding's three RELOAD pins (AllocPins2 `rhMy` / `rhRet` /
`rhS1`) replaced IN THEIR SLOTS by `AxSpinT2i.Gate`s — `Gate (relKh k + 7) (stBytes 8 (pch
0x1a))` (mycpu's ra reload inside holding), `Gate (relKh k + 9) (stBytes 8 (release + 0x10))`
(holding's ra reload; its spill is the link of release's OWN `jal holding`, computed from the
`jal`, `gprVal rs7 ra = release + 0x10`), `Gate (relKh k + 11) (stBytes 8 (gprVal rs0 a0))`
(holding's s1 reload; release's s1 = a0 after `c.mv s1,a0`) — and composed with
`AxSpinHdC.holdingFromReleaseG` (entry-ra return, `KLongG`, whose ⌜relKh k + 12 < LEN ∧ … ∧ vs1 =
s1⌝ replaces the old `E12` split and the `Hvs1` use).  A wrong reload value at either reload's row
end is refuted inside holding (`cutReloadG`).  The `rlL` gate (`Hvcpu`, a value pin of T2f's
`t2GateOk .rlL`, not a reload) and everything else are `wpdRelHeadP`'s.  `wpdRelHeadP` is now
the corollary `wpdRelHeadG ∘ AxSpinT2i.gateOfPinG` ×3 (statement unchanged; no free return
address, so no separate `…Gr` core is needed); `wpdRelHead` as before.  HONESTY: `wpdRelHeadG`
has no reload pin; `Hvcpu` remains (the rlL gate).

## P1 VALUE HOOK (Lean-only; the shape is AxSpinE8's header "P1 VALUE HOOK")

`wpdRelHeadG`'s hook takes, after `LEN ≤ k'` and before `∀ pr`, `AxSpinE8.EndRl GT i (if hb then
[(relKh k + 7, some (stBytes 8 (pch 0x1a))), (relKh k + 9, some (stBytes 8 (prl 0x10))),
(relKh k + 11, some (stBytes 8 (gprVal rs0 r10)))] else []) k'` (its three gates `rhMy` / `rhRet`
/ `rhS1`, on holding's long arm; holding's value hook `holdingFromReleaseG` is handed them via
`Era7'`/`Es17`; the `rhS1` row end `relKh k + 12` is the designated cut `rlL`, outside the hook,
whose arm `KrlL` receives the values and annotations as before).  Nothing else in its statement
changed; `wpdRelHeadP`/`wpdRelHead` unchanged.

## Pins and row premises (honesty notes)

1. GRAPH-VALUE PINS (Q20', provisional Option V; the theorem proves nothing about a graph whose
   values differ): holding's two return reloads (`(i, relKh k + 7)` = holding + 0x1a, `(i,
   relKh k + 9)` = release + 0x10, exactly `holdingFromRelease'`'s); holding's lk->cpu read
   `(i, relKh k + 4)` returns `stBytes 8 (mycpuRet tp)` (the design's "vcpu = cpuAddr i": so
   holding returns 1 and `c.beqz a0,panic` falls — `Hvcpu`); holding's s1 reload `(i, relKh k +
   11)` returns `stBytes 8 lk` (`Hvs1`; the design's "the reload's graph value = &lock is a pin
   like Hval": holding restores s1 from its private slot, and the sd / sw bases are s1).
   Ownership already implies the first two morally (the reloads read the private spills, the
   `RLfact` annotations) and `FldMCpuOwn` deposits ⌜the lk->cpu bytes read = acquire's sd
   bytes⌝ — but those facts are annotations, not pure facts the WPd can branch on.
2. ROW PREMISES on hart `i`'s OWN events, named as AxSpinRl2 / AxSpinRl3 ask (AxSpinT2a will
   supply them from `allocFull`): `HcpuWinW` / `HcpuWinR` — `CpuWin L GT i e` for both possible
   `OOwn` anchors `e = (i, kw)` (acquire's sd) and `e = (i, relKh k + 4)` (holding's read)
   (AxSpinRl2 deviation 2); `HrelZ4` — the releasing store's row label writes `z4` with class
   `WCrel`; `HrelOnly` — no lock-word write of hart `i` after `relKc k` other than the
   releasing store (AxSpinRl3 deviation 2).  `Hnoint` (no lk->cpu write between acquire's sd
   and holding's read) is `holdingFromRelease'`'s.
3. The text premises `releaseText` / `holdingText` / `mycpuText` are satisfiable
   (`releaseTextOf` here; holding's / mycpu's by their own certificates).

## Deviations from the design

1. Split at the pop_off seam (heartbeats): this file ends at `relKp k`; `AxSpinRl4b` has
   `wpdRelease`.  The head's post does not report ra / s0 / a0 / a5 (overwritten by pop_off and
   release's own reloads) nor holding's deposits other than the anchors it consumes; the
   anchors' frames `Qc` (claim) / `Qw` (acquire's sd) are dropped (`XxSwRelRel` deviation 3).
2. `releaseWpd5` (AxSpinCtl3) is SUPERSEDED and not used (not imported); its jal-target
   cross-check is re-done at the positional pc names (`AxSpinRl4.jalTgts`, same immediates).

**Reused:** `XxReg`/`XxSt` (AxSpinE6), `certAddi`/`certAdd` (AxSpinE7), `certJAL`/`certBTYPE`/
`brOt`/`tgtOf`/`gval`/`linkOw` (AxSymCtl2), `stepRegs`/`stepRegs0`/`gbPc`/`gbTlb`/`gbCtrl`/
`retxRefl`/`hitWSvpn`/`ldResStBytes8`/`gprValZero` (AxSpinE8), `hitWAgree` (AxSpinE),
`tokR`/`tokB` (AxSpinE7), `holdingFromRelease'` (AxSpinHdC), `KLong`/`OHeld`/`OOwn` (AxSpinHdA/
HdB), `XxSdCpuRel`/`XxFenceRel`/`CpuWin` (AxSpinRl2), `XxSwRelRel` (AxSpinRl3),
`RowRelease`/`relK*`/`rowReleaseHead`/`rowReleaseHolding` (AxSpinRl1), `AxSpinPO1.slot8`/`spo`,
`AxSpinTextCerts.kByte`/`pageOk`/`chkD`/`textAtA`/`textAtU`/`text4A`/`text4U`.
Stage 2: `holdingFromReleaseP`/`KShortEnd`/`KLongEnd` (AxSpinHdC/HdA), `XxSdCpu`/`XxFence`
(AxSpinRl2), `XxSwRel` (AxSpinRl3), `RowShXP`/`rowShXP*`/`AxSpinT2f.gvGrow` (AxSpinT2f),
`RowShP`/`rowShP*` (AxSpinRowP), `RowHoldingP` (AxSpinHd8), `AxSpinPO5.rowMycpuPOf`,
`rowShXNowr`/`xshapeRB` (AxSpinRl1).
P1: `holdingFromReleaseG`/`KLongG` (AxSpinHdC/HdA), `AxSpinT2i.Gate`/`gateOfPinG` (AxSpinT2i).
All new names grepped absent from the tree (stage 2: `RowReleaseP`, `wpdRelHeadP`, and the
file-qualified `AxSpinRl4.*` helpers; P1: `wpdRelHeadG`).

**W13 (I) (plan `notes/weak-allocproc-plan.md` §C W13 (I); [OWN.27]).** the release lemmas' anchor-domain premise is `(lbIsR l || lbIsW l) = true` (was `lbIsMem l = true`): `gwf` admits I/O events, which `fence rw,w` does not order (RVWMO; D48).
-/
import Weak.AxSpinRl3
import Weak.AxSpinHdC
import Weak.AxSpinPO1
import Weak.AxSpinPOt2
import Weak.AxSpinPOt3
import Weak.AxSpinAqt1
import Weak.AxSpinAqd
import Weak.AxSpinTextCerts
import Weak.AxSpinT2f

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 1. The words, the instructions, the text -/

/-- `jal holding` (release + 0x0c). -/
def Wr0c : BitVec 32 := 0xf07ff0ef#32
/-- `sd zero,16(s1)` (release + 0x12). -/
def Wr12 : BitVec 32 := 0x0004b823#32
/-- `fence rw,w` (release + 0x16). -/
def Wr16 : BitVec 32 := 0x0310000f#32
/-- `sw zero,0(s1)` (release + 0x1a). -/
def Wr1a : BitVec 32 := 0x0004a023#32
/-- `jal pop_off` (release + 0x1e). -/
def Wr1e : BitVec 32 := 0xf9bff0ef#32

/-- `jal holding`. -/
def rl0c : instruction := .JAL (2096902#21, .Regidx 1#5)
/-- `c.beqz a0,+28` (the panic arm at + 0x2c). -/
def rl10 : instruction :=
  .BTYPE (sign_extend (m := 13) (14#8 +++ 0b0#1), zreg, creg2reg_idx (.Cregidx 2#3), .BEQ)
/-- `sd zero,16(s1)`. -/
def rl12 : instruction := .STORE (16#12, .Regidx 0#5, .Regidx 9#5, 8)
/-- `sw zero,0(s1)`. -/
def rl1a : instruction := .STORE (0#12, .Regidx 0#5, .Regidx 9#5, 4)
/-- `jal pop_off`. -/
def rl1e : instruction := .JAL (2097050#21, .Regidx 1#5)

/-- (Lean-only) release's 17 non-panic instructions as (offset, width, encoding). -/
def AxSpinRl4.relCode : List (Nat × Nat × Nat) :=
  [(0x00, 2, 0x1101), (0x02, 2, 0xec06), (0x04, 2, 0xe822), (0x06, 2, 0xe426),
   (0x08, 2, 0x1000), (0x0a, 2, 0x84aa), (0x0c, 4, Wr0c.toNat), (0x10, 2, 0xcd11),
   (0x12, 4, Wr12.toNat), (0x16, 4, Wr16.toNat), (0x1a, 4, Wr1a.toNat), (0x1e, 4, Wr1e.toNat),
   (0x22, 2, 0x60e2), (0x24, 2, 0x6442), (0x26, 2, 0x64a2), (0x28, 2, 0x6105),
   (0x2a, 2, 0x8082)]

/-- (Lean-only) THE IMAGE CHECK: every entry of `AxSpinRl4.relCode` is this tree's kernel
instruction at `release + off`. -/
theorem AxSpinRl4.relCodeImg :
    AxSpinRl4.relCode.all (fun c =>
      match Xv6.Kernel.textTree.find? (KernelSyms.«release» + c.1) with
      | some k => Nat.beq k.width c.2.1 && Nat.beq k.enc c.2.2
      | none => false) = true := by
  decide +kernel

/-- (Lean-only) contiguous from `release + 0x00` to `+ 0x2c` (the panic arm). -/
theorem AxSpinRl4.relCodeContig :
    AxSpinRl4.relCode.length = 17 ∧ AxSpinRl4.relCode.head?.map (·.1) = some 0x00 ∧
    ((AxSpinRl4.relCode.zip AxSpinRl4.relCode.tail).all fun p =>
      Nat.beq (p.1.1 + p.1.2.1) p.2.1) = true ∧
    AxSpinRl4.relCode.getLast?.map (fun c => c.1 + c.2.1) = some 0x2c := by
  decide +kernel

/-- (Lean-only) the jal targets at the positional engine's pc names (AxSpinCtl3's
`jalTargets`). -/
theorem AxSpinRl4.jalTgts :
    AxSpinHdB.prl 0x0c + sign_extend (m := 64) (2096902#21 : BitVec 21) = pch 0 ∧
    AxSpinHdB.prl 0x1e + sign_extend (m := 64) (2097050#21 : BitVec 21) = ppp 0 := by
  decide +kernel

section text
variable (σi : ExecSt) (T : PTree)

/-- THE TEXT of `release` (17 words, the panic arm excluded). -/
def releaseText : Prop :=
  textAtS σi T (AxSpinHdB.prl 0x00) (AxSpinE7.hw 0x1101) ∧
  textAtS σi T (AxSpinHdB.prl 0x02) (AxSpinE7.hw 0xec06) ∧
  textAtS σi T (AxSpinHdB.prl 0x04) (AxSpinE7.hw 0xe822) ∧
  textAtS σi T (AxSpinHdB.prl 0x06) (AxSpinE7.hw 0xe426) ∧
  textAtS σi T (AxSpinHdB.prl 0x08) (AxSpinE7.hw 0x1000) ∧
  textAtS σi T (AxSpinHdB.prl 0x0a) (AxSpinE7.hw 0x84aa) ∧
  textAt4S σi T (AxSpinHdB.prl 0x0c) Wr0c ∧
  textAtS σi T (AxSpinHdB.prl 0x10) (AxSpinE7.hw 0xcd11) ∧
  textAt4S σi T (AxSpinHdB.prl 0x12) Wr12 ∧
  textAt4S σi T (AxSpinHdB.prl 0x16) Wr16 ∧
  textAt4S σi T (AxSpinHdB.prl 0x1a) Wr1a ∧
  textAt4S σi T (AxSpinHdB.prl 0x1e) Wr1e ∧
  textAtS σi T (AxSpinHdB.prl 0x22) (AxSpinE7.hw 0x60e2) ∧
  textAtS σi T (AxSpinHdB.prl 0x24) (AxSpinE7.hw 0x6442) ∧
  textAtS σi T (AxSpinHdB.prl 0x26) (AxSpinE7.hw 0x64a2) ∧
  textAtS σi T (AxSpinHdB.prl 0x28) (AxSpinE7.hw 0x6105) ∧
  textAtS σi T (AxSpinHdB.prl 0x2a) (AxSpinE7.hw 0x8082)

end text

/-! # 2. Tokens -/

/-- (Lean-only) `tokR` with the decode by the kernel walk at `drefMisa` (AxSpinAqt1's). -/
local macro "ax_spin_rl4_tokr" h:term:max i0:term:max hex:term:max ht:term:max : tactic =>
  `(tactic| (
    refine tokR _ _ _ _ $h $i0 _ $ht ?_ ?_ True.intro $hex
    · unfold ext_decode_compressed encdec_compressed_backwards
      simp (config := { decide := true }) only [↓reduceIte]
      rff_auto
    · intro s hm
      refine execOfRunRead drefMisa _ s _ true ?_ (by ax_epi_ledger_krfl)
      intro r v hv
      unfold drefMisa at hv
      split at hv <;> simp only [Option.some.injEq, reduceCtorEq] at hv
      subst hv
      exact hm))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
theorem rfFDr0c : rfF (ext_decode Wr0c) := by
  unfold Wr0c ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
theorem rfFDr12 : rfF (ext_decode Wr12) := by
  unfold Wr12 ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
theorem rfFDr16 : rfF (ext_decode Wr16) := by
  unfold Wr16 ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
theorem rfFDr1a : rfF (ext_decode Wr1a) := by
  unfold Wr1a ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
theorem rfFDr1e : rfF (ext_decode Wr1e) := by
  unfold Wr1e ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

theorem AxSpinRl4.walk0cM : runRead drefM (ext_decode Wr0c) = some (rl0c, true) := by kernel_rfl
theorem AxSpinRl4.walk0cS : runRead WkEntryNew.drefS0 (ext_decode Wr0c) = some (rl0c, true) := by
  kernel_rfl
theorem AxSpinRl4.walk12M : runRead drefM (ext_decode Wr12) = some (rl12, true) := by kernel_rfl
theorem AxSpinRl4.walk12S : runRead WkEntryNew.drefS0 (ext_decode Wr12) = some (rl12, true) := by
  kernel_rfl
theorem AxSpinRl4.walk16M : runRead drefM (ext_decode Wr16) = some (fenceRwW, true) := by
  kernel_rfl
theorem AxSpinRl4.walk16S : runRead WkEntryNew.drefS0 (ext_decode Wr16) = some (fenceRwW, true) := by
  kernel_rfl
theorem AxSpinRl4.walk1aM : runRead drefM (ext_decode Wr1a) = some (rl1a, true) := by kernel_rfl
theorem AxSpinRl4.walk1aS : runRead WkEntryNew.drefS0 (ext_decode Wr1a) = some (rl1a, true) := by
  kernel_rfl
theorem AxSpinRl4.walk1eM : runRead drefM (ext_decode Wr1e) = some (rl1e, true) := by kernel_rfl
theorem AxSpinRl4.walk1eS : runRead WkEntryNew.drefS0 (ext_decode Wr1e) = some (rl1e, true) := by
  kernel_rfl

section toks
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- `c.beqz a0,+28` (0xcd11). -/
theorem twrCd11 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0xcd11)) :
    textOkB σi T satp0 pc true rl10 := by
  ax_spin_rl4_tokr (0xcd11#16) (.C_BEQZ (14#8, .Cregidx 2#3)) (execExecuteCBEQZ _ _) H

theorem tw4R0c (pc : BitVec 64) : textAt4S σi T pc Wr0c → textOkB σi T satp0 pc false rl0c :=
  fun H => tokB σi T satp0 _ _ _ H (by decide) rfFDr0c
    (WkEntryNew.execAnyCfg _ _ AxSpinRl4.walk0cM AxSpinRl4.walk0cS)

theorem tw4R12 (pc : BitVec 64) : textAt4S σi T pc Wr12 → textOkB σi T satp0 pc false rl12 :=
  fun H => tokB σi T satp0 _ _ _ H (by decide) rfFDr12
    (WkEntryNew.execAnyCfg _ _ AxSpinRl4.walk12M AxSpinRl4.walk12S)

theorem tw4R16 (pc : BitVec 64) : textAt4S σi T pc Wr16 → textOkB σi T satp0 pc false fenceRwW :=
  fun H => tokB σi T satp0 _ _ _ H (by decide) rfFDr16
    (WkEntryNew.execAnyCfg _ _ AxSpinRl4.walk16M AxSpinRl4.walk16S)

theorem tw4R1a (pc : BitVec 64) : textAt4S σi T pc Wr1a → textOkB σi T satp0 pc false rl1a :=
  fun H => tokB σi T satp0 _ _ _ H (by decide) rfFDr1a
    (WkEntryNew.execAnyCfg _ _ AxSpinRl4.walk1aM AxSpinRl4.walk1aS)

theorem tw4R1e (pc : BitVec 64) : textAt4S σi T pc Wr1e → textOkB σi T satp0 pc false rl1e :=
  fun H => tokB σi T satp0 _ _ _ H (by decide) rfFDr1e
    (WkEntryNew.execAnyCfg _ _ AxSpinRl4.walk1eM AxSpinRl4.walk1eS)

end toks

/-! # 3. Non-vacuity of `releaseText` -/

/-- (Lean-only) release's byte range. -/
def AxSpinRl4.inRel (n : Nat) : Bool := decide (0x80000ce0 ≤ n) && decide (n < 0x80000d0c)

/-- (Lean-only) the image memory: kernel text on release's range, else `AxSpinE8f.σ8`'s. -/
def AxSpinRl4.memRel (a : BitVec 64) : Option (BitVec 8) :=
  if AxSpinRl4.inRel a.toNat then AxSpinTextCerts.kByte a.toNat else AxSpinE8f.σ8.mem a

/-- (Lean-only) THE IMAGE. -/
def AxSpinRl4.σRel : ExecSt := ⟨AxSpinE8f.σ8.regs, AxSpinRl4.memRel, AxSpinE8f.σ8.dev⟩

/-- (Lean-only) page 0x80000 in `σRel`. -/
theorem AxSpinRl4.pageR :
    AxSpinTextCerts.pageOk AxSpinRl4.σRel AxSpinE8f.tT AxSpinE8f.vpnD
      AxSpinE8f.P2 AxSpinE8f.P1 AxSpinE8f.L0leaf :=
  ⟨AxSpinE8f.mapsD,
    ⟨by unfold BytesAt; decide +kernel, by decide +kernel, by decide +kernel⟩,
    ⟨by unfold BytesAt; decide +kernel, by decide +kernel, by decide +kernel⟩,
    ⟨by unfold BytesAt; decide +kernel, by decide +kernel, by decide +kernel⟩,
    AxSpinTextCerts.chkD, by decide +kernel, by unfold ptePbmt0; decide +kernel⟩

/-- (Lean-only) one text conjunct: the fitting constructor, residual by kernel. -/
local macro "ax_spin_rl4_txt" : tactic => `(tactic|
  first
  | exact AxSpinTextCerts.textAtA AxSpinRl4.pageR _ _ (by decide +kernel)
  | exact AxSpinTextCerts.textAtU AxSpinRl4.pageR _ _ (by decide +kernel)
  | exact AxSpinTextCerts.text4U AxSpinRl4.pageR _ _ (by decide +kernel)
  | exact AxSpinTextCerts.text4A AxSpinRl4.pageR _ _ (by decide +kernel))

/-- (Lean-only) `releaseText` HOLDS at the instance (17 conjuncts). -/
theorem AxSpinRl4.releaseTextOf : releaseText AxSpinRl4.σRel AxSpinE8f.tT := by
  unfold releaseText
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ax_spin_rl4_txt

/-! # 4. THE HEAD -/

/-- (Lean-only) holding returns 1 when the lk->cpu read is mycpu's address. -/
theorem AxSpinRl4.hresSelf (x : BitVec 64) : hres (0#64 + x) x = 1#64 := by
  unfold hres
  rw [BitVec.zero_add, BitVec.sub_self]
  decide

/-- (Lean-only) `OHeld` at its designated read. -/
theorem AxSpinRl4.oHeldAt {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF]
    [AxannotGS GF] [AxSpinX.Xv6G GF] (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent)
    (kc kr : Nat) (Q : IProp GF) (v : List (BitVec 8)) :
    OHeld L GT nm i kc kr Q kr v =
      iprop(AxAnnot.annotOwn (i, kr) iprop(locked nm.xnReg L.xlLk i (i, kc) ∗ Q) ∗
        AxAnnot.annotOwn (i, kr)
          iprop(⌜∀ t b, greadsByte (gtAdGd GT).gdG (i, kr) L.xlLk t b → b ≠ b0⌝)) :=
  if_pos rfl

/-- (Lean-only) `OOwn` at its designated read. -/
theorem AxSpinRl4.oOwnAt {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF]
    [AxannotGS GF] [AxSpinX.Xv6G GF] (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent)
    (kw kr : Nat) (val : BitVec 64) (Q : IProp GF) (v : List (BitVec 8)) :
    OOwn L GT nm i kw kr val Q kr v =
      iprop((∃ e' : Geid, ⌜e' = (i, kw) ∨ e' = (i, kr)⌝ ∗
          AxAnnot.annotOwn e'
            iprop(Q ∗ RVL nm.xnH (gtAdGd GT) (clb L) e' (WeakInterpProj.wbytes 8 val))) ∗
        AxAnnot.annotOwn (i, kr)
          iprop(⌜∀ (j : Nat) a t b, (clb L)[j]? = some a →
            greadsByte (gtAdGd GT).gdG (i, kr) a t b →
            (WeakInterpProj.wbytes 8 val)[j]? = some b⌝)) :=
  if_pos rfl

/-- (Rocq `zsimp`) evaluate the closed `upd` tests. -/
local macro "ax_spin_rl4_zsimp" loc:(ppSpace Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := decide) only [AxSpinE8.updSame, AxSpinE8.updOther, AxSpinE8.updZero]
    $[$loc]?)

/-! # 5. Stage 2: release's PREFIX row (§4 THE HEAD follows in §6) -/

/-- (Lean-only, stage 2 P-form) THE ROW OF release on a PREFIX: the window `relSh c …` matched at
every PRESENT position (`RowShXP`, AxSpinT2f), holding's lw value fixes the branch bit `hb` when
the lw is present (`lkBranch`, guarded), and the `rlS` GATE: a row whose lw read 0 (`hb = false`:
holding returns 0, `c.beqz a0,panic` is taken) ENDS at the cut `relKh k + 1` (a row that
continues past a gate took the normal arm, design §A).  No length conjunct. -/
def RowReleaseP (k : Nat) (c hb : Bool) (row : List Lbl)
    (pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint : Int) : Prop :=
  RowShXP k row (relSh c pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint) ∧
  (relKh k < row.length → lkBranch row (relKh k) hb) ∧
  (hb = false → row.length ≤ relKh k + 1)

/-- (Lean-only) holding's prefix window (`RowHoldingP`, either branch) from the long window
`holdShB true …` matched on a prefix (`AxSpinRl1.rowHoldingOf` on prefixes; the short window is
the long one's first item). -/
theorem AxSpinRl4.rowHoldingPOf (k : Nat) (row : List Lbl) (hb : Bool)
    (plk pcl pra ps0 ps1 pram ps0m : Int) :
    RowShP k row (holdShB true plk pcl pra ps0 ps1 pram ps0m) →
    (k < row.length → lkBranch row k hb) →
    RowHoldingP k row hb plk pcl pra ps0 ps1 pram ps0m := by
  intro H Hb
  refine ⟨Hb, ?_⟩
  cases hb with
  | false =>
    intro j Hj Hk
    match j, Hj, Hk with
    | 0, _, Hk => exact H 0 _ rfl Hk
  | true =>
    refine ⟨fun j Hj Hr Hk => ?_, ?_⟩
    · match j, Hj, Hr, Hk with
      | 0, _, _, Hk => exact H 0 _ rfl Hk
      | 1, _, _, Hk => exact H 1 _ rfl Hk
      | 2, _, _, Hk => exact H 2 _ rfl Hk
      | 3, _, _, Hk => exact H 3 _ rfl Hk
      | 4, _, _, Hk => exact H 4 _ rfl Hk
      | 9, _, _, Hk => exact H 9 _ rfl Hk
      | 10, _, _, Hk => exact H 10 _ rfl Hk
      | 11, _, _, Hk => exact H 11 _ rfl Hk
      | 5, _, Hr, _ | 6, _, Hr, _ | 7, _, Hr, _ | 8, _, Hr, _ => omega
    · apply AxSpinPO5.rowMycpuPOf
      intro j it Hj Hk
      obtain ⟨lb, Hlb, Hs⟩ := H (5 + j) it (by
          simp only [holdShB, ↓reduceIte]
          rw [List.getElem?_append_left (by
              have := (List.getElem?_eq_some_iff.1 Hj).1
              simp only [mycLen] at this; simp only [List.length_append, mycLen,
                List.length_cons, List.length_nil]; omega),
            List.getElem?_append_right (by simp)]
          simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_sub_cancel_left]
          exact Hj) (by omega)
      exact ⟨lb, by rw [show k + 5 + j = k + (5 + j) by omega]; exact Hlb, Hs⟩

/-- (Lean-only) a graph value is read at a PRESENT row position. -/
theorem AxSpinRl4.gvLt (GD : Gdexec) (i k : Nat) (v : List (BitVec 8)) :
    graphValue GD (i, k) = some v → k < (AxOpsem.grow GD i).length := by
  rw [AxSpinT2f.gvGrow]
  unfold AxSpinT2f.rv
  intro h
  cases hk : (AxOpsem.grow GD i)[k]? with
  | none => simp [hk] at h
  | some lb => exact (List.getElem?_eq_some_iff.1 hk).1

section rowrelp
variable {k : Nat} {c hb : Bool} {row : List Lbl}
  {pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint : Int}

/-- (Lean-only) a full release row is a prefix row (lock held: `hb = true`). -/
theorem AxSpinRl4.rowRelPOfFull :
    RowRelease k c row pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint →
    RowReleaseP k c true row pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn
      pint :=
  fun H => ⟨rowShXPOfX H.1, fun _ => H.2.1, fun h => nomatch h⟩

/-- (Lean-only) the three spills' prefix window. -/
theorem AxSpinRl4.relPHead :
    RowReleaseP k c hb row pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint →
    RowShP k row (relHead pra ps0 ps1) := fun H =>
  (rowShXPMap _).1 (rowShXPAppL H.1)

/-- (Lean-only) holding's prefix window at `relKh k`, branch `hb`. -/
theorem AxSpinRl4.relPHolding :
    RowReleaseP k c hb row pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint →
    RowHoldingP (relKh k) row hb plk pcl hra hs0 hs1 hram hs0m := by
  intro H
  have H1 := (rowShXPMap _).1 (rowShXPAppL (rowShXPAppR H.1))
  exact AxSpinRl4.rowHoldingPOf _ _ hb _ _ _ _ _ _ _ (rowShPCongr H1 rfl) H.2.1

/-- (Lean-only) holding's lw is a memory event (when present). -/
theorem AxSpinRl4.relPLk :
    RowReleaseP k c hb row pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint →
    relKh k < row.length → ∃ l, row[relKh k]? = some l ∧ (lbIsR l || lbIsW l) = true := by
  intro H hk
  obtain ⟨lb, Hlb, aq, Hs⟩ := H.1 3 (.it (.RL plk 4)) (by cases c <;> rfl) hk
  exact ⟨lb, Hlb, AxSpinRl3.memOfRead lb aq plk 4 Hs⟩

/-- (Lean-only) the lk->cpu store item (when present). -/
theorem AxSpinRl4.relPCpu :
    RowReleaseP k c hb row pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint →
    relKc k < row.length →
    ∃ vw cls, row[relKc k]? = some (.LStore false pcl vw cls) ∧ vw.length = 8 := by
  intro H hk
  obtain ⟨lb, Hlb, vw, cls, rfl, Hl⟩ := H.1 15 (.it (.RS pcl 8)) (by cases c <;> rfl) hk
  exact ⟨vw, cls, Hlb, Hl⟩

/-- (Lean-only) the fence item (when present). -/
theorem AxSpinRl4.relPFence :
    RowReleaseP k c hb row pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint →
    relKf k < row.length → row[relKf k]? = some (.LFence true true false true) := by
  intro H hk
  obtain ⟨lb, Hlb, Hs⟩ := H.1 16 (.RB true true false true) (by cases c <;> rfl) hk
  rw [xshapeRB _ _ _ _ _ Hs] at Hlb
  exact Hlb

/-- (Lean-only) pop_off's prefix window at `relKp k`. -/
theorem AxSpinRl4.relPPop :
    RowReleaseP k c hb row pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint →
    RowShP (relKp k) row (ppSh c qra qs0 qmra qms0 pn pint) := by
  intro H
  have H1 := (rowShXPMap _).1 (rowShXPAppL (rowShXPAppR (rowShXPAppR (rowShXPAppR H.1))))
  exact rowShPCongr H1 (by
    simp only [List.length_map, List.length_cons, List.length_nil, List.length_append, relHead,
      holdShB, ↓reduceIte, mycLen, relKp])

/-- (Lean-only) `rowReleaseNowr` on a PREFIX: the spill `s`'s slot is not written between the
spill and its reload, once every position up to the reload is present. -/
theorem AxSpinRl4.relPNowr (s : Nat) (hs : s < 3) (pa : Int) (w : Nat) :
    RowReleaseP k c hb row pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn pint →
    relKr k c + s ≤ row.length →
    (∀ q ∈ ([(pra, 8), (ps0, 8), (ps1, 8)] : List (Int × Nat)).drop (s + 1), dj q.1 q.2 pa w) →
    (∀ q ∈ relWr plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn, dj q.1 q.2 pa w) →
    nowr row (k + s) (relKr k c + s) pa w := by
  intro H Hlen Hs Hd
  rw [show relKr k c + s = k + (18 + ppLen c + s) by simp only [relKr, relKp]; omega] at Hlen ⊢
  have HX : RowShX k row ((relSh c pra ps0 ps1 plk pcl hra hs0 hs1 hram hs0m qra qs0 qmra qms0 pn
      pint).take (18 + ppLen c + s)) := by
    intro j x Hj
    have hj : j < 18 + ppLen c + s := by
      have := (List.getElem?_eq_some_iff.1 Hj).1
      simp only [List.length_take] at this
      omega
    rw [List.getElem?_take, if_pos hj] at Hj
    exact H.1 j x Hj (by omega)
  refine rowShXNowr k row _ s _ pa w HX
    (by simp only [List.length_take, relShLen, relLen]; omega) ?_
  rw [List.take_take, Nat.min_self]
  simp only [relWr, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    at Hd
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12⟩ := Hd
  match s, hs with
  | 0, _ =>
    simp only [List.drop_succ_cons, List.drop_zero, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at Hs
    obtain ⟨e1, e2⟩ := Hs
    cases c <;>
    simp only [relSh, relHead, holdShB, mycSh, ppSh, ppHead, ppMid, ppTail, relTail, ppLen,
      ↓reduceIte, Bool.false_eq_true, List.map, List.cons_append, List.nil_append,
      Nat.reduceAdd, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, xitDisj, itDisj,
      true_and, and_true] <;>
    exact ⟨e1, e2, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12⟩
  | 1, _ =>
    simp only [List.drop_succ_cons, List.drop_zero, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq] at Hs
    cases c <;>
    simp only [relSh, relHead, holdShB, mycSh, ppSh, ppHead, ppMid, ppTail, relTail, ppLen,
      ↓reduceIte, Bool.false_eq_true, List.map, List.cons_append, List.nil_append,
      Nat.reduceAdd, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, xitDisj, itDisj,
      true_and, and_true] <;>
    exact ⟨Hs, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12⟩
  | 2, _ =>
    cases c <;>
    simp only [relSh, relHead, holdShB, mycSh, ppSh, ppHead, ppMid, ppTail, relTail, ppLen,
      ↓reduceIte, Bool.false_eq_true, List.map, List.cons_append, List.nil_append,
      Nat.reduceAdd, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, xitDisj, itDisj,
      true_and, and_true] <;>
    exact ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12⟩

end rowrelp

/-! ## The releasing store on a prefix row -/

section swrelp
open Iris.Std.PartialMap
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
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- (Lean-only, stage 2) `AxSpinRl3.XxSwRelRel` WITHOUT the full row: the three row facts it
read off `RowRelease` (holding's lw and the lk->cpu store are memory events, the fence item)
and the store's length bound are premises (a prefix row supplies them once `relKw kr` is
present).  Same anchors, same deposit. -/
theorem AxSpinRl4.xxSwRelRelP (kr : Nat)
    (s : Athread) (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12)
    (rs2 rs1 : BitVec 5) (va pa : BitVec 64) (kc ks : Nat) (vs : List (BitVec 8))
    (Ql Qc : IProp GF) :
    (∃ l, (AxOpsem.grow (gtAdGd GT) i)[relKh kr]? = some l ∧ (lbIsR l || lbIsW l) = true) →
    (∃ l, (AxOpsem.grow (gtAdGd GT) i)[relKc kr]? = some l ∧ (lbIsR l || lbIsW l) = true) →
    (AxOpsem.grow (gtAdGd GT) i)[relKf kr]? = some (.LFence true true false true) →
    relKw kr + 1 ≤ (AxOpsem.grow (gtAdGd GT) i).length →
    (AxOpsem.grow (gtAdGd GT) i)[relKw kr]? =
      some (.LStore false L.xlLk AxSpinX4.z4 .WCrel) →
    ks < kr → (∃ l, (AxOpsem.grow (gtAdGd GT) i)[ks]? = some l ∧ (lbIsR l || lbIsW l) = true) →
    (∀ (k' : Nat) (lb : Lbl) (rl : Bool) (n : Nat), relKc kr < k' →
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb →
      aidentWr (aident lb) = some (rl, L.xlLk, n) → k' = relKw kr) →
    RetX cpu rs (relKw kr) s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc (.STORE (imm, .Regidx rs2, .Regidx rs1, 4)) →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Store .Data) va 4 pa → hitW rs va → paZ pa = L.xlLk →
    gprVal rs rs2 = 0#64 →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      AxAnnot.annotOwn (i, relKh kr) iprop(locked nm.xnReg L.xlLk i (i, kc) ∗ Ql) -∗
      AxAnnot.annotOwn (i, relKc kr) iprop(Qc ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, relKc kr) vs) -∗
      AxAnnot.annotOwn (i, ks) (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, ks)) -∗
      (∀ (rs' : RegFile) (ib' : Ibch), ⌜GoodB T satp0 rs pc is_rvc none none rs'⌝ -∗
        ⌜graphData (gtAdGd GT) (i, relKw kr) = some AxSpinX4.z4⌝ -∗
        AxAnnot.annotOwn (i, relKw kr) (notheld nm.xnReg L.xlLk i) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', relKp kr⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro Hmh Hmc Hf Hlen Hst Hks Hksm Hone HRet Hc HPC Hhit Htx Hva Hda Hhv Hpa Hval
  let P1 : IProp GF := iprop(locked nm.xnReg L.xlLk i (i, kc) ∗ Ql)
  let P2 : IProp GF := iprop(Qc ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, relKc kr) vs)
  let P3 : IProp GF := RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, ks)
  let m : Mea GF := insert (insert ({[((i, ks) : Geid) := P3]} : Mea GF) (i, relKc kr) P2)
    (i, relKh kr) P1
  have Hn2 : get? ({[((i, ks) : Geid) := P3]} : Mea GF) (i, relKc kr) = none :=
    lookupSingletonNe (by simp only [relKc, ne_eq, Prod.mk.injEq, true_and]; omega)
  have Hn1 : get? (insert ({[((i, ks) : Geid) := P3]} : Mea GF) (i, relKc kr) P2)
      (i, relKh kr) = none := by
    rw [lookupInsertNe (by simp only [relKc, relKh, ne_eq, Prod.mk.injEq, true_and]; omega),
      lookupSingletonNe (by simp only [relKh, ne_eq, Prod.mk.injEq, true_and]; omega)]
  have Hdm : ∀ e, e ∈ (FiniteMap.dom_set m : GSet Geid) →
      e = (i, relKh kr) ∨ e = (i, relKc kr) ∨ e = (i, ks) := by
    intro e He
    simp only [m] at He
    rw [domInsert, domInsert, domSingleton] at He
    rcases elemOfUnion.1 He with H | H
    · exact Or.inl (elemOfSingleton.1 H)
    rcases elemOfUnion.1 H with H | H
    · exact Or.inr (Or.inl (elemOfSingleton.1 H))
    · exact Or.inr (Or.inr (elemOfSingleton.1 H))
  have Hin2 : ((i, relKc kr) : Geid) ∈ (FiniteMap.dom_set m : GSet Geid) := by
    simp only [m]
    rw [domInsert, domInsert]
    exact elemOfUnion.2 (Or.inr (elemOfUnion.2 (Or.inl (elemOfSingleton.2 rfl))))
  have Hin3 : ((i, ks) : Geid) ∈ (FiniteMap.dom_set m : GSet Geid) := by
    simp only [m]
    rw [domInsert, domInsert, domSingleton]
    exact elemOfUnion.2 (Or.inr (elemOfUnion.2 (Or.inr (elemOfSingleton.2 rfl))))
  have Hdom : ∀ e, e ∈ (FiniteMap.dom_set m : GSet Geid) → e.1 = i ∧ e.2 < relKf kr ∧
      ∃ l, (AxOpsem.grow (gtAdGd GT) i)[e.2]? = some l ∧ (lbIsR l || lbIsW l) = true := by
    intro e He
    rcases Hdm e He with rfl | rfl | rfl
    · exact ⟨rfl, by simp only [relKh, relKf]; omega, Hmh⟩
    · exact ⟨rfl, by simp only [relKc, relKf]; omega, Hmc⟩
    · exact ⟨rfl, by simp only [relKf]; omega, Hksm⟩
  have H := XxSwRel L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid s rs
    (relKw kr) pc is_rvc imm rs2 rs1 va pa (relKf kr) (i, kc) (i, relKc kr) (i, ks)
    (i, relKc kr) m .WCrel HRet Hc HPC Hhit Htx Hva Hda Hhv Hpa Hval
    (by simp only [relKf, relKw]; omega) Hf Hst Hdom Hin2 Hin3 Hin2 Hone Hlen
  rw [show relKw kr + 1 = relKp kr from rfl] at H
  iintro #Hil A1 A2 A3 C
  iapply H $$ Hil [A1 A2 A3] [] [C]
  · iapply (BigSepM.bigSepM_insert Hn1).2
    isplitl [A1]
    · iexact A1
    iapply (BigSepM.bigSepM_insert Hn2).2
    isplitl [A2]
    · iexact A2
    iapply BigSepM.bigSepM_singleton.2
    iexact A3
  · iintro Hb
    icases (BigSepM.bigSepM_insert Hn1).1 $$ Hb with ⟨⟨Hl, -⟩, Hb⟩
    icases (BigSepM.bigSepM_insert Hn2).1 $$ Hb with ⟨⟨-, Hv⟩, Hb⟩
    ihave Hn := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ Hb
    isplitl [Hl]
    · iexact Hl
    isplitl [Hv]
    · unfold RCpu
      iexists vs
      iexact Hv
    · iexact Hn
  · iintro %rs' %ib' %HGB %Hgd HO
    iapply C $$ %rs' %ib' %HGB %Hgd HO

end swrelp

/-! # 6. THE HEAD: the P-form and the stage-1 corollary -/

section relhead
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
variable (Htxm : mycpuText σi T) (Htxh : holdingText σi T) (Htxr : releaseText σi T)
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

set_option maxHeartbeats 6400000 in
include HL Hcons hmode hasid hppn Hfix Htxm Htxh Htxr HΨmid in
/-- (Lean-only, P1) THE GATE FORM of `wpdRelHead` on a PREFIX row: `wpdRelHeadP` with holding's
three reload pins (AllocPins2 `rhMy` / `rhRet` / `rhS1`) replaced IN THEIR SLOTS by
`AxSpinT2i.Gate`s (against mycpu's link holding + 0x1a, release's own `jal holding` link
release + 0x10, and release's s1 = a0) and handed to `AxSpinHdC.holdingFromReleaseG` (its long
continuation `KLongG` returns the three values past `relKh k + 12`); the `rlL` gate, the hook and
`KrlS` / `KrlL` exactly `wpdRelHeadP`'s.  Stage-2 description of the script follows.
(Lean-only, stage 2) THE P-FORM of `wpdRelHead` on a PREFIX row (`RowReleaseP k c hb …`;
holding's branch bit `hb` is the row's).  One `by_cases` per row position: the WINDOWED,
RESOURCE-FREE hook `HΨend` on `[k, relKw k]` EXCEPT release's two designated cuts — `rlS` at
`relKh k + 1` on `hb = false` (arm `KrlS`: holding's short-arm END continuation, with `OHeld`'s
lock-word deposit and the unused lk->cpu handle) and `rlL` at `relKh k + 12` (arm `KrlL`: the
long-arm END continuation with `OHeld`, `OOwn`'s readback and the five reload annotations, at
EVERY holding entry state `rs` with release's tp / a0).  Both arms also receive the nextpid
anchor.  Value pins guarded by position; the `rlL` gate (`lk->cpu` read = mycpu's address) only
for rows that continue past the cut. -/
theorem wpdRelHeadG (k : Nat) (c hb : Bool) (rs0 : RegFile) (ib0 : Ibch)
    (Pra Ps0 Ps1 Hra Hs0 Hs1 Hram Hs0m Pcl PclS Plk PlkS : BitVec 64)
    (plk qra qs0 qmra qms0 pn pint : Int)
    (kc kw ks : Nat) (val : BitVec 64) (cls : WmClass) (Qc Qw : IProp GF)
    (tsc : List Nat) (rvsc wvsc : List (BitVec 8)) (clsc : WmClass) :
    -- the row (prefix)
    RowReleaseP k c hb (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) (paZ Ps0) (paZ Ps1) plk (paZ Pcl)
      (paZ Hra) (paZ Hs0) (paZ Hs1) (paZ Hram) (paZ Hs0m) qra qs0 qmra qms0 pn pint →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hra) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hs0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hs1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hram) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hs0m) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pcl) →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = AxSpinHdB.prl 0 → hitW rs0 (AxSpinHdB.prl 0) →
    hitW rs0 (pcm 0) →
    -- release's three slots
    AxSpinPO1.slot8 σi T L i rs0 (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm24)
      Pra →
    AxSpinPO1.slot8 σi T L i rs0 (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm16)
      Ps0 →
    AxSpinPO1.slot8 σi T L i rs0 (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm8)
      Ps1 →
    -- holding's five slots (its frame `spo (spo sp)`, its mycpu's below)
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinHd8.imm24) Hra →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinHd8.imm16) Hs0 →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinHd8.imm8) Hs1 →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immRa)
      Hram →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immS0)
      Hs0m →
    slotsDisj [paZ Hra, paZ Hs0, paZ Hs1, paZ Hram, paZ Hs0m] →
    -- the lock (a0 = its address)
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) →
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) 4 Plk →
    ¬ L.xlText (paZ Plk) →
    dataAtS σi T (.Store .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) 4 PlkS →
    paZ PlkS = L.xlLk →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) 8 Pcl →
    paZ Pcl = L.xlLk + 16 → ¬ L.xlText (paZ Pcl) →
    dataAtS σi T (.Store .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) 8 PclS →
    paZ PclS = L.xlLk + 16 →
    -- acquire's claim and its lk->cpu store (the holder's facts; row items guarded)
    (relKh k < (AxOpsem.grow (gtAdGd GT) i).length →
      (AxOpsem.grow (gtAdGd GT) i)[kc]? = some (Lbl.LRmw true false L.xlLk tsc rvsc wvsc clsc)) →
    kc < relKh k → nolk L.xlLk (gtAdGd GT).gdG (i, kc) (i, relKh k) →
    (relKh k < (AxOpsem.grow (gtAdGd GT) i).length →
      (AxOpsem.grow (gtAdGd GT) i)[kw]? =
        some (Lbl.LStore false (L.xlLk + 16) (WeakInterpProj.wbytes 8 val) cls)) →
    kw < relKh k + 4 →
    (∀ w a v', a ∈ clb L → gwritesByte (gtAdGd GT).gdG w a v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG (i, kw) w →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (i, relKh k + 4) → False) →
    -- ROW PREMISES (AxSpinRl2 / AxSpinRl3; row items guarded)
    CpuWin L GT i (i, kw) → CpuWin L GT i (i, relKh k + 4) →
    (relKw k < (AxOpsem.grow (gtAdGd GT) i).length →
      (AxOpsem.grow (gtAdGd GT) i)[relKw k]? = some (.LStore false L.xlLk AxSpinX4.z4 .WCrel)) →
    (∀ (k' : Nat) (lb : Lbl) (rl : Bool) (n : Nat), relKc k < k' →
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb →
      aidentWr (aident lb) = some (rl, L.xlLk, n) → k' = relKw k) →
    -- the nextpid anchor (allocpid's store, before release)
    ks < k → (relKw k < (AxOpsem.grow (gtAdGd GT) i).length →
      ∃ l, (AxOpsem.grow (gtAdGd GT) i)[ks]? = some l ∧ (lbIsR l || lbIsW l) = true) →
    -- P1: holding's reload GATES (mycpu's ra, holding's ra = release's jal link)
    AxSpinT2i.Gate GT i (relKh k + 7) (stBytes 8 (pch 0x1a)) →
    AxSpinT2i.Gate GT i (relKh k + 9) (stBytes 8 (AxSpinHdB.prl 0x10)) →
    -- the rlL GATE (a row continuing past the cut took the normal arm)
    (relKh k + 12 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, relKh k + 4) =
        some (stBytes 8 (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4)))) →
    -- P1: holding's s1 reload GATE (release's s1 = the lock address a0)
    AxSpinT2i.Gate GT i (relKh k + 11) (stBytes 8 (gprVal rs0 AxSpinE8.r10)) →
    -- the row-end hook (windowed; NOT at the designated cuts)
    -- (P1 VALUE HOOK: holding's three gates, on its long arm)
    (∀ k' : Nat, k ≤ k' → k' ≤ relKw k → (hb = false → k' ≠ relKh k + 1) →
      k' ≠ relKh k + 12 → (AxOpsem.grow (gtAdGd GT) i).length ≤ k' →
      AxSpinE8.EndRl GT i (if hb then [(relKh k + 7, some (stBytes 8 (pch 0x1a))),
        (relKh k + 9, some (stBytes 8 (AxSpinHdB.prl 0x10))),
        (relKh k + 11, some (stBytes 8 (gprVal rs0 AxSpinE8.r10)))] else []) k' →
      ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    -- the designated cut rlS (hb = false: row ends right after holding's lw)
    (hb = false →
      ⊢ AxAnnot.annotOwn (i, ks) (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, ks)) -∗
        KShortEnd (hlc := hlc) L GT nm i Ψ (relKh k)
          (fun v => iprop(OHeld L GT nm i kc (relKh k) Qc (relKh k) v ∗ AxAnnot.annotOwn (i, kw)
            iprop(Qw ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, kw) (WeakInterpProj.wbytes 8 val))))) →
    -- the designated cut rlL (hb = true: row ends after holding's last reload)
    (hb = true → ∀ rs : RegFile, gprVal rs AxSpinE8.r4 = gprVal rs0 AxSpinE8.r4 →
      gprVal rs AxSpinE8.r10 = gprVal rs0 AxSpinE8.r10 →
      ⊢ AxAnnot.annotOwn (i, ks) (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, ks)) -∗
        KLongEnd (hlc := hlc) L GT nm i Ψ (relKh k) rs Hra Hs0 Hs1 Hram Hs0m
          (OHeld L GT nm i kc (relKh k) Qc (relKh k))
          (OOwn L GT nm i kw (relKh k + 4) val Qw (relKh k + 4))) →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      AxAnnot.annotOwn (i, kc) iprop(locked nm.xnReg L.xlLk i (i, kc) ∗ Qc) -∗
      AxAnnot.annotOwn (i, kw)
        iprop(Qw ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, kw) (WeakInterpProj.wbytes 8 val)) -∗
      AxAnnot.annotOwn (i, ks) (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, ks)) -∗
      (∀ (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = AxSpinHdB.prl 0x1e ∧ rs' .tlb = rs0 .tlb ∧
          gprVal rs' AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) ∧
          gprVal rs' AxSpinHd8.r9 = gprVal rs0 AxSpinE8.r10 ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
            r.toNat ≠ 10 → r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
          graphData (gtAdGd GT) (i, k) = some (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs0 AxSpinE8.r8)) ∧
          graphData (gtAdGd GT) (i, k + 2) = some (stBytes 8 (gprVal rs0 AxSpinHd8.r9))⌝ -∗
        AxAnnot.annotOwn (i, relKw k) (notheld nm.xnReg L.xlLk i) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', relKp k⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hw8 Hnr1 Hnr2 Hnr3 Hnr4 Hnr5 HnrCl Hc0 HPC0 Hhit0 HhitM
    ⟨HdaS_ra, _, Hh_ra, Hpr_ra, _⟩ ⟨HdaS_s0, _, Hh_s0, Hpr_s0, _⟩ ⟨HdaS_s1, _, Hh_s1, Hpr_s1, _⟩
    ⟨Hd1, Hd2, Hh1, Hp1, Hn1⟩ ⟨Hd4, Hd5, Hh2, Hp2, Hn2⟩ ⟨Hd7, Hd8, Hh3, Hp3, Hn3⟩
    ⟨Hd10, Hd11, Hh4, Hp4, Hn4⟩ ⟨Hd13, Hd14, Hh5, Hp5, Hn5⟩ Hdisj
    Hhlk Hhlc HdaLlk HntLk HdaSlk HpaLk HdaLcl HpaCl HntCl HdaScl HpaClS
    Hkc Hkck Hnl Hkw Hkwk Hnoint HwinW HwinR HrelZ4 HrelOnly Hks Hksm
    Hvm Hvr Hvcpu Hvs1 HΨend KrlS KrlL
  obtain ⟨T00, T02, T04, T06, T08, T0a, T0c, T10, T12, T16, T1a, -⟩ := Htxr
  have XR := XxReg L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XS := XxSt L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have Hpg : ∀ off : Int, WeakKpt.svpnOf (AxSpinHdB.prl off) = WeakKpt.svpnOf (AxSpinHdB.prl 0) →
      ∀ rs : RegFile, rs .tlb = rs0 .tlb → hitW rs (AxSpinHdB.prl off) :=
    fun off h rs ht => hitWSvpn rs _ _ h (hitWAgree rs0 rs _ ht Hhit0)
  iintro #Hil Hcl Hwl Hnp C
  -- row end at k
  by_cases E0 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k
  · iclear Hcl
    iclear Hwl
    iclear Hnp
    iclear C
    iapply (HΨend _ (Nat.le_refl _) (by simp only [relKw]; omega)
      (fun _ => by simp only [relKh]; omega) (by simp only [relKh]; omega) E0
        (by simp only [relKh, relKf, relKw]; ax_spin_e8_endrl) _)
  -- ---- + 0x00: c.addi sp,-32 (row position k) ----
  iapply (XR _ rs0 k (AxSpinHdB.prl 0x00) true q00 none
    (some (2#5, spo (gprVal rs0 AxSpinE8.r2)))
    (retxRefl cpu rs0 k ib0) Hc0 HPC0 (Hpg _ (by decide) rs0 rfl)
    (tw1101 σi T satp0 _ T00) (AxSpinE8.owOkSome 2#5 _ (by decide))
    (rfFOfRf0 _ (rf0Addi _ _ _))
    (certAddi _ rs0 (AxSpinHdB.prl 0x00) true 2#5 2#5 _ (by decide)) (by omega))
  iintro %rs1 %ib1 %HG1
  have HF1 := stepRegs T satp0 _ rs0 _ _ _ _ _ rs1 (fun _ => rfl) HG1
  have HPC1 : rs1 .PC = AxSpinHdB.prl 0x02 := by rw [gbPc T satp0 _ _ _ _ _ _ HG1]; decide
  have Htl1 : rs1 .tlb = rs0 .tlb := gbTlb T satp0 _ _ _ _ _ _ HG1
  have Esp1 : gprVal rs1 AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) := by
    rw [HF1]; ax_spin_rl4_zsimp
  -- ---- + 0x02: c.sdsp ra,24(sp) (spill at k) ----
  iapply (XS _ rs1 k (AxSpinHdB.prl 0x02) true AxSpinPO3.imm24 1#5 2#5
    (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm24) Pra
    (retxRefl cpu rs1 k ib1) (gbCtrl T satp0 _ _ _ _ _ _ HG1) HPC1 (Hpg _ (by decide) rs1 Htl1)
    (twEc06 σi T satp0 _ T02) (by rw [Esp1]) HdaS_ra
    (hitWAgree rs0 rs1 _ Htl1 Hh_ra) Hpr_ra Hw8 (by omega))
  iintro %rs2 %ib2 %HG2 %Hgd0
  have HF2 := stepRegs0 T satp0 _ rs1 _ _ _ rs2 HF1 HG2
  have HPC2 : rs2 .PC = AxSpinHdB.prl 0x04 := by rw [gbPc T satp0 _ _ _ _ _ _ HG2]; decide
  have Htl2 : rs2 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG2).trans Htl1
  have Esp2 : gprVal rs2 AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) := by
    rw [HF2]; ax_spin_rl4_zsimp
  -- row end at k + 1
  by_cases E1 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 1
  · iclear Hcl
    iclear Hwl
    iclear Hnp
    iclear C
    iapply (HΨend _ (by omega) (by simp only [relKw]; omega)
      (fun _ => by simp only [relKh]; omega) (by simp only [relKh]; omega) E1
        (by simp only [relKh, relKf, relKw]; ax_spin_e8_endrl) _)
  -- ---- + 0x04: c.sdsp s0,16(sp) (spill at k+1) ----
  iapply (XS _ rs2 (k + 1) (AxSpinHdB.prl 0x04) true AxSpinPO3.imm16 8#5 2#5
    (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm16) Ps0
    (retxRefl cpu rs2 (k + 1) ib2) (gbCtrl T satp0 _ _ _ _ _ _ HG2) HPC2
    (Hpg _ (by decide) rs2 Htl2)
    (twE822 σi T satp0 _ T04) (by rw [Esp2]) HdaS_s0
    (hitWAgree rs0 rs2 _ Htl2 Hh_s0) Hpr_s0 Hw8 (by omega))
  iintro %rs3 %ib3 %HG3 %Hgd1
  have HF3 := stepRegs0 T satp0 _ rs2 _ _ _ rs3 HF2 HG3
  have HPC3 : rs3 .PC = AxSpinHdB.prl 0x06 := by rw [gbPc T satp0 _ _ _ _ _ _ HG3]; decide
  have Htl3 : rs3 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG3).trans Htl2
  have Esp3 : gprVal rs3 AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) := by
    rw [HF3]; ax_spin_rl4_zsimp
  -- row end at k + 2
  by_cases E2 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 2
  · iclear Hcl
    iclear Hwl
    iclear Hnp
    iclear C
    iapply (HΨend _ (by omega) (by simp only [relKw]; omega)
      (fun _ => by simp only [relKh]; omega) (by simp only [relKh]; omega) E2
        (by simp only [relKh, relKf, relKw]; ax_spin_e8_endrl) _)
  -- ---- + 0x06: c.sdsp s1,8(sp) (spill at k+2) ----
  iapply (XS _ rs3 (k + 2) (AxSpinHdB.prl 0x06) true AxSpinPO3.imm8 9#5 2#5
    (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm8) Ps1
    (retxRefl cpu rs3 (k + 2) ib3) (gbCtrl T satp0 _ _ _ _ _ _ HG3) HPC3
    (Hpg _ (by decide) rs3 Htl3)
    (twE426 σi T satp0 _ T06) (by rw [Esp3]) HdaS_s1
    (hitWAgree rs0 rs3 _ Htl3 Hh_s1) Hpr_s1 Hw8 (by omega))
  iintro %rs4 %ib4 %HG4 %Hgd2
  have HF4 := stepRegs0 T satp0 _ rs3 _ _ _ rs4 HF3 HG4
  have HPC4 : rs4 .PC = AxSpinHdB.prl 0x08 := by rw [gbPc T satp0 _ _ _ _ _ _ HG4]; decide
  have Htl4 : rs4 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG4).trans Htl3
  -- row end at k + 3 = relKh k (before holding's lw)
  by_cases E3 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 3
  · iclear Hcl
    iclear Hwl
    iclear Hnp
    iclear C
    iapply (HΨend _ (by omega) (by simp only [relKw]; omega)
      (fun _ => by simp only [relKh]; omega) (by simp only [relKh]; omega) E3
        (by simp only [relKh, relKf, relKw]; ax_spin_e8_endrl) _)
  have Hlt3 : relKh k < (AxOpsem.grow (gtAdGd GT) i).length := by simp only [relKh]; omega
  -- ---- + 0x08: c.addi4spn s0,sp,32 (k+3) ----
  have Hc5 := certAddi (ctrlOkSW T satp0) rs4 (AxSpinHdB.prl 0x08) true 2#5 8#5
    (caddi4spnImm 8#8) (by decide)
  simp only [HF4] at Hc5
  ax_spin_rl4_zsimp at Hc5
  iapply (XR _ rs4 (k + 3) (AxSpinHdB.prl 0x08) true q08 _ _
    (retxRefl cpu rs4 (k + 3) ib4) (gbCtrl T satp0 _ _ _ _ _ _ HG4) HPC4
    (Hpg _ (by decide) rs4 Htl4)
    (tw1000 σi T satp0 _ T08) (AxSpinE8.owOkSome 8#5 _ (by decide))
    (rfFOfRf0 _ (rf0Addi _ _ _)) Hc5 (by omega))
  iintro %rs5 %ib5 %HG5
  have HF5 := stepRegs T satp0 _ rs4 _ _ _ _ _ rs5 HF4 HG5
  have HPC5 : rs5 .PC = AxSpinHdB.prl 0x0a := by rw [gbPc T satp0 _ _ _ _ _ _ HG5]; decide
  have Htl5 : rs5 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG5).trans Htl4
  -- ---- + 0x0a: c.mv s1,a0 (k+3) ----
  have Hc6 := certAdd (ctrlOkSW T satp0) rs5 (AxSpinHdB.prl 0x0a) true 10#5 0#5 9#5 (by decide)
  simp only [HF5] at Hc6
  ax_spin_rl4_zsimp at Hc6
  iapply (XR _ rs5 (k + 3) (AxSpinHdB.prl 0x0a) true a0a _ _
    (retxRefl cpu rs5 (k + 3) ib5) (gbCtrl T satp0 _ _ _ _ _ _ HG5) HPC5
    (Hpg _ (by decide) rs5 Htl5)
    (twa84aa σi T satp0 _ T0a) (AxSpinE8.owOkSome 9#5 _ (by decide))
    (rfFOfRf0 _ (rf0Add _ _ _)) Hc6 (by omega))
  iintro %rs6 %ib6 %HG6
  have HF6 := stepRegs T satp0 _ rs5 _ _ _ _ _ rs6 HF5 HG6
  have HPC6 : rs6 .PC = AxSpinHdB.prl 0x0c := by rw [gbPc T satp0 _ _ _ _ _ _ HG6]; decide
  have Htl6 : rs6 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG6).trans Htl5
  -- ---- + 0x0c: jal ra,holding (k+3) ----
  have Hcj : CertC (ctrlOkSW T satp0) rs6 (AxSpinHdB.prl 0x0c) false rl0c (some (pch 0))
      (some (1#5, BitVec.addInt (AxSpinHdB.prl 0x0c) (incr false))) := by
    have h := certJAL (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs6 (AxSpinHdB.prl 0x0c)
      false 2096902#21 1#5 (by decide)
    rw [AxSpinRl4.jalTgts.1] at h
    rw [show linkOw 1#5 (BitVec.addInt (AxSpinHdB.prl 0x0c) (incr false)) =
      some (1#5, BitVec.addInt (AxSpinHdB.prl 0x0c) (incr false)) by
        unfold linkOw; rw [if_neg (by decide)]] at h
    exact h
  iapply (XR _ rs6 (k + 3) (AxSpinHdB.prl 0x0c) false rl0c (some (pch 0))
    (some (1#5, BitVec.addInt (AxSpinHdB.prl 0x0c) (incr false)))
    (retxRefl cpu rs6 (k + 3) ib6) (gbCtrl T satp0 _ _ _ _ _ _ HG6) HPC6
    (Hpg _ (by decide) rs6 Htl6)
    (tw4R0c σi T satp0 _ T0c) (AxSpinE8.owOkSome 1#5 _ (by decide))
    (AxSpinPOx.rfFJal 2096902#21 (.Regidx 1#5)) Hcj (by omega))
  iintro %rs7 %ib7 %HG7
  have HF7 := stepRegs T satp0 _ rs6 _ _ _ _ _ rs7 HF6 HG7
  have HPC7 : rs7 .PC = pch 0 := gbPc T satp0 _ _ _ _ _ _ HG7
  have Htl7 : rs7 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG7).trans Htl6
  have Esp7 : gprVal rs7 AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) := by
    rw [HF7]; ax_spin_rl4_zsimp
  have Ea07 : gprVal rs7 AxSpinE8.r10 = gprVal rs0 AxSpinE8.r10 := by
    rw [HF7]; ax_spin_rl4_zsimp
  have Etp7 : gprVal rs7 AxSpinE8.r4 = gprVal rs0 AxSpinE8.r4 := by
    rw [HF7]; ax_spin_rl4_zsimp
  have Era7 : jalrTgt 0#12 (gprVal rs7 AxSpinE8.r1) = AxSpinHdB.prl 0x10 := by
    rw [HF7]; ax_spin_rl4_zsimp; decide
  have Era7' : gprVal rs7 AxSpinE8.r1 = AxSpinHdB.prl 0x10 := by
    rw [HF7]; ax_spin_rl4_zsimp; first | rfl | decide
  have Es17 : gprVal rs7 AxSpinHd8.r9 = gprVal rs0 AxSpinE8.r10 := by
    rw [HF7]; ax_spin_rl4_zsimp; exact BitVec.zero_add _
  have Ekeep7 : ∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
      gprVal rs7 r = gprVal rs0 r := by
    intro r Hr1 Hr2 Hr8 Hr9
    rw [HF7]
    by_cases E0 : r.toNat = 0
    · rw [AxSpinE8.updZero _ _ _ _ E0, AxSpinE8.gprValZero rs0 r E0]
    · have n1 : r ≠ 1#5 := fun h => Hr1 (by rw [h]; rfl)
      have n2 : r ≠ 2#5 := fun h => Hr2 (by rw [h]; rfl)
      have n8 : r ≠ 8#5 := fun h => Hr8 (by rw [h]; rfl)
      have n9 : r ≠ 9#5 := fun h => Hr9 (by rw [h]; rfl)
      simp (disch := assumption) only [AxSpinE8.updOther]
  have Ehs : AxSpinHd9.hsp1 rs7 = spo (spo (gprVal rs0 AxSpinE8.r2)) := by
    simp only [AxSpinHd9.hsp1, Esp7]; rfl
  -- ---- holding, at relKh k = k+3 (gate form, branch hb) ----
  have W := holdingFromReleaseG L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxh
    Ψ HΨmid (relKh k) rs7 ib7 hb plk Hra Hs0 Hs1 Hram Hs0m Pcl Plk kc kw val cls Qc Qw
    tsc rvsc wvsc clsc (AxSpinRl4.relPHolding HR) Hw8 Hnr1 Hnr2 Hnr3 Hnr4 Hnr5
    (gbCtrl T satp0 _ _ _ _ _ _ HG7) HPC7
    (hitWSvpn rs7 (pch 0) (AxSpinHdB.prl 0) (by decide) (hitWAgree rs0 rs7 _ Htl7 Hhit0))
    (hitWAgree rs0 rs7 _ Htl7 HhitM)
    (by rw [Ea07]; exact hitWAgree rs0 rs7 _ Htl7 Hhlk)
    (by rw [Ea07]; exact hitWAgree rs0 rs7 _ Htl7 Hhlc)
    (by rw [Ehs]; exact Hd1) (by rw [Ehs]; exact Hd2)
    (by rw [Ehs]; exact hitWAgree rs0 rs7 _ Htl7 Hh1)
    (by rw [Ehs]; exact Hd4) (by rw [Ehs]; exact Hd5)
    (by rw [Ehs]; exact hitWAgree rs0 rs7 _ Htl7 Hh2)
    (by rw [Ehs]; exact Hd7) (by rw [Ehs]; exact Hd8)
    (by rw [Ehs]; exact hitWAgree rs0 rs7 _ Htl7 Hh3)
    (by rw [Ehs]; exact Hd10) (by rw [Ehs]; exact Hd11)
    (by rw [Ehs]; exact hitWAgree rs0 rs7 _ Htl7 Hh4)
    (by rw [Ehs]; exact Hd13) (by rw [Ehs]; exact Hd14)
    (by rw [Ehs]; exact hitWAgree rs0 rs7 _ Htl7 Hh5)
    Hp1 Hn1 Hp2 Hn2 Hp3 Hn3 Hp4 Hn4 Hp5 Hn5 Hdisj
    (fun _ => ⟨Hvm, by rw [Era7']; exact Hvr, by rw [Es17]; exact Hvs1⟩)
    (by rw [Era7, Era7'])
    (by rw [Ea07]; exact HdaLcl) HpaCl HntCl HnrCl (Hkw Hlt3) Hkwk Hnoint
    (by rw [Ea07]; exact HdaLlk) HntLk (Hkc Hlt3) Hkck Hnl
    (fun k' h1 h2 h3 hv pr => HΨend k' (by simp only [relKh] at h1; omega)
      (by cases hb <;> simp only [↓reduceIte, Bool.false_eq_true, relKh] at h2 <;>
        simp only [relKw] <;> omega)
      (fun hf => by subst hf; simp only [↓reduceIte, Bool.false_eq_true] at h2; omega)
      (by cases hb <;> simp only [↓reduceIte, Bool.false_eq_true] at h2 <;> omega) h3
      (by rw [Era7', Es17] at hv; exact hv) pr)
  rw [show k + 3 = relKh k from rfl]
  cases hb with
  | false =>
    -- ===== the SHORT arm: the lock word read 0, the row ends at the cut rlS =====
    have Hl1 : (AxOpsem.grow (gtAdGd GT) i).length = relKh k + 1 := by
      have := HR.2.2 rfl; omega
    simp only [Bool.false_eq_true, ↓reduceIte] at W
    iapply W $$ Hcl Hwl
    iclear C
    isplit
    · -- holding's c.ret ran: the row is still at the cut (the gate ends it there)
      unfold KShort
      iintro %vlk %rs8 %ib8 %HK Ho
      obtain ⟨-, -, -, -, -, Hlvlk, Hgvlk, -⟩ := HK
      have K := KrlS rfl
      unfold KShortEnd at K
      iapply K $$ Hnp %vlk %(.PHart cpu (.pure ()) rs8 none ib8 : Pexv6) [] Ho
      ipureintro
      exact ⟨Hl1, Hlvlk, Hgvlk⟩
    · iapply (KrlS rfl) $$ Hnp
  | true =>
    -- ===== the LONG arm (the holder's path) =====
    simp only [↓reduceIte] at W
    unfold KLongG at W
    simp only [AxSpinRl4.oHeldAt, AxSpinRl4.oOwnAt] at W
    iapply W $$ Hcl Hwl
    isplit
    rotate_left
    · iclear C
      iapply (KrlL rfl rs7 Etp7 Ea07) $$ Hnp
    iintro %vlk %vcpu %vram %vs0m %vra %vs0 %vs1 %rs8 %ib8 %HKG %HK Hlk Hcpu A7 A8 A9 A10 A11
    obtain ⟨Hc8, HPC8, Htl8', Ea08, Esp8, Hlvlk, Hlcpu, Hlram, Hls0m, Hlra, Hls0, Hls1, -, -,
      Es18, Ekeep8, Hgvlk, Hgvcpu, Hgd1', Hgd2', Hgd3', Hgd5', Hgd6', Hgv7, Hgv8, Hgv9, Hgv10,
      Hgvs1⟩ := HK
    -- past the cut rlL (KLongG: the row continues, the three reloads read their spills)
    obtain ⟨Hlt12, -, -, Evs1g⟩ := HKG
    iclear A7
    iclear A8
    iclear A9
    iclear A10
    iclear A11
    icases Hlk with ⟨Hlk, -⟩
    icases Hcpu with ⟨⟨%e', %He', Hown⟩, -⟩
    have Htl8 : rs8 .tlb = rs0 .tlb := Htl8'.trans Htl7
    have Evcpu : vcpu = stBytes 8 (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4)) :=
      Option.some.inj (Hgvcpu.symm.trans (Hvcpu Hlt12))
    have Evs1 : vs1 = stBytes 8 (gprVal rs0 AxSpinE8.r10) := by rw [Evs1g, Es17]
    have Ea08' : gprVal rs8 AxSpinE8.r10 = 1#64 := by
      rw [Ea08, Evcpu, AxSpinE8.ldResStBytes8, Etp7]
      exact AxSpinRl4.hresSelf _
    have Es18' : gprVal rs8 AxSpinHd8.r9 = gprVal rs0 AxSpinE8.r10 := by
      rw [Es18, Evs1, AxSpinE8.ldResStBytes8]
    have Esp8' : gprVal rs8 AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) := Esp8.trans Esp7
    have HlenC : relKc k + 1 ≤ (AxOpsem.grow (gtAdGd GT) i).length := by
      simp only [relKc, relKh] at Hlt12 ⊢; omega
    rw [show relKh k + 12 = relKc k by unfold relKh relKc; omega]
    -- ---- + 0x10: c.beqz a0,panic — FALLS (a0 = 1 by the rlL gate) (relKc k) ----
    have Hcb : CertC (ctrlOkSW T satp0) rs8 (AxSpinHdB.prl 0x10) true rl10 none none := by
      have h := certBTYPE (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs8
        (AxSpinHdB.prl 0x10) true (sign_extend (m := 13) (14#8 +++ 0b0#1)) 0#5 10#5 .BEQ
        (by decide)
      have Ea : gval 10#5 rs8 = 1#64 := by
        unfold gval
        rw [if_neg (by decide)]
        exact Ea08'
      have Ez : gval 0#5 rs8 = zero_reg := by
        unfold gval
        rw [if_pos (by decide)]
      have Eot : brOt .BEQ 10#5 0#5 rs8
          (AxSpinHdB.prl 0x10 + sign_extend (m := 64) (sign_extend (m := 13) (14#8 +++ 0b0#1))) =
            none := by
        unfold brOt AxSymCtl2.bcond
        rw [Ea, Ez]
        rfl
      rw [Eot] at h
      exact h
    iapply (XR _ rs8 (relKc k) (AxSpinHdB.prl 0x10) true rl10 none none
      (retxRefl cpu rs8 (relKc k) ib8) Hc8 (HPC8.trans Era7') (Hpg _ (by decide) rs8 Htl8)
      (twrCd11 σi T satp0 _ T10) trivial (rfFBtype _ _ _ _) Hcb (by omega))
    iintro %rs9 %ib9 %HG9
    have HF9 := stepRegs0 T satp0 _ rs8 _ _ _ rs9 (fun _ => rfl) HG9
    have HPC9 : rs9 .PC = AxSpinHdB.prl 0x12 := by rw [gbPc T satp0 _ _ _ _ _ _ HG9]; decide
    have Htl9 : rs9 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG9).trans Htl8
    -- ---- + 0x12: sd zero,16(s1) — the owned lk->cpu store, value 0 (relKc k) ----
    have He1 : e'.1 = i := by rcases He' with rfl | rfl <;> rfl
    have Hwin : CpuWin L GT i e' := by
      rcases He' with rfl | rfl
      · exact HwinW
      · exact HwinR
    iapply (XxSdCpu L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
      _ rs9 (relKc k) (AxSpinHdB.prl 0x12) false 16#12 0#5 9#5
      (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) PclS 0#64 e'
      iprop(Qw ∗ RVL nm.xnH (gtAdGd GT) (clb L) e' (WeakInterpProj.wbytes 8 val)) Qw
      (retxRefl cpu rs9 (relKc k) ib9) (gbCtrl T satp0 _ _ _ _ _ _ HG9) HPC9
      (Hpg _ (by decide) rs9 Htl9) (tw4R12 σi T satp0 _ T12)
      (by rw [(HF9 9#5).trans Es18']) HdaScl (hitWAgree rs0 rs9 _ Htl9 Hhlc) HpaClS
      (AxSpinE8.gprValZero rs9 0#5 rfl) He1 Hwin ?_ HlenC) $$ Hown
    · iintro ⟨HQ, HV⟩
      isplitl [HQ]
      · iexact HQ
      · iexists (WeakInterpProj.wbytes 8 val)
        iexact HV
    iintro %rs10 %ib10 %HG10 %_ Hsd
    rw [show relKc k + 1 = relKf k from rfl]
    have HF10 := stepRegs0 T satp0 _ rs9 _ _ _ rs10 HF9 HG10
    have HPC10 : rs10 .PC = AxSpinHdB.prl 0x16 := by rw [gbPc T satp0 _ _ _ _ _ _ HG10]; decide
    have Htl10 : rs10 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG10).trans Htl9
    -- row end at relKf k
    by_cases Ef : (AxOpsem.grow (gtAdGd GT) i).length ≤ relKf k
    · iclear Hlk
      iclear Hsd
      iclear Hnp
      iclear C
      iapply (HΨend _ (by simp only [relKf]; omega) (by simp only [relKf, relKw]; omega)
        (fun h => nomatch h) (by simp only [relKf, relKh]; omega) Ef
        (by simp only [relKh, relKf, relKw]; ax_spin_e8_endrl) _)
    -- ---- + 0x16: fence rw,w (relKf k) ----
    iapply (XxFence L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
      _ rs10 (relKf k) (AxSpinHdB.prl 0x16) (retxRefl cpu rs10 (relKf k) ib10)
      (gbCtrl T satp0 _ _ _ _ _ _ HG10) HPC10 (Hpg _ (by decide) rs10 Htl10)
      (tw4R16 σi T satp0 _ T16) (by omega))
    iintro %rs11 %ib11 %HG11
    rw [show relKf k + 1 = relKw k from rfl]
    have HF11 := stepRegs0 T satp0 _ rs10 _ _ _ rs11 HF10 HG11
    have HPC11 : rs11 .PC = AxSpinHdB.prl 0x1a := by rw [gbPc T satp0 _ _ _ _ _ _ HG11]; decide
    have Htl11 : rs11 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG11).trans Htl10
    -- row end at relKw k
    by_cases Ew : (AxOpsem.grow (gtAdGd GT) i).length ≤ relKw k
    · iclear Hlk
      iclear Hsd
      iclear Hnp
      iclear C
      iapply (HΨend _ (by simp only [relKw]; omega) (Nat.le_refl _)
        (fun h => nomatch h) (by simp only [relKw, relKh]; omega) Ew
        (by simp only [relKh, relKf, relKw]; ax_spin_e8_endrl) _)
    have Hltw : relKw k < (AxOpsem.grow (gtAdGd GT) i).length := by omega
    -- ---- + 0x1a: sw zero,0(s1) — THE RELEASING STORE (relKw k) ----
    iapply (AxSpinRl4.xxSwRelRelP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
      k _ rs11 (AxSpinHdB.prl 0x1a) false 0#12 0#5 9#5
      (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) PlkS kc ks
      (WeakInterpProj.wbytes 8 0#64) Qc Qw
      (AxSpinRl4.relPLk HR Hlt3)
      (by
        obtain ⟨vw, cls', Hlb, -⟩ := AxSpinRl4.relPCpu HR (by simp only [relKc, relKw] at Hltw ⊢; omega)
        exact ⟨_, Hlb, rfl⟩)
      (AxSpinRl4.relPFence HR (by simp only [relKf, relKw] at Hltw ⊢; omega))
      (by omega) (HrelZ4 Hltw) Hks (Hksm Hltw) HrelOnly (retxRefl cpu rs11 (relKw k) ib11)
      (gbCtrl T satp0 _ _ _ _ _ _ HG11) HPC11 (Hpg _ (by decide) rs11 Htl11)
      (tw4R1a σi T satp0 _ T1a) (by rw [(HF11 9#5).trans Es18']) HdaSlk
      (hitWAgree rs0 rs11 _ Htl11 Hhlk) HpaLk (AxSpinE8.gprValZero rs11 0#5 rfl)) $$ Hil Hlk Hsd Hnp
    iintro %rs12 %ib12 %HG12 %_ Hnh
    have HF12 := stepRegs0 T satp0 _ rs11 _ _ _ rs12 HF11 HG12
    iapply C $$ %rs12 %ib12 [] Hnh
    ipureintro
    refine ⟨gbCtrl T satp0 _ _ _ _ _ _ HG12, ?_, (gbTlb T satp0 _ _ _ _ _ _ HG12).trans Htl11,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [gbPc T satp0 _ _ _ _ _ _ HG12]; decide
    · exact (HF12 2#5).trans Esp8'
    · exact (HF12 9#5).trans Es18'
    · intro r Hr1 Hr2 Hr8 Hr9 Hr10 Hr15
      exact (HF12 r).trans ((Ekeep8 r Hr1 Hr2 Hr8 Hr9 Hr10 Hr15).trans (Ekeep7 r Hr1 Hr2 Hr8 Hr9))
    · rw [Hgd0, HF1]; ax_spin_rl4_zsimp
    · rw [Hgd1, HF2]; ax_spin_rl4_zsimp
    · rw [Hgd2, HF3]; ax_spin_rl4_zsimp

set_option maxHeartbeats 1600000 in
include HL Hcons hmode hasid hppn Hfix Htxm Htxh Htxr HΨmid in
/-- (Lean-only, stage 2) THE P-FORM of `wpdRelHead` on a PREFIX row (`RowReleaseP k c hb …`;
holding's branch bit `hb` is the row's).  One `by_cases` per row position: the WINDOWED,
RESOURCE-FREE hook `HΨend` on `[k, relKw k]` EXCEPT release's two designated cuts — `rlS` at
`relKh k + 1` on `hb = false` (arm `KrlS`: holding's short-arm END continuation, with `OHeld`'s
lock-word deposit and the unused lk->cpu handle) and `rlL` at `relKh k + 12` (arm `KrlL`: the
long-arm END continuation with `OHeld`, `OOwn`'s readback and the five reload annotations, at
EVERY holding entry state `rs` with release's tp / a0).  Both arms also receive the nextpid
anchor.  Value pins guarded by position; the `rlL` gate (`lk->cpu` read = mycpu's address) only
for rows that continue past the cut.  P1: the corollary of `wpdRelHeadG` via
`AxSpinT2i.gateOfPinG` (statement unchanged). -/
theorem wpdRelHeadP (k : Nat) (c hb : Bool) (rs0 : RegFile) (ib0 : Ibch)
    (Pra Ps0 Ps1 Hra Hs0 Hs1 Hram Hs0m Pcl PclS Plk PlkS : BitVec 64)
    (plk qra qs0 qmra qms0 pn pint : Int)
    (kc kw ks : Nat) (val : BitVec 64) (cls : WmClass) (Qc Qw : IProp GF)
    (tsc : List Nat) (rvsc wvsc : List (BitVec 8)) (clsc : WmClass) :
    -- the row (prefix)
    RowReleaseP k c hb (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) (paZ Ps0) (paZ Ps1) plk (paZ Pcl)
      (paZ Hra) (paZ Hs0) (paZ Hs1) (paZ Hram) (paZ Hs0m) qra qs0 qmra qms0 pn pint →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hra) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hs0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hs1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hram) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hs0m) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pcl) →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = AxSpinHdB.prl 0 → hitW rs0 (AxSpinHdB.prl 0) →
    hitW rs0 (pcm 0) →
    -- release's three slots
    AxSpinPO1.slot8 σi T L i rs0 (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm24)
      Pra →
    AxSpinPO1.slot8 σi T L i rs0 (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm16)
      Ps0 →
    AxSpinPO1.slot8 σi T L i rs0 (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm8)
      Ps1 →
    -- holding's five slots (its frame `spo (spo sp)`, its mycpu's below)
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinHd8.imm24) Hra →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinHd8.imm16) Hs0 →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinHd8.imm8) Hs1 →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immRa)
      Hram →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immS0)
      Hs0m →
    slotsDisj [paZ Hra, paZ Hs0, paZ Hs1, paZ Hram, paZ Hs0m] →
    -- the lock (a0 = its address)
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) →
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) 4 Plk →
    ¬ L.xlText (paZ Plk) →
    dataAtS σi T (.Store .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) 4 PlkS →
    paZ PlkS = L.xlLk →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) 8 Pcl →
    paZ Pcl = L.xlLk + 16 → ¬ L.xlText (paZ Pcl) →
    dataAtS σi T (.Store .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) 8 PclS →
    paZ PclS = L.xlLk + 16 →
    -- acquire's claim and its lk->cpu store (the holder's facts; row items guarded)
    (relKh k < (AxOpsem.grow (gtAdGd GT) i).length →
      (AxOpsem.grow (gtAdGd GT) i)[kc]? = some (Lbl.LRmw true false L.xlLk tsc rvsc wvsc clsc)) →
    kc < relKh k → nolk L.xlLk (gtAdGd GT).gdG (i, kc) (i, relKh k) →
    (relKh k < (AxOpsem.grow (gtAdGd GT) i).length →
      (AxOpsem.grow (gtAdGd GT) i)[kw]? =
        some (Lbl.LStore false (L.xlLk + 16) (WeakInterpProj.wbytes 8 val) cls)) →
    kw < relKh k + 4 →
    (∀ w a v', a ∈ clb L → gwritesByte (gtAdGd GT).gdG w a v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG (i, kw) w →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (i, relKh k + 4) → False) →
    -- ROW PREMISES (AxSpinRl2 / AxSpinRl3; row items guarded)
    CpuWin L GT i (i, kw) → CpuWin L GT i (i, relKh k + 4) →
    (relKw k < (AxOpsem.grow (gtAdGd GT) i).length →
      (AxOpsem.grow (gtAdGd GT) i)[relKw k]? = some (.LStore false L.xlLk AxSpinX4.z4 .WCrel)) →
    (∀ (k' : Nat) (lb : Lbl) (rl : Bool) (n : Nat), relKc k < k' →
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb →
      aidentWr (aident lb) = some (rl, L.xlLk, n) → k' = relKw k) →
    -- the nextpid anchor (allocpid's store, before release)
    ks < k → (relKw k < (AxOpsem.grow (gtAdGd GT) i).length →
      ∃ l, (AxOpsem.grow (gtAdGd GT) i)[ks]? = some l ∧ (lbIsR l || lbIsW l) = true) →
    -- GRAPH-VALUE PINS (Q20' Option V), guarded by position
    (relKh k + 7 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, relKh k + 7) = some (stBytes 8 (pch 0x1a))) →
    (relKh k + 9 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, relKh k + 9) = some (stBytes 8 (AxSpinHdB.prl 0x10))) →
    -- the rlL GATE (a row continuing past the cut took the normal arm)
    (relKh k + 12 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, relKh k + 4) =
        some (stBytes 8 (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4)))) →
    (relKh k + 11 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, relKh k + 11) = some (stBytes 8 (gprVal rs0 AxSpinE8.r10))) →
    -- the row-end hook (windowed; NOT at the designated cuts)
    (∀ k' : Nat, k ≤ k' → k' ≤ relKw k → (hb = false → k' ≠ relKh k + 1) →
      k' ≠ relKh k + 12 → (AxOpsem.grow (gtAdGd GT) i).length ≤ k' → ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    -- the designated cut rlS (hb = false: row ends right after holding's lw)
    (hb = false →
      ⊢ AxAnnot.annotOwn (i, ks) (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, ks)) -∗
        KShortEnd (hlc := hlc) L GT nm i Ψ (relKh k)
          (fun v => iprop(OHeld L GT nm i kc (relKh k) Qc (relKh k) v ∗ AxAnnot.annotOwn (i, kw)
            iprop(Qw ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, kw) (WeakInterpProj.wbytes 8 val))))) →
    -- the designated cut rlL (hb = true: row ends after holding's last reload)
    (hb = true → ∀ rs : RegFile, gprVal rs AxSpinE8.r4 = gprVal rs0 AxSpinE8.r4 →
      gprVal rs AxSpinE8.r10 = gprVal rs0 AxSpinE8.r10 →
      ⊢ AxAnnot.annotOwn (i, ks) (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, ks)) -∗
        KLongEnd (hlc := hlc) L GT nm i Ψ (relKh k) rs Hra Hs0 Hs1 Hram Hs0m
          (OHeld L GT nm i kc (relKh k) Qc (relKh k))
          (OOwn L GT nm i kw (relKh k + 4) val Qw (relKh k + 4))) →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      AxAnnot.annotOwn (i, kc) iprop(locked nm.xnReg L.xlLk i (i, kc) ∗ Qc) -∗
      AxAnnot.annotOwn (i, kw)
        iprop(Qw ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, kw) (WeakInterpProj.wbytes 8 val)) -∗
      AxAnnot.annotOwn (i, ks) (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, ks)) -∗
      (∀ (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = AxSpinHdB.prl 0x1e ∧ rs' .tlb = rs0 .tlb ∧
          gprVal rs' AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) ∧
          gprVal rs' AxSpinHd8.r9 = gprVal rs0 AxSpinE8.r10 ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
            r.toNat ≠ 10 → r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
          graphData (gtAdGd GT) (i, k) = some (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs0 AxSpinE8.r8)) ∧
          graphData (gtAdGd GT) (i, k + 2) = some (stBytes 8 (gprVal rs0 AxSpinHd8.r9))⌝ -∗
        AxAnnot.annotOwn (i, relKw k) (notheld nm.xnReg L.xlLk i) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', relKp k⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hw8 Hnr1 Hnr2 Hnr3 Hnr4 Hnr5 HnrCl Hc0 HPC0 Hhit0 HhitM Bra Bs0 Bs1 Bh1 Bh2 Bh3 Bh4 Bh5
    Hdisj Hhlk Hhlc HdaLlk HntLk HdaSlk HpaLk HdaLcl HpaCl HntCl HdaScl HpaClS
    Hkc Hkck Hnl Hkw Hkwk Hnoint HwinW HwinR HrelZ4 HrelOnly Hks Hksm Hvm Hvr Hvcpu Hvs1 HΨend
    KrlS KrlL
  exact wpdRelHeadG L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxh Htxr Ψ
    HΨmid k c hb rs0 ib0 Pra Ps0 Ps1 Hra Hs0 Hs1 Hram Hs0m Pcl PclS Plk PlkS plk qra qs0 qmra
    qms0 pn pint kc kw ks val cls Qc Qw tsc rvsc wvsc clsc HR Hw8 Hnr1
    Hnr2 Hnr3 Hnr4 Hnr5 HnrCl Hc0 HPC0 Hhit0 HhitM Bra Bs0 Bs1 Bh1 Bh2 Bh3 Bh4 Bh5 Hdisj
    Hhlk Hhlc HdaLlk HntLk HdaSlk HpaLk HdaLcl HpaCl HntCl HdaScl HpaClS
    Hkc Hkck Hnl Hkw Hkwk Hnoint HwinW HwinR HrelZ4 HrelOnly Hks Hksm
    (AxSpinT2i.gateOfPinG Hvm) (AxSpinT2i.gateOfPinG Hvr) Hvcpu (AxSpinT2i.gateOfPinG Hvs1)
    (fun k' h1 h2 h3 h4 h5 _ => HΨend k' h1 h2 h3 h4 h5) KrlS KrlL


set_option maxHeartbeats 1600000 in
include HL Hcons hmode hasid hppn Hfix Htxm Htxh Htxr HΨmid in
/-- THE HEAD OF xv6's `release` (release + 0x00 … + 0x1a), positional: spills, `jal holding`
(the holder's path), the falling `c.beqz`, `sd zero,16(s1)`, `fence rw,w`, `sw zero,0(s1)`;
continues at `relKp k` (PC = release + 0x1e) with `(i, relKw k) ↦ₐ notheld i`.  Stage 2: the
full-row corollary of `wpdRelHeadP` (`hb = true`; the hook and both cut arms are vacuous under
`relKe k c < LEN`; the pins unguarded). -/
theorem wpdRelHead (k : Nat) (c : Bool) (rs0 : RegFile) (ib0 : Ibch)
    (Pra Ps0 Ps1 Hra Hs0 Hs1 Hram Hs0m Pcl PclS Plk PlkS : BitVec 64)
    (plk qra qs0 qmra qms0 pn pint : Int)
    (kc kw ks : Nat) (val : BitVec 64) (cls : WmClass) (Qc Qw : IProp GF)
    (tsc : List Nat) (rvsc wvsc : List (BitVec 8)) (clsc : WmClass) :
    -- the row
    RowRelease k c (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) (paZ Ps0) (paZ Ps1) plk (paZ Pcl)
      (paZ Hra) (paZ Hs0) (paZ Hs1) (paZ Hram) (paZ Hs0m) qra qs0 qmra qms0 pn pint →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hra) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hs0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hs1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hram) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Hs0m) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pcl) →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = AxSpinHdB.prl 0 → hitW rs0 (AxSpinHdB.prl 0) →
    hitW rs0 (pcm 0) →
    -- release's three slots
    AxSpinPO1.slot8 σi T L i rs0 (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm24)
      Pra →
    AxSpinPO1.slot8 σi T L i rs0 (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm16)
      Ps0 →
    AxSpinPO1.slot8 σi T L i rs0 (spo (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinPO3.imm8)
      Ps1 →
    -- holding's five slots (its frame `spo (spo sp)`, its mycpu's below)
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinHd8.imm24) Hra →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinHd8.imm16) Hs0 →
    AxSpinPO1.slot8 σi T L i rs0
      (spo (spo (gprVal rs0 AxSpinE8.r2)) + sign_extend (m := 64) AxSpinHd8.imm8) Hs1 →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immRa)
      Hram →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (spo (spo (gprVal rs0 AxSpinE8.r2))) + sign_extend (m := 64) AxSpinE8.immS0)
      Hs0m →
    slotsDisj [paZ Hra, paZ Hs0, paZ Hs1, paZ Hram, paZ Hs0m] →
    -- the lock (a0 = its address)
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) →
    hitW rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) 4 Plk →
    ¬ L.xlText (paZ Plk) →
    dataAtS σi T (.Store .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (0#12)) 4 PlkS →
    paZ PlkS = L.xlLk →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) 8 Pcl →
    paZ Pcl = L.xlLk + 16 → ¬ L.xlText (paZ Pcl) →
    dataAtS σi T (.Store .Data) (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) (16#12)) 8 PclS →
    paZ PclS = L.xlLk + 16 →
    -- acquire's claim and its lk->cpu store (the holder's facts)
    (AxOpsem.grow (gtAdGd GT) i)[kc]? = some (Lbl.LRmw true false L.xlLk tsc rvsc wvsc clsc) →
    kc < relKh k → nolk L.xlLk (gtAdGd GT).gdG (i, kc) (i, relKh k) →
    (AxOpsem.grow (gtAdGd GT) i)[kw]? =
      some (Lbl.LStore false (L.xlLk + 16) (WeakInterpProj.wbytes 8 val) cls) →
    kw < relKh k + 4 →
    (∀ w a v', a ∈ clb L → gwritesByte (gtAdGd GT).gdG w a v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG (i, kw) w →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (i, relKh k + 4) → False) →
    -- ROW PREMISES (AxSpinRl2 / AxSpinRl3; AxSpinT2a supplies them)
    CpuWin L GT i (i, kw) → CpuWin L GT i (i, relKh k + 4) →
    (AxOpsem.grow (gtAdGd GT) i)[relKw k]? = some (.LStore false L.xlLk AxSpinX4.z4 .WCrel) →
    (∀ (k' : Nat) (lb : Lbl) (rl : Bool) (n : Nat), relKc k < k' →
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb →
      aidentWr (aident lb) = some (rl, L.xlLk, n) → k' = relKw k) →
    -- the nextpid anchor (allocpid's store, before release)
    ks < k → (∃ l, (AxOpsem.grow (gtAdGd GT) i)[ks]? = some l ∧ (lbIsR l || lbIsW l) = true) →
    -- GRAPH-VALUE PINS (Q20' Option V)
    graphValue (gtAdGd GT) (i, relKh k + 7) = some (stBytes 8 (pch 0x1a)) →
    graphValue (gtAdGd GT) (i, relKh k + 9) = some (stBytes 8 (AxSpinHdB.prl 0x10)) →
    graphValue (gtAdGd GT) (i, relKh k + 4) =
      some (stBytes 8 (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4))) →
    graphValue (gtAdGd GT) (i, relKh k + 11) = some (stBytes 8 (gprVal rs0 AxSpinE8.r10)) →
    ⊢ isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI (gtAdGd GT)) -∗
      AxAnnot.annotOwn (i, kc) iprop(locked nm.xnReg L.xlLk i (i, kc) ∗ Qc) -∗
      AxAnnot.annotOwn (i, kw)
        iprop(Qw ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, kw) (WeakInterpProj.wbytes 8 val)) -∗
      AxAnnot.annotOwn (i, ks) (RNp L nm.xnH nm.xnM nm.xnI (gtAdGd GT) (i, ks)) -∗
      (∀ (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = AxSpinHdB.prl 0x1e ∧ rs' .tlb = rs0 .tlb ∧
          gprVal rs' AxSpinE8.r2 = spo (gprVal rs0 AxSpinE8.r2) ∧
          gprVal rs' AxSpinHd8.r9 = gprVal rs0 AxSpinE8.r10 ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
            r.toNat ≠ 10 → r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
          graphData (gtAdGd GT) (i, k) = some (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs0 AxSpinE8.r8)) ∧
          graphData (gtAdGd GT) (i, k + 2) = some (stBytes 8 (gprVal rs0 AxSpinHd8.r9))⌝ -∗
        AxAnnot.annotOwn (i, relKw k) (notheld nm.xnReg L.xlLk i) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', relKp k⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hw8 Hnr1 Hnr2 Hnr3 Hnr4 Hnr5 HnrCl Hc0 HPC0 Hhit0 HhitM Bra Bs0 Bs1 Bh1 Bh2 Bh3 Bh4 Bh5
    Hdisj Hhlk Hhlc HdaLlk HntLk HdaSlk HpaLk HdaLcl HpaCl HntCl HdaScl HpaClS
    Hkc Hkck Hnl Hkw Hkwk Hnoint HwinW HwinR HrelZ4 HrelOnly Hks Hksm Hvm Hvr Hvcpu Hvs1
  have Hlen := (rowReleaseLen HR).1
  simp only [relKe, relKr, relKp] at Hlen
  exact wpdRelHeadP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxh Htxr Ψ
    HΨmid k c true rs0 ib0 Pra Ps0 Ps1 Hra Hs0 Hs1 Hram Hs0m Pcl PclS Plk PlkS plk qra qs0 qmra
    qms0 pn pint kc kw ks val cls Qc Qw tsc rvsc wvsc clsc (AxSpinRl4.rowRelPOfFull HR) Hw8 Hnr1
    Hnr2 Hnr3 Hnr4 Hnr5 HnrCl Hc0 HPC0 Hhit0 HhitM Bra Bs0 Bs1 Bh1 Bh2 Bh3 Bh4 Bh5 Hdisj
    Hhlk Hhlc HdaLlk HntLk HdaSlk HpaLk HdaLcl HpaCl HntCl HdaScl HpaClS
    (fun _ => Hkc) Hkck Hnl (fun _ => Hkw) Hkwk Hnoint HwinW HwinR (fun _ => HrelZ4) HrelOnly
    Hks (fun _ => Hksm) (fun _ => Hvm) (fun _ => Hvr) (fun _ => Hvcpu) (fun _ => Hvs1)
    (fun _ _ h2 _ _ h5 _ => absurd h5 (by simp only [relKw] at h2; omega))
    (fun h => nomatch h)
    (fun _ _ _ _ => by
      iintro -
      unfold KLongEnd
      iintro %vlk %vcpu %vram %vs0m %vra %vs0 %vs1 %pr %Hp
      exact absurd Hp.1 (by simp only [relKh]; omega))

end relhead

end Weak
