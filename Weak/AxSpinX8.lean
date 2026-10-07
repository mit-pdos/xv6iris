/-
Weak: **Phase 1c, part 8 of the spinlock plan -- the CERTIFICATE GRAPHS of `AxSpinX7`** and their
consistency / ctrl-closure, decided by the shipped checkers (`catTConsistentBSound`,
`ctrlClosedBSound`; Rocq `vm_compute`) -- split out so the capstone file re-checks fast.

Rocq: `iris/AxSpinX8.v` @ xxvzwolszwmp.

The graphs:
  `AxSpinX8.spa` (19 memory events, NOT SC: B's stack reload and B's holder lk->cpu read are
    gmo-before the stores they read -- forwarded).  A claims genesis, writes lk->cpu := cpuAddr A,
    nextpid := 0+1, lk->cpu := 0, releases.  B: spill X; reload (gmo-BEFORE the spill:
    forwarded); noff := 1; reads noff; reads the text word (image 0); non-holder read of lk->cpu
    = cpuAddr A; claims A's release; HOLDER read of lk->cpu gmo-BEFORE its own
    `sd lk->cpu ← cpuAddr B` (forwarded); sd; reads nextpid = 1; writes 2; lk->cpu := 0;
    releases.
  `spaSc` (the same rows in program-interleaving order: every owned read in its gmo case).
  `AxSpinX8.spr` (THE RACE: A' writes cpuAddr A' to lk->cpu WITHOUT the lock, gmo-between B's
    `sd lk->cpu ← cpuAddr B` and B's holder read, which returns A''s value).

## Deviations from Rocq

1. `vm_compute` (`vmr`) ↦ `decide +kernel` (`notes/weak-port-iris-gaps.md` recipe).
2. VOCABULARY: `replicate` ↦ `List.replicate`; `tdep` triples `((e1, e2), DTctrl)` are Lean's
   right-nested `((e1, e2), DTctrl)` pairs; `a_row`/`b_row`/`r_row` ↦ `AxSpinX4.aRow`/`bRow`/`rRow`
   (same argument order).
3. O2 Stage C: none needed -- the Rocq rows already contain no fetch events (the text-word read
   `ld ropa` is a plain data load), so row positions, gmo lists and ctrl edges are Rocq's verbatim.

**Rocq → Lean name map.**  `xa_ctrl` `xaCtrl`, `xb_ctrl` `xbCtrl`, `spa_rowA` `spaRowA`,
`spa_rowB` `spaRowB`, `spa` `AxSpinX8.spa` (dup: AxSpinProt4), `spa_sc_rowB` `spaScRowB`,
`spa_sc` `spaSc`, `spr_rowB` `sprRowB`, `spr` `AxSpinX8.spr` (dup: AxSpinWit), `spa_cat_t`
`AxSpinX8.spaCatT` (dup), `spa_sc_cat_t` `spaScCatT`, `spr_cat_t` `AxSpinX8.sprCatT` (dup),
`spa_ctrl_closed` `AxSpinX8.spaCtrlClosed` (dup), `spa_sc_ctrl_closed` `spaScCtrlClosed`,
`spr_ctrl_closed` `AxSpinX8.sprCtrlClosed` (dup).

**Dropped:** none (Rocq 15 decls; Lean 15).
-/
import Weak.AxSpinX4

namespace Weak

open MachCSL
open Dtag

/-- Branch-feeding amoswaps control every po-later store (closed). -/
def xaCtrl : List Tdep :=
  [(((hA, 0), (hA, 1)), DTctrl), (((hA, 0), (hA, 3)), DTctrl),
   (((hA, 0), (hA, 4)), DTctrl), (((hA, 0), (hA, 6)), DTctrl)]
def xbCtrl : List Tdep :=
  [(((hB, 6), (hB, 7)), DTctrl), (((hB, 6), (hB, 9)), DTctrl),
   (((hB, 6), (hB, 11)), DTctrl), (((hB, 6), (hB, 13)), DTctrl)]

/-! (a) the positive graph -/

def spaRowA : List Lbl := AxSpinX4.aRow 0 [0, 0, 0, 0] zero32
def spaRowB : List Lbl :=
  AxSpinX4.bRow (List.replicate 8 3) (List.replicate 4 4) (List.replicate 8 0)
    (List.replicate 8 2) 7 (List.replicate 4 5) (List.replicate 8 9) Xv zero64 cpA cpB one32 one32
def AxSpinX8.spa : GdexecT :=
  mkgt [spaRowA, spaRowB]
    [(hA, 0), (hA, 1), (hB, 1), (hB, 0), (hB, 2), (hB, 3), (hB, 4),
     (hB, 5), (hA, 2), (hA, 3), (hA, 4), (hA, 6), (hB, 6), (hB, 10),
     (hB, 7), (hB, 8), (hB, 9), (hB, 11), (hB, 13)]
    (xaCtrl ++ xbCtrl)

/-- The same rows in SC (program-interleaving) order: every owned read in its gmo case. -/
def spaScRowB : List Lbl :=
  AxSpinX4.bRow (List.replicate 8 3) (List.replicate 4 4) (List.replicate 8 0)
    (List.replicate 8 2) 7 (List.replicate 4 5) (List.replicate 8 9) Xv zero64 cpA cpB one32 one32
def spaSc : GdexecT :=
  mkgt [spaRowA, spaScRowB]
    [(hA, 0), (hA, 1), (hB, 0), (hB, 1), (hB, 2), (hB, 3), (hB, 4),
     (hB, 5), (hA, 2), (hA, 3), (hA, 4), (hA, 6), (hB, 6), (hB, 7),
     (hB, 8), (hB, 9), (hB, 10), (hB, 11), (hB, 13)]
    (xaCtrl ++ xbCtrl)

/-! (b) THE RACE -/

def sprRowB : List Lbl :=
  AxSpinX4.bRow (List.replicate 8 1) (List.replicate 4 2) (List.replicate 8 0)
    (List.replicate 8 0) 0 (List.replicate 4 0) (List.replicate 8 5) Xv zero64 zero64 cpA one32
    zero32
def AxSpinX8.spr : GdexecT :=
  mkgt [AxSpinX4.rRow, sprRowB]
    [(hB, 0), (hB, 1), (hB, 2), (hB, 3), (hB, 4), (hB, 5), (hB, 6),
     (hB, 7), (hA, 0), (hB, 8), (hB, 9), (hB, 10), (hB, 11), (hB, 13)]
    xbCtrl

theorem AxSpinX8.spaCatT : rvwmoCatConsistentT AxSpinX8.spa :=
  catTConsistentBSound _ (by decide +kernel)
theorem spaScCatT : rvwmoCatConsistentT spaSc :=
  catTConsistentBSound _ (by decide +kernel)
theorem AxSpinX8.sprCatT : rvwmoCatConsistentT AxSpinX8.spr :=
  catTConsistentBSound _ (by decide +kernel)
theorem AxSpinX8.spaCtrlClosed : ctrlClosed AxSpinX8.spa :=
  ctrlClosedBSound _ AxSpinX8.spaCatT.1 (by decide +kernel)
theorem spaScCtrlClosed : ctrlClosed spaSc :=
  ctrlClosedBSound _ spaScCatT.1 (by decide +kernel)
theorem AxSpinX8.sprCtrlClosed : ctrlClosed AxSpinX8.spr :=
  ctrlClosedBSound _ AxSpinX8.sprCatT.1 (by decide +kernel)

end Weak
