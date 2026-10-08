/-
Weak: **THEOREM 2's VOCABULARY** — the definitions `allocpidOpen` (AxSpinT2b) is stated over:
the real layout `xlayXv6`, the row family `allocSeg`/`allocFull` of the inlined allocpid
(`allocproc + 0x38 .. + 0x9c`), `t2Complete`, `pidOf`, the Option V / Q18b value pins
`AllocPins`, the per-hart posts `t2Post`/`t2Phi`, the joint step `t2Joint` and the entry
condition `entryOk`.  Theorem 2 design (`notes/weak-lb-thm2-design.md`) §B, §D row `AxSpinT2a`.
NEW Lean file (no Rocq source: the Rocq development stopped before the capstone).

## What this file provides

§1 CONSTANTS AND POSITIONS.  `T2Prm` = the four control parameters of one hart's run (`b`:
   push_off's `noff == 0` arm; `hb`: holding's lock bit on acquire's call; `n`: failed spins;
   `c`: pop_off's `noff − 1 ≠ 0` arm).  Positions (row items; the segment's row STARTS with
   acquire's first spill — `allocproc + 0x38 .. + 0x40` (auipc/addi a0, jal acquire) emit no
   event under Stage C):
     0..2        acquire's spills (ra / s0 / s1)
     `t2KPo` = 3 push_off (`poSh b`, 17 / 22 items); its tail at `t2KPoT q` = 3 + 8 (+5)
     `t2KHd q` = `aqKp 0 b` holding (`holdShB hb`, 12 / 1)
     `t2KSp q` = `aqKh 0 b hb` the spins (`n + 1` RMWs); the claim at `t2KA q` = `aqKA 0 b hb n`
     `t2KMy q` = `aqKm 0 b hb n` acquire's mycpu, lk->cpu store at +4, reloads +5..+7
     `t2KBd q` = `t2KMy q + 8` THE nextpid READ (Ap7's `apBodySh`, 67 items: scan +1..+64,
                 nextpid write +65, `p->pid` write `t2KPid q` = +66)
     `t2KRl q` = `t2KBd q + 67` release (`relSh c`, Rl1); holding at `t2KRh q` = +3, pop_off at
                 `t2KPp q` = +18, the reloads at `t2KRr q` = `relKr _ c`
     `t2KT q`  = `relKe (t2KRl q) c` THE TERMINAL ITEM `sw a5,24(s1)` (`p->state = USED`,
                 allocproc + 0x9a); `t2Len q = t2KT q + 1` is the row length.
§2 THE ROW FAMILY.  `allocSeg q i S p : List Rxitem` (Rl1's extended shapes) composed by
   position from `aqHead`, `poSh`, `holdShB`, the `RM` spins, `aqTail`, `apBodySh`, `relSh`, the
   terminal `RS (p+24) 4`.  The stack slots are FIXED by the frame sizes (cross-checked against
   `Xv6/KernelImage.lean`; `S` = sp at allocproc + 0x38, the bottom of allocproc's 32-byte frame;
   VA = PA, kernel direct map):
     acquire / release (frame S−32): ra S−8, s0 S−16, s1 S−24;
     push_off / holding (frame S−64, called from acquire / release): ra S−40, s0 S−48, s1 S−56;
       their mycpu (frame S−80): ra S−72, s0 S−80;
     acquire's mycpu, pop_off (frame S−48): ra S−40, s0 S−48; pop_off's mycpu (frame S−64):
       ra S−56, s0 S−64;
     cpu fields noff / intena at `cpuZ i + 120 / + 124` (`cpus[i]`); `p` = the proc slot.
   `allocFull row q i S p` = `RowShX 0 row (allocSeg …)` ∧ `row.length = t2Len q` ∧ the two
   `lkBranch`es ∧ `spinVals` ∧ `RowAllocpidBody` (plain-read bits) ∧ `AxSpinAq1.spinRmw` (the
   spin items' exact labels, RMW class `WCexcl` — the honest class, `AxSpinRl1.rowClsHonest`;
   restated from `WCplain` 2026-10-08, AxSpinAmX) ∧ `t2CpuVals` (every lk->cpu write is a plain 8-byte store of
   `cvx i` or 0 — orchestrator ruling for AxSpinRl2's `CpuWin`; true on real rows, the data is
   fixed by the code) ∧ `t2RelVals` (release's lock-word store `sw zero,0(s1)` at
   `relKw (t2KRl q)` writes `z4` — AxSpinRl3's `Hst`, deviation 2 there).  NEITHER value condition
   follows from the shape: `RS`/`RSc` items pin address, width (and for `RSc` the class) but not
   the store data.  Projections:
   `allocAcquire` (AxSpinAqr's `RowAcquire 0 …`), `allocBody`, `allocRelease` (Rl1's
   `RowRelease`), `allocTerm`, `allocPush`/`allocTailSh`/`allocSpinSh` and the length facts;
   `allocSpinRmw`, `allocCpuVals`, `allocCpuWin` (AxSpinRl2's `CpuWin` from the family + the
   anchor's lob facts); whole-row facts `allocItem` (every row item matches a segment item), `allocW8` (`rowW8`),
   `allocNoRmwn` (the only RMWs are the 4-byte ones on `pid_lock`); `allocRelVals`, `allocRelZ4`
   (XxSwRelRel's `Hst`: `row[relKw (t2KRl q)]? = some (.LStore false zLk z4 .WCrel)`).
   AxSpinRl3's `Hone` window is DERIVED from the shape (§5 end): `allocRelWin` — after the claim
   `t2KA q` the only lock-word write is at `relKw (t2KRl q)`, given that hart `i`'s private
   ranges miss `pid_lock` (`AxSpinT2a.privNeLk` from `T2LayHyp`); `allocRelWinC` states it in
   XxSwRelRel's exact form (anchor `relKc (t2KRl q)`, `L.xlLk` with `hL`).
   `t2Complete GD i S p := ∃ q, allocFull (grow GD i) q i S p`; `pidOf GD i q` = the data of the
   `p->pid` store.
§3 `AllocPins GD i q` (Option V return / arm pins + the Q18b pins), one named field per pin,
   at the positions the leaves state them (PO4 `wpdPushOff`, HdC `holdingFromAcquire'`/
   `holdingFromRelease'`, E8 `wpdMycpu`, Ap9 `wpdAllocpidCs`, PO6 `wpdPopOff`); the return
   addresses' `jalrTgt` fixpoints `AxSpinT2a.jalrRets`; (added by AxSpinApA, 2026-10-08:
   the extra Option V pins the composed callees take — `poS1`, `hdS1`, `aqS1`, `rhCpu`, `rhS1`,
   `rlS1`; see AxSpinApA's header); `AxSpinT2a.mycpuRetHart` (`mycpu`'s
   result at `tp = hartId c` is `cpuAddr c`), `AxSpinT2a.hresZero`.
§4 POSTS.  `t2Post GD L nm i q s = ⌜¬ midState s⌝ -∗ ∃ w, ⌜pidOf = some (wbytes 4 w) ∧ a3 =
   sext32 w ∧ npSrc (read) (claim)⌝ ∗ FRAG nm w`; `t2Phi` (A, B: `t2Post`; else `True`) at
   `AxSpinX7.xv6GF`; `t2Concl`; `t2Joint : [∗list] [A,B,C] t2Phi ==∗ ⌜t2Concl⌝` by
   `issuedFragExcl` (`AxSpinT2a.fragNe`), the `¬ midState` of the final states as premises.
§5 LAYOUT.  `xlayXv6 A B C S p ptp`: lock `pid_lock`, `nextpid`, harts `[A,B,C]`; hart `j`'s
   PRIVATE bytes (Q-T2-4) = stack window `[S j − 80, S j)` ∪ `p j + 24 .. +27` (`p->state`) ∪
   `p j + 48 .. +51` (`p->pid`), struct-cpu bytes `cpus[j] + 120 .. +127`; read-only = kernel
   text `[_text, etext)` ∪ the PTE pages `ptp`; text = kernel text.  Everything else (other
   `proc[]` slots …) BLOCKED.  `T2LayHyp` (distinct harts < NCPU, distinct `proc[]` slots,
   disjoint stack windows inside `stack0`, PTE pages above `end`) ⇒ `xlayXv6Ok : xlayOk`;
   `AxSpinT2a.privIff` (priv by ranges); cid injectivity `t2CpuInj`.  NON-VACUITY:
   `xlayXv6Real` — `xlayOk` at the real `KernelSyms` (harts 0/1/2, `proc[0..2]`, stack tops
   `stack0 + 4096 (j+1)`).
§6 ENTRY.  `entryOk T satp0 i S p s`: `s` = hart `cpuOf i` at row position 0, pure program, in
   the S-mode / SIE = 0 regime `ctrlOkSW`, `PC = allocproc + 0x38`, `sp = S`, `s1 = p`,
   `tp = hartId (cpuOf i)`, WARM TLB on `t2Touch i S p` (the two text pages
   `[0x80000000, 0x80002000)`, nextpid, `pid_lock`, `cpus[i]`'s fields, the whole `proc[]`
   (scan), the stack window, `p`'s two fields).  Membership lemmas `t2TouchText`/`Scan`/`Np`/
   `Stk`.

HONESTY.  Everything here is a DEFINITION or row / layout arithmetic; nothing about values is
proved.  `allocFull` fixes A's / B's control flow and addresses on the normal path (the panic
arms of holding / pop_off, the nextpid wrap and the collision retry are not in the family);
`AllocPins` pins the return addresses, holding's and pop_off's arms and the Q18b normal-path
values (`≠ 1000`, no wrap, no collision) — the theorem built on them says nothing about a hart
whose control flow is diverted or whose nextpid read hits 1000 / a collision.  The pins concern
only A's / B's OWN control values and their nextpid READ (Q-T2-5); none constrains C.
`entryOk` is a scope restriction (HAD / warm TLB, design §A.5); with a 64-entry direct-mapped TLB
the touched pages must hash apart — true for the real layout (pages 0x80000/1, 0x8000a..0x80012,
0x80012..0x80018), checked by the certificate (T2c), not here.

## Deviations from the design
1. The terminal store is `sw a5,24(s1)` at allocproc + 0x9a (0x80001c0c, `c.sw` 0xcc9c), after
   `li a5,1` at + 0x98 (the design says "+0x98's sw"); the hart's run ends after + 0x9a.
2. `complete` is named `t2Complete` (`complete` exists in other namespaces); the pins are a
   `structure AllocPins` (named fields) rather than a conjunction `allocPins`.
3. `allocSeg`'s address parameters are not free: they are computed from `S` (allocproc's frame),
   `cpuZ i` and `p` (the slots the real frames give); `pidOf` takes the hart's `T2Prm` (the
   `p->pid` position depends on `b hb n`).
4. `xlayXv6` takes per-hart `S p : Agent → Int` and gives C private bytes too (C may be the same
   segment, certificate (a′)); `xlCpuf j` covers the whole 8 bytes `noff`/`intena`.
5. `holding`'s arm pins are stated semantically (`lk->cpu ≠ / = cpuAddr (cpuOf i)`); the bridge
   to `hres` is `AxSpinT2a.hresZero` + `AxSpinT2a.mycpuRetHart`.

**Imports / reused:** `AxSpinAq1.spinRmw` (AxSpinAq1), `CpuWin` (AxSpinRl2) — both merged in
the tip, copied into this slot for building only (orchestrator note).  `Rxitem`/`RowShX`/`rowShXAppL/AppR`/`rowShXMap`/`rowSpinOfX`/`holdShB`/`rowHoldingOf`/
`relSh`/`RowRelease`/`relK*` (AxSpinRl1), `aqHead`/`aqTail`/`RowAcquire`/`spinVals`/`aqK*`
(AxSpinAqr), `poSh` (AxSpinPO4), `apBodySh`/`RowAllocpidBody` (AxSpinAp7), `pca` (AxSpinAp),
`vaNp`/`AxSpinAp9.scanVa` (AxSpinAp9), `Xlay`/`xlayOk`/`priv`/`cpuOf`/`cpuOfNat` (AxSpinX),
`FRAG`/`npSrc` (AxSpinU), `issuedFragExcl` (AxSpinX2), `AxSpinJ2.bigSepLTriple`,
`AxSpinX7.xv6GF`, `midState` (AxSymEngine3), `ctrlOkSW` (AxDataX4), `hitW` (AxSpinE),
`cpuAddr_inj`/`cpuAddr_toNat` (MachCSL).  All new short names grepped absent from the tree;
Lean-only helpers are `AxSpinT2a.*`.
-/
import Weak.AxSpinRl2
import Weak.AxSpinAq1
import Weak.AxSpinAp9
import Weak.AxSpinJ2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. Constants and positions -/

/-- `&pid_lock` (0x80012500). -/
abbrev AxSpinT2a.zLk : Int := (KernelSyms.«pid_lock» : Int)
/-- `&nextpid` (0x8000a384). -/
abbrev AxSpinT2a.zNp : Int := (KernelSyms.«nextpid» : Int)

/-- `&cpus[cpuOf i]` as an integer. -/
def cpuZ (i : Agent) : Int := (KernelSyms.«cpus» : Int) + 128 * ((cpuOf i).val : Int)

theorem AxSpinT2a.cpuZAddr (i : Agent) : ((cpuAddr (cpuOf i)).toNat : Int) = cpuZ i := by
  rw [cpuAddr_toNat]
  have h : (KernelGeom.cpusBase).toNat = KernelSyms.«cpus» := by decide
  rw [h]
  unfold cpuZ
  push_cast
  rfl

/-- One hart's control parameters. -/
structure T2Prm where
  /-- push_off's arm (`noff == 0`: the intena store) -/
  b : Bool
  /-- holding's lock bit on acquire's call -/
  hb : Bool
  /-- failed spins -/
  n : Nat
  /-- pop_off's arm (`noff − 1 ≠ 0`: no intena check) -/
  c : Bool

/-- push_off's first event. -/
def t2KPo : Nat := 3
/-- push_off's tail (`tk` of `wpdPushOff`). -/
def t2KPoT (q : T2Prm) : Nat := t2KPo + 8 + (if q.b then 5 else 0)
/-- holding's first event (acquire's call). -/
def t2KHd (q : T2Prm) : Nat := aqKp 0 q.b
/-- the first spin. -/
def t2KSp (q : T2Prm) : Nat := aqKh 0 q.b q.hb
/-- the claim (the successful amoswap). -/
def t2KA (q : T2Prm) : Nat := aqKA 0 q.b q.hb q.n
/-- acquire's mycpu window. -/
def t2KMy (q : T2Prm) : Nat := aqKm 0 q.b q.hb q.n
/-- THE nextpid READ (the critical-section body's first event). -/
def t2KBd (q : T2Prm) : Nat := t2KMy q + 8
/-- the `p->pid` store. -/
def t2KPid (q : T2Prm) : Nat := t2KBd q + 66
/-- release's first event. -/
def t2KRl (q : T2Prm) : Nat := t2KBd q + 67
/-- holding's first event (release's call). -/
def t2KRh (q : T2Prm) : Nat := relKh (t2KRl q)
/-- pop_off's first event. -/
def t2KPp (q : T2Prm) : Nat := relKp (t2KRl q)
/-- release's reloads. -/
def t2KRr (q : T2Prm) : Nat := relKr (t2KRl q) q.c
/-- THE TERMINAL ITEM `sw a5,24(s1)`. -/
def t2KT (q : T2Prm) : Nat := relKe (t2KRl q) q.c
/-- the row length. -/
def t2Len (q : T2Prm) : Nat := t2KT q + 1

theorem AxSpinT2a.kHdEq (q : T2Prm) : t2KHd q = 20 + (if q.b then 5 else 0) := by
  unfold t2KHd aqKp; omega

theorem AxSpinT2a.kAEq (q : T2Prm) : t2KA q + 1 = t2KMy q := by
  simp only [t2KA, t2KMy, aqKA, aqKm]; omega

theorem AxSpinT2a.kSpA (q : T2Prm) : t2KA q = t2KSp q + q.n := rfl

theorem AxSpinT2a.kAlt (q : T2Prm) : t2KA q < t2KBd q := by
  simp only [t2KA, t2KBd, t2KMy, aqKA, aqKm]; omega

theorem AxSpinT2a.kTEq (q : T2Prm) : t2KT q = t2KRl q + relLen q.c := relKeEq _ _

theorem AxSpinT2a.kRrEq (q : T2Prm) : t2KRr q + 3 = t2KT q := rfl

theorem AxSpinT2a.kPpEq (q : T2Prm) : t2KPp q = t2KRl q + 18 := rfl

theorem AxSpinT2a.kRhEq (q : T2Prm) : t2KRh q = t2KRl q + 3 := rfl

theorem AxSpinT2a.kBdLen (q : T2Prm) : t2KBd q + 67 < t2Len q := by
  simp only [t2Len, t2KT, relKe, relKr, relKp, t2KRl]; omega

theorem AxSpinT2a.kTLen (q : T2Prm) : t2KT q < t2Len q := by
  simp only [t2Len]; omega

/-! # 2. The row family -/

theorem AxSpinT2a.aqHeadLen (a b c : Int) : (aqHead a b c).length = 3 := rfl

theorem AxSpinT2a.poShLen (b : Bool) (pra ps0 ps1 pmra pms0 pn pint : Int) :
    (poSh b pra ps0 ps1 pmra pms0 pn pint).length = 17 + (if b then 5 else 0) := by
  cases b <;> rfl

/-- THE SEGMENT: allocproc + 0x38 .. + 0x9a of hart `i` with frame base `S` and proc slot `p`. -/
def allocSeg (q : T2Prm) (i : Agent) (S p : Int) : List Rxitem :=
  (aqHead (S - 8) (S - 16) (S - 24)).map .it ++
  ((poSh q.b (S - 40) (S - 48) (S - 56) (S - 72) (S - 80) (cpuZ i + 120) (cpuZ i + 124)).map .it ++
  ((holdShB q.hb AxSpinT2a.zLk (AxSpinT2a.zLk + 16) (S - 40) (S - 48) (S - 56) (S - 72)
      (S - 80)).map .it ++
  (List.replicate (q.n + 1) (Rxitem.RM true false AxSpinT2a.zLk 4) ++
  ((aqTail (S - 40) (S - 48) (AxSpinT2a.zLk + 16) (S - 8) (S - 16) (S - 24)).map .it ++
  ((apBodySh AxSpinT2a.zNp (p + 48)).map .it ++
  (relSh q.c (S - 8) (S - 16) (S - 24) AxSpinT2a.zLk (AxSpinT2a.zLk + 16) (S - 40) (S - 48)
      (S - 56) (S - 72) (S - 80) (S - 40) (S - 48) (S - 56) (S - 64) (cpuZ i + 120)
      (cpuZ i + 124) ++
  [Rxitem.it (.RS (p + 24) 4)]))))))

theorem allocSegLen (q : T2Prm) (i : Agent) (S p : Int) :
    (allocSeg q i S p).length = t2Len q := by
  simp only [allocSeg, List.length_append, List.length_map, AxSpinT2a.aqHeadLen,
    AxSpinT2a.poShLen, holdShBLen, List.length_replicate, aqTailLen, AxSpinAp7.apBodyShLen,
    relShLen, List.length_cons, List.length_nil, t2Len, t2KT, relKe, relKr, relKp, relLen,
    t2KRl, t2KBd, t2KMy, aqKm, aqKh, aqKp, holdLen]
  omega

/-- The lk->cpu ROW VALUE CONDITION (orchestrator ruling for AxSpinRl2's `CpuWin`): every write
of the row to `lk->cpu` is a plain 8-byte store of `cvx i` (acquire's `c.sd a0,16(s1)`) or of 0
(release's `sd zero,16(s1)`). -/
def t2CpuVals (row : List Lbl) (i : Agent) : Prop :=
  ∀ (k : Nat) (lb : Lbl) (rl : Bool) (m : Nat), row[k]? = some lb →
    aidentWr (aident lb) = some (rl, AxSpinT2a.zLk + 16, m) →
    ∃ vw cls, lb = .LStore false (AxSpinT2a.zLk + 16) vw cls ∧
      (vw = cvx i ∨ vw = List.replicate 8 b0)

/-- The RELEASING-STORE ROW VALUE CONDITION (AxSpinRl3's `Hst`, deviation 2 there): release's
`sw zero,0(s1)` at `relKw (t2KRl q)` writes `z4`.  NOT a consequence of the shape — the shape item
`RSc zLk 4 .WCrel` pins the address, width and class but not the data; true on real rows (the
store writes `x0`; the positional bridge itself demands `graphData = stBytes 4 0 = z4`). -/
def t2RelVals (row : List Lbl) (q : T2Prm) : Prop :=
  ∀ vw cls, row[relKw (t2KRl q)]? = some (.LStore false AxSpinT2a.zLk vw cls) → vw = AxSpinX4.z4

/-- THE ROW FAMILY (one hart): the shape, the exact length, holding's lock bits on both calls,
the spin values and labels (`AxSpinAq1.spinRmw`), the body's plain reads, the lk->cpu store
values, the releasing store's value. -/
def allocFull (row : List Lbl) (q : T2Prm) (i : Agent) (S p : Int) : Prop :=
  RowShX 0 row (allocSeg q i S p) ∧ row.length = t2Len q ∧
  lkBranch row (t2KHd q) q.hb ∧ spinVals row (t2KSp q) q.n ∧
  lkBranch row (t2KRh q) true ∧
  RowAllocpidBody (t2KBd q) row AxSpinT2a.zNp (p + 48) ∧
  AxSpinAq1.spinRmw row (t2KSp q) q.n AxSpinT2a.zLk ∧ t2CpuVals row i ∧ t2RelVals row q

/-- Design `complete i`: hart `i`'s row is in the family. -/
def t2Complete (GD : Gdexec) (i : Agent) (S p : Int) : Prop :=
  ∃ q, allocFull (AxOpsem.grow GD i) q i S p

/-- The data of hart `i`'s `p->pid` store. -/
def pidOf (GD : Gdexec) (i : Agent) (q : T2Prm) : Option (List (BitVec 8)) :=
  graphData GD (i, t2KPid q)

theorem AxSpinT2a.rowShXCongr {k k' : Nat} {row : List Lbl} {sh : List Rxitem} :
    RowShX k row sh → k = k' → RowShX k' row sh := fun H e => e ▸ H

section parts
variable {row : List Lbl} {q : T2Prm} {i : Agent} {S p : Int}

/-- The segment's pieces at their positions. -/
theorem AxSpinT2a.segParts (H : RowShX 0 row (allocSeg q i S p)) :
    RowSh 0 row (aqHead (S - 8) (S - 16) (S - 24)) ∧
    RowSh t2KPo row (poSh q.b (S - 40) (S - 48) (S - 56) (S - 72) (S - 80) (cpuZ i + 120)
      (cpuZ i + 124)) ∧
    RowSh (t2KHd q) row (holdShB q.hb AxSpinT2a.zLk (AxSpinT2a.zLk + 16) (S - 40) (S - 48)
      (S - 56) (S - 72) (S - 80)) ∧
    RowShX (t2KSp q) row (List.replicate (q.n + 1) (Rxitem.RM true false AxSpinT2a.zLk 4)) ∧
    RowSh (t2KMy q) row (aqTail (S - 40) (S - 48) (AxSpinT2a.zLk + 16) (S - 8) (S - 16) (S - 24)) ∧
    RowSh (t2KBd q) row (apBodySh AxSpinT2a.zNp (p + 48)) ∧
    RowShX (t2KRl q) row (relSh q.c (S - 8) (S - 16) (S - 24) AxSpinT2a.zLk (AxSpinT2a.zLk + 16)
      (S - 40) (S - 48) (S - 56) (S - 72) (S - 80) (S - 40) (S - 48) (S - 56) (S - 64)
      (cpuZ i + 120) (cpuZ i + 124)) ∧
    RowShX (t2KT q) row [Rxitem.it (.RS (p + 24) 4)] := by
  unfold allocSeg at H
  have R1 := rowShXAppR _ _ _ _ H
  have R2 := rowShXAppR _ _ _ _ R1
  have R3 := rowShXAppR _ _ _ _ R2
  have R4 := rowShXAppR _ _ _ _ R3
  have R5 := rowShXAppR _ _ _ _ R4
  have R6 := rowShXAppR _ _ _ _ R5
  have R7 := rowShXAppR _ _ _ _ R6
  simp only [List.length_map, AxSpinT2a.aqHeadLen, AxSpinT2a.poShLen, holdShBLen,
    List.length_replicate, aqTailLen, AxSpinAp7.apBodyShLen, relShLen] at R1 R2 R3 R4 R5 R6 R7
  refine ⟨(rowShXMap _ _ _).1 (rowShXAppL _ _ _ _ H), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (rowShXMap _ _ _).1 (rowShXAppL _ _ _ _ R1)
  · refine (rowShXMap _ _ _).1 (AxSpinT2a.rowShXCongr (rowShXAppL _ _ _ _ R2) ?_)
    simp only [t2KHd, aqKp]; omega
  · refine AxSpinT2a.rowShXCongr (rowShXAppL _ _ _ _ R3) ?_
    simp only [t2KSp, aqKh, aqKp, holdLen]; omega
  · refine (rowShXMap _ _ _).1 (AxSpinT2a.rowShXCongr (rowShXAppL _ _ _ _ R4) ?_)
    simp only [t2KMy, aqKm, aqKh, aqKp, holdLen]; omega
  · refine (rowShXMap _ _ _).1 (AxSpinT2a.rowShXCongr (rowShXAppL _ _ _ _ R5) ?_)
    simp only [t2KBd, t2KMy, aqKm, aqKh, aqKp, holdLen]; omega
  · refine AxSpinT2a.rowShXCongr (rowShXAppL _ _ _ _ R6) ?_
    simp only [t2KRl, t2KBd, t2KMy, aqKm, aqKh, aqKp, holdLen]; omega
  · refine AxSpinT2a.rowShXCongr R7 ?_
    simp only [t2KT, relKe, relKr, relKp, relLen, t2KRl, t2KBd, t2KMy, aqKm, aqKh, aqKp,
      holdLen]
    omega

variable (HF : allocFull row q i S p)
include HF

theorem allocPush :
    RowSh t2KPo row (poSh q.b (S - 40) (S - 48) (S - 56) (S - 72) (S - 80) (cpuZ i + 120)
      (cpuZ i + 124)) := (AxSpinT2a.segParts HF.1).2.1

theorem allocSpinSh : RowSpin (t2KSp q) q.n row AxSpinT2a.zLk :=
  rowSpinOfX _ _ _ _ (AxSpinT2a.segParts HF.1).2.2.2.1

theorem allocTailSh :
    RowSh (t2KMy q) row (aqTail (S - 40) (S - 48) (AxSpinT2a.zLk + 16) (S - 8) (S - 16) (S - 24)) :=
  (AxSpinT2a.segParts HF.1).2.2.2.2.1

/-- acquire's row (AxSpinAqr) at position 0. -/
theorem allocAcquire :
    RowAcquire 0 q.b q.hb q.n row (S - 8) (S - 16) (S - 24) (S - 40) (S - 48) (S - 56) (S - 72)
      (S - 80) (cpuZ i + 120) (cpuZ i + 124) (S - 40) (S - 48) (S - 56) (S - 72) (S - 80)
      AxSpinT2a.zLk (AxSpinT2a.zLk + 16) (S - 40) (S - 48) := by
  obtain ⟨H0, H1, H2, H3, H4, -, -, -⟩ := AxSpinT2a.segParts HF.1
  have Hl := HF.2.1
  have Hlt := AxSpinT2a.kBdLen q
  refine ⟨H0, H1, rowHoldingOf _ _ _ _ _ _ _ _ _ _ H2 HF.2.2.1 ?_, rowSpinOfX _ _ _ _ H3, H4, ?_⟩
  · rw [Hl]
    simp only [t2KBd, t2KMy, aqKm, aqKh, holdLen] at Hlt ⊢
    omega
  · simp only [t2KBd, t2KMy] at Hlt
    rw [Hl]; omega

/-- the critical-section body (AxSpinAp7) at `t2KBd q`. -/
theorem allocBody : RowAllocpidBody (t2KBd q) row AxSpinT2a.zNp (p + 48) := HF.2.2.2.2.2.1

/-- the spin loop's label premise (AxSpinAq1). -/
theorem allocSpinRmw : AxSpinAq1.spinRmw row (t2KSp q) q.n AxSpinT2a.zLk := HF.2.2.2.2.2.2.1

/-- the lk->cpu store values. -/
theorem allocCpuVals : t2CpuVals row i := HF.2.2.2.2.2.2.2.1

/-- the releasing store's value. -/
theorem allocRelVals : t2RelVals row q := HF.2.2.2.2.2.2.2.2

/-- release's row (AxSpinRl1) at `t2KRl q`. -/
theorem allocRelease :
    RowRelease (t2KRl q) q.c row (S - 8) (S - 16) (S - 24) AxSpinT2a.zLk (AxSpinT2a.zLk + 16)
      (S - 40) (S - 48) (S - 56) (S - 72) (S - 80) (S - 40) (S - 48) (S - 56) (S - 64)
      (cpuZ i + 120) (cpuZ i + 124) := by
  refine ⟨(AxSpinT2a.segParts HF.1).2.2.2.2.2.2.1, HF.2.2.2.2.1, ?_⟩
  rw [HF.2.1]
  exact AxSpinT2a.kTLen q

/-- AxSpinRl3 `XxSwRelRel`'s `Hst`: release's lock-word store is the `WCrel` store of `z4`
(class from the shape, `rowReleaseRel`; data from `t2RelVals`). -/
theorem allocRelZ4 :
    row[relKw (t2KRl q)]? = some (.LStore false AxSpinT2a.zLk AxSpinX4.z4 .WCrel) := by
  obtain ⟨vw, Hlb, -⟩ := rowReleaseRel (allocRelease HF)
  have Hz := allocRelVals HF vw .WCrel Hlb
  rw [Hz] at Hlb
  exact Hlb

/-- the terminal `sw a5,24(s1)`. -/
theorem allocTerm :
    ∃ vw cls, row[t2KT q]? = some (.LStore false (p + 24) vw cls) ∧ vw.length = 4 := by
  obtain ⟨lb, Hlb, vw, cls, rfl, Hl⟩ :=
    (AxSpinT2a.segParts HF.1).2.2.2.2.2.2.2 0 (.it (.RS (p + 24) 4)) rfl
  exact ⟨vw, cls, Hlb, Hl⟩

/-- the terminal item is the row's last. -/
theorem allocTermLast : t2KT q + 1 = row.length := by rw [HF.2.1]; rfl

/-- the body's `k + 67 < LEN` (AxSpinAp9). -/
theorem allocBodyLen : t2KBd q + 67 < row.length := by
  rw [HF.2.1]; exact AxSpinT2a.kBdLen q

/-- every row item matches a segment item. -/
theorem allocItem (k : Nat) (lb : Lbl) :
    row[k]? = some lb → ∃ x, (allocSeg q i S p)[k]? = some x ∧ xshape x lb := by
  intro Hk
  have Hlt : k < (allocSeg q i S p).length := by
    rw [allocSegLen, ← HF.2.1]; exact (List.getElem?_eq_some_iff.1 Hk).1
  obtain ⟨x, Hx⟩ : ∃ x, (allocSeg q i S p)[k]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
  obtain ⟨lb', Hlb', Hs⟩ := HF.1 k x Hx
  rw [Nat.zero_add, Hk] at Hlb'
  cases Hlb'
  exact ⟨x, Hx, Hs⟩

end parts

/-- AxSpinRl2's `CpuWin` from the family, given the anchor's lob facts at the lk->cpu writes. -/
theorem allocCpuWin (L : Xlay) (GT : GdexecT) (i : Agent) (q : T2Prm) (S p : Int) (e : Geid)
    (HF : allocFull (AxOpsem.grow (gtAdGd GT) i) q i S p) (hL : L.xlLk = AxSpinT2a.zLk)
    (Hlob : ∀ (k : Nat) (lb : Lbl) (rl : Bool) (m : Nat), e.2 < k →
      (AxOpsem.grow (gtAdGd GT) i)[k]? = some lb →
      aidentWr (aident lb) = some (rl, L.xlLk + 16, m) →
      e ∈ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) (i, k)) :
    CpuWin L GT i e := by
  intro k lb rl m hk Hlb Hid
  rw [hL] at Hid ⊢
  refine ⟨allocCpuVals HF k lb rl m Hlb Hid, Hlob k lb rl m hk Hlb (by rw [hL]; exact Hid)⟩

/-! ## Whole-row facts: widths and RMWs -/

/-- (Lean-only) per-item width / RMW facts. -/
def AxSpinT2a.itB : Ritem → Bool
  | .RS _ n => decide (n ≤ 8)
  | .RL _ n => decide (n ≤ 8)
  | _ => true

def AxSpinT2a.xB : Rxitem → Bool
  | .it it => AxSpinT2a.itB it
  | .RB .. => true
  | .RSc _ n _ => decide (n ≤ 8)
  | .RM _ _ pa n => decide (pa = AxSpinT2a.zLk) && decide (n = 4)

theorem AxSpinT2a.allMap (l : List Ritem) :
    l.all AxSpinT2a.itB = true → ∀ x ∈ l.map Rxitem.it, AxSpinT2a.xB x = true := by
  intro H x Hx
  obtain ⟨it, Hit, rfl⟩ := List.mem_map.1 Hx
  exact List.all_eq_true.1 H it Hit

theorem AxSpinT2a.segB (q : T2Prm) (i : Agent) (S p : Int) :
    ∀ x ∈ allocSeg q i S p, AxSpinT2a.xB x = true := by
  intro x hx
  simp only [allocSeg, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h | h | h
  · exact AxSpinT2a.allMap _ rfl x h
  · exact AxSpinT2a.allMap _ (by cases q.b <;> rfl) x h
  · exact AxSpinT2a.allMap _ (by cases q.hb <;> rfl) x h
  · rw [List.eq_of_mem_replicate h]; rfl
  · exact AxSpinT2a.allMap _ rfl x h
  · exact AxSpinT2a.allMap _ rfl x h
  · have Hr : (relSh q.c (S - 8) (S - 16) (S - 24) AxSpinT2a.zLk (AxSpinT2a.zLk + 16) (S - 40)
        (S - 48) (S - 56) (S - 72) (S - 80) (S - 40) (S - 48) (S - 56) (S - 64) (cpuZ i + 120)
        (cpuZ i + 124)).all AxSpinT2a.xB = true := by cases q.c <;> rfl
    exact List.all_eq_true.1 Hr x h
  · rw [h]; rfl

section whole
variable {row : List Lbl} {q : T2Prm} {i : Agent} {S p : Int}
variable (HF : allocFull row q i S p)
include HF

/-- every write in the row is at most 8 bytes wide (E8's `rowW8`). -/
theorem allocW8 : rowW8 row := by
  intro k lb rl b m Hk Hw
  obtain ⟨x, Hx, Hs⟩ := allocItem HF k lb Hk
  have HB := AxSpinT2a.segB q i S p x (List.mem_of_getElem? Hx)
  cases x with
  | it it =>
    cases it with
    | RF n => obtain ⟨aq, b', E⟩ := Hs; rw [E] at Hw; cases Hw
    | RP pb n => obtain ⟨aq, E⟩ := Hs; rw [E] at Hw; cases Hw
    | RL pb n => obtain ⟨aq, E⟩ := Hs; rw [E] at Hw; cases Hw
    | RS pb n =>
      obtain ⟨vw, cls, rfl, Hl⟩ := Hs
      simp only [aident, aidentWr, Option.some.injEq, Prod.mk.injEq] at Hw
      obtain ⟨_, _, rfl⟩ := Hw
      simp only [AxSpinT2a.xB, AxSpinT2a.itB, decide_eq_true_eq] at HB
      omega
  | RB pr pw sr sw => rw [Hs] at Hw; cases Hw
  | RSc pb n cls =>
    obtain ⟨vw, rfl, Hl⟩ := Hs
    simp only [aident, aidentWr, Option.some.injEq, Prod.mk.injEq] at Hw
    obtain ⟨_, _, rfl⟩ := Hw
    simp only [AxSpinT2a.xB, decide_eq_true_eq] at HB
    omega
  | RM aq rl' pb n =>
    rw [Hs] at Hw
    simp only [aidentWr, Option.some.injEq, Prod.mk.injEq] at Hw
    obtain ⟨_, _, rfl⟩ := Hw
    simp only [AxSpinT2a.xB, Bool.and_eq_true, decide_eq_true_eq] at HB
    omega

/-- the only RMWs of the row are the 4-byte amoswaps on `pid_lock`. -/
theorem allocRmw (k : Nat) (lb : Lbl) (aq rl : Bool) (pa : Int) (m : Nat) :
    row[k]? = some lb → aident lb = .IRmw aq rl pa m → pa = AxSpinT2a.zLk ∧ m = 4 := by
  intro Hk Hid
  obtain ⟨x, Hx, Hs⟩ := allocItem HF k lb Hk
  have HB := AxSpinT2a.segB q i S p x (List.mem_of_getElem? Hx)
  cases x with
  | it it =>
    cases it with
    | RF n => obtain ⟨aq', b', E⟩ := Hs; rw [E] at Hid; cases Hid
    | RP pb n => obtain ⟨aq', E⟩ := Hs; rw [E] at Hid; cases Hid
    | RL pb n => obtain ⟨aq', E⟩ := Hs; rw [E] at Hid; cases Hid
    | RS pb n => obtain ⟨vw, cls, rfl, -⟩ := Hs; cases Hid
  | RB pr pw sr sw => rw [Hs] at Hid; cases Hid
  | RSc pb n cls => obtain ⟨vw, rfl, -⟩ := Hs; cases Hid
  | RM aq' rl' pb n =>
    rw [Hs] at Hid
    cases Hid
    simp only [AxSpinT2a.xB, Bool.and_eq_true, decide_eq_true_eq] at HB
    exact HB

/-- no RMW of `n` bytes at `pa` unless it is the 4-byte lock word (PO6's `noRmwn`). -/
theorem allocNoRmwn (pa : Int) (n : Nat) (h : pa ≠ AxSpinT2a.zLk ∨ n ≠ 4) : noRmwn row pa n := by
  intro k lb aq rl m Hk Hid
  obtain ⟨h1, h2⟩ := allocRmw HF k lb aq rl pa m Hk Hid
  rcases h with h | h
  · exact absurd h1 h
  · omega

/-- E8's `noRmw8`. -/
theorem allocNoRmw8 (pa : Int) : noRmw8 row pa :=
  allocNoRmwn HF pa 8 (.inr (by decide))

end whole

/-! # 3. The value pins (Option V + Q18b) -/

/-- The pins of one hart, at the positions the leaves state them.  Return addresses: push_off
→ acquire + 0x10, holding → acquire + 0x16 / release + 0x10, acquire's mycpu → acquire + 0x28,
acquire → allocproc + 0x44, pop_off → release + 0x22, release → allocproc + 0x98; the callees'
own mycpu returns as in PO4 / Hd9 / PO6. -/
structure AllocPins (GD : Gdexec) (i : Agent) (q : T2Prm) : Prop where
  /-- push_off's first mycpu (PO1) -/
  poMy1 : graphValue GD (i, t2KPo + 5) = some (stBytes 8 (AxSpinPO.ppo 0x14))
  /-- push_off's arm `b` (`noff == 0`) -/
  poArm : ∀ vn, graphValue GD (i, t2KPo + 7) = some vn → (ldRes false 4 vn == zero_reg) = q.b
  /-- push_off's second mycpu (the intena arm, PO2) -/
  poMy2 : q.b = true → graphValue GD (i, t2KPo + 10) = some (stBytes 8 (AxSpinPO.ppo 0x30))
  /-- push_off's tail mycpu (PO3) -/
  poMy3 : graphValue GD (i, t2KPoT q + 2) = some (stBytes 8 (AxSpinPO.ppo 0x1c))
  /-- push_off's return -/
  poRet : graphValue GD (i, t2KPoT q + 6) = some (stBytes 8 (AxSpinHdB.pac 0x10))
  /-- holding's mycpu and holding's return (acquire's call, long path) -/
  hdRets : q.hb = true →
    graphValue GD (i, t2KHd q + 7) = some (stBytes 8 (pch 0x1a)) ∧
    graphValue GD (i, t2KHd q + 9) = some (stBytes 8 (AxSpinHdB.pac 0x16))
  /-- holding's arm on acquire's call: not held by this cpu (no panic) -/
  hdArm : q.hb = true → ∀ vcpu, graphValue GD (i, t2KHd q + 4) = some vcpu →
    ldRes false 8 vcpu ≠ cpuAddr (cpuOf i)
  /-- acquire's mycpu -/
  aqMy : graphValue GD (i, t2KMy q + 2) = some (stBytes 8 (AxSpinHdB.pac 0x28))
  /-- acquire's return -/
  aqRet : graphValue GD (i, t2KMy q + 5) = some (stBytes 8 (pca 0x44))
  /-- Q18b: the nextpid read is not 1000 and does not wrap -/
  npNowrap : ∀ vs, graphValue GD (i, t2KBd q) = some vs →
    (wordOfBytes 4 vs : BitVec 32) ≠ 1000#32 ∧ (wordOfBytes 4 vs : BitVec 32).toNat + 1 < 2 ^ 32
  /-- Q18b: no pid collision in the scan -/
  npNcoll : ∀ vs, graphValue GD (i, t2KBd q) = some vs → ∀ j, j < 64 → ∀ v,
    graphValue GD (i, t2KBd q + 1 + j) = some v → (wordOfBytes 4 v : BitVec 32) ≠ wordOfBytes 4 vs
  /-- holding's mycpu and holding's return (release's call) -/
  rhRets : graphValue GD (i, t2KRh q + 7) = some (stBytes 8 (pch 0x1a)) ∧
    graphValue GD (i, t2KRh q + 9) = some (stBytes 8 (AxSpinHdB.prl 0x10))
  /-- holding's arm on release's call: held by this cpu (no panic) -/
  rhArm : ∀ vcpu, graphValue GD (i, t2KRh q + 4) = some vcpu → ldRes false 8 vcpu = cpuAddr (cpuOf i)
  /-- pop_off's mycpu -/
  ppMy : graphValue GD (i, t2KPp q + 4) = some (stBytes 8 (ppp 0x0c))
  /-- pop_off's `noff ≥ 1` (no panic) -/
  ppGe : ∀ vn, graphValue GD (i, t2KPp q + 6) = some vn →
    zopz0zKzJ_s zero_reg (ldRes false 4 vn) = false
  /-- pop_off's arm `c` -/
  ppArm : ∀ vn, graphValue GD (i, t2KPp q + 6) = some vn → (addiwm1 (ldRes false 4 vn) != zero_reg) = q.c
  /-- pop_off's intena check (arm `c = false`: intena = 0, interrupts stay off) -/
  ppInt : q.c = false → ∀ vi, graphValue GD (i, t2KPp q + 8) = some vi →
    (ldRes false 4 vi == zero_reg) = true
  /-- pop_off's return -/
  ppRet : graphValue GD (i, t2KPp q + 8 + (if q.c then 0 else 1)) =
    some (stBytes 8 (AxSpinHdB.prl 0x22))
  /-- release's return -/
  rlRet : graphValue GD (i, t2KRr q) = some (stBytes 8 (pca 0x98))
  /-- (AxSpinApA) push_off's s1 reload (acquire's `lk`, AxSpinAq2's extra pin) -/
  poS1 : graphValue GD (i, t2KPoT q + 8) =
    some (stBytes 8 (BitVec.ofNat 64 KernelSyms.«pid_lock»))
  /-- (AxSpinApA) holding's s1 reload on acquire's call (AxSpinAq2's extra pin) -/
  hdS1 : q.hb = true → graphValue GD (i, t2KHd q + 11) =
    some (stBytes 8 (BitVec.ofNat 64 KernelSyms.«pid_lock»))
  /-- (AxSpinApA) acquire's s1 reload returns acquire's s1 spill (`p`; the critical section's
  `p->pid` base) -/
  aqS1 : graphValue GD (i, t2KMy q + 7) = graphData GD (i, 2)
  /-- (AxSpinApA) holding's lk->cpu read on release's call returns this cpu (AxSpinRl4b's `Hvcpu`,
  the value form of `rhArm`) -/
  rhCpu : graphValue GD (i, t2KRh q + 4) = some (stBytes 8 (cpuAddr (cpuOf i)))
  /-- (AxSpinApA) holding's s1 reload on release's call (AxSpinRl4b's `Hvs1`) -/
  rhS1 : graphValue GD (i, t2KRh q + 11) =
    some (stBytes 8 (BitVec.ofNat 64 KernelSyms.«pid_lock»))
  /-- (AxSpinApA) release's s1 reload returns release's s1 spill (`p`; the terminal store's
  base) -/
  rlS1 : graphValue GD (i, t2KRr q + 2) = graphData GD (i, t2KRl q + 2)

/-- The return addresses are `jalr` fixpoints (the leaves' `Hret`). -/
theorem AxSpinT2a.jalrRets :
    jalrTgt 0#12 (AxSpinHdB.pac 0x10) = AxSpinHdB.pac 0x10 ∧
    jalrTgt 0#12 (AxSpinHdB.pac 0x16) = AxSpinHdB.pac 0x16 ∧
    jalrTgt 0#12 (AxSpinHdB.pac 0x28) = AxSpinHdB.pac 0x28 ∧
    jalrTgt 0#12 (pca 0x44) = pca 0x44 ∧
    jalrTgt 0#12 (AxSpinHdB.prl 0x10) = AxSpinHdB.prl 0x10 ∧
    jalrTgt 0#12 (AxSpinHdB.prl 0x22) = AxSpinHdB.prl 0x22 ∧
    jalrTgt 0#12 (pca 0x98) = pca 0x98 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- `mycpu`'s result at `tp = hartId c` is `&cpus[c]`. -/
theorem AxSpinT2a.mycpuRetHart : ∀ c : CPU, AxSpinE8.mycpuRet (hartId c) = cpuAddr c := by
  decide +kernel

/-- holding's result `seqz (lk->cpu − mycpu())` is zero iff the two differ. -/
theorem AxSpinT2a.hresZero (x y : BitVec 64) : hres (0#64 + x) y = 0#64 ↔ x ≠ y := by
  have h1 : sign_extend (m := 64) (1#12) = 1#64 := by decide
  unfold hres zopz0zI_u
  rw [h1, BitVec.zero_add]
  have key : (Sail.BitVec.toNatInt (x - y) < Sail.BitVec.toNatInt (1#64)) ↔ x = y := by
    unfold Sail.BitVec.toNatInt
    simp only [Int.ofNat_eq_natCast, BitVec.toNat_ofNat]
    constructor
    · intro hlt
      have h0 : (x - y).toNat = 0 := by omega
      have h2 : x - y = 0#64 := BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
      have h3 := congrArg (· + y) h2
      simp only [BitVec.sub_add_cancel, BitVec.zero_add] at h3
      exact h3
    · rintro rfl
      rw [BitVec.sub_self]
      decide
  have hT : zero_extend (m := 64) (bool_to_bit true) ≠ 0#64 := by decide
  have hF : zero_extend (m := 64) (bool_to_bit false) = 0#64 := by decide
  by_cases h : x = y
  · rw [decide_eq_true (key.2 h)]
    exact ⟨fun e => absurd e hT, fun e => absurd h e⟩
  · rw [decide_eq_false (fun hl => h (key.1 hl))]
    exact ⟨fun _ => h, fun _ => hF⟩

/-! # 4. The per-hart posts and the joint step -/

/-- (Lean-only) `sext32 w`: what `lw` puts in a register (`ldRes false 4 vs = sext32 (word vs)`). -/
def AxSpinT2a.sext32 (w : BitVec 32) : BitVec 64 := extend_value false (w : BitVec (8 * 4))

theorem AxSpinT2a.ldResSext32 (vs : List (BitVec 8)) :
    ldRes false 4 vs = AxSpinT2a.sext32 (wordOfBytes 4 vs) := rfl

/-- (Lean-only) a GPR of a hart state. -/
def AxSpinT2a.gprOf (s : Athread) (r : BitVec 5) : Option (BitVec 64) :=
  match s.atP with
  | .PHart _ _ rs _ _ => some (gprVal rs r)
  | _ => none

theorem AxSpinT2a.gprOfHart (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (k : Nat) (r : BitVec 5) :
    AxSpinT2a.gprOf ⟨.PHart cpu m rs fn ib, k⟩ r = some (gprVal rs r) := rfl

section posts
variable {GF : BundledGFunctors} [AxSpinX.Xv6G GF]

/-- THE POST of hart `i` (A or B): at a final (non-mid) state, an issued pid `w` with the
`p->pid` store's data, `a3` and the nextpid read's source, and the exclusive fragment. -/
def t2Post (GD : Gdexec) (L : Xlay) (nm : Xv6N) (i : Agent) (q : T2Prm) (s : Athread) : IProp GF :=
  iprop(⌜¬ midState s⌝ -∗ ∃ w : BitVec 32,
    ⌜pidOf GD i q = some (WeakInterpProj.wbytes 4 w) ∧
      AxSpinT2a.gprOf s 13#5 = some (AxSpinT2a.sext32 w) ∧
      npSrc GD.gdG L (i, t2KBd q) (i, t2KA q)⌝ ∗ FRAG nm w)

theorem AxSpinT2a.postOpen (GD : Gdexec) (L : Xlay) (nm : Xv6N) (i : Agent) (q : T2Prm)
    (s : Athread) (h : ¬ midState s) :
    t2Post (GF := GF) GD L nm i q s ⊢ ∃ w : BitVec 32,
      ⌜pidOf GD i q = some (WeakInterpProj.wbytes 4 w) ∧
        AxSpinT2a.gprOf s 13#5 = some (AxSpinT2a.sext32 w) ∧
        npSrc GD.gdG L (i, t2KBd q) (i, t2KA q)⌝ ∗ FRAG nm w := by
  unfold t2Post
  iintro H
  iapply H
  ipureintro
  exact h

/-- Two fragments at one ghost name carry different words (`issuedFragExcl`). -/
theorem AxSpinT2a.fragNe (nm : Xv6N) (wA wB : BitVec 32) :
    FRAG (GF := GF) nm wA ∗ FRAG nm wB ⊢ ⌜wA ≠ wB⌝ := by
  unfold FRAG
  iintro ⟨⟨%vA, HA, %HvA⟩, ⟨%vB, HB, %HvB⟩⟩
  by_cases hw : wA = wB
  · have key : ∀ v : Int, 0 ≤ v ∧ v < 2 ^ 32 → ((BitVec.ofInt 32 v).toNat : Int) = v := by
      intro v hv
      rw [BitVec.toNat_ofInt]
      omega
    have Heq : vA = vB := by
      have h1 := key vA HvA.1
      have h2 := key vB HvB.1
      rw [HvA.2] at h1
      rw [HvB.2, ← hw] at h2
      omega
    subst Heq
    iexfalso
    iapply issuedFragExcl nm.xnI vA
    isplitl [HA]
    · iexact HA
    · iexact HB
  · ipureintro
    exact hw

end posts

/-- THE PER-HART POSTS at the concrete GF (A, B: `t2Post`; anyone else: `True`). -/
def t2Phi (GD : Gdexec) (L : Xlay) (A B : Agent) (qA qB : T2Prm) :
    InvGS_gen .hasNoLC AxSpinX7.xv6GF → AxannotGS AxSpinX7.xv6GF → Xv6N → Agent → Athread →
      IProp AxSpinX7.xv6GF :=
  fun _ _ nm i s =>
    if i = A then t2Post GD L nm A qA s else if i = B then t2Post GD L nm B qB s else iprop(True)

theorem AxSpinT2a.phiA (GD : Gdexec) (L : Xlay) (A B : Agent) (qA qB : T2Prm)
    (Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF) (Hann : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N)
    (s : Athread) : t2Phi GD L A B qA qB Hinv Hann nm A s = t2Post GD L nm A qA s := by
  simp [t2Phi]

theorem AxSpinT2a.phiB (GD : Gdexec) (L : Xlay) (A B : Agent) (qA qB : T2Prm) (hAB : A ≠ B)
    (Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF) (Hann : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N)
    (s : Athread) : t2Phi GD L A B qA qB Hinv Hann nm B s = t2Post GD L nm B qB s := by
  simp [t2Phi, Ne.symm hAB]

theorem AxSpinT2a.phiC (GD : Gdexec) (L : Xlay) (A B C : Agent) (qA qB : T2Prm) (hCA : C ≠ A)
    (hCB : C ≠ B) (Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF) (Hann : AxannotGS AxSpinX7.xv6GF)
    (nm : Xv6N) (s : Athread) : t2Phi GD L A B qA qB Hinv Hann nm C s = iprop(True) := by
  simp [t2Phi, hCA, hCB]

/-- THE CONCLUSION the joint step delivers (Theorem 2's second conjunct, plus `npSrc`). -/
def t2Concl (GD : Gdexec) (L : Xlay) (A B : Agent) (qA qB : T2Prm) (sA sB : Athread) : Prop :=
  ∃ wA wB : BitVec 32,
    pidOf GD A qA = some (WeakInterpProj.wbytes 4 wA) ∧
    pidOf GD B qB = some (WeakInterpProj.wbytes 4 wB) ∧
    AxSpinT2a.gprOf sA 13#5 = some (AxSpinT2a.sext32 wA) ∧
    AxSpinT2a.gprOf sB 13#5 = some (AxSpinT2a.sext32 wB) ∧
    npSrc GD.gdG L (A, t2KBd qA) (A, t2KA qA) ∧ npSrc GD.gdG L (B, t2KBd qB) (B, t2KA qB) ∧
    wA ≠ wB

/-- THE JOINT STEP (design `Hjoint`): the three posts at the final states give `t2Concl`. -/
theorem t2Joint (GD : Gdexec) (L : Xlay) (A B C : Agent) (qA qB : T2Prm) (sN : Agent → Athread)
    (hAB : A ≠ B) (hmA : ¬ midState (sN A)) (hmB : ¬ midState (sN B))
    (Hinv : InvGS_gen .hasNoLC AxSpinX7.xv6GF) (Hann : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N) :
    ⊢ ([∗list] i ∈ [A, B, C], t2Phi GD L A B qA qB Hinv Hann nm i (sN i)) ==∗
      ⌜t2Concl GD L A B qA qB (sN A) (sN B)⌝ := by
  have Htri : ([∗list] i ∈ [A, B, C], t2Phi GD L A B qA qB Hinv Hann nm i (sN i)) ⊢
      t2Post GD L nm A qA (sN A) ∗ t2Post GD L nm B qB (sN B) := by
    refine (AxSpinJ2.bigSepLTriple A B C _).1.trans ?_
    rw [AxSpinT2a.phiA, AxSpinT2a.phiB GD L A B qA qB hAB]
    exact sep_mono .rfl sep_elim_left
  have HA := AxSpinT2a.postOpen (GF := AxSpinX7.xv6GF) GD L nm A qA (sN A) hmA
  have HB := AxSpinT2a.postOpen (GF := AxSpinX7.xv6GF) GD L nm B qB (sN B) hmB
  iintro HI
  ihave HI := Htri $$ HI
  icases HI with ⟨HPA, HPB⟩
  ihave HPA := HA $$ HPA
  ihave HPB := HB $$ HPB
  icases HPA with ⟨%wA, %HwA, FA⟩
  icases HPB with ⟨%wB, %HwB, FB⟩
  ihave %Hne := (AxSpinT2a.fragNe (GF := AxSpinX7.xv6GF) nm wA wB) $$ [FA FB]
  · isplitl [FA]
    · iexact FA
    · iexact FB
  imodintro
  ipureintro
  exact ⟨wA, wB, HwA.1, HwB.1, HwA.2.1, HwB.2.1, HwA.2.2, HwB.2.2, Hne⟩

/-! # 5. The layout -/

/-- (Lean-only) hart `j`'s private stack / proc-field bytes. -/
def AxSpinT2a.stkSet (S p : Int) : GSet Int :=
  LawfulSet.ofList (clRange (S - 80) 80 ++ (clRange (p + 24) 4 ++ clRange (p + 48) 4))
/-- (Lean-only) hart `j`'s struct-cpu bytes `noff`, `intena`. -/
def AxSpinT2a.cpufSet (j : Agent) : GSet Int := LawfulSet.ofList (clRange (cpuZ j + 120) 8)
/-- (Lean-only) the kernel text `[_text, etext)`. -/
def AxSpinT2a.textZ (a : Int) : Prop :=
  (KernelSyms.«_text» : Int) ≤ a ∧ a < (KernelSyms.«etext» : Int)

/-- THE REAL LAYOUT.  `S j` = hart `j`'s frame base (sp at allocproc + 0x38), `p j` its proc
slot, `ptp` the page-table pages. -/
def xlayXv6 (A B C : Agent) (S p : Agent → Int) (ptp : Int → Prop) : Xlay where
  xlLk := AxSpinT2a.zLk
  xlNp := AxSpinT2a.zNp
  xlHarts := [A, B, C]
  xlStk := fun j => if j = A ∨ j = B ∨ j = C then AxSpinT2a.stkSet (S j) (p j) else ∅
  xlCpuf := fun j => if j = A ∨ j = B ∨ j = C then AxSpinT2a.cpufSet j else ∅
  xlRo := fun a => AxSpinT2a.textZ a ∨ ptp a
  xlText := AxSpinT2a.textZ

/-- (Lean-only) the private ranges of a hart. -/
def AxSpinT2a.privZ (S p : Int) (j : Agent) (a : Int) : Prop :=
  (S - 80 ≤ a ∧ a < S) ∨ (p + 24 ≤ a ∧ a < p + 28) ∨ (p + 48 ≤ a ∧ a < p + 52) ∨
  (cpuZ j + 120 ≤ a ∧ a < cpuZ j + 128)

theorem AxSpinT2a.privIff (A B C : Agent) (S p : Agent → Int) (ptp : Int → Prop) (a : Int)
    (j : Agent) :
    priv (xlayXv6 A B C S p ptp) a j ↔
      (j = A ∨ j = B ∨ j = C) ∧ AxSpinT2a.privZ (S j) (p j) j a := by
  unfold priv
  simp only [xlayXv6, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨hj, hs⟩
    refine ⟨hj, ?_⟩
    rw [if_pos hj, if_pos hj] at hs
    unfold AxSpinT2a.stkSet AxSpinT2a.cpufSet at hs
    rw [← LawfulSet.mem_ofList, ← LawfulSet.mem_ofList] at hs
    simp only [List.mem_append, inClr] at hs
    unfold AxSpinT2a.privZ
    push_cast at hs
    omega
  · rintro ⟨hj, hz⟩
    refine ⟨hj, ?_⟩
    rw [if_pos hj, if_pos hj]
    unfold AxSpinT2a.stkSet AxSpinT2a.cpufSet
    rw [← LawfulSet.mem_ofList, ← LawfulSet.mem_ofList]
    simp only [List.mem_append, inClr]
    unfold AxSpinT2a.privZ at hz
    push_cast
    omega

/-- The layout hypotheses. -/
structure T2LayHyp (A B C : Agent) (S p : Agent → Int) (ptp : Int → Prop) : Prop where
  nd : [A, B, C].Nodup
  ncpu : A < NCPU ∧ B < NCPU ∧ C < NCPU
  /-- each hart's slot is a `proc[]` entry -/
  slot : ∀ j, (j = A ∨ j = B ∨ j = C) →
    ∃ m : Nat, m < 64 ∧ p j = (KernelSyms.«proc» : Int) + 376 * (m : Int)
  slotInj : ∀ j1 j2, (j1 = A ∨ j1 = B ∨ j1 = C) → (j2 = A ∨ j2 = B ∨ j2 = C) → j1 ≠ j2 →
    p j1 ≠ p j2
  /-- the stack windows lie in `stack0` -/
  stk : ∀ j, (j = A ∨ j = B ∨ j = C) →
    (KernelSyms.«stack0» : Int) + 80 ≤ S j ∧ S j ≤ (KernelSyms.«stack0» : Int) + 0x8000
  stkDisj : ∀ j1 j2, (j1 = A ∨ j1 = B ∨ j1 = C) → (j2 = A ∨ j2 = B ∨ j2 = C) → j1 ≠ j2 →
    S j1 + 80 ≤ S j2 ∨ S j2 + 80 ≤ S j1
  /-- the page-table pages are kalloc'd (above `end`) -/
  ptpEnd : ∀ a, ptp a → (KernelSyms.«end» : Int) ≤ a

theorem AxSpinT2a.symV :
    (KernelSyms.«pid_lock» : Int) = 0x80012500 ∧ (KernelSyms.«nextpid» : Int) = 0x8000a384 ∧
    (KernelSyms.«proc» : Int) = 0x80012930 ∧ (KernelSyms.«cpus» : Int) = 0x80012530 ∧
    (KernelSyms.«stack0» : Int) = 0x8000a420 ∧ (KernelSyms.«end» : Int) = 0x80023b10 ∧
    (KernelSyms.«_text» : Int) = 0x80000000 ∧ (KernelSyms.«etext» : Int) = 0x80007000 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem AxSpinT2a.hartLt (A B C : Agent) (S p : Agent → Int) (ptp : Int → Prop)
    (H : T2LayHyp A B C S p ptp) (j : Agent) (hj : j = A ∨ j = B ∨ j = C) : j < NCPU := by
  obtain ⟨h1, h2, h3⟩ := H.ncpu
  rcases hj with rfl | rfl | rfl <;> assumption

/-- The private ranges of a hart of the layout, made explicit. -/
theorem AxSpinT2a.privBounds (A B C : Agent) (S p : Agent → Int) (ptp : Int → Prop)
    (H : T2LayHyp A B C S p ptp) (a : Int) (j : Agent) :
    priv (xlayXv6 A B C S p ptp) a j →
      ∃ m : Nat, m < 64 ∧ p j = 0x80012930 + 376 * (m : Int) ∧ 0x8000a420 + 80 ≤ S j ∧
        S j ≤ 0x8000a420 + 0x8000 ∧ (j : Int) < 8 ∧
        ((S j - 80 ≤ a ∧ a < S j) ∨ (p j + 24 ≤ a ∧ a < p j + 28) ∨
          (p j + 48 ≤ a ∧ a < p j + 52) ∨
          (0x80012530 + 128 * (j : Int) + 120 ≤ a ∧ a < 0x80012530 + 128 * (j : Int) + 128)) := by
  intro Hp
  obtain ⟨hj, hz⟩ := (AxSpinT2a.privIff A B C S p ptp a j).1 Hp
  obtain ⟨m, hm, hpm⟩ := H.slot j hj
  have hS := H.stk j hj
  have hlt := AxSpinT2a.hartLt A B C S p ptp H j hj
  have hc := cpuOfNat j hlt
  obtain ⟨v1, -, v3, v4, v5, -, -, -⟩ := AxSpinT2a.symV
  unfold AxSpinT2a.privZ cpuZ at hz
  rw [hc, v4] at hz
  rw [v3] at hpm
  rw [v5] at hS
  have h8 : (j : Int) < 8 := by
    have h := Int.ofNat_lt.2 hlt
    exact h
  exact ⟨m, hm, hpm, hS.1, hS.2, h8, hz⟩

theorem xlayXv6Ok (A B C : Agent) (S p : Agent → Int) (ptp : Int → Prop)
    (H : T2LayHyp A B C S p ptp) : xlayOk (xlayXv6 A B C S p ptp) := by
  obtain ⟨v1, v2, -, -, -, v6, v7, v8⟩ := AxSpinT2a.symV
  have Hlwb : ∀ a, a ∈ lwb (xlayXv6 A B C S p ptp) → 0x80012500 ≤ a ∧ a < 0x80012504 := by
    intro a Ha
    unfold lwb at Ha
    rw [inClr] at Ha
    simp only [xlayXv6, v1] at Ha
    omega
  have HXO : ∀ a, a ∈ XO (xlayXv6 A B C S p ptp) →
      (0x80012510 ≤ a ∧ a < 0x80012518) ∨ (0x8000a384 ≤ a ∧ a < 0x8000a388) := by
    intro a Ha
    unfold XO clb npb at Ha
    rw [elemOfUnion, ← LawfulSet.mem_ofList, ← LawfulSet.mem_ofList, inClr, inClr] at Ha
    simp only [xlayXv6, v1, v2] at Ha
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold lwb clb npb
    simp only [xlayXv6]
    decide +kernel
  · intro a j Hp
    obtain ⟨m, hm, hpm, hS1, hS2, hj8, hz⟩ := AxSpinT2a.privBounds A B C S p ptp H a j Hp
    refine ⟨fun Hl => ?_, fun Hx => ?_⟩
    · have := Hlwb a Hl
      omega
    · have := HXO a Hx
      omega
  · intro a j1 j2 H1 H2
    apply Classical.byContradiction
    intro hne
    obtain ⟨m1, hm1, hp1, hS11, hS12, hj1, hz1⟩ := AxSpinT2a.privBounds A B C S p ptp H a j1 H1
    obtain ⟨m2, hm2, hp2, hS21, hS22, hj2, hz2⟩ := AxSpinT2a.privBounds A B C S p ptp H a j2 H2
    have hj1m := ((AxSpinT2a.privIff A B C S p ptp a j1).1 H1).1
    have hj2m := ((AxSpinT2a.privIff A B C S p ptp a j2).1 H2).1
    have hpne := H.slotInj j1 j2 hj1m hj2m hne
    have hsd := H.stkDisj j1 j2 hj1m hj2m hne
    have hjne : (j1 : Int) ≠ (j2 : Int) := fun e => hne (Int.ofNat_inj.1 e)
    have hmne : m1 ≠ m2 := by
      intro e
      subst e
      exact hpne (hp1.trans hp2.symm)
    omega
  · intro a j Hro Hw
    have Hro' : AxSpinT2a.textZ a ∨ ptp a := Hro
    have Hr : (0x80000000 ≤ a ∧ a < 0x80007000) ∨ 0x80023b10 ≤ a := by
      rcases Hro' with h | h
      · unfold AxSpinT2a.textZ at h
        rw [v7, v8] at h
        exact .inl h
      · have := H.ptpEnd a h
        rw [v6] at this
        exact .inr this
    rcases Hw with Hw | Hw | Hw
    · have := Hlwb a Hw
      omega
    · have := HXO a Hw
      omega
    · obtain ⟨m, hm, hpm, hS1, hS2, hj8, hz⟩ := AxSpinT2a.privBounds A B C S p ptp H a j Hw
      omega
  · exact H.nd
  · intro i Hi
    have Hi' : i ∈ [A, B, C] := Hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hi'
    exact AxSpinT2a.hartLt A B C S p ptp H i Hi'

/-- cid injectivity on the harts. -/
theorem t2CpuInj (A B : Agent) (hAB : A ≠ B) (hA : A < NCPU) (hB : B < NCPU) :
    cpuAddr (cpuOf A) ≠ cpuAddr (cpuOf B) := by
  intro h
  have := congrArg Fin.val (cpuAddr_inj h)
  rw [cpuOfNat A hA, cpuOfNat B hB] at this
  exact hAB this

/-- (Lean-only) the sanity instance's frame bases and slots. -/
def AxSpinT2a.sEx (j : Agent) : Int := (KernelSyms.«stack0» : Int) + 4096 * ((j : Int) + 1)
def AxSpinT2a.pEx (j : Agent) : Int := (KernelSyms.«proc» : Int) + 376 * (j : Int)

theorem AxSpinT2a.layHypReal :
    T2LayHyp 0 1 2 AxSpinT2a.sEx AxSpinT2a.pEx (fun _ => False) := by
  obtain ⟨-, -, v3, -, v5, -, -, -⟩ := AxSpinT2a.symV
  refine ⟨by decide, by decide, ?_, ?_, ?_, ?_, fun _ h => h.elim⟩
  · intro j hj
    rcases hj with rfl | rfl | rfl
    · exact ⟨0, by decide, by simp [AxSpinT2a.pEx]⟩
    · exact ⟨1, by decide, by simp [AxSpinT2a.pEx]⟩
    · exact ⟨2, by decide, by simp [AxSpinT2a.pEx]⟩
  · intro j1 j2 h1 h2 hne
    unfold AxSpinT2a.pEx
    rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
      first | exact absurd rfl hne | omega
  · intro j hj
    unfold AxSpinT2a.sEx
    rw [v5]
    rcases hj with rfl | rfl | rfl <;> omega
  · intro j1 j2 h1 h2 hne
    unfold AxSpinT2a.sEx
    rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
      first | exact absurd rfl hne | omega

/-- NON-VACUITY: the layout hypotheses hold at the real kernel symbols. -/
theorem xlayXv6Real : xlayOk (xlayXv6 0 1 2 AxSpinT2a.sEx AxSpinT2a.pEx (fun _ => False)) :=
  xlayXv6Ok _ _ _ _ _ _ AxSpinT2a.layHypReal

/-! ## The releasing store's window (AxSpinRl3's `Hone`), from the shape -/

/-- (Lean-only) the write base of a segment item (`none` for reads / fences). -/
def AxSpinT2a.xWa : Rxitem → Option Int
  | .it (.RS pa _) => some pa
  | .RSc pa _ _ => some pa
  | .RM _ _ pa _ => some pa
  | _ => none

/-- (Lean-only) a write matching a segment item writes at the item's base. -/
theorem AxSpinT2a.xWaOf (x : Rxitem) (lb : Lbl) (rl : Bool) (pa : Int) (n : Nat) :
    xshape x lb → aidentWr (aident lb) = some (rl, pa, n) → AxSpinT2a.xWa x = some pa := by
  intro Hs Hw
  cases x with
  | it it =>
    cases it with
    | RF n' => obtain ⟨aq, b', E⟩ := Hs; rw [E] at Hw; cases Hw
    | RP pb n' => obtain ⟨aq, E⟩ := Hs; rw [E] at Hw; cases Hw
    | RL pb n' => obtain ⟨aq, E⟩ := Hs; rw [E] at Hw; cases Hw
    | RS pb n' =>
      obtain ⟨vw, cls, rfl, -⟩ := Hs
      simp only [aident, aidentWr, Option.some.injEq, Prod.mk.injEq] at Hw
      obtain ⟨_, rfl, _⟩ := Hw
      rfl
  | RB pr pw sr sw => rw [Hs] at Hw; cases Hw
  | RSc pb n' cls =>
    obtain ⟨vw, rfl, -⟩ := Hs
    simp only [aident, aidentWr, Option.some.injEq, Prod.mk.injEq] at Hw
    obtain ⟨_, rfl, _⟩ := Hw
    rfl
  | RM aq rl' pb n' =>
    rw [Hs] at Hw
    simp only [aidentWr, Option.some.injEq, Prod.mk.injEq] at Hw
    obtain ⟨_, rfl, _⟩ := Hw
    rfl

/-- (Lean-only) the private bytes of a layout hart miss the lock word's base. -/
theorem AxSpinT2a.privNeLk (A B C : Agent) (S p : Agent → Int) (ptp : Int → Prop)
    (H : T2LayHyp A B C S p ptp) (j : Agent) (hj : j = A ∨ j = B ∨ j = C) :
    ∀ a, AxSpinT2a.privZ (S j) (p j) j a → a ≠ AxSpinT2a.zLk := by
  intro a hz
  obtain ⟨m, hm, hpm, hS1, hS2, hj8, hz'⟩ := AxSpinT2a.privBounds A B C S p ptp H a j
    ((AxSpinT2a.privIff A B C S p ptp a j).2 ⟨hj, hz⟩)
  have v1 : AxSpinT2a.zLk = 0x80012500 := rfl
  rw [v1]
  omega

section relwin
variable {row : List Lbl} {q : T2Prm} {i : Agent} {S p : Int}

/-- (Lean-only) the segment around the releasing store: the prefix through the claim, the
items up to the fence, the store, the rest. -/
theorem AxSpinT2a.segSplit :
    allocSeg q i S p =
      ((aqHead (S - 8) (S - 16) (S - 24)).map .it ++
        ((poSh q.b (S - 40) (S - 48) (S - 56) (S - 72) (S - 80) (cpuZ i + 120)
          (cpuZ i + 124)).map .it ++
        ((holdShB q.hb AxSpinT2a.zLk (AxSpinT2a.zLk + 16) (S - 40) (S - 48) (S - 56) (S - 72)
          (S - 80)).map .it ++
        List.replicate (q.n + 1) (Rxitem.RM true false AxSpinT2a.zLk 4)))) ++
      (((aqTail (S - 40) (S - 48) (AxSpinT2a.zLk + 16) (S - 8) (S - 16) (S - 24)).map .it ++
        ((apBodySh AxSpinT2a.zNp (p + 48)).map .it ++
        ((relHead (S - 8) (S - 16) (S - 24)).map .it ++
        ((holdShB true AxSpinT2a.zLk (AxSpinT2a.zLk + 16) (S - 40) (S - 48) (S - 56) (S - 72)
          (S - 80)).map .it ++
        [Rxitem.it (.RS (AxSpinT2a.zLk + 16) 8), .RB true true false true])))) ++
      (Rxitem.RSc AxSpinT2a.zLk 4 .WCrel ::
        ((ppSh q.c (S - 40) (S - 48) (S - 56) (S - 64) (cpuZ i + 120) (cpuZ i + 124)).map .it ++
        ((relTail (S - 8) (S - 16) (S - 24)).map .it ++ [Rxitem.it (.RS (p + 24) 4)])))) := by
  simp only [allocSeg, relSh, List.append_assoc, List.cons_append, List.nil_append]

/-- (Lean-only) no item of a list writes the lock word's base. -/
def AxSpinT2a.noLk (l : List Rxitem) : Prop := ∀ x ∈ l, AxSpinT2a.xWa x ≠ some AxSpinT2a.zLk

theorem AxSpinT2a.noLkMap (l : List Ritem) :
    (∀ pa n, Ritem.RS pa n ∈ l → pa ≠ AxSpinT2a.zLk) → AxSpinT2a.noLk (l.map .it) := by
  intro H x hx
  obtain ⟨it, hit, rfl⟩ := List.mem_map.1 hx
  cases it with
  | RS pa n => intro e; exact H _ _ hit (Option.some.inj e)
  | _ => intro e; cases e

theorem AxSpinT2a.noLkApp (l1 l2 : List Rxitem) :
    AxSpinT2a.noLk l1 → AxSpinT2a.noLk l2 → AxSpinT2a.noLk (l1 ++ l2) := by
  intro H1 H2 x hx
  rcases List.mem_append.1 hx with h | h
  · exact H1 x h
  · exact H2 x h

variable (Hpz : ∀ a, AxSpinT2a.privZ S p i a → a ≠ AxSpinT2a.zLk)
include Hpz

theorem AxSpinT2a.midNoLk :
    AxSpinT2a.noLk
      ((aqTail (S - 40) (S - 48) (AxSpinT2a.zLk + 16) (S - 8) (S - 16) (S - 24)).map .it ++
        ((apBodySh AxSpinT2a.zNp (p + 48)).map .it ++
        ((relHead (S - 8) (S - 16) (S - 24)).map .it ++
        ((holdShB true AxSpinT2a.zLk (AxSpinT2a.zLk + 16) (S - 40) (S - 48) (S - 56) (S - 72)
          (S - 80)).map .it ++
        [Rxitem.it (.RS (AxSpinT2a.zLk + 16) 8), .RB true true false true])))) := by
  have hs : ∀ d : Int, 1 ≤ d → d ≤ 80 → S - d ≠ AxSpinT2a.zLk := fun d h1 h2 =>
    Hpz _ (by unfold AxSpinT2a.privZ; omega)
  have hl : AxSpinT2a.zLk + 16 ≠ AxSpinT2a.zLk := by omega
  refine AxSpinT2a.noLkApp _ _ (AxSpinT2a.noLkMap _ ?_) (AxSpinT2a.noLkApp _ _
    (AxSpinT2a.noLkMap _ ?_) (AxSpinT2a.noLkApp _ _ (AxSpinT2a.noLkMap _ ?_)
    (AxSpinT2a.noLkApp _ _ (AxSpinT2a.noLkMap _ ?_) ?_)))
  · intro pa n h
    simp only [aqTail, mycSh, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, reduceCtorEq, Ritem.RS.injEq, false_or] at h
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hs 40 (by omega) (by omega)
    · exact hs 48 (by omega) (by omega)
    · exact hl
  · intro pa n h
    simp only [apBodySh, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
      or_false, reduceCtorEq, Ritem.RS.injEq, false_or, and_false, exists_false] at h
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · decide
    · exact Hpz _ (by unfold AxSpinT2a.privZ; omega)
  · intro pa n h
    simp only [relHead, List.mem_cons, List.not_mem_nil, or_false, Ritem.RS.injEq] at h
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hs 8 (by omega) (by omega)
    · exact hs 16 (by omega) (by omega)
    · exact hs 24 (by omega) (by omega)
  · intro pa n h
    simp only [holdShB, mycSh, ↓reduceIte, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, reduceCtorEq, Ritem.RS.injEq, false_or] at h
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hs 40 (by omega) (by omega)
    · exact hs 48 (by omega) (by omega)
    · exact hs 56 (by omega) (by omega)
    · exact hs 72 (by omega) (by omega)
    · exact hs 80 (by omega) (by omega)
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · intro e; exact hl (Option.some.inj e)
    · intro e; cases e

theorem AxSpinT2a.endNoLk :
    AxSpinT2a.noLk
      ((ppSh q.c (S - 40) (S - 48) (S - 56) (S - 64) (cpuZ i + 120) (cpuZ i + 124)).map .it ++
        ((relTail (S - 8) (S - 16) (S - 24)).map .it ++ [Rxitem.it (.RS (p + 24) 4)])) := by
  have hs : ∀ d : Int, 1 ≤ d → d ≤ 80 → S - d ≠ AxSpinT2a.zLk := fun d h1 h2 =>
    Hpz _ (by unfold AxSpinT2a.privZ; omega)
  refine AxSpinT2a.noLkApp _ _ (AxSpinT2a.noLkMap _ ?_) (AxSpinT2a.noLkApp _ _
    (AxSpinT2a.noLkMap _ ?_) (AxSpinT2a.noLkMap [Ritem.RS (p + 24) 4] ?_))
  · intro pa n h
    cases hc : q.c <;>
    simp only [hc, ppSh, ppHead, ppMid, ppTail, mycSh, ↓reduceIte, Bool.false_eq_true,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      reduceCtorEq, Ritem.RS.injEq, false_or] at h <;>
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
    first
      | exact hs 40 (by omega) (by omega) | exact hs 48 (by omega) (by omega)
      | exact hs 56 (by omega) (by omega) | exact hs 64 (by omega) (by omega)
      | exact Hpz _ (by unfold AxSpinT2a.privZ; omega)
  · intro pa n h
    simp only [relTail, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at h
  · intro pa n h
    simp only [List.mem_cons, List.not_mem_nil, or_false, Ritem.RS.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Hpz _ (by unfold AxSpinT2a.privZ; omega)

variable (HF : allocFull row q i S p)
include HF

/-- AxSpinRl3's `Hone` window, DERIVED FROM THE SHAPE (given that hart `i`'s private bytes miss
the lock word, `AxSpinT2a.privNeLk` from `T2LayHyp`): after the claim, the only lock-word write
of the row is release's `sw zero,0(s1)` at `relKw (t2KRl q)`. -/
theorem allocRelWin (k' : Nat) (lb : Lbl) (rl : Bool) (n : Nat) :
    t2KA q < k' → row[k']? = some lb → aidentWr (aident lb) = some (rl, AxSpinT2a.zLk, n) →
    k' = relKw (t2KRl q) := by
  intro hk Hk Hw
  obtain ⟨x, Hx, Hs⟩ := allocItem HF k' lb Hk
  have Hwa := AxSpinT2a.xWaOf x lb rl _ n Hs Hw
  rw [AxSpinT2a.segSplit] at Hx
  have Hpre : ((aqHead (S - 8) (S - 16) (S - 24)).map Rxitem.it ++
        ((poSh q.b (S - 40) (S - 48) (S - 56) (S - 72) (S - 80) (cpuZ i + 120)
          (cpuZ i + 124)).map Rxitem.it ++
        ((holdShB q.hb AxSpinT2a.zLk (AxSpinT2a.zLk + 16) (S - 40) (S - 48) (S - 56) (S - 72)
          (S - 80)).map Rxitem.it ++
        List.replicate (q.n + 1) (Rxitem.RM true false AxSpinT2a.zLk 4)))).length =
      t2KA q + 1 := by
    simp only [List.length_append, List.length_map, AxSpinT2a.aqHeadLen, AxSpinT2a.poShLen,
      holdShBLen, List.length_replicate, t2KA, aqKA, aqKh, aqKp, holdLen]
    omega
  rw [List.getElem?_append_right (by omega), Hpre] at Hx
  have Hmid := AxSpinT2a.midNoLk (i := i) Hpz
  have Hend := AxSpinT2a.endNoLk (q := q) Hpz
  have hml : ((aqTail (S - 40) (S - 48) (AxSpinT2a.zLk + 16) (S - 8) (S - 16) (S - 24)).map
        Rxitem.it ++
        ((apBodySh AxSpinT2a.zNp (p + 48)).map Rxitem.it ++
        ((relHead (S - 8) (S - 16) (S - 24)).map Rxitem.it ++
        ((holdShB true AxSpinT2a.zLk (AxSpinT2a.zLk + 16) (S - 40) (S - 48) (S - 56) (S - 72)
          (S - 80)).map Rxitem.it ++
        [Rxitem.it (.RS (AxSpinT2a.zLk + 16) 8), .RB true true false true])))).length = 92 := by
    simp only [List.length_append, List.length_map, aqTailLen, AxSpinAp7.apBodyShLen, relHead,
      holdShBLen, holdLen, ↓reduceIte, List.length_cons, List.length_nil]
  have hkw : relKw (t2KRl q) = t2KA q + 1 + 92 := by
    simp only [relKw, t2KRl, t2KBd, t2KMy, t2KA, aqKm, aqKA]; omega
  rcases Nat.lt_or_ge (k' - (t2KA q + 1)) 92 with h1 | h1
  · rw [List.getElem?_append_left (by omega)] at Hx
    exact absurd Hwa (Hmid x (List.mem_of_getElem? Hx))
  rw [List.getElem?_append_right (by omega), hml] at Hx
  rcases Nat.lt_or_ge 0 (k' - (t2KA q + 1) - 92) with h2 | h2
  · rw [show k' - (t2KA q + 1) - 92 = (k' - (t2KA q + 1) - 92 - 1) + 1 by omega,
      List.getElem?_cons_succ] at Hx
    exact absurd Hwa (Hend x (List.mem_of_getElem? Hx))
  · omega

/-- AxSpinRl3 `XxSwRelRel`'s `Hone` verbatim (anchor = release's `sd zero,16(s1)`), at a layout
whose lock word is `pid_lock` (`hL`; `rfl` for `xlayXv6`). -/
theorem allocRelWinC (L : Xlay) (hL : L.xlLk = AxSpinT2a.zLk) (k' : Nat) (lb : Lbl) (rl : Bool)
    (n : Nat) :
    relKc (t2KRl q) < k' → row[k']? = some lb → aidentWr (aident lb) = some (rl, L.xlLk, n) →
    k' = relKw (t2KRl q) := by
  intro hk Hk Hw
  rw [hL] at Hw
  refine allocRelWin Hpz HF k' lb rl n ?_ Hk Hw
  have := AxSpinT2a.kAlt q
  simp only [relKc, t2KRl] at hk
  omega

end relwin

/-! # 6. The entry condition -/

/-- The pages hart `i`'s segment touches (warm TLB at entry). -/
def t2Touch (i : Agent) (S p : Int) (va : BitVec 64) : Prop :=
  (0x80000000 ≤ (va.toNat : Int) ∧ (va.toNat : Int) < 0x80002000) ∨
  (AxSpinT2a.zNp ≤ va.toNat ∧ (va.toNat : Int) < AxSpinT2a.zNp + 4) ∨
  (AxSpinT2a.zLk ≤ va.toNat ∧ (va.toNat : Int) < AxSpinT2a.zLk + 24) ∨
  (cpuZ i + 120 ≤ va.toNat ∧ (va.toNat : Int) < cpuZ i + 128) ∨
  ((KernelSyms.«proc» : Int) ≤ va.toNat ∧ (va.toNat : Int) < (KernelSyms.«proc» : Int) + 376 * 64) ∨
  (S - 80 ≤ va.toNat ∧ (va.toNat : Int) < S) ∨
  (p + 24 ≤ va.toNat ∧ (va.toNat : Int) < p + 28) ∨ (p + 48 ≤ va.toNat ∧ (va.toNat : Int) < p + 52)

/-- THE ENTRY STATE of hart `i` at allocproc + 0x38: row position 0, S-mode / SIE = 0, `sp = S`,
`s1 = p`, `tp = hartId (cpuOf i)`, warm TLB on every touched page. -/
def entryOk (T : PTree) (satp0 : BitVec 64) (i : Agent) (S p : Int) (s : Athread) : Prop :=
  ∃ (rs : RegFile) (ib : Ibch), s = ⟨.PHart (cpuOf i) (.pure ()) rs none ib, 0⟩ ∧
    ctrlOkSW T satp0 rs ∧ rs .PC = pca 0x38 ∧
    gprVal rs 2#5 = BitVec.ofInt 64 S ∧ gprVal rs 9#5 = BitVec.ofInt 64 p ∧
    gprVal rs 4#5 = hartId (cpuOf i) ∧ ∀ va, t2Touch i S p va → hitW rs va

theorem entryK0 (T : PTree) (satp0 : BitVec 64) (i : Agent) (S p : Int) (s : Athread) :
    entryOk T satp0 i S p s → s.atK = 0 := by
  rintro ⟨rs, ib, rfl, -⟩
  rfl

theorem t2TouchText (i : Agent) (S p : Int) (va : BitVec 64) :
    0x80000000 ≤ va.toNat → va.toNat < 0x80002000 → t2Touch i S p va := by
  intro h1 h2
  exact .inl ⟨by omega, by omega⟩

theorem t2TouchNp (i : Agent) (S p : Int) : t2Touch i S p vaNp := by
  refine .inr (.inl ?_)
  rw [vaNpNextpid]
  simp only [AxSpinT2a.zNp, BitVec.toNat_ofNat]
  decide

/-- the `j`-th scan address as a number. -/
theorem AxSpinT2a.scanVaNat (j : Nat) (hj : j < 64) :
    (AxSpinAp9.scanVa j).toNat = 0x80012930 + 376 * j + 48 := by
  have h48 : sign_extend (m := 64) 48#12 = BitVec.ofNat 64 48 := by decide
  unfold AxSpinAp9.scanVa AxSpinAp9.a5j
  rw [h48, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hp : KernelSyms.«proc» = 0x80012930 := rfl
  rw [hp, Nat.mod_eq_of_lt (show 0x80012930 + 376 * j < 18446744073709551616 by omega),
    Nat.mod_eq_of_lt (show 48 < 18446744073709551616 by decide)]
  exact Nat.mod_eq_of_lt (by omega)

theorem t2TouchScan (i : Agent) (S p : Int) (j : Nat) (hj : j < 64) :
    t2Touch i S p (AxSpinAp9.scanVa j) := by
  refine .inr (.inr (.inr (.inr (.inl ?_))))
  rw [AxSpinT2a.scanVaNat j hj]
  obtain ⟨-, -, v3, -, -, -, -, -⟩ := AxSpinT2a.symV
  rw [v3]
  omega

theorem t2TouchStk (i : Agent) (S p : Int) (va : BitVec 64) :
    S - 80 ≤ va.toNat → (va.toNat : Int) < S → t2Touch i S p va := by
  intro h1 h2
  exact .inr (.inr (.inr (.inr (.inr (.inl ⟨h1, h2⟩)))))

end Weak
