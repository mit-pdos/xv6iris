/-
Weak: **THE CERTIFICATE TOOLKIT, demonstration** — two harts running REAL xv6 S-mode code on one
spinlock, turned into a tagged graph whose consistency, ctrl closure and run premise are
discharged by the GENERIC lemmas of `AxScRun`/`AxScRun2` plus closed kernel computation.

Rocq: `iris/AxScRun3.v` @ xxvzwolszwmp.

## What this file proves

THE INSTANCE (S-mode, Sv39, cold TLBs; state/page table of `AxSpinSpikeRun`; text bytes = this
tree's kernel text at its real addresses): hart 0 ("A", releaser) runs `release+0x16`
(`fence rw,w`) and `release+0x1a` (`sw zero,0(s1)`); hart 1 ("B", spinner) runs
`acquire+0x1a..0x22` twice (`c.mv a5,a4; amoswap.w.aq a5,a5,(s1); sext.w a5,a5; c.bnez a5`):
one FAILED iteration, then the SUCCESSFUL one.  `s1 = lk` (0x80001f00, in the mapped data page),
`a4 = 1`, lock initially 1.  SC schedule B×4, A×2, B×4.  (Kernel layout checked: in this tree
`acquire` = 0x80000c58, `release` = 0x80000ce0, and the offsets/encodings of the six
instructions are Rocq's.)

PIPELINE: `jrun` (the untrusted joint SC tracer, §1) emits the rows and the interleaving;
`graphOfSc` builds `g0`; `drive2` re-runs each hart on the graph's row and records its emission;
`gD` = `graphOfSc` with those emissions.  DISCHARGED (§3): `gDCatT`, `gDCtrlClosed`, `gDRun`
(both harts, `tierAAstep` form, to the row end), `gDVals` (the bridge premise).  NOT VACUOUS
(§4): `gDAmoValues` (B's first RMW reads 1 from the IMAGE, ts 0; its second reads 0 from A's
store, write 2), `gDCtrlEdge` (the ctrl edge from the first RMW to the second, recorded by the
driver), `gDSizes`.  All closed checks by `decide +kernel` (whole file ≈30 s on the VM; each
check 3–5 s, dominated by re-evaluating the tracer and the drives).

## Deviations from Rocq

1. O2 STAGE C: an `akIfetch` read is ADMINISTRATIVE — the tracer answers it from the shared
   memory and emits NO label (Rocq emitted an `LLoad` row item for each fetch).  Hence the
   concrete numbers differ: rows A = 8 (3 walker reads, fence, 3 walker reads, store) and
   B = 8 (6 walker reads, 2 RMWs), gmo 15, deps 10 (Rocq 12, 16, 27, 10); the ctrl edge is
   `(1,6) → (1,7)` (Rocq `(1,8) → (1,13)`).  The RMW read values/indices are Rocq's.
2. TYPES: the memory is `AxSpinSpikeRun.TMem` (Rocq `gmap pa (bv 8)`); write values are
   `Option` (`none` ⇒ failure); answers `.Ok (w, none)` / `.Ok (some true)`.  Addresses and
   byte values in the instance are `Nat` (Rocq `Z`), as in `AxSpinSpikeRun`; `imgMap` is a
   total `Int → Option` function (first binding wins; the byte list has no duplicates).
3. Rocq `GenericFail`/wildcard outcomes ⇒ `none` (as Rocq).
4. `textBytes` reads this tree's kernel text (`Xv6.Kernel.textTree`) through the Lean-only
   `AxScRun3.textByte` (Rocq `KernelInstrs.kernel_bytes`); `ems` is the computed definition
   (Rocq froze it with `Eval vm_compute`), so every check re-evaluates the drives.
5. `gDRun`: Lean `tierAAstep` takes no Iris instance, `T`, `ob_st0`, `ob_st_interp0`
   (`AxScRun2` deviation 4), so the inner quantifier is `∀ (N : Type) (nm : N)`.

**Rocq → Lean name map** (all file-qualified `AxScRun3.*`: short generic names; `sched`, `g0`,
`s0` are in the duplicated-name table).  `jmem` `Jmem`, `jtr` `jtr`, `jstate` `Jstate`, `jstep`
`jstep`, `jrun` `jrun`, `lk` `lk`, `pc_rel` `pcRel`, `pc_spin` `pcSpin`, `text_bytes`
`textBytes`, `init_bytes` `initBytes`, `img_map` `imgMap`, `img` `img`, `mem0` `mem0`, `regsA`
`regsA`, `regsB` `regsB`, `sched` `sched`, `jres` `jres`, `rows` `rows`, `il` `il`, `g0` `g0`,
`fuel` `fuel`, `drv` `drv`, `drv_ems` `drvEms`, `ems` `ems`, `gD` `gD`, `gD_inputs` `gDInputs`,
`gD_ctrl_ok` `gDCtrlOk`, `gD_cat_t` `gDCatT`, `gD_ctrl_closed` `gDCtrlClosed`, `drv_ok_b`
`drvOkB`, `drvA_ok` `drvAOk`, `drvB_ok` `drvBOk`, `s0` `s0`, `gD_run` `gDRun`, `gD_vals`
`gDVals`, `sizes` `sizes`, `gD_sizes` `gDSizes`, `amo_reads` `amoReads`, `gD_amo_values`
`gDAmoValues`, `gD_ctrl_edge` `gDCtrlEdge`.  Lean-only: `AxScRun3.textByte`.

**Dropped:** nothing (Rocq 40; Lean 40 + 1 Lean-only helper).  **Not ported:** `Print
Assumptions` (the lint's axiom check covers them), `Set Printing Depth`.
-/
import Weak.AxScRun2
import Weak.AxSpinSpikeRun

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D

/-! # 1. The joint SC tracer (untrusted generator) -/

/-- Rocq `jmem`. -/
abbrev AxScRun3.Jmem := AxSpinSpikeRun.TMem

/-- Rocq `jtr`: one instruction of one hart against the shared memory; the graph labels it
emits, in order.  An exclusive read is held pending and fused with the exclusive write into
ONE `LRmw`.  A fetch emits nothing (Stage C). -/
def AxScRun3.jtr {X : Type} : SailM X → RegFile → AxScRun3.Jmem →
    Option (Bool × Int × List (BitVec 8)) → List Lbl →
    Option (RegFile × AxScRun3.Jmem × List Lbl)
  | .pure _, rs, mem, _, acc => some (rs, mem, acc.reverse)
  | .impure (.error _) _, _, _, _, _ => none
  | .impure (.ok o) k, rs, mem, pend, acc =>
    match o, k with
    | .regRead r, k => AxScRun3.jtr (k (rs r)) rs mem pend acc
    | .regWrite r v, k => AxScRun3.jtr (k PUnit.unit) (rs.set r v) mem pend acc
    | .memRead n _ req, k =>
      if devAddr req.pa then none else
      match (List.range n).mapM (fun j => mem ((show PAddr from req.pa) + BitVec.ofNat 64 j)) with
      | some bs =>
        if (classify req.access_kind).akIfetch then
          AxScRun3.jtr (k (.Ok (wordOfBytes n bs, none))) rs mem pend acc
        else if (classify req.access_kind).akLatest then
          AxScRun3.jtr (k (.Ok (wordOfBytes n bs, none))) rs mem
            (some ((classify req.access_kind).akSync, paZ req.pa, bs)) acc
        else
          AxScRun3.jtr (k (.Ok (wordOfBytes n bs, none))) rs mem pend
            (Lbl.LLoad (classify req.access_kind).akSync (paZ req.pa) [] bs :: acc)
      | none => none
    | .memWrite n _ req, k =>
      if devAddr req.pa then none else
      match req.value with
      | none => none
      | some v =>
        let ws := WeakInterpProj.wbytes n v
        let mem' := AxSpinSpikeRun.writeBytes mem req.pa n v
        if (classify req.access_kind).akLatest then
          match pend with
          | some (aq, base, rvs) =>
            AxScRun3.jtr (k (.Ok (some true))) rs mem' none
              (Lbl.LRmw aq (classify req.access_kind).akSync base [] rvs ws .WCplain :: acc)
          | none => none
        else
          AxScRun3.jtr (k (.Ok (some true))) rs mem' pend
            (Lbl.LStore (classify req.access_kind).akSync (paZ req.pa) ws .WCplain :: acc)
    | .barrier b, k =>
      match ebarBits b with
      | (pr, pw, sr, sw) => AxScRun3.jtr (k ()) rs mem pend (Lbl.LFence pr pw sr sw :: acc)
    | .instrAnnounce _ _, k => AxScRun3.jtr (k ()) rs mem pend acc
    | .branchAnnounce _ _, k => AxScRun3.jtr (k ()) rs mem pend acc
    | .cacheOp _, k => AxScRun3.jtr (k ()) rs mem pend acc
    | .tlbi _, k => AxScRun3.jtr (k ()) rs mem pend acc
    | .takeException _, k => AxScRun3.jtr (k ()) rs mem pend acc
    | .returnException _, k => AxScRun3.jtr (k ()) rs mem pend acc
    | .translationStart _, k => AxScRun3.jtr (k ()) rs mem pend acc
    | .translationEnd _, k => AxScRun3.jtr (k ()) rs mem pend acc
    | .cycleCount, k => AxScRun3.jtr (k ()) rs mem pend acc
    | .message _, k => AxScRun3.jtr (k ()) rs mem pend acc
    | .getCycleCount, k => AxScRun3.jtr (k (0 : Nat)) rs mem pend acc
    | _, _ => none

/-- Rocq `jstate`: per-hart registers, the shared memory, per-hart rows, the interleaving. -/
abbrev AxScRun3.Jstate := List RegFile × AxScRun3.Jmem × List (List Lbl) × List Geid

/-- Rocq `jstep`: run ONE instruction (`riscvStep false`) of hart `h`; its memory labels join
the interleaving in order. -/
noncomputable def AxScRun3.jstep (s : AxScRun3.Jstate) (h : Nat) : Option AxScRun3.Jstate :=
  match s with
  | (rss, mem, rows, il) =>
    match rss[h]?, rows[h]? with
    | some rs, some row =>
      match AxScRun3.jtr (riscvStep false) rs mem none [] with
      | some (rs', mem', ls) =>
        let p0 := row.length
        some (rss.set h rs', mem', rows.set h (row ++ ls),
          il ++ ((List.range ls.length).zip ls).filterMap
            (fun jl => if lbIsMem jl.2 then some (h, p0 + jl.1) else none))
      | none => none
    | _, _ => none

/-- Rocq `jrun`. -/
noncomputable def AxScRun3.jrun (sched : List Nat) (s : AxScRun3.Jstate) :
    Option AxScRun3.Jstate :=
  sched.foldl (fun o h => o.bind fun s => AxScRun3.jstep s h) (some s)

/-! # 2. The instance -/

/-- Rocq `lk`: the lock word, in the mapped data page 0x80001. -/
def AxScRun3.lk : Nat := 0x80001f00
/-- Rocq `pc_rel`: `release + 0x16` (`fence rw,w`). -/
def AxScRun3.pcRel : Nat := KernelSyms.«release» + 0x16
/-- Rocq `pc_spin`: `acquire + 0x1a` (`c.mv a5,a4`). -/
def AxScRun3.pcSpin : Nat := KernelSyms.«acquire» + 0x1a

/-- (Lean-only) The kernel text byte at `a` (Rocq `KernelInstrs.kernel_bytes !! a`, `0` off the
text): the instruction starting at `a - j` (`j < 4`) that covers `a`. -/
def AxScRun3.textByte (a : Nat) : Nat :=
  ((List.range 4).findSome? fun j =>
    if j ≤ a then
      (Xv6.Kernel.textTree.find? (a - j)).bind fun k =>
        if j < k.width then some ((k.enc >>> (8 * j)) &&& 0xFF) else none
    else none).getD 0

/-- Rocq `text_bytes`: the real text bytes of acquire/release. -/
def AxScRun3.textBytes : List (Nat × Nat) :=
  (List.range 0xc8).map fun j => (KernelSyms.«acquire» + j, AxScRun3.textByte (KernelSyms.«acquire» + j))

/-- Rocq `init_bytes`. -/
def AxScRun3.initBytes : List (Nat × Nat) :=
  rBytes ++ (AxScRun3.textBytes ++
    [(AxScRun3.lk, 1), (AxScRun3.lk + 1, 0), (AxScRun3.lk + 2, 0), (AxScRun3.lk + 3, 0)])

/-- Rocq `img_map`. -/
def AxScRun3.imgMap (a : Int) : Option (BitVec 8) :=
  (AxScRun3.initBytes.find? fun p => decide ((p.1 : Int) = a)).map fun p => BitVec.ofNat 8 p.2

/-- Rocq `img`. -/
def AxScRun3.img (a : Int) : BitVec 8 := (AxScRun3.imgMap a).getD 0

/-- Rocq `mem0`. -/
def AxScRun3.mem0 : AxScRun3.Jmem := AxSpinSpikeRun.memOfList AxScRun3.initBytes

/-- Rocq `regsA`. -/
def AxScRun3.regsA : RegFile :=
  (rRegs AxScRun3.pcRel).set .x9 (AxSpinSpikeRun.w64 AxScRun3.lk)

/-- Rocq `regsB`. -/
def AxScRun3.regsB : RegFile :=
  ((rRegs AxScRun3.pcSpin).set .x9 (AxSpinSpikeRun.w64 AxScRun3.lk)).set .x14
    (AxSpinSpikeRun.w64 1)

/-- Rocq `sched`: B×4, A×2, B×4. -/
def AxScRun3.sched : List Nat := [1, 1, 1, 1, 0, 0, 1, 1, 1, 1]

/-- Rocq `jres`. -/
noncomputable def AxScRun3.jres : Option AxScRun3.Jstate :=
  AxScRun3.jrun AxScRun3.sched ([AxScRun3.regsA, AxScRun3.regsB], AxScRun3.mem0, [[], []], [])

/-- Rocq `rows`. -/
noncomputable def AxScRun3.rows : List (List Lbl) :=
  (AxScRun3.jres.map fun s => s.2.2.1).getD []
/-- Rocq `il`. -/
noncomputable def AxScRun3.il : List Geid := (AxScRun3.jres.map fun s => s.2.2.2).getD []

/-- Rocq `g0`: the graph before deps. -/
noncomputable def AxScRun3.g0 : GdexecT := graphOfSc AxScRun3.img AxScRun3.rows AxScRun3.il []

/-- Rocq `fuel`. -/
def AxScRun3.fuel : Nat := Nat.pow 10 5

/-- Rocq `drv`: the drive of hart `i` on the graph's row. -/
noncomputable def AxScRun3.drv (i : Nat) (rs : RegFile) :
    Option (SailM Unit × RegFile × Ibch × Nat × List Eitem) :=
  drive2 (fun a => some (AxScRun3.img a)) (rowOf AxScRun3.g0.gtG i)
    (rowOf AxScRun3.g0.gtG i).length AxScRun3.fuel (riscvStep false) rs ibNone 0

/-- Rocq `drv_ems`. -/
noncomputable def AxScRun3.drvEms (i : Nat) (rs : RegFile) : List Eitem :=
  ((AxScRun3.drv i rs).map fun r => r.2.2.2.2).getD []

/-- Rocq `ems`: the emissions the drives recorded. -/
noncomputable def AxScRun3.ems : List (List Eitem) :=
  [AxScRun3.drvEms 0 AxScRun3.regsA, AxScRun3.drvEms 1 AxScRun3.regsB]

/-- Rocq `gD`: THE CERTIFICATE GRAPH. -/
noncomputable def AxScRun3.gD : GdexecT :=
  graphOfSc AxScRun3.img AxScRun3.rows AxScRun3.il AxScRun3.ems

/-! # 3. The premises, discharged -/

theorem AxScRun3.gDInputs : scInputsOkB AxScRun3.rows AxScRun3.il AxScRun3.ems = true := by
  decide +kernel

theorem AxScRun3.gDCtrlOk : ctrlOkB AxScRun3.rows AxScRun3.ems = true := by
  decide +kernel

theorem AxScRun3.gDCatT : rvwmoCatConsistentT AxScRun3.gD :=
  graphOfScCatT _ _ _ _ AxScRun3.gDInputs

theorem AxScRun3.gDCtrlClosed : ctrlClosed AxScRun3.gD :=
  graphOfScCtrlClosed _ _ _ _ AxScRun3.gDCtrlOk

/-- Rocq `drv_ok_b`: the drive of hart `i` reaches its row end. -/
noncomputable def AxScRun3.drvOkB (i : Nat) (rs : RegFile) : Bool :=
  ((AxScRun3.drv i rs).map fun r => Nat.beq r.2.2.2.1 (rowOf AxScRun3.g0.gtG i).length).getD false

theorem AxScRun3.drvAOk : AxScRun3.drvOkB 0 AxScRun3.regsA = true := by decide +kernel
theorem AxScRun3.drvBOk : AxScRun3.drvOkB 1 AxScRun3.regsB = true := by decide +kernel

/-- Rocq `s0`. -/
def AxScRun3.s0 (i : Nat) : RegFile := if Nat.beq i 0 then AxScRun3.regsA else AxScRun3.regsB

/-- THE RUN PREMISE for both harts, in `AxSpinGate`'s `Hrun` form (Lean `tierAAstep`, deviation
4), at the certificate graph, ending at the row end. -/
theorem AxScRun3.gDRun (cpu : CPU) (i : Nat) (Hi : i ∈ [0, 1]) :
    ∃ n sN, sN.atK = (AxOpsem.grow (gtAdGd AxScRun3.gD) i).length ∧
      ∀ (N : Type) (nm : N),
        nsteps (tierAAstep (gtAdGd AxScRun3.gD) nm i) n
          (AxEpiRun.st cpu (riscvStep false) (AxScRun3.s0 i) ibNone 0) sN := by
  have Hok : AxScRun3.drvOkB i (AxScRun3.s0 i) = true := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hi
    rcases Hi with rfl | rfl
    · exact AxScRun3.drvAOk
    · exact AxScRun3.drvBOk
  unfold AxScRun3.drvOkB AxScRun3.drv at Hok
  cases Hd : drive2 (fun a => some (AxScRun3.img a)) (rowOf AxScRun3.g0.gtG i)
      (rowOf AxScRun3.g0.gtG i).length AxScRun3.fuel (riscvStep false) (AxScRun3.s0 i) ibNone 0 with
  | none => rw [Hd] at Hok; cases Hok
  | some r =>
    obtain ⟨m', rs', ib', k', its⟩ := r
    obtain ⟨Hk, n, Hr⟩ := runGraphOfSc AxScRun3.img AxScRun3.rows AxScRun3.il AxScRun3.ems i
      (rowOf AxScRun3.g0.gtG i).length AxScRun3.fuel _ _ _ m' rs' ib' k' its Hd
    exact ⟨n, AxEpiRun.st cpu m' rs' ib' k', Hk, fun N nm => Hr cpu N nm⟩

/-- The same premise through the INPUT rows (the tracer's), by the bridge. -/
theorem AxScRun3.gDVals : valsOkB AxScRun3.img AxScRun3.rows AxScRun3.il = true := by
  decide +kernel

/-! # 4. Not vacuous -/

/-- Rocq `sizes`: (hart-0 row, hart-1 row, gmo size, #deps). -/
noncomputable def AxScRun3.sizes : Nat × Nat × Nat × Nat :=
  ((rowOf AxScRun3.gD.gtG 0).length, (rowOf AxScRun3.gD.gtG 1).length,
    AxScRun3.gD.gtG.gxGmo.length, AxScRun3.gD.gtDeps.length)

/-- A = 3 walker reads (text page) + fence + 3 walker reads (data page) + store; B = 4 + 4
instructions, cold walks for the text and the lock page, 2 RMWs (Stage C: no fetch items). -/
theorem AxScRun3.gDSizes : AxScRun3.sizes = (8, 8, 15, 10) := by decide +kernel

/-- Rocq `amo_reads`: B's two RMWs, what they read (write indices, values). -/
noncomputable def AxScRun3.amoReads : List (List Nat × List (BitVec 8)) :=
  (rowOf AxScRun3.gD.gtG 1).filterMap fun l =>
    match l with
    | .LRmw _ _ _ ts rvs _ _ => some (ts, rvs)
    | _ => none

/-- The first RMW reads the IMAGE (ts 0: lock = 1, held) — the failed iteration; the second
reads A's release store (write 2; write 1 is B's own first RMW) — 0, acquired. -/
theorem AxScRun3.gDAmoValues :
    AxScRun3.amoReads = [([0, 0, 0, 0], [1#8, 0#8, 0#8, 0#8]), ([2, 2, 2, 2], [0#8, 0#8, 0#8, 0#8])] := by
  decide +kernel

/-- The ctrl edge of the spin loop: the first RMW's value feeds c.bnez, so the second RMW (a
store) is ctrl-dependent on it — recorded by the driver's emission. -/
theorem AxScRun3.gDCtrlEdge : (((1, 6), (1, 7)), Dtag.DTctrl) ∈ AxScRun3.gD.gtDeps := by
  decide +kernel

end Weak
