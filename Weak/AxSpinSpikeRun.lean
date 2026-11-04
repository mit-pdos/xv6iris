/-
Weak: Phase 0.5 SIZE SPIKE, part 3 -- a concrete S-mode run of real xv6 code, evaluated by the
KERNEL (Rocq `iris/AxSpinSpikeRun.v` @ xxvzwolszwmp).

Rocq header (verbatim, Rocq vocabulary):

    MEASUREMENT ONLY.  Self-contained (only [RiscvLang]/the Sail model): the
    S-mode state, Sv39 page table and the memory-event tracer are copies of
    [AxSmodeProbe]'s [s_regs]/[s_bytes]/[mtr] (not imported: that file's
    dependency cone is heavy), extended to iterate [riscv_step] and to carry
    the state.  The function run is [mycpu] (14 instructions, real bytes
    from KernelInstrs, at its real address 0x800018e6 -- page 0x80001, which
    the probe's L0[1] maps), from a cold TLB, tp = 1, ra = 0x80000000,
    sp = 0x80001000.

    RESULTS: [obs 14] = (pc 0x80000000 = ra, a0 = 0x800123f8 = cpus[1],
    per-step event counts [4;5;2;1;1;1;1;1;1;1;2;2;1;1] = 24 events incl.
    2 cold walks) in 0.066 s -- about 5 ms per S-mode instruction, so a whole
    allocpid hart (about 213 instructions) is about 1 s.  Step evaluation is NOT a
    bottleneck.

    DRIVER GAP ([AxEpiRun.drive]/[node_step]): ... (the Rocq driver; not ported here).

WHAT THIS FILE PROVES (Lean).  The definitions (state, page table, tracer, iterated runner,
observables) and, in place of Rocq's two `Time Eval vm_compute` commands, two THEOREMS pinning
the kernel's evaluation of the same observables (`obs_one`, `obs_fourteen`), closed by
`decide +kernel` on the real Lean Sail model (`MachCSL.riscvStep false` =
`Functions.try_step 0 false`, the `-D SYMBOLIC` regeneration), plus the check that the run's
code bytes are the kernel image's (`mycpuInstrs_text`).  `#kernel_eval` (below) is the
`Eval vm_compute` analogue: it prints the kernel's normal form of a closed term and its time.

LEAN RESULTS (this tree's kernel build, `Xv6/KernelImage.lean`): `obs 14` =
(pc 0x80000000 = ra, a0 = 0x800125b0 = cpus + 1 * 128, per-step GRAPH memory-event counts
[3, 4, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0] = 10 events: the 2 cold walks (6 reads), 2 frame
stores, 2 frame loads).  O2 STAGE C (`notes/weak-port-o2-stageC.md` §B4, item 20): a fetch is
an administrative label, not a graph event, so the tracer CLASSIFIES each read by its access
kind (`akIfetch`: kind 2 = fetch) and `obs` counts the non-fetch events only; with the 16
fetch reads all accesses are [4, 5, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1] = 26 (the Stage B
`obs`), and `obsEv_fourteen` lists all 26, fetches as kind 2.  The Lean model fetches a 4-byte-aligned pc as ONE 4-byte read and a pc at 2 mod 4
as a 2-byte read (a second one for a full word): the two extra events against Rocq are the
4-byte `auipc`/`addi` pair, which sit at 2 mod 4 in this build (0x8000196a/0x8000196e) and at
0 mod 4 in Rocq's.  Reads are kind 0, except the fetches (the reads at the pc, `AK_ifetch` in the
Lean model), kind 2.  Kernel evaluation times (`#kernel_eval`, VM, c4d): `obs 1` 0.30 s, `obs 14` 1.6 s
(about 0.12 s an S-mode instruction, against Rocq `vm_compute`'s 5 ms); the theorems' kernel
checks: `obs_one` 0.23 s, `obs_fourteen` 1.8 s, `obsEv_fourteen` 3.3 s.

Deviations from Rocq:
- The kernel image is THIS tree's (`MachCSL.KernelSyms`, `Xv6.Kernel.textTree`): `mycpu` is at
  0x8000195c (Rocq's build: 0x800018e6), `cpus` at 0x80012530; the 34 code bytes (14
  instructions and the next function's first halfword, as in Rocq) are generated from
  `mycpuInstrs`, which `mycpuInstrs_text` checks against the kernel text.  Same page (0x80001),
  same instruction sequence.
- Integers are `Nat` (Rocq `Z`; every value here is non-negative).  `w64` is `BitVec.ofNat 64`.
- The memory is a function `PAddr → Option (BitVec 8)` (`TMem`), built from the byte list by
  `memOfList` (Rocq `list_to_map` into a `gmap`); `TMem.set` is Rocq's `<[a := b]>`.
- Rocq `init_regstate` -> `spikeRegs0`, the all-default register file (every register at its
  type's `default`), the same as `vtest-lean`'s `zeroRegs` (not importable from here).
- The tracer's failure codes: 1 device read, 2 unmapped read bytes, 3 device write (as Rocq);
  4 a model failure (`.error`, Rocq `GenericFail`); 5 anything else (Rocq's wildcard), which
  in Lean also covers a write request with no value, `choose`, and the legacy RAM events.  A
  memory read is answered `.Ok (w, none)` and a write `.Ok (some true)`, as `MachCSL.evStep`
  answers them (Rocq answered `inl None` to a write).  The `-D SYMBOLIC` announce events are
  skipped, as Rocq's.
- `obs`/`obsEv` results are `Sum`s of tuples (Rocq `+`, `*`).
- O2 Stage C: the event kind 2 (fetch, by `akIfetch` of the access kind; Rocq: every read is
  kind 0) and `obs` counting graph events only (Rocq: all events).

Rocq -> Lean names (inside `namespace Weak`; `Q.` = `AxSpinSpikeRun.`, the file qualifier for
the names Rocq defines in more than one file, `notes/weak-port-dupnames.json`, and for this
file's own helpers): `w64` -> `Q.w64`; `s_root/s_l1/s_l0` -> `Q.sRoot/sL1/sL0`; `pte_nl/pte_leaf`
-> `Q.pteNl/pteLeaf`; `s_satp` -> `Q.sSatp`; `s_sp` -> `Q.sSp`; `ra0` -> `ra0`; `dw_bytes` ->
`Q.dwBytes`; `mycpu_bytes` -> `mycpuBytes`; `r_bytes` -> `rBytes`; `r_mem` -> `rMem`;
`s_pmpcfg` -> `Q.sPmpcfg`; `s_pmpaddr` -> `Q.sPmpaddr`; `r_regs` -> `rRegs`; `r_at` -> `rAt`;
`mev` -> `Q.Mev`; `ttr` -> `ttr`; `trun` -> `Q.trun`; `pc_of` -> `Q.pcOf`; `a0_of` -> `a0Of`;
`obs` -> `obs`; `obs_ev` -> `obsEv`; `Time Eval vm_compute in obs 1` / `obs 14` ->
`Q.obs_one` / `Q.obs_fourteen` (theorems) and `#kernel_eval`.  New: `Q.kernelNf`,
`Q.mycpuInstrs`, `Q.mycpuInstrs_text`, `Q.kinstrBytes`, `Q.TMem`, `Q.TMem.set`, `Q.memOfList`,
`Q.spikeRegs0`, `Q.TState`, `Q.readBytes`, `Q.writeBytes`, `Q.obsEv_fourteen`.

Dropped: nothing.

HOW THE CLOSED COMPUTATION IS DONE (the recipe this file establishes):
- the whole cycle (`MachCSL.riscvStep false`) at a CLOSED state is evaluated by the KERNEL:
  `decide +kernel` on `obs n = v` (a `DecidableEq` result type).  The model's `decode` is
  `noncomputable` (no compiled code), its `hartSupports`/`currentlyEnabled` are well-founded
  definitions and the elaborator's `rfl`/`decide` refuse or crawl on both; the kernel unfolds
  both.  Every value the model branches on must be closed (the `URunRW` finding): here the
  whole state is.  The tracer is structural on `FreeM` (no fuel).
- the value to state was read off `#kernel_eval obs 14` (kernel whnf, recursively on the
  constructor arguments), then pinned by the theorem.
-/
import MachCSL.Lang
import Xv6.KernelTree

namespace Weak

open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open MachCSL

/-! ## 0. `#kernel_eval`: Rocq's `Eval vm_compute in`, by the kernel -/

open Lean Meta in
/-- The kernel's normal form of a closed term, down through constructor applications (proofs
and types left alone); `fuel` bounds the depth. -/
partial def AxSpinSpikeRun.kernelNf (fuel : Nat) (e : Lean.Expr) : MetaM Lean.Expr := do
  if fuel = 0 then return e
  let env ← getEnv
  let r := match Lean.Kernel.whnf env (← getLCtx) e with
    | .ok r => r
    | .error _ => e
  match r.getAppFn with
  | .const c _ =>
    if let some (.ctorInfo info) := env.find? c then
      let args := r.getAppArgs
      let args' ← (List.range args.size).toArray.mapM fun i => do
        let a := args[i]!
        if i < info.numParams then return a
        let ty ← (try some <$> inferType a catch _ => pure none)
        match ty with
        | some t =>
          if (← isProp t) || t.isSort then return a else AxSpinSpikeRun.kernelNf (fuel - 1) a
        | none => return a
      return mkAppN r.getAppFn args'
    else return r
  | _ => return r

open Lean Elab Command Term Meta in
/-- `#kernel_eval e`: print the kernel's evaluation of the closed term `e` and its time. -/
elab "#kernel_eval " t:term : command => liftTermElabM do
  let e ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let t0 ← IO.monoMsNow
  let r ← AxSpinSpikeRun.kernelNf 10000 e
  let t1 ← IO.monoMsNow
  logInfo m!"{r}\n(kernel evaluation: {t1 - t0} ms)"

/-! ## 1. The S-mode state ([AxSmodeProbe] §1, plus mycpu's bytes)

The names Rocq defines in more than one file (`notes/weak-port-dupnames.json`), and this file's
own helpers, are file-qualified (`AxSpinSpikeRun.*`). -/

/-- Rocq `w64`. -/
def AxSpinSpikeRun.w64 (z : Nat) : BitVec 64 := BitVec.ofNat 64 z

def AxSpinSpikeRun.sRoot : Nat := 0x80010
def AxSpinSpikeRun.sL1 : Nat := 0x80011
def AxSpinSpikeRun.sL0 : Nat := 0x80012
/-- A non-leaf PTE (V). -/
def AxSpinSpikeRun.pteNl (ppn : Nat) : Nat := (ppn <<< 10) ||| 0x01
/-- A leaf PTE (V R W X A D). -/
def AxSpinSpikeRun.pteLeaf (ppn : Nat) : Nat := (ppn <<< 10) ||| 0xCF
/-- Sv39, root `sRoot`. -/
def AxSpinSpikeRun.sSatp : Nat := (8 <<< 60) ||| AxSpinSpikeRun.sRoot
def AxSpinSpikeRun.sSp : Nat := 0x80001000
def ra0 : Nat := 0x80000000

/-- The 8 little-endian bytes of the doubleword `v` at `a`. -/
def AxSpinSpikeRun.dwBytes (a v : Nat) : List (Nat × Nat) :=
  (List.range 8).map fun j => (a + j, (v >>> (8 * j)) &&& 0xFF)

/-- `mycpu` as it sits in this tree's kernel text: its 14 instructions and the next function's
first halfword (Rocq's 34 bytes). -/
def AxSpinSpikeRun.mycpuInstrs : List Xv6.Kernel.KInstr :=
  [⟨0x8000195c, 2, 0x1141⟩, ⟨0x8000195e, 2, 0xe406⟩, ⟨0x80001960, 2, 0xe022⟩,
   ⟨0x80001962, 2, 0x0800⟩, ⟨0x80001964, 2, 0x8792⟩, ⟨0x80001966, 2, 0x2781⟩,
   ⟨0x80001968, 2, 0x079e⟩, ⟨0x8000196a, 4, 0x00011517⟩, ⟨0x8000196e, 4, 0xbc650513⟩,
   ⟨0x80001972, 2, 0x953e⟩, ⟨0x80001974, 2, 0x60a2⟩, ⟨0x80001976, 2, 0x6402⟩,
   ⟨0x80001978, 2, 0x0141⟩, ⟨0x8000197a, 2, 0x8082⟩, ⟨0x8000197c, 2, 0x1101⟩]

/-- The run's code is the kernel's, at the kernel's `mycpu`. -/
theorem AxSpinSpikeRun.mycpuInstrs_text :
    (AxSpinSpikeRun.mycpuInstrs.all fun k => Xv6.Kernel.textTree.find? k.addr == some k) = true ∧
    (AxSpinSpikeRun.mycpuInstrs.head?.map (·.addr)) = some KernelSyms.«mycpu» := by
  decide +kernel

/-- The bytes of one instruction, little-endian. -/
def AxSpinSpikeRun.kinstrBytes (k : Xv6.Kernel.KInstr) : List (Nat × Nat) :=
  (List.range k.width).map fun j => (k.addr + j, (k.enc >>> (8 * j)) &&& 0xFF)

/-- Rocq `mycpu_bytes`. -/
def mycpuBytes : List (Nat × Nat) := AxSpinSpikeRun.mycpuInstrs.flatMap AxSpinSpikeRun.kinstrBytes

/-- Rocq `r_bytes`: the code and the three-level table mapping pages 0x80000 and 0x80001. -/
def rBytes : List (Nat × Nat) :=
  mycpuBytes ++
  AxSpinSpikeRun.dwBytes (AxSpinSpikeRun.sRoot * 4096 + 2 * 8) (AxSpinSpikeRun.pteNl AxSpinSpikeRun.sL1) ++
  AxSpinSpikeRun.dwBytes (AxSpinSpikeRun.sL1 * 4096 + 0 * 8) (AxSpinSpikeRun.pteNl AxSpinSpikeRun.sL0) ++
  AxSpinSpikeRun.dwBytes (AxSpinSpikeRun.sL0 * 4096 + 0 * 8) (AxSpinSpikeRun.pteLeaf 0x80000) ++
  AxSpinSpikeRun.dwBytes (AxSpinSpikeRun.sL0 * 4096 + 1 * 8) (AxSpinSpikeRun.pteLeaf 0x80001)

/-- The tracer's memory: a partial byte map. -/
abbrev AxSpinSpikeRun.TMem := PAddr → Option (BitVec 8)

/-- Rocq `<[a := b]> m`. -/
def AxSpinSpikeRun.TMem.set (m : AxSpinSpikeRun.TMem) (a : PAddr) (b : BitVec 8) :
    AxSpinSpikeRun.TMem :=
  fun a' => if a' = a then some b else m a'

/-- Rocq `list_to_map` (the first binding of an address wins, as `list_to_map` keeps the
last; the lists here have no duplicates). -/
def AxSpinSpikeRun.memOfList (l : List (Nat × Nat)) : AxSpinSpikeRun.TMem := fun a =>
  (l.find? fun p => AxSpinSpikeRun.w64 p.1 == a).map fun p => BitVec.ofNat 8 p.2

/-- Rocq `r_mem`. -/
def rMem : AxSpinSpikeRun.TMem := AxSpinSpikeRun.memOfList rBytes

/-- The all-default register file (Rocq `init_regstate`). -/
def AxSpinSpikeRun.spikeRegs0 : RegFile := fun r => by
  cases r <;> exact default

/-- Rocq `s_pmpcfg`: entry 0 = TOR, R/W/X. -/
def AxSpinSpikeRun.sPmpcfg : Vector (BitVec 8) 64 :=
  (AxSpinSpikeRun.spikeRegs0 .pmpcfg_n).set 0 0x0F#8
/-- Rocq `s_pmpaddr`: entry 0 covers [0, 0x88000000). -/
def AxSpinSpikeRun.sPmpaddr : Vector (BitVec 64) 64 :=
  (AxSpinSpikeRun.spikeRegs0 .pmpaddr_n).set 0 (AxSpinSpikeRun.w64 0x22000000)

/-- Rocq `r_regs pc`: S-mode at `pc`, Sv39 on, PMP entry 0, ra / sp / tp. -/
def rRegs (pc : Nat) : RegFile :=
  let w64 := AxSpinSpikeRun.w64
  let rs := AxSpinSpikeRun.spikeRegs0
  let rs := rs.set .PC (w64 pc)
  let rs := rs.set .nextPC (w64 pc)
  let rs := rs.set .cur_privilege .Supervisor
  let rs := rs.set .hart_state (.HART_ACTIVE ())
  let rs := rs.set .misa (w64 0x8000000000141105)
  let rs := rs.set .mstatus (w64 0xA00000000)
  let rs := rs.set .mseccfg (w64 0)
  let rs := rs.set .menvcfg (w64 0xA000000000000000)
  let rs := rs.set .mie (w64 0)
  let rs := rs.set .mideleg (w64 0x222)
  let rs := rs.set .medeleg (w64 0xB109)
  let rs := rs.set .satp (w64 AxSpinSpikeRun.sSatp)
  let rs := rs.set .pmpcfg_n AxSpinSpikeRun.sPmpcfg
  let rs := rs.set .pmpaddr_n AxSpinSpikeRun.sPmpaddr
  let rs := rs.set .htif_tohost_base none
  let rs := rs.set .pma_regions bootPMA
  let rs := rs.set .elp 0#1
  let rs := rs.set .x1 (w64 ra0)
  let rs := rs.set .x2 (w64 AxSpinSpikeRun.sSp)
  let rs := rs.set .x4 (w64 1)
  rs

/-- The tracer's state: one hart's registers and the memory (Rocq `RiscvLang.mstate`, whose
device component the tracer never touches). -/
structure AxSpinSpikeRun.TState where
  regs : RegFile
  mem : AxSpinSpikeRun.TMem

/-- Rocq `r_at`. -/
def rAt : AxSpinSpikeRun.TState := ⟨rRegs KernelSyms.«mycpu», rMem⟩

/-! ## 2. The tracer, carrying the state ([AxSmodeProbe.mtr] + final state) -/

/-- A memory event: (kind, width, pa); kind 0 a data or walker read, 1 a write, 2 an
instruction fetch (Lean-only class, O2 Stage C: a fetch is ADMINISTRATIVE, not a graph event;
told apart by its access kind `AK_ifetch`). -/
abbrev AxSpinSpikeRun.Mev := Nat × Nat × Nat

/-- The `n` bytes at `pa`, little-endian, if all are mapped (Rocq `read_bytes`). -/
def AxSpinSpikeRun.readBytes (m : AxSpinSpikeRun.TMem) (pa : PAddr) :
    (n : Nat) → Option (BitVec (8 * n))
  | 0 => some 0#0
  | n + 1 =>
    match AxSpinSpikeRun.readBytes m pa n, m (pa + BitVec.ofNat 64 n) with
    | some w, some b => some ((b ++ w).cast (by omega))
    | _, _ => none

/-- Write the `n` bytes of `w` at `pa` (Rocq `write_bytes`). -/
def AxSpinSpikeRun.writeBytes (m : AxSpinSpikeRun.TMem) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) :
    AxSpinSpikeRun.TMem :=
  (List.range n).foldl (fun m j => m.set (pa + BitVec.ofNat 64 j) (BitVec.extractLsb' (8 * j) 8 w)) m

/-- Rocq `ttr`: run a Sail computation over the state, recording the memory events; `inl`
(events, final state) or `inr` (failure code, events so far). -/
def ttr {X : Type} : SailM X → AxSpinSpikeRun.TState → List AxSpinSpikeRun.Mev →
    (List AxSpinSpikeRun.Mev × AxSpinSpikeRun.TState) ⊕ (Nat × List AxSpinSpikeRun.Mev)
  | .pure _, t, acc => .inl (acc.reverse, t)
  | .impure (.error _) _, _, acc => .inr (4, acc.reverse)
  | .impure (.ok o) k, t, acc =>
    match o, k with
    | .regRead r, k => ttr (k (t.regs r)) t acc
    | .regWrite r v, k => ttr (k PUnit.unit) ⟨t.regs.set r v, t.mem⟩ acc
    | .memRead n _ req, k =>
      let e : AxSpinSpikeRun.Mev := (if akIfetch req.access_kind then 2 else 0, n, req.pa.toNat)
      if devAddr req.pa then .inr (1, (e :: acc).reverse)
      else match AxSpinSpikeRun.readBytes t.mem req.pa n with
        | some w => ttr (k (.Ok (w, none))) t (e :: acc)
        | none => .inr (2, (e :: acc).reverse)
    | .memWrite n _ req, k =>
      let e : AxSpinSpikeRun.Mev := (1, n, req.pa.toNat)
      if devAddr req.pa then .inr (3, (e :: acc).reverse)
      else match req.value with
        | some w =>
          ttr (k (.Ok (some true))) ⟨t.regs, AxSpinSpikeRun.writeBytes t.mem req.pa n w⟩ (e :: acc)
        | none => .inr (5, acc.reverse)
    | .instrAnnounce _ _, k => ttr (k ()) t acc
    | .branchAnnounce _ _, k => ttr (k ()) t acc
    | .barrier _, k => ttr (k ()) t acc
    | .cacheOp _, k => ttr (k ()) t acc
    | .tlbi _, k => ttr (k ()) t acc
    | .takeException _, k => ttr (k ()) t acc
    | .returnException _, k => ttr (k ()) t acc
    | .translationStart _, k => ttr (k ()) t acc
    | .translationEnd _, k => ttr (k ()) t acc
    | .cycleCount, k => ttr (k ()) t acc
    | .message _, k => ttr (k ()) t acc
    | .getCycleCount, k => ttr (k (0 : Nat)) t acc
    | _, _ => .inr (5, acc.reverse)

/-- Rocq `trun`: `n` instruction steps (`tick := false`). -/
noncomputable def AxSpinSpikeRun.trun : Nat → AxSpinSpikeRun.TState → List (List AxSpinSpikeRun.Mev) →
    (List (List AxSpinSpikeRun.Mev) × AxSpinSpikeRun.TState) ⊕ (Nat × List AxSpinSpikeRun.Mev)
  | 0, t, acc => .inl (acc.reverse, t)
  | n + 1, t, acc =>
    match ttr (riscvStep false) t [] with
    | .inl (evs, t') => AxSpinSpikeRun.trun n t' (evs :: acc)
    | .inr x => .inr x

/-- Rocq `pc_of`. -/
def AxSpinSpikeRun.pcOf (t : AxSpinSpikeRun.TState) : Nat := (t.regs .PC).toNat
/-- Rocq `a0_of`. -/
def a0Of (t : AxSpinSpikeRun.TState) : Nat := (t.regs .x10).toNat

/-- Observable: (final pc, a0, #graph memory events per step -- the fetches, kind 2, are
administrative and not counted, O2 Stage C). -/
noncomputable def obs (n : Nat) : (Nat × Nat × List Nat) ⊕ (Nat × List AxSpinSpikeRun.Mev) :=
  match AxSpinSpikeRun.trun n rAt [] with
  | .inl (evs, t) =>
    .inl (AxSpinSpikeRun.pcOf t, a0Of t,
      evs.map fun l => (l.filter fun e => !Nat.beq e.1 2).length)
  | .inr x => .inr x

/-- Observable: (final pc, the events of every step). -/
noncomputable def obsEv (n : Nat) :
    (Nat × List (List AxSpinSpikeRun.Mev)) ⊕ (Nat × List AxSpinSpikeRun.Mev) :=
  match AxSpinSpikeRun.trun n rAt [] with
  | .inl (evs, t) => .inl (AxSpinSpikeRun.pcOf t, evs)
  | .inr x => .inr x

#kernel_eval obs 1
#kernel_eval obs 14

/-! ## 3. The measurements, as theorems -/

set_option profiler true in
/-- One step (Rocq `Time Eval vm_compute in obs 1`): `c.addi sp,-16` through a cold walk. -/
theorem AxSpinSpikeRun.obs_one : obs 1 = .inl (0x8000195e, 0, [3]) := by
  decide +kernel

set_option profiler true in
/-- The whole of `mycpu` (Rocq `Time Eval vm_compute in obs 14`): back at `ra`, `a0 = cpus[1]`. -/
theorem AxSpinSpikeRun.obs_fourteen :
    obs 14 = .inl (ra0, KernelSyms.«cpus» + 1 * 128, [3, 4, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]) := by
  decide +kernel

set_option profiler true in
/-- The events of every step of the run (walk reads at the three table levels, fetches at the
pc -- kind 2 --, the two frame stores and the two frame loads). -/
theorem AxSpinSpikeRun.obsEv_fourteen :
    obsEv 14 = .inl (ra0,
      [[(0, 8, 0x80010010), (0, 8, 0x80011000), (0, 8, 0x80012008), (2, 4, 0x8000195c)],
       [(2, 2, 0x8000195e), (0, 8, 0x80010010), (0, 8, 0x80011000), (0, 8, 0x80012000),
        (1, 8, 0x80000ff8)],
       [(2, 4, 0x80001960), (1, 8, 0x80000ff0)], [(2, 2, 0x80001962)], [(2, 4, 0x80001964)],
       [(2, 2, 0x80001966)], [(2, 4, 0x80001968)], [(2, 2, 0x8000196a), (2, 2, 0x8000196c)],
       [(2, 2, 0x8000196e), (2, 2, 0x80001970)], [(2, 2, 0x80001972)],
       [(2, 4, 0x80001974), (0, 8, 0x80000ff8)], [(2, 2, 0x80001976), (0, 8, 0x80000ff0)],
       [(2, 4, 0x80001978)], [(2, 2, 0x8000197a)]]) := by
  decide +kernel

end Weak
