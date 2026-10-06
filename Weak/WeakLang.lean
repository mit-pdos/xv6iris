/-
Weak: **the weak-memory multi-hart language** (M1b).

Rocq: `iris/WeakLang.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance: the RVWMO-class analogue of the SC language
(`RiscvLang`'s `gstate`/`prim_step`/`riscv_lang`): the same execution contexts
(harts, devices, power) over the promise-free view machine of
`Weak/WeakMem.lean`, a hart stepped by `Weak.wrun` (one WHOLE `riscvStep` per
step) instead of the SC interpreter.  The global state replaces the flat byte map
by the ERA-INITIAL image `wgimg` plus the global write log `wglog` (timestamp 0
is the image, timestamp `i+1` is `wglog[i]`), with one `Wstate` per hart; the
era bookkeeping (`wggen`/`wgpow`) is untouched -- the crash layer is orthogonal
to the memory model.  What this file proves: the per-arm inversions, the
cross-arm sanity facts M1c's state interpretation consumes (the log is
append-only within an era, the image is fixed for an era, the durable disk image
moves only in the disk's own steps, only the stepping hart's views move and
they only rise) and the reducibility helpers (corpses step; the power thread
steps while the power is on; a live device thread always steps).

INTERIM DEVICE MEMORY (Rocq "WHAT M5 REPLACES"): a device's bus-master read sees
the COHERENT FLAT projection `wflat` of image + log (the coherent latest byte,
`wflatLookup`), and its writes are appended as per-byte messages of the disk
agent `nDisk` (`wmsgsOfMap`).  The M5 disk-as-program (`VirtioProg`,
`WeakEvLang`) replaces this.

**Deviations from Rocq.**

1. NAMES: the tree's lowerCamelCase (`wgstate` ↦ `WGState`, `ibch` ↦ `Ibch`;
   the single-word `wgstate` fields keep their Rocq spelling `wgregs`, `wgimg`,
   `wglog`, `wgws`, `wgdev`, `wggen`, `wgpow`, `wgib`; `ib_bits` ↦ `ibBits`,
   `ib_rds` ↦ `ibRds`).  `wreg` is `Nat` (as `Weak/WeakDeps.lean`).
2. THE BASE LANGUAGE.  Rocq reused `RiscvLang`'s expression type `mexpr`
   (`LoopE gen cpu | UartLoopE gen | DiskLoopE gen | PlicLoopE gen |
   PowerLoopE`), its device step relations `uart_step`/`plic_step` and
   (through `wdisk_step`) `VirtioModel`'s `disk_step`.  Lean's MachCSL has no
   such relations: every device is a PROGRAM of the device language
   (`MachCSL.Dev.DevLang`, `DevOp`), and `MachCSL.Expr` carries a hart's
   residual Sail monad.  So:
   - the expression type is the new `WExpr` (`loop gen cpu` = Rocq `LoopE`;
     `dev gen d tid m` = a task of device `d` with program `m` left, the Lean
     form of `UartLoopE`/`DiskLoopE`/`PlicLoopE`; `power` = `PowerLoopE`).  It
     cannot be `MachCSL.Expr`: iris-lean's `PrimStep`'s state is an
     `outParam`, so one expression type has one language;
   - the three device arms are ONE arm, `wdevStep`, the mirror of
     `MachCSL.devStep` over `WGState`: the device's local step, `get`,
     `choose`, `sample`, `setPin` (Rocq `plic_step`'s pin write), `fork`/
     `join` (the task bookkeeping, new field `wgrt`) verbatim; `dmaRead` reads
     the flat projection `wflat` (Rocq: the disk's `mem_view` of `wflat`);
     `dmaWrite` appends `wdmaMsgs` = `wmsgsOfMap` of the written bytes (Rocq:
     `wmsgs_of_map w` of the DMA write set).  The TSO reservation check of
     `MachCSL.devOpStep` (`anyReserve`) is dropped: weak reservations are
     agent-local (`Wstate.wRes`), and Rocq's DMA has no such check;
   - Rocq `power_fork` is the Lean-only `wpowerFork` (the harts' loops and every
     device's root thread, as `MachCSL.powerFork`);
   - the observation type is `Empty` (Rocq `mobs := Empty_set`), so every arm's
     `κ = []` is kept and is trivially true.
   Consequently: `wdisk_step`, `wdisk_step_disk_step`, `disk_step_wdisk_step`
   (the bridge to the SC `disk_step`, which has no Lean counterpart) are NOT
   ported (0 downstream uses of the bridges; the live `WeakExec` use of
   `wdisk_step` is the disk arm, now `wdevStep`); the per-device inversions /
   frames / reducibility lemmas are stated once for any device:
   `wprim_step_{uart,disk,plic}_inv` ↦ `wprimStepDevInv`,
   `wprim_step_{uart,plic}_v_disk` ↦ `wprimStepDevDiskOf` (premise
   `d ≠ .virtio`), `wprim_step_{uart,disk,plic}_ws` ↦ `wprimStepDevWs`,
   `wprim_step_{uart,disk,plic}_dead` ↦ `wprimStepDevDead`, and
   `wprim_step_uart_idle`/`wprim_step_disk_idle` (a premise-free stutter) ↦
   `wprimStepDevLive` (a LIVE device thread always has a step: the device
   language has no stutter arm, but every primitive is answered or blocked).
3. `wprim_step` is a `match` on the expression (as `MachCSL.primStep`) rather
   than Rocq's five-way disjunction of `∃ gen, e = … ∧ …`; each arm's body is
   Rocq's, so `wprimStepLoopInv`/`wprimStepPowerInv` are the identity.
4. O2 STAGE B: the per-hart instruction view `Wmstate.wmItv` lives in the new
   field `wgitv`; `whartView` reads it and `whartWrite` writes it back; a boot
   resets it to 0 (`wbootFacts`).
5. BOOT.  `wboot_facts`' two image clauses (nothing outside RAM; RAM holds
   `boot_byte`) are `wgimg = bootImage` (the language constant, as
   `MachCSL.bootFacts`' `σ.mem = imgFlat bootImage`); the register clause is
   `MachCSL.bootFacts`' (`∃ f₀, bootRun (bootProg (bootHid c) bootPMA) f₀ =
   some ((), wgregs c)`, Rocq: an SC `run` of `ArchReset.boot_prog`); the three
   device clauses (`uart0_state`, `plic0_state`, `∃ v0, virtio_reset v0`) are
   `∃ ds, wgdev = ds.reset` in `wbootFacts` and `wgdev = old.reset` in
   `wbootShape` (Rocq: `dvirtio = virtio_reset old`); new clauses
   `wgitv c = 0` and `wgrt d = DevRt.init`.
6. MAPS: `gmap Arch.pa (bv 8)` is `GMapF PAddr (BitVec 8)` (= `MachCSL.Mem`);
   `m !! a` is `get? m a`; `<[k := v]> m` is `insert m k v`; `map_to_list` is
   `toList`; `m1 ∪ m2` is iris-lean's `PartialMap.union m1 m2` (a bare `∪`
   at `GMapF PAddr` resolves to `Std.ExtTreeMap`'s instance).  The Rocq `Insert CPU _ (CPU → _)` instances `gws_insert`,
   `gib_insert` (and `RiscvLang.greg_insert`) are `MachCSL.updCpu`.
7. `wlog_wf` is `∀ m ∈ log, wmsgWf m` (Rocq `Forall`).
8. `wwrite_msg_wf`: at value width `8 * n`, `n : Nat` (as
   `Weak.wwriteMsg`, WeakInterp deviation 7).
9. `tid_is_hart_cpu`: `∃ c : CPU, t = some c.val` (Rocq `fin_to_nat c`).
10. The Rocq `Local` index-arithmetic lemmas `bm_base_range`, `bm_succ_lo`,
   `bm_succ_hi`, `bm_here`, `bm_shift` exist to dodge Rocq's `lia`-with-`mword`
   failure; `omega` has no such problem, so they are inlined into
   `bytesMapLookup`'s proof.
11. `weak_lang_mixin` is the `val_stuck` field (`weakLangMixin`);
   `weak_riscv_lang` is the instance `weakRiscvLang : Language WExpr WGState
   Empty Empty`.

**File-qualified names** (`notes/weak-port-dupnames.json`): `WeakLang.whartViewImg`.

**Rocq → Lean name map.**  `ibch` `Ibch`, `IbCh` `Ibch.mk`, `ib_none` `ibNone`,
`ib_ann` `ibAnn`, `ib_read` `ibRead`, `ib_read_bits` `ibReadBits`,
`ib_read_rds_some` `ibReadRdsSome`, `ib_read_rds_none` `ibReadRdsNone`,
`wgstate` `WGState`, `gws_insert`/`gib_insert` `updCpu`, `gws_insert_eq`
`gwsInsertEq`, `gws_insert_ne` `gwsInsertNe`, `gib_insert_eq` `gibInsertEq`,
`gib_insert_ne` `gibInsertNe`, `greg_insert_eq` `gregInsertEq`,
`greg_insert_ne` `gregInsertNe`, `whart_view` `whartView`, `whart_write`
`whartWrite`, `whart_view_img` `WeakLang.whartViewImg`, `whart_view_log`
`whartViewLog`, `whart_view_ws` `whartViewWs`, `whart_view_dev` `whartViewDev`,
`whart_write_img/log/dev/gen/pow` `whartWriteImg/Log/Dev/Gen/Pow`,
`whart_write_ws_eq/ne` `whartWriteWsEq/Ne`, `whart_write_regs_eq/ne`
`whartWriteRegsEq/Ne`, `wmsg_wf` `wmsgWf`, `wlog_wf` `wlogWf`, `bytes_map`
`bytesMap`, `msg_map` `msgMap`, `wflat` `wflat`, `wflat_nil` `wflatNil`,
`wflat_app` `wflatApp`, `bytes_map_lookup` `bytesMapLookup`, `msg_map_lookup`
`msgMapLookup`, `wflat_lookup` `wflatLookup`, `wflat_latest` `wflatLatest`,
`n_disk` `nDisk`, `tid_is_hart` `tidIsHart`, `tid_is_hart_cpu` `tidIsHartCpu`,
`tid_is_hart_cpu_intro` `tidIsHartCpuIntro`, `n_disk_not_hart` `nDiskNotHart`,
`wmsgs_of_map` `wmsgsOfMap`, `wmsgs_of_map_tid/not_hart/plain/data/empty/wf`
`wmsgsOfMapTid/NotHart/Plain/Data/Empty/Wf`, `wwrite_msg_wf` `wwriteMsgWf`,
`wboot_facts` `wbootFacts`, `wboot_shape` `wbootShape`, `wboot_facts_log`
`wbootFactsLog`, `wboot_facts_ws` `wbootFactsWs`, `wboot_facts_wlog_wf`
`wbootFactsWlogWf`, `wthread_live` `wthreadLive`, `wprim_step` `wprimStep`,
`weak_lang_mixin` `weakLangMixin`, `weak_riscv_lang` `weakRiscvLang`,
`wprim_step_loop_inv` `wprimStepLoopInv`, `wprim_step_power_inv`
`wprimStepPowerInv`, `wprim_step_log_app` `wprimStepLogApp`,
`wprim_step_poweron_log` `wprimStepPoweronLog`, `wprim_step_img`
`wprimStepImg`, `wprim_step_loop_v_disk` `wprimStepLoopDiskOf`,
`wprim_step_loop_ws_other` `wprimStepLoopWsOther`, `wprim_step_loop_ws_le`
`wprimStepLoopWsLe`, `wprim_step_loop_dead` `wprimStepLoopDead`,
`wprim_step_power_off` `wprimStepPowerOff`; the per-device lemmas as in
deviation 2.
Lean-only: `WExpr`, `wpowerFork`, `WGState.setDev/setRt/setReg`, `wdmaView`,
`wdmaMsgs` (+ `wdmaMsgsTid/NotHart/Plain/Wf`), `wdevOpStep`, `wdevBlocked`,
`wdevStep`, `flatUnionSomeL`, `flatUnionR`, `wdevOpStepFrame`, `wdevStepFrame`, `wdevStepTotal`,
`whartViewItv`, `whartWriteItvEq/Ne`, `whartWriteIb`, `whartWriteRt`,
`nDiskDiskAgent`.

**Not ported:** `wdisk_step`, `wdisk_step_disk_step`, `disk_step_wdisk_step`
(deviation 2) and the five `Local` `bm_*` arithmetic lemmas (deviation 10).

**Statements checked** (diffed against Rocq by hand): all; the changed ones are
the deviations above.
-/
import Weak.WeakInterp

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! ## 1. The global weak state -/

/-- THE PER-INSTRUCTION CHANNEL (D3 / B2e-3b slice 2a): the hart's announced
instruction bits AND the dynamic register provenance of the instruction in
flight -- the dependency-carrying registers (GPRs `1..31`, `WeakDeps`' CSR
pseudo-registers `32..52`) the Sail run has READ since the instruction started.
Reset at the two instruction boundaries (`ibNone`, `ibAnn`), appended to at
every read of a carrier register (`ibRead`).  The state interpretation does
not mention it. -/
structure Ibch where
  ibBits : Option (BitVec 32)
  ibRds : List Nat
  deriving DecidableEq, Inhabited

def ibNone : Ibch := ⟨none, []⟩
def ibAnn (w : BitVec 32) : Ibch := ⟨some w, []⟩

/-- The accumulator: `o` is the already-classified register number (`none` =
not a dependency carrier). -/
def ibRead (i : Ibch) (o : Option Nat) : Ibch :=
  match o with
  | some r => ⟨i.ibBits, i.ibRds ++ [r]⟩
  | none => i

theorem ibReadBits (i : Ibch) (o : Option Nat) : (ibRead i o).ibBits = i.ibBits := by
  cases o <;> rfl
theorem ibReadRdsSome (i : Ibch) (r : Nat) : (ibRead i (some r)).ibRds = i.ibRds ++ [r] := rfl
theorem ibReadRdsNone (i : Ibch) : (ibRead i none).ibRds = i.ibRds := rfl

/-- `RiscvLang.gstate` with the flat byte map replaced by the era-initial image
plus the global write log, one `Wstate` per hart, the instruction channel
`wgib` (D3), and two Lean-only fields: the per-hart instruction view `wgitv`
(O2 Stage B, deviation 4) and the devices' task bookkeeping `wgrt`
(deviation 2). -/
structure WGState where
  wgregs : CPU → RegFile
  wgimg : Mem
  wglog : List Wmsg
  wgws : CPU → Wstate
  wgdev : DevStates
  wggen : Nat
  wgpow : Bool
  /-- D3: the instruction bits of the instruction in flight, and (slice 2a)
  the dynamic read set -/
  wgib : CPU → Ibch
  /-- O2 Stage B: each hart's instruction view (Lean-only) -/
  wgitv : CPU → Nat
  /-- each device's task bookkeeping (Lean-only, as `MachCSL.MState.devrt`) -/
  wgrt : DevId → DevRt

theorem gwsInsertEq (gw : CPU → Wstate) (c : CPU) (ws : Wstate) : updCpu gw c ws c = ws := by
  simp [updCpu]

theorem gwsInsertNe (gw : CPU → Wstate) (c c' : CPU) (ws : Wstate) :
    c' ≠ c → updCpu gw c ws c' = gw c' := by
  intro h; simp [updCpu, h]

theorem gibInsertEq (gi : CPU → Ibch) (c : CPU) (v : Ibch) : updCpu gi c v c = v := by
  simp [updCpu]

theorem gibInsertNe (gi : CPU → Ibch) (c c' : CPU) (v : Ibch) :
    c' ≠ c → updCpu gi c v c' = gi c' := by
  intro h; simp [updCpu, h]

theorem gregInsertEq (gr : CPU → RegFile) (c : CPU) (rs : RegFile) : updCpu gr c rs c = rs := by
  simp [updCpu]

theorem gregInsertNe (gr : CPU → RegFile) (c c' : CPU) (rs : RegFile) :
    c' ≠ c → updCpu gr c rs c' = gr c' := by
  intro h; simp [updCpu, h]

/-! ## 2. The hart seam: view extraction and write-back -/

/-- One hart's `Wmstate`: its own registers, weak state and instruction view,
the SHARED image, log and device fabric. -/
def whartView (g : WGState) (c : CPU) : Wmstate :=
  ⟨g.wgregs c, g.wgimg, g.wglog, g.wgws c, g.wgdev, g.wgitv c⟩

/-- The write-back.  THE IMAGE IS NEVER WRITTEN BACK: no `wrun` moves it
(`Weak.wrunImg`), so it stays literally fixed for a whole generation. -/
def whartWrite (g : WGState) (c : CPU) (s : Wmstate) : WGState :=
  { g with wgregs := updCpu g.wgregs c s.wmRegs, wglog := s.wmLog,
           wgws := updCpu g.wgws c s.wmWs, wgdev := s.wmDev,
           wgitv := updCpu g.wgitv c s.wmItv }

theorem WeakLang.whartViewImg (g : WGState) (c : CPU) : (whartView g c).wmImg = g.wgimg := rfl
theorem whartViewLog (g : WGState) (c : CPU) : (whartView g c).wmLog = g.wglog := rfl
theorem whartViewWs (g : WGState) (c : CPU) : (whartView g c).wmWs = g.wgws c := rfl
theorem whartViewDev (g : WGState) (c : CPU) : (whartView g c).wmDev = g.wgdev := rfl
theorem whartViewItv (g : WGState) (c : CPU) : (whartView g c).wmItv = g.wgitv c := rfl

theorem whartWriteImg (g : WGState) (c : CPU) (s : Wmstate) : (whartWrite g c s).wgimg = g.wgimg := rfl
theorem whartWriteLog (g : WGState) (c : CPU) (s : Wmstate) : (whartWrite g c s).wglog = s.wmLog := rfl
theorem whartWriteDev (g : WGState) (c : CPU) (s : Wmstate) : (whartWrite g c s).wgdev = s.wmDev := rfl
theorem whartWriteGen (g : WGState) (c : CPU) (s : Wmstate) : (whartWrite g c s).wggen = g.wggen := rfl
theorem whartWritePow (g : WGState) (c : CPU) (s : Wmstate) : (whartWrite g c s).wgpow = g.wgpow := rfl
theorem whartWriteIb (g : WGState) (c : CPU) (s : Wmstate) : (whartWrite g c s).wgib = g.wgib := rfl
theorem whartWriteRt (g : WGState) (c : CPU) (s : Wmstate) : (whartWrite g c s).wgrt = g.wgrt := rfl
theorem whartWriteWsEq (g : WGState) (c : CPU) (s : Wmstate) : (whartWrite g c s).wgws c = s.wmWs :=
  gwsInsertEq _ _ _
theorem whartWriteWsNe (g : WGState) (c : CPU) (s : Wmstate) (c' : CPU) :
    c' ≠ c → (whartWrite g c s).wgws c' = g.wgws c' :=
  gwsInsertNe _ _ _ _
theorem whartWriteRegsEq (g : WGState) (c : CPU) (s : Wmstate) :
    (whartWrite g c s).wgregs c = s.wmRegs :=
  gregInsertEq _ _ _
theorem whartWriteRegsNe (g : WGState) (c : CPU) (s : Wmstate) (c' : CPU) :
    c' ≠ c → (whartWrite g c s).wgregs c' = g.wgregs c' :=
  gregInsertNe _ _ _ _
theorem whartWriteItvEq (g : WGState) (c : CPU) (s : Wmstate) :
    (whartWrite g c s).wgitv c = s.wmItv := by
  simp [whartWrite, updCpu]
theorem whartWriteItvNe (g : WGState) (c : CPU) (s : Wmstate) (c' : CPU) :
    c' ≠ c → (whartWrite g c s).wgitv c' = g.wgitv c' := by
  intro h; simp [whartWrite, updCpu, h]

/-! ## 3. `wflat`: the coherent flat projection of image + log

INTERIM (Rocq design doc, Decision 6).  A bus master that has no view of its
own sees the COHERENT LATEST byte at every address: the image overlaid by the
log in order, last write per byte winning -- exactly `WeakMem.latest`'s pick
(`wflatLookup`).  A left fold of LEFT-BIASED unions. -/

/-- A message fits in the address space (`zPa` wraps modulo `2^64`). -/
def wmsgWf (m : Wmsg) : Prop :=
  0 ≤ m.wmPa ∧ m.wmPa + (m.wmData.length : Int) ≤ 18446744073709551616

def wlogWf (log : List Wmsg) : Prop := ∀ m ∈ log, wmsgWf m

def bytesMap (base : Int) : List (BitVec 8) → GMapF PAddr (BitVec 8)
  | [] => ∅
  | b :: bs => insert (bytesMap (base + 1) bs) (zPa base) b

def msgMap (m : Wmsg) : GMapF PAddr (BitVec 8) := bytesMap m.wmPa m.wmData

def wflat (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) : GMapF PAddr (BitVec 8) :=
  log.foldl (fun m msg => PartialMap.union (msgMap msg) m) img

/-- The left-biased union's two lookups, at the iris-lean union (deviation 6: a
bare `∪` at `GMapF PAddr` picks `Std.ExtTreeMap`'s own instance). -/
theorem flatUnionSomeL {m1 m2 : GMapF PAddr (BitVec 8)} {a : PAddr} {x : BitVec 8}
    (h : get? m1 a = some x) : get? (PartialMap.union m1 m2) a = some x :=
  lookupUnionSomeL (M := GMapF PAddr) h

theorem flatUnionR {m1 m2 : GMapF PAddr (BitVec 8)} {a : PAddr}
    (h : get? m1 a = none) : get? (PartialMap.union m1 m2) a = get? m2 a :=
  lookupUnionR (M := GMapF PAddr) h

theorem wflatNil (img : GMapF PAddr (BitVec 8)) : wflat img [] = img := rfl

theorem wflatApp (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (m : Wmsg) :
    wflat img (log ++ [m]) = PartialMap.union (msgMap m) (wflat img log) := by
  simp [wflat, List.foldl_append]

/-- `bytesMap` IS `WeakMem.msgByte`, transported across the address seam. -/
theorem bytesMapLookup (bs : List (BitVec 8)) (base : Int) (a : PAddr) :
    0 ≤ base → base + (bs.length : Int) ≤ 18446744073709551616 →
    get? (bytesMap base bs) a =
      (if base ≤ paZ a then bs[(paZ a - base).toNat]? else none) := by
  induction bs generalizing base with
  | nil =>
    intro _ _
    rw [bytesMap, lookupEmpty]
    split <;> simp
  | cons b bs ih =>
    intro hlo hhi
    simp only [List.length_cons] at hhi
    rw [bytesMap]
    by_cases ha : a = zPa base
    · subst ha
      rw [lookupInsert, WeakInterp.paZZPa base ⟨hlo, by omega⟩, if_pos (Int.le_refl _)]
      simp
    · rw [lookupInsertNe (fun h => ha h.symm), ih (base + 1) (by omega) (by omega)]
      have hne : paZ a ≠ base := fun h => ha (by rw [← h, zPaPaZ])
      by_cases h1 : base ≤ paZ a
      · rw [if_pos (by omega : base + 1 ≤ paZ a), if_pos h1]
        have e : (paZ a - base).toNat = (paZ a - (base + 1)).toNat + 1 := by omega
        rw [e, List.getElem?_cons_succ]
      · rw [if_neg (by omega), if_neg h1]

theorem msgMapLookup (m : Wmsg) (a : PAddr) :
    wmsgWf m → get? (msgMap m) a = msgByte m (paZ a) := by
  rintro ⟨hlo, hhi⟩
  exact bytesMapLookup m.wmData m.wmPa a hlo hhi

/-- THE CHARACTERIZATION: the flat view of a byte is what its COHERENT LATEST
timestamp writes. -/
theorem wflatLookup (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : PAddr) :
    wlogWf log →
    get? (wflat img log) a = logByte (imgZ img) log (latestTs log (paZ a)) (paZ a) := by
  induction log using snocInd with
  | h0 =>
    intro _
    rw [wflatNil, latestTsNil, logByte0, imgZLookup]
    rfl
  | hs l m ih =>
    intro hwf
    have hwf0 : wlogWf l := fun x hx => hwf x (List.mem_append_left _ hx)
    have hwfm : wmsgWf m := hwf m (List.mem_append_right _ (List.mem_singleton_self m))
    rw [wflatApp, latestTsApp]
    cases hw : msgWritesb m (paZ a) with
    | true =>
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 ((msgWritesbTrue m (paZ a)).1 hw)
      have hmm : get? (msgMap m) a = some v := by rw [msgMapLookup m a hwfm, hv]
      rw [flatUnionSomeL hmm]
      simp only [↓reduceIte]
      rw [logByteS, List.getElem?_concat_length]
      simp [hv]
    | false =>
      have hmm : get? (msgMap m) a = none := by
        rw [msgMapLookup m a hwfm]; exact (msgWritesbFalse m (paZ a)).1 hw
      rw [flatUnionR hmm]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [logByteApp (imgZ img) l [m] _ _ (latestTsLe l (paZ a))]
      exact ih hwf0

/-- ... and against `WeakMem.latest` itself, which pins the timestamp. -/
theorem wflatLatest (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : PAddr) (t : Nat) :
    wlogWf log → latest (imgZ img) log (paZ a) t →
    get? (wflat img log) a = logByte (imgZ img) log t (paZ a) := by
  intro hwf hl
  rw [wflatLookup img log a hwf, latestTsEq (imgZ img) log (paZ a) t hl]

/-! ## 4. The disk agent and its messages -/

/-- THE DISK'S AGENT INDEX: harts are agents `0 .. NCPU-1`, the disk is agent
`NCPU` (the DMA-tid unification). -/
def nDisk : Nat := NCPU

theorem nDiskDiskAgent : nDisk = diskAgent := rfl

/-- "The author is a HART". -/
def tidIsHart (t : Option Nat) : Prop := tidHart NCPU t

theorem tidIsHartCpu (t : Option Nat) : tidIsHart t ↔ ∃ c : CPU, t = some c.val := by
  constructor
  · rintro ⟨i, rfl, hlt⟩
    exact ⟨⟨i, hlt⟩, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c.val, rfl, c.isLt⟩

theorem tidIsHartCpuIntro (c : CPU) : tidIsHart (some c.val) :=
  (tidIsHartCpu _).2 ⟨c, rfl⟩

/-- THE DISK IS NOT A HART. -/
theorem nDiskNotHart : ¬ tidIsHart (some nDisk) := fun h => tidHartNeDisk NCPU _ h rfl

/-- A DMA write set as log messages: one message per byte, in `toList` order,
tagged `some nDisk`, plain. -/
def wmsgsOfMap (w : GMapF PAddr (BitVec 8)) : List Wmsg :=
  (toList w).map (fun ab : PAddr × BitVec 8 => ⟨paZ ab.1, [ab.2], some nDisk, .WCplain⟩)

theorem wmsgsOfMapTid (w : GMapF PAddr (BitVec 8)) (m : Wmsg) :
    m ∈ wmsgsOfMap w → m.wmTid = some nDisk := by
  intro h
  obtain ⟨_, _, rfl⟩ := List.mem_map.1 h
  rfl

theorem wmsgsOfMapNotHart (w : GMapF PAddr (BitVec 8)) (m : Wmsg) :
    m ∈ wmsgsOfMap w → ¬ tidIsHart m.wmTid := by
  intro h
  rw [wmsgsOfMapTid w m h]
  exact nDiskNotHart

theorem wmsgsOfMapPlain (w : GMapF PAddr (BitVec 8)) (m : Wmsg) :
    m ∈ wmsgsOfMap w → m.wmAk = .WCplain := by
  intro h
  obtain ⟨_, _, rfl⟩ := List.mem_map.1 h
  rfl

theorem wmsgsOfMapData (w : GMapF PAddr (BitVec 8)) (m : Wmsg) :
    m ∈ wmsgsOfMap w → m.wmData ≠ [] := by
  intro h
  obtain ⟨_, _, rfl⟩ := List.mem_map.1 h
  simp

theorem wmsgsOfMapEmpty : wmsgsOfMap (∅ : GMapF PAddr (BitVec 8)) = [] := by
  simp [wmsgsOfMap, mapToListEmpty]

theorem wmsgsOfMapWf (w : GMapF PAddr (BitVec 8)) : wlogWf (wmsgsOfMap w) := by
  intro m h
  obtain ⟨⟨a, b⟩, _, rfl⟩ := List.mem_map.1 h
  have := WeakInterp.paZRange a
  simp only [wmsgWf, List.length_singleton]
  omega

/-- ... and the harts' own messages fit, as soon as the access does not wrap. -/
theorem wwriteMsgWf (tid : Option Nat) (k : WmClass) (pa : PAddr) (n : Nat) (v : BitVec (8 * n)) :
    paZ pa + (n : Int) ≤ 18446744073709551616 → wmsgWf (wwriteMsg tid k pa n v) := by
  intro hfit
  have := WeakInterp.paZRange pa
  simp only [wmsgWf, wwriteMsgPa, wwriteMsgLength]
  omega

/-- The messages of a device's DMA write of `w` at `pa` (Lean-only): the write
set as a map, then `wmsgsOfMap`. -/
def wdmaMsgs (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) : List Wmsg :=
  wmsgsOfMap (bytesMap (paZ pa) (bytesOf w))

theorem wdmaMsgsTid (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (m : Wmsg) :
    m ∈ wdmaMsgs pa n w → m.wmTid = some nDisk := wmsgsOfMapTid _ m
theorem wdmaMsgsNotHart (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (m : Wmsg) :
    m ∈ wdmaMsgs pa n w → ¬ tidIsHart m.wmTid := wmsgsOfMapNotHart _ m
theorem wdmaMsgsPlain (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (m : Wmsg) :
    m ∈ wdmaMsgs pa n w → m.wmAk = .WCplain := wmsgsOfMapPlain _ m
theorem wdmaMsgsWf (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) : wlogWf (wdmaMsgs pa n w) :=
  wmsgsOfMapWf _

/-! ## 5. Expressions, boot / crash reset -/

/-- The weak language's expressions (deviation 2): a hart's loop (Rocq `LoopE`),
a task of a device with its program left (Rocq `UartLoopE`/`DiskLoopE`/
`PlicLoopE`), the power thread (Rocq `PowerLoopE`). -/
inductive WExpr where
  | loop (gen : Nat) (cpu : CPU)
  | dev (gen : Nat) (d : DevId) (tid : TaskId) (m : DevProg d)
  | power

/-- What a `PowerOn` forks (Rocq `power_fork`): every hart's loop and every
device's root thread at its loop boundary. -/
def wpowerFork (gen : Nat) : List WExpr :=
  cpus.map (WExpr.loop gen) ++ DevId.all.map (fun d => WExpr.dev gen d rootTask (.pure ()))

/-- A booted weak state (deviation 5): power on, the boot image, a FRESH ERA (no
writes, no agent has observed anything, instruction views at 0), every
register file the output of a run of the boot program, the devices a reset,
no device task. -/
def wbootFacts (g' : WGState) : Prop :=
  g'.wgpow = true
  ∧ g'.wgimg = bootImage
  ∧ g'.wglog = []
  ∧ (∀ c : CPU, g'.wgws c = wsInit)
  ∧ (∀ c : CPU, g'.wgitv c = 0)
  ∧ (∀ c : CPU, ∃ f₀ : RegFile, bootRun (bootProg (bootHid c) bootPMA) f₀ = some ((), g'.wgregs c))
  ∧ (∃ ds : DevStates, g'.wgdev = ds.reset)
  ∧ (∀ d : DevId, g'.wgrt d = DevRt.init)

def wbootShape (g g' : WGState) : Prop :=
  g'.wggen = g.wggen ∧ g'.wgdev = g.wgdev.reset ∧ wbootFacts g'

theorem wbootFactsLog (g' : WGState) : wbootFacts g' → g'.wglog = [] :=
  fun h => h.2.2.1

theorem wbootFactsWs (g' : WGState) : wbootFacts g' → ∀ c, g'.wgws c = wsInit :=
  fun h => h.2.2.2.1

theorem wbootFactsWlogWf (g' : WGState) : wbootFacts g' → wlogWf g'.wglog := by
  intro h
  rw [wbootFactsLog g' h]
  intro m hm
  cases hm

/-! ## 6. The device steps (deviation 2) -/

/-- Update one device's state. -/
abbrev WGState.setDev (g : WGState) (d : DevId) (s : DevSt d) : WGState :=
  { g with wgdev := g.wgdev.set d s }

/-- Update one device's task bookkeeping. -/
abbrev WGState.setRt (g : WGState) (d : DevId) (rt : DevRt) : WGState :=
  { g with wgrt := updCpu' g.wgrt d rt }

/-- Update one register of one hart. -/
abbrev WGState.setReg (g : WGState) (cpu : CPU) (r : Register) (v : RegisterType r) : WGState :=
  { g with wgregs := updCpu g.wgregs cpu ((g.wgregs cpu).set r v) }

/-- What a bus-master read may answer: every byte the flat projection covers
is its coherent latest byte, the others are anything (Rocq `mem_view` of
`wflat`). -/
def wdmaView (g : WGState) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) : Prop :=
  ∀ j, j < n → ∀ b, get? (wflat g.wgimg g.wglog) (pa + BitVec.ofNat 64 j) = some b →
    nthByte w j = b

/-- `MachCSL.devOpStep` over the weak state, silent (Rocq `mobs` is empty). -/
def wdevOpStep (gen : Nat) (d : DevId) (o : DevOp (DevSt d) (DevTask d)) (g : WGState) :
    o.ret → WGState → List WExpr → Prop :=
  match o with
  | .step f => fun _ g' efs =>
      ∃ s' os, f (g.wgdev.st d) = some (s', os) ∧ devObsOk d (g.wgdev.st d) s' os ∧
        g' = g.setDev d s' ∧ efs = []
  | .get => fun v g' efs => v = g.wgdev.st d ∧ g' = g ∧ efs = []
  | .choose => fun _ g' efs => g' = g ∧ efs = []
  | .dmaRead pa n => fun v g' efs => wdmaView g pa n v ∧ g' = g ∧ efs = []
  | .dmaWrite f pa n w => fun _ g' efs =>
      efs = [] ∧
      ((∃ s', f (g.wgdev.st d) = some s' ∧ devObsOk d (g.wgdev.st d) s' [] ∧ ramBytes pa n ∧
          g' = ({ g with wglog := g.wglog ++ wdmaMsgs pa n w } : WGState).setDev d s') ∨
       ((f (g.wgdev.st d) = none ∨ ¬ ramBytes pa n) ∧ g' = g))
  | .sample src => fun v g' efs => v = devLevel g.wgdev src ∧ g' = g ∧ efs = []
  | .setPin cpu mmode b => fun _ g' efs =>
      efs = [] ∧
      g' = (if mmode then g.setReg cpu .sig_meip (if b then 1#1 else 0#1)
            else g.setReg cpu .sig_seip (if b then 1#1 else 0#1))
  | .fork t => fun v g' efs =>
      v = (g.wgrt d).next ∧
      g' = g.setRt d { g.wgrt d with next := (g.wgrt d).next + 1 } ∧
      efs = [.dev gen d (g.wgrt d).next ((devSig d).task t)]
  | .join tid => fun _ g' efs => tid ∈ (g.wgrt d).done ∧ g' = g ∧ efs = []

/-- `MachCSL.devBlocked` over the weak state (no reservation arm). -/
def wdevBlocked (d : DevId) (o : DevOp (DevSt d) (DevTask d)) (g : WGState) : Prop :=
  match o with
  | .step f => ∀ s' os, f (g.wgdev.st d) = some (s', os) → ¬ devObsOk d (g.wgdev.st d) s' os
  | .dmaWrite f pa n _ =>
      ramBytes pa n ∧ ∃ s', f (g.wgdev.st d) = some s' ∧ ¬ devObsOk d (g.wgdev.st d) s' []
  | .join tid => tid ∉ (g.wgrt d).done
  | _ => False

/-- `MachCSL.devStep` over the weak state, silent. -/
def wdevStep (gen : Nat) (d : DevId) (tid : TaskId) (m : DevProg d) (g : WGState)
    (m' : DevProg d) (g' : WGState) (efs : List WExpr) : Prop :=
  match m with
  | .pure _ =>
      efs = [] ∧
      ((tid = rootTask ∧ m' = (devSig d).body ∧ g' = g) ∨
       (tid ≠ rootTask ∧ m' = .pure () ∧
         g' = (if tid ∈ (g.wgrt d).done then g
               else g.setRt d { g.wgrt d with done := tid :: (g.wgrt d).done })))
  | .op o k =>
      (∃ v : o.ret, m' = k v ∧ wdevOpStep gen d o g v g' efs) ∨
      (wdevBlocked d o g ∧ m' = m ∧ g' = g ∧ efs = [])

/-- What a device primitive leaves alone (Lean-only): the image, every hart's
weak state and instruction view, the era; the log only grows; a device other
than the disk keeps the durable disk image. -/
theorem wdevOpStepFrame {gen : Nat} {d : DevId} {o : DevOp (DevSt d) (DevTask d)} {g : WGState}
    {v : o.ret} {g' : WGState} {efs : List WExpr} (h : wdevOpStep gen d o g v g' efs) :
    g'.wgimg = g.wgimg ∧ g'.wgws = g.wgws ∧ g'.wgitv = g.wgitv ∧ g'.wggen = g.wggen ∧
      g'.wgpow = g.wgpow ∧ (∃ ms, g'.wglog = g.wglog ++ ms) ∧
      (d ≠ .virtio → diskOf g'.wgdev = diskOf g.wgdev) := by
  cases o with
  | step f =>
    obtain ⟨s', os, -, -, rfl, -⟩ := h
    exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨[], by simp⟩, fun hd => diskOf_set_other _ _ _ hd⟩
  | get =>
    obtain ⟨-, rfl, -⟩ := h
    exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨[], by simp⟩, fun _ => rfl⟩
  | choose =>
    obtain ⟨rfl, -⟩ := h
    exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨[], by simp⟩, fun _ => rfl⟩
  | dmaRead pa n =>
    obtain ⟨-, rfl, -⟩ := h
    exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨[], by simp⟩, fun _ => rfl⟩
  | dmaWrite f pa n w =>
    obtain ⟨-, ⟨s', -, -, -, rfl⟩ | ⟨-, rfl⟩⟩ := h
    · exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨_, rfl⟩, fun hd => diskOf_set_other _ _ _ hd⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨[], by simp⟩, fun _ => rfl⟩
  | sample src =>
    obtain ⟨-, rfl, -⟩ := h
    exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨[], by simp⟩, fun _ => rfl⟩
  | setPin cpu mmode b =>
    obtain ⟨-, rfl⟩ := h
    cases mmode <;> exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨[], by simp⟩, fun _ => rfl⟩
  | fork t =>
    obtain ⟨-, rfl, -⟩ := h
    exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨[], by simp⟩, fun _ => rfl⟩
  | join tid =>
    obtain ⟨-, rfl, -⟩ := h
    exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨[], by simp⟩, fun _ => rfl⟩

theorem wdevStepFrame {gen : Nat} {d : DevId} {tid : TaskId} {m m' : DevProg d} {g g' : WGState}
    {efs : List WExpr} (h : wdevStep gen d tid m g m' g' efs) :
    g'.wgimg = g.wgimg ∧ g'.wgws = g.wgws ∧ g'.wgitv = g.wgitv ∧ g'.wggen = g.wggen ∧
      g'.wgpow = g.wgpow ∧ (∃ ms, g'.wglog = g.wglog ++ ms) ∧
      (d ≠ .virtio → diskOf g'.wgdev = diskOf g.wgdev) := by
  cases m with
  | pure a =>
    obtain ⟨-, ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := h
    · exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨[], by simp⟩, fun _ => rfl⟩
    · split
      · exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨[], by simp⟩, fun _ => rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨[], by simp⟩, fun _ => rfl⟩
  | op o k =>
    obtain ⟨v, -, hs⟩ | ⟨-, -, rfl, -⟩ := h
    · exact wdevOpStepFrame hs
    · exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨[], by simp⟩, fun _ => rfl⟩

/-- EVERY DEVICE THREAD HAS A STEP (Lean-only): each primitive is answered or
blocked, and a finished program restarts (root) or records itself done. -/
theorem wdevStepTotal (gen : Nat) (d : DevId) (tid : TaskId) (m : DevProg d) (g : WGState) :
    ∃ m' g' efs, wdevStep gen d tid m g m' g' efs := by
  classical
  cases m with
  | pure a =>
    by_cases ht : tid = rootTask
    · exact ⟨_, _, _, rfl, Or.inl ⟨ht, rfl, rfl⟩⟩
    · exact ⟨_, _, _, rfl, Or.inr ⟨ht, rfl, rfl⟩⟩
  | op o k =>
    cases o with
    | step f =>
      by_cases hs : ∃ s' os, f (g.wgdev.st d) = some (s', os) ∧ devObsOk d (g.wgdev.st d) s' os
      · obtain ⟨s', os, hf, hok⟩ := hs
        exact ⟨k (), g.setDev d s', [], Or.inl ⟨(), rfl, s', os, hf, hok, rfl, rfl⟩⟩
      · refine ⟨_, g, [], Or.inr ⟨?_, rfl, rfl, rfl⟩⟩
        intro s' os hf hok
        exact hs ⟨s', os, hf, hok⟩
    | get => exact ⟨_, g, [], Or.inl ⟨g.wgdev.st d, rfl, rfl, rfl, rfl⟩⟩
    | choose => exact ⟨_, g, [], Or.inl ⟨0, rfl, rfl, rfl⟩⟩
    | dmaRead pa n =>
      refine ⟨_, g, [], Or.inl ⟨assembleBytes n (fun j =>
        (get? (wflat g.wgimg g.wglog) (pa + BitVec.ofNat 64 j)).getD 0), rfl, ?_, rfl, rfl⟩⟩
      intro j hj b hb
      rw [nthByteAssembleBytes n _ j hj, hb]
      rfl
    | dmaWrite f pa n w =>
      by_cases h1 : ∃ s', f (g.wgdev.st d) = some s' ∧ devObsOk d (g.wgdev.st d) s' [] ∧
          ramBytes pa n
      · obtain ⟨s', hf, hok, hr⟩ := h1
        exact ⟨_, _, [], Or.inl ⟨(), rfl, rfl, Or.inl ⟨s', hf, hok, hr, rfl⟩⟩⟩
      · by_cases h2 : f (g.wgdev.st d) = none ∨ ¬ ramBytes pa n
        · exact ⟨_, g, [], Or.inl ⟨(), rfl, rfl, Or.inr ⟨h2, rfl⟩⟩⟩
        · refine ⟨_, g, [], Or.inr ⟨?_, rfl, rfl, rfl⟩⟩
          have hr : ramBytes pa n := Classical.byContradiction fun h => h2 (Or.inr h)
          cases hf : f (g.wgdev.st d) with
          | none => exact absurd (Or.inl hf) h2
          | some s' => exact ⟨hr, s', hf, fun hok => h1 ⟨s', hf, hok, hr⟩⟩
    | sample src => exact ⟨_, g, [], Or.inl ⟨_, rfl, rfl, rfl, rfl⟩⟩
    | setPin cpu mmode b => exact ⟨_, _, [], Or.inl ⟨(), rfl, rfl, rfl⟩⟩
    | fork t => exact ⟨_, _, _, Or.inl ⟨_, rfl, rfl, rfl, rfl⟩⟩
    | join tid' =>
      by_cases hj : tid' ∈ (g.wgrt d).done
      · exact ⟨_, g, [], Or.inl ⟨(), rfl, hj, rfl, rfl⟩⟩
      · exact ⟨_, g, [], Or.inr ⟨hj, rfl, rfl, rfl⟩⟩

/-! ## 7. `wprimStep` -/

def wthreadLive (g : WGState) (gen : Nat) : Prop := g.wgpow = true ∧ g.wggen = gen

instance (g : WGState) (gen : Nat) : Decidable (wthreadLive g gen) := by
  unfold wthreadLive; infer_instance

/-- The primitive step (deviations 2, 3): a hart runs one WHOLE `riscvStep` by
`wrun` at tid `some cpu`; a device task one step of its program; the power
thread PowerOff (bump the generation) / PowerOn (fork and reboot).  Every arm
of a dead generation is a corpse self-loop. -/
def wprimStep : WExpr → WGState → List Empty → WExpr → WGState → List WExpr → Prop
  | .loop gen cpu, g, κ, e', g', efs =>
    e' = .loop gen cpu ∧ κ = [] ∧ efs = [] ∧
    ((wthreadLive g gen ∧
      ∃ (tick : Bool) (u : Unit) (s' : Wmstate),
        wrun (some cpu.val) (riscvStep tick) (whartView g cpu) u s' ∧ g' = whartWrite g cpu s') ∨
     (¬ wthreadLive g gen ∧ g' = g))
  | .dev gen d tid m, g, κ, e', g', efs =>
    κ = [] ∧
    ((wthreadLive g gen ∧ ∃ m', e' = .dev gen d tid m' ∧ wdevStep gen d tid m g m' g' efs) ∨
     (¬ wthreadLive g gen ∧ efs = [] ∧ e' = .dev gen d tid m ∧ g' = g))
  | .power, g, κ, e', g', efs =>
    e' = .power ∧ κ = [] ∧
    ((g.wgpow = true ∧ efs = [] ∧ g' = { g with wggen := g.wggen + 1, wgpow := false }) ∨
     (g.wgpow = false ∧ efs = wpowerFork g.wggen ∧ wbootShape g g'))

open Iris.ProgramLogic in
/-- Rocq `weak_riscv_lang`. -/
instance weakRiscvLang : Language WExpr WGState Empty Empty where
  primStep c κ c' := wprimStep c.1 c.2 κ c'.1 c'.2.1 c'.2.2
  toVal _ := none
  ofVal v := nomatch v
  coe_of_toVal_eq_some h := nomatch h
  toVal_coe v := nomatch v
  val_stuck _ := rfl

open Iris.ProgramLogic in
/-- Rocq `weak_lang_mixin` (its one non-vacuous field, `val_stuck`). -/
theorem weakLangMixin (e : WExpr) (g : WGState) (κ : List Empty) (e' : WExpr) (g' : WGState)
    (efs : List WExpr) : wprimStep e g κ e' g' efs → ToVal.toVal (Val := Empty) e = none :=
  fun _ => rfl

/-! ## 8. Per-arm inversion -/

theorem wprimStepLoopInv (gen : Nat) (cpu : CPU) (g : WGState) (κ : List Empty) (e' : WExpr)
    (g' : WGState) (efs : List WExpr) :
    wprimStep (.loop gen cpu) g κ e' g' efs →
    e' = .loop gen cpu ∧ κ = [] ∧ efs = [] ∧
    ((wthreadLive g gen ∧
      ∃ (tick : Bool) (u : Unit) (s' : Wmstate),
        wrun (some cpu.val) (riscvStep tick) (whartView g cpu) u s' ∧ g' = whartWrite g cpu s') ∨
     (¬ wthreadLive g gen ∧ g' = g)) := id

theorem wprimStepDevInv (gen : Nat) (d : DevId) (tid : TaskId) (m : DevProg d) (g : WGState)
    (κ : List Empty) (e' : WExpr) (g' : WGState) (efs : List WExpr) :
    wprimStep (.dev gen d tid m) g κ e' g' efs →
    κ = [] ∧
    ((wthreadLive g gen ∧ ∃ m', e' = .dev gen d tid m' ∧ wdevStep gen d tid m g m' g' efs) ∨
     (¬ wthreadLive g gen ∧ efs = [] ∧ e' = .dev gen d tid m ∧ g' = g)) := id

theorem wprimStepPowerInv (g : WGState) (κ : List Empty) (e' : WExpr) (g' : WGState)
    (efs : List WExpr) :
    wprimStep .power g κ e' g' efs →
    e' = .power ∧ κ = [] ∧
    ((g.wgpow = true ∧ efs = [] ∧ g' = { g with wggen := g.wggen + 1, wgpow := false }) ∨
     (g.wgpow = false ∧ efs = wpowerFork g.wggen ∧ wbootShape g g')) := id

/-! ## 9. Cross-arm sanity lemmas -/

/-- THE LOG IS APPEND-ONLY -- every arm except a PowerOn (a fresh era). -/
theorem wprimStepLogApp (e : WExpr) (g : WGState) (κ : List Empty) (e' : WExpr) (g' : WGState)
    (efs : List WExpr) :
    wprimStep e g κ e' g' efs → (e = .power → g.wgpow = true) →
    ∃ ms, g'.wglog = g.wglog ++ ms := by
  intro h hpow
  cases e with
  | loop gen cpu =>
    obtain ⟨-, -, -, ⟨-, tick, u, s', hrun, rfl⟩ | ⟨-, rfl⟩⟩ := h
    · exact wrunLogApp _ _ _ _ _ hrun
    · exact ⟨[], by simp⟩
  | dev gen d tid m =>
    obtain ⟨-, ⟨-, m', -, hs⟩ | ⟨-, -, -, rfl⟩⟩ := h
    · exact (wdevStepFrame hs).2.2.2.2.2.1
    · exact ⟨[], by simp⟩
  | power =>
    obtain ⟨-, -, ⟨-, -, rfl⟩ | ⟨hoff, -, -⟩⟩ := h
    · exact ⟨[], by simp⟩
    · rw [hpow rfl] at hoff; cases hoff

/-- ... and the PowerOn arm's own statement: the log is RESET. -/
theorem wprimStepPoweronLog (g : WGState) (κ : List Empty) (e' : WExpr) (g' : WGState)
    (efs : List WExpr) : wprimStep .power g κ e' g' efs → g.wgpow = false → g'.wglog = [] := by
  intro h hoff
  obtain ⟨-, -, ⟨hon, -⟩ | ⟨-, -, -, -, hb⟩⟩ := h
  · rw [hon] at hoff; cases hoff
  · exact wbootFactsLog g' hb

/-- THE ERA-INITIAL IMAGE IS FIXED for the whole generation. -/
theorem wprimStepImg (e : WExpr) (g : WGState) (κ : List Empty) (e' : WExpr) (g' : WGState)
    (efs : List WExpr) :
    wprimStep e g κ e' g' efs → (e = .power → g.wgpow = true) → g'.wgimg = g.wgimg := by
  intro h hpow
  cases e with
  | loop gen cpu =>
    obtain ⟨-, -, -, ⟨-, tick, u, s', -, rfl⟩ | ⟨-, rfl⟩⟩ := h <;> rfl
  | dev gen d tid m =>
    obtain ⟨-, ⟨-, m', -, hs⟩ | ⟨-, -, -, rfl⟩⟩ := h
    · exact (wdevStepFrame hs).1
    · rfl
  | power =>
    obtain ⟨-, -, ⟨-, -, rfl⟩ | ⟨hoff, -, -⟩⟩ := h
    · rfl
    · rw [hpow rfl] at hoff; cases hoff

/-- THE DURABLE DISK IMAGE: a hart step keeps it. -/
theorem wprimStepLoopDiskOf (gen : Nat) (cpu : CPU) (g : WGState) (κ : List Empty) (e' : WExpr)
    (g' : WGState) (efs : List WExpr) :
    wprimStep (.loop gen cpu) g κ e' g' efs → diskOf g'.wgdev = diskOf g.wgdev := by
  intro h
  obtain ⟨-, -, -, ⟨-, tick, u, s', hrun, rfl⟩ | ⟨-, rfl⟩⟩ := h
  · exact wrunDiskOf _ _ _ _ _ hrun
  · rfl

/-- ... and so does every device other than the disk. -/
theorem wprimStepDevDiskOf (gen : Nat) (d : DevId) (tid : TaskId) (m : DevProg d) (g : WGState)
    (κ : List Empty) (e' : WExpr) (g' : WGState) (efs : List WExpr) :
    wprimStep (.dev gen d tid m) g κ e' g' efs → d ≠ .virtio → diskOf g'.wgdev = diskOf g.wgdev := by
  intro h hd
  obtain ⟨-, ⟨-, m', -, hs⟩ | ⟨-, -, -, rfl⟩⟩ := h
  · exact (wdevStepFrame hs).2.2.2.2.2.2 hd
  · rfl

/-- VIEWS ONLY RISE, AND ONLY THE STEPPING HART'S. -/
theorem wprimStepLoopWsOther (gen : Nat) (cpu : CPU) (g : WGState) (κ : List Empty) (e' : WExpr)
    (g' : WGState) (efs : List WExpr) (c : CPU) :
    wprimStep (.loop gen cpu) g κ e' g' efs → c ≠ cpu → g'.wgws c = g.wgws c := by
  intro h hne
  obtain ⟨-, -, -, ⟨-, tick, u, s', -, rfl⟩ | ⟨-, rfl⟩⟩ := h
  · exact whartWriteWsNe g cpu s' c hne
  · rfl

theorem wprimStepLoopWsLe (gen : Nat) (cpu : CPU) (g : WGState) (κ : List Empty) (e' : WExpr)
    (g' : WGState) (efs : List WExpr) :
    wprimStep (.loop gen cpu) g κ e' g' efs → wsLe (g.wgws cpu) (g'.wgws cpu) := by
  intro h
  obtain ⟨-, -, -, ⟨-, tick, u, s', hrun, rfl⟩ | ⟨-, rfl⟩⟩ := h
  · rw [whartWriteWsEq]
    exact wrunWsLe _ _ _ _ _ hrun
  · exact wsLeRefl _

theorem wprimStepDevWs (gen : Nat) (d : DevId) (tid : TaskId) (m : DevProg d) (g : WGState)
    (κ : List Empty) (e' : WExpr) (g' : WGState) (efs : List WExpr) :
    wprimStep (.dev gen d tid m) g κ e' g' efs → g'.wgws = g.wgws := by
  intro h
  obtain ⟨-, ⟨-, m', -, hs⟩ | ⟨-, -, -, rfl⟩⟩ := h
  · exact (wdevStepFrame hs).2.1
  · rfl

/-! ## 10. Reducibility helpers -/

theorem wprimStepLoopDead (gen : Nat) (cpu : CPU) (g : WGState) :
    ¬ wthreadLive g gen → wprimStep (.loop gen cpu) g [] (.loop gen cpu) g [] :=
  fun hd => ⟨rfl, rfl, rfl, Or.inr ⟨hd, rfl⟩⟩

theorem wprimStepDevDead (gen : Nat) (d : DevId) (tid : TaskId) (m : DevProg d) (g : WGState) :
    ¬ wthreadLive g gen → wprimStep (.dev gen d tid m) g [] (.dev gen d tid m) g [] :=
  fun hd => ⟨rfl, Or.inr ⟨hd, rfl, rfl, rfl⟩⟩

theorem wprimStepPowerOff (g : WGState) :
    g.wgpow = true →
    wprimStep .power g [] .power { g with wggen := g.wggen + 1, wgpow := false } [] :=
  fun hon => ⟨rfl, rfl, Or.inl ⟨hon, rfl, rfl⟩⟩

/-- A LIVE device thread always steps (Rocq `wprim_step_uart_idle` /
`wprim_step_disk_idle`, deviation 2). -/
theorem wprimStepDevLive (gen : Nat) (d : DevId) (tid : TaskId) (m : DevProg d) (g : WGState) :
    wthreadLive g gen → ∃ e' g' efs, wprimStep (.dev gen d tid m) g [] e' g' efs := by
  intro hl
  obtain ⟨m', g', efs, hs⟩ := wdevStepTotal gen d tid m g
  exact ⟨.dev gen d tid m', g', efs, rfl, Or.inl ⟨hl, m', rfl, hs⟩⟩

end Weak
