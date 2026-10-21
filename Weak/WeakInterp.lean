/-
Weak: **the weak-memory interpreter over the real Sail monad** (M1a).

Rocq: `iris/WeakInterp.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance: the RVWMO-class analogue of the SC interpreter
(`RiscvLang.run` / `RiscvExec.exec`): one fetch-decode-execute cycle of the
generated model, interpreted over the promise-free view machine of
`Weak/WeakMem.lean` instead of a flat byte map (design doc
`claude-notes/design/weak-memory.md`).
- `Wmstate` is the SC machine state with the byte map replaced by an era-initial
  image + the global write log + this agent's `Wstate` (and, under O2 Stage B,
  the hart's instruction view `wmItv`).
- `wrun` is relational: a weak load ∃-quantifies the per-byte timestamps it read.
- `wexec` is the functional mirror threading a READ ORACLE (design doc,
  Decision 4): each RAM `memRead` pops one per-byte timestamp list, CHECKS
  admissibility, and returns the unconsumed remainder.
- `wexecWrun` is the soundness half of the SC `exec_run_det`; full determinism is
  false by design (a weak read has many admissible results), but
  `wreadBytesComplete` says the oracle can always be chosen to match any
  admissible read.
(The Rocq IMPORT DISCIPLINE paragraph is about Rocq's `Countable_mword` trap; it
has no Lean content.  This file imports `MachCSL.DiskOf`, hence `MachCSL.Lang`,
for the register file, the device fabric and the disk-image projection.)

**O2: the Lean (MachCSL) access-kind semantics** (owner decision O2,
`notes/weak-port-o2-design.md`, owner decisions D1–D5 in
`notes/weak-port-architecture.md`).  The Rocq §3 "THREE FINDINGS" note said the
Rocq model never emits `AK_ifetch`/`AK_ttw` (fetch and walk both landed in
`Read_plain`), so the Rocq `ak_coh` arm was dead.  The Lean model (sail-riscv
`070832a1`) DOES tag them (`PhysMemInterface.read_ram`: `Read_ifetch ↦ AK_ifetch`,
`Read_ttw ↦ AK_ttw`), and the weak tier follows MachCSL (`MachCSL.evStep`):
- `classify k = ⟨akIfetch k, akExcl k, akAcq k⟩` — BY DEFINITION MachCSL's
  classifiers (`MachCSL/TsoMem.lean`), so the weak dispatch is MachCSL's.
  `AK_ifetch ↦ ⟨true,false,false⟩` (the i-cache read); `AK_ttw ↦
  ⟨false,false,false⟩` (a plain read, MachCSL's `akPlain`, Rocq Decision 6's
  "walks are plain weak loads"); explicit/arch kinds as in Rocq.  The record's
  first field is Rocq `ak_coh` RENAMED `akIfetch`: it now means "i-cache read",
  not "coherent/latest read", and it is LIVE.  Findings (2) (no `AV_atomic_rmw`)
  and (3) (plain `.aq` loads are an internal error) are unaffected.
- The i-cache read (design §1.2, D3 per-byte): byte `a` may return timestamp `t`
  when `t` writes `a` and nothing writes `a` in `(t, max t itv]`
  (`Weak.ifetchByteOk`, `Weak/WeakPromise.lean`): `t` is latest at SOME view
  `tvn ≥ itv`.  No `readable`, no load pre-view, no coherence floor, no forward
  bank; the post-state is the IDENTITY (`wreadPost`'s `akIfetch` arm, the same
  line as Rocq's, new reason).  MachCSL's single footprint-wide `tvn` is one
  per-byte choice, so MachCSL's fetch is admitted here (one-way, D3).
- `wexec`'s i-cache arm CONSUMES THE ORACLE like every RAM read (Rocq read the
  computed `coh_ts` without the oracle): any admissible fetch is some oracle
  choice, so `wreadBytesComplete` holds for it too.

**Stage B (owner decision D2: modelled now).  Design choices made here:**
- B1. WHERE `itv` LIVES: OUTSIDE `Wstate`, as the sixth field `wmItv : Nat` of
  `Wmstate` (design §1.2: `wmstate.wmItv`).  `Wstate`, `wsLe`, `wsBounded` and
  every `WeakMem` step function are untouched, so `barrierPostLe`/`wrunWsLe`
  stand as in Rocq.  An era starts at `wmItv = 0` (the caller's reset, WeakLang).
- B2. `fence.i`: `barrierPost ws .Barrier_RISCV_i = ws` (the data views do not
  move, as in Rocq and as MachCSL's `fencePost` with neither edge), and the
  barrier arm also sets `wmItv' := itvPost ws itv b`, which for `fence.i` is
  `max itv (max ws.wVrNew ws.wVwOld)` and `itv` otherwise (`fenceIfetch`, reused
  from MachCSL).  This is MachCSL's pre-[OWN.143] `max itv (fencePost true false tv rv pub)` =
  `max itv (max tv pub)` with the data floor `tv ↦ wVrNew` and the hart's own
  last store `pub ↦ wVwOld` (`itvPostMachCSL`).  The read watermark is not
  joined (MachCSL's `acq = false`).
- B3. No forwarding into the i-cache: a hart's own store is fetchable only once
  `itv` passes it (after its own `fence.i`, through `wVwOld`), as in MachCSL.
- B4. The bound invariant: `itv ≤ |log|` is NOT part of `wsBounded`; it is the
  second conjunct of the Lean-only `wmBounded`, preserved by `wrunWmBounded`
  (the `fence.i` arm needs `wsBounded` for `wVrNew`/`wVwOld ≤ |log|`).
- B5. The PROMISE machine (`Weak/WeakPromise.lean`, `wpstep.WPIFetch`) checks an
  `LIFetch` at instruction view 0 — the sound Stage-A over-approximation at that
  tier: it has no `fence.i` label (`Barrier_RISCV_i` is an all-false `LFence`
  there) and no per-agent `itv`.  Giving it one (`paItv` + a `fence.i` label) is
  a WeakPromise/WeakEvInst change, left to the owner (see the report).
- D1 (fetches STAY graph reads in the AxSL tier) does not touch this file: the
  view tier's classification is O2's; the graph tier keeps Rocq's fetch-as-`LLoad`
  rows.  The design's §2 `LFetch` graph label is therefore NOT introduced.

**Deviations from Rocq.**

1. NAMES: as `Weak/WeakMem.lean` deviation 1 (lowerCamelCase; `wmstate` ↦
   `Wmstate`, `akinfo` ↦ `AkInfo`; fields `wm_regs` ↦ `wmRegs`, `ak_latest` ↦
   `akLatest`, `ak_sync` ↦ `akSync`).  `ak_coh` ↦ `akIfetch` (a RENAME with a
   new meaning, see O2 above).  The Rocq constructor `WMState r i l w d` is
   `⟨r, i, l, w, d, itv⟩`.
2. THE ADDRESS SEAM: `Arch.pa` is `PAddr = BitVec 64`; `pa_z a := a.toNat`,
   `z_pa z := BitVec.ofInt 64 z`.  `pa_uint_unsigned` (Rocq: `uint a =
   bv_unsigned a`, two readings of one word) becomes `paZ a = a.toNat`, `rfl`.
   `pa_add a j` is MachCSL's `a + BitVec.ofNat 64 j`.  `0 ≤ z < N` is
   `0 ≤ z ∧ z < N`.
3. THE IMAGE is a `MachCSL.Mem` (`Std.ExtTreeMap PAddr (BitVec 8)`, the type of
   MachCSL's boot image), Rocq `gmap Arch.pa (bv 8)`; `m !! a` is `m[a]?`.
4. THE MONAD: Rocq `M X` (the Rocq interface monad) is `SailM X` (lean-sail's
   `FreeM` over `Except (Sail.Error _) Outcome`); `wrun`/`wexec` are structural
   over it as Rocq's fixpoints are.  Arm-for-arm: Lean has no `GenericFail`/
   `Discard`/`ExtraOutcome`; a model `.error` node, `readRam`/`writeRam` (legacy,
   never emitted, stuck in MachCSL too) are stuck; `choose` branches in `wrun`
   and is stuck in `wexec` (as Rocq); `tlbi` is Rocq `TlbOp`; the two announce
   events are silent (the symbolic model, `notes/symbolic-model.md`).
5. READ ANSWERS are `.Ok (w, none)` (Rocq `inl (w, None)`); WRITE answers are
   `.Ok (some true)` (Rocq `inl None`), exactly MachCSL's `evStep` answer (owner decision
   2026-10-06; the model only distinguishes `Ok`/`Err`).
6. WRITE VALUES: Lean's write request carries `value : Option (BitVec (8*n))`
   (Rocq: the value itself).  A request with `value = none` is stuck (`False` /
   `none`), as in MachCSL's `evStep`.
7. `wwrite_msg`/`wwrite_msg_byte`/`_pa`/`_length` are stated at value width
   `8 * n` (Rocq: any width `{w : N} (v : bv w)`; every Rocq use is at `8 * n`),
   because MachCSL's `nthByte` is.  Widths `n : N` are `n : Nat`.
8. O2 statement changes (each consequence of the classification):
   - `classify`: the `AK_ttw` arm is `⟨false,false,false⟩` (Rocq `AkInfo true
     false false`); the definition is MachCSL's classifiers (the Rocq arm shapes
     are the lemmas `classifyExplicit`/`classifyIfetch`/`classifyTtw`/
     `classifyArch`).
   - `wbyte_ok`/`wbyte_okb`: the `ak_coh` branch `¬ writes_in log a t |log|`
     becomes the i-cache branch `¬ writesIn log a t (max t itv)`.
   - `wexec`: the i-cache arm consumes the oracle (above).
   - `wread_post_coh_id` ↦ `wreadPostIfetchId` (premise `akIfetch = true`).
   - `wread_all_seen`/`wread_all_seen_bytes`: the all-seen premise is
     `if akIfetch then |log| ≤ itv else |log| ≤ load_vpre ws sync` (Rocq: the
     second disjunct only, which no longer collapses an i-cache read).
   - `barrier_post`: unchanged; the barrier arm of `wrun`/`wexec` is
     `wbarrierPost` (data views AND `itv`, Stage B).
9. `assemble_bytes`/`nth_byte_assemble_len`/`bv_eq_of_bytes` (Rocq
   `RiscvModelBytes`) are the Lean-only `assembleBytes` (over a byte function)
   /`nthByteAssembleBytes`/`bvEqOfBytes` below; `mapM_Some_1/_2` are
   `MachCSL.Stdpp.mapM_Some_1/_2`.
10. `wrun_v_disk` ↦ `wrunDiskOf` over `MachCSL.diskOf` (Rocq `v_disk (dvirtio
   _)`), via `MachCSL.devRead_diskOf`/`devWrite_diskOf`.
11. THE MMIO TEST (orchestrator decision 2026-10-06, for `Weak/WeakBridge.lean`'s
   arm-for-arm port against `Weak/Exec.lean`): the device arms of `wrun`/`wexec`
   fire on `Weak.mmioAcc req.pa n = (devAddr req.pa && n != 0)` (Exec deviation
   2), Rocq `dev_addr pa`.  The two differ only on zero-width accesses, which the
   model never emits; a zero-width access at a device address is a no-op RAM
   access here, as in `exec` and `runRW`.  (`wrun` changes with `wexec` so that
   `wexecWrun` and `WeakExec.wrunWexec` stay arm-for-arm.)

**File-qualified names** (orchestrator rule: a Rocq name defined in more than
one Rocq file is declared `Weak.WeakInterp.<name>`; `notes/weak-port-dupnames.json`):
`WeakInterp.accAddr`, `WeakInterp.accAddr0`, `WeakInterp.paZZPa`,
`WeakInterp.paZRange`.

**Rocq → Lean name map.**  `pa_z` `paZ`, `z_pa` `zPa`, `acc_addr` `accAddr`,
`pa_uint_unsigned` `paUintUnsigned`, `z_pa_pa_z` `zPaPaZ`, `pa_z_z_pa` `paZZPa`,
`pa_z_range` `paZRange`, `z_pa_inj` `zPaInj`, `acc_addr_0` `accAddr0`, `img_z`
`imgZ`, `img_z_lookup` `imgZLookup`, `pa_z_add` `paZAdd`, `wmstate` `Wmstate`,
`wset_reg` `wsetReg`, `wset_dev` `wsetDev`, `wset_ws` `wsetWs`, `wimg` `wimg`,
`akinfo` `AkInfo`, `av_latest` `avLatest`, `as_sync` `asSync`, `classify`
`classify`, `barrier_post` `barrierPost`, `barrier_post_le` `barrierPostLe`,
`wbyte_ok` `wbyteOk`, `wbyte_okb` `wbyteOkb`, `wbyte_read` `wbyteRead`,
`wbyte_read_ok` `wbyteReadOk`, `wbyte_ok_read` `wbyteOkRead`, `wread_ok`
`wreadOk`, `wread_post` `wreadPost`, `wread_bytes` `wreadBytes`,
`wread_bytes_spec` `wreadBytesSpec`, `wread_bytes_complete`
`wreadBytesComplete`, `coh_ts` `cohTs`, `coh_ts_length` `cohTsLength`,
`coh_ts_lookup` `cohTsLookup`, `wm_class_of` `wmClassOf`, `wwrite_msg`
`wwriteMsg`, `wwrite_msg_byte` `wwriteMsgByte`, `wwrite_msg_pa` `wwriteMsgPa`,
`wwrite_msg_length` `wwriteMsgLength`, `wwrite_post` `wwritePost`, `wrun`
`wrun`, `wexec` `wexec`, `wexec_wrun` `wexecWrun`, `wexec_det` `wexecDet`,
`wread_post_regs/img/log/dev` `wreadPostRegs/Img/Log/Dev`, `wread_post_coh_id`
`wreadPostIfetchId`, `wwrite_post_log` `wwritePostLog`, `wread_post_ws_le`
`wreadPostWsLe`, `wwrite_post_ws_le` `wwritePostWsLe`, `wrun_v_disk`
`wrunDiskOf`, `wrun_img` `wrunImg`, `wrun_log_app` `wrunLogApp`,
`wrun_log_tid` `wrunLogTid`, `wrun_ws_le` `wrunWsLe`, `wread_all_seen`
`wreadAllSeen`, `wread_all_seen_bytes` `wreadAllSeenBytes`,
`barrier_post_bounded` `barrierPostBounded`, `wbyte_ok_bounded`
`wbyteOkBounded`, `wread_ok_ts_bounded` `wreadOkTsBounded`,
`wread_post_bounded` `wreadPostBounded`, `wwrite_post_bounded`
`wwritePostBounded`, `wrun_ws_bounded` `wrunWsBounded`, `wexec_ws_bounded`
`wexecWsBounded`.
Lean-only (no Rocq twin): `classifyExplicit/Ifetch/Ttw/Arch`,
`classifyAkIfetch/AkLatest/AkSync`, `classifyPlainIff`, `itvPost`,
`itvPostLe`, `itvPostI`, `itvPostNotI`, `itvPostMachCSL`, `itvPostBounded`,
`barrierPostI`, `wbarrierPost` (+ field lemmas), `wbyteOkIfetch`,
`wreadOkIfetch`, `wreadPostItv`, `wwritePostItv`, `assembleBytes`,
`nthByteAssembleBytes`, `bvEqOfBytes`, `forall2MapOfForall`, `getBangLt`,
`wrunStepInd` (the shared induction of the `wrun_*` lemmas), `wrunItvLe`,
`wmBounded`, `wrunWmBounded`, `wexecWmBounded`.

**Not ported:** nothing — every Rocq definition and lemma has a Lean twin.  (The
Rocq "FULL ORACLE-COMPLETENESS" comment is a non-result, kept below.)

**Statements checked** (diffed against Rocq by hand): all of them; the changed
ones are listed under deviation 8.
-/
import Weak.WeakPromise
import Weak.Exec
import MachCSL.DiskOf

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D

/-! ## 1. The address seam

Everything in `WeakMem` is keyed by `Int`; the machine's memory by `PAddr`.  Byte
`j` of an access based at `pa` is at `WeakInterp.accAddr pa j = paZ pa + j`, NOT at
`paZ (pa + j)`: the two agree exactly when the access does not wrap
(`paZAdd`), so the wrap-freedom obligation appears ONCE, at the points-to bridge
where `ramBytes` is in hand. -/

def paZ (a : PAddr) : Int := (a.toNat : Int)
def zPa (z : Int) : PAddr := BitVec.ofInt 64 z
def WeakInterp.accAddr (a : PAddr) (j : Nat) : Int := paZ a + (j : Int)

theorem paUintUnsigned (a : PAddr) : paZ a = (a.toNat : Int) := rfl

theorem zPaPaZ (a : PAddr) : zPa (paZ a) = a := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  simp only [zPa, paZ, BitVec.toNat_ofInt]
  omega

/-- The other direction, valid exactly on the address space. -/
theorem WeakInterp.paZZPa (z : Int) : 0 ≤ z ∧ z < 18446744073709551616 → paZ (zPa z) = z := by
  rintro ⟨h0, h1⟩
  simp only [paZ, zPa, BitVec.toNat_ofInt]
  omega

theorem WeakInterp.paZRange (a : PAddr) : 0 ≤ paZ a ∧ paZ a < 18446744073709551616 := by
  have := a.isLt
  simp only [paZ]
  omega

/-- `zPa` is injective on the address space. -/
theorem zPaInj (z1 z2 : Int) :
    0 ≤ z1 ∧ z1 < 18446744073709551616 → 0 ≤ z2 ∧ z2 < 18446744073709551616 →
    zPa z1 = zPa z2 → z1 = z2 := by
  intro h1 h2 heq
  rw [← WeakInterp.paZZPa z1 h1, ← WeakInterp.paZZPa z2 h2, heq]

theorem WeakInterp.accAddr0 (a : PAddr) : WeakInterp.accAddr a 0 = paZ a := by
  simp [WeakInterp.accAddr]

/-- The era-initial image, read through the seam. -/
def imgZ (m : Mem) : Image := fun z => m[zPa z]?

theorem imgZLookup (m : Mem) (a : PAddr) : imgZ m (paZ a) = m[a]? := by
  simp only [imgZ, zPaPaZ]

/-- The wrap-freedom side condition, stated once. -/
theorem paZAdd (a : PAddr) (j : Nat) :
    paZ a + (j : Int) < 18446744073709551616 → paZ (a + BitVec.ofNat 64 j) = WeakInterp.accAddr a j := by
  intro hfit
  have := a.isLt
  simp only [paZ, WeakInterp.accAddr, BitVec.toNat_add, BitVec.toNat_ofNat] at hfit ⊢
  omega

/-! ## 2. The machine state -/

/-- One hart's view of the weak machine: its own registers, the ERA-INITIAL image
(timestamp 0), the global write log, its own weak state, its view of the device
fabric, and (O2 Stage B, decision B1) its INSTRUCTION VIEW. -/
structure Wmstate where
  wmRegs : RegFile
  wmImg : Mem
  wmLog : List Wmsg
  wmWs : Wstate
  wmDev : DevStates
  /-- the hart's instruction view (O2 Stage B): raised only by `fence.i` -/
  wmItv : Nat

def wsetReg (s : Wmstate) (r : Register) (v : RegisterType r) : Wmstate :=
  { s with wmRegs := s.wmRegs.set r v }

def wsetDev (s : Wmstate) (d : DevStates) : Wmstate := { s with wmDev := d }

def wsetWs (s : Wmstate) (ws : Wstate) : Wmstate := { s with wmWs := ws }

/-- The image, as `WeakMem` wants it. -/
def wimg (s : Wmstate) : Image := imgZ s.wmImg

/-! ## 3. Access-kind dispatch (O2: MachCSL's classifiers)

What the Lean model emits (`model/Lean_RV64D/LeanRV64D/PhysMemInterface.lean`,
`read_ram`/`write_ram`): plain loads/stores `AK_explicit{plain,normal}`;
INSTRUCTION FETCH `AK_ifetch ()`; PAGE-TABLE WALK `AK_ttw ()`; LR/SC/AMO halves
`AK_explicit{exclusive, normal | rel_or_acq}`; the `.aqrl` strong forms
`AK_arch{exclusive}`.  The Rocq findings (2) and (3) carry over: no
`AV_atomic_rmw` is emitted, and acquire ordering only arrives on an exclusive
access.  Finding (1) is VOID here (see the header). -/

/-- The three Booleans every weak rule branches on.  `akIfetch` (Rocq `ak_coh`,
renamed): the i-cache read; `akLatest`: an exclusive / RMW access, must read the
global latest; `akSync`: release-or-acquire. -/
structure AkInfo where
  akIfetch : Bool
  akLatest : Bool
  akSync : Bool
  deriving DecidableEq, Inhabited, Repr

def avLatest (v : Access_variety) : Bool :=
  match v with
  | .AV_plain => false
  | .AV_exclusive => true
  | .AV_atomic_rmw => true

def asSync (st : Access_strength) : Bool :=
  match st with
  | .AS_normal => false
  | .AS_rel_or_acq => true
  | .AS_acq_rcpc => true

/-- O2: the classification IS MachCSL's (`akIfetch`/`akExcl`/`akAcq`). -/
def classify (k : AK) : AkInfo := ⟨akIfetch k, akExcl k, akAcq k⟩

theorem classifyAkIfetch (k : AK) : (classify k).akIfetch = akIfetch k := rfl
theorem classifyAkLatest (k : AK) : (classify k).akLatest = akExcl k := rfl
theorem classifyAkSync (k : AK) : (classify k).akSync = akAcq k := rfl

/-- The Rocq arm shapes, as lemmas. -/
theorem classifyExplicit (e : Explicit_access_kind) :
    classify (.AK_explicit e) = ⟨false, avLatest e.variety, asSync e.strength⟩ := by
  obtain ⟨v, st⟩ := e
  cases v <;> cases st <;> rfl

theorem classifyIfetch : classify (.AK_ifetch ()) = ⟨true, false, false⟩ := rfl

/-- O2: a page-table walk is a PLAIN read (Rocq: `AkInfo true false false`). -/
theorem classifyTtw : classify (.AK_ttw ()) = ⟨false, false, false⟩ := rfl

theorem classifyArch (a : RISCV_strong_access) :
    classify (.AK_arch a) = ⟨false, avLatest a.variety, true⟩ := by
  obtain ⟨v⟩ := a
  cases v <;> rfl

/-- The plain arm is exactly MachCSL's `akPlain`. -/
theorem classifyPlainIff (k : AK) :
    ((classify k).akIfetch = false ∧ (classify k).akLatest = false) ↔ akPlain k = true := by
  simp [classify, akPlain]

/-- The barrier lattice (design doc, the FENCE rule).  `fence.tso` is
`fence r,r ; fence rw,w`; `fence.i` moves no DATA view (its i-cache effect is
`itvPost`, Stage B). -/
def barrierPost (ws : Wstate) (b : barrier_kind) : Wstate :=
  match b with
  | .Barrier_RISCV_rw_rw => Weak.fencePost ws true true true true
  | .Barrier_RISCV_r_rw => Weak.fencePost ws true false true true
  | .Barrier_RISCV_r_r => Weak.fencePost ws true false true false
  | .Barrier_RISCV_rw_w => Weak.fencePost ws true true false true
  | .Barrier_RISCV_w_w => Weak.fencePost ws false true false true
  | .Barrier_RISCV_w_rw => Weak.fencePost ws false true true true
  | .Barrier_RISCV_rw_r => Weak.fencePost ws true true true false
  | .Barrier_RISCV_r_w => Weak.fencePost ws true false false true
  | .Barrier_RISCV_w_r => Weak.fencePost ws false true true false
  | .Barrier_RISCV_tso =>
      Weak.fencePost (Weak.fencePost ws true false true false) true true false true
  | .Barrier_RISCV_i => ws

/-- A fence only ever RAISES the view floors. -/
theorem barrierPostLe (ws : Wstate) (b : barrier_kind) : wsLe ws (barrierPost ws b) := by
  cases b <;> simp only [barrierPost]
  all_goals first
    | exact wsLeRefl _
    | exact fencePostLe _ _ _ _ _
    | exact wsLeTrans (fencePostLe _ _ _ _ _) (fencePostLe _ _ _ _ _)

theorem barrierPostI (ws : Wstate) : barrierPost ws .Barrier_RISCV_i = ws := rfl

/-- STAGE B (decision B2): the instruction view after barrier `b`.  Only
`fence.i` moves it, past the data floor and the hart's own last store. -/
def itvPost (ws : Wstate) (itv : Nat) (b : barrier_kind) : Nat :=
  if fenceIfetch b then max itv (max ws.wVrNew ws.wVwOld) else itv

theorem itvPostLe (ws : Wstate) (itv : Nat) (b : barrier_kind) : itv ≤ itvPost ws itv b := by
  unfold itvPost; split <;> omega

theorem itvPostI (ws : Wstate) (itv : Nat) :
    itvPost ws itv .Barrier_RISCV_i = max itv (max ws.wVrNew ws.wVwOld) := rfl

theorem itvPostNotI (ws : Wstate) (itv : Nat) (b : barrier_kind) :
    fenceIfetch b = false → itvPost ws itv b = itv := by
  intro h; simp [itvPost, h]

/-- The pre-[OWN.143] MachCSL shape (`MState.fence` before F1 joined `rv`): `max itv (fencePost true false tv rv pub)`
with `tv ↦ wVrNew`, `pub ↦ wVwOld` (the read watermark is not joined). -/
theorem itvPostMachCSL (ws : Wstate) (itv rv : Nat) (b : barrier_kind) :
    itvPost ws itv b =
      if fenceIfetch b then max itv (MachCSL.fencePost true false ws.wVrNew rv ws.wVwOld) else itv := by
  unfold itvPost MachCSL.fencePost
  split
  · simp only [↓reduceIte, Bool.false_eq_true]; omega
  · rfl

theorem itvPostBounded (ws : Wstate) (itv : Nat) (b : barrier_kind) (n : Nat) :
    wsBounded ws n → itv ≤ n → itvPost ws itv b ≤ n := by
  intro hb hi
  have h1 := hb.2.1
  have h2 := hb.2.2.1
  unfold itvPost; split <;> omega

/-- The barrier arm's post-state: data views AND instruction view. -/
def wbarrierPost (s : Wmstate) (b : barrier_kind) : Wmstate :=
  { s with wmWs := barrierPost s.wmWs b, wmItv := itvPost s.wmWs s.wmItv b }

theorem wbarrierPostWs (s : Wmstate) (b : barrier_kind) :
    (wbarrierPost s b).wmWs = barrierPost s.wmWs b := rfl
theorem wbarrierPostItv (s : Wmstate) (b : barrier_kind) :
    (wbarrierPost s b).wmItv = itvPost s.wmWs s.wmItv b := rfl
theorem wbarrierPostLog (s : Wmstate) (b : barrier_kind) : (wbarrierPost s b).wmLog = s.wmLog := rfl
theorem wbarrierPostImg (s : Wmstate) (b : barrier_kind) : (wbarrierPost s b).wmImg = s.wmImg := rfl
theorem wbarrierPostDev (s : Wmstate) (b : barrier_kind) : (wbarrierPost s b).wmDev = s.wmDev := rfl
theorem wbarrierPostRegs (s : Wmstate) (b : barrier_kind) :
    (wbarrierPost s b).wmRegs = s.wmRegs := rfl

/-! ## 4. Reads: admissibility, the post-state, and the decision procedure -/

/-- One byte of a read: timestamp `t` holds value `b` at `a`, and `t` is
admissible for this access kind (O2: the i-cache arm is `ifetchByteOk`'s window). -/
def wbyteOk (s : Wmstate) (ak : AkInfo) (a : Int) (t : Nat) (b : BitVec 8) : Prop :=
  logByte (wimg s) s.wmLog t a = some b ∧
  (if ak.akIfetch then ¬ writesIn s.wmLog a t (max t s.wmItv)
   else readable (wimg s) s.wmLog s.wmWs (loadVpre s.wmWs ak.akSync) a t ∧
        (ak.akLatest = true → ¬ writesIn s.wmLog a t s.wmLog.length))

def wbyteOkb (s : Wmstate) (ak : AkInfo) (a : Int) (t : Nat) : Bool :=
  match logByte (wimg s) s.wmLog t a with
  | none => false
  | some _ =>
      if ak.akIfetch
      then !(writesInb s.wmLog a t (max t s.wmItv))
      else readableb (wimg s) s.wmLog s.wmWs (loadVpre s.wmWs ak.akSync) a t &&
           (if ak.akLatest then !(writesInb s.wmLog a t s.wmLog.length) else true)

def wbyteRead (s : Wmstate) (ak : AkInfo) (a : Int) (t : Nat) : Option (BitVec 8) :=
  if wbyteOkb s ak a t then logByte (wimg s) s.wmLog t a else none

theorem wbyteReadOk (s : Wmstate) (ak : AkInfo) (a : Int) (t : Nat) (b : BitVec 8) :
    wbyteRead s ak a t = some b → wbyteOk s ak a t b := by
  unfold wbyteRead wbyteOkb wbyteOk
  cases hv : logByte (wimg s) s.wmLog t a with
  | none => simp
  | some v =>
    simp only [Option.some.injEq]
    cases hc : ak.akIfetch with
    | true =>
      simp only [↓reduceIte, Bool.not_eq_true']
      split
      · rename_i hw; intro hb; exact ⟨by simp only [Option.some.injEq] at hb ⊢; exact hb, notWritesInCompute _ _ _ _ hw⟩
      · intro h; cases h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases hr : readableb (wimg s) s.wmLog s.wmWs (loadVpre s.wmWs ak.akSync) a t with
      | false => simp
      | true =>
        have hrd := (readablebSpec _ _ _ _ _ _).1 hr
        cases hl : ak.akLatest with
        | true =>
          simp only [↓reduceIte, Bool.true_and, Bool.not_eq_true']
          split
          · rename_i hw; intro hb
            exact ⟨by simp only [Option.some.injEq] at hb ⊢; exact hb, hrd,
              fun _ => notWritesInCompute _ _ _ _ hw⟩
          · intro h; cases h
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_self]
          intro hb; exact ⟨by simp only [Option.some.injEq] at hb ⊢; exact hb, hrd, fun h => by cases h⟩

theorem wbyteOkRead (s : Wmstate) (ak : AkInfo) (a : Int) (t : Nat) (b : BitVec 8) :
    wbyteOk s ak a t b → wbyteRead s ak a t = some b := by
  rintro ⟨hv, hadm⟩
  unfold wbyteRead wbyteOkb
  rw [hv]
  cases hc : ak.akIfetch with
  | true =>
    rw [hc] at hadm
    simp only [↓reduceIte] at hadm ⊢
    rw [(notWritesInb _ _ _ _).2 hadm]; rfl
  | false =>
    rw [hc] at hadm
    simp only [Bool.false_eq_true, ↓reduceIte] at hadm ⊢
    obtain ⟨hrd, hlat⟩ := hadm
    rw [(readablebSpec _ _ _ _ _ _).2 hrd]
    cases hl : ak.akLatest with
    | true => rw [(notWritesInb _ _ _ _).2 (hlat hl)]; rfl
    | false => rfl

/-- O2: an i-cache byte is admissible exactly when `ifetchByteOk` holds. -/
theorem wbyteOkIfetch (s : Wmstate) (ak : AkInfo) (a : Int) (t : Nat) (b : BitVec 8) :
    ak.akIfetch = true → (wbyteOk s ak a t b ↔ ifetchByteOk (wimg s) s.wmLog s.wmItv a t b) := by
  intro hc
  simp only [wbyteOk, ifetchByteOk, hc, ↓reduceIte]

/-- A whole read: `ts` is the per-byte timestamp list, `w` the assembled
little-endian word. -/
def wreadOk (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat) (ts : List Nat)
    (w : BitVec (8 * n)) : Prop :=
  ts.length = n ∧ ∀ j : Nat, j < n → wbyteOk s ak (WeakInterp.accAddr pa j) ts[j]! (nthByte w j)

/-- The post-state.  An i-cache read (O2) leaves everything untouched; a weak read
folds `loadPost` over its bytes. -/
def wreadPost (s : Wmstate) (ak : AkInfo) (pa : PAddr) (ts : List Nat) : Wmstate :=
  if ak.akIfetch then s else wsetWs s (loadPostRun s.wmWs ak.akSync (paZ pa) ts)

/-! ### Assembling a word from its bytes (Lean helpers, deviation 9) -/

/-- The little-endian word whose byte `j < n` is `bs j`. -/
def assembleBytes : (n : Nat) → (Nat → BitVec 8) → BitVec (8 * n)
  | 0, _ => 0#0
  | n + 1, bs => BitVec.cast (by omega) (bs n ++ assembleBytes n bs)

theorem nthByteAssembleBytes : ∀ (n : Nat) (bs : Nat → BitVec 8) (j : Nat),
    j < n → nthByte (assembleBytes n bs) j = bs j
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, bs, j, hj => by
    apply BitVec.eq_of_getLsbD_eq_iff.2
    intro i hi
    simp only [assembleBytes, nthByte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_cast,
      BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
    by_cases hjn : j < n
    · have := congrArg (fun b : BitVec 8 => b.getLsbD i) (nthByteAssembleBytes n bs j hjn)
      simp only [nthByte, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and] at this
      rw [if_pos (by omega)]
      exact this
    · have hj' : j = n := by omega
      subst hj'
      rw [if_neg (by omega)]
      congr 1
      omega

/-- Two words with the same bytes are equal. -/
theorem bvEqOfBytes {n : Nat} (w w' : BitVec (8 * n)) :
    (∀ j, j < n → nthByte w j = nthByte w' j) → w = w' := by
  intro h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : i / 8 < n := by omega
  have hi8 : i % 8 < 8 := Nat.mod_lt _ (by omega)
  have := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8)) (h (i / 8) hj)
  simp only [nthByte, BitVec.getLsbD_extractLsb', hi8, decide_true, Bool.true_and] at this
  have e : 8 * (i / 8) + i % 8 = i := by omega
  rwa [e] at this

/-- A `mapM` that succeeds pointwise (Lean helper). -/
theorem forall2MapOfForall {α β : Type _} {f : α → Option β} {g : α → β} :
    ∀ l : List α, (∀ x ∈ l, f x = some (g x)) → List.Forall₂ (fun x y => f x = some y) l (l.map g)
  | [], _ => List.Forall₂.nil
  | x :: l, h => List.Forall₂.cons (h x List.mem_cons_self)
      (forall2MapOfForall l (fun y hy => h y (List.mem_cons_of_mem _ hy)))

/-- `l[j]!` in range (Lean helper). -/
theorem getBangLt {α : Type _} [Inhabited α] (l : List α) (j : Nat) (h : j < l.length) :
    l[j]! = l[j] := by
  simp [getElem!_pos, h]

/-- The functional read: check every byte, gather, assemble. -/
def wreadBytes (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat) (ts : List Nat) :
    Option (BitVec (8 * n)) :=
  if ts.length = n then
    match (List.range' 0 n).mapM (fun j : Nat => wbyteRead s ak (WeakInterp.accAddr pa j) ts[j]!) with
    | some bs => some (assembleBytes n (fun j => bs[j]?.getD 0))
    | none => none
  else none

theorem wreadBytesSpec (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat) (ts : List Nat)
    (w : BitVec (8 * n)) : wreadBytes s ak pa n ts = some w → wreadOk s ak pa n ts w := by
  unfold wreadBytes
  split
  · rename_i hlen
    cases hm : (List.range' 0 n).mapM (fun j : Nat => wbyteRead s ak (WeakInterp.accAddr pa j) ts[j]!) with
    | none => simp
    | some bs =>
      simp only [Option.some.injEq]
      intro hw
      subst hw
      refine ⟨hlen, fun j hj => ?_⟩
      have hF := mapM_Some_1 hm
      have hseq : (List.range' 0 n)[j]? = some j := by
        simp [hj]
      obtain ⟨b, hbj, hrd⟩ := Forall2_lookup_l hF hseq
      rw [nthByteAssembleBytes n _ j hj, hbj]
      exact wbyteReadOk s ak _ _ b hrd
  · simp

/-- THE ORACLE-COMPLETENESS FACT: any admissible read is accepted by `wexec` at
the matching oracle entry, and returns the same word. -/
theorem wreadBytesComplete (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat) (ts : List Nat)
    (w : BitVec (8 * n)) : wreadOk s ak pa n ts w → wreadBytes s ak pa n ts = some w := by
  rintro ⟨hlen, hbytes⟩
  unfold wreadBytes
  rw [if_pos hlen]
  have hm : (List.range' 0 n).mapM (fun j : Nat => wbyteRead s ak (WeakInterp.accAddr pa j) ts[j]!)
      = some ((List.range' 0 n).map (fun j => nthByte w j)) := by
    apply mapM_Some_2
    apply forall2MapOfForall
    intro j hj
    rw [List.mem_range'_1] at hj
    exact wbyteOkRead s ak _ _ _ (hbytes j (by omega))
  rw [hm]
  simp only [Option.some.injEq]
  apply bvEqOfBytes
  intro j hj
  rw [nthByteAssembleBytes n _ j hj, List.getElem?_map]
  simp [hj]

/-- The COMPUTED latest timestamps: per byte, the last message writing it. -/
def cohTs (s : Wmstate) (pa : PAddr) (n : Nat) : List Nat :=
  (List.range' 0 n).map (fun j : Nat => latestTs s.wmLog (WeakInterp.accAddr pa j))

theorem cohTsLength (s : Wmstate) (pa : PAddr) (n : Nat) : (cohTs s pa n).length = n := by
  simp [cohTs]

theorem cohTsLookup (s : Wmstate) (pa : PAddr) (n j : Nat) :
    j < n → (cohTs s pa n)[j]! = latestTs s.wmLog (WeakInterp.accAddr pa j) := by
  intro hj
  rw [getBangLt _ _ (by rw [cohTsLength]; exact hj)]
  simp [cohTs]

/-! ## 5. Writes

Promise-free: one message, appended at the log's fresh top.  THE TID IS A
PARAMETER of the whole interpreter (`wrun`/`wexec` take it and stamp it on every
message they append); nothing here inspects it.  THE MESSAGE CLASS (M6, D-M6-6;
inert): an exclusive write is `WCexcl`; otherwise a write with the
release-pending flag or an `.rl` write is the publication `WCrel`; else
`WCplain`. -/

def wmClassOf (ak : AkInfo) (ws : Wstate) : WmClass :=
  if ak.akLatest then .WCexcl
  else if (ws.wRelp || ak.akSync) then .WCrel else .WCplain

def wwriteMsg (tid : Option Nat) (k : WmClass) (pa : PAddr) (n : Nat) (v : BitVec (8 * n)) :
    Wmsg :=
  ⟨paZ pa, (List.range' 0 n).map (fun j : Nat => nthByte v j), tid, k⟩

theorem wwriteMsgByte (tid : Option Nat) (k : WmClass) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) (j : Nat) :
    j < n → msgByte (wwriteMsg tid k pa n v) (WeakInterp.accAddr pa j) = some (nthByte v j) := by
  intro hj
  simp only [msgByte, wwriteMsg, WeakInterp.accAddr]
  rw [if_pos (by omega)]
  have e : (paZ pa + (j : Int) - paZ pa).toNat = j := by omega
  rw [e, List.getElem?_map]
  simp [hj]

theorem wwriteMsgPa (tid : Option Nat) (k : WmClass) (pa : PAddr) (n : Nat) (v : BitVec (8 * n)) :
    (wwriteMsg tid k pa n v).wmPa = paZ pa := rfl

theorem wwriteMsgLength (tid : Option Nat) (k : WmClass) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) : (wwriteMsg tid k pa n v).wmData.length = n := by
  simp [wwriteMsg]

def wwritePost (tid : Option Nat) (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) : Wmstate :=
  { s with
    wmLog := s.wmLog ++ [wwriteMsg tid (wmClassOf ak s.wmWs) pa n v]
    wmWs := storePostRun s.wmWs ak.akSync (paZ pa) n (s.wmLog.length + 1) }

/-! ## 6. `wrun`: the relational interpreter

Structurally the SC interpreter, a structural recursion over the monad, with
three arms changed: `memRead`, `memWrite` and `barrier`.  Device addresses are
serviced synchronously; RAM reads pick per-byte timestamps. -/

def wrun (tid : Option Nat) {X : Type} : SailM X → Wmstate → X → Wmstate → Prop
  | .pure y, s, x, s' => x = y ∧ s' = s
  | .impure (.error _) _, _, _, _ => False
  | .impure (.ok o) k, s, x, s' =>
    match o, k with
    -- registers: untouched by weak memory (no register views — Decision 3)
    | .regRead r, k => wrun tid (k (s.wmRegs r)) s x s'
    | .regWrite r v, k => wrun tid (k PUnit.unit) (wsetReg s r v) x s'
    | .memRead n _ req, k =>
      if mmioAcc req.pa n then
        match devRead s.wmDev req.pa n with
        | some (w, d') => wrun tid (k (.Ok (w, none))) (wsetDev s d') x s'
        | none => False
      else
        ∃ (w : BitVec (8 * n)) (ts : List Nat),
          wreadOk s (classify req.access_kind) req.pa n ts w ∧
          wrun tid (k (.Ok (w, none))) (wreadPost s (classify req.access_kind) req.pa ts) x s'
    | .memWrite n _ req, k =>
      if mmioAcc req.pa n then
        match req.value with
        | some v =>
          match devWrite s.wmDev req.pa n v with
          | some d' => wrun tid (k (.Ok (some true))) (wsetDev s d') x s'
          | none => False
        | none => False
      else
        match req.value with
        | some v => wrun tid (k (.Ok (some true))) (wwritePost tid s (classify req.access_kind) req.pa n v) x s'
        | none => False
    -- FENCE: the view update, and (Stage B) the instruction view
    | .barrier b, k => wrun tid (k ()) (wbarrierPost s b) x s'
    -- trace / announce outcomes: state no-ops
    | .instrAnnounce _ _, k => wrun tid (k ()) s x s'
    | .branchAnnounce _ _, k => wrun tid (k ()) s x s'
    | .cacheOp _, k => wrun tid (k ()) s x s'
    | .tlbi _, k => wrun tid (k ()) s x s'
    | .takeException _, k => wrun tid (k ()) s x s'
    | .returnException _, k => wrun tid (k ()) s x s'
    | .translationStart _, k => wrun tid (k ()) s x s'
    | .translationEnd _, k => wrun tid (k ()) s x s'
    | .cycleCount, k => wrun tid (k ()) s x s'
    | .message _, k => wrun tid (k ()) s x s'
    | .getCycleCount, k => wrun tid (k (0 : Nat)) s x s'
    -- nondeterminism: branch over every choice
    | .choose _, k => ∃ c, wrun tid (k c) s x s'
    -- the legacy direct-RAM events: stuck
    | .readRam .., _ => False
    | .writeRam .., _ => False

/-! ## 7. `wexec`: the functional mirror, threading the read oracle

The oracle `χ` supplies one per-byte timestamp list per RAM read, in order (O2:
the i-cache reads included).  Every admissibility condition is CHECKED. -/

def wexec (tid : Option Nat) {X : Type} :
    SailM X → List (List Nat) → Wmstate → Option (X × Wmstate × List (List Nat))
  | .pure y, χ, s => some (y, s, χ)
  | .impure (.error _) _, _, _ => none
  | .impure (.ok o) k, χ, s =>
    match o, k with
    | .regRead r, k => wexec tid (k (s.wmRegs r)) χ s
    | .regWrite r v, k => wexec tid (k PUnit.unit) χ (wsetReg s r v)
    | .memRead n _ req, k =>
      if mmioAcc req.pa n then
        match devRead s.wmDev req.pa n with
        | some (w, d') => wexec tid (k (.Ok (w, none))) χ (wsetDev s d')
        | none => none
      else
        match χ.head? with
        | none => none
        | some ts =>
          match wreadBytes s (classify req.access_kind) req.pa n ts with
          | some w =>
            wexec tid (k (.Ok (w, none))) χ.tail (wreadPost s (classify req.access_kind) req.pa ts)
          | none => none
    | .memWrite n _ req, k =>
      if mmioAcc req.pa n then
        match req.value with
        | some v =>
          match devWrite s.wmDev req.pa n v with
          | some d' => wexec tid (k (.Ok (some true))) χ (wsetDev s d')
          | none => none
        | none => none
      else
        match req.value with
        | some v => wexec tid (k (.Ok (some true))) χ (wwritePost tid s (classify req.access_kind) req.pa n v)
        | none => none
    | .barrier b, k => wexec tid (k ()) χ (wbarrierPost s b)
    | .instrAnnounce _ _, k => wexec tid (k ()) χ s
    | .branchAnnounce _ _, k => wexec tid (k ()) χ s
    | .cacheOp _, k => wexec tid (k ()) χ s
    | .tlbi _, k => wexec tid (k ()) χ s
    | .takeException _, k => wexec tid (k ()) χ s
    | .returnException _, k => wexec tid (k ()) χ s
    | .translationStart _, k => wexec tid (k ()) χ s
    | .translationEnd _, k => wexec tid (k ()) χ s
    | .cycleCount, k => wexec tid (k ()) χ s
    | .message _, k => wexec tid (k ()) χ s
    | .getCycleCount, k => wexec tid (k (0 : Nat)) χ s
    -- choose / the legacy direct-RAM events: stuck, as in `exec`
    | .choose _, _ => none
    | .readRam .., _ => none
    | .writeRam .., _ => none

/-! ## 8. The bridge

The soundness half of the SC `exec_run_det`.  Determinism is false by design;
per-oracle determinism holds (`wexec` is a function), and `wreadBytesComplete`
supplies the converse one read at a time. -/

theorem wexecWrun (tid : Option Nat) {X : Type} (m : SailM X) :
    ∀ (χ : List (List Nat)) (s : Wmstate) (x : X) (s' : Wmstate) (χ' : List (List Nat)),
      wexec tid m χ s = some (x, s', χ') → wrun tid m s x s' := by
  induction m with
  | pure y =>
    intro χ s x s' χ' h
    simp only [wexec, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨rfl, rfl⟩
  | impure call k ih =>
    intro χ s x s' χ' h
    cases call with
    | error e => simp [wexec] at h
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [wexec] at h
        simp only [wrun]
        split at h
        · rename_i hd
          rw [if_pos hd]
          split at h
          · rename_i w d' hdr
            try rw [hdr]
            exact ih _ _ _ _ _ _ h
          · cases h
        · rename_i hd
          rw [if_neg hd]
          split at h
          · cases h
          · rename_i ts _
            split at h
            · rename_i w hrb
              exact ⟨w, ts, wreadBytesSpec _ _ _ _ _ _ hrb, ih _ _ _ _ _ _ h⟩
            · cases h
      case memWrite n va req =>
        simp only [wexec] at h
        simp only [wrun]
        split at h
        · rename_i hd
          rw [if_pos hd]
          split at h
          · rename_i v hv
            try rw [hv]
            split at h
            · rename_i d' hdw
              try rw [hdw]
              exact ih _ _ _ _ _ _ h
            · cases h
          · cases h
        · rename_i hd
          rw [if_neg hd]
          split at h
          · rename_i v hv
            try rw [hv]
            exact ih _ _ _ _ _ _ h
          · cases h
      all_goals first
        | (simp only [wexec, reduceCtorEq] at h; done)
        | (simp only [wexec] at h; simp only [wrun]; exact ih _ _ _ _ _ _ h)

/-- Per-oracle determinism, for free: `wexec` is a function. -/
theorem wexecDet (tid : Option Nat) {X : Type} (m : SailM X) (χ : List (List Nat)) (s : Wmstate)
    (x1 : X) (s1 : Wmstate) (χ1 : List (List Nat)) (x2 : X) (s2 : Wmstate)
    (χ2 : List (List Nat)) :
    wexec tid m χ s = some (x1, s1, χ1) → wexec tid m χ s = some (x2, s2, χ2) →
    x1 = x2 ∧ s1 = s2 ∧ χ1 = χ2 := by
  intro h1 h2
  rw [h1] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact h2

/- FULL ORACLE-COMPLETENESS — `wrun m s x s' → ∃ χ χ', wexec m χ s = some
(x, s', χ')` — is NOT provable, and the obstacle is `choose`, which `wrun`
branches over and `wexec` rejects; every read/write/barrier arm is complete on its
own (`wreadBytesComplete`).  (Rocq TODO(M1c): `choice_free`, never needed.) -/

/-! ## 9. Sanity lemmas -/

theorem wreadPostRegs (s : Wmstate) (ak : AkInfo) (pa : PAddr) (ts : List Nat) :
    (wreadPost s ak pa ts).wmRegs = s.wmRegs := by
  unfold wreadPost; split <;> rfl
theorem wreadPostImg (s : Wmstate) (ak : AkInfo) (pa : PAddr) (ts : List Nat) :
    (wreadPost s ak pa ts).wmImg = s.wmImg := by
  unfold wreadPost; split <;> rfl
theorem wreadPostLog (s : Wmstate) (ak : AkInfo) (pa : PAddr) (ts : List Nat) :
    (wreadPost s ak pa ts).wmLog = s.wmLog := by
  unfold wreadPost; split <;> rfl
theorem wreadPostDev (s : Wmstate) (ak : AkInfo) (pa : PAddr) (ts : List Nat) :
    (wreadPost s ak pa ts).wmDev = s.wmDev := by
  unfold wreadPost; split <;> rfl
/-- Stage B: no read moves the instruction view. -/
theorem wreadPostItv (s : Wmstate) (ak : AkInfo) (pa : PAddr) (ts : List Nat) :
    (wreadPost s ak pa ts).wmItv = s.wmItv := by
  unfold wreadPost; split <;> rfl
/-- O2: an i-cache read is view-silent (Rocq `wread_post_coh_id`). -/
theorem wreadPostIfetchId (s : Wmstate) (ak : AkInfo) (pa : PAddr) (ts : List Nat) :
    ak.akIfetch = true → wreadPost s ak pa ts = s := by
  intro h; simp [wreadPost, h]

theorem wwritePostLog (tid : Option Nat) (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) :
    (wwritePost tid s ak pa n v).wmLog = s.wmLog ++ [wwriteMsg tid (wmClassOf ak s.wmWs) pa n v] :=
  rfl
/-- Stage B: no write moves the instruction view (no forwarding into the i-cache). -/
theorem wwritePostItv (tid : Option Nat) (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) : (wwritePost tid s ak pa n v).wmItv = s.wmItv := rfl

theorem wreadPostWsLe (s : Wmstate) (ak : AkInfo) (pa : PAddr) (ts : List Nat) :
    wsLe s.wmWs (wreadPost s ak pa ts).wmWs := by
  unfold wreadPost
  split
  · exact wsLeRefl _
  · exact loadPostRunLe _ _ _ _

theorem wwritePostWsLe (tid : Option Nat) (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) : wsLe s.wmWs (wwritePost tid s ak pa n v).wmWs :=
  storePostRunLe _ _ _ _ _

/-- THE SHARED INDUCTION of the `wrun_*` lemmas (Lean helper): a reflexive,
transitive relation that every state-moving arm establishes holds of the whole
run. -/
theorem wrunStepInd (tid : Option Nat) (Q : Wmstate → Wmstate → Prop)
    (hrefl : ∀ s, Q s s)
    (htrans : ∀ s1 s2 s3, Q s1 s2 → Q s2 s3 → Q s1 s3)
    (hreg : ∀ s (r : Register) (v : RegisterType r), Q s (wsetReg s r v))
    (hdevr : ∀ s pa n (w : BitVec (8 * n)) d', devRead s.wmDev pa n = some (w, d') →
      Q s (wsetDev s d'))
    (hdevw : ∀ s pa n (w : BitVec (8 * n)) d', devWrite s.wmDev pa n w = some d' →
      Q s (wsetDev s d'))
    (hread : ∀ s ak pa n ts (w : BitVec (8 * n)), wreadOk s ak pa n ts w →
      Q s (wreadPost s ak pa ts))
    (hwrite : ∀ s ak pa n (v : BitVec (8 * n)), Q s (wwritePost tid s ak pa n v))
    (hbar : ∀ s b, Q s (wbarrierPost s b)) :
    ∀ {X : Type} (m : SailM X) (s : Wmstate) (x : X) (s' : Wmstate), wrun tid m s x s' → Q s s' := by
  intro X m
  induction m with
  | pure y =>
    intro s x s' h
    rw [h.2]
    exact hrefl s
  | impure call k ih =>
    intro s x s' h
    cases call with
    | error e => exact h.elim
    | ok o =>
      cases o
      case regWrite r v =>
        simp only [wrun] at h
        exact htrans _ _ _ (hreg s r v) (ih _ _ _ _ h)
      case memRead n va req =>
        simp only [wrun] at h
        split at h
        · split at h
          · rename_i w d' hdr
            exact htrans _ _ _ (hdevr s _ _ w d' hdr) (ih _ _ _ _ h)
          · exact h.elim
        · obtain ⟨w, ts, hok, h⟩ := h
          exact htrans _ _ _ (hread s _ _ _ ts w hok) (ih _ _ _ _ h)
      case memWrite n va req =>
        simp only [wrun] at h
        split at h
        · split at h
          · rename_i v _
            split at h
            · rename_i d' hdw
              exact htrans _ _ _ (hdevw s _ _ v d' hdw) (ih _ _ _ _ h)
            · exact h.elim
          · exact h.elim
        · split at h
          · rename_i v _
            exact htrans _ _ _ (hwrite s _ _ _ v) (ih _ _ _ _ h)
          · exact h.elim
      case barrier b =>
        simp only [wrun] at h
        exact htrans _ _ _ (hbar s b) (ih _ _ _ _ h)
      case choose p =>
        simp only [wrun] at h
        obtain ⟨c, h⟩ := h
        exact ih _ _ _ _ h
      case readRam => exact h.elim
      case writeRam => exact h.elim
      all_goals (simp only [wrun] at h; exact ih _ _ _ _ h)

/-- A CPU step never moves the disk IMAGE (Rocq `wrun_v_disk`). -/
theorem wrunDiskOf (tid : Option Nat) {X : Type} (m : SailM X) :
    ∀ (s : Wmstate) (x : X) (s' : Wmstate), wrun tid m s x s' → diskOf s'.wmDev = diskOf s.wmDev := by
  intro s x s' h
  exact wrunStepInd tid (fun s s' => diskOf s'.wmDev = diskOf s.wmDev)
    (fun _ => rfl) (fun _ _ _ h1 h2 => h2.trans h1) (fun _ _ _ => rfl)
    (fun _ _ _ _ _ h => devRead_diskOf _ _ _ _ _ h) (fun _ _ _ _ _ h => devWrite_diskOf _ _ _ _ _ h)
    (fun s ak pa _ ts _ _ => by
      show diskOf (wreadPost s ak pa ts).wmDev = diskOf s.wmDev
      rw [wreadPostDev]) (fun _ _ _ _ _ => rfl) (fun _ _ => rfl)
    m s x s' h

/-- THE ERA-INITIAL IMAGE IS NEVER WRITTEN. -/
theorem wrunImg (tid : Option Nat) {X : Type} (m : SailM X) :
    ∀ (s : Wmstate) (x : X) (s' : Wmstate), wrun tid m s x s' → s'.wmImg = s.wmImg := by
  intro s x s' h
  exact wrunStepInd tid (fun s s' => s'.wmImg = s.wmImg)
    (fun _ => rfl) (fun _ _ _ h1 h2 => h2.trans h1) (fun _ _ _ => rfl)
    (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ _ => wreadPostImg _ _ _ _) (fun _ _ _ _ _ => rfl) (fun _ _ => rfl)
    m s x s' h

/-- THE LOG IS APPEND-ONLY. -/
theorem wrunLogApp (tid : Option Nat) {X : Type} (m : SailM X) :
    ∀ (s : Wmstate) (x : X) (s' : Wmstate), wrun tid m s x s' → ∃ l, s'.wmLog = s.wmLog ++ l := by
  intro s x s' h
  exact wrunStepInd tid (fun s s' => ∃ l, s'.wmLog = s.wmLog ++ l)
    (fun _ => ⟨[], by simp⟩)
    (fun _ _ _ ⟨l1, h1⟩ ⟨l2, h2⟩ => ⟨l1 ++ l2, by rw [h2, h1, List.append_assoc]⟩)
    (fun _ _ _ => ⟨[], by simp [wsetReg]⟩)
    (fun _ _ _ _ _ _ => ⟨[], by simp [wsetDev]⟩) (fun _ _ _ _ _ _ => ⟨[], by simp [wsetDev]⟩)
    (fun _ _ _ _ _ _ _ => ⟨[], by rw [wreadPostLog]; simp⟩)
    (fun s ak pa n v => ⟨[wwriteMsg tid (wmClassOf ak s.wmWs) pa n v], rfl⟩)
    (fun _ _ => ⟨[], by simp [wbarrierPost]⟩)
    m s x s' h

/-- ... and WHOSE messages they are: every appended message carries `tid`. -/
theorem wrunLogTid (tid : Option Nat) {X : Type} (m : SailM X) :
    ∀ (s : Wmstate) (x : X) (s' : Wmstate), wrun tid m s x s' →
      ∃ l, s'.wmLog = s.wmLog ++ l ∧ ∀ mg ∈ l, mg.wmTid = tid := by
  intro s x s' h
  exact wrunStepInd tid (fun s s' => ∃ l, s'.wmLog = s.wmLog ++ l ∧ ∀ mg ∈ l, mg.wmTid = tid)
    (fun _ => ⟨[], by simp, by simp⟩)
    (fun _ _ _ ⟨l1, h1, o1⟩ ⟨l2, h2, o2⟩ => ⟨l1 ++ l2, by rw [h2, h1, List.append_assoc],
      fun mg hmg => by
        rcases List.mem_append.1 hmg with h | h
        · exact o1 mg h
        · exact o2 mg h⟩)
    (fun _ _ _ => ⟨[], by simp [wsetReg], by simp⟩)
    (fun _ _ _ _ _ _ => ⟨[], by simp [wsetDev], by simp⟩)
    (fun _ _ _ _ _ _ => ⟨[], by simp [wsetDev], by simp⟩)
    (fun _ _ _ _ _ _ _ => ⟨[], by rw [wreadPostLog]; simp, by simp⟩)
    (fun s ak pa n v => ⟨[wwriteMsg tid (wmClassOf ak s.wmWs) pa n v], rfl, by
      intro mg hmg
      rw [List.mem_singleton] at hmg
      subst hmg; rfl⟩)
    (fun _ _ => ⟨[], by simp [wbarrierPost], by simp⟩)
    m s x s' h

/-- THE AGENT'S VIEWS ONLY EVER RISE. -/
theorem wrunWsLe (tid : Option Nat) {X : Type} (m : SailM X) :
    ∀ (s : Wmstate) (x : X) (s' : Wmstate), wrun tid m s x s' → wsLe s.wmWs s'.wmWs := by
  intro s x s' h
  exact wrunStepInd tid (fun s s' => wsLe s.wmWs s'.wmWs)
    (fun _ => wsLeRefl _) (fun _ _ _ h1 h2 => wsLeTrans h1 h2) (fun _ _ _ => wsLeRefl _)
    (fun _ _ _ _ _ _ => wsLeRefl _) (fun _ _ _ _ _ _ => wsLeRefl _)
    (fun s ak pa _ ts _ _ => wreadPostWsLe s ak pa ts)
    (fun s ak pa n v => wwritePostWsLe tid s ak pa n v)
    (fun s b => barrierPostLe s.wmWs b)
    m s x s' h

/-- Stage B: the instruction view only ever rises. -/
theorem wrunItvLe (tid : Option Nat) {X : Type} (m : SailM X) :
    ∀ (s : Wmstate) (x : X) (s' : Wmstate), wrun tid m s x s' → s.wmItv ≤ s'.wmItv := by
  intro s x s' h
  exact wrunStepInd tid (fun s s' => s.wmItv ≤ s'.wmItv)
    (fun _ => Nat.le_refl _) (fun _ _ _ h1 h2 => Nat.le_trans h1 h2) (fun _ _ _ => Nat.le_refl _)
    (fun _ _ _ _ _ _ => Nat.le_refl _) (fun _ _ _ _ _ _ => Nat.le_refl _)
    (fun s ak pa _ ts _ _ => (wreadPostItv s ak pa ts).symm ▸ Nat.le_refl _)
    (fun _ _ _ _ _ => Nat.le_refl _)
    (fun s b => itvPostLe s.wmWs s.wmItv b)
    m s x s' h

/-- SC DEGENERACY.  In a state whose read floor already covers the whole log, a
read has NO choice: every admissible timestamp is the latest one.  O2: for an
i-cache read the floor is the instruction view (deviation 8). -/
theorem wreadAllSeen (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat) (ts : List Nat)
    (w : BitVec (8 * n)) :
    (if ak.akIfetch then s.wmLog.length ≤ s.wmItv
     else s.wmLog.length ≤ loadVpre s.wmWs ak.akSync) →
    wreadOk s ak pa n ts w → ts = cohTs s pa n := by
  intro hall ⟨hlen, hbytes⟩
  apply List.ext_getElem (by rw [hlen, cohTsLength])
  intro j h1 h2
  have hj : j < n := by omega
  obtain ⟨hv, hadm⟩ := hbytes j hj
  have hlat : latest (wimg s) s.wmLog (WeakInterp.accAddr pa j) ts[j]! := by
    cases hc : ak.akIfetch with
    | true =>
      rw [hc] at hadm hall
      simp only [↓reduceIte] at hadm hall
      exact ⟨by rw [hv]; rfl, fun hw => hadm (writesInMonoHi _ _ _ _ _ (by omega) hw)⟩
    | false =>
      rw [hc] at hadm hall
      simp only [Bool.false_eq_true, ↓reduceIte] at hadm hall
      exact readableAllSeen _ _ _ _ _ _ hall hadm.1
  rw [getBangLt _ _ h1] at hlat
  rw [← latestTsEq _ _ _ _ hlat, ← cohTsLookup s pa n j hj, getBangLt _ _ h2]

theorem wreadAllSeenBytes (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat) (ts : List Nat)
    (w : BitVec (8 * n)) :
    (if ak.akIfetch then s.wmLog.length ≤ s.wmItv
     else s.wmLog.length ≤ loadVpre s.wmWs ak.akSync) →
    wreadOk s ak pa n ts w → wreadBytes s ak pa n (cohTs s pa n) = some w := by
  intro hall hok
  rw [← wreadAllSeen s ak pa n ts w hall hok]
  exact wreadBytesComplete s ak pa n ts w hok

/-! ### The view-bound invariant (`WeakMem.wsBounded`) -/

theorem barrierPostBounded (ws : Wstate) (b : barrier_kind) (n : Nat) :
    wsBounded ws n → wsBounded (barrierPost ws b) n := by
  intro hb
  cases b <;> simp only [barrierPost]
  all_goals first
    | exact hb
    | exact fencePostBounded _ _ _ _ _ _ hb
    | exact fencePostBounded _ _ _ _ _ _ (fencePostBounded _ _ _ _ _ _ hb)

/-- An admissible byte's timestamp is inside the log. -/
theorem wbyteOkBounded (s : Wmstate) (ak : AkInfo) (a : Int) (t : Nat) (b : BitVec 8) :
    wbyteOk s ak a t b → t ≤ s.wmLog.length := by
  rintro ⟨hv, _⟩
  exact logByteBounded (wimg s) s.wmLog t a (by rw [hv]; rfl)

theorem wreadOkTsBounded (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat) (ts : List Nat)
    (w : BitVec (8 * n)) : wreadOk s ak pa n ts w → ∀ t ∈ ts, t ≤ s.wmLog.length := by
  rintro ⟨hlen, hbytes⟩ t ht
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
  have := wbyteOkBounded s ak _ _ _ (hbytes j (by omega))
  rwa [getBangLt _ _ hj] at this

theorem wreadPostBounded (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat) (ts : List Nat)
    (w : BitVec (8 * n)) :
    wsBounded s.wmWs s.wmLog.length → wreadOk s ak pa n ts w →
    wsBounded (wreadPost s ak pa ts).wmWs (wreadPost s ak pa ts).wmLog.length := by
  intro hb hok
  rw [wreadPostLog]
  unfold wreadPost
  split
  · exact hb
  · exact loadPostRunBounded _ _ _ _ _ hb (wreadOkTsBounded s ak pa n ts w hok)

/-- The write case: the log grows by ONE, and the store's timestamp is the new
length. -/
theorem wwritePostBounded (tid : Option Nat) (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) :
    wsBounded s.wmWs s.wmLog.length →
    wsBounded (wwritePost tid s ak pa n v).wmWs (wwritePost tid s ak pa n v).wmLog.length := by
  intro hb
  rw [wwritePostLog, List.length_append, List.length_singleton]
  exact storePostRunBounded _ _ _ _ _ s.wmLog.length _ hb (Nat.le_refl _) (by omega)

/-- THE INVARIANT'S PRESERVATION over a whole step. -/
theorem wrunWsBounded (tid : Option Nat) {X : Type} (m : SailM X) :
    ∀ (s : Wmstate) (x : X) (s' : Wmstate), wrun tid m s x s' →
      wsBounded s.wmWs s.wmLog.length → wsBounded s'.wmWs s'.wmLog.length := by
  intro s x s' h
  exact wrunStepInd tid
    (fun s s' => wsBounded s.wmWs s.wmLog.length → wsBounded s'.wmWs s'.wmLog.length)
    (fun _ h => h) (fun _ _ _ h1 h2 hb => h2 (h1 hb)) (fun _ _ _ hb => hb)
    (fun _ _ _ _ _ _ hb => hb) (fun _ _ _ _ _ _ hb => hb)
    (fun s ak pa n ts w hok hb => wreadPostBounded s ak pa n ts w hb hok)
    (fun s ak pa n v hb => wwritePostBounded tid s ak pa n v hb)
    (fun s b hb => barrierPostBounded s.wmWs b _ hb)
    m s x s' h

theorem wexecWsBounded (tid : Option Nat) {X : Type} (m : SailM X) (χ : List (List Nat))
    (s : Wmstate) (x : X) (s' : Wmstate) (χ' : List (List Nat)) :
    wexec tid m χ s = some (x, s', χ') →
    wsBounded s.wmWs s.wmLog.length → wsBounded s'.wmWs s'.wmLog.length := fun hex =>
  wrunWsBounded tid m s x s' (wexecWrun tid m χ s x s' χ' hex)

/-- Stage B (decision B4): the bound invariant WITH the instruction view. -/
def wmBounded (s : Wmstate) : Prop :=
  wsBounded s.wmWs s.wmLog.length ∧ s.wmItv ≤ s.wmLog.length

theorem wrunWmBounded (tid : Option Nat) {X : Type} (m : SailM X) :
    ∀ (s : Wmstate) (x : X) (s' : Wmstate), wrun tid m s x s' → wmBounded s → wmBounded s' := by
  intro s x s' h
  exact wrunStepInd tid (fun s s' => wmBounded s → wmBounded s')
    (fun _ h => h) (fun _ _ _ h1 h2 hb => h2 (h1 hb)) (fun _ _ _ hb => hb)
    (fun _ _ _ _ _ _ hb => hb) (fun _ _ _ _ _ _ hb => hb)
    (fun s ak pa n ts w hok hb => ⟨wreadPostBounded s ak pa n ts w hb.1 hok, by
      rw [wreadPostItv, wreadPostLog]; exact hb.2⟩)
    (fun s ak pa n v hb => ⟨wwritePostBounded tid s ak pa n v hb.1, by
      rw [wwritePostItv, wwritePostLog, List.length_append]; have := hb.2; omega⟩)
    (fun s b hb => ⟨barrierPostBounded s.wmWs b _ hb.1,
      itvPostBounded s.wmWs s.wmItv b _ hb.1 hb.2⟩)
    m s x s' h

theorem wexecWmBounded (tid : Option Nat) {X : Type} (m : SailM X) (χ : List (List Nat))
    (s : Wmstate) (x : X) (s' : Wmstate) (χ' : List (List Nat)) :
    wexec tid m χ s = some (x, s', χ') → wmBounded s → wmBounded s' := fun hex =>
  wrunWmBounded tid m s x s' (wexecWrun tid m χ s x s' χ' hex)

/-- O2 + Stage B: an i-cache `wreadOk` is exactly a per-byte `ifetchByteOk` run
(the bridge to the promise machine's `ifetchOk`). -/
theorem wreadOkIfetch (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat) (ts : List Nat)
    (w : BitVec (8 * n)) :
    ak.akIfetch = true →
    (wreadOk s ak pa n ts w ↔
      ts.length = n ∧ ∀ j : Nat, j < n →
        ifetchByteOk (wimg s) s.wmLog s.wmItv (WeakInterp.accAddr pa j) ts[j]! (nthByte w j)) := by
  intro hc
  unfold wreadOk
  constructor
  · rintro ⟨hl, h⟩; exact ⟨hl, fun j hj => (wbyteOkIfetch s ak _ _ _ hc).1 (h j hj)⟩
  · rintro ⟨hl, h⟩; exact ⟨hl, fun j hj => (wbyteOkIfetch s ak _ _ _ hc).2 (h j hj)⟩

end Weak
