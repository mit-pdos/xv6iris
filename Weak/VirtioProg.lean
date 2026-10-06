/-
Weak: **THE VIRTIO DEVICE AS A PROGRAM** (M5): a read / write / fence monad `DM` and
the device program `virtioProg`, plus THE EQUIVALENCE that ties it back to the atomic
autonomous request step `virtioReqStep`.

Rocq: `iris/VirtioProg.v` @ xxvzwolszwmp (1cc222280).

## The Rocq header (verbatim in substance)

Design: claude-notes/design/weak-memory-m5.md, sections `The device program` and
`Assumptions`.  M5 makes the disk a weak-memory AGENT rather than a flat-memory oracle:
the device acquire-loads the available index, plain-loads the ring entry / descriptors /
header / data buffer at the view it thereby acquired, stores the completion, FENCES, and
only then stores the used index -- one Layer-1 memory event per node, at the disk agent's
own `wstate`, using exactly the labels a hart uses.  This file is the PROGRAM half of
that: Iris-free, SC tree untouched.

THE WRITE ORDER (a DESIGN decision, not an artefact -- see the FINDING below), for one
completed request:

    [data buffer]  ;  status byte  ;  used elem .id  ;  used elem .len
       ;  FENCE  ;  used ring ->idx

The `DFence` is the device-side WRITE BARRIER of the virtio spec: every byte the driver
will look at after seeing the index bump is published BEFORE the index bump.  That single
fence is the whole synchronisation the driver's completion path relies on (`used->idx
read ; fence rw,rw ; used elem read` on the other side), and it is why the QUEUE_NOTIFY
doorbell's ordering is irrelevant to safety.  A disk WRITE reads the data buffer BEFORE
any store (assumption 1 covers that read too); a disk READ writes the data buffer first,
so the status byte -- the thing a poller may look at -- is never visible ahead of the data
it describes.

READ GRANULARITY: each descriptor is FOUR reads (addr:8 len:4 flags:2 next:2), one per
`viewWord` the model's `descAt` performs, not one 16-byte read that is then split.  Four
reads make every `runDm` step a CONVERSION (`runDreadDesc` is `rfl`); a single 16-byte read
would have to re-derive `viewWord mv (base + 8) 4` from a slice of `viewBytes mv base 16`,
i.e. address-add associativity, for no gain.  A real device is free to burst; splitting a
burst into its fields only ADDS interleavings, so this is the conservative choice as well.

ASSUMPTIONS this model makes about the device (weak-memory-m5.md):
 1. The device reads the available index with ACQUIRE ordering relative to its subsequent
    ring / descriptor / buffer reads (the spec's device-side read barrier).  Only that one
    read sets `aq`.
 2. The device's completion writes are ordered before its used-index write (the `DFence`;
    the spec's device-side write barrier).
 3. The device may process a published request at any time (polling); QUEUE_NOTIFY and
    the ISR are hints.  A superset of a notify-driven device.
 4. A malformed chain lets the device write anything anywhere (`DWild`), so a driver must
    PROVE its chains are well formed.
 5. No icache; MMIO registers are fabric state.

Two further points where the program is deliberately not a transcription of
`virtioComplete`:

 - A ZERO-LENGTH data transfer emits NO event at all (`dreadData` / `dwriteData`).  A
   store of zero bytes is not a memory event -- the language's store arm requires a
   nonempty payload (`DmWf`) -- and a zero-byte read has no address to read.  Both are
   no-ops in the model too (`viewBytes _ _ 0 = []`, `writeByteList m _ [] = m`), so this
   changes nothing but the event count.
 - The commit delta takes the CONFIGURATION and the ISR from the state at COMMIT time and
   the two ring counters from the state the program was STARTED at (`vdelta`): a hart's
   MMIO writes during the burst must not be clobbered, while `seen`/`usedIdx` are the +1
   of the values the burst actually consumed, exactly as `virtioComplete` has them.

FINDING (recorded rather than fudged): the model's write MAP and the program's ORDERED
writes differ on OVERLAP, and no device-correct emission order can fix that.
`virtioComplete` builds its map as
  data  >  status  >  used->idx  >  elem.len  >  elem.id
(highest precedence first; the status `insert` and the data `writeByteList` are applied
OUTERMOST, so they win), i.e. as if the device wrote the used index BEFORE the status byte
and the data LAST -- the reverse of any device that observes assumption 2.  A
later-writes-win fold of the order above gives the reverse precedence.  The two agree
exactly when the written regions do not overlap, which is what the DMA lease of the device
invariant gives a driver anyway; so `virtioProgReqStep` carries that as the explicit side
condition `virtioProgDisj` (Nodup on the addresses the program writes) and everything else
-- the resulting STATE, `DWild`, `DIdle`, the trichotomy, `DmWf` -- is unconditional.  The
emission order above was NOT changed to make the map equation come out; if the discrepancy
is ever to be closed it is `virtioComplete`'s nesting that should be re-ordered, not the
device's write barrier.

## Deviations from Rocq

1. THE DEVICE STATE IS LEAN'S.  Rocq's file runs over `VirtioModel.virtio_state` (five
   fields: cfg, isr, seen, used_idx, disk).  The Lean tree's virtio model
   (`MachCSL/Dev/Virtio.lean`) is the ANALOG of `VirtioModel.v` and has no atomic request
   step; but the weak tier's device fabric is `MachCSL.Dev.DevStates`, so downstream
   (`WeakEvLang`'s `virtio_prog (dvirtio (wgdev σ))`) runs the program on, and commits the
   delta to, Lean's `MachCSL.VirtioState`.  So the program reads `v.cfg`, `v.seen`,
   `v.usedIdx`, `v.disk` of Lean's state, and the commit delta `vdelta` (a record update
   `{ vc with isr, seen, usedIdx, disk }`) keeps the Lean-only fields (`inflight`, `cache`,
   `taken`, `cap`) of the COMMIT-time state, like `cfg`.  The types `VirtioCfg`, `VioReq`,
   `Virtio.VqDesc` (`vq_desc`), the predicate `Virtio.live` (`virtio_live`; Lean's queue-size
   test `qsizeOk` admits the powers of two up to 1024 where Rocq's `vq_size_ok` admits
   1,2,4,8), `VqDesc.has` (`vd_has`, the same `land`-test), the geometry
   `Virtio.availIdxAddr`/`availRingAddr`/`descAddr`/`usedIdxAddr`/`usedElemAddr` (each the
   Rocq `pa_off` expression, at `Nat` offsets) and `Virtio.diskRead`/`diskWrite`/`reqOff`
   (Rocq `disk_read`/`disk_write` at `bv_unsigned sector * virtio_sector_size`; the image is
   `Nat → BitVec 8`, Rocq `Z -> bv 8`) are all the Lean model's.
2. THE ATOMIC REFERENCE STEP IS PORTED HERE.  The equivalence theorems (sections 7-8) are
   stated against `VirtioModel.v`'s `virtio_req_step`, which has no Lean counterpart (the
   Lean model is a task program, `Virtio.body`/`serve`).  The fragment of `VirtioModel.v`
   they need -- `vmem`, `view_bytes`, `view_word`, `desc_at`, `avail_idx_at`,
   `avail_ring_at`, `chain_at`, `virtio_chain_ok`, `req_at`, `virtio_used_writes`,
   `virtio_complete`, `virtio_pending`, `virtio_req_step`, `virtio_stalled` and
   `RiscvModelBytes.write_bytes` / `VirtioModel.write_byte_list` -- is ported in section 0b,
   over the Lean state of item 1, Rocq-literal otherwise.  The completion's SEMANTICS stay
   Rocq's (they are this file's specification): status OK for IN/OUT only (Lean's
   `statusOf` also accepts FLUSH), the used element's `len` is the data length `r.len` (Lean
   reports `usedLen r`), the data comes from the DURABLE image `v.disk` (Lean's SC device
   reads through its write-back cache), and no in-flight map is consulted.  Recorded as
   DRIFT against `MachCSL/Dev/Virtio.lean`; unifying the two is the later cleanup that
   `notes/weak-port-architecture.md` (table A, row `VirtioProg`) defers.
3. `VioReq` has the Lean-only field `wr` (the data descriptor is device-writable); the
   program and `reqAt` both set it to `d1.has Virtio.descFWrite`, as `Virtio.fetch` does.
   Nothing here reads it.
4. BYTES.  `Arch.pa` is `PAddr` (`BitVec 64`), `bv n` is `BitVec n`, `N`/`nat` widths are
   `Nat`.  `pa_add a j` is `a + BitVec.ofNat 64 j` inline (the tree's convention,
   `Xv6/BlkmapBuf.lean`), and `pa_off a z` (a `Z` displacement) is the same at a `Nat`
   displacement (every displacement here is a nonnegative literal or product).
   `nth_byte` (width-generic) is the local `nthByteW` (`MachCSL.nthByte` wants a
   `BitVec (8 * n)`).  The little-endian decode `Z_to_bv (8 * n) (assemble_bytes bs)` is
   `MachCSL.bvOfBytes n bs` (`Dev/DevLang.lean`, the decode the Lean device uses); the two
   agree on lists of length `n`, and every use here is consistent, so every `runDm`
   conversion is still `rfl`.  `seq 0 n` is `List.range' 0 n`, `imap` is `List.mapIdx`,
   `concat` is `List.flatten`, `gmap Arch.pa (bv 8)` is `GMapF PAddr (BitVec 8)` with
   `get?`/`insert`, `list_to_map` is `PartialMap.ofList`, `≡ₚ` is `List.Perm`, `NoDup` is
   `List.Nodup`, `bv_unsigned` is `toNat`, `Z_to_bv 32 (bv_unsigned h)` is
   `BitVec.ofNat 32 h.toNat`, `bv_add x (Z_to_bv 16 1)` is `x + 1#16`, `bv_or` is `|||`.
5. `run_dm`'s write arm `let '(a, ws) := run_dm mv k in (a, (pa, bs) :: ws)` is written
   with projections, `((runDm mv k).1, (pa, bs) :: (runDm mv k).2)` (propositionally the
   same; it makes `runDwriteData` a case split rather than a pair destruct).
6. `chain_at`'s left-nested `((h, d0), d1), d2` tuple is Lean's right-nested
   `(h, d0, d1, d2)`.
7. NAME CLASHES (the orchestrator's file-qualification rule, `notes/weak-port-dupnames.json`):
   Rocq's `VirtioProg.wbytes` is also a `WeakInterpProj` name (the hart-side twin, same
   body), so it is declared FILE-QUALIFIED, `Weak.VirtioProg.wbytes`, and referred to as
   `VirtioProg.wbytes` (Rocq resolved the clash by `Require` order, `WeakEvLang.v`'s note).
   The `VirtioModel`/`RiscvModelBytes` fragment of deviation 2 is likewise declared in
   `namespace Weak.VirtioProg` (it is a Weak-local copy of SC-model names, and other weak
   files may need their own); this file `open`s it after section 0b.
8. The two local Ltacs (`dwild`, `dsplit`) are inlined (`by_cases`/`split`).
9. The descriptor read `dreadDesc` takes the index at `Nat` (Rocq `Z`, always called at a
   `bv_unsigned`).

## Name map (Rocq → Lean)

`vp_pa_add_0` ↦ `vpPaAdd0`; `DM`/`DRet`/`DRead`/`DWrite`/`DFence` ↦ same (constructors
exported); `dres`/`DDone`/`DWild`/`DIdle` ↦ `Dres`/same; `dm_wf` ↦ `DmWf` with
`dm_wf_ret/read/write/fence` ↦ `DmWf.ret/read/write/fence`; `dread_word` ↦ `dreadWord`;
`wbytes` ↦ `VirtioProg.wbytes` (deviation 7); `dwrite_word` ↦ `dwriteWord`; `dread_data` ↦
`dreadData`; `dwrite_data` ↦ `dwriteData`; `wcons` ↦ `wcons`; `dread_avail_idx` ↦
`dreadAvailIdx`; `dread_avail_ring` ↦ `dreadAvailRing`; `dread_desc` ↦ `dreadDesc`;
`run_dm` ↦ `runDm`; `run_dread_word` ↦ `runDreadWord`; `run_dread_data` ↦ `runDreadData`;
`run_dwrite_data` ↦ `runDwriteData`; `run_dread_avail_idx` ↦ `runDreadAvailIdx`;
`run_dread_avail_ring` ↦ `runDreadAvailRing`; `run_dread_desc` ↦ `runDreadDesc`;
`dm_writes_map` ↦ `dmWritesMap`; `wpairs` ↦ `wpairs`; `dm_writes_flat` ↦ `dmWritesFlat`;
`dm_writes_disj` ↦ `dmWritesDisj`; `ins_list_union` ↦ `insListUnion`;
`insert_list_to_map` ↦ `insertListToMap`; `wpairs_imap` ↦ `wpairsImap`;
`write_byte_list_union` ↦ `writeByteListUnion`; `imap_seq0` ↦ `imapSeq0`;
`write_bytes_byte_list` ↦ `writeBytesByteList`; `dm_writes_map_flat` ↦ `dmWritesMapFlat`;
`fmap_perm` ↦ `fmapPerm`; `concat_perm` ↦ `concatPerm`; `dm_writes_flat_perm` ↦
`dmWritesFlatPerm`; `dm_writes_map_perm` ↦ `dmWritesMapPerm`; `vstatus` ↦ `vstatus`;
`vdelta` ↦ `vdelta`; `vdkf` ↦ `vdkf`; `vdata` ↦ `vdata`; `vused_elem` ↦ `vusedElem`;
`dused_tail` ↦ `dusedTail`; `dtail` ↦ `dtail`; `dcomplete` ↦ `dcomplete`; `virtio_prog`
↦ `virtioProg`; `vused_ws` ↦ `vusedWs`; `vprog_ws` ↦ `vprogWs`; `vmodel_ws` ↦
`vmodelWs`; `run_dtail` ↦ `runDtail`; `run_dcomplete` ↦ `runDcomplete`;
`run_virtio_prog` ↦ `runVirtioProg`; `dm_writes_map_app` ↦ `dmWritesMapApp`;
`write_byte_list_single` ↦ `writeByteListSingle`; `foldl_wcons` ↦ `foldlWcons`;
`vused_ws_map` ↦ `vusedWsMap`; `virtio_complete_state` ↦ `virtioCompleteState`;
`virtio_complete_writes` ↦ `virtioCompleteWrites`; `vmodel_vprog_perm` ↦
`vmodelVprogPerm`; `vprog_writes_map` ↦ `vprogWritesMap`; `virtio_complete_pair` ↦
`virtioCompletePair`; `virtio_prog_disj` ↦ `virtioProgDisj`; `virtio_prog_req_step` ↦
`virtioProgReqStep`; `virtio_prog_stalled` ↦ `virtioProgStalled`; `virtio_prog_idle` ↦
`virtioProgIdle`; `virtio_prog_trichotomy` ↦ `virtioProgTrichotomy`;
`virtio_prog_req_step_state` ↦ `virtioProgReqStepState`; `virtio_prog_done_step` ↦
`virtioProgDoneStep`; `wbytes_nonempty` ↦ `wbytesNonempty`; `dm_wf_dread_word` ↦
`dmWfDreadWord`; `dm_wf_dwrite_word` ↦ `dmWfDwriteWord`; `dm_wf_dread_data` ↦
`dmWfDreadData`; `dm_wf_dwrite_data` ↦ `dmWfDwriteData`; `dm_wf_dread_desc` ↦
`dmWfDreadDesc`; `dm_wf_dtail` ↦ `dmWfDtail`; `dm_wf_dcomplete` ↦ `dmWfDcomplete`;
`virtio_prog_wf` ↦ `virtioProgWf`.

The `VirtioModel`/`RiscvModelBytes` fragment (deviation 2), all under `VirtioProg.`: `nth_byte` ↦ `nthByteW`;
`write_bytes` ↦ `writeBytes`; `write_byte_list` ↦ `writeByteList`; `vmem` ↦ `VMem`;
`view_bytes` ↦ `viewBytes`; `view_word` ↦ `viewWord`; `desc_at` ↦ `descAt`;
`avail_idx_at` ↦ `availIdxAt`; `avail_ring_at` ↦ `availRingAt`; `chain_at` ↦ `chainAt`;
`virtio_chain_ok` ↦ `virtioChainOk`; `req_at` ↦ `reqAt`; `virtio_used_writes` ↦
`virtioUsedWrites`; `virtio_complete` ↦ `virtioComplete`; `virtio_pending` ↦
`virtioPending`; `virtio_req_step` ↦ `virtioReqStep`; `virtio_stalled` ↦ `virtioStalled`.
Lean-only helper: `listToMapApp` (stdpp `list_to_map_app`), `listToMapProper` (stdpp
`list_to_map_proper`), `dmWritesMapFlatGen` (replaces the Rocq `rev_ind`).

## Not ported

Nothing: every Rocq definition and lemma has a Lean twin (the Ltacs are inlined).

## Statements checked

All exported theorems, by hand against the Rocq file (modulo deviations 1-9).
-/
import MachCSL.Dev.Virtio
import MachCSL.StdppMap

namespace Weak

open MachCSL Iris.Std Iris.Std.PartialMap

/-! ## 0. Prelude: `pa_add a 0 = a`. -/

theorem vpPaAdd0 (a : PAddr) : a + BitVec.ofNat 64 0 = a := by simp

/-! ## 0b. The `VirtioModel` fragment the equivalence is stated against (deviation 2) -/

namespace VirtioProg

/-- Rocq `RiscvModelBytes.nth_byte`: byte `j` of a value of any width. -/
def nthByteW {w : Nat} (val : BitVec w) (j : Nat) : BitVec 8 := val.extractLsb' (8 * j) 8

/-- Rocq `RiscvModelBytes.write_bytes`: an `n`-byte little-endian field store. -/
def writeBytes {w : Nat} (mm : GMapF PAddr (BitVec 8)) (pa : PAddr) (n : Nat) (val : BitVec w) :
    GMapF PAddr (BitVec 8) :=
  (List.range' 0 n).foldr (fun j acc => insert acc (pa + BitVec.ofNat 64 j) (nthByteW val j)) mm

/-- Rocq `VirtioModel.write_byte_list`. -/
def writeByteList (mm : GMapF PAddr (BitVec 8)) (pa : PAddr) (bs : List (BitVec 8)) :
    GMapF PAddr (BitVec 8) :=
  (bs.mapIdx (fun j b => (j, b))).foldr (fun jb acc => insert acc (pa + BitVec.ofNat 64 jb.1) jb.2) mm

/-- Rocq `VirtioModel.vmem`: memory as the device sees it (total). -/
abbrev VMem := PAddr → BitVec 8

/-- `n` bytes at `a`, as the device sees them. -/
def viewBytes (mv : VMem) (a : PAddr) (n : Nat) : List (BitVec 8) :=
  (List.range' 0 n).map (fun j => mv (a + BitVec.ofNat 64 j))

/-- An `n`-byte little-endian field, as the device sees it. -/
def viewWord (mv : VMem) (a : PAddr) (n : Nat) : BitVec (8 * n) :=
  bvOfBytes n (viewBytes mv a n)

def descAt (c : VirtioCfg) (mv : VMem) (i : Nat) : Virtio.VqDesc :=
  let base := Virtio.descAddr c i
  ⟨viewWord mv base 8, viewWord mv (base + BitVec.ofNat 64 8) 4,
   viewWord mv (base + BitVec.ofNat 64 12) 2, viewWord mv (base + BitVec.ofNat 64 14) 2⟩

def availIdxAt (c : VirtioCfg) (mv : VMem) : BitVec 16 :=
  viewWord mv (Virtio.availIdxAddr c) 2

def availRingAt (c : VirtioCfg) (mv : VMem) (i : BitVec 16) : BitVec 16 :=
  viewWord mv (Virtio.availRingAddr c i) 2

/-- The chain at available-ring position `i`: exactly three descriptors, each named by
an in-range index. -/
def chainAt (c : VirtioCfg) (mv : VMem) (i : BitVec 16) :
    Option (BitVec 16 × Virtio.VqDesc × Virtio.VqDesc × Virtio.VqDesc) :=
  let qnum := c.qnum.toNat
  let h := availRingAt c mv i
  if !decide (h.toNat < qnum) then none else
  let d0 := descAt c mv h.toNat
  if !d0.has Virtio.descFNext then none else
  if !decide (d0.next.toNat < qnum) then none else
  let d1 := descAt c mv d0.next.toNat
  if !d1.has Virtio.descFNext then none else
  if !decide (d1.next.toNat < qnum) then none else
  let d2 := descAt c mv d1.next.toNat
  if d2.has Virtio.descFNext then none else
  some (h, d0, d1, d2)

def virtioChainOk (c : VirtioCfg) (mv : VMem) (i : BitVec 16) : Bool :=
  match chainAt c mv i with
  | some _ => true
  | none => false

def reqAt (c : VirtioCfg) (mv : VMem) (i : BitVec 16) : Option VioReq :=
  match chainAt c mv i with
  | none => none
  | some (h, d0, d1, d2) =>
      some ⟨h, viewWord mv d0.addr 4, viewWord mv (d0.addr + BitVec.ofNat 64 8) 8,
            d1.addr, d1.len, d2.addr, d1.has Virtio.descFWrite⟩

def virtioUsedWrites (c : VirtioCfg) (ui : BitVec 16) (r : VioReq) : GMapF PAddr (BitVec 8) :=
  let elem := Virtio.usedElemAddr c ui
  let m1 := writeBytes ∅ elem 4 (BitVec.ofNat 32 r.head.toNat)
  let m2 := writeBytes m1 (elem + BitVec.ofNat 64 4) 4 r.len
  writeBytes m2 (Virtio.usedIdxAddr c) 2 (ui + 1#16)

/-- Completing ONE parsed request (Rocq-literal semantics, deviation 2). -/
def virtioComplete (v : VirtioState) (mv : VMem) (r : VioReq) :
    VirtioState × GMapF PAddr (BitVec 8) :=
  let n := r.len.toNat
  let doff := Virtio.reqOff r
  let st := if r.type.toNat = Virtio.blkTIn ∨ r.type.toNat = Virtio.blkTOut
            then Virtio.blkSOk else Virtio.blkSUnsupp
  let ws := insert (virtioUsedWrites v.cfg v.usedIdx r) r.status (BitVec.ofNat 8 st)
  let vd := fun dk => { v with isr := v.isr ||| BitVec.ofNat 32 Virtio.isrUsedBuffer,
                               seen := v.seen + 1#16, usedIdx := v.usedIdx + 1#16, disk := dk }
  if r.type.toNat = Virtio.blkTIn then
    (vd v.disk, writeByteList ws r.buf (Virtio.diskRead v.disk doff n))
  else if r.type.toNat = Virtio.blkTOut then
    (vd (Virtio.diskWrite v.disk doff (viewBytes mv r.buf n)), ws)
  else
    (vd v.disk, ws)

def virtioPending (v : VirtioState) (mv : VMem) : Bool :=
  Virtio.live v.cfg && !decide ((availIdxAt v.cfg mv).toNat = v.seen.toNat)

def virtioReqStep (v : VirtioState) (mv : VMem) : Option (VirtioState × GMapF PAddr (BitVec 8)) :=
  if !virtioPending v mv then none
  else match reqAt v.cfg mv v.seen with
    | none => none
    | some r => some (virtioComplete v mv r)

def virtioStalled (v : VirtioState) (mv : VMem) : Bool :=
  virtioPending v mv && !virtioChainOk v.cfg mv v.seen

end VirtioProg

open VirtioProg

/-! ## 1. The monad -/

inductive DM (A : Type) : Type where
  | DRet (a : A)
  | DRead (pa : PAddr) (n : Nat) (aq : Bool) (k : List (BitVec 8) → DM A)
  | DWrite (pa : PAddr) (bs : List (BitVec 8)) (k : DM A)
  | DFence (k : DM A)

export DM (DRet DRead DWrite DFence)

/-- The result of one device burst. -/
inductive Dres where
  | DDone (delta : VirtioState → VirtioState)
  | DWild
  | DIdle

export Dres (DDone DWild DIdle)

/-! ## 2. Structural well-formedness: what the language's arms will require -/

inductive DmWf {A : Type} : DM A → Prop where
  | ret (a : A) : DmWf (DRet a)
  | read (pa : PAddr) (n : Nat) (aq : Bool) (k : List (BitVec 8) → DM A) :
      0 < n → (∀ bs, DmWf (k bs)) → DmWf (DRead pa n aq k)
  | write (pa : PAddr) (bs : List (BitVec 8)) (k : DM A) : bs ≠ [] → DmWf k → DmWf (DWrite pa bs k)
  | fence (k : DM A) : DmWf k → DmWf (DFence k)

/-! ## 3. The typed read / write helpers -/

def dreadWord {A : Type} (pa : PAddr) (n : Nat) (aq : Bool) (k : BitVec (8 * n) → DM A) : DM A :=
  DRead pa n aq (fun bs => k (bvOfBytes n bs))

/-- the little-endian bytes of an `n`-byte field, i.e. what `writeBytes` puts in memory -/
def VirtioProg.wbytes (n : Nat) {w : Nat} (val : BitVec w) : List (BitVec 8) :=
  (List.range' 0 n).map (fun j => nthByteW val j)

def dwriteWord {A : Type} (pa : PAddr) (n : Nat) {w : Nat} (val : BitVec w) (k : DM A) : DM A :=
  DWrite pa (VirtioProg.wbytes n val) k

/-- a data transfer of zero bytes is no event at all -/
def dreadData {A : Type} (pa : PAddr) (n : Nat) (k : List (BitVec 8) → DM A) : DM A :=
  match n with
  | 0 => k []
  | n' + 1 => DRead pa (n' + 1) false k

def dwriteData {A : Type} (pa : PAddr) (bs : List (BitVec 8)) (k : DM A) : DM A :=
  match bs with
  | [] => k
  | b :: bs' => DWrite pa (b :: bs') k

/-- the write-list counterpart of `dwriteData` -/
def wcons (pa : PAddr) (bs : List (BitVec 8)) (ws : List (PAddr × List (BitVec 8))) :
    List (PAddr × List (BitVec 8)) :=
  match bs with
  | [] => ws
  | b :: bs' => (pa, b :: bs') :: ws

def dreadAvailIdx (c : VirtioCfg) (k : BitVec 16 → DM Dres) : DM Dres :=
  dreadWord (Virtio.availIdxAddr c) 2 true k

def dreadAvailRing (c : VirtioCfg) (i : BitVec 16) (k : BitVec 16 → DM Dres) : DM Dres :=
  dreadWord (Virtio.availRingAddr c i) 2 false k

def dreadDesc (c : VirtioCfg) (i : Nat) (k : Virtio.VqDesc → DM Dres) : DM Dres :=
  dreadWord (Virtio.descAddr c i) 8 false (fun a =>
  dreadWord (Virtio.descAddr c i + BitVec.ofNat 64 8) 4 false (fun l =>
  dreadWord (Virtio.descAddr c i + BitVec.ofNat 64 12) 2 false (fun f =>
  dreadWord (Virtio.descAddr c i + BitVec.ofNat 64 14) 2 false (fun nx =>
  k ⟨a, l, f, nx⟩))))

/-! ## 4. The flat runner -/

def runDm {A : Type} (mv : VMem) : DM A → A × List (PAddr × List (BitVec 8))
  | DRet a => (a, [])
  | DRead pa n _ k => runDm mv (k (viewBytes mv pa n))
  | DWrite pa bs k => ((runDm mv k).1, (pa, bs) :: (runDm mv k).2)
  | DFence k => runDm mv k

theorem runDreadWord {A : Type} (mv : VMem) (pa : PAddr) (n : Nat) (aq : Bool)
    (k : BitVec (8 * n) → DM A) :
    runDm mv (dreadWord pa n aq k) = runDm mv (k (viewWord mv pa n)) := rfl

theorem runDreadData {A : Type} (mv : VMem) (pa : PAddr) (n : Nat) (k : List (BitVec 8) → DM A) :
    runDm mv (dreadData pa n k) = runDm mv (k (viewBytes mv pa n)) := by
  cases n <;> rfl

theorem runDwriteData {A : Type} (mv : VMem) (pa : PAddr) (bs : List (BitVec 8)) (k : DM A) :
    runDm mv (dwriteData pa bs k) = ((runDm mv k).1, wcons pa bs (runDm mv k).2) := by
  cases bs <;> rfl

theorem runDreadAvailIdx (mv : VMem) (c : VirtioCfg) (k : BitVec 16 → DM Dres) :
    runDm mv (dreadAvailIdx c k) = runDm mv (k (availIdxAt c mv)) := rfl

theorem runDreadAvailRing (mv : VMem) (c : VirtioCfg) (i : BitVec 16) (k : BitVec 16 → DM Dres) :
    runDm mv (dreadAvailRing c i k) = runDm mv (k (availRingAt c mv i)) := rfl

theorem runDreadDesc (mv : VMem) (c : VirtioCfg) (i : Nat) (k : Virtio.VqDesc → DM Dres) :
    runDm mv (dreadDesc c i k) = runDm mv (k (descAt c mv i)) := rfl

/-! ## 5. The flat memory a write LIST denotes: later writes win -/

def dmWritesMap (ws : List (PAddr × List (BitVec 8))) : GMapF PAddr (BitVec 8) :=
  ws.foldl (fun m w => writeByteList m w.1 w.2) ∅

/-- one write, as (address, byte) pairs -/
def wpairs (w : PAddr × List (BitVec 8)) : List (PAddr × BitVec 8) :=
  w.2.mapIdx (fun j b => (w.1 + BitVec.ofNat 64 j, b))

/-- the whole write list, LATEST FIRST -- the order `ofList` wants -/
def dmWritesFlat (ws : List (PAddr × List (BitVec 8))) : List (PAddr × BitVec 8) :=
  (ws.map wpairs).reverse.flatten

/-- THE side condition of the write-map half of the equivalence: the program's writes
touch pairwise distinct addresses. -/
def dmWritesDisj (ws : List (PAddr × List (BitVec 8))) : Prop :=
  ((dmWritesFlat ws).map Prod.fst).Nodup

theorem insListUnion (m : GMapF PAddr (BitVec 8)) (l : List (PAddr × BitVec 8)) :
    l.foldr (fun p acc => insert acc p.1 p.2) m = PartialMap.union (PartialMap.ofList l) m := by
  induction l with
  | nil => exact (mapUnionEmptyL (M := GMapF PAddr)).symm
  | cons kx l ih =>
    obtain ⟨k, x⟩ := kx
    rw [List.foldr_cons, ih, LawfulPartialMap.ofList_cons]
    exact insertUnionL (M := GMapF PAddr)

theorem insertListToMap (m : GMapF PAddr (BitVec 8)) (k : PAddr) (x : BitVec 8) :
    insert m k x = PartialMap.union (PartialMap.ofList [(k, x)]) m :=
  insListUnion m [(k, x)]

theorem wpairsImap (pa : PAddr) (bs : List (BitVec 8)) :
    wpairs (pa, bs) =
      (bs.mapIdx (fun j b => (j, b))).map (fun jb : Nat × BitVec 8 => (pa + BitVec.ofNat 64 jb.1, jb.2)) := by
  apply List.ext_getElem
  · simp [wpairs]
  · intro i h1 h2
    simp [wpairs]

theorem writeByteListUnion (m : GMapF PAddr (BitVec 8)) (pa : PAddr) (bs : List (BitVec 8)) :
    writeByteList m pa bs = PartialMap.union (PartialMap.ofList (wpairs (pa, bs))) m := by
  rw [← insListUnion, wpairsImap, List.foldr_map]
  rfl

theorem imapSeq0 {B : Type} (g : Nat → Nat → B) (n : Nat) :
    (List.range' 0 n).mapIdx g = (List.range' 0 n).map (fun j => g j j) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

/-- a machine-word field store IS a byte-list store -/
theorem writeBytesByteList {w : Nat} (m : GMapF PAddr (BitVec 8)) (pa : PAddr) (n : Nat)
    (val : BitVec w) :
    writeBytes m pa n val = writeByteList m pa (VirtioProg.wbytes n val) := by
  have hl : ((List.range' 0 n).map (fun j => nthByteW val j)).mapIdx (fun j b => (j, b)) =
      (List.range' 0 n).map (fun j => (j, nthByteW val j)) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp
  unfold writeBytes writeByteList VirtioProg.wbytes
  rw [hl, List.foldr_map]

theorem listToMapApp (l1 l2 : List (PAddr × BitVec 8)) :
    (PartialMap.ofList (l1 ++ l2) : GMapF PAddr (BitVec 8)) =
      PartialMap.union (PartialMap.ofList l1) (PartialMap.ofList l2) := by
  induction l1 with
  | nil => exact (mapUnionEmptyL (M := GMapF PAddr)).symm
  | cons kx l ih =>
    obtain ⟨k, x⟩ := kx
    rw [List.cons_append, LawfulPartialMap.ofList_cons, LawfulPartialMap.ofList_cons, ih]
    exact insertUnionL (M := GMapF PAddr)

/-- Lean-only generalisation of `dmWritesMapFlat` to any starting map (it replaces the
Rocq proof's `rev_ind`). -/
theorem dmWritesMapFlatGen (m : GMapF PAddr (BitVec 8)) (ws : List (PAddr × List (BitVec 8))) :
    ws.foldl (fun m w => writeByteList m w.1 w.2) m =
      PartialMap.union (PartialMap.ofList (dmWritesFlat ws)) m := by
  induction ws generalizing m with
  | nil => exact (mapUnionEmptyL (M := GMapF PAddr)).symm
  | cons w ws ih =>
    obtain ⟨pa, bs⟩ := w
    rw [List.foldl_cons, ih, writeByteListUnion]
    have hf : dmWritesFlat ((pa, bs) :: ws) = dmWritesFlat ws ++ wpairs (pa, bs) := by
      simp [dmWritesFlat]
    rw [hf, listToMapApp]
    exact mapUnionAssoc (M := GMapF PAddr)

theorem dmWritesMapFlat (ws : List (PAddr × List (BitVec 8))) :
    dmWritesMap ws = PartialMap.ofList (dmWritesFlat ws) := by
  exact (dmWritesMapFlatGen ∅ ws).trans (mapUnionEmptyR (M := GMapF PAddr))

/-! ### permutation transfer -/

theorem fmapPerm {A B : Type} (f : A → B) (l1 l2 : List A) (h : l1.Perm l2) :
    (l1.map f).Perm (l2.map f) := h.map f

theorem concatPerm {A : Type} (L1 L2 : List (List A)) (h : L1.Perm L2) :
    L1.flatten.Perm L2.flatten := by
  induction h with
  | nil => exact List.Perm.refl _
  | cons x _ ih => exact ih.append_left x
  | swap x y L =>
    simp only [List.flatten_cons, ← List.append_assoc]
    exact (List.perm_append_comm).append_right _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem dmWritesFlatPerm (ws1 ws2 : List (PAddr × List (BitVec 8))) (hp : ws1.Perm ws2) :
    (dmWritesFlat ws1).Perm (dmWritesFlat ws2) := by
  unfold dmWritesFlat
  apply concatPerm
  exact (List.reverse_perm _).trans ((fmapPerm _ _ _ hp).trans (List.reverse_perm _).symm)

/-- stdpp `list_to_map_proper`. -/
theorem listToMapProper (l1 l2 : List (PAddr × BitVec 8)) (hnd : (l1.map Prod.fst).Nodup)
    (hp : l1.Perm l2) :
    (PartialMap.ofList l1 : GMapF PAddr (BitVec 8)) = PartialMap.ofList l2 := by
  have hnd2 : (l2.map Prod.fst).Nodup := (hp.map Prod.fst).nodup_iff.mp hnd
  apply mapEq
  intro i
  cases h1 : (get? (PartialMap.ofList l1 : GMapF PAddr (BitVec 8)) i) with
  | some x =>
    exact (elemOfListToMap1 hnd2 (hp.mem_iff.mp (elemOfListToMap2 h1))).symm
  | none =>
    have hn1 : i ∉ l1.map Prod.fst := notElemOfListToMap.mpr h1
    have hn2 : i ∉ l2.map Prod.fst := fun hm => hn1 ((hp.map Prod.fst).mem_iff.mpr hm)
    exact (notElemOfListToMap.mp hn2).symm

/-- THE reordering lemma: on pairwise distinct addresses the order of the writes does not
matter, so the model's map and the program's ordered writes may differ in order and still
denote the same memory. -/
theorem dmWritesMapPerm (ws1 ws2 : List (PAddr × List (BitVec 8))) (hp : ws1.Perm ws2)
    (hnd : dmWritesDisj ws1) : dmWritesMap ws1 = dmWritesMap ws2 := by
  rw [dmWritesMapFlat, dmWritesMapFlat]
  exact listToMapProper _ _ hnd (dmWritesFlatPerm _ _ hp)

/-! ## 6. The device program -/

/-- the status byte the model reports -- `virtioComplete`'s `st` -/
def vstatus (r : VioReq) : Nat :=
  if r.type.toNat = Virtio.blkTIn ∨ r.type.toNat = Virtio.blkTOut
  then Virtio.blkSOk else Virtio.blkSUnsupp

/-- THE COMMIT DELTA.  `v` is the state the burst STARTED at, `vc` the state at commit
time: the configuration and the ISR come from `vc` (a hart's MMIO writes during the burst
are not clobbered; so do the Lean-only fields, deviation 1), the two ring counters are the
+1 of what the burst consumed, and `dkf` is the disk image update. -/
def vdelta (v : VirtioState) (dkf : (Nat → BitVec 8) → (Nat → BitVec 8)) :
    VirtioState → VirtioState :=
  fun vc => { vc with isr := vc.isr ||| BitVec.ofNat 32 Virtio.isrUsedBuffer,
                      seen := v.seen + 1#16, usedIdx := v.usedIdx + 1#16, disk := dkf vc.disk }

/-- the disk-image update the FLAT run computes (a disk WRITE only) -/
def vdkf (_v : VirtioState) (mv : VMem) (r : VioReq) : (Nat → BitVec 8) → (Nat → BitVec 8) :=
  if r.type.toNat = Virtio.blkTIn then (fun dk => dk)
  else if r.type.toNat = Virtio.blkTOut then
    (fun dk => Virtio.diskWrite dk (Virtio.reqOff r) (viewBytes mv r.buf r.len.toNat))
  else (fun dk => dk)

/-- the bytes the device stores into the driver's buffer (a disk READ only) -/
def vdata (v : VirtioState) (r : VioReq) : List (BitVec 8) :=
  if r.type.toNat = Virtio.blkTIn
  then Virtio.diskRead v.disk (Virtio.reqOff r) r.len.toNat
  else []

def vusedElem (c : VirtioCfg) (ui : BitVec 16) : PAddr := Virtio.usedElemAddr c ui

/-- the used-ring report: element .id, element .len, FENCE, ->idx -/
def dusedTail (c : VirtioCfg) (ui : BitVec 16) (r : VioReq) (k : DM Dres) : DM Dres :=
  dwriteWord (vusedElem c ui) 4 (BitVec.ofNat 32 r.head.toNat)
    (dwriteWord (vusedElem c ui + BitVec.ofNat 64 4) 4 r.len
      (DFence (dwriteWord (Virtio.usedIdxAddr c) 2 (ui + 1#16) k)))

def dtail (v : VirtioState) (r : VioReq) (dkf : (Nat → BitVec 8) → (Nat → BitVec 8)) : DM Dres :=
  DWrite r.status [BitVec.ofNat 8 (vstatus r)]
    (dusedTail v.cfg v.usedIdx r (DRet (DDone (vdelta v dkf))))

def dcomplete (v : VirtioState) (r : VioReq) : DM Dres :=
  if r.type.toNat = Virtio.blkTIn then
    -- read the disk: the device WRITES the driver's buffer, first
    dwriteData r.buf (Virtio.diskRead v.disk (Virtio.reqOff r) r.len.toNat) (dtail v r (fun dk => dk))
  else if r.type.toNat = Virtio.blkTOut then
    -- write the disk: the device READS the driver's buffer, before storing
    dreadData r.buf r.len.toNat (fun dat =>
      dtail v r (fun dk => Virtio.diskWrite dk (Virtio.reqOff r) dat))
  else -- unsupported: no data transfer, status UNSUPP, same tail
    dtail v r (fun dk => dk)

def virtioProg (v : VirtioState) : DM Dres :=
  if Virtio.live v.cfg then
    dreadAvailIdx v.cfg (fun ai =>
    if ai.toNat = v.seen.toNat then DRet DIdle else
    dreadAvailRing v.cfg v.seen (fun h =>
    if !decide (h.toNat < v.cfg.qnum.toNat) then DRet DWild else
    dreadDesc v.cfg h.toNat (fun d0 =>
    if !d0.has Virtio.descFNext then DRet DWild else
    if !decide (d0.next.toNat < v.cfg.qnum.toNat) then DRet DWild else
    dreadDesc v.cfg d0.next.toNat (fun d1 =>
    if !d1.has Virtio.descFNext then DRet DWild else
    if !decide (d1.next.toNat < v.cfg.qnum.toNat) then DRet DWild else
    dreadDesc v.cfg d1.next.toNat (fun d2 =>
    if d2.has Virtio.descFNext then DRet DWild else
    dreadWord d0.addr 4 false (fun ty =>
    dreadWord (d0.addr + BitVec.ofNat 64 8) 8 false (fun sec =>
    dcomplete v ⟨h, ty, sec, d1.addr, d1.len, d2.addr, d1.has Virtio.descFWrite⟩)))))))
  else DRet DIdle

/-! ### the write LISTS, in the program's order and in the model's order -/

def vusedWs (c : VirtioCfg) (ui : BitVec 16) (r : VioReq) : List (PAddr × List (BitVec 8)) :=
  [ (vusedElem c ui, VirtioProg.wbytes 4 (BitVec.ofNat 32 r.head.toNat)),
    (vusedElem c ui + BitVec.ofNat 64 4, VirtioProg.wbytes 4 r.len),
    (Virtio.usedIdxAddr c, VirtioProg.wbytes 2 (ui + 1#16)) ]

def vprogWs (v : VirtioState) (r : VioReq) : List (PAddr × List (BitVec 8)) :=
  wcons r.buf (vdata v r) ((r.status, [BitVec.ofNat 8 (vstatus r)]) :: vusedWs v.cfg v.usedIdx r)

/-- the same writes in the precedence order `virtioComplete` nests them in -/
def vmodelWs (v : VirtioState) (r : VioReq) : List (PAddr × List (BitVec 8)) :=
  vusedWs v.cfg v.usedIdx r ++ (r.status, [BitVec.ofNat 8 (vstatus r)]) :: wcons r.buf (vdata v r) []

theorem runDtail (mv : VMem) (v : VirtioState) (r : VioReq)
    (dkf : (Nat → BitVec 8) → (Nat → BitVec 8)) :
    runDm mv (dtail v r dkf) =
      (DDone (vdelta v dkf), (r.status, [BitVec.ofNat 8 (vstatus r)]) :: vusedWs v.cfg v.usedIdx r) :=
  rfl

theorem runDcomplete (mv : VMem) (v : VirtioState) (r : VioReq) :
    runDm mv (dcomplete v r) = (DDone (vdelta v (vdkf v mv r)), vprogWs v r) := by
  unfold dcomplete vdkf vprogWs vdata
  by_cases hin : r.type.toNat = Virtio.blkTIn
  · simp only [hin, ↓reduceIte]
    rw [runDwriteData, runDtail]
  · by_cases hout : r.type.toNat = Virtio.blkTOut
    · simp only [hin, ↓reduceIte]
      simp only [hout, ↓reduceIte]
      rw [runDreadData, runDtail]
      rfl
    · simp only [hin, hout, ↓reduceIte]
      rw [runDtail]
      rfl

/-! ## 7. THE EQUIVALENCE: running the program at a flat memory IS the model's step -/

/-- The workhorse: the flat run of `virtioProg v` is one of exactly three shapes, and each
is pinned to the model's own test. -/
theorem runVirtioProg (v : VirtioState) (mv : VMem) :
    (virtioPending v mv = false ∧ runDm mv (virtioProg v) = (DIdle, [])) ∨
    (virtioPending v mv = true ∧ chainAt v.cfg mv v.seen = none ∧
      runDm mv (virtioProg v) = (DWild, [])) ∨
    (∃ r, virtioPending v mv = true ∧ reqAt v.cfg mv v.seen = some r ∧
      runDm mv (virtioProg v) = (DDone (vdelta v (vdkf v mv r)), vprogWs v r)) := by
  unfold virtioProg virtioPending reqAt chainAt
  by_cases hl : Virtio.live v.cfg = true
  case neg =>
    left
    simp only [hl, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, ?_⟩ <;> first | trivial | rfl
  simp only [hl, Bool.true_and, ↓reduceIte]
  rw [runDreadAvailIdx]
  by_cases hai : (availIdxAt v.cfg mv).toNat = v.seen.toNat
  · left
    simp only [hai, decide_true, Bool.not_true, ↓reduceIte]
    refine ⟨?_, ?_⟩ <;> first | trivial | rfl
  simp only [hai, decide_false, Bool.not_false, ↓reduceIte]
  right
  rw [runDreadAvailRing]
  by_cases h1 : (availRingAt v.cfg mv v.seen).toNat < v.cfg.qnum.toNat
  case neg =>
    left
    simp only [h1, decide_false, Bool.not_false, ↓reduceIte]
    refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl
  simp only [h1, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [runDreadDesc]
  by_cases h2 : (descAt v.cfg mv (availRingAt v.cfg mv v.seen).toNat).has Virtio.descFNext = true
  case neg =>
    left
    simp only [h2, Bool.not_false, ↓reduceIte]
    refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl
  simp only [h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  by_cases h3 : (descAt v.cfg mv (availRingAt v.cfg mv v.seen).toNat).next.toNat < v.cfg.qnum.toNat
  case neg =>
    left
    simp only [h3, decide_false, Bool.not_false, ↓reduceIte]
    refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl
  simp only [h3, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [runDreadDesc]
  generalize hd0 : descAt v.cfg mv (availRingAt v.cfg mv v.seen).toNat = d0 at *
  by_cases h4 : (descAt v.cfg mv d0.next.toNat).has Virtio.descFNext = true
  case neg =>
    left
    simp only [h4, Bool.not_false, ↓reduceIte]
    refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl
  simp only [h4, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  by_cases h5 : (descAt v.cfg mv d0.next.toNat).next.toNat < v.cfg.qnum.toNat
  case neg =>
    left
    simp only [h5, decide_false, Bool.not_false, ↓reduceIte]
    refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl
  simp only [h5, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [runDreadDesc]
  generalize hd1 : descAt v.cfg mv d0.next.toNat = d1 at *
  by_cases h6 : (descAt v.cfg mv d1.next.toNat).has Virtio.descFNext = true
  · left
    simp only [h6, ↓reduceIte]
    refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl
  simp only [h6, Bool.false_eq_true, ↓reduceIte]
  right
  rw [runDreadWord, runDreadWord, runDcomplete]
  exact ⟨_, trivial, rfl, rfl⟩

/-! ### the model's map, in the program's write order -/

theorem dmWritesMapApp (ws1 ws2 : List (PAddr × List (BitVec 8))) :
    dmWritesMap (ws1 ++ ws2) = ws2.foldl (fun m w => writeByteList m w.1 w.2) (dmWritesMap ws1) := by
  unfold dmWritesMap
  exact List.foldl_append

theorem writeByteListSingle (m : GMapF PAddr (BitVec 8)) (pa : PAddr) (b : BitVec 8) :
    writeByteList m pa [b] = insert m pa b := by
  unfold writeByteList
  simp only [List.mapIdx_cons, List.mapIdx_nil, List.foldr_cons, List.foldr_nil]
  rw [vpPaAdd0]

theorem foldlWcons (m : GMapF PAddr (BitVec 8)) (pa : PAddr) (bs : List (BitVec 8)) :
    (wcons pa bs []).foldl (fun m w => writeByteList m w.1 w.2) m = writeByteList m pa bs := by
  cases bs <;> rfl

theorem vusedWsMap (c : VirtioCfg) (ui : BitVec 16) (r : VioReq) :
    dmWritesMap (vusedWs c ui r) = virtioUsedWrites c ui r := by
  unfold dmWritesMap vusedWs virtioUsedWrites vusedElem
  simp only [List.foldl_cons, List.foldl_nil, writeBytesByteList]

theorem virtioCompleteState (v : VirtioState) (mv : VMem) (r : VioReq) :
    (virtioComplete v mv r).1 = vdelta v (vdkf v mv r) v := by
  unfold virtioComplete vdelta vdkf
  by_cases hin : r.type.toNat = Virtio.blkTIn
  · simp only [hin, ↓reduceIte]
  · by_cases hout : r.type.toNat = Virtio.blkTOut
    · simp only [hin, ↓reduceIte]
      simp only [hout, ↓reduceIte]
    · simp only [hin, hout, ↓reduceIte]

theorem virtioCompleteWrites (v : VirtioState) (mv : VMem) (r : VioReq) :
    (virtioComplete v mv r).2 = dmWritesMap (vmodelWs v r) := by
  unfold vmodelWs
  rw [dmWritesMapApp, vusedWsMap]
  simp only [List.foldl_cons]
  rw [foldlWcons, writeByteListSingle]
  unfold virtioComplete vstatus vdata
  by_cases hin : r.type.toNat = Virtio.blkTIn
  · simp only [hin, true_or, ↓reduceIte]
  · by_cases hout : r.type.toNat = Virtio.blkTOut
    · simp only [hin, false_or, ↓reduceIte]
      simp only [hout, ↓reduceIte]
      rfl
    · simp only [hin, hout, or_self, ↓reduceIte]
      rfl

/-- the ONE place the design's write order and the model's map nesting part company: they
are permutations of each other, nothing more -/
theorem vmodelVprogPerm (v : VirtioState) (r : VioReq) : (vmodelWs v r).Perm (vprogWs v r) := by
  unfold vmodelWs vprogWs
  cases vdata v r with
  | nil => exact List.perm_append_comm
  | cons b bs =>
    simp only [wcons]
    exact List.perm_append_comm.trans (List.Perm.swap _ _ _)

theorem vprogWritesMap (v : VirtioState) (mv : VMem) (r : VioReq) (hnd : dmWritesDisj (vprogWs v r)) :
    (virtioComplete v mv r).2 = dmWritesMap (vprogWs v r) := by
  rw [virtioCompleteWrites]
  exact (dmWritesMapPerm _ _ (vmodelVprogPerm v r).symm hnd).symm

theorem virtioCompletePair (v : VirtioState) (mv : VMem) (r : VioReq) (h : dmWritesDisj (vprogWs v r)) :
    virtioComplete v mv r = (vdelta v (vdkf v mv r) v, dmWritesMap (vprogWs v r)) :=
  Prod.ext (virtioCompleteState v mv r) (vprogWritesMap v mv r h)

/-! ## 8. The four theorems -/

/-- THE side condition of the write-map half (see the FINDING in the header): the program's
writes touch pairwise distinct addresses. -/
def virtioProgDisj (v : VirtioState) (mv : VMem) : Prop :=
  dmWritesDisj (runDm mv (virtioProg v)).2

theorem virtioProgReqStep (v : VirtioState) (mv : VMem) (v' : VirtioState)
    (w : GMapF PAddr (BitVec 8)) (hdisj : virtioProgDisj v mv) :
    virtioReqStep v mv = some (v', w) ↔
      ∃ delta ws, runDm mv (virtioProg v) = (DDone delta, ws) ∧ v' = delta v ∧
        w = dmWritesMap ws := by
  rcases runVirtioProg v mv with ⟨hp, hr⟩ | ⟨hp, hc, hr⟩ | ⟨r, hp, hq, hr⟩
  · constructor
    · intro h
      simp [virtioReqStep, hp] at h
    · rintro ⟨delta, ws, hrun, -⟩
      rw [hr] at hrun
      cases hrun
  · constructor
    · intro h
      simp [virtioReqStep, reqAt, hp, hc] at h
    · rintro ⟨delta, ws, hrun, -⟩
      rw [hr] at hrun
      cases hrun
  · unfold virtioProgDisj at hdisj
    rw [hr] at hdisj
    constructor
    · intro h
      simp only [virtioReqStep, hp, hq, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        Option.some.injEq] at h
      refine ⟨vdelta v (vdkf v mv r), vprogWs v r, hr, ?_, ?_⟩
      · rw [← virtioCompleteState, h]
      · rw [← vprogWritesMap v mv r hdisj, h]
    · rintro ⟨delta, ws, hrun, hv', hw⟩
      rw [hrun] at hr
      cases hr
      simp only [virtioReqStep, hp, hq, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [virtioCompletePair v mv r hdisj, hv', hw]

theorem virtioProgStalled (v : VirtioState) (mv : VMem) :
    virtioStalled v mv = true ↔ runDm mv (virtioProg v) = (DWild, []) := by
  unfold virtioStalled virtioChainOk
  rcases runVirtioProg v mv with ⟨hp, hr⟩ | ⟨hp, hc, hr⟩ | ⟨r, hp, hq, hr⟩
  · rw [hp, hr]
    simp
  · rw [hp, hc, hr]
    simp
  · rw [hp, hr]
    unfold reqAt at hq
    cases hch : chainAt v.cfg mv v.seen with
    | none => rw [hch] at hq; cases hq
    | some x => simp

theorem virtioProgIdle (v : VirtioState) (mv : VMem) :
    virtioPending v mv = false ↔ runDm mv (virtioProg v) = (DIdle, []) := by
  rcases runVirtioProg v mv with ⟨hp, hr⟩ | ⟨hp, hc, hr⟩ | ⟨r, hp, hq, hr⟩
  · rw [hp, hr]
    simp
  · rw [hp, hr]
    simp
  · rw [hp, hr]
    simp

theorem virtioProgTrichotomy (v : VirtioState) (mv : VMem) :
    runDm mv (virtioProg v) = (DIdle, []) ∨ runDm mv (virtioProg v) = (DWild, []) ∨
      ∃ delta ws, runDm mv (virtioProg v) = (DDone delta, ws) := by
  rcases runVirtioProg v mv with ⟨hp, hr⟩ | ⟨hp, hc, hr⟩ | ⟨r, hp, hq, hr⟩
  · exact Or.inl hr
  · exact Or.inr (Or.inl hr)
  · exact Or.inr (Or.inr ⟨_, _, hr⟩)

/-- The STATE half of the equivalence needs no side condition at all. -/
theorem virtioProgReqStepState (v : VirtioState) (mv : VMem) (v' : VirtioState)
    (w : GMapF PAddr (BitVec 8)) :
    virtioReqStep v mv = some (v', w) →
      ∃ delta ws, runDm mv (virtioProg v) = (DDone delta, ws) ∧ v' = delta v := by
  rcases runVirtioProg v mv with ⟨hp, hr⟩ | ⟨hp, hc, hr⟩ | ⟨r, hp, hq, hr⟩
  · intro h
    simp [virtioReqStep, hp] at h
  · intro h
    simp [virtioReqStep, reqAt, hp, hc] at h
  · intro h
    simp only [virtioReqStep, hp, hq, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Option.some.injEq] at h
    refine ⟨vdelta v (vdkf v mv r), vprogWs v r, hr, ?_⟩
    rw [← virtioCompleteState, h]

theorem virtioProgDoneStep (v : VirtioState) (mv : VMem) (delta : VirtioState → VirtioState)
    (ws : List (PAddr × List (BitVec 8))) :
    runDm mv (virtioProg v) = (DDone delta, ws) → ∃ w, virtioReqStep v mv = some (delta v, w) := by
  rcases runVirtioProg v mv with ⟨hp, hr⟩ | ⟨hp, hc, hr⟩ | ⟨r, hp, hq, hr⟩
  · rw [hr]; intro h; cases h
  · rw [hr]; intro h; cases h
  · rw [hr]
    intro h
    cases h
    refine ⟨(virtioComplete v mv r).2, ?_⟩
    simp only [virtioReqStep, hp, hq, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [← virtioCompleteState]

/-! ## 9. Structural well-formedness of the device program -/

theorem wbytesNonempty {w : Nat} (n : Nat) (val : BitVec w) (hn : 0 < n) : VirtioProg.wbytes n val ≠ [] := by
  intro hc
  have := congrArg List.length hc
  simp [VirtioProg.wbytes] at this
  omega

theorem dmWfDreadWord {A : Type} (pa : PAddr) (n : Nat) (aq : Bool) (k : BitVec (8 * n) → DM A)
    (hn : 0 < n) (hk : ∀ x, DmWf (k x)) : DmWf (dreadWord pa n aq k) :=
  .read _ _ _ _ hn (fun _ => hk _)

theorem dmWfDwriteWord {A : Type} (pa : PAddr) (n : Nat) {w : Nat} (val : BitVec w) (k : DM A)
    (hn : 0 < n) (hk : DmWf k) : DmWf (dwriteWord pa n val k) :=
  .write _ _ _ (wbytesNonempty n val hn) hk

theorem dmWfDreadData {A : Type} (pa : PAddr) (n : Nat) (k : List (BitVec 8) → DM A)
    (hk : ∀ bs, DmWf (k bs)) : DmWf (dreadData pa n k) := by
  cases n with
  | zero => exact hk _
  | succ n' => exact .read _ _ _ _ (Nat.succ_pos _) hk

theorem dmWfDwriteData {A : Type} (pa : PAddr) (bs : List (BitVec 8)) (k : DM A) (hk : DmWf k) :
    DmWf (dwriteData pa bs k) := by
  cases bs with
  | nil => exact hk
  | cons b bs' => exact .write _ _ _ (List.cons_ne_nil _ _) hk

theorem dmWfDreadDesc (c : VirtioCfg) (i : Nat) (k : Virtio.VqDesc → DM Dres)
    (hk : ∀ d, DmWf (k d)) : DmWf (dreadDesc c i k) := by
  unfold dreadDesc
  refine dmWfDreadWord _ _ _ _ (by decide) (fun a => ?_)
  refine dmWfDreadWord _ _ _ _ (by decide) (fun l => ?_)
  refine dmWfDreadWord _ _ _ _ (by decide) (fun f => ?_)
  refine dmWfDreadWord _ _ _ _ (by decide) (fun nx => ?_)
  exact hk _

theorem dmWfDtail (v : VirtioState) (r : VioReq) (dkf : (Nat → BitVec 8) → (Nat → BitVec 8)) :
    DmWf (dtail v r dkf) := by
  unfold dtail dusedTail
  refine .write _ _ _ (List.cons_ne_nil _ _) ?_
  refine dmWfDwriteWord _ _ _ _ (by decide) ?_
  refine dmWfDwriteWord _ _ _ _ (by decide) ?_
  refine .fence _ ?_
  refine dmWfDwriteWord _ _ _ _ (by decide) ?_
  exact .ret _

theorem dmWfDcomplete (v : VirtioState) (r : VioReq) : DmWf (dcomplete v r) := by
  unfold dcomplete
  split
  · exact dmWfDwriteData _ _ _ (dmWfDtail _ _ _)
  · split
    · exact dmWfDreadData _ _ _ (fun _ => dmWfDtail _ _ _)
    · exact dmWfDtail _ _ _

theorem virtioProgWf (v : VirtioState) : DmWf (virtioProg v) := by
  unfold virtioProg dreadAvailIdx dreadAvailRing
  split
  · refine dmWfDreadWord _ _ _ _ (by decide) (fun ai => ?_)
    split
    · exact .ret _
    refine dmWfDreadWord _ _ _ _ (by decide) (fun h => ?_)
    split
    · exact .ret _
    refine dmWfDreadDesc _ _ _ (fun d0 => ?_)
    split
    · exact .ret _
    split
    · exact .ret _
    refine dmWfDreadDesc _ _ _ (fun d1 => ?_)
    split
    · exact .ret _
    split
    · exact .ret _
    refine dmWfDreadDesc _ _ _ (fun d2 => ?_)
    split
    · exact .ret _
    refine dmWfDreadWord _ _ _ _ (by decide) (fun ty => ?_)
    refine dmWfDreadWord _ _ _ _ (by decide) (fun sec => ?_)
    exact dmWfDcomplete _ _
  · exact .ret _

end Weak
