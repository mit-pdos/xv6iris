/-
Weak: **THE VIRTIO DEVICE AS A PROGRAM** (M5, re-stated by W-DISK): a read / fence /
fabric-moving-write / pop monad `DM` and the device program `virtioProg`, ALIGNED to
MachCSL's `Virtio.body` / `Virtio.serve` (`MachCSL/Dev/Virtio.lean`), the ONE device model
of the tree.

Rocq: `iris/VirtioProg.v` @ xxvzwolszwmp (1cc222280) -- the M5 shape (the disk is a
weak-memory AGENT whose reads and writes are ordinary memory events at its own `Wstate`) is
Rocq's; the program text is no longer a transcription of the Rocq `VirtioModel` (W-DISK,
owner ruling [OWN.29], plan `notes/weak-allocproc-plan.md` §C "W-DISK", rev 27).

## Spec, stated first

virtio 1.x: the device reads the available index, then the ring entry and the 16-byte
descriptors of the chain; the used element's `len` is the number of bytes written into the
device-writable part of the chain; a driver MUST NOT issue FLUSH unless `VIRTIO_BLK_F_FLUSH`
is negotiated (this image's driver clears it, `Xv6/SpecVirtioDiskInit.lean`), so the answer to
an un-negotiated FLUSH is UNSPECIFIED; the driver MUST NOT publish a malformed chain and the
device's behaviour on one is unspecified; after writing the used index the device MAY send a
used-buffer notification.  RVWMO / riscv.cat / Sail have NO device-internal events (Sail has no
device or DMA model); Zifencei and the PMAs are silent.  Every device-internal step below is
MODEL text; the model of record is MachCSL's (`MachCSL/Dev/*.lean`).

## The monad

    DRet a                      the burst's result (`DIdle`, or `DStall` -- a stalled request)
    DRead pa n aq k             one RAM read (label `LLoad aq false`)
    DFence k                    the device-side `fence rw,rw` (label `LFence true true true true`)
    DWriteDev pre g pa bs k     ONE FABRIC-MOVING RAM WRITE (the pf twin of `DevM.dmaWriteStep`)
    DPop h k                    THE RING POP (one `LDev .dev 0 []` event)

`DWriteDev pre g pa bs k`, at the fabric `v` the write finds (the disk agent's step reads the
CURRENT fabric, `WeakEvLang.ediskStep` / `WeakEvInst.pdiskProg`): `pre` is the FOLDED part --
MachCSL's `DevM.modify`s and `DevM.guard`s since the previous fabric step -- and `(s, b) := pre v`;
  * `b = false`: THE ABORT -- label `LSilent`, the burst ends (`dp' = none`), the fabric becomes
    `s` (the moves `pre` made before the failing guard: MachCSL's task is BLOCKED at that guard,
    a zombie the matching schedule never steps again; matched 1 → 0);
  * `b = true`, `g s = some s'` and the footprint `ramBytes (pa s) |bs s|`: THE STORE -- label
    `LStore false (paZ (pa s)) (bs s)`, the fabric becomes `s'` IN THE SAME STEP (MachCSL's
    `dmaWrite` with a moving guard), the continuation is `k s`;
  * `b = true`, `g s = none` or a non-DRAM footprint: THE OWN-GUARD SKIP -- label `LSilent`,
    the fabric becomes `s`, the continuation is `k s` (`Lang.lean`'s `dmaWrite` no-op arm:
    "blocks nothing and writes nothing"; matched 1 → 1).
`pa`/`bs` are STATE-DEPENDENT (evaluated at `s`), and THE CONTINUATION RECEIVES `s`: a read
INSIDE the fabric step (MachCSL's `get`s folded into the write that follows them, [OWN.32]
ruling (a)), never a separate fabric-reading node.

`DPop h k`, at the fabric `v`: if `h` is already in flight (`(phase v h).isSome`) the pop is
REFUSED (`dp' = none`, the fabric unchanged -- MachCSL's refusal, back to the root loop);
otherwise `popState v h` (the head goes in flight at `.popped`, `seen + 1`) and `k` of it --
`Virtio.body`'s guard-pop, its own step, with `serve`'s first `get` (the descriptor addresses)
reading exactly the popped state.

## THE FOLDING RULE (binding, plan [R17.1])

Per MachCSL construct: (1) a `dmaWriteIf` / `dmaWriteStep`'s OWN guard (`reqOf s h = some r`;
the used index's `… ∧ usedIdx = ui ∧ cfg = c`) is the SAME node's `g` -- failure = SKIP;
(2) a `DevM.guard` (the capture latch `taken`; the `.pushed` gate) and the `DevM.modify`s since
the previous fabric step (`setPhase .fetched`, `.served`, `.status`, the capture's cache move)
are the NEXT fabric step's `pre` -- failure = (α) ABORT.  Every `pre` OPENS WITH THE IN-FLIGHT
PRE-CHECK `(phase s h).isSome` (failure: abort with NOTHING re-applied, `(s, false)`, so the
abort's fabric `setDvirtio d s` IS `d`, `WeakEvLang.setDvirtioSelf`) -- after a mid-burst
device reset (STATUS := 0 empties `inflight`) a `pre` without it would RESURRECT the request
on the empty map.  The used-index node is the exception the plan names: it has no folded move
(nothing between MachCSL's `get` after the gate and its index write), so its `pre` is the
identity and a lost request is an own-guard skip.

## The program, node by node (M1)–(M9), and what each node does to the fabric

    START (`pdiskProg`'s `dp = none` arm; snapshot = `body`'s root `get`: `live`, the avail /
      ring addresses, `seen`)                                     -- moves? its own step: no
                                                                     (d' = d); a `gfDev` member
                                                                     by CLASS (`LDev`)
    DRead avail idx (aq) ; DRead ring entry                       -- no
    DPop h  (guard-pop + `seen+1`; `serve`'s `get` for `cfg`)     -- YES
    3 × DRead descriptor (16 bytes each, `descOf`) ;
    DRead type ; DRead sector                                     -- no
      (a malformed chain: DRet DStall, a self-loop)               -- no
    OUT: (buf + len wraps past 2^64: DRet DStall, [OWN.40])       -- no
         DRead payload (elided at `len = 0`)                      -- no
         status DWriteDev, pre = check ; .fetched ; taken guard ;
                                 cache move + .served             -- YES
    IN, len ≠ 0: fill DWriteDev, pre = check ; .fetched ;
                 bytes = diskRead (cacheView s) at the write      -- YES
         status DWriteDev, pre = check ; .served                  -- YES
    IN, len = 0 / FLUSH / other:
         status DWriteDev, pre = check ; .fetched ; .served       -- YES
    used element DWriteDev, pre = check ; .status ; drainAll ;
         the gate `phase ∧ completeOk ∧ pushOk` → .pushed;
         continuation binds ui := s.usedIdx, c := s.cfg          -- YES
    DFence                                                        -- no
    used idx DWriteDev, pre = id, g = `serve`'s guard VERBATIM
         (reqOf ∧ usedIdx = ui ∧ cfg = c → complete)              -- YES
    DRet DIdle                                                    -- no

(the "moves the fabric?" column is what W13 (I)'s `gfDev` set is read off: the disk row's
members are START by class, the POP, and every fabric-moving `DWriteDev`; the `DRead`s, the
`DFence`, `DStall` and `DRet DIdle` move nothing).

Mismatch by mismatch against the pre-W-DISK program (mark = the ALIGNED program against the
spec):
 (M1) the used element is ONE 8-byte write of `usedLen r ++ head` -- FAITHFUL (was two 4-byte
      writes);
 (M2) its `len` is `usedLen r` (the device-writable part + the status byte) -- FAITHFUL (was
      the data length);
 (M3) a malformed chain STALLS (`Dres.DStall`, a silent self-loop mirroring `stall = await
      false`) -- a model choice on spec-unspecified behaviour, EQUAL to MachCSL, STRONGER than
      the retired arbitrary-store-chain arm; unreachable under the verified driver;
 (M4) the completion is FOLDED into the used-index write (`isr`, `usedIdx + 1`, the in-flight
      removal in the SAME pf step, [OWN.31]) -- EQUAL to MachCSL, STRONGER than "MAY then
      notify"; the separate COMMIT and its delta `vdelta` are RETIRED; ONE `DFence` sits
      immediately before the used-index write;
 (M5) zero-length data: the IN fill and the OUT capture read are EMITTED only when
      `r.len.toNat ≠ 0` (`r.len` is RAM content, so the program branches); MachCSL's zero-width
      ops are matched inside the next `DWriteDev`'s block; `DmWf` keeps `n ≠ 0`;
 (M5′) the store arm mirrors `dmaWrite`'s no-op arm (`¬ ramBytes ∨ g s = none → LSilent`);
      no `n = 0` disjunct (no emitted node has width 0);
 (M6) a descriptor is ONE 16-byte read decoded by `Virtio.descOf` -- FAITHFUL to the 16-byte
      structure (was four field reads);
 (M7) status = `Virtio.statusOf r` (FLUSH OK) -- a model choice on unspecified behaviour,
      vacuous for xv6;
 (M8) data from the CACHE-OVERLAID view: OUT's payload enters the `cache` at the status
      write's `pre` exactly as `capture` does (`cacheReq ∘ setPhase .served`); the request
      DRAINS at its completion gate -- `drainAll v = { v with disk := cacheView v, cache := [] }`
      inside the used-element write's `pre`, with `completeOk` VERBATIM (no pf-only gate);
      the IN fill reads `diskRead (cacheView s) (reqOff r) n` at the write's own `pre`-state;
 (M9) no START snapshot of `cfg` / `usedIdx` / `cacheView`: snapshots are taken where `serve`
      takes them -- START (`body`'s root `get`), POP (`serve`'s first `get`, via `DPop`'s
      continuation), the fill's `pre` (`fill`'s `get`), the used-element `pre` (the `get` after
      the gate: `usedIdx`, `cfg`, HANDED to the continuation and RE-TESTED at the index write,
      whose `usedIdx = ui ∧ cfg = c` conjuncts are KEPT -- a hart's configuration write between
      the two used writes makes both sides skip).

`R-dev` (the W4 F9 simulation's device clause, recorded here for its consumer): `dvirtio`
EQUAL on both sides, ALL fields (`disk` and `cache` included), with `cache = []` outside a
capture → gate window -- EXCEPT on the OUT CAPTURE SEGMENT (pf between the capture `DRead` and
the status `DWriteDev`), where MachCSL's state is `(pre₁ pf).1` with `pre₁ =
VirtioProg.preCaptureHead` = the status write's `pre` TRUNCATED before the capture's cache move
(check ; `.fetched` ; the `taken` guard): ONE formula for a free latch (1 → 3), a held latch
(1 → 1, MachCSL blocks at the guard) and a reset (pre-check identity, 1 → 0).  With `drainAll`
at the gate pf's durable image EQUALS MachCSL's at every pf-step boundary.

## Deviations from MachCSL's `serve`

The DM encoding; the folded guards (the FOLDING RULE above: own guard → skip, `DevM.guard` →
abort); and SEQUENTIAL single-request service (no `fork`: one request per burst, in ring
order, to completion before the next pop -- plan §B(11) (viii), [OWN.33]; STRONGER than virtio
and than MachCSL, the sound direction pf ⊆ MachCSL).  ONE pf-only node: the `DFence` before the
used-index write (`dusedTail`; 0 MachCSL steps -- `serve` goes from the used element to the
used index directly), on which the plan's §A(†) rule-4 ordering of (R1)'s disk use rests.
An OUT capture buffer wrapping past `2^64` stalls the request (Rocq deviation 6; [OWN.40]).
Also: the avail-index read keeps the M5 ACQUIRE bit (`aq = true`; MachCSL's DMA reads are at
the top of the store order, so the bit is pf-side only).

## Deviations from Rocq (the M5 file)

1. THE DEVICE STATE IS LEAN'S (`MachCSL.VirtioState`, the fabric `dvirtio (wgdev σ)`).
2. THE PROGRAM IS MACHCSL'S (above): the Rocq `VirtioModel` fragment (`virtio_req_step`,
   `virtio_complete`, `write_byte_list`, …), the write-map algebra (`dm_writes_map`, …) and
   the four equivalence theorems against the atomic step (`virtio_prog_req_step`, `_stalled`,
   `_idle`, `_trichotomy`, `_req_step_state`, `_done_step`) are RETIRED with it (nothing in
   `Weak/` consumed them); `run_virtio_prog` is RE-STATED as the flat-run SHAPE lemma over the
   aligned program (`runVirtioProg`: idle / refused / stall / the service of the decoded
   request).
3. THE MONAD: Rocq's `DWrite` (a plain write) is replaced by `DWriteDev`; `DPop` is new;
   `dres` is `DIdle | DStall` (Rocq's `DDone delta` retires with the COMMIT, its malformed-
   chain result with the stall).  `dwrite_word` / `dwrite_data` / `wcons` / `dtail`'s Rocq
   body / `vdelta` / `vdkf` / `vdata` / `vstatus` / `vused_elem` / `vused_ws` / `vprog_ws` /
   `vmodel_ws` / `run_dtail` / `run_dcomplete` retire with the plain write; `dtail` and
   `dusedTail` keep their names for the status write and the used-ring report.
4. BYTES: `PAddr` is `BitVec 64`; the little-endian decode is `MachCSL.bvOfBytes`, the encode
   `MachCSL.bytesOf` (every `DWriteDev` but the fill writes `bytesOf w` of MachCSL's own value
   `w`; the fill writes `diskRead …`, = `bytesOf (bvOfBytes n (diskRead …))`).
5. `runDm` threads the FABRIC state as well as the flat memory (a `DWriteDev` / `DPop` reads
   and moves it); the result is `Option A` (`none` = the burst ended without a result: an abort
   or a refused pop).
6. ([OWN.40], W4 F9) An OUT request whose capture buffer would wrap past `2^64`
   (`VirtioProg.outWraps`) STALLS (`DRet DStall`) instead of reading: FAITHFUL to the PMAs (no
   physical memory past the top of the address space), STRONGER than MachCSL's `serve` (whose
   `dmaRead` wraps its `PAddr`); the sound direction pf ⊆ MachCSL (the MachCSL task is simply
   never scheduled again).  Unreachable under xv6 (its buffers are 1 KiB, in DRAM).

## Name map (Rocq → Lean)

`vp_pa_add_0` `vpPaAdd0`; `DM`/`DRet`/`DRead`/`DFence` same; `dres` `Dres` (`DIdle`); `dm_wf`
`DmWf`; `dread_word` `dreadWord`; `dread_data` `dreadData`; `dread_avail_idx` `dreadAvailIdx`;
`dread_avail_ring` `dreadAvailRing`; `dread_desc` `dreadDesc`; `run_dm` `runDm`;
`run_dread_word` `runDreadWord`; `run_dread_data` `runDreadData`; `run_dread_avail_idx`
`runDreadAvailIdx`; `run_dread_avail_ring` `runDreadAvailRing`; `run_dread_desc`
`runDreadDesc`; `dused_tail` `dusedTail`; `dtail` `dtail`; `dcomplete` `dcomplete`;
`virtio_prog` `virtioProg`; `run_virtio_prog` `runVirtioProg` (re-stated); `dm_wf_dread_word`
`dmWfDreadWord`; `dm_wf_dread_data` `dmWfDreadData`; `dm_wf_dread_desc` `dmWfDreadDesc`;
`dm_wf_dtail` `dmWfDtail`; `dm_wf_dcomplete` `dmWfDcomplete`; `virtio_prog_wf` `virtioProgWf`.
`VirtioModel` names kept under `VirtioProg.` and re-stated over the aligned decode: `vmem`
`VMem`, `view_bytes` `viewBytes`, `view_word` `viewWord`, `desc_at` `descAt` (one 16-byte
read), `avail_idx_at` `availIdxAt`, `avail_ring_at` `availRingAt`, `req_at` `reqAt` (at a
head), `virtio_pending` `virtioPending`.
Lean-only (all `VirtioProg.`): `popState`, `drainAll`, `reqGuard`, `idxGuard`,
`preCaptureHead` (= the plan's `pre₁`), `outWraps`, `captureMove`, `preCapture`, `preFill`, `preServed`,
`preNoData`, `preGate`, `usedElemWord`, `idxNode`, `fillNode`, `fetchProg`; the constructors
`DWriteDev`, `DPop`, `DStall`; `DmWf.writeDev`/`.pop`; `dmWfIdxNode`, `dmWfFillNode`,
`dmWfFetchProg`, the pre-check lemmas `preCaptureHeadOut` … `preGateOut`, `runDreadDescEq`.
-/
import MachCSL.Dev.Virtio

namespace Weak

open MachCSL

/-! ## 0. Prelude: `pa_add a 0 = a`. -/

theorem vpPaAdd0 (a : PAddr) : a + BitVec.ofNat 64 0 = a := by simp

/-! ## 0b. The flat memory and the aligned decode (deviation 2) -/

namespace VirtioProg

/-- Memory as the device sees it (total). -/
abbrev VMem := PAddr → BitVec 8

/-- `n` bytes at `a`, as the device sees them. -/
def viewBytes (mv : VMem) (a : PAddr) (n : Nat) : List (BitVec 8) :=
  (List.range' 0 n).map (fun j => mv (a + BitVec.ofNat 64 j))

/-- An `n`-byte little-endian field, as the device sees it. -/
def viewWord (mv : VMem) (a : PAddr) (n : Nat) : BitVec (8 * n) :=
  bvOfBytes n (viewBytes mv a n)

/-- The available index (`Virtio.dma16` at `availIdxAddr`). -/
def availIdxAt (c : VirtioCfg) (mv : VMem) : BitVec 16 :=
  (viewWord mv (Virtio.availIdxAddr c) 2).extractLsb' 0 16

/-- The available-ring entry at position `i`. -/
def availRingAt (c : VirtioCfg) (mv : VMem) (i : BitVec 16) : BitVec 16 :=
  (viewWord mv (Virtio.availRingAddr c i) 2).extractLsb' 0 16

/-- A descriptor: ONE 16-byte read, decoded by `Virtio.descOf` (M6). -/
def descAt (c : VirtioCfg) (mv : VMem) (i : Nat) : Virtio.VqDesc :=
  Virtio.descOf (viewWord mv (Virtio.descAddr c i) 16)

/-- The request at head `h`, as `Virtio.fetch` decodes it; `none` on a malformed chain. -/
def reqAt (c : VirtioCfg) (mv : VMem) (h : BitVec 16) : Option VioReq :=
  let qnum := c.qnum.toNat
  if !decide (h.toNat < qnum) then none else
  let d0 := descAt c mv h.toNat
  if !d0.has Virtio.descFNext || !decide (d0.next.toNat < qnum) then none else
  let d1 := descAt c mv d0.next.toNat
  if !d1.has Virtio.descFNext || !decide (d1.next.toNat < qnum) then none else
  let d2 := descAt c mv d1.next.toNat
  if d2.has Virtio.descFNext then none else
  some { head := h, type := viewWord mv d0.addr 4, sector := viewWord mv (d0.addr + 8#64) 8,
         buf := d1.addr, len := d1.len, status := d2.addr, wr := d1.has Virtio.descFWrite }

/-- A request is pending: the queue is live and the avail index is not the pop index. -/
def virtioPending (v : VirtioState) (mv : VMem) : Bool :=
  Virtio.live v.cfg && decide (v.seen ≠ availIdxAt v.cfg mv)

end VirtioProg

open VirtioProg

/-! ## 1. The monad -/

inductive DM (A : Type) : Type where
  | DRet (a : A)
  | DRead (pa : PAddr) (n : Nat) (aq : Bool) (k : List (BitVec 8) → DM A)
  | DFence (k : DM A)
  /-- ONE FABRIC-MOVING RAM WRITE: the folded part `pre`, the own guard `g`, the
  state-dependent address and bytes, the state-receiving continuation (header). -/
  | DWriteDev (pre : VirtioState → VirtioState × Bool) (g : VirtioState → Option VirtioState)
      (pa : VirtioState → PAddr) (bs : VirtioState → List (BitVec 8)) (k : VirtioState → DM A)
  /-- THE RING POP of head `h` (header). -/
  | DPop (h : BitVec 16) (k : VirtioState → DM A)

export DM (DRet DRead DFence DWriteDev DPop)

/-- The result of one device burst: nothing (more) to do, or a stalled request (M3). -/
inductive Dres where
  | DIdle
  | DStall

export Dres (DIdle DStall)

/-! ## 2. Structural well-formedness: what the language's arms will require -/

inductive DmWf {A : Type} : DM A → Prop where
  | ret (a : A) : DmWf (DRet a)
  | read (pa : PAddr) (n : Nat) (aq : Bool) (k : List (BitVec 8) → DM A) :
      0 < n → (∀ bs, DmWf (k bs)) → DmWf (DRead pa n aq k)
  | fence (k : DM A) : DmWf k → DmWf (DFence k)
  /-- a `DWriteDev` writes a FIXED, NONZERO number of bytes at every state (M5) -/
  | writeDev (pre : VirtioState → VirtioState × Bool) (g : VirtioState → Option VirtioState)
      (pa : VirtioState → PAddr) (bs : VirtioState → List (BitVec 8)) (k : VirtioState → DM A)
      (n : Nat) : n ≠ 0 → (∀ s, (bs s).length = n) → (∀ s, DmWf (k s)) →
      DmWf (DWriteDev pre g pa bs k)
  | pop (h : BitVec 16) (k : VirtioState → DM A) : (∀ s, DmWf (k s)) → DmWf (DPop h k)

/-! ## 3. The typed read helpers -/

def dreadWord {A : Type} (pa : PAddr) (n : Nat) (aq : Bool) (k : BitVec (8 * n) → DM A) : DM A :=
  DRead pa n aq (fun bs => k (bvOfBytes n bs))

/-- a data transfer of zero bytes is no event at all (M5) -/
def dreadData {A : Type} (pa : PAddr) (n : Nat) (k : List (BitVec 8) → DM A) : DM A :=
  match n with
  | 0 => k []
  | n' + 1 => DRead pa (n' + 1) false k

/-- `Virtio.dma16` at the avail index, with the M5 acquire bit. -/
def dreadAvailIdx (c : VirtioCfg) (k : BitVec 16 → DM Dres) : DM Dres :=
  dreadWord (Virtio.availIdxAddr c) 2 true (fun w => k (w.extractLsb' 0 16))

/-- `Virtio.dma16` at a ring entry. -/
def dreadAvailRing (c : VirtioCfg) (i : BitVec 16) (k : BitVec 16 → DM Dres) : DM Dres :=
  dreadWord (Virtio.availRingAddr c i) 2 false (fun w => k (w.extractLsb' 0 16))

/-- ONE 16-byte descriptor read (M6). -/
def dreadDesc (c : VirtioCfg) (i : Nat) (k : Virtio.VqDesc → DM Dres) : DM Dres :=
  dreadWord (Virtio.descAddr c i) 16 false (fun w => k (Virtio.descOf w))

/-! ## 4. The folded parts and the guards (the FOLDING RULE, header) -/

namespace VirtioProg

/-- THE POP's move (`Virtio.body`'s guard): the head in flight at `.popped`, `seen + 1`. -/
def popState (v : VirtioState) (h : BitVec 16) : VirtioState :=
  { Virtio.setPhase v h .popped with seen := v.seen + 1#16 }

/-- THE GATE-TIME DRAIN (M8): every cached sector reaches the durable image. -/
def drainAll (v : VirtioState) : VirtioState :=
  { v with disk := Virtio.cacheView v, cache := [] }

/-- The status / used-element / fill writes' OWN guard (`dmaWriteIf (reqOf · h = some r)`). -/
def reqGuard (h : BitVec 16) (r : VioReq) (s : VirtioState) : Option VirtioState :=
  if decide (Virtio.reqOf s h = some r) then some s else none

/-- The used-index write's own guard, `serve`'s VERBATIM: it moves the state to `complete`. -/
def idxGuard (h : BitVec 16) (r : VioReq) (ui : BitVec 16) (c : VirtioCfg) (s : VirtioState) :
    Option VirtioState :=
  if decide (Virtio.reqOf s h = some r) && decide (s.usedIdx = ui) && decide (s.cfg = c) then
    some (Virtio.complete s h) else none

/-- **`pre₁`**: an OUT request's status `pre` TRUNCATED before the capture's cache move --
the in-flight pre-check, `setPhase .fetched`, the capture latch `taken` (`DevM.guard`). -/
def preCaptureHead (h : BitVec 16) (r : VioReq) (s : VirtioState) : VirtioState × Bool :=
  if (Virtio.phase s h).isSome then
    let s1 := Virtio.setPhase s h (.fetched r)
    if s1.taken = none then ({ s1 with taken := some h }, true) else (s1, false)
  else (s, false)

/-- The capture's move (`Virtio.capture`'s `modify`): the payload into the cache, `.served`. -/
def captureMove (h : BitVec 16) (r : VioReq) (bs : List (BitVec 8)) (v : VirtioState) :
    VirtioState :=
  Virtio.setPhase (if Virtio.reqOf v h = some r then Virtio.cacheReq v r bs else v) h (.served r)

/-- The OUT status write's `pre`: `pre₁`, then the capture's move. -/
def preCapture (h : BitVec 16) (r : VioReq) (bs : List (BitVec 8)) (s : VirtioState) :
    VirtioState × Bool :=
  let p := preCaptureHead h r s
  if p.2 then (captureMove h r bs p.1, true) else (p.1, false)

/-- The IN fill's `pre`: the pre-check, `setPhase .fetched`. -/
def preFill (h : BitVec 16) (r : VioReq) (s : VirtioState) : VirtioState × Bool :=
  if (Virtio.phase s h).isSome then (Virtio.setPhase s h (.fetched r), true) else (s, false)

/-- The status `pre` after a fill: the pre-check, `setPhase .served`. -/
def preServed (h : BitVec 16) (r : VioReq) (s : VirtioState) : VirtioState × Bool :=
  if (Virtio.phase s h).isSome then (Virtio.setPhase s h (.served r), true) else (s, false)

/-- The status `pre` with no data node (a zero-length IN, FLUSH, an unknown type): the
pre-check, `setPhase .fetched`, `setPhase .served`. -/
def preNoData (h : BitVec 16) (r : VioReq) (s : VirtioState) : VirtioState × Bool :=
  if (Virtio.phase s h).isSome then
    (Virtio.setPhase (Virtio.setPhase s h (.fetched r)) h (.served r), true)
  else (s, false)

/-- The used element's `pre`: the pre-check, `setPhase .status`, THE DRAIN, and the gate with
`completeOk` VERBATIM (M8). -/
def preGate (h : BitVec 16) (r : VioReq) (s : VirtioState) : VirtioState × Bool :=
  if (Virtio.phase s h).isSome then
    let s2 := drainAll (Virtio.setPhase s h (.status r))
    if (Virtio.phase s2 h).isSome && Virtio.completeOk s2 r h && Virtio.pushOk s2 then
      (Virtio.setPhase s2 h (.pushed r), true)
    else (s2, false)
  else (s, false)

/-- The used element `id:4 len:4`, little-endian (`len` the high word), MachCSL's value. -/
def usedElemWord (r : VioReq) : BitVec (8 * 8) :=
  Virtio.castW (by decide : 64 = 8 * 8) ((Virtio.usedLen r) ++ (r.head.setWidth 32))

/-- THE USED-INDEX WRITE, AND THE COMPLETION, in one fabric step (M4). -/
def idxNode (h : BitVec 16) (r : VioReq) (ui : BitVec 16) (c : VirtioCfg) : DM Dres :=
  DWriteDev (fun s => (s, true)) (idxGuard h r ui c) (fun _ => Virtio.usedIdxAddr c)
    (fun _ => bytesOf (n := 2) (ui + 1#16)) (fun _ => DRet DIdle)

end VirtioProg

/-! ## 5. The device program -/

/-- THE USED-RING REPORT: the used element (its `pre` the gate), FENCE, the used index. -/
def dusedTail (h : BitVec 16) (r : VioReq) : DM Dres :=
  DWriteDev (preGate h r) (reqGuard h r) (fun s => Virtio.usedElemAddr s.cfg s.usedIdx)
    (fun _ => bytesOf (usedElemWord r)) (fun s => DFence (idxNode h r s.usedIdx s.cfg))

/-- THE STATUS BYTE (its `pre` the folded moves since the previous fabric step), then the
report. -/
def dtail (h : BitVec 16) (r : VioReq) (pre : VirtioState → VirtioState × Bool) : DM Dres :=
  DWriteDev pre (reqGuard h r) (fun _ => r.status) (fun _ => bytesOf (n := 1) (Virtio.statusOf r))
    (fun _ => dusedTail h r)

/-- THE FILL (an IN request with `len ≠ 0`): the cache-overlaid image at the write's state. -/
def VirtioProg.fillNode (h : BitVec 16) (r : VioReq) : DM Dres :=
  DWriteDev (preFill h r) (reqGuard h r) (fun _ => r.buf)
    (fun s => Virtio.diskRead (Virtio.cacheView s) (Virtio.reqOff r) r.len.toNat)
    (fun _ => dtail h r (preServed h r))

/-- An OUT payload buffer that would WRAP past the top of the physical address space
(`buf + len > 2^64`; [OWN.40]): no physical memory is there (the PMAs), and the pf read
(Int addresses, `imgZ` aliasing the boot image past `2^64`) and MachCSL's (wrapping `PAddr`
arithmetic) would disagree. -/
def VirtioProg.outWraps (r : VioReq) : Bool := decide (2 ^ 64 < r.buf.toNat + r.len.toNat)

/-- THE SERVICE of a decoded request, from after its fetch to its completion. -/
def dcomplete (h : BitVec 16) (r : VioReq) : DM Dres :=
  if r.type.toNat = Virtio.blkTOut then
    -- a capture buffer wrapping past `2^64` STALLS the request ([OWN.40], deviation 6)
    if VirtioProg.outWraps r then DRet DStall else
    -- THE CAPTURE: the payload read (elided at `len = 0`), folded into the status `pre`
    dreadData r.buf r.len.toNat (fun bs => dtail h r (preCapture h r bs))
  else if r.type.toNat = Virtio.blkTIn ∧ r.len.toNat ≠ 0 then
    VirtioProg.fillNode h r
  else
    dtail h r (preNoData h r)

/-- THE FETCH (`Virtio.fetch`): three 16-byte descriptor reads and the header; a malformed
chain stalls. -/
def VirtioProg.fetchProg (c : VirtioCfg) (h : BitVec 16) : DM Dres :=
  let qnum := c.qnum.toNat
  if !decide (h.toNat < qnum) then DRet DStall else
  dreadDesc c h.toNat (fun d0 =>
  if !d0.has Virtio.descFNext || !decide (d0.next.toNat < qnum) then DRet DStall else
  dreadDesc c d0.next.toNat (fun d1 =>
  if !d1.has Virtio.descFNext || !decide (d1.next.toNat < qnum) then DRet DStall else
  dreadDesc c d1.next.toNat (fun d2 =>
  if d2.has Virtio.descFNext then DRet DStall else
  dreadWord d0.addr 4 false (fun ty =>
  dreadWord (d0.addr + 8#64) 8 false (fun sec =>
  dcomplete h { head := h, type := ty, sector := sec, buf := d1.addr, len := d1.len,
                status := d2.addr, wr := d1.has Virtio.descFWrite })))))

/-- THE BURST, from the START snapshot `v` (`body`'s root `get`): the avail index, the ring
entry, THE POP, the service. -/
def virtioProg (v : VirtioState) : DM Dres :=
  if Virtio.live v.cfg then
    dreadAvailIdx v.cfg (fun ai =>
    if v.seen ≠ ai then
      dreadAvailRing v.cfg v.seen (fun h => DPop h (fun s => fetchProg s.cfg h))
    else DRet DIdle)
  else DRet DIdle

/-! ### every `pre` opens with the in-flight pre-check -/

theorem preCaptureHeadOut (h : BitVec 16) (r : VioReq) (s : VirtioState)
    (hn : Virtio.phase s h = none) : preCaptureHead h r s = (s, false) := by
  simp [preCaptureHead, hn]

theorem preCaptureOut (h : BitVec 16) (r : VioReq) (bs : List (BitVec 8)) (s : VirtioState)
    (hn : Virtio.phase s h = none) : preCapture h r bs s = (s, false) := by
  simp [preCapture, preCaptureHeadOut h r s hn]

theorem preFillOut (h : BitVec 16) (r : VioReq) (s : VirtioState)
    (hn : Virtio.phase s h = none) : preFill h r s = (s, false) := by
  simp [preFill, hn]

theorem preServedOut (h : BitVec 16) (r : VioReq) (s : VirtioState)
    (hn : Virtio.phase s h = none) : preServed h r s = (s, false) := by
  simp [preServed, hn]

theorem preNoDataOut (h : BitVec 16) (r : VioReq) (s : VirtioState)
    (hn : Virtio.phase s h = none) : preNoData h r s = (s, false) := by
  simp [preNoData, hn]

theorem preGateOut (h : BitVec 16) (r : VioReq) (s : VirtioState)
    (hn : Virtio.phase s h = none) : preGate h r s = (s, false) := by
  simp [preGate, hn]

/-! ## 6. The flat runner -/

/-- Run the program at a flat memory `mv` and a fabric state that only the program moves
(deviation 5): `none` = the burst ended without a result (an abort, a refused pop). -/
def runDm {A : Type} (mv : VMem) :
    VirtioState → DM A → Option A × List (PAddr × List (BitVec 8)) × VirtioState
  | s, DRet a => (some a, [], s)
  | s, DRead pa n _ k => runDm mv s (k (viewBytes mv pa n))
  | s, DFence k => runDm mv s k
  | s, DWriteDev pre g pa bs k =>
      if (pre s).2 then
        match g (pre s).1 with
        | some s' =>
            ((runDm mv s' (k (pre s).1)).1,
             (pa (pre s).1, bs (pre s).1) :: (runDm mv s' (k (pre s).1)).2.1,
             (runDm mv s' (k (pre s).1)).2.2)
        | none => runDm mv (pre s).1 (k (pre s).1)
      else (none, [], (pre s).1)
  | s, DPop h k =>
      if (Virtio.phase s h).isSome then (none, [], s)
      else runDm mv (popState s h) (k (popState s h))

theorem runDreadWord {A : Type} (mv : VMem) (s : VirtioState) (pa : PAddr) (n : Nat) (aq : Bool)
    (k : BitVec (8 * n) → DM A) :
    runDm mv s (dreadWord pa n aq k) = runDm mv s (k (viewWord mv pa n)) := rfl

theorem runDreadData {A : Type} (mv : VMem) (s : VirtioState) (pa : PAddr) (n : Nat)
    (k : List (BitVec 8) → DM A) :
    runDm mv s (dreadData pa n k) = runDm mv s (k (viewBytes mv pa n)) := by
  cases n <;> rfl

theorem runDreadAvailIdx (mv : VMem) (s : VirtioState) (c : VirtioCfg) (k : BitVec 16 → DM Dres) :
    runDm mv s (dreadAvailIdx c k) = runDm mv s (k (availIdxAt c mv)) := rfl

theorem runDreadAvailRing (mv : VMem) (s : VirtioState) (c : VirtioCfg) (i : BitVec 16)
    (k : BitVec 16 → DM Dres) :
    runDm mv s (dreadAvailRing c i k) = runDm mv s (k (availRingAt c mv i)) := rfl

/-- The 16-byte read decodes by `descOf` (replaces the four-read `rfl` conversion, M6). -/
theorem runDreadDesc (mv : VMem) (s : VirtioState) (c : VirtioCfg) (i : Nat)
    (k : Virtio.VqDesc → DM Dres) :
    runDm mv s (dreadDesc c i k) = runDm mv s (k (descAt c mv i)) := rfl

/-- ... and the decode IS `descOf` of the viewed word (Lean-only). -/
theorem runDreadDescEq (c : VirtioCfg) (mv : VMem) (i : Nat) :
    descAt c mv i = Virtio.descOf (bvOfBytes 16 (viewBytes mv (Virtio.descAddr c i) 16)) := rfl

/-! ## 7. THE SHAPE of the flat run -/

/-- The flat run of `virtioProg v` is one of exactly four shapes, each pinned to the decode:
nothing pending; the popped head already in flight (refused); a malformed chain (stall); or
the service `dcomplete` of the decoded request from the popped state. -/
theorem runVirtioProg (v : VirtioState) (mv : VMem) :
    (virtioPending v mv = false ∧ runDm mv v (virtioProg v) = (some DIdle, [], v)) ∨
    (virtioPending v mv = true ∧
      (Virtio.phase v (availRingAt v.cfg mv v.seen)).isSome = true ∧
      runDm mv v (virtioProg v) = (none, [], v)) ∨
    (virtioPending v mv = true ∧
      (Virtio.phase v (availRingAt v.cfg mv v.seen)).isSome = false ∧
      reqAt v.cfg mv (availRingAt v.cfg mv v.seen) = none ∧
      runDm mv v (virtioProg v) =
        (some DStall, [], popState v (availRingAt v.cfg mv v.seen))) ∨
    (∃ r, virtioPending v mv = true ∧
      (Virtio.phase v (availRingAt v.cfg mv v.seen)).isSome = false ∧
      reqAt v.cfg mv (availRingAt v.cfg mv v.seen) = some r ∧
      runDm mv v (virtioProg v) =
        runDm mv (popState v (availRingAt v.cfg mv v.seen))
          (dcomplete (availRingAt v.cfg mv v.seen) r)) := by
  unfold virtioProg virtioPending
  by_cases hl : Virtio.live v.cfg = true
  case neg =>
    left
    simp only [hl, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    exact ⟨trivial, rfl⟩
  simp only [hl, Bool.true_and, ↓reduceIte]
  rw [runDreadAvailIdx]
  by_cases hai : v.seen = availIdxAt v.cfg mv
  · left
    simp only [hai, ne_eq, not_true_eq_false, decide_false, ↓reduceIte]
    exact ⟨trivial, rfl⟩
  simp only [hai, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
  right
  rw [runDreadAvailRing]
  generalize hh : availRingAt v.cfg mv v.seen = h
  show _ ∨ _ ∨ _
  by_cases hph : (Virtio.phase v h).isSome = true
  · left
    refine ⟨trivial, hph, ?_⟩
    show (if (Virtio.phase v h).isSome then _ else _) = _
    rw [if_pos hph]
  have hph' : (Virtio.phase v h).isSome = false := by simpa using hph
  have hrun : runDm mv v (DPop h (fun s => fetchProg s.cfg h)) =
      runDm mv (popState v h) (fetchProg v.cfg h) := by
    show (if (Virtio.phase v h).isSome then _ else _) = _
    rw [if_neg hph]
    rfl
  rw [hrun]
  right
  unfold fetchProg reqAt
  by_cases h1 : h.toNat < v.cfg.qnum.toNat
  case neg =>
    left
    simp only [h1, decide_false, Bool.not_false, ↓reduceIte]
    exact ⟨trivial, hph', trivial, rfl⟩
  simp only [h1, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [runDreadDesc]
  generalize hd0 : descAt v.cfg mv h.toNat = d0
  by_cases h2 : (!d0.has Virtio.descFNext || !decide (d0.next.toNat < v.cfg.qnum.toNat)) = true
  · left
    simp only [h2, ↓reduceIte]
    exact ⟨trivial, hph', trivial, rfl⟩
  simp only [h2, Bool.false_eq_true, ↓reduceIte]
  rw [runDreadDesc]
  generalize hd1 : descAt v.cfg mv d0.next.toNat = d1
  by_cases h3 : (!d1.has Virtio.descFNext || !decide (d1.next.toNat < v.cfg.qnum.toNat)) = true
  · left
    simp only [h3, ↓reduceIte]
    exact ⟨trivial, hph', trivial, rfl⟩
  simp only [h3, Bool.false_eq_true, ↓reduceIte]
  rw [runDreadDesc]
  generalize hd2 : descAt v.cfg mv d1.next.toNat = d2
  by_cases h4 : d2.has Virtio.descFNext = true
  · left
    simp only [h4, ↓reduceIte]
    exact ⟨trivial, hph', trivial, rfl⟩
  simp only [h4, Bool.false_eq_true, ↓reduceIte]
  right
  rw [runDreadWord, runDreadWord]
  exact ⟨_, trivial, hph', rfl, rfl⟩

/-! ## 8. Structural well-formedness of the device program -/

theorem dmWfDreadWord {A : Type} (pa : PAddr) (n : Nat) (aq : Bool) (k : BitVec (8 * n) → DM A)
    (hn : 0 < n) (hk : ∀ x, DmWf (k x)) : DmWf (dreadWord pa n aq k) :=
  .read _ _ _ _ hn (fun _ => hk _)

theorem dmWfDreadData {A : Type} (pa : PAddr) (n : Nat) (k : List (BitVec 8) → DM A)
    (hk : ∀ bs, DmWf (k bs)) : DmWf (dreadData pa n k) := by
  cases n with
  | zero => exact hk _
  | succ n' => exact .read _ _ _ _ (Nat.succ_pos _) hk

theorem dmWfDreadDesc (c : VirtioCfg) (i : Nat) (k : Virtio.VqDesc → DM Dres)
    (hk : ∀ d, DmWf (k d)) : DmWf (dreadDesc c i k) :=
  dmWfDreadWord _ _ _ _ (by decide) (fun _ => hk _)

theorem VirtioProg.dmWfIdxNode (h : BitVec 16) (r : VioReq) (ui : BitVec 16) (c : VirtioCfg) :
    DmWf (idxNode h r ui c) :=
  .writeDev _ _ _ _ _ 2 (by decide) (fun _ => bytesOf_length _) (fun _ => .ret _)

theorem dmWfDusedTail (h : BitVec 16) (r : VioReq) : DmWf (dusedTail h r) :=
  .writeDev _ _ _ _ _ 8 (by decide) (fun _ => bytesOf_length _)
    (fun _ => .fence _ (VirtioProg.dmWfIdxNode _ _ _ _))

theorem dmWfDtail (h : BitVec 16) (r : VioReq) (pre : VirtioState → VirtioState × Bool) :
    DmWf (dtail h r pre) :=
  .writeDev _ _ _ _ _ 1 (by decide) (fun _ => bytesOf_length _) (fun _ => dmWfDusedTail h r)

theorem VirtioProg.dmWfFillNode (h : BitVec 16) (r : VioReq) (hn : r.len.toNat ≠ 0) :
    DmWf (fillNode h r) :=
  .writeDev _ _ _ _ _ r.len.toNat hn (fun _ => by simp [Virtio.diskRead])
    (fun _ => dmWfDtail _ _ _)

theorem dmWfDcomplete (h : BitVec 16) (r : VioReq) : DmWf (dcomplete h r) := by
  unfold dcomplete
  split
  · split
    · exact .ret _
    · exact dmWfDreadData _ _ _ (fun _ => dmWfDtail _ _ _)
  · split
    · next hin => exact VirtioProg.dmWfFillNode h r hin.2
    · exact dmWfDtail _ _ _

theorem VirtioProg.dmWfFetchProg (c : VirtioCfg) (h : BitVec 16) : DmWf (fetchProg c h) := by
  unfold fetchProg
  dsimp only
  split
  · exact .ret _
  refine dmWfDreadDesc _ _ _ (fun d0 => ?_)
  split
  · exact .ret _
  refine dmWfDreadDesc _ _ _ (fun d1 => ?_)
  split
  · exact .ret _
  refine dmWfDreadDesc _ _ _ (fun d2 => ?_)
  split
  · exact .ret _
  refine dmWfDreadWord _ _ _ _ (by decide) (fun ty => ?_)
  refine dmWfDreadWord _ _ _ _ (by decide) (fun sec => ?_)
  exact dmWfDcomplete _ _

theorem virtioProgWf (v : VirtioState) : DmWf (virtioProg v) := by
  unfold virtioProg dreadAvailIdx dreadAvailRing
  split
  · refine dmWfDreadWord _ _ _ _ (by decide) (fun ai => ?_)
    dsimp only
    split
    · refine dmWfDreadWord _ _ _ _ (by decide) (fun h => ?_)
      exact .pop _ _ (fun s => VirtioProg.dmWfFetchProg _ _)
    · exact .ret _
  · exact .ret _

end Weak
