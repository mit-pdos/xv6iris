# Design: the virtio disk DRIVER side — concurrent-request protocol, DMA handoff, disk points-to

This is the design for specifying and proving the four driver functions of
`kernel/virtio_disk.c` — `virtio_disk_init`, `free_desc`, `virtio_disk_rw`,
`virtio_disk_intr` (`alloc_desc`/`free_chain`/`alloc3_desc` are inlined by the
compiler) — over the machine-side model that already exists
([`device.md`](device.md), [`../projects/virtio-disk.md`](../projects/virtio-disk.md)).
The machine side (VirtioModel.v / WpVirtio.v / `wp_dev_loop`) is done; this
file is about the DRIVER's ownership story.

## The problem in one paragraph

`virtio_disk_rw` builds a three-descriptor chain in memory the driver owns,
then *publishes* it by bumping `avail->idx`. From that store on, the DEVICE
reads the chain, the request header, and (for a write) the data buffer, and
writes the status byte, (for a read) the data buffer, and the used ring — all
by DMA, concurrently with every CPU. Later `virtio_disk_intr` observes the
completion in the used ring and hands the buffer back to the sleeping process.
So the proof needs (a) a byte-ownership story in which every DMA'd byte is
owned by the device invariant exactly while the device may touch it, (b) a
protocol that lets the publisher deposit resources at the publish store and the
interrupt handler withdraw them at the completion read, and (c) a *disk
points-to* so the spec of `virtio_disk_rw` can say what a read returns and what
a write does to the disk.

## Position sequence numbers: `nat`, not `bv 16`

Both rings are indexed by free-running 16-bit counters. All protocol state is
keyed by the NAT sequence number of a request (position `p`: the p-th request
ever published), and the bridge to the machine is `wrap16 p := Z_to_bv 16 (Z.of_nat p)`.
Three counters order every event, and they only ever grow:

    nr  — reclaimed: positions whose resources the driver has withdrawn
    nc  — completed: the device's progress (v_seen = v_used_idx = wrap16 nc)
    np  — published: the driver's progress (avail idx bytes hold wrap16 np)

with `nr ≤ nc ≤ np`. The protocol state splits the window into
`pend` (dom = `[nc, np)`, contiguous — the device serves strictly in order) and
`done` (dom ⊆ `[nr, nc)`, *not* necessarily contiguous). Wrap-around never
needs 16-bit window reasoning: every pending/done slot pins its own avail-ring
entry (2 bytes at `avail+4+2*(p mod 8)`), the pins are disjoint sub-maps of the
lease, so positions in the window are distinct mod 8, hence `np − nr ≤ 8 < 2^16`
and `wrap16` is injective on the window. That one separation fact replaces all
ring-index arithmetic.

## The slot: what one in-flight request pins and owns

For a request at position `p` (all geometry is `qnum = 8`, the only
configuration ever live):

Pinned (read-only for the device, part of `ctl ⊆ dma`), the slot's `pin` map:
- the avail-ring entry at `avail+4+2*(p mod 8)` (2 bytes) — names the head `h`;
- the three descriptor entries `desc+16*h / *m / *t` (48 bytes) — the chain;
- the request header `ops[h]` = `disk+0xa8+16*h` (16 bytes) — type + sector;
- for a WRITE (`VIRTIO_BLK_T_OUT`): the 1024 data bytes at `b->data`.
  Pinning the OUT payload is what makes the device's disk update
  *deterministic*, hence expressible as a ghost update on the disk auth.

Leased writable (in `dma ∖ ctl`):
- the status byte `&disk.info[h].status` = `disk+0x30+16*h` (1 byte);
- for a READ (`VIRTIO_BLK_T_IN`): the 1024 data bytes at `b->data`.

Standing (position-independent, leased from init to forever):
- the WHOLE used ring page (device-writable);
- the avail `idx` field (2 bytes at `avail+2`, in `ctl`, content `wrap16 np`).

The pure record (`VirtioQueue.v`, iris-free):

    Record vslot := VSlot {
      vs_req  : vio_req;         (* the parsed request; type ∈ {IN, OUT} *)
      vs_data : list (bv 8);     (* THE BLOCK'S CONTENT, both directions:
                                    OUT the payload the driver is writing,
                                    IN  the content the driver asserts the
                                        block already has *)
    }.

**`vs_data` records the block for a READ too, and that is load-bearing.**
`slot_pend_res` pins `vs_is_out sl = false → bs = vs_data sl` (an OUT
request's *current* content is arbitrary — the device is about to overwrite
it — so that half stays existential), and `slot_done_res` /
`virtio_proto_reclaim_acc` / `DiskInv.parked_res` then export the
unconditional `bs = vs_data sl`.  Without it a publisher that hands its
exclusive `disk_block` fragments into the pending resource and then SLEEPS
gets them back as an opaque list and can never identify them with what its
caller gave it — `virtio_disk_rw`'s read postcondition is unprovable.
General rule: **an invariant that takes an exclusive ghost fragment across a
sleep must record the fragment's VALUE.**

`slot_pin_ok c p sl pin` says: for EVERY view `mv` agreeing with `pin`,
`req_at c mv (wrap16 p) = Some (vs_req sl)`, the ring entry bytes are in `pin`,
the type is IN or OUT with `vr_len = 1024`, and for OUT
`view_bytes mv (vr_buf) 1024 = vs_data sl`. Because the request is a function
of the pin alone, the device step from position `p` is DETERMINED:
`vslot_step` computes the exact post-state and write-set
(`virtio_complete` at a determined request; the only view-dependence left is
the OUT payload, which the pin fixes). The status byte a step writes is
`0` (OK), because the type is IN/OUT — that is what refutes
`virtio_disk_intr`'s status panic.

`vproto_ok c nc np pend done ctl dma_dom` (pure) packages: pend/done domains as
above; `ctl` = the avail-idx bytes (content `wrap16 np`) ∪ the disjoint union
of all pins of `pend ∪ done`; every slot `slot_pin_ok`; write-sets bounded by
the lease and missing `ctl`; the used-page ⊆ dma; and the used-ring
completion records: for `p ∈ done`, the used element at `used+4+8*(p mod 8)`
holds `id = vr_head` (as bv 32) and the status byte holds 0. From it the FLAT
`virtio_queue_ok c ctl dma_dom S ai sn` of VirtioModel §7 is DERIVED
(`S = wrap16 <$> dom pend`, `ai = wrap16 np`, `sn = wrap16 nc`), so the
device-thread rules (`virtio_lease_not_stalled` / the step rule) keep working
off the flat form; the keyed form is what the driver's surgery manipulates:

- `vproto_publish` : append `np ↦ sl` given `slot_pin_ok` for the new pin,
  pin disjoint from dma, avail-idx bytes updated to `wrap16 (np+1)`.
- `vproto_step`    : the device consumes position `nc` (pend → done, nc+1);
  the write set is exactly `vslot_step`'s, so the used-ring record for `nc`
  and the status-byte-0 fact come out.
- `vproto_reclaim` : remove any `p ∈ done`; `ctl`/`dma` shrink by `pin(p)` and
  the slot's writable bytes; every other slot survives (their footprints are
  disjoint sub-maps).

## The Iris protocol: `virtio_proto` replaces `virtio_lease` in `dev_inv_body`

New ghost names bundle `disk_names` (class `diskGhostG`, wired through
`riscvΣ` like `uart_names`):

    γslot : ghost_map nat vslot     (* auth in proto; fragment = the RECEIPT *)
    γdk   : ghost_map Z   (bv 8)    (* the disk image auth; fragment = disk points-to *)
    γnc   : mono_nat                (* completed-count lower bounds, for intr *)

    disk_byte  o b  := o ↪[γdk] b
    disk_bytes o bs := [∗ list] j ↦ b ∈ bs, disk_byte (o + j) b
    disk_block bno bs := ⌜length bs = 1024⌝ ∗ disk_bytes (1024 * bno) bs

`virtio_proto γ v` (in `dev_inv_body`, replacing `virtio_lease v`; WpVirtio's
`dma_own`/`dma_agree`/`dma_update` stay as the base layer):

    ∃ nc np pend done ctl dma dmap,
      dma_own dma ∗ ⌜ctl ⊆ dma⌝ ∗
      ⌜vproto_ok (v_cfg v) nc np pend done ctl (dom dma)⌝ ∗
      ⌜v_seen v = wrap16 nc ∧ v_used_idx v = wrap16 nc⌝ ∗
      ghost_map_auth γslot 1 (pend ∪ done) ∗
      mono_nat_auth γnc 1 nc ∗
      ghost_map_auth γdk 1 dmap ∗ ⌜disk_view dmap (v_disk v)⌝ ∗
      ([∗ map] p ↦ sl ∈ pend, slot_res sl) ∗
      ([∗ map] p ↦ sl ∈ done, slot_res sl)

where `disk_view dmap dk := ∀ o b, dmap !! o = Some b → dk o = b` (the disk
analogue of `mem_view` — fragments exist only for offsets somebody minted, the
device model's disk stays total), and

    slot_res sl := disk_bytes (sector*512 of sl) (cur sl)
      (* IN:  cur = vs_data sl, pinned at deposit AND at completion (the
              device does not write the disk, so the fragments are unchanged);
         OUT: pending → cur = the OLD contents (existential at deposit);
              done    → cur = vs_data sl (the ghost update happened at the step) *)

When the queue is not live, `virtio_proto` degenerates to the empty lease +
empty auths (what adequacy allocates; `virtio_proto_init`).

The four PROTOCOL OPERATIONS, as view shifts over `virtio_proto` (each used
inside a `dev_inv`-opening leaf; conclusions ⌜…⌝ mean facts learned):

1. **publish** (rw's `sh` to `avail+2`): consumes the new slot's pin bytes +
   writable bytes (as `phys_pointsto`, disjoint from `dma` by ownership), the
   `disk_bytes` deposit, and produces the receipt `np ↪[γslot] sl` +
   ⌜the store's old bytes were `wrap16 np`⌝.
2. **observe-used-idx** (intr's / rw-irrelevant `lhu` of `used+2`): read-only;
   produces ⌜loaded = wrap16 nc⌝ ∗ `mono_nat_lb γnc nc`.
3. **reclaim** (intr's `lw` of the used element at `p mod 8`): consumes the
   receipt `p ↪[γslot] sl` + `mono_nat_lb γnc c` with `p < c`; since receipts
   live in `pend ∪ done` = `[nr', np)` and `p < c ≤ nc`, position `p ∈ done`;
   produces ⌜loaded id = vr_head (vs_req sl)⌝ ∗ the PAYOFF: all of `pin(p)`
   and the slot's writable bytes back as `phys_pointsto` — the status byte
   with value 0, the buffer holding (IN) the block's contents / (OUT) the
   payload — ∗ `disk_bytes` at the block's (new) contents.
4. **device step** (`wp_dev_loop` only): `vproto_step` + the `γdk` update for
   an OUT slot + `mono_nat` bump; packaged as `virtio_proto_step`, plus
   `virtio_proto_not_stalled` refuting `DevStepDiskWild`. These two are what
   `WpUart.wp_dev_loop`'s disk case now consumes.

MMIO writes the driver performs while live (`QUEUE_NOTIFY`, `INTERRUPT_ACK`)
are cfg/seen/used-idx-stable, so `virtio_proto` rides through them
(`virtio_proto_stable`, the analogue of `virtio_lease_stable`).

## `disk_res`: what `vdisk_lock` protects

`is_lock γvd disk_lock "virtio_disk" disk_res`, with (all cells as physical
points-tos of the static `struct disk` at `KernelSyms.disk`; geometry:
desc ptr +0, avail ptr +8, used ptr +16, `free[8]` +0x18, `used_idx` +0x20,
`info[i].b` +0x28+16i, `info[i].status` +0x30+16i, `ops[i]` +0xa8+16i,
`vdisk_lock` +0x128):

    disk_res γ := ∃ (nr np_d : nat) (flight : gmap nat flight_info) …,
      (* the three queue-page pointer cells, holding pd/pav/pu *)
      (* used_idx cell ↦ wrap16 nr *)
      (* per descriptor i < 8: free[i] cell ↦ bit_i, and if bit_i = 1:
           the 16 desc-entry bytes at pd+16i ∗ ops[i] (16 bytes) ∗
           info[i].status byte *)
      (* info[i].b cells, pinned to fl_buf for i = head of some flight slot *)
      (* per p ∈ dom flight = [nr, np_d): the receipt p ↪[γslot] (fl_slot p),
           the b->disk word of that request's buf ↦ 1, … *)
      (* parked payoffs for completed-and-processed requests keyed by
           position, deposited by intr, withdrawn by the sleeping rw *)
      (* the inert remainders of the three pages (bytes no one touches) *)

Key moves, all under the lock, all plain owned accesses (NO invariant opening):
- **alloc_desc**: find `free[i] = 1`, clear it, take the desc entry + ops +
  status bytes out of `disk_res`.
- **free_desc(i)**: caller returns those bytes; the `free[i]` panic arm is
  refuted by SEPARATION (if `free[i] = 1`, `disk_res` also owns the desc-entry
  bytes the caller is holding — two full points-tos, `False`); the `i < 8` arm
  by the caller's pure bound. Then `wakeup(&disk.free[0])`.
- **rw's descriptor formatting**: plain stores to bytes rw took at alloc.
- **intr's processing**: withdraws payoff at the reclaim leaf (see above),
  writes `b->disk = 0` (the cell is in the flight entry), moves the flight
  entry to a parked payoff, bumps the `used_idx` cell to `wrap16 (nr+1)`.
- **rw's completion wait**: the loop's `lw b->disk` reads the cell from the
  flight entry (value 1 → `sleep(b, &disk.vdisk_lock)`) or from the parked
  payoff (value 0 → exit); after exit rw withdraws the parked payoff — buffer
  contents, status 0, `disk_bytes` — then `free_chain` returns the descriptor
  bytes via `free_desc`, and `release`.

### The CLAIM is what a woken publisher has left

`dn_claim` is a `ghost_map nat dclaim` (DiskPtsto.v); the auth is in
`disk_res` over `flight ∪ parked` and the fragment is the publisher's. After
`sleep` it is the ONLY handle the process still holds on its own request, so
its value has to carry every fact the rest of `virtio_disk_rw` needs:

    Record dclaim := DClaim {
      dc_buf  : Arch.pa;                (* which struct buf              *)
      dc_slot : vslot;                  (* fixes vs_data / vs_sector_off *)
      dc_tri  : nat * nat * nat;        (* the chain's three descriptors *)
      dc_pin  : gmap Arch.pa (bv 8);    (* the pinned bytes              *)
    }.

`flight_res`/`parked_res` take the record — no existentials over buffer, slot
or pin. Two of the fields exist for reasons that are not obvious:

* `dc_tri`, plus the `disk_res` conjunct
  `∀ p v, (fl ∪ pk) !! p = Some v → tr !! p = Some (dc_tri v)`, is what lets
  the publisher read "my three descriptors are still allocated" (`fr i =
  false`) off the triple bookkeeping. It cannot be carried as a pure fact
  instead: `fr` is a different function after every `sleep`.
* `dc_pin` makes the parked payoff's residual pin CONCRETE
  (`dc_pinr pav p v := dc_pin v ∖ dc_ring_map pav p v`). An existential pin
  would hand the publisher an opaque `phys_map` out of which the descriptor
  words `free_chain` must return could never be recovered.

Naming the pin is necessary but not sufficient: `free_chain` needs the pin's
STRUCTURE (which byte belongs to which descriptor word), which is not
recoverable from the map. So the publisher carries it as a pure fact across
the sleep — `ProofVirtioDiskRwD.vdrwd_regions` is written as a CONS of the
avail-ring window onto `vdrwd_pinr_regions` (the twelve descriptor words, the
three `ops[head]` words, and a write's payload window), and the P4/P5/P6 seams
carry `pin ∖ ring = foldr union ∅ (vdrwd_pinr_regions …)` together with the
list's pairwise disjointness (`pm_ok`).  `pm_union` / `pm_split` are the two
directions of "separately-owned windows ⇄ one `phys_map` of their union".

The window/aliasing facts needed at publish (ring slot `np mod 8` bytes are in
driver hands, distinct from every pinned slot) come from OWNERSHIP, not
arithmetic: rw wrote that ring entry as a plain owned store just before the
publish leaf, so the bytes are in hand, and `dma_own ∗ phys_pointsto` forces
domain disjointness.

## The specs (module shape, per design/spec-modules.md)

- **`virtio_disk_init`** — unchanged from `SpecVirtioDiskInit.v` (raw
  `virtio_frag`, pre-`dev_inv`, all six panics refuted, returns the live
  config + three zeroed pages). A separate `virtio_proto_intro` +
  `disk_res` constructor turns its postcondition + the struct-disk cells into
  the pieces `dev_inv`-allocation and `newlock` need: `ctl` = avail idx bytes
  (zero) + nothing pending, `dma` = that ∪ the used page, `np = nc = nr = 0`.
  Init also MINTS the disk points-to: `ghost_map` from any chosen finite set
  of offsets agreeing with the (untouched) `v_disk`.
- **`free_desc`** — takes `locked γvd cpu_id` + the open `disk_res` BODY in
  pieces (it runs under the caller's critical section, like any helper called
  with a lock held): the desc-entry bytes + ops + status for `i`, the a0 bound
  `i < 8`, wakeup's `procs_inv` plumbing; returns `disk_res` re-closed with
  `free[i] = 1`.
- **`virtio_disk_rw(b, write)`** — the headline spec, roughly:

      { is_lock γvd … disk_res ∗ dev_inv ∗ procs_inv … ∗ sleep/wakeup plumbing ∗
        b->blockno ↦ bno ∗ b->disk ↦ _ ∗ b->data ↦ bs_buf (1024 bytes) ∗
        disk_block bno bs_disk ∗
        ⌜write ≠ 0 → …⌝ }
        virtio_disk_rw(b, write)
      { write = 0 (READ):  b->data ↦ bs_disk ∗ disk_block bno bs_disk
        write ≠ 0 (WRITE): b->data ↦ bs_buf  ∗ disk_block bno bs_buf
        ∗ b->disk ↦ 0 ∗ b->blockno ↦ bno ∗ callee_saved ∗ … }

  Nothing about other requests appears: concurrency is inside `disk_res` +
  `virtio_proto`.
- **`virtio_disk_intr`** — takes `dev_inv` + `is_lock …` + wakeup plumbing;
  acknowledges the ISR (`virtio_ack_clears` gives the line drops), processes
  every completion visible at its used-idx read, wakes each sleeper. Its
  postcondition is about the fabric being re-closed, not about which requests
  completed — the per-request payoff reaches rw through `disk_res`.

## The leaves (WpVirtioDev.v, WpSmodeHalf.v)

1. Width-4 S-mode MMIO leaves for the virtio window, in accessor form over
   `dev_write`/`dev_read` with the ghost-step wand shape of the `_kpt` UART
   leaves: `wp_{lw,sw}_virtio_dinv_s_sconf` open the bare `disk_inv`, and
   `wp_{lw,sw}_virtio_dev_s_sconf` are their `dev_inv`-bundle restatements.
   Every virtio MMIO access in the driver — init, notify, isr-read, ack — goes
   through them; there is no raw-`virtio_frag` leaf. WpPlicExec's width-4 exec
   towers are generic in the device window, so nothing was cloned for this.
2. Invariant-opening S-mode RAM access leaves for LEASED bytes (the avail-idx
   `lhu`/`sh`, the used-idx `lhu`, the used-element `lw`) come from
   `WpSconfMem.wp_{load,store}_s_sconf_au`, the width- and uns-generic
   ATOMIC-UPDATE parents (the WpSconfLock pattern): they open the invariant
   around the one memory step, and the bytes are materialized out of `dma_own`
   (they sit behind `phys_pointsto`; the VA is identity — `mem_ident_phys`)
   with the protocol operation (publish/observe/reclaim) plugged into the
   view-shift slot. Plain width-2 RAM leaves for the descriptor formatting are
   `wp_{lhu,lh,sh}_s_sconf` (WpSmodeHalf.v).

## File map

| file | contents | depends on |
| --- | --- | --- |
| `VirtioQueue.v` (iris-free) | wrap16, slot geometry, `vslot`, `slot_pin_ok`, `vproto_ok`, flat-derivation, publish/step/reclaim surgery, step determinism | VirtioModel |
| `DiskPtsto.v` | `γdk` ghost, `disk_byte/bytes/block`, `disk_view`, mint/agree/update | RiscvPtsto |
| `VirtioProto.v` | `disk_names`/`diskGhostG`, `virtio_proto`, the four protocol view shifts, `virtio_proto_intro/init/stable` | WpVirtio, VirtioQueue, DiskPtsto |
| `WpVirtio.v` | the base (`dma_own` etc.); the unkeyed `virtio_lease` survives here, used by nothing | — |
| `WpUart.v` | the device invariants; `disk_inv_body` carries `virtio_proto`; `wp_dev_loop`'s disk case runs on `virtio_proto_step`/`_not_stalled` | VirtioProto |
| `RiscvAdequacy.v` | allocates `disk_names` and the initial `virtio_proto` | VirtioProto |
| `WpVirtioDev.v` | the MMIO leaves above | WpPlic(Exec), VirtioProto |
| `DiskInv.v` | `struct disk` geometry, `disk_res`, its open/close/alloc lemmas | VirtioProto, WpLock, ProcGeom |
| `SpecFreeDesc/SpecVirtioDiskRw/SpecVirtioDiskIntr.v` + Proof/Link | the functions | the above |

## Why the alternatives were rejected

- *Fractional ctl shared with the lock* (½ in lease, ½ in `disk_res`): makes
  every desc write need both halves anyway, and turns `dma_update` fiddly.
  Moving whole bytes at publish/reclaim keeps full-ownership invariants and
  makes the free-descriptor writes invariant-free.
- *One flat S-set protocol (extending `virtio_queue_ok` in place)*: reclaim
  (shrinking the lease per-slot) and per-slot resources need KEYED state; the
  flat form survives as a derived view so the proven device-thread rules keep
  their shape.
- *Ghost-mirroring `disk_res` state into the proto* (auth/frag of an abstract
  driver state): unnecessary — the receipts (`γslot` fragments) plus byte
  ownership carry every cross-invariant fact needed; fewer ghosts, no
  agreement lemmas.
- *Sector-granularity disk points-to*: byte granularity with a `disk_block`
  derived form costs nothing extra (the auth is a `ghost_map Z (bv 8)`) and
  matches `disk_read`/`disk_write`, which are byte-addressed.
