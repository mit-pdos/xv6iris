# M5 — the disk as a weak-memory AGENT (design)

**Status (2026-08-17): DESIGN, decided by the orchestrator; supersedes the
"disk DMA gets a view / notify-carries-view" sketch of
[`weak-memory.md`](weak-memory.md) Decision 6 and the "fabric view" sketch
in the first draft of
[`../projects/weak-memory-soundness.md`](../projects/weak-memory-soundness.md).
Read that worklist for why M5 is on the critical path of the soundness
capstone (the flat DMA read is refuted as a Layer-1 instance AND is stronger
than hardware).**

## The idea in one sentence

The virtio device is a small PROGRAM: it acquire-loads the available-ring
index, plain-loads the ring entry / descriptors / header / data buffer at the
view it acquired, stores the completion (data, status, used element), FENCES,
stores the used index — one event per node, at the disk agent's OWN
`wstate`, using exactly the labels a hart uses (`LLoad`/`LStore`/`LFence`)
plus fabric-marked silent steps for reading/writing its own MMIO-visible
state.  The synchronization between driver and device is MESSAGE PASSING
THROUGH THE RINGS, which is what the virtio specification's memory-barrier
requirements say it is; the QUEUE_NOTIFY doorbell and the ISR are HINTS
(fabric events that carry no view).  Consequently:

- **No fabric view, no new Layer-1 label with a view effect, no replay
  change.**  Layer 1 needs exactly ONE addition, the fabric-touching silent
  label `LDev` (below), which it needs anyway for the PLIC wire.
- **The FENCE I/O-bit question becomes moot for safety.**  The ordering the
  driver relies on is `desc writes ; fence rw,rw ; avail->idx write` (a
  MEMORY fence, which the Sail model executes faithfully) and `used->idx
  read ; fence rw,rw ; used elem read`.  The doorbell's ordering only affects
  WHEN the device wakes up, and the model lets the device poll — a superset
  of a notify-driven device (see "assumptions").
- **The disk's reads are ordinary view-based reads**, so the pf machine's
  disk arms are `PFLoad`/`PFStore`/`PFFence`/`PFSilent(LDev)` and the ⇒
  direction of the instance holds for the disk exactly as for a hart.  The
  flat memory `wflat` disappears from the language.

## The device program

A read/write/fence monad, in `VirtioModel.v` (Iris-free), SC tree untouched:

```coq
Inductive DM (A : Type) :=
  | DRet   (a : A)
  | DRead  (pa : Arch.pa) (n : nat) (aq : bool) (k : list (bv 8) → DM A)
  | DWrite (pa : Arch.pa) (bs : list (bv 8)) (k : DM A)
  | DFence (k : DM A).                     (* fence rw,rw *)

Inductive dres :=
  | DDone (δ : virtio_state → virtio_state)   (* commit: applied to the CURRENT fabric state *)
  | DWild                                     (* malformed chain: the model's "anything" arm *)
  | DIdle.                                    (* nothing pending *)

Definition virtio_prog (v : virtio_state) : DM dres :=
  if ¬ virtio_live (v_cfg v) then DRet DIdle else
  DRead (avail idx, 2 bytes, aq := true) (fun idx =>
  if idx = v_seen v then DRet DIdle else
  DRead (avail ring slot (v_seen v)) … (fun h =>
  DRead (desc h) … DRead (desc next) … DRead (desc next2) …   (* chain_at, node by node *)
  (malformed ⇒ DRet DWild)
  DRead (header: type, sector) … (fun …
  match type with
  | IN  => DWrite (buf, disk_read …) (DWrite (status, ok) (DWrite (used elem) (DFence (DWrite (used idx) (DRet (DDone δ_in))))))
  | OUT => DRead (buf, len, plain) (fun data => DWrite (status, ok) (DWrite (used elem) (DFence (DWrite (used idx) (DRet (DDone (δ_out data)))))))
  | _   => DWrite (status, unsupp) (DWrite (used elem) (DFence (DWrite (used idx) (DRet (DDone δ_unsupp)))))
  end …)))).
```
`δ` bumps `v_seen`/`v_used_idx`, ORs the ISR used-buffer bit, and (OUT) writes
the disk image; it does NOT overwrite the configuration — a hart's MMIO
writes during the burst are not clobbered.  `avail_idx_at`/`avail_ring_at`/
`desc_at`/`chain_at`/`req_at` keep their `vmem` forms for the SC tree, and
ONE lemma pins the two together: running `virtio_prog v` with every read
answered from a flat `mv` and the writes collected yields exactly
`virtio_req_step v mv` (`Some (δ v, writes)`), `None`+`DWild` exactly when
`virtio_stalled v mv`, and `DIdle` exactly when not pending.

## The language (`WeakEvLang`)

`EDisk gen (dp : option (DM dres)) (dws : wstate)`.  Arms of the disk
thread (all under `ethread_live`):
- **start** (`dp = None`): read the fabric's virtio state `v := dvirtio (wgdev σ)`, `dp' := Some (virtio_prog v)`.  Fabric-touching, log/ws-free: label `LDev`.
- **`DRead pa n aq k`**: EXACTLY the hart's plain RAM-read arm at `dws` (`read_ok … dws aq false …`, `dws' := load_post_run dws aq …`, continuation `k` gets the bytes).  Label `LLoad aq false`.
- **`DWrite pa bs k`**: EXACTLY the hart's RAM-write arm at `dws`, tid `Some n_disk`, class `wm_class_of plain dws` (= `WCplain`/`WCrel` per `w_relp`).  Label `LStore`.
- **`DFence k`**: `dws' := fence_post dws true true true true`.  Label `LFence`.
- **`DRet (DDone δ)`**: commit: `wgdev' := set_dvirtio (wgdev σ) (δ (dvirtio (wgdev σ)))`, `dp' := None`.  Label `LDev`.
- **`DRet DWild`**: the retained "anything" arm: `dp' := None` and the disk may then emit ARBITRARY messages — model this as `dp' := Some (arbitrary DWrite chain)` chosen at this step (`∃ prog', prog' is a chain of DWrites ending in DRet DIdle`), so the emits are still ordinary store events.  Label `LDev` (it reads nothing; mark it fabric-free if simpler — decide at build time, record).
- **`DRet DIdle`**: `dp' := None`, silent (`LSilent`).
- **latch** (`WDiskStepLatch`, PLIC latch of the virtio irq level): unchanged, at any time, label `LDev`.
- The UART thread and PLIC thread: unchanged (labels `LDev`).

`wflat`, `wdisk_step`, `wmsgs_of_map`, `pend`, `epend_canon` leave the event language (they stay in `WeakLang.v` for the archived instruction-atomic tier).

## The instance (`WeakEvInst`)

`pstep_disk (PDisk dp) d l (PDisk dp') d'` = the program half of each arm
above (fabric moves at start/commit/latch, monad advance everywhere else),
`pcls_ev (PDisk _) (LStore …) ws := wm_class_of plain ws`; `pdev_ev _ l _ :=
(l = LDev)`.  The ⇒ direction now holds for every disk arm because every
memory-reading arm reads through the label.

## The label `LDev` (Layer 1, the only change)

`WeakPromise.wlabel` gains `LDev`: a silent-EFFECT label (no log, no view
change; `PFSilent`/`WPSilent` twins) whose only role is to be the
fabric-touching marker `pdev` can decide on.  Every `match` on `wlabel` in
Layer 1 gets the `LDev` case ≅ `LSilent`.  Needed because the PLIC wire is
a step of the TARGET hart's agent that reads the fabric, and "this silent
step read the fabric" is not decidable from `(p, LSilent, p')`.

**LANDED (2026-08-17).**  `LDev` is the LAST constructor of `wlabel`, and
each machine got a SEPARATE arm rather than a predicate `lb_silent l` over
a generalized silent arm: `WeakPromise.WPDev` and
`WeakPromiseBridge.PFDev`, both byte-identical twins of the silent arm
(same configuration update, no side condition).  The reason, recorded in
`WeakPromise.v`'s header: the predicate form changes the shape of an arm
that ~30 downstream proofs invert with an explicit intro pattern and that
~15 sites apply as a constructor, and — the real cost — it turns the
silent arm's label into a VARIABLE, so every downstream computation that
reduces `post_ws`/`aev_post`/`astep_ok`/`lat_free` at the concrete
`LSilent` would need a case split.  With a separate arm placed LAST,
every existing pattern and application stays valid verbatim and the cost
is exactly "+1 branch in the pattern, +1 bullet copying the silent one".
Files touched: `WeakPromise`, `WeakPromiseFact` (`astep_ok`, `wpstep_split`),
`WeakPromiseBridge` (`PFDev`, `proj_lbl`), `WeakRobustTrace`,
`WeakRobustGraph`, `WeakRobustAcyc`, `WeakRobustSer`, `WeakRobustProv`
(`aev_post`, `laev_post`), `WeakRobustSim`, `WeakRobustCone`,
`WeakRobustBlocks`, `WeakRobustMain`, `WeakRetag`, `WeakSailLTS2`,
`WeakSailComplete` (`post_ws`), `WeakSailCone`, `WeakCompose`,
`WeakComposeLang`, `WeakEvPf` (`elabel_ok`/`edlabel_ok`), `WeakEvInst`
(`elab_ok`/`elab_ws`/`edlab_ok`/`edlab_ws`).  Two deliberate NON-changes:
`lbl_quiet` does NOT list `LDev` (a quiet label is one that may be
commuted past another agent's step, and two fabric-touching steps are
exactly what must not commute — `WeakPromiseFact.wp_afree` is the scoped
law), and `WeakSailLTS2` gains `sail_step_ni_not_dev`/`sail_step_not_dev`
so the archive's five-shape inversion lemmas REFUTE the new arm instead of
enumerating it (the archive's `pdev` is constant `false` and its LTS pins
every label to one of the five original constructors).  Nothing in the
fabric machinery (`pdev`, `pdev_ok`, `wp_afree`, `mk_aev`, `qfab`) needed
more than the extra case — all of it is already generic in the label.

## The WP side (NOT on the capstone's path; recorded for the M4 port)

`WeakExec.wp_wdisk_step` (the lifting lemma at the flat memory) is retired
with the flat.  The disk thread gets per-node EWP rules that are the hart
rules' twins at `dws` (`ewp_disk_load`/`_store`/`_fence`, a start/commit
rule over `dev_interp`), and a driver proof shows: the acquire read of
`avail->idx` either returns `v_seen` (idle) or a value whose message the
driver released after its descriptor writes, so the chain reads see valid
descriptors and `DWild` is unreachable.  That proof is what makes the
driver's `__sync_synchronize()` sites load-bearing.

## Assumptions this model makes about the device (record in the final ledger)

1. The device reads the available index with ACQUIRE ordering relative to
   its subsequent ring/descriptor/buffer reads (the virtio spec's device-side
   read barrier).
2. The device's completion writes are ordered before its used-index write
   (the `DFence`; the spec's device-side write barrier).
3. The device may process a published request at any time (polling);
   QUEUE_NOTIFY and the ISR are hints.  This is a SUPERSET of a
   notify-driven device, and it is what makes the doorbell's I/O-fence
   ordering irrelevant to safety (a missing `fence w,o` before NOTIFY could
   only delay processing).
4. Unchanged: a malformed chain lets the device write anything anywhere
   (`DWild`), so the driver must prove chains are well formed.
5. Unchanged from Decision 6: no icache; MMIO registers are fabric state.
