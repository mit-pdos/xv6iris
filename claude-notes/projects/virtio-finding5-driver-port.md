# Project: finding 5 in the Iris driver — the completion order reaches the proofs

## STATUS (2026-08-25)

Branch `virtio-finding5`, 32 commits, **nothing pushed**, zero admits
throughout. The model side and `vtest-rocq` landed earlier (see
[`device-conformance.md`](device-conformance.md) §"Finding 5"); this file is
the **Iris driver port**, which is what is left.

`make -C iris -f CoqMakefile -j192 -k` is green except **three files**:

    ProofVirtioDiskIntr.vo    the interrupt handler   -- BLOCKED, design below
    ProofVirtioDiskRw.vo      mechanical signature drift
    ProofVirtioDiskRwD.vo     mechanical, but it is the publish site

Everything else — `VirtioModel`, `VirtioQueue`, `VirtioProto`, `DiskInv`,
`DiskBoot`, `BootCarveMain`, `BootShared`, `BootChain`, `SpecMain`,
`ProofMain`, `ProofVirtioDiskInit`, `RwB`/`RwC`/`RwE`/`RwF`, the whole fs and
user stack — is green.

**Build from the repo root, and pass `-j192`:**

    cd /shared/xv6iris-2
    ./gcp-rocq/run-on-gcp opam exec --switch=/shared/xv6rocq -- \
      make -C iris -f CoqMakefile -j192 -k

Running it from `iris/` gives `EXIT=127`; running it without `-j192` turns a
four-minute sweep into forty. `durable-notes.md:83` has the rule (pick `-j` by
RAM, `RAM_GB/2 = 354` here, so the 192 cores bind).

---

## THE SHAPE OF THE FIX

QEMU completes requests in **any** order, so three numbers that used to
coincide no longer do:

    position     where in the available ring a request was published; counts
                 forever; the protocol's key (vp_slots, vp_pin, vp_pend, ...)
    used index   how many completions have happened; what disk.used_idx and
                 the handler's watermark walk
    head         the first descriptor of a chain, < 8; what disk.info[] is
                 indexed by and what the used ring REPORTS

The old `DiskInv.disk_res` kept a per-request map keyed by **position**
(`flight_res`/`parked_res` with `dom fl = set_seq nr (np-nr)`), and the
handler reads a **head**. That interval clause is false once completion is
out of order, and nothing tied the lock resource's domain to the invariant's.

**The resolution is ownership transfer, not counting** (Nickolai's framing,
and the standing rule — see the `prefer-ownership-over-counting` memory):
publish hands the device the whole descriptor chain, the used ring hands it
back, and a per-descriptor **receipt** keyed by head records where it is.

    Xv6Cameras.hstate := HInactive | HActive (v : dclaim)
    dclaim = { dc_buf; dc_slot; dc_pin; dc_pos }
    disk_names gains dn_head : gname   (ghost_map nat hstate)

`VirtioProto.head_res γ i st` is the receipt's content:

    HInactive  emp
    HActive v  ⌜head (dc_slot v) = i⌝ ∗ d_info_b i ↦₈ dc_buf v ∗
               (  b_disk (dc_buf v) ↦₄ 1 ∗ disk_receipt γ (dc_pos v) ...
                ∨ b_disk (dc_buf v) ↦₄ 0 ∗ chain_back γ (dc_slot v) (dc_pin v) )

`heads_res_at γ (vp_spins pr)` holds the authority, totality over the eight
descriptors, and the **coupling**: every live `(position ↦ slot,pin)` has its
head ACTIVE with matching fields. `flight_res`, `parked_res`, `disk_claim`
and the `dn_claim` map are all **gone**; `dn_claim` survives only as an
unused field in `disk_names`.

Freshness facts that used to need counting are now points-to conflicts: two
live requests cannot share a head, because the entry would own `d_info_b`
twice; a chain cannot already be back, because that arm owns `dc_pin`, which
is in the DMA lease.

### The accessors, and which instruction each one is

| accessor | instruction |
|---|---|
| `virtio_proto_ring_acc` | `avail->ring[idx % NUM] = id` |
| `virtio_proto_publish_acc` | `avail->idx += 1` — INACTIVE → ACTIVE |
| `virtio_proto_poll_acc` | `while (b->disk == 1)`, **and the collect** |
| `virtio_proto_ord_at` | gives `∃ p, disk_ord γ p u` from `done_lb (S u)` |
| `virtio_proto_used_peek_at` | `id = used->ring[used_idx % NUM].id` |
| `virtio_proto_status_peek` | `if (info[id].status != 0) panic` |
| `virtio_proto_infob_acc` | `b = info[id].b` |
| `virtio_proto_deposit_acc` | `b->disk = 0` — reclaim AND deposit, one step |

---

## THINGS DISCOVERED THAT THE NEXT AGENT MUST NOT RE-LITIGATE

### 1. `disk.info[i].b` is driver-private. It stays driver-side.

I first put that cell inside the device invariant in every receipt state.
**That is wrong and it cost a day.** Unlike `info[i].status`, which `desc[t]`
points at and the device writes, `info[i].b` is named by **no descriptor** —
the device cannot touch it. Putting it in the invariant forced the
`disk.info[idx[0]].b = b` store in `virtio_disk_rw` to open the invariant,
which broke `ProofVirtioDiskRwC`'s free-slot destructure and forced eight
`d_info_b` cells through the whole boot chain.

It now rides in `free_slot_res` / `disk_slot_raw` / `vdrw_slot_rest` with the
rest of the free slot, and transfers into the receipt **only for the
in-flight window** — the one stretch where its reader (the handler, which
learns the head from the used ring) is not the thread that allocated it.
Reverting this made `ProofVirtioDiskRwC` and `ProofVirtioDiskInit` compile
**untouched**, deleted `HStaged`, deleted `virtio_proto_info_acc`, and made
`head_res HInactive = emp` (so the live flip needs no resources at all).

Rule: transfer a cell into the invariant at the point the **code** transfers
it, not for the whole lifetime of the slot.

### 2. `virtio_proto_collect_acc` was VACUOUS — check new accessors for this

It demanded the caller own `b_disk ↦₄ 0`, but `poll_acc` only *lends* that
cell back and the ACTIVE came-back arm owns it too. The premises were jointly
contradictory: the lemma was provable (by `exfalso` off the conflict) and
could never be applied at a call site. Deleted.

The poll now decides on the **value it reads**: read 1 and the receipt goes
back untouched; read 0 and that same step *is* the collect, handing the
caller `chain_back`, `d_info_b` and `b_disk`. A separate collect accessor is
not expressible — the loop only ever learns the value 0, never the cell.

**General lesson:** an accessor that takes a full points-to the invariant
also owns is vacuous. When writing one, ask whether the caller can ever
actually hold the premise, not just whether the lemma typechecks.

### 3. THE OPEN PROBLEM: the handler's four invariant openings

This is what blocks `ProofVirtioDiskIntr`, and it is a genuine design
problem, not a proof-engineering one.

`virtio_disk_intr` touches the invariant four times, and each touch must
*own* something at an address it computes from a register:

| # | instruction | must own | learns |
|---|---|---|---|
| 1 | `id = used->ring[used_idx % NUM].id` | 4 bytes at `used_elem_pa c u` | `h` |
| 2 | `if (info[id].status != 0)` | byte at `d_info_status h` | status |
| 3 | `b = info[id].b` | `d_info_b h` | `b` |
| 4 | `b->disk = 0` | `b_disk b` | — |

An invariant cannot lend a resource across a close, so between openings the
handler carries only **pure values**. Each opening independently re-derives
*which claim* it is about, and nothing makes them agree.

**If the accessors key on the head `h`** (looking up `hs !! h`) rather than
on the position, most of the connective tissue is free: `head_res`'s ACTIVE
arm already carries `⌜head (dc_slot v) = i⌝`, so at `i = h` the status
address falls out of `slot_pin_ok` as `d_info_status h`, and opening 3's
address is `d_info_b h` by construction. `dc_slot` and `dc_pin` never need to
cross a boundary — opening 4 re-derives both from `vp_slots`/`vp_pin` at `p`,
and the coupling makes them agree with the entry's claim *within* that
opening.

**Exactly two facts must survive a close:**

- **F1** `hs !! h = Some (HActive _)` — that the head read at 1 names a live,
  completed chain. Needed by 2, 3, 4.
- **F2** `dc_buf dc = b` — that the entry still names the buffer read at 3.
  Needed by 4.

So the carrier is **two numbers** — a descriptor index and a buffer address —
per position. NOT a whole `dclaim`: no `vslot` and no byte-map need to be
snapshotted. (I proposed the heavier version first; it is unnecessary.)

**Why it must be immutable rather than re-derived.** F1 and F2 hold across
the openings only because the entry cannot be retired while the handler
works: retirement needs the collect, the collect needs `b->disk = 0`, and
that needs a deposit, which needs the watermark `disk_read_at γ u` the
handler holds exclusively. That is a **rely-guarantee argument about what
other threads cannot do**, and Iris will not make it across an invariant
close. Recording `(h, b)` at publish — where they are chosen and never change
again — converts it into an ownership fact and the temporal reasoning
disappears.

### 4. Three ways to avoid new ghost state that DO NOT WORK

Do not spend time on these again; each was tried and failed for a specific
reason.

**(a) Pin via `slot_pin_ok`.** The pure fact the openings already return does
not determine the slot — two different slots satisfy it at the same position.

**(b) Pin via the receipt** (hand `disk_receipt` to the handler at the
used-element read, the way the pre-finding-5 code did). Needs a middle
"handler is carrying it" arm in the ACTIVE disjunct, and **that arm cannot be
refuted on re-entry**: nothing stops a second reclaim of the same position,
because the receipt's *absence* from the invariant is not a contradiction.
The old code was safe only because the position-keyed `fl` map made the slot
vanish from `vp_slots` at reclaim. Splitting reclaim from deposit reopens
this; keeping them as one atomic step (which `deposit_acc` does) is what
avoids it, and is why the ACTIVE disjunct has **two** arms and not three.

I prototyped the three-arm version twice and reverted it twice. If you find
yourself adding a third arm, re-read this paragraph first.

**(c) Extending `dn_ord` to carry the slot.** `disk_ord γ p u = p ↪[dn_ord]□ u`
is persistent (discarded fragment) and its auth is `vp_uix pr`. Its value
cannot be widened to include the slot, because the auth would then have to
**shrink at reclaim**, invalidating fragments that were already discarded.
The carrier must be an **insert-only** map for exactly this reason.

**(d) What DOES work, and is already written and compiling in one form.**
`vp_pa_add_base_inj : pa_add a k = pa_add b k -> a = b` (adding a constant is
a bijection mod 2^64; reuse `VirtioQueue.vq_wrap_cancel`, `pa_eq_of_unsigned`,
`pa_add_unsigned`). With `⌜vr_buf (vs_req (dc_slot v)) = pa_add (dc_buf v) 88⌝`
in `head_res` — that is `BufOwn.b_data`, spelled out because `BufOwn.v` is at
`_CoqProject:887`, far below `VirtioProto.v` at `:65` — the buffer is pinned
*given the slot*. It does not solve F1/F2 on its own, because the slot is
precisely what is not pinned, but it is the right clause to have and it
compiled cleanly. It is **not** in the tree right now (reverted with the
three-arm experiment); re-add it with the carrier.

---

## LIKELY NEXT STEPS

1. **Add the `(head, buffer)` carrier.** A persistent, insert-only ghost map
   `nat -> nat * Arch.pa` (position ↦ head, buffer), written at
   `virtio_proto_publish_acc` where both are known and neither ever changes.
   Six contained pieces: camera field in `Xv6Cameras`, `dn_bufat`-style gname
   in `DiskPtsto.disk_names`, a `disk_pubat γ p h b` definition with a
   persistence instance, the auth **plus a big-op of the fragments** inside
   `virtio_proto` (persistent fragments must be handed out, not re-derived
   from the auth — copy how `#Hordm` does it for `dn_ord`), the insert at
   publish, and an `ord_at`-style extractor the handler calls once.
   Then re-key `used_peek_at` / `status_peek` / `infob_acc` / `deposit_acc`
   on it. `heads_res_at_mono` and the device-thread steps thread the auth
   unchanged.

2. **Rewrite `ProofVirtioDiskIntr`'s loop.** `disk_res_at` has already been
   updated to mirror the new `disk_res` (four existentials, no `fl`/`pk`);
   `vt_loop_state` and `vt_loop_state_close` follow it. What is left:
   `vt_flight_at_nr` and the `parked_res` construction go away entirely;
   `wp_vt_reclaim` loses its `disk_receipt` premise and its `vt_payoff`
   postcondition (the handler never needs the payload now — it reads three
   values and stores `b->disk = 0`); `wp_vt_status` and `wp_vt_clear_disk`
   become invariant-opening steps using the peeks. `virtio_proto_reclaim_acc`
   no longer exists — the references at `:1006`, `:1218`, `:1224`, `:1359`,
   `:1424` are stale.

   The address-claim pre-opening (`fupd_wp` + `used_peek`) that sits before
   the atomic load exists because the WP leaf wants the claim *beside* the
   atomic update. `wordw_claim_of` yields `wordw_claim width a`, which
   depends only on the ADDRESS, not the value — so that pre-opening does not
   need the claim pinned and can stay read-only.

3. **`ProofVirtioDiskRw.v:684`** — mechanical. `free_cell_res` gained a
   leading `γ` (commit `1cb99cb6`); the `wp_vdrw_scan` family passes `pd`
   where `disk_names` is expected. Thread `γd` through.

4. **`ProofVirtioDiskRwD.v:976`** — the publish site, and the interesting one.
   `virtio_proto_publish_acc` now takes a `dc : dclaim`; the call site still
   passes `sl pin wrb` positionally. It must build
   `{| dc_buf := b; dc_slot := sl; dc_pin := pin; dc_pos := np |}`, discharge
   `dc_slot dc = sl` / `dc_pos dc = np` / `dc_pin dc = pin`, and **hand over
   the two driver-side cells** `d_info_b h ↦₈ b` and `b_disk b ↦₄ 1` that P3
   now leaves in the caller's hands (`vdrw_chain` carries both). This is also
   where the new carrier's `(h, b)` and the `vr_buf = pa_add b 88` clause get
   discharged — `DiskInv.slot_buf_link` is the pure fact that says it, and
   the rw proof already establishes it; **verify it is in scope at the
   publish site** rather than assuming.

5. **vtest.** `vtest-rocq/VSched.v` / `DiskOrder.v` need a pop item, and both
   QEMU completion orders must be re-verified after the driver lands.

6. **Before pushing:** full `-j192` sweep green, `make vtest` green, then fold
   the settled RULES (not this history) into
   [`design/virtio-driver.md`](../design/virtio-driver.md) and shrink
   `device-conformance.md`'s "Finding 5: what is left" section, whose plan
   items 1 and 2 are now stale — `dn_ord` landed, and the flight map they
   describe no longer exists.

---

## GOTCHAS THAT COST TIME HERE

- **`rewrite` in Iris proof mode rewrites the HYPOTHESIS CONTEXT too**, since
  the context is part of the goal term. `rewrite Hdcsl` will silently retype
  your Iris hypotheses — but **not** pure hypotheses already extracted with
  `%`, which live in the Coq context. That asymmetry produced two failures
  where a re-folded `head_res` reverted to `dc_slot dc` form while the
  hypothesis said `sl`.
- **ssreflect vs stdlib `rewrite` is per file.** `VirtioModel.v` and
  `VirtioQueue.v` take commas (`rewrite A, B`); `VirtioProto.v` takes spaces
  (`rewrite A B`). A comma in `VirtioProto.v` gives
  `Syntax error: [ltac_use_default] expected`.
- **`iFrame` matches greedily against the invariant's own row.** Both halves
  of `dn_nr` / `dn_np` / `dn_stage` are in scope inside an accessor, so
  `iFrame "Hpub Hrd"` can frame the invariant's half and then fail elsewhere.
  Use `iSplitR "Hpub Hrd"; [| by iFrame "Hpub Hrd"]` to isolate first.
- **`rewrite {1}/virtio_proto` vs `rewrite /virtio_proto`.** With `{1}` only
  the hypothesis is unfolded and the closing goal stays folded, so a later
  `iExists pr, dma` fails with "not an existential". The peeks that hand the
  invariant back want the unqualified form.
- **`rewrite !phys_word4_map` fails under a binder.** If the goal still has
  `∃ dc, ... phys_word4 ... (dc_slot dc) ...`, rewrite cannot go under it.
  Do `iExists dc` and the slot rewrite first.
- **`lia` can fail on `bv_unsigned` bounds** when the atom does not match
  syntactically. Prefer `rewrite -vq_mod64. apply bv_unsigned_in_range.` over
  posing the range lemma and calling `lia`.
- **`set_seq` in a GOAL causes hour-long hangs** — see the note in
  `durable-notes.md`. Keep it in pure side conditions.
- Run file edits in the **foreground and verify on disk** before launching a
  build. Bundling a Python edit with a build in one backgrounded command hid
  an aborted `assert` twice and burned three build cycles on an unmodified
  file.
- Keep `grep` out of `&&` chains: `grep -c` returning 0 exits nonzero and
  silently skipped a commit that had been reported as done.
- `git commit -F <file>`, not `-m` — quoting in these messages breaks.
