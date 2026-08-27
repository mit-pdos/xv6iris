# The machine flip: SC → Ztso in the kit, and the REAL Σ instantiation

STEP 5, THE SHIM-TAIL TRANCHE (2026-08-27, latest session).  **THE DELETED
SHIM'S TAIL IS MEASURED AND MOSTLY GONE, AND THE PLAIN ARM'S PRICE IS PAID
AT THE S-MODE LEAVES.**  Of the 181 real shim uses, **111 converted
mechanically** and **the 70 survivors are ALL the raw→ctx direction** — one
decision per raw-tower OWNER, five owners, characterised in A6.58's table.
The kit the sweep needed is two lemmas in `ByteBuf`
(`ctx_word_pointsto_split4`/`_join4`, plus `ctx_buf_forget`); the dominant
"↦₄ has not flipped yet" comment at the call sites is STALE — it has.  The
other half of the tranche is A6.36's overruling reaching the S-mode leaves:
a LOAD is the PLAIN arm, so `SmodeCorePt.wordw_win_load_c` (the read twin of
`wordw_win_store_c`, PURE, hence runnable inside an atomic update) is what
pays `Mobl_ram`, and every S-mode memory leaf now threads `own_context`.
FOUR of A6.57's nine red are GREEN (`DiskBoot`, `SwtchCtx`,
`WpSconfSfence`, `WpSmodePtLeaves`) and a fifth (`WpSconfMem`) is ported but
**UNVERIFIED — its compile ran 30 minutes and was terminated, not failed**,
which is this tranche's one real stop and leaves its whole `Proof*` cone
unreached.  `RiscvAdequacy`'s five allocations are LANDED (A6.59) with
`TsoGhost.view_auth_alloc` as the one new lemma, and step 6's remaining bill
is ONE item — the element carve, which changes the adequacy theorem's
CONCLUSION and is therefore its own tranche.  Clean model-aware rebuild
**728 of 1330, up from 663**.  A6.58–A6.60 are the record; **A6.60 is the
handoff**.

STEP 5, THE PIN'S CONSUMER HALF (2026-08-27, latest session).  **THE PIN
IS DONE END TO END, `HartSKpt` IS GREEN, AND `SmodeCorePt`'s A6.18 VERDICT
IS IN** (A6.56: four errors in 4,480 lines, only TWO of them genuine
re-port bugs and both stale rewrite/index directions in the text-tier
lemmas — the re-port's substance is sound).  A6.54's refutation of
pin-memo §5.5 was ratified and then made moot: A6.55's allowed-byte family
reads the LEAF BIT, so interior slots pin to singletons and keep their
EXACT values, `HartSTrans` and `Pt2WalkPt` never move, and §5.5's
conclusion is restored by a different mechanism.  Closing the two deepest
frontier files opened the whole S-mode PT tier: **112 files went green**.
Clean rebuild **663 of 1330, NINE red**, seven of them first-time-reached.
A6.55–A6.57 are the record; **A6.57 is the handoff**, and it names the
largest remaining block — the deleted shim's 240 references across 63
files — and the `RiscvAdequacy` inventory (§7 step 6, the last structural
piece never attempted).

STEP 5, THE A6.52 RULINGS (2026-08-26, earlier session).  Both are
IMPLEMENTED and green: **`PtTree`'s tier index now CARRIES the kernel
tier's canon-pin bound** (`ptier := KTier B | UTier ξ`, option β — the
measured 40-site sweep, and it cost ZERO net red), **`kpt_bound` has its
own era gname**, and with them the A/D write-back's gate
(`ledger_store_win_pin_ok` → `HartMStore.wobl_ram_ledger_pin_ex`) and the
PT read's value-after-view obligation (`fobl_ram_ex`, threaded through
`PtTreeAdue`).  **`HartSKpt` is down to ONE named gate** — its read lane
is still stated over the flat cache, which is A6.36's overruling catching
up with the file — and **the memo's "levels 2/1 verbatim" claim is
REFUTED by measurement** (A6.54).  Clean rebuild **551 of 1330, FOUR
red**.  A6.53–A6.54 are the record; **A6.54 is the handoff**.

STEP 5, THE PIN'S MACHINE HALF (2026-08-26, earlier same session).  **The
canon pin is BUILT AND GREEN from `TsoMemPa` up to `TsoCtx`** — the
element-carried `ts_elem`, the one-conjunct `ts_ok` interp tie, the four
pinned gates (`ledger_pin_mint` / `ledger_read_pin_ok` /
`ledger_read_pin_bytes_ok` / `ledger_store_pin_ok`) and `HartEvents`'
value-after-view rule pair, **with the old plain rule RE-DERIVED and all
eleven call sites unmoved**.  §5.5's one unprobed pure step is green and
lives in `PtAdBits`.  A6.48's four user-memory files are ONE item (the
tier is forced by `HartMemRun.bytes_own`) and are green, as are
`ProofEntry` and `BootCarve`.  Clean rebuild **551 of 1330, FOUR red**.
A6.49–A6.52 are the record; **A6.52 is the handoff**, and it names the
two design questions the pin memo did not answer (where `B` enters
`pt_slot_own`'s `None` arm; `kpt_bound`'s gname) plus the OTHER frontier,
the unstarted user-translation S-payer.

STEP 5, THE UNGATED TRANCHE (2026-08-26, earlier session).  **`WpUart` is
GREEN — A6.28/A6.29's DMA-completion append is PAID** (the lease flips to
`phys_ledger`, `virtio_proto_step` turns inside out, the disk loop runs
`ledger_store_ok` at `disk_agent`), and the A6.27/A6.28 threading is
through: `UserPtTree` (377 dependents), `WpStartNew`, `TransPt` — the last
of which needed TWO payers, one per page-table tier.  `HartSKpt` and its
tier stayed PARKED on the history ruling, untouched.  **A6.48 is the
handoff.**

STEP 5, THE RE-RULING (2026-08-26, same session, earlier).  A6.37(b) is
WITHDRAWN by the owner; **A6.47 rulings 1 and 2 are LANDED and green with
ZERO fallout** — the author export (`ledger_msg_at` / `ledger_vis` /
`ledger_read_vis_ok`, ONE gate for hart 0 and the secondaries) and the
plain arm's receipt mint (the callback hands back a WP parameterised by
`view_lb h tvn`; ten call sites drop it in one line).  **Ruling 3 is
STOPPED on a measured falsity: `kpt_body`'s `⌜t ≤ B⌝` tie is refuted by
the Svadu A/D write-back**, and the honest replacement is a per-address
history fact — now expressible, thanks to ruling 1, but real machinery
that wants its own ruling.  Ruling 4 (`WpUart`) is scoped, not started.
**A6.47 is the handoff.**

STEP 5, THE READ-SIDE TRANCHE (2026-08-26, same session, earlier).  **The
model `.vo` had never been rebuilt after A6.36 reverted its source, so
A6.38's number was measured against the PATCHED machine and is VOID
(A6.39).**
On the real pinned model: the read-side re-port is landed
(`HartMFetch` + `HartPilot`, A6.40), the whole A6.7(B) revert tail is
absorbed, A6.42's `ledger_read_ok` kit is in `TsoCtx`, `↦ₓ` now carries
its own timestamp-0 element so kernel TEXT pays the plain arm with no
change above the fetch leaves (A6.43), and the PT-read lane is threaded
(A6.44).  **A6.37's ratified `sfence.vma` drain has NO NODE in this model
and is a STOP (A6.41)**; the kernel-PT DISCHARGE point is located and is
the one design gate left in that lane (A6.45).  **A6.46 is the handoff.**

STEP 5, THE OVERRULING TRANCHE (2026-08-26, earlier session).  RULING 1's
overruling is IMPLEMENTED at the machine and the leaves (A6.36), the Sail
patch is reverted and parked, the kernel-PT read story is characterised
with one route measured dead (A6.37), and the store-side tranche that was
in flight is landed (A6.38).  Clean build: **244 of 1330, THREE red** —
read A6.38's number paragraph before reading that as a regression.
**A6.38 is the handoff.**

STEP 5, THE RATIFIED TRANCHE (2026-08-26, earlier same day).  A6.30's rule
is RATIFIED and implemented: **the A/D write-back is PAID**, at
`HartSKpt`'s `wpte_obl_at` seam, and `HartSKpt` is GREEN along with
`SRegime`/`IntrDefs` (the exec lane threaded) and `KstackOwn`.  The A6.18
acceptance compile is STILL not reached — A6.33 is the verdict and names
the blocker, which is A6.18's own predicted store half.  Clean build:
**550 of 1330, EIGHT red** (up from 513).  A6.32–A6.35 are the record;
**A6.35 is the frontier**.

STEP 5, THE A6.26 TRANCHE (2026-08-26, earlier session).  A6.24 IS LANDED
(`KptTree` + both callers), A6.17's cascade is landed at its leaves
(`StackOwn`/`WpMmodeLoad`/`WpTimerinit`), and `WpUart`'s plumbing is
A6.11-shaped with ONE open goal.  Clean build: **513 of 1330, EIGHT red**.
A6.27–A6.31 are the record; **A6.31 is the frontier**, A6.29 and A6.30 are
the two reported stops, and A6.30 is the one to read first — it measures
that the A6.24 payer has no payee anywhere above it and names the lane
(`HartSKpt`'s `wpte_obl_at` seam) where the A/D write-back is actually
payable.

STATUS (2026-08-26, end of session): design of record, AND steps 1–4 of
§7 are IMPLEMENTED and compiling — `TsoMemPa.v` (new), `TsoGhost.v`
(new), the Ztso arms in `RiscvLang.v`, the era ghosts + `tso_interp_at`
in `RiscvPtsto.v`, and the REAL bodies + law surface + four kit gates in
`TsoCtx.v` (`TsoCtxShim.v` gutted to its one still-true mint).
WHERE THAT WORK LIVES: only the two NEW files (`TsoMemPa.v`,
`TsoGhost.v` — pure additions, green in the SC tree too) are on the
branch; the flipped `RiscvLang.v`/`RiscvPtsto.v`/`TsoCtx.v`/
`TsoCtxShim.v` live in the FLIP WORKSPACE, a full tree copy at
`/tmp/claude-0/-shared-xv6iris-3/861bc642-1d31-482b-8fd8-39183ee1abdd/scratchpad/fliptree`
(builds LOCALLY via its own `iris/CoqMakefile`, not on the VM), because
landing them turns the whole lifting tier red — they land as one change
when step 5's tail is worked off.  If that /tmp path has been cleaned,
the four flipped files are re-derivable from this note's §1–§5 against
the twin (`TsoCtxTwin2.v`); copy the workspace somewhere durable before
trusting /tmp.  This is
items (i)+(ii) of tso-port.md §0.10′'s cutover list plus the machine
half of (iii); the lifting/leaf tier (§7 step 5) and adequacy (step 6)
are the standing red tail — see tso-port.md §0.11′ for the exact state.
Items here marked RULING are design decisions of this flip; revisit is
welcome, silence is consent.

STEP 5, ITEM-(iii) TIER (2026-08-26, later session).  TWELVE files went
GREEN across two tranches: `KernelDataInv`, `StackOwn`, `WpLock`,
`DiskInv`, `HartPilot`, then (after the owner's rulings) `WpMmodeLoad`,
`BootCarve`, `PtTreeAdue` and their cascade `HartSTrans`, `WpEntryNew`,
plus the machine files `RiscvLang`/`RiscvExec` re-cut for A6.11.  The
kit grew five additive laws and four gates in `TsoCtx.v`
(`ctx_pointsto_forget` / `ctx_word_pointsto_forget`,
`ctx_pointsto_canonical`, `ctx_ktier_mono` / `ctx_word_ktier_mono`, the
PRISTINE BYTE gate and its two image mints), `ctx_pointsto`'s clean arm
became `llb`-shaped so an image byte needs no per-context ghost step, and
`HartMFetch` gained the `mread_req8_ttw` twins.  Three lemmas that were
FALSE at TSO were replaced by the true ones (`stack_own_reindex` is now
the `ctx_dom` transport; `lk_cpu_cell_acc` is gone; `disk_step` yields its
write set).  A6.8–A6.14 below are the record; A6.13 is the standing
frontier and A6.14 the one tranche that remains.

THE A6.14 TRANCHE (2026-08-26, next session).  `ctx_store_ok` IS PORTED,
and porting it turned up the piece the plan had not named: **all five
members are PHYSICAL and the flip had only built the VA tower**.  So
`TsoCtx.v` gained `ctx_phys_pointsto` (the ledger byte at a physical
address, sealed) plus its 8-byte tower, the store gate in three forms
(map / window / submap), the physical load gate, and the `⊣⊢` that makes
the VA family the kmap claim over the physical one.  On that kit
**`KptTree`, `WpMmodeStore` and `HartMemRun` went GREEN** — the PT-slot
out-and-back is an ISOMORPHISM (A6.9's "cannot come back" was about
leaving the ledger, and the round trip never has to), and the whole user
tier's walker now runs on a ledger map.  `HartSMem` is a reported Σ-SEAM
STOP (A6.18) and `WpUart` is still A6.9's.  A6.16–A6.19 are the record;
A6.19 is the frontier, and explains why the green count went DOWN.

M1 STAGE 2 (2026-08-26, same session, next wave): `↦₂`/`↦₄` are FLIPPED —
the ctx towers are in `TsoCtx.v`, the notations re-declared, and the
fallout absorbed in 14 error-driven rounds.  `PageFields` and `ByteBuf`
went green with their shim crossings DELETED rather than converted, which
is the whole point of a stage.  `↦ₛ` was assessed and DELIBERATELY NOT
flipped (it would put a real ξ inside `is_lock` and buy nothing — A6.15
has the argument).  The red set is down to FIVE, all A6.14/A6.9.

## 0. The one-paragraph shape

The machine keeps `gmem` — re-read as the FLAT memory, i.e. the log
top — and gains the log and the views beside it.  Every consumer of
"memory now" (exclusive/AMO reads, ifetch, page walks, DMA, reservation
snapshots, boot, the power arms, `gen_heap_interp`) keeps its exact
shape; the ONLY arm whose text changes meaning is the plain explicit
data load, which advances the hart's view nondeterministically and
reads latest-visible from the log.  `ctx_pointsto` becomes
mem_pointsto's body plus a timestamp plus the twin's clean/dirty bit;
`own_context` becomes the twin's bundle at the ambient hart — the
running token IS the tie between the CPU's view and the context.

## 1. State (`RiscvLang.gstate`)

Three new fields beside `gmem`:

- `gimg : gmap Arch.pa (bv 8)` — the ERA-INITIAL image (timestamp 0).
- `glog : list pwmsg` — the era's global write log; log order IS the
  total store order; timestamp `S i` = slot `i`, `0` = the image.
- `gtv : CPU → nat` — per-hart views: the WHOLE per-hart memory-model
  state (TsoMem.v's shape, at the machine's types).

`gmem` STAYS, as the flat cache.  The step invariant (an `era_interp`
pure conjunct beside `resv_ok`):

    gmem_ok g := g.(gmem) = flat g.(gimg) g.(glog)
    gtv_ok g := ∀ h, g.(gtv) h ≤ length g.(glog)

RULING (message payload): a message carries its byte MAP, not a base +
byte list: `pwmsg := { pm_map : gmap Arch.pa (bv 8); pm_tid : agent }`,
minted by the write arm as `PWMsg (snap_of pa n v) tid` — the same
`write_bytes ∅` snapshot the reservations already use.  Consequence:
`msg_byte m a := pm_map m !! a`, the flat cache is
`flat img log := foldl (λ acc m, pm_map m ∪ acc) img log`, and the
write arm's cache update is the ONE generic lemma
`write_bytes m pa n v = write_bytes ∅ pa n v ∪ m` — no mword wrap
side conditions anywhere, ever.  (A base+list payload re-derives
pa_add/uint arithmetic in every lemma; measured against and rejected.)

Agents: `agent := nat`; `hart_agent c := fin_to_nat c`;
`disk_agent := NCPU` (the disk's DMA writes are authored messages too).

## 2. The arms (`mnode_step`)

- PLAIN EXPLICIT RAM LOAD (ak_excl false, ak_strong false — the one
  changed arm): choose `tv'` with `gtv cpu ≤ tv' ≤ length glog`; every
  byte j reads `tso_read gimg glog (hart_agent cpu) tv' (pa_add pa j)`;
  the hart's view moves to `tv'`.  Never blocked, never reserves
  (unchanged).
- EXCLUSIVE RAM READ: exactly today's arm (oth-blocked self-loop,
  snapshot vs `gmem`) — reading `gmem` IS reading at the top
  (`tso_read_top_flat`) — plus `gtv cpu := length glog`.  This is the
  AMO's "drain, then read memory", and the view-at-top is what mints
  the acquire receipt (`hart_view_lb`) in the lock leaves.
- RAM WRITE (plain and conditional alike): today's arm (oth-blocked;
  clears own reservation; `gmem := write_bytes …`) plus the append
  `glog := glog ++ [PWMsg (snap_of pa n v) (hart_agent cpu)]`.  The
  view: unchanged for a plain store (store buffering — advancing it
  would forbid SB); `:= S (length glog)` when `ak_excl` (the AMO write
  half passes its own append).
- BARRIER b: `fence_drains b = true` (kinds with a W→R edge:
  `rw_rw`, `rw_r`, `w_rw`, `w_r`) sets
  `gtv cpu := max (gtv cpu) (own_pub (hart_agent cpu) glog)` — "my
  buffer drained"; all other kinds (incl. `tso`, `i`) are no-ops:
  Ztso already orders R→R, R→W, W→W.
- MMIO read/write: byte-for-byte today's arms.  No log, no view action
  (ruling 2 below).
- IFETCH and TTW RAM READS: today's arm (read `gmem`), views untouched.
  RULING 1 below.
- Everything else (registers, announces, choose, Ret boundary):
  unchanged; the boundary drops reservations as today and never touches
  the view.
- THE DISK DMA write arm: appends with `pm_tid = disk_agent` beside its
  `gmem` update; DMA reads read `gmem` (ruling 2).
- POWER arms: the era wipe sets `gimg := (the reset memory the arm
  already builds)`, `glog := []`, `gtv := λ_, 0`, `gmem := gimg` —
  crash drops nothing FROM THE LOG (all appended messages are
  published); what dies is RAM itself, per the existing era machinery.

## 3. Rulings

RULING 1 — **OVERRULED BY OWNER (2026-08-26): implicit accesses take
the PLAIN ARM.**  Instruction fetches and translation-table walks go
through the same nondeterministic view advance as plain explicit data
loads — no strong arm, no `ak_strong`, no access-kind classification
at the machine.  The owner's staging argument, recorded verbatim in
spirit: the SC model ALREADY conflates the fetch/translation axes with
the data axis (implicit accesses were perfectly coherent, no separate
icache is modeled, and `sfence.vma`'s modeled role is the TLB flush,
which the proof fully reasons about); TSO-for-everything is strictly
weaker than the SC illusion and is the current goal; the further
weakening to real Zifencei/sfence.vma staleness (a separate icache /
walker-staleness axis with its own fence semantics) is a SECOND,
LATER de-confliction step, deliberately out of scope now.  The
original ruling's text (flat implicit reads — an SC residue for the
implicit axes, argued from RVWMO's explicit-access scope) is kept in
git history and in the A6.7 block; the ISA-scope evidence gathered
for it (RVWMO's "not (yet) formalized" carve-out, Zifencei, the
sfence.vma implicit-read text) is the design basis FOR THE LATER
de-confliction project, not for this port.  Consequences:
- the machine loses the strong RAM-read arm; the plain arm's guard is
  `ak_excl = false` alone;
- THE A6.7(B) SAIL PATCH IS PARKED, NOT ADOPTED: the model needs no
  access-kind distinction while all non-exclusive reads take one arm.
  The patch, its idempotence measurement and its fallout map stay
  recorded in the A6.7 block and in the backup
  (`/shared/xv6iris-3-fliptree-backup/sail-riscv`, commit 00046a7) as
  the ready-made prerequisite for the de-confliction project — which
  WILL need the model to tell the access classes apart;
- kernel TEXT discharges its plain-load obligations via the
  pristine/timestamp-0 tier (era-image bytes are visible at every
  view).  KERNEL-PT MAPPINGS ARE NOT PRISTINE — owner correction
  2026-08-26: `kvminit()` builds them with ordinary stores at WP time,
  so they are t > 0 and the pristine tier never applies.  Their read
  story is MESSAGE-PASSING: hart 0 writes the PT (log ≤ B) then the
  `started` flag (position F > B); a secondary reading `started = 1`
  on the plain arm has necessarily advanced its view past F ≥ B (the
  MP litmus shape Ztso forbids going stale on), and the flag-read
  leaf mints the persistent receipt `view_lb h F`; every later walk
  on that hart discharges from the inv-opened slot fact (value +
  ⌜timestamp ≤ B⌝ + stable-modulo-A/D) ∗ the receipt.  Hart 0's own
  walks are store forwarding, no receipt.  Own-hart PT writes via
  forwarding; cross-hart handoffs via the lock acquires the proofs
  already pass through;
- THE ONE GENUINELY NEW OBLIGATION: kernel-PTE low bytes are racy at
  runtime (the Svadu A/D write-back mutates bits 6–7 from any hart),
  so a walk at a nondeterministic view may see either value — walk
  certificates weaken from "reads exactly w" to "reads w modulo A/D
  bits"; the write-back path itself stays deterministic (the fork's
  atomic update reads EXCLUSIVE, at the top).  A6.20's "licenses no
  plain load" justification for the kernel-PT `phys_ledger` tier dies
  with the old ruling — the kernel-PT slots need a read story
  (boot-published receipt + stable-modulo-A/D), a design item for the
  implementing lane.

RULING 2 (MMIO and DMA strongly ordered) — already ratified in
tso-port.md §1: device transactions are direct; the disk reads/writes
flat memory.  A driver's RAM-visibility of DMA'd bytes still travels
through Σ (the virtio protocol's `ctx_dom` handoff), not through MMIO
side effects.

RULING 3 (run/exec stay flat).  The whole-instruction interpreter
`run` (and `exec`) keep reading `s.(mem)`: a run is the "hart pinned at
the top view" special case (`tso_read_top_flat`), which is exactly the
device-conformance tester's and the boot bracket's situation.  The
solo-block bracket in RiscvExec.v is re-proven under the premise that
makes it true at TSO: the run touches no RAM data loads, OR every log
message is the hart's own (the solo boot era) — whichever the proof
actually needs; discovered error-driven.

RULING 4 (reservations unchanged).  Snapshots are against `gmem`;
exclusive reads read at the top, so `resv_ok` keeps exactly today's
meaning and the conditional-write atomicity story is untouched.

## 4. The ghosts (per-era, in `riscvEraGS`)

    era_ts_name     : gname   ghost_map Arch.pa nat — per-byte
                              timestamp of the LATEST write; the
                              fragment rides INSIDE ctx_pointsto at the
                              fact's own dq, beside gen_heap's byte.
    era_logm_name   : gname   ghost_map nat pwmsg — log entries,
                              PERSISTED at append (append-only ⇒ stable);
                              the dirty author-tie rides on these.
    era_loglen_name : gname   mono_nat = length glog (persistent llb).
    era_view_name   : gname   auth (agent -d> max_natUR) — hart views
                              (persistent view_lb frags); the disk agent
                              pinned to the top.

`era_interp` gains their auths plus the pure ties
(`TM !! a = Some t → latest gimg glog a t (the gen_heap byte)`,
`LM !! i = glog !! i`, `gmem_ok`, `gtv_ok`).  gen_heap itself is
UNCHANGED and still interprets `gmem` — `pointsto` keeps meaning "the
flat byte", which is what keeps `↦ₚ`, `↦ₓ`, the walker, the devices and
the boot carve intact.

## 5. The real Σ bodies (`TsoCtx.v`, replacing the sealed `_def`s)

`CtxId` unchanged (bound gname : mono_nat; dirty gname :
ghost_map (nat * Arch.pa) unit).  The bodies, each the TsoCtxTwin2
definition wired to the machine's ghosts:

- `ctx_pointsto ξ a dq v` := mem_pointsto's body ∗ the timestamp ∗ the
  bit:

      ∃ ppn t, kmap_at (svpn_of a) ppn KP_rw ∗ ⌜canonical⌝ ∗
        ⌜addr_is_ram (pa_of ppn a)⌝ ∗ ⌜ktier_pin kt ppn a⌝ ∗
        pointsto (pa_of ppn a) dq v ∗
        (pa_of ppn a) ↪[era_ts_name]{dq} t ∗
        (mono_nat_lb_own (ctx_bound_name ξ) t          (* CLEAN *)
         ∨ (t, pa_of ppn a) ↪[ctx_dirty_name ξ]{dq} ())  (* DIRTY *)

- `own_context {CID} ξ` := the twin's running bundle AT THE AMBIENT
  HART — THE TIE, stated once:

      ∃ B K W D, ctx_at ξ 1 B D ∗
        view_lb (hart_agent cpu_id) K ∗ ⌜B ≤ K⌝ ∗
        llb W ∗ ⌜∀ k ∈ dom D, k.1 ≤ W⌝ ∗
        [∗ map] k ↦ _ ∈ D, dirty_ok (hart_agent cpu_id) B k

  ("this hart's view has passed K ≥ my bound, so every clean fact of
  mine is visible here; every dirty fact is mine-on-this-hart or under
  the bound.")

- `hart_view_lb {CID} K` := `view_lb (hart_agent cpu_id) K` (persistent,
  monotone; minted at the AMO-at-the-top leaves).
- `ctx_parked ξ T`, `ctx_dom ξ ξ'` := the twin's, verbatim.

Law surface: every exported law's proof is its named twin lemma with
the mem_pointsto plumbing (kmap_at persistent, pure conjuncts) riding
along.  The lifecycle laws (`ctx_parked_alloc`, `own_context_boot`,
`ctx_park`, `ctx_resume`, `ctx_exchange`, `ctx_deposit`) are
`twin_parked_alloc`/`twin_run_alloc`/`twin_park`/`twin_resume`/
`twin_exchange`/`twin_deposit`.  `TsoCtxShim`'s three FALSE-at-TSO
stopgaps (`own_context_alloc` conjures a bundle at bound 0 — still
sound; `hart_view_lb_any`, `ctx_dom_sc` — now unprovable) become the
honest M2/lock-kit worklists, as always planned.

## 6. The leaf seam (the (iii) worklist, next after this file's steps)

`mnode_step` widens: the hart-local step becomes
`(oth, img, s, log, tv, r) → (m', s', log', tv', r')` — mstate itself
is UNTOUCHED (run/exec ecology, `mem_bytes_at`, `set_reg` chains all
stable).  The lifting hands leaves `mstate_interp σ` plus the
memory-model interp bundle; the σ-callback obligation shapes split:

- `Mobl_ram` (strong: ifetch/ttw/exclusive) — today's flat shape;
- `Mobl_ram_plain` — the callback must prove
  `∀ tv', tv ≤ tv' → tso_read img log h tv' (pa_add pa j) = nth_byte`,
  which is EXACTLY `twin_load_ok`'s conclusion from
  `ctx_pointsto + own_context`;
- `Wobl_ram` — flat update + the append's four ghost steps (γts to the
  new top, γlogm persist, mono_nat bump, dirty-set insert), i.e.
  `twin_store_ok`;
- Barrier/AMO leaves mint `hart_view_lb` (`twin_passed_get`) — the M2
  receipt's honest producer.

### §6 amendments (orchestrator rulings, step-5 tranche 1)

Four questions the paragraph above did not answer, raised by the
`HartBlock`/`RiscvExec` port and ruled on here.  Same convention as the
RULINGs: revisit is welcome, silence is consent.

A6.1 **THE INTERP BUNDLE IS `tso_interp_of`, AND IT LIVES IN
`RiscvExec.v`.**  `RiscvPtsto.tso_interp_at` is stated at a `gstate` and
holds `view_auth … (avf g)` — the WHOLE per-agent view function — but a
leaf works at `mstate` and must never see `g`.  The bundle handed to a
leaf is therefore the gstate-free repackaging

    tso_interp_of E (img mem : gmap Arch.pa (bv 8))
                    (log : list pwmsg) (V : agent -> nat)

= `tso_interp_at`'s body with `gimg/gmem/glog/avf g` abstracted, and
`⌜mm_ok g⌝` restated as its two pure ties (`mem = flat img log` and
`∀ h, V h ≤ length log`).  `V` is handed over ABSTRACTLY, together with
`⌜V h = tv⌝` for the focused hart; the callback returns the bundle at the
FUNCTION UPDATE (`λ h', if h' = h then tv' else V h'`) and the lifting
rule discharges `that = avf g'`.  It lives in `RiscvExec.v` behind a
`⊣⊢` with `tso_interp_at` rather than definitionally in `RiscvPtsto.v`:
every leaf already `Require`s `RiscvExec`, and iterating on `RiscvPtsto`
costs a ~20-minute rebuild per attempt.  If the `⊣⊢` unfolding later
measures as a proof-performance hazard, moving it definitionally into
`RiscvPtsto.v` is a MECHANICAL follow-up — a marker to that effect stays
in the `RiscvExec.v` header.

A6.1a **THE GATE BRIDGE** (found while wiring §6's `Mobl_ram_plain` to
its discharge; resolved, no seam touched).  A6.1 and the step-4 kit were
designed against DIFFERENT assumptions and meet at the load gate:
`TsoCtx.ctx_load_ok` — whose own header names `Mobl_ram_plain` as its
consumer — is stated at a `gstate` and `tso_interp_at`, while A6.1 says a
LEAF must never see a `gstate` and so hands over `tso_interp_of`.

They reconcile without moving either statement, because `tso_interp_at`
READS ONLY four fields of its `gstate` (`gimg`, `gmem`, `glog`, `gtv`):
the bundle can RECONSTRUCT one, the other five filled with anything.
`RiscvExec.gs_of` does that and `tso_interp_of_at_gs` is the `⊣⊢`, both
directions so a gate can be applied and the bundle handed back.

WHAT MAKES IT WORK IS THE BUNDLE'S THIRD PURE TIE.  The reconstruction
needs `avf (gs_of …) =₁ V`, and `avf` answers `length log` off the hart
range — so without `⌜∀ h, NCPU ≤ h → V h = length log⌝` the view function
would be unconstrained exactly there.  That tie was added in tranche 2
for `vstep`'s idle case; it turns out to be what makes the kit's gate
reachable from a leaf at all.

A6.2 **THE DMA'S FOUR GHOST STEPS ARE `wp_disk_step`'s, AND THE
TIMESTAMP AUTHORITY IS A CALLBACK OBLIGATION.**  §2's disk arm appends
`PWMsg W disk_agent`, so `wp_disk_step` owes the same four steps
`Wobl_ram` owes (γts to the new top over `dom W`, γlogm persist,
`mono_nat` bump, view).  The view half is FREE: `avf` pins the disk agent
to `length glog`, so the append moves it with no update.  The γts half is
NOT free and cannot be done by the rule alone — the `era_ts_name`
fragments for `W`'s addresses ride inside the CLIENT's `ctx_pointsto` at
the client's own dq — so the timestamp authority is handed to the
callback exactly as the image auth already is, and the callback owes it
back at the appended log.

A6.3 **THE POWER ARMS' ERA WIPE LANDS WITH ADEQUACY (step 6).**  §2's
last bullet (`gimg := reset memory`, `glog := []`, `gtv := λ_, 0`,
`gmem := gimg`) has no lifting rule in `RiscvExec.v` and does not get one
here; the fresh era's `tso_interp_at` allocation is part of step 6's
initial-state ghosts.  A one-line marker sits where the lifting rules
live.

A6.4 **NO gstate-LEVEL `all_own` MACHINERY NOW** (open item for step 6).
`HartBlock`'s solo-block bracket is proven under the per-step ties
`s.(mem) = flat img log` and `all_own h log` (RULING 3, discharged);
`RiscvExec.hart_block_exec` closes it against `exec`.  Neither has a
CONSUMER anywhere in the tree, so the `gstate`-level fact that would feed
them is deliberately not built.  The finding to carry into the adequacy
work: at `gstate` level the solo era means "solo hart AND no DMA yet" —
the disk arm appends `PWMsg W disk_agent`, which breaks `all_own` for any
hart — so a boot bracket that wants it must be stated over the stretch
before the disk thread's first DMA, not merely before the other harts are
released.

A6.5 **THE BARRIER STAYS A SILENT NODE, AND THE SILENT STRETCH CARRIES
THE VIEW** (raised by the step-5 lifting port; NEEDS RATIFICATION).
`HartLift.hsil_node` — the silent-stretch walker every register-only
window is proven with — accepts `Interface.Barrier` along with the
announce class.  Post-flip that is no longer view-neutral: a fence with a
W→R edge DRAINS, so "silent node ⇒ the machine state is unchanged" is
FALSE for `fence rw,rw`.  Three ways out were available; the one taken is
the middle one, chosen because it is the only one that does not
invalidate existing proofs:

- drop `Barrier` from `hsil_node` (every silent stretch that walks over a
  fence it does not care about breaks — rejected);
- keep it silent and let the stretch CARRY the view: a new
  `HartLift.hsil_tv` / `hbar_tv` names the node's view effect
  (`fence_post` at a barrier, `tv` at everything else), the bridge lemmas
  conclude at `hsil_tv …` instead of at `tv`, and `wp_hsil_node` /
  `wp_hsil2_node` / `wp_hspan_node_local` pay one MONOTONE
  `RiscvExec.tso_interp_of_advance` — TAKEN;
- fuse the fence's receipt into the stretch (rejected: it would make
  every silent window mint `hart_view_lb`, which is not sound to hand out
  unconditionally).

CONSEQUENCE FOR §6's BARRIER LEAF (ratified): it stays a SEPARATE rule
over the same node, for the proof that wants the acquire receipt.  A
barrier walked by a silent stretch drains but DELIBERATELY PRODUCES NO
RECEIPT; a barrier stepped by the leaf drains and mints one.  Two ways to
step a fence, both sound, the proof picks — and the LEAF IS THE ONLY
PLACE A RECEIPT IS BORN, which is what keeps the receipt's meaning sharp.

A6.6 **THE READ RULE SPLITS, AND THE RECEIPT IS MINTED WHERE THE VIEW
AUTHORITY IS OPEN.**  Two decisions about `HartEvents.v`, the §6 leaf
file.

(a) THE SPLIT.  `wp_hart_ram_read` decided only `ak_excl`; the flipped
`MemRead` arm has THREE RAM branches, so the rule becomes two:

  - `ak_strong = true` (ifetch / page walk, RULING 1) keeps today's
    obligation verbatim — a `read_bytes σ.(mem)` fact.  This is §6's
    `Mobl_ram`.
  - `ak_strong = false` (the plain explicit load) takes §6's
    `Mobl_ram_plain`: the caller exhibits `w` and proves
    `∀ j < n, ∀ tv', tv ≤ tv' → tv' ≤ length log →
       tso_read img log (hart_agent cpu_id) (pa_add pa j) tv' =
       Some (nth_byte w j)`,
    and the rule then advances the view with
    `RiscvExec.tso_interp_of_advance`.

  The caller-side propagation is the INTENDED design, not collateral:
  `HartMLoad` / `HartMFetch` / the PT trio start producing that
  `tso_read` fact from `ctx_pointsto + own_context` through
  `TsoCtx.twin_load_ok`'s image.  That is what the whole twin exists for.

(b) THE RECEIPT.  The EXCLUSIVE READ rule — and the conditional/AMO write
whose success arm takes the view past its own append — MINTS the
machine-level receipt IN ITS POSTCONDITION, `TsoGhost.view_lb` at
`(hart_agent cpu_id)` and the new top, handed to the callback beside the
bundle.  Rationale: the rule is the one moment the view authority is in
hand AT THE TOP; a separate `twin_passed_get` wrapper would have to
re-open the interpretation later, which is strictly worse; and a
persistent receipt costs a consumer that does not want it nothing.
`TsoCtx.hart_view_lb` stays the Σ-SURFACE WRAPPER over this machine-level
fact — `HartEvents.v` must NOT import `TsoCtx` to state it.

A6.7 **RULING 1 HAS NO IMPLEMENTATION: `ak_strong` IS IDENTICALLY FALSE ON
EVERYTHING THIS MODEL EMITS** (blocking; NEEDS A RULING).  Found while
porting `HartEvents.v`; it is upstream of the whole leaf-consumer tier.

THE FACT.  `RiscvLang.ak_strong` is `true` only for `AK_ifetch` and
`AK_ttw`.  The generated model produces `AK_ifetch` from exactly one
place — `read_ram`'s `Read_ifetch` arm — and **nothing in the model ever
passes `Read_ifetch`**: it occurs only in that arm and in
`undefined_read_kind`'s pick list.  `AK_ttw` is never produced at all.
Every read this tree performs is built by
`read_ram <kind> (Physaddr pa) n false`, and the resulting `ReadReq` is
BYTE-FOR-BYTE IDENTICAL for an instruction fetch, a page-table walk and
an ordinary data load:

    access_kind = AK_explicit {AV_plain; AS_normal};  va = None;
    translation = tt;  tag = false

(`HartMFetch.mread_req`/`mread_req2`/`mread_req8`, `HartSMem.mread_req1`
— all the same record).  Only the RESERVED reads differ
(`AV_exclusive`).  So at the `MemRead` node there is NO INFORMATION
distinguishing a fetch or a walk from a data load.

THE CONSEQUENCE.  The strongly-ordered RAM-read arm of `mnode_step` is
DEAD CODE, §6's `Mobl_ram` has no non-exclusive instances, and every
fetch and every PTE read lands on the PLAIN TSO ARM — owing
`Mobl_ram_plain`.  For TEXT that is cheap (timestamp 0 is visible at
every view: `TsoMemPa.read_down_0`).  For PAGE TABLES it is not: xv6
writes its page tables at run time (`kvmmake`, `uvmcreate`, `freewalk`,
the Svadu A/D write-back), so those bytes live in the LOG and the walker
would need the full `ctx_pointsto + own_context` twin.  That is exactly
the expansion RULING 1 was written to prevent ("this keeps the whole
fetch-geometry and TLB lanes' proofs against `gen_heap`(flat) … out of
the port").

THE THREE WAYS OUT (a ruling is needed before the consumer tier can move):

- **(A) No strong arm; "flat" callers discharge `Mobl_ram_plain` from a
  STABILITY fact.**  No `RiscvLang.v` change, no full rebuild.  Text is a
  one-liner (`latest img log a 0 v` + `tso_read_of_latest`), but the PT
  lanes genuinely enter the port.  Honest, and does NOT deliver RULING 1.
- **(B) Make the machine's fetch/PTW arm real** by having the model
  wrapper emit `AK_ifetch`/`AK_ttw` for those accesses.  Delivers RULING
  1 exactly as written and keeps the fetch/TLB lanes flat, but touches
  the generated-model boundary: every `mread_req*` record and its
  `hread_req_at_*` lemma moves, plus a full rebuild.
- **(C) Classify by ADDRESS CLASS, not by request.**  Two leaf rules, the
  flat one gated on a predicate (`addr_is_text`, "in a kernel page-table
  page").  No model change, keeps the walker flat, matches the standing
  "text is timestamp-0" ruling — but the page-table half is a real
  coherence assumption (nobody stores to a PTE concurrently with a walk)
  that has to be justified, not gifted.

WHAT IS ALREADY IN PLACE.  `HartEvents.v` is green and carries BOTH read
rules — `wp_hart_ram_read_strong` (§6's `Mobl_ram`, today's flat
obligation verbatim, currently INSTANCE-FREE) and
`wp_hart_ram_read_plain` (§6's `Mobl_ram_plain`) — plus their `swp`
forms.  The bare names `wp_hart_ram_read`/`swp_hart_ram_read` are GONE ON
PURPOSE, so every call site is forced to say which it means and the red
list is exactly the set of decisions this ruling settles.

**RULING: (B).**  RULING 1 already commits the SEMANTICS ("fetches and
walks read the FLAT memory"); if the machine cannot distinguish those
accesses then the semantics literally cannot SAY RULING 1, so (B) is its
only faithful implementation.  (A) and (C) are AMENDMENTS to the ruling,
not implementations of it: (A) pulls the fetch-geometry and PT lanes into
the port — the very thing RULING 1 exists to prevent, and even the text
half would then owe a "no log message ever hits a text address" W^X fact;
(C) bakes an address-class policy into the MACHINE, which is not what
hardware does, and leaves the PT half an unjustified coherence
assumption.

### A6.7(B) — THE TAGGING SEAM DOES NOT EXIST IN HAND-WRITTEN CODE (STOP)

Implementing (B) was scoped under "tag at the request-construction seam
in the hand-written wrapper only; do not edit generated files".  That
seam is not there.  Four facts, each checked:

1. **The read kind is chosen from the wrong information, in generated
   code.**  Generated `checked_mem_read` binds
   `rk := read_kind_of_flags aq rl res` (`rv64d.v:23966`), and
   `read_kind_of_flags` (`rv64d.v:23693`) is generated and sees ONLY the
   acquire/release/reserved flags.  The `MemoryAccessType` (`access`) IS
   in scope at that point — it is passed to `pmpCheck` and `mmio_read`
   two lines away — but it never reaches the read-kind choice.
2. **The request record is built in generated code**, inside `read_ram`
   (`rv64d.v:6964–6997`), and the outcome is emitted by `sail_mem_read`,
   which lives in the OPAM PACKAGE
   (`SailStdpp/ConcurrencyInterfaceBuiltins.v`) — outside the tree
   entirely.
3. **The hand-written files are nowhere near the read path.**
   `model-xv6iris/` contains exactly two: `riscv_extras.v` (41 lines:
   bit-shift helpers, `get_time_ns`, reservation/terminal axioms) and
   `xv6iris_extras.v` (105 lines: reservation and `plat_term_write`
   realisations).  Neither ever sees a `MemoryAccessType`.
4. **`AK_ttw` IS UNREACHABLE BY CONSTRUCTION** — it occurs ZERO times in
   `rv64d.v` and `rv64d_types.v`.  `read_kind` has seven constructors and
   none is a walk (`Read_plain`, `Read_ifetch`, `Read_RISCV_acquire`,
   `Read_RISCV_strong_acquire`, and the three reserved ones), and
   `read_ram` has no arm producing `AK_ttw`.  So the WALKER half of (B)
   is not a tagging change at all: it needs a NEW read kind (or a new
   `read_ram` arm keyed on the access type).

**REGENERATING FROM A FRESH CLONE: THE SMT-CACHE TRAP.**
`tools/regen_sail_model.sh` passes
`--memo-z3-path "$SAIL_RISCV_DIR/build/model/sail_smt_cache"`, and
`build/model/` is a CMAKE BUILD DIRECTORY that `git clone` does not
create.  The long-lived checkout at `/shared/xv6rocq/sail-riscv` has one
(with a ~600 KB `sail_smt_cache` in it), which is why the script has
always worked there; a fresh clone dies at the very END of the run with

    Error: …/sail-riscv/build/model/sail_smt_cache: No such file or directory
    Fatal error: exception Sys_error(…)

after sail has already done all of its work.  THE FAILURE MODE IS THE
DANGEROUS PART: `set -e` aborts before the install step, so
`model-xv6iris/` is never written, and a `cmp` of the output against a
pre-run snapshot reports IDENTICAL — a green-looking idempotence result
from a run that produced nothing.  Fix before regenerating:
`mkdir -p $SAIL_RISCV_DIR/build/model`, and seed it by copying the
reference clone's `sail_smt_cache` (the cold run costs many minutes of
Z3; the warm one is a fraction of that).  Check the script's exit status,
not just the diff.

CONSEQUENCE: (B) is a MODEL-SOURCE change (`core/phys_mem_interface.sail`
— `checked_mem_read`/`read_kind_of_flags`, plus a walk kind) followed by
a regeneration, not a wrapper edit.  And it cannot be started from this
tree: `model-xv6iris/` holds no `.sail` sources at all (only the
generated `.v`, the two extras, `sail-config-rv64d.json` and
`sail-modules.txt`), so it needs the upstream Sail checkout and a
`make model`.  Per the stop rule this is reported rather than improvised;
it reopens the choice between (B)-as-model-change and the (A)/(C)
amendments.

### A6.7(B) — THE PROTOTYPE (local only; ratification package)

Built entirely in the fliptree; nothing pushed, nothing outward-facing.
The `sail-riscv` fork is cloned at `FLIPTREE/sail-riscv`, detached at the
pinned `23dcf8fd…`, with the patch as ONE local commit on top —
**`00046a7` "Tag instruction fetches and page-table walks at the
concurrency interface"**.  That commit is the artifact to ratify.

**IDEMPOTENCE: PASS.**  Regenerating at the pinned rev UNPATCHED with
sail 0.20.2 reproduces the checked-in model byte-for-byte:

    rv64d.v         IDENTICAL   (45060 lines)
    rv64d_types.v   IDENTICAL   (14813 lines)
    riscv_extras.v  IDENTICAL   (41 lines)

(mtimes confirm the files were really rewritten, not skipped — see the
SMT-cache trap above for why that check matters.)  The version-skew worry
does not arise: the pinned rev's `cmake/sail_required_version.txt` asks
for **0.20.2**, exactly the sail installed, so the script's "asks for
0.20.1" note is stale.  A clean baseline means the (B) diff below is
attributable entirely to the patch.

**THE PATCH** — 25 insertions, 1 deletion, two files.

`model/core/phys_mem_interface.sail`: a new `read_kind` constructor and
one arm in `read_ram`'s access-kind match —

    enum read_kind = {
      Read_plain,
      Read_ifetch,
    + Read_ttw,                       // + an 8-line comment
      …
    }

        Read_ifetch => AK_ifetch(),
    +   Read_ttw => AK_ttw(),

`model/sys/mem.sail`, inside `checked_mem_read` — the whole behavioural
change is this one `let`:

    - let rk = read_kind_of_flags(aq, rl, res);
    + let rk : read_kind = match (access, res) {
    +   (InstructionFetch(), false)   => Read_ifetch,
    +   (Load(PageTableEntry), false) => Read_ttw,
    +   (_, _)                        => read_kind_of_flags(aq, rl, res),
    + };

THE `res` GUARD IS LOAD-BEARING.  The fork's A/D-bit atomic update reads
its PTE through `read_pte_exclusive` (`sys/vmem.sail:76`), i.e.
`mem_read_priv(Load(PageTableEntry), …, res = true)`.  An unguarded
`Load(PageTableEntry) => Read_ttw` would have swallowed it and turned an
EXCLUSIVE read into a walk read, destroying the reservation and
`resv_ok`.  Guarded, it falls through to `Read_RISCV_reserved`, which is
correct and strictly stronger (RiscvLang's exclusive arm: flat read, view
to the top).  `Read_plain` therefore still means exactly what it meant —
an explicit data load — and no existing kind changes meaning.

**THE REGENERATED DIFF** (patched vs the byte-identical baseline, so all
of it is attributable to the patch):

    rv64d.v         100 changed lines
    rv64d_types.v    23 changed lines
    riscv_extras.v    0 changed lines

`rv64d.v`'s 100 collapse to **32 once sail's fresh-variable gensyms
(`exNNNNNN_`) are normalised away**, and of those 32 the SEMANTIC delta is
about a dozen lines:

  - `Read_ttw;` in `undefined_read_kind`'s pick list;
  - `Read_ttw => returnM ((AK_ttw (tt)))` in `read_ram`;
  - the nine-line `match (access, res) with … end >>= fun (rk : read_kind) =>`
    replacing the single `liftR ((read_kind_of_flags (aq) (rl) (res))) >>= fun rk =>`.

The rest is mechanical noise worth naming so nobody hunts it: six lines of
MONADIC BINDER RENUMBERING (`w__2/w__3/w__4` → `w__3/w__4/w__5`, because
the new match adds a bind) and four lines where `internal_error`'s
`__FILE__`/`__LINE__` literals shift by 8–9 (the patch adds that many lines
above them in `phys_mem_interface.sail`).  Nothing in `iris/` matches on
those strings.

`rv64d_types.v`'s 23 are entirely the enum plus its numbering helpers:
the `Read_ttw` constructor, and `num_of_read_kind` / `read_kind_of_num`
renumbered from 6 to 7 — none of which has a user in `iris/`.

The regenerated model COMPILES CLEAN under `coqc` (the script's own
compile-check, and a fresh `make -f CoqMakefile -j8` of `model-xv6iris`).

**THE PROOF FALLOUT** — small, and ADDITIVE by construction.  The rule
that kept it small: every `*_plain_*` certificate is consumed by DATA
loads (`UserMem`, `SmodeCore`, `WpSconfMem`, `WpAu4`, `WpSmodeHalf`,
`HartMLoad`, the disk lanes), which the patch does not touch, so nothing
existing was retargeted — the fetch and walk lanes got TWINS instead.
Each twin's proof is its `_plain_` original verbatim: after
`unfold read_ram; cbn match` the arm contributes only the request's
`access_kind` field, and nothing downstream inspects it
(`run_MemRead_ram_intro` / `exec_MemRead` care only about
`dev_addr (ReadReq.pa req)`).

Files changed, with what each needed:

  - `HartMemAsm.v` — `rk_ram_ok` gains `Read_ttw`.  ONE LINE, and the
    patch's only SILENT hazard: the match's `_ => false` wildcard means
    omitting it costs no error, just every walk classified as
    not-reaching-RAM.
  - `RiscvTryStep.v` — `run_read_ram_ifetch_4_pin` (twin).
  - `RiscvFetchExec.v` — `exec_read_ram_ifetch_4`,
    `run_read_ram_ifetch_2_pin`, `exec_read_ram_ifetch_2` (twins); the two
    `exec_checked_mem_read_ram*` sites take the `Read_ifetch` arm, which
    is a `returnR`, not a `liftR` of `read_kind_of_flags`.
  - `WpLoad.v` — `exec_read_ram_ttw_8` (twin, beside the existing
    `exec_read_ram_resv_8`).
  - `SmodePte.v` — the non-reserved PTE read takes the `Read_ttw` arm;
    the RESERVED one (`res = true`, the A/D update) still falls through to
    `Read_RISCV_reserved`, but its `(access, res)` match must be reduced
    before the `liftR` is exposed.
  - `HartMFetch.v` — fetch-variant request records rather than edits to
    the shared ones (`mread_req`/`mread_req2` are also consumed by
    `HartSMem`/`SmodeCorePt`, `mread_req8` by `HartMLoad`):
    `mread_req_ifetch`, `mread_req2_ifetch` and their
    `hread_req_at_*`/`hread_resume_*` lemmas, carrying `AK_ifetch tt`.
  - `MemAccessGen.v` (+ its 2 consumers in `UserMemMis.v`) — the generic
    split engine keeps `acc` ABSTRACT, so the new match does not reduce.
    Fixed with a side condition `rk_from_flags acc = true` and a rewriting
    lemma `rk_select_flags` that restores the old shape, leaving the long
    proof script untouched.  Two lemma statements gained a hypothesis
    (`exec_checked_mem_read_split`, `goodmb_checked_mem_read_split`); both
    are narrowly consumed (2 and 1 call sites, all in `UserMemMis.v`).

STILL TO ABSORB when their cone is reachable: `SmodeCorePt.v` (S-mode
fetch, widths 4/2 → the `_ifetch` twins), `PtTreeAdue.v` (8-byte PTE reads
→ needs an `mread_req8_ttw` twin carrying `AK_ttw tt`).

**AND THE PAYOFF IS VISIBLE ALREADY.**  `HartMFetch`'s two fetch sites now
take **`swp_hart_ram_read_strong`** — §6's `Mobl_ram`, the FLAT rule —
discharging `ak_strong … = true` by `reflexivity`.  That is RULING 1
actually holding: the fetch reads flat memory and never touches the store
buffer, and the fetch-geometry lane stays out of the port.  Before the
patch that rule had no instances at all.

**TWO-KIND, NOT ONE-KIND.**  Adding a real walk kind rather than reusing
`Read_ifetch` costs almost nothing on the proof side:
`num_of_read_kind` / `read_kind_of_num` / `undefined_read_kind` have ZERO
users in `iris/`, and the only match over `read_kind` in the whole tree is
`HartMemAsm.rk_ram_ok`, which has a `_ => false` wildcard — so it
compiles unchanged but would silently classify a walk as not-reaching-RAM.
One line (`Read_ttw` into its `true` list) is the entire enum-side
fallout.  The honest form was therefore taken.

### A6.7(B) — WHAT REMAINS AFTER THE PROTOTYPE

The model patch's own fallout is CLOSED (list above, all green).  What is
left in the tree is the leaf/kit tier, and it splits three ways.  Recorded
so the next session does not re-derive it.

**DONE — the fetch/PTW half of §7 step 5's consumers.**  `HartMFetch`,
`SmodeCore`, `UserMem` (M-, S- and U-mode fetch) now take
`swp_hart_ram_read_strong`, discharging `ak_strong … = true` by
`reflexivity`.  §6's `Mobl_ram` — today's flat obligation, verbatim —
holds for them, which is RULING 1 actually working.  `SmodePte` reads its
PTE at `Read_ttw`.  These lanes are OUT of the port, as intended.

**THE DATA HALF IS A Σ-SURFACE RESTRUCTURING, NOT A REPAIR.**  Measured at
`WpMmodeLoad` (the first site that must DISCHARGE rather than thread
`Mobl_ram_plain`): it holds `phys_word_pointsto ea dq v` — a gen_heap
fact — and proves the old flat obligation with `phys_word_read_bytes`.
The new obligation is
`∀ tv' ≥ tv, tso_read_bytes img log h tv' ea 8 v`, and **that is not
provable from a bare points-to at all** — a flat cell says nothing about
what a view below the top can see.  It needs `ctx_pointsto + own_context`
through `TsoCtx.ctx_load_ok` (+ the A6.1a bridge).  So every M-mode data
load's SPEC has to carry the context fact instead of the physical one.
This is the flip working as designed, not breakage: it is exactly the
`mem_pointsto` → `ctx_pointsto` migration the kit exists for.  Threading
is already in place beneath it (`HartMLoad`'s `robl_ram`, `HartMStore`'s
`wobl_ram`), so the obligation reaches this one place.

**THE (iii) WORKLIST, from `TsoCtxShim`'s deliberately-removed
equivalences.**  Each compile error is one entry, as that file's header
says.  `_to_mem` directions are true-but-unproven under the real bodies
(drop the timestamp and the bit); `_of_mem` directions are FALSE at TSO —
a timestamp fragment cannot be conjured — so those sites need their
surrounding invariant to carry `ctx_pointsto` from the start:

  - `DiskInv.v` — `ctx_buf_{to,of}_mem`, `ctx_pointsto_{to,of}_mem`
  - `StackOwn.v` — `ctx_word_{to,of}_mem`, `ctx_pointsto_to_mem`
  - `WpLock.v` — `ctx_word_{to,of}_mem`
  - `KernelDataInv.v` — `ctx_pointsto_to_mem`

**AND THREE TRANCHE-3 LEAVES** (fallout of the `HartEvents` split, not of
the model patch): `HartMemRun` and `WpUart` (callbacks gained binders —
`WpUart`'s is A6.2's DMA conjunct in `wp_disk_step`), and `HartPilot`,
whose two pilot lemmas have NO consumers and are free to reshape.

### A6.7 — WHAT IT GATES

The read side is blocked as expected (`HartMFetch`, `HartMLoad`,
`HartMemRun`, `SmodeCorePt`, `PtTreeAdue`, and `HartPilot`'s pilot
lemma).  The measured surprise is that **the WRITE side's BUILD is gated
too, though its statements are not**: `HartMStore.vo`'s prerequisite cone
runs through `HartMFetch.vo` (the fetch lane) and `HartPilot.vo`, so no
`.vo` below `HartSMem` can be produced until the read classification is
settled — even though every write statement is already ported.
`HartPilot`'s two pilot lemmas (`wp_hart_rw_seq`,
`wp_pilot_started_store`) have NO consumers, so they are free to change
shape when the ruling lands; only its `phys_*` byte lemmas are used
elsewhere (`HartLift2`, `PtTreeAdue`, `WpMmodeLoad`, `HartMemRun`).

### A6.8 THE FORGETFUL PROJECTION IS THE ONLY SURVIVING CROSSING, AND IT
### IS EXPORTED ONCE, BY NAME (step-5 tranche 3; landed)

The dead shim's `ctx_*_of/to_mem` pairs split cleanly, and the split is
now realised in `TsoCtx.v`'s law surface rather than re-derived per site:

- **`ctx_pointsto_forget : ctx_pointsto ξ a dq v ⊢ mem_pointsto a dq v`**
  (and `ctx_word_pointsto_forget` for the 8-byte tower).  This is the old
  `Local` projection `ctx_pointsto_mem_proj`, promoted.  Its header states
  the price where nobody can miss it: it drops the timestamp fragment and
  the clean/dirty bit, NEITHER of which can be recovered, and the result
  **licenses no plain load** (`ctx_load_ok` needs exactly the two dropped
  conjuncts).  `grep ctx_pointsto_forget` is now the honest inventory of
  bytes parked OUTSIDE the ledger — the unflipped `↦ₛ`/`↦₂`/`↦₄` towers,
  the deliberately-raw lock metadata (0.8′ ruling 2), the phys tier
  (ruling 6).  Rejected alternative: leaving it `Local` and restructuring
  each site — the sites are exactly the tiers the standing rulings say
  must STAY raw, so there is nothing to restructure, only a crossing to
  name.
- **`ctx_pointsto_canonical`** and **`ctx_ktier_mono` /
  `ctx_word_ktier_mono`**: the pure conjunct and the tier weakening, read
  off the sealed body directly.  These retire two rehearsal-era seams —
  0.9′'s "`mem_ktier_mono` rides the raw law between two shims" and every
  `to_mem`-then-`mem_canonical` step — for FREE, because neither ever
  wanted a context.  A crossing that exists only to reach a pure fact is
  a crossing that should not exist.

Landed at: `KernelDataInv.kernel_data_string` (the `↦ₛ` seam, unchanged
otherwise), `WpLock.lock_name_intro`, `StackOwn.stack_own_sp_bounds` /
`stack_ktier_mono`, `DiskInv.mem_win_to_phys` / `mem_win_canonical` /
`byte_to_phys`.  All four files GREEN.

**AND TWO FALSE LEMMAS DIED, EACH REPLACED BY THE TRUE ONE:**

- `StackOwn.stack_own_reindex` was `stack_own (XI:=ξ) ⊢ stack_own (XI:=ξ')`.
  It is now the TRANSPORT
  `ctx_dom ξ ξ' -∗ stack_own (XI:=ξ) sp n ==∗ ctx_dom ξ ξ' ∗ stack_own (XI:=ξ') sp n`
  — i.e. `CtxMorph` at the stack region, proven by `ctx_morph_big_sepL` +
  `ctx_morph_word`.  Its one call site (`ProofSwtch`) must now SUPPLY the
  domination, which is the M2 entry the placeholder was standing in for,
  made visible in the statement instead of hidden in the proof.
- `WpLock.lk_cpu_cell_acc` was
  `(∃ ξ, ctx_word_pointsto ξ (lock_cpu lk) 1 v) ⊣⊢ lock_cpu lk ↦₈ v`.
  THE ELIMINATION DIRECTION IS FALSE and, worse, unfixable as stated: the
  ∃ hides WHICH context owns the cell, and nothing can dominate an unknown
  context.  Replaced by a named `lk_cpu_cell` (the ∃ itself), the three
  `lk_cpu_res_free/win/held` unfold lemmas restated at it, and the trivial
  `lk_cpu_cell_intro`.  `lk_cpu_res` stays ∃-context (0.8′ ruling 2
  holds).  The M4 entry, now written in the file: the invariant must hold
  the cell's context PARKED, the acquirer mints `ctx_dom` from it with
  `ctx_dom_of_parked` and moves the word with `ctx_morph_word`.  The
  failures at `WpSconfLock` (which reads and writes the cell) ARE that
  entry.

### A6.9 THE LEDGER HAS NO MINT — WHY EVERY `_of_mem` IS STRUCTURALLY
### DEAD, AND WHAT THE DMA RECLAIM ACTUALLY NEEDS

The shim's header called the `_of_mem` directions "FALSE at TSO".  They
are worse than false-as-stated; they are **unreachable by any premise**,
and it is worth knowing why before anyone tries to rescue one with a side
condition.

`ctx_pointsto` carries `(pa_of ppn a) ↪[ts_name]{dq} t`, a `ghost_map`
ELEMENT of `era_ts_name`, and `tso_interp_at`'s tie is
`⌜dom TM = dom g.(gmem)⌝`.  A `ghost_map` element can only be created by
`ghost_map_insert`, which demands the key be ABSENT from the authority —
so every byte's element was handed out exactly once, at era allocation,
and no rule above the interpretation can produce another.  A raw byte has
left the ledger permanently.  There is no "given the interp and a full
points-to, mint the timestamp" gate, and there cannot be one at the
current tie.

TWO CONSEQUENCES WORTH CARRYING:

1. **The phys tier cannot STORE, either.**  A store's `Wobl_ram` owes the
   γts update over its footprint, which needs the elements.  So ruling
   6's "phys tier stays RAW" reads, post-flip, as "phys bytes are
   read-only and only through a pristine/strong arm".  `HartPilot`'s
   pilot rule is the worked instance: its store's append is now a
   THREADED premise, not a discharged one.
2. **If the tie were weakened to `dom TM ⊆ dom g.(gmem)`**, `ghost_map_insert`
   becomes available and a real mint gate exists — but it would still have
   to PROVE the byte's latest write visible, and the only free ways to
   know that are the top view (post-AMO) or the solo era.  That is a
   `RiscvPtsto.v` change (a full rebuild) and is recorded as an option,
   not taken.

**THE DMA RECLAIM, in full, since `DiskInv` is where it bites.**  The
device's bytes reach a driver's ledger for exactly one reason — the
driver's hart view passed the DMA's timestamp — and only an acquire says
so.  The shape:

  - the lease holds the window's context PARKED (`ctx_parked ξ T`)
    together with its timestamp elements;
  - `wp_disk_step`'s callback moves those elements to the appended log
    (A6.2, already stated in the rule);
  - the reclaiming thread, whose lock acquire put its view at the log top,
    mints `ctx_dom ξ cur_ctx` with `ctx_dom_of_parked` and re-registers the
    bytes through `ctx_morph_word`.

That is the `ctx_dom` handoff tso-port.md §1's RULING 2 promised, spelled
out.  **What was done instead, to keep `DiskInv` green and put the errors
where the work is:** the window bridge's CORE is now stated at the RAW
fact in both directions (`mem_win_to_phys_raw` / `phys_win_to_mem`) —
it is a pure kmap/identity-mapping fact and never wanted a context, and
the ctx entry point `mem_win_to_phys` is a thin `_forget` wrapper.  That
makes `word2_to_phys`/`word4_to_phys`/`phys_to_word2`/`phys_to_word4`
CROSSING-FREE (the `↦₂`/`↦₄` towers are unflipped, so the flip-era ctx
detour through the shim was pure overhead).  Only two lemmas' statements
moved, both flagged in place:

    phys_to_word8 : … -∗ phys_word8 a w -∗ word_pointsto a (DfracOwn 1) w
    phys_to_byte  : … -∗ phys_pointsto a (DfracOwn 1) b -∗
                          mem_pointsto a (DfracOwn 1) b

(both were `↦₈` / `↦ₘ`, i.e. ctx).  Their four call sites —
`ProofVirtioDiskRwF` ×3, `ProofVirtioDiskIntr` ×1 — are the DMA-reclaim
worklist, one entry each, and they are precisely the windows the DEVICE
writes (the descriptor doubleword and the status byte).

### A6.10 THE PRISTINE BYTE: THE RAW TIER'S OWN LOAD GATE
### (landed in `TsoCtx.v`; the `WpMmodeLoad` fix is one edit away)

A6.7(B)'s "the data half is a Σ-surface restructuring" is right for a byte
that is WRITTEN.  It is wrong for the ones M-mode actually loads, and the
cheap gate for those is now in the kit.

A byte whose LATEST WRITE IS THE ERA IMAGE — timestamp 0 — is visible to
EVERY agent at EVERY view, unconditionally (`TsoMemPa.read_down_0`:
`visibleb h tv log 0` is `true` with no side condition).  So its value
determines a plain load with **no context, no view, no bound, no log
length**.  The resource that says it:

    pristine_byte a  :=  a ↪[ts_name]□ 0
    pristine_win a n :=  [∗ list] j ∈ seq 0 n, pristine_byte (pa_add a j)

DISCARDED is exactly the right strength and it is not a convenience: a
discarded element also forbids the byte from ever being STORED to again (a
store must UPDATE it).  Read-only-forever and readable-from-anywhere are
the same fact here, so one resource says both — and it is persistent, so
it costs a holder nothing and serves every consumer of an image byte at
once.  The two gates, both proven:

**AND `ctx_pointsto`'s CLEAN ARM CHANGED SHAPE FOR THE SAME REASON.**  It
was `mono_nat_lb_own (ctx_bound_name ξ) t`; it is now
`llb (ctx_bound_name ξ) t`, i.e. that lower bound **or `⌜t = 0⌝`** —
`TsoGhost.llb`'s own trick, at the context's bound instead of the log
length.  This is not tidying.  `mono_nat_lb_own_0` is an UPDATE
(`⊢ |==> mono_nat_lb_own γ 0`), so with the bare bound an image byte's
justification costs one bupd PER CONTEXT — and a `∀ ξ` image fact would
need infinitely many under the binder, which makes
`KernelDataInv.kernel_data` (and kernel text) **unmintable as stated**.
With the `⌜t = 0⌝` arm the justification mentions no context at all, and
the mint is a plain entailment:

    ctx_pointsto_of_pristine     : kmap_at (svpn_of a) ppn KP_rw -∗
                                   mem_pointsto a DfracDiscarded v -∗
                                   pristine_byte (pa_of ppn a) -∗
                                   ctx_pointsto ξ a DfracDiscarded v
    ctx_pointsto_of_pristine_all : … -∗ ∀ ξ, ctx_pointsto ξ a DfracDiscarded v

(every premise persistent, so the ∀ costs nothing; `ppn` is explicit
because the mem fact's page number is existential while the receipt lives
at the PHYSICAL address, and the caller's own `kmap_at` pins it).  Nothing
downstream noticed: `llb_valid` gives `t ≤ B` on one arm and `0 ≤ B` on
the other, which is all `ctx_load_ok` and `ctx_morph_pointsto` ever asked.
One helper was needed — `llb_valid_q`, the fraction-generic form, because
`ctx_dom` holds only half the bound authority.

**THIS IS `BootCarve.kernel_data_intro`'s FIX, AND IT IS LANDED.**  The
carve hands raw discarded image bytes PLUS their pristine receipts and gets
the `∀ ξ` fact:

    kernel_data_intro (g : gstate) :
      (forall x, ram_lo <= x < ram_hi -> g.(gmem) !! pa_of_z x = Some (boot_byte x)) ->
      ([∗ map] a ↦ b ∈ ran_bytes g text_end rodata_end, a ↦ₘ□ b) -∗
      ([∗ map] a ↦ _ ∈ ran_bytes g text_end rodata_end, TsoCtx.pristine_va a) -∗
      kernel_data

`BootCarve` stays on the import blacklist — it names `TsoCtx` QUALIFIED
(`Require TsoCtx`, no `Import`), exactly as it named the shim before.  The
VA-side receipt `pristine_va a := ∃ ppn, kmap_at (svpn_of a) ppn KP_rw ∗
pristine_byte (pa_of ppn a)` exists because a consumer names an image byte
by its VA and does not know the page number, while the ledger is keyed
physically; `kmap_at_agree` is what lets it meet the `mem_pointsto`'s own
existential.  The second premise is `BootCarveMain`'s and then step 6's,
where the era's initial-state ghosts mint it.

**A MEASURED TRAP, recorded because it cost 30 minutes and looked like a
hang in an unrelated place.**  The obvious script — pull the byte out of
the big-op at `boot_byte a`, then `rewrite Hbb` to turn it into `b` —
does not terminate: two whole-range `big_sepM`s over `ran_bytes` are in the
proofmode environment, and `rewrite` walks them.  `coqc -time` names the
sentence exactly (the stream stops on it, at 14 GB RSS).  The fix is to
pin the value IN THE PURE LOOKUP (`rewrite <- (boot_byte_data …)` inside
the `assert`) so no `rewrite` ever touches the Iris goal — the same
discipline `KernelDataInv.kdata_ro_lookup`'s note already states for
`map_lookup_filter_Some_2`.

The two load gates, both proven:

    pristine_read_ok       : gen_heap_interp g.(gmem) -∗ tso_interp_at … g -∗
                             phys_pointsto a dq v -∗ pristine_byte a -∗
                             ⌜∀ h tv, tso_read g.(gimg) g.(glog) h tv a = Some v⌝
    pristine_read_bytes_ok : … the window form, concluding
                             ⌜∀ h tv, tso_read_bytes … a n w⌝

Note the shape: `∀ tv` with **no lower bound at all**, so a consumer's
`tv ≤ tv'` / `tv' ≤ length log` premises are simply not needed —
`HartMLoad.robl_ram` falls out.

WHO MINTS IT: the era's initial-state ghosts (step 6 / adequacy), beside
`kernel_text`/`kernel_data`'s mints — the image is where timestamp 0 comes
from.  This is the standing text-is-timestamp-0 ruling, stated as a
resource and extended from text to every never-written image byte.

**`WpMmodeLoad` — RATIFIED BY THE OWNER AND LANDED.**  `wp_ld_gpr`,
`wp_ld_gpr_tor` and `wp_cldsp_gpr_tor` each gained ONE persistent premise;
`phys_word_pointsto` is untouched and stays RAW.  GREEN.  The statement:

    …
    instr pc is_rvc (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    phys_word_pointsto ea dq v -∗
    TsoCtx.pristine_win ea 8 -∗            (* <-- THE MISSING RESOURCE *)
    ( … unchanged … )

and the read node's obligation is then discharged by
`pristine_read_bytes_ok` at `gs_of` (the A6.1a bridge: the leaf holds
`tso_interp_of`, the gate wants `tso_interp_at`, and
`tso_interp_of_pin` + `tso_interp_of_at_gs` reconcile them — exactly as
`ctx_load_ok` is reached).  IS THE PREMISE SATISFIABLE?  Yes, and it is
the truth about these loads: M-mode's only 8-byte data load in this tree
is `entry`'s `ld sp, stack0`, a link-time constant in the image that
nothing ever stores to.  The cascade is `WpEntryNew` and `WpTimerinit`
threading it up to the boot theorem, where adequacy mints it — which is
where an era-image fact belongs.

**ONE IMPLEMENTATION NOTE WORTH THE HOUR IT COST.**  The obligation is
spelled INLINE at the two call sites, not factored into a lemma in
`WpMmodeLoad.v`, and that is forced: the file imports `SailStdpp.Base`, so
a `gmap Arch.pa (bv 8)` BINDER written in it elaborates at the Sail key
instances (`Decidable_eq_mword`/`Countable_mword`) and will not unify with
`tso_interp_of`'s stdpp-keyed one — the durable-notes binder trap, whose
error names neither file.  The `img` the obligation talks about is
INTRODUCED FROM THE GOAL (it comes from `HartMLoad`'s premise), so it
carries the right instances and the trap does not fire.  `BootCarve.v`'s
header records the same rule for the same reason.

### A6.11 THE DMA WRITE SET IS ∃-QUANTIFIED, AND THAT MAKES `wp_disk_loop`
### UNPROVABLE (machine-tier) — **RULED, OPTION (A), AND LANDED**

**RULING (owner, 2026-08-26): option (A).**  "An under-determined `W` isn't
just unprovable downstream, it's a weaker machine than the device contract
intends."  Implemented: `disk_step d m d' W`'s second OUTPUT is now the
WRITE SET, not the post-state map — `DiskStepDma` yields its own `w`,
every other arm yields `∅`, and a caller reads the post-state as `W ∪ m`.
The `prim_step` arm's log clause became deterministic,

    ((W = ∅ /\ log' = g.(glog))
     \/ (W <> ∅ /\ log' = g.(glog) ++ [PWMsg W disk_agent]))

and `wp_disk_step`'s callback now takes `(d' W log')` with
`⌜disk_step d m d' W⌝` and owes the bundle at `W ∪ m`.  `RiscvLang.v`,
`RiscvExec.v` GREEN; the one fallout inside `RiscvLang` was
`prim_step_mm_ok`'s destructuring (`[(-> & ->) | (_ & ->)]`).
`RiscvExec.tso_interp_of_disk_idle` is the new one-liner the five
non-writing arms use: their `W = ∅` forces `log' = log`, and `avf` pins the
disk agent to the top, so `vstep disk_agent (length log) log V` IS the
bundle they were handed.

THE ORIGINAL DIAGNOSIS, KEPT because it is the reason the shape is wrong:

`WpUart.wp_disk_loop` is blocked, and NOT on plumbing.  `RiscvLang`'s disk
arm reads

    exists d' (W : gmap Arch.pa (bv 8)) log',
      disk_step g.(gdev) g.(gmem) d' (W ∪ g.(gmem)) /\
      ((W = ∅ /\ log' = g.(glog))
       \/ log' = g.(glog) ++ [PWMsg W disk_agent]) /\ …

`W` is tied to the step ONLY through `W ∪ gmem = m'`, which does not
determine it: for ANY arm — including `DiskStepIdle`, where `m' = m` — the
machine may choose a non-empty `W` of bytes already holding those values
and append `PWMsg W disk_agent`.  The WP rule must then hand the callback
a bundle at that appended log, and the callback must re-establish the
`latest` tie for `W`'s addresses, which needs their timestamp elements —
which it does not have and, for arbitrary `W`, cannot have.  So EVERY arm
of `wp_disk_loop`, not just the DMA completion, owes ghost steps it cannot
pay.

THE FIX IS MACHINE-SIDE AND SMALL, and there are two shapes:

- **(A) Make the write set a constructor output**: `disk_step d m d' W`
  with `m' := W ∪ m`, so the arms' own `w` IS the `W` the log records.
  Honest and total; touches `RiscvLang.v` (both copies of the arm), the
  `prim_step_disk_inv` inversion, and `WpUart`'s destructuring.
- **(B) Constrain `W` to the CHANGED bytes**
  (`∀ a v, W !! a = Some v → g.(gmem) !! a ≠ Some v`), which pins `W`
  uniquely as the difference and collapses the disjunction.  One clause;
  the honest weakening it buys is that a device write that changes no byte
  publishes nothing — unobservable except to a hart whose view is stale,
  and only for a value it would have read anyway.

Either is a `RiscvLang.v` edit and therefore a full rebuild.  (A) was the
recommendation and is what landed: it says what §2's DMA arm meant.

**AND IT IS NOT ENOUGH TO CLOSE `WpUart`** — measured, not predicted.  With
A6.11 five of `disk_step`'s six arms hand the bundle straight back and the
sixth is refuted, but the DMA COMPLETION arm still owes the append's four
ghost steps over the device's write set `w`, and the timestamp elements for
those addresses would have to come from the DMA LEASE — which holds
`phys_map`, raw gen_heap bytes with no ledger residue (A6.9).  So A6.11
removes a spurious blockage and leaves the real one: **`WpUart` is an A6.9
entry, not an A6.11 entry**, and its fix is the lease-as-parked-context
restructuring spelled out there.  A premise on `wp_disk_loop` of the shape
"∀ W, publish W" was considered and REJECTED: it is false as stated (it
would let anyone publish arbitrary bytes) and would compile — the
unsatisfiable-premise defect durable-notes calls the worst one.

### A6.12 THE USER TIER IS BLOCKED BY RULING 6, AND IT IS THE BIG ONE

`HartMemRun.swp_hmrun` — the memory-inclusive walker every user-tier proof
runs on (~60 consumers, `UserMem*`, `WpUmode*`, and the `Proof*` syscall
files) — carries its owned bytes as
`bytes_own mm := [∗ map] a ↦ b ∈ mm, a ↦ₚ b`, i.e. the RAW phys tier.
Post-flip its RAM branches split three ways and TWO of them are
unprovable from that resource:

- the FETCH read is fine — post-A6.7(B) it is `ak_strong`, RULING 1's flat
  arm, and the `bytes_own_read` discharge is unchanged;
- the PLAIN data load owes `Mobl_ram_plain`, which a flat cell cannot
  give (A6.7(B)'s measurement, and A6.10's pristine gate does not apply —
  user memory is written);
- the STORE owes the append's four ghost steps, which need the timestamp
  elements (A6.9).

So the whole user tier waits on ONE decision: `bytes_own` becomes
context-indexed.  The shape that costs least, recorded so it is not
re-derived:

    bytes_own mm := [∗ map] a ↦ b ∈ mm, ctx_pointsto cur_ctx a (DfracOwn 1) b

— SAME NAME, SAME ARITY, so the ~60 pass-through call sites are textually
unchanged (the M1-flip trick, again) — plus an `own_context cur_ctx`
premise on `swp_hmrun`, threaded in and out.  THAT premise is the real
cost: it breaks every `iApply`, and it cannot be folded into `bytes_own`
(the token is exclusive, so `bytes_own (mm1 ∪ mm2)` would duplicate it).
It also wants a `ctx_store_ok` in `TsoCtx` — §6 named it (`twin_store_ok`
is proven in `TsoCtxTwin2.v`) but the kit gate was never ported; the
current gate list is load / view-receipt / acquire-domination / pristine
only.

### A6.13 THE FRONTIER AFTER THE (iii) TRANCHE, AND THE THREE NEW FILES
### THE GREENING EXPOSED

A full `-k` sweep after the tranche gives **eight red files**, all in the
leaf/kit tier; the rest of the tree is behind them.  Three of them were
NOT visible before, because their prerequisite cone ran through files this
tranche fixed — so they are new entries, not regressions:

- `PageFields.v` — `bytes_word4` (4 × `ctx_pointsto_to_mem`, the FORGET
  direction, mechanical) and `word4_bwin` (`ctx_pointsto_of_mem`).
- `ByteBuf.v` — `bb_word4_acc`: `ctx_buf_to_mem` (forget) then
  `ctx_buf_of_mem` on the give-back.
- `BootCarve.v` — `kernel_data_intro`, the boot mint (`ctx_pointsto_of_mem`).
  A6.10 has its fix.

`PageFields` and `ByteBuf` are the SAME shape and it is worth naming as a
class rather than as two files: **the unflipped `↦₂`/`↦₄` towers are now a
ONE-WAY TRAPDOOR.**  `bytes_word4` takes context bytes and builds a raw
`↦₄`, forgetting the residue; `word4_bwin` takes the raw `↦₄` apart again
and wants `byte_any` — which IS context-indexed (`↦ₘ` flipped).  The round
trip loses the ledger and cannot recover it (A6.9), so the pair is
unprovable as a pair.  **The fix is M1 STAGE 2 — flip `↦₂`/`↦₄` — not a
per-site repair**, and it deletes the whole class (`WpSconfMem`'s
`wordw8_ctx` adapters, `PageFields`, `ByteBuf`, `DiskInv`'s word2/word4
bridges' remaining asymmetry).  Any per-site patching here is work that
stage 2 throws away.

**AFTER THE FOLLOW-UP TRANCHE** (A6.11 landed, `WpMmodeLoad`/`BootCarve`/
`PtTreeAdue` green, and their cascade `HartSTrans`/`WpEntryNew` absorbed),
the red set is SEVEN files and it has stopped moving — two consecutive
full `-k` sweeps, no file joining:

    HartMemRun.v    A6.14 — the user tier (bytes_own must go ctx)
    HartSMem.v      A6.14 — the S-mode data nodes; NEW, was behind PtTreeAdue
    WpMmodeStore.v  A6.14 — M-mode stores; check solo-era first
    KptTree.v       A6.14 — the PT-slot phys↔ctx pair; NEW, was behind PtTreeAdue
    WpUart.v        A6.9  — the DMA lease has no ledger residue (NOT A6.11:
                            that landed and freed five of the six arms)
    PageFields.v    M1 stage 2 (the ↦₄ trapdoor)
    ByteBuf.v       M1 stage 2 (the ↦₄ trapdoor)

Numbers: **1037 of 1330 `.v` files carry a fresh `.vo`**; the 293 that do
not are these seven plus their dependents.  The count barely moved because
the tranche traded blocked cones for different ones — five files went
green, two previously-unreachable ones (`HartSMem`, `KptTree`) surfaced,
and both are A6.14 members.

RECOMMENDED ORDER from here: **M1 stage 2** (`PageFields`, `ByteBuf`, and
the standing `WpSconfMem.wordw8_ctx` adapter class — build the ↦₂/↦₄ ctx
towers in `TsoCtx` mirroring the ↦₈ one, flip the notations, absorb
error-driven), then **A6.14 as ONE tranche** (port `ctx_store_ok` first;
then `HartSMem` — the smallest blast radius of the four — then
`WpMmodeStore` after checking the solo-era question, then `KptTree`, then
`HartMemRun`), with `WpUart`'s lease restructuring (A6.9) alongside.

THE PRE-TRANCHE SET, kept for the record:

    HartMemRun.v    A6.12 — the user tier (bytes_own must go ctx)
    WpMmodeLoad.v   A6.10 — one persistent premise, statement written out
    WpMmodeStore.v  A6.9  — the phys tier cannot store (same class)
    WpUart.v        A6.11 — RiscvLang's DMA write set is under-determined
    PtTreeAdue.v    A6.7(B)'s own leftover — the 8-byte PTE read needs an
                    `mread_req8_ttw` twin (already listed as STILL TO ABSORB)
    PageFields.v    stage 2 (the ↦₄ trapdoor)
    ByteBuf.v       stage 2 (the ↦₄ trapdoor)
    BootCarve.v     A6.10 — the boot mint; needs the pristine receipts

### A6.14 RULING 6 IS AMENDED, AND THE AMENDMENT HAS FOUR MEMBERS

**RULING (owner, 2026-08-26), recorded as the forced amendment to
tso-port.md §0.8′ ruling 6:** the phys tier stays RAW **only for tiers
whose RAM accesses are rescued by pristine receipts (A6.10) or by the
solo/top collapses**.  A tier that performs plain data loads AND stores of
RUNTIME-WRITTEN bytes must carry ctx facts plus `own_context`, because
A6.9 leaves no other payer for the store's ghost steps.

Four files are in that class, and they are one tranche, not four:

  - `HartMemRun` — the USER TIER's walker (A6.12).  `bytes_own` is `↦ₚ`.
    28 internal uses, ~60 consumers.
  - `HartSMem` — the S-MODE data nodes (`swp_read_ram_node1/2/4/8`, driven
    by the `node_read` tactic).  Same shape one privilege level down: the
    reads are `Read_plain`, so they owe `Mobl_ram_plain`, and the
    threading has to reach an owner.  Blast radius is small and precise —
    28 uses inside `HartSMem`, exactly ONE outside (`WpSconfMem`) — but
    `WpSconfMem`'s own words are deliberately RAW (0.10′ ruling 4), so the
    obligation arrives somewhere that cannot pay it; the discharge point
    has to be designed, not just reached.
  - `WpMmodeStore` — the M-mode store leaf.  A6.10 does NOT rescue this
    one: a pristine byte is read-only by construction (the discarded
    timestamp element forbids the update a store needs), so the M-mode
    stores must either carry ctx facts or be shown boot/solo-era only.
    **The cheaper thing to check first** (owner's ruling 4): if every
    M-mode store in this tree runs before the other harts are released,
    the honest shape is a solo-era store (`TsoMemPa.all_own`) rather than
    a ctx migration — report which it is before building either.
  - `KptTree` — `pt_slot_phys_to_mem`, the PT-slot `↦ₚ₈ ↔ ↦₈` bridge.
    Used in OUT-AND-BACK PAIRS by `ProofCopyout` / `ProofFreewalk` /
    `ProofUvmunmap`: the walk takes a slot down to the phys tier for the
    machine leaf and brings it back.  The round trip loses the ledger and
    A6.9 says it cannot be recovered.  Tempting fix — a `ctx_residue`
    split/join, so the caller keeps the timestamp+bit while the flat cell
    goes down — and it WOULD work for a pair that only READS.  It does not
    work here: the leaf STORES the slot, and a store must UPDATE the
    timestamp, so the residue goes stale in the caller's hand.  The PT-slot
    lane has to carry ctx facts all the way to the leaf.

The `ctx_store_ok` gate (§6's `Wobl_ram`; `TsoCtxTwin2.twin_store_ok` is
already proven) must be ported into `TsoCtx` before any of these can
close — the current gate list is load / view-receipt / acquire-domination
/ pristine only.

### A6.15 M1 STAGE 2 IS LANDED — ↦₂/↦₄ ARE CONTEXT-INDEXED, ↦ₛ IS NOT

**The flip.**  `TsoCtx.v` gained the 2- and 4-byte ctx towers, character
for character the 8-byte one at width 2/4 (`ctx_word{2,4}_pointsto` +
unfold / aligned_p / bytes / intro / timeless / discarded-persistent /
frac_split / half / half_split / half_join / persist / agree /
ktier_mono / forget, plus `ctx_morph_word{2,4}`), and all four dfrac
spellings of `↦₂` and `↦₄` are re-declared at them — bracket form
included, modifiers copied exactly.  Neither tower is sealed, for the
reason the 8-byte one is not: a tower OVER the sealed byte leaks nothing
and the tree's proofs destruct the word shape structurally.

**THE WAVE WAS SMALL — 14 rounds, not stage 1's ~30, and only ONE new
error file per round after the first.**  That is the flip working as
designed twice over: the ↦ₘ/↦₈ seams stage 1 found are the SAME seams,
already fixed, so stage 2 only had to re-point law names and add binders.

**THE PAYOFF, exactly as predicted.**  `PageFields` and `ByteBuf` are
GREEN and their shim crossings are GONE, not converted — in both files
the bytes and the word were on opposite sides of the seal only because
the tower had not flipped:

  - `PageFields.bytes_word4` dropped FOUR `ctx_pointsto_to_mem` lines and
    `word4_bwin` dropped its `ctx_pointsto_of_mem`; neither file imports
    `TsoCtxShim` any more.
  - `ByteBuf.bb_word4_acc` dropped `ctx_buf_to_mem` AND `ctx_buf_of_mem`
    — the out-and-back pair that A6.9 says can never be crossed once it
    has left the ledger simply never leaves it now.
  - `InodeInv`'s hermetic-seal crossing (`ctx_pointsto_shim` under
    `bi.pure_True`) became `reflexivity`.

`DiskInv`'s three widths are now uniform: all three `_to_phys` directions
forget, all three `phys_to_` directions are stated at the RAW fact
(`phys_to_word2`/`_word4` joined `_word8`/`_byte`), and the flip-era ctx
detour through the shim in `word2_to_phys`/`word4_to_phys` — which was
pure overhead once `↦₂`/`↦₄` were raw on both ends — is gone.

**↦ₛ DOES NOT FLIP, and that is a ruling, not an omission.**  It was
listed with `↦₂`/`↦₄`; it is the one that must not move.

  1. IT WOULD PUT A CONTEXT INSIDE `is_lock`.  `WpLock.lock_name` is
     `∃ p, word_pointsto (lock_name_field lk) □ p ∗ p ↦ₛ□ s`, and
     `lock_name` is half of the PERSISTENT lock handle.  Flipping `↦ₛ`
     makes the handle ξ-dependent IN THE STATEMENT — not as the artifact
     of the constant embedding that tso-port.md §0.11′ measured — and a
     boot-minted `is_lock` then cannot be stated at another thread.  That
     is §0.8′ ruling 2, and it is the root both design problems were
     routed around.
  2. IT WOULD BUY NOTHING.  Every string fact in the tree is a DISCARDED
     image literal (lock names, panic messages).  A discarded byte can
     never owe `Wobl_ram`, and its load obligation is discharged by the
     PRISTINE gate (A6.10), which needs no context at all.  The ledger
     index would be dead weight on 37 files.

  Net: flipping it removes ONE `forget` (in `kernel_data_string`), ADDS
  one (in `lock_name_intro`), puts a binder on 37 files and a real ξ in
  the lock handle.  `↦ₛ` therefore LEAVES the stage-2 list and joins
  `↦ₓ`/`↦ᵣ`/`↦ₚ` as deliberately raw.  The reasoning is recorded in
  `TsoCtx.v` beside the stage-2 notations.

**THE ICACHE CLUSTER HAD TO PICK ONE TIER, AND IT PICKED CTX.**  The one
real design decision of the wave.  `IcacheRef.inode_ident`'s two cells
(`i_dev`/`i_inum`) are held in HALVES by `IcacheEscrow`'s arms and by
`IcacheInv`'s `islot_rest`; `IcacheRef` did not import `TsoCtx`, so after
the flip a ctx arm met a raw `inode_ident` — which is not a seam that can
be crossed, it is ONE TIER DISAGREEING WITH ITSELF.  Two ways out were
tried, in this order:

  - RAW, via a `Local Notation` re-declaring `↦₄` at `word4_pointsto` in
    `IcacheInv` and `IcacheEscrow`.  Rejected after measurement: it only
    moves the disagreement (`InodeInv.inode_meta`'s `i_size` IS ctx, and
    `IcacheEscrow` holds both families), and a NON-local `Notation`
    ESCAPES to importers and silently un-flips their `↦₄` too — measured,
    it broke `IcacheEscrow`, which imports `IcacheInv` after `TsoCtx`.
    **Any per-file tier override must be `Local Notation`; a plain one is
    a tree-wide silent un-flip.**
  - CTX, by flipping `IcacheRef` itself.  Taken: it has TWO `↦₄`
    occurrences and no invariants, so the cheapest place to decide the
    cluster's tier is the file that owns the cells.  `IcacheRef`,
    `IcacheInv`, `IcacheEscrow`, `IcacheBoot`, `InodeInv`, `InodeLock`,
    `InodeRegion`, `BioInv`, `BioInitAt`, `BreadLru`, `ProofBreadParts`
    all follow.

**ONE FILE IS GENUINELY MIXED, AND IT IS SPELLED OUT.**  `BreadLru` takes
the flip for its `↦₄` slot cells but its six `bcache_lru` LINK words are
`BcacheInv`'s, which stays raw — so those six statements spell
`word_pointsto` explicitly.  A file that imports `TsoCtx` for one family
and needs another raw spells the raw one out; that is the rule.

**THE STANDING QUESTION STAGE 2 WIDENS (not opens): CTX FACTS INSIDE A
BARE `inv`.**  Three files now hold context-indexed cells inside an
`inv` body at the section's ambient context — `BioInv` (`buf_escrow_body`,
which ALREADY did from stage 1: `BufOwn.buf_own` is `{XI : CurCtx}`),
`IcacheInv` (`itable_body`'s `iref_cells`) and `InodeRegion`.  An
invariant body that names a context can only be used by a thread AT that
context; the honest forms are the ones §0.8′ already ruled for the cases
it met — ∀-context (`kernel_data`), ∃-context plus a parked handshake
(`lk_cpu_res`, `cpu_ctx_free`), or raw (`lock_name`).  Deciding which for
these three is an M2/M4 entry, not a stage-2 one, and it is NOT made
worse by the flip: stage 1 had already put the pattern in the tree.

**FIX-TABLE ADDITIONS from this wave** (for `tso-flip-replay.md`, if the
process is ever re-run):

| symptom | fix |
|---|---|
| `word{2,4}_pointsto_<law>` applied to a ctx fact | the `ctx_` twin; the rename is safe file-wide EXCEPT in files that import `TsoCtxShim` (those hold deliberate raw facts) — 19 files renamed blind, 14 skipped on that rule |
| a plain `Notation` re-declaring a family raw | make it `Local`, always |
| `XI is already used` in a file with inline binders | strip BOTH inline binders and use one section binder, when the decls are plain lemmas |
| a raw fact meeting a ctx one at the SAME address | not a seam — one tier disagreeing with itself; flip the file that OWNS the cells |

**THE UNREACHABLE INVENTORY.**  `grep TsoCtxShim` still names ~40 files
whose shim uses are labelled "↦₂/↦₄ has NOT flipped (M1 stage 2)".  Those
comments are now stale and most of those uses are simply DELETABLE — but
every one of them is behind the A6.14 frontier, so this wave could not
reach, fix or validate them.  They come out with their files.

**FRONTIER.**  Two identical full `-k` sweeps.  **1044 of 1330 files
fresh-green** (up from 1037), red set down from seven to **FIVE**, and
every one of them is an A6.14/A6.9 item:

    HartMemRun.v    A6.14 — the user tier
    HartSMem.v      A6.14 — the S-mode data nodes
    WpMmodeStore.v  A6.14 — M-mode stores (check the solo-era shape first)
    KptTree.v       A6.14 — the PT-slot phys↔ctx pair
    WpUart.v        A6.9  — the DMA lease has no ledger residue

M1 is now COMPLETE except for the deliberately-raw tiers
(`↦ₓ`/`↦ᵣ`/`↦ₚ`/`↦ₛ` and the four A6.14 members' own resources).

### A6.16 THE LEDGER HAS A PHYSICAL TIER — `ctx_store_ok` IS LANDED, AND IT
### CHANGES WHAT A6.9 AND A6.14 SAY (2026-08-26, the A6.14 tranche)

**THE GATE IS IN, AND IT IS STATED AT THE PHYSICAL BYTE.**  Porting
`TsoCtxTwin2.twin_store_ok` to the surface types turned up the one thing
the tranche's plan did not name, and it is what the whole A6.14 class was
stuck on:

> **ALL FIVE MEMBERS ARE PHYSICAL, AND THE FLIP ONLY BUILT THE VA TOWER.**
> `HartMemRun.bytes_own` is a `gmap Arch.pa`; `WpMmodeStore` and `KptTree`
> hold `↦ₚ₈`; `WpUart`'s lease is a `phys_map`; `HartSMem`'s data nodes
> take a `pa`.  `ctx_pointsto` is keyed by VA and carries `mem_pointsto`'s
> kernel-mapping plumbing, so "make `bytes_own` context-indexed" (A6.12's
> shape) is not even type-correct without an identity-mapping assumption
> the user tier does not have.

So `TsoCtx.v` gained the family the machine actually works over:

    ctx_phys_pointsto ξ a dq v  :=  ∃ t, phys_pointsto a dq v ∗
                                      a ↪[ts_name]{dq} t ∗
                                      (llb (ctx_bound_name ξ) t
                                       ∨ (t,a) ↪[ctx_dirty_name ξ]{dq} ())

— `ctx_pointsto`'s body with the VA plumbing stripped off, SEALED for
exactly `ctx_pointsto`'s reason (a permeable seal lets ctx↔raw cross by δ;
the rehearsal measured that), plus the 8-byte tower
`ctx_phys_word_pointsto` (unsealed, like `ctx_word_pointsto`: a tower over
a sealed byte leaks nothing).  **It is not a new tier**:

    ctx_pointsto_phys : ctx_pointsto ξ va dq v ⊣⊢
      ∃ ppn, kmap_at (svpn_of va) ppn KP_rw ∗ ⌜canonical⌝ ∗ ⌜ktier_pin⌝ ∗
             ctx_phys_pointsto ξ (pa_of ppn va) dq v

The VA family IS the kmap claim over this one, both directions, so the
gates are stated ONCE, physically, and the VA forms are corollaries.

**THE GATES, all proven and green:**

    ctx_store_ok        (g g' : gstate) ξ (Pold Pnew : gmap Arch.pa (bv 8)) :
      dom Pold = dom Pnew →
      g'.(gimg) = g.(gimg) →
      g'.(glog) = g.(glog) ++ [PWMsg Pnew (hart_agent cpu_id)] →
      g'.(gmem) = Pnew ∪ g.(gmem) →
      (∀ c, g'.(gtv) c = g.(gtv) c) →
      gen_heap_interp g.(gmem) -∗ tso_interp_at riscv_eraGS g -∗
      own_context ξ -∗
      ([∗ map] a ↦ v ∈ Pold, ctx_phys_pointsto ξ a (DfracOwn 1) v) ==∗
      gen_heap_interp g'.(gmem) ∗ tso_interp_at riscv_eraGS g' ∗
      own_context ξ ∗
      ([∗ map] a ↦ v ∈ Pnew, ctx_phys_pointsto ξ a (DfracOwn 1) v)

    ctx_store_win_ok    — the same at the leaf's shape: the arm's own
                          `write_bytes g.(gmem) pa n vnew`, the arm's own
                          `PWMsg (snap_of pa n vnew) (hart_agent cpu_id)`,
                          and a byte WINDOW on both sides.
    ctx_phys_load_ok       — `ctx_load_ok` without the VA plumbing; PURE
                             conclusion, so nothing is consumed.
    ctx_phys_load_bytes_ok — the window form, exactly
                             `HartEvents.wp_hart_ram_read_plain`'s
                             `Mobl_ram_plain` obligation.
    ctx_phys_win_map       — the leaf's byte LIST and the message's byte
                             MAP are one resource.

**FOUR DESIGN POINTS WORTH KEEPING.**

1. **THE MAP FORM IS THE PRIMITIVE, AND `write_bytes_union` IS WHY.**  A
   window store is ONE append covering n bytes, so a fold of a byte gate
   would be a different machine (n messages).  Stating the gate over a
   footprint MAP `Pnew` with `gmem' = Pnew ∪ gmem` makes it match
   `TsoMemPa.write_bytes_union` (`write_bytes m pa n v = snap_of pa n v ∪ m`)
   character for character — the payload ruling of §1 paying off a second
   time — and needs no address-distinctness anywhere in the proof.
2. **DISTINCTNESS IS NEEDED ONLY AT THE LIST↔MAP BRIDGE**, and it is free:
   `pa_add` is injective in its `nat` index.  `VirtioQueue.pa_add_inj` is
   the fact but that file sits far above the kit, so the five short lemmas
   are re-proven `Local` in `TsoCtx.v` (`tso_pa_add_inj` and friends).
3. **THE POST-STATE IS GIVEN BY FIELD EQUATIONS, NOT BUILT.**  Only the
   four fields `tso_interp_at` reads are constrained, so a leaf that
   already has the machine's successor state applies the gate with no
   `gs_of` round trip on the way out.
4. **A PLAIN STORE MOVES EXACTLY ONE VIEW, AND IT IS NOT THE AUTHOR'S.**
   The harts keep theirs (store buffering, §2); every BUS-MASTER agent is
   pinned to the top (RULING 2), so the append carries the disk's view
   with it and the gate pays one monotone `view_auth_update`.  This is the
   step the `gtv`-only reading of "the view does not move" misses.

**WHAT THIS REPAIRS.**

- **A6.9's consequence 1 — "the phys tier cannot STORE either" — was
  right about the ELEMENTS and wrong about the conclusion.**  A store's
  `Wobl_ram` owes the γts update, which needs the timestamp elements; it
  does NOT need the VA plumbing.  A tier that carries the elements can
  store.  Ruling 6's "phys stays RAW" therefore splits: `↦ₚ` stays raw
  (image bytes, pristine-rescued, the DMA window's flat half), and the
  A6.14 members move to `ctx_phys_pointsto`, which is the SAME tier with
  its ledger residue kept.
- **A6.14's `KptTree` entry is CLOSED, and its "the residue trick fails"
  reasoning is superseded.**  The reasoning was correct — a residue split
  goes stale because the leaf STORES the slot — and beside the point: the
  round trip never has to leave the ledger.  At the node's own identity
  mapping (`pa_of b a = a`, from `pt_node_claim`) the VA family and the
  physical family are the SAME resource under a persistent `kmap_at`, so
  `pt_slot_phys_to_mem` / `pt_slot_mem_to_phys` are now an ISOMORPHISM
  (`ctx_pointsto_of_phys` / `ctx_pointsto_to_phys`), lossless in both
  directions, and `KptTree.v` is **GREEN** with its `TsoCtxShim` import
  deleted.  CASCADE, deliberate: `PtTree.pt_page_own` holds its 512 slots
  at `↦ₚ₈` and must move to `ctx_phys_word_pointsto`, and so must the ~10
  `Proof*` walk files that thread it (`ProofFreewalk`, `ProofCopyout`,
  `ProofIsmapped`, `ProofUvmcopy`, `ProofWalkaddr`, `ProofWalkNoalloc`,
  …).  `PtTree.v` does not import `TsoCtx` today, so that is a section
  binder plus the A6.12 same-name move.

**THREE OF THE FOUR A6.14 MEMBERS WENT GREEN ON THIS GATE.**

- **`KptTree` — GREEN** (above): the slot crossing is an isomorphism.
- **`WpMmodeStore` — GREEN.**  `↦ₚ₈` → `ctx_phys_word_pointsto` in
  `wp_store_gpr` / `wp_store_gpr_tor` / `wp_csdsp_gpr_tor`, plus
  `own_context cur_ctx` in and out.  The obligation is discharged by a new
  **`HartMStore.wobl_ram_ctx`** — "[`wobl_ram`] says WHAT is owed; this
  says WHO can pay" — which is the one place A6.1a's bridge is paid TWICE,
  once in each direction (`tso_interp_of` → `gs_of` → gate → back), and
  the reason the gate's field-equation form matters: nothing has to be
  rebuilt, only the pin re-established at the moved view.  See A6.17 for
  the ruling this settles.
- **`HartMemRun` — GREEN, and it is the whole user tier.**
  `bytes_own mm := [∗ map] a ↦ b ∈ mm, ctx_phys_pointsto XI a (DfracOwn 1) b`
  — same name, same arity, one ambient `CurCtx` binder — plus
  `own_context` threaded through `swp_hmrun` and `swp_hmrun_of_exec`.
  Three findings worth keeping:
  1. **The walker's own resource IS a map**, so `ctx_store_ok`'s map form
     applies with no window bridge at all — via the new
     **`ctx_store_sub_ok`** (the writer owns MORE than it writes; the
     split is `Pold := mm ∩ Pnew`, stdpp's intersection keeping the LEFT,
     i.e. OLD, values, and the rejoined map is `Pnew ∪ mm`, which IS
     `write_bytes mm pa n v`).
  2. **The read arm splits THREE ways in the proof**, not two: exclusive
     (flat, RULING 4), `ak_strong` (the FETCH — RULING 1's flat arm,
     `bytes_own_read` verbatim through `_forget`), and plain (the Ztso
     arm, `bytes_own_tso_read`).  `hmrun` does not distinguish them, so
     the split is a `destruct (ak_strong …)` inside the RAM-read case.
  3. **A LATENT BUG THE FLIP EXPOSED, worth its own line:**
     `HartMemRun.v` Required `TsoCtx` at line 843, HALFWAY DOWN, while its
     sections at lines 187 and 1753 write `` `{XI : CurCtx} ``.  With the
     class not yet in scope, implicit generalisation invented a fresh
     `CurCtx : Type` VARIABLE and `XI` was a dummy — the binders were
     silent no-ops.  Moving the `Require Import` to the top is the fix.
     **`grep -n 'Require Import TsoCtx' *.v` against the line number of
     the first `` `{XI : CurCtx} `` is a cheap audit for the same defect
     elsewhere**, and the error it produces when it finally bites names
     neither file (`Could not find an instance for "TsoCtx.CurCtx"`).
- **`WpUart` — STILL RED, and it is still A6.9's entry.**  The gate does
  not reach it: `ctx_store_ok` is stated at `hart_agent cpu_id` and would
  need its author generalised to an `agent` parameter, but that is the
  easy half.  The hard half is unchanged — the lease holds `phys_map`,
  raw gen_heap bytes with no timestamp elements, so the DMA completion
  arm has no payer.  The fix is the lease-as-parked-context restructuring
  A6.9 spells out; four of `disk_step`'s six arms hand the bundle straight
  back (`tso_interp_of_disk_idle`) and only the completion arm is open.

### A6.17 THE `WpMmodeStore` SOLO-ERA QUESTION, MEASURED — SOLO-ERA IS
### REFUTED, AND THE EXPENSIVE HALF OF THE CTX SHAPE IS ALREADY PAID

A6.14 ruling 4 asked for this measurement before either shape is built.
Here it is.

**THE STORES, exhaustively.**  Three leaves (`wp_store_gpr`,
`wp_store_gpr_tor`, `wp_csdsp_gpr_tor`) and FOUR call sites in the whole
tree: `WpStartNew.v:1133`/`:1146` and `WpTimerinit.v:363`/`:378`.
`VcGen.v`'s mention of `wp_store_gpr` is a header comment, not a use.
Every one of the four is a `c.sdsp` of `ra`/`s0` to the hart's own M-mode
boot stack — `start()`'s and `timerinit()`'s prologue saves.

**SOLO-ERA IS FALSE HERE.**  All eight harts enter `_entry` and run
`start()`; `SystemAdequacy` mints eight contexts and runs eight harts'
WPs side by side.  `TsoMemPa.all_own h log` fails at the second hart's
first prologue save.  (A6.4 already recorded that no `gstate`-level
producer for `all_own` is built and that the disk agent breaks it for any
hart anyway; this adds that the M-mode bracket is not solo even before
the disk exists.)  **So the solo-era shape is not available, and the
ruling is the ctx conversion.**

**AND THE HALF A6.12 CALLED "THE REAL COST" IS ALREADY PAID.**
`own_context cur_ctx` is in hand throughout the M-mode bracket:
`BootChain.boot_entry_bridge` TAKES it as a premise (its header explains
why: taken, not minted, so main's cone stays context-implicit) before it
applies `Entry.wp_entry_boot`, and only hands it on to
`BootBridge.boot_bridge` at the far end.  There is exactly ONE token,
held across the whole bracket — no `iApply` breakage of the kind A6.12
budgeted for the user tier.  What it costs is threading that one token
down through `wp_entry_boot` → `WpStartNew`'s and `WpTimerinit`'s lemmas
→ the three store leaves: four statements.

**WHAT IS NOT FREE EITHER WAY, and it is the real bill.**  The M-mode
boot stack's bytes arrive as `stack_own_phys` — RAW, no timestamp
elements — so the ledger residue for them has to be minted at ADEQUACY
whichever shape is chosen.  That is why the solo-era shape would have
bought nothing even if it were true: it removes the bit, not the element.

**A THIRD SHAPE WAS FOUND AND REJECTED, worth recording because it is
sound and will be right somewhere else.**  A store gate needs the
elements but NOT a context: dropping the clean/dirty bit gives a
"write-only ledger byte" (`phys_pointsto a dq v ∗ ∃ t, a ↪[ts_name]{dq} t`)
that can be stored to for ever and licenses no load.  It fits these
stores exactly — the M-mode prologue saves are DEAD (A6.10 already
records that M-mode's only 8-byte data load in this tree is `entry`'s
`ld sp, stack0`, a link-time constant).  Rejected because it is strictly
more work here: it is a NEW resource with no producer, while
`own_context` already exists and already arrives, and the resulting byte
is weaker (unloadable).  Keep it in mind for a genuinely write-only
region.

### A6.18 THE Σ-SEAM STOP: `HartSMem`'s DISCHARGE POINT IS `WpSconfMem`'s
### `wordw_pointsto`, AND IT IS A FORCED AMENDMENT TO §0.10′ RULING 4

Reported rather than changed, per the tranche's own stop rule.

**THE CHAIN.**  `HartSMem`'s S-mode data nodes (`swp_read_ram_node1/2/4/8`
and their `_ex` / `_w` / `_w_ex` forms, all driven by the `node_read`
tactic) read `Read_plain`, so post-A6.7(B) they take
`wp_hart_ram_read_plain` and owe `Mobl_ram_plain` — a
`tso_read_bytes img log h tv' pa n w` fact at EVERY admissible view, in
place of today's `mem_bytes_at σ pa n bytes` against the flat cache.
`HartSMem` has 28 internal uses and exactly ONE external
(`WpSconfMem.v:503`, `swp_read_ram_node_w_ex`), and that is where the
obligation is discharged: `WpSconfMem.v:521–534` opens the caller's
atomic update, unfolds `wordw_pointsto`, and closes with `s_mem_chunk`
against `sigma.(mem)`.  A flat cell cannot give the new fact (A6.7(B)'s
measurement), so **the datum has to carry the ledger residue.**

**THE EXACT STATEMENTS.**  The datum is

```coq
  (* WpSconfMem.v:104 *)
  Definition wordw_pointsto `{KTR : !CurKtier} (width : Z) (a : Arch.pa)
      (dq : dfrac) (w : mword (8*width)) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) width = true⌝ ∗
     [∗ list] j ∈ seq 0 (Z.to_nat width),
        mem_pointsto (pa_add a j) dq (nth_byte w j))%I.
```

and it appears in the two ATOMIC-UPDATE roots

```coq
  wp_load_s_sconf_au  … (WpSconfMem.v:336)
    (|={⊤ ∖ ↑minstretN, Em}=> ∃ v : mword (8*width),
       wordw_pointsto (KTR := ktd) width ea dqm v ∗
       (wordw_pointsto (KTR := ktd) width ea dqm v
          ={Em, ⊤ ∖ ↑minstretN}=∗ Ψ v)) -∗ …

  wp_store_s_sconf_au … (WpSconfMem.v:1019)
    (|={⊤ ∖ ↑minstretN, Em}=> ∃ vold : mword (8*width),
       wordw_pointsto (KTR := ktd) width ea (DfracOwn 1) vold ∗
       (wordw_pointsto (KTR := ktd) width ea (DfracOwn 1) sv
          ={Em, ⊤ ∖ ↑minstretN}=∗ Ψ)) -∗ …
```

plus the three `_gen*` wrappers (`:602`, `:662`, `:700`), the store's
`wp_store_s_sconf_gen` (`:1243`), and every S-mode instruction leaf built
on them — `wp_lbu/lwu/cld/ld/clw/lw_s_sconf`, `wp_csd/sd/csw/sw_s_sconf`,
`wp_sb_s_sconf`, `wp_cldsp/csdsp_s_sconf`, `wp_sd_zero/sw_zero_s_sconf`
— about twenty exported statements, the whole S-mode load/store leaf
family.  `wordw_claim`, `wordw1_byte` and `wordw8_ctx` ride along.

**THE SHAPE THAT COSTS LEAST, and why the amendment is not as bad as it
looks.**

1. **`own_context` IS ALREADY THERE.**  Every one of those statements
   takes `sie_cap_gpr kt m n b p`, and §0.13′ records that
   `own_context cur_ctx` is a conjunct of `IntrDefs.sie_cap` — "a thread's
   AMBIENT context is its identity".  So the A6.14 premise costs nothing
   here: the token arrives with the capability the leaf already takes.
2. **THE DATUM MOVES IN PLACE, SAME NAME AND SAME ARITY.**  Replace
   `mem_pointsto` by `ctx_pointsto cur_ctx` in the body and give the
   definition an ambient `` `{XI : CurCtx} `` binder.  Every one of the
   ~20 exported statements is then TEXTUALLY UNCHANGED, `wordw8_ctx`
   collapses to `reflexivity`, and the hand-written continuation adapters
   §0.9′ built around it DIE — the same deletion `PageFields`/`ByteBuf`
   got from M1 stage 2, for the same reason.
3. **THE STORE HALF IS THE HIDDEN HALF.**  `wp_store_s_sconf_au` and its
   eight instruction leaves are S-mode's stores of ALL kernel data, and
   they owe `Wobl_ram` too — today `wordw_pointsto_write_c`
   (`WpSconfMem.v:199`) discharges only the gen_heap update.  So
   **`WpSconfMem` is an unlisted sixth A6.14 member**, hidden until now
   only because `HartSMem.vo` is stale and the file has never been built
   post-flip.

**WHAT IT COSTS ELSEWHERE.**  `grep wordw_pointsto` outside the file
names `WpSconfLock.v:435` (which already annotates the AU's datum as "the
RAW window … deliberately raw"), `ProofBrelse.v:203` and
`ProofVirtioDiskIntr.v:1043`; every other consumer supplies the datum
through the `↦₈` wrappers, which are ALREADY context-indexed — which is
itself the evidence that the raw spelling is the odd one out now.

**RATIFIED (owner, 2026-08-26), and recorded as the forced amendment to
§0.8′ ruling 6 / §0.10′ ruling 4 for the S-mode data tier — same family as
A6.14.**  The BODY flips to `ctx_pointsto cur_ctx` at the section's ambient
`XI`; every exported statement stays TEXTUALLY UNCHANGED, and that textual
invariance IS the acceptance test.  **It held**: the flip is three lines in
the definition, `wordw8_ctx` collapsed to its own body (no shim, no
`setoid_rewrite`, no continuation adapter), `mem_pointsto_claim` swapped
one shim name for `ctx_pointsto_forget`, and `wordw_claim_of` simply
dropped a conversion line.  No exported statement changed spelling.

**CAVEAT, stated plainly: `WpSconfMem.v` HAS NOT BEEN COMPILED.**  It sits
transitively above `HartSKpt` in the dependency cone, and `HartSKpt` is
blocked on A6.21's decision — so the acceptance test above is verified at
the STATEMENT level (nothing changed spelling, and the shim uses are gone
by inspection), not by the build.  The first thing to do after A6.21 lands
is `make WpSconfMem.vo` and re-check.

**AND `HartSMem` IS GREEN AGAINST IT** (the discharge point now exists).
The port is smaller than A6.14 predicted, because of one measurement:

> **THE EXCLUSIVE READ'S OBLIGATION DOES NOT CHANGE.**  RULING 4 says an
> exclusive read reads at the log top, i.e. off the FLAT cache — so
> `swp_read_ram_node4_racq`/`_ex` still owe a `mem_bytes_at` fact and
> nothing else, and the node simply FRAMES the bundle the rule hands it
> (dropping the receipt, which the leaf mints where it is wanted).  Only
> the PLAIN read and the STORES changed shape.

What moved: the three node tactics, the four `swp_read_ram_node*` and their
four `_ex` twins (to `swp_hart_ram_read_plain` and a `tso_read_bytes`
obligation), the four `swp_write_ram_node*` (the append), the conditional
write node and the three AMOSWAP engines' write-continuation premises (the
append at `S (length log)` — an AMO takes the view PAST its own append,
which is what makes it an acquire), and the `Mobl_ram` / `Wobl_ram` /
`Mobl_ram_ex` abbreviations.  **Everything above them is abstract over the
obligation and was untouched** — which is exactly the property that made
"28 uses inside, ONE outside" true in the first place.

TWO Ltac TRAPS, recorded because each cost a round: an identifier written
inside an `Ltac` body is resolved as a TERM at definition time (so
`iMod ("H" $! _ img log …)` fails with "the reference img was not found" —
use `$! _ _ _ _ _`), and a name bound by `let … := fresh` shadows the Coq
hypothesis a `"[%Hb …]"` intro pattern introduces (so `exact Hb` picks up
the Ltac variable).  Taking the pure fact as an Iris hypothesis
(`"[Hb Hcl]"` + `iExact "Hb"`) sidesteps both.

**THE ORIGINAL RULING TEXT, kept.**  §0.10′ ruling 4 / §0.8′ ruling 6 declare
`WpSconfMem.wordw_pointsto` deliberately RAW.  That ruling was made in
the CUTOVER REHEARSAL, when the only cost of a ctx datum was crossing a
seal for nothing.  Post-flip the ctx datum is the only one that can
discharge either obligation, so the ruling has to be amended exactly the
way A6.14 amended ruling 6.  **`HartSMem` cannot be closed until it is**
— its 28 internal uses can be ported and the obligation threaded, but it
would land at `WpSconfMem` with no payer.

### A6.19 THE FRONTIER AFTER THE A6.14 TRANCHE — THE WALL MOVED, AND THE
### GREEN COUNT WENT DOWN BECAUSE OF IT

**Two identical full `-k` sweeps.  ELEVEN red files, 643 of 1330
fresh-green (down from 1044).**  The drop is the tranche working, not
breaking, and it is worth stating plainly because the headline number
reads backwards:

> A6.12 said "the whole user tier waits on ONE decision".  Making that
> decision does not green the tier — it moves the wall from ONE file to
> that file's ~400-file cone, which then has to convert.  `bytes_own`
> going context-indexed and `PtBytes.phys_word_bytes_own_full` moving to
> the ledger word are consumed by `UserMem*`, `WpUmode*` and the `Proof*`
> syscall files, so ~400 files that had been sitting ABOVE the old
> frontier — never once compiled against a ctx `bytes_own` — are now
> behind it.  The 1044 was measured with the user tier's decision still
> unmade.

    HartSMem.v      A6.18 — Σ-SEAM STOP, reported not changed
    WpUart.v        A6.9  — the DMA lease still has no ledger residue
    HartSKpt.v      NEW   — the S-mode kernel-PT walk: the A/D write-back's
                            [xread_obl_ex]/[wpte_obl_at] pair.  Surfaced
                            when KptTree went green; an A6.14-class store.
    KstackOwn.v     NEW   — `kstack_byte_rekey` / `kstack_word_rekey`, the
                            KT0↔KT1 rekey.  Same A6.16 shape as KptTree
                            (`ctx_pointsto_phys` is the general bridge and
                            needs no new kit), but the word half also has
                            to leave the RAW `word_pointsto` tower.
    ProcPtOwn.v     NEW   — `page_own` ↔ `phys_page_own` at an identity
                            mapping; A6.16 verbatim.
    UserBytes.v     NEW   — `PtBytes.phys_word_bytes_own_full`'s one
                            consumer; follows it to the ledger word.
    UmodeMem.v      NEW   — the U-mode data tier, same class.
    PtWalkCert.v    NEW   — the walk certificate over `bytes_own`.
    HartStepFull.v  NEW   — `swp_hmrun_of_exec` at `bytes_own ∅`: the walk
                            touches no memory, but the rule wants the token
                            anyway.  A6.12's predicted `own_context`
                            threading, first instance.
    UserTrap.v      NEW   — the same, at the trap handler's `bytes_own ∅`.
    WpTimerinit.v   NEW   — A6.17's cascade: the ctx word + the token, from
                            `BootChain.boot_entry_bridge` down.

(`PtBytes.v` was on this list and is now GREEN: `phys_word_bytes_own_full`
restated at `ctx_phys_word_pointsto`, and its three sections given the
ambient `CurCtx` binder — the mechanical half of the class below.)

**THE TWO CLASSES THE NEW NINE SPLIT INTO**, so the next session does not
re-derive them:

- **(A6.16 verbatim)** `HartSKpt`, `KstackOwn`, `ProcPtOwn`, `UserBytes`,
  `UmodeMem`, `PtWalkCert` —
  a raw physical resource meeting a ctx one at an identity mapping.  The
  fix is `TsoCtx.ctx_pointsto_phys` (the general `⊣⊢`) or its two
  identity-mapped corollaries; NO new kit is needed.  What is needed is
  deciding, per file, which tier its OWNER holds (`pt_page_own`'s 512
  slots, `phys_page_own`'s 4096 bytes, the kernel stack's words) — the
  same "flip the file that OWNS the cells" rule A6.15 recorded.
- **(the `own_context` threading)** `HartStepFull`, `UserTrap`,
  `WpTimerinit` — the token has to reach the leaf.  It EXISTS at every one
  of these (it is a conjunct of `IntrDefs.sie_cap`, and
  `BootChain.boot_entry_bridge` holds it across the whole M-mode
  bracket); what is missing is a premise on the intermediate statements.
  Mechanical, wide, and the cost A6.12 budgeted for.

### A6.20 THE WRITE-ONLY LEDGER BYTE HAS A CONSUMER AFTER ALL, AND IT IS
### THE PAGE TABLE (the A6.18 tranche; kit landed)

A6.17 measured a third store shape at `WpMmodeStore` and rejected it there:
a store's four ghost steps need the timestamp ELEMENTS but **not a
context** — the clean/dirty bit is what licenses a later plain LOAD — so
dropping the bit gives a resource that can be stored to for ever and
licenses no load.  It was rejected because `own_context` already arrives
at the M-mode bracket and a loadable byte is strictly stronger.

**At the KERNEL PAGE TABLE the judgement reverses, and it is forced.**
`KptShare.kpt_body` holds `ptree_own 2 (DfracOwn 1) t` inside
`inv kptN`, a BARE invariant shared by every S-mode thread.  An invariant
body may not name a context (§0.8′ ruling 2), so its slots cannot be
`ctx_phys_pointsto`.  And they do not need to be:

> **a PTE is read at `Read_ttw` — RULING 1's FLAT arm — so no load license
> is ever wanted, while the Svadu A/D write-back is a real store and owes
> the append.**  Context-free ledger is the only sound shape there, and it
> is also the cheapest.

Landed in `TsoCtx.v` (all proven):

    phys_ledger a dq v := ∃ t, phys_pointsto a dq v ∗ a ↪[ts_name]{dq} t
                                                    (* sealed *)
    ctx_phys_pointsto_ledger : ctx_phys_pointsto ξ a dq v ⊢ phys_ledger a dq v
                               (* the bit is what is dropped, and with it
                                  the load licence, nothing else *)
    ledger_store_ok      — THREE of the four ghost steps (γts to the new
                           top, γlogm persist, the mono_nat bump) and NO
                           dirty-set insert, because there is no context to
                           insert into.  No [own_context] premise anywhere.
    ledger_store_win_ok / phys_ledger_win_map — the window forms.

The per-byte loop is strictly simpler than `ctx_store_bytes`: two
authorities instead of three, and no freshness obligation.

### A6.21 `pt_page_own`'s TIER IS NOT UNIFORM — THE KERNEL PT AND THE USER
### PTs WANT DIFFERENT LEDGERS (design point; NOT implemented)

`PtTree.pt_page_own` holds a node's 512 slots and serves BOTH:

  - the **kernel** page table, inside `KptShare.kpt_inv` — shared across
    contexts, read by the HARDWARE walker at `Read_ttw` (flat), written by
    the A/D write-back ⇒ **`phys_ledger`** (A6.20);
  - the **user** page tables, owned by a thread through
    `walk`/`freewalk`/`copyout` — read by SOFTWARE at `Read_plain` through
    `WpSconfMem.wordw_pointsto`, which needs a plain-load licence ⇒
    **`ctx_phys_word_pointsto`** (A6.16, and it is what `KptTree`'s now-green
    slot isomorphism hands back).

One tier cannot serve both: the context-free byte licenses no load, and
the ctx byte cannot live in a bare `inv`.  So `pt_page_own` has to be
PARAMETERISED — the natural shape is an `option CtxId` index (`None` = the
context-free ledger, `Some ξ` = the registered one), sound because
`ctx_phys_pointsto ξ … ⊢ phys_ledger …` is proven, so `Some ξ` is strictly
stronger and the kernel invariant simply takes `None`.

**DISPOSITION (owner, 2026-08-26): RATIFIED and LANDED in `PtTree.v`.**
`Section PtTreeIris` gained `Context (PTT : option CtxId)` and the slot
family

    pt_slot_own a dq w := match PTT with
                          | None    => phys_ledger_word a dq w
                          | Some xi => ctx_phys_word_pointsto xi a dq w
                          end

with `pt_slot_own_forget` (BOTH tiers forget to the raw physical word,
which is all the pure memory facts ever wanted of a slot — this is why the
index costs the walk lane nothing) and the two `reflexivity` equations
`pt_slot_own_Some` / `pt_slot_own_None` (needed because `iFrame` matches
SYNTACTICALLY and will not iota-reduce a slot on its own).

**THREE REALISATION NOTES, each of which saved a file-wide wave:**

1. **The old names survive as NOTATIONS, not definitions.**
   `Notation pt_page_own := (pt_page_own_at (Some TsoCtx.cur_ctx))` — and
   likewise `ptree_own`, `pt_kids_own`, `pt_frame` and the eight
   accessors.  A `Notation` is expanded AT THE USE SITE, so `cur_ctx`
   resolves to the consumer's own ambient instance — the same trick the M1
   flip used for `↦ₘ`.  That is what keeps ~50 consumer files textually
   unchanged where a `Definition` would have changed every arity.
2. **The notation must spell `TsoCtx.cur_ctx` QUALIFIED.**  `PtTree` does
   `Require Import TsoCtx`, which does not re-export; a consumer that only
   `Require`s `PtTree` has the module LOADED but not the names, so an
   unqualified `cur_ctx` in the notation body fails at the use site with
   an error that names neither file.
3. **The slot got its own notation** (`a ↦ₚₜ{dq} w` for the user tier,
   `↦ₖₜ` for the kernel one).  The consumers spelled a slot `a ↦ₚ₈{dq} w`
   — an INFIX — while the tiered slot's head is a PREFIX, so without a
   notation the conversion is a re-parenthesisation of every occurrence
   rather than a token substitution.  (Measured the hard way: a regex over
   the infix form mangled four continuation wands in `PtBuild`.)

`PtTree.v` and `PtBuild.v` are GREEN.  `PtBuild.zero_page_to_node` — the
node builder — now takes CTX bytes and is the file's tier decision in one
line: **a fresh kalloc page is a THREAD's, so a node is built at the user
tier, and installing it in the shared kernel table FORGETS the
registration (`ctx_phys_word_ledger`), which is exactly right — it stops
being any one thread's.**

**This was `HartSKpt`'s blocker and it is a design decision, not a repair**,
which is why it is reported rather than improvised.  The chain is
`HartSKpt`'s `iAssert`-built `Hrdx`/`Hwr` seams → `PtTreeAdue`'s
`xread_obl_ex`/`wpte_obl_at` (already ported, already bundle-carrying) →
`KptShare.kpt_body` → `PtTree.pt_page_own`.  Note the read seams need only
FRAMING (an exclusive/`Read_ttw` read is flat); only the A/D write-back
needs A6.20's gate.

### A6.22 A WALK THAT OWNS NO BYTES NEEDS NO THREAD IDENTITY — AND THAT IS
### WHAT KEEPS THE REGISTER-ONLY SITES UNCHANGED

A6.12 budgeted the `own_context` premise as "the real cost: it breaks
every `iApply`".  Most of that cost is avoidable, and the reason is worth
stating as a rule:

> `swp_hmrun_of_exec` takes the token unconditionally because its RAM arms
> cannot know IN ADVANCE that they will not fire.  **At `mm = ∅` they
> cannot fire at all** — the walker's own map answers nothing, so every
> memory arm is refuted by the walk equation itself, and `bytes_own ∅` is
> `emp` on both sides.  So the token can be MINTED inside the lemma and
> dropped: `TsoCtx.own_context_boot` is an UNCONDITIONAL mint, and the
> token never escapes, so no identity is claimed anywhere and the
> one-token-per-hart discipline is untouched.

`HartMemRun.swp_hmrun_of_exec_reg` is that form.  With it,
**`HartStepFull` and `UserTrap` are GREEN with ZERO statement changes** —
`swp_try_step_waiting`, `swp_exec_step_waiting`, `UserStep` and
`WpSmodeWfi` never learn that anything happened.  Without it, the premise
would have had to be threaded through four statements and their cones for
a resource none of them uses.

**THE RULE TO CARRY:** before threading `own_context` anywhere, ask
whether the site owns bytes at all.  The register-only walks (the WFI
loop, the waiting step, the trap prelude, the CSR windows) do not, and
they are a large fraction of the ~60 `bytes_own` consumers.

### A6.23 THE FRONTIER AFTER THE A6.18 TRANCHE

**Two identical full `-k` sweeps** (the second compiled exactly the eight
red retries and nothing else).  **EIGHT red files, 646 of 1330
fresh-green.**  Green this tranche: `HartSMem` (the Σ-seam's own file),
`HartStepFull`, `UserTrap`, `PtBytes` — and `WpSconfMem` is now behind
`HartSKpt` rather than blocked on a ruling.

    HartSKpt.v      A6.21 — BLOCKED ON A DECISION (pt_page_own's tier)
    UserBytes.v     A6.21 — same decision, downstream
    UmodeMem.v      A6.21 — same decision, downstream
    PtWalkCert.v    A6.21 — same decision, downstream
    ProcPtOwn.v     A6.16 — page_own ↔ phys_page_own at an identity map
    KstackOwn.v     A6.16 — the KT0↔KT1 kernel-stack rekey; the BYTE half
                            is [ctx_pointsto_phys] verbatim, the WORD half
                            also has to leave the raw [word_pointsto] tower
    WpTimerinit.v   A6.17 — the M-mode boot-stack cascade: the ctx word AND
                            the token, threaded from
                            [BootChain.boot_entry_bridge] down through
                            [wp_entry_boot] / [WpStartNew] / [WpTimerinit]
    WpUart.v        A6.9  — the DMA lease (unchanged; the one genuine
                            design item left, and it now has a gate shape
                            to be written against: A6.20's context-free
                            store is what a lease reclaim wants, since the
                            lease is invariant-owned too)

**FOUR OF THE EIGHT ARE ONE DECISION.**  `HartSKpt`, `UserBytes`,
`UmodeMem` and `PtWalkCert` all bottom out in `PtTree.pt_page_own`, and
A6.21 is the decision they wait on.  That is the honest shape of the
remaining frontier: it is no longer a list of repairs, it is one
parameterisation plus two small conversions plus one design item.

### A6.24 THE A/D WRITE-BACK'S CORE IS TIER-GENERIC, SO IT MUST TAKE ITS
### PAYER RATHER THAN BE ONE — the new design class the A6.21 wave surfaced
### (CHARACTERISED, NOT IMPLEMENTED)

With A6.21 landed the wave runs clean down to ONE place, and it is a design
point rather than a repair.

**THE FACT.**  `KptTree.ptree_translateAddr_own` is the shared translation
core.  It has exactly two callers — `KptShare.v:343` (the KERNEL page
table, inside `kpt_inv`) and `UptTree.v:757` (a USER page table) — so it
is used at BOTH of A6.21's tiers.  And it performs the Svadu A/D
write-back itself, at `KptTree.v:1165`, with `phys_word_pointsto_write`
against `gen_heap` alone.  Post-flip that store owes the append, and the
lemma is at the wrong ALTITUDE to pay it: its statement is
`reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ … ==∗ …` — an
`mstate`-level fact with **no memory-model bundle anywhere in it**.

**WHY IT CANNOT SIMPLY GAIN THE BUNDLE.**  The two tiers pay differently:

  - kernel (`PTT = None`): `TsoCtx.ledger_store_ok` — no context, no token;
  - user (`PTT = Some ξ`): `TsoCtx.ctx_store_win_ok` — needs
    `own_context ξ`, which the translating thread does have (it is its own
    page table) but which the kernel caller has no business supplying.

A single bundle-carrying statement would have to demand the token
unconditionally, and the kernel caller cannot honour it — it holds an
invariant, not an identity.

**THE SHAPE THAT WORKS.**  The core should not pay the append; it should
**take the payer**, as a threaded premise — the move A6.9's consequence 1
already forced for `HartPilot`'s pilot rule ("its store's append is now a
THREADED premise, not a discharged one").  Each caller then supplies its
own tier's gate: `KptShare` supplies `ledger_store_ok`, `UptTree` supplies
`ctx_store_win_ok` with the thread's token.

> **RULING (owner, 2026-08-26): RATIFIED, and this is the amendment's
> principle, kept verbatim —**
>
> > **the index says which ledger a slot is in; the payer says who may
> > move it.**

**AND `HartPilot`'s PREMISE CANNOT BE COPIED VERBATIM — measured, and it
would have been the obvious wrong turn.**  `wp_pilot_started_store`'s
threaded premise takes ONLY the bundle:

    (∀ σw img log tv V, ⌜V (hart_agent cpu_id) = tv⌝ -∗
       tso_interp_of … img σw.(mem) log V ==∗
       tso_interp_of … img (write_bytes …) (log ++ [PWMsg …]) (vstep …))

with the gen_heap update done by the rule itself.  **No gate can pay
that.**  `ctx_store_ok` and `ledger_store_ok` both take `gen_heap_interp`
AND `tso_interp_at` TOGETHER, because the interp's own tie
(`TM !! a = Some t → ∃ v, gmem !! a = Some v ∧ latest img log a t v`)
relates the two — a gate that moved the ledger without the flat cell would
have to break that tie transiently and could not restore it.  `HartPilot`
gets away with it only because its pilot lemmas have NO consumers (A6.7's
own note); `KptTree`'s premise will have two real ones.

**So the payer premise must take BOTH, and the caller's append currency
must be threaded through it rather than closed over** (a wand that
consumed the caller's bundle could not give it back).  Two parameters:

    (Sto : iProp Σ) (Stoq : mword 64 -> iProp Σ)

    (* the A/D write-back's payer *)
    (∀ wnew : mword 64,
       gen_heap_interp σ.(mem) -∗ Sto -∗
       pt_slot_own PTT (pt_addr0 p1 (svpn_of va)) (DfracOwn 1) p0 ==∗
       gen_heap_interp (write_bytes σ.(mem)
                          (pt_addr0 p1 (svpn_of va)) 8 wnew) ∗
       Stoq wnew ∗
       pt_slot_own PTT (pt_addr0 p1 (svpn_of va)) (DfracOwn 1) wnew)

The kernel caller instantiates `Sto := tso_interp_of … log V` and
`Stoq w := tso_interp_of … (log ++ [PWMsg (snap_of … w) …]) (vstep …)` and
discharges with `ledger_store_ok`; the user caller does the same with
`ctx_store_win_ok` plus its `own_context`.

**THE CONDITIONAL IS ALREADY THERE, AND THAT MAKES THE CONCLUSION CHEAP.**
The proof splits three ways on `ptree_translateAddr_cases`
(`KptTree.v:1124`): **O1** nothing moved, **O2** a TLB fill with the
current leaf, **O3** the Svadu write-back — and ONLY O3 touches memory.
O1 and O2 both report `t' = t`, O3 reports the right disjunct.  So the
resource disjunction the conclusion needs is EXACTLY the pure one the
statement already carries
(`⌜t' = t ∨ ∃ a1 d1, t' = ptree_set_leaf t vpn (pte_set_ad w a1 d1)⌝`):
return `Sto` on the `t' = t` side and `Stoq w'` on the other, tied to the
same disjunct.  **No caller gains a case split it did not already have.**

Cost: one statement change on `ptree_translateAddr_own` (~200 lines with a
delicate case analysis), its two callers, and whatever hands them the
interp (`PtTreeAdue` → `WpSmodePtEngine` → `SmodeCorePt`).

### A6.25 THE FRONTIER AFTER THE A6.21 TRANCHE — THREE FILES, AND ONE OF
### THEM IS THE ONLY REMAINING DESIGN ITEM ON THE PT LANE

**Two identical full `-k` sweeps** (the second compiled exactly the three
red retries and nothing else).  **THREE red files, 630 of 1330
fresh-green** — but see A6.26: a subsequent CLEAN build put the honest
number at **505**, the 630 having been inflated by ~125 `.vo`s that were
green against the pre-A6.21 `PtTree`.  The RED SET is the same either way,
and it is the number that matters here.

    KptTree.v       A6.24 — the A/D write-back's core must TAKE its payer
    WpTimerinit.v   A6.17 — the M-mode boot-stack threading cascade
    WpUart.v        A6.9  — the DMA lease

Green this tranche: `PtTree`, `PtBuild` (the A6.21 parameterisation
itself), and — through the `swp_hmrun_of_exec_reg` form of A6.22 —
`HartStepFull` and `UserTrap`.

**READ THE RED SET CAREFULLY, AND DO NOT MISREAD IT AS I FIRST DID.**
`HartSKpt`, `UserBytes`, `UmodeMem`, `PtWalkCert`, `ProcPtOwn`,
`KstackOwn` and `WpSconfMem` have LEFT THE ERROR LIST WITHOUT BEING
VERIFIED: their `.vo`s are still the stale Aug-25 ones, and they are
simply BEHIND `KptTree` in the dependency DAG, which `make` never reached.
They are neither green nor known-red.  The A6.21 index is what will make
them reachable, but the evidence that it fixes them is not in yet — the
first thing after A6.24 lands is to walk that list and check each.
**A file dropping off a `-k` error list means one of two things, and only
the `.vo` timestamp says which.**

**THE COUNT WENT DOWN AGAIN (646 → 630) AND THE REASON IS THE ABOVE.**
`KptTree` — which HAD been green — is a much deeper node than the files
that left the error list, so its cone (the whole user-PT walk lane and
everything above it, the other seven included) is now the blocked set.
**Red-set size and fresh-green count move in opposite directions whenever
a frontier file is replaced by a deeper one; neither number alone reads
the progress, and the error list alone reads it wrongly.**  The honest
measure here is that the remaining WORK is three named items — one design
decision (A6.24) and two known cascades — with a seven-file verification
pass behind the first of them.

CAVEAT ON THE MEASUREMENT: three sweeps were briefly running CONCURRENTLY
on this tree earlier in the session (a detached `make` outlived the
command that started it).  Concurrent `make -j` on one tree can in
principle leave a half-written `.vo` that is newer than its dependencies
and so never rebuilt.  Sweeps L and M were run singly and agree, and the
files compiled in them load hundreds of `.vo`s without complaint, so the
tree is very likely clean — but a `make clean`-and-rebuild is the only
thing that would prove it, and it has not been done.  **Do not start a
sweep with `&` inside a compound command; use `setsid` and wait on it.**

### A6.26 HANDOFF — WHERE THE NEXT LANE PICKS UP

Written at a clean boundary rather than pushed through, per the owner's
standing instruction.  Nothing below is speculative: every shape named has
either been proven in the kit or measured against the build.

> **THE HYGIENE REBUILD IS DONE, AND IT CORRECTS A NUMBER.**
> `fliptree/iris/*.vo` was deleted wholesale (the model's kept) and ONE
> `make -j12 -k` run from scratch under `setsid`.  Result:
>
> > **505 of 1330 files built from source, and EXACTLY the three expected
> > error files — `KptTree`, `WpTimerinit`, `WpUart` — with nothing else
> > surfacing.**
>
> Two things follow, and the second is the important one.
>
> 1. **The half-written-`.vo` caveat of A6.25 is DISCHARGED.**  505 files
>    compiled from source reproduce the incremental frontier exactly; the
>    concurrent-`make` incident left no corruption.  **AND THE NUMBER IS
>    SELF-VERIFYING:** the log shows 508 files ATTEMPTED, 505 `.vo`s
>    produced, 3 errors — so every file `make` reached is accounted for as
>    green or red, with none silently skipped.  `grep -c 'ROCQ compile'`
>    against `ls *.vo | wc -l` against the error count is the cheapest
>    integrity check on any sweep, and worth running on every one.
> 2. **THE TRUE FRESH-GREEN COUNT IS 505, NOT A6.25's 630.**  The 630 was
>    inflated by ~125 stale-but-valid `.vo`s built while `KptTree` was
>    still green — i.e. against the PRE-A6.21 `PtTree`.  Once `KptTree`
>    is red from the start, its whole cone is unreachable and never gets
>    built at all.  **An incremental fresh-green count silently keeps
>    files that were green against an EARLIER version of a file that is
>    now red; only a clean build tells you how much of the tree the
>    current sources actually prove.**  Read every earlier count in this
>    note with that in mind.
>
> The tree is now in the state that clean build left it: 505 `.vo`s, the
> three red files, and their cones unbuilt.

**THE KIT IS COMPLETE FOR EVERYTHING THAT REMAINS.**  `TsoCtx.v` now
carries, all proven:

    ctx_pointsto / ctx_word{,2,4}_pointsto        the VA ledger (M1)
    ctx_phys_pointsto / ctx_phys_word_pointsto    the PHYSICAL ledger (A6.16)
    phys_ledger / phys_ledger_word                the CONTEXT-FREE ledger (A6.20)
    ctx_pointsto_phys                             VA ⊣⊢ kmap ∗ physical
    ctx_pointsto_{to,of}_phys                     the identity-mapped crossing
    ctx_phys_pointsto_ledger / ctx_phys_word_ledger   registered ⊢ unregistered
    *_forget                                      every tier ⊢ the raw one
    ctx_load_ok / ctx_phys_load_ok / _bytes_ok    the load gates
    pristine_read_{ok,bytes_ok}                   the image-byte gate (A6.10)
    ctx_store_ok / _win_ok / _sub_ok              the store gate, three shapes
    ledger_store_ok / _win_ok                     the context-free store gate
    ctx_phys_win_map / phys_ledger_win_map        list ⊣⊢ the message's map
    hart_view_lb_get / ctx_dom_of_parked          the receipt and the acquire mint

**NO NEW KIT IS NEEDED** for A6.24, A6.17's cascade, or A6.9's lease.  What
remains is threading and two statement changes.

**THE THREE ITEMS, in the owner's order.**

1. **A6.24** — the shape is written out in full in that amendment,
   including the two parameters and why `HartPilot`'s premise cannot be
   copied.  Start at `KptTree.v:1165`.
2. **A6.17's cascade (`WpTimerinit`)** — `wp_csdsp_gpr_tor` now takes
   `ctx_phys_word_pointsto` and `own_context` (A6.17, landed at
   `WpMmodeStore`).  Both have to reach the four M-mode store sites from
   `BootChain.boot_entry_bridge`, which already HOLDS the token across the
   whole M-mode bracket — the threading is through `Entry.wp_entry_boot`,
   `WpStartNew` and `WpTimerinit`, four statements.  The stack bytes' own
   ledger residue is minted at adequacy (A6.17's "real bill").
3. **A6.9's lease (`WpUart`)** — two independent pieces, and the first is
   pure plumbing: `wp_disk_loop` is still written against the PRE-A6.11
   `wp_disk_step` (it destructures `disk_step`'s arms with a post-state
   `m'` where the rule now hands `(d' W log')` plus `⌜disk_step d m d' W⌝`).
   Reshape that first; four of the six arms then close with
   `RiscvExec.tso_interp_of_disk_idle`.  Only the DMA completion arm is the
   real item, and **A6.20 is its shape**: the lease is invariant-owned, so
   it is context-free ledger, and `ledger_store_ok` is the gate — with its
   author generalised from `hart_agent cpu_id` to an `agent` parameter for
   this one caller (a one-line generalisation of the gate; the proof never
   uses the hart-ness).

**THE VERIFICATION LIST BEHIND `KptTree`** (A6.25's correction): once
A6.24 lands, walk these and check each `.vo`, do not infer from the error
list — `HartSKpt`, `UserBytes`, `UmodeMem`, `PtWalkCert`, `ProcPtOwn`,
`KstackOwn`, and **`WpSconfMem`**, whose A6.18 acceptance test is still
verified only at the statement level.

**PROCESS NOTES EARNED THIS SESSION.**

- Never start a sweep with `&` inside a compound command; use `setsid` and
  wait on it.  Three concurrent `make -j12`s on one tree is how the
  half-written-`.vo` caveat got created.
- A file leaving a `-k` error list means either "fixed" or "no longer
  reached".  Only the `.vo` timestamp says which.
- Inside an `Ltac` body, a bare identifier is resolved as a TERM at
  definition time (`iMod ("H" $! _ img log …)` fails naming `img`); and a
  `let … := fresh` name shadows the Coq hypothesis an intro pattern
  introduces.  Take the fact as an Iris hypothesis and `iExact` it.
- Converting an INFIX spelling to a PREFIX head is a re-parenthesisation,
  not a token substitution.  Give the new form a notation first.
- `Require Import` does not re-export: a notation body that mentions a name
  from a transitively-required module must spell it QUALIFIED.

### A6.27 A6.24 IS LANDED AT THE CORE AND ITS TWO CALLERS — AND THE
### KERNEL PAGE TABLE HAS LEFT THE CONTEXT (step-5, A6.26 tranche)

**`KptTree.ptree_translateAddr_own` TAKES ITS PAYER, exactly as A6.24
characterised it, and `KptTree.v` is GREEN.**  What landed:

- the core gained `Context (PTT : option CtxId)` — it is stated at
  `PtTree.ptree_own_at PTT`, so it serves both A6.21 tiers — plus the two
  parameters `(Sto : iProp Σ) (Stoq : mword 64 -> iProp Σ)` and the payer
  wand A6.24 wrote out verbatim (gen_heap AND the caller's currency
  together, because every gate in `TsoCtx` takes `gen_heap_interp` and
  `tso_interp_at` together);
- **the pure disjunct BECAME the resource disjunct** rather than gaining a
  neighbour, and that was forced, not tidy: the two disjuncts
  (`t' = t` vs `t' = ptree_set_leaf …`) are not provably exclusive, so a
  caller holding the pure fact beside a separate `Sto ∨ Stoq` could not
  decide which currency it had.  Tied to one disjunct, it can.  Every
  caller re-derives the old pure fact in three lines
  (`iDestruct … as "[[%He Hs] | Hq]"`), which is A6.24's "no caller gains a
  case split it did not already have" paid in the shape the proofmode
  actually needs;
- O1 and O2 `iClear "Hpay"` — the payer is genuinely unused when nothing
  moved — and O3 replaces `phys_word_pointsto_write` with `iMod ("Hpay" …)`.

**AND THE KERNEL TABLE MOVED TO `PTT = None`, WHICH IS WHAT MAKES THE
KERNEL CALLER PAYABLE AT ALL.**  `KptTree.tlb_inv_pt` and
`KptShare.kpt_body`/`kpt_inv_alloc` now hold `kptree_own`
(= `ptree_own_at None`, the notation A6.21 had already prepared), and BOTH
sections dropped their `` `{XI : CurCtx} `` binder.  That is A6.20's ruling
finally realised in the files that own the cells: `kpt_body` is the body of
a bare `inv` shared by every S-mode thread, so it may not name a context —
and it does not need to, because a PTE is read at `Read_ttw` (RULING 1's
flat arm) and only the A/D write-back needs a gate.  Had the kernel table
stayed at `Some cur_ctx`, its caller would have had to supply
`own_context`, which an invariant-holder has no business owning (§0.13′:
"a thread's AMBIENT context is its identity").

`KptShare.tlb_res_pt_translateAddr_at` and
`UptTree.utlb_inv_pt_translateAddr` (+ its `_tramp_fetch` / `_tf_load`
wrappers) thread the payer; all three files are GREEN.

**THE WRAPPERS' PAYER IS ADDRESS- AND OLD-VALUE-GENERIC, AND `Stoq` LOSES
ITS INDEX.**  A6.24's core premise names the slot (`pt_addr0 p1 vpn`) and
the old word, because the core has `p1`, `w`, `a0`, `d0` in its binder
list.  A WRAPPER does not: which leaf slot the walk lands on is decided
inside its own proof, by the kmap/`upt_spec` lookup.  So a wrapper's
premise quantifies `∀ a wold wnew` and its conclusion is the un-indexed
`Sto ∨ Stoq`.  This is not a weakening: the discharger instantiates
`Stoq` with whatever ∃-packaging it wants (a bundle at "some appended
log"), and the wrapper's proof builds the core's pinned premise from the
generic one in three lines (`iAssert … with "[Hpay]" as "Hpay'"`).

### A6.28 THE M-MODE BOOT STACK IS A LEDGER REGION, AND A6.10 UNDERCOUNTED
### THE M-MODE LOADS BY EXACTLY TWO (A6.17's cascade; landed)

A6.17's cascade turned out to have a piece neither it nor A6.10 named, and
it is a correction to a claim, not a new design:

> **A6.10 says "M-mode's only 8-byte data load in this tree is `entry`'s
> `ld sp, stack0`, a link-time constant".  That is wrong.**  `timerinit`'s
> EPILOGUE reloads the `ra`/`s0` its own PROLOGUE stored
> (`WpTimerinit.v` instructions 26 and 27, `c.ldsp`), and a byte that was
> just stored to can never be pristine — a pristine byte's timestamp
> element is DISCARDED, which is precisely what forbids the update a store
> needs.  So `wp_cldsp_gpr_tor`'s pristine premise is UNSATISFIABLE at its
> only two call sites in the tree.

What landed, all green:

- **`StackOwn.stack_own_phys` flipped to the registered ledger word**
  (`TsoCtx.ctx_phys_word_pointsto` at an ambient `` `{XI : CurCtx} ``) —
  same name, same arity, so its whole lemma suite and its eight consumers
  are textually unchanged.  A6.17's "real bill" stands: the residue itself
  is minted at adequacy.
- **`HartMLoad.robl_ram_ctx`** — the mirror of `HartMStore.wobl_ram_ctx`:
  "`robl_ram` says WHAT is owed; this says WHO can pay it for a byte that
  is WRITTEN at run time".  Twelve lines, `ctx_phys_load_bytes_ok` at
  `gs_of` through the A6.1a bridge.  **The `tv' ≤ length log` half of
  `robl_ram` is simply not needed** — the gate's conclusion is ∀ tv' above
  the hart's own view with no upper bound, exactly as A6.10 noted for the
  pristine gate.
- **`WpMmodeLoad.wp_ld_gpr_tor` and `wp_cldsp_gpr_tor` moved to the ctx
  tier**: `pristine_win ea 8` out, `own_context cur_ctx` in, on both sides
  of the continuation.  `wp_ld_gpr` KEEPS the pristine shape — `entry`'s
  `ld sp, stack0` really is an image constant, and it is the tree's only
  one.  So the two leaf families now say which kind of M-mode byte they
  read, which is the honest split.
- **`WpTimerinit.wp_timerinit`** takes and returns `own_context cur_ctx`
  and is GREEN.

**THE RULE THIS LEAVES:** a pristine premise is a claim that the address is
never stored to, and the cheap audit for it is to look for a STORE to the
same effective address in the same lemma's own instruction stream.  Both
offenders here were four instructions apart.

### A6.29 `WpUart`: THE PLUMBING IS DONE, THE DMA COMPLETION'S APPEND IS
### REPORTED — AND IT NEEDS ONE MORE THING THAN A6.9's SKETCH SAID

**The pure plumbing (A6.26 item 3's first half) is LANDED.**
`wp_disk_loop` is reshaped to A6.11's `wp_disk_step`: the callback now
takes `(d' W log')` with `⌜disk_step d m d' W⌝` and the log disjunct, and
**five of the six arms close** — CAPTURE, DRAIN, LATCH, IDLE by
`RiscvExec.tso_interp_of_disk_idle` after `W = ∅` collapses the disjunct
(`destruct Hlog as [[_ ->] | [Hne _]]` plus one `left_id_L`), and WILD is
refuted as before.

**`TsoCtx.ledger_store_ok`'s AUTHOR IS NOW A PARAMETER** (A6.26's
one-liner, done): `(auth : agent)` in place of `hart_agent cpu_id`.  The
proof never used the hart-ness — `msg_byte` ignores `pm_tid` and both
`latest_app_*` laws are author-blind — and the context-free ledger has no
author tie to keep.  `ledger_store_win_ok` passes `hart_agent cpu_id`.
`CID` stays: the `gtv` premises quantify over harts.

**THE STOP, precisely.**  The DMA COMPLETION arm's non-empty-write-set case
is the one open goal in the file (the build now fails with
`[Focus] Wrong bullet` exactly there, and nowhere else).  Closing it needs
**two** things, and the second is the one A6.9's sketch did not name:

1. **the lease's byte family flipped to `TsoCtx.phys_ledger`** —
   `WpVirtio.dma_own` and `VirtioProto.phys_map` / `phys_word2` /
   `phys_word4` / `phys_list` are RAW `phys_pointsto`, so `dom w` has no
   timestamp elements (A6.9).  ~185 occurrences over seven files
   (`VirtioProto` 88, `ProofVirtioDiskRwD` 36, `DiskInv` 16,
   `ProofVirtioDiskIntr` 14, `WpVirtio` 11, `ProofVirtioDiskRwF` 11,
   `ProofVirtioDiskInit` 8), all of them behind the current frontier.
2. **`VirtioProto.virtio_proto_step` TURNED INSIDE OUT INTO AN ACCESSOR**
   (235 lines).  It currently performs the gen_heap update itself and
   hands back `gen_heap_interp (w ∪ m)`.  The gate CANNOT be split —
   `ledger_store_ok` takes `gen_heap_interp` and `tso_interp_at` TOGETHER
   because the interp's own tie relates the flat cell to the ledger — so
   the caller (`wp_disk_loop`, the only holder of the bundle) must be the
   one that moves the memory.  The lemma therefore has to hand OUT the old
   bytes at `dom w` and take back the new ones, in the style its own
   `dma_own_acc` family already has, rather than doing the update.

A6.9's sketch — "the lease holds the elements; `wp_disk_step`'s callback
moves them" — is right about WHERE the elements must be and WHO must move
them, and silent about the fact that the lemma standing between them
currently owns the update.  That is the extra item, and it is why this is
reported rather than improvised.

### A6.30 THE A6.24 PAYER HAS NO PAYEE ABOVE IT — MEASURED, AND IT CHANGES
### WHAT THE REST OF THAT CASCADE IS WORTH

The upward caller closure of `ptree_translateAddr_own` was computed in
full (1 880 declarations from the `KptShare` root alone) and every
ancestor's STATEMENT tested for `tso_interp_of` / `tso_interp_at`, both
literally and transitively through the bundle-carrying definitions
(`Mobl_ram`, `Wobl_ram`, `wobl_ram`, `xread_obl(_ex)`, `wpte_obl(_at)`,
`era_interp`).  **Zero hits, in every chain.**

> **A payer threaded up from the exec-lane translation lemmas is threaded
> to the top of the tower and never paid.**  `mstate_interp`
> (`RiscvPtsto.v:1978`) is `reg_interp ∗ gen_heap_interp ∗ dev_interp` and
> does NOT carry the bundle, and it is the widest thing these statements
> hold.

Two consequences, and the second is the useful one.

**(a) THE EXEC LANE DEAD-ENDS, so threading it costs little and buys
little.**  `KptShare.tlb_res_pt_translateAddr_at` → `SRegime.res_absorb`
(and `res_absorb_wit`, `IntrDefs.strans_absorb(_wit)`) → the RECORD FIELDS
`sr_absorb` / `sr_absorb_wit` (`SRegime.v:389`/`:456`, three instances:
`bare_regime`, `kpt_share_regime`, `strans_regime`) →
`SRegime.sr_absorb_ktier` → `SmodeCorePt.s_regime_fetch` →
`SmodeCorePt.tlb_inv_pt_fetch`, **which has ZERO callers**.  The U-mode
chain likewise ends at `UserMemAccess.user_pt_vmem_read_addr_load` /
`_write_addr_store`, zero callers.  So the `exec`-shaped translation face
is, today, consumer-free at the top: threading `Sto`/`Stoq` through it is
mechanical and terminates, but nothing downstream is unblocked by it.

**(b) THE LIVE LANE IS THE `swp` FACE, AND THERE THE PAYER IS ALREADY
PAYABLE — BECAUSE THE OBLIGATION RECEIVES THE BUNDLE INSTEAD OF HOLDING
IT.**  `HartSKpt.kpt_leaf_write_node` (`HartSKpt.v:507`) →
`swp_translate_kpt` (`:585`) → `SRegime.kpt_swp_translate` (`:1374`), and
`swp_translate_kpt` feeds its `Hwr` into
`HartSTrans.swp_translate_hit_ex` / `_miss_ex`, whose premises are
**`PtTreeAdue.xread_obl_ex` and `wpte_obl_at`** — and `wpte_obl_at`
(`PtTreeAdue.v:1220`) is

```coq
  (∀ σ img log V, ⌜read_bytes σ.(mem) pa 8 = Some w⌝ -∗
     mstate_interp σ -∗ tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
      ▷ (|={∅,⊤}=∗ mstate_interp (MState … (write_bytes …) …) ∗
           wobl_ram img σ log V 8 req ∗ R))
```

i.e. an obligation that is HANDED the bundle.  `HartSKpt` builds a
bundle-FREE `Hwr` (`HartSKpt.v:514–522`) today; giving it the
bundle-carrying shape and discharging it with `ledger_store_ok` against
the `None`-tier slot the kernel invariant now holds (A6.27) is the whole
of the A/D write-back's real payment.  **That is the seam A6.21 named
("`HartSKpt`'s `iAssert`-built `Hrdx`/`Hwr` seams"), and this measurement
says it is the ONLY one that matters** — `Hrdx` needs framing only (an
exclusive/`Read_ttw` read is flat).

**THE RULE TO CARRY:** before threading a payer upward, compute the
closure and check that something up there HOLDS the bundle.  If nothing
does, the obligation belongs on a lane where the bundle is handed DOWN as
a callback — which, in this tree, is always the `swp` lane, never the
`exec` one.

### A6.31 THE FRONTIER AFTER THE A6.26 TRANCHE — EIGHT RED, 513 OF 1330,
### AND THE COUNT WENT UP FOR THE FIRST TIME IN THREE TRANCHES

**ONE CLEAN BUILD** (`iris/*.vo` deleted wholesale, the model's kept, a
single `make -f CoqMakefile -j12 -k`).  The integrity check A6.26 asks for
holds exactly: **521 files ATTEMPTED, 513 `.vo` produced, 8 errors** —
every file `make` reached is accounted for, none silently skipped.

> **513 of 1330 fresh-green (A6.26's clean number was 505), and the red set
> is EIGHT.**  This is the first tranche in which the honest clean count
> ROSE while the red set grew, and both movements are the same fact:
> `KptTree` is green, so its cone became REACHABLE, and eight files inside
> it are now known-red instead of unreached.  A6.25's rule again — a file
> leaving or joining an error list means "fixed", "newly reachable", or "no
> longer reached", and only the `.vo` timestamp says which.

    WpUart.v       A6.29 — REPORTED STOP (the DMA completion's append).
                           Everything else in the file is A6.11-shaped and
                           closes; this is the single open goal.
    HartSKpt.v     A6.27 + A6.30(b).  Two things, and only the second is
                   :132   design: (i) its walk nodes still say [ptree_own]
                           (= [Some cur_ctx]) while [kpt_body] is now the
                           [None] tier -- a rename to the [_at None] forms;
                           (ii) [kpt_leaf_write_node]'s bundle-free [Hwr]
                           must become [PtTreeAdue.wpte_obl_at]-shaped and
                           pay with a [wobl_ram_ledger] (the ledger twin of
                           [HartMStore.wobl_ram_ctx], not yet written).
                           THIS IS THE A/D WRITE-BACK'S REAL PAYMENT POINT.
    UserPtTree.v   A6.27's cascade — [utlb_inv_pt_translateAddr_u] and its
                   :1382  four siblings thread [Sto]/[Stoq]; mechanical, and
                           the closure above it is 11 callers ending at
                           [UserMemAccess]'s two consumer-free lemmas.
    TransPt.v      A6.27's cascade, same shape one lane over: an [↦ₚ₈]
                   :910   write applied to an [↦ₚₜ] slot.  The A/D
                           write-back on the user-PT walk lane.
    WpStartNew.v   A6.28's cascade — [wp_store_gpr] now takes
                   :1138  [ctx_phys_word_pointsto] + [own_context]; the four
                           M-mode prologue/epilogue sites and the
                           [Entry]/[BootChain] threading above them.
    BootCarve.v    A6.28's OTHER end, and it is NOT a binder fix.
                   :1162  [boot_stack_own_phys] builds [stack_own_phys] out
                           of RAW carve bytes; now that the M-mode stack is
                           a ledger region, it cannot -- A6.9 says no rule
                           above the interpretation mints a timestamp
                           element.  **The fix is A6.10's shape one tier
                           down**: the carve gains a premise handing the
                           range's ledger residue, and [TsoCtx] gains the
                           physical twin of [ctx_pointsto_of_pristine] --
                           an EXCLUSIVE one, since the stack is written:
                           [phys_pointsto a dq v ∗ a ↪[ts]{dq} 0 ⊢
                            ctx_phys_pointsto ξ a dq v] through the
                           [⌜t = 0⌝] arm of [llb].  Then adequacy mints it,
                           which is where A6.17 always said the bill lands.
    KstackOwn.v    A6.16 verbatim, from A6.26's verification list: the last
                   :215   two [TsoCtxShim.ctx_pointsto_of_mem] uses
                           ([kstack_byte_rekey] / [kstack_word_rekey], the
                           KT0↔KT1 rekey).  [TsoCtx.ctx_pointsto_of_phys] is
                           the replacement; NO new kit.
    PtWalkCert.v   A6.7(B)'s OWN leftover, and it was predicted: the file is
                   :840   on the "STILL TO ABSORB" list.  The patched
                           [checked_mem_read] no longer exposes
                           [liftR (read_kind_of_flags …)] until the
                           [(access, res)] match is reduced.  Same one-line
                           fix as [SmodePte]'s.

**THE VERIFICATION LIST BEHIND `KptTree` (A6.26), WALKED BY `.vo` AND NOT
BY THE ERROR LIST — AND THE ANSWER IS "STILL UNREACHED".**  Of the seven,
`HartSKpt` and `KstackOwn` are RED (above), and **`UserBytes`, `UmodeMem`,
`ProcPtOwn`, `PtWalkCert` and `WpSconfMem` have NO `.vo` AT ALL**: they sit
behind `HartSKpt` / `KstackOwn` / `PtWalkCert` in the DAG and `make -k`
never reached them.  They are neither green nor known-red, exactly as
A6.25's rule warns — and this is the second tranche running in which
`WpSconfMem`'s A6.18 textual-invariance acceptance test could NOT be
confirmed by the build.  **`make WpSconfMem.vo` is still the first thing to
do once `HartSKpt` closes**, and until then A6.18 stands verified at the
statement level only.  (`PtWalkCert` is on both lists: it was an A6.26
verification entry AND is red on A6.7(B)'s own leftover.)

**WHAT THE TRANCHE LANDED, for the record:** `KptTree`, `KptShare`,
`UptTree`, `PtTree`/`PtBuild`'s consumers, `StackOwn`, `HartMLoad`,
`WpMmodeLoad`, `WpTimerinit`, `TsoCtx` (the author-generic ledger gate),
and `WpUart`'s five closing arms.

### A6.32 THE A/D WRITE-BACK IS PAID — `HartSKpt` IS GREEN, AND A6.30's RULE
### IS WHAT FOUND THE PAYMENT POINT (ratified tranche, ruling 2)

**LANDED, and it is the confirmation of A6.30(b).**  `HartSKpt` is GREEN.
Three pieces:

1. **`HartMStore.wobl_ram_ledger` and `wobl_ram_ledger_ex`** — the
   context-free twins of `wobl_ram_ctx`: a window of UNREGISTERED ledger
   bytes pays the flat update and the append's THREE ghost steps, with NO
   `own_context`.  **The `_ex` form is the one the page table needs and it
   was not predicted**: the Svadu A/D write-back is a CONDITIONAL write
   (`HartMStore.mwrite_req8_con` is `AV_exclusive`), so `wstore_tv` puts the
   hart's view PAST its own append and the plain form's `ak_excl = false`
   premise is unsatisfiable there.  Only the view arithmetic differs; the
   gate is the same.
2. **`HartSKpt.kpt_leaf_write_node` is now stated AT `PtTreeAdue.wpte_obl_at`**
   and discharges it against the `None`-tier slot `kpt_body` now holds.
   This is A6.30(b) realised: the obligation is a CALLBACK, so the seam
   holds the slot AND the bundle at the same instant — which is exactly what
   the gate needs, since the interp's tie means neither the flat cell nor
   the ledger may move without the other.
3. **`kpt_leaf_node_canon_obl`** — the read seam at `xread_obl_ex`, a pure
   framing wrapper.  The bundle-FREE `kpt_leaf_node_canon` KEEPS its own
   consumer (`swp_read_pte_kpt_ex`, the leaf read node), which is why this
   is a wrapper and not a restatement.  A PTE read is `Read_ttw`, RULING 1's
   flat arm, and owes no ghost step at all.

**AND THE EXEC LANE WAS THREADED ANYWAY, because it has to COMPILE even
though it cannot pay.**  A6.30(a) measured that `sr_absorb` dead-ends in
consumer-free lemmas; it does not follow that it can be left alone, because
`KptShare.tlb_res_pt_translateAddr_at` is its instance.  So `Sto`/`Stoq` and
the address-generic payer wand now ride through **both `s_regime` record
fields** (`sr_absorb`, `sr_absorb_wit`) and all of their instances and
dispatchers: `bare_absorb(_wit)` (returns `Sto` untouched — Bare translates
without touching memory), `res_absorb(_wit)`, `sr_absorb_ktier`,
`IntrDefs.strans_absorb(_wit)`.  `SRegime` and `IntrDefs` are GREEN.  The
record's payer is stated over `TsoCtx.phys_ledger_word` and that is not a
narrowing: the `s_regime` face only ever carries the SHARED KERNEL table or
Bare — a user page table translates through `UptTree`, not through this
record.

### A6.33 THE A6.18 ACCEPTANCE COMPILE, THIRD ATTEMPT: STILL NOT REACHED —
### AND THE THING IN THE WAY IS THE ONE A6.18 ITSELF PREDICTED

**VERDICT, stated plainly: `WpSconfMem.vo` STILL DOES NOT EXIST.**  The
blocker is no longer `HartSKpt` (green) or A6.21 (landed).  It is
`SmodeCorePt`, and it is **A6.18's own "THE STORE HALF IS THE HIDDEN HALF"
coming due** — measured this session, at every call site:

> `SmodeCorePt.s_win_write` (`:362`), `word_pointsto_write_c` (`:394`) and
> `word4_pointsto_write_c` (`:416`) change the VALUE of a now
> context-indexed byte using `gen_heap_interp` ALONE.  They compiled only
> through `TsoCtxShim.ctx_pointsto_{to,of}_mem`, which no longer exist.
> **`TsoCtx` exports no law that can replace them**, and that is by design:
> every value-changing law (`ctx_store_ok` / `_win_ok` / `_sub_ok`,
> `ledger_store_ok` / `_win_ok`) takes `gen_heap_interp` AND `tso_interp_at`
> TOGETHER, plus `own_context` at the registered tier.  The only update
> concluding a `ctx_pointsto` at an UNCHANGED value is
> `ctx_pointsto_persist` (a dfrac move).

**THE OBLIGATION IS ALREADY THE RIGHT SHAPE; THE PROOFS ARE STALE.**
`HartSMem.Wobl_ram` (`:3541`) is bundle-carrying, and so is the AMO twin
inside `swp_execute_AMOSWAP_S_ex_mode` (`HartSMem.v:4937`).  Every one of
the six consumers still enters the write node with the OLD one-binder
intro (`iIntros (sigma) "Hsi"`), so the bundle is OFFERED and never taken.
The full site table, which is the worklist:

| site | enclosing lemma | bundle taken? | `own_context` |
|---|---|---|---|
| `WpSconfMem.v:216` | `wordw_pointsto_write_c` (`:203`) | no — helper, no bundle in its statement | no |
| `WpSconfMem.v:245` | `mem_pointsto_write_c` (`:230`) | no — same | no |
| `WpSconfMem.v:1190` | `wp_store_s_sconf_au` (`:1023`) | offered by `Wobl_ram`, not intro'd | **OWNED** (`sie_cap_gpr`, destructured `:1082`) but parked on the `swp_mono` POST bracket at `:1140` |
| `WpSconfLock.v:1105` | `wp_amoswap_lockopen_s_sconf` (`:906`) | offered, not intro'd | **OWNED** (`:917`, destructured `:962`), parked on the post bracket at `:1019` |
| `WpSmodePtLeaves.v:1027` | `wp_csd_s_r_t` (`:856`) | offered, not intro'd | **ABSENT from the whole file** |
| `WpSmodePtMem.v:1806` | `wp_csw_s_r_t` (`:1624`) | offered, not intro'd | **ABSENT** |
| `WpSmodePtMem.v:2111` | `wp_sd_s_r_t` (`:1929`) | offered, not intro'd | **ABSENT** |

So the tranche splits cleanly in two, and the split is the useful part:

- **`WpSconfMem` and `WpSconfLock` need NO new premise.**  They already own
  the token through `IntrDefs.sie_cap`; it is merely routed into the
  `swp_mono` POST bracket instead of the engine's.  Re-route it, take the
  `img log tv V` binders and the bundle the obligation already hands over,
  and pay with a bundle-carrying restatement of the two helpers.  **A6.18's
  textual-invariance claim survives this**: the change is inside
  `Local Lemma`s and a proof script, not in any of the ~20 exported
  statements.
- **`WpSmodePtLeaves` and `WpSmodePtMem` DO need one** — `own_context` does
  not occur anywhere in either file; their premises are raw CSR cells.
  These are the S-mode leaves that store a PTE from SOFTWARE, i.e. a USER
  page table, which the storing thread owns — so `own_context cur_ctx` is
  the honest premise, and this is the A6.14/A6.18 threading class already
  ratified, just not yet reached.  It is a statement change on three leaves
  plus their cones.

**THE HELPERS' REPLACEMENT SHAPE**, so it is not re-derived: one
bundle-carrying window store in `SmodeCorePt`, stated at the leaf's own
footprint (`pa_of ppn a`, width `n`), taking `gen_heap_interp σ.(mem)`,
`tso_interp_of img σ.(mem) log V` and `own_context cur_ctx`, returning the
heap at `write_bytes` and the bundle at the appended log — i.e.
`HartSMem.Wobl_ram`'s conclusion, proven by `TsoCtx.ctx_store_win_ok` after
`TsoCtx.ctx_pointsto_phys` turns the VA window into the physical one
(`kmap_at_agree` pins the page number; the tier pin comes out of the same
destruct and goes back in on the way up).  `s_win_write`'s LIST-of-offsets
shape does not survive: the gate is a WINDOW gate because a store is ONE
append over n bytes, and both of its callers use `seq 0 n` or `[0]` anyway.

### A6.34 THE BOOT MINT'S FAR END: THE BRIDGE IS LANDED, ITS HOLDER IS
### LOCATED, AND ONLY THE CARVE'S RANGE PLUMBING IS LEFT (ruling 3)

`TsoCtx` gained, both one-liners over the sealed bodies:

    ledger_elem0 a dq        :=  a ↪[ts_name]{dq} 0
    phys_ledger_of_elem      :  phys_pointsto a dq v -∗ ledger_elem0 a dq -∗
                                phys_ledger a dq v
    ctx_phys_pointsto_of_elem:  phys_pointsto a dq v -∗ ledger_elem0 a dq -∗
                                ctx_phys_pointsto ξ a dq v

**A6.9 IS NOT WEAKENED, and the ruling's condition is met.**  Nothing here
MINTS an element.  `ledger_elem0` is the EXCLUSIVE twin of A6.10's
`pristine_byte` (which is the same element DISCARDED), and its holder is
the same one: **the era's initial-state ghost allocation** — the single
place any timestamp element is ever created, and demonstrably the supplier
already, since it is where `BootCarve.kernel_data_intro`'s `pristine_va`
premise and its image bytes come from.  The two laws only let the carve
pair an element back up with the byte it belongs to.  The timestamp is 0
because the era's log is empty at allocation, which is also what makes the
CLEAN arm free (`TsoGhost.llb`'s `⌜K = 0⌝` disjunct — no bupd, no context;
the same trick A6.10 needed to make `kernel_data` mintable at all).

**WHAT IS LEFT IS PLUMBING, NOT DESIGN.**  `BootCarve.boot_stack_own_phys`
(`:1157`) builds `stack_own_phys` out of `boot_raw_ran` by induction, and
`boot_raw_ran` is a big-op of bare `pointsto`s with its own split/word
lemma family (`boot_ran_split`, `boot_ran_word`).  Giving the carve ledger
bytes means carrying the element through THAT family — either a fused
`boot_led_ran` with the three lemmas re-proven, or an element big-op over
the same `ran_bytes` map split in step with it.  Either is mechanical; it is
the only reason `BootCarve` is still red.

### A6.35 THE FRONTIER AFTER THE RATIFIED TRANCHE — 550 OF 1330, EIGHT RED

**ONE CLEAN BUILD** (`iris/*.vo` deleted, one `make -j12 -k`).  The A6.26
integrity check holds: **558 attempted, 550 `.vo`, 8 errors** — every file
`make` reached is accounted for.

> **550 of 1330 fresh-green, up from A6.31's 513, with the red set still
> at EIGHT.**  Both numbers moved the right way for once: the A/D
> write-back being paid greened `HartSKpt` and unblocked ~37 files of its
> cone, and nothing regressed.

Green this tranche, each verified by its own `.vo`: **`HartSKpt`**,
`SRegime`, `IntrDefs`, **`KstackOwn`**, `KptShare`, `KptTree`, `UptTree`,
`HartMStore`, `TsoCtx`.

    SmodeCorePt.v:380  A6.33 — the three gen_heap-only write helpers.  THIS
                               is what now stands between the tree and the
                               A6.18 acceptance compile.
    WpUart.v:1002      A6.29 — the DMA completion (ruling 1; last by order)
    BootCarve.v:1162   A6.34 — the carve's range plumbing (kit landed)
    WpStartNew.v:1138  A6.28 — the M-mode store/load sites + Entry/BootChain
    UserPtTree.v:1382  A6.27 — [Sto]/[Stoq] through five statements
    TransPt.v:910      A6.27 — the same, one lane over
    PtWalkCert.v:840   A6.7(B) — see A6.35's last paragraph
    CpuOwn.v:110       NEW, and it is the OLDEST class in the port: a raw
                       `mem_pointsto_ne` applied to a now-ctx byte — the M1
                       flip's error class (a), one `ctx_` twin away.  It was
                       never visible before because it sits behind
                       `KstackOwn` in the DAG.

**AND `WpSconfMem` IS STILL UNREACHED — for the THIRD tranche running.**
`.vo` absent, along with `WpSconfLock`, `WpSmodePtMem`, `WpSmodePtLeaves`,
`UserBytes`, `UmodeMem`, `ProcPtOwn`: they are all behind `SmodeCorePt`.
A6.18's textual-invariance acceptance test therefore remains verified at
the STATEMENT level only.  **A6.33 is now the whole of what stands in the
way, and it is A6.18's own predicted store half** — so the next session's
first move is `SmodeCorePt`'s three helpers, and its first check after that
is `make WpSconfMem.vo`.

**`PtWalkCert` IS NOT THE ONE-LINE FIX A6.31 CALLED IT.**  Measured: its
`pr_exec_chk` (`:832`) is inside a section whose `res` is ABSTRACT
(`Context (aq rl res : bool)`), so the patched `checked_mem_read`'s
`match (access, res)` cannot reduce — at `Load PageTableEntry` the arm
taken depends on `res` (`Read_ttw` when false, `read_kind_of_flags` when
true, and the two are a `returnR` and a `liftR` respectively, so they do
not even have the same sequencing lemma).  Worse, its two instantiations
(`:970`, `:995`) name `Read_plain` for `res = false`, which the patch has
made WRONG.  This is `MemAccessGen`'s case exactly, and it wants
`MemAccessGen`'s fix: a side condition plus a `rk_select_*` rewriting
lemma, so the long proof script is untouched.

### A6.36 THE OVERRULING, IMPLEMENTED AT THE MACHINE — ONE PLAIN READ ARM,
### AND THE STRONG RULE IS DELETED RATHER THAN DEPRECATED

Implements the rewritten RULING 1.  Landed and green at the machine and
leaf tiers:

- **`RiscvLang.v`**: the strongly-ordered RAM-read arm of `mnode_step` is
  GONE and `ak_strong` with it; the plain arm's guard is `ak_excl = false`
  alone.  Exclusive arm, write arms, barriers, MMIO and DMA are untouched,
  exactly as the redirect said.  The fallout inside the file was three
  `MemRead` destructurings (`mnode_step_v_disk`, the `resv_ok` preservation
  and the frame lemma) losing one disjunct and one conjunct each.
- **The generated model is RESTORED to the pinned baseline**, bit-identical
  to the main repo's `model-xv6iris/` (`rv64d.v` and `rv64d_types.v` were
  the only two files the patch touched — 100 and 23 lines).  The patch
  commit `00046a7` is PARKED, untouched, in both `FLIPTREE/sail-riscv` and
  `/shared/xv6iris-3-fliptree-backup/sail-riscv`.
- **`HartEvents.v`**: `wp_hart_ram_read_strong` and `swp_hart_ram_read_strong`
  are **DELETED, not deprecated**, and the reason is worth recording because
  the redirect left it open:

> **The strong rule is NOT a derivable special case of the plain one.**  It
> concludes from a FLAT `read_bytes σ.(mem)` fact with no view advance, and
> a flat cell says nothing about what a view BELOW the top can see — the
> same measurement A6.7(B) made at `WpMmodeLoad`.  It was sound only
> because the machine had an arm that read flat; with that arm gone the
> rule has no proof, so keeping it as "deprecated" would mean keeping an
> unprovable statement.  A comment block in its place records what it was,
> why it went, and that the de-confliction project restores it together
> with the parked Sail patch.

  The two plain rules lost their now-meaningless `ak_strong … = false`
  premise (positional, so every call site drops one argument).
- **`HartBlock.v`** (the solo-era bracket) and **`HartMemRun.v`** (the user
  tier's walker) collapsed their three-way RAM-read case split to two.
  `HartMemRun`'s is the instructive one: A6.16 had it split
  exclusive / `ak_strong` / plain, and the fetch branch discharged
  `bytes_own_read` flat.  **Now every non-exclusive read of the walker's
  own bytes owes `Mobl_ram_plain`** — and that costs the user tier nothing,
  because A6.16 had already moved `bytes_own` to `ctx_phys_pointsto`.  The
  overruling lands cheapest exactly where the ledger was already carried.
- **`HartMemAsm.rk_ram_ok`** drops `Read_ttw` (the constructor no longer
  exists).  The wildcard hazard A6.7(B) recorded is unchanged and still
  worth the comment: omitting a kind from the true list costs no error.

**AND THE REVERT IS SMALLER THAN IT LOOKS, because `Read_ifetch` SURVIVED
THE UNPATCHING.**  The patch added `Read_ttw` and the `(access, res)`
selection; `Read_ifetch` is an ORIGINAL constructor of the pinned model.
So the A6.7(B) twins that carry `Read_ifetch` (`RiscvTryStep`'s
`run_read_ram_ifetch_4_pin`, `RiscvFetchExec`'s three) still typecheck and
compile untouched — they are simply instance-free now.  Only the `Read_ttw`
mentions and the `(access, res)` reductions have to go: `WpLoad`'s
`exec_read_ram_ttw_8`, `SmodePte`'s arm reduction, and
`MemAccessGen.rk_from_flags`/`rk_select_flags` with their side condition in
`UserMemMis`.  Worth knowing before anyone budgets the revert as the mirror
image of the patch: it is not.

### A6.37 THE KERNEL-PT READ STORY, EXACTLY — AND ONE MEASUREMENT THAT
### KILLS THE ROUTE THE PLAN ASSUMED FOR HART 0

Characterising the corrected discharge bullet.  The good news first: the
weakening the ruling calls for is ALREADY IN THE TREE, and the exact
statements needed are small.  The bad news is one measured fact about the
model that the plan did not have.

**FIRST, THE MODULO-A/D WEAKENING IS ALREADY BUILT — IT IS `ptree_canon`.**
`HartSKpt.kpt_leaf_node_canon` (and `kpt_maps_across` under it) already
conclude "∃ w, reads w ∧ `pte_canon w = pte_canon leaf0`", i.e. reads the
leaf MODULO A/D, and the shared table's cross-opening invariant is
`kpt_lb`, a snapshot up to `ptree_canon` — A/D-erased by construction.  So
the certificate weakening the ruling asks for costs nothing: the walk
lemmas were already stated at it.  What has to change is the OBLIGATION
those lemmas discharge — from the flat `read_bytes σ.(mem)` to
`HartSMem`'s `tso_read_bytes … tv'` at every reachable view.

**SECOND, WITHIN ONE OPENING THE READ IS EXACT, and that is what makes the
packaging lemma easy.**  `phys_ledger a dq v` is `phys_pointsto a dq v ∗
a ↪[ts_name]{dq} t`, and `era_interp`'s tie says `TM !! a = Some t →
latest img log a t v` — the element IS the LATEST write's timestamp and
`v` its value.  So a holder of the FULL-fraction ledger byte knows there
is no later message at that address at all, and a read at any `tv' ≥ t`
returns exactly `v`.  No history predicate over the log is needed, and no
"every later message is an A/D variant" invariant: the A/D write-back is
itself a `ledger_store_ok` under the same `kptN` invariant, so it cannot
interleave inside an opening.

**THE TWO STATEMENTS THAT ARE ACTUALLY MISSING** (both additive over
existing ghosts; neither is a new law about the seal):

    (* TsoCtx: the ledger byte with its timestamp EXPOSED.  [phys_ledger]
       hides [t] existentially, and every discharge below needs to compare
       it against a receipt. *)
    phys_ledger_at a dq v t := phys_pointsto a dq v ∗ a ↪[ts_name]{dq} t
    phys_ledger_at_ledger    : phys_ledger_at a dq v t ⊢ phys_ledger a dq v
    phys_ledger_of_at        : phys_ledger a dq v ⊢ ∃ t, phys_ledger_at a dq v t

    (* TsoCtx: the packaging lemma the ruling asks for -- [ctx_phys_load_ok]
       with the CONTEXT's bound replaced by the MACHINE's receipt.  Same
       proof shape: [t ≤ F ≤ gtv h] makes the latest message visible, and
       the interp's tie makes it the value. *)
    ledger_read_ok `{CID} (g : gstate) (h : agent) (a : Arch.pa) (n : N)
        (w : bv m) (dq : dfrac) (F : nat) :
      gen_heap_interp g.(gmem) -∗ tso_interp_at riscv_eraGS g -∗
      view_lb view_name loglen_name h F -∗
      ([∗ list] j ∈ seq 0 (N.to_nat n),
         ∃ t, ⌜(t ≤ F)%nat⌝ ∗ phys_ledger_at (pa_add a j) dq (nth_byte w j) t) -∗
      ⌜forall tv', (g.(gtv) … ≤ tv')%nat ->
         tso_read_bytes g.(gimg) g.(glog) h tv' a n w⌝

**AND `kpt_body` GAINS ONE PURE TIE PER SLOT** — the `⌜t ≤ B⌝` the ruling
names — with `B` a parameter of `kpt_inv` published at boot.  `PtTree`'s
tiered slot is the natural home: the `None` arm becomes
`∃ t, ⌜t ≤ B⌝ ∗ phys_ledger_at a dq w t`, which keeps `pt_slot_own_forget`
and every pure memory fact unchanged.

**THE MEASUREMENT THAT CHANGES THE PLAN — `sfence.vma` EMITS NO BARRIER IN
THIS MODEL.**  I checked, because the obvious route for hart 0 was "xv6's
`kvminithart` fences before it writes `satp`, so hart 0's own buffer
drains and the SAME receipt-based lemma serves it":

> `execute_SFENCE_VMA` (`rv64d.v:41179`) is register reads, a TVM
> privilege check and `flush_TLB` — **there is no `Interface.Barrier`
> outcome anywhere in it.**  So `sfence.vma` is a register-only node in
> this model, `fence_drains` never sees it, and hart 0's view does not
> move.  (Nor is there a lock acquire between `kvminit`'s last PT store
> and `kvminithart`'s first walk: xv6's `main` runs `kinit(); kvminit();
> kvminithart();` back to back, and the last `kalloc` — hence the last AMO
> that would have taken hart 0's view to the top — happens DURING PT
> construction, i.e. below `B`.)

**SO HART 0 REALLY IS STORE-FORWARDING-ONLY, AND FORWARDING NEEDS THE
AUTHOR.**  `TsoMemPa.visibleb h tv log t`'s own-author arm asks for
`pm_tid (log !! t) = h`, and nothing in `phys_ledger` records who wrote
the byte.  The ingredient that can carry it EXISTS and is free — the
`era_logm_name` entries are PERSISTED at append (§4), so the fragment
`t ↪[logm_name]□ m` is duplicable — but exporting it, and having
`ledger_store_ok` hand back its own append's fragment, is a NEW EXPORT on
`TsoCtx`'s surface that the corrected plan did not name.  Concretely:

    ledger_msg_at t m        := t ↪[logm_name]□ m          (persistent)
    ledger_store_ok … ==∗ … ∗ ledger_msg_at (length g.(glog))
                                 (PWMsg Pnew auth)
    ledger_read_own_ok       : the [ledger_read_ok] twin whose premise is
                               [ledger_msg_at t m ∗ ⌜pm_tid m = h⌝] in
                               place of [view_lb h F ∗ ⌜t ≤ F⌝]

**STOPPING POINT (for ratification).**  The secondary-hart half is fully
determined and needs no ruling — `phys_ledger_at` + `ledger_read_ok` +
the `⌜t ≤ B⌝` tie + the flag-read leaf's receipt, all over existing
ghosts.  The HART-0 half needs a decision, because the plan's "no
receipt, store forwarding" is only implementable with the author export
above:

  (a) EXPORT THE AUTHOR (the `ledger_msg_at` family): honest, small,
      no new camera — but it widens the sealed surface with a fact about
      the LOG, which nothing else in the kit exposes;
  (b) GIVE `sfence.vma` A BARRIER OUTCOME in the machine (a `RiscvLang`
      change, not a model change: the lifting could treat the SFENCE node
      as draining).  This is the ISA-honest reading — `sfence.vma` is
      exactly the fence that orders PT writes before implicit reads — and
      it costs one arm plus a full rebuild.  It also pre-pays part of the
      later de-confliction project;
  (c) HAVE BOOT PUBLISH A TOP RECEIPT: make hart 0 take one AMO (or an
      explicit drain) between `kvminit` and `kvminithart`.  That is a
      KERNEL SOURCE change and is rejected on the standing rule that the
      proof does not get to edit the program.

I recommend (b): it needs no new exported ghost fact, it makes hart 0 and
the secondaries use the SAME lemma, and it is the semantics the ISA
already assigns to the instruction xv6 actually executes there.

### A6.38 HANDOFF AFTER THE OVERRULING — WHAT LANDED, WHAT THE READ-SIDE
### RE-PORT ACTUALLY COSTS, AND A MEASUREMENT TRAP THAT ALMOST GOT ME

**RULING-INDEPENDENT WORK, LANDED AND GREEN** (all of it store-side or
kit, none of it touched by the overruling):

- **`SmodeCorePt`'s write family is bundle-carrying** (A6.33's ratified
  shape).  `s_win_write` is replaced by `wordw_win_store_c` — one append
  over the whole window through `TsoCtx.ctx_store_win_ok` at
  `RiscvExec.gs_of` — with `word_pointsto_write_c` / `word4_pointsto_write_c`
  restated on top of it, same names, new premises (`img σ log V` +
  `own_context`).  Three supporting lemmas do the VA↔physical window
  crossing: `win_pins` (reads the per-byte canonicality and TIER PIN off
  the window itself, which is what lets it go back in at the tier it came
  out of), `win_to_phys`, `win_of_phys`.  `TsoCtxShim` is gone from the
  file.
- **THE PAYER'S CURRENCY IS NOW MEMORY-INDEXED, AND THAT WAS FORCED.**
  A6.27's `Sto`/`Stoq wnew` pair cannot serve a caller that translates
  TWICE — and `SmodeCorePt.s_regime_fetch` does, on the straddling
  (2-mod-4) fetch: the second translation would need a second `Sto` and
  the currency is not duplicable.  Replacing the pair with a single
  `S : TsoMemPa.bytemap -> iProp Σ` (in at `S σ.(mem)`, out at
  `S σ'.(mem)`) makes "before" and "after" the same predicate at different
  arguments, so n translations chain with no extra parameters; the payer
  wand becomes `□` for the same reason.  **And it made the CORE simpler,
  not harder**: `ptree_translateAddr_own`'s conclusion goes back to the
  ORIGINAL pure `t'` disjunct (A6.27 had turned it into a resource
  disjunct precisely because a one-shot currency had to be tied to a
  branch), so every caller's `%Htsh` intro is verbatim what it was before
  the tranche started.  Threaded and green through `KptTree`, `KptShare`,
  `UptTree` (+2 wrappers), `SRegime` (both record fields, all instances),
  `IntrDefs`, `SmodeCorePt`.
- **`TsoMemPa.bytemap`** — a NAME for `gmap Arch.pa (bv 8)`.  Any file that
  imports `SailStdpp.Base` elaborates a fresh binder of that type at the
  SAIL key instances and it will not unify with the stdpp-keyed one
  (durable-notes' binder trap; `RiscvLang.v` dodges it by importing
  `SailStdpp.Base` LATE, which a leaf file cannot do).  Spelling the type
  with this name is the fix, and it is what every `S`/`img` binder added
  this tranche uses.

**THE OVERRULING'S OWN WORK: see A6.36 (machine + leaves) and A6.37 (the
kernel-PT read story, characterised, with one route measured dead).**

**THE CLOSING CLEAN BUILD: 247 ATTEMPTED, 244 `.vo`, 3 ERRORS** (`iris/*.vo`
deleted, one `make -j12 -k`; self-consistent, nothing silently skipped).

> **244 of 1330 fresh-green, down from A6.35's 550, with the red set down
> from EIGHT to THREE.**  A6.25's rule for the third time, and never more
> sharply: **red-set size and fresh-green count move in opposite directions
> whenever a frontier file is replaced by a DEEPER one.**  `HartMFetch` is
> as deep as this tree gets — the whole fetch tier stands on it — so making
> it red put ~300 files out of reach at a stroke, including every file the
> earlier tranche had left red (they are now unREACHED, not fixed).  The
> honest reading is not "the overruling cost 306 files"; it is "the
> overruling moved the frontier from the top of the tree to the bottom of
> the fetch lane, and everything above is queued behind two files."

**THE READ-SIDE RE-PORT (redirect item 5) IS A TWO-FILE FRONTIER, AND THAT
IS THE USEFUL MEASUREMENT.**  I expected the fetch tier to break wide
(`HartMFetch`, `HartPilot`, `SmodeCore`, `UserMem`, `SmodeCorePt`'s fetch,
`HartSMem`'s ttw-adjacent nodes).  A `-k` sweep after the machine change
says otherwise: **`HartMFetch` and `HartPilot` are the only two**, because
every other former strong-arm consumer sits ABOVE them in the DAG and is
unreached.  So the re-port is a chain, not a fan-out, and it starts at:

    HartMFetch.swp_checked_mem_read_ifetch4 / _ifetch2   (:721, :817)
      -- take the PLAIN obligation instead of the flat one (mirror
         [HartMLoad.swp_checked_mem_read_load8]'s [robl_ram] shape at
         widths 4 and 2), drop the [(access, res)] reductions the Sail
         patch needed, go back to [mread_req]/[mread_req2] and
         [read_ram Read_plain], and use [swp_hart_ram_read_plain].
         Their four call sites (:1525, :1582, :1647, :1654) then thread
         the obligation, and kernel TEXT discharges it from the PRISTINE
         tier -- [TsoCtx.pristine_read_bytes_ok], whose conclusion is
         ∀ tv with NO lower bound, so the plain rule's premises are free.
    HartPilot.hp_fetch_strong (:277) and the pilot rule (:366, :410)
      -- [ak_strong] is gone; A6.7 already records that both pilot lemmas
         have NO consumers, so they are free to reshape or delete.

**THE MEASUREMENT TRAP, recorded because it nearly went into this note as
a number.**  The incremental sweep after the machine change reported
**550 `.vo` and only 3 errors**, which would have read as "the overruling
cost almost nothing".  It is wrong: `make -k` deletes the `.glob` of a
failed target but **LEAVES THE STALE `.vo`** (durable-notes says so; this
is the first time it has bitten this project's numbers).  `HartMFetch.vo`
and `HartPilot.vo` were still sitting there at 18:26, older than the
`RiscvLang.vo` at 18:39 they were built against, and every one of the ~365
files below the change was never revisited.  `ls -la --time-style=+%H:%M
<file>.vo` against the changed file's `.vo` is the two-second check.
**Only a clean rebuild counts, and after a MACHINE change the incremental
number is not merely optimistic, it is meaningless.**

**WHERE THE NEXT LANE PICKS UP**, in order:

1. `HartMFetch` + `HartPilot` (above) — this is what gates everything.
2. Then the next layer surfaces error-driven: `SmodeCore`, `UserMem`,
   `SmodeCorePt`'s fetch, `PtTreeAdue`/`HartSMem`'s PTE reads, and the
   `Read_ttw` leftovers of the revert (`WpLoad.exec_read_ram_ttw_8`,
   `SmodePte`'s arm reduction, `MemAccessGen.rk_from_flags`/`rk_select_flags`
   + its side condition in `UserMemMis`).  Note `Read_ifetch` SURVIVED the
   unpatching (A6.36), so those twins compile untouched and only go if
   someone wants them gone.
3. A6.37's kit for the kernel-PT walk reads, once the hart-0 question is
   ratified.
4. The A6.33 tail that the overruling interrupted: `WpSconfMem` /
   `WpSconfLock` (re-park `own_context` on the engine's bracket — the
   escape hatch is the leaf's own `Ψ` slot, which a caller may instantiate
   as `Ψ ∗ own_context cur_ctx`, so **no exported statement changes and
   A6.18's textual-invariance test survives**), then
   `WpSmodePtLeaves`/`WpSmodePtMem` with the ratified premise.
5. `CpuOwn:110` (a raw `mem_pointsto_ne` on a ctx byte — M1's error class
   (a), one twin away), `BootCarve` (A6.34's plumbing),
   `WpStartNew`/`UserPtTree`/`TransPt` (A6.27/A6.28 threading), and
   `WpUart` last (A6.29, ruling 1 of the earlier redirect).
6. `PtWalkCert` is MOOT — its planned `MemAccessGen` treatment was A6.7(B)
   fallout and dies with the patch.

### A6.39 THE MEASUREMENT THAT INVALIDATES A6.38's NUMBER: THE MODEL WAS
### REVERTED IN THE SOURCE AND NEVER IN THE BUILD

Found in the first five minutes of the next lane, and it is the reason
A6.38's "244 of 1330, THREE red" must not be carried forward as a
baseline.

    model-xv6iris/rv64d.v    2026-08-26 18:37   (RESTORED to the pinned baseline)
    model-xv6iris/rv64d.vo   2026-08-26 11:15   (the A6.7(B) PATCHED build)

`iris/CoqMakefile` has no rule for the generated model (durable-notes says
so in as many words), so nothing in an `iris/` build ever notices that
`rv64d.v` moved.  Every `.vo` in the tree was consistent **with the other
`.vo` files**, Coq's digest check passed, and the whole clean rebuild ran
green against the model the revert was supposed to have removed.  A6.36's
claim "the generated model is RESTORED to the pinned baseline" is true of
the SOURCE and was never true of anything the proofs were checked against.

**HOW IT SURFACED**, and why it would not have surfaced on its own for a
long time: `HartMFetch`'s re-port restored `read_kind_of_flags` to the
`cbn` delta list, and the goal came back reading `read_ram Read_ifetch`
— a constructor the pinned model still HAS (A6.36's own observation) but
which `read_kind_of_flags false false false` cannot produce.  The two
`md5sum`s of `rv64d.v` (fliptree vs main repo) were identical; the `.vo`
mtime was the tell.

**THE RULE, beside A6.38's stale-`.vo` one.**  A6.38 said only a clean
rebuild counts after a machine change.  That is not sufficient: a clean
rebuild of `iris/` says nothing about `model-xv6iris/`.  **After any edit
under `model-xv6iris/`, rebuild the model FIRST**
(`make -f CoqMakefile` in `model-xv6iris/`, ~40 s) and check
`ls -la model-xv6iris/*.v model-xv6iris/*.vo` — a `.v` newer than its
`.vo` is the whole diagnostic, and it is the same check durable-notes
prescribes after a `git pull` that touches the model.  The failure mode
here is worse than the pull's, because the pull's version eventually dies
at `RiscvLang.v` with a model-field error, while a REVERT that leaves the
old `.vo` in place produces a tree that builds perfectly and proves
statements about the wrong machine.

> **THIS RULE BELONGS IN `durable-notes.md`'s Build section**, beside the
> existing "a `git pull` that touches `model-xv6iris/` means `make model`
> first" bullet — it is the same hazard with a worse failure mode and it is
> not specific to this port.  It is recorded here only because this
> session's write scope was this file; whoever lands the tranche should
> move it.

**WHAT IT COSTS.**  A6.38's 244/1330 is void.  The revert's real fallout
is the A6.7(B) list, which had been recorded as "STILL TO ABSORB" but was
in fact silently green: `RiscvTryStep`, `RiscvFetchExec`, `SmodeCore`,
`UserMem` (the `Read_ifetch` twins and the `(access, res)` reductions),
plus `WpLoad`/`SmodePte`/`MemAccessGen`/`UserMemMis`/`PtTreeAdue`/
`HartMFetch`'s `Read_ttw` mentions.

### A6.40 THE READ-SIDE RE-PORT IS LANDED — AND KERNEL TEXT PAYS WITH A
### PRISTINE RECEIPT BESIDE ITS BYTES, NOT INSTEAD OF THEM

A6.38's two-file frontier, worked in its order.

**`HartMFetch`** — the recipe held exactly.  `swp_checked_mem_read_ifetch4`
and `_ifetch2` go back to `mread_req`/`mread_req2` at
`read_ram Read_plain`, take `swp_hart_ram_read_plain`, and their premise
changes from the flat `⌜read_bytes σ.(mem) pa n = Some bytes⌝` to the
view-indexed

    Definition fobl_ram (img : TsoMemPa.bytemap) (log : list pwmsg)
        (tv : nat) (pa : Arch.pa) (n : N) {m : N} (w : bv m) : Prop :=
      ∀ tv' : nat, (tv <= tv')%nat -> (tv' <= length log)%nat ->
        tso_read_bytes img log (hart_agent cpu_id) tv' pa n w.

— `HartMLoad.robl_ram` at the fetch widths, with the same pass-through
discipline down `swp_fetch_ram` / `_rvc2` / `_base2` (the `_base2` wrapper
carries TWO of them, one per halfword).  The proof scripts are main's
verbatim once `read_kind_of_flags` is back in the `cbn` delta list; the
`Read_ttw` 8-byte twins and the `_ifetch` request twins are DELETED, with
a comment in each place saying what went and why.

**AND THE PAYER IS NAMED IN THE SAME FILE**, because "kernel text is
timestamp 0" is now a resource obligation rather than a ruling:

    Lemma fobl_ram_pristine (img : TsoMemPa.bytemap) (sg : mstate)
        (log : list pwmsg) (V : agent -> nat)
        (pa : Arch.pa) (n : N) {m : N} (w : bv m) (dq : dfrac) (tv : nat) :
      gen_heap_interp (hG := riscv_memGS) sg.(mem) -∗
      tso_interp_of riscv_eraGS img sg.(mem) log V -∗
      ([∗ list] j ∈ seq 0 (N.to_nat n),
         phys_pointsto (pa_add pa j) dq (nth_byte w j)) -∗
      TsoCtx.pristine_win pa (N.to_nat n) -∗
      ⌜fobl_ram img log tv pa n w⌝.

the mirror of `HartMLoad.robl_ram_ctx` one tier down, through
`TsoCtx.pristine_read_bytes_ok` and the A6.1a bridge
(`tso_interp_of_pin` + `tso_interp_of_at_gs` at `gs_of`).  **The shape to
carry upward: a fetch site now owes `↦ₚ` bytes AND a `pristine_win`
receipt.**  The bytes alone are not a load licence and never were — A6.8
said so about `ctx_pointsto_forget`; what changed is that the fetch lane
has joined the tiers that have to say it.

**`HartPilot`** — `hp_fetch_strong` is deleted (it VM-checked the tagging
that no longer happens), `wp_hart_rw_seq` loses the `ak_strong` premise,
and its fetch takes the plain rule with a `TsoCtx.pristine_win` premise
beside the `↦ₚ{dqf}` run.  Both pilot lemmas had no consumers (A6.7), so
this is the re-cut that ruling licensed.

> **ONE TACTIC FINDING, worth the line.**  The A6.1a bridge's
> `rewrite (tso_interp_of_at_gs …)` FAILS inside a whole-instruction WP
> with `Error: _pattern_value_ is used in conclusion` — the goal there
> carries the model's `let '(data, finished, i) := vars in …` loop
> patterns and `rewrite` will not abstract under them.  The fix is not a
> different tactic: state the discharge as its own lemma (`hp_read_pristine`,
> `fobl_ram_pristine`) where the goal is just the `⌜…⌝`, and `iDestruct`
> it at the call site.  That is why both payers above are lemmas and not
> inline scripts, and it is a reason to keep every kit-gate discharge out
> of the middle of a WP.

### A6.41 THE A6.37 RULING (b) HAS NO NODE EITHER — `sfence.vma` REACHES
### THE MACHINE ONLY THROUGH THE `tlb` REGISTER (STOP)

The ratified fix for the hart-0 half was "at whatever outcome node
`execute_SFENCE_VMA` actually reaches the machine through (the
`TlbOp`/flush path — find it), the arm sets
`tv' := max(tv, own_pub h log)`".  I looked for that node.  **There is
none**, and the shape of the finding is A6.7(B)'s exactly: the outcome the
ruling names exists in the INTERFACE and is never emitted by the generated
model.

Four facts, each checked:

1. **`Interface.TlbOp` EXISTS** — `SailStdpp.ConcurrencyInterface`'s
   `outcome` has `Barrier`, `CacheOp` and `TlbOp`, and
   `ConcurrencyInterfaceBuiltins`'s `sail_tlbi` emits
   `Next (TlbOp op) Ret`.  So the concurrency interface has a first-class
   TLB-maintenance node.
2. **`rv64d.v` NEVER EMITS IT.**  `execute_SFENCE_VMA` (`rv64d.v:41179`)
   is `rX_bits`, `read_reg cur_privilege`, `read_reg mstatus`, a TVM
   check, and `flush_TLB`.  `flush_TLB` (`rv64d.v:24735`) is
   `read_reg tlb` (four sites), a `foreach_ZM_up` over the 64 entries,
   `write_reg tlb` on the matching ones, and three PURE callbacks
   (`tlb_flush_begin_callback`/`tlb_flush_callback`/`tlb_flush_end_callback`,
   all `: unit`).  The RISC-V model keeps its TLB in an ARCHITECTURAL
   REGISTER and does its maintenance by register update; it does not use
   the interface's TLB node at all.
3. **KEYING THE DRAIN ON THE `tlb` REGISTER OVER-DRAINS, AND FATALLY.**
   `translate` (`rv64d.v:25236`) calls `lookup_TLB`, which is
   `read_reg tlb`.  So EVERY paged access reads that register: a drain
   there would advance the hart's view to `own_pub` on every S- and
   U-mode load, store and fetch, i.e. it would make the machine
   essentially SC once paging is on.  That is not a conservative
   simplification — a memory model must OVER-approximate the hardware,
   and a machine with fewer behaviours than the hardware makes every
   theorem above it unsound.
4. **KEYING ON THE `tlb` WRITE FAILS IN EXACTLY THE CASE WE NEED.**
   `flush_TLB` writes the register only for entries that MATCH, so an
   `sfence.vma` on a hart whose TLB is empty emits no write at all — and
   hart 0's first `kvminithart` (`main` → `kinit(); kvminit();
   kvminithart();`, before any translation has ever run) is precisely
   that case.

**THE INSTRUCTION-ORDER CHECK THE REDIRECT ASKED FOR: xv6 IS FINE, AND
THAT IS NOT THE PROBLEM.**  `kvminithart()` is

    sfence_vma();                       // "wait for any previous writes
                                        //  to the page table memory to finish"
    w_satp(MAKE_SATP(kernel_pagetable));
    sfence_vma();                       // flush stale entries from the TLB

and the disassembly agrees (`kernel.asm`, `kvminithart` at `0x80000ee4`):

    80000eec:  12000073   sfence.vma          <- the FIRST fence, before
    80000ef0:  00009797   auipc a5,0x9           anything else happens
    80000ef4:  3c87b783   ld    a5,968(a5)    # 8000a2b8 <kernel_pagetable>
    …                     w_satp(...)
    80000f04:  12000073   sfence.vma          <- the SECOND, after satp

so the first hardware walk (the fetch of the instruction after the second
`sfence.vma`, once `satp` is live) happens AFTER both fences.  Had the
drain a node to sit on, it would have sufficed exactly where the ruling
expected.  The blocker is the model, not the program.  (Note the `ld` of
`kernel_pagetable` between them: that is a plain DATA load of a global
hart 0 wrote in `kvminit`, and it is paid by the ctx tier's dirty arm, not
by any of this.)

**WHAT THIS LEAVES, and it needs a ruling.**  A6.37's three options are
now: (a) EXPORT THE AUTHOR (`ledger_msg_at` + `ledger_read_own_ok`) —
unchanged, still small, still additive over existing ghosts, and now the
ONLY one implementable without touching the Sail sources; (b) is a MODEL
change of the same class as the parked A6.7(B) patch (a `sail_tlbi` call
in `flush_TLB`, or a new outcome), so adopting it re-opens exactly the
regeneration cost the overruling was taken to avoid — and note it would
be a SMALLER patch than A6.7(B)'s and would also give the later
de-confliction project its `TlbOp` node for free; (c) stays rejected (the
proof does not edit the program).  **My recommendation flips to (a)**, on
the ground that (b) is no longer "one arm plus a full rebuild" but a
model-source change, and that the surface (a) widens is one persistent
fragment about the log — which the kit already stores, persists at append
and never exposes.

**AND ONE THING (a) DOES NOT COVER, found while checking the other half.**
The SECONDARY-hart route needs the flag read to MINT `view_lb h F`, and
xv6's flag read is `__atomic_load_n(&started, __ATOMIC_ACQUIRE)` — and the
disassembly (`main` at `0x80000e30`) is

    80000e46:  431c        lw    a5,0(a4)
    80000e48:  0230000f    fence r,rw

a plain load plus an acquire fence, NOT an exclusive read.  (The publishing
side is symmetric: `fence rw,w` at `80000edc` then the store —
`fence_drains` correctly declines that one too, a release fence has no
W→R edge either.)  `fence_drains`
correctly declines `r_rw` (no W→R edge), and A6.6(b) mints the receipt
only at the EXCLUSIVE read and the AMO write, so **nothing on that path
mints a receipt today**.  The honest fix is inside the existing design:
`wp_hart_ram_read_plain` already CHOOSES the advanced view `tvn` with the
view authority open, so it can hand back `view_lb h tvn` in its
postcondition at no cost, and the flag-read leaf then argues `F ≤ tvn`
from the VALUE it read (reading `started = 1` at `tvn` when the message
publishing 1 sits at `F` and the reader is not its author forces
`tvn ≥ F` — the MP shape).  That is a `HartEvents` statement change plus
a full rebuild, and it is item 1 of whatever lane picks this up.

### A6.42 THE A6.37 KIT, SECONDARY-HART HALF: LANDED IN `TsoCtx`

The half A6.37 called "fully determined and needs no ruling" is
implemented and green, exactly as written there:

    phys_ledger_at a dq v t := phys_pointsto a dq v ∗ a ↪[ts_name]{dq} t
    phys_ledger_at_ledger  : phys_ledger_at a dq v t ⊢ phys_ledger a dq v
    phys_ledger_of_at      : phys_ledger a dq v ⊢ ∃ t, phys_ledger_at a dq v t
    phys_ledger_at_forget  : phys_ledger_at a dq v t ⊢ phys_pointsto a dq v

    ledger_read_at_ok `{CID} (g : gstate) a dq v (t F : nat) :
      (t ≤ F)%nat ->
      gen_heap_interp g.(gmem) -∗ tso_interp_at riscv_eraGS g -∗
      view_lb view_name loglen_name (hart_agent cpu_id) F -∗
      phys_ledger_at a dq v t -∗
      ⌜∀ tv', (g.(gtv) cpu_id <= tv')%nat ->
         tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv' a = Some v⌝

    ledger_read_ok `{CID} (g : gstate) a (n : N) {m} (w : bv m) dq (F : nat) :
      gen_heap_interp g.(gmem) -∗ tso_interp_at riscv_eraGS g -∗
      view_lb view_name loglen_name (hart_agent cpu_id) F -∗
      ([∗ list] j ∈ seq 0 (N.to_nat n),
         ∃ t, ⌜(t ≤ F)%nat⌝ ∗ phys_ledger_at (pa_add a j) dq (nth_byte w j) t) -∗
      ⌜∀ tv', (g.(gtv) cpu_id <= tv')%nat ->
         tso_read_bytes g.(gimg) g.(glog) (hart_agent cpu_id) tv' a n w⌝

TWO THINGS THE SKETCH DID NOT SAY, both decided by the proof:

- **The timestamp is PER BYTE, under ONE receipt.**  `ledger_read_ok`'s
  premise is `[∗ list] j, ∃ t, ⌜t ≤ F⌝ ∗ …` and not a single `t` for the
  window, because a page-table page is written slot by slot and a common
  timestamp would be a false statement.  The receipt is shared; the
  timestamps are not.
- **The conclusion's lower bound is `g.(gtv) cpu_id`, not `F`**, i.e. it
  is `ctx_phys_load_bytes_ok`'s shape character for character — which is
  what lets a caller feed it to `Mobl_ram_plain` without any arithmetic.
  The proof is `ctx_phys_load_ok`'s CLEAN arm with `llb_valid` replaced by
  `view_auth_valid`: `t ≤ F ≤ avf g h = gtv cpu_id ≤ tv'`, then
  `visibleb_below`.  The DIRTY arm has no counterpart, which is the whole
  point — a context-free fact cannot own a dirty byte.

`kpt_body`'s `⌜t ≤ B⌝` tie is NOT landed: it is a change to `PtTree`'s
tiered slot with a mid-tree cascade, and its consumers
(`KptShare`/`HartSKpt`/`PtTreeAdue`) sit above the frontier, so it is
written where it can be checked against a real error rather than
predicted.

### A6.43 `↦ₓ` CARRIES ITS OWN TIMESTAMP NOW — AND THAT IS WHY THE FETCH
### TIER COST NOTHING ABOVE THE LEAVES

The overruling's real bill lands at the two places a fetch obligation is
DISCHARGED rather than threaded — `InstrBytes.text_fetch_obl` (the M-mode
loop's, from `instr_bytes`' persistent window) and `SmodeCorePt`'s S-mode
twin.  Both held `↦ₓ□` bytes and proved the flat `read_bytes`; neither can
prove the view-indexed fact, because a flat cell says nothing about what a
view below the top sees.  Three shapes were available and the third was
taken:

- thread a `pristine_win` premise from the payer up to the ~135 leaf
  sites — rejected, it is the whole tree;
- add the receipt as a conjunct of `instr_bytes` and mint it in
  `KernelText`'s two intro lemmas — better (≈6 files), but it puts a
  fetch-specific fact in a fetch-specific predicate and leaves `↦ₓ`
  itself still unable to pay;
- **put the DISCARDED timestamp element inside `text_pointsto`** — TAKEN.

      Definition pristine_elem (a : Arch.pa) : iProp Σ := a ↪[ts_name]□ 0%nat.

      text_pointsto va dq v := ∃ ppn, kmap_at (svpn_of va) ppn KP_rx ∗
        ⌜canonical⌝ ∗ ⌜addr_is_text (pa_of ppn va)⌝ ∗
        ⌜ktier_pin cur_ktier ppn va⌝ ∗
        pointsto (pa_of ppn va) dq v ∗
        pristine_elem (pa_of ppn va)                      (* NEW *)

**WHY THIS IS THE HONEST ONE, not merely the cheap one.**  `↦ₓ` means "a
kernel-TEXT byte at a `KP_rx` mapping".  DISCARDED at timestamp 0 says two
things at once — the byte's latest write is the era image (so every agent
at every view reads it) and no store can ever touch it again (a store must
UPDATE the element, which a discarded one forbids).  Both are already what
`↦ₓ` is FOR, so the resource now states its own meaning instead of relying
on a ruling; W^X over the text region becomes a consequence rather than an
assumption.

**AND THE PROPAGATION IS THE POINT.**  `kernel_text` is a `big_sepM` of
`↦ₓ□`; `KernelText.kernel_window_pc` cuts a window out of it;
`InstrBytes.instr_bytes` holds the window; `wp_instr` hands it to the 135
leaf sites.  Every one of those is TEXTUALLY UNCHANGED, and
`text_fetch_obl`'s PREMISE is character for character what it was — only
its conclusion moved.  The whole change is:

  - `RiscvPtsto`: the definition, `pristine_elem` + its two instances, and
    the six destructuring patterns inside the file; `text_pointsto_acc`
    and `text_pointsto_pin` EXPOSE the element (persistent, so their
    give-back wands are unchanged);
  - `HartLift2`: `text_byte_phys_pristine` (one `↦ₓ□` byte → a
    `phys_pointsto` plus a `TsoCtx.pristine_byte`, through the KT0 pin) and
    `text_tso_read_bytes`, the TSO twin of `text_read_bytes`, whose
    conclusion is `∀ agent, ∀ view` — no premise about either;
  - `InstrBytes.text_fetch_obl`: restated at `HartMFetch.fobl_ram`,
    discharged by the above through the A6.1a bridge;
  - `TrampText.tramp_text_mint`: the element travels with the byte (the
    KT1 va and the KT0 identity address name the same physical byte);
  - `KMap.phys_ident_text` and `BootCarve.boot_text_persist`: the ONE new
    obligation, at the one place `↦ₓ` is born from raw memory.  Its
    supplier is the era's initial-state ghost allocation — the same place
    `kernel_data_intro`'s `pristine_va` premise comes from — and its two
    callers (`BootShared`, `RiscvAdequacy`) were already red, so the
    change turned NO green file red.

**THE BINDER TRAP FIRED, AND `pristine_elem` IS THE FIX.**  Spelling the
element inline as `pa ↪[ts_name]□ 0%nat` inside `KMap.v` — a file that
imports `SailStdpp.Base` — fails with `Could not find an instance for
?EqDecision0 : EqDecision (mword 64)`: the Sail key instances elaborate a
fresh binder that will not unify with the stdpp-keyed ghost map.  Same
trap, same fix as `TsoMemPa.bytemap` (A6.38): give the thing a NAME whose
argument type is `Arch.pa`, and use the name everywhere.

**ONE MORE SCRIPT FINDING, cheap and repeated.**  A blind
`sed`/`str.replace` of an `iDestruct` pattern like
`"(Hk1 & _ & _ & _ & Hp1)"` hits `mem_pointsto`'s and `text_pointsto`'s
sites alike — they have the SAME arity — and the resulting failure
(`iAndDestructChoice: cannot destruct (pointsto …)`) names a line
hundreds above the edit.  Count the occurrences before replacing, and
check every one against the `rewrite /..._pointsto` on the line above it.

### A6.44 THE PT-READ LANE IS THREADED, AND THE DISCHARGE IS THE ONE
### DESIGN ITEM LEFT IN IT

`PtTreeAdue`'s two non-exclusive PTE reads (`swp_checked_mem_read_pte8`
and its predicate-indexed twin) take `swp_hart_ram_read_plain` at
`mread_req8` / `Read_plain`, and their obligation is
`fobl_ram img log tv pa 8 bytes` — threaded, not discharged, exactly as
`HartMLoad` threads `robl_ram`.  The `Read_ttw` request twins and their
`hread_*` lemmas are deleted with the patch.  The EXCLUSIVE twin (the A/D
write-back's `read_pte_exclusive`, `res = true`) is untouched: it still
reads at the top and still mints its receipt.

So the kernel-PT read story is now a single named hole at the far end:
whoever OWNS a kernel-PT slot (`KptShare`'s `kpt_body`, `HartSKpt`'s walk
lemmas) must pay `fobl_ram` from A6.42's `ledger_read_ok` — which needs
the `⌜t ≤ B⌝` tie in the slot and a `view_lb` receipt on the reading hart.
For a secondary hart that receipt is the boot MP one (A6.41 records that
the flag read does not mint it yet); for hart 0 it is A6.41's open ruling.

### A6.45 THE PT-SLOT DISCHARGE POINT IS `HartSKpt.kpt_slot_node`, AND IT
### IS THE DESIGN GATE — MEASURED, NOT PREDICTED

Worth naming exactly, because it is the ONE place the kernel-PT read story
has to be paid and everything else in that lane is threading:

    Lemma kpt_slot_node root_ppn t0 vpn p2 p1 p0 a w :
      ptree_maps t0 vpn p2 p1 p0 ->
      (forall σ q0, pt_slot_mem σ … -> … -> pt_slot_mem σ a w) ->
      kpt_lb t0 -∗ kpt_inv root_ppn -∗
      (∀ σ, mstate_interp σ ={⊤,∅}=∗
         ⌜read_bytes σ.(mem) a 8 = Some w⌝ ∗ ▷ (|={∅,⊤}=> mstate_interp σ))

It opens `kpt_inv`, reads the three slots out as PURE `pt_slot_mem` facts
(flat lookups in `σ.(mem)`), closes the invariant immediately — "everything
taken out of it was pure", says the proof — and concludes the flat
`read_bytes`.  Its two pinned specialisations (`kpt_pte2_node`,
`kpt_pte1_node`) are one-liners over it, and `kpt_leaf_node` is the same
shape modulo `pte_canon`.

**WHAT IT NEEDS AND DOES NOT HAVE.**  The obligation is now
`fobl_ram img log tv a 8 w`, and A6.42's `ledger_read_ok` pays it from
`phys_ledger_at a dq w t` ∗ `⌜t ≤ F⌝` ∗ `view_lb h F`.  The slot fact is
there — `kpt_body`'s tier is `phys_ledger` (A6.20), so the element comes
out of the same opening as `∃ t, phys_ledger_at …` via
`phys_ledger_of_at`.  What is missing is the pair `⌜t ≤ B⌝` (the
`kpt_body` tie A6.37 specified, not yet landed) and a `view_lb` receipt on
the reading hart, which is A6.41's open ruling for hart 0 and A6.41's
unminted flag-read receipt for the secondaries.  **And there is no
context-shaped escape**: `ctx_phys_load_bytes_ok` wants `own_context ξ`
and A6.20's ruling makes `kpt_inv` context-FREE on purpose (a bare `inv`
shared by every S-mode thread cannot name a context), so the walk cannot
borrow the walker's token.  The gate is real.

### A6.46 HANDOFF AFTER THE READ-SIDE TRANCHE

**THE CLOSING CLEAN BUILD: 522 ATTEMPTED, 516 `.vo`, 6 ERRORS**
(`iris/*.vo` deleted first, one `make -f CoqMakefile -j12 -k`; the three
counts are self-consistent — 522 − 6 = 516 — so nothing was silently
skipped, and `ls -la model-xv6iris/*.v *.vo` was checked: the model `.vo`
now POSTDATES its source, which is the check A6.39 exists for).

> **516 of 1330, SIX red.**  Not comparable to A6.38's 244 (that number was
> measured against the patched model and is void, A6.39) and not comparable
> to A6.35's 550 either (that one predates the overruling).  The honest
> reading is the frontier's shape: the fetch tier is GREEN to its top, the
> PT-read lane is threaded down to one discharge point, and the six red
> files are five known items plus the one design gate.

**WHAT LANDED, in the order it was worked:**

1. The model `.vo` was actually reverted (A6.39) — without this nothing
   else in the tranche means anything.
2. `HartMFetch` + `HartPilot` (A6.40), and the A6.7(B) revert leftovers it
   dragged in: `RiscvTryStep`, `RiscvFetchExec`, `SmodeCore`, `UserMem`,
   `WpLoad`, `MemAccessGen`, `UserMemMis`, `SmodePte` — every one of them
   reverted to the MAIN REPO's text, because a `diff` showed the fliptree
   copy differed from main by the A6.7(B) hunks and nothing else.  That
   `diff` against `/shared/xv6iris-3/iris/<f>.v` is the cheapest tool in
   this whole tranche and it should be the FIRST thing tried on any file
   whose only red is patch fallout.
3. A6.42's `TsoCtx` kit (the `phys_ledger_at` family + `ledger_read_ok`).
4. `HartMRun` (10 pass-through premises, one regex), `HartMLoad` /
   `HartSMem` (the plain rule lost a positional argument when `ak_strong`
   died — A6.36 said so and three call sites still had it).
5. A6.43's `↦ₓ`-carries-its-timestamp change, and with it `WpInstrRun`,
   `KMap`, `TrampText`, `BootCarve`'s text half, `HartLift2`, `InstrBytes`.
6. `PtTreeAdue`'s two PTE reads (A6.44).

**WHAT IS RED, and what each one is:**

- `HartSKpt` — **the design gate (A6.45)**, and the only one that needs a
  ruling.  Everything else in the S-mode PT lane is behind it
  (`SRegime` → `SmodeCorePt` → `IntrDefs` → the whole S-mode tier).
- `BootCarve` — A6.34's carve plumbing, unchanged and still mechanical.
- `TransPt`, `UserPtTree`, `WpStartNew` — A6.27/A6.28's threading
  (`↦ₚₜ` vs `↦ₚ₈`, the `S`-payer's shape at the boot store sites).
- `WpUart` — A6.29, unchanged: the DMA completion's append with a
  NON-EMPTY write set.  Not attempted this tranche, and the reason is the
  one A6.29 already gave: closing it needs `virtio_proto_step` turned
  inside out into an accessor, which is a device-conformance-tier
  statement change, not re-plumbing.

**ONE PIECE OF UNVERIFIED WORK, flagged because it cannot be compiled
where it stands.**  `SmodeCorePt`'s re-port is WRITTEN — the two S-mode
fetch leaves move to `swp_hart_ram_read_plain` (they still called the
pre-split `swp_hart_ram_read`, a name that has not existed since A6.6), and
`s_text_obl` is restated at `fobl_ram` with a new `s_text_byte` doing the
per-byte extraction of the `pointsto` AND the pristine element at the
TRANSLATED address (`svpn_of_pa_add` + `kmap_at_agree` + `pa_of_pa_add`,
`s_fetch_chunk`'s own three steps).  It sits behind `SRegime`, hence behind
`HartSKpt`, so **it has never been type-checked**.  Keeping it is strictly
better than reverting — without it the file is certainly broken — but the
first thing to do after `HartSKpt` goes green is compile it and expect
work.

**WHERE THE NEXT LANE PICKS UP:**

1. **The A6.41 ruling** (hart 0's forwarding: export the author, or patch
   the model to emit `TlbOp`).  Nothing in the kernel-PT lane moves without
   it.
2. With it: the `kpt_body` `⌜t ≤ B⌝` tie (A6.37), the flag-read receipt
   mint (A6.41's last paragraph — `wp_hart_ram_read_plain` hands back
   `view_lb h tvn`), and `HartSKpt.kpt_slot_node` on `ledger_read_ok`.
   Then `SmodeCorePt` (above), then the S-mode tier surfaces
   error-driven.
3. `TransPt`/`UserPtTree`/`WpStartNew` (A6.27/A6.28) and `BootCarve`
   (A6.34) are independent of all of that and can be worked in parallel.
4. `WpUart` last, on its own ruling.

### A6.47 THE OWNER'S RE-RULING: (b) WITHDRAWN, (a) RATIFIED, THE PLAIN
### ARM MINTS — BOTH LANDED, AND RULING 3's PREMISE IS REFUTED

A6.37(b) is WITHDRAWN by the owner as refuted by A6.41's measurement (its
premise was that an arm existed to change).  Four rulings came back; the
first two are implemented and green, the third is stopped on a measured
falsity, the fourth is scoped.

**RULING 1 — THE AUTHOR EXPORT, LANDED.**  `TsoCtx` gains, all additive
over ghosts that already existed:

    ledger_msg_at i m  :=  i ↪[logm_name]□ m            (persistent, timeless)

    ledger_vis h B t   :=  ⌜(t ≤ B)%nat⌝
                        ∨ ∃ i m, ⌜t = S i⌝ ∗ ledger_msg_at i m ∗ ⌜pm_tid m = h⌝
      (+ ledger_vis_below / ledger_vis_own / ledger_vis_mono)

    ledger_read_vis_ok `{CID} (g : gstate) a dq v (t B : nat) :
      gen_heap_interp g.(gmem) -∗ tso_interp_at riscv_eraGS g -∗
      view_lb view_name loglen_name (hart_agent cpu_id) B -∗
      ledger_vis (hart_agent cpu_id) B t -∗
      phys_ledger_at a dq v t -∗
      ⌜∀ tv', (g.(gtv) cpu_id <= tv')%nat ->
         tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv' a = Some v⌝
      (+ ledger_read_bytes_vis_ok, the window form)

**`ledger_vis`'s two arms ARE `TsoMemPa.visibleb`'s two**, which is what
makes this ONE gate for both routes — the thing the withdrawn (b) wanted
and this delivers without touching the machine: a secondary uses
`ledger_vis_below` with the boot receipt, hart 0 uses `ledger_vis_own` with
the author fragment its own store handed back, and nothing downstream has
to know which.  (`view_lb_0` makes the receipt free at `B = 0`, i.e. the
pure-forwarding case.)  Structurally it is `TsoGhost.dirty_ok`'s
disjunction lifted off the dirty set — the twin already had this shape for
the CONTEXT's dirty bytes; ruling 1 is that same idea made available
without a context.

The producer side moved with it.  `ledger_store_bytes` and `ledger_store_ok`
now return the window at the NEW timestamp (`phys_ledger_at … (S (length
g.(glog)))`) and **`ledger_store_ok` keeps the persistent log fragment it
used to discard** (`ghost_map_insert_persist … as "[Hm #Hmsg]"` — the
fragment was always minted, it was just thrown away) and hands it back as
`ledger_msg_at (length g.(glog)) (PWMsg Pnew auth)`.  `ledger_store_win_ok`
is UNCHANGED (it weakens back internally with `phys_ledger_at_ledger`, so
its existing `Wobl_ram` payers do not move) and a strengthened
`ledger_store_win_at_ok` sits beside it for the writers that want the tie.

**RULING 2 — THE PLAIN ARM'S RECEIPT, LANDED, AND THE SHAPE IS THE
INTERESTING PART.**  The receipt cannot be handed to the callback: the
machine picks `tvn` in `mnode_step`, which runs AFTER the callback's first
fupd, and the callback has already given the bundle away by then.  It also
cannot be handed to the callback's returned bundle, because the rule
advances that bundle afterwards.  What works is to make the callback hand
back a WP **parameterised by** the receipt:

    ▷ (|={∅,⊤}=> mstate_interp σ ∗ tso_interp_of riscv_eraGS img σ.(mem) log V ∗
         (∀ tvn : nat, ⌜(tv <= tvn)%nat⌝ -∗ ⌜(tvn <= length log)%nat⌝ -∗
            view_lb view_name loglen_name (hart_agent cpu_id) tvn -∗
            WP …))

The rule then advances, mints with `tso_interp_of_receipt_at` at
`vstep_here` (a one-line pure lemma added to `HartEvents`), and applies.
**A consumer that does not want it writes `iIntros (tvn _ _) "_"` and is
otherwise unchanged** — which is exactly what the ten existing call sites
did (`HartMFetch` ×2, `HartMLoad`, `HartMemRun`, `HartPilot`, `HartSMem`'s
two `Local Ltac`s, `SmodeCorePt` ×2, `PtTreeAdue` ×2).  The
value-implies-position step stays in the proofs, per the ruling.

**RULING 3 — STOPPED, BECAUSE `⌜t ≤ B⌝` IS FALSE.**  The tie A6.37
specified for `kpt_body` says every kernel-PT slot's LATEST write is at or
below the boot bound.  **The Svadu A/D write-back refutes it**: it is a
real store to a PT slot, performed by whichever hart took the access, at a
timestamp far above `B`.  After one of them, a slot's `phys_ledger_at`
timestamp `t` exceeds `B`, and `ledger_read_vis_ok` — which needs
`t ≤ B ≤ gtv` — no longer applies to any OTHER hart, which has neither the
bound nor the author fragment.

A6.37's justification for not needing history ("the A/D write-back is
itself a `ledger_store_ok` under the same `kptN` invariant, so it cannot
interleave inside an opening") is true and does not help: it rules out
interleaving DURING an opening, not a reader whose view predates a
COMPLETED write-back.  And the reader is not in trouble semantically — it
reads an older version, which is `pte_canon`-equal, which is all the
certificate claims (`kpt_leaf_node_canon`).  The gap is that
`phys_ledger_at` only knows the LATEST write, so the ledger gate cannot
say anything about the older one.

> **WHAT THE HONEST INVARIANT IS: a per-address HISTORY fact.**  "Every
> message ever appended that touches this slot is canon-equal to the
> pinned value."  It is now EXPRESSIBLE without new machinery, because
> ruling 1 exported `ledger_msg_at`: a growing big-op
> `[∗ list] i ∈ seq 0 W, ∃ m, ledger_msg_at i m ∗ ⌜a ∈ dom (pm_map m) →
> pte_canon (…) = pte_canon w⌝` over the log prefix, re-established at
> each `ledger_store_ok` (which now hands its own message back, so the new
> element is free) and carried in `kpt_body` beside `kpt_lb`.  That is
> real machinery, it is the piece A6.37 said was unnecessary, and it
> should be ruled on before it is built.

**AND THE ARITY COST WAS MEASURED TOO**, because A6.37 also asked for `B`
as a parameter of `kpt_inv`: `kpt_inv` has ~130 mention sites across **35
files** (`SpecMain`, `TransPt`, `UsertrapRes`, `UservecExitPt`, `WpSFrames`
… ), most of them spec files that carry it as a persistent hypothesis.
An arity change there is a tree-wide sweep, and it should not be paid
until the invariant's CONTENT is settled — the history fact above may want
a different parameterisation (a bound is the wrong shape for a history).

**RULING 4 — SCOPED, NOT STARTED, and the shape is measured.**  The
broader approval is recorded: internal restructuring of
`virtio_proto_step` and the lease family is PRE-APPROVED, and the stop
condition is only a conformance-suite statement move.  What the work is:

  - `VirtioProto.phys_map` / `phys_list` and `WpVirtio.dma_own` are
    `[∗ map] a ↦ b ∈ …, phys_pointsto a (DfracOwn 1) b` — the flip is to
    `TsoCtx.phys_ledger`, and it is the ~185 occurrences;
  - `VirtioProto.virtio_proto_step` (`:1795`) hands back
    `perm_done … -∗ gen_heap_interp (w ∪ m) ∗ disk_img_auth … ∗ virtio_proto γ v'`
    — i.e. it PERFORMS the gen_heap update.  That is what cannot stand:
    `ledger_store_ok` moves `gen_heap_interp` and `tso_interp_at`
    TOGETHER (the interp's own tie relates the flat cell to the ledger
    element), so the update has to happen at the caller.  Inside out means
    handing the write set's OLD bytes out as `phys_ledger` and taking the
    NEW ones back, with `WpUart.wp_disk_loop` doing the
    `ledger_store_ok` between.

Not started because it is a multi-file restructuring of a 2000-line
protocol file and half of it is worse than none.  Nothing gates it now.

**THE NUMBER: the red set did NOT move, and that is the result.**  The
sweep after rulings 1+2 rebuilt 418 files and produced the SAME six red
(`BootCarve`, `HartSKpt`, `TransPt`, `UserPtTree`, `WpStartNew`,
`WpUart`) — so both rulings landed with zero collateral, which is what a
receipt that a consumer may drop and an export that nobody yet consumes
should cost.  **The closing MODEL-AWARE CLEAN REBUILD reproduces it
exactly: 522 attempted, 516 `.vo`, 6 errors** (`iris/*.vo` deleted first;
`ls -la model-xv6iris/*.v *.vo` checked FIRST per A6.39 — the model `.vo`
postdates its source — and the three counts are self-consistent,
522 − 6 = 516).  Two independent builds, one incremental and one clean,
agreeing on the same 516/6 is the strongest form of the integrity check
this project has.

**WHERE THE NEXT LANE PICKS UP, revised:**

1. **The history-invariant ruling** (ruling 3's replacement, above).  It
   is the only thing gating `HartSKpt` and therefore the entire S-mode PT
   tier (`SRegime` → `SmodeCorePt` → `IntrDefs` → …), including the
   unverified `SmodeCorePt` re-port A6.46 flags.
2. `WpUart` (ruling 4, pre-approved, ungated).
3. `TransPt` / `UserPtTree` / `WpStartNew` (A6.27/A6.28) and `BootCarve`
   (A6.34) — independent of both, and independent of each other.
4. The flag-read receipt itself is now cheap: `wp_hart_ram_read_plain`
   mints `view_lb h tvn`, so the boot MP proof is
   "read 1 at `tvn`; the message publishing 1 is at `F`; I am not its
   author; hence `F ≤ tvn`; hence `view_lb h F` by `view_lb_le`" — no
   machinery, only the per-proof step the ruling left in the proofs.

### A6.48 THE UNGATED TRANCHE: `WpUart` IS CLOSED, AND THE PT THREADING
### IS THROUGH — WITH ONE MEASUREMENT THAT WAS NOT IN THE PLAN

Ruling 3's refutation went to a design-analysis lane; `HartSKpt` and
everything behind it stayed parked and UNTOUCHED, exactly as A6.45/A6.47
characterise them.  What follows is the ungated work.

**(1) `WpUart` IS GREEN.  A6.28/A6.29's DMA-completion append is PAID.**
The restructure was smaller than A6.29 feared, because the whole byte
family bottoms out in three definitions and the update happens in exactly
ONE place.

- **The lease flips tier in three lines.**  `WpVirtio.dma_own`,
  `VirtioProto.phys_map` / `phys_list` (and `phys_word2`/`phys_word4`) go
  from `phys_pointsto` to `TsoCtx.phys_ledger`.  A blanket rename inside
  `VirtioProto.v` (16 occurrences) needed **exactly one proof fix** —
  `phys_map_disj`, which unfolded the points-to to reach `pointsto_ne`;
  the sealed tier wants a law, so `TsoCtx` gained `phys_ledger_ne` (and
  `phys_ledger_ram`, its companion).  Every other lemma in that family is
  big-op algebra and did not notice.
- **`dma_update` becomes `dma_acc`, and `virtio_proto_step` turns inside
  out.**  The old shape handed back `gen_heap_interp (w ∪ m)` — it did the
  write.  It cannot, because `ledger_store_ok` moves `gen_heap_interp` and
  `tso_interp_at` TOGETHER.  The new shape hands the write set's OLD bytes
  out at the ledger tier and takes the NEW ones back:

      virtio_proto_step … ==∗
        ∃ kq wr (old : gmap Arch.pa (bv 8)),
          ⌜v_disk v' = wr_apply None (v_disk v)⌝ ∗ ⌜dom old = dom w⌝ ∗
          gen_heap_interp m ∗                       (* in and back, UNTOUCHED *)
          ([∗ map] a ↦ b ∈ old, phys_ledger a (DfracOwn 1) b) ∗
          perm_pend (dn_perm γ) kq wr ∅ ∗
          (perm_done (dn_perm γ) kq wr -∗
             ([∗ map] a ↦ b ∈ w, phys_ledger a (DfracOwn 1) b) -∗
             disk_img_auth (dn_img γ) (v_disk v') ∗ virtio_proto γ v')

  `WpVirtio.virtio_lease_acc` is the same reshape one tier down.
- **`WpUart.wp_disk_loop` performs the store**, in one `iAssert` that
  produces `gen_heap_interp (w ∪ m)`, the bundle at the appended log and
  the new bytes; A6.11's log disjunct picks the arm
  (`tso_interp_of_disk_idle` when `W = ∅`, `ledger_store_ok` at
  `disk_agent` otherwise, through the A6.1a `gs_of` bridge).
- **AND THE LEASE NEVER LEAVES THE LEDGER IN THE FIRST PLACE.**
  `DiskInv.mem_win_to_phys` used to `ctx_pointsto_forget` the driver's
  window on the way to the device tier.  It does not any more:
  `ctx_ident_ledger` (new, in `DiskInv`) takes `↦ₘ` → `ctx_phys_pointsto`
  → `phys_ledger` through `ctx_pointsto_to_phys` + the static claim, so
  the timestamp element travels with the byte — which is the whole reason
  the completion can pay its own append.  A6.9's sentence is unchanged as
  a statement (raw → ctx is still impossible); what changed is that this
  path was never raw.  The reverse bridges (`phys_win_to_mem`,
  `phys_to_byte`) `phys_ledger_forget` at the top and land at the raw VA
  byte as before.
- **ONE SPURIOUS BINDER FOUND BY THE DISK.**  `ledger_store_ok` carried
  `` `{CID : CpuId} `` and never used it — the author is a parameter.  The
  disk agent is not a hart and has no ambient `cpu_id` to offer, so the
  binder had to go; it failed as an unresolved `CpuId` at `Qed`, i.e. as
  "attempt to save an incomplete proof" with NO focused goals, which
  `Unshelve` is what diagnoses.

**(2) THE A6.27/A6.28 THREADING IS THROUGH: `UserPtTree`, `WpStartNew`,
`TransPt` are all green.**

- `UserPtTree.utlb_inv_pt_translateAddr_u` just needed `UptTree`'s
  template — the `S`-payer parameter plus the `□` wand and `S σ.(mem)` /
  `S σ'.(mem)`.  **This is the highest-leverage file in the tranche: 377
  dependents.**
- `WpStartNew.wp_start` gains `own_context cur_ctx`, threaded in and back
  out, because the M-mode boot stack is a ledger region (A6.17) and its
  two prologue stores owe the append.
- **`TransPt` needed TWO payers, and that was not in the plan.**  Its
  `_kcur` / `_kprev` wrappers walk BOTH trees — the user tree at the
  `Some ξ` tier and the SHARED KERNEL tree at the `None` tier
  (`kptree_own`).  A kernel-tree A/D write-back is a context-FREE ledger
  store (A6.20: its owner is a bare `inv`, so it can name no context), so
  it needs its own currency at `TsoCtx.phys_ledger_word`, not
  `ctx_phys_word_pointsto`.  **Two payers, one per tier, in one lemma** is
  the honest shape, and the tier-generic `_at` forms
  (`ptree_own_path_mem_at None`, `ptree_own_path_upd_at None`) are what
  the proof needed at the kernel sites.  `TransPt.kpt_frame` was also
  still spelled at the ctx tier and is now `pt_frame_at None`.

**(3) `BootCarve` — NOT ATTEMPTED, and here is the scoped shape** so the
next lane does not re-derive it.  `boot_stack_own_phys` must produce
`stack_own_phys` = `ctx_phys_word_pointsto XI`, and
`ctx_phys_pointsto_of_elem` builds that from `phys_pointsto` +
`ledger_elem0`.  So the carve needs an ELEMENT big-op over the same
`ran_bytes` map, split in step with `boot_raw_ran`:

    boot_led_ran g lo hi := [∗ map] a ↦ _ ∈ ran_bytes g lo hi,
                              ledger_elem0 a (DfracOwn 1)
    boot_led_split  — [boot_ran_split]'s proof verbatim
                      (ran_bytes_union + big_sepM_union + ran_bytes_disj)
    boot_led_word   — [boot_ran_word]'s byte extraction at the element

plus a `CurCtx` binder on `boot_stack_own_phys` and the pointwise
conversion.  Its supplier is the era's initial-state ghost allocation, so
the new premise lands on `BootShared` / `RiscvAdequacy` — both already
red.  It is ~60 lines of big-op work and it is the only reason `BootCarve`
is red.

**WHAT `WpUart` GOING GREEN REVEALED, and it is the useful measurement.**
Closing one deep file opened a cone that had never been compiled, and the
new red files are NOT new breakage — they are files reached for the first
time, each with an M1-class error the flip left in them.  Fixed as they
surfaced: `FileInvDefs` (`mem_pointsto_ne` on a `↦₄` tower → the twin
`ctx_pointsto_ne`), `FileInv` (two `ctx_word{2,4}_pointsto_frac_split`
calls missing the `ξ` placeholder).  **The rule: after a deep file goes
green, budget one cheap M1 fix per newly-reached file, and expect the red
COUNT to rise while the green count rises faster.**

**THE CLOSING MODEL-AWARE CLEAN REBUILD: 542 ATTEMPTED, 535 `.vo`, 7
ERRORS** (`iris/*.vo` deleted first; `ls -la model-xv6iris/*.v *.vo`
checked FIRST per A6.39 — the model `.vo` at 19:11 postdates its source at
18:37; 542 − 7 = 535, self-consistent).

> **535 of 1330, SEVEN red, up from A6.47's 516/6.**  The red COUNT rose
> and the green count rose faster, which is A6.25's rule running the
> favourable way for once: `WpUart` and `UserPtTree` were both frontier
> files, so closing them exposed tiers that had never been compiled at
> all.  Every one of the four new red files is a first-time-reached file
> with an M1-class error, not a regression.

**STILL RED — eight attempted-and-failed, plus `WpSconfMem`'s termination.
Four of the eight were EDITED after the sweep had already given up on them
(`WpSmodePtMemWrap`, `ProcInv`, `FsLookup`, `RiscvAdequacy`), so their next
compile is the first real news about them:**

- `HartSKpt` — PARKED on the history-invariant ruling (A6.45/A6.47), with
  `SmodeCorePt`'s unverified re-port behind it.  Untouched.
- `BootCarve` — A6.34, scoped above.
- `ProofEntry` — one premise: `wp_start` now takes `own_context cur_ctx`,
  so its boot-chain caller must supply it (`BootChain.boot_entry_bridge`
  holds one).  Same family as (2), one file further up.
- `ProcPtOwn` / `UmodeMem` / `UserBytes` / `UserMemPt` — the user-memory
  tier, newly reached behind `UserPtTree` and each an independent
  M1/tier-spelling item: `ProcPtOwn` still calls the deleted
  `TsoCtxShim.ctx_pointsto_of_mem`; `UserBytes` needed
  `rewrite /pt_slot_own; cbn match` to expose the `Some ξ` tier at
  `pt_page_own_maps` (landed) and has a second `bytes_own`-tier framing
  step left.  **These four gate the 377-file cone under `UserPtTree` and
  are the cheapest large win available.**

### A6.49 THE USER-MEMORY TIER IS FORCED, NOT CHOSEN — AND THE FOUR
### FILES A6.48 NAMED FALL OUT OF ONE SPELLING

A6.48 called `ProcPtOwn` / `UmodeMem` / `UserBytes` / `UserMemPt` four
independent M1/tier-spelling items.  They are ONE item, and the tier is
not a choice: `HartMemRun.bytes_own` is already
`[∗ map] a ↦ b ∈ mm, TsoCtx.ctx_phys_pointsto XI a (DfracOwn 1) b` (it had
to move when the plain load started owing `Mobl_ram_plain` and the store
started owing the append), and `UserBytes.umem_any_bytes` /
`umem_any_of_bytes` are a bijective RE-KEYING of the same cells.  Two
tiers cannot be re-keyed into each other, so `UserPtTree.umem_own` and
`udata_own` must sit at `ctx_phys_pointsto XI` too.

**AND THE RE-KEYING COSTS NOTHING.**  `UserPtTree` is the 377-dependent
file; its twelve `↦ₚ` occurrences are all inside `umem_own` / `udata_own`
and their big-op algebra, which never unfolds the cell.  Flipping the
spelling compiled with **zero proof changes**.  `UserBytes` was two
`bigset_gather_reindex` predicate arguments.

`ProcPtOwn` is the interesting one, because it is where the tier CROSSES.

> **THE KALLOC BOUNDARY IS AN ISOMORPHISM, and the old route was the
> wrong one.**  `page_own_to_phys` used to go `ctx_pointsto` →(forget)→
> raw `↦ₘ` →`KMap.mem_ident_phys`→ raw `↦ₚ`, and `phys_to_page_own` came
> back through the deleted `TsoCtxShim.ctx_pointsto_of_mem` — a mint
> A6.9 forbids.  At the ledger tier the crossing is
> `TsoCtx.ctx_pointsto_to_phys` / `ctx_pointsto_of_phys`, the SAME pair
> `KptTree` uses for a PT slot: the timestamp element and the clean/dirty
> bit ride through in both directions.  Landed as `ProcPtOwn.ctx_ident_phys`
> / `phys_ident_ctx` (the identity-mapped-kdata specialisation, off
> `kmap_static_claims_at` + `pa_of_id` + `ktier_pin_of_id`), and the four
> crossings (`page_own_to_phys`, `phys_to_page_own`, `win_mem_to_phys`,
> `win_phys_to_mem`) all go through them.  `ProcPtOwn` no longer mentions
> `TsoCtxShim` at all.

Also landed with it: `TsoCtx.ctx_phys_pointsto_ne` (the exclusivity law
`UmodeMem.umem_inj` needs — the sealed tier wants a law, A6.48's
`phys_map_disj` precedent) and `ProcPtOwn.phys_page_own_dup` off it.

**`ProofEntry` IS GREEN, and the premise it needed was TWO.**  A6.48
named `own_context cur_ctx`; `wp_entry` also wants A6.10's
`TsoCtx.pristine_win entry_ld_ea 8` (the `stack0` word is a link-time
constant read by an M-mode load).  Both are now premises of
`SpecEntry.wp_entry_boot_body`, and `own_context` comes back in its
continuation.  **This is a SPEC change above the kit** and is recorded
here as such: the supplier of both is `BootChain.boot_entry_bridge` /
the era's initial-state ghosts, i.e. the already-red boot lane.

**`BootCarve` IS GREEN.**  A6.48's scope was right to the line.  The
section took a `Context `{XI : TsoCtx.CurCtx}` (only the lemmas that
mention it pick it up), and the element family is
`boot_led_ran` / `boot_led_split` / `boot_led_bytes` / `boot_led_word`
(`boot_ran_split`'s and `boot_ran_bytes`' proofs verbatim over
`TsoCtx.ledger_elem0`) plus `boot_ctx_phys_word`, which pairs a raw boot
word with its eight elements through `ctx_phys_pointsto_of_elem`.
`boot_stack_own_phys` now takes `boot_led_ran g (uint sp − 8n) (uint sp)`
as a second resource.  **NOTHING MINTS AN ELEMENT** — the family only
cuts the era's big-op in step with `boot_raw_ran`'s.  The new premise
lands on `BootShared` / `RiscvAdequacy`, as scoped.

**WHAT THE CONE OPENED, and A6.48's rule ran again.**  Fixed as they
surfaced: `UmodeCap` (a missing `CurCtx` binder — `uv_trap_frame` mentions
it now), `UmodeFetch`'s `umem_fetch_byte` (`phys_valid` on a registered
byte → `ctx_phys_pointsto_forget` first), and `PtFree` (a `CurCtx` binder
plus the `↦ₚ₈` → `ctx_phys_word_pointsto XI` spelling on `pt_slots_any_phys`
/ `pt_slots_kfree_pre` — freewalk's loose node slots come out of
`pt_slot_own (Some ξ)`, which IS that tier, so the flip makes the caller's
job easier rather than harder).
**Characterised and NOT attempted** (they are lane items, not one-line M1
fixes):

- **`UserMemPt` — the user-execution STORE lane owes the append.**
  `udata_own_upd` (`:409`) does the gen_heap update itself with
  `phys_update`, which a ledger byte may not: `ledger_store_ok` moves
  `gen_heap_interp` and `tso_interp_at` TOGETHER.  The shape it must take
  is `HartMemRun.bytes_own_wobl`'s, verbatim one tier over — take
  `tso_interp_of` + `own_context XI`, give them back at the appended log.
  The threading then runs `udata_own_store_g` → `user_pt_store_data_g` →
  `UserMemAccess.split_store_fold` → `UserMemMis`, i.e. A6.27/A6.28's
  `S`-payer template applied to the user-store lane.  Four files.
- **`RiscvAdequacy` — newly reached behind `BootCarve`**, and its error is
  the pre-existing one A6.48 predicted (the era ghost allocation: `:634`
  fails on `riscvEraGS`'s arity, and `era_ts_name` is still never
  allocated).  Step 6 of §7, unchanged.

### A6.50 THE CANON PIN: THE MACHINE HALF IS BUILT AND GREEN

The pin memo's three rulings are implemented from `TsoMemPa` up to
`TsoCtx`, and the closing sweep says the cost is what the memo predicted.

**§5.5's ONE UNPROBED PURE STEP IS GREEN, first try, and it is smaller
than the memo estimated.**  Probed against `PtAdBits.vo`, then ported into
`PtAdBits.v` itself (which now `Require`s `RiscvModelBytes` for
`nth_byte` / `bv_eq_of_bytes`):

    nth_byte_testbit          the byte projection, bit by bit
    pte_set_ad_nth_byte_high  (1 ≤ j < 8) -> nth_byte (pte_set_ad w a d) j
                              = nth_byte w j          -- §2 AT THE BYTE
    pte_bytes_canon           byte 0 in the A/D class + bytes 1..7 the
                              leaf's own  ->  pte_canon w = pte_canon leaf0
    pte_byte0_class{,_self,_set_ad}   the four-element class, and its two
                              inhabitants: the mint's and the store's

25 lines, not 40–60: once `pte_set_ad_nth_byte_high` is stated at the
byte, the reassembly IS `bv_eq_of_bytes` + `pte_canon_set_ad`.

**THE ELEMENT-CARRIED PIN, LANDED (ruling 2).**  `TsoMemPa` gained the
pure layer (the archived probe's four lemmas verbatim, plus
`pin_ok_mono`), and — NAMED THERE, for the `bytemap` binder-trap reason —

    ts_elem := nat * option (gset (bv 8) * nat)
    ts_ok img mem log a e :=
      (∃ v, mem !! a = Some v ∧ latest img log a e.1 v)
      ∧ (∀ Sv B, e.2 = Some (Sv, B) -> pin_ok img log a B Sv)

**ONE interp conjunct, not two.**  The memo drew the pin tie as a new
conjunct beside the latest tie; bundling them into `ts_ok` keeps every
positional destructuring of `tso_interp_of` (`(_&_&_&_&_&_&_&_&%Hb&_)` in
`HartLift` / `HartSpan` / `HartLift2`, the nine named ones in `TsoCtx`)
textually unchanged.  That is the difference between a 4-site edit and a
20-site one, and it costs two projections (`ts_ok_latest` / `ts_ok_pin`).

`TsoGhost.tsomem_tsG` is now `ghost_mapG Σ Arch.pa TsoMemPa.ts_elem`.  The
six sealed definitions pin the option to `None`
(`ctx_pointsto_def`, `ctx_phys_pointsto_def`, `phys_ledger_def`,
`phys_ledger_at`, `pristine_byte`, `ledger_elem0`, plus
`RiscvPtsto.pristine_elem`), and both auth updates write `(S i, None)`.

**THE MEMO'S CENTRAL CLAIM HELD: every existing store gate is sound with
NO new premise.**  In `ctx_store_ok` / `ledger_store_ok`'s tie
reconstruction the pinned half is discharged by `pin_ok_app_frame` off the
footprint (the payer's element is `None` by definition, so no pinned
address can be in it) and is vacuous on it.  Two proof lines each.

**THE THREE GATES, in `TsoCtx`:**

    phys_ledger_pin a dq v t B Sv := phys_pointsto a dq v ∗
                                     a ↪[ts_name]{dq} (t, Some (Sv, B))
    pin_map_own Pv dq B Sf         := [∗ map] a ↦ v ∈ Pv,
                                        ∃ t, phys_ledger_pin a dq v t B (Sf a)

    ledger_pin_mint g a v t B Sv :
      (t ≤ B)%nat -> v ∈ Sv ->
      gen_heap_interp g.(gmem) -∗ tso_interp_at riscv_eraGS g -∗
      phys_ledger_at a (DfracOwn 1) v t ==∗
      gen_heap_interp g.(gmem) ∗ tso_interp_at riscv_eraGS g ∗
      phys_ledger_pin a (DfracOwn 1) v t B Sv

    ledger_read_pin_ok `{CID} g a dq v t B Sv :
      tso_interp_at riscv_eraGS g -∗
      view_lb view_name loglen_name (hart_agent cpu_id) B -∗
      phys_ledger_pin a dq v t B Sv -∗
      ⌜∀ (h : agent) (tv' : nat), (g.(gtv) cpu_id ≤ tv')%nat ->
         ∃ b, tso_read g.(gimg) g.(glog) h tv' a = Some b ∧ b ∈ Sv⌝
      (+ ledger_read_pin_bytes_ok, the window form)

    ledger_store_pin_ok g g' auth Pold Pnew B Sf :
      dom Pold = dom Pnew ->
      (∀ a v, Pnew !! a = Some v -> v ∈ Sf a) ->      (* THE ONE NEW PREMISE *)
      … the same five gstate equations as [ledger_store_ok] …
      gen_heap_interp g.(gmem) -∗ tso_interp_at riscv_eraGS g -∗
      pin_map_own Pold (DfracOwn 1) B Sf ==∗
      gen_heap_interp g'.(gmem) ∗ tso_interp_at riscv_eraGS g' ∗
      ledger_msg_at (length g.(glog)) (PWMsg Pnew auth) ∗
      [∗ map] a ↦ v ∈ Pnew,
        phys_ledger_pin a (DfracOwn 1) v (S (length g.(glog))) B (Sf a)

Three notes on shapes the memo did not fix.  (a) `ledger_pin_mint` needs
`gen_heap_interp` — the tie names `gmem !! a`, and only `phys_valid` ties
that to the fragment's `v`; it is framed straight back.  (b)
`ledger_read_pin_ok` is AGENT-GENERIC (`∀ h`), which is free and is what
makes it usable inside `fobl_ram`'s ∀-quantified view.  (c) the pinned
store's per-address sets ride as `Sf : Arch.pa -> gset (bv 8)`, so the auth
update is a `map_imap` (`pin_tm`) and not an `fmap`; and
`ledger_store_pin_bytes` has to hand the caller the OLD elements back
(`∀ a ∈ dom Pnew, ∃ t, TM !! a = Some (t, Some (Sf a, B))`), because
`pin_ok_app` needs the pin at the OLD log and the union shadows it.

**HART 0'S WINDOW (ruling 3(b)) IS NOT YET MOVED** — `ProofMain`'s
publication is untouched.  Nothing above `TsoCtx` consumes the pin yet, so
this is queued, not pending.
### A6.51 THE VALUE-AFTER-VIEW READ RULE (RULING 1), LANDED — AND THE
### EXISTING PAIR REALLY IS RE-DERIVABLE

`HartEvents` gained `wp_hart_ram_read_plain_ex` and
`swp_hart_ram_read_plain_ex`, with the obligation INSIDE the ∀ [tv'] and
the resumption's value handed to the continuation:

    ⌜∀ tv', (tv ≤ tv')%nat -> (tv' ≤ length log)%nat ->
       ∃ w, tso_read_bytes img log h tv' pa n w ∧ P w⌝ ∗
    ▷ (|={∅,⊤}=> … ∗
         (∀ tvn w, ⌜tv ≤ tvn⌝ -∗ ⌜tvn ≤ length log⌝ -∗
            ⌜tso_read_bytes img log h tvn pa n w⌝ -∗ ⌜P w⌝ -∗
            view_lb view_name loglen_name h tvn -∗
            WP (C (hread_resume (bv_unsigned w) m))))

**and `wp_hart_ram_read_plain`'s DIRECT PROOF IS GONE** — it is now nine
lines off the `_ex` rule at `P := fun _ => True`, with the byte-wise
determinism step (`bv_eq_of_bytes` on `Hrd tvn` vs the machine's
`Hbytes'`) moved out of the machine reasoning and into the derivation,
exactly as the memo predicted.  The `swp` twin is derived from the `wp`
one the same way `swp_hart_ram_read_plain` is.  **The eleven existing call
sites did not move** (`HartPilot`, `HartSMem` ×2, `HartMFetch` ×2,
`HartMemRun`, `HartMLoad`, `PtTreeAdue` ×2, `SmodeCorePt` ×2): they are
call sites of the OLD rule, whose statement is unchanged.

For progress the `_ex` rule instantiates the ∀ at the reader's own `tv`
(legal by `tso_interp_of_bound`) and names THAT value in the safety
witness; the machine's chosen `tvn` then picks its own `w`, and the two
agree byte-wise only when they must.  This is the piece that makes the
rule sound where the old one is false.
### A6.52 HANDOFF: THE PIN'S MACHINE HALF IS DONE, AND THE CONSUMER HALF
### HAS TWO QUESTIONS THE MEMO DID NOT ANSWER

**WHAT IS BUILT AND GREEN (the memo's §8 order, steps 1–6 of nine):**

    TsoMemPa   §10 pin_ok + pin_ok_mint/_app/_app_frame/_mono +
               read_down_app_frame;  §11 ts_elem + ts_ok (+3 projections)
    TsoGhost   tsomem_tsG :: ghost_mapG Σ Arch.pa TsoMemPa.ts_elem
    RiscvPtsto tso_interp_at's tie is now [ts_ok]; pristine_elem at (0, None)
    RiscvExec  tso_interp_of, same one-conjunct restatement
    TsoCtx     6 sealed defs pinned to [None]; 2 auth updates at (S i, None);
               phys_ledger_pin, pin_map_own, ledger_pin_mint,
               ledger_read_pin_ok (+ _bytes), ledger_store_pin_ok (+ the
               pin_tm / ledger_store_pin_bytes loop); ctx_phys_pointsto_ne
    PtAdBits   nth_byte_testbit, pte_set_ad_nth_byte_high, pte_bytes_canon,
               pte_byte0_class{,_self,_set_ad}          (§5.5, probed green)
    HartEvents wp/swp_hart_ram_read_plain_ex; the old pair RE-DERIVED

**WHAT IS LEFT, in the memo's order, with what each now costs:**

7. **`HartMFetch`/`PtTreeAdue` — `fobl_ram_ex`.**  `fobl_ram`
   (`HartMFetch:589`) has to gain a predicate-indexed twin whose ∃ is
   inside the ∀, matching `swp_hart_ram_read_plain_ex`'s obligation.  The
   PT read at `PtTreeAdue:934` already asks for
   `(∃ w, ⌜fobl_ram …⌝ ∗ ⌜P w⌝)`, i.e. the WRONG nesting — that is the one
   obligation to restate.
8. **`PtTree` — the `None` arm, AND THE FIRST OPEN QUESTION.**  The memo
   says the arm moves from `phys_ledger_word` to its pinned twin.  It
   cannot, as written: `pt_slot_own`'s tier index is
   `PTT : option CtxId` and the pinned twin needs the BOUND `B`.  The
   sets do NOT need a parameter (byte 0's is the four-element A/D class of
   the slot's own word, bytes 1..7's are its own bytes —
   `PtAdBits.pte_byte0_class` is exactly that predicate), so the question
   is only where `B` enters.  Two shapes, and the owner should pick:
   - **(α) existential + agreement**: `None ⇒ ∃ B, kpt_bound B ∗
     phys_ledger_word_pin a dq w B (…)`.  `pt_slot_own`'s ARITY does not
     move, and the reader pins `B` by `kpt_bound`'s agreement against its
     own copy.  Cost: `PtTree` must see `KptGhost`, which today sits ABOVE
     it (`KptGhost` requires `PtTree`) — so `kpt_bound` has to move DOWN,
     into `PtTree` or a new leaf beside it.
   - **(β) richer tier index**: `PTT : ptier` with `KTier (B : nat)` /
     `UTier (ξ : CtxId)`.  No layering move, and **the sweep is
     measurable, not tree-wide: only FIVE files spell the index
     explicitly** (`PtTree`, `KptTree`, `KptShare`, `TransPt`, `HartSKpt`
     — 39 sites); the other ~93 mentions go through the ambient-context
     notations A6.21 created for exactly this reason.
   I lean (β): it keeps `kpt_bound` where the memo put it and pays a
   measured 39-site edit instead of a layering inversion.
9. **`KptGhost` — `kpt_bound B`, a 30-line copy of `kpt_lb`'s csum shape,
   AND THE SECOND OPEN QUESTION**: it needs its own gname.  `kpt_name` is
   `era_kpt_name`, a field of `riscvEraGS` (`RiscvPtsto:194`) allocated in
   `RiscvAdequacy:914`.  So `kpt_bound` costs a THIRD site — the era
   record, its accessor, and the adequacy allocation.  **`RiscvAdequacy`
   is already red** (and A6.48/A6.50 add `era_ts_name`'s allocation to its
   bill anyway), so this is queued work, not new fallout.
10. `KptShare` — the mint at the publication point, `kpt_body` UNCHANGED,
    `kpt_bound` added to `tlb_res_pt`'s four touch points.
11. `HartMStore` — the pinned twin of `wobl_ram_ledger_ex`, off
    `TsoCtx.ledger_store_pin_ok`; its `vnew ∈ Sf a` premise is
    `PtAdBits.pte_byte0_class_set_ad` at byte 0 and reflexivity elsewhere,
    with `Hset : m0' = pte_set_ad q0 a d` already derived at
    `HartSKpt:562`.
12. `HartSKpt` — `kpt_leaf_node_canon_obl` off `ledger_read_pin_bytes_ok`
    + `PtAdBits.pte_bytes_canon`; levels 2/1 keep `kpt_slot_node` verbatim.
    Then `SmodeCorePt`'s unverified re-port finally COMPILES and gets its
    A6.18-style verdict — **still not reached this session**.
13. `ProofMain` — ruling 3(b): the publication moves to the
    `__sync_synchronize` drain.  Untouched; nothing consumes the pin yet.

**AND THE OTHER FRONTIER, which is NOT the pin: the user-translation
S-payer is unstarted.**  A6.48 landed `UserPtTree.utlb_inv_pt_translateAddr_u`'s
`S`-payer parameter but nothing above it was reachable at the time.  Now
that the user-memory tier is green, the cone opens onto FOURTEEN call
sites that pass their first Prop into `S`'s slot:
`UmodeFetch` ×5, `UserFetchPt` ×5, `UserMemMis` ×2, `UserMemPt` ×2 — plus
`UptTree`'s two wrappers, which are still parametric.  **Nobody has yet
CHOSEN what `S` is for a user-mode access**, and that is the design
question: the payer must own the process page table's slots at
`ctx_phys_word_pointsto cur_ctx` across the access, which is
`ProcPtOwn.proc_pt_own` / `upt_pages_own`'s territory.  Together with
`UserMemPt`'s store lane (A6.49) this is the whole remaining user tier.

**THE RED SET AND WHAT EACH IS** (closing clean rebuild, below):

- `HartSKpt` — the pin's consumer half, items 7–12 above.  Behind it:
  `SmodeCorePt` (unverified re-port) and the S-mode PT tier.
- `RiscvAdequacy` — §7 step 6, the era ghosts.  Newly reached behind
  `BootCarve`; `era_ts_name` was never allocated (A6.50's caveat), and
  `kpt_bound` will add to the same bill.
- `UserMemPt` — the user store lane owes the append (A6.49).
- `UmodeFetch` — the S-payer, above.

**THE CLOSING MODEL-AWARE CLEAN REBUILD: 554 ATTEMPTED, 549 `.vo`, 5
ERRORS** (`iris/*.vo` deleted first; `ls -la --time-style=full-iso
model-xv6iris/*.v *.vo` checked FIRST per A6.39 — the model `.vo` at
19:11 postdates its source at 18:37; 554 − 5 = 549, self-consistent).
The fifth error was `PtFree`, a first-time-reached file needing exactly
the A6.48 budget (a `CurCtx` binder plus the `↦ₚ₈` → `ctx_phys_word_pointsto`
spelling); fixing it and re-running the sweep on the clean base gives

> **551 of 1330, FOUR red, up from A6.48's 535/7.**  Sixteen files went
> green and three red files were closed (`ProofEntry`, `BootCarve`, and
> the four-file user-memory tier), while two first-time-reached files
> replaced them.  **And the pin's whole machine half — the element type,
> both interp ties, `TsoCtx`'s four pinned gates, and `HartEvents`' rule
> pair — landed inside that number with ZERO fallout: no file outside the
> seven it touches changed, which is the memo's central claim measured.**

**STILL RED — eight attempted-and-failed, plus `WpSconfMem`'s termination.
Four of the eight were EDITED after the sweep had already given up on them
(`WpSmodePtMemWrap`, `ProcInv`, `FsLookup`, `RiscvAdequacy`), so their next
compile is the first real news about them:**

- `HartSKpt` — the pin's CONSUMER half (A6.52 items 7–12), with
  `SmodeCorePt`'s unverified re-port behind it.  **Still not reached; no
  A6.18-style verdict yet.**
- `RiscvAdequacy` — §7 step 6, newly reached behind `BootCarve`.
- `UserMemPt` — the user store lane owes the append (A6.49).
- `UmodeFetch` — the user-translation S-payer, unstarted (A6.52).

### A6.53 THE A6.52 RULINGS, IMPLEMENTED — THE INDEX CARRIES THE BOUND,
### THE BOUND HAS ITS OWN GNAME, AND THE WRITE-BACK'S GATE IS BUILT

**RULING 1 (option β, the richer index) — LANDED, and the measurement
held.**  `PtTree` gained

    Inductive ptier := KTier (B : nat) | UTier (xi : TsoCtx.CtxId).

    pt_slot_own a dq w := match PTT with
      | KTier B  => TsoCtx.phys_ledger_word_pin a dq w B (pte_slot_set w)
      | UTier xi => TsoCtx.ctx_phys_word_pointsto xi a dq w
      end

`pt_slot_own_forget` stays a one-liner at both arms
(`phys_ledger_word_pin_forget` is the new one), `_ctx` is unchanged and
`_ker` gains the bound.  The notations moved with it: `↦ₚₜ` is
`UTier cur_ctx`, `kpt_page_own` / `kptree_own` / `kpt_kids_own` became
PARAMETERISED notations taking `B`, and the slot notation is
`a ↦ₖₜ[ B ] dq w`.

> **AND THE LEXER TRAP FIRED, exactly where durable-notes says it does.**
> The first spelling was `a ↦ₖₜ[ B ]{ dq } w`, which creates a fused `]{`
> token — and `KstackOwn`'s `va ↦ₘ[KT0]{dq} b` stopped parsing with
> *"Syntax error: ']' expected after [term level 50]"*, two hundred files
> away.  The rule in durable-notes ("a fused `]{` token would break
> ghost_map's `↪[γ]` tree-wide") is about `↦ₘ[kt]`'s OWN shape and it is
> right: the fix is to mirror `↦ₘ[kt] dq v`'s `"] dq"` spacing.

**THE SET FAMILY IS A PARAMETER AT `TsoCtx` AND A DEFINITION AT
`PtTree`** — naming `pte_canon` at the machine layer is the layering
violation candidate (iv) was rejected for.  `TsoCtx.phys_ledger_word_pin`
takes `Sf : nat -> TsoMemPa.byteset`; `PtTree` supplies

    pte_ad_byte0 w := the FOUR-element A/D class of w's byte 0
    pte_slot_set w j := if j =? 0 then pte_ad_byte0 w
                        else byteset_sing (nth_byte w j)

with the four laws that make the pin work: `pte_slot_set_set_ad` (the
family is INVARIANT under the write-back, so a slot's pin survives its own
store), `pte_slot_set_mem_set_ad` (the store gate's side condition),
`pte_slot_set_canon` (membership at every offset forces canon-equality —
this is §5.5's reassembly, now consumed), and `pte_slot_set_eq_of_mem`
(the family is determined by the CANON CLASS, which is what lets the
payer wand stay value-generic).

**THE PAYER WAND'S SIDE CONDITION IS TIER-GENERIC, and that is the shape
that made the sweep cheap.**  `ptree_translateAddr_own`'s payer gained one
premise:

    ⌜pte_canon wnew = pte_canon (pte_set_ad w a0 d0)⌝ -∗ …

At the `UTier` arm it is ignored; at `KTier` it is exactly what
`pte_canon_inv` + `pte_slot_set_mem_set_ad` need.  The walk only ever
writes an A/D variant, so every discharge is `pte_canon_set_ad`.  The four
outer chainable wands (`KptTree`, `KptShare`, `TransPt` ×2, and
`SmodeCorePt` ×2 behind them) moved from `TsoCtx.phys_ledger_word` to
`pt_slot_own (KTier B)` with the same premise.

**`kpt_inv`'s ARITY DID NOT MOVE, as designed.**  `kpt_body` existentially
quantifies `B` and carries `kpt_bound B` beside `kpt_lb t`; a reader
learns `B` by opening and matches it against its own copy.  The ∃ is in
the INVARIANT BODY, which is the memo's §5.4 shape — not inside
`pt_slot_own`'s arm, which is what ruling 1 forbade.  `tlb_inv_pt` (the
exclusive bundle) carries the bound existentially too, and
`tlb_inv_pt_share` is where the agreement is shot.

**RULING 2 — `kpt_bound` HAS ITS OWN ERA GNAME.**  `RiscvPtsto` gained
`kptbR := csumR (exclR unitO) (agreeR (leibnizO nat))`, the functor field
`riscvF_kptbGS`, the era field `era_kptb_name` and the accessor
`kptb_name`; `KptGhost` gained `kptb_unset` / `kpt_bound` /
`kptb_shoot` / `kpt_bound_agree` / `kptb_ghost_alloc` — `kpt_lb`'s shape,
one payload over, ~30 lines as predicted.  `tlb_res_pt` carries
`∃ B, kpt_bound B` (persistent, so the residue pays nothing).

**THE READ AND WRITE GATES ARE BUILT AND GREEN.**  `TsoCtx` gained the
window forms the walk actually applies —

    phys_ledger_word_pin (+ _unfold/_aligned_p/_bytes/_intro/_forget/_sets)
    phys_ledger_pin_win_map      the [big_sepM_foldr_ins] regrouping,
                                 offset-keyed sets re-keyed to addresses
    ledger_store_win_pin_ok      the A/D write-back's window gate

— and `HartMStore` gained `wobl_ram_ledger_pin_ex`, `wobl_ram_ledger_ex`'s
pinned twin at the `AV_exclusive` (conditional-store) arm, which is the
form `HartSKpt`'s `wpte_obl_at` seam consumes.

**AND THE VALUE-AFTER-VIEW OBLIGATION IS THREADED THROUGH THE PT READ.**
`HartMFetch` gained

    fobl_ram_ex img log tv pa n P :=
      ∀ tv', tv ≤ tv' -> tv' ≤ length log ->
        ∃ w, tso_read_bytes img log (hart_agent cpu_id) tv' pa n w ∧ P w
    fobl_ram_ex_of : fobl_ram … w -> P w -> fobl_ram_ex … P

and `PtTreeAdue.swp_checked_mem_read_pte8_ex`'s obligation moved from the
WRONG nesting `(∃ w, ⌜fobl_ram …⌝ ∗ ⌜P w⌝)` to `⌜fobl_ram_ex …⌝`, its
proof now running on `swp_hart_ram_read_plain_ex`.  **That is the last
kit-side piece of the pin's read path.**

### A6.54 HANDOFF: `HartSKpt` IS DOWN TO ONE NAMED GATE — AND THE MEMO'S
### "LEVELS 2/1 VERBATIM" IS REFUTED BY MEASUREMENT

**WHERE `HartSKpt` STOPS, exactly.**  After A6.53 the file's only error is
`:410`, and it is the obligation SHAPE and nothing else:

    swp_checked_mem_read_pte8 wants  ⌜HartMFetch.fobl_ram img log tv a 8 w⌝
    kpt_slot_node supplies           ⌜read_bytes σ.(mem) a 8 = Some w⌝

i.e. the whole `HartSKpt` read lane is still stated over the FLAT cache.
That is not an oversight of the pin work: it is A6.36's overruling
catching up with this file.  `PtTreeAdue.xread_obl` / `xread_obl_ex`
(`:557` / `:572`) are the PRE-overruling shape — they take the reader's
view already advanced to the top (`vstep … (length log)` plus
`view_lb … (length log)`) and conclude about `read_bytes σ.(mem)`, which
was sound only while a PTE read was RULING 1's flat `Read_ttw` arm.  It is
the plain arm now.

**THE TRANCHE, and it is the last one on the pin's critical path:**

1. Restate `PtTreeAdue.xread_obl_ex` at `fobl_ram_ex` (drop the top-view
   receipt; it is no longer what the rule gives).
2. Re-derive `HartSKpt`'s five node lemmas — `kpt_open_slots`,
   `kpt_slot_node`, `kpt_pte2_node`, `kpt_pte1_node`, `kpt_leaf_node{,_canon}`
   — off the PINNED resource rather than off `gen_heap_interp`:
   open `kpt_inv`, take the slot at `pt_slot_own (KTier B)`, apply
   `TsoCtx.ledger_read_pin_bytes_ok` (through the A6.1a bridge
   `tso_interp_of_pin` + `tso_interp_of_at_gs` at `gs_of`, exactly as
   `HartMFetch.fobl_ram_text` runs it), and reassemble with
   `PtTree.pte_slot_set_canon`.  The eight bytes are destructed one at a
   time and the word is `Z_to_bv 64 (assemble_bytes […])` +
   `PageGeom.nth_byte_assemble8` — `ProcPtOwn.phys_bytes_word8` is the
   worked precedent for that shape.
3. Port the write-back at `HartSKpt:565–579` to
   `HartMStore.wobl_ram_ledger_pin_ex` (built, A6.53).  **One small gap
   named here so it is not re-discovered:** that gate's `Sg` is
   ADDRESS-keyed while the word tower's `Sf` is OFFSET-keyed, and the call
   site has to supply the bridge `∀ j < 8, Sg (pa_add pa j) = Sf j`.  For
   an 8-aligned slot `Sg := fun a => pte_slot_set q0 (Z.to_nat (uint a mod 8))`
   works; the arithmetic fact it needs
   (`uint (pa_add pa j) mod 8 = j` for `j < 8` at an 8-aligned `pa`) does
   not exist yet and is the one lemma to add.  Alternatively give
   `ledger_store_win_pin_ok` an offset-keyed twin.
4. `Pt2WalkPt` (`:971/978/987/996/1339`) consumes the node lemmas and
   moves with them.

> **THE REFUTATION, and it is a real one.**  tso-pin-memo §5.5 says
> *"Levels 2/1 keep `kpt_slot_node` verbatim on `ledger_read_at_ok` +
> `⌜t ≤ B⌝`."*  **That cannot stand at the tier ruling 1 chose.**  Under
> `KTier B` EVERY slot of the kernel tree is pinned, so an interior slot's
> `ts_name` element is `Some (Sv, B)` — and `phys_ledger_at`, hence
> `ledger_read_at_ok`, is by DEFINITION the `None` element.  It does not
> apply to an interior slot at all.  Worse, nothing carries `t ≤ B` to the
> read site: `ledger_pin_mint` has it as a PREMISE, but the resource does
> not record it, and it is genuinely false of the leaf after a write-back.
>
> So an interior read yields what the pin gives — `pte_canon`-equality,
> not the exact word.  **That is sound for the walk**: `pte_set_ad_ppn`
> and `pte_set_ad_flag_*` say the PPN and the permission flags are
> canon-invariant, so `pt_addr1 p2 vpn` / `pt_addr0 p1 vpn` and every
> `pte_check_ok` are unchanged.  The cost is that `kpt_pte2_node` and
> `kpt_pte1_node` WEAKEN from an exact value to the canon predicate, and
> their consumers absorb it — which the `_ex` (predicate-indexed) read
> lemmas were built for.  **Do not try to recover exactness by carrying
> `⌜t ≤ B⌝`: it would have to be per-slot, and the leaf's is false.**

> **RATIFIED (owner, 2026-08-27), and then made moot.**  The weakening to
> canon-equality is ratified: PPN and flags are canon-invariant, so
> `kpt_pte2_node` / `kpt_pte1_node`'s consumers lose nothing the walk
> needs.  **A6.55 then found a third option and the weakening was never
> spent** — the allowed-byte family reads the leaf bit, so an interior slot
> pins to singletons and keeps its EXACT value.  The ratification stands as
> the fallback; nothing in the tree relies on it.

**STILL RED, and what each is** (closing rebuild below):

- `HartSKpt` — the tranche above.  Behind it: `SmodeCorePt`'s unverified
  re-port (its two payer wands are already moved to the pinned tier, so it
  will compile as soon as `HartSKpt` does) and the S-mode PT tier.
  **Still no A6.18-style verdict.**
- `RiscvAdequacy` — §7 step 6, and its bill is now three items:
  `era_ts_name` (never allocated, A6.50), `era_kptb_name` (A6.53), and the
  pre-existing `riscvEraGS`-arity failure at `:600`.  It is the first
  honest contact with step 6 and deserves its own inventory pass.
- `UserMemPt` — the user store lane owes the append (A6.49).
- `UmodeFetch` — the user-translation S-payer, unstarted (A6.52); 14 call
  sites across `UmodeFetch`/`UserFetchPt`/`UserMemMis`/`UserMemPt`, and
  the design question (what `S` IS for a user access) is untouched.

**THE CLOSING MODEL-AWARE CLEAN REBUILD: 555 ATTEMPTED, 551 `.vo`, 4
ERRORS** (`iris/*.vo` deleted first; `ls -la --time-style=full-iso
model-xv6iris/*.v *.vo` checked FIRST per A6.39 — the model `.vo` at
19:11:34 postdates its source at 18:37:36; 555 − 4 = 551,
self-consistent).

> **551 of 1330, FOUR red — the same number as A6.50's, with the WHOLE
> ruling-1/ruling-2 tranche landed inside it.**  Seven more files changed
> shape (`PtTree`'s index, `RiscvPtsto`'s functor and era record,
> `KptGhost`, `KptTree`, `KptShare`, `TransPt`, `HartMStore`) and the red
> COUNT did not move: `PtFree` and `KstackOwn` were reached, fixed and
> closed inside the same sweep.  An index change at the bottom of a
> 1330-file tree costing zero net red is the measurement that ruling 1's
> option (β) was the right call.

### A6.55 THE §5.5 WEAKENING IS NOT NECESSARY AFTER ALL — THE SET FAMILY
### IS CONDITIONED ON LEAF-NESS, AND `HartSKpt` IS GREEN

A6.54 refuted tso-pin-memo §5.5's "levels 2/1 keep `kpt_slot_node` verbatim"
and the owner RATIFIED the fallback (interior reads weaken to
canon-equality; PPN and flags are canon-invariant so the walk loses
nothing).  **The ratification is recorded and was not needed.**  Building
it turned up a third option the memo and the refutation both missed, and
it restores §5.5's CONCLUSION by a different mechanism:

> **§1's measurement is the fix.**  "A/D is defined only on LEAF PTEs, and
> the tree agrees: every write path targets `pt_addr0 p1 vpn` and nothing
> else."  So the allowed-byte family can READ the leaf bit:
>
>     pte_slot_set w j :=
>       if j =? 0 then (if pte_nonleafb w then byteset_sing (nth_byte w 0)
>                       else pte_ad_byte0 w)
>       else byteset_sing (nth_byte w j)
>
> An INTERIOR slot pins to eight singletons, so its read is EXACT
> (`pte_slot_set_exact`, and `ptree_maps` hands over the `pte_ptr` conjunct
> that fires it).  A LEAF pins byte 0 to the four-element A/D class and its
> read is canon-equal (`pte_slot_set_canon`).  **`kpt_pte2_node` /
> `kpt_pte1_node` keep their exact values, `HartSTrans` and `Pt2WalkPt` do
> not move at all**, and the ratified weakening is left unused.

What the leaf-conditioning costs is ONE premise, and it is honest: the
family is stable under the write-back (`pte_slot_set_set_ad`) and the
write-back's bytes are allowed (`pte_slot_set_mem_set_ad`) only *for a
leaf* — at a non-leaf both are FALSE, because `pte_set_ad` would move
byte 0 out of a singleton.  So the payer wand's side condition is

    pte_wb_ok wold wnew :=
      pte_leaf wold /\ ∀ j < 8, nth_byte wnew j ∈ pte_slot_set wold j

stated TIER-GENERICALLY (the `UTier` arm ignores it) and discharged at the
one place that writes — the walk's O3 arm, whose `Hvar` already proves
`pte_leaf` of the variant.  `pte_wb_ok_sets` is why the slot comes back
pinned at the SAME family, i.e. why the shared table is canon-INVARIANT
under its own write-back rather than merely canon-monotone.

**`HartSKpt` IS GREEN.**  Its read lane was the last piece and it was
A6.36's overruling catching up with the file: `kpt_slot_node` and friends
were stated over the FLAT cache (`read_bytes σ.(mem)`), which was sound
only while a PTE read was RULING 1's `Read_ttw` arm.  What landed:

    kpt_slot_bytes_pin   the pin at the interp seam -- the A6.1a bridge
                         ([tso_interp_of_pin] + [tso_interp_of_at_gs] at
                         [gs_of]) exactly as [HartMFetch.fobl_ram_text]
                         runs it, off [ledger_read_pin_bytes_ok]
    fobl_of_sets         byte sets -> EXACT word   (interior)
    fobl_ex_of_sets      byte sets -> canon-equal  (leaf; §5.5's reassembly,
                         eight bytes destructed and reassembled with
                         [PageGeom.nth_byte_assemble8])
    kpt_path_obl         all three slots off ONE opening
    kpt_obl / kpt_obl_ex the post-overruling obligation shapes
    kpt_pte2_obl / kpt_pte1_obl / kpt_leaf_obl

and the A/D write-back at `kpt_leaf_write_node` now runs on
`HartMStore.wobl_ram_ledger_pin_ex`.  **The offset→address bridge A6.54
flagged is a five-line `assert`**: `Sg a' := pte_slot_set q0 (Z.to_nat
(uint a' − uint pa))`, and the no-wraparound fact comes from
`kpt_addr_ok_own` applied to the slot itself — no new arithmetic lemma was
needed after all.

**THE READER'S CREDENTIALS ARE NOW EXPLICIT, and that is the design
change.**  `swp_translate_kpt` gained `kpt_bound B` and
`view_lb view_name loglen_name (hart_agent cpu_id) B`.  They ride as ONE
persistent conjunct `KptShare.kpt_creds` in `tlb_res_pt` (hence in
`SRegime.kpt_swp_res` / `kpt_res_at`, `WpSFrames.s_frames`,
`SmodeCorePt.spt_res_pt` and `WpIntrInv`'s cell round trip), so
`kpt_swp_translate`'s signature and IntrDefs' two call sites did not move.
`KptTree.tlb_inv_pt` carries the receipt too, which is where pin-memo
§5.6(b) lands: **hart 0's `__sync_synchronize` drain is now a stated
obligation of the publisher** rather than an assumption inside the walk.
`tlb_inv_pt_intro`'s producers (kvminithart / `ProofMain`) owe it.

### A6.56 THE A6.18 VERDICT ON `SmodeCorePt`, AT LAST — AND IT IS GOOD

`SmodeCorePt` has been carried as "the unverified re-port" since A6.46 and
deferred three times.  **It compiles.**  The verdict, in the form A6.18
asks for:

> **FOUR errors in 4,480 lines, and NONE of them is a flip or pin issue.**
> Two are mine (the `kpt_creds` conjunct in `spt_res_pt` and the
> `tlb_res_pt_intro` rebuild), and **the only two genuine re-port bugs are
> both in the TEXT-tier lemmas and both are stale index/rewrite
> directions**:
>
> - `s_text_byte` rewrote its HYPOTHESES at `ppn` when `kmap_at_agree`
>   yields `ppnj = ppn` — a no-op, leaving `iFrame` nothing to match.  The
>   normalisation runs at `ppnj` and the GOAL is brought to it.
> - `s_text_obl` rewrote `Hg` at index `k` where `lookup_seq` had left
>   `0 + k`.  One `Nat.add_0_l`.
>
> Between them the file compiled 3,200 lines untouched — including its two
> A/D payer wands, both of which had already been moved to the pinned tier
> blind (A6.53) and were right.  **The re-port's substance is sound; what
> it had was two typos that no amount of reading would have found and one
> compile did.**  That is the answer to A6.18's question, and it is the
> argument for compiling a re-port early rather than reviewing it.

**AND CLOSING IT OPENED THE WHOLE S-MODE PT TIER**: the `.vo` count went
from 551 to 600 in one sweep.  Four first-time-reached files came with it,
three now green (`CpuOwn` — `ctx_pointsto_ne`, the A6.48 precedent again;
`WpIntrInv` — the `kpt_creds` round trip; and `WpSmodePtLeaves` /
`UptWalkPt` characterised below).

### A6.57 HANDOFF: THE PIN IS DONE END TO END; WHAT IS LEFT IS THREE
### NAMED LANES AND ONE INVENTORY

**THE PIN'S WHOLE STORY IS NOW BUILT AND GREEN**, from `TsoMemPa`'s pure
layer to the kernel-PT walk that consumes it:

    TsoMemPa   pin_ok + the four laws; byteset/ts_elem/ts_ok
    TsoGhost   the element type
    RiscvPtsto/RiscvExec   the interp tie (one conjunct)
    TsoCtx     phys_ledger_pin, the word tower, the four gates, the window
               forms (phys_ledger_pin_win_map / ledger_store_win_pin_ok)
    PtAdBits   §5.5's reassembly
    PtTree     ptier, pte_slot_set (leaf-conditioned), pte_wb_ok
    KptGhost   kpt_bound;  KptShare  kpt_creds, kpt_body, publication
    HartEvents wp/swp_hart_ram_read_plain_ex (old pair re-derived)
    HartMFetch fobl_ram_ex;  PtTreeAdue  the PT read
    HartMStore wobl_ram_ledger_pin_ex
    HartSKpt   the discharge AND the write-back        <- both green
    SmodeCorePt / SRegime / IntrDefs / WpSFrames / WpIntrInv / CpuOwn

**Nothing in the pin's design was refuted in the building** — the memo's
three §8 rulings all stand as implemented, with two corrections recorded
(A6.53's one-conjunct `ts_ok`, A6.55's leaf-conditioned set family, which
restores §5.5's conclusion after A6.54 refuted its stated mechanism).

**THE LANES LEFT, in the order they now gate things:**

1. **`ProofMain` / kvminithart — the publisher's obligations.**
   `KptTree.tlb_inv_pt` now demands `view_lb … B` and the tree at
   `KTier B`, so the boot lane owes (a) `TsoCtx.ledger_pin_mint` per slot
   at the exclusive tier, and (b) the `__sync_synchronize` drain that makes
   the receipt free — pin-memo §5.6(b), and the LAST unimplemented ruling.
   Nothing above it is blocked on this (the premise is threaded), but the
   adequacy proof cannot close without it.
2. **`UptWalkPt` / the trampoline lane — `own_context` through
   `tramp_tr_obl`.**  `swp_translate_upt` now takes and returns the running
   token (the USER tree's slots are ledger words, so its own A/D write-back
   owes the append).  Its caller `TrampStepPt.tramp_tr_obl` does not carry
   one; that is the A6.27/A6.28 threading applied to the trampoline fetch,
   and it runs `TrampStepPt` → `SpecUsertrap` → `UservecExitPt`.
3. **`WpSmodePtLeaves` — the S-mode LOAD/STORE leaf's RAM obligation.**
   Its two claim reads are fixed (they used the deleted
   `TsoCtxShim.ctx_pointsto_to_mem`; the sealed tier reads the claim
   directly with `ctx_pointsto_phys`, and `ctx_phys_pointsto_ram` supplies
   what `mem_pointsto_acc` used to).  What remains is the same shape as
   `HartSKpt`'s read lane one tier over: the arm still calls
   `TsoCtxShim.ctx_buf_to_mem` and states its obligation over the flat
   cache.  `HartSKpt.kpt_slot_bytes_pin` + `fobl_of_sets` are the worked
   precedent.
4. **`UserMemPt` / `UmodeFetch` — the user tier (A6.49/A6.52), untouched.**
   The store lane's `wobl` threading and the translation S-payer.
5. **`WpSconfSfence` — one `own_context` at a `bytes_own ∅` call**, the
   smallest item on the list and the same threading as (2).
6. **`DiskBoot` / `SwtchCtx` / `WpSconfMem` — THE DELETED SHIM'S TAIL, and
   it is a class, not three files.**  `TsoCtxShim` is gutted to its one
   still-true mint (`own_context_alloc`), and **240 references across 63
   files still name it** — mostly `Proof*` files that have never been
   reached.  Three of them surfaced in this sweep, and the measurement
   worth recording is that **they are NOT identities**: I tried deleting
   the calls on the theory that M1 made `↦ₘ` the ctx byte, and
   `word4_pointsto` / `↦₈` are still the RAW towers on the other side, so
   the shim was doing a real tier move.  Each site needs the A6.13 law
   (`ctx_pointsto_forget` / `ctx_ktier_mono` / their word forms) or a
   re-tiering of the resource, decided per site.  **`grep -l TsoCtxShim\.`
   is the worklist and it is the largest remaining block of the flip.**

**AND THE `RiscvAdequacy` INVENTORY (its bill is FOUR items).**  The
file has never compiled in this workspace; `:600` is where it stops today,
and the errors are structural, not incremental:

- **(i) the era-record arity, and the error NAMES the gap.**  `:600` fails
  unifying `option riscvEraGS` with
  `option (gname → gname → gname → gname → riscvEraGS)` — the allocation
  still writes `RiscvEraGS f Hhn Hmn γu γp γv γk γkpt γs …`, i.e. it is
  short by exactly the FOUR TSO gnames the flip added
  (`era_ts_name`, `era_logm_name`, `era_loglen_name`, `era_view_name`),
  plus `era_kptb_name` (A6.53) which sits beside `era_kpt_name`.  So the
  arity gap IS the inventory: five allocations to write, in the record's
  own order.
- **(ii) `era_ts_name` is never allocated** (A6.50): the file has no
  `ts_name` mention at all, so `tso_interp_at`'s ghost_map auth has no
  origin.  The initial value is `dom TM = dom gmem` with every element
  `(0, None)`, and `ts_ok` at the empty log is `latest img [] a 0 v`,
  i.e. `img = gmem` — which is exactly `boot_shape`'s post-power state.
- **(iii) `era_kptb_name`** (A6.53), one `kptb_ghost_alloc` beside the
  existing `kpt_ghost_alloc`.
- **(iv) the boot-lane premises the flip has been accumulating**:
  `BootCarve.boot_led_ran` (A6.49) and `SpecEntry`'s two (A6.49) both
  bottom out in the era's initial-state ghosts, i.e. here.

None of (i)–(iv) is a design question; (ii) is the only one with content
and its content is written above.  **It is §7 step 6, and it is now the
only structural piece of the flip that has never been attempted.**

**THE CLOSING MODEL-AWARE CLEAN REBUILD: 672 ATTEMPTED, 661 `.vo`, 11
ERRORS** (`iris/*.vo` deleted first; `ls -la --time-style=full-iso
model-xv6iris/*.v *.vo` checked FIRST per A6.39 — the model `.vo` at
19:11:34 postdates its source at 18:37:36; 672 − 11 = 661,
self-consistent).  Two of the eleven were first-time-reached files needing
only a `CurCtx` binder (`SpecAllocpid`, `SpecProcdump`); fixing them and
re-running the sweep on that clean base gives

> **663 of 1330, NINE red, up from 551/4.**  `HartSKpt` and `SmodeCorePt`
> were the two deepest frontier files in the tree and closing them opened
> the entire S-mode PT tier: **112 files went green in one tranche**, and
> seven of the nine red are first-time-reached.

**STILL RED — eight attempted-and-failed, plus `WpSconfMem`'s termination.
Four of the eight were EDITED after the sweep had already given up on them
(`WpSmodePtMemWrap`, `ProcInv`, `FsLookup`, `RiscvAdequacy`), so their next
compile is the first real news about them:**

- `RiscvAdequacy` — §7 step 6, inventory above.  The only structural piece
  of the flip never attempted.
- `DiskBoot`, `SwtchCtx`, `WpSconfMem` — the deleted shim's tail (lane 6).
- `WpSmodePtLeaves` — the S-mode load leaf's RAM obligation (lane 3).
- `UptWalkPt`, `WpSconfSfence` — `own_context` threading (lanes 2, 5).
- `UserMemPt`, `UmodeFetch` — the user tier (lane 4).

**Nothing on that list is a design question.**  The pin's design work is
finished; what is left is threading, one inventory, and one large but
uniform grep.

### A6.58 THE SHIM TAIL IS ONE RESIDUE, NOT SIXTY-THREE DECISIONS — AND
### THE PLAIN ARM'S PRICE IS A TOKEN AT EVERY S-MODE LEAF

A6.57 handed over "240 references across 63 files, decided per site".  The
measurement is in and it is far sharper than that:

> **181 of the 240 are real lemma uses** (the other 59 are `Require
> TsoCtxShim.` lines and prose mentions).  **111 of the 181 convert
> MECHANICALLY**, by rules with exact replacements; **70 survive, and every
> single survivor is an `_of_mem` or `_shim`** — the raw→ctx direction, the
> one the flip makes FALSE.  So the tail is not sixty-three decisions.  It
> is one scripted sweep plus **one decision per RAW-TOWER OWNER**, and
> there are five owners.

**WHY THE MECHANICAL HALF EXISTS AT ALL, AND IT IS A STALE COMMENT.**
Nearly every converted site carries some spelling of

    (* ↦₄ has not flipped yet (M1 stage 2): the ctx word crosses here *)

and **it HAS flipped**: `TsoCtx`'s notation block declares `↦₂`/`↦₄` as the
context-indexed towers, and has since this workspace's `TsoCtx.v` was
written.  The client files never learned.  So the SC-era route — drop to
raw with the shim, do the halving, come back — is UNNECESSARY in its
forward direction and FALSE in its return one, and the repair is the same
algebra one tier up.  A6.57's "identities now" theory was therefore HALF
right, and the half it got right is exactly the half where the tier had
already moved: `WpSconfMem`'s `wordw_pointsto` (A6.18's payoff) really did
make its crossings identities, and they are simply deleted.

**THE KIT THE SWEEP NEEDED, and where it had to live.**  The ctx tower had
no 8↔4 halving: `InstrBytes.word_pointsto_split4`/`_join4` sit BELOW
`TsoCtx`, so their `↦₈`/`↦₄` are the raw towers and the file cannot import
the kit.  The halving is now stated one tier up, in **`ByteBuf.v`** — the
lowest file importing BOTH `InstrBytes` (whose half-byte lemmas are pure,
hence tier-blind) and `TsoCtx`, and one that every consumer of the raw pair
already imports:

    ctx_word_pointsto_split4 / ctx_word_pointsto_join4   (ξ EXPLICIT)
    ctx_buf_forget      -- [ctx_buf_to_mem]'s honest one-way successor

Both proofs are the raw ones VERBATIM.  Nothing new had to be proved; the
ctx tower is a byte window exactly as the raw one is.

**AND THE SWEEP'S ONE NON-LOCAL EFFECT**: thirteen converted files did not
import `ByteBuf`, so the sweep adds the `Require` — checked against the
dependency graph first, and all thirteen are safely above it (`ByteBuf`
reaches only `InstrBytes` / `KallocInv` / `TsoCtx`, none of which reaches a
`Proof*` or an S-mode leaf).  That check is worth re-running before the
owners' tranche adds more.

**THE FIVE RAW-TOWER OWNERS — the whole residue, and it is a RE-TIERING,
not a bridge.**  Every survivor has one shape: an invariant holds a word
cell in the RAW tower, an ordinary `c.ld`/`c.sd` leaf takes and returns a
CTX word, so each access crossed in and out.  The `out` direction is now
`ctx_word_pointsto_forget`; the `in` direction cannot be repaired AT THE
SITE, because a `ctx_pointsto` carries a timestamp fragment and a
clean/dirty bit that the era's allocation handed out once (A6.9).  **The
owner has to move tier.**

| owner | sites | files |
|---|---|---|
| the boot carve's frame slots | 25+1 | `BootCarveMain`, `BootBridge` |
| `BcacheInv`'s LRU links | 16 | `ProofBinit` `ProofBread` `ProofBrelse` |
| `ProcInv`'s proc-slot cells | 9 | `ProofKexit` `ProofReparent` `ProofKwait` `ProofSysKill` `ProofSysPause` `ProofSysOpenParts` `ProofSysUnlinkParts` `ProofKforkB5` `ProofForkretParts` |
| `DiskInv` / the devsw slot | 4 | `VirtioDiskRwDefs` `ProofFilewriteParts` |
| the buffer/string windows | 12 | `ProofSysPipe` `ProofDirlink` `ProofDirlookupParts` `ProofCreateParts` `ProofSyscall` `DinodeSlot` `ProofKexecTail` `ProofPrintk` |
| the near-frontier leaves | 2 | `WpSmodePtMem` `WpSconfLock` |

That re-tiering is `tools/ctx_convert.py`'s `ambient` pass on the owner
files plus their accessor lemmas, and it is **its own tranche**: the owners
are green today and every consumer above them is past the frontier, so it
cannot be compile-validated from here.  **`↦ₛ` is the one owner that must
NOT move** (A6.15's ruling — `WpLock.lock_name` sits inside the persistent
lock handle); its sites take the forget, and the `⊣⊢` statements that
crossed both ways (`ProofSyscall.sysc_pname_app`, `DinodeSlot`'s two)
weaken to `⊢`.

**AND THE OTHER HALF OF THIS TRANCHE: THE PLAIN ARM'S PRICE, PAID AT THE
S-MODE LEAVES.**  A6.36's overruling deleted the strongly-ordered read arm,
so an S-mode LOAD is `HartEvents`' PLAIN arm and what its leaf owes is
`HartSMem.Mobl_ram`'s VIEW-INDEXED family — what the load may return at
every view the hart can legally land on — and not a flat `read_bytes`
against `σ.(mem)`.  `SmodeCorePt.s_mem_chunk` cannot pay that, which is the
READ-side half of A6.18's prediction coming due one tier below `HartSKpt`.
What landed:

    SmodeCorePt.wordw_win_load_c    the READ twin of [wordw_win_store_c]:
                                    [win_to_phys] (now fraction-generic)
                                    then [TsoCtx.ctx_phys_load_bytes_ok]
    SmodeCorePt.word_pointsto_load_c   its 8-byte instance
    WpSconfMem.wordw_pointsto_load_c   the width-generic wrapper

**Its conclusion is PURE, and that is the whole design point**: the window,
the token and the interp bundle all survive the call, so an ATOMIC-UPDATE
leaf (`WpSconfMem`'s load) can run it INSIDE the update and still hand the
cell back.  The store twin cannot — it consumes, re-mints and appends.

**THE CONSEQUENCE IS A TOKEN AT EVERY S-MODE MEMORY LEAF, and it is the
A6.27/A6.28 threading finally reaching the leaves.**  `wp_cld_s_r_t` /
`wp_csd_s_r_t` (and their KT0 corollaries, and `WpSmodePtMemWrap`'s four
sp-relative wrappers) take `own_context XI` and hand it back beside the
word; `WpSconfMem`'s two engines stop framing `Hctx` into the POST side of
their `swp_mono` and send it DOWN to the node instead, getting it back
inside the leaf's payload (`R := own_context ∗ Ψ`).  §0.17′ is respected
throughout: no deposit or absorb runs inside a `wp_..._au_...`; the token
is a plain resource threaded through it.

Three more measurements from the same tranche, each a stop the SC text hid:

- **`WpSconfSfence` needed NO token at all.**  A6.22's rule applies exactly:
  the flush runs at `mm := ∅`, and `HartMemRun.swp_hmrun_of_exec_reg` is the
  sanctioned register-only instance that mints and drops a throwaway
  identity internally.  Using it is what keeps that leaf's STATEMENT fixed.
- **`SwtchCtx.ctx_cells_reindex` was a FREE re-index and is now a PRICED
  one.**  Its SC body was `ctx_word_to_mem` then `ctx_word_of_mem`; the
  honest law was already in the kit (`TsoCtx.CtxMorph` along a `ctx_dom`),
  and a save area is fourteen word cells and nothing else, so the lemma
  keeps its name and gains one `ctx_dom ξ ξ'` premise.  Its single caller
  (`ProofScheduler`) is the M2 worklist entry that price creates — and it
  is NOT a quarantine, because the obligation is now in the type.
- **`WpSconfMem.mem_pointsto_write_c` had no caller** and was stated over
  the deleted `s_win_write`; deleted rather than re-derived.

**NEWLY REACHED, ONE M1-CLASS FIX EACH** (the standing rule held): `ProcInv`
— the trapframe page is a LEDGER page and the tier is FORCED, not chosen,
exactly as A6.49 measured for the other four user-memory files
(`ProcDefs.tf_words`/`tf_tail` move to `ctx_phys_word_pointsto` /
`ctx_phys_pointsto`, and the file's own VA↔phys bridge becomes A6.14's
identity-mapping isomorphism `ctx_pointsto_to_phys`/`_of_phys` instead of a
raw crossing); `FsLookup` — one missing `CurCtx` section binder, reported as
an unresolved typeclass evar at the section's first `ic_loaded` contract.

### A6.59 `RiscvAdequacy`: THE FIVE ALLOCATIONS ARE LANDED, AND STEP 6'S
### REMAINING BILL IS THE ELEMENT CARVE

A6.57's inventory (i)–(iii) is **implemented**, in the record's own field
order, and the theorem now fixes the era's TSO initial state:

    kptb_ghost_alloc                       -> γkptb      (A6.53)
    ghost_map_alloc ((λ _, (0, None)) <$> gmem)  -> γts
    ghost_map_alloc_empty (nat -> pwmsg)   -> γlogm
    mono_nat_own_alloc 0                   -> γloglen
    TsoGhost.view_auth_alloc (avf g)       -> γview      (NEW lemma)

`view_auth_alloc` is the one piece that did not exist: auth AND fragment at
the same value, so the whole authority is ONE `own_alloc` with no update
(`vf tvs` is valid pointwise and includes itself — `auth_both_valid`).  It
is stated at an arbitrary view function so a later era can be born at the
view its predecessor left.

**THE THREE NEW HYPOTHESES, and they are one fact in three places.**  The
Ztso gstate carries three fields the SC one did not, and this theorem is
where their initial values are fixed: `glog = []`, `gimg = gmem`,
`gtv c = 0`.  Together they are exactly A6.57 item (ii)'s derivation:
`ts_ok` at the empty log is `latest img [] a 0 v`, i.e. `img = gmem`, and
`mm_ok`'s `gmem = flat gimg glog` is then `flat img [] = img`
definitionally, with `gtv c ≤ length glog` forced to 0.  They are
HYPOTHESES because this is the single-generation form; the power-cycle form
will get them from `boot_shape`, whose post-power state has an empty log by
construction.

**AND ONE MEASUREMENT THAT WAS NOT IN THE INVENTORY**: `riscvFixedGS` gained
TWO class slots under the flip (`riscvF_kptbGS`, `riscvF_tsomemGS`), so the
`RiscvFixedGS` constructor's positional underscore runs are 11 and 3, not
10 and 2.  The error names it as a type mismatch eleven fields away
(`Hmpre : gen_heapGpreS … while it is expected to have type ghost_varG Σ
log_mirror`) — worth knowing before reading it as a real mismatch.

**WHAT STEP 6 STILL OWES, and it is ONE item, not four.**  A6.57's (iv)
(`BootCarve.boot_led_ran`, `SpecEntry`'s two) is not a separate bill: it is
the same one.  The era's timestamp allocation hands back a big-op of
`ledger_elem0` FRAGMENTS — one per byte of `gmem` — and they have to be

- **cut at `text_end` in step with the bytes**, the text half PERSISTED into
  `RiscvPtsto.pristine_elem` (which is literally `a ↪[ts_name]□ (0,None)`)
  and handed to `BootCarve.boot_text_persist`, whose new premise is exactly
  that big-op;
- the DATA half handed to the client, which is a **new conjunct of the
  adequacy theorem's conclusion** — and therefore a change to every caller
  (`riscv_device_adequacy`, `SystemAdequacy`, `SpecMain`).

That conclusion change is the reason this is a tranche of its own and not a
tail of this one.  Nothing in it is a design question; the shape is fixed by
`boot_led_ran` (which already exists, already cuts, and already pairs the
elements back up with `boot_raw_ran`) and by `boot_text_persist`'s premise.
Beyond it, step 6's remaining structural pieces are unchanged from §7: the
eight per-hart mints and the power-cycle era's re-allocation.

### A6.60 FRONTIER AND HANDOFF AFTER THE SHIM-TAIL TRANCHE

**WHAT WENT GREEN IN THIS TRANCHE** (each was one of A6.57's nine):
`DiskBoot` (the zeroed-window words rebuild with `ctx_word4_pointsto_intro`
directly — the shim crossing there was a tier move for no reason),
`SwtchCtx` (A6.58's priced re-index), `WpSconfSfence` (A6.22's
register-only instance, statement unmoved), `WpSmodePtLeaves` (the plain
arm's price, both leaves).  `WpSconfMem` is the fifth, is fully ported, and is
**UNVERIFIED — its compile was TERMINATED, not failed.**

> **THE COST IS THE MEASUREMENT, AND IT IS THE TRANCHE'S ONE REAL STOP.**
> Post-flip `WpSconfMem.v` ran **30 minutes without finishing** and was then
> killed (`Error 143` = SIGTERM in the log; note that this is NOT a proof
> failure and must not be read as one).  It was WORKING, not looping —
> steady ~1.2 GB RSS growing linearly the whole time.  Both of its engines
> moved in this tranche (the read node onto `wordw_pointsto_load_c`, the
> write node onto the ledger append) and each is a forty-argument leaf
> application whose `R` is now a LAMBDA rather than a variable, which is the
> first thing to suspect: higher-order unification against
> `(fun bs => own_context ∗ Ψ bs)` at that arity is the plausible cost, and
> the cheap experiment is to `set (Ψc := …)` first so the leaf sees a head
> symbol instead of a lambda.
>
> Practical consequences, both worth carrying forward: **this file cannot be
> checked inside a ten-minute worker budget**, so iterate on it with a
> whole-tree `-k` sweep and read the error out of the log, never with a
> timed single-file make; and **nothing behind it was reached in this
> sweep** — the entire `Proof*` cone it gates, including the 35 files the
> shim sweep edited, is still uncompiled.
>
> **AND A PROCESS TRAP THAT COST AN HOUR OF FALSE READINGS, worth the two
> lines it takes to state.**  `pgrep -f "make -f CoqMakefile"` MATCHES ITS
> OWN WAITER: a shell running `until ! pgrep -f "make -f CoqMakefile"; do
> sleep; done` has that string in its own command line, so the loop never
> terminates and every poll reports "still running" forever — including long
> after the build is dead.  The same trap eats `pgrep -f rocqworker` (the
> `grep` in the pipeline matches itself).  Poll a build with the bracket
> idiom against the REAL process only —
> `ps -eo etime,args | grep "[r]ocqworker --kind=compile"` — and never
> conclude "the sweep is still running" from a bare `pgrep -f`.

**STILL RED — eight attempted-and-failed, plus `WpSconfMem`'s termination.
Four of the eight were EDITED after the sweep had already given up on them
(`WpSmodePtMemWrap`, `ProcInv`, `FsLookup`, `RiscvAdequacy`), so their next
compile is the first real news about them:**

- `UptWalkPt` — lane 2, and its price is now known exactly.
  `swp_translate_upt` already TAKES and RETURNS `own_context XI` (the user
  tree's slots are ledger words, so its A/D write-back owes the append);
  what is missing is the token in `TrampStepPt.tramp_tr_obl`, the □-obligation
  the walk is packaged as.  A □-obligation cannot capture a token, so the
  token has to be a parameter of its inner ∀ — taken and returned — which
  moves `tramp_tr_obl` itself.  **That is a change to a GREEN file**
  (`TrampStepPt`), with three producers (`UptWalkPt.utramp_tr_obl`,
  `Pt2WalkPt`'s two kernel ones) and two consumers, all of them
  pass-through.  Cheap, but not local.
- `UserMemPt` — lane 4.  `udata_own` is a big-op of `ctx_phys_pointsto`
  (A6.49's forced tier) and `udata_own_upd` still updates it with
  `phys_update`, the gen_heap-only law.  The successor is
  `TsoCtx.ctx_store_win_ok`, and the STATEMENT has to change shape with it:
  a store is ONE message (§1's payload ruling), so the update cannot stay a
  `foldr` over an arbitrary index list `l` — it becomes the window form over
  `write_bytes … n`.  **That is the one place in the user tier where the
  flip forces a spec change rather than a threading change.**
- `UmodeFetch` — lane 4's other half; the fetch obligation gained the
  `img`/`log` parameters and the file still passes a leaf-map hypothesis
  where a `bytemap → iProp` is expected.
- `WpSmodePtMem` — the 1/2/4-byte twin of `WpSmodePtLeaves`.  **Its claim
  half is DONE**: all four leaves now read the ppn, the canonicality and the
  tier pin straight off the ctx byte (A6.55's `ctx_pointsto_phys` +
  `ctx_phys_pointsto_ram`) instead of forgetting to `↦ₘ` and re-minting, so
  two of its three shim references are gone.  What is left is the same
  token threading `WpSmodePtLeaves` took — four statements in and out, the
  folded post, the leaf's `R`, and the obligation arm — with
  `SmodeCorePt.wordw_win_load_c` / `word{,4}_pointsto_write_c` at the leaf's
  width.  It is a copy of a worked proof, and it is the cheapest red file
  on this list.
- `WpSmodePtMemWrap`, `ProcInv`, `FsLookup`, `RiscvAdequacy` — all four are
  EDITED and unverified: the sweep had already given up on them when the
  fixes landed.  Their next compile is the first real news about them.

**THE SHIM TAIL'S LEDGER, closing:**

| class | sites | disposition |
|---|---|---|
| the stale stage-2 crossings | 45 | the ctx tower's own algebra (`ByteBuf`'s new `split4`/`join4`, `ctx_word{2,4}_pointsto_*`) |
| the honest FORGETS | 46 | `ctx_pointsto_forget` / `ctx_word_pointsto_forget` / `ByteBuf.ctx_buf_forget` |
| the identities (A6.18's tier already moved) | 17 | deleted |
| **the raw-tower RE-ENTRY** | **70** | **the five owners' re-tiering — its own tranche** |
| the M2 lock/park quarantine | 4 | `ProofAcquire` ×2, `ProofRelease`, `ProofSwtch` — `ctx_dom_sc` / `hart_view_lb_any`, exactly the sites the shim's header nominates |

`grep -l 'TsoCtxShim\.[a-z]'` is down from 47 files to 26, and of the 129
remaining mentions **52 are `Require` lines and seven are prose** (`ByteBuf` ×2, `BootCarve`, `KernelDataInv`,
`ProcInv`, `WpLock`, `TsoCtx` — each naming the dead lemma it replaced) and
one is `own_context_alloc`, which **has no caller left in the tree at all**:
`TsoCtxShim.v` is now dead weight and can be deleted the moment the
quarantine's four sites are paid.

**THE CLOSING MODEL-AWARE NUMBER: 728 of 1330** (`ls -la --time-style=full-iso
model-xv6iris/*.v *.vo` checked FIRST per A6.39 — the model `.vo` at
19:11:34 postdates its source at 18:37:36), **up from A6.57's 663**: 601
files compiled in the sweep, EIGHT attempted-and-failed, and ONE
(`WpSconfMem`) terminated after thirty minutes.  That number is a FLOOR,
not a frontier: `WpSconfMem` gates a large `Proof*` cone and the 35 files
the shim sweep edited never got their first compile behind it.

**SWEEP-INTEGRITY NOTE, and it resolves itself.**  `ProcDefs.v` was GREEN
when its two trapframe cells were re-tiered, so its `.vo` is now older than
its source and anything compiled against it in the tail of that run was
compiled against the OLD interface.  `make` fixes this on its own — the
next run rebuilds `ProcDefs` and, by timestamp, its whole cone — but the
number to trust is the one from a run started AFTER that edit, not the one
above.  Nothing else in the tranche has this shape: every other edited file
was red or unreached.

**FOR THE NEXT LANE, in the order they gate things:**

1. **`WpSconfMem` first, and give it an hour.**  It is ported and its
   compile was killed at 30 minutes, so nothing about it is known.  If it
   is still unbounded, the lambda-`R` experiment above is the first thing to
   try.  It gates a large cone, and the 35 shimfix-edited files get their
   first compile behind it; expect a batch of newly-reached M1-class fixes,
   one per file, per the standing rule.
2. `WpSmodePtMem` (worked precedent, mechanical) and `WpSmodePtMemWrap`.
3. The `tramp_tr_obl` token (lane 2) — small, but it moves a green file.
4. `UserMemPt`'s window-shaped store (the one forced spec change).
5. The five owners' re-tiering (A6.58's table) — the largest remaining
   block, and the last thing between the tree and a shim-free grep.
6. `RiscvAdequacy`'s element carve (A6.59) — the last structural piece.

## 7. Order of work

1. `iris/TsoMemPa.v` — the pure machine at machine types (NEW, no
   Iris): pwmsg/msg_byte/log_byte/visibleb/read_down/tso_read/own_pub/
   store snapshot/fence/flat + the latest-layer, ports of TsoMem.v +
   TsoCtxTwin.v's pure layer under the map-payload ruling.
2. `RiscvLang.v` — gstate fields, the arms, hart_node_step, DMA/power
   arms, in-file lemmas; `fence_drains` lives here (barrier_kind is the
   model's).
3. `RiscvPtsto.v` — era ghosts, `era_interp` conjuncts, view_lb/llb at
   machine types.
4. `TsoCtx.v` — the real bodies + law surface (twin images).
5. The lifting + leaves (HartSwp/HartSMem/HartMLoad/HartMStore/
   RiscvExec, WpSconfMem + PT trio + WpLock internals), error-driven —
   the `Require TsoCtxShim` grep is the worklist.
6. Adequacy (`RiscvAdequacy`/`SystemAdequacy`): initial-state ghosts
   (twin2_init's shape at boot), the eight per-hart mints.

Steps 1–4 are this session's target; 5–6 are the standing red tail the
tso branch exists to carry, worked file-by-file after.

## A6.39 — OWNER-RATIFIED (2026-08-26): the lock kit's designated
fallback at the real semantics is the parked-record + absorb idiom

When this workspace's step-5 tail reaches the lock tier (WpLock
internals, SpecAcquire/SpecRelease/ProofAcquire against the real
machine), the plan of record for the acquire-side payload transport is
still the twin's `ctx_dom_of_parked` at the AMO's at-the-top evidence.
**If that mint fights the real interp at the lock leaves, do not
wrestle it**: the owner has ratified the convergence of the lock kit
onto the parked-record idiom — `lock_inv`'s free arm holds
`∃ ξ T, ctx_parked ξ T ∗ R ξ`, release = `ctx_deposit` at
`T' ≤ t_release`, acquire = `ctx_absorb` from the AMO receipt, token
travels with the holder — which makes the acquire transport
INTERP-FREE and unifies the tree on one transfer algebra (deposit at
publish points, absorb at claim points).  Full statement, the
evidence-tie subtlety (`T ≤ t_release`, load-bearing only for
non-draining acquire paths like a plain-load TTAS spin), and the
expected client-file invariance:
`claude-notes/projects/tso-absorb-memo.md` §12.  Either way it is its
own tranche against a green main tree, with the bcache escrow as the
worked precedent.

> **LANDED ON MAIN, 2026-08-26 — `tso-port.md` §0.18′.**  The tranche ran
> on branch `tso` and the tree is green (clean 1315-file round, exit 0).
> Two things this note says are corrected by it, and both matter when the
> flip workspace reaches the lock tier:
>
> - **"token travels with the holder" is REFUTED, both it and the held-arm
>   alternative.**  `ctx_absorb` wants the record's token, the payload and
>   the claimer's `own_context` IN ONE HAND, and `own_context` is only in
>   hand OUTSIDE a WP leaf (a deposit or absorb cannot run inside a
>   `wp_..._au_...`; the bundle carrying it has already gone to the leaf).
>   A token that survives the held phase therefore forces either a
>   `ctx_deposit` inside the word-clear store's atomic update, or riding
>   the token inside `locked` — a resource change under 83 files.  **What
>   landed: a record minted PER PUBLICATION, at release, abandoned by the
>   winner that claims it.**  §12's own stamp analysis is what makes that
>   right: the tie `T' ≤ t_release` is per-publication, so no stamp needs
>   to ratchet across generations.
> - **Client-file invariance held exactly (ZERO), but the CREATORS moved.**
>   `newlock` has no `own_context` to deposit with, so the creator-side
>   transport is one quarantined `ctx_dom_sc` at `WpLock.lock_pay_intro`,
>   plus a `CtxMorph` class binder on the `newlock` family (free at call
>   sites; a `⌜⌝` slot on the two DELAYED forms, 3 sites).  At the real
>   semantics that lemma is the single compile error naming the
>   `own_context`-through-19-creator-call-sites cascade.
>
> Net for this workspace: at the lock tier, `ctx_dom_of_parked` is no
> longer on the critical path at all — the only thing the AMO must mint is
> the view receipt (`twin_passed_get`), and the acquire leaf's payload
> transport is `ZZAbsorbProbe.twin_absorb` against it.
