# The machine flip: SC → Ztso in the kit, and the REAL Σ instantiation

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

RULING 1 (coherent ifetch + coherent page walk).  Instruction fetches
and translation-table walks read the FLAT memory and do not move the
hart's view.  Ztso as an ISA memory model governs EXPLICIT accesses;
fetch and PTW coherence are separate axes (Zifencei / Svvptc /
sfence.vma discipline), and xv6's uses are covered by stronger events
anyway.  This keeps the whole fetch-geometry and TLB lanes' proofs
against `gen_heap`(flat) — including the Svadu A/D write-back story —
out of the port, matching the standing "text is timestamp-0" ruling.
The honest weakening is recorded here; revisit only if the tree grows
self-modifying-code obligations (kexec's are deferred by owner ruling).

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

**THE RULING NEEDED.**  §0.10′ ruling 4 / §0.8′ ruling 6 declare
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
