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
