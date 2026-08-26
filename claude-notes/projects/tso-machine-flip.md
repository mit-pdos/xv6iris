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
