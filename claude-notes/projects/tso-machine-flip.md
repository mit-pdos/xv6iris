# The machine flip: SC → Ztso in the kit, and the REAL Σ instantiation

M4, THE PREREQUISITE ROUND (2026-08-27, latest session).  **1091 of 1296,
RED 9** as of A6.81 (1088 for the rounds A6.73-A6.80 describe), over
rounds that rebuilt the whole tree from `RiscvLang` up and then
`WpSconfMem`'s 281-file cone on top.
**THE ATOMIC UNIT A6.77 HANDED OVER COULD NOT BE STARTED: three named
pieces of "everything below is landed" do not exist**, and one of them —
a degenerate window payload on the lock WORD — cannot be built at all
(`win_ok1`'s conjunct (1) fixes what may be written, and the lock word's
writer is an AMO storing the caller's register).  Two of the three are
now LANDED, additively and with zero client movement:
`WpSconfMem.wp_load_s_sconf_au_exv` (the value-UNKNOWN load, the only
shape the two racy lock reads can use — `_dat` names the value and serves
the holder route only), and `RiscvLang.mm_ok`'s third conjunct, **the era
image covers all of RAM**, which is what A6.74 §(3) always specified and
what closes A6.75 §(3)'s named residual without any per-cell payload.
The third is a TRANCHE, not a step: **the racy kit has no MINT**, and
cannot have a local one — `win_ok1` conjunct (1) quantifies over the whole
log, and the READER's conjunct (3) needs an own-last record a hart that
never touched the lock does not have.  Both close at the EMPTY LOG, so
what is owed is a boot mint plus its carve-to-`newlock` threading.

**THEN, ON THE COORDINATOR'S APPROVAL OF THAT TRANCHE, THE MINT WAS BUILT
AND CAME OUT LOCAL** (`TsoCtx.ledger_wpay_mint`, A6.79): its premise is
not the empty log but **the element's own timestamp being 0** -- the
interp's tie at such an element says *no message in the log writes this
byte*, which discharges conjunct (1), every agent's `own_last`, and the
clear word at once.  So the tranche moves OFF the boot carve: no
`newlock` creator cascade, no adequacy change, no barrier leaf.  The site
is **`initlock`'s own `lk->cpu = 0` store** (`initlock + 0x0e`,
`ProofInitlock:190`), mint-then-store in one leaf -- and its only
prerequisite is the boot-25 lane, re-entered as a **timestamp-0** lane
(`ctx_pointsto` hides `t`, so the witness must come from the carve, where
`BootCarve.boot_ctx_phys_word` already builds the honest cell with no
shim).  **THEN THE CARVE'S TIMESTAMP-0 EXIT WAS BUILT** (A6.80):
`BootCarve.boot_ledger_at0_word` hands the mint its input straight off
the carve (`ledger_elem0` IS `phys_ledger_at … 0`'s element, so the
bridge is `iFrame`), and `boot_ctx_of_mem_{byte,word,word4}` are the
honest replacements for the shim's dead raw→ctx conversions.  **The boot
25 is then a RESTRUCTURING, not a thread**: eleven of its thirteen
lemmas can take `boot_led_ran` beside `boot_raw_ran`, but
`bpay_raw_buf_raw` and `file_node_raw_fentry` take no range at all — they
convert already-carved raw BUNDLES — so the carve has to build ctx cells
directly and those two lemmas die with their raw bundle definitions.
**THEN THE BOOT 25 WAS PAID** (A6.81) -- and not by threading a second
range: `BootCarveMain`'s carve is 121 cuts and 7 stride families, so the
supplies are PAIRED in one predicate (`BootCarve.boot_cran`), the
`boot_cran_*` family is `boot_ran_*`'s statement for statement with its
CELL producers landing at the ctx tier directly, and the client's proof
text is a RENAME.  `BootCarveMain` IS GREEN with its 25 shim calls gone;
`power_boot_res` grew the element row the power arm never handed over;
the store AU is generalised in place (`wp_store_s_sconf_au_dat`, ~55
lines, not the ~350 estimated) and its `==∗` obligation is where a client
may MINT.  **BUT THE MINT'S SITE IS REFUTED**: `ProofPipealloc` calls
`initlock` on a `kalloc`'d page, whose cpu cell is at a timestamp `> 0`
(`kfree` memsets every freed page), so `ledger_wpay_mint`'s `e.1 = 0`
premise is unsatisfiable there and item 2's contract change would turn a
green file red.  A6.81 §(4) puts the three-way ruling to the coordinator
and the M4 line stops there; everything below the fork is landed.
Off the M4 line, **`VcGenS` is GREEN** (the leaves' `own_context` threaded
through the block WP) and its 85-file cone's two blockers are now measured
at line numbers: `ProofSwtch:157`'s conjured resume receipt, and
`ProofKernelvec:1704`'s ξ-indexed `devintr_caps` -- whose index enters
through `<{ P }>` at a `P` that is itself ambient-ξ (`cons_res`,
`tx_res`), not through `is_lock`, which is ξ-free.
**THE FLOOR WAS THEN RULED AND PROBED** (A6.82).  The owner's ruling on
§(4) is option (a) REFINED WITH A FLOOR: the window payload carries
`Bm`, the position of the MINT STORE, and `wpin`/`own_last` constrain
only messages at or above it, so a kalloc'd page's pre-mint garbage is
unconstrained; the reader pays with the stable pair
`hart_view_lb K ∗ ⌜Bm ≤ K⌝`, and **this is the canon pin's `B` and the
parked record's stamp a third time -- every history-shaped claim in this
port carries a floor and is claimed against a monotone receipt.**  THE
PROBE IS GREEN (twelve results, all closed) and its pure layer is landed
as `TsoMemPa` §12d, additively: `own_last` / `writer_pin` / `win_ok` are
the `Bm = 0` instances, proved as `iff`s.  The ruling's own claim is one
line (`read_down_shadow` IS `read_down_latest` at `t' := Bm`), but the
probe names a THIRD claim the sketch does not: **`win_ok` has to be
relativised too**, because xv6's `memset` is a byte loop and `kfree`'s
`memset(pa, 1, PGSIZE)` therefore appends PGSIZE one-byte messages, each
writing a proper subset of the window -- so the whole-window-or-none
property is false below the floor at exactly the cell the ruling exists
for, and the REASSEMBLY (`read_down_win`) takes it at every timestamp.
It survives, by the same shadow, as `read_down_win_fl`.  **AND THE FLOOR
INVERTS A6.79's FORCED ORDER: it must be STORE-then-mint**, because the
floor is the store's own position and conjunct (2b) asks that the floor
message have happened.
**A6.78 through A6.82 together are the record and the handoff.**

STEP 5, THE RULINGS TRANCHE (2026-08-27, latest session).  **CLEAN ROUND:
1083 of 1333, RED 14.**  Four owner rulings executed and one gate found missing.
**`BitmapInv` FLIPPED and the measured cost was ZERO consumer edits** —
one section binder, `ProofWritei` green, none of the ~90 consumers moved;
A6.58's raw-tower-owner table is now EMPTY.  **`↦ₛ` was OVERRULED
mid-tranche** (§0.21′): the kernel has dynamically generated strings
(`safestrcpy` at kfork/kexec), so pristine-as-definition is wrong; `↦ₛ`
stays raw here and its three rodata shim references are marked *awaiting
the §0.21′ port*.  Nothing was landed for it — which was the right outcome,
since the shape this tranche was converging on (a SPLIT: `↦ₛ□` pristine,
`↦ₛ{dq}` raw) is exactly what §0.21′'s single ctx tower replaces.  The
virtio width-2 asymmetry is routed to the DMA lane; the phys notation twin
is sequenced last, unstarted.  **THE PIN: `ProofKvminithart` and
`ProofMainSecondary` are GREEN** (`KptShare.kpt_creds` as a persistent
premise — A6.55's ruling one level down, the debt named on the unreached
boot chain), **but `ProofMain` is blocked on a gate nobody ever wrote**:
`kptb_unset` has no allocator, NOTHING moves a page table from `UTier ξ` to
`KTier B` (the canon pin's PUBLICATION step — designed at A6.53, consumer
side landed, producer side never written), and `kpt_bound` carries no
`llb`.  One coherent owner item, and the single blocker on the whole boot
tail.  **A6.70 is the record and the handoff.**

STEP 5, THE PT-CELL / BOOT-CONE TRANCHE (2026-08-27, latest session).
**THE PT-CELL STATEMENT HALF WAS THE CORK: 900 → 1080 of 1333, RED 16.**
The clean-round bill is paid (`rm -f *.vo`, model checked, one full round):
**900 of 1333** — same red set as A6.68's incremental round, so that round
was honest, but **the denominator is 1333 and A6.68's 901 counted a stale
`SystemAssumptions.vo`**.  `ProcInv` + `TfPage36` were pure statement
residue against A6.49's ledger-page move and gated the entire `Proof*`/boot
cone; fixing them (a local `↦ₚ₈c` notation for `TfPage36`'s 108 sites,
`ktier_pin_of_id` for `ProcInv`) bought 88 files at once and the cascade
took it to 1080.  **`iris/CtxKMap.v` now carries the identity crossing in
BOTH directions plus the `_ro_static` byte/buffer/word twins of
`ctx_pointsto_of_ro`** — the kit item the boot 26 was waiting on — and
`BootBridge`'s shim use is retired honestly (shim 30 → **29**; its problem
was never the read-only mint, it was that `stack_own_phys` is already
`ctx_phys` so the right primitive is the identity RE-ENTRY).  The boot 25
are SURVEYED in full (four shapes, one section, 13 lemmas, and a supply
chain `RiscvAdequacy:531` → `BootShared` (drops it) → `BootCarveMain`).
Four real findings behind the mechanical sweep: **`BitmapInv.v` is the last
unflipped raw-tower OWNER**; **`ProofMain` and `ProofKvminithart` are
blocked on the A6.53 PIN's boot threading, not on the lock kit**; the
virtio width-2 window is asymmetric post-flip (the DMA lease's own lane);
and **`↦ₛ` has not flipped**, which is what the remaining rodata three
cross on.  `WpSconfLock` untouched, parked as the M4 entry.  **A6.69 is the
record and the handoff.**

STEP 5, THE M2 TRANSPORT TRANCHE (2026-08-27, latest session).  **THE M2
TRANSPORT IS PAID FOR THE FIRST TIME, AND THE GATE IT NEEDED IS ONE A6.66
SAID DID NOT EXIST.**  `ctx_absorb`'s interp premise makes it unusable at
every M2 site (§0.17′ cuts both ways: `own_context` is only in hand OUTSIDE
a WP leaf, `tso_interp_at` only INSIDE one), and the interp was never
necessary — `TsoCtx.ctx_resume` already claims a parked record on a RECEIPT
alone.  `iris/TsoCtxAbsorbLb.v` proves the receipt-side pair
(`ctx_dom_of_parked_lb` / `ctx_absorb_lb`, no admits), which is
`tso-port.md` §0.18′'s statement character for character — fictional on
main, real here.  `SchedCtx.cpu_ctx_free` becomes a PARKED RECORD with the
hart's own receipt beside it and **`ProofScheduler` is GREEN**;
`ctx_cells_reindex` is the price and is NOT dead.  A6.67's ring was ten
files, not eight, and its real work is the boot ARRAY initializers
(`iris/SepThread.v`'s `big_sepL_fupd_thread`: `own_context` is exclusive, so
NBUF/NINODE lock creations must run in sequence).  `iris/CtxKMap.v` closes
A6.62's `ctx_phys` window for three files; `iris/SieCapCtx.v` is ported
from main.  `WpSconfLock` is REFILED: its blocker is the M4 racy owner cell,
not the rodata residue, which is why `ProofAcquire`/`ProofRelease` are
UNREACHED rather than red.  Shim: **still exactly 30 code references in five
files, verified — no tombstone.**  **901 of 1334, RED 14** (up from 875 of
1330, red 34) — TWO IDENTICAL INCREMENTAL `-k` SWEEPS at the same number,
with the model `.vo` checked to postdate its source first (A6.39); NOT a
`rm -f iris/*.vo` clean round, which this session did not have the wall
clock for and which the next tranche should pay before quoting 901.  **A6.68 is
the record and the handoff.**

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

### A6.61 `WpSconfMem` WAS NEVER SLOW — IT WAS ONE SENTENCE, AND THE
### OWNERS' TABLE IS WRONG BY TWO

**THE HEADLINE, AND IT RETIRES A6.60's MEASUREMENT.**  A6.60 recorded
post-flip `WpSconfMem.v` as "a ~20-minute single-file compile … working,
not looping" and the next run killed it at 30 minutes (Error 143).  Both
readings were guesses from OUTSIDE the process: the file had never been
observed to FINISH, and "~20 minutes" was an in-flight extrapolation.
`rocq compile -time` settles it, and the answer is not a slow file:

> **Everything in `WpSconfMem.v` up to character 31216 — 530 lines, both
> towers, the whole arithmetic preamble, 195 timed sentences — costs
> 4.57 SECONDS IN TOTAL, and the slowest single sentence in it is
> 0.665 s.  Then ONE sentence runs for the rest of the budget: the read
> engine's leaf application at `WpSconfMem.v:530`, the first thing inside
> its `2:{`.**  35 minutes of pegged CPU, RSS climbing to 1.34 GB and then
> flat, killed.  It is not the file, not the towers and not the flip's
> algebra.  It is one `iApply`.  (The file's other real cost is its
> `Require` prefix, ~3 minutes of loading that `-time` does not attribute
> to any sentence — worth knowing before blaming a proof.)

**WHY, AND THE FIX IS THREE WORDS.**  A6.36's overruling made the S-mode
load the PLAIN arm, so the leaf's `R` became the payload
`own_context ∗ Ψ bs` — and A6.60 noted in passing that `R` "is now a
lambda rather than a variable".  That passing remark WAS the bug.  The
lambda was written out TWICE inside a forty-argument application, once on
its own and once nested under `Mobl_ram_ex`:

    (fun bs => TsoCtx.own_context TsoCtx.cur_ctx ∗ Ψ bs)%I
    (Mobl_ram_ex width (pa_of ppn ea)
       (fun bs => TsoCtx.own_context TsoCtx.cur_ctx ∗ Ψ bs)%I)

Higher-order unification then has to guess the abstraction at both
positions while it works through forty arguments.  Naming it once gives
the leaf a RIGID HEAD:

    set (Psic := (fun bs => TsoCtx.own_context TsoCtx.cur_ctx ∗ Ψ bs)%I).
    …  Psic  …  (Mobl_ram_ex width (pa_of ppn ea) Psic)  …
    (* after the node closes, for the post's iDestruct pattern: *)
    rewrite /Psic.

**AND THE `set` ALONE IS MEASURED INSUFFICIENT — DO NOT INHERIT THIS AS A
SOLVED PROBLEM.**  With the `set` in place the same sentence was given a
FULL HOUR and did not finish: same 1.34 → 1.39 GB RSS plateau, same
non-termination, killed at 60 min.  The reason is that `set`'s local
definition stays TRANSPARENT, so the unifier may still delta-unfold it and
do exactly the guessing the naming was meant to prevent.  **The real fix
is a RIGID head, not merely a named one:**

    set (Psic := (fun bs => own_context cur_ctx ∗ Ψ bs)%I).
    assert (HPsic : Psic = (fun bs => …)%I) by reflexivity.
    clearbody Psic.

then `rewrite HPsic` in the TWO places that need the `∗`-shape back.
**TRIED IN A6.62′, AND IT DOES NOT WORK — read that note before acting on
this paragraph.**  The rigid head was killed at 57 minutes with an RSS
plateau matching the transparent run to 0.016%, which refutes the causal
story above.  The `set` is left in the file as harmless style; the real
cause is still open and A6.62′ names the one experiment that will settle
it.

> **THE DURABLE RULE, and it generalises past this file.**  At the
> forty-argument leaf applications (`swp_execute_LOAD_ram_*`,
> `swp_execute_STORE_ram_*` and their `_ex` forms), **never pass `R` as a
> lambda** — and when you name it, make it RIGID (`clearbody`), because a
> transparent `set` is not enough.
> The plain arm made every S-mode leaf's `R` a lambda, so this is a
> STANDING hazard for the whole leaf tier, not a `WpSconfMem` quirk.  And
> the diagnostic that found it is worth keeping: when a Rocq file appears
> to hang, `rocq compile -time` piped to a log and read WHILE IT RUNS
> names the sentence in the time it takes to reach it — here, four
> minutes to convert "the S-mode data engine does not compile" into "line
> 530 does not elaborate".  A6.60's "iterate on it with a whole-tree `-k`
> sweep and read the error out of the log" is superseded: the `-k` sweep
> tells you the file is red, `-time` tells you WHICH SENTENCE.

**WHAT LANDED IN THIS TRANCHE.**

- **`WpSmodePtMem` — DONE**, and it was exactly the copy of a worked proof
  A6.60 promised.  47 mechanical edits across the four leaves
  (`wp_clw_s_r_t` 4-byte load, `wp_ld_s_r_t` 8-byte load, `wp_csw_s_r_t`
  4-byte store, `wp_sd_s_r_t` 8-byte store) and their four KT0
  corollaries, taken straight off `WpSmodePtLeaves`'s diff: token in and
  out of each statement, into the folded post, into the leaf's `R`, into
  the obligation arm's spec list, and back out through the landing and the
  continuation.  The load arms swap `s_mem_chunk` for
  `SmodeCorePt.wordw_win_load_c` at their own width; the store arms swap
  `word{,4}_pointsto_write_c`'s `sigma.(mem)` for the `img σ log V` bundle
  and gain the `subst tv`.  **The file's last shim reference went with
  it** — `wp_ld_s_r_t`'s `ctx_buf_forget` … `TsoCtxShim.ctx_buf_of_mem`
  sandwich, whose return half is the FALSE direction — so the
  `Require TsoCtxShim` is deleted too.
- **The two REAL owner re-tierings — `BcacheInv` and `WaitInv`** (see the
  table below), plus their 21 dependent crossings and the 22 matching
  return-leg forgets, deleted across seven client files.  Seven files went
  shim-free; `ProofKwait` keeps one unrelated `ctx_buf_of_mem` on
  `p_xstate`.

**WHAT WAS MEASURED AND DELIBERATELY NOT LANDED**, because in both cases
A6.60's price is wrong by enough to change the decision:

- **`UptWalkPt` / `tramp_tr_obl`.**  The DIRECTION is confirmed by the
  compile error: `UptWalkPt.v:679` fails on `iSpecialize`, and the term it
  cannot instantiate begins `own_context XI -∗ upt_res_pt … -∗ …` —
  `swp_translate_upt` takes the token as its FIRST premise and the
  □-obligation has none to give.  A6.60 priced the repair at "three
  producers, two consumers, all of them pass-through".  **It is six files
  — `TrampStepPt`, `Pt2WalkPt`, `TransPt`, `UptWalkPt`, `UservecExitPt`,
  `UserretEntryPt` — and the pass-through claim is false at the point
  that matters.**  Inside `TrampStepPt` the obligation is CONSUMED five
  times (`iApply ("Htr" …)` at lines 635, 713, 742, 816, 878), all within
  `tramp_run_hart_active_instr_S`, and each consumer must SUPPLY a token
  it does not have: the payload `W` is framed AROUND the obligation by
  `swp_mono`, so it cannot carry one.  That lemma therefore gains an
  `own_context` premise, and the cascade runs out through
  `wp_instr_tramp_pt` / `wp_instr_ktramp_pt_share` into the four
  trap-handler files.  Its own tranche, against a green tree.  The
  definition in `TrampStepPt.v` is left BYTE-IDENTICAL with the finding
  recorded in a comment beside it.
- **`UserMemPt`'s window store.**  A6.60 has the shape right — the
  `foldr` over an arbitrary index list `l` becomes the window form,
  because a store is ONE message — and both call sites already instantiate
  `l := seq 0 (Z.to_nat k)`, so the caller side is free.  What A6.60 does
  not say is that `TsoCtx.ctx_store_win_ok` needs `tso_interp_at` and a
  gstate PAIR `g g'` with five side conditions, and `udata_own_upd`'s
  callers (`UserMemPt.v:747`, `UserMemMis.v:651`) hand it
  `gen_heap_interp m` and nothing else.  So the spec change is not one
  statement, it is the interp bundle threaded through
  `udata_own_store_g` to its own callers — and the proof needs a
  window-accessor over `udata_own`'s `big_sepM` (extract `n` bytes at
  consecutive addresses with a closing wand), which does not exist.  The
  old proof's per-byte induction is exactly what the payload ruling
  forbids, so it cannot be salvaged.  **Not a threading change and not a
  one-lemma change: its own tranche.**
- **`UmodeFetch`** is the remaining lane-4 half (the fetch obligation
  gained `img`/`log`); its error at line 561 is inside the
  `InstructionFetch` obligation arm, the same shape `WpSmodePtLeaves`
  already worked, and it is the cheapest of the three.

### THE OWNERS' TABLE IS WRONG BY TWO, AND THE TEST IS MECHANICAL

A6.58 named five raw-tower owners.  The test is one line — does the file
`Require Import TsoCtx` (in which case `↦ₘ/↦₂/↦₄/↦₈` are ALREADY the ctx
towers, `TsoCtx.v:3421–3468`) or not — and it says **three, and one of the
three is not the file A6.58 named**:

| A6.58's owner | verdict | why |
|---|---|---|
| boot carve's frame slots (26) | **REAL** | `BootCarve.v:61` is `Require TsoCtx` QUALIFIED ONLY, deliberately; its statements are bare `gen_heap pointsto`, one tier BELOW `↦ₘ` |
| `BcacheInv`'s LRU links (16) | **REAL — LANDED** | no TsoCtx import at all; `bcache_lru`/`bseg`/`blink_raw` held `↦₈` = `RiscvPtsto.word_pointsto` |
| `ProcInv`'s proc-slot cells (9) | **NOT AN OWNER** | `ProcInv.v:90` already imports TsoCtx; every `↦₈`/`↦₄` in it is ctx today.  The real owner of the five `p_parent` sites is **`WaitInv.v`** (`parents_own`), which A6.58 never names |
| `DiskInv` / devsw (4) | **NOT AN OWNER** | `VirtioDiskRwDefs` and `ConsoleInv` both import TsoCtx; the 3 survivors are a RAW KIT call (`InstrBytes.word_pointsto_join4`) and two explicit `word_pointsto` spellings inside `ProofFilewriteParts.fw_devidx`'s own statement |
| buffer/string windows (12) | **NOT AN OWNER** | all import TsoCtx; the raw enters through kit, and the ctx twins mostly already exist |

**SO THE RESIDUE IS NOT 70 DECISIONS ACROSS FIVE OWNERS.**  It is:

- **21 sites — LANDED here** (`BcacheInv` 16 + `WaitInv` 5).  Both files
  were single-section, used NO raw kit lemma by name and NO other flipped
  notation, and neither is reachable from `TsoCtx` (which reaches only
  `RiscvModelBytes`/`RiscvLang`/`RiscvPtsto`/`Ktier`/`TsoMemPa`/`TsoGhost`),
  so the re-tiering is two lines each — `Require Import TsoCtx.` and a
  `Context {XI : CurCtx}.` — and the 21 crossings plus 22 forgets delete.
  **Contrary to A6.58, this half IS compile-validatable from here**: both
  owners and all six of their downstream holders (`BreadLru`, `BioInv`,
  `BioInitAt`, `FsBoot`, `FsCfgBoot`, `ProcGeom`) are green.
- **26 sites — the boot carve, and it is the tranche's real design
  question.**  All three boot files are in `ctx_convert.py`'s
  `AMBIENT_BLACKLIST` BY NAME (lines 248–252) with the recorded reason
  *"a phantom ambient here is the boot_hart_res/eight-hart lesson"*, and
  `convert_ambient` also refuses any file without `Require Import TsoCtx`.
  **The tool cannot do this owner and must not be made to**; it needs
  explicit-ξ statements, or an owner ruling reversing the blacklist.
- **~22 sites — a second MECHANICAL sweep**, and three kit items close
  most of it: `ByteBuf.ctx_word_pointsto_join4` (exists, 6 sites),
  `TsoCtx.ctx_word{2,4}_pointsto_bytes` (exist, 4 sites), and **one lemma
  that exists nowhere in the tree — `ctx_pointsto_ktier_mono`**, the ctx
  twin of `RiscvPtsto.v:1362 mem_ktier_mono` (4 sites:
  `ProofCreateParts` ×2, `ProofForkretParts`, `ProofKexecTail`).  Plus 3
  `↦ₛ` forgets and the 3 `⊣⊢`→`⊢` weakenings.
- **`↦ₛ` — CONFIRMED IMMOVABLE, and it is exactly 3 sites**, not the
  vaguer set A6.58 implies: `ProofSyscall.v:2068` (`sysc_pname_app`),
  `ProofPrintk.v:1165` (`pk_str_byte`), `ProofPrintk.v:4429`
  (`pk_digits_data`).  All three are `↦ₛ□`/`↦ₛ{dq}` over READ-ONLY
  rodata, which is why a forget suffices.  The three `⊣⊢` that weaken are
  `ProofSyscall.sysc_pname_app` (`:2058`) — whose BACKWARD use at
  `ProofSyscall.v:4759` then stops typechecking, the one non-local
  consequence — and `DinodeSlot`'s `bb2_cell` (`:516`) / `bb4_cell`
  (`:528`), both `Local` and both consumed only by `dislot_acc_gen`.

`TsoCtxShim.v` itself is 43 lines declaring ONE thing, `own_context_alloc`,
and **no file in the tree references it**; the five names still in use
(`ctx_word_of_mem`, `ctx_pointsto_of_mem`, `ctx_buf_of_mem`,
`ctx_eslot_of_mem`, `ctx_pointsto_shim`) do not exist any more.  ~16 of the
surviving `Require TsoCtxShim` lines are already pure dead weight.

### THE ELEMENT CARVE — CHARACTERISED, FOR OWNER RATIFICATION

Step 6's one remaining item (A6.59).  **The statement is NOT changed here.**
This is the exact conjunct the system theorem's conclusion would gain, its
place, and its cascade.  Nothing below is landed.

**WHERE.**  `iris/RiscvAdequacy.v`, theorem `riscv_system_adequacy`
(declared line 410), in the client's resource bundle opened at line 495 —
inserted between lines 505 and 506, i.e. immediately after the existing
`↦ₘ` data conjunct and before the `kmap_auth kmap_M0` one.  It is the
THIRD conjunct of the bundle.

**THE CONJUNCT, VERBATIM:**

```coq
       (* THE ELEMENT CARVE (tso-machine-flip.md A6.59).  [↦ₘ] is the FLAT
          byte only ([mem_pointsto] = kmap claim + gen_heap [pointsto]); the
          ledger element that goes with it lives in the era's [ts_name]
          ghost_map, and THIS THEOREM'S [ghost_map_alloc] is its one and only
          supplier (A6.9 -- nothing above the interp mints one).  The TEXT
          half of that big-op is spent above: persisted into
          [RiscvPtsto.pristine_elem] and folded into [↦ₓ□] by
          [BootCarve.boot_text_persist].  This is the DATA half, at the same
          index map as the [↦ₘ] conjunct above it, so the client pairs the
          two byte-for-byte with [TsoCtx.ctx_phys_pointsto_of_elem] /
          [TsoCtx.phys_ledger_of_elem], and it is [BootCarve.boot_led_ran]'s
          content at [[text_end, ram_hi)] ([supra_text_ran], off [Hram]). *)
       ([∗ map] a ↦ _ ∈ filter (fun p : Arch.pa * bv 8 => text_end <= uint p.1)
                          g.(gmem), TsoCtx.ledger_elem0 a (DfracOwn 1)) ∗
```

Every name is checked against the tree: `TsoCtx.ledger_elem0`
(`TsoCtx.v:2135`, `:= (a ↪[ts_name]{dq} (0%nat, None))%I`) sits in a
section whose only binder is `Context {!riscvGS Σ}` — no `CurCtx`, no
`CurKtier` — so it typechecks at the theorem's `forall HR : riscvGS Σ`
binder; `TsoCtx` is reachable from `RiscvAdequacy` through
`BootCarve.v:61`; and the `filter …` term is a literal copy of
`RiscvAdequacy.v:504-505`, equal to `BootCarve.supra_text g`.

**AND THE SUPPLY IS ALREADY THERE, ON THE FLOOR.**  `RiscvAdequacy.v:645`
allocates `Htsfrags` from A6.59's `ghost_map_alloc` and **never mentions it
again** (only `Htsauth` is used, at 750/780/784).  The carve is four proof
lines at the 710–712 block: `big_sepM_fmap`, split at `text_end`, persist
the text half, frame the data half into the bundle at 715/719.

**THE CASCADE, and it names two ALREADY-STALE call sites:**

1. `RiscvAdequacy.v` itself — and **line 711 is stale today**:
   `iMod (@boot_text_persist Σ HR g Hram with "Hkbundle Htext")` passes two
   resources while `BootCarve.boot_text_persist` (`BootCarve.v:184`)
   already takes three, the middle one being
   `([∗ map] a ↦ _ ∈ sub_text g, pristine_elem a)`.  The carve is what
   fills that slot.
2. `BootCarve.v` §9 — two new lemmas: an element twin of `boot_bytes_split`
   (`:153`, proof verbatim: `map_filter_union_complement` + `supra_co_sub`),
   and the persist `ledger_elem0 … (DfracOwn 1) ==∗ pristine_elem`
   (`boot_ran_persist`'s shape at `:489`, with `ghost_map_elem_persist`) —
   one `big_sepM_bupd`, since the two are the same key at `DfracOwn 1` vs
   `DfracDiscarded`.  A third if the filter spelling is kept:
   `supra_text_ran` (`:333`) must stop being `Local`.
3. `RiscvAdequacy.riscv_device_adequacy` (`:838`) — one extra `_` in the
   destructure at `:895`.
4. `RiscvAdequacy.power_boot_res` (`:981`) + `wp_power_loop`'s PowerOn arm
   (`:1304`) + `riscv_power_adequacy` (`:1507`).  **Note the era record
   built at `:1270` is still short by ALL FIVE flip gnames** (`γkptb`,
   `γts`, `γlogm`, `γloglen`, `γview`) — A6.59's four `iMod`s have to be
   copied into that arm first.
5. `BootShared.v` — `power_boot_res_unpack` (`:1121`, destructure `:1350`)
   and `boot_shared_alloc`'s image block (`:1357-1373`), where **`:1358`
   is stale in exactly the same way as `RiscvAdequacy.v:711`** and
   **`:1373`'s `kernel_data_intro` is stale too** (`BootCarve.v:561`
   already demands a second resource, `pristine_va` over
   `[text_end, rodata_end)`).  Also `boot_hart_stack_raw` (`:275`) calls
   `boot_stack_own_phys` with one resource at `:286` while
   `BootCarve.v:1266` now takes two.
6. `SystemAdequacy.xv6_boot_era` (`:264`, states it at `:287`, feeds
   `boot_shared_alloc` at `:305`) and both `refine` sites (`:550`, `:709`)
   — pass-through.
7. `SpecEntry.v` — **no change, and it is the reason for the Dfrac
   choice**: `wp_entry_boot_body` already takes `TsoCtx.pristine_win
   mb_ld_ea 8`, and `mb_ld_ea` is in the DATA half, so those 8 persisted
   elements must come out of this conjunct.

**NOT in the cascade:** the log/loglen/view fragments.  `TsoGhost.llb`'s
`⌜K = 0⌝` disjunct and `TsoCtx.ctx_phys_pointsto_of_elem`
(`TsoCtx.v:2145`, `iLeft. iApply llb_0.`) make the clean arm free at
timestamp 0, so **the element alone is the whole bill — the conclusion
gains exactly ONE conjunct, not four.**

**FIVE QUESTIONS FOR THE OWNER, and the carve should not land until they
are answered:**

1. **Index spelling** — the `filter …` form above (zips byte-for-byte with
   the sibling `↦ₘ` row) or `boot_led_ran g text_end ram_hi`
   (`BootCarve.v:1183`, the client's own vocabulary)?  Interconvertible
   under `Hram` by `supra_text_ran`, which is `Local` today.  A6.59's "the
   shape is fixed by `boot_led_ran`" reads as fixing the RESOURCE
   (`ledger_elem0` at `DfracOwn 1`, one per byte), not the index term.
2. **Who persists the read-only sub-range?**  `kernel_data_intro` wants
   `pristine_va` over `[text_end, rodata_end)`.  Assumed above: the
   conclusion hands the whole data half at `DfracOwn 1` and the client
   persists (one new `BootCarve` lemma, conclusion stays one row).  The
   alternative is a THREE-way conclusion.
3. **Three names for one body** — `RiscvPtsto.pristine_elem` (`:1535`) and
   `TsoCtx.pristine_byte` (`:1454`) are literally the same term under two
   names in two files.  Alias one, or is the duplication deliberate tier
   hygiene?
4. **Is `power_boot_res`'s twin in this tranche?**  The carve's only real
   consumer is on the power path (`BootShared.boot_shared_alloc`), so
   shipping the conjunct into `riscv_system_adequacy` alone leaves it
   consumed by nobody but a `_`.
5. **Dfrac before persisting** — new persist lemma in `BootCarve` §9
   (assumed), or fold `ghost_map_elem_persist` into `boot_text_persist`
   and change an already-green statement in a green file?

### THE ONE CASCADE `WpSmodePtMem` OPENS, AND IT IS NOT `WpSmodePtMemWrap`

`WpSmodePtMemWrap` was already token-threaded and went GREEN against the
finished leaves on its first compile — the four sp-relative wrappers cost
nothing.  The bill lands one tier further out, and it was not on A6.60's
list:

> **`VcGenS.v` (1539 lines) contains ZERO `own_context` and calls the
> sp-relative wrappers at four sites** (`wp_csdsp_gpr_s_r_t` /
> `wp_cldsp_gpr_s_r_t`, lines 510, 544, 1006, 1041).  So
> `wp_vc_block_s_den_r` (`:378`) — the block verification-condition lemma,
> a big induction with a continuation — has to take and return the token,
> and the cascade runs on to its five consumers: `IntrDefs`,
> `ProofKernelvec`, `ProofSwtch`, `SRegime`, `WpSwtchVc`.  **That is the
> scheduler/trap tier, and it is this tranche's real successor.**

Threaded through an induction it is the same mechanical shape as the
leaves, but it is six more files and it was reached only because the leaf
statements finally moved.  Not landed here; characterised, like the two
above it.

### TWO PROCESS RULES THIS TRANCHE PAID FOR

Both cost real time here and both are cheap to obey.

**1. THE INVISIBLE STALENESS, and why A6.25's no-concurrent-make rule is
about CORRECTNESS, not contention.**  Two sweeps overlapped this tranche
(~02:05–02:19) while edits were landing.  The damage a concurrent make
does is not a race on one `.vo` — it is that a `.vo` COMPLETED during the
window is *newer than the source it disagrees with*, so `make` will never
rebuild it and every number downstream is quietly wrong.  A6.60's
`ProcDefs` note has the same shape but the benign polarity (`.vo` older
than source; `make` self-heals).  **The rule: after any window in which a
build overlapped an edit, delete every `iris/*.vo` whose mtime falls in
that window (with its `.vok`/`.vos`/`.glob`/`.aux`) before the next
`make`.**  Here that was 79 files and one minute — 731 `.vo` down to a
trustworthy 652 — against a full clean measured in hours.  A whole-tree
wipe is the wrong instrument for this; the window is.

**2. THE `pgrep` TRAP, which ate two sweeps.**  `pgrep -f "make -f
CoqMakefile"` and `pkill -f "rocqworker…"` MATCH THE POLLING SHELL'S OWN
COMMAND LINE.  A predecessor's `until ! pgrep -f "make -f CoqMakefile"`
waiter therefore never terminates (it is its own match), and a `pkill -f`
on the same string kills the wrapper it is running inside — which is what
produced two orphaned `WpSconfMem` workers reparented to init, running
concurrently, attributable to nobody.  **Poll with `ps -eo pid,comm` and
an anchored `^(make|rocqworker)$`, kill by PID, never by `-f` pattern.**

### FRONTIER AND HANDOFF

**THE CLOSING NUMBER: 731 of 1330 — AND IT IS A DIFFERENT KIND OF NUMBER
FROM A6.60's 728.**  A6.60's was a floor taken while `WpSconfMem` was in
flight and, as it turns out, with 79 `.vo` in the tree that had been built
during a concurrent-sweep window.  This one is built from a TRUSTWORTHY
FLOOR: those 79 were deleted with their `.vok`/`.vos`/`.glob`/`.aux`
(731 → 652), the model `.vo` was checked to postdate its source per A6.39
(19:11 vs 18:37), and the tree was rebuilt from there in one `make -j12 -k`
with no other build running.  **731 is honest; 728 was not comparable.**

It is still a FLOOR in the one way that matters: `WpSconfMem` never
compiled, so its cone — roughly 600 files, including every `Proof*` — has
still not had a first compile after the flip.

**THE RED SET IS SEVEN, and every one is characterised:**

| file | what it is |
|---|---|
| `WpSconfMem` | the one sentence, above.  Try `clearbody` next |
| `UptWalkPt` | the `tramp_tr_obl` token — six files, not three |
| `UserMemPt` | the window store — needs the interp bundle threaded and a new `big_sepM` window accessor |
| `UmodeFetch` | the fetch obligation's `img`/`log`; the cheapest of the three |
| `VcGenS` | NEWLY REACHED — the leaves' token reaching the VC generator; six more files |
| `ProcInv` | the trapframe LEDGER page (A6.49); `iExact` at `:601` |
| `TfPage36` | NEWLY REACHED, and its cheap fix is LANDED (the section's ambient binder, which had to be spelled `TsoCtx.CurCtx` — the file does not import TsoCtx, so a bare `CurCtx` silently declares a fresh `Type` variable and the error moves one line, not away).  Its residue is the same tier as `ProcInv`'s: `tf_words36`'s statement still spells the raw `↦ₚ₈`, and **TsoCtx declares no `↦ₚ₈` notation at all** — the ctx phys-word tower is only reachable as `TsoCtx.ctx_phys_word_pointsto`.  Settle `ProcInv` first; the two are one cascade |

**WHAT IS VALIDATED AND WHAT IS NOT, precisely.**  Green and checked this
tranche: `WpSmodePtMem` (with `WpSmodePtMemWrap` green on top of it),
`BcacheInv`, `WaitInv`, `BreadLru`, `TrampStepPt` (restored byte-identical
modulo comments), `FsLookup`, `ProcDefs`.  **NOT validated: the 21 deleted
crossings and 22 deleted forgets in the seven owner-client files**
(`ProofBinit`, `ProofBread`, `ProofBrelse`, `ProofKexit`, `ProofReparent`,
`ProofKwait`, `ProofKforkB5`) — all seven sit in `WpSconfMem`'s cone and
were never reached.  The owners moved and their accessors typecheck; the
clients are a promise until that cone opens.

`grep` for real `TsoCtxShim.<lemma>` sites is **down to ~50 across 26
files** from A6.58's 181/A6.60's 70-plus-prose, and `TsoCtxShim.v`'s single
declaration still has no caller anywhere.

**FOR THE NEXT LANE, in the order they gate things:**

1. Re-sweep behind `WpSconfMem`.  Its cone and the 35 shim-swept files
   still have not had a first compile; expect a batch of newly-reached
   M1-class fixes, one per file, per the standing rule.
2. `UmodeFetch` (the cheapest of the three lane-4 halves), then
   `WpSmodePtMemWrap`.
3. The `tramp_tr_obl` token — SIX files, not three, and
   `tramp_run_hart_active_instr_S` gains a premise (this note, above).
4. `UserMemPt`'s window store — the interp bundle threaded to
   `udata_own_store_g`'s callers plus a new `big_sepM` window accessor.
   Not a one-lemma change.
5. The boot carve's 26 sites — the blacklist ruling.
6. The mechanical ~22, of which `ctx_pointsto_ktier_mono` is the one
   lemma that must be written.
7. The element carve, after the five questions are answered.


### A6.62′ THE RIGID HEAD DOES NOT PAY EITHER — AND A6.61's DIAGNOSIS OF
### `WpSconfMem` IS REFUTED BY ITS OWN NEXT EXPERIMENT

The commissioned one-attempt-at-the-hour-budget ran.  `set` + `assert` +
`clearbody`, with `rewrite HPsic` restoring the `∗`-shape inside the
RAM-obligation arm and after the node — i.e. a payload name the unifier
**cannot** unfold.  **Killed at 57 minutes, same sentence, no `.vo`.**

And the measurement that matters is not the wall clock, it is the memory:

| run | payload | RSS plateau |
|---|---|---|
| A6.61 first | raw lambda ×2 | 1 339 520 B |
| A6.61 second | `set`, transparent | 1 391 132 B |
| this one | `clearbody`, RIGID | 1 391 352 B |

**The transparent and the rigid run agree to 0.016% on a 1.39 GB working
set.**  Two elaborations doing materially different higher-order guessing
do not land that close.  So A6.61's causal story — "the unifier is guessing
the abstraction at both positions" — **is refuted**: naming the payload,
rigidly or not, changes nothing, and the duplicated lambda was a RED
HERRING.  A6.61's "durable rule" survives only as style advice; it is not
this file's bug and it should not be inherited as a diagnosis.

**WHAT IS STILL TRUE AND WORTH KEEPING:** `-time` localised the cost to one
sentence and that has not changed — 195 sentences at 4.57 s total, then the
`iApply` at `WpSconfMem.v:530`.  The cost is inside that application, but
it is NOT in the payload argument.

**THE NEXT DIAGNOSTIC, and it is cheap and decisive.**  The `iApply` does
two separable things: it ELABORATES a forty-argument application, and it
UNIFIES the result with the WP goal.  Split them so `-time` can bill each:

    iPoseProof (swp_execute_LOAD_ram_Sw_ex (CID := CID) width … all 40 …)
      as "Hleaf".
    iApply ("Hleaf" with "…").

If the `iPoseProof` is the slow half, the problem is telescope elaboration
— and the next suspect is the *other* computed argument,
`Mobl_ram_ex width (pa_of ppn ea) Psic`, which should be `set` in its own
right before anything else is tried.  If the `iApply` is slow, it is
goal unification and the leaf's conclusion shape is what needs attention.
**One compile answers it**, and no further guesses should be spent before
that answer exists.

**OPERATIONALLY, per the ruling:** the file is a standing cost.  It must
not be allowed to block eleven idle cores again — schedule it LAST, and
never diagnose it with a timed single-file `make`; run the whole-tree `-k`
sweep and read `-time` out of a separate log.

### A6.62 THE MECHANICAL TRANCHE IS DONE, AND IT ENDED BY FINDING THAT
### THE `↦ₛ` RESIDUE IS BLOCKED ON THE ELEMENT CARVE

Worked against the coordinator's rulings of 2026-08-27 (carve Q1–Q5, and
the boot blacklist STANDS).  A6.61's shim residue went from **38 real
sites in 11 files to 30 in 5**, and the 30 are now exactly two things: the
boot carve's 26, which the ruling reserves for hand-written explicit-ξ
statements, and **four sites that are not mechanical at all and were
mis-classified twice**.

**THE ONE NEW KIT LEMMA, as commissioned:** `TsoCtx.ctx_pointsto_ktier_mono`
(`TsoCtx.v`, beside `ctx_pointsto_phys`) — the ctx twin of
`RiscvPtsto.mem_ktier_mono`.  Sound for the raw lemma's reason and no new
one: of `ctx_pointsto_def`'s seven conjuncts only `ktier_pin` mentions the
tier and it weakens (`ktier_pin_mono`); **the timestamp, the ledger element
and the clean/dirty bit are tier-BLIND**, which is why this is a weakening
and not a re-mint and why A6.9's prohibition is not in play.  It retired
the four sites that reached KT1 by dropping to the raw tower and crossing
back (`ProofCreateParts` ×2, `ProofForkretParts`, and — differently —
`ProofKexecTail`).

**WHAT ELSE LANDED, all of it the same discovery repeated:** nearly every
remaining "crossing" was a **round trip to nowhere**, because `↦ₘ`, `↦₂`,
`↦₄` and `↦₈` are ALL the ctx towers already (`TsoCtx.v:3421–3468`) and
only the *lemma names* in the proofs were still raw.

| site | what it actually was |
|---|---|
| `ProofSysKill`, `ProofSysOpenParts`, `ProofSysPause`, `ProofSysUnlinkParts` | raw `word_pointsto_join4` + shim → `ByteBuf.ctx_word_pointsto_join4` |
| `VirtioDiskRwDefs` ×2 | the same join, twice |
| `ProofFilewriteParts.fw_devidx` | the file's **only** raw spelling — every other cell in it is already `ctx_word_pointsto`; the statement moved and the crossing/forget pair deleted |
| `ProofSysPipe` ×2, `ProofKwait` | `↦₄`'s byte run IS copyout's context-indexed window; the "seam" was an identity |
| `ProofDirlink`, `ProofDirlookupParts` | raw `word2_pointsto_bytes`/`_intro` on a ctx buffer |
| `ProofKexecTail`'s `kxc_*_of_*` pair | stated over the raw `word4_pointsto` while its only consumer (`ProofKexecA:1449/1513`) feeds it straight to a `↦₄` leaf with **no crossing in between** — so the pair had to be ctx or the caller could never have typechecked |

**AND 23 DEAD `Require TsoCtxShim.` LINES ARE GONE**, checked against a
comment-stripped grep so a file is only unhooked when it has no real use
left.

### TWO CORRECTIONS TO A6.58's DISPOSITIONS, IN OPPOSITE DIRECTIONS

**1. `DinodeSlot`'s two `⊣⊢` DO NOT WEAKEN — they were identities.**
A6.58 (and A6.61's own table, inherited) listed `bb2_cell`/`bb4_cell` with
`ProofSyscall.sysc_pname_app` as `⊣⊢` that must become `⊢`.  Wrong: **both
sides of both are the context tower** (`↦ₘ` is `ctx_pointsto cur_ctx`,
`↦₂`/`↦₄` are `ctx_word{2,4}_pointsto cur_ctx`), so the per-byte step is
`reflexivity` and only the *unfold* had to name the ctx definition.  Same
for `ProofDirlookupParts.dlk_half_acc`.  **Three `⊣⊢` statements keep their
strength**; the "weakening" class is one member smaller than advertised and
that member is item 2.

**2. THE `↦ₛ`/RODATA SITES NEED THE OPPOSITE DIRECTION FROM THE ONE A6.58
PRESCRIBED, AND A FORGET CANNOT PAY THEM.**  A6.58: "its sites take the
forget".  Measured, they do not:

- `ProofPrintk:1165` — the format string is rodata at the raw `↦ₛ` tower
  and the byte must reach a **ctx** load slot: `mem → ctx`, the FALSE
  direction.  The forget at the end of that accessor is the easy half.
- `ProofPrintk:4429` — `kernel_data_string` is `KernelDataInv`'s RAW image
  byte and `pk_digits` is the flipped `↦ₘ`: again `mem → ctx`.
- `ProofSyscall:2058/2068` — `sysc_pname_app`'s `⊣⊢` really does weaken to
  `⊢`, but **that is not the end of it**: `ProofSyscall:4759` uses the
  BACKWARD direction to rebuild the proc-name buffer after the printk call
  (`iDestruct (sysc_pname_app …) as "Hnm"` from `[Hstr Hpad]`).  Weakening
  the lemma deletes a step the proof depends on.

> **AND THE FIX IS ALREADY IN THE KIT — IT IS JUST NOT SUPPLIED YET.**
> `TsoCtx.ctx_phys_pointsto_of_elem` (`:2174`) is exactly
> `phys_pointsto a dq v -∗ ledger_elem0 a dq -∗ ctx_phys_pointsto ξ a dq v`,
> and its proof is `iExists 0%nat … iLeft. iApply llb_0.` — **at timestamp
> 0 the clean arm is FREE**.  A read-only byte therefore has everything it
> needs for a ctx fact except the `ledger_elem0`, and **the era's
> `ghost_map_alloc` in `RiscvAdequacy` is the only supplier of those in the
> whole system (A6.9).  That allocation IS the element carve.**
>
> So the four residual non-boot sites are **BLOCKED ON A6.61's ELEMENT
> CARVE**, and under carve Q2's ruling (the client persists the data half)
> rodata at `[text_end, rodata_end)` lands in exactly the right half.  The
> kit item this creates is the VA-level twin of the existing lemma —
>
>     Lemma ctx_pointsto_of_ro (ξ : CtxId) (a : Arch.pa) (dq : dfrac) (v : bv 8) :
>       mem_pointsto a dq v -∗ pristine_elem a -∗ ctx_pointsto ξ a dq v.
>
> — and it should be written WITH the carve, not before it.  This is a
> dependency A6.59/A6.61 did not see: **the carve is not only step 6's last
> structural piece, it is what unblocks the last of step 5's shim tail.**

`WpSconfLock:146` is the fourth and is a different shape again: the cell is
forgotten to raw so `wordw_claim_of` can derive a persistent `#Hc8`, then
needed back as ctx.  Since the claim is persistent and derived, the honest
repair is a ctx-tier `wordw_claim_of` (read-only, so the same timestamp-0
argument applies) rather than a round trip.

### WHAT IS AND IS NOT VALIDATED

`TsoCtx.v` is edited, so the closing rebuild re-derives its whole cone —
which is the only reason any of this tranche gets checked at all.
**Everything else edited here lives in `WpSconfMem`'s unopened cone and is
a promise until that one sentence elaborates.**  The tranche is mechanical
by construction (every edit swaps a raw lemma name for the ctx twin that
already exists, at a statement whose tier was already ctx), but mechanical
is not the same as checked, and the next lane should read the first sweep
behind `WpSconfMem` as the real news about all of it.

### CLOSING NUMBER AND WHAT THE REBUILD PROVED

**731 of 1330, and this one is REBUILD-VALIDATED.**  `TsoCtx.v` was edited
(the new `ctx_pointsto_ktier_mono`), so the closing `make -j12 -k`
re-derived its entire cone: **657 files recompiled**, model `.vo` checked
to postdate its source first per A6.39 (19:11 vs 18:37), one make, nothing
else running.  The red set came back **unchanged at seven** — no edit in
this tranche broke anything that was green.

The rebuild also drew the validation line exactly:

| validated GREEN by this rebuild | still a promise (behind `WpSconfMem`) |
|---|---|
| `TsoCtx` (the new lemma), `ByteBuf`, `BcacheInv`, `WaitInv`, `BreadLru`, `WpSmodePtMem`, `WpSmodePtMemWrap` | every `Proof*` edit of A6.61 and A6.62 — the 21 owner-client deletions, all ten mechanical collapses, `DinodeSlot`, `ProofDirlookupParts`, `VirtioDiskRwDefs`, `ProofKexecTail`, `WpSconfLock` |

**AND THE REBUILD MADE THE OPERATIONAL COST CONCRETE.**  The sweep reached
657 compiles and then sat for ten minutes with **one** `rocqworker` alive
and eleven cores idle — `WpSconfMem`, alone, gating roughly 600 files.
That is the whole argument for scheduling it last: it is not merely slow,
it converts a twelve-core sweep into a one-core one.

### THE ORDER THAT NOW FOLLOWS FROM THE RULINGS

1. `WpSconfMem`'s one sentence.  If the rigid head does not pay, the file
   is a standing cost and should be scheduled LAST in every sweep so it
   never blocks the other eleven cores again.
2. The element carve, per Q1–Q5 — **promoted, because item 5 below now
   depends on it**: client vocabulary (`boot_led_ran`, `supra_text_ran`
   promoted to Global), one-row conclusion at `DfracOwn 1` with the client
   persisting, `pristine_elem`/`pristine_byte` aliased with a tier-hygiene
   comment (record the import-order direction), `power_boot_res`'s twin in
   the same tranche, and the new persist lemma in `BootCarve` §9 rather
   than churning a green statement.
3. The boot carve's 26, hand-written explicit-ξ per the standing blacklist.
4. `UmodeFetch`, then the `tramp_tr_obl` six and `UserMemPt`'s window
   store.
5. `ctx_pointsto_of_ro` and the four `↦ₛ`/rodata sites — after (2).
6. `VcGenS` and the scheduler/trap tier (A6.61) — the successor tranche.


### A6.63 THE ELEMENT CARVE IS IMPLEMENTED — AND IT UNBLOCKS THE BOOT 26
### AS WELL, WHICH MEANS A6.58's OWNER TABLE HAD THE DEPENDENCY BACKWARDS

Built to the ruled Q1–Q5.  **The theorem's conclusion gains exactly one
conjunct**, at `RiscvAdequacy.v:520`, between the `↦ₘ` data row and
`kmap_auth`:

```coq
       BootCarve.boot_led_ran g text_end ram_hi ∗
```

Q1 (client vocabulary) is why it is `boot_led_ran` and not the `filter`
term, and paying for it was one word: **`supra_text_ran` promoted from
`Local`** (`BootCarve.v:334`), which is the bridge between §2's
`text_end`-and-above half and the range vocabulary.  Q2 (the client
persists) is why it is one row at `DfracOwn 1` rather than a three-way
split.

**THE SUPPLY WAS ALREADY ON THE FLOOR, EXACTLY AS A6.61 FOUND.**
`RiscvAdequacy.v:645`'s `ghost_map_alloc` produced `Htsfrags` and the proof
never mentioned it again, while `boot_text_persist` — which has taken a
three-resource form since it was written — was being called with two.  The
carve is what closes both holes at once, and it is four lines:

```coq
  iEval (rewrite big_sepM_fmap) in "Htsfrags".
  iDestruct (@boot_led_all_split Σ HR g Hram with "Htsfrags")
    as "[Hledtext Hleddata]".
  iMod (@boot_led_text_persist Σ HR g with "Hledtext") as "#Hpristext".
  iMod (@boot_text_persist Σ HR g Hram with "Hkbundle Hpristext Htext") as "Htext".
```

**TWO NEW LEMMAS IN `BootCarve` §9**, both as ruled:

- `boot_led_all_split` — the element twin of `boot_bytes_split`, cut at
  `text_end` **in step with the raw bytes** so the halves pair byte for
  byte, landing the upper half as `boot_led_ran g text_end ram_hi`.  Proof
  is `boot_bytes_split`'s verbatim plus the `supra_text_ran` rewrite.
- `boot_led_text_persist` — Q5's new lemma rather than churning
  `boot_text_persist`'s green statement.  One `big_sepM_bupd` over
  `ghost_map_elem_persist`, because **`pristine_elem` IS `ledger_elem0` at
  `DfracDiscarded`** — same key, same value.

**Q3, THE ALIAS, AND THE DIRECTION IS RECORDED:** `TsoCtx.pristine_byte`
was a character-for-character duplicate of `RiscvPtsto.pristine_elem`.
**TsoCtx imports RiscvPtsto, so `pristine_elem` is the definition and
`pristine_byte` is now the alias** — never the other way round.  Kept a
`Definition` (not a `Notation`) so both instances and every existing
`rewrite /pristine_byte` keep working; the bodies are convertible, so no
proof in the tree changes.

**AND THE KIT ITEM THE `↦ₛ` RESIDUE NEEDED, `TsoCtx.ctx_pointsto_of_ro`:**

```coq
  Lemma ctx_pointsto_of_ro `{KTR : !CurKtier} (ξ : CtxId) (a : Arch.pa)
      (ppn : mword 44) (dq : dfrac) (v : bv 8) :
    kmap_at (svpn_of a) ppn KP_rw -∗
    mem_pointsto a dq v -∗
    ledger_elem0 (pa_of ppn a) dq -∗
    ctx_pointsto ξ a dq v.
```

The caller supplies `ppn` with its `kmap_at` witness — every leaf site
already holds one — so the element is indexed at the PHYSICAL address,
exactly as `ctx_pointsto_def` holds it, and `kmap_at_agree` ties the two
`ppn`s inside.  It is payable for one reason and it is worth restating:
**at timestamp 0 the clean arm is free** (`TsoGhost.llb_0`), so a byte
needs no new authority to enter the tier — it needs its ledger element,
and A6.9 says the era's allocation is the only supplier.

> **A LANDING NOTE THAT COST A COMPILE:** the first placement put
> `ctx_pointsto_of_ro` at `TsoCtx.v:1748`, four hundred lines ABOVE
> `ledger_elem0`'s definition (`:2171`).  `TsoCtx.v` is one 2000-line
> section and the kit is NOT in dependency order by eye — put a new lemma
> beside the one it is the twin of (`ctx_phys_pointsto_of_elem`), not
> beside the one it reads like.

### AND THE CARVE FLUSHED OUT WHY `RiscvAdequacy` HAS BEEN RED: THE
### FUNCTOR NEVER GREW WITH THE RECORD

Landing the conjunct moved the file's error from line 694 to line 712 —
i.e. **past the statement**, which is the first evidence the carve itself
elaborates.  What is at 712 is older and was misdiagnosed:

    Could not find an instance for the following existential variables:
    ?riscvF_kptbGS : inG Σ kptbR
    ?riscvF_tsomemGS : tsoMemG Σ

A6.58 read this as a POSITIONAL problem and left a comment saying so ("the
positional underscore runs are 11 before `Hmpre` and 3 after `γreg`").
**The counts are right.**  Counted against `riscvFixedGS`'s field list
(`RiscvPtsto.v:396`) the eleven underscores land exactly on
`regGS … mirrorGS`, and the three after `γreg` on
`resvGS`/`tsomemGS`/`diskGS`.  The problem is not where the `_`s are — it
is that **there is nothing for two of them to resolve to**:

- `riscvGpreS` (`RiscvAdequacy.v:87`) had `riscv_pre_kptGS :: inG Σ kptR`
  and **no `kptbR` field and no `tsoMemG` field**;
- `riscvΣ` (`:141`) had `GFunctor kptR` and **no `GFunctor kptbR` and no
  TSO functors**;
- and **`tsoMemΣ` did not exist at all** — `TsoGhost.v` defined the class
  `tsoMemG` (four fields) and never gave it a functor or a `subG` instance.

So the record grew for the flip (A6.53's pin bound, the TSO ghosts) and the
PRE-class and functor that are supposed to supply it never did.  **A record
field is capacity you must also allocate**; a positional `_` cannot invent
an instance.  Landed:

```coq
(* TsoGhost.v, beside the class *)
Definition tsoMemΣ : gFunctors :=
  #[ ghost_mapΣ Arch.pa TsoMemPa.ts_elem;
     ghost_mapΣ nat TsoMemPa.pwmsg;
     GFunctor (authR viewUR);
     ghost_mapΣ (nat * Arch.pa) unit ].
Global Instance subG_tsoMemG {Σ} : subG tsoMemΣ Σ -> tsoMemG Σ.
Proof. solve_inG. Qed.

(* RiscvAdequacy.v *)
  riscv_pre_kptbGS :: inG Σ kptbR;
  riscv_pre_tsomemGS :: tsoMemG Σ;
     GFunctor kptbR;
     tsoMemΣ;
```

`tsoMemΣ` deliberately carries **no `mono_natΣ`**, matching the class's own
standing note: a second `mono_natG` beside `riscvF_genGS` would make
resolution ambiguous, and `riscvΣ` already carries the one the tree shares.

### THE BOOT 26 ARE THE SAME PROBLEM AS THE `↦ₛ` FOUR, NOT A SEPARATE ONE

Read while sizing item (2), and it changes that item's shape.  All 26
surviving boot crossings (`BootCarveMain` ×25, `BootBridge` ×1) are the
raw→ctx direction on **loader image bytes**: `ctx_word_of_mem`,
`ctx_pointsto_of_mem`, `ctx_eslot_of_mem`, `ctx_buf_of_mem`, sitting on
top of `phys_ident_mem` / `phys_ident_text`.  That is *precisely* the shape
`ctx_pointsto_of_ro` now covers — the only difference is the dfrac: the
boot carve OWNS its bytes, so it needs `ledger_elem0 a (DfracOwn 1)`, not
the discarded one.

**And that supply is what the carve just created.**  `boot_led_ran g
text_end ram_hi` hands the client exactly those elements, at exactly that
dfrac, over exactly the data half the boot carve works on.

> So A6.58's table had the dependency backwards.  The boot carve is not a
> separate owner "the tool must not touch" *and nothing else* — it is
> **the largest consumer of the element carve**, and it could not have been
> done before it at any price.  The blacklist ruling still stands and is
> now better motivated: the boot files must name every ξ explicitly
> because they are where the elements are still being distributed, and an
> ambient ξ there would silently pick a context for bytes that have not
> been assigned one yet.

**WHAT ITEM (2) NOW IS, precisely.**  Not a sweep: ~14 lemmas across
`BootCarveMain` (one section, `:477`, `Context {!riscvGS Σ, !xv6G Σ}` and
**no** `CurCtx` — as the blacklist requires) and `BootBridge`.  Each gains
an explicit `(ξ : TsoCtx.CtxId)` parameter and an element premise for the
bytes it mints, and each crossing becomes a `ctx_pointsto_of_ro` at
`DfracOwn 1`.  The one kit item still missing is the *word*-level and
*buffer*-level twins (`ctx_word_pointsto_of_ro`, `ctx_buf_of_ro`), since 14
of the 26 sites are `ctx_word_of_mem` and 2 are `ctx_buf_of_mem`; both are
`big_sepL` folds of the byte lemma over 8 (resp. `len`) elements, i.e.
`boot_led_word`'s shape, which already exists at `BootCarve.v:1226`.

### ITEM (3) IS NOT A ONE-LINE ARGUMENT FIX — `UmodeFetch` IS SEVEN CALL
### SITES ACROSS TWO FILES, EACH OWING A □ OBLIGATION

A6.60 read this one as "the file still passes a leaf-map hypothesis where a
`bytemap → iProp` is expected", and the error text does say exactly that
(`UmodeFetch.v:561`: `Hl` has type `ud_um pt !! svpn_of pc = Some w_leaf`
while a `TsoMemPa.bytemap → iProp` is expected).  But the cause is not a
misplaced hypothesis — it is a **new explicit parameter** on
`UserPtTree.utlb_inv_pt_translateAddr_u` (`:1376`):

```coq
      (w va pa : mword 64) (σ : mstate)
      (S : TsoMemPa.bytemap -> iProp Σ) :
```

`S` is A6.24's payer, threaded through the U-mode wrapper: a predicate over
MACHINE memory that must survive the walk's A/D write-back.  It is taken as
`S σ.(mem)`, returned as `S σ'.(mem)`, and the caller owes a **□
obligation** that an 8-byte page-table write preserves it:

```coq
    □ (∀ (m : TsoMemPa.bytemap) (a : Arch.pa) (wold wnew : mword 64),
         gen_heap_interp m -∗ S m -∗
         TsoCtx.ctx_phys_word_pointsto TsoCtx.cur_ctx a (DfracOwn 1) wold ==∗
         gen_heap_interp (write_bytes m a 8 wnew) ∗
         S (write_bytes m a 8 wnew) ∗
         TsoCtx.ctx_phys_word_pointsto TsoCtx.cur_ctx a (DfracOwn 1) wnew) -∗
```

**So every caller must CHOOSE an `S` and PROVE that obligation**, and there
are seven: `UserFetchPt` `:194` `:334` `:397` `:565` and `UmodeFetch`
`:559` `:682` `:792`.  **`UserFetchPt` has no `.vo` either** — it is red
for the same reason and was simply never named, because `UmodeFetch` fails
first.  Item (3) is therefore two files, not one, and its real content is
choosing the store predicate at each site (for `UmodeFetch` the resource
that has to cross the walk is the user memory `umem pt M`) and discharging
the preservation obligation — the same A6.24/A6.27 payer question the
kernel-side wrappers already answered, one tier over.

Comparable in size to the `tramp_tr_obl` six.  Not landed.

### ITEM (6), CHARACTERISED: THE `VcGenS` CASCADE IS SIX STATEMENTS AND AN
### INDUCTION, AND IT REACHES THE SCHEDULER

The successor tranche's handoff, measured rather than estimated.

**THE FILE:** `VcGenS.v`, 1539 lines, **zero `own_context`**, and it
exports **six** block lemmas, not one — three regime-generic and three
`root_ppn` wrappers:

| lemma | line |
|---|---|
| `wp_vc_block_s_den_r` | 378 |
| `wp_vc_block_s_den` | 805 |
| `wp_vc_block_s_aux_r` | 875 |
| `wp_vc_block_s_aux` | 1281 |
| `wp_vc_block_s_r` | 1330 |
| `wp_vc_block_s` | 1373 |

**WHY IT IS NOT A STATEMENT SWEEP.**  Each `_r` form is proved by
`revert st. induction prog as [|op rest IH]`, and the token has to be
threaded *through the induction*: taken in the statement, handed to `IH` at
every step, and returned in the continuation beside `vheap_own` /
`vheap4_own`.  The four sp-relative call sites that force it are
`wp_csdsp_gpr_s_r_t` / `wp_cldsp_gpr_s_r_t` at `:510`, `:544`, `:1006`,
`:1041` — `WpSmodePtMemWrap`'s wrappers, which are already threaded and
green.

**THE REACH:** `IntrDefs`, `ProofKernelvec` (`:520`, `:651`, via
`wp_vc_block_s`), `ProofSwtch` (`:194`, via `wp_vc_block_s_den_r`),
`SRegime`, `WpSwtchVc`.  **`ProofSwtch` is already an M2 quarantine site**
(A6.60's lock/park four), so this cascade and the lock tranche land in the
same file and should be sequenced deliberately rather than raced.

**THE SHAPE TO COPY** is `WpSmodePtMem`'s (A6.61): token in and out of each
statement, into the folded post, into the leaf's spec list, back out
through the continuation — with the one addition that here it must also
survive `IH`.


### A6.64 `WpSconfMem` IS GREEN — AND THE CAUSE WAS NEITHER OF THE TWO
### THINGS A6.61 AND A6.62′ SAID IT WAS

**202 sentences, 4.74 seconds, `.vo` on disk.**  Against 35 minutes, 60
minutes and 57 minutes of non-termination in the three prior attempts.
The one sentence that would not elaborate now bills **0.042 s**.

**THE ROOT CAUSE, and it is a THIRD story.**  A6.61 said the leaf's payload
was a duplicated lambda and naming it would fix it (refuted by A6.62′).
A6.62′ said the name had to be RIGID and `clearbody` would fix it (refuted
by the 57-minute run).  Neither was the bug.  The bug is that **the payload
was spelled DIFFERENTLY at three positions of the same forty-argument
application**:

| position | what it said |
|---|---|
| the leaf's `R` | `Psic` (`= own_context ∗ Ψ bs`) |
| the obligation argument | `Mobl_ram_ex width (pa_of ppn ea) Psic` |
| **the node argument** | `swp_read_ram_node_w_ex width (pa_of ppn ea) **Ψ** …` |

The node was still handing the payload at `Ψ` — the PRE-flip payload —
while the leaf and the obligation wanted `own_context ∗ Ψ`.  So
higher-order unification was asked to discover the relationship between
`Ψ` and `own_context ∗ Ψ` while working through forty arguments, and it
diverged.  **Make the three agree and the application elaborates in 42
milliseconds.**

> **THE DURABLE RULE, corrected for the third and last time.**  At these
> leaf applications the payload must be spelled IDENTICALLY at the leaf's
> `R`, at the obligation argument and at the node argument.  Naming it
> (`set`) is what makes that consistency easy to write and easy to check by
> eye — but naming is not the fix and `clearbody` is not the fix.  **The
> flip's threading edits must move the NODE argument too, and A6.58's
> recipe never said so**, which is why every S-mode leaf that took the
> token has this hazard latent until its node is checked.

**AND THE SPLIT EXPERIMENT IS WHAT FOUND IT.**  Splitting `iApply` into
`iPoseProof … as "Hleaf"` + `iApply ("Hleaf" with …)` showed the cost was
entirely in the `iPoseProof` — i.e. in ELABORATING the application, with
the goal not yet consulted.  That is what ruled out goal unification and
sent the search into the argument list, where the mismatch was.  **The
split is worth keeping in the file**: it costs nothing and it is the only
thing that localises this class of failure.

### THE CROSS-LANE CpuId BACK-PORT WAS REAL, AND IT BIT EXACTLY AS PREDICTED

`tso-port.md` §0.20′ (M-leg) arrived while this was in flight and it was
right on every point.  `own_context` is CpuId-indexed; both engines re-park
with `rename CID into CID0; iIntros (CID Hs)`; the capability's token is at
the FRESH `CpuId` while typeclass resolution silently finds the section
instance.  Landed here:

- `{CIDw : CpuId}` binders on BOTH local helpers (`wordw_pointsto_write_c`
  AND `wordw_pointsto_load_c` — §0.20′ only had the write one, because
  main's SC read needs no token);
- **the parameter is used TWICE in each**, exactly as §0.20′ warned: once
  for `own_context (CID := CIDw)` and once for the message author /
  read agent `hart_agent (@cpu_id CIDw)` — 3 token sites and 6 author
  sites across the two helpers;
- `(CID := CIDw)` pushed down to `SmodeCorePt.wordw_win_store_c` /
  `wordw_win_load_c` (legal there — they are outside this section);
- `(CIDw := CID)` at both node calls, and `own_context (CID := CID)` in
  both leaf payloads;
- and the read node's `iAssert` obligation re-spelled at
  `hart_agent (@cpu_id CID)` — which failed first as
  `iApply: cannot apply` on two terms that print identically, the §0.20′
  signature exactly.

**Two more genuine bugs behind it**, both invisible until the file
compiled this far:

- both nodes needed the token passed IN through the spec pattern
  (`[HAU]` → `[HAU Hctx]`); it was being used inside the bracket without
  being given to it;
- **`wordw1_byte` was stated across the tier**: `wordw_pointsto` is built
  from `ctx_pointsto cur_ctx` (line 118), so the one-byte window IS the
  context byte, but the lemma claimed `⊣⊢ mem_pointsto a dq w` — the RAW
  one.  False in the return direction at TSO; at the ctx tower both
  directions are identities.  Same class as `DinodeSlot`'s two (A6.62).

### THE CONE OPENED: 868 OF 1330, AND THE FRONTIER IS A REAL FRONTIER NOW

**868, up from 731.**  `WpSconfMem` going green added **137 files** in two
sweeps, and for the first time since the flip the `Proof*` tier has been
compiled at all.  Model `.vo` checked to postdate its source first (A6.39);
one make; closing rebuild stable at the same number.

**A6.61 AND A6.62's UNVALIDATED WORK IS NOW VALIDATED, AND IT HELD.**  The
21 owner-client deletions, the ten mechanical collapses, `DinodeSlot`,
`ProofDirlookupParts`, `ProofDirlink`, `ProofKexecTail`, the four
`ProofSys*` join4s — all green.  The owner re-tiering of `BcacheInv` and
`WaitInv` is confirmed end to end, clients included.

> **ONE SELF-INFLICTED BUG, worth recording because the tool did it.**  The
> dead-`Require TsoCtxShim` sweep matched `^Require TsoCtxShim\.[^\n]*\n`
> and several of those lines were the FIRST line of a multi-line comment —
> so it deleted the opener and left the tail, giving `Syntax error: illegal
> begin of vernac` in seven files.  A second guard (`if "ByteBuf" not in
> t`) was defeated by a comment *I had just written* mentioning ByteBuf.
> **When a script edits `Require` lines, check comment balance afterwards**
> — `s.count("(*") != s.count("*)")` found all seven in one pass and is now
> the cheapest possible post-condition for any header-editing sweep.

**THE 39 RED, CLASSIFIED** — and the newly-reached ones are dominated by a
single owner, not scattered:

| class | files | what it is |
|---|---|---|
| **the PT-cell tier (`↦ₚₜ` vs `↦ₚ₈`)** | `ProofMappages` `ProofUvmcopy` `ProofUvmunmap` `ProofWalkaddr` `ProofIsmapped` `TfPage36` (+`ProcInv`) | the SAME forced ledger-page move A6.49 measured, now reaching the page-table proofs.  **One owner, one tranche** — settle `ProcInv`/`TfPage36` first and the rest follow |
| unresolved implicits | `ProofBmap` `ProofEndOp` `ProofFreewalk` `ProofInstallTrans` | missing section binders, the `FsLookup` class (A6.58) |
| `ctx_phys` window | `ProofWalk` `UserMemPt` | the window accessor `UserMemPt` needs (A6.62) |
| `ctx_dom` / swtch re-index | `ProofScheduler` | **exactly A6.58's prediction**: `SwtchCtx.ctx_cells_reindex` became a PRICED re-index and "its single caller (`ProofScheduler`) is the M2 worklist entry that price creates" |
| the characterized five | `UmodeFetch` `UptWalkPt` `UserMemPt` `VcGenS` `RiscvAdequacy` | A6.62/A6.63's queue, unchanged |
| the `↦ₛ`/rodata residue | `ProofPrintk` `WpSconfLock` `ProofFilewriteParts` | blocked on the element carve (A6.62) |

**`RiscvAdequacy` moved 694 → 1372** under the carve — past the statement,
past the era record, past the device corollary, into the power path — and
its remaining tail is A6.61's cascade items 4–6.  The carve itself
elaborates; what is left below it is the power arm's own cascade.

### WHAT THIS OPENS

`WpSconfMem` gates roughly six hundred files, including **every `Proof*`
edit A6.61 and A6.62 landed and could not check** — the 21 owner-client
deletions, the ten mechanical collapses, `DinodeSlot`,
`ProofDirlookupParts`, `VirtioDiskRwDefs`, `ProofKexecTail`,
`WpSconfLock`.  The sweep behind this file is the first real news about all
of them, and it is running now.


### A6.65 THE NODE-ARGUMENT AUDIT IS CLEAN (ONE INSTANCE, PAID), THE
### PT-CELL TIER IS ONE MISSING PURE LAW, AND THE M2 MINT IS GONE

**ITEM (1), THE AUDIT A6.64's OWN RULE DEMANDED — and the answer is the
good one.**  Grepped the whole tree for the two argument positions that can
carry a stale payload into a leaf application:

| position | sites outside the model files |
|---|---|
| a NODE term passed as an argument (`swp_{read,write}_ram_node*`) | **1** — `WpSconfMem.v:629`, the one A6.64 fixed |
| an OBLIGATION term passed as an argument (`Mobl_ram_ex` / `Wobl_ram_ex`) | **1** — `WpSconfMem.v:599`, same application |

**There is no second instance.**  And the reason is structural, not luck:
every other token-threaded S-mode leaf (`WpSmodePtLeaves`,
`WpSmodePtMem`, `WpSmodePtMemWrap`, `SmodeCorePt`) discharges its memory
obligation through a proof ARM — the `iIntros (sigma img log tv V)` bullet
— rather than by passing a node TERM.  An arm cannot carry a stale payload,
because the payload is whatever the goal says it is.  All four are green,
which is the confirmation.

> **SO THE RULE'S SCOPE IS NARROWER THAN IT LOOKED, AND THAT IS WORTH
> KNOWING:** the hazard belongs to the `_ex`-style leaves that take their
> node and obligation as TERMS.  `WpSconfMem` is the only file in the tree
> shaped that way today.  **But the rule still binds forward**: the leaves
> not yet threaded (`VcGenS`'s six block lemmas, the `tramp_tr_obl` six)
> will acquire the same hazard the moment they are threaded, and this
> audit is the thing to re-run after each of those tranches — it is one
> grep.

### ITEM (3), THE PT-CELL TIER: SIX FILES, ONE MISSING PURE LAW

A6.49's ledger-page move made `PtTree.pt_slot_own` the page-table tower
(`↦ₚₜ` = `pt_slot_own (UTier cur_ctx)`), and the walk-lane proofs were
still applying `RiscvPtsto.phys_word_pointsto_ram` — a RAW law — to a
tiered cell.  That is the whole of the class:

    iSpecialize: cannot instantiate (?a ↦ₚ₈{?dq} ?w -∗ ⌜addr_is_ram ?a⌝)
    with (pt_addr0 p1 (vpn_at vpn0 k) ↦ₚₜ w0)

**And `PtTree` already had the hard half.**  `pt_slot_own_forget` (`:1160`)
takes BOTH tiers down to the raw physical word — its own header says "all
the PURE memory facts below ever wanted of a slot".  What was missing was
the two-line composition, now landed beside it:

```coq
  Lemma pt_slot_own_ram  a dq w : pt_slot_own a dq w ⊢ ⌜addr_is_ram a⌝.
  Lemma pt_slot_own_ram7 a dq w : pt_slot_own a dq w ⊢ ⌜addr_is_ram (pa_add a 7)⌝.
```

**The conclusion is PURE, which is what makes this free at the call sites**:
a pure conclusion is persistent, so the slot is not consumed and the walk
lane keeps using it inline exactly as before.  Five call sites moved,
character for character (`ProofIsmapped:408`, `ProofMappages:763`,
`ProofUvmcopy:1102`, `ProofWalkaddr:637`, `ProofUvmunmap:836`).

`ProcInv` and `TfPage36` are the same owner one tier up — their `tf_words`
family still spells the raw `↦ₚ₈` in its STATEMENTS, and settling that is
what A6.62's frontier table meant by "settle `ProcInv`/`TfPage36` first".

### ITEM (4): `ProofScheduler` CANNOT BE PAID — THE M2 MINT NO LONGER EXISTS

A6.58 predicted this file exactly ("its single caller `ProofScheduler` is
the M2 worklist entry that price creates"), and the price is real:
`SwtchCtx.ctx_cells_reindex` (`:337`) now demands `ctx_dom ξ ξ'` and is a
`==∗`, while `ProofScheduler:510` still calls it with the cells alone,
inside a plain `iAssert`.

The obvious repair is the one `ProofAcquire:665` uses —
`iPoseProof (ctx_dom_sc ξ0 cur_ctx) as "Hdom"` — **and it is not available:
`ctx_dom_sc` does not exist any more.**  `TsoCtxShim.v` is down to a single
declaration (`own_context_alloc`, itself callerless); the SC-only transport
stopgaps were removed with the rest of the shim's body.

> So the M2 transport class — `ProofAcquire` ×2, `ProofRelease`,
> `ProofSwtch` and now `ProofScheduler` — **is blocked on the lock kit's
> REAL mint, not on a local edit.**  Per §0.18′ that mint is
> `ZZAbsorbProbe.twin_absorb` against `twin_passed_get`'s view receipt, and
> per A6.39 it is its own tranche against a green tree.  **Do not
> re-declare `ctx_dom_sc`**: it is false at the real machine, an axiom
> would be worse than the red, and the red is now honestly localised to
> five sites in one class.  Characterised, not paid.

### CLOSING NUMBER: 875 OF 1330, RED 34

The PT-tier law landed clean: **all five walk-lane files went green in one
rebuild** (`ProofIsmapped`, `ProofMappages`, `ProofUvmcopy`,
`ProofUvmunmap`, `ProofWalkaddr`), nothing regressed, red 39 → 34, and the
count moved 868 → **875**.  Model `.vo` checked to postdate its source
first (A6.39); one make throughout.

Two lemmas of two lines each bought five files, which is what a MISSING
PURE LAW looks like from the outside — the walk lane was never wrong about
its slots, it just had no way to say `addr_is_ram` at the tier the slots
now live in.

### THE QUEUE AS IT NOW STANDS

1. **`ProcInv` / `TfPage36`** — the PT-cell tier's statement half; the
   five walk-lane sites are already paid and will follow.
2. **The boot 26** — hand-written explicit-ξ, and A6.63 established the
   dependency runs the right way now: the carve supplies their elements at
   `DfracOwn 1` through `boot_led_ran`.  Still needs the word/buffer twins
   of `ctx_pointsto_of_ro` (both are `big_sepL` folds of the byte lemma,
   `boot_led_word`'s shape).
3. **`RiscvAdequacy`'s power tail** — A6.61's cascade items 4–6, now the
   only thing between the carve and a green adequacy file.
4. **`UmodeFetch`** (7 sites, 2 files, each owing a □ obligation — A6.62),
   the **`tramp_tr_obl` six**, **`UserMemPt`**'s window accessor.
5. **The M2 transport class** (5 sites) — the lock tranche.
6. **`VcGenS`** — six block statements and an induction, reaching the
   scheduler/trap tier (A6.61).  Re-run the node-argument grep after it.


### A6.66 THE LOCK KIT'S PARKED-RECORD IDIOM IS PORTED — AND HERE THE
### TRANSPORT PATH IS HONEST END TO END, WHICH IT IS NOT AT SC

`tso-port.md` §0.18′'s shape is in the fliptree, and the port produced a
better result than the source, for the reason A6.39 predicted: **this tree
has the real gates, so the receipts are real.**

**THE ONE MISSING GATE, NOW WRITTEN: `TsoCtx.ctx_absorb`.**  Release's
`ctx_deposit` was already here and is INTERP-FREE (a parked target's stamp
may be raised at will).  Its dual was not, and the difference is the whole
point:

```coq
  Lemma ctx_absorb `{CID : CpuId} (R : CtxId -> iProp Σ) `{!CtxMorph R}
      (g : gstate) (ξ ξ' : CtxId) (T : nat) :
    (length g.(glog) <= g.(gtv) cpu_id)%nat ->
    tso_interp_at riscv_eraGS g -∗
    own_context ξ' -∗ ctx_parked ξ T -∗ R ξ ==∗
    tso_interp_at riscv_eraGS g ∗ own_context ξ' ∗ ctx_parked ξ T ∗ R ξ'.
```

Two lines of proof over `ctx_dom_of_parked` + `ctx_morph`, and the premise
is the load-bearing part: **`length glog ≤ gtv cpu_id` is the AT-THE-TOP
condition, and it is exactly what the AMO leaf establishes when it reads at
the top** (A6.6's receipt ruling).

> **PARTLY REFUTED BY A6.68, and the refutation is in this block's own
> terms.**  The interp premise is right FOR THE ACQUIRE LEAF and wrong as a
> general claim: it makes `ctx_absorb` unusable at every M2 transport site,
> because those are ghost steps OUTSIDE every WP leaf and `tso_interp_at` is
> only in hand inside one.  `TsoCtxAbsorbLb.ctx_absorb_lb` is the same law
> against a persistent `hart_view_lb` receipt, is equally honest (it is
> `ctx_resume`'s evidence), and is what pays `ProofScheduler`.  Both forms
> stay; they are for different SITES, not different strengths.
>
> **COMPARE THE SAME LEMMA ON MAIN** (`WpLock`'s reference at HEAD): its
> proof is `rewrite ctx_dom_unseal /ctx_dom_def. done.` and its statement
> takes a `hart_view_lb K` that the caller CONJURES with
> `hart_view_lb_any`.  At SC `ctx_dom` is vacuous, so the transport is free
> and the receipt is fictional.  **Here the interp supplies the receipt and
> `hart_view_lb_any` has no role left at the acquire at all** — the premise
> is a strengthening of the statement and a weakening of what the caller
> must invent.  This is the flip making the lock kit *better*, and it is
> the first place in the port where that has been true.

**THE FREE ARM IS THE PARKED RECORD.**  `lock_inv`'s free branch moved from
the old `(∃ ξ : CtxId, R ξ)` to

```coq
  Definition lock_pay (R : CtxId -> iProp Σ) : iProp Σ :=
    (∃ (ξ : CtxId) (T : nat), ctx_parked ξ T ∗ R ξ)%I.
```

per-publication, exactly as §0.18′ ruled: a record is minted at each
release and abandoned by the winner that claims it, so no stamp ratchets
across generations and **no token travels with the holder**.

### AND THE CREATOR MINT IS DISCHARGEABLE HONESTLY HERE — CHECKED, NOT ASSUMED

§0.18′'s one blemish is `lock_pay_intro`: on main the creator has no
`own_context` to deposit with, so the transport is the shim's `ctx_dom_sc`,
**quarantined at one site**, and "when the shim burns this lemma is the
single compile error that names the whole cascade".

The coordinator's instruction was to check before quarantining, and the
check says **do not quarantine** — for the decisive reason that
`ctx_dom_sc` no longer exists in this tree at all (A6.65: `TsoCtxShim.v` is
down to one callerless declaration).  What replaced it is the honest proof:

```coq
  Lemma lock_pay_intro `{CID : CpuId} (R : CtxId -> iProp Σ) `{!CtxMorph R} :
    own_context cur_ctx -∗ R cur_ctx ==∗ own_context cur_ctx ∗ lock_pay R.
  Proof.
    iIntros "Hrun HR".
    iMod ctx_parked_alloc as (ξc) "Hpk".
    iMod (ctx_deposit R cur_ctx ξc 0 with "Hrun Hpk HR")
      as "(Hrun & %T' & _ & Hpk & HR)".
    iModIntro. iFrame "Hrun". iExists ξc, T'. iFrame "Hpk HR".
  Qed.
```

**So the lock's transport path has NO quarantine at any point in this
tree** — creator mint, release deposit and acquire absorb are all real
laws.  The price is the one §0.18′ priced and deferred: `ctx_deposit`
wants the creator's running token, so the creator family takes
`own_context` and hands it straight back.  **That trade is the finding**:
main bought the quarantine because it was cheaper than the cascade; here
the cascade is the only option, and it buys a genuinely axiom-free kit.

**LANDED IN `WpLock`, and the file is GREEN:** `lock_pay`,
`lock_pay_intro`, `lock_inv`'s new free arm, the two `lock_finisher` slots
at `lock_pay R`, and the creator family threaded — `lock_inv_alloc`,
`newlock`, `newlock_d`, `newlock_delayed`.  The two DELAYED forms take
`CtxMorph` as a `⌜⌝` premise on the inner ∀ (main's shape) plus the token
beside it.  **All four creators also gained a `{CID : CpuId}` binder** —
A6.64's lesson reaching the lock tier: `own_context` is CpuId-indexed, this
section binds no hart, and the token a caller hands over is at ITS hart.

### THE CASCADE, NAMED AT ITS BOUNDARY

What the honest mint costs is now a compile-time fact rather than an
estimate: every `newlock`-family caller must produce `own_context cur_ctx`
and a `CtxMorph R`.  §0.18′ counted **19 direct sites** — 12 in this family
and 7 more behind `WpLockAt.newlock_at`, each under a creator wrapper of
its own (`new_sleeplock*`, `new_tickslock`, `delayed_locks_alloc`,
`pipe_alloc`, `bcache_alloc`, …).  `BioInv.bio_init` already borrows the
running token, so the pattern exists in the tree.

**AND THE BOUNDARY IS MEASURED, NOT ESTIMATED: FOUR FILES.**  The rebuild
behind the ported `WpLock` turns exactly four files red, and they are the
creator WRAPPERS, not the 19 call sites: **`WpLockAt`, `SleepLock`,
`TicksInv`, `PipeInv`**.  Every one of §0.18′'s 19 direct sites reaches the
kit through one of these four, so the token and the `CtxMorph` premise are
threaded four times, not nineteen.  That is a far better shape than the
count suggested, and it is the argument for having taken the honest route:
the wrappers are a choke point the quarantine would have hidden.

**The five M2 sites A6.65 localised are what this unblocks**: with
`ctx_absorb` in the kit, `ProofAcquire` ×2 and `ProofRelease` stop needing
`ctx_dom_sc`, and per §0.18′ `ProofSwtch`'s `ctx_cells_reindex` price
becomes an absorb from the record, with `ProofScheduler` following the same
shape.  Those four files are the next tranche and they are now *possible*,
which they were not when A6.65 was written.


### A6.67 THE FOUR CHOKE POINTS ARE GREEN, AND THE HONEST MINT'S COST IS
### NOW A MEASURED RING, NOT AN ESTIMATE

**ALL FOUR CASCADE-BOUNDARY FILES LANDED:** `WpLockAt`, `TicksInv`,
`SleepLock`, `PipeInv`.  Each takes `own_context cur_ctx` and hands it
straight back; the two DELAYED creator forms also take `⌜CtxMorph R⌝` on
their inner ∀, which is main's shape.  Eleven creator entry points threaded
in four files — the choke point A6.66 predicted held exactly.

**AND `SleepLock` SHOWED WHAT A CHOKE POINT ACTUALLY LOOKS LIKE INSIDE**: it
is not one wrapper but a CHAIN of seven, each calling the next
(`new_sleeplock_gen_at` → `new_sleeplock_gen` → `new_sleeplock` →
`sl_fresh_new_gen` / `sl_fresh_new` / `sl_fresh_new_gen_at` →
`sl_fresh_new_tok`).  The token threads down the whole chain and every link
is the same three-line edit.  Worth knowing before starting the next such
file: **the count of `newlock` USES understates the work; the count of
WRAPPERS is the real one.**

**THREE MECHANICAL TRAPS, all of which cost a compile each and all of which
are avoidable:**

1. **`CpuId` is not in scope unqualified in most files.**  ``​`{CID : CpuId}``
   in `WpLockAt`, `TicksInv`, `SleepLock`, `PipeInv` silently declares a
   fresh `Type` variable named `CpuId` and the error moves one line instead
   of away — the same trap `TfPage36` sprang in A6.63.  **Spell it
   `RiscvLang.CpuId`** anywhere outside `RiscvLang`'s own importers.
2. **`iMod (…) as "…"; iDestruct …` chains onto the SIDE GOAL** the `with`
   pattern's brackets create, so the destruct runs on the wrong goal.  Put
   the destruct after the `{ … }` block as its own sentence.
3. **A premise added at the END of a statement must be introduced at the
   END of the `iIntros` pattern.**  Adding `own_context` last and
   introducing it second cost one compile in `PipeInv`.

### WHAT THE SWEEP SAYS: THE RING ADVANCES BY EIGHT

Behind the four choke points the next ring is now reached, and it is the
newlock family's own callers: **`BioInv`, `IcacheBoot`, `SleepLockAt`,
`ProofKinit`** (plus `ProofAcquiresleep`, `ProofBeginOp`, `ProofSysSync`,
`ProofFilewriteParts`, which the same cone opened).  `BioInv.bio_init`
already borrows the running token, so the pattern is in the tree; the
others take it the same way.

The count held at **875 of 1330** across the tranche — nothing regressed,
and the movement is reachability, not loss: files behind a newly-red
wrapper are unreached rather than failed.  **Read 875 as the floor it has
been all along**; the lock cascade has to bottom out before it moves again.

### THE SHIM IS NOT RETIRABLE YET, AND THE COUNT SAYS EXACTLY WHY

The retirement condition (zero code references) is **not met**: 30 remain,
in five files, and they are precisely the two blocks A6.62/A6.63 already
named —

| block | sites | blocked on |
|---|---|---|
| the boot carve | 26 (`BootCarveMain` 25, `BootBridge` 1) | the hand-written explicit-ξ tranche; the CARVE now supplies its elements (A6.63), so this is unblocked work, not a dependency |
| the `↦ₛ`/rodata four | 4 (`ProofPrintk` ×2, `ProofSyscall`, `WpSconfLock`) | `ctx_pointsto_of_ro`'s consumers — the kit lemma exists (A6.63), the sites are not yet moved |

> **A6.68 REFILES `WpSconfLock` OUT OF THIS TABLE.**  Its shim use is real
> but it is not the blocker: the file's FIRST error is `lk_cpu_cell_acc`,
> which `WpLock.v` deleted on purpose as the M4 racy-owner-cell entry.  The
> rodata group is three sites, not four.

**Nothing on the LOCK's path is in that list any more**, which is the
tranche's real result: A6.66's claim that the transport is honest end to
end survived contact with all four choke points.  When those 30 go, the
tombstone can be written; writing it now would be a lie about 30 live
references.

### THE QUEUE

1. **The eight-file ring** (`BioInv`, `IcacheBoot`, `SleepLockAt`,
   `ProofKinit`, …) — the same three-line edit per wrapper, with the three
   traps above pre-paid.
2. **The five M2 sites** — `ProofAcquire` ×2, `ProofRelease` onto
   `ctx_absorb`; `ProofSwtch`'s `ctx_cells_reindex` price paid as an absorb
   from the record, `ProofScheduler` following.  **These are now possible**
   (A6.65 recorded them as impossible; `ctx_absorb` is what changed).
   Delete `ctx_cells_reindex` if it goes dead.
   > **A6.68, MEASURED: half true.**  `ProofScheduler` is paid and green —
   > but with `ctx_absorb_lb` (receipt), not `ctx_absorb` (interp), which
   > has no site outside a WP leaf.  The other four are UNREACHED, not
   > payable: `ProofAcquire`/`ProofRelease` sit behind `WpSconfLock`, whose
   > blocker is the M4 racy owner cell, and `ProofSwtch` behind `VcGenS`.
   > **`ctx_cells_reindex` is NOT dead** — it is the price, and
   > `ProofScheduler` is the site that pays it.
3. The boot 26 (needs the word/buffer twins of `ctx_pointsto_of_ro`), then
   the four rodata sites — and then the shim's tombstone.
4. `RiscvAdequacy`'s power tail, `UmodeFetch` (7 sites, 2 files), the
   `tramp_tr_obl` six, `UserMemPt`'s window accessor.
5. `VcGenS` — characterize-only; re-run A6.65's node-argument grep after it.


### A6.68 THE M2 TRANSPORT IS PAID — AND THE GATE IT NEEDED WAS AN
### INTERP-FREE RECEIPT ABSORB, WHICH A6.66 SAID DID NOT EXIST

**CLOSING NUMBER: 901 of 1334, RED 14** (up from 875 of 1330, red 34; the
denominator moved because this tranche adds four files).
> **CORRECTED BY A6.69's CLEAN ROUND: it is 900 of 1333.**  The RED SET was
> exactly right; the count was inflated by one stale `SystemAssumptions.vo`
> inherited with the tree copy, and `SystemAssumptions.v` is deliberately
> out of `_CoqProject`, so the denominator is 1333.  Two identical
INCREMENTAL `-k` sweeps at the same number; model `.vo` checked to postdate
its source first (A6.39); no `Admitted`, no `Abort`, no `Axiom`.
**HONEST QUALIFIER: this is not a clean number.**  A `rm -f iris/*.vo`
round was not run — the incremental base is A6.67's, which was itself
clean, and every file this tranche edited recompiled from source in the
sweeps; but A6.38's rule says only a clean rebuild counts after a machine
change, and no machine change happened here.  Pay the clean round at the
head of the next tranche and correct 901 if it moves.

#### THE HEADLINE, AND IT IS A REFUTATION OF A6.66 IN ITS OWN TERMS

A6.66 landed `TsoCtx.ctx_absorb` against the interp and called the premise
"why the flip makes the lock kit *better*".  A6.67 then queued the five M2
sites as "now possible".  **They were not, and the reason is A6.66's own
premise.**  §0.17′'s measured rule cuts both ways:

> `own_context` is only in hand OUTSIDE a WP leaf.  `tso_interp_at` is only
> in hand INSIDE one.  **A transport that wants both in one hand has no
> site.**

Every M2 transport is a ghost step in the middle of a whole-function proof
— `ProofScheduler:510` is an `iAssert` at the top of `wp_scheduler_sconf`,
before the first instruction — so `ctx_absorb`'s interp is unreachable
there, permanently.

**AND THE INTERP WAS NEVER NECESSARY.**  `TsoCtx.ctx_resume` already claims
a parked context's facts on a RECEIPT alone — `(T ≤ K) → hart_view_lb K -∗
ctx_parked ξ T ==∗ own_context ξ` — with no interp, because a stamp is a
legal log position and a hart whose view has passed it has seen every write
the record published.  The same evidence justifies the `ctx_dom` mint.
**Landed, proved, no admits: `iris/TsoCtxAbsorbLb.v`.**

```coq
  Lemma ctx_dom_of_parked_lb `{CID : CpuId} (ξ ξ' : CtxId) (T K : nat) :
    (T <= K)%nat ->
    hart_view_lb K -∗ own_context ξ' -∗ ctx_parked ξ T ==∗
    own_context ξ' ∗ ctx_dom ξ ξ' ∗ (ctx_dom ξ ξ' -∗ ctx_parked ξ T).

  Lemma ctx_absorb_lb `{CID : CpuId} (R : CtxId -> iProp Σ) `{!CtxMorph R}
      (ξ ξ' : CtxId) (T K : nat) :
    (T <= K)%nat ->
    own_context ξ' -∗ hart_view_lb K -∗ ctx_parked ξ T -∗ R ξ ==∗
    own_context ξ' ∗ ctx_parked ξ T ∗ R ξ'.
```

It is `ctx_dom_of_parked`'s proof with the interp's two uses replaced: the
`llb_valid` "T is a legal log position" comes out of the record's own
`llb T`, and the bound-raise target is `max B' T` under the JOINED receipt
`max K' K` rather than `gtv cpu_id`.  **The join is a case split, not an
algebra step** — the max IS one of the two and `view_lb` is persistent
(`view_lb_max`, three lines).  **`ctx_absorb_lb` is `tso-port.md` §0.18′'s
statement character for character** — main's shape, which every M2 site was
written against; there it is fictional (SC's `ctx_dom` is vacuous), here it
is real.

> **THE CORRECTED RULING.**  `ctx_absorb` (interp) and `ctx_absorb_lb`
> (receipt) are BOTH honest and they are for different SITES, not different
> strengths: the interp form is for a claim made inside a lock leaf, where
> the AMO's at-the-top fact is what you have; the receipt form is for a
> ghost step outside every leaf, where a persistent `hart_view_lb` is what
> you have.  A6.66's "the interp supplies it and `hart_view_lb_any` has no
> role left" is right ABOUT THE ACQUIRE LEAF and wrong as a general claim.
> **Keep both.**

**WHY ITS OWN FILE:** it is a forty-line derivation off `TsoCtx.v`'s PUBLIC
unseal lemmas and needs nothing new from the kit, while `TsoCtx.v` is under
the whole tree.  Fold it into the gate block at cutover — the `SieCapCtx.v`
precedent, same reason, recorded in the file's header.

#### `ProofScheduler` IS GREEN, AND THE PRICE IS ONE DEFINITION

A6.58 predicted this file, A6.65 recorded it as unpayable.  It is paid, and
the shape is the lock kit's own idiom one tier up: **`SchedCtx.cpu_ctx_free`
is a PARKED RECORD now**, not a bare `∃ ξ`:

```coq
  (∃ (vs : list (mword 64)) (ξ : CtxId) (T : nat),
     ⌜ length vs = 14%nat ⌝ ∗
     TsoCtx.ctx_parked ξ T ∗ TsoCtx.hart_view_lb T ∗
     ctx_cells (XI := ξ) (a_cpu_ctx cid_word) vs)%I.
```

The receipt rides beside the token because the slot is HART-INDEXED
(`cid_word`): whoever last published into this cpu's save area was running
on this cpu, so "this hart's view has passed T" is a persistent fact it
could hand over.  **At boot the stamp is 0 and `TsoGhost.view_lb_0` gives
the receipt for nothing.**  `ProofScheduler`'s site is then five sentences:
borrow the token (`SieCapCtx.sie_cap_gpr_own_ctx_acc`), mint the domination
at `T ≤ T` (reflexivity), pay `SwtchCtx.ctx_cells_reindex`, hand the token
back, abandon the record.

> **`ctx_cells_reindex` IS NOT DEAD — A6.67's "delete it if it goes dead" is
> answered NO.** It is the price, and this is the site that pays it.

**THE COST, NAMED:** `cpu_ctx_free` has ten consumers; the only GREEN ones
were `SchedCtx` (the definition) and `SpecScheduler` (a premise slot).  The
eight PRODUCERS — `BootChain`, `BootShared`, `BootBridge`, `ProofMain`,
`ProofMainSecondary`, `SpecMain`, `SpecMainSecondary`, `CpuOwn` (comment
only) — are all behind the boot cascade and unreached, so they owe a
`ctx_parked_alloc` + `view_lb_0` pair each when that cascade opens.  That is
the honest bill and it is three lines apiece.

#### THE EIGHT-FILE RING WAS TEN, AND THE ARRAY INITIALIZERS ARE THE REAL WORK

A6.67's ring landed, plus what it opened: **`SleepLockAt`, `ProofKinit`,
`IcacheBoot`, `BioInv`, `BioInitAt`, `FsBoot`, `ProofAcquiresleep`,
`ProofBeginOp`, `ProofPipealloc`, `ProofInitlog`.**  Two idioms, and only
one of them is the three-line edit A6.67 promised:

1. **A proof holding the kernel bundle BORROWS its own token.**
   `SieCapCtx.sie_cap_gpr_own_ctx_acc` — **ported verbatim from main**,
   which already has this file; the fliptree did not.  Used at `ProofKinit`,
   `ProofInitlog`, `ProofPipealloc`, `ProofScheduler`.  Its own header
   argues why it is not in `IntrDefs.v`; that argument holds here too.
2. **A BOOT ARRAY INITIALIZER CANNOT DISTRIBUTE THE TOKEN, AND THIS IS THE
   ONE THING A6.67's ESTIMATE MISSED.**  `IcacheBoot` builds NINODE inode
   sleeplocks, `BioInv` / `BioInitAt` build NBUF buffer sleeplocks, and the
   existing idiom is `big_sepL_mono` into a list of INDEPENDENT fupds.
   `own_context` is EXCLUSIVE (`own_context_excl`), so the fifty steps must
   run in SEQUENCE.  Landed as `iris/SepThread.v`, one lemma, no tree
   dependencies at all:

```coq
  Lemma big_sepL_fupd_thread {A} (E : coPset) (Res : PROP)
      (Phi Psi : nat -> A -> PROP) (l : list A) :
    Res -∗
    ([∗ list] k↦x ∈ l, Res -∗ Phi k x ={E}=∗ Res ∗ Psi k x) -∗
    ([∗ list] k↦x ∈ l, Phi k x) ={E}=∗ Res ∗ [∗ list] k↦x ∈ l, Psi k x.
```

   Stated for an arbitrary `BiFUpd PROP` and an arbitrary linear `Res` on
   purpose: a generic statement cannot drift from the kit, and the same
   shape is what any exclusive boot authority would want.  **The rewrite at
   a call site is: state the per-element step as a `big_sepL_intro`'d wand,
   thread, then re-wrap for whatever collector follows** (`seq_fun_alloc`
   takes a list of fupds, so `BioInv` re-wraps with a one-line
   `big_sepL_mono`).

> **THE WRAPPER-CHAIN LESSON, EXTENDED.**  A6.67 said count WRAPPERS, not
> uses.  Add: **count LOOPS separately.**  A wrapper is three lines; a
> boot loop over an array is a threading lemma plus a restructured
> `iAssert`, and the two `bio_init` forms plus `icache_boot_at` were three
> of the ten files in this ring.

#### THE `↦ₚ` WINDOW: A6.62's "`ctx_phys` WINDOW" ITEM IS ONE MISSING TWIN

`ProofWalk`, `ProofKvmmake` and `ProofUvmcreate` all did the same thing to
a freshly-memset page: forget it out of the context (`ctx_buf_forget`), use
`KMap.mem_page_to_phys`, and hand the result to `zero_page_to_node` — which
now wants `ctx_phys_pointsto cur_ctx`.  **`KMap.v` sits BELOW `TsoCtx.v`, so
its `↦ₘ`/`↦ₚ` are the RAW families**, and the return trip is the direction
the flip makes false.  The content of the crossing at the tower is already
`TsoCtx.ctx_pointsto_phys` (a `⊣⊢`); what the raw lemma adds is IDENTITY.
Landed as `iris/CtxKMap.v`:

```coq
  Lemma ctx_mem_ident_phys (xi : CtxId) (pa : mword 64) dq b :
    kmap_static (svpn_of pa) KP_rw ->
    kmap_static_claims -∗ ctx_pointsto xi pa dq b -∗ ctx_phys_pointsto xi pa dq b.
  Lemma ctx_mem_page_to_phys (xi : CtxId) (p : mword 64) dq b : (* the 4096 fold *)
```

`mem_ident_phys`'s proof verbatim with the ledger residue carried through
instead of forgotten (`kmap_at_agree` against the static bundle, then
`KptPt.pa_of_id`).  Three files green off two lemmas.

> **AND THE OPPOSITE DIAGNOSIS WAS ALSO RIGHT ONCE, WHICH IS THE TRAP.**
> The SAME `ctx_buf_of_mem`/`ctx_buf_to_mem` pair around a **memset** call
> (`ProofBalloc`, `ProofIalloc`, `ProofSysUnlink` ×2) is a pure IDENTITY
> now — memset's contract is context-indexed and so is the buffer — and the
> right edit there is to DELETE both lines.  **The test is whose `↦ₘ` the
> next consumer means**: a consumer above `TsoCtx` (memset) wants the ctx
> family and the crossing is dead; a consumer below it (`KMap`, `PtTree`)
> wants the raw family and the crossing is real.  Deleting the pair at the
> `KMap` sites cost one compile before this was seen.

#### THE MECHANICAL RESIDUE: A MISSING `` `{XI : CurCtx} `` ON ONE DECLARATION

Sixteen files were red on nothing but this, all first-time-reached behind
the ring.  The convention in the `Proof*Defs` sections is a PER-DECLARATION
binder (not a section binder — several sections mix declarations that have
their own, and a section binder then collides with `XI is already used`), so
the fix is `Lemma foo `{XI : CurCtx} …` on the one declaration the error
names, repeated until the file is green.  **It is a fixpoint, not a single
pass**: `ProofInstallTrans` needed eight, `ProofEndOp` and `ProofBmap` six.
Automated with a build-parse-patch loop; the loop is worth rebuilding for
the next tranche, and its two real bugs are worth recording — take the
`File` line CLOSEST to the error (the notation warnings emit their own
`File` lines at the top of every file), and check the error BLOCK for
`CurCtx`, not just the `Error:` line, because the message is often
`Could not find an instance for the following existential variables:` with
`?XI : CurCtx` three lines down.

Files: `ProofBmap`, `ProofEndOp`, `ProofFilewriteParts`, `ProofInitlog`,
`ProofInstallTrans`, `ProofIput`, `ProofLogWrite`, `ProofProcdumpLoop`,
`ProofWriteHead`, `ProofSysSync`, `ProofBeginOp`, `ProofAcquiresleep`,
`ProofFreewalk` (partial).  Three one-off neighbours in the same class:
`ProofAcquiresleep.asl_word4_nonzero` needed `ctx_pointsto_forget` before
`mem_pointsto_acc`; `ProofBrelse` needed `ctx_word4_pointsto_agree` /
`ctx_word4_pointsto_frac_split` for the raw ones; `ProofIput` had three
`ctx_word4_pointsto_frac_split` calls missing the now-explicit `ξ`.

#### THE SHIM IS STILL NOT RETIRABLE, AND THE COUNT HAS NOT MOVED

Verified by grep before writing anything: **30 code references, in the same
five files** — `BootCarveMain` 25, `BootBridge` 1, `ProofPrintk` 2,
`ProofSyscall` 1, `WpSconfLock` 1.  Nothing this tranche touched was on the
shim's path.  Writing the tombstone now would be a lie about 30 live
references, exactly as A6.67 said.  (23 files still carry a bare
`Require TsoCtxShim` line with no use; those are free to drop, but the
A6.64 comment-balance rule applies to any script that does it.)

#### `WpSconfLock` IS BLOCKED ON THE M4 RACY CELL, NOT ON THE ↦ₛ RESIDUE —
#### AND THAT IS WHY `ProofAcquire`/`ProofRelease` ARE STILL UNREACHED

A6.67 filed `WpSconfLock` under "the `↦ₛ`/rodata four".  **Measured: its
first error is `lk_cpu_cell_acc`, which `WpLock.v` DELETED on purpose**
(its own comment: "THE ELIMINATION DIRECTION IS FALSE AT TSO … the failures
at the leaves that read and write this cell are that [M4] entry").  Two
sites:

- **`lock_claims` (`:139`) is payable and is not the blocker in principle.**
  It only wants `wordw_claim 8 (lock_cpu lk)` — an ADDRESS claim, which is
  context-free (`mem_claim` is `kmap_at` + canonicality + RAM + tier pin,
  and `mem_pointsto_claim` reaches it through `ctx_pointsto_forget`).  A
  claim lemma that reads off a `ctx_word_pointsto` at ANY `ξ` retires this
  site AND the `TsoCtxShim.ctx_word_of_mem` beside it.  Not landed.
- **`wp_ld_lkcpu_lockopen_gen` (`:432`) is the real M4 entry.**  The leaf
  hands the invariant's cell to a plain-load atomic update at `cur_ctx` and
  promises the value read IS the ledger's.  At TSO that is false without
  synchronisation, and `holding()`'s read of `lk->cpu` genuinely races.  No
  receipt exists at a plain load, so neither absorb form applies.

**So `ProofAcquire` ×2, `ProofRelease` and `ProofSwtch` are UNREACHED, not
red**: `ProofAcquire`/`ProofRelease` sit behind `WpSconfLock`, `ProofSwtch`
behind `VcGenS`.  A6.67's "five M2 sites, now possible" is therefore half
true — the fifth (`ProofScheduler`) is paid; the other four need their
gates opened first, and the gate is not the transport.

#### THE RED 14, CLASSIFIED

| class | files |
|---|---|
| the M4 racy owner cell | `WpSconfLock` |
| the `VcGenS` cascade (characterize-only, unchanged from A6.63) | `VcGenS` |
| the PT-cell tier's STATEMENT half (A6.65 queue 1) | `ProcInv`, `TfPage36` |
| `UmodeFetch` (7 sites / 2 files, the □ obligations) | `UmodeFetch`, `UptWalkPt` |
| the `ctx_phys` window at the USER tier | `UserMemPt` |
| the `↦ₛ`/rodata residue | `ProofPrintk` |
| `RiscvAdequacy`'s power tail | `RiscvAdequacy` |
| newly reached, one-offs | `ProofFreewalk` (`↦ₚₜ` framing), `ProofKvminithart` (`kvi_satp_mode` type), `ProofVirtioDiskIntr` (`wordw_pointsto 2` vs `word2_pointsto`), `ProofVirtioDiskRw` (`word4_pointsto` framing), `ProofVirtioDiskRwD` (`phys_ledger` vs `↦ₚ`) |

`VcGenS:510` is still exactly A6.63's diagnosis: `wp_csdsp_gpr_s_r_t` wants
`own_context ?XI` and the block lemma does not take one, so the token has to
be threaded through `revert st. induction prog` in all six statements.  The
node-argument grep (A6.65) must be re-run after that tranche.

#### THE QUEUE

1. **`ProcInv` / `TfPage36`** — the PT-cell tier's statement half; it gates
   `ProofSyscall`, `BootCarveMain` and the whole boot cone, so it is the
   largest single unblocker left.
2. **`WpSconfLock`** — write the context-free `wordw_claim` reader for
   `lock_claims`, then decide the M4 racy-read law.  `ProofAcquire`,
   `ProofRelease` are behind it.
3. **The boot 26** (needs the word/buffer twins of `ctx_pointsto_of_ro`),
   then the four rodata sites, then the shim's tombstone.
4. **`VcGenS`** — six statements and an induction; `ProofSwtch` is behind it.
5. `RiscvAdequacy`'s power tail, `UmodeFetch`, the `tramp_tr_obl` six,
   `UserMemPt`'s window accessor.
6. When the boot cascade opens: the eight `cpu_ctx_free` producers owe a
   `ctx_parked_alloc` + `view_lb_0` pair each.


### A6.69 THE PT-CELL STATEMENT HALF WAS THE CORK: 900 → 1080, AND THE
### RESIDUE IT UNCOVERED IS THREE MECHANICAL CLASSES AND FOUR REAL ONES

**THE CLEAN-ROUND BILL, PAID FIRST, AND IT CORRECTS A6.68 BY ONE.**
`rm -f iris/*.vo`, model `.vo` checked fresh, one full `-j12 -k`:
**900 of 1333**, red 14 — the SAME fourteen files A6.68's incremental round
named, so that round's red set was honest.  Its COUNT was not: **the
denominator is 1333, not 1334** (`SystemAssumptions.v` is deliberately out
of `_CoqProject` — its own header says why), and the 901st `.vo` was a
stale `SystemAssumptions.vo` inherited with the tree copy.  **Quote 900,
not 901.**

**CLOSING NUMBER AFTER THE TRANCHE: 1080 of 1333, RED 16.**  Two identical
`-k` sweeps at the same number.  No `Admitted`, no `Axiom` (the two
`Abort.`s in `FastSetSolverTests.v` are its deliberate `Fail set_solver`
regression tests).

#### (1) `ProcInv` / `TfPage36` — TWO FILES, AND THEY WERE THE CORK

Both were pure STATEMENT residue against A6.49's ledger-page move, and
between them they gate the whole `Proof*`/boot cone.

- **`TfPage36`**: 108 occurrences of the raw `↦ₚ₈` in its 36-way
  open/close statements, while `ProcDefs.tf_words` has been
  `TsoCtx.ctx_phys_word_pointsto XI` since A6.58.  Fixed as a LOCAL
  NOTATION plus a token swap, not 108 spelled-out applications:

```coq
  Local Notation "a ↦ₚ₈c w" :=
    (TsoCtx.ctx_phys_word_pointsto XI a (DfracOwn 1) w)
    (at level 20, format "a  ↦ₚ₈c  w") : bi_scope.
```

  > **AND THAT IS WHERE THE MISSING KIT ITEM IS: the PHYS tier has no
  > notation twin.**  `TsoCtx.v`'s notation block gives the VA tiers
  > `↦ₘ`/`↦₈`/`↦₄`/`↦₂` and gives the PHYSICAL family nothing, so every
  > phys-tier statement in the tree either spells
  > `ctx_phys_word_pointsto` out or silently keeps meaning the RAW family.
  > Adding `↦ₚc`/`↦ₚ₈c` to the kit would rebuild the tree for a display
  > change; it is a cutover item, and until then **a `↦ₚ₈` in a statement
  > means the raw tower and should be read as a flip residue.**

- **`ProcInv`**: one wrong argument (`ctx_pointsto_of_phys`'s third premise
  is `ktier_pin cur_ktier ppn a`, not the identity equation a second time
  — `RiscvPtsto.ktier_pin_of_id` is the bridge, at any tier), plus twelve
  raw `word4_pointsto_*` lemma names where the cells are `↦₄`.

**Payoff: 900 → 988 in one round**, and the second-order cascade took it to
1080.  A6.65's "settle `ProcInv`/`TfPage36` first" was right and was the
single highest-value item on the queue.

#### (2) THE KIT GREW FIVE LEMMAS, IN ONE LEAF FILE, AND ONE SHIM USE DIED

`iris/CtxKMap.v` (A6.68's `ctx_mem_page_to_phys` file) now carries the
whole identity crossing, both directions, at the tower:

| lemma | direction |
|---|---|
| `ctx_mem_ident_phys` / `ctx_mem_page_to_phys` | VA-ctx → phys-ctx (A6.68) |
| `ctx_phys_ident_mem` / `ctx_phys_word_ident_mem` | phys-ctx → VA-ctx |
| `ctx_pointsto_of_ro_static` | raw byte + element → ctx byte |
| `ctx_buf_of_ro_static` | the `n`-byte fold |
| `ctx_word_pointsto_of_ro_static` | the 8-byte fold |

The `_ro_static` three are **the word/buffer twins of
`TsoCtx.ctx_pointsto_of_ro` the boot 26 needs** (A6.67 queue item 3).  The
kit lemma asks for a `ppn` and its `kmap_at` and holds the element at
`pa_of ppn a`; every boot site has neither and its elements
(`BootCarve.boot_led_ran`) are keyed at the address itself.  At a STATIC
kernel-data mapping the two coincide (`KMap.kmap_static_claims_at` pins the
ppn to `kpt_leaf_ppn`, `KptPt.pa_of_id` gives `pa_of ppn a = a`), so the
`_static` forms are the same mint with the identity discharged once.

**`BootBridge` IS GREEN AND ITS SHIM USE IS RETIRED HONESTLY — and the
diagnosis was not the expected one.**  `phys_word_to_word`'s premise was
the raw `↦ₚ₈`, so it looked like a `ctx_pointsto_of_ro` site.  It is not:
`StackOwn.stack_own_phys` has been `TsoCtx.ctx_phys_word_pointsto` since
the ledger-page move, so the bridge never leaves the tower and the right
primitive is the identity RE-ENTRY (`ctx_phys_word_ident_mem`), which needs
no element at all.  **The old raw route was dropping the ledger residue and
its return leg is the direction the flip makes false** — which is exactly
why the shim use there could not be replaced in place.  Shim: **30 → 29.**

#### THE BOOT 25, SURVEYED IN FULL — AND THE SUPPLY CHAIN IS THE WORK

Not landed; measured, so the next tranche starts with the answer.

**THE 25 USES ARE FOUR SHAPES, all in `BootCarveMain.v`:**

| shim function | uses | shape it had |
|---|---|---|
| `ctx_word_of_mem` | 15 | `word_pointsto a dq w ⊢ ctx_word_pointsto cur_ctx a dq w` |
| `ctx_pointsto_of_mem` | 6 | `mem_pointsto a dq v ⊢ ctx_pointsto cur_ctx a dq v` |
| `ctx_eslot_of_mem` | 3 | the same under `∃ w` (an existential word slot) |
| `ctx_buf_of_mem` | 1 | the byte-run fold |

**ONE SECTION** (`BootCarveMain.v:477`, `Context {!riscvGS Σ, !xv6G Σ}` —
**no `CurCtx`**, as the blacklist requires; every lemma binds
`` `{XI : TsoCtx.CurCtx} `` itself), **13 enclosing lemmas**, and the
internal call graph that must move in lockstep is `boot_lk_raw` (12 uses),
`boot_proc_slot`, `boot_page_own`, `boot_ofile_cells`, `boot_own_ctx`,
`boot_proc_name`.

**THE SUPPLY CHAIN IS THE REAL COST, AND IT HAS A HOLE IN THE MIDDLE.**
`RiscvAdequacy.v:531` is the ONLY supplier of `boot_led_ran g text_end
ram_hi` in the system; `BootShared.v` threads only `boot_raw_ran` and drops
the ledger half; `BootCarveMain.v` and `BootBridge.v` **do not mention the
ledger at all** (`grep boot_led\|ledger_elem0\|pristine_elem` → zero hits).
So the tranche is `RiscvAdequacy` → `BootShared` → `BootCarveMain`, and the
threading is index-for-index free once started: `boot_led_ran g lo hi` is
the ledger half of the SAME `ran_bytes g lo hi` map `boot_raw_ran g lo hi`
is the raw half of, and `boot_led_split` cuts with the identical arithmetic
as `boot_ran_split`.

> **TWO LEMMAS HAVE NOWHERE TO GET ELEMENTS FROM AND MUST BE HANDLED
> SEPARATELY:** `bpay_raw_buf_raw` (`:994`) and `file_node_raw_fentry`
> (`:1446`) are PURE TRANSPORT — no `g`, no `boot_raw_ran` — so they need
> a brand-new explicit element premise or must be inlined into their
> callers.

#### (3) THE `cpu_ctx_free` PRODUCER BILL IS SMALLER THAN A6.68 ESTIMATED

A6.68 priced "eight producers, three lines apiece".  **Measured: the eight
are mostly THREADING sites, which the record change does not touch** —
`ProofMainSecondary`, `SpecMain`, `SpecMainSecondary` and `BootBridge` are
all GREEN against the parked-record definition without a single edit.  Only
a site that CONSTRUCTS the record owes anything, and the two candidates
(`BootShared:1245`'s `rewrite /cpu_ctx_free`, `BootChain:454`) are still
unreached behind `BootCarveMain`.  **The bill is at most two sites.**

#### (4) THE MECHANICAL RESIDUE IS THREE CLASSES, AND ALL THREE ARE SCRIPTED

Roughly forty files went green on nothing but these.  The scripts are worth
rebuilding for the next tranche; each is a build-parse-patch loop.

1. **A missing `` `{XI : CurCtx} `` on ONE declaration** (A6.68's class,
   unchanged): a fixpoint, not one pass.  Two bugs worth pre-paying —
   take the `File` line CLOSEST to the error (the notation warnings emit
   their own at the top of every file), and check the error BLOCK for
   `CurCtx`, not the `Error:` line (the message is usually `Could not find
   an instance for the following existential variables:` with `?XI :
   CurCtx` three lines down).  **Also match `Corollary`**, not just
   `Definition|Lemma|Instance`.
2. **A RAW lemma name against a CTX cell**: `word{,2,4}_pointsto_{agree,
   half,half_split,half_join,frac_split,bytes,intro,aligned_p,persist,
   unfold,split4,join4}` → the `ctx_` twin.  **The twins take the CONTEXT
   as their first EXPLICIT argument**, so a call that passed positional
   underscores needs one more, and `(KTR := kt) a …` becomes
   `(KTR := kt) cur_ctx a …` — that shift is the whole second half of the
   class and it bit in `ProofSysUnlink`, `ProofDirlink`, `ProofKexecSeam`,
   `ProofSysPipe`.
3. **A RAW window spelled with an explicit `(KTR := kt)` in a STATEMENT**:
   `word4_pointsto (KTR := KT1) a dq w` is a statement that never got the
   M1 flip; the ctx family takes the context right after the tier.
   `ProofSysPipe`'s epilogue continuation and `ProofSysSbrk`'s were both
   this.

> **AND THE STALE COMMENTS ARE A HAZARD, NOT JUST NOISE.**  Five files
> carried a comment saying "stage 2: `↦₄`/`↦₂` is still the raw tower, so
> the ctx bytes cross here" beside a live `ctx_buf_forget`.  **`↦₄` and
> `↦₂` HAVE flipped** (A6.58 already said the comment was stale), so every
> one of those crossings is the IDENTITY and the right edit is to delete
> the line: `ProofArgraw`, `ProofDirlink`, `ProofKwait`, `ProofSysPipe`
> (×2).  A6.68's rule generalises: **the test is whose `↦` the next
> consumer means** — a consumer above `TsoCtx` wants the ctx family and
> the crossing is dead; one below it (`KMap`, `PtTree`, `BitmapInv`) wants
> the raw family and the crossing is real.

#### (5) FOUR REAL FINDINGS THE MECHANICAL SWEEP UNCOVERED

- **`BitmapInv.v` IS AN UNFLIPPED RAW-TOWER OWNER, and it is the last one.**
  It does not `Require TsoCtx`, so its two `↦₄` cells (`sb_size` and its
  neighbour) are the RAW family, while ~90 consumers — all of which DO
  import `TsoCtx` — read the same cells as ctx.  `ProofWritei:2271` is
  where the seam first bites (`ProofBmap`'s `wp_bmap_gen` states its
  premise at the ctx tower; `ProofWritei` hands it `BitmapInv`'s raw one).
  **This is A6.58's "one decision per raw-tower OWNER" table with one row
  left**, and the decision is the owner's: flip `BitmapInv` (two cells, ~90
  consumers to re-check) or state `wp_bmap_gen`'s premise raw.
  Characterised, not paid.
- **`ProofMain` IS NOT BLOCKED ON THE LOCK KIT — it is blocked on the A6.53
  PIN.**  Its eleven creator call sites are threaded (borrow at each,
  return after; the shape is `SieCapCtx.sie_cap_gpr_own_ctx_acc` as
  everywhere else) and the first three elaborate.  The file stops at
  `:992` on something else entirely: `KptShare.kpt_inv_alloc` gained the
  pin's bound `(B : nat)` and a `kptb_unset` premise, and main's boot chain
  threads neither.  **`ProofKvminithart:236` is the same cause** —
  `tlb_res_pt_intro` gained `(B0 : nat)` plus `kpt_bound B0` and
  `view_lb … B0`, and the call still passes the pre-pin argument list.
  The reference shapes are green and adjacent: `WpSconfSfence:434` and
  `KptShare:289`.  **The pin's boot-side threading is the next tranche's
  own item**, and it is what `ProofMain`, `ProofKvminithart` and (behind
  them) `BootShared`/`BootChain` are all waiting on.
  > The eleven `ProofMain` creator edits are therefore **PARTIALLY
  > VALIDATED**: everything above `:992` elaborated, the eight below it
  > has not been checked.
- **THE VIRTIO WIDTH-2 WINDOW IS ASYMMETRIC POST-FLIP.**
  `DiskInv.word2_to_phys` takes the CTX `↦₂` while `DiskInv.phys_to_word2`
  returns the RAW `word2_pointsto`, and `ProofVirtioDiskIntr:1165` /
  `ProofVirtioDiskRwD:686` do the round trip.  The honest repair is a
  `phys_ledger → ctx` re-entry, and that is NOT the identity crossing
  `CtxKMap` provides: `phys_ledger` carries the timestamp element but NOT
  the clean/dirty bit, so re-entering the tower needs the DMA lease's own
  pin (`TsoCtx.phys_ledger_at` / `phys_ledger_pin`, which exist for exactly
  this).  **The virtio/DMA lease lane is its own tranche.**
- **`ProofFilewrite:3405` is a KTIER mismatch, not a tower one** (`↦₈[KT1]`
  wanted, `↦₈[KT0]` in hand).  `ProofFilewriteParts`'s twin was fixed by
  moving the leaf's `(ktd := KT0)` to `KT1`; this one is inside
  `fw_devidx` and was not chased.

#### `WpSconfLock` — UNTOUCHED, AS INSTRUCTED

Parked as the M4 racy-owner-cell entry.  A6.68's two-site split stands:
`lock_claims` (`:139`) is payable with a context-free `wordw_claim` reader
(the claim is an ADDRESS fact and survives `ctx_pointsto_forget` at ANY ξ),
and that same reader is what `ProofVirtioDiskIntr` wants; the M4 content is
`wp_ld_lkcpu_lockopen_gen` (`:432`), the plain load that promises the
ledger's value for a cell it does not own.

#### THE RED 16

`BootCarveMain` (the 25), `ProofPrintk` (2) and `ProofSyscall` (1) — the
shim's remaining 29 references, all on the `↦ₛ` / boot-carve path;
`ProofMain` and `ProofKvminithart` — the A6.53 pin's boot threading;
`ProofWritei` — the `BitmapInv` owner decision; `ProofFilewrite` — one
ktier; `ProofVirtioDiskIntr` / `ProofVirtioDiskRwD` — the DMA lease lane;
`UtResFits` (`ut_res_bare_park` missing), `UmodeFetch`, `UptWalkPt`,
`UserMemPt`, `VcGenS`, `RiscvAdequacy`, `WpSconfLock` — A6.67's
characterised list, unchanged.

> **SUPERSEDED BY `tso-port.md` §0.21′ (owner, 3496cae8): `↦ₛ` is the MAIN
> tree's lane and arrives at cutover.  The costing suggested below was not
> done and must not be — see A6.70 ruling 2.**
>
> **`↦ₛ` HAS NOT FLIPPED, AND THAT IS THE RODATA THREE.**
> `RiscvPtsto.string_pointsto` is still the raw byte tower, which is what
> `ProofPrintk`'s two and `ProofSyscall`'s one cross on.  Its uses are 34
> files but only a handful of statements; **flipping `↦ₛ` is a smaller job
> than moving its three consumers**, and it would retire three of the
> twenty-nine shim references outright.  Worth costing before the boot 25.

#### THE QUEUE

1. **The A6.53 pin's boot threading** — `kpt_inv_alloc`'s `B`/`kptb_unset`
   and `tlb_res_pt_intro`'s `B0`/`kpt_bound`/`view_lb` through `ProofMain`
   and `ProofKvminithart`.  It unblocks `BootShared`, `BootChain` and the
   whole boot tail, and `ProofMain`'s eleven threaded creators are waiting
   behind it.
2. **The boot 25** — the survey above is the plan; the `_ro_static` twins
   are landed and waiting.  Cost the `↦ₛ` flip first (it may retire three
   more shim references for less).
3. **`BitmapInv`'s owner decision** (the last raw-tower owner).
4. `RiscvAdequacy`'s power tail, `UmodeFetch` + `UptWalkPt`, the
   `tramp_tr_obl` six, `UserMemPt`'s window accessor, `UtResFits`.
5. `VcGenS` — still six statements and an induction; `ProofSwtch`,
   `ProofAcquire` and `ProofRelease` sit behind it and `WpSconfLock`.
6. The DMA/virtio lease lane; `WpSconfLock`'s M4 memo.


### A6.70 THE FOUR RULINGS, EXECUTED — AND THE PIN'S PRODUCER SIDE IS A
### GATE THAT WAS NEVER WRITTEN

**CLEAN ROUND: 1083 of 1333, RED 14** (from A6.69's 1080/16) — `rm -f
iris/*.vo`, model `.vo` checked fresh, one full `-j12 -k`, and the
incremental round immediately before it agreed on BOTH the count and the
red set, file for file.  No `Admitted`, no `Axiom`.  The movement is small
because this tranche's content is decisions, not files.

#### RULING 1 — `BitmapInv`: FLIPPED, AND THE MEASURED COST WAS ZERO

The owner rule held exactly and the blast radius the estimate feared did
not exist.  Only `Section BitmapAllocRes` (two cells, `sb_size` and
`sb_bmapstart`) needed `Require TsoCtx` + `` Context `{XI : CurCtx} ``;
**`ProofWritei` went green and not one of the ~90 consumers moved**,
because every one of them already had a `CurCtx` in scope and was already
reading the cells as ctx.  A6.58's raw-tower-owner table is now **empty**.

> **THE GENERAL LESSON, and it is cheap to apply:** when a file's cells are
> read as ctx by every consumer and raw by the file itself, the flip is one
> section binder and the consumers do not move.  The expensive-looking
> "~90 consumers" number was a count of MENTION sites, not of edits — the
> same mistake A6.67's "count wrappers, not uses" corrects one tier over.

#### RULING 2 — `↦ₛ`: **OVERRULED BY THE OWNER MID-TRANCHE.**  NOT
#### EVALUATED TO A DECISION HERE, NOT FLIPPED, AND NO LONGER THIS TREE'S

The instruction was to evaluate ONE shape — pristine-as-definition for
`↦ₛ` — and flip on it if it held.  **The owner overruled the premise while
the evaluation was in flight** (`tso-port.md` §0.21′, commit 3496cae8), on
a ground the evaluation had already half-found: **the kernel has
DYNAMICALLY GENERATED strings** — `safestrcpy` at kfork/kexec writes
`p->name` at t > 0 — **and a t=0-hardcoded `↦ₛ` could never state their
data.**  The evaluation's own scope limit (see below) was the same fact
seen from one site; the owner's ruling is the general form of it.

**THE DISPOSITION, and it is not this tree's work:** `↦ₛ` **stays RAW**
here, with its three named bridges, and the three rodata shim references
(`ProofPrintk` ×2, `ProofSyscall` ×1) stay in the residue ledger marked
**"awaiting the §0.21′ port"**.

> **THE PORT LANDED ON MAIN 2026-08-27 (`tso-port.md` §0.22′, commit
> `4d73cc8b`) AND IS NOW THIS TREE'S QUEUE ITEM 1 — see A6.71's
> cross-lane section for the recipe, the structure rule that answers the
> import-order finding below, and the one arm this tree owes.**  The proper redefinition — a CTX string
tower at arbitrary timestamps, with pristine kept only as the DERIVED
context-free form for the rodata / lock-handle sites — is being done on the
MAIN tree by a parallel lane and ports at cutover.

> **AND THE SHAPE THIS TRANCHE WAS TOLD TO TRY IS THE ONE TO AVOID.**  What
> the evaluation was converging on was a SPLIT: `↦ₛ□` re-pointed at a
> pristine definition, `↦ₛ{dq}` left raw, precisely because
> `ProofSyscall.sysc_pname_app`'s `p_name pa 0 ↦ₛ{dq} nm` is written at
> runtime and nothing pristine can be said about it.  **Two definitions
> behind one notation family is exactly the thing §0.21′'s single ctx tower
> replaces**, and it would have had to be unpicked at the port.  Landing
> nothing was the right outcome.

**TWO MEASUREMENTS FROM THE ABORTED EVALUATION ARE WORTH KEEPING, because
the §0.21′ port will meet both:**

- **THE IMPORT-ORDER FACT.**  `string_pointsto` lives in `RiscvPtsto.v`,
  **BELOW `TsoCtx.v`**, so it cannot mention `ctx_pointsto` where it
  stands.  A ctx string tower therefore either moves the definition above
  the tower (and with it the `↦ₛ` notation family, 34 files) or splits
  declaration from definition.  `pristine_elem` is the only ledger
  vocabulary available at `RiscvPtsto.v`'s altitude (`:1535`), which is
  why the pristine spelling looked forced from inside this tree.
- **THE RECEIPTS ARE ALREADY IN THE CARVE'S HAND.**
  `BootCarve.kernel_data_intro` (`:569`) takes
  `[∗ map] a ↦ _ ∈ ran_bytes g text_end rodata_end, TsoCtx.pristine_va a`
  and spends them through `ctx_pointsto_of_pristine_va` to build
  `kernel_data`'s ∀ξ form; `KernelDataInv.kernel_data_string` (`:171`) then
  instantiates ξ at a junk `MkCtxId inhabitant inhabitant` and FORGETS to
  the raw tower.  **Whatever §0.21′ lands, the rodata half needs no new
  supply — it needs the mint to stop discarding what it is handed.**

#### RULING 3 — the virtio width-2 asymmetry: ROUTED, no code change

`DiskInv.word2_to_phys` takes the CTX `↦₂`, `DiskInv.phys_to_word2` returns
the RAW `word2_pointsto`, and `ProofVirtioDiskIntr:1165` /
`ProofVirtioDiskRwD:686` do the round trip.  The re-entry needs the
clean/dirty bit `phys_ledger` does not carry, so it is
`phys_ledger_at`/`phys_ledger_pin`'s job — the DMA lease's own lane, as
diagnosed and as ruled.  Both files stay red under that lane.

#### RULING 4 — the phys notation twin: NOT STARTED, sequenced last

As ruled.  It pairs naturally with the `↦ₛ□` flip above (same mechanism,
same tree-wide re-meaning, same rebuild).

#### THE PIN: TWO FILES GREEN, AND THE THIRD IS BLOCKED ON A MISSING GATE

**`ProofKvminithart` and `ProofMainSecondary` ARE GREEN.**  The fix is
A6.55's own ruling one level down: `KptShare.kpt_creds` — the pin's
publication bound paired with THIS hart's receipt that its view has passed
it — becomes a PREMISE of `SpecKvminithart.wp_kvminithart_sconf_body` and,
above it, of `SpecMainSecondary.wp_main_secondary_sconf_body`.  It is
persistent, so threading costs nothing; the call site then reads
`iDestruct "Hcreds" as (Bc) "[#Hbdc #Hvlbc]"`, which is `SmodeCorePt`'s
green shape (it takes the same pair out of `tlb_res_pt`).  The obligation
lands where it belongs: a secondary hart's honest source is its own acquire
of `started` — the spin is a plain load but the `__sync_synchronize` after
it DRAINS (`RiscvLang.fence_drains`), so the hart emerges at the log top.
**Named debt on the (unreached) boot chain, not a hidden assumption.**

**`ProofMain` IS NOT, AND THE REASON IS A GATE NOBODY EVER WROTE.**  Three
findings, one item:

1. **`kptb_unset` HAS NO ALLOCATOR.**  `KptGhost.v` defines it, exactly two
   places consume it (`KptShare.kpt_inv_alloc`, `tlb_inv_pt_share`), and
   **nothing in the tree produces it** — while its twin `kpt_unset` has the
   full chain `RiscvAdequacy:1292` (the `own_alloc`) → `:1052`
   (`power_boot_res`) → `BootShared:1129` → `BootChain:741` →
   `SpecMain:646` → `ProofMain:831`.  A6.63 added the RA and the functor
   (`inG Σ kptbR`, `GFunctor kptbR`); the ERA MINT was never added.  **Same
   class as A6.63's own finding: a record field is capacity you must also
   allocate.**  This half is pure threading, five files.
2. **NOTHING MOVES A TREE FROM `UTier ξ` TO `KTier B`.**  `kpt_inv_alloc`
   wants `kptree_own B 2 (DfracOwn 1) t` = `ptree_own_at (KTier B) …`, and
   `PtTree.pt_slot_own (KTier B) = phys_ledger_word_pin … B …`, whose
   element arm is `Some (Sv, B)` — while `ctx_pointsto`, `ctx_phys_pointsto`
   and `phys_ledger` all pin that option to `None` **by definition**
   (`TsoCtx.v`'s own note says so, and says it is what keeps every store
   gate sound).  So the move is a GHOST UPDATE against the interp — it must
   discharge `TsoMemPa.pin_ok`, "from view B on, every agent's read of `a`
   lands in `Sv`" — and **there is no lemma anywhere that performs it**
   (`grep KTier` outside `PtTree.v` returns consumers only).  This is the
   canon pin's PUBLICATION STEP: designed in A6.53, its consumer side
   landed at A6.53–A6.55, its producer side never written.
3. **AND THE BOUND NEEDS AN `llb` IT DOES NOT CARRY.**  For a secondary to
   discharge `kpt_creds` from a top-of-log receipt it needs `B ≤ K`, i.e.
   `B` a legal log position.  `kpt_bound` is agreement-only (`kptbR` is
   `csum (excl unit) (agree nat)`); `llb loglen_name B` is what makes the
   comparison free, exactly as `ctx_parked`'s stamp carries one.

> **THIS IS ONE COHERENT DESIGN ITEM AND IT IS THE OWNER'S.**  The natural
> shape is a publication gate at hart 0's fence, choosing `B` := the
> publisher's OWN view bound so the receipt is free by construction and the
> `llb` comes with it:
> ```coq
>   Lemma kptree_publish `{CID : CpuId} (g : gstate) (xi : CtxId) lvl (t : ptree) :
>     (length g.(glog) <= g.(gtv) cpu_id)%nat ->
>     tso_interp_at riscv_eraGS g -∗ own_context xi -∗
>     ptree_own_at (UTier xi) lvl (DfracOwn 1) t ==∗
>     tso_interp_at riscv_eraGS g ∗ own_context xi ∗
>     ∃ B : nat, ptree_own_at (KTier B) lvl (DfracOwn 1) t ∗
>                llb loglen_name B ∗ hart_view_lb B.
> ```
> It is at-the-top (hart 0 reaches `__sync_synchronize`, which
> `RiscvLang.fence_drains` drains — A6.55 §5.6(b)'s own argument), it is
> the interp-side dual of A6.68's `ctx_absorb_lb`, and the `pin_ok`
> obligation is the real content: the slots are DfracOwn 1 and never
> written again, which is what makes `Sv` a singleton from `B` on.
> **Characterised, not paid — `ProofMain`, `BootShared`, `BootChain` and
> the whole boot tail are behind it.**

#### THE RED 14

`BootCarveMain` (the 25 shim refs — A6.69's survey is the plan),
`ProofPrintk` (2) and `ProofSyscall` (1) — the rodata residue, RAW and
**awaiting the §0.21′ port**, no longer this tree's item; `ProofMain` — the pin's publication
gate; `ProofVirtioDiskIntr` / `ProofVirtioDiskRwD` — the DMA lease lane;
`ProofFilewrite` (one ktier), `UtResFits` (`ut_res_bare_park` missing),
`UmodeFetch`, `UptWalkPt`, `UserMemPt`, `VcGenS`, `RiscvAdequacy`,
`WpSconfLock` (the parked M4 entry).

#### THE QUEUE

1. **The canon pin's publication gate** (the three items above, one owner
   decision).  It is the single blocker on the whole boot tail.
2. **The boot 25**, per A6.69's survey — and `BootShared`'s dropped ledger
   half is the same file the pin's `kptb_unset` threading touches, so the
   two want to be one pass.
3. **The phys notation twin**, against a green tree — a bottom-of-tree
   re-meaning, sequenced last as ruled.  (`↦ₛ` is NOT here: it belongs to
   the main tree's §0.21′ lane and arrives at cutover.)
4. `RiscvAdequacy`'s power tail, `UmodeFetch` + `UptWalkPt`, the
   `tramp_tr_obl` six, `UserMemPt`, `UtResFits`, `ProofFilewrite`.
5. `VcGenS` (six statements and an induction) — `ProofSwtch`, `ProofAcquire`
   and `ProofRelease` are behind it and `WpSconfLock`.
6. The DMA/virtio lease lane; `WpSconfLock`'s M4 memo.


### A6.71 THE PRODUCER GATE IS BUILT AND GREEN — AND ITS SITE DOES NOT
### EXIST, WHICH IS THE ONE THING A6.70 DID NOT MEASURE

**CLEAN ROUND: 1087 of 1333, RED 12** (from A6.70's 1083/14), the
incremental round before it agreeing file for file.  Details, the red
table and the queue are at the end of this section.

**A6.70's design is NOT refuted: the gate is provable, and it is proved.**
`kptree_publish` exists, discharges `TsoMemPa.pin_ok` per element off the
interp's own latest tie, and cost two leaf files and one afternoon.  What
the tranche found instead is that **the lemma has nowhere to be applied**,
and the reason is §0.17′'s rule read in the direction A6.68 did not need:

> `own_context` is only in hand OUTSIDE a WP leaf.  `tso_interp_at` is only
> in hand INSIDE one.

A6.68 hit that from the transport side and answered it with a RECEIPT form
(`ctx_absorb_lb`).  **The publication cannot be answered the same way**, and
the reason is not a missing lemma but the algebra: the move from
`(t, None)` to `(t, Some (Sv, B))` is a `ghost_map_update` on `ts_name`, and
that authority lives in `tso_interp_at` and nowhere else.  Measured:
**`tso_interp_at` occurs in FIFTEEN files and not one of them is a
`Proof*.v`** (`HartLift2`, `HartMStore`, `HartMemRun`, `RiscvExec`,
`RiscvAdequacy`, `RiscvPtsto`, `SmodeCorePt`, `TsoCtx`, `TsoCtxAbsorbLb`,
`VirtioProto`, `WpVirtio`, `WpMmodeLoad`, `WpSmodePtLeaves`, `WpSmodePtMem`,
`WpUart`).  `ProofMain:992` — where `kpt_inv_alloc` is called — is a ghost
step under `iApply fupd_wp` between two `jal`s.  There is no leaf there.

#### WHY NO WEAKER GATE EXISTS — three candidates, all refuted at the pure layer

1. **Derive `pin_ok` at READ time from an unpinned element plus `⌜t ≤ B⌝`.**
   True for a slot that is never written again (`pin_ok_mint` needs exactly
   that), and FALSE the moment the A/D write-back runs: the write-back's
   timestamp is `S (length glog) > B`, while `pin_ok` still holds because
   the NEW byte is in `Sv` (`pin_ok_app`).  A single exposed timestamp
   cannot state that; the history can only be maintained, which is why it
   is an interp conjunct.  **This is A6.53's design re-derived, not a gap.**
2. **Make the tie derivable so the element move is free** — i.e. put
   `⌜e.1 ≤ B ∧ v ∈ Sv⌝` in `ts_ok` instead of `pin_ok`.  Same refutation
   from the other end: the write-back breaks `e.1 ≤ B` while preserving the
   pin.
3. **Mint per slot at its own STORE** (`wobl_ram_ledger_pin_ex` exists and
   the store leaf does hold the interp).  Refuted by uniformity:
   `ptree_own_at (KTier B)` wants ONE `B` for the whole tree, the slots are
   written at increasing timestamps, and raising a minted pin's `B` is
   itself an element move.  *(There is a cheap repair if this route is ever
   wanted: make `phys_ledger_pin a dq v t B Sv` existential in the stored
   bound — `∃ B0, ⌜B0 ≤ B⌝ ∗ … (t, Some (Sv, B0))` — which makes upward
   weakening free by `pin_ok_mono` and costs one line in
   `ledger_read_pin_ok`.  Recorded, not landed: it does not help
   `ProofMain`, only the store-side route.)*

#### THE SITE IS AN OWNER DECISION, AND THE TREE ALREADY NAMES THE MISSING PIECE

`HartLift.v:139`, in the comment that made `Barrier` a silent node:

> "**§6's barrier leaf is a SEPARATE rule over the same node**, for the
> proof that wants the acquire receipt; keeping `Barrier` silent here is
> what keeps every existing silent-stretch proof working unchanged."

That rule has never been written.  `wp_hsil_node` already opens the interp
at a barrier (it must — a draining fence MOVES the view), so the machine
half is in place; what is missing is the lift of a client-facing rule
through `HartSpan`/`HartMemRun`/`HartLift2`/`RiscvExec`/`WpSconfEngine` to
a `wp_fence_publish_s_sconf` beside `WpSconfCtl.wp_fence_gen_later_s_sconf`
(which is the precedent: a fence rule that already carries a client
payload, with the file's own comment saying "the fence IS the acquire
barrier, so the reading the proof wants is that the fence is where `▷ P`
becomes `P`").  **Adding it breaks no exported statement.**

**AND THAT ALONE IS NOT ENOUGH, WHICH IS THE PART THAT NEEDS THE OWNER.**
`main()` has NO fence between `kvminit()` and `kvminithart()`; the drain is
`__sync_synchronize()`, six calls later.  `sfence.vma` is not a `Barrier`
node at all (A6.41's measurement), so `kvminithart`'s own two fences cannot
serve.  So the publication has to MOVE to `__sync_synchronize` —
pin-memo §5.6(b)'s own recommendation, "keep `tlb_inv_pt` across hart 0's
window and mint the pins at `__sync_synchronize`" — and that reopens
`SpecKvminithart`: A6.70 made `KptShare.kpt_creds` a PREMISE of
`wp_kvminithart_sconf_body`, which hart 0 cannot supply before publication.
Hart 0 would need the EXCLUSIVE arm (`tlb_inv_pt`, which
`KptTree.tlb_inv_pt_intro` still builds) and the secondaries the shared
one — **two forms of kvminithart's contract, which IS an exported-statement
change.**  Characterised and stopped there, per the standing constraint.

> **THE THREE CANDIDATE SITES, COSTED.**
> (a) **The barrier leaf + move the publication to `__sync_synchronize`.**
>     The honest one and pin-memo §5.6(b)'s own choice.  Cost: one new node
>     rule lifted through five files, plus the kvminithart split.
> (b) **A publish-capable variant of the `jal` leaf** at `ProofMain:992`'s
>     own instruction.  No contract moves, and it needs no drain argument
>     of its own IF the at-the-top premise can be established there — which
>     it cannot: hart 0 has just run `kvminit`, whose stores are in its
>     buffer, so `length glog ≤ gtv cpu_id` is FALSE at that instruction.
>     **Refuted, and the refutation is the same fact that forces (a).**
> (c) **Pin at the store** (candidate 3 above) — refuted on uniformity.
>
> So (a) is the only live route, and its cost is a real tranche.

#### WHAT LANDED (all green, no `Admitted`, no `Axiom`)

**`iris/CtxPinMint.v` — the ctx→pin crossing at the BYTE and the WORD.**
Its own file for `TsoCtxAbsorbLb.v`'s reason (A6.68): a derivation off
`TsoCtx.v`'s PUBLIC unseal lemmas, and `TsoCtx.v` is under the whole tree.
Three lemmas:

```coq
  tso_interp_ts_le  : tso_interp_at g -∗ a ↪[ts_name]{dq} e -∗
                      ⌜(e.1 ≤ length g.(glog))%nat⌝
  ctx_phys_pin_mint : (length g.(glog) ≤ B)%nat -> v ∈ Sv ->
                      gen_heap_interp g.(gmem) -∗ tso_interp_at g -∗
                      ctx_phys_pointsto xi a (DfracOwn 1) v ==∗ … ∗
                      ∃ t, phys_ledger_pin a (DfracOwn 1) v t B Sv
  ctx_phys_word_pin_mint  (the 8-byte fold, offset-indexed sets)
```

`tso_interp_ts_le` is the half the CALLER must never be asked for and the
interp always has: `latest` demands `log_byte img log t a = Some v`, and
`TsoMemPa.log_byte_some_le` reads `t ≤ length log` straight off it.  So the
mint's only real premise is that `B` is at or above the log top.

**`iris/KptPublish.v` — the tree gate, A6.70's recorded shape.**
`pte_slot_set_self` (a word is in its own family — the leaf case is
`PtAdBits.pte_set_ad_refl`, "every word is an A/D variant of itself"), then
the slot run, the node, the children (with the level's IH handed in as a
Coq-level premise: the tree recurses on the LEVEL and the big-op on the
LIST, so the two inductions cannot be one), then

```coq
  Lemma kptree_publish `{CID : CpuId} (g : gstate) (xi : CtxId) lvl (t : ptree) :
    (length g.(glog) <= g.(gtv) cpu_id)%nat ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ own_context xi -∗
    ptree_own_at (UTier xi) lvl (DfracOwn 1) t ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ own_context xi ∗
    ∃ B : nat, ptree_own_at (KTier B) lvl (DfracOwn 1) t ∗
               llb loglen_name B ∗ hart_view_lb B.
```

**TWO AMENDMENTS TO A6.70'S RECORDED STATEMENT, both measured:**

1. **`gen_heap_interp` is FORCED, not decoration.**  `TsoCtx.ledger_pin_mint`
   must know the FLAT cell's value to discharge `v ∈ Sv` against the map the
   interp's tie speaks about (`phys_valid`), so the flat interp travels with
   the tso one.  Every site that has one has the other, so this costs
   nothing — but the recorded statement was short by a conjunct.
2. **`own_context xi` is THREADED, NOT CONSUMED, and is not needed at all.**
   A slot's clean/dirty bit is a ghost-map FRAGMENT; abandoning one leaves
   `own_context`'s dirty-watermark arm (a statement about the AUTHORITY's
   domain) intact.  Kept in the recorded shape as documentation of WHOSE
   table is published; `kptree_publish_bare` is the same gate without it.

`B` is chosen as the publisher's own view (`g.(gtv) cpu_id`), which is what
makes both receipts free: `TsoCtx.hart_view_lb_get` at `T = 0` (`llb_0`)
hands back `hart_view_lb (gtv cpu_id)`, and `TsoGhost.view_lb_llb` projects
the `llb`.  Nothing is invented.

#### THE `kptb_unset` ERA ALLOCATOR IS LANDED, FIVE FILES, EXACTLY A6.70's PREDICTION

A6.63 added the RA (`kptbR`), the functor field and the era gname; the ERA
MINT was never handed to the client, so `KptShare.kpt_inv_alloc`'s second
one-shot premise had no producer anywhere in the tree.  The chain now
mirrors `kpt_unset`'s, row for row:

| file | what was added |
|---|---|
| `RiscvAdequacy` (system bundle) | `kptb_unset ∗` beside `kpt_unset ∗`; `Hkptb` framed (the `own_alloc` was already there) |
| `RiscvAdequacy.power_boot_res` | `own (era_kptb_name HE) (Cinl (Excl ()) : kptbR) ∗`; `Hkptb2` framed |
| `BootShared` (`power_boot_res_unpack`, `boot_hart_pre`) | one conjunct each |
| `BootChain` | one premise + one `iIntros` name |
| `SpecMain` / `ProofMain` | one premise + three `iIntros` names |

> **AND THE DEVICE-ONLY COROLLARY IS THE THIRD FILE THAT COUNTS
> UNDERSCORES.**  `riscv_device_adequacy`'s `iIntros` discards the boot
> bundle positionally, so every conjunct added to it costs one more `_`
> there.  Same class as A6.69's mechanical residue 1; the tell is
> `iIntuitionistic: (virtio_frag …) not persistent`, which names a
> DIFFERENT conjunct than the one that moved.

#### `kpt_bound` CARRIES ITS `llb`, AND THE PUBLISHER PAYS IT FOR NOTHING

A6.70 finding 3, landed: `KptGhost.kpt_bound B` is now
`own kptb_name (Cinr (to_agree B)) ∗ llb loglen_name B` (still persistent —
one `bi.sep_persistent` on the instance), `kptb_shoot` takes the receipt,
and a new `kpt_bound_llb` projects it.  `KptShare.kpt_inv_alloc` gained the
premise; **its one existing caller pays nothing**, because
`KptTree.tlb_inv_pt` already carries `view_lb view_name loglen_name … B` and
`TsoGhost.view_lb_llb` projects the `llb` from it.  `kptree_publish` hands
the two out together for the same reason.

#### `RiscvAdequacy` IS GREEN — AND IT WAS THE BOOT TAIL'S REAL CORK

Not "the power tail" as a design item: **four mechanical residues**, none
of them a decision, and behind them sat `BootShared` → `BootCarveMain`
(the boot 25) as well as the whole `power_boot_res` chain.

1. **`boot_facts`' last conjunct is the flip's FOUR-way machine-reset fact**
   (reservations, log, image, views), not the reservation clause alone —
   the power arm's `resv_map_none` call wanted `proj1` of it.
2. **The power arm never got its `tso_interp_at`.**  A6.59 landed the
   conjunct in the SYSTEM theorem and A6.63′ landed the four ALLOCATIONS in
   the power arm, but not the interp they feed.  It is the boot
   construction verbatim at `g2`: a fresh era starts with an empty log, so
   all four conjuncts are the same fact read four ways, and `boot_shape`'s
   own reset clause supplies every one.
3. **`boot_fixedGS` counts underscores**, and `riscvFixedGS` gained TWO
   fields since it was written (`riscvF_kptbGS` between `kptGS` and
   `lockSetGS`, `riscvF_tsomemGS` between `resvGS` and `diskGS`), so both
   positional runs are one longer.  The error names the FIRST named
   argument after the short run (`γgen … expected mono_natG Σ`), which
   points three fields away from the one that moved.
4. **`power_interp_resv_ok` walks `era_interp` positionally** and needed one
   more `_` for the same conjunct as (2).

> **THE LESSON, and it generalises past this file:** every one of the four
> is "a conjunct/field was added below, and a POSITIONAL consumer above did
> not move".  A6.69's mechanical class 1 was about a missing binder; this
> is its dual and it has the same tell — **the error always names a
> neighbour, never the conjunct that moved.**  Read the SHAPE, not the
> name.

#### `ProofFilewrite` IS GREEN, AND THE FIX IS A GENERALISATION, NOT A TIER MOVE

A6.69 filed it as "one ktier" and A6.70 kept it there.  **Measured: the
mismatch is not repairable at the CALL site, in either direction.**
`SpecFilewrite.filewrite_dev_env` states the `devsw[major].write` cell at
the AMBIENT tier (`Ktier.curktier_default` = `KT0`) while the function runs
at `sie_cap_gpr KT1`, and `ProofFilewriteParts.fw_devidx` demanded `KT1` on
BOTH legs — so the caller could neither supply the cell nor take it back
(`ctx_word_ktier_mono` is one-way `KT0 → KT1`, and `fwn_dqv` is an
arbitrary dfrac, so it cannot be duplicated either).

**The fix is one binder on `fw_devidx`:** `{ktd : ktier} `{!KtierLe ktd
KT1}`, the slot at `(KTR := ktd)` in premise and continuation, and
`(ktd := ktd)` on the `c.ld` leaf inside.  **That is the LEAF's own shape
one tier up** — `wp_cld_s_sconf` already carries exactly that pair — so it
is a generalisation, no Spec statement moves, and the crossing stays out of
the round trip.

> **THE RULE, and it is worth carrying:** when a helper pins its DATUM's
> tier to the capability's, it silently forbids every caller whose datum is
> static kernel data.  A helper's datum tier should be `{ktd}` +
> `KtierLe ktd kt` unless it has a reason not to be — the leaves are
> already stated that way and Ktier.v's own note explains why.

#### THE SHIM, RE-COUNTED — AND IT IS A TOMBSTONE ALREADY

**`TsoCtxShim.v` is 43 lines and carries exactly ONE lemma,
`own_context_alloc`.**  Every other name it ever had is gone.  So the "29
references" are **29 DANGLING NAMES in four red files** — not uses of a
live shim — and four of the twelve red files are red for that one reason:

| file | dangling refs | what they need |
|---|---|---|
| `BootCarveMain` | 25 | the honest raw→ctx mint (below) |
| `ProofPrintk` | 2 | the §0.22′ string tier (below) |
| `ProofSyscall` | 1 | the §0.22′ string tier |
| `WpSconfLock` | 1 | the parked M4 entry |

`Require TsoCtxShim` still appears in 23 files with no use; those are free
to strip whenever someone is in the neighbourhood (A6.64's comment-balance
rule applies to any script that does it).  **Count unchanged this tranche:
29 refs, 4 files.**

#### THE BOOT 25, RE-SURVEYED AGAINST THE GREEN `RiscvAdequacy` — AND
#### A6.69's DEPENDENCY DIRECTION WAS BACKWARDS

A6.69 wrote the supply chain as `RiscvAdequacy → BootShared →
BootCarveMain`.  **Measured from `.CoqMakefile.d`, it is the other way:**
`BootCarveMain` → `BootChain` → `BootShared`, and `BootChain` additionally
needs `LinkMain` (hence `ProofMain`).  Three consequences:

- **`BootCarveMain` is REACHABLE NOW** — all of its dependencies are green
  — and it is the only one of the three that is.
- **`BootShared` and `BootChain` are behind `ProofMain`**, i.e. behind the
  publication gate's missing site.  They are not their own items.
- **The elements cannot arrive "from BootShared".**  They must arrive as a
  PREMISE: `BootCarve.boot_led_ran g lo hi` threaded into `BootCarveMain`'s
  thirteen carve lemmas beside the `boot_raw_ran` they already take, with
  `BootShared`/`RiscvAdequacy` supplying it at the top — which is exactly
  the shape `BootCarve.boot_ctx_phys_word` / `boot_stack_own_phys` already
  have (`boot_raw_ran -∗ boot_led_ran -∗ …`).

**AND THE MISSING KIT PIECE IS NAMED:** `BootCarve` has the ELEMENT family
(`boot_led_ran`/`_split`/`_bytes`/`_word`) and the PHYSICAL pairing
(`boot_ctx_phys_word`), but **no VA-tier pairing** — no
`boot_ran_cell8_ctx` / `_cell4_ctx` / `_cell2_ctx` / `_byte_ctx` /
`_run_ctx`.  `boot_ran_cell8` and friends produce the RAW word (BootCarve
does `Require TsoCtx`, NOT `Import`, so its `↦₈`/`↦ₘ` are the raw family —
worth knowing before reading that file), and the crossing to ctx is what
the 25 dangling shim names were doing.  The mints to build them on are
landed and waiting: `CtxKMap.ctx_pointsto_of_ro_static` /
`ctx_word_pointsto_of_ro_static` / `ctx_buf_of_ro_static` (A6.69).

> **BUT PRICE IT BEFORE STARTING: `BootCarveMain` UNBLOCKS THREE FILES.**
> The measured blocked-cone sizes of the twelve red files are
> `WpSconfLock` 160, `VcGenS` 85, `ProofPrintk` 68, `ProofVirtioDiskRwD`
> 66, `UserMemPt` 46, `UptWalkPt` 42, `UmodeFetch` 37, `UtResFits` 21,
> `ProofVirtioDiskIntr` 15, `ProofSyscall` 11, `ProofMain` 5,
> `BootCarveMain` 3 (248 files behind the twelve, of 249 unbuilt).  The
> boot 25 is a QUEUE item, not a cork.

#### THE U-MODE WALK LANE IS ONE ITEM, NOT THREE, AND IT IS A THREADING

`UmodeFetch`, `UptWalkPt` and `UserMemPt` are the same cause:
`UserPtTree.utlb_inv_pt_translateAddr_u` grew A6.24's payer — a
memory-indexed payload `S : bytemap → iProp Σ` plus a `□` wand that pays
the PTE write-back at the caller's own context — and the U-mode consumers
still pass the pre-payer argument list.  The tell is not a tier error: it
is `The term "Hl" has type "… = Some w" while it is expected to have type
"TsoMemPa.bytemap → iProp ?Σ"`, i.e. a POSITIONAL argument landing in the
new `S` slot.

**The template is green and adjacent** (`UptTree`'s two wrappers, and the
S-mode lane's `SmodeCorePt`, which threads `S` all the way up and
instantiates it with `tso_interp_of` at the top).  The measured scope:
`UmodeFetch` 5 call sites, `UserFetchPt` 7, `UserMemPt` 2, `UserMemMis` 2,
`UserMemAccess` 2 — **18 sites in five files, all currently unbuilt**, and
the threading terminates where the S-mode one does.  **One tranche, one
pass; it is worth ~125 files.**

#### THE CROSS-LANE RULING THAT ARRIVED MID-TRANCHE: §0.22′ IS LANDED ON
#### MAIN AND IT IS THIS TREE'S NEXT ITEM, NOT A SEPARATE WAVE

**`tso-port.md` §0.22′ (owner/main, commit `4d73cc8b`) LANDS the ctx string
tower** — the port obligation A6.70 ruling 2 filed as "awaiting the §0.21′
port".  Recorded here as the queue's item, per the coordinator's routing:
it belongs to the frontier's `ProofPrintk`/`ProofSyscall` item, not to a
wave of its own.  **NOT STARTED IN THIS TRANCHE** — it is a `TsoCtx.v`
change under the whole tree (44 files on main, four rounds), and starting it
behind an unfinished publication gate would leave two flips in flight, which
A6.69's own ruling forbids.

**WHAT PORTS, AND THE STRUCTURE RULE THAT MAKES IT CHEAP.**  A6.70's
import-order finding is ANSWERED and the answer needed no new decision:
**a tier flip never relocates the raw definition.**  `TsoCtx.v` declares a
SECOND tower (`ctx_string_pointsto ξ a dq s := [∗ list] j ↦ b ∈
cstring_bytes s, ctx_pointsto ξ (pa_add a j) dq b`) and re-declares the
four `↦ₛ` spellings at it; `RiscvPtsto`'s raw tower stays put as the
below-Σ fact, exactly as `word4_pointsto` does.  Import order decides, the
spellings are character-identical, nothing moves.  Law set: the stage-2
word towers' adapted to strings — **with `_bytes_agree` DELIBERATELY WEAKER**
(byte-level, because a string may be a proper prefix of another through an
embedded NUL, which only `PrintkFmt.nonul` far above `TsoCtx` rules out).

**THE HANDLE FORM IS WHAT THIS TREE ACTUALLY NEEDS.**
`ctx_string_all a dq s := ∀ ξ, ctx_string_pointsto ξ a dq s` —
persistent, `kernel_data`'s own shape — carried by `WpLock.lock_name` and
`SleepLock.sl_name`, which keeps **`is_lock`/`is_sleeplock` CHARACTER-
IDENTICAL and still CLOSED**.

> **IT IS HALF THE PARK PROTOCOL'S FIRST DESIGN PROBLEM — AND THE HALF IT
> IS NOT MUST NOT BE MISREAD AS SOLVED.**  Main reports `UsertrapRes.v` /
> `UtResFits.v` / `ParkCap.v` untouched and green across ITS flip, and the
> ∀-context handle is what keeps `is_lock` closed there.  **But this tree's
> `ut_res_bare_park` is `Abort`ed (`UsertrapRes.v:1768`, with its own
> paragraph saying why), and the abort is on the PAYLOAD half, not the
> name:** `procs_inv`'s per-proc `is_lock`s wrap payloads reaching
> `proc_ctx`/`valid_context`, which ARE ξ-dependent, and `proc_ctx (XI := ξ)
> ⊣⊢ (XI := ξ′)` fails `reflexivity` fast (the earlier 35-minute
> `iExact "Hcaps"` was unification exhausting itself on an unprovable goal).
> So §0.22′ retires the NAME half of the handle and the M2 redesign the
> file already sketches — **λ-convert the proc-lock payload so `procs_inv`
> is a CLOSED term (§0.19′ recipe rule 1), or pin the resumer's bundle to
> `N`'s `un_*` fields** — is still owed for the other half.  `UtResFits`
> (21 files behind it) needs BOTH.

**THE ONE ARM THIS TREE OWES AND MAIN COULD ONLY SKETCH:**
`ctx_string_all`'s mint at `⌜t = 0⌝`, through the ctx byte's CLEAN-ARM
disjunct (`llb γ 0`, A6.10's timestamp-0 fact — the reason the clean arm is
`llb`-shaped and not a bare lower bound).  **That is where
`BootCarve.kernel_data_intro`'s pristine receipts finally get spent**, and
A6.70's own measurement said the supply was already in the carve's hand and
being discarded: `KernelDataInv.kernel_data_string` instantiates
`kernel_data`'s ∀ at a junk `MkCtxId inhabitant inhabitant` and forgets to
the raw tower.  On main that junk witness is gone —
`kernel_data_string_all` keeps the ∀ — and **the whole chain rodata →
`kernel_data_string_all` → `lock_name_intro` → `is_lock` has no seam at
all.**

> **THE DIAGNOSTIC WORTH KEEPING (main's own lesson):** *a lemma that
> instantiates a ∀ at a junk witness is a lemma whose conclusion is in the
> wrong tier — the junk witness IS the diagnostic.*  Grep for
> `MkCtxId inhabitant`.

**WHAT IT RETIRES HERE, measured against this tree's red set:** the three
rodata shim references (`ProofPrintk` ×2, `ProofSyscall` ×1) collapse into
`kernel_data_string_all` with ZERO shim — **68 + 11 files behind those two**
— and `ProofSyscall`'s hand-rolled `sysc_name_addr`/`sysc_pname_app` split
retires into `ProcDefs`'s `pname_cells_borrow`/`_return` accessor family
(main's `ProcDefs.v` has it; `pname_cells` stays its own resource per the
§0.21′ amendment — the bridge is a POSITIONAL split, not a conversion).
Add `UtResFits`'s 21 and the port is worth **~100 files and the last of the
rodata shim**.

#### THE CLEAN ROUND, AND THE RED 12

**CLEAN ROUND: 1087 of 1333, RED 12** (from A6.70's 1083/14).  `rm -f
iris/*.{vo,vok,vos,glob}`, the model `.vo` checked fresh against its `.v`
(19:11 over 18:37 — durable-notes' model-aware rule), `kernel-rocq/*.vo`
likewise, one full `-j12 -k`.  **The incremental round immediately before it
agreed on BOTH the count and the red set, file for file.**  No `Admitted`,
no `Axiom` beyond the pre-existing assumed `Link*` contracts.

> **ONE `Abort` OUTSIDE `FastSetSolverTests`, and it is a NAMED WORKLIST
> ENTRY, not a hole:** `UsertrapRes.ut_res_bare_park` (`:1768`), aborted
> deliberately with a paragraph saying why (the M2 park-protocol seam
> above).  It is why `UtResFits` is red, and it is the one place in the
> tree where a red file's cause is a missing lemma rather than a broken
> proof.  Anyone counting `Abort`s should know it is there and why.

**THE RED 12**, with the file count behind each:

| file | behind it | cause |
|---|---|---|
| `WpSconfLock` | 160 | the parked M4 racy-owner-cell entry (untouched, as instructed) |
| `VcGenS` | 85 | six statements + an induction; `:510`'s `wp_csdsp_gpr_s_r_t` is A6.63's diagnosis unchanged |
| `ProofPrintk` | 68 | 2 rodata shim refs — **§0.22′ port** |
| `ProofVirtioDiskRwD` | 66 | the DMA lease lane (A6.70 ruling 3) |
| `UserMemPt` | 46 | the U-mode payer threading |
| `UptWalkPt` | 42 | the U-mode payer threading |
| `UmodeFetch` | 37 | the U-mode payer threading |
| `UtResFits` | 21 | `ut_res_bare_park`'s abort (M2 park protocol) |
| `ProofVirtioDiskIntr` | 15 | the DMA lease lane |
| `ProofSyscall` | 11 | 1 rodata shim ref — **§0.22′ port** |
| `ProofMain` | 5 | the publication gate's missing SITE (this note's headline) |
| `BootCarveMain` | 3 | the boot 25 |

**Two files left the red set and neither was a decision:** `RiscvAdequacy`
(four positional residues) and `ProofFilewrite` (one binder).
`BootShared`/`BootChain` did NOT join the green set — they are behind
`ProofMain` through `LinkMain`, which the dependency direction above
explains.

#### THE QUEUE

1. **The §0.22′ string-tier port** (the cross-lane section above).  Biggest
   measured payoff — `ProofPrintk` + `ProofSyscall` + the last rodata shim
   — the recipe is written on main, and it is a `TsoCtx.v` change so it
   wants a tree with nothing else in flight.  **It is now the only flip in
   the queue, which is what A6.69's one-flip-at-a-time rule was waiting
   for.**
2. **The U-mode walk lane's `S`/payer threading** — 18 sites, five files,
   ~125 behind them, template green and adjacent.  Mechanical.
3. **The publication gate's SITE** — the owner decision above (the barrier
   leaf + moving the publication to `__sync_synchronize`, with
   `SpecKvminithart`'s hart-0/secondary split as its cost).  `ProofMain`,
   `BootChain`, `BootShared` and the boot tail are behind it, and the GATE
   itself is landed and waiting.
4. **`VcGenS`** (85 behind it) — still six statements and an induction;
   re-run A6.65's node-argument grep after it.
5. **The boot 25** in `BootCarveMain` — the VA-tier `_ctx` cell family in
   `BootCarve` plus a `boot_led_ran` premise on thirteen carve lemmas.
   Small payoff (3 files) but it retires 25 of the 29 dangling shim names.
6. **The DMA/virtio lease lane**; **`WpSconfLock`'s M4 memo**; the phys
   notation twin (A6.70 ruling 4, still last).


### A6.72 THE BARRIER LEAF IS WRITTEN AND THE GATE RUNS AT A FENCE — AND
### THE PUBLICATION'S LAST MILE IS A THIRD ARM IN THE REGIME, WHICH THE
### SAME RULING PARKS

Owner ruling of 2026-08-27 (commit `53124a5c`), executed in order.  Items 1
and the gate's own half are **LANDED AND GREEN**; item 2's remaining cost is
measured below and it collides with the ruling's own `WpSconfLock` park.

#### (1) `iris/HartBarrier.v` — A6.5's LEAF, AT LAST

`HartLift.v:139` has named it as missing since the lifting port
("§6's barrier leaf is a SEPARATE rule over the same node, for the proof
that wants the acquire receipt").  It is now three definitions and two
rules:

```coq
  hbar_at / hbar_resume / hbar_at_inv            (* HartLift's F8 style *)

  pub_step (P Q : iProp Σ) :=
    ∀ g : gstate,
      ⌜(own_pub (hart_agent cpu_id) g.(glog) <= g.(gtv) cpu_id)%nat⌝ -∗
      hart_view_lb (g.(gtv) cpu_id) -∗
      gen_heap_interp g.(gmem) -∗ tso_interp_at riscv_eraGS g -∗ P ==∗
      gen_heap_interp g.(gmem) ∗ tso_interp_at riscv_eraGS g ∗ Q

  wp_hart_barrier / swp_hart_barrier :
    mctx C -> hbar_at m = Some bk -> fence_drains bk = true ->
    gen_cert -∗ pub_step P Q -∗ P -∗ ▷ (Q -∗ …) -∗ …
```

**THE SHAPE IS A BUPD, NOT A CALLBACK, and that is the design content.**  A
memory leaf hands the client the bundle inside its own mask-changing fupd
because the client must ANSWER the event (what value was read, was the write
blocked).  A barrier has no answer: the step is deterministic and
state-preserving except for the view.  So the rule does the whole mask dance
itself — advance (`tso_interp_of_advance`), mint (`tso_interp_of_receipt_at`),
bridge to the `gstate` face (`tso_interp_of_at_gs`, A6.1a's bridge, the same
one `HartMStore.wobl_ram_ledger` pays in both directions) — and runs the
client's bupd at the DRAINED view.  Nothing below `gstate` reaches the
client.

#### (2) THE PREMISE IS THE DRAIN, NOT THE LOG TOP — AND A6.70's RECORDED
#### STATEMENT ASKED FOR THE WRONG ONE

This is the tranche's real correction, and it is what makes a FENCE serve at
all.  Under Ztso `fence_post` takes the view to `max tv (own_pub h log)` —
**the author's own last message, NOT the top of the log.**  A6.70's
`kptree_publish` demanded `length glog ≤ gtv cpu_id`, which only an AMO
delivers, and which at the fence would have needed `TsoMemPa.all_own` — a
fact about OTHER agents that no client can hold and that A6.4's boot bracket
exists to state.

**It is not needed.**  What a publisher must show of a byte is that its
timestamp is under the bound, and a byte registered to the context the hart
is RUNNING has exactly two possibilities, which are `TsoMemPa.visibleb`'s own
two arms one tier up:

- **CLEAN**: `llb (ctx_bound_name ξ) t`, so `t ≤ B_ξ ≤ K ≤ gtv cpu_id`
  through the token's own receipt;
- **DIRTY**: an entry of the token's dirty set, and `TsoGhost.dirty_ok` says
  a dirty entry is either under `B_ξ` too **or is THIS HART'S OWN MESSAGE** —
  whose index is under `own_pub`, which the drain has carried the view past.

`CtxPinMint.ctx_phys_ts_own` is that sentence; `own_pub_ge` (the `foldr Nat.max`
lower bound, two lines, kept in the leaf rather than in `TsoMemPa`) is the
only pure step stdpp lacked.

> **AND IT VINDICATES A6.70's `own_context` PARAMETER.**  A6.71 reported the
> token as "threaded, not consumed — not needed at all".  **That was true
> only of the log-top form.**  At the drain the token is exactly what pays
> the bound, so the recorded statement was right and A6.71's amendment 2 is
> WITHDRAWN.  `kptree_publish_bare` is deleted with it.

#### (3) `iris/WpSconfFencePub.v` — `fence rw,rw` AS A PUBLICATION POINT

`swp_barrier_pub` → `swp_execute_FENCE_pub_S` → `wp_fence_pub_s_sconf`,
mirroring `WpSconfCtl`'s fence chain with a `pub_step` threaded through.
Two things worth keeping:

- **rw,rw IS SPELLED CONCRETELY, and a generic pred/succ rule would be
  FALSE.**  Only four of the model's nine barrier kinds drain
  (`fence_drains`: the W→R edges) and the dispatch's fallback arm is not a
  barrier at all.  The nine-way chain is decided here once by
  `fence_rw_bits`: bits [1:0] of both effective sets are `11` at EITHER
  value of the FIOM CSR bit, so the arm is `Barrier_RISCV_rw_rw`.
- **THE LEAF GOES THROUGH `WpSmodeIntr.wp_instr_s_sconf`, NOT
  `WpSconfEngine.wp_instr_s_gen`, AND THAT IS FORCED.**  The generic
  engine's step obligation is stated at a **∀-BOUND hart**, and `pub_step`
  is hart-indexed twice over (its receipt is `hart_view_lb` at THIS hart;
  the token it spends is `own_context`, which A6.64 found is `CpuId`-indexed
  too).  So the publishing leaf takes the lower funnel and collapses the
  binder with `WpNext.wp_next_off_intro` — the `WpSconfSfence` precedent,
  same reason (`tlb ↦ᵣ` there, the token here).  **It therefore requires
  `b = false`**, which costs the one caller nothing: `__sync_synchronize`
  runs in main's boot arm with interrupts off.

> **THE GENERAL RULE, and it is worth carrying past this file:** a leaf that
> consumes a HART-INDEXED resource cannot go through a ∀-hart engine.  The
> tell is `Wrong argument name CID` or a `(CID := CIDn)` that will not
> typecheck; the fix is the lower funnel plus `wp_next_off_intro`, and the
> price is `b = false`.

#### (4) THE LAST MILE: HART 0 MUST **WALK** BEFORE IT DRAINS, AND THE ONLY
#### PLACE THAT CAN LIVE IS A THIRD ARM IN THE REGIME

The ruling's item 2 — publish at `__sync_synchronize`, hart 0's pre-fence
walks at its own UTier table — is right about WHERE the walks discharge and
is blocked on WHERE THE SLOT SAYS SO.  Measured, in this order:

1. **`main()` has no fence between `kvminit()` and `kvminithart()`.**  The
   drain is `__sync_synchronize`, six calls later.
2. **`sfence.vma` cannot serve.**  Re-checked at the model, not from the
   note: `execute_SFENCE_VMA` bottoms out in `flush_TLB` and emits no
   `Interface.Barrier` at all.  A6.41 stands.
3. **No AMO serves either.**  `acquire`'s `amoswap` DOES put the view at the
   log top (`wp_hart_ram_read_excl`), and `kalloc` runs one per allocation —
   but `proc_mapstacks`/`kvmmap` write PTEs AFTER the last `kalloc`, so the
   slots' timestamps are above every AMO in `kvminit`.
4. **So hart 0 crosses `csrw satp` with an undrained view and walks on its
   very next instruction fetch** — which is pin-memo §5.6's problem
   statement verbatim.

`SpecKvminithart` splitting is therefore **not the cost**; it is a
consequence.  The cost is that hart 0's window must hold the EXCLUSIVE table
(`KptTree.tlb_inv_pt`, whose `translateAddr` absorption already exists at
`KptTree.v:1325`) inside its translation slot, and the slot has no arm for
it: `IntrDefs.strans_res_at` is Bare ∨ KPT, and `SRegime.kpt_res_at` is
`tlb_snap_ok ∗ kpt_inv ∗ kpt_creds` — every conjunct persistent, none of
them ownable pre-publication.  **pin-memo §5.6(b) says this in one clause
("hart 0's window discharges at the exclusive tier with `ledger_vis_own`")
and prices it as "`ProofMain`'s publication moves", which is an
underestimate.**

> **THE MEASUREMENT: 14 FILES, ~110 MENTION SITES** —
> `IntrDefs`, `SRegime`, `WpSmodeIntr`, `WpIntrInv`, `WpSconfMem`,
> `SmodeCorePt`, `TrampStepPt`, `UservecExitPt`, `UserretEntryPt`,
> `ProofUart`, `WpPlic`, `WpVirtioDev`, `WpSmodeWfi`, **`WpSconfLock`**.
>
> **AND THE LAST ROW IS THE STOP.**  `WpSconfLock` is the parked M4 entry
> and the same ruling says "do not touch it before the memo lands".  A third
> arm in `strans_res_at` cannot avoid it.  **So item 2's remainder is
> blocked on the M4 memo, not on a decision this lane can take** — and it is
> blocked on the ONE file whose cone (160) makes it the critical path
> anyway, which is consistent rather than accidental.

**THE ALTERNATIVE, PRICED SO IT IS NOT RE-PROPOSED BLIND.**  pin-memo §5.6's
option (a) — make the pin's tie two-armed like `TsoCtx.ledger_vis`
(`B ≤ tv' ∨ h = A`, with `A` the pin's recorded author) — needs no regime
arm, and hart 0's pre-drain walks discharge by store forwarding exactly as
its A6.41 story says.  Its cost is the mirror image: `TsoMemPa.ts_elem`
gains the author, the interp's tie and `pin_ok`'s three laws change (all
under the whole tree), and **every boot PT-construction store site must KEEP
the author fragment `ledger_store_ok` hands back** (`BootCarve` / `TransPt` /
`KptTree`).  The memo recommended (b); (b) is now measured; the choice is
the owner's with both numbers on the table.

#### WHAT THIS UNBLOCKS IMMEDIATELY, AND WHAT IT DOES NOT

The gate and its site are DONE: `kptree_publish` is stated in `pub_step`'s
shape, character for character, so the moment hart 0's window has a home the
publication is one `iApply`.  `ProofMain` stays red on the same line
(`:996`, the `kpt_inv_alloc` call), now for a NAMED and MEASURED reason
rather than for a missing lemma.

#### (5) THE `lock_word` ∃-REPLAY — A LATENT FALSITY, FIXED
#### (`tso-port.md` §0.19′'s ruling; the M4 memo's ruling 4)

Raised from outside this lane and it was real: `WpLock.lock_word lk v` was
`(lk ↦₄ v)` under the section's AMBIENT `CurCtx`, which makes `lock_inv` —
and therefore **`is_lock`, the PERSISTENT HANDLE** — ξ-indexed.  §0.12′'s
park record carries three lock handles (wait / ticks / nextpid) across a
∀-quantified resume context precisely because `is_lock` is a CLOSED TERM, so
the ambient index falsified the park rows outright.  It was latent only
because the `WpSconfLock` cone (160 files, every `is_lock` client and the
park rows among them) is unreached.

**Landed at main's shape:**

```coq
  Definition lock_word (lk : mword 64) (v : mword 32) : iProp Σ :=
    (∃ ξ : CtxId, ctx_word4_pointsto ξ lk (DfracOwn 1) v)%I.
  Lemma lock_word_intro (lk : mword 64) (v : mword 32) : lk ↦₄ v ⊢ lock_word lk v.
```

**MEASURED COST: SIX SITES IN TWO FILES**, all of them the INTRODUCTION leg
(`WpLock` ×5 — `lock_finisher_close`, the Timeless instance and the three
`newlock`-family mints — and `WpLockAt` ×1); `SpecPanic`'s only mention is a
comment.  Every one is `iDestruct (lock_word_intro with "Hword")` in front
of an `iFrame` that was already there.  **The client-facing spellings do not
move**: the creators still take, and the destroyers still hand back,
`lk ↦₄ 0` at the caller's own context.

> **AND ONE HALF OF MAIN'S LEMMA DELIBERATELY DOES NOT PORT.**  Main states
> `lock_word_acc` as a `⊣⊢` and proves the ∃-ELIMINATION with
> `TsoCtxShim.ctx_word4_{to,of}_mem` — sound at SC, where `ctx` is
> degenerate, and **FALSE at this machine**: a cell at an unknown ξ licenses
> no load at ours.  So this tree gets the introduction leg only, and the
> elimination is the M4 racy-owner-cell entry
> (`WpSconfLock.wp_ld_lkcpu_lockopen_gen` is its twin one field over).  The
> note is in the definition's own header so nobody re-derives it by
> accident.

#### THE M4 MEMO IS RATIFIED, AND IT IS THE SUCCESSOR'S BRIEF

`claude-notes/projects/tso-m4-memo.md` (owner, commit `ebcef079`), both
probes green, four rulings — recorded here because the tranche sequences by
cone size and `WpSconfLock` gates **160 files, the largest in the red set**:

1. **DELETE `wp_cld_lkcpu_lockopen_s_sconf`** — zero consumers, both trees.
2. **THE SPLIT.**  Stores + the AMO ride the parked-record/absorb idiom
   (already ratified at §0.18′ / A6.66); the two HOLDER reads ride
   `ledger_vis_own` + `view_lb_0` at `phys_ledger_word` and need **no new
   law** — the held arm already carries the store gate's `ledger_msg_at`
   fragment.  **Only `notheld` gets new kit.**
3. **THE RACY KIT**: `own_last` plus the WINDOW-shaped writer-pin, with all
   three coverage claims (`win_ok`, the writer-pin, `own_last`) in ONE
   `ts_elem` option payload on BYTE 0 — no second ghost map.  The
   byte-keyed form is REJECTED, with the layout computation as the recorded
   reason.  The memo's §6 mechanical list IS the implementation order:
   `TsoMemPa`'s probed lemmas verbatim → `TsoGhost` → the `ts_ok` growth →
   `TsoCtx`'s gates → the `Mobl_ram_exv` S-mode lane (**minding A6.63's
   node-argument rule**) → `WpLock` / `WpSconfLock` / `ProofHolding`.
4. **The `lock_word` ∃-replay** — done above.

**THE ACCEPTANCE TEST IS STATED AND IT IS SHARP:** the exported surface
(`SpecAcquire` / `SpecRelease` / `SpecHolding` / `is_lock` / `locked`) does
NOT move.

> **AND IT INTERLOCKS WITH (4) ABOVE.**  The publication's last mile wants a
> third arm in `strans_res_at`, whose blast radius includes `WpSconfLock`;
> the M4 tranche is the one that opens that file.  So the two are not two
> queue items competing for position — **M4 is the prerequisite of the
> publication's last mile**, and taking M4 by cone size also unblocks the
> boot tail's real cork.  That is why the ordering below puts it where it
> does.

#### THE CLEAN ROUND, THE RED 12, AND THE QUEUE

**CLEAN ROUND: 1089 of 1333, RED 12** (from A6.71's 1087/12).  `rm -f
iris/*.{vo,vok,vos,glob}`, model and `kernel-rocq` `.vo` verified fresh, one
full `-j12 -k`.  The two new files are the whole movement; **the RED SET IS
UNCHANGED, file for file.**

> **AND THE `lock_word` REPLAY'S OWN ACCEPTANCE TEST PASSED SEPARATELY,
> WHICH IS THE MEASUREMENT WORTH KEEPING.**  The incremental round that
> followed it rebuilt `WpLock`'s WHOLE 657-FILE CONE from source and
> produced **exactly the same twelve red files** — no client moved, no
> spelling moved.  A definition inside a persistent handle changing from an
> ambient index to an ∃ is invisible to every consumer, which is the
> property that made the bug latent and the fix cheap.

**THE RED 12**, with the file count behind each, unchanged from A6.71 except
for the causes now being sharper:

| file | behind it | cause |
|---|---|---|
| `WpSconfLock` | 160 | the M4 tranche — **memo ratified, `tso-m4-memo.md`** |
| `VcGenS` | 85 | six statements + an induction (A6.63's diagnosis) |
| `ProofPrintk` | 68 | 2 rodata shim refs — the §0.22′ port |
| `ProofVirtioDiskRwD` | 66 | the DMA lease lane (A6.70 ruling 3) |
| `UserMemPt` | 46 | the U-mode payer threading |
| `UptWalkPt` | 42 | the U-mode payer threading |
| `UmodeFetch` | 37 | the U-mode payer threading |
| `UtResFits` | 21 | `ut_res_bare_park`'s abort (M2 park protocol) |
| `ProofVirtioDiskIntr` | 15 | the DMA lease lane |
| `ProofSyscall` | 11 | 1 rodata shim ref — the §0.22′ port |
| `ProofMain` | 5 | the publication's last mile (§(4) above) |
| `BootCarveMain` | 3 | the boot 25 |

#### THE QUEUE, RE-ORDERED BY WHAT THE MEASUREMENTS SAY

1. **The §0.22′ string-tier port** (A6.71's cross-lane section has the
   recipe).  Independent of everything below, largest payoff of the
   independent items (`ProofPrintk` 68 + `ProofSyscall` 11 + the last rodata
   shim), and it is the only FLIP queued — which is what A6.69's
   one-flip-at-a-time rule was waiting for.
2. **The M4 tranche**, to `tso-m4-memo.md` §6's mechanical order.  Gates
   160 files and is the PREREQUISITE of item 4: the publication's last mile
   needs a third arm in `strans_res_at`, and `WpSconfLock` is in that arm's
   blast radius.  Acceptance test: the exported lock surface does not move.
3. **The U-mode walk lane's `S`/payer threading** — 18 sites, five files,
   ~125 behind them, template green and adjacent (A6.71).  Independent.
4. **The publication's last mile** — the exclusive arm (or pin-memo
   §5.6(a)'s two-armed tie; both priced in §(4) above).  `ProofMain`,
   `BootChain`, `BootShared` and the boot tail behind it.  **The gate and
   its site are landed and waiting**; this is the only piece left.
5. **The boot 25** in `BootCarveMain`: the VA-tier `_ctx` cell family in
   `BootCarve` (built on `CtxKMap`'s landed `_ro_static` three) plus a
   `boot_led_ran` premise on the thirteen carve lemmas, split in lockstep
   with `boot_raw_ran`.  Small payoff (3 files) but it retires 25 of the 29
   dangling shim names.
6. `VcGenS`; the DMA/virtio lease lane; the phys notation twin (last).



### A6.73 THE STRING TIER IS FLIPPED IN THIS TREE TOO — AND THE U-MODE
### LANE TURNS OUT TO BE TWO FILES, NOT THREE, BECAUSE `UmodeFetch` IS
### BINARY-TIER

Three things landed in this tranche: the §0.22′ string port (queue item 1),
the owner's §0.24′ U-mode descoping (arrived mid-tranche, measured and
executed here), and M4's PURE layer.  The M4 Iris lanes are characterised
below with two measurements the memo does not have.

#### (1) THE §0.22′ PORT — MAIN'S SHAPE, PORTED, AND THE OWED ARM IS PAID

Ported, not re-derived, exactly as the port obligation asked: `TsoCtx.v`
declares a SECOND tower (`ctx_string_pointsto ξ a dq s := [∗ list] j ↦ b ∈
cstring_bytes s, ctx_pointsto ξ (pa_add a j) dq b`) over its own sealed
byte, re-declares all four `↦ₛ` spellings at it, and `RiscvPtsto`'s raw
tower stays put.  The law set is the stage-2 word towers' adapted to
strings, `_bytes_agree` deliberately weaker (byte-level — a string may be a
proper prefix of another through an embedded NUL, which only
`PrintkFmt.nonul`, far above `TsoCtx`, rules out), plus one law main does
not have: **`ctx_string_pointsto_forget`**, this tree's shim-tier
projection, stated for the same reason `ctx_word4_pointsto_forget` is.

**THE ONE ARM THIS TREE OWED IS PAID, AND IT WAS SMALLER THAN A6.71
PRICED IT.**  The arm is `ctx_string_all` at `⌜t = 0⌝` — the rodata
literal's mint through the ctx byte's CLEAN-ARM `llb` disjunct — and the
measurement is that **`kernel_data` in this tree was ALREADY minted that
way**, one byte at a time, by `BootCarve` through
`TsoCtx.ctx_pointsto_of_pristine_va_all` (a discarded image byte + its
pristine receipt + `llb_0`, no update modality, no context).  So
`kernel_data_string_all` needs no new mint at all: it keeps `kernel_data`'s
own ∀ and hands it straight through, and the pristine receipts A6.71 said
were "being discarded" were in fact already spent — one tier down.  What
was owed was the STRING-tier spelling of that arm, and it is one lemma:

```coq
  Lemma ctx_string_all_of_pristine (a : Arch.pa) (s : string) :
    string_pointsto a DfracDiscarded s -∗
    ([∗ list] j ↦ _ ∈ cstring_bytes s, pristine_va (pa_add a j)) -∗
    ctx_string_all a DfracDiscarded s.
```

recorded beside the byte mint for a producer that holds raw image bytes and
their receipts directly.  `kernel_data_string_all` does not go through it,
and saying so in the file is the point: **the timestamp-0 story JUSTIFIES
the derived form; it is never the meaning of `↦ₛ`.**

**THE SEAM COUNT WENT TO ZERO ON THE RODATA CHAIN.**
`KernelDataInv.kernel_data_string`'s junk witness (`MkCtxId inhabitant
inhabitant`) and its `ctx_pointsto_forget` crossing are both gone;
`kernel_data_string` is now `kernel_data_string_all` instantiated at
`cur_ctx`, statement character-identical.  `ProofPrintk`'s `pk_str_byte`
and `pk_digits_data` crossings ceased to exist (the string's byte IS the
load leaf's ctx slot, in BOTH directions — which a shim crossing never
was), and `ProofSyscall`'s hand-rolled `sysc_name_addr` / `sysc_pname_app`
retired into `ProcDefs`'s accessor family
(`pname_addr` / `pname_pad` / `pname_bytes_split` / `pname_wf_cstring` /
`pname_cells_borrow` / `pname_cells_return`), with kfork's `safestrcpy`
source coming out of the borrow and `ssc_src_ok` discharged from the
string's OWN NUL (`ProofKforkParts.kfk_src_of_string` /
`kfk_src_ok_of_string`).

`WpLock.lock_name` and `SleepLock.sl_name` carry `ctx_string_all`;
**`is_lock` / `is_sleeplock` are character-identical and still CLOSED**, so
the park rows did not move.  `SpecInitlock` / `SpecInitlockWrapper` /
`SpecInitsleeplock` take the ∀ form and their callers mint with
`kernel_data_string_all`.

**FALLOUT: 42 FILES, AND IT IS MAIN'S FALLOUT PLUS EXACTLY ONE.**  Main's
44-file change applies here almost verbatim — 41 of its hunks land, three
(`ProofSysRead` / `ProofSysSbrk` / `ProofSysWrite`) are comment-only fixes
to a `Require TsoCtxShim` line this tree no longer has — and main's four
error classes reproduce file for file.  The one ADDITION is
**`ProofProcdumpLoop`**, a binder-less `*Res` section whose `pdl_pkastr`
speaks `pk_desc_res` — the class-1 fix (`Context \`{XI : CurCtx}.`, every
statement text unchanged).  Main did not need it because its copy already
carried the binder; **that is the only divergence the port found across 42
files**, which is the strongest evidence yet that porting main's landed
shape beats re-deriving it.

#### (2) §0.24′ — THE U-MODE SPLIT, MEASURED, AND IT MOVES THE QUEUE

The owner's ruling (commit `dc36835c`) reduces the U-mode lane: the GENERIC
user-mode safety tier stays, the SPECIFIC-BINARY tier (init/sync/sh/echo
certificates and machinery consumed only by them) is deferred.  Measured
before threading anything, from `iris/.CoqMakefile.d`:

**THE TIER IS ALREADY DEPENDENCY-CLOSED, AND `_CoqProject` ALREADY NAMES
IT.**  Seed the reverse-dependency closure with `{UProof*, USpec*, UCode*}`
(26 files) and iterate "every consumer of a descoped file is itself
descoped" to a FIXPOINT: it terminates at **41 iris files (+ 4 `user-rocq`
symbol files)** — and that set is *character for character* the block
`_CoqProject` already delimits as `# --- BEGIN verified Umode WP tier ---`.
So the reverse-dependency check the ruling asks for passes by construction:
**no file outside the block consumes any file inside it**, and
`SystemAdequacy` depends on NONE of them.  The descoping is therefore a
comment sweep over a block that was written to be swept — the Aug-19
precedent replayed, with the ruling recorded in place.

> **THE RESULT THAT MOVES THE QUEUE: `UmodeFetch` IS IN THE BINARY TIER.**
> All 37 of its consumers are `UProof*`/`USpec*`/`UCode*`/`Umode*`/
> `WpUmode*`, and its own header says what it is — *"the CONCRETE-byte
> instruction fetch of the VERIFIED user-mode tier"*.  The GENERIC tier's
> fetch composer is the separate `UserFetchPt.v`, which sources from
> `udata_own` and hands out an EXISTENTIAL word.  **So the U-mode payer
> threading's frontier is TWO files — `UptWalkPt` and `UserMemPt` — not
> three, and the ~125-file estimate behind them was inflated by the binary
> cone.**  The generic remainder behind those two is `ProofUser`,
> `UserMem*`/`UserFetchPt`/`Userret*`/`Uservec*`, `LinkMain`, `BootChain`,
> `BootShared`, `FsAdequacyImg` and `SystemAdequacy`.

The threading sites themselves are unchanged in kind — `UserMemPt:427` is a
raw `↦ₚ` store gate fed a `ctx_phys_pointsto`, `UptWalkPt:679` is the
`own_context` payer missing from a `translateAddr` obligation — and they
stay on the queue at their generic sites.

#### (3) M4: THE PURE LAYER IS IN, AND TWO THINGS THE MEMO DID NOT MEASURE

`TsoMemPa.v` §12/§12b carries both probes **verbatim** — `own_last`,
`writer_pin` and their three maintenance lemmas; `racy_read_split`,
`racy_read_not_mine`, `racy_read_own`; `win_ok`, `find_top`,
`read_down_win`, `find_top_spec`/`_max`, `racy_read_window`, `wpin`,
`racy_read_window_pin`, `lkcpu_not_mine` — with the byte-layout
computation recorded in the header as the reason the kit is WINDOW-shaped
(the forgery it rules out is spelled: hart 1 assembles `0x80012468` from
hart 3's byte 0 and hart 2's byte 1, both legal writes by their own
authors).  Ruling 1 (delete `wp_cld_lkcpu_lockopen_s_sconf`) is deferred to
the tranche that re-proves the file, since deleting a leaf out of a red
file buys nothing.

**MEASUREMENT A — THE MEMO'S "ONLY `notheld` GETS NEW KIT" IS TRUE OF THE
LAW AND FALSE OF THE LEAF.**  All three surviving reads go through
`WpSconfMem.wp_load_s_sconf_au`, whose datum premise is
`wordw_pointsto width ea dqm v` = **the CTX word tower at `cur_ctx`**
(`wordw8_ctx` is the identity), discharged by the Local lemma
`wordw_pointsto_load_c`, which additionally consumes `own_context`.  A cell
that lives in a SHARED invariant cannot be at the reader's ambient ξ, and
`lk_cpu_res`'s `∃ ξ` is exactly the admission of that.  So the memo's
"`lk_cpu_res` at `phys_ledger_word`" is not a reshape of one definition —
**it forces a PHYS-DATUM sibling of the load AU**, `wp_load_s_sconf_au_phys`,
identical to the existing one except that the one `iAssert` that runs
`wordw_pointsto_load_c` runs `ledger_read_bytes_vis_ok` (holder) or the new
`ledger_read_racy_ok` (`notheld`) instead.  It is CHEAPER in one respect
worth recording: the phys form consumes no `own_context`, so A6.64's
forty-argument hazard has one fewer payload spelling to keep in agreement —
but A6.63's node-argument rule still applies to the node it passes.

**MEASUREMENT B — THE `_exv` LANE IS SHALLOWER THAN §6 SAYS, BECAUSE THE
HART TIER ALREADY HAS IT.**  `HartEvents.wp/swp_hart_ram_read_plain_ex`
(A6.51) is ALREADY the value-after-view shape the racy read needs —
`⌜∀ tv' ≥ tv, ∃ w, tso_read_bytes … w ∧ P w⌝`, with the value coming back
FROM THE STEP together with `⌜P w⌝` and the view receipt — and
`PtTreeAdue.v:985–1006` is a worked call site of it.  What is missing is
only the S-mode wrapper tier:

```coq
  Mobl_ram_exv (width) (pa) (P : mword (8*width) -> Prop) (R : iProp Σ)
    (* [Mobl_ram_ex]'s body with [∃ bytes] moved INSIDE the [∀ tv'] and
       the resource made value-independent *)
  swp_read_ram_node{1,2,4,8}_exv, swp_read_ram_node_w_exv
  wp_load_s_sconf_au_exv     (* = wp_load_s_sconf_au through
                                swp_execute_LOAD_S_gen_ex, which already
                                takes its node AND its obligation as
                                arguments — no new engine *)
```

`Mobl_ram_ex` itself must NOT be used for this: its `∃ bytes` sits outside
the `∀ tv'`, i.e. it names one word good at every reachable view, which is
`tso-pin-memo.md` §0's refuted shape and is false of any cell another hart
writes.

**WHAT REMAINS OF M4, in the memo's order, with the above folded in:**
`TsoGhost`'s `ts_elem` window payload on byte 0 (`win_ok` + the
window writer-pin + the per-agent `own_last`; all three are COVERAGE CLAIMS
over the log, so `tso-pin-memo.md` §3 puts them in the interp, never in the
invariant) → `ts_ok`'s growth → `TsoCtx`'s `ledger_read_racy_ok` and the
author premise on `ledger_store_pin_ok` (the frame side condition
`pm_tid m = h → msg_byte m a = None` is discharged from `ledger_store_ok`'s
own `auth` argument, which is already there) → the `_exv` lane above → the
phys-datum AU of measurement A → `WpLock`'s `lk_cpu_res` at
`phys_ledger_word` plus the held arm's per-byte `ledger_vis` residue (the
`ledger_msg_at` fragment `ledger_store_ok` hands back) → `WpSconfLock`
(**3 red sites, not 1** — `lock_word`'s ∃-replay turned the two
`wp_clw_lockopen_*` leaves red exactly as the memo predicted; the file's
first error is now `wordw_claim_of` refusing `lock_word lk w`) →
`ProofHolding`'s 2 call sites.  `lock_claims`' surviving
`TsoCtxShim.ctx_word_of_mem` crossing is on the same path and dies with it.

#### THE CLEAN ROUND, THE RED SET, AND THE QUEUE

**CLEAN ROUND: 1088 of 1296, RED 9** — `rm -f iris/*.{vo,vok,vos,glob}`,
`CoqMakefile` regenerated from the descoped `_CoqProject`, the model `.vo`
verified fresh against its `.v` (19:11 over 18:37 — durable-notes' model-aware
rule) and `kernel-rocq`'s likewise, one full `-j12 -k`.  No `Admitted`, no
`admit`, no new `Axiom`; the ONE `Abort` outside `FastSetSolverTests` is still
`UsertrapRes.ut_res_bare_park` (`:1768`), the named worklist entry.

**AND THE CONFIRM ROUND AGREES FILE FOR FILE:** an incremental `-j12 -k`
immediately after it recompiled **exactly nine targets — the nine red ones —
and failed on all nine**, i.e. no green file needed rebuilding and the red
set is identical.  That is the two-consecutive-rounds check A6.72 ran, and
it also rules out the mtime artefact durable-notes warns about (a
"Nothing to be done" round proves nothing; a round that rebuilds precisely
the failures proves the rest is real).

**THE GREEN COUNT AND THE RED SET BOTH RECONCILE EXACTLY, which is the
check worth stating:** A6.72's 1089 green, minus the 3 rows the descoping
removed that were already GREEN (`UmodeArith`, `UmodeCap`, `UmodeMem`), plus
`ProofPrintk` and `ProofSyscall` = **1088**.  Red 12 − `ProofPrintk` −
`ProofSyscall` − `UmodeFetch` (descoped) = **9**.  Nothing else moved in
either direction, in either direction of the port.

> **THE DENOMINATOR IS 1296 AND IT IS NOT 1333 − 41; SAY SO RATHER THAN
> RECONCILE IT.**  Measured: `iris/` holds 1338 `.v` files, `_CoqProject`
> listed 1337 of them (the omission is `SystemAssumptions.v`, deliberate —
> durable-notes' `make audit` entry) and now lists 1296.  A6.72's stated
> denominator of 1333 is four short of what this workspace measures, and
> nothing in this tranche can account for the difference; treat 1296/1337
> as the numbers of record and A6.72's 1333 as a count taken some other
> way.

**SHIM LEDGER: files naming `TsoCtxShim` 31 → 28, qualified uses 40 → 36** —
`KernelDataInv` and `ProofSyscall` lost it entirely, `ProofPrintk` lost its two
rodata crossings AND its now-dead `Require`.  **No shim use was ADDED**, so
this port, like main's, is a tier flip that pays nothing for what it buys.
**25 of the 36 remaining uses are in `BootCarveMain` alone** — which is why the
boot 25 is worth its 3-file payoff.

**THE RED 9**, with the cone behind each *recomputed after the descoping*:

| file | behind it | cause |
|---|---|---|
| `WpSconfLock` | 160 | the M4 tranche — §(3) above is the brief |
| `VcGenS` | 85 | six statements + an induction (A6.63's diagnosis) |
| `ProofVirtioDiskRwD` | 66 | the DMA lease lane (A6.70 ruling 3) |
| `UserMemPt` | 23 | the U-mode payer threading (**was 46**) |
| `UtResFits` | 21 | `ut_res_bare_park`'s abort (M2 park protocol) |
| `UptWalkPt` | 19 | the U-mode payer threading (**was 42**) |
| `ProofVirtioDiskIntr` | 15 | the DMA lease lane |
| `ProofMain` | 5 | the publication's last mile (A6.72 §(4)) |
| `BootCarveMain` | 3 | the boot 25 |

> **AND THE DESCOPING'S PAYOFF IS IN THAT TABLE, not just in the row count.**
> The U-mode lane was priced at "~125 files behind three frontier files"; after
> §0.24′ it is **42 behind two**, and `UmodeFetch`'s 37 left the port with it.
> A6.71's estimate was not wrong — it was measuring the binary cone.

**WHAT THE ROUND ALSO CAUGHT, and it is `make -k`'s recorded trap:** a
failing target has its `.glob` deleted but **its stale `.vo` left in
place**, so a green/red survey done with `test -f *.vo` reads a file that
turned red in THIS round as green.  `ProofProcdumpLoop` was that file.  Any
number in this note is from the LOG, and the closing one is from a clean
tree.

#### THE QUEUE, AS THE MEASUREMENTS NOW LEAVE IT

1. **The M4 tranche** — §(3) above is its brief, and it now has the two
   missing measurements (the phys-datum load AU; the `_exv` lane's real
   depth).  Gates `WpSconfLock`'s cone and is the prerequisite of item 3.
2. **The U-mode payer threading at its GENERIC sites** — `UptWalkPt` and
   `UserMemPt` only, per §(2).  Independent.
3. **The publication's last mile** — the third `strans_res_at`/`kpt_res_at`
   arm (or pin-memo §5.6(a)'s two-armed tie); the gate and its site are
   landed and waiting.  Behind M4.
4. **The boot 25** in `BootCarveMain` (**25 of the tree's 36 remaining
   qualified shim uses are in that one file** — the single largest shim
   concentration left, which is what makes a 3-file payoff worth taking).
5. `VcGenS`; the DMA/virtio lease lane; `UtResFits`' park protocol; the
   phys notation twin (last).


### A6.74 THE `_exv` LANE IS BUILT AND GREEN — AND THE WINDOW PAYLOAD
### CANNOT LIVE ON BYTE 0, WHICH IS A CORRECTION TO M4 RULING 3, NOT A
### DETAIL

Continuing the M4 Iris half on the coordinator's ratification of A6.73's
two measurements (commit `d6c857b0`).  Item (B) is LANDED; item (A) is
designed and priced below; and the step before both — the `ts_elem` window
payload — turned out to have a maintenance obligation the memo's shape
cannot discharge, which is the entry worth reading first.

#### (1) LANDED: `Mobl_ram_exv` AND THE FOUR `_exv` NODES

`HartSMem.v` gains `swp_read_ram_node{1,2,4,8}_exv`, `Mobl_ram_exv` and the
width dispatcher `swp_read_ram_node_w_exv`.  The obligation is
`Mobl_ram_ex`'s body with the `∃ bytes` moved INSIDE the `∀ tv'` and the
resource made value-INDEPENDENT:

```coq
  Definition Mobl_ram_exv (width : Z) (pa : mword 64)
      (P : mword (8 * width) -> Prop) (R : iProp Σ) : iProp Σ :=
    (∀ σ img log tv V, ⌜V (hart_agent cpu_id) = tv⌝ -∗ mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
        ⌜forall tv', (tv <= tv')%nat -> (tv' <= length log)%nat ->
           exists bytes, tso_read_bytes img log (hart_agent cpu_id) tv' pa
                           (Z.to_N width) bytes /\ P bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ ∗ tso_interp_of … ∗ R))%I.
```

`R` is not value-indexed on purpose: a racy leaf's continuation wants
`⌜P c⌝ ∗ T`, and a value-indexed `Rr` would have to be chosen before the
step it is about.  A6.73's measurement B held exactly — the cost was the
statements: `HartEvents.swp_hart_ram_read_plain_ex` is already this shape
one tier down, so each node is one `Ltac` invocation.

> **TWO `Ltac` PAPER CUTS, both of which report something else, and both
> already in the file's neighbourhood as a precedent.**  (i) A name a
> tactic introduces inside an `Ltac` body is NOT reachable by its literal
> spelling later in that body — `iIntros (tvn w) … rewrite (Hres w)` fails
> with *"The reference w was not found"*, which reads like a missing
> lemma.  `let bs := fresh "bs" in` at the top is the fix, and it is why
> `node_read_ex` was written that way.  (ii) The rule's predicate `P` must
> be passed EXPLICITLY (`node_read_exv … P`): left as `_` it stays an evar
> that the goal never determines, and the failure surfaces four tactics
> later as `No such assumption` on a pure side goal.  Prefer anonymous
> intro patterns plus `assumption` over named ones inside an `Ltac`.

Validated: the file compiles standalone, and the round over its cone leaves
**the same nine red files, unchanged** — the lane is purely additive.

#### (2) THE CORRECTION: THE WINDOW PAYLOAD IS PER-BYTE, BECAUSE BYTE 0'S
#### MAINTENANCE OBLIGATION IS UNDISCHARGEABLE

The M4 memo's ruling 3 puts all three coverage claims "in ONE `ts_elem`
option payload on BYTE 0 — no second ghost map", and §8 adds that
`win_ok`'s maintenance "is a per-store side condition of the same shape as
the pin's (`vnew ∈ Sv`)".  **The first half is right about the ghost map
and wrong about the byte; the second half is false, and the two are the
same fact.**

`win_ok` says every timestamp writes the WHOLE window at `a` or none of it.
Hang it on byte 0's element and its FRAME arm — the arm every store in the
tree that is not the lock's must take — needs

> the appended message does not write SOME of `a … a+n-1` while missing
> byte 0,

which is a fact about a SET of addresses.  The pin's frame arm is free
because `pin_ok_app_frame`'s side condition is `msg_byte m a = None`, i.e.
`a ∉ dom Pnew`, and `ledger_store_ok` knows that per address.  It does NOT
know disjointness from a window whose extent lives inside the interp's
existential `TM`, and no caller can state it: the window's addresses are
not visible from the store site.  Carried honestly, it becomes a premise on
`ledger_store_ok` — i.e. on every store in the tree — which is exactly the
"exemption in a definition is a premise on every consumer" trap
durable-notes prices.

**THE FIX MAKES THE OBLIGATION PER-BYTE AGAIN, and it costs nothing else.**
Put the payload on EVERY byte of the window and state the writer-pin AT
THAT BYTE but ABOUT the window:

```coq
  Record ts_win := TsWin {
    tw_base : Arch.pa;  tw_n : nat;  tw_j : nat;      (* this byte's offset *)
    tw_z    : nat -> bv 8;                            (* the CLEAR word *)
    tw_cp   : agent -> nat -> bv 8;                   (* each author's word *)
    tw_own  : agent -> option nat;                    (* per-agent own-last *)
  }.

  Definition win_ok1 img log (a : Arch.pa) (W : ts_win) : Prop :=
    a = pa_add (tw_base W) (tw_j W) /\ (tw_j W < tw_n W)%nat
    (* (1) ANY message touching THIS byte writes the WHOLE window, with a
       word allowed for its author.  Frame condition: [msg_byte m a = None]
       -- the pin's, exactly. *)
    /\ (forall i m, log !! i = Some m -> is_Some (msg_byte m a) ->
          (forall k, (k < tw_n W)%nat ->
             msg_byte m (pa_add (tw_base W) k) = Some (tw_z W k))
          \/ (forall k, (k < tw_n W)%nat ->
             msg_byte m (pa_add (tw_base W) k) = Some (tw_cp W (pm_tid m) k)))
    (* (2) the era image covers the window: [win_ok]'s [t = 0] arm *)
    /\ (forall k, (k < tw_n W)%nat -> is_Some (img !! pa_add (tw_base W) k))
    (* (3) per agent, at THIS byte *)
    /\ (forall h t, tw_own W h = Some t ->
          (t <= length log)%nat
          /\ (forall tv, visibleb h tv log t = true)
          /\ log_byte img log t a = Some (tw_z W (tw_j W))
          /\ own_last log h a t).
```

**AND `win_ok` IS THEN A THEOREM, NOT A CONJUNCT.**  From `n` copies of
`win_ok1` agreeing on `(base, n, z, cp, own)`, the window's all-or-none
property follows: at `t = 0` by (2); at `t = S i` because if the message
writes ANY window byte `k`, byte `k`'s own copy of (1) forces it to write
all of them; above the log both arms are `None`.  `wpin` is byte 0's copy
of (1) verbatim.  So `TsoMemPa.win_ok` / `wpin` stay exactly as §12b
states them and become the ASSEMBLY step the reader runs, which is where
they belong — the reader holds all `n` bytes (`phys_ledger_word` is
eight `phys_ledger`s) and the lock's resource is what asserts the `n`
copies agree.

> **THE GENERAL RULE, and it is the third time this port has paid for it:**
> *a coverage claim's home is decided by its FRAME condition, not by its
> content.*  `tso-pin-memo.md` §3 put these claims in the interp rather
> than an invariant because they quantify over the log; this section says
> WHERE in the interp — at the finest key whose frame arm the store gate
> can already discharge.  A claim about `n` addresses parked on one of them
> is a claim no framing store can pay.

Cost of the corrected shape versus the memo's: identical ghost surface
(one option payload in the existing `ts_elem`, no second map), `n` elements
updated per lock store instead of one — and `ledger_store_ok` already
updates every address of `Pnew` coherently, so that is free.  The lock's
own store gate (`ledger_store_win_ok`, the twin of `ledger_store_pin_ok`)
is what preserves the payload across the eight bytes it writes.

#### (3) ITEM (A), THE PHYS-DATUM SIBLING AU — DESIGNED, AND ITS SHAPE IS
#### A6.47 RULING 1'S AGAIN

`wp_load_s_sconf_au`'s datum is `wordw_pointsto` (the CTX word tower at
`cur_ctx`) and its obligation is discharged by the Local
`wordw_pointsto_load_c`, which also consumes `own_context`.  The sibling
must not simply swap in `phys_ledger_word`, because the three lock reads
discharge by three DIFFERENT routes (holder = `ledger_vis_own` +
`view_lb_0`; `notheld` = the racy kit; free-path = neither).  **So the
leaf takes the ledger resource as a PARAMETER and one gate premise:**

```coq
    (Res : iProp Σ)                        (* whatever the client holds *)
    (∀ g, gen_heap_interp g.(gmem) -∗ tso_interp_at riscv_eraGS g -∗ Res -∗
       ⌜∀ tv', (g.(gtv) cpu_id <= tv')%nat ->
          ∃ w, tso_read_bytes g.(gimg) g.(glog) (hart_agent cpu_id) tv'
                 pa (Z.to_N width) w ∧ P w⌝) ->
```

— one leaf, both routes, nothing downstream knowing which, exactly as
A6.47 ruling 1 did for `ledger_read_vis_ok`.  **Nothing below `gstate`
reaches the client** (A6.72's barrier-leaf rule); the `tso_interp_of` ↔
`tso_interp_at` step stays inside, on `tso_interp_of_at_gs`.  Mind
A6.63's node-argument rule and A6.64's `CIDw` binder: this is the file and
the sentence where the 35/60/57-minute elaborations happened, and the phys
form has one FEWER payload spelling to keep in agreement (it consumes no
`own_context`), which helps rather than hurts.

> **AND A THIRD KIT ITEM THE MEMO DOES NOT LIST, found while sizing this.**
> The memo's site table marks `wp_clw_lockopen_s_sconf` (the free-path word
> read) "receipt in hand? no" and treats that as costing nothing.  At the
> real machine "no receipt" still owes a READ RESULT: the leaf must exhibit
> `∃ w, tso_read_bytes … w` at every reachable view even when it concludes
> nothing about `w`.  That is payable, and cheaply — `read_down` bottoms
> out at the era image and the image covers RAM — but it is a gate that
> does not exist: call it `ledger_read_any_ok`, `P := fun _ => True`, from
> `addr_is_ram` plus the interp's image coverage.  Both "any value" leaves
> (`wp_clw_lockopen_s_sconf`, and `wp_cld_lkcpu_lockopen_s_sconf` if it
> were not being deleted) need it, and it is the honest reason ruling 1's
> deletion is worth taking: it removes one of the two customers.

#### THE NUMBER, AND WHAT IT PROVES ABOUT THE LANE

**1088 of 1296, RED 9 — UNCHANGED from A6.73**, over a round that rebuilt
`HartSMem`'s 290-file cone from source.  That is the acceptance test for an
additive lane and it passed exactly: new statements, no client movement, no
red-set movement in either direction.

#### HANDOFF: M4'S REMAINING ORDER, WITH THE TWO CORRECTIONS FOLDED IN

The coordinator's order stands; §(2) and §(3) above replace two of its
steps' contents, and one step is added.

1. **`TsoMemPa`'s `ts_win` / `ts_pay` and `ts_ok`'s growth** — §(2)'s
   PER-BYTE shape, not byte 0's.  `ts_elem` becomes `nat * ts_pay` with
   `ts_pay := TsPay { tp_pin : option (byteset * nat); tp_win : option
   ts_win }`, which keeps `e.1` (~20 positional sites) and moves only
   `e.2`; `(t, None)` becomes `(t, ts_pay_none)`.  `ts_ok` gains a THIRD
   bullet (`∀ W, tp_win e = Some W -> win_ok1 img log a W`) — LAST, per
   durable-notes' new-conjunct rule, so the ~20 destructurings do not move.
   The assembly lemma (`n` copies of `win_ok1` ⟹ `win_ok` + `wpin`) is the
   only genuinely new proof and §(2) has its argument in full.
   Sites: `TsoMemPa`, `RiscvPtsto`, `RiscvExec`, `TsoCtx`, `CtxPinMint`,
   `DiskInv` — the pin memo's measured six.
2. **`TsoCtx`'s gates**: `ledger_read_racy_ok` (the `n`-copy assembly plus
   `lkcpu_not_mine`, then the byte-to-word step: a differing byte at `k`
   makes the assembled word differ, via `bv_eq_of_bytes`);
   `ledger_read_any_ok` (§(3)'s footnote); `ledger_store_win_ok` (the
   payload-preserving twin of `ledger_store_pin_ok`); the author premise on
   `ledger_store_pin_ok`, whose side condition `pm_tid m = h ->
   msg_byte m a = None` comes straight off `ledger_store_ok`'s existing
   `auth` argument.
3. **The phys-datum sibling AU** — §(3)'s parametric-`Res` shape.
4. **`WpLock`'s `lk_cpu_res` at `phys_ledger_word`** plus the held arm's
   per-byte `ledger_vis` residue (the `ledger_msg_at` fragment
   `ledger_store_ok` already hands back), and the eight-copy `ts_win`
   agreement the reader assembles from.
5. **`WpSconfLock`**: delete the dead leaf; the two holder reads on
   `ledger_vis_own` + `view_lb_0`; `notheld` on the racy kit; the free-path
   read on `ledger_read_any_ok`; the stores/AMO on the parked record.
   `lock_claims`' surviving `TsoCtxShim.ctx_word_of_mem` dies here.
6. **`ProofHolding`**'s 2 call sites, statements unchanged.

**ACCEPTANCE, unchanged:** `SpecAcquire` / `SpecRelease` / `SpecHolding` /
`is_lock` / `locked` / `lock_openable` do not move, and `WpSconfLock`'s
160-file cone opens.


### A6.75 THE GHOST SURGERY IS LANDED AND THE RACY GATE IS PROVEN — AND
### THE GATE TURNS OUT TO NEED NO RECEIPT AND NO VIEW PREMISE AT ALL

Executing the coordinator's ratified order (commit `cd07c1db`).  Steps 1 and
the READ half of step 2 are LANDED AND GREEN; the store half, the sibling
AU and the leaf tier are the handoff.

#### (1) STEP 1: THE `ts_elem` WINDOW PAYLOAD, PER BYTE

`TsoMemPa` §12c/§12d.  `ts_elem` is now `nat * ts_pay` with

```coq
  Record ts_pay := TsPay { tsp_pin : option (byteset * nat);
                          tsp_win : option ts_win }.
  Record ts_win := TsWin { tw_base; tw_n; tw_j; tw_z; tw_cp; tw_own }.
```

and `ts_ok` grew a THIRD conjunct (`∀ W, tsp_win e.2 = Some W ->
win_ok1 img log a W`), LAST per durable-notes' new-conjunct rule.  **`e.1`
did not move**, which is why the ~20 positional projections of the interp
did not either: the payload is a RECORD, so the two optional arms got NAMES
instead of positions and only `e.2`'s spelling changed.

**MEASURED CHURN: 33 literal sites across five files** (`TsoCtx` 28,
`RiscvAdequacy` 4 + 2 tie proofs, `RiscvPtsto` 1, `CtxPinMint` 1), plus
four hand-written `ts_ok` proofs that gained a `split_and!` and one arm.
The pin memo's estimate of "six files" was right.

> **AND THE FRAME ARM CAME OUT DEFINITIONAL, WHICH IS THE WHOLE POINT OF
> A6.74 §(2).**  `win_ok1_app_frame` needs `msg_byte m a = None` and
> NOTHING ELSE — no premise about the rest of the window — so the three
> framing tie proofs in `TsoCtx` each took one extra line of exactly the
> pin's shape.  A store that wrote *some* of the window and not this byte
> would not falsify the claim, it would drop it (that byte's element is in
> `dom Pnew` and gets replaced), and it cannot happen anyway:
> `ledger_store_ok` demands FULL ownership of every byte it writes, so a
> partial writer would have to own a window byte the lock's invariant is
> holding.  **Ownership is what makes the per-byte shape work, and that is
> the sentence the byte-0 shape had no analogue of.**

> **ONE NAME COLLISION, and it reports two files away.**  The obvious field
> names `tp_pin` / `tp_win` collide with `HartTp.tp_pin` (the hart's
> register-file pin, used tree-wide).  A record field shadows it in every
> importer, and the failure surfaces in `IntrDefs` as *`The term "m" has
> type "regfile" while it is expected to have type "ts_pay"`* — which reads
> like a broken `gpr_file` and is a naming clash.  Fields are `tsp_*`, and
> the definition says why.

#### (2) STEP 2, READ HALF: `ledger_read_racy_ok`, AND ITS PREMISE LIST IS
#### THE RESULT

```coq
  Definition phys_ledger_win (a : Arch.pa) (dq : dfrac) (v : bv 8) (t : nat)
      (W : ts_win) : iProp Σ :=
    (phys_pointsto a dq v ∗ a ↪[ts_name]{dq} (t, ts_pay_win W))%I.

  Lemma ledger_read_racy_ok (g : gstate) base n dq f ts z cp own t :
    (0 < n)%nat ->
    own (hart_agent cpu_id) = Some t ->
    (exists k, (k < n)%nat /\ z k <> cp (hart_agent cpu_id) k) ->
    (forall h', h' <> hart_agent cpu_id ->
       exists k, (k < n)%nat /\ cp h' k <> cp (hart_agent cpu_id) k) ->
    tso_interp_at riscv_eraGS g -∗
    ([∗ list] j ∈ seq 0 n,
       phys_ledger_win (pa_add base j) dq (f j) (ts j)
         (TsWin base n j z cp own)) -∗
    ⌜forall tv, exists k, (k < n)%nat /\
       tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv (pa_add base k)
       <> Some (cp (hart_agent cpu_id) k)⌝.
```

**READ THE PREMISES FOR WHAT IS NOT THERE: no `view_lb`, no bound `B`, no
`g.(gtv)`.**  The conclusion holds at EVERY view — not at every view above
something — because `read_down` scans DOWN from the top and `visibleb_own`
makes the reader's own message visible at every view.  A receipt could not
improve it and none is needed.  That is the sharpest available statement of
why the racy kit is **not a weakened pin**: the pin's conclusion is
`∀ tv' ≥ B`, and this one has no `B` to have.

The word form (`ledger_read_racy_word_ok`) is the byte-to-word step the
leaf consumes: one differing byte makes the assembled word differ, stated
at a general `bv m` so the step is done once.  Both compiled first try over
the assembly theorems.

#### (3) THE THIRD KIT ITEM, AND IT IS *PURE*

`ledger_read_any_ok` consumes **no resource at all**:

```coq
  Lemma ledger_read_any_ok (g : gstate) (a : Arch.pa) (b : bv 8) :
    g.(gimg) !! a = Some b ->
    forall tv, exists c, tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv a
                         = Some c.
```

over the new `TsoMemPa.tso_read_total` (`read_down` bottoms out at
timestamp 0, visible at every view by `visibleb_below`, and that is the era
image).  **That is the honest statement of "no evidence"**: the free-path
leaf's obligation is discharged by the machine's own totality over the
image, not by anything the client owns.  `ledger_win_img_cover` supplies
its premise for a WINDOWED cell out of `win_ok1`'s conjunct (2) — so the
free-path read of `lk->cpu` costs nothing extra.

> **AND IT LEAVES ONE NAMED OBLIGATION.**  The free-path read of the lock
> WORD (`lk`, not `lk->cpu`) has no window payload, so its image coverage
> has no supplier yet.  Either give the lock word a (degenerate,
> `tw_n = 4`) window payload, or add an image-coverage conjunct to the
> lock's own claim.  It is a premise, not a design question — but it is
> not free, and it is the one thing between `ledger_read_any_ok` and
> `wp_clw_lockopen_s_sconf`.

#### THE NUMBER

**1088 of 1296, RED 9 — UNCHANGED across all of it**, over rounds that
rebuilt `TsoMemPa`'s whole cone twice from source, and a confirm round that
recompiled **exactly the nine red targets and failed on all nine**.  No `Admitted`, no
`admit`, no new `Axiom`; the one `Abort` is still
`UsertrapRes.ut_res_bare_park`.  Shim ledger unchanged at 36 qualified uses
in 28 files.  **A ghost element grew a second optional payload, a tie grew
a third conjunct, and not one client moved** — which is the acceptance test
the pin memo set for this kind of change, passed a second time.

#### HANDOFF: WHAT IS LEFT OF M4, IN ORDER

1. **`TsoCtx.ledger_store_win_ok`** — the payload-preserving twin of
   `ledger_store_pin_ok`, for the lock's own 8-byte `sd`.  It writes all
   `n` bytes, so it must (a) re-establish `win_ok1`'s conjunct (1) for the
   new message from the store's own value, (b) update `tw_own` for the
   AUTHOR to `S (length glog)` (`own_last_app_self`) and leave every other
   agent's entry alone (`own_last_app_frame`, side condition off the
   store's `auth`), and (c) carry (2) unchanged.  The author premise on
   `ledger_store_pin_ok` is the same `auth` argument and comes with it.
2. **The phys-datum sibling AU** — A6.74 §(3)'s parametric-`Res` shape,
   over the `_exv` nodes A6.74 §(1) landed.  This is the file A6.64's
   forty-argument hazard lives in; keep the three payload spellings in
   agreement and move the NODE argument with the obligation.
3. **`WpLock.lk_cpu_res` at `phys_ledger_word`** plus the eight
   `phys_ledger_win` fragments (the reader assembles from them) and the
   held arm's `ledger_vis` residue.
4. **`WpSconfLock`** — delete the dead leaf; holder reads on
   `ledger_vis_own` + `view_lb_0`; `notheld` on `ledger_read_racy_word_ok`;
   free path on `ledger_read_any_ok` (plus §(3)'s named obligation for the
   lock word); stores/AMO on the parked record.  `lock_claims`' surviving
   `TsoCtxShim.ctx_word_of_mem` dies here.
5. **`ProofHolding`**'s 2 call sites, statements unchanged.

**ACCEPTANCE, unchanged:** `SpecAcquire` / `SpecRelease` / `SpecHolding` /
`is_lock` / `locked` / `lock_openable` do not move, and `WpSconfLock`'s
160-file cone opens.


### A6.76 THE STORE GATE CLOSES THE GHOST TIER — AND ITS TWO ARMS ARE THE
### LOCK'S TWO STORES, WHICH IS WHAT MAKES THE KIT HONEST

`ledger_store_wpay_ok` is landed and green.  With it, **M4's whole ghost
and gate tier is complete**: the payload, its three maintenance laws, the
assembly theorems, all four read gates and now the store gate.  What is
left of M4 is entirely above the ledger — the leaf tier — and is the
handoff.

#### (1) THE STORE GATE, AND THE DISJUNCTION IS THE DESIGN

```coq
  Lemma ledger_store_wpay_ok (g g' : gstate) (auth : agent)
      (Pold Pnew : gmap Arch.pa (bv 8))
      (base : Arch.pa) (n : nat) (z : nat -> bv 8)
      (cp : agent -> nat -> bv 8) (own own' : agent -> option nat)
      (Wold Wf : Arch.pa -> ts_win) :
    …
    ((forall j, (j < n)%nat -> Pnew !! pa_add base j = Some (z j))
       /\ own' auth = Some (S (length g.(glog)))
     \/ (forall j, (j < n)%nat -> Pnew !! pa_add base j = Some (cp auth j))
       /\ own' auth = None) ->
    (forall h, h <> auth -> own' h = own h) -> …
```

**THE TWO ARMS ARE `release` AND `acquire`, and nothing else fits.**  A
release writes the CLEAR word and the author's own-last entry moves to the
top — so the author may read "not mine" again.  An acquire writes the
author's OWN word and the entry is **REVOKED** (`own' auth = None`) — the
author is excluded from the racy conclusion until it releases.  That
asymmetry is not a convenience: `win_ok1`'s conjunct (3) says an agent's
recorded own-last write left the CLEAR there, so an agent that has just
written its own word HAS no such record, and the only sound thing to do is
drop it.  A one-armed gate would have been unprovable.

Every OTHER agent's entry is untouched, and its four conjuncts frame on the
author premise alone — `pm_tid msg = h -> msg_byte msg a = None`, which is
**the same `auth` argument `ledger_store_ok` has always taken**.  The
memo's ruling-3 note that "the author is already a parameter of every store
gate" is therefore exactly right, and it is right for the window kit for
the same reason it was right for `own_last`.

`ledger_store_wpay_bytes` (the induction) is `ledger_store_pin_bytes` with
the element function swapped — a mechanical transform, which is itself the
evidence that the corrected per-byte payload sits in the shape the ledger
already had.

> **ONE NAMING TRAP, and it is worth the line.**  `ledger_store_win_ok`
> ALREADY EXISTS in `TsoCtx` and means something else — "win" is the byte
> WINDOW of an ordinary multi-byte store, not the racy payload.  The clash
> reports as a flat `ledger_store_win_ok already exists` at the end of a
> 180-line insertion.  The racy-payload family is therefore `wpay_`:
> `phys_ledger_wpay` / `wpay_map_own` / `wpay_tm` /
> `ledger_store_wpay_{bytes,ok}`.  Grep for `win_` in this file before
> adding to it.

#### (2) TWO ssreflect PAPER CUTS PAID IN `TsoMemPa`

- **`case: … => [->|…]` REWRITES THE GOAL ONLY.**  In
  `win_ok1_app_store` the hypothesis `Hown : own' h = Some t` still
  mentioned `h` after the `->`, and the next `rewrite Ho in Hown` failed
  with *"The LHS of Ho does not match any subterm of the goal"* — an error
  that names the goal while the problem is in a hypothesis.  Use an
  explicit equation plus `subst`.
- **`by rewrite H in H'` does not close a `None = Some _` goal**; it leaves
  the contradiction sitting in the context.  `(rewrite H in H'; discriminate H')`.

#### (3) THE NUMBER

**1088 of 1296, RED 9 — UNCHANGED**, over a round that rebuilt
`TsoMemPa`'s whole cone from source again, plus a confirm round that
recompiled exactly the nine red targets and failed on all nine.  No `Admitted`, no `admit`, no
new `Axiom`; the one `Abort` is still `UsertrapRes.ut_res_bare_park`.
**Three rounds of ghost-tier surgery — a grown element, a grown tie, four
new gates and a new store gate — and the client count has not moved once.**

#### HANDOFF: M4'S LEAF TIER, WHICH IS ALL THAT IS LEFT

The ledger now offers everything the leaves need.  In order:

1. **The phys-datum sibling AU** (A6.74 §(3)): `wp_load_s_sconf_au`'s twin
   whose datum is the ledger rather than the ctx word tower, taking the
   ledger resource as a PARAMETER plus one gate premise so that one leaf
   serves all three routes.  Its three suppliers all exist now —
   `ledger_read_bytes_vis_ok` (holder), `ledger_read_racy_word_ok`
   (`notheld`), `ledger_read_any_ok` (free path) — and the `_exv` node lane
   under it is landed.  **This is the file A6.64's forty-argument hazard
   lives in**: keep the three payload spellings in agreement and move the
   NODE argument with the obligation.
2. **`WpLock.lk_cpu_res` at `phys_ledger_word`**, holding the eight
   `phys_ledger_wpay` fragments (the reader assembles from them via
   `ledger_read_racy_word_ok`), plus the held arm's `ledger_vis` residue.
   Give the lock WORD a degenerate (`tw_n = 4`) payload at the same time —
   that closes A6.75 §(3)'s named image-coverage residual, since
   `ledger_win_img_cover` then supplies `ledger_read_any_ok`'s premise for
   it too.
3. **`WpSconfLock`**: delete the dead leaf; holder reads on
   `ledger_vis_own` + `view_lb_0`; `notheld` on
   `ledger_read_racy_word_ok`; free path on `ledger_read_any_ok`;
   stores/AMO on the parked record and `ledger_store_wpay_ok`.
   `lock_claims`' surviving `TsoCtxShim.ctx_word_of_mem` dies here.
4. **`ProofHolding`**'s 2 call sites, statements unchanged.

**ACCEPTANCE, unchanged:** `SpecAcquire` / `SpecRelease` / `SpecHolding` /
`is_lock` / `locked` / `lock_openable` do not move, and `WpSconfLock`'s
160-file cone opens — sweep it and report the honest number when it does.


### A6.77 THE SIBLING AU IS A GENERALISATION IN PLACE, NOT A COPY — AND
### THAT IS THE MEASUREMENT THAT REPLACES A6.74's ESTIMATE

Item (1) of the leaf tier is LANDED AND GREEN, additively.  Items (2)–(4)
are one atomic unit and are the handoff; §"WHY IT STOPS HERE" says why they
could not be split.

#### (1) `wp_load_s_sconf_au_dat` — ONE BINDER, ONE PREMISE, ONE TACTIC

A6.74 §(3) priced the phys-datum sibling as "identical to the existing one
except that the one `iAssert` runs a different gate", and estimated it as a
~250-line copy of the hazard file's biggest proof.  **The copy is not
needed.**  Measured: the entire ctx-specific content of
`wp_load_s_sconf_au`'s 326-line proof is that ONE `iAssert` (the
`wordw_pointsto_load_c` call).  So the datum abstracts IN PLACE:

```coq
  Lemma wp_load_s_sconf_au_dat … (Dat : mword (8*width) -> iProp Σ) :
    …
    (forall (CIDw : CpuId) img sigma log V (ppn : mword 44) v,
       (uint ea < 274877906944)%Z ->
       (bv_unsigned (subrange_vec_dec ea 11 0) + width <= 4096)%Z ->
       kmap_at (svpn_of ea) ppn KP_rw -∗
       gen_heap_interp (hG := riscv_memGS) sigma.(mem) -∗
       tso_interp_of riscv_eraGS img sigma.(mem) log V -∗
       TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx -∗
       Dat v -∗
       ⌜forall tvr, (V (hart_agent (@cpu_id CIDw)) <= tvr)%nat ->
          tso_read_bytes img log (hart_agent (@cpu_id CIDw)) tvr
            (pa_of ppn ea) (Z.to_N width) v⌝) ->
    … Dat v ∗ (Dat v ={Em, ⊤ ∖ ↑minstretN}=∗ Ψ v) … 
```

and **`wp_load_s_sconf_au` survives below it, character-identical, as the
instance at `wordw_pointsto`** — so its ~15 in-file wrappers and every
consumer in the tree are untouched.  One leaf, every route; nothing below
`gstate` reaches the client (A6.72's barrier-leaf rule holds by
construction, since the premise is discharged *inside*).

> **`Hload`'s CONCLUSION IS PURE, AND THAT IS LOAD-BEARING.**  It takes the
> caller's `own_context` without consuming it, because the proof mode
> keeps every hypothesis handed to a pure assertion — the same property
> `WpSconfLock`'s evidence premises already rely on.  A phys-datum instance
> simply ignores that argument: **the ledger tier needs no token**, which
> is the one respect in which the phys route is CHEAPER than the ctx one,
> not dearer (A6.64's hazard has one fewer payload spelling to keep in
> agreement).

**THREE PRE-FLIGHT ITEMS, and each one bit exactly where the coordinator
said it would:**

- **the `CIDw` binder (A6.64).**  `Hload` must be stated at a `∀`-bound
  `CIDw` and the discharge applied at `CID` — the ambient spelling prints
  identically and fails to unify.
- **`ea` must be spelled `ea`, not its body.**  Writing
  `add_vec (rget m rs1) (sign_extend' 64 imm)` in the premise makes
  `iSpecialize` fail against the goal's `kmap_at (svpn_of ea)` — the two
  print differently and are convertible, and the proof mode wants the
  former.
- **an implicit that leaves the statement must leave the binder list.**
  `{dqm : dfrac}` became uninferrable the moment `Dat` replaced
  `wordw_pointsto … dqm`; the error (`Cannot infer the implicit parameter
  dqm`) names the lemma, not the removed occurrence.
- and the address facts the CLAIM yields inside the leaf (`Hcan`, `Hoff`)
  have to be handed ON to `Hload`: the wrapper cannot supply them, since
  they are derived from the claim the leaf opens.

**COST: 281 files rebuilt (`WpSconfMem`'s cone), red set unchanged.**

#### WHY IT STOPS HERE

Items (2)–(4) are **one atomic unit**: reshaping `WpLock.lk_cpu_res` to
`phys_ledger_word` + the `wpay` fragments turns all three `WpSconfLock`
leaves red at once, and `ProofHolding`'s two sites follow them.  There is
no intermediate state in which the tree is green, so starting it without
the budget to finish would leave a red tree — which is exactly what the
one-flip-at-a-time discipline forbids.  Item (1) was separable *because it
is additive*, and it was taken for that reason.

**1088 of 1296, RED 9 — UNCHANGED**, over the round that rebuilt the AU's
cone.  No `Admitted`, no `admit`; the one `Abort` is still
`UsertrapRes.ut_res_bare_park`.

#### HANDOFF: THE ATOMIC REMAINDER

Everything below it is landed and waiting — the `_exv` nodes, all four read
gates, the store gate, and now the datum-parametric AU.

1. **`WpLock.lk_cpu_res` at `phys_ledger_word`**: the `∃ ξ` goes away, the
   cell becomes eight `phys_ledger_wpay` fragments naming one
   `(base, 8, z, cp, own)`, and the held arm keeps the `ledger_vis` residue
   (`ledger_store_ok`'s `ledger_msg_at` fragment).  Give the lock WORD a
   degenerate `tw_n = 4` payload in the same edit: `ledger_win_img_cover`
   then supplies `ledger_read_any_ok`'s premise for it, closing A6.75
   §(3)'s named residual.
2. **`WpSconfLock`**: `wp_ld_lkcpu_lockopen_gen` and the two
   `wp_clw_lockopen_*` leaves move to `wp_load_s_sconf_au_dat` with
   `Dat := ` the ledger fragments and `Hload := ` the route's gate —
   holder `ledger_read_bytes_vis_ok`, `notheld`
   `ledger_read_racy_word_ok`, free path `ledger_read_any_ok`.  Delete
   `wp_cld_lkcpu_lockopen_s_sconf` (memo ruling 1).  Stores/AMO on the
   parked record and `ledger_store_wpay_ok`.  `lock_claims`' surviving
   `TsoCtxShim.ctx_word_of_mem` dies here (it exists only to put the
   ∃-cell back).
3. **`ProofHolding`**'s 2 call sites, statements unchanged.

**ACCEPTANCE, unchanged:** the exported lock surface does not move, and
`WpSconfLock`'s 160-file cone opens — sweep it and report the honest number
when it does.


### A6.78 THE ATOMIC UNIT DOES NOT EXIST YET — THREE OF ITS PREREQUISITES
### WERE ASSUMED LANDED AND ARE NOT, AND TWO OF THEM ARE NOW LANDED

A6.77's handoff says of items (2)–(4) that "everything below is landed and
waiting".  Measured against the source before touching anything: **three
named pieces of that "everything" do not exist, and one of them cannot be
built in the shape the handoff names.**  This round measured all three,
LANDED THE TWO CHEAP ONES ADDITIVELY, and leaves the third — which is a
tranche, not a step — as the handoff.

**CLEAN ROUND: 1088 of 1296, RED 9 — UNCHANGED**, across a round that
rebuilt the WHOLE tree from `RiscvLang` up (the memory-model invariant
grew a conjunct) and then `WpSconfMem`'s 281-file cone on top of it.  No
`Admitted`, no `admit`, no new `Axiom`; the one `Abort` is still
`UsertrapRes.ut_res_bare_park`.  Shim ledger unchanged: **26 live
qualified uses -- `BootCarveMain` 25 and `WpSconfLock`'s `lock_claims`
1** -- which is the whole remaining `TsoCtxShim` surface, and the two
items it names are the boot-25 lane and this tranche's step 3.

#### (1) THE `_dat` AU SERVES *ONE* OF THE THREE ROUTES, NOT THREE

A6.77 §HANDOFF item 2 routes all three lock reads through
`wp_load_s_sconf_au_dat` with `Hload := ` the route's gate.  Read the
leaf's premise:

```coq
    (forall CIDw img sigma log V ppn v, … -∗ Dat v -∗
       ⌜forall tvr, (V (hart_agent (@cpu_id CIDw)) <= tvr)%nat ->
          tso_read_bytes img log … (Z.to_N width) v⌝) ->
```

**it NAMES the value.**  The atomic update hands over `∃ v, Dat v ∗ …`
and the caller builds that update with no machine state in sight, so `v`
is fixed before the read it is about.  That is exactly right for the
HOLDER route (`ledger_read_bytes_vis_ok` concludes an equality) and
impossible for the other two: `ledger_read_racy_word_ok` concludes an
EXCLUSION (`w ≠ cpw`) and `ledger_read_any_ok` concludes only
`∃ c, tso_read … = Some c`.  Neither can be turned into "the read returns
THIS v".

This is the same distinction A6.74 §(1) built `Mobl_ram_exv` for and then
recorded in that definition's own header — *"[Mobl_ram_ex] must NOT be
used for such a cell: its shape asserts one word good at every reachable
view, which is false the moment another hart writes."*  The `_exv` node
lane has been sitting in `HartSMem` with **zero consumers** since A6.74;
A6.77 built the `_dat` generalisation instead and recorded it as covering
all three routes.  It does not.

**LANDED: `WpSconfMem.wp_load_s_sconf_au_exv`.**  The existential moves
INSIDE the view quantifier and the resource loses its value index:

```coq
  Lemma wp_load_s_sconf_au_exv … (P : mword (8*width) -> Prop) (Res T : iProp Σ) :
    … ->
    (forall CIDw img sigma log V ppn, … -∗ Res -∗
       ⌜forall tvr, (V (hart_agent (@cpu_id CIDw)) <= tvr)%nat ->
          exists v, tso_read_bytes img log … (Z.to_N width) v /\ P v⌝) ->
    … -∗
    (|={⊤ ∖ ↑minstretN, Em}=> Res ∗ (Res ={Em, ⊤ ∖ ↑minstretN}=∗ T)) -∗
    ( ∀ v, wp_next b p (fun CID => … -∗ ⌜P v⌝ -∗ T -∗ WP …)) -∗ …
```

**AND IT NEEDED NO NEW ENGINE, which is the measurement worth keeping.**
`swp_execute_LOAD_ram_Sw_ex` takes its `Rr` and its obligation as
ARGUMENTS, and `swp_read_ram_node_w_exv`'s post
(`∃ bytes, ⌜r = …⌝ ∗ ⌜P bytes⌝ ∗ R`) IS the `_ex` engine's
(`∃ bytes, ⌜r = …⌝ ∗ Rr bytes`) at `Rr := fun bs => ⌜P bs⌝ ∗ R` —
literally the same term, since `∗` associates right.  So the leaf is
`_dat`'s proof with **three arguments and four tactics changed**, and it
compiled first try; the file is 18 s.

> **A6.64's THREE-SPELLINGS RULE, restated for this shape.**  What must be
> `clearbody`-rigid here is `Rex` (the value-independent payload), **not**
> the engine's `Rr`: `Rr` is the literal lambda `fun bs => ⌜P bs⌝ ∗ Rex`,
> and making IT rigid stops the node's post from unifying with the
> engine's slot.  The rule survives — the leaf's `Rr`, the obligation
> argument (`Mobl_ram_exv width pa P Rex`) and the NODE argument
> (`swp_read_ram_node_w_exv width pa P Rex`) are spelled in agreement —
> but the thing you hoist is one level down from `_dat`'s.

#### (2) THE DEGENERATE `tw_n = 4` WINDOW PAYLOAD ON THE LOCK WORD IS NOT
#### BUILDABLE — AND THE OTHER HALF OF A6.75 §(3)'s DISJUNCTION IS

A6.75 §(3) left a named residual: the free-path read of the lock WORD has
no image-coverage supplier, and offered two ways to pay it — *"either give
the lock word a (degenerate, `tw_n = 4`) window payload, or add an
image-coverage conjunct to the lock's own claim"* — and A6.76/A6.77 both
took the first.  **The two are not equivalent and the first is false.**

`win_ok1`'s conjunct (1) says every message touching the byte writes the
WHOLE window with **either the CLEAR word `tw_z` or its author's own word
`tw_cp (pm_tid m)`** — two fixed byte functions, fixed for the life of the
payload (`win_ok1_app_store` re-establishes the claim only at the SAME
`z` and `cp`; only `own` may move).  The lock word's writers are release's
`sw zero` — fine, that is `z` — and **the AMO, whose stored value is
`amoswap_stored (rget m rs2)`, a caller's register**.  No fixed `cp` can
cover it.  Nothing "degenerate" repairs this: `cp h := z` makes the AMO
arm false, and shrinking to `tw_n = 1` per byte keeps conjunct (1)
value-constrained.  The payload is a claim about WHAT IS WRITTEN; the lock
word is the one cell in the kit whose written value is not the kit's to
choose.

**LANDED: the other half.  `RiscvLang.mm_ok` gains a THIRD conjunct,**
last per the new-conjunct rule:

```coq
  /\ (forall a : Arch.pa, (ram_lo <= uint a < ram_hi)%Z -> is_Some (g.(gimg) !! a))
```

— *the era image covers all of RAM* — and `TsoCtx` gains
`ledger_img_cover` / `ledger_read_any_ram_ok` / `ledger_read_any_word_ok`
off it.  **This is what A6.74 §(3) actually specified** (*"payable from
`addr_is_ram` plus the interp's image coverage"*); A6.75 found no such
interp conjunct and downgraded it to a PREMISE on `ledger_read_any_ok`,
which is what sent the design looking for a per-cell payload to pay it.

**AND IT IS THE RIGHT HOME, for the reason A6.74 §(2) gave about frames.**
`gimg` is written exactly ONCE per era (the PowerOn arm) and framed by
every other step, so the conjunct is free at every arm but one, and at
that one it is `boot_facts`' own RAM-totality clause, already there.  A
per-cell ghost claim would instead have needed a MINT — and no cell's
creator can prove a fact about the era image.  *A coverage claim's home is
decided by its frame condition* (A6.74's rule); this one's frame condition
is "the image does not move", so its home is the machine invariant.

**MEASURED CHURN: 5 files, no client movement.**  `RiscvLang` (the
conjunct + the two preservation lemmas + a local `mword_of_int (uint w) = w`),
`RiscvExec` (`tso_interp_of`'s fourth pure tie + `tso_interp_of_img_cover`;
every leaf reaches the bundle through NAMED accessors, so the 21 files that
mention `tso_interp_of` did not move), `TsoCtx` (11 `destruct Hmm` and 4
`mm_ok` reconstructions, one token each), `CtxPinMint` (1),
`RiscvAdequacy` (2 sites).

> **ONE EXPORTED STATEMENT DID MOVE, and it is named here because the
> owner's standing rule says to name it.**  `riscv_system_adequacy` (and
> its device corollary) gains
> `(Hramtot : forall a, addr_is_ram a -> is_Some (g.(gmem) !! a))` —
> the CONVERSE of the `Hram` premise it already takes.  The
> single-generation form takes `g` as given, so RAM totality has to be
> assumed there; the POWER form (`riscv_power_adequacy`, and hence
> `SystemAdequacy`'s two theorems) takes it from `boot_facts` and its
> statement is UNCHANGED.  No caller of the single-generation form exists
> outside the device corollary, so the cost was one argument.

> **A `lia` PAPER CUT WORTH THE LINE.**  In `RiscvLang`, closing
> `0 ≤ bv_unsigned w` (the side goal of `rewrite Z2N.id`) with `lia`
> fails as **"Cannot find witness"** even with `bv_unsigned_in_range` in
> the context — the same misleading message durable-notes files under the
> evar trap, here with no evar in sight.  `pose proof … as [Hr0 _]` and
> `exact Hr0`.  The identical proof body in `RiscvExtras` works, so it is
> the ambient hint/instance set, not the goal.

#### (3) THE RACY KIT HAS NO MINT, AND THAT IS THE REMAINING TRANCHE

`ledger_store_wpay_ok` PRESERVES the window payload — its input is
`wpay_map_own Pold (DfracOwn 1) Wold`, i.e. the payload must already be
there.  **There is no `ledger_wpay_mint`, and there cannot be one from
local facts**, because `win_ok1`'s conjunct (1) quantifies over the WHOLE
log: creating the claim requires knowing that no earlier message wrote the
cell with a disallowed word.  `ledger_pin_mint` has no such problem — the
pin's `pin_ok_mint` needs only the address's LATEST write — which is
exactly why the pin lane was mintable and this one is not.

**AND THE READER SIDE HAS THE SAME SHAPE OF GAP.**
`ledger_read_racy_word_ok` requires `own (hart_agent cpu_id) = Some t` —
an own-last record for the READING hart.  `holding()`'s `notheld` caller
is a hart that does not hold the lock, which does NOT imply it ever wrote
`lk->cpu`.  A hart that has never touched this lock has no record, and
`win_ok1` conjunct (3) says nothing at `own h = None`.

**BOTH GAPS CLOSE AT THE SAME PLACE, AND IT IS THE EMPTY LOG.**  At
`glog = []`:

- conjunct (1) is VACUOUS (no messages);
- conjunct (2) is now free — §(2)'s image coverage;
- conjunct (3) holds for EVERY agent at `own := fun _ => Some 0%nat`:
  timestamp 0 is `img !! a`, `visibleb h tv log 0 = true` at every view
  (`visibleb_below`), the image byte at `lk->cpu` is the clear word
  (`.bss`), and `own_last [] h a 0` is vacuous.

and once minted it is maintained for free: `own_last_app_frame`'s side
condition is `pm_tid m = h -> msg_byte m a = None`, which every OTHER
store in the tree discharges from `ledger_store_ok`'s own `auth`.

So the missing piece is **a boot mint plus its threading**: `TsoCtx`
gains a `ledger_wpay_mint` whose premise set is the empty log (or,
equivalently, the four conjuncts above), `BootCarve` mints the lock cells'
payload while the log is still empty, and the payload rides to
`lock_inv_alloc` through the `newlock` family — the creator cascade
§0.18′ priced (19 call sites) plus `BootCarveMain`.  **That is a tranche
of its own and it is what item (2) of A6.77's handoff is really waiting
on.**

> Two alternatives were considered and are recorded as rejected.  (i)
> Relativising conjunct (1) to timestamps above a mint index `tw_lo`
> makes the mint local, but the READER's conjunct (3) still needs
> "visible at every view", which only timestamp 0 or the reader's own
> message gives — so it moves the gap rather than closing it, at the cost
> of reworking `read_down_win` / `find_top` / `racy_read_window`.  (ii)
> Deriving the reader's own-last record from a hart-local "I have never
> written `a`" resource: no such ghost exists, and adding one is a bigger
> change than the boot mint.

#### HANDOFF: M4'S LEAF TIER, WITH THE ORDER CORRECTED

Below the leaves, what now exists: the `_exv` node lane AND its S-mode
consumer (§(1)); all four read gates plus §(2)'s three image gates; the
two-armed store gate; both datum-parametric AUs.  What does NOT exist is
the racy payload's MINT.

1. **The racy payload's boot mint and its threading** (§(3)) —
   `TsoCtx.ledger_wpay_mint` at the empty log, `BootCarve`'s mint of the
   lock cells, and the payload through the `newlock` family to
   `WpLock.lock_inv_alloc`.  **This gates `wp_cld_lkcpu_lockopen_notheld_s_sconf`
   and therefore `ProofHolding:281` and therefore the whole cone.**
2. **`WpLock.lk_cpu_res` at `phys_ledger_word`** with the eight
   `phys_ledger_wpay` fragments and the held arm's `ledger_vis` residue.
   The lock WORD gets **no** payload (§(2)): its free-path read is
   `ledger_read_any_word_ok` off `addr_is_ram`, and its HOLDER read
   (`wp_clw_lockopen_locked_s_sconf`, which must conclude the word is
   NONZERO) needs the held arm to carry the AMO's `ledger_msg_at`
   author fragment, so that `ledger_vis_own` gives the exact value.
   **That last point is new and is not in A6.77's list.**
3. **`WpSconfLock`**: delete `wp_cld_lkcpu_lockopen_s_sconf`; the two
   holder reads on `wp_load_s_sconf_au_dat`; `notheld` and the free-path
   word read on `wp_load_s_sconf_au_exv`; the stores/AMO on the parked
   record and `ledger_store_wpay_ok`.  **The AMO leaf is the biggest
   single item and A6.77's list does not price it**: it does its own
   inline read and write of the lock word through
   `word4_pointsto_write_c` (the ctx tower), and at the reshaped cell
   both have to be re-done at the ledger tier.
   `lock_claims`' surviving `TsoCtxShim.ctx_word_of_mem` dies here.
4. **`ProofHolding`**'s 2 call sites, statements unchanged.

**ACCEPTANCE, unchanged:** `SpecAcquire` / `SpecRelease` / `SpecHolding` /
`is_lock` / `locked` / `lock_openable` do not move, and `WpSconfLock`'s
160-file cone opens.


### A6.79 THE RACY MINT IS LANDED — AND ITS PREMISE IS LOCAL, WHICH MOVES
### THE TRANCHE OFF THE BOOT CARVE ENTIRELY

The coordinator ratified A6.78's `Hramtot` and approved the boot-mint
tranche as characterised there.  Step 1 is LANDED AND GREEN, and it came
out **stronger than the approval assumed**: the mint does not need the
empty log, and therefore does not need `BootCarve`, the 19-site `newlock`
creator cascade, or any adequacy change.  What it needs instead is one
store leaf, and the site is named below.

**CLEAN ROUND: 1088 of 1296, RED 9 — UNCHANGED.**  No `Admitted`, no
`admit`, no new `Axiom`; the one `Abort` is still
`UsertrapRes.ut_res_bare_park`.

#### (1) `TsoCtx.ledger_wpay_mint` — AND THE PREMISE IS `e.1 = 0`

```coq
  Lemma ledger_wpay_mint1 (g : gstate) (a : Arch.pa) (v : bv 8) (W : ts_win) :
    a = pa_add (tw_base W) (tw_j W) ->
    (tw_j W < tw_n W)%nat ->
    (forall k, (k < tw_n W)%nat -> is_Some (g.(gimg) !! pa_add (tw_base W) k)) ->
    (forall h t, tw_own W h = Some t -> t = 0%nat) ->
    tw_z W (tw_j W) = v ->
    gen_heap_interp … -∗ tso_interp_at riscv_eraGS g -∗
    phys_ledger_at a (DfracOwn 1) v 0%nat ==∗
    gen_heap_interp … ∗ tso_interp_at riscv_eraGS g ∗
    phys_ledger_wpay a (DfracOwn 1) v 0%nat W.
```

plus `ledger_wpay_mint`, its `n`-byte window form at
`W j := TsWin base n j f cp (fun _ => Some 0%nat)`.

**A6.78 said all three gaps close "at the empty log"; measured, they close
at a WEAKER and LOCAL fact — the element's own timestamp.**  The interp's
tie at a timestamp-0 element is `latest img log a 0 v`, whose SECOND half
is *"no timestamp above 0 writes `a`"* — i.e. **no message in the log
writes this byte at all**.  That single fact discharges, at once:

- **conjunct (1)** — vacuously: its premise `is_Some (msg_byte m a)` is
  false for every logged message, so the "clear word or the author's own"
  disjunction is never asked;
- **conjunct (3)'s `own_last log h a 0` for EVERY agent** — same reason,
  and this is the half A6.78 filed as needing a boot-time record;
- and the byte value: `log_byte img log 0 a = img !! a = Some v`, so
  `tw_z` is forced to the cell's current value rather than chosen.

**conjunct (2)** is A6.78's own image coverage, reached through
`ledger_img_cover` off `phys_ledger_ram` — so the two landings of the
previous round are what make this one a short proof.  `tw_cp` stays a free
parameter (conjunct (1) is vacuous, so the author words are the caller's
choice, and they are then fixed for the payload's life:
`win_ok1_app_store` re-establishes the claim only at the same `z` and
`cp`, and moves only `own`).

> **THE RULE THIS LEAVES, and it is the one to carry forward:** *an
> unwritten cell is a cell that can be given any history-shaped claim,
> because it has no history.*  The pin's mint reads the address's LATEST
> write; the window's reads the address's WHOLE past, and `e.1 = 0` is the
> ledger's own certificate that the past is empty.  No new ghost, no boot
> parameter, and no premise a client cannot hold.

#### (2) WHERE IT CAN BE APPLIED — AND `BootCarve` IS NOT IT

**`BootCarve` cannot mint: it has no interp.**  It is pure resource
algebra over already-minted fragments (`boot_raw_ran` is a `big_sepM` of
`pointsto`), and the `ghost_map_update` on `ts_name` needs the AUTHORITY,
which lives in `tso_interp_at` and nowhere else.  That is A6.71's rule
read in this direction:

> `own_context` is only in hand OUTSIDE a WP leaf.
> `tso_interp_at` is only in hand INSIDE one.

So the approval's "BootCarve mints the lock cells before anything is
written" is not executable as stated, and the honest replacement is
CHEAPER.

**THE SITE IS `initlock`'s OWN `lk->cpu = 0` STORE.**  `CodeInitlock`
`ini_0e` is `sd zero,16(a0)` at `initlock + 0x0e`, proved in
`ProofInitlock:190` by `wp_sd_zero_s_sconf` — an ordinary store leaf,
which has the interp internally.  A wpay variant of it does BOTH halves in
one node, in this order:

1. **mint first**, while the cell is still at timestamp 0 (`.bss`, never
   written in this era) — `ledger_wpay_mint` at
   `z := nth_byte (zero_reg : mword 64)`, `cp h := nth_byte (cpus_ptr …)`,
   `own := fun _ => Some 0`;
2. **then store**, through `ledger_store_wpay_ok`'s RELEASE arm, which
   writes the clear word and moves the AUTHOR's entry to the top while
   leaving every other agent's at `Some 0` (its `Hoth` premise).

> **THE ORDER IS FORCED, and it is worth stating because the obvious
> alternative is unsound.**  Minting AFTER the store fails: conjunct (3)
> would then need, for every OTHER hart, a timestamp visible at every view
> holding the clear word, and only timestamp 0 is — but `own_last log h a 0`
> has become "no message writes `a`", which hart 0's own store has just
> falsified for itself and which no local fact re-establishes for the
> others.  Mint-then-store keeps every non-author at `Some 0` and that is
> exactly the entry `win_assemble_not_mine` consumes.

**WHAT THIS COSTS, AND WHAT IT DOES NOT.**  It costs one new store leaf
(the wpay twin of `wp_sd_zero_s_sconf`), `SpecInitlock`'s post, and
`SpecProcinit.lk_fresh` — which is *already* initlock's post, so the
payload rides to `WpLock.lock_inv_alloc` on a shape that exists.  It does
NOT cost: `BootCarve`, the adequacy statement (again), the 19-site
`newlock` creator cascade, or a barrier-leaf/`__sync_synchronize` move
(A6.71's route (a), which the publication's last mile still needs and this
does not).

> **ONE THREADING OBLIGATION REMAINS AND IT IS THE BOOT 25.**  The mint
> wants the cpu cell AT TIMESTAMP 0 when `initlock` reaches it, and
> **`ctx_pointsto` HIDES the timestamp** — its body is
> `∃ ppn t, kmap_at … ∗ … ∗ (pa_of ppn va) ↪[ts_name]{dq} (t, ts_pay_none) ∗ …`,
> so no downstream lemma can recover `t = 0` from a `↦₈` cell.  The
> witness therefore has to come from the CARVE, which is the one place it
> is known (`RiscvAdequacy` allocates every element at `(0, ts_pay_none)`
> and `BootCarve.boot_led_ran` hands them out as `ledger_elem0`).
> **And the honest producer already exists**: `BootCarve.boot_ctx_phys_word`
> pairs `boot_raw_ran`'s bytes with `boot_led_word`'s eight elements and
> builds `ctx_phys_word_pointsto` with no shim at all — the cell shape
> `BootCarveMain`'s 25 surviving `TsoCtxShim.ctx_word_of_mem` calls are
> standing in for.  So the boot-25 lane and this obligation are ONE piece
> of work, exactly as the approval hoped, just entered from the other end:
> **thread `boot_led_ran` alongside `boot_raw_ran` through the
> `boot_ran_cell*` family, and keep the element's timestamp exposed on the
> lock's cpu word.**

#### HANDOFF: THE ORDER, RE-COSTED

1. **The boot-25 lane, entered as a timestamp-0 lane.** `BootCarve` gains
   the ctx/ledger cell producers at exposed timestamp 0 (its `ledger_elem0`
   supply is already there — `RiscvAdequacy`'s `boot_led_all_split`), and
   `BootCarveMain`'s 25 shim calls die with it.  **3 files behind it, and
   it is the mint's only prerequisite.**
2. **The `initlock` wpay store leaf** (§(2)) + `SpecInitlock` + `lk_fresh`.
3. **`WpLock.lk_cpu_res` at the eight `phys_ledger_wpay` fragments**; the
   lock WORD still gets no payload (A6.78 §(2)), its free-path read is
   `ledger_read_any_word_ok` and its holder read needs the AMO's
   `ledger_msg_at` author fragment in the held arm.
4. **`WpSconfLock`** — the three leaves on `wp_load_s_sconf_au_dat` /
   `wp_load_s_sconf_au_exv`, the deletion, the stores/AMO on the parked
   record; the AMO leaf's inline read AND write redone at the ledger tier.
5. **`ProofHolding`**'s 2 call sites, statements unchanged.

Items 3–5 remain ONE atomic unit; 1 and 2 are separable and additive, and
1 is separable from 2.

**ACCEPTANCE, unchanged:** `SpecAcquire` / `SpecRelease` / `SpecHolding` /
`is_lock` / `locked` / `lock_openable` do not move, and `WpSconfLock`'s
160-file cone opens.


### A6.80 THE CARVE'S TIMESTAMP-0 EXIT IS BUILT — AND THE BOOT 25 IS A
### RESTRUCTURING, NOT A THREAD, WHICH IS THE MEASUREMENT THAT MATTERS

Executing the coordinator's ratification of A6.79 (commit `d33057e0`),
items 1 and 2.  **Item 1's REUSABLE HALF IS LANDED** — the carve now has
the honest raw→ctx producers the shim's dead conversions stood in for,
AND the timestamp-0 exit the mint consumes.  **Item 1's remainder and item
2 are measured below and were not started**, for a reason the discipline
names: item 2's reshape moves GREEN files, and there was not budget to
land it in one pass.

**CLEAN ROUND: 1088 of 1296, RED 9 — UNCHANGED.**  No `Admitted`, no
`admit`, no new `Axiom`; the one `Abort` is still
`UsertrapRes.ut_res_bare_park`.

#### (1) LANDED: THE MINT'S CARVE INPUT, AND IT IS DEFINITIONAL

```coq
  (* TsoCtx *)
  Lemma phys_ledger_at0_of_elem a dq v :
    phys_pointsto a dq v -∗ ledger_elem0 a dq -∗ phys_ledger_at a dq v 0%nat.
  Lemma phys_ledger_at0_elem a dq v :
    phys_ledger_at a dq v 0%nat ⊢ phys_pointsto a dq v ∗ ledger_elem0 a dq.

  (* BootCarve *)
  Lemma boot_ledger_at0_word (g : gstate) (base : Z) : … ->
    boot_raw_ran g base (base + 8) -∗ boot_led_ran g base (base + 8) -∗
    ∃ w : bv 64, [∗ list] j ∈ seq 0 8,
      TsoCtx.phys_ledger_at (pa_add (pa_of_z base) j) (DfracOwn 1)
        (nth_byte w j) 0%nat.
```

**`ledger_elem0` IS `phys_ledger_at … 0`'s element**, so the bridge is
`iFrame` and the carve exit is `boot_ctx_phys_word` with ONE pairing
lemma swapped.  A6.79 said the witness "has to come from the carve
because `ctx_pointsto` hides `t`"; this is that exit, and it cost four
lines plus a comment.  **The supply side was already threaded** —
`RiscvAdequacy` hands the boot client `BootCarve.boot_led_ran g text_end
ram_hi` beside the raw bytes (its own line 540), so nothing above the
carve moves to reach it.

**ALSO LANDED: the honest replacements for the shim's raw→ctx
conversions**, `BootCarve.boot_ctx_of_mem_{byte,word,word4}`:

```coq
  Lemma boot_ctx_of_mem_byte (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    addr_is_kdata a ->
    kmap_static_claims -∗ a ↦ₘ{dq} v -∗ TsoCtx.ledger_elem0 a dq -∗
    TsoCtx.ctx_pointsto XI a dq v.
```

off `TsoCtx.ctx_pointsto_of_ro` over the carve's identity map.  **They
take TWO resources and that is the whole point**: a ctx byte carries the
address's ledger element and a raw one has none, which is why
`TsoCtxShim.ctx_*_of_mem` was false at this machine and why its use sites
are not lines that can be deleted.  At timestamp 0 the CLEAN arm is free
(`llb_0`), so no context authority is needed and the cell is born at any
ξ — A6.63's reason, re-used.

#### (2) THE BOOT 25, INVENTORIED — AND TWO SITES HAVE NOWHERE TO THREAD

25 shim calls, **13 lemmas**, measured:

| lemma | word | byte | eslot | buf |
|---|---|---|---|---|
| `boot_lk_raw` (:525) | 2 | | | |
| `boot_cons_res` (:584) | | | | 1 |
| `boot_sl_raw` (:679) | 3 | | | |
| `boot_disk_slots` (:827) | 1 | 1 | 1 | |
| **`bpay_raw_buf_raw`** (:1005) | | 1 | | |
| **`file_node_raw_fentry`** (:1455) | | 2 | 2 | |
| `boot_log_raw` (:1649) | 2 | | | |
| `boot_ctx_cells` (:1778) | 1 | | | |
| `boot_ofile_cells` (:1880) | 1 | | | |
| `boot_proc_name` (:1917) | | 1 | | |
| `boot_proc_slot` (:2076) | 5 | | | |
| `boot_page_own` (:2193) | | 1 | | |

Eleven of the thirteen take a `boot_raw_ran` range and can take a
`boot_led_ran` beside it — those are the thread the approval described.
**The two in bold cannot: they take NO range at all.**
`bpay_raw_buf_raw` and `file_node_raw_fentry` are pure BUNDLE
CONVERSIONS — they receive an already-carved *raw* bundle
(`bpay_raw` / `file_node_raw`) and hand back its *ctx* twin — so there is
no place in their statements for an element run to arrive.

> **AND THAT IS THE MEASUREMENT THAT REPLACES "THREAD IT THROUGH".**  The
> carve's raw/ctx split exists because the SC-era shim made the crossing
> free, so the file could carve RAW everywhere and convert per bundle at
> the end.  With the crossing costing an element, the conversion has to
> move to where the elements are — i.e. **the carve must build the CTX
> cells directly and the two conversion lemmas disappear**, taking their
> raw bundle definitions with them.  That is a restructuring of
> `BootCarveMain`'s raw/ctx layering, not a rename, and it is why the
> lane is worth its own pass rather than being folded into item 2.
> The eleven range-taking lemmas are mechanical; these two are the design.

#### (3) ITEM 2, MEASURED — AND WHY IT WAS NOT STARTED

The mint runs at `initlock`'s `lk->cpu = 0` (A6.79 §(2)), so the cpu word
must reach it at the exposed timestamp.  Measured:

- **`SpecInitlock` takes the three lock fields DIRECTLY** (`c_name ↦₈
  vname`, `c_cpu ↦₈ vcpu`; post `c_cpu ↦₈ 0`), not a bundle — so the
  contract change is two conjuncts, and the post becomes the wpay
  payload.
- **`lk_raw` is DESTRUCTURED IN EXACTLY ONE PLACE** in the whole tree
  (`BootCarveMain:524`, its producer).  Its other 60 mentions across 11
  files are applications, which do not move.  `lk_fresh` is the same
  shape (49 mentions, 13 files).  **So growing the cpu conjunct is the
  `ts_ok` pattern again — cheap at the mentions, real at the two ends.**
- The two ends are `boot_lk_raw` (RED already) and initlock's callers —
  `ProofInitlock`, `ProofProcinit`, `ProofConsoleinit`, `ProofUartinit`,
  `SpecMain`, `SpecConsoleinit`, `SpecUartinit`, `SpecProcinit` — **and
  those are GREEN.**

**That is why it stopped here.**  The BootCarve work above is additive and
`BootCarveMain` is already red, so neither could regress the number; item
2 reshapes a definition that eight GREEN files produce or consume, and
its largest single piece — a mint-then-store variant of the store AU, the
`Wobl_ram` twin of this round's `wp_load_s_sconf_au_exv` — is a ~350-line
leaf of its own.  Starting it without budget to finish would leave green
files red, which is the one thing the standing discipline forbids.

#### HANDOFF

1. **The boot-25 restructuring** — the eleven range-taking lemmas take
   `boot_led_ran` beside `boot_raw_ran` and use
   `boot_ctx_of_mem_{byte,word,word4}`; `bpay_raw_buf_raw` and
   `file_node_raw_fentry` die together with their raw bundle definitions,
   the carve building ctx cells directly.  `BootCarveMain` greens and the
   shim ledger drops to **`WpSconfLock`'s `lock_claims`, one ref**.
2. **Item 2**: `SpecInitlock`'s two conjuncts + `lk_raw`/`lk_fresh`'s cpu
   field at the exposed timestamp (`boot_ledger_at0_word` is the
   producer, landed), the mint-then-store leaf, and initlock's eight
   caller files — **one pass, they are green**.
3–5. Unchanged (A6.78's corrected leaf list), still one atomic unit.

**ACCEPTANCE, unchanged:** the exported lock surface does not move, and
`WpSconfLock`'s 160-file cone opens.


### A6.81 THE BOOT 25 IS PAID BY A PAIRED RANGE, NOT BY A SECOND ARGUMENT —
### AND THE MINT'S SITE IS REFUTED AT ONE OF `initlock`'s CALLERS

Executing the coordinator's tranche after A6.80.  **Item 1 IS LANDED AND
GREEN**; item 2's largest single piece is landed additively; **item 2's
SITE is refuted by measurement** and items 2–3 therefore stop at a design
question, which is §(4).  One separable file outside the M4 line went
green on the way (`VcGenS`, §(5)), and it exposed the two ξ-indexing
problems at concrete sites rather than as predictions.

**1091 of 1296, RED 9** (from 1088 / red 9): `BootCarveMain`, `VcGenS`
and `WpSwtchVc` are green; `ProofKernelvec` and `ProofSwtch`, which were
UNREACHED behind `VcGenS`, are now red and measured.  **The confirm round
recompiled exactly those nine targets and failed on all nine**, which is
A6.73's two-consecutive-rounds check and rules out the mtime artefact.
The model `.vo` was verified to postdate its source first (19:11 over
18:37, A6.39's rule).  No `Admitted`, no `admit`, no new `Axiom`; the one
`Abort` is still `UsertrapRes.ut_res_bare_park`.

#### (1) THE MEASUREMENT THAT REPLACES "THREAD `boot_led_ran` ALONGSIDE"

A6.80 priced the eleven range-taking lemmas as "take a `boot_led_ran`
beside the `boot_raw_ran`".  Measured, that is the expensive spelling:
**`BootCarveMain`'s carve is 121 `boot_ran_split`s, 16 `boot_ran_eq`s and
7 stride families**, and a second range threaded beside the first doubles
every one of them.

**What it costs instead is ONE definition:**

```coq
  (* BootCarve *)
  Definition boot_cran (g : gstate) (lo hi : Z) : iProp Σ :=
    (boot_raw_ran g lo hi ∗ boot_led_ran g lo hi)%I.
```

plus a `boot_cran_*` family that is `boot_ran_*`'s **statement for
statement** — same premises, same argument order — whose CELL producers
land at the CTX tier directly (`boot_cran_cell8` / `_cell4` / `_cell2` /
`_byte` / the three `_bss` pins / `_cell4_at` / `_mem_run` /
`_bytes_list` / `_bytes_zero` / `_stride_family{,_seq}` / `_split` /
`_eq`, 21 items).  Each is three lines: the raw producer on the left
half, `boot_led_run` (`boot_led_word` generalised to any width) on the
right, and `boot_ctx_of_mem_{byte,word,word2,word4}` to pair them.

> **THE RULE, and it is the one to carry to the next carve of this
> shape:** *when a crossing costs a second resource at every cell, pair
> the two SUPPLIES in one predicate rather than threading the second
> through every cut.*  The client's proof text is then a RENAME
> (`boot_ran_X` → `boot_cran_X`), and the crossing lemma disappears from
> the client entirely instead of appearing once per cell.

**`BootCarveMain` IS GREEN AND ITS 25 SHIM CALLS ARE GONE**, with no
`ctx_*_of_mem` replacement at any of them: the cells are born ctx.
Measured cost — the rename, plus **nine shapes restated at the ctx tier**
(the five local records `dinfo_raw` / `dops_raw` / `bpay_raw` /
`file_node_raw` / `proc_slot_raw`, and the four conclusions
`boot_word4_cells` / `boot_zero_cells` / `boot_name_cells` /
`boot_procs_raw`) and **eight `` `{XI : CurCtx} `` binders added**.  The file does NOT `Import TsoCtx`: its bare `↦` notations stay
the raw ones the range machinery is stated in, and the ctx tower is
named qualified in exactly those seven shapes.  That is the whole of the
"restructuring, not a rename" A6.80 named.

> **AND A6.80's TWO BOLD LEMMAS DID NOT DIE — THEY BECAME FRAMINGS.**
> `bpay_raw_buf_raw` and `file_node_raw_fentry` are now
> `iIntros "$"` (their raw bundle definitions were restated at the ctx
> tier, which is what "the carve builds ctx cells directly" means in
> practice).  Keeping the NAMES is right and is worth the line: their
> content is the ADDRESS agreement — that the `k`th record of the carve's
> stride family is the `k`th buffer / file entry — and nothing else in
> the tree says so.

#### (2) THE ELEMENT SUPPLY HAD TO GROW A ROW IN `power_boot_res`

The single-generation theorem hands the boot client
`BootCarve.boot_led_ran g text_end ram_hi` (A6.80 §(1) checked this).
**The POWER form does not**, and `BootShared` — the client both forms
share — is where the carve runs.  So `RiscvAdequacy.power_boot_res` gains

```coq
     ([∗ map] a ↦ _ ∈ g'.(gmem),
        ghost_map_elem (era_ts_name HE) a (DfracOwn 1)
          ((0%nat, TsoMemPa.ts_pay_none) : TsoMemPa.ts_elem)) ∗
```

— the WHOLE map, exactly as it hands the whole raw one, cut by the client
with `boot_led_all_split`.  Its supplier is the power loop's own
`ghost_map_alloc` (`Htsfrags2`), which until now was allocated and
dropped.

> **IT SITS BEFORE `crash_inv`, NOT LAST, AND THE REASON IS THE UNPACK.**
> `BootShared.power_boot_res_unpack` is one `iExact`, so the two right-
> nested chains must associate identically; the fixed-layer tail
> (`crash_inv ∗ gen_cert`) is ONE bundle at the unpack and three
> conjuncts in `power_boot_res`, so a row appended after it does not
> convert.  The new-conjunct rule ("put it last") is about DESTRUCTURING
> churn; where an `iExact` bridges two spellings, the rule is *put it
> before the bundled tail*.

**`BootShared` is UPDATED BUT UNREACHED**, and honestly so: it was
already stale before this round (its `boot_text_persist` call is
two-argument and that lemma has taken the pristine elements since A6.63),
and its only route to a compiler is `BootChain → LinkMain → ProofMain`,
which is red on the publication's last mile.  Its edit is the mirror of
`RiscvAdequacy`'s own carve: `boot_led_all_split`, `boot_led_text_persist`,
`boot_text_persist` at three arguments, then `boot_cran_intro` pairing the
data half back onto the raw range, and `boot_cran_raw` at the two ranges
that stay raw (the rodata prefix that becomes `kernel_data`, and
`_entry`'s GOT word).

#### (3) LANDED ADDITIVELY: THE STORE AU IS A GENERALISATION IN PLACE

A6.80 priced item 2's leaf as "a ~350-line leaf of its own, the
`Wobl_ram` twin of `wp_load_s_sconf_au_exv`".  **A6.77's measurement
applies again and the copy is not needed**: the entire ctx-specific
content of `wp_store_s_sconf_au`'s 230-line proof is the write node's ONE
`wordw_pointsto_write_c` call, so the datum abstracts in place:

```coq
  Lemma wp_store_s_sconf_au_dat … (Res Post : iProp Σ) :
    …
    (forall (CIDw : CpuId) (img : bytemap) (sigma : mstate)
            (log : list pwmsg) (V : agent -> nat) (ppn : mword 44),
       (uint ea < 274877906944)%Z ->
       (bv_unsigned (subrange_vec_dec ea 11 0) + width <= 4096)%Z ->
       ktier_pin ktd ppn ea ->
       kmap_at (svpn_of ea) ppn KP_rw -∗
       gen_heap_interp (hG := riscv_memGS) sigma.(mem) -∗
       tso_interp_of riscv_eraGS img sigma.(mem) log V -∗
       TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx -∗
       Res ==∗
       gen_heap_interp … ∗ tso_interp_of … ∗
       TsoCtx.own_context (CID := CIDw) TsoCtx.cur_ctx ∗ Post) ->
    … wordw_claim (KTR := ktd) width ea -∗
    (|={⊤ ∖ ↑minstretN, Em}=> Res ∗ (Post ={Em, ⊤ ∖ ↑minstretN}=∗ Ψ)) -∗ …
```

and `wp_store_s_sconf_au` survives below it, statement-identical, as the
instance at `Res := ∃ vold, wordw_pointsto … vold` /
`Post := wordw_pointsto … sv`.  **~55 lines, and it compiled first try.**

> **THE MASK IS `==∗`, AND THAT IS WHAT MAKES THE OBLIGATION A MINT
> SITE.**  The node has already closed to `∅` and the obligation runs
> inside the caller's own atomic-update mask, so a caller may run
> `ledger_wpay_mint` (or any other ghost update needing the interp) right
> there.  This is A6.71's rule read FORWARDS: `tso_interp_at` is only in
> hand inside a WP leaf, and this premise is how a leaf lends it out.
>
> `ktier_pin ktd ppn ea` is passed to the obligation as well as `Hcan`
> and `Hoff`: a ledger-tier caller works at the PHYSICAL address
> `pa_of ppn ea`, and at `KT0` that pin is `pa_of ppn ea = ea`
> (`ktier_pin_id`) — the only bridge between the leaf's VA-keyed claim
> and a `phys_ledger_*` cell.

#### (4) THE MINT'S SITE IS REFUTED: `initlock` HAS A DYNAMIC CALLER

**`ledger_wpay_mint`'s premise is `phys_ledger_at a … 0` — the element's
own timestamp — and A6.79 justified the site by ".bss, never written in
this era".  Measured: `initlock` is NOT only called on `.bss` locks.**

`ProofPipealloc:1522` applies `Initlock.wp_initlock_sconf` to the lock
inside a **`kalloc`'d page** (`ProofPipealloc:1379`'s
`PipeInv.page_own_pipe_raw`, off `Kalloc.wp_kalloc_sconf`).  Every page
on `kmem`'s free list has been written — `kfree` memsets it, and at boot
`kinit`/`freerange` memsets every page there is — so its bytes are at a
timestamp `> 0` and the mint's premise is **unsatisfiable at that call
site**.  Strengthening `SpecInitlock`'s precondition to the exposed
timestamp therefore turns a GREEN file red with no available discharge,
which is the one thing the standing discipline forbids.

**AND NEITHER OF THE OBVIOUS REPAIRS WORKS, for reasons already on the
record:**

- **Mint after the store instead.**  Conjunct (3) then needs, for every
  OTHER hart, a timestamp visible at every one of its views that is also
  that hart's last write to the cell.  `Some 0` serves a hart that never
  wrote the byte; the hart that ran `kfree`'s memset DID write it, and
  nothing local recovers its timestamp.  (A6.79's forced-order note is
  the same argument one step earlier.)
- **Keep `own h = Some 0` and lean on conjunct (1).**  `win_ok1`
  conjunct (1) quantifies over the WHOLE log and allows exactly two
  words per byte — the clear word `tw_z` and the author's own
  `tw_cp h`.  The memset's messages wrote neither.

> **WHAT THE REFUTATION ACTUALLY POINTS AT, and it is a shape the memo
> already contains.**  The exclusion the `notheld` read needs is only
> *"no message writes `cpus_ptr h` to this window except `h`'s own"* —
> the memset's `0xff…` bytes are harmless to it.  What forbids them is
> that `win_ok1`'s conjunct (1) is hard-coded to a two-word disjunction,
> where `tso-m4-memo.md` §8's probed `wpin` is a PREDICATE per author
> (`Wf : agent -> (nat -> option (bv 8)) -> Prop`).  So the question for
> the coordinator is one of three:
>
> 1. **Generalise `ts_win`'s conjunct (1) to the memo's `wpin`
>    predicate** (the probe is green and archived; the cost is `TsoMemPa`
>    + `ts_ok` + the two store gates), which makes the mint's premise
>    "every past message wrote something *allowed*" rather than
>    "there are no past messages", and a `kalloc`'d page's history is
>    then admissible because the kit may name the memset's word.
> 2. **Fork `SpecInitlock`** into the `.bss` contract (payload-producing)
>    and the plain one, by making `wp_initlock_sconf_body`
>    DATUM-PARAMETRIC in the `lk->cpu` field — the same move §(3) just
>    made one tier down, and the honest one if (1) is judged too big.
>    Its cost is the `INITLOCK` module type and its ~19 client files.
> 3. **Accept that `pipe`'s lock has no racy payload**, which is only
>    viable if `holding()` can be discharged for it another way — and it
>    cannot: `ProofHolding:281`'s `notheld` leaf is the single one every
>    `acquire` runs.
>
> **Nothing below the fork moves either way**: §(3)'s AU, the four read
> gates, both store gates, `ledger_wpay_mint` and `boot_ledger_at0_word`
> are all landed and serve any of the three.

#### (5) OFF THE M4 LINE: `VcGenS` IS GREEN, AND ITS CONE'S TWO BLOCKERS
#### ARE NOW MEASURED RATHER THAN PREDICTED

`VcGenS`'s red was A6.63's diagnosis exactly — the memory leaves take
`TsoCtx.own_context` and hand it back, and the generated block WP did not
carry it.  Threading it is **six statements and two induction bodies**,
and it is mechanical: the token rides beside the symbolic heap
(`vheap_own` / `vheap4_own`) in every one of them.  `VcGenS` and
`WpSwtchVc` are green.

**THE CONE DID NOT OPEN, AND WHERE IT STOPS IS THE RESULT.**  Of the 85
files behind `VcGenS`, 82 are behind `ProofSwtch` and 12 behind
`ProofKernelvec`; both are now RED (they were UNREACHED), and each is one
of the two ξ/receipt problems, at a concrete site:

- **`ProofSwtch:157`** still calls the shim's `hart_view_lb_any` — which
  no longer exists — to feed `ctx_resume XIt Tt Tt`.  The honest receipt
  is the acquire's (`hart_view_lb_get` at the AMO), so what is owed is
  the park protocol's STAMP TIE: `valid_context` must publish a bound
  `Tpark ≥ Tt` and the resumer must arrive holding `hart_view_lb Tpark`.
  Same family as `UtResFits`' `ut_res_bare_park` abort.
- **`ProofKernelvec:1704`** cannot hand `devintr_caps` to `kerneltrap`:
  the handler is stated at a **∀-bound resume context** `XIc` while the
  caps bundle was captured at the ambient one, and
  `SpecDevintr.devintr_caps` is `{CID XI}`-indexed (measured with
  `About`).  **This is the boot-captured-caps problem with a line
  number, and the index's entry point is now named too.**
  `WpLock.is_lock` is ξ-FREE by construction — its `R` is a
  `CtxId → iProp Σ` — but the tree instantiates that slot with
  `<{ P }>` (`TsoCtx.const_pay`), the CONSTANT function at a `P` that is
  itself stated at the ambient ξ:

  ```coq
    is_conslock γ := is_lock γ a_cons "cons" <{ cons_res }>       (* ConsoleInv *)
    is_txlock γl γu := is_lock γl a_tx_lock "uart" <{ tx_res γu }> ∗ …
    console_caps γu := ∃ γtx γc, is_txlock γtx γu ∗ is_conslock γc ∗ …
  ```

  and `ConsoleInv.cons_res`'s cells are `ctx_pointsto XI` (that is what
  `BootCarveMain.boot_cons_res` now produces directly, §(1)).
  `disk_geom`'s three `↦₈□` pointers are the same story one bundle over.

  > **SO THE SLOT IS PARAMETRIC AND THE PAYLOADS ARE NOT, AND THAT IS
  > THE WHOLE OF IT.**  `const_pay` is the right shape only for a
  > ξ-FREE resource.  The repair direction is per payload, not per
  > handle: state `cons_res` (and `tx_res`, and `disk_geom`'s pointer
  > row) as a FUNCTION of ξ and instantiate `R` with it, so that the
  > acquirer gets the cells at ITS context — which is what
  > `R : CtxId → iProp Σ` was introduced for.  `disk_geom`'s row is the
  > cheap one: its three cells are `DfracDiscarded`, and a discarded ctx
  > byte is re-indexable at any ξ by the same argument
  > `TsoCtx.ctx_pointsto_of_ro` / `CtxKMap`'s `_ro_static` twins already
  > make for the static image.  `cons_res`'s is the real one: it is
  > OWNED and it is what the lock protects.

`ProofKernelvec`'s token threading is landed anyway (four block lemmas
plus the two call sites), because it is owed no matter how the caps
question is settled and it is what turned the second error into a
measurement.

#### (6) THE SHIM LEDGER, AND IT IS DOWN TO ONE LIVE USE

| what | where | count |
|---|---|---|
| live qualified use | `WpSconfLock:146` (`lock_claims`) | **1** |
| dangling symbol (deleted) | `ProofAcquire:668`, `ProofSwtch:157` (`hart_view_lb_any`) | 2 |
| surviving lemma with ZERO users | `TsoCtxShim.own_context_alloc` | 1 |
| dead `Require Import TsoCtxShim` | 19 files, all GREEN | 19 |

`BootCarveMain`'s 25 are gone with its `Require`.  **The 19 dead
`Require`s are the cheapest remaining cleanup in the tree and were left
alone on purpose**: each is one green file's cone, and none of them costs
anything but a grep hit.

#### HANDOFF

1. **The M4 line is BLOCKED on §(4)'s three-way ruling.**  Everything
   below the fork is landed; nothing above it can be built until the
   ruling picks one.
2. **`BootShared`** is written and unvalidatable until `ProofMain` greens
   (the publication's last mile).  `ProofMain:996` is the single error:
   `KptShare.kpt_inv_alloc` now takes `(B : nat)`, `kptree_own B 2 … t`
   and `llb loglen_name B`, and `kvminit`'s post is `ptree_own`
   (= `ptree_own_at (UTier cur_ctx)`).  `KptPublish.kptree_publish` is
   the gate; its premise is the DRAIN, and main's only `fence rw,rw` is
   AFTER `kvminithart`, which is the design question A6.70 left open.
3. **`ProofSwtch` (82 behind) and `ProofKernelvec` (12)** — §(5)'s two
   problems, both now at a line number.
4. Unchanged: the DMA/virtio lane, `UtResFits`, the two U-mode files.

**ACCEPTANCE for the M4 unit is unchanged** and is still gated on §(4).


### A6.82 THE FLOOR PROBE IS GREEN — AND IT NAMES A THIRD CLAIM THE
### RULING'S SKETCH DOES NOT: `win_ok` HAS TO BE RELATIVISED TOO

Executing the coordinator's ruling on A6.81 §(4) — option (a), the window
payload gains a FLOOR `Bm` (the position of the mint store), `wpin` and
`own_last` constrain only messages at or above it, and the reader pays
with `hart_view_lb K ∗ ⌜Bm ≤ K⌝`.  Step (1) of the ordered plan was
**PROBE FIRST**.

**THE PROBE PASSES.**  Twelve results, all `Closed under the global
context`; no `Admitted`, no `admit`, no `Axiom`.  Its pure layer is
LANDED as `TsoMemPa.v` §12d (421 lines, ADDITIVE — see §(4)), and the
probe file is archived at the flip workspace root as `ZZFloorProbe.v`
beside `ZZRacyProbe` / `ZZWinProbe` / `ZZPinProbe`.

**1091 of 1296, RED 9 — UNCHANGED**, over a whole-tree round that
rebuilt `TsoMemPa`'s 1257-file cone (1061 targets) from the bottom, and a
confirm round that then recompiled **exactly the nine red targets and
failed on all nine**.  That the number did not move IS the check that
§12d is additive.  No `Admitted`, no `admit`, no `Axiom`; the one `Abort`
is still `UsertrapRes.ut_res_bare_park`.

#### (1) THE RULING'S CENTRAL CLAIM IS ONE LINE, AND IT WAS ALREADY IN TREE

The shadow — *a reader whose view has passed the floor cannot resolve
below it* — is `read_down_latest` at `t' := Bm`, with visibility from
`visibleb_below`:

```coq
  Lemma read_down_shadow (h : agent) (tv Bm : nat) (a : Arch.pa) (bm : bv 8) :
    (Bm <= tv)%nat -> (Bm <= length log)%nat ->
    log_byte img log Bm a = Some bm ->
    exists (T : nat) (v : bv 8),
      (Bm <= T)%nat /\ tso_read img log h tv a = Some v
      /\ visibleb h tv log T = true /\ log_byte img log T a = Some v.
```

Four tactic lines.  `racy_read_split_fl` — the per-byte theorem
relativised — is the unrelativised proof with **two extra `lia`s**: the
timestamp the read settles on is at or above the ANCHOR, and the anchor
is at or above the floor, so both relativised gates apply to it.

**AND THE PREMISE A NON-WRITER CAN ACTUALLY HOLD NOW EXISTS**, which is
the whole point of the exercise:

```coq
  Lemma own_last_fl_anchor (Bm : nat) (h : agent) (a : Arch.pa) :
    (forall i m, (Bm <= S i)%nat -> log !! i = Some m -> pm_tid m = h ->
       msg_byte m a = None) ->
    own_last_fl Bm h a Bm.
```

*"I have written nothing to this byte since the mint"* — which a hart
that memset the page in a previous life can say and `own_last`'s
unrelativised *"I have never written this byte"* it cannot.

#### (2) THE THIRD CLAIM: `win_ok`, AND THE REASON IS `memset`

**The ruling relativises `wpin` and `own_last`.  `win_ok` is a third
history claim and it needs the same treatment — for a reason that is a
fact about the kernel's C, not about the kit.**

`TsoMemPa.read_down_win` is the REASSEMBLY: it is what makes one
timestamp serve every byte of the window, and it is what defeats the
byte-layout forgery the M4 memo §3 computed.  It takes `win_ok` — *every
timestamp writes the whole window or none of it* — **at every
timestamp**.  Measured against the source:

```c
  /* kalloc.c */   kfree(void *pa) { ... memset(pa, 1, PGSIZE); ... }
  /* string.c */   memset(...) { char *cdst = dst;
                                 for (i = 0; i < n; i++) cdst[i] = c; }
```

xv6's `memset` is a **byte loop**, so `kfree` appends PGSIZE ONE-BYTE
messages and every one of them writes a PROPER SUBSET of any window
wider than a byte.  `win_ok` is therefore FALSE below the floor **at
exactly the cell this ruling exists for**, and a floor that relativised
only `wpin`/`own_last` would leave the reassembly unprovable.

**IT STILL GOES THROUGH, AND FOR THE SAME REASON THE RULING GIVES.**

```coq
  Definition win_ok_fl (Bm : nat) : Prop :=
    forall t : nat, (Bm <= t)%nat ->
      (forall j, (j < n)%nat -> is_Some (log_byte img log t (pa_add a j)))
      \/ (forall j, (j < n)%nat -> log_byte img log t (pa_add a j) = None).

  Lemma read_down_win_fl (h : agent) (tv Bm t j : nat) :
    win_ok_fl Bm -> (j < n)%nat -> (Bm <= tv)%nat -> (Bm <= t)%nat ->
    (forall k, (k < n)%nat -> is_Some (log_byte img log Bm (pa_add a k))) ->
    read_down img log h tv (pa_add a j) t
    = match find_top h tv t with
      | Some T => log_byte img log T (pa_add a j) | None => None end.
```

`read_down_win`'s induction with the base case moved from 0 to `Bm`: at
`t = Bm` the mint store is visible (`Bm ≤ tv`) and writes every byte, so
the scan HALTS there and never asks `win_ok` about anything below.  The
step case is the original, verbatim.  `find_top_spec` / `find_top_max`
need no floor at all — they never mention `win_ok`.

> **THE RULE THIS LEAVES.**  *Relativising a history claim to a floor is
> not a premise weakening — it is a re-proof of everything that SCANS.*
> The predicates (`own_last`, `writer_pin`, `wpin`) weaken for free and
> their frame arms cost nothing; the lemma that walks the log down
> (`read_down_win`) has to learn where to stop.  The tell for the next
> instance: a claim quantified over `∀ t` with a proof by induction on
> `t` will need its base case moved, and a claim quantified over
> `∀ i, log !! i = Some m -> …` will not.

#### (3) TWO MEASUREMENTS THAT SIZE THE IRIS SIDE

- **`win_ok` lifts the reader's obligation from `n` facts to ONE.**  In
  `racy_read_window_floor` the reader's anchor premise is stated only
  about byte 0 — *"no message of mine at or above the floor writes
  `pa_add a 0`"* — and `win_ok_fl` carries it to every byte of the
  window (a message that wrote byte `j` would have had to write byte 0).
  So what a `notheld` reader must hold in Iris is one own-last fact, not
  a window of them.
- **The maintenance lemmas are the unrelativised ones with a hypothesis
  DROPPED.**  `own_last_fl_app_frame` / `writer_pin_fl_app` are the
  originals with `(Bm ≤ S i)` threaded and ignored, because a premise
  that quantifies over FEWER messages is weaker.  The store gates'
  frame arms therefore do not move.

#### (4) WHY §12d IS ADDITIVE, AND WHAT IS STILL OWED

`own_last`, `writer_pin` and `win_ok` are **literally the `Bm = 0`
instances** — `own_last_fl_0`, `writer_pin_fl_0` and `win_ok_fl_0` are
proved as `iff`s — so §12d adds names and takes none away, and nothing
that consumes them moves.  `lkcpu_not_mine_floor0` is the corollary that
matters for the eight `.bss` callers: at floor 0 the receipt is free
(`0 ≤ tv`; `TsoGhost.view_lb_0` in Iris) **and the "reader never wrote"
premise carries no floor bound at all**, so the boot mint's clients pay
nothing for the relativisation.

**STEP (2) IS NOW THE FIELD AND THE GATES, and its surface is measured:**

| symbol | refs | files |
|---|---|---|
| `TsWin` | 11 | `TsoMemPa`, `TsoCtx` |
| `win_ok1` | 16 | + one COMMENT in `BootCarve` |
| `ts_pay_win` | 11 | `TsoMemPa`, `TsoCtx` |
| `ts_ok_win` | 8 | `TsoMemPa`, `TsoCtx` |

**Two files of code.**  The dev loop is cheap — `make TsoCtx.vo` rebuilds
**five** files — and only the closing round is the 1257-file cone.

The shape `win_ok1` wants, with the two conjuncts that change and the one
that is new:

```coq
  Record ts_win := TsWin { … the six existing fields …; tw_lo : nat }.

  Definition win_ok1 img log a W : Prop :=
    a = pa_add (tw_base W) (tw_j W)
    /\ (tw_j W < tw_n W)%nat
    (* (1) RELATIVISED *)
    /\ (forall i m, (tw_lo W <= S i)%nat -> log !! i = Some m ->
          is_Some (msg_byte m a) -> (z-arm \/ cp-arm))
    (* (2) image coverage -- unchanged *)
    /\ (forall k, (k < tw_n W)%nat -> is_Some (img !! pa_add (tw_base W) k))
    (* (2b) NEW: THE FLOOR ITSELF wrote the whole window with the clear
       word, and it is a legal log position.  This is what the reader's
       anchor and [win_ok_fl]'s base case both consume. *)
    /\ (tw_lo W <= length log)%nat
    /\ (forall k, (k < tw_n W)%nat ->
          log_byte img log (tw_lo W) (pa_add (tw_base W) k) = Some (tw_z W k))
    (* (3) per agent, AT OR ABOVE THE FLOOR *)
    /\ (forall h t, tw_own W h = Some t ->
          (tw_lo W <= t)%nat /\ (t <= length log)%nat
          /\ (forall tv, visibleb h tv log t = true)
          /\ log_byte img log t a = Some (tw_z W (tw_j W))
          /\ own_last_fl (tw_lo W) log h a t)
```

> **(2b) IS A STRENGTHENING AT FLOOR 0 AND IT IS PAYABLE THERE**, which
> is the check that the degenerate case survives: at `tw_lo = 0` it says
> the ERA IMAGE holds `tw_z` across the window, and `ledger_wpay_mint`
> already has all `n` cells in hand at their own values — `tw_z` IS that
> function, and the interp's tie at a timestamp-0 element says the cell's
> value is the image byte.  The current conjunct (3) asks for the same
> fact at ONE byte; (2b) is it at all of them.

**AND CONJUNCT (3)'s VISIBILITY CLAUSE MUST BE RELATIVISED WITH THE
REST** — `∀ tv, visibleb h tv log t = true` is free at `t = 0` and FALSE
at any `t > 0` for a non-author, so it becomes
`∀ tv, (tw_lo W ≤ tv)%nat → visibleb h tv log t = true`, which
`visibleb_below` gives at `t = tw_lo`.  The reader supplies the bound
from its receipt.  That is the same pair the ruling names, arriving in
the payload rather than at the gate.

> **AND THAT INVERTS A6.79's FORCED ORDER: WITH A FLOOR IT IS
> STORE-THEN-MINT, NOT MINT-THEN-STORE.**  A6.79 ruled the order forced
> the other way, and its argument was precise: minting after the store
> leaves conjunct (3) unprovable for the other harts, because
> `own_last log h a 0` has become *"no message writes `a`"* and the
> author's own store has just falsified it.  **The floor is exactly what
> repairs that**, and it has to be the store's own position — so the
> store must have HAPPENED:
>
> - minting BEFORE the store would set `tw_lo := S (length glog)`, a
>   message that does not exist yet, and (2b) is false until it does;
> - minting AFTER it sets `tw_lo := S (length glog_before)`, the store's
>   own index — a real past message that wrote the whole window with the
>   clear word, which is (2b) verbatim, and conjunct (3) then holds for
>   every agent at `own h := Some tw_lo` (`own_last_fl tw_lo` asks only
>   about messages at or above the floor, and the only one there is the
>   floor itself, whose author's own bound `S i ≤ tw_lo` is an equality).
>
> So the leaf that item 2 needs is a **store-then-mint** leaf, which is
> the cheaper one: `wp_store_s_sconf_au_dat`'s obligation runs the store
> gate first and the mint second, both inside the one `==∗`.
>
> **The author is not a special case at the READ, either.**  The hart
> that ran `initlock` HAS written at the floor, so `own_last_fl_anchor`'s
> "wrote nothing at or above `Bm`" is too strong for it — but
> `racy_read_window_fl` at `t := Bm` needs only `own_last_fl Bm h a Bm`,
> which the author satisfies with the same equality.  Only the
> convenience wrapper `racy_read_window_floor` uses the never-wrote form.

#### HANDOFF

1. **Step (2)**: the `tw_lo` field + `win_ok1` above + `win_ok1_app_store`
   / `win_ok1_app_frame` / `ts_ok_win`, then `TsoCtx`'s three gates —
   `ledger_wpay_mint` (its premise stops being `e.1 = 0` and becomes the
   floor's own coverage, and its ORDER inverts — see §(4)),
   `ledger_store_wpay_ok` (the floor is FRAMED: both arms keep `tw_lo`
   unchanged, exactly as they keep `tw_z` and `tw_cp`), and
   `ledger_read_racy_word_ok`.  **The read gate's shape change is the
   one to look at first**: today it is VIEW-FREE (`⌜∀ tv, …⌝`, because
   `own h = Some t` with `t` visible at every view was enough), and with
   the floor it becomes `ledger_read_pin_ok`'s shape —
   `view_lb view_name loglen_name (hart_agent cpu_id) K` in the premise,
   `⌜tw_lo W ≤ K⌝` beside it, and `⌜∀ tv', (g.(gtv) cpu_id ≤ tv')%nat →
   …⌝` in the conclusion.  That makes the racy gate structurally
   identical to the pin's, which is the design rhyme showing up at the
   Iris tier as well as the pure one.  Two files.
2. **Step (3)**: item 2 with NO `SpecInitlock` fork — the floor rides the
   payload, `pipealloc` mints at its own `initlock` store with
   `tw_lo :=` that store's position, and the eight `.bss` callers take
   the floor-0 instance.  Then the atomic unit (A6.78's corrected leaf
   list) per the standing discipline.
3. **Where each reader's receipt comes from** is the one thing still to
   write down per call site: `holding()`'s `notheld` read is under
   `acquire`, whose AMO drains (`hart_view_lb_get`), so the receipt is at
   the log top and dominates any floor; the boot callers are floor 0 and
   free.  That is the ruling's "whoever can NAME a lock received its
   address through a synchronized handoff whose stamp dominates the
   mint", and it should be recorded per site as the leaves are re-proved.
4. Queued and characterised, not started: `ProofSwtch`'s stamp tie (the
   park-port family) and `ProofKernelvec`'s payload ξ-functions (the M3
   recipe on `cons_res` / `tx_res` / `disk_geom`'s pointer row) —
   A6.81 §(5).


### A6.83 THE FLOOR IS LANDED AT THE IRIS TIER — AND THE MINT STOPPED
### BEING A .bss LEMMA: ITS PREMISE IS "n CELLS AT ONE TIMESTAMP"

Executing A6.82's handoff items 1 and 2 in the flip workspace.  **Item 1
is landed whole; item 2's MACHINERY is landed whole and ADDITIVELY, and
its contract flip is deliberately not started** — it is the first half of
the M4 atomic unit and the standing discipline forbids opening it without
budget to close it.  A third piece that A6.82 did not name is landed
beside them: the `notheld` read's discharge AT THE LOCK'S OWN
PARAMETERS.

**1091 of 1296, RED 9 — UNCHANGED**, measured on the GCP VM (see §(6)):
`UserMemPt`, `UptWalkPt`, `ProofSwtch`, `WpSconfLock`, `ProofKernelvec`,
`ProofVirtioDiskRwD`, `ProofVirtioDiskIntr`, `ProofMain`, `UtResFits` —
the same nine, across two whole-tree rounds (one cold, one over the
`TsoCtx` cone).  No `Admitted`, no `admit`, no `Axiom`; the one `Abort`
is still `UsertrapRes.ut_res_bare_park`.  The shim ledger is unchanged at
**one live use** (`WpSconfLock:146`, `lock_claims`).

#### (1) ITEM 1, LANDED: `tw_lo` AND THE RELATIVISED `win_ok1`

`ts_win` gains `tw_lo : nat` (LAST field, so every `TsWin` application
grew one argument and nothing reordered), and `win_ok1` is A6.82 §(4)
verbatim: conjunct (1) at `tw_lo ≤ S i`, the new (2b) pair
(`tw_lo ≤ length log` and the floor wrote the CLEAR word across the whole
window), conjunct (3) with `tw_lo ≤ t` and the visibility clause
relativised to `∀ tv ≥ tw_lo`.  `win_ok1_app_frame` / `win_ok1_app_store`
are the originals with the floor FRAMED — both arms keep `tw_lo` exactly
as they keep `tw_z` and `tw_cp` — and the store gate
(`ledger_store_wpay_ok`) grew one parameter and one argument at its
`win_ok1_app_store` call.  **The store gates' frame arms did not move**,
as A6.82 §(3) predicted.

`TsoMemPa` needed one structural change and it is worth naming for the
next reader: **§12d's two floor sections now sit ABOVE §12c**, because
`win_ok1` conjunct (3) mentions `own_last_fl`, which is defined in
`Section floor_byte`.  The file's order is now
racy → window → **floor_byte → floor_window → floor-0** → `ts_win` /
`win_ok1` / assemble → `ts_pay` / `ts_ok`.  Nothing else moved.

**Two lemmas were added to `Section floor_window` and they are the shape
the READ gate consumes**: `racy_read_window_pin_fl_at` and
`lkcpu_not_mine_fl_at` — `racy_read_window_pin_fl` / `lkcpu_not_mine_fl`
at an ANCHOR the reader owns rather than at the floor itself.  A6.82's
closing paragraph is why: conjunct (3) hands over *"my own last write at
or above the floor is at `t`"*, and that form makes the MINT'S AUTHOR no
special case (it satisfies `own_last_fl Bm h a Bm` by the equality
`S i = Bm`), where the never-wrote wrapper would be too strong for it.

The read gates are `ledger_read_pin_ok`'s shape now, exactly as the
handoff asked: `ledger_read_racy_ok` / `ledger_read_racy_word_ok` take
`view_lb view_name loglen_name (hart_agent cpu_id) K` and `⌜lo ≤ K⌝`, and
conclude `∀ tv ≥ g.(gtv) cpu_id, …`.  **The design rhyme is now literal
at both tiers** — every history-shaped claim in this port carries a floor
and is claimed against a monotone receipt.

#### (2) THE MEASUREMENT THAT CHANGED ITEM 2's SHAPE: THE MINT'S PREMISE
#### IS `n` CELLS AT ONE TIMESTAMP, AND `.bss` IS ITS `t = 0` INSTANCE

A6.79's mint needed `e.1 = 0`; A6.82 replaced its ORDER but left the
impression that the floor-0 mint survives beside a floored one.  Measured,
**there is only one mint and the old one is its instance.**

```coq
  (* TsoMemPa *)
  Lemma win_ok1_of_latest img log base n j (t : nat) (f : nat -> bv 8) cp :
    (j < n)%nat ->
    (forall k, (k < n)%nat -> latest img log (pa_add base k) t (f k)) ->
    (forall k, (k < n)%nat -> is_Some (img !! pa_add base k)) ->
    win_ok1 img log (pa_add base j) (TsWin base n j f cp (fun _ => Some t) t).
```

`latest img log a t v` says *`t` wrote the byte AND NOTHING ABOVE `t`
DID*.  At floor `t`, conjunct (1) is therefore about the message at `t`
ALONE — and that message wrote the WHOLE window, because every byte's own
element names the SAME `t`.  Conjunct (2b) is that message read as the
floor; conjunct (3) at `own := fun _ => Some t` is `visibleb_below` plus
the same one-message argument.  **`t = 0` is A6.79's mint** (the era image
as the floor, the log empty of writes to the cell); `t = length glog` is
the store-then-mint site.  One lemma, two instances, no `.bss` special
case anywhere.

So `TsoCtx.ledger_wpay_mint` now takes the timestamp as a parameter and
its premise is the `n` cells at it; `ledger_wpay_mint1` was split into
the GHOST STEP alone (it takes the pure `win_ok1` as a premise), because
the window claim is about all `n` bytes and no single byte's cell can
establish it.  The extraction is one `iAssert (⌜_⌝)` over the cells —
the pattern the file already used for image coverage, which keeps the
spatial context intact.  Two new projections pay for it:
`ledger_latest_ok` (the interp's tie, projected) and
`ledger_wpay_floor_le` (`tw_lo ≤ length glog`, which is the fact a reader
compares its receipt against).

#### (3) ITEM 2's MACHINERY, LANDED ADDITIVELY — THE STORE-THEN-MINT LEAF
#### EXISTS AND IS GREEN

Three lemmas, one per tier, each a copy of its neighbour with the gate
swapped:

| where | name | what it is |
|---|---|---|
| `TsoCtx` | `ledger_store_win_wpay_mint_ok` | `ledger_store_win_at_ok` then `ledger_wpay_mint` at the store's own timestamp |
| `SmodeCorePt` | `word_pointsto_wpay_mint_c` | `word_pointsto_write_c` with the ledger gate swapped; the ctx word goes IN, the payload comes OUT |
| `WpSconfMem` | `wp_sd_zero_wpay_s_sconf` | `wp_sd_zero_s_sconf` on `wp_store_s_sconf_au_dat`, mint inside the one `==∗` |

**All three compiled first try**, which is A6.77/A6.81's measurement
again: the datum-parametric AUs and the `_win_` gate family are the
abstraction, and a new payer is a re-parameterisation rather than a copy.

> **THE ONE THING THE LEAF HAD TO INVENT, and it generalises.**  The
> payload is keyed by PHYSICAL address; the leaf's cell by VA; and `ppn`
> is bound INSIDE the write obligation, so the post cannot be STATED at
> `ea` there.  The fix is to state it at the translated address and carry
> the equation: `Post := ∃ pl lo, ⌜pl = ea⌝ ∗ …`, with `ktier_pin_id`
> discharging it inside the obligation and the leaf itself destructing it
> before its own continuation sees it.  **Any future leaf that hands back
> a ledger-tier resource owes this trick**, because `ktier_pin ktd ppn ea`
> is the only bridge and it lives inside the obligation.

`lo` is EXISTENTIAL in the leaf's post and that is the honest statement:
the floor is a log position no caller can name.  What a reader needs is
not its value but a receipt dominating it, and `ledger_wpay_floor_le`
plus the AMO's `hart_view_lb_get` is that comparison.

#### (4) LANDED BESIDE THEM: THE `notheld` READ, DISCHARGED AT `cpus_ptr`

`WpLock.lkcpu_read_not_mine` — the M4 memo's whole reason for existing,
now a green lemma:

```coq
  Lemma lkcpu_read_not_mine `{CID : CpuId} (g : gstate) (lk : mword 64)
      (dq : dfrac) (f : nat -> bv 8) (ts : nat -> nat)
      (own : agent -> option nat) (lo t K : nat) :
    own (hart_agent cpu_id) = Some t -> (lo <= K)%nat ->
    tso_interp_at riscv_eraGS g -∗
    TsoGhost.view_lb view_name loglen_name (hart_agent cpu_id) K -∗
    ([∗ list] j ∈ seq 0 8,
       TsoCtx.phys_ledger_wpay (pa_add (lock_cpu lk) j) dq (f j) (ts j)
         (TsoMemPa.TsWin (lock_cpu lk) 8 j lkcpu_z lkcpu_cp own lo)) -∗
    ⌜forall tv, (g.(gtv) cpu_id <= tv)%nat -> forall w : mword 64,
       tso_read_bytes g.(gimg) g.(glog) (hart_agent cpu_id) tv (lock_cpu lk)
         (N.of_nat 8) w -> w <> cpus_ptr cpu_id⌝.
```

with the payload's two byte functions FIXED here, beside `lk_cpu_val`:

```coq
  Definition agent_cpus_ptr (h : agent) : mword 64 :=      (* h < NCPU ? cpus_ptr h : 0 *)
  Definition lkcpu_z  : nat -> bv 8         := nth_byte (zero_reg : mword 64).
  Definition lkcpu_cp (h : agent) : nat -> bv 8 := nth_byte (agent_cpus_ptr h).
```

> **THE DMA AGENTS ARE NOT A GAP, THEY ARE FREE.**  `agent` is `nat` and
> includes the non-hart agents; giving them the CLEAR word as their "own
> word" makes the kit's per-agent distinguishing premise true of them by
> the same `cpus_ptr_nonzero` a free lock uses.  A DMA agent that wrote
> the cell would falsify conjunct (1), not this.

The bridge from the word-level facts (`cpus_ptr_inj`,
`cpus_ptr_nonzero`) to the kit's per-byte premises is `nth_byte_ne`
(*two words that differ, differ at a byte*, off `bv_eq_of_bytes`) — four
lines, and it is exactly the step the memo §3's layout computation says a
byte-keyed kit cannot take in the other direction.

#### (5) THE M4 ATOMIC UNIT'S SURFACE, RE-MEASURED — IT IS SMALLER THAN
#### A6.78's LIST READS, AND THE REASON IS WHERE THE RED LINE FALLS

| symbol | mentions | files | status |
|---|---|---|---|
| `lk_cpu_res` | 41 | `WpLock`, `WpLockAt`, `WpSconfLock` (+1 comment in `WpSconfMem`) | 1 green line outside `WpLock` |
| `lk_cpu_cell` | — | `WpLock`, `WpSconfLock` | — |
| `lk_fresh` | 49 | 13 | applications, per A6.80 |

**`WpLockAt:82` is the ONLY green line outside `WpLock` that destructures
the owner cell** (`rewrite lk_cpu_res_free`).  `ProofAcquire`,
`ProofRelease`, `ProofHolding` and `WpSconfLock` are all RED already, so
the reshape cannot regress them.  What the unit still owes, in order:

1. `WpLock`: `lk_cpu_res` at `phys_ledger_word` + the eight
   `phys_ledger_wpay` fragments, its four unfold lemmas, and the
   per-state constraint on `own` — **the one piece of design left**, and
   it is: *every non-holder's entry is `Some _`* (the holder's is
   revoked by its own acquire store, which is `ledger_store_wpay_ok`'s
   second arm).  A `notheld` reader is a non-holder by definition, so
   that invariant is exactly what `lkcpu_read_not_mine`'s first premise
   consumes.
2. `lock_inv_alloc` / the `newlock` family's `lock_cpu lk ↦₈ 0`
   conjunct becomes the payload; `SpecProcinit.lk_fresh` and
   `SpecInitlock`'s post follow it; `ProofInitlock` swaps
   `wp_sd_zero_s_sconf` for §(3)'s leaf at its `+0x0e` site (ONE call).
3. `WpSconfLock`'s leaves (A6.78's corrected list), `ProofHolding`'s 2
   sites, and `lock_claims`' shim ref — the shim hits zero here.

**ACCEPTANCE unchanged**: the exported lock surface does not move and the
160-file cone opens.

#### (6) THE BUILD MOVED TO THE GCP VM, AND THE NUMBERS BELOW ARE ITS

Owner instruction, mid-tranche: this workspace builds on the shared VM
now (`remote-build-gcp.md`'s non-main-tree recipe, from the fliptree
root, always under `flock /tmp/claude-gcp.lock`).  Measured here: the
cold first round is **~9 minutes** for 1125 files at `-j180` (it carried
§(1)'s `TsoMemPa`), and the second -- 1019 files, the whole `TsoCtx`
cone, carrying §(2)-§(4) -- was of the same order, against ~35 minutes
for the same cone locally.  **Both rounds report the same nine**, which
is A6.73's two-consecutive-rounds check.  `md5sum kernel-rocq/*.v user-rocq/*.v` verified
unchanged after both rounds.

> **AND IT ALREADY PAID FOR ITSELF IN A WAY WORTH RECORDING.**  The local
> round this replaced DIED OF `ENOSPC` — `/tmp` is a 13 GB tmpfs shared
> with every other session on the box, and two targets failed with
> `System error: "No space left on device"`, which `make -k` reports in
> exactly the shape a real proof failure has.  **A local red list is not
> trustworthy without a disk check.**  Local `coqc` stays for `-time`
> diagnostics; all numbers come from the VM.

#### HANDOFF

1. **The M4 unit, per §(5)** — everything below it is landed and green:
   the floor at both tiers, the store-then-mint leaf, the `notheld`
   discharge at `cpus_ptr`, all four read gates, both store gates.  The
   only open design is §(5) item 1's `own` invariant, and it is one
   sentence.
2. **The 19 dead `Require Import TsoCtxShim` lines** (A6.81 §(6)) are
   now CHEAP — each was one green file's cone at 35 min and is one
   `-j180` round at 6 min.  Sweep them with the next tranche that
   touches the tree, not on their own.
3. Unchanged and queued: `ProofSwtch`'s stamp tie, `ProofKernelvec`'s
   payload ξ-functions (A6.81 §(5)), the virtio pair, the two U-mode
   files, `ProofMain`'s last mile.


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
