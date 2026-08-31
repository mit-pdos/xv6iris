# tso-umode-lane.md — brief for the USER-MODE CONE agent (§0.37′)

*(Written 2026-08-31 by the kernel-lane session at r60, snapshot
`86e7eca4c7b9f` on `tso-flip`, 1265/1304, red roots 4.  Owner's
instruction: "work through the generic user-mode WP theorem (as opposed
to the user-mode proofs of specific binaries, which you shouldn't
convert to TSO yet)".)*

## 0. Mission and scope

Make the GENERIC user-mode machinery green under the TSO (Ztso) machine:
the U-mode step engine, instruction fetch, memory access, and the
user-page-table walk — the theorem that says "a U-mode step over
`utlb_inv_pt` + the process's memory behaves like the SC one did".

- IN scope: `UptWalkPt.v` (:679 is a red root), `UserMemPt.v` (:427 is
  the other), and their engine-side cone: `UserFetchPt`, `UserMemAccess`,
  `UserMemMis`, `UserMemArms*`, `UserMemClassify*`, `UserActiveClass`,
  `UserMemCert`, `UserFaultCert`, `UmodeFetch`, `WpUmodeStep`,
  `UmodeCap`, `UserExec`, `UserFrame`, `UptTree`, `UserPtTree`,
  `UserBytes`, `ProcPtOwn` (only if forced — it is big and mostly green).
- OUT of scope (owner ruling): the per-binary user proofs and their
  links — `ProofUser*.v`, `LinkUser*.v`, `ProofUservec/ProofUserret`
  and the trampoline-proof files (`UserretPt`, `UservecPt`,
  `UserretEntryPt`, `UservecExitPt`, `TrampStepPt`) — leave red; they
  are consumers of your theorem and will be converted later.  If your
  work reveals their needed interface, RECORD it here, do not edit them.

## 1. Ground rules (non-negotiable, from the owner and hard experience)

1. **All builds on the GCP VM** via `run-on-gcp` (from YOUR OWN clone's
   `gcp-rocq/` — see §6; never the kernel lane's copy):
   `<your-notes-clone>/gcp-rocq/run-on-gcp bash -c 'cd iris && opam exec
   --switch=/shared/xv6rocq -- make -f CoqMakefile -j180 -k <File>.vo …'`
   run with your WORK checkout as cwd — never compile in the container,
   including one-file checks.  The
   sync pushes local edits and DELETES remote-only files; logs get
   `*.aux` names; read logs with `--no-sync`.
2. **Measure before designing.**  Read the actual error, the enclosing
   lemma, and the PRE-FLIP proof of the same lemma before inventing
   anything.  A ported proof that needs a NEW hypothesis means the port
   is wrong (owner rule).
3. **Zero admits in landed code.**  To measure something deeper in the
   red cone: copy the file aside, replace the enclosing lemma's proof
   with `Admitted.`, compile, then RESTORE and delete every scratch
   `.vo` the experiment produced on the VM (marker under /tmp, not in
   the tree).
4. **Σ-level design points are the owner's.**  If you conclude a new
   ghost, a new `ts_pay` arm, or an interface change to the context/
   ledger layer is needed, STOP and surface it (write it up here and in
   `tso-port.md` as a question); do not build it.
5. **Known tactic traps** (each cost hours once): never `apply` a
   structural/leaf lemma against a named Iris hypothesis that can
   diverge — dispatch syntactically; hoist side conditions out of
   `ltac:( )` application position; `iEval (rewrite …) in "H"` instead
   of bare `rewrite` when a big_op could unify with `seq 0 4096`;
   ssreflect `rewrite lemma` side conditions come FIRST; `set_solver`
   over big unions can take minutes — use explicit union lemmas; python
   heredocs eat trailing `/\` — use quoted `cat` heredocs for Coq text.

## 2. Read these before editing anything

In `claude-notes/` of your own clone (branch `tso`):
- `durable-notes.md` — build system, cross-cutting gotchas.
- `projects/tso-port.md` — the rulings.  Minimum: §0.7′ (explicit-index
  rule), §0.37′ (why this cone was left red), §0.44′ (process contexts
  are twins; fork mints a running twin), §0.46′ (A/D write-backs are
  REAL TSO writes — no preset, no kernel patch), §0.47′ (`ctx_values`,
  the racy-read rule).
- `projects/tso-machine-flip.md` — A6.135 §§1–5 (the kernel-table
  design and what got built; your cone reuses the vocabulary but mostly
  NOT the racy machinery — see §3 below).
- `projects/tso-handoff-current.md` — current certified state.
- File headers: `UptTree.v`, `UptWalkPt.v`, `UserPtTree.v`,
  `WpUmodeStep.v` (§ "utlb_inv_pt + umem in, ONE byte map out"),
  `ProcPtOwn.v` (the proc_pt_own ↔ utlb_inv_pt duality).

## 3. The TSO machinery you need (and the key simplification)

**The machine** (`TsoMemPa.v`): memory is an era image plus an
append-only log of write messages (`pwmsg`); each hart has a view; a
read (`tso_read`) scans down from the top for the newest VISIBLE write
(`visibleb`: position ≤ view, OR the hart's own message — **reads
always see the hart's own writes**).  The state interpretation
(`tso_interp_of` / `tso_interp_at`) ties a `gen_heap` of flat bytes to
the log through a per-address element map (`ts_name` cells carrying a
stamp + an optional "arm": pin/window/release payloads).

**Contexts** (`TsoCtx.v`): a context ξ has a bound B (positions ≤ B are
visible to any hart running ξ) and a monotone dirty set D (the
positions ξ itself wrote).  `ctx_phys_pointsto ξ a dq v` = the flat
byte + its stamp cell + a justification "stamp ≤ B ∨ stamp ∈ D".
`own_context ξ` is the run token.  `ctx_phys_word_pointsto` is the
8-byte form.  Word stores go through the ctx store gates in
`HartMStore.v` (`wobl_ram_ctx` — the NON-exclusive store payer that
registers the new stamp in ξ's dirty set).

**THE KEY FACT FOR YOUR CONE**: the user page table and the process's
memory are **context-owned, single-writer** (`UTier ξ` slots =
`ctx_phys_word_pointsto`; `utlb_inv_pt` owns satp/tlb/tree outright).
Nobody races you.  Reads-own-writes + the bound make the owning
context's view of its own table effectively SC.  So your port is a
**tier translation** (raw physical `↦ₚ` → ctx tier), NOT an invariant
design problem.  You should almost never need: `pin`s, `kpt_slot_pin`,
`cv_boot_cred`, `pin_ok_author`, the publish telescopes, or the ghost
hooks.  Those are the KERNEL table's shared-reader machinery (A6.135).
If you find yourself reaching for them, re-read §0.44′/§0.37′ first and
suspect the design.

**§0.44′ (twins)**: a process's table cells are registered to the
process's context; fork mints a running twin and moves rows.  The
generic U-mode theorem runs at the ambient `XI : CurCtx` (`cur_ctx`) —
the swtch/park story of WHICH context is current is the forkret-park
lane's problem, not yours; take `own_context cur_ctx` as given by the
capability the engine threads (it lives inside `sie_cap`, borrowable
via `sie_cap_gpr_own_ctx_acc`).

**§0.46′ (A/D write-backs)**: the hardware walker's A/D bit write-backs
are REAL TSO writes.  On the USER table they are writes to ξ-owned
cells by the hart RUNNING ξ — i.e., ordinary ctx-tier stores (dirty-set
registered), NOT the exclusive pinned gate the kernel table needed.
`PtTreeAdue.v` has the ADUE absorption vocabulary; `UserExec.v`'s
header claims the write-backs are "absorbed" — measure whether that
absorption survives the flip or needs the ctx store payer threaded.

**Useful landed lemmas you MAY reuse** (green, stable): everything in
`TsoCtx.v` (ctx load/store gates, `ctx_word_pointsto` lemmas,
`ctx_absorb_lb`), `HartMStore.wobl_ram_ctx`, `CtxValues.v`'s
`big_sepL_seq_exist` (bounded choice), and — only if you genuinely need
an interp-exposing moment at an instruction — the A6.135 ghost-hook
pattern (`HartRegNode.wp_hart_regwrite_gs`, `HartBarrier.ghost_step`).

## 4. The two roots, measured (r60 log, verbatim)

**`UserMemPt.v:427`** — a U-mode byte-run store still written at the
RAW tier:
```
iSpecialize: cannot instantiate
  (pa_add pa x ↦ₚ b ==∗
   gen_heap_interp (<[pa_add pa x := nth_byte v x]> (foldr … m xs)) ∗
   pa_add pa x ↦ₚ nth_byte v x)
with (ctx_phys_pointsto XI (pa_add pa x) (DfracOwn 1) b).
```
The hypothesis is already ctx-tier; the store loop's inner wand still
expects `↦ₚ` + a bare `gen_heap` update.  Pre-flip this was the flat
`phys_update` fold; under TSO a store must go through the ctx store
payer (one log message for the run, dirty-set registered) — the shape
`HartMStore.wobl_ram_ctx` / the `TsoCtx` word-store gates provide.
Look at how the KERNEL-side byte runs were converted (grep the A6.22
note in `WpSconfSfence.v` and the `swp_hmrun_of_exec_reg` remark about
context-indexed byte tiers) and at what the enclosing lemma's SC
version did.

**`UptWalkPt.v:679`** — the U-mode instruction-fetch translate:
```
iSpecialize: cannot instantiate
  (own_context XI -∗
   upt_res_pt uroot tfp um tv -∗
   hreg_frame (s_rs …) s_Drw -∗ hreg_frame_ro Df (s_rs …) s_Dro -∗
   SWP translateAddr (Virtaddr va) (InstructionFetch ())
   {{ r, ⌜r = Ok (Physaddr pax, PBMT_PMA, init_ext_ptw)⌝ ∗ … }})
with …
```
A shape drift in the walk-lemma chain around `upt_res_pt` /
`own_context` (the callee's premise list moved under the flip).  Find
the callee's current statement, diff against the call, and expect the
fix to be threading (the token + residue order), not new theory.  The
S-mode twin of this chain (`SmodeCorePt` / `HartSTrans` /
`swp_translate_kpt`) is GREEN — use it as the reference for how the
translate chain looks post-flip, remembering your slots are UTier so
the credential machinery (`cv_boot_cred` etc.) does NOT appear; the
UTier walk reads through `ctx_phys_word_pointsto` with the token.

Suggested order: fix `UserMemPt` first (self-contained store-loop
surgery), then `UptWalkPt`, then `make -k` the engine cone
(`UserFetchPt`, `UserMemAccess`, `UserMemMis`, `UmodeFetch`,
`WpUmodeStep`, `UserExec`) and iterate on what falls out — expect the
same two error classes (raw-tier stores; drifted translate threading)
repeated.

## 5. File ownership — DO NOT CROSS (active kernel-lane work)

The kernel lane (this author) is concurrently working on:
- `ProofKernelvec.v` / `SpecKerneltrap.v` / `ProofKerneltrap.v` (the
  §0.39′ red, mid-measurement),
- the secondary wiring: `ProofMain.v`, `ProofMainSecondary.v`,
  `StartedInv.v`, `SpecMainSecondary.v`, `BootChain.v`, `BootShared.v`,
  `LinkMain*.v`, `SystemAdequacy.v`,
- and owns the shared TSO/KPT infrastructure: `TsoMemPa.v`,
  `TsoGhost.v`, `TsoCtx.v`, `CtxValues.v`, `CtxPinMint.v`,
  `KptPublish.v`, `PtTree.v`, `KptShare.v`, `KptTree.v`, `HartSKpt.v`,
  `HartMStore.v`, `HartRegNode.v`, `WpSconfCsr.v`,
  `SpecKvminithart.v`, `ProofKvminithart.v`.

**Do not edit any of those files.**  If your cone needs a change in one
(e.g., a new ctx-tier lemma in `TsoCtx.v`, or a `PtTree.v` UTier
tweak), write the exact statement you need into THIS file under
"requests to the kernel lane" and continue on something else; the
kernel lane will land it.  `_CoqProject` additions: append only, and
note them here.

Also frozen for you (green, other lanes' landed work): `StartedInv.v`,
`VirtioProto.v`, `DiskInv.v`, `DiskAvail.v`, `WpLock.v`,
`WpSconfLock.v`, `ProofForkretPark.v` (red, but it is the scheduler
lane's).

## 6. Checkout, branches, and coordination protocol

**Your own directories, your own branch — never the kernel lane's.**
The kernel lane's directories are OFF-LIMITS entirely:
`/shared/xv6iris-3` (its notes/tooling clone), `/shared/xv6iris-3-fliptree`
(its work tree), `/shared/xv6iris-3-fliptree-backup` (its mirror), and
`/shared/tmp/virtio` (its scratch).  Set up two checkouts of your own:
(a) a clone of the repo at branch `tso` (for `claude-notes/` and
`gcp-rocq/run-on-gcp`), (b) a work tree materialized from `tso-flip`
@ r60.  Pick your own scratch dir (e.g. `/shared/tmp/umode`).

  `tso-flip` is a SNAPSHOT
branch: every commit on it is a whole-tree state (temp-index
`commit-tree`, `.vo` binaries included), not a diff — so a snapshot
pushed from a tree that lacks the kernel lane's latest edits would
silently revert them.  Therefore:

- Bootstrap your checkout from `tso-flip` @ r60 (`86e7eca4c7b9f`) into
  a directory that is NOT `/shared/xv6iris-3-fliptree` (e.g.
  `/shared/xv6iris-3-umode`).  The snapshot carries the matching `.vo`
  set, so your first VM build is warm-ish.  `run-on-gcp` derives the
  remote build tree from your local path, so a distinct directory name
  automatically gives you your own VM tree — no build collisions with
  the kernel lane.
- Push YOUR whole-tree snapshots (same temp-index recipe, drop
  `iris/.lia.cache` with `git update-index --force-remove` — it is
  229MB) to your OWN branch **`tso-flip-umode`**, parented on the r60
  snapshot.  Never push to `tso-flip`.
- At green boundaries the kernel lane merges your u-cone files into the
  main tree and the combined state lands on `tso-flip`.  Keep the file
  fences of §5 and the merge is a plain copy of disjoint files.
- To PICK UP kernel-lane progress mid-flight (e.g. a landed request
  from §7): copy the named files from the latest `tso-flip` snapshot
  into your tree — do not rebase your whole tree onto it unless the
  kernel lane says the snapshot is a certified round.
- `_CoqProject`: append-only, and record every addition in §8 so the
  merge is mechanical.

**Notes**: commit your entries in THIS file to branch `tso` from YOUR
OWN clone (commit from that clone's repo root; committing from inside
`claude-notes/` breaks relative paths), and `git pull --rebase` before
pushing (the kernel lane pushes to `tso` too) — at every meaningful
step:
measurements, landed lemmas, requests, dead ends, build state.

**Builds**: targeted `make <File>.vo` on your own tree any time.  Full
rounds (`ZZbuild.sh`) only on your own tree/tmux session (pick a
distinct session name).  Never `--pull-vo` into or rsync the kernel
lane's tree or its mirror `/shared/xv6iris-3-fliptree-backup`.

**Numbers**: sentinel-backed only — report green counts from an actual
make run, never from memory.

## 7. Requests to the kernel lane

None so far — every edit stayed inside the §5 fences.  Two INTERFACE
records for the later (out-of-lane) conversions, no action needed now:

- **The trampoline tranche (A6.61)**: the `tramp_tr_obl` instances at the
  user table now live in **`UptWalkTramp.v`** (new file, appended to
  `_CoqProject`, DELIBERATELY RED — it is the §0.37′ red root's successor).
  When the A6.61 token-parameter tranche runs, it edits that file plus
  TrampStepPt/Pt2WalkPt/TransPt/UservecExitPt/UserretEntryPt; the
  trampoline-proof files additionally need `Require Import UptWalkTramp`
  (UserretPt:195 now fails on `wp_instr_u_pt` not found, and Pt2WalkPt:427
  on the un-threaded token — both were red before, the messages moved).
  `UptWalkPt.utf_translate` (the trapframe leaf) is fixed IN PLACE: it now
  takes `own_context XI` between `resv_frag` and `upt_res_pt` and hands it
  back in the post, exactly like `swp_translate_upt`.
- **ProofUser (per-binary side)**: the generic theorems in
  `UserActiveClass.v` (`active_class_intro`,
  `user_step_obligation_active_holds`, `wp_user_exec_full`) gained ONE
  section premise, the residue token accessor
  `Rut_ctx : forall pt', ⊢ Rut pt' -∗ own_context cur_ctx ∗
                            (own_context cur_ctx -∗ Rut pt')`.
  For the concrete `Rut := fun pt => ∃ ksp, usertrap_res pt ksp` the
  accessor is the `own_context cur_ctx` conjunct of
  `UsertrapRes.ut_trap_parked` ("the token rides the parked twin") — a
  two-line borrow.  ProofUser:75 fails on the new premise; it is the
  §0-OUT per-binary lane's to supply.

## 8. U-lane log

**2026-08-31 (session 1): the §0.37′ cone is GREEN — 1279/1305, snapshot
`tso-flip-umode` @ `9bfb42d9ed4` (parent r60 `86e7eca4c7b`), zero admits.
CERTIFIED by a CLEAN round (rm all iris `.vo`, full `ZZbuild.sh`):
GREEN=1279/1305, 26 red, error roots exactly ProofForkretPark:318 +
ProofKernelvec:1704 (other lanes), UptWalkTramp:101 (deliberate),
Pt2WalkPt:427 / UserretPt:195 / ProofUser:75 (out-of-scope, §7).**

Baseline reproduced first: fresh tree from the r60 snapshot rebuilt to
exactly 1265/1304 with the four certified red roots.  Two tooling facts
worth keeping:
- A tree materialized by `git archive | tar` gets ONE mtime for every
  file, so a stale snapshot `iris/.CoqMakefile.d` (r60's predates
  CtxValues.v) is treated as current and `make -j` compiles new files in
  garbage order ("Cannot find a physical path bound to logical path …" at
  files that compiled before their Requires).  Delete
  `.CoqMakefile.d`/`CoqMakefile*` after materializing and let make regen.
- Keep a locally-generated `CoqMakefile` in the tree: `run-on-gcp`'s
  `--delete` sync removes the VM's regenerated copy on every push if the
  local side lacks it (same class as the handoff's `*.aux` gotcha).

**UserMemPt:427 dissolved by deletion, not conversion.**  Measured: the
SC-era interp-level composers (`udata_own_upd`, `udata_read_word_g`,
`udata_own_store_g`, `user_pt_load/store_data_g`, UserMemAccess §2/§6/§7/§8
wrappers, UserMemMis's MisWindow/MisUser sections, ALL of UserFetchPt's
Iris sections) have ZERO live consumers on the flip tree — every
cross-file reference is a comment.  The port had already replaced that
route: the safety tier consumes PURE exec+goodmb pairs (UserFetchCert /
UserMemCert / UserFaultCert) through `HartMemRun.swp_hmrun_of_exec`, whose
RAM arms pay the ledger (`bytes_own` = ctx-tier map; `bytes_own_wobl` =
the one-message store gate that replaced the per-byte fold — its header
says so explicitly).  So the fix was to DELETE the dead composers; the
pure lemmas (heavily consumed: exec_/goodmb_ pairs, the GenRead/GenWrite
sections, wchain) all stayed.  UserFetchPt shrank to
`u_fetch_fault_flavor` + imports.  If an interp-level udata store is ever
wanted again, `udata_own data = ∃ dm, ⌜dom dm = data⌝ ∗ bytes_own dm`
makes `bytes_own_wobl` serve it directly.

**UptWalkPt:679 split.**  §§0–4 (upt_tmem, upt_res_pt, upt_swp_open/close,
`swp_translate_upt`) were already green text; §6's `utf_translate` needed
only the token threading (done in place).  §5 (the □-shaped
`tramp_tr_obl` instances — the A6.61 blocker recorded verbatim inside
TrampStepPt.v at the failure point) moved to `UptWalkTramp.v` (red, §7).
The engine cone (`WpUmodeStep`/`WpUmodeStore` etc. — delisted from
`_CoqProject` on the flip tree, so not built) consumes only
upt_swp_open/close, which stay green in UptWalkPt.

**UserActiveClass:1126 — the ONE design point, resolved inside the lane.**
The fetch/execute hmrun bridges (`swp_fetch_of_pure`,
`swp_execute_of_pure`) needed `own_context cur_ctx` for
`swp_hmrun_of_exec`.  `active_class` is a □-obligation (cannot capture
the linear token), but the class holds `Rut pt` at every bridge site, and
the token's ruled home across a user excursion IS the kernel residue
(`ut_trap_parked`'s `own_context cur_ctx` conjunct, M2 ruling quoted in
UsertrapRes.v).  So the section takes the `Rut_ctx` borrow accessor (§7)
and `u_swp_fetch` borrows before the fetch bridge, threads the token
through both execute bridges, and restores into `Rut` before each arm
close.  No Σ-level change, no new ghost, `UserStepFull`/`UserExec`
untouched.

Current red roots (whole tree): ProofForkretPark:318 + ProofKernelvec:1704
(other lanes, untouched), UptWalkTramp:101 (deliberate, §7), and the
out-of-scope trampoline/per-binary files behind them (Pt2WalkPt:427,
UserretPt:195, ProofUser:75 — see §7 for what each needs).

`_CoqProject` delta: `UptWalkTramp.v` appended at end (only change).

**KERNEL-LANE MERGE NOTE (2026-08-31): `tso-flip-umode` @ `9bfb42d9ed4` merged into the main tree and certified as r61 (`72bb94f1300a3`, 1279/1305) on `tso-flip`.  ZZchain.sh path change and the snapshot-materialization artifacts (sail-riscv, .CoqMakefile.d) were NOT adopted; everything else was.**
