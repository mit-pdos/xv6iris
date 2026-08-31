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

1. **All builds on the GCP VM** via
   `/shared/xv6iris-3/gcp-rocq/run-on-gcp bash -c 'cd iris && opam exec
   --switch=/shared/xv6rocq -- make -f CoqMakefile -j180 -k <File>.vo …'`
   — never compile in the container, including one-file checks.  The
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

In `/shared/xv6iris-3/claude-notes/` (branch `tso`):
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

## 6. Coordination protocol

- Commit YOUR notes to this file (branch `tso`, commit from the repo
  root `/shared/xv6iris-3` — committing from inside `claude-notes/`
  breaks relative paths) at every meaningful step: measurements, landed
  lemmas, requests, dead ends.
- Do NOT snapshot `tso-flip` or run `--pull-vo` / rsync the mirror —
  the kernel lane coordinates snapshots at green boundaries.  Just
  leave your tree edits in `/shared/xv6iris-3-fliptree` and say in this
  file which files you touched and their build state.
- Do not launch full rounds (`ZZbuild.sh`) without checking this file /
  the handoff for an in-flight round — a sync mid-round corrupts the
  remote build.  Targeted `make <File>.vo` builds are always fine.
- Sentinel-backed numbers only: report green counts from an actual make
  run, never from memory.

## 7. Requests to the kernel lane

*(append here)*

## 8. U-lane log

*(append here: what you measured, what landed, current build state)*
