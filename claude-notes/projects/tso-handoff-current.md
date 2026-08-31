# TSO port: LIVE HANDOFF CHECKPOINT (2026-08-31, r63 banked — SUCCESSION DOC)

This file is the resumption point for a FRESH agent taking over the TSO
port.  It is updated at green boundaries; trust the newest git commit of
it on branch `tso`.  The previous coordinator ran out of credits at r63;
a successor agent TAKES OVER THE PRIMARY TREE AND THIS ROLE (the
lane-isolation rule — own clone, own branch — applies to CONCURRENT
side lanes, not to the successor of the coordinator itself).

Reading order for a fresh agent:
1. `claude-notes/README.md`, `durable-notes.md`, `remote-build-gcp.md`.
2. This file, top to bottom.
3. `projects/tso-port.md` — the OWNER RULINGS (§0.x′).  Minimum set:
   §0.7′ §0.11′ §0.12′ §0.23′ §0.25′ §0.27′ §0.35′ §0.36′ §0.37′ §0.38′
   §0.39′ §0.41′ §0.42′ §0.44′ §0.46′ §0.47′, and the ProofForkretPark
   crossing write-up (search "THE PARK'S SECOND CROSSING").
4. `projects/tso-machine-flip.md` — the A6-series measured record
   (A6.119–A6.139).  Skim headers; read in full the sections named below.
5. `projects/tso-umode-lane.md` — the user-cone brief + its §7 interface
   records (the next conversion's starting point).
6. `projects/main-tso-readiness.md` — the SEPARATE main-branch port
   track (another agent's; not yours unless told).

## 1. WHERE THE PROJECT STANDS (r63, certified 2026-08-31)

**GREEN = 1283/1305 iris files, zero admits, zero axioms** (grep-verified;
`Admitted` appears only in comments).  model-xv6iris, kernel-rocq,
user-rocq all build clean.  Proven under the TSO machine end to end:

- the TSO machine itself (`TsoMemPa`), the context/ledger tier
  (`TsoCtx`, `CtxValues`), locks + acquire/release floors, scheduler +
  swtch + the park box, fork/exec/exit/wait, the whole FS + virtio
  (incl. the §0.41′ release-cell used-index and two-message completion),
  console/UART, the kernel page table end to end (A6.135), secondary
  boot wiring (A6.138), and the ENTIRE trap-handler chain — kerneltrap,
  kernelvec, usertrap + links (A6.139, landed this round).
- the GENERIC user-mode step theorem (fetch/mem-access/user-walk
  engine) — u-mode lane, merged at r61.

**The 22 red files fall into exactly three buckets:**

**A. Trampoline + per-binary user cone (~15 files; owner ruled "do not
convert yet" — the ruling may be lifted; ask).**  Two jobs:
  (1) the trampoline TOKEN TRANCHE: `tramp_tr_obl` (a □-obligation,
  cannot capture a token) must take/return `own_context` as an inner-∀
  parameter.  Edits `UptWalkTramp` (deliberately red — the instances are
  parked there), `TrampStepPt`, `Pt2WalkPt`, `TransPt`, `UservecExitPt`,
  `UserretEntryPt`; the trampoline-proof files then need
  `Require Import UptWalkTramp`.  Mechanical threading, ~7k lines.
  (2) the per-binary conversion proper: `UserretPt:195` (fails on
  `wp_instr_u_pt` not found — the u-lane renamed that layer),
  `UservecPt`, `ProofUserret`, `ProofUservec` (~5k lines, UNMEASURED),
  plus `ProofUser:75` which needs only the recorded `Rut_ctx` accessor
  (a two-line borrow from `UsertrapRes.ut_trap_parked`).  Interface
  needs are pre-recorded in `tso-umode-lane.md` §7.

**B. `ProofForkretPark:318` — the one genuinely hard open problem.**
Forkret's cap mints the child's fresh context; every ξ-dependent global
arrives at the PARKER's ξ; a fresh context cannot hold `inv`/`is_lock`
handles; both context-motion laws are ξ-preserving by design.  Fully
characterized in `tso-port.md` with two ranked ways out.  Way 1
(restate `wp_forkret_gen_body` with an explicit `ξg` for the globals —
`procs_inv`, `park_globals`, `proc_lock_res`, `is_kstack` — thread-local
rows stay ambient) needs NO new machinery but reopens the green
`ProofForkret` (~1900 lines; risk spot = the boot arm where
kexec/fsinit mix the two contexts).  It is a spec change ⇒ NEEDS THE
OWNER'S SIGN-OFF FIRST.  Way 2 (λ-payload sweep) is measured-blocked on
`CtxMorph proc_lock_res` and `CtxMorph ftable_res`.

**C. The boot/adequacy tail (blocked-only, mostly written).**
`LinkMain`, `BootChain`, `BootShared`, `FsAdequacyImg`,
`SystemAdequacy` + Link stragglers have no errors of their own — they
sit under A and B (the kernelvec leg of their cone is PAID as of r63).
Their TSO text (incl. the A6.138 deposit-wand edit in `BootChain`) was
written while unbuildable ⇒ expect a modest first-compile fallout tail.
NOTE: the old scratch-admit measurement trick NO LONGER WORKS here —
`UserretPt` fails on a missing REFERENCE, which admits cannot skip.

True error roots (r63): `ProofUser:75`, `UserretPt:195`,
`Pt2WalkPt:427`, `ProofForkretPark:318`, `UptWalkTramp:101`(deliberate).

## 2. THE LEGS (trees, branches, dirs)

- **T-leg / PRIMARY fliptree**: `/shared/xv6iris-3-fliptree`.  GitHub
  branch **`tso-flip`**, last snapshot **r63 = `bfe7168564bc0`**
  (chain: r59 `081a27ff178f` → r60 `86e7eca4c7b9f` → r61
  `72bb94f1300a3` → r62 `05ff8bf16c8e4` → r63).  VM build tree
  `/mnt/rocq/trees/_shared_xv6iris-3-fliptree` (incremental, warm).
  Durable mirror `/shared/xv6iris-3-fliptree-backup` (rsync at green
  boundaries; current at r63).  Local tree carries the pulled r63
  `.vo` set (1309 files), so it matches the build.
- **U-mode lane**: branch **`tso-flip-umode`** @ `9bfb42d9ed4`
  (parent r60); MERGED into the primary at r61.  Its mission (generic
  U-mode theorem) is COMPLETE.  The per-binary conversion (bucket A) is
  the successor job — if it goes to a side lane, that lane gets its OWN
  clone/dir/branch per the isolation rule in `tso-umode-lane.md` §6.
- **Notes**: `/shared/xv6iris-3`, branch **`tso`** — notes + `gcp-rocq/`
  only; commit+push at every meaningful step (`git pull --rebase` first;
  other lanes push here too).
- **Main-side port**: `main-tso-readiness.md` (Slice 5 demarcated) — a
  SEPARATE agent ports the TSO vocabulary onto `main`.  Not blocking
  the fliptree proof.
- **Historical**: `/shared/xv6iris-3-kpttree` (frozen; K15 preset
  strategy + its merge RETIRED by §0.46′ — A/D write-backs are modeled,
  see memory/notes), `/shared/xv6iris-3-intrtree` (parked; SpecDevintr
  long since merged).  `/shared/tmp/virtio`: scratch; the A6.126 WIP
  patch there is SUPERSEDED (all landed by r50–r58); still holds
  `admit_at.py` and file-copies used for old measurements.

## 3. TSO MACHINERY MAP (what the next agent must know)

The measured record is the A6-series; this is the orientation layer.

**The machine** (`TsoMemPa.v`): memory = era image + APPEND-ONLY
message log (`pwmsg`); each hart has a VIEW (log position).  `visibleb`:
a message is visible if its position ≤ your view OR it is your own
(reads-own-writes = TSO store forwarding).  `tso_read`/`read_down` read
down the log through visibility.  `pin_ok img log a B Sv`: byte `a`'s
value is determined for every view ≥ B (the "pin"); anchor-generalized
(`pin_ok_author` takes any anchor p ≥ B).  A store appends ONE message
per instruction (window form, `write_bytes`), never per-byte folds.
§0.46′: the page-walker's A/D write-backs are REAL TSO writes.

**Contexts** (`TsoCtx.v`): a context ξ = bound B + monotone dirty set D.
`own_context ξ` is the RUNNING token (CpuId-indexed — one per hart-side
identity).  `ctx_phys_pointsto` has a clean arm (value pinned since B)
and a dirty arm (own write recorded in D; the dirty fragment is the
FULL element — forgetting it is irreversible).  `ctx_dom` = domination
(ξ′ extends ξ); `CtxMorph R` transports R along ctx_dom; `CtxMove R`
(`{CID}`-indexed) moves R between two live contexts via both tokens
(`==∗`).  Tactics `ctx_morph_solve`/`ctx_move_solve` dispatch
SYNTACTICALLY — never `apply` a structural/leaf instance against a
named hypothesis: unification dives guarded fixpoints and hangs 10–20
min (this bit again at A6.139/SchedCtx; root-cause pattern: a payload
row left at ambient XI becomes ξ-varying under a λ — PIN rows at the
box's own ξ, e.g. `p_sched`'s `trap_csrs (XI := ξ)`).

**ctx_values** (`CtxValues.v`, §0.47′ — the racy-read rule): the
abstraction for values read WITHOUT synchronization.  `cv_touch`/
`ctx_values` mint per-position value witnesses; `cv_own st v B` = the
author's own record at stamp B; `cv_boot_cred B` = `view_lb … B ∨
(⌜hart_agent cpu_id = 0⌝ ∗ llb loglen_name B)` — "either I can SEE
position B or I am the boot hart and B is below the log length".  This
is what lets boot-hart-written page-table slots be read by secondaries:
`cv_slot_read_ok` turns the credential into a read gate.  Used
throughout A6.135's `kpt_slot_pin` (per-byte ∃Ba ≤ B with a 3-arm
credential: Ba=0 / author's own / view_lb).

**Locks** (WpLock + friends): `lk_floor` = the holder's log-position
floor; its creator arm is the ctx tower's OWN dirty witness
(`ctx_wrote`) — §0.38′ (received-or-wrote) ∘ §0.36′(a) (author rides
its own write).  The AMO leaf exports the win with its floor
(`lock_pay_won`); acquire absorbs via `TsoCtxAbsorbLb.ctx_absorb_lb`.
`lock_finisher` is two-part (prelude at entry, body at the store).
λ-payloads: `ticks_res`/`cons_res`/`disk_res`/`proc_lock_res` are
context-λs (`*_at` twins + `CtxMorphTac.v` driver).

**Release cells** (§0.41′, A6.126): the virtio used index is an
author-only window arm (`tsp_rel`) with a view-CARRYING load leaf
(`_au_rel` — the read yields the writer's position); the device's
completion is a second message via `ledger_store_rel_ok`.

**Parking / twins** (§0.42′/§0.44′, A6.127): `ctx_park : own_context ξ
==∗ ∃T, ctx_parked ξ T` and `ctx_resume` are ξ-PRESERVING (identity =
`ctx_bound_name ξ`).  Fork mints a RUNNING TWIN of the parker
(`own_context_twin`) and moves rows; stamp-0 alloc is boot-only.  The
scheduler contexts never park; parked continuations live in the park
box (`SchedCtx.p_sched`), whose rows are pinned at the box's ξ.  The
fresh-context-cannot-hold-handles wall is bucket B above.

**Kernel page table** (A6.135): `kpt_slot_pin`, `kpt_creds := ∃B,
kpt_bound B ∗ cv_boot_cred B`, boot telescope `kptree_publish_boot`
(unconditional per-slot own-stamp mints), the satp-write ghost hook
(`wp_csrw_satp_s_sconf_gs` — the establishment hook Pk/Qk contract in
SpecKvminithart).  Secondaries DERIVE their creds (A6.138): the started
cell's payload is position-indexed (`P : nat → CtxId → iProp`), the
store obligation fires at `S (length log)`, and the spinner gets
`∃pos, P pos cur_ctx ∗ view_lb pos` — from which
`view_lb_le + cv_boot_cred_view + kpt_creds_intro` mint kpt_creds.

**Interrupt handlers** (A6.139 — READ THIS BEFORE TOUCHING IntrDefs/
WpIntrInv/SpecKernelvec/ProofKernelvec/ProofUsertrap): the handler
contract is a FAMILY FIXPOINT over an ENVIRONMENT `E : CurCtx -d>
iPropO Σ`: `ihs_fam := (CurCtx -d> iPropO Σ) -d> CPU -d> mword 64 -d>
iPropO Σ`; `ihs kt := fixpoint (ihs_pre kt)`; `intr_handler_spec kt E h
:= ihs kt E cpu_id h`.  The trap engine hands the □-body `□ E XIc` at
the ARRIVAL context; `env_move E` (hart-generic: ∀ CIDm ξ0 ξ1) is the
witness that E moves between contexts; `intr_res kt := ∃E,
intr_res_at kt E ∗ □ E XI ∗ □ env_move E` (arity-neutral pack);
`ihs_env kt h` is the same pack around the spec (what usertrap's folds
consume).  For kernelvec, `E := kernelvec_env γu γv γdk γtl γs pd pav
pu = λξ, devintr_caps (XI := ξ) …` and `kernelvec_env_move` is proved
once in `SpecKernelvec`; the caps premise is GONE from the handler
body.  LOAD-BEARING DETAILS: the four eq bridges
(`intr_res_of_eq` etc.) are `reflexivity` at the SPELLED
`ires_pack_of (ihs kt) XI` — keep them so; `Typeclasses Opaque
intr_res_at/ires_pack/ihs_env` seals the fixpoint from unification
(unsealing hangs everything); `iDestruct` of a TC-opaque name needs
`iEval (rewrite /name)` first; `ires_pack_of_contractive` is MANUAL
dist_later plumbing (`solve_contractive` fails on the pack shape).
Installer pattern (ProofMain/ProofMainSecondary/ProofUsertrap): spec
without caps + `□ E XI` bullet built by `rewrite /kernelvec_env;
iModIntro; iExact "Hcaps"` + the `_env_move` witness.

**Cross-cutting tactic traps** (each cost hours at least once): never
`apply`/`refine` leaf instances against named pieces (dispatch
syntactically, `apply _`); hoist side conditions out of `ltac:( )`
application position; `iEval (rewrite …) in "H"`, not bare rewrite,
near big_ops; explicit union lemmas instead of `set_solver` on tower
unions (417 s once); □-premises fill from intuitionistic hyps only when
implicits MATCH (pin `(XI := …)`/`(CID := …)`); section-local constants
cannot take `(XI := ξ)` — state instances AFTER the section; instance
implicit class indices can grab a row's binder — spell
`CtxMove (CID := CID)` explicitly; `iApply ("Hcont" …); last first`
scrambles bullet order — spell subgoals in order; python heredocs eat
trailing `/\` and can mis-terminate — write edit scripts to a file.

## 4. PROCESS LAW (owner rules; non-negotiable)

1. **ALL builds on the GCP VM** via `/shared/xv6iris-3/gcp-rocq/
   run-on-gcp`, run with the FLIPTREE as $PWD (it keys the VM tree off
   the local path — running from a subdir creates a junk remote tree).
   NEVER compile in the container, including one-file checks.
2. **Measure before designing.**  Read the actual error, the enclosing
   lemma, and the PRE-FLIP proof first.  A ported proof that needs a
   NEW hypothesis means the port is wrong.
3. **Zero admits in landed code.**  Scratch admits only for
   measurement: copy aside, admit, compile, RESTORE, delete every
   scratch `.vo` on the VM (marker under /tmp, not in the tree).
4. **Σ-level design points are the owner's** (new ghosts, ts_pay arms,
   context/ledger interface changes): characterize + surface, get a
   §0.x′ ruling in `tso-port.md`, only then build.
5. **Sentinel-backed numbers only** — green counts from an actual run.
6. **Lane isolation**: concurrent side lanes get their own clone, own
   work tree (distinct dir name), own snapshot branch, own scratch.
7. Snapshot recipe (green boundaries): pull `.vo` first
   (`run-on-gcp --pull-vo true`), then temp-index snapshot:
   `GIT_DIR=/shared/xv6iris-3/.git GIT_INDEX_FILE=<tmp>; git
   --work-tree=. add -A -f .; git update-index --force-remove
   iris/.lia.cache` (229MB), `write-tree`, `commit-tree -p tso-flip`,
   `update-ref`, push.  Then rsync the mirror.

## 5. run-on-gcp / round gotchas (all measured)

- Every non-`--no-sync` invocation rsyncs local→VM with `--delete`: a
  remote-only file matching no exclude is DELETED (this once ate a
  round log, and it deletes the VM's regenerated `CoqMakefile` if the
  local tree lacks one — keep local `iris/CoqMakefile`+`.conf`).  Logs
  get `*.aux` names; read them with `--no-sync`.
- Rounds: `ZZbuild.sh` at the tree root, launched under tmux
  (`tmux new-session -d -s r64 "bash ZZbuild.sh > ZZround.log.aux
  2>&1"`); a detached setsid/nohup dies with the ssh session.  rsync
  drops exec bits — `bash ./ZZbuild.sh`.  NO syncs while a round runs.
  Warm round ≈ 20–40 min.  Never put a `pkill -f` and its target's
  launch text in one Bash call (kills your own shell).
- `GREEN=` can count a stale `.vo` whose recompile failed; certify from
  the ERROR ROOTS (`grep -B4 "^Error" ZZ-iris.log.aux | grep 'File "'`)
  plus the RED list.  The stale-.vo trap: a local recheck past a
  changed root needs the VM `.vo` pulled first.
- A tree materialized from `git archive` has ONE mtime — delete
  `.CoqMakefile.d`/`CoqMakefile*` and let make regen (else garbage
  compile order).
- Hangs under tmux: profile with `-time`, `Set Printing All` + `Show`;
  a conversion crawl past ~10 min IS the signature of an unprovable/
  diverging unification — kill it, don't wait.

## 6. WHERE TO PICK UP (in order)

1. **Bucket B first if the owner is available**: get the sign-off on
   Way 1 (the `ξg` restatement of `wp_forkret_gen_body`), then do it —
   it unblocks `LinkForkret`/`LinkForkretParkPaid` and is the only
   kernel-side red left.
2. **Bucket A when the owner lifts the per-binary hold**: run the token
   tranche first (mechanical), then measure `UserretPt:195` /
   `Pt2WalkPt:427` and convert the four trampoline-proof files;
   `ProofUser` last (two-line accessor).  Start from
   `tso-umode-lane.md` §7.
3. **Bucket C last**: first honest compile of the boot/adequacy chain;
   fix the fallout tail; that closes `SystemAdequacy` = the whole
   system proven under TSO.
4. Bank every green boundary: round → pull-vo → snapshot → mirror →
   notes (`tso-machine-flip.md` running log + THIS file) → push `tso`.

## 7. Open owner items

- **ProofForkretPark Way-1 sign-off** (bucket B; spec change).
- **Lifting the §0.37′/per-binary hold** (bucket A) and deciding which
  lane runs it.
- The C-leg cutover gate (§0.23′/§0.25′) once SystemAdequacy is green.
- The main-side slices (separate agent, main-tso-readiness.md).
