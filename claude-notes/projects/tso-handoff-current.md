# TSO port: LIVE HANDOFF CHECKPOINT (2026-08-31, r67 CERTIFIED)

This file is the resumption point for a FRESH agent taking over the TSO
port.  It is updated at green boundaries; trust the newest git commit of
it on branch `tso`.  The successor coordinator (this round) OWNS THE
PRIMARY TREE; lane isolation applies to CONCURRENT side lanes only.

Reading order for a fresh agent:
1. `claude-notes/README.md`, `durable-notes.md`, `remote-build-gcp.md`.
2. This file, top to bottom.
3. `projects/tso-port.md` — the OWNER RULINGS (§0.x′).  Minimum set:
   §0.7′ §0.11′ §0.12′ §0.23′ §0.25′ §0.27′ §0.35′ §0.36′ §0.37′ §0.38′
   §0.39′ §0.41′ §0.42′ §0.44′ §0.46′ §0.47′.
4. `projects/tso-machine-flip.md` — the A6-series measured record.  Read
   A6.139–A6.141 in full (the kernelvec family fixpoint; the trampoline
   port; the fork-crossing reduction).
5. `projects/tso-umode-lane.md` — historical (its mission is complete;
   §7's interface records are DISCHARGED as of A6.140/A6.141).
6. `projects/main-tso-readiness.md` — the SEPARATE main-branch track.

## 1. WHERE THE PROJECT STANDS (post-A6.140/A6.141)

**r67 CERTIFIED: GREEN = 1298/1306, zero admits/axioms, snapshot
`d876d3cd070` on `tso-flip` (parent r63 `bfe7168564bc0`); mirror
refreshed.  RED = 8: ProofForkretPark (the single true error root, at
its park_globals bullet :345) + its cone (LinkForkretParkPaid,
LinkUserinit, LinkMain, BootChain, BootShared, FsAdequacyImg,
SystemAdequacy).**

**THE A6.142-144 INSTRUMENT LAYER (post-r67, all GREEN, snapshot
`25e3f031004`):** the owner ruled the three remaining ξ-bodied cases
case-by-case: ctx_values/word-pins for `ip->ref` (set [1..2^31), never
0), CtxAnchor for the bcache, `f->off` delegated to a main-side agent.
Instruments now ALL BUILT AND CERTIFIED:
- `CtxAnchor.v` (A6.142): parked-context custody in an [inv] --
  anchor/astamp/aguard, deposit/withdraw/open_close; guard = floor row on
  guarding locks.
- `TsoMemPa` §12f + `TsoCtx` + `CtxPinw.v` (A6.143): the WORD-SET PIN
  (ts_pinw/pinw_ok1 + 4th ts_pay arm; phys_ledger_pinw with
  ok/mint1/drop; racy read gate `ledger_read_pinw_ok`; exact read
  `ledger_read_pinw_latest`; member store `ledger_store_pinw_ok` +
  `pinw_write_c` the au_dat leaf face).  The racy LOAD leaf is the
  existing `wp_load_s_sconf_au_rel` (generic; no clone needed).
- `WpLock.lock_pay_intro_llb` (A6.144): the floored payload mint via
  `ctx_parked_raise` on the lock record -- serves BOTH the itable exact
  read row and the anchor's guard mint; closes A6.142's one gap.

**ICACHE RESTRUCTURE PROGRESS (A6.145; snapshots `d9dc2d46dbe`,
`1578c811f86`, `7703294ca9d`, all GREEN):** 4a (icfg families) DONE; 4b-i
(iref_set + panic bounds + iref_pin_slot + itable_body_pinw additive in
IcacheInv) DONE; 4b-ii (iliveUR agree payload -> (gname * epoch-floor);
live_genlo real element; live_gen/live_frac arity-preserved wrappers;
live_genlo_bump takes the fresh floor) DONE.  The FLOORED-SLICE
architecture is decided and recorded (flip notes A6.145 cont.): cred
threading vanishes into the inode_ref/inode_shr bundle tier via
live_fracc; floor-free live_genlo/iref_tok are the ONLY forms inside inv
bodies.  REMAINING (4b-iii/4c/4d, mapped, not built): live_fracc + flat
inode_ref restatement + conversion lemmas; body cutover (itable_body :=
itable_body_pinw with live arms at live_genlo, per-slot lo bound across
pin row and live arm); itable_res gains free-slot ctx cells + istmp
halves + the A6.144 floor row + the is_itable λ-flip; icM_wf gains n <=
IREFSLOTS; accessor family (racy read = wp_load_s_sconf_au_rel +
ledger_read_pinw_ok at the slice+floor; locked exact =
ledger_read_pinw_latest at the row; count stores = pinw_write_c; arm =
live_genlo_bump at the arm store's position + pinw mint; retire = drop +
cells back to the payload); then ProofIget/Idup/Iput/Ilock/Iunlock +
Specs + IcacheBoot.

**OLD PLAN NOTE (superseded in part):**  Plan:
(4a) `icfg` gains two per-slot gname families `icfg_ieplo`(epoch floor)
+ `icfg_istmp`(cell stamp), both mono_nat (no Σ change; one MkIcfg site
in IcacheRef.icfg_alloc); epoch cell = fractional mono_nat_auth_own,
fraction riding each reference so epochs cannot retire under a live
cred.  (4b) `IcacheInv.itable_body`: live slots hold pinw windows (set =
words [1..IREFSLOTS], per-byte via `iref_set`) + epoch half + stamp
half; free-slot cells move to `itable_res` (the lock payload) as
ctx-tier zeros; `is_itable` takes the λ-flip (should CtxMorph clean --
no nested cinvs); the lock payload gains the A6.144 floor row (stamp
half + ctx_floor at it).  (4c) accessor family rewritten (racy load =
au_rel + `ledger_read_pinw_ok` at the cred; locked exact =
`ledger_read_pinw_latest` at the floor row; count stores =
`pinw_write_c`; arm/retire = mint/drop + epoch update); 7 AU-consumer
proofs (ProofIget/Idup/Iput/Ilock/Iunlock + Specs) + `iref_cred`
threading through SpecIlock/SpecIunlock callers.  IREFSLOTS bound: the
increment's member premise needs n+1 <= 422 = the caller's unit
(strengthen `iref_slots_no_overflow`).  THEN Phase 5: the bcache anchor
refactor per the agreed three-way split (transit custody + b->valid in
the anchor; refcnt==0 custody in bcache.lock's payload; recycler
trivial).

r63 was 1283/1305 with five error roots.  This round LANDED, per the
owner's direction ("the per-binary proofs don't need to be done … but
the reasoning about executing in the kernel's trampoline page, in
userret / usertrap, does need to be ported"):

- THE WHOLE TRAMPOLINE EXECUTION TIER (A6.140): the tramp_tr_obl token
  tranche (TrampStepPt/UptWalkTramp/Pt2WalkPt/TransPt), the satp-switch
  legs (UserretEntryPt/UservecExitPt), the instruction leaves
  (UserretPt/UservecPt, trapframe now ctx-tier), the token-threaded
  S-mode RAM engines (HartSMemTok.v, NEW), the whole-function chains
  (ProofUserret 38-instr, ProofUservec 44-instr + usertrap + userret),
  the trap-loop Löb closer (ProofUserretClosed) and its Links, the
  userret→user bridge (UserretUser), and ProofUser (the u-lane's
  recorded Rut_ctx accessor).  The residue opens
  (usertrap_res_tf_open/_tf_csrs_open + parked twin) hand the running
  token out and take it back; kpt_creds threads uservec's kcur window
  and rides uservec_post.
- THE FORK CROSSING, MEASURED TO ITS TRUE WALL (A6.141 + its §0
  correction): the `is_ftable` context-λ flip made `CtxMove
  park_globals` provable and the park's bullets cross — but
  `WpLock.newlock`'s `CtxMorph R` premise (the producer side) then
  demands a morphable payload, and `ftable_res` contains ξ-BODIED cinvs.
  The flip is REVERTED and re-lands with the rooted restatement; both
  the `park_globals` and `proc_priv` bullets are blocked on the SAME
  design point.

**The red set now funnels through ONE design point** (see §6): the
ξ-BODIED invariant/cinv bodies — `IcacheInv.itable_inv`,
`BioInv.buf_escrow`, `inode_pay`'s `cinv fileipN (inode_held_short)`,
and `off_hold`'s cinv over `off_content`.
Everything else red is the boot/adequacy tail sitting behind
ProofForkretPark: LinkForkretParkPaid, LinkUserinit, LinkMain,
BootChain, BootShared, FsAdequacyImg, SystemAdequacy.

True error root (single): `ProofForkretPark` at its park_globals /
proc_priv bullets (one shared blocker).

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

1. **THE OWNER REVIEW ITEM (blocks everything left)**: restate the four
   ξ-bodied invariant/cinv bodies (`itable_inv`, `buf_escrow`,
   `inode_pay`'s `cinv fileipN`, `off_hold`'s cinv) in §0.47′'s ROOTED form
   (establishment context packed inside; cells as ctx_values/rooted
   records; access gated on domination; A6.129 §4's per-lock mono_nat
   stamp is the instrument for re-base).  Both invs then become ξ-free
   propositions, `CtxMove proc_priv` closes by the A6.141 §3 unfold
   tower, and ProofForkretPark's last bullet goes through.  NOTE the
   child twin is born dominating everything its parker dominated, so
   the fork pays nothing at the gate.  Characterization + the measured
   unfold tower: tso-machine-flip.md A6.141.
2. **Bucket C right after**: LinkForkretParkPaid → LinkUserinit →
   LinkMain → BootChain/BootShared → FsAdequacyImg → SystemAdequacy —
   first honest compile of text written while unbuildable; expect a
   modest fallout tail, then the whole system is proven under TSO.
3. With the ruling landed, re-apply the recorded reverts: the
   `is_ftable` λ-flip + `ftable_res_at` + the 9 consumer re-spells +
   `park_globals_move` (all in comments at their sites), and the same
   class for `bio_ctx`'s `<{ bcache_res bn V }>`.
4. Bank every green boundary: round → pull-vo → snapshot → mirror →
   notes (`tso-machine-flip.md` running log + THIS file) → push `tso`.

## 7. Open owner items

- **The rooted-invariant restatement of itable_inv/buf_escrow** (the
  A6.141 §3 review item; the ONLY blocker of the last kernel red).
- The C-leg cutover gate (§0.23′/§0.25′) once SystemAdequacy is green.
- The main-side slices (separate agent, main-tso-readiness.md).

## A6.145 4b-iii FRONTIER (live worktree state, tree RED at ~8 proof files)

The floored-bundle swap is COMPLETE AND GREEN through: IcacheRef (the
whole vocabulary: live_genlo/live_gen/live_frac wrappers, live_fracc,
live_frac0 interim kit + absorb/pin, floored inode_ref/inode_shr/_short/
_held_ty/_shr_held_gen, genlo-exposed intro equivalences, iref_tok0),
IcacheInv (pool arms at live_frac0, the five movers, live_slot_alloc/
regen lo-exposed, pool-sourced AU posts at iref_tok0), IcacheEscrow,
FileInvDefs, IcacheBoot/FsCfgBoot (boot rows at live_frac0).

REMAINING RED (the consumer wave; each is the same 3 adaptations):
ProofIunlockput:279 ProofIput:1006 ProofIreclaim:1687 ProofIget:1450
ProofCreateFreshTy:572 ProofSysOpenParts:715 ProofSysMkdir:1272
ProofSysMknod:1735 SpecFilestat:435 SpecFileread:666 (+ their cones).
The adaptations: (1) `inode_shr_gen_intro`-style destructures gain
(g lo tl) + ⌜lo<=tl⌝ + #floor (KEEP the floor aside -- persistent -- for
any later rebuild/forget, whose new signatures take it); (2) pool-sourced
AU outputs arrive as iref_tok0 (weaken via iref_tok0_tok, or keep frac0
for the floored-bundle mint via live_frac0_fracc); (3) Spec-level
accessors that expose `inode_shr_gen` through a round trip (SpecFilestat/
SpecFileread pay-accessors, SpecIlock/SpecIunlock posts) should expose
the GENLO form instead so the return re-ties lo, floors held outside.
Pre-cutover every lo is 0 (live_frac0 kit; ctx_floor _ 0 free).

## A6.145 4b-iii pattern addendum (pin-on-exit)

The AU s-rows do NOT need genlo binders: `live_slot_norm_of_lv` now PINS
the caller's slice against the pool's zero-epoch residual on the way out
(`live_frac0_pin`), so every pool-touching AU RETURNS `live_frac0` rows
(one-sided upgrade, no new binders).  Ride-only s-rows (never pool-
touched, e.g. `iref_upgrade_store_au`) stay `live_frac`.  Downstream a
proof rebuilds the floored bundle from a returned frac0 row via
`live_frac0_fracc` (floor 0 free).  New kit since the last note:
`live_slot_live_genlo`, `iref_share_lookup_au_lo` (identity-preserving
look), `live_frac0_absorb/pin/join/split/bump`, `iref_tok0` (+`_tok`).
CURRENT RED (same 3 adaptations each): ProofIunlockput:279 ProofIput:1006
ProofIreclaim:1687 ProofIget:1450 ProofCreateFreshTy:572
ProofFilestat:531 ProofSysOpenParts:715 ProofSysMkdir:1272
ProofSysMknod:1735 ProofSysChdir:1545 ProofFileread:1892 ProofNamex:3129
ProofKexecA:1152.

## A6.145 4b-iii progress checkpoint 2 (live worktree)

GREEN through the wave so far: IcacheRef (full genlo kit now incl.
inode_ref_genlo_shed / _gather_genlo / shr_genlo_split+halve /
pin_on_keep / forget_on_keep / genlo agrees / halve lemmas),
SpecCreate (floored payout row), SpecFilestat/SpecFileread (genlo
carves), ProofFilestat, ProofFileread, ProofNamex, ProofNamexTr,
ProofSysChdir, ProofKexecA, ProofSysMkdir, ProofSysMknod, ProofIdup,
ProofSysLink, ProofCreateFreshTy, FileInvDefs, boot chain.
REMAINING RED: ProofCreate (tail branches -- keeps that round-tripped
through IUP calls come back gen-erased; blocked on the iput specs),
ProofSysUnlink (same), ProofSysOpenParts:715 (the file_ref builder --
restate its Hkeep premise genlo+floor), ProofIget:1450, and the iput
trio ProofIput/ProofIunlockput/ProofIreclaim.  NEXT UNIT: restate
SpecIput/SpecIunlockput's reference premises as ∃lo tl floored genlo
rows (create_locked's shape) and adapt their proofs; the caller branches
then pass the shed's floored pieces straight through instead of
forgetting before the call.

## r64 BANKED (snapshot 5c49e67e31d): the A6.145 consumer wave is COMPLETE

GREEN = 1304/1305.  The ONLY red is the pre-existing ProofForkretPark:345.

What landed since checkpoint 2:
- ProofCreate end to end: the three parked-body ∀s (cr_mkdir_body 2127 /
  cr_fail_body / the grey-links lemma) gained explicit (lo tl) binders with
  pure+floor+genlo child rows; cr_alloc_body's parent row went ∃-packed;
  the Hfbad box row is genlo at the shed's fixed lo; suppliers instantiate
  (lo tl) or (0,0) and package via iExists/floor_0 blocks.  GOTCHA learned
  twice: iApply spec-string side-goals for mid-spatial [%]/[] entries come
  AFTER every earlier premise's goal -- put the new brace blocks at the END
  of the existing run (pure [%] first, [] floor last... actually: in premise
  order, empirically -- move blocks until the reported goal matches).
- THE INTERIM PIN INSTRUMENTS (IcacheInv): live_slot_pin (every live_slot
  arm carries a live_frac0 piece, so any outstanding genlo slice pins to
  lo=0 by pair-agree), iref_share_pin0 (the same through itable_inv alone,
  big_sepL_lookup_acc at the slot -- no itable_half needed),
  inode_shr_gen_pin0 and inode_ref_short_gen_pin0 (share-/short-shaped
  wrappers: _gen ={Eo}=∗ erased floored form at (g,0,0) via ctx_floor_0).
  These are THE seam-closers everywhere a floor-free _gen comes back from a
  spec post (iunlock returns, ilock posts) and an erased/floored form is
  owed downstream.  SpecIunlock's post row stays _gen -- deliberately: five
  green callers keep compiling, and the two that need floors (IUP:281,
  Ireclaim:1813) pin at the seam.  ProofSysOpen so_tail_pub pins internally
  (statement unchanged); its three interior forgets are pin0 fupds now.
- ProofIput: the floored inode_ref premise destructures 4-part
  (frag/fracc/slh/ident); pure lookups use iref_frag_lookup (frag-only);
  rebuild sites re-pin via iref_share_pin0 + live_frac0_fracc.
- ProofIdup: upgrade AU posts iref_tok0/live_frac0 (inline AU row updated);
  exit rebuilds fracc via live_frac0_fracc.
- ProofFilewrite/Parts: the loop carve is genlo end to end -- carve exposes
  (lox tlx)+floor, halve via inode_shr_genlo_halve, lend weakened _gen to
  ilock, on return inode_shr_gen_pin_on_keep + genlo_halve rejoin, payback
  at genlo (fw_shr_regen retained but bypassed on the main path).

NEXT (unchanged from the map): 4b-iii itable_body cutover (itable_body :=
itable_body_pinw, live arms bound per-slot lo), itable_res extension +
accessor rewiring, icM_wf n <= IREFSLOTS, IcacheBoot construction,
ilock/iunlock racy reads; then Phase 5 bcache anchors; then 4.5 ic_escrow.

## r65 BANKED (snapshot 1a1555e8d4f): 4b-iii Stage A -- the racy-read leg

Additive, world still 1304/1305.  What is now CERTIFIED:
- The v2 per-slot body (`IcacheInv.pinw_slot`): one (g, lo) binder spans
  the four pinw ledger rows (`iref_pin_rows k w lo tst`, each byte
  ⌜t<=tst⌝-bounded for the A6.144 exact read) and the genlo-ized
  liveness arm (norm residual / frozen full / free full -- the old
  live_norm/live_frzn shapes at the slot's own epoch).
  `itable_body_pinw` = half + wf + the merged rows; `itable_inv_pinw`
  is the parallel inv name (cutover: itable_body := itable_body_pinw).
- `pinw_slot_slice`: an outstanding genlo slice REFUTES the free and
  frozen arms (full unit + slice > 1, Qp.not_add_le_l) and pins the norm
  arm's (g, lo) to its own by pair-agree; the subtraction witness comes
  out at the slot's qt so the opener can reclose.
- `iref_load_pinw_au`: the wp_load_s_sconf_au_rel Res-accessor -- open
  icacheN, slice finds its window, borrow rows across the step, reclose.
- `IcachePinwObl.iref_read_obl` (NEW FILE, after IcacheInv in
  _CoqProject): floor(tl>=lo) --own_context_floor_view--> view_lb --
  ledger_read_pinw_ok --> at EVERY drain view the four bytes assemble an
  iref_set member --> 0 < v < 2^31 (iref_set_read).  This is the
  ilock/iunlock panic-killer, end to end, at the gstate tier; consumers
  do the tso_interp_of_at_gs rewrite + KT0 identity at their sites
  (StartedInv.started_read_obl is the worked model).
- DESIGN NOTE MADE CONCRETE: the epoch credential IS the (g, lo)
  liveness generation (flip notes A6.145 correction); the r64-era
  iref_cred/icfg_ieplo quantum forms are REMOVED from IcacheInv (ieplo
  gnames stay allocated, unused).

NEXT LEGS (4b-iii remaining, in order): (1) the count-store leg --
strengthen CtxPinw's two store faces to expose the re-mint bound
(rows return ∃t ⌜t <= length g'.(glog)⌝; line ~220's iExists (S len) is
the witness), then the incr/decr AU faces yielding iref_pin_rows and
taking back rows at w' + msg_at + llb, stamp halves joined with the
A6.144 payload row and max-bumped; floors deferred to release
(WpLock.lock_pay_intro_llb re-floors the payload).  (2) arm/retire --
ctx cell <-> pinw rows conversion + live_genlo_bump at full unit (fresh
g', lo' = the arm store's position); free-slot cells + istmp halves +
floor row into IcacheEscrow.itable_res2; is_itable2 λ-flip.  (3) the
swap + the 11 cell-faced AU rewrites + icM_wf n <= IREFSLOTS +
IcacheBoot + the consumer wave (the r64 interim pin0 seams get replaced
by real floors from lock rows -- un-parkers re-mint under the lock).

## r66 BANKED (snapshot 63d92f9b612): 4b-iii store-twin leg

Additive, world 1304/1305.  CtxPinw's two store faces
(ledger_store_pinw_ok / pinw_write_c) now EXPOSE the re-mint bound: the
returned window rows carry ⌜t <= length g'.(glog)⌝ / ⌜t <= S (length
log)⌝, which is what lets an AU reclose [iref_pin_rows] at a bumped
stamp.  FOUR pinw store AU twins are certified in IcacheInv's Reg
section, all against [itable_inv_pinw]:
- iref_incr_store_pinw_au (licenced up-count; the model),
- iref_close_store_pinw_au (survivor down-count),
- iref_dup_store_pinw_au (self-split, no arm motion),
- iref_upgrade_mir_store_pinw_au (licence-free up-count; the caller's
  own slice refutes frozen, mirror rides for the region only).
The SHARED choreography: open icacheN; pinw_slot_acc_upd; slot
destructures to (g, lo, tst) with ⌜lo<=tst⌝; the caller's genlo
slice/token AGREES (g, lo) by pair-agree and REFUTES the frozen arm
(full unit + slice > 1); the two istmp halves (inv + A6.144 payload)
agree, yield rows at tstp; on take-back ([pinw_store_post] = ∃tst',
llb tst' ∗ rows(w')), max-bump the joined stamp auth, rebound rows,
reclose; posts return the payload half at (max tstp tst') + llb(max)
via llb_max, with ⌜lo <= tstn⌝ for the caller's later floor mint.
Ghost movers: pinw_arm_split/pinw_arm_join (residual Qp algebra),
iref_close_step_noarm, iref_dup_step_genlo, pinw_slot_acc_upd.
NOTE: iref_upgrade_store_au needs NO twin (rider stays outside).

NEXT: the ARM/RETIRE conversion faces in CtxPinw (all instruments
verified present): retire = ledger_pinw_drop_run -> ledger_store_win_at_ok
-> hart_view_lb_get (my view = S len after my own store) ->
TsoCtx.ctx_bound_raise (own_context + hart_view_lb ==> ctx_floor) ->
ctx_floor_le -> ctx_phys_pointsto_of_at_floor per byte; arm =
ctx_phys_pointsto_ledger per byte -> at-store -> pinw mint
(pinw_ok1_mint at lo := S len, member = the count-1 word) +
live_genlo_bump (fresh g', lo' := S len) in the AU.  Then close_last/
alloc AU twins, the locked exact read, itable_res2 extension, swap,
consumers.

## r67 BANKED (snapshot 3c7eadaef5151c62e19232728fd1a570f54a1020): arm/retire machine faces

CtxPinw gains the two conversion faces, closing the machine-tier
accessor vocabulary:
- ledger_arm_pinw_ok: ctx window cells drop to the ledger
  (ctx_phys_pointsto_ledger), the member store lands at the generic
  at-gate, and the window is MINTED (pinw_ok1_mint via log_byte_top on
  the appended message) at lo := the store's own position -- the arm
  point.  Returns rows bounded by length g'.glog.
- ledger_retire_pinw_ok: pinw drop_run -> at-gate store (non-member ok)
  -> the storer's own view is at the top (premise: length g'.glog <=
  gtv' cpu), so hart_view_lb_get + TsoCtx.ctx_bound_raise mint the ctx
  floor and ctx_phys_pointsto_of_at_floor converts each byte back to a
  ctx cell.  own_context threads through.
REMAINING 4b-iii: alloc/close_last AU twins over the faces (arm:
live_genlo_bump fresh (g', lo'=S len) + M insert + stamp into the inv;
retire: full-unit gather + M delete + cells/stamp back to the payload),
the locked exact-read accessor (ledger_read_pinw_latest at the A6.144
row), itable_res2 extension (free cells + stamp halves + llb + floor
row), is_itable2 λ-flip, icM_wf n<=IREFSLOTS, THE SWAP, IcacheBoot, and
the consumer wave.

## r68 BANKED (snapshot 9caa3f015dd): arm/retire AU twins

- iref_alloc_pinw_install: the ARM's icache-side ghost install.  The
  physical leg runs on the CALLER's payload cell through
  CtxPinw.ledger_arm_pinw_ok inside the store leaf's obligation; this
  fupd then: opens icacheN, takes the FREE arm (full unit at (g0,lo0)),
  pinw_arm_alloc bumps to a fresh (g', loA) and splits
  1 = 1/2(escrow) + q(tok) + c(residual), frzsel splits, the FULL stamp
  auth (payload-held for free slots, with llb tstp) max-bumps and one
  half enters the slot row, the minted rows (at loA, from the face)
  rebound and install, M inserts (q,1).  Posts iref_tok_genlo + escrow
  slice + pending + selector half + stamp half back (max tstp loA).
- iref_close_last_store_pinw_au: the RETIRE.  Store-twin-shaped: yields
  the window at (lo,tstp), the closing wand is ∀P (the ctx cells from
  ledger_retire_pinw_ok thread through as P); the unit reassembles
  (tok qt + escrow 1/2 + residual c at agreed (g,lo)) and parks in the
  free arm AT THE SAME (g,lo); frzsel halves rejoin; the FULL stamp
  auth (iCombine normalizes 1/2+1/2 to 1 -- no div_2 rewrite needed)
  leaves for the payload; the ireg 1->0 freeze choreography is copied
  verbatim from iref_close_last_store_au.
REMAINING before the swap: the locked exact-read accessor, the
freeze-path movers over pinw_slot (frz_slot_freeze/kill + the
share-lookup family + regen), close_last_freeze twin, itable_res2
extension + is_itable2 flip, icM_wf bound, THE SWAP, IcacheBoot,
consumers.
