# The main cutover branch (`tso-cutover`): real TSO semantics onto main

**What this is.**  The owner directed the merge of the real TSO semantics
into `main` (2026-08-31, ahead of §0.23′'s full gate; §0.25′'s three-case
gate is met on the flip tree).  Because the machine flip cannot keep a
tree green through the transition, the work lives on branch
**`tso-cutover`** (off `main`, worktree `/shared/xv6iris-2-main`, VM tree
`_shared_xv6iris-2-main`), banked at named rounds; it lands on `main` as
one validated merge when green.  The flip reference is `/shared/flip63`
at **tso-flip r69** (`b784e0ec2`).

**What LANDED ON MAIN directly (green, pre-branch):** the model tier —
`TsoMem.v` (the Ztso view machine), `TsoLitmus.v` (SB allowed, n6 the
not-secretly-SC witness), `TsoMemPa.v` (era image + append-only pwmsg log
+ pins + §12f pinw), `TsoGhost.v` (view_lb/llb) — zero consumers, so SC
main is untouched (`5aefcbfc5`).

**The merge method** (r1–r3, and the rule for the rest): per file,
3-way merge with base = merge-base(main, tso-flip) — `tools/merge3.sh` —
resolving toward FLIP for machine/obligation content and toward MAIN for
its post-fork features.  The two main-side feature families that must
survive every resolution:
  - the OBSERVATION tier (mobs/κ traces, obs_interp; flip's mobs is
    Empty_set) — the uart/power arms carry κ, state_interp keeps the obs
    conjunct beside power_interp, and flip's inversion/frame lemmas
    adapt to the κ-shaped arms;
  - the VIRTIO POP-ERA device model (indexed virtio_req/capture, the pop
    arm, VirtioModel wholesale) — composed with flip's disk-as-log-agent
    arm: disk_step returns the WRITE SET, the loop appends it as ONE
    message by `PWMsg W disk_agent`.

**Round log:**
- r1 (`49b970365`): RiscvLang (GState + gimg/glog/gtv, mnode_step over
  agent/img/log/view, mm_ok, the composed device arms), RiscvExec (disk
  loop threads (d' W log') + tso beside obs), RiscvPtsto (era_interp
  carries tso_interp_at; state_interp keeps obs), the HartM* engines at
  flip's view-indexed obligation families, ObsTrace arity.
- r2: TsoCtx = flip's real file (ledger bodies, the ==∗ CtxMorph — main's
  -∗ was a port-era strengthening, dropped) + a MAIN-COMPAT appendix
  (log_lb := llb loglen_name; ctx_vis over real ctx_wrote; the or /
  big_sepS / if_then / if_else / string morph combinators at bupd shape).
  TsoCtxMove/Park/AbsorbLb = flip's.  Satellites added: CtxValues,
  CtxPinw, CtxKMap, CtxPinMint, TsoCtxTwin/Twin2/Rehearsal, SepThread,
  HartBarrier, KptPublish, WpSconfFencePub, HartSMemTok.  CtxMorphTac
  keeps main's syntactic dispatch minus the SC phys rows.  **TsoCtxShim
  is flip's TOMBSTONE** — every remaining `TsoCtxShim.*` reference is a
  build error naming its own seam site.
- r3: StartedInv = flip's (A6.135/138 position-indexed barrier); the
  engines converge byte-identical to flip; UartAccepted/ProcGeom fixes.

**The enumerated frontier (error roots after r3, cones blocked behind
them):**
1. `WpLock` — the M4 lock kit: lock word/owner cell to the ledger tier
   (`phys_ledger_word4`, `lk_cpu_cell_ex`), lock_inv goes ξ-closed, the
   is_lock transports become flip's one-liners.  THE keystone; most of
   the kernel cone sits behind it.  3-way + main's fd/park-era API kept.
2. `DiskInv` + `WpUart` — the A6.125/A6.126 virtio pin-half reshape
   (flight/parked res over hcell_map, the release window `_au_rel`,
   `ledger_store_rel_map_ok`) composed with main's pop-era protocol
   (VirtioProto's indexed step).  Deferred whole this round: it is a
   subsystem port, not a seam fix.
3. `PtTreeAdue`/`PtTreeMove`/`StackOwn`/`KptPublish` — main's PtTree/
   phys tier against the real cells: the SC phys morphs are FALSE at
   TSO (a full phys cell does not transport by domination).  Needs the
   T-leg treatments: clean-half (`ctx_phys_pointsto_h`) instances, the
   twin-born-dominating fork argument (A6.141), §0.46′ A/D write-backs.
   OWNER input may be needed where main's PtTree shapes have no flip
   counterpart (process law 4).
4. `WpInstrRun` — fetch obligation to `fobl_ram` (view-indexed family);
   likely mechanical vs flip.
Behind these: the kernel proof stack re-enumerates (locks, park, intr,
umode — mostly statement-converged with flip already, so expect the
runbook's fix-table classes), then main's OWN fs/fd architecture needs
its TSO adaptation wave (flip's fs shapes are per-tier recipes, not
ports: main's FsAbs/Fd tier postdates the fork).

**Facts that cost time, recorded:**
- flip's CtxMorph is `==∗`; every main-side `iDestruct (ctx_morph …)`
  needs `iMod`.
- main seals `word_pointsto`/`hreg_frame`(_ro) with Typeclasses Opaque
  (perf); flip files destructing them need `iEval (rewrite /name)` first.
- `git merge-file` drops flip-side additions when main deleted nearby
  text — after a 3-way, `diff` against flip and re-add `>`-only blocks
  (HartMFetch/HartMPmp/RiscvFetchExec were retaken wholesale).
- ObsTrace-class arity fixes: hart node destructs gain (log' tv'), the
  disk arm gains (W log' … Hlog), MemRead's plain arm gains a tvn binder.
