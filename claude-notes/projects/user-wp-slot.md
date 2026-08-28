# Project: the per-process user-execution WP slot — step 3 (real linkage)

**STATUS.**  Steps 1 and 2 are LANDED and green (full tree + `audit-only`
at the sanctioned 13 assumptions).  The design as built is
[`../design/user-wp-slot.md`](../design/user-wp-slot.md): the WP userret
runs is a residue-resident resource (`uexec_wp` in `ut_own`, extracted at
userret, re-deposited each round, minted generically at the two parks —
userinit's and sys_fork's), the trapframe-keyed `uexec_slot V M` exists
with the `uexec_wp ⊢ uexec_slot` mover, and `USyncKernel.sync_uexec_slot` is the
`sync` program's entry deposit — type-compatible with the slot, with
`uv_cap` visibly the one gap.  What follows is what is LEFT: making a
verified process actually run IN PLACE of the generic WP.

## MILESTONE G (owner-directed): the WP circulates instead of being re-minted

**LANDED** (full tree + `audit-only` at the sanctioned 13); the design as
built is in `../design/user-wp-slot.md`, and ledger item 6 below is
resolved by it.

Userret extracts the WP from the per-process resource and runs it;
the user-space WP RETURNS the next WP at its trap; usertrap re-deposits
that returned WP.  Initialization (forkret's park; later exec) is the only
place a WP is ever minted; the loop's per-round mints are deleted.  (Lane
H below moved the mint from the park's ambient world to the PARKER, but the
"initialization only" property is unchanged.)

- `uexec_wp` becomes a GUARDED FIXPOINT (`ParkCap.park_token_F` is the
  pattern): the handler premise is
  `▷ (user_trap_frame C pt Rut ∗ uexec_wp -∗ WP Loop)` — the recursive
  occurrence sits under the handler's `▷`, so the functional is
  contractive.  The generic inhabitant `⊢ □ uexec_wp` is a Löb proof that
  returns ITSELF at every trap.
- Across user execution `Rut` is the HOLED residue — the accessor's
  closer, `λ p, ∃ ksp, (uexec_wp -∗ usertrap_res_bare p ksp)`.  No new
  residue forms; `user_inv`/`user_trap_frame` take `Rut` opaquely, so the
  safety tier is untouched.  The trap-entry seam (where the loop opens
  the frame) applies the hole to the returned WP, so the residue is whole
  BEFORE the kernel excursion — syscall parks carry the slot.
- The forkret entry needs ONE combined opener on the bare residue (slot
  out + tf words borrowed + closer landing in the holed form): two
  borrows of a sealed bundle come out of one opener.
- `wp_userret_closed_body`'s public boundary and the safety tower keep
  their shapes; `US : USER` becomes unused in the loop's modules and is
  dropped; `uexec_slot`/`sync_uexec_slot` reshape their handler premise
  mechanically (the returned WP is typed at the general `uexec_wp`).
- **LANE H (follow-up, LANDED).**  The DUPLICABLE copy is gone:
  `SyscParkEnv.park_world`'s `□ uexec_wp` (and `UsertrapRes.park_world_uwp`)
  are deleted, and the child's WP is a LINEAR row the PARKER supplies, on
  the park channel, captured at the park exactly the way `fd_frags_any` is
  (`ut_park_intro_body` / `ParkCap.park_chan` / `park_token_park` /
  `ut_res_bare_park`).  `SpecKfork`'s contract gains the premise ("the
  child's user-execution WP, consumed by the park"), threaded through
  `ProofKforkMain` → `ProofKforkB5`, and sys_fork pays it
  (`SysForkProof (Kfork : KFORK) (UG : UEXEC_GEN)`, `LinkSysFork`).  A WP
  now enters the world at exactly TWO greppable `uexec_wp_gen` sites —
  userinit's park and sys_fork's kfork call — which is the contract shape
  the verified-fork story needs (the parent owes the child a WP).  Details
  in `../design/user-wp-slot.md`.

## MILESTONE J (PLANNED, owner to review): boundary-row circulation

Supersedes the residue-row mechanics of milestone G while keeping its
return channel and lane H's park delivery.  The slot is STORAGE-FREE
(see the placement ruling below); V and M are named BY BINDERS at the
seams, never by storage.  Landable GREEN under the generic
instantiation, before any sync linking:

1. **M-exposure refactor — RULED (owner): no `_at` flavor, no
   ∃-closed wrapper.  `proc_priv` ITSELF takes `M` as an argument**
   (`proc_priv γf pa pid V M`, the page contents as the named
   `umem_own`-shaped view; same for `proc_priv_nopt`/`_bare`/core),
   and every referring site changes.  The three wins this buys:
   (1) the WP ties to `proc_priv` freely — the slot's key names the
   block's own `V M`; (2) syscall specs become PRECISE — they can
   speak about arguments in `V`, the return value into a0, and how
   the syscall reads or writes `M`; (3) most kernel functions taking
   `proc_priv` do not change `V`/`M`, and their signatures now SAY so
   — preservation of WP preconditions by signature, no machinery.
   STAGING for green: first the signature sweep with memory-writing
   functions' posts ∃-weakened (`∃ M', proc_priv … V' M'` — today's
   information content made explicit), then per-function precise
   M-effects (copyout's written window, vmfault's zero page — the
   win-2 spec-writing, incremental).  SWEPT (uncommitted, full gate +
   audit green): 214 files; decisions — `proc_priv_nopt` carries NO
   `M` (the bytes ride `proc_pt P M`;
   `proc_priv V M ⊣⊢ proc_priv_nopt V ∗ proc_pt (pv_upt V) M`);
   `proc_pt_any := ∃ M, proc_pt P M` is the ∃-weakened tier for the
   sub-`proc_priv` copy cone and dormant arms.  The ∃-weakened set
   (the win-2 worklist, full list in the sweep log) includes the copy
   cone, `wp_syscall_sconf`, `wp_piperead_sconf`, the kexec trio, and
   `ut_own_priv`'s closer (now `∀ V' M'`).  One precise crossing
   landed already: `wp_uvmcopy_sconf` names the PARENT's image and
   returns it on the nose (the va-keyed `M` is recoverable from the
   sz-relative `proc_ptm` view because `umem_lazy`'s existential half
   is a submap pinned by its domain — reusable lemmas in
   ProofUvmcopy).  (Noted alternative — `M` as a
   `pprivate` field `pv_mem`, mirroring `pv_tf` — set aside per the
   ruling; the argument form is what syscall specs will be written
   against.)  The residue's ∃-prefix gains `M` directly.
2. **Delete `ut_own`'s slot row and its accessors** (`uwp_acc`,
   `run_open`); `Rut` returns to the plain bare form (the hole trick
   dies); the park channel's closer row is re-typed KEYED under the
   binders it already receives (`V'` is an argument; `M'` joins).
3. **Boundary rows**: slotted residue VARIANTS
   (`∃ N V av M, ⟨rows⟩ ∗ S V M`, the shape functional `S` chosen by
   the boundary) — usertrap's pre takes `S := uexec_ret sc_v`
   (cause-indexed, coupled to the `sc_v` its boundary already names);
   its arms' posts and the composed `wp_uservec_pt` post carry the
   PRECISE slot at the final key, PLUS the agreement equations
   (`mf = tf_resume_gpr b V'`, `ret_pc uepc = tf_resume_pc V'`, memory
   = the named `M'`); the loop applies the keyed slot from the round's
   post.  The paired return channel refines so the returned WP is
   bound by the trap state at the frame's own binders.
4. **Item 3 has TWO halves** (identified this round): the RESTORE
   agreement (userret reads the tf words — already exposed at
   `wp_userret_pt`'s level) and the SAVE agreement (the returned WP is
   machine-keyed at trap time; uservec's save walk manufactures
   `V_trap` with tf-derived state = trapped state, licensing the
   conversion to tf-keying).  Both look provable from what those
   proofs do internally; the work is exposing them at the composed
   post.
5. Then the userinit probe re-applies; expected next wall: the
   `uv_cap` premise on the true branch → the sync trap-exit reshape
   onto the return channel (umode side).

## THE uvis RULING (owner): the slot is keyed on the ACTUALLY-user-visible state

The page-table descriptor is kernel-side REALIZATION, not observation:
a process sees its va-keyed memory and its registers, never PPNs — two
states with the same view on different tables are user-indistinguishable.
So a second record, `uvis := { uvis_tf : list (mword 64); uvis_M :
gmap Z (bv 8) }` with `uvis_of : ustate -> uvis`, captures the
user-visible state (ustate minus the table; later fd view and pid as
fields), and `uexec_slot (W : uvis)` UNIVERSALLY QUANTIFIES the
realizing descriptor inside — `∀ P, ⌜loop_ok C P⌝ -∗ …
user_pt_inv P (uvis_M W) … Rut P …` — exactly parallel to the ∀-dead
register-file base, and exactly the ∀-descriptor form the fork clause
needs for the child (same `M`, fresh table).  `ustate`/`proc_priv`
keep the descriptor exposed: the trap seams, the phase splits and the
table-moving specs are keyed on it.  Small change by construction:
nothing in the kernel consumes `uexec_slot` yet, so the re-key touches
UexecSlot/UexecCond/USyncKernel only.  `uvis_tf` keeps the full
36-word list (words 0/1/2/4 are kernel words, dead weight in the key;
a later refinement may restrict to the 32 user-relevant words — epc,
word 3, IS user-visible and stays).

## THE proc_pt_any ELIMINATION CAMPAIGN (owner-ruled)

`proc_pt_any` is a spec smell: a file whose contract holds it cannot
say what happens to the process state.  EVERY instance gets converted
to the memory-indexed form and `proc_pt_any` is DELETED at the end.
The conversion is INCREMENTAL and BOTTOM-UP — a caller cannot be
converted before its callees, since its proof must thread the callee's
named image.  Fault-only paths become same-`M` by `SpecVmfault`'s
`proc_ptm` theorem; genuine writers get their precise M-effect specs
(win 2) as they convert.  The tiers, bottom-up: vm.c leaves
(copyin/copyout/copyinstr/walkaddr) → fetch/arg layer → either_copy →
file/pipe/console read-write → syscall dispatch → exec cone → usertrap
arms → the residue crossings (`ut_res_pt_open/close`, allocproc,
freeproc, kexit) → delete `proc_pt_any` (and `proc_pt_at_any`).  The
full per-declaration inventory and DAG is the session sweep log
§L1-INV; the per-entry M-effect worklist is §B4.

FIVE RULES THE CAMPAIGN RUNS ON:

- **A leaf's `_mem` form is the PRIMITIVE; its `proc_pt_any` form is a
  five-line corollary** (`ProcPtOwn.proc_pt_ptm` in, `proc_ptm_pt` out —
  `ProofCopyin.wp_copyin_sconf` WAS the worked recipe, until tier 3
  deleted it too).  When a leaf's last ∃-caller converts, DELETE the
  corollary rather than keep it.
- **Re-alting a copy loop to the lazy view is mechanical** once the loop
  names its source bytes: swap `proc_pt_acc_rep0` / `proc_pt_rebuild` /
  `proc_pt_page_acc(_vmfault)` for their `proc_ptm`
  twins, and hand the borrowed page over NAMED, rejoining with
  `ByteBuf.bb_join3_fn` rather than the existential `bb_join3` — an
  existential join is what stops a read-only borrow from closing at the
  image it opened at.
- **A PRECISE POST NAMES THE MOVE, NOT A FRESH IMAGE.**  Where a writer
  can stop part-way, keep the existential over the PREFIX LENGTH -- a
  `nat` -- and write the image as a function of it
  (`umem_wr M dst d src`).  `∃ M', ⌜P M'⌝ ∗ … M'` type-checks and says
  the same thing, but it is not an equation and a caller cannot rewrite
  with it.
- **A LOOP'S WINDOW NEEDS ITS CURSOR PINNED.**  A byte-at-a-time copy
  loop carries a cursor with no stated relation to the entry address,
  which makes the round's `umem_wr` uncomposable with the run already
  written.  The invariant that fixes it is one line -- `cur = pa_add dst
  k`, `k` the count delivered so far -- and adding it is most of the diff
  in consoleread and piperead.  `UserPtTree.umem_wr_app` then appends the
  round with NO no-wrap side condition, because the run is keyed by
  `add_vec_int`.
- **RE-KEYING AN EXIT ONTO A MOVED BLOCK CANNOT CARRY A WINDOW READ OFF
  THAT BLOCK.**  Two runs at the SAME base do not compose (`umem_wr`
  promises nothing about a run that wraps), so an exit that a shift
  lemma re-bases must key its window on a bare entry image carried as its
  own parameter -- `ProofConsoleread.cr_ret`'s `Ment`.
- **WHEN A WRITER'S POST ALREADY CARRIES A COUNT, SPEND THE FAILURE ARM'S
  EXISTENTIAL BY RE-INSTANTIATING THAT COUNT.**  readi's `-1` exit used
  to report the loop counter, leaving the partly-copied chunk invisible
  and forcing an `∃ d` on the image.  Reporting *counter + what the
  failing chunk managed* makes one number do both jobs and leaves readi's
  post with NO existential at all.
- **DROPPING A `∀ M'` FROM A POST BREAKS CALLERS THAT WERE PASSING A
  DIFFERENT IMAGE, SILENTLY-UNTIL-IT-DOESN'T.**  While the post bound
  `∀ M'`, a caller could hand the callee `upd_usM U Mx` in place of `U`
  and the two closers stayed CONVERTIBLE -- the bound `M'` overwrote
  `Mx` either way.  Same-`M` ends that: the block now really is at
  `us_M U`, and every such call site has to drop its threaded image
  (`ProofSysUnlink`'s `su_w1_seam` lost its `Mp` binder for exactly this
  reason).  The tell is `iSpecialize: cannot instantiate … (upd_usM U Mx)
  … with … U`.
- **Converting a callee's post breaks its callers even when their own
  specs do not move, and the fix is a SUBSTITUTION.**  Delete the `M'`
  binder at the `iIntros` and textually replace
  `upd_usM (us_upt U P') M'` by `us_upt U P'` through the file; the
  caller's own ∃-weakened post then closes by unification at
  `M' := us_M U` and needs no edit.  That is what lets one tier convert
  without dragging the tier above it in.

STATE: tiers 0 (vm.c leaves), 1 (fetch/arg), 2 (`either_copy`) and 3
(the file / pipe / console read-write layer) are DONE, and so are the
three items that were ready out of order.  `either_copyin_post` is
same-`U`; `either_copyout_post` is the campaign's FIRST PRECISE WRITER --

```coq
∃ (P' : uptd) (d : nat),
  ⌜uptd_ext (pv_upt (us_V U)) P'⌝ ∗ ⌜either_copyout_ran len r d⌝ ∗
  proc_priv_core p pid
    (upd_usM (us_upt U P') (umem_wr (us_M U) dst d src_bytes))
```

-- the entry image with the copied prefix written at `dst`, an EQUATION
rather than a fresh binder.  TIER 3 lifted that through nine contracts:
`wp_readi_sconf`, `wp_consoleread_sconf`, `wp_piperead_sconf`,
`wp_filestat_sconf` and `wp_fileread_sconf` are PRECISE (the block comes
back at `umem_wr (us_M U) dst d bs`, with `d` a length and `bs` a byte
function -- never a `gmap`); `wp_writei_sconf`/`_gen`,
`wp_consolewrite_sconf`, `wp_pipewrite_sconf` and `wp_filewrite_sconf`
are SAME-`M`.  readi's post carries NO existential at all: its `tot` is
both the reported count and the window's length.

The window vocabulary is `UserPtTree`'s: `umem_wr_app` (adjacent runs
append, no no-wrap side condition), `umem_wr_ext`, and `umem_wrote M M'
dst d` (`∃ src, M' = umem_wr M dst d src`) with `_0`/`_app`/`_out`/`_dom`
for a reader whose source is a DEVICE and whose bytes therefore cannot be
named -- the console ring, the far end of a pipe.

`wp_vmfault_sconf` and `wp_uvmunmap_sconf` are deleted (no callers left),
and so now are `either_copyout_post_any` and `wp_copyin_sconf`
(piperead, its last caller, moved to `wp_copyin_sconf_mem`);
`wp_copyout_sconf` survives on ProofSysPipe ×2, ProofKwait ×1 and
ProofKexecC ×2.  The
six fs-syscall specs no longer bind `∀ M'`.  `SpecUvmclear` and
`SpecProcFreepagetable` have `_mem` forms.  The frontier is TIER 4, the
syscall dispatch: sys_read/write/fstat/wait/pipe/sbrk, growproc, kwait,
and then `wp_syscall_sconf`, none of which needs new algebra.

## The ledger

1. **Re-key the residue's conjunct** from the ∀-state `uexec_wp` to the
   trapframe-keyed slot at `ut_own`'s own `V` (and an `M` per item 2).
   Localized by design to `UsertrapRes.v` plus the dispatcher's deposit
   obligations (the accessor's closer is the deposit channel).  One
   ruling obtained, one open:
   - PLACEMENT — RULED, twice revised, now SETTLED (owner): the slot
     is STORAGE-FREE — never a conjunct of `proc_priv` OR `ut_own`.
     Follow the lifetime: running during user execution; in usertrap's
     proof context (cause-shaped) from trap entry to deposit — a
     mid-excursion park's closure captures the context, and the slot
     types are hart-free, so no stored row is needed for
     park-survival; at a concrete just-built key from deposit to sret;
     and delivered at process creation through the park channel
     (kfork's lane-H premise / userinit).  Storing it in the block
     would ERASE the discriminating knowledge (which scause, which
     ret) the surrounding proof holds for free, and would thread a
     conjunct through 216 `proc_priv` consumers none of which may
     touch it.  Instead: EXPLICIT BOUNDARY ROWS on the trap chain —
     `usertrap`'s precondition gains the cause-indexed
     `uexec_ret sc_v V M` (its boundary already names `sc_v`); its
     arms' posts, and the composed round's post, carry the PRECISE
     slot at the final key; userret's application site consumes it
     from the round's post.  `ut_own`'s slot row and its accessors
     are DELETED, not moved.  What survives of the earlier ruling is
     M-NAMING (item 2): the block's page-contents existential becomes
     a named `M` so the rows are stateable, and the trap-chain
     boundaries get SLOTTED VARIANTS of the residue whose `∃ V M`
     scope includes the row (a phase-form beside
     `ut_res`/`parked`/`bare`, seen only by the trap chain).  Costs
     accepted: boundary-spec surgery on uservec/usertrap/userret, and
     the run-site agreement (item 3) becomes unavoidable even for the
     generic era once the rows are keyed.
   - THE `sp_idx` TIER QUESTION: `UexecSlot.v` deliberately does not
     import `UmodeAbi` (`tf_resume_gpr_sp` is stated at
     `Regidx (mword_of_int 2)`, convertible with `sp_idx`).  If the
     re-key puts `uexec_slot` into `UsertrapRes.v`'s cone and anyone
     wants the `sp_idx` spelling, `UmodeAbi` enters the residue's build
     path — rule first.

2. **Pin the image for a verified process.**  Both run sites today
   receive `M` existentially (`umem_any` at the entry, `user_pt_any` from
   `uservec_post`).  A verified mode of the residue must carry
   `umem_own`-at-a-known-`M` — `M` is the one resume ingredient `V` does
   not determine.  Nothing landed depends on the image being anonymous,
   so this is additive.

3. **Boundary exposure.**  For the loop to apply a trapframe-keyed slot,
   the round's post must EXPOSE that the returned registers are the
   residue's trapframe words and the returned memory its image.
   `SpecUserret.wp_userret_pt` already says the register half at its own
   level (its continuation returns `userret_gpr m vra…` built from the
   tf-word arguments — lane D confirmed the loop's application tuple is
   literally the `tf_resume_gpr b V` / `tf_resume_pc V` pair); the
   composed `wp_uservec_pt` post must stop existentially hiding it.

4. **The deposit-covering formulation** — how a deposited slot covers the
   kernel's own writes between deposit and resume (a syscall's
   `tf->a0 := ret` / `epc += 4`; read() filling the `(a1, a2)` buffer
   window; a vmfault's zero page).  DELIBERATELY UNDESIGNED (owner
   ruling): it cannot be a pure predicate on `(V, M)` pairs — read()'s
   widening relates the delivered bytes to file-system state, an
   iProp-level fact — so it will be an iProp-based,
   universally-quantified shape, designed against the first concrete
   proof obligation inside item 5.  Raw material on the process side:
   `usys_ret`'s `∀ ret` continuation (the syscall case) and
   `uv_intr_wp`'s resume wand (the identity case).

   **THE SYSCALL SHAPE (owner-specified).**  At an ecall, the u-mode
   proof returns a UNIVERSALLY QUANTIFIED WP: forall a0, resuming with
   the rest of `V` and `M` exactly the same is ok — spelled over the
   BUMPED trapframe, `uexec_slot_sc V M := ∀ r, uexec_slot
   (V[epc := epc+4][a0 := r]) M` — and, for buffer-filling syscalls
   later, additionally universal over the updated memory region.  So
   usertrap DISTINGUISHES trap kinds: a transparent trap (device
   interrupt) returns the PRECISE `uexec_slot V M`, deposited at trap
   entry and untouched; a syscall trap returns the sc shape, carried
   through the dispatch IN THE PROOF (a mid-syscall park's closure
   captures it; residue-residence is only needed across user
   execution), and the dispatcher instantiates it at its concrete ret
   — holding the precise slot at exactly the `V'` it built — before
   userret.  NO SHAPE DISJUNCTION IN `proc_priv` (owner ruling): the
   disjunction's discriminant is the trap cause, which `proc_priv` has
   no business knowing — the multiplexing lives at USERTRAP'S BOUNDARY,
   which already takes `sc_v` as an argument: a cause-indexed family
   `uexec_ret sc V M := if sc = ecall then uexec_slot_sc V M else
   uexec_slot V M` in usertrap's precondition, correlated with the
   frame's actual cause by the user-side trap arms (they know theirs
   concretely).  `proc_priv` holds ONE row — its home state, the
   precise `uexec_slot V M` (transitionally the ∀-state form until the
   run-site agreement lands; a sequential type change, never a
   disjunction) — and is HOLED throughout the kernel excursion, so the
   mid-syscall closers (copyout, a0/epc writes) face no slot
   obligations at all; the cause-shaped WP travels in usertrap's proof
   context (mid-syscall parks capture it in the closure), and the
   deposit back into `proc_priv` happens where the shape is precise
   again — immediately on the transparent arm, at
   instantiation-at-ret on the syscall arm.  Sync fits entirely:
   sync = the sc shape, exit's return is never consumed.

   **VMFAULT REPRESENTATION WART.**  "Zero-fill vmfault is transparent"
   requires the process-visible `M` to be the sz-region view with
   unbacked pages reading as zeros (fault-invisible); today `umem_own`
   pins `dom M = uva_dom pt`, so a fault EXTENDS `M`.  A representation
   change on the `user_pt_inv`/umode side, deferred until a faulting
   program forces it (sync never faults).  RESOLVED BY RULING (owner): the
   wart was a representation mismatch, not a missing proof —
   `SpecVmfault`'s `proc_ptm` form already proves vmfault preserves
   `M` at the sz-region view (`umem_lazy`; unbacked pages read as
   zeros).  `proc_priv`'s boundary conjunct becomes
   `proc_ptm (pv_upt V) (uint (pv_sz V)) M` (sz is already in `V`),
   making copyin and every fault-only path same-`M` by the existing
   theorem; the ∃-weakened worklist shrinks to the genuine writers;
   the mapped-domain view stays at the sub-`proc_priv` tier.  Lands
   together with the USTATE RECORD (owner ruling):
   `Record ustate := { us_V : pprivate; us_M : gmap Z (bv 8) }`,
   `proc_priv γf pa pid (U : ustate)` — future user-visible state
   (fd view, PID) becomes FIELDS, never arity changes; the slot
   re-keys on the record.

   **THE FORK CLAUSE (owner-specified).**  fork's spec will require the
   u-mode proof to deposit TWO WPs at the ecall: one requiring return
   value 0 (the child) and one handling the non-zero return (the
   parent), everything else — `M`, the other registers — identical.
   The kernel-side seam already exists: kfork's "parking a child
   consumes a `uexec_wp`" premise takes the child half (replacing
   today's generic mint in sys_fork's proof), and the parent half is
   the slot returned through the ecall's return channel.  In the
   trapframe+image keying: `V_child` = the parent's `V` modulo the a0
   word (plus fresh `pv_upt`/pid), and the child's image is the SAME
   va-keyed `M` (fork copies pages; the va view is address-space
   independent).  The parent continuation must also cover the failure
   arm (`a0 = -1`, no child, child WP not consumed); the kernel's spec
   selects the arm.

5. **Discharge `uv_cap` from the kernel** (usertrap/userret round trip +
   per-syscall kernel specs) — the step that turns `sync_uexec_slot`'s
   one assumption into a theorem.  Known shape: `uv_cap` is `□` while the
   residue is linear, resolved by the Umode tier's frames
   (`uv_trap_frame`, `uv_run`) gaining a `Rut pt` conjunct — the parked
   residue travels in the frames exactly as the safety tier's do; the
   tier's port history says the `USpec*`/`UProof*` statements tolerate an
   opaque added conjunct, and the engine (`WpUmodeStep`) is where it
   lands.  Also owed here: the reverse direction of
   `UmodeKernelTie`'s movers — `user_pt_inv`'s three pure facts
   (`dom M = uva_dom pt`, `uva_pa_inj`, `upt_acc_wf`) are dropped on the
   way into the Umode tier and must be re-supplied from the table on the
   way back.
