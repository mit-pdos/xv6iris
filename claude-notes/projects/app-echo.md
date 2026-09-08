# Project: the ECHO application — `echo hello world` end to end, file system unmodified

Design of record: [`../design/applications.md`](../design/applications.md).
This file is what is LEFT to make `AppEcho` an instance of
`App.xv6_app_adequacy`, in execution order.  The scaffold itself — the
record, the theorem, the two-instance claim (running in `app_inv`, durable
in the crash slot), the transport, the birth step, the era mint — is
landed (the top banner of `iris/App.v`).

## The target statement

At the real image, powered off, never booted: for every run,

    disc κs -> good_out κs /\ pristine (v_disk g2)

where `disc` says every `ObsUartIn` byte of every power cycle so far is a
prefix of `(echo hello world\n)*`, `good_out` says every cycle's
`ObsUartOut` bytes are a prefix of the expected console stream for that
cycle's inputs, and `pristine dk` says the committed map `dk` recovers to
has the mkfs image's abstract view (so init, sh and echo are the image's
binaries at every reboot).

## Lanes (design §6), with what each unblocks

- [ ] **L2 — the step moves to the process.**  RULED 2026-09-07 (owner):
  each syscall's precondition is its landed contract's ONE-SHOT AU bundle,
  supplied by the process through the ecall arm the way `UexecRetExec`
  already does for exec; no persistent promise crosses the seam.  Then
  the `fsabs_*` dischargers, `app_step_acc`, `app_auto`, the mint's
  license premise and `Happ_auto` are deleted.  Plan and open items
  below.  Gate: none (L3 landed).
- [x] ~~**L3 — round E of `app-instances.md`**~~ (kernel side, application-
  independent).  LANDED: every view move on a dispatched path is an AU fire
  or a `_step`; link, mkdir, create's legs, the write and `iput`'s free are
  AU forms with their deltas (`fs-syscall-specs.md` §4); the only `_same`
  movers left are the two between absent rows (ilock's fresh-inode fill,
  the escrow deposit's free); `top_move` and the `_auto` movers are gone.
  `Happ_auto` stays for L2, which is what it is now the only payer of.
- [x] ~~**L4 — the crash predicate's application conjunct.**~~  Dissolved
  into the durable instance and the transport (round C): the claim rides
  the crash slot beside the snapshot and crosses at commit/clone/boot as a
  resource.
- [ ] **L5 — console input tie.**  Unblocks: sh minting the taint at the
  point it leaves the discipline; hence L2's last step and L6's sh.
  Gate: none (console.c is proven; the ledger is new).
- [ ] **L6 — the programs.**  init and sh on the Uk engine with paid
  ecalls; the exec-site gate at the observed image; fork's real row.
  Gate: L2, L5; `user-wp-slot.md` items 1–3.
- [ ] **L7 — the output side.**  `echo_out`, `good_out`, the tx wand.
  Gate: L6 (the writes' receipts).

## What is in `iris/AppEcho.v` today

The pure data and the obligations provable WITHOUT any lane:

- `echo_line` ("echo hello world\n" as bytes), `ins` (the input bytes of
  a history), `star_prefix pat l` ("l is a prefix of pat^*", spelled as
  one list equality so it is decidable and prefix-closed by one `take`),
  `disc_seg`, and `disc h := Forall disc_seg (cycles_of h)` — every
  cycle's input so far keeps the discipline; the open cycle is the last
  element of `cycles_of` while the power is on.  Closure laws:
  `disc_out` (an output byte moves nothing), `disc_power` (a power event
  moves nothing), `disc_in` (breaking the discipline is forever).
- The FIXED PART: `echo_fixed := gname`, `echo_cl γ := mono_nat_auth_own γ 1 0`,
  `echo_birth` (`Hbirth`); the ledger `echo_R γ h := mono_nat_auth_own γ 1 (echo_phase h)`
  (0 while `disc h`, 1 after) with `echo_R_alloc` (`HR0`, off `echo_cl`),
  `echo_R_pow` (`Hpow`), `echo_R_tx`, `echo_R_rx` (the two UART arms, as
  basic updates over the ledger alone — the theorem's wands frame the UART
  ghosts around them) and `echo_R_untainted` (`disc h` and the taint
  `mono_nat_lb_own γ 1` contradict: what the end of the run reads).
- `echo_fs_pure av := era0_pins av /\ era0_sh_pins av` over the VIEW, and
  `echo_fs av := ⌜echo_fs_pure av⌝` as the application's `iProp` predicate
  (the /init and /sh binaries are the image's, path and content; per inum,
  not a whole-map equality); `echo_xfer` (`Happ_xfer`, by
  `app_xfer_raw_pure`: a pure claim duplicates); `echo_fs_era0`/`echo_init`
  (`Happ_init` at the image, off `FsInitPinBoot.era0_recovery_pins` /
  `FsShPin.era0_recovery_sh_pins`).

Not there, on purpose: a theorem.  `Happ_auto` is payable only by the
generic application until L3 (and then the steps only from a process,
L2); `Hphi` needs L2 and L7.  A theorem taking those as hypotheses would be
the GAP-premise trap (`durable-notes.md`).  Echo's own pin (`/echo`'s
inum and bytes, `FsShPin`'s shape) joins `echo_fs` with L6.

## L2 — the plan, corrected 2026-09-07 (the first two drafts were wrong; see the end)

**THE RULING (owner, 2026-09-07).**  No persistent promise crosses the
ecall seam.  Each syscall's precondition is the ONE-SHOT AU bundle its
landed contract already defines, supplied by the process; there is no
"universal AU", no pure delta table, no kernel-side discharger.

#### What is landed (design/fs-syscall-specs.md; the `SpecSys*AU.v` files)

Every fs syscall has an AU-form contract whose CLIENT-supplied part is a
BUNDLE of one-shot fupds, one per linearization instant the code has:

- **the walk** — `open_walk_pre_era γfs cw P Pmiss` / `mknod_walk_pre_era`
  (parent prefix): for the path string fetched, one `={⊤}=∗` yielding the
  cursor `P 0 start` and ONE `FsAbs.ax_hop` PER PATH COMPONENT, each fired
  in `dirlookup` under that directory's lock against its then-current
  entry map: `P k d -∗ lend d ents ={⊤}=∗ lend d ents ∗ (P (S k) c | Pmiss k d)`.
  `P`/`Pmiss` are the client's own cursor predicates.
- **read-kind commits** — `aopen_commit_at`, `dlookup_commit_at`: single
  phase, borrow the kernel's half `ghost_map_auth (γtop) (1/2) I`, learn
  the row purely (`arow_at`), return the receipt `Φ (abs_view I) i a`.
- **write-kind commits** — `acre_commit_at`, `atrunc_commit_at`,
  `awrite_full_at`/`awrite_part_at`: TWO PHASES.  Phase 1 borrows the
  pre-map at the instant and the client returns `AppInv.app_step i I
  (delta …)` — its application claim survives THIS delta — plus phase 2,
  which borrows the post-map (the client WITNESSES the delta applied) and
  returns the receipt.
- **the undo legs** — `cre_child_unfired = aarm_commit_at ∗ aunarm_commit_at`:
  the child's row appears at nlink 1; if the parent's entry write fails
  the unarm fires instead.
- **write's chain** — `awrite_chain Γ E i γo Φ k cnt`: `wchunks n` nodes,
  each `full ∧ part` (the kernel picks), each returning the NEXT node;
  the partial arm ends the loop.  One fire per `begin_op`…`end_op` chunk.
- **exec** — `SpecKexecAU.exec_au_pre S … = walk ∗ aopen_commit_at Φo ∗
  exec_slot_pre S Φo …`, where `exec_slot_pre : ∀ av i f nl W', Φo av i
  (AFile f) -∗ ⌜loadable f⌝ -∗ ⌜kexec_image_ok f … W'⌝ -∗ S W'` — GIVEN
  the observation receipt for the file kexec read and the key it built,
  the caller supplies the slot at that key.  NO PINNING IN THE SPEC: a
  caller narrows the files it answers for through its own `Φo`.
- **the posts return what did not fire** — e.g. `open_post_fail_plain =
  bundle unspent ∨ (walk died: dead receipt ∗ both commits unfired) ∨
  (observation fired ∗ trunc unfired)`.  "Unspent" is the post's
  disjunction; nothing inside an AU says "fire me unspent".

**Who supplies the bundle today.**  The DISPATCHER (`ProofSyscall`), at
the trivial families (`fun _ _ => True`), paying every write-kind
commit's `app_step` out of the parked license via the `fsabs_*`
dischargers.  EXCEPT exec: `UexecRetExec` (a parallel form of the trap
contract behind the ambient class `uexecXG`, payload `xbundle X W`) makes
the PROCESS hand over `sys_exec_au_pre uslot_x … P Pmiss Φo …` at its exec
ecall — families existential in the arm ("some bundle at this key"),
re-bound by the dispatch; the slot wand concludes at the fixpoint
variable.  It is a GIVE: on failure the refunded bundle stays in the
kernel's frame (a program cannot retry exec).  `UexecExecInst.v` is the
kernel-side instance.

#### L2 = do for every fs syscall what exec already does

- The ecall arm of `UexecRet.uexec_ret_F` splits off each syscall number
  that HAS an AU contract and demands that contract's bundle from the
  process, through the same class mechanism (`UexecRetExec` and
  `UexecRetFs` fold into `uexec_ret_F`, as both headers say they will).
  Syscalls without an fs contract keep today's arm.  Verified programs
  prove their bundles — the walk cursor, the commits (each write-kind
  commit's `app_step` for THEIR predicate), the receipts they want.
- The dispatcher passes the process's bundle to the sealed contract
  instead of the trivial one (exec's arm at ProofSyscall ~2902 is the
  model).  The `fsabs_*` dischargers, `app_step_acc`, `app_auto`, the
  mint's license premise and `Happ_auto` are then deleted (§(iv) items
  1, 3–5 stand; item 2, the leftover `□ fw_app_write_step` on the plain
  write contract, is retired in favour of the chain's per-chunk step).
- **The generic slot.**  An unverified program's slot must produce every
  bundle at the trivial families; the write-kind `app_step`s are payable
  iff the application predicate is trivially true — `app_triv` by
  definition, echo from the taint (`taint ⊢ ∀ av, echo_pred av`).  So
  `uexec_wp_uslot`/`cond_entry_slot` gain the premise `□ ∀ av, app_pred
  app_run av` and `UEXEC_GEN` carries it.  This is not a design choice;
  it is what "unconstrained abstract state" means as a premise.
- **exec needs nothing new.**  Pre-taint, sh's `Φo`/cursor at the
  fire-time view (opening `app_inv` inside the commit for its own pins)
  proves the observed file is echo's and answers with echo's verified
  slot; in the taint branch it answers with the generic slot.  Whether
  the kernel's proof ever takes `exec_post_ok`'s "(b) generic mint" arm
  for an x-tier process must be checked (`ProofKexecAU`).

#### What is actually left to decide for L2-a

- ~~D-A~~ **REFUNDS, RULED 2026-09-07 (owner): every piece of a bundle is
  `AU ∧ R`,** with `R` the caller-chosen REFUND — provable from the same
  resources the caller spent building the AU (both conjuncts from one
  context).  The kernel eliminates to the AU side at the fire and to `R`
  when it hands the piece back unfired.  What this costs in the landed
  shape: each piece's definition gains one `∧ R` parameter; the posts are
  UNCHANGED, because they already return unfired pieces verbatim
  (`open_post_fail_plain`'s three arms; `write_post_fail_at` returns
  `awrite_chain … (length bss + x)`, the unfired tail, `x ≤ 1`).  The
  halfway abort is NOT a real issue: a bundle is a `∗` of independent
  one-shot pieces, no piece is ever half-fired (both commit phases sit in
  one `ftopN` critical section; a hop is one fupd), sequencing rides the
  cursor `P k d` which the death receipt returns, and the chain is NESTED
  (node k's phase 2 yields node k+1), so `R_k` on the outermost unfired
  node covers everything invested in the tail.  Two real obligations on
  the caller: a resource used by two pieces must be pre-fractioned (one
  piece per fraction), and a FIRED piece returns its investment only
  through the receipt the caller chose (`aopen_commit_at_pinned` already
  hands the `nview` share back inside `Φ`).  CONSEQUENCE: the arm must be
  the DEPOSIT shape (the post read back under the arm's ∀, the fd-row
  pilot's route) and not `UexecRetExec`'s give, which drops the post.
- **THE WRITE CHAIN'S REFUND IS A PREFIX CURSOR (owner, 2026-09-07).**  Node
  k of the chain becomes `Q k ∧ (full_k ∧ part_k)` and the base case
  `chain k 0 := Q k`, with `Q k` the caller's predicate "after the prefix
  of k chunks" — the walk's cursor `P k d`, carried over to chunks.  It
  fits because the chain is NESTED: node k+1 is built by the caller
  INSIDE node k's phase 2, where the post-map witness
  (`abs_view I' = delta_write i off bs (abs_view I)`, and for the partial
  arm the counted `r` beside the landed run) is in hand, so `Q (k+1)`
  genuinely knows chunk k landed.  The kernel eliminates to the arms when
  it fires chunk k and returns the node otherwise; the caller eliminates
  to `Q` at whatever position the loop stopped — success (`length bss`
  chunks, the chain "resumes at the receipts' length"), the partial arm
  (`x = 1`, one past the receipts), or an early -1 (`x = 0`).  So the
  three returns of `write_post_ok_at`/`write_post_fail_at` collapse to
  "here is the node at the stop position", and `Q` subsumes both the
  refund `R` and the per-chunk receipt family `Φ`/`wri_receipts`/
  `wri_part_receipt`, which can go.  AND `Q` CAN CARRY THE BUFFER (owner's
  question, 2026-09-07; my "cannot" was wrong).  Each node's phase 1
  ∀-binds the chunk's bytes `bs` and the landed contract ties them to the
  caller's buffer only once, in the post, on the concatenation
  (`ubytes_at M ua (concat bss)`, ruling A) — a presentation choice made
  because the chunk DECOMPOSITION is existential.  But the source side
  chains by construction (filewrite reads `addr + i` at its own running
  total), and the per-chunk fact is ALREADY in the proof:
  `SpecFilewriteAU.v:299` has `⌜ubytes_at M (add_vec_int ua t) bs⌝` at
  running total `t`, and the post's concatenation is `ubytes_at_app` over
  it.  So node k's phase 1 gains the pure premise `⌜ubytes_at M (ua + tot)
  bs⌝` with `tot` the total the cursor `Q k` carries, and `Q (k+1)` can
  say "the file holds the first `tot + |bs|` bytes of my buffer, spliced
  at the offsets I saw".  The per-chunk FILE offsets stay unrelated across
  instants (another writer through the same `struct file` may move
  `f->off` between chunks) — known at each fire from the lent
  `off_gv` half, not chained.
- **D-B. Which syscalls in the first cut.**  Those with landed AU
  contracts: mknod, open (plain/create), unlink, link, chdir, write,
  exec; plus whatever mkdir/read have.  Inventory before the brief.
- ~~D-C~~ **ONE SPEC PER SYSCALL — RULED 2026-09-07 (owner).**  Raised on
  `sys_write`, which has THREE proved contracts today (the plain
  `SpecSysWrite` over every descriptor kind, whose FD_INODE arm takes the
  persistent premise `SpecFilewrite.fw_app_write_step`, minted from the
  license at ProofSyscall:4458; `SpecSysWriteAUEra`, the chain, premise-
  pinned to an open writable inode; `SpecSysWriteConsAU`, the console
  arm) with the dispatcher choosing by the descriptor's state
  (`sysc_write_inode`, ~4478) — and then generalised: EVERY syscall gets
  ONE contract.  Its arms are keyed on what the code keys on (the
  descriptor's `fdstate`: `FdInode` → the chain, `FdDevice` console → the
  console receipt, `FdPipe` → pipewrite's, closed/unwritable → -1; for
  path syscalls, the walk's outcome), the AU form IS the contract, and the
  plain forms retire.  Stable forms stay as DERIVED corollaries (a lemma,
  never a second proof against the code).  THIS SUPERSEDES R10
  ("landed contracts never move; new specs are parallel forms") for the
  syscall layer: the parallel forms were the transitional device and they
  are now folded.  Inventory of the parallel families to fold (2026-09-07):
  write ×3 (+`SpecFilewrite`/`AU`/`Cons`), read ×3 (`Read`/`AU`/`AUAt`),
  open ×2, mknod ×3 (`Mknod`/`AU`/`AUEra`), unlink ×2, chdir ×2, dup ×2,
  exec ×2 (+ `SpecKexec`/`AU`/`B2`/`B3`/`Pin`/`Pinned`), create ×4
  (`Create`/`AU`/`AUF`/`AUFOpen`), sync ×2.  Single-form today: link,
  mkdir, close, pipe, fstat, fork, exit, wait, kill, getpid, sbrk, pause,
  uptime.  The plain forms' remaining consumers are their own proof files
  and the dispatcher (`grep -l "SpecSysWrite\." iris/*.v` etc.), so the
  fold is per syscall: restate the AU contract with all arms, re-point the
  dispatcher, delete the plain statement and proof.  This is L2-b's shape
  now — the unified contract is where the process's bundle lands.
Not decisions: the generic slot's premise (above); pinning (echo's own
`Φo`, never the spec's); the write chain (landed).

#### Why the first two drafts were wrong (so nobody re-proposes them)

Draft 1 (commit `d26c19aea`) made the step a `□` promise: refuted above.
Draft 2 (this file, earlier today) kept a SINGLE per-call AU over a pure
delta table `sys_delta` with kernel-side `fsabs_*_pre_au` dischargers.
That was a parallel form of the landed bundles — the near-duplicate the
guiding principle forbids — and it could not be right: the AU shape is
per syscall (a hop per path component, two-phase commits, undo legs, a
chain for write, a slot wand for exec), and the process supplies THE
BUNDLE, not a summary of it.  `sys_delta`, `app_au`, `app_au_any`,
`AppAu.v`, `FsSysDelta.v`, `sys_ask` are all withdrawn.

## The two options for the generic slot's supply — RULED 2026-09-07: option 2

§(iv) item 6 leaves two ways to make every ecall payable: (1) PREVENT bad
input, drop the taint, and prove no syscall ever violates the invariant;
(2) SWITCH to a tainted mode at the first off-discipline byte, after which
processes run the generic slot.  Findings:

- **Option 1 in its pure form is not available.**  Adequacy quantifies
  over every environment byte and the rx wand must be provable for ANY
  `b` (uart-trace.md ruling 3, the design's own note on `Hrx`).  "Prevent"
  means restricting `prim_step`, which ruling 3 refused.  The only way to
  make the post-bad-byte WP obligations discharge without a semantic change
  is a WP-level vacuity token minted at the bad byte — which IS the taint.
  Option 1 also does not save L5: sh's verified path needs to know the
  bytes it reads are the typed ones to follow the disciplined parse at all.
- **Option 2 works, but "all slots become generic" is not a kernel
  mechanism.**  A slot is the process's OWN WP; each verified program
  switches ITSELF at the receipt where the taint first reaches it, by
  applying the generic inhabitant with the taint as its supply at the
  current key.  Most never switch: init's and echo's calls are all
  view-preserving, and a view-preserving AU is trivial for ANY predicate.
- **Where the taint is minted and how it travels (= L5's shape).**  The rx
  wand fires INSIDE `WpUart.wp_uart_loop` (rx arm, ~WpUart.v:930) with the
  UART invariant open — kernel-visible.  Give the loop's invariant a TAG
  COLUMN: per pushed byte a persistent, application-chosen iProp the wand
  returns beside `R h'` (opaque `T : list mobs -> iProp`, so no era
  identity is needed — the dual of Lane C's `uart_acc`).  uartgetc's RHR
  read pulls byte + tag; a kernel ledger threads it consoleintr → cons.buf
  → consoleread → the read syscall's AU RECEIPT.  For echo the tag is
  "prefix still disciplined ∨ taint"; sh's `gets` reads one byte per
  `read`, and `star_prefix` is prefix-closed, so a per-byte check suffices.
- **Every fs-CONTENT-dependent AU gets a taint branch.**  Its fire-time
  claim is `taint ∨ pins`.  Pre-taint the pins branch plus `kexec_ok`'s
  success arm makes the exec gate hold (init's exec sh, sh's exec echo);
  in the taint branch the AU hands the taint to the exec mint as the
  generic slot's supply through its KERNEL-FACING output.  So the AU's
  output is `▷ P av' ∗ Ψ` with `Ψ` the kernel's ask (exec: gate ∨ supply).
  Fork needs no supply: the child's slot is the parent's second conjunct;
  J's re-mint on the fork arm must go (fork's real row) because re-minting
  would need a supply.  Children of a tainted process inherit the
  persistent taint (`Forkable` trivially).
- **No global atomic switch is needed.**  Between the bad push and sh's
  read every process is still verified and pins-preserving; after it,
  each opener of `app_inv` gets the disjunction and handles both arms.
  The lb is at the fixed part's gname, so it survives reboots; era n+1
  boots at `taint ∨ pins` and init's exec-sh AU takes the taint branch.
  `Hphi` is unchanged.
- **Costs specific to option 2:** the disjunction predicate (Q4), the tag
  column in `WpUart` (machine layer), the console ledger (kernel), the
  taint branch in each content-dependent continuation, the supply field in
  `UEXEC_GEN`.  Common to both options: L5's tie, the exec-site forcing
  function, fork's real row, the per-program AUs on the disciplined path.

RULED 2026-09-07 (owner): option 2.  It is the only one the semantics
admits and its extra cost is the tag plumbing, which L5 owes in either case.

## Lanes in flight

- ~~**W-UNIFY**~~ LANDED 2026-09-08 (commit `c1d4268d8`; Opus lane, two
  phases, 14 files deleted, +2069/−10994).  sys_write has ONE spec; the
  chain is the prefix-cursor form with the per-chunk buffer tie; the
  design of record is `design/fs-syscall-specs.md` §4 ("AS BUILT" and
  "ONE CONTRACT PER SYSCALL").  `fw_app_write_step` and the receipt
  families are gone; the dispatcher's input is
  `FsAbsInvFire.fsabs_sys_write_in` at the trivial cursor (still paying
  each node's `app_step` from the license — that leaves with the license).
  Follow-up landed (`1d85aa28b`): filewrite's dead `foff_permit_row`
  premise removed; no comment in `iris/*.v` names a folded write form.
  §(iv) item 2 is resolved.  Loose end for a small lane (CONS-FOLD):
  consolewrite itself has two forms (`SpecConsolewrite` plain,
  `SpecConsolewriteLoc` located); the located one is the general (a seed
  premise and a receipt) and the write cone now uses only it, so
  `LinkConsolewrite.v` is dead — fold the plain form into the located
  one and delete the link.  Next lanes cut from the same mold: read (×3 → 1), mknod
  (×3 → 1), open/unlink/chdir/dup/exec (×2 → 1), create (×4 → 1), sync
  (×2 → 1); then the one-shot pieces gain `∧ R`; then the arm change.

- ~~**READ-UNIFY**~~ LANDED 2026-09-08 (Opus lane, two phases; 7 files
  deleted, +931/−4579).  sys_read has ONE spec: `FILEREAD`/`SYSREAD` keep
  their frames and take `Φ` (the observation receipt) and `R` (the refund);
  the inode arm's input is `aread_commit_at … Φ ∧ R` — the first piece
  stated in the `AU ∧ R` shape — and the `n < 0` guard, the one arm that
  does not fire, returns that conjunction; every other descriptor kind gets
  the landed blanket only.  The descriptor-state key `sys_fd_st` is shared
  with write (`SpecArgfd.v`).  Read's arms live beside its commit in
  `FsAbsReadFire.v`; `SpecSysReadAU.v` is the pure vocabulary leaf (its
  name and `SpecSysWriteAU.v`'s are a later rename).  `foff_permit_row`
  and its three lemmas are deleted: both fileread and filewrite move the
  offset shadow inside the piece.  The console READ arm is where the input
  tag (L5) will land; untouched here.

## Decisions outstanding after the 2026-09-07 rulings

For L2-a: only D-B (which syscalls in the first cut; the inventory is
above and is mine).  D-A and D-C are RULED (refund by `AU ∧ R` / the
prefix cursor; one spec per syscall).
For later lanes: the rx wand's tag output (L5), read's receipt (L5),
`kexec_ok`'s success arm and Lane X's chain conjunct (L6), fork's real
row (L6), init's wait null-window row (L6).  Ordering: L2-a → the park
→ L5 → L2-b → L6 → L7.  Q4 stays provisional.
