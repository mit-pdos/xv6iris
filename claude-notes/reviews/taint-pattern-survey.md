# Review: where else the `link ∨ taint` pattern pays (2026-09-17, Fable, read-only)

The owner's question: "see if there's also other parts of the syscall spec or
generic proof that can be made easier with this taint-style invariant/spec
pattern."  Tree `main` at `2931ce499`.  Nothing edited.

## 0. The pattern, and the two facts that decide every verdict below

THE PATTERN (design/pipe.md "The coupling, or the taint"; `iris/PipeQueue.v`):
the kernel invariant's coupling of user-facing ghost to physical state is
`(coupled) ∨ pipe_taint_cred`, `pipe_taint_cred := □ riscv_kill_cred`
(`PipeQueue.v:111`); every payment is `link ∨ taint` (`pipe_wpay`/`pipe_rpay`/
`pipe_cpay`, `PipeQueue.v:291-300`); every post is `fired ∨ (taint ∗ payment
back)` (`pipe_cpost`, `:316`; `pipe_wpost`, `:347`; `pipe_rpost`, `:429`); the
disconnect is permanent (no fresh authority at an existing name); the generic
supply pays the taint arm outright (`UexecExecInst.xv6_sbundle_of_supply_ne`,
`:958`, rows 5/16/21/2 via `fsabs_fileread_in`, `fsabs_filewrite_in`,
`fileclose_cpay_taint`, `fileclose_cpays_taint`).

FACT A — THE GENERIC TIER ALREADY HOLDS THE TAINT EVERYWHERE.  The generic
slot is "reachable ONLY tainted": `UexecRet.uslot_of_creds` (`:2748`),
`uexec_wp_uslot` (`:2816`), `uexec_dep_F_of_supply` (`:2515`),
`UexecCond.cond_entry_slot`, `UexecExecMint.uslot_mint_pay` (`:432`) all take
`□ riscv_kill_cred`, and the generic supply `UexecExecInst.xv6_ssupply :=
app_sup ∗ □ riscv_kill_cred ∗ □ cons_licence` (`:943`) carries it again.  So
ANY kernel row that has a taint arm is already free for the generic proof.
The survey therefore reduces to: (a) which couplings still LACK a taint arm,
so that the generic tier has to conjure a pure fact or thread a resource; and
(b) which premises are being blamed on (a) when they are really the price of a
VERIFIED program's precision.

FACT B — THE TAINT IS NOT IN A VERIFIED PROGRAM'S HANDS, AND MUST NOT BE.
`riscv_kill_cred` is `ai_kill riscvF_app_iface` (`RiscvPtsto.v:632`); for the
echo/file application that is `echo_taint γ := mono_nat_lb_own (eg_taint γ) 1`
(`AppEcho.v:211`, wired at `echo_ifc`, `:1439`); the counter's authority
`echo_cl` is the application's FIXED part, born at the trace slot, moved only
by the console discipline's break.  `app_sup ⊣⊢ taint` for a constraining
application (`AppEcho.echo_taint_of_sup` `:1232` / `echo_sup_of_taint`;
`AppFile.file_taint_of_sup` `:974` / `file_sup_of_taint` `:967`), and the
output licence follows from the taint too (`UInitBoot.v:821`, `□ (echo_taint
-∗ cons_licence)`).  A verified program under an untainted discipline cannot
mint the taint and must not be able to: a program that could taint itself at
an arm it dislikes makes its claim `P ∨ taint` vacuous on that arm — the
vacuity trap of durable-notes in a new coat.  CONSEQUENCE: "pay every
unreached arm with the taint instead of refuting it" is available to the
GENERIC tier and to nobody else.  For a verified program an unreachable arm is
closed by ARM EXCLUSIVITY in the kernel contract, never by a taint.  Every
candidate below is judged against A and B.

## 1. Ranked candidates

### R1 (TAKE, FIRST) — the supply IS the taint: collapse `xv6_ssupply` to one credential

- WHERE.  `UexecExecInst.xv6_ssupply := (app_sup ∗ □ riscv_kill_cred ∗ □
  cons_licence)` (`:943`); `xv6_sbundle_of_supply_ne` destructs it as
  `#(Hsup & Hkc & Hlic)` (`:963`); `UexecExecMint.udep_gen : app_sup -∗ □
  riscv_kill_cred -∗ cons_licence -∗ udep` (`:90`); `filewrite_in_of_sup`
  (`:251`), `udepw_of_sup_write` (`:266`), `udepw_law_of_sup_write` (`:289`),
  `udepw_of_sup_close` (`:303`), `udepw_law_of_sup_close` (`:329`),
  `udepw_of_sup_exit` (`:345`), `uslot_mint`/`_pay`/`_all` (`:397/:432/:451`);
  `FsAbsInvFire.fsabs_fileread_in : cons_licence -∗ app_sup -∗ pipe_taint_cred
  -∗ …` (`:309`), `fsabs_filewrite_in` (`:359`); `UexecRet.uslot_of_creds` /
  `uexec_wp_uslot{,_mint,_triv}` / `uexec_dep_F_of_supply` each take `□
  ssupply -∗ □ riscv_kill_cred` — the taint TWICE, once inside `ssupply` and
  once beside it (`UexecRet.v:2515` says so: "It comes from the same place
  the supply does ([UexecExecInst.xv6_ssupply] is the pair)");
  `UexecCond.cond_entry_slot`; `SystemAdequacy.v:1045` carries the premise
  `(app_sup ⊢ cons_licence)` by hand.  21 callers of `sbundle_of_supply_ne`.
- WHY IT HURTS.  Every generic-tier signature threads three persistent
  credentials that are one fact.  The three are interderivable at BOTH
  instances: generic (`app_sup_raw_triv`, `ai_kill = True`,
  `cons_licence_triv`) and constraining (Fact B).  The kernel already ASSUMES
  the identity: `pipe_taint_cred := □ riscv_kill_cred` is documented as "the
  application's own taint", and `PinnedExec`'s taint arm `T` must yield all
  three at every mint site (`UInitBoot:821` proves the licence half by hand).
  What is conjured is not a precondition but a premise list: three names for
  the disconnect.
- THE PATTERN APPLIED.  Add ONE application law, `al_sup_of_kill : ∀ c r, □
  app_kill A c ⊢ app_sup_raw (app_pred A c) r` to `App.xv6_app_laws`
  (`App.v:275`; `al_sup` already turns `app_sup_raw` into the licence-shaped
  law, so the licence needs no second law).  Then `xv6_ssupply := □
  riscv_kill_cred`, and `app_sup`/`cons_licence` are derived inside
  `xv6_sbundle_of_supply_ne` and `udep_gen`.  `UexecSG.ssupply` stays opaque
  (the class carries only `ctokG` and cannot name the taint — `UexecSG.v:468`
  note); nothing at the class moves.
- WHAT IT REMOVES.  The `□ riscv_kill_cred` argument beside `□ ssupply` on
  `uslot_of_creds`, `uexec_wp_uslot{,_mint,_triv}`, `uexec_dep_F_of_supply`,
  `cond_entry_slot`, `uslot_mint_pay/_all`; the `cons_licence` and `app_sup`
  arguments on `udep_gen`, `filewrite_in_of_sup`, `udepw_*_of_sup_*`,
  `fsabs_fileread_in`, `fsabs_filewrite_in` (each becomes `pipe_taint_cred -∗
  …`); the `SystemAdequacy:1045` premise `(app_sup ⊢ cons_licence)` and its
  hand proof at `UInitBoot:821`; the "TRIPLE" paragraph at
  `UexecExecMint.v:80`.
- WHAT IT COSTS.  ~20 statement sites (all generic-tier, none in a program
  walk); one new class field discharged at three instances (`app_triv`,
  `app_echo`, the file app) by lemmas that exist.  Soundness: the law pins the
  discipline "an application's kill price IS its taint".  An application with
  `app_kill = True` and a constraining predicate cannot satisfy it — but such
  an application already cannot run the generic slot (its exec taint arm `T`
  would have to yield `app_sup`, and nothing else does), so the tree assumes
  the identity today; the law only states it.
- VERDICT: TAKE.  One credential, one name, and the survey's other verdicts
  get shorter statements for free.

### R2 (ALREADY RULED, in flight as OFF-HAND-7; the RESIDUE to delete is what this entry adds) — the held offset's coupling

- WHERE.  Kernel coupling: `FileInvDefs.fdstate_ok`'s FD_INODE arm pins `m =
  OffParked` (`:564`) and `FileOffCell.off_resident γo k := ∃ v, cell ∗ ⌜wf⌝ ∗
  off_gv γo ½ v` (`:106`) — the kernel half, with the user half either
  `OffGv.off_user_inv γo` (parked row; existential, nobody reads it) or
  `UserOff.uoff γo off` (held row) via `FdSlots.foff_row` (`:762`).  The
  generic-proof sites that conjured a precondition for it are the four refuted
  shapes (completed/app-file-design.md §7), and what is STILL IN THE TREE of them:
  `UsysMemOk.usys_fd_ok`'s open arm conjunct `fdst_parked (FdOpen rd wr t)`
  (`UsysMemOk.v` open row, "WHY IT BELONGS HERE … LICENSES A GENERIC OPEN TO
  INSTALL A HELD DESCRIPTOR"), `usys_fd_ok_parked` (`:791`),
  `FdSlots.fdv_all_parked` (`:252`), `FileInvDefs.file_ref_parked` /
  `file_ref_parked_keep` (`:1800-1825`), `foff_row_dup`'s `fdst_parked`
  premise (`FdSlots.v:785`) discharged at `ProofSysDup.v:1046` and
  `ProofKforkB3.v:782`, the dead `FdPark.uoff_surr{,s,s_map,_at}` /
  `uoff_rcpt` family (`FdPark.v:163-356`), `UkRun.ukn_held` (`:193`) with the
  class `ukn_parked` (`:213`), `urun_parked_row := True` (`:791`), the unused
  premises `ukn_held N = ∅` at `UkRunSys.v:1001/:1185` and `UkShEcho.v:538/
  :828`, `ukn_held N ⊆ hs` at `UkFork.v:817/:1181`, `UkSh.ush_gen_slot`'s
  `⌜ukn_held N = ∅⌝` conjunct and `ush_gen_slot_held` (`UkSh.v:6515/:6526`),
  and `Context {Hpark : !ukn_parked N}` at `UkInit.v:112`, `UkInitMain.v:115`
  (+ `UInitKernel:417`).
- WHY IT HURTS.  Lanes OFF-HAND-1..5 spent five rounds trying to carry "all
  rows parked" through the generic supply law, the Löb, the exec crossing and
  a record bit/set — each an instance of conjuring a precondition the generic
  tier cannot state (user-read.md §8.1's three findings; app-file.md §7).
  What remains costs: every open the kernel publishes is forced parked
  (`ProofSysOpenPub:324-330` cannot switch to `off_pub_hand_0`, OFF-HAND-6
  H5), so no held descriptor can exist and echo's append / cat's read cannot
  be stated; dup and fork read parkedness off the reference instead of
  deciding by the count; and 13 files still name `fdv_all_parked`.
- THE PATTERN APPLIED (the design of record, app-file.md §3 "THE OFFSET" and
  §3.5, restated as the pipe's three pieces so the lane has the exact
  shape): (i) COUPLING — `off_resident γo k := ∃ v, cell ∗ ⌜wf⌝ ∗ (off_gv γo ½
  v ∨ □ riscv_kill_cred)`; the taint arm is a dead ghost for THIS object,
  permanent (a `ghost_var` half cannot be re-minted at γo — the pipe's "no
  fresh authority at an existing name" holds verbatim).  `fdstate_ok`'s held
  arm drops `m = OffParked` and pins the count instead: `file_pay_st` gains
  `⌜¬ fdst_parked st -> q = 1⌝` in the coupled arm (OFF-HAND-6 finding 2),
  so the injectivity reading survives.  (ii) PAYMENT — read/write at a held
  row pay NOTHING extra (fact 4: the half rides the bundle and the kernel
  lends it to the fire through `FdPark.off_supply_of_st_at_eq`, `:530`, which
  returns the row ADVANCED); dup/fork of a row pay `⌜fdst_parked (source)⌝ ∨
  □ riscv_kill_cred` — the copy's `foff_row` entry at `OffHeld off` is then
  `uoff γo off ∨ □ riscv_kill_cred`, the taint filling the second row.
  (iii) POST — a fire through a tainted entry has a kernel half and no user
  half, so it spends the taint into (i)'s right arm and hands back `(row
  advanced) ∨ (taint ∗ row unmoved)` — `pipe_wpost`'s shape.  The one
  subtlety the in-flight lane must price: the three app-tier pieces that LEND
  the kernel half to the client (`FsAbsReadFire.aread_commit_at`,
  `FsAbsWriteFire.awrite_full_at`, `awrite_part_at`; `UexecSG.v:126-134`
  "the three pieces that lend the offset shadow") have nothing to lend on a
  disconnected object.  Either their lent conjunct becomes `off_gv γo ½ off ∨
  taint`, or — cheaper, and already half-built — the disconnect is pushed
  into the abstract supplier `UserOff.off_supply γo E off d R` that
  `arf_read_fire_gen` / `wrf_awrite_fire_gen` already take (OFF-HAND-6
  finding 1), so the pieces do not move.  Recommend the second.
- WHAT IT REMOVES.  Everything in WHERE after "STILL IN THE TREE": the open
  row's `fdst_parked` conjunct (the row keeps `fdst_nopipe`), `usys_fd_ok_
  parked`, `fdv_all_parked` and its list kit, `file_ref_parked{,_keep}`, the
  `fdst_parked` premise of `foff_row_dup` (dup/fork read the count or spend
  the taint), `FdPark.uoff_surr*`/`uoff_rcpt` (dead since OFF-HAND-6 H1),
  `ukn_held`/`ukn_parked`/`urun_parked_row`/`ush_gen_slot`'s row/
  `ush_gen_slot_held`, the four unused leaf premises, the three `Hpark`
  contexts, `SpecKexec.kexec_image_ok_parked`/`exec_key_ok_parked`,
  `ProcInv.proc_priv_parked`'s chain (consumer-less since OFF-HAND-5).
- WHAT IT COSTS.  The site list is OFF-HAND-6 finding 3 (the coupled H2+H3
  change): `usys_fd_ok` gains a read/write arm `sts' = <[fd := fdst_adv (sts
  !!! fd) d]> sts`, `usys_fd_ok_quiet` gains two premises at 20 occurrences
  (`UsysMemOk`, `UkRunSys`, `UexecApply`, `UkRunExecRef`), `SpecSyscall.
  sysc_fd_ok`/`SpecUsertrap.ut_fd_ecall` relay, `ProofSyscall`'s read/write
  arms prove, `SpecFileread`/`SpecFilewrite` posts return `foff_row (fdst_adv
  st d)`, `file_ref` retypes at the advanced state; plus (i)'s box and the
  supplier's taint arm.  Soundness: the taint is the RIGHT one
  (`riscv_kill_cred`): only a tainted process can dup/fork a held row, a
  verified holder's post is `advanced ∨ taint`, and its claim already reads
  `… ∨ taint`.  Re-coupling: never, by construction.  The vacuity check to
  write before the sweep: `off_resident`'s right arm must not be reachable
  from a PARKED row's fire (a parked fire has `off_user_inv`'s half and never
  needs the taint) — one four-line lemma, or the disconnect leaks into every
  generic read.
- VERDICT: ALREADY RULED (do not re-design); TAKE THE DELETIONS as the lane's
  exit criterion — the residue is the four refuted shapes still compiling.

### R3 (TAKE, but as an APPLICATION taint, and only if the owner keeps declining the capacity conjunct) — the write chain's partial arm

- WHERE.  `FsAbsWriteFire.awrite_chain` node `Q k ∧ (awrite_full_at ∧
  awrite_part_at)` (fs-syscall-specs.md §4 "sys_write is honestly
  NON-atomic"): the PARTIAL arm's delta is `delta_write i off bs` with only
  `take r bs` the caller's and `⌜length bs <= r + BSIZE⌝` — "up to one block
  of bytes nobody names lands in f" (F-WRITE finding 3).  The application
  site that must pay it: `AppFile.f_bytes_typed` admits only whole-chunk
  subsequences, so `FileWrite.file_awrite_node`'s partial arm "cannot be paid
  at all", and `TreeMove.tree_awrite_chain` proves both arms only because the
  tree claim is looser.
- WHY IT HURTS.  The arm is the KERNEL's choice at every node (`∧`), so the
  application cannot refute it without a capacity conjunct that app-file.md
  §0 explicitly declines; F-WRITE's ruling (a)/(b) is still open and
  `UEchoFile`'s post is blocked on it.  This is not the generic tier's
  problem (`fsabs_awrite_chain` pays both arms from `app_sup`,
  `FsAbsInvFire.v:249`); it is the verified program facing an arm that is
  reachable (disk full) and unrefutable.
- THE PATTERN APPLIED.  Not `riscv_kill_cred` — a short write is legitimate
  kernel behaviour, not a discipline break, and the kernel cannot mint the
  console taint.  An APPLICATION-LEVEL disconnect instead: `AppFile.f_state`
  gains a third arm `f_short r := mono_nat_lb_own (fn_short r) 1`
  (persistent, timeless, the counter's authority kept inside the claim beside
  the escrow ledger, `AppFile.v:597-619`), `file_pred := taint ∨ (pure ∗
  cons_state ∗ (f_state ∨ f_short))`; the partial arm is paid by a
  `file_app_step_short` that bumps the counter under the claim (the step
  lends the claim, so the mint is in mask); posts and `file_phi` read `exact
  ∨ short`; `file_claim_read` reads the authority at 0 to conclude "no short
  write ever happened" on the runs that matter.  This is F-WRITE's way (b)
  in taint form, with no change to `FileDisc.ralt`/`fsm` — the disconnect
  replaces the "bounded junk tail" model.
- WHAT IT REMOVES.  The open ruling; the need for a capacity conjunct or a
  junk-tail model; `file_awrite_node`'s unpayable arm (the chain closes under
  `awrite_chain`'s induction "in a dozen lines", F-WRITE).  RELAYs 2 and 3
  (offset anchor, chunk length) are NOT touched: they are precision on the
  full arm and the held row (R2) supplies RELAY 1/2; RELAY 3 stays a kernel
  contract fact (`awrite_full_at` should carry `⌜length bs = min FW_MAX
  (n - k·FW_MAX)⌝`, which the fire knows).
- WHAT IT COSTS.  `AppFile.v` (~6 lemmas: the arm, the step, the reads, the
  supply-of-taint twins), `FileWrite.v`'s node, `file_phi`'s conclusion and
  its adequacy reading, the durable statement of milestone 2 (`… ∨ short`).
  Soundness: the token is minted only by the application's own step at the
  partial arm, so it is not the self-taint trap of Fact B — the application
  is not choosing to give up on an arm it could have refuted; it is recording
  an event the kernel really performed.  Re-coupling: never (a `mono_nat_lb`
  at 1 is permanent), which is honest — the junk tail is on disk.
- VERDICT: TAKE if (b) stays the ruling; NOT if the owner would rather take
  the capacity conjunct (then there is nothing to taint).

### R4 (TAKE, small) — close's deposit at an `open()`ed descriptor: export what the row already says

- WHERE.  `UsysMemOk.usys_fd_ok`'s open row carries `fdst_nopipe (FdOpen rd
  wr t)` (open arm, last conjunct).  `UkRunSys.wp_uk_ecall_open` (`:834`)'s fd
  arm exports only `∃ fd rd wr t, … ualloc … (FdOpen rd wr t)` — the nopipe
  fact is dropped at the leaf.  `UkRun.udepw_cl` (`:628`) is `⌜nonpipe⌝ ∨
  udepw N m pc 21`, and its comment still says "a descriptor open returned
  carries an existential type: usys_fd_ok's open row does not pin it" —
  stale since the pipe landing.  Consequence: `UkCat.kcat_deps` (`UkCat.v:119`)
  demands `udepw_law 21` and `kcat_cldep_of_law` (`:266`), threaded through
  `UkCatMain.v:355/:399/:415`, and CAT-ENTRY finds that the only producer of
  `udepw_law 21` at a claim-bearing instance is the taint
  (`UexecExecMint.udepw_law_of_sup_close`, `:329`) — so cat's close forces a
  TAINTED entry.
- WHY IT HURTS.  A verified program closing a descriptor it opened cannot take
  `udepw_cl`'s free arm although the kernel proved the fact; it pays with a
  law only the taint supplies.  This is exactly "conjuring a precondition"
  one syscall late.
- THE PATTERN APPLIED.  No new taint arm: the disjunction exists
  (`udepw_cl`), the generic tier pays its right arm from the taint already,
  and what is missing is the LEFT arm's evidence at the leaf.  `wp_uk_ecall_
  open`'s fd arm (and `_recv`, `_recv_img/_gimg/_dimg`) export `⌜fdst_nopipe
  (FdOpen rd wr t)⌝` beside the handle; `UserFd.ufd` holders then take
  `udepw_cl_nonpipe`.
- WHAT IT REMOVES.  `udepw_law 21` from `kcat_deps`, `kcat_cldep_of_law`, the
  three `UkCatMain` signatures; the stale paragraph on `udepw_cl`; one of the
  two reasons CAT-ENTRY's C2/C3 stopped.  (The `fdst_parked` conjunct on the
  same row goes with R2.)
- WHAT IT COSTS.  Five open-leaf statements gain a pure conjunct;
  `ProofSyscall`'s arm 15 already proves it.  No soundness question.
- VERDICT: TAKE, alongside R2's row edit (one touch of the open row).

### R5 (NOT THE RIGHT TOOL) — sys_open's create/lookup/truncate pieces, permits, refunds and kept receipts

- WHERE.  `SysOpenDefs.open_au_create_at` (`:906`): six `∗`-separated pieces
  `pf_at acre_commit_at Fok ∗ pf_at dlookup_commit_at Fex ∗ pf_at
  aopen_commit_at Fo ∗ open_trunc_piece (trunc_permit_of …) Ft ∗
  cre_child_unfired Farm Fun`; `trunc_permit_of` (`:548`) is `∃ d nm, T d nm ∗
  (cre_acre_fired Fok … ∨ (cre_ex_fired Fex … ∗ pf_at aarm_commit_at Farm))`;
  `cre_ft_kept` (`:728`) keeps the permit on the refund side;
  `open_post_fail_create` (`SpecSysOpen.v:817`) is a three-way fold with arm
  (a) "create fired, fdalloc failed"; `open_post_ok_create` (`:737`) has the
  EXISTS-DEVICE sub-arm.  The generic proof site: `FsAbsInvFire.fsabs_open_in`
  (`:431`) — every piece at `pfam_triv`, every permit unread
  (`open_trunc_piece_of_all`, `atrunc_of_permit_of_all`), all paid from
  `app_sup`.
- WHY IT HURTS.  It does not hurt the generic tier at all: the pieces are
  `AU ∧ R` records, the trivial family is `pfam_triv`, and `fsabs_open_in` is
  one line per piece.  What cost F-OPEN-2..5 five lanes is the VERIFIED
  program's precision — refuting the exists arm at an absent deed (P3), the
  device sub-arm (S3), and getting the deed home on arm (a) — and Fact B says
  a taint cannot buy any of that: a verified program does not hold the taint,
  and the refutations are about the POST (which arm the kernel reports), not
  about what the program has to PAY.  Paying `Fex`'s piece is free
  (`pfam_triv`); the trouble is that the post's exists arm is a run the deed
  says is impossible and the contract does not say so.
- THE PATTERN APPLIED.  A `fired ∨ taint` post would let only a TAINTED
  caller drop the arm — which the generic caller already does by ignoring
  posts.  The honest fix for P3/S3 is ARM EXCLUSIVITY in the kernel contract,
  named twice by the lanes and never taken: F-OPEN-2's restatement 3 /
  F-OPEN-5's (i) — `FsAbsCreateFire.acre_commit_at_gen` takes the UNFIRED
  `Fex` piece beside the arm's receipt (create's `dirlookup` either finds the
  name and fires `Fex`, or does not and fires the arm; today both receipts
  are reachable in the statement), or F-OPEN-5's (ii) — `open_post_ok_create`
  saying which branch of the permit it paid.  That is a contract-precision
  change on create/mknod/unlink/open, orthogonal to taint.
- WHAT IT REMOVES (if exclusivity is taken).  `FileOpen`'s
  `file_dev_refute`, the `∨ fown r s` disjunct's last residue, half of the
  F-OPEN-5 escrow's reason to exist (the `s = None` reading would come free
  from exclusivity rather than from a ledger of spent tokens).
- WHAT IT COSTS.  Kernel-tier: the four AU surfaces that carry `Fex`; the
  `ProofSysOpen*` arm builders.  The escrow ledger (`esc_auth`/`esc_recs`/
  `esc_wit`, `AppFile.v:340-444`) stays for the VIEW problem (the truncate
  fires at a later view than the lookup), which is not exclusivity's either.
- VERDICT: NOT WORTH IT AS A TAINT CHANGE — wrong tool.  Record instead that
  restatement 3 (arm exclusivity) is the open item, so nobody re-proposes a
  taint here.

### R6 (ALREADY DONE) — `urun_nopipe`, close(21), exit(2) and `fileclose_cpays`

- WHERE.  `UkRun.urun_nopipe fdv := ⌜fdv_nopipe fdv⌝ ∨ □ riscv_kill_cred`
  (`:695`) — the pattern verbatim; `udep`'s four laws (`:407`): key-free,
  close key-guarded (`ukey_nonpipe`), exit table-guarded (`ukey_table_
  nopipe`), and exit FROM THE TAINT at any table; `xv6_sbundle_exit_taint`
  (`UexecExecInst.v:1291`), `fileclose_cpays_taint` (`SpecFileclose.v:456`),
  `SchedCtx.kill_row`'s paid arm `kill_owed ∗ □ riscv_kill_cred` (`:277`),
  `SpecKexit` at `fileclose_cpays sts` (`:302`).
- WHY THE RECORD MUST STATE "NO PIPE".  Not a conjured precondition: a
  verified program that never called `pipe(2)` holds no fragment and no
  taint, so the only way it can mint `fileclose_cpays` for its table is to
  know the table has no pipe row; `fdst_nopipe` on the open row and
  `usys_fd_ok_nopipe` (`UsysMemOk.v:935`) carry it for free and
  `urun_nopipe_step` re-establishes it at every leaf.  The pipe-holding
  program's price (links from an application registry, one per pipe) is
  pipe.md's own open item and is application-level.
- VERDICT: ALREADY DONE.  R4 removes the one stale consumer (`udepw_law 21`
  demanded where the left arm was available).

### R7 (ALREADY DONE) — fork / exec / wait / exit's child-token coupling

- WHERE.  `ChildTok.my_pay`/`child_tok`/`kill_shot` (`:288/:339/:567`);
  `UkFork.wp_uk_ecall_fork` takes `□ (riscv_kill_cred -∗ Q (-1))` (`:817`
  block) — the `-1` arm paid by the taint; `kill_row`'s paid arm (R6);
  `UexecRet.uexec_wait_F` (`:1186` block) is the pure row `uwait_ans_pid_m`;
  `SpecKexec.exec_slot_pre`'s two wands carry no descriptor fact at all
  (OFF-HAND-5 D1); `PinnedExec.pinned_exec_bundle_at`'s pin law `□ (∀ v,
  app_pred v -∗ app_pred v ∗ (⌜Pin v⌝ ∨ T))` (`:349`) and `ExecEntry.
  image_entry_taint T Q X := □ ∀ W', T -∗ my_pay … -∗ X W'` (`:170`).
- VERDICT: ALREADY DONE.  The only residue is R2's dead carrier
  (`ukn_held ⊆ hs` on the fork leaf, `ush_gen_slot`'s row).

### R8 (ALREADY DONE; R1 finishes it) — the console

- WHERE.  `ConsoleInv.cons_acc cn Wd Rd := (∃ n, cons_reader cn n ∗ …) ∨
  (cons_dirty_cred Wd ∗ ∀ cur dc, |==> Rd cur dc)` (`:2069`) with
  `cons_dirty_cred Wd := □ Wd` (`:1812`) at `Wd := app_sup` — the mould
  user-read.md §8.1 names; `WpUart.cons_licence` (`:2041`) is a persistent
  LAW over `riscv_cons_res`, false at a real console claim (`UShLine.v:25`)
  and derivable from the taint (`UInitBoot:821`).
- WHAT IS LEFT.  Only R1: the licence is the third name for the taint and
  should be derived, not threaded.  CAT-ENTRY's "independently FALSE"
  finding is a symptom of the same thing — cat's walk was landed at the free
  laws instead of at a per-call chain, which is a walk-shape defect, not a
  coupling gap.
- VERDICT: ALREADY DONE.

### R9 (NOTHING TO DO) — cwd, sbrk, chdir, mknod/unlink/link/mkdir

- WHERE.  `UserCwd.ucwd_auth`/`ucwd` are two halves of one `ghost_var`
  INSIDE `urun` (`UserCwd.v:40-45`; `UkRun.urun` binds `cw`), `UserHeap.usz`
  likewise (`:634`); the kernel posts are pure (`UsysMemOk.usys_cwd_ok`
  `:979`, `SpecSysSbrk.sys_sbrk_ok` `:116`); the generic chdir row is a
  closed fact (`fsabs_chdir_pre`, no supply); mknod/unlink/link/mkdir are
  `pf_at … pfam_triv` pieces paid from `app_sup` (`fsabs_mknod_pre`,
  `fsabs_unlink_pre`, `fsabs_link_pre`, `SpecSysMkdir.mkdir_au_at_unit`).
- WHY NOTHING.  There is no kernel-invariant coupling of user-facing ghost to
  physical state here: the U-tier halves are the program's own bookkeeping
  keyed to its own run, invisible to the generic tier (which has no `urun`).
  The fs pieces are already Fact-A-free.
- VERDICT: NOTHING TO DO.

### R10 (PART OF R2) — `fdstate_ok`'s injectivity and reference-count facts

- WHERE.  `FileInvDefs.fdstate_ok_inj` (three readers: `FileInvDefs`,
  `ProofSysOpenPub`, `ProofSysOpenParts`); `file_pay_st_agree` / `_split`;
  design/file-table.md "The core: a per-slot reference-count auth".
- THE PATTERN APPLIED.  As OFF-HAND-6 finding 2 rules and app-file.md §3
  records: the COUPLED arm pins `⌜¬ fdst_parked st -> q = 1⌝` (a held object
  has one row), injectivity closes at the parked form; the TAINT arm (a
  dup/fork that spent the taint) is where a held row may have two shares,
  and there `fdstate_ok`'s held arm says nothing (the object's box is
  disconnected).  No separate change.
- VERDICT: ALREADY RULED (R2).

### R11 (NOTHING TO DO; one optional cleanup) — `UexecRet`'s Löb

- WHERE.  `uexec_ret_cont_gen` (`:1504`) hands the successor's pure rows
  (`usys_mem_ok`, `usys_fd_ok`, `usys_cwd_ok`, `usys_ch_ok`, `uvis_pid`,
  `usys_lazy_keep`, `uexec_live_ok` `:1450`) TO the process; `uslot_of_creds`
  is a slot at EVERY key and carries no invariant of its own across rounds.
  The one thing it ever had to carry was `fdv_all_parked` (user-read.md
  §8.1 finding 3), and R2 deletes it.
- OPTIONAL.  `sbundle_of_supply_ne` / `udep`'s laws / `xv6_sbundle_free` are
  `==∗`-shaped for a trace seed that no longer exists (`UexecSG.v:80`
  "used to carry"; `UexecExecMint.v:243` "every arm of its proof is
  `iModIntro`").  Dropping the modality removes an `iMod` at every leaf; not
  a taint change, and the header argues for keeping it for future
  allocations.  Leave unless a lane is already in those files.
- VERDICT: NOTHING TO DO.

## 2. Couplings surveyed and found already on the pattern (so nobody re-audits them)

| coupling | kernel site | taint arm | generic payer |
|---|---|---|---|
| pipe byte queue | `PipeInvDefs.pipe_qres` | `pipe_taint_cred` | `fsabs_fileread_in`/`fsabs_filewrite_in`/`fileclose_cpay(s)_taint` |
| console ring reader | `ConsoleInv.cons_acc` | `cons_dirty_cred app_sup` | `cons_acc_cred` |
| console output claim | `WpUart.cons_licence` | the licence IS the taint's law | `cons_out_chain_of_licence` |
| fs abstract view | `AppInv.app_body` (half the map authority) | `app_pred := taint ∨ exact` (echo, file) | `app_sup` (= taint, Fact B) |
| kill flag | `SchedCtx.kill_row` | `kill_owed ∗ □ riscv_kill_cred` | usertrap via `kill_paid_shot_tear` |
| fork's `-1` / child payload | `UkFork.wp_uk_ecall_fork`, `sfork_pay` | `□ (riscv_kill_cred -∗ Q (-1))` | trivial payload |
| exec image | `PinnedExec` pin law, `image_entry_taint` | `⌜Pin v⌝ ∨ T` | generic slot from `T` |
| exit's table closes | `UkRun.urun_nopipe` | `⌜nopipe⌝ ∨ □ riscv_kill_cred` | `xv6_sbundle_exit_taint` |
| input tag | `riscv_rx_tag` | echo's `pristine ∨ taint` | — |
| file offset box | `FileOffCell.off_resident` | NONE YET (R2, in flight) | parked: `off_user_inv`; held: R2 |

## 3. The three changes I would make first

1. **R1 — make the taint the ONE generic credential.**  Add `al_sup_of_kill`
   to `App.xv6_app_laws`, set `xv6_ssupply := □ riscv_kill_cred`, derive
   `app_sup` and `cons_licence` inside `xv6_sbundle_of_supply_ne`/`udep_gen`.
   Removes the duplicated `□ riscv_kill_cred` beside `□ ssupply` on every
   generic-tier lemma (`uslot_of_creds`, `uexec_wp_uslot*`,
   `uexec_dep_F_of_supply`, `cond_entry_slot`, `uslot_mint*`), the
   `app_sup`/`cons_licence` arguments on `udep_gen`, `filewrite_in_of_sup`,
   `udepw_*_of_sup_*`, `fsabs_fileread_in`, `fsabs_filewrite_in`, the
   `SystemAdequacy:1045` premise and the `UInitBoot:821` hand proof.  ~20
   statements, no program walk touched, and every later taint arm is stated
   at one name.
2. **R2's deletions, as OFF-HAND-7's exit criterion.**  When the held row's
   coupling lands (`off_resident`'s `∨ □ riscv_kill_cred`, the count pin in
   `file_pay_st`, dup/fork's `⌜parked⌝ ∨ taint`, the read/write row), delete
   in the same lane: the open row's `fdst_parked` conjunct, `usys_fd_ok_
   parked`, `fdv_all_parked`, `file_ref_parked{,_keep}`, `foff_row_dup`'s
   premise, `FdPark.uoff_surr*`/`uoff_rcpt`, `ukn_held`/`ukn_parked`/
   `urun_parked_row`/`ush_gen_slot`'s row, the four unused leaf premises,
   the three `Hpark` contexts, `kexec_image_ok_parked`/`exec_key_ok_parked`,
   `proc_priv_parked`'s chain.  That is the four refuted shapes finally
   leaving the tree; and push the disconnect into `UserOff.off_supply` so
   the three lending pieces do not move.
3. **R4 — export `fdst_nopipe` from the open leaves.**  One pure conjunct on
   `wp_uk_ecall_open{,_recv,_recv_img,_recv_gimg,_recv_dimg}`'s fd arm (the
   kernel row already proves it), then `udepw_cl_nonpipe` at every close of
   an opened descriptor.  Removes `udepw_law 21` from `UkCat.kcat_deps`,
   `kcat_cldep_of_law` and the three `UkCatMain` signatures — the one
   premise that forced cat's entry to be tainted — and the stale comment on
   `udepw_cl`.

And two things NOT to do, so they are not proposed again: no taint on
`sys_open`'s create/lookup/truncate pieces (R5 — the residues P3/S3 are arm
exclusivity, `acre_commit_at_gen` taking the unfired `Fex`), and no
`riscv_kill_cred` on the write chain's partial arm (R3 — if anything, an
application-level `f_short`, minted by the application's own step).
