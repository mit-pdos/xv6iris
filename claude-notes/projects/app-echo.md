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

#### THE ARM, concretely (design 2026-09-08, after the folds; the ARM lane's brief is cut from this)

Landed mechanism to generalise: the exec GIVE.  `UexecRetExec.uexecXG` is
an ambient class with `xbundle : (uvis -d> iPropO Σ) -> uvis -> iProp Σ`
(the payload at the RECURSIVE OCCURRENCE, so the slot wand inside it
concludes at the fixpoint) plus `xbundle_ne`/`xbundle_cong`;
`uexec_ret_x_F` splits `USYS_exec` off the returning arm and demands
`xbundle X W` beside it; `UexecExecInst.v` instantiates the class at
`SpecSysExecAU.sys_exec_au_pre` (the families existential in the arm,
re-bound by the dispatch); `SpecSyscall`'s dispatcher contract TAKES
`xbundle uslot_x (uvis_of U sts)` from the trap loop; the x-tier loop
(`UexecApplyX`) holds `∀ W'', uslot_x W''` — the generic slot as a
persistent SUPPLY over every key.  The return former's cone has no fs
class (`fileG`/`appcfg` do not occur in UexecRet/UexecSlot/UexecWp).

The ARM lane = that mechanism at EVERY fs syscall, in the DEPOSIT shape:

1. **One class, `uexecSG Σ`**, replacing `uexecXG`: `sbundle X n W` (the
   process's bundle for syscall number `n` at trapping key `W`; `emp`
   for numbers without a contract), `spost X n W r` (what comes BACK
   under the arm's `∀ r`: the syscall's armed post — unfired pieces as
   `AU ∧ R`, receipts, cursors; `emp` for exec, whose bundle is consumed
   and whose process never resumes on success), `sbundle_ne`,
   `sbundle_cong` (the bundle reads only the image, the arguments, the
   descriptor view and the cwd off its key), and the SUPPLY LAW
   `ssupply : iProp Σ` (persistent, opaque here) with
   `sbundle_of_supply : □ ssupply -∗ ∀ X n W, sbundle X n W`.  Instance
   (above the fs tower, `UexecExecInst.v` grown or a sibling):
   `sbundle X n W := match n with 15 => open_in …; 17 => mknod_au_pre …;
   16 => the write chain at the trivial…` — NO: at the process's OWN
   families, existential in the arm exactly as exec's are; `spost` the
   matching `*_arms`; `ssupply := □ ∀ av, app_pred app_run av` (the
   predicate is trivially true — `app_triv` by definition, echo from the
   taint), and `sbundle_of_supply` is today's `fsabs_*_in`/`fsabs_*_pre`
   dischargers with the license read replaced by the supply (each write-
   kind `app_step` is `iLeft`/trivial under it).
2. **The arm** (`UexecRet.uexec_ret_F`, absorbing `UexecRetExec` and
   `UexecRetFs`, as both headers promise): the returning-syscall arm
   becomes `sbundle X n W ∗ (∀ r M' π' szv' fdv' cw', <the four pure
   rows> -∗ spost X n W r -∗ X (bump …))`; exec's arm keeps its give
   (`spost` = `emp`); the fd-row MIRROR (`mcur`) is a second component
   of the same payload when the pilot's P4 lands, not a second arm.
3. **The generic inhabitants** `uexec_wp_uslot`/`cond_entry_slot` take
   `□ ssupply` and mint `sbundle` per call from it; `UEXEC_GEN` carries
   `ssupply`'s discharge for the theorem's instantiation (`app_triv`:
   trivial).  The x-tier's `∀ W'', uslot_x W''` supply becomes the one
   tier.  Every verified program's ecall leaf (`UkStep`/`UkRunSys*`/
   `UkFork`/`UkInit*`/`UkSh*`/`UkEcho`) deposits its bundle at its own
   families and receives `spost`; today's leaves take the plain arm, so
   the conservativity direction is `UexecRetExec`'s (the enrichment
   DEMANDS a resource): each leaf gains the deposit as a premise, and a
   program that owns nothing about the fs passes the supply-minted bundle.
4. **The dispatcher** (`ProofSyscall`) takes `sbundle uslot n (uvis_of U
   sts)` for each fs arm — exec's mold at SpecSyscall.v:331 — and hands
   `spost` back; the `fsabs_*` dischargers are then only the supply law's
   proof.  `app_inv` keeps the half authority and the claim; `app_auto`,
   `app_auto_raw`, `app_step_of_auto`, `app_step_acc(_view)`, the mint's
   license premise (`FsCfgSnap`, `BootShared`), the movers' `▷ app_auto`
   binder (`InodeRegion.ireg_top_retag_gen` and twin) and `Happ_auto`
   (`App`, `SystemAdequacy`) are deleted.
5. **Staging.**  ARM-a: the class, the arm fold, the generic inhabitants,
   the Uk leaves (kernel untouched; ripple = the 54 slot/return-channel
   files).  ARM-b: the dispatcher, the supply law's instance, the
   deletions, the two statement changes (`Happ_auto` leaves the theorems;
   `UEXEC_GEN` gains the supply).  ARM-c: echo's `ssupply` from the taint
   and `echo_pred := taint ∨ pins` (Q4).

**Corrections from ARM's phase-0 inventory (2026-09-08), ruled in:**
(i) the supply law takes the slot family — `□ ssupply -∗ □ (∀ W', X W')
-∗ ∀ n W, sbundle X n W` — because exec's bundle carries the slot wand at
the recursive occurrence; (ii) `sbundle_mono` is a class field (the fd
mirror's tier `uslot_fs` stays alive for P4 and injects through it);
(iii) `ssupply` is opaque in the class — `appcfg` is not in the return
former's cone; (iv) STAGING: `spost` is in the class from ARM-a at `emp`
for every number and the tier fold (`uslot_x` → `uslot`, the kernel-side
renames in SpecSyscall/SpecUsertrap/SpecUservec/ProofUsertrap*/
ProofUservec/ProofSyscall/ProofUserretClosed) is ARM-a's, so the 51-file
ripple lands once; ARM-b changes the class INSTANCE (real `sbundle`/
`spost` at the process's families for read 5, exec 7, chdir 9, open 15,
write 16, mknod 17, unlink 18, link 19, mkdir 20; sync 22 is free), the
dispatcher's arms, `uexec_ret_round_slot`'s `spost` premise, and the
license deletions (19 files / 122 hits; `app_step_acc` mostly in
`FsAbsCreateFire`, not `FsAbsInvFire`; `app_auto` is a structural
conjunct of `app_body`); (v) `UEXEC_GEN` splits: it gains `ssupply_gen :
⊢ □ ssupply` and its inhabitant becomes a functor over the application's
supply (`True` at `app_triv`) — `Happ_auto`'s REPLACEMENT; (vi) the park
does NOT bite: `park_token_F`'s fixpoint is over the token, `uslot`
enters it as a constant of type `uvis → iProp`, and `UexecRetFs` already
proved a linear deposit-and-return in the arm is contractiveness-neutral
— fd-row-pilot §6 item 3's obstruction was `uslot_fs`'s `gname` INDEX,
which the class routes around; the one real cost is the `uexecSG` binder
on every park consumer resolving the same instance (the "two instances
printing identically" hazard); (vii) two key gaps, both fixable without a
shape change: write's `⌜fwn_wp fn ma = consolewrite⌝` moves from the
input into FILEWRITE/SYSWRITE's premise list; read/write get
`sys_fd_st_of_key` from `ProcInv.ofile_slot`; (viii) the generic
inhabitants AND sync's/echo's gate branches take `□ ssupply` (both
programs write(2)); (ix) today's x-tier supply `∀ W'', uslot_x W''` is
minted from nothing but the generic family (`fsabs_exec_pre`'s
`fsabs_env` premise is dead), which is why the real supply must be the
application predicate's.

**The deposit's CARRIER (ruled 2026-09-08, refined once).**  The program
proofs sit BELOW the fs vocabulary, so a leaf cannot pay `sbundle uslot n
W` directly.  Refuted: (1) `□ ssupply` as a conjunct of the kernel's
bundle `uvb` — the kernel would owe the supply to resume ANY process,
unsatisfiable pre-taint for echo: the GAP-premise trap in the trap loop;
(2) `□ ssupply` inside `urun` — the same trap one level down; (3) the
deposit as an explicit premise of every ecall leaf — ~1000 edits across
370 program lemmas; (3′) a free key predicate `Sok n W` in `urun` — the
leaf cannot discharge it, because the key is bound one layer in by
`urun`'s existentials.  RULED: a small ambient class `uprogSG Σ` with
`Dsup : iProp Σ` (the program's SUPPLIER, used as `□ Dsup`) and `psok :
Z -> Prop` (the NUMBERS it admits); `urun` gains `□ Dsup` and the pure
minting law over its OWN bound variables, quantified over the registers
and pc so `urun_close` re-establishes it:
`⌜∀ n m' pc', psok n -> n <> USYS_exec -> ⊢ □ Dsup -∗ sbundle uslot n
(uvis_of_run m' pc' M pm sz fdv cw)⌝`.  The key-dependence a program's
bundles have (echo's "fd 1 is the console") is a fact about the bound
`fdv`/`M`, provable where the constructor proves this conjunct; the
honest consequence of the register quantification is that a program
holding a FILE descriptor pays the write chain for every fd/count its
`psok` admits.  The leaf takes `⌜psok n⌝` as a pure premise; each program
file binds its `psok <literal>` facts as section variables, discharged in
its kernel-side constructor (no program lemma statement moves).
Instances: the generic slot and every ARM-a/b program at `Dsup :=
ssupply`, `psok := λ _, True`; echo's programs (ARM-c) at `Dsup := emp`,
`psok` := the numbers they call.  Exec's leaf keeps the explicit-premise
shape (its bundle carries the slot wand).

**The law is KEY-FREE, and the criterion is "payable at every key from
the supplier alone" (ruled 2026-09-08, forced by the compiler).**  `urun`
is re-established after every instruction and the program's own execution
moves every component of the key (a store moves `M`, sbrk moves `pm`/`sz`,
open/dup/close/pipe move `fdv`, every returning ecall moves `cw`), so a
law inside `urun` indexed by the key must be closed under all five — i.e.
it is the key-free law: `udep := □ Dsup ∗ ⌜∀ n W, psok n -> n <>
USYS_exec -> ⊢ □ Dsup -∗ sbundle uslot n W⌝`.  Consequences: (a) a
number is in a program's `psok` iff its bundle is payable at EVERY key
from `□ Dsup` alone; for a constraining program that excludes any
syscall whose bundle is keyed on the descriptor view or reads the image
(write is keyed on `sys_fd_st`; exec and mknod read paths out of the
image), which take the EXPLICIT route: the leaf's premise is the weaker
`psok n ∨ sbundle uslot n W`, and the program produces the deposit from
a section-variable law with a key premise discharged from its own
ledger, proved in its kernel-side constructor; (b) for the GENERIC slot
(`Dsup := ssupply`) every contract's bundle must be payable at every key
from the supplier — which exposes a PIECE-SHAPE DEFECT for ARM-b: read's
`aread_commit_at` and the write chain's nodes lend the offset shadow's
kernel half at `off` and demand it back MOVED (`off + d` / `off + |bs|`);
today's dischargers pay that with the per-row `off_user_inv γo`, which no
process holds at an arbitrary key.  RULE: a piece may not ask the client
to return a kernel-owned ghost moved; the client returns the shadow
unmoved and observes, and the kernel's fire lemma moves it from the row
invariant it holds.  ARM-b re-shapes those two pieces (and any other with
the same dependence) before turning the real bundles on.

**Two more ARM-a rulings (2026-09-08).**  (a) The leaf's premise is a
WAND off the two authorities the leaf holds, not a bare premise (the key
is bound by `urun`'s existential): `udepw … m pc n := ∀ M pm sz fdv cw,
uheap … -∗ ufd_auth … -∗ uheap … ∗ ufd_auth … ∗ (⌜psok n ∧ n <> USYS_exec⌝
∨ sbundle uslot n (uvis_of_run m pc M pm sz fdv cw))`; the left disjunct
carries `n <> USYS_exec`, so one minting lemma serves every number and
exec is the ordinary leaf whose disjunct is always the right one.  (b)
`psok`'s discharge travels beside `udep`: the gate slots and
`cond_entry_slot` take `⌜∀ k, k <> USYS_exec -> psok k⌝` with `□ Dsup`,
and the mint sites, which see the instance, discharge both.  The law
stays PER-NUMBER (refuted: folding `psok` out of the law into the leaf
gate — then the law is `∀ n`, and a program with `Dsup := emp`, echo
pre-taint, could not instantiate it at all).  Program files carry the
hypothesis `Hpsok` as a section variable; their kernel-side constructors
discharge it.

**Three more ARM-a rulings (2026-09-08, milestone A).**  (a) Exec's
deposit is supplied EXPLICITLY: `uxsup := □ ∀ W, sbundle uslot USYS_exec
W`, threaded from the kernel-side constructors down to the exec leaves
(sh's `runcmd` chain, init's exec arm) and never placed in `urun` (the
GAP-premise trap one number over); this is the explicit route, stopping
where the sh kernel file's exec-bundle premise stops today.  (b) The fd-
mirror tier (`uexec_ret_fs_F`) carries the deposit at the recursive `X`
through `sbundle_mono` and the post at the plain family; `urun_fs` gains
`udep`; its three ecall leaves take `psok n` as a pure premise.  (c) The
trap contract has TWO readers per returning ecall: exec's three-disjunct
out-shape stays exec's own (its `spost` is `emp`; the new-image slot and
the a0 gap are exec-specific), and the per-number `ut_sys_in n` /
`ut_sys_out n` carry `sbundle uslot n (uvis_of U sts)` in and `spost
uslot n (uvis_of U sts) r` out for every other syscall; the loop picks by
number.  Sweep hazard recorded: a section `Hypothesis` lands after the
USED explicit section variables and a same-section caller takes no
argument — position it by a closure check, not by a fixed offset.

**ARM-a, steps 2–3 (2026-09-08): as landed, and the park blocker.**  The
four transitional files are deleted and the tier is one (`uslot`); the
class instance grew `UexecExecInst.v` (above `FsAbsInvFire`, since the
supply law's exec case is `fsabs_exec_half`) with `ssupply := True` for
ARM-a — the landed mint's `fsabs_env` premise was dead, so the
`UEXEC_GEN` split is ARM-b's, where the supply becomes the application
predicate; no `Context SG` above the instance (a section variable there
is a second class of the same type: `ProofSysFork` HUNG on it, a stable
multi-GB RSS for an hour — the "two instances printing identically"
hazard); `ut_sys_in n` replaces `ut_exec_in` through the round,
`ut_sys_out n` is defined but threaded by ARM-b (nothing to carry while
`spost` is `emp`).  THE BLOCKER: `park_token`'s fixpoint reads `uslot`,
so it is class-indexed, and the instance was `CurCtx`-indexed (the exec
bundle's definitions carry `{XI : CurCtx}`), so `UtResFits`'s park lemma
resolved the instance at its own `XI` in the statement and at the
resumer's `Xc` in the proof — identical print, not convertible.  RULED:
the deposit instance must be CurCtx-FREE — a process's deposit cannot
depend on the hart context of the kernel proof consuming it; the `{XI :
CurCtx}` binders on the exec chain's definitions are the TSO rebase's
mechanical appends and are removed where the bodies never use the
context (fallback only if a body genuinely does: the slot family as an
explicit index of `park_pkg`/`park_token`).

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
  SHAPE RULED 2026-09-08 (R-CONJ phase 0): receipt and refund travel as
  ONE generic per-piece record `pfam Σ A := { pf_recv : A ; pf_refund :
  iProp Σ }` (one field per piece in every bundle and arm, 1:1 with the
  pieces, arities unchanged; cursors `P`/`Pmiss`/the write chain's `Q`
  stay bare — the TYPE says which families are one-shot pieces); the `∧`
  sits at the ASSEMBLY (`piece … F.(pf_recv) ∧ F.(pf_refund)` in the
  bundle and in every unfired-return arm; piece definitions untouched;
  fire lemmas eliminate in one line; dischargers at the named trivial
  pair).  Read's landed flat `Φ, R` converts to the record in the same
  pass.
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

- ~~**MKNOD-UNIFY**~~ LANDED 2026-09-08 (Opus lane, two phases; net about
  740 lines removed).  sys_mknod has ONE contract in `SpecSysMknod.v`:
  the frame, `mknod_au_pre` (walk ∗ create commit ∗ exists observation ∗
  the child's two legs), `mknod_arms`, the blanket as the derived
  `mknod_arms_ret`, `SYSMKNOD`.  `ProofSysMknod.v` seals it against six
  callees (the dead plain `Create` argument is off) and derives the stable
  form as the lemma `wp_sys_mknod_stable_of`; `LinkSysMknod.v` links it.
  Gone: the era/stable parallel forms and their links, the plain frame
  (no consumer), the astate-shaped commits and their three prose-only
  bridges.  `SpecSysMknodAU.v` is a 135-line pure leaf.

- ~~**PATH-UNIFY**~~ LANDED 2026-09-08 (Opus lane, one syscall at a time):
  ~~OPEN~~ LANDED — one `SYSOPEN`/`wp_sys_open` keyed on `om_create vom`
  (`open_in`/`open_arms` are an `if` over the two landed arm families);
  the blanket `sys_open_post` is DERIVED (`open_arms_landed`) because it
  carries resources; the two arm bodies stay as unsealed definitions with
  one proof each; `SpecSysOpenAU.v` survives as the statement leaf with
  the dependency inverted (`SpecSysOpen` requires it); the plain frame
  and the two AU links are gone, `LinkSysOpen.v` is the link, the
  dispatcher's omode destruct is one call with `fsabs_open_in`.
  ~~UNLINK~~ LANDED — mknod's fold exactly: `SYSUNLINK`/`wp_sys_unlink`,
  the blanket derived (`unlink_arms_ret`), `SpecSysUnlinkAU.v` the
  statement leaf (its `utgt_commit_at` IS sys_link's undo leg, which is
  why it stays a leaf) with the dependency inverted, the plain frame
  deleted, ONE closer (`sys_unlink_closer` takes the armed post `ARMS`;
  the proof layer's byte-identical twin `su_au_closer` retired),
  `LinkSysUnlink.v`.  `ProofSysUnlinkAU.v` keeps its name because
  `ProofSysUnlink.v` is the pure layer below it (hygiene backlog).
  ~~CHDIR~~ LANDED — the AU form IS the contract (`SYSCHDIR`/
  `wp_sys_chdir`, blanket derived by `chdir_arms_landed`);
  `SpecSysChdirAU.v` folded whole (chdir mints no vocabulary: its pieces
  are the open leaf's); the duplicate 2402-line plain walk deleted and the
  era walk takes `ProofSysChdir.v`'s name; one `LinkSysChdir.v`; the
  friendly packaging in `FsSyscalls.v` §4 runs over the one contract with
  `fsabs_chdir_pre` (a bare `⊢`) and the bridge, needing nothing more.
  Lane total: 6 files deleted, about 4300 lines net removed.

- ~~**DUPSYNC-UNIFY**~~ LANDED 2026-09-08 (Opus lane): ~~DUP~~ LANDED — the landed
  `SYSDUP`/`wp_sys_dup_sconf` was ALREADY the sharp form (commit
  `a00e59a30` had moved the copy post into it), so the AU family was the
  redundant one: `SpecSysDupAU`, `ProofSysDupAU`, `ProofSysDupAUTail`,
  `LinkSysDupAU` deleted (about 1600 lines); `SpecSysDup.v` gains the
  pure "one pointer, two names" ties and the derived sharpened reading
  `sys_dup_post_sharp` as a lemma; dispatcher untouched.  The brief's
  premise was stale — check `git log` on a file before briefing a fold.
  ~~SYNC~~ LANDED — one `SYS_SYNC` = the flush statement (the caller's
  epoch witness `log_epoch_lb γ e` in, the receipt `flushed_sync γ e` out);
  `SpecSysSyncFlush.v` folded whole into `SpecSysSync.v` (the dependency
  runs `SpecSysSync → LogInv`, so no witness leaf); the weakening functor
  deleted, the dispatcher passes `sync_witness_0` inline and drops the
  receipt; one `Module SysSync`.

- ~~**CREATE-UNIFY**~~ LANDED 2026-09-08 (Opus lane, three phases; 7 files
  deleted, net about 14.7k lines removed).  create has ONE contract over
  all inode types: `SpecCreate.wp_create_sconf` takes the parent-prefix
  era walk (`ep_start`), the exists observation (`dlookup_commit_at`) and
  the four legs (`cre_commits`, dots included), and returns
  `cre_ok_arms`/`cre_fail_arms` with the cursor at the parent and every
  instant fired or refunded; the pure success reading is `cre_ok_pure`.
  The type-pinned twins (`SpecCreateAU` T_DEVICE, `SpecCreateAUF` T_FILE,
  `SpecCreateAUFOpen`, their proofs and links) are gone; what mknod and
  open want are LEMMAS over the one contract (`cre_{ok,fail}_arms_{dev,
  file}`, `cre_ok_pure_{dev,file}`), and each discharges create's dots leg
  trivially (it cannot fire at their types).  mkdir carries the real
  families (`mkdir_au_pre`, `mkdir_arms` with the cursor and the
  observation).  The general proof gained the era walk at its one
  nameiparent call site, the observation fire at dirlookup, the bundle
  threaded through the halves, and SIX ARM BUILDERS in
  `ProofCreateShared.v` so the arms are spelled once.  Cone fix:
  `T_FILE`/`T_DEVICE`/`create_made` moved down into `FsAbsCreateFire.v`.
  `SpecNameiparent`/`SpecNamex` stay (link, unlink and the era wrapper
  use them).

- ~~**EXEC-UNIFY**~~ LANDED 2026-09-08 (Opus lane; 16 files deleted, 4
  renamed, net about 8,300 lines removed; the change spans commits
  `3366682cc` — the lane's pre-staged deletions/renames, swept into a
  notes commit — and `4dca397a2`; the tree at `4dca397a2` is the gated
  state).  kexec and sys_exec each have
  ONE contract: the AU statements are the seals `SpecKexecAU.KEXEC` /
  `SpecSysExecAU.SYSEXEC` (`wp_kexec_sconf`, `wp_sys_exec_sconf`; the
  bundle names `exec_au_pre`/`sys_exec_au_pre` kept); `SpecKexec.v` and
  `SpecSysExec.v` are vocabulary leaves.  Deleted: the plain compositions
  and links, the PINNED prover layer (`SpecKexecPin`, `ProofKexecPin*`,
  `LinkKexecPin` — an orphan: no caller, and the AU form's `kexec_image_ok`
  is strictly stronger), and the off-build pinned seven (`SpecKexecPinned`
  four, `DirViewPin`, `NameiInitPinned`, `LinkNameiPinned`).  forkret's
  boot arm calls the one kexec contract with `exec_au_pre_triv` (a bare
  `⊢`) at `S := fun _ => emp`, zero cone growth.  `UShKernel.v` absorbed
  its ~35 lines from the pinned file.  Follow-ons, not touched: `KEXECB3`
  has no consumer by design; `KexecOkQ`'s `Q` hole has one instantiation
  left (`KexecAUBridge.exec_built_Q`) — retiring it touches the eight
  phase files.

- ~~**R-CONJ**~~ LANDED 2026-09-08 (Opus lane, two phases; 64 files, +1754/
  −1444, one new leaf).  Every one-shot piece of every fs syscall bundle is
  `pf_at AU F` — `AU F.(pf_recv) ∧ F.(pf_refund)` — with `F : pfam Σ A`
  the per-piece pair of receipt and refund (`iris/PieceFam.v`); every
  unfired-return arm returns the same `pf_at`; receipt-only definitions
  take the pair and project; the 16 fire lemmas eliminate through
  `pf_at_au`; cursors stay bare; nine seals re-typed in place at their
  old arities; the dispatcher, the friendly packaging and forkret pass
  `pfam_triv`; read converted to the record.  Refuted on the way: a
  class-indexed trivial constant (resolution guesses `A` before
  unification); `iDestruct … as "[H _]"` on `∧` (pick a side with
  `pf_at_au` instead); a bare `/=` at syscall altitude (durable note
  `d90560642`).  `pf_at_mono_pair` is the mover when an enrichment
  wrapper re-proves the AU side under the caller's own refund.

- ~~**ARM-a**~~ LANDED 2026-09-08 (two Opus agents plus coordinator
  finishing; 84 files, 4 deleted, +2.5k/−2.5k).  The step moves to the
  process: `UexecSG.v` (the deposit class and the program class), the
  three-piece arm in `UexecRet`, `udep`/`udepw`/`uxsup` in `UkRun`, the 12
  arm sites, the folded round, `ut_sys_in n`, the CurCtx-free instance at
  `spost := emp` with the exec bundle at 7 and `ssupply := True`, the gate
  slots and `cond_entry_slot` at `udep`/the `psok` blanket/`□ ssupply`,
  the exec tier folded into the one `uslot`.  The license is still in
  place; ARM-b turns the real bundles on and deletes it.  Gate: nothing
  left to build, the thirteen, zero Admitted, no folded name anywhere.

- **ARM-a, after the second agent's cut-off (2026-09-08).**  Its last edits
  were the ruled fix (the exec chain's dead `{XI : CurCtx}` binders on
  `aopen_commit_at`/`open_walk_pre_era` dropped; the class instance made
  context-free).  The one remaining red file, `SpecUserretClosed.v`, was
  being OOM-KILLED (one worker at ~478 GB RSS): durable-notes' "a lemma's
  binder list shorter than its definition's makes Coq synthesise the
  missing instance through the bundling and explode" — its
  `wp_userret_closed_body` bound `{riscvGS, xv6G, bioslotG}` and its body
  now needs `uexecSG Σ` (through `ukc`/`uslot`).  Fix: the `{SG : uexecSG
  Σ}` binder on the definition and the seal's Parameter, and the class
  import moved ABOVE the first use (it sat below it, where the backtick
  would have invented a fresh type).  Single-file compile green under a
  16 GB cap; the cone rebuild is `armb15`.  Rule of thumb for the next
  sweep: every Definition/Parameter whose body reaches `uslot`, `ukc`,
  `uexec_ret` or `udep` needs the class in its own binder list, and the
  class must be imported before it.

- **ARM-b** (in flight, 2026-09-08): ~~B0~~ LANDED and pushed
  (`6060c4442`) — the three offset-shadow pieces return the shadow
  unmoved and the fire lemmas advance it from the row invariant (which
  reaches them through `foff_row st`, already in the descriptor bundle);
  write's console conjunct is a contract premise and `filewrite_in` /
  `sys_write_in` name no kernel ghost record; `SpecArgfd.fd_st_of_key` +
  `sys_fd_st_of_key` bridge the descriptor key; `fsabs_sys_read_in` is a
  bare `⊢` at every key, `fsabs_sys_write_in` needs only the license (B2
  replaces it) and a fupd for the console seed.  RULED for B1: the
  minting law is BUPD-SHAPED (`⊢ □ Dsup ==∗ sbundle uslot n W`, the class
  laws and `udep`'s conjunct alike) — a lower bound at the empty trace is
  mintable from the unit by anyone, so the seed belongs to the law's
  modality, not to a supplier; the instance's read/write bundles are
  spelled at `fd_st_of_key`.  B1 (the real bundles, the `UEXEC_GEN` split,
  `ut_sys_out` as a post row) and B2 (the deletions, `Happ_auto` leaves)
  in flight.

- **HYGIENE BACKLOG from the folds** (one mechanical sweep, after the
  syscall folds; not a lane by itself): (a) the vocabulary leaves keep
  their old names although no AU is left in them — `SpecSysWriteAU.v`,
  `SpecSysReadAU.v`, `SpecSysMknodAU.v` (18 requiring files) — rename to
  what they hold; (b) `FsAbsMknodFire.mknod_walk_pre_era` /
  `mknod_walk_dead_era` are the nameiparent family's walk premise (open,
  unlink, create, mknod all consume them) — the misleading half is the
  `mknod_` prefix, rename family-wide; (c) consolewrite's two forms
  (CONS-FOLD, above); (d) `ProofSysUnlinkAU.v` seals the one unlink
  contract while `ProofSysUnlink.v` is the pure layer below it, and
  `SpecKexecAU.v`/`SpecSysExecAU.v`/`ProofKexecAUA.v` hold the one exec
  contracts — rename; (e) dead after the folds: `SpecSysOpenAU.
  aopen_commit` and `aopen_commit_at_weaken` (no consumer),
  `FsAbsMknodFire.mkf_acre_fire` (no application site; `caf_acre_fire` is
  the one used), `KEXECB3`'s consumer-less seal, `KexecOkQ`'s single-
  instantiation `Q` hole.

## Decisions outstanding (refreshed 2026-09-08)

Everything ruled on 2026-09-07/08 is implemented up to and including the
refund record; the ten syscall folds and R-CONJ are on main.  Still open:

- **ARM (L2-a/L2-b)** — in flight; its phase-0 inventory may surface the
  park-channel question (fd-row-pilot §6 item 3) as a real decision.
- **L5** — the rx wand's TAG output and the console ledger (the design
  sketch is under "The two options for the generic slot's supply"); the
  console READ arm's receipt is where the tag reaches sh.
- **L6** — fork's real row (mandatory: re-minting needs the supply);
  init's `wait(0)` null-window row; echo's own bundles (its pins as
  cursor/receipt families; the exec slot wand answered from
  `kexec_image_ok`).
- **Q4** stays provisional (`echo_pred := taint ∨ pins`).
- Hygiene backlog (above) after ARM.
