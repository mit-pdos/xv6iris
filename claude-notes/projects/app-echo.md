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

- [x] ~~**L2 — the step moves to the process.**~~  LANDED 2026-09-08 (lanes
  ARM-a and ARM-b, commits `7cc15a670` … `cb831ce4c`).  Each ecall deposits
  its syscall's one-shot bundle at the process's own families and gets the
  armed post back at those families; the generic slot mints from the
  supply (`app_sup`, born at boot from `Happ_sup`); `app_auto`/`Happ_auto`
  are GONE.  The application's obligations are `Hbirth`, `Happ_xfer`,
  `Happ_init`, `Happ_sup`, the ledger's and `Hphi`.  The chdir/open
  receipt split (RECEIPT-SPLIT) and fork's real row (KFORK-CHILD,
  STEADY-PARK, FORK-ROW) are landed.
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
- [x] ~~**L5 — console input tie.**~~  LANDED 2026-09-09 (RECEIPT-IMAGE,
  L5-a in two halves, L5-b): every received byte carries the
  application's persistent tag from the rx wand to the read syscall's
  receipt; the PLIC claim is the UART's lock (`plic_slot`, the pop
  token); the ring is coupled.
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

**Two B1 rulings (2026-09-08).**  (a) THE SUPPLY'S CARRIER.  `ssupply`
reads `app_pred`/`app_run`, fields of `appcfg`, and that record is BUILT
INSIDE THE BOOT FUPD (`SystemAdequacy.xv6_boot_era`'s `MkAppcfg N A r`),
so no module-level inhabitant of a `UEXEC_GEN` supply field can exist
without an axiom (the Link chain never sees a concrete record).  The
supply therefore travels as `Happ_auto` did: a Coq hypothesis `Happ_sup :
∀ c r, ⊢ □ ∀ av, app_pred A c r av` of `xv6_power_adequacy_gen`, trivial
at `app_triv`, born at boot as a FOURTH kernel-wide persistent credential
beside `kernel_text`/`cpu_claim`/`wire_inv`, threaded into the closed
loop's premise list and to the userinit and sys_fork mints.  B2 EXCHANGES
`Happ_auto` for `Happ_sup` and deletes the per-step license.  Why this is
not the GAP-premise trap: `Happ_auto` promised the predicate survives
every one-row move — unpayable by any constraining application even with
all programs verified; `Happ_sup` says the predicate is trivially true,
the honest premise of the GENERIC theorem, which runs unverified
programs.  A constraining application does not instantiate the generic
theorem: its mint sites park verified slots (L6), fork copies the parent's
slot, and the tainted generic slot's supply arrives through the exec
bundle the tainted process deposits.  (b) FAMILIES SCOPED OVER BOTH
LEGS.  With `sbundle` and `spost` existential separately, the post a
program gets back is at SOME families and tells it nothing about its own
receipts.  The class gains `sfam : Z -> Type`, `sbundle_at`, `spost_at`
(indexed by the family witness `f : sfam n`; `unit` for numbers without
a contract), and the arm is `∃ f, sbundle_at X n W f ∗ (∀ r …, rows -∗
spost_at X n W f r -∗ X (bump …))` — the fd-row pilot's deposit shape at
the families instead of the mirror; the dispatcher destructs `f`, runs
the contract at those families and returns `spost_at f r`; `ut_sys_in/
out` carry `f`; `sysc_exec_in` folds into `sysc_sys_in`.

**Three fires paid from neither the deposit nor the supply (found by the
credential step, 2026-09-08) — and the two contract corrections they
force.**  The discharger tower bottoms out in `app_step_acc` at `app_inv`;
re-basing it on `□ app_sup` is a premise rename EXCEPT at three sites
inside the fs proofs that manufacture pieces the PROCESS never deposited:
create's DOTS leg at pinned `T_FILE` (`ProofSysOpenAUEntryC` ~481) and
`T_DEVICE` (`ProofSysMknod` ~1712) — a leg that can never fire but which
`cre_commits` demands — and sys_open's FRESH-create arm, which refunds the
client's trunc piece and conjures its own (`socr_Phit_triv`) for the
`O_TRUNC` the code runs on the just-created file.  Threading the supply
into `SYSOPEN`/`SYSMKNOD` would make two syscalls unrunnable for a
constraining application (the GAP trap one level down) — refused.  RULED
(B): (i) the dots leg is GUARDED BY THE TYPE — `cre_commits` carries
`⌜tyz = T_DIR⌝ -∗ pf_at (adots_commit_at …) Fdots`, likewise the dots
disjunct of `cre_ok_arms`/`cre_fail_arms`; `cre_dots_unit` and both sites
go; a caller whose type cannot write dots owes nothing for that move;
(ii) on the fresh arm the CLIENT'S trunc piece FIRES at `bs0 = []`
(identity delta, `app_step_id`) and its receipt `Φt av i []` comes back;
the manufactured piece and the refund into `socr_fresh` go;
`open_post_ok_create`'s fresh arm carries the fired receipt.  Order:
the credential half first (green), then the tower re-base with (i)/(ii)
(green), then the instance, the post row, B2.

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

- ~~**ARM-b**~~ LANDED 2026-09-08 (three Opus agents): ~~B0~~ LANDED and pushed
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
  spelled at `fd_st_of_key`.  B1 first slice LANDED (`f5f0a59b4`): the bupd-shaped law; `sfam` as
  ONE RECORD TYPE (one field per contracted syscall) rather than `Z ->
  Type` — a dependent family cannot state `Proper` past the number binder
  and would put an `eq_rect` at the trap seam we touch once; `sbundle_at`/
  `spost_at` indexed by the witness `f`, the arm `∃ f, deposit at f ∗
  post at f`, `uexec_ret_F_split` handing out the witness, `f` a plain
  parameter of the trap/uservec/syscall bodies and their module types;
  `sbundle` survives as a derived reader, `spost` gone.  Two more rulings (a third agent finishes from the clean tree): the
  supply credential lands FIRST — the discharger tower bottoms out in
  `app_step_acc`/`app_step_acc_view`, stated at `app_inv`, so the instance
  pays its write-kind steps either by duplicating the tower (~16 twins B2
  would delete) or by RE-BASING those two lemmas and the `_unit`/`fsabs_*`
  layers on `□ app_sup` (a premise rename), which needs the credential to
  exist; and `spost_at` is `emp` at chdir 9 and open 15 THIS ROUND, because
  their landed arms bundle `proc_priv`, the fd bundle and `fd_slot` —
  kernel resources a process at its own key cannot name; splitting those
  two arms into a kernel half and a receipt half is OWED (ARM-c/L6, where
  open's receipts matter).  Read's and write's returned posts drop the pure
  blanket (it reads `pv_ofile V`; the round carries `usys_*`).  Order:
  (ii) `Happ_sup` + the re-based tower → (i) the instance at the nine
  bundles → (iii) `ut_sys_out` as a post row → B2.  The CREDENTIAL HALF
  LANDED (`84af6179e`): `AppInv.app_sup` (raw and pinned, `app_step_of_sup`),
  `Happ_sup` on the two adequacy theorems and `xv6_app_adequacy` at the
  raw record, discharged trivially at `app_triv`; `boot_shared_alloc` takes
  it at the literal record and returns it at the era's `fileG` (the one
  place the record is a literal — the boot hart's chain runs at the
  existential `fileG`, so the credential cannot be handed to it directly);
  threaded to the userinit mint, through the park package and forkret to
  the closed loop's Löb, and to the fork mint as a conjunct of
  `SyscParkEnv.park_world` (no syscall contract changed).  `xv6_ssupply :=
  app_sup`; `udep_gen`/`uslot_mint` take it.  Headers: no supply field on
  `UEXEC_GEN`; why `Happ_sup` is not the GAP trap.  The TOWER HALF LANDED
  (`83616aee6`): `app_step_acc : app_sup -∗ app_step i I av'` (one lemma,
  `_view` folded in, no mask, no side condition); the rename through the
  `_unit` layers and the fourteen `fsabs_*` wrappers; the dispatcher reads
  the credential off `park_world` (`syscall_env_sup`); B-dots as the atom
  `cre_dots_leg` guarded by `T_DIR`, discharged once at create's taken
  directory branch, `cre_dots_unit` gone; B-trunc: the fresh arm's fired
  trunc receipt at `bs0 = []`, `socr_Phit_triv` gone.  No fire on any
  dispatched path is paid from the license any more.  STEP (i) LANDED
  (`d4e1a388b`): `xfam` is one record over all nine contracts' families;
  `sbundle_at` is one match on the number at the process's own input and
  key (read/write at `fd_st_of_key`; the instance CurCtx-free at every
  branch — more dead `{XI : CurCtx}` binders dropped on open's chain and
  mkdir's, plus mkdir's dead capacity binders); the two supply laws hand
  back `FsAbsInvFire`'s dischargers (write's console seed is the one bupd);
  `sysc_exec_in` folded into the per-number `sysc_sys_in`; all eight fs
  arms take their input from the deposit and drop the armed post they get
  back.  `spost_at` stays `emp` until `ut_sys_out` is a post row: the
  round's premise is PRODUCED by the loop and has no producer before that
  row — turning the posts on first made `ProofUserretClosed` unprovable.
  STEP (iii) LANDED (`6b9666092`): `ut_sys_out n f` is a row of
  `usertrap_post` at the plain entry frame and the outgoing a0 word;
  `sysc_sys_out` beside `sysc_exec_out` in the dispatcher's post, produced
  by the six fs arms from their contracts' armed posts (read/write's
  `*_extra` at `fd_st_of_key` without the pure blanket) and paid quietly by
  the rest; `xv6_spost`'s six real branches, `emp` at exec (consumed) and
  at chdir/open (the arm split owed); the loop discharges the round's
  `spost` premise from uservec's row.  B2 LANDED (`cb831ce4c`): `app_auto`/`Happ_auto` and the license family
  deleted from AppInv, the movers, the mint, the two adequacy theorems and
  `App.xv6_app_adequacy`; the eleven external `app_top_update` sites drop
  the license token; App.v/AppEcho.v state the obligations exactly.  THE
  ARM IS COMPLETE.

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

#### RECEIPT-SPLIT (LANDED 2026-09-08) — chdir's and open's posts stop being `emp`

The ARM's post at 9 and 15 is `emp` because the landed arms bundle
`proc_priv`, the fd bundle and `fd_slot`.  The lane splits each arm into a
KERNEL half (what the dispatcher's tail keeps: the block, the fd bundle,
`fd_slot`, the `fd_frees` head) and a RECEIPT half the process can name,
and the instance returns the receipt.

THE POST IS READ AT THE RESUME VIEW.  A receipt is worth something only if
it ties what the walk reached to the key the process resumes at: chdir's
says the new working directory IS the inum `i` whose row is `ADir e`, and
open's says the descriptor's state in the resumed table IS
`FdOpen rd wr (FdInode i γo)` (or `FdDevice ma`) at the inode the path
resolved to — facts the pure rows (`usys_cwd_ok`, `usys_fd_ok`) leave
existential.  So `spost_at X n f W r fdv' cw'`: the trap key, the returned
a0, and the resume key's descriptor view and cwd, bound by the same ∀ in
`uexec_ret_ret_F` that already binds them.  `sysc_sys_out`/`ut_sys_out`
and uservec's row carry the two arguments (uservec's exec row already
takes `U' sts sts'`).  Receipts: `chdir_receipt Γ γfs cw P Pmiss Fo r cw'`
(fail: `cw' = cw` and the refund; ok: `cw' = i`, the cursor, `arow_at`,
`pf_recv`); `open_fd_rcpt rb wb t sts r fdv'` (pure: `r = fd`,
`sts !! fd = Some FdClosed`, `fdv' = <[fd := FdOpen rb wb t]> sts`) inside
`open_receipt_plain/_create`, mirroring `open_in`.  The arms keep their
strength; `chdir_arms_split`/`open_arms_split` are the rearrangements the
tails consume.

AS LANDED.  `UexecSG.spost_at` reads the returned a0 AND the resume key's
two moving components — the descriptor view and the working directory —
under the same ∀ of `UexecRet.uexec_ret_ret_F` that binds the four pure
rows; the route down is `SpecSyscall.sysc_sys_out`,
`SpecUsertrap.ut_sys_out` (with its `_cong` and `_quiet`) and
`SpecUservec`'s post row, all at the record and view the round leaves.
`SpecSysChdir.chdir_receipt` and `SpecSysOpen.open_receipt` (plain and
create, keyed on O_CREATE as `open_in` is) are the process-nameable halves
of the two arm families; `chdir_arms_split` (premise `pv_cwi (us_V U) =
cw`, which the body instantiates) and `open_arms_split` hand the
dispatcher the kernel half (`proc_priv`, the fragments, `fd_slot`) plus
the pure row `sysc_fd_ok` needs, and the process the receipt.
`SpecSysOpenAU.open_fd_rcpt` / `open_fd_ok_split` split open's descriptor
bundle without moving `open_fd_ok` (the five ProofSysOpenAU* producers are
untouched).  `UexecExecInst.xv6_spost` pays eight numbers; exec alone pays
`emp`; `sysc_num_nofs` excludes 9 and 15; `ProofSyscall.sysc_out_chdir` /
`sysc_out_open` are the two arms' intros.  Three dead `{XI : CurCtx}`
binders (`open_walk_dead_era`, `open_post_fail_plain/_create`) are gone.
`UexecSG.f_equiv_wide` / `solve_contractive_wide` carry the two U-mode
fixpoints past stdpp's five-argument `f_equiv` (durable-notes gotcha).
Audit unchanged at thirteen.

#### FORK'S REAL ROW — scoped, NOT a single lane (2026-09-08)

What it takes to hand kfork the process's deposited child continuation
(`uexec_fork_F`'s second conjunct, at the ONE record
`bump W 0 (uvis_M W) (uvis_perm W) (uvis_sz W) (uvis_fd W) (uvis_cwd W)`)
instead of minting from the supply:

1. `SpecKfork`'s slot premise is a FAMILY over every W with
   `uvis_fd W = stsP ∧ uvis_cwd W = pv_cwi (us_V Up)` — free in tf, image,
   perm, sz.  It must become the single record: kfork's contract has to
   STATE the child's ustate as a function of the parent's (trapframe copied
   with a0 := 0 — `bump_tf` at 0 — image, perm and sz equal).  Today's
   proof knows the pieces separately (B4's `Vc'` facts, B6's
   `upd_pt (upd_sz Vc (pv_sz Up)) P' (pv_tf Vc)`, `SpecUvmcopy`'s pointwise
   flags) but never assembles them.
2. THE IMAGE IS THE OBSTACLE.  `SpecUvmcopy`'s post is
   `M' = umem_write Mnew 0 (4096 * n) (fun a => Mold !!! a)` — agreement on
   the copied range, `Mnew` elsewhere — not `M' = Mold` as a gmap.  The
   child arm demands `uvis_M W` on the nose.  RESOLVED: the key's image IS
   canonical.  `proc_priv` holds the LAZY view (`umem_lazy P sz M`:
   `is_Some (M !! va) <-> uva_mapped P va \/ uva_live sz va`, unmapped live
   bytes read zero) and `um_below sz` puts every mapped page below sz, so
   `dom M` is exactly `[0, pgroundup sz)`.  The child is indexed at the
   parent's size (the "copied region live in both" premise) and
   `n = uvm_np sz` covers that whole range, so `umem_write Mnew 0 (4096 n)
   (Mold !!! ·) = Mold` by `map_eq` — a pure lemma over `umem_write` and the
   two domain laws, no change to the child arm.
3. THE PARK RESUMES AT AN EXISTENTIAL RECORD.  `ParkCap.park_pkg`'s
   closer instantiates the family at `uvis_of U' sts` with U' related to
   the parked U only by `pv_upt`, `pv_fdg`, `pv_cwi` — because forkret's
   boot arm runs kexec("/init") between park and resume.  A forked child
   never runs the boot arm (kfork holds `first_done`), so a STEADY park
   variant whose closer resumes at the parked record exactly is sound, but
   it is new ParkCap/ProofForkretPark/SpecForkretParkPaid machinery.
4. Then the dispatcher's fork arm (`UexecApply` FORK ROW note) instantiates
   both arms: parent at `r ≠ 0` from `kfork_post`'s pid arm, child handed
   to kfork.

Three lanes at least: (a) kfork states the child record (with the image
lemma above); (b) the steady park; (c) the row.  Order: (b) first — the
kfork↔park seam is where a single slot must be accepted before kfork can
be asked for one; then (a); then (c).

LANES (a) AND (c), DESIGNED (2026-09-08; briefs cut after (b) lands).

(a) KFORK-CHILD.  `SpecKfork`'s slot premise becomes ONE slot at the
record kfork builds, stated from the parent:
  `kfork_child Up := MkUstate (upd_tf (us_V Up) (<[14%nat := zero_reg]>
   (pv_tf (us_V Up)))) (us_M Up)`; premise `uslot (uvis_of (kfork_child Up) stsP)`.
The proof re-keys it onto the child's actual record `Uc` at the park
(`uslot_of_urun_eq`): trapframe — the copy loop leaves `pv_tf Vc = pv_tf Up`
(`ProofKforkMain` ~586, `V1`) and B7 stores word 14 (`kfk_b7`'s post);
image — `umem_write Mnew 0 (4096 n) (Mold !!! ·) = Mold` (the lazy view is
canonical, above); perm — `perm_of (ud_um P') sz = perm_of (ud_um Pold) sz`
from uvmcopy's pointwise post (`perm_leaf` reads bits 1..4 only,
`pte_set_ad` writes 6..7, `uvm_pte (pte_flags10 w)` keeps the low ten;
`dom` agrees because `um_below` puts every mapped page under `n`); sz —
`np->sz = p->sz`; cwd — B4's `pv_cwi Vc' = pv_cwi Up`.  `ProofSysFork`
hands kfork the single slot, minted from the supply for now.
  KFORK-CHILD (LANDED 2026-09-08; brief `brief-kfork-child.md`).
  Phase-1 facts: `kfork_child Up := us_tf Up (<[14%nat := zero_reg]>
  (pv_tf (us_V Up)))` and the pure lemmas live in a new leaf
  `iris/KforkChild.v` (a lemma in UserPtTree rebuilds 659 files, in
  ProcPtOwn 621; the leaf rebuilds none) — `umem_write_copy_id`,
  `perm_leaf_pte_set_ad`, `perm_leaf_uvm_pte_flags10`, `perm_of_ext`,
  `perm_of_uvmcopy_child`, `urun_eq_kfork_child`; `4096 * uvm_np sz =
  pgroundup sz` is `ProcPtOwn.uvm_np_live`; the child's table is literally
  `∅` before the copy (B6's `HCempty`).  `kfk_b5` is abstract over the run
  key `Wk` with `urun_eq Wk Uc` and `uvis_fd Wk = stsP`.  B6 DISCARDED the
  child's image (`∃ Mc, proc_ptm P' … Mc` at the uvmcopy return) and
  `kfk_pro_exit3` carried neither sz, image nor perm facts to Main — phase 2
  keeps the concrete image and threads the three facts.  AS LANDED: B6
  closes the child's image at `us_M Up`, its exit clause and `kfork_arm3`
  carry sz/image/perm, Main assembles `urun_eq_kfork_child`;
  `ProofSysFork` mints the one slot from the supply (lane (c) replaces
  the mint by the deposit); `UexecCond.uslot_congr` deleted (no callers).

(c) FORK-ROW.  The child continuation travels DOWN as fork's deposit and
the parent's arm is instantiated at the return:
  - `UexecRet.uexec_dep_F` at fork := the child conjunct at its one record,
    `X (bump W 0 (uvis_M W) (uvis_perm W) (uvis_sz W) (uvis_fd W) (uvis_cwd W))`
    (the `∀ fdv' cw'` guards collapse: fork copies the table and keeps the
    cwd); `uexec_arm_F` at fork := the parent conjunct only.
  - `SpecUsertrap.ut_fork_in` / `SpecSyscall.sysc_fork_in` carry it (mold:
    `ut_exec_out`, a number-specific row); the dispatcher's fork arm hands
    it to `SysFork`, whose contract takes `uslot (uvis_of (kfork_child U) sts)`
    — `bump_tf (uvis_tf W) 0` and `<[14 := 0]> (pv_tf U)` agree on the
    resume gpr and pc (the dispatcher's record is the key with epc bumped),
    the rest of the key is the parent's; `ProofSysFork`'s mint goes.
  - THE PARENT AT r ≠ 0 resumes on the program's parent conjunct.
  - THE PARENT AT r = 0 — PID WRAP — RESUMES ON THE SUPPLY.  `allocpid`'s
    counter is a 32-bit word with no bound (`nextpid_res_at` is an
    existential value; `addiw` wraps), so the kernel cannot promise
    `pid ≠ 0` without a fork budget nothing enforces.  The row therefore
    reads: `r ≠ 0` → the program's arm; `r = 0` → `uslot_mint` from
    `app_sup`, i.e. after 2^32 forks a verified parent may fall to the
    generic slot.  Honest, and it is exactly what the supply is for; the
    program's `⌜r <> 0⌝` guard stays.  No positivity invariant on nextpid.
    [2026-09-09, XV6_REV ded23f2: upstream fixed the wrap — pids are now
    reused from `[1, PIDMAX]` by a scan under pid_lock, so the kernel CAN
    promise `pid ≠ 0`; the contracts do not say so yet.  What retiring this
    row costs is itemised in `kernel-defects.md` ("STILL OPEN AS PROOF
    WORK").]
  FORK-ROW (LANDED 2026-09-09; brief `brief-fork-row.md`).  Phase-1
  facts: `uexec_fork_F = uexec_fork_parent_F ∗ <guarded child>`; the arm
  at fork is the parent piece, the deposit `uexec_fork_child_F X W := X
  (bump W 0 (uvis_M W) (uvis_perm W) (uvis_sz W) (uvis_fd W) (uvis_cwd W))`;
  `_split`/`_join` really split fork (the child's guards re-enter by
  substitution).  `SpecUsertrap.ut_fork_in sc_v tf U sts := ⌜ecall ∧ num tf
  = fork⌝ -∗ uslot (uvis_of (us_tf U (bump_tf tf 0)) sts)` is stated over
  the TRAPFRAME argument (the record on `wp_usertrap_body` carries the
  previous round's epc; the prologue rewrites it), instantiated at
  `<[tf_epc_idx := ret_pc sepc_v]> (pv_tf (us_V U))` exactly as
  `ut_exec_out` is; its congruence is `tf_ueq`-shaped with two length
  premises.  The bridge to `SpecSyscall.sysc_fork_in U sts := … uslot
  (uvis_of (kfork_child U) sts)` is a RECORD EQUALITY: usertrap's `+4`
  store (`Ha5`) and `HV1tf0` make `<[14 := 0]> (pv_tf V1)` literally
  `bump_tf (pv_tf U) 0`.  The non-ecall arms DROP the input rows (no
  `_quiet` relay; the caller-less `ut_sys_in_quiet` goes too).  Uk* files
  compile unchanged.  AS LANDED: `ProofSysFork` forwards the slot — the
  mint, its `UEXEC_GEN` argument and `LinkSysFork`'s `UG` are gone, so
  userinit's park is the ONE mint site left; at the return the round
  instantiates the parent's arm at the pid, and `r = 0` (the pid wrap)
  alone falls to the supply; `park_world` stays in sys_fork's contract
  (kfork takes it independently).  Deleted as caller-less:
  `uexec_dep_F_of_supply_ne`, `uexec_dep_of_supply_ne`.

FORK'S REAL ROW IS COMPLETE: (a) KFORK-CHILD, (b) STEADY-PARK, (c)
FORK-ROW all on main.  The generic slot is minted in exactly two places —
userinit's park and the pid-wrap return — and the loop's round otherwise
runs on the process's own deposit.

STEADY-PARK (lane (b), LANDED 2026-09-08).  The slot the park captures
sees only (resume gpr, resume pc, image, perm, sz, fd, cwd) —
`UexecApply.uslot_key_cong` — and forkret's steady arm resumes at a record
that agrees with the parked one on all of them (`tf_ueq` from
prepare_return, `us_M U` unchanged, `ud_um (ud_norm P) = ud_um P`, sz and
cwi untouched).  So the park package gains an OPTIONAL parked run key
`Wk : option uvis`: `Some (uvis_of U [])` when the parker holds
`first_done` (kfork), `None` otherwise (userinit).  With `Some`, the
package carries `first_done` and the closer gets the pure premise
`urun_eq Wk U'`; the parker captures ONE slot `uslot (uvis_of U sts)` and
the closer re-keys it by the congruence.  forkret's boot arm refutes
`Some` by `first_tok_boot_excl` (its `first_addr ↦₄ 1` against the
package's `↦₄□ 0`); its steady arm proves `urun_eq` from the facts it
already has.  kfork parks steady, instantiating its family at
`uvis_of Uc stsP`; `SpecKfork`'s premise is unchanged until lane (a).
Brief: scratchpad `brief-steady-park.md`.  Phase-1 corrections: the
run-key vocabulary (`urun_eq`, `urun_eq_of`, `urun_eq_resume` in
projection form, `uslot_of_urun_eq` from `uslot_ukc`) lives in
`UexecRet.v` (UexecSlot has no `tf_resume_gpr0`; `ProcInv.upd_upt` is
outside UexecRet's cone); `steady` is a plain parameter of
`forkret_park_paid_body` / `wp_forkret_gen_body`, and the boot-arm
refutation's `first_done` is a premise of `wp_forkret_gen_body` (the
closer stays a ∀-wand), moved by one more `ctx_move` in the cap's proof;
two park lemmas, `park_token_park` and `park_token_park_steady`, no
shared body.  AS LANDED: `park_cap` takes `steady : bool`; `park_pkg`'s
`Wk : option uvis` is `if steady then Some (uvis_of U []) else None`; a
`Some` package carries `first_done` and its closer takes `urun_eq Wk U'`;
`wp_forkret_gen_body` gains `steady` and `if steady then first_done else
emp`; forkret's steady arm proves the run key by `urun_eq_resume`, its
boot arm is refuted by `first_tok_boot_excl` in the main theorem, so
`fkr_boot` keeps `Wk := None`; `ProofKforkB5` parks steady, spending its
family at `uvis_of Uc stsP`.  Gotcha recorded: `iFrame` past a package
row reaches INTO `first_done`'s `fs_ready` copies of persistent rows —
build such packages with `iSplitL`/`iSplitR`.  `UexecCond.uslot_congr`
has no callers (delete in (a) or (c)).

#### HYGIENE (LANDED 2026-09-09; brief `brief-hygiene.md`)

The sweep owed after the folds, ruled from the phase-1 inventory:
(H1) the `AU`-suffixed leaves become `Sys{Write,Read,Mknod,Open}Defs.v`;
exec was INVERTED (its `AU` files held the contracts and `SpecKexec.v` /
`SpecSysExec.v` were live vocabulary leaves) — swapped in one pass:
`SpecKexec`→`KexecDefs`, `SpecKexecAU`→`SpecKexec`, `SpecSysExec`→
`SysExecDefs`, `SpecSysExecAU`→`SpecSysExec`, `ProofKexecA`→
`ProofKexecACode`, `ProofKexecAUA`→`ProofKexecA`, `KexecAUBridge`→
`KexecBridge`; unlink: `ProofSysUnlink`→`ProofSysUnlinkPure`, the `AU`
proof family drops the suffix (`…AUParts`→`ProofSysUnlinkShared`); open's
thirteen `ProofSysOpenAU*` drop it (`…AUParts`→`ProofSysOpenShared`).
Lemma-level `_au` bundle names stay (EXEC-UNIFY's record).
(H2) `npar_walk_pre_era`/`npar_walk_dead_era`, `namei_walk_pre_era`/
`namei_walk_dead_era`, `npar_elems` — `_era` KEPT: both walks are stated
over the era lend, so the suffix names a real concept.
(H3) `uexec_ret_ret_F`→`uexec_ret_cont_F`.
(H4) `aopen_commit`/`aopen_commit_at_weaken` and `mkf_acre_fire` deleted;
`KEXECB3` collapses into `ProofKexecB3.v` (the ascription stays — dropping
it would make the 4200-line functor body transparent); `KexecOkQ`'s `Q`
hole is LEFT (threaded through eight phase files, plugged once; a header
line records it).
(H5) the fd-row pilot's ten parallel-form files are deleted (none in the
adequacy cone; `FsImgConsole.v` dies with them); its design note is
retired to `completed/`; `fd_frags_any` is live and stays.
(H6) CONS-FOLD: the Loc form takes the plain names; `consolewrite_stack`
survives into the folded file (it is on the path).
Rebuild: 607 files (the `FdSlots.v` comment is in).  AS LANDED: 14 files
deleted (the pilot's ten, the superseded consolewrite trio, `SpecKexecB3`),
34 renamed, no `AU` in any filename; `SysUnlinkDefs.v` joined the leaves;
`ProofSysUnlinkPure.v` is the pure layer under unlink's walk, `*Shared.v`
each walk's hoisted layer; `ProofKexecACode.v` phase A at the machine,
`ProofKexecA.v` phase A at the contract; `KexecBridge.v` the pure closer.

#### RECEIPT-IMAGE (LANDED 2026-09-09; brief `brief-receipt-image.md`)

A GAP IN READ'S RECEIPT.  `read_post_ok` hands the process the node `a`,
the offset and the count, but the bytes in its OWN BUFFER are the image
row's existential `bs` (`usys_mem_ok` at read: `M' = umem_wr M addr d bs`)
and the receipt is read at `(W, r, fdv', cw')` — no `M'`.  fileread's and
sys_read's contracts say so in as many words ("this contract does not
relay that … a caller that wants it calls readi").  So a verified reader
learns nothing about what it read; sh's `gets` cannot follow a parse, and
L5's console tags would have nothing to attach to.

THE FIX.  `spost_at X n f W r M' fdv' cw'` — the post is read at the
resume image too (RECEIPT-SPLIT's mold; `π'`/`szv'` stay out).
`read_post_ok Γ i n F r M' addr` gains the pure tie: on an `AFile bs` row,
`∀ j < d, M' !! (addr + j) = Some (bs !!! (off + j))`; the directory arm
stays unstated, the console/pipe arms are not `FdInode`.  The obligation
sits at fileread's two fire sites: readi's post is an equation
(`umem_wr … tot (rd_bytes data off)`), the fired row is
`abs_row (era_node dnl bml data)` whose file bytes are `file_bytes
(fn_data …) (fn_size …)`, and `rd_bytes data off j = file_byte data
(off + j)`; `umem_wr_lookup_in` closes it.  Then L5's console receipt is
`∃ bs, ⌜∀ j < d, M' !! (addr+j) = Some (bs j)⌝ ∗ [∗] tags` at the same
place.  Phase-1 facts: `spost_at` has EIGHT arguments (`f_equiv_wide`
grew an eight-arity case); `file_bytes_lookup` existed in `ElfBridge.v`
and moved beside `file_bytes` in `FsTree.v`; the stable corollaries
`arf_stable_ok_arm`/`arf_stable_of_arms` take `M' addr` and weaken the
tie away; SpecSyscall's contract has ONE post row at `us_M U'` and the
read arm's `umem_wr … dw bsw` is its instantiation inside ProofSyscall.
AS LANDED: the `AFile` tie is GUARDED by the caller's run linearity
(`∀ i < d, uint (addr + i) = uint addr + i`) — `umem_wr` is keyed by the
64-bit va precisely so no kernel contract promises the destination does
not wrap (SpecCopyout's and SpecReadi's headers), and `umem_wr_lookup_in`
takes linearity as a hypothesis; a program that owns its buffer has it for
free (`UkRunSys.uheap_ubytes_run` bounds mapped addresses below MAXVA).
`ProofFileread.fr_buffer_tie` is the obligation, `FsTree.file_bytes_lookup`
its last step.  Fourteen quiet sites, not sixteen; `sysc_out_read` reads
the destination argument.

ORDER AFTER THIS: L5-a (the tag column in `uart_inv_body` beside `u_rx`,
the rx wand returns the persistent tag, `uartgetc` pops byte + tag),
L5-b (consoleintr → `cons_res`'s tag column → consoleread's post →
fileread's device arm → sys_read's console receipt), ARM-c (echo's supply
from the taint, `echo_pred := taint ∨ pins`), L6 (init/sh/echo programs),
L7.

#### L5 — findings for the design (2026-09-09); L5-a in flight (`brief-l5a-tag.md`), L5-b drafted (`brief-l5b-ledger.md`)

THE READS ARE FREE.  uartgetc's LSR poll and RHR load are
`wp_uart_read_free_s_sconf` (WpSconfUartAccess): the loaded byte is an
arbitrary `bt`/`c` with NO relation to the device's `u_rx`.  So the kernel
today learns nothing about the byte it hands consoleintr.  The tag column
needs NON-FREE reads: `SpecUart.wp_lb_uart_s_sconf_body` already carries
an invariant-open callback (`∀ u bt u', ⌜uart_read u off = Some (bt, u')⌝
-∗ uart_ghosts γ u' -∗ R ==∗ uart_ghosts γ u' ∗ S bt` — the LSR `_ea` read
uses it to learn THRE); the RHR pop is `uart_read u 0 = Some (b, u')` with
`u_rx u = b :: rx'` when nonempty, and JUNK (`byte0` with the FIFO on)
when empty.

THE JUNK ARM IS REFUTABLE.  uartgetc runs only inside uartintr, between
devintr's `plic_claim` (which returns `uart_irq_id` and sets `p_claimed`)
and `plic_complete`; `DevModel.plic_latch` refuses to re-pend a claimed
source, so no second hart enters uartintr for the UART until completion —
exactly one hart pops the FIFO at a time, and after a non-free LSR read
shows DR the FIFO is still nonempty at the pop.  What is missing is the
RESOURCE: `plic_inv_body` is `∃ p, plic_frag p ∗ ⌜plic_ok p⌝` with nothing
about the claim.  Add an rx CLAIM TOKEN `uart_rx_tok` held by the PLIC
invariant while `p_claimed p uart_irq_id = false`, handed out by
`plic_claim`'s post when it returns the UART id and taken back by
`plic_complete`; uartintr's contract takes and returns it; the non-free
reads require it.  Without it the honest receipt is `tag ∨ ⌜junk⌝`, and
a junk 0x00 in sh's line breaks the output side (L7) with no taint to fall
back on.

THE TAG COLUMN.  The application supplies a persistent family
`Tg : list mobs → iProp` (echo: `⌜disc h⌝ ∨ taint`) and its rx wand returns
`R h' ∗ Tg h'` (`echo_R_rx` can: disciplined → left; otherwise the counter
is 1 → the lb).  `uart_inv_body` gains a column aligned with `u_rx`: the
history prefixes `hs` at which each queued byte was pushed, with
`[∗ list] h ∈ hs, Tg h` and `⌜last h = ObsUartIn b⌝` per byte (persistent,
so a pop hands the reader a copy).  The rx arm of `wp_uart_loop` pushes;
every other arm preserves; the RHR pop drops the head.  Then the kernel
ledger: consoleintr takes the byte's `(h, Tg h)` and stores it in
`cons_res`'s ring beside the byte; consoleread's post yields, for the `d`
bytes copied, `∃ hs, ⌜length hs = d ∧ ∀ j, last (hs !! j) = ObsUartIn
(bs j)⌝ ∗ [∗ list] h ∈ hs, Tg h`; fileread's device arm and sys_read's
console receipt carry it to the process (RECEIPT-IMAGE's `M'` gives the
`bs j` tie).  Lane cut: L5-a = token + non-free reads + column + the App
hypothesis (`Htag`); L5-b = the console ledger through to the receipt.
Two design details fixed in the briefs: the tag family is AMBIENT, a
field `riscv_rx_tag` beside `riscv_obs_pred` in the machine class, so
`dev_inv`'s type does not move; the rx token is a ghost_var half
`uart_rx_tok γ k` (k = bytes popped) with a mono-nat `uart_rx_pushed_lb`
— the LSR read under the token mints `pushed ≥ k + 1`, the RHR pop under
both finds the FIFO nonempty (no junk arm).  consoleintr stores
`cons_xlate b` (`'\r'` → `'\n'`) with the tag; the ring gains the
coupling `r ≤ w ≤ e ≤ r + 128` the ConsoleInv header foresaw, maintained
at consoleintr's guard and consoleread's push-back.

L5-a PHASE-1 FINDINGS AND RULINGS (2026-09-09).  (F1) `uart_tx_pop` in
LOOPBACK mode re-queues the drained byte into `u_rx` with no observation
— the column carries `⌜uart_loopback u = false⌝` (true at reset, nothing
writes MCR).  (F2) `uartinit`'s FCR write (`0x07`) FLUSHES `u_rx` without
a pop, which no monotone counter survives — RULED: the rx token is born
into the BOOT CHAIN at `dev_inv_alloc`, threads `main → consoleinit →
uartinit` (the flush is "pop everything" under the token: `nk := np`;
every FCR write requires it), and `main` DEPOSITS it into `plic_inv`
before `plicinit`/`plicinithart`.  `plic_inv_body` is two-armed:
pre-init `uart_preinit γ ∗ ⌜∀ c, ¬ plic_enabled p c uart⌝` (so a UART
claim there is refuted through `plic_cand`) or post-init `uart_inited γ ∗
tokslot γ p`; `plicinithart`'s enable write requires the persistent
`uart_inited`.  (F3) `plic_ok` gains `p_pending i → ¬ p_claimed i` (the
claim's handout needs the token to have been inside).  (F4) the RHR read
is a pop only with DLAB clear — the pop takes `uart_dlab_off`.  (F5) the
free read keeps two users (ISR ack at 2, uartintr's THRE poll at 5) and
gains `off ≠ 0`.  The column is a SEPARATE callback leg on the UART
load/store bodies (`uart_colE`), not inside `uart_ghosts`, so the
application's rx/tx wands keep their shape.  `riscv_obs_pred` lives in
`riscvFixedGS` (RiscvPtsto.v:523), set by `RiscvAdequacy.boot_fixedGS`
— `riscv_rx_tag` sits beside it.  `AppEcho.v` builds no `xv6_app`
record; it gains `echo_tag γcl h := ⌜disc h⌝ ∨ mono_nat_lb_own γcl 1`.

RULED 2026-09-09 (owner): THE PLIC IS THE LOCK, AND IT GETS A CSL SPEC.
uartintr/uartgetc's exclusion is NOT a kernel bug (the PLIC gateway does
not re-forward a claimed source until completion; the claim brackets the
whole handler) — it is a correctness argument that the proofs must
state: `plic_claim` returns the claimed source's payload `R i` (the UART's
is the EXCLUSIVE RIGHT TO POP, `uart_rx_tok`), `plic_complete` takes it
back into the PLIC's logical ownership.  The PLIC invariant is not
initialised until needed: per source `plic_preinit ∨ (plic_inited ∗ if
claimed then emp else R i)`; boot populates the UART's slot uninitialised;
initialising the UART/PLIC (main, after consoleinit's flush under the
token, before plicinit) swaps to the right arm and mints the persistent
`inited`; the disjunction elimination is FOLDED INTO plic_claim /
plic_complete (they take the persistent witness, which rides
`console_caps`), so callers never see it.  The `¬ enabled` clause and
plicinithart's premise from the phase-1 design are dropped.  Brief:
`brief-l5a-finish.md` (a fresh agent over the previous agent's tree, which
was complete and proved except two red files; backup `l5a-wip-*.tgz`).
L5-a (2/2) LANDED: the PLIC invariant is a row of per-source SLOTS
(`WpUart.plic_slot γ p i := plic_preinit γ i ∨ (plic_inited γ i ∗ if
p_claimed p i then emp else plic_payload γ i)`, over `plic_tracked =
[uart; virtio]` — under `plic_ok` a claim returns only those two); the
three tables are concrete and name only the UART (payload = the receive
token `uart_rx_tok`, one-shot = `un_init`); the pre-state says nothing
about `p`, so plicinit/plicinithart owe only `plic_slots_stable`, and the
deposit's unreachable in-service branch parks `emp`; `plic_claim` /
`plic_complete` take `uart_inited` and own the disjunction.  The column,
the non-free LSR/RHR reads (`wp_uart_lsr_read_rx_s_sconf`,
`wp_uart_rhr_pop_s_sconf`, `wp_uart_fcr_write_s_sconf`, the free read at
`off ≠ 0`), `wp_uartgetc_inline`'s byte + tag (`ObsTrace.obs_ends_in`),
uartintr's token loop, consoleintr's tag premise (taken, unused until
L5-b), the boot chain (`dev_inv_alloc` → main → consoleinit → uartinit's
flush → main's deposit before plicinit), `BootChain`/`SystemAdequacy`
naming the token.  `rx_masked`/`rx_empty` moved to WpSconfUartAccess.
L5-a (1/2) LANDED `8dbf1eaec`: the ambient family, the permit's tag
output, `plic_serve_ok` in `plic_ok` with `plic_claim_serves`, the App
plumbing, `echo_tag`.  Placements ruled for (2/2): `uart_inited γd` is a
fourth row of `console_caps` (which already crosses `started` inside
`main_deposit`); `uart_dlab_off` is already inside `is_txlock` ⊂
`console_caps`, so the RHR pop's DLAB premise costs no contract change.

#### L5-b LEDGER (LANDED 2026-09-09; briefs `brief-l5b-ledger.md`, `brief-l5b-finish.md`)

Phase-1 facts.  The ring's coupling is stated on the 32-BIT DIFFERENCES
the code itself compares (`c.subw` then `bltu`): `cons_ok r w e :=
uint (w - r) ≤ uint (e - r) ≤ 128`; `uint r ≤ uint w ≤ uint e` is
FALSE because the three `uint` indices only ever increment and wrap
(not a kernel bug — unsigned differences are exactly right).
`cons_slot r k := (uint r + k) mod 128` is wrap-blind because 128 | 2^32
and injective on `[0,128)`; `cons_row r e bs ts` ties each live slot's
tag `Some h` to its byte by `obs_ends_in h b ∧ bs !! slot = cons_xlate b`
(`'\r' → '\n'`, the one translation before the store).  consoleread's
post gains `hs` with `cons_tagged bs hs d` and the persistent tags;
`SpecFileread.console_receipt r M' addr` (no `n`) at `FdDevice CONSOLE`
by `decide`, with the three `fileread_extra_dev_*` lemmas; the `-1`
disjunct exists only at fileread's tier.  THREE maintainers in
consoleintr, not two: the guard (`ct_dflt`, the fact born at +0x044 must
be passed down to `ct_store`/`ct_cr` with the tag premise), the two
`cons.e--` (kill loop and backspace need `⌜ee ≠ ww⌝`), and `cons.w := e`
(`ct_wake_prop` took the ring whole and a2 opaque — it now takes the ring
destructed with `⌜a2 = sext ee⌝`).  consoleread's `cr_win`/`cr_run` hid
the run's source under `umem_wrote`; they name it now, with the `hs`
accumulator through seven loop invariants; the pop needs `⌜rr ≠ ww⌝`.
`boot_cons_res` founds `r = w = e = 0` (bss cells) with `ts = replicate
128 None`.  AS LANDED (second agent, after the first died on the session
limit mid-consoleintr): consoleintr maintains the coupling at FOUR
places (the room guard feeding the store and the `'\r'` arm, the two
`cons.e--` under a hoisted `e ≠ w`, the wake tail's `w := e`);
consoleread's `cr_win`/`cr_run` name the run's source, the pop reads the
slot's tag out of `cons_tags` (persistent, `cons_tags_get`), rounds
append by `cr_wr_glue`/`cr_tagged_glue`, the +0xe6 push-back restores the
coupling; ProofFileread's console arm SPLITS ON THE MAJOR
(`fileread_extra_of_dev_console` / `_of_dev_other`) because fileread's
contract does not know its devsw column is the console's table — the
tie `frn_rp fn = devsw_read_val` is the DISPATCHER's premise
(SpecSysRead), so `devsw_read_val_is_console` is a table fact only.
`fileread_extra_dev`/`_of_dev` are split three ways.  L5 IS COMPLETE: a
byte's tag travels rx wand → UART column → uartgetc → consoleintr → the
ring → consoleread → fileread's console receipt → the read syscall's
`spost_at` → the process.

#### ARM-c — DESIGN (2026-09-09): `Happ_sup` leaves the theorem; the kernel never mints

WHERE THE SUPPLY IS SPENT TODAY.  `app_sup` (boot-born from `Happ_sup`,
threaded as the fourth kernel-wide credential) is spent by the kernel at
exactly THREE mint sites: (1) userinit's park (`ProofUserinit` ~806:
`uslot_mint` at the family the park captures); (2) the trap loop's exec
GAP arm (`UexecApply` ~888: `ut_exec_out`'s third disjunct — kexec
succeeded, `r ≠ -1`, but the node is not `anode_loadable`, `exec_post_ok`'s
arm (b); the round mints because the process's slot wand
`exec_slot_pre` speaks only of loadable files); (3) the pid-wrap row
(`UexecApply` ~908).  Everything else that names `app_sup` — the
`fsabs_*`/`caf_*`/`lnk_*` dischargers, `xv6_ssupply`, the supply law —
is the CONSTRUCTION of a generic slot's bundles from a supply, used by
whoever mints such a slot; those stay, parametric in the supply.

WHY A CONSTRAINING APPLICATION CANNOT HOLD `Happ_sup`.  It is `∀ c r,
⊢ app_sup_raw (app_pred A c) r`, i.e. "the claim is trivially true"; for
echo `echo_pred := taint ∨ pins` is true of every view only under the
taint, which exists only after the first bad byte.  So `taint ⊢ app_sup`
(the taint is persistent) but no closed hypothesis does.  The generic
slot's supply must therefore come from a PROCESS that holds the taint,
never from the kernel.

THE THREE SITES, RETIRED.
1. userinit: the park takes the FIRST PROCESS'S SLOT from the theorem
   instead of a supply.  Shape: forkret's boot arm runs kexec("/init")
   between park and resume, so the slot is an exec-slot piece at the
   OBSERVED image — `∀ av i f nl W', Φo av i (AFile f) -∗ ⌜kexec_loadable
   f⌝ -∗ ⌜kexec_image_ok f … W'⌝ -∗ uslot W'` with `Φo` the observation of
   /init's node (echo: era-0 pins say it is the image's /init, and
   `UkInit`'s program proof supplies `uslot` at that key — L6's
   "exec-site gate at the observed image").  The generic theorem supplies
   it from `app_sup_raw_triv`'s mint.  `SpecUserinit`/`SpecMain`/
   `BootShared`/`SyscParkEnv.park_world` lose `app_sup`.
2. exec's gap: the process's exec deposit COVERS arm (b).  `exec_slot_pre`
   gains the non-loadable-success case (`Fo.(pf_recv) av i a -∗ ⌜¬
   anode_loadable a⌝ -∗ ⌜kexec_ok …⌝ -∗ S W'`, at whatever the landed
   success conjuncts pin); a verified process refutes it from its pin
   (the observed node IS the image's loadable file), a tainted process
   pays it with the generic slot minted from the taint.  `ut_exec_out`'s
   third disjunct and the round's `Hmk` at the exec arm disappear.
3. the pid wrap: the KERNEL FIX (kernel-defects.md, `allocpid` panics on
   wrap) — after it `kfork_post`'s pid arm is `0 < pidv`, the parent
   always resumes on its own arm, and the round's last `Hmk` goes.  Until
   the fix lands the pid-wrap row keeps `app_sup` as a premise of the
   loop, which is the one place a constraining application cannot pay.
Then the loop's `Hmk` premise, `park_world`'s supply row and the
kernel-wide threading are deleted; `Happ_sup` leaves `xv6_app_adequacy`;
`app_triv` keeps `app_sup_raw_triv` for its own mints; `AppEcho` gets
`echo_pred := taint ∨ pins` (`Happ_xfer`: pure ∨ persistent transports;
`Happ_init`: era-0 pins) and the tainted generic slot's supply is
`echo_tag`'s taint arm, delivered through L5-b's console receipt.  ORDER:
after L5-b: (2) exec's arm (b) in the deposit; (1) userinit's slot piece
+ `UkInit`'s slot at the observed image (L6 init); (3) waits on the
kernel fix; then `Happ_sup` goes.  Brief for (2): `brief-armc-execb.md`.
EXEC-B (LANDED 2026-09-09).  Phase-1 facts: `SpecKexec.exec_slot_pre`
is the CONJUNCTION of the loadable wand and the other-success wand
(`Φo av i a -∗ ⌜¬ anode_loadable a⌝ -∗ ⌜exec_key_ok na alen sts W'⌝ -∗
S W'`), `exec_key_ok` being what `kexec_ok` pins about the resume key
(a0 = argc, sp = a1 = `kxc_sp_final`, the stack bounds, `kxc_stack_ok`,
`uvis_fd = sts`, `length tf = TFWORDS`, `na ≤ MAXARG`; nothing about the
image); `kexec_ok_exec_key_ok` closes it.  `exec_post_ok`'s arm (b)
returns `Fs.(pf_recv) (exec_key U' sts na)`; the exec channel
(`sysc_exec_out`/`ut_exec_out`) is two-armed.  ONE (b)-producing site
(`ProofKexec.kxau_close`), not two; `UexecApply`'s round restates the
channel inline, so its two statements lose the third disjunct too.  No
program file names `exec_slot_pre` (all go through `uxsup`).  AS
LANDED: `exec_key_ok` carries no entry point (outside `kexec_loadable`
the epc names a value with no ELF semantics), sp = a1 = `kxc_sp_final`
directly, `na ≤ MAXARG`, `TFWORDS`; `kexec_ok_exec_key_ok`'s one extra
premise is the entry frame's length, which kexec's closer carries; both
dispatcher success arms close by the same two lines; the loop's `Hmk`
has ONE site left, the pid-wrap row (the "third site" was a comment).
STEP (2) OF ARM-c IS DONE: the kernel mints at exec nowhere.

#### THE PINNED EXEC BUNDLE — design for ARM-c (1) and L6's init/sh (2026-09-09)

HOW A VERIFIED PROGRAM DEPOSITS EXEC.  `UkRun.udepw`'s explicit disjunct
is `sbundle uslot USYS_exec (uvis_of_run …)` = `UexecExecInst.exec_sbundle`
= `sys_exec_au_pre (MkPfam uslot R) Γ γfs cw P Pmiss Fo M av sts`: a walk
cursor, the observation piece, the slot piece.  Today every program pays
it from `uxsup` (the supply's generic family, `xv6_sbundle_of_supply`'s
exec branch).  A CONSTRAINING program builds its own:
- THE OBSERVATION reads the pin.  `aopen_commit_at Γ E Φ` fires at mask
  `E = appE = ↑appN`, with the kernel's `ghost_map_auth (γtop Γ) (1/2) I`
  in hand; `γtop (fs_gamma_L γfs) = fs_top γfs` is `app_body`'s authority
  half, so the caller's fupd opens `app_inv`, agrees `I` and reads
  `app_pred app_run (abs_view I)` — for echo `⌜echo_fs_pure av⌝ ∨ taint`
  (pure ∨ persistent) — into its receipt: `Φ av i a := ⌜arow_at av i a⌝ ∗
  (⌜echo_fs_pure av⌝ ∨ taint)`.  With `arow_at av SH_INO a` the pins give
  `a = MkAnode (AFile sh_bytes) 1` and `sh_bytes = ElfUser.sh_elf`
  (`FsShPin.sh_bytes_elf`); likewise `init_bytes = init_elf`.
- THE CURSOR carries the resolved inum ∨ taint at each hop the same way
  (`apath_at av ROOTINO sh_path = Some SH_INO`, `arun …` are pins).
- THE SLOT PIECE answers with the program's kernel-side constructor at
  the kexec'd key: `UShKernel.sh_slot_of_kexec : kexec_image_ok sh_elf na
  alen afun sts W' → … → uslot W'` is the mold (its premises: stack room
  below the argument block, `length sts = NOFILE`, no lowest-closed
  descriptor, the map stops at the break, the payload `R` and `ush_rest`);
  init needs its twin `init_slot_of_kexec` in a new `UInitKernel.v` over
  `UkInitMain.wp_kinit_start` (`init_code`, `init_rodata`, `usz`,
  `ustd_any`, `urun`, and — recursively — init's OWN pinned exec bundle
  for "sh" in place of `uxsup`).  In the taint arm of the receipt the slot
  piece answers with the generic slot minted from the taint
  (`taint ⊢ app_sup` for `echo_pred := taint ∨ pins`).
- A GENERIC LEMMA `pinned_exec_bundle` assembles the three from a pin
  triple (path, inum, bytes) + a `*_slot_of_kexec`; init's and sh's are
  its two instances.
- LOADABILITY OF THE TWO IMAGES IS NOT YET PROVED: no `kexec_loadable
  sh_elf` / `kexec_loadable init_elf` exists.  The pieces do — `ElfUser`'s
  `*_elf_wf`, `*_elf_entry`, `*_elf_segments`; `UShKernel.sh_loads` (two
  phdrs at vaddr 0 and 0x2000, ascending); `KexecImageAlg` has
  `kexec_loadable f <-> kxb_loadable f` (computable) — so each is a
  `vm_compute`-shaped lemma over the dumped bytes.  The pinned slot piece
  needs them twice: to take arm (a)'s wand with `⌜kexec_loadable f⌝`, and
  to REFUTE arm (b)'s `⌜¬ anode_loadable a⌝` once the pin gives `a`.

L6-INIT PHASE 1 (2026-09-09): A and B LANDED in the working tree —
`ElfLoadable.v` (`sh_elf_loadable`, `init_elf_loadable`, the `*_anode_
loadable` forms; a computable `kexec_loadable_b`; 1.8 s), `UInitKernel.v`
(`init_uexec_slot`, `init_slot_of_kexec` on UShKernel's mold, still
taking `uxsup`).  THREE BLOCKERS for C/D, ruled:
1. THE OBSERVED INUM IS UNTIED: `exec_slot_pre`'s wands get `Φo av i a` at
   an arbitrary `i`; the pin speaks of `ino`.  RULED: both wands gain the
   cursor's final position `P L i` as a premise (the proof holds exactly
   one copy, `ProofKexecA.kxa_receipt`); `exec_post_ok`'s success arms
   drop it, the fail arms keep it.
2. THE WALK PREMISE IS OVER EVERY PATH (`namei_walk_pre_era`'s `∀ pl`), so
   a pinned cursor cannot answer hops of another path.  RULED: the exec
   bundle states its walk AT THE ARGUMENT'S STRING — `namei_walk_pre_era_at
   γfs cw pl P Pmiss` guarded by the copyinstr fact about `M` at `av`;
   open/chdir/unlink keep the `∀ pl` form.
3. THE PROCESS'S CWD IS HIDDEN (`urun`'s existential, `udepw`'s `∀ cw`),
   and init execs the RELATIVE "sh".  Design pending: a per-program cwd
   fact carried like `ufd_auth` (stepped by `usys_cwd_ok`) or a pure cwd
   parameter for programs that never chdir.
Also: `app_inv` is kernel-tier (`fsabs_env`), so the pinned bundle is
built in the kernel-side constructor and handed to the program as the
opaque `uxsup`/`udepw`; the claim law must be stated DUPLICATING (the
fire puts the claim back into `app_body`) and the taint must be Timeless
(the later off `app_body`) — echo's `mono_nat_lb_own` is.  `FsAbsPins.v`
does not exist: the pinned-walk vocabulary is `FsAbs.v` §4 (`apr_walk`),
era instance `FsAbsEra.apr_walk_era`.

L6-INIT PHASE 2a LANDED (2026-09-09): blocker 1 — `exec_slot_pre` takes the
walk's terminal cursor `Pfin : Z → iProp` as both wands' first premise
(`exec_au_pre` at `P (length (path_elems pl))`), `exec_post_ok`'s success
arms no longer return it, the fail arms do; blocker 2 — `exec_au_pre`/
`_post_ok`/`_post_fail`/`_arms` are at ONE path `pl` with the walk as
`FsAbsEra.ex_start` (already `namei_walk_pre_era`'s body at one path;
`FsAbsOpenFire.opf_start_of_open` is the ∀-bridge, unusable from
UexecExecInst because of an explicit CurCtx binder — make it a section
variable), and `sys_exec_au_pre` carries the PATH pointer `pv` (argument
0; `av` is argv, argument 1) and owes the walk/slot at paths satisfying
`exec_path_shape` — what `SpecFetchstr.fetchstr_ret` promises, a NUL-
terminated int-sized string with NO tie to the user image.  SO THE
SEMANTIC HALF IS OWED: `exec_path_of M pv pl` (named, beside the shape)
needs a memory-indexed `wp_fetchstr_sconf_mem`/`copyinstr_got`; only then
is the bundle owed at the one string in the process's image, which the
pinned cursor needs.  Blocker 3 RULED: option (2) — the cwd rides the
EXISTING size ghost as a pair (`ghost_var γs (1/2) (sz, cw)` inside
`uheap`, the handle `usz_cwd γs sz c`, `usz` an existential wrapper), the
break's own mechanism; no `urun`/`uheap` argument moves (584 + 36 sites
untouched), ~68 `usz` sites + the sbrk and chdir leaves; `udepw` then
reads `c` in place of `∀ cw`.  Refuted: a cwd filter on `udepw` alone
(nothing at the u-tier pins `cw`).  Remaining lanes, in order:
FETCHSTR-MEM (the reading), CWD-GHOST (option 2), then C+D.

USERINIT AND THE BOOT ARM.  forkret's boot arm kexec("/init") today takes
`exec_au_pre_triv` with the slot predicate `emp` and gets the user WP from
the park closer's FAMILY (minted from the supply).  For a constraining
application the park package carries init's PINNED EXEC BUNDLE instead of
a family (a third mode beside `Wk : option uvis`): the boot arm feeds it
to kexec and the closer's `uslot (uvis_of U' sts)` is exec's arm (a)
receipt `Fs.(pf_recv) (exec_key U' sts na)` (the a0 store makes
`exec_key` the resumed record).  `SpecUserinit`/`SpecMain`/`BootShared`
then take the bundle from the theorem (`Hinit_slot`) in place of
`app_sup`; the generic theorem supplies it from the trivial supply.
`UexecCond.cond_entry_slot`'s decidable gate chain (sync, echo, then the
generic WP) is the mechanism that PICKS a verified program's slot from an
exec'd key; the pinned bundle makes the generic tail unreachable for a
pinned exec (the observed node IS the image's file), which is what lets
the supply leave.  Lanes: L6-INIT (`init_slot_of_kexec`, the pinned
bundle lemma, init's exec of sh), then ARM-c(1) (userinit's bundle mode),
then `Happ_sup` leaves (after EXEC-B and the kernel's pid fix).

## Decisions outstanding (refreshed 2026-09-08)

Everything ruled on 2026-09-07/08 is implemented up to and including the
refund record; the ten syscall folds and R-CONJ are on main.  Still open:

- **ARM (L2-a/L2-b)** — in flight; its phase-0 inventory may surface the
  park-channel question (fd-row-pilot §6 item 3) as a real decision.
- **L5** — the rx wand's TAG output and the console ledger (the design
  sketch is under "The two options for the generic slot's supply"); the
  console READ arm's receipt is where the tag reaches sh.
- **L6** — fork's real row LANDED (three lanes, above); init's `wait(0)`
  null-window row; echo's own bundles (its pins as
  cursor/receipt families; the exec slot wand answered from
  `kexec_image_ok`).
- **Q4** stays provisional (`echo_pred := taint ∨ pins`).
- Hygiene backlog (above) after ARM.
