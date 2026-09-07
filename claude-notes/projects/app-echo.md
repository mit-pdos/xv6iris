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

- [ ] **L2 — the step moves to the process.**  Proposal below (a persistent
  per-call give on the ecall arm, dischargers off it, `Happ_auto` deleted,
  echo's taint disjunct); its four questions await the owner.  The returning-ecall arm's
  persistent give carrying `app_step`, the AU fires taking it from there,
  the generic slot at `taint -∗ □ uexec_wp`; then `app_auto`/`app_auto_raw`/
  `Happ_auto`/`app_step_of_auto`/`app_step_acc` — the era-wide blanket
  promise the GENERIC dischargers still pay every AU fire's step with, and
  which only the generic application can pay — are deleted.  Unblocks: every
  non-generic step.  Gate: none (L3 landed).  Shape: `fd-row-pilot.md` §2's
  deposit disjunct at a persistent payload; `UexecRetExec.uexecXG` for
  the ambient class.
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

## The L2 proposal (awaiting the owner's rulings; questions at the end)

#### (i) The give: a persistent, per-call promise (pure vocabulary `sys_delta`)

    sys_delta (n : Z) (tf : list (mword 64)) (fdv : list fdstate) (cw : Z)
              (av : aview) (i : Z) (av' : aview) : Prop
      -- "syscall n, issued with trapframe words tf from fd table fdv and cwd cw, may move row i
          of the view av to av'": the per-syscall table over FsAbsDelta's vocabulary, e.g.
          mknod: ∃ d nm c j, av' = delta_arm j c av ∨ av' = delta_unarm j av ∨ av' = delta_create d nm j c av
                 with (d, nm) the path's parent/last element resolved in av from cw (the AU walk's
                 `apath_at`/`mknod_parent_elems` vocabulary, SpecSysMknodAU) and c = ADev (a1) (a2);
          write:  ∃ off bs, av' = delta_write i off bs av, i the inum of fdv !! a0 (FdInode i _);
          read/fstat/chdir/dup/close/exit/…: av' = av;  exec: av' = av (reads only);
          unlink/link/open(O_CREATE|O_TRUNC)/mkdir: their deltas at the resolved path.

    app_give (P : aview -> iProp) (n : Z) (W : uvis) : iProp :=
      □ ∀ I i av', ⌜sys_delta n (uvis_tf W) (uvis_fd W) (uvis_cwd W) (abs_view I) i av'⌝ -∗
                   app_step_P P i I av'
    app_give_any P := □ ∀ I i av', app_step_P P i I av'          -- = app_auto_raw's body

(`app_step_P` is `AppInv.app_step` with the predicate a parameter instead of `app_pred app_run`,
so a process file below the kernel proofs can state it; `app_step` is its instance.)  PERSISTENT,
so the kernel may fire it as many times as the syscall retags, and no "return" leg is needed —
this is why L2 is cheaper than the fd-row pilot's deposit (below): nothing linear crosses.

#### (ii) The channel: the ecall arm of `uexec_ret` carries the give

`UexecRet.uexec_ret_F`'s generic ecall arm (UexecRet.v ~539-600) becomes

    app_give P n W ∗ (∀ r M' π' szv' fdv' cw', ⌜usys_mem_ok …⌝ -∗ ⌜usys_fd_ok …⌝ -∗ … -∗ X (bump …))

with `P` the application's predicate reached through the ambient class the slot already has
(`UexecRetExec.uexecXG`'s pattern: a class so the return former's cone gains no fs imports —
the give mentions only `aview`/`fs_node` maps and `FsAbsDelta`, which sit below).  The process
picks nothing: every process proves the give for every ecall it issues.  The generic inhabitant
`UexecRet.uexec_wp_uslot : □ uexec_wp -∗ uslot W` gains the premise `app_give_any P` (it cannot
know which calls the unverified program makes); `UexecCond.cond_entry_slot` likewise.  For
`app_triv` both are free (`app_auto_raw_triv`).

#### (iii) The kernel side: dischargers off the give, `Happ_auto` deleted

The trap loop already carries the ecall's `uexec_ret` to the dispatcher (milestone J's shape:
`ProofUsertrapSys` holds the slot bundle `uslot_x (uvis_of U sts)`; `ProofSyscall.sysc_arm_pre`).
The dispatcher's fs arms today read `FirstTok.fsabs_env = app_inv` off `syscall_env` and pay with
the license.  After L2 each arm reads `app_give (app_pred app_run) n W` off the payload and uses
NEW dischargers `fsabs_*_pre_give : app_give P n W -∗ ⌜n = USYS_x⌝ -∗ <bundle at the True
families>` — one per dispatched fs syscall (mknod, open create/plain, unlink, link, mkdir, write
inode, chdir, exec; read is read-kind and owes nothing) — each proved by showing that every
commit's step the contract can demand is `sys_delta n …`-shaped at the row the commit's premise
names.  That is the substance of the lane: ~10 lemmas of the shape `fsabs_mknod_pre_era` but
with the delta obligation discharged from the table instead of the blanket.  Then `app_inv`
keeps only the half authority and the claim (`app_auto` is no longer parked in it),
`AppInv.app_auto`/`app_auto_raw`/`app_step_of_auto`/`app_step_acc(_view)` are deleted, and
`Happ_auto` leaves `xv6_app_adequacy` and `xv6_power_adequacy_gen` (SystemAdequacy — the ONE
statement change the round makes; the fs adequacy statement is untouched).

#### (iv) Echo's side: the taint pays the generic give

Echo's programs are enriched (they prove `app_give echo_fs n W` per call — init's mknod/open of
the console, sh's exec/fork/wait/read/write, echo's write: every one is either `av' = av` or a
create at a fresh inum under `/`, which preserves the per-inum pins; ONE lemma
`echo_fs_sys_delta : ∀ n tf fdv cw av i av', sys_delta … -> echo_fs_pure av -> echo_fs_pure av'`
for the deltas those calls can make, since the pins name inums 1 and 2's rows and `/`'s entries
only by lookup).  After the taint (input leaves the discipline) a process runs the generic slot,
which needs `app_give_any`; so echo's predicate becomes

    echo_pred γ av := mono_nat_lb_own γ 1 ∨ ⌜echo_fs_pure av⌝

— once tainted, the witness is persistent and re-establishes the claim at any view (the "echo
pays by taint" of round E2's notes, made exact).  `Happ_xfer`/`Happ_init` are unaffected (a
disjunction of a persistent and a pure claim duplicates; era 0 is the right disjunct).  The
taint-to-generic handoff `taint -∗ app_give_any echo_pred` is the "generic slot at
`taint -∗ □ uexec_wp`" app-echo.md names.

#### Why not the fd-row pilot's deposit disjunct as the whole channel

`fd-row-pilot.md` §2 routes a LINEAR mirror half through the trap (`mcur γm u` in, stepped `u'`
out) so the process LEARNS the syscall's effect (the console pilot's `r3 = 0`).  L2 needs the
opposite direction only: the process PROMISES.  A persistent give crosses without a return leg,
needs no `uenr_dom` disjunction (every process supplies it; the generic one supplies the blanket
form), no mirror joins in the loop, and no parking generalization (§6's third ask) — the payload
is persistent, so the park's fixpoint is untouched.  The two are complementary and the pilot's
route (a) can land later on top: its enriched disjunct would carry the mirror half BESIDE the give.

#### Cost and staging (each stage a green gate)

- L2-a (pure + slot side, kernel untouched): `sys_delta` (FsAbsDelta or a new `FsSysDelta.v`
  below UexecRet's cone), `app_step_P`/`app_give`/`app_give_any` (a new `AppGive.v` below
  UexecRet), the class hook, the arm change in `uexec_ret_F`, `uexec_wp_uslot`/`cond_entry_slot`
  with the `app_give_any` premise, the Uk engine's ecall leaves gaining the give obligation
  (`UkStep`/`UkSync`/`UkFork`/`UkInit`… — each verified program proves its gives; sync's are all
  `av' = av`).  Ripple: everything above `UexecRet` that builds a slot (~the Uk files, the three
  mint sites' generic inhabitants).  Sizing before the brief: `grep -l "uexec_ret\|uslot" iris/*.v`.
- L2-b (kernel side): the dispatcher's arms take the give from the trap's payload (find where
  `ProofUsertrapSys` hands the ecall's `uexec_ret` to `ProofSyscall` — the `sysc_arm_pre`
  bundle's slot component), the `fsabs_*_pre_give` dischargers, `app_inv` without the license,
  `Happ_auto` deleted from App.v/SystemAdequacy.v (statement change: owner sign-off), the
  AppInv deletions.
- L2-c (echo): `echo_pred` with the taint disjunct, `echo_fs_sys_delta`, the three programs'
  gives (lands with L6's program proofs; L2 only states the shape).

#### Questions for the owner

- Q1. THE GIVE IS PERSISTENT AND PER-CALL , not the AU bundle itself (route (a) with
  receipts).  Agree?  (The receipts are the fd-row pilot's business; L2 pays steps only.)
- Q2. `Happ_auto` LEAVES the system theorem  — a statement change to
  `SystemAdequacy.xv6_power_adequacy_gen`'s hypotheses (the audited fs statement is untouched).
  The alternative keeps it as the generic slot's premise only (no theorem change; the license
  survives as a resource the generic inhabitant consumes).  Recommendation: delete — a hypothesis
  nobody can discharge except the trivial application is the GAP-premise trap in a milder form.
- Q3. `sys_delta`'s resolution of paths: the table names the parent/last-element the AU walks
  resolve (`apath_at` at the process's `cwd`).  Under concurrency the view may change between
  the give and the fire, so the table must be stated at the FIRE-TIME view (the commit's `I`),
  which is what the give does (`abs_view I` is the commit's).  A give stated at the trap-time view
  would be unsound.  Confirm the fire-time reading.
- Q4. Echo's predicate gains the taint disjunct ; `app_pred`'s type stays
  `app_names -> aview -> iProp` (the taint witness lives in `app_fixed`'s gname).  Agree?
