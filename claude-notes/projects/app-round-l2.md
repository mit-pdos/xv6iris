# Lane L2 — the step moves to the process: PROPOSAL (2026-09-07, after round E2 closed)

STATUS: PROPOSAL, awaiting the owner's rulings (Q1-Q4 at the end).  Written read-only against
origin/main at round E2's close (E2-Z landed: every view move on a dispatched path is an AU fire
paid with `app_step`, or a `_same` between absent rows; `top_move`/the `_auto` movers are gone).
Design of record it refines: `design/applications.md` §1-§2 (the mover `app_step`, "supplied by
whoever moves the map — the syscall proof, which gets it from the process's payload (lane L2)"),
`design/user-wp-slot.md` (the ruled trap contract, part (A)), `design/fd-row-pilot.md` §2 (the
seam ruling: route (a), the deposit disjunct).  Worklist entry: `app-echo.md` L2.

## 1. What is left of the license, and why echo cannot pay it

`App.xv6_app_adequacy` takes `Happ_auto : ⊢ app_auto_raw (app_pred A c) r` (App.v ~171): the
application's claim survives EVERY one-row move of the map.  It is parked in `app_inv` at the era
mint and spent at exactly one place: the dispatcher's `_unit` dischargers (`FsAbsInvFire.fsabs_*`,
`SpecCreate.cre_commits_unit`, `SpecSysLink.link_commits_unit`, `fw_app_write_step_acc`, …), which
build every AU contract's commit bundle at the `True` receipt families by paying each commit's
`app_step` off `app_auto` (`AppInv.app_step_acc`/`app_step_acc_view`/`app_step_of_auto`).  The
kernel therefore never proves anything about the application; the application promises
everything.  The generic application (`app_triv`) pays by `app_auto_raw_triv`.  Echo's predicate
`echo_fs av := ⌜era0_pins av /\ era0_sh_pins av⌝` (AppEcho.v) cannot: a blanket move may rewrite
`/init`'s inum.  So `Happ_auto` is the one hypothesis that keeps `AppEcho` from being an instance.

The AU contracts already carry everything a per-syscall discharge needs: each commit's premise
spells the pre-view facts and the delta (`cre_pre` + `delta_create d nm i c`, `delta_arm i c`,
`delta_link_tgt t a`, `delta_unl_ent`/`delta_unl_tgt`, `delta_write i off bs`, `delta_trunc`, …;
E2-D's `fs_delta` is their disjunction), and phase 1 hands back the caller's `app_step` AT that
delta.  What is missing is the channel by which the process ISSUING the syscall, which knows the
call and its arguments, supplies those steps instead of the era-wide license.

## 2. The proposal, in four pieces

### (i) The give: a persistent, per-call promise (pure vocabulary `sys_delta`)

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
this is why L2 is cheaper than the fd-row pilot's deposit (§3 below): nothing linear crosses.

### (ii) The channel: the ecall arm of `uexec_ret` carries the give

`UexecRet.uexec_ret_F`'s generic ecall arm (UexecRet.v ~539-600) becomes

    app_give P n W ∗ (∀ r M' π' szv' fdv' cw', ⌜usys_mem_ok …⌝ -∗ ⌜usys_fd_ok …⌝ -∗ … -∗ X (bump …))

with `P` the application's predicate reached through the ambient class the slot already has
(`UexecRetExec.uexecXG`'s pattern: a class so the return former's cone gains no fs imports —
the give mentions only `aview`/`fs_node` maps and `FsAbsDelta`, which sit below).  The process
picks nothing: every process proves the give for every ecall it issues.  The generic inhabitant
`UexecRet.uexec_wp_uslot : □ uexec_wp -∗ uslot W` gains the premise `app_give_any P` (it cannot
know which calls the unverified program makes); `UexecCond.cond_entry_slot` likewise.  For
`app_triv` both are free (`app_auto_raw_triv`).

### (iii) The kernel side: dischargers off the give, `Happ_auto` deleted

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

### (iv) Echo's side: the taint pays the generic give

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

## 3. Why not the fd-row pilot's deposit disjunct as the whole channel

`fd-row-pilot.md` §2 routes a LINEAR mirror half through the trap (`mcur γm u` in, stepped `u'`
out) so the process LEARNS the syscall's effect (the console pilot's `r3 = 0`).  L2 needs the
opposite direction only: the process PROMISES.  A persistent give crosses without a return leg,
needs no `uenr_dom` disjunction (every process supplies it; the generic one supplies the blanket
form), no mirror joins in the loop, and no parking generalization (§6's third ask) — the payload
is persistent, so the park's fixpoint is untouched.  The two are complementary and the pilot's
route (a) can land later on top: its enriched disjunct would carry the mirror half BESIDE the give.

## 4. Cost and staging (each stage a green gate)

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

## 5. Questions for the owner

- Q1. THE GIVE IS PERSISTENT AND PER-CALL (§2(i)), not the AU bundle itself (route (a) with
  receipts).  Agree?  (The receipts are the fd-row pilot's business; L2 pays steps only.)
- Q2. `Happ_auto` LEAVES the system theorem (§2(iii)) — a statement change to
  `SystemAdequacy.xv6_power_adequacy_gen`'s hypotheses (the audited fs statement is untouched).
  The alternative keeps it as the generic slot's premise only (no theorem change; the license
  survives as a resource the generic inhabitant consumes).  Recommendation: delete — a hypothesis
  nobody can discharge except the trivial application is the GAP-premise trap in a milder form.
- Q3. `sys_delta`'s resolution of paths: the table names the parent/last-element the AU walks
  resolve (`apath_at` at the process's `cwd`).  Under concurrency the view may change between
  the give and the fire, so the table must be stated at the FIRE-TIME view (the commit's `I`),
  which is what §2(i) does (`abs_view I` is the commit's).  A give stated at the trap-time view
  would be unsound.  Confirm the fire-time reading.
- Q4. Echo's predicate gains the taint disjunct (§2(iv)); `app_pred`'s type stays
  `app_names -> aview -> iProp` (the taint witness lives in `app_fixed`'s gname).  Agree?
