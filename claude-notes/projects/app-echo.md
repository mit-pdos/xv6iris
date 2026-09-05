# Project: the ECHO application — `echo hello world` end to end, file system unmodified

Design of record: [`../design/applications.md`](../design/applications.md).
This file is what is LEFT to make `AppEcho` an instance of
`App.xv6_app_adequacy`, in execution order.  The scaffold itself — the
record, the theorem, the two-instance claim (running in `app_inv`, durable
in the crash slot), the transport, the birth step, the era mint — is
landed (rounds A/C/D0 of `app-instances.md`, 2026-09-05; the top banner
of `iris/App.v`).

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

- [ ] **L2 — the step moves to the process.**  The returning-ecall arm's
  persistent give carrying `app_step`, the AU fires taking it from there,
  the generic slot at `taint -∗ □ uexec_wp`.  Unblocks: every non-generic
  step.  Gate: L3 (a site still on `_auto` is paid era-wide by `app_auto`,
  which only the generic application has).  Shape: `fd-row-pilot.md` §2's
  deposit disjunct at a persistent payload; `UexecRetExec.uexecXG` for
  the ambient class.
- [ ] **L3 — round E of `app-instances.md`** (kernel side, application-
  independent).  Every `ireg_top_retag_auto` site becomes `_same` (view
  unchanged) or `_step` (paid from an AU contract's `app_step`); link,
  mkdir and `iput`'s free move onto AU forms with their deltas
  (`fs-syscall-specs.md` §4); then `top_move`, the `_auto` movers and
  `Happ_auto` are deleted.  Gate: none.
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
