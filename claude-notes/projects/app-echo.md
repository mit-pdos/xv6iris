# Project: the ECHO application — `echo hello world` end to end, file system unmodified

Design of record: [`../design/applications.md`](../design/applications.md).
This file is what is LEFT to make `AppEcho` an instance of
`App.xv6_app_adequacy`, in execution order.  The scaffold itself — the
record, the theorem, the client counter, the conditional invariant, the
license, the era mint — is landed (see the top banner of `iris/App.v`).

## The target statement

At the real image, powered off, never booted: for every run,

    disc κs -> good_out κs /\ pristine (v_disk g2)

where `disc` says every `ObsUartIn` byte of every power cycle so far is a
prefix of `(echo hello world\n)*`, `good_out` says every cycle's
`ObsUartOut` bytes are a prefix of the expected console stream for that
cycle's inputs, and `pristine dk` says the committed map `dk` recovers to
has the mkfs image's abstract view (so init, sh and echo are the image's
binaries at every reboot).

## Lanes (design §5), with what each unblocks

- [ ] **L2 — per-process license.**  The returning-ecall arm's persistent
  give `app_lic`, the dispatcher's write-kind fires taking it, the
  generic slot at `tainted -∗ □ uexec_wp`.  Unblocks: every non-generic
  `Happ_lic`.  Gate: none.  Shape: `fd-row-pilot.md` §2's deposit
  disjunct at a persistent payload; `UexecRetExec.uexecXG` for the
  ambient class.
- [ ] **L3 — every mover fires.**  mkdir, link, iput-free on AU forms
  whose fires re-sync the copy; the `ftop_body` tie half.  Unblocks:
  `⌜fsc_app I⌝` meaning the file system.  Gate: none; it is
  `fs-syscall-specs.md`'s remaining lanes.
- [ ] **L4 — the crash predicate's application conjunct.**  Unblocks:
  `Happ_swap`, hence `Happ_boot` at a non-pristine boot, hence the
  `pristine` half of `app_phi`.  Gate: L3 (the collection reads the copy).
- [ ] **L5 — console input tie.**  Unblocks: sh minting `tainted` at the
  point it leaves the discipline; hence L2's last step and L6's sh.
  Gate: none (console.c is proven; the ledger is new).
- [ ] **L6 — the programs.**  init and sh on the Uk engine with licensed
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
- `echo_R γcl h := mono_nat_auth_own γcl 1 (if decide (disc h) then 0 else 1)`
  with `echo_R_alloc` (`HR0`), `echo_R_pow` (`Hpow`), `echo_R_tx`,
  `echo_R_rx` (the two UART arms, as basic updates over the ledger alone —
  the theorem's wands frame the UART ghosts around them) and
  `echo_R_untainted` (`disc h` and `client_lb 1` contradict: what the end
  of the run reads).
- `echo_fs I := era0_pins (abs_view I) /\ era0_sh_pins (abs_view I)` (the
  /init and /sh binaries are the image's, path and content; per inum, not
  a whole-map equality) and `echo_fs_era0` (`Happ_boot` at era 0, off
  `FsInitPinBoot.era0_recovery_pins` / `FsShPin.era0_recovery_sh_pins`).

Not there, on purpose: a theorem.  `Happ_lic` is payable only from
`tainted` until L2; `Hlend`/`Happ_boot` at a non-pristine boot need L4;
`Hphi` needs both and L7.  A theorem taking those as hypotheses would be
the GAP-premise trap (`durable-notes.md`).  Echo's own pin (`/echo`'s
inum and bytes, `FsShPin`'s shape) joins `echo_fs` with L6.
