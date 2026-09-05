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

The pure data: `disc`, `echo_line`, the image's abstract view `echo_av0`
and `echo_fs`, the record `echo_app` at `app_lend := ⌜pristine⌝ ∨
tainted`, `echo_R` with the counter at `if decide (disc h) then 0 else 1`,
and the obligations that are provable WITHOUT any lane: `HR0`, `HRt`,
`Hpow`, `Hrx` (the counter's step), `Happ_boot` at era 0 (the image's
map is `echo_av0`, off `FsInitPinBoot`'s route).  No theorem is stated
for the application: `Htx`, `Happ_lic`, `Happ_swap` and `Hphi` are the
lanes' outputs, and a theorem taking them as hypotheses would be the
GAP-premise trap (`durable-notes.md`).
