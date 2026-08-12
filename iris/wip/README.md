# `iris/wip/` — not part of the build

Files here are deliberately **not** in `iris/_CoqProject`: they do not compile,
and the coverage report (`tools/proof_coverage.py`) is keyed off `_CoqProject`
rather than a `*.v` glob, so nothing they claim is ever counted. Anything that
lands moves back up to `iris/` and gets a `_CoqProject` entry in the same
change.

## `ProofUartwrite.v` / `LinkUartwrite.v`

The definitional layer of a re-proof of `uartwrite` against xv6 `ae96fd0`,
which rewrote the transmit path (see
[`../../claude-notes/projects/uart-driver.md`](../../claude-notes/projects/uart-driver.md)
and [`../../claude-notes/projects/sleep-split.md`](../../claude-notes/projects/sleep-split.md)).
`SpecUartwrite.v` is written, compiling and believed right; what is missing is
the proof BODY — `uw_tail`, `uw_one`, `uw_iter`, `wp_uartwrite_sconf` and the
`Module UartwriteProof`. The file's closing `PROOF PLAN` comment carries the
full instruction table, the register roles, the frame-slot map and the
per-callee premise lists, all checked against `kernel.asm`; read it before
starting.

Meanwhile `iris/LinkUartwrite.v` (in the build) supplies the contract with an
`Axiom`, in the tree's usual shape for an unproven callee. Proving uartwrite
means replacing that file with the real functor instantiation —

```coq
Require Import LinkAcquiresleep LinkReleasesleep LinkSleep LinkSleepPrepare
        LinkUart ProofUartwrite.
Module Uartwrite := UartwriteProof Acquiresleep Releasesleep Sleep SleepPrepare Uart.
```

— moving `ProofUartwrite.v` back up to `iris/`, and adding it to
`_CoqProject`. Nothing else changes.

The separate `iris/LinkTxLockInit.v` axiom is **not** yours to retire: it is
`kernel-defects.md` D2 (upstream never initializes `tx_lock`), and it stays
whether or not uartwrite is proved.
