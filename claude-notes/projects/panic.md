# Project: panic()

`panic()` is PROVEN — `SpecPanic.v` / `CodePanic.v` / `ProofPanic.v` /
`LinkPanic.v`, sealed as `PanicProof Printk : PANIC`, `Print Assumptions` = the
5 Sail platform externs + funext and nothing else.  What is left is the
SPLICE: moving the 169 files that still thread the placeholder credential
(`PanicStub.v`) over to the real contract.

## The contract

No postcondition — panic's last instruction is a self-jump, so the contract is
a bare `WP Loop` and a caller that reaches panic has discharged its own goal.
That half was always right and is inherited from the placeholder.

Everything in the PRECONDITION is forced by the two `printk` calls, which are
ordinary calls with `SpecPrintk.PRINTK`:

- **the message** — `a0` is the vararg of a `"%s"` directive, so it is a
  `pk_arg_desc` of kind `PkStr` (`PkAStr dq s`, consumed; or `PkANull`).
  Every xv6 panic site passes a `.rodata` literal, so the site discharges it
  with `KernelDataInv.kernel_data_string` out of `kernel_data`;
- **`panic_stack = 52`** — panic's own 4 slots over `printk_stack = 48`;
- **`cpu_own n eb p C b`** (consumed, never returned) plus printk's
  `n + 2 < 2^31`.  Unlike printk's, panic's `n` is arbitrary: a panic arm is
  normally reached with locks already held;
- **`panic_env γpr γl γd γv`** — pr.lock's `is_lock` (resource `emp`),
  `dev_inv`, `is_txlock`, bundled so a site threads ONE hypothesis; plus a
  `uart_sent_sub γd bs`, which printk threads in as well as out.

**Why the placeholder is not derivable and the real one is not optional.**
`PanicStub.panic_wp` asks for the machine capability and nothing else, so it
claims panic is safe at an arbitrary `a0` (printk would read a string nobody
owns) and at an arbitrary stack budget (the frame push would run off the
stack).  It is an `Axiom` because it cannot be proved, not because nobody got
to it.

## The proof

Fourteen instructions.  The only two things worth knowing:

- **the self-jump is proved by Löb, HART-GENERICALLY.**  `wp_cj_s_sconf` hands
  its continuation back UNDER A LATER (a backward jump is a loop back edge),
  and that later is exactly what discharges the induction hypothesis; with no
  postcondition there is nothing else to establish.  `ProofSpin.wp_spin` is the
  M-mode twin.  Hart-generic because with interrupts on the spin can be
  trapped and resumed elsewhere, so the IH has to hold at every hart:
  `pn_spin` quantifies `h` INSIDE the Löb, outside any `CpuId` section.
- **`Loop` NAMES THE HART.**  `Notation Loop := (LoopE gen_id cpu_id)`, so a
  statement that quantifies a hart for a `WP Loop` must bind it as
  `(h : CpuId)`, not as `(h : CPU)`; with a bare `CPU` the body does not
  elaborate at all (`Could not find an instance for "CpuId"`, reported at
  `Loop`).  This is the counterexample to reading durable-notes' "`WP e` is
  hart-free" as "`WP Loop` is hart-free" — the WP former is, the expression
  is not.

The message survives the first call because gcc parks it in `s1`:
`callee_saved` carries `s1` across `printk("panic: ")` and `c.mv a1,s1` makes
it the `"%s"` vararg of the second call.

## Where the splice stands (2026-08-15)

`PanicStub` is down from 104 spec files to 75, and what is left is a
**ten-function inventory**, not a tree-wide sweep.

**Done, on `main`:**

- **`acquire`'s arm is refuted**, not discharged — the lock invariant's held
  state keeps `lk_in i s` beside `lk->cpu`, so a hart whose held set omits `s`
  cannot be the owner. That is what freed ~everything: acquire is called from
  nearly every function in the tree.
- **The printk cone needs no credential at all.** `SpecPanic`'s own
  `panic_wp_any` premise existed for printk's inner `acquire(&tx_lock)`; with
  acquire's arm gone, printk, printint, consputc and uartputc_sync all drop it
  and panic's contract is self-contained. **The `panic → printk → acquire →
  panic` cycle never had to be closed by Löb.**
- **`pr` and `uart` are at the top of the lock order** (16, 17). `SpecPanic`
  demands `locks_below lks "pr"`, and `iget` panics holding `itable` (14).
- Nine files' `panic_wp_any_at` was feeding **printk**, not a panic — xv6's
  `ialloc` is `printf(...); return 0;`. Those are deleted.

**The real inventory — ten functions with a `jal panic` of their own:**
bread, ilock, iget, dirlookup, dirlink, fileread, filewrite, kexit (two arms),
kexec's B2, kvmmap.

**On branch `panic-splice`** (not green — one of ten arms spliced):

- `PanicCred.v` — `panic_cred`, the real contract packaged the way the stub
  was: persistent, hart-generic, no postcondition. `kernel_data` rides inside
  (a .rodata message is minted from it by `panic_cred_msg`), and it mentions
  **no console typeclasses**, so the 140 files that thread it keep their
  ambient context. `panic_go` is the application form.
- `LinkPanicCred.v` — `panic_cred_holds`, **proved** from
  `Panic.wp_panic_sconf` and `SpecPrintk.printk_env`. `printk_env` *is*
  `panic_env` plus an existential `γl`.
- 228 premises across 140 files renamed to it; `ProofKvmmap` spliced.

**What each remaining arm costs:** its own message lemmas (string, address,
`_bytes` by `vm_compute` — the addresses are in `.rodata`, e.g. `bget: no
buffers` at `0x800073c0`), a `cpu_own_transport` to the panic hart, and a
stack floor of `panic_stack = 52` at the panic point — `K_bread` 40,
`K_ilock` 44, `K_iget` 16 all have to rise, and that ripples into callers'
budgets. Then the root moves off the bridge: `boot_shared_alloc` cannot use
`panic_cred_holds` (it runs before `consoleinit`), so the root belongs in
main, where `printk_env` is in hand — and then `PanicStub.v` /
`LinkPanicStub.v` go.

## Panics that are UNREACHABLE rather than threaded

Two of the four are already retired at the source, which is the cheaper end of
the splice — a site that cannot reach `panic` needs no credential at all:

- **`sched`'s all four** — `panic("sched locks")` and the three
  `unreachable()` checks. `SpecSched` has ONE contract now, at `cpu_own 1`,
  and it takes no `panic_wp_any`
  ([`iput-acquiresleep.md`](iput-acquiresleep.md)). `SpecSched.v` and
  `ProofSched.v` dropped their `Require Import PanicStub` outright, so two
  files left the 433-file closure and `sched` is off the splice list.
- **`acquire`'s "acquire"** — planned, from the `lk->cpu` disjointness the
  held set already carries; see [`../completed/lock-set.md`](../completed/lock-set.md).
  That one is the big win, and it should land BEFORE the splice below.

## What is LEFT: the splice

169 files `Require` `PanicStub.v` and thread `panic_wp` / `panic_wp_any`
(433 transitively depend on it).  Retiring it means, per site: change the
premise to `SpecPanic`'s contract and, at the actual panic arm, supply the
message literal, `cpu_own`, `panic_env` and a `uart_sent_sub`.

**The cost is not in panic — it is in acquire.**  The arms bottom out at
`panic("acquire")`, `panic("release")` and friends, so acquire's precondition
would gain printk's whole environment and every caller of acquire would have
to thread it.  That is the sweep, and it is why the placeholder is still here.

Two things fall out of it for free when it happens:

- `LinkPanicStub.v` and its `Axiom` go away;
- panic's own proof stops taking `panic_wp_any` as a premise and closes by
  **Löb**: printk's precondition then asks for panic's real contract, `iLöb`
  supplies it under a later, and panic pushes its frame before it calls
  printk — so there is a step to strip the later on.

## Layering note (do not undo)

`SpecPanic.v` must sit BELOW `SpecPrintk.v` (printk's spec asks for a panic
credential), so the caller-side printk vocabulary it needs —
`pk_arg_desc` / `pk_desc_kind` / `pk_desc_res` / `pk_vararg` / `pk_pr_lock` —
lives in **`PrintkArgs.v`**, and `SpecPrintk.v` `Require Export`s it so
nothing that reached those names through SpecPrintk had to change.
`pk_desc_res` lost its vacuous `CpuId` parameter in the move (a string
points-to is memory, which is shared).

Keeping the real contract in `SpecPanic.v` rather than bolting it onto the
placeholder's file is also a BUILD constraint, not taste: the placeholder is
in 433 files' dependency closure, of which 330 do not otherwise reach
`UartTxInv` and 354 do not reach `PrintkFmt`.
