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

## CHECKPOINT — 2026-08-16, handoff

Read this section first; it is written for whoever picks the splice up next.
It separates **what is verified**, **what is in flight**, and **what is
guessed**, because some of the numbers below are measured and some are not.

### Git state

- **`main` = `9ca5ba0a`, clean and GREEN** (all 1120 iris files). Everything in
  "What is done" below is on it and pushed.
- **Branch `panic-kvmmap-wip` is RED.** It holds the one-site conversion
  described under "The worked example". Its last full build failed with two
  errors; four of its files were edited afterwards and never compiled. Details
  in "In flight" below. Do not merge it without building it.
- A branch called `panic-splice` existed and was **deleted on purpose**: it
  contained `PanicCred.v`, an approach the user rejected. See "Rejected".

### What is DONE and verified (on `main`)

1. **`acquire`'s `if(holding(lk)) panic("acquire")` arm is dead code.** The
   lock invariant's held state keeps `lk_in i s` beside `lk->cpu`, so a hart
   whose held set omits `s` cannot be the holder; `holding()` provably returns
   0. Cost to callers: nothing — `s ∉ lks` is acquire's own premise and the
   held-set authority is already inside `cpu_own`. This is what freed the
   credential from most of the tree.
2. **The printk cone needs no panic credential at all** — printk, printint,
   consputc, uartputc_sync, and `SpecPanic` itself. The
   `panic → printk → acquire → panic` cycle that this file planned to close by
   Löb dissolved when acquire's arm was refuted. `LinkPrintk` no longer reaches
   `LinkPanicStub`.
3. **`pr` = 16 and `uart` = 17** in `LockRank.v` — above `itable` (14) and
   `ftable` (15). `SpecPanic` demands `locks_below lks "pr"` and `iget` panics
   holding itable. Verified green with no other file changing.
4. **The inventory is TEN functions**, not the nineteen an earlier count
   suggested. `panic_wp_any_at` marks *credential conversion*, not a panic
   jump; nine files were feeding printk (xv6's `ialloc` is
   `printf(...); return 0;`). Those conversions are deleted. The ten that
   actually `jal panic`, by grep for `mword_of_int KernelSyms.panic`:
   **bread, ilock, iget, dirlookup, dirlink, fileread, filewriteParts, kexit
   (TWO arms), kexecB2, kvmmap**.
5. Spec files still threading `PanicStub`: **75**, down from 104. Every one of
   them feeds one of those ten.

### The DESIGN, as directed by the user (do not re-litigate)

- **A panic site links against `SpecPanic` like any other callee.** Its proof
  functor takes `(Panic : PANIC)`, its Link file passes `Panic`. There is to be
  **no repackaging of panic's WP into a credential**.
- **The call site supplies explicitly**: the 52-slot stack budget, `cpu_own`
  (with `n+2 < 2^31` and `locks_below lks "pr"`), `kernel_text`/`kernel_data`,
  `pc_is`, and the message descriptor.
- **The call site does NOT reason about `panic_env` or `uart_sent_sub`** — the
  user's explicit instruction. Plan agreed in conversation, NOT yet implemented:
  - **`uart_sent_sub` comes out of the invariant.** It is already persistent
    (`uart_sent γ l = own (un_acc) (◯ML l)`, a mono-list lower bound), and its
    authority `uart_sent_auth` already lives inside `dev_inv`'s body
    (`WpUart.dev_inv_body` → `uart_ghosts`). `WpUart.v:409`
    (`uart_sent_auth γ u -∗ uart_sent_auth γ u ∗ uart_sent γ (uart_acc u)`)
    hands out a snapshot with no update. So
    `dev_inv γ γv ={↑uartN}=∗ uart_sent_sub γ []` should be provable, and
    **`SpecPanic` can drop both the `bs` parameter and the `uart_sent_sub`
    premise**: panic has no postcondition, so it never reports what it sent;
    `ProofPanic` mints `[]` for itself before its first printk call.
    *Not proved yet — the ingredients are checked, the proof is not written,
    and the mask side conditions are NOT verified.*
  - **`panic_env`'s four ghost names get existentially quantified** —
    `∃ γpr γl γd γv, panic_env γpr γl γd γv`, one nameless persistent token in
    the slot `panic_wp_any` occupies today, so none of the 75 specs gains a
    parameter. The user was offered the alternative of globalizing the console
    names in a class (like `GenId` fixes `gen_id`) and **has not chosen**;
    assume the existential unless told otherwise.
- **Obligations that belong to a conditional failure arm go ON that arm.** See
  the kvmmap example below: its panic arm is guarded by `on = None`, and every
  live caller is at `Some`, so putting the stack/interrupt/environment premises
  inside the `None` branch cost the callers nothing.

### What `panic_env` contains (asked and answered)

Three persistent credentials, no ownership:

| | |
|---|---|
| `is_lock γpr pk_pr_lock "pr" emp` | pr.lock at `KernelSyms.pr`. Resource is **`emp`** (`SpecPrintk.pr_res`): it protects no separation-logic state, only output interleaving. From `printkinit`. |
| `dev_inv γd γv` | `uart_inv ∗ plic_inv ∗ disk_inv ∗ perm_inv`. `uart_inv` is `inv uartN` over a body holding `uart_frag u ∗ uart_ghosts γ u ∗ …` — **including `uart_sent_auth`**, which is what makes the derivation above possible. |
| `is_txlock γl γd` | `is_lock γl a_tx_lock "uart" (tx_res γd) ∗ uart_dlab_off γd`. From `uartinit`. |

### The WORKED EXAMPLE: kvmmap (on branch `panic-kvmmap-wip`)

`ProofKvmmap.vo` **compiles**. The recipe, which the other nine arms should
follow:

1. `SpecKvmmap`: the `None` arm became
   `⌜54 <= K⌝ ∗ ⌜lvl+2 < 2^31⌝ ∗ kernel_data ∗ ∃ γpr γu γv, printk_env γpr γu γv`.
   (`printk_env` was used rather than `panic_env` because it also carries
   `uart_sent_sub γ []` — once the derivation above lands, `panic_env` is
   enough.) The section gained `!uartGhostG Σ, !diskGhostG Σ`.
2. `ProofKvmmap`: functor is `KvmmapProof (Mappages : MAPPAGES) (Panic : PANIC)`;
   message lemmas hoisted as NAMED pure lemmas (`kvmmap_msg`, `_addr`,
   `_above`, `_nonul`, `_nz`, `_bytes`), never inline `ltac:`
   (optimization.md); the arm destructs the bundle, mints the string with
   `KernelDataInv.kernel_data_string`, transports `cpu_own` to the panic hart,
   and applies `Panic.wp_panic_sconf`.
3. `LinkKvmmap`: `Module Kvmmap := KvmmapProof Mappages Panic.`

**Three traps this hit, all of which will recur:**

- **`cpu_own` must be at the panic hart.** The arm sits several `b`-generic
  instructions past the last transport; `cpu_own_transport CID9 CIDd …` was
  needed. Getting the SOURCE hart wrong gives "iSpecialize: cannot instantiate
  … with (cpu_own …)" — which reads like an ordering bug and is not.
- **`Import` is not transitive.** `uartGhostG`/`diskGhostG` must be reachable
  as INSTANCES in each file's own section: `Require Import DiskPtsto WpUart`
  explicitly. Reaching them through `SpecPrintk` leaves the section variables
  ungeneralized and the lemma statement with unresolved `?Σ` ("Could not find
  an instance for ?riscvGS0 : riscvGS ?Σ").
- **panic's noff headroom is `n+2`, not `n+1`** (pr.lock, then tx_lock under
  it), so a spec whose premise is `+1` has to be raised.

### IN FLIGHT — exactly where it stopped

On `panic-kvmmap-wip`:

- `SpecKvmmap.v`, `ProofKvmmap.v`, `LinkKvmmap.v` — converted; `ProofKvmmap.vo`
  built successfully.
- The last **full** build of that state: `MAKEEXIT=2`, two errors, both the
  ungeneralized-`Σ` trap, at `ProofKvmmake.v:932` (its `Hypothesis wp_kvmmap`)
  and `ProofProcMapstacks.v:804` (its kvmmap application).
- `ProofKvmmake.v`, `ProofProcMapstacks.v`, `SpecKvmmake.v`,
  `SpecProcMapstacks.v` were then edited to add
  `!uartGhostG Σ, !diskGhostG Σ` to their class binders (3, 1, 2, 2 sites
  respectively) plus explicit `Require Import DiskPtsto WpUart`.
  **THESE FOUR WERE NEVER COMPILED.** That is the immediate next thing to run.

### What is NOT known

- Whether that four-file class propagation compiles, and whether it stops
  there or keeps propagating up the kvm chain.
- Whether the `dev_inv ⇒ uart_sent_sub []` derivation goes through — in
  particular whether the masks work where `ProofPanic` would mint it.
- **The stack ripple, which is the biggest unknown.** `panic_stack = 52` must
  hold AT the panic point. Measured only for kvmmap (`K-2` there, so
  `54 <= K`). `K_bread` = 40, `K_ilock` = 44, `K_iget` = 16, `K_dirlookup` = 90
  today. Raising them pushes the requirement into every caller's budget, and
  nobody has checked that the deep chains (usertrap → syscall → … → bread)
  still fit the 512-slot kernel stack. If some chain does not fit, that is a
  REAL finding about the kernel, not a proof artifact.
- Whether any of the other nine arms are guarded the way kvmmap's is (so their
  obligations can sit on the arm and cost callers nothing). kvmmap's was; the
  others were not examined.
- Whether the two `kexit` arms differ from each other.

### Message addresses (extracted from the kernel image, reusable)

`objdump -s -j .rodata xv6-riscv/kernel/kernel` and search; these are already
confirmed:

| message | address |
|---|---|
| `bget: no buffers` | `0x800073c0` |
| `ilock` | `0x80007468` |
| `ilock: no type` | `0x80007470` |
| `iget: no inodes` | `0x80007430` |
| `dirlookup not DIR` | `0x800074c0` |
| `dirlookup read` | `0x800074d8` |
| `dirlink read` | `0x800074e8` |
| `fileread` | `0x80007598` |
| `filewrite` | `0x800075a8` |
| `kvmmap` | `0x80007118` |
| `init exiting` | `0x80007200` |

The bytes lemma is `do (len+1) (destruct j …); vm_compute in Hj; discriminate`
— see `ProofIalloc.ia_msg_bytes` or the kvmmap one for the exact shape.

### REJECTED — do not rebuild

`PanicCred.v` / `LinkPanicCred.v`: a persistent, hart-generic `panic_cred` that
wrapped panic's real contract in the stub's shape, so the 75 specs could keep
threading one opaque token. It worked (`panic_cred_holds` was PROVED from
`Panic.wp_panic_sconf` and `printk_env`), but the user rejected it: it
duplicates `SpecPanic` and hides the very premises the splice exists to expose.
Sites link against `SpecPanic`. The lesson worth keeping from it: `printk_env`
IS `panic_env` plus an existential `γl` — pr.lock's resource is `emp` on both
sides and the addresses are the same `KernelSyms.pr`.

### Build commands

Full build (~10 min):

```
./gcp-rocq/run-on-gcp --sync-only
./gcp-rocq/run-on-gcp --no-sync bash -c 'cd /mnt/rocq/trees/_shared_xv6iris-6 &&
  setsid nohup bash -c "make -k proofs > /mnt/rocq/build-xv6iris-6.log 2>&1;
  echo MAKEEXIT=\$? >> /mnt/rocq/build-xv6iris-6.log" >/dev/null 2>&1 </dev/null &'
```

**Single file (4–60 s — use this while iterating, it is the difference between
a 10-minute and a 30-second cycle):**

```
./gcp-rocq/run-on-gcp --no-sync bash -c 'cd /mnt/rocq/trees/_shared_xv6iris-6/iris &&
  opam exec --switch=/shared/xv6rocq -- make -f CoqMakefile ProofFoo.vo'
```

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
