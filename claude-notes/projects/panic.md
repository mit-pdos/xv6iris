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
  `dev_inv`, `is_txlock`, bundled so a site threads ONE hypothesis.
  **NOT a `uart_sent_sub`, and not a `bs`** — printk threads that claim in as
  well as out, but the input slot only feeds the OUTPUT, and panic has no
  postcondition.  See the checkpoint below and `SpecPanic.v`'s header.

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

## CHECKPOINT — 2026-08-16, after the budget landing

### Git state

`main` = the commit this note lands in, GREEN (`MAKEEXIT=0`, 1159 files, a
`make -n` dry run schedules nothing).  Rebased onto `19cc4717`.

**Branch `panic-kvmmap-wip` is SUPERSEDED — delete it, do not rebase it.**
`main` retired kvmmap's panic arm by a better route at `be67d08a`: `SpecKvmmap`
became COUNTED-ONLY (`exists nb, on = Some nb /\ pt_missing t vpn0 npages < nb`
as an unconditional premise), so the `on = None` arm is excluded outright.
`ProofKvmmap` has no `PanicStub` and `LinkKvmmap` is back to
`KvmmapProof Mappages`.  The branch's approach — keep the `None` arm live and
hang panic's obligations on it — would REGRESS that.  Its patch, if ever
wanted: it was one commit, `e36e9a43`, on the pre-`9ca5ba0a` base.

### DONE in this pass

1. **panic's contract lost its `bs` parameter and its `uart_sent_sub`
   premise.**  See `SpecPanic.v`'s header for the argument; the short form is
   that printk's `uart_sent_sub` slot is an ACCUMULATOR FOR A POSTCONDITION
   (`bs` in, `bs ++ cs` out, `bs` never inspected) and panic has no
   postcondition, so the premise had no purpose.  `ProofPanic` mints its own
   with the new `UartTxInv.uart_sent_sub_nil_free`.
2. **`uart_sent_sub γ []` is FREE FROM NOTHING** — no `dev_inv`, no invariant,
   no mask, no allocated authority, at an arbitrary `γ`.  `uart_sent γ l` is
   `own γ.(un_acc) (◯ML l)` and `◯ML [] = ε` (`mono_list_lb_nil_is_unit`), so
   `own_unit` hands it over under a plain `|==>`.  This is STRONGER than the
   route the previous checkpoint planned (through `dev_inv` + `WpUart.v:409`,
   with mask side conditions unverified); those side conditions never needed
   checking.
3. **The stack budgets now cover panic.**  See the next section.
4. **The budget constants are `Notation`, not `Definition`** — see below.

Panic's seal is unchanged: `Print Assumptions Panic.wp_panic_sconf` = funext +
the 5 Sail platform externs.

### THE STACK BUDGETS NOW COVER panic (this was the big unknown)

Every `K_*` in the tree used to be the panic-FREE depth — that is what
`PanicStub` bought, since its `panic_wp` asks for no stack at all.  Validated
against the kernel image (`riscv64-linux-gnu-objdump`, max-depth over the call
graph, cutting the `swtch`/`scheduler` cycle): `printk` 48, `readi` 78,
`dirlookup` 90, `sys_exec` 234 — each matching its constant exactly.

**IT FITS.  Peak is now `K_usertrap` = 342 against `boot_stack_depth` = 512.**
No kernel defect.  Two things pulled it past the naive figure:

- **`forkret`'s `if (first)` branch** is budgeted even though `SpecForkret`
  currently excludes it (discarded-cell premise).  Deliberate — the user's
  instruction was to budget for the eventual fully-proven state.
  `K_forkret` is `6 + K_kexec` = 190 now; `prepare_return` no longer dominates.
- **`syscall()` dispatches INDIRECTLY through `syscalls[]`**, so no static
  `jal` edge exists for any of the 22 `sys_*`.  `K_syscall` was `4 + K_sys_exit`
  = 82, covering ONE syscall; it is `4 + K_sys_exec` = 248 now, and
  `K_usertrap` (whose formula already carries `kv_frame_slots`) follows.
- `kv_frame_slots` 78 -> 90, forced by `SpecKerneltrap.kt_carve_fits`
  (`32 + kerneltrap_stack <= kv_frame_slots`).  It is a derived reserve, not a
  hardware constant.  `boot_stack_slots K_main` 180 -> 214.

**Method note, worth keeping.**  Computing the ripple as a DELTA between two
fixpoints of a disassembly model and adding it to the spec values DOES NOT
COMPOSE — it under-delivers wherever the model's baseline disagreed with the
spec (caught by `ProofEndOp`).  What works is an ABSOLUTE monotone fixpoint
seeded at the current spec values, fed by both the constraints the proofs state
outright (`(K_f <= K)%nat -> (K_g <= K - n)%nat`) and the static call edges.
Frames from the prologues are reliable — they match the `K - n` the proofs
name.  Baseline DEPTHS are not, because of indirect dispatch.

### BUDGET CONSTANTS ARE NOW `Notation`, NOT `Definition`

102 of them, as `Notation X := (e) (only parsing).`  There is nothing to
unfold, so `lia` sees the literals and no proof has to know which callee
dominates a derived budget.  This removed 423 `unfold` tactics and 16
ssreflect `rewrite /X` sites.  Three traps, all of which will recur if more are
added:

- **A `Notation` inside a `Section` does NOT survive its `End`.**
  `kv_frame_slots` (IntrDefs) and `K_kvmmake` (KvmSpec) had to be hoisted above
  their `Section` line.
- **The `: nat` ascription is gone, so a bare numeral parses in the ambient
  scope.**  `K_proc_pagetable := 3` came out as `Z`.  Every body needs `%nat`.
- **`rewrite /X` is ssreflect's unfold** and fails with the baffling
  "The term S is not unfoldable" once `X` is a numeral.

Cost accepted: `only parsing` means goals display `58`, not `K_bread`.

### THE REAL DEFECT CLASS: literals that encode another constant's value

Six build rounds (13 -> 4 -> 16 -> 8 -> 4 -> 1 -> 0 errors), and after the
first every single failure was the same thing: **a numeral written into a
proof that silently encoded some other constant's then-current value.**  None
is findable by grepping for the constant's name, because the name never
appears.

| site | literal | what it meant |
|---|---|---|
| `ProofMain.mn_bounds` + 4 `mn_grp_*` | `50 <= n` | `K_userinit` |
| `ProofKexit.kx_rest` | `60 <= av` | `K_iput` |
| `SpecPipealloc` | `74 <= K` | `6 + fileclose_stack` |
| `ProofSysPipe.sp_bounds` | `74 <= av - 8` | pipealloc's budget |
| `ProofKernelvec` (x3) | `46 + av` | `kv_frame_slots - 32` |
| `ProofConsoleread` (x4), `ProofPiperead` | `trap_res true = 78` | `kv_frame_slots` |
| `ProofCreateParts.cr_K_value` | `K_create = 114` | itself |
| `BootBridge.boot_stack_slots_main` | `= 180` | `2 + kv_frame_slots + K_main` |

Where the referenced constant was in scope it is now NAMED (`K_end_op` in
ProofKexit, `K_userinit` in ProofMain).  Where it was not — `SpecPipealloc`
reaches `SpecFileclose` only in prose, and pulling that cone in for one numeral
is the worse trade — the literal stays with the derivation in the comment.
**The `Notation` change does not fix this class.  A bare literal is still a
bare literal.**

Also note `fileclose_stack`'s dominating callee FLIPPED: it was `8 + K_iput`,
it is `8 + K_end_op` now (76 > 72).

### THE PANIC-SITE CENSUS (from the image, with proof status)

`unreachable(char *)` IS NOT `panic(char *)`.  It is
`addi sp,sp,-16; ...; sb zero,0(0xe000000); j .` — **2 slots**, a byte store to
the QEMU test device, no printk, and it never reads its argument.  Budgeting it
like panic would inflate `mappages`/`walk`/`uvmunmap`/`kerneltrap`/`usertrap`
for paths no proof can take.

61 static sites: **36 `panic()`, 25 `unreachable()`.**  All 25 `unreachable()`
are refuted.  Of the 36:

- **15 LIVE, at TEN functions** — bread, iget, ilock (x2), dirlookup (x2),
  dirlink, fileread, filewrite, kexit (x2), kexec, **sys_unlink (x3)**.
  `sys_unlink` was NOT on the previous checkpoint's list.  It costs the budget
  nothing (frame 30, needs 82, `K_sys_unlink` was already 134).
- **21 refuted** — acquire, release, sched, bmap, bfree, brelse, bwrite,
  iunlock, fsinit, forkret, free_desc (x2), sleep_prepare, kvmmap,
  virtio_disk_init (x6), virtio_disk_intr.

**CAUTION on that "refuted" column.**  It is not uniform, and the previous
version of this note got two wrong.  `SpecFsinit.v:81` says its magic test is
"A LIVE ARM, AND IT IS AN IMAGE PREMISE" — refuted only by assuming
`sb_magic (sb_image ...) = FSMAGIC`, i.e. that mkfs wrote the magic; a bogus
superblock reaches it.  `forkret`'s `panic("exec")` is not refuted at all — the
whole `if (first)` branch is excluded by `first_addr ↦₄{DfracDiscarded} 0`, and
`SpecForkret` says outright that proving it "needs a one-shot ghost that
nothing carries yet".  The useful axis is not dead/live but **does the
refuting hypothesis get discharged by real callers, or does it survive as an
assumption?**

### STILL OPEN — the bundle shape (USER DECISION, not yet made)

The nine/ten sites cannot be converted until this is settled.  After the `bs`
removal, all four names in `panic_env γpr γl γd γv` occur EXACTLY ONCE in
`wp_panic_sconf_body` — inside that one persistent conjunct — and none occurs
in the conclusion (a bare `WP Loop`).  So

    (∀ γ⃗, panic_env γ⃗ -∗ WP Loop)  ≡  ((∃ γ⃗, panic_env γ⃗) -∗ WP Loop)

is ∃-elimination: **the fully-existential form is LOSSLESS here, provably.**
That is NOT true of `SpecConsoleintr.console_caps`, which is the hybrid shape
(existential `γtx`/`γc`, parameter `γu`) precisely because its `γu` occurs
elsewhere.  The rule: *a ghost name can be existentially bound iff it occurs
nowhere else in the statement.*

Options: **(A) fully existential** (recommended), **(B) hybrid à la
`console_caps`** — costs only `iget`, since 8 of 9 sites already carry
`γd`/`γv` — or **(C) a global `ConsoleNames` class**.  (C) is worse than it
looks: a class makes the INDEX implicit but not the RESOURCE free (the site
still supplies `dev_inv`), while adding a binder to every section plus the
"Import is not transitive" instance trap.  The `GenId` analogy does not carry —
`gen_id` is consumed by the `Loop` notation in every WP in the tree.

Good news for whichever is chosen: **the class ripple is small.** 8 of 9 spec
files already have `!uartGhostG Σ, !diskGhostG Σ`; only `SpecIget`/`ProofIget`
(diskGhostG but not uartGhostG) and `ProofFilewriteParts` need propagation.
kvmmap was painful because it sits in the device-free kvm/boot cone; the fs
cone already has the device.

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

A site that cannot reach `panic` needs no credential at all, and this is the
cheaper end of the splice.  The full census (61 sites, which are `panic()` and
which the 2-slot `unreachable()`, and the proof status of each) is in the
checkpoint above; these two are the ones that shaped the design:

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

163 files `Require` `PanicStub.v` and thread `panic_wp` / `panic_wp_any`.
Retiring it means, per site: change the premise to `SpecPanic`'s contract and,
at the actual panic arm, supply the message literal, `cpu_own` (at the PANIC
HART — see the transport trap below) and the `panic_env` bundle.  No
`uart_sent_sub`, and the stack budget is already there.

**The cost is NOT in acquire, and that is the change since this file was
written.** The plan of record feared acquire's precondition would gain printk's
whole environment and ripple to every caller.  `acquire`'s arm is REFUTED now,
so the printk cone asks for no panic credential at all and the cycle never has
to be closed by Löb.  What is left is the ten functions with a live arm, listed
in the checkpoint.

Blocked on one thing only: the bundle-shape decision (A/B/C in the checkpoint).

`LinkPanicStub.v` and its `Axiom` go away when the last of the ten lands;
`Print Assumptions` on adequacy currently still shows
`LinkPanicStub.PanicAssumed.panic_wp_holds` (and `LinkUserinit.Userinit.wp_userinit_sconf`).

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
