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

Three commits landed: `507b7e60` (stack budgets), `801d6d30` (existential
ghost names), `1f1b328d` (**dirlink — the first call site off the
placeholder**).  All pushed, tree GREEN (`MAKEEXIT=0`).

FOURTEEN arms left, at nine functions.  Next up, in this order, because they
are the only ones whose callers pay nothing: **filewrite** (1 arm),
**sys_unlink** (3 arms, all in `ProofSysUnlinkTails.v` at `CID3`, but its three
`su_panic_*` helpers carry no `cpu_own`/`kernel_data` so those must be threaded
in from the caller).  Then the remaining seven, which need `kernel_data` and
`panic_env` threaded from boot.

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

### THE BUNDLE SHAPE — DECIDED: (A) FULLY EXISTENTIAL, and implemented

`panic_env` is `∃ γpr γl γd γv, panic_env_at γpr γl γd γv`.  A site threads ONE
nameless persistent token; no spec below panic gains a parameter.  Landed at
`801d6d30`; the reasoning is in `SpecPanic.v`'s own header, in full, so it does
not have to be re-derived.  Two independent legs:

- **Logically it is ∃-elimination, not a weakening.**  With `uart_sent_sub`
  gone, all four names occur EXACTLY ONCE in `wp_panic_sconf_body` — inside
  that one conjunct — and none occurs in the conclusion (a bare `WP Loop`).
  This is precisely what is NOT true of `SpecConsoleintr.console_caps`, which
  binds its two lock names but keeps `γu` a parameter because its `γu` occurs
  again in the contract proper.  **The rule: a ghost name may be existentially
  bound iff it occurs nowhere else in the statement.**
- **Physically a caller cannot supply a bogus console.**  `lock_inv γ lk s R`
  contains `lock_word lk v`, the lock word itself, so γpr/γl are pinned by the
  addresses the definition already names; `dev_inv`'s body holds `uart_frag u`,
  the ghost half of the PHYSICAL device state paired with `uart_auth` inside
  `state_interp`, so at most one (γd, γv) can have a live `dev_inv`.

What the names are, since that is what the choice turned on: γpr and γl key
nothing but their own lock's held-state ghost (pr.lock's resource is `emp`;
tx_lock's is `tx_res γd`, keyed by γd and NOT by γl).  γd is the only one
indexing real resources (`uart_tx_own`, `uart_sent`, `uart_dlab_off`).  γv is
baggage — panic touches nothing disk, and it rides along only because
`dev_inv` bundles all four devices.

### THE RECIPE — proven on dirlink (`1f1b328d`), follow it verbatim

**Pick the next site by RIPPLE, not by order.**  Only three of the ten already
carry `kernel_data` AND `printk_env`, so only those three cost their callers
nothing: **dirlink (done), filewrite (1 arm), sys_unlink (3 arms)**.  The other
seven have neither and need both threaded from boot — bread alone has fifteen
callers.  Do the cheap three first.

`SpecPrintk.printk_env_panic : printk_env γpr γd γv -∗ panic_env` is what makes
them cheap: printk_env IS panic_env plus an existential γl and the trace
witness (`pr_res` is `emp`; both name the same `KernelSyms.pr`).  No cycle —
SpecPanic sits below SpecPrintk and does not require it back.

Per site: functor gains `(PN : PANIC)`, Link passes `Panic`, message lemmas
hoisted as NAMED pure lemmas (optimization.md), and the arm becomes an
ordinary application.  **LEAVE the now-unused `panic_wp_any` premise in the
spec** — dropping it is a separate 163-file sweep, and the arm conversion is
green without it.

**FOUR TRAPS, all of which recur at every remaining arm:**

1. **THE REGFILE THE SPEC WANTS IS THE POST-JAL ONE.**  `wp_jal_s_sconf`
   returns `sie_cap_gpr (<[Regidx rd := regval_into_reg (add_vec_int pc 4)]> m)
   n b p`, so passing the regfile posed BEFORE the jump makes the unifier grind
   on `PB2 =?= <[Rra := _]> PB2` — which cannot succeed — and `iSpecialize`
   NEVER RETURNS.  Every arm reaches panic through a `jal`, so every arm has
   this.  The placeholder hid it: `panic_wp` inferred `m` from `Hcg`.  Pose the
   post-jal file and pass that.
2. **PROVE a0's VALUE DIRECTLY ON THE POST-JAL FILE WITH `pcw`**, and state it
   in the goal's `!!!` form.  Deriving it across the `ra` write with
   `rewrite upd_ne` cost 100s in the tactic and another 110s at `Qed`;
   `by pcw` costs nothing.  And `rget f r` is a DEFINITION, so `rewrite` cannot
   match it against `f !!! Regidx (mword_of_int 10)` however convertible.
3. **NO INLINE `ltac:` IN THE APPLICATION.**  `lia` with a bitvector anywhere
   in the context is the documented search-forever case, and `lkbelow` against
   an evar-valued `lks` is worse.  Pass `lks` EXPLICITLY and discharge every
   side condition with a closed lemma over plain nat/Z/gset
   (`dl_panic_K`, `dl_panic_noff`, `dl_panic_below`, `dl_msg_nz`).
4. **`nonul` IS AMBIGUOUS in the fs cone** — `DirentEnc`'s is over
   `list (bv 8)`, `PrintkFmt`'s over `string`.  Qualify it.  And `Require
   Import` is not transitive: `SpecPrintk` must be imported explicitly for
   `printk_env_panic`, even where the contract already mentions `printk_env`.

The shape, from `ProofDirlink.v`:

```coq
pose (PB3 := <[Regidx Rra := regval_into_reg
                (add_vec_int (mword_of_int (DK + 0x68) : mword 64) 4)]> PB2).
assert (Ha0msg3 : PB3 !!! Regidx Ra0 = (mword_of_int dl_msg_a : mword 64)) by pcw.
iPoseProof (dl_msg_str with "Hkd") as "#Hstr".
iPoseProof (printk_env_panic with "Hpk") as "#Hpenv".
iDestruct (cpu_own_transport CIDrd CIDpa4 0%nat eb (proc_addr j) b
             ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
iApply (PN.wp_panic_sconf (CID := CIDpa4) PB3 (K - 10)%nat
          0%nat eb b (proc_addr j) (PkAStr DfracDiscarded dl_msg) lks
          (dl_panic_K K HK) eq_refl dl_panic_noff (dl_panic_below lks Hbelow)
          with "Hcg Hcnt Htext Hkd Hpc Hpenv [Hstr]").
{ rewrite /pk_desc_res Ha0msg3.
  iSplit; [iPureIntro; exact dl_msg_nonul|].
  iSplit; [iPureIntro; exact dl_msg_nz|]. iExact "Hstr". }
```

Cost when done right: **0.4s** (48.6s against a 48.2s baseline for the file).

### HOW TO PROFILE ONE OF THESE — do this BEFORE changing anything

A wrong arm does not fail, it HANGS, and an unbounded compile teaches nothing.

```
timeout 260 coqc -time ... Foo.v          # hard cap, per-statement timings
Timeout 25 <tactic>.                       # Rocq combinator, bounds ONE step
```

Bisect with `Timeout` (split `iApply` into `iPoseProof` + per-hypothesis
`iSpecialize`) and each run finishes in ~2 minutes naming the exact offender.
Get the TRUE baseline by timing the unmodified HEAD version of the same file —
the checked-in `.v.timing` files are stale (dirlink's said 130s; the real
figure was 48s).  **I changed three things before profiling and two of them
were real defects that were not the cause; the third became the new
bottleneck.  Profile first.**

### Message addresses AND BYTE COUNTS (measured; reusable)

`riscv64-linux-gnu-objdump -d` the kernel and follow each `jal <panic>` back to
its `addi a0,a0,..` annotation.  The byte count is what the
`do N (destruct j …)` in each `*_msg_bytes` lemma needs (length + 1 for NUL).

| function | address | bytes | message |
|---|---|---|---|
| bread | `0x800073c0` | 17 | `bget: no buffers` |
| iget | `0x80007430` | 16 | `iget: no inodes` |
| ilock | `0x80007468` | 6 | `ilock` |
| ilock | `0x80007470` | 15 | `ilock: no type` |
| dirlookup | `0x800074c0` | 18 | `dirlookup not DIR` |
| dirlookup | `0x800074d8` | 15 | `dirlookup read` |
| dirlink | `0x800074e8` | 13 | `dirlink read` (DONE) |
| fileread | `0x80007598` | 9 | `fileread` |
| filewrite | `0x800075a8` | 10 | `filewrite` |
| kexit | `0x80007200` | 13 | `init exiting` |
| kexit | `0x80007210` | 12 | `zombie exit` |
| kexec | `0x800075c0` | 30 | `loadseg: address should exist` |
| sys_unlink | `0x800075f0` | 18 | `unlink: nlink < 1` |
| sys_unlink | `0x80007608` | 18 | `isdirempty: readi` |
| sys_unlink | `0x80007620` | 15 | `unlink: writei` |

The bytes lemma: prefer `ProofIalloc.ia_msg_bytes`' form
(`vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity`) over
`ProofPanic`'s `vm_compute in Hj |- *; congruence`.

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
