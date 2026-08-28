# The INTR lane — executing §0.39′ (the kernelvec handler contract)

Worklist for the interrupt-side lane of the real-Ztso flip.  Workspace:
`/shared/xv6iris-3-intrtree` (a full copy of the fliptree at the certified r22
boundary).  Owner ruling under execution: `tso-port.md` §0.39′ — the kernelvec
handler contract becomes CONTEXT-DEPENDENT, proven once at boot, usable only by
a context whose bound dominates the credential's publication stamp.

Sibling lanes and their notes: `tso-machine-flip.md` (A-series, lock lane),
`tso-kpt-lane.md` (K-series).  Nothing here duplicates those; the files this
lane touches are `IntrDefs`, `SpecDevintr`, `SpecKernelvec`, `ProofKernelvec`,
`ProofDevintr` and the immediate interrupt cone.

---

## I0. Baseline, certified

Sentinel-backed, this tree, remote build (`ZZintrbuild.sh`, per-subtree
`coq_makefile`, `-j180 -k`):

```
SUBEXIT[model-xv6iris]=0  SUBEXIT[kernel-rocq]=0  SUBEXIT[user-rocq]=0
MAKEEXIT=2       GREEN=1100/1296
```

Primary RED set (9), as the coordinator's brief gives it, all present:
`ProofForkretPark, ProofKernelvec, ProofMain, ProofSwtch, ProofVirtioDiskIntr,
ProofVirtioDiskRwD, UptWalkPt, UserMemPt, WpSconfLock`.  Everything else in the
196-file not-green list is cascade (the `Link*` tier, `ProofUser*`,
`ProofAcquire/Release/Holding`, the virtio Rw chain, `BootChain/BootShared/
SystemAdequacy`).  `ProofUsertrap` and `ProofMainSecondary` are GREEN.

**DISK CAVEAT, and it cost an hour — record it.**  The `.vo` shipped in this
tree copy are STALE with respect to the `.v`: `About is_lock` against them
reports NO `CurCtx` argument, which contradicts `WpLock.v:1102` as it stands.
Rocq does not check `.v`/`.vo` correspondence, so a local `coqc` probe against
the shipped artifacts answers questions about a DIFFERENT tree.  Every
measurement below was re-taken against artifacts pulled off the VM
(`run-on-gcp --pull-vo`) after a green build of these sources.

---

## I1. The failure is ONE site, and it is exactly §0.39′'s subject

`ProofKernelvec.v:1704`, the only error the build reports for the file
(coqc stops at the first, so nothing downstream of it has been checked yet):

```
Error: Tactic failure: iSpecialize: cannot instantiate
(devintr_caps γu γv γdk γtl γs pd pav pu -∗ … -∗ WP Loop)%I
with (devintr_caps γu γv γdk γtl γs pd pav pu).
```

The two `devintr_caps` print identically and differ only in the implicit
`CurCtx`.  `kernelvec_handler_spec` is proven at the boot context `XI`; under
`intr_handler_spec_intro`'s `□ ∀ (XIc : CurCtx)` it must call
`Kerneltrap.wp_kerneltrap_sconf (XI := XIc)`, whose premise is
`devintr_caps (XI := XIc)`.  Every other tactic in the file went through.

---

## I2. What the contract's shape would have to be (design, arity-preserving)

Worked out before the refutation below, and recorded because it survives it —
this is the spelling §0.39′ wants, and it moves NO arity and NO consumer:

* `intr_handler_spec kt handler := ∃ T, ctx_floor cur_ctx T ∗ ihs kt cpu_id handler T`
  — the contract itself becomes the context-dependent object (which is what
  §0.39′ says it is), and its ARITY does not move.
* `ihs` gains a `nat` stamp index; `ihs_body_of kt R T handler` gains the
  premise `ctx_floor ξb T` inside its existing `□ ∀ (XIb : CurCtx) …`.
* `ires_of S c` gains the matching `∃ T`, under the SAME `▷` (nat is
  inhabited, so `▷ ∃` commutes with `∃ ▷`).  Then
  `intr_res kt = ∃ h b, ⌜…⌝ ∗ ⌜…⌝ ∗ ghost ∗ stvec ↦ᵣ h ∗ ▷ intr_handler_spec kt h`
  is UNCHANGED TEXT, `intr_res_intro` is UNCHANGED, and so are its NINE call
  sites across six files (`WpSconfCsr` ×3, `WpIntrInv` ×2, `WpSconfSret`,
  `ProofMain`, `ProofMainSecondary`, `UsertrapRes`) and the eight
  `rewrite /intr_res` destructure sites (those three files plus
  `ProofPrepareReturn` and `ProofKernelvec` ×2) — every one of them passes the
  contract through as `▷ intr_handler_spec kt h` and never names its internals.
* `intr_handler_spec_apply`'s STATEMENT is unchanged (it destructs the `∃ T`
  and feeds the floor itself), so `WpIntrInv` needs no edit; only
  `intr_handler_spec_intro` grows the `T` + floor arguments, and its only user
  is `ProofKernelvec`.
* `SpecKernelvec.KERNELVEC` is UNCHANGED — the producer derives the stamp and
  the floor FROM THE CREDENTIAL, so `ProofMain`/`ProofMainSecondary` (both
  forbidden to this lane) do not move.

That last point is what makes the design admissible at all: the boot-side
`ctx_floor cur_ctx T` is free, because `T` is the MAXIMUM of the handles' own
floors and a max over a finite family is ATTAINED — no `own_context`, which
matters because under the `□` no exclusive resource survives.

Known cascade of this design, NOT taken here: `intr_res` becomes
context-dependent, so wherever the enabled arm crosses contexts (swtch's
`sie_cap` exchange, the `trap_csrs` park record) the floor must be
re-established at the new context.  Both sites are in the lock lane's already
red `ProofSwtch` / park cone, and the payment there is the ordinary
0.35′(iii) absorb at the resumer's `p->lock` AMO.

---

## I3. LANDED: the relocation kit (`SpecDevintr.v`, section `CapsFresh`)

Proven and compiling.  Seven exported constants:

```coq
cfresh   T P    := □ ∀ ξ : CtxId, ctx_floor ξ T -∗ P ξ
freshpack ξ P   := ∃ T : nat, ctx_floor ξ T ∗ cfresh T P
freshpack_here / _mono / _pair / _const
freshpack_is_lock    (ξa : CtxId) γ lk s R :
    is_lock (XI := ξa) γ lk s R -∗ freshpack ξa (λ ζ, is_lock (XI := ζ) γ lk s R)
freshpack_big_sepL   (the indexed big-op, by induction on the list)
```

`freshpack_is_lock` is the load-bearing one and it is SHORT for a measured
reason: **`lock_inv` and `lock_name` take no `CurCtx`** (measured, fresh `.vo`),
so the only ξ in `is_lock` is `lk_floor cur_ctx lo`, and §0.38′'s two arms
relocate differently and NEITHER DOWNGRADES:

* LEFT arm (`ctx_floor ξa lo`) — the handle's own stamp is `lo`; a target that
  has passed `lo` gets the LEFT arm back;
* RIGHT arm (`llb loglen_name lo`) — already context-free, rides to any target
  at stamp 0 and the target keeps the same arm.

A laundering `left → right` is also derivable (`own_context ξ` +
`own_context_floor_view` + `view_lb_llb` + `llb_le`) and was REJECTED, not
used: it would mint right-arm-only handles at arbitrary contexts, and
§0.35′(iv) case 1 (`holding()`'s lock-free read of `lk->cpu`, which precedes
acquire's AMO) discharges against the LEFT arm.  §0.38′ says the right arm's
only resting holder is the creator before its first AMO; manufacturing more of
them would break the one read that has no AMO in front of it.

---

## I4. REFUTATION BY MEASUREMENT: §0.39′ is not executable on this tree, and the blocker is §0.28′(1), not freshness

**The finding.**  A freshness premise cannot produce `devintr_caps` at the
consumer's ξ, because the mismatch between `devintr_caps ξ` and
`devintr_caps ζ` is not a FLOOR mismatch — it is an IDENTITY mismatch in the
lock payloads.  Measured with `Set Printing Implicit. Print procs_inv.`
against fresh artifacts:

```
procs_inv XI γs =
  ⌜length γs = NPROC⌝ ∗
  ([∗ list] i ↦ γl ∈ γs,
     is_lock XI γl (proc_addr i) proc-the-string
       <{ proc_lock_res … XI γs γl (proc_addr i) }>) ∗
  ([∗ list] i ↦ _ ∈ γs, ∃ ks, is_kstack XI (proc_addr i) ks)
```

The payload is embedded at the SAME `XI` the handle is stated at, by
`const_pay` (`<{ }>`), whose own header says so: *"P is elaborated as the
combinator's ARGUMENT — outside any CurCtx-typed binder — so its ambient facts
always bind the caller's context"*.  `R` is a PARAMETER of `lock_inv`, so
`procs_inv ξ` and `procs_inv ζ` are handles to two DIFFERENT Iris invariants.
No premise about ζ's bound can bridge that.

**Per-member measurement of `devintr_caps` (fresh `.vo`, `About`):**

| member | takes `CurCtx`? | why | relocatable today |
|---|---|---|---|
| `dev_inv γu γv` | no | four Iris `inv`s | YES (const) |
| `console_caps γu` | YES | `is_conslock`'s payload `cons_res` is ξ-indexed and const-embedded; the `is_txlock`/`tx_res` half is CLEAN (no `CurCtx`) | NO |
| `disk_geom γv pd pav pu` | YES | three `↦₈□` = `ctx_word_pointsto ξ` CLEAN facts | NO |
| `is_lock γdk d_lock <{disk_res …}>` | YES | payload `disk_res … ξ` const-embedded | NO |
| `timer_cap` | no | pin + `inv` | YES (const) |
| `tick_keeper γtl γs` | YES | `ticks_res … ξ` const-embedded, plus `procs_inv` | NO |
| `procs_inv γs` | YES | `proc_lock_res … ξ` const-embedded, plus `is_kstack ξ` | NO |

**Why the payloads are ξ-indexed at all:** the M1/M4 notation flip is COMPLETE
through stage 2 — `TsoCtx.v:5312–5401` rebinds `↦ₘ`, `↦₈`, `↦₄`, `↦₂`, `↦ₛ` to
`ctx_*_pointsto cur_ctx`, and every one of `SchedCtx`, `ConsoleInv`,
`TicksInv`, `DiskInv` imports `TsoCtx` after `RiscvPtsto`.  So
`proc_lock_res` (`p_state pa ↦₄ st`, `p_chan pa ↦₈ ch`), `cons_res`
(`a_cons_r ↦₄ r`, `cons_data` over `↦ₘ`), `ticks_res` (`a_ticks ↦₄ t`) and
`disk_res` are all genuinely ξ-indexed — CORRECTLY so.  What is wrong is that
they are wrapped in `<{ }>` rather than λ-abstracted over the payload's own ξ.

**This is §0.28′(1)'s unfinished λ-conversion, and measurement widens its
list.**  The ruling named the stragglers as "console/uart/ticks".  Measured:
UART (`tx_res`) is ALREADY clean; the actual stragglers on the trap path are

| payload | home | `<{ }>` mention sites |
|---|---|---|
| `proc_lock_res` | `SchedCtx.v` | 44 (19 files) |
| `disk_res` | `DiskInv.v` | 175 |
| `ticks_res` | `TicksInv.v` | 16 |
| `cons_res` | `ConsoleInv.v` | 10 |
| (`wait_res`) | | 41 |
| (`tx_res` — already ξ-free) | | 11 |

Tree-wide surface: **457 `<{ }>` sites across 163 files.**  That is an M3-sweep
sized change, it collides head-on with the lock lane's cone, and it is not a
single-lane job.

**And the mention-site count UNDERSTATES it, which is worth being explicit
about before anyone prices it as a sed.**  `<{ P }>` currently discharges the
lock surface's transport obligation for FREE, through
`TsoCtx.ctx_morph_const_pay` (priority 99): a constant embedding is trivially
`CtxMorph`.  Replacing `<{ proc_lock_res … }>` by `(λ ζ, proc_lock_res (XI := ζ) …)`
turns that free instance into a REAL proof obligation per payload —
`CtxMorph (λ ζ, proc_lock_res ζ …)` has to be built out of the structural
instances (`ctx_morph_pointsto` / `_sep` / `_exist` / `_word` / `_word4`)
through `proc_slots`' state-indexed `if`-chains and `proc_pub`'s big-ops.  That
per-payload transport proof, not the rename, is what §0.28′(1) is actually
asking for, and it is what TsoCtx's own note means by *any payload failing it
at SC is a payload the TSO flip would break*.

**Consequence for §0.39′.**  The ruling's PRINCIPLE stands — the handler
contract IS context-dependent and freshness IS the right currency for the
FLOORS.  Its EXECUTION CLAIM does not: *"the boot proof establishes the
∀-fresh-ξ form … derived from the started deposit's transportable rows +
freshness — the derivation ProofMainSecondary already performs green"* is not
available.  `ProofMainSecondary` performs no context crossing at all: it takes
`started_inv (main_deposit …)` at its OWN ambient ξ as a hypothesis and
assembles `devintr_caps` by framing (`ProofMainSecondary.v:688–690`).  The
crossing is deferred to `ProofMain` — which is RED.  There is no existing
transport to reuse, and none can exist for these rows until the payloads are
λ-converted.

**A second, independent gap in the ruling's justification — CORES vs
CONTEXTS.**  §0.39′ grounds the freshness in the started barrier: *the other
cores get this contract through the [started] barrier, which ensures those CPUs
have a sufficiently fresh context*.  That covers the per-core BOOT contexts,
and those are not the contexts the contract quantifies over.  §0.28′'s addendum
settles that an interrupt is not a context crossing — *the preempted thread
keeps its identity* — so the handler runs at the PREEMPTED THREAD's ξ, which for
every trap after `userinit` is a process context minted long after boot and
reached through the park chain (§0.33′'s inventory: `park_world` / the p->lock
resume tie), not through `started`.  Freshness for those is still plausible —
every kernel context descends from SOME barrier — but the started deposit is not
its channel, and whatever is, has to be named before the premise is dischargeable
at the trap sites (`WpIntrInv`'s interrupt arm).  This is separable from the
payload blocker below and would remain open even if the λ-conversion landed
tomorrow.

**Also note:** the two options §0.39′ supersedes (the ∀-caps parameter in the
entry package; the layer hoist) are refuted by the SAME measurement, for the
same reason — every spelling that needs `devintr_caps` at a context other than
the one that minted it hits the payload identity, not the floor.  So the
supersession is not what unblocks this; the λ-conversion is.

---

## I5. Characterized and STOPPED (forbidden files — for the coordinator to route)

1. **`TsoCtx` (forbidden): the freshpack law for a DISCARDED context pointsto.**
   Needed by `disk_geom`'s three `↦₈□` and by `is_kstack`.  Exact statement
   wanted, in `SpecDevintr`'s `freshpack` shape:

   ```coq
   Lemma ctx_word_pointsto_freshpack `{KTR : !CurKtier} (ξ : CtxId) a w :
     ctx_word_pointsto ξ a DfracDiscarded w ⊢
     ∃ t : nat, ctx_floor ξ t ∗
       □ (∀ ζ : CtxId, ctx_floor ζ t -∗ ctx_word_pointsto ζ a DfracDiscarded w).
   ```

   (and the byte-level `ctx_pointsto` twin it is built from).  This is exactly
   §0.39′'s pattern one tier down: the discarded fact's clean lower bound sits
   at its write timestamp `t`, and a target context that has passed `t` may
   restate it.  NOT the `ctx_string_all` route: `ctx_string_all a dq s :=
   ∀ ξ, ctx_string_pointsto ξ a dq s` (§0.21′, `TsoCtx.v:1347`) is mintable only
   for rodata (`t = 0`, via `ctx_pointsto_of_pristine_va_all`), and
   `d_desc_ptr` / `p_kstack` are written at RUNTIME — so the ∀-context form is
   not free for them and the freshness form is the honest one.

2. **The M3 λ-conversion of the four straggler payloads** (`proc_lock_res`,
   `disk_res`, `ticks_res`, `cons_res`) — §0.28′(1), sized above.  Owner-level
   scheduling call: it is the gate on §0.39′, on this lane, and (same root
   cause) on the park-protocol crossing the lock lane is paying in `ProofSwtch`
   / `ProofForkretPark`, where a handle minted at the parker's ξ has to be
   usable at the resumer's.

3. Not attempted, and not needed until (1)+(2) land: the `IntrDefs` stamp index
   of §I2.  Landing it now would make `ProofKernelvec` fail at the same line
   for the same reason, with a wider blast radius.

---

## I6. Changed files, this lane

* `iris/SpecDevintr.v` — added section `CapsFresh` (the relocation kit, §I3)
  and the in-file record of the refutation (§I4).  No existing definition,
  lemma or statement moved; the change is purely additive.
* `ZZintrbuild.sh` (tree root) — the sentinel-backed remote build driver
  (`MAKEEXIT` / `GREEN=g/n` / `RED <file>` / `DONE`).  Scratch, not for merge.

Nothing committed.

**Verification build after the change** (same driver, sentinel-backed):

```
SUBEXIT[model-xv6iris]=0  SUBEXIT[kernel-rocq]=0  SUBEXIT[user-rocq]=0
MAKEEXIT=2       GREEN=1100/1296
```

RED list byte-identical to the I0 baseline (196 entries, `diff` clean).  Red-list
delta: **none** — the change is additive and regresses nothing; it also greens
nothing, because the blocker in §I4 is upstream of anything this lane may touch.
