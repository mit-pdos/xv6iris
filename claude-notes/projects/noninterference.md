# noninterference — a design discussion, checkpointed

STATUS: DESIGN DISCUSSION, CHECKPOINTED 2026-09-04 (Fable, with the
owner).  Not part of the kernel proof's design and deliberately NOT under
`design/`: nothing under `iris/` implements any of it, and no lane is
running it.  It records how non-interference (NI) between user processes
could be formalized, specified and proved in this framework, the options
that were considered and rejected, one formulation that was proposed and
then corrected in review, and the honest limits.  Anyone picking this up
starts here; the rulings below are recommendations and the owner decides.

Related design of record: [`design/user-wp-slot.md`](../design/user-wp-slot.md)
(the trap contract this would re-shape), [`design/uk-engine.md`](../design/uk-engine.md)
and [`design/user-heap.md`](../design/user-heap.md) (the U tiers whose
determinism is half of any proof), [`design/adequacy.md`](../design/adequacy.md)
(`Hphi`, and its item (d) — "hyperproperties are out of
`wp_strong_adequacy`'s reach" — which §4 says how to sidestep),
[`uart-trace.md`](uart-trace.md) (the trace-export pattern §6 reuses),
[`design/fs-bitmap.md`](../design/fs-bitmap.md) (the FREE POOL: the in-tree
precedent for §3's ledger).

## 0. The position, in one paragraph

State NI as **refinement of each process's trap-boundary trace to a
deterministic ABSTRACT PROCESS MACHINE whose only inputs are the process's
own initial state and a PUBLIC, ACTOR-LABELLED EVENT HISTORY** (allocations
and frees, forks, fs writes, ticks, the order of rounds), and prove it
UNARILY in the existing CSL from three ingredients the tree already has in
embryo: (a) FUNCTIONAL rather than relational rows in
`UexecRet.uexec_ret_F`'s ecall arm — the kernel's round on a process's trap
is a function of the trapped key and the event-history prefix; (b) ghost
LEDGERS that make every shared kernel resource's spec deterministic
relative to the events that moved it (kalloc first); (c) OWNERSHIP for "no
other thread changes this process's view" — the frame rule, not a lemma
about other processes' code.  The two-run statement is then a PURE
corollary outside Iris because the abstract machine is a function, and
SECRECY of a process A reduces to the question "which events does A
generate?" — whose answer for xv6 is §3.  No relational logic (SeLoC-style
double WP), no product program, no leaf lemma re-proved; §5 says exactly
what a double WP would have bought and why it is not needed here.

## 1. The observation function already exists: `uvis`

`UexecSlot.uvis = (tf, M, π, sz, fdv, cwd)` — the trapframe words, the lazy
va-keyed image, the per-page X/W map, the break, the descriptor view, the
cwd inum.  Every ruling that shaped it was an OBSERVABILITY ruling made for
abstraction reasons: "a process observes its registers and its va-keyed
bytes, never PPNs" (why the table is not in the key); "the process cannot
observe lazy allocation" (why the image is the lazy view and the page-fault
arm is transparent); "an interrupt cannot retype a descriptor" (why `ukb_F`
pins `fdv` across the transparent arm).  Those are exactly the decisions an
NI proof must make about what a subject can see, and they were made before
anyone asked about NI.  The observation of process P at any point is P's
key.  Nothing has to be invented here.

Partitions are processes (later, process families: a parent and its
children, which share pipes and `wait`).  Low = the process under study;
high = everything else — other processes' images and registers, other
files' contents on disk, the physical placement of the low process's own
pages, the buffer cache, the proc table, the free lists.  Kernel state the
process cannot observe is high BY DEFAULT, and the proof never has to say
what happens to it.

## 2. The formulation that was proposed and corrected

**First proposal (rejected in review).**  Declassify xv6's channels as an
ORACLE of OUTCOMES read off the low process's own trace: the pid `fork`
returns, a "sbrk failed" bit, the `uptime` value, a "killed" bit.  Then
"P's trace = F(P's key, oracle)" is unary and the two-run corollary is
free.

**The owner's objection, which is right.**  Declassifying B's OUTCOME
("sbrk failed") is useless for secrecy: the theorem then says nothing about
whether the failure correlates with A's data.  Put sharply — suppose the
secret process A makes no syscalls at all, and the adversary B calls
`sbrk`; `kalloc` fails "nondeterministically" per its spec; how could one
argue B learns nothing about A, when the spec does not say where the
nondeterminism comes from?  Read that way the first proposal only proves
"an adversary that makes no syscalls learns nothing", which is unrealistic,
and it makes the INTEGRITY direction clear (nobody writes P's view except
through P's own rows) while leaving SECRECY, the interesting direction,
unaddressed.

**The correction: the oracle is the EVENT HISTORY, not the outcomes.**  The
nondeterminism must be moved from the outcome to its SOURCE.  The kalloc
spec's nondeterministic failure is the spec's abstraction, not the
kernel's behaviour: `kalloc` fails iff the free list is empty.  Give the
allocator a ghost LEDGER — an abstract free count, or the free set, in its
invariant — and every allocation outcome is a function of the ledger, which
is a function of the sequence of allocation and free EVENTS so far, each
labelled by the actor (which process's round, or which kernel path,
produced it).  Do the same for `nextpid`, `ticks`, the zombie set and the
fs abstract state.  The oracle ι is then the public, actor-labelled event
history and never any process's data, and "P's trace = F(P's key, ι)"
really says P learns nothing but the events.  The two-run corollary is
unchanged in form, but its hypothesis "equal ι" is now a statement about
what the OTHER processes did, not about what P happened to observe.

The ledger is the device that PINS DOWN THE KERNEL'S CAUSALITY: the finite
list of event kinds is the complete answer to "through what can one
process's execution affect another's", and a syscall row that cannot be
made functional in (own key, ι-prefix) is a channel that has not been named
yet.  `bitmap_inv`'s FREE POOL is the in-tree precedent: `balloc`'s failure
is already a deterministic function of a ghost pool; the kalloc ledger is
the same shape one layer down.

## 3. What xv6 actually leaks: the lazy-allocation channel

With ι the event history, secrecy of A becomes "which events does A
generate?", and xv6's answer is uncomfortable but true.

- **A SYSCALL-FREE process still generates kernel events.**  Touching a
  lazily-allocated page runs `vmfault` → `kalloc`, which moves the ledger,
  which B observes at the memory limit through `sbrk`'s failure.  That is
  a real STORAGE channel of xv6 — a syscall-free A can encode a bit by
  touching or not touching a page — not an artefact of any proof method,
  and no relational logic makes it go away.  seL4, CertiKOS and Nickel all
  hit exactly this and all CHANGED THE ALLOCATOR (static partitioning of
  untyped memory; per-process quotas; Nistar's containers).  xv6 has no
  quotas of any kind.
- **Which pages are lazy.**  exec maps the ELF segments and the stack
  eagerly (`uvmalloc`, `flags2perm`); only `sbrk`-grown pages are lazy
  (`vmfault` maps a first-touched page `R|W|U`; `perm_of`'s fill is exactly
  those).  So a process that has NEVER CALLED `sbrk` has no lazy pages, and
  its user steps generate no events at all: no page faults, no
  allocations, and its interrupt rounds are the transparent arm, which
  runs `yield`/`scheduler` and touches no ledger.
- **The other channels**, for the record: pid allocation (`nextpid` is
  global; `fork`'s return, `getpid`, `wait`'s pid); proc-slot exhaustion
  (`fork` returns −1); `uptime` (`ticks`); the order in which children
  exit, seen through `wait`, and how many bytes a pipe holds; console input
  (already `ObsUartIn` in the trace); `kkill(pid)`, which scans all 64
  procs with NO permission check — any process may kill any pid — an
  authorized cross-partition flow by xv6's design that breaks both
  directions of NI unless the high side is assumed not to call it, or the
  kill is an event.  NOT channels: U-mode `rdtime`/`rdcycle`/`rdinstret`
  trap, because xv6 never writes `scounteren` (grep of `kernel/` finds no
  occurrence), and `usertrap` kills the process — deterministic; and
  instruction-cache staleness, because no page a program can write is a
  page it can fetch from (`flags2perm` never yields W+X unless the ELF asks
  for it — require that it does not, a decidable fact about the image).
  `lr`/`sc` success is left free by the platform axioms; a low process
  using them would need an oracle bit per `sc`.

**The honest theorems for UNMODIFIED xv6**, in decreasing strength of what
they say about A:

1. **Strong instance.**  A process that has issued no syscalls (hence has
   no lazy pages) generates no kernel events; its data affects nothing any
   other process observes, with the ADVERSARY UNRESTRICTED — any syscalls,
   file system included.  A genuine secrecy result, and the first one to
   aim at: A = a verified or arbitrary program before its first syscall,
   B = anything.
2. **General.**  A's data influences other processes only through the
   events A generates.  The event VOCABULARY is the graded declassification
   policy: `Alloc A` concedes A's footprint COUNT, `Alloc A vpn` concedes
   more, `FsWrite A ino` concedes that A wrote a file but not what.
3. **Anything stronger for a syscalling A needs a kernel change** (memory
   and pid quotas per process, a `kill` permission check).  The framework
   would then be able to prove that the change closes the channel — the
   row for `sbrk` becomes functional in A's OWN quota ledger and the
   `Alloc` event drops out of ι.

The INTEGRITY direction is a corollary of the same theorem and is
straightforward, as the owner noted: B's key is a function of B's own key
and ι, so nothing writes B's memory or registers except through B's rows.

## 4. The unwinding conditions and their CSL homes

A classical NI proof (Rushby; seL4) discharges three unwinding conditions.
Each has a natural home here; the mapping is the argument that the
architecture fits.

- **Output consistency**: trivial, the unwinding relation IS "P's keys are
  equal".
- **Steps by others do not change P's observation.**  In seL4 and
  CertiKOS this is proven over the whole kernel — every operation of B
  preserves A's observation.  Here it is OWNERSHIP: P's image
  (`user_ptm_inv pt sz M`), trapframe words, `sz`, `fd_frags` and cwd are
  owned by P's slot while P runs and by P's residue (`UsertrapRes.ut_own`)
  while the kernel serves P; no other thread's WP ever holds them, so no
  other thread's step can be PROVEN to write them, and a ledger fragment
  for P's own history rides with them so only its holder can append.
  Nothing is proven about the high side's code, which is why the high side
  runs arbitrary code from the first milestone on.  The design constraint
  this induces: NI stays free exactly as long as every fact a process can
  observe is carried by a resource the process or its residue owns; a
  spec that let the U tier see a physical address or a shared kernel
  counter is where the argument would break.
- **The kernel round on P's trap** (step consistency for the kernel's
  part): the FUNCTIONAL ROWS.  Today `uexec_ret_F`'s ecall arm is
  `∀ r M' π' szv' fdv' cw', ⌜usys_mem_ok …⌝ -∗ … -∗ X (bump W r M' …)` — a
  RELATION between trapped and resumed key, deliberately loose ("safe at
  every `r`").  Write a pure `usys_det n W ι : uvis` and make the arm, for
  `n` in the class, `X (usys_det n W ι)` at the round's ι-prefix.  The
  direction of obligation is the one `design/user-wp-slot.md` stresses:
  the PROGRAM proves the arm and the KERNEL instantiates it, so a
  functional row is easier for the program and harder for the kernel — at
  `UexecApply.uexec_ret_round_slot` the loop must PROVE the round's actual
  `(r, M', …)` equals `usys_det`.  That is where the proof's content lives:
  `sbrk` (`r` = old `sz`, or −1 iff the ledger is empty; `M'`/`π'` already
  functional in `sz'` via `usys_sbrk_img`/`usys_sbrk_perm`, kernel source
  `SpecGrowproc.growproc_ok`); `fork` (child key `bump W 0 …`, functional
  today; parent `r` = the pid the ledger says); `wait`, `exit`, `getpid`,
  `uptime`; console `write` (`r = n` iff the buffer is readable in `π`,
  today the QUIET row — the "real loss" `uk-engine.md` records is the first
  place a functional row is missing).  The transparent arm `X W` is ALREADY
  functional, which is what makes scheduling and lazy allocation invisible
  and the property timing-insensitive.  `exec` success is a MINT from the
  new image (`UexecCond.cond_entry_slot`), the ORIGIN of a trace rather
  than a step of it.
- **User steps** (step consistency for the process's part).  For a
  VERIFIED low process, its own proof: every `UkRun*` leaf is functional
  in `(m, pc, M)`.  For ARBITRARY low code a new theorem `ustep : uvis ->
  uvis + trap` with the generic tier's landing stated as "lands at a
  realization of `ustep W`".  Foothold: `UserTotalU.v`'s execute facts
  travel with `goodmb` twins in `(Dr, Dw)` (certified register read/write
  sets) and `goodb_agree_congr` — read-frame congruence, "two states
  agreeing on the read set agree on the result" — IS the register half of
  the unwinding lemma; the memory half is `UserMemClassify` restated at the
  key, the abstraction the `uvb`-level leaves already present, which is
  what sidesteps the memory-isomorphism problem of §5.  The largest single
  item; DEFERRED by scoping the first theorem to a verified low process.
- **On linearity.**  The kernel can resume P only through a slot it got
  from P's `uexec_ret` (or a mint at userinit / fork / exec-success), so
  once the rows are functional the TYPE of the return channel is the NI
  policy — good intuition, and why M0 below has value on its own.  But the
  theorem must be about the ledger, because the generic `□ uexec_wp` is
  mintable at any key by anyone holding a `UEXEC_GEN`.

## 5. Unary versus double WP: what each buys, and why unary suffices here

The owner's question was whether secrecy fundamentally requires a
SeLoC-style double WP (Frumin–Krebbers–Birkedal 2021; ReLoC is the
refinement cousin) for the kernel, since otherwise "we don't know where the
kalloc nondeterminism comes from".  The considered answer:

- **What a relational logic buys, precisely.**  It proves "the result
  depends only on low state" WITHOUT exhibiting the function.  A unary
  logic must EXHIBIT it — a functional spec relative to an abstract state
  — and the two-run reasoning is then done once, on the pure abstract
  machine (CertiKOS's "security-preserving simulation", Costanzo–Shao–Gu
  PLDI 2016; seL4's unwinding on the abstract spec carried down by
  refinement, Murray et al. 2013).  That is the real trade-off, and it
  favours the relational route for code one never intends to specify
  functionally (a hash table inside a black box: `dwp e e {{ v1 v2, v1 = v2 }}`
  is far cheaper than saying what `e` returns).
- **Why it favours the unary route HERE.**  The tree is exhibiting the
  functions anyway: the atomic-update specs on the fs abstract state, the
  `proc_pt_any` campaign ("every contract to a PRECISE image or an
  existential written out"), `usys_fd_ok`/`usys_pipe_ok`/`usys_cwd_ok`.
  What secrecy adds is LEDGERS for the shared state still left
  nondeterministic (kalloc, `nextpid`, `ticks`, the zombie set) and ACTOR
  labels on events.  xv6's syscalls are coarse-grained atomic against that
  abstract state, so a TOTAL ORDER of events exists and each process's
  trace is a function of its key and its position in it: the kernel is
  LINEARIZABLE against a deterministic abstract machine, and NI is a
  property of that machine.  Everything nondeterministic in the semantics
  — the tick choice, hart interleaving, device steps, `lr`/`sc`, the icache
  view — ends up in ι as "the schedule", which every concurrent-NI
  formulation declassifies one way or another.
- **A double WP over `riscv_lang` would redo the ownership argument.**  For
  the strong instance (§3.1) the relational invariant is simple — the two
  runs are identical except A's pages and registers — and the proof would
  be: every kernel step either reads none of them or is A's own user step.
  But "kernel code holding no points-to for A's pages cannot be proven to
  read them" is exactly what the unary proof already relies on, and the
  functional rows are how the unary logic EXPORTS "did not read".  The
  relational version would also have to relate two PHYSICAL memories up to
  the placement of A's pages (kalloc serves the high side too, so A's ppns
  differ across runs), which the key-level statements abstract away for
  free.  And the whole tree is unary: leaves, engines, whole-function
  specs; a relational logic would re-derive rules per primitive.
- **Where the unary route IS weak**, honestly: kernel components whose
  functional spec is far off (the fs internals above all — a double WP
  could prove "the fs syscall's result depends only on the fs abstract
  state" without pinning the result); and genuinely racy user-visible
  behaviour at instruction granularity, which relational reasoning handles
  and functional specs cannot.  xv6 has neither once the schedule is in ι.
- **Possibilistic NI** ("for every run from s1 there is a run from s2 with
  equal observations") was also considered and rejected: weaker (it does
  not bound what P learns from scheduling) and harder here, since proving
  it needs step-simulation EXISTENCE, which a WP does not give.

## 6. The theorem, staged

- **M0 — contract-level determinism, no export.**  `usys_det` for the
  private class; `uexec_ret_F`'s ecall arm re-cut on it for those `n`; the
  loop's discharge at `uexec_ret_round_slot` through `UexecRound.uround_ok`.
  Deliverable: `round_det : uround_ok … -> W' = usys_det n W ι`, and
  `uexec_ret_F` readable as the policy.  TCB of the statement:
  `uexec_ret_F`'s shape and `usys_det`, measurable with `tools/tcb/`.
- **M1 — the ledgers, inside the logic.**  The kalloc ledger (free count
  or free set, with `kalloc`/`kfree` specs deterministic in it and an
  actor-labelled `Alloc`/`Free` event appended per call — the FREE POOL
  pattern), then `nextpid`, `ticks`, the zombie set; a per-process key
  history `uhist : mono_list uvis` beside `proc_priv`, appended at
  trap-out (`uvis_of_run`) and resume (`usys_det`); the invariant "every
  history is a run of the abstract machine at the event history".  The
  strong instance (§3.1) is provable at this stage as an in-logic
  statement: a process before its first syscall appends no events.
- **M2 — trace export.**  Two hardware-level observations in
  `RiscvLang.mobs`: `ObsUEnter cpu satp tf` at the sret-to-User node and
  `ObsUExit cpu satp sc tf` at the trap-from-User node (`satp` is the
  pid-free identity of the address space); `prim_step`'s hart arm emits at
  exactly those two nodes and stays silent elsewhere; the two boundary
  lemmas gain a permit in the shape of `WpUart.uart_obs_permit`; the client
  ledger `Pt` (`riscv_obs_pred`, ruling 2 of `uart-trace.md`) ties the
  events in `h` to the ghost histories and the event ledger.  Then
  `phi g h := ∀ s, utrace s h ⊑ canon (first_key s h) (events h)` and
  `xv6_ni_adequacy_xv6Σ` is `xv6_power_adequacy_xv6Σ` at that `phi`; the
  two-run corollaries (general, and the strong instance) are pure.  Events
  rather than a ghost-only history because `Hphi` concludes a `Prop` about
  `(g', h)`: a history not reflected in `h` exports only existentially, and
  an existential per run kills the two-run corollary.  The image is tied
  to the emitted registers by the permit (`user_ptm_inv`'s exactness — the
  `upt_tree_spec` "blocks direction" — proves the pure page walk of `g`
  equals `M`).  Fallback if the hart-arm cost is refused: a final-state
  statement through a pure observation on `gmem` at the proc table, which
  gives reachability but no two-run corollary.
- **M3 — extensions**, independent: arbitrary low code (`ustep`, §4);
  process FAMILIES as partitions (pipes and `wait` order become
  family-internal event positions; `UkFork`'s two-continuation leaf already
  distributes non-address-space resources); across power cycles (ledgers
  keyed by era); the no-`kill` corollary; kernel changes (quotas) and the
  theorem that they close a channel; private FILES, where "shares no
  state" stops being a syntactic class and the fs-syscall-specs lane's
  functional specs are the prerequisite.

**Suggested first instances.**  Secrecy: A = any program before its first
syscall, B = anything (§3.1).  Integrity/trace: low = `echo` (verified on
the Uk engine: `write` to the console, `exit`), high = anything `sh` runs —
trivial as a program, but it exercises the `write` row, the `exit` arm,
both boundary events and the export with a three-key `canon`.  Then a
verified program using `sbrk` and `fork`/`wait`, for the ledger positions.

## 7. Costs and risks

- **The hart arm of `prim_step` emits.**  `κ = []` is baked into the hart
  arm and asserted in the hart lifting lemmas (`RiscvExec.v`'s `assert (…
  κ = [])` sites).  Emitting only at the two privilege-changing nodes keeps
  every other hart rule's κ trivially `[]`, but each assert site is touched
  once.  The one infrastructure cost that is not a re-spelling.
- **Functional rows are STRONGER GUARDS the kernel must meet**, one per
  syscall in the class (`write`'s count, `wait`'s pid, `sbrk`'s −1 arm as
  "ledger empty").  The fs-syscall-specs lane's per-entry receipts are the
  template.
- **The ledgers change the kalloc/pid/ticks specs tree-wide**: every
  caller of `kalloc` threads a ledger fragment or the ledger lives in an
  invariant every caller opens.  The FREE POOL's `bitmap_inv` (persistent
  invariant, opened through `wp_log_write_au`-style suppliers) is the shape
  to copy.
- **The channels are REAL.**  §3's theorems are true of xv6 only modulo
  the events; that is a statement about xv6 worth a line beside
  `kernel-defects.md` as a design property, not a defect: no kill
  permission check, no memory or pid quotas, lazy allocation charged to the
  global pool.
- **Physical placement leaks exist and are invisible** (which ppns P gets
  depends on the high side); nothing at the key sees it; keep the U tier's
  vocabulary key-only (§4's design constraint).
- **Not covered**: timing (P reads time only via `uptime`, an event; but
  the interleaving of P's and a high process's console OUTPUT is
  observable from outside the machine and is not part of P's observation —
  a property of the outside observer); integrity of the KERNEL against P,
  which is the existing safety theorem.
