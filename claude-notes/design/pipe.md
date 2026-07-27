# Design: pipes (`struct pipe` / `kernel/pipe.c`)

A pipe is one kalloc'd page holding a single self-contained object. Unlike the
ftable — an array of slots in a global array under one global lock, with an
immutable-while-referenced part read with no lock at all
([`file-table.md`](file-table.md)) — a pipe has **no lock-free part**: every
field is read and written only under `pi->lock`. So the well-formedness
predicate is exactly the shape the C code suggests, and everything interesting
is in the reference algebra instead.

Rocq: `PipeInv.v` (geometry, algebra, `pipe_res`/`is_pipe`, `new_pipe`);
`SpecPipealloc.v` is the first function spec, in the usual spec-module shape
([`spec-modules.md`](spec-modules.md)).

## Geometry

```c
#define PIPESIZE 512
struct pipe { struct spinlock lock; char data[PIPESIZE];
              uint nread; uint nwrite; int readopen; int writeopen; };
```

| field | off | width |
|---|---|---|
| `lock` | 0 | 24 (`locked`@0, `name`@8, `cpu`@16; **4 bytes of padding at 4**) |
| `data` | 24 | 512 |
| `nread` | 536 | 4 |
| `nwrite` | 540 | 4 |
| `readopen` | 544 | 4 |
| `writeopen` | 548 | 4 |

`sizeof(struct pipe)` = 552, allocated out of a 4096-byte page. All four word
offsets fit a 12-bit immediate, so the field addresses are the usual
`add_vec pi (sign_extend' 64 imm)` form (`poff_of`). The lock is the first
member, so `&pi->lock = pi` — which is literally the `a0` pipealloc passes to
`initlock`.

## The predicate

```coq
is_pipe γl γp pi := ⌜page_valid pi⌝ ∗ is_lock γl pi "pipe" (pipe_res γp pi)
```

Persistent, so every holder of either end shares it. `page_valid` is kalloc's
guarantee riding along with the object — it is what makes the page re-freeable,
so it has to survive to `pipeclose`.

`pipe_res` owns **every remaining byte of the page**: the four counter/flag
words, `pipe_data pi bs` (the 512-byte buffer with its contents tracked, so
piperead/pipewrite can say *which* bytes are in the pipe), and `pipe_slack pi`
— the 4 padding bytes inside `struct spinlock` plus everything past offset 552.
Nothing reads the slack; it is held only so the whole page can go back to
`kfree`, which memsets all 4096 bytes.

The queue coupling (live bytes are those at indices `[nread, nwrite)` mod
PIPESIZE, `nwrite - nread ≤ PIPESIZE`) is deliberately **not** imposed yet: it
belongs with the read/write specs and lands as one extra conjunct of
`pipe_res`.

## The reference count: two ends, not one number

xv6 gives a pipe no `int ref`; it gives it two flags, `readopen` and
`writeopen`, and `pipeclose(pi, writable)` clears the one its argument selects
and frees the page when both have reached 0. The number of outstanding
references *is* `readopen + writeopen`, so the ghost mirrors the **ends**:

```coq
pipe_ref γp w q := own (pn_end γp w) q        (* fracR, one gname per end *)
```

`w` is the `struct file`'s `writable` flag — the same bool pipeclose receives.
Indexing by a bool rather than cloning read/write means every law is stated
once. The invariant holds, per end, either "the flag is nonzero" or "the flag
is zero **and** the whole fraction has come home":

```coq
pipe_endstate γp w v := ⌜pflag_open v⌝ ∨ ⌜v = 0⌝ ∗ pipe_ref γp w 1
```

Three things fall out, and they are the whole reason for the shape:

- a holder of **any** positive fraction of an end proves that end's flag is
  nonzero (`pipe_endstate_holder`) — otherwise the invariant would hold
  fraction 1 of it as well;
- only a holder of the **full** fraction can close an end, so an end cannot be
  closed twice, and a `dup`ed file cannot close the pipe out from under its
  twin;
- the closer of the *second* end recovers fraction 1 of **both** ends
  (`pipe_endstate_closed`), which is the licence to reclaim the page.

A single counter does none of this: it cannot tell `pipeclose(pi,1)` twice
apart from one close of each end.

`pflag_open v := neq_vec (sign_extend' 64 v) zero_reg = true` — the shape the
`c.beqz`/`c.bnez` tests consume, as in `SleepLock.v`.

## Wiring to `struct file`

`pipe_held pi w q := ∃ γl γp, is_pipe γl γp pi ∗ pipe_ref γp w q` is the
address-keyed view for FileInv's `file_payload` on the `FD_PIPE` arm (all
`fcontent` records is the pipe's *address*).

**Caveat to settle when `fileclose` is built:** two `pipe_held` shares of the
same address cannot be recombined without knowing they name the same `γp`.
Every share of one ftable slot's payload descends from a single split, so this
never bites within a slot; if it ever does (a fraction parked in `file_rest`
and recombined across holders), pin the identity — either an `agree` component
on the ftable authority's per-slot entry, or a global address-keyed pipe
registry.

## Open item: reclaiming the page (blocks `pipeclose`, not `pipealloc`)

With `is_lock` built on a plain Iris `inv`, a pipe's page **can never actually
be freed**:

- the invariant is permanent, so `pipe_res` can never be taken back out;
- worse, `lock_name` *discards* the 8-byte name field forever (`↦₈□`), and
  `kfree` memsets all 4096 bytes, so even the lock's own fields cannot be
  reassembled into `page_own pi`.

So `pipeclose` will need (a) a cancellable form of `is_lock` — WpLock over
`cinv`, with a fractional cancel token that the two end references carry, so
holding both ends fully means holding the whole cancel token — and (b) a name
field that is reclaimable rather than discarded. Decide this before proving
`pipeclose`; the resource layout above is arranged so the switch touches
`is_pipe` and `WpLock` only.

`pipealloc` needs none of it: gcc proved its `if (pi) kfree(pi)` arm dead
(every path reaching `bad` has `pi == 0`), so pipealloc never frees a pipe.

## Carving the page: `PageFields.v`

`kalloc` hands back `page_own p` — 4096 anonymous bytes — and every object
built on a page has to turn that into the field cells its code loads and
stores. `PageFields.v` is that bridge, once: `bwin_split` (chop a byte
window), `bwin_rebase` (a window at offset `o` of `p` is a window at offset 0
of `pa_add p o`, so every field lemma is stated at 0), `bwin_bytes_list`
(anonymous bytes are *some* concrete byte list — what a content-tracking
buffer wants), `bytes_word4`/`bytes_word8` and their offset forms
`page_field4`/`page_field8`, plus `page_off_aligned` (the alignment side
condition, from `page_valid` + divisibility of the offset).

`PipeInv.page_own_pipe_raw` is the pipe's instantiation: `page_own pi ⊢
pipe_raw pi`, the ten windows (lock word, 4 padding bytes, name, cpu, the
512-byte buffer, the four counter/flag words, the 3544-byte tail) in the exact
shapes the instructions produce. Only the forward direction is built; the
converse (fields → page, for `kfree`) is the same lemmas run backwards, since
`bwin_split`/`bwin_rebase` are equivalences and `RiscvPtsto` already has
`word{4,8}_pointsto_bytes`.

Gotcha the arithmetic hit: `lia` returns "Cannot find witness" as soon as
`bv_unsigned` is anywhere in the goal *or the context*, so `page_off_arith`
packages the reasoning over plain `Z` variables and is fed the bitvector
values — the recipe in `durable-notes.md`.

## `pipealloc`

`SpecPipealloc.v` (contract), `WpPipeallocDecode.v` (72 instruction facts),
`ProofPipealloc.v` (the whole-function proof, a functor over `FILEALLOC`,
`KALLOC`, `INITLOCK` and `FILECLOSE`). It is where the two halves of the model meet: the two
*exclusive* `file_ref γf k 1 C` that filealloc hands back (which is what
licenses the eight unlocked stores into the two `struct file`s) and the fresh
page from kalloc, which becomes the pipe. Out come one `is_pipe` and its two
end references — exactly the pairing `sys_pipe` installs as each file's
`FD_PIPE` payload.

Read off the disassembly rather than the C:

- the `kfree` arm is gone (above);
- on the `bad` paths the two `struct file *` cells are **not** restored: the
  second-filealloc failure leaves a stale non-null pointer in `*f0`, and the
  kalloc failure leaves stale pointers in both. The failure postcondition
  therefore promises the cells back and nothing about their contents;
- `ip`/`off`/`major` are never written, so a pipe file inherits whatever the
  recycled ftable slot held (same observation as `off` in
  [`file-table.md`](file-table.md)); they stay existentially quantified in the
  postcondition's `fcontent`;
- the two files are allocated *before* the page, so the `bad` paths call
  `fileclose` on files whose `type` is still `FD_NONE` — no payload, no
  `pipeclose`/`iput`.

Frame: `c.addi16sp sp,-48` (6 slots) over the deepest callee, fileclose's
`fileclose_stack` = 18, hence `24 ≤ K`. The `"pipe"` string literal is at
`0x80007598`.

### How the proof is organised

Three things carry `ProofPipealloc.v`:

- **The branches read the cells, not the registers.** Every `c.beqz` after a
  call re-loads `*f0` / `*f1` from memory, so the control flow is decided by
  what was last *stored* into `pf0`/`pf1`. That is also why the two dead arms
  (`+0x96` and `+0xa2`, "`*f0 == 0` although filealloc succeeded") close:
  `fnode_nonzero` — a file slot's address `acur file_base 40 k` is never null.
- **The page is carved once** (`page_own_pipe_raw`), the four counter stores
  and `initlock` run on the pieces, and `new_pipe` turns them into the pipe
  plus its two end references. `new_pipe` allocates an invariant, so it needs
  `iApply fupd_wp` first — `iMod` of a *fancy* update does not eliminate
  straight into a `WP` goal the way a basic update does.
- **Four exits, three join points.** The epilogue (`+0xb8`), the "close `*f1`
  if it exists" tail (`+0xa8`) and the "close `*f0` first" tail (`+0xa4`) are
  `iAssert`ed continuations, offered to the arms as a **conjunction**
  (`EPI ∧ T8 ∧ T4C`) because exactly one is taken and they must therefore
  *share* the frame slots and the caller's continuation rather than split
  them. Building them takes two nested `iAssert`s (`EPI`, then `EPI ∧ T8`,
  then the three-way one), since each new component's proof needs the previous
  one in hand.

pipealloc takes **two** `fd_slot γs` (`FdSlots.v`), one per end — it creates
two references, and the `+4` per-process allowance in `FDSLOTS` is exactly the
locals a syscall may hold before installing them in descriptors. On the
first-filealloc-failure path only one slot is spent; the other is simply
dropped (the logic is affine).

`LinkPipealloc.v` does not exist yet: the functor cannot be instantiated until
`fileclose` is proven, so `tools/proof_coverage.py` will not count pipealloc
as proven before then. That is honest — the proof rests on the assumed
`FILECLOSE` contract.
