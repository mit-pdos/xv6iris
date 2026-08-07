# fileclose — the last unproven callee of three proved functions

`fileclose` is the single function standing between the tree and three `Link`
files: `sys_pipe`, `sys_close` and `kexit` are all proved and all unlinked
because their only unproven callee is this one
([`sys-pipe.md`](sys-pipe.md), [`kexit.md`](kexit.md),
[`../design/file-table.md`](../design/file-table.md)). One
`ProofFileclose.v` + `LinkFileclose.v` buys three links and 392 bytes of
coverage.

```c
void fileclose(struct file *f) {
  struct file ff;
  acquire(&ftable.lock);
  if (f->ref < 1) panic("fileclose");
  if (--f->ref > 0) { release(&ftable.lock); return; }
  ff = *f;  f->ref = 0;  f->type = FD_NONE;
  release(&ftable.lock);
  if (ff.type == FD_PIPE) pipeclose(ff.pipe, ff.writable);
  else if (ff.type == FD_INODE || ff.type == FD_DEVICE) {
    begin_op(); iput(ff.ip); end_op();
  }
}
```

194 bytes @ `KernelSyms.fileclose`, 60 instructions, an 8-slot frame
(`ra@56, s0@48, s1@40, s2@32, s3@24, s4@16, s5@8`), five exits through one
epilogue at `+0x8e`.

## What has LANDED

- **The payload link.** This was the real blocker and it is done: a
  `file_ref` now carries the pipe end / inode reference it names, so the
  last closer has a WHOLE `pipe_ref` to give `pipeclose` and a whole
  `cwd_ref` to give `iput`. Design and rationale:
  [`../design/file-table.md`](../design/file-table.md), section
  "`file_payload`". `file_close_last_step` had to be generalized off
  `qt = 1` on the way — see the note under "the three ghost steps" there,
  it is the kind of mistake that only surfaces at the consumer.
- **`CodeFileclose.v`** — 72 instruction facts, generated (`make gen-code`
  after adding the manifest row).

## What is LEFT, and the design decisions already made

### 1. The contract's second half: a TYPE-INDEXED callee environment

The reference half of the contract is unchanged and stable (a reference in,
one `fd_slot` out, silent about which arm ran). The new half is that
fileclose can free a pipe's page and can do disk I/O and SLEEP, so its
callers must own the corresponding fabric. What they must own depends on
`fc_type Cf`, because the type is what selects the arm:

| type | environment | returns |
|---|---|---|
| `FD_PIPE` | pipeclose's: `procs_inv`, the kmem lock, `kalloc_avail γka on`, and `n+2 < 2^31` | `kalloc_avail on ∨ kalloc_avail (avail_inc on)` |
| `FD_INODE`/`FD_DEVICE` | begin_op/iput/end_op's: `bio_ctx`, `log_ctx`, `fs_crash_seam`, `gen_cert`, `dev_inv`, `disk_geom`, the virtio lock, `bslots bn 3`, `procs_inv`, `scheds_inv`, `own_ctx`, `park_hlf`, `p_pid`, and the pure `n = 0` / `eb = true` / `p = proc_addr j` / `j < NPROC` / `γs !! j` / `log_geom_ok` | `own_ctx ∗ park_hlf ∗ p_pid ∗ bslots` |
| `FD_NONE` | nothing | nothing |

**Indexing rather than taking the union is what keeps the cheap callers
cheap**, and it is not a trick: pipealloc closes files it has just allocated
and not yet typed (`filealloc`'s post already pins `fc_type Cf = FD_NONE`),
so it owns no file system and must not be asked for one; sys_pipe closes
FD_PIPE files and is asked only for the pipe fabric it already has. Only a
caller closing a descriptor of UNKNOWN type — sys_close, kexit — pays for
both, which is the truth about closing an arbitrary fd.

The log RESERVATION is deliberately NOT in the environment: begin_op mints
`log_op γ MAXOPBLOCKS` and end_op retires it, so an operation's budget never
crosses fileclose's boundary.

A draft of this contract is written; it is **not landed**, because it breaks
the four callers at once (below) and a red tree helps nobody. The draft
carries `fileclose_env_out_of_env` — the check that the FAST path
(`--f->ref > 0`, which returns without touching any of it) can pay the
postcondition out of the precondition. Keep that lemma: it is what catches a
bundle stated with a return going the wrong way.

**The naming wart is solved: one `Record fclose_names`** bundling every
ghost name and geometry value both arms are indexed by, with an explicit
`Inhabited` instance (spelled out — `bio_names` has function fields and
several of these records have no instance of their own). A caller that
cannot reach either arm passes `inhabitant`. The alternative — flat
parameters — would make pipealloc *name* a `bio_names` it has never heard
of; pushing them under an existential forces the continuation inside the
same binder and contorts the spec.

**The ghost CLASSES do propagate, and that part is unavoidable.** A caller
that can reach fileclose can reach iput, so `bioG`/`diskGhostG`/`uartGhostG`/
`fsLogG`/`logG`/`fsCrashG` must be in scope at every call site — including
pipealloc's, whose *contract* says nothing about a file system. Capacity
only, no resource: pipealloc's `Module Type` grows six class binders and
nothing else. There is no way to hide them behind a derived FD_NONE-only
interface: the derivation's proof needs the classes, and Coq's section
discharge would put them back into the derived lemma's statement anyway.

### 2. The stack constant, and its ripple

`fileclose_stack` goes **18 → 68** = its own 8 slots + `SpecIput.K_iput`
(60, the deepest callee; end_op wants 58, begin_op 26, pipeclose 22,
acquire/release 10). It is a CONSTANT, not per-arm — a function's stack need
is a property of the function ([`../durable-notes.md`](../durable-notes.md)).
The callers move with it:

| function | own frame | new bound |
|---|---|---|
| `pipealloc` | 6 | 74 |
| `sys_close` | 4 | 72 |
| `kexit` | 6 | 74 |
| `sys_pipe` | 8 | 82 (pipealloc, not copyout, now sets it) |

Two of the arithmetic lemmas that discharge these (`ProofSysPipe.sp_bounds`
and friends) `unfold fileclose_stack; lia` — they must also unfold `K_iput`
now, or `lia` cannot see the literal.

### 3. The four callers

- **`ProofPipealloc`** — two call sites, both at `fc_type = FD_NONE`, so the
  environment is `emp`. Only the junk-parameter wart above.
- **`ProofSysPipe`** — FD_PIPE, so `SpecSysPipe` gains `γs` + `procs_inv`
  (pipeclose's wakeup needs it) and the `n+2` bound; it already has the kmem
  lock and `kalloc_avail`. The two call sites are inside the shared
  `sp_close2` block lemma, so the threading happens once.
- **`ProofSysClose`** — unknown type: `SpecSysClose` gains BOTH bundles. This
  is the biggest contract growth in the set, and it is honest — closing an
  arbitrary descriptor can write the disk.
- **`ProofKexit`** — unknown type, in a LOOP over NOFILE descriptors. It
  already carries the whole FS bundle (it calls begin_op/iput/end_op itself);
  what it gains is the kmem lock and `kalloc_avail`, and the loop invariant
  gains `∃ on, kalloc_avail γka on` because each iteration may or may not
  free a pipe page.

### 3b. THE OPEN DESIGN QUESTION: sys_pipe cannot see the type

Landing the contract was attempted and **backed out** because of this, which
is worth having written down before the next attempt.

`pipealloc` is fine — `SpecFilealloc`'s post pins `fc_type Cf = FD_NONE`, and
the two error-path closes are discharged by `fileclose_env_none`. (Its `PF1`
disjunct and the `T4C` continuation each needed the type conjunct threaded
through; both edits are small and were verified to compile.)

`sys_pipe` is NOT fine, and the reason is structural. Two of its three error
tails close a file it has already INSTALLED in a descriptor and then
re-borrowed: `p->ofile[fd0] = 0` hands back an `ofile_slot`'s payload, and
that payload is `∃ k q C, cell ↦ fnode k ∗ file_ref γf k q C` — the content
is existentially quantified, so **the type is not recoverable**, and neither
`fileclose_pipe_env` nor `fileclose_env_none` can be produced. The proof
knows the file was FD_PIPE when it went in; the model has forgotten.

Two ways out, and they are not equivalent:

1. **Make sys_pipe own both bundles** and case-split on the type, handing
   fileclose whichever arm's environment matches. Mechanical, no new algebra
   — but it makes sys_pipe's contract demand a file system it provably never
   uses, which is exactly the over-claiming the type-indexing exists to
   avoid. It is also the *only* option for sys_close and kexit, which close
   descriptors of genuinely unknown type.
2. **A PERSISTENT per-slot content (or type) witness.** `SpecSysPipe.v`'s
   header already flags this as the missing piece for a different reason
   ("the post can say descriptor `fd0` names ftable slot `k0`, but not that
   `k0`'s type is FD_PIPE"), so it pays for two things at once. The payload
   link makes it cheap now: change the payload component from
   `frac × agree` to `option frac × agree`, so that `(None, to_agree pn)` is
   a duplicable — hence persistent — fragment extractable from any share.
   Put the type (or a content snapshot) in `fpnames`, tied to the content by
   a pure conjunct inside `file_payload`; a caller then keeps the witness
   across the install and re-borrow and recovers the type by agreement. It
   also needs `fnode` injectivity, which follows from `acur_unsigned`.

Option 2 for sys_pipe, option 1 for sys_close and kexit, is probably the
right split — but it is a real design decision and it should be made before
the contract lands, because it decides how many of the four callers grow.

### 4. The proof

Nothing exotic is expected; the shape is `ProofFiledup.v` (acquire, the dead
`f->ref < 1` panic arm via `FileInv.fref_word_spos`, the ghost step, release)
plus the last-reference arm. Notes for it:

- **The order the C code uses is the order the model needs.** `f->type =
  FD_NONE` is stored, and the lock released, BEFORE the payload is spent. At
  FD_NONE the payload is `emp`, so what goes back into the table is the slot
  with no payload while the closer walks away with the pipe end.
- `s2..s5` are saved LAZILY — only on the slow path (`+0x26`), and the fast
  path never touches them — so `callee_saved` comes out differently on the
  two paths and neither needs the other's stores.
- The three arms rejoin at the epilogue (`+0x8e`) after restoring `s2..s5`;
  the FD_NONE arm (`+0x64`) reaches it by a `j`, so it is the same
  rejoining-arms shape as pipeclose's, and the epilogue should be one
  `iAssert`ed continuation rather than three copies.
- `ff = *f` is four loads at `+0x2e..+0x3e` (`type`→s2, `writable`→s3 via a
  `lbu`, `pipe`→s4, `ip`→s5); `fc_wbool` is exactly the truth value of that
  `lbu`, which is what `pipeclose`'s `eq_vec a1 zero_reg = negb w` premise
  consumes.
- The type dispatch is `beq s2,1` then `(uint)(s2-2) <= 1` — an `addiw` and
  a `bgeu`, i.e. the FD_INODE/FD_DEVICE test is one unsigned comparison, not
  two.
