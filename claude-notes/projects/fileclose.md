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

**Known wart, decide before landing.** The parameters of the arm a caller
does *not* take still have to be NAMED by it (a `bio_names`, a `log_names`,
…). pipealloc has none of those in scope. Options: `Inhabited` instances on
the five ghost-name records so a caller passes `inhabitant`; or one
`Record fclose_names` bundling them with one `Inhabited` instance; or push
the parameters under an existential inside the bundle, which forces the
continuation inside the same binder and contorts the spec. The record is
probably right.

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
