# kexec — the exec() system call

`kexec()` (kernel/exec.c) is **the largest function in the tree**: 287
instructions / 860 bytes at `KernelSyms.kexec = 0x800046bc`, more than three
times the next one (`kfork`, 270 B). It is also the only function that is at
once an FS client, a page-table *builder*, and a `struct proc` mutator — the
three subsystems meet nowhere else.

Design lives here rather than in `design/`: the pieces it needs belong to
subsystems that already have design files
([`fs-icache.md`](../design/fs-icache.md),
[`proc-struct.md`](../design/proc-struct.md),
[`tlb-translation.md`](../design/tlb-translation.md)), and what is
kexec-specific is the *composition*.

## Status

| piece | state |
| --- | --- |
| `CodeKexec.v` (287 instr facts, prefix `kxc_`) | **landed**, generated |
| `CodeFlags2perm.v` (16 instr facts, `fpi_`) | **landed**, generated |
| `SpecFlags2perm.v` / `ProofFlags2perm.v` / `LinkFlags2perm.v` | **landed, PROVEN AND LINKED** |
| `ElfEnc.v` — the ELF byte vocabulary | **landed** |
| `ProcInv.proc_priv_newspace` / `proc_priv_name` / `upd_name` / `upd_exec` | **landed** |
| `SpecKexec.v` — the contract | **landed** |
| `ProofKexec*.v` | NOT STARTED |

`exec.c` is 1/2 functions, 32/892 bytes. `Print Assumptions
Flags2perm.wp_flags2perm_sconf` is byte-identical to what every leaf carries
(the 5 platform axioms + funext).

Two things worth keeping from `flags2perm`, small as it is:

- **THE MACHINE COMPUTES A DIFFERENT EXPRESSION FROM THE C, and the contract
  states the machine's.** gcc turned `if (flags & 0x1) perm = PTE_X` into a
  SHIFT-AND-MASK (`slliw a0,a0,3` then `andi a0,a0,8`), so no branch is
  emitted for it and the answer is `8 * bit0`; only the second test survives
  as a `beqz`. Stating `f2p` on the two BITS rather than on two comparisons is
  what makes the contract need no range premise on the `int` argument — both
  `andi`s clear every bit `slliw`'s sign extension could have reached.
- **`bitblast` does not exist here** (stdpp 1.12 ships only
  `bv_simplify`/`bv_solve`, and `bv_solve` ends in `lia`, which cannot see
  through `Z.land`/`Z.shiftl`). Bit-level facts are hand-driven at the
  `Z.testbit` level, in the style of `ProcPtOwn.z_pgd_land`; stdpp's
  `bv_*_unsigned` lemmas hold by `done`, which makes the descent cheap.

## The shape of the function

Four phases, and the phase boundaries are where the resources change hands.

```
  A  open        myproc(); begin_op(); namei(path); ilock(ip);
                 readi(ip,0,&elf,0,64)          -> the ELF header
  B  load        proc_pagetable(p)              -> a SECOND table
                 per PT_LOAD phdr:  readi(&ph)  uvmalloc  loadseg
                 loadseg is INLINED: walkaddr + readi straight into the
                 physical page (no memmove)
                 iunlockput(ip); end_op()
  C  stack       uvmalloc(sz .. sz+8192, PTE_W); uvmclear(guard page)
                 per argument: strlen, copyout; then copyout(ustack)
  D  commit      p->trapframe->a1/epc/sp; safestrcpy(p->name, last, 16);
                 p->pagetable = new; p->sz = sz;
                 proc_freepagetable(old, oldsz)
```

Everything before D is undone by `bad:`, which is why the contract's failure
arm can hand the process back at the **identical** `pprivate`.

### The frame

544 bytes / 68 slots. Four objects live in it and therefore do **not** appear
in the contract — they are carved out of the frame with
`StackBytes.slot_bytes_own`, exactly as namei's `name[DIRSIZ]` is:

| object | address | size |
| --- | --- | --- |
| `struct elfhdr elf` | `s0-432` | 64 |
| `struct proghdr ph` | `s0-488` | 56 |
| `uint64 ustack[33]` | `s0-368` | 264 |
| spilled `0xfff` / `path` / `sz1` / `argv` / `off` | `s0-536 … -504` | 8 each |

### The register-spill hazard

**gcc spills the callee-saved registers LAZILY, at four different points, and
the exits restore different subsets.** `s4` is spilled only after the `namei`
null test (+0x32); `s6` only after the magic test (+0x90); `s3/s5/s7-s11` only
after `proc_pagetable` succeeds (+0x9e…+0xaa). The common epilogue at +0x72
restores only `ra/s0/s1/s2`; the four `bad:` tails each restore their own
subset before jumping to it.

This is `completed/fileclose.md`'s "a lazily-spilled callee-saved register
makes `callee_saved` a PREMISE of the epilogue rather than a consequence of
its loads", at four times the scale. Plan the block decomposition around the
spill points, not around the C's statement boundaries.

### Loops

Three, and they nest:

1. the **phdr loop** (`i < elf.phnum`), whose body contains
2. the **loadseg page loop** (`i < filesz`, step PGSIZE) — a separate loop
   with its own induction, entered from two places (+0xf6 and +0x19a);
3. the **argv loop**, plus a trivial fourth, the **path scan** for `last`.

The phdr loop's continuation is a genuine "return from inside a loop" shape —
`kwait` is the model to read first (see
[`proc-struct-resources.md`](proc-struct-resources.md)).

## The contract

`SpecKexec.wp_kexec_sconf_body`. Its parameter block is `SpecNamei`'s FS
fabric verbatim (that is deliberate — kexec's phase A *is* namei's
precondition) plus `proc_priv`, the path buffer and the argv vector.

Two pure models live in `SpecKexec.v` because they are kexec-specific:

- `kxc_sp` / `kxc_sp_final` / `kxc_stack_ok` — the argument-push recurrence,
  transcribed from the instructions (`sub`, then `andi ...,-16`) rather than
  from the C's `sp -= sp % 16`, and the per-argument `bltu`-against-stackbase
  tests.
- `kxc_tf` — the three trapframe words D writes: `epc` (word 3,
  `tf_epc_idx`), `sp` (word 6, `kxc_tf_sp_idx` — the layout had no name for
  it), `a1` (word 15, `tf_arg_idx 1`).

### What the success arm does NOT say, and why

**It does not say the image is loaded.** `proc_pt` owns its pages at
EXISTENTIAL contents — the user-safety altitude `SpecVmfault.v` and
`SpecCopyout.v` already record. So no contract in this tree can state "the
process will run the file's text". What survives is structural: the entry PC,
the stack pointer, the new size, and the coherence between them. Closing this
needs a **contents-indexed refinement of `proc_pt`**, which is the single
largest thing kexec gives up and is not kexec's to build.

**It does not pin the new size to the ELF's segment table.** `szv'` is
existential. Pinning it means modelling the phdr loop's fold over
`ph.vaddr + ph.memsz`; `ElfEnc.v` has the field readers, so it is stateable,
but it buys nothing while the contents are existential anyway.

**It does not pin `p->name`** (existential at `PNAMELEN`). The only reader is
`procdump`, which `design/proc-struct.md` already records as unprovable as
written.

## THE THREE UPSTREAM SPEC CHANGES kexec IS BLOCKED ON

None of these is kexec's own design going wrong; each is a callee contract
that was stated for the callers it had. All three were found by trying to
compose them, and each has a recorded fix.

### 1. `SpecCopyout` assumes the destination table is the RUNNING process's

`wp_copyout_sconf_body` demands `p_pagetable p ↦₈{dqp} page_base P.(ud_root)`
and `p_sz p ↦₈{dqs} szv`. That is not decoration: copyout calls `vmfault`,
and `vmfault` reads `p->sz` for its bound check and maps into **`p->pagetable`
— not the table it was passed** (kernel/vm.c). kexec copies into a table that
is not installed yet, so the premise is unpayable.

*The fix*: a second contract for the case the destination range is **already
mapped**, where the `walkaddr` in copyout's loop always succeeds, the
`vmfault` call is dead, and the process is not mentioned at all — no `p_sz`,
no `p_pagetable`, and `P' = P` in the post (copyout maps nothing). kexec is
exactly that caller: its stack pages were `uvmalloc`'d three instructions
earlier. This is strictly the cleaner statement of what copyout does, and it
is what the guiding principle asks for. Cost: re-prove `ProofCopyout`'s loop
under a "range mapped" invariant; the arms are refuted, not re-derived.

Note in passing: the divergence between "the table passed" and
"`p->pagetable`" inside `vmfault` is a real latent inconsistency in xv6, not
just a spec artifact. It is unreachable from kexec (the pages are mapped), so
it is **not** a `kernel-defects.md` entry — but it is why the generalised
contract must forbid the fault path rather than model it.

### 2. `SpecSafestrcpy` over-asks its SOURCE

It demands the full `n = 16` source bytes. Its own header admits the over-ask
("only `n-2` are read … harmless and simpler, since every caller already owns
that much"). It is **not** harmless here: kexec's source is `last`, a pointer
*into* the path string, and 16 bytes past `last` can run off the end of the
caller's `char path[MAXPATH]`.

*The fix*: take an owned source length `ns` with
`(n - 1 <= ns)%nat \/ (exists k, (k < ns)%nat /\ f k = 0)` — "either you own
everything the loop's budget can reach, or there is a NUL inside what you
own, so it stops first". kexec then passes `ns := plen - last` and pays the
second disjunct from the path's own `bb_cstr`. `safestrcpy` is 52 bytes with
one loop; this is a small re-proof.

### 3. The log budget does not close for a two-element path

Arithmetic, not resources, and it is the sharpest edge:

- `begin_op` mints `log_op γ MAXOPBLOCKS`, `MAXOPBLOCKS = 10`.
- `SpecNamei` charges `(L + 1) * iput_units` and guarantees only
  `n - (L+1)*iput_units ≤ n'`, with `iput_units = 3`.
- `SpecIunlockput` demands `iput_units ≤ n'`.

So the composition needs `3(L+1) + 3 ≤ 10`, i.e. **`L ≤ 1` path elements** —
`/init` and `sh` are fine, `/bin/sh` is not. (`L = 3` cannot even call namei:
`3·4 > 10`.)

*The fix, and it belongs to the fs-namei project*: namei's charge is one
element too generous **on the success arm**. `namex` iputs the inodes it
walks *past* and RETURNS the last one — so a successful lookup of an
`L`-element path does at most `L` iputs, not `L+1`. Making the budget clause
depend on the `ok` flag (`L * iput_units` on success, `(L+1) * iput_units` on
failure) gives `n' ≥ 10 - 6 = 4 ≥ 3` at `L = 2` and the composition closes.

`SpecKexec` states the premise in the CONSTANTS
(`(L + 1) * iput_units + iput_units <= MAXOPBLOCKS`) rather than as `L ≤ 1`,
precisely so that it relaxes on its own the day namei's success arm is
tightened. **Do not** hard-code `L ≤ 1`.

## What is NOT blocked

- **`proc_pagetable` in the uncounted regime.** kexec runs at
  `kalloc_env γa None` (uvmalloc and proc_freepagetable both require it),
  while `wp_proc_pagetable_sconf` is counted-only. This looks like a fourth
  blocker and is not: `SpecProcPagetable` already exports the general
  `PROC_PAGETABLE_GEN` / `wp_proc_pagetable_core`, whose post is the
  `ppt_post` disjunction at an arbitrary `on` — including `None`. kexec is
  the caller that can use it, because it **tests the result against 0** and
  has a live `bad:` arm for the failure. Use `PROC_PAGETABLE_GEN`.
- **Joining proc_pagetable's output to `proc_pt`.**
  `ProcPtOwn.proc_pt_intro_ppt` is exactly the join:
  `ptree_own 2 (DfracOwn 1) t ∗ ⌜pt_rep0 t (ppt_map tfp)⌝` becomes
  `proc_pt (upt_desc (pt_base t) tfp)`. `page_valid` for the trapframe comes
  from `proc_pt_wf` inside the block being replaced
  (`ProofKforkParts.proc_priv_tfp_valid`).
- **`readi` into a kernel destination.** kexec is on `readi`'s KERNEL arm
  (`user = false`, `a1 = 0`) for all three of its readi call sites. Hand it
  `p_pid` *and* the destination bytes; do **not** hand a `p_pid` fraction on
  the user arm (the documented trap that bit `fileread`). For `loadseg`'s
  readi the destination is a physical user page — get its bytes out of
  `proc_pt` with `ProcPtOwn.proc_pt_page_acc`, the `↦ₚ ⇄ ↦ₘ` move from
  `completed/copy-inout.md`.
- **The `ilock` panic.** `if (ip->type == 0) panic("ilock: no type")` is the
  tree's one live panic; `SpecIlock` does not refute it. Supply
  `panic_wp_any` and expect nothing back on that arm. kexec's contract passes
  it for this reason.

## The seams, with the lemmas

Phase A's three joins are already worked out elsewhere; copy them rather than
re-deriving:

- **namei → ilock** — `ProofNamex.v` ~:3042. `inode_held` is pointer-keyed and
  existential, `ilock` is slot-keyed and wants a share:
  destruct it, then `IcacheRef.inode_ref_shed` (whose sum is deliberately left
  unreduced so `qi := q/2`, `s := q/2` matches `iunlockput`'s `(qi + s)` with
  no arithmetic). Pull the single-slot persistents out of the families with
  `ProofNamex.nx_esc_acc` / `nx_slk_acc`, and split `bslots bn 3` with
  `nx_bs3_split`.
- **ilock → readi** — `ProofFileread.v` ~:1736. Peel `ic_loaded` into
  `inode_meta` / `inode_map` / `inode_blocks`; `blkmap_wf`, `bm_covers` and
  the `MAXFILE*BSIZE` bound all fall out of the `inode_ok` inside it. Pass
  `dqd := DfracOwn (1/2)` — ilock's half of `i_dev`.
- **readi → iunlockput** — `ProofFileread.v` ~:1995. `bm`, `data` and `dn`
  come back literally unchanged, so `ic_loaded` re-assembles with the pure
  conjuncts verbatim. `inode_ref_gather` fires *inside* iunlockput.

Slot accounting closes: `iref_slots 2` in → namei success leaves 1 →
iunlockput returns 1 → 2 out. `bslots bn 3` threads whole through
namei/iunlockput and splits to `bslot` for ilock and readi.

## Cleanup found while writing the contract

Neither blocks anything; both are the same shape — a fact that is not about a
function living in that function's Spec, so a second Spec has to require the
first one to name it.

- **`ROOTDEV` lives in `SpecNamex.v`.** It is a param.h constant. Hoist it the
  way `tf_epc_idx` and friends were hoisted into `ProcGeom.v` for this same
  reason (`InodeInv.ireg_blocks_ok` is the older precedent). Until then
  `SpecKexec.v` requires `SpecNamex` for it, and says so.
- **`ic_sleeplocks` is defined THREE TIMES, identically**, in `IcacheBoot.v`,
  `SpecFileclose.v` and `SpecDirlink.v`. They are transparent, so the three
  are convertible — but a contract that must COMPOSE with `SpecNamei`'s has to
  name the one namei's import scope resolves to (`SpecDirlink`'s), and there
  is nothing in the source that tells you which that is. One definition, in
  `IcacheBoot.v`, re-exported.

## Worklist

1. **The two callee re-proofs** (§1 and §2 above). Independent of each other
   and of everything below; do them first, they unblock phases C and D.
2. **Phase A** — `ProofKexecA.v`, entry through the ELF-header readi and the
   magic test, plus the two short `bad:` tails that are reachable from it.
   This is the phase whose *resources* are hardest and whose *control flow* is
   easiest; get the FS composition right here and B/C inherit it.
3. **Phase B** — the phdr loop and the inlined loadseg. Two nested fuel
   inductions. `ElfEnc.v`'s `ph_at`/`ph_at_succ` is the offset recurrence.
4. **Phase C** — the argument loops against `kxc_sp`.
5. **Phase D** — the commit. `proc_priv_newspace` + three `tf_page_word_upd`
   + `proc_priv_name`; `upd_exec_compose` is the equation that turns the
   composite back into the contract's `upd_exec`.
6. **`LinkKexec.v`**, then wire `sys_exec` (which is 0/1 and needs
   `SpecKexec` plus the argv-page story `fetchstr`/`kalloc` builds).

Take the branch-per-phase strategy the fs-icache project uses. Phases A–D
each end at a join the next one starts from, so they are separable files, and
the spill points above tell you which callee-saved registers are live across
each boundary.
