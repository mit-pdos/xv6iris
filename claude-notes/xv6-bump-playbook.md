# Bumping `XV6_REV`: the playbook

How to move this development to a new upstream xv6 revision, what breaks, in
what order, and which of it is mechanical. Mostly a list of ways the job *looks*
finished when it is not.

Read [`durable-notes.md`](durable-notes.md) first for the build and the
cross-cutting gotchas; this file is only about version bumps.

---

## 0. The one-paragraph version

Change `XV6_REV`, force the kernel rebuild, re-dump, regenerate the decode
layer, **verify the dump actually moved**, then classify: exactly which
functions changed SHAPE (a real C change) versus merely MOVED (relayout).
Relayout is a tool's job and should cost you almost nothing. Shape changes are
proof work. Then loop `make -k` → fix → `make -k` until it is clean, because
each round only reveals the next layer. Finish with `Print Assumptions` on the
top-level theorem and a module-type ascription on every `Link` file you
touched.

---

## 1. The mechanical steps, in order, with their traps

```sh
# 1. pin
$EDITOR Makefile                       # XV6_REV ?= <new sha>
cd xv6-riscv && git fetch --all && git checkout <new sha> && cd ..

# 2. FORCE the kernel rebuild  -- `make kernel` DOES NOT DO THIS
make -C xv6-riscv kernel/kernel

# 3. ELF -> kernel-rocq/    (KernelSyms.v, KernelData.v, KernelInstrs.v)
make dump

# 4. kernel-rocq/ -> iris/  (Code<F>.v, KernelDecode*.v, KernelConsts.v)
make gen-code
```

### TRAP: `make kernel` is a no-op once the ELF exists

    $(KERNEL_ELF): | $(XV6_DIR)

`|` is an **order-only** prerequisite — "the directory must exist", not
"rebuild when the sources change". After a `git checkout` of a different
revision, `make kernel` prints *"Nothing to be done for 'kernel'"* and you
proceed to verify a stale image against new proofs. Always step 2 explicitly.

### TRAP: `gen-code` does not re-dump

`gen-code` reads `kernel-rocq/`, not the ELF. Run alone after a bump it
regenerates the decode layer from the **old** dump and prints its usual healthy
summary (`172 Code files, 8031 instr facts`). Both no-ops look like success.

### VERIFY, always — two lines, and they have caught a silent no-op

```sh
grep -E "Definition kalloc " kernel-rocq/KernelSyms.v
grep -E " kalloc$" xv6-riscv/kernel/kernel.sym
```

If those disagree the dump is stale and every proof in the tree is being
checked against an image that no longer exists.

### Three `gen_code.py` footguns

* **`--only` IS A FOOTGUN — DO NOT USE IT ALONE.** It restricts which *Code*
  files are written, but `main()` ALWAYS rewrites all 16 `KernelDecode*.v`
  shards from the `decoded` dict, which under `--only` holds just that one
  function's words — so `--only CodeReadi.v` would replace the 2306-lemma shared
  catalogue with 84 lemmas. To add ONE function: run the FULL generator into a
  scratch directory and copy out only what changed, then confirm every
  pre-existing Code file came back byte-identical and that the shard diffs are
  pure additions. (Adding a function also needs a `tools/code_manifest.json` row
  `[file, symbol, prefix, width]`, where `width` is the zero-padded hex width of
  the offset in the lemma name — `2` under 256 bytes, `3` at or above.)
* **The closing tactic is picked from the AST's head, and the whitelist is
  INCOMPLETE — a new instruction form can emit a decode lemma that does not
  compile.** Each `kd_<word>` is closed with `decode_bridge_ms`, whose final
  `vm_compute; reflexivity` needs the two sides' bitvector WELL-FORMEDNESS proof
  terms to coincide; where they do not, the generator selects
  `decode_bridge_ms_bv` — but only for a hard-coded list (`FENCE (`, `FENCEI (`,
  `CSRReg (`, `CSRImm (`). **`SHIFTIWOP` is missing from it**, so every `sraiw`
  emits a failing lemma: SRAIW's `funct7 = 0100000` sits above the 5-bit shamt,
  so the decoder yields `Z_to_bv 5 (1024 + shamt)` while the lemma states
  `mword_of_int shamt` — same `bv_unsigned`, different obligation, and the error
  prints two sides that look IDENTICAL. `slliw`/`srliw`/`sllw` are unaffected
  because their slices carry no funct7 bits. **The general rule: any instruction
  whose AST field is NARROWER than the encoded field it is sliced from needs the
  `_bv` bridge.** Fix the selection line in `gen_code.py`, not the shard — a
  hand-patched shard is silently reverted by the next `make gen-code`. When
  three decode shards fail at once after adding a function, look at what
  instruction forms that function introduced, not at the shards.
* **A `Code<F>.v` with no manifest row is a time bomb, and its own `.vo` hides
  it.** A Code file can sit in the tree and in `_CoqProject` with a `.vo` while
  its decode words were never written into `KernelDecode*.v`. It surfaces only
  on the next full build, as *"Variable decname should be bound to a term but is
  bound to the identifier `kd_0ed7e663`"*. The manifest row is what makes a Code
  file reproducible, so **a Code file the manifest does not list is the tell.**

---

## 2. Classify before you fix

This is the step that decides whether the bump costs an hour or a week. One
sweep over the generated Code files:

```sh
for c in iris/Code*.v; do b=$(basename $c)
  for sym in $(python3 tools/relayout_map.py map $b 2>/dev/null |
               tail -1 | sed 's/.*symbols: //;s/)//'); do
    n=$(python3 tools/relayout_shift.py $b $sym 2>/dev/null |
        sed -n '/== UNALIGNED ==/,$p' | tail -n +2 | wc -l)
    [ "$n" != 0 ] && echo "  $sym: $n unaligned"
  done
done
```

`UNALIGNED` counts instructions that were genuinely **inserted or deleted**;
everything else merely moved. Typically one or two functions show a shape change
and the rest of the tree is pure relayout.

**`UNALIGNED` is necessary but NOT sufficient.** Alignment is on
number-normalised ASTs, so when the new code repeats a shape already present,
difflib can pair the wrong copy — and then the list looks exactly right while
the map underneath is wrong. On `namex` (`03e5422a`) the new bail block is
`mv a0,s4 ; jal iunlockput` and the existing `L_par` arm is
`mv a0,s4 ; jal iunlock`; difflib matched them, `0x7a`/`0x7c` mapped to
*themselves* instead of `+0x84`/`+0x86`, and the map proposed rewriting
`L_par`'s `jal iunlock` into `jal iunlockput` — a well-typed immediate nothing
downstream catches — while `UNALIGNED` showed exactly the 6 entries the C
predicted. On a function whose new code duplicates an existing pair, check the
shift map against the disassembly; the cheap tell is an offset that maps to
itself inside a range where everything around it shifted.

Cross-check it against `git diff <old>..<new> -- kernel/` — the two should name
the same functions. If the sweep says a function changed shape and the C did
not, suspect the tooling, not gcc.

**A SHAPE CHANGE IN AN UNPROVEN FUNCTION COSTS NOTHING**, and the sweep says so
directly: a function with no `Code<F>.v` cannot appear in it. On `a28e94b` the
only reshaped function was `consoleintr`, which is assumed rather than proven
(`LinkConsoleintr.v`), so the whole bump was pure relayout and the sweep
printed nothing at all. An empty sweep is a real answer, not a broken command
— confirm it against the C diff rather than re-running the tools.

**AND THE SHIFT NEED NOT REACH THE END OF `.text`.** Everything after a
function that changed size moves by the delta *until an alignment boundary
absorbs it*. Here `consoleintr` lost 8 bytes, 170 symbols moved `-0x8`, and
then `kernelvec` onward did not move at all — `kernelvec.S`'s alignment ate the
8, and the freed padding surfaced as 8 fresh zero bytes in `KernelData.v`. So
derive the per-symbol delta from `KernelSyms.v` instead of assuming one shift:

```sh
git show HEAD:kernel-rocq/KernelSyms.v > /tmp/old-syms.v   # before `make dump`
```

then diff the two symbol tables and group by delta. The groups are the map: one
`+0` group before the change and after the absorbing boundary, one shifted
group between.

**Do this before touching anything.** Skipping it and reading "48 of 55 offsets
reshaped" off the *same-offset* tool says a function needs a from-scratch
rewrite when it does not. The shift tool answers directly — its `UNALIGNED` list
*is* the semantic diff of the upstream change:

    OLD 0x010  JAL myproc          <- deleted myproc() call
    OLD 0x014  LOAD 72(a0)         <- deleted p->sz read
    OLD 0x062  LOAD 80(s1)         <- deleted p->pagetable read
    NEW 0x00a  ADDI zreg -> x20    <- inserted li s4,0

---

## 3. The relayout (the cheap 90%)

Two tools, and picking the wrong one is the main way to waste time.

| | `relayout_map.py` | `relayout_shift.py` |
|---|---|---|
| compares | same offset, old vs new | difflib-aligned streams |
| use when | the function only MOVED | the function gained/lost an instruction |
| on a reshaped function | safe but nearly useless (quarantines everything above the first reshape) | gives the shift map and the semantic diff |

Usage, and `residue` is **mandatory** after `apply`:

```sh
python3 tools/relayout_map.py map     CodeBalloc.v
python3 tools/relayout_map.py apply   CodeBalloc.v ProofBalloc.v [ALIAS...] --write
python3 tools/relayout_map.py residue CodeBalloc.v ProofBalloc.v [ALIAS...]
```

Bulk-applying across a failure list is fine and is what makes a pure-relayout
bump cheap (~600-700 substitutions over ~80 files in a few minutes).
`tools/relayout_batch.py` is that driver — it pairs every `Code<F>.v` whose
diff carries immediate changes with each hand-written file that ANCHORS on one
of its symbols (see below for why that, and not "imports the module"), and
refuses to run at all if any source reports a SHAPE change, so §2 stays
mandatory:

```sh
python3 tools/relayout_batch.py            # dry run
python3 tools/relayout_batch.py --write
python3 tools/relayout_batch.py --residue  # the mandatory post-step, every pair
```

### AN ALIAS DECLARED IN A SIBLING FILE MAKES THE BATCH REPORT A TRUTHFUL "0"

`relayout_map.find_aliases` reads only the file it is rewriting, but a proof
split into `Proof<F>.v` + `Proof<F>Parts.v` declares the alias in the Parts
file (`Notation FC := KernelSyms.fileclose (only parsing).`) and *uses* it in
the other. The scan then never re-anchors, `apply` reports a healthy-looking
"0 substitutions", and the file is left stale — the failure mode the alias
machinery exists to prevent, one file over. `relayout_batch.py` resolves
aliases through the target's own `Require`s, and that scoping is not optional:
`KX` is `kexec` in one proof family and `kexit` in another, so a tree-wide
alias table would rewrite one function's region with the other's map.
`residue` is the only thing that catches this class of miss, which is the
reason it is mandatory rather than advisory.

### PAIR BY ANCHOR, NOT BY IMPORT

The obvious pairing — a proof file is a target when it names the `Code<F>`
module it gets its instruction facts from — is wrong, and wrong in the silent
direction. A `Proof<F>Parts.v` can state pure *arithmetic* lemmas about the
immediates and need no instruction fact at all:

```coq
Lemma prr_uservec_addr :
  add_vec (add_vec (mword_of_int (PRR + 0x18) : mword 64)
             (auipc_off (mword_of_int 4 : mword 20)))
    (sign_extend' 64 (mword_of_int 2972 : mword 12))
  = (mword_of_int KernelSyms.uservec : mword 64).
```

That file never Requires `CodePrepareReturn`, so an import-keyed batch never
visits it and `residue` never runs on it either — the miss is invisible to
BOTH halves of the process, and it surfaced only as a build error
(`Unable to unify "2147508224" with "2147508216"` — `uservec` vs `uservec - 8`).
So the target set is every hand-written file that ANCHORS on the symbol, via
`KernelSyms.<sym>` or via an alias its own imports declare. That widened the
sweep from 142 files to 286 and found exactly the two missing substitutions.

**Build the anchor index in one pass.** The natural phrasing — for each Code
file, for each candidate target, work out that target's aliases — re-reads
every target *and its whole import list* once per Code file, which is ~170 ×
~200 × ~30 file reads: minutes of wall time that look exactly like a hang.
Invert it: read each file once, build `sym -> [files]`, then every lookup is a
dict hit. 20 s for the whole tree.

### WHAT THE BATCH STRUCTURALLY CANNOT REACH

Anything not anchored on a `KernelSyms.<sym> + off`. The live instance is the
thin-wrapper pattern, where a whole function's immediates are *arguments* to a
shared lemma:

```coq
ilw_code KernelSyms.fileinit (mword_of_int 3) (mword_of_int 30)
         (mword_of_int 1406) (mword_of_int 1182) (mword_of_int 2083622).
```

There is no anchor on that line, so no map applies and only `residue` reports
it. `grep -ln 'ilw_code\|wp_initlock_wrapper'` names them all
(`ProofFileinit`, `ProofPrintkinit`, `ProofTrapinit`); fix by hand from
`relayout_map.py map`. Note which of the five moved: the two `addi`
immediates completing a data address did, the `jal` did not — caller and
callee shifted together, so their distance is unchanged.

### READING `residue`'s OUTPUT

Most of what it prints is noise, and the two kinds look alike. It flags any
*value* that is a pre-bump immediate anywhere in the map, so a pc OFFSET
(`KernelSyms.mappages + 0x9c`) or a prose comment (`c.sdsp s2,16(sp)`) trips
it whenever that number also moved somewhere. `AMBIGUOUS` likewise usually
means the line already holds the correct NEW value which happens to be some
other offset's OLD one. Triage by checking the value against the map AT THE
LINE'S OWN ANCHOR — that is decisive in one lookup, and it is the only check
worth doing on each.

### What the tools deliberately will NOT rewrite

Each of these is a bug that was found the hard way:

* **pc offsets** — `KernelSyms.argraw + 0x18` is an address, not an immediate.
* **register fields** — `Regidx (mword_of_int 15)`. A moved register means gcc
  reallocated, which means the proof needs a human. Reported as
  `REGISTERS REALLOCATED`.
* **bitvector widths** — `mword 12`, `sign_extend' 64`, `ones 0`.
* **anything above a symbol's first reshaped offset** — those offsets no longer
  name the same instruction in both images.
* **anything that is not the operand of `mword_of_int`** — see below.

### THE RULE THAT SUBSUMES THE OTHERS

Every immediate a proof spells goes through `mword_of_int`. A line carries
numbers in several roles:

```coq
(mword_of_int 12 : mword 12)                     (* immediate, then a TYPE *)
(sign_extend' 64 (mword_of_int 52 : mword 12))   (* WIDTH, immediate, TYPE  *)
sie_cap_gpr W2 (K - 4)                           (* frame arithmetic        *)
```

Map entries `12 -> 4088` and `64 -> 52` once produced `mword 4088`,
`sign_extend' 52` and `K - 4076`. `relayout_map.py` now substitutes **only the
operand of `mword_of_int`**. If you write an ad-hoc substitution script,
apply the same rule.

### And substitute in ONE PASS

Old→new pairs chain: `0x...70 -> 0x...78` next to `0x...78 -> 0x...80` applied
sequentially double-shifts the first. This bit both the tool and a hand-written
`.rodata` script.

---

## 4. The categories of breakage

### 4a. Immediates (jal/branch targets, auipc/addi pairs) — the tools

### 4b. `.rodata` string addresses — SPELLED THREE WAYS

A new string literal anywhere shifts every later one (`b7c25cf` interned
`"uart"` at `0x80007030` and pushed everything above it `+8`). Proofs name
those addresses in three different forms, and each needs its own sweep:

1. bare hex in a proof — `kernel_data_string 0x80007650%Z "virtio_disk"`
2. **named `Definition`s in `Spec*.v`** — `bcache_name_str : Z := 0x800073b0`
3. symbolically — `KernelSyms.etext + 0x648`

Form 2 is the dangerous one: **specs compile fine with a wrong address**
(it is still a well-typed `Z`), so the failure appears in a proof far away and
a failing-file sweep never touches the spec.

**Derive these by CONTENT, never by arithmetic.** Search the new image for the
NUL-terminated string each definition is *named after*, requiring a NUL before
it so a tail cannot match, then verify all of them:

    bcache_name_str  0x800073b0 -> 'bcache'      itable_name_str 0x80007440 -> 'itable'
    sl_str_addr      0x80007568 -> 'sleep lock'  waitlock_str    0x80007168 -> 'wait_lock'

An arithmetic `+8` sweep left `itable_name_str` pointing at `" inodes"` and
`inode_name_str` at `"itable"` — each off by one string, and each failing later
with an opaque byte mismatch. Two blind spots to know:

* `" inodes"` is the **tail** of `"iget: no inodes"`, not a literal — exact
  search finds nothing; read the raw bytes.
* `argraw`'s switch **jump table** shares the region and is not a string. Its
  entries move on any bump that moves `argraw`, but `ProofArgraw` no longer
  spells them: `ar_tbl := KernelSyms.states_0 + 0x30` and `ar_entry` computes
  each entry from `argraw + ar_case_off i - ar_tbl`, so a re-dump carries the
  whole table for free. **That is the shape to copy** whenever a proof needs a
  `.rodata` datum that is really a pair of symbols — derive, do not transcribe.

Do the whole verification in one pass rather than by eye — it is ~15 lines
against `objcopy -O binary --only-section=.rodata`, it checks the NUL-before
condition the manual method forgets, and on a bump that moves no strings it
returns a clean table in seconds:

```sh
grep -rn "_str[a-z_]* : Z := 0x\|_addr : Z := 0x8000[67]" iris/*.v
```

is the list to feed it; there are ~24 and every one must print the string its
name claims. Also invalidate any cached byte map before using it
(`bytes_*.json`); a stale cache produced confidently wrong answers twice.

### 4c. Data symbols

`sb`, `disk`, `proc`, `tickslock`, `end`, `bcache`, `itable`, `ftable`, `log`,
`kmem`, `pid_lock`, `wait_lock`, `ticks` all move. A proof reaching one through
an `lw` displacement goes stale **even when the symbol itself is symbolic**
(`sb_inodestart` is `KernelSyms.sb + 24`, but the displacement that reaches it
is a literal). FOR `end` SPECIFICALLY THE CANONICAL HANDLE IS `PageGeom.kmem_lo`, which
already is `ltac:(eval vm_compute in KernelSyms.end_)` and is in scope almost
everywhere (`KallocInv` and `PtTree` both `Require Export PageGeom`) — do not
write a second copy of the idiom. Otherwise prefer replacing a literal with
`KernelSyms.<sym>` when the surrounding proof can still close — but check first: an opaque constant breaks
a `lia` that needs the concrete value. `ltac:(eval vm_compute in KernelSyms.x)`
gives you both.

### 4a-bis. THE IMMEDIATE IS RIGHT AND THE SYMBOL IS WRONG

A relayout tool rewrites NUMBERS. It has no idea the callee's IDENTITY changed.
When a bump replaces one call with another — `initsleeplock(&tx_lock,"uart")`
became `initlock(&tx_lock,"uart")` in `d80e61c5` — the `jal` immediate moves and
the tool updates it correctly, but the proof's companion assertion

    assert (Htgtisl : add_vec pc (sign_extend' 64 imm)
                      = mword_of_int KernelSyms.initsleeplock) by pcw.

still names the OLD function. Here it fails loudly (`pcw` cannot close it), but
the diff looks like a clean relayout, so it is easy to "fix" the immediate again
and stay stuck. After any bump that changes WHICH function is called, grep the
touched proofs for `= mword_of_int KernelSyms.` and check each names the
function its immediate actually reaches.

### 4a-ter. THE SHIFT IS NOT ALWAYS A SHIFT

`relayout_shift.py` reports one old->new offset map, which suits a function that
gained or lost a contiguous block. A rewrite can instead be several deletions
and insertions at once. `uartputc_sync` in `d80e61c5` was TWO deletions and TWO
insertions: the flag prologue (20 bytes) replaced by an `acquire` call, the
device core moved -8 uniformly, the trailing flag test (10 bytes) replaced by a
`release` call, and the epilogue moved -6 — net -6 (80 -> 74 bytes). Deriving
that from `kernel.asm` directly was the right call; a single-shift reading of it
would have been wrong everywhere.

### 4c-bis. DERIVED constants — an address divided by something

The nastiest of the address categories, because no address sweep can see it.
A proof that needs an alignment or divisibility fact often carries the address
*pre-divided*:

```coq
assert (Hz : 2147582528 + 1112*kk + (88 + (64*qq + off))
             = (536895654 + 278*kk + 16*qq) * 4 + off) by lia.
```

`536895654` is `(bcache + 0x18 + 88) / 4`. Move `bcache` by 16 and the literal
must move by 4 — and it is not an address, does not look like one, and does not
appear in any symbol table. It surfaces only as `lia` reporting
**"Cannot find witness"**, which reads like a broken proof rather than a stale
constant.

Found in `DinodeSlot.v`, `ProofBmapParts.v`, `ProofInitlog.v`,
`ProofWriteHead.v` (all four carry the same `bcache`-derived value). When a
`lia` that used to close starts failing after a bump and the surrounding
addresses look right, compute the constant from the new address rather than
reading the proof:

```sh
grep -rn "5368956[0-9][0-9]" iris/        # then recompute (addr + off) / divisor
```

### 4d. Stack budgets — the cascade

If a changed function's **frame** grew, every caller's budget constant rises,
and they surface one build round at a time. `0024d4b` moved twelve:

```
psz must outlive walkaddr/vmfault/memmove in copyout
  -> gcc parks it in s11 -> frame 12 -> 14 slots
  -> copyout 50->52 -> either_copyout 56->58 -> readi 70->72
  -> dirlookup 82->84 -> {dirlink 92->94, namex 94->96}
  -> {namei 98->100, nameiparent 96->98} -> kexec 166->168
```

Rules learned:

* **Re-derive from the image, never adjust by +2.** `addi sp,sp,-N` → `N/8`
  slots, plus the deepest callee's bound.
* **"The callee gained an argument" does not imply "its frame grew."** copyin
  and copyinstr gained `psz` and stayed at 12 slots — their extra argument dies
  before the first call. copyout's had to live across it.
* **Check whether the call site sits inside the trap reserve.** `kwait` is
  `eb`-generic with `trap_res false = 0`, so it had to rise; `piperead`'s call
  is inside the reserve (`78 + (av-12)`) and did not. Same callee, opposite
  answer.
* **Write budgets as expressions.** `sys_wait_stack := (4 + K_kwait)` absorbed
  its ripple automatically; every baked number had to be found by a failing
  `lia`.
* Shortcut: check the changed functions' prologues immediately, and if no frame
  grew there is no cascade.
* **A FUNCTION THAT SHRANK CAN STILL HAVE GROWN ITS FRAME**, so "the C only
  deleted code" does not license skipping that prologue check. `a28e94b`
  deleted one switch arm from `consoleintr` (the `C('P')` → `procdump()` case,
  8 bytes shorter overall) and gcc took the freed register pressure as licence
  to re-allocate: `addi sp,sp,-32` became `addi sp,sp,-48`. Deleting a CALL
  also retires whatever that callee contributed to the deepest-callee term, so
  both halves of the budget move, in opposite directions.

### 4e. Register reallocation — NOT always a rename

gcc swapped `filestat`'s two lazily-spilled callee-saveds (`p` s3→s2,
`&st` s2→s3) **but not their spill slots** — 48(sp) stayed s2's. So it is a
*role* swap bounded by the prologue and epilogue, and a blanket rename attributes
the caller's saved words to the wrong slots. **That still compiles**: both slots
are `word_pointsto` at an address, so nothing at the leaf distinguishes them,
and it would surface only in the final `callee_saved`, if at all.

### 4f. Link-file functor arity

If a function gains a callee, its `Proof<F>.v` functor gains a parameter and
`Link<F>.v` must pass it. **Forgetting compiles**: Rocq accepts partial
application and silently defines the module as a *functor*. `LinkUartinit.v`
went green while being wrong; it surfaced only where a downstream functor
rejected it.

The check that works is a module-type ascription, which a functor cannot
satisfy:

```coq
Module Chk : SpecUartinit.UARTINIT := Uartinit.
```

---

## 5. Iterating to green

```sh
make -k -j8 2>&1 | tee build.log      # collect, fix, repeat
```

### `make -k` UNDERCOUNTS, always

A file whose dependency failed is never *attempted*, so each round reveals only
the next layer. On `0024d4b` the first list was 8 files; the true count was 25,
and twelve of those were pure relayout that no batch had ever seen. **Re-run
the full build after every round** and expect new names; do not conclude
"almost done" from a shrinking list.

### Per-file errors from a `-j` log are UNRELIABLE

With `-j8`, output from different files interleaves, so scraping
`File "./X.v"` … `Error` mis-assigns errors — it once blamed `ProofPrintkinit`
for a lemma it does not reference. Use the parallel log only to get the *set*
of failing files; then compile each individually for its real error.

### Watch for stale `.vo`s that are nobody's fault

A partial rebuild leaves `.vo`s inconsistent with a dependency ("makes
inconsistent assumptions over library ..."). Recompile the unmodified sources
in dependency order; nothing is wrong with the tree.

---

## 6. Parallelizing

The `Spec<F>.v` / sealed-functor / `Link<F>.v` architecture means **a function
proof depends only on its callees' SPECS, never their proofs** — verify with:

```sh
grep -oE "Require [A-Za-z ]*(Link|Proof)[A-Za-z]*" iris/Proof<F>.v
```

Empty output ⇒ the file is independent and can be worked on concurrently with
any other. On `0024d4b`, 12 of 13 code-changed proofs were mutually independent
and went out to seven agents at once.

Rules that made that work:

* **No `make`** in a worker — concurrent whole-tree builds fight. Targeted
  `coqc` only.
* **No editing `Spec*.v`**, and no `admit` to get green. If a spec looks wrong,
  STOP and report. Seven real spec bugs were found this way, each surfacing as
  an unsatisfiable premise at a *call site* far from the wrong spec. A worker
  that weakens the contract to fit hides the bug.
* A worker that needs to confirm "everything else in this file is fine" can
  stand up a temporary `Axiom` for the one blocking fact — but must delete it
  **and the `.vo` it produced**, or a later `Print Assumptions` is poisoned.

---

## 7. Finishing

0. **`make check-decode` BEFORE the validating build, never after.** It is
   `gen-code` plus `git diff --exit-code`, and both halves surprise you at the
   end of a bump. The diff is against **HEAD**, so while the bump is still
   uncommitted the target necessarily FAILS and its output is just the bump's
   own decode changes — not a defect, and not a check that tells you anything
   at that point. Worse, the `gen-code` half **rewrites every generated file
   unconditionally**, so running it after a green build touches ~180 mtimes and
   forces a from-scratch recompile of the tree. Content-wise the rewrite is a
   no-op — confirm with a hash sweep rather than by rebuilding:

   ```sh
   cd iris && md5sum KernelDecode*.v KernelConsts.v Code*.v | md5sum
   ```

   before and after; equal digests mean the build compiled exactly those bytes.

1. `make -k -j8` clean (`MAKEEXIT=0`).
2. **`Print Assumptions` on the top-level theorem** —
   `SystemAdequacy.xv6_power_adequacy_xv6Σ`. It is the only check that sees
   through every functor and seal. Expect the 5 Sail platform externs
   (`load_reservation`, `cancel_reservation`, `match_reservation`,
   `valid_reservation`, `plat_term_write`), `functional_extensionality_dep`,
   and the deliberately-unproven kernel functions. Anything else is a
   regression. Note that axioms in `Link` files for cones not yet wired into
   boot do **not** appear — absence is not proof they are gone.
3. Ascription-check every `Link` file whose functor arity changed (§4f).
4. Update the affected `claude-notes/` files, and delete whatever the bump made
   obsolete — a bump's whole point is often that machinery goes away.

---

## 8. Expect a bump to DELETE work

Most bumps here have been dominated by deletion: upstream fixing a conflation
(a function reading `myproc()` instead of its argument, a lock that was the
wrong kind) retires whatever the proofs had built to describe it, and the
retirement is usually cheaper than the workaround was. **So when a bump appears
to make a spec more complicated, look again** — and when it makes one simpler,
delete the machinery rather than porting it.
