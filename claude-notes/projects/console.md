# console.c — consolewrite, consoleread, consoleintr

The console's own three functions. `consputc` and `consoleinit` are older work
(`consputc` is printk's spinning path, `consoleinit` is boot); the device model
is [`../design/device.md`](../design/device.md) and the UART driver underneath
is [`uart-driver.md`](uart-driver.md).

| function | where | status |
|---|---|---|
| `consolewrite(int,uint64,int)` | SpecConsolewrite / CodeConsolewrite / ProofConsolewrite / LinkConsolewrite | **PROVEN + LINKED, axiom-clean** (5 platform axioms + funext only) |
| `consoleread(int,uint64,int)` | SpecConsoleread / CodeConsoleread / LinkConsoleread | **spec written; proof owed.** The Link file is still an `Axiom` |
| `consoleintr(int)` | SpecConsoleintr / LinkConsoleintr | assumed — but **now provable**: xv6 `a28e94b` removed its `procdump` call, so its callees are exactly acquire / consputc / release / wakeup, all four proven and linked |
| `consputc(int)` | SpecConsputc / ProofConsputc / LinkConsputc | proven + linked |
| `consoleinit(void)` | SpecConsoleinit / ProofConsoleinit / LinkConsoleinit | proven + linked |

## The module's state: `ConsoleInv.v`

`cons` is a static global, so it is much thinner than a pipe: no reference
algebra, no cancellable lock, no reclamation. `is_conslock γ` is
`WpLock.is_lock γ a_cons "cons" cons_res` and is THE WHOLE CREDENTIAL a caller
passes — one persistent proposition, by value.

**`cons_res` is UNCONSTRAINED** — the 128 ring bytes and the three index words,
with nothing relating them. ConsoleInv.v's header argues why at length; the
short version is that the only address computed from an index is
`cons.buf[cons.r % 128]`, compiled as `andi a3,a5,127`, so it is in range for
every value of `cons.r`, and the only thing that FILLS the ring is consoleintr,
and nothing CONSUMES one: a coupling would be a line-discipline claim ("what
was typed is what is read"), and consoleread's bytes leave through
either_copyout into user memory, which this layer does not model.

**The "nobody could establish it" half of that argument expired with the
bump.** Until `a28e94b` consoleintr called procdump and was assumed, so a
coupling would have been a property of an axiom; that call is gone. What
remains is "nobody needs it", which is the honest reason to keep the resource
flat. When a consumer arrives, ConsoleInv.v is where the coupling goes, and
the two places that must maintain it are consoleintr's
`cons.e - cons.r < INPUT_BUF_SIZE` guard and consoleread's `cons.r--`
push-back at +0xe6 — a DECREMENT, safe only because it undoes the `cons.r++`
two instructions earlier.

## How the credentials reach the two functions

fileread/filewrite dispatch through `devsw[major]`, so what the device arm may
ask for is bounded by what the file layer holds. Both `*_dev_env`s gained a
persistent conjunct, and the *column* bundles (`fileread_devsw` /
`filewrite_devsw`, what sys_read / sys_write own) gained the same:

- read side, `fileread_dev_caps` = `is_conslock (frn_cons fn)` — one conjunct,
  because consoleread never touches the UART;
- write side, `filewrite_dev_caps` = `dev_inv (fwn_uart fn) (fwn_disk fn)` ∗
  `is_txlock (fwn_txlock fn) (fwn_uart fn)` — uartwrite's whole credential.

The ripple stops at sys_read / sys_write: `SpecSyscall.syscall_env` is an
abstract parameter and LinkSyscall.v axiomatises the WP, so nothing above reads
those contracts' premise lists.

## consolewrite — PROVEN

`iris/ProofConsolewrite.v` (~1970 lines, 6 `Qed`s, ~11 s / 900 MB to compile).
A CHUNKED COPY LOOP, filewrite's shape one tier down.

- **The bounce buffer is the frame's four lowest slots.** `buf` is `s0-128`,
  which IS the pushed sp, so it is slots 16..13 of a sixteen-slot frame.
  `StackBytes.slotsn_bytes_own` carves them into 32 bytes at the prologue and
  `bytes_own_slotsn` puts them back before the pop. The loop owns `bytes_own`
  (contents unspecified) and NAMES the first `nn` of them per iteration —
  per iteration, not once, because `nn` varies, which is what
  `StackBytes.bytes_own_name` was added for.
- **The loop is rotated.** Head = the test at +0x5e (`n - i`, then the `min`
  with 32); the body at +0x38 is reached from BOTH arms of the `min`, so it is
  an iAssert'ed continuation. Back edge is +0x5a's fall-through. Termination is
  `n - i`, decreasing by `nn >= 1`, so ordinary induction on a fuel `mrem`
  bounding it — the base case is VACUOUS (the head is only entered at `i < n`).
- **The epilogue is shared by three paths** (`n <= 0` at +0x80, loop exit at
  +0x6c, copy-failed at +0x84), so `cw_epi` is a lemma at +0x96 and the two
  nine-load restore runs are one generated lemma applied at two addresses.
- **`cw_cs_hi` is ten equations, not a `forall c, is_cs_idx c = true -> …`.**
  The restores SET s2..s10, so the quantified form would need a case split on
  the thirteen callee-saved indices; ten equations transport through an insert
  tower whose keys are literals, one `upd_ne` per level.
- **The stack constant went 62 → 72**, and that is not slack: 16 own slots plus
  either_copyin's 56, with NO discount for `IntrDefs.trap_res`, because
  consolewrite holds no lock and both its calls are made with interrupts on.
  `SpecFilewrite.filewrite_stack` became `12 + consolewrite_stack` (it was
  `12 + K_writei`); nothing above sys_write reads it.

### Gotchas paid for here (reusable)

- **A bare `iFrame` at `proc_priv` altitude does not terminate** — the tail
  conjunct is `ProcInv.tf_page`'s 4096-element big-op. Intro the tail as ONE
  hypothesis and close with `iExact`. Measured: >2 min on one line, versus
  instant. See [`../optimization.md`](../optimization.md); a file proving over
  `proc_priv` needs this AND `Set Printing Depth 40`.
- **`replace 32 with (nnN + (32 - nnN))` rewrites the 32 inside its own RHS**,
  and the buffer never reassembles. `set` the tail length first and rewrite
  through one equation.
- **`destruct (…) eqn:H` specialises the comparison fact in the Iris context**,
  so the leaf's premise closes by `reflexivity`; the `eqn:` fact is only good
  for the arithmetic afterwards. (durable-notes.md has the general form.)
- `rewrite a b` (space-separated) and `by tac` are ssreflect, so a file that
  does not import the proofmode must use `rewrite a, b`.

## consoleread — WHAT IS LEFT

The contract is written (SpecConsoleread.v) and is `SpecPiperead.v`'s conjunct
for conjunct, with `is_pipe`/`pipe_ref` replaced by the single persistent
`is_conslock`. **ProofPiperead.v is the template and the two functions are the
same animal** — a blocking read into user memory under a spinlock an interrupt
handler also takes. What differs, in the order a proof meets it:

- `either_copyout` rather than `copyout` (one more frame, and the flag is the
  literal 1 — the contract is stated only for the user arm);
- NO `wakeup` on the way out (piperead wakes the writer; the console does not);
- the outer `while (n > 0)` wraps the wait loop, so there are THREE loops'
  worth of structure, not two: an iLöb for the unbounded wait (+0x48), a fuel
  induction on `n` for the outer copy loop, and the `^D` / `'\n'` early breaks;
- the `^D` arm's `cons.r--` at +0xe6, guarded by `bgeu` on `n` vs `target` at
  +0xe2 — the one place a future ring invariant will have to be re-established;
- `killed(myproc())` at +0x48/+0x4c, which piperead also has.

`consoleread_stack` is 62, piperead's, and should hold for the same reason: the
copy happens under `cons.lock`, i.e. interrupts off, where `trap_res true` is
spendable stack; the calls made with interrupts ON are `sleep` (22) and the
re-`acquire` (10), both well inside `62 - 12`.

## consoleintr — NOW IN SCOPE

xv6 `a28e94b` deleted the `case C('P'): procdump()` arm, which is what had
kept this function assumed: procdump walks the whole proc table and prints,
so its footprint was the scheduler's. What is left is 364 bytes whose only
calls are

    +0x014 acquire   +0x050 consputc  +0x0ce consputc  +0x10c release
    +0x128 consputc  +0x130 consputc  +0x166 wakeup

— **all four callees proven and linked**. So the credential is knowable:
`is_conslock` (it takes cons.lock across the whole body) plus consputc's,
which is `dev_inv γd γv` ∗ `is_txlock γl γd` ∗ a `uart_sent_sub γd bs` it
extends (SpecConsputc.v). It is a straight-line switch with one bounded
`while` (the C('U') kill-line loop, bounded by `cons.e - cons.w`), so it has
no iLöb and no park — easier than either of the other two.

Proving it retires this cone's last assumption and makes
`LinkConsoleintr.v` an ordinary functor application; it is also what would
make a line-discipline coupling in `cons_res` worth stating (see above).

## What a relayout costs this cone — measured

Across the `a28e94b` + `2691300` bumps ("no procdump from the console"), which
SHRANK consoleintr and so moved everything after it:

| | changed | of | what |
|---|---|---|---|
| consolewrite | 2 | 68 | both `jal` immediates |
| consoleread | 10 | 94 | all ten `jal` immediates |

**Offsets identical, no AST changed shape, no register reallocation, no frame
or branch-displacement change** — consolewrite/consoleread sit BEFORE
consoleintr, so neither moved or resized, and only their call TARGETS did.
`cons`, `devsw`, `consputc` and `consoleintr` kept their addresses too, so
ConsoleInv.v needed nothing.

So this cone is in the bump playbook's cheapest category, and the repair is:
`make gen-code`, then update the `jal` literals in the proof. Do it by
comparing the regenerated `Code<F>.v` against the proof rather than with
`tools/fix_proof_imms.py` over the whole tree — on an already-bumped tree that
tool's wide window reports a screenful of candidates in files upstream has
already fixed, and none of them are yours.

## Owed elsewhere

- **Boot wiring**: nothing mints `is_conslock` yet. consoleinit's contract
  already hands back the initialized lock word, the sealed `lock_name` and the
  cpu field — `WpLock.newlock`'s raw material — but the ring's own storage
  belongs to whoever owns the .bss, and the assembly that runs `newlock` over
  `cons_res` does not exist. Same debt `UartTxInv.is_txlock` carries, to be
  discharged in the same place.
- **`W32Arith.v` dedup**: the 32-bit ALU laws now have a home, but
  `ProofFilewriteParts.v`'s `fw_subw_moi` / `fw_addw_moi` / `fw_sextw_moi` /
  `fw_bge_moi` and `ProofFilereadParts.v`'s `fr_sext_moi32` are still their own
  copies. Retire them into `W32Arith.v` next time either file is open.
