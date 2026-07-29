# the UART driver: uartwrite, uartintr, uartgetc

`uart.c` is **4/4 symbols proven**.  This file covers the interrupt-driven
half — the two functions that share `tx_lock`, plus the one that has no
symbol at all.  (`uartinit` and `uartputc_sync` are older work; the device
model itself is `claude-notes/design/device.md`.)

| function | where | status |
|---|---|---|
| `uartwrite(char buf[], int n)` @ 0x800008dc, 52 instrs, 80-byte frame | SpecUartwrite / WpUartwriteDecode / ProofUartwrite / LinkUartwrite | proven + linked |
| `uartintr(void)` @ 0x800009ce, 39 instrs, 32-byte frame | SpecUartintr / WpUartintrDecode / ProofUartintr / LinkUartintr | proven + linked (over an ASSUMED consoleintr) |
| `uartgetc(void)` — **inlined, no symbol** | WpUartgetc | proven as a block lemma |

All three rest on the definitional layer `UartTxInv.v`.

```c
void uartwrite(char buf[], int n) {
  acquire(&tx_lock);
  int i = 0;
  while (i < n) {
    while (tx_busy != 0)
      sleep(&tx_chan, &tx_lock);
    WriteReg(THR, buf[i]);
    i += 1;
    tx_busy = 1;
  }
  release(&tx_lock);
}
```

## The crux: what licenses the THR store

`wp_uart_thr_write_s_sconf` (WpSconfUartAccess.v) will not push a byte unless
the FIFO provably has room — `uart_tx_ready_persists` (WpUart.v) wants the
transmitter token PLUS `uart_out_lb γu l`, i.e. a THRE observation carried
forward.  uartputc_sync gets that by POLLING LSR.  uartwrite never polls: the
only thing it looks at is the software flag `tx_busy`.

So the certificate has to be *stored in the software state*, and that is what
`UartTxInv.tx_res` does:

```coq
tx_res γu := ∃ (b : mword 32) (l : list (bv 8)),
   a_tx_busy ↦₄ b ∗ uart_tx_own γu l ∗
   (⌜ b = mword_of_int 0 ⌝ -∗ uart_out_lb γu l)
```

Read it as: *`tx_busy == 0` is the software's record of a THRE observation.*
uartintr is the writer of that record (it checks `LSR & LSR_TX_IDLE` and only
then clears `tx_busy`), uartwrite is its reader.  The implication form is what
makes both directions one line: the reader learns `uart_out_lb` from the `lw`
that returns 0, and the writer re-closes with `tx_res_busy` (no certificate,
`b = 1`) at the `sw s6,0(s1)` one instruction after the push.

**Consequence — the transmitter token cannot live with a caller.**  uartintr
needs it (to read the trace out at the THRE check, via `uart_tx_poll_thre`) and
uartwrite needs it (to push), and the two meet only under `tx_lock`.  Hence
`is_txlock γl γu` is the WHOLE credential a caller passes: the lock (whose
resource is the cell + the token) plus the persistent `uart_dlab_off`.

## uartwrite

### Open tension with uartputc_sync (for whoever wires up boot)

`SpecUartPutc.wp_uartputc_sconf` takes `uart_tx_own γd l` FROM ITS CALLER, and
the token is exclusive.  Once `tx_lock` owns the token, the printk cone
(printk → consputc → uartputc_sync) has no way to obtain one — which is
accurate about the C, where `uartputc_sync` deliberately does not take
`tx_lock` and really can interleave its bytes with `uartwrite`'s.  Nothing is
broken today (neither cone is linked to a boot proof yet), but the two specs
cannot both be discharged from one `uart_ghosts_alloc`.  When that seam
matters, the likely fix is to let the PANIC path (`panicking != 0`, which is
all uartputc_sync is verified for) take the token out of `tx_res` — a panicking
hart is not sharing the UART with anyone — rather than to weaken the token.

## The contract's output claim: `uart_sent_sub`, not `uart_sent`

uartwrite SLEEPS between bytes, so other harts' bytes may be accepted in
between; a contiguous `uart_sent γu (l ++ buf)` is simply false.  The honest
claim is `UartTxInv.uart_sent_sub γu bs := ∃ tr, uart_sent γu tr ∗ ⌜bs `sublist_of` tr⌝`
— *every byte of the buffer was accepted by the UART, in order, possibly
interleaved*.  Persistent (so it costs nothing to thread) and monotone.

Two `dev_inv` lemmas make it work, both plain fupds run under `fupd_wp` (no
physical step — the WP is at mask ⊤, so `iApply fupd_wp` then `iMod` is all it
takes):

- `uart_tx_own_snapshot` — the token pins the accepted trace, so it yields the
  persistent record at the CURRENT value.  Used once, right after `acquire`, to
  give the `n = 0` path something to return.
- `uart_tx_own_sent_sub` — an EARLIER record is a prefix of the trace the token
  now names, so the accumulated sublist claim carries over to the trace the
  next push is about to extend.  Used once per byte, immediately before the
  THR store.  This is what re-links across the sleep.

`n` is a `nat` in the spec (a caller with a non-positive count has nothing to
pass), so the C's `n <= 0` guard is exactly the `n = 0` arm.

## Proof structure (ProofUartwrite.v, ~1500 lines)

| lemma | covers | technique |
|---|---|---|
| `uw_tail` | +0x7c → return | release, 4 restores, frame pop, `c.ret` |
| `uw_one` | one iteration: head +0x6c, sleep retry, body | two nested iAsserts |
| `uw_iter` | the whole loop | `nat` induction on bytes remaining |
| `wp_uartwrite_sconf` | prologue, acquire, `blez`, setup, loop, 5 restores | — |

- **The two loops are different beasts.**  The outer one is bounded by `n`, so
  it is an INDUCTION (`uw_iter`, on `k` with `i + S k = n` — the `S` matters:
  the head is only ever entered with at least one byte left, so a plain
  `i + k = n` would leave an unprovable `k = 0` case).  The inner
  `while (tx_busy) sleep()` is unbounded, so it is an iLöb (`SleepLoop`, an
  iAssert inside `uw_one` proved `with "[]"` from the persistent context).
- **`Body` is an iAssert because TWO edges arrive at +0x5a**: the `c.j` at
  +0x70 (tx_busy was already 0) and the sleep loop's fall-through at +0x58.
- **THE TWO LOOP EXITS ARE OFFERED AS A CONJUNCTION**, not a separating one:
  `uw_next_cont ... ∧ uw_exit_cont ...`.  Exactly one is taken, and both need
  the caller's tail continuation, so `∗` is unprovable and `∧` is exactly
  right (`iSplit` at the supply site duplicates the context; `iDestruct "H" as
  "[H _]"` picks a side at the use site).  Same recipe as pipewrite's
  `pw_exits`.  This is what let the induction supply a DEAD back edge in the
  `k = 0` case (`iIntros (M') "%Hlt". exfalso. lia.` — `exfalso` works because
  an Iris goal is `envs_entails Δ P : Prop`).
- **The shrink-wrapped registers are what makes the two paths joinable.**
  gcc saves s2/s3/s4/s6/s7 AFTER the `blez` and restores them before the
  release, so on the `n = 0` path those five slots are never written.  The
  epilogue therefore owns them EXISTENTIALLY (`uw_gap5`) and both paths hand it
  the same shape; `uw_saved5_gap` weakens the loop path's version.
- `subst n` is the move at the loop exit and on the `n = 0` arm: with
  `S i = n` (resp. `n = 0`) in hand it makes `uw_bytes f (S i)` and the goal's
  `uw_bytes f n` the same term, instead of fighting `rewrite` over an `n` that
  also appears in `buf n`/`uw_buf`.

## Gotchas paid for here (reusable)

- **`++` in a TACTIC argument parses in `string_scope`** in these files
  (`iExists (l ++ [c])` → "expected type string").  Write `(l ++ [c])%list`.
  In a Definition body under `%I` it is fine.
- **`sublist_app` / `sublist_nil_l` / `sublist_inserts_r` resolve to a STRING
  lemma** once WpUart's import closure is loaded; qualify them
  (`stdpp.list_relations.sublist_app`).  `` `sublist_of` `` notation itself is fine.
- `f i : bv 8` needs an `(f i : mword 8)` ascription wherever it feeds
  `zero_extend'`/a leaf's value argument (the usual mword-vs-bv trap).
- `rewrite bv_zero_extend_unsigned`'s side goal is an `N` inequality that
  `lia` cannot do under the bitvector zify hook — `first [done | vm_compute;
  discriminate | lia]`.
- `destruct (…) eqn:H` REWRITES the matched scrutinee in every hypothesis
  mentioning it, so a comparison fact asserted beforehand (`Hcmp0 : … = Z.geb 0 n`)
  already reads `… = true` in the branch — pass `Hcmp0`, not the `eqn` fact.
- A `split_and!` followed by a uniform peel tactic can close MORE goals than
  expected; when the leftover count is not obvious, use
  `split_and!; first [ exact <the odd one> | <the uniform peel> ]` rather than
  bullets (a wrong bullet count reads as "Wrong bullet -: Try unfocusing").
- `pa_add_eqb` (ByteCursor.v) reads the `beq s4,s5` loop-exit test back as
  `Nat.eqb (S i) n` with NO no-wrap assumption on the buffer — do not re-derive
  a canonicality argument for it.
- uartwrite's 80-byte frame is BYTE-IDENTICAL to copyinstr's (same slots, same
  registers, same order), so the whole prologue/epilogue decode layer is
  KernelRvcDecode's shared `cdec_*` helpers.

## uartintr — the other half of `tx_res`

```c
void uartintr(void) {
  ReadReg(ISR);                       // acknowledge
  acquire(&tx_lock);
  if (ReadReg(LSR) & LSR_TX_IDLE) { tx_busy = 0; wakeup(&tx_chan); }
  release(&tx_lock);
  while (1) { int c = uartgetc(); if (c == -1) break; consoleintr(c); }
}
```

uartintr is what makes the invariant's implication ever TRUE again after
uartwrite has set the flag, and the proof is exactly that step: the LSR read
is taken WITH the transmitter token (borrowed out of `tx_res`), so the leaf
hands back `⌜lsr_thre_clear b = false⌝ -∗ uart_out_lb γu l`; on the arm where
the branch is taken that hypothesis holds, so the certificate is in hand two
instructions before the `sw zero` that clears `tx_busy`, and `tx_res_idle`
re-closes the invariant with it.  The other arm re-closes with the cell and
the wand it borrowed.  **That single move is the whole reason both functions
exist in one design.**

- **The rx half needs no ghosts at all.**  `DevModel.uart_read_stable` — new,
  and the one model fact this work added — says NO uart read moves
  `uart_acc` / `u_out` / `uart_dlab` (only the RHR read advances the device,
  and it pops the RECEIVE FIFO).  So `WpSconfUartAccess.wp_uart_read_free_s_sconf`
  is a UART read at ANY of the eight offsets with `R := emp` and no ghost
  obligation, and that is why the drain can legitimately run AFTER the
  release, as the C does.  One leaf covers the ISR acknowledge, uartgetc's
  rx-ready poll and its RHR pop.
- **The rx loop is an iLöb**, not an induction: nothing bounds how many bytes
  the device supplies.
- **`ui_after_tx` is a lemma, not a continuation**, because both arms of the
  THRE test reach the release at +0x2e (the tx arm jumps BACK to it from
  +0x6a).
- The LSR read leaf had to be generalized over the DISPLACEMENT
  (`wp_uart_lsr_read_ea_s_sconf`): uartputc_sync does `lbu a5,0(a4)` off a
  base holding UART0+5, uartintr does `lbu a5,5(a5)` off one holding UART0.
  The old zero-displacement name survives as a restatement (the WRAPPER
  RECIPE), so ProofUartPutc did not change.

### consoleintr is ASSUMED — and what that hides

`SpecConsoleintr.v` + `LinkConsoleintr.v` (an `Axiom`, the second file of that
kind after LinkKerneltrap.v; `MANIFEST_ASSUMED` in `tools/proof_coverage.py`
reports it).  The contract is `wakeup`'s shape: the running-thread bundle in,
every callee-saved register and the nesting level back out.

What it hides is worth naming: consoleintr ECHOES, so it calls consputc and
hence uartputc_sync, which really does touch the UART — a proven consoleintr
could not have a contract silent about the transmitter.  In the C that is a
genuine race (uartputc_sync deliberately does not take tx_lock).  So the
assumption asserts more than "consoleintr is unproven": it asserts that the
echo is invisible to uartintr's caller, which is true of the register and lock
state but not of the device.  Same seam as the uartputc_sync tension above.

## uartgetc — a function with no address

`static int uartgetc(void)` is called once, so gcc inlines it: **there is no
`uartgetc` in KernelSyms.v**, and the symbol-driven coverage report cannot
count it.  What is in the image is its body, four instructions at
uartintr +0x44..+0x4c, with the C's `c != -1` test fused into the caller's
loop branch — the `-1` is never materialized; the `beqz` on the rx-ready bit
IS it.

`WpUartgetc.wp_uartgetc_inline` states it the only way the compiled kernel
admits: a block lemma parameterized by its four instruction addresses and its
two exits ("no input", at the branch target; "a byte", at the instruction
after the RHR read, with the byte in a0).  The two exits are an `∧` for the
usual reason.  Reach for this shape for any other `static` helper gcc inlines.

## Remaining work

- **consolewrite** is uartwrite's only caller (`console.c`, via a 64-byte
  bounce buffer filled by `either_copyin`); its proof is what would first
  exercise that contract.  **consoleread** and **consoleintr** are the rest of
  console.c; proving consoleintr retires this cone's only assumption.
- **Boot wiring**: `new_txlock` (UartTxInv.v) is the ghost step that turns
  uartinit's postcondition — the zeroed lock word, the `tx_busy` cell and the
  transmitter token from `uart_ghosts_alloc` — into `is_txlock`.  Nothing calls
  it yet; it belongs with the rest of the parked boot wiring
  (`completed/interrupt-sweep.md`).
- **devintr** is uartintr's caller (via the PLIC claim); wiring it up is what
  puts the handler on the trap path.
- The `uartputc_sync` token tension above.
- Decode hygiene: four base words (`lui a5,0x10000`, `andi a5,a5,32`,
  `auipc a5,0xa`, `lbu a0,0(s2)`) moved into KernelBaseDecode.v for uartintr;
  the private copies in WpUartinitDecode.v / WpUartPutcSync.v /
  WpPrintkDecode.v are now redundant and the next decode sweep can retire
  them.
