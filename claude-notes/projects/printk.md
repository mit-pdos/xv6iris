# Project: printk (printk.c / console.c's consputc)

The kernel's formatted-output path, verified bottom-up:

    printk  ->  printint  ->  consputc  ->  uartputc_sync   (proven)
            ->               consputc

Status: **consputc and printint PROVEN** (both sealed and linked); **printk
SPECIFIED** (`SpecPrintk.v` + `PrintkFmt.v` compile; no proof yet).

## The panic-path decision (read this first)

The entire cone is verified on the path where **`panicking != 0` and
`panicked == 0`**, because that is the path `uartputc_sync`'s existing proof
covers (`SpecUartPutc.v`; its `pv`/`pkv` premises say exactly that). This is not
a shortcut, it is the only currently reachable path, and it buys two real
simplifications that show up in every spec of the cone:

- `uartputc_sync` does **no push_off/pop_off**, so nothing in the cone threads
  an `intr_count` and no interrupt bookkeeping appears.
- `printk` skips **both** `acquire(&pr.lock)` and `release(&pr.lock)` (its two
  `if (panicking == 0)` tests fail), so printk's spec needs **no lock
  resource** at all -- `pr.lock` is never touched on this path.

It is also the path that matters most: it is what `panic()` runs, and `panic` is
the one caller that must work when everything else is broken. The general
(`panicking == 0`) path is a strictly larger job and is blocked on
uartputc_sync's own general path -- see "What is left" below.

## The specs

All three follow the spec-module shape (`design/spec-modules.md`): a
`wp_<f>_sconf_body` definition + a `Module Type`, so a proof can be written and
sealed later without any consumer changing. **A `Module Type` with no proof is
not an axiom** -- nothing depends on it until a `Link<F>.v` instantiates it --
so "specified but unproven" is a sound, checkable state.

- **`SpecConsputc.v`** (`CONSPUTC`) -- proven, see below.
- **`SpecPrintint.v`** (`PRINTINT`) -- proven, see below.  The one
  non-boilerplate precondition is
  `10 <= uint base <= 16`, and both ends are load-bearing:
  - upper: `digits[x % base]` indexes a 16-byte table with no check, so
    `base > 16` reads off the end;
  - lower: `buf[20]` holds one byte per digit, and a 64-bit value has at most 20
    digits only once `base >= 10` (19 + the '-' in the negative case). At
    `base = 2` the same code writes 64 bytes and runs off the frame.

  printk calls it only with 10 and 16, so it discharges this.
- **`SpecPrintk.v`** (`PRINTK`) + **`PrintkFmt.v`** -- the interesting one. Three
  parts beyond boilerplate:
  1. the format string as `fmt ↦ₛ{dqf} f` with `nonul f`, handed back untouched;
  2. the varargs, DESCRIBED by the caller (`descs : list pk_arg_desc`, each
     `PkANum` / `PkANull` / `PkAStr dq s`) and required to MATCH the format
     string: `pk_kinds f = map pk_desc_kind descs`. That equation is the honest
     rendering of C's unchecked variadic contract -- a `%s` whose argument is not
     a string is simply unprovable. The varargs are not extra parameters: the
     ABI puts them in a1..a7, so vararg `j` IS `m0 !!! a(j+1)` (`pk_vararg`);
  3. `length descs <= 7`, because printk spills a1..a7 into its OWN frame and an
     eighth `va_arg` would read the caller's frame, which printk does not own.

  `PrintkFmt.v` is the pure model: `pk_dir` classifies the up-to-three
  characters after a `%` (which vararg the arm consumes, how many characters it
  eats), `pk_kinds` runs it over a format string. It is a plain structural
  fixpoint -- every recursive call is on a syntactic tail -- and it mirrors the
  C code's own "read c1 only if c0 != 0, c2 only if c1 != 0", so it never looks
  past the terminator. It carries `Example`s pinning it to real xv6 format
  strings; keep those, they are the cheapest check that the model still matches
  `printk.c`.

**The post of all three is deliberately loose**: `∀ mf bs, ... uart_tx_own γd
(l ++ bs) ∗ uart_sent γd (l ++ bs)`. Some byte list reached the UART; which
bytes is not stated. Nothing in the kernel reads back what was printed, and a
byte-accurate post would have to carry a decimal/hex rendering of every vararg
up through the format recursion. The exclusive-transmitter token comes back
standing for `l ++ bs` so the caller can print again.

## consputc (PROVEN)

`SpecConsputc.v` / `WpConsputcDecode.v` / `ProofConsputc.v` / `LinkConsputc.v`.
Seventeen instructions, a 2-slot frame, one BEQ, and either one or three calls to
uartputc_sync.

The reusable lesson is the **rejoining-arms shape**: the backspace arm's `c.j`
lands on the ordinary arm's `ld ra`, so the epilogue is proved ONCE
(`wp_consputc_epi`) against an arbitrary map `mc` constrained only by what the
join actually guarantees --

    mc !!! sp = the pushed sp     and
    ∀ c, is_cs_idx c = true -> c <> sp -> c <> s0 -> mc !!! c = m !!! c

-- and it turns those back into the caller-visible `callee_saved m mf`. Each arm
proves the agreement from its callees' `callee_saved` hops via a helper
`Hthread0 : ∀ c, is_cs_idx c = true -> mf !!! c = W3 !!! c` (agreement with the
map at the BRANCH, which is unconditional because the arms touch only
caller-saved registers), and only then composes with the prologue's changes.
Deriving sp from the same helper does NOT work through a `c <> sp`-guarded
statement -- state the unguarded "agrees with the branch map" form first and
specialize twice. Splitting the epilogue out this way is also what keeps the
byte-list bookkeeping (one byte on one arm, three on the other) out of the frame
reasoning: the epilogue never mentions the UART.

## New leaves this project added (all in the family files, reusable)

- `wp_li4_s_sconf` (WpSconfAlu) -- the 4-byte `li rd,imm` = `addi rd,x0,imm`.
  NOT an instance of `wp_addi4_s_sconf`, whose post would read
  `m !!! Regidx zreg`; this is the base-encoding twin of `wp_cli_s_sconf`.
- `wp_divu_s_sconf` / `wp_remu_s_sconf` (WpSconfAlu) over
  `exec_execute_DIVU_gpr` / `exec_execute_REMU_gpr` + `gpr_divu_val` /
  `gpr_remu_val` (WpMmodeMul, beside MUL). Taken at `is_unsigned = true`, which
  is what collapses the model's signed-overflow fixup; the divide-by-zero cases
  are the architectural ones (quotient -1, remainder the dividend), so no side
  condition is needed and a call site that knows its divisor closes the
  `Z.eqb .. 0` test by `vm_compute`.
  (The 4-byte `addiw` this cone also needs is `wp_addiw_s_sconf`, which landed
  concurrently with the copyin/copyout work -- a duplicate `wp_addiw4_s_sconf`
  was written here and deleted on the merge.)
- `wp_bge_x0_taken_s_sconf` (WpSconfBtype) -- the taken twin of the existing
  fall lemma; `blez rs2` is `bge x0,rs2`.
- `wp_lbu_s_sconf` (WpSconfMem) is now **dfrac-parametric**. It hardcoded
  `DfracOwn 1`, which cannot read a `kernel_data` image byte (`↦ₘ□`) -- exactly
  what printint's `digits[x % base]` is.

Note `sie_cap_gpr_x0` (IntrDefs) already existed -- it is what lets a call site
reduce `m !!! Regidx zreg` in a leaf post, needed for `neg rd,rs` = `sub
rd,x0,rs`. Do not re-derive it.

## What is left

### printint -- DONE

`WpPrintintDecode.v` (50 instruction facts) / `PrintintArith.v` / `StackBytes.v`
/ `ProofPrintint.v` / `LinkPrintint.v`.  The four reusable pieces, and the traps
each one cost:

- **`StackBytes.v`** -- a C `char` array inside the frame.  `bytes_own dq base n`
  is `n` individually-owned bytes with UNSPECIFIED contents, which is exactly
  what an array of chars is both before and after the loop writes it -- so
  neither loop has to say anything about what it wrote, and the whole
  buffer stays one resource across both.  `slot_bytes_own` / `bytes_own_slot`
  carve a frame word into eight bytes and back (the rebuild is
  `Z_to_bv 64 (assemble_bytes ..)` + `nth_byte_assemble_len`), and
  `slots3_bytes_own` / `bytes_own_slots3` do printint's three slots at once.
  Take the alignment fact out BEFORE splitting -- the bytes no longer carry it
  and the rebuild needs it.
- **`PrintintArith.v`** -- all the arithmetic, deliberately with ByteCursor's
  MINIMAL import set (no iris, no `bitvector.tactics`).  That is not tidiness:
  the zify hook those bring makes `lia` answer "Cannot find witness" on goals
  mentioning a `bv_unsigned`, and half of this file is such goals.  It holds
  `tbt64`/`tbt_moi` (the value DIVU/REMU write, back to a literal),
  `sextw_moi`/`addiw_lit` (the `addiw` round-trip on a small index),
  `digit_step` (the buffer bound), `pa_add_neq_base` (the print loop's
  sentinel compare) and `sign_slot_addr` (gcc's `(i-32)+s0-24` for `buf[i]`).
  Gotcha found here: an inner `bv_wrap` in the MIDDLE of a sum is invisible to
  `bv_wrap_add_idemp_l/r` -- rotate it to the head first (`wrap_add3`).
- **the digit loop** is an induction on a FUEL `f` with `uint x < 10^f` and
  `i + f <= 20`; the body is its own lemma (`wp_printint_dbody`) ending at the
  back-edge branch, so the induction is four short cases.  The fuel is where
  `10 <= base` is spent: `digit_step` turns "the loop continues" into "a
  decimal digit fell off", which bounds the writes.
- **the print loop** is an induction on the descending cursor index, with the
  `consputc` call inside it; s1/s2 survive the call because both are
  callee-saved, which is the whole reason gcc put the cursor and the sentinel
  there.

Two performance/robustness traps worth repeating, both of which cost a >10-minute
hang before being found (`coqc -time` pins them instantly -- the log's last
sentence is the one BEFORE the offending tactic):

- **never `vm_compute` a goal mentioning a symbolic address.**  The epilogue's
  `sp` cancellation must be `apply frame_cancel_64`, not an inline bv block --
  exactly as `design/code-organization.md` says.  Keep the pushed sp available
  in BOTH forms (`add_vec sp0 (sext (caddi16sp_imm 60))` for the cancellation,
  `pa_stk sp0 8` for the slot addresses) and convert with a one-line `assert`.
- **never leave a leaf's value argument as `_` when you pass an inline
  `ltac:` to discharge its premise**: the tactic runs against an evar and
  `vm_compute` diverges.  Pass the term explicitly.

Also: `f_equal` CLOSES a subgoal whose sides are convertible, so
`f_equal. apply bv_eq; vm_compute; reflexivity.` fails with "No such goal" on
half the frame-address lemmas -- write `f_equal; try (apply bv_eq; vm_compute;
reflexivity)`.  And a value bound out of an existential resource arrives as
`bv 8`, so ascribe `(b : mword 8)` at every leaf that wants an `mword`.

### printk (nothing but the spec)

810 bytes / ~200 instructions, ~15 dispatch arms. The pieces:

- the 24-slot frame; the va_list area is slots 1..7 (a1..a7 spilled at
  `8(s0)..56(s0)`, s0 = sp0-64), `ap` itself lives at `-120(s0)` (slot 23), and
  s1/s3..s11 are saved LAZILY at 0x34 and restored at two different points
  (0x74a/0x772) -- two more rejoining arms;
- the format loop is a recursion on the format string, following `pk_kinds`'s
  structure exactly: at each `%`, `pk_dir c0 c1 c2` picks the arm and how far
  the index advances. The loop measure is the remaining suffix;
- ten of the arms are the same shape (load the vararg from the va_list, bump
  `ap`, call printint with a base/sign pair) and should be one parametric lemma,
  not ten copies;
- `%p` is printptr INLINED (a 16-iteration hex loop, 0x6b0..0x6f4) and `%s` a
  string walk (0x70a..0x740) with the `(null)` literal out of `kernel_data`;
- `digits` and the `"(null)"` literal both come from `kernel_data`
  (`kernel_data_window` / `kernel_data_string`, both above `text_end`).

### The general (non-panic) path

Blocked on uartputc_sync: only its `panicking != 0` path is proven
(`ProofUartPutc.v`). The general path adds push_off/pop_off (both proven, and
`WpPushOffTop.v`/`WpPopOff.v` are ready) and hence an `intr_count`, which would
then have to be threaded through consputc, printint and printk. On top of that
printk itself would take and release `pr.lock`, so its spec would grow an
`is_lock` over whatever resource `pr.lock` protects (today: nothing -- see
`ProofPrintkinit.v`, which leaves the lock un-invariant-ed on purpose). Do
uartputc_sync's general path first; everything above it is then a re-threading,
not a re-proof.

## Build note for this tree

`/shared/xv6iris-cleanup` builds in the **`/shared/xv6rocq` opam switch**
(Rocq 9.0.1) -- `eval $(opam env --switch=/shared/xv6rocq)` before any raw
`coqc`/`make`, as `durable-notes.md` says. A fresh shell here defaults to the
`xv6iris` switch (Rocq 9.1.1), which has no `stdpp.bitvector` and fails with
"Cannot find a physical path bound to logical path bitvector.definitions".
