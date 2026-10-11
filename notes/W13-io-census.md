# W13 I/O census: MMIO dataflow, rule 9, risk R5 (read-only)

Early-warning analysis for W13 (K) risk R5 and (F-dep)'s rule-9 class. This is not a §C item, and no
Lean was edited. **Source of truth:** `Xv6/KernelImage.lean` (xv6-riscv b72cbac1, branch verified),
with function boundaries taken from its `<sym>` comments. C intent comes from the `Xv6/Spec*.lean`
headers named in the brief. Plan references are to `notes/weak-allocproc-plan.md`.

**State of the label in this workspace.** The MMIO arms of `pnodeStep` emit `LDev .rd/.wr` with a
payload (`Weak/WeakEvInst.lean:305,341`), and devAddr is the criterion (`MachCSL/Dev/Fabric.lean:126`:
`pa < 0x80000000`, decided on the PHYSICAL address). So uservec's TRAPFRAME accesses are RAM (VA
0x3fffffe000, PA a kalloc page).

## 0. Inventory

### Hart MMIO accesses (every static site in the image)

| device | loads (pc) | stores (pc) |
|---|---|---|
| UART (base from `uarts[i].base`, RO after boot) | uartwrite LSR `0x80000976`; uartputc_sync LSR `0x800009ec`; uartintr ISR `0x80000a36`, LSR `0x80000a3a`, LSR `0x80000a5c`, RHR `0x80000a64` | uartinitone ×7 `0x800008a0 8aa 8b2 8b8 8be 8c6 8d4` (×2 ports); THR `0x80000988` (uartwrite), `0x800009fa` (uartputc_sync) |
| PLIC `0xc000000` | plic_claim SCLAIM `0x80005886` | plicinit `0x8000582c 82e 830`; plicinithart SENABLE `0x80005856`, SPRIORITY `0x80005864`; plic_complete `0x800058aa` |
| virtio `0x10001000` | init: MAGIC `0x80005950`, VERSION `0x80005964`, DEVICE_ID `0x80005972`, VENDOR `0x8000597e`, DEVICE_FEATURES `0x800059a2`, STATUS `0x800059bc`, QUEUE_READY `0x800059d0`, QUEUE_NUM_MAX `0x800059dc`; intr: INTERRUPT_STATUS `0x80005d4a` | init: STATUS `0x80005992 998 99c`, DRIVER_FEATURES `0x800059b2`, STATUS `0x800059b6`, QUEUE_SEL `0x800059cc`, QUEUE_NUM `0x80005a42`, the six address regs `0x80005a46 a4c a5a a60 a6a a70`, QUEUE_READY `0x80005a76`, STATUS\|DRIVER_OK `0x80005a9c`; NOTIFY `0x80005c92`; ACK `0x80005d52` |
| none | — | `unreachable` `sb zero,0(t0)` to `0xe000000` at `0x8000086c`: devAddr is true but `devDecode` = none (`Fabric.lean:129-135`), so `devWrite` = none and `pnodeStep` has no successor. Not a realizable event. |

That is 16 static MMIO loads. `kvmmake`'s `lui 0x10000/0x1000a/0x10001/0xc000`
(`0x8000117c–0x800011ae`) are page-table arguments, not accesses.

### Memory fences (decoded by hand: pred = bits 27:24 PI PO PR PW, succ = bits 23:20 SI SO SR SW)

| pc | word | decoded | PW∧SR? |
|---|---|---|---|
| `0x80000cf6` (release), `0x80000f7a` (main, before `started := 1`) | `0x0310000f` | fence rw,w | no (no SR) |
| `0x80000ee6` (main, `started` spin, harts ≥ 1 only) | `0x0230000f` | fence r,rw | no (no PW) |
| `0x80005c7a`, `0x80005c8a` (rw, before NOTIFY), `0x80005d54`, `0x80005d66` (intr) | `0x0ff0000f` | fence iorw,iorw. With menvcfg = 0 the i/o bits are dead, so on memory this is **rw,rw**. | yes |

The image has exactly one AMO: `amoswap.w.aq` at `0x80000c74` (acquire). It has no lr/sc.

## (a) MMIO-load table

Each value is traced to a fixpoint through registers, callee-saved spills, call arguments and stack slots.

| pc | register | function | consumers (classified) | rule-9 status |
|---|---|---|---|---|
| `0x80000976` | UART0 LSR | uartwrite | **ctrl** (`andi` `0x8000097a` → `beqz` `0x8000097e`) | none |
| `0x800009ec` | UARTn LSR | uartputc_sync | **ctrl** (`0x800009f0` → `beqz` `0x800009f4`) | none |
| `0x80000a36` | UARTn ISR | uartintr | **none**: a dead value. `a4` is overwritten at `0x80000a56` and is not read on the wakeup path (`wakeup` never reads `a4`). | none |
| `0x80000a3a` | UARTn LSR | uartintr | **ctrl** (`0x80000a3e` → `bnez` `0x80000a42`) | none |
| `0x80000a5c` | UARTn LSR (inlined uartgetc) | uartintr | **ctrl** (`andi 1` → `beqz` `0x80000a62`) | none |
| `0x80000a64` | UARTn RHR (uartgetc pop) | uartintr | **Port 0** (`rx` = consoleintr, `.data` `0x8000a398`). The byte goes via `zext` to `a0`, then `jalr` `0x80000a70` into consoleintr `s1`. **ctrl:** `0x800002e2 2ea 2f0 2f4 312 340 344` and consputc `beq a0,256` `0x80000298`. **data→RAM store:** `cons.buf` `sb s1,24(a4)` at `0x80000338`, plus spills of `s1` in acquire `0x80000c5e`, uartputc_sync `0x800009b2`, release `0x80000ce6` and wakeup `0x80002046`. **data→I/O store:** consputc → `uartputc_sync(0,c)` puts it in `s5`, then `zext` `0x800009f6`, then THR `0x800009fa`. **Port 1** (`rx` = 0, `0x8000a3c0`): no consumer. The pop is discarded and `a0` is overwritten (next RHR, or devintr `mv a0,s1` `0x8000267e`). | none |
| `0x80005886` | PLIC SCLAIM(hart) | plic_claim | **ctrl:** devintr `beq` `0x80002660 666 66c`, `bnez` `0x80002672`; printint `bltz` `0x8000049c`, `bgeu` `0x800004d0`. **data→I/O store:** `mv a0,s1` `0x8000267e` → plic_complete `sw s1,4(a5)` `0x800058aa`. **data→RAM store:** `s1` spills in uartintr `0x80000a1c`, virtio_disk_intr `0x80005d2e`, plic_complete `0x80005896`, acquire `0x80000c5e` (via printk's `acquire(&pr)`) and printk `0x80000560`; printk vararg slot `sd a1,8(s0)` `0x80000532`; printint digit `sb a5,0(a3)` `0x800004c4`. **addr→plain RAM LLoad:** `lbu a5,0(a5)` `0x800004c0` = `digits[irq % 10]`. **data→I/O store (via the stack buffer):** `lbu a0,0(s1)` `0x80000504` → prputc → THR `0x800009fa`. | **D-8-masked** (`0x800004c0`) |
| `0x80005950` / `964` / `972` / `97e` | MAGIC / VERSION / DEVICE_ID / VENDOR_ID | virtio_disk_init | **ctrl** (`bne` `0x8000595c 96a 976 98a`) | none |
| `0x800059a2` | DEVICE_FEATURES | virtio_disk_init | **data→I/O store** (`and` → DRIVER_FEATURES `0x800059b2`) | none |
| `0x800059bc` | STATUS | virtio_disk_init | **ctrl** (`andi 8` → `beqz` `0x800059c4`); **data→I/O store** (`ori 4` → STATUS `0x80005a9c`). `s2` is never spilled: kalloc, memset, acquire, release, push_off, pop_off, holding and mycpu save only `s0`/`s1`. | none |
| `0x800059d0` / `0x800059dc` | QUEUE_READY / QUEUE_NUM_MAX | virtio_disk_init | **ctrl** (`0x800059d4`; `0x800059e0`, `0x800059e6`) | none |
| `0x80005d4a` | INTERRUPT_STATUS | virtio_disk_intr | **data→I/O store** (`andi 3` → ACK `0x80005d52`) | none |

**Classes that never occur:** addr→RAM store, addr→I/O access, addr→LR/AMO. Every MMIO base comes
from a constant `lui` or from RAM `uarts[i].base`. PLIC context addresses come from `cpuid()` (`tp`),
never from `irq`.

**Detail of the printk/printint path.** devintr hands `irq` to `printk("unexpected interrupt
irq=%d\n", irq)` (`0x80002698`; format literal at `0x80007270`). The vararg is spilled to the stack
at `0x80000532`. The `%d` arm reloads it with `lw a0,0(a5)` at `0x800005fe`; `a5` is the va pointer
from `-120(s0)` and does not depend on `irq`. Then `printint(a0,10,1)`:
- `neg` `0x8000051e`
- `remu` `0x800004ba`
- `add` with `digits` (`0x80007730`)
- the masked load `lbu` `0x800004c0`
- `sb` `0x800004c4`, a data dependency through the digits load
- `divu` `0x800004ca`

The print loop's `lbu a0,0(s1)` at `0x80000504` takes its address from `s2 + a4`. Here `a4` is the
digit count, an `addiw` chain from 0 that is only control-dependent on `irq`. So the THR byte reaches
`irq` only through rf on the stack buffer, never through a register dependency.

**Beyond the brief's fixpoint (checked anyway).** The `cons.buf` byte is later read by consoleread
`0x80000206` under `cons.lock`. Its index is `cons.r`, not the byte. Its consumers are ctrl
(`0x80000210`, `0x80000232`) and data via the stack (`0x80000214`) → either_copyout, a RAM store
whose address is not byte-derived.

**The D-8-masked instance's location is never written.** `digits` is in W3's pristine window
`[bcRoLo, bcRoHi) = [0x80000000, 0x8000a380)` (`Xv6/BootCarve.lean:143-144`). Two facts cover it:
- `textPristine` (`Xv6/TextPristine.lean:36`): every history in the window is the fresh era's.
- `kernelData_digits` (`Xv6/KernelData.lean:2420`): a `DFrac.discard` byte buffer.

So it is read-only forever and has no fr successor.

**Jump tables.** None of the three suspected switches compiles to a table:
- consoleintr is a `beq` chain (`0x800002e0–0x800002f4`; no `^P` arm).
- devintr is a `beq` chain (`0x8000265e–0x80002672`).
- printk's format switch is a `beq` chain (`0x800005be–0x8000080c`).

The image's only table jump is argraw `jr a5` at `0x80002870` (table `0x80007778`, indexed by the
argument number `n`). The other indirect jumps are uartintr `jalr` `0x80000a70` (target `u->rx`, RO
`.data`), syscall `0x800029da` (`syscalls[]`, index from the trapframe), fileread/filewrite
(`devsw[]`), forkret and the trampoline. None has an MMIO index.

**(F-dep) coverage check.** In-edges into I/O events come from RAM sources (`uarts[i].base`, `disk.*`
pointer words), so (R1) covers them. Data edges from I/O load to I/O store
(FEATURES→DRIVER_FEATURES, STATUS→STATUS, STATUS→ACK, irq→complete, RHR→THR echo) are covered by (R3).
I/O load → RAM store edges (data, and ctrl via the never-reset `dtCtl`) are covered by (R2). The one
class beyond the residue is I/O load →addr→ RAM load, which occurs once and is D-8-masked, so no edge
is emitted. Its LR/AMO form, the graph hit, does not occur: no acquire call site's `a0` is reached by
any traced MMIO value, because the uartintr/uartwrite `uid` arguments are constants chosen by control
(`0x80002678`, `0x8000268a`, `0x80000128`).

## (b) R5

### b.0 Key finding: a segment that passes through an I/O event is pinned by composition

R5 (plan:1174-1175) says an I/O-entry / READ-exit segment has no fence pin, so it must close by lock
discipline, or else it is a STOP. That is true of the **direct** pins: `segPin`
(`Weak/WeakRvwmoGlue.lean:233`) is one rule-4/5/deps edge from entry to exit, and rule 4 skips I/O
events. But a segment is an `rtc rsame` path (`Glue.lean:101-102,148-154`), and `Cert.Pinned` only
needs `gmoLt entry exit` (`KillArms.lean:294`). Composition gives that, as follows.

**Claim L-IO.** This is an argument, not checked in Lean. Take (K)'s same-row relation as
rsameIO := `gpow ∨ gppo ∨ deps ∨` the same-row arms of `ioResidue` ((R1), (R2), (R3)-po, (R2′)).
Suppose an rsameIO path from `entry` to `exit` visits an I/O event. Then `entry = exit` or
`gmoLt entry exit`.

*Proof sketch.* Let `x` be the first I/O event on the path. Every non-I/O-to-I/O step is po-forward.
- **Prefix.** If `entry ≠ x`, then `entry` is po-before `x`. It is RAM, so (R1) gives `entry <gmo x`.
- **Suffix.** Induct on the steps after `x`. Keep as anchor `z` the last I/O event so far, with
  `x ≤gmo z`; the base case uses (R3), and a cross-row `gfBefore` step is also covered by (R3).
- **Each next event `y`:**
  - a RAM write: `gpo z y`, so (R2) gives `z <gmo y`;
  - an I/O event: (R3);
  - a RAM read that is not a write: its in-edge cannot be `gpow`, (R1), (R2) or (R3), which all
    target writes or I/O. So the in-edge is `gppo` (`gppoGmo`), `deps` (`rvwmoMinusDepsConsistent`'s
    deps ⊆ gmo, `Glue.lean:237,240`; (F-dep)'s new edges must satisfy this too), or (R2′) (by (T)). Its
    source is gmo-after `x` or is `x` itself, so `x <gmo y`.

Every cross kind is ⊆ gmo: `gcross` by `gcrossGmo`, and gmo|IO by definition. So the segment carries
a `Pinned` certificate (with (K)'s generalized cross relation), and the I/O event acts as a composite
pin. ∎

**Consequence.** If a racy read `r` is po-after an I/O event `x` but is not rsameIO-reachable from
`x`, then `x` and `r` are in no common segment of any racyDIO cycle. If `r` is reachable, then
`x <gmo r`. So the (a′) point (reads po-after I/O stay unordered) is a statement about po, and it
never surfaces as an unpinned segment. The per-site table below is still given, as the brief asks.

**Caveat for the W12 cat chain (the target).** `racyDSplitC` moves rfi into `rsameC` (plan:426-427).
rfi is not ⊆ gmo, because of store forwarding, so the read case gains a sub-case: a read entered by
rfi from a source write `w_r` po-after `x`, which (R2) puts gmo-after `x`. The invariant becomes:
every path event after `x` is gmo-after `x`, **or** is a read forwarded from a write that is
gmo-after `x`. Every ppo/deps step out of such a read either lands on a write ((R2)) or stays in the
class:
- rule 2's other source is co-after `w_r`;
- rule 12's store is po-after `x`;
- rule 3/5 sources are AMOs, which are writes.

The one exception is a fence with PR∧SR but ¬PW. The image's only such fence is `fence r,rw` at
`0x80000ee6`. Harts ≥ 1 reach it only before their first I/O event (main's spin precedes their
printk), and hart 0 skips it (`beqz` `0x80000ee2`).

A forwarded exit `r` is handled definitionally: `gfr r w'` with `r` reading `w_r` gives `gco w_r w'`
(`gfr`/`gco` at `Weak/WeakRvwmoAcyc.lean:184-189`). The (R2) edge `x → w_r` is itself in racyDIO, so
the cycle can be rewritten to exit at `w_r` with a co cross edge.

Unverified for that sub-case: user-mode code after `sret`, which lives in fs-image binaries, not
the kernel image.

### b.1 Scan rules and where the windows end

**Window end.** The window closes at the next `amoswap.w.aq` (`0x80000c74`). A fence with PW∧SR
also closes it, but only with a RAM write between the I/O event and the fence; the only such fences
are the four `0x0ff0000f` in virtio. Neither `fence rw,w` (`0x80000cf6`) nor a plain store closes it.

`holding()` (`0x80000bf2`, `0x80000c04`) and push_off run **before** the amoswap inside acquire.
So every window contains at least one `holding()` read, and so do all the lock-word reads in
`release`.

**Excluded from "racy" (no concurrent writer), with evidence:**
- **Own stack**, and the own trapframe page (uservec `0x8000607e–0x8000608a`).
- **Own `cpus[tp]`.** All writers index by `tp`: push_off `0x80000c3e`, `0x80000c54`; pop_off
  `0x80000cb4`; scheduler `0x80001e64`, `0x80001ea4`, `0x80001eba`, `0x80001ebe`.
- **`uarts[i].base` / `.rx`.** Read-only after boot: `uartBaseWord` / `uartRxWord`, `DFrac.discard`
  (`Xv6/UartInv.lean:63-69`).
- **`digits` and format literals.** `textPristine`.
- **`disk.desc`, `disk.avail`, `disk.used` pointers.** Written only in virtio_disk_init
  (`0x800059f6`, `0x800059fc`, `0x80005a04`), and frozen in `diskGeom`.
- **`kernel_pagetable`.** Written in kvminit only, before `started`.
- **`p->trapframe` of the running process.** allocproc/freeproc only.
- **Everything hart 0 reads during boot** (`main` `0x80000f10–0x80000f6c`). Harts ≥ 1 are in the
  `started` spin (`0x80000ee4–0x80000eec`), whose only access is a read of `started`. The disk row
  has no request before the first NOTIFY, and no user rows exist yet.

### b.2 Table

| # | I/O event(s) | racy reads in the window (pc: location; concurrent writer) | certificate | window ends at |
|---|---|---|---|---|
| 1 | uartputc_sync LSR `0x800009ec`, THR `0x800009fa` (from consputc / prputc) | release(tx): `0x80000bf2` `tx.locked` (other harts' failing amoswap `0x80000c74`); `0x80000c04` `tx.cpu` | **C1**; **C2-held** | next acquire's amoswap |
| 1c | …returning into consoleintr (`cons.lock` still held) | `cons.e`/`cons.w`/`cons.r`/`cons.buf` at `0x80000324`, `0x8000034a`, `0x80000388`, `0x8000039a`, `0x8000039e`, `0x80000404`; release(cons) `0x80000bf2`/`0x80000c04`; wakeup → acquire(proc[0]) `0x80000bf2`/`0x80000c04` | **C3-cons**; C1/C2-held; C1/C2-unheld | amoswap in `wakeup` → acquire, or the next LSR (row 3) |
| 1p | …returning into printk/printint (`pr` held) | next `acquire(tx1)` holding `0x80000bf2`; release(pr) `0x80000bf2`/`0x80000c04`; then printk's caller | C1 (pinned via own release store); C1/C2-held; **C5** | next prputc's amoswap |
| 2 | uartwrite LSR `0x80000976`, THR `0x80000988` | release(tx0) `0x80000bf2`/`0x80000c04`; sleep_prepare → acquire(p->lock) `0x80000bf2`/`0x80000c04` | C1/C2-held; C1/C2-unheld | amoswap in sleep_prepare's or sleep's acquire |
| 3 | uartintr ISR `0x80000a36`, LSR `0x80000a3a`/`0x80000a5c`, RHR `0x80000a64` | (`uarts[i]` excluded) wakeup(u) → acquire(proc[0]) holding; consoleintr → acquire(cons) holding `0x80000bf2`/`0x80000c04` | C1/C2-unheld | that amoswap; or loop exit → row 5 |
| 4 | PLIC delivery (kernelvec/uservec → kerneltrap/usertrap → devintr) and plic_claim `0x80005886` | none before the claim (only stack stores and CSRs; uservec's trapframe loads and usertrap's own-cpu loads are excluded); after the claim, the dispatch: acquire(vdisk)/acquire(pr) holding | — / C1/C2-unheld | the dispatch's first amoswap |
| 5 | plic_complete `0x800058aa` (+ every PLIC claim/complete race: I/O–I/O, (R3)) | devintr, kerneltrap and kernelvec epilogues (own stack); usertrap `killed(p)` → acquire holding; kerneltrap `sret` into interrupted code | C1/C2-unheld; **C5** | usertrap: amoswap in killed; kernel: open (C5) |
| 6 | plicinit `0x8000582c–30`, plicinithart (hart 0), uartinitone ×7, virtio_disk_init, main printk (hart 0) | none (boot exclusion) | — | kalloc's `acquire(&kmem)` `0x80000b90` |
| 6′ | plicinithart `0x80005856`/`0x80005864` on harts ≥ 1 (and their printk) | release(pr)/(tx1) holding; scheduler → acquire(proc[0]) holding | C1/C2; C1/C2-unheld | amoswap `0x80000c74` from scheduler `0x80001e96` |
| 7 | NOTIFY `0x80005c92` | `b->disk` `0x80005c96` (intr `0x80005d92`, under vdisk); `desc[].flags`/`next` `0x80005cf2`/`0x80005cf8`; `disk.free[i]` `0x800058ce`; sleep_prepare/wakeup → acquire holding | **C3-vdisk**; C1/C2-unheld | amoswap in sleep_prepare(b) or wakeup(&disk.free[0]) |
| 8 | INTERRUPT_STATUS `0x80005d4a`, ACK `0x80005d52` | `used_idx` `0x80005d5a`/`0x80005d6c`; `info[id].b` `0x80005d90`; **DMA-written:** `used->idx` `0x80005d5e`, `used->ring[].id` `0x80005d76`, `info[id].status` `0x80005d82`; release(vdisk) holding; wakeup → acquire holding | C3-vdisk; **C4**; C1/C2 | first `wakeup`'s amoswap (fence `0x80005d54` does NOT end the window: there is no RAM write in `(0x80005d4a, 0x80005d54)`) |

### b.3 One paragraph per candidate

**C1. The spinlock word `lk->locked`, read by holding() at `0x80000bf2`.** This read occurs inside
release (`0x80000cec`) and inside acquire before the amoswap (`0x80000c6a`). Writers are the amoswap
`0x80000c74`, the release store `0x80000cfa` and initlock `0x80000be2`. Failing amoswaps of other
harts write it even while this hart holds the lock, so no lock protects it. It is unlocked, and
under the brief's direct criterion it is unpinned; the window ends only at a later amoswap.
**Certificate: Pinned by composition (L-IO).**

In the finite windows above, the rsameIO path from the I/O event usually does not exist at all. In
release(L), the hart's last access to the same word is its own amoswap, which is po-before every I/O
event inside the critical section. The events in between are stack stores, with no fence and a
different byte, so nothing has a ppo or dep edge into `0x80000bf2`. The segment is therefore vacuous.

One case has a **named** composite pin. After the hart's own `release(L)` that follows the I/O event,
the next `acquire(L)` (row 1p: printk's next prputc reacquires `tx1`) reads the word after the
release store `0x80000cfa`. (R2) gives `x <gmo 0x80000cfa`, and `gpoloc` (rules 1–3, same byte, W→R)
continues to `0x80000bf2`. Under cat, that W→R step is rfi, handled by the b.0 caveat. Not a STOP.

**C2. `lk->cpu`, read by holding() at `0x80000c04`.** This read happens only when the C1 read is
non-zero. Its only writers are acquire `0x80000c80` (after a successful amoswap), release
`0x80000cf2` (before the release store) and initlock `0x80000be6`.
- **Held** (inside release): the lock protects this location.
  **Certificate: CSchained.** The lock is `L` itself. The window is [own `0x80000c74`, own release
  store `0x80000cfa`]; `0x80000c04` lies before the release store.
  This needs `lk->cpu` to be in `wprotAt`'s protected set for `L`. KernelPins classifies
  `0x80000c04` as `PResidue` (`Weak/KernelPins.lean:255`), so the RAM kill already depends on the
  same fact. Check the W8 export before (K) relies on it.
- **Unheld** (inside acquire, on a lock another hart holds): the writer is the holder. It is
  unlocked, so **Pinned by composition (L-IO)**. It is vacuous in every listed window, for the same
  reason as C1.

**C3-cons. Console ring fields after a consputc echo** (`0x80000324`, `0x8000034a`, `0x80000388`,
`0x8000039a`, `0x8000039e`, `0x80000404`). Their writers (consoleintr `0x8000032e`, `0x80000338`,
`0x80000390`, `0x800003e8`, `0x8000040e`, `0x8000041a`, `0x80000422`; consoleread `0x800001fc`,
`0x80000264`) all run under `cons.lock`. **Certificate: CSchained.** The lock is `cons.lock`
(`0x80012420`). The window runs from consoleintr's acquire `0x800002dc` (amoswap `0x80000c74`) to
release `0x800003d4` (store `0x80000cfa`). The THR events are inside it; the (R2) step to the release
store is the "(R2)-rerouting through the release" of plan:1174.

**C3-vdisk. Disk driver state under `disk.vdisk_lock`** (`0x80023af8`). In virtio_disk_rw after
NOTIFY:
- `b->disk` `0x80005c96`, written by intr `0x80005d92` under the lock;
- `desc[].flags`/`next` `0x80005cf2`/`0x80005cf8`, written by the driver only
  (`0x80005bea–0x80005c5e`, free_desc `0x800058e4–0x800058f4`); the device only reads descriptors;
- `disk.free[i]` `0x800058ce`.

In virtio_disk_intr after STATUS/ACK:
- `used_idx` `0x80005d5a`/`0x80005d6c`, written at `0x80005da4`;
- `info[id].b` `0x80005d90`, written at `0x80005c66` and `0x80005cdc`.

**Certificate: CSchained.** The lock is `vdisk_lock`. In rw the window runs from acquire `0x80005b26`
(or `0x80005bac`) to release `0x80005cb0` or `0x80005d0c`. In intr it runs from acquire `0x80005d42`
to release `0x80005dba`.

**C4. DMA-written ring words after STATUS/ACK.** These are `used->idx` `0x80005d5e`,
`used->ring[i].id` `0x80005d76` and `info[id].status` `0x80005d82`. The status byte is the device's
`VRING_DESC_F_WRITE` buffer, set at `0x80005c58`/`0x80005c5a`; the driver also writes it at
`0x80005c40` under the lock. The writer is the disk row's DMA, which takes no lock, so lock
discipline cannot apply. Under the brief's direct criterion this read is unlocked and unpinned: the
window passes fence `0x80005d54` because no RAM write precedes the fence after the I/O events. The
plan's "post-ACK loads (the third fence)" are ISA-prose-tier for exactly this reason.

No named invariant refutes the stale read, so **Bad is not available**.

**Certificate: Pinned by composition (L-IO), vacuous in the window.** The candidate predecessors of
`0x80005d5e` are `ld disk.used` `0x80005d58` and `lhu used_idx` `0x80005d5a`. The first gives an
addr edge, which is D-8-masked (rule 9's RAM-load half is omitted) and so absent. The second has no
ppo relation. No PW∧SR fence has a write before it. So no rsameIO path from `0x80005d4a`/`0x80005d52`
reaches these reads.

From the second loop iteration on, the window has already ended at wakeup's amoswap. Even without
that, fence `0x80005d66` would pin these reads, through the writes `0x80005d92`/`0x80005da4` ((R2),
then rule 4).

**C5. Open continuations.** In three places the window runs into code that the census cannot bound:
- **`plic_complete` → kerneltrap → `sret`.** Execution resumes in whatever kernel code was interrupted
  with SIE = 1. That is any process-context code outside spinlocks, e.g. sleeplock-protected buffer or
  inode reads. In the scheduler it is `0x80001ed2`, which reaches acquire.
- **printk returning to its caller.** The callers are balloc, ialloc, ireclaim, install_trans,
  syscall, usertrap, main, devintr and panic. `procdump` (`0x80002412`) has **no caller** in the image
  (dead code), so its unlocked `%s p->name` read is unreachable.
- **uartwrite returning through consolewrite and filewrite.**

**Certificate: Pinned by composition (L-IO), uniformly.** No per-site list is possible here, and
L-IO is the argument that makes one unnecessary.

**Sites the brief named, cross-referenced.**

| site | where it is covered |
|---|---|
| plic_claim/plic_complete races | rows 4, 5 (I/O–I/O via (R3); the RAM reads that follow are C1/C2/C5) |
| plicinit, plicinithart | rows 6, 6′ |
| uartputc_sync (locked; `uid` in `a0` → `s3`) | rows 1, 1c, 1p |
| uartwrite | row 2 |
| uartintr → consoleintr through `u->rx` | rows 3, 1c (`u->rx` at `0x80000a6c` is excluded as read-only after boot) |
| printk/prputc | row 1p, C5 |
| NOTIFY `0x80005c92` | row 7 |
| STATUS read / ACK `0x80005d52` / used-ring reads | row 8, C4 |

### b.4 Names in the plan that are absent from the image

- **`pr.locking`.** `pr` is the data symbol `0x800124c8` with **size `0x18`**, which is exactly one
  `struct spinlock`. initlock writes `+0`, `+8`, `+16` (`0x80000be0–0x80000be6`), and acquire and
  release touch only `+0`/`+16`. There is no `locking` field. printk calls `acquire(&pr)` at
  `0x8000054c` and `release(&pr)` at `0x80000782` unconditionally.
- **`panicked`.** There is no data symbol of that name; the full list is at
  `Xv6/KernelImage.lean:17899-17937`. panic (`0x80000838–0x8000085e`) makes two printk calls and then
  self-jumps at `0x8000085e`; it writes no flag. uartputc_sync (`0x800009ac–0x80000a14`) and uartwrite
  check no flag.
- **`uartstart`.** There is no such symbol; the uart functions are uartinitone, uartinit, uartwrite,
  uartputc_sync and uartintr. Transmit is synchronous: uartwrite writes THR at `0x80000988` under
  `tx_lock` and sleeps when LSR is not idle, with no tx ring. `uartstart` also does not appear anywhere
  in `notes/weak-allocproc-plan.md`.
- The only racy flag the image actually has is **`started`** (`0x8000a400`). Its writer is
  `0x80000f7e`, after `fence rw,w` `0x80000f7a`; its reader is `0x80000ee4`, followed by
  `fence r,rw` `0x80000ee6`.

## (c) Cross-check of §B(11)'s per-arm trusted uses (plan:659-669) against the image

**Confirmed as written.**
- uartinitone's seven WriteRegs: `0x800008a0` … `0x800008d4`.
- plicinit (`0x8000581e`) and plicinithart (`0x8000583a`).
- uartputc_sync's LSR read `0x800009ec`, after the lock's store half (amoswap `0x80000c74`,
  `lk->cpu` store `0x80000c80`).
- virtio_disk_intr's STATUS read `0x80005d4a`.
- THR.
- NOTIFY `0x80005c92`, not followed by any fence.
- plic_complete `0x800058aa`.
- ACK `0x80005d52`, the only device store with a fence after it (`0x80005d54`).
- The two pre-NOTIFY fences `0x80005c7a`/`0x80005c8a` and "the third fence" `0x80005d54`.
- The unlocked claim/complete races: no lock in `0x80005870–0x800058b4`.
- "UART then PLIC in main": uartinit by way of `0x80000f10`, then plicinit at `0x80000f54`.

**Omissions.**
1. **(R1) at uartwrite's LSR `0x80000976` and THR `0x80000988`.** The shape is the same as the listed
   uartputc_sync use (acquire at `0x8000096e`, then the lock's store half). Only uartputc_sync is
   named.
2. **(R1) in virtio_disk_init, which has no fence.** RAM stores precede MMIO stores in four places:
   - the ring-pointer stores `0x800059f6`, `0x800059fc`, `0x80005a04`, and kalloc's three memset
     zeroings (memset `0x80000d2c`, called at `0x80005a1c`, `0x80005a2e`, `0x80005a38`), before
     QUEUE_NUM, the address registers and QUEUE_READY (`0x80005a42–0x80005a76`);
   - `free[0..7] = 1` (`0x80005a78–0x80005a94`) before DRIVER_OK `0x80005a9c`;
   - initlock's stores before MAGIC `0x80005950`;
   - kalloc's `acquire` and `release` stores.
3. **(R1) for stores after a delivery and before the claim.** §B(11) lists stores before the PLIC
   delivery only. These come after it:
   - kernelvec's saves `0x800057c2–0x800057e2`;
   - uservec's trapframe saves `0x8000600c–0x8000607a` (physically RAM);
   - usertrap's `epc` store `0x800026de`;
   - the devintr/plic_claim prologue saves (e.g. `0x80002654`).

   All of these are RAM stores po-before `0x80005886`.
4. **(R1) for handler-body stores before plic_complete `0x800058aa`, and before uartintr's
   next-iteration LSR `0x80000a5c`.** Examples: cons stores `0x8000032e`/`0x80000338`, `b->disk := 0`
   `0x80005d92`, `used_idx` `0x80005da4`, release stores `0x80000cfa`.
5. **(R2) for device stores not listed.**
   - plicinit's `0x8000582c`/`0x8000582e`/`0x80005830`: no fence follows them.
   - uartinitone's seven stores, followed by initlock's RAM stores `0x80000be0`/`0x80000be2`/
     `0x80000be6`.
   - virtio_disk_init's MMIO stores, followed by kalloc, memset and `free[]` stores.
6. **(R2) for I/O loads (a presentation gap, no real use is missing).** The arm is stated for any
   I/O event, but §B(11) lists stores only. Under (F-dep) every load whose value is branched on
   ctrl-pins all later stores (rule 11; `dtCtl` is never reset), so those are graph facts. Two loads
   remain:
   - STATUS `0x80005d4a`: subsumed through ACK.
   - ISR `0x80000a36`: dead, and no store lies between it and LSR's branch `0x80000a42`.
7. **(R3) cross-channel order beyond "UART then PLIC in main".**
   - PLIC→virtio in main (`0x80000f58` → `0x80000f68`).
   - UART1→PLIC on harts ≥ 1 (printk `0x80000efc` → plicinithart `0x80000f08`).
   - Inside every handler: PLIC claim → UART (ISR/LSR/RHR, consputc echo THR on UART0, the
     unexpected-irq printk THR on UART1) or virtio (STATUS/ACK) → PLIC complete. The irq→complete
     and RHR→echo pairs are dependency-pinned (graph facts under (F-dep)).
   - Process context: UART0 THR (consolewrite) and virtio NOTIFY in the same row.

**Stale or misdescribed entries.**
1. **"the racy flags `pr.locking`/`panicked`"** (plan:669). The same entry is repeated at R5 :1175,
   :446 and :1338. Both are absent (b.4). The image's racy flag is `started` (b.4), plus `ticks` and
   `p->killed`, which are lock-read.
2. **R5's candidate list** (plan:1175) names `pr.locking`/`panicked` (stale), and also plicinithart
   and the claim/complete races. Per b.0 and b.2 these are not STOP candidates. For the races, R5's
   I/O–I/O part is (R3), and the RAM reads that follow are C1, C2 and C5.
3. **"UART LSR" listed among the "racy flag reads"** (plan:446). LSR (`0x80000976`, `0x800009ec`,
   `0x80000a3a`, `0x80000a5c`) is an MMIO read (`LDev .rd`), not a RAM racy flag. KernelPins does
   classify those pcs as `PCtrl` load sites (`Weak/KernelPins.lean:205,216,226,228`), because its
   generator does not separate MMIO loads.
4. **Citation drift (minor).** These are the line numbers as checked in this workspace; the plan and
   brief cite slightly different lines.

   | cited | actual |
   |---|---|
   | D-8 plain-`LLoad` `asrc = []` | `Weak/WeakEvInst.lean:322` |
   | `LExLoad` `asrc` | `:331-332` |
   | `LDev` arms | `:305`, `:341` |
   | "rule 9 (LOAD half) OMITTED BECAUSE OF D-8" (plan cites `WeakAxiomatic3.lean:2063-2067`) | `Weak/WeakAxiomatic3.lean:2076-2077` |

5. **Not an entry, but worth recording for (E)/(F-dep).** `unreachable`'s MMIO store `0x8000086c` to
   `0xe000000` is undecoded and has no `pnodeStep` successor. No graph contains it, so it is
   correctly absent from §B(11).

## (d) Verdict

rule-9 graph hits: **none** (the only AMO is `amoswap.w.aq` `0x80000c74`, and no lock-pointer
argument is MMIO-derived; there is no lr/sc). D-8-masked ISA instances: **1** static site, printint
`lbu a5,0(a5)` at `0x800004c0` = `digits[irq % 10]`, reached from devintr's
`printk("unexpected interrupt irq=%d\n", irq)` (`0x80002698` → `0x800005fe` → printint). Its location
is never written (`textPristine`, `kernelData_digits`). R5 STOP candidates: **none**. Every segment
through an I/O event is Pinned by composition (b.0 L-IO; argument, not Lean). The lock-protected
reads are also CSchained (C2-held, C3-cons, C3-vdisk). The unlocked ones (C1, C2-unheld, the
DMA-written ring C4, the open continuations C5) are vacuous or composite-pinned. Under W12's cat
chain this needs the rfi sub-case of b.0, which relies on the image fact that the only PR∧SR∧¬PW
fence, `fence r,rw` `0x80000ee6`, never follows an I/O event.
