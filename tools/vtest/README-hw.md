# tools/vtest on REAL HARDWARE -- the board side of the device tests

[`README.md`](README.md) is the suite; this file is the second machine.
Read that one first -- the naming, the ABI, the observation channels and the
findings table are all its, and none of them change here.

The question is the same one, asked of a development board instead of QEMU:

> is what the real hardware did an execution our model ALLOWS?

What changes is only how an image gets loaded, started and read back, so the
test sources in `tests/`, the ABI in `abi.h` and the model side in
`vtest-rocq/` are shared.  A board run writes `vtest-rocq/<Name>HwGen.v`
beside `vtest.py`'s `<Name>Gen.v`, and **the same `vtest-rocq/<Name>.v`
checks the model against both** -- so a divergence that shows up on only one
machine is visible in one file, next to the other machine's answer.

    make hwtest-probe     talk to the board, print what is there
    make hwtest-gen HWTEST_TESTS="clint_time core_smoke"
    make hwtest           regenerate every runnable capture, then vtest-check

`hwtest-gen` needs the board and OpenOCD; nothing else does, and none of it
is wired into `make vtest`, which must keep working with no hardware
present.  `vtest-check` checks hardware captures like any other -- they are
checked-in literals.


## THE POINT, and why a board is worth the trouble

QEMU is a reference *implementation*, not a machine.  It is the same
codebase the model was written against, it runs on an x86 host whose memory
model it inherits, and its `virt` board is a synthetic platform designed to
be easy.  Every finding the suite had before this file came from comparing
one model of a machine against another model of the same machine.

A real SoC agrees with neither.  It has hart 0 as a 32-bit monitor core, a
UART from a different vendor, no virtio at all, firmware already running,
and a clock that does not stop when you stop looking.  **Two of the first
three questions asked of it produced findings that six months of QEMU
testing had not** -- see "Findings" below -- and both are things a QEMU
image structurally could not have found, because every QEMU test runs on
hart 0 and the harness's clock never ticks.


## WHAT A BOARD RUN CLAIMS -- and it is NARROWER than a QEMU run

Three things are weaker here, and each is a real limitation rather than a
detail.  Nothing in `vtest-rocq/` hides them: a hardware lemma names its own
`<name>_hw_text` and its own hart, so what it claims is on its face.

### 1. It is not the same binary

`README.md`'s architecture section opens with "one binary runs on both
machines", and on a board that is not true.  Three things force it:

| | why |
|---|---|
| `PRIMARY_HART` | the JH7110's hart 0 is a 32-bit E24 monitor core and cannot execute a 64-bit image at all, so `_vtest_body` runs on a U74 |
| `UART_REG_SHIFT` | the board's UART is a different chip with a different register stride (finding 30) |
| `VTEST_BOARD` | puts a `fence.i` first, because a JTAG code load does not reach the I-cache |

They are all in [`abi.h`](abi.h), they all default to the identity, and the
QEMU images are **byte-identical** to what they were before board support
existed -- checked mechanically against all 56 checked-in `<name>_text`
captures, not by inspection.

Why this is still an honest one-directional claim: a capture carries its own
program, so "the model, run on THIS image, admits what THIS machine did" is
exactly as true as before.  What it costs is *attribution*.  When QEMU and
the board disagree, the difference is no longer necessarily the machine --
it might be the three macros -- so a cross-machine claim has to be argued
rather than read off.  Keep the list of macros short for that reason, and
keep it in `abi.h` where it can be seen at once.

### 2. The board's power-on register file is not reachable

On QEMU every run starts from a machine that has just been reset, and
`VTest.v` starts the model from `ColdBoot.cold_regs` -- the model's own
reset chain.  The two agree because both are power-on states, and
`core_regs_*` is the evidence.

**This rig cannot give us that.**  OpenOCD reports `reset_config trst_only`
-- there is no SRST line -- and `reset halt` re-initialises the JTAG TAP and
halts without resetting the cores: measured 2026-08-29, `mtvec` still held
OpenSBI's `0x40000410` and `mepc`/`mcause` still held firmware's values
afterwards.  So the harts start wherever firmware left them.

What `board.py`'s `establish_state()` does instead is write a *defined*
start state -- every GPR zeroed, `satp`/`mtvec`/`mie`/`mip`/`medeleg`/
`mideleg`/`mcounteren`/`mscratch`/`mepc`/`mcause`/`mtval` and the S-mode
shadows cleared, `mstatus` set to `ArchReset.board_regs`' power-on
obligation -- so a run starts somewhere known rather than somewhere
firmware-dependent.

**The consequence, and it is the one real limitation of this rig: for the
registers in that list, a `core_regs_*` test on this board measures what the
runner wrote.**  It is not vacuous for anything else -- `misa`, the
counters, the PMP file, and every register a test writes itself are real
observations -- but a hardware reset-value result is not available here and
must not be reported as one.  A board with SRST wired, or a `dmcontrol.
ndmreset` the SoC honours, would lift this.

### 3. The machine is not quiescent

`halt` and `resume` are SMP-wide on this board -- one OpenOCD group of five
harts -- so "run on one hart and leave the rest alone" does not exist.  By
default the runner takes over only its own harts and leaves firmware running
on hart 1, which keeps the board alive (and, importantly, keeps petting
anything firmware is petting).  U-Boot idling at its prompt polls UART0 and
touches nothing else the tests use, which is tolerable for `core`, `pt`,
`conc`, `clint` and `plic` -- but it *is* a second agent on the machine, and
a `uart` test cannot tolerate it at all.

`board.py --takeover` additionally points firmware's hart at the image, so
every U74 is ours and the machine really is quiescent.  Read the watchdog
warning below before using it.


## The board profile

One entry in `PROFILES` in [`board.py`](board.py).  Today: `visionfive2`,
a StarFive VisionFive 2 (JH7110).  Measured, not assumed:

| | QEMU virt | VisionFive 2 (JH7110) |
|---|---|---|
| DRAM | `0x80000000` | base `0x40000000`, but `0x80000000`–`0x80301000` is free and writable, so **the whole ABI works unchanged** |
| harts | hart 0 | hart 0 = **E24, 32-bit**; U74s are **mhartid 1–4** |
| `misa` | `0x800000000014112D` (the model's `MISA_C`) | `0x800000000094112F` — adds **B** (bit 1) and **X** (bit 23) |
| UART | `0x10000000`, 16550, byte-strided | `0x10000000`, **Synopsys DW-APB v3.14a** (`UCV` `0x3331342a`, `CTR` `0x44570110`), **reg-shift 2** |
| PLIC | `0x0c000000` | `0x0c000000` — present |
| CLINT | `0x02000000` | `0x02000000` — present, `mtime` **live** |
| virtio-blk | `0x10001000` | absent |

`primary_hart` is **2**, not 1: hart 1 is where firmware runs, and taking it
is what the watchdog warning is about.


## HOW A RUN WORKS, and the four things that will bite you

    halt → write the zero regions and the image (gdb `restore`, bulk)
         → clear our harts' CLINT MSIP
         → write a defined register state on our harts
         → resume (SMP-wide)
         → poll RESULT_BASE for DONE over JTAG while running
         → halt → read the 4 KB result region back (gdb `dump binary memory`)

**Bulk, always.**  Every JTAG memory access is a round trip.  `restore`
writes a whole region in one go — an image plus two zeroed 4 KB regions in
1.6 s — where a gdb `while` loop writing the same 8 KB a doubleword at a
time did not finish in two minutes.

**OpenOCD is not in our filesystem.**  It may be another container or
another host, so `load_image`/`dump_image` — which open files on OpenOCD's
side — cannot be used at all.  Everything moves over the GDB remote
protocol; only run control goes over the telnet command server.

**The telnet console is not a synchronous channel.**  OpenOCD writes
asynchronous messages to it (`Disabling abstract command writes to CSRs`,
target-halted events, background poll errors) and injects stray NUL bytes
mid-line.  A reader that waits for the next `> ` prompt reads someone else's
output and is off by one from then on — observed as an `mdw` that returned
nothing and a `targets` that returned the previous command's answer.  Every
command is therefore framed by an `echo <marker>` sentinel, matched at the
start of a line so the command's own echo does not end the reply early.

**Do not change the JTAG adapter speed.**  It is 2000 kHz and that is where
it should stay.  Stepping it to 16 MHz to speed up the region loads corrupted
a DMI transaction and left the E24 unexaminable (`DMI operation didn't
complete in 2 seconds`, `Examination failed`), after which OpenOCD's polling
wedged its own command server and the server had to be restarted.  The
bulk-load cost is real -- see the Gdb class in `board.py` for what was done
about it instead -- but this is not the lever.

**Never touch the E24.**  Reading a 64-bit CSR on hart 0 (`$misa`, `$satp`)
does not merely fail — it *drops the gdb connection*, twice measured.  It is
in `ignore_harts` and nothing may put it in a thread list.


## Hazards, each of which cost a board

**The watchdog, and the firmware hart.**  The first end-to-end attempt
pointed hart 1's `pc` at the image and resumed.  The SoC reset a few seconds
later and U-Boot restarted; OpenOCD's debug module did not survive it
(`dmstatus=0x0`, and `jtag arp_init` does not recover it in this build — the
server had to be restarted).  Hart 1 was firmware's *running* hart.  Either
the JH7110 watchdog is gated off while the harts are debug-halted and
resumed counting with nobody left to pet it, or the hart trapped into
firmware with a context that had only `pc` set.  Both say the same thing:
**do not hijack the hart firmware is running on, and set a complete
register state rather than just `pc`.**  If you use `--takeover`, expect to
need the watchdog stopped first (`wdt list` / `wdt stop` at the U-Boot
prompt, or the JH7110 WDT registers at `0x13070000` over JTAG).

**Firmware leaves state behind.**  A secondary hart parked by OpenSBI is
waiting for an IPI, so **its CLINT MSIP is 1** when we take it over, where
the model's power-on CLINT has 0.  `clint_msip` read exactly that before the
runner learned to clear it.  Anything else firmware leaves set is a start
state the model does not have; when a board test disagrees in its *first*
observation, suspect this before suspecting the model.

**A compressed instruction at the end of the image.**  The model sometimes
fetches four bytes for a two-byte instruction, and its memory is a finite
`gmap` holding exactly the image.  So a compressed instruction in the last
two bytes has its fetch run off the end and the machine goes **`VStuck` at
an address that disassembles to something perfectly ordinary**.  This is not
a decode problem — the model handles RVC fine, and a board image is full of
it.  QEMU images never hit it because they are built `-march=rv64imafd` and
contain no compressed instructions at all; board images are built
`-march=rv64gc`, what xv6 itself uses, and `core_smoke`'s final `ret` came
out as a two-byte `c.jr ra` (measured: `VStuck` at `0x8000008c`).
`board.py`'s `pad_image()` adds four bytes, which the machine does not
notice and the model needs.


## Findings

These continue the numbering in [`README.md`](README.md), which stays the
authority; they are written up here because they are what the board found.

| # | what | model | the board | kind | found by |
|---|------|-------|-----------|------|----------|
| 27 | **the model's clock never runs** | `mtime` frozen at 0 however many instructions retire; `mcycle`/`cycle` frozen with it | both advance, on QEMU *and* on the board | **UNSOUNDNESS** | `clint_time`, `core_csrprobe` |
| 28 | **the CLINT is not indexed by hart** | only hart 0's registers exist: `clint_load`/`clint_store` compare the offset with `eq_vec` against `MSIP_BASE` = 0 and `MTIMECMP_BASE` = 0x4000; everything else takes a load access fault | every hart has its own MSIP at `CLINT+4*hartid`, with the semantics the model gets right for hart 0 | **UNSOUNDNESS**, live in xv6 | `clint_msip` |
| 29 | `misa` — all three machines differ | `0x…14112D` (A C D F I M S U) | board `0x…94112F` adds **B** and **X** and has no H; QEMU `0x…1411AD` adds **H** | incompleteness both ways | `core_csrprobe` |
| 30 | the UART is a **different chip** | byte-strided 16550 in an 8-byte window (`DevModel.uart_size = 8`) | Synopsys DW-APB v3.14a, **reg-shift 2**: LSR is at `0x14` and the whole file lies outside the model's window | board difference, not a model defect | the probe |
| 31 | CSRs the **U74 refuses** that both the model and QEMU implement | implemented | `menvcfg`, `mconfigptr`, `senvcfg` (privileged spec 1.12 additions the core predates) and `time` (SiFive leaves `rdtime` to firmware — OpenSBI emulates it) all take an illegal instruction | **model is WIDER than the board** | `core_csrprobe` |
| 32 | **`csrr mseccfg` has NO TRANSITION in the model** | `exec` returns None → `VStuck`: it neither answers nor refuses | an ordinary illegal-instruction trap, on both machines | a THIRD outcome; same class as finding 25's `sc.w` | `core_csrwide` |
| 33 | **the machine's identity** | `mvendorid`/`marchid`/`mimpid` all 0 — an anonymous machine (QEMU too) | `0x489` (SiFive's JEDEC id), `0x7`, `0x4210427` | incompleteness | `core_csrprobe` |

### The two that matter most

**Finding 27 is the largest, and it is not a device question.**
`VTest.run_until` steps `riscv_step false` — the argument is the clock tick,
and the harness never passes `true` — so no execution of the model has a
moving `mtime`.  `ClintTime.v` states it with `minstret` as the control: the
counters advance in the model exactly as on both machines, so the freeze is
the *clock* and not "counters are unimplemented", and `mcycle` freezes with
`mtime` rather than with `minstret`.  `core_csrprobe` reaches the same
conclusion by a second, independent route — `mcycle` and `cycle` read 0 in
the model while `minstret` and `instret` are nonzero.  Same shape as finding
24 (the SC memory model): not a wrong value but a behaviour the model cannot
have.  Unlike 24 it may be cheap — the model *has* the tick — and finding out
which is the next thing worth doing.

**Finding 28 is the one only a board could find.**  Every QEMU test runs on
hart 0, where `4*hartid` is 0 and the gap is invisible; it took a machine
whose hart 0 cannot run the image at all to address `CLINT+8`.  `ClintMsip.v`
holds both halves — QEMU on hart 0, where the model's MSIP semantics are
*right* end to end (including raising and dropping `mip.MSIP`, which a
"stored but inert" model would fail as the UART's MCR did in finding 6), and
the board on hart 2, where the same program completes on the machine and the
model faults at `0x8000006c` with `mtval = 0x2000008` and trap-loops forever.
Either half alone would be misread.  It is live: xv6's `start()` stores to
`CLINT_MTIMECMP(id)` with `id = r_mhartid()`.  Same shape as findings 11/12,
where the PLIC was indexed by hart instead of by CONTEXT.

### One row where the board vindicates the model against QEMU

`mideleg`.  QEMU has the hypervisor extension, so VSSIP/VSTIP/VSEIP/SGEIP are
hardwired into it (`0x1444`, finding 19's consequence).  The board has no H
and reads 0 — which is what the model reads.  Every other row here has the
model narrower or wider than the hardware; on this one QEMU is the outlier,
and it is a reminder that "QEMU-virt is the reference" is an assumption the
suite makes and not a fact.

### Finding 31 has a live consequence for the `pt_` area

README's rules require a `pt_` program to pin `menvcfg.ADUE` explicitly
before `satp` (finding 20), because power-on ADUE differs between the model
and the machine.  **On this board it cannot** — `menvcfg` does not exist —
so any port of the `pt_` area to this hardware has to decide what to do
about Svadu first.  That eight of the nine `pt_` tests nonetheless run here
(see the scoreboard) is because they set ADUE before the first translated
access and the U74's behaviour happens to match; it is not because the rule
was satisfied.

### Finding 32 should be settled before README's open decision

README's open decision asks "which machine is the model claiming to be?" and
leaves findings 19 and 22 unclassified until someone answers it.  Finding 22
records the model as *"implemented, read successfully"* on its seven CSRs.
Through this suite's interpreter that is not what happens: `csrr mseccfg`
has no transition at all.  Whether finding 22's claim was measured some other
way or has rotted is worth checking, because the decision was framed on the
belief that the model answers here.

## The memory model, measured

`conc_mp` is the litmus test that separates RVWMO from TSO -- the one thing
`conc_sb` cannot ask, because `conc_sb` separates TSO from SC and QEMU's host
is TSO.  The writer stores a monotonic sequence number to X and then to Y;
the reader reads Y and then X.  The writer's own order makes X at least as
new as Y at every instant, so a reader seeing **Y newer than X** has observed
a reordering: **impossible under TSO, allowed under RVWMO**.

| | witness (races observed in flight) | forbidden |
|---|---|---|
| the model | — (sequentially consistent; cannot produce it) | 0 by construction |
| QEMU virt | **0** of 20480 — see below | 0, and it means nothing |
| VisionFive 2 | **81920 of 81920** | **0** |

**QEMU cannot be asked this question at all**, and that is the sharpest
argument in this file for why a board is worth the trouble.  Its vCPUs
round-robin with a long scheduling quantum, so the reader's whole loop runs
inside one quantum and the writer never gets in -- measured, X and Y both
still 0 when the unfenced pass ended, witness 0 out of 20480.  (The FENCED
pass does interleave, because the fences break the translation block.)  It is
not that QEMU gives a different answer; it is that it gives no answer.

**THE SEPARATION IS NOT THE PROBLEM.**  X and Y are 1 KB apart -- sixteen
64-byte lines on this core.  64 would already put them in different lines,
but adjacent is not independent (a next-line prefetcher pulls the neighbour,
and adjacent lines sit in adjacent L1 sets), so the distance was widened to
remove the question.  It changed nothing: witness still 4096 of 4096,
forbidden still 0, and the raw log still shows `X - Y = 1` on every
iteration.  That is a useful negative -- it rules out false sharing and
prefetch coupling as the explanation, and leaves the lockstep below as the
only one standing.

**THE RAW OBSERVATIONS EXPLAIN THE NULL, and they are why the count alone
would have been misleading.**  The test logs the first 32 raw `(r1, r2)`
pairs, and on the board they are:

    iter 0   r1 = Y = 1    r2 = X = 2       X - Y = 1
    iter 1   r1 = Y = 4    r2 = X = 5       X - Y = 1
    iter 2   r1 = Y = 5    r2 = X = 6       X - Y = 1
    ...

`X - Y` is **1 on every single iteration**.  The reader is not catching the
writer at some random point in a long window; it is catching it exactly
between two adjacent stores, one sequence number apart, every time.  The two
harts are running in lockstep at one iteration each, because the two cache
lines ping-pong between them and each iteration is one round of coherence
traffic.

That is the regime in which reordering CANNOT occur: both of the writer's
stores miss, so each must obtain the line before the next proceeds, and they
are serialised by the coherence protocol rather than by any ordering rule.
The store buffer never holds two stores at once, so it has nothing to drain
out of order.  **A 100% witness count is maximal SAMPLING and, here, minimal
OPPORTUNITY** -- the very coupling that makes the reader always observe the
pair is what stops the pair from ever being reordered.

So the refinement is not "run it longer".  It is to break the lockstep: the
writer needs to run AHEAD with several stores in flight, which means X must
miss while Y hits, which means the reader must not be pulling both lines
every iteration.  Sampling rarely, or giving the writer a private hot Y,
is the direction.

**What the board result does and does not say.**  It says that in 81920
races, every one of which the reader demonstrably observed while the writer
was between its two stores, the U74 never let the second store be seen
before the first.  It does **not** say the U74 is TSO.  The mechanism that
would produce this outcome on an in-order core is a store buffer that drains
out of order -- Y hitting in L1 while X waits for ownership -- and a core
with a strictly FIFO drain can never exhibit it however long you look.  A
null result here bounds the rate; it does not establish a memory model.

Two refinements worth trying before drawing any conclusion: bias the cache
state so the writer's X line is remote and its Y line local (the current
test has the reader touching both, which makes them symmetric), and add IRIW,
which needs four harts -- this board has four U74s, but one runs firmware
unless `--takeover` is used.

## The board scoreboard, and what it does and does not say

Every non-`disk`, non-`uart` test, run on the VisionFive 2.  **These rows say
only whether the program set the DONE flag on the board** — they are not
model comparisons, and nothing is claimed from a row until a capture is taken
and checked in `vtest-rocq/`.

| area | completes | does not | the reason, where known |
|---|---|---|---|
| `pt_` | 8 of 9 | `pt_tlb` | not diagnosed |
| `core_` | 7 of 10 | `core_regs_mcsr`, `core_regs_scsr`, `core_regs_ctr` | **finding 31**: they read for VALUES, so the U74's refusal of `menvcfg`/`senvcfg`/`time` ends the run.  `core_csrprobe` is the test that answers the same question anyway |
| `clint_` | 2 of 2 | — | both captured and checked against the model |
| `plic_` | 2 of 7 | `thresh`, `mask`, `arb`, `tie`, `level` | not diagnosed.  The two that pass only read and write registers; **all five that actually drive an interrupt fail**, which is one cause and not five — most likely firmware still owning the PLIC on hart 1 and claiming sources out from under the test.  A `--takeover` question |
| `conc_` | 1 of 5 | `lost`, `byte`, `amo`, `sb` | not diagnosed.  Their two-pass rendezvous is tuned for QEMU's TB warm-up, which is not a thing on real harts |

**Checked in and proved against the model so far: `core_smoke`,
`clint_time`, `clint_msip`, `core_csrprobe`.**  The rest of the "completes"
column is a triage list, not a result.

## What is not done

- **The serial channel.**  `uart_tx` and `uart_loop` compare what the 16550
  actually transmitted, captured from QEMU's serial file.  The board's
  serial line is not exposed to the runner yet, so `<name>_hw_serial` is
  always `[]` — which means *not observed*, not *nothing was sent*, and the
  generated file says so.  Until it is wired up, a board UART test cannot
  check the one property that channel exists for: that a loopbacked byte
  does **not** reach the wire.
- **The `uart` area.**  The test sources address the register file by bare
  offset and must be converted to `UART_REG(n)` before they mean anything
  here (finding 30).  `skip_areas` excludes them until then.
- **The `disk` area.**  The JH7110 has no virtio-mmio block device.  Not a
  finding — a device that is not there — and `skip_areas` excludes it.
- **A hardware reset-value result**, for the reason in §2 above.
- **Diagnosing the scoreboard's "does not complete" column.**  Three
  suspected causes for thirteen rows; only the `core_regs_*` three are
  actually explained (finding 31).
- **`trap_m` and `trap_s`** — dedicated M- and S-mode trap-handler tests.
  What `core_csrprobe`'s control establishes is only the narrowest case: one
  illegal instruction, M-mode, no delegation.  `trap.S` is the foundation; a
  delegated test needs an S-mode handler beside it.
