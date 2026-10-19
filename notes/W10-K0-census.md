# W10-K0 — route K follow-up: dead-frame census of the image, and the UART chain

Worker w2, 2026-10-18. Read-only follow-up to `notes/W10-K-spike.md` (§5 row K0, §2 R-K2 item 4).
No Lean edits and no builds. Everything below was read off the TRACKED image `Xv6/KernelImage.lean`
(xv6-riscv `b72cbac1`, the objdump text in its comments) and the `.rodata`/`.data` bytes in
`Xv6/KernelData.lean`. The local `~/dev/xv6-riscv/kernel/kernel.asm` that the spike used is a
DIFFERENT build: `holding` is at `0x80000b82` there and `0x80000bf2` here. All pcs below are from the
tracked image. The C source used for orientation is `origin/verified` of `~/dev/xv6-riscv`. It lacks
chroot, so it is only approximate; the binary decides every verdict.

## 0. Verdicts

- **(a) No BLOCKER. The `holding` skip (K5) is S–M.**
  - The skipped window leaves exactly ONE byte different between GF and the member once `acquire`
    returns: byte `C−72`, where `C` is the sp of `acquire`'s caller (§1).
  - The image has exactly ONE genuinely uninitialized stack read: `filestat`'s copyout of
    `struct stat`'s 4-byte hole.
  - Since `C ≡ 0 (mod 16)`, the differing byte always sits at an address `≡ 8 (mod 16)`. The hole's
    bytes sit at `≡ 4..7 (mod 16)`, so the hole can NEVER read the differing byte, whatever ran
    before. Independently, the spike's overwrite argument also holds in this build.
  - Site count:
    - **SAFE: 1 genuine uninitialized read** (the stat hole).
    - **SAFE, not actually uninitialized:**
      - 1 082 stack loads are must-written statically;
      - 39 stack loads read slots that a callee writes, on every path that reaches the load;
      - 26 escaped stack objects are read by a callee, and only the bytes written earlier are read.
    - **NEEDS-ARGUMENT: 0. BLOCKER: 0.**
- **(b) The UART 3-hart chain: CONFIRMED as xv6-reachable, but on a different path from the
  spike's.**
  - The spike's version mixed two devices. `printk` writes UART **1** (`0x1000a000`, IRQ 12, no
    handler), while `consoleintr` is the handler of UART **0** (`0x10000000`, IRQ 10).
  - The real instance:
    - hart 2 is a process writing to the console (for example the shell's `"$ "` prompt) in
      `uartwrite`, with `w‴` the release inside `sleep_prepare`;
    - hart 1 is `uartintr(0)`;
    - hart 3 is the next `consoleintr`, calling `wakeup` (§3).
  - Its `r3` is `holding+0x0`, so the 3-hart residue needs the K5 `holding` skip (or P). K5 is not
    blocked (a).

## 1. What the skipped `holding` long arm leaves behind

Disassembly in this image:
- `acquire` is at `0x80000c58`, frame 32: `ra@24 s0@16 s1@8`, and `mv s1,a0` (= lk) runs BEFORE
  `jal push_off`.
- `push_off` is at `0x80000c1e`, frame 32: `ra@24 s0@16 s1@8`.
- `holding` is at `0x80000bf2`:
  - short arm: `lw; bnez; li a0,0; ret`, with NO stores;
  - long arm from `+0x8`: frame 32, `ra@24 s0@16 s1@8`, then `jal mycpu`.
- `mycpu` is at `0x8000195c`, frame 16: `ra@8 s0@0`.

Let `A` be `acquire`'s sp and `C = A+32` its caller's sp. Here are the bytes below `A` on the two
sides:

| slot | before the window (the last writer is `push_off` and its last `mycpu`, on both sides) | GF after the long arm | differs? |
|---|---|---|---|
| `A−8`  | `push_off` ra = `0x80000c68` | `holding` ra = `0x80000c6e` | yes, but rewritten by `acquire`'s own `jal mycpu` (`0x80000c7c`, ra `0x80000c80`) on both sides before `acquire` returns |
| `A−16` | `push_off` saves `acquire`'s s0 = `C` | `holding` saves `acquire`'s s0 = `C` | no |
| `A−24` | `push_off` saves `acquire`'s s1 = `lk` | `holding` saves `acquire`'s s1 = `lk` | no |
| `A−32` | not written by either | not written | no |
| `A−40` | `push_off`'s last `mycpu` ra = `0x80000c3a` (every `push_off` path ends with the call at `0x80000c36`) | `holding`'s `mycpu` ra = `0x80000c0c` | **yes** |
| `A−48` | `mycpu` saves `push_off`'s s0 = `A` | `mycpu` saves `holding`'s s0 = `A` | no |

So once `acquire` returns, **GF and the member differ only at byte `A−40 = C−72`** (`0x0c` versus
`0x3a`). The upper seven bytes of that slot are equal (`0x0000000080000c..`).
- This holds in both directions: if the member takes the long arm where GF did not (R-K2 item 5),
  the same byte differs.
- The failed-`amoswap` and `started` skips have no stores (spike R-K4, CertZ34), so they add nothing.
- Interrupts are off inside the window (`push_off` comes first), so no `kernelvec` frame lands in it.

The spike's R-K2 item 4 talked about "holding's frame + mycpu's frame". That over-approximates the
divergence: it is one byte.

**Alignment.**
- All 373 `addi sp,sp,imm` in the image have `imm ≡ 0 (mod 16)` (sizes 16…544).
- The only other writes of sp are:
  - `_entry`: `stack0` is at `0x8000a420` and is `aligned(16)`; it adds `4096·(hartid+1)`;
  - `swtch` `0x800024ee`: restores a saved, aligned sp; a new process's context sp is `kstack+PGSIZE`;
  - `uservec` `0x8000607e`: `kernel_sp = kstack+PGSIZE`;
  - `userret` `0x800060b8`: a user sp, irrelevant here;
  - `kernelvec`: `−256`.
- Hence every `C ≡ 0 (mod 16)`, and **the differing byte is always at an address `≡ 8 (mod 16)`**.

## 2. (a) The census

**Method.** A Python pass over `Xv6/KernelImage.lean` (scratch only, not committed):
- per function, a CFG with sp and s0 offsets tracked from entry (frame pointers are on);
- a forward must-written analysis over frame bytes, meeting by intersection (`argraw`'s `jr` table
  is resolved to its case bodies);
- every load from `sp` or `s0` is checked against the must-written set;
- every instruction that copies a stack address into another register (`addi/mv/add rX,sp|s0`) is
  listed as an escape and triaged by hand against the callee;
- `argint`/`argaddr` are summarised as unconditional writers through `a1`;
- loads below the current sp, or into the caller's frame: none (`printk`'s va area
  `s0+8..s0+63` lies inside its own 192-byte frame).

The bound to prove is "every load of a kernel-stack byte reads a byte written earlier in the same
activation". It is enough because:
- the differing byte is created below `C−64`, which is dead memory;
- it stays different only until a store overwrites it;
- a live frame slot that the current activation wrote cannot hold it: callees and interrupt frames
  sit strictly below the activation's sp, and RISC-V has no red zone.

Only a read of a never-written byte could observe it.

### 2.1 Static result

| class | loads | verdict |
|---|---|---|
| must-written inside the function (prologue saves and restores, spills, locals) | 1 054 | SAFE (mechanical) |
| written through `argint`/`argaddr` (unconditional `sw/sd a0,0(s1)` at `0x80002946`/`0x80002962`) | 28 | SAFE (mechanical, with the callee summary) |
| written by a callee on every path that reaches the load (table 2.2) | 39 | SAFE (path argument) |
| analysis artifacts: `argraw` `0x8000287a` (restore of its own `s1`, flagged only because of the `jr` merge); `_entry` `0x80000004` (a GOT load through `auipc sp`, not a stack load) | 2 | SAFE |
| total `sp`/`s0`-based loads | 1 123 | |

There are no callee-saved slots read before they are written; every conditional save (shrink-wrap,
for example `sys_dup` `0x80004ee2`) is paired on the same paths. `kernelvec` restores only what it
saved. `swtch` and the trampoline read the context or trapframe, not the stack.

### 2.2 The 39 callee-written loads

| function (loads) | slot | writer | why it is written on every path to the load |
|---|---|---|---|
| `sys_read`/`sys_write` (1+1) `0x80004f4c`/`0x80004f94` | `f` @`s0−24` | `argfd` `*pf` (`0x80004d0e`) | the load follows `bltz a0` on `argfd`'s result; `argfd` returns 0 only after writing `*pf` |
| `sys_fstat` (1) `0x80005012` | `f` | `argfd` | same |
| `sys_dup` (1) `0x80004ee6` | `f` | `argfd` | same |
| `sys_close` (2) `0x80004fc4`/`fd4` | `fd`, `f` | `argfd` (`0x80004d06`, `0x80004d0e`) | same |
| `sys_exec` (2) `0x8000562e`/`642` | `uarg` @`s0−480` | `fetchaddr` → `copyin` (8 bytes) | follows `bltz`; `fetchaddr` returns 0 iff `copyin` returned 0 (full copy) |
| `sys_pipe` (6) `0x80005700`…`7a0` | `rf`, `wf` | `pipealloc` | `pipealloc` stores 0 to both first (`0x8000461a`/`61e`), unconditionally |
| `sys_unlink` (1) `0x800051e0` | `off` @`s0−212` | `dirlookup` `*poff` (`0x800039fa`) | `dirlookup`'s chroot self arm (`0x800039a6`, `name == ".."` at the root) returns WITHOUT writing `*poff`, but `sys_unlink` rejects `"."` and `".."` first (`namecmp` at `0x80005182`/`0x80005196`, before `dirlookup` at `0x800051ae`). The only other `*poff` caller passes `poff = 0` |
| `sys_unlink` (1) `0x80005262` | `de.inum` @`s0−232` | `readi` (inlined `isdirempty`) | follows `bne a0,16` → panic |
| `dirlookup` (2) `0x800039e6`/`9fe` | `de.inum` @`s0−96` | `readi` | follows `bne a0,s3(=16)` → panic |
| `dirlink` (1) `0x80003bbe` | `de.inum` @`s0−80` | `readi` | follows `bne` (=16) |
| `pipewrite` (1) `0x80004804` | `ch` @`s0−97` | `copyin` (1 byte) | follows `beq a0,-1` (`copyin` returns 0 or −1) |
| `kexec` (13) `0x800049c4`…`c5c` | `elf` @`s0−432` (64 bytes), `ph` @`s0−488` (56 bytes) | `readi` | follows `bne a0,64` / `bne a0,s11(=56)`; `readi` returns `n` only after copying all `n` bytes |
| `virtio_disk_rw` (6) `0x80005b72`…`cc6` | `idx[0..2]` @`s0−96` | inlined `alloc3_desc`, `sw a5,0(a1)` (`0x80005b42`) | `idx[j]` is read only when `j < s2` (the count already written), or after all three succeed |

### 2.3 Escaped stack objects read by a callee or through a derived pointer

These are the 27 objects that are not plain `argint`/`argaddr` cells: 26 are read only where written, and the 27th is `st`:

| object | reader | bytes read | written by | verdict |
|---|---|---|---|---|
| `consolewrite` `buf[32]` | `uartwrite` (`0x80000984`) | `nn` | `either_copyin` of `nn` bytes; on −1 it breaks before `uartwrite` | SAFE |
| `consoleread` `cbuf` | `either_copyout` | 1 | `sb` at `0x80000214` | SAFE |
| `printint` `buf[16]` | own `lbu 0(s1)` loop | `buf[0..i)` | the digit loop plus `-` | SAFE |
| `printk` va area `s0+8..+56` | `va_arg` | at most 3 slots (every format in `.rodata` has ≤ 3 conversions) | prologue spills `a1..a7` (`0x80000532`–`540`) | SAFE |
| `forkret` `argv[2]` | `kexec` | `argv[0..1]` | `0x800019e2`/`e6` | SAFE |
| `dirlookup` `de` | `namecmp(name, de.name)` | up to 14 | `readi` = 16 | SAFE |
| `dirlink` `de` | `writei` | 16 | `strncpy` pads 14 (`0x80000e56` loop) + `sh inum` `0x80003bf8` | SAFE |
| `namei`, `create`, `sys_link`, `sys_unlink` `name[DIRSIZ]` | `dirlookup`/`namecmp`/`strncpy` | up to the NUL, or 14 | `skipelem` (inlined in `namex`): `len` bytes + NUL, or 14 bytes; `nameiparent` returns non-null only after it ran | SAFE |
| `sys_open`/`mkdir`/`mknod`/`chdir`/`chroot`/`link` (old and new)/`unlink`/`exec` `path` (9 objects) | `namex` / `kexec` | up to the NUL | `argstr` → `copyinstr` (NUL-terminated, else −1, checked) | SAFE |
| `sys_exec` `argv[32]` | `kexec`, free loop | up to the null entry | `memset` 256 (`0x80005606`) | SAFE |
| `sys_unlink` `de` @`s0−64` | `writei` | 16 | `memset` 16 | SAFE |
| `kexec` `ustack` | `copyout` | `(argc+1)·8` | loop `sd s8,0(a5)` + `sd zero,-256(a5)` | SAFE |
| `sys_pipe` `fd0`/`fd1` | `copyout` | 4 + 4 | `sw` `0x80005708`/`718` | SAFE |
| `piperead` `ch` | `copyout` | 1 | `sb` `0x800048f4` | SAFE |
| **`filestat` `st` @`s0−72`** | **`copyout`** (`0x800043e2`, 24 bytes) | **24** | **`stati`: 0..11 and 16..23. Bytes 12..15 are NEVER written** (`Xv6/SpecStati.lean:28`, `FilestatParts.lean:217`) | **SAFE, §2.4** |

No stack object is ever handed to the device: virtio uses the global `disk.ops`. This agrees with the
Xv6 proofs: grepping `Xv6/` for memory "holes" finds only `struct stat` (`SpecStati.lean:28`,
`FilestatParts.lean:217-221,258,304`). Every other "hole" hit is a separation-logic wand hole, not
memory.

### 2.4 The one genuine uninitialized read: the `struct stat` hole

- Let `S` be `sys_fstat`'s sp. `filestat`'s frame is 80 bytes with `s0 = S`.
- `st` is at `S−72..S−49`, so the hole is **`S−60..S−57`**. (The spike's `S−64…S−57` is the
  enclosing 8-byte block.)

Argument 1 (alignment, independent of history):
- `S ≡ 0 (mod 16)`, so the hole bytes are `≡ 4..7 (mod 16)`.
- The only byte a skip can make differ is `≡ 8 (mod 16)` (§1).
- So the hole never observes a skipped window.

Argument 2 (overwrite, the spike's, re-checked on this build):
- `argfd` (frame `[S−48,S)`) calls `myproc` at `0x80004cec` with sp `S−80`.
- `myproc` saves `s0` (= `S`) at `16(sp) = S−64`. That 8-byte store covers the hole, and it is a
  deterministic store that is never skipped.
- `argfd` reaches that `myproc` call on every path that returns ≥ 0, which is the only way to reach
  `filestat`.
- Afterwards, every call made before the copyout, and every interrupt frame, sits below `filestat`'s
  sp `S−80`. The `acquire` calls inside `ilock`/`iunlock` are deeper still.
- One possible store into the hole between the two points is a `kernelvec` frame taken in
  `sys_fstat` with sp = `S`. It writes `[S−256,S)` with register values, and those values agree,
  because the only skip taints (R-K3: `a5` and `mycpu` scratch) die inside the window, with
  interrupts off.

**Verdict: SAFE.** Argument 1 alone suffices.

### 2.5 What K5 still has to formalise

None of this changes the K5 estimate. The census is done; what remains is the proof plumbing:

1. **A dead-byte disagreement set in the relation.** Memory agrees except at the set `D` of bytes
   `{C−72}` left by skipped windows. Today's memory agreement is exact.
2. **The invariant "`D` is never read before it is overwritten".** It is discharged by:
   - (i) a per-pc must-written table: every frame load reads a byte written in the current
     activation (the 1 082 static loads, plus the 39 path facts in 2.2);
   - (ii) the 16-alignment of sp and the single-byte shape of `D` (§1);
   - (iii) the hole's offset being `≢ 8 (mod 16)`.

   Items (ii) and (iii) and the §1 byte table are `decide +kernel` facts about `Xv6/KernelImage.lean`.
   Item (i) is a generated table plus about 39 hand path facts. The 39 path facts are mostly already
   in the Xv6 specs as post-conditions of `argfd`/`readi`/`copyin`/`fetchaddr`.
3. **No end-of-run memory equality may mention `D`.** If any capstone clause compares final memory,
   it must exclude dead stack bytes.

Size: 0.4–0.9k lines inside K5's 1.0–2.2k. Confidence for K5 rises from L+/M− to **M**.

## 3. (b) The UART chain, concretely

The `uarts[]` table (`.data` `0x8000a390`, stride 40: base, handler, tx lock):
- UART 0: base `0x10000000`, handler `consoleintr` (`0x800002c8`), IRQ 10 → `uartintr(0)` (`devintr`
  `0x8000267a`);
- UART 1: base `0x1000a000`, handler 0, IRQ 12 → `uartintr(1)`.

`printk` → `prputc` (`0x80000482`: `li a0,1`) → `uartputc_sync(1,·)`. So the spike's "printk's THR
store, seen by a `uartintr` that runs `consoleintr`" crosses devices. The spike's `procdump`
observation stands (dead code).

**The confirmed instance (all on UART 0).**

- **Hart 2.** A process `P2` writes to the console: `sys_write` → `filewrite` → `consolewrite`
  (`0x8000012a`) → `uartwrite`. Each `uartwrite` iteration does the following:
  1. `sleep_prepare(&uarts[0])` (`0x80000968`) runs `acquire(P2.lock)` and `p->chan = …`, then
     `release(P2.lock)`. Its store `sw zero,0(s1)` at **`0x80000cfa` is `w‴`** (z = `P2.lock`).
  2. `acquire(uarts[0].tx)` (`0x8000096e`; amoswap.w.aq `0x80000c74`).
  3. LSR read `0x80000976`.
  4. **`X` = THR store `sb a5,0(a4)` at `0x80000988`.**
  - Between `w‴` and `X` there is no fence (only `pop_off`, `push_off`, the `.aq` AMO, `mycpu`, and
    `sd lk->cpu`), and `P2.lock` is not re-acquired before `X`.
  - RVWMO: `w‴` is a RAM store and `X` is an I/O store. No PPO rule orders them: `.aq` orders only
    later accesses, and ordering them would need `fence w,o`. So `X` may precede `w‴` in global
    memory order: FAITHFUL to RVWMO, and a real store-buffer behaviour.
  - The trigger is any console output, for example the shell's prompt. That is fs.img-reachable,
    with no `printk` needed.
- **Hart 1.** A UART-0 interrupt (RX, or the THRE interrupt raised when an earlier character
  drains) → `uartintr(0)`:
  - ISR read `lbu a4,2(a5)` at `0x80000a36` (reading it clears the THRE identification);
  - **`LSR₁` = `lbu a5,5(a5)` at `0x80000a3a`.** It reads THRE = 0, which with an idle device before
    `X` pins `X` before `LSR₁` in the fabric order;
  - branch `0x80000a42`, then RX loop LSR `0x80000a5c`, RHR `0x80000a64`, `jalr` handler
    `0x80000a70` → `consoleintr` → `acquire(cons)` `0x800002dc` → … → `release(cons)` `0x800003d4`;
  - **`R_y` = `0x80000cfa` on `cons.locked`.** It is control-dependent on `0x80000a3a`
    (RVWMO PPO rule 11: a store control-dependent on the load). `R_y`'s own `fence rw,w` does NOT
    order the I/O read, because pred `rw` excludes `i`, so the control dependency is the edge.
- **Hart 3.** The next UART-0 interrupt → `consoleintr` → `acquire(cons)`: **`A_y3` = amoswap at
  `0x80000c74`, reading `R_y`**.
  - On `'\n'` it calls `wakeup(&cons.r)` (`0x8000042e`, still inside the `cons`-held region) →
    `acquire(p->lock)` for each `p ≠ myproc()` (`0x8000207a`) → `acquire(P2.lock)` →
    **`r3` = `holding+0x0` `lw a5,0(a0)` at `0x80000bf2`** (then the amoswap at `0x80000c74`).
  - `A_y3`'s `.aq` orders `r3` after it.

**GF vs member.**
- GF allows `r3` to read the stale 1 (the AMO-write of `P2`'s `sleep_prepare` acquire,
  fr `r3 → w‴`). The cycle check: `X <fab LSR₁ <ctrl R_y <rf A_y3 <aq r3 <fr w‴`, and `w‴ <gmo X`
  is not required.
- GF hart 3 then takes `holding`'s long arm (`lk->cpu`, at `0x80000c04`, is `&cpus[2]` or 0,
  ≠ `&cpus[3]`, so it returns 0) and spins with failed amoswaps until it reads `w‴`.
- The member (TSO stores in program order, device accesses replayed in GF's fabric order) is forced
  to `w‴ < X < LSR₁ < R_y < A_y3 < r3`, so its `r3` reads latest 0.
- **This is the F44-1 store-buffered-past-acquire shape, reachable in xv6.** K covers it: hart 3
  skips the `holding` long arm (§1: one byte, safe by §2) and its failed spins. `A_y3` reads `R_y` at
  latest, because GF's `A_y3` reads it and atomicity keeps it latest.

**A 2-hart variant exists too.** Hart 1's OWN `wakeup` inside the same `consoleintr`:
- `LSR₁ →ctrl→` its `acquire(cons)` AMO (an AMO is a store, so rule 11 applies) `→aq→` its `r1`
  on `P2.lock`.
- This gives `X <fab LSR₁ < AMO_cons < r1 <fr w‴` with harts 2 and 1 only.
- δ1′ (floor = source position) covers this 2-hart variant: the source of `AMO_cons` can lie below
  `w‴`. It does not cover the 3-hart one: `A_y3`'s source `R_y` lies above `X`, which lies above
  `w‴`.

So the spike's §6 conclusion stands: the fabric residue for δ1′ is the 3-hart chain, and its `r3`
can be `holding+0x0`.

## 4. Corrections to the spike (W10-K-spike.md)

1. R-K2 item 4: the divergence a skipped `holding` window leaves is ONE byte (`C−72`, the low byte of
   a `mycpu` return address), not "holding's + mycpu's frames". The hole is `S−60..S−57`.
2. §3, the 3-hart chain: hart 2's `X` is `uartwrite`'s THR store on UART 0 (`0x80000988`), with
   `w‴` = `sleep_prepare`'s release. It is not `printk`/`uartputc_sync`, which write UART 1, a device
   with no handler. The spike's hart-1 and hart-3 roles (`uartintr` → `consoleintr`; `consoleintr` →
   `wakeup`) are right.
3. The spike used `~/dev/xv6-riscv/kernel/kernel.asm` (another build). Its `filestat` frame happens
   to match, but its pcs do not; use `Xv6/KernelImage.lean`.

Not covered here: K0(c), the owner question Q-K-INSTRET, which stays open.
