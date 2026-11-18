# S-0 progress — `mpFF` end to end on Sail ([OWN.P20], [OWN.P21]; brief `~/dev/weak-orch/promising/SailS0_prompt.txt`)

## Status (top): GREEN, STOPPED — KILL "fetch-doom rule unprovable" FIRES (2026-11-18)

The target `sail_mpFF` as briefed is FALSE in machine v2: the assembled `mpFF` has a VALID run (all promises
fulfilled) in which hart 1's flag load returns 1 and its data load returns 0.  Cause: machine v2's fetch arm admits
OUT-OF-THIN-AIR INSTRUCTION FETCH — a hart may fetch the bytes of a message it (or another hart) has only PROMISED,
execute them, and fulfil that promise later in a computation steered by the fetched code.  So no fetch rule of the
form "a fetch returns the image's bytes, or the run is invalid (doom)" can be proved, and the frozen-text doom of
SailScope §1 L3 (b) is unsound for doomed continuations.  Stopped before building the walker, the emission lemmas
and the target (nothing to measure for them; see "What was not built").

Build: `lake build Weak.Prom.SailS0Fetch` and `lake build Weak.Prom.SailS0Check` green.
`#print axioms Weak.Prom.SailS0.fetch_own_then_fulfil`: propext, Classical.choice, Quot.sound.
No sorry/axiom/native_decide/opaque/implemented_by.  New files only; no existing file edited; no root edit.

## Kills
* R1 (quiet platform): PASS by inspection, no premise beyond the boot state.  Boot of hart 0 (`bootX 0`,
  SailS0Check.lean:26): `mstatus = 0x0000000a00000000` (MIE = 0), `mie = 0`, privilege M.  `getPendingSet`
  (model SysControl.lean:690–717) at priv M gives `mIE = (MIE = 1)`, `sIE = false`, so `dispatchInterrupt` returns
  `none` for EVERY `mip`; `tick_clock`/`clint_dispatch` (Platform.lean:550, :381) write only `mcycle`/`mtime`/`mip`;
  no mpFF class writes `mstatus`/`mie`/`cur_privilege`.  Not proved in Lean (stopped first).
* R2 (class lemma size/time): NOT MEASURED (walker not built).
* R7 (target ≤ 2× `mp_verdict` + `lit_mpFF` = 2 × 43 lines, CoreLitMP.lean:98–140): NOT APPLICABLE (target false).
* FETCH-DOOM: FIRES (below).

## The finding (Lean: Weak/Prom/SailS0Fetch.lean)
* `memStep.fetch` (Machine.lean:696–703) admits any byte of the CURRENT log above the FENCE.I floor `wIfl`
  (`fetchByteOk`), including outstanding promises (also the fetching hart's own); it orders nothing after the fetch
  except the current instruction's own accesses (`wIfv`, PA-1f), which `memStep.instr` resets at the next `LInstr`;
  register writes and control labels carry only SYNTACTIC sources (Emit.lean `regSrcs`, `depsCtrl`), never the fetch
  view.  Data loads cannot do this (a read raises `coh`, so a later own write of the same message fails COH); a fetch
  moves no `coh`.
* `fetch_own_then_fulfil` (SailS0Fetch.lean:73): from `psInit`, a hart holding the outstanding promise `t` of a plain
  write `m` fetches `m`'s bytes from `t`, retires (`LInstr`), and fulfils `t` with a plain store in a later
  instruction (EXT `stPreA … < t` and COH hold).  The `example` at :95 instantiates it at mpFF's first text word
  `0x80400000` with `addi x5,x5,1`.

## The counterexample run (assembled mpFF, 2 active harts; harts 2–7 never step)
Text (SailS0Check.lean:21–25): H0 at `0x80400000`: `0x00532023` sw x5,0(x6); `0x0110000f` fence w,w; `0x0053a023`
sw x5,0(x7); `0x0000006f` j . (end idiom at `0x8040000c`; `asmInstr (.jmp _)` rejects a non-forward target, so it is
encoded directly).  H1 at `0x80410000`: `0x00032283` lw x5,0(x6); `0x0230000f` fence r,rw; `0x00042383` lw x7,0(x8);
j .  Registers: H0 x5=1, x6=0x80001000 (x), x7=0x80002000 (y); H1 x6=y, x8=x — set directly, no `li`.
1. H0 promises six TEXT messages (timestamps 1–6, this order): N0 = (A0, nop 0x13), P5 = (A0, `addi x5,x5,1`
   0x00128293), N1 = (A0+4, nop), P6 = (A0+4, `addi x6,x6,4` 0x00430313), N2 = (A0+8, nop), J = (A0+12,
   `jal x0,-12` 0xFF5FF06F); A0 = 0x80400000.
2. Pass 1: H0 fetches N0 at A0 (nop), the image fence (vwOld = 0 ⇒ vwNew stays 0), the image `sw x5,0(x7)`: y := 1
   (promise + fulfil, ts 7), then J at A0+12 (back to A0).
3. H1 runs its real text: `lw y` reads ts 7 (value 1); `fence r,rw` (vrNew = 7); `lw x` reads the image 0 — nobody
   ever writes x.  Outcome x5 = 1, x7 = 0 (the forbidden one).
4. H0 loops A0 → A0+12 → A0, each fetch choosing image or message (no FENCE.I, `wIfl = 0`): slot 0 ∈ {N0, P5, image
   sw x5,0(x6)}, slot 1 ∈ {N1, P6} (never the image fence again), slot 2 = N2, slot 3 = J.  P6 moves x6 to A0, A0+4,
   A0+8, A0+12; P5 moves x5's low 32 bits (mod 2^32) to each message's word; at each point the image `sw x5,0(x6)`
   fulfils N0, P5, N1, P6, N2, J in timestamp order (COH per address).  EXT: H0 never loads, so every register view,
   `vcap` and `vwNew` stay 0 and every pre-view is 0 < ts.  ~10^10 instructions, finite; then no promise is left.
The MachSail explorer (4,068 tests) cannot see such runs: its fetch domain is the least fixed point of what its trees
write from the image, and a hart stops at its code end.  `lit_*` theorems (`litStep`, no fetch) are unaffected.

## Owner question (blocks S-0..S-4 of the Sail direction)
Every FORBIDDEN verdict over `pstepV2` is false as the machine stands (a hart that can loop through its text, or any
of the 6 spare harts of `adequacyS`, can run thin-air code).  Options, RVWMO-first: the text is silent on fetch
ordering beyond Zifencei PA-1f ("an instruction fetch is always ordered before any explicit memory accesses that
instruction gives rise to", zifencei.adoc:107–108) and PA-0 (fetched values are values the location held).
* (A) FETCH DEPENDENCY: an instruction's register writes and its control label also carry its fetch view (the
  fetched word determines every effect).  Kills single- and multi-hart cycles (a hart's later stores are above every
  message it fetched; a cycle of authors would need strictly decreasing timestamps).  Reading: FAITHFUL in spirit
  (physical causality), not stated by the text.  The fetch rule then needs a minimal-witness doom (+0.5–1k, est.).
* (B) a fetch reads only the image or FULFILLED messages: STRONGER (loses LB through code: a fetch of an independent
  store promised by another hart), but makes the frozen-text rule trivial (no doom: fetched `t ≥ 1` is shot,
  contradicting the frozen `pend t`); needs a configuration-level premise (memStep sees one agent's promises only).
* (C) keep the machine and state Sail headlines under a visible run premise "no fetch returns a non-image byte":
  weakens every headline.

## What was not built (stopped at the kill)
Trace-recording walker + bridge, emission lemmas (sw/sd, lw/ld, fence, jal x0, li classes), fetch rule, RAM leaves,
target, cone.  Measurements requested in (7) do not exist.

## Measurements
| item | lines | time |
|---|---|---|
| SailS0Fetch.lean (finding, `fetch_own_then_fulfil`) | 106 | elaboration 0.3 s |
| SailS0Check.lean (`#eval`: binary, boot facts) | 31 | 0.7 s (closure 401 jobs, cached) |
| total new | 137 | |

## Increment log
1. SailS0Fetch.lean — `tvsAt`, `memByte_msg`, `fetch_msg_ok`, `cohBelow_empty`, `fetch_own_then_fulfil`, example.
2. SailS0Check.lean — `mpLocs`, `endIdiom`, four `#eval`s (assembled words, end PCs, end idiom, boot mstatus/mie/priv).
