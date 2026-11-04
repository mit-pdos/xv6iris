# PROGRESS — AmoTight (discharge `amoTightV2 ps`, AmoSplitV2.lean:217–222)

Worker: Opus (AmoTight). Workspace `/home/bsdinis/dev/xv6iris-pcsl6`. Brief: `~/dev/weak-orch/promising/AmoTight_prompt.txt`.

## Status (top): STOPPED — `amoTightV2` is FALSE for a reachable state (brief: "stop and give the counterexample")
- No theorem changed; `amoSplitFused` / `amoSplitFused_behavior` still carry the premise `amoTightV2 ps`.
- No kill criterion (program-specific named inputs) involved.

## Counterexample (amocas, failed compare) — EMPIRICAL, compiled Sail model
`Weak/Prom/AmoTightCex.lean` (NEW; `lake env lean --run Weak/Prom/AmoTightCex.lean`, after
`lake build Weak.Prom.MachSail`, green 2026-11-04). A boundary hart (`⟨.pure (), x, none, ixNone⟩`, the shape of
`hartInit`; M-mode power-on file `SailLit.bootX 0`, `PC = 0x80400000`, `x5 = 1`, `x6 = 2`, `x7 = 0x80010000`),
first step `LInstr` (`m := riscvStep false`), fetch answered with `amocas.w x5, x6, (x7)` (word
`rType (5<<<2) 6 7 2 5 0x2F`), AMO read answered `0` (≠ `x5[31:0]`). Labels emitted through `MachSail.sNext`
(the executable transcription of Emit.lean `hstep`/`hnodeStep`):
```
(106 silent) LIFetch 0x80400000 · (4) LCtrl [] · (169) LAmoLd aq=false 0x80010000 [x7]
(2 silent)   LRegW 5 [ldres]          <- NOT LSilent, NOT LAmoSt: violates amoTightV2
(8 silent)   boundary (runner stops on amocas; Emit's bndStep then offers the optional write-back LAmoSt or LInstr)
```
Same start, read answering `1` (successful compare): `LAmoLd`, 84 silent, `LAmoSt`, `LRegW 5`. `amoadd.w`: `LAmoLd`, 83 silent,
`LAmoSt`, `LRegW 5`. This agrees with the earlier record `Weak/Prom/DecoderObs.lean` o252 (`amocas.w`: x5 written, no memory write).
Code: `execute_AMO` (InstsEnd.lean:18664–18763) handles AMOCAS in the same function: `if op == AMOCAS && loaded != X(rd)`
then `wX_bits rd …; RETIRE_SUCCESS` with no `mem_write_value`. Zacas is on: `hartSupports Ext_Zacas = true`
(PlatformConfig.lean:2130), `currentlyEnabled Ext_Zacas ⇐ Ext_Zaamo ⇐ misa.A`.
Consequence: no proof of `amoTightV2` can exist for a statement that admits boundary harts. `amoSplitFused (⇒)`
very likely fails too (`fuseStep` has no step for a read half on its own).

## Second, more basic problem with the statement
`amoTightV2 ps` quantifies over arbitrary `ps : List HState`, so `h.m` can be any `SailM Unit` (for example an exclusive
`memRead` followed by `regWrite x1`). So it is false even for a program that is not a Sail continuation.
Any statement that could be proved has to restrict `ps` to boundary harts (`h.m = .pure ()`, `h.ix = ixNone`,
`h.fn = none`, like `hartInit`).

## (i) traps, (ii) amocas, (iii) misaligned: read off the code (NOT proved)
- (iii) Misaligned: `is_aligned_vaddr` is tested first, and `plat_misaligned_exception` for an AMO access is
  `plat_misaligned_access.amo = some AccessFault` (VmemUtils.lean:220, PlatformConfig.lean:4453–4457). So the
  instruction traps before `translateAddr` and before any read. Aligned ⇒ `split_misaligned` returns `(1, width)`
  (SplitAccessUtils.lean:257–263): one read and one write.
- (i) Trap between the halves: `mem_write_value` → `checked_mem_write` runs `check_pma_with_pmp_priority` and the
  per-piece `pmpCheck` with the SAME arguments as `mem_write_ea`'s check before the read (same paddr, width, `Atomic`
  access, pbmt, `con = true`; priv recomputed from `mstatus`/`cur_privilege`). Only register READS happen in
  between, and `pmaCheck`/`pmpCheck` are deterministic register-only code. So the write check cannot fail after the
  read check passed. `within_mmio_readable` and `within_mmio_writable` differ only for HTIF at width > 8 (amocas.q).
  Conclusion: no trap between the halves for non-cas AMOs (argued, not proved).
- (ii) amocas: FALSE, see above. The faithful options are (a) restrict to non-cas AMOs, with a SCOPE predicate on
  programs like `translationOff` ("no reachable announced bits satisfy `isAmocas`"), or (b) a variant where a
  failed amocas is a read half followed by `LRegW rd` and an optional boundary write-back. That is not an RMW, so
  under (b) the fused program needs a "read only" fused label.

## Why the non-cas version was not attempted (estimate for the coordinator)
Even restricted to boundary `ps` and non-cas programs, a proof needs an invariant over ALL of `riscvStep`:
1. every exclusive non-fetch `memRead` reachable in the tree comes from `execute_LOADRES` or `execute_AMO`;
2. the decoder link: announced bits with an AMO or LR decode satisfy `isLR` correctly, and `v2Roles` is not
   `ORcsr`;
3. a symbolic run of `execute_AMO`'s continuation (the `checked_mem_read` loop tail, `rX_bits`, the
   `mem_write_value` checks equal to the earlier ones).

Item 1 is a whole-ISA monadic program-logic proof (every `execute_*` clause, including V/F/D/crypto). It is far
beyond one worker session.

## Workspace edits
- NEW `Weak/Prom/AmoTightCex.lean` (executable witness; not imported by anything; no theorems).
- NEW this file. No existing file edited.

## Log
- 2026-11-04: Read execute_AMO / Mem.lean / PlatformConfig. Built `Weak.Prom.MachSail` (green) and ran
  `AmoTightCex.lean`: the counterexample was confirmed. STOPPED.
