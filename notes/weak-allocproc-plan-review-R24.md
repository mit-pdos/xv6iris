VERDICT: SATISFIED

# Review R24 of `notes/weak-allocproc-plan.md` (rev 27)

Reviewer: one-off adversarial advisor (advisory only: no builds, no proofs, no git or jj, no subagents).  Every cite
below was read at the working-copy tip of `../xv6iris-weak`.  Scope per the R24 brief (narrow): verify rev 27's
application of R23's two required changes ([R23.1] W8 class (i) with a DYNAMIC owner; [R23.2] the rev-25 `gfDev`
formula / "FABRIC MOVES" sweep), then decide whether W-DISK and the W8-design spike are launchable as written.  Items
(a)/(b) of the standing brief were settled in R1–R23 and are not re-litigated; nothing found below is unsound.

**Sign-off.**  YES — no required change.  Both R23 fixes are applied correctly and completely; the code facts they rest
on hold at the tip; W-DISK and W8-design are launchable as written.  What remains is suggestion-level: one wording in
W8-design (3) that is narrower than the sentence before it, a counting rule the spike should sharpen (three buckets,
not two), one design option the spike should test before concluding the dynamic case needs (f2) doors, a concrete
example for the brief, and stale "rev 25" labels.  No owner question is missing (see the last section).

## What was checked and holds

- **[R23.1] applied in all four places R23 named.**  §C W8-design (1) (`:2247-2258`): the skeleton carries a DYNAMIC
  per-byte owner ("every write to the byte since the last HANDOFF is by the current owner; a handoff is `swtch` under
  `p->lock` (release by the old hart's scheduler, acquire by the new one's)"), the alternative "(ii) with `p->lock`
  ACROSS the handoff / a third shape 'owned since the lock handoff'" is named, and the static class is pinned to
  `PPerCpu` (`cpus[tp]`) and the fixed per-hart boot/scheduler stacks (`stack0`; `scheduler` never returns), with the
  target running on both (hart 0's boot stack in `userinit`, the caller's `p->kstack` in `fork`); (3) (`:2261-2262`)
  limits (β) to the statically owned bytes; (4) (f3) (`:2270-2275`) is "ONLY for `PPerCpu` and the fixed per-hart
  stacks", the 1,034 `PStack` sites are to be COUNTED by context, and the doors are named with cites ([R23.s4]:
  `procHeld` abbrev `Xv6/SchedCtx.lean:1590` of `procHeldAt :663`, `stackOwn` `MachCSL/KCtx.lean:256`, `wp_swtch_body`
  `Xv6/SpecSwtch.lean:35-58`); §C W8 (i) (`:2283-2285`) reads "no foreign writer SINCE THE LAST OWNERSHIP HANDOFF" and
  records that W11's kill of a cross-hart edge INTO a process-stack read goes through the `p->lock` handoff, with the
  (f1) → re-open [OWN.36] rule; §B(9d) (`:677-678`) and D24 (`:3051-3054`) say the same; the header (`:3-7`) and the
  history line (`:137`) record it.
  *Code facts behind it, re-checked.*  `wp_swtch_body` (`Xv6/SpecSwtch.lean:35-57`) resumes under `∀ (h : CPU) …
  kctx h (resumedK …) -∗ … wpLoop h` — any hart; `swtch_loads` (`Xv6/ProofSwtch.lean:136-143`) takes `stackOwn w1 av`
  IN at `:140` and hands `stackOwn k.sp k.avail` OUT at `:142` — the handoff is literally in the SC rule; `stackOwn`
  (`MachCSL/KCtx.lean:256-257`) is `wordPointsTo … (DFrac.own 1)` per slot — exclusive; `procHeldAt :663-668` carries
  `locked … (Γ.lock j) h`; `kstackVa` (`Xv6/SpecProcinit.lean:66`) is per slot, allocated at boot (`p->kstack = KSTACK(…)`,
  `:11`) and never freed; the scheduler writes `c->proc = p` before and `c->proc = 0` after `swtch`
  (`Xv6/SpecScheduler.lean:11,13`).  The pin table has exactly 1,034 `PStack` entries (`Weak/KernelPins.lean`: 1,035
  occurrences of the word, one in the header comment `:14`; census line `:23`) and 3 `PPerCpu` (`:476,546,548` —
  `myproc+0x1e`, `sched+0x2a`, `sched+0x54`); `KernelPinsDef.lean:33` ("[PStack]/[PPerCpu] are the no-other-writer
  cases") and `:89` ("[sp] addresses the hart's own frame") are the static gloss R23 corrected.  The concrete
  cross-hart sites exist in the table: `sched+0x7e..+0x86` (`KernelPins.lean:549-553`, the epilogue loads after `swtch`
  returns — hart B reads the frame hart A pushed) and `kernelvec+0x28..` (`:1671-1673`, the trap-frame restores after a
  `yield` from `kerneltrap`).  The handoff chain in xv6 is as the plan states: A's `sched` holds `p->lock` into `swtch`,
  A's `scheduler` resumes and does `c->proc = 0; release(&p->lock)`; B's `scheduler` does `acquire(&p->lock)`, sees
  RUNNABLE, `swtch`es in; `forkret`'s first run releases the lock B's scheduler acquired.  Every intermediate hop on a
  slot's lifetime (`wait`'s `freeproc`, `allocproc`, `fork`'s `release`) is under the same `p->lock`, and none of them
  writes `p->kstack` bytes, so "no foreign writer since the last handoff" is the right invariant and the release →
  acquire pair is the right kill edge.
- **[R23.2] applied completely.**  The two unsatisfiable leftovers are gone: W-DISK (ii)(c) (`:1692`) now reads "the
  endpoint criterion `(i,k) ∈ gfDev ↔ (gisIo (i,k) = true ∨ dvi k ≠ dvo k)` (§A(†)) [R23.2]"; §C W13 (M) (`:2105-2106`)
  "RESTATES it per [OWN.31][R22.2] as `(i,k) ∈ gfDev ↔ (gisIo (i,k) = true ∨ dvi k ≠ dvo k)` — I/O-class by CLASS plus
  every fabric-moving row item".  The four "FABRIC MOVES" glosses now read "fabric TRANSACTIONS (I/O-class events by
  class, plus fabric-moving stores)": §A(†) `:387`, W-DISK (M4) `:1473`, Status `:2371`, Q3's definitions `:2649`; Q3
  (b) `:2667` carries the disjunction.  A whole-file sweep (`MOVES`, `fabric moves`, `gisIo →`, `gisIo ∧ dvi`, `gfDev ↔
  dvi`, `ONE non-I/O`, `the I/O EVENTS in fabric order`) finds only (α) the header/§A(†)/W-DISK (iv) sentences that
  QUOTE rev 25's formula as the refuted one (`:18-19`, `:394-396`, `:1699`), (β) the rev-19 wording quoted as history
  inside Q2 (`:2596`), (γ) "the device threads' fabric moves" in §B(11)'s list of what `ioResidueGmo` ranges over
  (`:883`) and D49's title "The device-side fabric moves" (`:2887`) — both about device-side moves as a concept, not
  glosses of `gfDev` — and (δ) the quoted header convention of `WeakEvInst.lean` (`:1552`).  None is a leftover.
- **R23's suggestions, as adopted.**  [R23.s1] §A(†) `:391-392` and W13 (I) `:2117-2121`: the endpoints bracket the
  BLOCK (`HFone`/`HFpair`, `WeakRvwmoFab.lean:242-259` — confirmed: `admRun true p (dvi k) …` opens and `pstepEv … (dvo
  k)` closes each arm), START a member by class with `d' = d` (`WeakEvInst.lean:488` ✓), own-guard SKIPs after a moving
  `pre` unreachable.  [R23.s2] `:1417-1418` and `:1543`: FLUSH/unknown type `:526`, `:534`, `:536` — 1 → 3 at any `r.len`
  (confirmed against `serve`: the non-IN/non-OUT branch takes `pure ()` then `setPhase … (.served r)` at `:534`, the
  status write at `:536`); the pf-only `DFence` in the deviations line `:1755-1756` (`dusedTail`, `VirtioProg.lean:586-589`
  ✓ — `DFence` wraps the idx write at `:589`; `serve` goes from the used-element `dmaWriteIf :546-548` straight to
  `dmaWriteStep :552-554` ✓).  [R23.s3] `cacheView :359` (arm `:361` ✓), `xv6RvwmoSafeModuloF :228` ✓, `dmaRead :568` /
  `dmaWrite :569-574` ✓ (`Lang.lean`), `DRead` arm `:491-494` ✓, `Gfexec :517`/`gfDev :520` ✓.  [R23.s5] the acceptance
  wording `:1745-1746` ("no `DWild` constructor, arm or lemma left in `Weak/` and its header prose rewritten;
  `WeakEvInst.lean:33`, `VirtioProg.lean:48,76,148` mention it in comments") — the three comment lines and `:33` are
  exactly where the word occurs outside code (`VirtioProg.lean:331,334,611-619,667,837,861` and `WeakEvInst.lean:511`
  are the code occurrences W-DISK retires).
- **Launchability.**  W-DISK: the binding MECHANISM text is unchanged from R23's check except the [R23.2]/[R23.s2]/
  [R23.s5] edits above, each verified; nothing in it instructs the worker wrongly.  W8-design: the brief now names the
  dynamic owner, the doors, the counting task and the (f1)/(f2)/(f3), (r1)/(r2) outcomes; a worker can execute it
  read-only and the result is reviewed before W8 proper launches ([OWN.36]).  Both launchable.

## REQUIRED changes

None.

## SUGGESTIONS

- **[R24.s1] W8-design (3): the SPLIT sentence is narrower than the clause before it.**  `:2261-2262` reads "for (i)
  it can cover only the STATICALLY owned bytes — if so W8 SPLITS: (i)/(iii) an `Xv6/`-only parallel item, (ii) the
  ledger".  After [R23.1] the split, if (β) works, is "the STATIC part of (i) (`PPerCpu` + `stack0`) and (iii) an
  `Xv6/`-only parallel item; the DYNAMIC part of (i) (process-context `PStack`) joins (ii) in the ledger (or in the
  third shape of (1))".  One clause; otherwise a spike could read the sentence as licensing an `Xv6/`-only (i).
- **[R24.s2] The `PStack` count needs THREE buckets, not two, and "both" counts as dynamic.**  (f3)'s instruction
  (`:2272`) says "COUNTS the 1,034 `PStack` sites by context (scheduler/boot stack vs `p->kstack`, via the pin table's
  pcs)".  The table's `-- fn+off` comments make the per-function count mechanical (top of the list: `kexec` 31,
  `pipewrite` 27, `sys_exec` 23, `readi` 23, `printk` 22, `consolewrite` 21, `writei` 18, `kernelvec` 17 …), but the
  function → context map is not a partition: `kernelvec` (17 sites) runs on `stack0` when a timer interrupt lands in
  `scheduler` (interrupts are on there) and on `p->kstack` in process context; `printk`, `acquire`/`release`,
  `uartputc_sync`, `consoleintr`, `virtio_disk_intr`, `wakeup` are called from both.  Say: "three buckets —
  scheduler/boot-only (M-mode `_entry`/`start`/`timerinit`, `main`, `scheduler`, `procinit`, `proc_mapstacks`, …),
  process-only, and BOTH; the static (f3)/(β) class is the first bucket plus `PPerCpu`; BOTH is handled as dynamic".
  S text in (f3).
- **[R24.s3] Let the spike TEST a σ-derived dynamic owner before concluding the dynamic case needs (f2) doors.**  The
  plan now states "(f3) derived from `σ` alone — ONLY for `PPerCpu` and the fixed per-hart stacks" (`:2270`) as a fact.
  It is the conservative reading, but a σ-derived DYNAMIC owner map exists in principle: the scheduler writes `c->proc =
  p` before `swtch` and `c->proc = 0` after it, both under `p->lock` (`Xv6/SpecScheduler.lean:11,13`; the cells are
  `MachCSL/KCtx.lean:554`'s "this hart's `struct cpu` cells"), so "owner of `p->kstack` at time `t` = the hart `h` with
  `cpus[h].proc = &proc[j]` at `t`" is a function of `σ`'s per-byte histories (`HEnt.t` gives the time), and the
  invariant "every history entry on a `kstack_j` byte was written by that hart" is then a PURE predicate on `σ` — the
  (f3) shape — modulo the boot-era writes (hart 0's `proc_mapstacks` → `kalloc` → `memset` with no `c->proc` set; the
  predicate needs "before the slot's first handoff" or a boot-era exemption) and modulo whether it is RE-ESTABLISHABLE
  without `Xv6/` feeding (the same open question (f3) has for the static class).  Suggested text for (4): "(f3) … for
  `PPerCpu` and the fixed per-hart stacks; for process-context `PStack` the spike TESTS (f3′) an owner map read off
  `cpus[h].proc`'s history (boot-era writes exempted) before falling back to (f2)'s doors — **unverified**".  Named as an
  option only; the spike decides.  Not a memory-model question (every option FAITHFUL; the published statement is
  unchanged).
- **[R24.s4] Give the brief its tiny example.**  Hart A runs process P: `sched` pushes `ra`/`s0`–`s2` on `p->kstack`
  (prologue), `swtch` into A's scheduler, A: `c->proc = 0; release(&p->lock)`; hart B: `acquire(&p->lock)`, `swtch`
  into P, `sched+0x7e..+0x86` (`KernelPins.lean:549-553`) LOAD the words A pushed — the cross-hart rf edge into a `PStack`
  read, killed only by A's release → B's acquire.  The same shape at `kernelvec+0x28..` (`:1671-1673`) after a `yield`
  from `kerneltrap`.  Two lines in (1); they make the "since the last handoff" clause checkable against the table and
  pin the (f2) count (the two doors are `swtch_loads`' `stackOwn` IN/OUT, `ProofSwtch.lean:140,142`).
- **[R24.s5] Stale labels.**  "MAY LAUNCH NOW (rev 25; no owner gate)" (`:1103`) and "Status of the launch (rev 25,
  2026-10-11)" (`:2337`) → rev 27; the RULED Q-W8-lane's closing line "if the spike shows (β) suffices for (i)/(iii),
  split W8 accordingly" (`:2476`) could carry "(for (i): its static part [R23.1])" so the §D record matches §C.
- **[R24.s6] W8 (i)'s initial owner map.**  "Since the last handoff" needs a value before any handoff: name it (each
  hart's `stack0` slice owned by that hart from power-on — the image's bss, written by no one; each `p->kstack` page
  owned by hart 0 from `proc_mapstacks` until the slot's first `swtch`-in).  One line in (1).

## Owner questions the plan is missing

None.  The two focus items are plan text in the sound direction and both are applied; neither is a memory-model
question (RVWMO, riscv.cat, the Sail model in this tree, Zifencei and the PMAs are SILENT on how a proof states or
feeds ownership of kernel-stack bytes, and every form of W8's export is FAITHFUL — the published quantifier and
conclusions are unchanged).  [R24.s3] is a design option for the read-only spike, which [OWN.36] already lets re-open
the lane under the (f1) outcome; it needs no ruling now.  W-DISK's and W13 (I)'s `gfDev` text are consistent across
§A(†), §B(11), §C and §D after [R23.2]; Q-GFDEV-delta stays REPORT level.  The plan's existing questions keep their
"Spec:" lines and the 2026-10-10 format.
