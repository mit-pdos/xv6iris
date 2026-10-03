# noninterference — the campaign

STATUS: PAUSED 2026-09-15, the day it opened (owner: spec cleanup
first — see `completed/spec-cleanup.md`, CLOSED 2026-09-17; its
RD-1/RD-2 owned-offset and functional file rows were this campaign's §4
determinism prerequisites arriving early.  The parked offset form landed
there; the OWNED form is now upstream's OFF-LINK, so §4 should be re-read
against `completed/app-file-design.md` §3 before a lane is briefed).  Resumes on the
owner's word only.  Below: CAMPAIGN OPENED
2026-09-15 (owner's word, the day after the echo adequacy theorem
closed).  §§0–7 below are the design discussion as
checkpointed 2026-09-04 (Fable, with the owner) and remain the design of
record until a lane's as-landed note contradicts them; the LANES section
is the live worklist.  The build host exists again: the proofs build on this EC2 machine
(durable-notes, Build), so nothing here is gated on a box any more.

## PORT TO LEAN (opened 2026-10-01; owner: "port I+J to Lean main")

The Lean port (this tree) deliberately left out the NI groundwork: drift themes **I** (M1's four
ledgers, uhist, VmfaultQuiet) and **J** (the permit sweep G/L1a/L1b/L2) of `notes/rocq_drift.md`.
The Rocq commits are the specification; the design notes below (identical to Rocq's) are the
design of record; the Lean twins' "Deviations from Rocq" headers rule where the two disagree.
Base: `origin/lean` deb2995ee, branch `lean-ni`.  Order = Rocq's landing order (each lane's
Rocq commit was gated green on its predecessor), one Opus lane per Rocq commit, worktree per
lane, `lake build Xv6 MachCSL` + `tools/ci/lint.sh` + no `sorry` before a lane lands; baselines
(`tools/audit/baseline.json`, `tools/tcb/expected.json`, coverage) in the same commit when they
move.  Rocq sources: `git show <sha>:iris/<File>.v` (the shared `.git` holds the `rocq` history).

| Lane | Rocq commit(s) | Design of record | Lean homes (twins) | Depends on |
|---|---|---|---|---|
| **PI-1 kalloc ledger** | b5e67a96b (KallocEv.v), bed7ee0dd | `design/ni-kalloc-ledger.md` | new `Xv6/KallocEv.lean`; `KallocDefs`, `KmemGhost`, `SpecKalloc`/`SpecKfree`, `ProofKalloc`/`ProofKfree`, `FsCfgKits`, `ProofMain` | — |
| **PI-2 pid ledger** | d66e99d0d (PidEv.v), 8043e4cdd | `design/ni-pid-ledger.md` | new `Xv6/PidEv.lean`; `PidLock`, `SlotGen` (WchG name), `SpecAllocproc`/`ProofAllocproc`, `SpecFreeproc`/`ProofFreeproc`, `ProofKexit`, `ProofKwait`, `ProofUserinit` | PI-1 (shared `wchG`-style name plumbing) |
| **PI-3 ticks ledger** | dd1843b7a | `design/ni-ticks-ledger.md` | `TicksDefs` (Rocq TicksInv), `SpecSysUptime`/`ProofSysUptime`, `ProofClockintr`, `ProofSysPause` | — (parallel with PI-1) |
| **PI-4 zombie ledger** | 2107981b4 (ZombEv.v) | `design/ni-zombie-ledger.md` | new `Xv6/ZombEv.lean`; `WaitInv`, `UserChildren`, `ProofKexit`, `ProofKwait`, `ProofFreeproc` | PI-2 |
| **PI-5 uhist** | 5634a3874 (UhistDefs.v) | `design/ni-uhist.md` | new `Xv6/UhistDefs.lean`; `ProcDefs` (ProcPriv), `UsertrapRes`, `UtResFits`, `ProofUsertrap*`, `ProofUserret*`, `ProofForkret*` | PI-4 |
| **PI-6 VmfaultQuiet** | 7cec90c7b | `design/ni-strong-instance.md` R4 | new `Xv6/VmfaultQuiet.lean` (pure) | — |
| **PJ-G ground** | 9fb1d089c | `design/ni-strong-instance.md` §7, §7.1 | `ProcDefs` (`ProcPriv.ev`), `SlotGen` (`actCnt` at a new `WchG` name, `SgenUR`'s shape over `Nat`), `ProcInv`/`ProcPrivAcc`/`FdTable`, `SpecProcinit`, `SpecFreeproc`, `WaitInv`, `ProofKfork*`, `ProofForkret`, `ProofKexit`, `ProofAllocproc`/`ProofFreeproc` | PI-5 |
| **PJ-L1a** | f344a089a | §7.2 | ring one + block-holders (48 Rocq files; 39 have twins, kexec/kfork parts restructured) | PJ-G |
| **PJ-L1b** | b69bd0fab | §7.3 | copy ring + every block-holding chain (84 Rocq files; 68 twins; sys_open/unlink parts restructured) | PJ-L1a |
| **PJ-L2** | 78f9234b8 | §7.4 | inner VM ring (32 Rocq files; 30 twins) | PJ-L1b |

**L3 (opened 2026-10-01, owner: "go ahead with L3").** Rocq never landed L3, so there is no Rocq commit to
port: the design is §7 of `design/ni-strong-instance.md` (the lend is REQUIRED and STEPPED at the leaves) and the
Lean-specific "what remains" list of §7.4L. Three gated sub-lanes, in dependency order, integrated on `lean-l3`:

| Lane | Content | Depends on |
|---|---|---|
| **PJ-L3a** | `walk` (allocating form), `freewalk`, `uvmcreate` take the lend (`(ke : Nat)`, `actLend k.proc ke` in, `∃ k' ≥ ke` out, framed through; their callers in the VM ring pass theirs instead of framing) | L2 |
| **PJ-L3b** | `kalloc`/`kfree` led forms take the lend and STEP it (`actLend p (ke+1)` out: the append IS the step; `actLend_step` on the right disjunct, nothing at `p = 0`); the token-free led forms are deleted; the plain `wp_kalloc`/`wp_kfree` survive only with the premise `k.proc = 0` for the boot contracts (`kinit`, `freerange`, `virtio_disk_init`, the kvm chain already at `p = 0`, …); every non-boot allocator call site switches to the led+lend form and drops the receipt; the block-holders' `V.updEv k'` closes absorb the raised counts | L3a |
| **PJ-L3c** | the four ledger appends require and step the lend: allocproc's pid section (`PAlloc`), freeproc's led form (`PFree`), kwait's led forms (`ZReap`), kexit's exit append (`ZExit`, from its own block: the ZOMBIE park rides the deficit block) | L3b |

- [x] PJ-L3a  - [x] PJ-L3b  - [x] PJ-L3c

**T as designed for the Lean tree (2026-10-01, Fable; awaiting the owner's word).** L3 established by
construction (§7.7L of the design note) that a slot's counter moves only through `actCnt_step`, once per
actor-labelled append, and only in code running as that slot's process. T turns that into a statement about
the trap loop:

1. **The row.** `usertrapPost` gains one pure premise beside `utGenKept`, in the kept-row style:
   `utEvQuiet sc V V' : Prop := sc ≠ uecallScause → V.pvLazy = false → V'.ev = V.ev`. No other landed
   statement moves: `utRound`/`uroundOk` stay as they are (Rocq planned `ev ev'` inside `uround_ok`; the
   Lean rows are separate pure conjuncts, so the separate row is the faithful spelling).
2. **The discharges, per row.** Timer/device/unexpected-cause rows: the block is framed (no lend taken),
   so `V' = V` on `ev` by the existing closes. Ecall row: vacuous. Page-fault row: the arm lends the block's
   counter to `vmfault` and closes at `V.updEv kv` (L2); at `lazy = false` it needs `kv = V.ev`, which needs
   **a tightening of `wp_vmfault_body`'s post**: its continuation gains `⌜(¬ (va < sz ∧ page absent)) → k' = ke⌝`
   (the quiet arms append nothing: `va ≥ sz` and `page present` return before any `kalloc`; the allocating
   arm is exactly `va < sz ∧ absent`, which `VmfaultQuiet.vmfaultQuiet` refutes at `lazyFree`). That is the
   one Spec that moves, and only by a pure conjunct; `ProofVmfault` proves it (the quiet arms frame the
   lend, `actLend_cont_frame`). Kill row: the exception — a killed quiet process exits through kexit
   (`UT_KEXIT`, no resume row), so nothing to discharge in `usertrapPost`; the statement is for a quiet
   process that is not killed.
3. **The theorem.** Pure corollary `utRoundQuiet`: over a run of rounds whose causes are all `≠ uecallScause`
   at `pvLazy = false`, `ev` is constant (induction on the run using the row); and, as the in-logic reading,
   `actCnt`'s exclusivity (`actCnt_excl`) gives that no append labelled with that slot's process happened in
   the run — stated as the design note's §7.8L invariant, since the ledgers' contents are M2's business.
4. **Gate:** full `tools/ci/run_all.sh`; no TCB move expected (a pure conjunct and theorems).

- [x] PJ-T (landed 985e7f2d2; the run's chaining -- each round starting at the record the last ended at -- is a hypothesis of utRoundQuiet, not proved from the loop, which re-opens the parked block at an existential record: M2's first item)


**M2 as designed for the Lean tree (2026-10-01, Fable; owner: "go ahead with M2").** §6's M2, re-read against
this tree. The machine layer (`MachCSL`) already has the trace machinery `uart-trace.md` built: `Obs` (power,
device), `obsInterp` in `stateInterp` with the past `h`, `obsWf` as the pure step invariant, `obsAuth`/`obsFrag`
halves, the client's `MachFixedGS.obsPred`, the non-silent device rule `wpDev_lift_obs` with its step permit
(`uartObsPermit`), and `xv6PowerAdequacyGen`'s trace-aware `phi`/`Hphi`. The hart arm of `primStep` is silent
(`obs = []`, `primStep_hart_inv`, `wpHart_lift` via `obsInterp_silent_nil`). Four waves, one or two Opus lanes
each, integrated on `lean-m2`:

| Wave | Content | Depends on |
|---|---|---|
| **M2-W1 machine layer** | `Obs.uEnter cpu satp epc gprs` and `Obs.uExit cpu satp scause epc gprs` (the 31 GPRs as a list; `satp` is the address space's pid-free identity); emitted by the hart arm EXACTLY at the `regWrite .cur_privilege` event whose old and new values differ and one of them is `User` (the model writes `cur_privilege` LAST in `trap_handler` -- after scause/stval/sepc -- and in `sret` after mstatus, so everything the event names is in `σ.regs cpu` at that write); every other hart event stays silent. `primStep`'s hart arm becomes `obs = hartObs cpu o v σ`; `primStep_hart_inv` and `primStep_obsWf` extended (`isIo` true for the two, `obsStep`/`openSeg`/`obsBoots` arms, `obsWire`/`obsIns` ignore them); `wpHart_lift` splits into the silent lifting (all events but a privilege-crossing write) and `swp_writeReg_priv`, a permit-taking rule shaped like the UART's: the caller's `hartObsPermit`-style assumption receives `obsAuth h ∗ ⌜obsWf h g⌝ ∗ ⌜the event⌝` and returns `obsAuth (h ++ [e])`. The two towers (`UTrap`'s U→S write, `WpSmodeSretU`'s S→U write) take the permit; `WpSmodeSret` (S→S), `WpTrap`, M-mode writes stay silent (same value or no User). CI: the device-conformance suite and `check-gen` must stay green; no TCB move expected beyond `Lang.lean`'s own lines. | — |
| **M2-W2 the client ledger** | the xv6 `obsPred` (`Pt`): at every `uExit`/`uEnter` of this address space the event's registers ARE the trapped/resumed key's trapframe and `satp` the slot's root (the residue owns both: `UsertrapRes`, `UserKernelBridge.userInv_of_sret`, `userTrapFrame_open`), and the per-space subsequence of `h` is in step with the residue's `uhist` rounds (PI-5). The permits are discharged where the towers run: `UserStepTrap`/`UkLand` (the user tier's trap), `UserKernelBridge.wpLoop_userret_sret` (the kernel's sret). Deliverable: `utrace s h` (pure), the invariant, and the two boundary permits as the client's instances. | W1 |
| **M2-W3 = M0 functional rows** | `usysDet n W ι : Uvis` for the private class (§4's list: sbrk, fork's parent, wait, exit, getpid, uptime, console write; the transparent arm is already functional) and the loop's `round_det` discharge at `UexecApply.uexecRet_roundSlot` from the kernel's `SyscRows` plus the ledger RECEIPTS (`ledReceipt`, `pidReceipt`, `zombReceipt`, `tickLb`): the round's actual `(r, M', …)` equals `usysDet` at the round's ι-prefix. `uexecRetF`'s ecall arm is re-cut on it for those `n` (the program proves the functional arm; the kernel instantiates it). | — (parallel with W1) |
| **M2-W4 the theorem** | `events h` (the actor-labelled event history read off the boundary trace: each round's number and arguments at `uExit`, its result at `uEnter`, the fault cause for lazy allocations), `canon k ι` (the abstract process machine: `usysDet` folded over ι), `phi g h := ∀ s, utrace s h ⊑ canon (firstKey s h) (events h)`, `xv6NiAdequacy` := `xv6PowerAdequacyGen` at that `phi` (a new root in `tools/ci/roots.txt` and `tools/audit/baseline.json`), and the PURE two-run corollaries: general (equal ι ⇒ equal traces) and the strong instance (a process with no rounds before its first ecall generates no events: T's `utRoundQuiet` lifted to the trace). | W2, W3 |

- [x] M2-W1 (ef6f784b5; the permit lives in wireInv; one Spec moved: SpecUserret.wp_userret_body gains wireInv)  - [x] M2-W2 (W2a f964ed918, W2b feefd976e, W2c a27f0567a, W2d 9576822d7 landed; W2d also moved USERVEC's post (the exit token handed back), syscForkIn, USERRET_CLOSED's and MAIN's pre, parkMode -- the claims' routes, accepted by the coordinator -- NiFitIs is an IMPLICATION niFit → uFit and the system record keeps uFit := True so NiLedger stays out of the system theorem's TCB (coordinator ruling on O2); W2d pending) (DESIGNED 2026-10-02, "M2-W2 design" below; awaiting rulings O1-O6)  - [x] M2-W3 (M0) (38c39d26f: class = {exit, getpid, uptime}; sbrk, fork, wait, write NOT functional -- see its as-landed note; owner decision pending)  - [x] M2-W4 (421fc579f: xv6NiAdequacy, xv6NiTwoRun, xv6NiStrongInstance registered as roots; class {exit, getpid, uptime}; niOneShot in the conclusion)

**Owner ruling after W3 (2026-10-02): land M2 at the HONEST class, then grow it.** W2 and W4 proceed with
`canon` over the class {exit, getpid, uptime} plus the transparent rounds; the strong instance (a process before its
first ecall) is the headline and does not depend on the class. The four non-functional rows are M2's FOLLOW-UP
lanes, cheapest first (each names a channel §2 says is unnamed, as a ledger or a tie, then re-admits the row to
the class with its `round_det` discharge):

| Lane | Names the channel | Re-admits |
|---|---|---|
| **M2-G1 slot placement** | a slot-placement ledger (allocproc's first-UNUSED choice as an actor-labelled event; the zombie ledger's D3 "nothing under the wait lock knows the slots" is thereby revisited) | `wait` (which child is reaped: the lowest zombie slot), fork's −1 on slot exhaustion |
| **M2-G2 the pid counter** | the pid ledger's counter tie and first-ness (R2(b)/(c) of `ni-pid-ledger.md`): `nextpid` is `nextOf` of the history | fork's pid |
| **M2-G3 sbrk** | `sysSbrkOk`'s −1 only when the pool is empty (growproc/uvmalloc functional in the allocator ledger), and the eager grow's page-table pages as events (`Alloc A vpn`-grained, §3 "concedes more") | `sbrk` |
| **M2-G4 console write** | the kernel's short count stated at the key's permission view `π` (copyin at the key, not the table) and a write row in the trap contract | console `write` |

- [ ] M2-G1 (DESIGNED 2026-10-03, "M2-G1 design" below; awaiting rulings G1-R1..R6)  - [ ] M2-G2 (DESIGNED 2026-10-03, "M2-G2 design" below; awaiting rulings G2-R1..R5)  - [ ] M2-G3  - [ ] M2-G4

Risk register (honest): W1 changes the language and every lifting lemma -- mechanical but wide, and the device
suite must not notice; W3 is the proof's content and may find a row that cannot be made functional in `(key,
ι-prefix)` -- that is a channel not yet named (§2), to be reported, not papered over; W4's `events h` must be a
PURE function of the trace or the two-run corollary dies (§6's reason for exporting events).

### M2-W1 as landed (2026-10-01)

Lane `lane/m2w1`.  **Emission.**  `Obs` gains `uEnter cpu satp epc gprs` and `uExit cpu satp scause epc gprs`
(`gprs` = `hartGprs f` = `[x1..x31]`).  `hartObs cpu o σ` is `[]` except at `.regWrite .cur_privilege p`, where
`hartObsPriv cpu (σ.regs cpu) p` emits `uExitOf` (old User, new not; `scause`/`sepc`, or `mcause`/`mepc` when `p`
is Machine) or `uEnterOf` (old not User, new User; `sepc`), read off the file the write overwrites.
`primStep`'s hart arm: `obs = hartObsM cpu m g.m` (the head event's `hartObs`) when live, `[]` dead; `hartStep`
byte-identical (no `hartStepO`: a blocked step is a memory access, which is silent).  **Trace theory.**
`isIo` stays device-only; new `isUser`; `obsStep` keeps the power on, `obsBoots` ignores them, and `segStep` /
`cycStep` SKIP them (deviation from the row's "appends": the open segment and every cycle stay console I/O, so
the wire/input ties and every app's per-cycle ledger are blind to user events -- `openSeg_user`,
`cyclesOf_user`; the events live in `h`).  **Logic.**  `wpHart_lift_obs` (callback gets `obsWf h g ∧ threadLive
g genId`, `machInterp g.m ∗ obsAuth h`, returns `obsAuth (h ++ hartObsM …)`), `wpHart_lift` derived (callback
proves `hartObsM cpu m σ = []`).  `swp_writeReg(_bind)` gains `hq : r ≠ .cur_privilege ∨ v = w`;
`swp_writeReg_priv_quiet` (a privilege write staying on one side, e.g. `mret` M→S); the observed rule

    def hartObsStep (cpu) (p p' : Privilege) : IProp GF :=
      ∀ h g, ⌜obsWf h g ∧ g.pow = true ∧ g.m.regs cpu .cur_privilege = p⌝ -∗
        obsAuth h ={⊤}=∗ obsAuth (h ++ hartObsPriv cpu (g.m.regs cpu) p')
    def hartObsPermit := □ ∀ cpu p p', hartObsStep cpu p p'
    theorem swp_writeReg_priv : hartObsStep cpu p p' ∗ cur_privilege ↦ᵣ p ∗ ▷ (cur_privilege ↦ᵣ p' -∗ Φ ())
      ⊢ swp cpu (writeReg .cur_privilege p') Φ

(fixed-layer, `MachCSL/Resources.lean`; `swp_run` finds the one-write permit as `Hpriv`).  The five `UTrap`
towers take `hartObsStep cpu User Supervisor`; `execSpecF_sretU`'s input frame and `wpLoop_s_sretU` take
`hartObsStep cpu Supervisor User`.  **Holder (coordinator ruling (b′)).**  `wireInv(At) := inv wireN body ∗
hartObsPermit`; the power thread seals it at power-on from `obsInv` and the new hook `wp_power.Huser` (the trace
predicate accepts a user event; `hartObsPermit_of_hook`), which `riscvPowerAdequacy` / `riscvTraceAdequacy` /
`xv6PowerAdequacyGen` take as a hypothesis (`obsPredAt_user` at the unit instance, `obsLedgerAt_user` at a
ledger), and `Xv6AppLaws` gains `al_user` (`union_al_user`: the union ledger is unchanged by computation; triv:
`emp`).  Walker: `UFoot.noPriv` (no walk writes `cur_privilege`; `uFootL`'s `Dw` excludes it); the
`URunRWDemo` ECALL-through-the-walker facts are retired.

Statements that moved.  MachCSL: `Obs`, `primStep` (+inv/live/dead), `wpHart_lift` (callback),
`swp_event(_step)` (+defaulted `hsil`), `swp_writeReg(_bind)` (+`hq`), the five `UTrap` towers, `execSpecF_sretU`,
`wpLoop_s_sretU`, `wireInv(At)`(body) / `wireInv(At)_alloc` (+permit), `wp_power` / `riscvPowerAdequacy` /
`riscvTraceAdequacy` (+`Huser`), `UFoot` (+`noPriv`), `openSeg_power` (`isPower`), `obsNoPower_of_boots` (I/O or
user).  Xv6: `xv6PowerAdequacyGen` (+`Huser`), `Xv6AppLaws` (+`al_user`), **`SpecUserret.wp_userret_body`
(+`wireInv ∗` after `kctx`: userret's own `sret` needs the permit and the spec held no ambient that has it)**,
`ust_swp_exec_trap`/`UstTower` (+`hartObsStep`), `ust_trapArmGen`/`ust_trapArm`/`ust_armOb_*`/`uk_armOb_interrupt`
/`uk_armOb_trap`/`ust_fetchArm`/`ust_step_active`/`uk_fetchArm` (+`wireInv ∗` after `hwConfig`),
`ust_obligationActive_holds` (+`wireInv -∗`), `userret_usret`/`userret_exit`/`userret_user_run` (+`wireInv ∗`),
`ufFoot_wr` (`ufRwList.erase .cur_privilege`).  Byte-identical: `hartStep`, `SpecUser.USER`, `uexecF`,
`userInv`, `userTrapFrame`, `uvAmb`, every other Spec.

### M2-W3 (M0) as landed (2026-10-01)

Lane `lane/m2w3`.  **The class is {exit, getpid, uptime}**; sbrk, fork's parent, wait and console write were
examined and are NOT functional in (key, ι-prefix) today (below).  New pure `Xv6/UsysDet.lean`: `UIota` (the four
ledgers at the round: the allocator's `Kev` list, the pid ledger's `Pev` list, the zombie ledger's `Zev` list,
the tick count; readings `poolEmpty`/`nextPid`/`zombies`/`status`), `usysDetClass`, and `usysDet n W ι` = for
getpid / uptime the bumped key `bump W (usysDetRet n W ι) W.M W.perm W.sz W.fd W.cwd W.gen W.ch W.lazy W.secc`
with `usysDetRet` = `signExtend 64 W.pid` (getpid) or `usysUptimeWord ι.ticks` = the count truncated to 32 bits
and zero-extended (uptime); `W` itself at exit (never resumed: `uroundOk_exit`).  `usysDet_mem`/`usysDet_rows`:
the functional row satisfies every landed row; `usysDet_of_rows`: at a class number the landed rows at a
fitting ι (`usysIotaFits`: uptime's answer is `ι`'s count) PIN the bumped key to `usysDet` on the nose.

Discharges.  getpid: already functional in the key (`usysRetPid`, no ledger).  exit: no resume.  uptime: the
one row the kernel had to strengthen -- the arm (`SyscallArmsProc.syscall_arm_uptime`) now runs
`SYSUPTIME.wp_sys_uptime_led` and records the receipt's count as the new LAST `SyscRows` field `uptime :
syscNum V ≠ USYS_uptime ∨ usysUptimeRet (syscA0 V')`; `UsysMemOkSpec.syscMemOk_usys` (one premise more) and
`UsertrapSysRows` carry it into `usysMemOk`'s new uptime branch (`usysUptimeRet r ∧ identity`), so the round
relation `uroundOk` (unchanged text) carries it to the loop.  `UexecApply.uexecRet_roundDet` is `round_det`:
from `uexecRet_roundSlot`'s own premises and `hfit`, `ukeyEq (usysDet n (uvisRun W) ι) W'` (KEY equality: the
round pins the resume trapframe through its restored file and pc only); `_exists` supplies ι from the row.  The
engine's arm: `uexecRetF`'s TEXT is unchanged; with the uptime row in `usysMemOk` the relational arm's ∀ ranges
over exactly `usysDet`'s image, and `uexecRetContF_det` proves `uexecRetContF X n f W ⊣⊢ uexecRetDetF X n f W :=
∀ ι, spostAt … (usysDetRet n W ι) … -∗ X (usysDet n W ι)` at getpid/uptime.  A literal `if usysDetClass` branch in
`uexecRetF` would add nothing and break the generic program proofs (`UkRunSysDefs.uexecRet_retK`,
`UkRunSysQuiet`), so it was not cut; no `Uk*`/`Ush*`/`User*` file changed.

Rows NOT functional, and what they depend on (each a finding; details in `UsysDet`'s header):
- **sbrk** -- `SpecSysSbrk.sysSbrkOk`'s -1 disjunct is unconditional (spurious failure licensed even on the lazy
  grow and the shrink, which are key-functional in the code); the eager grow's kalloc COUNT depends on the page
  table's interior pages (not in the key) and its outcome on the positions of several interleaved `Kev`s, not one
  snapshot; and no receipt reaches the arm (L3b drops them; `growprocOk`/`sysSbrkOk` carry none).
- **fork (parent)** -- the pid ledger ties only the live set (R2(a)); the counter tie and first-ness (R2(b)/(c))
  are not stated, so the pid is not a function of the history; -1 depends on proc-slot exhaustion (no ledger) and
  on several kallocs (allocproc, uvmcopy -- page-table pages again); `SpecKfork`/`SpecSysFork` carry no receipt.
- **wait** -- kwait reaps the zombie child in the LOWEST PROC SLOT, and slots are allocproc's global
  first-UNUSED choice, which no ledger records (zombie ledger D3): with two zombie children WHICH pid wait
  answers depends on global slot placement -- **a channel not yet named (§2): proc-slot placement**.  Also -1 on
  `killed` (the kill channel) and on a status copyout that faults a lazy page (`vmfault` → `kalloc`).
- **console write** -- the trap contract has no write row (identity, `r` free); the kernel's answer
  (`writeConsArms`) has an EXISTENTIAL short count (`writeConsShort`: some byte in the faulting chunk) read off
  the page table `P`, not the key's `π` (untouched lazy pages are live in `π`, unmapped in `P`, and copyin does
  not fault them).

Statements moved: `SyscRows` (+`uptime`, last), `usysMemOk` (+ the uptime branch, after fork),
`syscMemOk_usys` (+`hup`), `syscRows_keep` (+`h14`, defaulted), the `SyscallArmsFdDefs`/`Path` row builders
(+`h14 : n ≠ 14`, defaulted).  Byte-identical: `uexecRetF`, `uexecRetContGen`, `uroundOk`, `uexecRet_roundSlot(_of)`,
every Spec but `SpecSyscall`, every `Uk*`/`User*` file.

### M2-W2 design (2026-10-02)

Design pass on `lane/m2w2` (based on `lean-m2`, which has W1 and W3). No code was landed. Rulings O1–O6 at the
end are needed before the lanes start. Short version: the permit carries **pure evidence plus one
machine receipt**. The machine layer gains a *read frame* at the privilege write, so it can say which event was
emitted, and a receipt that says where the event sits in the history. The client's half is a **pure filing
ledger**. Incarnations are identified by filing, not by `satp`.

**Four findings that shape the design.**
- **F1 (content needs a read frame).** `hartObsStep` receives `g`, and `g.m.regs cpu` *is* the event's
  content. But the permit cannot connect that file to anything the caller knows, because the rule
  (`swp_writeReg_priv`) holds only the `cur_privilege` cell. The values the event reads (`satp`, `scause`/`sepc`,
  `x1..x31`) are held by the caller. On U→S the arm's `uFr` holds them, plus the tower's `scause`/`sepc` it
  just wrote. On S→U `execSpecF_sretU` already frames `gprFile cpu R ∗ sepc ↦ epc`, and `satp` is in
  `confCells`. So the only way to tie "the event at position i" to "the registers this proof holds" is a rule
  that takes those cells as a read frame and proves `hartObsPriv cpu (g.m.regs cpu) p' = [e]` for an `e` built
  from them. The same holds for options (i) and (ii) of the brief. A Rut-lent permit (i) still needs it,
  because the residue knows the key but not the file.
- **F2 (the kernel has to construct something the client defines).** Until now every fixed-layer family
  (`rxTag`, `killCred`, `consRes`) is *minted by the client and carried opaquely by the kernel*. NI
  evidence runs the other way: only the kernel's loop knows the round and the key, and the ledger has to be
  told something whose meaning is Xv6's (`roundOkKeys`, the trap frame's layout). The kernel's proofs see an
  abstract `MachFixedGS`, so they need the field's definition as an equation. This coupling is unavoidable.
  The alternatives (a rider through `wireInv`, a sealed "factory", a global instance) all fail the same way:
  using an opaque field needs its equation, and a global-instance trick does not reach the user tier,
  which imports nothing that knows `Uvis`. The cheapest carrier is a Prop-class equation, modelled on
  `ClaimIs` (O2).
- **F3 (`satp` is not an identity).** A root is freed when a process exits, is killed, or runs a successful
  `exec`, and a later `kalloc` can hand the same page to a new process. `exec` also changes the root in the
  middle of an incarnation. A killed process's last `uExit` is never followed by its own `uEnter`. If the
  root is reused, the newcomer's first `uEnter` reads, by `satp`, as the "resume" of that exit. So
  `utrace s h` keyed by `satp` is false of real runs: `phi` would claim a transparent resume whose registers
  belong to another process. The fix is that the ledger *files* each enter against a round or an origin, and
  traces are read per filing (O1).
- **F4 (honest accounting needs an authority).** With persistent evidence, an enter can always be filed as an
  "origin", because "some key fits these registers" is always satisfiable. A run could then hide a round's law
  by declaring its resume a fresh incarnation. Closing this needs one-shot claims minted by the ledger:
  each exit claimable once as a round, each fork exit once more as a child's origin, each power-on once as
  initproc's origin. That is plumbing through `kfork`/`userinit` (W2d, O4). The core below is sound but has this
  loophole, so W4 must not publish the per-incarnation theorem before W2d.

**1. The ledger (where).** It lives in the existing trace slot (`obsPred`), not in a third fixed-layer slot.
Ruling 2 of `uart-trace.md` only keeps trace state out of `Pc`. The history ghost has exactly two halves
(machine / slot), so a third holder would re-split `obsName` and add a hook family at every power arm. It is
also not the app's `R`: the console ledgers are blind to user events (`cyclesOf_user`), and NI is a property
of the kernel, not of an application. So **`AppLaws` stays byte-identical** (`al_user` stays blind). The NI
ledger is a *second conjunct beside the app's `R`*, which W4's theorem composes as
`obsLedgerAt (fun h => A.R c h ∗ niR h)`. Every other slot, including the trivial `obsPredAt`, discharges the
enter hook by ignoring the evidence. In the core the ledger is **pure** (`Xv6/NiLedger.lean`, new, after
`UsysDet`):

    inductive NiEntry | origin (j : Nat) (W0 : Uvis) | round (i j : Nat) (sc : BitVec 64) (W W' : Uvis)
    def tfGprs (tf) : List (BitVec 64) := (List.range 31).map (fun k => tfW tf (5 + k))   -- = x1..x31 of tfResumeGpr0 tf
    def exitFits  (x : Obs) (sc) (W : Uvis) : Prop := ∃ cpu s, x = .uExit cpu s sc (tfW W.tf tfEpcIdx) (tfGprs W.tf)
    def enterFits (e : Obs) (W : Uvis) : Prop :=
      ∃ cpu s ep, e = .uEnter cpu s ep (tfGprs W.tf) ∧ retPc ep = tfResumePc W.tf
    def niFit : Option (Nat × Obs) → Obs → Prop               -- the evidence's meaning (O2's equation target)
      | none,        e => ∃ W0, enterFits e W0                 -- origin (W2d tightens: see F4)
      | some (_, x), e => ∃ sc W W', exitFits x sc W ∧ enterFits e W' ∧ roundOkKeys sc W W' ∧ W'.pid = W.pid
    def niOk (h : List Obs) (F : List NiEntry) : Prop :=
      (∀ f ∈ F, match f with
        | .origin j W0        => ∃ e, h[j]? = some e ∧ enterFits e W0
        | .round i j sc W W'  => i < j ∧ (∃ x, h[i]? = some x ∧ exitFits x sc W) ∧
                                 (∃ e, h[j]? = some e ∧ enterFits e W') ∧ roundOkKeys sc W W' ∧ W'.pid = W.pid) ∧
      (∀ j e, h[j]? = some e → isUEnter e → ∃! f ∈ F, f.j = j)          -- coverage: every enter is filed, once
    def niR (h : List Obs) : IProp GF := ⌜∃ F, niOk h F⌝
    theorem niR_snoc  : isUEnter e = false → niR h ⊢ niR (h ++ [e])                   -- exits, power, UART: blind
    theorem niR_enter : isUEnter e → niFit ox e → (∀ i x, ox = some (i, x) → i < h.length ∧ h[i]? = some x) →
                        niR h ⊢ niR (h ++ [e])                                          -- the filing

*Per user event in `h`:* every `uEnter` at position `j` has exactly one filing. A `round` filing names the exit at
`i < j`, the cause, and the trapped and resumed keys with `roundOkKeys`. An `origin` filing names the
incarnation's first key `W0`. Exits carry no filing: an exit is either cited by a round or is a final or
pending exit (a kill, `exit`, or a round still in flight). *At the end of the trace*, `niR h` gives
`∃ F, niOk h F`, which is all W4 needs (§4). The facts are monotone in `h` (prefix), so power, UART and exit
events step `niR` by `niR_snoc`. `niR` is timeless (pure). **`uhist` is not used**: `roundOkKeys` comes
straight from `urc_roundOkKeys` at `urc_exit`, ni-uhist's D5 append stays as it is, and R3 still holds.
`uhist` is the natural carrier for W2d's per-incarnation claims.

**2. The evidence at each boundary, and who has it.**
- **(a) S→U (kernel).** The event is `e = .uEnter cpu (satpOf .kpt P.root) sep (tfGprs ws)`.
  - `satp`: `userret`'s `csrw satp, a0` with `ha0 : k.regs 10 = satpOf .kpt P.root` (`wp_userret_body`).
  - The GPRs: `userret_exit`'s file `(urLoadSeq … R).set 10 (tfW ws 14)` equals `tfResumeGpr0 ws` off x0.
    The lemma is `UserretDefs.urLoadSeq_resume`, used today through `gprFile_ext` in
    `ProofUserret.userret_user_run`; the read-frame rule needs it *before* the `sret`, at `userret_exit`.
  - The pc: `UserretClosedResume.urc_resume`'s `hsep : retPc sep = tfResumePc V.tf`.
  - With `ws = V'.tf` and the slot key `uvisOf V' M' sts' gn cs' pid`, this is `enterFits e W'`.
  - `roundOkKeys sc W W'` is `UserretClosedRows.urc_roundOkKeys`, already called in `urc_exit`.
  - The pid tie is `hpid : W.pid = pid` plus `uvisOf`'s pid.
  - The origin path is forkret's first resume (`fkr_close` → `USERRET_CLOSED` → `urc_resume`, with no pending
    round), filed as `origin` at `W0 = uvisOf V M sts gn cs pid`.
- **(b) U→S (user tier).** The user frame holds the cells, so with the read-frame rule the arm learns exactly
  `x = .uExit cpu (satpOf .kpt pt.root) sc' sep' gs` and gets the machine receipt `uRcpt (i, x)`. The KEY is
  not needed at the exit. The trapped key `W` is *defined* by the slot from the trap frame
  (`UexecRet.trappedMachine` = `userTrapFrameAtm … (tfW W.tf tfEpcIdx) (tfResumeGpr0 W.tf)`), and the round's
  law is only known at the next enter. The options:
  - **(i) Rut lends a keyed exit permit.** It still needs F1's read frame, it changes `wpUserExecClosedBody`'s
    accessor premise, and it gains nothing, because the residue has no key-level fact about the exit. Rejected.
  - **(ii) A neutral witness, converted by the kernel.** Adopted, with the witness being the **machine's**
    receipt rather than a client tag: `uRcpt (i, x) := ∃ h0, ⌜h0.length = i⌝ ∗ obsHistLb (h0 ++ [x])`. It is
    persistent, unforgeable (the machine's own mono-list), and needs no client field. It travels **in
    `userTrapFrame`** (one more persistent conjunct over its existentials: `uRcpt (i, .uExit cpu (satpOf .kpt
    pt.root) sc sep (gprs g))`) to `urc_round`, where `trappedMachine` puts it at `W`. From there it is kept
    in the `□` context through `UV`/`UT` to `urc_exit` → `urc_resume`. "Converted" here means *cited* at the
    next enter's filing, not re-minted at `uservec`.
  - **(iii) Nothing cheaper exists:** F1 forces the frame, and the receipt has to reach the kernel through
    some USER-visible object. Of those, `userTrapFrame` is the one that already carries exactly the trap's
    values.
- **Every Spec or structure text that moves:**
  - `USER`, through `userTrapFrame`, which is referenced by `stvecHandlerWp`. The accessor premise is unchanged.
  - `userTrapFrameAt`/`Atm`, and so `UexecRet.trappedMachine` and the engine's `uexecF`/`ukb`. The *spelling* is
    byte-identical; the *meaning* changes through the definition.
  - `USERRET`: `wp_userret_body` gains a persistent `uRcptOpt ox ∗ ⌜MachFixedGS.uFit ox (.uEnter cpu
    (satpOf .kpt P.root) sep (tfGprs ws))⌝` beside `wireInv`.
  - `USERRET_CLOSED`, `FORKRET`, `FORKRET_PARK_PAID`, `USERINIT` and `MAIN`'s quantifiers gain `[NiFitIs]` (O2).
  - `xv6PowerAdequacyGen`: `Huser` → `HuserExit` / `HuserEnter`.
  - `AppLaws`: unchanged.

**3. The machine change (`MachCSL`).**

    -- Resources.lean
    def hartStep (e : Obs) (Out : IProp GF) : IProp GF :=          -- consent for EXACTLY e (replaces hartObsStep)
      ∀ h g, ⌜obsWf h g ∧ g.pow = true⌝ -∗ obsAuth h ={⊤}=∗ obsAuth (h ++ [e]) ∗ Out
    def uRcpt (ix : Nat × Obs) : IProp GF := ∃ h0, ⌜h0.length = ix.1⌝ ∗ obsHistLb (h0 ++ [ix.2])   -- persistent
    -- MachFixedGS: one new Prop field beside rxTag
      uFit : Option (Nat × Obs) → Obs → Prop        -- an enter's justification; Xv6 sets it to niFit
    def hartObsPermit : IProp GF :=
      □ ((∀ e, ⌜isUExit e⌝ -∗ hartStep e emp) ∧
         (∀ e ox, ⌜isUEnter e ∧ MachFixedGS.uFit ox e⌝ -∗ uRcptOpt ox -∗ hartStep e emp))
    theorem hartObsPermit_of_hook
      (HuserExit  : ∀ h e, isUExit e → ▷ obsPred ∗ obsHalf h ⊢ |==> ◇ (▷ obsPred ∗ obsHalf (h ++ [e])))
      (HuserEnter : ∀ h e ox, isUEnter e → MachFixedGS.uFit ox e →
                      (∀ i x, ox = some (i, x) → i < h.length ∧ h[i]? = some x) →
                      ▷ obsPred ∗ obsHalf h ⊢ |==> ◇ (▷ obsPred ∗ obsHalf (h ++ [e]))) : obsInv ⊢ hartObsPermit
    -- Wp.lean: the read-frame rules (swp_writeReg_priv retires; _quiet stays)
    theorem swp_writeReg_uexit (cpu) (s sc ep : BitVec 64) (gs : List (BitVec 64)) (Out Φ) :
      hartStep (.uExit cpu s sc ep gs) Out ∗ cur_privilege ↦ᵣ User ∗ hartRdX cpu s sc ep gs ∗
      ▷ (cur_privilege ↦ᵣ Supervisor -∗ hartRdX cpu s sc ep gs -∗ Out -∗
           (∃ i, uRcpt (i, .uExit cpu s sc ep gs)) -∗ Φ ()) ⊢ swp cpu (writeReg .cur_privilege .Supervisor) Φ
    theorem swp_writeReg_uenter (cpu) (p) (hp : privUser p = false) (s ep gs Out Φ) :   -- dual, hartRdE = satp, sepc, gprs

`hartRdX cpu s sc ep gs := satp ↦ s ∗ scause ↦ sc ∗ sepc ↦ ep ∗ gprCells cpu gs`, with
`gprFile cpu G ⊣⊢ gprCells cpu (gprList G)`. The proofs use `reg_valid` on the frame, then
`MonoList.lb_own_get` on the stepped authority for the receipt. The permit body validates the receipt against
`obsHistAuth` (`auth_lb_own_valid`), so hooks only ever see pure facts and no hook is lent the authority.

**Where it moves:**
- `UTrap`'s five towers: `hartObsStep cpu User Supervisor` → `hartStep (.uExit cpu s sc' sep' gs) Out ∗ satp ↦ s
  ∗ gprCells cpu gs`, with `Out` and the receipt passed to `Φ`. `Out` is generic so W2d does not touch the towers
  again.
- `execSpecF_sretU` / `wpLoop_s_sretU`: the consent is at `.uEnter cpu c.satp epc (gprList R)`.
- `wireInv(At)`: the text is unchanged (the permit's definition changes). `wireInv_step` splits into
  `wireInv_exit` / `wireInv_enter`.
- `Power.lean`: sealing from the two hooks. `riscvPowerAdequacy`: `Huser` → `HuserExit`/`HuserEnter`, and
  `bootFixedGS` gains the `uFit` argument. `riscvTraceAdequacy` and its blind R: both hooks via
  `obsLedgerAt_uexit`/`_uenter`, with `uFit := fun _ _ => True`.
- `obsLedgerAt_user` splits the same way.
- The hartObsPermit_triv / `obsPredAt` instance discharges both hooks blindly. `al_user` keeps its shape and
  is now used for both arms by the app's `R` part.

**4. How W4 consumes it.** Everything is pure, over `h` and the filing `F` from `niR`'s end-of-trace
reading (`obsLedgerAt_phi` at `fun h => ∃ F, niOk h F`):
- **The incarnation.** `inc h F j` is the era (`obsBoots (h.take j)`) and pid of filing `j`: `W0.pid`, or
  `W'.pid` of a round. Pids are not reused within an era (`nextpid` only grows; wrap-around is M2-G2's counter
  tie). Across eras they restart, hence the era.
- **The trace.** `utrace q h F` is the positions of incarnation `q`'s filings with their cited exits, in
  order, mapped to `h`. It replaces `utrace s h` (F3, O1). `firstKey q F` is the origin's `W0`.
- **`events h F`.** For the class it is only the uptime readings: per round filing with `scause = uecallScause`
  and effective number `usysEff W.secc tf = SYS_uptime`, the enter's `a0`. getpid needs nothing (its answer is
  `sext W.pid`, fixed per incarnation), and exit has no resume. Transparent rounds (`scause ≠ uecallScause`, the
  interrupt and lazy-fault rows) contribute nothing: `uroundOk`'s non-ecall branch is
  `uroundIdOk tf tf' ∧ <the rest unchanged>`. *Caution:* the class is decided by `usysEff W.secc`, and the
  seccomp mask lives in the key, not in `h`. So the Obs-level law reads `a7` through the incarnation's mask,
  which is a first-key datum like pid, constant until a (non-class) seccomp round.
- **The tick's source.** Read the delivered answer as the event; do not export `clockintr`. The tick is a
  software increment on cpu 0 in S-mode, with no hardware event to hang an observation on, and exporting a
  memory write would be a new language semantics. §6's argument is met because the reading *is* in `h`. Its
  honesty rests on §5: the clock is part of the schedule, which ι declassifies. The weakness is that the
  readings' cross-process monotonicity is not exported. W2c+ can add it by carrying the uptime round's `tickLb`
  into `niFit` (per era).
- **`phi`.** `phi g h := ∃ F, niOk h F ∧ ∀ q, NiClassLaw q (utrace q h F)`. Per round of `q`:
  - `scause ≠ ecall` → `uroundIdOk`, i.e. the enter replays the exit's GPRs and pc.
  - getpid → the same with `a0 := sext pid_q` and pc + 4.
  - uptime → `a0 := reading`, the rest kept.
  - Other ecalls: unconstrained.
  
  The proof is `usysDet_of_rows`/`uexecRet_roundDet` over `roundOkKeys`, which is in `niOk`. The two-run
  corollary is pure: equal `firstKey`, equal readings and equal exits imply equal enters. The strong instance
  in trace form: before its first ecall, `q`'s rounds are all transparent, so its enters replay its exits.
  T's "no ledger events" half stays in-logic, because the ledgers are not in `h`.
- **Precondition:** without W2d's claims, origins are free (F4) and `∃ F` admits filing a round as an origin.
  W4 may *develop* on the core but publishes after W2d.

**5. Lanes** (on `lean-m2`, one `lake` at a time, `lake build Xv6 MachCSL` + `tools/ci/lint.sh`, no `sorry`):

| Lane | Content | Moves | Gate |
|---|---|---|---|
| **W2a machine** | §3: `hartStep`, `uRcpt`, `uFit` field (+`bootFixedGS`), read-frame rules, permit split + sealing, the five towers, sretU, adequacy hooks; Xv6 kept green with `uFit` at `True` in `xv6FixedGS` and receipts dropped at the callers (`uf_trapCells` lends `satp` + GPR cells; `ProofUserret` takes `wireInv_enter` at `none`) | MachCSL statements above; `xv6PowerAdequacyGen` hooks; `UstTower`/`ust_*` signatures | full `run_all.sh` (device suite, `check-gen`), TCB: `Lang`-adjacent `Resources`/`Wp` |
| **W2b user receipt** | the receipt from the tower to `userTrapFrame` (rider `ustR`/engine rider, `UserStepClose`, `UserFrame:454`, `UkArms`/`UkFetchArm`/`UkEngine`/`UkLand`/`UkBundle`), `userTrapFrame(At/Atm)` + `trappedMachine_frame`, `userTrapFrame_open` | `USER` (via `userTrapFrame`) | full; audit baseline (USER is a root) |
| **W2c the ledger + kernel filing** | `NiLedger.lean` (§1), `NiFitIs` class + instance at `SystemBootEra` (beside `hClaim`), `xv6FixedGS` sets `uFit := niFit`; `urc_round` keeps the receipt, `urc_exit`/`urc_resume` take `ox` and file (round or origin), `wp_userret_body` premise; `[NiFitIs]` through the cone (UserretClosed*, ForkretClose, Spec/ProofUserretClosed, Spec/ProofForkret, Spec/ProofForkretPark, Spec/ProofUserinit, ProofMain, MainFs, Link*) | `USERRET`, 5 structures' quantifiers | full |
| **W2d claims (owner, O4)** | ledger-minted one-shot claims: exit consent `Out := MachFixedGS.uClaim e` carried in `userTrapFrame`; fork exits yield a second claim routed through `SpecKfork` to the child's park; power-on yields initproc's claim through the era turn; `niR` becomes `∃ F, ⌜niOk⌝ ∗ claimAuth γni …` at a birth-allocated name | `SpecKfork`, `SpecUserinit`, `xv6PowerAdequacyGen`'s birth, `USER` (a second conjunct) | full |

W2a and W2b can go in sequence in one Opus lane (each about 15–25 files, mechanical). W2c is the content.
W2d is gated on O4.

**RULINGS (2026-10-02; O1/O2/O5/O6 by the coordinator as recommended, O3/O4 by the owner):** O1 incarnations by
filing (era, pid), not `satp`. O2 the kernel's equation carrier is the Prop-class `NiFitIs`. O3 ACCEPTED: USER's
text moves by the one persistent receipt conjunct in `userTrapFrame`. O4: W2a–c now; W2d (claims) BEFORE W4
publishes; W4 may be developed on the core meanwhile. O5 the uptime reading is the tick event (optional per-era
monotonicity later). O6 `phi` is `∃ F`. Lane order: W2a+W2b (one lane, in sequence) → W2c → W2d → W4.

**Owner rulings requested.**
- **O1.** Incarnations by filing (era, pid), not `satp` (F3). The alternative, a `satp`-keyed trace truncated
  at the first non-class exit, is pure but drops every later incarnation on a reused root and still misreads
  a kill.
- **O2.** The kernel's equation carrier: a Prop-class `NiFitIs` (`MachFixedGS.uFit = niFit`) bound in the
  forkret/userret-closed cone (about 20 files, 5 structure quantifiers), recommended. It cannot ride
  `ClaimIs`, because `SchedCtx` sits below `Uvis`. The alternative hosts the class law
  (`scause`/`a7`/`a0` rules) in MachCSL as a pure def: no class, but MachCSL learns xv6's ABI and every G-lane
  edits it.
- **O3.** USER's text moves by one persistent conjunct in `userTrapFrame` (unavoidable by F1, §2(iii)).
- **O4.** W2d (claims) before W4 publishes (F4), or accept a per-round-only W4 statement.
- **O5.** The uptime reading as the tick event, with optional per-era monotonicity.
- **O6.** `phi` is `∃ F`. The filing is part of the run's witness, the same way first keys are. The two-run
  corollary is stated per incarnation at equal first key and readings.

### M2-W2a+b as landed (2026-10-02)

Lane `lane/m2w2ab` (on `lean-m2`), two commits.  **W2a (machine).**  §3 as written, with three deviations:
(1) the exact-event consent is named `hartObsStep (e : Obs) (Out : IProp GF)` (W1's per-write `hartObsStep cpu p p'`
retires; `MachCSL.hartStep` is the language's step relation and keeps its name);
(2) RULING P2: the permit carries a TEMPORARY third, blind entry arm, because the kernel's `sret` proofs are
generic in the `MachGS` instance and cannot know `uFit none e` without the W2c Spec move
(`USERRET` then carries the evidence);
(3) the uenter rule also hands back a receipt (`∃ i, uRcpt (i, e)`), as the dual of the exit rule.  Statements:

    def hartObsStep (e : Obs) (Out : IProp GF) : IProp GF :=
      ∀ h g, ⌜obsWf h g ∧ g.pow = true⌝ -∗ obsAuth h ={⊤}=∗ obsAuth (h ++ [e]) ∗ Out
    def uRcpt (ix : Nat × Obs) : IProp GF := ∃ h0, ⌜h0.length = ix.1⌝ ∗ obsHistLb (h0 ++ [ix.2])
    def hartObsPermit : IProp GF :=
      □ ((∀ e, ⌜isUExit e = true⌝ -∗ hartObsStep e emp) ∧
         (∀ e ox, ⌜isUEnter e = true ∧ MachFixedGS.uFit ox e⌝ -∗ uRcptOpt ox -∗ hartObsStep e emp) ∧
         (∀ e, ⌜isUEnter e = true⌝ -∗ hartObsStep e emp))          -- M2-W2a interim
    swp_writeReg_uexit cpu s sc ep gs Out Φ : hartObsStep (.uExit cpu s sc ep gs) Out ∗ cur_privilege ↦ User ∗
      hartRdX cpu s sc ep gs ∗ ▷ (cur_privilege ↦ Supervisor -∗ hartRdX … -∗ Out -∗ (∃ i, uRcpt (i, .uExit …)) -∗ Φ ())
      ⊢ swp cpu (writeReg .cur_privilege .Supervisor) Φ
    swp_writeReg_uenter cpu p (hp : privUser p = false) s ep gs Out Φ : the dual over `hartRdE cpu s ep gs`

`gprCells cpu gs` (Wp: the explicit `x1..x31` cells, a match on a 31-element list, `False` otherwise),
`gprList`/`gprFile_gprCells` (KCtx), `isUExit`/`isUEnter` (ObsTrace), `MachFixedGS.uFit` (+ `bootFixedGS`'s last
argument `Uf`, `AppIface.bootFixedGS`'s last argument; `xv6FixedGS` passes `fun _ _ => True`), `swp_run` through
`swp_writeReg_uexit_bind`/`_uenter_bind` (names `Hpriv`, `Hsatp`, `Hscause`, `Hsepc`, `Hgprs`; back `Hout`,
`Hrcpt`).  Towers: `hartObsStep (.uExit cpu s sc' sep' gs) Out ∗ satp ↦ s ∗ gprCells cpu gs`, `Out` and the receipt
to `Φ`.  sretU: consent at `.uEnter cpu c.satp epc (gprList R)`, `Out` generic, receipt dropped.
`wireInv_exit`/`wireInv_enter` (+ interim `wireInv_enterBlind`).  Hooks `HuserExit`/`HuserEnter`/`HuserEnterBlind`
in `wp_power`/`riscvPowerAdequacy`/`xv6PowerAdequacyGen`; `obsLedgerAt_uexit`/`_uenter` (via `obsLedgerAt_userP`);
`obsPredAt_user` is evidence-blind and discharges all three hooks; `riscvTraceAdequacy` fixes `Uf := True`, and its
`HuserEnter` is blind.  `al_user`'s text is unchanged and serves every arm.

**The M2-W2a interim items W2c removes** (each one is marked `M2-W2a interim: W2c removes this`):
the third `hartObsPermit` conjunct and `hartObsPermit_enterBlind` (Resources); `hartObsPermit_of_hook`'s
`HuserEnterBlind`; `wireInv_enterBlind` (WireInv); `wp_power`'s `HuserEnterBlind` and its use at the sealing
(Power); `riscvPowerAdequacy`'s `HuserEnterBlind` and its pass-through, plus `riscvTraceAdequacy`'s third hook
(Adequacy); `xv6PowerAdequacyGen`'s `HuserEnterBlind`, plus its triv instance (SystemAdequacy); the ledger's
third hook (AppLaws); and the kernel's two `sret`s (`UserretPt.userret_usret`,
`UserKernelBridge.wpLoop_userret_sret`).

**W2b (user receipt).**  `userTrapFrame`/`userTrapFrameAt`/`userTrapFrameAtm` gain one last conjunct
`(∃ i : Nat, uRcpt (i, .uExit cpu (satpOf .kpt pt.root) sc sep (gprList g)))`.  USER's text moves only through it.
`SpecUser.wpUserExecClosedBody`'s text is byte-identical, and no `Spec*.lean` changed in W2b.  The carry runs as
follows:

- **The rider.** `UserFrame.ufExitEv`/`uxRcpt` (a user file, or the receipt of the exit the file names).
  `UserStepTrap.ukRider cpu Rr := fun _ s2 => Rr ∗ uxRcpt cpu s2.file`, and `ustR cpu := ukRider cpu emp`.
  `ust_trapArmGen` mints it from the tower's receipt (`ufExitEv_trapS`); the retire/wait arms mint it from
  `priv = User`.
- **Through the landing and the tick.** `ucLand_rcptRegs`, `uxRcpt_land_tick`.
- **Into the frame.** `UserStepActive.ust_step_active`'s continuation gains `uxRcpt cpu s3.file -∗`, and
  `ust_close`/`ust_close_trap` take it.  `uf_close_trap` takes `∃ k, uRcpt (k, ufExitEv cpu f)`.
- **The engine.** The rider is `ukRider h (uxTextOwn …)`; `uk_fetchArm` gains `hRtU` (a retire lands at User);
  `uk_armOb_retire` gains `hpr`; `uk_trapped` takes `uxRcpt cpu s.file`.
- **Kernel side.** `userTrapFrame_trapped` re-keys the receipt to `g0` (`gprList_ext`).
  `UserKernelBridge.userTrapFrame_open` exposes the receipt as its last conjunct; `uservec_frame_open` drops it,
  since W2c is its first consumer.  `urc_frame_rut` keeps it in the frame.

Gates (both commits): full build, `lint.sh`, `tcb.sh` (`expected.json` unchanged; line counts only),
`audit.sh` (baseline unchanged), `run_all.sh vtest`.

Not ported: 42666b2b7 (`tools/intr_cone.py`, a Rocq-module cone audit; the Lean counterpart is a
`tools/` item for when T lands).  Rocq's L3 and T were never landed; they stay future work.

### M2-W2c as landed (2026-10-02)

Lane `lane/m2w2c` (on `lean-m2`), one commit.  **The ledger** (`Xv6/NiLedger.lean`, new, imported after
`UhistDefs`): §1 as written -- `tfGprs`, `exitFits`, `enterFits`, `niFit`, `NiEntry` (+ `NiEntry.j`), `niOk`,
`niR h := ⌜∃ F, niOk h F⌝` (timeless, persistent), `niR_nil`, `niR_snoc`, `niR_enter` (pure cores `niOk_nil`,
`niOk_snoc`, `niOk_enter`) -- plus the bridge `gprList_tfResumeGpr0 : gprList (tfResumeGpr0 ws) = tfGprs ws`.
`niOk`'s per-entry clause is the named `niEntryOk`, and `∃!` is spelled out (iris-lean's notation shadows it).

**Where each entry is filed.**  `SpecUserret.wp_userret_body` gains `(ox : Option (Nat × Obs))` and, beside
`wireInv`, `uRcptOpt ox ∗ ⌜MachFixedGS.uFit ox (.uEnter cpu (satpOf .kpt P.root) sep (tfGprs ws))⌝`;
`ProofUserret` threads it to `UserretPt.userret_exit`/`userret_usret`, whose `sret` now takes
`wireInv_enter` (the restored file is `tfGprs ws` by `urLoadSeq_resume` + the bridge).
`UserretClosedResume.urc_resume [NiFitIs]` takes `ox` and `hfit : niFit ox e`:
- ROUND: `urc_round` keeps the exit receipt out of the trapped frame (`urc_frame_rut` now also returns it),
  `urc_exit` takes `uRcpt (i, x)` with `exitFits x sc W` and files `some (i, x)` with `urc_roundOkKeys` and the
  pid tie (`hpid`);
- ORIGIN: `ProofUserretClosed.userretClosed_proof` (forkret's first resume, hence userinit's too) files `none`
  at the slot's own key (`urc_fit_origin`).
`UserKernelBridge.wpLoop_userret_sret` takes the same evidence.

**`[NiFitIs]`** on the five structures (`USERRET_CLOSED`, `FORKRET`, `FORKRET_PARK_PAID` -- both fields --,
`USERINIT`, `MAIN`) and on: `urc_resume`, `urc_exit`, `urc_round`, `urc_loop`, `fkr_close`,
`fkr_tail_close`/`fkr_steady`/`fkr_boot`, `forkret_park_paid`/`fkp_cap`/`park_token_intro`,
`ui_finish`/`ui_publish`, `mn_userinit`, `mn_phaseB`/`mn_phaseC`, `bootHartPrimary`,
`xv6Era_harts`/`xv6Era_run`; the instance `hNi` beside `hClaim` in `SystemBootEra`.

**Interim removed**: the permit's blind arm, `hartObsPermit_enterBlind`, `wireInv_enterBlind`, the
`HuserEnterBlind` hooks of `hartObsPermit_of_hook`/`wp_power`/`riscvPowerAdequacy`/`xv6PowerAdequacyGen` and
their uses (`riscvTraceAdequacy`, `xv6PowerAdequacy`, `xv6AppAdequacy`); `grep 'M2-W2a interim'` is empty.

**DEVIATION (O2's shape).**  `NiFitIs` is an implication, `fit : ∀ ox e, niFit ox e → MachFixedGS.uFit ox e`
(`uFit_of_niFit`), not `eq : uFit = niFit`, and `xv6FixedGS` keeps `uFit := fun _ _ => True` (the boot
instance is `trivial`).  Reason: `xv6FixedGS` is named in `xv6PowerAdequacy`'s statement, so `uFit := niFit`
would pull `NiLedger` and its closure (`UhistDefs`, `UexecRound`, `UsysMemOk`, `UexecSlot`, ...) into that
root's trusted base, which this lane must not do.  The kernel only ever produces `uFit` from `niFit`, so the
implication is all it uses; W4's theorem instantiates a record at `uFit := niFit` (instance by `id`) with
`obsLedgerAt (fun h => A.R c h ∗ niR h)`, its `HuserEnter` hook then receiving `niFit`.  The system and app
theorems keep their slots (`obsPredAt` / `obsLedgerAt (A.R c)`), `AppLaws` and their statements unchanged
(`riscvPowerAdequacy`/`xv6PowerAdequacyGen` lose the interim hypothesis).

What remains: W2d (claims), W4.

### M2-W2d as landed (2026-10-02)

Lane `lane/m2w2d` (on `lean-m2`, W1, W3, W2a-c), one commit.  F4 is closed: every user entry is
filed by SPENDING a one-shot claim the trace slot minted.

**The machine (`MachCSL`).**  `MachFixedGS` gains three client slots, carried and never read (as
`syncTok`): `uClaimR : Nat → IProp` (the round claim of the exit at a position), `uClaimX : Nat → Obs →
IProp` (what an exit mints beside it: Xv6's ledger puts a fork ecall's child-origin claim there),
`uClaimO : IProp` (an origin ticket).  `uExitTok x := ∃ i, uRcpt (i, x) ∗ uClaimR i ∗ uClaimX i x`
(not persistent) and `uClaimFor ox := uClaimForRaw uClaimR uClaimO ox` (`some (i, _)` ↦ `uClaimR i`,
`none` ↦ `uClaimO`).  The permit's exit arm is `hartObsStep e (uExitTok e)` (the permit adds the
receipt at `h.length`, `hartObsStep_of_exitHook`); its entry arm takes `uRcptOpt ox -∗ uClaimFor ox -∗`.
Hooks: `HuserExit` returns `… ∗ uClaimR h.length ∗ uClaimX h.length e`; `HuserEnter` is handed
`uClaimFor ox ∗ …`; the power-on's yield (`powerYield`) and `powerBootRes` carry `uClaimO` after `Tn`.
`bootFixedGS`/`AppIface.bootFixedGS` take `Ucr Ucx Uco` after `Uf`; `riscvPowerAdequacy` takes
`Ucr Ucx Uco : CT → …` and states its hooks at them (`uClaimForRaw (Ucr c) (Uco c) ox` for the entry).
New helpers: `obsLedgerAt_uexitM` (minting), `obsLedgerAt_uenterS` (spending), `uexitHook_emp`,
`uenterHook_drop`, `powerHook_emp` (blind hooks at a record minting `emp`), `obsPredAt_uexit/_uenter`.

**The system theorem stays blind.**  `xv6FixedGS` passes `uFit := True` and `emp` for the three
claim families; `xv6PowerAdequacyGen`'s STATEMENT IS UNCHANGED (its proof hands `riscvPowerAdequacy`
the `emp` families and wraps `Hobs`/`HuserExit`/`HuserEnter` with `powerHook_emp`/`uexitHook_emp`/
`uenterHook_drop`); `riscvTraceAdequacy` likewise; `AppLaws` unchanged.  The boot instance `hNi`
gains `fork := fun _ _ _ => .rfl` (`emp ⊢ emp`).

**How each claim travels.**
- *Exit → kernel.*  The tower's `Out` is `uExitTok x`; the user tier's rider `uxRcpt` is now
  `⌜User⌝ ∨ uExitTok (ufExitEv cpu f)` (spatial); `userTrapFrame`/`At`/`Atm`'s last conjunct is
  `uExitTok (.uExit cpu (satpOf .kpt pt.root) sc sep (gprList g))` (USER's one NI conjunct, now the
  token).  `urc_frame_rut` leaves it in the frame; USERVEC hands it back (below); `urc_round` splits it:
  the receipt and `uClaimR i` go to `urc_exit` → `urc_resume`'s ROUND filing (`uClaimFor (some (i,
  x))`), `uClaimX i x` to `urc_deposit`.
- *Fork → child park.*  `urc_deposit [NiFitIs] … i x (hx : exitFits x sc W)` turns `uClaimX i x` into
  `uClaimO` by `NiFitIs.fork` at a fork ecall (`niForkExit_of_fits`, from `uvisNum W = fork`) and puts
  it into `syscForkIn` (under its `⌜syscNum V = fork⌝ -∗`); `syscall_arm_fork` moves it into
  `kforkPark` (new row after `Rc`); kfork drops it on `-1` and hands it to `parkToken_park_steady`
  (new premise), which parks it in `parkMode (some _) = firstDone ∗ uClaimO`; forkret's steady arm
  passes it through `fkr_steady` → `fkr_tail_close` → `fkr_close` to `USERRET_CLOSED` (new last row),
  whose ORIGIN filing spends it (`uClaimFor none`).
- *Power-on → userinit.*  The power hook mints `uClaimO` (NI: `initClaim γ b`, `niR_powerOn`);
  `powerBootRes_unpack` returns it beside `Tn`; `xv6Era_run` takes it (new premise after `B`) into
  `bootPrimarySupply` (after `initBootBundle`) → `MAIN`'s pre (after `initBootBundle`) → `ProofMain`'s
  phases → `userinitPark` (last row) → `parkToken_park` (new premise) → `parkMode none = initBootBundle ∗
  consReader ∗ uClaimO` → forkret's boot arm (`fkr_boot`) → `USERRET_CLOSED`'s origin filing.

**The NI ledger (`Xv6/NiLedger.lean`).**  Claims live on the shared `Xv6G.gmUnitG` camera
(`Nat ↦ ()`) at a name `γ`: `roundClaim γ i := γ ↪◯MAP[2 * i] ()`, `originClaim γ i := γ ↪◯MAP[2 * i +
1] ()`, `initClaim γ b := γ ↪◯MAP[2 * b + 1] ()` (a position is an exit or a power-on, never both).
`niOriginTicket γ := ∃ p, γ ↪◯MAP[2 * p + 1] ()`, `niExitMint γ i x := if niForkExit x then
originClaim γ i else emp`, `niSpend γ ox := uClaimForRaw (roundClaim γ) (niOriginTicket γ) ox`.
`niClaims γ h F := ∃ m, γ ↪●MAP m ∗ ⌜niOneShot h F ∧ ∀ k, get? m k = some () → niKeyOk h k ∧ k ∉
F.map NiEntry.key⌝`; `niR γ h := ∃ F, ⌜niOk h F⌝ ∗ niClaims γ h F` (timeless, NOT persistent).
`niOneShot h F` (pure, new): the filings' claim keys (`NiEntry.key`: a round's `2 i`, an origin's
`2 p + 1`) are pairwise distinct, each minted in `h` (`niKeyOk`: an exit; a fork exit or a power-on)
strictly before the enter it files.  Steps: `niR_alloc`, `niR_snoc` (non-enter, mints nothing),
`niR_exit` (mints `roundClaim γ h.length ∗ niExitMint γ h.length e`), `niR_powerOn` (mints
`initClaim γ h.length`), `niR_enter` (`niSpend γ ox ∗ niR γ h ⊢ |==> niR γ (h ++ [e])`), `niR_pure`
(`⊢ ⌜∃ F, niOk h F ∧ niOneShot h F⌝`).  `niExitMint_fork`/`initClaim_ticket` are the NI record's
`NiFitIs.fork` and power-hook conversions.

**W4's request (pid row).**  `niPidRow sc W W' := sc = uecallScause → usysRetPid (usysEff W.secc (tfOf
(tfResumeGpr0 W.tf) (retPc (tfW W.tf tfEpcIdx)))) (tfW W'.tf (tfArgIdx 0)) W.pid` is a new conjunct of
`niFit`'s round arm and of `niEntryOk`'s round clause (last); `urc_exit` supplies it
(`urc_niPidRow`, from usertrap's `utRetPid`).

**Statements that moved beyond the brief's list (flagged).**  (1) `USERVEC`: `uservecPost` gains a
last premise `uExitTok (.uExit cpu (satpOf .kpt P.root) sc sep (gprList g)) -∗` -- uservec used to drop
the frame's receipt; with exclusive claims inside it must hand the token back (SpecUservec deviation
9); the only alternative routes (the residue `Rut`, or a second conjunct beside `trappedMachine` in
`ukb`) move USER-interface texts instead.  (2) `syscForkIn`'s DEFINITION (hence `SYSCALL`/`USERTRAP`'s
meaning; their texts are byte-identical) carries `uClaimO`: the only carrier from the round to kfork.
(3) `USERRET_CLOSED`'s pre (+`uClaimO`), `MAIN`'s pre (+`uClaimO`), `parkMode` (hence `FORKRET`'s
meaning): the routes the brief describes.

**What W4 must absorb.**  `niR γni h` (the name a parameter, born by `niR_alloc` beside the trace slot;
`niR` is no longer persistent; `niR_nil` is gone); `NiEntry.origin j W0 p` (new LAST field `p`, the
spent claim's position); `niFit`/`niEntryOk`'s round arm gains `niPidRow sc W W'` (last conjunct);
`NiFitIs` gains `fork` (the NI instance: `niExitMint_fork`); the NI record's slots: `uClaimR :=
roundClaim γni`, `uClaimX := niExitMint γni`, `uClaimO := niOriginTicket γni`; its hooks:
`HuserExit` by `obsLedgerAt_uexitM` over `niR_exit`, `HuserEnter` by `obsLedgerAt_uenterS` over
`niR_enter` (`uClaimForRaw` is `niSpend` by `rfl`), the power-on arm minting `uClaimO` from `niR_powerOn`
+ `initClaim_ticket` (yield `cons ∗ Tn ∗ Uco c`); `riscvPowerAdequacy`'s new `Ucr Ucx Uco`; read the
end of the run with `niR_pure`.  `SystemBootEra`/`SystemAdequacy` edits are confined to `xv6FixedGS`'s
three new `emp` arguments, `xv6Era_run`'s new `uClaimO` premise (and its use in `xv6BootEra`:
`powerBootRes_unpack`'s 4th output `Huo`, passed to `hR`), the `hNi` fork field, and the
`xv6PowerAdequacyGen` proof's call (three `emp` families, the three hook wrappers) plus the
`xv6TraceHook` call's three `emp`s in `xv6FsAdequacy`.

### M2-W4 as landed (2026-10-02)

Lane `lane/m2w4` (rebased on `lean-m2` 38f8e4e02, W2d absorbed): the trace-level NI theorem, registered as roots.
Three new files and one generalization.

**`Xv6/NiTrace.lean` (pure; imports `NiLedger`, `UsysDet`).**  `NiEntry.pid`, `incOf h f := (obsBoots (h.take
f.j), f.pid)`, `inc h F j : Option NiInc` (`NiInc := Nat × BitVec 32`), `niFilingAt F j := F.find? (·.j == j)`;
`NiStep := origin (W0 : Uvis) (e : Obs) | round (secc : BitVec 64) (x e : Obs)`, `niStepOf h f`, `utrace q h F`
(the steps of `q`'s filings, in enter order), `firstKey q h F` (the trace's head origin's key); `exitView` (cause,
epc, `x1..x31`), `enterView` (resume pc, `x1..x31`), `gprsNum secc gs` (the effective number of an exit's
registers through a mask), `NiStep.reading` / `events q h F` (the uptime ecalls' `a0`: THE READINGS),
`NiStep.input` / `.output` / `.ecall` / `.replays`.  The law, verbatim:

    def niRoundLaw (secc : BitVec 64) (pid : BitVec 32) (x e : Obs) : Prop :=
      ∃ (sc ep : BitVec 64) (xg : List (BitVec 64)) (pc' : BitVec 64) (eg : List (BitVec 64)),
        exitView x = some (sc, ep, xg) ∧ enterView e = some (pc', eg) ∧
        (sc ≠ uecallScause → pc' = retPc ep ∧ eg = xg) ∧
        (sc = uecallScause → gprsNum secc xg ≠ USYS_exit) ∧
        (sc = uecallScause → usysDetResumes (gprsNum secc xg) →
          pc' = retPc (retPc ep + 4#64) ∧ eg = xg.set 9 (gprsA0 eg) ∧
          (gprsNum secc xg = USYS_getpid → gprsA0 eg = BitVec.signExtend 64 pid) ∧
          (gprsNum secc xg = USYS_uptime → usysUptimeRet (gprsA0 eg)))
    def NiStep.law (pid : BitVec 32) : NiStep → Prop
      | .origin W0 e => enterView e = some (tfResumePc W0.tf, tfGprs W0.tf)
      | .round secc x e => niRoundLaw secc pid x e
    def NiClassLaw (q : NiInc) (tr : List NiStep) : Prop := ∀ s ∈ tr, s.law q.2
    theorem niOk_classLaw {h : List Obs} {F : List NiEntry} (hF : niOk h F) :
        ∀ q, NiClassLaw q (utrace q h F)
    theorem niTwoRun {h₁ h₂ : List Obs} {F₁ F₂ : List NiEntry} (hF₁ : niOk h₁ F₁) (hF₂ : niOk h₂ F₂)
        (q : NiInc) (hcls : NiInClass (utrace q h₁ F₁))
        (hin : (utrace q h₁ F₁).map NiStep.input = (utrace q h₂ F₂).map NiStep.input)
        (hev : events q h₁ F₁ = events q h₂ F₂) :
        (utrace q h₁ F₁).map NiStep.output = (utrace q h₂ F₂).map NiStep.output
    theorem niStrongInstance {h : List Obs} {F : List NiEntry} (hF : niOk h F) (q : NiInc) :
        ∀ s ∈ (utrace q h F).takeWhile (fun s => !s.ecall), s.replays

The getpid row is W2d's pid row (`niPidRow` + `usysRetPid_getpid`) at the filing's pid, which `utrace q` makes
`q.2`; so `NiClassLaw` takes `q` and the getpid answer is a function of the incarnation (no reading).

**`Xv6/NiAdequacy.lean`.**  `def xv6NiPhi (_ : GState) (h : List Obs) : Prop := ∃ F, niOk h F ∧ niOneShot h F ∧
∀ q, NiClassLaw q (utrace q h F)`; `niLedgerR A c γ h := A.R c h ∗ niR γ h` and its laws (`niBirth`: the
application's birth plus `niR_alloc`, the name kept in the fixed part; `niLedger_R0`, `_pow` (a power-on mints
initproc's claim, `niR_powerOn` + `initClaim_ticket`, yielded beside the turn), `_back`, `_tx`, `_rx`, and THE
TWO HOOK DISCHARGES `niLedger_exit` (`al_user` + `niR_exit`: the mint) / `niLedger_enter` (`al_user` +
`niR_enter`: the filing, spending `niSpend`)); `xv6NiAppAdequacy` = `xv6PowerAdequacyGenU` at the fixed part
`A.fixed × GName`, `Uf := niFit` (`hUf := fun _ _ h => h`), `Ucr/Ucx/Uco := roundClaim γ / niExitMint γ /
niOriginTicket γ` (`hUfork := niExitMint_fork`), the slot `obsLedgerAt (niLedgerR A c γ)`, hooks
`obsLedgerAt_uexitM`/`obsLedgerAt_uenterS`, `Hphi` from `obsLedgerAt_phi` + `niR_pure` + `niOk_classLaw`.
(Elaboration note: the four record-dependent arguments are closed as separate goals after `refine`, by
`intro`-ing `EraInitBoot`/`EraEcho`'s binders; passed inline, the `fun p => A.pred p.1` vs `A.pred` unification
times out.)  **`Xv6/LinkNiAdequacy.lean`** (a Link file: it imports `ProofUser`), verbatim:

    theorem xv6NiAdequacy {hlc : HasLC}
        (g : GState) (Hgen0 : g.gen = 0) (Hpow : g.pow = false) (Hdisk : diskOf g.m.devs = fsImgDisk)
        (n : Nat) (κs : List Obs) (t2 : List Expr) (g2 : GState)
        (hsteps : ([Expr.power], g) -<κs>->ₜₚ^[n] (t2, g2)) :
        (∀ e2, e2 ∈ t2 → Reducible (e2, g2)) ∧ xv6NiPhi g2 κs
    theorem xv6NiTwoRun {hlc : HasLC}
        (g₁ g₂ : GState) (Hgen₁ : g₁.gen = 0) (Hpow₁ : g₁.pow = false) (Hdisk₁ : diskOf g₁.m.devs = fsImgDisk)
        (Hgen₂ : g₂.gen = 0) (Hpow₂ : g₂.pow = false) (Hdisk₂ : diskOf g₂.m.devs = fsImgDisk)
        (n₁ n₂ : Nat) (κs₁ κs₂ : List Obs) (t₁ t₂ : List Expr) (g₁' g₂' : GState)
        (hsteps₁ : ([Expr.power], g₁) -<κs₁>->ₜₚ^[n₁] (t₁, g₁'))
        (hsteps₂ : ([Expr.power], g₂) -<κs₂>->ₜₚ^[n₂] (t₂, g₂')) :
        ∃ F₁ F₂, niOk κs₁ F₁ ∧ niOneShot κs₁ F₁ ∧ niOk κs₂ F₂ ∧ niOneShot κs₂ F₂ ∧ ∀ q : NiInc,
          NiInClass (utrace q κs₁ F₁) →
          (utrace q κs₁ F₁).map NiStep.input = (utrace q κs₂ F₂).map NiStep.input →
          events q κs₁ F₁ = events q κs₂ F₂ →
          (utrace q κs₁ F₁).map NiStep.output = (utrace q κs₂ F₂).map NiStep.output
    theorem xv6NiStrongInstance {hlc : HasLC}
        (g : GState) (Hgen0 : g.gen = 0) (Hpow : g.pow = false) (Hdisk : diskOf g.m.devs = fsImgDisk)
        (n : Nat) (κs : List Obs) (t2 : List Expr) (g2 : GState)
        (hsteps : ([Expr.power], g) -<κs>->ₜₚ^[n] (t2, g2)) :
        ∃ F, niOk κs F ∧ niOneShot κs F ∧ ∀ q : NiInc, ∀ s ∈ (utrace q κs F).takeWhile (fun s => !s.ecall),
          s.replays

**The generalization (outside the new files, on top of W2d's edits).**  `SystemBootEra.xv6FixedGSU … Uf Ucr Ucx
Uco` (the literal at the record's enter justification and claim slots; `xv6FixedGS` := it at `True`/`emp`, text of
every statement naming it unchanged); `xv6BootEra` takes `Uf hUf Ucr Ucx Uco hUfork` and builds `NiFitIs` from
`hUf`/`hUfork`; `SystemAdequacy.xv6PowerAdequacyGenU` (the proof, `Uf hUf Ucr Ucx Uco hUfork` before `Pt`, the
hooks at `riscvPowerAdequacy`'s shape) and `xv6PowerAdequacyGen` (statement byte-identical) := it at
`True`/`emp` with W2d's wrappers (`powerHook_emp`, `uexitHook_emp`, `uenterHook_drop`).  No existing root's
statement, axioms or TCB moved.

**Honest scope.**  (1) The class is {exit, getpid, uptime}; other ecalls' enters are free; the two-run corollary
assumes `q`'s ecalls are in the class (`NiInClass`).  (2) Origins are honest by `niOneShot` (in the conclusion):
every filing spent a distinct claim minted before its enter (a round's at its exit, an origin's at a fork exit or a
power-on); that an origin's first KEY is the forked child's is not stated.  (3) THE MASK IS CARRIED PER FILING:
"constant within an incarnation until a seccomp round" is NOT provable from `niOk` (nothing ties a round's trapped
key to the previous round's resumed key), so each round step carries its trapped key's `secc` and the two-run
inputs include it.  (4) The uptime reading is the tick (O5); the law adds that it is a tick count's word.
(5) The filing `F` is existential (O6).

### Merge with the chroot bump (2026-10-03)

`lean` (M2 complete) merged with `origin/lean` at 4bfa3048b (the chroot kernel bump to xv6 b72cbac1, four
dead-code passes, the 18 dead modules, the dead-import sweep, the build-shape cuts).  **No statement of ours or
theirs changed** beyond the textual union at the 15 conflicted sites: wherever upstream threaded the root
(`initBootBundle … rt cw …`, `parkMode rt cw …`, `parkPkg … V.rti V.cwi …`, `ui_publish` on `IGETROOT`/`IDUP`
in place of `NAMEI_ROOT`), our origin ticket `MachFixedGS.uClaimO` rides beside it unchanged (`parkMode`'s two
arms, `userinitPark`, `wp_main_boot_body`, `bootPrimarySupply(_intro)`, `mn_phaseB/C`, `fkr_boot`,
`parkToken_park(_steady)`), and `[NiFitIs]` stays on `ui_publish`/`ui_finish`.  Upstream's dead-code passes had
deleted helpers that were dead in OUR tree too (`wireInv_alloc`, `wireInv_eq`, `wpLoop_s_sretU`,
`userInv_of_sret`, `userTrapFrame_open`, `wpLoop_userret_sret`, `userTrapFrameAt(_frame)`,
`userTrapFrameAtm_at`, `uf_drefU_acc`, `uf_swp_decode16/32`, `uf_cfg_walk`, `usysMemOk_perm`,
`bootFixedGS_obsPredTriv`/`_obsLedger`, `riscvTraceAdequacy`): those deletions were taken (our M2 edits to
them were edits of unreached code).  Two helpers M2 uses were restored in place (`-- restored for NI M2 …`):
`Resources.obsHistLb_prefix` (by `uRcpt_valid`) and `UsysMemOk.usysRetPid_getpid` (by `UsysDet` and
`NiTrace`), both deleted by dead-code pass 1 (baa85f62c).

**The key and the root.**  Upstream did NOT give `Uvis` a root field (`uvisOf` reads `V.cwi`, not `V.rti`),
and `usysMemOk` has no chroot branch (entry 24 falls to the default arm).  The W3 rows are unaffected: the
class {exit, getpid, uptime} reads neither the cwd nor the root, so no row claim became false.  But the root is
process-visible state that decides later fs calls' outcomes, so a future lane that grows the class to any path
call must first give the key the root (the cwd's twin, chroot.md §1) and `usysMemOk` a chroot row.
`UtRoundQuiet` (T's pure corollary, unreached) was deleted upstream; `niStrongInstance`'s comments say so.

### M2-G1 design (2026-10-03)

Design pass on `lane/g1` (based on `lean` 33ce10f9a). No code landed. The pure vocabulary in §1 was
shape-checked in a scratch file that `decide`s the examples; it is not in the tree. The rulings G1-R1…R6 at
the end are needed before a lane starts.

**Short version.** The channel W3 found is real, and it is narrower than "slot placement". `wait`'s
choice depends on four things: which slots hold the caller's children, which of those are zombies, their
exit statuses, and the order of the slots. Every write of those facts happens under `wait_lock`:
- the parent cell: kfork's `np->parent = p`, kexit's `reparent`, kwait's `pp->parent = 0`;
- the ZOMBIE store: kexit, holding both locks;
- the reap: kwait.

So **the slot-placement ledger is the zombie ledger, grown into a FAMILY ledger at the lock it already
lives at.** That means:
- one new event, `ZFork`: kfork's parent store, recording the child's slot, pid and generation;
- one new field each on `ZExit` (the reparent target) and `ZReap` (the reaped slot);
- two CHECKABLE ties that answer D3:
  - the parent cells, physical, in the same payload, against the fold;
  - a per-slot ghost-map entry, anchored in the slot's own lock payload at the state cell and the
    escrow, against the fold's zombie column.

`pid_lock` and the pid ledger are untouched, so G2 is independent. The authority does not split.

Fork's −1 on slot exhaustion is a **different** channel with a worse shape. allocproc's scan is not
atomic, so no snapshot of the slots decides it (F2). Naming it needs a new ledger kept in an *invariant*,
not in a lock payload. Even then fork's −1 stays non-functional through allocproc's and uvmcopy's
kallocs (G3). So it is designed here (§6) and **parked behind G3**.

**Findings.**
- **F1 (allocproc's choice is placement, not a function).** The brief says allocproc's scan runs under
  `pid_lock`. It does not.
  - `allocproc` takes each `p->lock` in turn (`ap_scan_acq`/`ap_scan_rel`). `pid_lock` is taken only in the
    inlined `allocpid`, after the choice, nested inside slot `j`'s lock.
  - So "first UNUSED slot" is not even a fact about one moment. The scan can pass slot 0 while it is USED.
    Slot 0 is then freed behind the cursor, and the scan takes slot 5 while 0 and 5 are both free.
  - The chosen `j` therefore cannot be computed from any history prefix. It must be RECORDED as an event,
    exactly as the pid is today: R2(a), "the outcome IS the event".
  - The honest vocabulary concedes slot indices of a family's children. A process can see slot order only
    through `wait`, and only for its own children.
- **F2 (fork's slot −1 is a window, not a snapshot).** The scan fails iff every slot `i` was non-UNUSED *at
  the instant the cursor visited it*.
  - That is a property of 64 instants. No single history prefix decides it.
  - It can be stated honestly only with an event `SFull act` whose well-formedness says: for each `i`, the
    slot was occupied at some ledger position inside the scan's window.
  - Positions inside the window need a ledger snapshot at each visit, taken while holding only slot `i`'s
    lock. A lock-payload ledger cannot give that, because the scanner does not hold its lock. An `inv`-held
    authority can (§6).
- **F3 (the kill arm of wait is vacuous at the boundary).** `usertrap` runs `if (killed(p)) kexit(-1)` after
  `syscall()`. The killed flag is monotone while the process lives (`KillRow`: `killRow ∗ killShot ⊢ kl ≠ 0`).
  So a round whose −1 came from `killShot` never resumes. The kill channel (§3) does not have to be named
  for wait.
  - G1c must check that usertrap's post-syscall `killed` read is the reading form (`wp_killed_r` with the
    block's row). Only then does the resume path refute a persistent `killShot gn`. If it is the plain
    form, G1c switches it.
- **F4 (the copyout −1 is the lazy channel, nothing new).**
  - `SpecCopyout`'s −1 arm names a byte not `uvaWmapped` at the ENTRY table `P`.
  - At `W.lazy = false`, `P` and the key's `π` agree on writability. G1c needs this lemma, next to
    `VmfaultQuiet`.
  - So at a non-null pointer the copyout outcome is a function of the key exactly when the process has no
    lazy pages.
  - At `W.lazy = true` a lazily absent page faults through `vmfault → kalloc`: the allocator's position,
    which is G3's territory (§3's channel).
- **F5 (the children's NAMES are in the key).** `ukeyEq` compares `W.ch`, a set of generations. So
  `usysDet wait` must compute `W.ch \ {γ'}`, which needs the reaped child's generation as a function of
  `(W, ι)`.
  - The generation is a ghost name, but the key already carries `gen` and `ch` (W3 accepted that).
  - `ZFork` therefore records it, and a tie with the payload's `gs` pins it (§1 T1).
  - The trace level never reads it (W4's law reads registers only).
- **F6 (W3's per-round ι is unanchored).** `SyscRows` is pure, and the uptime receipt `tickLb n` stops at the
  arm. So `uexecRet_roundDet_exists` supplies ι *from the answer*, and "∃ ι, W' = usysDet W ι" is only as
  strong as the SHAPE of `usysDet`'s dependence on ι.
  - G1 inherits this as it stands; it is not made worse.
  - The cure is one cross-cutting lane, M2-X (§4), which serves every ledger.

**1. The vocabulary (pure; `Xv6/ZombEv.lean` grows, no new file).** Events:

    inductive Zev where
      | ZFork (act : BitVec 64) (j : Nat) (pid : BitVec 32) (g : GName)   -- NEW: kfork's np->parent = p
      | ZExit (act : BitVec 64) (pid : BitVec 32) (xs : Int) (ip : BitVec 64)  -- + ip: reparent's target
      | ZReap (act : BitVec 64) (j : Nat) (pid : BitVec 32)              -- + j: the reaped slot

What each event means:
- **`ZFork`** is appended by kfork when it stores `np->parent = p` (`kf_wait_fork`, under `wait_lock`).
  - `act = p = k.proc`, the parent's slot address.
  - `j`, `pid` and `g` are the child's slot, pid and generation (`genSlot g (procAddr j)`,
    `genPid g pid`, all in scope there).
  - This is THE PLACEMENT EVENT. It is recorded where the placement becomes visible to the family, not at
    allocproc's choice (F1: there it is not a function anyway, and `pid_lock` is the wrong lock).
  - userinit appends none. Init's parent cell stays 0.
- **`ZExit`** gains `ip`, the `initproc` word `reparent` writes. The fold then needs no global init address.
  `act` is already the exiting slot's address (`procAddr j`, the PI-4 port).
- **`ZReap`** gains the slot `j`. The fold clears the right slot without having to prove that pids are
  unique among zombies.
- **No `SZombie`.** `ZExit`/`ZReap` already are the zombie transitions, and with the actor equal to the slot
  they are slot-indexed.

Readings (the scratch check's definitions):

    structure ZSlot where par : BitVec 64; gen : GName; zomb : Option (BitVec 32 × Int)
    def famStep (m : Nat → ZSlot) : Zev → Nat → ZSlot
      | .ZFork act j _ g     => fun k => if k = j then ⟨act, g, none⟩ else m k
      | .ZExit act pid xs ip => fun k => let s := m k
          let s := if s.par = act then { s with par := ip } else s          -- reparent
          if procAddr k = act then { s with zomb := some (pid, xs) } else s  -- the exiting slot
      | .ZReap _ j _         => fun k => if k = j then ⟨0, 0, none⟩ else m k  -- pp->parent = 0; freeproc
    def famOf (h) : Nat → ZSlot := h.foldl famStep (fun _ => ⟨0, 0, none⟩)
    def zHasKids (h) (a) : Prop := ∃ k < NPROC, (famOf h k).par = a          -- kwait's havekids
    def zLowest (h) (a) : Option (Nat × BitVec 32 × Int × GName)            -- least k < NPROC with
      -- (famOf h k).par = a ∧ (famOf h k).zomb = some (pid, xs): the slot, pid, status, generation

- `zombiesOf`/`statusOf` keep their meaning: `ZFork` steps neither, and the new fields are ignored.
  `statusOf_dom` is re-proved with one more arm.
- `zombLedAuth`/`zombLedLb`/`zombReceipt` are untouched: same camera (`MonoListG GF Zev`), same name
  (`wzlName`). The camera's carrier type changes, so every `Zev` pattern match moves. These are:
  `ZombEv`, `UsysDet`'s readings, `kw_reap_ghost`, ProofKexit's append, `waitAnsLed`.

**D3 revisited: the ties.** D3 was right that "by construction" is all a ledger nobody READS needs. G1's row
must be PROVEN from the ledger: kwait has to show `rv = (zLowest h me).pid`. That needs the scan's
observations, made under `wait_lock` and the slot locks, to equal readings of `h`. Two ties in
`WaitInvTies.waitInvResAt` (inside its existential block, beside `∃ h, zombLedAuth h`) do it:

- **T1 (parents, physical, same lock).** `⌜∀ k < NPROC, ps k = (famOf h k).par ∧ (ps k ≠ 0 → gs k = (famOf h
  k).gen)⌝`. Here `ps` is the payload's own 64 parent cells, so this is checked against code-written state.
  The four writers of `ps` all hold the payload:
  - boot: all zero at `h = []`;
  - kfork: the store and `ZFork`;
  - kexit: reparent, then the ZOMBIE store and `ZExit` with `ip` the word reparent wrote, in one critical
    section;
  - kwait: `pp->parent = 0` and `ZReap`.
  - The `gs` half holds because the generation `gs k` is pinned only while `ps k ≠ 0` (`genHalvesEnt k 0 g =
    emp`), and only kfork makes `ps k` nonzero.
- **T2 (zombies, anchored at both ends).** A ghost map at a new `WchG` name `wzsName` (a
  `GhostMapG GF Nat (Option (BitVec 32 × Int))` field of `WchGpre`).
  - The wait payload holds `ghost_map_auth wzsName 1 (fun k => (famOf h k).zomb)`.
  - Slot `k`'s lock payload holds the element `ghost_map_elem wzsName k (own 1) v`:
    - `v = some (pid, xstateVal xsv)` beside `exitTok V.gen pid (xstateVal xsv)` in `procDormant`'s ZOMBIE
      branch, at the escrow's own binders, so the status the parent copies out IS the ledger's;
    - `v = none` in the UNUSED branch and, through `procSlotsAt`, in every non-dormant arm.
  - Only two moves change the element:
    - kexit's ZOMBIE store, with both locks and both pieces in hand: `none → some`, with `ZExit`;
    - kwait's reap, with both: `some → none`, with `ZReap`, put back at the UNUSED re-close after
      freeproc.
  - Every other state change goes between non-zombie arms at `none` and frames it.
  - This is NOT D3's "mirror of a mirror". D3's flag was anchored at nothing the code writes. Here one end
    is the state cell and the escrow under `p->lock`, and the other end is the fold under `wait_lock`.

Cost of T2: `SchedCtx.procSlotsAt` gains a sixth conjunct, `if invDormant st then emp else zsElem pa none`.
- Its `CtxMorph` instance needs one more `instCtxMorphConst`.
- Seven `procSlots_*` lemmas change (`_used`, `_recast` with side conditions `st, st' ≠ ZOMBIE`,
  `_dispatch`, `_park_gen(')`, `_running(_intro)`).
- `ProcDefs.procDormant`'s xstate block gains the element. Its callers' `if_neg`/`if_pos` rewrites are
  mechanical.
- Four proofs destructure `procSlotsAt`: `ProcsInvAlloc` (boot: 64 elements born at `none` with the
  auth), `ProofAllocproc`, `ProofKwait`, `ProofKfork`.
- `procLockResAt`'s text does not change.
- The boot: `childrenBootRows` gains the auth at `fun _ => none`, and `ProcsInvAlloc` the 64 elements.

**2. The ghost: where it lives, and the permit.**
- **Authority: `wait_lock`, unsplit.** The scan and the reap that need it are both under `wait_lock`. kfork's
  parent store and kexit's ZOMBIE store are under `wait_lock` too. `pid_lock` holds nothing G1 reads.
- Born in `childrenBootRows` beside `zombLedAuth []`, plus `wzsName`'s auth at `fun _ => none`.
  `childrenRes_alloc` adds the name. `MainKvm.mn_pidWait_born` gains the map auth beside `zombLedAuth []`
  (its one caller, `ProofMain.mn_phaseB`, threads it). The 64 elements go to the slots in `ProcsInvAlloc`.
- **Receipts.**
  - (a) kexit: none (no post). The append stays in `kx_park`'s ZOMBIE ghost update.
  - (b) kfork: `kf_wait_fork` returns `zombReceipt h (ZFork p i pid g)`. kfork drops it. M2-X would carry
    it.
  - (c) kwait: `waitAnsLed`'s reap arm already carries `zombReceipt h (.ZReap act rv)`. Its pure part
    grows to `⌜zLowest h act = some (j, rv, xs, γ')⌝`. The −1 arm splits its reason:
    - the no-children reason becomes `∃ h, zombLedLb h ∗ ⌜¬ zHasKids h act⌝`, the lb taken under the lock
      at the decision;
    - the copyout reason is `nullst = false`, as today;
    - the kill reason is `killShot`, as today (F3: dead at the boundary).
  - `waitAnsLed_post`/`waitAnsLed_of` change accordingly. `waitAns` and every landed reader are unchanged.
- **The permit** (L3's rule: one `actLend_step` per actor-labelled append).
  - `ZExit` and `ZReap` already step. The new fields do not change that.
  - `ZFork` is a NEW actor-labelled append, so it costs ONE step in kfork's `wait_lock` section.
    `kf_wait_fork` takes `actLend p ke` and returns `actLend p (ke+1)`.
  - kfork holds its lend there (it lent it to allocproc and uvmcopy and got it back). `SpecKfork`'s post is
    already `∃ k' ≥ ke`, so no Spec text moves for the step.
- **The brief's "pair `SAlloc` with `PAlloc`" question does not arise for wait.** Placement is recorded at
  `ZFork`, under the family's lock, in the family's ledger. The pid ledger and `ap_found` are untouched.
  - If the owner wants the placement also at the choice point (G1-R1), the cheap form is `PAlloc act j
    pid`: one append, one step, the same event. A separate `SAlloc` in the pid ledger would be a second
    append and a second step for the same transition. Not recommended.

**3. The rows.**
- **kwait's proof (`ProofKwait`).**
  - `kw_scan`/`kw_slot`'s loop invariant already has `R 14 = 0 → ∀ k' < n, parents k' ≠ procAddr j`. It gains
    the first-ness half `∀ k' < n, parents k' = procAddr j → (famOf h k').zomb = none`, at the payload's
    `h`, which is constant while the scan holds `wait_lock`:
    - at a slot whose parent cell is the caller and whose state is not ZOMBIE, the slot's element `none`
      against T2's auth gives the reading;
    - at the found ZOMBIE slot, the element `some (pid, xs)` gives the pid and status;
    - T1 turns the cells into `famOf`'s `par` and `gen`.
  - So `kw_reap_ghost` concludes `zLowest h (procAddr j) = some (n, pid, xs, g)`.
  - `kw_nokids_ghost` concludes `¬ zHasKids h (procAddr j)`.
  - The sleep/re-scan path re-takes `h` at each acquire. Only the final, successful scan's `h` is cited.
- **The functional row (`UsysDet`).**
  - `UIota` gains a fifth field, `act : BitVec 64`: the round's actor, the caller's slot address. This is
    the caller's own placement, so it is public.
  - `usysDetClass` gains `USYS_wait`.
  - `usysDet USYS_wait W ι` is defined as:
    - **no children** (`¬ zHasKids ι.zev ι.act`): `bump W (-1) …`, everything else kept;
    - **`zLowest ι.zev ι.act = some (j, pid, xs, γ)`**: `bump W (sext pid) (usysWr W.M a0 (if a0 = 0 then []
      else le32 xs)) … (ch := W.ch.erase γ) …`;
    - **children, none a zombie**: unreachable on a resumed round (kwait sleeps), so `W` with r := −1 as a
      default, never cited.
  - **Not in the class** (the row's premise): `W.lazy = true ∧ a0 ≠ 0`. That is the copyout's allocator
    channel (F4), G3's.
    - So the class predicate becomes key-dependent: `usysDetClassAt n W`, at wait `W.lazy = false ∨ a0 = 0`.
    - `usysDetClass` itself stays the number set, and the dependence is an extra premise of `round_det`.
  - The copyout's −1 on a bad pointer at `lazy = false` is the arm `∃ d < 4, ¬ πWritable W.perm (a0 + d)`.
    This is a function of the key, so it joins the row as its first test (−1, nothing reaped, `ch` kept).
- **`SyscRows`** gains one last field after `uptime`:

      wait : syscNum V ≠ USYS_wait ∨ ∃ (hz : List Zev),
        syscWaitRow V V' (syscImg V M) (syscImg V' M') cs cs' hz V.procAddr    -- the pure image of the
                                                                                -- answer at the receipt

  - `syscWaitRow` is the four arms above, stated on `syscA0 V'`, the image and `cs'`.
  - `SyscallArmsWait.syscall_arm_wait` switches to the led kwait (`KWAIT.wp_kwait_led`; Lean has the
    field, the PI-4 port) through `SYSWAIT`. `SpecSysWait`'s eb body gains the led answer. It reads the row
    off `waitAnsLed`'s new pure parts and the copyout's window (`syscUwaitWr`, already there).
  - `UsysMemOkSpec.syscMemOk_usys` takes one premise more (as W3's `hup`). `UsertrapSysRows` carries it
    into `usysMemOk`'s wait branch, which becomes the functional arm (`usysWaitRet`, beside `usysUptimeRet`).
- **`round_det`.** `UexecApply.uexecRet_roundDet` extends its class case to wait at `usysDetClassAt`, and
  `_exists` supplies `ι.zev := hz` and `ι.act` from the row.
- **What stays non-functional in wait.**
  - The copyout at `lazy = true`, non-null: allocator, G3.
  - The kill arm: dead at the boundary, F3, so not a row.
  - Init's orphans ARE covered (T1 reparents to `ip`).
- **Fork's −1 is not re-admitted by G1** (§6):
  - the slot half needs F2's `inv` ledger;
  - the allocator half (allocproc's trapframe and `proc_pagetable` kallocs, uvmcopy's per-page and
    table-page kallocs, whose COUNT depends on the parent's page-table interior, which is not in the key:
    UsysDet §4 sbrk (b)'s obstacle) is G3's;
  - the pid on success is G2's.
  - `SyscRows.fork` keeps its text.

**4. W4's law.**
- **The family events cannot enter the trace.** `kexit`'s ZOMBIE store and the reap are kernel-internal
  writes, with no machine event to hang an `Obs` on. Their order relative to the parent's `wait` depends on
  the kernel's own interleaving, which is not in `h`. So `events h F` cannot RECOMPUTE `zLowest`. As for
  the tick (W2 O5): **read the answer as the event.**
- **What changes in `NiTrace`.**
  - `NiStep.reads` admits an ecall whose effective number is `USYS_wait`. `reading` is its enter's a0, so
    `events q h F` = q's uptime and wait readings, in order.
  - `niRoundLaw`'s resume clause covers wait through `usysDetResumes`: pc + 4, `x1..x31` kept but a0.
  - Its wait conjunct is the answer's shape: a0 = −1 or the sign-extension of a pid in `[1, PIDMAX]`
    (`usysWaitRet`, from `niFit`'s round arm, supplied at `urc_exit` like `niPidRow`).
  - `NiInClass` is read at `usysDetClassAt`. The trace has no `lazy` bit, so a wait ecall is in the class
    iff its key's `lazy = false` or its a0 argument is null. The filing's trapped key carries `lazy`, as it
    carries `secc` (W4's honest scope (3)).
  - `niTwoRun`'s hypothesis `events₁ = events₂` now includes the wait answers.
- **Honesty cost, stated plainly.** At the trace level, wait's answer is a declassified reading, like
  uptime's. The theorem says equal readings and equal inputs give equal outputs. It does not say WHY the
  reading is what it is. The content is in-logic, in M0's `round_det`: the answer is `zLowest` of a prefix
  of the family ledger at the caller's slot. That prefix records the children's forks (with placement),
  exits (with statuses), reaps, and the reparenting.
  - So what wait declassifies is: the family's exit order up to slot order, the statuses, and the slot
    placement of the caller's children (which concedes global slot occupancy at each fork, F1).
  - Without the in-logic row, the reading would be §2's rejected "oracle of outcomes". With it, the
    reading is honest in the same sense as O5's tick.
- **Rejected alternative: a per-filing family witness `z` in `NiEntry.round` with `a0 = pick z`.** `F` is
  existential (O6) and `z` would be tied to nothing in `h`, so it is the answer in disguise. It is no
  stronger, and it costs more.
- **What WOULD be stronger, M2-X ("ι export", cross-cutting; NOT G1).**
  - Carry each round's persistent receipt (`zombLedLb`, `tickLb`, later `pidLedLb`/`ledLb`) to the enter
    filing, through a fourth `MachFixedGS` client slot carrying persistent evidence beside `uClaimR`.
  - Keep in `niR` the longest lb seen per ledger. Two lbs of one mono-list are prefix-comparable
    (`MonoList` lb/lb validity), so `niOk` can state that **all cited prefixes of one ledger form a chain**.
  - Then `phi` quantifies ONE history per ledger per run, and the two-run hypothesis becomes "equal
    histories" instead of "equal readings". That is §2's ι, really exported.
  - The route is W2d's: syscall arm → `syscWaitOut` → usertrap → userret → filing. It serves ticks (the
    per-era monotonicity W2 deferred), wait, G2's pid and G3's allocator at once.
  - Recommended as its own lane after G1–G3.

**5. Lanes** (on `lane/g1`, one `lake` at a time; gate per lane: `lake build Xv6 MachCSL` + `tools/ci/lint.sh` +
no `sorry`; full `tools/ci/run_all.sh` at G1b and G1d; `tools/audit/baseline.json`/`tools/tcb/expected.json` in
the same commit when they move):

| Lane | Content | Files | Moves | Gate |
|---|---|---|---|---|
| **G1a vocabulary** | §1's events and readings, snoc lemmas, `famOf_take` (prefix reading), `zLowest_spec` (least, member, parent, zombie), `zHasKids_iff`, `statusOf_dom` re-proved | `ZombEv` (pure); every `Zev` match: `UsysDet`, `UserChildren` (`waitAnsLed`'s `ZReap act rv` → `ZReap act j rv`), `ProofKexit` (append), `ProofKwait` (`kw_reap_ghost`) | the `Zev` constructors; `waitAnsLed` (+ slot) | build + lint |
| **G1b the ties and the four transitions** | T1 in `waitInvResAt`, T2's camera (`WchGpre` field, `wzsName`), the elements in `procSlotsAt`/`procDormant`, the boot, kfork's `ZFork` append + lend step in `kf_wait_fork`, kexit's `ZExit … ip` + element move, kwait's `ZReap … j` + element move, the reparent re-establishing T1 | `SlotGen` (camera + name), `WaitInvTies`, `WaitInv`, `SchedCtx`, `ProcDefs`, `ProcsInvAlloc`, `MainKvm`/`ProofMain` (boot), `ProofKfork`, `ProofKexit`, `ProofKwait`, `ProofAllocproc` (frame), `ProofFreeproc` (frame), xv6GF/unionGF slot | `waitInvResAt` body; `procSlotsAt`, `procDormant` (definitions; statements naming them byte-identical); `kf_wait_fork`; `childrenBootRows` | full (camera change: ~1000-file rebuild); audits |
| **G1c kwait's first-ness and the led answer** | `kw_scan`/`kw_slot` invariant (first-ness), `kw_reap_ghost` → `zLowest`, `kw_nokids_ghost` → lb + `¬zHasKids`, `waitAnsLed` pure parts; F3's check of usertrap's post-syscall killed read; F4's `P`/`π` lemma at `lazy = false` | `ProofKwait`, `UserChildren`, `SpecKwait` (led body text through `waitAnsLed`), `VmfaultQuiet` (lemma), possibly `ProofUsertrap*` (F3) | `waitAnsLed`; `KWAIT.wp_kwait_led(_eb)` (via the answer) | build + lint |
| **G1d the rows and `round_det`** | `UIota.act`, `usysDetClassAt`, `usysDet` wait arm, `usysDet_rows`/`_of_rows` extended; `SyscRows.wait`; `syscall_arm_wait` on the led contract; `usysMemOk`'s wait branch functional (`usysWaitRet`); `uexecRet_roundDet(_exists)`; W4: `NiStep.reads`, `niRoundLaw`'s wait conjunct, `niFit`/`niEntryOk`'s round arm (+ `niWaitRow`, after `niPidRow`), `urc_exit` supplies it, `NiInClass` at the class-at | `UsysDet`, `SpecSyscall`, `SyscallArmsWait`, `SpecSysWait`/`ProofSysWait`, `UsysMemOk`, `UsysMemOkSpec`, `UsertrapSysRows`, `UexecApply`, `NiLedger`, `NiTrace`, `UserretClosed*` | `SyscRows` (+`wait`, last); `usysMemOk` (wait branch); `SYSWAIT`'s body; `niFit`; `NiInClass`; the three NI roots' statements are byte-identical (their meaning grows) | full; audit (roots' TCB) |

G1a→G1b→G1c→G1d in sequence (G1b is the wide one, mechanical; G1c is the proof content). Estimated: G1a small,
G1b ~25 files, G1c 3–5 files but the scan invariant is the hard part, G1d ~15 files (W3's and W2d's routes).

**6. Fork's −1 on slot exhaustion (G1f, designed, PARKED behind G3).**
- **Ledger.** A slot-OCCUPANCY ledger `Sev := SOcc j | SVac j | SFull act`. It is held in an Iris invariant
  `inv slotN (∃ h, slotLedAuth h ∗ ghost_map_auth wsoName (occOf h))`, with the element `occ j` in slot
  `j`'s lock payload: occupied in every non-UNUSED arm, vacant at UNUSED, the `pavSlot` position. It can't
  be a lock payload (F2).
  - allocproc's found arm appends `SOcc j` (`ap_found`, with slot `j`'s lock).
  - freeproc appends `SVac j` at the UNUSED store.
  - Each scan visit opens the invariant (a timeless fupd, no step) and takes a `slotLedLb` snapshot at
    which `occOf · i = occupied`.
  - The failure arm appends `SFull act` after the last release, with the window fact:
    `∀ i < NPROC, ∃ k ∈ [|h₀|, |h_end|], occOf (h.take k) i`.
  - `SOcc`/`SVac` are UNLABELLED (no step): the actor is already in the paired `PAlloc`/`PFree`. `SFull`
    is labelled and costs one step.
- **Cost.**
  - The `pavSlot` conjunct is generalised from a marker to the element.
  - Every slot-payload re-close at a state change across UNUSED gains a ghost-map update: allocproc,
    freeproc, the boot.
  - `ap_scan`'s 64-visit loop carries a chain of lbs.
  - `allocprocPostLed`'s null arm gains the `SFull` receipt and the window.
  - The steady regime's `procsAvail none` becomes redundant for the refutation. Boot keeps its count.
- **What it buys alone: nothing on the row.** fork's −1 also fires on allocproc's two kallocs and uvmcopy's
  kallocs, whose COUNT is not a function of the key (UsysDet §4 fork/sbrk (b)).
- **Re-admit fork as a joint lane G1f+G2+G3**: −1 iff `SFull` at the round, or `KNull` at one of the round's
  allocator positions as G3 states them. The pid on success, from G2's counter tie.

**RULINGS G1-R1…R6 (2026-10-03, coordinator, all as recommended; they follow O5 and the owner's "honest class, then grow"):** R1 placement recorded at kfork's parent store (`ZFork act j pid g`); R2 D3 overturned, ties T1 and T2; R3 the new fields; R4 the key-dependent class at wait (`usysDetClassAt`); R5 wait's answer is a READING at the trace level, with §4's honesty paragraph; M2-X (ι export) is a later cross-cutting lane; R6 fork's slot −1 parked behind G3. Lanes G1a → G1b → G1c → G1d in sequence.

**Owner rulings requested.**
- **G1-R1** The slot-placement datum is recorded at kfork's parent store (`ZFork act j pid g`, in the
  zombie/family ledger under `wait_lock`), not at allocproc's choice (F1). Recommended. The alternative,
  `PAlloc act j pid` in the pid ledger, records the same `j` one lock earlier, but nothing under `wait_lock`
  can read it.
- **G1-R2** D3 is overturned. Recommended: the two checkable ties T1 (parent cells) and T2 (per-slot ghost
  map anchored at the state and the escrow). G1's row must be PROVEN from the ledger, and by-construction
  cannot be read. Cost: `procSlotsAt`/`procDormant` definitions, a camera field, a full rebuild.
- **G1-R3** `ZExit` gains `ip`, `ZReap` gains `j`, `ZFork` carries the generation `g` (F5). Recommended. The
  alternative to `g` is to drop `ch` from `round_det`'s key equality at wait: weaker, and inconsistent with
  W3.
- **G1-R4** The class becomes key-dependent at wait (`usysDetClassAt`: `lazy = false ∨ a0 = 0`). Recommended.
  The lazy non-null copyout is G3's.
- **G1-R5** W4: the wait answer is a READING (O5's rule). Recommended, with the honesty paragraph of §4 in the
  as-landed note. M2-X (ι export) is a separate cross-cutting lane, after G1–G3.
- **G1-R6** Fork's slot −1 (§6) is parked behind G3 and re-admitted jointly. Recommended. The alternative,
  landing G1f now, costs the invariant-held ledger and moves no row.

Each lane's as-landed line goes under its row's design note (the Rocq notes' rule), and this table's
checkbox below flips when the lane is on `lean-ni`:

- [x] PI-1  - [x] PI-2  - [x] PI-3  - [x] PI-4  - [x] PI-5  - [x] PI-6  - [x] PJ-G  - [x] PJ-L1a  - [x] PJ-L1b  - [x] PJ-L2

### M2-G1a+b as landed (2026-10-03)

Lane `lane/g1`, two commits (G1a, then G1b).  Rulings R1-R6 as recommended.

**G1a (the vocabulary).**  `ZombEv`: `Zev = ZFork act j pid g | ZExit act pid xs ip | ZReap act j pid`;
`ZSlot {par, gen, zomb}`, `famStep`, `famOf` (`famOf_snoc`, `famOf_take`: the prefix reading), `zHasKids`
(decidable; `zHasKids_iff`: through T1's cells it IS the scan over the cells), `zScan`/`zLowest`
(`zLowest_spec`: least slot below NPROC, parent, zombie, generation, and first-ness).  `zombiesOf`/`statusOf`
unchanged in meaning (`ZFork` steps neither); `statusOf_dom` no longer exists (a dead-code sweep removed it),
so nothing to re-prove.  Statement moves: the constructors; `zombExit` (+`ip`), `zombReap` (+slot);
`waitAnsLed`'s reap arm `∃ h j, zombReceipt h (.ZReap act j rv)` (and `waitAnsLed_of`'s side row).  kexit's
`ip` is `kx_rest_root`'s own parameter (`initIdentAt curCtx ip`, the word `reparent` writes); kwait's slot is
`kw_reap_ghost`'s `n`.  **Deviation from §1: `ZFork` keeps the zombie column** (`{m k with par, gen}`):
kfork's parent store runs after `release(&np->lock)`, so the child's T2 element is in its lock payload and
cannot be read there; keeping the column makes the step's effect on T2's authority the identity.

**G1b (the ties and the four transitions).**
- Camera and name: `WchGpre.zsG : GhostMapG GF Nat (Option (BitVec 32 × Int)) RegMapF` (xv6GF/unionGF slot
  125), `WchG.wzsName` (`xv6GF_wchG` gains `γzs`).  The map is keyed by the slot's ADDRESS as a number
  (`pa.toNat`): the payloads that hold the elements are stated at `pa`.  `UserChildren`: `zsElem pa v`,
  `zsAuth f := ∃ M, ghost_map_auth wzsName 1 M ∗ ⌜∀ k < NPROC, get? M (procAddr k).toNat = some (f k)⌝`
  (a finite map cannot be a function; the authority is tied to the column below NPROC), `zsAuth_lookup`,
  `zsAuth_update`, `zsAuth_congr`.
- `WaitInvTies.famLed ps gs := ∃ h, zombLedAuth h ∗ ⌜∀ k < NPROC, ps k = (famOf h k).par ∧ (ps k ≠ 0#64 →
  gs k = (famOf h k).gen)⌝ ∗ zsAuth (fun k => (famOf h k).zomb)` replaces `waitInvResAt`'s trailing
  `∃ h, zombLedAuth h` (T1 and T2's authority).  The writers' steps: `famLed_fork`, `famLed_exit`,
  `famLed_reap`, `famLed_boot`; boot mint `zsRows_alloc`.
- T2's elements.  `procSlotsAt` gains `if st = ZOMBIE then emp else zsElem pa none` (**deviation: UNUSED's
  element is here, not in `procDormant`** -- `freeproc`'s post names `procDormant … UNUSED` and nothing it
  takes carries an element for a reaped ZOMBIE, so kwait puts it back at its re-close, as §2 says);
  `procDormant`/`procDormantNoctx`'s ZOMBIE branch holds `exitTok … ∗ zsElem pa (some (pid, xstateVal xsv))`.
  **Carriers across Spec texts that could not move** (no Spec text moved): `procHeldAt` carries the element
  at `zsHeld st` (RUNNING, RUNNABLE, SLEEPING) -- `sched`'s pre/post and `pSched`'s arms name `procHeld`, so
  it is the only route between the parking proc, the scheduler and the resumed proc; `FdTable.procPrivNocwd`
  carries it from allocproc to kfork/userinit (allocproc's post names it).  `procHeldAt_cases`/`_intro` take
  `¬ zsHeld st`; `_live_*` (at `zsHeld`) and `_gen_*` (conditional) are new.  `procSlots_dispatch` /
  `_running` return the element, `_running_intro` / `_park_gen(')` take it, `_recast` / `_used` unchanged
  (their side conditions already exclude ZOMBIE).
- The four transitions.  kfork: `kf_wait_fork` appends `ZFork p i pid g` (`famLed_fork`), takes `actLend p
  ke` and returns `actLend p (ke+1)` (kfork lends its block's counter there and takes it back: the parent's
  block comes back at `kev + 1`; `kforkPost` is `∃ k' ≥ ke`), returns the receipt (dropped).  kexit: the
  ZOMBIE store's `famLed_exit` (T1 = `reparent`'s cells `rpMap`, element `none → some` out of the RUNNING
  payload into the ZOMBIE block).  kwait: `famLed_reap` (T1 = the stored 0, element `some → none`, back at the
  UNUSED re-close after freeproc).  Boot: `childrenBootRows` gains `zsAuth (fun _ => none)` and each slot's
  element; `waitRes_alloc`, `mn_pidWait_born` take the authority, `mnSlotIn`/`procsInvSlot` the element.
- Statements moved (non-Spec): `waitRes_alloc`, `mn_pidWait_born`, `mn_slots_zip`, `mnSlotIn`, `procsInvSlot`,
  `procPriv_null_mint` / `procPrivNocwd_null_open`, the `procSlots_*` lemmas listed above,
  `procHeldAt_cases/_intro`, `kf_wait_fork`, `kw_reap_ghost`, `kw_dormant_freeprocIn`, `kw_pay_unused`,
  `kw_slots_unused_intro`, `kf_pay_unused`, `kf_slots_unused_intro`, `procSlots_used_intro`,
  `ap_slots_unused_elim/_intro`, `apPostCells`, `ui_slots_runnable`, `ui_finish`, `ui_publish`, `sleep_tail`,
  `kx_dormant_build`.  Spec texts: none moved.
- Not yet read by anything: `zLowest_spec`, `zHasKids_iff`, `famOf_take`, `zsAuth_lookup` (G1c's).

### M2-G1c as landed (2026-10-03)

Lane `lane/g1`, one commit on G1a+b.  No Spec text moved beyond `waitAnsLed` (so `KWAIT.wp_kwait_led(_eb)`'s
answers grow through it); `waitAns`, its readers, `SYSWAIT`/`SpecSysWait` untouched.

- **The named history.**  `WaitInvTies.famLed ps gs` is now `∃ h, famLedAt ps gs h` (`famLedAt := zombLedAuth
  h ∗ ⌜famTie ps gs h⌝ ∗ zsAuth …`, T1 the pure `famTie`); readers `famLedAt_tie`, `famLedAt_lookup` (T2,
  via `zsAuth_lookup`), `famLedAt_lb`.  `famLed_reap` is stated at `famLedAt … h` and returns
  `zombReceipt h (ZReap act n pid)` at that `h`.  `childrenInv_reap`'s pure conjunct adds `gs k = g`.
  `ProofKwait.kwWRest ξ ps h` names `h`; `kw_wait_pay_elim` opens `∃ parents h` once per acquire (the
  sleep/re-scan path re-opens at each re-acquire; only the final scan's `h` is cited).
- **The scan's first-ness.**  `kw_scan`/`kw_slot` carry `∀ k' < n, parents k' = procAddr j → (famOf h
  k').zomb = none` (the advance continuation at `n + 1`); `kw_slot_first` reads it at a visited non-ZOMBIE
  child off `procSlotsAt`'s element.  `kw_reap_ghost` (+ `zh`, `hfirst`) proves `zLowest zh (procAddr j) =
  some (n, pide, xstateVal xs, Vf.gen)` by `zLowest_spec` and appends the reap at `zh`.  `kw_nokids_ghost`
  returns `⌜cs = ∅ ∧ ¬ zHasKids zh (procAddr j)⌝ ∗ zombLedLb zh` (`zHasKids_iff` through T1).
- **`waitAnsLed`** (UserChildren): `(⌜rv = -1 ∧ cs' = cs⌝ ∗ waitWhyLed cs gn nullst act) ∨ ∃ h j γ',
  zombReceipt h (ZReap act j rv) ∗ ⌜zLowest h act = some (j, rv, xs, γ')⌝ ∗ ⌜cs' = cs \ {γ'} ∧ 1 ≤ rv ≤
  PIDMAX⌝ ∗ ⌜γ' ∈ cs ∨ pidv = 1⌝ ∗ exitTok γ' rv xs ∗ genUniq cs rv γ'` -- the reading at the receipt's
  prefix (before the reap).  `waitWhyLed := ⌜nullst = false⌝ ∨ (⌜cs = ∅⌝ ∗ ∃ h, zombLedLb h ∗ ⌜¬ zHasKids h
  act⌝) ∨ killShot gn`.  **Deviation from §2(c): the no-children reason KEEPS `cs = ∅`** beside the ledger's
  reading (`waitAnsLed_post` must produce the landed `waitWhy`).  `waitAnsLed_post` (drop), `waitAnsLed_neg`,
  `waitAnsLed_of` (now the reap arm's builder at the explicit `γ'`, with Rocq's generation crossing folded in).
  Deleted as unreached after the switch: `waitAnsGen`, `waitAns_of_gen`, `waitWhy_notnull/_empty/_shot`
  (replaced by `waitWhyLed_*`), `famOf_take` (genuinely unneeded).  `zLowest_spec`, `zHasKids_iff`,
  `zsAuth_lookup` are now reached from `KWAIT`'s proof.
- **F3: no change needed.**  usertrap's post-syscall check (+0xa6, `UsertrapTailA6`) is already the reading
  form: `KILLED.wp_killed_r` with `utKillRead gn (utKillOut … ∗ ⌜utLive …⌝)`, lending `utLiveRes = (… ∗
  ⌜utLive⌝) ∨ killShot gn`; at a zero flag `UsertrapParts.ut_kill_lend` refutes the shot
  (`KillRow.killPaid_shot_nz`), and `usertrap_a6_after` resumes (UT_RET) only off `⌜utLive A V2 cs2⌝`.  So a
  round whose `-1` came from `killShot` never resumes; G1d cites `ut_kill_lend` / `usertrap_a6_after`.
- **F4.**  `VmfaultQuiet.lazyFree_wmapped_iff (P) (sz) (hwf : uptWf P) (hlf : lazyFree P.um sz) (va : Nat) :
  uvaWmapped P va ↔ ∃ q, permOf P.um sz.toNat (va / 4096) = some q ∧ q.W = true` -- every `va`, no size
  premise.  Unreached until G1d: allowlisted in `tools/ci/dead_allow.txt` (remove the row when G1d lands).

### M2-G2 design (2026-10-03)

Design pass on `lane/g2` (based on `lean` 0dec77fa1: G1a–c landed, G1d running in parallel on `lane/g1`). No
code landed. The pure vocabulary of §1 was shape-checked in a scratch file: `liveB`, `cycAt`, `pidPick`,
`cycAt_zero`, `cycAt_succ` proved, plus five `native_decide` examples (the wrap and the F4 witness among
them). It is not in the tree. The rulings G2-R1…R5 at the end are needed before a lane starts.

**Short version.**
- **The brief's premise is the pre-ded23f2 kernel.** "`pid = nextpid++`, no wrap, so first-ness is trivial"
  was true before upstream's ded23f2. The pinned kernel WRAPS and REUSES pids (`kernel-defects.md`, "FIXED
  UPSTREAM (ded23f2)"). So the pid is NOT the counter. It is the first candidate, going cyclically from the
  counter, that no proc slot holds.
  - So R2(b) alone does not pin it, and R2(c) first-ness is not trivial.
  - But R2(c) is cheap (F2): the whole of allocpid runs under `pid_lock` and reads only cells that the
    payload owns.
- **The channel.** fork's pid is `pidPick PIDMAX h`, where `h` is the pid-ledger prefix just before the
  round's `PAlloc`:
  - `pidPick` is the first `c` in `nextOf h, next(nextOf h), …` (wrapping `PIDMAX → 1`) with `c ∉ liveOf h`;
  - so it is a function of the history: its counter and its live set.
- **The ghost.**
  - One pure conjunct, `pidTie np pids h`, inside `pidLedger`, which gains the payload's `np` and `pids` as
    parameters.
  - No camera, no new name, no new append, no new permit step.
  - The boot is `nextOf [] = 1` with every cell 0. The two existing appends re-establish the tie by
    construction.
- **The loop.** `ap_pidloop` gains one ghost index: the candidate is the `k`-th cyclic successor of the
  counter, and every earlier one was held by some slot.
- **The receipt.** `allocprocPostLed`'s found arm carries `pidAllocRcpt act pid := ∃ h, pidReceipt h (.PAlloc
  act pid) ∗ ⌜pid.toNat = pidPick PIDMAX h⌝`.
- **The row: none in G2 (F4).** Before M2-X, a pure `∃ h, r = pidPick h` row is EQUIVALENT to the landed range
  row, because `pidPick` is onto `[1, PIDMAX]`. Fork is re-admitted by the joint lane after M2-X.

**Findings.**
- **F1 (the kernel wraps and reuses; the counter's range).** The compiled allocpid is inlined in allocproc
  (`ProofAllocproc`, `0x80001bb6…0x80001c06`):
  - `lw a3, nextpid`, then the loop. At the head (`+0x62`): `a1 := 1`; `beq a3, a6(=1000)`; else `addiw
    a1, a3, 1`.
  - The 64-word scan of `proc[i].pid` (`+0x74…+0x7e`, `ap_pidscan`): on a match, `mv a3, a1` and retry; on
    fall-through (`+0x82`), `sw a1 → nextpid` and then `c.sw a3 → p->pid`.
  - **The counter is stored ONCE, after the loop**, at `apNewPid pid` (`= if pid = 1000 then 1 else pid + 1`).
    The retries' intermediate counter values live only in `a1`.
  - So after a `PAlloc _ pid` the cell is exactly `nextStep PIDMAX _ (.PAlloc _ pid)`. The landed `PidEv.nextOf`
    already models the wrap, so nothing in `nextOf` changes.
  - **Range.** The payload says `1 ≤ np ≤ PIDMAX` (`PIDMAX = genPidMax = 1000`, `ProcGeom`, `SlotGen` by
    `rfl`). At the bound the candidate is 1000 and the counter wraps to 1. Every candidate is in
    `[1, 1000]`, and neither 0 nor 1001 is ever reached.
  - **Termination** (`|live| ≤ NPROC = 64 < 1000`) is not proved and is not needed. `ap_pidloop` is a Löb
    partial-correctness loop, and the tie speaks only about the exit.
  - **Rocq's estimate does not apply.** Rocq said "the merge point knows only the interval", and so priced
    R2(b) as a loop change. Lean's loop already carries `R' 11 = signExtend (apNewPid pid)` to the exit
    (`apExitCont`), so R2(b) costs nothing in the loop, only the payload's close.
- **F2 (one snapshot, no window; unlike G1 F1/F2).** `pid_lock` is held from the counter read (`+0x48`)
  through the scan, both stores, the register insert and the `PAlloc` append, up to the `release` (`+0x94`).
  - A pid cell is written only as a whole word (`ap_pid_joinA`: the private half, the payload's `pidLockQ`
    quarter and `p->lock`'s quarter).
  - So no cell moves while the scan holds the payload's quarters. Every verdict of the scan is a reading of
    the ONE function `pids` that the payload binds.
  - The tie turns that snapshot into the history. No per-visit lb, no invariant-held ledger, no
    `SFull`-style event.
- **F3 (the tie is to the cells, not to the register).**
  - `pidRegDom` gives one direction only: registered → held by some slot.
  - First-ness needs the converse: a candidate that some slot holds is live in `h`.
  - So the new tie is stated against the cells: `∀ z, liveOf h z ↔ pidCells pids z`.
  - It holds by construction at the three payload builders, and there are no others (`PidLock`'s body is
    unfolded only in `MainKvm.mn_pidRes_boot`, `ProofAllocproc.ap_found` and `ProofFreeproc.fp_pidRes_acc`):
    - boot: every cell 0 and `h = []`;
    - alloc: the store fills a cell that held 0 (`hpidsn0`), beside `PAlloc pid`;
    - free: it clears slot `j`'s cell, the only cell holding `pid` (`pidsOk`), beside `PFree pid`.
  - `liveOf h = dom R` (R2(a)) stays as it is.
- **F4 (a pure row is vacuous before M2-X; sharper than G1 F6).** `pidPick PIDMAX` is onto `[1, PIDMAX]`:
  `[] ↦ 1`, and `[PAlloc a (p-1), PFree a (p-1)] ↦ p`.
  - So `∃ hp, r = sext (pidPick PIDMAX hp)` holds exactly when the landed `1 ≤ r ≤ PIDMAX` does.
  - A `SyscRows.fork` or `usysDet` strengthening through an unanchored `∃` adds nothing.
  - The content of G2 is in the RECEIPT: an lb of THE ledger with the `pidPick` fact at its prefix. It reaches a
    row only when M2-X carries the lb to the filing, where all cited prefixes form one chain.
  - Uptime's row (W3) is equally shape-only, but there the shape is the whole claim (O5). Here the claim is
    the dependence on `h`, and the `∃` erases it.
- **F5 (the parent's key also moves by a fresh ghost name).**
  - The parent resumes with `ch ∪ {γc}` (`uforkAns` / `uexecForkParentF`; `kforkRet`'s success arm,
    `γc ∉ csP`).
  - `γc` is `V_c.gen`, minted by `gen_alloc` inside allocproc. It is a function of no prefix. It is the
    `g` of the `ZFork pa i pid g` that `kf_wait_fork` appends (G1b), with the same name (`kf_wait_fork …
    V_c.gen …`, `chFrag … (cs ∪ {g})`).
  - So whatever the joint lane's row is, it reads `γc` off the round's `ZFork` receipt (which kfork drops
    today), or concludes `ukeyEq` up to `ch` at fork.
  - The trace never sees it (W4's law reads registers only).
  - Both receipts are persistent, so G2b carries both.
- **F6 (what the channel concedes).** `pidPick` reads the GLOBAL counter. A process's fork answer reveals:
  - how many allocations every actor made since the counter was last seen (mod `PIDMAX`);
  - which pids are live just past the counter.
  This is §3's "pid allocation: `nextpid` is global". R1 conceded pids as public. It is inherent to xv6:
  removing it means per-process pid namespaces, a kernel change. After M2-X, the two-run hypothesis for fork
  is "equal pid-ledger histories", which says exactly this.

**1. The vocabulary (pure; `Xv6/PidEv.lean` grows, no new file).**

    /-- the live set as a Bool reading (the decidable twin of `liveOf`) -/
    def liveStepB (S : Nat → Bool) : Pev → Nat → Bool
      | .PAlloc _ p => fun z => z == p.toNat || S z
      | .PFree _ p  => fun z => S z && z != p.toNat
    def liveB (h : List Pev) : Nat → Bool := h.foldl liveStepB (fun _ => false)
    /-- the i-th candidate from n, cyclically in [1, pidmax] -/
    def cycAt (pidmax n i : Nat) : Nat := (n - 1 + i) % pidmax + 1
    /-- THE PID A FORK GETS after history h: the first cyclic candidate from the counter that is not live -/
    def pidPick (pidmax : Nat) (h : List Pev) : Nat :=
      match (List.range pidmax).find? (fun i => !liveB h (cycAt pidmax (nextOf pidmax h) i)) with
      | some i => cycAt pidmax (nextOf pidmax h) i
      | none   => nextOf pidmax h          -- unreachable while |live| < pidmax

- `liveB_iff : liveB h z = true ↔ liveOf h (z : Int)`.
- `cycAt_zero` (at `1 ≤ n ≤ pidmax`): the 0-th candidate is `n`.
- `cycAt_succ` (at `2 ≤ pidmax`): `cycAt n (i+1) = if cycAt n i = pidmax then 1 else cycAt n i + 1`, which is
  `nextStep`'s arm. Proved in the scratch with `Nat.add_mod_eq_ite`.
- `cycAt_period`: `cycAt n (i + pidmax) = cycAt n i`.
- **`pidPick_spec`**: if `∀ i < k, liveOf h (cycAt … i)` and `¬ liveOf h (cycAt … k)`, then `pidPick
  pidmax h = cycAt … k`.
  - `k < pidmax` follows from `cycAt_period` and leastness. No pigeonhole is needed.
- `pidPick_surj` (F4's witness; for the record and the M2-X lane).
- `nextOf_snoc_alloc` / `nextOf_snoc_free`.
- `nextOf_bound`, re-landed only if a reader appears (the dead-code pass baa85f62c deleted it).

`PidLock.lean` (Iris; beside the landed ledger):

    def pidCells (pids : Nat → BitVec 32) (z : Nat) : Prop := z ≠ 0 ∧ ∃ j, j < NPROC ∧ (pids j).toNat = z
    /-- R2(b)+(c): the counter IS the history's, and the cells' live set IS the history's -/
    def pidTie (np : BitVec 32) (pids : Nat → BitVec 32) (h : List Pev) : Prop :=
      np.toNat = nextOf PIDMAX h ∧ ∀ z : Nat, liveOf h (z : Int) ↔ pidCells pids z
    def pidLedger (np : BitVec 32) (pids : Nat → BitVec 32) (R : IntMapF GName) : IProp GF :=
      ∃ h, pidLedAuth h ∗ ⌜liveOf h = PartialMap.dom R ∧ pidTie np pids h⌝
    /-- THE ALLOCATION RECEIPT: the PAlloc's prefix, and the pid it was bound to give -/
    def pidAllocRcpt (act : BitVec 64) (pid : BitVec 32) : IProp GF :=
      ∃ h, pidReceipt h (.PAlloc act pid) ∗ ⌜pid.toNat = pidPick PIDMAX h⌝
    def pidNext (c : BitVec 32) : BitVec 32 := if c = 1000#32 then 1#32 else c + 1#32  -- ProofAllocproc.apNewPid, moved

**2. The ghost and the three steps.**
- **The payload.**
  - `pidLockResAt`'s body changes in one place: `pidLedger R` becomes `pidLedger np pids R`, where `np` and
    `pids` are the body's outer binders.
  - `pidLockResAt`'s and `pidLockPay`'s statements are byte-identical, and so is every `isLock … "nextpid"
    pidLockPay` namer (20 files).
  - The `CtxMorph` instance needs nothing: the conjunct is context-free.
- **The steps.**
  - `pidLedger_empty : pidLedAuth [] ⊢ pidLedger 1#32 (fun _ => 0#32) ∅`.
  - `pidLedger_alloc` takes:
    - `n < NPROC` and `pids n = 0`;
    - `1 ≤ pid ≤ PIDMAX`;
    - `∀ j < NPROC, pids j ≠ pid` (the scan's fall-through, which the landed loop already gives);
    - first-ness `∃ k, pid.toNat = cycAt PIDMAX np.toNat k ∧ ∀ i < k, pidCells pids (cycAt PIDMAX
      np.toNat i)`.

    It gives `|==> pidLedger (pidNext pid) (apPidsSet pids n pid) (insert R pid g) ∗ pidAllocRcpt act pid`.
    - The `pidPick` fact is `pidPick_spec` through the tie at the OPENED `h`.
    - The re-closed tie is `nextOf_snoc_alloc` + `(pidNext pid).toNat = nextStep …`, and `liveOf_snoc_alloc`
      against the filled cell.
  - `pidLedger_free` takes `j < NPROC`, `pids j = pid`, `pidsOk pids` and `pid ≠ 0`. It gives
    `pidLedger np (pidsClear pids j) (delete R pid) ∗ ∃ h, pidReceipt h (.PFree act pid)`. The counter is
    untouched (`nextOf_snoc_free`).
- **The loop (`ProofAllocproc`; internal statements).**
  - `ap_pidloop` gains a ghost start `n0 : BitVec 32`. Its ∀-binders gain `k : Nat` with `cand.toNat = cycAt
    PIDMAX n0.toNat k ∧ ∀ i < k, pidCells pids (cycAt PIDMAX n0.toNat i)`.
  - The retry arm already has `pids m' = cand` (`ap_pidscan`'s match). `cand ≥ 1` makes it a `pidCells`
    witness, and `cycAt_succ` + `(apNewPid cand).toNat = …` give `k + 1`.
  - The entry is `k = 0` (`cycAt_zero` at the payload's bound).
  - `apExitCont` gains the first-ness conjunct. `ap_pidscan` is unchanged.
- **`ap_found`.** The payload open restates the body text (the `icases (show pidLockPay … ⊢ …)` at the pid
  section), so that text moves. The close calls the new `pidLedger_alloc` with the exit's first-ness.
  `ap_pid_mint`, `ap_tok_read` and the boot-era marks are untouched.
- **The receipt in the Spec.**
  - `SpecAllocproc.allocprocPostLed`'s found arm changes `(∃ h, pidReceipt h (.PAlloc act pid))` to
    `pidAllocRcpt act pid`. This is the LED TWIN's text; nobody consumes it yet.
  - `apPostCells` likewise.
  - `allocprocPostLed_post`, `allocprocPost` and `wp_allocproc_body` are byte-identical.
- **The other builders.** `MainKvm.mn_pidRes_boot` (proof only) and `ProofFreeproc.fp_pidRes_acc` (proof only;
  `pidsOk` is already in hand at the close).
  - `childrenBootRows`, `mn_pidWait_born` and `xv6GF` are untouched.
  - No camera changes, so no ~1000-file camera rebuild. But `PidLock` is widely imported.

**3. The receipt to the kernel's row (G2b: the led-twin route, as W3/G1 did for uptime and wait).**
- **`SpecKfork`.**
  - `kforkRetLed γ j pid V M stsP Q csP Rc rv` is `kforkRet`'s copy whose success arm adds, at the SAME `γc`
    (F5):
    - `pidAllocRcpt (procAddr j) rv`;
    - `∃ hz i, zombReceipt hz (.ZFork (procAddr j) i rv γc)`.
  - Also: `kforkRetLed_ret` (the drop), `kforkPostLed`, `wp_kfork_led_eb_body`, and the field
    `KFORK.wp_kfork_led_eb`.
  - The landed `wp_kfork_eb` becomes its corollary, as allocproc's did.
- **`ProofKfork`.**
  - `kfork_proof` switches to `AL.wp_allocproc_led` and destructs the found arm's receipt as `#Hrcpt`.
  - Persistent receipts ride the intuitionistic context to the success epilogue (`kf_epilogue'` at
    `kforkRetLed`), and so does `kf_wait_fork`'s receipt (dropped today).
  - The −1 arms (uvmcopy failure → freeproc) drop them. The actor is `procAddr j` (`hproc`).
- **`SpecSysFork` / `ProofSysFork`.** `wp_sys_fork_led_eb_body` and the field `SYSFORK.wp_sys_fork_led_eb`, a
  forwarder. `LinkKfork` / `LinkSysFork` build the structures with the new field.
- **`SyscallArmsFork` does not switch in G2** (F4: there is nothing pure for it to record).
  - The arm switch, and the receipt's route past the arm (W2d's: syscall arm → usertrap → userret →
    filing), are M2-X's.
  - `SyscRows.fork`, `usysMemOk`'s fork branch, `UsertrapSysRows`, `uexecForkParentF` and `uforkAns`:
    byte-identical.

**4. The row (deferred to the joint lane G1f+G2+G3, after M2-X).** For the record, the partial row G2 alone
supports:
- the pid reading `usysForkPid ι := signExtend 64 (BitVec.ofNat 32 (pidPick PIDMAX ι.pev))`, with `ι.pev` the
  prefix BEFORE the round's `PAlloc` (the receipt's `h`);
- **`r = -1 ∨ r = usysForkPid ι`** — the pid is pinned whenever fork succeeds;
- on success, the parent's key is `bump W r W.M W.perm W.sz W.fd W.cwd W.gen (W.ch ∪ {γ}) W.lazy W.secc`, with
  `γ` the round's `ZFork` generation (F5). On −1 it is `bump W (-1) …` with `W.ch` kept.
- The child's key is unchanged: it is already functional (`bump W 0 …` at the child's first key), and its pid
  is the same `pidPick` (a first-key datum, `q.2`).

**Not admitted now; no `usysDetPartial`.** Three reasons:
- (i) F4: before M2-X the row is equivalent to the landed one.
- (ii) The success bit is unexplained. It depends on slot exhaustion (G1f's `SFull`, an invariant-held
  ledger) and on allocproc's and uvmcopy's kallocs (G3).
- (iii) `γ` needs the `ZFork` receipt in ι, which is M2-X's route too.

**The joint lane re-admits fork as follows.**
- `usysDet USYS_fork W ι := if forkOk ι then <success key> else <−1 key>`, where `forkOk ι := ¬ SFull at the
  round ∧ no KNull at the round's allocator positions` (as G3 states them).
- `usysDetClassAt` (G1d's shape, `n a0`) gains fork under G3's key conditions (uvmcopy's count depends on the
  page table's interior, UsysDet §4).
- `round_det`'s `_exists` supplies `ι.pev` and `ι.zev` from the exported lbs.

**5. W4's law.**
- **Now: nothing.** `events`, `NiStep.reads`, `NiInClass` and `niRoundLaw` are unchanged by G2.
- **Cheap, but NOT recommended now: fork's answer as a reading.** `NiStep.reads` would admit `gprsNum = USYS_fork`
  and the resume clause would cover it (pc + 4, `x1..x31` kept but `a0`). The conjunct `a0 = −1 ∨ 1 ≤ sint a0 ≤
  PIDMAX` is already derivable from `niFit` (`roundOkKeys` → `uroundOk` → `usysMemOk`'s fork branch, `M' =
  M`), with no kernel work.
  - But the reading would carry BOTH the success bit and the pid.
  - The pid part is explained in-logic only after M2-X; the bit not at all until G1f+G3.
  - So the bit would be §2's rejected "oracle of outcomes". wait's reading (G1-R5) and uptime's (O5) each have
    an in-logic receipt behind the whole answer; fork's would not.
- **After M2-X and the joint lane.**
  - `niRoundLaw`'s fork conjunct becomes `a0 = sext (pidPick PIDMAX hc)` on success, where `hc` is the filing's
    cited pid-ledger prefix. Prefixes are chain-comparable (M2-X), so there is ONE pid history per run.
  - The pid part then leaves `events`. The two-run hypothesis "equal pid-ledger histories" replaces "equal fork
    readings".
  - The success bit becomes a function of the cited slot/allocator prefixes.
- **Honesty cost** (for the as-landed note, F6): fork declassifies the global allocation count since the
  caller last looked (mod `PIDMAX`) and the live pids just past the counter. The in-logic row says it is
  EXACTLY that (`pidPick` of a prefix of the one pid ledger) and nothing else: not slot placement (that is
  `ZFork`'s, G1), and not the scheduler's interleaving beyond the order of `PAlloc`/`PFree` events.

**6. Lanes** (on `lane/g2`, rebased onto G1d when it lands; one `lake` at a time).
- Gate per lane: `lake build Xv6 MachCSL` + `tools/ci/lint.sh` + no `sorry`.
- Full `tools/ci/run_all.sh` at G2a: `PidLock` is imported by ~20 namers and their cones.
- `tools/ci/dead_allow.txt` rows for anything unreached.

| Lane | Content | Files | Moves | Gate |
|---|---|---|---|---|
| **G2a the tie, first-ness, the receipt** | §1 (pure) + §2: `pidCells`, `pidTie`, `pidLedger np pids R`, `pidAllocRcpt`, `pidNext`, the three steps; `ap_pidloop`'s index; the open/close in `ap_found`; `allocprocPostLed`'s receipt | `PidEv`, `PidLock`, `ProofAllocproc`, `SpecAllocproc`, `ProofFreeproc`, `MainKvm` | `pidLockResAt` body; `pidLedger` (+`np pids`) and `pidLedger_empty/alloc/free`; `allocprocPostLed` (led twin text); `apPostCells`, `ap_pidloop`, `apExitCont` (internal); `apNewPid` → `PidLock.pidNext`. Byte-identical: `pidLockPay` and its namers, `allocprocPost`, `wp_allocproc_body`, `wp_freeproc(_led)_body`, every kfork/userinit statement | full; `pidPick_surj` unreached (dead_allow, or keep it out of the tree and cite the scratch) |
| **G2b the led kfork** | §3: `kforkRetLed` (+ both receipts), `kforkPostLed`, `KFORK.wp_kfork_led_eb`, `SYSFORK.wp_sys_fork_led_eb`; `kfork_proof` on the led allocproc; the landed fields as corollaries | `SpecKfork`, `ProofKfork`, `SpecSysFork`, `ProofSysFork`, `LinkKfork`, `LinkSysFork` | `KFORK`, `SYSFORK` (+ one field each); no landed body text | build + lint; the two led fields are unreached until M2-X switches the arm (dead_allow rows, or land G2b inside M2-X) |
| **G2c = the joint lane** | §4's row with `forkOk`, `usysDetClassAt` fork, `SyscRows.fork` strengthened, `round_det`, W4's fork conjunct | (G1f + G3 + M2-X files) | — | after M2-X |

G2a stands alone. G2b depends on G2a and is independent of G1d: G1d touches `SyscallArmsFork` only for the
`SyscRows.wait` builder, and G2b does not touch it. Estimate: G2a is 6 files, with the loop index the only
proof content (~100 lines in `ap_pidloop`, ~60 in the steps). G2b is 6 files, mechanical but long
(the success path runs from `kfork_proof`'s allocproc call through `kf_publish`, ~860 lines, to
`kf_epilogue'`; the persistent receipts are framed through it).

**Owner rulings requested.**
- **G2-R1 (the counter at `PIDMAX`).** xv6 (ded23f2) wraps and reuses, so the tie uses `nextOf`'s landed wrap
  (`pid = PIDMAX → 1`), and first-ness is the cyclic scan (`pidPick`). Recommended: state BOTH R2(b) and R2(c).
  - In Rocq, R2(c) was "heavy". In Lean it is one ghost index in `ap_pidloop`: the loop already carries the
    counter register and the scan's verdict, and one snapshot decides everything (F2).
  - Termination stays unproved: it is not needed.
- **G2-R2 (the tie against the cells).** Recommended: the new `pidCells` equivalence beside the landed register
  tie (F3). The alternative is to strengthen `SlotGen.pidRegDom` to an iff, which moves `pidRegDom_*` and
  `ap_pid_mint`'s freshness path for the same content.
- **G2-R3 (led twins vs a Spec move for kfork).** Recommended: led twins (`kforkRetLed`, `KFORK.wp_kfork_led_eb`,
  `SYSFORK.wp_sys_fork_led_eb`), carrying both persistent receipts (`PAlloc`'s with `pidPick`, and `ZFork`'s with
  `γc`, F5). Timing: land G2b with M2-X, which is the first reader. The alternative is now, with dead_allow rows.
- **G2-R4 (no partial row, no `SyscRows.fork` move before M2-X).** Recommended, because of F4. The alternative,
  `SyscRows.fork : … ∨ ∃ hp, syscA0 V' = sext (pidPick PIDMAX hp)` now, is a Spec move with provably no content
  (`pidPick_surj`). `usysDetClassAt` does not admit fork until the joint lane.
- **G2-R5 (W4).** Recommended: fork's answer stays out of `events` until the joint lane. After it, the pid part
  comes from the cited prefix and the success bit from the slot/allocator prefixes, with F6's honesty paragraph
  in the as-landed note. The alternative, fork's whole answer as a reading now (cheap, §5), is not recommended:
  it would declassify an unexplained success bit.

## Lanes (opened 2026-09-15)

Execution order is §6's, adjusted for one territory fact: upstream's
post-Qed redesign (app-echo, POST-QED R1) is actively re-cutting the
claim files around the engine, so M0's re-cut of `uexec_ret_F` WAITS for
that to settle (or goes to upstream with it — relay if they want it);
M1's ledgers are fresh ground and go first.

- [x] **NI-LEDGER-KALLOC** (M1's first ledger; kernel) — LANDED 2026-09-28
  (b5e67a96b, bed7ee0dd; as-landed record in
  [`design/ni-kalloc-ledger.md`](../design/ni-kalloc-ledger.md) §7: the
  ledger inside `kmem_avail_auth`, no landed contract moved, led-form
  contracts beside the landed ones, no consumer yet).  Original brief:
  the allocator's ghost ledger on the FREE POOL pattern
  (`bitmap_inv`, per §2/§7): an abstract free set in the allocator's
  invariant; `kalloc` fails iff it is empty; each `kalloc`/`kfree`
  appends an actor-labelled `Alloc`/`Free` event.  Deliverables: the
  event vocabulary + ledger file; `SpecKalloc`'s rows deterministic in
  the ledger; callers served by the invariant (not per-caller
  fragments).  Rulings R1-R5 taken as recommended (owner, 2026-09-28).
- [x] **NI-LEDGER-REST** (M1 remainder, COMPLETE 2026-09-29): `nextpid` — coordinate with
  the landed TRAP-ROWS `upid`/`ukn_pid` work, the U tier already sees
  pid numbers — then `ticks`, the zombie set; then the per-process key
  history `uhist : mono_list uvis` beside `proc_priv`.  PID LEDGER
  DESIGN PASS 2026-09-28: [`design/ni-pid-ledger.md`](../design/ni-pid-ledger.md)
  (events `PAlloc act pid | PFree act pid` inside `<pid_lock>`'s payload,
  tied to the pid register's domain, the name a `wchG` field, receipts
  on allocproc/freeproc led twins).  PID LEDGER LANDED 2026-09-28
  (d66e99d0d, f43d32a72; as-landed record in the design note §5; no consumer
  yet).  TICKS DESIGN PASS 2026-09-28:
  [`design/ni-ticks-ledger.md`](../design/ni-ticks-ledger.md) — a
  monotone counter at a `wchG` name mirroring the cell inside
  `<tickslock>`'s payload, uptime's led twin returns the count; ONE
  landed statement moves by a binder (`wp_sys_uptime_sconf_body` gains
  `!wchG Σ`, ruling R1).  TICKS LANDED 2026-09-28 (dd1843b7a; as-landed
  record in the design note §5).  ZOMBIE DESIGN PASS 2026-09-28:
  [`design/ni-zombie-ledger.md`](../design/ni-zombie-ledger.md) — exits
  (with the status) and reaps under `<wait_lock>`'s payload at a `wchG`
  name, kwait's led twin; NO tie, since nothing under the wait lock
  knows the zombie slots (D3).  ZOMBIE LANDED 2026-09-28 (2107981b4;
  as-landed record in the design note §5).  M1'S FOUR LEDGERS ARE IN
  (allocator, pid, ticks, zombie), all as receipts beside the landed
  contracts with no consumer yet; what remains of M1 is the per-process
  key history `uhist : mono_list uvis` beside `proc_priv`, and the
  first consumers (the dispatcher's rows reading the receipts), which
  is M0's territory.  UHIST DESIGN PASS 2026-09-28:
  [`design/ni-uhist.md`](../design/ni-uhist.md) — a ghost list of rounds
  `(sc, W, W')` in the residue beside the block, named by `ut_names`,
  appended once per round by the trap loop with the round relation as
  its invariant.  UHIST LANDED 2026-09-29 (5634a3874; as-landed record in
  the design note §5 — the camera is an ENCODED ledger over `positive`,
  a gname-free `xv6G` member, because the key record sits above the
  camera file).  **M1 IS COMPLETE**: the four ledgers and the
  per-process history, all as receipts/invariants beside landed
  contracts, no consumer yet.  NEXT, in order of value: (1) the first
  consumers — the dispatcher's rows reading the receipts (`usys_det`,
  M0), which waits on upstream's post-Qed re-cut of the claim files;
  (2) the permit sweep for the strong instance
  (`design/ni-strong-instance.md` §3, 69+7 contracts), now sizeable
  against the full vocabulary; (3) M2's export.
- [ ] **NI-STRONG-INSTANCE** (§3.1): a process before its first syscall
  appends no events.  PERMIT SWEEP OPENED 2026-09-29 (owner's word;
  plan in `design/ni-strong-instance.md` §7: an exclusive per-slot
  counter `act_cnt`, `pv_ev` in the record, top-down layers G, L1-L6,
  T).  G LANDED 2026-09-29 (9fb1d089c; §7.1).  L1a LANDED 2026-09-29
  (f344a089a; §7.2: the counter in the bare block travels with the fs/syscall
  contracts for free, so the sweep is ~22 block-less contracts in three
  rings; ring one and the block-holders' posts above it are in).  L1b
  LANDED 2026-09-29 (b69bd0fab; §7.3: the copy ring and the whole file layer
  above it, 84 files).  L2 LANDED 2026-09-29 (78f9234b8; §7.4).  Next: L3
  the allocator and the appends, then T.  DESIGN PASS 2026-09-28,
  [`design/ni-strong-instance.md`](../design/ni-strong-instance.md): NOT
  a free consequence of the ledger — absence is ownership, and kalloc's
  premises do not distinguish a quiet round from a syscall, so the
  in-logic form needs an exclusive per-process permit threaded through
  the allocating cone, which is the whole syscall/fs layer (69 contracts:
  vmfault sits under copyin/copyout/copyinstr).  Recommendation D: defer
  the permit sweep until NI-LEDGER-REST so it is paid once for all
  ledgers; land now the pure `vmfault_quiet` (lazy flag off ⇒ vmfault's
  kalloc arm is unreachable) and a functor-inventory check.  RULED D
  (owner, 2026-09-28); `vmfault_quiet` LANDED (`iris/VmfaultQuiet.v`)
  and the inventory check LANDED (`tools/intr_cone.py`, `make
  intr-cone-check`: the interrupt arm's 24-instance cone implements no
  KALLOC/KFREE); the permit sweep waits for NI-LEDGER-REST.
- [ ] **NI-DET-ROWS** (M0): `usys_det` and the ecall arm's re-cut, the
  loop's `round_det` discharge — after the post-Qed redesign settles;
  §4 lists the row set to start from.
- [x] **NI-TRACE** (M2) LANDED 2026-10-02 in the Lean tree at the honest class (see "M2 as designed for the Lean tree" and the W1–W4 as-landed notes; follow-ups G1–G4 grow the class).  - [ ] **NI-EXT** (M3): unchanged from §6.

Related design of record: [`design/user-wp-slot.md`](../design/user-wp-slot.md)
(the trap contract this would re-shape), [`design/uk-engine.md`](../design/uk-engine.md)
and [`design/user-heap.md`](../design/user-heap.md) (the U tiers whose
determinism is half of any proof), [`design/adequacy.md`](../design/adequacy.md)
(`Hphi`, and its item (d) — "hyperproperties are out of
`wp_strong_adequacy`'s reach" — which §4 says how to sidestep),
[`uart-trace.md`](../completed/uart-trace.md) (the trace-export pattern §6 reuses),
[`design/fs-bitmap.md`](../design/fs-bitmap.md) (the FREE POOL: the in-tree
precedent for §3's ledger).

## 0. The position, in one paragraph

State NI as **refinement of each process's trap-boundary trace to a
deterministic ABSTRACT PROCESS MACHINE whose only inputs are the process's
own initial state and a PUBLIC, ACTOR-LABELLED EVENT HISTORY** (allocations
and frees, forks, fs writes, ticks, the order of rounds), and prove it
UNARILY in the existing CSL from three ingredients the tree already has in
embryo: (a) FUNCTIONAL rather than relational rows in
`UexecRet.uexec_ret_F`'s ecall arm — the kernel's round on a process's trap
is a function of the trapped key and the event-history prefix; (b) ghost
LEDGERS that make every shared kernel resource's spec deterministic
relative to the events that moved it (kalloc first); (c) OWNERSHIP for "no
other thread changes this process's view" — the frame rule, not a lemma
about other processes' code.  The two-run statement is then a PURE
corollary outside Iris because the abstract machine is a function, and
SECRECY of a process A reduces to the question "which events does A
generate?" — whose answer for xv6 is §3.  No relational logic (SeLoC-style
double WP), no product program, no leaf lemma re-proved; §5 says exactly
what a double WP would have bought and why it is not needed here.

## 1. The observation function already exists: `uvis`

`UexecSlot.uvis = (tf, M, π, sz, fdv, cwd)` — the trapframe words, the lazy
va-keyed image, the per-page X/W map, the break, the descriptor view, the
cwd inum.  Every ruling that shaped it was an OBSERVABILITY ruling made for
abstraction reasons: "a process observes its registers and its va-keyed
bytes, never PPNs" (why the table is not in the key); "the process cannot
observe lazy allocation" (why the image is the lazy view and the page-fault
arm is transparent); "an interrupt cannot retype a descriptor" (why `ukb_F`
pins `fdv` across the transparent arm).  Those are exactly the decisions an
NI proof must make about what a subject can see, and they were made before
anyone asked about NI.  The observation of process P at any point is P's
key.  Nothing has to be invented here.

Partitions are processes (later, process families: a parent and its
children, which share pipes and `wait`).  Low = the process under study;
high = everything else — other processes' images and registers, other
files' contents on disk, the physical placement of the low process's own
pages, the buffer cache, the proc table, the free lists.  Kernel state the
process cannot observe is high BY DEFAULT, and the proof never has to say
what happens to it.

## 2. The formulation that was proposed and corrected

**First proposal (rejected in review).**  Declassify xv6's channels as an
ORACLE of OUTCOMES read off the low process's own trace: the pid `fork`
returns, a "sbrk failed" bit, the `uptime` value, a "killed" bit.  Then
"P's trace = F(P's key, oracle)" is unary and the two-run corollary is
free.

**The owner's objection, which is right.**  Declassifying B's OUTCOME
("sbrk failed") is useless for secrecy: the theorem then says nothing about
whether the failure correlates with A's data.  Put sharply — suppose the
secret process A makes no syscalls at all, and the adversary B calls
`sbrk`; `kalloc` fails "nondeterministically" per its spec; how could one
argue B learns nothing about A, when the spec does not say where the
nondeterminism comes from?  Read that way the first proposal only proves
"an adversary that makes no syscalls learns nothing", which is unrealistic,
and it makes the INTEGRITY direction clear (nobody writes P's view except
through P's own rows) while leaving SECRECY, the interesting direction,
unaddressed.

**The correction: the oracle is the EVENT HISTORY, not the outcomes.**  The
nondeterminism must be moved from the outcome to its SOURCE.  The kalloc
spec's nondeterministic failure is the spec's abstraction, not the
kernel's behaviour: `kalloc` fails iff the free list is empty.  Give the
allocator a ghost LEDGER — an abstract free count, or the free set, in its
invariant — and every allocation outcome is a function of the ledger, which
is a function of the sequence of allocation and free EVENTS so far, each
labelled by the actor (which process's round, or which kernel path,
produced it).  Do the same for `nextpid`, `ticks`, the zombie set and the
fs abstract state.  The oracle ι is then the public, actor-labelled event
history and never any process's data, and "P's trace = F(P's key, ι)"
really says P learns nothing but the events.  The two-run corollary is
unchanged in form, but its hypothesis "equal ι" is now a statement about
what the OTHER processes did, not about what P happened to observe.

The ledger is the device that PINS DOWN THE KERNEL'S CAUSALITY: the finite
list of event kinds is the complete answer to "through what can one
process's execution affect another's", and a syscall row that cannot be
made functional in (own key, ι-prefix) is a channel that has not been named
yet.  `bitmap_inv`'s FREE POOL is the in-tree precedent: `balloc`'s failure
is already a deterministic function of a ghost pool; the kalloc ledger is
the same shape one layer down.

## 3. What xv6 actually leaks: the lazy-allocation channel

With ι the event history, secrecy of A becomes "which events does A
generate?", and xv6's answer is uncomfortable but true.

- **A SYSCALL-FREE process still generates kernel events.**  Touching a
  lazily-allocated page runs `vmfault` → `kalloc`, which moves the ledger,
  which B observes at the memory limit through `sbrk`'s failure.  That is
  a real STORAGE channel of xv6 — a syscall-free A can encode a bit by
  touching or not touching a page — not an artefact of any proof method,
  and no relational logic makes it go away.  seL4, CertiKOS and Nickel all
  hit exactly this and all CHANGED THE ALLOCATOR (static partitioning of
  untyped memory; per-process quotas; Nistar's containers).  xv6 has no
  quotas of any kind.
- **Which pages are lazy.**  exec maps the ELF segments and the stack
  eagerly (`uvmalloc`, `flags2perm`); only `sbrk`-grown pages are lazy
  (`vmfault` maps a first-touched page `R|W|U`; `perm_of`'s fill is exactly
  those).  So a process that has NEVER CALLED `sbrk` has no lazy pages, and
  its user steps generate no events at all: no page faults, no
  allocations, and its interrupt rounds are the transparent arm, which
  runs `yield`/`scheduler` and touches no ledger.
- **The other channels**, for the record: pid allocation (`nextpid` is
  global; `fork`'s return, `getpid`, `wait`'s pid); proc-slot exhaustion
  (`fork` returns −1); `uptime` (`ticks`); the order in which children
  exit, seen through `wait`, and how many bytes a pipe holds; console input
  (already `ObsUartIn` in the trace); `kkill(pid)`, which scans all 64
  procs with NO permission check — any process may kill any pid — an
  authorized cross-partition flow by xv6's design that breaks both
  directions of NI unless the high side is assumed not to call it, or the
  kill is an event.  NOT channels: U-mode `rdtime`/`rdcycle`/`rdinstret`
  trap, because xv6 never writes `scounteren` (grep of `kernel/` finds no
  occurrence), and `usertrap` kills the process — deterministic; and
  instruction-cache staleness, because no page a program can write is a
  page it can fetch from (`flags2perm` never yields W+X unless the ELF asks
  for it — require that it does not, a decidable fact about the image).
  `lr`/`sc` success is left free by the platform axioms; a low process
  using them would need an oracle bit per `sc`.

**The honest theorems for UNMODIFIED xv6**, in decreasing strength of what
they say about A:

1. **Strong instance.**  A process that has issued no syscalls (hence has
   no lazy pages) generates no kernel events; its data affects nothing any
   other process observes, with the ADVERSARY UNRESTRICTED — any syscalls,
   file system included.  A genuine secrecy result, and the first one to
   aim at: A = a verified or arbitrary program before its first syscall,
   B = anything.
2. **General.**  A's data influences other processes only through the
   events A generates.  The event VOCABULARY is the graded declassification
   policy: `Alloc A` concedes A's footprint COUNT, `Alloc A vpn` concedes
   more, `FsWrite A ino` concedes that A wrote a file but not what.
3. **Anything stronger for a syscalling A needs a kernel change** (memory
   and pid quotas per process, a `kill` permission check).  The framework
   would then be able to prove that the change closes the channel — the
   row for `sbrk` becomes functional in A's OWN quota ledger and the
   `Alloc` event drops out of ι.

The INTEGRITY direction is a corollary of the same theorem and is
straightforward, as the owner noted: B's key is a function of B's own key
and ι, so nothing writes B's memory or registers except through B's rows.

## 4. The unwinding conditions and their CSL homes

A classical NI proof (Rushby; seL4) discharges three unwinding conditions.
Each has a natural home here; the mapping is the argument that the
architecture fits.

- **Output consistency**: trivial, the unwinding relation IS "P's keys are
  equal".
- **Steps by others do not change P's observation.**  In seL4 and
  CertiKOS this is proven over the whole kernel — every operation of B
  preserves A's observation.  Here it is OWNERSHIP: P's image
  (`user_ptm_inv pt sz M`), trapframe words, `sz`, `fd_frags` and cwd are
  owned by P's slot while P runs and by P's residue (`UsertrapRes.ut_own`)
  while the kernel serves P; no other thread's WP ever holds them, so no
  other thread's step can be PROVEN to write them, and a ledger fragment
  for P's own history rides with them so only its holder can append.
  Nothing is proven about the high side's code, which is why the high side
  runs arbitrary code from the first milestone on.  The design constraint
  this induces: NI stays free exactly as long as every fact a process can
  observe is carried by a resource the process or its residue owns; a
  spec that let the U tier see a physical address or a shared kernel
  counter is where the argument would break.
- **The kernel round on P's trap** (step consistency for the kernel's
  part): the FUNCTIONAL ROWS.  Today `uexec_ret_F`'s ecall arm is
  `∀ r M' π' szv' fdv' cw', ⌜usys_mem_ok …⌝ -∗ … -∗ X (bump W r M' …)` — a
  RELATION between trapped and resumed key, deliberately loose ("safe at
  every `r`").  Write a pure `usys_det n W ι : uvis` and make the arm, for
  `n` in the class, `X (usys_det n W ι)` at the round's ι-prefix.  The
  direction of obligation is the one `design/user-wp-slot.md` stresses:
  the PROGRAM proves the arm and the KERNEL instantiates it, so a
  functional row is easier for the program and harder for the kernel — at
  `UexecApply.uexec_ret_round_slot` the loop must PROVE the round's actual
  `(r, M', …)` equals `usys_det`.  That is where the proof's content lives:
  `sbrk` (`r` = old `sz`, or −1 iff the ledger is empty; `M'`/`π'` already
  functional in `sz'` via `usys_sbrk_img`/`usys_sbrk_perm`, kernel source
  `SpecGrowproc.growproc_ok`); `fork` (child key `bump W 0 …`, functional
  today; parent `r` = the pid the ledger says); `wait`, `exit`, `getpid`,
  `uptime`; console `write` (`r = n` iff the buffer is readable in `π`,
  today the QUIET row — the "real loss" `uk-engine.md` records is the first
  place a functional row is missing).  The transparent arm `X W` is ALREADY
  functional, which is what makes scheduling and lazy allocation invisible
  and the property timing-insensitive.  `exec` success is a MINT from the
  new image (`UexecCond.cond_entry_slot`), the ORIGIN of a trace rather
  than a step of it.
- **User steps** (step consistency for the process's part).  For a
  VERIFIED low process, its own proof: every `UkRun*` leaf is functional
  in `(m, pc, M)`.  For ARBITRARY low code a new theorem `ustep : uvis ->
  uvis + trap` with the generic tier's landing stated as "lands at a
  realization of `ustep W`".  Foothold: `UserTotalU.v`'s execute facts
  travel with `goodmb` twins in `(Dr, Dw)` (certified register read/write
  sets) and `goodb_agree_congr` — read-frame congruence, "two states
  agreeing on the read set agree on the result" — IS the register half of
  the unwinding lemma; the memory half is `UserMemClassify` restated at the
  key, the abstraction the `uvb`-level leaves already present, which is
  what sidesteps the memory-isomorphism problem of §5.  The largest single
  item; DEFERRED by scoping the first theorem to a verified low process.
- **On linearity.**  The kernel can resume P only through a slot it got
  from P's `uexec_ret` (or a mint at userinit / fork / exec-success), so
  once the rows are functional the TYPE of the return channel is the NI
  policy — good intuition, and why M0 below has value on its own.  But the
  theorem must be about the ledger, because the generic `□ uexec_wp` is
  mintable at any key by anyone holding a `UEXEC_GEN`.

## 5. Unary versus double WP: what each buys, and why unary suffices here

The owner's question was whether secrecy fundamentally requires a
SeLoC-style double WP (Frumin–Krebbers–Birkedal 2021; ReLoC is the
refinement cousin) for the kernel, since otherwise "we don't know where the
kalloc nondeterminism comes from".  The considered answer:

- **What a relational logic buys, precisely.**  It proves "the result
  depends only on low state" WITHOUT exhibiting the function.  A unary
  logic must EXHIBIT it — a functional spec relative to an abstract state
  — and the two-run reasoning is then done once, on the pure abstract
  machine (CertiKOS's "security-preserving simulation", Costanzo–Shao–Gu
  PLDI 2016; seL4's unwinding on the abstract spec carried down by
  refinement, Murray et al. 2013).  That is the real trade-off, and it
  favours the relational route for code one never intends to specify
  functionally (a hash table inside a black box: `dwp e e {{ v1 v2, v1 = v2 }}`
  is far cheaper than saying what `e` returns).
- **Why it favours the unary route HERE.**  The tree is exhibiting the
  functions anyway: the atomic-update specs on the fs abstract state, the
  `proc_pt_any` campaign ("every contract to a PRECISE image or an
  existential written out"), `usys_fd_ok`/`usys_pipe_ok`/`usys_cwd_ok`.
  What secrecy adds is LEDGERS for the shared state still left
  nondeterministic (kalloc, `nextpid`, `ticks`, the zombie set) and ACTOR
  labels on events.  xv6's syscalls are coarse-grained atomic against that
  abstract state, so a TOTAL ORDER of events exists and each process's
  trace is a function of its key and its position in it: the kernel is
  LINEARIZABLE against a deterministic abstract machine, and NI is a
  property of that machine.  Everything nondeterministic in the semantics
  — the tick choice, hart interleaving, device steps, `lr`/`sc`, the icache
  view — ends up in ι as "the schedule", which every concurrent-NI
  formulation declassifies one way or another.
- **A double WP over `riscv_lang` would redo the ownership argument.**  For
  the strong instance (§3.1) the relational invariant is simple — the two
  runs are identical except A's pages and registers — and the proof would
  be: every kernel step either reads none of them or is A's own user step.
  But "kernel code holding no points-to for A's pages cannot be proven to
  read them" is exactly what the unary proof already relies on, and the
  functional rows are how the unary logic EXPORTS "did not read".  The
  relational version would also have to relate two PHYSICAL memories up to
  the placement of A's pages (kalloc serves the high side too, so A's ppns
  differ across runs), which the key-level statements abstract away for
  free.  And the whole tree is unary: leaves, engines, whole-function
  specs; a relational logic would re-derive rules per primitive.
- **Where the unary route IS weak**, honestly: kernel components whose
  functional spec is far off (the fs internals above all — a double WP
  could prove "the fs syscall's result depends only on the fs abstract
  state" without pinning the result); and genuinely racy user-visible
  behaviour at instruction granularity, which relational reasoning handles
  and functional specs cannot.  xv6 has neither once the schedule is in ι.
- **Possibilistic NI** ("for every run from s1 there is a run from s2 with
  equal observations") was also considered and rejected: weaker (it does
  not bound what P learns from scheduling) and harder here, since proving
  it needs step-simulation EXISTENCE, which a WP does not give.

## 6. The theorem, staged

- **M0 — contract-level determinism, no export.**  `usys_det` for the
  private class; `uexec_ret_F`'s ecall arm re-cut on it for those `n`; the
  loop's discharge at `uexec_ret_round_slot` through `UexecRound.uround_ok`.
  Deliverable: `round_det : uround_ok … -> W' = usys_det n W ι`, and
  `uexec_ret_F` readable as the policy.  TCB of the statement:
  `uexec_ret_F`'s shape and `usys_det`, measurable with `tools/tcb/`.
- **M1 — the ledgers, inside the logic.**  The kalloc ledger (free count
  or free set, with `kalloc`/`kfree` specs deterministic in it and an
  actor-labelled `Alloc`/`Free` event appended per call — the FREE POOL
  pattern), then `nextpid`, `ticks`, the zombie set; a per-process key
  history `uhist : mono_list uvis` beside `proc_priv`, appended at
  trap-out (`uvis_of_run`) and resume (`usys_det`); the invariant "every
  history is a run of the abstract machine at the event history".  The
  strong instance (§3.1) is provable at this stage as an in-logic
  statement: a process before its first syscall appends no events.
- **M2 — trace export.**  Two hardware-level observations in
  `RiscvLang.mobs`: `ObsUEnter cpu satp tf` at the sret-to-User node and
  `ObsUExit cpu satp sc tf` at the trap-from-User node (`satp` is the
  pid-free identity of the address space); `prim_step`'s hart arm emits at
  exactly those two nodes and stays silent elsewhere; the two boundary
  lemmas gain a permit in the shape of `WpUart.uart_obs_permit`; the client
  ledger `Pt` (`riscv_obs_pred`, ruling 2 of `uart-trace.md`) ties the
  events in `h` to the ghost histories and the event ledger.  Then
  `phi g h := ∀ s, utrace s h ⊑ canon (first_key s h) (events h)` and
  `xv6_ni_adequacy_xv6Σ` is `xv6_power_adequacy_xv6Σ` at that `phi`; the
  two-run corollaries (general, and the strong instance) are pure.  Events
  rather than a ghost-only history because `Hphi` concludes a `Prop` about
  `(g', h)`: a history not reflected in `h` exports only existentially, and
  an existential per run kills the two-run corollary.  The image is tied
  to the emitted registers by the permit (`user_ptm_inv`'s exactness — the
  `upt_tree_spec` "blocks direction" — proves the pure page walk of `g`
  equals `M`).  Fallback if the hart-arm cost is refused: a final-state
  statement through a pure observation on `gmem` at the proc table, which
  gives reachability but no two-run corollary.
- **M3 — extensions**, independent: arbitrary low code (`ustep`, §4);
  process FAMILIES as partitions (pipes and `wait` order become
  family-internal event positions; `UkFork`'s two-continuation leaf already
  distributes non-address-space resources); across power cycles (ledgers
  keyed by era); the no-`kill` corollary; kernel changes (quotas) and the
  theorem that they close a channel; private FILES, where "shares no
  state" stops being a syntactic class and the fs-syscall-specs lane's
  functional specs are the prerequisite.

**Suggested first instances.**  Secrecy: A = any program before its first
syscall, B = anything (§3.1).  Integrity/trace: low = `echo` (verified on
the Uk engine: `write` to the console, `exit`), high = anything `sh` runs —
trivial as a program, but it exercises the `write` row, the `exit` arm,
both boundary events and the export with a three-key `canon`.  Then a
verified program using `sbrk` and `fork`/`wait`, for the ledger positions.

## 7. Costs and risks

- **The hart arm of `prim_step` emits.**  `κ = []` is baked into the hart
  arm and asserted in the hart lifting lemmas (`RiscvExec.v`'s `assert (…
  κ = [])` sites).  Emitting only at the two privilege-changing nodes keeps
  every other hart rule's κ trivially `[]`, but each assert site is touched
  once.  The one infrastructure cost that is not a re-spelling.
- **Functional rows are STRONGER GUARDS the kernel must meet**, one per
  syscall in the class (`write`'s count, `wait`'s pid, `sbrk`'s −1 arm as
  "ledger empty").  The fs-syscall-specs lane's per-entry receipts are the
  template.
- **The ledgers change the kalloc/pid/ticks specs tree-wide**: every
  caller of `kalloc` threads a ledger fragment or the ledger lives in an
  invariant every caller opens.  The FREE POOL's `bitmap_inv` (persistent
  invariant, opened through `wp_log_write_au`-style suppliers) is the shape
  to copy.
- **The channels are REAL.**  §3's theorems are true of xv6 only modulo
  the events; that is a statement about xv6 worth a line beside
  `kernel-defects.md` as a design property, not a defect: no kill
  permission check, no memory or pid quotas, lazy allocation charged to the
  global pool.
- **Physical placement leaks exist and are invisible** (which ppns P gets
  depends on the high side); nothing at the key sees it; keep the U tier's
  vocabulary key-only (§4's design constraint).
- **Not covered**: timing (P reads time only via `uptime`, an event; but
  the interleaving of P's and a high process's console OUTPUT is
  observable from outside the machine and is not part of P's observation —
  a property of the outside observer); integrity of the KERNEL against P,
  which is the existing safety theorem.
