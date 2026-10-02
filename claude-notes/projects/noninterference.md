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

- [x] M2-W1 (ef6f784b5; the permit lives in wireInv; one Spec moved: SpecUserret.wp_userret_body gains wireInv)  - [x] M2-W2 (W2a f964ed918, W2b feefd976e, W2c a27f0567a, W2d 9576822d7 landed; W2d also moved USERVEC's post (the exit token handed back), syscForkIn, USERRET_CLOSED's and MAIN's pre, parkMode -- the claims' routes, accepted by the coordinator -- NiFitIs is an IMPLICATION niFit → uFit and the system record keeps uFit := True so NiLedger stays out of the system theorem's TCB (coordinator ruling on O2); W2d pending) (DESIGNED 2026-10-02, "M2-W2 design" below; awaiting rulings O1-O6)  - [x] M2-W3 (M0) (38c39d26f: class = {exit, getpid, uptime}; sbrk, fork, wait, write NOT functional -- see its as-landed note; owner decision pending)  - [ ] M2-W4

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

- [ ] M2-G1  - [ ] M2-G2  - [ ] M2-G3  - [ ] M2-G4

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

Each lane's as-landed line goes under its row's design note (the Rocq notes' rule), and this table's
checkbox below flips when the lane is on `lean-ni`:

- [x] PI-1  - [x] PI-2  - [x] PI-3  - [x] PI-4  - [x] PI-5  - [x] PI-6  - [x] PJ-G  - [x] PJ-L1a  - [x] PJ-L1b  - [x] PJ-L2

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
- [ ] **NI-TRACE** (M2) and **NI-EXT** (M3): unchanged from §6.

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
