VERDICT: NOT SATISFIED

# Review R1 of `notes/weak-allocproc-plan.md` (adversarial, evidence-based; 2026-10-09)

Scope of this round: every load-bearing claim of the plan checked against the tree (`file:line`
cites `../xv6iris-weak`).  No earlier review rounds exist.  Advisory only; no proofs or builds run.

## What checks out (so the owner knows what NOT to re-litigate)

- **F1 is true in substance.**  `Xv6.Allocproc` (`Xv6/LinkAllocproc.lean:14-16`) is
  `allocproc_proof` (`Xv6/ProofAllocproc.lean:3623-3639`, 3639 lines); the header (`:26-40`)
  confirms the scan at a quantified hart via `wpNext` (interrupts may be on), the inlined allocpid
  under `pid_lock` (Löb outer loop, 64-word scan), `p->state = USED`, `kalloc`, `proc_pagetable`,
  `memset` of the context, `ra = forkret`, `sp = kstack+PGSIZE`, both `freeproc` tails.  The
  contract `wp_allocproc_body` (`Xv6/SpecAllocproc.lean:204-224`) has the premises the plan should
  list (see [R1.9]): `k.tier = KTier.kpt`, `allocprocSlots (= 48) ≤ k.avail`, `k.noff + 2 < 2^31`,
  `"kmem"/"nextpid"/"proc" ∉ k.locks`, `procsInv`, the two `isLock`s, `kallocAvail γk on`,
  `procsAvailAt Γ pav tk`, `□ (killCred -∗ Q (-1))`, `actLend`.  It is instantiated in the audited
  cone (`Xv6/LinkSyscall.lean:84`, `Xv6/LinkMain.lean:53`); the audit baseline is the three Lean
  axioms + `bv_decide` certificates + three opaques (`tools/audit/baseline.json:10-14`,
  `notes/adequacy_axioms_baseline.md:19-45`), no `sorryAx` (`:47-48`).  Callee line counts: 10.7k
  (`wc`; `ProofPushOff`/`ProofPopOff` do not exist as files — they are inside `ProofAcquire`/
  `ProofRelease`; fix the list).
- **TsoMem is as described** (`MachCSL/TsoMem.lean:1-40`; fences `:345-364`: `rw,w`/`w,w`/`r,w`
  are no-ops; `fence.tso` acquire-only; `.aq` carried bit `:255-280`; `othersReserve :247`).  xv6's
  release is literally `fence rw,w; sw zero,0(s1)` (`Xv6/ProofRelease.lean:83-86`), acquire is
  `amoswap.w.aq` (`Xv6/ProofAcquire.lean:5,28`); so "the release fence is a no-op view-wise and the
  proof does not exercise it" is correct.
- **sRVWMO as cited** (`Weak/WeakAxiomatic3.lean:2050-2071`: rules 1–5, 7, 14; 6, 8–13 omitted or
  redundant; `srvwmoConsistent :2071`; T1 `srvwmoRealizable :2077`); the two divergences LB and
  reader-fence-only MP (`Weak/WeakSrvwmoLitmus.lean:1663-1695`).  TsoMem has no dependency
  order and neither does sRVWMO, so "exactly the same ppo residue" is right on the ppo side — but
  see [R1.7] for what TsoMem adds beyond it.
- Cited anchors exist and say what the plan says: `t2Ev` (`Weak/WeakEvInst.lean:2046`),
  `tierAAdequacy` (`Weak/AxTierA.lean:91-98`), `robustMain` (`Weak/WeakRobustMain.lean:1520`),
  `xv6RvwmoSafeModulo` (`Weak/WeakRvwmoCapstone.lean:187`), `l2Claim` (`Weak/WeakRvwmoGlue.lean:449`),
  `walkSupply` (`Weak/WeakRvwmoGlue2.lean:453`), `riscvPowerAdequacy` (`MachCSL/Adequacy.lean:266`),
  `xv6FsAdequacy` (`Xv6/SystemAdequacy.lean:543-551`), `wpPfStep` (`Weak/WeakPromiseBridge.lean:339`),
  `primStep` (`MachCSL/Lang.lean:599`), `classify` (`Weak/WeakInterp.lean:306`), `itvPostMachCSL`
  (`:376`), `wgrt` (`Weak/WeakLang.lean:202`), `efetchItvOkRunOfUnwritten` (`Weak/WeakEvCapstone.lean:697`),
  `xv6NiTwoRun` (`Xv6/LinkNiAdequacy.lean:100`), `pteVariant`/`kptBody` (`MachCSL/KptInv.lean:39,85`),
  `rvwmoCatConsistent` (`Weak/AxGraphCat.lean:188`), `AxLitmus.lean:29`, `audit.sh:44`,
  `AxSpinT2b2.lean:126,325`, `relaxed-ww.md:30-41` (the "exactly two ghost steps" quote),
  `weak-memory-lift.md:19-29` (φ refutable), `weak-port-skip.md:6` (`WeakComposeLang` skipped).

## REQUIRED changes

**[R1.1] "≤ NCPU harts" is false; the theorem is at exactly 8 harts.**  `PowerOn` forks
`cpus = List.finRange NCPU` (`MachCSL/Lang.lean:315-319`, "the new generation's whole complement of
harts"); `NCPU = 8` (`MachCSL/TsoMem.lean:52`); `riscvPowerAdequacy` takes `[∗list] cpu ∈ cpus,
hartWP …` (`MachCSL/Adequacy.lean:383`).  Change §A T-alloc-RVWMO and checklist item 2 to "exactly
`NCPU = 8` harts, all booted (the kernel's `param.h` NCPU); fewer harts is NOT covered" and list it
under the named assumptions in §B(11).

**[R1.2] "no hart stuck/panicking (`Reducible`)" overclaims: `Reducible` does not exclude panics.**
`panic` is a verified function with NO postcondition whose contract is a bare `wpLoop`: "a caller
that reaches `panic` has thereby discharged its own goal" (`Xv6/SpecPanic.lean:11-14`, used by
`bread`'s "bget: no buffers" arm).  A panicking hart spins (`for(;;)`), which is reducible; so is a
hart blocked on a foreign reservation (`blockedStep`, `MachCSL/Lang.lean:395-403`, a self-loop).
Change §A item 5 and T-alloc-RVWMO (a) to: "no hart is ever stuck in the machine semantics (no Sail
event without an answer: no unmodelled address, no fault the model rejects); panics are NOT excluded
by the system theorem".  If the owner wants "allocproc never panics" it is new, separate work
(e.g. a UART-trace statement: `printk` is traced through `uartSentSub`, `Xv6/SpecPanic.lean:36-41`,
so "no `panic:` bytes in the console trace" is expressible; size M–L; add as an owner question).
Note the lock cone does refute its own panic arms (`Xv6/ProofRelease.lean:75-77`, "beqz a0, panic:
not taken"), but that is a WP fact, not a conclusion of `xv6FsAdequacy`.

**[R1.3] W1's milestone promises conjuncts the ledgers cannot export; W1 is not "deps: none, one
file" as specified.**  Evidence: `Kev` is `KAlloc p | KNull p | KFree p` (`Xv6/KallocEv.lean:45-52`)
— NO page address; `kmemLedger` ties only counts (`npages + allocs h = frees h`,
`Xv6/KallocDefs.lean:220-222`).  `Pev` is `PAlloc act pid | PFree act pid` (`Xv6/PidEv.lean:50-55`)
— NO slot index.  `liveOf : List Pev → Int → Prop` is a SET (`Xv6/PidEv.lean:69`), so "live pids
pairwise distinct" is vacuous as a predicate on `h`; the meaningful fact is "every `PAlloc` in `h`
picked a pid not live at its prefix (`pid = pidPick PIDMAX prefix`)", which only the per-call
RECEIPT carries (`pidAllocRcpt`, `Xv6/PidLock.lean:118-119`) — the authority `pidLedger`
(`:113-114`) carries only `liveOf h = dom R ∧ pidTie`, and `pidTie`'s cell side is existential
(`pidCells`, `:85`), so slot-uniqueness is not an invariant of the tree:
`claude-notes/kernel-defects.md:245-246` says so explicitly ("Uniqueness (no two live slots share a
pid) is a further step nothing consumes yet").  Therefore: "allocated pages disjoint from every
other live process's pages and from the free list" and "live slots pairwise distinct" are NOT
"pure predicates on the exported histories", and "live pids pairwise distinct" needs a
history-wide invariant the authority does not hold.  Change §A(b), §C W1: EITHER (i) re-scope W1 to
what is exportable today — `PAlloc` pids ∈ [1, PIDMAX] and the counter tie (`nextOf`), `KAlloc`/
`KNull` well-formedness (`poolEmpty`), the slot-exhaustion receipt — and say so; OR (ii) add the
shared-file work honestly: strengthen `pidLedger` with a history-wide `pidHistWf h` (every `PAlloc`
= `pidPick` of its prefix ⇒ live pids distinct by induction) and re-thread `ProofAllocproc`/
`ProofFreeproc`/`NiLedger`; and/or add addresses to `Kev` (ripples through `ProofKalloc`,
`ProofKfree`, `NiLedger`, `UnionOutLed`, every ledger consumer).  (ii) is L, serial, touches shared
files, so it cannot be in "Stage 0, ∥, none touches shared files".  Pick one and size it.

**[R1.4] W1's conclusion must be tied to something an outsider can observe, or it is unfalsifiable.**
The NI idiom the plan invokes ties ghost filings to the OBSERVATION trace (`xv6NiPhi g h := ∃ F,
niOk h F ∧ …`, `Xv6/NiAdequacy.lean:7-9`); "∃ ghost history h, well-formed(h)" alone says nothing
about the run.  Two concrete ties exist in the tree and the plan must choose: (α) a STATE predicate
on `g2.m` — precedent `xv6TracePure … ∧ (g.pow = true → mmOk g.m)` (`Xv6/SystemSlot.lean:135-136`):
e.g. "at the top of the store order, the `proc[i].pid` words of slots whose `state` word ≠ UNUSED
are in [1, PIDMAX] and pairwise distinct"; (β) an OBSERVATION predicate — `Obs.uEnter cpu satp epc
gprs` (`MachCSL/Lang.lean:243-249`) carries the register file at the user boundary, so the pid a
fork returns is in `κs` and `PAlloc` receipts can be cited against it (the NI fork lane F2/F3
already does this).  Add the chosen tie to W1's milestone statement; without it D3's "(Rec) trace-
level ledger predicate" is not yet "a theorem on allocproc an outsider can read".

**[R1.5] W5's chain "T1 → pf run → W4" skips the program half; the right lemmas exist and must be
cited.**  T1 yields `execWf (candExec c)`, which is a run of the MEMORY-ONLY machine `mstep` on a
label trace (`Weak/WeakAxiomatic.lean:273-277`; `Mstate = ⟨msImg, msLog, msWs⟩`, `:103-106`, no
program).  To get an `epfRun` of `WeakEvLang` one needs program conformance of the candidate,
`execProgOk' (pstepPin img pstepEv) pclsEv pst dv (candExec c)` (`Weak/WeakAxRealize.lean:373-386`,
which also does the RMW un-fusing via `lblRealizesPair`) and the lift `execWfPfRunProg`
(`Weak/WeakAxRealize.lean:802-808`); `xv6SrvwmoSafe`'s FIRST conjunct (`Weak/WeakSrvwmoCapstone.lean:
76-102`, proof `:111-116`) packages exactly this and needs none of the WP-package premises.
Change §A T-alloc-RVWMO to quantify over `(c : Cand)` with `srvwmoConsistent c`, `c.cdImg = imgZ
σ0.wgimg`, `execProgOk' (pstepPin …) pclsEv pst dv (candExec c)`, `pst 0 = epsInit σ0`,
`dv 0 = efInit σ0.wgdev` (the (c)-premises of `xv6SrvwmoSafe`), and §C W5 to start from the
`rtc epfRun (epInit gen, σ0) (P', σ')` that conjunct gives.  Also §B(1)(i) ("pf run ⇒
srvwmoConsistent, grep finds no such theorem") should note that route (M) does not need it.

**[R1.6] Conclusion (a) does not transfer through a one-directional simulation.**  W4 (epfRun ⇒
`primStep` run) + `xv6FsAdequacy` gives `Reducible` of the MACHCSL configuration.  `Reducible` of
the weak configuration `(e2, σ2)` needs the converse enabledness at related states (TsoMem-enabled
⇒ WeakMem-enabled), which is not implied by "WeakMem is more restrictive" — it is the opposite
direction.  (`xv6SrvwmoSafe` gets weak-side reducibility from the WEAK WP package `wpPackage`,
`Weak/WeakRvwmoGlue.lean:338-346`, which xv6 does not have.)  Add **W4b** (M): "if the related
MachCSL hart can answer event `o`, the WeakEv hart can answer it" (memory arms total modulo views;
devices/`Efab` aligned), or restate (a) as a property of the projected MachCSL run and say so in
the header.  Trace/state conclusions (W1, `xv6TracePure`) transfer without W4b.

**[R1.7] "TsoMem forbids ONLY W→W reordering and LB" omits a strengthening that must be named.**
TsoMem BLOCKS a foreign hart's store or exclusive read overlapping a held reservation (self-loop;
`MachCSL/Lang.lean:366-378,395-403`) and DMA likewise (`anyReserve`, `:539,562`); the reservation
persists until the holder's next store of ANY address (`MState.store … resv := none`, `:145-153`)
or a blocked exclusive read.  RVWMO's atomicity axiom constrains only SUCCESSFUL LR/SC pairs
(foreign stores in between make the SC fail); sRVWMO keeps exclusives fused (`WeakAxiomatic3.lean:
2070`).  So TsoMem is stronger than both here.  Harmless for kernel code (xv6 uses only `amoswap`,
`ProofAcquire.lean:5`), but user code may `lr` (arbitrary `USER` code is in the theorem), and
the SC success predicates are the two opaques.  Also note WeakMem CLEARS the reservation at any
non-trivial fence (`Weak/WeakMem.lean:686`) while TsoMem keeps it across fences (`MState.fence`,
`Lang.lean:157-160`) — a split-exclusive divergence W2's spike must check.  Change §0 F1 and §B(9)/
(11) to: "forbids W→W reordering and LB (rule 14), AND serialises foreign stores against held
reservations (beyond RVWMO's atomicity axiom)", and add the reservation items to W2's risk list and
to the T-alloc-sRVWMO header's named strengthenings.

**[R1.8] W3's corollary depends on W4, and Stage 1 does not need W3 at all.**  `efetchItvOk` is a
predicate on the WEAK event language (`pstepEv`, `σ.wglog`, `σ.wgitv c`;
`Weak/WeakEvCapstone.lean:681-685`); a MachCSL-side `kernelTextUnwritten` transports to it only
through W4's log projection (or must be re-proved weak-side).  Route (M) (W4/W5) never uses
`efetchItvOk`/`fetchSrcOk`; they are premises of `xv6RvwmoSafeModulo`/`robustMain` (route 9c, W7).
Change W3: "Deps: lemma none; corollary W4; consumer W7", and move its "Closes owner Q4" to Stage 2.
(The lemma itself is a fine Stage-0 item.)

**[R1.9] "The real kernel binary … no mocks" must say WHICH xv6.**  The image is xv6-riscv
`b72cbac1` on the project's `verified` branch, with additions (per-process root `p->root`,
`sys_chroot`, `igetroot`; `notes/STATUS.md:8-11`, `README.md:89-90`) and upstream's post-`ded23f2`
allocpid (bounded counter `PIDMAX = 1000` + liveness scan, inlined by gcc;
`claude-notes/kernel-defects.md:224-231`, `Xv6/ProcGeom.lean:80`).  The textbook allocproc an xv6
expert has in mind has a monotone `nextpid` and no scan.  Change checklist item 1 to name the fork
and the two deltas; list the contract premises of `wp_allocproc_body` (above) as what the caller
discharges; and say "4096 bytes of `5`" is `kalloc`'s fill (`Xv6/SpecKalloc.lean:69`), not
allocproc's, and that `allocprocPost` exposes the trapframe through `procPrivNocwd`, not as a
literal byte list.

**[R1.10] Audit/layout of the composition files is wrong as written.**  `Xv6/` never imports
`Weak/` (grep: 0 files) while 11 `Weak/` files import `Xv6` (e.g. `Weak/AxSpinX.lean`); the lake
libraries are `MachCSL`, `Xv6`, `Weak` in that dependency order (`lakefile.toml:2,28-40`).  So W5
cannot be `Xv6/SrvwmoAdequacy.lean`; it must live in `Weak/` and be registered in
`tools/ci/roots-weak.txt` + `tools/audit/baseline-weak.json` + the `XV6_AUDIT_MODULES` list in
`tools/ci/audit.sh:44`, not `roots.txt`/`baseline.json` (§B(12)).  Its cone will include the whole
`Xv6` adequacy cone; say so (audit time/memory) and that `--weak` CI must build it.

**[R1.11] The W2 spike's STOP rule must also cover the direction in [R1.6]** and the spike report
must list, per memory label, (a) WeakMem ⊆ TsoMem (simulation) and (b) TsoMem-enabled ⇒
WeakMem-enabled (receptiveness).  Spot checks that look fine and can be recorded as such: fences —
WeakMem's `fencePost` raises `wVrNew` to `max wVrOld wVwOld` for `pr,pw` (`Weak/WeakMem.lean:674-678`),
`wVwOld` being the max own-store timestamp (`storePost`, `:634`) = TsoMem's `ownPub`, `wVrOld` =
TsoMem's `rv`; so `fence rw,rw`/`r,r`/`rw,w` agree in the simulation direction.  Items still open:
`wRelp` publication (`:640`), `wRes := none` on fences (`:686`), split exclusives
(`PFExLoad`/`PFExStore`, `Weak/WeakPromiseBridge.lean:414-436`) vs `othersReserve`, i-fetch agent
(no forwarding, `Lang.lean:339-341`) vs `LIFetch`'s `ifetchOk`, DMA vs `Efab`.

## SUGGESTIONS

- [R1.s1] Sizes: `wc Weak/AxSpin*.lean` is 88k lines (plan: ≈ 57k for a subset) — say "≥ 57k".
  allocproc's dynamic footprint has 7 `memset`s of a page (4 `kalloc` fills of `5` + root/L1/L0
  zeroing in `uvmcreate`/`walk`), not 4; the order of magnitude stands.
- [R1.s2] Cite `mmOk` (`MachCSL/Resources.lean:779`) as the already-exported memory-model
  invariant: W5's header can say the TSO histories are well-formed at every reachable state.
- [R1.s3] In §B(2) name the TLB premise precisely: `utlbOk` caches leaves "up to the A/D bits"
  (`MachCSL/UTlb.lean:17-21`); the kernel-table story is `KptInv.pteVariant`.  Both are MachCSL
  modelling choices (hardware A/D write-back as a plain LR/SC that moves no view) — list them in
  §B(11) as trusted-base items, not only in §B(2).
- [R1.s4] §B(9b): the two-log design lives on branch `relaxed-ww-twolog` (Rocq era,
  `relaxed-ww.md:7`); say the Lean port has none of it, so W6's "L" is a fresh estimate.
- [R1.s5] D6: `allocpidOpen2`'s header already describes it as a riscv.cat-tier validation
  (`Weak/AxSpinT2b2.lean:318-324`); the amendment is a one-paragraph note, size S.

## Owner questions the plan is missing

- Q-A. Is "exactly 8 harts, all booted" acceptable as the published hart model, or is a
  "≤ 8 (some harts never leave `_entry`)" variant wanted (a MachCSL change)?
- Q-B. Is "no panic" wanted in the conclusion (UART-trace form, new work), or is "no hart stuck in
  the machine semantics" enough with panics stated as not excluded?
- Q-C. For W1: re-scope to today's ledgers (fast) or strengthen `pidLedger`/`Kev` (shared, L,
  serial) to get pid/slot uniqueness and page disjointness as exported facts?
- Q-D. State-level (α) or observation-level (β) tie for W1's conclusion?
- Q-E. Does "credible for xv6" mean the `verified`-branch fork (chroot + post-`ded23f2` allocpid)
  or upstream master?  (The answer changes the header's first sentence, not the proofs.)
- Q-F. Where does the composed theorem live (`Weak/`, audited under `--weak`), and is the `--weak`
  audit's build cost (the full `Xv6` cone) acceptable in CI?
