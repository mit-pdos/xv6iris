VERDICT: NOT SATISFIED

# Review R3 of `notes/weak-allocproc-plan.md` rev 3 (adversarial, evidence-based; 2026-10-09)

Scope: (1) were R1's and R2's required changes — including the reviser's own [R2.1-alt] and
[R2.3-alt] — applied correctly; (2) a fresh audit of what rev 3 now rests on (the pinned Stage-1
statement, the shape premise, the non-vacuity gate W5c, the (↓) simulation on plain loads).
`file:line` cites `../xv6iris-weak`.  Advisory only; no proofs or builds run.

## R1 / R2 application check

All five R2 items are in rev 3 and substantively right: [R2.1] §B(4), W3/W4/W5 (the lift
`wpPfRtcEpfRtc` does take `efetchItvOk` at every reachable state, `Weak/WeakEvCapstone.lean:1008-1011`;
the capstone's T1 conjunct calls it with `Hcov`, `Weak/WeakSrvwmoCapstone.lean:118-120`; W5 now
starts from `execWfPfRunProg`, `Weak/WeakAxRealize.lean:802-808`, and `wpPfRunPinSub :225`);
[R2.2] `wbootFacts` (`Weak/WeakLang.lean:482-490`: `wgimg = bootImage`, boot-program register
files, `∃ ds, wgdev = ds.reset`, `wgitv = 0`) + `wggen = 0` + the disk; single era (`epowerFork`,
`Weak/WeakEvLang.lean:201-204`, forks the 8 hart loops, two UARTs, the disk agent and the PLIC —
no power thread; `DevId.all`, `MachCSL/Dev/DevIds.lean:35`, is the same four); [R2.3] the split
(`Weak/WeakEvInst.lean:323-331,350-364`), the fused `Lbl` (`Weak/WeakAxiomatic.lean:87-92`), the
pair (`lblRealizesPair`, `Weak/WeakAxRealize.lean:305-313`), the 0-floor `PFExLoad`
(`Weak/WeakPromiseBridge.lean:418-423`), W4b dropped; [R2.4] both spin arms, the i-fetch model,
the SC-failure model in §B(11); [R2.5] W5c added (but mis-specified — [R3.3]).

[R2.1-alt] is right about the MECHANISM — `fetchPin` demands `t = 0` and image bytes for every
fetch label (`Weak/WeakAxRealize.lean:160-165`), `execWfPfRunProg` needs `pstepPinned`, and
`userret`'s `fence.i` (`Xv6/SpecUserret.lean:6`; `ifenceStep_stamp`, `MachCSL/UIcacheFence.lean:152`)
raises TsoMem's `itv` (`MachCSL/Lang.lean:157-163`) so that a user-text fetch of image bytes has
no TsoMem step — but wrong about the INFERENCE it draws ("the pinned theorem therefore covers
kernel-only runs"): the pin does not exclude user-mode candidates, see [R3.1].

[R2.3-alt] is right in substance: `lbNobarex` excludes only `LExStore` (`Weak/WeakAxRealize.lean:97-103`,
"a dangling `LExLoad` realizes a plain load"), `projLbl (LExLoad …) = some (LLoad …)`
(`Weak/WeakPromiseBridge.lean:545`), `PFExLoad` reads at `lat = false` (`:418-423`) while TsoMem's
exclusive read takes `topBytes` and is blocked by `othersReserve` (`MachCSL/Lang.lean:368-371`),
and a held reservation blocks every foreign store until the holder's next store
(`:147-153,377`).  The FORM of the predicate is wrong, see [R3.2].

Also re-confirmed this round: `Xv6.Allocproc` (`Xv6/LinkAllocproc.lean:14-16`) = `allocproc_proof`
(`Xv6/ProofAllocproc.lean:3623-3639`, header `:26-40`: scan at a quantified hart, inlined allocpid
under `pid_lock`, `kalloc`, `proc_pagetable`, `memset`, both `freeproc` tails); `wp_allocproc_body`'s
premises (`Xv6/SpecAllocproc.lean:204-224`); `xv6FsAdequacy_closed`'s three hypotheses and two
conclusions (`Xv6/LinkSystemAdequacyClosed.lean:20-26`: `Reducible` + `xv6TracePure` =
`fsBootPure ∧ (pow → mmOk)`, `Xv6/SystemSlot.lean:135-136`); the baseline (`tools/audit/baseline.json:11-14`,
`notes/adequacy_axioms_baseline.md:19-45`); sRVWMO's residue table and the two divergences
(`Weak/WeakAxiomatic3.lean:2050-2071`, `Weak/WeakSrvwmoLitmus.lean:1663-1695`); TsoMem's fences
(`MachCSL/TsoMem.lean:345-364`) against WeakMem's `fencePost` (`Weak/WeakMem.lean:669-689`:
`wRelp` armed at `pw ∧ sw` `:684`, `wRes := none` at any non-trivial fence `:688`).

## REQUIRED changes

**[R3.1] The pinned Stage-1 statement is UNPROVABLE as written: a pinned candidate CAN enter
user mode, and then (a) has no realizing MachCSL run.  "Kernel-only" must be a PREMISE, not a
consequence of the pin.**  Evidence: (i) a pinned fetch is pf-admissible at floor 0 AT ANY LOG
(`fetchPinIfetchOk`, `Weak/WeakAxRealize.lean:167-176`; `ifetchByteOkb` with `itv = 0` checks
`writesIn (t, max t 0] = ∅`, `Weak/WeakPromise.lean:228-231`), so the replay
(`execPrefixPfRunProg :745-751`; fetches are `lbAdmin true`, `:130-134`; `admStepPf` takes
`fetchPin`, `:426-430`) realizes it whatever the log holds; (ii) the program LTS constrains the
fetched VALUE only through the memory side (`pstepEv`'s i-cache arm, `Weak/WeakEvInst.lean:306-312`:
any `w`, `tvs` of its bytes); (iii) the boot image covers all of RAM and is ZERO past the ELF
(`MachCSL/BootImage.lean:30-45`, `BootImageSpec`).  Hence a conformant, sRVWMO-consistent
candidate exists whose hart runs `userinit` → scheduler → `userret` → `sret` and then fetches
the image's zero bytes at the user page (illegal instruction, trap, kernel kills the process):
`execProgOk' (pstepPin …)` holds, `srvwmoConsistent` holds, W5's premises hold — and W4's
`LIFetch` row has no TsoMem step, because TsoMem reads the latest version ≤ `tvn` with
`itv ≤ tvn` (`MachCSL/Lang.lean:360-362`) and `itv` has passed `uvmfirst`'s writes.  So
T-alloc-sRVWMO as stated in §A is false for that candidate.  Change: (a) add to §A's premise
list `candKfetch c pst` — every `LIFetch` label of the conformance run has its footprint in the
kernel text `[0x80000000, etext = 0x80007000)` (the disassembly's `etext`, `Xv6/KernelImage.lean:771`)
— folded into the shaped conformance predicate of [R3.2]; (b) rewrite footnote (†): "the pin
fixes WHAT a fetch answers, not WHERE it fetches; `candKfetch` is the kernel-only restriction;
Stage 1b (W5d) replaces `pstepPin` + `candKfetch` by Zifencei admissibility"; (c) say the same
in §B(4)(ii)-(iii), W5's header, D18; (d) W3 discharges the (↓) `LIFetch` row ONLY under
`candKfetch` — state W4's row with that hypothesis.

**[R3.2] `candExclPaired c pst` (and `candKfetch`) cannot be a separate conjunct on `(c, pst)`:
the labels it talks about are existentially quantified inside `execProgOk'`.**  Evidence:
`execProgOk'` (`Weak/WeakAxRealize.lean:373-386`) is `∀ k s, … ∃ p pa da p', … admStar … ∧
((∃ l, lblRealizes … l ∧ pstep … l …) ∨ (∃ pm dm pm2 dm2 l1 l2, lblRealizesPair …))` — the
realizing label `l` and the administrative stars (`admStar = rtc admStep`, no label list,
`:343-344`) are chosen per index; "every `LExLoad` of the conformance run" is not a function
of `c` and `pst` (two conformance witnesses for the same `(c, pst, dv)` can differ in `l`).
Change: define ONE shaped conformance predicate `execProgOk'S pstep pcls pst dv E` :=
`execProgOk'` with (i) the left disjunct's `l` not an `LExLoad` (this re-imposes the T1-D gate
`lbFused` on the left arm only, cf. `lblRealizesUnproj :245-247`), and (ii) the stars taken as
label-carrying `admRun`s (`Weak/WeakRvwmoConf.lean:374-381`) whose every `LIFetch` is in kernel
text (Stage 1) / Zifencei-admissible (Stage 1b).  §A's premise is `execProgOk'S (pstepPin …)`;
W5b's `execPrefixPfRunProgShaped` consumes it and carries `pairAdjacent` + the fetch facts
along the run; W5c must PRODUCE it (`execProgOk'Snoc`, `Weak/WeakRvwmoCert.lean:413`, yields plain
`execProgOk'` — W5c needs the S-variant or a derivation lemma); D19 names it.

**[R3.3] W5c is mis-specified: the `sw &started` block does not witness W5's premise set, and
reaching it genuinely is a whole-boot replay.**  Evidence: W5's premises fix `pst 0 = epsInit σ0`
with `wbootFacts σ0` — every hart at the monad BOUNDARY `.pure ()` with the boot program's
register file (`epsInit`, `Weak/WeakEvCapstone.lean:1026-1027`; `wbootFacts`, `Weak/WeakLang.lean:488`:
`bootRun (bootProg …) f₀ = some ((), wgregs c)`), i.e. the pc at `_entry`.  The existing witness
is built at the MID-instruction node `WeakEvStarted.evX2` ("the residual after the fetch and the
179 silent nodes behind it") with an EMPTY administrative run and a register file that is
UNIVERSALLY QUANTIFIED (`Weak/WeakRvwmoConfWit.lean:11-22`); `smC img := ⟨img, []⟩` is over an
arbitrary image and `smSnocConsistent` gives the consistency half only (`Weak/WeakRvwmoCert.lean:522-546`).
And `started = 1` is the LAST store of the boot: `main` runs `kinit(); kvminit(); …;
virtio_disk_init(); userinit();` before it (`Xv6/SpecMain.lean:6-15`) — a candidate reaching it
from `epsInit σ0` carries `kinit`'s freerange (≈ 32k page-memsets) and all of `userinit`
(= allocproc).  Change: W5c's block is `_entry`'s FIRST memory instruction, `ld sp,1000(sp)` at
`0x80000004` (`Xv6/KernelImage.lean:14-17`; the GOT word at `0x8000a3e8`, image bytes, `t = 0`):
one candidate event per hart (or hart 0 alone, the other seven idle), pinned fetches of `_entry`'s
two instructions, the administrative run by kernel evaluation (`esil`, `Weak/WeakEvLift.lean:897`;
`pevrunAdmRun`, `Weak/WeakRvwmoCert2.lean:180`) — the `esil → admRun` bridge at the `pstepEv`
tier that `Weak/WeakRvwmoConfWit2.lean:26-28` records as THE missing mechanism; consistency half
from the first-load-of-the-image lemma `gtraceSnocReadImage` (`Weak/WeakRvwmoFloor.lean:1025-1035`)
or `snocRdAdm` (`Weak/WeakRvwmoCert.lean:257`); a concrete `σ0` with `wbootFacts` (a `bootRun`
output, `MachCSL/BootRun.lean`); and the shaped predicate of [R3.2].  Size M–L, not M.  D16's
text must say what the gate certifies: that the premise set is SATISFIABLE — not that any
candidate reaches `allocproc` (that is the whole-boot replay, D18's user-fetch witness).

**[R3.4] The (↓) simulation fails on PLAIN LOADS even on shaped runs: the pf machine and sRVWMO
are per-byte and admit TORN reads; TsoMem reads every byte of a load at ONE view.  A
single-copy-atomicity premise must be named (or the spike's STOP list must carry it).**
Evidence: WeakMem `readable img log ws vpre a t` is per byte — `t` writes `a` and nothing writes
`a` in `(t, max vpre (coh ws a)]` (`Weak/WeakMem.lean:400-402`); the pf load checks it per byte
(`readOkD`, `Weak/WeakPromise.lean:183-188`), the axiomatic machine likewise (`byteRd`/`rdOk`,
`Weak/WeakAxiomatic.lean:122-130`), and `candShape`/`candValues` are per byte
(`Weak/WeakAxiomatic2.lean:910-921`); no axiom joins the bytes of one label (N10:
"no mixed-size litmus or theorem exists", `notes/weak-memory-scope.md:204-208`).  TsoMem's
plain read picks ONE `tvn` for the footprint and reads each byte's latest entry visible at it
(`MachCSL/Lang.lean:363-367`; `FlatMem.readBytes`, `MachCSL/TsoMem.lean:145-147`).  Counterexample:
two whole-word stores `S1@4`, `S2@6` to `W`, a hart at floor 0: the pf/mstep load with
`ts = [4,4,6,6]` is admissible (each `(t, max 0 0]` is empty) and `srvwmoConsistent`; TsoMem
yields all-`S1` or all-`S2` at every `tvn`.  So a shaped, realized `PFLoad` has no TsoMem step
— exactly W2's STOP condition, not among D7's suspects.  (RMWs are exempt: `rmwLatest`,
`Weak/WeakAxiomatic.lean:134`, puts every byte at the top; fetches under W5d are NOT exempt:
`ifetchByteOk` is per byte, `Weak/WeakPromise.lean:222-231`.)  The RISC-V ISA guarantees
single-copy atomicity for naturally aligned accesses ≤ XLEN, so the premise is ISA-faithful —
but it must be NAMED.  Change: add `candSca c` to §A ("every `LLoad` (and, Stage 1b, `LIFetch`)
of the candidate reads its bytes at one view: `∃ tvn, ∀ j, ts[j]` is the latest write to byte `j`
at or below `tvn` or the hart's own later store"), to §B(11)'s strengthenings, to the relation
`R`'s notes in §B(10), to W2's spike table (row "plain load", marked (↓) iff `candSca`), to
W5b (carried along the run); add D20 (premise vs. an atomicity axiom in sRVWMO — the latter
re-opens T1, XL).

## SUGGESTIONS

- [R3.s1] W1 is largely ALREADY exported.  `xv6NiAdequacy` (`Xv6/LinkNiAdequacy.lean:82-90`) has
  the SAME three boot hypotheses as `xv6FsAdequacy_closed` and concludes `xv6NiPhi g2 κs`
  (`Xv6/NiAdequacy.lean:91-92`), whose `NiClassLaw` (`Xv6/NiTrace.lean:660`, via the filings
  `niOk`, `Xv6/NiLedger.lean:319-322`) contains `niRoundLaw`'s fork row (`Xv6/NiTrace.lean:633-646`):
  the enter's `a0 = usysForkAns ι` = sign-extended `pidPick PIDMAX ι.pev` or `-1`
  (`Xv6/UsysDet.lean:293-302`) at the CITED pid prefix — tie β, with the exit/enter round
  identification already solved (`exitView`/`enterView`, `uroundIdOk`).  Re-scope W1 to "cite
  `xv6NiPhi`; add the pure history lemmas (`pidPick ∈ [1, PIDMAX]`, the `nextOf` tie,
  `poolEmpty` at `KNull`) on `ι.pev`/`ι.kev`": S–M.  Conclusion (b) then reads "every filed fork
  round answers `usysForkAns` of its citation", which also answers how a fork return is
  identified in `κs` (by the filing, not by `satp`).
- [R3.s2] Name the transported companions precisely in (a): `xv6NiAdequacy` and
  `unionAdequacyClosed` (`Xv6/LinkUInitUnion.lean:163-164`) transfer for free along W4's
  projection (same hypotheses); the two-run NI corollaries transfer only if BOTH runs are
  projected candidates.
- [R3.s3] Add to §B(10)'s open items the `.aq` off-by-one: at an acquire pair TsoMem's `tv`
  becomes the WRITE's timestamp `top + 1` (`MachCSL/Lang.lean:150`), WeakMem's `wVrNew` the
  READ's (`exloadPostRunD`), `storePostD` not touching `wVrNew` (`Weak/WeakMem.lean:634-647`);
  `R` must relate `tv = max wVrNew (own last store)`.
- [R3.s4] Cite hygiene: `WeakSrvwmoCapstone.lean:116` → `:118-120`; `BootSharedDev.lean:283`
  proves `diskOf ds0.reset = (ds0.st .virtio).disk` (the `diskOf ds = diskOf ds.reset` reading is
  a corollary, state it); `topBytes` `Lang.lean:368-371`; `othersReserve` on writes `:377`;
  `PFIFetch` `WeakPromiseBridge.lean:441-449`; W5c's `execProgOk'Snoc`/`SnocPair` live in
  `Weak/WeakRvwmoCert.lean:413,453` (the sentence reads as if in `WeakRvwmoCert2`).
- [R3.s5] D7's suspect list: add tearing ([R3.4]) and the `.aq` off-by-one ([R3.s3]) beside
  the parked release fence and the fence-clears-reservation items.

## Owner questions the plan is missing

- Q-K. Single-copy atomicity ([R3.4]): accept `candSca` as a named ISA-faithful premise on the
  candidate, or add the axiom to sRVWMO (re-opens T1; XL)?
- Q-L. Stage-1 coverage ([R3.1]): publish the pinned landing with the explicit premise
  `candKfetch` ("kernel-only candidates", i.e. `userinit`'s uncontended call), or hold until
  W5d makes the fork path a candidate?
- Q-M. Non-vacuity ([R3.3]): is the `_entry` first-load witness (M–L; certifies satisfiability,
  not that any candidate reaches `allocproc`) an acceptable publication gate?
- Q-N. W1 via `xv6NiPhi` ([R3.s1]): accept the re-scope (S–M) in place of a new ledger export?
