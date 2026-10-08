# Weak-memory scope: what the Lean weak tier can and cannot prove (2026-10-08)

Written for the owner (request of 2026-10-08, `notes/weak-port-resume.md:216`). Every claim
cites `file:line` of a Lean declaration or a note; paths are relative to the repository root
(`Weak/…`, `notes/…`) except `oq:N`, which means `~/dev/weak-orch/open_questions.txt` line N.
Anything I could not confirm by reading or grepping is marked **unverified**.

## Executive summary

- **Provable today (32 elementary examples, §1).** Three kinds of proof: (a) litmus verdicts
  decided on concrete graphs (`decide +kernel`), against the faithful riscv.cat model
  `rvwmoCatConsistent` and against the strengthened sRVWMO; (b) program-logic (WPd) results:
  2-hart spill/reload races, lock handoff, a lock-protected counter, and real xv6 `mycpu` /
  `holding` / `push_off` / `pop_off` / `release`; (c) operational invariants on a litmus machine
  and on the promising machine.
- **Caveat on (b).** Q22 (4-byte words at 2-mod-4 pcs made the mycpu/push_off/pop_off/acquire/
  allocpid/release text premises unsatisfiable) is FIXED (update 2026-10-08, §2 N3): `wpdMycpu` is
  applied with every premise discharged (`AxSpinE8f.certA`) and the other text premises are shown
  satisfiable (`Weak/AxSpinTextCerts.lean`, `AxSpinRow3.relStoreTextOf`). The WPds still pin
  control flow by graph-value premises (Option V), and they leave several leaves as λ-bound slots.
- **Not provable (14 items, §2).** Self-modifying code, load→load address dependencies, MMIO
  ordering, LR/SC with failing SC, liveness, unpinned racy control flow, IRIW/SB-fenced in the
  sRVWMO suite, mixed-size accesses, and anything that composes the AxSL tier with the machine tier.
- **Assumptions (16 items, §3).** The Sail model, a hand-written cat model, a machine that is
  stronger than RVWMO (sRVWMO: LB and reader-fence-only MP are forbidden), the residual
  hypotheses of the Tier-2 capstone (`l2Claim`, `walkSupply`), the Stage C fetch pin, the PTW/H5'
  model, the kernel image, and the owner rulings Q11–Q22.

---

## 1. Provable elementary programs

Notation: `x`,`y` are distinct addresses (in the litmus files they are 0 and 1, or 0 and 8),
the image is all-zero, and `r1`,`r2` are registers. "Allowed" means a consistent witness graph or
run is exhibited. "Forbidden" means a proof that the outcome is impossible, with its scope
stated.

### 1(a) Axiomatic tier — decision procedure on a concrete graph

`Weak/AxLitmus.lean` is the suite against `rvwmoCatConsistent` (`Weak/AxGraphCat.lean:188`,
riscv.cat's ppo `gppoCat` at `:178`). An **important scope limit** (`Weak/AxLitmus.lean:15-21`):
an ALLOWED verdict exhibits one gmo, but a FORBIDDEN verdict refutes only **the one natural
candidate gmo**, not every gmo. The single exception, `cowrForbidden`, is proved for every gmo
(see P8).

| # | program | outcome | verdict | Lean |
|---|---|---|---|---|
| P1 | SB: `H0: sw x,1; lw r1,y` ‖ `H1: sw y,1; lw r2,x` | r1=r2=0 | allowed | `sbCat` `Weak/AxLitmus.lean:164` |
| P2 | SB + `fence rw,rw` on both harts | r1=r2=0 | forbidden (1 candidate) | `sbdfCandInconsistent` `:290` |
| P3 | MP: `H0: sw x,1; sw y,1` ‖ `H1: lw r1,y; lw r2,x` | r1=1,r2=0 | allowed | `mpnCat` `:176` |
| P4 | MP, writer `fence rw,w` only / reader `fence r,rw` only / reader plain `amoswap` | r1=1,r2=0 | allowed (each) | `mpwCat` `:189`, `mprCat` `:203`, `mprmwCat` `:218` |
| P5 | MP with both fences | r1=1,r2=0 | forbidden (1 candidate; rule 4) | `mpdfCandInconsistent` `:259` |
| P6 | MP: writer `fence rw,w`, reader `lw.aq r1,y` | r1=1,r2=0 | forbidden (1 candidate; rule 5) | `mpaqCandInconsistent` `:274` |
| P7 | LB: `H0: lw r1,x; sw y,1` ‖ `H1: lw r2,y; sw x,1` | r1=r2=1 | allowed (riscv.cat) | `AxLitmus.lbCat` `:225` |
| P7' | LB with a data/ctrl dependency on each side | r1=r2=1 | forbidden (1 candidate; dependencies in gmo) | `lbDepsCandInconsistent` `:328` |
| P8 | CoWW `sw x,1; sw x,2` / CoRR `sw x,1; sw x,2 ‖ lw x(=2); lw x(=1)` / CoWR `sw x,1; sw x,2; lw x(=1)` | as listed | forbidden; CoWR for **all** gmo | `cowwCandInconsistent` `:243`, `corrCatInconsistent` `:306` (+ the isolation check `corrNo2Accepts` `:321`), `cowrForbidden` `:350` |
| P9 | ctrl dependency then forwarding: `H1: lw z; [branch]; sw x,1; lw x` with the forwarded read placed first in gmo | consistent | allowed in the tagged model, refuted by untagged rule 12 | `twCatT` `Weak/AxDeps.lean:876`, `twNotCatForget` `:883`, `catTSeparates` `:898` |
| P10 | every SC-interleaved tagged graph, e.g. the 2-hart allocpid-shaped spike graphs `g10`/`g40` | consistent | allowed, generically | `scGraphCatT` `Weak/AxScCat.lean:188`, `g40CatT` `:268`; `scStrictlyStronger` `:280` (SC is strictly stronger) |
| P11 | PTE install: `sd pte; sfence.vma; [walk]; ld` | walker reads the new PTE and agrees | allowed, model holds | `gAdSoundF` `Weak/AxSfence.lean:495`, `gsfokSoundF` `:638` |
| P12 | PTE race without sfence: `H1: sd pteNew` ‖ `H0: [walk]; ld` | walker uses the stale PTE although `sd` is gmo-earlier | allowed (no agreement) | `raceBreaksAgreeF` `Weak/AxSfence.lean:559` |
| P13 | 2-hart lock graph `amoswap.aq L; sw x; fence rw,w; sw L,0` ‖ the reader twin | consistent; premises of the program-logic theorem L3 hold | allowed (certificate) | `gABCat` `Weak/AxLock3Cert.lean:76`, `lock3sCertAB` `:87` |

The sRVWMO suite, `Weak/WeakSrvwmoLitmus.lean`, is checked against `srvwmoConsistent`
(`Weak/WeakAxiomatic3.lean:2073`), which is RVWMO plus rule 14, "stores are never early"
(`:2050-2071`). Its negative verdicts cover the **whole candidate family**, not one candidate:

| # | program | outcome | sRVWMO | Lean |
|---|---|---|---|---|
| P14 | SB; MP plain; MP writer-fence-only | weak | allowed | `sb00Allowed` `:703`, `mpnWeakAllowed` `:827`, `mpwWeakAllowed` `:959` |
| P15 | `sw x,1 ‖ amoswap.aq r1,x,2` | AMO reads the latest value | allowed | `amoLatestAllowed` `:1065` |
| P16 | MP both fences / MP fence + `.aq` / CoRR | weak | forbidden | `mpfForbiddenModel` `:1308`, `mpaForbiddenModel` `:1401`, `corrForbiddenModel` `:1572` |
| P17 | **LB** / **MP with only the reader fence** | weak | **forbidden** (RVWMO allows both: the two deliberate divergences, `:1658-1695`) | `lbForbiddenModel` `:1196`, `mpgForbiddenModel` `:1487` |
| P18 | release→acquire MP (`sw.rl` … `lw.aq`) | stale acquire read | forbidden with `.rl`, reachable without it | `ceRlTrueInconsistent` `Weak/WeakAxiomatic3.lean:1833`, `ceRlStaleReachable` `:1862` |
| P19 | own-store forwarding `sw x; lw x` | early read | machine-reachable | `ceFwdReachable` `Weak/WeakAxiomatic3.lean:2042` |

### 1(b) Program logic (WPd over graphs, AxSL tier)

All of these hold for **every** `rvwmoCatConsistent` graph that satisfies the stated row shape,
given that the per-hart runs of the opax LTS cover the rows (`tierAAdequacy`,
`Weak/AxTierA.lean:91-98`, premises `Hrun`/`Hend`).

- **L1. Stack spill/reload with an arbitrary racing hart.**
  `H0: c.sdsp ra,8(sp); c.ldsp ra,8(sp)` ‖ `H1:` any program with a WPd from its own slot's
  resources ⟹ the reload returns the spilled value: `epiReloadSound3`
  (`Weak/AxEpiSound3.lean:136`). A store-forwarding variant without the gmo premise is
  `epiReloadSound3Fwd` (`Weak/AxEpiSoundFwd.lean:125`). Extended to `c.sdsp; c.ldsp; c.jr ra`
  (PC = the saved target): `epiRetSound2` (`Weak/AxEpiRetb.lean:1175`; statement at
  `Weak/AxEpiRetCert.lean:121-155`). Negative twin (ownership carries the proof): the concrete
  racing `H1: c.sdsp` into H0's slot has **no** WPd, `race2WpdUnprovable`
  (`Weak/AxEpiRace2Run.lean:209`).
- **L2. Lock handoff over abstract rows.**
  `A: sw x (owned); fence rw,w; sw L,0` ‖ `B: amoswap.aq L (reads 0 from A); lw x` ⟹ B's read
  gets the token / value: `lockSliceHandoff'` (`Weak/AxLockSlice.lean:201`). It carries
  explicit residual hypotheses (`:21-28`). A satisfiability witness is `race4Sound`
  (`Weak/AxLockWitness.lean:192`). A racing third writer is excluded only by ownership:
  `raceWcExcludedAtWxWrelSlot` (`Weak/AxLockRace.lean:174`).
- **L3. Lock-protected MP, 2 harts.** The programs are hand-written Sail-monad terms, with no
  decode (`Weak/AxLock3Prog.lean:311-315`, `:430-434`):
  `A: amoswap.aq L; sw x,vA; fence rw,w; sw L,0` ‖ `B: amoswap.aq L; lw x(=vB); fence rw,w; sw L,0`.
  If B's acquire reads from A's release, then vB = vA; if B acquires first, it reads the initial x.
  This is `lock3sValue` (`Weak/AxLock3Thm.lean:402`), and it assumes both acquires read `0`
  (`Hb0A/Hb0B`, `:21-22`). A racing unlocked writer is refuted by `raceWpdUnprovable`
  (`Weak/AxLock3Race.lean:250`).
- **L4. Lock-protected counter (allocpid-shaped), 2 harts.** Each hart runs
  `amoswap.w.aq lk; lw np; sw np,np+1; fence rw,w; sw.rl lk,0`
  (`Weak/AxSpinU2.lean:77-82`; hand nodes at real widths, no fetch/decode). The two harts read
  distinct pids: `uAlloc2` (`Weak/AxSpinU4.lean:87`), with the certificate `uaSound` (`:375`). An
  unlocked `sw np,5` racer has no WPd: `urWpdUnprovable` (`:431`).
- **L5. Real xv6 functions** (S-mode, SIE = 0, warm TLB, positional CPS WPd at the joint
  instance Ixv6):
  `mycpu` — `wpdMycpu` (`Weak/AxSpinE8.lean:306`); `holding` — `wpdHolding`
  (`Weak/AxSpinHdA.lean:185`); `push_off` — `wpdPushOff` (`Weak/AxSpinPO4.lean:132`); `pop_off` —
  `wpdPopOff` (`Weak/AxSpinPO6.lean:362`); `release` — `releaseWpd5`
  (`Weak/AxSpinCtl3.lean:605`); the `sfence.vma zero,zero` whole-instruction certificate —
  `sfenceWhole` (`Weak/AxSfence2.lean:503`). **Status:** `wpdMycpu` is vacuous in this tree
  (`AxSpinE8f.mycpuTextFalse`, `Weak/AxSpinE8f.lean:287`; explanation at `:22-31`), and
  `holding`/`push_off`/`pop_off` compose it, so they inherit the unsatisfiable `mycpuText`
  premise (`Weak/AxSpinE8f.lean:29-31`). Every other premise of `wpdMycpu` holds at a
  concrete instance (`AxSpinE8f.wpdMycpuPremises`, `:34`). `releaseWpd4`
  (`Weak/AxRelease4.lean:936`) is vacuous for a different reason: its `rli_10` premise is
  ⌜False⌝ (`instr4Rli10False`, `Weak/AxSpinCtl.lean:323`). `releaseWpd5` replaces it, but
  `w_cret`, `w_hold`, `w_pop` and the stack/cpu ownership lemmas are still λ-bound
  (`Weak/AxSpinCtl3.lean:18-21`). The full acquire is not closed. Its row shape and text facts
  exist (`Weak/AxSpinAqr.lean`); `acquireText` is satisfiable since the Q22 fix
  (`AxSpinTextCerts.acquireTextOf`).

### 1(c) Operational

`Weak/WeakLitmus.lean` defines a tiny hart language over the promise-free view machine
`WeakMem`. **It is not Sail** (`:6-8`). Verdicts are reachability or invariant facts about
`lstep` runs:

| # | program | verdict | Lean |
|---|---|---|---|
| O1 | SB / MP plain / MP writer-fence / SB with `fence rw,rw` (0,1) | reachable | `sb00Reachable` `:228`, `mpNofenceWeakReachable` `:249`, `mpWfenceWeakReachable` `:275`, `sbFenced01Reachable` `:304` |
| O2 | MP both fences / MP `.aq` / MP reader-fence-only / CoRR / LB | unreachable | `mpFencedForbidden` `:516`, `mpAcquireForbidden` `:606`, `mpReaderFenceOnlyForbidden` `:701`, `corrForbidden` `:836`, `lbForbidden` `:1065` |
| O3 | IRIW, 4 harts, both readers `fence rw,rw` | unreachable | `iriwForbidden` `:1291` |
| O4 | `sw x,1 ‖ amoswap.aq r1,x,2` reads 1; own-store read-back keeps coherence; `.aq` is never forwarded | reachable / facts | `amoSwapReachable` `:1344`, `fwdSelfreadCoh` `:1382`, `fwdSelfreadAcquire` `:1387` |
| O5 | LB in the **full promising** machine | reachable | `lbWeakOutcomeReachable` `Weak/WeakPromiseLitmus.lean:185` |
| O6 | every litmus run projects to an `execWf` execution of the axiomatic LTS | theorem | `lstepExecWf` `Weak/WeakLitmusProj.lean:271` |
| O7 | xv6 boot handoff (`main.c`: `fence rw,w; c.sw started` ‖ `c.lw started; fence r,rw`), view-tier Iris | without the fence the payload is not delivered; with it, it is | `mpLoadAloneDoesNotDeliver` `Weak/WkStartedMp.lean:129`, `mpFenceDelivers` `:142`, `wstartedMpByte` `:172` (per-instruction leaves still above it, `:18`) |
| O8 | the real store `main+0xb0` `c.sw a4,0(a5)` run through Sail | two data words give label lists that differ pointwise only in the data | `rswPair` `Weak/AxPair2.lean:242`, `rswTwoWords` `:288` |

---

## 2. Not provable (or not yet)

- **N1. Self-modifying code, or executing freshly written bytes.** In the graph tier every fetch
  is pinned to the **boot image at timestamp 0** (`WeakAxRealize.fetchPin`,
  `Weak/WeakAxRealize.lean:160-165`). The pin sits in the WP step clause (Q8,
  `notes/weak-port-architecture.md:283`) and in the program LTS `pstepPin` (`:184-186`). So
  "store code, `fence.i`, jump to it" has no graph-tier model. The machine tier does model
  `fence.i` through the i-cache view (`WeakInterp.itvPost`, `Weak/WeakInterp.lean:363`;
  `amo_acq_fenceI`, `Weak/WeakFence.lean:399`), but the capstones **carry** "fetched bytes not
  written below the i-cache view" as `efetchItvOk` (`Weak/WeakEvCapstone.lean:681-686`; owner
  Q4 "leave as premise", `notes/weak-port-architecture.md:266`). I found no elementary fence.i
  litmus theorem (**unverified absence**).
- **N2. Load→load address dependency (e.g. MP with an address-dependent reader).** The xv6
  load emission masks the load's address sources (D-8), so neither the rule-9 load-half edge nor
  the general rule-13 edge is recorded (`rowDepsTR13Masked`, `Weak/AxDeps.lean:757`), and sRVWMO
  omits that rule (`Weak/WeakAxiomatic3.lean:2065-2067`). Forbidding MP+addr therefore cannot be
  derived from dependency edges. This is the sound direction: the model is weaker than RVWMO here.
- **N3. (RESOLVED 2026-10-08) 4-byte instructions at 2-mod-4 pcs (Q22).** `textAt4S` used to
  require `is_aligned_vaddr pc 4`, so text facts at ~half of this kernel's 4-byte words (mycpu,
  push_off, pop_off+0x16, acquire+0x12, the inlined allocpid, release's lock words) were false.
  Fixed in place (`Weak/AxDataX6.lean`, `textAt4S`): the 2-mod-4 arm models Sail's two halfword
  fetches, under a no-page-straddle conjunct (owner Q22a). What remains unprovable: a 4-byte
  instruction straddling a page boundary (in this kernel only `log_write+0x34`, unused by the weak
  line). Acceptance: `AxSpinE8f.mycpuTextOf`/`certA`, `AxSpinRow3.relStoreTextOf`,
  `AxSpinTextCerts.{pushOff,popOff,acquire,allocpid}TextOf`.
- **N4. Control flow that depends on racy or diverted values without value pins.** Under Stage C a
  diverted return into mapped text is not stuck (Q20, oq:35), so the "diverted ⇒ stuck" verdicts
  cannot be proved. Rocq's `Xx_ret` shape is provable only vacuously
  (`notes/weak-port-q20-offrow.md:10`, `:117-125`). The theorems instead **assume** the return
  value (Option V, oq:36): `graphValue … (i,k+2) = some (stBytes 8 ret) → jalrTgt 0#12 ret = ret`
  (`Weak/AxSpinE8.lean:322`). Likewise, the `c.jr` capstone does not cover a racing value whose
  target is `pcJr` itself (`Hafter`, Q15, oq:28). The inlined allocpid scan reads are racy and
  value-pinned (Q18a/b, oq:38-39). The E8d stuck twin is false on Rocq's literal instance and
  was restated on a synthetic one (Q21, oq:43).
- **N5. Liveness and progress.** Adequacy is partial correctness. It needs the run handed in and
  covering the row (`Weak/AxTierA.lean:91-98`); WPds are `.MaybeStuck`; harts never terminate
  (`terminated s := False`, `Weak/AxOpsem.lean:41`); a spin loop's failed iterations are "NAMED,
  not modelled" (`Weak/AxLockSlice.lean:18-19`). So "acquire eventually succeeds" or deadlock
  freedom cannot be stated. I found no fairness theorem by grep (**unverified absence**).
- **N6. Devices / MMIO ordering.** Opax graph reads require `devAddr = false`
  (`Weak/AxOpsem.lean:515`). Device steps are erased existentially, not oracled (`:32-33`). The
  per-instruction relation `tpdd` is false for the real store's continuation because its MMIO
  branch reaches the console (`Weak/AxPair2.lean:18-20`). The graph tier cannot express
  `fence io`-style ordering (**unverified** whether any `fence o,i` theorem exists elsewhere).
- **N7. LR/SC with a failing SC or a dangling reservation.** Exclusive pairs are FUSED into one
  `LRmw`; a bare `LExStore` is excluded by gate `lbNobarex` (`Weak/WeakAxRealize.lean:19`,
  `:99-103`). Split-exclusive shapes are outside the sRVWMO suite's alphabet
  (`Weak/WeakSrvwmoLitmus.lean:1652-1655`). The reservation predicates are opaque constants
  (`notes/adequacy_axioms_baseline.md:36-38`).
- **N8. Page-table updates without `sfence.vma`.** The model admits a stale walk (P12), so no
  "the new mapping is used" property holds without the marker. Every PTW conclusion also rests
  on the H5' walker model (A11).
- **N9. Litmus shapes not done.** AxLitmus skips the `.aq`-RMW spinlock handoff, CoRW, 2+2W, the
  "R" test, and a computed RVWMO⁻ verdict for `cowr`/`corr` (`Weak/AxLitmus.lean:29-31`). The
  sRVWMO suite lacks IRIW, SB-fenced in both directions, and the atomicity negative
  (`Weak/WeakSrvwmoLitmus.lean:1635-1651`). The cat-tier FORBIDDEN verdicts other than CoWR are
  one-candidate refutations (`Weak/AxLitmus.lean:15-21`). A full "no gmo works" proof would need
  completeness of `gwfB`/`gloadValueB`/`gatomB`, which is not proved.
- **N10. Mixed-size and misaligned data accesses.** Grepping `Weak/` and `notes/` for
  mixed-size or misaligned finds only Sail-internal simp lemmas and the misaligned-**PC** fault
  arm (`Weak/AxSpinVA7.lean:3-12`). No mixed-size litmus or theorem exists (**unverified
  absence**). The graph model is byte-granular (`gwritesByte`/`greadsByte`); whether its
  coherence matches riscv.cat on mixed-size accesses is **unverified**.
- **N11. Store forwarding in the Tier-2 route.** RVWMO⁻ orders a write before its own po-later
  same-byte read, which forbids forwarding (`Weak/AxGraphCat.lean:10-16`). The Tier-2 capstone
  quantifies over RVWMO⁻(+deps) graphs (`Weak/WeakRvwmoCapstone.lean:10-14`), so on that route a
  forwarding execution is not covered. The AxSL tier uses the faithful model (L1-Fwd).
- **N12. Composing the two tiers.** No machine-tier file (`Weak/Weak*.lean`, `Weak/Wk*.lean`)
  mentions `rvwmoCatConsistent` or `tierAAdequacy` (grep). So no Lean theorem carries an
  AxSL-tier WPd result (§1(b)) down to the Sail machine. No `Weak` theorem is a CI root either
  (`tools/ci/roots.txt:6-18`, Xv6 only).
- **N13. Skipped files** (`notes/weak-port-skip.md:3-38`): the archive `WeakShape*` (26 files),
  `WeakCompose`/`WeakComposeLang`, `WeakRobustL2b`, `WeakSailCone`, and `WeakSailLTS`/`LTS2`.
  Under O2 the `sailShaped` premise of `WeakSailLTS` is false at every fetch, so its theorems
  would be vacuous (`:38`). `WeakSailComplete` is ported as its register-file section only.
- **N14. Dropped in porting** (each false or unused under Stage C):
  - `race2_hart1_stuck` (`Weak/AxEpiRace2Run.lean:32`, oq:25);
  - `chk_pre_exits` (`notes/weak-port-protocol.md:308`);
  - Rocq `Htxt8`/`cert_a` (`Weak/AxSpinE8f.lean:96`);
  - 14 trivial-instance declarations of AxEpiRetFwd (oq:33);
  - `wlabel_is_fetch` (`notes/weak-port-protocol.md:157`).

  Restored after first being dropped: the fetch-address stuck verdicts (Q13, oq:26;
  `notes/weak-port-protocol.md:246`).

---

## 3. Main assumptions

**Trusted base**

- **A1. Logic and axioms.** CI lint bans `sorry`/`admit`, `axiom` declarations and
  `native_decide` in `Weak/` (`tools/ci/lint.sh:8-10`), as the owner ruled
  (`notes/weak-port-architecture.md:232-233`). The top theorems use only `propext`,
  `Classical.choice`, `Quot.sound` and `bv_decide` certificates (`notes/STATUS.md:18-19`;
  `notes/adequacy_axioms_baseline.md:19-24`). The axiom **audit**, however, covers only the Xv6
  roots (`notes/adequacy_axioms_baseline.md:12-15`). Whether any tool prints the axioms of
  `Weak` theorems is **unverified**: they are not audit roots.
- **A2. The Sail model.** sail-riscv fork `070832a1`, regenerated with `-D SYMBOLIC`, with
  lean-sail `Outcome` announce events added (`notes/weak-port-architecture.md:54-75`,
  `:224-227`). The drift from the Rocq weak line's `c32fbf41` is 3 commits, and only
  `AK_ifetch`/`AK_ttw` matter (`notes/weak-port-sail-drift.md:1-15`). There are two opaque
  reservation predicates and the platform hooks (`notes/adequacy_axioms_baseline.md:34-43`). The
  Lean model's whole cone is trusted (84 of 90 files, `:67-69`).
- **A3. Kernel image and build.** `Xv6/KernelImage.lean` is auto-generated by
  `tools/dump_kernel.py` from xv6-riscv `b72cbac1` (`Xv6/KernelImage.lean:1`;
  `notes/STATUS.md:8`). Drift from Rocq's kernel:
  - `allocpid` has no symbol; gcc inlined it into `allocproc+0x38..+0x94`, together with a
    64-round pid-collision scan. The Ap line was retargeted (`Weak/AxSpinAp.lean:3-11`; Q18, oq:32).
  - `mycpu` moved to 0x8000195c (`Weak/AxSpinE8f.lean:25-28`).
  - `release+0x34`'s jal immediate drifts (`Weak/AxSpinCtl3.lean:26-31`).
  - The s1 spill in `release` is sourced from acquire's `c.ldsp`, not from `lw nextpid`
    (INFO-CTL, oq:44).

**Memory-model fidelity and the operational↔axiomatic link**

- **A4. The cat model is a hand transcription.** `rvwmoCatConsistent` (`Weak/AxGraphCat.lean:188`)
  omits rules 6, the RCpc part of 7, and 8. Each omission enlarges the model, which is the sound
  direction (`:42-43`). Untagged rule 12 is **stronger** than RVWMO
  (`ctrl;[W];rfi;[R]`, `:39-42`); the tagged model fixes this (P9). Fidelity is checked only by
  the litmus suite ("No disagreement with riscv.cat/herd found", `Weak/AxLitmus.lean:29`), not by
  any proof of equivalence with herd.
- **A5. The machine is sRVWMO, which is stronger than RVWMO.** sRVWMO adds rule 14 (stores never
  early) and keeps ppo rules 1–5, 7 and 14 (`Weak/WeakAxiomatic3.lean:2050-2071`). The proved
  links are:
  - T1: `srvwmoRealizable` (`:2077`), sRVWMO-consistent ⇒ a promise-free run;
  - T2: `t2Ev` (`Weak/WeakEvInst.lean:2046`), a run ⇒ an `execWf` execution;
  - `rule14Linearization` (`Weak/WeakRvwmoLin.lean:1846`), RVWMO⁻ + rule 14 ⇒ an sRVWMO
    candidate.

  Consequence: hardware that exhibits LB, or reader-fence-only MP, is outside the machine's
  behaviours (P17; `Weak/WeakSrvwmoLitmus.lean:1676-1695`). The bridge from the promising machine
  (LB reachable, O5) to the promise-free machine is the robustness theorem `robustMain`
  (`Weak/WeakRobustMain.lean:1520`). It needs violation-free promise-free runs and the premise
  `fetchSrcOk` (`Weak/WeakRobustSim.lean:530`; Q4).
- **A6. The Tier-2 capstone holds modulo residual hypotheses.** `xv6RvwmoSafeModulo`
  (`Weak/WeakRvwmoCapstone.lean:187`) carries:
  - (R-1) `l2Claim` (`Weak/WeakRvwmoGlue.lean:449`), "L2′ proper, the project's remaining
    content";
  - (R-2) `walkSupply` (`Weak/WeakRvwmoGlue2.lean:453`);
  - the fetch-view premise `efetchItvOk` (residuals `Weak/WeakRvwmoCapstone.lean:18-19`; fetch-view premise `:42`, `:194`).

  `xv6SrvwmoSafe` (`Weak/WeakSrvwmoCapstone.lean:76`) takes the WP package and `efetchItvOk`
  as premises (`:36-38`, `:90`).
- **A7. The AxSL tier's hardware interface.** An AxSL result applies to an execution only if that
  execution **is** an `rvwmoCatConsistent` graph whose rows the per-hart opax runs of
  `riscvStep` realize, with values free at reads and checked in identity at writes
  (`Weak/AxOpsem.lean:13-29`; `Weak/AxTierA.lean:91-98`). Nothing proves that the machine tier
  produces such graphs (N12).

**Stage C, fences, page tables**

- **A8. Stage C: fetches are not graph events.** The owner reversed D1
  (`notes/weak-port-architecture.md:267-275`). A fetch is an admin label pinned to the boot image
  (A9). This is argued faithful in `notes/weak-port-o2-stageC.md:12-29`: riscv.cat has no fetch
  events, and removing the edges only admits more executions. The argument relies on xv6 never
  writing kernel text (`:66-72`), which is carried as `efetchItvOk`, not proved (Q4).
- **A9. Fetch pin in the WP step clause.** Q8 (`notes/weak-port-architecture.md:283`; oq:14),
  with the residual per-tick hypotheses `noSfAnn`/`sfAnnB = false` on the row-run lemmas (Q10,
  oq:21-22).
- **A10. The `sfence.vma` marker.** The marker is `LFence false false false false`, emitted at
  the SFENCE.VMA announce (Q7, `notes/weak-port-q7-sfence.md:22-25`). An illegal `sfence.vma`
  (U-mode, or TVM set) also emits it (`:47-48`).
- **A11. The walker model H5'.** `ptwModelF` and its clauses (`Weak/AxSfence.lean:25-33`,
  `:224`) are hardware assumptions beyond RVWMO. H5'.2 is "a genuinely new hardware clause"
  (`:599`, `gsfNotH5F`).

**Option V and owner rulings (oq:23-48; consolidated ruling at oq:48)**

- **A12. Option V (Q20′, accepted at oq:48).** Control flow is pinned by graph-value premises,
  e.g. `Hval` and `Hret : jalrTgt 0#12 ret = ret` (`Weak/AxSpinE8.lean:322`). The same holds for
  push_off/pop_off/holding returns and branch arms (`notes/weak-port-protocol.md:358-379`). This
  is the Stage C form of Rocq's "TEMPORARY ASSUMPTION — ROW PINNING" (`Weak/AxSpinE8.lean:30-37`).
- **A13. Stage C restatements Q11–Q16.**
  - Q11: after-step boundaries and a second pinned fetch (oq:23).
  - Q13: no-image fetch ⇒ stuck (oq:26).
  - Q14: cold-page tail (oq:27).
  - Q15: `Hafter` (oq:28).
  - Q16: EvB no-image case (oq:29).
- **A14. Accepted INFO deviations.**
  - Q17: `XGprWriteL`, a stronger lifting premise (one more ▷), oq:37.
  - LEAFS5: ▷-free slots abstracting `Xv6.release_gen_proof`, oq:42.
  - REL4: `instrX` text premise, true at release's words but not kernel-wide, oq:45.
  - CTL3: `wBrTaken`, a new premise of `releaseWpd5`, `Weak/AxSpinCtl3.lean:49-51`, oq:47.
  - CTL: the s1 spill source, oq:44.
  - Q18a–c: a value-agnostic racy scan, value premises, and the `p->pid` flow as a premise,
    oq:38-40.
  - Q21: the restated synthetic E8d instance, oq:43.
  - Q19: the `cSf` rework (oq:34). `sfenceWhole` is now present (`Weak/AxSfence2.lean:503`).
- **A15. Remaining unproved hypotheses carried as theorem premises.**
  - `releaseWpd5`: `stackOwnSlots` (`Weak/AxSpinCtl3.lean:457`), `wCret5` (`:459`), `Hdead`,
    `wBrTaken` (`:598-599`).
  - `lockSliceHandoff(')`: `H_L`, `Hnalloc_*`, `Hpol`, `Hfence`, `Hsn`, and the unprimed
    `Hhandoff` (`Weak/AxLockSlice.lean:21-28`).
  - `lock3sValue`: `Hb0A/Hb0B` (`Weak/AxLock3Thm.lean:21-22`).
  - The machine capstones: `efetchItvOk` / `fetchSrcOk` (Q4).

  `wCret4` is **unverified**: grep finds only `wCret5`.
- **A16. Interface restatements.** Q3: Rocq's `mmode_config` is replaced by `mConf` plus the
  clock cells (`notes/weak-port-architecture.md:263-265`). Q1: device programs are modelled in
  the event tier (`:259-261`; `Weak/WeakEvCapstone.lean:66-73`).
