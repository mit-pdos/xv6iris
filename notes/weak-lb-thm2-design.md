# Theorem 2 (`allocpidOpen`) on the Lean weak tier — design (advisor, 2026-10-08)

Advisory only; read-only survey of the finished weak port (`Weak/*.lean`, same tree as
`../xv6iris-weak`), the Rocq plan of record (`notes/rocq-spinlock-plan.md` rev 8), the step-3 plan
(`notes/rocq-spinlock-step3-plan.md`, ID-1..ID-10), `notes/weak-memory-scope.md`,
`notes/weak-port-architecture.md` (Stage C, Q8) and `~/dev/weak-orch/open_questions.txt` (Q18a-c,
Q20' Option V, Q21, Q22/Q22a).  `file:line` cites this workspace.  Nothing here is proved; estimates
are S ≤ 300 lines, M ≤ 600, L ≤ 1000.

## A. Assumption / feasibility check

**Verdict: Theorem 2 is stateable and provable, non-vacuously, in the current Lean tier — as a
TWO-STAGE landing.**  Stage T2-core (this plan): both conjuncts for COMPLETE rows under Option V,
where "no panic" is carried by graph-value pins (the panic branches are pinned not taken) and
DISTINCTNESS + the nextpid-source fact are proved from ownership through the joint adequacy.  Stage
T2-cuts (later, ID-8): panic-freedom proper (cut rows refuted by D4 readback).  Reasons:

1. **Everything below the two lock functions exists in Lean.**  Joint adequacy
   `tierAAdequacyAnnGateJointT` (`Weak/AxSpinJ.lean:352`; iProp posts Φ, `Hjoint ==∗ ⌜P⌝`,
   `HobAlloc`, `Hok`) — exactly the plan's Phase-3 variant; the open-third-hart shape on hand
   nodes `uAllocOpen` (`Weak/AxSpinJ2.lean:361`) with certificates `ua3Sound`/`ur3WpdUnprovable`/
   `ur3WpdTrivial`; the joint instance Ixv6 `protXv6`/`RPid`/`xv6Init`/`xv6HobAlloc`/`xv6Hok`
   (`Weak/AxSpinX.lean:600-616, 659, 665, 765`) with Theorem 2's ghosts `●mono`, `issuedAuth`,
   `issuedFrag`, `issuedFragExcl` (`Weak/AxSpinX2.lean:256`), `npIssue` (`:264`), `FRAG`
   (`Weak/AxSpinU.lean:244`), `npSrc` (`:111`); the positional leaves `XxReg/XxSt/XxLd/XxRet`
   (`Weak/AxSpinE6.lean:142-303`), `XxLdW` (AxSpinXP2), `XxStF`/`FstMNp`/`FldMWNp`/`FldMWScan`
   (`Weak/AxSpinAp8.lean:105-396`), the amoswap leaf `XxAmoswap` (`Weak/AxSpinAm3.lean`) with
   `OAcq`/`FstAcqNh` (`Weak/AxSpinAm4.lean`); the real callees `wpdMycpu` (`Weak/AxSpinE8.lean:306`),
   `wpdHolding` (`Weak/AxSpinHdA.lean:185`) with both call sites `holdingFromAcquire'`/
   `holdingFromRelease'` (`Weak/AxSpinHdC.lean:242, 328`), `wpdPushOff` (`Weak/AxSpinPO4.lean:132`),
   `wpdPopOff` (`Weak/AxSpinPO6.lean:362`), the inlined critical section `wpdAllocpidCs`
   (`Weak/AxSpinAp9.lean:503`), acquire's row shape `RowAcquire`/`spinVals`/`aqKp/aqKh/aqKm/aqKA`
   (`Weak/AxSpinAqr.lean:103-126`), the text certificates (`Weak/AxSpinTextCerts.lean`,
   `AxSpinE8f.certA`), and the certificate toolkit `graphOfSc`/`scGraphCatT`/`graphOfScCtrlClosed`/
   `drive2`/`runGraphOfSc`/joint tracer `jrun` (`Weak/AxScCat.lean:188`, `Weak/AxScRun.lean:1374,
   1477`, `Weak/AxScRun2.lean:187, 690`, `Weak/AxScRun3.lean:152`).
2. **What does NOT exist (Rocq stopped here too; no Rocq source to port):** a positional
   `wpdAcquire` (spin induction + composition), a positional `wpdRelease` (the step-3 plan's
   `AxSpinRs/AxSpinRl*` were never written; `releaseWpd5`, `Weak/AxSpinCtl3.lean:605`, is the
   RETIRED surface-v4 replay with `wCret5`/`stackOwnSlots`/`Hdead`/`wBrTaken` λ-bound — do not
   close it, supersede it), the whole-segment composition, the row family, the real layout, the
   capstones and their certificates.  ≈ 11 new files, ≈ 6k lines (§D).
3. **Stage C + Option V do not make ownership vacuous against C.**  Every value pin concerns hart
   A/B's OWN control values: return addresses (reloads of its private slots), `noff`/`intena`
   (its private cpu fields), holding's results (`vlk`, `vcpu`), the spin count, the branch arms.
   None pins C's writes or the lock/nextpid DATA that C can affect, except the three Q18b pins on
   A/B's nextpid READ (`≠ 1000`, `Hnowrap`, `Hncoll`): these restrict WHICH executions are
   covered (C may legitimately drive nextpid to 1000 — then the theorem says nothing), they do not
   constrain C.  Certificates (a′)/(b) below satisfy them on both the positive and the race graph,
   so the statement is exercised, not vacuous.  Honesty line for the header: "Hrow + the Option V
   pins fix A's and B's control flow and addresses; the theorem proves nothing about a hart whose
   control flow or addresses are diverted or whose nextpid read hits 1000 / a collision; ownership
   is load-bearing for the DATA facts: pid distinctness and the nextpid read's source."
4. **FINDING on certificate (b) (plan: C = unlocked `lw; addiw; sw nextpid`).**  With the inlined
   collision scan the plan's racer cannot make `pid_A = pid_B` on a covered graph: if B's read
   returns A's pid, B's scan (ppo rule 5 after B's `.aq` claim, which is gmo-after A's release,
   which is gmo-after A's `p->pid` store) reads `p_A->pid = pid_A` ⇒ the collision branch ⇒
   `Hncoll` fails ⇒ the graph is outside the theorem.  Two sound retargets: (b-np) refute the
   `npSrc` conjunct of Φ_B (U4/J2 template `ur3WpdUnprovable`): C stores e.g. `5` to nextpid gmo-after
   B's claim, B's read sources it, no collision, `npSrc` false ⇒ C unprovable; (b-lk) C = unlocked
   `sw zero,0(&pid_lock)` (a bogus release while A holds the lock): B enters concurrently, both
   read nextpid = n0, B's scan of `p_A->pid` is gmo-before A's store ⇒ `pid_A = pid_B` with every
   A/B premise true ⇒ C unprovable (a WCplain 0-write to the lock word has no arm; only the WCrel
   release arm admits 0).  Recommend (b-np) as THE certificate (b) (mechanical) and (b-lk) as the
   stretch that refutes the distinctness conjunct itself.  Both have sanity twins at the trivial
   protocol (`ur3WpdTrivial` template).
5. **HAD / warm TLB.**  Under Stage C fetches are admin steps pinned to the boot image (Q8); Sv39
   walker reads ARE still graph events (`AxScRun3` rows contain them).  The theorem states WARM
   TLB at entry for every touched page (`hitW`, `dataAtS`, as every leaf demands) and read-only
   PTE pages (`Xlay.xlRo`) — the Lean form of HAD, a stated scope restriction (step-3 §6).  The
   certificate run warms up OUTSIDE the graph (a pre-run), then starts the graph run from the warm
   state: legitimate, `Hrun` takes any `s0` with `atK = 0`.
6. **`Hrun` for the certificates.**  `AxScRun3.jrun` already runs REAL S-mode xv6 code on several
   harts and emits rows + interleaving; `drive2` has the fence and fused-RMW arms; `runGraphOfSc`
   yields the `tierAAstep` premise; consistency and ctrl closure come from the generic lemmas
   (`scInputsOkB`, `ctrlOkB` by `decide +kernel`), not from deciding the graph.  COST: the Lean
   kernel runs ≈ 0.12 s per S-mode instruction (`Weak/AxSpinSpikeRun.lean:43-45`); one allocpid
   hart ≈ 230 instructions (≈ 133 graph events warm); (a′) = 3 harts ≈ 700 instructions ≈ 1.5 min
   per evaluation, and each `decide +kernel` re-evaluates the tracer (`AxScRun3`: "each check
   3–5 s, dominated by re-evaluating the tracer").  Mitigation (§E).
7. **Consistency for the certificate graphs:** `graphOfScCatT` (generic) — the plan's owner
   decision; no `rvwmoCatConsistentT` decision on 500-event graphs.
8. **Premise table of the proposed statement** (G = graph-true for correct lock code; O = holds
   only by ownership; P = Option V pin; cert = discharged by (a′)):

   | premise | source | status | cert |
   |---|---|---|---|
   | `HconsT : rvwmoCatConsistentT GT`, `Hcl : ctrlClosed GT` | plan Hcons/Hctrl_closed | model | `graphOfScCatT`, `graphOfScCtrlClosed` |
   | `Hharts : gmo harts ⊆ [A,B,C]` | plan | scope | decide |
   | `HL : xlayOk xlayXv6`, cid injectivity (`cpuAddr_inj`), slot disjointness | Hlayout | layout | decide |
   | `Himg`: lk->cpu = 0, lock = 0, nextpid = n0 (1 ≤ n0), `proc[j].pid` image ≠ candidates, text bytes (`textFixed`, `*Text σi T`) | Himg | image | `AxSpinTextCerts`-style |
   | `HrowA/HrowB : grow GD i ∈ allocFull i` (shape + value conditions `b hb n c`) | Hrow | G (row) | tracer rows |
   | Option V pins per hart (≈ 15: return reloads, `noff`/`intena` values, holding's `vlk`/`vcpu` arms, spin count) | Q20' | P (G by ownership in T2-cuts) | graph values |
   | Q18b pins: `≠ 1000`, `Hnowrap`, `Hncoll` | Q18b | P (scope) | graph values |
   | `Hentry_i`: pc = allocproc+0x38, sp, s1 = p_i, tp, SIE = 0, warm TLB | Hentry | scope | registers |
   | `Hrun_i`, `Hk0`, `Hend` (A, B, C) | adequacy | run | `runGraphOfSc` |
   | `HwpC : ∀ Hinv Hann nm, ⊢ xv6Init L GD nm C -∗ WPd_C {{True}}` at Ixv6 | plan | the ONLY iProp premise | (a′) C := allocpid; (b) refuted |

## B. The Lean statement

**Entry point (simplest honest).**  Start at `allocproc + 0x38` (`auipc a0,0x11` — the first
instruction of the inlined copy, `Weak/AxSpinAp.lean` header) with `s1 = p_i` (the proc slot
`allocproc`'s scan picked; a PREMISE, `p_A ≠ p_B`, both in `proc[]`), `sp` = allocproc's frame
(acquire/release spill BELOW it), `tp = cid_word_of i`, `SIE = 0`, warm TLB.  End at the boundary
after `allocproc + 0x98` `sw a5,24(s1)` (`p->state = USED`, a private 4-byte store) — the row's
TERMINAL item, needed because `XxRet` continues at `k` with `k < LEN` (`Weak/AxSpinE6.lean:308`):
release's `c.ret` needs a later memory event.  What is lost: allocproc's own scan/acquire of
`p->lock` and the caller context are outside the theorem; `p_i` is assumed, not derived.

**Row family** (`AxSpinT2a`): `allocSeg b hb n c (addrs) : List Ritem` =
`aqHead ++ poSh b ++ RowHolding hb ++ RowSpin n ++ aqTail` (= `RowAcquire`, `Weak/AxSpinAqr.lean:126`)
`++ apBodySh pnp ppid` (67, `Weak/AxSpinAp7.lean:114`) `++ relSh c` (new: 3 spills, `RowHolding true`,
`RS pcl 8`, fence item, `RSc plk 4 WCrel`, `ppSh c`, 3 reloads) `++ [RS (p_i+24) 4]`.
`allocFull i := { row | ∃ b hb n c, RowSh 0 row (allocSeg …) ∧ row.length = |allocSeg| ∧ lkBranch ×2 ∧
spinVals ∧ pop_off arm bits }`; `complete i := grow GD i ∈ allocFull i`.  Stage T2-core takes
`Hrow_i : complete i` outright (so the conclusion's `complete A → complete B →` is vacuous there —
state it anyway, for the T2-cuts upgrade).  The fence item needs `Ritem.RB`/`RSc` added to
`Weak/AxSpinPOr.lean:90` (ID-1).

**Ghost state / lock invariant** — unchanged from the port: `RPid L γh γm γi GD e` =
`(∃ vs, RVL (clb L) e vs) ∗ ∃ v, ⌜0 ≤ v < 2³²⌝ ∗ RVL (npb L) e (bytes v) ∗ ●mono v ∗ ∃ S, issuedAuth γi S
∗ ⌜S ⊆ [0,v)⌝` (`Weak/AxSpinX.lean:606-616`); `isLock nm.xnReg L.xlLk (RPid …)`; the exclusive
fragment `◯{v}` minted at the `sw nextpid` (`fxNpIncr`, `Weak/AxSpinX2.lean:1048`), read back as
`FRAG nm w` at `(i, k+65)` (`wpdAllocpidCs`'s continuation).  The 64-slot scan uses the
value-agnostic flow `FldMWScan` (Q18a); the `p->pid` store uses the PRIVATE write flow: put
`p_i + 48 .. + 52` (and `p_i + 24 .. + 28` for the terminal store) into `xlStk i`-style private
bytes of hart `i` (`priv`, `Weak/AxSpinX.lean:118`), so `Opid := FstM` built from `fxPrivWrite`
(`Weak/AxSpinX2.lean:888`) — a new small lemma `FstMPriv n` (Q18c: "flow is a premise" becomes
"flow is the private store flow").  C's scan reads of A's/B's slots are plain reads (no ownership
needed; writes are what the protocol gates).

**Layout** `xlayXv6 A B C pA pB stk cpuf : Xlay` with `xlHarts := [A,B,C]`, `xlLk := pid_lock`
(0x80012500), `xlNp := nextpid` (0x8000a384), `xlStk i` = stack slice ∪ `{p_i+24..27, p_i+48..51}`
for i ∈ {A,B} (C's private set is whatever the instance needs — empty is fine, no `L3`/`Lx` bridge),
`xlCpuf i` = `cpus[i].noff/intena`, `xlRo` = kernel text ∪ PTE pages, `xlText` = the lock text.
Everything else (incl. `proc[j].pid` for j ∉ {p_A,p_B}) is BLOCKED — so a verified C never writes
them and the scan values are image values (which is why `Hncoll` is true in (a′)).

**Per-hart posts.**  `Φ Hinv Hann nm i s := ⌜¬ midState s⌝ -∗ ∃ w, ⌜pidOf GD i = some w ∧
gprVal (regs s) 13 = sext32 w ∧ npSrc GD L (rd_i) (claim_i)⌝ ∗ FRAG nm w` for i ∈ {A,B}, where
`pidOf GD i := graphData GD (i, kpid_i)` (the `p->pid` store's data, position from the family) and
`npSrc` is read back from the `(i,k)` annotation; `Φ C := True`.  The `⌜¬ midState⌝ -∗` guard
(`midState`, `Weak/AxSymEngine3.lean:292`) makes every leaf's `HΨmid` free, as ID-8 prescribes.
`a3` survives release (no callee writes it; the CPS "other GPRs kept" clauses prove it) — this is
Rocq's `a0 (σf i)` here.

**Hjoint** (template `AxSpinJ2.jointAB`, `Weak/AxSpinJ2.lean:212`): `Φ A ∗ Φ B ∗ Φ C ==∗ ⌜wA ≠ wB⌝`
by `issuedFragExcl` (two fragments at one `nm.xnI` with equal words ⇒ equal `v` ⇒ `False`).

**THEOREM 2 (`allocpidOpen`, Lean shape):**
```
theorem allocpidOpen (GT : GdexecT) (A B C : Agent) (pA pB : Int) (n0 : Int) …
  (HconsT) (Hcl) (Hharts : ∀ e ∈ gmo, e.1 ∈ [A,B,C]) (HL : xlayOk (xlayXv6 …)) (Hdistinct …)
  (Himg …) (σi T satp0) (hmode hasid hppn) (Htxt : lockText σi T ∧ allocpidText σi T) (Hfix …)
  (HrowA : complete A) (HrowB : complete B) (HpinsA HpinsB : allocPins GT i …)      -- Option V + Q18b
  (s0 sN : Agent → Athread) (n : Agent → Nat) (Hentry : ∀ i ∈ [A,B], entryOk (s0 i) …)
  (Hrun : ∀ Hann nm i, i ∈ [A,B,C] → nsteps (tierAAstep (gtAdGd GT) nm i) (n i) (s0 i) (sN i))
  (Hk0) (Hend)
  (HwpC : ∀ [Hinv] [Hann] (nm), ⊢ xv6Init L (gtAdGd GT) nm C -∗
           tierAWpd … (protXv6 L) nm (s0 C) .MaybeStuck C (fun _ => True)) :
  (∀ i ∈ [A,B], npSrc (gtAdGd GT).gdG L (rd i) (claim i)) ∧
  (complete A → complete B →
     ∃ wA wB, pidOf A = some (wbytes 4 wA) ∧ pidOf B = some (wbytes 4 wB) ∧
       gprVal (regs (sN A)) 13 = sext32 wA ∧ gprVal (regs (sN B)) 13 = sext32 wB ∧ wA ≠ wB)
```
**THEOREM 1 (`allocpid2Distinct`) as a corollary:** `Hharts ⊆ [A,B]`, `C` any fresh agent with
`grow GD C = []`, `n C = 0`, `s0 C = sN C` at `atK = 0`, `HwpC` := the WPd of a hart at its row end
with post `True` (provable from `postLifting` of `True`; `Weak/AxTierA.lean` idiom) — S.  Rocq's
"no panic" conjunct appears in both as the pinned branch arms (T2-core) and becomes a theorem in
T2-cuts.

## C. Proof architecture

1. **acquire WPd** (new `AxSpinAq1/Aq2`).  `wpdSpin j n`: ordinary induction on `n − j` over
   `RowSpin`/`spinVals` (`Weak/AxSpinAqr.lean:103-108`, stride 1): iteration = `XxReg` (c.mv a5,a4),
   `XxAmoswap` with `FstAcqNh … (OAcq LK RP) kA (kA+1)` (`Weak/AxSpinAm3/Am4`), `XxReg` (sext.w),
   `XxReg` (c.bnez: the direction is `aqFail vs` of the RMW's pinned graph value, `spinVals` says
   it fails iff `j < n` — no new pin); failure hands `NH i` back, the claim yields
   `(i,kA) ↦ₐ LK ∗ (i,kA) ↦ₐ RP`, split by `wpdAnnotSplit` (`Weak/AxSpinH5.lean:104`) into `RCPU`/`RNP`.
   Composition: `XxSt` ×3 (spills at k..k+2) → `wpdPushOff` at k+3 (`poSh b`, cont. `aqKp`) → `XxReg`
   (c.mv a0,s1) → `holdingFromAcquire'` at `aqKp` (`hb`; `ORacy` at `aqKp+4` deposits `rdFact`; the
   non-panic arm pinned: `hb → vcpu ≠ cpuAddr i`, i.e. `a0 = 0`) → `XxReg` ×2 (c.li, c.bnez not
   taken) → `wpdSpin 0 n` → `wpdMycpu` at `aqKm` → `XxSdCpu` (c.sd a0,16(s1): 8-byte owned store via
   `fxCpuWrite`, `RCPU` from the claim, value `cpuAddr i`; shared with release) → `XxLd` ×3 → `XxRet`
   (pin: ra reload value = allocproc+0x44).  Register-only instructions are `XxReg` with the
   `atok*` text facts of `AxSpinAq/Aqd/Aqt1/Aqt2`.
2. **release WPd** (new `AxSpinRl1..4`) — the simplest sound alternative to closing `releaseWpd5`'s
   λ-bound slots is to NOT close them: the positional route has no `w_cret`/`w_hold`/`w_pop`
   slots (the row position of the next memory event replaces them — plan "PHASE 5 ROUTE CHANGE").
   D3's address gate disappears too: `s1` is reloaded from a PRIVATE slot (`XxLd`, value = spill by
   `RLfact`), and under Option V the store base is pinned by the row (`RS pcl 8` at the shape
   position; the reload's graph value = `p_i`-independent `&pid_lock` is a pin like `Hval`).
   Pieces: `XxSt` ×3 → `holdingFromRelease'` (`kc` = the claim, `nolk`, `OHeld` ⇒ `locked ∗ ⌜≠0⌝` at
   the lw; pin: `vcpu = cpuAddr i` so the `c.beqz a0,panic` falls) → `XxSdCpu` (value 0, draws the
   `lk->cpu` handle from acquire's sd via `OOwn`/forwarded case) → `XxFence` (new: 1-item leaf on
   `AxCert2.wpdFenceNodeM`, `Weak/AxCert2.lean:337`; no flow resource) → `XxSwRel` (new: 4-byte
   WCrel store leaf whose `FstM` is `fxReleasePid` (`Weak/AxSpinX2.lean:567`) at anchors `RCPU` =
   acquire's/release's lk->cpu store, `RNP` = `(i, k+65)`, `locked` from `OHeld`; `gob`/`lobp`
   through the fence by `fenceGob`/`fenceLobp` (`Weak/AxSpinProt3.lean:389`, `AxSpinProt5.lean:112`)
   — the positional twin of `wpdReleaseX`, `Weak/AxSpinU.lean:1275`) → `wpdPopOff` (`ppSh c`) →
   `XxLd` ×3 → `XxRet`.  Deposits `(i, kw) ↦ₐ NH i` (unused by the theorem).
3. **Whole segment** (new `AxSpinApA.wpdAllocpidSeg`): `XxReg` ×2 (auipc/addi a0) + jal (`XxReg`
   with link) → `wpdAcquire` → `wpdAllocpidCs` (`Weak/AxSpinAp9.lean:503`; anchor `e := (i, aqKA)`
   with `e ∈ lobp (i,k)` by `acqGob` (`Weak/AxSpinProt3.lean:379`) + ppo rule 5; `Opid := FstMPriv 4`)
   → `XxReg` ×3 → `wpdRelease` → `XxStF` (terminal `sw a5,24(s1)`, private) → `Φ`.  All text facts
   are `allocpidTextOf`/`acquireTextOf`/… (`Weak/AxSpinTextCerts.lean`) — satisfiable since Q22.
4. **Joint adequacy**: `tierAAdequacyAnnGateJointT` at `GF := AxSpinX7.xv6GF`, `obStInterp0 :=
   protXv6 L`, `init := xv6Init L`, `HobAlloc := xv6HobAlloc L` (needs `xlayOk` + image premises),
   `Hok := xv6Hok GT HconsT Hcl` (`Weak/AxSpinX.lean:765`; generic over all harts, C included — no
   per-hart policy), `Hwp` = `[∗list]` over `[A,B,C]` of `wpdAllocpidSeg` ×2 and `HwpC`
   (`AxSpinJ2.uAllocOpen`'s script, `Weak/AxSpinJ2.lean:361-470`, is the template).
5. **Distinctness**: ghost exclusivity (`issuedFragExcl`), NOT the graph dichotomy — position-
   independent, works with an arbitrary C (ID-10; `uAlloc2Joint` precedent).  The `npSrc`
   conjunct is read back from the `(i,k)` annotation at the row end (`postLifting`).
6. **Certificates**: (a′) `AxSpinT2c`: C := the same segment on slot `p_C`; serial schedule
   A, B, C (nextpid 1→2→3→4; scans see 0/1/2, candidates 1/2/3 — `Hncoll` holds); rows from a
   warm-started `jrun`, graph `graphOfSc`, `drive2` per hart, premises by `decide +kernel`;
   conclusion checked.  (b) `AxSpinT2d`: (b-np) racer `lw;addiw;sw nextpid` landing gmo-after
   B's claim, B's read sources it ⇒ `npSrc` false ⇒ `HwpC` unprovable (reductio through
   `allocpidOpen`, `ur3WpdUnprovable` template); (b-lk) stretch, §A.4.  (c′) the same racer at the
   trivial `axGA2` instance (`ur3WpdTrivial` template).  (d) `tools/ci/lint.sh` already bans
   `sorry`/`axiom`/`native_decide`; add `allocpidOpen` to `tools/audit/baseline.json` so
   `tools/audit/Audit.lean` prints its axioms (expected: `propext`, `Classical.choice`, `Quot.sound`
   + `bv_decide` certs); grep the final theorem's binders for `IProp` — only `HwpC` may remain.

## D. Work plan

| file | content | est. | size |
|---|---|---|---|
| `AxSpinRl1` | `Ritem.RB/RSc` (+ `ishape` arms, `RowSh` lemmas), `relSh c`, `relK*` positions, `rowClsHonest` (ID-6) | 200 | S |
| `AxSpinRl2` | `XxFence` (on `wpdFenceNodeM`), `XxSdCpu` (8-byte owned lk->cpu store, value generic; reuse `XxStF` + `fxCpuWrite`) | 450 | M |
| `AxSpinRl3` | `FstRel` (positional `fxReleasePid` via `fenceGob`/`fenceLobp`), `XxSwRel` (WCrel 4-byte store leaf) | 500 | M |
| `AxSpinRl4` | `wpdRelease` composition (pins: `vcpu = cpuAddr i`, two reload returns, pop_off's) | 900 | L |
| `AxSpinAq1` | `wpdSpin` induction (`XxAmoswap` + `FstAcqNh` + `XxReg`), `wpdAnnotSplit` of the claim | 450 | M |
| `AxSpinAq2` | `wpdAcquire` composition (`XxSdCpu` imported from Rl2 or duplicated) | 900 | L |
| `AxSpinApA` | `FstMPriv n`, `wpdAllocpidSeg` (allocproc+0x38..+0x98) | 700 | L |
| `AxSpinT2a` | `xlayXv6`, `allocSeg`/`allocFull`/`complete`/`pidOf`, `allocPins`, `Φ`, `Hjoint`, `entryOk` | 450 | M |
| `AxSpinT2b` | `allocpidOpen`, `allocpid2Distinct` (corollary), headers with the honesty text | 550 | M |
| `AxSpinT2c` | (a′): 3-hart warm tracer run, `graphOfSc`, `drive2`, every premise, conclusion true; (a-) optional spinning-B prefix witness | 500 + compute | L |
| `AxSpinT2d` | (b-np) race, (c′) sanity twin, [(b-lk) stretch]; (d) audit root | 500 | M |

DAG: `Rl1 → Rl2 → Rl3 → Rl4`; `Aq1 → Aq2` (needs `XxSdCpu`: take it from Rl2 or write a local
copy); `T2a` independent (needs only `Rl1`'s shape); `ApA ← Aq2 ∧ Rl4 ∧ T2a`; `T2b ← ApA`;
`T2c` splits: rows/graph/run computation ← `T2a` (start early; premise discharge ← `T2b`);
`T2d ← T2b`.  **Parallel lanes (Opus workers, one file each, own `jj workspace`):** lane R
(Rl1→Rl2→Rl3→Rl4), lane A (Aq1→Aq2), lane L (T2a, then T2c's tracer half), then ApA, then T2b ∥
T2c-discharge, then T2d.  **Critical path:** Rl1→Rl2→Rl3→Rl4→ApA→T2b→T2d (7 files, ≈ 4k lines).
**Acceptance checks:** (i) `AxSpinT2c` type-checks with `allocpidOpen` APPLIED (every premise
discharged, conclusion with concrete `wA ≠ wB`); (ii) `ur`-style (b) and (c′) both present (the
protocol, not the framework, refuses C); (iii) `grep -n "^variable (w\|λ-bound\|STILL λ" Weak/AxSpinT2*.lean
Weak/AxSpinApA.lean Weak/AxSpinAq*.lean Weak/AxSpinRl*.lean` empty; the capstone's only iProp
hypothesis is `HwpC`; (iv) `tools/audit` prints the expected axiom set; (v) `lake build` of the new
files within the VM budget (`T2c` ≤ 20 min).

## E. Risks and owner questions (recommended option first)

- **Q-T2-1 Two-stage landing.** (Rec) T2-core proves distinctness + `npSrc` on complete rows with
  the panic arms PINNED (Option V premises, honest header); T2-cuts (ID-8 `RowShP`/`Des`/P-twins,
  ≈ 5 files, L) later proves conjunct 1 by D4 readback.  Alt: do T2-cuts first (delays the headline
  by weeks).
- **Q-T2-2 Entry/exit.** (Rec) entry `allocproc+0x38` with `s1 = p_i` a premise, exit after
  `+0x98`'s `sw a5,24(s1)` (terminal row item).  Alt: start at `jal acquire` (+0x40) — saves two
  `XxReg`s, nothing else.
- **Q-T2-3 Certificate (b) retarget** (finding §A.4: the collision scan defends the pids against
  the plan's nextpid racer on covered graphs).  (Rec) (b-np) refutes `npSrc` (J2 template), (b-lk)
  bogus-release racer as the stretch that falsifies `wA ≠ wB` itself.  Alt: drop `Hncoll` from the
  statement by adding the collision-retry row family (M-L; also removes a Q18b pin).
- **Q-T2-4 `p->pid` class.** (Rec) private bytes of hart `i` in `xlayXv6` (`fxPrivWrite` flow;
  `Opid` discharged).  Alt: keep `Opid` as a premise of the capstone (leaves an iProp-shaped hole
  — fails (d)).
- **Q-T2-5 Q18b pins in a headline theorem.** (Rec) accept `≠ 1000`/`Hnowrap`/`Hncoll` as scope
  pins, stated verbatim in the header ("a verified C may raise nextpid to 1000; such executions
  are not covered").  They are satisfiable on (a′) and on both races.
- **Q-T2-6 Tracer cost.** 0.12 s/instruction in the Lean kernel; (a′) ≈ 700 instructions.  (Rec)
  evaluate `jrun` ONCE per file into literal rows/interleaving (`#kernel_eval` → paste; one
  `decide +kernel` ties the literal to `jrun`), run the remaining checks on the literals; keep
  `T2c` at ≤ 20 min.  Alt: accept re-evaluation per check (hours).  Risk M.
- **Q-T2-7 `ctrlOkB` on ≈ 500-event emissions** (Rocq: 16–36 s; Lean kernel slower).  (Rec) run
  the spike (`AxSpinSpike` counts, `g40CatT` style) on one real row before T2c; fall back to
  per-hart emission checks if quadratic blow-up shows.  Risk M.
- **Q-T2-8 Page table for the certificate.**  `AxSpinE8f.tT` covers pages 0x80000/0x80001 only;
  T2c needs pid_lock/nextpid/proc/cpus/stack pages with A/D preset.  (Rec) build `tXv6 : PTree`
  from the kvmmake-faithful identity map (A/D-preset variant referenced in `AxDataX8`/`AxWalk4`;
  verify it exists, else S new).  Risk S.
- **Q-T2-9 `XxSdCpu` ownership.**  Release's `sd zero,16(s1)` must draw the `lk->cpu` handle from
  acquire's `c.sd a0,16(s1)` — positions are 100+ items apart; the handle's anchor is the claim
  (`RCPU` at `aqKA`, rule 5) so the window premise is a row fact ("no other lk->cpu write between").
  (Rec) state it as a row premise derived from `allocSeg` (true: only the two sds write `clb`).
- **Q-T2-10 Superseding `releaseWpd5`.** (Rec) mark `AxSpinCtl3`/`AxRelease4`/`AxSpinRow3`
  `releaseWpd6` headers SUPERSEDED (the plan's route change); their λ-bound slots are not closed
  and are not on the path to Theorem 2.
- **Q-T2-11 Theorem 1 form.** (Rec) corollary of Theorem 2 with an empty-row C (one trivial WPd);
  Alt: a separate 2-hart statement via `tierAAdequacyAnnGateJointT` at `[A,B]` (S, but duplicates
  the capstone).
- **Risk: `jrun` and warm start.**  The tracer currently starts cold (`AxScRun3`); a warm-up
  pre-run needs the tracer to carry the TLB state across the boundary — `AxSpinSpikeRun`'s runner
  already carries the state, so this is plumbing (S), but if the warm-up itself must be a graph
  prefix the family gains walker items (avoid).
- **Risk: heartbeats.**  `wpdAllocpidCs` needed `maxHeartbeats 1600000`; the segment composition
  will be heavier — split `ApA` at the acquire/CS/release seams if a single theorem times out.
