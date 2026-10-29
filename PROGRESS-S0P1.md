# PROGRESS — S0-P parts (1) + (5): reference checker core + litmus oracle

Worker: Opus (S0P1). Workspace `/home/bsdinis/dev/xv6iris-pcsl2`. Plan of record rev 7 (§5, §6, §8 S0-P/S1).

## K1 — STOPPED AT A GREEN POINT (oracle vs repository herd results)

All 76 §5-row verdicts equal Table S's text verdicts (and the repo's herd result wherever §20 names a test): no K1
from the rows.  The ORACLE RUN over `tests/non-mixed-size` (budget ≤ 8 memory instructions: 7551 of 7907 files compared)
found 615 disagreements with `model-results/herd.logs`, from THREE root causes, each re-read against the files and
the text.  None is resolved here; (b) and (c) need a ruling, (a) needs a decision on what the litmus mnemonic
denotes.  Raw outputs: `~/dev/weak-orch/promising/litmus/oracle-cap6.txt` (and the cap-8 runs, `oracle-cap8-both.txt`,
final: budget 8, both conventions).

**(K1-a) 610 tests — litmus `lw.aq` / `sw.rl` (`ld.aq`, `sd.rl`): herd RCpc, the manual RCsc.**
- Tests: `RELAX/{PodWRRlAq,PosWRRlAq,PodWRPAq,PodWRRlP,PosWRPAq,PosWRRlP,PodWR,Rfi,PosWR}/*`, `RelAcq_2_THREAD/
  {SB+porlaqs, R+poprl+porlaq, R+porlrl+porlaq}`; all herd `Sometimes`, reference `Never`; every one has an
  `s*.rl` po-before an `l*.aq` (checked file-wise).
- Example `RelAcq_2_THREAD/SB+porlaqs`: `sw.rl x5,0(x6); lw.aq x7,0(x8)` ‖ symmetric, `exists (0:x7=0 /\ 1:x7=0)`.
- The manual: Zalasr (`s0t/fetched-S/manual-e17d92a1/unpriv_zalasr.adoc:68–69` "The instruction always has an
  acquire-RCsc annotation", `:122–123` "The instruction always has a release-RCsc annotation"), so rule 7
  (rvwmo.adoc:289 "a and b both have RCsc annotations") orders `sw.rl` before `lw.aq` ⇒ SB+porlaqs FORBIDDEN.
  herd's verdicts are those of RCpc annotations (the pre-Zalasr litmus convention; rvwmo.adoc:150–153 "the ISA
  does not currently contain native RCpc load-acquire or store-release instructions").
- Evidence run: the same corpus with the mnemonics read as RCpc (`Instr.loadAqPc`/`storeRlPc`, oracle-only, flag
  `rcpc`): ALL 610 then agree (7546 agree, 5 disagree = exactly K1-b + K1-c).
- Decision needed (coordinator/owner): the reference follows the manual (Zalasr = RCsc) — no change proposed.
  Question is only how the oracle treats these 610 tests: (i) as expected disagreements (herd's logs predate
  Zalasr), or (ii) compare them under the RCpc reading (then they test the RCpc rules 5–6 only).

**(K1-b) 3 tests — SC to an address other than its LR's: herd forces failure, the manual permits success.**
- `HAND/SC-FAIL` (`lr.w x7,0(x2); sc.w x8,x6,0(x3)`, x≠y, `forall (y=0 /\ 0:x8=1)`): herd `Always`, reference
  `Sometimes`.  `HAND/LR-SC-diff-loc1` (two harts, `lr.w (x); sc.w (y)` / `lr.w (x); sc.w (z)`, both succeed):
  herd `Never`, reference `Sometimes`; `HAND/LR-SC-diff-loc2` (same, with an MP-like exchange between the pairs):
  herd `Never`, reference `Sometimes`.
- The manual: zalrsc.adoc:91–93 "An implementation can register an arbitrarily large reservation set on each lr,
  provided the reservation set includes all bytes of the addressed data word or doubleword"; :99–101 "Note this lr
  might have had a different effective address and data size, but reserved the sc's address as part of the
  reservation set"; rvwmo.adoc:340–342 "The Atomicity Axiom theoretically supports lr/sc pairs of different widths
  and to mismatched addresses, since implementations are permitted to allow sc operations to succeed in such
  cases".  Plan §6 [R2.2] mandates exactly this ("pairing is by program order alone … with no address or width
  match"), and Table S row 35d's text verdict is ALLOWED for the same pattern.  herd is STRONGER than the text.
- No change proposed; needs acknowledgement that the repository is not an oracle for mismatched LR/SC.

**(K1-c) 2 tests — rule 13 through a FAILED SC (reading R-13).**
- `HAND/LB+addr+addrpx-poxp+VAR`, `…+VAR2`: P1 `lw x5,0(x6); xor x7,x5,x5; add x9,x8,x7; ori x10,x0,1;
  sc.w x11,x10,0(x9)` (no LR: the SC always fails, herd's states show `1:x11=1`) `; ori x12,x0,1; sw x12,0(x13)`,
  `exists (0:x5=1 /\ 1:x5=1)`: herd `Sometimes`, reference `Never`.
- Why: rule 13 (rvwmo.adoc:301–302) "b is a store, and there exists some instruction m between a and b in program
  order such that m has an address dependency on a".  This draft reads "instruction m" literally, so the failed SC
  (an instruction whose address source `rs1` depends on `lw x5`) orders `lw x5` before `sw x12` ⇒ LB cycle.
  herd's `r13 = [R];addr;[M];po;[W]` ranges over memory EVENTS; a failed SC has none ("An unsuccessful sc
  instruction does not give rise to any memory operations", rvwmo.adoc:82), so no edge.
- The text is ambiguous: "syntactic address dependency" is defined between MEMORY OPERATIONS (rvwmo.adoc:226–234: "let a and b be two memory operations, and let i and j be the instructions that generate a and b"),
  but rule 13 says "instruction m"; the explanatory note (mm-explanatory.adoc:1063–1065 "a store generally cannot
  be performed until it is known that preceding instructions will not cause an exception due to failed address
  resolution") supports the literal reading (a failed SC still resolves its address: zalrsc.adoc:17 "No sc.w
  instruction shall retire unless it passes memory permission checks").
- Options: (A) literal reading (current; STRONGER than herd); (B) memory-operation reading (= herd; WEAKER than
  (A)).  One-line change in `rule13` (`Weak/Prom/Ref.lean`): restrict `m` to `Kind.isMem`.  Not taken here.

## Done (green)

- `Weak/Prom/Ref.lean` — `rvwmoRef` at execution level: events with skeletons (kind, dynamic instruction index,
  size, RCpc/RCsc annotations, syntactic deps), byte-wise rf derived from gmo (`rfSrc` = the load value axiom's
  store), ppo rules 1–13 (rule 6, 7-RCsc, 8 present; aq/rl same-class only = F-S3 fix), I/O rules (2)–(5),
  load value / atomicity (LR's bytes, mismatched pairs) / §zalrsc success conditions (existential reservation set,
  decided via the minimal one, `resvOkB_iff`) / progress (literal, proved for finite executions, `progressFin`).
  Reflective checker `refCoreB` (sound + complete for `rvwmoRef`).
- `Weak/Prom/RefProg.lean` — litmus ISA (RV64I subset, Zalrsc, Zaamo, Zalasr `l*.aq`/`s*.rl` (RCsc), FENCE,
  FENCE.TSO = `fence r,rw` + `fence w,w` at one instruction index, `fence.i` (data no-op), `csrr` of an unwritten
  CSR), symbolic per-path interpreter with taint = syntactic dependencies (failed SC's `rd` not a destination,
  † no carry for memory instructions), `progExec` / `allowedRef` / `forbiddenRef`.
- `Weak/Prom/RefCheck.lean` — enumerator: paths × gmo linearisations (pruned by the value-independent ppo rules
  4–11, 13) × load values COMPUTED by one pass along gmo (no rf enumeration).  Proved: `forbid_sound`
  (`forbidB T = true → forbiddenRef T`, i.e. enumerator completeness incl. `pass_correct`), `exists_sound`,
  `probe_sound`.  `#print axioms` on end-to-end verdicts: propext, Classical.choice, Quot.sound only.
- `Weak/Prom/RefTests.lean` (tests) + `Weak/Prom/RefLitmus.lean` (rows 1–25) + `Weak/Prom/RefLitmus2.lean`
  (rows 26a–i, 28, 28c, 29–32, 31b, 35a–d, 36, 37, 41, 52–61, probe IO-AQ / F-S3): 77 `ref_<test>` theorems by
  `decide +kernel` (whole build < 1 min), each FORBIDDEN row with a non-vacuity theorem `ref_<test>_exec`.
  EVERY verdict equals Table S's text verdict (and the repo's herd result where §20 names a test).
- `Weak/Prom/LitmusParse.lean` (parser) + `Weak/Prom/LitmusOracle.lean` (run as `lake env lean --run …`): the
  corpus is fetched on the VM into `.lake/litmus/repo` (not committed; herd.logs sha256 e3452bfa… = Table S's copy).
  The 31 hand-written rows that name a repository test are STRUCTURALLY EQUAL to the parsed files (checked by the
  run).
- Deferred (translation, [OWN.P3]): rows 33, 34, 39, 40, 40b, 42–51.  Row 38 is a logic target (no verdict).
  Row 27 (G4) is S4.

## Oracle summary (budget ≤ 8 memory instructions; `~/dev/weak-orch/promising/litmus/oracle-cap8-both.txt`)

- RCsc (the manual): files 7907; compared 7551: agree 6936 (Never 4275, Sometimes 2654, Always 7), disagree 615
  (K1-a 610, K1-b 3, K1-c 2).
- RCpc (herd's convention for `l*.aq`/`s*.rl`): agree 7546, disagree 5 (K1-b 3, K1-c 2).
- Both: parse-out-of-scope 19 (`filter` clauses 8, `&z` pointer inits 6, no init block 2, backward branch 1,
  unsupported 2 incl. `jalr`); no herd result 318 (names absent from herd.logs); over budget 19 (9 memory
  instructions).  Run time ≈ 75 min per convention, single-threaded interpreter on the VM.

## Decisions / readings (none is an owner question unless listed under K1)

- R-IO: rules 1–4, 8–13 relate RAM–I/O pairs; rules 5–7 same-class only (mm-explanatory.adoc:1149–1153 — the
  explicit aq/rl exception implies the others apply).  rf-based rules 2, 3, 12 only for RAM loads.
- R-13: see K1-c.
- R-AT: the atomicity axiom quantifies over actual stores (`rfSrc = some s`); the initial-value case is covered by
  §zalrsc's success condition (equivalent).
- R-SCF: a failed SC writes `rd := 1` (zalrsc.adoc:62–63 "value 1 encodes an unspecified failure. Other failure
  codes are reserved"); its `rd` is not a dependency destination (listing :589 "if successful").
- Zalasr `l*.aq`/`s*.rl` = RCsc (unpriv_zalasr.adoc:68–69, :122–123).  See K1-a for the repository.
- Front-end scope (`condsOk`): aligned accesses only (misaligned decomposition is in `Ref.lean`'s execution model,
  not generated by the litmus front end; NA-9/F-S1/SA-1 open).  The enumerator needs `io = []` (I/O load values
  are free); I/O executions are checked by `probe_sound` witnesses (IO-AQ).

## Open items

- K1 a/b/c above.
- Not done: CMO events (machine v2 has them), device agents, misaligned decomposition in the front end, `filter`
  clauses and `&loc` inits in the parser.
