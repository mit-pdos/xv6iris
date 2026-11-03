# PROGRESS — S0-P rest: parts (3) decoder check, (4) probe generator, (6) calibration + reports

Worker: Opus (S0rest), 2026-11-03. Workspace `/home/bsdinis/dev/xv6iris-pcsl3`. Plan of record rev 7 (§1A, §8 S0-P,
Appendix A/B). Brief: `~/dev/weak-orch/promising/S0rest_prompt.txt`.

## Fixes to Machine.lean / Emit.lean (record)

**S0rest-F1 — FIXED (Emit.lean + its executable mirror MachSail.lean `sNext`). A CSR read-modify-write's `rd`
took the NEW CSR view (STRONGER, new root cause beyond SR-1…SR-31).**
- Found by: G2 CARRY probes of `csrrw/csrrs/csrrc x5,csr,x6` on all 21 writable TABLE CSRs (63 probes,
  text ALLOWED, machine FORBIDDEN), e.g. H0 `ld a0,(x); xor s,a0,a0; add x6,x6,s; csrrw x5,mscratch,x6;
  xor t,x5,x5; ori t,t,1; sd t,(y)` ‖ H1 `ld b,(y); …; sd u,(x)`, outcome a0 = b = 1.
- Cause: Sail writes the CSR before `rd` (`csr_val ← read; write_CSR; X(rd) := csr_val`), and `rd`'s source
  `[p]` (`depsRd2`) was evaluated after `LRegW p [rs1, …]`, so `rd` inherited `rs1`'s view.
- Spec: rvwmo.adoc:487–495 (csrrw‡ "carries a dependency from rs1 to csr and from csr to rd"; csrrs/c‡ "from csr
  and rs1 to csr and from csr to rd"): `rd` depends on the CSR's previous writer, not on `rs1`.
- Fix: `Emit.csrCapture` — at the FIRST read of the CSR's register by such an instruction (with `rd ≠ x0`) the
  instance emits `LRegW 53 [p]` (`csrOldKey`, a fresh dependency key: the old CSR's view) instead of `LSilent`;
  `regSrcs` gives `rd` the source `[DReg 53]` (`v2Rd2`); new `Ix.csrOld` flag.  `MachSail.sNext`'s `regRead` arm
  mirrors it; DecoderTable `v2Old` maps key 53 back to the CSR for the listing comparison.  Mark: FAITHFUL.
- Regression after the fix: decoder check unchanged (`v2_no_stronger`, `v2_weaker`, `v2_inert` re-proved); G2
  CSR STRONGER 63 → 0; every Sail-level family unchanged-or-eq (G1 42624/42624 eq, ROW, G1w, G1b, G1lxs, G3, G5,
  TS); corpus: `MachOracle` (label level, cap 99, noref) 7876 eq herd, 9 na, 3 = the known appendix-bug tests
  (= `machine-cap99-noref-D3.txt`); `MachSailOracle` (cap 99, noref) Sail = label on all 4086 Sail-scope tests,
  4075 eq herd, 2 appendix-bug, 9 na (= `sail-cap99-noref.txt`).  Raw: `~/dev/weak-orch/promising/litmus/s0rest/`.
- Also present in TODAY's emission (`erwOf`'s `erwSrcs [p] rds` at the `rd` write): unseeded; not visible to
  today's deciders (no Sail-level today's driver).

## (3) DECODER CHECK — GREEN (2026-11-03)

Files (new, under Weak/Prom/): `DecoderTable.lean` (class table + expected roles from the listing),
`DecoderSail.lean` (driver: every class through the Sail model, both emissions' classification; generates
`DecoderObs.lean`), `DecoderCheck.lean` (kernel `decide +kernel` verdicts), `DecoderReport.lean` (readable report).

- 1041 classes (all 122 `instruction` constructors' encoding classes incl. aq/rl, widths, CSR splits over 24 table
  CSRs and 17 outside, taken/not-taken branches, SC success / Sail-level failure / memory-level failure); Sail's
  decoder confirms every word's constructor (Zbb/Zba/Zbs-only and `c.sext.*`/`c.zext.h/w` decode ILLEGAL and trap;
  Zbkb-shared `andn`/`rol`/`rev8` DO decode — Table C row C-D-26 said unreachable; roles are `ORalu`, D-ok).
- **Emission v2: NO STRONGER mismatch** (`v2_no_stronger`, `v2_trap_no_stronger`); 27 INERT (F5' load/LR `rd ← rs1`,
  `inertF5`; read-only CSR keys, `inertRO`); WEAKER classes (`v2_weaker`), root causes:
  W1 CSRs outside `csrReg`'s table are untracked (C-D-24); W2 `amocas` `rd^D` (and `.q` pairs) missing data
  sources (C-D-13); W3 Zcb loads/stores/ALU and Zimop/Zicfiss mop forms are `ORnone` (address/data/carry lost;
  `rd` written `LRegW rd []`); W4 `cbo.zero` address source (C-D-17); W5 a failed SC's `rd` is reset (`[]`) where
  the text keeps its old dependency; W6 non-destination side-effect writes reset a key: `mret`/`sret` `mstatus`,
  `stimecmp` → `mip`, `pmpcfg2`/`pmpaddr5` → the shared `PMPCFG0`/`PMPADDR0` key (vector aliasing, C-R-8).
- Annotations + label constructor per access kind (`annot_v2`, kernel-evaluated through Sail's own
  `read_kind_of_flags`/`write_kind_of_flags`/`read_ram`/`write_ram`; `rdTag_spec`/`wrTag_spec` tie the tag functions
  to `Emit.ramRead`/`ramWrite`): FAITHFUL for LR/SC/AMO/plain × all `(aq, rl)`.
- `obs_v2_eq` / `obs_today_eq`: the pure projections equal the Sail run's classification for every class.
- Finding (INERT): Emit's FC-5 `trapped` heuristic (`r = .mcause ∨ r = .scause`) also fires on a plain
  `csrw mcause/scause`; only read at an SC / `amocas` / Zicbom boundary, so it changes nothing. `MachSail.sNext`
  stops such programs ("trap") — a Sail-level scope gap only.

Today's emission (calibration, decider `decide`): `cal_SR11_dec6`, `cal_SR11_dec7`, `cal_SR19`, `cal_SR9_rd`,
`cal_SR20` all rediscovered (see the calibration table below); `annot_today`.

## (4) PROBE GENERATOR — GREEN (2026-11-03)

Files: `ProbeGen.lean` (G1, G1w, G1lxs, G1b, G3, G5, TS, ROW), `ProbeRun.lean` (runner: reference = RefCheck
enumerator; v2 label level; v2 THROUGH SAIL; TODAY's machine; FULL outcome sets on the probe's observables, text
verdicts on the designated outcome), `ProbeG2.lean` (G2, Sail level), `CalibToday.lean` (today's machine).
Run: `lake env lean --run Weak/Prom/ProbeRun.lean <fam> <shard> <shards> [nosail] [notoday] [noref]`,
`… ProbeG2.lean <shard> <shards>`; 90 shards on the VM; whole matrix ≈ 4 min wall (today's G1 ≈ 10 min).
Raw outputs: `~/dev/weak-orch/promising/litmus/s0rest/` (`res-*.txt` = final v2 run after F1; `today-res-G1.txt`,
`today-prefix-res-*.txt` = today's machine columns; `decoder-report.txt`).

Counts and results ON v2 (after F1; MR = label level vs reference, SR = Sail level vs reference):
| family | probes | MR | SR | notes |
|---|---|---|---|---|
| G1 | 55298 (+4 drop classes: 3823 cells logged by `g1Drops`) | 55298 eq | 42624 eq, 12674 na (Zalasr: no Sail access kind) | 15 shapes × 19 R-slot / 16 W-slot events × 16 links (+ovl) |
| G1w | 204 | eq | 204 eq | widths 1/2/8 |
| G1lxs | 32 | eq | 30 eq, 2 na (csrr) | LR;X;SC, with/without interference |
| G1b | 252 | eq | 168 eq, 84 na (Zalasr) | v2 `PState` def-use pairs, adjacent and split |
| G2 | 1044 | — | 1002 eq, 42 WEAKER, 0 STRONGER | after F1 (before: 63 STRONGER, all F1) |
| G3 | 17 | eq | eq | adShape guard constants, SC-arm branches, fwdHit |
| G5 | 9 | eq | 8 eq + row47-P0 (see below); all 9 verdicts = text | fixed platform |
| TS | 8 | eq | eq; all verdicts = text | Table S §19.2 phase-1 subset |
| ROW | 77 | eq; verdicts = text | 74 eq, 2 na (pointer in memory; csrr), 1 harness artefact (`addrpo`) | |

Explained non-eq on v2 (none is a machine defect):
- `addrpo` (Sail): harness relocation artefact (loaded relocated pointer + relocated base leaves RAM → trap → runs
  dropped).
- `G5 row47-P0` (Sail, platform `P ≡ false`): Sail cannot succeed an SC when the opaque reservation predicate is
  false, so success outcomes are absent at that platform BY DESIGN (the union over platforms is the full set); the
  probe's designated outcome (failure) matches the text.
- G2 WEAKER (42): failed SC's `rd` reset (16, W5); CSR chains through untracked CSRs (10, W1); Zcb `c.lbu/lh/lhu/
  zext.b/not/mul` and Zimop `mop.r/rr` (`ORnone`, W3).
- G2 text-verdict fixes during the run (harness, not machine): release annotations of `amo*.rl/aqrl`, `sc.rl/aqrl`,
  `lr.aqrl` (rule 6 orders the harness's load before them) were first missing from the text-verdict computation.
- Harness fix: Sail-level probes now start every uninitialised GPR at 0 (the boot program leaves a0/a1 =
  hartid/DTB), as the reference and label level do.

Scope gaps (open): branch logging for G3 (E3's "every branch taken, logged") is NOT implemented — branch coverage is
shown by outcome differences only (G3 on today's machine: both branches of each `adShapedb` conjunct separate
STRONGER from eq); G4 deferred ([OWN.P3]); G5 probes needing misaligned decomposition, `cbo.*`, `amocas`, MMIO
or `choose` cannot run (`MachSail.sNext` stops there; reference front end has no such instructions): G5-MIS1/2,
CMO-TEAR, CMO-INV, ZC-WB, DEV-SC; Zalasr label level only.

## (6) CALIBRATION (E0) — PASSED for phase-1 scope

Today's machine (`WeakPromise.wpstep`) + today's emission (`WeakEvInst.pnodeStep`), unseeded, label level
(`CalibToday.lean`; uncertified, so every rediscovery below is also explained by the blocking premise), plus the
decoder check on today's emission.

| Seeded row | decider | rediscovered? | evidence / why |
|---|---|---|---|
| SR-7 (M14 W-TV bank) | outcome | YES | ROW `lbAmoPo` (row 29) today STRONGER; G1: 256 cells `amo*;{po,fi,fr.r,fw.r,frw.r};st` STRONGER. `loadPostAt` banks the AMO read's timestamp in `wTbank`; the AMO's `LExStore` (`storePostRunD`) puts it into `vcap`, so every later store follows the AMO's read. Row 33 out of scope. |
| SR-8 (M15 walker gate) | outcome | YES | ROW `lbAmoAd` (row 30) STRONGER; G3 adShape with the guard's constants: STRONGER exactly when `adShapedb` holds (0x01→0x41, 0x00→0x40, 0x3f→0x7f, 0x81→0xc1, 0xc1→0x41), eq when a conjunct fails (0x41→0x41, 0x01→0x01, 0x01→0x42), 2-byte cases BOTH/WEAKER |
| SR-9 reservation (31, 31b, 35a–d, 36) | outcome | YES (7/7) | all STRONGER; also lbLrsc, lrScSc, mix26h/i, G1lxs 29/32, G1 ~13k SC cells, TS T-LR2/LRSC-AQRL/PAUSE-SC/T-R3b. `instrPost` clears `wRes` at every `LInstr` (announce and boundary), so no SC succeeds through `pstepEv` |
| SR-9 failed-SC rd | decide | YES | `cal_SR9_rd` |
| SR-11 DEC-6 | decide | YES | `cal_SR11_dec6` (`sret`/`mret` ctrl through sepc/mepc) |
| SR-11 DEC-7 | decide | YES | `cal_SR11_dec7` (load `rd` ← mstatus, pmpcfg0, pmpaddr0 read by Sail; `jalr` link ← rs1) |
| SR-11 DEC-5 (satp) | decide | out of phase-1 scope | M-mode: Sail reads no `satp` at an access (observed read sets) |
| SR-19 | decide | YES | `cal_SR19` (CSR outside the table, Zcb, Zimop `rd` stale). Row 41's outcome cannot separate it (its observable `a0` is overwritten by the `csrr`). |
| SR-20 (D-S0-4 default reading) | decide | YES | `cal_SR20` (trap entry's mepc/mstatus `LSilent`) |
| SR-21 (c2) | G5 text≠instance | YES | G5 `row47-P1`, `SCFAIL` at `P ≡ true`: text ALLOWED, today unreachable; at `P ≡ true` the instance's exclusive `memWrite` arm offers only `.Ok (some true)` or the memory-blind retry (WeakEvInst `pnodeStep`), so `rd = 1` is unreachable on the instance independently of SR-9 (`row47-P0`, `P ≡ false`: today reaches it) |
| SR-10, SR-12, SR-14, SR-15, SR-16, SR-17, SR-27, SR-29 | — | out of phase-1 scope (translation/A/D, [OWN.P3]) | |
| SR-24 (to check) | TS | v2 FAITHFUL | FT-1/FT-2 on v2 Sail level = text |

Unseeded findings on today's machine (bonus): F1 (CSR old view, same `erwSrcs` cause; not visible to today's
deciders); Zalasr has no form (scope).

## Disagreement report on v2 and K0b

- STRONGER root causes on v2 beyond SR-1…SR-31: **1** (S0rest-F1, fixed). K0b (N = 5): not fired.
- No unexplained disagreement remains on v2 (above). K0c: one fix iteration.
- WEAKER on v2 (sound, recorded): decoder W1–W6 (above), G2 WEAKER (same causes).

## S0 exit verdict (phase-1 scope)

- E0: PASSED (every in-scope seeded STRONGER row rediscovered by its decider).
- E1: NOT MET — no v2 re-extraction of Table C by a meta-script was done in this stage (C-D extraction is the
  decoder table; C-F/C-A/C-E/C-S re-extraction from Machine.lean/Emit.lean remains).
- E2, E5: met at S0-T (unchanged).
- E3: PARTIAL — C-D/C-R/C-K decided by `decide`; C-F/C-A by G1/G1b/G3 comparisons; C-E/C-S only for the phase-1
  G5/TS probes the pipelines can run; G3 branch logging not implemented; G4 deferred.
- E4: MET for every probe in scope (v2 label and Sail = reference up to the explained harness artefacts); the
  litmus-tests-riscv oracle agrees (corpus re-run after F1).
- Overall: S0 NOT exited; open items E1, E3 (branch logging, unrunnable G5 rows), G4 (deferred by ruling).
