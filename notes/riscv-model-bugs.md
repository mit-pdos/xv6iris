# Bugs found in external RISC-V memory-model artefacts

Owner, 2026-11-02: "When I ask you for bugs, these differences seem to be bugs in herd. Record them."

Found while validating our Lean reference model (`Weak/Prom/Ref.lean`, `rvwmoRef`, the encoding of the RVWMO chapter of the
RISC-V ISA manual) against the litmus-tests-riscv corpus. The definition is the manual's prose (owner ruling 6, "The
definition is the RiscV reference"). Evidence and runs: `~/dev/weak-orch/promising/herdcheck/report.md`,
`herdcheck/run-corpus.md`, `~/dev/weak-orch/promising/litmus/oracle-cap8-*.txt`, `xv6iris-pcsl2/PROGRESS-S0P1.md` (K1).

Versions: herdtools7 master `9f90176bdd6fc2ec3b34a7989c2ba011f538d821` (herd7 7.58+1, 2026-10-30); riscv-isa-manual main
`e17d92a1` / `8fb3965f` (2026-10-26 / 10-29); litmus-tests-riscv `08728edcd99c7e1819d2d4c6789df6d5299ccb69` (2026-05-20).

Marks: STRONGER = forbids executions the manual's prose allows; WEAKER = allows executions the prose forbids.

## herdtools7 (herd7 and its bundled riscv.cat)

| # | Bug | Evidence | Mark | Tests affected | Upstream status |
|---|---|---|---|---|---|
| H1 | Zalasr load-acquire / store-release (`lw.aq`, `sw.rl`, …) are treated as **RCpc**; the manual makes them **RCsc** | `herd/libdir/riscv-defs.cat:32-34,50` `let RCsc = (Acq\|Rel\|AcqRel) & (EX\|X)` (only AMOs and LR/SC); `herd/RISCVSem.ml:157,191` plain accesses get annotation `P`. Manual: `unpriv_zalasr.adoc:68-69` "The instruction always has an acquire-RCsc annotation", `:122-123` release-RCsc; ppo rule 7 (`rvwmo.adoc:289`). Example `RelAcq_2_THREAD/SB+porlaqs`: herd Sometimes, manual Never | WEAKER | 610 corpus tests (K1-a) | PR #576 (2023-05-04) open, unmerged; "zalasr" appears nowhere in herdtools7 |
| H2 | An SC to a **different address** than its LR is **forced to fail** by default; the manual permits success | `herd/RISCVSem.ml:195-203` (without `lrscdiffok` the SC's address must equal the reserved one). Manual: `rvwmo.adoc:340-342` "implementations are permitted to allow sc operations to succeed in such cases"; `zalrsc.adoc:91-93, 99-101` | STRONGER | 3 tests: `HAND/SC-FAIL`, `HAND/LR-SC-diff-loc1`, `HAND/LR-SC-diff-loc2` (K1-b) | `-variant LrScDiffOk` (2018) opt-in; PR #1896 (Maranget, 2026-07-03) makes it the default, open |
| H3 | herd cannot parse `jalr x0` in RISC-V litmus tests | herd error on `SF_THESIS/HAND/MP+fence.rw.rw+ctrlind`, `…+ctrlindaddr` | tool limitation | 2 tests (no herd verdict) | not reported |
| H4 | 9 LR/SC-heavy tests do not terminate within 900 s (e.g. `ATOMICS/CO/2+2W+posxxs`) | `herdcheck/run-corpus.md` | tool limitation | 9 tests | not reported |

## The ISA manual's formal appendix (`src/unpriv/mm-formal.adoc`)

| # | Bug | Evidence | Mark | Tests affected | Upstream status |
|---|---|---|---|---|---|
| M1 | **Typo** in the herd listing: `and RL = RelAcqRel` (should be `Rel\|AcqRel`); herd rejects the file ("unbound var: RelAcqRel") | `mm-formal.adoc:300` | — (model unusable as published) | whole appendix model | **regression**: fixed in `src/mm-herd.adoc` by e6fa8a7f (2025-12-10, #2289, "Current riscv AQ & RL (Zalasr) instructions are RCsc"); reintroduced when dfed013d (2026-04-06, #2833) deleted mm-herd.adoc and kept the old copy in mm-formal.adoc |
| M2 | Atomicity for **mismatched LR/SC** pairs is missing: the herd atomicity rules relate events at one location only, but the prose Atomicity Axiom is over the bytes the **LR** read | `mm-formal.adoc:371` (`winside = (infloc;rmw;inflocext) & …`), `:401` (`empty rmw & (fre;coe)`); prose `rvwmo.adoc:330-337` | WEAKER (once SCs to other addresses may succeed, as the prose allows) | `HAND/LR-SC-diff-loc3`, `HAND/LR-SC-diff-loc4` (herd+appendix+LrScDiffOk: Sometimes; prose: Never) | not reported |
| M3 | ppo **rule 12** is written from a **read** (`r12 = [R];(addr\|data);[W];rfi;[R]`), but the prose lets the first operation be any memory operation, and a successful SC's `rd` is a dependency source | `mm-formal.adoc:326-327`; prose `rvwmo.adoc:250-256` (sc's rd as destination), `:298-300` (rule 12); herd's own library uses `[M]` | WEAKER | `HAND/PPOLDSTLD02` (appendix: Sometimes; prose and herd's library: Never) | not reported |
| M4 | Stale pre-Zalasr text alongside the Zalasr chapter | `rvwmo.adoc:123-128` (only AMO/LR/SC listed as RCsc-annotated); `rvwmo.adoc:149-153` ("the ISA does not currently contain native RCpc load-acquire or store-release instructions"); Alloy `restrict_to_current_encodings` (`mm-formal.adoc:236-238`) `no (LoadNormal + StoreNormal) & (Acquire + Release)` | documentation | — | not reported |

Ambiguity (not counted as a bug): ppo rule 13's "instruction m" (`rvwmo.adoc:301-302`) vs the formal `r13 = [R];addr;[M];po;[W]`
(a failed SC issues no memory operation). Owner ruling [OWN.P6]: memory-operation reading (= the formal model).

## Sail RISC-V model

Upstream: riscv/sail-riscv main `02cc53657cf8` (2026-11-03). Our generated Lean copy (`model/Lean_RV64D`) comes from the
fork zeldovich/sail-riscv `070832a1` (on upstream `61266bd`, 2026-08-03) via `tools/regen_sail_model.sh`, with the module
list `model/sail-modules.txt` and the config `model/sail-config-rv64d.json`. Evidence: the SA-3 investigation
(2026-11-03, `~/dev/weak-orch/promising/SA3_prompt.txt`). Owner rulings [OWN.P8], [OWN.P9].

| # | Gap | Evidence | Where the gap is | Effect | Status / treatment |
|---|---|---|---|---|---|
| S1 | **No Zalasr** (load-acquire `l*.aq`, store-release `s*.rl`, RCsc) | the instructions are not decoded: they trap as illegal. Mem.lean:222-255's `internal_error` for unreserved aq/rl is unreachable (every caller passes safe flags). Upstream mem.sail has the same behaviour | **upstream Sail gap**: Zalasr is ratified but not implemented; PR #328 open since 2023-10-27, stale (maintainer asked for an update 2026-08-20) | faithful for a hart without Zalasr; 3801 corpus tests can be checked only at label level / against the reference | [OWN.P9]: keep the trap; Zalasr covered by `rvwmoRef` + label level. (Earlier wording here said "raise internal_error"; corrected.) |
| S2 | **Zkr module missing from our build** while the config says `Zkr.supported: true`: an M-mode `csrr`/`csrw` of `mseccfg` (0x747) or `mseccfgh` (0x757) ends in `assert false` (no step) | `currentlyEnabled` has no `Ext_Zkr` clause (PlatformConfig.lean:2976-2978), reached from `is_CSR_accessible` (SysControl.lean:319, :330; the `\|\|` at :330 is eager) | **our build config** (`model/sail-modules.txt`); upstream builds with `--all-modules` | the only Sail error site reachable in phase 1 (M-mode code touching mseccfg); no xv6 kernel path reaches it | [OWN.P9]: include the Zkr module, regenerate at the same pinned commit; `seed` answered nondeterministically (SA-2) |
| S3 | **`misa` and the config advertise F and D (and Zicfilp, Zicfiss, Smmpm) but those instruction modules are not compiled**: FP instructions trap as illegal on a hart that claims them | `model/sail-config-rv64d.json` (F :552, D :565, Zicfilp :665, Zicfiss :668, Smmpm :919) vs `model/sail-modules.txt` | **our build config** (module list vs config mismatch); upstream builds all modules, so not an upstream bug | not a faithful RISC-V hart (advertises what it cannot execute); kernel image has no FP instructions | [OWN.P9]: clear F/D/Zicfilp/Zicfiss/Smmpm from misa and the config (rv64imac-style hart); regenerate |
| S4 | **`internal_error` on a failed PTE conditional write** (translation on) | Vmem.lean:367 | upstream behaviour; reachable only if the instance answers a conditional PTE write with `.Err ()` | deferred with translation ([OWN.P3]) | Emit must never answer `.Err ()` there; otherwise global havoc ([OWN.P9]) |

## litmus-tests-riscv

| # | Bug | Evidence | Mark | Tests affected |
|---|---|---|---|---|
| L1 | `model-results/herd.logs` is stale: last regenerated 2018-12-22 (f45b4bf), before Zalasr; covers 6874 of 7907 test files | repo history at 08728edc | — | the 610 tests of H1 read as RCsc; 1033 tests without a stored verdict |

## Net effect on our reference

Against herd master + the manual's appendix model (typo fixed) + `-variant LrScDiffOk`, our reference agrees on 7863 tests
and disagrees on 3 (M2 ×2, M3 ×1), in each case following the prose. Against the stored 2018 logs read as RCpc: 7548 agree,
3 disagree (H2).
