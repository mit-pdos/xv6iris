# Theorem 2 on RVWMO: final state (2026-10-09)

The Lean weak tier proves that xv6's real allocpid code (inlined into `allocproc`,
`+0x38 .. +0x9a`) hands out distinct pids on RVWMO against an ARBITRARY third hart C that is
constrained only by a WPd against the xv6 protocol (`HwpC`, the only iProp premise). This is the
Iris-style ownership + lock-invariant argument recovered on the AxSL tier.

## Statement (`Weak/AxSpinT2b2.lean`)

`allocpidOpen2`: harts A, B run the segment on any instruction-boundary PREFIX of its row
(`allocPre`, pins `AllocPins2`). Conclusion:

1. `¬ t2Cut` for A and B. Neither hart enters `panic()` (acquire's / release's holding checks,
   pop_off's `noff < 1`), neither takes `intr_on`, and no ra/s1 reload reads anything but its
   spill. All proved (`cutIff`).
2. If a hart's segment completes: its nextpid read is served by a write made under the lock
   (`npSrc`), and `a3 = sext32 w` at its final state, with `w` its stored pid word.
3. If both complete: the stored pid words differ and so do the `a3` registers.

`allocpid2Distinct2` is Theorem 1 (C's row empty).

## Remaining premises

| Group | Premises |
| --- | --- |
| Model | tagged RVWMO consistency, ctrl closure, A/D bits preset and read-only PTE pages, warm TLB, runs end at an instruction boundary |
| Layout / image | `xlayXv6`, kernel text (incl. `tailText`, `tailText2`), `MapOk`, 16-byte frames, `HimgNoff`, `Himgc`, initial nextpid |
| Scope pins (`AllocPins2`) | `npNowrap` (pid ≠ 1000, no wrap: a wrap would break the monotone ghost), `npNcoll` (no scanned pid equals the candidate; unreachable without a wrap), `ppArm` (path selector) |
| Store values | `t2CpuVals`, `t2RelVals`, the amoswap's written word (fixed by the code; rows fix address/width/class only) |

Removed along the way: the 5 panic-arm pins, the release lock bit, the 18 reload pins, `poArm`,
`HsrcAl` (protocol now requires full-width lk->cpu writes, `clFull`), the interim `rlEnd`, and the
`a3`-free post. The prefix-closure argument (a panic prefix extends to a consistent execution)
stays informal.

## Certificates (all hypothesis-free, audited: `tools/ci/audit.sh --weak`, 10 roots)

| Lean | Shows |
| --- | --- |
| `allocpidOpen2Cert` (AxSpinT2q1) | the premises hold on a concrete 3-hart run; pids 1, 2; `a3` = 1, 2 |
| `allocpidPrefixCert` (T2q2) | applied on a prefix run where neither hart completes |
| `allocpidLkRaceCert` + trivial twin (T2q3) | a racer forging `lk->locked`/`lk->cpu` has no WPd: no-panic is ownership-load-bearing |
| `allocpidStkRaceCert` + trivial twin (T2q4) | a racer overwriting A's ra spill has no WPd: stack ownership keeps control flow on the row |
| `allocpidRaceCert` (T2e3, stage 1) | an unlocked nextpid racer has no WPd (`npSrc`) |
| `allocpidOpenCert` (T2c, stage 1) | stage-1 capstone on the concrete run |

Axioms: `propext`, `Classical.choice`, `Quot.sound` + `bv_decide` certificates; opaques: the two
reservation predicates; no `sorryAx`.

## Design notes

`notes/weak-lb-thm2-design.md` (stage 1), `weak-lb-thm2-stage2.md`, `weak-lb-thm2-pins.md` (P1–P4),
`weak-lb-thm2-p4.md`, `weak-lb-thm2-spike.md`; owner rulings in `~/dev/weak-orch/open_questions.txt`
(Q-T2-*, Q-S2-*, Q-P*).
