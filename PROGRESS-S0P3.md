# PROGRESS — S0-P part (2), milestone 3: the litmus corpus through the REAL Sail model + emission v2

Worker: Opus (S0P3), 2026-11-02. Workspace `/home/bsdinis/dev/xv6iris-pcsl3` (from milestone 2, change vtrmyrsl).
Plan of record rev 7 (§1A, §8 S0-P). Brief: `~/dev/weak-orch/promising/S0P3_prompt.txt`.

## Defects / fixes

**None.** No difference between the Sail level and the label level, nor between the Sail level and the reference,
on any test in Sail scope (below). No edit to Machine.lean, Emit.lean, MachExplore.lean, MachLitmus.lean or any
proof file.

## LATEST (2026-11-02): MILESTONE 3 GREEN on the Sail-scope corpus

`~/dev/weak-orch/promising/litmus/sail-cap8.txt` (= `sail-run1.txt`; cap 8, Sail level + label level + reference +
fresh herd logs): of the 7869 tests the label level compares,
- **4068 run through Sail**: Sail level = label level = reference on **all 4068** outcome sets
  (`SM=eq SR=eq`).  Sail vs herd: 4063 eq, 2 herd-has-more = the known appendix bugs `HAND/LR-SC-diff-loc3`,
  `HAND/PPOLDSTLD02` (Sail = label = reference), 3 `na` (herd timeouts, `ATOMICS/CO/2+2W+…sxx…`).
  No run stopped (no trap, MMIO, decomposable access, `choose`, fuel); no domain miss; no budget hit; reservation
  platforms: 3445 tests 1 (no SC), 553 tests 2, 70 tests 4; the union over platforms = the all-true platform's set
  on every test (`platDiff` never).
- **3801 out of Sail scope** (`SCOPE-SAIL asm`): 2705 use a Zalasr store-release (`s*.rl`), 1096 a Zalasr
  load-acquire (`l*.aq`) — the sail-riscv model has no Zalasr instruction and no access kind for an unreserved
  acquire load / release store (`read_kind_of_flags`/`write_kind_of_flags` raise `internal_error`,
  model/Lean_RV64D/LeanRV64D/Mem.lean:222–255).  This includes `HAND/LR-SC-diff-loc4` (`sw.rl`).
- 19 parse-out-of-scope and 19 over the cap, as before.
- Time: Sail level 2234 CPU-s (label level 182, reference 3954); 3 min 26 s wall on 80 shards.

`sail-cap99-noref.txt` (no cap, no reference): 4086 tests through Sail (the 18 over-cap ones in Sail scope too):
Sail level = label level on all 4086; vs herd 4075 eq, the same 2 appendix-bug tests, 9 `na` (herd timeouts);
3802 Zalasr out of Sail scope; no stop, miss or budget; 2184 CPU-s Sail level.  `litmus-appx/` deleted (local and
VM).

Sensitivity check (mutation, reverted): with the Sail emission's LOAD address sources dropped (`asrc := []` in the
`memRead` arm), 204 tests become `SM=WEAKER` (e.g. `SAFE/ISA2+fence.w.w+data+addr`: Sail Sometimes, label/herd
Never); so the pipeline does see the emitted labels.  (Only 204: the loaded register still carries the address
sources through `depsRd`'s F5' list.)

## The pipeline (files, all new, under Weak/Prom/)

- `Weak/Prom/SailExec.lean` — `subst_cone% c r`: every definition on a path from `r` to `c` becomes a function of
  `c` (`f._rp P := (value of f)[c := P, g := g._rp P]`, kernel-checked and compiled).  Applied to the opaque
  reservation predicate `xv6_resv_matches` and `MachCSL.riscvStep`: 10 definitions (`match_reservation`,
  `vmem_write_addr`, `vmem_write`, `execute_STORE`, `execute_STORECON`, `execute_SSPUSH`, `execute`,
  `run_hart_active`, `try_step`, `riscvStep`).  `riscvStepP P tick`; `riscvStepP_opaque : riscvStepP
  xv6_resv_matches = riscvStep := rfl` (the code that runs IS the model at platform `P`).  The decoder cone's code
  is `Vtest.Model`'s `compile_cone%` (rfl-proved `csimp`); no `implemented_by`.  (The opaque's own compiled code is
  the `Inhabited` default `false`: without this every SC would fail before its write.)
- `Weak/Prom/MachSail.lean` —
  * relocation: Sail RAM is `[0x80000000, 0x88000000)` (sail-config-rv64d.json `memory.regions`; below is MMIO,
    `devAddr`): locations at `OFF + a`, register/`li` values in a location's window relocated, final registers
    mapped back; an initial memory value that is an address is out of scope (none in the corpus);
  * assembler (`asmInstr`, standard encodings; `li` = `addi` / `lui+addiw` / `lui+addiw+slli 32+srli 32`, no
    source); code at `0x80400000 + 0x10000·h`, in the image at timestamp 0;
  * start state: the platform power-on file (`bootProg` via `bootRun`, as `Vtest.bootRegsOf`: M-mode, `satp = 0`,
    interrupts off), `PC`, the test's GPRs;
  * `sNext`: Emit.lean `hstep`/`hnodeStep`/`bndStep` one Sail event at a time, executably (labels exactly
    Emit's: `LIFetch`, `LCtrl (depsCtrl …)`, `LRegW r (regSrcs …)` = the decoder's sources, `LLoad/LExLoad` with
    `akAcq`/`akStrong`, `LStore/LExStore` with `akStrong`/`akRel`, `LAmoLd`/`LAmoSt`, SC `.Ok`/`.Err ()`, end-of-SC
    `LExFail`, `barLabel`, the FENCE.TSO half parked in `fn`); the clock tick is not taken (timer state only,
    interrupts off); a trap / MMIO / decomposable access / `choose` / `getCycleCount` / amocas / Zicbom STOPS the
    run (counted);
  * the PROGRAM TREE (`build`): the Sail run with reads answered from a value domain, as a tree of non-silent
    labels (the Sail side sees only answers, so one tree per hart per domain serves every final memory);
  * the three arms the label level never needs, as successor functions over v2's own post-state functions:
    `succFetch` (`memStep.fetch`, brute-force over timestamps, `fetchByteOk` above `wIfl`), `succAmoLd`
    (`memStep.amoLd`), `succAmoSt` (`memStep.amoSt`: slot, `exclOk`, COH, EXT); the rest is `MachExplore.succ`;
  * explorer: milestone 1's (promises-first normal form, per-hart message-list closure — now over the Sail trees —,
    `arrange`, per-hart walks `runT`, outcome product); a read child missing from the tree is a DOMAIN MISS
    (counted; 0 on the corpus);
  * reservation platforms (D51): the SC addresses `A` of the all-true trees, every `P : A → Bool` (one `P` per run,
    shared by every hart and SC: the predicate has no hart argument), outcome set = union.
- `Weak/Prom/MachSailOracle.lean` — driver `<repo> <herd.logs> <cap> <shard> <shards> [noref] [only=<substr>]`;
  MachOracle.lean's parsing / herd / reference / label-level code copied (that file defines `main`).

## Milestone-1 gap list (MachLitmus.lean header items 1–8) after the Sail run

1 fetch (`LIFetch` at the fetch floor, FENCE.I's `fenceIPost`), 2 split AMO halves (`amoSplitFused`), 3 silent
labels / one `LCtrl` per `nextPC` write, 4 the decoder's sources (incl. `depsRd`'s F5' address sources on a load's
`rd`), 5 the parked FENCE.TSO half (Emit's split r,r now + rw,w parked vs the label level's r,rw + w,w), 6 the
reservation predicate both ways + `.Err ()` — no outcome difference on the 4068 Sail-scope tests.  7 (misaligned)
is not exercised (no misaligned access in the corpus).  8: Zalasr has no Sail form (3801 tests out of Sail scope).

## Open items

- Zalasr: 3801 corpus tests are label-level only (needs a Zalasr-capable Sail model).
- `Weak/Prom/MachSail.lean` imports `Vtest.XState` (the conformance lib, not a default target) for `XRegs` and the
  `compile_cone%` csimp rules; fine for an oracle, a layering note if it is ever rooted.
- The Sail-level driver is uncertified (milestone 2's `explorerStep_sound` covers `succ`; `succFetch`/`succAmoLd`/
  `succAmoSt` and `sNext` vs `pstepV2` would need the same treatment).

## Runner (temporary `litmus-appx/run.sh`; `litmus-appx/model-results/herd.logs` = copy of
herdcheck/herd-appendix-lrscdiffok.logs; corpus = `.lake/litmus/repo` on the VM; folder deleted after the runs)

```sh
N=$1; shift; rm -rf /tmp/sailor; mkdir -p /tmp/sailor; k=0
while [ $k -lt $N ]; do
  (lake env lean --run Weak/Prom/MachSailOracle.lean .lake/litmus/repo litmus-appx/model-results/herd.logs ${CAP:-8} $k $N "$@" \
     > /tmp/sailor/out-$k.txt 2>&1; echo "exit $?" >> /tmp/sailor/out-$k.txt) &
  k=$((k+1)); done; wait
k=0; while [ $k -lt $N ]; do cat /tmp/sailor/out-$k.txt; k=$((k+1)); done
```
VM build: `.lake` (and `model/Lean_RV64D/.lake`, `vendor/lean-sail/.lake`) copied from the pcsl2 tree on the VM, then
`lake build Weak.Prom.MachSailOracle` (warm: seconds).
