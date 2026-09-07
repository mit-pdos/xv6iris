# vtest-rocq -- the model side of the device semantics tests

The capture side is [`tools/vtest`](../tools/vtest); read its README and
[`abi.h`](../tools/vtest/abi.h) first.

## Layout

There is ONE set of test cases (`tools/vtest/tests/*.S`); executing a case on
a platform produces a test RUN, so a case yields up to two runs.  **The
platform is the DIRECTORY**, never part of a file name.

At the top level, what both platforms share:

- **`V*.v`** -- the harness.  `VTest.v` (the ABI constants, the initial
  machine, the stepper, the observation projections), `VRun.v` /
  `VRunConc.v` (what a run IS and what it means for one to pass),
  `VSched.v` / `VConc.v` / `VNode.v` / `VTso.v` / `VIcache.v` (the
  schedules and the multi-hart, relaxed and fetch steppers),
  `VExecStuck.v` (`ENoStep` vs `EChoice`), `VBoot.v`, and `VModelFacts.v`
  -- the universally quantified statements about the model that no capture
  comparison can express.  Read `VTest.v`'s header before adding a test: it
  says what a test claims and what it does not.
- **`<Case>Sched.v`** -- HAND-WRITTEN, one per multi-hart or fetch case: the
  interleavings.  An interleaving that reproduces a particular observed
  outcome is the thing a human works out, so it cannot be generated -- and
  it is the same list on both platforms, which is why it lives here.

Under **`QEMU/`** and **`JH7110/`**, everything that is about one platform:

- **`<Case>Gen.v`** -- GENERATED, the CAPTURE: the image that ran, the whole
  untrimmed result region, every 512-byte disk sector the run changed, the
  serial bytes, and the set of distinct results seen over repeats.  Written
  by `make vtest-gen` (QEMU) or `make hwtest-gen` (the board), never edited.
  The board's definitions keep their `_hw_` infix, so the two platforms'
  globals stay distinct even though the files are both `<Case>Gen.v`.
- **`<Case>Hart<N>Gen.v`** -- the same, built with `PRIMARY_HART=N` and run
  under `-smp N+1`.  QEMU only.
- **`<Case>Run.v`** -- GENERATED from the capture, offline: the run as a
  `VRun.TEST_RUN`, whose `outcome` is COMPUTED from the model rather than
  asserted.
- **`<Case>Pass.v`** -- GENERATED: the `VRun.TEST_PASSES` instantiation, the
  same two tactics every time.  A file that does not compile is a run that
  does not pass, which is a finding and not a build error to paper over.

A `Require` across directories is qualified (`From VTest.QEMU Require Import
CoreSmokeRun`); the harness and the schedules are unambiguous and are not.

## Adding a test

1. Write `tools/vtest/tests/<name>.S` (include `abi.h`, define `_vtest_body`).
2. `make vtest-gen` -- runs it on QEMU and writes `QEMU/<Name>Gen.v`, then
   the run module and its proof.
3. `make vtest-check`, and `make vtest-table` for the per-case verdict.

`_CoqProject` IS the record of which runs pass: a proof is listed exactly
when it holds, and CI fails if anything listed does not compile.  There is no
second file saying the same thing.  `make vtest-runs` rebuilds the run
modules from the checked-in captures (no QEMU, no board); `make vtest-passes`
attempts every proof and rewrites `_CoqProject` with the ones that held.

## What a red test means

`VRun.run_passes` admits two things: the model exhibits every outcome the
platform observed (`MDone`), or the model has no transition at all
(`MNoStep`, which `VExecStuck.exec_r_no_step` makes mean the RELATION and not
just the interpreter).  A red run is therefore one of:

- **A different result** -- the model and the hardware disagree.  Classify it
  and add it to the findings table in
  [`tools/vtest/README.md`](../tools/vtest/README.md): *incompleteness* (the
  model is stricter, so some real driver is unverifiable) or *defect* (the
  model produces a value the hardware never does, so a proof depending on it
  is about a device that does not exist).  The second kind is what this suite
  exists to find.  A known divergence is pinned on both sides and proved
  unequal rather than left red.
- **`MBudget`** -- the model did not reach the DONE flag in `budget` steps.
- **`MUnknown`** -- `exec` hit an `Interface.Choose`.  Not a pass and not a
  refutation: a gap, where the relation does have transitions and only the
  interpreter will not pick one.

## Cost

Dominated by building the byte map, not by running the program: every
declared byte is a `gmap` insert on a 64-bit key.  A 29-instruction test with
8,264 declared bytes takes ~8 s; the same test with a 16 KB DMA region
declared took 33 s.  Declare the regions you use and no more.  Instruction
execution itself is ~8 ms each.
