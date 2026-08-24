# vtest-rocq -- the model side of the device semantics tests

The QEMU side is [`tools/vtest`](../tools/vtest); read its README and
[`abi.h`](../tools/vtest/abi.h) first.  Here:

- **`VTest.v`** -- the harness: the ABI constants, the initial machine, the
  stepper, and the observation projections.  Read its header before adding a
  test; it says what a test claims and, more importantly, what it does not
  claim yet.
- **`<Name>Gen.v`** -- GENERATED, one per test: the image bytes and what QEMU
  produced.  Regenerate with `make vtest-gen`, never edit.
- **`<Name>.v`** -- the test: a handful of `vm_cast_no_check`d equations
  between a projection of the model's reached state and the capture.

## Adding a test

1. Write `tools/vtest/tests/<name>.S` (include `abi.h`, define `_vtest_body`).
2. `make vtest-gen` -- runs it on QEMU and writes `<Name>Gen.v`.
3. Write `<Name>.v` and add both to `_CoqProject`.
4. `make vtest-check`.

## What a red test means

- **A different result** -- the model and the hardware disagree.  Classify it
  and add it to the findings table in
  [`tools/vtest/README.md`](../tools/vtest/README.md): *incompleteness* (the
  model is stricter, so some real driver is unverifiable) or *defect* (the
  model produces a value the hardware never does, so a proof depending on it
  is about a device that does not exist).  The second kind is what this suite
  exists to find, and `T2Rw.v` section 3 is the worked example.  A known
  divergence is pinned on both sides rather than left red -- see that file.
- **An empty result (`[]`)** -- `run_until` returned `None`: the model either
  got STUCK or ran out of budget.  `budget_left` tells them apart.  A stuck
  machine is usually the interesting case: an MMIO offset or access width the
  model does not decode, a `QueueNum` it refuses, or an access outside the
  regions the test declared.

## Cost

Dominated by building the byte map, not by running the program: every
declared byte is a `gmap` insert on a 64-bit key.  `t0_smoke` is 29
instructions and 8,264 declared bytes and takes ~8 s; the same test with a
16 KB DMA region declared took 33 s.  Declare the regions you use and no
more.  Instruction execution itself is ~8 ms each.
