# USER proof — residuals handed to later lanes

Collected from the USER lane reports (Sept 26 2026). Each item names the lane that owns it.

## Model faithfulness (audit running)
- The Lean backend evaluates effectful `&&`/`||` operands eagerly (Sail/Rocq short-circuit). Consequences
  found by U1-X3: `is_CSR_accessible` reaches `currentlyEnabled Ext_Zkr` for CSRs 0x747/0x757, and the
  generated `currentlyEnabled` has no `Ext_Zkr` clause → `assert false` (no Sail step); extra reads of
  mstateen1..3/sstateen1..3. `uxr_execute_CSRReg/Imm` exclude 0x747/0x757 (`hz`) until resolved.

## U3 assembly
- `uwkTreeMem (bmWrite mm addr 8 v) (t.setLeaf 2 vpn v)` (the byte map still holds the tree after an
  A/D write-back) — needs `pagesNodup` + a `setLeaf` entries lemma (U1-P1 left it; U1-F's
  `ubMemStep_setLeaf` is the step side).
- A single tree-level `translate` theorem bundling lookup / hit / miss / write-back (pieces in UTlb).
- PC 2-alignment: not in the frame (Rocq doesn't carry it); comes from a successful fetch (U2-F).
- `kmapStatic` for user-tier page-table reads: lane U1-K adds it to `uvAmb`/USER (deviation from
  Rocq; Rocq's cells are physical).

## Cleanups (one home per concept)
- `utlbOk` (Xv6) ≡ `utlbInv` (MachCSL/UTlb) up to renaming (`Iff.rfl`): make one the definition.
- Read-only walk transfer: X2's `uxc_runRW_ro`, X3's `uxr_runRW_of_runRead`, U1-C's
  `uc_runRW_of_runRead` — merge into URunRW.
- Walk tactics: `uwk_run` (UWalkRun, general MetaM stepper) vs U1-P2's hand-rolled `utr_*`; new
  lanes use `uwk_run`.
- `UxrCfg` / `UxcCfg` / `UfCfg` / `UtrPins` restate config pins separately; consider one record.

## Reservations (lane U2-R, coordinator decision: Rocq's `resv_any`)
- `runRW`'s exclusive write refuses unless the walk's own `rv` is set; a walk from `ctxTok` starts at
  `rv = false`, so an SC in a later cycle than its LR (every real pair) walks to `none`. Fix: exclusive
  write proceeds from any reservation state (Rocq `resv_any`) + the Iris step for an exclusive write with
  no reservation (`resvFrag … none`). Then U2-M1's SC-success lemmas drop `s.rv = true`.
- `lr.aq`/`lr.aqrl`: walker refuses acquire exclusive reads; the Iris read rule returns a fragment with
  `acq = true` that `uResvTok`/`ctxTok` don't accept. Same lane.
- U2-M1 leaves: execute-level arms go to U2-M4 (`rX_bits` → `uma_get_transformed_data_addr` →
  `uma_vmem_read`/`_write`); `transform_effective_address` takes `senvcfg = 0`, `MXR = 0` as hypotheses.
