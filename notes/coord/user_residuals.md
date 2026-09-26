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

## From U2-M2 / U2-M3 / U2-F / U3-A (Sept 26 2026)
- **uptWf validity pin (decision: adopt Rocq's `upt_map_wf` `pte_valid`)**: add `uwkInv w = false` for
  every user leaf to `uptWf` (+ its producers: mappages/uvmalloc/uvmcopy/kexec sites, like D53). Without
  it, `utlbOk` admits a cached write-without-read leaf whose TLB hit hits `check_PTE_permission`'s assert
  (no Sail step). Then U2-F's `UftLeavesValid P` premise of `ustFetchSpec_holds` is dropped. Worktree
  lane after the bump lands (touches kernel uvm proofs).
- **CSR hypothesis widened (U3-A `UclCsrEager`)**: 11 numbers — 0x747/0x757 (Zkr, missing clause) and
  0x10D–F/0x60D–F/0x61D–F (eager reads of mstateen1..3/sstateen1..3 outside `ufFoot`). FALSE today (walk
  = none), so `ucl_execTotal` is vacuous until fixed. The stateen nine should go via the eager-&&
  elimination lemma (lane andelim); 0x747/0x757 need the Zkr clause or the backend fix (user decision).
  U3-A duplicated U1-X3's CSR table at a smaller pin (`uclPin`): fold U1-X3's into it later.
- **Memory contract `UclMemArms`** (6 fields, U2-M4 builds to it): load/store (`uWidth1248`),
  loadres/storecon (`lrsc_width_valid`), amo (`uAmoWidthOk`), zicbop; stated on `execute i` from the
  state; compressed memory forms follow via ExecuteAs redirects.
- **AMO acquire (`.aq`/`.aqrl`)** and LR.aq: walker gap, lane U2-R (resv_any) covers them.
- **AMO config divergence to check**: Rocq's `arm_AMO_u` comment says only AMOSWAP retires (others trap);
  Lean's `bootPMA` gives RAM `atomic_support = AMOCASQ` (every op retires). Check Rocq's platform PMA and
  align (BootReset phase 2 touches bootPMA).
- **decodableU too weak at width 16**: doesn't record width 16 ⇒ CAS with even rs2/rd; strengthen for the
  AMOCAS.Q facts (U2-M4/U3-A).
- **Failing AMOCAS leaves the reservation bit set** (model's reserved-read kind) — noted, not a proof gap.
- **U2-M2 straddle-store hypothesis**: high part's translation asked for every byte map with the same
  domain as after the low write; U3/U2-M4 discharges it (user stores can't reach PT bytes — from
  UserBytes' disjointness).
- Duplicates: `uma_intra_bv` ≡ `umm_intra_bv`; `umoW` ≡ `umaW`; `umo_gtda` vs M1's vmem front.
- New walker `uftRun` (U2-F): runRW + fetch nodes via oracle; `swp_uftRun` proved once.
- **bv_decide enum pitfall**: bv_decide over a Sail enum adds `<Enum>.enumToBitVec`; two modules doing it
  clash on import. Shared home pattern: MachCSL/BvEnumSatp.lean.
