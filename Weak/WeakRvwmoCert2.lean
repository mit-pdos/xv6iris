/-
Weak: **B2e-3b slice 3b — segment certification**.

Rocq: `iris/WeakRvwmoCert2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Design `claude-notes/design/weak-memory-route-b.md` §4e ("SLICES 2b/3, STATED", "SLICE 3's SHAPE
AND ITS ONE OPEN RISK", sub-slice 3b).  Slice 3a (`WeakRvwmoCert`) appends ONE block to a
candidate; slice 2b (`WeakEvProv`) says a hart's run is a function of the registers it READS.
This file joins them: given hart `x`'s G-emission (`WeakRvwmoConf.hartConf`) and a candidate in
which `x`'s trace is a PREFIX of its G-row, it runs `x` forward through the emission's remaining
blocks, appending each to the candidate, and concludes that the appended labels are the row's own
— re-TIMESTAMPED to the candidate's log, same addresses / data / classes — as long as no
instruction reads a TAINTED carrier.

THE THREE DELIVERABLES.
(1) `certStep*` (§3) — one `pstepEv` of the certified hart mirroring one emission step: the
    mirror (`WeakEvProv.pstepEvDagree`), the in-log retime (`WeakEvInst.pstepEvTsLoad`), and the
    WITNESS (any byte list of the right width is readable; the word is CONSTRUCTED by `bvOfBytes`,
    the successor node differs and the taint set grows, `WeakEvProv.taintClosureLoad`).
(2) `certBlock*` (§4) — one `hemit` block (`cblk`: the block with its run's annotations
    exposed) transported across the register-file change and appended to the candidate
    (`snocConsistent` + `execProgOk'Snoc`).
(3) `certSegment` (§5) — the iteration over the `hemit` derivation, maintaining the
    certification invariant (same monad node / parked fence / channel, register files agreeing
    off `T`, the same `wRelp`, the supply in place); its output is a SOLO extension whose appended
    labels are `lblReidxW` of the row's, so a WRITE (the exit write) comes out VERBATIM.

THE BLOCK / INSTRUCTION SEAM: the taint hypothesis is carried on the run's accumulated read list
(`rdsOk P rds`); instruction alignment enters only at `instrRdsOfChannel` (§3.4).

NARROWED (Rocq N-1..N-3, discharged later): `floorOk` (coherence side condition) is a hypothesis
of `certReadInLog`; `srcInLog` vs. a witness is the DATA of the read policy; the policy itself is
a hypothesis (`Hpol`) of `certSegment`.  §7's open obligations (O-1 the fused pair, O-2
re-convergence after a witness, O-3 `floorOk`/`srcInLog` bookkeeping, O-4 the general policy) are
Rocq comments, unchanged.

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below); `M unit` ↦ `SailM Unit`; `regstate` ↦ `RegFile`;
   `oib32` ↦ `Ibch`; `wreg` ↦ `Nat`; `register` ↦ `Register`; `dev_state` ↦ `Efab` (the event
   instance's fabric, `WeakEvPf` deviation 9); `agent` ↦ `Nat`; `bv (8 * n)` with `n : N` ↦
   `BitVec (8 * n)` with `n : Nat`; `l !! n` ↦ `l[n]?`; `tvs.*1`/`.*2` ↦ `tvs.map Prod.fst`/
   `Prod.snd`; `Forall P l` ↦ `∀ x ∈ l, P x`; `Forall2` ↦ `List.Forall₂`; `EStep i lb` ↦
   `⟨i, lb⟩`; `es_lb`/`es_ag` ↦ `esLb`/`esAg`; `zip` ↦ `List.zip`.  Rocq's `Notation ofence` is
   the local notation `Ofence`.  Axiomatic labels are written `Lbl.LLoad`/`.LLoad` (wlabels are
   the `open Wlabel` ones).
2. THE PROGRAM STEP's Lean shape (`WeakEvInst` deviations 4/5): `pstepEv` quantifies the barrier
   report `obar` beside `ors`/`oib` and has the PLIC-wire arm (`pstepPlic`, label `LDev`);
   `pnodeStepLoadSubst`/`pstepEvLoadSubst` carry `obar` through and refute the PLIC arm.
   `bvOfBytes` assembles the word with `WeakInterp.assembleBytes` (Rocq: `Z_to_bv` of
   `assemble_bytes`, `nth_byte_assemble_len`).
3. O2 / STAGE C — THE FETCH IS ADMINISTRATIVE (`WeakRvwmoConf` deviation 3): `projLbl
   (LIFetch ..) = none`, so a load row label has Rocq's TWO realizing wlabels again
   (`hlblRealizesLoadShape`'s Stage-B third case and `cblkLoadRetime`'s third branch are gone).
4. O2 / STAGE C — THE PINNED LTS (`WeakRvwmoCert` deviation 2; orchestrator ruling: the Cert
   chain runs at `pstepPin img pstepEv`).  Every appended block must supply `fetchPin img` for
   its ADMINISTRATIVE labels (the realizing wlabel's pin is free), and `cblk` hides them, so:
   - Lean-only `cblkG A …`: Rocq's `cblk` body with the admin predicate `lbAdmin true` of the
     admin labels abstracted to `A`; Rocq's `cblk` IS `cblkG (lbAdmin true)` (definitionally,
     so every destructuring of a `cblk` is unchanged), and the PINNED block is
     `cblkPin im := cblkG (lbPin im)`, `lbPin im l := lbAdmin true l ∧ fetchPin im l`.
   - the transports that only carry the admin conjunct are proved once, at any `A`
     (`WeakRvwmoCert2.cblkRelpG`, `certBlockMirrorG`, `cblkRetimeG`, `cblkSubstG`,
     `cblkLoadRetimeG`, `certBlockReadG`, `certBlockWitnessG`); the Rocq-named lemmas are their
     `lbAdmin true` instances (statements unchanged), and at `lbPin im` they transport pins.
   - `cblkPinCblk` (forget the pins), `cblkIntroPin` (`cblkIntro` of a pinned run),
     `cblkElimPin` (`cblkElim` with the pins), `WeakRvwmoCert2.esPin im es` (every label of an
     emission item list is pinned; `emFetchImg im em = esPin im em.emItems`) and
     `WeakRvwmoCert2.esPinBlock` (its split at one block).
   - `certBlockSnoc`: the supply at `pstepPin c.cdImg pstepEv` (premise and conclusion), the
     block `cblkPin c.cdImg …`; Stage B's `lbFetchInert` premise is DELETED.
   - `certSegment`: the supply pinned at `c.cdImg`; the new premise `esPin c.cdImg es` (after
     `srvwmoConsistent c`); the policy `Hpol` takes and returns `cblkPin c0.cdImg` blocks, and
     Stage B's `lbFetchInert` conjunct is DELETED.  `polStore` likewise (its Stage-B helper
     `lbFetchInertOfStoreNe` is DELETED); `certSegmentWitness` / `certSegmentNonvacuous` state
     the pinned supply.
5. `certStepTaint` takes ONE `cpu` for both runs, as Rocq (`WeakEvProv.taintClosureLoad` is
   stated at two).
6. Rocq's `Section segment` / `Section nonvacuity` contexts become explicit parameters (in
   Rocq's order), as the sections' closing does.  `cert_segment_nonvacuous`'s witnesses: CPU
   `⟨0, _⟩`, `evRs0`, `ibNone`, and `dev0_state` ↦ `efInit ⟨fun _ => default⟩`
   (`WeakRvwmoCert` deviation 3).  Rocq's `img0` notation is the literal `fun _ => none`.
7. §8's `Print Assumptions` audit is dropped (the lint's axiom/sorry ban is the audit).

**File-qualified names:** none of this file's Rocq names is in `notes/weak-port-dupnames.json`;
Lean-only (deviation 4; all `WeakRvwmoCert2.`-qualified): `cblkG`, `lbPin`, `cblkPin`, `cblkPinCblk`,
`cblkIntroPin`, `cblkElimPin`,
`WeakRvwmoCert2.esPin`, `WeakRvwmoCert2.esPinBlock`, `WeakRvwmoCert2.nvPin`, and the `…G` transports
`WeakRvwmoCert2.cblkRelpG`/`certBlockMirrorG`/`cblkRetimeG`/`cblkSubstG`/`cblkLoadRetimeG`/
`certBlockReadG`/`certBlockWitnessG`.

**Rocq → Lean name map.**  `pstep_ev_phart` `pstepEvPhart`, `adm_run_phart` `admRunPhart`,
`adm_run_pevrun` `admRunPevrun`, `pevrun_adm_run` `pevrunAdmRun`, `pcls_ev_rs` `pclsEvRs`,
`hlbl_realizes_rs` `hlblRealizesRs`, `hlbl_realizes_pair_rs` `hlblRealizesPairRs`,
`bv_of_bytes` `bvOfBytes`, `pnode_step_load_subst` `pnodeStepLoadSubst`, `pstep_ev_load_subst`
`pstepEvLoadSubst`, `cert_step_mirror` `certStepMirror`, `cert_step_reindex`
`certStepReindex`, `cert_step_witness` `certStepWitness`, `instr_rds_of_channel`
`instrRdsOfChannel`, `cert_step_taint` `certStepTaint`, `cblk` `cblk`, `pevrun_nil_inv`
`pevrunNilInv`, `pevrun_single_inv` `pevrunSingleInv`, `cblk_intro` `cblkIntro`, `cblk_elim`
`cblkElim`, `cblk_relp` `cblkRelp`, `cert_block_mirror` `certBlockMirror`, `lbl_reidx`
`lblReidx`, `lbl_reidx_refl` `lblReidxRefl`, `lbl_reidx_store` `lblReidxStore`,
`lbl_reidx_fence` `lblReidxFence`, `lbl_reidx_relp` `lblReidxRelp`, `lbl_reidx_sub`
`lblReidxSub`, `lbl_poisoned` `lblPoisoned`, `lbl_poisoned_notw` `lblPoisonedNotw`,
`lbl_reidx_w` `lblReidxW`, `lbl_reidx_w_refl` `lblReidxWRefl`, `lbl_reidx_w_of` `lblReidxWOf`,
`lbl_reidx_w_pois` `lblReidxWPois`, `lbl_reidx_w_store` `lblReidxWStore`, `lbl_reidx_w_fence`
`lblReidxWFence`, `lbl_reidx_sub_relp` `lblReidxSubRelp`, `lbl_poisoned_relp`
`lblPoisonedRelp`, `lbl_reidx_w_relp` `lblReidxWRelp`, `lbl_reidx_w_isw` `lblReidxWIsw`,
`lbl_reidx_w_notw` `lblReidxWNotw`, `hlbl_realizes_load` `hlblRealizesLoad`,
`hlbl_realizes_load_inv` `hlblRealizesLoadInv`, `cblk_retime` `cblkRetime`, `cblk_subst`
`cblkSubst`, `hlbl_realizes_load_shape` `hlblRealizesLoadShape`, `cblk_load_retime`
`cblkLoadRetime`, `cblk_vfree` `cblkVfree`, `cblk_vfree_of_retime` `cblkVfreeOfRetime`,
`cert_block_read` `certBlockRead`, `cert_block_witness` `certBlockWitness`, `cert_block_snoc`
`certBlockSnoc`, `src_in_log` `srcInLog`, `floor_ok` `floorOk`, `snoc_rd_adm_of`
`snocRdAdmOf`, `cert_read_in_log` `certReadInLog`, `wit_tvs` `witTvs`, `wit_tvs_fst`
`witTvsFst`, `wit_tvs_snd` `witTvsSnd`, `wit_tvs_lbl` `witTvsLbl`, `wit_tvs_length`
`witTvsLength`, `cert_read_witness` `certReadWitness`, `cert_write_ok` `certWriteOk`,
`cert_fence_ok` `certFenceOk`, `cert_rmw_latest_ok` `certRmwLatestOk`, `lb_rmwfree`
`lbRmwfree`, `cand_snoc_relp` `candSnocRelp`, `cand_snoc_relp_ne` `candSnocRelpNe`,
`cert_segment` `certSegment`, `seg_exit_write` `segExitWrite`, `lb_store_ne` `lbStoreNe`,
`lb_store_ne_rmwfree` `lbStoreNeRmwfree`, `lb_store_ne_ok` `lbStoreNeOk`, `pol_store`
`polStore`, `nv_hemit` `nvHemit`, `nv_row_class` `nvRowClass`, `cert_segment_witness`
`certSegmentWitness`, `cert_segment_nonvacuous` `certSegmentNonvacuous`.

**Dropped:** nothing (Rocq 78 declarations + the `ofence` notation; Lean 78 + 16 helpers).
-/
import Weak.WeakRvwmoCert
import Weak.WeakEvProv

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-- The parked-fence field, abbreviated: it appears in every signature. -/
local notation "Ofence" => Option (Bool × Bool × Bool × Bool)

/-! # 1. The hart-shaped pieces -/

theorem pstepEvPhart (cpu : CPU) (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch)
    (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    pstepEv (.PHart cpu m rs fn ib) d l p' d' →
    ∃ m' rs' fn' ib', p' = .PHart cpu m' rs' fn' ib' := by
  cases p' with
  | PHart cpu' m' rs' fn' ib' =>
    rintro ⟨rfl, -⟩
    exact ⟨m', rs', fn', ib', rfl⟩
  | PDisk _ => intro h; exact h.elim

theorem admRunPhart (instr : Bool) (p p' : Pexv6) (d : Efab) (ls : List Wlabel) (d' : Efab) :
    admRun instr p d ls p' d' →
    ∀ cpu m rs fn ib, p = .PHart cpu m rs fn ib →
    ∃ m' rs' fn' ib', p' = .PHart cpu m' rs' fn' ib' := by
  intro h
  induction h with
  | ARnil p d =>
    intro cpu m rs fn ib hp
    exact ⟨m, rs, fn, ib, hp⟩
  | ARcons p d l p1 d1 ls p' d' _ hs _ ih =>
    intro cpu m rs fn ib hp
    subst hp
    obtain ⟨m1, rs1, fn1, ib1, rfl⟩ := pstepEvPhart cpu m rs fn ib d l p1 d1 hs
    exact ih cpu m1 rs1 fn1 ib1 rfl

/-- `admRun` and `pevrun` are the same run with the same labels. -/
theorem admRunPevrun (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel) (p' : Pexv6)
    (d' : Efab) :
    admRun instr p d ls p' d' → pevrun ls p d p' d' := by
  intro h
  induction h with
  | ARnil p d => exact pevrun.nil p d
  | ARcons p d l p1 d1 ls p' d' _ hs _ ih => exact pevrun.more hs ih

theorem pevrunAdmRun (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel) (p' : Pexv6)
    (d' : Efab) :
    pevrun ls p d p' d' → (∀ l, l ∈ ls → lbAdmin instr l) → admRun instr p d ls p' d' := by
  intro h
  induction h with
  | nil p d => intro _; exact .ARnil p d
  | @more l ls p d p1 d1 p2 d2 hs _ ih =>
    intro hadm
    exact .ARcons p d l p1 d1 ls p2 d2 (hadm l List.mem_cons_self) hs
      (ih fun l0 hl0 => hadm l0 (List.mem_cons_of_mem _ hl0))

/-- THE PROJECTION EQUATION DOES NOT READ THE REGISTER FILE. -/
theorem pclsEvRs (cpu : CPU) (m : SailM Unit) (rs rs' : RegFile) (fn fn' : Ofence)
    (ib ib' : Ibch) (l : Wlabel) (ws : Wstate) :
    pclsEv (.PHart cpu m rs fn ib) l ws = pclsEv (.PHart cpu m rs' fn' ib') l ws := by
  cases l <;> rfl

theorem hlblRealizesRs (cpu : CPU) (m : SailM Unit) (rs rs' : RegFile) (fn fn' : Ofence)
    (ib ib' : Ibch) (ws : Wstate) (lb : Lbl) (l : Wlabel) :
    hlblRealizes (.PHart cpu m rs fn ib) ws lb l →
    hlblRealizes (.PHart cpu m rs' fn' ib') ws lb l := by
  rintro ⟨hnb, hlat, hrf, hpr⟩
  refine ⟨hnb, hlat, hrf, ?_⟩
  rw [pclsEvRs cpu m rs' rs fn' fn ib' ib l ws]
  exact hpr

theorem hlblRealizesPairRs (cpu : CPU) (m : SailM Unit) (rs rs' : RegFile) (fn fn' : Ofence)
    (ib ib' : Ibch) (cpu2 : CPU) (m2 : SailM Unit) (rsm rsm' : RegFile) (fnm fnm' : Ofence)
    (ibm ibm' : Ibch) (ws : Wstate) (lb : Lbl) (l1 l2 : Wlabel) :
    hlblRealizesPair (.PHart cpu m rs fn ib) (.PHart cpu2 m2 rsm fnm ibm) ws lb l1 l2 →
    hlblRealizesPair (.PHart cpu m rs' fn' ib') (.PHart cpu2 m2 rsm' fnm' ibm') ws lb l1 l2 := by
  rintro ⟨aq, rl, base, tvs, data, asrc1, asrc2, vsrc2, rfl, rfl, hne, hlen, rfl⟩
  refine ⟨aq, rl, base, tvs, data, asrc1, asrc2, vsrc2, rfl, rfl, hne, hlen, ?_⟩
  rw [pclsEvRs cpu2 m2 rsm' rsm fnm' fnm ibm' ibm]

/-! # 2. A substituted read is a real step -/

theorem bvOfBytes (n : Nat) (bs : List (BitVec 8)) :
    bs.length = n →
    ∃ w : BitVec (8 * n), ∀ j : Nat, j < n → bs[j]? = some (nthByte w j) := by
  intro hlen
  refine ⟨assembleBytes n (fun j => bs.getD j 0#8), fun j hj => ?_⟩
  rw [nthByteAssembleBytes n _ j hj, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega)]
  rfl

/-- THE SUBSTITUTION, at the monad node: ANY byte list of the read's own width is readable
there; only the CONTINUATION differs. -/
theorem pnodeStepLoadSubst (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates)
    (aq : Bool) (base : Int) (tvs tvs2 : List (Nat × BitVec 8)) (m' : SailM Unit)
    (ors : Option RegFile) (fn' : Ofence) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    pnodeStep m rs ib d (LLoad aq false base tvs []) m' ors fn' d' oib obar →
    tvs2.length = tvs.length →
    ∃ m2, pnodeStep m rs ib d (LLoad aq false base tvs2 []) m2 ors fn' d' oib obar := by
  intro h hts
  match m, h with
  | .pure _, h => obtain ⟨_, h, _⟩ := h; exact nomatch h
  | .impure (.error _) _, h => exact h.elim
  | .impure (.ok o) k, h =>
    cases o with
    | memRead n va req =>
      simp only [pnodeStep] at h ⊢
      split at h
      · obtain ⟨_, _, h, _⟩ := h; exact nomatch h
      · rename_i hd
        simp only [hd, Bool.false_eq_true, ↓reduceIte]
        rcases h with ⟨_, _, _, _, _, h, _⟩ | ⟨hif, ⟨hlat, w, tvs0, hlen, _, h, hrest⟩ |
          ⟨_, _, _, _, _, h, _⟩⟩
        · exact nomatch h
        · injection h with h1 _ h3 h4
          subst h1 h3 h4
          have hl2 : (tvs2.map Prod.snd).length = n := by
            rw [List.length_map, hts, hlen]
          obtain ⟨w2, hw2⟩ := bvOfBytes n _ hl2
          exact ⟨k (.Ok (w2, none)),
            Or.inr ⟨hif, Or.inl ⟨hlat, w2, tvs2, hts.trans hlen, hw2, rfl, rfl, hrest.2⟩⟩⟩
        · exact nomatch h
    | memWrite n va req =>
      simp only [pnodeStep] at h
      split at h
      · split at h
        · obtain ⟨_, h, _⟩ := h; exact nomatch h
        · exact h.elim
      · split at h
        · rcases h with ⟨_, ⟨_, h, _⟩ | ⟨_, ⟨h, _⟩ | ⟨h, _⟩⟩⟩ <;> exact nomatch h
        · exact h.elim
    | regWrite r v =>
      obtain ⟨h, _⟩ := h
      rcases erwLabelCases (erwOf (depsOfIb ib.ibBits) ib.ibRds r) with h' | ⟨_, _, h'⟩ | ⟨_, h'⟩ <;>
        rw [h'] at h <;> exact nomatch h
    | barrier b =>
      obtain ⟨h, _⟩ := h
      obtain ⟨_, _, _, _, h'⟩ := ebarLabelFence b
      rw [h'] at h; exact nomatch h
    | choose p => obtain ⟨_, h, _⟩ := h; exact nomatch h
    | readRam => exact h.elim
    | writeRam => exact h.elim
    | regRead => exact nomatch h.1
    | cacheOp => exact nomatch h.1
    | tlbi => exact nomatch h.1
    | translationStart => exact nomatch h.1
    | translationEnd => exact nomatch h.1
    | takeException => exact nomatch h.1
    | returnException => exact nomatch h.1
    | cycleCount => exact nomatch h.1
    | getCycleCount => exact nomatch h.1
    | message => exact nomatch h.1
    | instrAnnounce => exact nomatch h.1
    | branchAnnounce => exact nomatch h.1

theorem pstepEvLoadSubst (cpu : CPU) (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch)
    (d : Efab) (aq : Bool) (base : Int) (tvs tvs2 : List (Nat × BitVec 8)) (m' : SailM Unit)
    (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) (d' : Efab) :
    pstepEv (.PHart cpu m rs fn ib) d (LLoad aq false base tvs []) (.PHart cpu m' rs' fn' ib') d' →
    tvs2.length = tvs.length →
    ∃ m2, pstepEv (.PHart cpu m rs fn ib) d (LLoad aq false base tvs2 [])
            (.PHart cpu m2 rs' fn' ib') d' := by
  rintro ⟨-, ors, oib, obar, hrs, hib, ⟨hn, hd⟩ | ⟨_, _, _, _, h, _⟩⟩ hts
  · rcases fn with _ | ⟨pr, pw, sr, sw⟩
    · obtain ⟨m2, hn2⟩ := pnodeStepLoadSubst m rs ib d.efDev aq base tvs tvs2 m' ors fn'
        d'.efDev oib obar hn hts
      exact ⟨m2, rfl, ors, oib, obar, hrs, hib, Or.inl ⟨hn2, hd⟩⟩
    · exact nomatch hn.1
  · exact nomatch h

/-! # 3. Deliverable (1): `certStep` -/

/-! ## 3.1 The node is not a memory read (or its answers are taken equal) -/

theorem certStepMirror (P : Nat → Prop) (cpu : CPU) (m : SailM Unit) (rs1 rs2 : RegFile)
    (fn : Ofence) (ib : Ibch) (d : Efab) (l : Wlabel) (m' : SailM Unit) (rs1' : RegFile)
    (fn' : Ofence) (ib' : Ibch) (d' : Efab) :
    rdsOk P (pnodeRds m) →
    dregAgree P rs1 rs2 →
    pstepEv (.PHart cpu m rs1 fn ib) d l (.PHart cpu m' rs1' fn' ib') d' →
    ∃ rs2', pstepEv (.PHart cpu m rs2 fn ib) d l (.PHart cpu m' rs2' fn' ib') d' ∧
      dregAgree P rs1' rs2' :=
  fun hrds hag hst => pstepEvDagree P cpu m rs1 rs2 fn ib d l m' rs1' fn' ib' d' hrds hag hst

/-! ## 3.2 A plain load whose G-source IS in the log -/

theorem certStepReindex (P : Nat → Prop) (cpu : CPU) (m : SailM Unit) (rs1 rs2 : RegFile)
    (fn : Ofence) (ib : Ibch) (d : Efab) (aq : Bool) (base : Int)
    (tvs tvs2 : List (Nat × BitVec 8)) (m' : SailM Unit) (rs1' : RegFile) (fn' : Ofence)
    (ib' : Ibch) (d' : Efab) :
    rdsOk P (pnodeRds m) →
    dregAgree P rs1 rs2 →
    pstepEv (.PHart cpu m rs1 fn ib) d (LLoad aq false base tvs [])
      (.PHart cpu m' rs1' fn' ib') d' →
    tvs2.map Prod.snd = tvs.map Prod.snd →
    ∃ rs2', pstepEv (.PHart cpu m rs2 fn ib) d (LLoad aq false base tvs2 [])
              (.PHart cpu m' rs2' fn' ib') d' ∧
      dregAgree P rs1' rs2' := by
  intro hrds hag hst hts
  obtain ⟨rs2', hst2, hag2⟩ := pstepEvDagree P cpu m rs1 rs2 fn ib d _ m' rs1' fn' ib' d'
    hrds hag hst
  exact ⟨rs2', pstepEvTsLoad _ _ _ _ _ _ _ _ hst2 hts, hag2⟩

/-! ## 3.3 A plain load whose G-source is NOT in the log (a WITNESS) -/

theorem certStepWitness (P : Nat → Prop) (cpu : CPU) (m : SailM Unit) (rs1 rs2 : RegFile)
    (fn : Ofence) (ib : Ibch) (d : Efab) (aq : Bool) (base : Int)
    (tvs tvs2 : List (Nat × BitVec 8)) (m' : SailM Unit) (rs1' : RegFile) (fn' : Ofence)
    (ib' : Ibch) (d' : Efab) :
    rdsOk P (pnodeRds m) →
    dregAgree P rs1 rs2 →
    pstepEv (.PHart cpu m rs1 fn ib) d (LLoad aq false base tvs [])
      (.PHart cpu m' rs1' fn' ib') d' →
    tvs2.length = tvs.length →
    ∃ m2 rs2', pstepEv (.PHart cpu m rs2 fn ib) d (LLoad aq false base tvs2 [])
                 (.PHart cpu m2 rs2' fn' ib') d' ∧
      dregAgree P rs1' rs2' := by
  intro hrds hag hst hlen
  obtain ⟨rs2', hst2, hag2⟩ := pstepEvDagree P cpu m rs1 rs2 fn ib d _ m' rs1' fn' ib' d'
    hrds hag hst
  obtain ⟨m2, hst3⟩ := pstepEvLoadSubst cpu m rs2 fn ib d aq base tvs tvs2 m' rs2' fn' ib' d'
    hst2 hlen
  exact ⟨m2, rs2', hst3, hag2⟩

/-! ## 3.4 The block / instruction seam -/

theorem instrRdsOfChannel (T : List Nat) (cpu : CPU) (ls : List Wlabel) (rds : List Nat)
    (wrs : List Register) (ann : Bool) (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch)
    (d : Efab) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) (d' : Efab) :
    phrun cpu ls rds wrs ann m rs fn ib d m' rs' fn' ib' d' →
    LInstr ∉ ls →
    (∀ n, n ∈ ib'.ibRds → n ∉ T) →
    rdsOk (fun n => n ∉ T) rds := by
  intro hrun hni hib n hn
  apply hib
  rw [phrunIbRds cpu ls rds wrs ann m rs fn ib d m' rs' fn' ib' d' hrun
    (phrunNoInstr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrun hni)]
  exact List.mem_append_right _ hn

/-! ## 3.5 The taint growth, at the step's OWN annotation -/

theorem certStepTaint (T : List Nat) (rd : Nat) (cpu : CPU)
    (ls1 : List Wlabel) (rds1 : List Nat) (wrs1 : List Register) (ann1 : Bool)
    (ma1 : SailM Unit) (rsa1 : RegFile) (fna1 : Ofence) (iba1 : Ibch) (da1 : Efab)
    (mb1 : SailM Unit) (rsb1 : RegFile) (fnb1 : Ofence) (ibb1 : Ibch) (db1 : Efab)
    (ls2 : List Wlabel) (rds2 : List Nat) (wrs2 : List Register) (ann2 : Bool)
    (ma2 : SailM Unit) (rsa2 : RegFile) (fna2 : Ofence) (iba2 : Ibch) (da2 : Efab)
    (mb2 : SailM Unit) (rsb2 : RegFile) (fnb2 : Ofence) (ibb2 : Ibch) (db2 : Efab) :
    dregAgree (fun n => n ∉ T) rsa1 rsa2 →
    phrun cpu ls1 rds1 wrs1 ann1 ma1 rsa1 fna1 iba1 da1 mb1 rsb1 fnb1 ibb1 db1 →
    phrun cpu ls2 rds2 wrs2 ann2 ma2 rsa2 fna2 iba2 da2 mb2 rsb2 fnb2 ibb2 db2 →
    (∀ r, r ∈ wrs1 ++ wrs2 → ∃ n, eregNum r = some n ∧ n ∈ rd :: T) →
    dregAgree (fun n => n ∉ rd :: T) rsb1 rsb2 :=
  fun hag h1 h2 hws => taintClosureLoad T rd cpu ls1 rds1 wrs1 ann1 ma1 rsa1 fna1 iba1 da1 mb1
    rsb1 fnb1 ibb1 db1 cpu ls2 rds2 wrs2 ann2 ma2 rsa2 fna2 iba2 da2 mb2 rsb2 fnb2 ibb2 db2
    hag h1 h2 hws

/-! # 4. Deliverable (2): `certBlock` -/

/-- (Lean-only, deviation 4) Rocq's `cblk` with the admin-label predicate abstracted to `A`. -/
def WeakRvwmoCert2.cblkG (A : Wlabel → Prop) (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl)
    (l : Wlabel) (rds : List Nat) (wrs : List Register) (m : SailM Unit) (rs : RegFile)
    (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) :
    Prop :=
  ∃ (ls : List Wlabel) (ma : SailM Unit) (rsa : RegFile) (fna : Ofence) (iba : Ibch) (da : Efab)
    (rdsA : List Nat) (wrsA : List Register) (annA : Bool) (rdsB : List Nat)
    (wrsB : List Register) (annB : Bool),
    (∀ l0, l0 ∈ ls → A l0) ∧
    phrun cpu ls rdsA wrsA annA m rs fn ib d0 ma rsa fna iba da ∧
    hlblRealizes (.PHart cpu ma rsa fna iba) ws lb l ∧
    phrun cpu [l] rdsB wrsB annB ma rsa fna iba da m' rs' fn' ib' d0 ∧
    rds = rdsA ++ rdsB ∧ wrs = wrsA ++ wrsB

/-- ONE `hemit` block with its run's annotations exposed (deviation 4: `cblkG (lbAdmin true)`,
definitionally Rocq's body). -/
def cblk (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl) (l : Wlabel) (rds : List Nat)
    (wrs : List Register) (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch)
    (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) : Prop :=
  WeakRvwmoCert2.cblkG (lbAdmin true) cpu d0 ws lb l rds wrs m rs fn ib m' rs' fn' ib'


/-- (Lean-only, deviation 4) A PINNED admin label: administrative, and pinned to `im`. -/
def WeakRvwmoCert2.lbPin (im : Image) (l : Wlabel) : Prop :=
  lbAdmin true l ∧ WeakAxRealize.fetchPin im l

/-- (Lean-only, deviation 4) THE PINNED BLOCK: its admin labels are pinned to `im`. -/
def WeakRvwmoCert2.cblkPin (im : Image) (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl)
    (l : Wlabel) (rds : List Nat) (wrs : List Register) (m : SailM Unit) (rs : RegFile)
    (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) :
    Prop :=
  WeakRvwmoCert2.cblkG (WeakRvwmoCert2.lbPin im) cpu d0 ws lb l rds wrs m rs fn ib m' rs' fn' ib'

/-- (Lean-only, deviation 4) Every label of an item list is pinned to `im`
(`emFetchImg im em` is `esPin im em.emItems`). -/
def WeakRvwmoCert2.esPin (im : Image) (es : List Eitem) : Prop :=
  ∀ l0, l0 ∈ es.map Prod.fst → WeakAxRealize.fetchPin im l0

/-- (Lean-only, deviation 4) The pin, split at one block. -/
theorem WeakRvwmoCert2.esPinBlock (im : Image) (ls : List Wlabel) (l : Wlabel) (k : Nat)
    (es : List Eitem) :
    WeakRvwmoCert2.esPin im (eadm ls ++ (l, some k) :: es) →
    (∀ l0, l0 ∈ ls → WeakAxRealize.fetchPin im l0) ∧ WeakRvwmoCert2.esPin im es := by
  intro h
  unfold WeakRvwmoCert2.esPin at h
  rw [eblockFst] at h
  exact ⟨fun l0 hl => h l0 (List.mem_append_left _ hl),
    fun l0 hl => h l0 (List.mem_append_right _ (List.mem_cons_of_mem _ hl))⟩

/-! ## 4.1 `cblk` and the `hemit` block are the same object -/

theorem pevrunNilInv (p : Pexv6) (d : Efab) (p' : Pexv6) (d' : Efab) :
    pevrun [] p d p' d' → p' = p ∧ d' = d := by
  intro h
  cases h
  exact ⟨rfl, rfl⟩

theorem pevrunSingleInv (l : Wlabel) (p : Pexv6) (d : Efab) (p' : Pexv6) (d' : Efab) :
    pevrun [l] p d p' d' → pstepEv p d l p' d' := by
  intro h
  cases h with
  | more hs hr =>
    cases hr
    exact hs

theorem cblkIntro (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl) (l : Wlabel)
    (ls : List Wlabel) (pa : Pexv6) (da : Efab) (m : SailM Unit) (rs : RegFile) (fn : Ofence)
    (ib : Ibch) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) :
    admRun true (.PHart cpu m rs fn ib) d0 ls pa da →
    hlblRealizes pa ws lb l →
    pstepEv pa da l (.PHart cpu m' rs' fn' ib') d0 →
    ∃ rds wrs, cblk cpu d0 ws lb l rds wrs m rs fn ib m' rs' fn' ib' := by
  intro har hre hst
  obtain ⟨ma, rsa, fna, iba, rfl⟩ := admRunPhart true _ _ d0 ls da har cpu m rs fn ib rfl
  obtain ⟨rdsA, wrsA, annA, hA⟩ := pevrunPhrun ls _ d0 _ da
    (admRunPevrun _ _ _ _ _ _ har) cpu m rs fn ib ma rsa fna iba rfl rfl
  obtain ⟨rdsB, wrsB, annB, hB⟩ := pevrunPhrun [l] _ da _ d0
    (pevrun.more hst (pevrun.nil _ _)) cpu ma rsa fna iba m' rs' fn' ib' rfl rfl
  exact ⟨rdsA ++ rdsB, wrsA ++ wrsB, ls, ma, rsa, fna, iba, da, rdsA, wrsA, annA, rdsB, wrsB,
    annB, admRunAdmin _ _ _ _ _ _ har, hA, hre, hB, rfl, rfl⟩

theorem cblkElim (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl) (l : Wlabel) (rds : List Nat)
    (wrs : List Register) (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch)
    (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) :
    cblk cpu d0 ws lb l rds wrs m rs fn ib m' rs' fn' ib' →
    ∃ ls pa da, admRun true (.PHart cpu m rs fn ib) d0 ls pa da ∧
      hlblRealizes pa ws lb l ∧
      pstepEv pa da l (.PHart cpu m' rs' fn' ib') d0 := by
  rintro ⟨ls, ma, rsa, fna, iba, da, rdsA, wrsA, annA, rdsB, wrsB, annB, hadm, hA, hre, hB, -, -⟩
  exact ⟨ls, .PHart cpu ma rsa fna iba, da,
    pevrunAdmRun true _ d0 ls _ da (phrunPevrun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA) hadm, hre,
    pevrunSingleInv _ _ _ _ _ (phrunPevrun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB)⟩

/-- (Lean-only, deviation 4) Forget the pins. -/
theorem WeakRvwmoCert2.cblkPinCblk (im : Image) (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl)
    (l : Wlabel) (rds : List Nat) (wrs : List Register) (m : SailM Unit) (rs : RegFile)
    (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) :
    WeakRvwmoCert2.cblkPin im cpu d0 ws lb l rds wrs m rs fn ib m' rs' fn' ib' →
    cblk cpu d0 ws lb l rds wrs m rs fn ib m' rs' fn' ib' := by
  rintro ⟨ls, ma, rsa, fna, iba, da, rdsA, wrsA, annA, rdsB, wrsB, annB, hadm, hA, hre, hB,
    h1, h2⟩
  exact ⟨ls, ma, rsa, fna, iba, da, rdsA, wrsA, annA, rdsB, wrsB, annB,
    fun l0 h => (hadm l0 h).1, hA, hre, hB, h1, h2⟩

/-- (Lean-only, deviation 4) `cblkIntro` of a run whose admin labels are pinned. -/
theorem WeakRvwmoCert2.cblkIntroPin (im : Image) (cpu : CPU) (d0 : Efab) (ws : Wstate)
    (lb : Lbl) (l : Wlabel) (ls : List Wlabel) (pa : Pexv6) (da : Efab) (m : SailM Unit)
    (rs : RegFile) (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence)
    (ib' : Ibch) :
    admRun true (.PHart cpu m rs fn ib) d0 ls pa da →
    (∀ l0, l0 ∈ ls → WeakAxRealize.fetchPin im l0) →
    hlblRealizes pa ws lb l →
    pstepEv pa da l (.PHart cpu m' rs' fn' ib') d0 →
    ∃ rds wrs, WeakRvwmoCert2.cblkPin im cpu d0 ws lb l rds wrs m rs fn ib m' rs' fn' ib' := by
  intro har hpin hre hst
  obtain ⟨ma0, rsa0, fna0, iba0, rfl⟩ := admRunPhart true _ _ d0 ls da har cpu m rs fn ib rfl
  obtain ⟨rdsA0, wrsA0, annA0, hA0⟩ := pevrunPhrun ls _ d0 _ da
    (admRunPevrun _ _ _ _ _ _ har) cpu m rs fn ib ma0 rsa0 fna0 iba0 rfl rfl
  obtain ⟨rdsB0, wrsB0, annB0, hB0⟩ := pevrunPhrun [l] _ da _ d0
    (pevrun.more hst (pevrun.nil _ _)) cpu ma0 rsa0 fna0 iba0 m' rs' fn' ib' rfl rfl
  exact ⟨rdsA0 ++ rdsB0, wrsA0 ++ wrsB0, ls, ma0, rsa0, fna0, iba0, da, rdsA0, wrsA0, annA0,
    rdsB0, wrsB0, annB0, fun l0 h => ⟨admRunAdmin _ _ _ _ _ _ har l0 h, hpin l0 h⟩, hA0, hre,
    hB0, rfl, rfl⟩

/-- (Lean-only, deviation 4) `cblkElim`, keeping the pins. -/
theorem WeakRvwmoCert2.cblkElimPin (im : Image) (cpu : CPU) (d0 : Efab) (ws : Wstate)
    (lb : Lbl) (l : Wlabel) (rds : List Nat) (wrs : List Register) (m : SailM Unit)
    (rs : RegFile) (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence)
    (ib' : Ibch) :
    WeakRvwmoCert2.cblkPin im cpu d0 ws lb l rds wrs m rs fn ib m' rs' fn' ib' →
    ∃ ls pa da, admRun true (.PHart cpu m rs fn ib) d0 ls pa da ∧
      (∀ l0, l0 ∈ ls → WeakAxRealize.fetchPin im l0) ∧
      hlblRealizes pa ws lb l ∧
      pstepEv pa da l (.PHart cpu m' rs' fn' ib') d0 := by
  rintro ⟨ls, ma, rsa, fna, iba, da, rdsA, wrsA, annA, rdsB, wrsB, annB, hadm, hA, hre, hB, -, -⟩
  exact ⟨ls, .PHart cpu ma rsa fna iba, da,
    pevrunAdmRun true _ d0 ls _ da (phrunPevrun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA)
      (fun l0 h => (hadm l0 h).1), fun l0 h => (hadm l0 h).2, hre,
    pevrunSingleInv _ _ _ _ _ (phrunPevrun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB)⟩

/-- (Lean-only, deviation 4) `cblkRelp` at any admin predicate `A`. -/
theorem WeakRvwmoCert2.cblkRelpG (A : Wlabel → Prop)
    (cpu : CPU) (d0 : Efab) (ws ws' : Wstate) (lb : Lbl) (l : Wlabel)
    (rds : List Nat) (wrs : List Register) (m : SailM Unit) (rs : RegFile) (fn : Ofence)
    (ib : Ibch) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) :
    ws'.wRelp = ws.wRelp →
    WeakRvwmoCert2.cblkG A cpu d0 ws lb l rds wrs m rs fn ib m' rs' fn' ib' →
    WeakRvwmoCert2.cblkG A cpu d0 ws' lb l rds wrs m rs fn ib m' rs' fn' ib' := by
  rintro hr ⟨ls, ma, rsa, fna, iba, da, rdsA, wrsA, annA, rdsB, wrsB, annB, hadm, hA, hre, hB,
    rfl, rfl⟩
  exact ⟨ls, ma, rsa, fna, iba, da, rdsA, wrsA, annA, rdsB, wrsB, annB, hadm, hA,
    hlblRealizesRelp _ _ _ _ _ hr hre, hB, rfl, rfl⟩

/-- The projection equation inside a block reads the wstate only through `wRelp`. -/
theorem cblkRelp (cpu : CPU) (d0 : Efab) (ws ws' : Wstate) (lb : Lbl) (l : Wlabel)
    (rds : List Nat) (wrs : List Register) (m : SailM Unit) (rs : RegFile) (fn : Ofence)
    (ib : Ibch) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) :
    ws'.wRelp = ws.wRelp →
    cblk cpu d0 ws lb l rds wrs m rs fn ib m' rs' fn' ib' →
    cblk cpu d0 ws' lb l rds wrs m rs fn ib m' rs' fn' ib' :=
  WeakRvwmoCert2.cblkRelpG (lbAdmin true) cpu d0 ws ws' lb l rds wrs m rs fn ib m' rs' fn' ib'

/-! ## 4.2 The block, transported -/

/-- (Lean-only, deviation 4) `certBlockMirror` at any admin predicate `A`. -/
theorem WeakRvwmoCert2.certBlockMirrorG (A : Wlabel → Prop)
    (P : Nat → Prop) (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl)
    (l : Wlabel) (rds : List Nat) (wrs : List Register) (m : SailM Unit) (rs1 : RegFile)
    (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs1' : RegFile) (fn' : Ofence) (ib' : Ibch)
    (rs2 : RegFile) :
    WeakRvwmoCert2.cblkG A cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
    rdsOk P rds →
    dregAgree P rs1 rs2 →
    ∃ rs2', WeakRvwmoCert2.cblkG A cpu d0 ws lb l rds wrs m rs2 fn ib m' rs2' fn' ib' ∧ dregAgree P rs1' rs2' := by
  rintro ⟨ls, ma, rsa, fna, iba, da, rdsA, wrsA, annA, rdsB, wrsB, annB, hadm, hA, hre, hB,
    rfl, rfl⟩ hrds hag
  obtain ⟨hrdsA, hrdsB⟩ := rdsOkApp P _ _ hrds
  obtain ⟨rsa2, hA2, haga⟩ := phrunDagree P cpu ls rdsA wrsA annA m rs1 fn ib d0 ma rsa fna iba
    da hA hrdsA rs2 hag
  obtain ⟨rs2', hB2, hag2⟩ := phrunDagree P cpu [l] rdsB wrsB annB ma rsa fna iba da m' rs1' fn'
    ib' d0 hB hrdsB rsa2 haga
  exact ⟨rs2', ⟨ls, ma, rsa2, fna, iba, da, rdsA, wrsA, annA, rdsB, wrsB, annB, hadm, hA2,
    hlblRealizesRs _ _ _ _ _ _ _ _ _ _ _ hre, hB2, rfl, rfl⟩, hag2⟩

/-- THE MIRROR: the block reads no tainted carrier, so the certified hart runs it step for step. -/
theorem certBlockMirror (P : Nat → Prop) (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl)
    (l : Wlabel) (rds : List Nat) (wrs : List Register) (m : SailM Unit) (rs1 : RegFile)
    (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs1' : RegFile) (fn' : Ofence) (ib' : Ibch)
    (rs2 : RegFile) :
    cblk cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
    rdsOk P rds →
    dregAgree P rs1 rs2 →
    ∃ rs2', cblk cpu d0 ws lb l rds wrs m rs2 fn ib m' rs2' fn' ib' ∧ dregAgree P rs1' rs2' :=
  WeakRvwmoCert2.certBlockMirrorG (lbAdmin true) P cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn'
    ib' rs2

/-! ## 4.3 The two read policies, at the block -/

/-- The label correspondence the certification delivers: the candidate's own timestamps, the
row's everything else. -/
def lblReidx (lb lb' : Lbl) : Prop :=
  match lb with
  | .LLoad aq base ts vs =>
      match lb' with
      | .LLoad aq' base' ts' vs' => aq' = aq ∧ base' = base ∧ vs' = vs ∧ ts'.length = ts.length
      | _ => False
  | .LRmw aq rl base ts rvs wvs kc =>
      match lb' with
      | .LRmw aq' rl' base' ts' rvs' wvs' kc' =>
          aq' = aq ∧ rl' = rl ∧ base' = base ∧ rvs' = rvs ∧ wvs' = wvs ∧ kc' = kc ∧
          ts'.length = ts.length
      | _ => False
  | _ => lb' = lb

theorem lblReidxRefl (lb : Lbl) : lblReidx lb lb := by
  cases lb <;> simp [lblReidx]

/-- THE EXIT WRITE IS VERBATIM. -/
theorem lblReidxStore (rl : Bool) (base : Int) (vs : List (BitVec 8)) (kc : WmClass) (lb' : Lbl) :
    lblReidx (.LStore rl base vs kc) lb' → lb' = .LStore rl base vs kc :=
  fun h => h

theorem lblReidxFence (pr pw sr sw : Bool) (lb' : Lbl) :
    lblReidx (.LFence pr pw sr sw) lb' → lb' = .LFence pr pw sr sw :=
  fun h => h

theorem lblReidxRelp (b : Bool) (lb lb' : Lbl) :
    lblReidx lb lb' → lpostRelp b lb' = lpostRelp b lb := by
  cases lb <;> cases lb' <;> intro h <;> simp only [lblReidx, reduceCtorEq] at h
  all_goals first
    | rfl
    | (obtain ⟨-, -, -, -, rfl, -⟩ := h; rfl)
    | (subst h; rfl)

/-- The witness-aware correspondence: same footprint, PLAIN, arbitrary values. -/
def lblReidxSub (lb lb' : Lbl) : Prop :=
  match lb with
  | .LLoad aq base ts _ =>
      match lb' with
      | .LLoad aq' base' ts' vs' =>
          aq = false ∧ aq' = false ∧ base' = base ∧ ts'.length = ts.length ∧
          vs'.length = ts'.length
      | _ => False
  | _ => False

/-- THE THIRD ARM: a poisoned block (only a load). -/
def lblPoisoned (lb lb' : Lbl) : Prop :=
  match lb with
  | .LLoad _ _ _ _ =>
      match lb' with
      | .LLoad aq' _ ts' vs' => aq' = false ∧ vs'.length = ts'.length
      | _ => False
  | _ => False

theorem lblPoisonedNotw (lb lb' : Lbl) :
    lblPoisoned lb lb' → lbIsW lb = false ∧ lbIsW lb' = false := by
  cases lb <;> cases lb' <;> simp [lblPoisoned, lbIsW]

def lblReidxW (lb lb' : Lbl) : Prop :=
  lblReidx lb lb' ∨ lblReidxSub lb lb' ∨ lblPoisoned lb lb'

theorem lblReidxWRefl (lb : Lbl) : lblReidxW lb lb := Or.inl (lblReidxRefl lb)

theorem lblReidxWOf (lb lb' : Lbl) : lblReidx lb lb' → lblReidxW lb lb' := Or.inl

theorem lblReidxWPois (lb lb' : Lbl) : lblPoisoned lb lb' → lblReidxW lb lb' :=
  fun h => Or.inr (Or.inr h)

/-- THE EXIT WRITE IS STILL VERBATIM. -/
theorem lblReidxWStore (rl : Bool) (base : Int) (vs : List (BitVec 8)) (kc : WmClass)
    (lb' : Lbl) :
    lblReidxW (.LStore rl base vs kc) lb' → lb' = .LStore rl base vs kc := by
  rintro (h | h | h)
  · exact h
  · exact h.elim
  · exact h.elim

theorem lblReidxWFence (pr pw sr sw : Bool) (lb' : Lbl) :
    lblReidxW (.LFence pr pw sr sw) lb' → lb' = .LFence pr pw sr sw := by
  rintro (h | h | h)
  · exact h
  · exact h.elim
  · exact h.elim

theorem lblReidxSubRelp (b : Bool) (lb lb' : Lbl) :
    lblReidxSub lb lb' → lpostRelp b lb' = lpostRelp b lb := by
  cases lb <;> cases lb' <;> simp [lblReidxSub, lpostRelp]

theorem lblPoisonedRelp (b : Bool) (lb lb' : Lbl) :
    lblPoisoned lb lb' → lpostRelp b lb' = lpostRelp b lb := by
  cases lb <;> cases lb' <;> simp [lblPoisoned, lpostRelp]

theorem lblReidxWRelp (b : Bool) (lb lb' : Lbl) :
    lblReidxW lb lb' → lpostRelp b lb' = lpostRelp b lb := by
  rintro (h | h | h)
  · exact lblReidxRelp b lb lb' h
  · exact lblReidxSubRelp b lb lb' h
  · exact lblPoisonedRelp b lb lb' h

/-- … and it moves neither the write bit nor, therefore, the message. -/
theorem lblReidxWIsw (lb lb' : Lbl) : lblReidxW lb lb' → lbIsW lb' = lbIsW lb := by
  cases lb <;> cases lb' <;>
    simp only [lblReidxW, lblReidx, lblReidxSub, lblPoisoned, lbIsW, reduceCtorEq, or_false,
      imp_self, implies_true]

theorem lblReidxWNotw (lb lb' : Lbl) :
    lblReidxW lb lb' → lbIsW lb = false → lbIsW lb' = false := by
  intro h hw
  rw [lblReidxWIsw lb lb' h, hw]

/-- The load block's two ends, computed. -/
theorem hlblRealizesLoad (p : Pexv6) (ws : Wstate) (aq : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) :
    hlblRealizes p ws (.LLoad aq base (tvs.map Prod.fst) (tvs.map Prod.snd))
      (LLoad aq false base tvs []) :=
  ⟨trivial, rfl, rfl, rfl⟩

theorem hlblRealizesLoadInv (p : Pexv6) (ws : Wstate) (lb : Lbl) (aq : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) :
    hlblRealizes p ws lb (LLoad aq false base tvs []) →
    lb = .LLoad aq base (tvs.map Prod.fst) (tvs.map Prod.snd) := by
  rintro ⟨-, -, -, hpr⟩
  exact (Option.some.inj hpr).symm

/-- (Lean-only, deviation 4) `cblkRetime` at any admin predicate `A`. -/
theorem WeakRvwmoCert2.cblkRetimeG (A : Wlabel → Prop)
    (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl) (rds : List Nat)
    (wrs : List Register) (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch)
    (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) (aq : Bool) (base : Int)
    (tvs tvs2 : List (Nat × BitVec 8)) :
    WeakRvwmoCert2.cblkG A cpu d0 ws lb (LLoad aq false base tvs []) rds wrs m rs fn ib m' rs' fn' ib' →
    tvs2.map Prod.snd = tvs.map Prod.snd →
    ∃ rds2 wrs2,
      WeakRvwmoCert2.cblkG A cpu d0 ws (.LLoad aq base (tvs2.map Prod.fst) (tvs2.map Prod.snd))
        (LLoad aq false base tvs2 []) rds2 wrs2 m rs fn ib m' rs' fn' ib' := by
  rintro ⟨ls, ma, rsa, fna, iba, da, rdsA, wrsA, annA, rdsB, wrsB, annB, hadm, hA, -, hB,
    rfl, rfl⟩ hts
  have hst : pstepEv (.PHart cpu ma rsa fna iba) da (LLoad aq false base tvs2 [])
      (.PHart cpu m' rs' fn' ib') d0 :=
    pstepEvTsLoad _ _ _ _ _ _ _ _
      (pevrunSingleInv _ _ _ _ _ (phrunPevrun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB)) hts
  obtain ⟨rdsB2, wrsB2, annB2, hB2⟩ := pevrunPhrun [_] _ da _ d0
    (pevrun.more hst (pevrun.nil _ _)) cpu ma rsa fna iba m' rs' fn' ib' rfl rfl
  exact ⟨rdsA ++ rdsB2, wrsA ++ wrsB2, ls, ma, rsa, fna, iba, da, rdsA, wrsA, annA, rdsB2,
    wrsB2, annB2, hadm, hA, hlblRealizesLoad _ _ _ _ _, hB2, rfl, rfl⟩

/-- RE-TIMESTAMPING a load block: same values, the candidate's indices, nothing else moves. -/
theorem cblkRetime (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl) (rds : List Nat)
    (wrs : List Register) (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch)
    (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) (aq : Bool) (base : Int)
    (tvs tvs2 : List (Nat × BitVec 8)) :
    cblk cpu d0 ws lb (LLoad aq false base tvs []) rds wrs m rs fn ib m' rs' fn' ib' →
    tvs2.map Prod.snd = tvs.map Prod.snd →
    ∃ rds2 wrs2,
      cblk cpu d0 ws (.LLoad aq base (tvs2.map Prod.fst) (tvs2.map Prod.snd))
        (LLoad aq false base tvs2 []) rds2 wrs2 m rs fn ib m' rs' fn' ib' :=
  WeakRvwmoCert2.cblkRetimeG (lbAdmin true) cpu d0 ws lb rds wrs m rs fn ib m' rs' fn' ib' aq base
    tvs tvs2

/-- (Lean-only, deviation 4) `cblkSubst` at any admin predicate `A`. -/
theorem WeakRvwmoCert2.cblkSubstG (A : Wlabel → Prop)
    (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl) (rds : List Nat)
    (wrs : List Register) (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch)
    (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) (aq : Bool) (base : Int)
    (tvs tvs2 : List (Nat × BitVec 8)) :
    WeakRvwmoCert2.cblkG A cpu d0 ws lb (LLoad aq false base tvs []) rds wrs m rs fn ib m' rs' fn' ib' →
    tvs2.length = tvs.length →
    ∃ m2 rds2 wrs2,
      WeakRvwmoCert2.cblkG A cpu d0 ws (.LLoad aq base (tvs2.map Prod.fst) (tvs2.map Prod.snd))
        (LLoad aq false base tvs2 []) rds2 wrs2 m rs fn ib m2 rs' fn' ib' := by
  rintro ⟨ls, ma, rsa, fna, iba, da, rdsA, wrsA, annA, rdsB, wrsB, annB, hadm, hA, -, hB,
    rfl, rfl⟩ hlen
  have hst : pstepEv (.PHart cpu ma rsa fna iba) da (LLoad aq false base tvs [])
      (.PHart cpu m' rs' fn' ib') d0 :=
    pevrunSingleInv _ _ _ _ _ (phrunPevrun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB)
  obtain ⟨m2, hst2⟩ := pstepEvLoadSubst cpu ma rsa fna iba da aq base tvs tvs2 m' rs' fn' ib' d0
    hst hlen
  obtain ⟨rdsB2, wrsB2, annB2, hB2⟩ := pevrunPhrun [_] _ da _ d0
    (pevrun.more hst2 (pevrun.nil _ _)) cpu ma rsa fna iba m2 rs' fn' ib' rfl rfl
  exact ⟨m2, rdsA ++ rdsB2, wrsA ++ wrsB2, ls, ma, rsa, fna, iba, da, rdsA, wrsA, annA, rdsB2,
    wrsB2, annB2, hadm, hA, hlblRealizesLoad _ _ _ _ _, hB2, rfl, rfl⟩

/-- SUBSTITUTING a load block's values (a WITNESS): the successor NODE differs. -/
theorem cblkSubst (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl) (rds : List Nat)
    (wrs : List Register) (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch)
    (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) (aq : Bool) (base : Int)
    (tvs tvs2 : List (Nat × BitVec 8)) :
    cblk cpu d0 ws lb (LLoad aq false base tvs []) rds wrs m rs fn ib m' rs' fn' ib' →
    tvs2.length = tvs.length →
    ∃ m2 rds2 wrs2,
      cblk cpu d0 ws (.LLoad aq base (tvs2.map Prod.fst) (tvs2.map Prod.snd))
        (LLoad aq false base tvs2 []) rds2 wrs2 m rs fn ib m2 rs' fn' ib' :=
  WeakRvwmoCert2.cblkSubstG (lbAdmin true) cpu d0 ws lb rds wrs m rs fn ib m' rs' fn' ib' aq base
    tvs tvs2

/-! ## 4.3a The wlabel shape of a load block, and the shape-free retime -/

theorem hlblRealizesLoadShape (p : Pexv6) (ws : Wstate) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) (l : Wlabel) :
    hlblRealizes p ws (.LLoad aq base ts vs) l →
    ∃ tvs : List (Nat × BitVec 8),
      tvs.map Prod.fst = ts ∧ tvs.map Prod.snd = vs ∧
      (l = LLoad aq false base tvs [] ∨ ∃ asrc, l = LExLoad aq base tvs asrc) := by
  rintro ⟨_, hlat, hrf, hpr⟩
  cases l with
  | LLoad aq' lat base' tvs asrc =>
    simp only [projLbl, Option.some.injEq, Lbl.LLoad.injEq] at hpr
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hpr
    have hl : lat = false := hlat
    have hr : asrc = [] := hrf
    subst hl hr
    exact ⟨tvs, rfl, rfl, Or.inl rfl⟩
  | LExLoad aq' base' tvs asrc =>
    simp only [projLbl, Option.some.injEq, Lbl.LLoad.injEq] at hpr
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hpr
    exact ⟨tvs, rfl, rfl, Or.inr ⟨asrc, rfl⟩⟩
  | _ => simp [projLbl] at hpr

/-- (Lean-only, deviation 4) `cblkLoadRetime` at any admin predicate `A`. -/
theorem WeakRvwmoCert2.cblkLoadRetimeG (A : Wlabel → Prop)
    (cpu : CPU) (d0 : Efab) (ws : Wstate) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) (l : Wlabel) (rds : List Nat) (wrs : List Register)
    (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs' : RegFile)
    (fn' : Ofence) (ib' : Ibch) (tvs2 : List (Nat × BitVec 8)) :
    WeakRvwmoCert2.cblkG A cpu d0 ws (.LLoad aq base ts vs) l rds wrs m rs fn ib m' rs' fn' ib' →
    tvs2.map Prod.snd = vs →
    ∃ l2 rds2 wrs2,
      WeakRvwmoCert2.cblkG A cpu d0 ws (.LLoad aq base (tvs2.map Prod.fst) (tvs2.map Prod.snd)) l2 rds2 wrs2
        m rs fn ib m' rs' fn' ib' := by
  rintro ⟨ls, ma, rsa, fna, iba, da, rdsA, wrsA, annA, rdsB, wrsB, annB, hadm, hA, hre, hB,
    rfl, rfl⟩ hts
  have hst : pstepEv (.PHart cpu ma rsa fna iba) da l (.PHart cpu m' rs' fn' ib') d0 :=
    pevrunSingleInv _ _ _ _ _ (phrunPevrun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB)
  obtain ⟨tvs, -, hs, hl⟩ := hlblRealizesLoadShape _ ws aq base ts vs l hre
  have hts' : tvs2.map Prod.snd = tvs.map Prod.snd := by rw [hts, hs]
  rcases hl with rfl | ⟨asrc, rfl⟩
  · have hst2 := pstepEvTsLoad _ _ _ _ _ _ _ _ hst hts'
    obtain ⟨rdsB2, wrsB2, annB2, hB2⟩ := pevrunPhrun [_] _ da _ d0
      (pevrun.more hst2 (pevrun.nil _ _)) cpu ma rsa fna iba m' rs' fn' ib' rfl rfl
    exact ⟨_, rdsA ++ rdsB2, wrsA ++ wrsB2, ls, ma, rsa, fna, iba, da, rdsA, wrsA, annA, rdsB2,
      wrsB2, annB2, hadm, hA, hlblRealizesLoad _ _ _ _ _, hB2, rfl, rfl⟩
  · have hst2 := pstepEvTsExload _ _ _ _ _ _ _ _ _ hst hts'
    obtain ⟨rdsB2, wrsB2, annB2, hB2⟩ := pevrunPhrun [_] _ da _ d0
      (pevrun.more hst2 (pevrun.nil _ _)) cpu ma rsa fna iba m' rs' fn' ib' rfl rfl
    exact ⟨LExLoad aq base tvs2 asrc, rdsA ++ rdsB2, wrsA ++ wrsB2, ls, ma, rsa, fna, iba, da,
      rdsA, wrsA, annA, rdsB2, wrsB2, annB2, hadm, hA, ⟨trivial, trivial, trivial, rfl⟩, hB2,
      rfl, rfl⟩

theorem cblkLoadRetime (cpu : CPU) (d0 : Efab) (ws : Wstate) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) (l : Wlabel) (rds : List Nat) (wrs : List Register)
    (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs' : RegFile)
    (fn' : Ofence) (ib' : Ibch) (tvs2 : List (Nat × BitVec 8)) :
    cblk cpu d0 ws (.LLoad aq base ts vs) l rds wrs m rs fn ib m' rs' fn' ib' →
    tvs2.map Prod.snd = vs →
    ∃ l2 rds2 wrs2,
      cblk cpu d0 ws (.LLoad aq base (tvs2.map Prod.fst) (tvs2.map Prod.snd)) l2 rds2 wrs2
        m rs fn ib m' rs' fn' ib' :=
  WeakRvwmoCert2.cblkLoadRetimeG (lbAdmin true) cpu d0 ws aq base ts vs l rds wrs m rs fn ib m'
    rs' fn' ib' tvs2

/-! ## 4.3b The substitution's machine-side cost, named -/

def cblkVfree (cpu : CPU) (d0 : Efab) (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat)
    (_l : Wlabel) (_rds : List Nat) (_wrs : List Register) (m : SailM Unit) (rs : RegFile)
    (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) :
    Prop :=
  ∀ tvs2 : List (Nat × BitVec 8), tvs2.length = ts.length →
    ∃ l2 rds2 wrs2,
      cblk cpu d0 ws (.LLoad aq base (tvs2.map Prod.fst) (tvs2.map Prod.snd)) l2 rds2 wrs2
        m rs fn ib m' rs' fn' ib'

/-- THE DEGENERATE CASE: substituting the values already read costs nothing. -/
theorem cblkVfreeOfRetime (cpu : CPU) (d0 : Efab) (ws : Wstate) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) (l : Wlabel) (rds : List Nat) (wrs : List Register)
    (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs' : RegFile)
    (fn' : Ofence) (ib' : Ibch) :
    cblk cpu d0 ws (.LLoad aq base ts vs) l rds wrs m rs fn ib m' rs' fn' ib' →
    ∀ tvs2 : List (Nat × BitVec 8), tvs2.map Prod.snd = vs →
      ∃ l2 rds2 wrs2,
        cblk cpu d0 ws (.LLoad aq base (tvs2.map Prod.fst) (tvs2.map Prod.snd)) l2 rds2 wrs2
          m rs fn ib m' rs' fn' ib' :=
  fun hblk tvs2 hts => cblkLoadRetime cpu d0 ws aq base ts vs l rds wrs m rs fn ib m' rs' fn'
    ib' tvs2 hblk hts

/-- (Lean-only, deviation 4) `certBlockRead` at any admin predicate `A`. -/
theorem WeakRvwmoCert2.certBlockReadG (A : Wlabel → Prop)
    (P : Nat → Prop) (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl)
    (rds : List Nat) (wrs : List Register) (m : SailM Unit) (rs1 : RegFile) (fn : Ofence)
    (ib : Ibch) (m' : SailM Unit) (rs1' : RegFile) (fn' : Ofence) (ib' : Ibch) (rs2 : RegFile)
    (aq : Bool) (base : Int) (tvs tvs2 : List (Nat × BitVec 8)) :
    WeakRvwmoCert2.cblkG A cpu d0 ws lb (LLoad aq false base tvs []) rds wrs m rs1 fn ib m' rs1' fn' ib' →
    rdsOk P rds → dregAgree P rs1 rs2 → tvs2.map Prod.snd = tvs.map Prod.snd →
    ∃ rs2' rds2 wrs2,
      WeakRvwmoCert2.cblkG A cpu d0 ws (.LLoad aq base (tvs2.map Prod.fst) (tvs2.map Prod.snd))
        (LLoad aq false base tvs2 []) rds2 wrs2 m rs2 fn ib m' rs2' fn' ib' ∧
      lblReidx lb (.LLoad aq base (tvs2.map Prod.fst) (tvs2.map Prod.snd)) ∧
      dregAgree P rs1' rs2' := by
  intro hblk hrds hag hts
  have hlb : lb = .LLoad aq base (tvs.map Prod.fst) (tvs.map Prod.snd) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hre, _⟩ := hblk
    exact hlblRealizesLoadInv _ _ _ _ _ _ hre
  obtain ⟨rs2', hblk2, hag2⟩ := WeakRvwmoCert2.certBlockMirrorG A P cpu d0 ws lb _ rds wrs m rs1 fn ib m' rs1' fn'
    ib' rs2 hblk hrds hag
  obtain ⟨rds2, wrs2, hblk3⟩ := WeakRvwmoCert2.cblkRetimeG A cpu d0 ws lb rds wrs m rs2 fn ib m' rs2' fn' ib' aq
    base tvs tvs2 hblk2 hts
  refine ⟨rs2', rds2, wrs2, hblk3, ?_, hag2⟩
  subst hlb
  exact ⟨rfl, rfl, hts, by simp only [List.length_map]; exact lenOfSnd hts⟩

/-- THE IN-LOG READ — the block, transported and retimed. -/
theorem certBlockRead (P : Nat → Prop) (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl)
    (rds : List Nat) (wrs : List Register) (m : SailM Unit) (rs1 : RegFile) (fn : Ofence)
    (ib : Ibch) (m' : SailM Unit) (rs1' : RegFile) (fn' : Ofence) (ib' : Ibch) (rs2 : RegFile)
    (aq : Bool) (base : Int) (tvs tvs2 : List (Nat × BitVec 8)) :
    cblk cpu d0 ws lb (LLoad aq false base tvs []) rds wrs m rs1 fn ib m' rs1' fn' ib' →
    rdsOk P rds → dregAgree P rs1 rs2 → tvs2.map Prod.snd = tvs.map Prod.snd →
    ∃ rs2' rds2 wrs2,
      cblk cpu d0 ws (.LLoad aq base (tvs2.map Prod.fst) (tvs2.map Prod.snd))
        (LLoad aq false base tvs2 []) rds2 wrs2 m rs2 fn ib m' rs2' fn' ib' ∧
      lblReidx lb (.LLoad aq base (tvs2.map Prod.fst) (tvs2.map Prod.snd)) ∧
      dregAgree P rs1' rs2' :=
  WeakRvwmoCert2.certBlockReadG (lbAdmin true) P cpu d0 ws lb rds wrs m rs1 fn ib m' rs1' fn' ib'
    rs2 aq base tvs tvs2

/-- (Lean-only, deviation 4) `certBlockWitness` at any admin predicate `A`. -/
theorem WeakRvwmoCert2.certBlockWitnessG (A : Wlabel → Prop)
    (P : Nat → Prop) (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl)
    (rds : List Nat) (wrs : List Register) (m : SailM Unit) (rs1 : RegFile) (fn : Ofence)
    (ib : Ibch) (m' : SailM Unit) (rs1' : RegFile) (fn' : Ofence) (ib' : Ibch) (rs2 : RegFile)
    (aq : Bool) (base : Int) (tvs tvs2 : List (Nat × BitVec 8)) :
    WeakRvwmoCert2.cblkG A cpu d0 ws lb (LLoad aq false base tvs []) rds wrs m rs1 fn ib m' rs1' fn' ib' →
    rdsOk P rds → dregAgree P rs1 rs2 → tvs2.length = tvs.length →
    ∃ m2 rs2' rds2 wrs2,
      WeakRvwmoCert2.cblkG A cpu d0 ws (.LLoad aq base (tvs2.map Prod.fst) (tvs2.map Prod.snd))
        (LLoad aq false base tvs2 []) rds2 wrs2 m rs2 fn ib m2 rs2' fn' ib' ∧
      dregAgree P rs1' rs2' := by
  intro hblk hrds hag hlen
  obtain ⟨rs2', hblk2, hag2⟩ := WeakRvwmoCert2.certBlockMirrorG A P cpu d0 ws lb _ rds wrs m rs1 fn ib m' rs1' fn'
    ib' rs2 hblk hrds hag
  obtain ⟨m2, rds2, wrs2, hblk3⟩ := WeakRvwmoCert2.cblkSubstG A cpu d0 ws lb rds wrs m rs2 fn ib m' rs2' fn' ib' aq
    base tvs tvs2 hblk2 hlen
  exact ⟨m2, rs2', rds2, wrs2, hblk3, hag2⟩

/-- THE WITNESS READ — the block, transported and SUBSTITUTED. -/
theorem certBlockWitness (P : Nat → Prop) (cpu : CPU) (d0 : Efab) (ws : Wstate) (lb : Lbl)
    (rds : List Nat) (wrs : List Register) (m : SailM Unit) (rs1 : RegFile) (fn : Ofence)
    (ib : Ibch) (m' : SailM Unit) (rs1' : RegFile) (fn' : Ofence) (ib' : Ibch) (rs2 : RegFile)
    (aq : Bool) (base : Int) (tvs tvs2 : List (Nat × BitVec 8)) :
    cblk cpu d0 ws lb (LLoad aq false base tvs []) rds wrs m rs1 fn ib m' rs1' fn' ib' →
    rdsOk P rds → dregAgree P rs1 rs2 → tvs2.length = tvs.length →
    ∃ m2 rs2' rds2 wrs2,
      cblk cpu d0 ws (.LLoad aq base (tvs2.map Prod.fst) (tvs2.map Prod.snd))
        (LLoad aq false base tvs2 []) rds2 wrs2 m rs2 fn ib m2 rs2' fn' ib' ∧
      dregAgree P rs1' rs2' :=
  WeakRvwmoCert2.certBlockWitnessG (lbAdmin true) P cpu d0 ws lb rds wrs m rs1 fn ib m' rs1' fn'
    ib' rs2 aq base tvs tvs2

/-! ## 4.4 The block, APPENDED -/

/-- Deviation 4: the pinned LTS and the pinned block. -/
theorem certBlockSnoc (c : Cand) (x : Nat) (pst : Nat → List Pexv6) (dv : Nat → Efab)
    (cpu : CPU) (d0 : Efab) (lb : Lbl) (l : Wlabel) (rds : List Nat) (wrs : List Register)
    (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs' : RegFile)
    (fn' : Ofence) (ib' : Ibch) :
    srvwmoConsistent c →
    execProgOk' (pstepPin c.cdImg pstepEv) pclsEv pst dv (candExec c) →
    (pst (cdEnd c))[x]? = some (.PHart cpu m rs fn ib) →
    dv (cdEnd c) = d0 →
    WeakRvwmoCert2.cblkPin c.cdImg cpu d0 ((candLastSt c).msWs x) lb l rds wrs m rs fn ib m' rs'
      fn' ib' →
    mstepOk (candLastSt c) x lb →
    srvwmoConsistent (candSnoc c ⟨x, lb⟩) ∧
    execProgOk' (pstepPin c.cdImg pstepEv) pclsEv (pstSnoc c pst x (.PHart cpu m' rs' fn' ib'))
      (dvSnoc c dv d0) (candExec (candSnoc c ⟨x, lb⟩)) := by
  intro hc hpo hp hdv hblk hok
  refine ⟨snocConsistent c ⟨x, lb⟩ hc hok, ?_⟩
  obtain ⟨ls, pa, da, har, hpin, hre, hst⟩ :=
    WeakRvwmoCert2.cblkElimPin c.cdImg cpu d0 _ lb l rds wrs m rs fn ib m' rs' fn' ib' hblk
  exact execProgOk'Snoc c x _ pa da ls l lb _ d0 pst dv hpo hp (by rw [hdv]; exact har) hpin hre
    hst

/-! ## 4.5 The three admissibility routes, as `mstepOk` providers -/

def srcInLog (c : Cand) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) : Prop :=
  vs.length = ts.length ∧
  ∀ (j : Nat) (t : Nat) (v : BitVec 8), ts[j]? = some t → vs[j]? = some v →
    logByte c.cdImg (cdLogEnd c) t (accAddr base j) = some v

def floorOk (c : Cand) (x : Nat) (aq : Bool) (base : Int) (ts : List Nat) : Prop :=
  ∀ (j : Nat) (t : Nat), ts[j]? = some t →
    ¬ writesIn (cdLogEnd c) (accAddr base j) t (cdFloor c x aq (accAddr base j))

theorem snocRdAdmOf (c : Cand) (x : Nat) (aq : Bool) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) :
    srcInLog c base ts vs → floorOk c x aq base ts → snocRdAdm c x aq base ts vs :=
  fun ⟨hlen, hval⟩ hfl => ⟨hlen, hval, hfl⟩

/-- (a) THE IN-LOG READ. -/
theorem certReadInLog (c : Cand) (x : Nat) (aq : Bool) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) :
    srcInLog c base ts vs → floorOk c x aq base ts →
    mstepOk (candLastSt c) x (.LLoad aq base ts vs) :=
  fun h1 h2 => snocRdOk c x aq base ts vs (snocRdAdmOf c x aq base ts vs h1 h2)

/-- (b) THE WITNESS READ: the latest message of every byte. -/
def witTvs (c : Cand) (base : Int) (n : Nat) : List (Nat × BitVec 8) :=
  List.zip (lrdTs c base n) (lrdVs c base n)

theorem witTvsFst (c : Cand) (base : Int) (n : Nat) :
    (witTvs c base n).map Prod.fst = lrdTs c base n := by
  unfold witTvs
  exact List.map_fst_zip (Nat.le_of_eq (lrdLength c base n).symm)

theorem witTvsSnd (c : Cand) (base : Int) (n : Nat) :
    (witTvs c base n).map Prod.snd = lrdVs c base n := by
  unfold witTvs
  exact List.map_snd_zip (Nat.le_of_eq (lrdLength c base n))

theorem witTvsLbl (c : Cand) (aq : Bool) (base : Int) (n : Nat) :
    Lbl.LLoad aq base ((witTvs c base n).map Prod.fst) ((witTvs c base n).map Prod.snd)
      = latestReadLbl c aq base n := by
  rw [witTvsFst, witTvsSnd]
  rfl

theorem witTvsLength (c : Cand) (base : Int) (n : Nat) : (witTvs c base n).length = n := by
  simp [witTvs, lrdTs, lrdVs]

theorem certReadWitness (c : Cand) (x : Nat) (aq : Bool) (base : Int) (n : Nat) :
    srvwmoConsistent c → latestBytesOk c base n →
    mstepOk (candLastSt c) x (latestReadLbl c aq base n) :=
  fun hc hb => snocRdOk c x aq base _ _ (latestSnocRdAdm c x aq base n hc hb)

/-- (c) THE WRITE and the FENCE. -/
theorem certWriteOk (c : Cand) (x : Nat) (rl : Bool) (base : Int) (vs : List (BitVec 8))
    (kc : WmClass) :
    vs ≠ [] → mstepOk (candLastSt c) x (.LStore rl base vs kc) :=
  fun h => h

theorem certFenceOk (c : Cand) (x : Nat) (pr pw sr sw : Bool) :
    mstepOk (candLastSt c) x (.LFence pr pw sr sw) :=
  trivial

/-- … and the RMW, whose atomicity forces the LATEST anyway. -/
theorem certRmwLatestOk (c : Cand) (x : Nat) (aq rl : Bool) (base : Int) (n : Nat)
    (wvs : List (BitVec 8)) (kc : WmClass) :
    srvwmoConsistent c → latestBytesOk c base n →
    wvs ≠ [] → wvs.length = n →
    mstepOk (candLastSt c) x (.LRmw aq rl base (lrdTs c base n) (lrdVs c base n) wvs kc) := by
  intro hc hb hne hlen
  refine ⟨hne, by simp [lrdTs, hlen], snocRdOk c x aq base _ _ (latestSnocRdAdm c x aq base n hc hb),
    ?_⟩
  show rmwLatest (candLastSt c).msImg (candLastSt c).msLog base (lrdTs c base n)
  rw [candLastImg, candLastLog]
  intro j t hj
  obtain ⟨hjn, rfl⟩ := lrdTsLookup c base n j t hj
  exact latestTsLatest _ _ _ (hb j hjn)

/-! # 5. Deliverable (3): `certSegment` -/

def lbRmwfree (lb : Lbl) : Prop :=
  match lb with
  | .LRmw .. => False
  | _ => True

/-- The candidate's per-agent release-pending bit, one snoc on. -/
theorem candSnocRelp (c : Cand) (i : Nat) (lb : Lbl) :
    ((candLastSt (candSnoc c ⟨i, lb⟩)).msWs i).wRelp
      = lpostRelp ((candLastSt c).msWs i).wRelp lb := by
  have h1 : candLastSt (candSnoc c ⟨i, lb⟩) = stt (candExec (candSnoc c ⟨i, lb⟩)) (cdEnd c + 1) := by
    unfold candLastSt
    rw [cdEndSnoc]
  rw [h1, candNext _ (cdEnd c) ⟨i, lb⟩ (candSnocTrEnd c _), candSnocLastSt c ⟨i, lb⟩]
  exact mnextWsRelp _ _ _

/-- THE "OTHER AGENT" TWIN. -/
theorem candSnocRelpNe (c : Cand) (i j : Nat) (lb : Lbl) :
    j ≠ i →
    ((candLastSt (candSnoc c ⟨i, lb⟩)).msWs j).wRelp = ((candLastSt c).msWs j).wRelp := by
  intro hne
  have h1 : candLastSt (candSnoc c ⟨i, lb⟩) = stt (candExec (candSnoc c ⟨i, lb⟩)) (cdEnd c + 1) := by
    unfold candLastSt
    rw [cdEndSnoc]
  rw [h1, candNext _ (cdEnd c) ⟨i, lb⟩ (candSnocTrEnd c _), candSnocLastSt c ⟨i, lb⟩]
  rw [mnextWsNe _ _ _ _ hne]

/-- THE ITERATION.  Rocq's `Section segment` context is the leading parameters (deviation 6);
deviation 4: the pinned LTS, the emission's pin `esPin c.cdImg es`, and `Hpol` on pinned
blocks. -/
theorem certSegment (x : Nat) (cpu : CPU) (d0 : Efab) (T : List Nat) (Q : Lbl → Prop)
    (_HQrmw : ∀ lb, Q lb → lbRmwfree lb)
    (Hpol : ∀ (c0 : Cand) (ws : Wstate) (lb : Lbl) (l : Wlabel) (rds : List Nat)
      (wrs : List Register) (m : SailM Unit) (rs1 rs2 : RegFile) (fn : Ofence) (ib : Ibch)
      (m' : SailM Unit) (rs1' : RegFile) (fn' : Ofence) (ib' : Ibch),
      srvwmoConsistent c0 →
      Q lb →
      ((candLastSt c0).msWs x).wRelp = ws.wRelp →
      dregAgree (fun n => n ∉ T) rs1 rs2 →
      WeakRvwmoCert2.cblkPin c0.cdImg cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
      ∃ lb' l' rds' wrs' rs2',
        WeakRvwmoCert2.cblkPin c0.cdImg cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m' rs2' fn' ib' ∧
        mstepOk (candLastSt c0) x lb' ∧
        lblReidx lb lb' ∧
        dregAgree (fun n => n ∉ T) rs1' rs2')
    (k0 : Nat) (ws0 : Wstate) (rowseg : List Lbl) (p : Pexv6) (es : List Eitem)
    (pfin : Pexv6) :
    hemit (fun _ => d0) k0 ws0 rowseg p es pfin →
    (∀ lb ∈ rowseg, Q lb) →
    ∀ m0 rs10 fn0 ib0, p = .PHart cpu m0 rs10 fn0 ib0 →
    ∀ (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab) (rs20 : RegFile),
      srvwmoConsistent c →
      WeakRvwmoCert2.esPin c.cdImg es →
      execProgOk' (pstepPin c.cdImg pstepEv) pclsEv pst dv (candExec c) →
      (pst (cdEnd c))[x]? = some (.PHart cpu m0 rs20 fn0 ib0) →
      dv (cdEnd c) = d0 →
      dregAgree (fun n => n ∉ T) rs10 rs20 →
      ((candLastSt c).msWs x).wRelp = ws0.wRelp →
      ∃ (c' : Cand) (pst' : Nat → List Pexv6) (dv' : Nat → Efab) (tradd : List Estep)
        (m1 : SailM Unit) (rs11 rs21 : RegFile) (fn1 : Ofence) (ib1 : Ibch),
        c'.cdTr = c.cdTr ++ tradd ∧
        (∀ s, s ∈ tradd → s.esAg = x) ∧
        List.Forall₂ lblReidxW rowseg (tradd.map (fun s => s.esLb)) ∧
        srvwmoConsistent c' ∧
        execProgOk' (pstepPin c.cdImg pstepEv) pclsEv pst' dv' (candExec c') ∧
        (pst' (cdEnd c'))[x]? = some (.PHart cpu m1 rs21 fn1 ib1) ∧
        dv' (cdEnd c') = d0 ∧
        pfin = .PHart cpu m1 rs11 fn1 ib1 ∧
        dregAgree (fun n => n ∉ T) rs11 rs21 ∧
        ((candLastSt c').msWs x).wRelp = (rowWsAux k0 ws0 rowseg).wRelp := by
  intro hem
  induction hem with
  | HEnil k ws p =>
    intro _ m0 rs10 fn0 ib0 hp0 c pst dv rs20 hc _ hpo hp hdv hag hrelp
    exact ⟨c, pst, dv, [], m0, rs10, rs20, fn0, ib0, by simp, fun s hs => absurd hs List.not_mem_nil,
      .nil, hc, hpo, hp, hdv, hp0, hag, hrelp⟩
  | HEone k ws lb row p ls pa da l p' es pfin har hre hst _ ih =>
    intro hrf m0 rs10 fn0 ib0 hp0 c pst dv rs20 hc hes hpo hp hdv hag hrelp
    subst hp0
    obtain ⟨hpin, hes'⟩ := WeakRvwmoCert2.esPinBlock c.cdImg ls l k es hes
    have hlb : Q lb := hrf lb List.mem_cons_self
    have hrf' : ∀ lb ∈ row, Q lb := fun lb0 h => hrf lb0 (List.mem_cons_of_mem _ h)
    obtain ⟨ma, rsa, fna, iba, rfl⟩ := admRunPhart true _ _ d0 ls da har cpu m0 rs10 fn0 ib0 rfl
    obtain ⟨m1, rs11, fn1, ib1, rfl⟩ := pstepEvPhart cpu ma rsa fna iba da l p' d0 hst
    obtain ⟨rds, wrs, hblk⟩ := WeakRvwmoCert2.cblkIntroPin c.cdImg cpu d0 ws lb l ls
      (.PHart cpu ma rsa fna iba) da m0 rs10 fn0 ib0 m1 rs11 fn1 ib1 har hpin hre hst
    obtain ⟨lb', l', rds', wrs', rs21, hblk2, hok, hri, hag2⟩ :=
      Hpol c ws lb l rds wrs m0 rs10 rs20 fn0 ib0 m1 rs11 fn1 ib1 hc hlb hrelp hag hblk
    obtain ⟨hc2, hpo2⟩ := certBlockSnoc c x pst dv cpu d0 lb' l' rds' wrs' m0 rs20 fn0 ib0 m1 rs21
      fn1 ib1 hc hpo hp hdv
      (WeakRvwmoCert2.cblkRelpG _ cpu d0 ws ((candLastSt c).msWs x) lb' l' rds' wrs' m0 rs20 fn0
        ib0 m1 rs21 fn1 ib1 hrelp hblk2) hok
    have hend : cdEnd (candSnoc c ⟨x, lb'⟩) = cdEnd c + 1 := cdEndSnoc c _
    have hp2 : (pstSnoc c pst x (.PHart cpu m1 rs21 fn1 ib1) (cdEnd (candSnoc c ⟨x, lb'⟩)))[x]?
        = some (.PHart cpu m1 rs21 fn1 ib1) := by
      rw [hend, pstSnocGt c pst x _ (cdEnd c + 1) (by omega)]
      exact List.getElem?_set_self (lookup_lt_Some hp)
    have hdv2 : dvSnoc c dv d0 (cdEnd (candSnoc c ⟨x, lb'⟩)) = d0 := by
      rw [hend, dvSnocGt c dv d0 (cdEnd c + 1) (by omega)]
    have hrelp2 : ((candLastSt (candSnoc c ⟨x, lb'⟩)).msWs x).wRelp = (lblPost k ws lb).wRelp := by
      rw [candSnocRelp, hrelp, lblReidxWRelp _ lb lb' (lblReidxWOf _ _ hri), lblPostRelp]
    obtain ⟨c', pst', dv', tradd, m2, rs12, rs22, fn2, ib2, htr, hag', hf2, hc', hpo', hp'',
      hdv', hfin, hagf, hrelpf⟩ :=
      ih hrf' m1 rs11 fn1 ib1 rfl (candSnoc c ⟨x, lb'⟩) (pstSnoc c pst x (.PHart cpu m1 rs21 fn1 ib1))
        (dvSnoc c dv d0) rs21 hc2 hes' hpo2 hp2 hdv2 hag2 hrelp2
    refine ⟨c', pst', dv', ⟨x, lb'⟩ :: tradd, m2, rs12, rs22, fn2, ib2, ?_, ?_,
      .cons (Or.inl hri) hf2, hc', hpo', hp'', hdv', hfin, hagf, hrelpf⟩
    · rw [htr, candSnocTr, List.append_assoc]
      rfl
    · intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · rfl
      · exact hag' s hs
  | HEpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin _ hre _ _ _ _ _ =>
    intro hrf
    exfalso
    have hlb := _HQrmw lb (hrf lb List.mem_cons_self)
    obtain ⟨aq, rl, base, tvs, data, asrc1, asrc2, vsrc2, -, -, -, -, rfl⟩ := hre
    exact hlb

/-! ## 5.1 The exit write, verbatim -/

theorem segExitWrite (x : Nat) (rowseg : List Lbl) (tradd : List Estep) (j : Nat) (rl : Bool)
    (base : Int) (vs : List (BitVec 8)) (kc : WmClass) :
    List.Forall₂ lblReidxW rowseg (tradd.map (fun s => s.esLb)) →
    (∀ s, s ∈ tradd → s.esAg = x) →
    rowseg[j]? = some (.LStore rl base vs kc) →
    tradd[j]? = some ⟨x, .LStore rl base vs kc⟩ := by
  intro hf2 hag hj
  obtain ⟨y, hy, hri⟩ := Forall2_lookup_l hf2 hj
  rw [List.getElem?_map] at hy
  cases hs : tradd[j]? with
  | none => rw [hs] at hy; cases hy
  | some s =>
    rw [hs] at hy
    simp only [Option.map_some, Option.some.injEq] at hy
    subst hy
    have hlb := lblReidxWStore rl base vs kc _ hri
    have hx : s.esAg = x := hag s (List.mem_of_getElem? hs)
    cases s with
    | mk a b =>
      simp only at hlb hx
      rw [hlb, hx]

/-! # 6. Non-vacuity -/

/-- The label class of the witness segment: a plain store with data. -/
def lbStoreNe (lb : Lbl) : Prop :=
  match lb with
  | .LStore _ _ vs _ => vs ≠ []
  | _ => False

theorem lbStoreNeRmwfree (lb : Lbl) : lbStoreNe lb → lbRmwfree lb := by
  cases lb <;> simp [lbStoreNe, lbRmwfree]

theorem lbStoreNeOk (c : Cand) (x : Nat) (lb : Lbl) :
    lbStoreNe lb → mstepOk (candLastSt c) x lb := by
  cases lb with
  | LStore rl base vs kc => exact fun h => h
  | _ => exact fun h => h.elim

/-- THE POLICY, discharged: at an empty taint set every block mirrors (deviation 4: on pinned
blocks; the mirror keeps the admin labels, hence their pins). -/
theorem polStore (x : Nat) (cpu : CPU) (d0 : Efab) :
    ∀ (c0 : Cand) (ws : Wstate) (lb : Lbl) (l : Wlabel) (rds : List Nat)
      (wrs : List Register) (m : SailM Unit) (rs1 rs2 : RegFile) (fn : Ofence) (ib : Ibch)
      (m' : SailM Unit) (rs1' : RegFile) (fn' : Ofence) (ib' : Ibch),
      srvwmoConsistent c0 →
      lbStoreNe lb →
      ((candLastSt c0).msWs x).wRelp = ws.wRelp →
      dregAgree (fun n => n ∉ ([] : List Nat)) rs1 rs2 →
      WeakRvwmoCert2.cblkPin c0.cdImg cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
      ∃ lb' l' rds' wrs' rs2',
        WeakRvwmoCert2.cblkPin c0.cdImg cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m' rs2' fn' ib' ∧
        mstepOk (candLastSt c0) x lb' ∧
        lblReidx lb lb' ∧
        dregAgree (fun n => n ∉ ([] : List Nat)) rs1' rs2' := by
  intro c0 ws lb l rds wrs m rs1 rs2 fn ib m' rs1' fn' ib' _ hlb _ hag hblk
  obtain ⟨rs2', hblk2, hag2⟩ := WeakRvwmoCert2.certBlockMirrorG _ (fun n => n ∉ ([] : List Nat))
    cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' rs2 hblk (fun n _ => List.not_mem_nil) hag
  exact ⟨lb, l, rds, wrs, rs2', hblk2, lbStoreNeOk c0 x lb hlb, lblReidxRefl lb, hag2⟩

theorem nvHemit (cpu : CPU) (rs : RegFile) (ib : Ibch) (d0 : Efab) :
    hemit (fun _ => d0) 0 wsInit evRow (evP0 cpu rs ib) (evEm cpu rs ib).emItems
      (evEm cpu rs ib).emFin :=
  evHartConf 0 cpu rs ib d0

/-- (Lean-only, deviation 4) The real block's emission is pinned at any image (its one label is a
store). -/
theorem WeakRvwmoCert2.nvPin (cpu : CPU) (rs : RegFile) (ib : Ibch) (im : Image) :
    WeakRvwmoCert2.esPin im (evEm cpu rs ib).emItems := by
  intro l0 hl0
  simp only [evEm, List.map_cons, List.map_nil, List.mem_singleton] at hl0
  subst hl0
  trivial

theorem nvRowClass : ∀ lb ∈ evRow, lbStoreNe lb := by
  intro lb hlb
  simp only [evRow, List.mem_singleton] at hlb
  subst hlb
  exact smBytes

/-- THE INSTANTIATION (Rocq `Section nonvacuity`'s context `cpu rs ib d0`, deviation 6). -/
theorem certSegmentWitness (cpu : CPU) (rs : RegFile) (ib : Ibch) (d0 : Efab) :
    ∃ (c' : Cand) (pst' : Nat → List Pexv6) (dv' : Nat → Efab) (tradd : List Estep),
      c'.cdTr = tradd ∧
      (∀ s, s ∈ tradd → s.esAg = 0) ∧
      List.Forall₂ lblReidxW evRow (tradd.map (fun s => s.esLb)) ∧
      srvwmoConsistent c' ∧
      execProgOk' (pstepPin (fun _ => none) pstepEv) pclsEv pst' dv' (candExec c') ∧
      tradd[0]? = some ⟨0, .LStore false (paZ evFlag) (WeakInterpProj.wbytes 4 lockOne)
        .WCplain⟩ := by
  obtain ⟨c', pst', dv', tradd, _, _, _, _, _, htr, hag, hf2, hc', hpo', -⟩ :=
    certSegment 0 cpu d0 [] lbStoreNe lbStoreNeRmwfree (polStore 0 cpu d0) 0 wsInit evRow
      (evP0 cpu rs ib) _ _ (nvHemit cpu rs ib d0) nvRowClass evX2.2 rs none ib rfl
      (smC (fun _ => none)) (smPst cpu rs ib) (smDv d0) rs (smConsistent _)
      (WeakRvwmoCert2.nvPin cpu rs ib _) (smProg0 _ cpu rs ib d0) rfl rfl (dregAgreeRefl _ _)
      (by rw [smWs])
  refine ⟨c', pst', dv', tradd, by rw [htr]; rfl, hag, hf2, hc', hpo', ?_⟩
  exact segExitWrite 0 evRow tradd 0 _ _ _ _ hf2 hag rfl

/-- THE POINT, with the objects hidden. -/
theorem certSegmentNonvacuous :
    ∃ (c' : Cand) (pst' : Nat → List Pexv6) (dv' : Nat → Efab) (tradd : List Estep),
      tradd ≠ [] ∧ c'.cdTr = tradd ∧
      (∀ s, s ∈ tradd → s.esAg = 0) ∧
      srvwmoConsistent c' ∧
      execProgOk' (pstepPin (fun _ => none) pstepEv) pclsEv pst' dv' (candExec c') ∧
      tradd[0]? = some ⟨0, .LStore false (paZ evFlag) (WeakInterpProj.wbytes 4 lockOne)
        .WCplain⟩ := by
  obtain ⟨c', pst', dv', tradd, htr, hag, -, hc', hpo', hlk⟩ :=
    certSegmentWitness ⟨0, by decide⟩ evRs0 ibNone (efInit ⟨fun _ => default⟩)
  refine ⟨c', pst', dv', tradd, ?_, htr, hag, hc', hpo', hlk⟩
  rintro rfl
  simp at hlk

end Weak
