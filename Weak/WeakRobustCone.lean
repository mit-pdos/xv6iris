/-
Weak: **THE BLOCK-CONTIGUOUS CONE REPLAY** (lift stage B3).

Rocq: `iris/WeakRobustCone.v` @ xxvzwolszwmp.

The Rocq header, in substance.  `WeakRobustMain.badEdgeViolates` builds a violating
promise-free configuration by replaying the minimal bad edge's ancestor cone in an
ARBITRARY topological order.  Here the same exhibit is re-derived over a
BLOCK-CONTIGUOUS order, and the run's segment structure is exported, so that a later
stage can regroup the run into whole-instruction steps.  A block is a maximal stretch
of an agent's trace between two BOUNDARY states (`bnd`); the one structural premise
(`hcsl`, the design's (P1')/(P2)) says that AFTER a cross-edge source, and until the
next boundary state, the agent's events are non-memory.  With "cross-edge TARGETS are
memory events" (`crossTgtMem`) this gives at most ONE cross source per block
(`xsrcUnique`) and every cross target of a block program-order at-or-before it
(`xtgtLeXsrc`), which makes the BLOCK-CONTRACTED graph acyclic (`RblkAcyc`: a
contracted cycle composes into a `gdep2` cycle, and `Idx` strictly increases along
`tc gdep2` on the cone).  `topoSort` is run over the cone's block identifiers
(`Rblk'`, which also forces the reader's block last), the block order becomes a
LEXICOGRAPHIC key (`klt`), and `topoSort` is run again at the event level (`Rev`);
the second order exports the `qorder` predecessor property, block contiguity,
in-block trace order and reader-block-last (§5.2).  `QcfgStep` is `QinvStep`'s
step-exporting twin, and `pfChainBuild` the per-event configuration chain (one
`WeakRobustBlocks.cstep` of the processed event's agent per element of the order);
`blocksViolates` / `badEdgeViolatesBlocks` re-derive the violation at that order.
DEPENDENCY-FREE: no Iris, no Sail.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1 (capitalised Rocq names
   keep their capital: `Qcfg_step` ↦ `QcfgStep`, `Idx_mono` ↦ `IdxMono`, ...).
   File-qualified (in `notes/weak-port-dupnames.json`): `is_mem` ↦
   `WeakRobustCone.isMem`, `bpos` ↦ `WeakRobustCone.bpos`.  `cstep_of_step` is
   `WeakRobustCone.cstepOfStep` because `WeakRobustBlocks` already has a Lean-only
   `cstepOfStep` (same statement; the Lean twin is proved by it).  The binder `done`
   is `dn`; `done_b` is `doneB`.
2. VOCABULARY: as `Weak/WeakRobustSim.lean` deviation 2 (`l !! i` ↦ `l[i]?`, `S n` ↦
   `n + 1`, `NoDup` ↦ `List.Nodup`, `PDevs d []` ↦ `⟨d, []⟩`, `remove_dups` ↦
   `removeDups`, `list_find` ↦ `listFind` with a `decide` predicate, `Forall P l` ↦
   `∀ x ∈ l, P x`); `Decision`/`RelDecision` instances ↦ `Decidable`/`DecidableRel`
   instances (`xsrcDec`, `RblkDec`, `okeDec`, `Rblk'Dec`, `kltDec`, `RevDec`), the
   `Decision (bnd p)` context ↦ `[DecidablePred bnd]`.
3. SECTION VARIABLES: the `coneblocks` section's data (`pstep pcls TS img d0 ps bnd
   b2 ord0 bord doneB`) are IMPLICIT `variable`s (explicit, via `variable (…) in`,
   on the definitions `bno bid isMem xsrc cl Idx Rblk oke Rblk' bids bpos klt Rev
   doneFull`, matching Rocq's call sites in §8); the section HYPOTHESES are explicit
   arguments of exactly the declarations whose LEAN proof uses them (`include … in`),
   in declaration order.  Consequences: `pdev` is a parameter nowhere (Rocq threads
   it only into `Qinv_step`, whose Lean twin takes none: `WeakRobustSim` deviation
   3); the unused section hypotheses `Hbnd0` and `Hbordnd` are parameters nowhere
   (no Rocq proof uses them either; `badEdgeViolatesBlocks` does not take `Hbnd0`,
   as in Rocq after `End main`); `Hqcl`, `clNodup`, `IdxMono`, `coneAcyc` take only
   `hb2wf hrr hq0 hmem0` (`Hqcl` is proved by `qorderStep` directly instead of
   through `HQcl`'s replay; `HQcl` itself is ported with its full premises);
   `clB2Lt`/`kltB2` take `hb2wf` explicitly (Rocq: section context).  `hnag` is
   kept (unused, `_hnag`) on `qcfgStepEx`, and passed through `QcfgStep`,
   `pfChainBuild`, `blocksViolates`, `badEdgeViolatesBlocks` (Rocq consumes it
   there; the Lean twins of `nproc_cur`/`qorder_step`/`Qinv_nil` take none).
4. O2 / owner decision D4: THE FETCH-SOURCE PREMISE.  The Lean replay
   (`WeakRobustSim.QinvStep`) carries the Lean-only premise `fetchSrcOk TS`
   (`WeakRobustSim` deviation 4), so every declaration here that replays an event
   GAINED it as a premise (`hfetch`): `QcfgStep` (after `hdf`), `HQcl`,
   `QinvPrefix`, `qorderPrefix`, `qorderDoneFull`, `qorderDoneB`, `pfChainBuild`,
   `blocksViolates`, and `badEdgeViolatesBlocks` (as its LAST hypothesis before
   `b1 b2`, the place `WeakRobustMain.badEdgeViolates` has it, after `hcsl`).
   `QcfgStep` gains the `LIFetch` arm of `QinvStep` (transcribed verbatim, as the
   other eleven arms).  `lbWrites`/`lbLoads` of `LIFetch` are `false`
   (`WeakRobustBlocks` deviation 4), so `hcsl` and `isMem` are unchanged in shape.
   A fetch-free program discharges `hfetch` by `WeakRobustMain.fetchSrcOkOfNoFetch`
   (no separate NoFetch variant is stated here).
5. PROOFS: `tc` is core `Relation.TransGen` (built from the LAST step): `tcFirst`,
   `chain2`, `tcRblk'Rblk`, `tcRevKlt` go by tail induction (Rocq: head).
   `qorderPrefix`/`qorderDoneFull`/`qorderDoneB` additionally `include d0` (it
   occurs only in their proofs, via `QinvPrefix`), so callers pass `(d0 := d0)`.
   Statements otherwise unchanged.
6. Lean-only helpers (no Rocq twin): `blkNoSucc` (the `blk_no` unfolding),
   `bidEqFst`, `bidEqSnd` (the two halves of a `bid` equation; Rocq: `[= ? ?]`).

**Rocq → Lean name map.**  `lidx`; `lidx_lookup` ↦ `lidxLookup`; `lidx_inj` ↦ `lidxInj`;
`lidx_lt` ↦ `lidxLt`; `lidx_eq_elem` ↦ `lidxEqElem`; `tc_first` ↦ `tcFirst`; `not_impl2`
↦ `notImpl2`; `bnd_at` ↦ `bndAt`; `blk_no` ↦ `blkNo`; `blk_no_mono` ↦ `blkNoMono`;
`blk_no_lt_index` ↦ `blkNoLtIndex`; `blk_no_gap` ↦ `blkNoGap`; `bnd_at_false` ↦
`bndAtFalse`; `blk_no_bnd_lt` ↦ `blkNoBndLt`; `qcfg_step_ex` ↦ `qcfgStepEx`; `Qcfg_step`
↦ `QcfgStep`; `bno`; `bid`; `bid_agent` ↦ `bidAgent`; `bid_same_gap` ↦ `bidSameGap`;
`bno_lt_index` ↦ `bnoLtIndex`; `bno_le_of_index` ↦ `bnoLeOfIndex`; `is_mem` ↦
`WeakRobustCone.isMem`; `ts_writes` ↦ `tsWrites`; `ts_mem` ↦ `tsMem`; `reads_loads` ↦
`readsLoads`; `reads_mem` ↦ `readsMem`; `xsrc`; `xsrc_mem` ↦ `xsrcMem`; `cross_tgt_mem`
↦ `crossTgtMem`; `cross_src_last` ↦ `crossSrcLast`; `xsrc_unique` ↦ `xsrcUnique`;
`xtgt_le_xsrc` ↦ `xtgtLeXsrc`; `gdep2_sa_lt` ↦ `gdep2SaLt`; `gdep2_sa_ne` ↦ `gdep2SaNe`;
`xsrc_dec` ↦ `xsrcDec`; `cl`; `ord0_wf` ↦ `ord0Wf`; `ord0_tc` ↦ `ord0Tc`; `b2_nin` ↦
`b2Nin`; `b2_pre` ↦ `b2Pre`; `ord0_dc` ↦ `ord0Dc`; `elem_of_cl` ↦ `elemOfCl`; `ord0_cl`
↦ `ord0Cl`; `b2_cl` ↦ `b2Cl`; `cl_wf` ↦ `clWf`; `cl_dc` ↦ `clDc`; `cl_dc'` ↦ `clDc'`;
`HQcl`; `Hqcl`; `ord0_nodup` ↦ `ord0Nodup`; `cl_nodup` ↦ `clNodup`; `Idx`; `Idx_lookup`
↦ `IdxLookup`; `Idx_lt` ↦ `IdxLt`; `Idx_mono` ↦ `IdxMono`; `cone_acyc` ↦ `coneAcyc`;
`Rblk`; `oke`; `oke_dec` ↦ `okeDec`; `oke_use` ↦ `okeUse`; `not_oke` ↦ `notOke`;
`xsrc_oke` ↦ `xsrcOke`; `oneedge`; `chain2`; `Rblk_acyc` ↦ `RblkAcyc`; `b2blk_no_out` ↦
`b2blkNoOut`; `Rblk'`; `tc_Rblk_from_b2` ↦ `tcRblkFromB2`; `tc_Rblk'_Rblk` ↦
`tcRblk'Rblk`; `Rblk'_acyc` ↦ `Rblk'Acyc`; `bids`; `elem_of_bids` ↦ `elemOfBids`;
`bids_nodup` ↦ `bidsNodup`; `bpos` ↦ `WeakRobustCone.bpos`; `bid_in_bord` ↦ `bidInBord`;
`bpos_lookup` ↦ `bposLookup`; `bpos_inj` ↦ `bposInj`; `klt`; `klt_dec` ↦ `kltDec`;
`klt_trans` ↦ `kltTrans`; `klt_irrefl` ↦ `kltIrrefl`; `klt_total` ↦ `kltTotal`;
`gdep2_klt` ↦ `gdep2Klt`; `bpos_b2_max` ↦ `bposB2Max`; `cl_b2_lt` ↦ `clB2Lt`; `klt_b2` ↦
`kltB2`; `Rev`; `tc_Rev_klt` ↦ `tcRevKlt`; `Rev_acyc` ↦ `RevAcyc`; `done_full` ↦
`doneFull`; `done_b_ord0` ↦ `doneBOrd0`; `done_b_cl` ↦ `doneBCl`; `done_full_len` ↦
`doneFullLen`; `done_full_last` ↦ `doneFullLast`; `done_full_lookup` ↦ `doneFullLookup`;
`done_full_mem` ↦ `doneFullMem`; `done_full_cl` ↦ `doneFullCl`; `done_full_nodup` ↦
`doneFullNodup`; `done_full_klt` ↦ `doneFullKlt`; `done_full_nklt` ↦ `doneFullNklt`;
`done_full_pred` ↦ `doneFullPred`; `done_full_contig` ↦ `doneFullContig`;
`done_full_inblk` ↦ `doneFullInblk`; `done_full_reader_last` ↦ `doneFullReaderLast`;
`Qinv_prefix` ↦ `QinvPrefix`; `qorder_prefix` ↦ `qorderPrefix`; `qorder_done_full` ↦
`qorderDoneFull`; `qorder_done_b` ↦ `qorderDoneB`; `qcfg_nil` ↦ `qcfgNil`;
`cstep_of_step` ↦ `WeakRobustCone.cstepOfStep`; `pf_chain_build` ↦ `pfChainBuild`;
`blocks_violates` ↦ `blocksViolates`; `bad_edge_violates_blocks` ↦
`badEdgeViolatesBlocks`; `Rblk_dec` ↦ `RblkDec`; `Rblk'_dec` ↦ `Rblk'Dec`; `Rev_dec` ↦
`RevDec`.

**Not ported:** nothing (every Rocq definition and lemma has a Lean twin).
-/
import Weak.WeakRobustBlocks
import Weak.WeakRobustLin

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std Wlabel

/-! ## §0 TWO GENERIC LIST HELPERS -/

/-- The position of an element in a list, as a FUNCTION (`length` when absent). -/
def lidx (l : List (Nat × Nat)) (x : Nat × Nat) : Nat :=
  match listFind (fun y => decide (y = x)) l with
  | some (i, _) => i
  | none => l.length

theorem lidxLookup (l : List (Nat × Nat)) (x : Nat × Nat) :
    x ∈ l → l[lidx l x]? = some x := by
  intro hin
  unfold lidx
  rcases hf : listFind (fun y => decide (y = x)) l with _ | ⟨i, y⟩
  · have := list_find_None.1 hf x hin
    simp at this
  · obtain ⟨hl, hp, -⟩ := list_find_Some.1 hf
    have hyx : y = x := of_decide_eq_true hp
    subst hyx
    exact hl

theorem lidxInj (l : List (Nat × Nat)) (x : Nat × Nat) (i : Nat) :
    l.Nodup → l[i]? = some x → lidx l x = i := by
  intro hnd hi
  exact NoDup_lookup hnd (lidxLookup l x (elem_of_list_lookup_2 hi)) hi

theorem lidxLt (l : List (Nat × Nat)) (x : Nat × Nat) : x ∈ l → lidx l x < l.length :=
  fun hin => lookup_lt_Some (lidxLookup l x hin)

theorem lidxEqElem (l : List (Nat × Nat)) (x y : Nat × Nat) :
    x ∈ l → y ∈ l → lidx l x = lidx l y → x = y := by
  intro hx hy heq
  have h1 := lidxLookup l x hx
  have h2 := lidxLookup l y hy
  rw [heq, h2] at h1
  exact (Option.some.inj h1).symm

/-- The first edge of a `tc` chain. -/
theorem tcFirst {A : Type _} (R : A → A → Prop) (x z : A) : tc R x z → ∃ y, R x y := by
  intro h
  induction h with
  | single h => exact ⟨_, h⟩
  | tail _ _ ih => exact ih

/-- A decidable de Morgan step for a two-premise implication. -/
theorem notImpl2 (A B C : Prop) [Decidable A] [Decidable B] [Decidable C] :
    ¬ (A → B → C) → A ∧ B ∧ ¬ C := by
  intro hn
  by_cases hA : A
  · by_cases hB : B
    · by_cases hC : C
      · exact (hn (fun _ _ => hC)).elim
      · exact ⟨hA, hB, hC⟩
    · exact (hn (fun _ hB' => (hB hB').elim)).elim
  · exact (hn (fun hA' => (hA hA').elim)).elim

/-! ## §1 BLOCK VOCABULARY ON ONE TRACE -/

section blockvocab

variable {P D : Type}
variable (bnd : P → Prop) [DecidablePred bnd]

def bndAt (T : Atrace P D) (j : Nat) : Bool :=
  match T.atAgs[j]? with
  | some ag => decide (bnd ag.paSt)
  | none => false

def blkNo (T : Atrace P D) : Nat → Nat
  | 0 => 0
  | k + 1 => blkNo T k + if bndAt bnd T (k + 1) then 1 else 0

theorem blkNoSucc (T : Atrace P D) (k : Nat) :
    blkNo bnd T (k + 1) = blkNo bnd T k + if bndAt bnd T (k + 1) then 1 else 0 := rfl

theorem blkNoMono (T : Atrace P D) (k k' : Nat) : k ≤ k' → blkNo bnd T k ≤ blkNo bnd T k' := by
  induction k' with
  | zero =>
    intro h
    have hk : k = 0 := by omega
    subst hk
    exact Nat.le_refl _
  | succ k' ih =>
    intro h
    by_cases hk : k = k' + 1
    · subst hk; exact Nat.le_refl _
    · have := ih (by omega)
      rw [blkNoSucc]
      split <;> omega

/-- Blocks are intervals: a strictly larger block number forces a strictly larger
trace index. -/
theorem blkNoLtIndex (T : Atrace P D) (k k' : Nat) :
    blkNo bnd T k < blkNo bnd T k' → k < k' := by
  intro hlt
  rcases Nat.lt_or_ge k k' with h | h
  · exact h
  · have := blkNoMono bnd T k' k h
    omega

/-- SAME BLOCK ⟹ NO BOUNDARY STRICTLY BETWEEN. -/
theorem blkNoGap (T : Atrace P D) (k k' m : Nat) :
    blkNo bnd T k = blkNo bnd T k' → k ≤ m → m + 1 ≤ k' → bndAt bnd T (m + 1) = false := by
  intro heq h1 h2
  cases hb : bndAt bnd T (m + 1) with
  | false => rfl
  | true =>
    exfalso
    have ha := blkNoMono bnd T k m h1
    have hc := blkNoMono bnd T (m + 1) k' h2
    have hs : blkNo bnd T (m + 1) = blkNo bnd T m + 1 := by simp [blkNoSucc, hb]
    omega

theorem bndAtFalse (T : Atrace P D) (j : Nat) (ag : Wpagent P) :
    T.atAgs[j]? = some ag → bndAt bnd T j = false → ¬ bnd ag.paSt := by
  intro hj hb
  unfold bndAt at hb
  rw [hj] at hb
  exact of_decide_eq_false hb

/-- …and conversely a boundary state at `m + 1` separates the blocks. -/
theorem blkNoBndLt (T : Atrace P D) (m : Nat) :
    bndAt bnd T (m + 1) = true → blkNo bnd T m < blkNo bnd T (m + 1) := by
  intro hb
  simp [blkNoSucc, hb]

end blockvocab

/-! ## §2 THE STEP-EXPORTING TWIN OF `QinvStep` -/

section stepout

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)
variable (TS : Ptraces P D) (img : Image) (d0 : D) (ps : List P)

/-- `qcfgStep`, repackaged so that the arms below can be transcribed from
`QinvStep` verbatim. -/
theorem qcfgStepEx (hwf : ptracesWf pstep TS) (hwfl : writesFulfilled TS)
    (_hnag : TS.ptTrs.length = ps.length)
    (dn : List Gev) (e : Gev) (T : Atrace P D) (ev : Aev D) (ag' : Wpagent P) (cf : Wpcfg P D)
    (newws : Wstate) (lb' : Wlabel) (dv : D) :
    qorder TS dn →
    nproc dn e.1 = e.2 →
    TS.ptTrs[e.1]? = some T → T.atEvs[e.2]? = some ev →
    T.atAgs[e.2 + 1]? = some ag' →
    qcfg pstep pcls TS ⟨d0, []⟩ img d0 ps dn cf →
    newws = aevPost (pi TS (dn ++ [e])) ev (aevsPost (pi TS dn) (T.atEvs.take e.2) wsInit) →
    qfab TS ⟨d0, []⟩ (dn ++ [e]) dv →
    wpPfStep pstep pcls e.1 lb' cf
      ⟨cf.pcImg, WeakRobustSim.pfLog TS (dn ++ [e]), dv, cf.pcAgs.set e.1 ⟨ag'.paSt, newws, ∅⟩⟩ →
    ∃ lb cf', wpPfStep pstep pcls e.1 lb cf cf' ∧
      qcfg pstep pcls TS ⟨d0, []⟩ img d0 ps (dn ++ [e]) cf' :=
  fun hq hnp hT hev hag' hc hnew hdv hstep =>
    ⟨lb', _, hstep, qcfgStep pstep pcls TS ⟨d0, []⟩ img d0 ps hwf hwfl dn e T ev ag' cf newws lb'
      dv hq hnp hT hev hag' hc hnew hdv hstep⟩

/-- THE STEP, EXPORTED.  (O2: `hfetch`, deviation 4.) -/
theorem QcfgStep (hwf : ptracesWf pstep TS) (hwsi : ptracesWsInit TS) (hco : ∀ a, coTc TS a)
    (hwfl : writesFulfilled TS) (hlf : latFreeProg pstep) (hobl : tsOblivious pstep)
    (hcls : clsCanonical pcls TS) (hclsobl : pclsObl pcls) (himg : TS.ptImg = img)
    (hnag : TS.ptTrs.length = ps.length)
    (hdata : ∀ (p : Nat) (m : Wmsg), TS.ptLog[p]? = some m → m.wmData ≠ [])
    (hdf : ∀ (j : Nat) (T : Atrace P D) (k : Nat) (ev : Aev D), TS.ptTrs[j]? = some T →
      T.atEvs[k]? = some ev → ev.aeDev = none)
    (hfetch : fetchSrcOk TS) (dn : List Gev) (e : Gev) (cf : Wpcfg P D) :
    qorder TS dn → qcfg pstep pcls TS ⟨d0, []⟩ img d0 ps dn cf →
    gevWf TS e → e ∉ dn →
    (∀ e', gdep2 TS e' e → gevWf TS e' → e' ∈ dn) →
    ∃ lb cf', wpPfStep pstep pcls e.1 lb cf cf' ∧
      qcfg pstep pcls TS ⟨d0, []⟩ img d0 ps (dn ++ [e]) cf' := by
  intro hq hc hwfe hnin hpre
  have hwit := ptracesWitNil TS d0 hdf
  have hpre3 : ∀ e', gdep3 TS ⟨d0, []⟩ e' e → gevWf TS e' → e' ∈ dn :=
    fun e' hd hw => hpre e' (gdep3NilGdep2 TS d0 e' e hd) hw
  have hq' := qorderStep TS dn e hq hwfe hnin hpre
  have hnp := nprocCur TS dn e hq hwfe hnin hpre
  have hc0 := hc
  obtain ⟨_, hcimg, hclog, _, hcags, hfab⟩ := hc
  obtain ⟨T, hT, hklt⟩ := (gevWfBounds TS e).1 hwfe
  obtain ⟨ev, hev⟩ := Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 hklt)
  have hgev : gevEv TS e = some ev := by simp [gevEv, hT, hev]
  have hatr := hwf e.1 T hT
  obtain ⟨ag, ag2, st', f, hag, hag2, hps, hok, hagn⟩ :=
    astepsWfStep pstep TS.ptImg TS.ptLog e.1 T.atAgs T.atEvs e.2 ev hatr hev
  -- THE FABRIC ARM
  obtain ⟨dnew, hpure, hfab'⟩ :=
    qfabStep pstep TS ⟨d0, []⟩ hwit dn e T ev ag st' cf hnin hpre3 hT hev hps hfab
  obtain ⟨agn, hagn0, hcflk⟩ := hcags e.1 T hT
  rw [hnp, hag] at hagn0
  cases hagn0
  rw [hnp] at hcflk
  have hstpost : ag2.paSt = st' := by rw [hagn]
  -- π is stable on everything this event READS
  have hstab : ∀ a t, gevReads TS e a t → pi TS (dn ++ [e]) t = pi TS dn t := by
    intro a t hr
    apply piApp
    by_cases ht : t = 0
    · exact Or.inr ht
    · exact Or.inl (readTsInFl pstep TS hwf hwfl dn e a t hq hpre hr (by omega))
  have hmapOf : ∀ base tvs, lbReads ev.aeLb = tvsReads base tvs →
      (tvs.map Prod.fst).map (pi TS (dn ++ [e])) = (tvs.map Prod.fst).map (pi TS dn) := by
    intro base tvs hlr
    apply list_fmap_ext
    intro i t hi
    obtain ⟨a, ha⟩ := tvsFstReads base tvs i t hi
    exact hstab a t ⟨ev.aeLb, by simp [gevLb, hgev], by rw [hlr]; exact ha⟩
  have hkcOf : ∀ ts m, ev.aeTs = some ts → TS.ptLog[ts - 1]? = some m →
      m.wmAk = pcls ag.paSt ev.aeLb ag.paWs :=
    fun ts m h1 h2 => hcls e.1 T e.2 ev ag ts m hT hev hag h1 h2
  obtain ⟨W, hWdef⟩ : ∃ W, W = aevsPost (pi TS dn) (T.atEvs.take e.2) wsInit := ⟨_, rfl⟩
  rw [← hWdef] at hcflk
  have hrelp : ag.paWs.wRelp = W.wRelp := by
    rw [hWdef]; exact replayWsRelp pstep TS hwf hwsi e.1 e.2 T ag (pi TS dn) hT hag
  have hlogNone : gevTs TS e = none → WeakRobustSim.pfLog TS (dn ++ [e]) = cf.pcLog := by
    intro h
    rw [hclog]
    unfold WeakRobustSim.pfLog
    rw [flAppNone TS dn e h]
  have hlogSome : ∀ ts m, ev.aeTs = some ts → TS.ptLog[ts - 1]? = some m →
      WeakRobustSim.pfLog TS (dn ++ [e]) = cf.pcLog ++ [m] := by
    intro ts m h1 h2
    rw [hclog]
    unfold WeakRobustSim.pfLog
    rw [flAppSome TS dn e ts (by simp [gevTs, hgev, h1]), List.map_append, List.map_cons,
      List.map_nil, msgAtEq TS ts m h2]
  have hpitsOf : ∀ ts, ev.aeTs = some ts → pi TS (dn ++ [e]) ts = cf.pcLog.length + 1 := by
    intro ts h
    rw [hclog, flLen]
    apply piMem pstep TS hwf (dn ++ [e]) _ ts hq'
    rw [flAppSome TS dn e ts (by simp [gevTs, hgev, h]), lookup_app_r (Nat.le_refl _), Nat.sub_self]
    rfl
  have hokc := hok
  generalize hlbe : ev.aeLb = l at hok hpure
  cases l with
  | LSilent =>
    obtain ⟨_, hts0⟩ := hok
    have hgts : gevTs TS e = none := by simp [gevTs, hgev, hts0]
    refine qcfgStepEx pstep pcls TS img d0 ps hwf hwfl hnag dn e T ev ag2 cf W .LSilent dnew
      hq hnp hT hev hag2 hc0 ?_ hfab' ?_
    · rw [← hWdef]; simp only [aevPost, hlbe]
    · rw [hstpost, hlogNone hgts]
      exact .PFSilent cf _ st' dnew hcflk hpure
  | LLoad aq lat base tvs asrc =>
    have hlat : lat = false := by
      cases lat
      · rfl
      · exact absurd hpure (latFreeProgLat pstep _ _ _ _ _ _ _ _ hlf)
    subst hlat
    obtain ⟨hro, _, hts0⟩ := hok
    have hgts : gevTs TS e = none := by simp [gevTs, hgev, hts0]
    have hmap := hmapOf base tvs (by rw [hlbe]; rfl)
    refine qcfgStepEx pstep pcls TS img d0 ps hwf hwfl hnag dn e T ev ag2 cf
      (loadPostRunD W aq (srcsView W asrc) base ((tlabelTs (pi TS dn) tvs).map Prod.fst))
      (.LLoad aq false base (tlabelTs (pi TS dn) tvs) asrc) dnew
      hq hnp hT hev hag2 hc0 ?_ hfab' ?_
    · rw [← hWdef]; simp only [aevPost, hlbe]; rw [tlabelTsFst, hmap]
    · rw [hstpost, hlogNone hgts]
      refine .PFLoad cf ⟨ag.paSt, W, ∅⟩ aq false base _ asrc st' dnew hcflk
        (hobl.1 _ _ aq false base tvs _ asrc st' dnew (tlabelTsSnd _ _).symm hpure) ?_
      show readOkD cf.pcImg cf.pcLog W aq false base (tlabelTs (pi TS dn) tvs) (srcsView W asrc)
      rw [hcimg, hclog]
      exact readOkPf pstep TS img hwf hwsi hco hwfl himg dn e T ev ag
        (.LLoad aq false base tvs asrc) base tvs false W hq hpre hnp hT hev hag hlbe trivial rfl
        hro hWdef
  | LStore rl base data asrc vsrc =>
    obtain ⟨ts, kc, _, hlog, _, _, hts⟩ := hok
    have hpits := hpitsOf ts hts
    have hnedata : data ≠ [] := hdata (ts - 1) _ hlog
    have hkc : kc = pcls ag.paSt (.LStore rl base data asrc vsrc) ag.paWs := by
      have := hkcOf ts _ hts hlog; rw [hlbe] at this; exact this
    refine qcfgStepEx pstep pcls TS img d0 ps hwf hwfl hnag dn e T ev ag2 cf
      (storePostRunD W rl (srcsView W asrc) (srcsView W vsrc) base data.length
        (cf.pcLog.length + 1))
      (.LStore rl base data asrc vsrc) dnew hq hnp hT hev hag2 hc0 ?_ hfab' ?_
    · rw [← hWdef]; simp only [aevPost, hlbe, hts, hpits]
    · rw [hstpost, hlogSome ts _ hts hlog]
      -- THE PINNED CLASS (G6a)
      exact .PFStore cf ⟨ag.paSt, W, ∅⟩ rl base data asrc vsrc kc st' dnew hcflk hpure hnedata
        (by rw [hkc]; exact hclsobl.1 ag.paSt rl base data asrc vsrc ag.paWs W hrelp)
  | LRmw aq rl base tvs data asrc vsrc =>
    obtain ⟨ts, kc, hlen, _, hlog, hro, _, _, _, hts⟩ := hok
    have hpits := hpitsOf ts hts
    have hnedata : data ≠ [] := hdata (ts - 1) _ hlog
    have hmap := hmapOf base tvs (by rw [hlbe]; rfl)
    have hkc : kc = pcls ag.paSt (.LRmw aq rl base tvs data asrc vsrc) ag.paWs := by
      have := hkcOf ts _ hts hlog; rw [hlbe] at this; exact this
    refine qcfgStepEx pstep pcls TS img d0 ps hwf hwfl hnag dn e T ev ag2 cf
      (storePostRunD
        (loadPostRunD W aq (srcsView W asrc) base ((tlabelTs (pi TS dn) tvs).map Prod.fst))
        rl (srcsView W asrc) (srcsView W vsrc) base data.length (cf.pcLog.length + 1))
      (.LRmw aq rl base (tlabelTs (pi TS dn) tvs) data asrc vsrc) dnew
      hq hnp hT hev hag2 hc0 ?_ hfab' ?_
    · rw [← hWdef]; simp only [aevPost, hlbe, hts, hpits]; rw [tlabelTsFst, hmap]
    · rw [hstpost, hlogSome ts _ hts hlog]
      refine .PFRmw cf ⟨ag.paSt, W, ∅⟩ aq rl base _ data asrc vsrc kc st' dnew hcflk
        (hobl.2.1 _ _ aq rl base tvs _ data asrc vsrc st' dnew (tlabelTsSnd _ _).symm hpure)
        hnedata (by rw [tlabelTsLength]; exact hlen) ?_ ?_ ?_
      · show readOkD cf.pcImg cf.pcLog W aq false base (tlabelTs (pi TS dn) tvs) 0
        rw [hcimg, hclog]
        exact readOkPf pstep TS img hwf hwsi hco hwfl himg dn e T ev ag
          (.LRmw aq rl base tvs data asrc vsrc) base tvs false W hq hpre hnp hT hev hag hlbe
          trivial rfl hro hWdef
      · rw [hclog]
        exact exclOkPf pstep TS hwf hco hwfl dn e T ev ag f aq rl base tvs data asrc vsrc ts
          hq hnin hpre hT hev hlbe hts hokc
      · -- THE PINNED CLASS (G6a)
        rw [hkc]
        exact hclsobl.2.1 ag.paSt aq rl base tvs _ data asrc vsrc ag.paWs W
          (tlabelTsSnd _ _).symm hrelp
  | LFence pr pw sr sw =>
    obtain ⟨_, hts0⟩ := hok
    have hgts : gevTs TS e = none := by simp [gevTs, hgev, hts0]
    refine qcfgStepEx pstep pcls TS img d0 ps hwf hwfl hnag dn e T ev ag2 cf
      (fencePost W pr pw sr sw) (.LFence pr pw sr sw) dnew hq hnp hT hev hag2 hc0 ?_ hfab' ?_
    · rw [← hWdef]; simp only [aevPost, hlbe]
    · rw [hstpost, hlogNone hgts]
      exact .PFFence cf _ pr pw sr sw st' dnew hcflk hpure
  | LDev kd ba bs sa sv =>
    -- the `LSilent` case verbatim, at `PFDev`
    obtain ⟨_, hts0⟩ := hok
    have hgts : gevTs TS e = none := by simp [gevTs, hgev, hts0]
    refine qcfgStepEx pstep pcls TS img d0 ps hwf hwfl hnag dn e T ev ag2 cf W (.LDev kd ba bs sa sv) dnew
      hq hnp hT hev hag2 hc0 ?_ hfab' ?_
    · rw [← hWdef]; simp only [aevPost, hlbe]
    · rw [hstpost, hlogNone hgts]
      exact .PFDev cf _ st' dnew hcflk hpure
  | LRegW rdw wsrc =>
    obtain ⟨_, hts0⟩ := hok
    have hgts : gevTs TS e = none := by simp [gevTs, hgev, hts0]
    refine qcfgStepEx pstep pcls TS img d0 ps hwf hwfl hnag dn e T ev ag2 cf
      (regwPost W rdw (srcsView W wsrc)) (.LRegW rdw wsrc) dnew hq hnp hT hev hag2 hc0 ?_ hfab' ?_
    · rw [← hWdef]; simp only [aevPost, hlbe]
    · rw [hstpost, hlogNone hgts]
      exact .PFRegW cf _ rdw wsrc st' dnew hcflk hpure
  | LCtrl csrc =>
    obtain ⟨_, hts0⟩ := hok
    have hgts : gevTs TS e = none := by simp [gevTs, hgev, hts0]
    refine qcfgStepEx pstep pcls TS img d0 ps hwf hwfl hnag dn e T ev ag2 cf
      (ctrlPost W (srcsView W csrc)) (.LCtrl csrc) dnew hq hnp hT hev hag2 hc0 ?_ hfab' ?_
    · rw [← hWdef]; simp only [aevPost, hlbe]
    · rw [hstpost, hlogNone hgts]
      exact .PFCtrl cf _ csrc st' dnew hcflk hpure
  | LInstr =>
    obtain ⟨_, hts0⟩ := hok
    have hgts : gevTs TS e = none := by simp [gevTs, hgev, hts0]
    refine qcfgStepEx pstep pcls TS img d0 ps hwf hwfl hnag dn e T ev ag2 cf
      (instrPost W) .LInstr dnew hq hnp hT hev hag2 hc0 ?_ hfab' ?_
    · rw [← hWdef]; simp only [aevPost, hlbe]
    · rw [hstpost, hlogNone hgts]
      exact .PFInstr cf _ st' dnew hcflk hpure
  -- THE RMW SPLIT: THE TWO SPLIT HALVES (S4 / T2-2a)
  | LExLoad xaq xbase xtvs xasrc =>
    obtain ⟨hro, _, hts0⟩ := hok
    have hgts : gevTs TS e = none := by simp [gevTs, hgev, hts0]
    have hmap := hmapOf xbase xtvs (by rw [hlbe]; rfl)
    refine qcfgStepEx pstep pcls TS img d0 ps hwf hwfl hnag dn e T ev ag2 cf
      (exloadPostRunD W xaq (srcsView W xasrc) xbase ((tlabelTs (pi TS dn) xtvs).map Prod.fst))
      (.LExLoad xaq xbase (tlabelTs (pi TS dn) xtvs) xasrc) dnew
      hq hnp hT hev hag2 hc0 ?_ hfab' ?_
    · rw [← hWdef]; simp only [aevPost, hlbe]; rw [tlabelTsFst, hmap]
    · rw [hstpost, hlogNone hgts]
      refine .PFExLoad cf ⟨ag.paSt, W, ∅⟩ xaq xbase _ xasrc st' dnew hcflk
        (hobl.2.2.1 _ _ xaq xbase xtvs _ xasrc st' dnew (tlabelTsSnd _ _).symm hpure) ?_
      show readOkD cf.pcImg cf.pcLog W xaq false xbase (tlabelTs (pi TS dn) xtvs) 0
      rw [hcimg, hclog]
      exact readOkPf pstep TS img hwf hwsi hco hwfl himg dn e T ev ag
        (.LExLoad xaq xbase xtvs xasrc) xbase xtvs false W hq hpre hnp hT hev hag hlbe trivial rfl
        hro hWdef
  | LExStore yrl ybase ydata yasrc yvsrc =>
    obtain ⟨ts, kc, R, _, hlog, hres, hrb, hrlen, hexw, _, _, hts⟩ := hok
    have hgts : gevTs TS e = some ts := by simp [gevTs, hgev, hts]
    have hpits := hpitsOf ts hts
    have hnedata : ydata ≠ [] := hdata (ts - 1) _ hlog
    have hkc : kc = pcls ag.paSt (.LExStore yrl ybase ydata yasrc yvsrc) ag.paWs := by
      have := hkcOf ts _ hts hlog; rw [hlbe] at this; exact this
    -- THE REPLAYED RESERVATION (T2-2a): same base, π-retimed column
    have hrc := replayWsRes pstep TS hwf hwsi e.1 e.2 T ag (pi TS dn) hT hag
    rw [hres, ← hWdef] at hrc
    obtain ⟨R', hR', hrbase, hrcol⟩ := resColsInv _ _ _ hrc
    -- ITS SOURCE: the po-earlier exclusive read, already processed
    obtain ⟨m, ev0, aq0, tvs0, asrc0, hmlt, hev0, hlb0, hcol0⟩ :=
      replayWsResSrc pstep TS hwf hwsi e.1 e.2 T ag R hT hag hres
    have hgev0 : gevEv TS (e.1, m) = some ev0 := by simp [gevEv, hT, hev0]
    have hwfe0 : gevWf TS (e.1, m) := by unfold gevWf; rw [hgev0]; rfl
    have he0 : (e.1, m) ∈ dn := (qorderMem TS dn e.1 m hq).2 ⟨hwfe0, by rw [hnp]; exact hmlt⟩
    rw [hrb] at hlb0
    have hrds : ∀ (jb t : Nat), R.rvTs[jb]? = some t →
        gevReads TS (e.1, m) (ybase + (jb : Int)) t := by
      intro jb t hjb
      rw [hcol0, List.getElem?_map] at hjb
      cases ht0 : tvs0[jb]? with
      | none => rw [ht0] at hjb; cases hjb
      | some p =>
        obtain ⟨t0, v0⟩ := p
        rw [ht0] at hjb
        simp only [Option.map_some, Option.some.injEq] at hjb
        subst hjb
        exact ⟨ev0.aeLb, by simp [gevLb, hgev0],
          by rw [hlb0]; exact (memTvsReads _ _ _ _).2 ⟨jb, v0, ht0, rfl⟩⟩
    have hwbs : ∀ jb : Nat, jb < R.rvTs.length → writesB TS (ybase + (jb : Int)) e ts :=
      fun jb hjb => ⟨hgts, ⟨ybase, ydata, some e.1, kc⟩, hlog,
        msgByteRun ybase ydata _ kc jb (by rw [← hrlen]; exact hjb)⟩
    refine qcfgStepEx pstep pcls TS img d0 ps hwf hwfl hnag dn e T ev ag2 cf
      (storePostRunD W yrl (srcsView W yasrc) (srcsView W yvsrc) ybase ydata.length
        (cf.pcLog.length + 1))
      (.LExStore yrl ybase ydata yasrc yvsrc) dnew hq hnp hT hev hag2 hc0 ?_ hfab' ?_
    · rw [← hWdef]; simp only [aevPost, hlbe, hts, hpits]
    · rw [hstpost, hlogSome ts _ hts hlog]
      refine .PFExStore cf ⟨ag.paSt, W, ∅⟩ yrl ybase ydata yasrc yvsrc kc R' st' dnew hcflk
        hpure hnedata hR' (by rw [hrbase, hrb]) (by rw [hrcol, List.length_map, hrlen]) ?_ ?_
      · rw [hclog, hrcol]
        exact exclOkTsPf pstep TS hwf hco hwfl dn e (e.1, m) ybase R.rvTs ts hq hnin he0 hrds
          hgts hwbs hexw
      · -- THE PINNED CLASS (G6a)
        rw [hkc]
        exact hclsobl.2.2 ag.paSt yrl ybase ydata yasrc yvsrc ag.paWs W hrelp
  -- O2 (deviation 4): THE FETCH, replayed at instruction view 0 with retimed answers
  | LIFetch base tvs =>
    obtain ⟨hif, _, hts0⟩ := hok
    have hgts : gevTs TS e = none := by simp [gevTs, hgev, hts0]
    refine qcfgStepEx pstep pcls TS img d0 ps hwf hwfl hnag dn e T ev ag2 cf W
      (.LIFetch base (tlabelTs (pi TS dn) tvs)) dnew hq hnp hT hev hag2 hc0 ?_ hfab' ?_
    · rw [← hWdef]; simp only [aevPost, hlbe]
    · rw [hstpost, hlogNone hgts]
      refine .PFIFetch cf ⟨ag.paSt, W, ∅⟩ base _ st' dnew hcflk
        (hobl.2.2.2 _ _ base tvs _ st' dnew (tlabelTsSnd _ _).symm hpure) ?_
      show ifetchOk cf.pcImg cf.pcLog 0 base (tlabelTs (pi TS dn) tvs)
      rw [hcimg, hclog]
      intro jb t' v hjb
      obtain ⟨t, htv, rfl⟩ := tlabelTsLookupInv (pi TS dn) tvs jb t' v hjb
      have hb := (ifetchByteOk0 _ _ _ _ _).1 (hif jb t v htv)
      refine (ifetchByteOk0 _ _ _ _ _).2 (logBytePf pstep TS img hwf himg dn t _ v hq ?_ hb)
      by_cases ht0 : t = 0
      · exact Or.inl ht0
      · obtain ⟨er, hter, htc⟩ :=
          hfetch e base tvs jb t v (by simp [gevLb, hgev, hlbe]) htv (by omega)
        have hin : er ∈ dn := by
          cases htc with
          | single h => exact hpre er h (gdep2Wf TS er e h).1
          | tail h1 h2 => exact qorderTcIn TS dn er _ hq (hpre _ h2 (gdep2Wf TS _ e h2).1) h1
        exact Or.inr ((elemOfFl TS dn t).2 ⟨er, hin, hter⟩)

end stepout

/-! ## §3 THE CONE'S BLOCKS -/

section coneblocks

variable {P D : Type}
variable {pstep : P → D → Wlabel → P → D → Prop}
variable {pcls : P → Wlabel → Wstate → WmClass}
variable {TS : Ptraces P D} {img : Image} {d0 : D} {ps : List P}
variable {bnd : P → Prop} [DecidablePred bnd]
variable {b2 : Gev} {ord0 : List Gev} {bord : List (Nat × Nat)} {doneB : List Gev}

/-! ### §3.1 Block identifiers -/

variable (TS bnd) in
/-- The block NUMBER of an event: how many boundary states its agent passed through
before it. -/
def bno (e : Gev) : Nat :=
  match TS.ptTrs[e.1]? with
  | some T => blkNo bnd T e.2
  | none => 0

variable (TS bnd) in
/-- The block IDENTIFIER: agent and block number. -/
def bid (e : Gev) : Nat × Nat := (e.1, bno TS bnd e)

variable (TS bnd) in
theorem bidAgent (e : Gev) : (bid TS bnd e).1 = e.1 := rfl

/-- Lean-only helper: the agent half of a block identifier. -/
theorem bidEqFst {x y : Gev} : bid TS bnd x = bid TS bnd y → x.1 = y.1 := by
  intro h
  have h' := congrArg Prod.fst h
  exact h'

/-- Lean-only helper: the block-number half of a block identifier. -/
theorem bidEqSnd {x y : Gev} : bid TS bnd x = bid TS bnd y → bno TS bnd x = bno TS bnd y := by
  intro h
  have h' := congrArg Prod.snd h
  exact h'

/-- SAME AGENT, SAME BLOCK ⟹ no boundary state strictly between. -/
theorem bidSameGap (e x : Gev) (T : Atrace P D) (m : Nat) :
    TS.ptTrs[e.1]? = some T → x.1 = e.1 → bid TS bnd x = bid TS bnd e →
    e.2 ≤ m → m + 1 ≤ x.2 → bndAt bnd T (m + 1) = false := by
  intro hT hag hbid hle1 hle2
  have hb : bno TS bnd x = bno TS bnd e := bidEqSnd hbid
  have hb' : blkNo bnd T x.2 = blkNo bnd T e.2 := by
    unfold bno at hb
    rw [hag, hT] at hb
    exact hb
  exact blkNoGap bnd T e.2 x.2 m hb'.symm hle1 hle2

/-- SAME AGENT, DIFFERENT BLOCKS ⟹ block numbers and trace indices agree on their
order. -/
theorem bnoLtIndex (x y : Gev) :
    bno TS bnd x < bno TS bnd y → x.1 = y.1 → x.2 < y.2 := by
  intro hlt hag
  unfold bno at hlt
  rw [hag] at hlt
  cases hT : TS.ptTrs[y.1]? with
  | none => rw [hT] at hlt; exact absurd hlt (Nat.lt_irrefl 0)
  | some T => rw [hT] at hlt; exact blkNoLtIndex bnd T _ _ hlt

theorem bnoLeOfIndex (x y : Gev) :
    x.1 = y.1 → x.2 ≤ y.2 → bno TS bnd x ≤ bno TS bnd y := by
  intro hag hle
  unfold bno
  rw [hag]
  cases hT : TS.ptTrs[y.1]? with
  | none => exact Nat.le_refl 0
  | some T => exact blkNoMono bnd T _ _ hle

/-! ### §3.2 Memory events, cross sources and cross targets -/

variable (TS) in
/-- A MEMORY event: its label appends a message or reads one. -/
def WeakRobustCone.isMem (e : Gev) : Prop :=
  ∃ l, gevLb TS e = some l ∧ (lbWrites l = true ∨ lbLoads l = true)

/-- A fulfil writes. -/
theorem tsWrites (hwf : ptracesWf pstep TS) (e : Gev) (ts : Nat) :
    gevTs TS e = some ts → ∃ l, gevLb TS e = some l ∧ lbWrites l = true := by
  intro hts
  cases hev : gevEv TS e with
  | none => simp [gevTs, hev] at hts
  | some ev =>
    obtain ⟨T, ag, ag', st', f, -, -, -, -, hok, -⟩ := gevStep pstep TS e ev hwf hev
    refine ⟨ev.aeLb, by simp [gevLb, hev], ?_⟩
    cases hlw : lbWrites ev.aeLb with
    | true => rfl
    | false =>
      have hn := lbWritesTsNone _ _ _ _ _ _ _ hok hlw
      simp [gevTs, hev, hn] at hts

theorem tsMem (hwf : ptracesWf pstep TS) (e : Gev) (ts : Nat) :
    gevTs TS e = some ts → WeakRobustCone.isMem TS e := by
  intro hts
  obtain ⟨l, hl, hw⟩ := tsWrites hwf e ts hts
  exact ⟨l, hl, Or.inl hw⟩

/-- A read loads. -/
theorem readsLoads (e : Gev) (a : Int) (t : Nat) :
    gevReads TS e a t → ∃ l, gevLb TS e = some l ∧ lbLoads l = true := by
  rintro ⟨l, hl, hin⟩
  refine ⟨l, hl, ?_⟩
  cases l <;> first | rfl | (simp [lbReads] at hin)

theorem readsMem (e : Gev) (a : Int) (t : Nat) :
    gevReads TS e a t → WeakRobustCone.isMem TS e := by
  intro hr
  obtain ⟨l, hl, hw⟩ := readsLoads e a t hr
  exact ⟨l, hl, Or.inr hw⟩

variable (TS) in
/-- A CROSS SOURCE: an event with a `gdep2` edge to another agent. -/
def xsrc (e : Gev) : Prop := ∃ v, gdep2 TS e v ∧ e.1 ≠ v.1

theorem xsrcMem (hwf : ptracesWf pstep TS) (e : Gev) : xsrc TS e → WeakRobustCone.isMem TS e := by
  rintro ⟨v, hd, hne⟩
  obtain ⟨ts, hts⟩ := crossEdgeFulfil TS e v hd hne
  exact tsMem hwf e ts hts

/-- DELIVERABLE 2b: CROSS TARGETS ARE MEMORY EVENTS. -/
theorem crossTgtMem (hwf : ptracesWf pstep TS) (e1 e2 : Gev) :
    gdep2 TS e1 e2 → e1.1 ≠ e2.1 → WeakRobustCone.isMem TS e2 := by
  rintro ((hpo | hrf) | hE) hne
  · exact absurd hpo.1 hne
  · obtain ⟨ts, a, -, hrd⟩ := hrf
    exact readsMem e2 a ts hrd
  · obtain ⟨t1, t2, -, hts2, -⟩ := gETsLtEx TS e1 e2 hE
    exact tsMem hwf e2 t2 hts2

variable (hwf : ptracesWf pstep TS)
variable (hwsi : ptracesWsInit TS)
variable (hco : ∀ a, coTc TS a)
variable (hwfl : writesFulfilled TS)
variable (hlf : latFreeProg pstep)
variable (hobl : tsOblivious pstep)
variable (hcls : clsCanonical pcls TS)
variable (hclsobl : pclsObl pcls)
variable (himg : TS.ptImg = img)
variable (hnag : TS.ptTrs.length = ps.length)
variable (hdata : ∀ (p : Nat) (m : Wmsg), TS.ptLog[p]? = some m → m.wmData ≠ [])
variable (hdf : ∀ (j : Nat) (T : Atrace P D) (k : Nat) (ev : Aev D), TS.ptTrs[j]? = some T →
  T.atEvs[k]? = some ev → ev.aeDev = none)
variable (hps0 : ∀ (j : Nat) (T : Atrace P D) (ag0 : Wpagent P), TS.ptTrs[j]? = some T →
  T.atAgs[0]? = some ag0 → ps[j]? = some ag0.paSt)
variable (hee : eeOk TS)
variable (hfetch : fetchSrcOk TS)
variable (hcsl : ∀ e1 e2, gdep2 TS e1 e2 → e1.1 ≠ e2.1 →
  ∀ (T : Atrace P D), TS.ptTrs[e1.1]? = some T →
  ∀ (k' : Nat) (ev' : Aev D), e1.2 < k' → T.atEvs[k']? = some ev' →
  (∀ (k'' : Nat) (ag'' : Wpagent P), e1.2 < k'' → k'' ≤ k' →
     T.atAgs[k'']? = some ag'' → ¬ bnd ag''.paSt) →
  lbWrites ev'.aeLb = false ∧ lbLoads ev'.aeLb = false)

include hwf hcsl in
/-- DELIVERABLE 2a: CROSS SOURCES ARE BLOCK-LAST MEMORY EVENTS. -/
theorem crossSrcLast (e1 e2 x : Gev) :
    gdep2 TS e1 e2 → e1.1 ≠ e2.1 →
    x.1 = e1.1 → e1.2 < x.2 → bid TS bnd x = bid TS bnd e1 → gevWf TS x →
    ¬ WeakRobustCone.isMem TS x := by
  intro hd hne hag hlt hbid hwfx
  obtain ⟨hwf1, -⟩ := gdep2Wf TS e1 e2 hd
  obtain ⟨T, hT, -⟩ := (gevWfBounds TS e1).1 hwf1
  have hTx : TS.ptTrs[x.1]? = some T := by rw [hag]; exact hT
  have hxlt : x.2 < T.atEvs.length := by
    obtain ⟨T', hT', hxlt⟩ := (gevWfBounds TS x).1 hwfx
    rw [hTx] at hT'
    cases hT'
    exact hxlt
  obtain ⟨ev', hev'⟩ := Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 hxlt)
  have hnob : ∀ (k'' : Nat) (ag'' : Wpagent P), e1.2 < k'' → k'' ≤ x.2 →
      T.atAgs[k'']? = some ag'' → ¬ bnd ag''.paSt := by
    intro k'' ag'' h1 h2 hlk
    obtain ⟨m, rfl⟩ : ∃ m, k'' = m + 1 := ⟨k'' - 1, by omega⟩
    exact bndAtFalse bnd T (m + 1) ag'' hlk
      (bidSameGap e1 x T m hT hag hbid (by omega) (by omega))
  obtain ⟨hw, hl⟩ := hcsl e1 e2 hd hne T hT x.2 ev' hlt hev' hnob
  rintro ⟨l, hlb, hor⟩
  have hlb' : gevLb TS x = some ev'.aeLb := by simp [gevLb, gevEv, hTx, hev']
  rw [hlb'] at hlb
  have hleq : ev'.aeLb = l := Option.some.inj hlb
  subst hleq
  rcases hor with hc | hc
  · rw [hc] at hw; cases hw
  · rw [hc] at hl; cases hl

include hwf hcsl in
/-- AT MOST ONE CROSS SOURCE PER BLOCK. -/
theorem xsrcUnique (w1 w2 : Gev) :
    xsrc TS w1 → xsrc TS w2 → bid TS bnd w1 = bid TS bnd w2 →
    gevWf TS w1 → gevWf TS w2 → w1 = w2 := by
  intro hx1 hx2 hbid hw1 hw2
  have hag : w1.1 = w2.1 := bidEqFst hbid
  have hkey : ∀ u v, xsrc TS u → bid TS bnd u = bid TS bnd v → v.1 = u.1 →
      u.2 < v.2 → gevWf TS v → WeakRobustCone.isMem TS v → False := by
    rintro u v ⟨z, hd, hne⟩ hb hag' hlt hwfv hm
    exact crossSrcLast hwf hcsl u z v hd hne hag' hlt hb.symm hwfv hm
  rcases Nat.lt_trichotomy w1.2 w2.2 with hlt | heq | hgt
  · exact (hkey w1 w2 hx1 hbid hag.symm hlt hw2 (xsrcMem hwf w2 hx2)).elim
  · exact Prod.ext hag heq
  · exact (hkey w2 w1 hx2 hbid.symm hag hgt hw1 (xsrcMem hwf w1 hx1)).elim

include hwf hcsl in
/-- A block's cross TARGETS sit program-order at-or-before its cross SOURCE. -/
theorem xtgtLeXsrc (y w : Gev) :
    WeakRobustCone.isMem TS y → xsrc TS w → bid TS bnd y = bid TS bnd w → gevWf TS y →
    y.2 ≤ w.2 := by
  rintro hm ⟨z, hd, hne⟩ hbid hwfy
  rcases Nat.lt_or_ge w.2 y.2 with hgt | hle
  · have hag : y.1 = w.1 := bidEqFst hbid
    exact (crossSrcLast hwf hcsl w z y hd hne hag hgt hbid hwfy hm).elim
  · exact hle

/-! ### §3.3 SAME-AGENT `gdep2` EDGES RESPECT PROGRAM ORDER -/

include hwf hee in
theorem gdep2SaLt (x y : Gev) : gdep2 TS x y → x.1 = y.1 → x.2 < y.2 := by
  rintro (hd | ⟨r, hat⟩) hag
  · exact gdepSameAgentLt pstep TS x y hwf hd hag
  · obtain ⟨a, hra⟩ := gEAtGERa TS r x y hat
    have hra' := hra
    obtain ⟨l, ts, tstar, that, -, -, hleaf, -, hts1, hts2, -, hlt⟩ := hra'
    have hfl : tstar ≤ rdFloor TS r a := lvalGe id (rdLeaves TS r a) tstar hleaf
    rcases Nat.lt_trichotomy x.2 y.2 with h | h | h
    · exact h
    · exfalso
      have hxy : x = y := Prod.ext hag h
      rw [hxy] at hts1
      have : that = tstar := Option.some.inj (hts2.symm.trans hts1)
      omega
    · exfalso
      have := hee r a x y x tstar hra hag.symm h hts1
      omega

include hwf hee in
theorem gdep2SaNe (x y : Gev) : gdep2 TS x y → x.1 = y.1 → x ≠ y := by
  intro hd hag hxy
  have := gdep2SaLt hwf hee x y hd hag
  rw [hxy] at this
  exact Nat.lt_irrefl _ this

/-! ### §3.4 Decidability of the cross-source predicate -/

instance xsrcDec (TS : Ptraces P D) (e : Gev) : Decidable (xsrc TS e) :=
  decidable_of_iff (∃ v ∈ gevEnum TS, gdep2 TS e v ∧ e.1 ≠ v.1)
    ⟨fun ⟨v, _, h⟩ => ⟨v, h⟩,
     fun ⟨v, hd, hne⟩ => ⟨v, (elemOfGevEnum TS v).2 (gdep2Wf TS e v hd).2, hd, hne⟩⟩

/-! ## §4 THE CONE AND ITS BLOCK-CONTRACTED GRAPH -/

variable (hb2wf : gevWf TS b2)
variable (hrr : ¬ tc (gdep2 TS) b2 b2)
variable (hb2mem : WeakRobustCone.isMem TS b2)
variable (hq0 : Qinv pstep pcls TS ⟨d0, []⟩ img d0 ps ord0)
variable (hmem0 : ∀ e, e ∈ ord0 ↔ (gevWf TS e ∧ tc (gdep2 TS) e b2))

variable (b2 ord0) in
/-- The cone WITH the bad read: the carrier of every ordering argument below. -/
def cl : List Gev := ord0 ++ [b2]

include hmem0 in
theorem ord0Wf (e : Gev) : e ∈ ord0 → gevWf TS e := fun he => ((hmem0 e).1 he).1

include hmem0 in
theorem ord0Tc (e : Gev) : e ∈ ord0 → tc (gdep2 TS) e b2 := fun he => ((hmem0 e).1 he).2

include hrr hmem0 in
theorem b2Nin : b2 ∉ ord0 := fun he => hrr (ord0Tc hmem0 b2 he)

include hmem0 in
theorem b2Pre (x : Gev) : gdep2 TS x b2 → gevWf TS x → x ∈ ord0 :=
  fun hd hw => (hmem0 x).2 ⟨hw, tc_once hd⟩

include hmem0 in
theorem ord0Dc (x y : Gev) : y ∈ ord0 → gdep2 TS x y → gevWf TS x → x ∈ ord0 :=
  fun hy hd hw => (hmem0 x).2 ⟨hw, tc_l hd (ord0Tc hmem0 y hy)⟩

variable (b2 ord0) in
theorem elemOfCl (e : Gev) : e ∈ cl b2 ord0 ↔ (e ∈ ord0 ∨ e = b2) := by
  unfold cl
  rw [List.mem_append, List.mem_singleton]

variable (b2 ord0) in
theorem ord0Cl (e : Gev) : e ∈ ord0 → e ∈ cl b2 ord0 :=
  fun he => (elemOfCl b2 ord0 e).2 (Or.inl he)

variable (b2 ord0) in
theorem b2Cl : b2 ∈ cl b2 ord0 := (elemOfCl b2 ord0 b2).2 (Or.inr rfl)

include hb2wf hmem0 in
theorem clWf (e : Gev) : e ∈ cl b2 ord0 → gevWf TS e := by
  intro he
  rcases (elemOfCl b2 ord0 e).1 he with h | h
  · exact ord0Wf hmem0 e h
  · rw [h]; exact hb2wf

include hmem0 in
/-- …and the cone is DOWNWARD CLOSED. -/
theorem clDc (x y : Gev) : y ∈ cl b2 ord0 → gdep2 TS x y → gevWf TS x → x ∈ ord0 := by
  intro hy hd hw
  rcases (elemOfCl b2 ord0 y).1 hy with h | h
  · exact ord0Dc hmem0 x y h hd hw
  · rw [h] at hd; exact b2Pre hmem0 x hd hw

include hmem0 in
theorem clDc' (x y : Gev) : y ∈ cl b2 ord0 → gdep2 TS x y → gevWf TS x → x ∈ cl b2 ord0 :=
  fun hy hd hw => ord0Cl b2 ord0 x (clDc hmem0 x y hy hd hw)

include hwf hwsi hco hwfl hlf hobl hcls hclsobl himg hdata hdf hfetch hb2wf hrr hq0 hmem0 in
/-- ONE more `QinvStep`: the cone plus the bad read is still a `qorder`. -/
theorem HQcl : Qinv pstep pcls TS ⟨d0, []⟩ img d0 ps (cl b2 ord0) :=
  QinvStep pstep pcls TS ⟨d0, []⟩ img d0 ps hwf hwsi hco hwfl hlf hobl hcls hclsobl himg hdata
    (ptracesWitNil TS d0 hdf) hfetch ord0 b2 hq0 hb2wf (b2Nin hrr hmem0)
    (fun e' hd hw' => b2Pre hmem0 e' (gdep3NilGdep2 TS d0 e' b2 hd) hw')

include hb2wf hrr hq0 hmem0 in
theorem Hqcl : qorder TS (cl b2 ord0) :=
  qorderStep TS ord0 b2 (QinvOrder pstep pcls TS ⟨d0, []⟩ img d0 ps ord0 hq0) hb2wf
    (b2Nin hrr hmem0) (fun e' hd hw' => b2Pre hmem0 e' hd hw')

include hq0 in
theorem ord0Nodup : ord0.Nodup := (QinvOrder pstep pcls TS ⟨d0, []⟩ img d0 ps ord0 hq0).1

include hb2wf hrr hq0 hmem0 in
theorem clNodup : (cl b2 ord0).Nodup := (Hqcl hb2wf hrr hq0 hmem0).1

/-! ### §4.1 The event-level position, and cone acyclicity -/

variable (b2 ord0) in
def Idx (e : Gev) : Nat := lidx (cl b2 ord0) e

variable (b2 ord0) in
theorem IdxLookup (e : Gev) : e ∈ cl b2 ord0 → (cl b2 ord0)[Idx b2 ord0 e]? = some e :=
  lidxLookup _ e

variable (b2 ord0) in
theorem IdxLt (e : Gev) : e ∈ cl b2 ord0 → Idx b2 ord0 e < (cl b2 ord0).length :=
  lidxLt _ e

include hb2wf hrr hq0 hmem0 in
theorem IdxMono (x y : Gev) :
    x ∈ cl b2 ord0 → y ∈ cl b2 ord0 → tc (gdep2 TS) x y → Idx b2 ord0 x < Idx b2 ord0 y := by
  intro hx hy htc
  obtain ⟨i, hi, hlk⟩ := qorderTcIndex TS (cl b2 ord0) x y (Idx b2 ord0 y)
    (Hqcl hb2wf hrr hq0 hmem0) (IdxLookup b2 ord0 y hy) htc
  have hxi : Idx b2 ord0 x = i := lidxInj _ x i (clNodup hb2wf hrr hq0 hmem0) hlk
  rw [hxi]
  exact hi

include hb2wf hrr hq0 hmem0 in
theorem coneAcyc (e : Gev) : e ∈ cl b2 ord0 → ¬ tc (gdep2 TS) e e := by
  intro he htc
  exact Nat.lt_irrefl _ (IdxMono hb2wf hrr hq0 hmem0 e e he he htc)

/-! ### §4.2 The contracted relation `Rblk` and its acyclicity -/

variable (TS bnd b2 ord0) in
def Rblk (B C : Nat × Nat) : Prop :=
  B ≠ C ∧ ∃ x y, x ∈ cl b2 ord0 ∧ y ∈ cl b2 ord0 ∧ bid TS bnd x = B ∧ bid TS bnd y = C ∧
    gdep2 TS x y

instance RblkDec (TS : Ptraces P D) (bnd : P → Prop) [DecidablePred bnd] (b2 : Gev)
    (ord0 : List Gev) : DecidableRel (Rblk TS bnd b2 ord0) := fun B C =>
  decidable_of_iff (B ≠ C ∧ ∃ x ∈ cl b2 ord0, ∃ y ∈ cl b2 ord0,
      bid TS bnd x = B ∧ bid TS bnd y = C ∧ gdep2 TS x y)
    ⟨fun ⟨hne, x, hx, y, hy, h⟩ => ⟨hne, x, y, hx, hy, h⟩,
     fun ⟨hne, x, y, hx, hy, h⟩ => ⟨hne, x, hx, y, hy, h⟩⟩

variable (TS bnd b2 ord0) in
/-- `oke y` — "no cross source of `y`'s block sits strictly BEFORE `y`". -/
def oke (y : Gev) : Prop :=
  ∀ w ∈ cl b2 ord0, bid TS bnd w = bid TS bnd y → xsrc TS w → y.2 ≤ w.2

instance okeDec (TS : Ptraces P D) (bnd : P → Prop) [DecidablePred bnd] (b2 : Gev)
    (ord0 : List Gev) (y : Gev) : Decidable (oke TS bnd b2 ord0 y) := by
  unfold oke; infer_instance

theorem okeUse (y w : Gev) :
    oke TS bnd b2 ord0 y → w ∈ cl b2 ord0 → bid TS bnd w = bid TS bnd y → xsrc TS w →
    y.2 ≤ w.2 :=
  fun hall hw => hall w hw

theorem notOke (y : Gev) :
    ¬ oke TS bnd b2 ord0 y →
    ∃ w, w ∈ cl b2 ord0 ∧ bid TS bnd w = bid TS bnd y ∧ xsrc TS w ∧ w.2 < y.2 := by
  intro hno
  unfold oke at hno
  obtain ⟨w, hw, hnq⟩ := not_Forall_Exists hno
  obtain ⟨h1, h2, h3⟩ := notImpl2 _ _ _ hnq
  exact ⟨w, hw, h1, h2, by omega⟩

include hwf hcsl hb2wf hmem0 in
/-- A block's UNIQUE cross source is `oke`. -/
theorem xsrcOke (w : Gev) : w ∈ cl b2 ord0 → xsrc TS w → oke TS bnd b2 ord0 w := by
  intro hw hx u hu hbu hxu
  have : u = w := xsrcUnique hwf hcsl u w hxu hx hbu (clWf hb2wf hmem0 u hu) (clWf hb2wf hmem0 w hw)
  rw [this]
  exact Nat.le_refl _

include hwf hee hcsl hb2wf hmem0 in
/-- THE ONE-EDGE STEP: from an `oke` event of `B`, a contracted edge `B → C` is
realized by a `tc gdep2` path to an `oke` event of `C`. -/
theorem oneedge (B C : Nat × Nat) :
    Rblk TS bnd b2 ord0 B C →
    ∀ z, z ∈ cl b2 ord0 → bid TS bnd z = B → oke TS bnd b2 ord0 z →
    ∃ y, y ∈ cl b2 ord0 ∧ bid TS bnd y = C ∧ oke TS bnd b2 ord0 y ∧ tc (gdep2 TS) z y := by
  rintro ⟨hne, x, y', hxcl, hycl, hbx, hby, hd⟩ z hzcl hbz hokez
  have hzwf := clWf hb2wf hmem0 z hzcl
  have hxwf := clWf hb2wf hmem0 x hxcl
  have hywf := clWf hb2wf hmem0 y' hycl
  have hzx : bid TS bnd z = bid TS bnd x := hbz.trans hbx.symm
  have hzag : z.1 = x.1 := bidEqFst hzx
  have hzno : bno TS bnd z = bno TS bnd x := bidEqSnd hzx
  by_cases hsa : x.1 = y'.1
  · -- SAME-AGENT edge
    have hlt := gdep2SaLt hwf hee x y' hd hsa
    have hle : bno TS bnd x ≤ bno TS bnd y' := bnoLeOfIndex x y' hsa (by omega)
    have hbno : bno TS bnd x < bno TS bnd y' := by
      rcases Nat.lt_or_ge (bno TS bnd x) (bno TS bnd y') with h | h
      · exact h
      · exfalso
        apply hne
        rw [← hbx, ← hby]
        exact Prod.ext hsa (show bno TS bnd x = bno TS bnd y' by omega)
    have hgpo : ∀ u, u ∈ cl b2 ord0 → bid TS bnd u = C → WeakRobustGraph.gpo TS z u := by
      intro u hu hbu
      have hbu' : bid TS bnd u = bid TS bnd y' := hbu.trans hby.symm
      have huag : u.1 = y'.1 := bidEqFst hbu'
      have huno : bno TS bnd u = bno TS bnd y' := bidEqSnd hbu'
      refine ⟨by rw [hzag, hsa, huag], ?_, hzwf, clWf hb2wf hmem0 u hu⟩
      exact bnoLtIndex (TS := TS) (bnd := bnd) z u (by omega) (by rw [hzag, hsa, huag])
    by_cases hok : oke TS bnd b2 ord0 y'
    · exact ⟨y', hycl, hby, hok, tc_once (gpoGdep2 TS z y' (hgpo y' hycl hby))⟩
    · obtain ⟨w, hw, hbw, hxw, -⟩ := notOke _ hok
      exact ⟨w, hw, hbw.trans hby, xsrcOke hwf hcsl hb2wf hmem0 w hw hxw,
        tc_once (gpoGdep2 TS z w (hgpo w hw (hbw.trans hby)))⟩
  · -- CROSS edge
    have hxs : xsrc TS x := ⟨y', hd, hsa⟩
    have hzx' : rtc (gdep2 TS) z x := by
      have hle : z.2 ≤ x.2 := okeUse z x hokez hxcl hzx.symm hxs
      rcases Nat.lt_or_ge z.2 x.2 with h | h
      · exact rtc_once (gpoGdep2 TS z x ⟨hzag, h, hzwf, hxwf⟩)
      · have hzx2 : z = x := Prod.ext hzag (by omega)
        rw [hzx2]
        exact rtc_refl _
    have hokey : oke TS bnd b2 ord0 y' := by
      by_cases h : oke TS bnd b2 ord0 y'
      · exact h
      · exfalso
        obtain ⟨w, hw, hbw, hxw, hlt⟩ := notOke _ h
        have hmemy := crossTgtMem hwf x y' hd hsa
        have := xtgtLeXsrc hwf hcsl y' w hmemy hxw hbw.symm hywf
        omega
    exact ⟨y', hycl, hby, hokey, tc_rtc_l hzx' (tc_once hd)⟩

include hwf hee hcsl hb2wf hmem0 in
/-- …iterated along a contracted PATH. -/
theorem chain2 (B C : Nat × Nat) :
    tc (Rblk TS bnd b2 ord0) B C →
    ∀ z, z ∈ cl b2 ord0 → bid TS bnd z = B → oke TS bnd b2 ord0 z →
    ∃ y, y ∈ cl b2 ord0 ∧ bid TS bnd y = C ∧ oke TS bnd b2 ord0 y ∧ tc (gdep2 TS) z y := by
  intro htc
  induction htc with
  | single hR => exact oneedge hwf hee hcsl hb2wf hmem0 _ _ hR
  | tail _ hR ih =>
    intro z hz hbz hokez
    obtain ⟨y', hy', hby', hoky', htc1⟩ := ih z hz hbz hokez
    obtain ⟨y, hy, hby, hoky, htc2⟩ := oneedge hwf hee hcsl hb2wf hmem0 _ _ hR y' hy' hby' hoky'
    exact ⟨y, hy, hby, hoky, tc_transitive htc1 htc2⟩

include hwf hee hcsl hb2wf hrr hq0 hmem0 in
/-- DELIVERABLE 3: THE CONTRACTED GRAPH IS ACYCLIC ON THE CONE. -/
theorem RblkAcyc (B : Nat × Nat) : ¬ tc (Rblk TS bnd b2 ord0) B B := by
  intro htc
  obtain ⟨C, -, x0, y0, hx0, -, hbx0, -⟩ := tcFirst _ B B htc
  have hstart : ∃ z, z ∈ cl b2 ord0 ∧ bid TS bnd z = B ∧ oke TS bnd b2 ord0 z := by
    by_cases hok : oke TS bnd b2 ord0 x0
    · exact ⟨x0, hx0, hbx0, hok⟩
    · obtain ⟨w, hw, hbw, hxw, -⟩ := notOke _ hok
      exact ⟨w, hw, hbw.trans hbx0, xsrcOke hwf hcsl hb2wf hmem0 w hw hxw⟩
  have hdesc : ∀ n z, z ∈ cl b2 ord0 → bid TS bnd z = B → oke TS bnd b2 ord0 z →
      (cl b2 ord0).length - Idx b2 ord0 z ≤ n → False := by
    intro n
    induction n with
    | zero =>
      intro z hz _ _ hlen
      have := IdxLt b2 ord0 z hz
      omega
    | succ n ih =>
      intro z hz hbz hokez hlen
      obtain ⟨y, hy, hby, hoky, htcy⟩ := chain2 hwf hee hcsl hb2wf hmem0 B B htc z hz hbz hokez
      have hlt := IdxMono hb2wf hrr hq0 hmem0 z y hz hy htcy
      have := IdxLt b2 ord0 y hy
      exact ih y hy hby hoky (by omega)
  obtain ⟨z, hz, hbz, hokez⟩ := hstart
  exact hdesc _ z hz hbz hokez (Nat.le_refl _)

/-! ### §4.3 The reader's block is a SINK -/

include hwf hee hcsl hb2wf hrr hb2mem hmem0 in
theorem b2blkNoOut (C : Nat × Nat) : ¬ Rblk TS bnd b2 ord0 (bid TS bnd b2) C := by
  rintro ⟨hne, x, y, hx, hy, hbx, hby, hd⟩
  have hxwf := clWf hb2wf hmem0 x hx
  have hywf := clWf hb2wf hmem0 y hy
  have hagx : x.1 = b2.1 := bidEqFst hbx
  have hnox : bno TS bnd x = bno TS bnd b2 := bidEqSnd hbx
  have hyne : y ≠ b2 := by
    intro h
    rw [h] at hby
    exact hne hby
  have hyord : y ∈ ord0 := by
    rcases (elemOfCl b2 ord0 y).1 hy with h | h
    · exact h
    · exact absurd h hyne
  have htcy := ord0Tc hmem0 y hyord
  rcases Nat.lt_trichotomy b2.2 x.2 with hlt | heq | hgt
  · have hxord : x ∈ ord0 := by
      rcases (elemOfCl b2 ord0 x).1 hx with h | h
      · exact h
      · exfalso; rw [h] at hlt; exact Nat.lt_irrefl _ hlt
    exact hrr (tc_l (gpoGdep2 TS b2 x ⟨hagx.symm, hlt, hb2wf, hxwf⟩) (ord0Tc hmem0 x hxord))
  · have hxb2 : x = b2 := Prod.ext hagx heq.symm
    rw [hxb2] at hd
    exact hrr (tc_l hd htcy)
  · by_cases hsa : x.1 = y.1
    · have hlt2 := gdep2SaLt hwf hee x y hd hsa
      have hle := bnoLeOfIndex (TS := TS) (bnd := bnd) x y hsa (by omega)
      have hbno : bno TS bnd x < bno TS bnd y := by
        rcases Nat.lt_or_ge (bno TS bnd x) (bno TS bnd y) with h | h
        · exact h
        · exfalso
          apply hne
          rw [← hbx, ← hby]
          exact Prod.ext hsa (show bno TS bnd x = bno TS bnd y by omega)
      have hag2 : b2.1 = y.1 := hagx.symm.trans hsa
      exact hrr (tc_l (gpoGdep2 TS b2 y ⟨hag2, bnoLtIndex (TS := TS) (bnd := bnd) b2 y (by omega) hag2, hb2wf, hywf⟩)
        htcy)
    · exact crossSrcLast hwf hcsl x y b2 hd hsa hagx.symm hgt hbx.symm hb2wf hb2mem

variable (TS bnd b2 ord0) in
/-- The relation actually sorted: `Rblk` plus an edge from every other block INTO
the reader's, which forces the reader's block last. -/
def Rblk' (B C : Nat × Nat) : Prop :=
  Rblk TS bnd b2 ord0 B C ∨ (C = bid TS bnd b2 ∧ B ≠ bid TS bnd b2)

instance Rblk'Dec (TS : Ptraces P D) (bnd : P → Prop) [DecidablePred bnd] (b2 : Gev)
    (ord0 : List Gev) : DecidableRel (Rblk' TS bnd b2 ord0) := fun B C => by
  unfold Rblk'; infer_instance

include hwf hee hcsl hb2wf hrr hb2mem hmem0 in
theorem tcRblkFromB2 (C : Nat × Nat) : ¬ tc (Rblk TS bnd b2 ord0) (bid TS bnd b2) C := by
  intro htc
  obtain ⟨D', hR⟩ := tcFirst _ _ _ htc
  exact b2blkNoOut hwf hee hcsl hb2wf hrr hb2mem hmem0 D' hR

include hwf hee hcsl hb2wf hrr hb2mem hmem0 in
theorem tcRblk'Rblk (B C : Nat × Nat) :
    tc (Rblk' TS bnd b2 ord0) B C → C ≠ bid TS bnd b2 → tc (Rblk TS bnd b2 ord0) B C := by
  intro htc
  induction htc with
  | single hR =>
    intro hne
    rcases hR with hR | ⟨heq, -⟩
    · exact tc_once hR
    · exact absurd heq hne
  | @tail B' C' _ hR ih =>
    intro hne
    rcases hR with hR | ⟨heq, -⟩
    · have hB' : B' ≠ bid TS bnd b2 := by
        intro h
        rw [h] at hR
        exact b2blkNoOut hwf hee hcsl hb2wf hrr hb2mem hmem0 C' hR
      exact tc_r (ih hB') hR
    · exact absurd heq hne

include hwf hee hcsl hb2wf hrr hb2mem hq0 hmem0 in
theorem Rblk'Acyc (B : Nat × Nat) : ¬ tc (Rblk' TS bnd b2 ord0) B B := by
  intro htc
  by_cases hB : B = bid TS bnd b2
  · rw [hB] at htc
    obtain ⟨D', hR⟩ := tcFirst _ _ _ htc
    rcases hR with hR | ⟨-, hc⟩
    · exact b2blkNoOut hwf hee hcsl hb2wf hrr hb2mem hmem0 D' hR
    · exact hc rfl
  · exact RblkAcyc hwf hee hcsl hb2wf hrr hq0 hmem0 B
      (tcRblk'Rblk hwf hee hcsl hb2wf hrr hb2mem hmem0 B B htc hB)

variable (TS bnd b2 ord0) in
/-- The cone's block identifiers. -/
def bids : List (Nat × Nat) := removeDups ((cl b2 ord0).map (bid TS bnd))

variable (TS bnd b2 ord0) in
theorem elemOfBids (B : Nat × Nat) :
    B ∈ bids TS bnd b2 ord0 ↔ ∃ e, e ∈ cl b2 ord0 ∧ bid TS bnd e = B := by
  unfold bids
  rw [elem_of_remove_dups, List.mem_map]

variable (TS bnd b2 ord0) in
theorem bidsNodup : (bids TS bnd b2 ord0).Nodup := NoDup_remove_dups

/-! ## §5 THE BLOCK-CONTIGUOUS ENUMERATION -/

variable (hbordnd : bord.Nodup)
variable (hbordmem : ∀ B, B ∈ bord ↔ B ∈ bids TS bnd b2 ord0)
variable (hbordlt : ∀ (i j : Nat) (B C : Nat × Nat), bord[i]? = some B → bord[j]? = some C →
  Rblk' TS bnd b2 ord0 B C → i < j)

variable (bord) in
def WeakRobustCone.bpos (B : Nat × Nat) : Nat := lidx bord B

include hbordmem in
theorem bidInBord (e : Gev) : e ∈ cl b2 ord0 → bid TS bnd e ∈ bord :=
  fun he => (hbordmem _).2 ((elemOfBids TS bnd b2 ord0 _).2 ⟨e, he, rfl⟩)

include hbordmem in
theorem bposLookup (e : Gev) :
    e ∈ cl b2 ord0 → bord[WeakRobustCone.bpos bord (bid TS bnd e)]? = some (bid TS bnd e) :=
  fun he => lidxLookup bord _ (bidInBord hbordmem e he)

include hbordmem in
theorem bposInj (x y : Gev) :
    x ∈ cl b2 ord0 → y ∈ cl b2 ord0 →
    WeakRobustCone.bpos bord (bid TS bnd x) = WeakRobustCone.bpos bord (bid TS bnd y) →
    bid TS bnd x = bid TS bnd y :=
  fun hx hy heq => lidxEqElem bord _ _ (bidInBord hbordmem x hx) (bidInBord hbordmem y hy) heq

variable (TS bnd bord) in
/-- THE KEY: block position, then trace index. -/
def klt (x y : Gev) : Prop :=
  WeakRobustCone.bpos bord (bid TS bnd x) < WeakRobustCone.bpos bord (bid TS bnd y) ∨
  (WeakRobustCone.bpos bord (bid TS bnd x) = WeakRobustCone.bpos bord (bid TS bnd y) ∧
    x.2 < y.2)

instance kltDec (TS : Ptraces P D) (bnd : P → Prop) [DecidablePred bnd] (bord : List (Nat × Nat))
    (x y : Gev) : Decidable (klt TS bnd bord x y) := by
  unfold klt; infer_instance

theorem kltTrans (x y z : Gev) :
    klt TS bnd bord x y → klt TS bnd bord y z → klt TS bnd bord x z := by
  unfold klt
  intro h1 h2
  omega

theorem kltIrrefl (x : Gev) : ¬ klt TS bnd bord x x := by
  unfold klt
  omega

theorem kltTotal (x y : Gev) :
    klt TS bnd bord x y ∨ klt TS bnd bord y x ∨
    (WeakRobustCone.bpos bord (bid TS bnd x) = WeakRobustCone.bpos bord (bid TS bnd y) ∧
      x.2 = y.2) := by
  unfold klt
  omega

include hwf hee hbordmem hbordlt in
/-- DELIVERABLE 3, CONSUMED: every `gdep2` edge of the cone strictly increases the
key. -/
theorem gdep2Klt (x y : Gev) :
    x ∈ cl b2 ord0 → y ∈ cl b2 ord0 → gdep2 TS x y → klt TS bnd bord x y := by
  intro hx hy hd
  by_cases heq : bid TS bnd x = bid TS bnd y
  · exact Or.inr ⟨by rw [heq], gdep2SaLt hwf hee x y hd (bidEqFst heq)⟩
  · exact Or.inl (hbordlt _ _ _ _ (bposLookup hbordmem x hx) (bposLookup hbordmem y hy)
      (Or.inl ⟨heq, x, y, hx, hy, rfl, rfl, hd⟩))

include hbordmem hbordlt in
/-- …and the reader's block has the LARGEST key. -/
theorem bposB2Max (e : Gev) :
    e ∈ cl b2 ord0 → bid TS bnd e ≠ bid TS bnd b2 →
    WeakRobustCone.bpos bord (bid TS bnd e) < WeakRobustCone.bpos bord (bid TS bnd b2) :=
  fun he hne => hbordlt _ _ _ _ (bposLookup hbordmem e he)
    (bposLookup hbordmem b2 (b2Cl b2 ord0)) (Or.inr ⟨rfl, hne⟩)

include hb2wf hrr hmem0 in
/-- A cone event of the reader's own agent is program-order BEFORE the reader. -/
theorem clB2Lt (e : Gev) : e ∈ ord0 → e.1 = b2.1 → e.2 < b2.2 := by
  intro he hag
  rcases Nat.lt_trichotomy e.2 b2.2 with h | h | h
  · exact h
  · exfalso
    have hb : e = b2 := Prod.ext hag h
    have := ord0Tc hmem0 e he
    rw [hb] at this
    exact hrr this
  · exfalso
    exact hrr (tc_l (gpoGdep2 TS b2 e ⟨hag.symm, h, hb2wf, ord0Wf hmem0 e he⟩)
      (ord0Tc hmem0 e he))

include hb2wf hrr hmem0 hbordmem hbordlt in
theorem kltB2 (e : Gev) : e ∈ ord0 → klt TS bnd bord e b2 := by
  intro he
  by_cases heq : bid TS bnd e = bid TS bnd b2
  · exact Or.inr ⟨by rw [heq], clB2Lt hb2wf hrr hmem0 e he (bidEqFst heq)⟩
  · exact Or.inl (bposB2Max hbordmem hbordlt e (ord0Cl b2 ord0 e he) heq)

variable (TS bnd ord0 bord) in
/-- THE EVENT-LEVEL RELATION SORTED SECOND: the key, restricted to the cone. -/
def Rev (x y : Gev) : Prop := x ∈ ord0 ∧ y ∈ ord0 ∧ klt TS bnd bord x y

instance RevDec (TS : Ptraces P D) (bnd : P → Prop) [DecidablePred bnd] (ord0 : List Gev)
    (bord : List (Nat × Nat)) : DecidableRel (Rev TS bnd ord0 bord) := fun x y => by
  unfold Rev; infer_instance

theorem tcRevKlt (x y : Gev) : tc (Rev TS bnd ord0 bord) x y → klt TS bnd bord x y := by
  intro h
  induction h with
  | single h => exact h.2.2
  | tail _ h ih => exact kltTrans _ _ _ ih h.2.2

theorem RevAcyc (x : Gev) : ¬ tc (Rev TS bnd ord0 bord) x x :=
  fun h => kltIrrefl x (tcRevKlt x x h)

/-! ### §5.1 The enumeration itself -/

variable (hdnd : doneB.Nodup)
variable (hdmem : ∀ e, e ∈ doneB ↔ e ∈ ord0)
variable (hdord : ∀ (i j : Nat) (x y : Gev), doneB[i]? = some x → doneB[j]? = some y →
  (x ∈ ord0 ∧ y ∈ ord0 ∧ klt TS bnd bord x y) → i < j)

variable (b2 doneB) in
def doneFull : List Gev := doneB ++ [b2]

include hdmem in
theorem doneBOrd0 (e : Gev) : e ∈ doneB → e ∈ ord0 := (hdmem e).1

include hdmem in
theorem doneBCl (e : Gev) : e ∈ doneB → e ∈ cl b2 ord0 :=
  fun he => ord0Cl b2 ord0 e ((hdmem e).1 he)

variable (b2 doneB) in
theorem doneFullLen : (doneFull b2 doneB).length = doneB.length + 1 := by
  simp [doneFull]

variable (b2 doneB) in
theorem doneFullLast : (doneFull b2 doneB)[doneB.length]? = some b2 := by
  simp [doneFull]

variable (b2 doneB) in
theorem doneFullLookup (i : Nat) (x : Gev) :
    (doneFull b2 doneB)[i]? = some x →
    (i < doneB.length ∧ doneB[i]? = some x) ∨ (i = doneB.length ∧ x = b2) := by
  intro hi
  unfold doneFull at hi
  rcases Nat.lt_or_ge i doneB.length with hlt | hge
  · rw [lookup_app_l hlt] at hi
    exact Or.inl ⟨hlt, hi⟩
  · rw [lookup_app_r hge] at hi
    have hlt := lookup_lt_Some hi
    simp only [List.length_singleton] at hlt
    have h0 : i - doneB.length = 0 := by omega
    rw [h0] at hi
    have hi' : some b2 = some x := hi
    exact Or.inr ⟨by omega, (Option.some.inj hi').symm⟩

include hdmem in
theorem doneFullMem (e : Gev) : e ∈ doneFull b2 doneB ↔ e ∈ cl b2 ord0 := by
  unfold doneFull cl
  rw [List.mem_append, List.mem_append, hdmem]

include hdmem in
theorem doneFullCl (e : Gev) : e ∈ doneFull b2 doneB → e ∈ cl b2 ord0 :=
  (doneFullMem hdmem e).1

include hrr hmem0 hdnd hdmem in
theorem doneFullNodup : (doneFull b2 doneB).Nodup := by
  unfold doneFull
  refine NoDup_app.2 ⟨hdnd, ?_, NoDup_singleton⟩
  intro x hx hx2
  rw [List.mem_singleton] at hx2
  rw [hx2] at hx
  exact b2Nin hrr hmem0 ((hdmem b2).1 hx)

include hb2wf hrr hmem0 hbordmem hbordlt hdmem hdord in
/-- THE POSITIONAL ORDER: the enumeration realizes the key. -/
theorem doneFullKlt (i j : Nat) (x y : Gev) :
    (doneFull b2 doneB)[i]? = some x → (doneFull b2 doneB)[j]? = some y →
    klt TS bnd bord x y → i < j := by
  intro hi hj hk
  rcases doneFullLookup b2 doneB i x hi with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩ <;>
    rcases doneFullLookup b2 doneB j y hj with ⟨hj1, hj2⟩ | ⟨hj1, hj2⟩
  · exact hdord i j x y hi2 hj2 ⟨doneBOrd0 hdmem x (elem_of_list_lookup_2 hi2),
      doneBOrd0 hdmem y (elem_of_list_lookup_2 hj2), hk⟩
  · omega
  · exfalso
    rw [hi2] at hk
    have hk2 := kltB2 hb2wf hrr hmem0 hbordmem hbordlt y
      (doneBOrd0 hdmem y (elem_of_list_lookup_2 hj2))
    exact kltIrrefl b2 (kltTrans _ _ _ hk hk2)
  · exfalso
    rw [hi2, hj2] at hk
    exact kltIrrefl b2 hk

include hb2wf hrr hmem0 hbordmem hbordlt hdmem hdord in
theorem doneFullNklt (i j : Nat) (x y : Gev) :
    (doneFull b2 doneB)[i]? = some x → (doneFull b2 doneB)[j]? = some y → i < j →
    ¬ klt TS bnd bord y x := by
  intro hi hj hlt hk
  have := doneFullKlt hb2wf hrr hmem0 hbordmem hbordlt hdmem hdord j i y x hj hi hk
  omega

/-! ### §5.2 What the enumeration exports -/

include hwf hee hb2wf hrr hmem0 hbordmem hbordlt hdmem hdord in
/-- (a) THE `qorder` PREDECESSOR PROPERTY. -/
theorem doneFullPred (n : Nat) (y : Gev) :
    (doneFull b2 doneB)[n]? = some y →
    ∀ x, gdep2 TS x y → gevWf TS x → ∃ i, i < n ∧ (doneFull b2 doneB)[i]? = some x := by
  intro hn x hd hwx
  have hycl := doneFullCl hdmem y (elem_of_list_lookup_2 hn)
  have hxord := clDc hmem0 x y hycl hd hwx
  obtain ⟨i, hi⟩ := elem_of_list_lookup.1 ((hdmem x).2 hxord)
  have hifull : (doneFull b2 doneB)[i]? = some x := by
    unfold doneFull
    rw [lookup_app_l (lookup_lt_Some hi)]
    exact hi
  exact ⟨i, doneFullKlt hb2wf hrr hmem0 hbordmem hbordlt hdmem hdord i n x y hifull hn
    (gdep2Klt hwf hee hbordmem hbordlt x y (ord0Cl b2 ord0 x hxord) hycl hd), hifull⟩

include hb2wf hrr hmem0 hbordmem hbordlt hdmem hdord in
/-- (b) BLOCK CONTIGUITY: between two events of one block there is nothing else. -/
theorem doneFullContig (i j k : Nat) (x y z : Gev) :
    i < j → j < k →
    (doneFull b2 doneB)[i]? = some x → (doneFull b2 doneB)[j]? = some y →
    (doneFull b2 doneB)[k]? = some z →
    bid TS bnd x = bid TS bnd z → bid TS bnd y = bid TS bnd x := by
  intro hij hjk hi hj hk hxz
  have hxcl := doneFullCl hdmem x (elem_of_list_lookup_2 hi)
  have hycl := doneFullCl hdmem y (elem_of_list_lookup_2 hj)
  have h1 := doneFullNklt hb2wf hrr hmem0 hbordmem hbordlt hdmem hdord i j x y hi hj hij
  have h2 := doneFullNklt hb2wf hrr hmem0 hbordmem hbordlt hdmem hdord j k y z hj hk hjk
  have hle1 : WeakRobustCone.bpos bord (bid TS bnd x) ≤ WeakRobustCone.bpos bord (bid TS bnd y) := by
    rcases kltTotal (TS := TS) (bnd := bnd) (bord := bord) x y with ha | ha | ⟨ha, -⟩
    · unfold klt at ha; omega
    · exact absurd ha h1
    · omega
  have hle2 : WeakRobustCone.bpos bord (bid TS bnd y) ≤ WeakRobustCone.bpos bord (bid TS bnd z) := by
    rcases kltTotal (TS := TS) (bnd := bnd) (bord := bord) y z with hm | hm | ⟨hm, -⟩
    · unfold klt at hm; omega
    · exact absurd hm h2
    · omega
  have heq : WeakRobustCone.bpos bord (bid TS bnd y) = WeakRobustCone.bpos bord (bid TS bnd x) := by
    rw [hxz] at hle1 ⊢
    omega
  exact bposInj hbordmem y x hycl hxcl heq

include hb2wf hrr hmem0 hbordmem hbordlt hdnd hdmem hdord in
/-- (c) IN-BLOCK ORDER IS TRACE ORDER. -/
theorem doneFullInblk (i j : Nat) (x y : Gev) :
    i < j → (doneFull b2 doneB)[i]? = some x → (doneFull b2 doneB)[j]? = some y →
    bid TS bnd x = bid TS bnd y → x.2 < y.2 := by
  intro hij hi hj hbid
  have h1 := doneFullNklt hb2wf hrr hmem0 hbordmem hbordlt hdmem hdord i j x y hi hj hij
  have hne : x ≠ y := by
    intro h
    rw [h] at hi
    have := NoDup_lookup (doneFullNodup hrr hmem0 hdnd hdmem) hi hj
    omega
  have hag : x.1 = y.1 := bidEqFst hbid
  rcases Nat.lt_trichotomy x.2 y.2 with h | h | h
  · exact h
  · exact absurd (Prod.ext hag h) hne
  · exact (h1 (Or.inr ⟨by rw [hbid], h⟩)).elim

include hb2wf hrr hmem0 hbordmem hbordlt hdmem hdord in
/-- (d) THE READER'S BLOCK IS LAST. -/
theorem doneFullReaderLast (i j : Nat) (x y : Gev) :
    (doneFull b2 doneB)[i]? = some x → (doneFull b2 doneB)[j]? = some y →
    bid TS bnd y = bid TS bnd b2 → bid TS bnd x ≠ bid TS bnd b2 → i < j := by
  intro hi hj hby hbx
  have hxcl := doneFullCl hdmem x (elem_of_list_lookup_2 hi)
  refine doneFullKlt hb2wf hrr hmem0 hbordmem hbordlt hdmem hdord i j x y hi hj (Or.inl ?_)
  rw [hby]
  exact bposB2Max hbordmem hbordlt x hxcl hbx

/-! ## §6 DRIVING THE INVARIANT, AND THE RUN'S SEGMENT STRUCTURE -/

include hwf hwsi hco hwfl hlf hobl hcls hclsobl himg hdata hdf hps0 hee hfetch hb2wf hrr hmem0
  hbordmem hbordlt hdnd hdmem hdord in
theorem QinvPrefix (n : Nat) :
    n ≤ (doneFull b2 doneB).length →
    Qinv pstep pcls TS ⟨d0, []⟩ img d0 ps ((doneFull b2 doneB).take n) := by
  induction n with
  | zero =>
    intro _
    rw [take_0]
    exact QinvNil pstep pcls TS ⟨d0, []⟩ img d0 ps hwf hps0 rfl
  | succ n ih =>
    intro hn
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.1
      (lookup_lt_is_Some_2 (l := doneFull b2 doneB) (i := n) (by omega))
    rw [take_S_r he]
    have hwfe := clWf hb2wf hmem0 e (doneFullCl hdmem e (elem_of_list_lookup_2 he))
    refine QinvStep pstep pcls TS ⟨d0, []⟩ img d0 ps hwf hwsi hco hwfl hlf hobl hcls hclsobl himg
      hdata (ptracesWitNil TS d0 hdf) hfetch _ e (ih (by omega)) hwfe ?_ ?_
    · intro hin
      obtain ⟨i, hi, hilt⟩ := elem_of_take.1 hin
      have := NoDup_lookup (doneFullNodup hrr hmem0 hdnd hdmem) hi he
      omega
    · intro e' hd hw'
      obtain ⟨i, hi, hlk⟩ := doneFullPred hwf hee hb2wf hrr hmem0 hbordmem hbordlt hdmem hdord
        n e he e' (gdep3NilGdep2 TS d0 e' e hd) hw'
      exact elem_of_take.2 ⟨i, hlk, hi⟩

include hwf hwsi hco hwfl hlf hobl hcls hclsobl himg hdata hdf hps0 hee hfetch hb2wf hrr hmem0
  hbordmem hbordlt hdnd hdmem hdord d0 in
theorem qorderPrefix (n : Nat) :
    n ≤ (doneFull b2 doneB).length → qorder TS ((doneFull b2 doneB).take n) :=
  fun hn => QinvOrder pstep pcls TS ⟨d0, []⟩ img d0 ps _
    (QinvPrefix hwf hwsi hco hwfl hlf hobl hcls hclsobl himg hdata hdf hps0 hee hfetch hb2wf hrr
      hmem0 hbordmem hbordlt hdnd hdmem hdord n hn)

include hwf hwsi hco hwfl hlf hobl hcls hclsobl himg hdata hdf hps0 hee hfetch hb2wf hrr hmem0
  hbordmem hbordlt hdnd hdmem hdord d0 in
theorem qorderDoneFull : qorder TS (doneFull b2 doneB) := by
  have := qorderPrefix (pcls := pcls) (img := img) (d0 := d0) (ps := ps) hwf hwsi hco hwfl hlf
    hobl hcls hclsobl himg hdata hdf hps0 hee hfetch hb2wf hrr hmem0 hbordmem hbordlt hdnd hdmem
    hdord _ (Nat.le_refl _)
  rwa [take_ge (Nat.le_refl _)] at this

include hwf hwsi hco hwfl hlf hobl hcls hclsobl himg hdata hdf hps0 hee hfetch hb2wf hrr hmem0
  hbordmem hbordlt hdnd hdmem hdord d0 in
theorem qorderDoneB : qorder TS doneB := by
  have hle : doneB.length ≤ (doneFull b2 doneB).length := by
    rw [doneFullLen]; exact Nat.le_succ _
  have := qorderPrefix (pcls := pcls) (img := img) (d0 := d0) (ps := ps) hwf hwsi hco hwfl hlf
    hobl hcls hclsobl himg hdata hdf hps0 hee hfetch hb2wf hrr hmem0 hbordmem hbordlt hdnd hdmem
    hdord _ hle
  unfold doneFull at this
  rwa [take_app_length] at this

include hwf hps0 in
theorem qcfgNil : qcfg pstep pcls TS ⟨d0, []⟩ img d0 ps [] (wpInit img d0 ps) := by
  refine ⟨rtc_refl _, rfl, rfl, by simp [wpInit], ?_, qfabInit TS ⟨d0, []⟩ d0 rfl⟩
  intro j T hT
  obtain ⟨ag0, hag0⟩ := Option.isSome_iff_exists.1 (atraceFirstIsSome pstep _ _ _ _ (hwf j T hT))
  refine ⟨ag0, hag0, ?_⟩
  simp [wpInit, hps0 j T ag0 hT hag0, nprocNil, aevsPost]

theorem WeakRobustCone.cstepOfStep (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    wpPfStep pstep pcls i l c c' → cstep pstep pcls i c c' :=
  Weak.cstepOfStep pstep pcls i l c c'

include hwf hwsi hco hwfl hlf hobl hcls hclsobl himg hnag hdata hdf hps0 hee hfetch hb2wf hrr
  hmem0 hbordmem hbordlt hdnd hdmem hdord in
/-- THE CHAIN. -/
theorem pfChainBuild (n : Nat) :
    n ≤ (doneFull b2 doneB).length →
    ∃ cfs : List (Wpcfg P D), cfs.length = n + 1 ∧
      cfs[0]? = some (wpInit img d0 ps) ∧
      (∀ (i : Nat) (e : Gev) (c c' : Wpcfg P D), (doneFull b2 doneB)[i]? = some e →
         cfs[i]? = some c → cfs[i + 1]? = some c' → cstep pstep pcls e.1 c c') ∧
      (∀ (i : Nat) (c : Wpcfg P D), cfs[i]? = some c →
         qcfg pstep pcls TS ⟨d0, []⟩ img d0 ps ((doneFull b2 doneB).take i) c) := by
  induction n with
  | zero =>
    intro _
    refine ⟨[wpInit img d0 ps], rfl, rfl, ?_, ?_⟩
    · intro i e c c' _ _ hc'
      have := lookup_lt_Some hc'
      simp only [List.length_singleton] at this
      omega
    · intro i c hc
      have hlt := lookup_lt_Some hc
      simp only [List.length_singleton] at hlt
      have hi0 : i = 0 := by omega
      subst hi0
      have hc' : some (wpInit img d0 ps) = some c := hc
      cases hc'
      rw [take_0]
      exact qcfgNil hwf hps0
  | succ n ih =>
    intro hn
    obtain ⟨cfs, hlen, h0, hstep, hq⟩ := ih (by omega)
    obtain ⟨cn, hcn⟩ := Option.isSome_iff_exists.1
      (lookup_lt_is_Some_2 (l := cfs) (i := n) (by omega))
    have hqn := hq n cn hcn
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.1
      (lookup_lt_is_Some_2 (l := doneFull b2 doneB) (i := n) (by omega))
    have hwfe := clWf hb2wf hmem0 e (doneFullCl hdmem e (elem_of_list_lookup_2 he))
    have hqo := qorderPrefix (pcls := pcls) (img := img) (d0 := d0) (ps := ps) hwf hwsi hco hwfl
      hlf hobl hcls hclsobl himg hdata hdf hps0 hee hfetch hb2wf hrr hmem0 hbordmem hbordlt hdnd
      hdmem hdord n (by omega)
    have hnin : e ∉ (doneFull b2 doneB).take n := by
      intro hin
      obtain ⟨i, hi, hilt⟩ := elem_of_take.1 hin
      have := NoDup_lookup (doneFullNodup hrr hmem0 hdnd hdmem) hi he
      omega
    have hpre : ∀ e', gdep2 TS e' e → gevWf TS e' → e' ∈ (doneFull b2 doneB).take n := by
      intro e' hd hw
      obtain ⟨i, hi, hlk⟩ := doneFullPred hwf hee hb2wf hrr hmem0 hbordmem hbordlt hdmem hdord
        n e he e' hd hw
      exact elem_of_take.2 ⟨i, hlk, hi⟩
    obtain ⟨lb, cf', hstp, hqcf⟩ := QcfgStep pstep pcls TS img d0 ps hwf hwsi hco hwfl hlf hobl
      hcls hclsobl himg hnag hdata hdf hfetch _ e cn hqo hqn hwfe hnin hpre
    refine ⟨cfs ++ [cf'], by simp [hlen], by rw [lookup_app_l (show 0 < cfs.length by omega)]; exact h0, ?_, ?_⟩
    · intro i e0 c c' he0 hc hc'
      rcases Nat.lt_or_ge (i + 1) cfs.length with hlt | hge
      · rw [lookup_app_l (show i < cfs.length by omega)] at hc
        rw [lookup_app_l hlt] at hc'
        exact hstep i e0 c c' he0 hc hc'
      · have hlt' := lookup_lt_Some hc'
        simp only [List.length_append, List.length_singleton] at hlt'
        have hin : i = n := by omega
        rw [hin] at hc hc' he0
        rw [lookup_app_l (show n < cfs.length by omega), hcn] at hc
        have hcc : cn = c := Option.some.inj hc
        subst hcc
        rw [lookup_app_r (show cfs.length ≤ n + 1 by omega), hlen, Nat.sub_self] at hc'
        have hcc' : some cf' = some c' := hc'
        have hcc'' : cf' = c' := Option.some.inj hcc'
        subst hcc''
        rw [he] at he0
        have hee0 : e = e0 := Option.some.inj he0
        subst hee0
        exact WeakRobustCone.cstepOfStep _ _ _ _ hstp
    · intro i c hc
      rcases Nat.lt_or_ge i cfs.length with hlt | hge
      · rw [lookup_app_l hlt] at hc
        exact hq i c hc
      · have hlt' := lookup_lt_Some hc
        simp only [List.length_append, List.length_singleton] at hlt'
        have hi : i = n + 1 := by omega
        subst hi
        rw [lookup_app_r (show cfs.length ≤ n + 1 by omega), hlen, Nat.sub_self] at hc
        have hcc : some cf' = some c := hc
        have hcc' : cf' = c := Option.some.inj hcc
        subst hcc'
        rw [take_S_r he]
        exact hqcf

/-! ## §7 THE VIOLATION AT THE BLOCK-CONTIGUOUS ORDER -/

include hwf hwsi hco hwfl hlf hobl hcls hclsobl himg hnag hdata hdf hps0 hee hfetch hb2wf hrr
  hmem0 hbordmem hbordlt hdnd hdmem hdord in
theorem blocksViolates (nh : Nat) (b1 : Gev) :
    bad nh TS ⟨d0, []⟩ b1 b2 →
    ∃ (cfs : List (Wpcfg P D)) (cf : Wpcfg P D),
      -- the run, with its per-event segment structure
      cfs.length = (doneFull b2 doneB).length + 1 ∧
      cfs[0]? = some (wpInit img d0 ps) ∧
      cfs[(doneFull b2 doneB).length]? = some cf ∧
      (∀ (i : Nat) (e : Gev) (c c' : Wpcfg P D), (doneFull b2 doneB)[i]? = some e →
         cfs[i]? = some c → cfs[i + 1]? = some c' → cstep pstep pcls e.1 c c') ∧
      (∀ (i : Nat) (c : Wpcfg P D), cfs[i]? = some c →
         qcfg pstep pcls TS ⟨d0, []⟩ img d0 ps ((doneFull b2 doneB).take i) c) ∧
      rtc (wpPfRun pstep pcls) (wpInit img d0 ps) cf ∧
      -- the violation, in both the named and the hart-restricted form
      (∃ p m a, violatesAt cf p m b1.1 b2.1 a) ∧
      violationHart clsOf pubOf nh cf := by
  intro hbad
  have hbad' := hbad
  obtain ⟨hrf, hne, hh1, hh2, ⟨t, m, hts1, hlogm, hak⟩, hnopub⟩ := hbad'
  obtain ⟨t', a, hts1', hrd2⟩ := hrf
  rw [hts1] at hts1'
  cases hts1'
  have hb1wf := gevTsWf TS b1 t hts1
  have htpos := gevTsPos pstep TS b1 t hwf hts1
  -- the run
  obtain ⟨cfs, hlen, h0, hstepc, hqc⟩ := pfChainBuild hwf hwsi hco hwfl hlf hobl hcls hclsobl
    himg hnag hdata hdf hps0 hee hfetch hb2wf hrr hmem0 hbordmem hbordlt hdnd hdmem hdord
    (doneFull b2 doneB).length (Nat.le_refl _)
  obtain ⟨cf, hcf⟩ := Option.isSome_iff_exists.1
    (lookup_lt_is_Some_2 (l := cfs) (i := (doneFull b2 doneB).length) (by omega))
  have hqcf : qcfg pstep pcls TS ⟨d0, []⟩ img d0 ps (doneFull b2 doneB) cf := by
    have := hqc _ cf hcf
    rwa [take_ge (Nat.le_refl _)] at this
  obtain ⟨hrun, -, hclog, -, hcags, -⟩ := hqcf
  -- the bad message and its pf position
  have hq' : qorder TS (doneFull b2 doneB) :=
    qorderDoneFull (pcls := pcls) (img := img) (d0 := d0) (ps := ps) hwf hwsi hco hwfl hlf hobl
      hcls hclsobl himg hdata hdf hps0 hee hfetch hb2wf hrr hmem0 hbordmem hbordlt hdnd hdmem hdord
  have hb2nin : b2 ∉ doneB := fun hin => b2Nin hrr hmem0 ((hdmem b2).1 hin)
  have hpre2 : ∀ e', gdep2 TS e' b2 → gevWf TS e' → e' ∈ doneB :=
    fun e' hd hw' => (hdmem e').2 (b2Pre hmem0 e' hd hw')
  have hb1ord : b1 ∈ ord0 :=
    (hmem0 b1).2 ⟨hb1wf, tc_once (grfGdep2 TS b1 b2 ⟨t, a, hts1, hrd2⟩)⟩
  have hb1in' : b1 ∈ doneFull b2 doneB := List.mem_append_left _ ((hdmem b1).2 hb1ord)
  have htfl : t ∈ fl TS (doneFull b2 doneB) := (elemOfFl TS _ t).2 ⟨b1, hb1in', hts1⟩
  obtain ⟨hp1, -, hp3⟩ := pfLogPi pstep TS hwf (doneFull b2 doneB) t hq' htfl
  have hmsgeq : msgAt TS t = m := msgAtEq TS t m hlogm
  obtain ⟨base0, data0, kc, hm0⟩ := gevTsMsg pstep TS b1 t hwf hts1
  have hmeq : m = ⟨base0, data0, some b1.1, kc⟩ := by
    rw [hlogm] at hm0; exact Option.some.inj hm0
  have htid : m.wmTid = some b1.1 := by rw [hmeq]
  -- the reader's event and the byte it read
  obtain ⟨T2, hT2, -⟩ := (gevWfBounds TS b2).1 hb2wf
  obtain ⟨ev2, hev2, hinrd⟩ := gevReadsEv TS b2 a t T2 hT2 hrd2
  have hatr2 := hwf b2.1 T2 hT2
  obtain ⟨ag2, -, -, f2, -, -, -, hok2, -⟩ :=
    astepsWfStep pstep TS.ptImg TS.ptLog b2.1 T2.atAgs T2.atEvs b2.2 ev2 hatr2 hev2
  have hshape : ∃ (base : Int) (tvs : List (Nat × BitVec 8)) (jb : Nat) (v : BitVec 8),
      a = base + (jb : Int) ∧ tvs[jb]? = some (t, v) ∧
      ((∃ aq lat asrc, ev2.aeLb = LLoad aq lat base tvs asrc) ∨
       (∃ aq rl data asrc vsrc ts,
          ev2.aeLb = LRmw aq rl base tvs data asrc vsrc ∧ ev2.aeTs = some ts) ∨
       -- THE RMW SPLIT (S2): the exclusive read is a third reading shape
       (∃ aq asrc, ev2.aeLb = LExLoad aq base tvs asrc)) := by
    obtain ⟨lb2, ots2, dv2⟩ := ev2
    cases lb2 with
    | LLoad aq lat base tvs asrc =>
      obtain ⟨jb, v, htv, rfl⟩ := (memTvsReads base tvs a t).1 hinrd
      exact ⟨base, tvs, jb, v, rfl, htv, Or.inl ⟨aq, lat, asrc, rfl⟩⟩
    | LRmw aq rl base tvs data asrc vsrc =>
      obtain ⟨jb, v, htv, rfl⟩ := (memTvsReads base tvs a t).1 hinrd
      obtain ⟨ts2, k2, _, _, _, _, _, _, _, hts2⟩ := hok2
      exact ⟨base, tvs, jb, v, rfl, htv, Or.inr (Or.inl ⟨aq, rl, data, asrc, vsrc, ts2, rfl, hts2⟩)⟩
    | LExLoad aq base tvs asrc =>
      obtain ⟨jb, v, htv, rfl⟩ := (memTvsReads base tvs a t).1 hinrd
      exact ⟨base, tvs, jb, v, rfl, htv, Or.inr (Or.inr ⟨aq, asrc, rfl⟩)⟩
    | LSilent => simp [lbReads] at hinrd
    | LStore => simp [lbReads] at hinrd
    | LFence => simp [lbReads] at hinrd
    | LDev => simp [lbReads] at hinrd
    | LRegW => simp [lbReads] at hinrd
    | LCtrl => simp [lbReads] at hinrd
    | LInstr => simp [lbReads] at hinrd
    | LExStore => simp [lbReads] at hinrd
    | LIFetch => simp [lbReads] at hinrd
  obtain ⟨base, tvs, jb, v, ha, htv, hlbsh⟩ := hshape
  have hlbv : logByte TS.ptImg TS.ptLog t (base + (jb : Int)) = some v := by
    refine astepReadLogByte TS.ptImg TS.ptLog b2.1 ag2 ev2.aeLb f2 ev2.aeTs base tvs jb t v
      hok2 ?_ htv
    rcases hlbsh with ⟨aq, lat, asrc, hl⟩ | ⟨aq, rl, data, asrc, vsrc, _, hl, _⟩ | ⟨aq, asrc, hl⟩
    · exact Or.inl ⟨aq, lat, asrc, hl⟩
    · exact Or.inr (Or.inl ⟨aq, rl, data, asrc, vsrc, hl⟩)
    · exact Or.inr (Or.inr ⟨aq, asrc, hl⟩)
  have hbyte : (msgByte m (base + (jb : Int))).isSome := by
    rw [logBytePos TS.ptImg TS.ptLog t m _ htpos hlogm] at hlbv
    rw [hlbv]; rfl
  -- the reader's coherence floor
  have hnproc2 : nproc (doneFull b2 doneB) b2.1 = b2.2 + 1 := by
    unfold doneFull
    rw [nprocAppEq doneB b2,
      nprocCur TS doneB b2
        (qorderDoneB (pcls := pcls) (img := img) (d0 := d0) (ps := ps) hwf hwsi hco hwfl hlf hobl
          hcls hclsobl himg hdata hdf hps0 hee hfetch hb2wf hrr hmem0 hbordmem hbordlt hdnd hdmem
          hdord)
        hb2wf hb2nin hpre2]
  obtain ⟨agn2, -, hlk2⟩ := hcags b2.1 T2 hT2
  rw [hnproc2, take_S_r hev2, aevsPostApp] at hlk2
  have hcoh : pi TS (doneFull b2 doneB) t ≤
      coh (aevPost (pi TS (doneFull b2 doneB)) ev2
        (aevsPost (pi TS (doneFull b2 doneB)) (T2.atEvs.take b2.2) wsInit))
        (base + (jb : Int)) :=
    aevPostCohRead _ ev2 _ base tvs jb t v htv hlbsh
  -- the violating configuration
  have hviol : violatesAt cf (pi TS (doneFull b2 doneB) t - 1) m b1.1 b2.1 (base + (jb : Int)) := by
    refine ⟨?_, htid, ?_, ?_, fun h => hne h.symm, hbyte, ?_⟩
    · rw [hclog, hp3, hmsgeq]
    · simp only [clsOf, hak]
    · -- NOT PUBLISHED
      rintro ⟨p', m', heq, hlogp, hpub⟩
      have hp' : p' = pi TS (doneFull b2 doneB) t - 1 := by omega
      subst hp'
      rw [hclog, hp3, hmsgeq] at hlogp
      cases hlogp
      rw [htid] at hpub
      obtain ⟨q, mq, hle, hq0', htidq, hrelq⟩ := hpub
      rw [hclog, WeakRobustSim.pfLog, list_lookup_fmap] at hq0'
      cases hfl0 : (fl TS (doneFull b2 doneB))[q]? with
      | none => rw [hfl0] at hq0'; cases hq0'
      | some t0 =>
        rw [hfl0] at hq0'
        simp only [Option.map_some, Option.some.injEq] at hq0'
        subst hq0'
        have ht0in : t0 ∈ fl TS (doneFull b2 doneB) := elem_of_list_lookup.2 ⟨q, hfl0⟩
        obtain ⟨ep, hepin, hepts, heplog, heptid⟩ := flMsg pstep TS hwf _ t0 hq' ht0in
        have hepag : ep.1 = b1.1 := by
          rw [heptid] at htidq; exact Option.some.inj htidq
        have hpiq : pi TS (doneFull b2 doneB) t0 = q + 1 := piMem pstep TS hwf _ q t0 hq' hfl0
        have hepge : b1.2 ≤ ep.2 := by
          rcases Nat.lt_or_ge ep.2 b1.2 with hlt | hge
          · exfalso
            have htcb1 : tc (gdep2 TS) ep b1 :=
              tc_once (gpoGdep2 TS ep b1 ⟨hepag, hlt, gevTsWf TS ep t0 hepts, hb1wf⟩)
            have := piLtOfTc pstep TS hwf _ ep b1 t0 t hq' hb1in' htcb1 hepts hts1
            omega
          · exact hge
        have hepord : ep ∈ ord0 := by
          rcases List.mem_append.1 hepin with h | h
          · exact (hdmem ep).1 h
          · exfalso
            rw [List.mem_singleton] at h
            apply hne
            rw [← hepag, h]
        exact hnopub ⟨ep, hepag, hepge, ⟨t0, msgAt TS t0, hepts, heplog, hrelq⟩,
          tcGdep2Gdep3 TS _ ep b2 (ord0Tc hmem0 ep hepord)⟩
    · simp only [obsFlr, hlk2]
      omega
  refine ⟨cfs, cf, hlen, h0, hcf, hstepc, hqc, hrun,
    ⟨_, m, _, hviol⟩, ?_⟩
  obtain ⟨hl, ht, hc, hpb, hn, hb, ho⟩ := hviol
  exact ⟨_, m, b1.1, b2.1, _, hl, ht, ⟨b1.1, ht, hh1⟩, hc, hpb, hn, ⟨b2.1, rfl, hh2⟩, hb, ho⟩

end coneblocks

/-! ## §8 THE PACKAGED THEOREM -/

/-- `WeakRobustMain.badEdgeViolates`, re-derived over a BLOCK-CONTIGUOUS order and
with the run's segment structure exported.  (O2: `hfetch`, deviation 4.) -/
theorem badEdgeViolatesBlocks {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass)
    (TS : Ptraces P D) (img : Image) (d0 : D) (ps : List P)
    (hwf : ptracesWf pstep TS) (hwsi : ptracesWsInit TS) (hco : ∀ a, coTc TS a)
    (hwfl : writesFulfilled TS) (hlf : latFreeProg pstep) (hobl : tsOblivious pstep)
    (hcls : clsCanonical pcls TS) (hclsobl : pclsObl pcls) (himg : TS.ptImg = img)
    (hnag : TS.ptTrs.length = ps.length)
    (hdata : ∀ (p : Nat) (m : Wmsg), TS.ptLog[p]? = some m → m.wmData ≠ [])
    (hdf : ∀ (j : Nat) (T : Atrace P D) (k : Nat) (ev : Aev D), TS.ptTrs[j]? = some T →
      T.atEvs[k]? = some ev → ev.aeDev = none)
    (hps0 : ∀ (j : Nat) (T : Atrace P D) (ag0 : Wpagent P), TS.ptTrs[j]? = some T →
      T.atAgs[0]? = some ag0 → ps[j]? = some ag0.paSt)
    (hfo : ptracesFwdOwn TS) (hee : eeOk TS) (nh : Nat)
    (hsplit : edgesSplitCyc nh TS ⟨d0, []⟩)
    (bnd : P → Prop) [DecidablePred bnd]
    (hcsl : ∀ e1 e2, gdep2 TS e1 e2 → e1.1 ≠ e2.1 →
      ∀ (T : Atrace P D), TS.ptTrs[e1.1]? = some T →
      ∀ (k' : Nat) (ev' : Aev D), e1.2 < k' → T.atEvs[k']? = some ev' →
      (∀ (k'' : Nat) (ag'' : Wpagent P), e1.2 < k'' → k'' ≤ k' →
         T.atAgs[k'']? = some ag'' → ¬ bnd ag''.paSt) →
      lbWrites ev'.aeLb = false ∧ lbLoads ev'.aeLb = false)
    (hfetch : fetchSrcOk TS) (b1 b2 : Gev) :
    bad nh TS ⟨d0, []⟩ b1 b2 → badMin nh TS ⟨d0, []⟩ b2 →
    ∃ (order : List Gev) (cfs : List (Wpcfg P D)) (cf : Wpcfg P D),
      -- (a) THE ORDER: the cone plus the bad read, duplicate-free, with the bad read
      -- LAST and every `gdep2` predecessor strictly earlier
      (∀ e, e ∈ order ↔ (gevWf TS e ∧ (e = b2 ∨ tc (gdep2 TS) e b2))) ∧
      order.Nodup ∧
      order[order.length - 1]? = some b2 ∧
      (∀ (n : Nat) (y : Gev), order[n]? = some y → ∀ x, gdep2 TS x y → gevWf TS x →
         ∃ i, i < n ∧ order[i]? = some x) ∧
      -- (b) BLOCK STRUCTURE
      (∀ (i j k : Nat) (x y z : Gev), i < j → j < k →
         order[i]? = some x → order[j]? = some y → order[k]? = some z →
         bid TS bnd x = bid TS bnd z → bid TS bnd y = bid TS bnd x) ∧
      (∀ (i j : Nat) (x y : Gev), i < j → order[i]? = some x → order[j]? = some y →
         bid TS bnd x = bid TS bnd y → x.2 < y.2) ∧
      (∀ (i j : Nat) (x y : Gev), order[i]? = some x → order[j]? = some y →
         bid TS bnd y = bid TS bnd b2 → bid TS bnd x ≠ bid TS bnd b2 → i < j) ∧
      -- (c) THE RUN
      cfs.length = order.length + 1 ∧
      cfs[0]? = some (wpInit img d0 ps) ∧
      cfs[order.length]? = some cf ∧
      (∀ (i : Nat) (e : Gev) (c c' : Wpcfg P D), order[i]? = some e → cfs[i]? = some c →
         cfs[i + 1]? = some c' → cstep pstep pcls e.1 c c') ∧
      (∀ (i : Nat) (c : Wpcfg P D), cfs[i]? = some c →
         qcfg pstep pcls TS ⟨d0, []⟩ img d0 ps (order.take i) c) ∧
      rtc (wpPfRun pstep pcls) (wpInit img d0 ps) cf ∧
      -- (d) THE VIOLATION, in both forms
      (∃ p m a, violatesAt cf p m b1.1 b2.1 a) ∧
      violationHart clsOf pubOf nh cf := by
  intro hbad hmin
  have hbad2 := hbad
  obtain ⟨hrf, -, -, -, -, -⟩ := hbad2
  have hrf2 := hrf
  obtain ⟨t0, a0, -, hrd0⟩ := hrf2
  have hb2wf : gevWf TS b2 := gevReadsWf TS b2 a0 t0 hrd0
  have hb2mem : WeakRobustCone.isMem TS b2 := readsMem b2 a0 t0 hrd0
  have hrr : ¬ tc (gdep2 TS) b2 b2 := fun hc => hmin b1 b2 hbad (tcGdep2Gdep3 TS _ b2 b2 hc)
  obtain ⟨ord0, hq0, hmem0⟩ :=
    coneQinvNil pstep pcls TS img d0 ps hwf hwsi hco hwfl hlf hobl hcls hclsobl himg hnag hdata
      hps0 hdf hfetch b2 hb2wf hrr
      (coneAcycOfMinNil pstep TS d0 nh b2 hwf hfo hee hdf hsplit hmin)
  obtain ⟨bord, -, hbordmem, hbordlt⟩ :=
    topoSort (Rblk' TS bnd b2 ord0) (bids TS bnd b2 ord0)
      (Rblk'Acyc hwf hee hcsl hb2wf hrr hb2mem hq0 hmem0) (bidsNodup TS bnd b2 ord0)
  obtain ⟨doneB, hdnd, hdmem, hdord⟩ :=
    topoSort (Rev TS bnd ord0 bord) ord0 (RevAcyc (TS := TS) (bnd := bnd) (ord0 := ord0) (bord := bord))
      (ord0Nodup hq0)
  obtain ⟨cfs, cf, hlenc, hc0, hcf, hstepc, hqc, hrun, hv1, hv2⟩ :=
    blocksViolates hwf hwsi hco hwfl hlf hobl hcls hclsobl himg hnag hdata hdf hps0 hee hfetch hb2wf
      hrr hmem0 hbordmem hbordlt hdnd hdmem hdord nh b1 hbad
  refine ⟨doneFull b2 doneB, cfs, cf, ?_, doneFullNodup hrr hmem0 hdnd hdmem, ?_,
    doneFullPred hwf hee hb2wf hrr hmem0 hbordmem hbordlt hdmem hdord,
    doneFullContig hb2wf hrr hmem0 hbordmem hbordlt hdmem hdord,
    doneFullInblk hb2wf hrr hmem0 hbordmem hbordlt hdnd hdmem hdord,
    doneFullReaderLast hb2wf hrr hmem0 hbordmem hbordlt hdmem hdord,
    hlenc, hc0, hcf, hstepc, hqc, hrun, hv1, hv2⟩
  · intro e
    unfold doneFull
    rw [List.mem_append, List.mem_singleton]
    constructor
    · rintro (he | he)
      · obtain ⟨hw, htc⟩ := (hmem0 e).1 ((hdmem e).1 he)
        exact ⟨hw, Or.inr htc⟩
      · rw [he]; exact ⟨hb2wf, Or.inl rfl⟩
    · rintro ⟨hw, heq | htc⟩
      · exact Or.inr heq
      · exact Or.inl ((hdmem e).2 ((hmem0 e).2 ⟨hw, htc⟩))
  · rw [doneFullLen, Nat.add_sub_cancel]
    exact doneFullLast b2 doneB

end Weak
