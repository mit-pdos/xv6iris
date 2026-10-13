/-
Weak: **THE RULE-14 LINEARIZATION (T2-1c): graph → same-log candidate**.

Rocq: `iris/WeakRvwmoLin.v` @ xxvzwolszwmp.

The Rocq header, in substance (design: `claude-notes/design/weak-memory-tier2-s6.md`;
the model is `WeakRvwmoGraph`'s RVWMO⁻ and the target is `WeakAxiomatic3`'s
`srvwmoConsistent`).

THE THEOREM.  An RVWMO⁻-consistent graph that ALSO satisfies rule 14 ("a memory
event po-before a write is gmo-before it", `grule14`) is realized by a
candidate — same image, same per-hart program rows, and THE SAME LOG: the
candidate's final message list is exactly `gwrites G` (the graph's writes in gmo
order) mapped through `gmsg`.  So a graph read's per-byte `ts` entry, which
names a gmo-WRITE-INDEX, is NUMERICALLY the candidate log position of the same
write: the linearization renumbers nothing.

THE CONSTRUCTION (closed form; no topological selection).  For an event `e`,
`gnxw G e` is the po-FIRST write at-or-after `e` in `e`'s own hart.  The trace
enumerates, for each write `w` of `gwrites G` (in gmo order) `w`'s SEGMENT (the
events whose `gnxw` is `w`, in po order), then hart by hart the TAILS (the
events with no write at-or-after them).  Both are read off one RANK function,
`grank`: `gwix` of the next write, or `|gwrites| + 1 + hart` when there is
none.  The trace is `rblocks (grank G) (gevs G)` — the events grouped by rank,
groups in rank order, each group in the source list's order.

WHY IT WORKS: (P1) per-hart po order (`linProg`, `glinPoLt`); (P2) writes land at
their `gwix` (`linTsWrite`); (P3) rf is gmo-FORWARD (`WeakRvwmoLin.grfGmo`), so a
read's source is already in the prefix log (`linSourceBefore`); (P4) po and rf
both increase the trace index; (P5) fr is `gpos`-forward (`gfrGe`).

THE OBLIGATIONS.  Only SIX are proved here: `candShape`, `candValues`,
`axCoherence`, `axAtomicity`, `axOrd`, `axRelOrd`; `ob`-acyclicity comes from
`promiseFreeObAcyclic` once `promiseFreeCompleteLocal` has turned the six into
`execWf`.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  Duplicated Rocq
   names (protocol rule) are FILE-QUALIFIED: `WeakRvwmoLin.grank`,
   `WeakRvwmoLin.grow`, `WeakRvwmoLin.growLookup`, `WeakRvwmoLin.gmsg`,
   `WeakRvwmoLin.gmsgByte`, `WeakRvwmoLin.filterAll`, `WeakRvwmoLin.gisWGmem`,
   `WeakRvwmoLin.gisWGlblIs`, `WeakRvwmoLin.grfGmo`,
   `WeakRvwmoLin.gwritesByteIsW`, `WeakRvwmoLin.gwritesByteLbl`.
2. VOCABULARY: as `WeakRvwmoGraph` deviation 2; `mjoin (f <$> l)` ↦
   `(l.map f).flatten`, `omap f l` ↦ `l.filterMap f`, `default d o` ↦
   `o.getD d`, `filter (λ x, rk x = d)` ↦ `filter (fun x => decide (rk x = d))`,
   `filter (gis_w G)` ↦ `filter (gisW G)` (Boolean already), `≡ₚ` ↦
   `List.Perm`.  `gnxw`'s `list_find (λ k, gis_w G (e.1, k) = true)` is
   `listFind (fun k => gisW G (e.1, k))` (the Boolean itself).
3. SECTION `lin`: the Rocq section variables (`Hwf`, `Hppo`, `Hlv`, `Hat`,
   `H14`) become explicit hypotheses, and — as Rocq's section closing does —
   each lemma takes exactly the ones its proof uses, in section order, after
   `G`.  The section-local `Hnd` is `linNd` (takes `hwf`).
4. `StronglySorted_app_2` (Rocq stdlib) is `List.pairwise_append`, inline.
5. `pidx`, `filterSortedPidx`, `filterUnique` take `[DecidableEq A]` /
   a Boolean predicate (stdpp's `EqDecision` / `Decision`).

**Name map** (Rocq → Lean): `pidx`; `pidx_lookup` ↦ `pidxLookup`;
`pidx_of_lookup` ↦ `pidxOfLookup`; `pidx_cons_eq` ↦ `pidxConsEq`; `pidx_cons_ne`
↦ `pidxConsNe`; `StronglySorted_weaken` ↦ `stronglySortedWeaken`;
`filter_sorted_pidx` ↦ `filterSortedPidx`; `filter_no` ↦ `filterNo`;
`filter_unique` ↦ `filterUnique`; `elem_of_mjoin_seq` ↦ `elemOfMjoinSeq`;
`mjoin_seq_S` ↦ `mjoinSeqS`; `mjoin_seq_none` ↦ `mjoinSeqNone`;
`mjoin_seq_single` ↦ `mjoinSeqSingle`; `filter_mjoin_fmap` ↦ `filterMjoinFmap`;
`nodup_mjoin_seq` ↦ `nodupMjoinSeq`; `rblocks`; `rblocks_S` ↦ `rblocksS`;
`elem_of_rblocks` ↦ `elemOfRblocks`; `rblocks_nodup` ↦ `rblocksNodup`;
`rblocks_rank_sorted` ↦ `rblocksRankSorted`; `rblocks_sorted` ↦
`rblocksSorted`; `rblocks_perm` ↦ `rblocksPerm`; `rblocks_id` ↦ `rblocksId`;
`rblocks_ext` ↦ `rblocksExt`; `rblocks_filter` ↦ `rblocksFilter`; `grow` ↦
`WeakRvwmoLin.grow`; `gevs_hart` ↦ `gevsHart`; `gevs`; `gnxw`; `grank` ↦
`WeakRvwmoLin.grank`; `grank_bound` ↦ `grankBound`; `glin_eids` ↦ `glinEids`;
`glbl`; `glin_step` ↦ `glinStep`; `gmsg` ↦ `WeakRvwmoLin.gmsg`; `lin_cand` ↦
`linCand`; `lin_nw` ↦ `linNw`; `grow_lookup` ↦ `WeakRvwmoLin.growLookup`;
`gx_lbl_bounds` ↦ `gxLblBounds`; `glbl_some` ↦ `glblSome`; `elem_of_gevs_hart`
↦ `elemOfGevsHart`; `gevs_hart_lookup` ↦ `gevsHartLookup`;
`gevs_hart_lookup_inv` ↦ `gevsHartLookupInv`; `gevs_hart_nodup` ↦
`gevsHartNodup`; `elem_of_gevs` ↦ `elemOfGevs`; `gevs_nodup` ↦ `gevsNodup`;
`filter_all` ↦ `WeakRvwmoLin.filterAll`; `filter_gevs_hart` ↦ `filterGevsHart`;
`gnxw_Some` ↦ `gnxwSome`; `gnxw_None` ↦ `gnxwNone`; `gnxw_self` ↦ `gnxwSelf`;
`Hnd` ↦ `linNd`; `gis_w_gmem` ↦ `WeakRvwmoLin.gisWGmem`; `gis_w_glbl_is` ↦
`WeakRvwmoLin.gisWGlblIs`; `gwrites_byte_gw` ↦ `gwritesByteGw`;
`gwrites_byte_lbl` ↦ `WeakRvwmoLin.gwritesByteLbl`; `gwrites_byte_isw` ↦
`gwritesByteIsw`; `greads_byte_lbl` ↦ `greadsByteLbl`; `greads_byte_mem` ↦
`greadsByteMem`; `gwrites_gmo` ↦ `gwritesGmo`; `gwrites_lbl` ↦ `gwritesLbl`;
`gwrites_isw` ↦ `gwritesIsw`; `gcomax`; `grf_gmo` ↦ `WeakRvwmoLin.grfGmo`;
`gfr_ge` ↦ `gfrGe`; `gsame_hart_gwix` ↦ `gsameHartGwix`; `grank_write` ↦
`grankWrite`; `grank_lt_bound` ↦ `grankLtBound`; `grank_mono` ↦ `grankMono`;
`glin_nodup` ↦ `glinNodup`; `elem_of_glin` ↦ `elemOfGlin`; `glin_lookup_lbl` ↦
`glinLookupLbl`; `glin_index` ↦ `glinIndex`; `glin_hart` ↦ `glinHart`;
`glin_po_lt` ↦ `glinPoLt`; `glin_po_iff` ↦ `glinPoIff`; `glin_rank_lt` ↦
`glinRankLt`; `glin_writes` ↦ `glinWrites`; `lin_tr_lookup` ↦ `linTrLookup`;
`lin_tr_lookup_inv` ↦ `linTrLookupInv`; `lin_tr_len` ↦ `linTrLen`; `lin_lbl` ↦
`linLbl`; `es_wmsg_glin` ↦ `esWmsgGlin`; `tr_msgs_omap` ↦ `trMsgsOmap`;
`omap_glin` ↦ `omapGlin`; `lin_log_take` ↦ `linLogTake`; `gmsg_is_w` ↦
`gmsgIsW`; `omap_gmsg_len` ↦ `omapGmsgLen`; `lin_log_len` ↦ `linLogLen`;
`filter_take_mono` ↦ `filterTakeMono`; `lin_nw_mono` ↦ `linNwMono`; `lin_nw_S`
↦ `linNwS`; `lin_gwrites_split` ↦ `linGwritesSplit`; `lin_ts_write` ↦
`linTsWrite`; `lin_source_before` ↦ `linSourceBefore`; `lin_read_ts_le` ↦
`linReadTsLe`; `omap_gmsg_filter` ↦ `omapGmsgFilter`; `lin_full_log` ↦
`linFullLog`; `lin_ex_log` ↦ `linExLog`; `lin_ex_img` ↦ `linExImg`;
`omap_lookup_all` ↦ `omapLookupAll`; `lin_log_full_lookup` ↦
`linLogFullLookup`; `gmsg_byte` ↦ `WeakRvwmoLin.gmsgByte`; `gmsg_byte_inv` ↦
`gmsgByteInv`; `lin_log_byte_final` ↦ `linLogByteFinal`;
`lin_log_byte_final_inv` ↦ `linLogByteFinalInv`; `lin_is_W` ↦ `linIsW`;
`lin_wr_b` ↦ `linWrB`; `lin_reads_at` ↦ `linReadsAt`; `lin_rd_b` ↦ `linRdB`;
`lin_acc_b` ↦ `linAccB`; `lin_po_dict` ↦ `linPoDict`; `greads_byte_is_r` ↦
`greadsByteIsR`; `gwrites_byte_is_w` ↦ `WeakRvwmoLin.gwritesByteIsW`;
`lin_src_gmo` ↦ `linSrcGmo`; `gx_lbl_row_lookup` ↦ `gxLblRowLookup`;
`lin_shape` ↦ `linShape`; `lin_values` ↦ `linValues`; `lin_atomicity` ↦
`linAtomicity`; `lin_ets_wr` ↦ `linEtsWr`; `lin_ets_rd` ↦ `linEtsRd`;
`lin_nwr_read` ↦ `linNwrRead`; `lin_poloc_ets` ↦ `linPolocEts`;
`lin_read_ts_le'` ↦ `linReadTsLe'`; `lin_coh_lexlt` ↦ `linCohLexlt`;
`lin_coherence` ↦ `linCoherence`; `lin_fence_between` ↦ `linFenceBetween`;
`lin_acq_po_gmo` ↦ `linAcqPoGmo`; `lin_rel_acq_gmo` ↦ `linRelAcqGmo`;
`lin_fr_bound` ↦ `linFrBound`; `lin_pub_bound` ↦ `linPubBound`;
`lin_ord_core` ↦ `linOrdCore`; `lin_read_at_2` ↦ `linReadAt2`; `lin_ord` ↦
`linOrd`; `lin_rel_ord` ↦ `linRelOrd`; `filter_fmap_glin` ↦ `filterFmapGlin`;
`lin_prog` ↦ `linProg`; `lin_srvwmo` ↦ `linSrvwmo`; `rule14_linearization` ↦
`rule14Linearization`.

**Lean-only helpers** (no Rocq twin): `gevsHartNil` (a hart outside the
program has no events — the `Hnil` assertion both `filter_gevs_hart` and
`glin_hart` prove inline), `linTrEq` (a trace step at a known event index IS
that event's step — the `lin_tr_lookup` + `simplify_eq` idiom).

**W13 (L) — §6, Lean-only (no Rocq twin; plan `notes/weak-allocproc-plan.md` §C W13 (L),
[W2s], G3-Q (a″) [OWN.17]).**  The ANCHORED rank trace: `gnxa` (the po-next anchor of an arbitrary
anchor class `anc`), `gancs` (gmo filtered by `anc`), `gaix` (the anchor index), `grankA`,
`grankBoundA`, `glinEidsA`, `linCandA`, `linNwA`; admissibility `granc14` (anchor-14: a memory
event po-before an anchor is gmo-before it) and `ancOk`.  For `anc = gisW G` the construction IS
§2's, definitionally (`glinEidsAW`, `linCandAW`, `linNwAW`; `ancOkW` from rule 14), so §2–§3 are
its write instance and are left as they were (their statements need `gwf` only where §6's need
`ancOk`).  Lemmas (the §2–§3 twins, file order): `gnxaSome`, `gnxaNone`, `gnxaSelf`,
`gancsElemOf`, `gancsNodup`, `gaixLookup`, `gaixLe`, `gaixInj`, `gancsSorted`, `gaixGposLt`,
`gancsOfAnc`, `ancLbl`, `gsameHartGaix`, `grankAAnc`, `grankALtBound`, `grankAMono`, `glinANodup`,
`elemOfGlinA`, `glinALookupLbl`, `glinAIndex`, `glinAPerm`, `glinAHart`, `glinAPoLt`, `glinAPoIff`,
`glinARankLt`, `glinAWrites`, `linTrALookup`, `linTrALookupInv`, `linTrALen`, `linALbl`,
`linALogTake`, `linALogLen`, `linANwMono`, `linANwS`, `linAGwritesSplit`, `linASourceBefore`,
`linAReadTsLe`, `linAFullLog`; and the two new facts `glinAGmoAnc` (an anchor gmo-before an event
is emitted before it) and `glinAAncIff` (between anchors, trace order IS gmo order).

**Not ported:** nothing.

**Statements checked** (by hand, against Rocq): all of them.
-/
import Weak.WeakAxiomatic3
import Weak.WeakRvwmoGraph

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl Ev

/-! # 1. A GENERIC ORDER-THEORY KIT -/

/-! ## 1.1 `pidx`: the position of an element in a list -/

def pidx {A : Type _} [DecidableEq A] (l : List A) (x : A) : Nat :=
  match listFind (fun y => decide (y = x)) l with
  | some (i, _) => i
  | none => 0

theorem pidxLookup {A : Type _} [DecidableEq A] (l : List A) (x : A) :
    x ∈ l → l[pidx l x]? = some x := by
  intro hx
  unfold pidx
  cases hf : listFind (fun y => decide (y = x)) l with
  | some q =>
    obtain ⟨i, z⟩ := q
    obtain ⟨hi, hz, _⟩ := list_find_Some.1 hf
    have : z = x := of_decide_eq_true hz
    subst this
    exact hi
  | none =>
    have := list_find_None.1 hf x hx
    simp at this

theorem pidxOfLookup {A : Type _} [DecidableEq A] (l : List A) (i : Nat) (x : A) :
    l.Nodup → l[i]? = some x → pidx l x = i := by
  intro hnd hi
  exact NoDup_lookup hnd (pidxLookup l x (elem_of_list_lookup_2 hi)) hi

theorem pidxConsEq {A : Type _} [DecidableEq A] (a : A) (l : List A) :
    pidx (a :: l) a = 0 := by
  simp [pidx, listFind]

theorem pidxConsNe {A : Type _} [DecidableEq A] (a x : A) (l : List A) :
    x ≠ a → x ∈ l → pidx (a :: l) x = pidx l x + 1 := by
  intro hne hx
  have hax : decide (a = x) = false := decide_eq_false (fun h => hne h.symm)
  unfold pidx
  simp only [listFind, hax, Bool.false_eq_true, ↓reduceIte]
  cases hf : listFind (fun y => decide (y = x)) l with
  | some q => obtain ⟨i, z⟩ := q; rfl
  | none =>
    have := list_find_None.1 hf x hx
    simp at this

/-! ## 1.2 Sortedness helpers -/

theorem stronglySortedWeaken {A : Type _} (R1 R2 : A → A → Prop) (l : List A) :
    (∀ x y, x ∈ l → y ∈ l → R1 x y → R2 x y) →
    List.Pairwise R1 l → List.Pairwise R2 l := by
  intro himp hss
  exact hss.imp_of_mem (fun hx hy h => himp _ _ hx hy h)

/-- FILTER PRESERVES RELATIVE ORDER: the filtered list is sorted by position in
the ORIGINAL list. -/
theorem filterSortedPidx {A : Type _} [DecidableEq A] (p : A → Bool) (l : List A) :
    l.Nodup → List.Pairwise (fun x y => pidx l x < pidx l y) (l.filter p) := by
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro hnd
    have ha := NoDup_cons_1_1 hnd
    have hnd' := NoDup_cons_1_2 hnd
    have hsub : ∀ x, x ∈ l.filter p → pidx (a :: l) x = pidx l x + 1 := by
      intro x hx
      have hx' := (elem_of_list_filter.1 hx).2
      exact pidxConsNe a x l (fun h => ha (h ▸ hx')) hx'
    rw [filter_cons]
    split
    · refine List.pairwise_cons.2 ⟨?_, ?_⟩
      · intro y hy
        rw [pidxConsEq, hsub y hy]
        omega
      · refine stronglySortedWeaken _ _ _ ?_ (ih hnd')
        intro x y hx hy hxy
        rw [hsub x hx, hsub y hy]
        omega
    · refine stronglySortedWeaken _ _ _ ?_ (ih hnd')
      intro x y hx hy hxy
      rw [hsub x hx, hsub y hy]
      omega

/-! ## 1.3 `filter`: emptiness and uniqueness -/

theorem filterNo {A : Type _} (p : A → Bool) (l : List A) :
    (∀ x, x ∈ l → ¬ p x = true) → l.filter p = [] :=
  fun h => List.filter_eq_nil_iff.2 (fun x hx => h x hx)

theorem filterUnique {A : Type _} (p : A → Bool) (l : List A) (x : A) :
    l.Nodup → x ∈ l → p x = true → (∀ y, y ∈ l → p y = true → y = x) → l.filter p = [x] := by
  intro hnd
  induction l generalizing x with
  | nil => intro hx; simp at hx
  | cons a l ih =>
    intro hx hp huniq
    have ha := NoDup_cons_1_1 hnd
    have hnd' := NoDup_cons_1_2 hnd
    rw [filter_cons]
    split
    · rename_i hpa
      have hax : a = x := huniq a List.mem_cons_self hpa
      subst hax
      congr 1
      apply filterNo
      intro y hy hpy
      have : y = a := huniq y (List.mem_cons_of_mem a hy) hpy
      subst this
      exact ha hy
    · rename_i hpa
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact absurd hp hpa
      · exact ih x hnd' hx' hp (fun y hy hpy => huniq y (List.mem_cons_of_mem a hy) hpy)

/-! ## 1.4 `mjoin` over an index range -/

theorem elemOfMjoinSeq {A : Type _} (f : Nat → List A) (N : Nat) (x : A) :
    x ∈ ((List.range' 0 N).map f).flatten ↔ ∃ j, j < N ∧ x ∈ f j := by
  rw [elem_of_list_join]
  constructor
  · rintro ⟨l, hx, hl⟩
    obtain ⟨j, rfl, hj⟩ := elem_of_list_fmap.1 hl
    have := elem_of_seq.1 hj
    exact ⟨j, by omega, hx⟩
  · rintro ⟨j, hj, hx⟩
    exact ⟨f j, hx, elem_of_list_fmap.2 ⟨j, rfl, elem_of_seq.2 (by omega)⟩⟩

theorem mjoinSeqS {A : Type _} (f : Nat → List A) (N : Nat) :
    ((List.range' 0 (N + 1)).map f).flatten = ((List.range' 0 N).map f).flatten ++ f N := by
  rw [List.range'_concat]
  simp

theorem mjoinSeqNone {A : Type _} (f : Nat → List A) (N : Nat) :
    (∀ j, j < N → f j = []) → ((List.range' 0 N).map f).flatten = [] := by
  induction N with
  | zero => intro _; rfl
  | succ N ih =>
    intro h0
    rw [mjoinSeqS, h0 N (by omega), List.append_nil]
    exact ih (fun j hj => h0 j (by omega))

theorem mjoinSeqSingle {A : Type _} (f : Nat → List A) (N i : Nat) :
    (∀ j, j < N → j ≠ i → f j = []) → i < N →
    ((List.range' 0 N).map f).flatten = f i := by
  induction N with
  | zero => intro _ hi; omega
  | succ N ih =>
    intro h0 hi
    rw [mjoinSeqS]
    by_cases hiN : i = N
    · subst hiN
      rw [mjoinSeqNone f i (fun j hj => h0 j (by omega) (by omega)), List.nil_append]
    · rw [h0 N (by omega) (Ne.symm hiN), List.append_nil]
      exact ih (fun j hj hji => h0 j (by omega) hji) (by omega)

theorem filterMjoinFmap {A B : Type _} (p : A → Bool) (f : B → List A) (l : List B) :
    (l.map f).flatten.filter p = (l.map (fun j => (f j).filter p)).flatten := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [List.map_cons, List.flatten_cons, List.filter_append, ih]

theorem nodupMjoinSeq {A : Type _} (f : Nat → List A) (key : A → Nat) (N : Nat) :
    (∀ j, (f j).Nodup) → (∀ j x, x ∈ f j → key x = j) →
    ((List.range' 0 N).map f).flatten.Nodup := by
  intro hnd hkey
  induction N with
  | zero => exact List.nodup_nil
  | succ N ih =>
    rw [mjoinSeqS, NoDup_app]
    refine ⟨ih, ?_, hnd N⟩
    intro x hx hx2
    obtain ⟨j, hj, hxj⟩ := (elemOfMjoinSeq f N x).1 hx
    have e1 := hkey j x hxj
    have e2 := hkey N x hx2
    omega

/-! ## 1.5 `rblocks`: group a list by a rank, blocks in rank order -/

def rblocks {A : Type _} (rk : A → Nat) (l : List A) (n : Nat) : List A :=
  ((List.range' 0 n).map (fun d => l.filter (fun x => decide (rk x = d)))).flatten

theorem rblocksS {A : Type _} (rk : A → Nat) (l : List A) (n : Nat) :
    rblocks rk l (n + 1) = rblocks rk l n ++ l.filter (fun x => decide (rk x = n)) :=
  mjoinSeqS (fun d => l.filter (fun x => decide (rk x = d))) n

theorem elemOfRblocks {A : Type _} (rk : A → Nat) (l : List A) (n : Nat) (x : A) :
    x ∈ rblocks rk l n ↔ x ∈ l ∧ rk x < n := by
  unfold rblocks
  rw [elemOfMjoinSeq]
  constructor
  · rintro ⟨d, hd, hx⟩
    obtain ⟨he, hx⟩ := elem_of_list_filter.1 hx
    have := of_decide_eq_true he
    exact ⟨hx, by omega⟩
  · rintro ⟨hx, hrk⟩
    exact ⟨rk x, hrk, elem_of_list_filter.2 ⟨decide_eq_true rfl, hx⟩⟩

theorem rblocksNodup {A : Type _} (rk : A → Nat) (l : List A) (n : Nat) :
    l.Nodup → (rblocks rk l n).Nodup := by
  intro hnd
  induction n with
  | zero => exact List.nodup_nil
  | succ n ih =>
    rw [rblocksS, NoDup_app]
    refine ⟨ih, ?_, NoDup_filter hnd⟩
    intro x hx hx2
    have hlt := ((elemOfRblocks rk l n x).1 hx).2
    have heq := of_decide_eq_true (elem_of_list_filter.1 hx2).1
    omega

/-- The blocks are constant-rank and in rank order — no hypothesis at all. -/
theorem rblocksRankSorted {A : Type _} (rk : A → Nat) (l : List A) (n : Nat) :
    List.Pairwise (fun x y => rk x ≤ rk y) (rblocks rk l n) := by
  induction n with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    rw [rblocksS, List.pairwise_append]
    refine ⟨ih, ?_, ?_⟩
    · apply stronglySortedLookupIntro
      intro i j x y hi hj _
      have h1 := of_decide_eq_true (elem_of_list_filter.1 (elem_of_list_lookup_2 hi)).1
      have h2 := of_decide_eq_true (elem_of_list_filter.1 (elem_of_list_lookup_2 hj)).1
      omega
    · intro x hx y hy
      have hlt := ((elemOfRblocks rk l n x).1 hx).2
      have heq := of_decide_eq_true (elem_of_list_filter.1 hy).1
      omega

theorem rblocksSorted {A : Type _} (rk : A → Nat) (R : A → A → Prop) (l : List A) (n : Nat) :
    List.Pairwise R l →
    (∀ x y, x ∈ l → y ∈ l → rk x < rk y → R x y) →
    List.Pairwise R (rblocks rk l n) := by
  intro hss hcross
  induction n with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    rw [rblocksS, List.pairwise_append]
    refine ⟨ih, stronglySortedFilter R _ l hss, ?_⟩
    intro x hx y hy
    obtain ⟨hxl, hlt⟩ := (elemOfRblocks rk l n x).1 hx
    obtain ⟨heq, hyl⟩ := elem_of_list_filter.1 hy
    have := of_decide_eq_true heq
    exact hcross x y hxl hyl (by omega)

theorem rblocksPerm {A : Type _} (rk : A → Nat) (l : List A) (n : Nat) :
    l.Nodup → (∀ x, x ∈ l → rk x < n) → List.Perm (rblocks rk l n) l := by
  intro hnd hb
  apply NoDup_Permutation (rblocksNodup rk l n hnd) hnd
  intro x
  rw [elemOfRblocks]
  exact ⟨fun h => h.1, fun h => ⟨h, hb x h⟩⟩

/-- A list already sorted by rank (with a tie-break the rank refines) is its own
block decomposition. -/
theorem rblocksId {A : Type _} (rk : A → Nat) (R : A → A → Prop) (l : List A) (n : Nat) :
    l.Nodup → List.Pairwise R l →
    (∀ x, x ∈ l → rk x < n) →
    (∀ x y, x ∈ l → y ∈ l → rk x < rk y → R x y) →
    (∀ x y, x ∈ l → y ∈ l → R x y → R y x → x = y) →
    rblocks rk l n = l := by
  intro hnd hss hb hcross hasym
  apply StronglySorted_unique_strong (R := R)
  · intro x y hx hy hxy hyx
    exact hasym x y ((elemOfRblocks rk l n x).1 hx).1 hy hxy hyx
  · exact rblocksSorted rk R l n hss hcross
  · exact hss
  · exact rblocksPerm rk l n hnd hb

theorem rblocksExt {A : Type _} (rk : A → Nat) (l l' : List A) (n : Nat) :
    (∀ d, l.filter (fun x => decide (rk x = d)) = l'.filter (fun x => decide (rk x = d))) →
    rblocks rk l n = rblocks rk l' n := by
  intro h
  unfold rblocks
  congr 1
  exact List.map_congr_left (fun d _ => h d)

theorem rblocksFilter {A : Type _} (rk : A → Nat) (p : A → Bool) (l : List A) (n : Nat) :
    (rblocks rk l n).filter p = rblocks rk (l.filter p) n := by
  unfold rblocks
  rw [filterMjoinFmap]
  congr 1
  apply List.map_congr_left
  intro d _
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro x _
  exact Bool.and_comm _ _

/-! # 2. THE CONSTRUCTION -/

/-- The program row of a hart (`[]` outside the program). -/
def WeakRvwmoLin.grow (G : Gexec) (i : Nat) : List Lbl := (G.gxProg[i]?).getD []

/-- The labeled events of one hart, in po order; and of the whole graph. -/
def gevsHart (G : Gexec) (i : Nat) : List Geid :=
  (List.range' 0 (WeakRvwmoLin.grow G i).length).map (fun k => (i, k))

def gevs (G : Gexec) : List Geid :=
  ((List.range' 0 G.gxProg.length).map (gevsHart G)).flatten

/-- The po-FIRST write at-or-after `e`, in `e`'s own hart (`e` itself when `e`
is a write). -/
def gnxw (G : Gexec) (e : Geid) : Option Geid :=
  (listFind (fun k => gisW G (e.1, k))
    (List.range' e.2 ((WeakRvwmoLin.grow G e.1).length - e.2))).map
    (fun ik : Nat × Nat => (e.1, ik.2))

/-- THE RANK.  `gwix` of the next write — so segments come out in gmo order and
each segment ends with its own write — or a past-the-end slot indexed by the
hart, for the tails. -/
def WeakRvwmoLin.grank (G : Gexec) (e : Geid) : Nat :=
  match gnxw G e with
  | some w => gwix G w
  | none => (gwrites G).length + 1 + e.1

def grankBound (G : Gexec) : Nat := (gwrites G).length + 1 + G.gxProg.length

def glinEids (G : Gexec) : List Geid :=
  rblocks (WeakRvwmoLin.grank G) (gevs G) (grankBound G)

def glbl (G : Gexec) (e : Geid) : Lbl := (gxLbl G e).getD (LFence false false false false)

def glinStep (G : Gexec) (e : Geid) : Estep := ⟨e.1, glbl G e⟩

/-- The message an event contributes to the log. -/
def WeakRvwmoLin.gmsg (G : Gexec) (e : Geid) : Option Wmsg :=
  match gxLbl G e with
  | some l =>
    match lbWr l with
    | some (base, vs) => some ⟨base, vs, some e.1, lbCls l⟩
    | none => none
  | none => none

def linCand (G : Gexec) : Cand := ⟨G.gxImg, (glinEids G).map (glinStep G)⟩

/-- How many messages the first `k` steps append. -/
def linNw (G : Gexec) (k : Nat) : Nat := (((glinEids G).take k).filter (gisW G)).length

/-! ## 2.1 Events and labels — hypothesis-free bookkeeping -/

theorem WeakRvwmoLin.growLookup (G : Gexec) (i : Nat) :
    i < G.gxProg.length → G.gxProg[i]? = some (WeakRvwmoLin.grow G i) := by
  intro hi
  unfold WeakRvwmoLin.grow
  rw [List.getElem?_eq_getElem hi]
  rfl

theorem gxLblBounds (G : Gexec) (e : Geid) :
    (gxLbl G e).isSome ↔
    (e.1 < G.gxProg.length ∧ e.2 < (WeakRvwmoLin.grow G e.1).length) := by
  unfold gxLbl WeakRvwmoLin.grow
  cases hp : G.gxProg[e.1]? with
  | none =>
    have := List.getElem?_eq_none_iff.1 hp
    constructor
    · intro h; simp at h
    · rintro ⟨h1, _⟩; omega
  | some p =>
    have hlt := lookup_lt_Some hp
    simp only [Option.bind_some, Option.getD_some]
    rw [lookup_lt_is_Some]
    exact ⟨fun h => ⟨hlt, h⟩, fun h => h.2⟩

theorem glblSome (G : Gexec) (i k : Nat) :
    i < G.gxProg.length → k < (WeakRvwmoLin.grow G i).length → (gxLbl G (i, k)).isSome :=
  fun hi hk => (gxLblBounds G (i, k)).2 ⟨hi, hk⟩

theorem elemOfGevsHart (G : Gexec) (i : Nat) (e : Geid) :
    e ∈ gevsHart G i ↔ (e.1 = i ∧ e.2 < (WeakRvwmoLin.grow G i).length) := by
  unfold gevsHart
  rw [elem_of_list_fmap]
  constructor
  · rintro ⟨k, rfl, hk⟩
    have := elem_of_seq.1 hk
    exact ⟨rfl, by simp only; omega⟩
  · rintro ⟨hi, hk⟩
    obtain ⟨i', k'⟩ := e
    simp only at hi hk
    subst hi
    exact ⟨k', rfl, elem_of_seq.2 (by omega)⟩

theorem gevsHartLookup (G : Gexec) (i k : Nat) :
    k < (WeakRvwmoLin.grow G i).length → (gevsHart G i)[k]? = some (i, k) := by
  intro hk
  unfold gevsHart
  rw [list_lookup_fmap, lookup_seq_lt hk]
  simp

theorem gevsHartLookupInv (G : Gexec) (i k : Nat) (e : Geid) :
    (gevsHart G i)[k]? = some e → e = (i, k) ∧ k < (WeakRvwmoLin.grow G i).length := by
  unfold gevsHart
  rw [list_lookup_fmap]
  cases hs : (List.range' 0 (WeakRvwmoLin.grow G i).length)[k]? with
  | none => simp
  | some x =>
    obtain ⟨rfl, hlt⟩ := lookup_seq.1 hs
    intro h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨by simp, hlt⟩

theorem gevsHartNodup (G : Gexec) (i : Nat) : (gevsHart G i).Nodup := by
  apply NoDup_alt.2
  intro a b e ha hb
  obtain ⟨rfl, _⟩ := gevsHartLookupInv G i a e ha
  obtain ⟨heq, _⟩ := gevsHartLookupInv G i b _ hb
  simp only [Prod.mk.injEq] at heq
  exact heq.2

theorem elemOfGevs (G : Gexec) (e : Geid) : e ∈ gevs G ↔ (gxLbl G e).isSome := by
  unfold gevs
  rw [elemOfMjoinSeq]
  constructor
  · rintro ⟨j, hj, he⟩
    obtain ⟨he, hk⟩ := (elemOfGevsHart G j e).1 he
    subst he
    exact (gxLblBounds G e).2 ⟨hj, hk⟩
  · intro he
    obtain ⟨hi, hk⟩ := (gxLblBounds G e).1 he
    exact ⟨e.1, hi, (elemOfGevsHart G e.1 e).2 ⟨rfl, hk⟩⟩

theorem gevsNodup (G : Gexec) : (gevs G).Nodup := by
  apply nodupMjoinSeq _ (fun e : Geid => e.1)
  · exact gevsHartNodup G
  · intro j e he
    exact ((elemOfGevsHart G j e).1 he).1

theorem WeakRvwmoLin.filterAll {A : Type _} (p : A → Bool) (l : List A) :
    (∀ x, x ∈ l → p x = true) → l.filter p = l :=
  fun h => List.filter_eq_self.2 h

theorem gevsHartNil (G : Gexec) (i : Nat) : ¬ i < G.gxProg.length → gevsHart G i = [] := by
  intro hi
  unfold gevsHart WeakRvwmoLin.grow
  rw [List.getElem?_eq_none (by omega)]
  rfl

theorem filterGevsHart (G : Gexec) (i : Nat) :
    (gevs G).filter (fun e : Geid => decide (e.1 = i)) = gevsHart G i := by
  unfold gevs
  rw [filterMjoinFmap]
  by_cases hi : i < G.gxProg.length
  · rw [mjoinSeqSingle (fun j => (gevsHart G j).filter (fun e : Geid => decide (e.1 = i)))
      G.gxProg.length i ?_ hi]
    · apply WeakRvwmoLin.filterAll
      intro e he
      exact decide_eq_true ((elemOfGevsHart G i e).1 he).1
    · intro j _ hne
      apply filterNo
      intro e he hc
      have h1 := ((elemOfGevsHart G j e).1 he).1
      have h2 := of_decide_eq_true hc
      exact hne (h1 ▸ h2)
  · rw [gevsHartNil G i hi]
    apply mjoinSeqNone
    intro j hj
    apply filterNo
    intro e he hc
    have h1 := ((elemOfGevsHart G j e).1 he).1
    have h2 := of_decide_eq_true hc
    omega

/-! ## 2.2 `gnxw`: the next write -/

theorem gnxwSome (G : Gexec) (i k : Nat) (w : Geid) :
    gnxw G (i, k) = some w →
    ∃ m, w = (i, m) ∧ k ≤ m ∧ m < (WeakRvwmoLin.grow G i).length ∧
      gisW G (i, m) = true ∧
      (∀ k', k ≤ k' → k' < m → gisW G (i, k') = false) := by
  unfold gnxw
  simp only
  cases hf : listFind (fun k' => gisW G (i, k'))
      (List.range' k ((WeakRvwmoLin.grow G i).length - k)) with
  | none => simp
  | some q =>
    obtain ⟨n, j⟩ := q
    intro h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨hn, hw, hmin⟩ := list_find_Some.1 hf
    obtain ⟨rfl, hlt⟩ := lookup_seq.1 hn
    refine ⟨k + n, rfl, by omega, by omega, hw, ?_⟩
    intro k' hk1 hk2
    exact hmin (k' - k) k' (lookup_seq.2 ⟨by omega, by omega⟩) (by omega)

theorem gnxwNone (G : Gexec) (i k k' : Nat) :
    gnxw G (i, k) = none → k ≤ k' → k' < (WeakRvwmoLin.grow G i).length →
    gisW G (i, k') = false := by
  unfold gnxw
  simp only [Option.map_eq_none_iff]
  intro hf hk1 hk2
  exact list_find_None.1 hf k' (elem_of_seq.2 ⟨hk1, by omega⟩)

theorem gnxwSelf (G : Gexec) (i k : Nat) :
    (gxLbl G (i, k)).isSome → gisW G (i, k) = true → gnxw G (i, k) = some (i, k) := by
  intro hl hw
  obtain ⟨hi, hk⟩ := (gxLblBounds G (i, k)).1 hl
  simp only at hi hk
  cases hf : gnxw G (i, k) with
  | none => rw [gnxwNone G i k k hf (Nat.le_refl _) hk] at hw; cases hw
  | some w =>
    obtain ⟨m, rfl, hkm, hm, hwm, hmin⟩ := gnxwSome G i k w hf
    by_cases hkm' : k = m
    · subst hkm'; rfl
    · rw [hmin k (Nat.le_refl _) (by omega)] at hw; cases hw

/-! # 3. THE GRAPH-SIDE FACTS AND THE TRACE ORDER

Everything below runs under RVWMO⁻ + rule 14; the Rocq section variables ARE
`rvwmoMinusConsistent G ∧ grule14 G`, unpacked (deviation 3: each lemma takes the
ones it uses). -/

/-- The section-local `Hnd`. -/
theorem linNd (G : Gexec) (hwf : gwf G) : G.gxGmo.Nodup := hwf.1

/-! ## 3.1 Membership and classification -/

theorem WeakRvwmoLin.gisWGmem (G : Gexec) (e : Geid) :
    (gxLbl G e).isSome → gisW G e = true → gmem G e := by
  intro hs hw
  obtain ⟨l, hl⟩ := someOfIsSome hs
  refine ⟨l, hl, ?_⟩
  simp only [gisW, hl] at hw
  simp [lbIsMem, hw]

theorem WeakRvwmoLin.gisWGlblIs (G : Gexec) (e : Geid) :
    (gxLbl G e).isSome → gisW G e = true → glblIs G e lbIsW := by
  intro hs hw
  obtain ⟨l, hl⟩ := someOfIsSome hs
  simp only [gisW, hl] at hw
  exact ⟨l, hl, hw⟩

theorem gwritesByteGw (G : Gexec) (hwf : gwf G) (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte G e a v → e ∈ gwrites G := by
  rintro ⟨l, base, vs, j, hl, hwr, _⟩
  have hw : gisW G e = true := by simp only [gisW, hl]; exact lbWrIsW l _ hwr
  exact (gwritesElemOf G e).2
    ⟨gwfMemGmo G e hwf (WeakRvwmoLin.gisWGmem G e (by rw [hl]; rfl) hw), hw⟩

theorem WeakRvwmoLin.gwritesByteLbl (G : Gexec) (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte G e a v → (gxLbl G e).isSome := by
  rintro ⟨l, base, vs, j, hl, _⟩
  rw [hl]; rfl

theorem gwritesByteIsw (G : Gexec) (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte G e a v → gisW G e = true := by
  rintro ⟨l, base, vs, j, hl, hwr, _⟩
  simp only [gisW, hl]
  exact lbWrIsW l _ hwr

theorem greadsByteLbl (G : Gexec) (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    greadsByte G e a t v → (gxLbl G e).isSome := by
  rintro ⟨l, base, ts, vs, j, hl, _⟩
  rw [hl]; rfl

theorem greadsByteMem (G : Gexec) (hwf : gwf G) (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    greadsByte G e a t v → e ∈ G.gxGmo := by
  rintro ⟨l, base, ts, vs, j, hl, hrd, _⟩
  exact gwfMemGmo G e hwf ⟨l, hl, by simp [lbIsMem, lbRdIsR l _ hrd]⟩

theorem gwritesGmo (G : Gexec) (w : Geid) : w ∈ gwrites G → w ∈ G.gxGmo :=
  fun h => ((gwritesElemOf G w).1 h).1

theorem gwritesLbl (G : Gexec) (hwf : gwf G) (w : Geid) : w ∈ gwrites G → (gxLbl G w).isSome := by
  intro h
  obtain ⟨l, hl, _⟩ := gwfGmoMem G w hwf (gwritesGmo G w h)
  rw [hl]; rfl

theorem gwritesIsw (G : Gexec) (w : Geid) : w ∈ gwrites G → gisW G w = true :=
  fun h => ((gwritesElemOf G w).1 h).2

/-! ## 3.2 (P3) rf is gmo-FORWARD, and (P5) fr is gpos-forward -/

theorem gcomax (G : Gexec) (hlv : gloadValue G) (r : Geid) (a : Int) (t : Nat) (v : BitVec 8)
    (w' : Geid) (v' : BitVec 8) :
    greadsByte G r a t v → gwritesByte G w' a v' → gvisible G w' r → gwix G w' ≤ t :=
  fun hrd hwr hvis => (hlv r a t v hrd).2 w' v' hwr hvis

/-- THE KEY (P3): a read's named source is gmo-BEFORE it.  The `gpo` disjunct of
`gvisible` (store forwarding) is same-hart AND same-byte, so ppo rules 1–3 turn
it into a gmo edge. -/
theorem WeakRvwmoLin.grfGmo (G : Gexec) (hppo : gppoGmo G) (hlv : gloadValue G) (r : Geid)
    (a : Int) (i : Nat) (v : BitVec 8) (w : Geid) :
    greadsByte G r a (i + 1) v → gwriteAt G (i + 1) = some w → gmoLt G w r := by
  intro hrd hw
  obtain ⟨w0, hw0, hwb, hvis⟩ := (hlv r a (i + 1) v hrd).1
  rw [hw, Option.some.injEq] at hw0
  subst hw0
  rcases hvis with hmo | hpo
  · exact hmo
  · exact hppo _ _ (Or.inl ⟨hpo, a, Or.inl ⟨v, hwb⟩, Or.inr ⟨i + 1, v, hrd⟩⟩)

/-- (P5): a write the read did NOT take is not gmo-visible to it, and `gmo` is
total on members. -/
theorem gfrGe (G : Gexec) (hwf : gwf G) (hlv : gloadValue G) (r : Geid) (a : Int) (t : Nat)
    (v : BitVec 8) (w' : Geid) (v' : BitVec 8) :
    greadsByte G r a t v → gwritesByte G w' a v' → t < gwix G w' → gpos G r ≤ gpos G w' := by
  intro hrd hwr hlt
  apply gmoNltGe G w' r (linNd G hwf) (gwritesGmo G w' (gwritesByteGw G hwf w' a v' hwr))
    (greadsByteMem G hwf r a t v hrd)
  intro hmo
  have := gcomax G hlv r a t v w' v' hrd hwr (Or.inl hmo)
  omega

/-! ## 3.3 Same-hart writes: position order IS `gwix` order (rule 14) -/

theorem gsameHartGwix (G : Gexec) (hwf : gwf G) (h14 : grule14 G) (i k1 k2 : Nat) :
    i < G.gxProg.length →
    k1 < (WeakRvwmoLin.grow G i).length → k2 < (WeakRvwmoLin.grow G i).length →
    gisW G (i, k1) = true → gisW G (i, k2) = true → k1 < k2 →
    gwix G (i, k1) < gwix G (i, k2) := by
  intro hi hb1 hb2 hw1 hw2 hlt
  have hl1 := glblSome G i k1 hi hb1
  have hl2 := glblSome G i k2 hi hb2
  have hmo : gmoLt G (i, k1) (i, k2) :=
    h14 _ _ ⟨rfl, hlt, hl1, hl2⟩ (WeakRvwmoLin.gisWGmem G _ hl1 hw1)
      (WeakRvwmoLin.gisWGlblIs G _ hl2 hw2)
  exact (gwixGposLt G _ _ (linNd G hwf) (gisWGwrites G _ hwf hl1 hw1)
    (gisWGwrites G _ hwf hl2 hw2)).2 hmo.2.2

/-! ## 3.4 The rank: monotone in po, bounded, and `gwix` on writes -/

theorem grankWrite (G : Gexec) (hwf : gwf G) (e : Geid) :
    e ∈ gwrites G → WeakRvwmoLin.grank G e = gwix G e := by
  intro he
  obtain ⟨i, k⟩ := e
  unfold WeakRvwmoLin.grank
  rw [gnxwSelf G i k (gwritesLbl G hwf _ he) (gwritesIsw G _ he)]

theorem grankLtBound (G : Gexec) (hwf : gwf G) (e : Geid) :
    (gxLbl G e).isSome → WeakRvwmoLin.grank G e < grankBound G := by
  intro hl
  obtain ⟨hi, hk⟩ := (gxLblBounds G e).1 hl
  obtain ⟨i, k⟩ := e
  simp only at hi hk
  unfold WeakRvwmoLin.grank grankBound
  cases hf : gnxw G (i, k) with
  | none => dsimp only; omega
  | some w =>
    obtain ⟨m, rfl, _, hm, hw, _⟩ := gnxwSome G i k w hf
    have := gwixLe G (i, m) (gisWGwrites G (i, m) hwf (glblSome G i m hi hm) hw)
    dsimp only; omega

theorem grankMono (G : Gexec) (hwf : gwf G) (h14 : grule14 G) (i k1 k2 : Nat) :
    i < G.gxProg.length → k1 ≤ k2 → k2 < (WeakRvwmoLin.grow G i).length →
    WeakRvwmoLin.grank G (i, k1) ≤ WeakRvwmoLin.grank G (i, k2) := by
  intro hi hle hk2
  unfold WeakRvwmoLin.grank
  cases h2 : gnxw G (i, k2) with
  | some w2 =>
    obtain ⟨m2, rfl, hk2m, hm2, hw2, _⟩ := gnxwSome G i k2 w2 h2
    cases h1 : gnxw G (i, k1) with
    | none => rw [gnxwNone G i k1 m2 h1 (by omega) hm2] at hw2; cases hw2
    | some w1 =>
      obtain ⟨m1, rfl, hk1m, hm1, hw1, hmin1⟩ := gnxwSome G i k1 w1 h1
      have hle' : m1 ≤ m2 := by
        by_cases hlt : m2 < m1
        · rw [hmin1 m2 (by omega) hlt] at hw2; cases hw2
        · omega
      dsimp only
      by_cases heq : m1 = m2
      · subst heq; exact Nat.le_refl _
      · exact Nat.le_of_lt (gsameHartGwix G hwf h14 i m1 m2 hi hm1 hm2 hw1 hw2 (by omega))
  | none =>
    cases h1 : gnxw G (i, k1) with
    | none => dsimp only; omega
    | some w1 =>
      obtain ⟨m1, rfl, _, hm1, hw1, _⟩ := gnxwSome G i k1 w1 h1
      have := gwixLe G (i, m1) (gisWGwrites G (i, m1) hwf (glblSome G i m1 hi hm1) hw1)
      dsimp only; omega

/-! ## 3.5 The trace: NoDup, membership, and the two order facts -/

theorem glinNodup (G : Gexec) : (glinEids G).Nodup := rblocksNodup _ _ _ (gevsNodup G)

theorem elemOfGlin (G : Gexec) (hwf : gwf G) (e : Geid) :
    e ∈ glinEids G ↔ (gxLbl G e).isSome := by
  unfold glinEids
  rw [elemOfRblocks, elemOfGevs]
  exact ⟨fun h => h.1, fun h => ⟨h, grankLtBound G hwf e h⟩⟩

theorem glinLookupLbl (G : Gexec) (hwf : gwf G) (k : Nat) (e : Geid) :
    (glinEids G)[k]? = some e → (gxLbl G e).isSome :=
  fun h => (elemOfGlin G hwf e).1 (elem_of_list_lookup_2 h)

theorem glinIndex (G : Gexec) (hwf : gwf G) (e : Geid) :
    (gxLbl G e).isSome → ∃ k : Nat, (glinEids G)[k]? = some e :=
  fun h => elem_of_list_lookup_1 ((elemOfGlin G hwf e).2 h)

/-- (P1) The per-hart subsequence of the trace IS the hart's event row. -/
theorem glinHart (G : Gexec) (hwf : gwf G) (h14 : grule14 G) (i : Nat) :
    (glinEids G).filter (fun e : Geid => decide (e.1 = i)) = gevsHart G i := by
  unfold glinEids
  rw [rblocksFilter, filterGevsHart]
  by_cases hi : i < G.gxProg.length
  · apply rblocksId (WeakRvwmoLin.grank G) (fun x y : Geid => x.2 ≤ y.2)
    · exact gevsHartNodup G i
    · apply stronglySortedLookupIntro
      intro a b x y hx hy hab
      obtain ⟨rfl, _⟩ := gevsHartLookupInv G i a x hx
      obtain ⟨rfl, _⟩ := gevsHartLookupInv G i b y hy
      show a ≤ b
      omega
    · intro x hx
      obtain ⟨hx1, hx2⟩ := (elemOfGevsHart G i x).1 hx
      apply grankLtBound G hwf
      exact (gxLblBounds G x).2 ⟨by rw [hx1]; exact hi, by rw [hx1]; exact hx2⟩
    · intro x y hx hy hrk
      obtain ⟨hx1, hx2⟩ := (elemOfGevsHart G i x).1 hx
      obtain ⟨hy1, hy2⟩ := (elemOfGevsHart G i y).1 hy
      by_cases h : x.2 ≤ y.2
      · exact h
      · exfalso
        obtain ⟨ix, kx⟩ := x
        obtain ⟨iy, ky⟩ := y
        simp only at hx1 hy1 hx2 hy2 h
        rw [hx1] at hrk
        rw [hy1] at hrk
        have := grankMono G hwf h14 i ky kx hi (by omega) hx2
        omega
    · intro x y hx hy h1 h2
      obtain ⟨hx1, _⟩ := (elemOfGevsHart G i x).1 hx
      obtain ⟨hy1, _⟩ := (elemOfGevsHart G i y).1 hy
      exact Prod.ext (hx1.trans hy1.symm) (by omega)
  · rw [gevsHartNil G i hi]
    unfold rblocks
    exact mjoinSeqNone _ _ (fun j _ => rfl)

/-- ... hence trace order and po order agree inside a hart. -/
theorem glinPoLt (G : Gexec) (hwf : gwf G) (h14 : grule14 G) (k1 k2 : Nat) (e1 e2 : Geid) :
    (glinEids G)[k1]? = some e1 → (glinEids G)[k2]? = some e2 →
    e1.1 = e2.1 → e1.2 < e2.2 → k1 < k2 := by
  intro h1 h2 hag hlt
  have hss := filterSortedPidx (fun e : Geid => decide (e.1 = e1.1)) (glinEids G) (glinNodup G)
  rw [glinHart G hwf h14 e1.1] at hss
  have hb1 : e1.2 < (WeakRvwmoLin.grow G e1.1).length :=
    ((gxLblBounds G e1).1 (glinLookupLbl G hwf k1 e1 h1)).2
  have hb2 : e2.2 < (WeakRvwmoLin.grow G e1.1).length := by
    rw [hag]; exact ((gxLblBounds G e2).1 (glinLookupLbl G hwf k2 e2 h2)).2
  have hg1 : (gevsHart G e1.1)[e1.2]? = some e1 := by rw [gevsHartLookup G e1.1 e1.2 hb1]
  have hg2 : (gevsHart G e1.1)[e2.2]? = some e2 := by rw [gevsHartLookup G e1.1 e2.2 hb2, hag]
  have hp : pidx (glinEids G) e1 < pidx (glinEids G) e2 :=
    stronglySortedLookupElim _ _ e1.2 e2.2 e1 e2 hss hg1 hg2 hlt
  rw [pidxOfLookup _ k1 e1 (glinNodup G) h1, pidxOfLookup _ k2 e2 (glinNodup G) h2] at hp
  exact hp

theorem glinPoIff (G : Gexec) (hwf : gwf G) (h14 : grule14 G) (k1 k2 : Nat) (e1 e2 : Geid) :
    (glinEids G)[k1]? = some e1 → (glinEids G)[k2]? = some e2 → e1.1 = e2.1 →
    (k1 < k2 ↔ e1.2 < e2.2) := by
  intro h1 h2 hag
  refine ⟨fun hk => ?_, glinPoLt G hwf h14 k1 k2 e1 e2 h1 h2 hag⟩
  by_cases hlt : e1.2 < e2.2
  · exact hlt
  · exfalso
    by_cases heq : e1.2 = e2.2
    · have he : e1 = e2 := Prod.ext hag heq
      rw [he] at h1
      have := NoDup_lookup (glinNodup G) h1 h2
      omega
    · have := glinPoLt G hwf h14 k2 k1 e2 e1 h2 h1 hag.symm (by omega)
      omega

/-- Rank order implies trace order — the blocks are emitted in rank order. -/
theorem glinRankLt (G : Gexec) (k1 k2 : Nat) (e1 e2 : Geid) :
    (glinEids G)[k1]? = some e1 → (glinEids G)[k2]? = some e2 →
    WeakRvwmoLin.grank G e1 < WeakRvwmoLin.grank G e2 → k1 < k2 := by
  intro h1 h2 hlt
  have hss := rblocksRankSorted (WeakRvwmoLin.grank G) (gevs G) (grankBound G)
  by_cases hk : k1 < k2
  · exact hk
  · exfalso
    by_cases heq : k1 = k2
    · rw [heq, h2, Option.some.injEq] at h1
      rw [h1] at hlt
      omega
    · have hx : WeakRvwmoLin.grank G e2 ≤ WeakRvwmoLin.grank G e1 :=
        stronglySortedLookupElim _ _ k2 k1 e2 e1 hss h2 h1 (by omega)
      omega

/-! ## 3.6 (P2) The trace's writes ARE `gwrites G` -/

theorem glinWrites (G : Gexec) (hwf : gwf G) : (glinEids G).filter (gisW G) = gwrites G := by
  have hnd := linNd G hwf
  have hel : ∀ e, e ∈ (gevs G).filter (gisW G) ↔ e ∈ gwrites G := by
    intro e
    constructor
    · intro he
      obtain ⟨hb, he⟩ := elem_of_list_filter.1 he
      exact gisWGwrites G e hwf ((elemOfGevs G e).1 he) hb
    · intro he
      exact elem_of_list_filter.2 ⟨gwritesIsw G e he, (elemOfGevs G e).2 (gwritesLbl G hwf e he)⟩
  unfold glinEids
  rw [rblocksFilter]
  have hR : rblocks (WeakRvwmoLin.grank G) (gwrites G) (grankBound G) = gwrites G := by
    apply rblocksId (WeakRvwmoLin.grank G) (fun x y : Geid => gwix G x ≤ gwix G y)
    · exact gwritesNodup G hnd
    · refine stronglySortedWeaken _ _ _ ?_ (gwritesSorted G hnd)
      intro x y hx hy hxy
      exact Nat.le_of_lt ((gwixGposLt G x y hnd hx hy).2 hxy)
    · intro x hx
      exact grankLtBound G hwf x (gwritesLbl G hwf x hx)
    · intro x y hx hy hrk
      rw [grankWrite G hwf x hx, grankWrite G hwf y hy] at hrk
      exact Nat.le_of_lt hrk
    · intro x y hx hy h1 h2
      exact gwixInj G x y hnd hx hy (by omega)
  refine Eq.trans ?_ hR
  apply rblocksExt
  intro d
  cases hd : gwriteAt G d with
  | some w =>
    obtain ⟨hw, hwix⟩ := gwriteAtInv G d w hnd hd
    have huniq : ∀ y, y ∈ gwrites G → decide (WeakRvwmoLin.grank G y = d) = true → y = w := by
      intro y hy hp
      have := of_decide_eq_true hp
      rw [grankWrite G hwf y hy] at this
      exact gwixInj G y w hnd hy hw (by omega)
    have hpw : decide (WeakRvwmoLin.grank G w = d) = true :=
      decide_eq_true (by rw [grankWrite G hwf w hw]; exact hwix)
    rw [filterUnique _ _ w (NoDup_filter (gevsNodup G)) ((hel w).2 hw) hpw
        (fun y hy hp => huniq y ((hel y).1 hy) hp),
      filterUnique _ _ w (gwritesNodup G hnd) hw hpw huniq]
  | none =>
    have hno : ∀ e, e ∈ gwrites G → ¬ decide (WeakRvwmoLin.grank G e = d) = true := by
      intro e he heq
      have := of_decide_eq_true heq
      rw [grankWrite G hwf e he] at this
      rw [← this, gwriteAtGwix G e he] at hd
      cases hd
    rw [filterNo _ _ (fun e he => hno e ((hel e).1 he)), filterNo _ _ hno]

/-! ## 3.7 The candidate's trace and log -/

theorem linTrLookup (G : Gexec) (k : Nat) (e : Geid) :
    (glinEids G)[k]? = some e → (linCand G).cdTr[k]? = some (glinStep G e) := by
  intro h
  show ((glinEids G).map (glinStep G))[k]? = _
  rw [list_lookup_fmap, h]
  rfl

theorem linTrLookupInv (G : Gexec) (k : Nat) (s : Estep) :
    (linCand G).cdTr[k]? = some s → ∃ e, (glinEids G)[k]? = some e ∧ s = glinStep G e := by
  show ((glinEids G).map (glinStep G))[k]? = some s → _
  rw [list_lookup_fmap]
  cases he : (glinEids G)[k]? with
  | none => simp
  | some e =>
    intro h
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨e, rfl, h.symm⟩

/-- Lean-only helper: a trace step at a known event index IS that event's step. -/
theorem linTrEq (G : Gexec) (k : Nat) (e : Geid) (s : Estep) :
    (glinEids G)[k]? = some e → (candExec (linCand G)).exTr[k]? = some s → s = glinStep G e := by
  intro he hs
  rw [candExTr, linTrLookup G k e he, Option.some.injEq] at hs
  exact hs.symm

theorem linTrLen (G : Gexec) : (linCand G).cdTr.length = (glinEids G).length := by
  simp [linCand]

theorem linLbl (G : Gexec) (hwf : gwf G) (k : Nat) (e : Geid) :
    (glinEids G)[k]? = some e → gxLbl G e = some (glbl G e) := by
  intro h
  obtain ⟨l, hl⟩ := someOfIsSome (glinLookupLbl G hwf k e h)
  simp [glbl, hl]

theorem esWmsgGlin (G : Gexec) (e : Geid) : esWmsg (glinStep G e) = WeakRvwmoLin.gmsg G e := by
  unfold esWmsg WeakRvwmoLin.gmsg glinStep glbl
  cases gxLbl G e with
  | none => rfl
  | some l =>
    simp only [Option.getD_some]
    cases lbWr l with
    | none => rfl
    | some p => rfl

theorem trMsgsOmap (l : List Estep) : trMsgs l = l.filterMap esWmsg := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    rw [trMsgs, esMsgWmsg, ih, List.filterMap_cons]
    cases esWmsg s <;> rfl

theorem omapGlin (G : Gexec) (l : List Geid) :
    (l.map (glinStep G)).filterMap esWmsg = l.filterMap (WeakRvwmoLin.gmsg G) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    rw [List.map_cons, List.filterMap_cons, List.filterMap_cons, esWmsgGlin, ih]

theorem linLogTake (G : Gexec) (k : Nat) :
    cdLog (linCand G) k = ((glinEids G).take k).filterMap (WeakRvwmoLin.gmsg G) := by
  unfold cdLog
  show trMsgs (((glinEids G).map (glinStep G)).take k) = _
  rw [← fmap_take, trMsgsOmap, omapGlin]

theorem gmsgIsW (G : Gexec) (e : Geid) : (WeakRvwmoLin.gmsg G e).isSome ↔ gisW G e = true := by
  unfold WeakRvwmoLin.gmsg gisW
  cases gxLbl G e with
  | none => simp
  | some l => cases l <;> simp [lbWr, lbIsW]

theorem omapGmsgLen (G : Gexec) (l : List Geid) :
    (l.filterMap (WeakRvwmoLin.gmsg G)).length = (l.filter (gisW G)).length := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    rw [List.filterMap_cons, filter_cons]
    cases hm : WeakRvwmoLin.gmsg G e with
    | some m =>
      have hw : gisW G e = true := (gmsgIsW G e).1 (by rw [hm]; rfl)
      simp [hw, ih]
    | none =>
      have hw : gisW G e = false := by
        cases h : gisW G e
        · rfl
        · have := (gmsgIsW G e).2 h
          rw [hm] at this
          cases this
      simp [hw, ih]

theorem linLogLen (G : Gexec) (k : Nat) : (cdLog (linCand G) k).length = linNw G k := by
  rw [linLogTake, omapGmsgLen]
  rfl

theorem filterTakeMono {A : Type _} (p : A → Bool) (l : List A) (k k' : Nat) :
    k ≤ k' → ((l.take k).filter p).length ≤ ((l.take k').filter p).length := by
  intro hle
  have h : l.take k = (l.take k').take k := by rw [List.take_take, Nat.min_eq_left hle]
  rw [h]
  conv => rhs; rw [← List.take_append_drop k (l.take k')]
  rw [List.filter_append, List.length_append]
  omega

theorem linNwMono (G : Gexec) (k k' : Nat) : k ≤ k' → linNw G k ≤ linNw G k' :=
  filterTakeMono _ _ k k'

theorem linNwS (G : Gexec) (k : Nat) (e : Geid) :
    (glinEids G)[k]? = some e → gisW G e = true → linNw G (k + 1) = linNw G k + 1 := by
  intro he hw
  unfold linNw
  rw [take_S_r he, List.filter_append]
  simp [hw]

/-- (P2) The write at trace index `k` is `gwrites G` entry number `linNw G k` —
the trace's writes come out in gmo order. -/
theorem linGwritesSplit (G : Gexec) (hwf : gwf G) (k : Nat) (e : Geid) :
    (glinEids G)[k]? = some e → gisW G e = true → (gwrites G)[linNw G k]? = some e := by
  intro he hw
  have hsplit : (glinEids G).filter (gisW G) =
      ((glinEids G).take k).filter (gisW G) ++ e :: ((glinEids G).drop (k + 1)).filter (gisW G) := by
    conv => lhs; rw [← List.take_append_drop (k + 1) (glinEids G)]
    rw [take_S_r he]
    simp [List.filter_append, hw]
  rw [← glinWrites G hwf, hsplit]
  unfold linNw
  rw [lookup_app_r (Nat.le_refl _), Nat.sub_self]
  rfl

theorem linTsWrite (G : Gexec) (hwf : gwf G) (k : Nat) (e : Geid) :
    (glinEids G)[k]? = some e → gisW G e = true →
    evTs (candExec (linCand G)) (ev_at k) = gwix G e := by
  intro he hw
  have hk : k ≤ (linCand G).cdTr.length := by
    rw [linTrLen]; have := lookup_lt_Some he; omega
  rw [candEvTs (linCand G) k hk, linLogLen]
  exact (gwixOfLookup G (linNw G k) e (linNd G hwf) (linGwritesSplit G hwf k e he hw)).symm

/-- (P3) A read's source has already been emitted. -/
theorem linSourceBefore (G : Gexec) (hwf : gwf G) (hppo : gppoGmo G) (hlv : gloadValue G)
    (h14 : grule14 G) (k : Nat) (r : Geid) (a : Int) (i : Nat) (v : BitVec 8) :
    (glinEids G)[k]? = some r → greadsByte G r a (i + 1) v →
    ∃ kw w, gwriteAt G (i + 1) = some w ∧ (glinEids G)[kw]? = some w ∧ kw < k := by
  intro hk hrd
  obtain ⟨w, hwa, _, _⟩ := (hlv r a (i + 1) v hrd).1
  have hmo := WeakRvwmoLin.grfGmo G hppo hlv r a i v w hrd hwa
  obtain ⟨hw, _⟩ := gwriteAtInv G (i + 1) w (linNd G hwf) hwa
  obtain ⟨kw, hkw⟩ := glinIndex G hwf w (gwritesLbl G hwf w hw)
  refine ⟨kw, w, hwa, hkw, ?_⟩
  apply glinRankLt G kw k w r hkw hk
  rw [grankWrite G hwf w hw]
  have hrl := greadsByteLbl G r a (i + 1) v hrd
  obtain ⟨hri, hrk⟩ := (gxLblBounds G r).1 hrl
  obtain ⟨ir, kr⟩ := r
  simp only at hri hrk
  unfold WeakRvwmoLin.grank
  cases hf : gnxw G (ir, kr) with
  | none => have := gwixLe G w hw; dsimp only; omega
  | some w' =>
    obtain ⟨m, rfl, hkm, hm, hwm, _⟩ := gnxwSome G ir kr w' hf
    have hlm := glblSome G ir m hri hm
    have hmo' : gmoLt G w (ir, m) := by
      by_cases hkm' : kr = m
      · subst hkm'; exact hmo
      · apply gmoLtTrans G w (ir, kr) (ir, m) hmo
        exact h14 _ _ ⟨rfl, show kr < m by omega, hrl, hlm⟩
          (gwfGmoMem G (ir, kr) hwf (greadsByteMem G hwf _ a _ v hrd))
          (WeakRvwmoLin.gisWGlblIs G _ hlm hwm)
    dsimp only
    exact (gwixGposLt G w (ir, m) (linNd G hwf) hw
      (gisWGwrites G (ir, m) hwf hlm hwm)).2 hmo'.2.2

theorem linReadTsLe (G : Gexec) (hwf : gwf G) (hppo : gppoGmo G) (hlv : gloadValue G)
    (h14 : grule14 G) (k : Nat) (r : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    (glinEids G)[k]? = some r → greadsByte G r a t v → t ≤ (cdLog (linCand G) k).length := by
  intro hk hrd
  rw [linLogLen]
  cases t with
  | zero => omega
  | succ i =>
    obtain ⟨kw, w, hwa, hkw, hlt⟩ := linSourceBefore G hwf hppo hlv h14 k r a i v hk hrd
    obtain ⟨hw, hwix⟩ := gwriteAtInv G (i + 1) w (linNd G hwf) hwa
    have hsp := linGwritesSplit G hwf kw w hkw (gwritesIsw G w hw)
    rw [gwixOfLookup G (linNw G kw) w (linNd G hwf) hsp] at hwix
    have hS := linNwS G kw w hkw (gwritesIsw G w hw)
    have := linNwMono G (kw + 1) k (by omega)
    omega

/-! ## 3.8 The final log IS `gwrites G` through `gmsg` -/

theorem omapGmsgFilter (G : Gexec) (l : List Geid) :
    l.filterMap (WeakRvwmoLin.gmsg G) = (l.filter (gisW G)).filterMap (WeakRvwmoLin.gmsg G) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    rw [filter_cons]
    cases hw : gisW G e with
    | true =>
      simp only [↓reduceIte]
      rw [List.filterMap_cons, List.filterMap_cons, ih]
    | false =>
      have hm : WeakRvwmoLin.gmsg G e = none := by
        cases h : WeakRvwmoLin.gmsg G e
        · rfl
        · have := (gmsgIsW G e).1 (by rw [h]; rfl)
          rw [hw] at this
          cases this
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [List.filterMap_cons, hm, ih]

theorem linFullLog (G : Gexec) (hwf : gwf G) :
    cdLog (linCand G) (linCand G).cdTr.length = (gwrites G).filterMap (WeakRvwmoLin.gmsg G) := by
  rw [linLogTake, linTrLen, take_ge (Nat.le_refl _), omapGmsgFilter, glinWrites G hwf]

theorem linExLog (G : Gexec) (hwf : gwf G) :
    exLog (candExec (linCand G)) = (gwrites G).filterMap (WeakRvwmoLin.gmsg G) := by
  rw [candExLog, linFullLog G hwf]

theorem linExImg (G : Gexec) : exImg (candExec (linCand G)) = G.gxImg := candExImg _

theorem omapLookupAll {A B : Type _} (f : A → Option B) (l : List A) (i : Nat) (x : A) :
    (∀ y, y ∈ l → (f y).isSome) → l[i]? = some x → (l.filterMap f)[i]? = f x := by
  induction l generalizing i with
  | nil => intro _ hi; simp at hi
  | cons a l ih =>
    intro hall hi
    obtain ⟨b, hb⟩ := someOfIsSome (hall a List.mem_cons_self)
    rw [List.filterMap_cons, hb]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simp [hb]
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi ⊢
      exact ih i (fun y hy => hall y (List.mem_cons_of_mem a hy)) hi

theorem linLogFullLookup (G : Gexec) (i : Nat) (w : Geid) :
    (gwrites G)[i]? = some w →
    ((gwrites G).filterMap (WeakRvwmoLin.gmsg G))[i]? = WeakRvwmoLin.gmsg G w :=
  fun hi => omapLookupAll _ _ i w (fun y hy => (gmsgIsW G y).2 (gwritesIsw G y hy)) hi

theorem WeakRvwmoLin.gmsgByte (G : Gexec) (w : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte G w a v → ∃ m, WeakRvwmoLin.gmsg G w = some m ∧ msgByte m a = some v := by
  rintro ⟨l, base, vs, j, hl, hwr, hv, ha⟩
  refine ⟨⟨base, vs, some w.1, lbCls l⟩, ?_, ?_⟩
  · simp [WeakRvwmoLin.gmsg, hl, hwr]
  · unfold msgByte
    have h1 : base ≤ a := by rw [← ha]; unfold accAddr; omega
    have h2 : (a - base).toNat = j := by rw [← ha]; unfold accAddr; omega
    simp only [h1, ↓reduceIte, h2]
    exact hv

theorem gmsgByteInv (G : Gexec) (w : Geid) (m : Wmsg) (a : Int) (v : BitVec 8) :
    WeakRvwmoLin.gmsg G w = some m → msgByte m a = some v → gwritesByte G w a v := by
  unfold WeakRvwmoLin.gmsg
  cases hl : gxLbl G w with
  | none => simp
  | some l =>
    dsimp only
    cases hwr : lbWr l with
    | none => simp
    | some p =>
      obtain ⟨base, vs⟩ := p
      intro hm hv
      simp only [Option.some.injEq] at hm
      subst hm
      unfold msgByte at hv
      dsimp only at hv
      split at hv
      · rename_i hb
        exact ⟨l, base, vs, (a - base).toNat, hl, hwr, hv, by unfold accAddr; omega⟩
      · cases hv

theorem linLogByteFinal (G : Gexec) (t : Nat) (w : Geid) (a : Int) (v : BitVec 8) :
    gwriteAt G t = some w → gwritesByte G w a v →
    logByte G.gxImg ((gwrites G).filterMap (WeakRvwmoLin.gmsg G)) t a = some v := by
  cases t with
  | zero => intro h; simp [gwriteAt] at h
  | succ i =>
    intro hw hb
    rw [logByteS, linLogFullLookup G i w hw]
    obtain ⟨m, hm, hmb⟩ := WeakRvwmoLin.gmsgByte G w a v hb
    rw [hm]
    exact hmb

theorem linLogByteFinalInv (G : Gexec) (t : Nat) (w : Geid) (a : Int) (v : BitVec 8) :
    gwriteAt G t = some w →
    logByte G.gxImg ((gwrites G).filterMap (WeakRvwmoLin.gmsg G)) t a = some v →
    gwritesByte G w a v := by
  cases t with
  | zero => intro h; simp [gwriteAt] at h
  | succ i =>
    intro hw hlb
    rw [logByteS, linLogFullLookup G i w hw] at hlb
    cases hm : WeakRvwmoLin.gmsg G w with
    | none => rw [hm] at hlb; simp at hlb
    | some m =>
      rw [hm] at hlb
      exact gmsgByteInv G w m a v hm hlb

/-! ## 3.9 The dictionary: candidate relations ARE graph relations -/

theorem linIsW (G : Gexec) (hwf : gwf G) (k : Nat) (e : Geid) :
    (glinEids G)[k]? = some e →
    (isW (candExec (linCand G)) (ev_at k) ↔ gisW G e = true) := by
  intro hk
  unfold isW gisW
  rw [linLbl G hwf k e hk]
  constructor
  · rintro ⟨s, hs, hw⟩
    rw [linTrEq G k e s hk hs] at hw
    exact hw
  · intro hw
    exact ⟨glinStep G e, by rw [candExTr]; exact linTrLookup G k e hk, hw⟩

theorem linWrB (G : Gexec) (hwf : gwf G) (k : Nat) (e : Geid) (a : Int) :
    (glinEids G)[k]? = some e →
    (wrB (candExec (linCand G)) a (ev_at k) ↔ ∃ v, gwritesByte G e a v) := by
  intro hk
  have hgw : (gxLbl G e).isSome := glinLookupLbl G hwf k e hk
  constructor
  · rintro ⟨hW, hwr⟩
    have hw := (linIsW G hwf k e hk).1 hW
    unfold evWrites at hwr
    rw [linExImg, linExLog G hwf, linTsWrite G hwf k e hk hw] at hwr
    obtain ⟨v, hv⟩ := someOfIsSome hwr
    exact ⟨v, linLogByteFinalInv G (gwix G e) e a v
      (gwriteAtGwix G e (gisWGwrites G e hwf hgw hw)) hv⟩
  · rintro ⟨v, hv⟩
    have hw := gwritesByteIsw G e a v hv
    refine ⟨(linIsW G hwf k e hk).2 hw, ?_⟩
    unfold evWrites
    rw [linExImg, linExLog G hwf, linTsWrite G hwf k e hk hw,
      linLogByteFinal G (gwix G e) e a v (gwriteAtGwix G e (gisWGwrites G e hwf hgw hw)) hv]
    rfl

theorem linReadsAt (G : Gexec) (hwf : gwf G) (k : Nat) (e : Geid) (a : Int) (t : Nat)
    (v : BitVec 8) :
    (glinEids G)[k]? = some e →
    (readsAt (candExec (linCand G)) k a t v ↔ greadsByte G e a t v) := by
  intro hk
  constructor
  · rintro ⟨s, base, ts, vs, j, hs, hrd, hj, hv, ha⟩
    rw [linTrEq G k e s hk hs] at hrd
    exact ⟨glbl G e, base, ts, vs, j, linLbl G hwf k e hk, hrd, hj, hv, ha.symm⟩
  · rintro ⟨l, base, ts, vs, j, hl, hrd, hj, hv, ha⟩
    rw [linLbl G hwf k e hk, Option.some.injEq] at hl
    subst hl
    exact ⟨glinStep G e, base, ts, vs, j, by rw [candExTr]; exact linTrLookup G k e hk, hrd, hj,
      hv, ha.symm⟩

theorem linRdB (G : Gexec) (hwf : gwf G) (k : Nat) (e : Geid) (a : Int) :
    (glinEids G)[k]? = some e →
    (rdB (candExec (linCand G)) a (ev_at k) ↔ ∃ t v, greadsByte G e a t v) := by
  intro hk
  constructor
  · rintro ⟨k', t, v, heq, hr⟩
    have hkk : k' = k := by injection heq with h; exact h.symm
    rw [hkk] at hr
    exact ⟨t, v, (linReadsAt G hwf k e a t v hk).1 hr⟩
  · rintro ⟨t, v, hr⟩
    exact ⟨k, t, v, rfl, (linReadsAt G hwf k e a t v hk).2 hr⟩

theorem linAccB (G : Gexec) (hwf : gwf G) (k : Nat) (e : Geid) (a : Int) :
    (glinEids G)[k]? = some e →
    (accB (candExec (linCand G)) a (ev_at k) ↔ gaccesses G e a) := by
  intro hk
  unfold accB gaccesses
  rw [linWrB G hwf k e a hk, linRdB G hwf k e a hk]

theorem linPoDict (G : Gexec) (hwf : gwf G) (h14 : grule14 G) (k1 k2 : Nat) (e1 e2 : Geid) :
    (glinEids G)[k1]? = some e1 → (glinEids G)[k2]? = some e2 →
    (po (candExec (linCand G)) (ev_at k1) (ev_at k2) ↔ WeakRvwmoGraph.gpo G e1 e2) := by
  intro h1 h2
  constructor
  · rintro ⟨a, b, s1, s2, ha, hb, hlt, hs1, hs2, hag⟩
    have ha' : a = k1 := by injection ha with h; exact h.symm
    have hb' : b = k2 := by injection hb with h; exact h.symm
    rw [ha'] at hs1 hlt
    rw [hb'] at hs2 hlt
    have e1' := linTrEq G k1 e1 s1 h1 hs1
    have e2' := linTrEq G k2 e2 s2 h2 hs2
    subst e1' e2'
    exact ⟨hag, (glinPoIff G hwf h14 k1 k2 e1 e2 h1 h2 hag).1 hlt,
      glinLookupLbl G hwf k1 e1 h1, glinLookupLbl G hwf k2 e2 h2⟩
  · rintro ⟨hag, hlt, _, _⟩
    exact ⟨k1, k2, glinStep G e1, glinStep G e2, rfl, rfl,
      glinPoLt G hwf h14 k1 k2 e1 e2 h1 h2 hag hlt, linTrLookup G k1 e1 h1,
      linTrLookup G k2 e2 h2, hag⟩

theorem greadsByteIsR (G : Gexec) (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    greadsByte G e a t v → glblIs G e lbIsR := by
  rintro ⟨l, base, ts, vs, j, hl, hrd, _⟩
  exact ⟨l, hl, lbRdIsR l _ hrd⟩

theorem WeakRvwmoLin.gwritesByteIsW (G : Gexec) (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte G e a v → glblIs G e lbIsW := by
  rintro ⟨l, base, vs, j, hl, hwr, _⟩
  exact ⟨l, hl, lbWrIsW l _ hwr⟩

theorem linSrcGmo (G : Gexec) (hwf : gwf G) (hppo : gppoGmo G) (hlv : gloadValue G) (e : Geid)
    (a : Int) (t : Nat) (v : BitVec 8) :
    greadsByte G e a t v → 0 < t →
    ∃ w, gwriteAt G t = some w ∧ gwritesByte G w a v ∧ gmoLt G w e ∧ gwix G w = t := by
  intro hg ht
  cases t with
  | zero => omega
  | succ i =>
    obtain ⟨w, hwa, hwb, _⟩ := (hlv e a (i + 1) v hg).1
    exact ⟨w, hwa, hwb, WeakRvwmoLin.grfGmo G hppo hlv e a i v w hg hwa,
      (gwriteAtInv G (i + 1) w (linNd G hwf) hwa).2⟩

/-! # 4. THE SIX OBLIGATIONS -/

theorem gxLblRowLookup (G : Gexec) (e : Geid) (l : Lbl) :
    gxLbl G e = some l →
    G.gxProg[e.1]? = some (WeakRvwmoLin.grow G e.1) ∧ (WeakRvwmoLin.grow G e.1)[e.2]? = some l := by
  intro hl
  have hb : (gxLbl G e).isSome := by rw [hl]; rfl
  obtain ⟨hi, _⟩ := (gxLblBounds G e).1 hb
  have hp := WeakRvwmoLin.growLookup G e.1 hi
  refine ⟨hp, ?_⟩
  unfold gxLbl at hl
  rw [hp] at hl
  exact hl

/-! ## 4.1 `candShape` — `gwf`'s shape clause, verbatim -/

theorem linShape (G : Gexec) (hwf : gwf G) : candShape (linCand G) := by
  intro k s hs
  obtain ⟨e, hk, rfl⟩ := linTrLookupInv G k s hs
  obtain ⟨l, hl⟩ := someOfIsSome (glinLookupLbl G hwf k e hk)
  have hgl : (glinStep G e).esLb = l := by simp [glinStep, glbl, hl]
  obtain ⟨hp, hr⟩ := gxLblRowLookup G e l hl
  have := hwf.2.2 e.1 (WeakRvwmoLin.grow G e.1) e.2 l hp hr
  rw [hgl]
  exact this

/-! ## 4.2 `candValues` — (P2)+(P3) put the source at log position `t` -/

theorem linValues (G : Gexec) (hwf : gwf G) (hppo : gppoGmo G) (hlv : gloadValue G)
    (h14 : grule14 G) : candValues (linCand G) := by
  intro k s base ts vs hs hrd j t v hj hv
  obtain ⟨e, hk, rfl⟩ := linTrLookupInv G k s hs
  have hg : greadsByte G e (accAddr base j) t v :=
    ⟨glbl G e, base, ts, vs, j, linLbl G hwf k e hk, hrd, hj, hv, rfl⟩
  show logByte G.gxImg (cdLog (linCand G) k) t (accAddr base j) = some v
  cases t with
  | zero => exact (hlv e (accAddr base j) 0 v hg).1
  | succ i =>
    obtain ⟨w, hwa, hwb, _⟩ := (hlv e (accAddr base j) (i + 1) v hg).1
    have hle := linReadTsLe G hwf hppo hlv h14 k e (accAddr base j) (i + 1) v hk hg
    have hkl : k ≤ (linCand G).cdTr.length := by have := lookup_lt_Some hs; omega
    obtain ⟨rest, hrest⟩ := cdLogSplit (linCand G) k (linCand G).cdTr.length hkl
    rw [← logByteApp G.gxImg (cdLog (linCand G) k) rest (i + 1) (accAddr base j) hle, ← hrest,
      linFullLog G hwf]
    exact linLogByteFinal G (i + 1) w (accAddr base j) v hwa hwb

/-! ## 4.3 `axAtomicity` — `gatomicity` through (P2) -/

theorem linAtomicity (G : Gexec) (hwf : gwf G) (hat : gatomicity G) :
    axAtomicity (candExec (linCand G)) := by
  intro kr a w0 w hW hrf hw hgt hlt
  cases w with
  | ev_init => simp [evTs] at hgt
  | ev_at kw =>
    obtain ⟨sr, hsr, _⟩ := id hW
    obtain ⟨er, hkr, _⟩ := linTrLookupInv G kr sr hsr
    obtain ⟨sw, hsw, _⟩ := hw.1
    obtain ⟨ew, hkw, _⟩ := linTrLookupInv G kw sw hsw
    obtain ⟨v', hwb⟩ := (linWrB G hwf kw ew a hkw).1 hw
    have hwe := gwritesByteIsw G ew a v' hwb
    obtain ⟨_, k, t0, v0, heq, hr, hts0⟩ := hrf
    have hkk : k = kr := by injection heq with h; exact h.symm
    rw [hkk] at hr
    have hgr := (linReadsAt G hwf kr er a t0 v0 hkr).1 hr
    have hwr := (linIsW G hwf kr er hkr).1 hW
    rw [linTsWrite G hwf kw ew hkw hwe] at hgt hlt
    rw [linTsWrite G hwf kr er hkr hwr] at hlt
    rw [hts0] at hgt
    exact hat er a t0 v0 hgr
      (WeakRvwmoLin.gisWGlblIs G er (glinLookupLbl G hwf kr er hkr) hwr) ew v' hwb ⟨hgt, hlt⟩

/-! ## 4.4 `axCoherence` — ppo 1–3 plus the load-value axiom's co-maximality -/

theorem linEtsWr (G : Gexec) (hwf : gwf G) (k : Nat) (e : Geid) (a : Int) :
    (glinEids G)[k]? = some e → wrB (candExec (linCand G)) a (ev_at k) →
    ets (candExec (linCand G)) a (ev_at k) = gwix G e := by
  intro hk hw
  rw [etsWr _ a _ hw]
  exact linTsWrite G hwf k e hk ((linIsW G hwf k e hk).1 hw.1)

theorem linEtsRd (G : Gexec) (hwf : gwf G) (k : Nat) (e : Geid) (a : Int) (t : Nat)
    (v : BitVec 8) :
    (glinEids G)[k]? = some e → ¬ wrB (candExec (linCand G)) a (ev_at k) →
    greadsByte G e a t v → ets (candExec (linCand G)) a (ev_at k) = t := by
  intro hk hn hg
  exact etsRd _ a k t v hn ((linReadsAt G hwf k e a t v hk).2 hg)

theorem linNwrRead (G : Gexec) (hwf : gwf G) (k : Nat) (e : Geid) (a : Int) :
    (glinEids G)[k]? = some e → ¬ wrB (candExec (linCand G)) a (ev_at k) →
    gaccesses G e a → ∃ t v, greadsByte G e a t v := by
  intro hk hn hacc
  rcases hacc with hw | hr
  · exact absurd ((linWrB G hwf k e a hk).2 hw) hn
  · exact hr

/-- THE COHERENCE STEP: same-byte program order does not lower the byte's
timestamp.  Every arm is `gvisible` arithmetic. -/
theorem linPolocEts (G : Gexec) (hwf : gwf G) (hppo : gppoGmo G) (hlv : gloadValue G)
    (k1 k2 : Nat) (e1 e2 : Geid) (a : Int) :
    (glinEids G)[k1]? = some e1 → (glinEids G)[k2]? = some e2 →
    WeakRvwmoGraph.gpo G e1 e2 → gmoLt G e1 e2 → gaccesses G e1 a → gaccesses G e2 a →
    ets (candExec (linCand G)) a (ev_at k1) ≤ ets (candExec (linCand G)) a (ev_at k2) := by
  intro h1 h2 _ hmo ha1 ha2
  have hnd := linNd G hwf
  rcases wrBDec (candExec (linCand G)) a (ev_at k2) with hw2 | hn2
  · rw [linEtsWr G hwf k2 e2 a h2 hw2]
    obtain ⟨v2, hwb2⟩ := (linWrB G hwf k2 e2 a h2).1 hw2
    have he2 := gwritesByteGw G hwf e2 a v2 hwb2
    rcases wrBDec (candExec (linCand G)) a (ev_at k1) with hw1 | hn1
    · rw [linEtsWr G hwf k1 e1 a h1 hw1]
      obtain ⟨v1, hwb1⟩ := (linWrB G hwf k1 e1 a h1).1 hw1
      exact Nat.le_of_lt ((gwixGposLt G e1 e2 hnd (gwritesByteGw G hwf e1 a v1 hwb1) he2).2
        hmo.2.2)
    · obtain ⟨t1, v1, hg1⟩ := linNwrRead G hwf k1 e1 a h1 hn1 ha1
      rw [linEtsRd G hwf k1 e1 a t1 v1 h1 hn1 hg1]
      cases t1 with
      | zero => omega
      | succ i1 =>
        obtain ⟨w0, _, hwb, hmo0, hwix⟩ :=
          linSrcGmo G hwf hppo hlv e1 a (i1 + 1) v1 hg1 (by omega)
        rw [← hwix]
        exact Nat.le_of_lt ((gwixGposLt G w0 e2 hnd (gwritesByteGw G hwf w0 a v1 hwb) he2).2
          (gmoLtTrans G w0 e1 e2 hmo0 hmo).2.2)
  · obtain ⟨t2, v2, hg2⟩ := linNwrRead G hwf k2 e2 a h2 hn2 ha2
    rw [linEtsRd G hwf k2 e2 a t2 v2 h2 hn2 hg2]
    rcases wrBDec (candExec (linCand G)) a (ev_at k1) with hw1 | hn1
    · rw [linEtsWr G hwf k1 e1 a h1 hw1]
      obtain ⟨v1, hwb1⟩ := (linWrB G hwf k1 e1 a h1).1 hw1
      exact gcomax G hlv e2 a t2 v2 e1 v1 hg2 hwb1 (Or.inl hmo)
    · obtain ⟨t1, v1, hg1⟩ := linNwrRead G hwf k1 e1 a h1 hn1 ha1
      rw [linEtsRd G hwf k1 e1 a t1 v1 h1 hn1 hg1]
      cases t1 with
      | zero => omega
      | succ i1 =>
        obtain ⟨w0, _, hwb, hmo0, hwix⟩ :=
          linSrcGmo G hwf hppo hlv e1 a (i1 + 1) v1 hg1 (by omega)
        rw [← hwix]
        exact gcomax G hlv e2 a t2 v2 w0 v1 hg2 hwb (Or.inl (gmoLtTrans G w0 e1 e2 hmo0 hmo))

theorem linReadTsLe' (G : Gexec) (hwf : gwf G) (hppo : gppoGmo G) (hlv : gloadValue G)
    (h14 : grule14 G) (k : Nat) (a : Int) (t : Nat) (v : BitVec 8) :
    readsAt (candExec (linCand G)) k a t v → t ≤ (cdLog (linCand G) k).length := by
  intro hr
  obtain ⟨s, _, _, _, _, hs, _⟩ := id hr
  obtain ⟨e, hk, _⟩ := linTrLookupInv G k s hs
  exact linReadTsLe G hwf hppo hlv h14 k e a t v hk ((linReadsAt G hwf k e a t v hk).1 hr)

theorem linCohLexlt (G : Gexec) (hwf : gwf G) (hppo : gppoGmo G) (hlv : gloadValue G)
    (hat : gatomicity G) (h14 : grule14 G) (a : Int) (e1 e2 : Ev) :
    cohRel (candExec (linCand G)) a e1 e2 →
    lexlt (ets (candExec (linCand G)) a e1, evIx e1) (ets (candExec (linCand G)) a e2, evIx e2) := by
  intro h
  unfold lexlt
  rcases h with hpl | hrf | hco | hfr
  · obtain ⟨⟨k1, k2, s1, s2, rfl, rfl, hlt, hs1, hs2, hag⟩, ha1, ha2⟩ := hpl
    obtain ⟨g1, hk1, rfl⟩ := linTrLookupInv G k1 s1 hs1
    obtain ⟨g2, hk2, rfl⟩ := linTrLookupInv G k2 s2 hs2
    have hpo : WeakRvwmoGraph.gpo G g1 g2 :=
      ⟨hag, (glinPoIff G hwf h14 k1 k2 g1 g2 hk1 hk2 hag).1 hlt, glinLookupLbl G hwf k1 g1 hk1,
        glinLookupLbl G hwf k2 g2 hk2⟩
    have hg1 := (linAccB G hwf k1 g1 a hk1).1 ha1
    have hg2 := (linAccB G hwf k2 g2 a hk2).1 ha2
    have hmo : gmoLt G g1 g2 := hppo g1 g2 (Or.inl ⟨hpo, a, hg1, hg2⟩)
    have hle := linPolocEts G hwf hppo hlv k1 k2 g1 g2 a hk1 hk2 hpo hmo hg1 hg2
    simp only [evIx]
    omega
  · have hrf' := hrf
    obtain ⟨hw, k, t, v, rfl, hr, hts⟩ := hrf'
    have hix := candRfIx (linCand G) a e1 k (linValues G hwf hppo hlv h14) hrf
    rw [etsWr _ a e1 hw, hts]
    rcases wrBDec (candExec (linCand G)) a (ev_at k) with hw2 | hn2
    · rw [etsWr _ a _ hw2, evTsAt]
      have htl := linReadTsLe' G hwf hppo hlv h14 k a t v hr
      have hkl : k ≤ (linCand G).cdTr.length := by
        obtain ⟨s, _, _, _, _, hs, _⟩ := hr
        rw [candExTr] at hs
        exact Nat.le_of_lt (lookup_lt_Some hs)
      rw [candElog (linCand G) k hkl]
      left
      show t < _
      omega
    · rw [etsRd _ a k t v hn2 hr]
      right
      exact ⟨rfl, hix⟩
  · obtain ⟨hw1, hw2, hlt⟩ := hco
    rw [etsWr _ a e1 hw1, etsWr _ a e2 hw2]
    exact Or.inl hlt
  · obtain ⟨⟨w0, hrf0, hco⟩, hne⟩ := hfr
    obtain ⟨_, hw2, hlt⟩ := hco
    rw [etsWr _ a e2 hw2]
    obtain ⟨_, kr, t0, v0, rfl, hr, hts0⟩ := hrf0
    rcases wrBDec (candExec (linCand G)) a (ev_at kr) with hw1 | hn1
    · cases e2 with
      | ev_init => simp [evTs] at hlt
      | ev_at kw =>
        obtain ⟨sr, _, _, _, _, hsr, _⟩ := id hr
        obtain ⟨er, hkr, _⟩ := linTrLookupInv G kr sr hsr
        obtain ⟨sw, hsw, _⟩ := hw2.1
        obtain ⟨ew, hkw, _⟩ := linTrLookupInv G kw sw hsw
        obtain ⟨v', hwb⟩ := (linWrB G hwf kw ew a hkw).1 hw2
        have hwe := gwritesByteIsw G ew a v' hwb
        have hwr := (linIsW G hwf kr er hkr).1 hw1.1
        have hgr := (linReadsAt G hwf kr er a t0 v0 hkr).1 hr
        have hlt0 : t0 < gwix G ew := by
          rw [← linTsWrite G hwf kw ew hkw hwe, ← hts0]; exact hlt
        rw [etsWr _ a _ hw1, linTsWrite G hwf kr er hkr hwr, linTsWrite G hwf kw ew hkw hwe]
        left
        have hle : ¬ gwix G ew < gwix G er := fun hc =>
          hat er a t0 v0 hgr (WeakRvwmoLin.gisWGlblIs G er (glinLookupLbl G hwf kr er hkr) hwr)
            ew v' hwb ⟨hlt0, hc⟩
        have hnee : er ≠ ew := by
          intro hc
          have hkk : kr = kw := NoDup_lookup (glinNodup G) hkr (by rw [hc]; exact hkw)
          exact hne (by rw [hkk])
        have hwix : gwix G er ≠ gwix G ew := fun hc =>
          hnee (gwixInj G er ew (linNd G hwf)
            (gisWGwrites G er hwf (glinLookupLbl G hwf kr er hkr) hwr)
            (gwritesByteGw G hwf ew a v' hwb) hc)
        show gwix G er < gwix G ew
        omega
    · rw [etsRd _ a kr t0 v0 hn1 hr]
      left
      show t0 < evTs (candExec (linCand G)) e2
      omega

theorem linCoherence (G : Gexec) (hwf : gwf G) (hppo : gppoGmo G) (hlv : gloadValue G)
    (hat : gatomicity G) (h14 : grule14 G) : axCoherence (candExec (linCand G)) :=
  fun a => tcLexlt _ (fun e => (ets (candExec (linCand G)) a e, evIx e))
    (fun x y h => linCohLexlt G hwf hppo hlv hat h14 a x y h)

/-! ## 4.5 `axOrd` / `axRelOrd` — the ordering edges map to `gppo` -/

theorem linFenceBetween (G : Gexec) (hwf : gwf G) (h14 : grule14 G) (k1 k2 : Nat) (e1 e2 : Geid)
    (pr pw sr sw : Bool) :
    (glinEids G)[k1]? = some e1 → (glinEids G)[k2]? = some e2 →
    fenceBetween (candExec (linCand G)) k1 k2 pr pw sr sw →
    gfenceBetween G e1 e2 pr pw sr sw := by
  rintro h1 h2 ⟨kf, sf, s1, s2, hlt1, hlt2, hs1, hsf, hs2, hag1, hag2, hlf⟩
  have e1' := linTrEq G k1 e1 s1 h1 hs1
  have e2' := linTrEq G k2 e2 s2 h2 hs2
  subst e1' e2'
  obtain ⟨qf, hqf, rfl⟩ := linTrLookupInv G kf sf hsf
  have hag1' : e1.1 = qf.1 := hag1
  have hag2' : qf.1 = e2.1 := hag2
  have hag : e1.1 = e2.1 := hag1'.trans hag2'
  refine ⟨hag, (glinPoIff G hwf h14 k1 k2 e1 e2 h1 h2 hag).1 (by omega), qf.2,
    (glinPoIff G hwf h14 k1 kf e1 qf h1 hqf hag1').1 hlt1,
    (glinPoIff G hwf h14 kf k2 qf e2 hqf h2 hag2').1 hlt2, ?_⟩
  have heq : (e1.1, qf.2) = qf := by rw [hag1']
  rw [heq, linLbl G hwf kf qf hqf]
  exact congrArg some hlf

/-- `acqPo` (like the graph's own rule-5 arm before it was narrowed) does not
pin its SUCCESSOR to a memory access, so the `gmem` side condition is a premise
here; both call sites have it, the successor being the read the `fr` edge
starts at. -/
theorem linAcqPoGmo (G : Gexec) (hwf : gwf G) (hppo : gppoGmo G) (h14 : grule14 G)
    (k1 k2 : Nat) (g1 g2 : Geid) :
    (glinEids G)[k1]? = some g1 → (glinEids G)[k2]? = some g2 → gmem G g2 →
    acqPo (candExec (linCand G)) (ev_at k1) (ev_at k2) → gmoLt G g1 g2 := by
  rintro h1 h2 hmem2 ⟨n1, n2, s1, s2, ha, hb, hlt, hs1, hs2, hag, hisr, haq⟩
  have ha' : n1 = k1 := by injection ha with h; exact h.symm
  have hb' : n2 = k2 := by injection hb with h; exact h.symm
  rw [ha'] at hs1 hlt
  rw [hb'] at hs2 hlt
  have e1' := linTrEq G k1 g1 s1 h1 hs1
  have e2' := linTrEq G k2 g2 s2 h2 hs2
  subst e1' e2'
  exact hppo g1 g2 (Or.inr (Or.inr (Or.inl
    ⟨⟨hag, (glinPoIff G hwf h14 k1 k2 g1 g2 h1 h2 hag).1 hlt, glinLookupLbl G hwf k1 g1 h1,
        glinLookupLbl G hwf k2 g2 h2⟩,
      ⟨glbl G g1, linLbl G hwf k1 g1 h1, hisr⟩, ⟨glbl G g1, linLbl G hwf k1 g1 h1, haq⟩,
      hmem2⟩)))

theorem linRelAcqGmo (G : Gexec) (hwf : gwf G) (hppo : gppoGmo G) (h14 : grule14 G)
    (k1 k2 : Nat) (g1 g2 : Geid) :
    (glinEids G)[k1]? = some g1 → (glinEids G)[k2]? = some g2 →
    relAcqPo (candExec (linCand G)) (ev_at k1) (ev_at k2) → gmoLt G g1 g2 := by
  rintro h1 h2 ⟨n1, n2, s1, s2, ha, hb, hlt, hs1, hs2, hag, hw1, hrl1, hr2, haq2⟩
  have ha' : n1 = k1 := by injection ha with h; exact h.symm
  have hb' : n2 = k2 := by injection hb with h; exact h.symm
  rw [ha'] at hs1 hlt
  rw [hb'] at hs2 hlt
  have e1' := linTrEq G k1 g1 s1 h1 hs1
  have e2' := linTrEq G k2 g2 s2 h2 hs2
  subst e1' e2'
  exact hppo g1 g2 (Or.inr (Or.inr (Or.inr (grelAcqGrcsc G g1 g2
    ⟨⟨hag, (glinPoIff G hwf h14 k1 k2 g1 g2 h1 h2 hag).1 hlt, glinLookupLbl G hwf k1 g1 h1,
        glinLookupLbl G hwf k2 g2 h2⟩,
      ⟨glbl G g1, linLbl G hwf k1 g1 h1, hw1⟩, ⟨glbl G g1, linLbl G hwf k1 g1 h1, hrl1⟩,
      ⟨glbl G g2, linLbl G hwf k2 g2 h2, hr2⟩, ⟨glbl G g2, linLbl G hwf k2 g2 h2, haq2⟩⟩))))

theorem linFrBound (G : Gexec) (hwf : gwf G) (hlv : gloadValue G) (k2 : Nat) (e2 : Geid)
    (a : Int) (w : Ev) :
    (glinEids G)[k2]? = some e2 →
    frB (candExec (linCand G)) a (ev_at k2) w →
    ∃ kw ew, w = ev_at kw ∧ (glinEids G)[kw]? = some ew ∧ ew ∈ gwrites G ∧
      evTs (candExec (linCand G)) w = gwix G ew ∧ gpos G e2 ≤ gpos G ew := by
  rintro hk2 ⟨⟨w0, hrf, hco⟩, _⟩
  obtain ⟨_, hw, hlt⟩ := hco
  obtain ⟨_, k, t0, v0, heq, hr, hts0⟩ := hrf
  have hkk : k = k2 := by injection heq with h; exact h.symm
  rw [hkk] at hr
  cases w with
  | ev_init => simp [evTs] at hlt
  | ev_at kw =>
    obtain ⟨sw, hsw, _⟩ := hw.1
    obtain ⟨ew, hkw, _⟩ := linTrLookupInv G kw sw hsw
    obtain ⟨v', hwb⟩ := (linWrB G hwf kw ew a hkw).1 hw
    have hwe := gwritesByteIsw G ew a v' hwb
    have hgr := (linReadsAt G hwf k2 e2 a t0 v0 hk2).1 hr
    refine ⟨kw, ew, rfl, hkw, gwritesByteGw G hwf ew a v' hwb, linTsWrite G hwf kw ew hkw hwe, ?_⟩
    apply gfrGe G hwf hlv e2 a t0 v0 ew v' hgr hwb
    rw [← linTsWrite G hwf kw ew hkw hwe, ← hts0]
    exact hlt

theorem linPubBound (G : Gexec) (hwf : gwf G) (hppo : gppoGmo G) (hlv : gloadValue G)
    (k1 : Nat) (e1 : Geid) (t : Nat) :
    (glinEids G)[k1]? = some e1 →
    (pubW (candExec (linCand G)) (ev_at k1) t ∨ pubR (candExec (linCand G)) (ev_at k1) t) →
    t = 0 ∨ ∃ u, u ∈ gwrites G ∧ gwix G u = t ∧ gpos G u ≤ gpos G e1 := by
  rintro hk (hpw | hpr)
  · right
    obtain ⟨hW, _, hts⟩ := hpw
    have hw := (linIsW G hwf k1 e1 hk).1 hW
    refine ⟨e1, gisWGwrites G e1 hwf (glinLookupLbl G hwf k1 e1 hk) hw, ?_, Nat.le_refl _⟩
    rw [hts]
    exact (linTsWrite G hwf k1 e1 hk hw).symm
  · obtain ⟨k, s, a, v, heq, _, hr, _⟩ := hpr
    have hkk : k = k1 := by injection heq with h; exact h.symm
    rw [hkk] at hr
    cases t with
    | zero => left; rfl
    | succ i =>
      right
      have hg := (linReadsAt G hwf k1 e1 a (i + 1) v hk).1 hr
      obtain ⟨u, _, hwb, hmo, hwix⟩ := linSrcGmo G hwf hppo hlv e1 a (i + 1) v hg (by omega)
      exact ⟨u, gwritesByteGw G hwf u a v hwb, hwix, Nat.le_of_lt hmo.2.2⟩

theorem linOrdCore (G : Gexec) (hwf : gwf G) (hppo : gppoGmo G) (hlv : gloadValue G)
    (k1 k2 : Nat) (e1 e2 : Geid) (a : Int) (w : Ev) (t : Nat) :
    (glinEids G)[k1]? = some e1 → (glinEids G)[k2]? = some e2 →
    gmoLt G e1 e2 →
    (pubW (candExec (linCand G)) (ev_at k1) t ∨ pubR (candExec (linCand G)) (ev_at k1) t) →
    frB (candExec (linCand G)) a (ev_at k2) w →
    t < evTs (candExec (linCand G)) w := by
  intro h1 h2 hmo hpub hfr
  obtain ⟨kw, ew, rfl, _, hew, hts, hge⟩ := linFrBound G hwf hlv k2 e2 a w h2 hfr
  rw [hts]
  rcases linPubBound G hwf hppo hlv k1 e1 t h1 hpub with rfl | ⟨u, hu, hux, hup⟩
  · exact WeakRvwmoGraph.gwixPos G ew hew
  · rw [← hux]
    exact (gwixGposLt G u ew (linNd G hwf) hu hew).2 (by have := hmo.2.2; omega)

theorem linReadAt2 (G : Gexec) (hwf : gwf G) (k2 : Nat) (s2 : Estep) (a : Int) (w : Ev) :
    (candExec (linCand G)).exTr[k2]? = some s2 →
    frB (candExec (linCand G)) a (ev_at k2) w →
    ∃ e2, (glinEids G)[k2]? = some e2 ∧ glblIs G e2 lbIsR := by
  intro hs2 hfr
  obtain ⟨e2, hk2, _⟩ := linTrLookupInv G k2 s2 hs2
  refine ⟨e2, hk2, ?_⟩
  obtain ⟨⟨w0, ⟨_, k, t0, v0, heq, hr, _⟩, _⟩, _⟩ := hfr
  have hkk : k = k2 := by injection heq with h; exact h.symm
  rw [hkk] at hr
  exact greadsByteIsR G e2 a t0 v0 ((linReadsAt G hwf k2 e2 a t0 v0 hk2).1 hr)

theorem linOrd (G : Gexec) (hwf : gwf G) (hppo : gppoGmo G) (hlv : gloadValue G)
    (h14 : grule14 G) : axOrd (candExec (linCand G)) := by
  intro e1 k2 s2 a w t hs2 hcase hfr
  obtain ⟨e2, hk2, hr2⟩ := linReadAt2 G hwf k2 s2 a w hs2 hfr
  rcases hcase with ⟨hord, hpub⟩ | ⟨hord, hpub⟩
  · obtain ⟨k1, k2', pr, sw, rfl, heq2, hfb⟩ := hord
    have hkk : k2' = k2 := by injection heq2 with h; exact h.symm
    rw [hkk] at hfb
    obtain ⟨_, _, s1, _, _, _, hs1, _⟩ := id hfb
    obtain ⟨e1, hk1, _⟩ := linTrLookupInv G k1 s1 hs1
    have hw1 : glblIs G e1 lbIsW :=
      WeakRvwmoLin.gisWGlblIs G e1 (glinLookupLbl G hwf k1 e1 hk1) ((linIsW G hwf k1 e1 hk1).1 hpub.1)
    have hmo : gmoLt G e1 e2 := hppo e1 e2 (Or.inr (Or.inl ⟨pr, true, true, sw,
      linFenceBetween G hwf h14 k1 k2 e1 e2 pr true true sw hk1 hk2 hfb,
      Or.inr ⟨hw1, rfl⟩, Or.inl ⟨hr2, rfl⟩⟩))
    exact linOrdCore G hwf hppo hlv k1 k2 e1 e2 a w t hk1 hk2 hmo (Or.inl hpub) hfr
  · obtain ⟨k1, s1, a1, v1, rfl, hs1, hr1, _⟩ := id hpub
    obtain ⟨e1, hk1, _⟩ := linTrLookupInv G k1 s1 hs1
    have hisr1 : glblIs G e1 lbIsR :=
      greadsByteIsR G e1 a1 t v1 ((linReadsAt G hwf k1 e1 a1 t v1 hk1).1 hr1)
    have hmo : gmoLt G e1 e2 := by
      rcases hord with ⟨n1, n2, pw, sw, heq1, heq3, hfb⟩ | hacq
      · have h1' : n1 = k1 := by injection heq1 with h; exact h.symm
        have h3' : n2 = k2 := by injection heq3 with h; exact h.symm
        rw [h1', h3'] at hfb
        exact hppo e1 e2 (Or.inr (Or.inl ⟨true, pw, true, sw,
          linFenceBetween G hwf h14 k1 k2 e1 e2 true pw true sw hk1 hk2 hfb,
          Or.inl ⟨hisr1, rfl⟩, Or.inl ⟨hr2, rfl⟩⟩))
      · exact linAcqPoGmo G hwf hppo h14 k1 k2 e1 e2 hk1 hk2
          (WeakRvwmoGraph.glblIsRGmem G e2 hr2) hacq
    exact linOrdCore G hwf hppo hlv k1 k2 e1 e2 a w t hk1 hk2 hmo (Or.inr hpub) hfr

theorem linRelOrd (G : Gexec) (hwf : gwf G) (hppo : gppoGmo G) (hlv : gloadValue G)
    (h14 : grule14 G) : axRelOrd (candExec (linCand G)) := by
  intro e1 k2 s2 a w t hs2 hrel hpub hfr
  obtain ⟨e2, hk2, hr2⟩ := linReadAt2 G hwf k2 s2 a w hs2 hfr
  obtain ⟨hW, ⟨k1, rfl⟩, _⟩ := id hpub
  obtain ⟨s1, hs1, _⟩ := id hW
  obtain ⟨e1, hk1, _⟩ := linTrLookupInv G k1 s1 hs1
  have hmo : gmoLt G e1 e2 := by
    rcases hrel with hra | ⟨em, hra, _, hacq⟩
    · exact linRelAcqGmo G hwf hppo h14 k1 k2 e1 e2 hk1 hk2 hra
    · obtain ⟨n1, _, sm, _, rfl, _, _, hsm, _⟩ := id hacq
      obtain ⟨em, hkm, _⟩ := linTrLookupInv G n1 sm hsm
      exact gmoLtTrans G e1 em e2 (linRelAcqGmo G hwf hppo h14 k1 n1 e1 em hk1 hkm hra)
        (linAcqPoGmo G hwf hppo h14 n1 k2 em e2 hkm hk2 (WeakRvwmoGraph.glblIsRGmem G e2 hr2) hacq)
  exact linOrdCore G hwf hppo hlv k1 k2 e1 e2 a w t hk1 hk2 hmo (Or.inl hpub) hfr

/-! ## 4.6 The per-agent program rows, and the whole log -/

theorem filterFmapGlin (G : Gexec) (l : List Geid) (i : Nat) :
    (l.map (glinStep G)).filter (fun s : Estep => decide (s.esAg = i)) =
    (l.filter (fun e : Geid => decide (e.1 = i))).map (glinStep G) := by
  rw [List.filter_map]
  rfl

theorem linProg (G : Gexec) (hwf : gwf G) (h14 : grule14 G) (i : Nat) :
    ((linCand G).cdTr.filter (fun s : Estep => decide (s.esAg = i))).map (fun s => s.esLb) =
    WeakRvwmoLin.grow G i := by
  show (((glinEids G).map (glinStep G)).filter (fun s : Estep => decide (s.esAg = i))).map
    (fun s => s.esLb) = _
  rw [filterFmapGlin, glinHart G hwf h14 i, List.map_map]
  unfold gevsHart
  rw [List.map_map]
  apply List.ext_getElem?
  intro k
  rw [list_lookup_fmap]
  by_cases hk : k < (WeakRvwmoLin.grow G i).length
  · rw [lookup_seq_lt hk]
    have hi : i < G.gxProg.length := by
      cases hp : G.gxProg[i]? with
      | some p => exact lookup_lt_Some hp
      | none => unfold WeakRvwmoLin.grow at hk; rw [hp] at hk; simp at hk
    have hl : gxLbl G (i, k) = (WeakRvwmoLin.grow G i)[k]? := by
      unfold gxLbl
      rw [WeakRvwmoLin.growLookup G i hi]
      rfl
    obtain ⟨l, hlk⟩ := someOfIsSome (lookup_lt_is_Some_2 hk)
    rw [hlk]
    simp only [Option.map_some, Function.comp_apply, glinStep, glbl, Nat.zero_add, hl, hlk,
      Option.getD_some]
  · rw [lookup_seq_ge (j := 0) (n := (WeakRvwmoLin.grow G i).length) (i := k) (by omega),
      lookup_ge_None_2 (l := WeakRvwmoLin.grow G i) (i := k) (by omega)]
    rfl

/-! ## 4.7 The section's theorem -/

theorem linSrvwmo (G : Gexec) (hwf : gwf G) (hppo : gppoGmo G) (hlv : gloadValue G)
    (hat : gatomicity G) (h14 : grule14 G) : srvwmoConsistent (linCand G) := by
  have hval := linValues G hwf hppo hlv h14
  have hwfe := (promiseFreeCompleteLocal (linCand G) (linShape G hwf) hval
    (candRfTotal _ hval) (linCoherence G hwf hppo hlv hat h14) (linOrd G hwf hppo hlv h14)
    (linRelOrd G hwf hppo hlv h14) (linAtomicity G hwf hat)).1
  exact ⟨linShape G hwf, hval, promiseFreeSound _ hwfe, soundRelOrd _ hwfe,
    promiseFreeObAcyclic _ hwfe⟩

/-! # 5. THE RULE-14 LINEARIZATION -/

theorem rule14Linearization (G : Gexec) :
    rvwmoMinusConsistent G → grule14 G →
    ∃ c : Cand,
      srvwmoConsistent c ∧
      c.cdImg = G.gxImg ∧
      (∀ i, (c.cdTr.filter (fun s : Estep => decide (s.esAg = i))).map (fun s => s.esLb) =
        (G.gxProg[i]?).getD []) ∧
      cdLog c c.cdTr.length = (gwrites G).filterMap (WeakRvwmoLin.gmsg G) := by
  rintro ⟨hwf, hppo, hlv, hat⟩ h14
  exact ⟨linCand G, linSrvwmo G hwf hppo hlv hat h14, rfl, fun i => linProg G hwf h14 i,
    linFullLog G hwf⟩

/-! # 6. W13 (L): THE ANCHORED RANK TRACE (Lean-only; plan §C W13 (L), [W2s], G3-Q (a″))

The rank trace above anchors every event at its po-next WRITE, so it respects gmo between two
writes and nothing else.  W13 (L) makes I/O events (and, under G3-Q (a″), disk-row reads)
ANCHORS too: `gnxa G anc e` is the po-next event at-or-after `e` of an arbitrary ANCHOR CLASS
`anc`, ranked by its index `gaix` in the anchor sub-order `gancs G anc` (gmo filtered by `anc`).
For `anc = gisW G` this IS the construction above, definitionally (`glinEidsAW`, `linCandAW`), so
the old trace is one instance.  The class is admissible (`ancOk`) when anchors are memory events,
every write is an anchor, and ANCHOR-14 holds: a memory event po-before an anchor is gmo-before
it (`granc14`; rule 14 is the instance `anc = gisW`).  Under `ancOk` the anchored trace keeps the
per-hart po order, emits the writes in gmo order (so the log is unchanged), and respects gmo
between an anchor and EVERY later event (`glinAGmoAnc`) — in particular, the anchors come out in
gmo order (`glinAAncIff`). -/

/-- The po-FIRST anchor at-or-after `e`, in `e`'s own row. -/
def gnxa (G : Gexec) (anc : Geid → Bool) (e : Geid) : Option Geid :=
  (listFind (fun k => anc (e.1, k))
    (List.range' e.2 ((WeakRvwmoLin.grow G e.1).length - e.2))).map
    (fun ik : Nat × Nat => (e.1, ik.2))

/-- The ANCHOR SUB-ORDER: gmo filtered by the class (for `gisW G` it is `gwrites G`). -/
def gancs (G : Gexec) (anc : Geid → Bool) : List Geid := G.gxGmo.filter anc

/-- The (1-based) anchor index (for `gisW G` it is `gwix G`). -/
def gaix (G : Gexec) (anc : Geid → Bool) (e : Geid) : Nat :=
  match listFind (fun e' => decide (e' = e)) (gancs G anc) with
  | some (i, _) => i + 1
  | none => 0

/-- THE ANCHORED RANK: `gaix` of the next anchor, or a past-the-end slot per row. -/
def grankA (G : Gexec) (anc : Geid → Bool) (e : Geid) : Nat :=
  match gnxa G anc e with
  | some a => gaix G anc a
  | none => (gancs G anc).length + 1 + e.1

def grankBoundA (G : Gexec) (anc : Geid → Bool) : Nat :=
  (gancs G anc).length + 1 + G.gxProg.length

def glinEidsA (G : Gexec) (anc : Geid → Bool) : List Geid :=
  rblocks (grankA G anc) (gevs G) (grankBoundA G anc)

def linCandA (G : Gexec) (anc : Geid → Bool) : Cand :=
  ⟨G.gxImg, (glinEidsA G anc).map (glinStep G)⟩

def linNwA (G : Gexec) (anc : Geid → Bool) (k : Nat) : Nat :=
  (((glinEidsA G anc).take k).filter (gisW G)).length

/-- ANCHOR-14: a memory event po-before an anchor is gmo-before it. -/
def granc14 (G : Gexec) (anc : Geid → Bool) : Prop :=
  ∀ e a, WeakRvwmoGraph.gpo G e a → gmem G e → anc a = true → gmoLt G e a

/-- An ADMISSIBLE anchor class. -/
def ancOk (G : Gexec) (anc : Geid → Bool) : Prop :=
  (∀ e, anc e = true → gmem G e) ∧ (∀ e, gisW G e = true → anc e = true) ∧ granc14 G anc

/-! ## 6.1 The write instance IS the rank trace above -/

theorem glinEidsAW (G : Gexec) : glinEidsA G (gisW G) = glinEids G := rfl

theorem linCandAW (G : Gexec) : linCandA G (gisW G) = linCand G := rfl

theorem linNwAW (G : Gexec) (k : Nat) : linNwA G (gisW G) k = linNw G k := rfl

theorem ancOkW (G : Gexec) (h14 : grule14 G) : ancOk G (gisW G) := by
  refine ⟨fun e he => ?_, fun _ h => h, fun e a hpo hm ha => ?_⟩
  · have hs : (gxLbl G e).isSome := by
      unfold gisW at he; cases h : gxLbl G e <;> simp_all
    exact WeakRvwmoLin.gisWGmem G e hs he
  · exact h14 e a hpo hm (WeakRvwmoLin.gisWGlblIs G a hpo.2.2.2 ha)

/-! ## 6.2 `gnxa`: the next anchor -/

theorem gnxaSome (G : Gexec) (anc : Geid → Bool) (i k : Nat) (a : Geid) :
    gnxa G anc (i, k) = some a →
    ∃ m, a = (i, m) ∧ k ≤ m ∧ m < (WeakRvwmoLin.grow G i).length ∧
      anc (i, m) = true ∧
      (∀ k', k ≤ k' → k' < m → anc (i, k') = false) := by
  unfold gnxa
  simp only
  cases hf : listFind (fun k' => anc (i, k'))
      (List.range' k ((WeakRvwmoLin.grow G i).length - k)) with
  | none => simp
  | some q =>
    obtain ⟨n, j⟩ := q
    intro h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨hn, hw, hmin⟩ := list_find_Some.1 hf
    obtain ⟨rfl, hlt⟩ := lookup_seq.1 hn
    refine ⟨k + n, rfl, by omega, by omega, hw, ?_⟩
    intro k' hk1 hk2
    exact hmin (k' - k) k' (lookup_seq.2 ⟨by omega, by omega⟩) (by omega)

theorem gnxaNone (G : Gexec) (anc : Geid → Bool) (i k k' : Nat) :
    gnxa G anc (i, k) = none → k ≤ k' → k' < (WeakRvwmoLin.grow G i).length →
    anc (i, k') = false := by
  unfold gnxa
  simp only [Option.map_eq_none_iff]
  intro hf hk1 hk2
  exact list_find_None.1 hf k' (elem_of_seq.2 ⟨hk1, by omega⟩)

theorem gnxaSelf (G : Gexec) (anc : Geid → Bool) (i k : Nat) :
    (gxLbl G (i, k)).isSome → anc (i, k) = true → gnxa G anc (i, k) = some (i, k) := by
  intro hl hw
  obtain ⟨hi, hk⟩ := (gxLblBounds G (i, k)).1 hl
  simp only at hi hk
  cases hf : gnxa G anc (i, k) with
  | none => rw [gnxaNone G anc i k k hf (Nat.le_refl _) hk] at hw; cases hw
  | some w =>
    obtain ⟨m, rfl, hkm, hm, hwm, hmin⟩ := gnxaSome G anc i k w hf
    by_cases hkm' : k = m
    · subst hkm'; rfl
    · rw [hmin k (Nat.le_refl _) (by omega)] at hw; cases hw

/-! ## 6.3 The anchor sub-order and `gaix` (the `gwrites`/`gwix` facts, for any class) -/

theorem gancsElemOf (G : Gexec) (anc : Geid → Bool) (e : Geid) :
    e ∈ gancs G anc ↔ e ∈ G.gxGmo ∧ anc e = true := by
  unfold gancs
  rw [elem_of_list_filter]
  exact And.comm

theorem gancsNodup (G : Gexec) (anc : Geid → Bool) : G.gxGmo.Nodup → (gancs G anc).Nodup :=
  fun hnd => NoDup_filter hnd

theorem gaixLookup (G : Gexec) (anc : Geid → Bool) (a : Geid) :
    a ∈ gancs G anc → ∃ i, (gancs G anc)[i]? = some a ∧ gaix G anc a = i + 1 := by
  intro he
  unfold gaix
  cases hf : listFind (fun e' => decide (e' = a)) (gancs G anc) with
  | some q =>
    obtain ⟨i, x⟩ := q
    obtain ⟨hi, hx, _⟩ := list_find_Some.1 hf
    have : x = a := of_decide_eq_true hx
    subst this
    exact ⟨i, hi, rfl⟩
  | none =>
    have := list_find_None.1 hf a he
    simp at this

theorem gaixLe (G : Gexec) (anc : Geid → Bool) (a : Geid) :
    a ∈ gancs G anc → gaix G anc a ≤ (gancs G anc).length := by
  intro he
  obtain ⟨i, hi, h⟩ := gaixLookup G anc a he
  have := lookup_lt_Some hi
  omega

theorem gaixInj (G : Gexec) (anc : Geid → Bool) (a1 a2 : Geid) :
    a1 ∈ gancs G anc → a2 ∈ gancs G anc → gaix G anc a1 = gaix G anc a2 → a1 = a2 := by
  intro h1 h2 heq
  obtain ⟨i1, hi1, e1⟩ := gaixLookup G anc a1 h1
  obtain ⟨i2, hi2, e2⟩ := gaixLookup G anc a2 h2
  have : i1 = i2 := by omega
  subst this
  rw [hi1, Option.some.injEq] at hi2
  exact hi2

theorem gancsSorted (G : Gexec) (anc : Geid → Bool) :
    G.gxGmo.Nodup → List.Pairwise (fun x y => gpos G x < gpos G y) (gancs G anc) := by
  intro hnd
  apply stronglySortedFilter
  apply stronglySortedLookupIntro
  intro i j x y hi hj hlt
  rw [gposOfLookup G i x hnd hi, gposOfLookup G j y hnd hj]
  exact hlt

/-- Anchor index order IS gmo position order. -/
theorem gaixGposLt (G : Gexec) (anc : Geid → Bool) (a1 a2 : Geid) :
    G.gxGmo.Nodup → a1 ∈ gancs G anc → a2 ∈ gancs G anc →
    (gaix G anc a1 < gaix G anc a2 ↔ gpos G a1 < gpos G a2) := by
  intro hnd h1 h2
  obtain ⟨i1, hi1, e1⟩ := gaixLookup G anc a1 h1
  obtain ⟨i2, hi2, e2⟩ := gaixLookup G anc a2 h2
  have hss := gancsSorted G anc hnd
  constructor
  · intro hlt
    exact stronglySortedLookupElim _ _ i1 i2 a1 a2 hss hi1 hi2 (by omega)
  · intro hlt
    rw [e1, e2]
    by_cases hi : i1 < i2
    · omega
    by_cases heq : i1 = i2
    · subst heq
      rw [hi1, Option.some.injEq] at hi2
      subst hi2
      omega
    exfalso
    have hgt := stronglySortedLookupElim _ _ i2 i1 a2 a1 hss hi2 hi1 (by omega)
    omega

/-- Under `ancOk`, an anchor is a labelled member of the anchor sub-order. -/
theorem gancsOfAnc (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hok : ancOk G anc) (a : Geid) :
    anc a = true → a ∈ gancs G anc :=
  fun ha => (gancsElemOf G anc a).2 ⟨gwfMemGmo G a hwf (hok.1 a ha), ha⟩

theorem ancLbl (G : Gexec) (anc : Geid → Bool) (hok : ancOk G anc) (a : Geid) :
    anc a = true → (gxLbl G a).isSome := by
  intro ha
  obtain ⟨l, hl, -⟩ := hok.1 a ha
  rw [hl]; rfl

/-! ## 6.4 Same-row anchors: position order IS `gaix` order (anchor-14) -/

theorem gsameHartGaix (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hok : ancOk G anc)
    (i k1 k2 : Nat) :
    anc (i, k1) = true → anc (i, k2) = true → k1 < k2 →
    gaix G anc (i, k1) < gaix G anc (i, k2) := by
  intro hw1 hw2 hlt
  have hl1 := ancLbl G anc hok _ hw1
  have hl2 := ancLbl G anc hok _ hw2
  have hmo : gmoLt G (i, k1) (i, k2) :=
    hok.2.2 _ _ ⟨rfl, hlt, hl1, hl2⟩ (hok.1 _ hw1) hw2
  exact (gaixGposLt G anc _ _ (linNd G hwf) (gancsOfAnc G anc hwf hok _ hw1)
    (gancsOfAnc G anc hwf hok _ hw2)).2 hmo.2.2

/-! ## 6.5 The anchored rank: `gaix` on anchors, bounded, monotone in po -/

theorem grankAAnc (G : Gexec) (anc : Geid → Bool) (hok : ancOk G anc) (a : Geid) :
    anc a = true → grankA G anc a = gaix G anc a := by
  intro ha
  obtain ⟨i, k⟩ := a
  unfold grankA
  rw [gnxaSelf G anc i k (ancLbl G anc hok _ ha) ha]

theorem grankALtBound (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hok : ancOk G anc)
    (e : Geid) : (gxLbl G e).isSome → grankA G anc e < grankBoundA G anc := by
  intro hl
  obtain ⟨hi, hk⟩ := (gxLblBounds G e).1 hl
  obtain ⟨i, k⟩ := e
  simp only at hi hk
  unfold grankA grankBoundA
  cases hf : gnxa G anc (i, k) with
  | none => dsimp only; omega
  | some w =>
    obtain ⟨m, rfl, _, _, hw, _⟩ := gnxaSome G anc i k w hf
    have := gaixLe G anc (i, m) (gancsOfAnc G anc hwf hok _ hw)
    dsimp only; omega

theorem grankAMono (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hok : ancOk G anc)
    (i k1 k2 : Nat) :
    k1 ≤ k2 → k2 < (WeakRvwmoLin.grow G i).length →
    grankA G anc (i, k1) ≤ grankA G anc (i, k2) := by
  intro hle hk2
  unfold grankA
  cases h2 : gnxa G anc (i, k2) with
  | some w2 =>
    obtain ⟨m2, rfl, hk2m, hm2, hw2, _⟩ := gnxaSome G anc i k2 w2 h2
    cases h1 : gnxa G anc (i, k1) with
    | none => rw [gnxaNone G anc i k1 m2 h1 (by omega) hm2] at hw2; cases hw2
    | some w1 =>
      obtain ⟨m1, rfl, hk1m, hm1, hw1, hmin1⟩ := gnxaSome G anc i k1 w1 h1
      have hle' : m1 ≤ m2 := by
        by_cases hlt : m2 < m1
        · rw [hmin1 m2 (by omega) hlt] at hw2; cases hw2
        · omega
      dsimp only
      by_cases heq : m1 = m2
      · subst heq; exact Nat.le_refl _
      · exact Nat.le_of_lt (gsameHartGaix G anc hwf hok i m1 m2 hw1 hw2 (by omega))
  | none =>
    cases h1 : gnxa G anc (i, k1) with
    | none => dsimp only; omega
    | some w1 =>
      obtain ⟨m1, rfl, _, _, hw1, _⟩ := gnxaSome G anc i k1 w1 h1
      have := gaixLe G anc (i, m1) (gancsOfAnc G anc hwf hok _ hw1)
      dsimp only; omega

/-! ## 6.6 The anchored trace: NoDup, membership, the order facts -/

theorem glinANodup (G : Gexec) (anc : Geid → Bool) : (glinEidsA G anc).Nodup :=
  rblocksNodup _ _ _ (gevsNodup G)

theorem elemOfGlinA (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hok : ancOk G anc) (e : Geid) :
    e ∈ glinEidsA G anc ↔ (gxLbl G e).isSome := by
  unfold glinEidsA
  rw [elemOfRblocks, elemOfGevs]
  exact ⟨fun h => h.1, fun h => ⟨h, grankALtBound G anc hwf hok e h⟩⟩

theorem glinALookupLbl (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hok : ancOk G anc)
    (k : Nat) (e : Geid) : (glinEidsA G anc)[k]? = some e → (gxLbl G e).isSome :=
  fun h => (elemOfGlinA G anc hwf hok e).1 (elem_of_list_lookup_2 h)

theorem glinAIndex (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hok : ancOk G anc) (e : Geid) :
    (gxLbl G e).isSome → ∃ k : Nat, (glinEidsA G anc)[k]? = some e :=
  fun h => elem_of_list_lookup_1 ((elemOfGlinA G anc hwf hok e).2 h)

theorem glinAPerm (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hok : ancOk G anc) :
    List.Perm (glinEidsA G anc) (gevs G) :=
  rblocksPerm _ _ _ (gevsNodup G)
    (fun x hx => grankALtBound G anc hwf hok x ((elemOfGevs G x).1 hx))

/-- The per-row subsequence of the anchored trace IS the row. -/
theorem glinAHart (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hok : ancOk G anc) (i : Nat) :
    (glinEidsA G anc).filter (fun e : Geid => decide (e.1 = i)) = gevsHart G i := by
  unfold glinEidsA
  rw [rblocksFilter, filterGevsHart]
  by_cases hi : i < G.gxProg.length
  · apply rblocksId (grankA G anc) (fun x y : Geid => x.2 ≤ y.2)
    · exact gevsHartNodup G i
    · apply stronglySortedLookupIntro
      intro a b x y hx hy hab
      obtain ⟨rfl, _⟩ := gevsHartLookupInv G i a x hx
      obtain ⟨rfl, _⟩ := gevsHartLookupInv G i b y hy
      show a ≤ b
      omega
    · intro x hx
      obtain ⟨hx1, hx2⟩ := (elemOfGevsHart G i x).1 hx
      apply grankALtBound G anc hwf hok
      exact (gxLblBounds G x).2 ⟨by rw [hx1]; exact hi, by rw [hx1]; exact hx2⟩
    · intro x y hx hy hrk
      obtain ⟨hx1, hx2⟩ := (elemOfGevsHart G i x).1 hx
      obtain ⟨hy1, hy2⟩ := (elemOfGevsHart G i y).1 hy
      by_cases h : x.2 ≤ y.2
      · exact h
      · exfalso
        obtain ⟨ix, kx⟩ := x
        obtain ⟨iy, ky⟩ := y
        simp only at hx1 hy1 hx2 hy2 h
        rw [hx1] at hrk
        rw [hy1] at hrk
        have := grankAMono G anc hwf hok i ky kx (by omega) hx2
        omega
    · intro x y hx hy h1 h2
      obtain ⟨hx1, _⟩ := (elemOfGevsHart G i x).1 hx
      obtain ⟨hy1, _⟩ := (elemOfGevsHart G i y).1 hy
      exact Prod.ext (hx1.trans hy1.symm) (by omega)
  · rw [gevsHartNil G i hi]
    unfold rblocks
    exact mjoinSeqNone _ _ (fun j _ => rfl)

theorem glinAPoLt (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hok : ancOk G anc)
    (k1 k2 : Nat) (e1 e2 : Geid) :
    (glinEidsA G anc)[k1]? = some e1 → (glinEidsA G anc)[k2]? = some e2 →
    e1.1 = e2.1 → e1.2 < e2.2 → k1 < k2 := by
  intro h1 h2 hag hlt
  have hss := filterSortedPidx (fun e : Geid => decide (e.1 = e1.1)) (glinEidsA G anc)
    (glinANodup G anc)
  rw [glinAHart G anc hwf hok e1.1] at hss
  have hb1 : e1.2 < (WeakRvwmoLin.grow G e1.1).length :=
    ((gxLblBounds G e1).1 (glinALookupLbl G anc hwf hok k1 e1 h1)).2
  have hb2 : e2.2 < (WeakRvwmoLin.grow G e1.1).length := by
    rw [hag]; exact ((gxLblBounds G e2).1 (glinALookupLbl G anc hwf hok k2 e2 h2)).2
  have hg1 : (gevsHart G e1.1)[e1.2]? = some e1 := by rw [gevsHartLookup G e1.1 e1.2 hb1]
  have hg2 : (gevsHart G e1.1)[e2.2]? = some e2 := by rw [gevsHartLookup G e1.1 e2.2 hb2, hag]
  have hp : pidx (glinEidsA G anc) e1 < pidx (glinEidsA G anc) e2 :=
    stronglySortedLookupElim _ _ e1.2 e2.2 e1 e2 hss hg1 hg2 hlt
  rw [pidxOfLookup _ k1 e1 (glinANodup G anc) h1, pidxOfLookup _ k2 e2 (glinANodup G anc) h2] at hp
  exact hp

theorem glinAPoIff (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hok : ancOk G anc)
    (k1 k2 : Nat) (e1 e2 : Geid) :
    (glinEidsA G anc)[k1]? = some e1 → (glinEidsA G anc)[k2]? = some e2 → e1.1 = e2.1 →
    (k1 < k2 ↔ e1.2 < e2.2) := by
  intro h1 h2 hag
  refine ⟨fun hk => ?_, glinAPoLt G anc hwf hok k1 k2 e1 e2 h1 h2 hag⟩
  by_cases hlt : e1.2 < e2.2
  · exact hlt
  · exfalso
    by_cases heq : e1.2 = e2.2
    · have he : e1 = e2 := Prod.ext hag heq
      rw [he] at h1
      have := NoDup_lookup (glinANodup G anc) h1 h2
      omega
    · have := glinAPoLt G anc hwf hok k2 k1 e2 e1 h2 h1 hag.symm (by omega)
      omega

/-- Rank order implies trace order. -/
theorem glinARankLt (G : Gexec) (anc : Geid → Bool) (k1 k2 : Nat) (e1 e2 : Geid) :
    (glinEidsA G anc)[k1]? = some e1 → (glinEidsA G anc)[k2]? = some e2 →
    grankA G anc e1 < grankA G anc e2 → k1 < k2 := by
  intro h1 h2 hlt
  have hss := rblocksRankSorted (grankA G anc) (gevs G) (grankBoundA G anc)
  by_cases hk : k1 < k2
  · exact hk
  · exfalso
    by_cases heq : k1 = k2
    · rw [heq, h2, Option.some.injEq] at h1
      rw [h1] at hlt
      omega
    · have hx : grankA G anc e2 ≤ grankA G anc e1 :=
        stronglySortedLookupElim _ _ k2 k1 e2 e1 hss h2 h1 (by omega)
      omega

/-- THE ANCHOR FACT: an anchor gmo-before an event is EMITTED before it (the next anchor of the
event is gmo-after it by anchor-14, or the event sits in a past-the-end tail). -/
theorem glinAGmoAnc (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hok : ancOk G anc)
    (k ka : Nat) (r a : Geid) :
    (glinEidsA G anc)[k]? = some r → (glinEidsA G anc)[ka]? = some a → anc a = true →
    gmoLt G a r → ka < k := by
  intro hk hka ha hmo
  apply glinARankLt G anc ka k a r hka hk
  rw [grankAAnc G anc hok a ha]
  have hrl := glinALookupLbl G anc hwf hok k r hk
  have haG := gancsOfAnc G anc hwf hok a ha
  obtain ⟨hri, hrk⟩ := (gxLblBounds G r).1 hrl
  obtain ⟨ir, kr⟩ := r
  simp only at hri hrk
  unfold grankA
  cases hf : gnxa G anc (ir, kr) with
  | none => have := gaixLe G anc a haG; dsimp only; omega
  | some w' =>
    obtain ⟨m, rfl, hkm, hm, hwm, _⟩ := gnxaSome G anc ir kr w' hf
    have hlm := glblSome G ir m hri hm
    have hmo' : gmoLt G a (ir, m) := by
      by_cases hkm' : kr = m
      · subst hkm'; exact hmo
      · apply gmoLtTrans G a (ir, kr) (ir, m) hmo
        exact hok.2.2 _ _ ⟨rfl, show kr < m by omega, hrl, hlm⟩
          (gwfGmoMem G (ir, kr) hwf hmo.2.1) hwm
    dsimp only
    exact (gaixGposLt G anc a (ir, m) (linNd G hwf) haG
      (gancsOfAnc G anc hwf hok _ hwm)).2 hmo'.2.2

/-- …so between two anchors, trace order IS gmo order. -/
theorem glinAAncIff (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hok : ancOk G anc)
    (k1 k2 : Nat) (a1 a2 : Geid) :
    (glinEidsA G anc)[k1]? = some a1 → (glinEidsA G anc)[k2]? = some a2 →
    anc a1 = true → anc a2 = true → (k1 < k2 ↔ gmoLt G a1 a2) := by
  intro h1 h2 ha1 ha2
  refine ⟨fun hlt => ?_, glinAGmoAnc G anc hwf hok k2 k1 a2 a1 h2 h1 ha1⟩
  have hm1 := gwfMemGmo G a1 hwf (hok.1 a1 ha1)
  have hm2 := gwfMemGmo G a2 hwf (hok.1 a2 ha2)
  have hne : a1 ≠ a2 := by
    intro heq
    rw [heq] at h1
    have := NoDup_lookup (glinANodup G anc) h1 h2
    omega
  rcases gmoLtTotal G a1 a2 (linNd G hwf) hm1 hm2 hne with h | h
  · exact h
  · have := glinAGmoAnc G anc hwf hok k1 k2 a1 a2 h1 h2 ha2 h
    omega

/-! ## 6.7 The anchored trace's writes ARE `gwrites G` -/

theorem glinAWrites (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hok : ancOk G anc) :
    (glinEidsA G anc).filter (gisW G) = gwrites G := by
  have hnd := linNd G hwf
  have hel : ∀ e, e ∈ (gevs G).filter (gisW G) ↔ e ∈ gwrites G := by
    intro e
    constructor
    · intro he
      obtain ⟨hb, he⟩ := elem_of_list_filter.1 he
      exact gisWGwrites G e hwf ((elemOfGevs G e).1 he) hb
    · intro he
      exact elem_of_list_filter.2 ⟨gwritesIsw G e he, (elemOfGevs G e).2 (gwritesLbl G hwf e he)⟩
  have hwA : ∀ w, w ∈ gwrites G → anc w = true := fun w hw => hok.2.1 w (gwritesIsw G w hw)
  have hrkW : ∀ w, w ∈ gwrites G → grankA G anc w = gaix G anc w :=
    fun w hw => grankAAnc G anc hok w (hwA w hw)
  have hwG : ∀ w, w ∈ gwrites G → w ∈ gancs G anc :=
    fun w hw => (gancsElemOf G anc w).2 ⟨gwritesGmo G w hw, hwA w hw⟩
  unfold glinEidsA
  rw [rblocksFilter]
  have hR : rblocks (grankA G anc) (gwrites G) (grankBoundA G anc) = gwrites G := by
    apply rblocksId (grankA G anc) (fun x y : Geid => gaix G anc x ≤ gaix G anc y)
    · exact gwritesNodup G hnd
    · refine stronglySortedWeaken _ _ _ ?_ (gwritesSorted G hnd)
      intro x y hx hy hxy
      exact Nat.le_of_lt ((gaixGposLt G anc x y hnd (hwG x hx) (hwG y hy)).2 hxy)
    · intro x hx
      exact grankALtBound G anc hwf hok x (gwritesLbl G hwf x hx)
    · intro x y hx hy hrk
      rw [hrkW x hx, hrkW y hy] at hrk
      exact Nat.le_of_lt hrk
    · intro x y hx hy h1 h2
      exact gaixInj G anc x y (hwG x hx) (hwG y hy) (by omega)
  refine Eq.trans ?_ hR
  apply rblocksExt
  intro d
  by_cases hex : ∃ w, w ∈ gwrites G ∧ grankA G anc w = d
  · obtain ⟨w, hw, hwd⟩ := hex
    have huniq : ∀ y, y ∈ gwrites G → decide (grankA G anc y = d) = true → y = w := by
      intro y hy hp
      have := of_decide_eq_true hp
      rw [hrkW y hy] at this
      rw [hrkW w hw] at hwd
      exact gaixInj G anc y w (hwG y hy) (hwG w hw) (by omega)
    have hpw : decide (grankA G anc w = d) = true := decide_eq_true hwd
    rw [filterUnique _ _ w (NoDup_filter (gevsNodup G)) ((hel w).2 hw) hpw
        (fun y hy hp => huniq y ((hel y).1 hy) hp),
      filterUnique _ _ w (gwritesNodup G hnd) hw hpw huniq]
  · have hno : ∀ e, e ∈ gwrites G → ¬ decide (grankA G anc e = d) = true :=
      fun e he heq => hex ⟨e, he, of_decide_eq_true heq⟩
    rw [filterNo _ _ (fun e he => hno e ((hel e).1 he)), filterNo _ _ hno]

/-! ## 6.8 The anchored candidate's trace and log -/

theorem linTrALookup (G : Gexec) (anc : Geid → Bool) (k : Nat) (e : Geid) :
    (glinEidsA G anc)[k]? = some e → (linCandA G anc).cdTr[k]? = some (glinStep G e) := by
  intro h
  show ((glinEidsA G anc).map (glinStep G))[k]? = _
  rw [list_lookup_fmap, h]
  rfl

theorem linTrALookupInv (G : Gexec) (anc : Geid → Bool) (k : Nat) (s : Estep) :
    (linCandA G anc).cdTr[k]? = some s → ∃ e, (glinEidsA G anc)[k]? = some e ∧ s = glinStep G e := by
  show ((glinEidsA G anc).map (glinStep G))[k]? = some s → _
  rw [list_lookup_fmap]
  cases he : (glinEidsA G anc)[k]? with
  | none => simp
  | some e =>
    intro h
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨e, rfl, h.symm⟩

theorem linTrALen (G : Gexec) (anc : Geid → Bool) :
    (linCandA G anc).cdTr.length = (glinEidsA G anc).length := by
  simp [linCandA]

theorem linALbl (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hok : ancOk G anc) (k : Nat)
    (e : Geid) : (glinEidsA G anc)[k]? = some e → gxLbl G e = some (glbl G e) := by
  intro h
  obtain ⟨l, hl⟩ := someOfIsSome (glinALookupLbl G anc hwf hok k e h)
  simp [glbl, hl]

theorem linALogTake (G : Gexec) (anc : Geid → Bool) (k : Nat) :
    cdLog (linCandA G anc) k = ((glinEidsA G anc).take k).filterMap (WeakRvwmoLin.gmsg G) := by
  unfold cdLog
  show trMsgs (((glinEidsA G anc).map (glinStep G)).take k) = _
  rw [← fmap_take, trMsgsOmap, omapGlin]

theorem linALogLen (G : Gexec) (anc : Geid → Bool) (k : Nat) :
    (cdLog (linCandA G anc) k).length = linNwA G anc k := by
  rw [linALogTake, omapGmsgLen]
  rfl

theorem linANwMono (G : Gexec) (anc : Geid → Bool) (k k' : Nat) :
    k ≤ k' → linNwA G anc k ≤ linNwA G anc k' :=
  filterTakeMono _ _ k k'

theorem linANwS (G : Gexec) (anc : Geid → Bool) (k : Nat) (e : Geid) :
    (glinEidsA G anc)[k]? = some e → gisW G e = true → linNwA G anc (k + 1) = linNwA G anc k + 1 := by
  intro he hw
  unfold linNwA
  rw [take_S_r he, List.filter_append]
  simp [hw]

/-- The write at trace index `k` is `gwrites G` entry number `linNwA G anc k`. -/
theorem linAGwritesSplit (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hok : ancOk G anc)
    (k : Nat) (e : Geid) :
    (glinEidsA G anc)[k]? = some e → gisW G e = true → (gwrites G)[linNwA G anc k]? = some e := by
  intro he hw
  have hsplit : (glinEidsA G anc).filter (gisW G) =
      ((glinEidsA G anc).take k).filter (gisW G) ++
        e :: ((glinEidsA G anc).drop (k + 1)).filter (gisW G) := by
    conv => lhs; rw [← List.take_append_drop (k + 1) (glinEidsA G anc)]
    rw [take_S_r he]
    simp [List.filter_append, hw]
  rw [← glinAWrites G anc hwf hok, hsplit]
  unfold linNwA
  rw [lookup_app_r (Nat.le_refl _), Nat.sub_self]
  rfl

/-- A read's source has already been emitted (RVWMO⁻: rf ⊆ gmo, writes are anchors). -/
theorem linASourceBefore (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hok : ancOk G anc)
    (hppo : gppoGmo G) (hlv : gloadValue G) (k : Nat) (r : Geid) (a : Int) (i : Nat)
    (v : BitVec 8) :
    (glinEidsA G anc)[k]? = some r → greadsByte G r a (i + 1) v →
    ∃ kw w, gwriteAt G (i + 1) = some w ∧ (glinEidsA G anc)[kw]? = some w ∧ kw < k := by
  intro hk hrd
  obtain ⟨w, hwa, _, _⟩ := (hlv r a (i + 1) v hrd).1
  have hmo := WeakRvwmoLin.grfGmo G hppo hlv r a i v w hrd hwa
  obtain ⟨hw, _⟩ := gwriteAtInv G (i + 1) w (linNd G hwf) hwa
  obtain ⟨kw, hkw⟩ := glinAIndex G anc hwf hok w (gwritesLbl G hwf w hw)
  exact ⟨kw, w, hwa, hkw,
    glinAGmoAnc G anc hwf hok k kw r w hk hkw (hok.2.1 w (gwritesIsw G w hw)) hmo⟩

theorem linAReadTsLe (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hok : ancOk G anc)
    (hppo : gppoGmo G) (hlv : gloadValue G) (k : Nat) (r : Geid) (a : Int) (t : Nat)
    (v : BitVec 8) :
    (glinEidsA G anc)[k]? = some r → greadsByte G r a t v →
    t ≤ (cdLog (linCandA G anc) k).length := by
  intro hk hrd
  rw [linALogLen]
  cases t with
  | zero => omega
  | succ i =>
    obtain ⟨kw, w, hwa, hkw, hlt⟩ := linASourceBefore G anc hwf hok hppo hlv k r a i v hk hrd
    obtain ⟨hw, hwix⟩ := gwriteAtInv G (i + 1) w (linNd G hwf) hwa
    have hsp := linAGwritesSplit G anc hwf hok kw w hkw (gwritesIsw G w hw)
    rw [gwixOfLookup G (linNwA G anc kw) w (linNd G hwf) hsp] at hwix
    have hS := linANwS G anc kw w hkw (gwritesIsw G w hw)
    have := linANwMono G anc (kw + 1) k (by omega)
    omega

theorem linAFullLog (G : Gexec) (anc : Geid → Bool) (hwf : gwf G) (hok : ancOk G anc) :
    cdLog (linCandA G anc) (linCandA G anc).cdTr.length =
      (gwrites G).filterMap (WeakRvwmoLin.gmsg G) := by
  rw [linALogTake, linTrALen, take_ge (Nat.le_refl _), omapGmsgFilter, glinAWrites G anc hwf hok]

end Weak
