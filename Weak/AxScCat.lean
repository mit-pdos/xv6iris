/-
Weak: **SC interleavings are tagged-cat consistent** (generic).  PURE (no Iris).

Rocq: `iris/AxScCat.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Spinlock plan, Phase 0.5 follow-up.  The size spike (`AxSpinSpike`) showed that deciding
`rvwmoCatConsistentT` on the 600–900-event certificate graphs with the shipped checker is
infeasible in Rocq (≈16 h).  The certificates only need EXISTENCE of consistent graphs, and the
graphs they use are SC interleavings; so this file proves, ONCE AND GENERICALLY, that every
SC-shaped tagged graph satisfies the tagged model.

THE PREDICATE `scGraph GT` (four conjuncts):
  (1) `gwf G`: gmo lists every memory event exactly once (a total order on the memory events),
      label shapes;
  (2) `scPoGmo G`: po between memory events ⊆ gmo;
  (3) `scRf G`: every read byte takes its value from the gmo-LATEST gmo-EARLIER write of that
      byte — its named source `gwriteAt t` is gmo-before the read, writes the byte with the
      value, and every gmo-earlier write of the byte has write index ≤ t; `t = 0` (the image)
      forces "no gmo-earlier write of the byte at all" (`scRfImage`) and the image value;
  (4) `gtdepsWf G D`: every tagged dependency edge is a po-forward edge from a read.
No separate RMW-adjacency clause: the fused `LRmw` is ONE event, and atomicity follows from (3)
alone (`scAtomicity`).  Store forwarding needs no clause either: an own po-earlier store is
gmo-earlier by (2).

WHAT IS PROVED.
  §2 `scLoadValue`, `scAtomicity`, `scTdepsGmo` (deps po-forward ⇒ gmo-forward), `scPpo` (ppo
     arms are po between memory events; rule 12 = dep edge (gmo-forward) ; rf (gmo-forward
     under (3))), and the capstone `scGraphCatT : scGraph GT → rvwmoCatConsistentT GT`.
  §3 a SOUND boolean `scGraphB` (`scGraphBSound`; cubic, for SMALL graphs only).
  §4 SANITY.  Satisfiable: `tw2Sc` (`AxDeps.tw2`) and `g10Sc` / `g40Sc` — the spike
     generator's truncated allocpid graphs (`AxSpinSpike.g10/g40`; in this tree 50 / 144 gmo
     events) — so the capstone applies to them (`g40CatT`).  NOT TRIVIAL: `twNotSc` —
     `AxDeps.tw` is consistent (`twCatT`) yet NOT `scGraph` (its gmo puts a forwarded read
     before its po-earlier source store), so `scGraph` is strictly stronger
     (`scStrictlyStronger`); `tw2RfBad`: a po-respecting gmo whose read names a stale source
     fails (3).
  §5 CTRL CLOSURE (row level).  `rowDepsTCtrlClosed`: in the emission fold `rowDepsT` the
     branch-source accumulator `dtCtl` is never reset, so a ctrl edge `(j,k)` emitted by a row
     prefix is re-emitted as `(j,k')` at EVERY later store-like item at position `k' > k`.  The
     graph↔emission bridge is NOT proved here (as in Rocq).

HONEST SCOPE (Rocq).  `scGraphCatT` is unconditional.  What a certificate still has to supply
is `scGraph` of ITS graph; on small instances `scGraphB` decides it.

FETCHES (owner decision D1): this tier keeps the Rocq treatment — a fetch is a graph `LLoad`;
nothing here distinguishes it.  In §5 `dstepT`'s `LIFetch` arm leaves `dtCtl` unchanged and
emits read edges only (no `DTctrl`).

**Deviations from Rocq.**

1. NAMES: lowerCamelCase (`_b` ↦ `B`, `_sound` ↦ `Sound`).  `row_deps_t_aux_app` is in
   `notes/weak-port-dupnames.json` (AxGate, AxScCat): declared file-qualified as
   `AxScCat.rowDepsTAuxApp`.
2. VOCABULARY as `AxGraphDec` deviation 2 (`forallb` ↦ `List.all`, `implb a b` ↦ `!a || b`,
   `Nat.leb` ↦ `decide (· ≤ ·)`); the read-byte triple is left-nested `(Int × Nat) × BitVec 8`.
   Edges are `((j, k), tg)` (AxDeps' `Redge`) where Rocq writes `(j, k, tg)`.
3. The `vm_compute` verdicts are `decide +kernel`.  In this tree `g10` / `g40` are the Lean
   spike's graphs (this kernel's text; see `AxSpinSpike`'s header), not Rocq's 46 / 136-event
   ones.
4. `tw` is `AxDeps.tw` (file-qualified there); `B0`/`B1` (Rocq local notations for
   `WeakLitmus.b0/b1`) are AxDeps' `b0`/`b1` (`WeakLitmus`'s, the same values).
5. `tw2RfBad`'s final step: Rocq computes the bound `gwix … ≤ 0` to `1 ≤ 0`; here
   `gwix … = 1` is a `decide +kernel` fact and `omega` closes.

**Name map** (Rocq → Lean): `sc_po_gmo` `scPoGmo`; `sc_rf` `scRf`; `sc_graph` `scGraph`;
`sc_rf_image` `scRfImage`; `sc_load_value` `scLoadValue`; `sc_atomicity` `scAtomicity`;
`sc_tdeps_gmo` `scTdepsGmo`; `sc_ppo` `scPpo`; `sc_graph_cat_t` `scGraphCatT`; `sc_po_gmo_b`
`scPoGmoB`; `sc_po_gmo_b_sound` `scPoGmoBSound`; `sc_src_b` `scSrcB`; `sc_max_b` `scMaxB`;
`sc_rf_b` `scRfB`; `sc_rf_b_sound` `scRfBSound`; `sc_graph_b` `scGraphB`; `sc_graph_b_sound`
`scGraphBSound`; `tw2_sc` `tw2Sc`; `tw2_cat_t'` `tw2CatT'`; `g10_sc` `g10Sc`; `g40_sc` `g40Sc`;
`g40_cat_t` `g40CatT`; `tw_not_sc` `twNotSc`; `sc_strictly_stronger` `scStrictlyStronger`;
`tw_prog_stale` `twProgStale`; `tw_stale` `twStale`; `tw2_rf_bad` `tw2RfBad`; `dt_fin` `dtFin`;
`row_deps_t_aux_app` `AxScCat.rowDepsTAuxApp`; `dstep_t_ctl_mono` `dstepTCtlMono`;
`dt_fin_ctl_mono` `dtFinCtlMono`; `dstep_t_ctrl_src` `dstepTCtrlSrc`;
`row_deps_t_aux_ctrl_src` `rowDepsTAuxCtrlSrc`; `dstep_t_store_ctrl` `dstepTStoreCtrl`;
`row_deps_t_ctrl_closed` `rowDepsTCtrlClosed`.

**Not ported:** nothing (the §6 `Print Assumptions` block has no Lean twin; the lint's axiom
check covers it).
-/
import Weak.AxGraphDec
import Weak.AxDeps
import Weak.AxSpinSpike

namespace Weak

open MachCSL MachCSL.Stdpp
open Wlabel Dtag

/-! # 1. The predicate -/

/-- po between memory events is gmo-forward. -/
def scPoGmo (G : Gexec) : Prop :=
  ∀ e1 e2, WeakRvwmoGraph.gpo G e1 e2 → gmem G e1 → gmem G e2 → gmoLt G e1 e2

/-- Every read byte reads the gmo-latest gmo-earlier write of the byte (or the image, when there
is none). -/
def scRf (G : Gexec) : Prop :=
  ∀ e a t v, greadsByte G e a t v →
    (match t with
     | 0 => G.gxImg a = some v
     | _ + 1 => ∃ w, gwriteAt G t = some w ∧ gwritesByte G w a v ∧ gmoLt G w e) ∧
    (∀ w' v', gwritesByte G w' a v' → gmoLt G w' e → gwix G w' ≤ t)

def scGraph (GT : GdexecT) : Prop :=
  gwf GT.gtG ∧ scPoGmo GT.gtG ∧ scRf GT.gtG ∧ gtdepsWf GT.gtG GT.gtDeps

/-- `t = 0` really means "no gmo-earlier write of the byte". -/
theorem scRfImage (G : Gexec) (e : Geid) (a : Int) (v : BitVec 8) :
    gwf G → scRf G → greadsByte G e a 0 v →
    G.gxImg a = some v ∧ ∀ w' v', gwritesByte G w' a v' → ¬ gmoLt G w' e := by
  intro hwf hrf hrd
  obtain ⟨himg, hmax⟩ := hrf e a 0 v hrd
  refine ⟨himg, fun w' v' hw' hlt => ?_⟩
  have h1 := hmax w' v' hw' hlt
  have h2 := WeakRvwmoGraph.gwixPos G w' (gwritesByteInGwrites G w' a v' hwf hw')
  omega

/-! # 2. SC ⇒ the tagged model -/

theorem scLoadValue (G : Gexec) : scPoGmo G → scRf G → gloadValue G := by
  intro hpo hrf e a t v hrd
  obtain ⟨hsrc, hmax⟩ := hrf e a t v hrd
  refine ⟨?_, ?_⟩
  · cases t with
    | zero => exact hsrc
    | succ t =>
      obtain ⟨w, hat, hwb, hlt⟩ := hsrc
      exact ⟨w, hat, hwb, Or.inl hlt⟩
  · rintro w' v' hw' (hlt | hpo')
    · exact hmax w' v' hw' hlt
    · exact hmax w' v' hw' (hpo w' e hpo' (gaccessesGmem G w' a (Or.inl ⟨v', hw'⟩))
        (gaccessesGmem G e a (Or.inr ⟨t, v, hrd⟩)))

theorem scAtomicity (G : Gexec) : gwf G → scRf G → gatomicity G := by
  intro hwf hrf e a t v hrd hw w' v' hw' ⟨_, hlt2⟩
  have hnd := hwf.1
  have hin' := gwritesByteInGwrites G w' a v' hwf hw'
  have he : e ∈ gwrites G := by
    obtain ⟨l, hl, hlw⟩ := hw
    exact gisWGwrites G e hwf (by rw [hl]; rfl) (by simp [gisW, hl, hlw])
  have hmo : gmoLt G w' e :=
    ⟨((gwritesElemOf G w').1 hin').1, ((gwritesElemOf G e).1 he).1,
      (gwixGposLt G w' e hnd hin' he).1 hlt2⟩
  have := (hrf e a t v hrd).2 w' v' hw' hmo
  omega

theorem scTdepsGmo (G : Gexec) (D : List Tdep) : scPoGmo G → gtdepsWf G D → gtdepsGmo G D := by
  intro hpo hdw d hd
  obtain ⟨hag, hlt, hr, htg⟩ := hdw d hd
  have hm2 : gmem G d.1.2 := by
    split at htg
    · exact WeakRvwmoGraph.glblIsWGmem _ _ htg
    · exact htg
  refine hpo _ _ ⟨hag, hlt, ?_, ?_⟩ (WeakRvwmoGraph.glblIsRGmem _ _ hr) hm2
  · obtain ⟨l, hl, _⟩ := hr
    rw [hl]; rfl
  · obtain ⟨l, hl, _⟩ := hm2
    rw [hl]; rfl

theorem scPpo (GT : GdexecT) :
    scPoGmo GT.gtG → scRf GT.gtG → gtdepsWf GT.gtG GT.gtDeps → gppoCatTGmo GT := by
  intro hpo hrf hdw e1 e2 h
  rcases h with h6 | h12
  · have hlv := scLoadValue _ hpo hrf
    obtain ⟨hm1, hm2⟩ := gppoGmem _ _ _ (gppoCat6Gppo _ _ _ hlv h6)
    exact hpo _ _ (gppoCat6Gpo _ _ _ h6) hm1 hm2
  · obtain ⟨_, m, had, a, t, v, hrd, hat⟩ := h12
    obtain ⟨tg, hin, _, _⟩ := (elemOfGtAd _ _ _ _).1 had
    have hdm := scTdepsGmo _ _ hpo hdw _ hin
    obtain ⟨hsrc, _⟩ := hrf e2 a t v hrd
    cases t with
    | zero => simp [gwriteAt] at hat
    | succ t =>
      obtain ⟨w, hat', _, hlt⟩ := hsrc
      have hat2 : gwriteAt GT.gtG (t + 1) = some m := hat
      rw [hat2] at hat'
      cases hat'
      exact gmoLtTrans GT.gtG _ _ _ hdm hlt

/-- THE CAPSTONE. -/
theorem scGraphCatT (GT : GdexecT) : scGraph GT → rvwmoCatConsistentT GT := by
  rintro ⟨hwf, hpo, hrf, hdw⟩
  exact ⟨hwf, scPpo GT hpo hrf hdw, scLoadValue _ hpo hrf, scAtomicity _ hwf hrf, hdw,
    scTdepsGmo _ _ hpo hdw⟩

/-! # 3. A sound boolean (small graphs) -/

def scPoGmoB (G : Gexec) : Bool :=
  (gevents G).all (fun e1 => (gevents G).all (fun e2 =>
    !(gpoB G e1 e2 && glblB G e1 lbIsMem && glblB G e2 lbIsMem) || gmoLtB G e1 e2))

theorem scPoGmoBSound (G : Gexec) : scPoGmoB G = true → scPoGmo G := by
  rw [scPoGmoB, forallbForallTrue]
  intro H e1 e2 hpo hm1 hm2
  obtain ⟨he1, he2⟩ := gpoGevents G e1 e2 hpo
  have h := (forallbForallTrue _ _).1 (H e1 he1) e2 he2
  rw [(gpoBSpec _ _ _).2 hpo, (glblBSpec _ _ lbIsMem).2 hm1, (glblBSpec _ _ lbIsMem).2 hm2]
    at h
  exact (gmoLtBSpec _ _ _).1 (by simpa using h)

def scSrcB (G : Gexec) (e : Geid) (x : (Int × Nat) × BitVec 8) : Bool :=
  match x.1.2 with
  | 0 => gimgB G x.1.1 x.2
  | _ + 1 =>
    match gwriteAt G x.1.2 with
    | some w => gwbB G w x.1.1 x.2 && gmoLtB G w e
    | none => false

def scMaxB (G : Gexec) (e : Geid) (x : (Int × Nat) × BitVec 8) : Bool :=
  (gevents G).all (fun w' =>
    !(gwaB G w' x.1.1 && gmoLtB G w' e) || decide (gwix G w' ≤ x.1.2))

def scRfB (G : Gexec) : Bool :=
  (gevents G).all (fun e => (grdBytes G e).all (fun x => scSrcB G e x && scMaxB G e x))

theorem scRfBSound (G : Gexec) : scRfB G = true → scRf G := by
  rw [scRfB, forallbForallTrue]
  intro H e a t v hrd
  have h := (forallbForallTrue _ _).1 (H e (greadsByteGevents G e a t v hrd)) ((a, t), v)
    ((greadsByteBytes _ _ _ _ _).1 hrd)
  rw [Bool.and_eq_true] at h
  obtain ⟨hsrc, hmax⟩ := h
  refine ⟨?_, ?_⟩
  · cases t with
    | zero =>
      simp only [scSrcB] at hsrc
      exact (gimgBSpec _ _ _).1 hsrc
    | succ t =>
      simp only [scSrcB] at hsrc
      cases hw : gwriteAt G (t + 1) with
      | none => rw [hw] at hsrc; cases hsrc
      | some w =>
        rw [hw, Bool.and_eq_true] at hsrc
        exact ⟨w, rfl, (gwbBSpec _ _ _ _).1 hsrc.1, (gmoLtBSpec _ _ _).1 hsrc.2⟩
  · intro w' v' hw' hlt
    have h := (forallbForallTrue _ _).1 hmax w' (gwritesByteGevents G w' a v' hw')
    have h1 : gwaB G w' a = true := (gwaBSpec _ _ _).2 ⟨v', hw'⟩
    have h2 : gmoLtB G w' e = true := (gmoLtBSpec _ _ _).2 hlt
    simpa [h1, h2] using h

def scGraphB (GT : GdexecT) : Bool :=
  gwfB GT.gtG && scPoGmoB GT.gtG && scRfB GT.gtG && gtdepsWfB GT.gtG GT.gtDeps

theorem scGraphBSound (GT : GdexecT) : scGraphB GT = true → scGraph GT := by
  rw [scGraphB, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  rintro ⟨⟨⟨hwf, hpo⟩, hrf⟩, hdw⟩
  exact ⟨gwfBSound _ hwf, scPoGmoBSound _ hpo, scRfBSound _ hrf, gtdepsWfBSound _ _ hdw⟩

/-! # 4. Sanity -/

/-- Satisfiable: `tw2` (rule-12-abiding gmo of `AxDeps.tw`). -/
theorem tw2Sc : scGraph tw2 := scGraphBSound _ (by decide +kernel)

theorem tw2CatT' : rvwmoCatConsistentT tw2 := scGraphCatT _ tw2Sc

/-- Satisfiable on the spike generator's own graphs (truncated allocpid harts, 2 harts). -/
theorem g10Sc : scGraph AxSpinSpike.g10 := scGraphBSound _ (by decide +kernel)

theorem g40Sc : scGraph AxSpinSpike.g40 := scGraphBSound _ (by decide +kernel)

theorem g40CatT : rvwmoCatConsistentT AxSpinSpike.g40 := scGraphCatT _ g40Sc

/-- NOT TRIVIAL: `tw` is consistent but not SC — its gmo puts the forwarded read (1,2) before
its po-earlier source store (1,1). -/
theorem twNotSc : ¬ scGraph AxDeps.tw := by
  rintro ⟨_, hpo, _, _⟩
  have H : gmoLt AxDeps.tw.gtG (1, 1) (1, 2) :=
    hpo _ _ ((gpoBSpec _ _ _).1 (by decide +kernel))
      ((glblBSpec _ _ lbIsMem).1 (by decide +kernel))
      ((glblBSpec _ _ lbIsMem).1 (by decide +kernel))
  exact absurd ((gmoLtBSpec _ _ _).2 H) (by decide +kernel)

theorem scStrictlyStronger : rvwmoCatConsistentT AxDeps.tw ∧ ¬ scGraph AxDeps.tw :=
  ⟨twCatT, twNotSc⟩

/-- A po-respecting gmo whose read names a STALE source: `tw2`'s order with hart 1's reload
(1,2) reading the image of x although its own store (1,1) is gmo-earlier.  (3) fails. -/
def twProgStale : List (List Lbl) :=
  [[Lbl.LLoad false 0 [1] [b1],
    Lbl.LLoad false 1 [0] [b0]],
   [Lbl.LLoad false 2 [0] [b0],
    Lbl.LStore false 0 [b1] .WCplain,
    Lbl.LLoad false 0 [0] [b0]]]

def twStale : GdexecT :=
  mkgt twProgStale [(1, 0), (1, 1), (1, 2), (0, 0), (0, 1)] twDeps

theorem tw2RfBad : ¬ scRf twStale.gtG := by
  intro hrf
  have hrd : greadsByte twStale.gtG (1, 2) 0 0 b0 :=
    (greadsByteBytes _ _ _ _ _).2 (by decide +kernel)
  have hw : gwritesByte twStale.gtG (1, 1) 0 b1 :=
    (gwritesByteBytes _ _ _ _).2 (by decide +kernel)
  have hlt : gmoLt twStale.gtG (1, 1) (1, 2) := (gmoLtBSpec _ _ _).1 (by decide +kernel)
  have hle := (hrf _ _ _ _ hrd).2 _ _ hw hlt
  have hix : gwix twStale.gtG (1, 1) = 1 := by decide +kernel
  omega

/-! # 5. Ctrl closure of the emission fold (row level) -/

/-- The state after a row prefix. -/
def dtFin (s : DstateT) (es : List Eitem) : DstateT :=
  match es with
  | [] => s
  | it :: es' => dtFin (dstepT s it).1 es'

theorem AxScCat.rowDepsTAuxApp (s : DstateT) (es1 es2 : List Eitem) :
    rowDepsTAux s (es1 ++ es2) = rowDepsTAux s es1 ++ rowDepsTAux (dtFin s es1) es2 := by
  induction es1 generalizing s with
  | nil => rfl
  | cons it es1' ih =>
    simp only [List.cons_append, rowDepsTAux, dtFin, ih, List.append_assoc]

/-- `dtCtl` only grows. -/
theorem dstepTCtlMono (s : DstateT) (it : Eitem) (j : Nat) :
    j ∈ s.dtCtl → j ∈ (dstepT s it).1.dtCtl := by
  intro h
  obtain ⟨l, ok⟩ := it
  cases l <;> cases ok <;> simp [dstepT, h]

theorem dtFinCtlMono (s : DstateT) (es : List Eitem) (j : Nat) :
    j ∈ s.dtCtl → j ∈ (dtFin s es).dtCtl := by
  induction es generalizing s with
  | nil => exact id
  | cons it es ih => exact fun h => ih _ (dstepTCtlMono s it j h)

/-- A ctrl edge's source is in `dtCtl` at the emitting step. -/
theorem dstepTCtrlSrc (s : DstateT) (it : Eitem) (j k : Nat) :
    ((j, k), DTctrl) ∈ (dstepT s it).2 → j ∈ s.dtCtl := by
  obtain ⟨l, ok⟩ := it
  cases l <;> cases ok <;>
    simp [dstepT, dedgesR, dedgesW, elemOfTagEdges] <;> intros <;> assumption

theorem rowDepsTAuxCtrlSrc (s : DstateT) (es : List Eitem) (j k : Nat) :
    ((j, k), DTctrl) ∈ rowDepsTAux s es → j ∈ (dtFin s es).dtCtl := by
  induction es generalizing s with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons it es ih =>
    intro h
    simp only [rowDepsTAux, List.mem_append] at h
    rcases h with h | h
    · exact dtFinCtlMono _ es j (dstepTCtlMono s it j (dstepTCtrlSrc s it j k h))
    · exact ih _ h

/-- A store-like item at position k' emits a ctrl edge from every accumulated source below k'. -/
theorem dstepTStoreCtrl (s : DstateT) (it : Eitem) (k' j : Nat) :
    it.2 = some k' → elbIsW it.1 = true → j ∈ s.dtCtl → j < k' →
    ((j, k'), DTctrl) ∈ (dstepT s it).2 := by
  obtain ⟨l, ko⟩ := it
  simp only
  rintro rfl hw hj hlt
  have he : ((j, k'), DTctrl) ∈ tagEdges DTctrl k' s.dtCtl :=
    (elemOfTagEdges ..).2 ⟨rfl, rfl, hj, hlt⟩
  cases l <;> simp only [elbIsW, Bool.false_eq_true] at hw <;>
    simp only [dstepT, dedgesW, List.mem_append] <;> exact Or.inr (Or.inr (Or.inl he))

/-- THE ROW-LEVEL CTRL CLOSURE: a ctrl edge (j,k) emitted by a row prefix reappears as (j,k') at
every later store-like item at k' > k. -/
theorem rowDepsTCtrlClosed (es1 : List Eitem) (it : Eitem) (es2 : List Eitem) (j k k' : Nat) :
    ((j, k), DTctrl) ∈ rowDepsT es1 →
    it.2 = some k' → elbIsW it.1 = true → k < k' →
    ((j, k'), DTctrl) ∈ rowDepsT (es1 ++ it :: es2) := by
  intro hin hk hw hlt
  rw [rowDepsT, AxScCat.rowDepsTAuxApp]
  simp only [rowDepsTAux, List.mem_append]
  refine Or.inr (Or.inl (dstepTStoreCtrl _ it k' j hk hw ?_ ?_))
  · exact rowDepsTAuxCtrlSrc _ _ j k hin
  · have := rowDepsTLt es1 j k DTctrl hin
    omega

end Weak
