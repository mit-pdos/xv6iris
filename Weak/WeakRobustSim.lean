/-
Weak: **THE SIMULATION** (M6 W2b): replaying a traced full-machine behavior as a
PROMISE-FREE run along a topological order of the extended dependency graph.

Rocq: `iris/WeakRobustSim.v` @ xxvzwolszwmp.

The Rocq header, in substance.  THE CONSTRUCTION.  `WeakRobustOrd.toposortIndS`
hands the events of a downward-closed subset one at a time, in an order in
which every `gdep3`-predecessor of the next event is already processed.  After
processing `dn` we have built: the TIMESTAMP MAP π = `pi TS dn` (the behavior's
fulfilled timestamps occurring in `dn`, in PROCESSING order, mapped to the
promise-free log positions `1 .. |fl dn|`; everything else sent injectively
above that range, 0 fixed; `sigmaOk (pi TS dn)` is what `WeakRobustProv`'s
transport theorems consume); the PROMISE-FREE LOG `WeakRobustSim.pfLog TS dn`
(literally `(fl TS dn).map (msgAt TS)`); and a pf configuration reached from
`wpInit img d0 ps` whose agent `j` sits at trace position `nproc dn j` with
`Wstate` `aevsPost (pi TS dn) (take (nproc dn j) evs) wsInit`.

THE FOUR CRUXES.  (1) VALUES: a read of `t` reads `pfLog`'s position
`pi t - 1`, which holds the SAME message; `t = 0` reads the image.  (2)
READABLE: a byte-`a` write at pf position `q' ∈ (π t, pf-floor]` is `π t̂` for
a PROCESSED `t̂`; the four cases `t̂ = t` (π injective), `t̂ < t` (co + the
processing order), `t < t̂ ≤ F` (the behavior's own `readable`), `t̂ > F` (the
`gE` edges) are all refuted.  (3) EXCL_OK (rmw), same shape, with the split
pair's reservation column (`exclOkTsPf`) read at the po-earlier `LExLoad`.
(4) FINAL MEMORY: every log message is fulfilled, so the latest byte-`a` write
maps to the pf log's latest.  THE FABRIC (G4): `qfab dn (pcDev cf)` says the
replayed fabric is `devAt`'s fold over the processed witness prefix, and
`qdev dn n` that the processed events are exactly the first `n` witness
entries; `qfabStep` is the whole of G4's device arm.  THE PREMISES are all
bundle-level; `tsOblivious` (worklist finding (v)): the pf witness steps the
program with π-RETIMED labels.  DISCIPLINE PREMISES ARE NOT USED.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1 (the capitalised
   Rocq names keep their capital: `NoDup_omap_inj` ↦ `NoDupOmapInj`,
   `Qinv_step` ↦ `QinvStep`, ...).  File-qualified (in
   `notes/weak-port-dupnames.json`): `pf_log` ↦ `WeakRobustSim.pfLog`.  The
   binder `done` is `dn` (`done` is a tactic keyword).  Rocq's `lb_aq` here is
   `WeakRobustAcyc.lbAq` (as in `WeakRobustOrd`).
2. VOCABULARY: as `Weak/WeakRobustOrd.lean` deviation 2 (`l !! i` ↦ `l[i]?`,
   `NoDup` ↦ `List.Nodup`, `omap` ↦ `List.filterMap`, `f <$> l` ↦ `l.map f`,
   `tvs.*1`/`.*2` ↦ `tvs.map Prod.fst`/`Prod.snd`, `filter` ↦
   `List.filter (decide ∘ ·)`, `list_find` ↦ `listFind` with a `decide`
   predicate, `S n` ↦ `n + 1`, `bool_decide (t = 0)` ↦ `if t = 0`, `default d o`
   ↦ `o.getD d`, `<[i:=x]> l` ↦ `l.set i x`), `Inj eq eq` ↦
   `Function.Injective` (the instance `piL_inj` is the theorem `piLInj`).
3. SECTION VARIABLES: the Rocq `book`/`sim`/`wrapper` sections' parameters
   (`pstep pcls TS DS img d0 ps`) are `variable`s, included exactly where a
   declaration mentions them; the section HYPOTHESES (`Hwf Hwsi Hco Hwfl Hlf
   Hobl Hcls Hclsobl Himg Hnag Hdata Hps0 Hwit Hd0`) are explicit arguments of
   exactly the declarations whose Rocq proof uses them, in Rocq's order.  `pdev`
   is not a parameter anywhere in the simulation: Rocq threads it only into
   `grf_source_unique pstep pdev`, whose Lean twin `grfSourceUnique` takes no
   `pdev` (`WeakRobustGraph` deviation 3); `NoDupFl` & co. therefore take none.
4. O2 / owner decision D4 (the Lean-only label `LIFetch base tvs`,
   `Weak/WeakPromise.lean` deviation 8; `wpPfStep.PFIFetch`,
   `Weak/WeakPromiseBridge.lean` deviation 6).  An i-cache fetch is NOT a
   reads-of source (`lbReads (LIFetch ..) = []`, `WeakRobustGraph` deviation 4),
   so the dependency graph has NO edge into a fetch from the write it fetched,
   and the replay cannot by itself guarantee that write is already in the pf
   log when the fetch is replayed (the replayed fetch, at instruction view 0,
   needs exactly the VALUE crux: the fetched message is in the pf log).
   Changes, all confined to the new label:
   - `tsOblivious` gains a FOURTH conjunct, `LIFetch`'s (the retimed fetch is
     stepped like the retimed load), as `notes/weak-port-o2-design.md` §1.4
     prescribes ("`ts_oblivious` gains a state-identity arm").
   - NEW PREMISE `fetchSrcOk TS` (Lean-only definition): every nonzero
     timestamp a fetch answers is fulfilled by an event `tc gdep2`-before the
     fetch.  It is an explicit argument of `QinvStep`, `simPrefix`,
     `simFull`, and, as a separate bundle-level premise (the shape of the
     `clsCanonical` one), of `wpBehaviorRobustDev` / `wpBehaviorRobust`.  It
     is vacuous for fetch-free programs (`fetchSrcOkNoFetch`) and for fetches
     of never-written bytes (timestamp 0).  OWNER-VISIBLE: the downstream
     capstone must discharge it (e.g. from the fetched text's publication
     order, or by adding fetch rf edges to the graph whose acyclicity it
     already proves).
   - `QinvStep` / `aevPostExt` gain the `LIFetch` arm (`aevPost` is the
     identity there; the replay step is `PFIFetch`).  For every Rocq label the
     statements and proofs are Rocq's.
5. Induction shapes: `qorderTcIndex` goes by tail induction on `tc` (core
   `Relation.TransGen`, built from the last step; Rocq: head-style);
   `promiseRunShape` by tail induction on `rtc`; `NoDupOmapInj` by plain list
   induction.  Statements unchanged.
6. `piLSpec` / `piLMem` etc.: Rocq's `S (length L) + t` is `L.length + 1 + t`.
   `msg_at`'s junk default `WMsg 0 [] None WCplain` is `⟨0, [], none, .WCplain⟩`.
7. Lean-only helpers (no Rocq twin): `fetchSrcOk`, `fetchSrcOkNoFetch`,
   `logBytePf` (the VALUES crux, shared by `readOkPf` and the `LIFetch` arm).

**Rocq → Lean name map.**  `NoDup_omap_inj` ↦ `NoDupOmapInj`; `log_byte_pos` ↦
`logBytePos`; `latest_ts_zero_iff` ↦ `latestTsZeroIff`; `piL`; `piL_0` ↦ `piL0`;
`piL_spec` ↦ `piLSpec`; `piL_pos` ↦ `piLPos`; `piL_eq_zero` ↦ `piLEqZero`;
`piL_inj` ↦ `piLInj`; `piL_sigma_ok` ↦ `piLSigmaOk`; `piL_mem` ↦ `piLMem`;
`piL_mem_le` ↦ `piLMemLe`; `piL_app` ↦ `piLApp`; `fl`; `pi`; `msg_at` ↦ `msgAt`;
`pf_log` ↦ `WeakRobustSim.pfLog`; `fpos`; `fl_app` ↦ `flApp`; `fl_app_none` ↦
`flAppNone`; `fl_app_some` ↦ `flAppSome`; `elem_of_fl` ↦ `elemOfFl`; `fl_len` ↦
`flLen`; `pi_app` ↦ `piApp`; `pi_0` ↦ `pi0`; `pi_sigma_ok` ↦ `piSigmaOk`;
`pi_pos` ↦ `piPos`; `fl_take_app` ↦ `flTakeApp`; `fpos_mono` ↦ `fposMono`;
`fpos_succ` ↦ `fposSucc`; `fl_lookup_fpos` ↦ `flLookupFpos`; `fpos_lt` ↦
`fposLt`; `nproc`; `nproc_app_eq` ↦ `nprocAppEq`; `nproc_app_ne` ↦
`nprocAppNe`; `nproc_nil` ↦ `nprocNil`; `tlabel_ts_snd` ↦ `tlabelTsSnd`;
`tlabel_ts_length` ↦ `tlabelTsLength`; `tlabel_ts_lookup` ↦ `tlabelTsLookup`;
`tlabel_ts_lookup_inv` ↦ `tlabelTsLookupInv`; `aev_post_ext` ↦ `aevPostExt`;
`aevs_post_ext` ↦ `aevsPostExt`; `lfloor_leaf` ↦ `lfloorLeaf`; `ts_oblivious` ↦
`tsOblivious`; `qdev`; `qfab`; `qfab_init` ↦ `qfabInit`; `pd_ord_not_free` ↦
`pdOrdNotFree`; `qdev_index` ↦ `qdevIndex`; `qfab_step` ↦ `qfabStep`; `qorder`;
`qcfg`; `Qinv`; `qorder_dc` ↦ `qorderDc`; `qorder_wf` ↦ `qorderWf`;
`qorder_mem` ↦ `qorderMem`; `qorder_tc_index` ↦ `qorderTcIndex`;
`qorder_tc_in` ↦ `qorderTcIn`; `fl_ts_pos` ↦ `flTsPos`; `NoDup_fl` ↦ `NoDupFl`;
`pi_mem` ↦ `piMem`; `pf_log_pi` ↦ `pfLogPi`; `msg_at_eq` ↦ `msgAtEq`; `fl_msg`
↦ `flMsg`; `pf_writes_in_inv` ↦ `pfWritesInInv`; `read_source_in` ↦
`readSourceIn`; `read_ts_in_fl` ↦ `readTsInFl`; `occ_processed` ↦
`occProcessed`; `ws_stable` ↦ `wsStable`; `pi_lt_of_tc` ↦ `piLtOfTc`;
`pi_lt_of_co` ↦ `piLtOfCo`; `nproc_cur` ↦ `nprocCur`; `qorder_step` ↦
`qorderStep`; `read_ok_pf` ↦ `readOkPf`; `pf_writes_in_by_inv` ↦
`pfWritesInByInv`; `msg_byte_run` ↦ `msgByteRun`; `excl_ok_pf` ↦ `exclOkPf`;
`excl_ok_ts_pf` ↦ `exclOkTsPf`; `replay_ws_relp` ↦ `replayWsRelp`;
`replay_ws_res` ↦ `replayWsRes`; `replay_ws_res_src` ↦ `replayWsResSrc`;
`qcfg_step` ↦ `qcfgStep`; `Qinv_step` ↦ `QinvStep`; `Qinv_nil` ↦ `QinvNil`;
`sim_prefix` ↦ `simPrefix`; `sim_full` ↦ `simFull`; `Qinv_run` ↦ `QinvRun`;
`Qinv_order` ↦ `QinvOrder`; `log_ne` ↦ `logNe`; `log_ne_init` ↦ `logNeInit`;
`log_ne_promise_step` ↦ `logNePromiseStep`; `log_ne_promise_run` ↦
`logNePromiseRun`; `promise_run_shape` ↦ `promiseRunShape`;
`wp_behavior_robust_dev` ↦ `wpBehaviorRobustDev`; `wp_behavior_robust` ↦
`wpBehaviorRobust`.

**Not ported:** nothing (every Rocq definition and lemma has a Lean twin).

**Statements checked** (by hand, against Rocq): all of them; the only
statement changes are deviation 4's (`tsOblivious`'s fourth conjunct, the
`fetchSrcOk` premise of `QinvStep`/`simPrefix`/`simFull`/the two wrappers).
-/
import Weak.WeakRobustOrd
import Weak.WeakRobustSer

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std Wlabel

/-! ## LAYER 0: two generic list facts, and one `WeakMem` convenience -/

theorem NoDupOmapInj {A B : Type _} (f : A → Option B) (l : List A) :
    l.Nodup →
    (∀ x y b, x ∈ l → y ∈ l → f x = some b → f y = some b → x = y) →
    (l.filterMap f).Nodup := by
  induction l with
  | nil => intro _ _; exact List.nodup_nil
  | cons x l ih =>
    intro hnd hinj
    obtain ⟨hx, hnd⟩ := List.nodup_cons.1 hnd
    have hinj' : ∀ y z b, y ∈ l → z ∈ l → f y = some b → f z = some b → y = z :=
      fun y z b hy hz => hinj y z b (List.mem_cons_of_mem _ hy) (List.mem_cons_of_mem _ hz)
    rw [List.filterMap_cons]
    cases hfx : f x with
    | none => exact ih hnd hinj'
    | some b =>
      refine List.nodup_cons.2 ⟨?_, ih hnd hinj'⟩
      intro hb
      obtain ⟨y, hy, hfy⟩ := List.mem_filterMap.1 hb
      have hyx : y = x := hinj y x b (List.mem_cons_of_mem _ hy) (by simp) hfy hfx
      subst hyx
      exact hx hy

theorem logBytePos (img : Image) (log : List Wmsg) (q : Nat) (m : Wmsg) (a : Int) :
    0 < q → log[q - 1]? = some m → logByte img log q a = msgByte m a := by
  intro hq hm
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hm
  rw [logByteS, hm]
  rfl

/-- `latestTs` is 0 exactly when nothing in the log writes the byte. -/
theorem latestTsZeroIff (log : List Wmsg) (a : Int) :
    latestTs log a = 0 ↔ ¬ writesIn log a 0 log.length := by
  constructor
  · intro hz hw
    apply latestTsTop log a
    rw [hz]; exact hw
  · intro hn
    rcases latestTsWrites log a with hz | ⟨i, m, hr, hlk, hs⟩
    · exact hz
    · exfalso
      apply hn
      have hle := latestTsLe log a
      exact ⟨i + 1, by omega, by omega, m, by rw [Nat.add_sub_cancel]; exact hlk, hs⟩

/-! ## LAYER 1: the timestamp map π, on an abstract position list -/

/-- `piL L t`: 0 is fixed; a member of `L` goes to (its first index) + 1; a
non-member goes injectively ABOVE `|L|`. -/
def piL (L : List Nat) (t : Nat) : Nat :=
  if t = 0 then 0
  else match listFind (fun t' => decide (t' = t)) L with
    | some (i, _) => i + 1
    | none => L.length + 1 + t

theorem piL0 (L : List Nat) : piL L 0 = 0 := by simp [piL]

theorem piLSpec (L : List Nat) (t : Nat) :
    t ≠ 0 →
    (∃ i, L[i]? = some t ∧ i < L.length ∧ piL L t = i + 1) ∨
    (t ∉ L ∧ piL L t = L.length + 1 + t) := by
  intro ht
  unfold piL
  rw [if_neg ht]
  rcases hf : listFind (fun t' => decide (t' = t)) L with _ | ⟨i, x⟩
  · refine Or.inr ⟨fun hin => ?_, rfl⟩
    have := list_find_elem_of (p := fun t' => decide (t' = t)) hin (by simp)
    rw [hf] at this
    cases this
  · obtain ⟨hi, hx, _⟩ := list_find_Some.1 hf
    have hxt : x = t := of_decide_eq_true hx
    subst hxt
    exact Or.inl ⟨i, hi, lookup_lt_Some hi, rfl⟩

theorem piLPos (L : List Nat) (t : Nat) : t ≠ 0 → 0 < piL L t := by
  intro ht
  rcases piLSpec L t ht with ⟨i, _, _, h⟩ | ⟨_, h⟩ <;> rw [h] <;> omega

theorem piLEqZero (L : List Nat) (t : Nat) : piL L t = 0 → t = 0 := by
  intro h
  by_cases ht : t = 0
  · exact ht
  · have := piLPos L t ht; omega

theorem piLInj (L : List Nat) : Function.Injective (piL L) := by
  intro t1 t2 heq
  by_cases h1 : t1 = 0
  · subst h1; exact (piLEqZero L t2 (by rw [← heq, piL0])).symm
  by_cases h2 : t2 = 0
  · subst h2; exact piLEqZero L t1 (by rw [heq, piL0])
  rcases piLSpec L t1 h1 with ⟨i1, hi1, _, hp1⟩ | ⟨_, hp1⟩ <;>
  rcases piLSpec L t2 h2 with ⟨i2, hi2, _, hp2⟩ | ⟨_, hp2⟩ <;>
  rw [hp1, hp2] at heq
  · have hi : i1 = i2 := by omega
    subst hi
    rw [hi1] at hi2
    cases hi2; rfl
  · have := lookup_lt_Some hi1; omega
  · have := lookup_lt_Some hi2; omega
  · omega

theorem piLSigmaOk (L : List Nat) : sigmaOk (piL L) := ⟨piL0 L, piLInj L⟩

/-- MEMBERSHIP, at a KNOWN index — needs `Nodup` to identify the index
`listFind` returns with the one at hand. -/
theorem piLMem (L : List Nat) (i t : Nat) :
    L.Nodup → L[i]? = some t → t ≠ 0 → piL L t = i + 1 := by
  intro hnd hi ht
  unfold piL
  rw [if_neg ht]
  rcases hf : listFind (fun t' => decide (t' = t)) L with _ | ⟨i', x⟩
  · exfalso
    have := list_find_elem_of (p := fun t' => decide (t' = t)) (elem_of_list_lookup_2 hi)
      (by simp)
    rw [hf] at this
    cases this
  · obtain ⟨hi', hx, _⟩ := list_find_Some.1 hf
    have hxt : x = t := of_decide_eq_true hx
    subst hxt
    show i' + 1 = i + 1
    rw [NoDup_lookup hnd hi' hi]

theorem piLMemLe (L : List Nat) (t : Nat) : t ∈ L → piL L t ≤ L.length := by
  intro hin
  by_cases ht : t = 0
  · subst ht; rw [piL0]; omega
  · rcases piLSpec L t ht with ⟨i, _, hlt, h⟩ | ⟨hn, _⟩
    · omega
    · exact absurd hin hn

/-- STABILITY under append: `listFind` over a prefix is unchanged. -/
theorem piLApp (L L' : List Nat) (t : Nat) : t ∈ L ∨ t = 0 → piL (L ++ L') t = piL L t := by
  intro hin
  by_cases ht : t = 0
  · subst ht; rw [piL0, piL0]
  have hmem : t ∈ L := by
    rcases hin with h | h
    · exact h
    · exact absurd h ht
  unfold piL
  rw [if_neg ht, if_neg ht]
  rcases hf : listFind (fun t' => decide (t' = t)) L with _ | ⟨i, x⟩
  · exfalso
    have := list_find_elem_of (p := fun t' => decide (t' = t)) hmem (by simp)
    rw [hf] at this
    cases this
  · rw [list_find_app_l hf]

/-! ## LAYER 2: the bookkeeping over a processed prefix -/

section book

variable {P D : Type}
variable (TS : Ptraces P D)

/-- The processed timestamps, in processing order. -/
def fl (dn : List Gev) : List Nat := dn.filterMap (gevTs TS)

def pi (dn : List Gev) : Nat → Nat := piL (fl TS dn)

/-- The message a timestamp names (junk off the log — never consumed). -/
def msgAt (t : Nat) : Wmsg := (TS.ptLog[t - 1]?).getD ⟨0, [], none, .WCplain⟩

/-- THE PROMISE-FREE LOG.  Definitionally a `map` of `fl`. -/
def WeakRobustSim.pfLog (dn : List Gev) : List Wmsg := (fl TS dn).map (msgAt TS)

/-- The position `fl` reaches after `n` processed events. -/
def fpos (dn : List Gev) (n : Nat) : Nat := (fl TS (dn.take n)).length

/-! ### `fl` -/

theorem flApp (dn l : List Gev) : fl TS (dn ++ l) = fl TS dn ++ fl TS l := by
  simp [fl, List.filterMap_append]

theorem flAppNone (dn : List Gev) (e : Gev) : gevTs TS e = none → fl TS (dn ++ [e]) = fl TS dn := by
  intro he
  rw [flApp]
  simp [fl, he]

theorem flAppSome (dn : List Gev) (e : Gev) (t : Nat) :
    gevTs TS e = some t → fl TS (dn ++ [e]) = fl TS dn ++ [t] := by
  intro he
  rw [flApp]
  simp [fl, he]

theorem elemOfFl (dn : List Gev) (t : Nat) : t ∈ fl TS dn ↔ ∃ e, e ∈ dn ∧ gevTs TS e = some t := by
  unfold fl
  exact elem_of_list_omap

theorem flLen (dn : List Gev) : (WeakRobustSim.pfLog TS dn).length = (fl TS dn).length := by
  simp [WeakRobustSim.pfLog]

/-- `pi` is stable on already-processed timestamps. -/
theorem piApp (dn l : List Gev) (t : Nat) :
    t ∈ fl TS dn ∨ t = 0 → pi TS (dn ++ l) t = pi TS dn t := by
  intro ht
  unfold pi
  rw [flApp]
  exact piLApp _ _ t ht

theorem pi0 (dn : List Gev) : pi TS dn 0 = 0 := piL0 _

theorem piSigmaOk (dn : List Gev) : sigmaOk (pi TS dn) := piLSigmaOk _

theorem piPos (dn : List Gev) (t : Nat) : t ≠ 0 → 0 < pi TS dn t := piLPos _ t

/-! ### `fpos`: the position an event's timestamp takes in `fl` -/

theorem flTakeApp (dn : List Gev) (n n' : Nat) :
    n ≤ n' → ∃ L, fl TS (dn.take n') = fl TS (dn.take n) ++ L := by
  intro hle
  refine ⟨fl TS ((dn.drop n).take (n' - n)), ?_⟩
  rw [← flApp, take_take_drop]
  congr 2
  omega

theorem fposMono (dn : List Gev) (n n' : Nat) : n ≤ n' → fpos TS dn n ≤ fpos TS dn n' := by
  intro hle
  obtain ⟨L, hL⟩ := flTakeApp TS dn n n' hle
  unfold fpos
  rw [hL, List.length_append]
  omega

theorem fposSucc (dn : List Gev) (n : Nat) (e : Gev) (t : Nat) :
    dn[n]? = some e → gevTs TS e = some t → fpos TS dn (n + 1) = fpos TS dn n + 1 := by
  intro hn ht
  unfold fpos
  rw [take_S_r hn, flAppSome TS _ e t ht, List.length_append]
  rfl

theorem flLookupFpos (dn : List Gev) (n : Nat) (e : Gev) (t : Nat) :
    dn[n]? = some e → gevTs TS e = some t → (fl TS dn)[fpos TS dn n]? = some t := by
  intro hn ht
  have hsplit : fl TS dn = fl TS (dn.take n) ++ fl TS (dn.drop n) := by
    rw [← flApp, List.take_append_drop]
  have : fl TS (e :: dn.drop (n + 1)) = t :: fl TS (dn.drop (n + 1)) := by
    simp [fl, ht]
  unfold fpos
  rw [hsplit, drop_S hn, this, lookup_app_r (Nat.le_refl _), Nat.sub_self]
  rfl

theorem fposLt (dn : List Gev) (n n' : Nat) (e : Gev) (t : Nat) :
    dn[n]? = some e → gevTs TS e = some t → n < n' → fpos TS dn n < fpos TS dn n' := by
  intro hn ht hlt
  have h1 := fposSucc TS dn n e t hn ht
  have h2 := fposMono TS dn (n + 1) n' (by omega)
  omega

end book

/-! ## `nproc`: how many of agent `j`'s events are processed -/

def nproc (dn : List Gev) (j : Nat) : Nat := (dn.filter (fun e => decide (e.1 = j))).length

theorem nprocAppEq (dn : List Gev) (e : Gev) : nproc (dn ++ [e]) e.1 = nproc dn e.1 + 1 := by
  simp [nproc, List.filter_append]

theorem nprocAppNe (dn : List Gev) (e : Gev) (j : Nat) : j ≠ e.1 → nproc (dn ++ [e]) j = nproc dn j := by
  intro hne
  have : ¬ e.1 = j := fun h => hne h.symm
  simp [nproc, List.filter_append, this]

theorem nprocNil (j : Nat) : nproc [] j = 0 := rfl

/-! ## LAYER 2b: EXTENSIONALITY of the σ-transported fold -/

theorem tlabelTsSnd (σ : Nat → Nat) (tvs : List (Nat × BitVec 8)) :
    (tlabelTs σ tvs).map Prod.snd = tvs.map Prod.snd := by
  simp [tlabelTs]

theorem tlabelTsLength (σ : Nat → Nat) (tvs : List (Nat × BitVec 8)) :
    (tlabelTs σ tvs).length = tvs.length := by
  simp [tlabelTs]

theorem tlabelTsLookup (σ : Nat → Nat) (tvs : List (Nat × BitVec 8)) (j t : Nat) (v : BitVec 8) :
    tvs[j]? = some (t, v) → (tlabelTs σ tvs)[j]? = some (σ t, v) := by
  intro hj
  simp [tlabelTs, hj]

theorem tlabelTsLookupInv (σ : Nat → Nat) (tvs : List (Nat × BitVec 8)) (j t' : Nat) (v : BitVec 8) :
    (tlabelTs σ tvs)[j]? = some (t', v) → ∃ t, tvs[j]? = some (t, v) ∧ t' = σ t := by
  unfold tlabelTs
  rw [List.getElem?_map]
  cases hj : tvs[j]? with
  | none => intro h; cases h
  | some p =>
    obtain ⟨t, v'⟩ := p
    intro h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨t, rfl, rfl⟩

theorem aevPostExt {D : Type} (σ σ' : Nat → Nat) (ev : Aev D) (w : Wstate) :
    (∀ t, aevTsOccurs ev t → σ t = σ' t) →
    aevPost σ ev w = aevPost σ' ev w := by
  intro hag
  obtain ⟨lb, ts, dd⟩ := ev
  have hread : ∀ base tvs, lbReads lb = tvsReads base tvs →
      (tvs.map Prod.fst).map σ = (tvs.map Prod.fst).map σ' := by
    intro base tvs hlb
    apply list_fmap_ext
    intro i u hu
    apply hag
    left
    obtain ⟨a, ha⟩ := tvsFstReads base tvs i u hu
    exact ⟨a, by rw [show (⟨lb, ts, dd⟩ : Aev D).aeLb = lb from rfl, hlb]; exact ha⟩
  have hfl : ∀ t, ts = some t → σ t = σ' t := fun t ht => hag t (Or.inr ht)
  cases lb with
  | LSilent => rfl
  | LLoad aq lat base tvs asrc =>
    simp only [aevPost]; rw [hread base tvs rfl]
  | LStore rl base data asrc vsrc =>
    cases ts with
    | none => rfl
    | some t => simp only [aevPost]; rw [hfl t rfl]
  | LRmw aq rl base tvs data asrc vsrc =>
    cases ts with
    | none => rfl
    | some t => simp only [aevPost]; rw [hread base tvs rfl, hfl t rfl]
  | LFence => rfl
  | LDev => rfl
  -- the three dependency-only arms are σ-FREE
  | LRegW => rfl
  | LCtrl => rfl
  | LInstr => rfl
  -- THE RMW SPLIT (S2): `LLoad`'s / `LStore`'s arm verbatim
  | LExLoad xaq xbase xtvs xasrc =>
    simp only [aevPost]; rw [hread xbase xtvs rfl]
  | LExStore rl base data asrc vsrc =>
    cases ts with
    | none => rfl
    | some t => simp only [aevPost]; rw [hfl t rfl]
  -- O2 (deviation 4): the fetch is the identity
  | LIFetch => rfl

theorem aevsPostExt {D : Type} (σ σ' : Nat → Nat) (evs : List (Aev D)) (w : Wstate) :
    (∀ t, evTsOccurs evs t → σ t = σ' t) →
    aevsPost σ evs w = aevsPost σ' evs w := by
  induction evs generalizing w with
  | nil => intro _; rfl
  | cons ev evs ih =>
    intro hag
    show aevsPost σ evs (aevPost σ ev w) = aevsPost σ' evs (aevPost σ' ev w)
    rw [aevPostExt σ σ' ev w (fun t ht => hag t (evTsOccursCons ev evs t (Or.inl ht)))]
    exact ih _ (fun t ht => hag t (evTsOccursCons ev evs t (Or.inr ht)))

/-- Every element of a read floor is a LEAF of the state it is computed from. -/
theorem lfloorLeaf (S : Lstate) (aq : Bool) (a : Int) (t : Nat) :
    t ∈ lfloor S aq a → lstateLeaf S t := by
  unfold lfloor
  intro ht
  rcases List.mem_append.1 ht with ht | ht
  · exact lloadVpreLeaf _ _ _ ht
  · exact lcohLeaf _ _ _ ht


/-! ## LAYER 3: the simulation invariant

TIMESTAMP OBLIVIOUSNESS (worklist finding (v)): the pf witness steps the program
with π-RETIMED labels, so `robust` is only provable for programs that do not
branch on a timestamp.  The Sail instantiation satisfies this trivially. -/

def tsOblivious {P D : Type} (pstep : P → D → Wlabel → P → D → Prop) : Prop :=
  (∀ (p : P) (d : D) (aq lat : Bool) (base : Int) (tvs tvs' : List (Nat × BitVec 8))
     (asrc : List Dsrc) (p' : P) (d' : D), tvs.map Prod.snd = tvs'.map Prod.snd →
     pstep p d (LLoad aq lat base tvs asrc) p' d' →
     pstep p d (LLoad aq lat base tvs' asrc) p' d') ∧
  (∀ (p : P) (d : D) (aq rl : Bool) (base : Int) (tvs tvs' : List (Nat × BitVec 8))
     (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (p' : P) (d' : D),
     tvs.map Prod.snd = tvs'.map Prod.snd →
     pstep p d (LRmw aq rl base tvs data asrc vsrc) p' d' →
     pstep p d (LRmw aq rl base tvs' data asrc vsrc) p' d') ∧
  -- THE RMW SPLIT (S4): the EXCLUSIVE READ is retimed by the replay just as a
  -- plain load is.
  (∀ (p : P) (d : D) (aq : Bool) (base : Int) (tvs tvs' : List (Nat × BitVec 8))
     (asrc : List Dsrc) (p' : P) (d' : D), tvs.map Prod.snd = tvs'.map Prod.snd →
     pstep p d (LExLoad aq base tvs asrc) p' d' →
     pstep p d (LExLoad aq base tvs' asrc) p' d') ∧
  -- O2 (deviation 4, Lean-only): the FETCH is retimed likewise.
  (∀ (p : P) (d : D) (base : Int) (tvs tvs' : List (Nat × BitVec 8)) (p' : P) (d' : D),
     tvs.map Prod.snd = tvs'.map Prod.snd →
     pstep p d (LIFetch base tvs) p' d' →
     pstep p d (LIFetch base tvs') p' d')

/-- (Lean-only, deviation 4) THE FETCH-SOURCE PREMISE: every nonzero timestamp an
i-cache fetch answers is fulfilled by an event `tc gdep2`-before the fetch (a
fetch is not a reads-of source, so the graph itself does not order them). -/
def fetchSrcOk {P D : Type} (TS : Ptraces P D) : Prop :=
  ∀ (e : Gev) (base : Int) (tvs : List (Nat × BitVec 8)) (j t : Nat) (v : BitVec 8),
    gevLb TS e = some (LIFetch base tvs) → tvs[j]? = some (t, v) → 0 < t →
    ∃ er, gevTs TS er = some t ∧ tc (gdep2 TS) er e

/-- …vacuous for a program that never fetches (Lean-only, deviation 4). -/
theorem fetchSrcOkNoFetch {P D : Type} (TS : Ptraces P D) :
    (∀ (e : Gev) (base : Int) (tvs : List (Nat × BitVec 8)),
       gevLb TS e ≠ some (LIFetch base tvs)) →
    fetchSrcOk TS :=
  fun h e base tvs _ _ _ hl => (h e base tvs hl).elim

section sim

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)
variable (TS : Ptraces P D) (DS : Pdevs D) (img : Image) (d0 : D) (ps : List P)

/-! ### THE FABRIC HALF OF THE INVARIANT -/

def qdev (dn : List Gev) (n : Nat) : Prop :=
  ∀ (m : Nat) (e : Gev), DS.pdOrd[m]? = some e → (e ∈ dn ↔ m < n)

def qfab (dn : List Gev) (d : D) : Prop :=
  ∃ n, qdev DS dn n ∧ d = devAt TS DS n

theorem qfabInit (hd0 : DS.pdInit = d0) : qfab TS DS [] d0 := by
  refine ⟨0, fun m e _ => ⟨fun h => by simp at h, fun h => by omega⟩, ?_⟩
  show d0 = DS.pdInit
  rw [hd0]

/-- The witness never lists a DEV-FREE event (W1). -/
theorem pdOrdNotFree (hwit : ptracesWit TS DS) (m : Nat) (e : Gev) (ev : Aev D) :
    DS.pdOrd[m]? = some e → gevEv TS e = some ev → ev.aeDev = none → False := by
  intro hm hev hnone
  obtain ⟨hW1, _⟩ := hwit
  obtain ⟨ev', hev', hs⟩ := hW1 m e hm
  rw [gevEvEvAt, hev'] at hev
  cases hev
  rw [hnone] at hs
  cases hs

/-- THE POSITION OF THE EVENT BEING PROCESSED. -/
theorem qdevIndex (hwit : ptracesWit TS DS) (dn : List Gev) (n : Nat) (e : Gev) (m : Nat) :
    qdev DS dn n → e ∉ dn →
    (∀ e', gdep3 TS DS e' e → gevWf TS e' → e' ∈ dn) →
    DS.pdOrd[m]? = some e → n = m := by
  intro hqd hnin hpre hm
  have hle : n ≤ m := by
    rcases Nat.lt_or_ge m n with h | h
    · exact absurd ((hqd m e hm).2 h) hnin
    · exact h
  cases m with
  | zero => omega
  | succ m' =>
    have hlt := lookup_lt_Some hm
    obtain ⟨e', he'⟩ := Option.isSome_iff_exists.1
      (lookup_lt_is_Some_2 (l := DS.pdOrd) (i := m') (by omega))
    have hin : e' ∈ dn :=
      hpre e' (gdevGdep3 TS DS e' e ⟨m', he', hm⟩) (gevDevWf TS e' (pdOrdDev TS DS m' e' hwit he'))
    have := (hqd m' e' he').1 hin
    omega

/-- THE HEART OF G4. -/
theorem qfabStep (hwit : ptracesWit TS DS) (dn : List Gev) (e : Gev) (T : Atrace P D)
    (ev : Aev D) (ag : Wpagent P) (st' : P) (cf : Wpcfg P D) :
    e ∉ dn →
    (∀ e', gdep3 TS DS e' e → gevWf TS e' → e' ∈ dn) →
    TS.ptTrs[e.1]? = some T → T.atEvs[e.2]? = some ev →
    astepProg pstep ag ev st' →
    qfab TS DS dn cf.pcDev →
    ∃ d', pstep ag.paSt cf.pcDev ev.aeLb st' d' ∧ qfab TS DS (dn ++ [e]) d' := by
  intro hnin hpre hT hev hprog ⟨n, hqd, hfab⟩
  have hgev : gevEv TS e = some ev := by simp [gevEv, hT, hev]
  have hea : evAt TS e = some ev := hgev
  have hwit' := hwit
  obtain ⟨hW1, hW2, hW3, hW4⟩ := hwit'
  unfold astepProg at hprog
  cases hdd : ev.aeDev with
  | some dd =>
    -- FABRIC-TOUCHING: replayed AT ITS RECORDED FABRIC
    simp only [hdd] at hprog
    obtain ⟨m, hm⟩ := hW2 e.1 e.2 ev hea (by rw [hdd]; rfl)
    have hm' : DS.pdOrd[m]? = some e := hm
    have hn : n = m := qdevIndex TS DS hwit dn n e m hqd hnin hpre hm'
    subst hn
    have hdin := hW4 n e hm'
    have hfst : dd.1 = devAt TS DS n := by
      simp [evDin, hea, hdd] at hdin
      exact hdin
    refine ⟨dd.2, ?_, n + 1, ?_, ?_⟩
    · rw [hfab, ← hfst]; exact hprog
    · intro m0 e0 hm0
      rw [List.mem_append, List.mem_singleton]
      constructor
      · rintro (hin | rfl)
        · have := (hqd m0 e0 hm0).1 hin; omega
        · have := pdOrdIndexInj TS DS m0 n e0 hwit hm0 hm'; omega
      · intro hlt
        rcases Nat.lt_or_ge m0 n with h | h
        · exact Or.inl ((hqd m0 e0 hm0).2 h)
        · have h' : m0 = n := by omega
          subst h'
          rw [hm'] at hm0
          cases hm0
          exact Or.inr rfl
    · simp [devAt, hm', evDout, hea, hdd]
  | none =>
    -- DEV-FREE: the fold, and the fabric, stand still
    simp only [hdd] at hprog
    refine ⟨cf.pcDev, hprog _, n, ?_, hfab⟩
    intro m0 e0 hm0
    rw [List.mem_append, List.mem_singleton]
    constructor
    · rintro (hin | rfl)
      · exact (hqd m0 e0 hm0).1 hin
      · exact (pdOrdNotFree TS DS hwit m0 e0 ev hm0 hgev hdd).elim
    · intro hlt; exact Or.inl ((hqd m0 e0 hm0).2 hlt)

/-! ### The order half of the invariant -/

def qorder (dn : List Gev) : Prop :=
  dn.Nodup ∧
  (∀ e, e ∈ dn → gevWf TS e) ∧
  (∀ x, x ∈ dn → ∀ y, gdep2 TS y x → gevWf TS y → y ∈ dn) ∧
  (∀ (n : Nat) y, dn[n]? = some y → ∀ x, gdep2 TS x y → ∃ i, i < n ∧ dn[i]? = some x) ∧
  (∀ j k, (j, k) ∈ dn ↔ (gevWf TS (j, k) ∧ k < nproc dn j))

/-- The pf-configuration half — the last clause is G4's FABRIC CLAUSE. -/
def qcfg (dn : List Gev) (cf : Wpcfg P D) : Prop :=
  rtc (wpPfRun pstep pcls) (wpInit img d0 ps) cf ∧
  cf.pcImg = img ∧ cf.pcLog = WeakRobustSim.pfLog TS dn ∧
  cf.pcAgs.length = ps.length ∧
  (∀ (j : Nat) (T : Atrace P D), TS.ptTrs[j]? = some T →
     ∃ agn, T.atAgs[nproc dn j]? = some agn ∧
       cf.pcAgs[j]?
       = some ⟨agn.paSt, aevsPost (pi TS dn) (T.atEvs.take (nproc dn j)) wsInit, ∅⟩) ∧
  qfab TS DS dn cf.pcDev

def Qinv (dn : List Gev) : Prop := qorder TS dn ∧ ∃ cf, qcfg pstep pcls TS DS img d0 ps dn cf

/-! ### What the order half buys -/

theorem qorderDc (dn : List Gev) (x y : Gev) :
    qorder TS dn → x ∈ dn → gdep2 TS y x → gevWf TS y → y ∈ dn :=
  fun hq hx hd hw => hq.2.2.1 x hx y hd hw

theorem qorderWf (dn : List Gev) (e : Gev) : qorder TS dn → e ∈ dn → gevWf TS e :=
  fun hq he => hq.2.1 e he

theorem qorderMem (dn : List Gev) (j k : Nat) :
    qorder TS dn → ((j, k) ∈ dn ↔ (gevWf TS (j, k) ∧ k < nproc dn j)) :=
  fun hq => hq.2.2.2.2 j k

/-- The processing order respects `tc gdep2`. -/
theorem qorderTcIndex (dn : List Gev) (x y : Gev) (n : Nat) :
    qorder TS dn → dn[n]? = some y → tc (gdep2 TS) x y →
    ∃ i, i < n ∧ dn[i]? = some x := by
  intro hq hn htc
  have hpred := hq.2.2.2.1
  induction htc generalizing n with
  | single h => exact hpred n _ hn x h
  | tail _ h ih =>
    obtain ⟨m, hm, hlkm⟩ := hpred n _ hn _ h
    obtain ⟨i, hi, hlki⟩ := ih m hlkm
    exact ⟨i, by omega, hlki⟩

theorem qorderTcIn (dn : List Gev) (x y : Gev) :
    qorder TS dn → y ∈ dn → tc (gdep2 TS) x y → x ∈ dn := by
  intro hq hy htc
  obtain ⟨n, hn⟩ := elem_of_list_lookup_1 hy
  obtain ⟨i, _, hi⟩ := qorderTcIndex TS dn x y n hq hn htc
  exact elem_of_list_lookup_2 hi

/-! ### `fl` / `pfLog` bookkeeping under the invariant -/

theorem flTsPos (hwf : ptracesWf pstep TS) (dn : List Gev) (t : Nat) :
    t ∈ fl TS dn → 0 < t := by
  intro ht
  obtain ⟨e, _, hts⟩ := (elemOfFl TS dn t).1 ht
  exact gevTsPos pstep TS e t hwf hts

theorem NoDupFl (hwf : ptracesWf pstep TS) (dn : List Gev) : qorder TS dn → (fl TS dn).Nodup := by
  intro hq
  exact NoDupOmapInj _ _ hq.1 (fun x y b _ _ hx hy => grfSourceUnique pstep TS x y b hwf hx hy)

theorem piMem (hwf : ptracesWf pstep TS) (dn : List Gev) (i t : Nat) :
    qorder TS dn → (fl TS dn)[i]? = some t → pi TS dn t = i + 1 := by
  intro hq hi
  have hpos := flTsPos pstep TS hwf dn t (elem_of_list_lookup_2 hi)
  exact piLMem _ i t (NoDupFl pstep TS hwf dn hq) hi (by omega)

/-- A processed timestamp names its own pf log position. -/
theorem pfLogPi (hwf : ptracesWf pstep TS) (dn : List Gev) (t : Nat) :
    qorder TS dn → t ∈ fl TS dn →
    0 < pi TS dn t ∧ pi TS dn t ≤ (WeakRobustSim.pfLog TS dn).length ∧
    (WeakRobustSim.pfLog TS dn)[pi TS dn t - 1]? = some (msgAt TS t) := by
  intro hq ht
  obtain ⟨i, hi⟩ := elem_of_list_lookup_1 ht
  have hp := piMem pstep TS hwf dn i t hq hi
  have hlt := lookup_lt_Some hi
  rw [hp, flLen]
  refine ⟨by omega, by omega, ?_⟩
  rw [Nat.add_sub_cancel]
  simp [WeakRobustSim.pfLog, hi]

/-- …and the message it names is the behavior's own. -/
theorem msgAtEq (t : Nat) (m : Wmsg) : TS.ptLog[t - 1]? = some m → msgAt TS t = m := by
  intro h
  simp [msgAt, h]

theorem flMsg (hwf : ptracesWf pstep TS) (dn : List Gev) (t : Nat) :
    qorder TS dn → t ∈ fl TS dn →
    ∃ e, e ∈ dn ∧ gevTs TS e = some t ∧
      TS.ptLog[t - 1]? = some (msgAt TS t) ∧
      (msgAt TS t).wmTid = some e.1 := by
  intro _ ht
  obtain ⟨e, he, hts⟩ := (elemOfFl TS dn t).1 ht
  obtain ⟨base, data, kc, hm⟩ := gevTsMsg pstep TS e t hwf hts
  refine ⟨e, he, hts, ?_, ?_⟩
  · rw [msgAtEq TS t _ hm]; exact hm
  · rw [msgAtEq TS t _ hm]

/-- THE INVERSION the two cruxes run on. -/
theorem pfWritesInInv (hwf : ptracesWf pstep TS) (dn : List Gev) (a : Int) (lo hi : Nat) :
    qorder TS dn → writesIn (WeakRobustSim.pfLog TS dn) a lo hi →
    ∃ that ehat,
      lo < pi TS dn that ∧ pi TS dn that ≤ hi ∧
      ehat ∈ dn ∧ writesB TS a ehat that ∧
      (msgAt TS that).wmTid = some ehat.1 := by
  rintro hq ⟨q, hlo, hhi, m, hm, hb⟩
  unfold WeakRobustSim.pfLog at hm
  rw [List.getElem?_map] at hm
  cases hfl : (fl TS dn)[q - 1]? with
  | none => rw [hfl] at hm; cases hm
  | some that =>
    rw [hfl] at hm
    simp only [Option.map_some, Option.some.injEq] at hm
    subst hm
    have hin : that ∈ fl TS dn := elem_of_list_lookup_2 hfl
    have hpi := piMem pstep TS hwf dn (q - 1) that hq hfl
    have hq1 : q - 1 + 1 = q := by omega
    rw [hq1] at hpi
    obtain ⟨ehat, he, hts, hlog, htid⟩ := flMsg pstep TS hwf dn that hq hin
    refine ⟨that, ehat, by rw [hpi]; exact hlo, by rw [hpi]; exact hhi, he, ⟨hts, _, hlog, hb⟩, htid⟩

/-! ### Leaf/read provenance -/

theorem readSourceIn (hwf : ptracesWf pstep TS) (hwfl : writesFulfilled TS) (dn : List Gev)
    (e : Gev) (a : Int) (t : Nat) :
    (∀ e', gdep2 TS e' e → gevWf TS e' → e' ∈ dn) →
    gevReads TS e a t → 0 < t →
    ∃ er, er ∈ dn ∧ writesB TS a er t := by
  intro hpre hr hpos
  obtain ⟨er, hw, hrf⟩ := gevReadsSource pstep TS e a t hwf hwfl hr hpos
  exact ⟨er, hpre er (grfGdep2 TS er e hrf) (writesBWf TS a er t hw), hw⟩

theorem readTsInFl (hwf : ptracesWf pstep TS) (hwfl : writesFulfilled TS) (dn : List Gev)
    (e : Gev) (a : Int) (t : Nat) :
    qorder TS dn →
    (∀ e', gdep2 TS e' e → gevWf TS e' → e' ∈ dn) →
    gevReads TS e a t → 0 < t → t ∈ fl TS dn := by
  intro _ hpre hr hpos
  obtain ⟨er, he, hw⟩ := readSourceIn pstep TS hwf hwfl dn e a t hpre hr hpos
  exact (elemOfFl TS dn t).2 ⟨er, he, hw.1⟩

/-- Every nonzero timestamp occurring in agent `j`'s PROCESSED prefix is in
`fl dn`. -/
theorem occProcessed (hwf : ptracesWf pstep TS) (hwfl : writesFulfilled TS) (dn : List Gev)
    (j : Nat) (T : Atrace P D) (t : Nat) :
    qorder TS dn → TS.ptTrs[j]? = some T →
    evTsOccurs (T.atEvs.take (nproc dn j)) t → 0 < t →
    t ∈ fl TS dn := by
  rintro hq hT ⟨ev, hev, hocc⟩ hpos
  obtain ⟨k, hk, hklt⟩ := elem_of_take.1 hev
  have hgev : gevEv TS (j, k) = some ev := by simp [gevEv, hT, hk]
  have hwfe : gevWf TS (j, k) := by unfold gevWf; rw [hgev]; rfl
  have hin : (j, k) ∈ dn := (qorderMem TS dn j k hq).2 ⟨hwfe, hklt⟩
  rcases hocc with ⟨a, ha⟩ | hts
  · have hr : gevReads TS (j, k) a t := ⟨ev.aeLb, by simp [gevLb, hgev], ha⟩
    exact readTsInFl pstep TS hwf hwfl dn (j, k) a t hq
      (fun e' hd hw' => qorderDc TS dn (j, k) e' hq hin hd hw') hr hpos
  · exact (elemOfFl TS dn t).2 ⟨(j, k), hin, by simp [gevTs, hgev, hts]⟩

/-- …hence `pi` is STABLE on the processed prefixes as `dn` grows. -/
theorem wsStable (hwf : ptracesWf pstep TS) (hwfl : writesFulfilled TS) (dn l : List Gev)
    (j : Nat) (T : Atrace P D) :
    qorder TS dn → TS.ptTrs[j]? = some T →
    aevsPost (pi TS (dn ++ l)) (T.atEvs.take (nproc dn j)) wsInit
    = aevsPost (pi TS dn) (T.atEvs.take (nproc dn j)) wsInit := by
  intro hq hT
  apply aevsPostExt
  intro t hocc
  apply piApp
  by_cases ht : t = 0
  · exact Or.inr ht
  · exact Or.inl (occProcessed pstep TS hwf hwfl dn j T t hq hT hocc (by omega))

/-- π ORDERS the timestamps of `tc gdep2`-related PROCESSED events. -/
theorem piLtOfTc (hwf : ptracesWf pstep TS) (dn : List Gev) (e1 e2 : Gev) (t1 t2 : Nat) :
    qorder TS dn → e2 ∈ dn → tc (gdep2 TS) e1 e2 →
    gevTs TS e1 = some t1 → gevTs TS e2 = some t2 →
    pi TS dn t1 < pi TS dn t2 := by
  intro hq he2 htc h1 h2
  obtain ⟨n2, hn2⟩ := elem_of_list_lookup_1 he2
  obtain ⟨n1, hlt, hn1⟩ := qorderTcIndex TS dn e1 e2 n2 hq hn2 htc
  have hf1 := flLookupFpos TS dn n1 e1 t1 hn1 h1
  have hf2 := flLookupFpos TS dn n2 e2 t2 hn2 h2
  have hp1 := piMem pstep TS hwf dn _ t1 hq hf1
  have hp2 := piMem pstep TS hwf dn _ t2 hq hf2
  have hfl := fposLt TS dn n1 n2 e1 t1 hn1 h1 hlt
  omega

/-- The co-order version, packaged against `Hco`. -/
theorem piLtOfCo (hwf : ptracesWf pstep TS) (hco : ∀ a, coTc TS a) (dn : List Gev) (a : Int)
    (e1 e2 : Gev) (t1 t2 : Nat) :
    qorder TS dn → e2 ∈ dn →
    writesB TS a e1 t1 → writesB TS a e2 t2 → t1 < t2 →
    pi TS dn t1 < pi TS dn t2 := by
  intro hq he2 hw1 hw2 hlt
  exact piLtOfTc pstep TS hwf dn e1 e2 t1 t2 hq he2
    (tcGdepGdep2 TS e1 e2 (hco a e1 e2 t1 t2 hw1 hw2 hlt)) hw1.1 hw2.1

/-! ### The per-agent prefix fact, and the order step -/

/-- THE EVENT BEING PROCESSED IS THE NEXT ONE OF ITS AGENT. -/
theorem nprocCur (dn : List Gev) (e : Gev) :
    qorder TS dn → gevWf TS e → e ∉ dn →
    (∀ e', gdep2 TS e' e → gevWf TS e' → e' ∈ dn) →
    nproc dn e.1 = e.2 := by
  intro hq hwfe hnin hpre
  obtain ⟨j, k⟩ := e
  show nproc dn j = k
  have hle : nproc dn j ≤ k := by
    rcases Nat.lt_or_ge k (nproc dn j) with hlt | hge
    · exact absurd ((qorderMem TS dn j k hq).2 ⟨hwfe, hlt⟩) hnin
    · exact hge
  rcases Nat.lt_or_ge (nproc dn j) k with hlt | hge
  · exfalso
    have hwf' : gevWf TS (j, nproc dn j) := by
      obtain ⟨T, hT, hk⟩ := (gevWfBounds TS (j, k)).1 hwfe
      exact (gevWfBounds TS (j, nproc dn j)).2 ⟨T, hT, by simp at hk ⊢; omega⟩
    have hin : (j, nproc dn j) ∈ dn :=
      hpre _ (gpoGdep2 TS _ _ ⟨rfl, hlt, hwf', hwfe⟩) hwf'
    have := ((qorderMem TS dn j (nproc dn j) hq).1 hin).2
    omega
  · omega

theorem qorderStep (dn : List Gev) (e : Gev) :
    qorder TS dn → gevWf TS e → e ∉ dn →
    (∀ e', gdep2 TS e' e → gevWf TS e' → e' ∈ dn) →
    qorder TS (dn ++ [e]) := by
  intro hq hwfe hnin hpre
  have hnp := nprocCur TS dn e hq hwfe hnin hpre
  obtain ⟨hnd, hwfs, hdc, hpred, hmem⟩ := hq
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine NoDup_app.2 ⟨hnd, ?_, NoDup_singleton⟩
    intro x hx hx'
    rw [List.mem_singleton] at hx'
    subst hx'
    exact hnin hx
  · intro e' he'
    rcases List.mem_append.1 he' with he' | he'
    · exact hwfs e' he'
    · rw [List.mem_singleton] at he'; subst he'; exact hwfe
  · intro x hx y hd hy
    rw [List.mem_append]
    left
    rcases List.mem_append.1 hx with hx | hx
    · exact hdc x hx y hd hy
    · rw [List.mem_singleton] at hx; subst hx; exact hpre y hd hy
  · intro n y hn x hd
    rcases Nat.lt_or_ge n dn.length with hlt | hge
    · rw [lookup_app_l hlt] at hn
      obtain ⟨i, hi, hlki⟩ := hpred n y hn x hd
      exact ⟨i, hi, by rw [lookup_app_l (lookup_lt_Some hlki)]; exact hlki⟩
    · have hn' : n = dn.length := by
        have := lookup_lt_Some hn
        simp at this; omega
      subst hn'
      rw [lookup_app_r (Nat.le_refl _), Nat.sub_self] at hn
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst hn
      have hxin : x ∈ dn := hpre x hd (gdep2Wf TS x _ hd).1
      obtain ⟨i, hi⟩ := elem_of_list_lookup_1 hxin
      exact ⟨i, lookup_lt_Some hi, by rw [lookup_app_l (lookup_lt_Some hi)]; exact hi⟩
  · intro j k
    obtain ⟨j0, k0⟩ := e
    simp only at hnp
    by_cases hj : j = j0
    · subst hj
      have hnn : nproc (dn ++ [(j, k0)]) j = nproc dn j + 1 := nprocAppEq dn (j, k0)
      rw [hnn, hnp, List.mem_append, List.mem_singleton]
      constructor
      · rintro (hin | hin)
        · obtain ⟨hw, hlt⟩ := (hmem j k).1 hin
          exact ⟨hw, by omega⟩
        · cases hin; exact ⟨hwfe, by omega⟩
      · rintro ⟨hw, hlt⟩
        by_cases hk : k = k0
        · subst hk; exact Or.inr rfl
        · exact Or.inl ((hmem j k).2 ⟨hw, by omega⟩)
    · have hnn : nproc (dn ++ [(j0, k0)]) j = nproc dn j := nprocAppNe dn (j0, k0) j hj
      rw [hnn, List.mem_append, List.mem_singleton]
      constructor
      · rintro (hin | hin)
        · exact (hmem j k).1 hin
        · cases hin; exact absurd rfl hj
      · intro h; exact Or.inl ((hmem j k).2 h)

/-! ### CRUX 1+2: the transported READ (values and readability) -/

/-- (Lean-only helper) THE VALUES CRUX: a timestamp that is 0 or processed reads
the same byte value in the pf log at its π-image. -/
theorem logBytePf (hwf : ptracesWf pstep TS) (himg : TS.ptImg = img) (dn : List Gev) (t : Nat)
    (a : Int) (v : BitVec 8) :
    qorder TS dn → (t = 0 ∨ t ∈ fl TS dn) →
    logByte TS.ptImg TS.ptLog t a = some v →
    logByte img (WeakRobustSim.pfLog TS dn) (pi TS dn t) a = some v := by
  intro hq ht hval
  rcases ht with rfl | hin
  · rw [pi0, logByte0]
    rw [logByte0, himg] at hval
    exact hval
  · obtain ⟨hp1, _, hp3⟩ := pfLogPi pstep TS hwf dn t hq hin
    rw [logBytePos img _ _ (msgAt TS t) a hp1 hp3]
    have hpos := flTsPos pstep TS hwf dn t hin
    obtain ⟨p, rfl⟩ : ∃ p, t = p + 1 := ⟨t - 1, by omega⟩
    rw [logByteS] at hval
    cases hm : TS.ptLog[p]? with
    | none => rw [hm] at hval; cases hval
    | some m =>
      rw [hm] at hval
      rw [msgAtEq TS (p + 1) m (by rw [Nat.add_sub_cancel]; exact hm)]
      exact hval

theorem readOkPf (hwf : ptracesWf pstep TS) (hwsi : ptracesWsInit TS) (hco : ∀ a, coTc TS a)
    (hwfl : writesFulfilled TS) (himg : TS.ptImg = img)
    (dn : List Gev) (e : Gev) (T : Atrace P D) (ev : Aev D) (ag : Wpagent P) (l : Wlabel)
    (base : Int) (tvs : List (Nat × BitVec 8)) (lat : Bool) (ws : Wstate) :
    qorder TS dn →
    (∀ e', gdep2 TS e' e → gevWf TS e' → e' ∈ dn) →
    nproc dn e.1 = e.2 →
    TS.ptTrs[e.1]? = some T →
    T.atEvs[e.2]? = some ev →
    T.atAgs[e.2]? = some ag →
    ev.aeLb = l →
    (match l with
     | LLoad .. | LRmw .. | LExLoad .. => True
     | LSilent | LStore .. | LFence .. | LDev | LRegW .. | LCtrl _ | LInstr | LExStore ..
     | LIFetch .. => False) →
    lbReads l = tvsReads base tvs →
    readOkD TS.ptImg TS.ptLog ag.paWs (WeakRobustAcyc.lbAq l) lat base tvs
      (srcsView ag.paWs (lbRasrc l)) →
    ws = aevsPost (pi TS dn) (T.atEvs.take e.2) wsInit →
    readOkD img (WeakRobustSim.pfLog TS dn) ws (WeakRobustAcyc.lbAq l) false base
      (tlabelTs (pi TS dn) tvs) (srcsView ws (lbRasrc l)) := by
  intro hq hpre hnp hT hev hag hlbe hrdl hreads hro hws
  have hgev : gevEv TS e = some ev := by simp [gevEv, hT, hev]
  have hlb : gevLb TS e = some l := by simp [gevLb, hgev, hlbe]
  have hrel : lrel (pi TS dn) (preLstate TS e) ws := by
    rw [hws, preLstateTr TS e T hT]
    exact lrelAevsPostInit _ _ (piSigmaOk TS dn)
  have hleaves : ∀ a, rdLeaves TS e a
      = lsrcsView (preLstate TS e) (lbRasrc l) ++ lfloor (preLstate TS e) (WeakRobustAcyc.lbAq l) a := by
    intro a
    unfold rdLeaves
    rw [hlb]
    cases l <;> first | rfl | exact False.elim hrdl
  have hfpf : ∀ a, max (loadVpreD ws (WeakRobustAcyc.lbAq l) (srcsView ws (lbRasrc l))) (coh ws a)
      = lval (pi TS dn) (rdLeaves TS e a) := by
    intro a
    rw [hleaves a]
    exact lrelFloorD _ _ _ _ _ _ hrel
  have hfbeh : ∀ a, rdFloor TS e a
      = max (loadVpreD ag.paWs (WeakRobustAcyc.lbAq l) (srcsView ag.paWs (lbRasrc l)))
          (coh ag.paWs a) :=
    fun a => rdFloorWs pstep TS e T ag l a hwf hwsi hT hag hlb hrdl
  intro jb t' v hjb
  obtain ⟨t, htv, rfl⟩ := tlabelTsLookupInv (pi TS dn) tvs jb t' v hjb
  obtain ⟨hval, hrd, _⟩ := hro jb t v htv
  have hreadin : (base + (jb : Int), t) ∈ lbReads l := by
    rw [hreads]; exact (memTvsReads _ _ _ _).2 ⟨jb, v, htv, rfl⟩
  have hgr : gevReads TS e (base + (jb : Int)) t := ⟨l, hlb, hreadin⟩
  -- ---- VALUES ----
  have hvalpf : logByte img (WeakRobustSim.pfLog TS dn) (pi TS dn t) (base + (jb : Int)) = some v := by
    refine logBytePf pstep TS img hwf himg dn t _ v hq ?_ hval
    by_cases ht0 : t = 0
    · exact Or.inl ht0
    · exact Or.inr (readTsInFl pstep TS hwf hwfl dn e _ t hq hpre hgr (by omega))
  -- ---- READABILITY ----
  have hnw : ¬ writesIn (WeakRobustSim.pfLog TS dn) (base + (jb : Int)) (pi TS dn t)
      (max (loadVpreD ws (WeakRobustAcyc.lbAq l) (srcsView ws (lbRasrc l)))
        (coh ws (base + (jb : Int)))) := by
    rw [hfpf (base + (jb : Int))]
    intro hw
    obtain ⟨that, ehat, hlo, hhi, hehat, hwb, _⟩ :=
      pfWritesInInv pstep TS hwf dn (base + (jb : Int)) _ _ hq hw
    have hthatpos := writesBPos pstep TS _ _ _ hwf hwb
    rcases Nat.lt_trichotomy that t with hlt | heq | hgt
    · have htpos : 0 < t := by omega
      obtain ⟨er, her, hwr⟩ := readSourceIn pstep TS hwf hwfl dn e _ t hpre hgr htpos
      have := piLtOfCo pstep TS hwf hco dn _ ehat er that t hq her hwb hwr hlt
      omega
    · subst heq; omega
    · rcases Nat.lt_or_ge (rdFloor TS e (base + (jb : Int))) that with habove | hle
      · have hbound : lval (pi TS dn) (rdLeaves TS e (base + (jb : Int))) < pi TS dn that := by
          refine lvalLt _ _ _ ?_ (piPos TS dn that (by omega))
          intro tstar hstar
          by_cases hs0 : tstar = 0
          · subst hs0; rw [pi0]; exact piPos TS dn that (by omega)
          · have hleaf := rdLeavesLeaf TS e _ tstar hstar
            have hocc := preLstateLeafOccurs TS e T tstar hT hleaf
            rw [← hnp] at hocc
            have hinfl := occProcessed pstep TS hwf hwfl dn e.1 T tstar hq hT hocc (by omega)
            obtain ⟨estar, _, htsstar⟩ := (elemOfFl TS dn tstar).1 hinfl
            refine piLtOfTc pstep TS hwf dn estar ehat tstar that hq hehat ?_ htsstar hwb.1
            exact tc_once (gEGdep2 TS _ _ ⟨e, l, base + (jb : Int), t, tstar, that, hlb, hreadin,
              hstar, by omega, htsstar, hwb.1, hwb.2, habove⟩)
        omega
      · apply hrd.2
        rw [← hfbeh (base + (jb : Int))]
        exact ⟨that, hgt, hle, hwb.2⟩
  exact ⟨hvalpf, ⟨by rw [hvalpf]; rfl, hnw⟩, fun h => by cases h⟩

/-! ### CRUX 3: the transported EXCLUSIVITY WINDOW of an rmw -/

/-- The author-aware form of `pfWritesInInv`. -/
theorem pfWritesInByInv (hwf : ptracesWf pstep TS) (dn : List Gev) (Q : Option Nat → Prop)
    (a : Int) (lo hi : Nat) :
    qorder TS dn → writesInBy (WeakRobustSim.pfLog TS dn) Q a lo hi →
    ∃ that ehat,
      lo < pi TS dn that ∧ pi TS dn that ≤ hi ∧
      ehat ∈ dn ∧ writesB TS a ehat that ∧ Q (some ehat.1) := by
  rintro hq ⟨q, hlo, hhi, m, hm, hb, hQ⟩
  unfold WeakRobustSim.pfLog at hm
  rw [List.getElem?_map] at hm
  cases hfl : (fl TS dn)[q - 1]? with
  | none => rw [hfl] at hm; cases hm
  | some that =>
    rw [hfl] at hm
    simp only [Option.map_some, Option.some.injEq] at hm
    subst hm
    have hin : that ∈ fl TS dn := elem_of_list_lookup_2 hfl
    have hpi := piMem pstep TS hwf dn (q - 1) that hq hfl
    have hq1 : q - 1 + 1 = q := by omega
    rw [hq1] at hpi
    obtain ⟨ehat, he, hts, hlog, htid⟩ := flMsg pstep TS hwf dn that hq hin
    rw [htid] at hQ
    exact ⟨that, ehat, by rw [hpi]; exact hlo, by rw [hpi]; exact hhi, he, ⟨hts, _, hlog, hb⟩, hQ⟩

theorem msgByteRun (base : Int) (data : List (BitVec 8)) (tid : Option Nat) (k : WmClass) (jb : Nat) :
    jb < data.length → (msgByte ⟨base, data, tid, k⟩ (base + (jb : Int))).isSome := by
  intro hj
  have hb : base ≤ base + (jb : Int) := by omega
  have hidx : (base + (jb : Int) - base).toNat = jb := by omega
  simp only [msgByte, if_pos hb, hidx]
  exact lookup_lt_is_Some_2 hj

theorem exclOkPf (hwf : ptracesWf pstep TS) (hco : ∀ a, coTc TS a) (hwfl : writesFulfilled TS)
    (dn : List Gev) (e : Gev) (T : Atrace P D) (ev : Aev D) (ag : Wpagent P)
    (f : Wstate → Wstate) (aq rl : Bool) (base : Int) (tvs : List (Nat × BitVec 8))
    (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (ts : Nat) :
    qorder TS dn →
    e ∉ dn →
    (∀ e', gdep2 TS e' e → gevWf TS e' → e' ∈ dn) →
    TS.ptTrs[e.1]? = some T →
    T.atEvs[e.2]? = some ev →
    ev.aeLb = LRmw aq rl base tvs data asrc vsrc →
    ev.aeTs = some ts →
    astepOk TS.ptImg TS.ptLog e.1 ag ev.aeLb f ev.aeTs →
    exclOk (WeakRobustSim.pfLog TS dn) e.1 base (tlabelTs (pi TS dn) tvs)
      ((WeakRobustSim.pfLog TS dn).length + 1) := by
  intro hq hnin hpre hT hev hlbe htse hok
  have hgev : gevEv TS e = some ev := by simp [gevEv, hT, hev]
  have hgts : gevTs TS e = some ts := by simp [gevTs, hgev, htse]
  have hok' := hok
  rw [hlbe, htse] at hok'
  obtain ⟨ts', kc, hlen, _, hlog, _, _, _, _, heq⟩ := hok'
  cases heq
  intro jb t' v hjb
  obtain ⟨tr, htv, rfl⟩ := tlabelTsLookupInv (pi TS dn) tvs jb t' v hjb
  have hreadin : (base + (jb : Int), tr) ∈ lbReads ev.aeLb := by
    rw [hlbe]; exact (memTvsReads _ _ _ _).2 ⟨jb, v, htv, rfl⟩
  have hgr : gevReads TS e (base + (jb : Int)) tr := ⟨ev.aeLb, by simp [gevLb, hgev], hreadin⟩
  have hjblt : jb < data.length := by rw [← hlen]; exact lookup_lt_Some htv
  have hwbe : writesB TS (base + (jb : Int)) e ts :=
    ⟨hgts, ⟨base, data, some e.1, kc⟩, hlog, msgByteRun base data _ kc jb hjblt⟩
  rw [show (WeakRobustSim.pfLog TS dn).length + 1 - 1 = (WeakRobustSim.pfLog TS dn).length by omega]
  intro hw
  obtain ⟨that, ehat, hlo, hhi, hehat, hwb, hfor⟩ :=
    pfWritesInByInv pstep TS hwf dn _ (base + (jb : Int)) _ _ hq hw
  have hthatpos := writesBPos pstep TS _ _ _ hwf hwb
  rcases Nat.lt_trichotomy that tr with hlt | heq | hgt
  · -- below the read: co-monotonicity puts it below π tr
    have htrpos : 0 < tr := by omega
    obtain ⟨er, her, hwr⟩ := readSourceIn pstep TS hwf hwfl dn e _ tr hpre hgr htrpos
    have := piLtOfCo pstep TS hwf hco dn _ ehat er that tr hq her hwb hwr hlt
    omega
  · subst heq; omega
  · rcases Nat.lt_or_ge (ts - 1) that with habove | hle
    · by_cases hne : that = ts
      · -- the rmw's OWN message: its event is not processed
        subst hne
        have heq3 : ehat = e := grfSourceUnique pstep TS ehat e that hwf hwb.1 hgts
        subst heq3
        exact hnin hehat
      · -- strictly above: co would drag the current event into `dn`
        have htc : tc (gdep TS) e ehat := hco (base + (jb : Int)) e ehat ts that hwbe hwb (by omega)
        exact hnin (qorderTcIn TS dn e ehat hq hehat (tcGdepGdep2 TS e ehat htc))
    · -- the BEHAVIOR's own exclusivity window
      apply astepOkReadExcl TS.ptImg TS.ptLog e.1 ag ev.aeLb f ts tr (base + (jb : Int))
        (by rw [← htse]; exact hok) hreadin
      obtain ⟨e2, _, hts2, hlog2, htid2⟩ :=
        flMsg pstep TS hwf dn that hq ((elemOfFl TS dn that).2 ⟨ehat, hehat, hwb.1⟩)
      obtain ⟨hts_, m, hm, hb⟩ := hwb
      have hmm : msgAt TS that = m := by rw [hlog2] at hm; injection hm
      have heq2 : e2 = ehat := grfSourceUnique pstep TS e2 ehat that hwf hts2 hts_
      refine ⟨that, hgt, hle, m, hm, hb, ?_⟩
      show m.wmTid ≠ some e.1
      rw [← hmm, htid2, heq2]
      exact hfor

/-! ### CRUX 3, SPLIT FORM (T2-2a): the transported EXCLUSIVITY WINDOW OF A PAIR -/

theorem exclOkTsPf (hwf : ptracesWf pstep TS) (hco : ∀ a, coTc TS a) (hwfl : writesFulfilled TS)
    (dn : List Gev) (e e0 : Gev) (base : Int) (rts : List Nat) (ts : Nat) :
    qorder TS dn →
    e ∉ dn →
    e0 ∈ dn →
    (∀ (jb t : Nat), rts[jb]? = some t → gevReads TS e0 (base + (jb : Int)) t) →
    gevTs TS e = some ts →
    (∀ jb : Nat, jb < rts.length → writesB TS (base + (jb : Int)) e ts) →
    exclOkTs TS.ptLog e.1 base rts ts →
    exclOkTs (WeakRobustSim.pfLog TS dn) e.1 base (rts.map (pi TS dn))
      ((WeakRobustSim.pfLog TS dn).length + 1) := by
  intro hq hnin he0 hrd hgts hwbe hex
  have hpre0 : ∀ e', gdep2 TS e' e0 → gevWf TS e' → e' ∈ dn :=
    fun e' hd hw' => qorderDc TS dn e0 e' hq he0 hd hw'
  intro jb t' hjb
  rw [List.getElem?_map] at hjb
  cases htr : rts[jb]? with
  | none => rw [htr] at hjb; cases hjb
  | some tr =>
  rw [htr] at hjb
  simp only [Option.map_some, Option.some.injEq] at hjb
  subst hjb
  have hgr : gevReads TS e0 (base + (jb : Int)) tr := hrd jb tr htr
  have hwbes : writesB TS (base + (jb : Int)) e ts := hwbe jb (lookup_lt_Some htr)
  rw [show (WeakRobustSim.pfLog TS dn).length + 1 - 1 = (WeakRobustSim.pfLog TS dn).length by omega]
  intro hw
  obtain ⟨that, ehat, hlo, hhi, hehat, hwb, hfor⟩ :=
    pfWritesInByInv pstep TS hwf dn _ (base + (jb : Int)) _ _ hq hw
  have hthatpos := writesBPos pstep TS _ _ _ hwf hwb
  rcases Nat.lt_trichotomy that tr with hlt | heq | hgt
  · have htrpos : 0 < tr := by omega
    obtain ⟨er, her, hwr⟩ := readSourceIn pstep TS hwf hwfl dn e0 _ tr hpre0 hgr htrpos
    have := piLtOfCo pstep TS hwf hco dn _ ehat er that tr hq her hwb hwr hlt
    omega
  · subst heq; omega
  · rcases Nat.lt_or_ge (ts - 1) that with habove | hle
    · by_cases hne : that = ts
      · subst hne
        have heq3 : ehat = e := grfSourceUnique pstep TS ehat e that hwf hwb.1 hgts
        subst heq3
        exact hnin hehat
      · have htc : tc (gdep TS) e ehat :=
          hco (base + (jb : Int)) e ehat ts that hwbes hwb (by omega)
        exact hnin (qorderTcIn TS dn e ehat hq hehat (tcGdepGdep2 TS e ehat htc))
    · -- the BEHAVIOR's own exclusivity window, on the RESERVATION
      apply hex jb tr htr
      obtain ⟨e2, _, hts2, hlog2, htid2⟩ :=
        flMsg pstep TS hwf dn that hq ((elemOfFl TS dn that).2 ⟨ehat, hehat, hwb.1⟩)
      obtain ⟨hts_, m, hm, hb⟩ := hwb
      have hmm : msgAt TS that = m := by rw [hlog2] at hm; injection hm
      have heq2 : e2 = ehat := grfSourceUnique pstep TS e2 ehat that hwf hts2 hts_
      refine ⟨that, hgt, hle, m, hm, hb, ?_⟩
      show m.wmTid ≠ some e.1
      rw [← hmm, htid2, heq2]
      exact hfor

/-! ### THE REPLAYED AGENT STATE AGREES WITH THE RECORDED ONE ON `wRelp` -/

theorem replayWsRelp (hwf : ptracesWf pstep TS) (hwsi : ptracesWsInit TS) (j k : Nat)
    (T : Atrace P D) (ag : Wpagent P) (σ : Nat → Nat) :
    TS.ptTrs[j]? = some T → T.atAgs[k]? = some ag →
    ag.paWs.wRelp = (aevsPost σ (T.atEvs.take k) wsInit).wRelp := by
  intro hT hag
  have hwfi := hwf j T hT
  obtain ⟨ag0, hag0⟩ := Option.isSome_iff_exists.1
    (atraceFirstIsSome pstep TS.ptImg TS.ptLog j T hwfi)
  have hws0 : ag0.paWs = wsInit := hwsi j T ag0 hT hag0
  have hfold := astepsWsFold pstep TS.ptImg TS.ptLog j T.atAgs T.atEvs k ag0 ag hwfi hag0 hag
  rw [hfold, hws0]
  exact wRelpAevsPostIndep id σ _ wsInit wsInit rfl

/-- …AND ITS RESERVATION IS THE σ-RETIMED IMAGE (T2-2a). -/
theorem replayWsRes (hwf : ptracesWf pstep TS) (hwsi : ptracesWsInit TS) (j k : Nat)
    (T : Atrace P D) (ag : Wpagent P) (σ : Nat → Nat) :
    TS.ptTrs[j]? = some T → T.atAgs[k]? = some ag →
    resCols σ (aevsPost σ (T.atEvs.take k) wsInit).wRes ag.paWs.wRes := by
  intro hT hag
  have hwfi := hwf j T hT
  obtain ⟨ag0, hag0⟩ := Option.isSome_iff_exists.1
    (atraceFirstIsSome pstep TS.ptImg TS.ptLog j T hwfi)
  have hws0 : ag0.paWs = wsInit := hwsi j T ag0 hT hag0
  have hfold := astepsWsFold pstep TS.ptImg TS.ptLog j T.atAgs T.atEvs k ag0 ag hwfi hag0 hag
  rw [hfold, hws0]
  exact aevsPostResInit σ _

/-- …AND THE RECORDED RESERVATION NAMES AN EARLIER EVENT OF THE SAME AGENT. -/
theorem replayWsResSrc (hwf : ptracesWf pstep TS) (hwsi : ptracesWsInit TS) (j k : Nat)
    (T : Atrace P D) (ag : Wpagent P) (R : Wresv) :
    TS.ptTrs[j]? = some T → T.atAgs[k]? = some ag →
    ag.paWs.wRes = some R →
    ∃ (m : Nat) (ev : Aev D) (aq : Bool) (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc),
      m < k ∧ T.atEvs[m]? = some ev ∧
      ev.aeLb = LExLoad aq R.rvBase tvs asrc ∧ R.rvTs = tvs.map Prod.fst := by
  intro hT hag hres
  have hwfi := hwf j T hT
  obtain ⟨ag0, hag0⟩ := Option.isSome_iff_exists.1
    (atraceFirstIsSome pstep TS.ptImg TS.ptLog j T hwfi)
  have hws0 : ag0.paWs = wsInit := hwsi j T ag0 hT hag0
  have hfold := astepsWsFold pstep TS.ptImg TS.ptLog j T.atAgs T.atEvs k ag0 ag hwfi hag0 hag
  rw [hfold, hws0] at hres
  obtain ⟨m, ev, aq, tvs, asrc, hm, hlb, hts⟩ := aevsPostResSrc (T.atEvs.take k) wsInit R wsInitRes hres
  obtain ⟨hm', hlt⟩ := lookup_take_Some.1 hm
  exact ⟨m, ev, aq, tvs, asrc, hlt, hm', hlb, hts⟩

/-! ### Assembling the configuration half after one pf step -/

theorem qcfgStep (hwf : ptracesWf pstep TS) (hwfl : writesFulfilled TS)
    (dn : List Gev) (e : Gev) (T : Atrace P D) (ev : Aev D) (ag' : Wpagent P) (cf : Wpcfg P D)
    (newws : Wstate) (lb' : Wlabel) (dv : D) :
    qorder TS dn →
    nproc dn e.1 = e.2 →
    TS.ptTrs[e.1]? = some T → T.atEvs[e.2]? = some ev →
    T.atAgs[e.2 + 1]? = some ag' →
    qcfg pstep pcls TS DS img d0 ps dn cf →
    newws = aevPost (pi TS (dn ++ [e])) ev (aevsPost (pi TS dn) (T.atEvs.take e.2) wsInit) →
    qfab TS DS (dn ++ [e]) dv →
    wpPfStep pstep pcls e.1 lb' cf
      ⟨cf.pcImg, WeakRobustSim.pfLog TS (dn ++ [e]), dv, cf.pcAgs.set e.1 ⟨ag'.paSt, newws, ∅⟩⟩ →
    qcfg pstep pcls TS DS img d0 ps (dn ++ [e])
      ⟨cf.pcImg, WeakRobustSim.pfLog TS (dn ++ [e]), dv, cf.pcAgs.set e.1 ⟨ag'.paSt, newws, ∅⟩⟩ := by
  intro hq hnp hT hev hag' hc hnew hdv hstep
  obtain ⟨hrun, hcimg, _, hclen, hcags, _⟩ := hc
  have hlt : e.1 < cf.pcAgs.length := by
    obtain ⟨_, _, hlk⟩ := hcags e.1 T hT
    exact lookup_lt_Some hlk
  refine ⟨rtc_r hrun ⟨e.1, lb', hstep⟩, hcimg, rfl, by simp [hclen], ?_, hdv⟩
  intro j T' hT'
  dsimp only
  by_cases hj : j = e.1
  · subst hj
    have hTT : T' = T := by rw [hT'] at hT; exact Option.some.inj hT
    subst hTT
    refine ⟨ag', by rw [nprocAppEq, hnp]; exact hag', ?_⟩
    have hst := wsStable pstep TS hwf hwfl dn [e] e.1 T' hq hT'
    rw [hnp] at hst
    rw [list_lookup_insert hlt, hnew, nprocAppEq, hnp, take_S_r hev, aevsPostApp, hst]
  · obtain ⟨agn, hagn, hlkj⟩ := hcags j T' hT'
    refine ⟨agn, by rw [nprocAppNe dn e j hj]; exact hagn, ?_⟩
    rw [list_lookup_insert_ne (fun h => hj h.symm), hlkj, nprocAppNe dn e j hj,
      wsStable pstep TS hwf hwfl dn [e] j T' hq hT']

/-! ### THE STEP: one traced event becomes one promise-free step -/

theorem QinvStep (hwf : ptracesWf pstep TS) (hwsi : ptracesWsInit TS) (hco : ∀ a, coTc TS a)
    (hwfl : writesFulfilled TS) (hlf : latFreeProg pstep) (hobl : tsOblivious pstep)
    (hcls : clsCanonical pcls TS) (hclsobl : pclsObl pcls) (himg : TS.ptImg = img)
    (hdata : ∀ (p : Nat) (m : Wmsg), TS.ptLog[p]? = some m → m.wmData ≠ [])
    (hwit : ptracesWit TS DS) (hfetch : fetchSrcOk TS) (dn : List Gev) (e : Gev) :
    Qinv pstep pcls TS DS img d0 ps dn → gevWf TS e → e ∉ dn →
    (∀ e', gdep3 TS DS e' e → gevWf TS e' → e' ∈ dn) →
    Qinv pstep pcls TS DS img d0 ps (dn ++ [e]) := by
  rintro ⟨hq, cf, hc⟩ hwfe hnin hpre3
  -- the ORDER half sees only `gdep2`; the FABRIC half spends the `gdev` edges
  have hpre : ∀ e', gdep2 TS e' e → gevWf TS e' → e' ∈ dn :=
    fun e' hd hw => hpre3 e' (gdep2Gdep3 TS DS e' e hd) hw
  have hq' := qorderStep TS dn e hq hwfe hnin hpre
  have hnp := nprocCur TS dn e hq hwfe hnin hpre
  refine ⟨hq', ?_⟩
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
    qfabStep pstep TS DS hwit dn e T ev ag st' cf hnin hpre3 hT hev hps hfab
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
    refine ⟨_, qcfgStep pstep pcls TS DS img d0 ps hwf hwfl dn e T ev ag2 cf W .LSilent dnew
      hq hnp hT hev hag2 hc0 ?_ hfab' ?_⟩
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
    refine ⟨_, qcfgStep pstep pcls TS DS img d0 ps hwf hwfl dn e T ev ag2 cf
      (loadPostRunD W aq (srcsView W asrc) base ((tlabelTs (pi TS dn) tvs).map Prod.fst))
      (.LLoad aq false base (tlabelTs (pi TS dn) tvs) asrc) dnew
      hq hnp hT hev hag2 hc0 ?_ hfab' ?_⟩
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
    refine ⟨_, qcfgStep pstep pcls TS DS img d0 ps hwf hwfl dn e T ev ag2 cf
      (storePostRunD W rl (srcsView W asrc) (srcsView W vsrc) base data.length
        (cf.pcLog.length + 1))
      (.LStore rl base data asrc vsrc) dnew hq hnp hT hev hag2 hc0 ?_ hfab' ?_⟩
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
    refine ⟨_, qcfgStep pstep pcls TS DS img d0 ps hwf hwfl dn e T ev ag2 cf
      (storePostRunD
        (loadPostRunD W aq (srcsView W asrc) base ((tlabelTs (pi TS dn) tvs).map Prod.fst))
        rl (srcsView W asrc) (srcsView W vsrc) base data.length (cf.pcLog.length + 1))
      (.LRmw aq rl base (tlabelTs (pi TS dn) tvs) data asrc vsrc) dnew
      hq hnp hT hev hag2 hc0 ?_ hfab' ?_⟩
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
    refine ⟨_, qcfgStep pstep pcls TS DS img d0 ps hwf hwfl dn e T ev ag2 cf
      (fencePost W pr pw sr sw) (.LFence pr pw sr sw) dnew hq hnp hT hev hag2 hc0 ?_ hfab' ?_⟩
    · rw [← hWdef]; simp only [aevPost, hlbe]
    · rw [hstpost, hlogNone hgts]
      exact .PFFence cf _ pr pw sr sw st' dnew hcflk hpure
  | LDev =>
    -- the `LSilent` case verbatim, at `PFDev`
    obtain ⟨_, hts0⟩ := hok
    have hgts : gevTs TS e = none := by simp [gevTs, hgev, hts0]
    refine ⟨_, qcfgStep pstep pcls TS DS img d0 ps hwf hwfl dn e T ev ag2 cf W .LDev dnew
      hq hnp hT hev hag2 hc0 ?_ hfab' ?_⟩
    · rw [← hWdef]; simp only [aevPost, hlbe]
    · rw [hstpost, hlogNone hgts]
      exact .PFDev cf _ st' dnew hcflk hpure
  | LRegW rdw wsrc =>
    obtain ⟨_, hts0⟩ := hok
    have hgts : gevTs TS e = none := by simp [gevTs, hgev, hts0]
    refine ⟨_, qcfgStep pstep pcls TS DS img d0 ps hwf hwfl dn e T ev ag2 cf
      (regwPost W rdw (srcsView W wsrc)) (.LRegW rdw wsrc) dnew hq hnp hT hev hag2 hc0 ?_ hfab' ?_⟩
    · rw [← hWdef]; simp only [aevPost, hlbe]
    · rw [hstpost, hlogNone hgts]
      exact .PFRegW cf _ rdw wsrc st' dnew hcflk hpure
  | LCtrl csrc =>
    obtain ⟨_, hts0⟩ := hok
    have hgts : gevTs TS e = none := by simp [gevTs, hgev, hts0]
    refine ⟨_, qcfgStep pstep pcls TS DS img d0 ps hwf hwfl dn e T ev ag2 cf
      (ctrlPost W (srcsView W csrc)) (.LCtrl csrc) dnew hq hnp hT hev hag2 hc0 ?_ hfab' ?_⟩
    · rw [← hWdef]; simp only [aevPost, hlbe]
    · rw [hstpost, hlogNone hgts]
      exact .PFCtrl cf _ csrc st' dnew hcflk hpure
  | LInstr =>
    obtain ⟨_, hts0⟩ := hok
    have hgts : gevTs TS e = none := by simp [gevTs, hgev, hts0]
    refine ⟨_, qcfgStep pstep pcls TS DS img d0 ps hwf hwfl dn e T ev ag2 cf
      (instrPost W) .LInstr dnew hq hnp hT hev hag2 hc0 ?_ hfab' ?_⟩
    · rw [← hWdef]; simp only [aevPost, hlbe]
    · rw [hstpost, hlogNone hgts]
      exact .PFInstr cf _ st' dnew hcflk hpure
  -- THE RMW SPLIT: THE TWO SPLIT HALVES (S4 / T2-2a)
  | LExLoad xaq xbase xtvs xasrc =>
    obtain ⟨hro, _, hts0⟩ := hok
    have hgts : gevTs TS e = none := by simp [gevTs, hgev, hts0]
    have hmap := hmapOf xbase xtvs (by rw [hlbe]; rfl)
    refine ⟨_, qcfgStep pstep pcls TS DS img d0 ps hwf hwfl dn e T ev ag2 cf
      (exloadPostRunD W xaq (srcsView W xasrc) xbase ((tlabelTs (pi TS dn) xtvs).map Prod.fst))
      (.LExLoad xaq xbase (tlabelTs (pi TS dn) xtvs) xasrc) dnew
      hq hnp hT hev hag2 hc0 ?_ hfab' ?_⟩
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
    refine ⟨_, qcfgStep pstep pcls TS DS img d0 ps hwf hwfl dn e T ev ag2 cf
      (storePostRunD W yrl (srcsView W yasrc) (srcsView W yvsrc) ybase ydata.length
        (cf.pcLog.length + 1))
      (.LExStore yrl ybase ydata yasrc yvsrc) dnew hq hnp hT hev hag2 hc0 ?_ hfab' ?_⟩
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
    refine ⟨_, qcfgStep pstep pcls TS DS img d0 ps hwf hwfl dn e T ev ag2 cf W
      (.LIFetch base (tlabelTs (pi TS dn) tvs)) dnew hq hnp hT hev hag2 hc0 ?_ hfab' ?_⟩
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

/-! ### The base case, and the induction -/

theorem QinvNil (hwf : ptracesWf pstep TS)
    (hps0 : ∀ (j : Nat) (T : Atrace P D) (ag0 : Wpagent P), TS.ptTrs[j]? = some T →
      T.atAgs[0]? = some ag0 → ps[j]? = some ag0.paSt)
    (hd0 : DS.pdInit = d0) :
    Qinv pstep pcls TS DS img d0 ps [] := by
  refine ⟨⟨List.nodup_nil, fun e he => by simp at he, fun x hx => by simp at hx,
    fun n y hn => by simp at hn, fun j k => ⟨fun h => by simp at h, fun ⟨_, hlt⟩ => by
      rw [nprocNil] at hlt; omega⟩⟩, wpInit img d0 ps, rtc_refl _, rfl, rfl, by simp [wpInit], ?_,
    qfabInit TS DS d0 hd0⟩
  intro j T hT
  obtain ⟨ag0, hag0⟩ := Option.isSome_iff_exists.1 (atraceFirstIsSome pstep _ _ _ _ (hwf j T hT))
  refine ⟨ag0, hag0, ?_⟩
  simp [wpInit, hps0 j T ag0 hT hag0, nprocNil, aevsPost]

/-- THE SUBSET SIMULATION (design item (iv)). -/
theorem simPrefix (hwf : ptracesWf pstep TS) (hwsi : ptracesWsInit TS) (hco : ∀ a, coTc TS a)
    (hwfl : writesFulfilled TS) (hlf : latFreeProg pstep) (hobl : tsOblivious pstep)
    (hcls : clsCanonical pcls TS) (hclsobl : pclsObl pcls) (himg : TS.ptImg = img)
    (hdata : ∀ (p : Nat) (m : Wmsg), TS.ptLog[p]? = some m → m.wmData ≠ [])
    (hps0 : ∀ (j : Nat) (T : Atrace P D) (ag0 : Wpagent P), TS.ptTrs[j]? = some T →
      T.atAgs[0]? = some ag0 → ps[j]? = some ag0.paSt)
    (hwit : ptracesWit TS DS) (hd0 : DS.pdInit = d0) (hfetch : fetchSrcOk TS)
    (Ssub : Gev → Prop) [DecidablePred Ssub] :
    gdep3Acyclic TS DS → subOk TS (gdep3 TS DS) Ssub →
    ∃ order,
      Qinv pstep pcls TS DS img d0 ps order ∧
      order.Nodup ∧
      (∀ e, e ∈ order ↔ (gevWf TS e ∧ Ssub e)) ∧
      (∀ x y (i j : Nat), order[i]? = some x → order[j]? = some y →
         gdep3 TS DS x y → i < j) := by
  rintro hacyc ⟨hdc, _⟩
  exact toposortIndS TS (gdep3 TS DS) Ssub (Qinv pstep pcls TS DS img d0 ps) hacyc hdc
    (QinvNil pstep pcls TS DS img d0 ps hwf hps0 hd0)
    (fun dn e hQ hwfe _ hnin hpre => QinvStep pstep pcls TS DS img d0 ps hwf hwsi hco hwfl hlf
      hobl hcls hclsobl himg hdata hwit hfetch dn e hQ hwfe hnin hpre)

/-! ### THE FULL SIMULATION: the promise-free witness of a behavior -/

theorem simFull (hwf : ptracesWf pstep TS) (hwsi : ptracesWsInit TS) (hco : ∀ a, coTc TS a)
    (hwfl : writesFulfilled TS) (hlf : latFreeProg pstep) (hobl : tsOblivious pstep)
    (hcls : clsCanonical pcls TS) (hclsobl : pclsObl pcls) (himg : TS.ptImg = img)
    (hnag : TS.ptTrs.length = ps.length)
    (hdata : ∀ (p : Nat) (m : Wmsg), TS.ptLog[p]? = some m → m.wmData ≠ [])
    (hps0 : ∀ (j : Nat) (T : Atrace P D) (ag0 : Wpagent P), TS.ptTrs[j]? = some T →
      T.atAgs[0]? = some ag0 → ps[j]? = some ag0.paSt)
    (hwit : ptracesWit TS DS) (hd0 : DS.pdInit = d0) (hfetch : fetchSrcOk TS)
    (cend : Wpcfg P D) :
    gdep3Acyclic TS DS →
    TS.ptImg = cend.pcImg →
    TS.ptLog = cend.pcLog →
    cend.pcAgs.length = ps.length →
    (∀ (j : Nat) (T : Atrace P D), TS.ptTrs[j]? = some T →
       T.atAgs[T.atEvs.length]? = cend.pcAgs[j]?) →
    ∃ cf, rtc (wpPfRun pstep pcls) (wpInit img d0 ps) cf ∧
      progOf cf = progOf cend ∧ (∀ a, memOf cf a = memOf cend a) := by
  intro hacyc himgc hlogc hlenc hlast
  obtain ⟨order, hQ, _, hmemo, _⟩ :=
    toposortIndFull TS (gdep3 TS DS) (Qinv pstep pcls TS DS img d0 ps) hacyc
      (QinvNil pstep pcls TS DS img d0 ps hwf hps0 hd0)
      (fun dn e hQ hwfe hnin hpre => QinvStep pstep pcls TS DS img d0 ps hwf hwsi hco hwfl hlf
        hobl hcls hclsobl himg hdata hwit hfetch dn e hQ hwfe hnin hpre)
  obtain ⟨hq, cf, hrun, hcimg, hclog, hclen, hcags, _⟩ := hQ
  refine ⟨cf, hrun, ?_⟩
  -- every agent's trace is fully processed
  have hfulln : ∀ (j : Nat) (T : Atrace P D), TS.ptTrs[j]? = some T →
      nproc order j = T.atEvs.length := by
    intro j T hT
    obtain ⟨agn, hagn, _⟩ := hcags j T hT
    have hlen2 := astepsWfLen pstep TS.ptImg TS.ptLog j T.atAgs T.atEvs (hwf j T hT)
    have hle : nproc order j ≤ T.atEvs.length := by have := lookup_lt_Some hagn; omega
    rcases Nat.lt_or_ge (nproc order j) T.atEvs.length with hlt | hge
    · exfalso
      have hwfe : gevWf TS (j, nproc order j) := (gevWfBounds TS _).2 ⟨T, hT, hlt⟩
      have hin := (hmemo _).2 hwfe
      have := ((qorderMem TS order j (nproc order j) hq).1 hin).2
      omega
    · omega
  refine ⟨?_, ?_⟩
  · -- PROGRAM STATES
    unfold progOf
    apply list_eq
    intro i
    rw [List.getElem?_map, List.getElem?_map]
    rcases Nat.lt_or_ge i ps.length with hi | hi
    · obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1
        (lookup_lt_is_Some_2 (l := TS.ptTrs) (i := i) (by omega))
      obtain ⟨agn, hagn, hlk⟩ := hcags i T hT
      rw [hfulln i T hT, hlast i T hT] at hagn
      rw [hlk, hagn]
      rfl
    · rw [lookup_ge_None_2 (l := cf.pcAgs) (by omega), lookup_ge_None_2 (l := cend.pcAgs) (by omega)]
  · -- FINAL FLAT MEMORY
    intro a
    unfold memOf
    rw [hcimg, hclog, ← himgc, ← hlogc, ← himg]
    rcases latestTsWrites TS.ptLog a with hz | ⟨p, m, hr, hlk, hs⟩
    · -- nothing writes `a` at all, on either side
      have hz' : latestTs (WeakRobustSim.pfLog TS order) a = 0 := by
        refine (latestTsZeroIff _ a).2 (fun hw => ?_)
        obtain ⟨that, ehat, _, _, _, hwb, _⟩ := pfWritesInInv pstep TS hwf order a _ _ hq hw
        apply (latestTsZeroIff TS.ptLog a).1 hz
        have hpos := writesBPos pstep TS _ _ _ hwf hwb
        obtain ⟨_, mm, hmm, hb⟩ := hwb
        exact ⟨that, hpos, by have := lookup_lt_Some hmm; omega, mm, hmm, hb⟩
      rw [hz, hz', logByte0, logByte0]
    · -- the latest byte-`a` write maps to the pf log's latest
      have hpos : 0 < latestTs TS.ptLog a := by rw [hr]; omega
      have hlk' : TS.ptLog[latestTs TS.ptLog a - 1]? = some m := by
        rw [hr, Nat.add_sub_cancel]; exact hlk
      have hmsg : msgAt TS (latestTs TS.ptLog a) = m := msgAtEq TS _ m hlk'
      obtain ⟨em, hem⟩ := hwfl _ m hpos hlk'
      have hemin : em ∈ order := (hmemo em).2 (gevTsWf TS em _ hem)
      have hwbm : writesB TS a em (latestTs TS.ptLog a) := ⟨hem, m, hlk', hs⟩
      have hinfl : latestTs TS.ptLog a ∈ fl TS order := (elemOfFl TS order _).2 ⟨em, hemin, hem⟩
      obtain ⟨hp1, _, hp3⟩ := pfLogPi pstep TS hwf order _ hq hinfl
      have hlat : latest TS.ptImg (WeakRobustSim.pfLog TS order) a
          (pi TS order (latestTs TS.ptLog a)) := by
        refine ⟨?_, fun hw => ?_⟩
        · rw [logBytePos _ _ _ (msgAt TS (latestTs TS.ptLog a)) _ hp1 hp3, hmsg]
          exact hs
        · obtain ⟨that, ehat, hlo, _, _, hwb, _⟩ := pfWritesInInv pstep TS hwf order a _ _ hq hw
          have hle : that ≤ latestTs TS.ptLog a := by
            rcases Nat.lt_or_ge (latestTs TS.ptLog a) that with hgt | hle
            · exfalso
              apply latestTsTop TS.ptLog a
              obtain ⟨_, mm, hmm, hb⟩ := hwb
              exact ⟨that, hgt, by have := lookup_lt_Some hmm; omega, mm, hmm, hb⟩
            · exact hle
          rcases Nat.eq_or_lt_of_le hle with heq | hlt
          · subst heq; omega
          · have := piLtOfCo pstep TS hwf hco order a ehat em that _ hq hemin hwb hwbm hlt
            omega
      rw [latestTsEq _ _ a _ hlat, logBytePos _ _ _ (msgAt TS (latestTs TS.ptLog a)) _ hp1 hp3,
        hmsg, logBytePos _ _ _ m _ hpos hlk']

end sim

/-! ## The invariant's configuration half, as a standalone accessor -/

theorem QinvRun {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (TS : Ptraces P D) (DS : Pdevs D) (img : Image)
    (d0 : D) (ps : List P) (dn : List Gev) :
    Qinv pstep pcls TS DS img d0 ps dn →
    ∃ cf, rtc (wpPfRun pstep pcls) (wpInit img d0 ps) cf ∧
      cf.pcImg = img ∧ cf.pcLog = WeakRobustSim.pfLog TS dn ∧
      cf.pcAgs.length = ps.length ∧
      (∀ (j : Nat) (T : Atrace P D), TS.ptTrs[j]? = some T →
         ∃ agn, T.atAgs[nproc dn j]? = some agn ∧
           cf.pcAgs[j]?
           = some ⟨agn.paSt, aevsPost (pi TS dn) (T.atEvs.take (nproc dn j)) wsInit, ∅⟩) ∧
      qfab TS DS dn cf.pcDev :=
  fun ⟨_, cf, hc⟩ => ⟨cf, hc⟩

theorem QinvOrder {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (TS : Ptraces P D) (DS : Pdevs D) (img : Image)
    (d0 : D) (ps : List P) (dn : List Gev) :
    Qinv pstep pcls TS DS img d0 ps dn → qorder TS dn :=
  fun h => h.1

/-! ## LAYER 4: the behavior-level wrapper

Everything the section context asks for that is not already a published theorem
of a sibling file is discharged here from the PROMISE PHASE. -/

section wrapper

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)
variable (pdev : P → Wlabel → P → Bool)

/-- Every logged message carries a nonempty payload. -/
def logNe (log : List Wmsg) : Prop :=
  ∀ (p : Nat) (m : Wmsg), log[p]? = some m → m.wmData ≠ []

theorem logNeInit (img : Image) (d0 : D) (ps : List P) :
    logNe (wpInit (P := P) (D := D) img d0 ps).pcLog := by
  intro p m hp
  simp [wpInit] at hp

theorem logNePromiseStep (c c' : Wpcfg P D) :
    logNe c.pcLog → wpPromiseStep c c' → logNe c'.pcLog := by
  intro hne hs
  obtain ⟨j, agj, base, data, kc, _, hnn, rfl⟩ := wpPromiseStepInv c c' hs
  intro p m hp
  dsimp only at hp
  rcases Nat.lt_or_ge p c.pcLog.length with hlt | hge
  · rw [lookup_app_l hlt] at hp
    exact hne p m hp
  · have hp' : p = c.pcLog.length := by
      have := lookup_lt_Some hp
      simp at this; omega
    subst hp'
    rw [lookup_app_r (Nat.le_refl _), Nat.sub_self] at hp
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
    subst hp
    exact hnn

theorem logNePromiseRun (c c' : Wpcfg P D) :
    logNe c.pcLog → rtc (wpPromiseStep (P := P) (D := D)) c c' → logNe c'.pcLog := by
  intro h0 hr
  induction hr with
  | refl => exact h0
  | tail _ hs ih => exact logNePromiseStep _ _ ih hs

/-- The promise phase freezes the image, the agent count, the FABRIC and every
program state. -/
theorem promiseRunShape (c c' : Wpcfg P D) :
    rtc (wpPromiseStep (P := P) (D := D)) c c' →
    c'.pcImg = c.pcImg ∧ c'.pcAgs.length = c.pcAgs.length ∧
    c'.pcDev = c.pcDev ∧
    (∀ (i : Nat) (ag' : Wpagent P), c'.pcAgs[i]? = some ag' →
       ∃ ag, c.pcAgs[i]? = some ag ∧ ag'.paSt = ag.paSt) := by
  intro h
  induction h with
  | refl => exact ⟨rfl, rfl, rfl, fun i ag' hlk => ⟨ag', hlk, rfl⟩⟩
  | tail _ hs ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    obtain ⟨j, agj, base, data, kc, hlkj, _, rfl⟩ := wpPromiseStepInv _ _ hs
    have hjlt := lookup_lt_Some hlkj
    refine ⟨h1, by simp [h2], h3, fun i ag' hlk => ?_⟩
    dsimp only at hlk
    by_cases hij : i = j
    · subst hij
      rw [list_lookup_insert hjlt] at hlk
      cases hlk
      exact h4 i agj hlkj
    · rw [list_lookup_insert_ne (fun h => hij h.symm)] at hlk
      exact h4 i ag' hlk

/-- THE BEHAVIOR-LEVEL SIMULATION, THE FABRIC-CARRYING FORM (G4), with the class
premises (G6a) and — deviation 4 — the fetch-source premise. -/
theorem wpBehaviorRobustDev (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D) :
    pdevOk pstep pdev →
    latFreeProg pstep → tsOblivious pstep →
    pclsObl pcls →
    wpBehavior pstep img d0 ps c →
    (∀ (mid : Wpcfg P D) (TS : Ptraces P D) (DS : Pdevs D),
       rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid →
       ptracesDevOf pstep pdev TS DS mid c →
       gdep3Acyclic TS DS ∧ (∀ a, coTc TS a)) →
    (∀ (mid : Wpcfg P D) (TS : Ptraces P D) (DS : Pdevs D),
       rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid →
       ptracesDevOf pstep pdev TS DS mid c →
       clsCanonical pcls TS) →
    (∀ (mid : Wpcfg P D) (TS : Ptraces P D) (DS : Pdevs D),
       rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid →
       ptracesDevOf pstep pdev TS DS mid c →
       fetchSrcOk TS) →
    ∃ cf, rtc (wpPfRun pstep pcls) (wpInit img d0 ps) cf ∧
      progOf cf = progOf c ∧ (∀ a, memOf cf a = memOf c a) := by
  intro hpok hlf hobl hclsobl hb hprem hpcan hpfetch
  obtain ⟨mid, TS, DS, hprom, hofd, _, hacct⟩ :=
    wpBehaviorFulfilOnceDev pstep pdev img d0 ps c hpok hlf hb
  have hwit : ptracesWit TS DS := ptracesDevOfWit pstep pdev TS DS mid c hofd
  have hinit : DS.pdInit = mid.pcDev := hofd.2.1
  obtain ⟨hacyc, hco⟩ := hprem mid TS DS hprom hofd
  have hcls := hpcan mid TS DS hprom hofd
  have hfetch := hpfetch mid TS DS hprom hofd
  have hof := hofd.1
  have hwf : ptracesWf pstep TS := ptracesOfWf pstep TS mid c hof
  have hla : logAuthored mid.pcLog :=
    logAuthoredPromiseRun _ _ (logAuthoredInit img d0 ps) hprom
  have hwfl : writesFulfilled TS := ptracesOfWritesFulfilled pstep TS mid c hof hla hacct
  have hlne : logNe mid.pcLog := logNePromiseRun _ _ (logNeInit img d0 ps) hprom
  have hwsi : ptracesWsInit TS :=
    ptracesOfWsInit pstep TS mid c hof (cfgWsInitPromiseRun _ _ (cfgWsInitInit img d0 ps) hprom)
  obtain ⟨hpimg, hplen, hpdev, hpst⟩ := promiseRunShape (wpInit img d0 ps) mid hprom
  have hd01 : DS.pdInit = d0 := by rw [hinit, hpdev]; rfl
  obtain ⟨himg0, hlog0, hlent, _, hfst, hlst, hclogc, hcimgc, hclenc⟩ := hof
  have himg1 : TS.ptImg = img := by rw [himg0, hpimg]; rfl
  have hlen1 : TS.ptTrs.length = ps.length := by rw [hlent, hplen]; simp [wpInit]
  have hdata1 : ∀ (p : Nat) (m : Wmsg), TS.ptLog[p]? = some m → m.wmData ≠ [] := by
    rw [hlog0]; exact hlne
  have hps1 : ∀ (j : Nat) (T : Atrace P D) (ag0 : Wpagent P), TS.ptTrs[j]? = some T →
      T.atAgs[0]? = some ag0 → ps[j]? = some ag0.paSt := by
    intro j T ag0 hT hag0
    have hmid : mid.pcAgs[j]? = some ag0 := by rw [← hfst j T hT]; exact hag0
    obtain ⟨ag, hag, hst⟩ := hpst j ag0 hmid
    simp only [wpInit, List.getElem?_map] at hag
    cases hp0 : ps[j]? with
    | none => rw [hp0] at hag; cases hag
    | some p0 =>
      rw [hp0] at hag
      simp only [Option.map_some, Option.some.injEq] at hag
      subst hag
      rw [hst]
  exact simFull pstep pcls TS DS img d0 ps hwf hwsi hco hwfl hlf hobl hcls hclsobl himg1 hlen1
    hdata1 hps1 hwit hd01 hfetch c hacyc (by rw [himg0, hcimgc]) (by rw [hlog0, hclogc])
    (by rw [hclenc, hplen]; simp [wpInit]) hlst

/-- THE DEV-FREE READING (the OLD `wp_behavior_robust`). -/
theorem wpBehaviorRobust (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D) :
    pdevOk pstep pdev →
    (∀ p l p', pdev p l p' = false) →
    latFreeProg pstep → tsOblivious pstep →
    pclsObl pcls →
    wpBehavior pstep img d0 ps c →
    (∀ (mid : Wpcfg P D) (TS : Ptraces P D),
       rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid →
       ptracesOf pstep TS mid c →
       gdep2Acyclic TS ∧ (∀ a, coTc TS a)) →
    (∀ (mid : Wpcfg P D) (TS : Ptraces P D),
       rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid →
       ptracesOf pstep TS mid c →
       clsCanonical pcls TS) →
    (∀ (mid : Wpcfg P D) (TS : Ptraces P D),
       rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid →
       ptracesOf pstep TS mid c →
       fetchSrcOk TS) →
    ∃ cf, rtc (wpPfRun pstep pcls) (wpInit img d0 ps) cf ∧
      progOf cf = progOf c ∧ (∀ a, memOf cf a = memOf c a) := by
  intro hpok hnodev hlf hobl hclsobl hb hprem hpcan hpfetch
  refine wpBehaviorRobustDev pstep pcls pdev img d0 ps c hpok hlf hobl hclsobl hb ?_ ?_ ?_
  · intro mid TS DS hprom hofd
    have hdf := ptracesDevOfFree pstep pdev TS DS mid c hnodev hofd
    have hwit := ptracesDevOfWit pstep pdev TS DS mid c hofd
    obtain ⟨hacyc, hco⟩ := hprem mid TS hprom hofd.1
    exact ⟨gdep3AcyclicDevfree TS DS hwit hdf hacyc, hco⟩
  · intro mid TS DS hprom hofd
    exact hpcan mid TS hprom hofd.1
  · intro mid TS DS hprom hofd
    exact hpfetch mid TS hprom hofd.1

end wrapper

/-! ## What the rest of W2b/W5 inherits from this file

- `tsOblivious`: worklist finding (v), the one new premise the simulation forces
  on `pstep` (plus, in Lean, the `LIFetch` conjunct, deviation 4).
- `simFull`: the promise-free witness of a traced behavior — same per-agent
  program states, same flat memory — from `gdep3Acyclic`, `coTc`,
  `writesFulfilled`, `ptracesWf`/`ptracesWsInit`, the promise-phase shape facts
  and (Lean, deviation 4) `fetchSrcOk`.  NO discipline premise is used.
- `wpBehaviorRobustDev` / `wpBehaviorRobust`: the behavior-level packaging.
- `qdev` / `qfab` / `qfabStep`: the fabric half of the invariant.
- `simPrefix` (+ `QinvRun` / `QinvOrder`): the SUBSET form over any `subOk`.
- `piL` / `pi` / `fl` / `WeakRobustSim.pfLog` / `nproc`: the π machinery. -/

end Weak
