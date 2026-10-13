/-
Weak: **RVWMO⁻, the tier-2 declared model** (T2-1, slice 1).

Rocq: `iris/WeakRvwmoGraph.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance (design: `claude-notes/design/weak-memory-tier2-s6.md`
§1).  THE POINT: tier 2's declared model must express EARLY STORES, and the
`Cand` presentation provably cannot (its gmo IS trace order).  This file is the
herd-style presentation: per-agent label lists (po = position), and the GLOBAL
MEMORY ORDER as DATA — a list `gxGmo` of the memory events — so a store may sit
gmo-before its own po-earlier reads.

THE ENCODING TRICK: the fused label alphabet `WeakAxiomatic.Lbl` is reused
UNCHANGED, with a read's per-byte `ts` entries reinterpreted as
GMO-WRITE-INDICES (0 = the era-initial image; `t > 0` names the `t`-th write in
`gxGmo`).  In a `Cand`, `ts` entries are log positions and the log is the
trace's writes in trace order — the same convention — so the `Cand → graph`
embedding (`graphOfCand`) is the IDENTITY on labels and programs.

THE MODEL (RVWMO⁻ = RVWMO minus ppo rules 6 and 9–13): `gwf` (shapes + gmo
well-formedness), `gppoGmo` (ppo⁻ ⊆ gmo, ppo⁻ keeping rules 1–3 as same-byte
program order, 4 fences, 5 acquires, 7 RCsc pairs), `gloadValue` (a read names
a same-byte write (gmo ∪ po)-before it and co-maximal among such; the po
disjunct is store forwarding), `gatomicity` (no same-byte write co-between a
fused RMW's read source and the RMW itself).  Dropping ppo rules only ADDS
behaviours, so a safety theorem against RVWMO⁻ covers RVWMO.  THE DEFERRED
PIECE: the store-side dependency fragment, added in §7 as graph DATA
(`gdDeps`).

THIS SLICE delivers the presentation, the model, the embedding `graphOfCand`
(definition only), and the NON-COLLAPSE WITNESS `lbGraphConsistent` — the
four-event LB execution is RVWMO⁻-consistent, so tier 2 is about a real gap.
§6 (position arithmetic), §7 (the dependency fragment, route B stage B0) and §8
(additive helpers for the exchange kit) are additive.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1; types
   UpperCamelCase, fields lowerCamelCase.  Duplicated Rocq names (protocol
   rule) are FILE-QUALIFIED: `WeakRvwmoGraph.gpo`,
   `WeakRvwmoGraph.glblIsRGmem`, `WeakRvwmoGraph.glblIsWGmem`,
   `WeakRvwmoGraph.gwixPos`, `WeakRvwmoGraph.gwritesByteGisW`.
2. VOCABULARY: as `WeakMem` deviation 2; `agent` ↦ `Nat`, `Z` ↦ `Int`,
   `bv 8` ↦ `BitVec 8`, `l !! i` ↦ `l[i]?`, `x ≫= f` ↦ `x.bind f`,
   `is_Some o` ↦ `o.isSome`, `NoDup` ↦ `List.Nodup`, `StronglySorted` ↦
   `List.Pairwise`, `filter P` ↦ `List.filter p` (`gisW` is already Boolean;
   `es_ag s = i` ↦ `decide (s.esAg = i)`), `list_find (λ e', e' = e)` ↦
   `listFind (fun e' => decide (e' = e))`, `imap pair` ↦ `mapIdx (·, ·)`,
   `seq 0 n` ↦ `List.range' 0 n`, `list_max l` ↦ `l.foldr max 0` (stdpp's
   definition), `GExec img prog gmo` ↦ `⟨img, prog, gmo⟩`.
3. `StronglySorted_filter`'s `P` with a `Decision` instance is a Boolean
   predicate `p`, as the shim's `filter` convention.
4. `lbGraphConsistent`'s closed `vm_compute` side conditions (gmo membership,
   `gpos`/`gwix` values, `gwriteAt`) are `decide`.
5. Lean-only helpers (no Rocq twin): `lbgLbl` (the four labels of `lbg`, the
   engine of every `lbg` case split).
6. W13 (M) (plan `notes/weak-allocproc-plan.md` §C W13; D38 [OWN.14]): `lbIsMem`
   (hence `gmem`, gmo, `gwf`'s membership clause) also holds of the I/O-class label
   `Lbl.LIo` (`lbIsR l || lbIsW l || lbIsIo l`; Rocq: reads and writes only).  `lbIsR`/`lbIsW`
   stay RAM-only.  W13 (I) ([OWN.27]) flips `gwf`'s `LIo` shape arm to `True` (it was `False`
   under W13 (E)/(M)), so a `gwf` graph may carry I/O events; the (M)-era helpers
   `gwfNoIo`/`gwfMemRW` are retired with the `False` arm.
7. D35-fix ([OWN.54], plan `notes/weak-allocproc-plan.md` §C top): RVWMO⁻'s RULE-7 ARM is
   `grcsc` (`[RCsc];po;[RCsc]` with riscv.cat's `lbRcsc := lbAq || lbRl`), defined HERE
   (`AxGraphCat` uses it as the cat model's rule-7 arm); Rocq's `gppo` has `grelAcq`
   (`[W.rl];po;[R.aq]`), kept as a lemma-level name with `grelAcq ⊆ grcsc`
   (`grelAcqGrcsc`).  Widened IN STEP with the cat model so that
   `gppoCat6Gppo`/`minusImpliesCat` keep their statements.  SEMANTIC CONSEQUENCE: RVWMO⁻ is
   STRONGER (it orders riscv.cat's `[W.rl];po;[W.rl]`, `[W.rl];po;[R.aq]`, rl-only-RMW pairs —
   EQUAL to riscv.cat's rule 7), and `WeakRvwmoAcyc.racy` carries `gppo` BY NAME, so `racyD`
   (the acyclicity premise of `normalizeOfAcyclic`, `hullRun`, the kill, and every `racyD ∪ …`
   built on it) WIDENS with NO text change: those premises must now exclude rule-7-wide
   cycles — EMPTY on xv6 graphs, which carry no `W.rl` (the kernel's only annotated atomic is
   `acquire`'s `amoswap.w.aq`).

**Name map** (Rocq → Lean): `geid` ↦ `Geid`; `gexec` ↦ `Gexec` (`gx_img`/
`gx_prog`/`gx_gmo` ↦ `gxImg`/`gxProg`/`gxGmo`); `gdexec` ↦ `Gdexec`
(`gd_g`/`gd_deps` ↦ `gdG`/`gdDeps`); `gx_lbl` ↦ `gxLbl`, `lb_is_mem` ↦
`lbIsMem`, `gmem`, `gpos`, `gmo_lt` ↦ `gmoLt`, `gis_w` ↦ `gisW`, `gwrites`,
`gwrite_at` ↦ `gwriteAt`, `gwix`, `gwrites_byte` ↦ `gwritesByte`,
`greads_byte` ↦ `greadsByte`, `gpo` ↦ `WeakRvwmoGraph.gpo`, `gwf`,
`gfence_between` ↦ `gfenceBetween`, `glbl_is` ↦ `glblIs`, `glbl_is_r_gmem` ↦
`WeakRvwmoGraph.glblIsRGmem`, `glbl_is_w_gmem` ↦ `WeakRvwmoGraph.glblIsWGmem`,
`gfence_covers` ↦ `gfenceCovers`, `gacq_po` ↦ `gacqPo`, `grel_acq` ↦
`grelAcq`, (deviation 7: `AxGraphCat`'s `lb_rcsc` ↦ `lbRcsc`, `grcsc` and
`lb_rcsc_bits` ↦ `lbRcscMem` live here; Lean-only `glblIsRcscGmem`, `grelAcqGrcsc`), `gaccesses`, `gpoloc`, `gppo`, `gppo_gmo` ↦ `gppoGmo`, `gvisible`,
`gload_value` ↦ `gloadValue`, `gatomicity`, `rvwmo_minus_consistent` ↦
`rvwmoMinusConsistent`, `grule14`, `graph_of_cand` ↦ `graphOfCand`, `lbg`,
`lbg_acc` ↦ `lbgAcc`, `lbg_wr` ↦ `lbgWr`, `lb_graph_consistent` ↦
`lbGraphConsistent`, `StronglySorted_lookup_elim` ↦
`stronglySortedLookupElim`, `StronglySorted_lookup_intro` ↦
`stronglySortedLookupIntro`, `StronglySorted_filter` ↦ `stronglySortedFilter`,
`gpos_lookup` ↦ `gposLookup`, `gpos_elem_lookup` ↦ `gposElemLookup`,
`gpos_of_lookup` ↦ `gposOfLookup`, `gpos_lt_len` ↦ `gposLtLen`, `gpos_inj` ↦
`gposInj`, `gmo_lt_trans` ↦ `gmoLtTrans`, `gmo_lt_irrefl` ↦ `gmoLtIrrefl`,
`gmo_lt_total` ↦ `gmoLtTotal`, `gmo_nlt_ge` ↦ `gmoNltGe`, `gwrites_elem_of` ↦
`gwritesElemOf`, `gwrites_nodup` ↦ `gwritesNodup`, `gwrites_lookup_elem` ↦
`gwritesLookupElem`, `gwix_lookup` ↦ `gwixLookup`, `gwix_of_lookup` ↦
`gwixOfLookup`, `gwix_pos` ↦ `WeakRvwmoGraph.gwixPos`, `gwix_le` ↦ `gwixLe`,
`gwrite_at_gwix` ↦ `gwriteAtGwix`, `gwrite_at_inv` ↦ `gwriteAtInv`,
`gwix_inj` ↦ `gwixInj`, `gwrites_sorted` ↦ `gwritesSorted`, `gwix_gpos_lt` ↦
`gwixGposLt`, `gwf_mem_gmo` ↦ `gwfMemGmo`, `gwf_gmo_mem` ↦ `gwfGmoMem`,
`gis_w_gwrites` ↦ `gisWGwrites`, `gdeps_wf` ↦ `gdepsWf`, `gdeps_gmo` ↦
`gdepsGmo`, `rvwmo_minus_deps_consistent` ↦ `rvwmoMinusDepsConsistent`,
`lbgd`, `lb_graph_deps_consistent` ↦ `lbGraphDepsConsistent`,
`glbl_is_w_gis_w` ↦ `glblIsWGisW`, `gwrites_byte_gis_w` ↦
`WeakRvwmoGraph.gwritesByteGisW`, `gppo_same_hart` ↦ `gppoSameHart`,
`gaccesses_gmem` ↦ `gaccessesGmem`, `gppo_gmem` ↦ `gppoGmem`, `gppo_po_lt` ↦
`gppoPoLt`, `gwix_zero` ↦ `gwixZero`, `gwix_elem` ↦ `gwixElem`,
`gwf_lbl_shape` ↦ `gwfLblShape`, `gread_byte_write_byte` ↦
`greadByteWriteByte`, `gread_source_byte` ↦ `greadSourceByte`.

**Not ported:** nothing.

**Statements checked** (by hand, against Rocq): all of them.
-/
import Weak.WeakAxiomatic2
import Weak.WeakLitmus

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

/-! # 1. The presentation -/

/-- An event id: (agent, position in the agent's program). -/
abbrev Geid : Type := Nat × Nat

structure Gexec where
  gxImg : Image
  gxProg : List (List Lbl)
  gxGmo : List Geid

def gxLbl (G : Gexec) (e : Geid) : Option Lbl := (G.gxProg[e.1]?).bind (fun p => p[e.2]?)

/-- Memory events: reads, writes and (W13 (M), D38 [OWN.14]) I/O-class accesses — `gmem :=
lbIsMem || lbIsIo`, so I/O events are in gmo.  Fences are program events but not memory
events — they are not in gmo. -/
def lbIsMem (l : Lbl) : Bool := lbIsR l || lbIsW l || lbIsIo l

def gmem (G : Gexec) (e : Geid) : Prop := ∃ l, gxLbl G e = some l ∧ lbIsMem l = true

/-- gmo POSITION (junk off the order; guarded by membership). -/
def gpos (G : Gexec) (e : Geid) : Nat :=
  match listFind (fun e' => decide (e' = e)) G.gxGmo with
  | some (i, _) => i
  | none => 0

def gmoLt (G : Gexec) (e1 e2 : Geid) : Prop :=
  e1 ∈ G.gxGmo ∧ e2 ∈ G.gxGmo ∧ gpos G e1 < gpos G e2

/-- The WRITE SUB-ORDER and write indices.  `gwrites G` enumerates the write
events in gmo order; a read's per-byte `ts` entry `t > 0` names
`(gwrites G)[t - 1]?`; `t = 0` names the era-initial image. -/
def gisW (G : Gexec) (e : Geid) : Bool :=
  match gxLbl G e with
  | some l => lbIsW l
  | none => false

def gwrites (G : Gexec) : List Geid := G.gxGmo.filter (gisW G)

def gwriteAt (G : Gexec) (t : Nat) : Option Geid :=
  match t with
  | 0 => none
  | i + 1 => (gwrites G)[i]?

/-- The write index of a write event (1-based; 0 is the image). -/
def gwix (G : Gexec) (e : Geid) : Nat :=
  match listFind (fun e' => decide (e' = e)) (gwrites G) with
  | some (i, _) => i + 1
  | none => 0

/-- The byte footprints, off the labels. -/
def gwritesByte (G : Gexec) (e : Geid) (a : Int) (v : BitVec 8) : Prop :=
  ∃ l base vs j, gxLbl G e = some l ∧ lbWr l = some (base, vs) ∧
    vs[j]? = some v ∧ accAddr base j = a

def greadsByte (G : Gexec) (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) : Prop :=
  ∃ l base ts vs j, gxLbl G e = some l ∧ lbRd l = some (base, ts, vs) ∧
    ts[j]? = some t ∧ vs[j]? = some v ∧ accAddr base j = a

/-- Program order. -/
def WeakRvwmoGraph.gpo (G : Gexec) (e1 e2 : Geid) : Prop :=
  e1.1 = e2.1 ∧ e1.2 < e2.2 ∧ (gxLbl G e1).isSome ∧ (gxLbl G e2).isSome

/-! # 2. Well-formedness: the order is DATA, so its sanity is an axiom -/

def gwf (G : Gexec) : Prop :=
  G.gxGmo.Nodup ∧
  (∀ e, e ∈ G.gxGmo ↔ gmem G e) ∧
  -- label shapes, as in `cand_shape`
  (∀ (i : Nat) (p : List Lbl) (k : Nat) (l : Lbl), G.gxProg[i]? = some p → p[k]? = some l →
     match l with
     | LLoad _ _ ts vs => vs.length = ts.length
     | LStore _ _ vs _ => vs ≠ []
     | LFence _ _ _ _ => True
     | LRmw _ _ _ ts rvs wvs _ =>
         wvs ≠ [] ∧ wvs.length = ts.length ∧ rvs.length = ts.length
     -- W13 (I): an I/O-class event has no shape constraint (`linCand` replays it as the inert
     -- `mstep.MStepIo`)
     | LIo .. => True)

/-! # 3. RVWMO⁻: the kept ppo arms, load-value, atomicity -/

/-- Rule 4: a fence between, with the given predecessor/successor bits. -/
def gfenceBetween (G : Gexec) (e1 e2 : Geid) (pr pw sr sw : Bool) : Prop :=
  e1.1 = e2.1 ∧ e1.2 < e2.2 ∧
  ∃ kf, e1.2 < kf ∧ kf < e2.2 ∧ gxLbl G (e1.1, kf) = some (LFence pr pw sr sw)

/-- The label classifiers, reused from `WeakAxiomatic`. -/
def glblIs (G : Gexec) (e : Geid) (P : Lbl → Bool) : Prop :=
  ∃ l, gxLbl G e = some l ∧ P l = true

/-- A read or a write IS a memory event. -/
theorem WeakRvwmoGraph.glblIsRGmem (G : Gexec) (e : Geid) : glblIs G e lbIsR → gmem G e := by
  rintro ⟨l, hl, hr⟩
  exact ⟨l, hl, by simp [lbIsMem, hr]⟩

theorem WeakRvwmoGraph.glblIsWGmem (G : Gexec) (e : Geid) : glblIs G e lbIsW → gmem G e := by
  rintro ⟨l, hl, hw⟩
  exact ⟨l, hl, by simp [lbIsMem, hw]⟩

/-- ppo⁻, the kept arms: rules 1–3 as same-byte program order; rule 4 (SOME
fence whose predecessor bit covers `e1`'s kind and whose successor bit covers
`e2`'s kind); rule 5 (`e1` an acquire read); rule 7 (an RCsc pair, `grcsc` — riscv.cat's
RCsc, deviation 7). -/
def gfenceCovers (G : Gexec) (e1 e2 : Geid) : Prop :=
  ∃ pr pw sr sw,
    gfenceBetween G e1 e2 pr pw sr sw ∧
    ((glblIs G e1 lbIsR ∧ pr = true) ∨ (glblIs G e1 lbIsW ∧ pw = true)) ∧
    ((glblIs G e2 lbIsR ∧ sr = true) ∨ (glblIs G e2 lbIsW ∧ sw = true))

/-- RULE 5.  The `gmem G e2` conjunct is NOT decoration: riscv.cat's ppo is a
relation on MEMORY ACCESSES, and `gmo` holds exactly the memory events, so an
arm whose successor may be a FENCE would be unsatisfiable rather than strong
(see the Rocq comment and `WeakRvwmoLockWit.v`'s header). -/
def gacqPo (G : Gexec) (e1 e2 : Geid) : Prop :=
  WeakRvwmoGraph.gpo G e1 e2 ∧ glblIs G e1 lbIsR ∧ glblIs G e1 lbAq ∧ gmem G e2

/-- `[W.rl];po;[R.aq]` — Rocq's RVWMO⁻ rule-7 arm, kept as a LEMMA-LEVEL name (D35-fix
[OWN.54]): `gppo`'s rule-7 arm is now the wider `grcsc`, and `grelAcq ⊆ grcsc`
(`grelAcqGrcsc`). -/
def grelAcq (G : Gexec) (e1 e2 : Geid) : Prop :=
  WeakRvwmoGraph.gpo G e1 e2 ∧ glblIs G e1 lbIsW ∧ glblIs G e1 lbRl ∧
  glblIs G e2 lbIsR ∧ glblIs G e2 lbAq

/-- RCsc, riscv.cat's reading (herd `riscv-defs.cat`: `let RCsc = (Acq|Rel|AcqRel) & (EX|X)`;
D35-fix [OWN.54]): an aq- OR rl-annotated access.  The alphabet carries the bits only on
atomics (a hart's `LLoad aq`/`LStore rl` come from LR/SC/AMO access kinds, `LRmw` from AMOs),
so the `& (EX|X)` conjunct is implicit. -/
def lbRcsc (l : Lbl) : Bool := lbAq l || lbRl l

/-- RULE 7  `[RCsc];po;[RCsc]` (riscv.cat's `r7`) — RVWMO⁻'s rule-7 arm (D35-fix [OWN.54]:
Rocq's arm is `grelAcq`; this one is `grcsc`-wide, so RVWMO⁻ ⇒ the cat model survives). -/
def grcsc (G : Gexec) (e1 e2 : Geid) : Prop :=
  WeakRvwmoGraph.gpo G e1 e2 ∧ glblIs G e1 lbRcsc ∧ glblIs G e2 lbRcsc

/-- An RCsc label is a memory label (a load, store or fused RMW) — Rocq's `lb_rcsc_bits`
(`AxGraphCat`, "an RCsc label is a fused RMW carrying both bits", FALSE under riscv.cat's
RCsc), deviation 7. -/
theorem lbRcscMem (l : Lbl) : lbRcsc l = true → lbIsMem l = true := by
  cases l <;> simp +contextual [lbRcsc, lbAq, lbRl, lbIsMem, lbIsW, lbIsR]

theorem glblIsRcscGmem (G : Gexec) (e : Geid) : glblIs G e lbRcsc → gmem G e := by
  rintro ⟨l, hl, h⟩
  exact ⟨l, hl, lbRcscMem l h⟩

/-- Rocq's RVWMO⁻ rule-7 arm `[W.rl];po;[R.aq]` is an RCsc pair (riscv.cat's reading).  The
converse (Rocq's `grcsc_grel_acq`) is FALSE under riscv.cat's RCsc: two `LStore true` in po
are `grcsc` but not `grelAcq`. -/
theorem grelAcqGrcsc (G : Gexec) (e1 e2 : Geid) : grelAcq G e1 e2 → grcsc G e1 e2 := by
  rintro ⟨hpo, _, ⟨l1, hl1, r1⟩, _, ⟨l2, hl2, a2⟩⟩
  exact ⟨hpo, ⟨l1, hl1, by simp [lbRcsc, r1]⟩, ⟨l2, hl2, by simp [lbRcsc, a2]⟩⟩

def gaccesses (G : Gexec) (e : Geid) (a : Int) : Prop :=
  (∃ v, gwritesByte G e a v) ∨ (∃ t v, greadsByte G e a t v)

def gpoloc (G : Gexec) (e1 e2 : Geid) : Prop :=
  WeakRvwmoGraph.gpo G e1 e2 ∧ ∃ a, gaccesses G e1 a ∧ gaccesses G e2 a

def gppo (G : Gexec) (e1 e2 : Geid) : Prop :=
  gpoloc G e1 e2 ∨ gfenceCovers G e1 e2 ∨ gacqPo G e1 e2 ∨ grcsc G e1 e2

def gppoGmo (G : Gexec) : Prop := ∀ e1 e2, gppo G e1 e2 → gmoLt G e1 e2

/-- LOAD VALUE.  A read's named source must exist, cover the byte with the
value, be visible ((gmo ∪ po)-before the read — the po disjunct is store
forwarding), and be co-MAXIMAL among visible same-byte writes.  `t = 0` (the
image) additionally requires NO visible same-byte write at all. -/
def gvisible (G : Gexec) (w r : Geid) : Prop := gmoLt G w r ∨ WeakRvwmoGraph.gpo G w r

def gloadValue (G : Gexec) : Prop :=
  ∀ e a t v, greadsByte G e a t v →
    (match t with
     | 0 => G.gxImg a = some v
     | _ + 1 => ∃ w, gwriteAt G t = some w ∧ gwritesByte G w a v ∧ gvisible G w e) ∧
    (∀ w' v', gwritesByte G w' a v' → gvisible G w' e → gwix G w' ≤ t)

/-- ATOMICITY (the fused RMW): no same-byte write co-between the read source and
the RMW's own write. -/
def gatomicity (G : Gexec) : Prop :=
  ∀ e a t v, greadsByte G e a t v → glblIs G e lbIsW →
    ∀ w' v', gwritesByte G w' a v' →
      ¬ (t < gwix G w' ∧ gwix G w' < gwix G e)

def rvwmoMinusConsistent (G : Gexec) : Prop :=
  gwf G ∧ gppoGmo G ∧ gloadValue G ∧ gatomicity G

/-- RULE 14, as the graph-side gate the linearization (T2-1c) consumes: a
memory event po-before a write is gmo-before it. -/
def grule14 (G : Gexec) : Prop :=
  ∀ e w, WeakRvwmoGraph.gpo G e w → gmem G e → glblIs G w lbIsW → gmoLt G e w

/-! # 4. The embedding: every `Cand` IS a graph -/

def graphOfCand (c : Cand) : Gexec :=
  ⟨c.cdImg,
   (List.range' 0 ((c.cdTr.map Estep.esAg).foldr max 0 + 1)).map
     (fun i => (c.cdTr.filter (fun s => decide (s.esAg = i))).map (fun s => s.esLb)),
   (((c.cdTr.mapIdx (fun i s => (i, s))).filter (fun ks : Nat × Estep => lbIsMem ks.2.esLb)).map
     (fun ks : Nat × Estep =>
       (ks.2.esAg, ((c.cdTr.take ks.1).filter (fun s => decide (s.esAg = ks.2.esAg))).length)))⟩

/-! # 5. THE NON-COLLAPSE WITNESS: LB is RVWMO⁻-consistent

The four-event load-buffering execution — each hart reads the OTHER hart's
po-later store — with gmo placing both stores FIRST.  sRVWMO forbids this
outcome for every conformant candidate; RVWMO⁻ admits it, so the tier-2 gap is
real and this model is not sRVWMO in disguise. -/

def lbg : Gexec :=
  ⟨img0,
   [[LLoad false 0 [2] [b1], LStore false 8 [b1] .WCplain],
    [LLoad false 8 [1] [b1], LStore false 0 [b1] .WCplain]],
   [(0, 1), (1, 1), (0, 0), (1, 0)]⟩

/-- Lean-only: the four labels of `lbg`. -/
theorem lbgLbl (e : Geid) (l : Lbl) : gxLbl lbg e = some l →
    (e = (0, 0) ∧ l = LLoad false 0 [2] [b1]) ∨
    (e = (0, 1) ∧ l = LStore false 8 [b1] .WCplain) ∨
    (e = (1, 0) ∧ l = LLoad false 8 [1] [b1]) ∨
    (e = (1, 1) ∧ l = LStore false 0 [b1] .WCplain) := by
  obtain ⟨i, k⟩ := e
  intro hl
  rcases i with _ | _ | i <;> rcases k with _ | _ | k <;> simp [gxLbl, lbg] at hl <;>
    subst hl <;> simp

/-- The byte each `lbg` event accesses — the poloc refutation's engine. -/
theorem lbgAcc (e : Geid) (a : Int) :
    gaccesses lbg e a →
    (e = (0, 0) ∧ a = 0) ∨ (e = (0, 1) ∧ a = 8) ∨
    (e = (1, 0) ∧ a = 8) ∨ (e = (1, 1) ∧ a = 0) := by
  rintro (⟨v, l, base, vs, j, hl, hwr, hv, ha⟩ | ⟨t, v, l, base, ts, vs, j, hl, hrd, ht, hv, ha⟩)
  · rcases lbgLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [lbWr] at hwr <;> obtain ⟨rfl, rfl⟩ := hwr <;>
      rcases j with _ | j <;> simp at hv <;> simp [accAddr] at ha <;> subst ha <;> simp
  · rcases lbgLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [lbRd] at hrd <;> obtain ⟨rfl, rfl, rfl⟩ := hrd <;>
      rcases j with _ | j <;> simp at hv <;> simp [accAddr] at ha <;> subst ha <;> simp

theorem lbgWr (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte lbg e a v →
    (e = (0, 1) ∧ a = 8) ∨ (e = (1, 1) ∧ a = 0) := by
  rintro ⟨l, base, vs, j, hl, hwr, hv, ha⟩
  rcases lbgLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [lbWr] at hwr <;> obtain ⟨rfl, rfl⟩ := hwr <;>
    rcases j with _ | j <;> simp at hv <;> simp [accAddr] at ha <;> subst ha <;> simp

theorem lbGraphConsistent : rvwmoMinusConsistent lbg := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- gwf: NoDup
    decide
  · intro e
    constructor
    · intro he
      simp only [lbg, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, rfl⟩
    · rintro ⟨l, hl, hm⟩
      rcases lbgLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · intro i p k l hp hk
    rcases i with _ | _ | i <;> simp [lbg] at hp <;> subst hp <;>
      rcases k with _ | _ | k <;> simp at hk <;> subst hk <;> simp
  · -- gppo⁻ ⊆ gmo: there are NO ppo⁻ edges — different bytes per hart, no
    -- fences, no acquires, no releases
    intro e1 e2 hppo
    exfalso
    rcases hppo with hpl | hf | ha | hr
    · -- poloc: the two events of one hart touch different bytes
      obtain ⟨⟨hag, hlt, _, _⟩, a, h1, h2⟩ := hpl
      rcases lbgAcc e1 a h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases lbgAcc e2 _ h2 with ⟨rfl, ha2⟩ | ⟨rfl, ha2⟩ | ⟨rfl, ha2⟩ | ⟨rfl, ha2⟩ <;>
        simp at hag hlt ha2
    · obtain ⟨pr, pw, sr, sw, ⟨_, _, kf, _, _, hlf⟩, _, _⟩ := hf
      rcases lbgLbl _ _ hlf with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
    · obtain ⟨_, ⟨l, hl, _⟩, ⟨l', hl', haq⟩, _⟩ := ha
      rw [hl, Option.some.injEq] at hl'
      subst hl'
      rcases lbgLbl _ _ hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [lbAq] at haq
    · obtain ⟨_, ⟨l, hl, hrc⟩, _⟩ := hr
      rcases lbgLbl _ _ hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
        simp [lbRcsc, lbAq, lbRl] at hrc
  · -- load value
    intro e a t v hr
    obtain ⟨l, base, ts, vs, j, hl, hrd, hj, hv, ha⟩ := hr
    rcases lbgLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [lbRd] at hrd <;> obtain ⟨rfl, rfl, rfl⟩ := hrd <;>
      rcases j with _ | j <;> simp at hj hv <;> subst hj hv <;>
      simp [accAddr] at ha <;> subst ha
    · -- hart 0 reads byte 0 at write index 2 = hart 1's store to 0
      refine ⟨?_, ?_⟩
      · show ∃ w, gwriteAt lbg 2 = some w ∧ gwritesByte lbg w 0 b1 ∧ gvisible lbg w (0, 0)
        refine ⟨(1, 1), by decide, ⟨LStore false 0 [b1] .WCplain, 0, [b1], 0, rfl, rfl, rfl,
          by simp [accAddr]⟩, Or.inl ⟨by decide, by decide, by decide⟩⟩
      · intro w' v' hw' _
        rcases lbgWr w' _ _ hw' with ⟨rfl, hab⟩ | ⟨rfl, _⟩
        · simp at hab
        · decide
    · -- hart 1 reads byte 8 at write index 1 = hart 0's store to 8
      refine ⟨?_, ?_⟩
      · show ∃ w, gwriteAt lbg 1 = some w ∧ gwritesByte lbg w 8 b1 ∧ gvisible lbg w (1, 0)
        refine ⟨(0, 1), by decide, ⟨LStore false 8 [b1] .WCplain, 8, [b1], 0, rfl, rfl, rfl,
          by simp [accAddr]⟩, Or.inl ⟨by decide, by decide, by decide⟩⟩
      · intro w' v' hw' _
        rcases lbgWr w' _ _ hw' with ⟨rfl, _⟩ | ⟨rfl, hab⟩
        · decide
        · simp at hab
  · -- atomicity: no event both reads and writes
    intro e a t v hr ⟨l, hl, hw⟩
    obtain ⟨l', base, ts, vs, j, hl', hrd, _⟩ := hr
    rw [hl, Option.some.injEq] at hl'
    subst hl'
    rcases lbgLbl e l hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      simp [lbIsW, lbRd] at hw hrd

/-! # 6. POSITION ARITHMETIC (additive; consumed by `WeakRvwmoLin`)

The rule-14 linearization is all `gpos`/`gwix` bookkeeping.  Two facts carry
it: `gmo` is TOTAL on its members (the order is a `Nodup` list), and the write
sub-order `gwrites` is a FILTER of `gxGmo` — hence write indices and gmo
positions order the writes THE SAME WAY (`gwixGposLt`). -/

/-! ## Sortedness by lookup — the generic kit the filter argument needs -/

theorem stronglySortedLookupElim {A : Type _} (R : A → A → Prop) (l : List A) (i j : Nat)
    (x y : A) :
    List.Pairwise R l → l[i]? = some x → l[j]? = some y → i < j → R x y := by
  intro hss hi hj hlt
  rw [List.getElem?_eq_some_iff] at hi hj
  obtain ⟨hi', rfl⟩ := hi
  obtain ⟨hj', rfl⟩ := hj
  exact List.pairwise_iff_getElem.1 hss i j hi' hj' hlt

theorem stronglySortedLookupIntro {A : Type _} (R : A → A → Prop) (l : List A) :
    (∀ (i j : Nat) (x y : A), l[i]? = some x → l[j]? = some y → i < j → R x y) →
    List.Pairwise R l := by
  intro h
  refine List.pairwise_iff_getElem.2 ?_
  intro i j hi hj hlt
  exact h i j _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hlt

theorem stronglySortedFilter {A : Type _} (R : A → A → Prop) (p : A → Bool) (l : List A) :
    List.Pairwise R l → List.Pairwise R (l.filter p) :=
  fun h => h.sublist List.filter_sublist

/-! ## `gpos`: the gmo position of a member -/

theorem gposLookup (G : Gexec) (e : Geid) :
    e ∈ G.gxGmo → ∃ i, G.gxGmo[i]? = some e ∧ gpos G e = i := by
  intro he
  unfold gpos
  cases hf : listFind (fun e' => decide (e' = e)) G.gxGmo with
  | some q =>
    obtain ⟨i, x⟩ := q
    obtain ⟨hi, hx, _⟩ := list_find_Some.1 hf
    have : x = e := of_decide_eq_true hx
    subst this
    exact ⟨i, hi, rfl⟩
  | none =>
    have := list_find_None.1 hf e he
    simp at this

theorem gposElemLookup (G : Gexec) (e : Geid) : e ∈ G.gxGmo → G.gxGmo[gpos G e]? = some e := by
  intro he
  obtain ⟨i, hi, h⟩ := gposLookup G e he
  rw [h]; exact hi

theorem gposOfLookup (G : Gexec) (i : Nat) (e : Geid) :
    G.gxGmo.Nodup → G.gxGmo[i]? = some e → gpos G e = i := by
  intro hnd hi
  obtain ⟨i', hi', h⟩ := gposLookup G e (elem_of_list_lookup_2 hi)
  rw [h]
  exact NoDup_lookup hnd hi' hi

theorem gposLtLen (G : Gexec) (e : Geid) : e ∈ G.gxGmo → gpos G e < G.gxGmo.length :=
  fun he => lookup_lt_Some (gposElemLookup G e he)

theorem gposInj (G : Gexec) (e1 e2 : Geid) :
    G.gxGmo.Nodup → e1 ∈ G.gxGmo → e2 ∈ G.gxGmo → gpos G e1 = gpos G e2 → e1 = e2 := by
  intro _ h1 h2 heq
  have l1 := gposElemLookup G e1 h1
  have l2 := gposElemLookup G e2 h2
  rw [heq, l2, Option.some.injEq] at l1
  exact l1.symm

theorem gmoLtTrans (G : Gexec) (e1 e2 e3 : Geid) :
    gmoLt G e1 e2 → gmoLt G e2 e3 → gmoLt G e1 e3 := by
  rintro ⟨h1, _, h12⟩ ⟨_, h3, h23⟩
  exact ⟨h1, h3, by omega⟩

theorem gmoLtIrrefl (G : Gexec) (e : Geid) : ¬ gmoLt G e e := by
  rintro ⟨_, _, h⟩
  omega

/-- TOTALITY on members: the missing half of "gmo is a strict total order". -/
theorem gmoLtTotal (G : Gexec) (e1 e2 : Geid) :
    G.gxGmo.Nodup → e1 ∈ G.gxGmo → e2 ∈ G.gxGmo → e1 ≠ e2 →
    gmoLt G e1 e2 ∨ gmoLt G e2 e1 := by
  intro hnd h1 h2 hne
  by_cases hlt : gpos G e1 < gpos G e2
  · exact .inl ⟨h1, h2, hlt⟩
  · refine .inr ⟨h2, h1, ?_⟩
    by_cases heq : gpos G e1 = gpos G e2
    · exact absurd (gposInj G e1 e2 hnd h1 h2 heq) hne
    · omega

/-- The contrapositive shape the load-value axiom hands back: not gmo-before
means at-or-after. -/
theorem gmoNltGe (G : Gexec) (e1 e2 : Geid) :
    G.gxGmo.Nodup → e1 ∈ G.gxGmo → e2 ∈ G.gxGmo →
    ¬ gmoLt G e1 e2 → gpos G e2 ≤ gpos G e1 := by
  intro _ h1 h2 hn
  by_cases hlt : gpos G e1 < gpos G e2
  · exact absurd ⟨h1, h2, hlt⟩ hn
  · omega

/-! ## `gwrites` / `gwix`: the write sub-order -/

theorem gwritesElemOf (G : Gexec) (e : Geid) :
    e ∈ gwrites G ↔ e ∈ G.gxGmo ∧ gisW G e = true := by
  unfold gwrites
  rw [elem_of_list_filter]
  exact And.comm

theorem gwritesNodup (G : Gexec) : G.gxGmo.Nodup → (gwrites G).Nodup :=
  fun hnd => NoDup_filter hnd

theorem gwritesLookupElem (G : Gexec) (i : Nat) (w : Geid) :
    (gwrites G)[i]? = some w → w ∈ gwrites G :=
  fun hi => elem_of_list_lookup_2 hi

theorem gwixLookup (G : Gexec) (w : Geid) :
    w ∈ gwrites G → ∃ i, (gwrites G)[i]? = some w ∧ gwix G w = i + 1 := by
  intro he
  unfold gwix
  cases hf : listFind (fun e' => decide (e' = w)) (gwrites G) with
  | some q =>
    obtain ⟨i, x⟩ := q
    obtain ⟨hi, hx, _⟩ := list_find_Some.1 hf
    have : x = w := of_decide_eq_true hx
    subst this
    exact ⟨i, hi, rfl⟩
  | none =>
    have := list_find_None.1 hf w he
    simp at this

theorem gwixOfLookup (G : Gexec) (i : Nat) (w : Geid) :
    G.gxGmo.Nodup → (gwrites G)[i]? = some w → gwix G w = i + 1 := by
  intro hnd hi
  obtain ⟨i', hi', h⟩ := gwixLookup G w (gwritesLookupElem G i w hi)
  rw [h, NoDup_lookup (gwritesNodup G hnd) hi' hi]

theorem WeakRvwmoGraph.gwixPos (G : Gexec) (w : Geid) : w ∈ gwrites G → 0 < gwix G w := by
  intro he
  obtain ⟨i, _, h⟩ := gwixLookup G w he
  omega

theorem gwixLe (G : Gexec) (w : Geid) : w ∈ gwrites G → gwix G w ≤ (gwrites G).length := by
  intro he
  obtain ⟨i, hi, h⟩ := gwixLookup G w he
  have := lookup_lt_Some hi
  omega

theorem gwriteAtGwix (G : Gexec) (w : Geid) : w ∈ gwrites G → gwriteAt G (gwix G w) = some w := by
  intro he
  obtain ⟨i, hi, h⟩ := gwixLookup G w he
  rw [h]
  exact hi

theorem gwriteAtInv (G : Gexec) (t : Nat) (w : Geid) :
    G.gxGmo.Nodup → gwriteAt G t = some w → w ∈ gwrites G ∧ gwix G w = t := by
  cases t with
  | zero => intro _ h; simp [gwriteAt] at h
  | succ i =>
    intro hnd hi
    exact ⟨gwritesLookupElem G i w hi, gwixOfLookup G i w hnd hi⟩

theorem gwixInj (G : Gexec) (w1 w2 : Geid) :
    G.gxGmo.Nodup → w1 ∈ gwrites G → w2 ∈ gwrites G → gwix G w1 = gwix G w2 → w1 = w2 := by
  intro _ h1 h2 heq
  obtain ⟨i1, hi1, e1⟩ := gwixLookup G w1 h1
  obtain ⟨i2, hi2, e2⟩ := gwixLookup G w2 h2
  have : i1 = i2 := by omega
  subst this
  rw [hi1, Option.some.injEq] at hi2
  exact hi2

/-- THE ORDER-PRESERVATION FACT: `gwrites` is a filter of `gxGmo`, so a write's
INDEX and its gmo POSITION agree on order. -/
theorem gwritesSorted (G : Gexec) :
    G.gxGmo.Nodup → List.Pairwise (fun x y => gpos G x < gpos G y) (gwrites G) := by
  intro hnd
  apply stronglySortedFilter
  apply stronglySortedLookupIntro
  intro i j x y hi hj hlt
  rw [gposOfLookup G i x hnd hi, gposOfLookup G j y hnd hj]
  exact hlt

theorem gwixGposLt (G : Gexec) (w1 w2 : Geid) :
    G.gxGmo.Nodup → w1 ∈ gwrites G → w2 ∈ gwrites G →
    (gwix G w1 < gwix G w2 ↔ gpos G w1 < gpos G w2) := by
  intro hnd h1 h2
  obtain ⟨i1, hi1, e1⟩ := gwixLookup G w1 h1
  obtain ⟨i2, hi2, e2⟩ := gwixLookup G w2 h2
  have hss := gwritesSorted G hnd
  constructor
  · intro hlt
    exact stronglySortedLookupElim _ _ i1 i2 w1 w2 hss hi1 hi2 (by omega)
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
    have hgt := stronglySortedLookupElim _ _ i2 i1 w2 w1 hss hi2 hi1 (by omega)
    omega

/-- `gwf`'s membership clause, in the direction the linearization uses. -/
theorem gwfMemGmo (G : Gexec) (e : Geid) : gwf G → gmem G e → e ∈ G.gxGmo :=
  fun hwf he => (hwf.2.1 e).2 he

theorem gwfGmoMem (G : Gexec) (e : Geid) : gwf G → e ∈ G.gxGmo → gmem G e :=
  fun hwf he => (hwf.2.1 e).1 he

/-- A write EVENT (label-level) is a member of the write sub-order. -/
theorem gisWGwrites (G : Gexec) (e : Geid) :
    gwf G → (gxLbl G e).isSome → gisW G e = true → e ∈ gwrites G := by
  intro hwf hs hw
  obtain ⟨l, hl⟩ := someOfIsSome hs
  refine (gwritesElemOf G e).2 ⟨gwfMemGmo G e hwf ⟨l, hl, ?_⟩, hw⟩
  simp only [gisW, hl] at hw
  simp [lbIsMem, hw]

/-! # 7. The dependency fragment (route B, stage B0)

Bare RVWMO⁻ admits thin-air, so the tier-2 capstone's hypothesis must carry the
STORE-DEP FRAGMENT, as graph DATA: a list of (read, store) event pairs —
address/data deps into stores (rules 9/10's store halves), control deps into
stores (rule 11), and the W-TV translation edge — with the ordering axiom
`gdepsGmo`.  Sources are always READS.  Adding constraints SHRINKS the declared
model toward RVWMO, and every added edge class is ⊆ RVWMO's own ppo.  The
CONFORMANCE clause is a capstone-level hypothesis, deliberately NOT part of
consistency. -/

structure Gdexec where
  gdG : Gexec
  gdDeps : List (Geid × Geid)

/-- Well-formedness: each edge runs from a READ to a po-LATER WRITE of the same
hart. -/
def gdepsWf (G : Gexec) (deps : List (Geid × Geid)) : Prop :=
  ∀ rw : Geid × Geid, rw ∈ deps →
    rw.1.1 = rw.2.1 ∧ rw.1.2 < rw.2.2 ∧ glblIs G rw.1 lbIsR ∧ glblIs G rw.2 lbIsW

/-- THE ORDERING AXIOM — the ppo 9–13 store fragment: a dep-source read is
globally ordered before its dependent store. -/
def gdepsGmo (G : Gexec) (deps : List (Geid × Geid)) : Prop :=
  ∀ rw : Geid × Geid, rw ∈ deps → gmoLt G rw.1 rw.2

def rvwmoMinusDepsConsistent (GD : Gdexec) : Prop :=
  rvwmoMinusConsistent GD.gdG ∧ gdepsWf GD.gdG GD.gdDeps ∧ gdepsGmo GD.gdG GD.gdDeps

/-- NON-COLLAPSE, re-checked for the extended model: LB's load;store pairs are
syntactically independent, so the LB witness carries the EMPTY dep set and
stays consistent. -/
def lbgd : Gdexec := ⟨lbg, []⟩

theorem lbGraphDepsConsistent : rvwmoMinusDepsConsistent lbgd :=
  ⟨lbGraphConsistent, fun _ h => by simp [lbgd] at h, fun _ h => by simp [lbgd] at h⟩

/-! # 8. ADDITIVE HELPERS for the exchange kit (route B, stage B2) -/

theorem glblIsWGisW (G : Gexec) (e : Geid) : glblIs G e lbIsW → gisW G e = true := by
  rintro ⟨l, hl, hw⟩
  simp [gisW, hl, hw]

/-- (Named `_gis_w`, not `_is_w`: `WeakRvwmoLin.v` has a SECTION-LOCAL
`gwrites_byte_is_w` whose conclusion is the `glblIs` form.) -/
theorem WeakRvwmoGraph.gwritesByteGisW (G : Gexec) (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte G e a v → gisW G e = true := by
  rintro ⟨l, base, vs, j, hl, hwr, _, _⟩
  simp only [gisW, hl]
  exact lbWrIsW l _ hwr

/-- EVERY ppo⁻ ARM IS SAME-HART — each of the four disjuncts carries either
`gpo` or `gfenceBetween`, both of which pin the agent. -/
theorem gppoSameHart (G : Gexec) (e1 e2 : Geid) : gppo G e1 e2 → e1.1 = e2.1 := by
  rintro (⟨⟨hag, _⟩, _⟩ | ⟨_, _, _, _, ⟨hag, _⟩, _, _⟩ | ⟨⟨hag, _⟩, _⟩ | ⟨⟨hag, _⟩, _⟩) <;>
    exact hag

/-- EVERY ppo⁻ ARM IS MEMORY-TO-MEMORY (`ppo ⊆ M × M`, riscv.cat's own typing). -/
theorem gaccessesGmem (G : Gexec) (e : Geid) (a : Int) : gaccesses G e a → gmem G e := by
  rintro (⟨v, l, base, vs, j, hl, hwr, _⟩ | ⟨t, v, l, base, ts, vs, j, hl, hrd, _⟩)
  · exact WeakRvwmoGraph.glblIsWGmem G e ⟨l, hl, lbWrIsW l _ hwr⟩
  · exact WeakRvwmoGraph.glblIsRGmem G e ⟨l, hl, lbRdIsR l _ hrd⟩

theorem gppoGmem (G : Gexec) (e1 e2 : Geid) : gppo G e1 e2 → gmem G e1 ∧ gmem G e2 := by
  rintro (⟨_, a, h1, h2⟩ | ⟨_, _, _, _, _, h1, h2⟩ | ⟨_, h1, _, h2⟩ | ⟨_, h1, h2⟩)
  · exact ⟨gaccessesGmem G e1 a h1, gaccessesGmem G e2 a h2⟩
  · refine ⟨?_, ?_⟩
    · rcases h1 with ⟨h, _⟩ | ⟨h, _⟩
      · exact WeakRvwmoGraph.glblIsRGmem G e1 h
      · exact WeakRvwmoGraph.glblIsWGmem G e1 h
    · rcases h2 with ⟨h, _⟩ | ⟨h, _⟩
      · exact WeakRvwmoGraph.glblIsRGmem G e2 h
      · exact WeakRvwmoGraph.glblIsWGmem G e2 h
  · exact ⟨WeakRvwmoGraph.glblIsRGmem G e1 h1, h2⟩
  · exact ⟨glblIsRcscGmem G e1 h1, glblIsRcscGmem G e2 h2⟩

/-- ... AND PO-EARLIER: `gpo` and `gfenceBetween` both carry `e1.2 < e2.2`. -/
theorem gppoPoLt (G : Gexec) (e1 e2 : Geid) : gppo G e1 e2 → e1.1 = e2.1 ∧ e1.2 < e2.2 := by
  rintro (⟨⟨hag, hlt, _⟩, _⟩ | ⟨_, _, _, _, ⟨hag, hlt, _⟩, _, _⟩ | ⟨⟨hag, hlt, _⟩, _⟩ |
    ⟨⟨hag, hlt, _⟩, _⟩) <;> exact ⟨hag, hlt⟩

/-! ## 8.1 `gwix`'s junk value, and its contrapositive

`gwix` is `0` off the write sub-order, so a NONZERO write index is itself a
membership certificate. -/

theorem gwixZero (G : Gexec) (w : Geid) : w ∉ gwrites G → gwix G w = 0 := by
  intro hnin
  unfold gwix
  cases hf : listFind (fun e' => decide (e' = w)) (gwrites G) with
  | none => rfl
  | some q =>
    exfalso
    obtain ⟨i, z⟩ := q
    obtain ⟨hi, hz, _⟩ := list_find_Some.1 hf
    have : z = w := of_decide_eq_true hz
    subst this
    exact hnin (elem_of_list_lookup_2 hi)

theorem gwixElem (G : Gexec) (w : Geid) : 0 < gwix G w → w ∈ gwrites G := by
  intro hpos
  by_cases h : w ∈ gwrites G
  · exact h
  · rw [gwixZero G w h] at hpos
    omega

/-! ## 8.2 `gwf`'s shape clause, at an EVENT -/

theorem gwfLblShape (G : Gexec) (e : Geid) (l : Lbl) :
    gwf G → gxLbl G e = some l →
    match l with
    | LLoad _ _ ts vs => vs.length = ts.length
    | LStore _ _ vs _ => vs ≠ []
    | LFence _ _ _ _ => True
    | LRmw _ _ _ ts rvs wvs _ =>
        wvs ≠ [] ∧ wvs.length = ts.length ∧ rvs.length = ts.length
    | LIo .. => True := by
  intro hwf hl
  obtain ⟨_, _, hsh⟩ := hwf
  unfold gxLbl at hl
  cases hp : G.gxProg[e.1]? with
  | none => rw [hp] at hl; simp at hl
  | some p =>
    rw [hp] at hl
    exact hsh e.1 p e.2 l hp hl

/-- (Lean-only, W13 (I)) A RAM read or write is a memory event (`lbIsMem` also holds of the
I/O class, so the converse is false once `gwf` admits `LIo`). -/
theorem WeakRvwmoGraph.lbIsMemOfRW (l : Lbl) : (lbIsR l || lbIsW l) = true → lbIsMem l = true := by
  intro h; simp [lbIsMem, h]

/-! ## 8.3 A FUSED RMW'S READ FOOTPRINT IS ITS WRITE FOOTPRINT -/

theorem greadByteWriteByte (G : Gexec) (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    gwf G → gisW G e = true → greadsByte G e a t v →
    ∃ v', gwritesByte G e a v' := by
  rintro hwf hw ⟨l, base, ts, vs, j, hl, hrd, ht, hv, ha⟩
  have hsh := gwfLblShape G e l hwf hl
  simp only [gisW, hl] at hw
  have hwr : ∃ wvs, lbWr l = some (base, wvs) ∧ wvs.length = ts.length := by
    cases l with
    | LLoad => simp [lbIsW] at hw
    | LStore => simp [lbRd] at hrd
    | LFence => simp [lbIsW] at hw
    | LRmw aq rl b ts' rvs wvs k =>
      have hsh' : wvs ≠ [] ∧ wvs.length = ts'.length ∧ rvs.length = ts'.length := hsh
      simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
      obtain ⟨rfl, rfl, rfl⟩ := hrd
      exact ⟨wvs, rfl, hsh'.2.1⟩
    | LIo => simp [lbIsW] at hw
  obtain ⟨wvs, hwr, hlen⟩ := hwr
  have hj : j < wvs.length := by rw [hlen]; exact lookup_lt_Some ht
  obtain ⟨v', hv'⟩ := someOfIsSome (lookup_lt_is_Some_2 hj)
  exact ⟨v', l, base, wvs, j, hl, hwr, hv', ha⟩

/-! ## 8.4 A read's NAMED SOURCE covers the byte with the read value -/

theorem greadSourceByte (G : Gexec) (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) (w : Geid) :
    gloadValue G → greadsByte G e a t v → gwriteAt G t = some w →
    gwritesByte G w a v := by
  intro hlv hrd hwat
  obtain ⟨hsrc, _⟩ := hlv e a t v hrd
  cases t with
  | zero => simp [gwriteAt] at hwat
  | succ t =>
    obtain ⟨w0, hw0, hwb, _⟩ := hsrc
    rw [hwat, Option.some.injEq] at hw0
    subst hw0
    exact hwb

end Weak
