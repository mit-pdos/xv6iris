/-
Weak: **the W5d-G fetch spike, RE-CREATED** (plan rev 18 §C W5d-G "G0 — Day one", §B(4)(iii);
D27 RULED (a) [OWN.6], D41 RULED (a) [OWN.16], D42–D43 RULED (a) [OWN.18]).  Lean-only scratch,
no Rocq twin; imported by no root.

The Stage-0 spike's Lean file (226 lines, 2026-10-09) was lost before jj snapshotted it
[R10.4][OWN.18].  This file re-creates it from the report `notes/W5dG-spike.md`: VERBATIM where
the report's §2 gives Lean (`gwlog`, `gfcut`, `gzContrib`, `gzFetch`; `emZifencei` up to R8's slot
function), and from the
report's prose (§0, §2 "Kernel-text instance", §3) plus plan §B(4)(iii) where it does not.

What it does.  The fetch stays an ADMINISTRATIVE emission item (report §0).  The graph-tier
Zifencei condition `gzFetch` (the NAMED trusted-base item, readings (H1)–(H3), no reference
model) names no cut.  The cut form `fetchCutOk` (ONE view `q`) is what the pf machine and TsoMem
consume.  Proved here, at the level of logs and indices (the graph-to-index transport is G4's):
- `fetchRelCut`: the RELATIONAL form `fetchRelOk` ((Z1)–(Z3) over write indices, contributor
  indices `cs`) gives the cut form at `itv := lmax cs`; `fetchCutEdge` / `fetchCutRel`: the
  converse — the cut form gives the edges, so the relational form loses nothing.
- `fetchCutPrefix`: the cut form on the full log, bounded by `cut`, is the pf/W5d check at the
  realizing prefix `log.take cut`, with ONE view, and implies the per-byte check at any lower
  i-view.
- `fetchPinCutOk`: the kernel-text instance (tag 0, image bytes, no write to the bytes).
Stated, nothing proved about them (as in the spike): `gzFetch`, `gzFetchCut`, `emZifencei`,
`gfcut`, `gwlog` (and `gzContrib`, which the report's Lean block also carries).

**Re-creation record: where the report is ambiguous, and how it is resolved.**

R1. `fetchCutOk`'s shape.  Report §0: "∃ q with itv ≤ q ≤ next-own-write" on the normalized
    graph; report §3.4 (and the plan's cite of `GraphFetchSpike.lean:36`): "∃ q, itv ≤ q ≤ |log| ∧
    ifetchOk img log q base tvs"; plan §B(4)(iii) [W2s](i), written after the spike: the cut form
    ADDS `t ≤ q` per byte (else a byte source above `q` passes `ifetchByteOk … q` vacuously and
    TsoMem at `tvn := q` cannot read it).  RESOLVED: one predicate with an explicit bound `cut`
    (`cut := log.length` is the M2 clause, `cut := gfcut G i k` over `gwlog G` the graph form
    "≤ next-own-write") carrying the [W2s] conjunct.  This is STRONGER than the report's literal:
    every theorem concluding it (`fetchRelCut`, `fetchPinCutOk`) is stronger, and
    `GraphFetchSpike.fetchCutOkLit` recovers the literal.  Evidence the bound belongs in the form:
    without it the full-log `fetchCutPrefix` is FALSE (a source may lie above the cut) and
    `fetchCutEdge`'s E1/E3 fail.
R2. "Proved: `fetchCutOk`, `fetchRelOk`".  Both are FORMS in the report's own prose (§0 "a
    single-cut form (`fetchCutOk`, …)"; §3.2 "gives `fetchRelOk` at `GD'`").  RESOLVED:
    definitions, with every proved theorem stated about them; the "stated" list is what the
    report says nothing is proved about.
R3. `fetchCutPrefix`: no Lean in the report.  From §3.3 ("replayed … where the log is
    `gwlog.take (gfcut)` … the pf/Ev itv there is ≤ lmax cs … gives `ifetchOk img prefix itv` AND
    a single view q").  RESOLVED: premises `cut ≤ |log|`, the floor bound `itv ≤ itv0`, the cut
    form at `itv0` on the full log; conclusions the M2 cut form at `log.take cut` (bound
    `(log.take cut).length`) AND `ifetchOk img (log.take cut) itv`.
R4. `fetchCutEdge`: the report gives only the name.  RESOLVED as the converse of `fetchRelCut`
    in edge terms: from the cut form, E1 as `t ≤ cut`, E2 with the i-view standing for the
    contributors (`itv < t'`), E3 (`tl < t'`), for every write `t'` to a fetched byte co-after its
    source.  `GraphFetchSpike.fetchCutRel` packages it as `fetchRelOk … [itv]`.
R5. `fetchRelOk` / `fetchRelCut`: no Lean in the report.  RESOLVED as the index transport of
    `gzFetch`: (Z1) verbatim over the log; (Z2) `gmoLt src nxw` ↦ `t ≤ cut` (`t < gwix nxw` iff
    `t ≤ gfcut`); (Z3) `gmoLt c w'` ↦ `c < t'` over the contributor INDICES `cs`, `gmoLt wl w'` ↦
    `tl < t'` (for `tl = 0`, which `gzFetch` leaves unconstrained since `gwriteAt G 0 = none`,
    `tl < t'` holds anyway as `t < t'`), the writes `w'` being the indices `t'` whose entry writes
    the byte.  The contributors' bound "≤ gfcut, DERIVED … not assumed" (§3.2) is a conjunct G4
    derives.  `lmax cs` ↦ `cs.foldr max 0` (stdpp `list_max`, `WeakRvwmoGraph` deviation 2).
R6. `gzFetchCut`: no Lean in the report.  RESOLVED as the cut form on the FULL `gwlog G` bounded
    by `gfcut G i k` (§0 "on the normalized graph", "≤ next-own-write"); `fetchCutPrefix` moves it
    to the realizing prefix (§3.3), and `fetchRelCut` at `(gwlog G, gfcut G i k)` produces it with
    [W2s]'s per-byte bound (plan: "G5's `gzFetchCut` must produce it").  `itv` is a parameter.
R7. `gzContrib`'s docstring says "variant (b), §5 Q-G2", but its body is Q-G2's (a) — the
    SUPERSET "everything the hart wrote or read before fence.i" ((b) is the exact `itvPost` set,
    needing a view fold).  D41 RULED (a) [OWN.16].  RESOLVED: body verbatim, docstring says (a).
R8. `emZifencei`'s "slot n := #row items among em.emItems.take n" MIS-NUMBERS after an exclusive
    pair: `hemit`'s `HEpair` emits TWO row items `(l1, some k)`, `(l2, some k)` for one slot
    (`WeakRvwmoConf.lean:703-714`).  RESOLVED: `GraphFetchSpike.emSlot` = the slot tag of the
    first row item at or after `n` — `hemit`'s "admin block before row slot k" (`eadm ls ++ (l,
    some k) :: …`; a fetch is never in the intra-pair star, `lbAdmin false (LIFetch ..)` is
    `False`); it equals the count when no pair precedes; `GraphFetchSpike.emSlotAdm` proves it is
    `k` throughout slot `k`'s admin block; past the last row item it is past-the-end (no `gnxw`).
    The literal count is NOT faithful after a pair: it is WEAKER ((Z2) against a later own write,
    allowing a source the hart's next store must follow, against (H3)) and STRONGER (fence.i
    sites po-AFTER the fetch would count as contributors).
R9. `fetchPinCutOk`: "tag 0, image bytes and no write to the bytes" ↦ `fetchPin img (LIFetch base
    tvs)` and `¬ writesIn log (base + j) 0 |log|` per fetched byte; the cut needs `itv ≤ cut`
    (`q := itv`).
R10. Binder types the report's Lean leaves implicit are filled in (`emZifencei`'s `G : Gexec`,
    `i : Nat`; `∀ (j t : Nat) (v : BitVec 8)`, (Z3)'s `∀ (l tl : Nat) (vl : BitVec 8)
    (wl : Geid)`); `base + j` is `base + (j : Int)` (`ifetchOk`'s and
    `accAddr`'s addressing).

**Deviations.**  None from the report's Lean except R7 (docstring only) and R8 (the slot
function).  Lean-only helpers are file-qualified (`GraphFetchSpike.*`).  RENAME (W13 (I), review
R32 [R32.3]): the report's `emZifencei` is `GraphFetchSpike.emZifencei` here -- the unqualified
`Weak.emZifencei` is the fetch-clause SLOT of the fabric bundle `gfexecConfIO`
(`WeakRvwmoFab.lean`, content `emFetchImg` until W5d-G G1 fills it with this definition's).

**Out of scope (G1–G7, after W13 (M) [OWN.24]).**  `emFenceI`/`emFenceISound`, `xv6ConfS`'s use
of `GraphFetchSpike.emZifencei` as the content of the `emZifencei` slot (W13 (I)),
`Gdexec.gdFetch`, the gwlog/gwix bridge, retime, hull closure (the report's risk R1),
`linPrefixLog`, the floor bound.

**W5d-G G1 edits (2026-10-13; plan rev 45 §C W5d-G, the six G0 carry-overs).**  (Z2) of `gzFetch`
is STRENGTHENED to R1 (a)'s E1′ (carry-over 4; see `gzFetch`); `gzContrib`'s fence.i sites are a
`Prop` predicate (the emission's `GraphFetch.emFenceI`); docstrings per carry-overs 3, 5, 6.
`emFenceI`/`emFenceISound`, `emSlotShift` (carry-over 2) and the kernel-text instance of
`gzFetch` are in `Weak/GraphFetch.lean`; the `emZifencei` slot content and the Zifencei bundle
`gfexecConfZ` in `Weak/WeakRvwmoFab.lean`.
-/
import Weak.WeakRvwmoConf
import Weak.WeakRvwmoLin

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! # 1. The realizing log -/

/-- The graph's write log in gmo order (what `linCand` realizes). -/
def gwlog (G : Gexec) : List Wmsg := (gwrites G).filterMap (WeakRvwmoLin.gmsg G)

/-- Below the hart's next own write at/after slot `k` (`linCand` puts `(i, k)` in that write's
segment, so the log there is `(gwlog G).take (gfcut G i k)`); every write past the hart's last. -/
def gfcut (G : Gexec) (i k : Nat) : Nat :=
  match gnxw G (i, k) with
  | some w => gwix G w - 1
  | none => (gwrites G).length

/-! # 2. The cut form -/

/-- THE CUT FORM: ONE view `q`, `itv ≤ q ≤ cut`, at which every fetched byte is admissible, and
every byte's source is at or below `q` ([W2s](i)).  `cut := log.length` is W5d's M2 fetch clause;
`gzFetchCut` is the graph instance.  (R1) -/
def fetchCutOk (img : Image) (log : List Wmsg) (cut itv : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) : Prop :=
  ∃ q, itv ≤ q ∧ q ≤ cut ∧ ifetchOk img log q base tvs ∧ ∀ t ∈ tvs.map Prod.fst, t ≤ q

theorem GraphFetchSpike.mapFstOfLookup (tvs : List (Nat × BitVec 8)) (j t : Nat) (v : BitVec 8) :
    tvs[j]? = some (t, v) → t ∈ tvs.map Prod.fst :=
  fun hj => List.mem_map.2 ⟨(t, v), List.mem_iff_getElem?.2 ⟨j, hj⟩, rfl⟩

/-- Forgetting the [W2s] per-byte bound gives the report's literal §3.4 form.  (R1) -/
theorem GraphFetchSpike.fetchCutOkLit (img : Image) (log : List Wmsg) (cut itv : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) :
    fetchCutOk img log cut itv base tvs → ∃ q, itv ≤ q ∧ q ≤ cut ∧ ifetchOk img log q base tvs :=
  fun ⟨q, h1, h2, h3, _⟩ => ⟨q, h1, h2, h3⟩

/-- A byte admissible at view `q` with its source at or below the cut stays admissible on the
prefix up to the cut. -/
theorem GraphFetchSpike.ifetchByteOkTake (img : Image) (log : List Wmsg) (c q : Nat) (a : Int)
    (t : Nat) (v : BitVec 8) :
    t ≤ c → ifetchByteOk img log q a t v → ifetchByteOk img (log.take c) q a t v := by
  intro htc h
  have htl := ifetchByteOkBounded img log q a t v h
  obtain ⟨hv, hn⟩ := h
  have htk : t ≤ (log.take c).length := by simp only [List.length_take]; omega
  refine ⟨?_, fun hw => hn ?_⟩
  · rw [← logByteApp img (log.take c) (log.drop c) t a htk, List.take_append_drop]
    exact hv
  · have h' := writesInApp (log.take c) (log.drop c) a t _ hw
    rwa [List.take_append_drop] at h'

/-- THE CUT FORM IS THE pf/W5d CHECK AT THE REALIZING PREFIX, with ONE view: the cut form on the
full log, bounded by `cut`, at `itv0` gives the M2 cut form on `log.take cut` at any `itv ≤ itv0`
(the floor bound), and the per-byte check `ifetchOk … itv` there.  (R3) -/
theorem fetchCutPrefix (img : Image) (log : List Wmsg) (cut itv0 itv : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) :
    cut ≤ log.length → itv ≤ itv0 → fetchCutOk img log cut itv0 base tvs →
    fetchCutOk img (log.take cut) (log.take cut).length itv base tvs ∧
      ifetchOk img (log.take cut) itv base tvs := by
  rintro hcut hitv ⟨q, h1, h2, hok, hts⟩
  have hok' : ifetchOk img (log.take cut) q base tvs := fun j t v hj =>
    GraphFetchSpike.ifetchByteOkTake img log cut q _ t v
      (Nat.le_trans (hts t (GraphFetchSpike.mapFstOfLookup tvs j t v hj)) h2) (hok j t v hj)
  have hlen : (log.take cut).length = cut := by simp only [List.length_take]; omega
  exact ⟨⟨q, by omega, by omega, hok', hts⟩, ifetchOkAnti img _ q itv base tvs (by omega) hok'⟩

/-- THE CUT FORM GIVES THE EDGES (index form): every byte's source is at or below the cut (E1),
and every write to a fetched byte co-after its source is above the i-view (E2, the i-view standing
for the contributors) and above every byte's source (E3).  (R4) -/
theorem fetchCutEdge (img : Image) (log : List Wmsg) (cut itv : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) :
    fetchCutOk img log cut itv base tvs →
    ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) →
      t ≤ cut ∧
      ∀ t', t < t' → (logByte img log t' (base + (j : Int))).isSome →
        itv < t' ∧ ∀ (l tl : Nat) (vl : BitVec 8), tvs[l]? = some (tl, vl) → tl < t' := by
  rintro ⟨q, h1, h2, hok, hts⟩ j t v hj
  have htq := hts t (GraphFetchSpike.mapFstOfLookup tvs j t v hj)
  refine ⟨by omega, fun t' htt' hw => ?_⟩
  have hqt' : q < t' := by
    refine Nat.lt_of_not_le (fun hle => (hok j t v hj).2 ?_)
    rw [Nat.max_eq_right htq]
    exact (writesInLogByte img log _ t q).2 ⟨t', htt', hle, hw⟩
  exact ⟨by omega, fun l tl vl hl =>
    Nat.lt_of_le_of_lt (hts tl (GraphFetchSpike.mapFstOfLookup tvs l tl vl hl)) hqt'⟩

/-! # 3. The relational form -/

/-- THE RELATIONAL FORM: `gzFetch` over write INDICES (the graph-to-index transport is G4's):
(Z1) value; (Z2) source at or below the cut; (Z3) every write to the byte co-after its source is
above every contributor index and every byte's source; contributors at or below the cut.  (R5) -/
def fetchRelOk (img : Image) (log : List Wmsg) (cut : Nat) (cs : List Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) : Prop :=
  (∀ c ∈ cs, c ≤ cut) ∧
  ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) →
    logByte img log t (base + (j : Int)) = some v ∧
    t ≤ cut ∧
    ∀ t', t < t' → (logByte img log t' (base + (j : Int))).isSome →
      (∀ c ∈ cs, c < t') ∧ ∀ (l tl : Nat) (vl : BitVec 8), tvs[l]? = some (tl, vl) → tl < t'

theorem GraphFetchSpike.leFoldrMax (l : List Nat) (x : Nat) : x ∈ l → x ≤ l.foldr max 0 := by
  induction l with
  | nil => intro h; cases h
  | cons y l ih =>
    intro h
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem GraphFetchSpike.foldrMaxLe (l : List Nat) (b : Nat) :
    (∀ x ∈ l, x ≤ b) → l.foldr max 0 ≤ b := by
  induction l with
  | nil => intro _; exact Nat.zero_le _
  | cons y l ih =>
    intro h
    simp only [List.foldr_cons]
    exact Nat.max_le.2 ⟨h y (List.mem_cons.2 (Or.inl rfl)),
      ih (fun x hx => h x (List.mem_cons.2 (Or.inr hx)))⟩

/-- THE RELATIONAL FORM GIVES THE CUT at `itv := lmax cs`, with
`q := max (lmax cs) (lmax sources)`.  At `(gwlog G, gfcut G i k)` the conclusion is
`gzFetchCut G i k (cs.foldr max 0) base tvs`.  (R5, R6) -/
theorem fetchRelCut (img : Image) (log : List Wmsg) (cut : Nat) (cs : List Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) :
    fetchRelOk img log cut cs base tvs → fetchCutOk img log cut (cs.foldr max 0) base tvs := by
  rintro ⟨hcs, hb⟩
  refine ⟨max (cs.foldr max 0) ((tvs.map Prod.fst).foldr max 0), Nat.le_max_left _ _, ?_, ?_, ?_⟩
  · refine Nat.max_le.2 ⟨GraphFetchSpike.foldrMaxLe cs cut hcs, GraphFetchSpike.foldrMaxLe _ cut ?_⟩
    intro t ht
    obtain ⟨⟨t0, v⟩, hmem, rfl⟩ := List.mem_map.1 ht
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hmem
    exact (hb j t0 v hj).2.1
  · intro j t v hj
    obtain ⟨hv, -, hz3⟩ := hb j t v hj
    have htq : t ≤ (tvs.map Prod.fst).foldr max 0 :=
      GraphFetchSpike.leFoldrMax _ t (GraphFetchSpike.mapFstOfLookup tvs j t v hj)
    refine ⟨hv, fun hw => ?_⟩
    obtain ⟨t', h1, h2, h3⟩ := (writesInLogByte img log _ t _).1 hw
    obtain ⟨hc, hl⟩ := hz3 t' h1 h3
    have hc' : cs.foldr max 0 ≤ t' - 1 :=
      GraphFetchSpike.foldrMaxLe cs _ (fun c hcm => by have := hc c hcm; omega)
    have hl' : (tvs.map Prod.fst).foldr max 0 ≤ t' - 1 := by
      apply GraphFetchSpike.foldrMaxLe
      intro x hx
      obtain ⟨⟨t0, v0⟩, hmem, rfl⟩ := List.mem_map.1 hx
      obtain ⟨l, hl0⟩ := List.mem_iff_getElem?.1 hmem
      have := hl l t0 v0 hl0
      show t0 ≤ t' - 1
      omega
    omega
  · intro t ht
    exact Nat.le_trans (GraphFetchSpike.leFoldrMax _ t ht) (Nat.le_max_right _ _)

/-- The relational form is exact: the cut form gives it back with the i-view as the only
contributor.  (R4) -/
theorem GraphFetchSpike.fetchCutRel (img : Image) (log : List Wmsg) (cut itv : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) :
    fetchCutOk img log cut itv base tvs → fetchRelOk img log cut [itv] base tvs := by
  intro h
  have hedge := fetchCutEdge img log cut itv base tvs h
  obtain ⟨q, h1, h2, hok, _⟩ := h
  refine ⟨fun c hc => ?_, fun j t v hj => ?_⟩
  · rw [List.mem_singleton] at hc
    omega
  · obtain ⟨htc, he⟩ := hedge j t v hj
    refine ⟨(hok j t v hj).1, htc, fun t' h1' h2' => ?_⟩
    obtain ⟨hi, hl⟩ := he t' h1' h2'
    exact ⟨fun c hc => by rw [List.mem_singleton] at hc; omega, hl⟩

/-- THE GRAPH CUT FORM: one view `q` with `itv ≤ q <` next-own-write (`q ≤ gfcut = gwix nxw -
1`) over the graph's write log.  (R6; G0 review item 5) -/
def gzFetchCut (G : Gexec) (i k itv : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) : Prop :=
  fetchCutOk G.gxImg (gwlog G) (gfcut G i k) itv base tvs

/-! # 4. The trusted-base item -/

/-- fence.i contributors at slot k (Q-G2 (a), the superset; D41 RULED (a) [OWN.16]; R7): own
writes po-before a fence.i site before the slot, and rf-sources of the hart's reads po-before
it.  (W5d-G G1: the fence.i sites `fi` are a predicate on row slots -- the emission's
`GraphFetch.emFenceI em`, D40 [OWN.15].) -/
def gzContrib (G : Gexec) (fi : Nat → Prop) (i k : Nat) (c : Geid) : Prop :=
  ∃ f, f < k ∧ fi f ∧
    ((c.1 = i ∧ c.2 < f ∧ gisW G c = true) ∨
     (∃ r a t v, r.1 = i ∧ r.2 < f ∧ greadsByte G r a t v ∧ gwriteAt G t = some c))

/-- THE TRUSTED-BASE ITEM, one fetch item (hart i, row slot k).

W5d-G G1 (G0 review item 4; plan §B(4)(iii) R1 (a), E1′): (Z2) is stated in the E1′ form --
the source is gmo-before EVERY memory event of hart `i` at or after slot `k` -- not the report's
"gmo-before the next own write `gnxw`".  The report's form is WEAKER than its own reading (H3):
a later own store to another address may be gmo-before `gnxw`, so it admitted a fetch reading
the hart's own LATER store.  E1′ reads (H3′): an instruction's memory accesses are performed
after the fetches of it and of every po-earlier instruction (in-order fetch), and a fetch after
its source -- STRONGER than the spec (RVWMO has no fetch model; Zifencei is silent on the
order of a fetch against later accesses), gmo-TRUE on in-order-fetch hardware; listed in plan
§B(11).  It implies (H3) (every own write at/after `k` is gmo-after the source) and the report's
(Z2) (`gnxw` is such a write), and it makes "kept fetch ⇒ source kept" follow from
racyD-closure of the hull (risk R1 (a)).  (Z3)'s "one fill instant per label": Sail's `fetch`
(`LeanRV64D/Fetch.lean:253-288`) does ONE 4-byte read at a 4-aligned pc under `Ext_Ziccif`
(`PlatformConfig.lean:2157`) -- it FOLLOWS from Sail + Ziccif; only (H1)'s no-forwarding half
is a stronger hardware reading (G0 review item 6). -/
def gzFetch (G : Gexec) (C : Geid → Prop) (i k : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) : Prop :=
  ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) →
    -- (Z1) value
    logByte G.gxImg (gwlog G) t (base + (j : Int)) = some v ∧
    -- (Z2) not from the future -- E1′: before every own memory event at/after the slot
    (∀ w k', gwriteAt G t = some w → k ≤ k' → gmem G (i, k') → gmoLt G w (i, k')) ∧
    -- (Z3) fresh past fence.i, one cut per label
    (∀ w' v', gwritesByte G w' (base + (j : Int)) v' → t < gwix G w' →
       (∀ c, C c → gmoLt G c w') ∧
       (∀ (l tl : Nat) (vl : BitVec 8) (wl : Geid), tvs[l]? = some (tl, vl) →
         gwriteAt G tl = some wl → gmoLt G wl w'))

/-- The row slot of emission item `n`: the slot tag of the first row item at or after `n`;
past-the-end after the last row item.  (R8)  The past-the-end default is the number of ROW
ITEMS, which double-counts exclusive pairs (two row items per slot); it is UNREACHABLE for a
`hemit` emission -- `hemit` ends with a row item (`HEnil` emits nothing), so every admin item,
fetches included, has a row item after it (G0 review item 3). -/
def GraphFetchSpike.emSlot (its : List Eitem) (n : Nat) : Nat :=
  (((its.drop n).filterMap Prod.snd).head?).getD (its.filterMap Prod.snd).length

/-- Every item of slot `k`'s admin block, and the row item itself, sits at slot `k`.  (R8) -/
theorem GraphFetchSpike.emSlotAdm (ls : List Wlabel) (l : Wlabel) (k : Nat) (es : List Eitem)
    (n : Nat) : n ≤ ls.length → GraphFetchSpike.emSlot (eadm ls ++ (l, some k) :: es) n = k := by
  intro hn
  have hlen : (eadm ls).length = ls.length := by simp only [eadm, List.length_map]
  have hnil : ((eadm ls).drop n).filterMap Prod.snd = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro a ha
    obtain ⟨l', -, rfl⟩ := List.mem_map.1 (List.mem_of_mem_drop ha)
    rfl
  unfold GraphFetchSpike.emSlot
  rw [List.drop_append_of_le_length (by omega), List.filterMap_append, hnil]
  rfl

/-- `xv6ConfS`'s fetch clause: every administrative fetch item satisfies `gzFetch` at its row
slot. -/
def GraphFetchSpike.emZifencei (G : Gexec) (C : Nat → Geid → Prop) (i : Nat) (em : Hemission) :
    Prop :=
  ∀ (n : Nat) (base : Int) (tvs : List (Nat × BitVec 8)),
    em.emItems[n]? = some (Wlabel.LIFetch base tvs, none) →
    gzFetch G (C (GraphFetchSpike.emSlot em.emItems n)) i (GraphFetchSpike.emSlot em.emItems n)
      base tvs

/-! # 5. The kernel-text instance -/

/-- A pinned fetch (tag 0, image bytes) of bytes the log never writes satisfies the cut form at
any `itv ≤ cut` (`q := itv`).  (R9) -/
theorem fetchPinCutOk (img : Image) (log : List Wmsg) (cut itv : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) :
    WeakAxRealize.fetchPin img (Wlabel.LIFetch base tvs) →
    (∀ j, j < tvs.length → ¬ writesIn log (base + (j : Int)) 0 log.length) →
    itv ≤ cut →
    fetchCutOk img log cut itv base tvs := by
  rintro ⟨h0, himg⟩ hnw hitv
  refine ⟨itv, Nat.le_refl _, hitv, fun j t v hj => ?_, fun t ht => by
    rw [h0 t ht]; exact Nat.zero_le _⟩
  have hlt : j < tvs.length := lookup_lt_Some hj
  have ht : t = 0 := h0 t (GraphFetchSpike.mapFstOfLookup tvs j t v hj)
  subst ht
  refine ifetchByteOkImg img log itv _ v ?_ (hnw j hlt)
  rw [himg j hlt, List.getElem?_map, hj]
  rfl

end Weak

