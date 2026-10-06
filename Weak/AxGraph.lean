/-
Weak: **`gob`, coherence, and the OWNED-READ lemma** (AxSL tier, track B).

Rocq: `iris/AxGraph.v` @ xxvzwolszwmp.

The Rocq header, in substance (design: `claude-notes/design/weak-memory-lb-axsl.md`
§1, layers L0/L1/L2).  PURE (no Iris): the graph lemmas the base logic consumes,
stated over `WeakRvwmoGraph`'s presentation (`Gexec`/`Gdexec`, `gmoLt`,
`WeakRvwmoGraph.gpo`, `gwritesByte`, `greadsByte`, `gvisible`, `gloadValue`) and
REUSING `WeakRvwmoAcyc`'s `grf`/`gco`/`gfr` and `WeakRvwmoLock`'s byte
bookkeeping.

  §1  decidability of `gpo`/`gmoLt`/`gvisible` and the generic `lastSuch` kit;
  §2  `grfAt` (`grf` with the BYTE pinned), byte-level determinism, the external
      variants `grfe`/`gcoe`/`gfre`, and `gob` (the transitive closure of
      ppo⁻ ∪ deps ∪ rfe ∪ co ∪ fr);
  §3  `obSubGmo` / `obIrreflexive` — L0's ordering theorem;
  §4  THE OWNED-READ LEMMA `ownedRead`: an ob-chained history of same-byte writes
      that COVERS every visible write determines the read's rf-source as the last
      visible entry of the history (generic forms `ownedReadWith` & co., over
      any relation `R ⊆ gmoLt`, for `AxGraphCat.gob_cat`);
  §5  `visibleCases` and the FORWARDING characterization (`ownForwardWeak`, the
      commissioned weak form with both extra hypotheses dropped; `ownForward`,
      the true flat form under full `rvwmoMinusConsistent`);
  §6  sanity on the LB witness `lbgd`.

The Rocq header's two "corrections to the commissioned statements" stand: (1)
`ownForwardWeak` needs neither `¬ gmoLt w r` nor the no-intervening-write
hypothesis, and with them (plus `gppoGmo`) the co-later disjunct dies, giving
`ownForward`; (2) `ownedRead`'s "some entry of `Hl` is visible" hypothesis is
NOT redundant (without it the read may take the era-initial image, `t = 0`).

FETCHES (owner decision D1): this tier keeps the Rocq treatment — a fetch is a
graph `LLoad` read like any other; nothing in this file distinguishes it.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  The duplicated
   Rocq names (`notes/weak-port-dupnames.json`) `gpo_dec`, `gmo_lt_dec` are
   FILE-QUALIFIED (`AxGraph.gpoDec`, `AxGraph.gmoLtDec`); the dependencies'
   duplicates are referred to qualified (`WeakRvwmoGraph.gpo`,
   `WeakRvwmoGraph.gwixPos`, `WeakRvwmoAcyc.grf`).
2. VOCABULARY: as `WeakRvwmoGraph` deviation 2 (`l !! i` ↦ `l[i]?`, `S n` ↦
   `n + 1`, `is_Some o` ↦ `o.isSome = true`, `Z` ↦ `Int`, `bv 8` ↦
   `BitVec 8`, `relation geid` ↦ `Geid → Geid → Prop`); `Decision P` ↦
   `Decidable P` (`lastSuch`'s decision procedure is still an EXPLICIT
   argument, matched by `isTrue`/`isFalse`).
3. The `Local Instance`s are `local instance`s built by `unfold; infer_instance`
   (Rocq's `gpo_dec` is a hand-built decision; same proposition).
4. CLOSURE INDUCTION: `obSubGmo` inducts on the library `tc`, which splits at
   the LAST step (`MachCSL.Rel` deviation 1): the mirrored proof of the same
   statement.
5. The closed `vm_compute` side conditions (`gwriteAt lbg t`, gmo membership and
   positions) are `decide`.

**Name map** (Rocq → Lean): `gpo_dec` ↦ `AxGraph.gpoDec`; `gmo_lt_dec` ↦
`AxGraph.gmoLtDec`; `gvisible_dec` ↦ `gvisibleDec`; `last_such` ↦ `lastSuch`;
`last_such_None` ↦ `lastSuchNone`; `last_such_spec` ↦ `lastSuchSpec`;
`last_such_is_Some` ↦ `lastSuchIsSome`; `last_such_snoc` ↦ `lastSuchSnoc`;
`last_visible` ↦ `lastVisible`; `grf_at` ↦ `grfAt`; `grf_at_grf` ↦ `grfAtGrf`;
`greads_byte_det` ↦ `greadsByteDet`; `grf_at_det` ↦ `grfAtDet`; `grfe`;
`gcoe`; `gfre`; `gdeps_rel` ↦ `gdepsRel`; `gobr`; `gob`; `gob_step` ↦
`gobStep`; `gob_trans` ↦ `gobTrans`; `grfe_gmo` ↦ `grfeGmo`; `gobr_gmo` ↦
`gobrGmo`; `ob_sub_gmo` ↦ `obSubGmo`; `ob_irreflexive` ↦ `obIrreflexive`;
`ob_asym` ↦ `obAsym`; `grf_at_comax` ↦ `grfAtComax`; `grf_at_exists` ↦
`grfAtExists`; `grf_at_value` ↦ `grfAtValue`; `chain_with` ↦ `chainWith`;
`chain_with_gmo` ↦ `chainWithGmo`; `ob_chain` ↦ `obChain`; `ob_chain_gob` ↦
`obChainGob`; `ob_chain_gmo` ↦ `obChainGmo`; `owned_read_with` ↦
`ownedReadWith`; `owned_read_snoc_with` ↦ `ownedReadSnocWith`;
`owned_read_value_with` ↦ `ownedReadValueWith`; `owned_read` ↦ `ownedRead`;
`owned_read_snoc` ↦ `ownedReadSnoc`; `owned_read_value` ↦ `ownedReadValue`;
`visible_cases` ↦ `visibleCases`; `own_forward_weak` ↦ `ownForwardWeak`;
`own_forward` ↦ `ownForward`; `lb_ob_irreflexive` ↦ `lbObIrreflexive`;
`lb_ob_acyclic` ↦ `lbObAcyclic`; `lb_rf_10` ↦ `lbRf10`; `lb_rf_01` ↦
`lbRf01`; `lb_both_loads_read_the_other_hart` ↦
`lbBothLoadsReadTheOtherHart`; `lb_ob_rfe` ↦ `lbObRfe`; `lbg_wb_01` ↦
`lbgWb01`; `lbg_vis_01_10` ↦ `lbgVis0110`; `lb_owned_read` ↦ `lbOwnedRead`.

**Not ported:** nothing (the §7 `Print Assumptions` block has no Lean twin; the
lint's axiom check covers it).
-/
import Weak.WeakRvwmoAcyc
import Weak.WeakRvwmoLock

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl

/-! # 1. Decidability, and the generic "last element satisfying P" kit -/

local instance AxGraph.gpoDec (G : Gexec) (e1 e2 : Geid) :
    Decidable (WeakRvwmoGraph.gpo G e1 e2) := by
  unfold WeakRvwmoGraph.gpo; infer_instance

local instance AxGraph.gmoLtDec (G : Gexec) (e1 e2 : Geid) : Decidable (gmoLt G e1 e2) := by
  unfold gmoLt; infer_instance

local instance gvisibleDec (G : Gexec) (w r : Geid) : Decidable (gvisible G w r) := by
  unfold gvisible; infer_instance

/-- The LAST element of a list satisfying `P`.  The decision procedure is an
EXPLICIT argument: no typeclass inference inside the fixpoint. -/
def lastSuch {A : Type _} (P : A → Prop) (dec : ∀ x, Decidable (P x)) :
    List A → Option A
  | [] => none
  | x :: l' =>
    match lastSuch P dec l' with
    | some y => some y
    | none =>
      match dec x with
      | isTrue _ => some x
      | isFalse _ => none

theorem lastSuchNone {A : Type _} (P : A → Prop) (dec : ∀ x, Decidable (P x)) (l : List A) :
    lastSuch P dec l = none → ∀ (k : Nat) y, l[k]? = some y → ¬ P y := by
  induction l with
  | nil => intro _ k y hk; simp at hk
  | cons z l ih =>
    intro hn k y hk
    cases hls : lastSuch P dec l with
    | some u => simp only [lastSuch, hls] at hn; cases hn
    | none =>
      simp only [lastSuch, hls] at hn
      generalize dec z = d at hn
      cases d with
      | isTrue _ => cases hn
      | isFalse hz =>
        cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
          subst hk
          exact hz
        | succ k =>
          exact ih hls k y (by simpa using hk)

/-- THE SPEC: the returned element sits in the list, satisfies `P`, and no LATER
position of the list satisfies `P`. -/
theorem lastSuchSpec {A : Type _} (P : A → Prop) (dec : ∀ x, Decidable (P x)) (l : List A)
    (x : A) :
    lastSuch P dec l = some x →
    ∃ m : Nat, l[m]? = some x ∧ P x ∧ (∀ (k : Nat) y, l[k]? = some y → P y → k ≤ m) := by
  induction l with
  | nil => intro h; simp [lastSuch] at h
  | cons z l ih =>
    intro h
    cases hls : lastSuch P dec l with
    | some u =>
      simp only [lastSuch, hls, Option.some.injEq] at h
      subst h
      obtain ⟨m, hm, hP, hmax⟩ := ih hls
      refine ⟨m + 1, by simpa using hm, hP, ?_⟩
      intro k y hk hPy
      cases k with
      | zero => omega
      | succ k =>
        have := hmax k y (by simpa using hk) hPy
        omega
    | none =>
      simp only [lastSuch, hls] at h
      generalize dec z = d at h
      cases d with
      | isFalse _ => cases h
      | isTrue hz =>
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨0, rfl, hz, ?_⟩
        intro k y hk hPy
        cases k with
        | zero => omega
        | succ k =>
          exact absurd hPy (lastSuchNone P dec l hls k y (by simpa using hk))

theorem lastSuchIsSome {A : Type _} (P : A → Prop) (dec : ∀ x, Decidable (P x)) (l : List A)
    (k : Nat) (y : A) :
    l[k]? = some y → P y → (lastSuch P dec l).isSome = true := by
  intro hk hy
  cases hls : lastSuch P dec l with
  | some u => rfl
  | none => exact absurd hy (lastSuchNone P dec l hls k y hk)

/-- ... and when the list's LAST element itself satisfies `P`, the answer is that
element — the "`last H`" form the corollaries use. -/
theorem lastSuchSnoc {A : Type _} (P : A → Prop) (dec : ∀ x, Decidable (P x)) (l : List A)
    (x : A) :
    P x → lastSuch P dec (l ++ [x]) = some x := by
  intro hx
  induction l with
  | nil =>
    simp only [List.nil_append, lastSuch]
    generalize dec x = d
    cases d with
    | isTrue _ => rfl
    | isFalse hn => exact absurd hx hn
  | cons z l ih =>
    simp only [List.cons_append, lastSuch, ih]

/-- The graph instance. -/
def lastVisible (G : Gexec) (Hl : List Geid) (r : Geid) : Option Geid :=
  lastSuch (fun w => gvisible G w r) (fun w => gvisibleDec G w r) Hl

/-! # 2. The relations: `grfAt`, the external variants, and `gob` -/

/-- `grf` WITH THE BYTE PINNED; `WeakRvwmoAcyc.grf G w r` is `∃ a, grfAt G a w r`. -/
def grfAt (G : Gexec) (a : Int) (w r : Geid) : Prop :=
  ∃ t v, greadsByte G r a t v ∧ gwriteAt G t = some w

theorem grfAtGrf (G : Gexec) (a : Int) (w r : Geid) : grfAt G a w r → WeakRvwmoAcyc.grf G w r := by
  rintro ⟨t, v, hrd, hat⟩
  exact ⟨a, t, v, hrd, hat⟩

/-- A read event reads ONE value at ONE timestamp per byte (`accAddr` is
injective in the byte index). -/
theorem greadsByteDet (G : Gexec) (r : Geid) (a : Int) (t1 : Nat) (v1 : BitVec 8) (t2 : Nat)
    (v2 : BitVec 8) :
    greadsByte G r a t1 v1 → greadsByte G r a t2 v2 → t1 = t2 ∧ v1 = v2 := by
  rintro ⟨l1, bs1, ts1, vs1, j1, hl1, hrd1, ht1, hv1, ha1⟩
    ⟨l2, bs2, ts2, vs2, j2, hl2, hrd2, ht2, hv2, ha2⟩
  rw [hl1, Option.some.injEq] at hl2
  subst hl2
  rw [hrd1, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hrd2
  obtain ⟨rfl, rfl, rfl⟩ := hrd2
  have : j1 = j2 := accAddrInj bs1 j1 j2 (by rw [ha1, ha2])
  subst this
  rw [ht1, Option.some.injEq] at ht2
  rw [hv1, Option.some.injEq] at hv2
  exact ⟨ht2, hv2⟩

/-- ... hence the rf-source at a byte is UNIQUE. -/
theorem grfAtDet (G : Gexec) (a : Int) (w1 w2 r : Geid) :
    grfAt G a w1 r → grfAt G a w2 r → w1 = w2 := by
  rintro ⟨t1, v1, hr1, ha1⟩ ⟨t2, v2, hr2, ha2⟩
  obtain ⟨ht, _⟩ := greadsByteDet G r a t1 v1 t2 v2 hr1 hr2
  subst ht
  rw [ha1, Option.some.injEq] at ha2
  exact ha2

/-- THE EXTERNAL VARIANTS (different harts). -/
def grfe (G : Gexec) (w r : Geid) : Prop := WeakRvwmoAcyc.grf G w r ∧ w.1 ≠ r.1
def gcoe (G : Gexec) (w w' : Geid) : Prop := gco G w w' ∧ w.1 ≠ w'.1
def gfre (G : Gexec) (r w' : Geid) : Prop := gfr G r w' ∧ r.1 ≠ w'.1

/-- The dependency fragment (`gdDeps`), as a relation. -/
def gdepsRel (GD : Gdexec) (x y : Geid) : Prop := (x, y) ∈ GD.gdDeps

/-- ONE ob STEP; `gob` is its transitive closure. -/
def gobr (GD : Gdexec) (x y : Geid) : Prop :=
  gppo GD.gdG x y ∨ gdepsRel GD x y ∨ grfe GD.gdG x y ∨ gco GD.gdG x y ∨ gfr GD.gdG x y

def gob (GD : Gdexec) (x y : Geid) : Prop := tc (gobr GD) x y

theorem gobStep (GD : Gdexec) (x y : Geid) : gobr GD x y → gob GD x y := tc_once

theorem gobTrans (GD : Gdexec) (x y z : Geid) : gob GD x y → gob GD y z → gob GD x z :=
  tc_transitive

/-! # 3. `gob ⊆ gmo` -/

/-- rfe ⊆ gmo.  `gvisible`'s forwarding disjunct is `gpo`, which pins the agent —
so for a CROSS-HART pair only the `gmoLt` disjunct survives. -/
theorem grfeGmo (G : Gexec) (w r : Geid) : gloadValue G → grfe G w r → gmoLt G w r := by
  rintro hlv ⟨⟨a, t, v, hrd, hat⟩, hne⟩
  cases t with
  | zero => simp [gwriteAt] at hat
  | succ i =>
    have h1 := (hlv r a (i + 1) v hrd).1
    obtain ⟨w0, hat0, _, hvis⟩ := h1
    have hw0 : w0 = w := by
      rw [hat0] at hat
      exact Option.some.inj hat
    subst hw0
    rcases hvis with hmo | ⟨hag, _⟩
    · exact hmo
    · exact absurd hag hne

theorem gobrGmo (GD : Gdexec) (x y : Geid) :
    rvwmoMinusDepsConsistent GD → gobr GD x y → gmoLt GD.gdG x y := by
  rintro ⟨hc, _, hdg⟩ hr
  have ⟨hwf, hppo, hlv, _⟩ := hc
  rcases hr with h | h | h | h | h
  · exact hppo _ _ h
  · exact hdg (x, y) h
  · exact grfeGmo _ _ _ hlv h
  · exact gcoGmo _ _ _ hwf h
  · exact gfrGmo _ _ _ hc h

/-- THE ORDERING THEOREM: every ob edge is gmo-forward. -/
theorem obSubGmo (GD : Gdexec) (x y : Geid) :
    rvwmoMinusDepsConsistent GD → gob GD x y → gmoLt GD.gdG x y := by
  intro hcons h
  induction h with
  | single h => exact gobrGmo GD _ _ hcons h
  | tail _ h ih => exact gmoLtTrans _ _ _ _ ih (gobrGmo GD _ _ hcons h)

theorem obIrreflexive (GD : Gdexec) (x : Geid) :
    rvwmoMinusDepsConsistent GD → ¬ gob GD x x :=
  fun hcons hob => gmoLtIrrefl _ _ (obSubGmo GD x x hcons hob)

theorem obAsym (GD : Gdexec) (x y : Geid) :
    rvwmoMinusDepsConsistent GD → gob GD x y → ¬ gob GD y x :=
  fun hcons hxy hyx => obIrreflexive GD x hcons (gobTrans GD x y x hxy hyx)

/-! # 4. Coherence at a byte, and THE OWNED-READ LEMMA -/

/-- CO-MAXIMALITY: the rf-source of `r` at `a` carries the largest write index
among the same-byte writes visible to `r`. -/
theorem grfAtComax (G : Gexec) (a : Int) (w r w' : Geid) (v' : BitVec 8) :
    gwf G → gloadValue G → grfAt G a w r →
    gwritesByte G w' a v' → gvisible G w' r →
    gwix G w' ≤ gwix G w := by
  rintro hwf hlv ⟨t, v, hrd, hat⟩ hwb hvis
  have hmax := (hlv r a t v hrd).2
  rw [(gwriteAtInv G t w hwf.1 hat).2]
  exact hmax w' v' hwb hvis

/-- EXISTENCE: a read of a byte that HAS a visible same-byte write cannot be
taking the era-initial image, so its rf-source exists. -/
theorem grfAtExists (G : Gexec) (r : Geid) (a : Int) (t : Nat) (v : BitVec 8) (w0 : Geid)
    (v0 : BitVec 8) :
    gwf G → gloadValue G → greadsByte G r a t v →
    gwritesByte G w0 a v0 → gvisible G w0 r →
    ∃ w, grfAt G a w r ∧ gwritesByte G w a v ∧ gvisible G w r := by
  intro hwf hlv hrd hwb hvis
  obtain ⟨hsrc, hmax⟩ := hlv r a t v hrd
  cases t with
  | zero =>
    exfalso
    have h1 := hmax w0 v0 hwb hvis
    have h2 := WeakRvwmoGraph.gwixPos G w0 (gwritesByteGwrites G w0 a v0 hwf hwb)
    omega
  | succ i =>
    obtain ⟨w, hat, hwb', hvis'⟩ := hsrc
    exact ⟨w, ⟨i + 1, v, hrd, hat⟩, hwb', hvis'⟩

/-- The source's value IS the value read, at that byte. -/
theorem grfAtValue (G : Gexec) (a : Int) (w r : Geid) (t : Nat) (v v' : BitVec 8) :
    gloadValue G → grfAt G a w r → greadsByte G r a t v →
    gwritesByte G w a v' → v = v' := by
  rintro hlv ⟨t0, v0, hrd0, hat⟩ hrd hwb
  obtain ⟨ht, hv⟩ := greadsByteDet G r a t0 v0 t v hrd0 hrd
  subst ht hv
  exact gwritesByteDet G w a v0 v' (greadSourceByte G r a t0 v0 w hlv hrd0 hat) hwb

/-! ## 4.1 Chained histories, GENERIC in the ordering relation -/

/-- `Hl` is `R`-chained when consecutive entries are `R`-related. -/
def chainWith (R : Geid → Geid → Prop) (Hl : List Geid) : Prop :=
  ∀ i w1 w2, Hl[i]? = some w1 → Hl[i + 1]? = some w2 → R w1 w2

/-- An `R`-chained history is gmo-INCREASING whenever `R ⊆ gmoLt`. -/
theorem chainWithGmo (G : Gexec) (R : Geid → Geid → Prop) (Hl : List Geid) (i j : Nat)
    (w1 w2 : Geid) :
    (∀ x y, R x y → gmoLt G x y) → chainWith R Hl →
    Hl[i]? = some w1 → Hl[j]? = some w2 → i < j →
    gmoLt G w1 w2 := by
  intro hsub hch hi hj hlt
  induction j generalizing w2 with
  | zero => omega
  | succ j ih =>
    by_cases hij : i = j
    · subst hij
      exact hsub _ _ (hch i w1 w2 hi hj)
    · have hlen : j < Hl.length := by
        have := lookup_lt_Some hj
        omega
      obtain ⟨u, hu⟩ := someOfIsSome (lookup_lt_is_Some_2 hlen)
      exact gmoLtTrans G _ _ _ (ih u hu (by omega)) (hsub _ _ (hch j u w2 hu hj))

/-- The `gob` instance. -/
def obChain (GD : Gdexec) (Hl : List Geid) : Prop := chainWith (gob GD) Hl

theorem obChainGob (GD : Gdexec) (Hl : List Geid) (i j : Nat) (w1 w2 : Geid) :
    obChain GD Hl → Hl[i]? = some w1 → Hl[j]? = some w2 → i < j →
    gob GD w1 w2 := by
  intro hch hi hj hlt
  induction j generalizing w2 with
  | zero => omega
  | succ j ih =>
    by_cases hij : i = j
    · subst hij
      exact hch i w1 w2 hi hj
    · have hlen : j < Hl.length := by
        have := lookup_lt_Some hj
        omega
      obtain ⟨u, hu⟩ := someOfIsSome (lookup_lt_is_Some_2 hlen)
      exact gobTrans GD _ _ _ (ih u hu (by omega)) (hch j u w2 hu hj)

/-- ... so an ob-chained history is gmo-INCREASING. -/
theorem obChainGmo (GD : Gdexec) (Hl : List Geid) (i j : Nat) (w1 w2 : Geid) :
    rvwmoMinusDepsConsistent GD → obChain GD Hl →
    Hl[i]? = some w1 → Hl[j]? = some w2 → i < j →
    gmoLt GD.gdG w1 w2 :=
  fun hcons => chainWithGmo GD.gdG (gob GD) Hl i j w1 w2 (fun x y => obSubGmo GD x y hcons)

/-! ## 4.2 THE OWNED-READ LEMMA

`Hl` is a history of writes to byte `a`, `R`-chained for a gmo-forward `R`,
COVERING every same-byte write visible to `r`.  Then the rf-source of `r` at `a`
is the LAST entry of `Hl` visible to `r`.  Only `gwf` and `gloadValue` are
consumed: no ppo arm enters, so the same proof serves every ppo variant. -/

theorem ownedReadWith (G : Gexec) (R : Geid → Geid → Prop) (Hl : List Geid) (a : Int)
    (r w0 : Geid) :
    (∀ x y, R x y → gmoLt G x y) → gwf G → gloadValue G →
    -- `Hl` is a list of writes to byte `a`
    (∀ w, w ∈ Hl → ∃ v, gwritesByte G w a v) →
    -- ... `R`-chained
    chainWith R Hl →
    -- COVERAGE: every same-byte write visible to `r` is in the history
    (∀ w v, gwritesByte G w a v → gvisible G w r → w ∈ Hl) →
    -- some entry IS visible (else the read may take the era image)
    w0 ∈ Hl → gvisible G w0 r →
    -- `r` reads byte `a`
    (∃ t v, greadsByte G r a t v) →
    ∃ w, lastVisible G Hl r = some w ∧ grfAt G a w r := by
  rintro hsub hwf hlv hwrites hch hcov hw0 hvis0 ⟨t, v, hrd⟩
  obtain ⟨v0, hwb0⟩ := hwrites w0 hw0
  -- the source exists ...
  obtain ⟨ws, hrf, hwbs, hviss⟩ := grfAtExists G r a t v w0 v0 hwf hlv hrd hwb0 hvis0
  -- ... and is in the history
  obtain ⟨k, hk⟩ := elem_of_list_lookup_1 (hcov ws v hwbs hviss)
  -- ... so `lastVisible` is defined
  obtain ⟨w, hlast⟩ := someOfIsSome
    (lastSuchIsSome (fun u => gvisible G u r) (fun u => gvisibleDec G u r) Hl k ws hk hviss)
  refine ⟨w, hlast, ?_⟩
  obtain ⟨m, hm, hvisw, hmax⟩ := lastSuchSpec _ _ _ _ hlast
  -- the source occupies the last visible position
  have hkm : k = m := by
    by_cases hne : k = m
    · exact hne
    exfalso
    have hle := hmax k ws hk hviss
    have hlt : k < m := by omega
    obtain ⟨vw, hwbw⟩ := hwrites w (elem_of_list_lookup_2 hm)
    obtain ⟨_, _, hpos⟩ := chainWithGmo G R Hl k m ws w hsub hch hk hm hlt
    have hgws := gwritesByteGwrites G ws a v hwf hwbs
    have hgw := gwritesByteGwrites G w a vw hwf hwbw
    have h1 := (gwixGposLt G ws w hwf.1 hgws hgw).2 hpos
    have h2 := grfAtComax G a ws r w vw hwf hlv hrf hwbw hvisw
    omega
  subst hkm
  rw [hk, Option.some.injEq] at hm
  subst hm
  exact hrf

/-- THE CONSUMABLE FORM.  If the LAST entry is visible, the rf-source is that
entry (stated in the `Hl0 ++ [wl]` shape). -/
theorem ownedReadSnocWith (G : Gexec) (R : Geid → Geid → Prop) (Hl0 : List Geid) (wl : Geid)
    (a : Int) (r : Geid) :
    (∀ x y, R x y → gmoLt G x y) → gwf G → gloadValue G →
    (∀ w, w ∈ Hl0 ++ [wl] → ∃ v, gwritesByte G w a v) →
    chainWith R (Hl0 ++ [wl]) →
    (∀ w v, gwritesByte G w a v → gvisible G w r → w ∈ Hl0 ++ [wl]) →
    gvisible G wl r →
    (∃ t v, greadsByte G r a t v) →
    grfAt G a wl r := by
  intro hsub hwf hlv hwrites hch hcov hvisl hrd
  have hwlin : wl ∈ Hl0 ++ [wl] := elem_of_app.2 (Or.inr (elem_of_list_singleton.2 rfl))
  obtain ⟨w, hlast, hrf⟩ :=
    ownedReadWith G R (Hl0 ++ [wl]) a r wl hsub hwf hlv hwrites hch hcov hwlin hvisl hrd
  have hsn : lastVisible G (Hl0 ++ [wl]) r = some wl := lastSuchSnoc _ _ _ _ hvisl
  rw [hsn, Option.some.injEq] at hlast
  subst hlast
  exact hrf

/-- ... and the VALUE the read observes is the one the last entry wrote. -/
theorem ownedReadValueWith (G : Gexec) (R : Geid → Geid → Prop) (Hl0 : List Geid) (wl : Geid)
    (a : Int) (r : Geid) (t : Nat) (v vl : BitVec 8) :
    (∀ x y, R x y → gmoLt G x y) → gwf G → gloadValue G →
    (∀ w, w ∈ Hl0 ++ [wl] → ∃ v', gwritesByte G w a v') →
    chainWith R (Hl0 ++ [wl]) →
    (∀ w v', gwritesByte G w a v' → gvisible G w r → w ∈ Hl0 ++ [wl]) →
    gvisible G wl r →
    greadsByte G r a t v →
    gwritesByte G wl a vl →
    v = vl := by
  intro hsub hwf hlv hwrites hch hcov hvisl hrd hwbl
  exact grfAtValue G a wl r t v vl hlv
    (ownedReadSnocWith G R Hl0 wl a r hsub hwf hlv hwrites hch hcov hvisl ⟨t, v, hrd⟩) hrd hwbl

/-! ## 4.3 The `gob` instances (the original statements) -/

theorem ownedRead (GD : Gdexec) (Hl : List Geid) (a : Int) (r w0 : Geid) :
    rvwmoMinusDepsConsistent GD →
    (∀ w, w ∈ Hl → ∃ v, gwritesByte GD.gdG w a v) →
    obChain GD Hl →
    (∀ w v, gwritesByte GD.gdG w a v → gvisible GD.gdG w r → w ∈ Hl) →
    w0 ∈ Hl → gvisible GD.gdG w0 r →
    (∃ t v, greadsByte GD.gdG r a t v) →
    ∃ w, lastVisible GD.gdG Hl r = some w ∧ grfAt GD.gdG a w r := by
  intro hcons
  have ⟨⟨hwf, _, hlv, _⟩, _, _⟩ := hcons
  exact ownedReadWith GD.gdG (gob GD) Hl a r w0 (fun x y => obSubGmo GD x y hcons) hwf hlv

theorem ownedReadSnoc (GD : Gdexec) (Hl0 : List Geid) (wl : Geid) (a : Int) (r : Geid) :
    rvwmoMinusDepsConsistent GD →
    (∀ w, w ∈ Hl0 ++ [wl] → ∃ v, gwritesByte GD.gdG w a v) →
    obChain GD (Hl0 ++ [wl]) →
    (∀ w v, gwritesByte GD.gdG w a v → gvisible GD.gdG w r → w ∈ Hl0 ++ [wl]) →
    gvisible GD.gdG wl r →
    (∃ t v, greadsByte GD.gdG r a t v) →
    grfAt GD.gdG a wl r := by
  intro hcons
  have ⟨⟨hwf, _, hlv, _⟩, _, _⟩ := hcons
  exact ownedReadSnocWith GD.gdG (gob GD) Hl0 wl a r (fun x y => obSubGmo GD x y hcons) hwf hlv

theorem ownedReadValue (GD : Gdexec) (Hl0 : List Geid) (wl : Geid) (a : Int) (r : Geid) (t : Nat)
    (v vl : BitVec 8) :
    rvwmoMinusDepsConsistent GD →
    (∀ w, w ∈ Hl0 ++ [wl] → ∃ v', gwritesByte GD.gdG w a v') →
    obChain GD (Hl0 ++ [wl]) →
    (∀ w v', gwritesByte GD.gdG w a v' → gvisible GD.gdG w r → w ∈ Hl0 ++ [wl]) →
    gvisible GD.gdG wl r →
    greadsByte GD.gdG r a t v →
    gwritesByte GD.gdG wl a vl →
    v = vl := by
  intro hcons
  have ⟨⟨hwf, _, hlv, _⟩, _, _⟩ := hcons
  exact ownedReadValueWith GD.gdG (gob GD) Hl0 wl a r t v vl
    (fun x y => obSubGmo GD x y hcons) hwf hlv

/-! # 5. Visibility: the two cases, and FORWARDING -/

/-- `gvisible` is `gmoLt ∨ gpo`; the second case is only interesting when the
first FAILS — a store gmo-after its own po-earlier read, which is LB's shape. -/
theorem visibleCases (G : Gexec) (w r : Geid) :
    gvisible G w r → gmoLt G w r ∨ (WeakRvwmoGraph.gpo G w r ∧ ¬ gmoLt G w r) := by
  rintro (h | h)
  · exact Or.inl h
  · by_cases hm : gmoLt G w r
    · exact Or.inl hm
    · exact Or.inr ⟨h, hm⟩

/-- FORWARDING, the commissioned (weak) form.  NEITHER `¬ gmoLt w r` NOR the
no-intervening-write hypothesis is needed for this conclusion. -/
theorem ownForwardWeak (G : Gexec) (a : Int) (w r : Geid) (v : BitVec 8) (t : Nat)
    (vr : BitVec 8) :
    gwf G → gloadValue G →
    WeakRvwmoGraph.gpo G w r → gwritesByte G w a v → greadsByte G r a t vr →
    ∃ ws, grfAt G a ws r ∧ gwritesByte G ws a vr ∧ gvisible G ws r ∧
      (ws = w ∨ gco G w ws) := by
  intro hwf hlv hpo hwb hrd
  have hvis : gvisible G w r := Or.inr hpo
  obtain ⟨ws, hrf, hwbs, hviss⟩ := grfAtExists G r a t vr w v hwf hlv hrd hwb hvis
  refine ⟨ws, hrf, hwbs, hviss, ?_⟩
  have hgw := gwritesByteGwrites G w a v hwf hwb
  have hgws := gwritesByteGwrites G ws a vr hwf hwbs
  have hle := grfAtComax G a ws r w v hwf hlv hrf hwb hvis
  by_cases heq : gwix G w = gwix G ws
  · exact Or.inl (gwixInj G w ws hwf.1 hgw hgws heq).symm
  · exact Or.inr ⟨a, v, vr, hwb, hwbs, by omega⟩

/-- FORWARDING, THE TRUE FORM.  Under the two extra hypotheses — and `gppoGmo`,
which only full `rvwmoMinusConsistent` supplies — the "co-later visible write"
disjunct is impossible: the rf-source of `r` at `a` IS `w`. -/
theorem ownForward (G : Gexec) (a : Int) (w r : Geid) (v : BitVec 8) (t : Nat) (vr : BitVec 8) :
    rvwmoMinusConsistent G →
    WeakRvwmoGraph.gpo G w r → gwritesByte G w a v → greadsByte G r a t vr →
    ¬ gmoLt G w r →
    (∀ w' v', gwritesByte G w' a v' → WeakRvwmoGraph.gpo G w w' →
      WeakRvwmoGraph.gpo G w' r → False) →
    grfAt G a w r ∧ vr = v := by
  intro hcons hpo hwb hrd hnmo hnoint
  obtain ⟨hwf, hppo, hlv, _⟩ := hcons
  obtain ⟨ws, hrf, hwbs, hviss, hor⟩ := ownForwardWeak G a w r v t vr hwf hlv hpo hwb hrd
  rcases hor with heq | hco
  · subst heq
    exact ⟨hrf, gwritesByteDet G ws a vr v hwbs hwb⟩
  exfalso
  have hmows := gcoGmo G w ws hwf hco
  -- `ws` is visible; the gmo disjunct would compose to `gmoLt w r`
  have hposr : WeakRvwmoGraph.gpo G ws r := by
    rcases hviss with hmo | hp
    · exact absurd (gmoLtTrans G _ _ _ hmows hmo) hnmo
    · exact hp
  obtain ⟨hag1, _, hs1, _⟩ := hpo
  obtain ⟨hag2, hlt2, hs3, hs4⟩ := hposr
  have hag : ws.1 = w.1 := hag2.trans hag1.symm
  by_cases hlt : w.2 < ws.2
  · -- `ws` is po-BETWEEN `w` and `r`: killed by the hypothesis
    exact hnoint ws vr hwbs ⟨hag.symm, hlt, hs1, hs3⟩ ⟨hag2, hlt2, hs3, hs4⟩
  · by_cases heq2 : w.2 = ws.2
    · -- same event: `gco` is irreflexive through `gmo`
      have hwe : w = ws := Prod.ext hag.symm heq2
      subst hwe
      exact gmoLtIrrefl G _ hmows
    · -- `ws` is po-EARLIER, same byte: gpoloc ⊆ ppo⁻ ⊆ gmo
      have hmosw : gmoLt G ws w :=
        hppo ws w (Or.inl ⟨⟨hag, by omega, hs3, hs1⟩, a, Or.inl ⟨vr, hwbs⟩, Or.inl ⟨v, hwb⟩⟩)
      exact gmoLtIrrefl G _ (gmoLtTrans G _ _ _ hmosw hmows)

/-! # 6. SANITY on the LB witness `lbgd`

`gob` is acyclic there (by `obIrreflexive`); both loads' rf-sources are the
OTHER hart's store, uniquely, and both edges are `grfe`. -/

theorem lbObIrreflexive (x : Geid) : ¬ gob lbgd x x :=
  obIrreflexive lbgd x lbGraphDepsConsistent

theorem lbObAcyclic (x y : Geid) : gob lbgd x y → ¬ gob lbgd y x :=
  obAsym lbgd x y lbGraphDepsConsistent

/-- Hart 1's load `(1,0)` (byte 8) reads hart 0's store `(0,1)`. -/
theorem lbRf10 : grfAt lbg 8 (0, 1) (1, 0) :=
  ⟨1, b1, ⟨LLoad false 8 [1] [b1], 8, [1], [b1], 0, rfl, rfl, rfl, rfl, by simp [accAddr]⟩,
    by decide⟩

/-- Hart 0's load `(0,0)` (byte 0) reads hart 1's store `(1,1)`. -/
theorem lbRf01 : grfAt lbg 0 (1, 1) (0, 0) :=
  ⟨2, b1, ⟨LLoad false 0 [2] [b1], 0, [2], [b1], 0, rfl, rfl, rfl, rfl, by simp [accAddr]⟩,
    by decide⟩

/-- THE LB SHAPE: both rf edges are EXTERNAL, and each is the UNIQUE source at its
byte. -/
theorem lbBothLoadsReadTheOtherHart :
    grfe lbg (0, 1) (1, 0) ∧
    grfe lbg (1, 1) (0, 0) ∧
    (∀ w, grfAt lbg 8 w (1, 0) → w = (0, 1)) ∧
    (∀ w, grfAt lbg 0 w (0, 0) → w = (1, 1)) :=
  ⟨⟨grfAtGrf _ _ _ _ lbRf10, by decide⟩, ⟨grfAtGrf _ _ _ _ lbRf01, by decide⟩,
    fun w hw => grfAtDet _ _ _ _ _ hw lbRf10, fun w hw => grfAtDet _ _ _ _ _ hw lbRf01⟩

/-- The two rf edges ARE `gob` steps (so `gob` is non-empty on `lbgd`) and are
gmo-forward — §3's theorem, instantiated. -/
theorem lbObRfe :
    gob lbgd (0, 1) (1, 0) ∧
    gob lbgd (1, 1) (0, 0) ∧
    gmoLt lbg (0, 1) (1, 0) ∧
    gmoLt lbg (1, 1) (0, 0) := by
  obtain ⟨h1, h2, _, _⟩ := lbBothLoadsReadTheOtherHart
  have hob1 : gob lbgd (0, 1) (1, 0) := gobStep _ _ _ (Or.inr (Or.inr (Or.inl h1)))
  have hob2 : gob lbgd (1, 1) (0, 0) := gobStep _ _ _ (Or.inr (Or.inr (Or.inl h2)))
  exact ⟨hob1, hob2, obSubGmo lbgd _ _ lbGraphDepsConsistent hob1,
    obSubGmo lbgd _ _ lbGraphDepsConsistent hob2⟩

/-! ## 6.1 NON-VACUITY of `ownedReadSnoc`

Hart 1's load of byte 8 against the one-entry history `[(0,1)]` — hart 0's store
to byte 8, the only write to that byte in `lbg`, so coverage is free —
reproduces `lbRf10` through the GENERIC machinery. -/

theorem lbgWb01 : gwritesByte lbg (0, 1) 8 b1 :=
  ⟨LStore false 8 [b1] .WCplain, 8, [b1], 0, rfl, rfl, rfl, by simp [accAddr]⟩

theorem lbgVis0110 : gvisible lbg (0, 1) (1, 0) :=
  Or.inl ⟨by decide, by decide, by decide⟩

theorem lbOwnedRead : grfAt lbg 8 (0, 1) (1, 0) := by
  refine ownedReadSnoc lbgd [] (0, 1) 8 (1, 0) lbGraphDepsConsistent ?_ ?_ ?_ ?_ ?_
  · intro w hw
    rw [List.nil_append, elem_of_list_singleton] at hw
    subst hw
    exact ⟨b1, lbgWb01⟩
  · intro i w1 w2 _ h2
    simp at h2
  · intro w v hw _
    rcases lbgWr w 8 v hw with ⟨rfl, _⟩ | ⟨rfl, hab⟩
    · simp
    · simp at hab
  · exact lbgVis0110
  · exact ⟨1, b1, LLoad false 8 [1] [b1], 8, [1], [b1], 0, rfl, rfl, rfl, rfl, by simp [accAddr]⟩

end Weak
