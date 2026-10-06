/-
Weak: **the graph-side FLAT MEMORY, and its agreement with rf** (AxSL tier).

Rocq: `iris/AxBridge.v` @ xxvzwolszwmp.

The Rocq header, in substance (design: `claude-notes/design/weak-memory-lb-axsl.md`
§1-L3 "Leaf layer RE-DERIVED" / AxBridge).  PURE (no Iris): the graph-side flat
memory the instruction rule (L3) evaluates the SC certificate against.

THE IDEA.  At a program position `e` of hart `i`, memory is: the po-latest of the
hart's OWN pending (forwarded) writes to the byte, if any (`ownPendingK`), else
the gmo-latest write to the byte among events gmo-BEFORE `e` (`prefixLatest` over
`gmoPrefix`), else the era-initial image byte (`G.gxImg`).  `flatMemSpec` shows
this is exactly "the value of the gwix-maximal write to the byte that is
`gvisible` from `e`", falling back to the image when none exists — `gloadValue`'s
own characterization of what a HYPOTHETICAL read at `e` would see.

  §1  `gwrVal` — the computable value a write event puts at a byte;
  §2  `gmoPrefix`/`gmoPrefixSpec`, `prefixLatestW`/`prefixLatest`;
  §3  `ownPendingDec`/`ownPendingK` (via `lastSuch` over `List.range' 0 e.2`);
  §4  `flatMem`, `flatMemSpec`, and the reusable half `flatMemUnique`;
  §5  `flatMemGrf`/`flatMemReadValue` (a read's value IS flat memory at the read)
      and `flatMemOwned` (under `ownedReadCatSnoc`'s hypotheses);
  §6  `flatMemWrite` — after a write, a later same-hart access reads its value,
      under the Rocq header's CORRECTED side conditions: no other same-byte write
      gmo-between `w` and `e`, AND no same-byte write po-strictly-between them
      (both needed; neither implies the other);
  §7  `flatMemBytes` and its agreement with an `LLoad`'s value list;
  §8  `flatMemB` and smoke tests on `AxGraphWit.fwd` / `AxGraphWit.rel`.

FETCHES (owner decision D1): this tier keeps the Rocq treatment — a fetch is a
graph `LLoad` read like any other; nothing in this file distinguishes it.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  None of this file's
   names is in `notes/weak-port-dupnames.json`; the dependencies' duplicates are
   referred to qualified (`WeakRvwmoGraph.gpo`, `WeakRvwmoGraph.gwixPos`,
   `WeakRvwmoLock.gwritesByteLbl`, `AxGraphWit.rel`).
2. VOCABULARY: as `AxGraph` deviation 2 (`agent` ↦ `Nat`, `Z` ↦ `Int`, `bv 8` ↦
   `BitVec 8`, `seq` ↦ `List.range'`, `mapM` ↦ `List.mapM`, `list_find` ↦
   `listFind` with a `Bool` predicate, `Decision` ↦ `Decidable`, `gd_g` ↦
   `.gdG`, `gx_img G a` ↦ `G.gxImg a`, `bv_eqb` ↦ `AxGraphDec.bvEqb`).
   `prefixLatest`'s option-monad `w ← _; v ← _; Some (w, v)` is `Option.bind`.
3. The `Decision` instances (`byte_write_dec`, `own_pending_dec_inst`) are
   transparent `Decidable` instances built from the `Bool` checkers by `if`.
4. `flatMemWriteMax`: the event `e`'s label `isSome` is taken from the `gpo w' e`
   hypothesis already in hand instead of `gwfGmoMem` (same statement).
5. The four `vm_compute` smoke tests are `decide +kernel`.

**Name map** (Rocq → Lean): `gwr_val` ↦ `gwrVal`; `gwr_val_of_write` ↦
`gwrValOfWrite`; `byte_write_dec` ↦ `byteWriteDec`; `gmo_prefix` ↦ `gmoPrefix`;
`gmo_prefix_spec` ↦ `gmoPrefixSpec`; `gmo_prefix_index_gpos` ↦
`gmoPrefixIndexGpos`; `prefix_latest_w` ↦ `prefixLatestW`; `prefix_latest` ↦
`prefixLatest`; `prefix_latest_w_spec` ↦ `prefixLatestWSpec`;
`prefix_latest_w_none` ↦ `prefixLatestWNone`; `own_pending_dec` ↦
`ownPendingDec`; `own_pending_b` ↦ `ownPendingB`; `own_pending_b_spec` ↦
`ownPendingBSpec`; `own_pending_dec_inst` ↦ `ownPendingDecInst`;
`own_pending_k` ↦ `ownPendingK`; `own_pending_k_spec` ↦ `ownPendingKSpec`;
`own_pending_k_none` ↦ `ownPendingKNone`; `flat_mem` ↦ `flatMem`;
`gvisible_irrefl` ↦ `gvisibleIrrefl`; `flat_mem_case` ↦ `flatMemCase`;
`flat_mem_spec` ↦ `flatMemSpec`; `flat_mem_unique` ↦ `flatMemUnique`;
`flat_mem_grf` ↦ `flatMemGrf`; `flat_mem_read_value` ↦ `flatMemReadValue`;
`flat_mem_owned` ↦ `flatMemOwned`; `flat_mem_write_max` ↦ `flatMemWriteMax`;
`flat_mem_write` ↦ `flatMemWrite`; `flat_mem_bytes` ↦ `flatMemBytes`;
`flat_mem_bytes_of_lookup` ↦ `flatMemBytesOfLookup`; `flat_mem_bytes_of_read` ↦
`flatMemBytesOfRead`; `flat_mem_b` ↦ `flatMemB`; `flat_mem_b_spec` ↦
`flatMemBSpec`; `flat_mem_fwd_smoke` ↦ `flatMemFwdSmoke`; `flat_mem_fwd_smoke_b`
↦ `flatMemFwdSmokeB`; `flat_mem_rel_smoke` ↦ `flatMemRelSmoke`;
`flat_mem_rel_smoke_b` ↦ `flatMemRelSmokeB`.

**Not ported:** nothing (the §9 `Print Assumptions` block has no Lean twin; the
lint's axiom check covers it).
-/
import Weak.WeakRvwmoDec
import Weak.AxGraph
import Weak.AxGraphCat
import Weak.AxGraphDec
import Weak.AxGraphWit

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl

/-! # 1. The value a write puts at a byte, computably -/

def gwrVal (G : Gexec) (w : Geid) (a : Int) : Option (BitVec 8) :=
  match listFind (fun x : Int × BitVec 8 => decide (x.1 = a)) (gwrBytes G w) with
  | some (_, x) => some x.2
  | none => none

theorem gwrValOfWrite (G : Gexec) (w : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte G w a v → gwrVal G w a = some v := by
  intro hwb
  have hmem : (a, v) ∈ gwrBytes G w := (gwritesByteBytes G w a v).1 hwb
  unfold gwrVal
  cases hf : listFind (fun x : Int × BitVec 8 => decide (x.1 = a)) (gwrBytes G w) with
  | some q =>
    obtain ⟨i0, x0⟩ := q
    obtain ⟨hi0, hp0, _⟩ := list_find_Some.1 hf
    have hx0 : gwritesByte G w x0.1 x0.2 :=
      (gwritesByteBytes G w x0.1 x0.2).2 (elem_of_list_lookup_2 hi0)
    have ha : x0.1 = a := of_decide_eq_true hp0
    rw [ha] at hx0
    exact congrArg some (gwritesByteDet G w a x0.2 v hx0 hwb)
  | none =>
    have := list_find_None.1 hf (a, v) hmem
    simp at this

/-- A byte-write existence check, `AxGraphDec` style: the decision `lastSuch`
needs. -/
instance byteWriteDec (G : Gexec) (a : Int) (w : Geid) :
    Decidable (∃ v, gwritesByte G w a v) :=
  if hb : gwaB G w a = true then isTrue ((gwaBSpec G w a).1 hb)
  else isFalse (fun h => hb ((gwaBSpec G w a).2 h))

/-! # 2. The gmo-prefix of an event, and the co-maximal write in it -/

def gmoPrefix (G : Gexec) (e : Geid) : List Geid :=
  G.gxGmo.take (gpos G e)

theorem gmoPrefixSpec (G : Gexec) (e w : Geid) :
    gwf G → e ∈ G.gxGmo → (w ∈ gmoPrefix G e ↔ gmoLt G w e) := by
  intro hwf he
  unfold gmoPrefix
  rw [elem_of_take]
  constructor
  · rintro ⟨m, hm, hlt⟩
    have hg : gpos G w = m := gposOfLookup G m w hwf.1 hm
    exact ⟨elem_of_list_lookup_2 hm, he, by rw [hg]; exact hlt⟩
  · rintro ⟨hw, _, hlt⟩
    exact ⟨gpos G w, gposElemLookup G w hw, hlt⟩

theorem gmoPrefixIndexGpos (G : Gexec) (e w : Geid) (m : Nat) :
    gwf G → (gmoPrefix G e)[m]? = some w → gpos G w = m := by
  intro hwf hm
  have hb : m < gpos G e := by
    have := lookup_lt_Some hm
    unfold gmoPrefix at this
    rw [List.length_take] at this
    omega
  have hgm : G.gxGmo[m]? = some w := by
    unfold gmoPrefix at hm
    rw [lookup_take hb] at hm
    exact hm
  exact gposOfLookup G m w hwf.1 hgm

def prefixLatestW (G : Gexec) (e : Geid) (a : Int) : Option Geid :=
  lastSuch (fun w => ∃ v, gwritesByte G w a v) (byteWriteDec G a) (gmoPrefix G e)

def prefixLatest (G : Gexec) (e : Geid) (a : Int) : Option (Geid × BitVec 8) :=
  (prefixLatestW G e a).bind (fun w => (gwrVal G w a).bind (fun v => some (w, v)))

theorem prefixLatestWSpec (G : Gexec) (e w : Geid) (a : Int) :
    gwf G → e ∈ G.gxGmo →
    prefixLatestW G e a = some w →
    gmoLt G w e ∧ (∃ v, gwritesByte G w a v) ∧
    (∀ w', gmoLt G w' e → (∃ v', gwritesByte G w' a v') → gpos G w' ≤ gpos G w) := by
  intro hwf he heq
  unfold prefixLatestW at heq
  obtain ⟨m, hm, hP, hmax⟩ := lastSuchSpec _ _ _ _ heq
  have hwmo : gmoLt G w e := (gmoPrefixSpec G e w hwf he).1 (elem_of_list_lookup_2 hm)
  refine ⟨hwmo, hP, ?_⟩
  intro w' hw'mo hP'
  obtain ⟨m', hm'⟩ := elem_of_list_lookup_1 ((gmoPrefixSpec G e w' hwf he).2 hw'mo)
  have hle := hmax m' w' hm' hP'
  rw [gmoPrefixIndexGpos G e w m hwf hm, gmoPrefixIndexGpos G e w' m' hwf hm']
  exact hle

theorem prefixLatestWNone (G : Gexec) (e : Geid) (a : Int) :
    gwf G → e ∈ G.gxGmo →
    prefixLatestW G e a = none →
    ∀ w, gmoLt G w e → ¬ ∃ v, gwritesByte G w a v := by
  intro hwf he heq w hwmo hex
  unfold prefixLatestW at heq
  obtain ⟨m, hm⟩ := elem_of_list_lookup_1 ((gmoPrefixSpec G e w hwf he).2 hwmo)
  exact lastSuchNone _ _ _ heq m w hm hex

/-! # 3. Own pending (forwarded) writes: hart `i`'s own writes to `a` that are
po-before `e` and gmo-AFTER `e` -/

def ownPendingDec (G : Gexec) (i : Nat) (e : Geid) (a : Int) (k : Nat) : Prop :=
  WeakRvwmoGraph.gpo G (i, k) e ∧ gmoLt G e (i, k) ∧ ∃ v, gwritesByte G (i, k) a v

def ownPendingB (G : Gexec) (i : Nat) (e : Geid) (a : Int) (k : Nat) : Bool :=
  gpoB G (i, k) e && gmoLtB G e (i, k) && gwaB G (i, k) a

theorem ownPendingBSpec (G : Gexec) (i : Nat) (e : Geid) (a : Int) (k : Nat) :
    ownPendingB G i e a k = true ↔ ownPendingDec G i e a k := by
  simp only [ownPendingB, ownPendingDec, Bool.and_eq_true, gpoBSpec, gmoLtBSpec, gwaBSpec,
    and_assoc]

instance ownPendingDecInst (G : Gexec) (i : Nat) (e : Geid) (a : Int) (k : Nat) :
    Decidable (ownPendingDec G i e a k) :=
  if hb : ownPendingB G i e a k = true then isTrue ((ownPendingBSpec G i e a k).1 hb)
  else isFalse (fun h => hb ((ownPendingBSpec G i e a k).2 h))

def ownPendingK (G : Gexec) (i : Nat) (e : Geid) (a : Int) : Option Nat :=
  lastSuch (ownPendingDec G i e a) (ownPendingDecInst G i e a) (List.range' 0 e.2)

theorem ownPendingKSpec (G : Gexec) (i : Nat) (e : Geid) (a : Int) (k : Nat) :
    ownPendingK G i e a = some k →
    ownPendingDec G i e a k ∧
    (∀ k', k' < e.2 → ownPendingDec G i e a k' → k' ≤ k) := by
  intro heq
  unfold ownPendingK at heq
  obtain ⟨m, hm, hP, hmax⟩ := lastSuchSpec _ _ _ _ heq
  have hkm : k = m := by
    have := (lookup_seq.1 hm).1
    omega
  subst hkm
  refine ⟨hP, ?_⟩
  intro k' hk' hP'
  exact hmax k' k' (lookup_seq.2 ⟨by omega, hk'⟩) hP'

theorem ownPendingKNone (G : Gexec) (i : Nat) (e : Geid) (a : Int) :
    ownPendingK G i e a = none →
    ∀ k, k < e.2 → ¬ ownPendingDec G i e a k := by
  intro heq k hk hod
  unfold ownPendingK at heq
  exact lastSuchNone _ _ _ heq k k (lookup_seq.2 ⟨by omega, hk⟩) hod

/-! # 4. Flat memory, and its characterization -/

def flatMem (G : Gexec) (i : Nat) (e : Geid) (a : Int) : Option (BitVec 8) :=
  match ownPendingK G i e a with
  | some k => gwrVal G (i, k) a
  | none =>
    match prefixLatest G e a with
    | some (_, v) => some v
    | none => G.gxImg a

theorem gvisibleIrrefl (G : Gexec) (e : Geid) : ¬ gvisible G e e := by
  rintro (hmo | hpo)
  · exact gmoLtIrrefl G e hmo
  · exact Nat.lt_irrefl _ hpo.2.1

/-- Every candidate write for byte `a` visible from `e` is either gmo-before `e`
or one of hart `i`'s own po-before-`e` writes that is gmo-AFTER `e` — PROVIDED
`e ∈ G.gxGmo` (totality) and `i = e.1`. -/
theorem flatMemCase (G : Gexec) (i : Nat) (e w' : Geid) (a : Int) (v' : BitVec 8) :
    gwf G → e ∈ G.gxGmo → i = e.1 →
    gwritesByte G w' a v' → gvisible G w' e →
    gmoLt G w' e ∨ (WeakRvwmoGraph.gpo G w' e ∧ gmoLt G e w') := by
  intro hwf he _ hwb hvis
  have hmem := ((gwritesElemOf G w').1 (gwritesByteGwrites G w' a v' hwf hwb)).1
  by_cases hne : w' = e
  · subst hne
    exact absurd hvis (gvisibleIrrefl G w')
  rcases gmoLtTotal G w' e hwf.1 hmem he hne with hlt | hlt
  · exact .inl hlt
  · refine .inr ⟨?_, hlt⟩
    rcases hvis with hmo | hpo
    · exact absurd (gmoLtTrans G _ _ _ hmo hlt) (gmoLtIrrefl G w')
    · exact hpo

/-- THE CHARACTERIZATION: `flatMem` is the value of the gwix-maximal write to `a`
visible from `e`, or the image byte when none is visible. -/
theorem flatMemSpec (G : Gexec) (i : Nat) (e : Geid) (a : Int) :
    gwf G → (∀ e1 e2, gppo1 G e1 e2 → gmoLt G e1 e2) → e ∈ G.gxGmo → i = e.1 →
    (∃ w v, gwritesByte G w a v ∧ gvisible G w e ∧
        (∀ w' v', gwritesByte G w' a v' → gvisible G w' e → gwix G w' ≤ gwix G w) ∧
        flatMem G i e a = some v) ∨
    ((∀ w v, gwritesByte G w a v → ¬ gvisible G w e) ∧
     flatMem G i e a = G.gxImg a) := by
  intro hwf hr1 he hi
  have hnd := hwf.1
  cases hok : ownPendingK G i e a with
  | some k =>
    left
    obtain ⟨⟨hpoik, hgmoik, v, hwbik⟩, hmaxk⟩ := ownPendingKSpec G i e a k hok
    refine ⟨(i, k), v, hwbik, .inr hpoik, ?_, ?_⟩
    · rintro ⟨wi, wk⟩ v' hwb' hvis'
      have hg1 := gwritesByteGwrites G _ a v' hwf hwb'
      have hg2 := gwritesByteGwrites G _ a v hwf hwbik
      rcases flatMemCase G i e (wi, wk) a v' hwf he hi hwb' hvis' with hlt | ⟨hpw', hgmw'⟩
      · have hww := gmoLtTrans G _ _ _ hlt hgmoik
        have := (gwixGposLt G (wi, wk) (i, k) hnd hg1 hg2).2 hww.2.2
        omega
      · have hwi : wi = i := hpw'.1.trans hi.symm
        subst wi
        have hle := hmaxk wk hpw'.2.1 ⟨hpw', hgmw', v', hwb'⟩
        by_cases hk : wk = k
        · subst hk
          exact Nat.le_refl _
        have hltk : wk < k := by omega
        have hgpo : WeakRvwmoGraph.gpo G (i, wk) (i, k) :=
          ⟨rfl, hltk, WeakRvwmoLock.gwritesByteLbl G _ a v' hwb',
            WeakRvwmoLock.gwritesByteLbl G _ a v hwbik⟩
        have hgm2 := hr1 _ _ ⟨hgpo, a, .inl ⟨v', hwb'⟩, v, hwbik⟩
        have := (gwixGposLt G (i, wk) (i, k) hnd hg1 hg2).2 hgm2.2.2
        omega
    · simp only [flatMem, hok]
      exact gwrValOfWrite G (i, k) a v hwbik
  | none =>
    cases hpw : prefixLatestW G e a with
    | some w =>
      obtain ⟨hwmo, ⟨v, hwbv⟩, hmaxw⟩ := prefixLatestWSpec G e w a hwf he hpw
      left
      refine ⟨w, v, hwbv, .inl hwmo, ?_, ?_⟩
      · rintro ⟨wi, wk⟩ v' hwb' hvis'
        rcases flatMemCase G i e (wi, wk) a v' hwf he hi hwb' hvis' with hlt | ⟨hpw', hgmw'⟩
        · have hle := hmaxw _ hlt ⟨v', hwb'⟩
          have hg1 := gwritesByteGwrites G _ a v' hwf hwb'
          have hg2 := gwritesByteGwrites G w a v hwf hwbv
          have hm1 := ((gwritesElemOf G _).1 hg1).1
          have hm2 := ((gwritesElemOf G _).1 hg2).1
          by_cases heqp : gpos G (wi, wk) = gpos G w
          · rw [gposInj G _ _ hnd hm1 hm2 heqp]
            exact Nat.le_refl _
          · have := (gwixGposLt G _ _ hnd hg1 hg2).2 (by omega)
            omega
        · exfalso
          have hwi : wi = i := hpw'.1.trans hi.symm
          subst wi
          exact ownPendingKNone G i e a hok wk hpw'.2.1 ⟨hpw', hgmw', v', hwb'⟩
      · simp only [flatMem, hok, prefixLatest, hpw, Option.bind, gwrValOfWrite G w a v hwbv]
    | none =>
      right
      refine ⟨?_, by simp only [flatMem, hok, prefixLatest, hpw, Option.bind]⟩
      rintro ⟨wi, wk⟩ v'' hwb'' hvis''
      rcases flatMemCase G i e (wi, wk) a v'' hwf he hi hwb'' hvis'' with hlt | ⟨hpo'', hgm''⟩
      · exact prefixLatestWNone G e a hwf he hpw _ hlt ⟨v'', hwb''⟩
      · have hwi : wi = i := hpo''.1.trans hi.symm
        subst wi
        exact ownPendingKNone G i e a hok wk hpo''.2.1 ⟨hpo'', hgm'', v'', hwb''⟩

/-- THE REUSABLE HALF: any INDEPENDENTLY established gwix-maximal visible write
pins `flatMem` (uniqueness, via `gwixInj`). -/
theorem flatMemUnique (G : Gexec) (i : Nat) (e w : Geid) (a : Int) (v : BitVec 8) :
    gwf G → (∀ e1 e2, gppo1 G e1 e2 → gmoLt G e1 e2) → e ∈ G.gxGmo → i = e.1 →
    gwritesByte G w a v → gvisible G w e →
    (∀ w' v', gwritesByte G w' a v' → gvisible G w' e → gwix G w' ≤ gwix G w) →
    flatMem G i e a = some v := by
  intro hwf hr1 he hi hwb hvis hmax
  rcases flatMemSpec G i e a hwf hr1 he hi with
    ⟨w2, v2, hwb2, hvis2, hmax2, heq⟩ | ⟨hnone, _⟩
  · have hle1 := hmax2 w v hwb hvis
    have hle2 := hmax w2 v2 hwb2 hvis2
    have hgw := gwritesByteGwrites G w a v hwf hwb
    have hgw2 := gwritesByteGwrites G w2 a v2 hwf hwb2
    have hweq := gwixInj G w w2 hwf.1 hgw hgw2 (by omega)
    rw [← hweq] at hwb2
    rw [heq, gwritesByteDet G w a v2 v hwb2 hwb]
  · exact absurd hvis (hnone w v hwb)

/-! # 5. Agreement with the graph's read/rf values -/

/-- A read's rf-value at a byte IS the flat-memory value at the read. -/
theorem flatMemGrf (G : Gexec) (a : Int) (w r : Geid) (t : Nat) (v : BitVec 8) :
    gwf G → gloadValue G → (∀ e1 e2, gppo1 G e1 e2 → gmoLt G e1 e2) →
    grfAt G a w r → greadsByte G r a t v →
    flatMem G r.1 r a = some v := by
  intro hwf hlv hr1 hrf hrd
  have hre := greadsByteGmo G r a t v hwf hrd
  obtain ⟨t0, v0, hrd0, hat0⟩ := hrf
  obtain ⟨ht, _⟩ := greadsByteDet G r a t0 v0 t v hrd0 hrd
  rw [ht] at hat0
  cases t with
  | zero => simp [gwriteAt] at hat0
  | succ t' =>
    have hwb := greadSourceByte G r a (t' + 1) v w hlv hrd hat0
    have hvis : gvisible G w r := by
      obtain ⟨w0, hat, _, hvis0⟩ := (hlv r a (t' + 1) v hrd).1
      rw [hat0, Option.some.injEq] at hat
      rw [hat]
      exact hvis0
    have hmax : ∀ w' v', gwritesByte G w' a v' → gvisible G w' r → gwix G w' ≤ gwix G w :=
      fun w' v' hwb' hvis' => grfAtComax G a w r w' v' hwf hlv ⟨t' + 1, v, hrd, hat0⟩ hwb' hvis'
    exact flatMemUnique G r.1 r w a v hwf hr1 hre rfl hwb hvis hmax

/-- More generally: ANY value a `greadsByte` fact assigns — image-sourced
(`t = 0`) or not — is the flat-memory value at the read. -/
theorem flatMemReadValue (G : Gexec) (r : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    gwf G → gloadValue G → (∀ e1 e2, gppo1 G e1 e2 → gmoLt G e1 e2) →
    greadsByte G r a t v → flatMem G r.1 r a = some v := by
  intro hwf hlv hr1 hrd
  cases t with
  | zero =>
    rcases flatMemSpec G r.1 r a hwf hr1 (greadsByteGmo G r a 0 v hwf hrd) rfl with
      ⟨w2, v2, hwb2, hvis2, _, _⟩ | ⟨_, heq⟩
    · exfalso
      have hmaxt := (hlv r a 0 v hrd).2
      have hpos := WeakRvwmoGraph.gwixPos G w2 (gwritesByteGwrites G w2 a v2 hwf hwb2)
      have := hmaxt w2 v2 hwb2 hvis2
      omega
    · rw [heq]
      exact (hlv r a 0 v hrd).1
  | succ t' =>
    obtain ⟨w, hat, _, _⟩ := (hlv r a (t' + 1) v hrd).1
    exact flatMemGrf G a w r (t' + 1) v hwf hlv hr1 ⟨t' + 1, v, hrd, hat⟩ hrd

/-- THE TOKEN CONNECTION.  Under `AxGraphCat.ownedReadCatSnoc`'s hypotheses, the
flat-memory value at the owned read `r` IS the last history entry's value. -/
theorem flatMemOwned (GD : Gdexec) (Hl0 : List Geid) (wl : Geid) (a : Int)
    (r : Geid) (t : Nat) (v vl : BitVec 8) :
    rvwmoCatConsistent GD →
    (∀ w, w ∈ Hl0 ++ [wl] → ∃ v', gwritesByte GD.gdG w a v') →
    obCatChain GD (Hl0 ++ [wl]) →
    (∀ w v', gwritesByte GD.gdG w a v' → gvisible GD.gdG w r →
             w ∈ Hl0 ++ [wl]) →
    gvisible GD.gdG wl r →
    greadsByte GD.gdG r a t v →
    gwritesByte GD.gdG wl a vl →
    flatMem GD.gdG r.1 r a = some v ∧ v = vl := by
  intro hcons hwr hch hcov hvisl hrd hwbl
  have hrf := ownedReadCatSnoc GD Hl0 wl a r hcons hwr hch hcov hvisl ⟨t, v, hrd⟩
  obtain ⟨hwf, hppo, hlv, _⟩ := hcons
  exact ⟨flatMemGrf _ a wl r t v hwf hlv (fun e1 e2 h1 => hppo e1 e2 (.inl (.inl h1))) hrf hrd,
    grfAtValue _ a wl r t v vl hlv hrf hrd hwbl⟩

/-! # 6. After a write: what a later same-hart access reads

See the header for why the side conditions differ from the commissioned
statement. -/

theorem flatMemWriteMax (G : Gexec) (hwf : gwf G)
    (hr1 : ∀ e1 e2, gppo1 G e1 e2 → gmoLt G e1 e2) (e w : Geid) (a : Int) (v : BitVec 8) :
    e ∈ G.gxGmo → WeakRvwmoGraph.gpo G w e → gwritesByte G w a v →
    (∀ w' v', gwritesByte G w' a v' → WeakRvwmoGraph.gpo G w w' →
      WeakRvwmoGraph.gpo G w' e → False) →
    (∀ w' v', gwritesByte G w' a v' → w' ≠ w → gmoLt G w w' → gmoLt G w' e → False) →
    ∀ w' v', gwritesByte G w' a v' → gvisible G w' e → gwix G w' ≤ gwix G w := by
  intro _ hpo hwb hnopo hbtw w' v' hwb' hvis'
  by_cases hne : w' = w
  · subst hne
    exact Nat.le_refl _
  have hnd := hwf.1
  have hgw := gwritesByteGwrites G w a v hwf hwb
  have hgw' := gwritesByteGwrites G w' a v' hwf hwb'
  have hmw := ((gwritesElemOf G w).1 hgw).1
  have hmw' := ((gwritesElemOf G w').1 hgw').1
  rcases gmoLtTotal G w' w hnd hmw' hmw hne with hlt | hgt
  · have := (gwixGposLt G w' w hnd hgw' hgw).2 hlt.2.2
    omega
  · exfalso
    by_cases hb : gmoLt G w' e
    · exact hbtw w' v' hwb' hne hgt hb
    · have hpo' : WeakRvwmoGraph.gpo G w' e := by
        rcases hvis' with h | h
        · exact absurd h hb
        · exact h
      obtain ⟨hagwe, _, _, _⟩ := hpo
      obtain ⟨hagw'e, hltw'e, _, hlbe⟩ := hpo'
      have hl := WeakRvwmoLock.gwritesByteLbl G w a v hwb
      have hl' := WeakRvwmoLock.gwritesByteLbl G w' a v' hwb'
      by_cases hlt2 : w'.2 < w.2
      · apply gmoLtIrrefl G w'
        refine gmoLtTrans G _ _ _ ?_ hgt
        exact hr1 _ _ ⟨⟨hagw'e.trans hagwe.symm, hlt2, hl', hl⟩, a, .inl ⟨v', hwb'⟩, v, hwb⟩
      · have hgtpos : w.2 < w'.2 := by
          by_cases heq2 : w.2 = w'.2
          · exact absurd (Prod.ext (hagw'e.trans hagwe.symm) heq2.symm) hne
          · omega
        exact hnopo w' v' hwb' ⟨hagwe.trans hagw'e.symm, hgtpos, hl, hl'⟩
          ⟨hagw'e, hltw'e, hl', hlbe⟩

theorem flatMemWrite (G : Gexec) (hwf : gwf G)
    (hr1 : ∀ e1 e2, gppo1 G e1 e2 → gmoLt G e1 e2) (w e : Geid) (a : Int) (v : BitVec 8) :
    e ∈ G.gxGmo → WeakRvwmoGraph.gpo G w e → gwritesByte G w a v →
    (∀ w' v', gwritesByte G w' a v' → WeakRvwmoGraph.gpo G w w' →
      WeakRvwmoGraph.gpo G w' e → False) →
    (∀ w' v', gwritesByte G w' a v' → w' ≠ w → gmoLt G w w' → gmoLt G w' e → False) →
    flatMem G w.1 e a = some v := fun he hpo hwb hnopo hbtw =>
  flatMemUnique G w.1 e w a v hwf hr1 he hpo.1 hwb (.inr hpo)
    (flatMemWriteMax G hwf hr1 e w a v he hpo hwb hnopo hbtw)

/-! # 7. Multi-byte flat memory -/

def flatMemBytes (G : Gexec) (i : Nat) (e : Geid) (base : Int) (n : Nat) :
    Option (List (BitVec 8)) :=
  (List.range' 0 n).mapM (fun j => flatMem G i e (accAddr base j))

theorem flatMemBytesOfLookup (G : Gexec) (i : Nat) (e : Geid) (base : Int)
    (n : Nat) (vs : List (BitVec 8)) :
    vs.length = n →
    (∀ j v, vs[j]? = some v → flatMem G i e (accAddr base j) = some v) →
    flatMemBytes G i e base n = some vs := by
  intro hlen hf
  unfold flatMemBytes
  apply mapM_Some_2
  apply Forall2_same_length_lookup_2
  · rw [List.length_range']
    exact hlen.symm
  · intro j x y hx hy
    have hxj : x = j := by
      have := (lookup_seq.1 hx).1
      omega
    subst hxj
    exact hf _ y hy

/-- AGREEMENT: an `LLoad`'s value list `vs` IS `flatMemBytes` at the read, byte
by byte, under per-byte `gloadValue`. -/
theorem flatMemBytesOfRead (G : Gexec) (r : Geid) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) :
    gwf G → gloadValue G → (∀ e1 e2, gppo1 G e1 e2 → gmoLt G e1 e2) →
    gxLbl G r = some (LLoad aq base ts vs) → ts.length = vs.length →
    flatMemBytes G r.1 r base vs.length = some vs := by
  intro hwf hlv hr1 hlbl hlen
  apply flatMemBytesOfLookup G r.1 r base vs.length vs rfl
  intro j v hv
  have hj : j < vs.length := lookup_lt_Some hv
  obtain ⟨t, ht⟩ := someOfIsSome (lookup_lt_is_Some_2 (l := ts) (i := j) (by omega))
  exact flatMemReadValue G r _ t v hwf hlv hr1
    ⟨LLoad aq base ts vs, base, ts, vs, j, hlbl, rfl, ht, hv, rfl⟩

/-! # 8. Computable checker, and smoke tests -/

def flatMemB (G : Gexec) (i : Nat) (e : Geid) (a : Int) (v : BitVec 8) : Bool :=
  match flatMem G i e a with
  | some v' => bvEqb v v'
  | none => false

theorem flatMemBSpec (G : Gexec) (i : Nat) (e : Geid) (a : Int) (v : BitVec 8) :
    flatMemB G i e a v = true ↔ flatMem G i e a = some v := by
  unfold flatMemB
  cases flatMem G i e a with
  | some v' =>
    rw [bvEqbSpec]
    constructor
    · intro h
      rw [h]
    · intro h
      exact (Option.some.inj h).symm
  | none => simp

/-- `AxGraphWit.fwd` (FWD+acq): hart 0's acquire read (0,1) is forwarded from its
own po-earlier store (0,0) — `flatMem` returns that store's value `b1`. -/
theorem flatMemFwdSmoke : flatMem fwd.gdG 0 (0, 1) 0 = some b1 := by decide +kernel

theorem flatMemFwdSmokeB : flatMemB fwd.gdG 0 (0, 1) 0 b1 = true := by decide +kernel

/-- `AxGraphWit.rel` (release-then-read): hart 0's read R0a (0,3) is NOT forwarded
from its own W0a (0,0) — the re-owner's later W1a (1,1) wins: `b2`. -/
theorem flatMemRelSmoke : flatMem AxGraphWit.rel.gdG 0 (0, 3) 0 = some b2 := by decide +kernel

theorem flatMemRelSmokeB : flatMemB AxGraphWit.rel.gdG 0 (0, 3) 0 b2 = true := by
  decide +kernel

end Weak
