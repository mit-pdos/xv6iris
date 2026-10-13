/-
Weak: **the exchange kit** (route B, stages B2a/B2c/B2b).

Rocq: `iris/WeakRvwmoXchg.v` @ xxvzwolszwmp.

The Rocq header, in substance (design: `claude-notes/design/weak-memory-route-b.md`
§3b).  The model is `WeakRvwmoGraph`'s RVWMO⁻.  Route B normalizes an
RVWMO⁻-consistent graph towards `grule14` by ADJACENT EXCHANGES in the global
memory order.  This file delivers the exchange steps:

  - `gswap G n` — the graph with gmo positions `n` and `n + 1` exchanged (§2), on
    top of a generic list-swap kit (§1) whose whole content is one index
    INVOLUTION `sidx`: `(lswap l n)[i]? = l[sidx n i]?`;
  - `gswapReadDown` (§3) — RVWMO⁻-consistency is preserved when the UPPER of the
    two swapped events is not a write, is not reading the lower one, and is not
    ppo⁻-ordered after it; `gswapReadDownDeps` (§4), the `Gdexec` corollary;
  - `gviol` + `gswapViolMono` / `gswapResolves` (§5) — rule-14 bookkeeping: a
    read-down swap never CREATES a violation and RESOLVES the swapped pair's;
  - `gswapWriteDown` (§6, B2c) — a WRITE descends past a read, with one co-max
    side condition; its `Gdexec` corollary and violation bookkeeping;
  - `gswapw` + `gswapwWw` (§7–§9, B2b) — the (W,W) move on BYTE-DISJOINT
    writes: the two `gwix` values exchange and every reader's `ts` entry is
    renumbered by the adjacent transposition `tswap` (= §1's `sidx`); the
    corresponding corollaries and bookkeeping (§9.1, §10), and two non-vacuity
    smoke tests on `lbg` (§3.1, §10.1).

Two side conditions beyond the order theory are hypothesized, as in Rocq:
`(x, e) ∉ gdDeps` on both descent corollaries, and `¬ gpo G x e` on the two
violation-monotonicity lemmas.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  None of this
   file's names is in `notes/weak-port-dupnames.json`, so none is
   file-qualified; the `WeakRvwmoGraph` duplicates used are referred to
   qualified (`WeakRvwmoGraph.gpo`, `WeakRvwmoGraph.gwritesByteGisW`, …).
2. VOCABULARY: as `WeakRvwmoGraph` deviation 2 (`l !! i` ↦ `l[i]?`, `S n` ↦
   `n + 1` (`S (S n)` ↦ `n + 2` in `lswap`'s `drop`, `S (S m)` ↦ `m + 1 + 1`
   in `gswapwWritesKit`), `NoDup` ↦ `List.Nodup`, `f <$> l` ↦ `l.map f`,
   `f <$> o` ↦ `o.map f`, `is_Some o` ↦ `o.isSome`, `Is_true b` ↦
   `b = true`).
3. `sidx`/`tswap` use `if i = n` (a decidable `Prop`) where Rocq uses
   `bool_decide`; `tswapUnfold` states the `if` form.
4. `lswap_filter`'s `P` with a `Decision` instance is a Boolean predicate `p`,
   and its hypothesis `¬ P a ∨ ¬ P b` is `p a = false ∨ p b = false`.
   `lswap_elem_of`'s `EqDecision A` premise is dropped (unused by the proof).
5. Rocq's `Section gswapw_wix` (contexts `G n x e m Hnd Hx He Hm HSm Hgws`) is
   flattened: each lemma takes exactly the context items its Rocq proof uses,
   in section order (as Rocq's section closing does).
6. The smoke tests' closed `vm_compute` side conditions are `decide`/`rfl`.
8. W13 (I) (`gwf`'s `LIo` shape arm flipped to `True`): `gswapUpperIsRead` takes the premise
   that `r` is not an I/O-class event (Rocq: none — no I/O events in its graphs).
7. Lean-only helper (no Rocq twin): `sidxSpec`, the three-way case analysis
   of `sidx` that every arithmetic proof here (Rocq: `repeat case_bool_decide;
   lia`) is run through.
9. D35-fix ([OWN.54]; `WeakRvwmoGraph` deviation 7): `gppo`'s rule-7 arm is `grcsc`, so
   `gswapwPpo` rewrites with the Lean-only `gswapwRcsc` (over the Lean-only `lblTswapRcsc`);
   `gswapwRelAcq` is kept.

**Name map** (Rocq → Lean): `sidx`; `sidx_n` ↦ `sidxN`; `sidx_Sn` ↦ `sidxSn`;
`sidx_id` ↦ `sidxId`; `sidx_invol` ↦ `sidxInvol`; `sidx_inj` ↦ `sidxInj`;
`sidx_mono` ↦ `sidxMono`; `sidx_mono_inv` ↦ `sidxMonoInv`; `lswap`;
`lswap_split` ↦ `lswapSplit`; `lsplit2`; `lswap_lookup` ↦ `lswapLookup`;
`lswap_elem_of` ↦ `lswapElemOf`; `lswap_NoDup` ↦ `lswapNoDup`; `lswap_length` ↦
`lswapLength`; `lswap_filter` ↦ `lswapFilter`; `lswap_app_middle` ↦
`lswapAppMiddle`; `gswap`; `gswap_img`/`_prog`/`_gmo`/`_lbl`/`_is_w`/`_mem`/
`_lbl_is`/`_wrb`/`_rdb`/`_accesses`/`_po`/`_ppo` ↦ `gswapImg`/`gswapProg`/
`gswapGmo`/`gswapLbl`/`gswapIsW`/`gswapMem`/`gswapLblIs`/`gswapWrb`/`gswapRdb`/
`gswapAccesses`/`gswapPo`/`gswapPpo`; `gswap_elem_of` ↦ `gswapElemOf`;
`gswap_nodup` ↦ `gswapNodup`; `gswap_gpos` ↦ `gswapGpos`; `gswap_gpos_lower` ↦
`gswapGposLower`; `gswap_gpos_upper` ↦ `gswapGposUpper`; `gswap_gmo_lt` ↦
`gswapGmoLt`; `gswap_gmo_lt_inv` ↦ `gswapGmoLtInv`; `gswap_gwrites` ↦
`gswapGwrites`; `gswap_gwrite_at` ↦ `gswapGwriteAt`; `gswap_gwix` ↦
`gswapGwix`; `gswap_upper_is_read` ↦ `gswapUpperIsRead`; `gswap_read_down` ↦
`gswapReadDown`; `lbg_swap_consistent` ↦ `lbgSwapConsistent`;
`gswap_read_down_deps` ↦ `gswapReadDownDeps`; `gviol`; `gviol_grule14` ↦
`gviolGrule14`; `gswap_viol_mono` ↦ `gswapViolMono`; `gswap_resolves` ↦
`gswapResolves`; `gswap_gwrites_lo`/`_gwrite_at_lo`/`_gwix_lo` ↦
`gswapGwritesLo`/`gswapGwriteAtLo`/`gswapGwixLo`; `gswap_write_down` ↦
`gswapWriteDown`; `gswap_write_down_deps` ↦ `gswapWriteDownDeps`;
`gswap_viol_mono_rw` ↦ `gswapViolMonoRw`; `tswap`; `tswap_unfold` ↦
`tswapUnfold`; `tswap_invol` ↦ `tswapInvol`; `tswap_inj` ↦ `tswapInj`;
`tswap_lt` ↦ `tswapLt`; `tswap_lt_inv` ↦ `tswapLtInv`; `tswap_le` ↦
`tswapLe`; `tswap_zero` ↦ `tswapZero`; `tswap_eq_zero` ↦ `tswapEqZero`;
`tswap_S` ↦ `tswapS`; `lbl_tswap` ↦ `lblTswap`; `lbl_tswap_is_r`/`_is_w`/
`_is_mem`/`_aq`/`_rl`/`_cls`/`_wr` ↦ `lblTswapIsR`/`lblTswapIsW`/
`lblTswapIsMem`/`lblTswapAq`/`lblTswapRl`/`lblTswapCls`/`lblTswapWr`;
`lbl_tswap_rd` ↦ `lblTswapRd`; `lbl_tswap_rd_inv` ↦ `lblTswapRdInv`;
`lbl_tswap_fence` ↦ `lblTswapFence`; `gswapw`; `gswapw_img`/`_gmo`/`_gpos`/
`_gmo_lt` ↦ `gswapwImg`/`gswapwGmo`/`gswapwGpos`/`gswapwGmoLt`; `gswapw_lbl` ↦
`gswapwLbl`; `gswapw_is_w` ↦ `gswapwIsW`; `gswapw_is_Some` ↦ `gswapwIsSome`;
`gswapw_glbl_is` ↦ `gswapwGlblIs`; `gswapw_mem` ↦ `gswapwMem`; `gswapw_wrb` ↦
`gswapwWrb`; `gswapw_rdb` ↦ `gswapwRdb`; `gswapw_accesses` ↦
`gswapwAccesses`; `gswapw_po` ↦ `gswapwPo`; `gswapw_fence_between` ↦
`gswapwFenceBetween`; `gswapw_poloc` ↦ `gswapwPoloc`; `gswapw_fence_covers` ↦
`gswapwFenceCovers`; `gswapw_acq_po` ↦ `gswapwAcqPo`; `gswapw_rel_acq` ↦
`gswapwRelAcq`; `gswapw_ppo` ↦ `gswapwPpo`; `gswapw_writes_kit` ↦
`gswapwWritesKit`; `gwix_adjacent` ↦ `gwixAdjacent`; `gswapw_gwrites_lookup` ↦
`gswapwGwritesLookup`; `gswapw_gwrite_at` ↦ `gswapwGwriteAt`; `gswapw_nodup'`
↦ `gswapwNodup'`; `gswapw_gwix` ↦ `gswapwGwix`; `gswapw_ww` ↦ `gswapwWw`;
`gswapw_ww_deps` ↦ `gswapwWwDeps`; `gswapw_viol_mono` ↦ `gswapwViolMono`;
`gswapw_resolves` ↦ `gswapwResolves`; `lbg_swapw_consistent` ↦
`lbgSwapwConsistent`.

**Not ported:** nothing.
-/
import Weak.WeakMem
import Weak.WeakAxiomatic
import Weak.WeakAxiomatic2
import Weak.WeakRvwmoGraph

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl

/-! # 1. A GENERIC ADJACENT-SWAP KIT FOR LISTS

Organised around the INDEX INVOLUTION `sidx n`, which exchanges `n` and `n + 1`
and fixes everything else. -/

/-! ## 1.1 The index involution -/

def sidx (n i : Nat) : Nat :=
  if i = n then n + 1 else if i = n + 1 then n else i

/-- Lean-only: the three cases of `sidx`. -/
theorem sidxSpec (n i : Nat) :
    (i = n ∧ sidx n i = n + 1) ∨ (i = n + 1 ∧ sidx n i = n) ∨
    (i ≠ n ∧ i ≠ n + 1 ∧ sidx n i = i) := by
  unfold sidx
  by_cases h1 : i = n
  · subst h1; simp
  · by_cases h2 : i = n + 1
    · subst h2; simp
    · simp [h1, h2]

theorem sidxN (n : Nat) : sidx n n = n + 1 := by
  rcases sidxSpec n n with h | h | h <;> omega

theorem sidxSn (n : Nat) : sidx n (n + 1) = n := by
  rcases sidxSpec n (n + 1) with h | h | h <;> omega

theorem sidxId (n i : Nat) : i ≠ n → i ≠ n + 1 → sidx n i = i := by
  intro h1 h2
  rcases sidxSpec n i with h | h | h <;> omega

theorem sidxInvol (n i : Nat) : sidx n (sidx n i) = i := by
  rcases sidxSpec n i with h | h | h <;> rcases sidxSpec n (sidx n i) with h' | h' | h' <;> omega

theorem sidxInj (n i j : Nat) : sidx n i = sidx n j → i = j := by
  intro heq
  rw [← sidxInvol n i, ← sidxInvol n j, heq]

/-- The order behaviour: `sidx` is monotone EXCEPT on the swapped pair. -/
theorem sidxMono (n p1 p2 : Nat) :
    p1 < p2 → ¬ (p1 = n ∧ p2 = n + 1) → sidx n p1 < sidx n p2 := by
  intro hlt hne
  rcases sidxSpec n p1 with h | h | h <;> rcases sidxSpec n p2 with h' | h' | h' <;> omega

theorem sidxMonoInv (n p1 p2 : Nat) :
    sidx n p1 < sidx n p2 → p1 < p2 ∨ (p1 = n + 1 ∧ p2 = n) := by
  intro hlt
  rcases sidxSpec n p1 with h | h | h <;> rcases sidxSpec n p2 with h' | h' | h' <;> omega

/-! ## 1.2 `lswap`: exchange the elements at positions `n` and `n + 1` -/

def lswap {A : Type _} (l : List A) (n : Nat) : List A :=
  match l[n]?, l[n + 1]? with
  | some a, some b => l.take n ++ b :: a :: l.drop (n + 2)
  | _, _ => l

theorem lswapSplit {A : Type _} (l : List A) (n : Nat) (a b : A) :
    l[n]? = some a → l[n + 1]? = some b →
    lswap l n = l.take n ++ b :: a :: l.drop (n + 2) := by
  intro hn hsn
  unfold lswap
  rw [hn, hsn]

/-- The companion decomposition of the ORIGINAL list, with the same take/drop
skeleton. -/
theorem lsplit2 {A : Type _} (l : List A) (n : Nat) (a b : A) :
    l[n]? = some a → l[n + 1]? = some b →
    l = l.take n ++ a :: b :: l.drop (n + 2) := by
  intro hn hsn
  apply List.ext_getElem?
  intro i
  have hlen : n + 1 < l.length := lookup_lt_Some hsn
  have htk : (l.take n).length = n := by simp; omega
  by_cases hi : i < n
  · rw [lookup_app_l (by omega), lookup_take hi]
  by_cases h1 : i = n
  · rw [h1, lookup_app_r (by omega), htk, Nat.sub_self, hn]; rfl
  by_cases h2 : i = n + 1
  · rw [h2, lookup_app_r (by omega), htk, show n + 1 - n = 0 + 1 by omega, hsn]; rfl
  · rw [lookup_app_r (by omega), htk, show i - n = (i - (n + 2)) + 1 + 1 by omega]
    simp only [List.getElem?_cons_succ, lookup_drop]
    congr 1
    omega

/-- THE EQUATION the whole kit rests on. -/
theorem lswapLookup {A : Type _} (l : List A) (n : Nat) (a b : A) (i : Nat) :
    l[n]? = some a → l[n + 1]? = some b →
    (lswap l n)[i]? = l[sidx n i]? := by
  intro hn hsn
  have hlen : n + 1 < l.length := lookup_lt_Some hsn
  have htk : (l.take n).length = n := by simp; omega
  rw [lswapSplit l n a b hn hsn]
  by_cases hi : i < n
  · rw [lookup_app_l (by omega), lookup_take hi, sidxId n i (by omega) (by omega)]
  by_cases h1 : i = n
  · rw [h1, lookup_app_r (by omega), htk, Nat.sub_self, sidxN, hsn]; rfl
  by_cases h2 : i = n + 1
  · rw [h2, lookup_app_r (by omega), htk, sidxSn, show n + 1 - n = 0 + 1 by omega, hn]; rfl
  · rw [lookup_app_r (by omega), htk, sidxId n i h1 h2,
      show i - n = (i - (n + 2)) + 1 + 1 by omega]
    simp only [List.getElem?_cons_succ, lookup_drop]
    congr 1
    omega

theorem lswapElemOf {A : Type _} (l : List A) (n : Nat) (a b x : A) :
    l[n]? = some a → l[n + 1]? = some b → (x ∈ lswap l n ↔ x ∈ l) := by
  intro hn hsn
  rw [elem_of_list_lookup, elem_of_list_lookup]
  constructor
  · rintro ⟨i, hi⟩
    rw [lswapLookup l n a b i hn hsn] at hi
    exact ⟨_, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨sidx n i, by rw [lswapLookup l n a b _ hn hsn, sidxInvol]; exact hi⟩

theorem lswapNoDup {A : Type _} (l : List A) (n : Nat) (a b : A) :
    l[n]? = some a → l[n + 1]? = some b → l.Nodup → (lswap l n).Nodup := by
  intro hn hsn hnd
  apply NoDup_alt.2
  intro i j x hi hj
  rw [lswapLookup l n a b i hn hsn] at hi
  rw [lswapLookup l n a b j hn hsn] at hj
  exact sidxInj n i j (NoDup_lookup hnd hi hj)

theorem lswapLength {A : Type _} (l : List A) (n : Nat) (a b : A) :
    l[n]? = some a → l[n + 1]? = some b → (lswap l n).length = l.length := by
  intro hn hsn
  have hlen : n + 1 < l.length := lookup_lt_Some hsn
  rw [lswapSplit l n a b hn hsn]
  simp
  omega

/-- THE FILTER FACT.  A swap is invisible to a filter that rejects one of the
two swapped elements. -/
theorem lswapFilter {A : Type _} (p : A → Bool) (l : List A) (n : Nat) (a b : A) :
    l[n]? = some a → l[n + 1]? = some b → (p a = false ∨ p b = false) →
    (lswap l n).filter p = l.filter p := by
  intro hn hsn hnp
  have hrhs : l.filter p =
      (l.take n).filter p ++ (a :: b :: l.drop (n + 2)).filter p := by
    rw [← List.filter_append, ← lsplit2 l n a b hn hsn]
  rw [hrhs, lswapSplit l n a b hn hsn, List.filter_append]
  rcases hnp with h | h
  · cases hb : p b <;> simp [h, hb]
  · cases ha : p a <;> simp [h, ha]

/-- THE SELF-APPLICATION SHAPE, on the take/drop-free normal form. -/
theorem lswapAppMiddle {A : Type _} (L R : List A) (a b : A) :
    lswap (L ++ a :: b :: R) L.length = L ++ b :: a :: R := by
  have hn : (L ++ a :: b :: R)[L.length]? = some a := list_lookup_middle rfl
  have hsn : (L ++ a :: b :: R)[L.length + 1]? = some b := by
    rw [lookup_app_r (by omega)]
    simp
  rw [lswapSplit _ L.length a b hn hsn]
  simp [List.drop_append]

/-! # 2. `gswap`: the adjacent exchange as a graph transformation

Only `gxGmo` moves; every label-derived notion is unchanged definitionally. -/

def gswap (G : Gexec) (n : Nat) : Gexec :=
  ⟨G.gxImg, G.gxProg, lswap G.gxGmo n⟩

/-! ## 2.1 Everything read off the labels is untouched -/

theorem gswapImg (G : Gexec) (n : Nat) : (gswap G n).gxImg = G.gxImg := rfl
theorem gswapProg (G : Gexec) (n : Nat) : (gswap G n).gxProg = G.gxProg := rfl
theorem gswapGmo (G : Gexec) (n : Nat) : (gswap G n).gxGmo = lswap G.gxGmo n := rfl
theorem gswapLbl (G : Gexec) (n : Nat) : gxLbl (gswap G n) = gxLbl G := rfl
theorem gswapIsW (G : Gexec) (n : Nat) : gisW (gswap G n) = gisW G := rfl
theorem gswapMem (G : Gexec) (n : Nat) : gmem (gswap G n) = gmem G := rfl
theorem gswapLblIs (G : Gexec) (n : Nat) : glblIs (gswap G n) = glblIs G := rfl
theorem gswapWrb (G : Gexec) (n : Nat) : gwritesByte (gswap G n) = gwritesByte G := rfl
theorem gswapRdb (G : Gexec) (n : Nat) : greadsByte (gswap G n) = greadsByte G := rfl
theorem gswapAccesses (G : Gexec) (n : Nat) : gaccesses (gswap G n) = gaccesses G := rfl
theorem gswapPo (G : Gexec) (n : Nat) :
    WeakRvwmoGraph.gpo (gswap G n) = WeakRvwmoGraph.gpo G := rfl
theorem gswapPpo (G : Gexec) (n : Nat) : gppo (gswap G n) = gppo G := rfl

/-! ## 2.2 Membership, `Nodup` and positions -/

theorem gswapElemOf (G : Gexec) (n : Nat) (x r e : Geid) :
    G.gxGmo[n]? = some x → G.gxGmo[n + 1]? = some r →
    (e ∈ (gswap G n).gxGmo ↔ e ∈ G.gxGmo) :=
  fun hx hr => lswapElemOf G.gxGmo n x r e hx hr

theorem gswapNodup (G : Gexec) (n : Nat) (x r : Geid) :
    G.gxGmo[n]? = some x → G.gxGmo[n + 1]? = some r →
    G.gxGmo.Nodup → (gswap G n).gxGmo.Nodup :=
  fun hx hr hnd => lswapNoDup G.gxGmo n x r hx hr hnd

/-- The position law: a member's new position is `sidx` of its old one. -/
theorem gswapGpos (G : Gexec) (n : Nat) (x r e : Geid) :
    G.gxGmo.Nodup → G.gxGmo[n]? = some x → G.gxGmo[n + 1]? = some r →
    e ∈ G.gxGmo → gpos (gswap G n) e = sidx n (gpos G e) := by
  intro hnd hx hr he
  apply gposOfLookup (gswap G n) _ e (gswapNodup G n x r hx hr hnd)
  show (lswap G.gxGmo n)[_]? = _
  rw [lswapLookup _ n x r _ hx hr, sidxInvol]
  exact gposElemLookup G e he

theorem gswapGposLower (G : Gexec) (n : Nat) (x r : Geid) :
    G.gxGmo.Nodup → G.gxGmo[n]? = some x → G.gxGmo[n + 1]? = some r →
    gpos (gswap G n) x = n + 1 := by
  intro hnd hx hr
  rw [gswapGpos G n x r x hnd hx hr (elem_of_list_lookup_2 hx), gposOfLookup G n x hnd hx, sidxN]

theorem gswapGposUpper (G : Gexec) (n : Nat) (x r : Geid) :
    G.gxGmo.Nodup → G.gxGmo[n]? = some x → G.gxGmo[n + 1]? = some r →
    gpos (gswap G n) r = n := by
  intro hnd hx hr
  rw [gswapGpos G n x r r hnd hx hr (elem_of_list_lookup_2 hr),
    gposOfLookup G (n + 1) r hnd hr, sidxSn]

/-! ## 2.3 `gmoLt`: every pair keeps its order, except the swapped one -/

theorem gswapGmoLt (G : Gexec) (n : Nat) (x r e1 e2 : Geid) :
    G.gxGmo.Nodup → G.gxGmo[n]? = some x → G.gxGmo[n + 1]? = some r →
    gmoLt G e1 e2 → ¬ (e1 = x ∧ e2 = r) → gmoLt (gswap G n) e1 e2 := by
  rintro hnd hx hr ⟨h1, h2, hlt⟩ hne
  refine ⟨(gswapElemOf G n x r e1 hx hr).2 h1, (gswapElemOf G n x r e2 hx hr).2 h2, ?_⟩
  rw [gswapGpos G n x r e1 hnd hx hr h1, gswapGpos G n x r e2 hnd hx hr h2]
  apply sidxMono _ _ _ hlt
  rintro ⟨hp1, hp2⟩
  apply hne
  constructor
  · have hl1 := gposElemLookup G e1 h1
    rw [hp1, hx, Option.some.injEq] at hl1
    exact hl1.symm
  · have hl2 := gposElemLookup G e2 h2
    rw [hp2, hr, Option.some.injEq] at hl2
    exact hl2.symm

theorem gswapGmoLtInv (G : Gexec) (n : Nat) (x r e1 e2 : Geid) :
    G.gxGmo.Nodup → G.gxGmo[n]? = some x → G.gxGmo[n + 1]? = some r →
    gmoLt (gswap G n) e1 e2 → gmoLt G e1 e2 ∨ (e1 = r ∧ e2 = x) := by
  rintro hnd hx hr ⟨h1, h2, hlt⟩
  have h1' := (gswapElemOf G n x r e1 hx hr).1 h1
  have h2' := (gswapElemOf G n x r e2 hx hr).1 h2
  rw [gswapGpos G n x r e1 hnd hx hr h1', gswapGpos G n x r e2 hnd hx hr h2'] at hlt
  rcases sidxMonoInv _ _ _ hlt with hp | ⟨hp1, hp2⟩
  · exact .inl ⟨h1', h2', hp⟩
  · refine .inr ⟨?_, ?_⟩
    · have hl1 := gposElemLookup G e1 h1'
      rw [hp1, hr, Option.some.injEq] at hl1
      exact hl1.symm
    · have hl2 := gposElemLookup G e2 h2'
      rw [hp2, hx, Option.some.injEq] at hl2
      exact hl2.symm

/-! ## 2.4 The write sub-order is EQUAL when the upper event is no write -/

theorem gswapGwrites (G : Gexec) (n : Nat) (x r : Geid) :
    G.gxGmo[n]? = some x → G.gxGmo[n + 1]? = some r → gisW G r = false →
    gwrites (gswap G n) = gwrites G := by
  intro hx hr hnw
  show (lswap G.gxGmo n).filter (gisW G) = G.gxGmo.filter (gisW G)
  exact lswapFilter _ _ n x r hx hr (.inr hnw)

theorem gswapGwriteAt (G : Gexec) (n : Nat) (x r : Geid) (t : Nat) :
    G.gxGmo[n]? = some x → G.gxGmo[n + 1]? = some r → gisW G r = false →
    gwriteAt (gswap G n) t = gwriteAt G t := by
  intro hx hr hnw
  cases t with
  | zero => rfl
  | succ i =>
    show (gwrites (gswap G n))[i]? = (gwrites G)[i]?
    rw [gswapGwrites G n x r hx hr hnw]

theorem gswapGwix (G : Gexec) (n : Nat) (x r : Geid) :
    G.gxGmo[n]? = some x → G.gxGmo[n + 1]? = some r → gisW G r = false →
    gwix (gswap G n) = gwix G := by
  intro hx hr hnw
  funext w
  unfold gwix
  rw [gswapGwrites G n x r hx hr hnw]

/-! # 3. THE MAIN LEMMA — the read-down move preserves RVWMO⁻

`r` sits at gmo position `n + 1` and `x` at `n`; `r` moves DOWN past `x`. -/

/-- `r` is a read, for free — W13 (I) (deviation 8): once it is not an I/O-class event (`gwf`
admits `LIo` events, which are in gmo but neither reads nor writes). -/
theorem gswapUpperIsRead (G : Gexec) (r : Geid) :
    gwf G → r ∈ G.gxGmo → gisW G r = false →
    (∀ l, gxLbl G r = some l → lbIsIo l = false) → glblIs G r lbIsR := by
  intro hwf hin hnw hnio
  obtain ⟨l, hl, hm⟩ := gwfGmoMem G r hwf hin
  refine ⟨l, hl, ?_⟩
  simp only [gisW, hl] at hnw
  simp only [lbIsMem, hnw, Bool.or_false, hnio l hl] at hm
  exact hm

theorem gswapReadDown (G : Gexec) (n : Nat) (x r : Geid) :
    rvwmoMinusConsistent G →
    G.gxGmo[n]? = some x →
    G.gxGmo[n + 1]? = some r →
    gisW G r = false →
    (∀ a t v, greadsByte G r a t v → gwriteAt G t ≠ some x) →
    ¬ gppo G x r →
    rvwmoMinusConsistent (gswap G n) := by
  rintro ⟨⟨hnd, hmem, hshape⟩, hppo, hlv, hat⟩ hx hr hnw hnrf hnppo
  refine ⟨⟨gswapNodup G n x r hx hr hnd, ?_, hshape⟩, ?_, ?_, ?_⟩
  · -- gwf
    intro e
    exact (gswapElemOf G n x r e hx hr).trans (hmem e)
  · -- gppo⁻ ⊆ gmo
    intro e1 e2 hp
    exact gswapGmoLt G n x r e1 e2 hnd hx hr (hppo e1 e2 hp)
      (by rintro ⟨rfl, rfl⟩; exact hnppo hp)
  · -- load value
    intro e a t v hrd
    obtain ⟨hsrc, hmax⟩ := hlv e a t v hrd
    refine ⟨?_, ?_⟩
    · cases t with
      | zero => exact hsrc
      | succ t =>
        have hsrc' : ∃ w, gwriteAt G (t + 1) = some w ∧ gwritesByte G w a v ∧ gvisible G w e :=
          hsrc
        obtain ⟨w, hwat, hwb, hvis⟩ := hsrc'
        show ∃ w, gwriteAt (gswap G n) (t + 1) = some w ∧ gwritesByte (gswap G n) w a v ∧
          gvisible (gswap G n) w e
        refine ⟨w, ?_, hwb, ?_⟩
        · rw [gswapGwriteAt G n x r _ hx hr hnw]; exact hwat
        · rcases hvis with hgmo | hpo
          · refine .inl (gswapGmoLt G n x r w e hnd hx hr hgmo ?_)
            rintro ⟨rfl, rfl⟩
            exact hnrf a (t + 1) v hrd hwat
          · exact .inr hpo
    · intro w' v' hwb' hvis'
      rw [gswapGwix G n x r hx hr hnw]
      apply hmax w' v' hwb'
      rcases hvis' with hgmo | hpo
      · rcases gswapGmoLtInv G n x r w' e hnd hx hr hgmo with h | ⟨rfl, rfl⟩
        · exact .inl h
        · exfalso
          rw [WeakRvwmoGraph.gwritesByteGisW G _ a v' hwb'] at hnw
          cases hnw
      · exact .inr hpo
  · -- atomicity
    intro e a t v hrd hw w' v' hwb
    rw [gswapGwix G n x r hx hr hnw]
    exact hat e a t v hrd hw w' v' hwb

/-! ## 3.1 A NON-VACUITY SMOKE TEST

In `lbg`'s gmo `[(0,1), (1,1), (0,0), (1,0)]` the last two events are the two
cross-hart LOADS, so hart 1's load may slide below hart 0's. -/

theorem lbgSwapConsistent : rvwmoMinusConsistent (gswap lbg 2) := by
  refine gswapReadDown lbg 2 (0, 0) (1, 0) lbGraphConsistent rfl rfl rfl ?_ ?_
  · rintro a t v ⟨l, base, ts, vs, j, hl, hrd, ht, hv, ha⟩
    simp only [gxLbl, lbg] at hl
    simp at hl
    subst hl
    simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    rcases j with _ | j <;> simp at ht
    subst ht
    decide
  · intro hppo
    have := gppoSameHart _ _ _ hppo
    simp at this

/-! # 4. The `Gdexec` corollary

`gdepsGmo`'s only risk is the flipped pair — excluded for free, because a dep
edge targets a WRITE and `r` is not one. -/

theorem gswapReadDownDeps (GD : Gdexec) (n : Nat) (x r : Geid) :
    rvwmoMinusDepsConsistent GD →
    GD.gdG.gxGmo[n]? = some x →
    GD.gdG.gxGmo[n + 1]? = some r →
    gisW GD.gdG r = false →
    (∀ a t v, greadsByte GD.gdG r a t v → gwriteAt GD.gdG t ≠ some x) →
    ¬ gppo GD.gdG x r →
    rvwmoMinusDepsConsistent ⟨gswap GD.gdG n, GD.gdDeps⟩ := by
  rintro ⟨hcons, hdwf, hdgmo⟩ hx hr hnw hnrf hnppo
  have hnd := hcons.1.1
  refine ⟨gswapReadDown _ n x r hcons hx hr hnw hnrf hnppo, ?_, ?_⟩
  · intro p hp
    exact hdwf p hp
  · intro p hp
    refine gswapGmoLt GD.gdG n x r _ _ hnd hx hr (hdgmo p hp) ?_
    rintro ⟨_, heq⟩
    obtain ⟨_, _, _, hw⟩ := hdwf p hp
    rw [heq] at hw
    rw [glblIsWGisW _ _ hw] at hnw
    cases hnw

/-! # 5. RULE-14 BOOKKEEPING for the B2 induction's measure

A rule-14 INVERSION of `G` is a pair `(e, w)` with `e` a memory event po-before
the write `w`, but `w` gmo-before `e`. -/

def gviol (G : Gexec) (e w : Geid) : Prop :=
  WeakRvwmoGraph.gpo G e w ∧ gmem G e ∧ glblIs G w lbIsW ∧ gmoLt G w e

theorem gviolGrule14 (G : Gexec) : gwf G → (∀ e w, ¬ gviol G e w) → grule14 G := by
  intro hwf hno e w hpo hme hw
  have hnd := hwf.1
  have hew : e ≠ w := by
    rintro rfl
    exact absurd hpo.2.1 (Nat.lt_irrefl _)
  have hmw : gmem G w := WeakRvwmoGraph.glblIsWGmem G w hw
  rcases gmoLtTotal G e w hnd (gwfMemGmo G e hwf hme) (gwfMemGmo G w hwf hmw) hew with h | h
  · exact h
  · exact absurd ⟨hpo, hme, hw, h⟩ (hno e w)

/-- VIOLATIONS ONLY SHRINK: a read-down swap never creates one. -/
theorem gswapViolMono (G : Gexec) (n : Nat) (x r e w : Geid) :
    G.gxGmo.Nodup → G.gxGmo[n]? = some x → G.gxGmo[n + 1]? = some r →
    gisW G r = false → gviol (gswap G n) e w → gviol G e w := by
  rintro hnd hx hr hnw ⟨hpo, hme, hw, hgmo⟩
  refine ⟨hpo, hme, hw, ?_⟩
  rcases gswapGmoLtInv G n x r w e hnd hx hr hgmo with h | ⟨rfl, rfl⟩
  · exact h
  · rw [glblIsWGisW G _ hw] at hnw
    cases hnw

/-- ... AND THE SWAPPED PAIR'S OWN VIOLATION IS RESOLVED. -/
theorem gswapResolves (G : Gexec) (n : Nat) (x r : Geid) :
    gwf G → G.gxGmo[n]? = some x → G.gxGmo[n + 1]? = some r →
    gisW G r = false → gisW G x = true → r.1 = x.1 → r.2 < x.2 →
    gviol G r x ∧ ¬ gviol (gswap G n) r x := by
  intro hwf hx hr hnw hwx hag hlt
  have hnd := hwf.1
  have hxin := elem_of_list_lookup_2 hx
  have hrin := elem_of_list_lookup_2 hr
  obtain ⟨lx, hlx, _⟩ := gwfGmoMem G x hwf hxin
  obtain ⟨lr, hlr, hmr⟩ := gwfGmoMem G r hwf hrin
  refine ⟨⟨⟨hag, hlt, by simp [hlr], by simp [hlx]⟩, ⟨lr, hlr, hmr⟩,
    ⟨lx, hlx, by simpa [gisW, hlx] using hwx⟩, hxin, hrin, ?_⟩, ?_⟩
  · rw [gposOfLookup G n x hnd hx, gposOfLookup G (n + 1) r hnd hr]
    omega
  · rintro ⟨_, _, _, _, _, hpos⟩
    rw [gswapGposLower G n x r hnd hx hr, gswapGposUpper G n x r hnd hx hr] at hpos
    omega

/-! # 6. B2c — THE WRITE-DOWN MOVE: a write descends past a read

The LOWER event `x` is the non-write and the UPPER event `e` the WRITE.  `x`'s
visible-write set GROWS by exactly `e`, so co-maximality needs one side
condition. -/

/-! ## 6.1 The write sub-order equations, mirrored to a non-write LOWER -/

theorem gswapGwritesLo (G : Gexec) (n : Nat) (x e : Geid) :
    G.gxGmo[n]? = some x → G.gxGmo[n + 1]? = some e → gisW G x = false →
    gwrites (gswap G n) = gwrites G := by
  intro hx he hnw
  show (lswap G.gxGmo n).filter (gisW G) = G.gxGmo.filter (gisW G)
  exact lswapFilter _ _ n x e hx he (.inl hnw)

theorem gswapGwriteAtLo (G : Gexec) (n : Nat) (x e : Geid) (t : Nat) :
    G.gxGmo[n]? = some x → G.gxGmo[n + 1]? = some e → gisW G x = false →
    gwriteAt (gswap G n) t = gwriteAt G t := by
  intro hx he hnw
  cases t with
  | zero => rfl
  | succ i =>
    show (gwrites (gswap G n))[i]? = (gwrites G)[i]?
    rw [gswapGwritesLo G n x e hx he hnw]

theorem gswapGwixLo (G : Gexec) (n : Nat) (x e : Geid) :
    G.gxGmo[n]? = some x → G.gxGmo[n + 1]? = some e → gisW G x = false →
    gwix (gswap G n) = gwix G := by
  intro hx he hnw
  funext w
  unfold gwix
  rw [gswapGwritesLo G n x e hx he hnw]

/-! ## 6.2 The lemma -/

theorem gswapWriteDown (G : Gexec) (n : Nat) (x e : Geid) :
    rvwmoMinusConsistent G →
    G.gxGmo[n]? = some x → G.gxGmo[n + 1]? = some e →
    gisW G x = false → gisW G e = true →
    ¬ gppo G x e →
    -- THE CO-MAX SIDE CONDITION: on every byte both touch, the passed read
    -- already reads at-or-after the descending write
    (∀ a t v, greadsByte G x a t v →
       (∃ v', gwritesByte G e a v') → gwix G e ≤ t) →
    rvwmoMinusConsistent (gswap G n) := by
  rintro ⟨⟨hnd, hmem, hshape⟩, hppo, hlv, hat⟩ hx he hnwx hwe hnppo hcomax
  refine ⟨⟨gswapNodup G n x e hx he hnd, ?_, hshape⟩, ?_, ?_, ?_⟩
  · intro e'
    exact (gswapElemOf G n x e e' hx he).trans (hmem e')
  · intro e1 e2 hp
    exact gswapGmoLt G n x e e1 e2 hnd hx he (hppo e1 e2 hp)
      (by rintro ⟨rfl, rfl⟩; exact hnppo hp)
  · intro e' a t v hrd
    obtain ⟨hsrc, hmax⟩ := hlv e' a t v hrd
    refine ⟨?_, ?_⟩
    · -- the ∃-half: the named source is untouched
      cases t with
      | zero => exact hsrc
      | succ t =>
        have hsrc' : ∃ w, gwriteAt G (t + 1) = some w ∧ gwritesByte G w a v ∧
            gvisible G w e' := hsrc
        obtain ⟨w, hwat, hwb, hvis⟩ := hsrc'
        show ∃ w, gwriteAt (gswap G n) (t + 1) = some w ∧ gwritesByte (gswap G n) w a v ∧
          gvisible (gswap G n) w e'
        refine ⟨w, ?_, hwb, ?_⟩
        · rw [gswapGwriteAtLo G n x e _ hx he hnwx]; exact hwat
        · rcases hvis with hgmo | hpo
          · refine .inl (gswapGmoLt G n x e w e' hnd hx he hgmo ?_)
            rintro ⟨rfl, rfl⟩
            rw [WeakRvwmoGraph.gwritesByteGisW G _ a v hwb] at hnwx
            cases hnwx
          · exact .inr hpo
    · -- the ∀-half: THE side condition's only consumer
      intro w' v' hwb' hvis'
      rw [gswapGwixLo G n x e hx he hnwx]
      rcases hvis' with hgmo | hpo
      · rcases gswapGmoLtInv G n x e w' e' hnd hx he hgmo with h | ⟨rfl, rfl⟩
        · exact hmax w' v' hwb' (.inl h)
        · -- THE NEW VISIBILITY: `e` has descended below the read `x`
          exact hcomax a t v hrd ⟨v', hwb'⟩
      · exact hmax w' v' hwb' (.inr hpo)
  · -- atomicity: every number it mentions is frozen
    intro e' a t v hrd hw w' v' hwb
    rw [gswapGwixLo G n x e hx he hnwx]
    exact hat e' a t v hrd hw w' v' hwb

/-! ## 6.3 The `Gdexec` corollary

UNLIKE §4, the "no dep edge across the swapped pair" side condition is NOT free
here and is HYPOTHESIZED. -/

theorem gswapWriteDownDeps (GD : Gdexec) (n : Nat) (x e : Geid) :
    rvwmoMinusDepsConsistent GD →
    GD.gdG.gxGmo[n]? = some x →
    GD.gdG.gxGmo[n + 1]? = some e →
    gisW GD.gdG x = false →
    gisW GD.gdG e = true →
    ¬ gppo GD.gdG x e →
    (∀ a t v, greadsByte GD.gdG x a t v →
       (∃ v', gwritesByte GD.gdG e a v') → gwix GD.gdG e ≤ t) →
    (x, e) ∉ GD.gdDeps →
    rvwmoMinusDepsConsistent ⟨gswap GD.gdG n, GD.gdDeps⟩ := by
  rintro ⟨hcons, hdwf, hdgmo⟩ hx he hnwx hwe hnppo hcomax hdep
  have hnd := hcons.1.1
  refine ⟨gswapWriteDown _ n x e hcons hx he hnwx hwe hnppo hcomax, ?_, ?_⟩
  · intro p hp
    exact hdwf p hp
  · intro p hp
    refine gswapGmoLt GD.gdG n x e _ _ hnd hx he (hdgmo p hp) ?_
    rintro ⟨h1, h2⟩
    apply hdep
    have hpe : p = (x, e) := Prod.ext h1 h2
    rw [← hpe]
    exact hp

/-! ## 6.4 Violation bookkeeping

The only gmo pair whose order flips is `(x, e)`, so the only violation the move
could CREATE is `(x, e)` itself — excluded by `¬ gpo G x e`. -/

theorem gswapViolMonoRw (G : Gexec) (n : Nat) (x e e' w' : Geid) :
    G.gxGmo.Nodup → G.gxGmo[n]? = some x → G.gxGmo[n + 1]? = some e →
    ¬ WeakRvwmoGraph.gpo G x e → gviol (gswap G n) e' w' → gviol G e' w' := by
  rintro hnd hx he hnpo ⟨hpo, hme, hw, hgmo⟩
  refine ⟨hpo, hme, hw, ?_⟩
  rcases gswapGmoLtInv G n x e w' e' hnd hx he hgmo with h | ⟨rfl, rfl⟩
  · exact h
  · exact absurd hpo hnpo

/-! # 7. THE TRANSPOSITION ARITHMETIC

The renumbering of write indices is an ADJACENT TRANSPOSITION — literally §1.1's
`sidx`, at a different argument. -/

def tswap (k1 : Nat) (t : Nat) : Nat := sidx k1 t

theorem tswapUnfold (k1 t : Nat) :
    tswap k1 t = if t = k1 then k1 + 1 else if t = k1 + 1 then k1 else t := rfl

theorem tswapInvol (k1 t : Nat) : tswap k1 (tswap k1 t) = t := sidxInvol k1 t

theorem tswapInj (k1 t1 t2 : Nat) : tswap k1 t1 = tswap k1 t2 → t1 = t2 := sidxInj k1 t1 t2

theorem tswapLt (k1 a b : Nat) :
    a < b → ¬ (a = k1 ∧ b = k1 + 1) → tswap k1 a < tswap k1 b := sidxMono k1 a b

theorem tswapLtInv (k1 a b : Nat) :
    tswap k1 a < tswap k1 b → a < b ∨ (a = k1 + 1 ∧ b = k1) := sidxMonoInv k1 a b

/-- The ≤ variant — co-maximality's shape.  Same exclusion. -/
theorem tswapLe (k1 a b : Nat) :
    a ≤ b → ¬ (a = k1 ∧ b = k1 + 1) → tswap k1 a ≤ tswap k1 b := by
  intro hle hne
  unfold tswap
  rcases sidxSpec k1 a with h | h | h <;> rcases sidxSpec k1 b with h' | h' | h' <;> omega

/-- `0` is the ERA-INITIAL image and stays put once `k1 ≥ 1`. -/
theorem tswapZero (k1 : Nat) : 0 < k1 → tswap k1 0 = 0 := by
  intro hk
  unfold tswap
  rcases sidxSpec k1 0 with h | h | h <;> omega

theorem tswapEqZero (k1 t : Nat) : 0 < k1 → tswap k1 t = 0 → t = 0 := by
  intro hk
  unfold tswap
  rcases sidxSpec k1 t with h | h | h <;> omega

/-- The successor shift: transposing write indices `m+1`/`m+2` is transposing
LIST positions `m`/`m+1`. -/
theorem tswapS (m i : Nat) : tswap (m + 1) (i + 1) = sidx m i + 1 := by
  unfold tswap
  rcases sidxSpec (m + 1) (i + 1) with h | h | h <;> rcases sidxSpec m i with h' | h' | h' <;> omega

/-! # 8. `gswapw`: the (W,W) exchange, with the `ts`-transposition rewrite -/

def lblTswap (k1 : Nat) (l : Lbl) : Lbl :=
  match l with
  | LLoad aq base ts vs => LLoad aq base (ts.map (tswap k1)) vs
  | LStore rl base vs k => LStore rl base vs k
  | LFence pr pw sr sw => LFence pr pw sr sw
  | LRmw aq rl base ts rvs wvs k => LRmw aq rl base (ts.map (tswap k1)) rvs wvs k
  | LIo kd base vs => LIo kd base vs

/-! ## 8.1 Label-shape stability -/

theorem lblTswapIsR (k1 : Nat) (l : Lbl) : lbIsR (lblTswap k1 l) = lbIsR l := by cases l <;> rfl
theorem lblTswapIsW (k1 : Nat) (l : Lbl) : lbIsW (lblTswap k1 l) = lbIsW l := by cases l <;> rfl
theorem lblTswapIsMem (k1 : Nat) (l : Lbl) : lbIsMem (lblTswap k1 l) = lbIsMem l := by
  cases l <;> rfl
theorem lblTswapAq (k1 : Nat) (l : Lbl) : lbAq (lblTswap k1 l) = lbAq l := by cases l <;> rfl
theorem lblTswapRl (k1 : Nat) (l : Lbl) : lbRl (lblTswap k1 l) = lbRl l := by cases l <;> rfl
theorem lblTswapRcsc (k1 : Nat) (l : Lbl) : lbRcsc (lblTswap k1 l) = lbRcsc l := by
  simp only [lbRcsc, lblTswapAq, lblTswapRl]
theorem lblTswapCls (k1 : Nat) (l : Lbl) : lbCls (lblTswap k1 l) = lbCls l := by cases l <;> rfl
theorem lblTswapWr (k1 : Nat) (l : Lbl) : lbWr (lblTswap k1 l) = lbWr l := by cases l <;> rfl

theorem lblTswapRd (k1 : Nat) (l : Lbl) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    lbRd l = some (base, ts, vs) →
    lbRd (lblTswap k1 l) = some (base, ts.map (tswap k1), vs) := by
  intro h
  cases l <;> simp_all [lblTswap, lbRd]

theorem lblTswapRdInv (k1 : Nat) (l : Lbl) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    lbRd (lblTswap k1 l) = some (base, ts, vs) →
    ∃ ts0, lbRd l = some (base, ts0, vs) ∧ ts = ts0.map (tswap k1) := by
  intro h
  cases l <;> simp only [lblTswap, lbRd, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
  · obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨_, rfl, rfl⟩
  · obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨_, rfl, rfl⟩

theorem lblTswapFence (k1 : Nat) (l : Lbl) (pr pw sr sw : Bool) :
    lblTswap k1 l = LFence pr pw sr sw → l = LFence pr pw sr sw := by
  intro h
  cases l <;> simp_all [lblTswap]

/-! ## 8.2 The transformation -/

def gswapw (G : Gexec) (n k1 : Nat) : Gexec :=
  ⟨G.gxImg, G.gxProg.map (fun row : List Lbl => row.map (lblTswap k1)), lswap G.gxGmo n⟩

/-- The ORDER half of `gswapw` is literally `gswap`'s. -/
theorem gswapwImg (G : Gexec) (n k1 : Nat) : (gswapw G n k1).gxImg = G.gxImg := rfl
theorem gswapwGmo (G : Gexec) (n k1 : Nat) : (gswapw G n k1).gxGmo = (gswap G n).gxGmo := rfl
theorem gswapwGpos (G : Gexec) (n k1 : Nat) : gpos (gswapw G n k1) = gpos (gswap G n) := rfl
theorem gswapwGmoLt (G : Gexec) (n k1 : Nat) : gmoLt (gswapw G n k1) = gmoLt (gswap G n) := rfl

/-! ## 8.3 The label equation, and everything read off it -/

theorem gswapwLbl (G : Gexec) (n k1 : Nat) (e : Geid) :
    gxLbl (gswapw G n k1) e = (gxLbl G e).map (lblTswap k1) := by
  unfold gxLbl gswapw
  simp only [List.getElem?_map]
  cases G.gxProg[e.1]? <;> simp [List.getElem?_map]

theorem gswapwIsW (G : Gexec) (n k1 : Nat) (e : Geid) : gisW (gswapw G n k1) e = gisW G e := by
  unfold gisW
  rw [gswapwLbl]
  cases gxLbl G e <;> simp [lblTswapIsW]

theorem gswapwIsSome (G : Gexec) (n k1 : Nat) (e : Geid) :
    (gxLbl (gswapw G n k1) e).isSome ↔ (gxLbl G e).isSome := by
  rw [gswapwLbl]
  cases gxLbl G e <;> simp

theorem gswapwGlblIs (G : Gexec) (n k1 : Nat) (e : Geid) (P : Lbl → Bool) :
    (∀ l, P (lblTswap k1 l) = P l) →
    (glblIs (gswapw G n k1) e P ↔ glblIs G e P) := by
  intro hP
  unfold glblIs
  rw [gswapwLbl]
  constructor
  · rintro ⟨l, hl, hpl⟩
    obtain ⟨l0, hl0, rfl⟩ := Option.map_eq_some_iff.1 hl
    exact ⟨l0, hl0, by rw [← hP]; exact hpl⟩
  · rintro ⟨l, hl, hpl⟩
    exact ⟨lblTswap k1 l, by simp [hl], by rw [hP]; exact hpl⟩

theorem gswapwMem (G : Gexec) (n k1 : Nat) (e : Geid) : gmem (gswapw G n k1) e ↔ gmem G e :=
  gswapwGlblIs G n k1 e lbIsMem (lblTswapIsMem k1)

theorem gswapwWrb (G : Gexec) (n k1 : Nat) (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte (gswapw G n k1) e a v ↔ gwritesByte G e a v := by
  unfold gwritesByte
  rw [gswapwLbl]
  constructor
  · rintro ⟨l, base, vs, j, hl, hwr, hv, ha⟩
    obtain ⟨l0, hl0, rfl⟩ := Option.map_eq_some_iff.1 hl
    rw [lblTswapWr] at hwr
    exact ⟨l0, base, vs, j, hl0, hwr, hv, ha⟩
  · rintro ⟨l, base, vs, j, hl, hwr, hv, ha⟩
    exact ⟨lblTswap k1 l, base, vs, j, by simp [hl], by rw [lblTswapWr]; exact hwr, hv, ha⟩

/-- THE READ EQUATION: reads survive with their `ts` entries transposed. -/
theorem gswapwRdb (G : Gexec) (n k1 : Nat) (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    greadsByte (gswapw G n k1) e a t v ↔ greadsByte G e a (tswap k1 t) v := by
  unfold greadsByte
  rw [gswapwLbl]
  constructor
  · rintro ⟨l, base, ts, vs, j, hl, hrd, ht, hv, ha⟩
    obtain ⟨l0, hl0, rfl⟩ := Option.map_eq_some_iff.1 hl
    obtain ⟨ts0, hrd0, rfl⟩ := lblTswapRdInv k1 l0 base ts vs hrd
    rw [List.getElem?_map] at ht
    obtain ⟨t0, ht0, rfl⟩ := Option.map_eq_some_iff.1 ht
    rw [tswapInvol]
    exact ⟨l0, base, ts0, vs, j, hl0, hrd0, ht0, hv, ha⟩
  · rintro ⟨l, base, ts, vs, j, hl, hrd, ht, hv, ha⟩
    refine ⟨lblTswap k1 l, base, ts.map (tswap k1), vs, j, by simp [hl],
      lblTswapRd k1 l base ts vs hrd, ?_, hv, ha⟩
    rw [List.getElem?_map, ht]
    simp [tswapInvol]

theorem gswapwAccesses (G : Gexec) (n k1 : Nat) (e : Geid) (a : Int) :
    gaccesses (gswapw G n k1) e a ↔ gaccesses G e a := by
  unfold gaccesses
  constructor
  · rintro (⟨v, hw⟩ | ⟨t, v, hr⟩)
    · exact .inl ⟨v, (gswapwWrb G n k1 e a v).1 hw⟩
    · exact .inr ⟨tswap k1 t, v, (gswapwRdb G n k1 e a t v).1 hr⟩
  · rintro (⟨v, hw⟩ | ⟨t, v, hr⟩)
    · exact .inl ⟨v, (gswapwWrb G n k1 e a v).2 hw⟩
    · refine .inr ⟨tswap k1 t, v, (gswapwRdb G n k1 e a (tswap k1 t) v).2 ?_⟩
      rw [tswapInvol]
      exact hr

/-! ## 8.4 Program order and ppo⁻ are untouched -/

theorem gswapwPo (G : Gexec) (n k1 : Nat) (e1 e2 : Geid) :
    WeakRvwmoGraph.gpo (gswapw G n k1) e1 e2 ↔ WeakRvwmoGraph.gpo G e1 e2 := by
  unfold WeakRvwmoGraph.gpo
  rw [gswapwIsSome G n k1 e1, gswapwIsSome G n k1 e2]

theorem gswapwFenceBetween (G : Gexec) (n k1 : Nat) (e1 e2 : Geid) (pr pw sr sw : Bool) :
    gfenceBetween (gswapw G n k1) e1 e2 pr pw sr sw ↔ gfenceBetween G e1 e2 pr pw sr sw := by
  unfold gfenceBetween
  constructor
  · rintro ⟨hag, hlt, kf, h1, h2, hlf⟩
    rw [gswapwLbl] at hlf
    obtain ⟨l0, hl0, heq⟩ := Option.map_eq_some_iff.1 hlf
    rw [lblTswapFence k1 l0 pr pw sr sw heq] at hl0
    exact ⟨hag, hlt, kf, h1, h2, hl0⟩
  · rintro ⟨hag, hlt, kf, h1, h2, hlf⟩
    exact ⟨hag, hlt, kf, h1, h2, by simp [gswapwLbl, hlf, lblTswap]⟩

theorem gswapwPoloc (G : Gexec) (n k1 : Nat) (e1 e2 : Geid) :
    gpoloc (gswapw G n k1) e1 e2 ↔ gpoloc G e1 e2 := by
  unfold gpoloc
  simp only [gswapwPo, gswapwAccesses]

theorem gswapwFenceCovers (G : Gexec) (n k1 : Nat) (e1 e2 : Geid) :
    gfenceCovers (gswapw G n k1) e1 e2 ↔ gfenceCovers G e1 e2 := by
  have hR := fun e => gswapwGlblIs G n k1 e lbIsR (lblTswapIsR k1)
  have hW := fun e => gswapwGlblIs G n k1 e lbIsW (lblTswapIsW k1)
  unfold gfenceCovers
  simp only [gswapwFenceBetween, hR, hW]

theorem gswapwAcqPo (G : Gexec) (n k1 : Nat) (e1 e2 : Geid) :
    gacqPo (gswapw G n k1) e1 e2 ↔ gacqPo G e1 e2 := by
  have hR := gswapwGlblIs G n k1 e1 lbIsR (lblTswapIsR k1)
  have hA := gswapwGlblIs G n k1 e1 lbAq (lblTswapAq k1)
  unfold gacqPo
  rw [gswapwPo, hR, hA, gswapwMem]

theorem gswapwRelAcq (G : Gexec) (n k1 : Nat) (e1 e2 : Geid) :
    grelAcq (gswapw G n k1) e1 e2 ↔ grelAcq G e1 e2 := by
  have hW := gswapwGlblIs G n k1 e1 lbIsW (lblTswapIsW k1)
  have hL := gswapwGlblIs G n k1 e1 lbRl (lblTswapRl k1)
  have hR := gswapwGlblIs G n k1 e2 lbIsR (lblTswapIsR k1)
  have hA := gswapwGlblIs G n k1 e2 lbAq (lblTswapAq k1)
  unfold grelAcq
  rw [gswapwPo, hW, hL, hR, hA]

theorem gswapwRcsc (G : Gexec) (n k1 : Nat) (e1 e2 : Geid) :
    grcsc (gswapw G n k1) e1 e2 ↔ grcsc G e1 e2 := by
  have h1 := gswapwGlblIs G n k1 e1 lbRcsc (lblTswapRcsc k1)
  have h2 := gswapwGlblIs G n k1 e2 lbRcsc (lblTswapRcsc k1)
  unfold grcsc
  rw [gswapwPo, h1, h2]

theorem gswapwPpo (G : Gexec) (n k1 : Nat) (e1 e2 : Geid) :
    gppo (gswapw G n k1) e1 e2 ↔ gppo G e1 e2 := by
  unfold gppo
  rw [gswapwPoloc, gswapwFenceCovers, gswapwAcqPo, gswapwRcsc]

/-! ## 8.5 THE WRITE SUB-ORDER SWAPS TOO — the §1 kit, self-applied -/

theorem gswapwWritesKit (G : Gexec) (n k1 : Nat) (x e : Geid) :
    G.gxGmo.Nodup →
    G.gxGmo[n]? = some x → G.gxGmo[n + 1]? = some e →
    gisW G x = true → gisW G e = true →
    ∃ m, (gwrites G)[m]? = some x ∧ (gwrites G)[m + 1]? = some e ∧
      gwix G x = m + 1 ∧ gwix G e = m + 1 + 1 ∧
      gwrites (gswapw G n k1) = lswap (gwrites G) m := by
  intro hnd hx he hwx hwe
  have hfilt : gisW (gswapw G n k1) = gisW G := funext (gswapwIsW G n k1)
  have hsplit : ∃ L R, gwrites G = L ++ x :: e :: R ∧
      gwrites (gswapw G n k1) = L ++ e :: x :: R := by
    refine ⟨(G.gxGmo.take n).filter (gisW G), (G.gxGmo.drop (n + 2)).filter (gisW G), ?_, ?_⟩
    · have h := congrArg (List.filter (gisW G)) (lsplit2 G.gxGmo n x e hx he)
      unfold gwrites
      rw [h]
      simp [List.filter_append, hwx, hwe]
    · unfold gwrites
      rw [hfilt]
      show (lswap G.gxGmo n).filter (gisW G) = _
      rw [lswapSplit G.gxGmo n x e hx he]
      simp [List.filter_append, hwx, hwe]
  obtain ⟨L, R, h1, h2⟩ := hsplit
  have hm : (gwrites G)[L.length]? = some x := by
    rw [h1]
    exact list_lookup_middle rfl
  have hsm : (gwrites G)[L.length + 1]? = some e := by
    rw [h1, lookup_app_r (by omega)]
    simp
  refine ⟨L.length, hm, hsm, gwixOfLookup G _ x hnd hm, gwixOfLookup G _ e hnd hsm, ?_⟩
  rw [h2, h1, lswapAppMiddle]

/-- ADJACENCY, standalone: two gmo-adjacent writes have consecutive indices. -/
theorem gwixAdjacent (G : Gexec) (n : Nat) (x e : Geid) :
    G.gxGmo.Nodup →
    G.gxGmo[n]? = some x → G.gxGmo[n + 1]? = some e →
    gisW G x = true → gisW G e = true →
    gwix G e = gwix G x + 1 := by
  intro hnd hx he hwx hwe
  obtain ⟨m, _, _, hkx, hke, _⟩ := gswapwWritesKit G n 0 x e hnd hx he hwx hwe
  rw [hke, hkx]

/-! ## 8.6 THE KEY EQUATIONS: write indices are renumbered by `tswap`

(Rocq's `Section gswapw_wix`, flattened — deviation 5.) -/

theorem gswapwGwritesLookup (G : Gexec) (n : Nat) (x e : Geid) (m : Nat)
    (hm : (gwrites G)[m]? = some x) (hsm : (gwrites G)[m + 1]? = some e)
    (hgws : gwrites (gswapw G n (m + 1)) = lswap (gwrites G) m) (i : Nat) :
    (gwrites (gswapw G n (m + 1)))[i]? = (gwrites G)[sidx m i]? := by
  rw [hgws]
  exact lswapLookup _ m x e i hm hsm

theorem gswapwGwriteAt (G : Gexec) (n : Nat) (x e : Geid) (m : Nat)
    (hm : (gwrites G)[m]? = some x) (hsm : (gwrites G)[m + 1]? = some e)
    (hgws : gwrites (gswapw G n (m + 1)) = lswap (gwrites G) m) (t : Nat) :
    gwriteAt (gswapw G n (m + 1)) t = gwriteAt G (tswap (m + 1) t) := by
  cases t with
  | zero =>
    rw [tswapZero (m + 1) (by omega)]
    rfl
  | succ i =>
    rw [tswapS]
    exact gswapwGwritesLookup G n x e m hm hsm hgws i

theorem gswapwNodup' (G : Gexec) (n : Nat) (x e : Geid) (m : Nat)
    (hnd : G.gxGmo.Nodup) (hx : G.gxGmo[n]? = some x) (he : G.gxGmo[n + 1]? = some e) :
    (gswapw G n (m + 1)).gxGmo.Nodup :=
  gswapNodup G n x e hx he hnd

theorem gswapwGwix (G : Gexec) (n : Nat) (x e : Geid) (m : Nat)
    (hnd : G.gxGmo.Nodup) (hx : G.gxGmo[n]? = some x) (he : G.gxGmo[n + 1]? = some e)
    (hm : (gwrites G)[m]? = some x) (hsm : (gwrites G)[m + 1]? = some e)
    (hgws : gwrites (gswapw G n (m + 1)) = lswap (gwrites G) m) (w : Geid) :
    gwix (gswapw G n (m + 1)) w = tswap (m + 1) (gwix G w) := by
  by_cases hin : w ∈ gwrites G
  · obtain ⟨i, hi, hw⟩ := gwixLookup G w hin
    rw [hw, tswapS]
    apply gwixOfLookup _ _ _ (gswapwNodup' G n x e m hnd hx he)
    rw [gswapwGwritesLookup G n x e m hm hsm hgws, sidxInvol]
    exact hi
  · rw [gwixZero G w hin, tswapZero (m + 1) (by omega)]
    apply gwixZero
    intro hin'
    apply hin
    rw [gwritesElemOf] at hin' ⊢
    obtain ⟨h1, h2⟩ := hin'
    rw [gswapwIsW] at h2
    exact ⟨(gswapElemOf G n x e w hx he).1 h1, h2⟩

/-! # 9. B2b — THE (W,W) EXCHANGE, byte-disjoint

Every numeric comparison `gloadValue` and `gatomicity` make is between `ts`
entries and `gwix` values renumbered by the SAME adjacent transposition, which
preserves every inequality EXCEPT one between the transposed pair itself —
excluded by BYTE-DISJOINTNESS (which also covers the fused-RMW read halves, via
`greadByteWriteByte`). -/

theorem gswapwWw (G : Gexec) (n : Nat) (x e : Geid) :
    rvwmoMinusConsistent G →
    G.gxGmo[n]? = some x → G.gxGmo[n + 1]? = some e →
    gisW G x = true → gisW G e = true →
    -- byte-disjoint (this also covers the RMW read halves)
    (∀ a, (∃ v, gwritesByte G x a v) → ¬ ∃ v', gwritesByte G e a v') →
    ¬ gppo G x e →
    rvwmoMinusConsistent (gswapw G n (gwix G x)) := by
  rintro ⟨hwf, hppo, hlv, hat⟩ hx he hwx hwe hdisj hnppo
  obtain ⟨hnd, hmem, hshape⟩ := hwf
  obtain ⟨m, hm, hsm, hkx, hke, hgws⟩ := gswapwWritesKit G n (gwix G x) x e hnd hx he hwx hwe
  rw [hkx] at hgws ⊢
  have hgwat := gswapwGwriteAt G n x e m hm hsm hgws
  have hgwix := gswapwGwix G n x e m hnd hx he hm hsm hgws
  have hxin : x ∈ gwrites G := (gwritesElemOf G x).2 ⟨elem_of_list_lookup_2 hx, hwx⟩
  have hein : e ∈ gwrites G := (gwritesElemOf G e).2 ⟨elem_of_list_lookup_2 he, hwe⟩
  -- THE THREE BYTE-DISJOINTNESS COROLLARIES
  have hxrd : ∀ a t v, greadsByte G x a t v → ¬ ∃ v', gwritesByte G e a v' := by
    intro a t v hrd
    obtain ⟨v2, hv2⟩ := greadByteWriteByte G x a t v ⟨hnd, hmem, hshape⟩ hwx hrd
    exact hdisj a ⟨v2, hv2⟩
  have herd : ∀ a t v, greadsByte G e a t v → ¬ ∃ v', gwritesByte G x a v' := by
    rintro a t v hrd ⟨v', hv'⟩
    obtain ⟨v2, hv2⟩ := greadByteWriteByte G e a t v ⟨hnd, hmem, hshape⟩ hwe hrd
    exact hdisj a ⟨v', hv'⟩ ⟨v2, hv2⟩
  have hrde : ∀ e' a v, greadsByte G e' a (gwix G e) v → gwritesByte G e a v := by
    intro e' a v hrd
    exact greadSourceByte G e' a _ v e hlv hrd (gwriteAtGwix G e hein)
  refine ⟨⟨gswapwNodup' G n x e m hnd hx he, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- gwf: membership
    intro e'
    rw [gswapwMem G n (m + 1) e']
    exact (gswapElemOf G n x e e' hx he).trans (hmem e')
  · -- gwf: shapes
    intro i p' k l' hp' hk'
    simp only [gswapw, List.getElem?_map] at hp'
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 hp'
    rw [List.getElem?_map] at hk'
    obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 hk'
    have hsh := hshape i p k l hp hl
    cases l <;> simp only [lblTswap, List.length_map] at hsh ⊢ <;> exact hsh
  · -- gppo⁻ ⊆ gmo
    intro e1 e2 hp
    have hp0 := (gswapwPpo G n (m + 1) e1 e2).1 hp
    rw [gswapwGmoLt]
    exact gswapGmoLt G n x e e1 e2 hnd hx he (hppo e1 e2 hp0)
      (by rintro ⟨rfl, rfl⟩; exact hnppo hp0)
  · -- load value
    intro e' a t v hrd
    have hrd0 := (gswapwRdb G n (m + 1) e' a t v).1 hrd
    obtain ⟨hsrc, hmax⟩ := hlv e' a (tswap (m + 1) t) v hrd0
    refine ⟨?_, ?_⟩
    · -- the ∃-half: the source moves WITH the renumbering
      cases t with
      | zero =>
        rw [tswapZero (m + 1) (by omega)] at hsrc
        exact hsrc
      | succ i =>
        rw [tswapS] at hsrc
        have hsrc' : ∃ w, gwriteAt G (sidx m i + 1) = some w ∧ gwritesByte G w a v ∧
            gvisible G w e' := hsrc
        obtain ⟨w, hwat, hwb, hvis⟩ := hsrc'
        show ∃ w, gwriteAt (gswapw G n (m + 1)) (i + 1) = some w ∧
          gwritesByte (gswapw G n (m + 1)) w a v ∧ gvisible (gswapw G n (m + 1)) w e'
        refine ⟨w, ?_, (gswapwWrb G n (m + 1) w a v).2 hwb, ?_⟩
        · rw [hgwat, tswapS]
          exact hwat
        · rcases hvis with hgmo | hpo
          · left
            rw [gswapwGmoLt]
            refine gswapGmoLt G n x e w e' hnd hx he hgmo ?_
            -- `e` would have to read `x` — byte-disjoint
            rintro ⟨rfl, rfl⟩
            exact herd a _ v hrd0 ⟨v, hwb⟩
          · exact .inr ((gswapwPo G n (m + 1) w e').2 hpo)
    · -- the ∀-half: co-maximality, transported by `tswapLe`
      intro w' v' hwb' hvis'
      have hwb0 := (gswapwWrb G n (m + 1) w' a v').1 hwb'
      have hle : tswap (m + 1) (gwix G w') ≤ tswap (m + 1) (tswap (m + 1) t) := by
        apply tswapLe
        · apply hmax w' v' hwb0
          rcases hvis' with hgmo | hpo
          · rw [gswapwGmoLt] at hgmo
            rcases gswapGmoLtInv G n x e w' e' hnd hx he hgmo with h | ⟨rfl, rfl⟩
            · exact .inl h
            · -- the NEW visibility `(e, x)` — vacuous
              exact absurd ⟨v', hwb0⟩ (hxrd a _ v hrd0)
          · exact .inr ((gswapwPo G n (m + 1) w' e').1 hpo)
        · -- THE TRANSPOSED PAIR: `w' = x` AND the read names `e`
          rintro ⟨hw'k, htk⟩
          have hw'in : w' ∈ gwrites G := gwixElem G w' (by rw [hw'k]; omega)
          have hw'x : w' = x := gwixInj G w' x hnd hw'in hxin (by rw [hw'k, hkx])
          subst hw'x
          exact hdisj a ⟨v', hwb0⟩ ⟨v, hrde e' a v (by rw [hke, ← htk]; exact hrd0)⟩
      rw [tswapInvol] at hle
      rw [hgwix]
      exact hle
  · -- atomicity
    intro e' a t v hrd hw w' v' hwb
    have hrd0 := (gswapwRdb G n (m + 1) e' a t v).1 hrd
    have hw0 := (gswapwGlblIs G n (m + 1) e' lbIsW (lblTswapIsW (m + 1))).1 hw
    have hwb0 := (gswapwWrb G n (m + 1) w' a v').1 hwb
    rw [hgwix, hgwix]
    rintro ⟨h1, h2⟩
    have h1' : tswap (m + 1) (tswap (m + 1) t) < tswap (m + 1) (gwix G w') := by
      rw [tswapInvol]; exact h1
    rcases tswapLtInv _ _ _ h1' with hlt1 | ⟨ha1, hb1⟩ <;>
      rcases tswapLtInv _ _ _ h2 with hlt2 | ⟨ha2, hb2⟩
    · -- both comparisons survive: `G`'s own atomicity refutes it
      exact hat e' a (tswap (m + 1) t) v hrd0 hw0 w' v' hwb0 ⟨hlt1, hlt2⟩
    · -- `w' = e` co-between and `e' = x` the RMW — same byte, excluded
      have hw'in : w' ∈ gwrites G := gwixElem G w' (by rw [ha2]; omega)
      have he'in : e' ∈ gwrites G := gwixElem G e' (by rw [hb2]; omega)
      have hw'e : w' = e := gwixInj G w' e hnd hw'in hein (by rw [ha2, hke])
      have he'x : e' = x := gwixInj G e' x hnd he'in hxin (by rw [hb2, hkx])
      subst hw'e he'x
      exact hxrd a _ v hrd0 ⟨v', hwb0⟩
    · -- the read names `e` and `w' = x` — same byte, excluded
      have hw'in : w' ∈ gwrites G := gwixElem G w' (by rw [hb1]; omega)
      have hw'x : w' = x := gwixInj G w' x hnd hw'in hxin (by rw [hb1, hkx])
      subst hw'x
      exact hdisj a ⟨v', hwb0⟩ ⟨v, hrde e' a v (by rw [hke, ← ha1]; exact hrd0)⟩
    · omega

/-! ## 9.1 The `Gdexec` corollary

FLAGGED (as in Rocq): the "no dep edge across the swapped pair" condition is
HYPOTHESIZED — an `LRmw` is a write AND a read, so `(x, e)` with `x` an RMW and
`e` a po-later same-hart store is a well-formed dep edge. -/

theorem gswapwWwDeps (GD : Gdexec) (n : Nat) (x e : Geid) :
    rvwmoMinusDepsConsistent GD →
    GD.gdG.gxGmo[n]? = some x →
    GD.gdG.gxGmo[n + 1]? = some e →
    gisW GD.gdG x = true → gisW GD.gdG e = true →
    (∀ a, (∃ v, gwritesByte GD.gdG x a v) → ¬ ∃ v', gwritesByte GD.gdG e a v') →
    ¬ gppo GD.gdG x e →
    (x, e) ∉ GD.gdDeps →
    rvwmoMinusDepsConsistent ⟨gswapw GD.gdG n (gwix GD.gdG x), GD.gdDeps⟩ := by
  rintro ⟨hcons, hdwf, hdgmo⟩ hx he hwx hwe hdisj hnppo hdep
  have hnd := hcons.1.1
  refine ⟨gswapwWw _ n x e hcons hx he hwx hwe hdisj hnppo, ?_, ?_⟩
  · intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hdwf p hp
    exact ⟨h1, h2, (gswapwGlblIs _ n _ p.1 lbIsR (lblTswapIsR _)).2 h3,
      (gswapwGlblIs _ n _ p.2 lbIsW (lblTswapIsW _)).2 h4⟩
  · intro p hp
    show gmoLt (gswapw GD.gdG n (gwix GD.gdG x)) p.1 p.2
    rw [gswapwGmoLt]
    refine gswapGmoLt GD.gdG n x e _ _ hnd hx he (hdgmo p hp) ?_
    rintro ⟨h1, h2⟩
    apply hdep
    have hpe : p = (x, e) := Prod.ext h1 h2
    rw [← hpe]
    exact hp

/-! # 10. RULE-14 BOOKKEEPING for the (W,W) move -/

theorem gswapwViolMono (G : Gexec) (n k1 : Nat) (x e e' w' : Geid) :
    G.gxGmo.Nodup → G.gxGmo[n]? = some x → G.gxGmo[n + 1]? = some e →
    ¬ WeakRvwmoGraph.gpo G x e → gviol (gswapw G n k1) e' w' → gviol G e' w' := by
  rintro hnd hx he hnpo ⟨hpo, hme, hw, hgmo⟩
  have hpo0 := (gswapwPo G n k1 e' w').1 hpo
  have hme0 := (gswapwMem G n k1 e').1 hme
  have hw0 := (gswapwGlblIs G n k1 w' lbIsW (lblTswapIsW k1)).1 hw
  rw [gswapwGmoLt] at hgmo
  refine ⟨hpo0, hme0, hw0, ?_⟩
  rcases gswapGmoLtInv G n x e w' e' hnd hx he hgmo with h | ⟨rfl, rfl⟩
  · exact h
  · exact absurd hpo0 hnpo

/-- ... AND THE SWAPPED PAIR'S OWN VIOLATION IS RESOLVED, in the resolving
orientation: the UPPER event `e` is po-BEFORE the lower write `x`. -/
theorem gswapwResolves (G : Gexec) (n : Nat) (x e : Geid) :
    gwf G → G.gxGmo[n]? = some x → G.gxGmo[n + 1]? = some e →
    gisW G x = true → gisW G e = true → e.1 = x.1 → e.2 < x.2 →
    gviol G e x ∧ ¬ gviol (gswapw G n (gwix G x)) e x := by
  intro hwf hx he hwx hwe hag hlt
  have hnd := hwf.1
  have hxin := elem_of_list_lookup_2 hx
  have hein := elem_of_list_lookup_2 he
  obtain ⟨lx, hlx, _⟩ := gwfGmoMem G x hwf hxin
  obtain ⟨le, hle, hme⟩ := gwfGmoMem G e hwf hein
  refine ⟨⟨⟨hag, hlt, by simp [hle], by simp [hlx]⟩, ⟨le, hle, hme⟩,
    ⟨lx, hlx, by simpa [gisW, hlx] using hwx⟩, hxin, hein, ?_⟩, ?_⟩
  · rw [gposOfLookup G n x hnd hx, gposOfLookup G (n + 1) e hnd he]
    omega
  · rintro ⟨_, _, _, _, _, hpos⟩
    rw [gswapwGpos, gswapGposLower G n x e hnd hx he, gswapGposUpper G n x e hnd hx he] at hpos
    omega

/-! ## 10.1 A NON-VACUITY SMOKE TEST for the (W,W) move

`lbg`'s gmo opens with the two STORES, byte-disjoint (hart 0 stores byte 8,
hart 1 stores byte 0), so they may be exchanged. -/

theorem lbgSwapwConsistent :
    rvwmoMinusConsistent (gswapw lbg 0 (gwix lbg (0, 1))) := by
  refine gswapwWw lbg 0 (0, 1) (1, 1) lbGraphConsistent rfl rfl rfl rfl ?_ ?_
  · rintro a ⟨v, hv⟩ ⟨v', hv'⟩
    rcases lbgWr _ _ _ hv with ⟨_, ha⟩ | ⟨hb, _⟩
    · rcases lbgWr _ _ _ hv' with ⟨hb, _⟩ | ⟨_, ha'⟩
      · simp at hb
      · rw [ha] at ha'
        omega
    · simp at hb
  · intro hppo
    have := gppoSameHart _ _ _ hppo
    simp at this

end Weak
