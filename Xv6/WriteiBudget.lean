/-
**THE LOG BUDGET'S AMORTISED LEDGER**, ported from section 6
(`Section LogAmort`) of `/shared/xv6rocq/iris/WriteiBudget.v`.

**SCOPE: THE `logAmort` FAMILY AND NOTHING ELSE.**  `WriteiBudget.v` has
eleven sections; ten of them (`FW_MAX`, `wi_cost*`, `bm_iter_cost`,
`bm_pot`, `wi_inv_bud` / `wi_inv_spent` / `wi_step_alloc` / `wi_inv_exit`,
`wi_fset`, `wi_logset`, `wi_ad_of_alloced`) are stated over
`SpecWritei.wi_blocks`, `SpecBmap.bmap_cost`, `BitmapInv.bitmap_geom_ok`
and `InodeInv.blkmap`, none of which this port has yet, so they land with
`writei` (wave 5).  Section 6 needs NOTHING but the log's own ledger
fragment, which is already here (`Xv6.logOpS`, `logOpb`, `logOpS_opb`,
`logOpS_timeless` in `Xv6/LogInv.lean`), so it lands now.  `log_amort` /
`wi_amort` are referenced by no other Rocq file -- they are the parked
"two-credit day" machinery -- so nothing downstream waits on this.

**WHAT IT IS FOR.**  "`u` units are genuinely free, and one unit is still
held back for each block of `F` this op has not yet logged."  `v` is the
op's real remaining budget and `Sb` its real already-logged set; both are
existential, because no caller can know either.  The potential
`u + unpaid F Sb` is what stays put across a `log_write` of a block of
`F`, which is what makes a loop invariant possible.

**IDEMPOTENCE, AND WHERE IT IS CASHED.**  `logAmort_present` is
IDEMPOTENT -- `u` is the same going in and coming out, whichever arm of the
write runs -- and that is the whole point of the amortisation: with every
`log_write` spending a unit, `itrunc`'s 269 `bfree`s would cost 269
against `MAXOPBLOCKS = 10`.  It is cashed by `log_write`'s CREDITED arm:
`Xv6.LOG_WRITE.wp_log_write_gen` takes exactly the
`⌜cr = true → b ∈ Sb⌝ ∗ logOpS γ (v + 1) Sb` this lemma hands out and
returns the `logOpS γ (if cr then v + 1 else v) (b :: Sb)` its wand takes
back; the atomic-update form `wp_log_write_au` does the same at the
epoch-named entry (`Xv6.logOpS_named`, `Xv6.logCredit_own`,
`Xv6.logOpSwe_opSe`, `Xv6.logOpSe_opS`).

**DEVIATIONS from Rocq, all forced by the port's standing `gset Z` →
`List Nat` deviation (`Xv6/LogDefs.lean`).**

1. **THE POTENTIAL COUNTS UNPAID MEMBERS, NOT A SET DIFFERENCE'S
   CARDINALITY.**  Rocq's `log_amort` uses `size (F ∖ Sb)`.  Here
   `Sb : List Nat` is NOT deduplicated -- `Xv6.logSpendStep` and
   `logRecordStep` both produce `b :: Sb` unconditionally -- so
   `unpaid F Sb` counts the members of `F` that are not in `Sb`, which is
   well defined for a duplicated `Sb` and agrees with Rocq's whenever `F`
   is duplicate-free (which every call site's `F` is: `[bmapstart, ind]`).
2. **`logAmort_intro` TAKES `u + F.length ≤ v`** where Rocq takes
   `u + size F ≤ v`.  `size F ≤ length F` for a list-as-set, so this is a
   STRONGER premise and the lemma is weaker; `wiAmort_intro`, the only
   consumer, supplies `2 = [bms, ind].length` either way.
3. **`logAmort_shrink` TAKES `F'.Sublist F`** where Rocq takes `F' ⊆ F`.
   With bare membership the cardinality claim is FALSE (`F'` may duplicate
   a member of `F`), and every call site -- writei's loop drops the
   indirect block from `[bmapstart, ind]` -- supplies a sublist.
4. **`Sb ∪ {[b]}` IS `b :: Sb`** and `{[x]} ∪ F` is `x :: F`, which is
   exactly what the ledger's own steps produce; **`Sb ⊆ Sb'` is
   `∀ x ∈ Sb, x ∈ Sb'`**, the shape `logOpSw`'s consumers already use.
5. `S u` is `u + 1` and `S (S u)` is `u + 2`, the port's arithmetic
   spelling.
-/
import Xv6.LogInv

namespace Xv6

open Iris Iris.BI Iris.ProofMode MachCSL

set_option linter.unusedSectionVars false

/-! ## The potential, as list arithmetic

None of this exists in the tree; it is all pure `List`/`omega`. -/

/-- The members of `F` this op has not yet logged (Rocq's
`size (F ∖ Sb)`; deviation 1). -/
def unpaid (F Sb : List Nat) : Nat := (F.filter (fun x => decide (x ∉ Sb))).length

theorem unpaid_nil (Sb : List Nat) : unpaid [] Sb = 0 := rfl

theorem unpaid_le (F Sb : List Nat) : unpaid F Sb ≤ F.length :=
  List.length_filter_le _ _

/-- Logging more can only shrink the held-back term. -/
theorem unpaid_mono (F Sb Sb' : List Nat) (h : ∀ x ∈ Sb, x ∈ Sb') :
    unpaid F Sb' ≤ unpaid F Sb := by
  induction F with
  | nil => exact Nat.le_refl 0
  | cons a F ih =>
    unfold unpaid at *
    by_cases ha' : a ∈ Sb'
    · rw [List.filter_cons_of_neg (by simp [ha'])]
      by_cases ha : a ∈ Sb
      · rw [List.filter_cons_of_neg (by simp [ha])]; exact ih
      · rw [List.filter_cons_of_pos (by simp [ha]), List.length_cons]; omega
    · have ha : a ∉ Sb := fun hc => ha' (h a hc)
      rw [List.filter_cons_of_pos (by simp [ha']), List.filter_cons_of_pos (by simp [ha]),
        List.length_cons, List.length_cons]
      omega

/-- A block of `F` that was NOT paid for drops the potential by at least
one -- the STRICT drop, and no `Nodup` is needed for it. -/
theorem unpaid_cons_hit (F Sb : List Nat) (b : Nat) (hb : b ∈ F) (hn : b ∉ Sb) :
    unpaid F (b :: Sb) + 1 ≤ unpaid F Sb := by
  induction F with
  | nil => cases hb
  | cons a F ih =>
    unfold unpaid at *
    by_cases hab : a = b
    · subst hab
      rw [List.filter_cons_of_neg (by simp), List.filter_cons_of_pos (by simp [hn]),
        List.length_cons]
      have := unpaid_mono F Sb (a :: Sb) (fun x hx => List.mem_cons_of_mem a hx)
      unfold unpaid at this
      omega
    · have hbF : b ∈ F := by
        rcases List.mem_cons.1 hb with h | h
        · exact absurd h.symm hab
        · exact h
      have ihh := ih hbF
      by_cases ha : a ∈ Sb
      · rw [List.filter_cons_of_neg (by simp [ha]),
          List.filter_cons_of_neg (by simp; exact ha)]
        exact ihh
      · rw [List.filter_cons_of_pos (by simp [ha]; exact hab),
          List.filter_cons_of_pos (by simp [ha]), List.length_cons, List.length_cons]
        omega

/-- A block already paid for leaves the potential alone. -/
theorem unpaid_cons_paid (F Sb : List Nat) (b : Nat) (hb : b ∈ Sb) :
    unpaid F (b :: Sb) = unpaid F Sb := by
  unfold unpaid
  congr 1
  refine List.filter_congr (fun x _ => ?_)
  by_cases hx : x ∈ Sb
  · simp [hx, List.mem_cons_of_mem b hx]
  · have : x ≠ b := fun hc => hx (hc ▸ hb)
    simp [hx, this]

/-- Enlarging `F` costs at most one. -/
theorem unpaid_grow (F Sb : List Nat) (x : Nat) : unpaid (x :: F) Sb ≤ 1 + unpaid F Sb := by
  unfold unpaid
  by_cases hx : x ∈ Sb
  · rw [List.filter_cons_of_neg (by simp [hx])]; omega
  · rw [List.filter_cons_of_pos (by simp [hx]), List.length_cons]; omega

/-- ...and a member ALREADY LOGGED costs nothing (what `logAmort_adopt`
reads). -/
theorem unpaid_cons_mem (F Sb : List Nat) (b : Nat) (hb : b ∈ Sb) :
    unpaid (b :: F) Sb = unpaid F Sb := by
  unfold unpaid; rw [List.filter_cons_of_neg (by simp [hb])]

/-- Reserving fewer blocks is weaker (deviation 3). -/
theorem unpaid_sublist (F F' Sb : List Nat) (h : F'.Sublist F) :
    unpaid F' Sb ≤ unpaid F Sb :=
  (h.filter _).length_le

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [LogG GF]

/-! ## The ledger algebra -/

/-- Rocq's `log_amort`. -/
def logAmort (γ : LogNames) (F : List Nat) (u : Nat) : IProp GF :=
  iprop(∃ (Sb : List Nat) (v : Nat), ⌜u + unpaid F Sb ≤ v⌝ ∗ logOpS γ v Sb)

instance logAmort_timeless (γ : LogNames) (F : List Nat) (u : Nat) :
    Timeless (logAmort (GF := GF) γ F u) := by unfold logAmort; infer_instance

/-- ENTERING: a caller with `u + |F|` units in hand and no credits at all
can reserve `F`.  This is the worst case -- every block of `F` still to be
paid for (deviation 2). -/
theorem logAmort_intro (γ : LogNames) (F : List Nat) (u v : Nat) (hv : u + F.length ≤ v) :
    logOpb (GF := GF) γ v ⊢ logAmort γ F u := by
  unfold logOpb logAmort
  iintro ⟨%Sb, H⟩
  iexists Sb, v
  isplitr [H]
  · ipureintro
    have := unpaid_le F Sb
    omega
  · iexact H

/-- LEAVING: at least the `u` free units are really there.  A callee that
wants the counted form (`iupdate`, `end_op`) takes this. -/
theorem logAmort_elim (γ : LogNames) (F : List Nat) (u : Nat) :
    logAmort (GF := GF) γ F u ⊢ ∃ v : Nat, ⌜u ≤ v⌝ ∗ logOpb γ v := by
  unfold logAmort
  iintro ⟨%Sb, %v, %hv, H⟩
  iexists v
  isplitr [H]
  · ipureintro; omega
  · iapply logOpS_opb γ v Sb
    iexact H

/-- Fewer free units is weaker. -/
theorem logAmort_weaken (γ : LogNames) (F : List Nat) (u u' : Nat) (hu : u' ≤ u) :
    logAmort (GF := GF) γ F u ⊢ logAmort γ F u' := by
  unfold logAmort
  iintro ⟨%Sb, %v, %hv, H⟩
  iexists Sb, v
  isplitr [H]
  · ipureintro; omega
  · iexact H

/-- ...and RESERVING FEWER BLOCKS is weaker (`F` is capacity held back,
not a claim; deviation 3). -/
theorem logAmort_shrink (γ : LogNames) (F F' : List Nat) (u : Nat) (hF : F'.Sublist F) :
    logAmort (GF := GF) γ F u ⊢ logAmort γ F' u := by
  unfold logAmort
  iintro ⟨%Sb, %v, %hv, H⟩
  iexists Sb, v
  isplitr [H]
  · ipureintro
    have := unpaid_sublist F F' Sb hF
    omega
  · iexact H

/-- **PRESENTING A BLOCK OF `F` to `log_write`.  IDEMPOTENT**: `u` is the
same on the way in and on the way out, whichever arm runs.

* the block is already logged (`b ∈ Sb`): the credited arm absorbs and the
  unit comes back, so the potential cannot have moved;
* it is not: the uncredited arm spends the unit, but `b` joins `Sb` and the
  held-back term drops by exactly one.

The `u + 1` shape is what guarantees `log_write`'s own "a unit must be in
hand either way" premise is satisfiable even when every block of `F` is
already paid for. -/
theorem logAmort_present (γ : LogNames) (F : List Nat) (u b : Nat) (hbF : b ∈ F) :
    logAmort (GF := GF) γ F (u + 1) ⊢
      ∃ (Sb : List Nat) (v : Nat) (cr : Bool),
        ⌜cr = true → b ∈ Sb⌝ ∗ logOpS γ (v + 1) Sb ∗
        (logOpS γ (if cr then v + 1 else v) (b :: Sb) -∗ logAmort γ F (u + 1)) := by
  unfold logAmort
  iintro ⟨%Sb, %v, %hv, H⟩
  obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
  by_cases hin : b ∈ Sb
  · -- PAID: absorb.
    iexists Sb, v', true
    rw [show (if (true : Bool) then v' + 1 else v') = v' + 1 from rfl]
    isplitr [H]
    · ipureintro; intro _; exact hin
    isplitl [H]
    · iexact H
    iintro H
    iexists (b :: Sb), (v' + 1)
    isplitr [H]
    · ipureintro
      rw [unpaid_cons_paid F Sb b hin]
      omega
    · iexact H
  · -- UNPAID: spend.
    iexists Sb, v', false
    rw [show (if (false : Bool) then v' + 1 else v') = v' from rfl]
    isplitr [H]
    · ipureintro; intro h; exact absurd h (by simp)
    isplitl [H]
    · iexact H
    iintro H
    iexists (b :: Sb), v'
    isplitr [H]
    · ipureintro
      have := unpaid_cons_hit F Sb b hbF hin
      omega
    · iexact H

/-- **SPENDING ON A BLOCK OUTSIDE `F`**: one genuine unit of `u`.  This is
the per-data-block charge, and the block it logs may be anything -- the
conclusion is stated over an arbitrary larger set so that a callee which
logged more blocks than the one asked for still re-establishes the
invariant (deviation 4). -/
theorem logAmort_spend (γ : LogNames) (F : List Nat) (u : Nat) :
    logAmort (GF := GF) γ F (u + 1) ⊢
      ∃ (Sb : List Nat) (v : Nat),
        logOpS γ (v + 1) Sb ∗
        (∀ Sb' : List Nat, ⌜∀ x ∈ Sb, x ∈ Sb'⌝ -∗ logOpS γ v Sb' -∗ logAmort γ F u) := by
  unfold logAmort
  iintro ⟨%Sb, %v, %hv, H⟩
  obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
  iexists Sb, v'
  isplitl [H]
  · iexact H
  iintro %Sb' %hsub H
  iexists Sb', v'
  isplitr [H]
  · ipureintro
    have := unpaid_mono F Sb Sb' hsub
    omega
  · iexact H

/-- ...and the same at a budget that is not `_ + 1`: spending nothing. -/
theorem logAmort_reframe (γ : LogNames) (F : List Nat) (u : Nat) (Sb : List Nat) (v : Nat)
    (hv : u + unpaid F Sb ≤ v) : logOpS (GF := GF) γ v Sb ⊢ logAmort γ F u := by
  unfold logAmort
  iintro H
  iexists Sb, v
  isplitr [H]
  · ipureintro; exact hv
  · iexact H

/-- **ADOPTING A BLOCK INTO `F`.**  Enlarging `F` by a block THE OP HAS
ALREADY LOGGED leaves the potential untouched, because the new member is
not unpaid.  This is what lets `writei` reserve capacity for an indirect
block whose identity it does not learn until `balloc` returns it: the loop
enters at `F = [bmapstart]` and adopts the indirect block, at no cost, out
of `balloc`'s own credited postcondition. -/
theorem logAmort_adopt (γ : LogNames) (F : List Nat) (u b : Nat) (Sb : List Nat) (v : Nat)
    (hb : b ∈ Sb) (hv : u + unpaid F Sb ≤ v) :
    logOpS (GF := GF) γ v Sb ⊢ logAmort γ (b :: F) u := by
  refine logAmort_reframe γ (b :: F) u Sb v ?_
  rw [unpaid_cons_mem F Sb b hb]
  exact hv

/-- **RESERVING A BLOCK WHOSE IDENTITY IS NOT YET KNOWN.**
`logAmort_adopt` is free but needs the block to be logged ALREADY; this is
its dual -- one GENUINE unit buys capacity for an ARBITRARY block, logged
or not.  It is what lets a loop reserve for the data block `bmap` is about
to return before `bmap` has returned it.  (There is no `∀ x` form: the
ledger element is not duplicable, so the block must be picked at the
moment the wand is applied, not afterwards.) -/
theorem logAmort_reserve (γ : LogNames) (F : List Nat) (u x : Nat) :
    logAmort (GF := GF) γ F (u + 1) ⊢ logAmort γ (x :: F) u := by
  unfold logAmort
  iintro ⟨%Sb, %v, %hv, H⟩
  iexists Sb, v
  isplitr [H]
  · ipureintro
    have := unpaid_grow F Sb x
    omega
  · iexact H

/-- **THE CREDITED `balloc`'s SHAPE, EXACTLY.**  `wp_balloc_gen` takes
`logOpS γ (u + 2) Sb` with `cr = true → bmapstart ∈ Sb` and returns
`logOpS γ (if cr then u + 1 else u)` at a set that contains
`bmapstart :: Sb` -- it presents ONE block of `F` (the bitmap block,
absorbing when credited) and spends ONE genuine unit (the `bzero` of the
freshly allocated block).  So the free units drop by EXACTLY ONE across a
`balloc`, whichever arm of the bitmap's `log_write` ran.

TWO units must be free going in: the credited arm needs two in hand even
though it hands one back, because `log_write`'s own "a unit must be in
hand either way" premise applies on the absorbing arm too. -/
theorem logAmort_present_spend (γ : LogNames) (F : List Nat) (u b : Nat) (hbF : b ∈ F) :
    logAmort (GF := GF) γ F (u + 2) ⊢
      ∃ (Sb : List Nat) (v : Nat) (cr : Bool),
        ⌜cr = true → b ∈ Sb⌝ ∗ logOpS γ (v + 2) Sb ∗
        (∀ Sb' : List Nat, ⌜∀ x ∈ b :: Sb, x ∈ Sb'⌝ -∗
          logOpS γ (if cr then v + 1 else v) Sb' -∗ logAmort γ F (u + 1)) := by
  unfold logAmort
  iintro ⟨%Sb, %v, %hv, H⟩
  obtain ⟨v', rfl⟩ : ∃ v', v = v' + 2 := ⟨v - 2, by omega⟩
  by_cases hin : b ∈ Sb
  · -- PAID: the bitmap write absorbs; only the bzero's unit is gone.
    iexists Sb, v', true
    rw [show (if (true : Bool) then v' + 1 else v') = v' + 1 from rfl]
    isplitr [H]
    · ipureintro; intro _; exact hin
    isplitl [H]
    · iexact H
    iintro %Sb' %hsub H
    iexists Sb', (v' + 1)
    isplitr [H]
    · ipureintro
      have := unpaid_mono F Sb Sb' (fun x hx => hsub x (List.mem_cons_of_mem b hx))
      omega
    · iexact H
  · -- UNPAID: the bitmap write spends too, but `b` joins the set and the
    -- held-back term drops by exactly one, so `u` moves by one all the same.
    iexists Sb, v', false
    rw [show (if (false : Bool) then v' + 1 else v') = v' from rfl]
    isplitr [H]
    · ipureintro; intro h; exact absurd h (by simp)
    isplitl [H]
    · iexact H
    iintro %Sb' %hsub H
    iexists Sb', v'
    isplitr [H]
    · ipureintro
      have h1 := unpaid_mono F (b :: Sb) Sb' hsub
      have h2 := unpaid_cons_hit F Sb b hbF hin
      omega
    · iexact H

/-! ## The shape writei's loop carries

The bitmap block and (once it exists) the indirect block reserved, `u`
units free for the data blocks still to come and for `iupdate`. -/

def wiAmort (γ : LogNames) (bmapstart ind u : Nat) : IProp GF :=
  logAmort γ [bmapstart, ind] u

theorem wiAmort_intro (γ : LogNames) (bmapstart ind u v : Nat) (hv : u + 2 ≤ v) :
    logOpb (GF := GF) γ v ⊢ wiAmort γ bmapstart ind u := by
  unfold wiAmort
  exact logAmort_intro γ [bmapstart, ind] u v hv

theorem wiAmort_elim (γ : LogNames) (bmapstart ind u : Nat) :
    wiAmort (GF := GF) γ bmapstart ind u ⊢ ∃ v : Nat, ⌜u ≤ v⌝ ∗ logOpb γ v := by
  unfold wiAmort
  exact logAmort_elim γ [bmapstart, ind] u

end

end Xv6
