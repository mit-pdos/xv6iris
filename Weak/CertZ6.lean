/-
Weak: **W10-3 [OWN.94] (N2′), increment 1 — THE LOCKSTEP WALK INVARIANT and the walk policy from a
scheduler** (`PROGRESS-W10N2p.md`; the W10 sizing's W10-3 row "Walkb's invariant and site supply at
cat + Z").  Lean-only, no Rocq twin.

`WeakRvwmoWalkb`'s `wlkInv'` carries, per hart, its emission from its current row position and the
walk state's process identified with it.  The Z twin, for the LOCKSTEP walk (every hart's certified
state IS its emission state; the poisoned / tainted arm is W10-4's):

  §1  `wRelp` agreement is FREE: a hart's appended labels are `lblReidxW` of its row prefix
      (`CertZ6.foldRelpReidx`), so the candidate's release-pending bit is the emission's
      (`CertZ6.relpAgree`, through `candLastWsRelp`);
  §2  the emission's blocks per slot (`CertZ6.emBlocks`: fused — `lbFused`, by (P2) — or a pair, at
      the emission's fabric endpoints, and at ANY fabric when contact-free) extracted from a hart's
      `hartConff` (**`CertZ6.emBlocksOfHart`**, from `GraphFetchBlocks.hemitfBlocks` + (P2)
      `GraphFetchBlocks.emNoDangle`);
  §3  **`CertZ6.lockInv`** (per hart: its counter, its certified program state = the emission's,
      its trace labels `lblReidxW` of its row prefix; every agent a hart; plus an extra invariant
      `X` the scheduler keeps) and the SCHEDULER **`CertZ6.schedZ`** (the remaining obligation:
      at every invariant state, an enabled hart — its block's fabric is the walk's, or the block is
      contact-free — whose next read/fetch VALUES agree with the latest bytes, keeping `X`);
      **`CertZ6.walkPolOfSched`** — the walk policy `CertZ2.walkPolZ` from the scheduler.

Spec: proof organisation; the scheduler is the order + value-agreement datum (FAITHFUL), nothing
assumed of `GF`'s gmo.  Lean-only helpers file-qualified (`CertZ6.*`).
-/
import Weak.CertZ5

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. `wRelp` agreement -/

theorem CertZ6.foldRelpReidx (b : Bool) :
    ∀ (r r' : List Lbl), List.Forall₂ lblReidxW r r' → r'.foldl lpostRelp b = r.foldl lpostRelp b := by
  intro r r' h
  induction h generalizing b with
  | nil => rfl
  | cons hx _ ih =>
    simp only [List.foldl_cons]
    rw [lblReidxWRelp _ _ _ hx]
    exact ih _

/-- **`wRelp` AGREEMENT IS FREE**: if hart `x`'s trace labels are `lblReidxW` of its row prefix, the
candidate's release-pending bit is the emission's at that slot. -/
theorem CertZ6.relpAgree (c : Cand) (x : Nat) (row : List Lbl) (n : Nat) :
    List.Forall₂ lblReidxW (row.take n) (CertZ2.hartTr c.cdTr x) →
    ((candLastSt c).msWs x).wRelp = (rowWsAux 0 wsInit (row.take n)).wRelp := by
  intro h
  rw [candLastWsRelp]
  unfold rowWs
  rw [rowWsAuxRelp, rowWsAuxRelp]
  have htk : (trow x c.cdTr).take (tcnt x c.cdTr) = CertZ2.hartTr c.cdTr x := by
    show (CertZ2.hartTr c.cdTr x).take (tcnt x c.cdTr) = _
    apply List.take_of_length_le
    simp [CertZ2.hartTr, tcnt]
  rw [htk]
  exact CertZ6.foldRelpReidx _ _ _ h

/-! # 2. The emission's blocks -/

/-- Hart's emission blocks, per row slot `n`: the program state `f n → f (n+1)`, the leading star
`g n`, the realizing label `r n`, the fabric endpoints `dvi n → dvo n` (any fabric when
`tq n = false`); a single-step block's realizing label is fused. -/
def CertZ6.emBlocks (row : List Lbl) (f : Nat → Pexv6) (g : Nat → List Wlabel)
    (r : Nat → Wlabel) (dvi dvo : Nat → Efab) (tq : Nat → Bool) : Prop :=
  ∀ n lb, row[n]? = some lb →
    (lbFused (r n) ∧
      GraphFetchBlocks.blkOne (dvi n) (dvo n) (rowWsAux 0 wsInit (row.take n)) lb (g n) (r n)
        (f n) (f (n + 1)) ∧
      (tq n = false → ∀ d, GraphFetchBlocks.blkOne d d (rowWsAux 0 wsInit (row.take n)) lb (g n)
        (r n) (f n) (f (n + 1)))) ∨
    (GraphFetchBlocks.blkPair (dvi n) (dvo n) (rowWsAux 0 wsInit (row.take n)) lb (g n) (r n)
        (f n) (f (n + 1)) ∧
      (tq n = false → ∀ d, GraphFetchBlocks.blkPair d d (rowWsAux 0 wsInit (row.take n)) lb (g n)
        (r n) (f n) (f (n + 1))))

/-- **`CertZ6.emBlocksOfHart`**: a hart's emission (with (P2), no dangling exclusive read) gives its
blocks; the single-step blocks are fused (a dangling `LExLoad` would need an `LExStore` of its slot,
which the slot's uniqueness excludes; an `LExStore` never realizes, `lbNobarex`). -/
theorem CertZ6.emBlocksOfHart (i : Nat) (row : List Lbl) (p0 : Pexv6) (dvi dvo : Nat → Efab)
    (tq : Nat → Bool) (em : Hemission) :
    hartConff i row p0 dvi dvo tq em → GraphFetchBlocks.emNoDangle em →
    ∃ (f : Nat → Pexv6) (g : Nat → List Wlabel) (r : Nat → Wlabel), f 0 = p0 ∧
      CertZ6.emBlocks row f g r dvi dvo tq := by
  intro hem hnd
  obtain ⟨f, g, r, hf0, hblk⟩ :=
    GraphFetchBlocks.hemitfBlocks dvi dvo tq 0 wsInit row p0 em.emItems em.emFin hem
  refine ⟨f, g, r, hf0, fun n lb hn => ?_⟩
  obtain ⟨⟨pre, rest, hes, -, -⟩, -, harm⟩ := hblk n lb hn
  simp only [Nat.add_zero] at harm
  rcases harm with ⟨h1, h2, h3⟩ | h4
  · refine .inl ⟨?_, h1, h2⟩
    obtain ⟨pa, da, -, hre, -⟩ := h1
    have hnb := hre.1
    cases hr : r n with
    | LExLoad aq base tvs asrc =>
      exfalso
      have hpos : em.emItems[(pre ++ eadm (g n)).length]? =
          some (Wlabel.LExLoad aq base tvs asrc, some n) := by
        rw [hes, List.append_assoc, List.getElem?_append_right (by simp)]
        simp [hr]
      obtain ⟨n', rl, base', data, asrc', vsrc', hn'⟩ := hnd _ aq base tvs asrc n (by
        rw [hpos])
      have hmem : (Wlabel.LExStore rl base' data asrc' vsrc', some n) ∈ em.emItems :=
        List.mem_of_getElem? hn'
      have := h3 _ hmem rfl
      rw [hr] at this
      cases this
    | LExStore => rw [hr] at hnb; exact hnb.elim
    | _ => simp [lbFused]
  · exact .inr h4

/-! # 3. The lockstep invariant, the scheduler, the walk policy -/

/-- **THE LOCKSTEP INVARIANT** over the rows, the emission states `F x n` and an extra invariant
`X`. -/
def CertZ6.lockInv (rows : List (List Lbl)) (F : Nat → Nat → Pexv6) (X : CertZ2.WInv) :
    CertZ2.WInv :=
  fun St itvOf fiOf cnt =>
    (∀ x, x < rows.length →
      cnt x ≤ (rows.getD x []).length ∧
      (St.cstPst (cdEnd St.cstC))[x]? = some (F x (cnt x)) ∧
      List.Forall₂ lblReidxW ((rows.getD x []).take (cnt x)) (CertZ2.hartTr St.cstC.cdTr x)) ∧
    (∀ s, s ∈ St.cstC.cdTr → s.esAg < rows.length) ∧
    X St itvOf fiOf cnt

/-- The fabric after hart `x`'s slot `n`: the emission's end fabric if the block touches the
fabric, else the walk's current one (a contact-free block keeps it). -/
def CertZ6.dNext (DVO : Nat → Nat → Efab) (TQ : Nat → Nat → Bool) (St : CycState) (x n : Nat) :
    Efab :=
  if TQ x n = true then DVO x n else St.cstDv (cdEnd St.cstC)

/-- **THE SCHEDULER — the walk's remaining datum (W10-3b order, W10-4 values)**: at every invariant
state with a hart left, an ENABLED hart (its block contact-free, or the block's start fabric the
walk's) whose next row label's read footprint exists, whose read VALUES and fetch VALUES are the
latest bytes, keeping the extra invariant `X` at the appended state. -/
def CertZ6.schedZ (d0 : Efab) (rows : List (List Lbl)) (F : Nat → Nat → Pexv6)
    (G : Nat → Nat → List Wlabel) (DVI DVO : Nat → Nat → Efab) (TQ : Nat → Nat → Bool)
    (X : CertZ2.WInv) : Prop :=
  ∀ (St : CycState) (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool) (cnt : Nat → Nat),
    CertZ.cstOkZW d0 St itvOf fiOf → CertZ6.lockInv rows F X St itvOf fiOf cnt →
    (∃ x, x < rows.length ∧ cnt x < (rows.getD x []).length) →
    ∃ (x : Nat) (lb : Lbl),
      x < rows.length ∧ (rows.getD x [])[cnt x]? = some lb ∧
      (TQ x (cnt x) = true → DVI x (cnt x) = St.cstDv (cdEnd St.cstC)) ∧
      CertZ4.readFoot St.cstC lb ∧
      (∀ aq base ts vs, lb = .LLoad aq base ts vs → lrdVs St.cstC base ts.length = vs) ∧
      (∀ aq rl base ts rvs wvs kc, lb = .LRmw aq rl base ts rvs wvs kc →
        lrdVs St.cstC base ts.length = rvs) ∧
      CertZ5.fetchAgree St.cstC (G x (cnt x)) ∧
      X (CertZ2.stSnoc St x (CertZ4.machLbl St.cstC lb) (F x (cnt x + 1))
          (CertZ6.dNext DVO TQ St x (cnt x)))
        (CertZ.itvSnoc St.cstC ⟨x, CertZ4.machLbl St.cstC lb⟩
          ((G x (cnt x)).map (CertZ5.fetchRet St.cstC)) itvOf fiOf)
        (CertZ.fiSnoc St.cstC ⟨x, CertZ4.machLbl St.cstC lb⟩
          ((G x (cnt x)).map (CertZ5.fetchRet St.cstC)) fiOf)
        (CertZ2.bump cnt x)

theorem CertZ6.forall₂Snoc {α β : Type} (R : α → β → Prop) (l1 : List α) (l2 : List β) (a : α)
    (b : β) : List.Forall₂ R l1 l2 → R a b → List.Forall₂ R (l1 ++ [a]) (l2 ++ [b]) := by
  intro h hab
  induction h with
  | nil => exact .cons hab .nil
  | cons hx _ ih => exact .cons hx ih

theorem CertZ6.hartTrSnoc (tr : List Estep) (s : Estep) (y : Nat) :
    CertZ2.hartTr (tr ++ [s]) y =
      if s.esAg = y then CertZ2.hartTr tr y ++ [s.esLb] else CertZ2.hartTr tr y := by
  by_cases h : s.esAg = y <;> simp [CertZ2.hartTr, List.filter_append, h]

/-- **`CertZ6.walkPolOfSched` — THE WALK POLICY FROM THE SCHEDULER** (`wlkStep'OfSupply`'s twin
for the lockstep walk): every step is the emission's block re-answered (`CertZ5.lockstepOne`/
`lockstepPair`), the invariant kept. -/
theorem CertZ6.walkPolOfSched (d0 : Efab) (rows : List (List Lbl)) (F : Nat → Nat → Pexv6)
    (G : Nat → Nat → List Wlabel) (R : Nat → Nat → Wlabel) (DVI DVO : Nat → Nat → Efab)
    (TQ : Nat → Nat → Bool) (X : CertZ2.WInv) :
    (∀ (x n : Nat) (lb : Lbl), (rows.getD x [])[n]? = some lb → CertZ4.lblShape lb) →
    (∀ x, x < rows.length →
      CertZ6.emBlocks (rows.getD x []) (F x) (G x) (R x) (DVI x) (DVO x) (TQ x)) →
    CertZ6.schedZ d0 rows F G DVI DVO TQ X →
    CertZ2.walkPolZ d0 rows (CertZ6.lockInv rows F X) := by
  intro hsh hem hsched St itvOf fiOf cnt hok hinv hd
  obtain ⟨x, lb, hx, hlb, hfab, hft, hvl, hvr, hfag, hX⟩ := hsched St itvOf fiOf cnt hok hinv hd
  obtain ⟨hper, hagt, -⟩ := hinv
  obtain ⟨-, hp, hf2⟩ := hper x hx
  have hc := hok.1
  have hr := CertZ6.relpAgree St.cstC x (rows.getD x []) (cnt x) hf2
  have hitv := CertZ5.itvBound d0 St itvOf fiOf hok (cdEnd St.cstC) (Nat.le_refl _) x
  have hstep : ∃ (pa : Pexv6) (da : Efab),
      CertZ2.stepOkZ St itvOf x (CertZ4.machLbl St.cstC lb) (F x (cnt x)) pa da
        ((G x (cnt x)).map (CertZ5.fetchRet St.cstC)) (F x (cnt x + 1))
        (CertZ6.dNext DVO TQ St x (cnt x)) := by
    rcases hem x hx (cnt x) lb hlb with ⟨hfu, h1, hq⟩ | ⟨h1, hq⟩
    · cases htq : TQ x (cnt x) with
      | true =>
        have hd' : CertZ6.dNext DVO TQ St x (cnt x) = DVO x (cnt x) := by
          simp [CertZ6.dNext, htq]
        rw [hd']
        rw [hfab htq] at h1
        exact CertZ5.lockstepOne St itvOf x lb _ _ _ _ _ _ hc (hsh x _ lb hlb) hft hr hfu h1 hfag
          hvl hitv
      | false =>
        have hd' : CertZ6.dNext DVO TQ St x (cnt x) = St.cstDv (cdEnd St.cstC) := by
          simp [CertZ6.dNext, htq]
        rw [hd']
        exact CertZ5.lockstepOne St itvOf x lb _ _ _ _ _ _ hc (hsh x _ lb hlb) hft hr hfu
          (hq htq _) hfag hvl hitv
    · cases htq : TQ x (cnt x) with
      | true =>
        have hd' : CertZ6.dNext DVO TQ St x (cnt x) = DVO x (cnt x) := by
          simp [CertZ6.dNext, htq]
        rw [hd']
        rw [hfab htq] at h1
        exact CertZ5.lockstepPair St itvOf x lb _ _ _ _ _ _ hc (hsh x _ lb hlb) hft hr h1 hfag
          hvr hitv
      | false =>
        have hd' : CertZ6.dNext DVO TQ St x (cnt x) = St.cstDv (cdEnd St.cstC) := by
          simp [CertZ6.dNext, htq]
        rw [hd']
        exact CertZ5.lockstepPair St itvOf x lb _ _ _ _ _ _ hc (hsh x _ lb hlb) hft hr
          (hq htq _) hfag hvr hitv
  obtain ⟨pa, da, hok'⟩ := hstep
  refine ⟨x, lb, CertZ4.machLbl St.cstC lb, F x (cnt x), pa, da,
    (G x (cnt x)).map (CertZ5.fetchRet St.cstC), F x (cnt x + 1),
    CertZ6.dNext DVO TQ St x (cnt x), hx, hlb, hp, CertZ4.machLblReidx St.cstC lb hvl hvr, hok',
    ⟨fun y hy => ?_, fun s hs => ?_, hX⟩⟩
  · obtain ⟨hle, hpy, hfy⟩ := hper y hy
    have hpst : (CertZ2.stSnoc St x (CertZ4.machLbl St.cstC lb) (F x (cnt x + 1))
        (CertZ6.dNext DVO TQ St x (cnt x))).cstPst
        (cdEnd (CertZ2.stSnoc St x (CertZ4.machLbl St.cstC lb) (F x (cnt x + 1))
          (CertZ6.dNext DVO TQ St x (cnt x))).cstC) =
        (St.cstPst (cdEnd St.cstC)).set x (F x (cnt x + 1)) := by
      show pstSnoc St.cstC St.cstPst x _ (cdEnd (candSnoc St.cstC _)) = _
      rw [cdEndSnoc, pstSnocGt _ _ _ _ _ (by omega)]
    rw [hpst]
    show _ ∧ _ ∧ List.Forall₂ lblReidxW _ (CertZ2.hartTr (St.cstC.cdTr ++ [⟨x, _⟩]) y)
    rw [CertZ6.hartTrSnoc]
    by_cases hy' : y = x
    · subst hy'
      rw [CertZ2.bumpSelf, if_pos rfl]
      refine ⟨lookup_lt_Some hlb, List.getElem?_set_self (lookup_lt_Some hp), ?_⟩
      rw [take_S_r hlb]
      exact CertZ6.forall₂Snoc _ _ _ _ _ hfy (CertZ4.machLblReidx St.cstC lb hvl hvr)
    · rw [CertZ2.bumpNe cnt x y hy', if_neg (Ne.symm hy'),
        List.getElem?_set_ne (Ne.symm hy')]
      exact ⟨hle, hpy, hfy⟩
  · change s ∈ St.cstC.cdTr ++ [⟨x, _⟩] at hs
    rcases List.mem_append.1 hs with hs | hs
    · exact hagt s hs
    · simp only [List.mem_singleton] at hs
      rw [hs]
      exact hx

end Weak
