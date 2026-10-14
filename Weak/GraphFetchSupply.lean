/-
Weak: **W5d-G G5 (part 3) — the M2 cut clause supplied by the graph** (plan rev 48 §C W5d-G G5
"`supplyOfQconf` producing the M2 cut clause", `notes/W5dG-spike.md` §3.3; D27 RULED (a)
[OWN.6], D40 [OWN.15], D41 RULED (a) [OWN.16], D42–D43 RULED (a) [OWN.18]).  Lean-only, no Rocq
twin.

M2's premise set (`srvwmoXv6M2Premises`, `Weak/PfRunUnpinned.lean`) carries the fetch clause as
the PER-INDEX clause `PfRunUnpinned.fcutEM2 cohSrc E itvOf fiOf` of `execProgOk'SC`: at trace
index `K`, every fetch of the leading administrative star passes the cut form `fcutM2` at
`itvOf K ag`, and `fiOf`/`itvOf` follow the star's `LInstr`/`LIFetch` fold and MachCSL's
`fence.i` raise.  This file supplies that clause for the rule-14 linearization `linCand G` of a
graph whose emissions satisfy the Zifencei slot `GraphFetch.emZif` (`gzFetch` at every fetch
item, real slot tag [OWN.26], the emission's fence.i contributors):

* §1 `GraphFetch.emBlock em k ls l` -- `ls` is the administrative block of slot `k` in `em`
  (the items since the previous row item), its row item `(l, some k)`; the fetch items of `ls`
  sit at slot `k` (`GraphFetchSupply.emBlockFetch`, by `GraphFetch.emSlotShift` and
  `GraphFetchSpike.emSlotAdm`);
* §2 the FREE functions of M2 made concrete from the leading stars `lsOf`:
  `GraphFetchSupply.fiOfL` (the `fiArm` fold) and `GraphFetchSupply.itvOfL` (the `fence.i`
  raise); the boot values and the recurrences of `fcutEM2` hold by construction;
* §3 **`GraphFetchSupply.itvFloor`** -- THE FLOOR BOUND for `itvOfL`: at every trace index,
  hart `i`'s instruction view is at or below the maximum of the fence.i contributors at its
  current slot (a raise happens only at an `emFenceI` site, where `GraphFetchFloor.fencePostConeSrc`
  and `GraphFetchFloor.coneLeContrib` bound it);
* §4 **`GraphFetch.linFcutEM2`** -- THE SUPPLY: `fcutEM2 cohSrc (candExec (linCand G)) itvOfL fiOfL`
  at every trace index, with the boot values (M2's `itvOf 0 i = 0`, `fiOf 0 i = false`), from
  `GraphFetch.linFetchCut` at the floor bound;
* §5 **`GraphFetch.normalizeFetchSupply`** -- composed with G4's `GraphFetch.normalizeOfAcyclicZ`:
  a `racyDIO`-acyclic core graph whose emissions satisfy the slot and store their fetch fragment
  normalizes to an RVWMO⁻ + rule-14 graph whose linearization carries the M2 clause, at the
  renamed emissions.

**The leading stars and the block premise** ([OWN.86]).  The supply takes the leading stars
`lsOf` (one per trace index) and the harts' leading-star functions `g`, with `lsOf K = g i k` at
`(i, k)`'s index and `GraphFetch.emBlockF G (em i) i k (g i)`: `g i k` is the administrative block
of slot `k` in `em i`, the cycle labels of everything before it are those of the earlier leading
stars (`GraphFetch.cycUpto (g i) k`), and AT A `LFence false×4` ROW EVENT the block's row item is
that fence (`GraphFetchSupply.projFence`: forced by the realization relation, `projLbl` is
injective on fences).  `GraphFetchSupply.fiOfLUpto` unfolds the arm `fiOfL` into the fold of the
hart's earlier leading stars, so a raise of the shadow's `itv` (arm set at a fence) is exactly the
emission-wide latest cycle label `LInstr` before the fence, i.e. an `emFenceI` site
(`GraphFetchSupply.siteOfArm`).  (Before [OWN.86] the premise asked a cycle label INSIDE the
fence's block, because G1's `emFenceI` read the block only; that is false on Sail emissions with a
PLIC wire item inside a `fence.i` window, `PROGRESS-W5dG63b.md` §(1).)  The shaped supply (G6)
builds `lsOf`/`g` from `hemitf` (`GraphFetchBlocks.hemitfBlocks`) -- FAITHFUL (a fact about
emissions, no trusted text).

Spec marks.  No new trusted text: proof organisation (FAITHFUL).

Lean-only helpers are file-qualified (`GraphFetchSupply.*`).
-/
import Weak.GraphFetchFloor
import Weak.GraphFetchRetime
import Weak.PfRunUnpinned

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. Blocks -/

/-- `ls` is the administrative block of slot `k` in `em`, closed by the row item `(l, some k)`. -/
def GraphFetch.emBlock (em : Hemission) (k : Nat) (ls : List Wlabel) (l : Wlabel) : Prop :=
  ∃ (pre rest : List Eitem),
    em.emItems = pre ++ eadm ls ++ (l, some k) :: rest ∧
    (∀ it, pre.getLast? = some it → it.2.isSome = true)

/-- The leading stars of the slots before `k`, concatenated in slot order. -/
def GraphFetch.cycUpto (g : Nat → List Wlabel) (k : Nat) : List Wlabel :=
  ((List.range k).map g).flatten

theorem GraphFetch.cycUptoSucc (g : Nat → List Wlabel) (k : Nat) :
    GraphFetch.cycUpto g (k + 1) = GraphFetch.cycUpto g k ++ g k := by
  unfold GraphFetch.cycUpto
  rw [List.range_succ, List.map_append, List.flatten_append]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem GraphFetch.cycUptoCons (g : Nat → List Wlabel) (k : Nat) :
    GraphFetch.cycUpto g (k + 1) = g 0 ++ GraphFetch.cycUpto (fun m => g (m + 1)) k := by
  unfold GraphFetch.cycUpto
  rw [List.range_succ_eq_map, List.map_cons, List.flatten_cons, List.map_map]
  rfl

/-- The supply's block premise at `(i, k)`, for the hart's leading-star function `g` ([OWN.86]):
`g k` is slot `k`'s administrative block in `em` (closed by the row item `(l, some k)`), the cycle
labels of everything before it are those of the earlier leading stars `GraphFetch.cycUpto g k`
(the row items and the intra-pair stars carry none), and at a `LFence false×4` row event the row
item is that fence. -/
def GraphFetch.emBlockF (G : Gexec) (em : Hemission) (i k : Nat) (g : Nat → List Wlabel) : Prop :=
  ∃ (l : Wlabel) (pre rest : List Eitem),
    em.emItems = pre ++ eadm (g k) ++ (l, some k) :: rest ∧
    (∀ it, pre.getLast? = some it → it.2.isSome = true) ∧
    (pre.map Prod.fst).filter GraphFetch.lbCyc = (GraphFetch.cycUpto g k).filter GraphFetch.lbCyc ∧
    (glbl G (i, k) = Lbl.LFence false false false false → l = Wlabel.LFence false false false false)

/-- The block premise gives the block. -/
theorem GraphFetch.emBlockOfF (G : Gexec) (em : Hemission) (i k : Nat) (g : Nat → List Wlabel) :
    GraphFetch.emBlockF G em i k g → ∃ l, GraphFetch.emBlock em k (g k) l := by
  rintro ⟨l, pre, rest, he, hp, -, -⟩
  exact ⟨l, pre, rest, he, hp⟩

/-- The realization relation forces a fence row item: `projLbl` is injective on fences. -/
theorem GraphFetchSupply.projFence (c : WmClass) (l : Wlabel) (pr pw sr sw : Bool) :
    projLbl c l = some (Lbl.LFence pr pw sr sw) → l = Wlabel.LFence pr pw sr sw := by
  cases l <;> simp [projLbl]

/-- A fetch of slot `k`'s block is an emission fetch item at slot `k`. -/
theorem GraphFetchSupply.emBlockFetch (em : Hemission) (k : Nat) (ls : List Wlabel) (l : Wlabel)
    (base : Int) (tvs : List (Nat × BitVec 8)) :
    GraphFetch.emBlock em k ls l → Wlabel.LIFetch base tvs ∈ ls →
    ∃ n, em.emItems[n]? = some (Wlabel.LIFetch base tvs, none) ∧
      GraphFetchSpike.emSlot em.emItems n = k := by
  rintro ⟨pre, rest, he, -⟩ hm
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hm
  have hpl : p < ls.length := lookup_lt_Some hp
  have hlen : (eadm ls).length = ls.length := by simp [eadm]
  refine ⟨pre.length + p, ?_, ?_⟩
  · rw [he, List.append_assoc, List.getElem?_append_right (by omega),
      show pre.length + p - pre.length = p by omega, List.getElem?_append_left (by omega)]
    simp [eadm, hp]
  · rw [he, List.append_assoc, GraphFetch.emSlotShift pre _ p ?_]
    · exact GraphFetchSpike.emSlotAdm ls l k rest p (by omega)
    · rw [List.drop_append_of_le_length (by omega), List.filterMap_append]
      simp

/-- An `emFenceI` site from a fence block whose latest cycle label is `LInstr`. -/
theorem GraphFetchSupply.emFenceIOfBlock (em : Hemission) (f : Nat) (ls : List Wlabel) :
    GraphFetch.emBlock em f ls (Wlabel.LFence false false false false) →
    GraphFetch.lastCycL ls = some Wlabel.LInstr → emFenceI em f := by
  rintro ⟨pre, rest, he, -⟩ hl
  exact GraphFetch.emFenceIOfLast em f pre ls rest he hl

/-! # 2. The instruction view and the arm bit, from the leading stars -/

/-- The two `fiArm` folds are the same function. -/
theorem GraphFetchSupply.fiFoldEq (b : Bool) (ls : List Wlabel) :
    PfRunUnpinned.fiFold b ls = GraphFetch.fiFold b ls := by
  induction ls generalizing b with
  | nil => rfl
  | cons l ls ih =>
    show PfRunUnpinned.fiFold (PfRunUnpinned.fiStep b l) ls = GraphFetch.fiFold (GraphFetch.fiStep b l) ls
    rw [ih]
    cases l <;> rfl

/-- **THE ARM IS THE SITE** ([OWN.86]): at a `LFence false×4` row event whose block premise holds,
the shadow's arm after the earlier leading stars and the block (the hart's labels up to the fence,
cycle-wise) set means the fence is an `emFenceI` site -- the emission-wide latest cycle label
before it is `LInstr`. -/
theorem GraphFetchSupply.siteOfArm (G : Gexec) (em : Hemission) (i k : Nat) (g : Nat → List Wlabel) :
    GraphFetch.emBlockF G em i k g → glbl G (i, k) = Lbl.LFence false false false false →
    PfRunUnpinned.fiFold (PfRunUnpinned.fiFold false (GraphFetch.cycUpto g k)) (g k) = true →
    emFenceI em k := by
  rintro ⟨l, pre, rest, he, -, hcyc, hfen⟩ hgl harm
  have hl := hfen hgl
  subst hl
  refine GraphFetch.emFenceIOfPre em k (pre ++ eadm (g k)) rest (by rw [he]) ?_
  have h1 : GraphFetch.fiFold false (GraphFetch.cycUpto g k ++ g k) = true := by
    rw [← GraphFetchSupply.fiFoldEq]
    unfold PfRunUnpinned.fiFold at harm ⊢
    rw [List.foldl_append]
    exact harm
  rw [GraphFetch.fiFoldLast] at h1
  have h2 : GraphFetch.lastCycL ((pre ++ eadm (g k)).map Prod.fst) =
      GraphFetch.lastCycL (GraphFetch.cycUpto g k ++ g k) := by
    rw [List.map_append, GraphFetch.eadmLabels]
    unfold GraphFetch.lastCycL
    rw [List.filter_append, List.filter_append, hcyc]
  rw [h2]
  cases hlc : GraphFetch.lastCycL (GraphFetch.cycUpto g k ++ g k) with
  | none => rw [hlc] at h1; cases h1
  | some lc =>
    rw [hlc] at h1
    cases lc <;> simp_all [GraphFetch.isInstr]

/-- M2's `fiOf`, made concrete: the leading star's fold on the acting hart, framed elsewhere. -/
def GraphFetchSupply.fiOfL (tr : List Estep) (lsOf : Nat → List Wlabel) : Nat → Nat → Bool
  | 0, _ => false
  | K + 1, i =>
    match tr[K]? with
    | some s =>
      if s.esAg = i then PfRunUnpinned.fiFold (GraphFetchSupply.fiOfL tr lsOf K i) (lsOf K)
      else GraphFetchSupply.fiOfL tr lsOf K i
    | none => GraphFetchSupply.fiOfL tr lsOf K i

/-- M2's `itvOf`, made concrete: MachCSL's `fence.i` raise on the acting hart, framed elsewhere. -/
def GraphFetchSupply.itvOfL (stamp : CohStamp) (E : Exec) (lsOf : Nat → List Wlabel) :
    Nat → Nat → Nat
  | 0, _ => 0
  | K + 1, i =>
    match E.exTr[K]? with
    | some s =>
      if s.esAg = i then
        PfRunUnpinned.itvStep stamp E K i (GraphFetchSupply.itvOfL stamp E lsOf K i)
          (PfRunUnpinned.fiFold (GraphFetchSupply.fiOfL E.exTr lsOf K i) (lsOf K))
      else GraphFetchSupply.itvOfL stamp E lsOf K i
    | none => GraphFetchSupply.itvOfL stamp E lsOf K i

/-- The recurrences and the frame condition of `fcutEM2` hold by construction. -/
theorem GraphFetchSupply.recOk (stamp : CohStamp) (E : Exec) (lsOf : Nat → List Wlabel) (K : Nat)
    (s : Estep) :
    E.exTr[K]? = some s →
    GraphFetchSupply.fiOfL E.exTr lsOf (K + 1) s.esAg =
        PfRunUnpinned.fiFold (GraphFetchSupply.fiOfL E.exTr lsOf K s.esAg) (lsOf K) ∧
      GraphFetchSupply.itvOfL stamp E lsOf (K + 1) s.esAg =
        PfRunUnpinned.itvStep stamp E K s.esAg (GraphFetchSupply.itvOfL stamp E lsOf K s.esAg)
          (PfRunUnpinned.fiFold (GraphFetchSupply.fiOfL E.exTr lsOf K s.esAg) (lsOf K)) ∧
      ∀ i, i ≠ s.esAg →
        GraphFetchSupply.fiOfL E.exTr lsOf (K + 1) i = GraphFetchSupply.fiOfL E.exTr lsOf K i ∧
        GraphFetchSupply.itvOfL stamp E lsOf (K + 1) i = GraphFetchSupply.itvOfL stamp E lsOf K i := by
  intro hs
  refine ⟨?_, ?_, fun i hi => ⟨?_, ?_⟩⟩
  · simp only [GraphFetchSupply.fiOfL, hs, if_true]
  · simp only [GraphFetchSupply.itvOfL, hs, if_true]
  · simp only [GraphFetchSupply.fiOfL, hs, Ne.symm hi, if_false]
  · simp only [GraphFetchSupply.itvOfL, hs, Ne.symm hi, if_false]

/-- **The arm, unfolded** ([OWN.86]): when the leading star at every trace index is the acting
hart's `g` at its own count, `fiOfL` at index `K` is the fold of hart `i`'s earlier leading stars
from the boot bit. -/
theorem GraphFetchSupply.fiOfLUpto (tr : List Estep) (lsOf : Nat → List Wlabel)
    (g : Nat → Nat → List Wlabel)
    (hls : ∀ K s, tr[K]? = some s → lsOf K = g s.esAg (tcnt s.esAg (tr.take K))) :
    ∀ K i, GraphFetchSupply.fiOfL tr lsOf K i =
      PfRunUnpinned.fiFold false (GraphFetch.cycUpto (g i) (tcnt i (tr.take K))) := by
  intro K
  induction K with
  | zero => intro i; rfl
  | succ K ih =>
    intro i
    cases hs : tr[K]? with
    | none =>
      have hle : tr.length ≤ K := List.getElem?_eq_none_iff.1 hs
      have ht : tr.take (K + 1) = tr.take K := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le hle]
      simp only [GraphFetchSupply.fiOfL, hs]
      rw [ht]
      exact ih i
    | some s =>
      by_cases hag : s.esAg = i
      · simp only [GraphFetchSupply.fiOfL, hs]
        rw [if_pos hag, ih i, tcntStepEq i tr K s hs hag, GraphFetch.cycUptoSucc, hls K s hs, hag]
        unfold PfRunUnpinned.fiFold
        rw [List.foldl_append]
      · simp only [GraphFetchSupply.fiOfL, hs]
        rw [if_neg hag, ih i, tcntStepNe i tr K s hs hag]

/-- On the rule-14 linearization, a per-event leading-star choice is the acting hart's `g` at its
own count. -/
theorem GraphFetchSupply.lsOfLin (G : Gexec) (hwf : gwf G) (h14 : grule14 G)
    (lsOf : Nat → List Wlabel) (g : Nat → Nat → List Wlabel)
    (hls : ∀ K i k, (glinEids G)[K]? = some (i, k) → lsOf K = g i k) :
    ∀ K s, (linCand G).cdTr[K]? = some s →
      lsOf K = g s.esAg (tcnt s.esAg ((linCand G).cdTr.take K)) := by
  intro K s hs
  obtain ⟨e, he, rfl⟩ := linTrLookupInv G K s hs
  have hcnt := GraphFetchFloor.ownCount G hwf h14 K e he
  obtain ⟨i, k⟩ := e
  simp only [glinStep] at hcnt ⊢
  rw [hcnt]
  exact hls K i k he

/-! # 3. The floor bound for `itvOfL` -/

/-- The contributors' maximum grows with the slot. -/
theorem GraphFetchSupply.contribSlotMono (G : Gexec) (fi : Nat → Prop) (i k k' : Nat) :
    k ≤ k' →
    (GraphFetchCut.contribIdx G (gzContrib G fi i k)).foldr max 0 ≤
      (GraphFetchCut.contribIdx G (gzContrib G fi i k')).foldr max 0 :=
  fun hk => GraphFetchFloor.contribMono G _ _
    (fun _ ⟨f, hf, hfi, h⟩ => ⟨f, by omega, hfi, h⟩)

/-- **THE FLOOR BOUND**: along the linearization, hart `i`'s concrete instruction view is at or
below the maximum of its emission's fence.i contributors at its current slot. -/
theorem GraphFetchSupply.itvFloor (G : Gexec) (hc : rvwmoMinusConsistent G) (h14 : grule14 G)
    (em : Nat → Hemission) (lsOf : Nat → List Wlabel) (g : Nat → Nat → List Wlabel)
    (hblk : ∀ K i k, (glinEids G)[K]? = some (i, k) →
      lsOf K = g i k ∧ GraphFetch.emBlockF G (em i) i k (g i)) :
    ∀ K, K ≤ (glinEids G).length → ∀ i,
      GraphFetchSupply.itvOfL cohSrc (candExec (linCand G)) lsOf K i ≤
        (GraphFetchCut.contribIdx G
          (gzContrib G (emFenceI (em i)) i (tcnt i ((linCand G).cdTr.take K)))).foldr max 0 := by
  have hwf := hc.1
  intro K
  induction K with
  | zero => intro _ i; exact Nat.zero_le _
  | succ K ih =>
    intro hK i
    have hKl : K < (glinEids G).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (glinEids G)[K]? = some e :=
      someOfIsSome (lookup_lt_is_Some_2 hKl)
    have hs : (linCand G).cdTr[K]? = some (glinStep G e) := linTrLookup G K e he
    have hsE : (candExec (linCand G)).exTr[K]? = some (glinStep G e) := hs
    have ih' := ih (by omega) i
    by_cases hag : e.1 = i
    · have hst := tcntStepEq i _ K _ hs hag
      have hcnt := GraphFetchFloor.ownCount G hwf h14 K e he
      obtain ⟨ei, f⟩ := e
      simp only at hag hcnt
      subst hag
      rw [hst, hcnt]
      rw [hcnt] at ih'
      have hmono := GraphFetchSupply.contribSlotMono G (emFenceI (em ei)) ei f (f + 1) (by omega)
      simp only [GraphFetchSupply.itvOfL, hsE, glinStep, ↓reduceIte]
      show PfRunUnpinned.itvStep cohSrc (candExec (linCand G)) K ei _ _ ≤ _
      unfold PfRunUnpinned.itvStep
      rw [hsE]
      simp only
      split
      · rename_i hraise
        rw [Bool.and_eq_true] at hraise
        obtain ⟨hfz, harm⟩ := hraise
        have hglbl : glbl G (ei, f) = Lbl.LFence false false false false := by
          have : PfRunUnpinned.lbFenceZeroL (glbl G (ei, f)) = true := hfz
          revert this
          unfold PfRunUnpinned.lbFenceZeroL
          split <;> simp_all
        obtain ⟨hlsK, hbf⟩ := hblk K ei f he
        -- the arm is set: the hart's latest cycle label before the fence is `LInstr`, so `f` is
        -- a site ([OWN.86])
        have hsite : emFenceI (em ei) f := by
          refine GraphFetchSupply.siteOfArm G (em ei) ei f (g ei) hbf hglbl ?_
          have hup := GraphFetchSupply.fiOfLUpto (linCand G).cdTr lsOf g
            (GraphFetchSupply.lsOfLin G hwf h14 lsOf g (fun K i k h => (hblk K i k h).1)) K ei
          rw [hcnt] at hup
          rw [← hup, ← hlsK]
          exact harm
        have hfp := GraphFetchFloor.fencePostConeSrc G hwf h14 K ei f he
        have hcone := GraphFetchFloor.coneLeContrib G hc (emFenceI (em ei)) ei f (f + 1) hsite
          (by omega)
        rw [candExTr] at *
        omega
      · omega
    · have hne := tcntStepNe i _ K _ hs hag
      rw [hne]
      have : GraphFetchSupply.itvOfL cohSrc (candExec (linCand G)) lsOf (K + 1) i =
          GraphFetchSupply.itvOfL cohSrc (candExec (linCand G)) lsOf K i := by
        simp only [GraphFetchSupply.itvOfL, hsE]
        simp only [glinStep, hag, if_false]
      rw [this]
      exact ih'

/-! # 4. THE SUPPLY -/

/-- The cut form bounded by the log's length IS M2's fetch clause. -/
theorem GraphFetchSupply.fcutM2OfCut (img : Image) (log : List Wmsg) (itv i : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) :
    fetchCutOk img log log.length itv base tvs → PfRunUnpinned.fcutM2 itv img log i base tvs := by
  rintro ⟨q, h1, h2, h3, h4⟩
  exact ⟨q, h1, h2, h3, fun j t v hj => h4 t (GraphFetchSpike.mapFstOfLookup tvs j t v hj)⟩

/-- **THE M2 CUT CLAUSE, SUPPLIED** (plan §C W5d-G G5): for the rule-14 linearization of an
RVWMO⁻ + rule-14 graph whose emissions satisfy the Zifencei slot, and leading stars `lsOf`
that are the emissions' blocks (`GraphFetch.emBlockF`), M2's per-index clause
`fcutEM2 cohSrc (candExec (linCand G)) itvOfL fiOfL` holds at every trace index, with M2's boot
values. -/
theorem GraphFetch.linFcutEM2 (G : Gexec) (hc : rvwmoMinusConsistent G) (h14 : grule14 G)
    (em : Nat → Hemission) (lsOf : Nat → List Wlabel)
    (g : Nat → Nat → List Wlabel) (hz : ∀ i, GraphFetch.emZif G i (em i))
    (hblk : ∀ K i k, (glinEids G)[K]? = some (i, k) →
      lsOf K = g i k ∧ GraphFetch.emBlockF G (em i) i k (g i)) :
    (∀ i, GraphFetchSupply.itvOfL cohSrc (candExec (linCand G)) lsOf 0 i = 0) ∧
    (∀ i, GraphFetchSupply.fiOfL (candExec (linCand G)).exTr lsOf 0 i = false) ∧
    ∀ K s, (candExec (linCand G)).exTr[K]? = some s →
      PfRunUnpinned.fcutEM2 cohSrc (candExec (linCand G))
        (GraphFetchSupply.itvOfL cohSrc (candExec (linCand G)) lsOf)
        (GraphFetchSupply.fiOfL (candExec (linCand G)).exTr lsOf) K s.esAg (lsOf K)
        (stt (candExec (linCand G)) K) := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun K s hs => ?_⟩
  obtain ⟨hr1, hr2, hr3⟩ := GraphFetchSupply.recOk cohSrc (candExec (linCand G)) lsOf K s hs
  refine ⟨fun base tvs hm => ?_, hr1, hr2, hr3⟩
  have hs' : (linCand G).cdTr[K]? = some s := hs
  obtain ⟨e, he, rfl⟩ := linTrLookupInv G K s hs'
  obtain ⟨i, k⟩ := e
  have hKl : K ≤ (linCand G).cdTr.length := by have := lookup_lt_Some hs'; omega
  obtain ⟨hlsK, hbf⟩ := hblk K i k he
  obtain ⟨l, hb⟩ := GraphFetch.emBlockOfF G (em i) i k (g i) hbf
  rw [hlsK] at hm
  obtain ⟨n, hn, hslot⟩ := GraphFetchSupply.emBlockFetch (em i) k (g i k) l base tvs hb hm
  have hzf := hz i n base tvs hn
  rw [hslot] at hzf
  have hcnt := GraphFetchFloor.ownCount G hc.1 h14 K (i, k) he
  have hfl := GraphFetchSupply.itvFloor G hc h14 em lsOf g hblk K
    (by rw [linTrLen] at hKl; exact hKl) i
  simp only at hcnt
  rw [hcnt] at hfl
  have hcut := (GraphFetch.linFetchCut G hc h14 (emFenceI (em i)) K i k base tvs _ he hzf hfl).1
  have hlog : (stt (candExec (linCand G)) K).msLog = cdLog (linCand G) K := candElog _ K hKl
  have himg : (stt (candExec (linCand G)) K).msImg = G.gxImg := candEimg _ K hKl
  rw [hlog, himg]
  exact GraphFetchSupply.fcutM2OfCut _ _ _ _ _ _ hcut

/-! # 5. Composed with the normalization -/

/-- **THE M2 CLAUSE THROUGH THE NORMALIZATION**: a `racyDIO`-acyclic core graph whose emissions
satisfy the Zifencei slot and store their fetch fragment normalizes (G4,
`GraphFetch.normalizeOfAcyclicZ`) to an RVWMO⁻ + rule-14 graph whose rule-14 linearization
carries M2's per-index clause at the renamed emissions' blocks. -/
theorem GraphFetch.normalizeFetchSupply (GF : Gfexec) (em : Nat → Hemission) :
    rvwmoCoreD GF.gfGd →
    (∀ x, ¬ tc (racyDIO GF) x x) →
    (∀ i, GraphFetch.emFetchIn GF.gfGd i (em i)) →
    (∀ i, GraphFetch.emZif GF.gfGd.gdG i (em i)) →
    ∃ (GD' : Gdexec) (pi : Nat → Nat),
      rvwmoMinusDepsConsistent GD' ∧
      grule14 GD'.gdG ∧
      rowsRel pi GF.gfGd.gdG GD'.gdG ∧
      GD'.gdDeps = GF.gfGd.gdDeps ∧
      GD'.gdFetch = GF.gfGd.gdFetch ∧
      wperm pi GF.gfGd.gdG GD'.gdG ∧
      ∀ (lsOf : Nat → List Wlabel) (g : Nat → Nat → List Wlabel),
        (∀ K i k, (glinEids GD'.gdG)[K]? = some (i, k) →
          lsOf K = g i k ∧ GraphFetch.emBlockF GD'.gdG (emRen pi (em i)) i k (g i)) →
        (∀ i, GraphFetchSupply.itvOfL cohSrc (candExec (linCand GD'.gdG)) lsOf 0 i = 0) ∧
        (∀ i, GraphFetchSupply.fiOfL (candExec (linCand GD'.gdG)).exTr lsOf 0 i = false) ∧
        ∀ K s, (candExec (linCand GD'.gdG)).exTr[K]? = some s →
          PfRunUnpinned.fcutEM2 cohSrc (candExec (linCand GD'.gdG))
            (GraphFetchSupply.itvOfL cohSrc (candExec (linCand GD'.gdG)) lsOf)
            (GraphFetchSupply.fiOfL (candExec (linCand GD'.gdG)).exTr lsOf) K s.esAg (lsOf K)
            (stt (candExec (linCand GD'.gdG)) K) := by
  intro hcore hacy hin hz
  obtain ⟨GD', pi, hc', h14, hrr, hdeps, hfe, hw, hzren⟩ :=
    GraphFetch.normalizeOfAcyclicZ GF hcore hacy
  refine ⟨GD', pi, hc', h14, hrr, hdeps, hfe, hw, fun lsOf g hblk => ?_⟩
  exact GraphFetch.linFcutEM2 GD'.gdG hc'.1 h14 (fun i => emRen pi (em i)) lsOf g
    (fun i => hzren i (em i) (hin i) (hz i)) hblk

end Weak
