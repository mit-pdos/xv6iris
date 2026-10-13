/-
Weak: **W5d-G G1 — the graph-tier Zifencei fetch clause, statement layer** (plan rev 45 §C
W5d-G G1, §B(4)(iii); D27 RULED (a) [OWN.6], D40 [OWN.15], D41 RULED (a) [OWN.16], D42–D43
RULED (a) [OWN.18], [OWN.26]).  Lean-only, no Rocq twin.

The trusted-base item is `gzFetch` (`Weak/GraphFetchSpike.lean`, (Z2) in R1 (a)'s E1′ form
since G1); the spike's `GraphFetchSpike.emZifencei G C i em` quantifies it over every
administrative fetch item of a row emission at its REAL slot tag `GraphFetchSpike.emSlot`
[OWN.26].  This file supplies what the bundle needs to instantiate it:

* §1 `GraphFetch.emSlotShift` (G0 review item 2): the slot of an item is unchanged by a prefix
  of the item list, when a row item follows it (always, for a `hemit` emission);
* §2 THE fence.i SITES `emFenceI em f` (D40 [OWN.15]): `fence.i` and the Q7 `sfence.vma` marker
  share the label `LFence false false false false` (`WeakEvInst.ebarLabel .Barrier_RISCV_i`,
  `WeakEvLang.annLabel`), so the sites come from the EMISSION STRUCTURE: the row item of slot `f`
  is that fence AND, in its administrative block (the items since the previous row item), the
  latest `LInstr`/`LIFetch` is `LInstr`.  fence.i's cycle is boundary `LInstr`, fetch, announce
  `LInstr`, barrier; sfence.vma's is boundary `LInstr`, fetch, marker.
  **`GraphFetch.emFenceISound`**: at an `emFenceI` site the latest cycle label of the block is
  the announce `LInstr` (`GraphFetch.lastCycL`), so the hart's latest own `LInstr`/`LIFetch`
  step before the realizing node is `LInstr` WHATEVER preceded the block
  (`GraphFetch.fiFoldOfEmFenceI`: the shadow's `fiArm` fold is `true` from either start) -- by
  `sailCycleOrder_holds`'s second clause (at an `sfence.vma` ANNOUNCE node the latest is an
  `LIFetch`), the node is not the marker.  The converse `GraphFetch.emFenceIOfLast` (a
  `LFence false×4` row item whose block's latest cycle label is `LInstr` is a site) gives
  completeness for the Sail cycle, whose fence.i block always holds its own announce;
* §3 the contributor instance `GraphFetch.emContrib` (`gzContrib` at `emFenceI em`) and THE SLOT
  CONTENT `GraphFetch.emZif G i em` (= `GraphFetchSpike.emZifencei G (emContrib G em i) i em`;
  `Weak.emZifencei` in `WeakRvwmoFab` is this);
* §4 THE KERNEL-TEXT INSTANCE (plan §B(4)(iii); D43 (a) [OWN.18] keeps `pstepPin`/`fetchPin` as
  it): a pinned fetch (tag 0, image bytes) of bytes the graph never writes satisfies `gzFetch`
  (`GraphFetch.gzFetchOfPin`), so a pinned emission whose fetched bytes are unwritten satisfies
  the slot (`GraphFetch.emZifOfPin`); kernel-only executions get an EMPTY fetch fragment.

Spec marks.  RVWMO has NO instruction-fetch model; the Zifencei text ("a subsequent instruction
fetch ... will see any previous data stores already visible to the same RISC-V hart") and the
Sail model (`fence.i` is the bare `Barrier_RISCV_i`) are the reference.  `emFenceI` is FAITHFUL
(it identifies exactly Sail's fence.i barriers on Sail-cycle runs; it adds no order).  The
contributor superset is D41 (a) (STRONGER than TsoMem's `itvPost` set, within the Zifencei text).
(Z2)'s E1′ is a NAMED stronger hardware reading (see `gzFetch`).

Deviations: none from the plan's G1 statement list except where the bundle carries the clause --
see `WeakRvwmoFab` deviation 6 (the PINNED bundle `gfexecConfIO` keeps `emFetchImg` for the pinned
supply until G6, D43 (a); the Zifencei bundle is `gfexecConfZ`).  Lean-only helpers are
file-qualified (`GraphFetch.*`).
-/
import Weak.GraphFetchSpike
import Weak.WeakRvwmoSupply

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! # 1. Slots under a prefix (G0 review item 2) -/

/-- The slot of item `|pre| + n` of `pre ++ its` is the slot of item `n` of `its`, when a row item
follows it in `its`. -/
theorem GraphFetch.emSlotShift (pre its : List Eitem) (n : Nat) :
    (its.drop n).filterMap Prod.snd ≠ [] →
    GraphFetchSpike.emSlot (pre ++ its) (pre.length + n) = GraphFetchSpike.emSlot its n := by
  intro hne
  have hd : (pre ++ its).drop (pre.length + n) = its.drop n := by
    rw [List.drop_append]
    simp
  unfold GraphFetchSpike.emSlot
  rw [hd]
  obtain ⟨x, xs, hx⟩ : ∃ x xs, (its.drop n).filterMap Prod.snd = x :: xs := by
    cases h : (its.drop n).filterMap Prod.snd with
    | nil => exact absurd h hne
    | cons x xs => exact ⟨x, xs, rfl⟩
  rw [hx]
  rfl

/-- A `hemit` emission ENDS with a row item (`HEnil` emits nothing). -/
theorem GraphFetch.hemitLast (dv : Nat → Efab) (k : Nat) (ws : Wstate) (row : List Lbl)
    (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemit dv k ws row p es pfin → ∀ it, es.getLast? = some it → it.2.isSome = true := by
  intro h
  induction h with
  | HEnil => intro it hit; cases hit
  | HEone k ws lb row p ls pa da l p' es pfin _ _ _ _ ih =>
    intro it hit
    rw [List.getLast?_append, List.getLast?_cons] at hit
    cases hes : es.getLast? with
    | none => rw [hes] at hit; cases hit; rfl
    | some it' => rw [hes] at hit; cases hit; exact ih it' hes
  | HEpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin _ _ _ _ _ _ ih =>
    intro it hit
    rw [List.getLast?_append, List.getLast?_cons, List.getLast?_append, List.getLast?_cons] at hit
    cases hes : es.getLast? with
    | none => rw [hes] at hit; cases hit; rfl
    | some it' => rw [hes] at hit; cases hit; exact ih it' hes

/-- When the list ends with a row item, a row item follows every position. -/
theorem GraphFetch.rowAfterOfLast (its : List Eitem) (n : Nat) :
    (∀ it, its.getLast? = some it → it.2.isSome = true) → n < its.length →
    (its.drop n).filterMap Prod.snd ≠ [] := by
  intro hl hn
  have hne : its ≠ [] := by intro h; rw [h] at hn; simp at hn
  obtain ⟨it, hit⟩ : ∃ it, its.getLast? = some it := by
    cases h : its.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 h) hne
    | some it => exact ⟨it, rfl⟩
  have hd : (its.drop n).getLast? = some it := by
    rw [List.getLast?_drop]
    simp only [show ¬ its.length ≤ n by omega, if_false]
    exact hit
  have hmem : it ∈ its.drop n := List.mem_of_getLast? hd
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (hl it hit)
  intro hnil
  have : x ∈ (its.drop n).filterMap Prod.snd := List.mem_filterMap.2 ⟨it, hmem, hx⟩
  rw [hnil] at this
  cases this

/-- The slot of an item of a `hemit` emission is unchanged by a prefix of the item list. -/
theorem GraphFetch.emSlotShiftHemit (dv : Nat → Efab) (k : Nat) (ws : Wstate) (row : List Lbl)
    (p : Pexv6) (pre es : List Eitem) (pfin : Pexv6) (n : Nat) :
    hemit dv k ws row p es pfin → n < es.length →
    GraphFetchSpike.emSlot (pre ++ es) (pre.length + n) = GraphFetchSpike.emSlot es n :=
  fun h hn => GraphFetch.emSlotShift pre es n
    (GraphFetch.rowAfterOfLast es n (GraphFetch.hemitLast dv k ws row p es pfin h) hn)

/-! # 2. The fence.i sites (D40 [OWN.15]) -/

/-- The cycle-skeleton labels: the instruction boundary / announce `LInstr` and a fetch. -/
def GraphFetch.lbCyc (l : Wlabel) : Bool :=
  match l with
  | .LInstr => true
  | .LIFetch .. => true
  | _ => false

/-- `true` exactly at `LInstr`. -/
def GraphFetch.isInstr (l : Wlabel) : Bool :=
  match l with
  | .LInstr => true
  | _ => false

/-- The latest cycle label of a label list. -/
def GraphFetch.lastCycL (ls : List Wlabel) : Option Wlabel := (ls.filter GraphFetch.lbCyc).getLast?

/-- The shadow's `fiArm` step (`TsoShadow.shStepF`; `PfRunUnpinned.fiStep` is the same function):
set by `LInstr`, cleared by `LIFetch`, else carried. -/
def GraphFetch.fiStep (b : Bool) (l : Wlabel) : Bool :=
  match l with
  | .LInstr => true
  | .LIFetch .. => false
  | _ => b

def GraphFetch.fiFold (b : Bool) (ls : List Wlabel) : Bool := ls.foldl GraphFetch.fiStep b

/-- The fold IS "the latest cycle label is `LInstr`", falling back to the start bit when the list
has no cycle label. -/
theorem GraphFetch.fiFoldLast (b : Bool) (ls : List Wlabel) :
    GraphFetch.fiFold b ls =
      match GraphFetch.lastCycL ls with
      | none => b
      | some l => GraphFetch.isInstr l := by
  induction ls generalizing b with
  | nil => rfl
  | cons x xs ih =>
    have hc : GraphFetch.lastCycL (x :: xs) =
        (GraphFetch.lastCycL xs).or (if GraphFetch.lbCyc x then some x else none) := by
      unfold GraphFetch.lastCycL
      rw [show x :: xs = [x] ++ xs from rfl, List.filter_append, List.getLast?_append]
      cases x <;> rfl
    show GraphFetch.fiFold (GraphFetch.fiStep b x) xs = _
    rw [ih, hc]
    cases GraphFetch.lastCycL xs with
    | some l => rfl
    | none => cases x <;> rfl

/-- **THE fence.i SITES** of an emission (D40 [OWN.15]): the row item of slot `f` is
`LFence false false false false`, and the administrative block before it (the items since the
previous row item, or since the start) has `LInstr` as its latest cycle label. -/
def emFenceI (em : Hemission) (f : Nat) : Prop :=
  ∃ (pre : List Eitem) (ls : List Wlabel) (rest : List Eitem),
    em.emItems = pre ++ eadm ls ++ (Wlabel.LFence false false false false, some f) :: rest ∧
    (∀ it, pre.getLast? = some it → it.2.isSome = true) ∧
    GraphFetch.lastCycL ls = some Wlabel.LInstr

/-- At a site the shadow's `fiArm` fold over the block is `true` from EITHER start bit: whatever
the hart did before the block, its latest own `LInstr`/`LIFetch` before the realizing node is the
block's `LInstr`. -/
theorem GraphFetch.fiFoldOfEmFenceI (ls : List Wlabel) (b : Bool) :
    GraphFetch.lastCycL ls = some Wlabel.LInstr → GraphFetch.fiFold b ls = true := by
  intro h
  rw [GraphFetch.fiFoldLast, h]
  rfl

/-- **`emFenceISound`**: an `emFenceI` site's row item is the all-false fence, its block is
administrative (it follows a row item or the start), and the block's latest cycle label is
`LInstr` -- so for ANY prefix `st` of the hart's own labels, the latest own cycle label before
the realizing node is `LInstr`, never an `LIFetch`; by `sailCycleOrder_holds` (an `sfence.vma`
ANNOUNCE node has an `LIFetch` there) the node is a `fence.i` barrier, not the marker. -/
theorem GraphFetch.emFenceISound (em : Hemission) (f : Nat) :
    emFenceI em f →
    ∃ (pre : List Eitem) (ls : List Wlabel) (rest : List Eitem),
      em.emItems = pre ++ eadm ls ++ (Wlabel.LFence false false false false, some f) :: rest ∧
      ∀ st : List Wlabel,
        GraphFetch.lastCycL (st ++ ls) = some Wlabel.LInstr ∧
        GraphFetch.fiFold false (st ++ ls) = true ∧
        ∀ base tvs, GraphFetch.lastCycL (st ++ ls) ≠ some (Wlabel.LIFetch base tvs) := by
  rintro ⟨pre, ls, rest, he, _, hl⟩
  refine ⟨pre, ls, rest, he, fun st => ?_⟩
  have hl' : GraphFetch.lastCycL (st ++ ls) = some Wlabel.LInstr := by
    unfold GraphFetch.lastCycL at hl ⊢
    rw [List.filter_append, List.getLast?_append, hl]
    rfl
  refine ⟨hl', GraphFetch.fiFoldOfEmFenceI _ _ hl', fun base tvs h => ?_⟩
  rw [hl'] at h
  cases h

/-- Completeness: an all-false fence row item whose administrative block's latest cycle label is
`LInstr` IS a site. -/
theorem GraphFetch.emFenceIOfLast (em : Hemission) (f : Nat) (pre : List Eitem) (ls : List Wlabel)
    (rest : List Eitem) :
    em.emItems = pre ++ eadm ls ++ (Wlabel.LFence false false false false, some f) :: rest →
    (∀ it, pre.getLast? = some it → it.2.isSome = true) →
    GraphFetch.lastCycL ls = some Wlabel.LInstr → emFenceI em f :=
  fun he hp hl => ⟨pre, ls, rest, he, hp, hl⟩

/-- Non-vacuity, computed: fence.i's cycle (boundary `LInstr`, fetch, announce `LInstr`, barrier)
is a site. -/
theorem GraphFetch.fenceICycleSite (base : Int) (tvs : List (Nat × BitVec 8)) (fin : Pexv6) :
    emFenceI ⟨eadm [Wlabel.LInstr, Wlabel.LIFetch base tvs, Wlabel.LInstr] ++
      [(Wlabel.LFence false false false false, some 0)], fin⟩ 0 :=
  GraphFetch.emFenceIOfLast _ 0 [] [Wlabel.LInstr, Wlabel.LIFetch base tvs, Wlabel.LInstr] []
    rfl (fun _ h => by cases h) rfl

/-- ... and sfence.vma's (boundary `LInstr`, fetch, marker) does not arm the fold: its block's
latest cycle label is the fetch. -/
theorem GraphFetch.sfenceCycleLast (base : Int) (tvs : List (Nat × BitVec 8)) (b : Bool) :
    GraphFetch.lastCycL [Wlabel.LInstr, Wlabel.LIFetch base tvs] = some (Wlabel.LIFetch base tvs) ∧
      GraphFetch.fiFold b [Wlabel.LInstr, Wlabel.LIFetch base tvs] = false :=
  ⟨rfl, rfl⟩

/-! # 3. The slot content -/

/-- The fence.i contributors of hart `i` at slot `k` (`gzContrib` at the emission's sites;
D41 (a) [OWN.16]). -/
def GraphFetch.emContrib (G : Gexec) (em : Hemission) (i k : Nat) (c : Geid) : Prop :=
  gzContrib G (emFenceI em) i k c

/-- **THE SLOT CONTENT** (`xv6ConfS`'s fetch clause; `Weak.emZifencei` in `WeakRvwmoFab`): every
administrative fetch item of hart `i`'s emission satisfies the trusted-base item `gzFetch` at its
real slot tag [OWN.26], with the emission's fence.i contributors. -/
def GraphFetch.emZif (G : Gexec) (i : Nat) (em : Hemission) : Prop :=
  GraphFetchSpike.emZifencei G (GraphFetch.emContrib G em i) i em

/-! # 4. The kernel-text instance (D43 (a) [OWN.18]) -/

/-- A pinned fetch (tag 0, the image's bytes) of bytes the graph never writes satisfies the
trusted-base item at any contributor set: (Z1) is the image byte, (Z2) is vacuous (index 0 names
no write), (Z3) is vacuous (no write to the bytes). -/
theorem GraphFetch.gzFetchOfPin (G : Gexec) (C : Geid → Prop) (i k : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) :
    WeakAxRealize.fetchPin G.gxImg (Wlabel.LIFetch base tvs) →
    (∀ j, j < tvs.length → ∀ w v, ¬ gwritesByte G w (base + (j : Int)) v) →
    gzFetch G C i k base tvs := by
  rintro ⟨h0, himg⟩ hnw j t v hj
  have hlt : j < tvs.length := lookup_lt_Some hj
  have ht : t = 0 := h0 t (GraphFetchSpike.mapFstOfLookup tvs j t v hj)
  subst ht
  refine ⟨?_, fun w _ hw => (by cases hw), fun w' v' hw' _ => absurd hw' (hnw j hlt w' v')⟩
  rw [logByte0, himg j hlt, List.getElem?_map, hj]
  rfl

/-- The fetched bytes of an emission are unwritten in the graph. -/
def GraphFetch.emFetchUnwritten (G : Gexec) (em : Hemission) : Prop :=
  ∀ (n : Nat) (base : Int) (tvs : List (Nat × BitVec 8)),
    em.emItems[n]? = some (Wlabel.LIFetch base tvs, none) →
    ∀ j, j < tvs.length → ∀ w v, ¬ gwritesByte G w (base + (j : Int)) v

/-- **THE KERNEL-TEXT INSTANCE OF THE SLOT**: a pinned emission (`emFetchImg`, the stage-C
clause) whose fetched bytes the graph never writes satisfies the Zifencei slot content, at any
contributor set. -/
theorem GraphFetch.emZifOfPin (G : Gexec) (C : Nat → Geid → Prop) (i : Nat) (em : Hemission) :
    emFetchImg G.gxImg em → GraphFetch.emFetchUnwritten G em →
    GraphFetchSpike.emZifencei G C i em := by
  intro hpin hnw n base tvs hn
  refine GraphFetch.gzFetchOfPin G _ i _ base tvs (hpin _ ?_) (hnw n base tvs hn)
  unfold emLabels
  exact List.mem_map.2 ⟨_, List.mem_of_getElem? hn, rfl⟩

/-- The kernel-text instance at the bundle's contributors. -/
theorem GraphFetch.emZifOfPinC (G : Gexec) (i : Nat) (em : Hemission) :
    emFetchImg G.gxImg em → GraphFetch.emFetchUnwritten G em → GraphFetch.emZif G i em :=
  GraphFetch.emZifOfPin G _ i em

end Weak
