/-
Weak: **W5d-G G6-3 (= W11 (iii)), layer L1 — the UNPINNED supply: the leading stars built from the
emission, and `topoSupplyZ`** (plan `notes/weak-allocproc-plan.md` rev 51, §C top "W5d-G G6 — LAUNCH
PLAN [rev 50]", paragraph "G6-3 = W11 (iii)"; D27 RULED (a) [OWN.6], D42–D43 (a) [OWN.18]).
Lean-only, no Rocq twin.

The PINNED supply (`topoSupply` `WeakRvwmoSupply.lean`, `fconfRealize` `WeakRvwmoFabInd.lean`)
realizes a graph's rule-14 linearization at the PINNED program LTS `pstepPin im pstepEv` with the
plain conformance predicate `execProgOk'`.  M2 (`srvwmoXv6M2Premises`, `Weak/PfRunUnpinned.lean`)
wants the SHAPED, UNPINNED predicate `execProgOk'SC pstepEv pclsEv fokTriv (fcutEM2 cohSrc E itvOf
fiOf)` (and its shadow form `execProgOk'STC`).  This file supplies it from a Zifencei fabric bundle
(`GraphFabConf.gfexecConfZF`, what `xv6ConfSZForget` returns):

  §1  the two EMISSION premises the shaped predicate needs and no bundle carries (below);
  §2  the shaped block `GraphFetchBlocks.hblkS` (the star as a label-carrying `admRunG`, the left
      arm `lbFused`) and its two halves `blkOne`/`blkPair`;
  §3  **`GraphFetchBlocks.hemitfBlocks`** — from a `hemitf` derivation, per row slot: the program
      states, THE LEADING STAR'S LABELS (`g n`, the emission's administrative block of slot `n`)
      and the row item (`r n`), the block's POSITION in the emission (`GraphFetch.emBlock`), the
      block at its two fabric endpoints and, when contact-free, at ANY fabric;
  §4  `GraphFetchBlocks.rowBlocks` — per row: `GraphFetch.emBlockF` (the block premise of G5's
      supply) DISCHARGED from the emission, modulo the fence-block premise (§1), and the shaped
      blocks at the global fabric (members) / any fabric (non-members);
  §5  **`GraphFetchBlocks.supplyOfFconfZ`** — the interleaving theorem (`supplyOfFconf`'s twin) at
      the UNPINNED LTS, producing `execProgOk'SC` at any per-index clause the stars satisfy;
  §6  **`topoSupplyZ`** — the composition with G5's `GraphFetch.normalizeFetchSupply`: a
      `racyDIO`-acyclic core Zifencei bundle normalizes to `GF'` whose rule-14 linearization
      `linCand GF'.gfGd.gdG` carries, under the guard `trDevOrdered` (as `fconfRealize`), M2's
      conjunct `execProgOk'SC pstepEv pclsEv fokTriv (fcutEM2 cohSrc (candExec c) itvOfL fiOfL)`
      with M2's boot values, and `candScaT` (`linCandScaTMinus`); `topoSupplyZT` adds
      `candDiskLat` to reach `execProgOk'STC` (M2's conjunct verbatim).

**The leading stars `lsOf`** (plan: "`lsOf` built from `hemit`").  `lsOf K` is the administrative
block of the trace step `K`'s slot in its hart's emission: hart `s.esAg`'s chosen block function
`g` at the hart's own count `tcnt s.esAg (take K)` (= the slot `k` of `(i, k)`, G5's
`GraphFetchFloor.ownCount`).  The SAME function `g` is the supply's leading star, so the per-index
clause G5 proves for `lsOf` (`GraphFetch.normalizeFetchSupply`) is the one `execProgOk'SC` reads.

**The two emission premises (§1) — NOT in any bundle; named here, spec-first.**
(P1) `GraphFetchBlocks.emFenceCyc em` — between the previous row item and a `LFence false×4` row
  item the emission has a cycle label (`LInstr`/`LIFetch`): the second conjunct of G5's `emBlockF`
  (`lastCycL ls ≠ none`).  The plan (G6-3, "`emBlockF` discharged from the Sail cycle") expected it
  from `cycleOkBoot` (`SailCycleOrderK.lean:251`) by `hemit`-induction.  It does NOT follow:
  `SailCycleOrderK.good` tracks the PHASE (the latest own cycle label) and lets every data read /
  write keep the phase (`:159-168`), so it does not say that no ROW event lies between that label
  and the fence.  What holds on Sail: `LFence false×4` is `ebarLabel Barrier_RISCV_i` (`ebarNow`
  maps every other barrier kind to a non-zero fence, `WeakEvInst.lean:741-753`) or the SFENCE.VMA
  announce marker (`annLabel`); `execute FENCEI` is the one barrier after its own announce and
  the marker follows the instruction's own fetch with no memory node between.  Proving it needs a
  refined residual invariant (the phase plus a "row event since" bit) walked over the cycle — a
  W-SCO-sized extension.  Spec-first: RVWMO/riscv.cat/Zifencei/PMAs are silent (block structure
  is the pf LTS's); Sail is the reference.  (a) prove it from Sail (the refined walk) — FAITHFUL,
  not done here (size M–L); (b) widen G1's `emFenceI` to the emission-wide latest cycle label —
  STRONGER trusted fetch text on non-Sail emissions (G5 deviation 3 (b)), not taken; (c) THIS
  FILE: a named premise of the supply, universally over the hart's emissions (a statement about
  Sail emissions, no trusted text) — interim, WEAKER until (a).
(P2) `GraphFetchBlocks.emNoDangle em` — every tagged `LExLoad` row item has an `LExStore` row
  item of the same slot (no DANGLING exclusive read).  `execProgOk'SC`'s clause (i) asks the left
  arm's realizing label to be `lbFused`; a `hemitf` `HFone` block may realize a plain `LLoad` by a
  dangling `LExLoad` (`hlblRealizes` admits it, `lbNobarex`), which no bundle excludes.  This is
  the plan's EXISTING candidate restriction D19 ("a dangling LR or failing SC is outside the
  theorem", §B(11); [R2.3-alt]), moved from the candidate to the emission: EQUAL to M2's clause (i),
  a scope restriction w.r.t. RVWMO (an LR without SC is legal); the kernel image has no LR/SC
  (`KernelSitesDef.lean:388`), user text is unconstrained.  Stated per graph row.

**Deviations from the plan text.**  (1) FILE PLACEMENT (G5's deviation 1): the Z-twins cannot sit
in `WeakRvwmoSupply`/`LinInd`/`FabInd`/`CatLinChain` — `PfRunUnpinned.fcutEM2` and
`GraphFetch.normalizeFetchSupply` are ABOVE them (`GraphFetchSupply` imports `LinInd`, `FabInd`,
`Glue`, `Cert4`, `KillIO`), so every twin is in a NEW leaf; the pinned chain and the registered cone
are untouched.  (2) `topoSupplyZ` is the FABRIC twin (`fconfRealize`'s statement shape over
`gfexecConfZF`, the trace-order guard `trDevOrdered` kept as a guard): the Zifencei bundles are
fabric bundles (`xv6ConfSZ`), there is no quiescent Zifencei bundle, and G5's supply needs
`racyDIO`-acyclicity (`normalizeOfAcyclicZ`).  (3) The trace is the RULE-14 linearization
`linCand` (G5's); `candDiskLat` is PROVED on the anchored `linCandIO` only
(`RvwmoXv6ScaT.linCandDiskLat`), so `topoSupplyZT` takes it as a premise.  (4) §1's premises.

Spec marks.  No new trusted text: (P1) is a Sail fact stated as a premise (interim), (P2) is D19;
everything else is proof organisation (FAITHFUL).  Lean-only helpers are file-qualified
(`GraphFetchBlocks.*`).
-/
import Weak.GraphFetchSupply
import Weak.GraphFabConf
import Weak.RvwmoXv6ScaT

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. The two emission premises -/

/-- (P1) Between the previous row item and every `LFence false×4` row item, the emission has an
administrative cycle label (`LInstr`/`LIFetch`). -/
def GraphFetchBlocks.emFenceCyc (em : Hemission) : Prop :=
  ∀ (n k : Nat), em.emItems[n]? = some (Wlabel.LFence false false false false, some k) →
    ∃ (m : Nat) (l : Wlabel), m < n ∧ em.emItems[m]? = some (l, none) ∧ GraphFetch.lbCyc l = true ∧
      ∀ m', m < m' → m' < n → ∃ l', em.emItems[m']? = some (l', none)

/-- (P2, D19) Every tagged exclusive read has an exclusive write of the same slot: no dangling
`LExLoad`. -/
def GraphFetchBlocks.emNoDangle (em : Hemission) : Prop :=
  ∀ (n : Nat) (aq : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc) (k : Nat),
    em.emItems[n]? = some (Wlabel.LExLoad aq base tvs asrc, some k) →
    ∃ (n' : Nat) (rl : Bool) (base' : Int) (data : List (BitVec 8)) (asrc' vsrc' : List Dsrc),
      em.emItems[n']? = some (Wlabel.LExStore rl base' data asrc' vsrc', some k)

theorem GraphFetchBlocks.emItemsRen (π : Nat → Nat) (em : Hemission) (n : Nat) :
    (emRen π em).emItems[n]? = (em.emItems[n]?).map (eitemRen π) := by
  show (em.emItems.map (eitemRen π))[n]? = _
  rw [List.getElem?_map]

theorem GraphFetchBlocks.lbCycRen (π : Nat → Nat) (l : Wlabel) :
    GraphFetch.lbCyc (wlblRen π l) = GraphFetch.lbCyc l := by
  cases l <;> rfl

theorem GraphFetchBlocks.renFence (π : Nat → Nat) (l : Wlabel) (pr pw sr sw : Bool) :
    wlblRen π l = Wlabel.LFence pr pw sr sw → l = Wlabel.LFence pr pw sr sw := by
  cases l <;> simp [wlblRen]

theorem GraphFetchBlocks.renExLoad (π : Nat → Nat) (l : Wlabel) (aq : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc) :
    wlblRen π l = Wlabel.LExLoad aq base tvs asrc → ∃ tvs0, l = Wlabel.LExLoad aq base tvs0 asrc := by
  intro h
  cases l <;> simp only [wlblRen, reduceCtorEq, Wlabel.LExLoad.injEq] at h
  obtain ⟨rfl, rfl, -, rfl⟩ := h
  exact ⟨_, rfl⟩

/-- An item lookup in a renamed emission is a renamed lookup. -/
theorem GraphFetchBlocks.itemRenInv (π : Nat → Nat) (em : Hemission) (n : Nat) (l : Wlabel)
    (o : Option Nat) :
    (emRen π em).emItems[n]? = some (l, o) → ∃ l0, em.emItems[n]? = some (l0, o) ∧ l = wlblRen π l0 := by
  rw [GraphFetchBlocks.emItemsRen]
  cases h : em.emItems[n]? with
  | none => simp
  | some it =>
    obtain ⟨l0, o0⟩ := it
    intro he
    simp only [Option.map_some, Option.some.injEq, eitemRen, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨l0, rfl, rfl⟩

theorem GraphFetchBlocks.itemRen (π : Nat → Nat) (em : Hemission) (n : Nat) (l : Wlabel)
    (o : Option Nat) :
    em.emItems[n]? = some (l, o) → (emRen π em).emItems[n]? = some (wlblRen π l, o) := by
  intro h
  rw [GraphFetchBlocks.emItemsRen, h]
  rfl

theorem GraphFetchBlocks.emFenceCycRen (π : Nat → Nat) (em : Hemission) :
    GraphFetchBlocks.emFenceCyc em → GraphFetchBlocks.emFenceCyc (emRen π em) := by
  intro h n k hn
  obtain ⟨l0, hit, hl⟩ := GraphFetchBlocks.itemRenInv π em n _ _ hn
  rw [GraphFetchBlocks.renFence π l0 _ _ _ _ hl.symm] at hit
  obtain ⟨m, l, hm, hml, hc, hmid⟩ := h n k hit
  refine ⟨m, wlblRen π l, hm, GraphFetchBlocks.itemRen π em m l none hml,
    by rw [GraphFetchBlocks.lbCycRen]; exact hc, fun m' h1 h2 => ?_⟩
  obtain ⟨l', hl'⟩ := hmid m' h1 h2
  exact ⟨wlblRen π l', GraphFetchBlocks.itemRen π em m' l' none hl'⟩

theorem GraphFetchBlocks.emNoDangleRen (π : Nat → Nat) (em : Hemission) :
    GraphFetchBlocks.emNoDangle em → GraphFetchBlocks.emNoDangle (emRen π em) := by
  intro h n aq base tvs asrc k hn
  obtain ⟨l0, hit, hl⟩ := GraphFetchBlocks.itemRenInv π em n _ _ hn
  obtain ⟨tvs0, rfl⟩ := GraphFetchBlocks.renExLoad π l0 aq base tvs asrc hl.symm
  obtain ⟨n', rl, base', data, asrc', vsrc', hn'⟩ := h n aq base tvs0 asrc k hit
  exact ⟨n', rl, base', data, asrc', vsrc', GraphFetchBlocks.itemRen π em n' _ _ hn'⟩

/-! # 2. The shaped block -/

/-- A single-step block: the label-carrying leading star `ls`, then the realizing step `l`. -/
def GraphFetchBlocks.blkOne (d d' : Efab) (ws : Wstate) (lb : Lbl) (ls : List Wlabel) (l : Wlabel)
    (p p' : Pexv6) : Prop :=
  ∃ (pa : Pexv6) (da : Efab),
    admRunG pstepEv true p d ls pa da ∧ hlblRealizes pa ws lb l ∧ pstepEv pa da l p' d'

/-- A pair block: the leading star `ls`, the exclusive read `l`, an `LInstr`-free star, the
exclusive write. -/
def GraphFetchBlocks.blkPair (d d' : Efab) (ws : Wstate) (lb : Lbl) (ls : List Wlabel) (l : Wlabel)
    (p p' : Pexv6) : Prop :=
  ∃ (pa : Pexv6) (da : Efab) (pm : Pexv6) (dm : Efab) (ls2 : List Wlabel) (pm2 : Pexv6) (dm2 : Efab)
    (l2 : Wlabel),
    admRunG pstepEv true p d ls pa da ∧ hlblRealizesPair pa pm2 ws lb l l2 ∧
    pstepEv pa da l pm dm ∧ admRunG pstepEv false pm dm ls2 pm2 dm2 ∧ pstepEv pm2 dm2 l2 p' d'

/-- THE SHAPED BLOCK (`execProgOk'SC`'s per-index block at the leading star `ls`). -/
def GraphFetchBlocks.hblkS (d d' : Efab) (ws : Wstate) (lb : Lbl) (ls : List Wlabel)
    (p p' : Pexv6) : Prop :=
  ∃ (pa : Pexv6) (da : Efab),
    admRunG pstepEv true p d ls pa da ∧
    ((∃ l, lbFused l ∧ hlblRealizes pa ws lb l ∧ pstepEv pa da l p' d') ∨
     (∃ (pm : Pexv6) (dm : Efab) (ls2 : List Wlabel) (pm2 : Pexv6) (dm2 : Efab) (l1 l2 : Wlabel),
        hlblRealizesPair pa pm2 ws lb l1 l2 ∧ pstepEv pa da l1 pm dm ∧
        admRunG pstepEv false pm dm ls2 pm2 dm2 ∧ pstepEv pm2 dm2 l2 p' d'))

theorem GraphFetchBlocks.hblkSOne (d d' : Efab) (ws : Wstate) (lb : Lbl) (ls : List Wlabel)
    (l : Wlabel) (p p' : Pexv6) :
    lbFused l → GraphFetchBlocks.blkOne d d' ws lb ls l p p' → GraphFetchBlocks.hblkS d d' ws lb ls p p' := by
  rintro hf ⟨pa, da, h1, h2, h3⟩
  exact ⟨pa, da, h1, .inl ⟨l, hf, h2, h3⟩⟩

theorem GraphFetchBlocks.hblkSPair (d d' : Efab) (ws : Wstate) (lb : Lbl) (ls : List Wlabel)
    (l : Wlabel) (p p' : Pexv6) :
    GraphFetchBlocks.blkPair d d' ws lb ls l p p' → GraphFetchBlocks.hblkS d d' ws lb ls p p' := by
  rintro ⟨pa, da, pm, dm, ls2, pm2, dm2, l2, h1, h2, h3, h4, h5⟩
  exact ⟨pa, da, h1, .inr ⟨pm, dm, ls2, pm2, dm2, l, l2, h2, h3, h4, h5⟩⟩

/-- The contact-recording run forgets to the generic label-carrying run. -/
theorem GraphFetchBlocks.admRunGOfT (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel)
    (p' : Pexv6) (d' : Efab) (b : Bool) :
    WeakRvwmoFab.admRunT instr p d ls p' d' b → admRunG pstepEv instr p d ls p' d' := by
  intro h
  induction h with
  | ATnil p d => exact .nil p d
  | ATcons p d l p1 d1 ls p' d' b ha hs _ ih => exact .cons p d l p1 d1 ls p' d' ha hs ih

/-! # 3. The per-slot extraction -/

/-- A list whose last element sits after a tagged item, the rest tagged at its end. -/
theorem GraphFetchBlocks.lastTagged (A B : List Eitem) (x : Eitem) :
    x.2.isSome = true → (∀ it, B.getLast? = some it → it.2.isSome = true) →
    ∀ it, (A ++ x :: B).getLast? = some it → it.2.isSome = true := by
  intro hx hB it h
  rw [List.getLast?_append, List.getLast?_cons] at h
  cases hb : B.getLast? with
  | none =>
    simp [hb] at h
    subst h
    exact hx
  | some y =>
    simp [hb] at h
    subst h
    exact hB y hb

/-- An untagged block item has no slot tag. -/
theorem GraphFetchBlocks.eadmTagNone (ls : List Wlabel) (it : Eitem) : it ∈ eadm ls → it.2 = none := by
  intro h
  simp only [eadm, List.mem_map] at h
  obtain ⟨_, _, rfl⟩ := h
  rfl

/-- **THE EXTRACTION**: per row slot `n` of a `hemitf` derivation at offset `k` — the program
state `f n`, the leading star's labels `g n` and the row item `r n`; the block's position in the
emission; its two fabric endpoints and, contact-free, any fabric; and the arm: a single step (whose
realizing item is the ONLY item of its slot) or a pair. -/
theorem GraphFetchBlocks.hemitfBlocks (dvi dvo : Nat → Efab) (tq : Nat → Bool) (k : Nat)
    (ws : Wstate) (row : List Lbl) (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemitf dvi dvo tq k ws row p es pfin →
    ∃ (f : Nat → Pexv6) (g : Nat → List Wlabel) (r : Nat → Wlabel), f 0 = p ∧
      ∀ n lb, row[n]? = some lb →
        (∃ pre rest, es = pre ++ eadm (g n) ++ (r n, some (n + k)) :: rest ∧
          ∀ it, pre.getLast? = some it → it.2.isSome = true) ∧
        (tq (n + k) = false → dvo (n + k) = dvi (n + k) ∧ lbIsIo lb = false) ∧
        ((GraphFetchBlocks.blkOne (dvi (n + k)) (dvo (n + k)) (rowWsAux k ws (row.take n)) lb
              (g n) (r n) (f n) (f (n + 1)) ∧
            (tq (n + k) = false → ∀ d, GraphFetchBlocks.blkOne d d (rowWsAux k ws (row.take n)) lb
              (g n) (r n) (f n) (f (n + 1))) ∧
            ∀ it, it ∈ es → it.2 = some (n + k) → it.1 = r n) ∨
         (GraphFetchBlocks.blkPair (dvi (n + k)) (dvo (n + k)) (rowWsAux k ws (row.take n)) lb
              (g n) (r n) (f n) (f (n + 1)) ∧
            (tq (n + k) = false → ∀ d, GraphFetchBlocks.blkPair d d (rowWsAux k ws (row.take n)) lb
              (g n) (r n) (f n) (f (n + 1))))) := by
  intro h
  induction h with
  | HFnil k ws p =>
    exact ⟨fun _ => p, fun _ => [], fun _ => Wlabel.LSilent, rfl, fun n lb hn => by simp at hn⟩
  | HFone k ws lb row p ls pa da l p' es pfin b har hre hst htq hem ih =>
    obtain ⟨f', g', r', hf0, hf⟩ := ih
    refine ⟨fun n => match n with | 0 => p | n' + 1 => f' n',
      fun n => match n with | 0 => ls | n' + 1 => g' n',
      fun n => match n with | 0 => l | n' + 1 => r' n', rfl, ?_⟩
    intro n lb0 hn
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst hn
      have hio : pdevEv pa l p' = false → lbIsIo lb = false := by
        intro hpl
        cases hc : lbIsIo lb with
        | false => rfl
        | true =>
          rw [WeakRvwmoFab.realizesIoTouch pa ws lb l p' hre hc] at hpl
          exact absurd hpl (by decide)
      have hst' : pstepEv pa da l (f' 0) (dvo k) := by rw [hf0]; exact hst
      have hq : tq k = false → dvo k = dvi k ∧ lbIsIo lb = false ∧
          ∀ d, GraphFetchBlocks.blkOne d d ws lb ls l p (f' 0) := by
        intro hk
        rw [hk] at htq
        obtain ⟨hb, hpl⟩ := Bool.or_eq_false_iff.mp htq.symm
        obtain ⟨hda, hall0⟩ := WeakRvwmoFab.admRunTQuiet _ _ _ _ _ _ _ har hb
        obtain ⟨hd, hall⟩ := pdevEvOk pa da l p' (dvo k) hst hpl
        refine ⟨by rw [hd, hda], hio hpl, fun d => ⟨pa, d,
          GraphFetchBlocks.admRunGOfT _ _ _ _ _ _ _ (hall0 d), hre, ?_⟩⟩
        rw [hf0]; exact hall d
      simp only [Nat.zero_add]
      refine ⟨⟨[], es, by simp, fun it h => by simp at h⟩,
        fun hk => ⟨(hq hk).1, (hq hk).2.1⟩,
        Or.inl ⟨⟨pa, da, GraphFetchBlocks.admRunGOfT _ _ _ _ _ _ _ har, hre, hst'⟩,
          fun hk => (hq hk).2.2, fun it hit htag => ?_⟩⟩
      rcases List.mem_append.1 hit with hit | hit
      · rw [GraphFetchBlocks.eadmTagNone ls it hit] at htag
        exact absurd htag (by simp)
      · rcases List.mem_cons.1 hit with rfl | hit
        · rfl
        · have := hemitfTagGe _ _ _ _ _ _ _ _ _ it k hem hit htag
          omega
    | succ n =>
      simp only [List.getElem?_cons_succ] at hn
      obtain ⟨⟨pre, rest, hes, hpre⟩, hq, harm⟩ := hf n lb0 hn
      have e : n + 1 + k = n + (k + 1) := by omega
      rw [e]
      refine ⟨⟨eadm ls ++ (l, some k) :: pre, rest, by rw [hes]; simp,
        GraphFetchBlocks.lastTagged _ _ _ rfl hpre⟩, hq, ?_⟩
      rcases harm with ⟨h1, h2, h3⟩ | h4
      · refine Or.inl ⟨h1, h2, fun it hit htag => ?_⟩
        rcases List.mem_append.1 hit with hit | hit
        · rw [GraphFetchBlocks.eadmTagNone ls it hit] at htag
          exact absurd htag (by simp)
        · rcases List.mem_cons.1 hit with rfl | hit
          · simp only [Option.some.injEq] at htag
            omega
          · exact h3 it hit htag
      · exact Or.inr h4
  | HFpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin b1 b2 har1 hre hst1 har2
      hst2 htq hem ih =>
    obtain ⟨f', g', r', hf0, hf⟩ := ih
    refine ⟨fun n => match n with | 0 => p | n' + 1 => f' n',
      fun n => match n with | 0 => ls1 | n' + 1 => g' n',
      fun n => match n with | 0 => l1 | n' + 1 => r' n', rfl, ?_⟩
    intro n lb0 hn
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst hn
      have hio : lbIsIo lb = false := by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hlb⟩ := hre
        rw [hlb]; rfl
      have hst2' : pstepEv pm2 dm2 l2 (f' 0) (dvo k) := by rw [hf0]; exact hst2
      have hq : tq k = false → dvo k = dvi k ∧
          ∀ d, GraphFetchBlocks.blkPair d d ws lb ls1 l1 p (f' 0) := by
        intro hk
        rw [hk] at htq
        have htq' := htq.symm
        simp only [Bool.or_eq_false_iff] at htq'
        obtain ⟨⟨⟨hb1, hp1⟩, hb2⟩, hp2⟩ := htq'
        obtain ⟨hda, hall1a⟩ := WeakRvwmoFab.admRunTQuiet _ _ _ _ _ _ _ har1 hb1
        obtain ⟨hdm, hall1⟩ := pdevEvOk pa da l1 pm dm hst1 hp1
        obtain ⟨hdm2, hall2a⟩ := WeakRvwmoFab.admRunTQuiet _ _ _ _ _ _ _ har2 hb2
        obtain ⟨hd2, hall2⟩ := pdevEvOk pm2 dm2 l2 p' (dvo k) hst2 hp2
        refine ⟨by rw [hd2, hdm2, hdm, hda], fun d => ⟨pa, d, pm, d, ls2, pm2, d, l2,
          GraphFetchBlocks.admRunGOfT _ _ _ _ _ _ _ (hall1a d), hre, hall1 d,
          GraphFetchBlocks.admRunGOfT _ _ _ _ _ _ _ (hall2a d), ?_⟩⟩
        rw [hf0]; exact hall2 d
      simp only [Nat.zero_add]
      exact ⟨⟨[], eadm ls2 ++ (l2, some k) :: es, by simp, fun it h => by simp at h⟩,
        fun hk => ⟨(hq hk).1, hio⟩,
        Or.inr ⟨⟨pa, da, pm, dm, ls2, pm2, dm2, l2,
          GraphFetchBlocks.admRunGOfT _ _ _ _ _ _ _ har1, hre, hst1,
          GraphFetchBlocks.admRunGOfT _ _ _ _ _ _ _ har2, hst2'⟩, fun hk => (hq hk).2⟩⟩
    | succ n =>
      simp only [List.getElem?_cons_succ] at hn
      obtain ⟨⟨pre, rest, hes, hpre⟩, hq, harm⟩ := hf n lb0 hn
      have e : n + 1 + k = n + (k + 1) := by omega
      rw [e]
      refine ⟨⟨eadm ls1 ++ (l1, some k) :: (eadm ls2 ++ (l2, some k) :: pre), rest,
        by rw [hes]; simp,
        GraphFetchBlocks.lastTagged _ _ _ rfl (GraphFetchBlocks.lastTagged _ _ _ rfl hpre)⟩, hq, ?_⟩
      rcases harm with ⟨h1, h2, h3⟩ | h4
      · refine Or.inl ⟨h1, h2, fun it hit htag => ?_⟩
        rcases List.mem_append.1 hit with hit | hit
        · rw [GraphFetchBlocks.eadmTagNone ls1 it hit] at htag
          exact absurd htag (by simp)
        rcases List.mem_cons.1 hit with rfl | hit
        · simp only [Option.some.injEq] at htag
          omega
        rcases List.mem_append.1 hit with hit | hit
        · rw [GraphFetchBlocks.eadmTagNone ls2 it hit] at htag
          exact absurd htag (by simp)
        rcases List.mem_cons.1 hit with rfl | hit
        · simp only [Option.some.injEq] at htag
          omega
        · exact h3 it hit htag
      · exact Or.inr h4

/-! # 4. Per row: `emBlockF` and the shaped blocks -/

/-- The fence-block premise (P1) at a block: a cycle label lies inside the block. -/
theorem GraphFetchBlocks.cycInBlock (pre : List Eitem) (ls : List Wlabel) (x : Eitem)
    (rest : List Eitem) :
    (∀ it, pre.getLast? = some it → it.2.isSome = true) →
    (∃ (m : Nat) (l : Wlabel), m < pre.length + ls.length ∧
      (pre ++ eadm ls ++ x :: rest)[m]? = some (l, none) ∧ GraphFetch.lbCyc l = true ∧
      ∀ m', m < m' → m' < pre.length + ls.length →
        ∃ l', (pre ++ eadm ls ++ x :: rest)[m']? = some (l', none)) →
    GraphFetch.lastCycL ls ≠ none := by
  intro hpre ⟨m, l, hm, hml, hc, hmid⟩
  have hlen : (eadm ls).length = ls.length := by simp [eadm]
  by_cases hge : pre.length ≤ m
  · rw [List.append_assoc, List.getElem?_append_right hge,
      List.getElem?_append_left (by omega)] at hml
    simp only [eadm, List.getElem?_map] at hml
    cases hj : ls[m - pre.length]? with
    | none => rw [hj] at hml; simp at hml
    | some l' =>
      rw [hj] at hml
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hml
      obtain ⟨rfl, -⟩ := hml
      have hmem : l' ∈ ls.filter GraphFetch.lbCyc :=
        List.mem_filter.2 ⟨List.mem_of_getElem? hj, hc⟩
      unfold GraphFetch.lastCycL
      intro hnone
      rw [List.getLast?_eq_none_iff] at hnone
      rw [hnone] at hmem
      exact absurd hmem List.not_mem_nil
  · exfalso
    have hpl : 0 < pre.length := by omega
    have hlast : pre.getLast? = pre[pre.length - 1]? := List.getLast?_eq_getElem?
    obtain ⟨it, hit⟩ : ∃ it, pre[pre.length - 1]? = some it :=
      someOfIsSome (lookup_lt_is_Some_2 (by omega))
    have htag := hpre it (by rw [hlast, hit])
    have hat : (pre ++ eadm ls ++ x :: rest)[pre.length - 1]? = some it := by
      rw [List.append_assoc, List.getElem?_append_left (by omega), hit]
    by_cases heq : m = pre.length - 1
    · subst heq
      rw [hat] at hml
      simp only [Option.some.injEq] at hml
      subst hml
      simp at htag
    · obtain ⟨l', hl'⟩ := hmid (pre.length - 1) (by omega) (by omega)
      rw [hat] at hl'
      simp only [Option.some.injEq] at hl'
      subst hl'
      simp at htag

/-- **THE PER-ROW BLOCK DATA** at a renamed (or any) row: the leading stars `g`, the emission's
block premise `GraphFetch.emBlockF` modulo (P1), the left arm `lbFused` by (P2), the shaped
blocks at the global fabric `fab` (members of `dev`) and at any fabric (non-members). -/
theorem GraphFetchBlocks.rowBlocks (G : Gexec) (i : Nat) (row : List Lbl) (p0 : Pexv6)
    (dvi dvo : Nat → Efab) (tq : Nat → Bool) (em : Hemission) (dev : List Geid)
    (fab : Nat → Efab) :
    hartConff i row p0 dvi dvo tq em →
    GraphFetchBlocks.emFenceCyc em → GraphFetchBlocks.emNoDangle em →
    (∀ n, n < row.length → (i, n) ∉ dev → tq n = false) →
    (∀ n m, dev[m]? = some (i, n) → dvi n = fab m ∧ dvo n = fab (m + 1)) →
    (∀ n lb, row[n]? = some lb → glbl G (i, n) = lb) →
    ∃ (f : Nat → Pexv6) (g : Nat → List Wlabel), f 0 = p0 ∧
      ∀ n lb, row[n]? = some lb →
        GraphFetch.emBlockF G em i n (g n) ∧
        (∀ m, dev[m]? = some (i, n) →
          GraphFetchBlocks.hblkS (fab m) (fab (m + 1)) (rowWs row n) lb (g n) (f n) (f (n + 1))) ∧
        ((i, n) ∉ dev → ∀ d, GraphFetchBlocks.hblkS d d (rowWs row n) lb (g n) (f n) (f (n + 1))) := by
  intro hem hfc hnd hnm hpin hgl
  have hem' : hemitf dvi dvo tq 0 wsInit row p0 em.emItems em.emFin := hem
  obtain ⟨f, g, r, hf0, hf⟩ := GraphFetchBlocks.hemitfBlocks _ _ _ _ _ _ _ _ _ hem'
  refine ⟨f, g, hf0, fun n lb hn => ?_⟩
  obtain ⟨⟨pre, rest, hes, hpre⟩, hq, harm⟩ := hf n lb hn
  simp only [Nat.add_zero] at hes hq harm
  have hws : rowWsAux 0 wsInit (row.take n) = rowWs row n := rfl
  rw [hws] at harm
  have hlt : n < row.length := lookup_lt_Some hn
  -- the left arm's realizing label is fused (P2)
  have hfused : (∀ it', it' ∈ em.emItems → it'.2 = some n → it'.1 = r n) → lbFused (r n) := by
    intro huniq
    cases hr : r n
    case LExLoad aq base tvs asrc =>
      exfalso
      have hidx : em.emItems[pre.length + (g n).length]? = some (r n, some n) := by
        rw [hes, List.append_assoc, List.getElem?_append_right (by omega)]
        have : pre.length + (g n).length - pre.length = (eadm (g n)).length := by simp [eadm]
        rw [this, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
      rw [hr] at hidx
      obtain ⟨n', rl, base', data, asrc', vsrc', hn'⟩ := hnd _ aq base tvs asrc n hidx
      have h1 := huniq _ (List.mem_of_getElem? hn') rfl
      rw [hr] at h1
      simp at h1
    case LExStore rl base data asrc vsrc =>
      exfalso
      rcases harm with ⟨⟨pa, da, -, ⟨hnb, -⟩, -⟩, -⟩ | ⟨⟨pa, da, pm, dm, ls2, pm2, dm2, l2, -, hpr, -⟩, -⟩
      · rw [hr] at hnb; exact hnb
      · obtain ⟨_, _, _, _, _, _, _, _, h1, -⟩ := hpr
        rw [hr] at h1; simp at h1
    all_goals simp [lbFused]
  refine ⟨⟨r n, ⟨pre, rest, hes, hpre⟩, fun hfen => ?_⟩, fun m hm => ?_, fun hnin d => ?_⟩
  · rw [hgl n lb hn] at hfen
    subst hfen
    have hrn : r n = Wlabel.LFence false false false false := by
      rcases harm with ⟨⟨pa, da, -, ⟨-, -, -, hpr⟩, -⟩, -⟩ | ⟨⟨pa, da, pm, dm, ls2, pm2, dm2, l2, -, hpr, -⟩, -⟩
      · exact GraphFetchSupply.projFence _ _ _ _ _ _ hpr
      · obtain ⟨_, _, _, _, _, _, _, _, -, -, -, -, hlb⟩ := hpr
        simp at hlb
    refine ⟨hrn, ?_⟩
    have hidx : em.emItems[pre.length + (g n).length]? =
        some (Wlabel.LFence false false false false, some n) := by
      rw [hes, List.append_assoc, List.getElem?_append_right (by omega)]
      have : pre.length + (g n).length - pre.length = (eadm (g n)).length := by simp [eadm]
      rw [this, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, hrn]
      rfl
    obtain ⟨m, l, hm, hml, hc, hmid⟩ := hfc _ n hidx
    refine GraphFetchBlocks.cycInBlock pre (g n) (r n, some n) rest hpre ⟨m, l, hm, ?_, hc, ?_⟩
    · rw [← hes]; exact hml
    · intro m' h1 h2
      rw [← hes]; exact hmid m' h1 h2
  · obtain ⟨hi, ho⟩ := hpin n m hm
    rw [← hi, ← ho]
    rcases harm with ⟨h1, -, h3⟩ | ⟨h1, -⟩
    · exact GraphFetchBlocks.hblkSOne _ _ _ _ _ _ _ _ (hfused h3) h1
    · exact GraphFetchBlocks.hblkSPair _ _ _ _ _ _ _ _ h1
  · have htq := hnm n hlt hnin
    rcases harm with ⟨-, h2, h3⟩ | ⟨-, h2⟩
    · exact GraphFetchBlocks.hblkSOne _ _ _ _ _ _ _ _ (hfused h3) (h2 htq d)
    · exact GraphFetchBlocks.hblkSPair _ _ _ _ _ _ _ _ (h2 htq d)

/-! # 5. THE INTERLEAVING THEOREM at the unpinned LTS -/

/-- **`supplyOfFconf`'s twin at the UNPINNED LTS, shaped**: per-hart chosen states and leading
stars `F i = (f, g)` whose blocks are shaped (`hblkS`) at the global fabric `fab ∘ dcnt`, a
per-index clause `fcutE` the leading stars satisfy, and the plain loads `scaOk` give
`execProgOk'SC pstepEv pclsEv fokTriv fcutE`. -/
theorem GraphFetchBlocks.supplyOfFconfZ (c : Cand) (boot : Nat → Pexv6) (fab : Nat → Efab)
    (GF : Gfexec) (rows : Nat → List Lbl) (N : Nat)
    (F : Nat → (Nat → Pexv6) × (Nat → List Wlabel))
    (fcutE : Nat → Nat → List Wlabel → Mstate → Prop) :
    (∀ i, (c.cdTr.filter (fun s => decide (s.esAg = i))).map (fun s => s.esLb) = rows i) →
    (∀ i, N ≤ i → rows i = []) →
    (∀ i, i < N → (F i).1 0 = boot i ∧
       ∀ n lb, (rows i)[n]? = some lb →
         (∀ m, GF.gfDev[m]? = some (i, n) →
            GraphFetchBlocks.hblkS (fab m) (fab (m + 1)) (rowWs (rows i) n) lb ((F i).2 n)
              ((F i).1 n) ((F i).1 (n + 1))) ∧
         ((i, n) ∉ GF.gfDev →
            ∀ d, GraphFetchBlocks.hblkS d d (rowWs (rows i) n) lb ((F i).2 n)
              ((F i).1 n) ((F i).1 (n + 1)))) →
    (∀ k s, c.cdTr[k]? = some s →
       (s.esAg, tcnt s.esAg (c.cdTr.take k)) ∈ GF.gfDev →
       GF.gfDev[dcnt GF c.cdTr k]? = some (s.esAg, tcnt s.esAg (c.cdTr.take k))) →
    (∀ k s, c.cdTr[k]? = some s →
       fcutE k s.esAg ((F s.esAg).2 (tcnt s.esAg (c.cdTr.take k))) (stt (candExec c) k)) →
    (∀ k s, c.cdTr[k]? = some s →
       ∀ (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)),
         s.esLb = .LLoad aq base ts vs →
         scaOk (stt (candExec c) k).msImg (stt (candExec c) k).msLog s.esAg base ts) →
    ∃ pst : Nat → List Pexv6,
      pst 0 = (List.range' 0 N).map boot ∧
      execProgOk'SC pstepEv pclsEv PfRunUnpinned.fokTriv fcutE pst
        (fun k => fab (dcnt GF c.cdTr k)) (candExec c) := by
  intro hrows hbnd hch hord hfc hsca
  refine ⟨fun k => (List.range' 0 N).map (fun i => (F i).1 (tcnt i (c.cdTr.take k))), ?_, ?_⟩
  · apply List.ext_getElem?
    intro j
    simp only [List.getElem?_map]
    by_cases hj : j < N
    · rw [lookup_seq_lt hj]
      simp only [Option.map_some, Nat.zero_add]
      exact congrArg some (hch j hj).1
    · rw [lookup_seq_ge (by omega)]
      rfl
  · intro k s hs
    change c.cdTr[k]? = some s at hs
    have hklen : k ≤ c.cdTr.length := by have := lookup_lt_Some hs; omega
    have hrow : (rows s.esAg)[tcnt s.esAg (c.cdTr.take k)]? = some s.esLb := by
      rw [← hrows]; exact trowAt _ _ k s hs rfl
    have hiN : s.esAg < N := by
      by_cases hge : s.esAg < N
      · exact hge
      · rw [hbnd _ (by omega)] at hrow; simp at hrow
    obtain ⟨_, hfb⟩ := hch _ hiN
    obtain ⟨hdev, hnodev⟩ := hfb _ _ hrow
    have hblk' : GraphFetchBlocks.hblkS
        (fab (dcnt GF c.cdTr k)) (fab (dcnt GF c.cdTr (k + 1)))
        (rowWs (rows s.esAg) (tcnt s.esAg (c.cdTr.take k))) s.esLb
        ((F s.esAg).2 (tcnt s.esAg (c.cdTr.take k)))
        ((F s.esAg).1 (tcnt s.esAg (c.cdTr.take k)))
        ((F s.esAg).1 (tcnt s.esAg (c.cdTr.take k) + 1)) := by
      by_cases hin : (s.esAg, tcnt s.esAg (c.cdTr.take k)) ∈ GF.gfDev
      · have hda : dstepAt GF c.cdTr k = true := by
          unfold dstepAt; rw [hs]; exact decide_eq_true hin
        rw [dcntStepDev _ _ _ hda]
        exact hdev _ (hord k s hs hin)
      · have hda : dstepAt GF c.cdTr k = false := by
          unfold dstepAt; rw [hs]; exact decide_eq_false hin
        rw [dcntStepNe _ _ _ hda]
        exact hnodev hin _
    obtain ⟨pa, da, hstar, hdisj⟩ := hblk'
    have hrelp : ((stt (candExec c) k).msWs s.esAg).wRelp =
        (rowWs (rows s.esAg) (tcnt s.esAg (c.cdTr.take k))).wRelp := by
      rw [candWsRelp c _ k hklen]
      unfold trow
      rw [hrows]
    refine ⟨hsca k s hs, (F s.esAg).1 (tcnt s.esAg (c.cdTr.take k)), pa, da,
      (F s.esAg).1 (tcnt s.esAg (c.cdTr.take k) + 1), (F s.esAg).2 (tcnt s.esAg (c.cdTr.take k)),
      ?_, ?_, hstar, fun _ _ _ => trivial, hfc k s hs, ?_⟩
    · simp only [List.getElem?_map]
      rw [lookup_seq_lt hiN]
      simp
    · apply List.ext_getElem?
      intro j
      by_cases hj : j = s.esAg
      · rw [hj, List.getElem?_set_self (by simp only [List.length_map, List.length_range']; omega),
          List.getElem?_map, lookup_seq_lt hiN]
        simp only [Option.map_some, Nat.zero_add, tcntStepEq _ _ k s hs rfl]
      · rw [List.getElem?_set_ne (fun h => hj h.symm)]
        simp only [List.getElem?_map]
        by_cases hjN : j < N
        · rw [lookup_seq_lt hjN]
          simp only [Option.map_some, Nat.zero_add, tcntStepNe j _ k s hs (fun h => hj h.symm)]
        · rw [lookup_seq_ge (by omega)]
          rfl
    · rcases hdisj with ⟨l, hfu, hre, hst⟩ | ⟨pm, dm, ls2, pm2, dm2, l1, l2, hre, hs1, hs2, hs3⟩
      · left
        exact ⟨l, hfu, (hlblRealizesAx _ _ _ _ _).2 (hlblRealizesRelp _ _ _ _ _ hrelp hre), hst⟩
      · right
        exact ⟨pm, dm, ls2, pm2, dm2, l1, l2,
          (hlblRealizesPairAx _ _ _ _ _ _ _).1 (hlblRealizesPairRelp _ _ _ _ _ _ _ hrelp hre),
          hs1, hs2, hs3⟩

/-! # 6. THE COMPOSITION: `topoSupplyZ` -/

/-- The empty emission stores its (empty) fragment. -/
theorem GraphFetchBlocks.emptyFetchIn (GD : Gdexec) (i : Nat) (p : Pexv6) :
    GraphFetch.emFetchIn GD i ⟨[], p⟩ := by
  rintro x y ⟨n, base, tvs, hn, -⟩
  simp at hn

/-- The empty emission satisfies the slot. -/
theorem GraphFetchBlocks.emptyZif (G : Gexec) (i : Nat) (p : Pexv6) :
    GraphFetch.emZif G i ⟨[], p⟩ := by
  intro n base tvs hn
  simp at hn

/-- A linearized event's label is its row's entry. -/
theorem GraphFetchBlocks.rowLbl (G : Gexec) (i k : Nat) (lb : Lbl) :
    gxLbl G (i, k) = some lb → ((G.gxProg[i]?).getD [])[k]? = some lb := by
  unfold gxLbl
  cases h : G.gxProg[i]? with
  | none => simp
  | some row => simp

/-- **`topoSupplyZ` — THE UNPINNED, SHAPED SUPPLY** (G6-3 L1; the Zifencei twin of
`fconfRealize`/`topoSupply`, deviation 2): a `racyDIO`-acyclic core graph whose Zifencei fabric
bundle holds (`GraphFabConf.gfexecConfZF`, what `xv6ConfSZForget` returns) and whose rows'
emissions satisfy (P1)/(P2) normalizes to `GF'` (the same fabric order) whose rule-14
linearization is consistent, carries the rows (renamed), is `candScaT`, and — under the guard
`trDevOrdered` (`fconfRealize`'s) — is supplied at the UNPINNED LTS by M2's shaped conjunct
`execProgOk'SC pstepEv pclsEv fokTriv (fcutEM2 cohSrc E itvOfL fiOfL)` along the fabric
`fab ∘ dcnt GF'`, the leading stars `lsOf` the emissions' blocks, with M2's boot values. -/
theorem topoSupplyZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec) (N : Nat) :
    rvwmoCoreD GF.gfGd →
    (∀ x, ¬ tc (racyDIO GF) x x) →
    GraphFabConf.gfexecConfZF boot d0 fab GF →
    (∀ (i : Nat) (row : List Lbl) (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
      GF.gfGd.gdG.gxProg[i]? = some row → hartConff i row (boot i) dvi dvo tq em →
      GraphFetchBlocks.emFenceCyc em ∧ GraphFetchBlocks.emNoDangle em) →
    GF.gfGd.gdG.gxProg.length ≤ N →
    ∃ (pi : Nat → Nat) (GF' : Gfexec),
      rowsRel pi GF.gfGd.gdG GF'.gfGd.gdG ∧
      GF'.gfDev = GF.gfDev ∧
      rvwmoMinusDepsConsistent GF'.gfGd ∧
      grule14 GF'.gfGd.gdG ∧
      srvwmoConsistent (linCand GF'.gfGd.gdG) ∧
      (linCand GF'.gfGd.gdG).cdImg = GF.gfGd.gdG.gxImg ∧
      (∀ i, ((linCand GF'.gfGd.gdG).cdTr.filter (fun s => decide (s.esAg = i))).map
          (fun s => s.esLb) = ((GF.gfGd.gdG.gxProg[i]?).getD []).map (lblRen pi)) ∧
      candScaT cohSrc (linCand GF'.gfGd.gdG) ∧
      (trDevOrdered GF' (linCand GF'.gfGd.gdG) →
        ∃ (pst : Nat → List Pexv6) (lsOf : Nat → List Wlabel),
          pst 0 = (List.range' 0 N).map boot ∧
          fab (dcnt GF' (linCand GF'.gfGd.gdG).cdTr 0) = d0 ∧
          (∀ i, GraphFetchSupply.itvOfL cohSrc (candExec (linCand GF'.gfGd.gdG)) lsOf 0 i = 0) ∧
          (∀ i, GraphFetchSupply.fiOfL (candExec (linCand GF'.gfGd.gdG)).exTr lsOf 0 i = false) ∧
          execProgOk'SC pstepEv pclsEv PfRunUnpinned.fokTriv
            (PfRunUnpinned.fcutEM2 cohSrc (candExec (linCand GF'.gfGd.gdG))
              (GraphFetchSupply.itvOfL cohSrc (candExec (linCand GF'.gfGd.gdG)) lsOf)
              (GraphFetchSupply.fiOfL (candExec (linCand GF'.gfGd.gdG)).exTr lsOf))
            pst (fun k => fab (dcnt GF' (linCand GF'.gfGd.gdG).cdTr k))
            (candExec (linCand GF'.gfGd.gdG))) := by
  intro hcore hacy hconf hprem hN
  obtain ⟨h0, -, -, hc⟩ := hconf
  -- the bundle's emissions, chosen
  have hch : ∀ i, i < GF.gfGd.gdG.gxProg.length →
      ∃ a : Hemission × (Nat → Efab) × (Nat → Efab) × (Nat → Bool), ∀ row,
        GF.gfGd.gdG.gxProg[i]? = some row →
        hartConff i row (boot i) a.2.1 a.2.2.1 a.2.2.2 a.1 ∧
        (∀ k : Nat, k < row.length →
          ((i, k) ∈ GF.gfDev ↔ (gisIo GF.gfGd.gdG (i, k) = true ∨ a.2.1 k ≠ a.2.2.1 k ∨
            a.2.2.2 k = true))) ∧
        (∀ (k n : Nat), GF.gfDev[n]? = some (i, k) → a.2.1 k = fab n ∧ a.2.2.1 k = fab (n + 1)) ∧
        (emZifencei GF.gfGd.gdG i a.1 ∧ GraphFetch.emFetchIn GF.gfGd i a.1) := by
    intro i hi
    obtain ⟨row, hrow⟩ : ∃ row, GF.gfGd.gdG.gxProg[i]? = some row :=
      someOfIsSome (lookup_lt_is_Some_2 hi)
    obtain ⟨em, dvi, dvo, tq, hem, hiff, hpin, hfz, -⟩ := hc i row hrow
    refine ⟨(em, dvi, dvo, tq), fun row' hrow' => ?_⟩
    rw [hrow, Option.some.injEq] at hrow'
    subst hrow'
    exact ⟨hem, hiff, hpin, hfz⟩
  obtain ⟨E, hE⟩ := natBoundedChoice
    ((⟨[], boot 0⟩ : Hemission), fun _ => d0, fun _ => d0, fun _ => false) _ _ hch
  let emF : Nat → Hemission := fun i =>
    if i < GF.gfGd.gdG.gxProg.length then (E i).1 else ⟨[], boot i⟩
  have hrowOf : ∀ i, i < GF.gfGd.gdG.gxProg.length → ∃ row, GF.gfGd.gdG.gxProg[i]? = some row :=
    fun i hi => someOfIsSome (lookup_lt_is_Some_2 hi)
  have hin : ∀ i, GraphFetch.emFetchIn GF.gfGd i (emF i) := by
    intro i
    by_cases hi : i < GF.gfGd.gdG.gxProg.length
    · obtain ⟨row, hrow⟩ := hrowOf i hi
      simp only [emF, if_pos hi]
      exact (hE i hi row hrow).2.2.2.2
    · simp only [emF, if_neg hi]
      exact GraphFetchBlocks.emptyFetchIn _ _ _
  have hz : ∀ i, GraphFetch.emZif GF.gfGd.gdG i (emF i) := by
    intro i
    by_cases hi : i < GF.gfGd.gdG.gxProg.length
    · obtain ⟨row, hrow⟩ := hrowOf i hi
      simp only [emF, if_pos hi]
      exact (hE i hi row hrow).2.2.2.1
    · simp only [emF, if_neg hi]
      exact GraphFetchBlocks.emptyZif _ _ _
  obtain ⟨GD', pi, hc', h14, hrr, -, -, -, hsup⟩ :=
    GraphFetch.normalizeFetchSupply GF emF hcore hacy hin hz
  have hwf : gwf GD'.gdG := hc'.1.1
  have hprog : ∀ i : Nat, GD'.gdG.gxProg[i]? =
      (GF.gfGd.gdG.gxProg[i]?).map (fun row : List Lbl => row.map (lblRen pi)) := by
    intro i
    rw [hrr.2.1, List.getElem?_map]
  have hlenEq : GD'.gdG.gxProg.length = GF.gfGd.gdG.gxProg.length := rowsRelNharts pi _ _ hrr
  obtain ⟨hsr, -, hrowL, -⟩ := rule14Linearization' GD'.gdG hc'.1 h14
  -- the per-hart block data at the normalized graph
  have hblkData : ∀ i, i < N → ∃ a : (Nat → Pexv6) × (Nat → List Wlabel), a.1 0 = boot i ∧
      ∀ n lb, ((GD'.gdG.gxProg[i]?).getD [])[n]? = some lb →
        GraphFetch.emBlockF GD'.gdG (emRen pi (emF i)) i n (a.2 n) ∧
        (∀ m, GF.gfDev[m]? = some (i, n) →
          GraphFetchBlocks.hblkS (fab m) (fab (m + 1)) (rowWs ((GD'.gdG.gxProg[i]?).getD []) n) lb
            (a.2 n) (a.1 n) (a.1 (n + 1))) ∧
        ((i, n) ∉ GF.gfDev → ∀ d,
          GraphFetchBlocks.hblkS d d (rowWs ((GD'.gdG.gxProg[i]?).getD []) n) lb (a.2 n) (a.1 n)
            (a.1 (n + 1))) := by
    intro i hiN
    by_cases hi : i < GF.gfGd.gdG.gxProg.length
    · obtain ⟨row, hrow0⟩ := hrowOf i hi
      obtain ⟨hem, hiff, hpin, -⟩ := hE i hi row hrow0
      have hemF : emF i = (E i).1 := by simp only [emF, if_pos hi]
      obtain ⟨hfc, hndg⟩ := hprem i row (E i).1 _ _ _ hrow0 hem
      have hrowG : GD'.gdG.gxProg[i]? = some (row.map (lblRen pi)) := by
        rw [hprog, hrow0]; rfl
      obtain ⟨f, g, hf0, hf⟩ := GraphFetchBlocks.rowBlocks GD'.gdG i (row.map (lblRen pi)) (boot i)
        _ _ _ (emRen pi (E i).1) GF.gfDev fab (hartConffRen pi i row (boot i) _ _ _ _ hem)
        (GraphFetchBlocks.emFenceCycRen pi _ hfc) (GraphFetchBlocks.emNoDangleRen pi _ hndg)
        (fun n hn hnin => by
          cases htq : (E i).2.2.2 n with
          | false => rfl
          | true =>
            rw [List.length_map] at hn
            exact absurd ((hiff n hn).2 (Or.inr (Or.inr htq))) hnin)
        hpin
        (fun n lb hn => by
          unfold glbl gxLbl
          rw [hrowG]
          simp [hn])
      refine ⟨(f, g), hf0, fun n lb hn => ?_⟩
      rw [hrowG] at hn ⊢
      rw [hemF]
      exact hf n lb hn
    · refine ⟨(fun _ => boot i, fun _ => []), rfl, fun n lb hn => ?_⟩
      have hnone : GF.gfGd.gdG.gxProg[i]? = none := List.getElem?_eq_none (by omega)
      rw [hprog, hnone] at hn
      simp at hn
  obtain ⟨Fx, hFx⟩ := natBoundedChoice ((fun _ => boot 0), (fun _ => [])) _ N hblkData
  let lsOf : Nat → List Wlabel := fun K =>
    match (linCand GD'.gdG).cdTr[K]? with
    | some s => (Fx s.esAg).2 (tcnt s.esAg ((linCand GD'.gdG).cdTr.take K))
    | none => []
  have hlsOf : ∀ K s, (linCand GD'.gdG).cdTr[K]? = some s →
      lsOf K = (Fx s.esAg).2 (tcnt s.esAg ((linCand GD'.gdG).cdTr.take K)) := by
    intro K s hs
    simp only [lsOf, hs]
  have hblkF : ∀ K i k, (glinEids GD'.gdG)[K]? = some (i, k) →
      GraphFetch.emBlockF GD'.gdG (emRen pi (emF i)) i k (lsOf K) := by
    intro K i k he
    have hs := linTrLookup GD'.gdG K (i, k) he
    have hcnt := GraphFetchFloor.ownCount GD'.gdG hwf h14 K (i, k) he
    have hl := GraphFetchBlocks.rowLbl GD'.gdG i k _ (linLbl GD'.gdG hwf K (i, k) he)
    have hiN : i < N := by
      by_cases h : i < GD'.gdG.gxProg.length
      · omega
      · have hnone : GD'.gdG.gxProg[i]? = none := List.getElem?_eq_none (by omega)
        rw [hnone] at hl
        simp at hl
    rw [hlsOf K _ hs]
    simp only [glinStep] at hcnt ⊢
    rw [hcnt]
    exact ((hFx i hiN).2 k _ hl).1
  obtain ⟨hi0, hf0', hcut⟩ := hsup lsOf hblkF
  have hscaT := linCandScaTMinus GD'.gdG hc'.1 h14
  refine ⟨pi, ⟨GD', GF.gfDev⟩, hrr, rfl, hc', h14, hsr, rowsRelImg pi _ _ hrr,
    fun i => (hrowL i).trans (by rw [hprog]; cases GF.gfGd.gdG.gxProg[i]? <;> rfl), hscaT, fun hord => ?_⟩
  obtain ⟨pst, hpst0, hprg⟩ := GraphFetchBlocks.supplyOfFconfZ (linCand GD'.gdG) boot fab
    ⟨GD', GF.gfDev⟩ (fun i => (GD'.gdG.gxProg[i]?).getD []) N Fx _ hrowL
    (fun i hi => by rw [List.getElem?_eq_none (by omega)]; rfl)
    (fun i hi => ⟨(hFx i hi).1, fun n lb hn => ⟨((hFx i hi).2 n lb hn).2.1, ((hFx i hi).2 n lb hn).2.2⟩⟩)
    hord
    (fun k s hs => by rw [← hlsOf k s hs]; exact hcut k s hs)
    (fun k s hs aq base ts vs hlb => scaOkTSca _ _ _ _ _ _ (hscaT k s hs aq base ts vs hlb))
  exact ⟨pst, lsOf, hpst0, h0, hi0, hf0', hprg⟩

/-- **M2's conjunct verbatim** (`srvwmoXv6M2Premises`'s `execProgOk'STC … fcutEM2 …`): the shaped
supply of `topoSupplyZ` with its `candScaT` and a `candDiskLat` (deviation 3: proved on the
anchored trace only) is `execProgOk'STC`. -/
theorem GraphFetchBlocks.stcOfSC {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass)
    (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop) (stamp : CohStamp)
    (fcutE : Nat → Nat → List Wlabel → Mstate → Prop) (pst : Nat → List P) (dv : Nat → D)
    (c : Cand) :
    execProgOk'SC pstep pcls fok fcutE pst dv (candExec c) → candScaT stamp c → candDiskLat c →
    execProgOk'STC pstep pcls fok stamp fcutE pst dv (candExec c) :=
  fun h1 h2 h3 => ⟨h1, h2, h3⟩

/-- `topoSupplyZ` in M2's vocabulary: under the guard and `candDiskLat`, the free functions
`itvOf`/`fiOf` of `srvwmoXv6M2Premises` exist with M2's boot values and the conjunct
`execProgOk'STC pstepEv pclsEv fokTriv cohSrc (fcutEM2 cohSrc (candExec c) itvOf fiOf)`. -/
theorem topoSupplyZT (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec) (N : Nat) :
    rvwmoCoreD GF.gfGd →
    (∀ x, ¬ tc (racyDIO GF) x x) →
    GraphFabConf.gfexecConfZF boot d0 fab GF →
    (∀ (i : Nat) (row : List Lbl) (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
      GF.gfGd.gdG.gxProg[i]? = some row → hartConff i row (boot i) dvi dvo tq em →
      GraphFetchBlocks.emFenceCyc em ∧ GraphFetchBlocks.emNoDangle em) →
    GF.gfGd.gdG.gxProg.length ≤ N →
    ∃ (pi : Nat → Nat) (GF' : Gfexec),
      rowsRel pi GF.gfGd.gdG GF'.gfGd.gdG ∧ GF'.gfDev = GF.gfDev ∧
      srvwmoConsistent (linCand GF'.gfGd.gdG) ∧
      (linCand GF'.gfGd.gdG).cdImg = GF.gfGd.gdG.gxImg ∧
      candScaT cohSrc (linCand GF'.gfGd.gdG) ∧
      (trDevOrdered GF' (linCand GF'.gfGd.gdG) → candDiskLat (linCand GF'.gfGd.gdG) →
        ∃ (pst : Nat → List Pexv6) (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool),
          pst 0 = (List.range' 0 N).map boot ∧
          fab (dcnt GF' (linCand GF'.gfGd.gdG).cdTr 0) = d0 ∧
          execProgOk'STC pstepEv pclsEv PfRunUnpinned.fokTriv cohSrc
            (PfRunUnpinned.fcutEM2 cohSrc (candExec (linCand GF'.gfGd.gdG)) itvOf fiOf) pst
            (fun k => fab (dcnt GF' (linCand GF'.gfGd.gdG).cdTr k)) (candExec (linCand GF'.gfGd.gdG)) ∧
          (∀ i, itvOf 0 i = 0) ∧ (∀ i, fiOf 0 i = false)) := by
  intro hcore hacy hconf hprem hN
  obtain ⟨pi, GF', hrr, hdev, -, -, hsr, himg, -, hscaT, hsup⟩ :=
    topoSupplyZ boot d0 fab GF N hcore hacy hconf hprem hN
  refine ⟨pi, GF', hrr, hdev, hsr, himg, hscaT, fun hord hdl => ?_⟩
  obtain ⟨pst, lsOf, hpst0, hd0, hi0, hf0, hprg⟩ := hsup hord
  exact ⟨pst, _, _, hpst0, hd0, GraphFetchBlocks.stcOfSC _ _ _ _ _ _ _ _ hprg hscaT hdl, hi0, hf0⟩

end Weak
