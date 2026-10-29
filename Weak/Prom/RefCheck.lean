/-
Weak/Prom: **the reference checker** — the candidate enumerator (paths × gmo linearisations, load values computed
along gmo) with its COMPLETENESS proof, and the verdict theorems' combinators (S0-P part (1)).

`forbidB T = true → forbiddenRef T` (`forbid_sound`) and `existsB T = true → allowedRef T` (`exists_sound`):
both Bools are evaluated by the KERNEL (`decide +kernel`); `native_decide` is never used (it would add
`Lean.ofReduceBool`).

## The enumerator

1. PATHS: every hart is explored symbolically along both outcomes of every branch and SC (`explore`); the
   per-hart results are combined (`Test.paths`).  Complete: `symRun … = some r → (ch, r) ∈ explore …`.
2. GMO: every duplicate-free ordering of the memory operations that respects the VALUE-INDEPENDENT part of ppo
   (`staticOrd`: rules 4–11, 13, which need no address and no rf; I/O-free tests) is listed (`lins`).  Complete:
   a gmo of a consistent execution is duplicate-free, lists exactly the memory operations and respects ppo.
3. VALUES: rf is not enumerated.  Given the path and gmo, the load values are COMPUTED by one pass along gmo
   (`passVals`): a load's bytes are the load value axiom's answer, using only the values of gmo-earlier loads.
   This is complete because in a consistent execution every value a load's answer depends on comes from a
   gmo-earlier load: a gmo-earlier store's address and data sources are gmo-before it (rules 9, 10; an AMO's own
   load is the AMO), and a store `m` po-before but gmo-after the load `r` can be `r`'s source only if `m` is a plain
   store whose address and data sources are gmo-before `r` (rule 3 excludes AMO/SC sources, rule 12 orders the
   sources) — so the pass only consults po-earlier stores whose expressions mention gmo-earlier loads only
   (`lvComp`), and the axiom's latest store passes that filter (`pass_correct`).  This is the formal content of
   "values are well-founded along gmo": no out-of-thin-air value can be missed.
4. CHECK: the candidate (paths, computed values, gmo) is checked by the reflective checker `refCoreB` (complete
   and sound for `rvwmoRef`), with the path conditions and the outcome.

The enumerator's scope (checked by the Bool, so a test outside it makes `forbidB` false, never unsound): no I/O
regions, and `varsOkB` — every expression's load variables are within the matching syntactic dependencies (the
interpreter's invariant, checked per path).
-/
import Weak.Prom.RefProg

namespace Weak.Prom.Ref

/-! ## 1. Paths -/

/-- All complete paths of hart `h` from `s`, with their choice lists. -/
def explore (p : List Instr) (h : Nat) : Nat → SSt → List (List Bool × SSt)
  | 0, _ => []
  | fuel + 1, s =>
      if s.pc = p.length then [([], s)] else
      match p[s.pc]? with
      | none => []
      | some i =>
          match stepI h p.length s i with
          | .stuck => []
          | .next s' => explore p h fuel s'
          | .fork t f =>
              (explore p h fuel t).map (fun cr => (true :: cr.1, cr.2)) ++
                (explore p h fuel f).map (fun cr => (false :: cr.1, cr.2))

def Test.exploreH (T : Test) (h : Nat) : List (List Bool × SSt) :=
  explore (T.prog h) h ((T.prog h).length + 1) (T.init h)

def Test.exploreFrom (T : Test) : Nat → Nat → List (List (List Bool) × List SSt)
  | _, 0 => [([], [])]
  | h, k + 1 =>
      (T.exploreH h).flatMap (fun cs => (T.exploreFrom (h + 1) k).map (fun rs => (cs.1 :: rs.1, cs.2 :: rs.2)))

/-- All path combinations of the test. -/
def Test.paths (T : Test) : List (List (List Bool) × List SSt) := T.exploreFrom 0 T.harts.length

/-! ## 2. Symbolic lookups -/

def sevAt (trs : List SSt) (e : EvId) : SEv := ((trs[e.1]?).bind (·.evs[e.2]?)).getD default

def sskOf (trs : List SSt) (e : EvId) : Skel := (sevAt trs e).sk

def sids (trs : List SSt) : List EvId := idsOf (trs.map (·.evs))

def memIds (trs : List SSt) : List EvId := (sids trs).filter (fun e => (sskOf trs e).kind.isMem)

/-- The value-independent ppo of the symbolic trace (I/O-free). -/
def statRel (trs : List SSt) : EvId → EvId → Bool := staticOrd (sids trs) (sskOf trs) (fun _ => false)

/-! ## 3. gmo linearisations -/

/-- Every ordering of `rest` in which no element comes after one it must precede under `rel`. -/
def lins (rel : EvId → EvId → Bool) : Nat → List EvId → List (List EvId)
  | 0, rest => if rest = [] then [[]] else []
  | n + 1, rest =>
      if rest = [] then [[]] else
      (rest.filter (fun e => rest.all (fun a => !rel a e))).flatMap
        (fun e => (lins rel n (rest.filter (fun x => x != e))).map (e :: ·))

/-! ## 4. The value pass -/

def lk (acc : List (EvId × List Nat)) (e : EvId) : List Nat := (acc.lookup e).getD []

def touchesS (ν : Val) (se : SEv) (x : Nat) : Bool :=
  decide (se.addr.eval ν ≤ x ∧ x < se.addr.eval ν + se.sk.sz)

def wbyteS (ν : Val) (se : SEv) (x : Nat) : Nat :=
  ((byteList (se.wval.eval ν) se.sk.sz)[x - se.addr.eval ν]?).getD 0

def varsOfS (se : SEv) : List EvId := se.addr.vars ++ se.wval.vars

/-- The pass's candidate stores for byte `x` of load `r` (current partial valuation `ν`): gmo-earlier stores, and
po-earlier stores whose expressions mention gmo-earlier loads only. -/
def candP (trs : List SSt) (g : List EvId) (ν : Val) (r : EvId) (x : Nat) (w : EvId) : Bool :=
  (sskOf trs w).kind.isStore && touchesS ν (sevAt trs w) x &&
    (gB g w r || (poS (sskOf trs) w r && (varsOfS (sevAt trs w)).all (fun v => gB g v r)))

/-- The bytes the pass assigns to load `r`. -/
def lvComp (img : Nat → Nat) (trs : List SSt) (g : List EvId) (ν : Val) (r : EvId) : List Nat :=
  (List.range (sskOf trs r).sz).map (fun k =>
    let x := (sevAt trs r).addr.eval ν + k
    match (g.filter (candP trs g ν r x)).getLast? with
    | some w => wbyteS ν (sevAt trs w) x
    | none => img x)

def passStep (img : Nat → Nat) (trs : List SSt) (g : List EvId) (acc : List (EvId × List Nat)) (e : EvId) :
    List (EvId × List Nat) :=
  if (sskOf trs e).kind.isLoad then (e, lvComp img trs g (lk acc) e) :: acc else acc

def passVals (img : Nat → Nat) (trs : List SSt) (g : List EvId) : List (EvId × List Nat) :=
  g.foldl (passStep img trs g) []

/-- Check one candidate: outcome first (cheap), then path conditions, then `rvwmoRef`. -/
def checkCand (T : Test) (trs : List SSt) (g : List EvId) : Bool :=
  let ν := lk (passVals T.imgF trs g)
  T.cond.eval (finalReg trs ν) (finalByte (conc T trs ν g)) && condsOk ν trs && refCoreB (conc T trs ν g)

/-! ## 5. The enumerator's scope check -/

def isLoadId (trs : List SSt) (v : EvId) : Bool := (sids trs).contains v && (sskOf trs v).kind.isLoad

def depsOk (trs : List SSt) (e : EvId) : Bool :=
  let se := sevAt trs e
  (se.sk.adep ++ se.sk.ddep ++ se.sk.cdep).all (fun j =>
    decide ((sskOf trs (e.1, j)).ii < se.sk.ii) && (sskOf trs (e.1, j)).kind.isMem &&
      (sids trs).contains (e.1, j))

def varsOkB (trs : List SSt) : Bool :=
  (sids trs).all (fun e =>
    (sevAt trs e).addr.vars.all (fun v => v.1 == e.1 && (sskOf trs e).adep.contains v.2 && isLoadId trs v) &&
    (sevAt trs e).wval.vars.all (fun v => v.1 == e.1 &&
      ((sskOf trs e).ddep.contains v.2 || ((sskOf trs e).kind == .amo && v.2 == e.2)) && isLoadId trs v) &&
    depsOk trs e) &&
  trs.all (fun s => s.conds.all (fun c => (c.2.1.vars ++ c.2.2.1.vars).all (isLoadId trs)) &&
    s.regs.all (fun x => x.1.vars.all (isLoadId trs)))

/-! ## 6. Verdicts -/

def candsOf (trs : List SSt) : List (List EvId) := lins (statRel trs) (memIds trs).length (memIds trs)

/-- FORBIDDEN by enumeration: no candidate satisfies the check. -/
def forbidB (T : Test) : Bool :=
  T.io.isEmpty && T.paths.all (fun p => varsOkB p.2 && (candsOf p.2).all (fun g => !checkCand T p.2 g))

/-- ALLOWED by search: some candidate satisfies the check. -/
def existsB (T : Test) : Bool :=
  T.paths.any (fun p => (candsOf p.2).any (fun g => checkCand T p.2 g))

/-- The first witness (for reports). -/
def witnessOf (T : Test) : Option (List (List Bool) × List EvId) :=
  T.paths.findSome? (fun p => ((candsOf p.2).find? (fun g => checkCand T p.2 g)).map (fun g => (p.1, g)))

/-! ## 7. Paths: exploration is sound and complete -/

theorem symRun_explore (p : List Instr) (h : Nat) :
    ∀ (fuel : Nat) (s : SSt) (ch : List Bool) (r : SSt),
      symRun p h fuel s ch = some r → (ch, r) ∈ explore p h fuel s
  | 0, s, ch, r, H => by simp [symRun] at H
  | fuel + 1, s, ch, r, H => by
    unfold symRun at H
    unfold explore
    by_cases hpc : s.pc = p.length
    · rw [if_pos hpc] at H ⊢
      by_cases hch : ch = []
      · rw [if_pos hch] at H
        cases H; subst hch; exact List.mem_singleton.2 rfl
      · rw [if_neg hch] at H; cases H
    · rw [if_neg hpc] at H ⊢
      cases hi : p[s.pc]? with
      | none => rw [hi] at H; cases H
      | some i =>
        rw [hi] at H
        simp only at H ⊢
        cases hs : stepI h p.length s i with
        | stuck => rw [hs] at H; cases H
        | next s' => rw [hs] at H; exact symRun_explore p h fuel s' ch r H
        | fork t f =>
          rw [hs] at H
          simp only
          cases ch with
          | nil => cases H
          | cons b ch' =>
            cases b
            · exact List.mem_append_right _
                (List.mem_map.2 ⟨(ch', r), symRun_explore p h fuel f ch' r H, rfl⟩)
            · exact List.mem_append_left _
                (List.mem_map.2 ⟨(ch', r), symRun_explore p h fuel t ch' r H, rfl⟩)

theorem explore_symRun (p : List Instr) (h : Nat) :
    ∀ (fuel : Nat) (s : SSt) (ch : List Bool) (r : SSt),
      (ch, r) ∈ explore p h fuel s → symRun p h fuel s ch = some r
  | 0, s, ch, r, H => by simp [explore] at H
  | fuel + 1, s, ch, r, H => by
    unfold explore at H
    unfold symRun
    by_cases hpc : s.pc = p.length
    · rw [if_pos hpc] at H ⊢
      have := List.mem_singleton.1 H
      cases this
      simp
    · rw [if_neg hpc] at H ⊢
      cases hi : p[s.pc]? with
      | none => rw [hi] at H; cases H
      | some i =>
        rw [hi] at H
        simp only at H ⊢
        cases hs : stepI h p.length s i with
        | stuck => rw [hs] at H; cases H
        | next s' => rw [hs] at H; exact explore_symRun p h fuel s' ch r H
        | fork t f =>
          rw [hs] at H
          simp only at H ⊢
          rcases List.mem_append.1 H with H | H
          · obtain ⟨⟨c, r'⟩, hm, he⟩ := List.mem_map.1 H
            cases he
            exact explore_symRun p h fuel t c _ hm
          · obtain ⟨⟨c, r'⟩, hm, he⟩ := List.mem_map.1 H
            cases he
            exact explore_symRun p h fuel f c _ hm

theorem runFrom_explore (T : Test) :
    ∀ (chs : List (List Bool)) (h : Nat) (trs : List SSt),
      T.runFrom h chs = some trs → (chs, trs) ∈ T.exploreFrom h chs.length
  | [], h, trs, H => by
    simp only [Test.runFrom, Option.some.injEq] at H
    subst H; simp [Test.exploreFrom]
  | c :: cs, h, trs, H => by
    unfold Test.runFrom at H
    cases h1 : T.runH h c with
    | none => rw [h1] at H; cases H
    | some s =>
      cases h2 : T.runFrom (h + 1) cs with
      | none => rw [h1, h2] at H; cases H
      | some rs =>
        rw [h1, h2] at H
        simp only [Option.some.injEq] at H
        subst H
        simp only [List.length_cons, Test.exploreFrom, List.mem_flatMap, List.mem_map]
        exact ⟨(c, s), symRun_explore _ _ _ _ _ _ h1, (cs, rs), runFrom_explore T cs (h + 1) rs h2, rfl⟩

theorem explore_runFrom (T : Test) :
    ∀ (k h : Nat) (chs : List (List Bool)) (trs : List SSt),
      (chs, trs) ∈ T.exploreFrom h k → T.runFrom h chs = some trs ∧ chs.length = k
  | 0, h, chs, trs, H => by
    simp only [Test.exploreFrom, List.mem_singleton, Prod.mk.injEq] at H
    obtain ⟨rfl, rfl⟩ := H
    exact ⟨rfl, rfl⟩
  | k + 1, h, chs, trs, H => by
    simp only [Test.exploreFrom, List.mem_flatMap, List.mem_map] at H
    obtain ⟨⟨c, s⟩, hcs, ⟨cs, rs⟩, hrs, he⟩ := H
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨h1, h2⟩ := explore_runFrom T k (h + 1) cs rs hrs
    refine ⟨?_, by simp [h2]⟩
    have h0 : T.runH h c = some s := explore_symRun _ _ _ _ _ _ hcs
    simp [Test.runFrom, h0, h1]

theorem runAll_paths (T : Test) (chs : List (List Bool)) (trs : List SSt) :
    T.runAll chs = some trs → (chs, trs) ∈ T.paths := by
  intro H
  unfold Test.runAll at H
  by_cases hl : chs.length = T.harts.length
  · rw [if_pos hl] at H
    have := runFrom_explore T chs 0 trs H
    rw [hl] at this
    exact this
  · rw [if_neg hl] at H; cases H

theorem paths_runAll (T : Test) (chs : List (List Bool)) (trs : List SSt) :
    (chs, trs) ∈ T.paths → T.runAll chs = some trs := by
  intro H
  obtain ⟨h1, h2⟩ := explore_runFrom T _ 0 chs trs H
  simp [Test.runAll, h2, h1]

/-! ## 8. Positions and linearisations -/

theorem pos_cons_self (e : EvId) (g : List EvId) : pos (e :: g) e = 0 := by simp [pos]

theorem pos_cons_ne (e a : EvId) (g : List EvId) (h : e ≠ a) : pos (e :: g) a = pos g a + 1 := by
  simp [pos, h]

theorem pos_lt_length (g : List EvId) (e : EvId) (h : e ∈ g) : pos g e < g.length := by
  induction g with
  | nil => cases h
  | cons x t ih =>
    by_cases hx : x = e
    · subst hx; simp [pos]
    · rw [pos_cons_ne _ _ _ hx]
      have : e ∈ t := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm hx
        · exact h
      simp only [List.length_cons]
      have := ih this
      omega

theorem pos_getElem (g : List EvId) (hn : g.Nodup) (n : Nat) (hl : n < g.length) : pos g g[n] = n := by
  induction g generalizing n with
  | nil => cases hl
  | cons x t ih =>
    cases n with
    | zero => simp [pos]
    | succ n =>
      have hnt := (List.nodup_cons.1 hn)
      have hlt : n < t.length := by simpa using hl
      have hne : x ≠ t[n] := fun h => hnt.1 (h ▸ List.getElem_mem hlt)
      simp only [List.getElem_cons_succ]
      rw [pos_cons_ne _ _ _ hne, ih hnt.2 n hlt]

theorem mem_take_of_pos_lt (g : List EvId) (v : EvId) (hv : v ∈ g) :
    ∀ n, pos g v < n → v ∈ g.take n := by
  induction g with
  | nil => cases hv
  | cons x t ih =>
    intro n hn
    cases n with
    | zero => omega
    | succ n =>
      by_cases hx : x = v
      · subst hx; simp
      · rw [pos_cons_ne _ _ _ hx] at hn
        have hvt : v ∈ t := by
          rcases List.mem_cons.1 hv with h | h
          · exact absurd h.symm hx
          · exact h
        simp only [List.take_succ_cons, List.mem_cons]
        exact Or.inr (ih hvt n (by omega))

/-- A list RESPECTS `rel`: an element it must precede is listed later. -/
def respects (rel : EvId → EvId → Bool) (g : List EvId) : Prop :=
  ∀ a b, rel a b = true → a ∈ g → b ∈ g → pos g a < pos g b

theorem lins_complete (rel : EvId → EvId → Bool) :
    ∀ (g rest : List EvId) (N : Nat), g.Nodup → (∀ x, x ∈ g ↔ x ∈ rest) → respects rel g →
      g.length ≤ N → g ∈ lins rel N rest
  | [], rest, N, _, hm, _, _ => by
    have : rest = [] := List.eq_nil_iff_forall_not_mem.2 (fun x hx => by simpa using (hm x).2 hx)
    subst this
    cases N <;> simp [lins]
  | e :: g', rest, N, hn, hm, hr, hl => by
    cases N with
    | zero => simp at hl
    | succ N =>
      have her : e ∈ rest := (hm e).1 (List.mem_cons_self ..)
      have hne : rest ≠ [] := List.ne_nil_of_mem her
      have hnd := List.nodup_cons.1 hn
      unfold lins
      rw [if_neg hne]
      apply List.mem_flatMap.2
      refine ⟨e, List.mem_filter.2 ⟨her, ?_⟩, List.mem_map.2 ⟨g', ?_, rfl⟩⟩
      · apply List.all_eq_true.2
        intro a ha
        cases hra : rel a e
        · rfl
        · exfalso
          have := hr a e hra ((hm a).2 ha) (List.mem_cons_self ..)
          rw [pos_cons_self] at this
          omega
      · apply lins_complete rel g' _ N hnd.2
        · intro x
          simp only [List.mem_filter, bne_iff_ne, ne_eq]
          constructor
          · intro hx
            exact ⟨(hm x).1 (List.mem_cons_of_mem _ hx), fun h => hnd.1 (h ▸ hx)⟩
          · rintro ⟨hx, hxe⟩
            rcases List.mem_cons.1 ((hm x).2 hx) with h | h
            · exact absurd h hxe
            · exact h
        · intro a b hab ha hb
          have hae : e ≠ a := fun h => hnd.1 (h ▸ ha)
          have hbe : e ≠ b := fun h => hnd.1 (h ▸ hb)
          have := hr a b hab (List.mem_cons_of_mem _ ha) (List.mem_cons_of_mem _ hb)
          rw [pos_cons_ne _ _ _ hae, pos_cons_ne _ _ _ hbe] at this
          omega
        · simp at hl; omega

/-! ## 9. The concrete execution's structure -/

theorem mem_idsOf {α : Type} (L : List (List α)) (e : EvId) :
    e ∈ idsOf L ↔ ∃ l, L[e.1]? = some l ∧ e.2 < l.length := by
  obtain ⟨h, i⟩ := e
  simp only [idsOf, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨h', hh, i', hi, rfl, rfl⟩
    exact ⟨L[h'], List.getElem?_eq_getElem hh, by simpa [List.getElem?_eq_getElem hh] using hi⟩
  · rintro ⟨l, hl, hi⟩
    have hh : h < L.length := by
      rcases Nat.lt_or_ge h L.length with h1 | h1
      · exact h1
      · rw [List.getElem?_eq_none h1] at hl; cases hl
    exact ⟨h, hh, i, by simpa [hl] using hi, rfl, rfl⟩

theorem idsOf_congr {α β : Type} (L : List (List α)) (L' : List (List β)) (hl : L.length = L'.length)
    (hh : ∀ h : Nat, (L[h]?.getD []).length = (L'[h]?.getD []).length) : idsOf L = idsOf L' := by
  simp only [idsOf, hl, hh]

theorem conc_ids (T : Test) (trs : List SSt) (ν : Val) (g : List EvId) :
    (conc T trs ν g).ids = sids trs := by
  unfold Exec.ids conc sids
  apply idsOf_congr
  · simp
  · intro h
    simp only [List.getElem?_mapIdx, List.getElem?_map]
    cases trs[h]? <;> simp

theorem conc_sk (T : Test) (trs : List SSt) (ν : Val) (g : List EvId) (e : EvId) :
    (conc T trs ν g).sk e = sskOf trs e := by
  unfold Exec.sk Exec.ev conc sskOf sevAt
  simp only [List.getElem?_mapIdx]
  cases h1 : trs[e.1]? with
  | none => rfl
  | some s =>
    simp only [Option.map_some, Option.bind_some, List.getElem?_mapIdx]
    cases h2 : s.evs[e.2]? with
    | none => rfl
    | some se => rfl

theorem conc_skf (T : Test) (trs : List SSt) (ν : Val) (g : List EvId) :
    (conc T trs ν g).sk = sskOf trs := funext (conc_sk T trs ν g)

theorem conc_ev (T : Test) (trs : List SSt) (ν : Val) (g : List EvId) (e : EvId) (he : e ∈ sids trs) :
    (conc T trs ν g).ev e = concEv ν e.1 e.2 (sevAt trs e) := by
  obtain ⟨l, hl, hi⟩ := (mem_idsOf _ e).1 he
  simp only [List.getElem?_map] at hl
  cases h1 : trs[e.1]? with
  | none => rw [h1] at hl; cases hl
  | some s =>
    rw [h1] at hl
    simp only [Option.map_some, Option.some.injEq] at hl
    subst hl
    unfold Exec.ev conc sevAt
    simp only [List.getElem?_mapIdx, h1, Option.map_some, Option.bind_some, List.getElem?_eq_getElem hi,
      Option.getD_some]

theorem isIo_conc (T : Test) (trs : List SSt) (ν : Val) (g : List EvId) (hio : T.io = []) :
    isIo (conc T trs ν g) = fun _ => false := funext (isIo_nil _ hio)

theorem Kind.isMem_of_isLoad (k : Kind) : k.isLoad = true → k.isMem = true := by
  cases k <;> simp [Kind.isLoad, Kind.isMem]

theorem Kind.isMem_of_isStore (k : Kind) : k.isStore = true → k.isMem = true := by
  cases k <;> simp [Kind.isStore, Kind.isMem]

theorem gB_trans (g : List EvId) (a b c : EvId) : gB g a b = true → gB g b c = true → gB g a c = true := by
  simp only [gB, Bool.and_eq_true, decide_eq_true_eq]
  rintro ⟨⟨h1, _⟩, h3⟩ ⟨⟨_, h5⟩, h6⟩
  exact ⟨⟨h1, h5⟩, by omega⟩

theorem gB_mem (g : List EvId) (a b : EvId) : gB g a b = true → a ∈ g ∧ b ∈ g ∧ pos g a < pos g b := by
  simp only [gB, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem]
  intro h; exact ⟨h.1.1, h.1.2, h.2⟩

theorem ppoB_intro (X : Exec) (a b : EvId) (ha : (X.sk a).kind.isMem = true) (hb : (X.sk b).kind.isMem = true)
    (hpo : poX X a b = true)
    (hr : (rule1 X a b || rule2 X a b || rule3 X a b || staticRules X.ids X.sk (isIo X) a b ||
      rule12 X a b) = true) : ppoB X a b = true := by
  unfold ppoB; rw [ha, hb, hpo, hr]; rfl

/-! ## 10. The scope check, unpacked -/

section Scope

variable (trs : List SSt) (hv : varsOkB trs = true)
include hv

theorem varsOk_addr (e : EvId) (he : e ∈ sids trs) (v : EvId) (hvm : v ∈ (sevAt trs e).addr.vars) :
    v.1 = e.1 ∧ (sskOf trs e).adep.contains v.2 = true ∧ isLoadId trs v = true := by
  unfold varsOkB at hv
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hv
  obtain ⟨⟨h1, h2⟩, h3⟩ := (hv.1 e he).1.1 v hvm
  exact ⟨h1, h2, h3⟩

theorem varsOk_wval (e : EvId) (he : e ∈ sids trs) (v : EvId) (hvm : v ∈ (sevAt trs e).wval.vars) :
    v.1 = e.1 ∧ ((sskOf trs e).ddep.contains v.2 = true ∨ ((sskOf trs e).kind = .amo ∧ v.2 = e.2)) ∧
      isLoadId trs v = true := by
  unfold varsOkB at hv
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Bool.or_eq_true] at hv
  obtain ⟨⟨h1, h2⟩, h3⟩ := (hv.1 e he).1.2 v hvm
  exact ⟨h1, h2, h3⟩

theorem varsOk_deps (e : EvId) (he : e ∈ sids trs) (j : Nat)
    (hj : j ∈ (sskOf trs e).adep ++ (sskOf trs e).ddep ++ (sskOf trs e).cdep) :
    (sskOf trs (e.1, j)).ii < (sskOf trs e).ii ∧ (sskOf trs (e.1, j)).kind.isMem = true ∧
      (e.1, j) ∈ sids trs := by
  unfold varsOkB at hv
  simp only [Bool.and_eq_true, List.all_eq_true] at hv
  have := (hv.1 e he).2
  unfold depsOk at this
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.contains_iff_mem] at this
  obtain ⟨⟨h1, h2⟩, h3⟩ := this j hj
  exact ⟨h1, h2, h3⟩

theorem varsOk_conds (s : SSt) (hs : s ∈ trs) (c : PCond) (hc : c ∈ s.conds) (v : EvId)
    (hvm : v ∈ c.2.1.vars ++ c.2.2.1.vars) : isLoadId trs v = true := by
  unfold varsOkB at hv
  simp only [Bool.and_eq_true, List.all_eq_true] at hv
  exact (hv.2 s hs).1 c hc v hvm

theorem varsOk_regs (s : SSt) (hs : s ∈ trs) (x : Ex × List Nat) (hx : x ∈ s.regs) (v : EvId)
    (hvm : v ∈ x.1.vars) : isLoadId trs v = true := by
  unfold varsOkB at hv
  simp only [Bool.and_eq_true, List.all_eq_true] at hv
  exact (hv.2 s hs).2 x hx v hvm

end Scope

theorem isLoadId_spec (trs : List SSt) (v : EvId) (h : isLoadId trs v = true) :
    v ∈ sids trs ∧ (sskOf trs v).kind.isLoad = true := by
  simp only [isLoadId, Bool.and_eq_true, List.contains_iff_mem] at h
  exact h

/-! ## 11. The value pass is correct on consistent executions -/

section Pass

variable (T : Test) (trs : List SSt) (ν : Val) (g : List EvId)
  (hio : T.io = []) (hv : varsOkB trs = true) (hX : rvwmoRef (conc T trs ν g))

theorem mem_sids_of_gmo (hX : rvwmoRef (conc T trs ν g)) (e : EvId) (he : e ∈ g) : e ∈ sids trs := by
  have := (hX.1.1.2.1 e he).1
  rwa [conc_ids] at this

theorem gB_of_ord (hX : rvwmoRef (conc T trs ν g)) (a b : EvId) (ha : a ∈ sids trs) (hb : b ∈ sids trs)
    (h : orderedB (conc T trs ν g) a b = true) : gB g a b = true :=
  hX.1.2.2.1 a (by rw [conc_ids]; exact ha) b (by rw [conc_ids]; exact hb) h

include hv hX in
/-- Rule 9: an address source is gmo-before the access. -/
theorem gB_of_addr (e : EvId) (he : e ∈ sids trs) (hm : (sskOf trs e).kind.isMem = true) (v : EvId)
    (hvm : v ∈ (sevAt trs e).addr.vars) : gB g v e = true := by
  obtain ⟨h1, h2, h3⟩ := varsOk_addr trs hv e he v hvm
  obtain ⟨hvs, hvl⟩ := isLoadId_spec trs v h3
  have hve : (e.1, v.2) = v := by rw [← h1]
  obtain ⟨hii, _, _⟩ := varsOk_deps trs hv e he v.2 (by simp at h2; simp [h2])
  rw [hve] at hii
  apply gB_of_ord T trs ν g hX v e hvs he
  apply ppo_ordered
  apply ppoB_intro
  · rw [conc_sk]; exact Kind.isMem_of_isLoad _ hvl
  · rw [conc_sk]; exact hm
  · simp only [poX, conc_skf, poS, h1, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]; exact hii
  · have : staticRules (conc T trs ν g).ids (conc T trs ν g).sk (isIo (conc T trs ν g)) v e = true := by
      have h2' : v.2 ∈ (sskOf trs e).adep := by simpa using h2
      simp [staticRules, rule9, conc_skf, h1, h2']
    simp [this]

include hv hX in
/-- Rule 10 (or the AMO itself): a data source of a store is gmo-before it, or is the AMO. -/
theorem gB_of_wval (e : EvId) (he : e ∈ sids trs) (hst : (sskOf trs e).kind.isStore = true) (v : EvId)
    (hvm : v ∈ (sevAt trs e).wval.vars) : gB g v e = true ∨ v = e := by
  obtain ⟨h1, h2, h3⟩ := varsOk_wval trs hv e he v hvm
  obtain ⟨hvs, hvl⟩ := isLoadId_spec trs v h3
  rcases h2 with h2 | ⟨_, h2⟩
  · left
    have hve : (e.1, v.2) = v := by rw [← h1]
    obtain ⟨hii, _, _⟩ := varsOk_deps trs hv e he v.2 (by simp at h2; simp [h2])
    rw [hve] at hii
    apply gB_of_ord T trs ν g hX v e hvs he
    apply ppo_ordered
    apply ppoB_intro
    · rw [conc_sk]; exact Kind.isMem_of_isLoad _ hvl
    · rw [conc_sk]; exact Kind.isMem_of_isStore _ hst
    · simp only [poX, conc_skf, poS, h1, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]; exact hii
    · have : staticRules (conc T trs ν g).ids (conc T trs ν g).sk (isIo (conc T trs ν g)) v e = true := by
        have h2' : v.2 ∈ (sskOf trs e).ddep := by simpa using h2
        simp [staticRules, rule10, conc_skf, h1, h2', hst]
      simp [this]
  · right; exact Prod.ext h1 h2

include hv hX in
/-- The variables of a store gmo-before `r` are gmo-before `r`. -/
theorem vars_before (r w : EvId) (hw : w ∈ sids trs) (hst : (sskOf trs w).kind.isStore = true)
    (hB : gB g w r = true) (v : EvId) (hvm : v ∈ varsOfS (sevAt trs w)) :
    gB g v r = true ∧ isLoadId trs v = true := by
  rcases List.mem_append.1 hvm with hvm | hvm
  · exact ⟨gB_trans g v w r (gB_of_addr T trs ν g hv hX w hw (Kind.isMem_of_isStore _ hst) v hvm) hB,
      (varsOk_addr trs hv w hw v hvm).2.2⟩
  · refine ⟨?_, (varsOk_wval trs hv w hw v hvm).2.2⟩
    rcases gB_of_wval T trs ν g hv hX w hw hst v hvm with h | h
    · exact gB_trans g v w r h hB
    · rw [h]; exact hB

theorem touches_concEv (ν : Val) (h i : Nat) (se : SEv) (x : Nat) :
    touches (concEv ν h i se) x = touchesS ν se x := rfl

theorem wbyte_concEv (ν : Val) (h i : Nat) (se : SEv) (x : Nat) (hs : se.sk.kind.isStore = true) :
    wbyte (concEv ν h i se) x = wbyteS ν se x := by
  simp [wbyte, wbyteS, concEv, hs]

theorem getLast?_filter_of (l : List EvId) (q : EvId → Bool) (w : EvId) (h : l.getLast? = some w)
    (hq : q w = true) : (l.filter q).getLast? = some w := by
  obtain ⟨l', rfl⟩ := List.getLast?_eq_some_iff.1 h
  simp [List.filter_append, hq]

theorem writesB_concEv (ν : Val) (h i : Nat) (se : SEv) (x : Nat) :
    writesB (concEv ν h i se) x = (se.sk.kind.isStore && touchesS ν se x) := rfl

include hv in
theorem vars_isLoad (w : EvId) (hw : w ∈ sids trs) (v : EvId) (hvm : v ∈ varsOfS (sevAt trs w)) :
    isLoadId trs v = true := by
  rcases List.mem_append.1 hvm with hvm | hvm
  · exact (varsOk_addr trs hv w hw v hvm).2.2
  · exact (varsOk_wval trs hv w hw v hvm).2.2

theorem touchesS_congr (ν₁ ν₂ : Val) (se : SEv) (x : Nat) (h : ∀ v ∈ varsOfS se, ν₁ v = ν₂ v) :
    touchesS ν₁ se x = touchesS ν₂ se x := by
  unfold touchesS
  rw [Ex.eval_congr ν₁ ν₂ se.addr (fun v hv => h v (List.mem_append_left _ hv))]

theorem wbyteS_congr (ν₁ ν₂ : Val) (se : SEv) (x : Nat) (h : ∀ v ∈ varsOfS se, ν₁ v = ν₂ v) :
    wbyteS ν₁ se x = wbyteS ν₂ se x := by
  unfold wbyteS
  rw [Ex.eval_congr ν₁ ν₂ se.addr (fun v hv => h v (List.mem_append_left _ hv)),
    Ex.eval_congr ν₁ ν₂ se.wval (fun v hv => h v (List.mem_append_right _ hv))]

include hio hv hX in
/-- One byte of the pass equals the load value axiom's answer. -/
theorem byte_eq (ν' : Val) (r : EvId) (hrs : r ∈ sids trs) (hrl : (sskOf trs r).kind.isLoad = true)
    (hag : ∀ v, gB g v r = true → isLoadId trs v = true → ν' v = ν v) (k : Nat) (hk : k < (sskOf trs r).sz)
    (x : Nat) (hx : x = ((conc T trs ν g).ev r).pa + k) :
    (match (g.filter (candP trs g ν' r x)).getLast? with
      | some w => wbyteS ν' (sevAt trs w) x
      | none => T.imgF x) = lvVal (conc T trs ν g) r x := by
  -- the pass's filter is the axiom's filter, restricted
  have hpt : ∀ w ∈ g, candP trs g ν' r x w =
      ((writesB ((conc T trs ν g).ev w) x && (gmoBefore (conc T trs ν g) w r || poX (conc T trs ν g) w r)) &&
       (gB g w r || (varsOfS (sevAt trs w)).all (fun v => gB g v r))) := by
    intro w hw
    have hws := mem_sids_of_gmo T trs ν g hX w hw
    rw [conc_ev T trs ν g w hws, writesB_concEv]
    have hgm : gmoBefore (conc T trs ν g) w r = gB g w r := rfl
    have hpo : poX (conc T trs ν g) w r = poS (sskOf trs) w r := by simp [poX, conc_skf]
    rw [hgm, hpo]
    show ((sskOf trs w).kind.isStore && touchesS ν' (sevAt trs w) x &&
      (gB g w r || (poS (sskOf trs) w r && (varsOfS (sevAt trs w)).all (fun v => gB g v r)))) = _
    cases hs : (sskOf trs w).kind.isStore
    · simp [sskOf] at hs ⊢; simp [hs]
    · cases hB : gB g w r
      · cases hV : (varsOfS (sevAt trs w)).all (fun v => gB g v r)
        · simp
        · have hagw : ∀ v ∈ varsOfS (sevAt trs w), ν' v = ν v := fun v hvm =>
            hag v (List.all_eq_true.1 hV v hvm) (vars_isLoad trs hv w hws v hvm)
          rw [touchesS_congr ν' ν _ x hagw]
          simp [sskOf] at hs ⊢; simp [hs]
      · have hagw : ∀ v ∈ varsOfS (sevAt trs w), ν' v = ν v := fun v hvm =>
          let h := vars_before T trs ν g hv hX r w hws hs hB v hvm
          hag v h.1 h.2
        rw [touchesS_congr ν' ν _ x hagw]
        simp [sskOf] at hs ⊢; simp [hs]
  have hfil : g.filter (candP trs g ν' r x) =
      (g.filter (fun w => writesB ((conc T trs ν g).ev w) x &&
        (gmoBefore (conc T trs ν g) w r || poX (conc T trs ν g) w r))).filter
        (fun w => gB g w r || (varsOfS (sevAt trs w)).all (fun v => gB g v r)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro w hw
    rw [hpt w hw, Bool.and_comm]
  have hrf : rfSrc (conc T trs ν g) r x =
      (g.filter (fun w => writesB ((conc T trs ν g).ev w) x &&
        (gmoBefore (conc T trs ν g) w r || poX (conc T trs ν g) w r))).getLast? := rfl
  unfold lvVal
  rw [hfil]
  cases hL : rfSrc (conc T trs ν g) r x with
  | none =>
    rw [hrf] at hL
    rw [List.getLast?_eq_none_iff.1 hL]
    rfl
  | some w =>
    have hrf' : rfSrc (conc T trs ν g) r (((conc T trs ν g).ev r).pa + k) = some w := by rw [← hx]; exact hL
    rw [hrf] at hL
    have hwm : w ∈ g.filter (fun w => writesB ((conc T trs ν g).ev w) x &&
        (gmoBefore (conc T trs ν g) w r || poX (conc T trs ν g) w r)) := by
      obtain ⟨l', hl'⟩ := List.getLast?_eq_some_iff.1 hL
      rw [hl']; simp
    obtain ⟨hwg, hPt⟩ := List.mem_filter.1 hwm
    have hws := mem_sids_of_gmo T trs ν g hX w hwg
    have hPt' := hPt
    rw [conc_ev T trs ν g w hws, writesB_concEv] at hPt'
    simp only [Bool.and_eq_true, Bool.or_eq_true] at hPt'
    have hst : (sskOf trs w).kind.isStore = true := hPt'.1.1
    have hQ : (gB g w r || (varsOfS (sevAt trs w)).all (fun v => gB g v r)) = true := by
      cases hB : gB g w r
      · simp only [Bool.false_or]
        have hpo : poX (conc T trs ν g) w r = true := by
          rcases hPt'.2 with h | h
          · exact absurd h (by rw [show gmoBefore (conc T trs ν g) w r = gB g w r from rfl, hB]; simp)
          · exact h
        have hpo' : w.1 = r.1 ∧ (sskOf trs w).ii < (sskOf trs r).ii := by
          simpa [poX, poS, conc_skf] using hpo
        have hrs' : r ∈ (conc T trs ν g).ids := by rw [conc_ids]; exact hrs
        have hws' : w ∈ (conc T trs ν g).ids := by rw [conc_ids]; exact hws
        cases hk' : (sskOf trs w).kind with
        | st =>
          apply List.all_eq_true.2
          intro v hvm
          have hdv : v.1 = w.1 ∧ ((sskOf trs w).adep.contains v.2 || (sskOf trs w).ddep.contains v.2) = true ∧
              isLoadId trs v = true := by
            rcases List.mem_append.1 hvm with hvm | hvm
            · obtain ⟨h1, h2, h3⟩ := varsOk_addr trs hv w hws v hvm
              exact ⟨h1, by simp at h2; simp [h2], h3⟩
            · obtain ⟨h1, h2, h3⟩ := varsOk_wval trs hv w hws v hvm
              rcases h2 with h2 | ⟨h2, _⟩
              · exact ⟨h1, by simp at h2; simp [h2], h3⟩
              · rw [hk'] at h2; cases h2
          obtain ⟨h1, h2, h3⟩ := hdv
          obtain ⟨hvs, hvl⟩ := isLoadId_spec trs v h3
          have hve : (w.1, v.2) = v := by rw [← h1]
          obtain ⟨hii, _, _⟩ := varsOk_deps trs hv w hws v.2 (by
            simp only [Bool.or_eq_true, List.contains_iff_mem] at h2
            simp only [List.mem_append]
            rcases h2 with h2 | h2
            · exact Or.inl (Or.inl h2)
            · exact Or.inl (Or.inr h2))
          rw [hve] at hii
          apply gB_of_ord T trs ν g hX v r hvs hrs
          apply ppo_ordered
          apply ppoB_intro
          · rw [conc_sk]; exact Kind.isMem_of_isLoad _ hvl
          · rw [conc_sk]; exact Kind.isMem_of_isLoad _ hrl
          · simp only [poX, conc_skf, poS, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
            exact ⟨h1.trans hpo'.1, Nat.lt_trans hii hpo'.2⟩
          · have h12 : rule12 (conc T trs ν g) v r = true := by
              unfold rule12
              simp only [conc_skf, isIo_conc T trs ν g hio, hrl, Bool.true_and, Bool.not_false,
                List.any_eq_true]
              refine ⟨w, hws', ?_⟩
              simp only [Bool.and_eq_true, beq_iff_eq]
              refine ⟨⟨⟨⟨?_, ?_⟩, hst⟩, h2⟩, List.any_eq_true.2 ⟨k, List.mem_range.2 hk, by rw [hrf']; simp⟩⟩
              · simp only [poX, conc_skf, poS, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
                exact ⟨h1, hii⟩
              · exact hpo
            simp [h12]
        | amo | sc =>
          exfalso
          have h3 : rule3 (conc T trs ν g) w r = true := by
            unfold rule3
            simp only [conc_skf, isIo_conc T trs ν g hio, hk', Kind.isRmwW, hrl, Bool.true_and,
              Bool.not_false]
            exact List.any_eq_true.2 ⟨k, List.mem_range.2 hk, by rw [hrf']; simp⟩
          have := gB_of_ord T trs ν g hX w r hws hrs (ppo_ordered _ _ _ (ppoB_intro _ _ _
            (by rw [conc_sk]; exact Kind.isMem_of_isStore _ hst)
            (by rw [conc_sk]; exact Kind.isMem_of_isLoad _ hrl) hpo (by simp [h3])))
          rw [hB] at this; cases this
        | ld | lr | scFail | fence _ => rw [hk'] at hst; cases hst
      · rfl
    rw [getLast?_filter_of _ _ w hL hQ]
    show wbyteS ν' (sevAt trs w) x = wbyte ((conc T trs ν g).ev w) x
    rw [conc_ev T trs ν g w hws, wbyte_concEv _ _ _ _ _ hst]
    apply wbyteS_congr
    intro v hvm
    cases hB : gB g w r
    · rw [hB] at hQ
      exact hag v (List.all_eq_true.1 (by simpa only [Bool.false_or] using hQ) v hvm) (vars_isLoad trs hv w hws v hvm)
    · have h := vars_before T trs ν g hv hX r w hws hst hB v hvm
      exact hag v h.1 h.2

include hio hv hX in
/-- The pass computes a load's bytes correctly from correct gmo-earlier values. -/
theorem lvComp_eq (ν' : Val) (r : EvId) (hr : r ∈ g) (hrl : (sskOf trs r).kind.isLoad = true)
    (hag : ∀ v, gB g v r = true → isLoadId trs v = true → ν' v = ν v) :
    lvComp T.imgF trs g ν' r = ν r := by
  have hrs := mem_sids_of_gmo T trs ν g hX r hr
  have hXr := conc_ev T trs ν g r hrs
  have hpa : (sevAt trs r).addr.eval ν' = ((conc T trs ν g).ev r).pa := by
    rw [hXr]
    exact Ex.eval_congr _ _ _ (fun v hvm => hag v
      (gB_of_addr T trs ν g hv hX r hrs (Kind.isMem_of_isLoad _ hrl) v hvm) (varsOk_addr trs hv r hrs v hvm).2.2)
  have hrd : ((conc T trs ν g).ev r).rdat = ν r := by
    have h' : (sevAt trs r).sk.kind.isLoad = true := hrl
    rw [hXr]; simp only [concEv, h', if_true]
  have hrs' : r ∈ (conc T trs ν g).ids := by rw [conc_ids]; exact hrs
  have hlen : (ν r).length = (sskOf trs r).sz := by
    rw [← hrd]
    have := (hX.1.2.1 r hrs').1 (by rw [conc_sk]; exact hrl)
    rwa [conc_sk] at this
  have hlv := hX.1.2.2.2.1 r hrs' (by rw [conc_sk]; exact hrl) (isIo_nil _ hio r)
  apply List.ext_getElem?
  intro k
  unfold lvComp
  by_cases hk : k < (sskOf trs r).sz
  · rw [List.getElem?_map, List.getElem?_range hk]
    have := hlv k (by simpa [conc_sk] using hk)
    rw [hrd] at this
    rw [this]
    show some _ = _
    congr 1
    simp only [hpa]
    exact byte_eq T trs ν g hio hv hX ν' r hrs hrl hag k hk _ rfl
  · rw [List.getElem?_map, List.getElem?_eq_none (by simp; omega)]
    symm
    apply List.getElem?_eq_none
    omega

include hio hv hX in
theorem pass_take (n : Nat) : ∀ e ∈ g.take n, (sskOf trs e).kind.isLoad = true →
    lk ((g.take n).foldl (passStep T.imgF trs g) []) e = ν e := by
  induction n with
  | zero => intro e he; simp at he
  | succ n ih =>
    by_cases hn : n < g.length
    · have ht : g.take (n + 1) = g.take n ++ [g[n]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hn]; rfl
      rw [ht, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      intro e he hel
      have hnd : g.Nodup := hX.1.1.1
      unfold passStep
      by_cases hrl : (sskOf trs g[n]).kind.isLoad = true
      · rw [if_pos hrl]
        by_cases her : e = g[n]
        · subst her
          simp only [lk, List.lookup, beq_self_eq_true, Option.getD_some]
          apply lvComp_eq T trs ν g hio hv hX _ _ (List.getElem_mem hn) hrl
          intro v hvr hvl
          obtain ⟨hvg, _, hlt⟩ := gB_mem g v _ hvr
          rw [pos_getElem g hnd n hn] at hlt
          exact ih v (mem_take_of_pos_lt g v hvg n hlt) (isLoadId_spec trs v hvl).2
        · have hne : (e == g[n]) = false := by simp [her]
          simp only [lk, List.lookup, hne]
          rcases List.mem_append.1 he with he | he
          · exact ih e he hel
          · exact absurd (List.mem_singleton.1 he) her
      · rw [if_neg hrl]
        rcases List.mem_append.1 he with he | he
        · exact ih e he hel
        · rw [List.mem_singleton.1 he] at hel; exact absurd hel hrl
    · have h1 : g.take (n + 1) = g := List.take_of_length_le (by omega)
      have h2 : g.take n = g := List.take_of_length_le (by omega)
      rw [h1]; rw [h2] at ih; exact ih

include hio hv hX in
/-- **THE PASS IS CORRECT**: on a consistent execution, the pass recomputes every load's bytes. -/
theorem pass_correct (e : EvId) (he : e ∈ g) (hel : (sskOf trs e).kind.isLoad = true) :
    lk (passVals T.imgF trs g) e = ν e := by
  have := pass_take T trs ν g hio hv hX g.length e (by rw [List.take_of_length_le (Nat.le_refl _)]; exact he) hel
  rwa [List.take_of_length_le (Nat.le_refl _)] at this

end Pass

/-! ## 12. Congruence: the execution depends on the valuation only at load events -/

theorem all_congr' {α : Type} (l : List α) (p q : α → Bool) (h : ∀ x ∈ l, p x = q x) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.all_cons]
    rw [h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem mem_ev_sids (trs : List SSt) (s : SSt) (hs : s ∈ trs) (se : SEv) (hse : se ∈ s.evs) :
    ∃ e ∈ sids trs, sevAt trs e = se := by
  obtain ⟨h, hh, rfl⟩ := List.getElem_of_mem hs
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hse
  refine ⟨(h, i), (mem_idsOf _ _).2 ⟨trs[h].evs, by simp [hh], hi⟩, ?_⟩
  simp [sevAt, List.getElem?_eq_getElem hh, List.getElem?_eq_getElem hi]

theorem concEv_congr (ν₁ ν₂ : Val) (h i : Nat) (se : SEv) (hvars : ∀ v ∈ varsOfS se, ν₁ v = ν₂ v)
    (hld : se.sk.kind.isLoad = true → ν₁ (h, i) = ν₂ (h, i)) : concEv ν₁ h i se = concEv ν₂ h i se := by
  unfold concEv
  rw [Ex.eval_congr ν₁ ν₂ se.addr (fun v hv => hvars v (List.mem_append_left _ hv)),
    Ex.eval_congr ν₁ ν₂ se.wval (fun v hv => hvars v (List.mem_append_right _ hv))]
  by_cases hl : se.sk.kind.isLoad = true
  · rw [hld hl]
  · simp [hl]

theorem conc_congr (T : Test) (trs : List SSt) (g : List EvId) (hv : varsOkB trs = true) (ν₁ ν₂ : Val)
    (hag : ∀ e ∈ sids trs, (sskOf trs e).kind.isLoad = true → ν₁ e = ν₂ e) :
    conc T trs ν₁ g = conc T trs ν₂ g := by
  unfold conc
  congr 1
  apply List.ext_getElem?
  intro h
  rw [List.getElem?_mapIdx, List.getElem?_mapIdx]
  cases hs : trs[h]? with
  | none => rfl
  | some s =>
    simp only [Option.map_some, Option.some.injEq]
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_mapIdx, List.getElem?_mapIdx]
    cases hse : s.evs[i]? with
    | none => rfl
    | some se =>
      simp only [Option.map_some, Option.some.injEq]
      have hi : i < s.evs.length := by
        rcases Nat.lt_or_ge i s.evs.length with h1 | h1
        · exact h1
        · rw [List.getElem?_eq_none h1] at hse; cases hse
      have hid : (h, i) ∈ sids trs := (mem_idsOf _ _).2 ⟨s.evs, by simp [hs], hi⟩
      have hsev : sevAt trs (h, i) = se := by simp [sevAt, hs, hse]
      apply concEv_congr
      · intro v hvm
        rw [← hsev] at hvm
        obtain ⟨hvs, hvl⟩ := isLoadId_spec trs v (vars_isLoad trs hv (h, i) hid v hvm)
        exact hag v hvs hvl
      · intro hl
        exact hag (h, i) hid (by simp [sskOf, hsev, hl])

theorem condsOk_congr (trs : List SSt) (hv : varsOkB trs = true) (ν₁ ν₂ : Val)
    (hag : ∀ v, isLoadId trs v = true → ν₁ v = ν₂ v) : condsOk ν₁ trs = condsOk ν₂ trs := by
  unfold condsOk
  apply all_congr'
  intro s hs
  congr 1
  · apply all_congr'
    intro c hc
    obtain ⟨cc, a, b, t⟩ := c
    show (brEval cc (a.eval ν₁) (b.eval ν₁) == t) = (brEval cc (a.eval ν₂) (b.eval ν₂) == t)
    rw [Ex.eval_congr ν₁ ν₂ a (fun v hvm => hag v (varsOk_conds trs hv s hs _ hc v (List.mem_append_left _ hvm))),
      Ex.eval_congr ν₁ ν₂ b
        (fun v hvm => hag v (varsOk_conds trs hv s hs _ hc v (List.mem_append_right _ hvm)))]
  · apply all_congr'
    intro se hse
    obtain ⟨e, he, rfl⟩ := mem_ev_sids trs s hs se hse
    rw [Ex.eval_congr ν₁ ν₂ (sevAt trs e).addr (fun v hvm => hag v (varsOk_addr trs hv e he v hvm).2.2)]

theorem finalReg_congr (trs : List SSt) (hv : varsOkB trs = true) (ν₁ ν₂ : Val)
    (hag : ∀ v, isLoadId trs v = true → ν₁ v = ν₂ v) : finalReg trs ν₁ = finalReg trs ν₂ := by
  funext h r
  unfold finalReg
  cases hs : trs[h]? with
  | none => rfl
  | some s =>
    have hsm : s ∈ trs := List.mem_of_getElem? hs
    simp only [Option.map_some, Option.getD_some]
    apply Ex.eval_congr
    intro v hvm
    apply hag
    unfold SSt.rd at hvm
    by_cases hr : r = 0
    · rw [if_pos hr] at hvm; cases hvm
    · rw [if_neg hr] at hvm
      cases hx : s.regs[r]? with
      | none => rw [hx] at hvm; cases hvm
      | some x =>
        rw [hx] at hvm
        exact varsOk_regs trs hv s hsm x (List.mem_of_getElem? hx) v hvm

/-! ## 13. The verdict theorems' combinators -/

/-- **SOUNDNESS of `existsB`**: a candidate that passes the check is an execution with the outcome. -/
theorem exists_sound (T : Test) (h : existsB T = true) : allowedRef T := by
  unfold existsB at h
  obtain ⟨⟨chs, trs⟩, hp, hg⟩ := List.any_eq_true.1 h
  obtain ⟨g, _, hc⟩ := List.any_eq_true.1 hg
  have hR := paths_runAll T chs trs hp
  unfold checkCand at hc
  simp only [Bool.and_eq_true] at hc
  refine ⟨chs, lk (passVals T.imgF trs g), g, ?_, ?_⟩
  · unfold progExec; rw [hR]; exact ⟨hc.1.2, refCoreB_sound _ hc.2⟩
  · unfold outcome; rw [hR]; exact hc.1.1

/-- **COMPLETENESS of the enumerator, as a verdict**: if no candidate passes the check (and the test is in the
enumerator's scope), the reference forbids the outcome. -/
theorem forbid_sound (T : Test) (hf : forbidB T = true) : forbiddenRef T := by
  intro chs ν g hP hO
  unfold progExec at hP
  unfold outcome at hO
  cases hR : T.runAll chs with
  | none => rw [hR] at hP; exact hP
  | some trs =>
    rw [hR] at hP hO
    obtain ⟨hc, hX⟩ := hP
    unfold forbidB at hf
    simp only [Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff] at hf
    obtain ⟨hio, hall⟩ := hf
    obtain ⟨hv, hcands⟩ := hall (chs, trs) (runAll_paths T chs trs hR)
    have hwf := hX.1.1
    have hmem : ∀ x, x ∈ g ↔ x ∈ memIds trs := by
      intro x
      unfold memIds
      rw [List.mem_filter]
      constructor
      · intro hx
        have := hwf.2.1 x hx
        rw [conc_ids, conc_sk] at this
        exact this
      · rintro ⟨hx, hm⟩
        exact hwf.2.2 x (by rw [conc_ids]; exact hx) (by rw [conc_sk]; exact hm)
    have hresp : respects (statRel trs) g := by
      intro a b hab ha hb
      have hab' : staticOrd (conc T trs ν g).ids (conc T trs ν g).sk (isIo (conc T trs ν g)) a b = true := by
        rw [conc_ids, conc_skf, isIo_conc T trs ν g hio]; exact hab
      have := gB_of_ord T trs ν g hX a b (mem_sids_of_gmo T trs ν g hX a ha) (mem_sids_of_gmo T trs ν g hX b hb)
        (ppo_ordered _ _ _ (staticOrd_ppo _ _ _ hab'))
      exact (gB_mem g a b this).2.2
    have hg : g ∈ candsOf trs :=
      lins_complete _ g (memIds trs) _ hwf.1 hmem hresp
        (nodup_length_le g (memIds trs) hwf.1 (fun x hx => (hmem x).1 hx))
    have hno := hcands g hg
    have hpass : ∀ e ∈ sids trs, (sskOf trs e).kind.isLoad = true → lk (passVals T.imgF trs g) e = ν e := by
      intro e he hel
      have heg : e ∈ g := hwf.2.2 e (by rw [conc_ids]; exact he)
        (by rw [conc_sk]; exact Kind.isMem_of_isLoad _ hel)
      exact pass_correct T trs ν g hio hv hX e heg hel
    have hpass' : ∀ v, isLoadId trs v = true → lk (passVals T.imgF trs g) v = ν v := fun v hv' =>
      hpass v (isLoadId_spec trs v hv').1 (isLoadId_spec trs v hv').2
    have hconc := conc_congr T trs g hv _ _ hpass
    have hcond := condsOk_congr trs hv _ _ hpass'
    have hfr := finalReg_congr trs hv _ _ hpass'
    have hcc : checkCand T trs g = true := by
      unfold checkCand
      simp only
      rw [hconc, hcond, hfr, hO, hc, refCoreB_complete _ hX]
      rfl
    rw [hcc] at hno
    cases hno

/-- A probe about one candidate: the check passes and the gmo satisfies `p` (for properties of gmo itself, e.g.
I/O ordering, which no final-state outcome can express). -/
def probeB (T : Test) (chs : List (List Bool)) (g : List EvId) (p : List EvId → Bool) : Bool :=
  match T.runAll chs with
  | some trs => checkCand T trs g && p g
  | none => false

theorem probe_sound (T : Test) (chs : List (List Bool)) (g : List EvId) (p : List EvId → Bool)
    (h : probeB T chs g p = true) : ∃ ν, progExec T chs ν g ∧ outcome T chs ν g ∧ p g = true := by
  unfold probeB at h
  cases hR : T.runAll chs with
  | none => rw [hR] at h; cases h
  | some trs =>
    rw [hR] at h
    unfold checkCand at h
    simp only [Bool.and_eq_true] at h
    refine ⟨lk (passVals T.imgF trs g), ?_, ?_, h.2⟩
    · unfold progExec; rw [hR]; exact ⟨h.1.1.2, refCoreB_sound _ h.1.2⟩
    · unfold outcome; rw [hR]; exact h.1.1.1

end Weak.Prom.Ref
