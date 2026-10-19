/-
Weak: **allocproc route P, increment P-W2 (1/3) — `SbWalk`, the BUFFERED walk candidate and walk state**
(`notes/weak-allocproc-routeP-design.md` §3.2; plan rev 55 row P-W2; rulings [OWN.106] [OWN.112]
[OWN.113]).  Lean-only, no Rocq twin.  A PRIMED TWIN: nothing registered imports this file.

The walk of route P is built STEP BY STEP ([OWN.106]): each walk step appends ONE item to the
candidate, an EVENT (the next GF event of a row, an `SbCand.stepE` step) or a LANDING (an admin step,
`SbCand.land`, of any policy-landable pending store).  This file is the bookkeeping of that walk,
re-parametrized from `SilWalk`/`SilReplay` on `SbCand` (no silent column, NO dependency shadow — route P
has no silent write to bound — plus the pending lists):

  §1  `SbWalk.Item` / `SbWalk.CandW` (an image and an item list), the walk machine state
      **`SbWalk.WS`** — the `SbCand` state, each pending entry tagged with its store's ROW INDEX
      (`pend`), the member rows so far (`rows`, the labels as stepped), the forwarding record of each
      load (`fw`: per byte, the row index of the store it forwarded from), and the member's gmo so far
      (`gmo`: loads / AMOs / I/O at their event, plain stores at their LANDING) — the states
      **`SbWalk.stAt`**, validity **`SbWalk.validW pol`** (every event an `SbCand.stepE` step, every
      landing `pol.landOk`), and the bookkeeping invariant **`SbWalk.Inv`** (`invStAt`: it holds at
      every state of a valid candidate) — the buffers are the tagged lists, every pending tag names its
      store's row label and message, tags are fresh, the gmo lists every memory event exactly once once
      landed, and THE LOG IS THE GMO'S WRITE MESSAGES (`Inv.log`), the label shapes of `gwf`;
  §2  the walk state **`SbWalk.St`** (candidate, program states, fabric), the program data
      **`SbWalk.progOk`** (`SilReplay.progOkD` without the shadow: an event item is the program's
      admin star, its fetches at view 0 of the LANDED log, then the label realized by one pf label or
      the exclusive pair at the `SbCand` state's views; a landing moves no program), the walk invariant
      **`SbWalk.ok`**, the one-step extensions **`SbWalk.okSnocE`** / **`SbWalk.okSnocL`**, the start
      `SbWalk.okStart`, and the agent bound `SbWalk.agBound`.

Spec: FAITHFUL (proof organisation; the machine is `SbCand`'s, the program data `SilReplay`'s).
Lean-only helpers `SbWalk.*`.
-/
import Weak.SbCand
import Weak.SilReplay

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

namespace SbWalk

/-! # 1. The walk candidate and its machine states -/

/-- A walk item: an event of agent `s.esAg`, or the landing of agent `i`'s `k`-th pending entry. -/
inductive Item where
  | ev (s : Estep)
  | land (i k : Nat)
  deriving DecidableEq, Inhabited

/-- **THE WALK CANDIDATE**: the image and the items, in walk order. -/
structure CandW where
  img : Image
  its : List Item

def upd {α : Type} (f : Nat → α) (i : Nat) (a : α) : Nat → α := fun j => if j = i then a else f j

theorem updEq {α : Type} (f : Nat → α) (i : Nat) (a : α) : upd f i a i = a := by simp [upd]

theorem updNe {α : Type} (f : Nat → α) (i : Nat) (a : α) (j : Nat) : j ≠ i → upd f i a j = f j := by
  intro h; simp [upd, h]

/-- A plain store (issued into the buffer; in gmo at its landing). -/
def isSt (l : Lbl) : Bool :=
  match l with
  | LStore .. => true
  | _ => false

/-- A memory event placed in gmo AT ITS EVENT: a load, an AMO, an I/O access. -/
def gmoEv (l : Lbl) : Bool := lbIsMem l && !isSt l

/-- The row index of the store a byte `a` forwards from: the YOUNGEST tagged pending entry covering it
(`SbCand.fwdByte`'s choice). -/
def fwdId (ps : List (Nat × SbEnt)) (a : Int) : Option Nat :=
  ps.foldl (fun o p => if (msgByte p.2.msg a).isSome then some p.1 else o) none

/-- The forwarding record of a label: per byte of a load, the forwarding store's row index. -/
def fwOf (ps : List (Nat × SbEnt)) (l : Lbl) : List (Option Nat) :=
  match l with
  | LLoad _ base ts _ => (List.range ts.length).map (fun j => fwdId ps (accAddr base j))
  | _ => []

/-- **THE WALK MACHINE STATE.** -/
structure WS where
  σ : SbCand.CandS
  pend : Nat → List (Nat × SbEnt)
  rows : Nat → List Lbl
  fw : Nat → List (List (Option Nat))
  gmo : List Geid

def init (img : Image) : WS :=
  ⟨⟨⟨img, [], fun _ => wsInit⟩, fun _ => []⟩, fun _ => [], fun _ => [], fun _ => [], []⟩

/-- The tagged buffer after an event. -/
def pendE (w : WS) (i : Nat) (l : Lbl) : List (Nat × SbEnt) :=
  match l with
  | LStore rl base vs k => w.pend i ++ [((w.rows i).length, SbCand.issueEnt w.σ i rl base vs k)]
  | LFence _ pw _ sw => if pw && sw then (w.pend i).map (fun p => (p.1, p.2.bump)) else w.pend i
  | _ => w.pend i

/-- One walk item. -/
def nextI (w : WS) : Item → WS
  | .ev s =>
    ⟨SbCand.nextE w.σ s.esAg s.esLb,
     upd w.pend s.esAg (pendE w s.esAg s.esLb),
     upd w.rows s.esAg (w.rows s.esAg ++ [s.esLb]),
     upd w.fw s.esAg (w.fw s.esAg ++ [fwOf (w.pend s.esAg) s.esLb]),
     if gmoEv s.esLb then w.gmo ++ [(s.esAg, (w.rows s.esAg).length)] else w.gmo⟩
  | .land i k =>
    match (w.pend i)[k]? with
    | some p =>
      ⟨SbCand.nextL w.σ i k, upd w.pend i ((w.pend i).eraseIdx k), w.rows, w.fw,
       w.gmo ++ [(i, p.1)]⟩
    | none => w

/-- **THE WALK'S STATES.** -/
def stAt (c : CandW) : Nat → WS
  | 0 => init c.img
  | k + 1 =>
    match c.its[k]? with
    | some it => nextI (stAt c k) it
    | none => stAt c k

theorem stAtSucc (c : CandW) (k : Nat) (it : Item) :
    c.its[k]? = some it → stAt c (k + 1) = nextI (stAt c k) it := by
  intro h
  show (match c.its[k]? with
    | some it => nextI (stAt c k) it
    | none => stAt c k) = _
  rw [h]

/-- What an item owes at the state before it. -/
def okI (pol : SbPol) (w : WS) : Item → Prop
  | .ev s => SbCand.stepE w.σ s.esAg s.esLb (SbCand.nextE w.σ s.esAg s.esLb)
  | .land i k => pol.landOk (w.σ.sb i) k

/-- **WALK VALIDITY** under the landing policy `pol`. -/
def validW (pol : SbPol) (c : CandW) : Prop :=
  ∀ (k : Nat) (it : Item), c.its[k]? = some it → okI pol (stAt c k) it

/-- The message a member event writes (as `WeakRvwmoKillArms.gmsg`, off the rows). -/
def wmsgOf (rows : Nat → List Lbl) (e : Geid) : Option Wmsg :=
  match (rows e.1)[e.2]? with
  | some l =>
    match lbWr l with
    | some (base, vs) => some ⟨base, vs, some e.1, lbCls l⟩
    | none => none
  | none => none

/-- The label shapes of `gwf`. -/
def shapeOk (l : Lbl) : Prop :=
  match l with
  | LLoad _ _ ts vs => vs.length = ts.length
  | LStore _ _ vs _ => vs ≠ []
  | LFence _ _ _ _ => True
  | LRmw _ _ _ ts rvs wvs _ => wvs ≠ [] ∧ wvs.length = ts.length ∧ rvs.length = ts.length
  | LIo .. => True

/-- **THE BOOKKEEPING INVARIANT.** -/
structure Inv (img : Image) (w : WS) : Prop where
  img : w.σ.ms.msImg = img
  sb : ∀ i : Nat, w.σ.sb i = (w.pend i).map Prod.snd
  pendSt : ∀ (i : Nat) (p : Nat × SbEnt), p ∈ w.pend i → ∃ rl base vs kc,
    (w.rows i)[p.1]? = some (LStore rl base vs kc) ∧ p.2.msg = ⟨base, vs, some i, kc⟩
  pendNd : ∀ i : Nat, ((w.pend i).map Prod.fst).Nodup
  pendGmo : ∀ (i : Nat) (p : Nat × SbEnt), p ∈ w.pend i → (i, p.1) ∉ w.gmo
  gmoNd : w.gmo.Nodup
  gmoMem : ∀ e : Geid, e ∈ w.gmo → ∃ l : Lbl, (w.rows e.1)[e.2]? = some l ∧ lbIsMem l = true
  memIn : ∀ (i r : Nat) (l : Lbl), (w.rows i)[r]? = some l → lbIsMem l = true →
    (i, r) ∈ w.gmo ∨ r ∈ (w.pend i).map Prod.fst
  log : w.σ.ms.msLog = w.gmo.filterMap (wmsgOf w.rows)
  shape : ∀ (i r : Nat) (l : Lbl), (w.rows i)[r]? = some l → shapeOk l
  fwLen : ∀ i : Nat, (w.fw i).length = (w.rows i).length

/-! ## 1.1 List helpers -/

theorem eraseIdxMid {α : Type} (a b : List α) (x : α) : (a ++ x :: b).eraseIdx a.length = a ++ b := by
  induction a with
  | nil => rfl
  | cons y a ih => simp [ih]

theorem eraseIdxSplit {α : Type} : ∀ (l : List α) (k : Nat) (p : α), l[k]? = some p →
    ∃ a b, l = a ++ p :: b ∧ a.length = k
  | [], _, _, h => by simp at h
  | y :: l, 0, p, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    exact ⟨[], l, by rw [h]; rfl, rfl⟩
  | y :: l, k + 1, p, h => by
    simp only [List.getElem?_cons_succ] at h
    obtain ⟨a, b, h1, h2⟩ := eraseIdxSplit l k p h
    exact ⟨y :: a, b, by rw [h1]; rfl, by simp [h2]⟩

theorem nodupOne {α : Type} (a : α) : [a].Nodup := List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩

theorem lookupLtSome {α : Type} {l : List α} {k : Nat} {a : α} : l[k]? = some a → k < l.length :=
  fun h => lookup_lt_Some h

theorem getAppOld {α : Type} (l : List α) (x : α) (r : Nat) (a : α) :
    l[r]? = some a → (l ++ [x])[r]? = some a := fun h => lookup_app_l_Some h

theorem getAppInv {α : Type} (l : List α) (x : α) (r : Nat) (a : α) :
    (l ++ [x])[r]? = some a → l[r]? = some a ∨ (r = l.length ∧ a = x) := by
  intro h
  by_cases hr : r < l.length
  · left; rwa [List.getElem?_append_left hr] at h
  · right
    have hle : l.length ≤ r := by omega
    rw [List.getElem?_append_right hle] at h
    have hr' : r - l.length = 0 := by
      have := lookup_lt_Some h
      simp at this; omega
    rw [hr'] at h
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    exact ⟨by omega, h.symm⟩

/-! ## 1.2 The invariant along items -/

theorem invInit (img : Image) : Inv img (init img) where
  img := rfl
  sb _ := rfl
  pendSt _ _ h := by simp [init] at h
  pendNd _ := List.nodup_nil
  pendGmo _ _ h := by simp [init] at h
  gmoNd := List.nodup_nil
  gmoMem _ h := by simp [init] at h
  memIn _ _ _ h := by simp [init] at h
  log := rfl
  shape _ _ _ h := by simp [init] at h
  fwLen _ := rfl

/-- A row lookup survives an event (rows only grow). -/
theorem rowsEvOld (w : WS) (s : Estep) (i r : Nat) (l : Lbl) :
    (w.rows i)[r]? = some l → ((nextI w (.ev s)).rows i)[r]? = some l := by
  intro h
  show (upd w.rows s.esAg (w.rows s.esAg ++ [s.esLb]) i)[r]? = some l
  by_cases hi : i = s.esAg
  · subst hi; rw [updEq]; exact getAppOld _ _ _ _ h
  · rw [updNe _ _ _ _ hi]; exact h

theorem rowsEvInv (w : WS) (s : Estep) (i r : Nat) (l : Lbl) :
    ((nextI w (.ev s)).rows i)[r]? = some l →
    (w.rows i)[r]? = some l ∨ (i = s.esAg ∧ r = (w.rows s.esAg).length ∧ l = s.esLb) := by
  intro h
  change (upd w.rows s.esAg (w.rows s.esAg ++ [s.esLb]) i)[r]? = some l at h
  by_cases hi : i = s.esAg
  · subst hi
    rw [updEq] at h
    rcases getAppInv _ _ _ _ h with h | ⟨h1, h2⟩
    · exact .inl h
    · exact .inr ⟨rfl, h1, h2⟩
  · rw [updNe _ _ _ _ hi] at h; exact .inl h

/-- The message of an old gmo event survives an event. -/
theorem wmsgEvOld (w : WS) (s : Estep) (e : Geid) (l : Lbl) :
    (w.rows e.1)[e.2]? = some l → wmsgOf (nextI w (.ev s)).rows e = wmsgOf w.rows e := by
  intro h
  unfold wmsgOf
  rw [h, rowsEvOld w s e.1 e.2 l h]

theorem filterMapCongr {α β : Type} (f g : α → Option β) (l : List α) :
    (∀ a, a ∈ l → f a = g a) → l.filterMap f = l.filterMap g := by
  intro h
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filterMap_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

/-- The shape a valid event step's label has. -/
theorem shapeOfStep (σ : SbCand.CandS) (i : Nat) (l : Lbl) :
    SbCand.stepE σ i l (SbCand.nextE σ i l) → shapeOk l := by
  intro h
  cases h with
  | load aq base ts vs hrd _ => exact hrd.1
  | issue rl base vs k hne _ => exact hne
  | fence => trivial
  | rmw aq rl base ts rvs wvs k hne hlen hrd _ _ _ _ => exact ⟨hne, hlen, hrd.1⟩
  | io => trivial

/-- The message an event appends to the LANDED log: an AMO's (a plain store only issues). -/
def evMsg (i : Nat) (l : Lbl) : List Wmsg :=
  match l with
  | LRmw _ _ base _ _ wvs k => [⟨base, wvs, some i, k⟩]
  | _ => []

/-- The log after an event: an AMO appends its message, nothing else does. -/
theorem logNextE (σ : SbCand.CandS) (i : Nat) (l : Lbl) :
    (SbCand.nextE σ i l).ms.msLog = σ.ms.msLog ++ evMsg i l ∧
    (SbCand.nextE σ i l).ms.msImg = σ.ms.msImg := by
  cases l <;> simp [SbCand.nextE, mnext, evMsg]

/-- The buffer after an event. -/
theorem sbNextE (σ : SbCand.CandS) (i : Nat) (l : Lbl) (j : Nat) :
    (SbCand.nextE σ i l).sb j =
      match l with
      | LStore rl base vs k =>
        if j = i then σ.sb i ++ [SbCand.issueEnt σ i rl base vs k] else σ.sb j
      | LFence _ pw _ sw => if pw && sw then (if j = i then (σ.sb i).map SbEnt.bump else σ.sb j)
        else σ.sb j
      | _ => σ.sb j := by
  cases l with
  | LStore => simp [SbCand.nextE, SbCand.updSb]
  | LFence pr pw sr sw =>
    by_cases h : pw && sw <;> simp [SbCand.nextE, SbCand.updSb, h]
  | _ => rfl

theorem esMsgOf (w : WS) (i : Nat) (l : Lbl) :
    evMsg i l = (if gmoEv l then [(i, (w.rows i).length)] else []).filterMap
      (wmsgOf (upd w.rows i (w.rows i ++ [l]))) := by
  have hlk : (upd w.rows i (w.rows i ++ [l]) i)[(w.rows i).length]? = some l := by
    rw [updEq]; simp
  cases l <;>
    simp [evMsg, gmoEv, isSt, lbIsMem, lbIsR, lbIsW, lbIsIo, wmsgOf, hlk, lbWr, lbCls]

/-- **THE INVARIANT ALONG AN EVENT.** -/
theorem invEv (img : Image) (w : WS) (s : Estep) :
    Inv img w → SbCand.stepE w.σ s.esAg s.esLb (SbCand.nextE w.σ s.esAg s.esLb) →
    Inv img (nextI w (.ev s)) := by
  intro hI hst
  obtain ⟨i, l⟩ := s
  dsimp only at hst
  have hlen : ∀ (p : Nat × SbEnt), p ∈ w.pend i → p.1 < (w.rows i).length := by
    intro p hp
    obtain ⟨_, _, _, _, h, -⟩ := hI.pendSt i p hp
    exact lookup_lt_Some h
  have hgl : ∀ e, e ∈ w.gmo → e.2 < (w.rows e.1).length := by
    intro e he
    obtain ⟨_, h, -⟩ := hI.gmoMem e he
    exact lookup_lt_Some h
  have hnew : (i, (w.rows i).length) ∉ w.gmo := fun h => by
    have := hgl _ h; simp at this
  -- the tagged buffer after the event, agent by agent
  have hpend : ∀ j, (nextI w (.ev ⟨i, l⟩)).pend j = if j = i then pendE w i l else w.pend j := by
    intro j; by_cases hj : j = i
    · subst hj; simp [nextI, upd]
    · simp [nextI, upd, hj]
  -- a member of the new tagged buffer: an old one (maybe bumped), or the new store
  have hpmem : ∀ j p, p ∈ (nextI w (.ev ⟨i, l⟩)).pend j →
      (∃ q, q ∈ w.pend j ∧ q.1 = p.1 ∧ q.2.msg = p.2.msg) ∨
      (j = i ∧ ∃ rl base vs k, l = LStore rl base vs k ∧ p.1 = (w.rows i).length ∧
        p.2 = SbCand.issueEnt w.σ i rl base vs k) := by
    intro j p hp
    rw [hpend j] at hp
    by_cases hj : j = i
    · subst hj
      rw [if_pos rfl] at hp
      unfold pendE at hp
      cases l with
      | LStore rl base vs k =>
        rcases List.mem_append.1 hp with hp | hp
        · exact .inl ⟨p, hp, rfl, rfl⟩
        · simp only [List.mem_singleton] at hp
          subst hp
          exact .inr ⟨rfl, rl, base, vs, k, rfl, rfl, rfl⟩
      | LFence pr pw sr sw =>
        by_cases hb : pw && sw
        · simp only [hb, if_true, List.mem_map] at hp
          obtain ⟨q, hq, rfl⟩ := hp
          exact .inl ⟨q, hq, rfl, rfl⟩
        · simp only [hb, Bool.false_eq_true, if_false] at hp
          exact .inl ⟨p, hp, rfl, rfl⟩
      | _ => exact .inl ⟨p, hp, rfl, rfl⟩
    · rw [if_neg hj] at hp
      exact .inl ⟨p, hp, rfl, rfl⟩
  have hfst : ∀ j, ((nextI w (.ev ⟨i, l⟩)).pend j).map Prod.fst =
      if j = i ∧ isSt l = true then (w.pend j).map Prod.fst ++ [(w.rows i).length]
      else (w.pend j).map Prod.fst := by
    intro j
    rw [hpend j]
    by_cases hj : j = i
    · subst hj
      rw [if_pos rfl]
      unfold pendE
      cases l with
      | LStore => simp [isSt]
      | LFence pr pw sr sw =>
        by_cases hb : pw && sw <;> simp [hb, isSt, List.map_map, Function.comp_def]
      | _ => simp [isSt]
    · simp [hj]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (SbCand.nextE w.σ i l).ms.msImg = img
    rw [(logNextE w.σ i l).2]; exact hI.img
  · intro j
    show (SbCand.nextE w.σ i l).sb j = _
    rw [sbNextE, hpend j]
    by_cases hj : j = i
    · subst hj
      rw [if_pos rfl]
      unfold pendE
      cases l with
      | LStore => simp [hI.sb]
      | LFence pr pw sr sw =>
        by_cases hb : pw && sw <;> simp [hb, hI.sb, List.map_map, Function.comp_def]
      | _ => simp [hI.sb]
    · rw [if_neg hj]
      cases l with
      | LStore => simp [hj, hI.sb]
      | LFence pr pw sr sw => by_cases hb : pw && sw <;> simp [hb, hj, hI.sb]
      | _ => simp [hj, hI.sb]
  · intro j p hp
    rcases hpmem j p hp with ⟨q, hq, h1, h2⟩ | ⟨rfl, rl, base, vs, k, rfl, h1, h2⟩
    · obtain ⟨rl, base, vs, kc, hr, hm⟩ := hI.pendSt j q hq
      exact ⟨rl, base, vs, kc, by rw [← h1]; exact rowsEvOld w _ j q.1 _ hr, by rw [← h2]; exact hm⟩
    · refine ⟨rl, base, vs, k, ?_, by rw [h2]; rfl⟩
      rw [h1]
      show (upd w.rows j (w.rows j ++ [LStore rl base vs k]) j)[(w.rows j).length]? = _
      rw [updEq]; simp
  · intro j
    rw [hfst j]
    split
    · rename_i h
      obtain ⟨rfl, -⟩ := h
      refine List.nodup_append.2 ⟨hI.pendNd j, nodupOne _, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha
      have := hlen q hq
      omega
    · exact hI.pendNd j
  · intro j p hp hin
    have hg : (j, p.1) ∈ w.gmo ∨ (gmoEv l = true ∧ (j, p.1) = (i, (w.rows i).length)) := by
      change (j, p.1) ∈ (if gmoEv l then w.gmo ++ [(i, (w.rows i).length)] else w.gmo) at hin
      split at hin
      · rename_i hgm
        rcases List.mem_append.1 hin with h | h
        · exact .inl h
        · exact .inr ⟨hgm, List.mem_singleton.1 h⟩
      · exact .inl hin
    rcases hpmem j p hp with ⟨q, hq, h1, -⟩ | ⟨rfl, rl, base, vs, k, rfl, h1, -⟩
    · rcases hg with h | ⟨-, h⟩
      · exact hI.pendGmo j q hq (by rw [h1]; exact h)
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, h⟩ := h
        have := hlen q hq
        omega
    · rcases hg with h | ⟨hgm, -⟩
      · exact hnew (by rw [← h1]; exact h)
      · simp [gmoEv, isSt] at hgm
  · change (if gmoEv l then w.gmo ++ [(i, (w.rows i).length)] else w.gmo).Nodup
    split
    · exact List.nodup_append.2 ⟨hI.gmoNd, nodupOne _,
        fun a ha b hb => by simp only [List.mem_singleton] at hb; subst hb; exact fun h => hnew (h ▸ ha)⟩
    · exact hI.gmoNd
  · intro e he
    change e ∈ (if gmoEv l then w.gmo ++ [(i, (w.rows i).length)] else w.gmo) at he
    split at he
    · rename_i hgm
      rcases List.mem_append.1 he with h | h
      · obtain ⟨l', hl', hm⟩ := hI.gmoMem e h
        exact ⟨l', rowsEvOld w _ e.1 e.2 l' hl', hm⟩
      · simp only [List.mem_singleton] at h
        subst h
        refine ⟨l, ?_, ?_⟩
        · show (upd w.rows i (w.rows i ++ [l]) i)[(w.rows i).length]? = _
          rw [updEq]; simp
        · simp only [gmoEv, Bool.and_eq_true] at hgm; exact hgm.1
    · obtain ⟨l', hl', hm⟩ := hI.gmoMem e he
      exact ⟨l', rowsEvOld w _ e.1 e.2 l' hl', hm⟩
  · intro j r l' hl' hm
    have hgold : ∀ e, e ∈ w.gmo → e ∈ (nextI w (.ev ⟨i, l⟩)).gmo := by
      intro e he
      change e ∈ (if gmoEv l then w.gmo ++ [(i, (w.rows i).length)] else w.gmo)
      split
      · exact List.mem_append.2 (.inl he)
      · exact he
    rcases rowsEvInv w ⟨i, l⟩ j r l' hl' with h | ⟨rfl, rfl, rfl⟩
    · rcases hI.memIn j r l' h hm with h | h
      · exact .inl (hgold _ h)
      · right
        rw [hfst j]
        split
        · exact List.mem_append.2 (.inl h)
        · exact h
    · by_cases hs : isSt l' = true
      · right
        rw [hfst j, if_pos ⟨rfl, hs⟩]
        exact List.mem_append.2 (.inr (List.mem_singleton.2 rfl))
      · left
        change (j, (w.rows j).length) ∈ (if gmoEv l' then w.gmo ++ [(j, (w.rows j).length)] else w.gmo)
        have hg : gmoEv l' = true := by simp [gmoEv, hm, hs]
        rw [if_pos hg]
        exact List.mem_append.2 (.inr (List.mem_singleton.2 rfl))
  · show (SbCand.nextE w.σ i l).ms.msLog = (nextI w (.ev ⟨i, l⟩)).gmo.filterMap
      (wmsgOf (nextI w (.ev ⟨i, l⟩)).rows)
    rw [(logNextE w.σ i l).1, hI.log]
    change _ = (if gmoEv l then w.gmo ++ [(i, (w.rows i).length)] else w.gmo).filterMap
      (wmsgOf (upd w.rows i (w.rows i ++ [l])))
    have hcong : w.gmo.filterMap (wmsgOf w.rows) =
        w.gmo.filterMap (wmsgOf (upd w.rows i (w.rows i ++ [l]))) := by
      refine filterMapCongr _ _ _ (fun e he => ?_)
      obtain ⟨l', hl', -⟩ := hI.gmoMem e he
      exact (wmsgEvOld w ⟨i, l⟩ e l' hl').symm
    rw [hcong, esMsgOf w i l]
    split <;> simp
  · intro j r l' hl'
    rcases rowsEvInv w ⟨i, l⟩ j r l' hl' with h | ⟨rfl, rfl, rfl⟩
    · exact hI.shape j r l' h
    · exact shapeOfStep w.σ j l' hst
  · intro j
    show (upd w.fw i (w.fw i ++ [fwOf (w.pend i) l]) j).length =
      (upd w.rows i (w.rows i ++ [l]) j).length
    by_cases hj : j = i
    · subst hj; rw [updEq, updEq]; simp [hI.fwLen]
    · rw [updNe _ _ _ _ hj, updNe _ _ _ _ hj]; exact hI.fwLen j

/-- **THE INVARIANT ALONG A LANDING.** -/
theorem invLand (img : Image) (pol : SbPol) (w : WS) (i k : Nat) :
    Inv img w → pol.landOk (w.σ.sb i) k → Inv img (nextI w (.land i k)) := by
  intro hI hok
  have hk : k < (w.pend i).length := by
    have := pol.inRange _ _ hok
    rw [hI.sb i, List.length_map] at this; exact this
  obtain ⟨p, hp⟩ : ∃ p, (w.pend i)[k]? = some p := ⟨_, List.getElem?_eq_getElem hk⟩
  obtain ⟨a, b, hab, hka⟩ := eraseIdxSplit _ _ _ hp
  have hera : (w.pend i).eraseIdx k = a ++ b := by rw [hab, ← hka, eraseIdxMid]
  have hsbk : (w.σ.sb i)[k]? = some p.2 := by rw [hI.sb i, List.getElem?_map, hp]; rfl
  have hsbe : (w.σ.sb i).eraseIdx k = (a ++ b).map Prod.snd := by
    rw [hI.sb i, hab, List.map_append, List.map_cons, ← hka, ← List.length_map (f := Prod.snd),
      eraseIdxMid, List.map_append]
  have hst : nextI w (.land i k) =
      ⟨SbCand.nextL w.σ i k, upd w.pend i (a ++ b), w.rows, w.fw, w.gmo ++ [(i, p.1)]⟩ := by
    simp only [nextI, hp, hera]
  have hnl : SbCand.nextL w.σ i k =
      ⟨⟨w.σ.ms.msImg, w.σ.ms.msLog ++ [p.2.msg],
        updWs w.σ.ms.msWs i (SbCand.landPost (w.σ.ms.msWs i) p.2 (w.σ.ms.msLog.length + 1))⟩,
       SbCand.updSb w.σ.sb i ((a ++ b).map Prod.snd)⟩ := by
    simp only [SbCand.nextL, hsbk, hsbe]
  have hpin : p ∈ w.pend i := by rw [hab]; simp
  have hnd := hI.pendNd i
  rw [hab, List.map_append, List.map_cons] at hnd
  have hpa : p.1 ∉ (a ++ b).map Prod.fst := by
    rw [List.map_append]
    intro h
    rcases List.mem_append.1 h with h | h
    · exact (List.nodup_append.1 hnd).2.2 _ h _ (List.mem_cons_self) rfl
    · exact (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1 h
  have hpend : ∀ j, upd w.pend i (a ++ b) j = if j = i then a ++ b else w.pend j := by
    intro j; by_cases hj : j = i
    · subst hj; simp [upd]
    · simp [upd, hj]
  have hsub : ∀ j q, q ∈ upd w.pend i (a ++ b) j → q ∈ w.pend j := by
    intro j q hq
    rw [hpend j] at hq
    by_cases hj : j = i
    · subst hj; rw [if_pos rfl] at hq; rw [hab]
      rcases List.mem_append.1 hq with h | h
      · exact List.mem_append.2 (.inl h)
      · exact List.mem_append.2 (.inr (List.mem_cons_of_mem _ h))
    · rwa [if_neg hj] at hq
  obtain ⟨rl, base, vs, kc, hrow, hmsg⟩ := hI.pendSt i p hpin
  rw [hst]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.shape, hI.fwLen⟩
  · dsimp only; rw [hnl]; exact hI.img
  · intro j
    dsimp only
    rw [hnl, hpend j]
    show SbCand.updSb w.σ.sb i _ j = _
    by_cases hj : j = i
    · subst hj; rw [SbCand.updSbEq, if_pos rfl]
    · rw [SbCand.updSbNe _ _ _ _ hj, if_neg hj, hI.sb j]
  · intro j q hq; dsimp only at hq ⊢; exact hI.pendSt j q (hsub j q hq)
  · intro j
    show ((upd w.pend i (a ++ b) j).map Prod.fst).Nodup
    rw [hpend j]
    by_cases hj : j = i
    · subst hj; rw [if_pos rfl, List.map_append]
      rw [List.map_append] at hpa
      exact List.nodup_append.2 ⟨(List.nodup_append.1 hnd).1,
        (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).2,
        fun x hx y hy => (List.nodup_append.1 hnd).2.2 x hx y (List.mem_cons_of_mem _ hy)⟩
    · rw [if_neg hj]; exact hI.pendNd j
  · intro j q hq hin
    dsimp only at hq hin
    rcases List.mem_append.1 hin with h | h
    · exact hI.pendGmo j q (hsub j q hq) h
    · simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      rw [hpend j, if_pos rfl] at hq
      exact hpa (h ▸ List.mem_map_of_mem hq)
  · exact List.nodup_append.2 ⟨hI.gmoNd, nodupOne _,
      fun x hx y hy => by
        simp only [List.mem_singleton] at hy; subst hy
        exact fun h => hI.pendGmo i p hpin (h ▸ hx)⟩
  · intro e he
    dsimp only at he ⊢
    rcases List.mem_append.1 he with h | h
    · exact hI.gmoMem e h
    · simp only [List.mem_singleton] at h; subst h
      exact ⟨_, hrow, rfl⟩
  · intro j r l hl hm
    dsimp only at hl ⊢
    rcases hI.memIn j r l hl hm with h | h
    · exact .inl (List.mem_append.2 (.inl h))
    · by_cases hj : j = i
      · subst hj
        rw [hab, List.map_append, List.map_cons] at h
        by_cases hr : r = p.1
        · subst hr; exact .inl (List.mem_append.2 (.inr (List.mem_singleton.2 rfl)))
        · right
          show r ∈ (upd w.pend j (a ++ b) j).map Prod.fst
          rw [updEq, List.map_append]
          rcases List.mem_append.1 h with h | h
          · exact List.mem_append.2 (.inl h)
          · rcases List.mem_cons.1 h with h | h
            · exact absurd h hr
            · exact List.mem_append.2 (.inr h)
      · right
        show r ∈ (upd w.pend i (a ++ b) j).map Prod.fst
        rw [updNe _ _ _ _ hj]; exact h
  · dsimp only
    rw [hnl]
    show w.σ.ms.msLog ++ [p.2.msg] = (w.gmo ++ [(i, p.1)]).filterMap (wmsgOf w.rows)
    rw [hI.log, List.filterMap_append]
    congr 1
    simp [wmsgOf, hrow, lbWr, lbCls, hmsg]

/-- **THE INVARIANT HOLDS AT EVERY STATE OF A VALID CANDIDATE.** -/
theorem invStAt (pol : SbPol) (c : CandW) :
    validW pol c → ∀ k, Inv c.img (stAt c k) := by
  intro hv k
  induction k with
  | zero => exact invInit c.img
  | succ k ih =>
    cases hk : c.its[k]? with
    | none =>
      show Inv c.img (match c.its[k]? with
        | some it => nextI (stAt c k) it
        | none => stAt c k)
      rw [hk]; exact ih
    | some it =>
      rw [stAtSucc c k it hk]
      have hok := hv k it hk
      cases it with
      | ev s => exact invEv c.img _ s ih hok
      | land i j => exact invLand c.img pol _ i j ih hok

/-! ## 1.3 Monotonicity: rows, the forwarding record and gmo only grow -/

theorem nextIMono (w : WS) (it : Item) :
    (∀ i, w.rows i <+: (nextI w it).rows i) ∧ (∀ i, w.fw i <+: (nextI w it).fw i) ∧
    w.gmo <+: (nextI w it).gmo := by
  cases it with
  | ev s =>
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · show w.rows i <+: upd w.rows s.esAg (w.rows s.esAg ++ [s.esLb]) i
      by_cases hi : i = s.esAg
      · subst hi; rw [updEq]; exact List.prefix_append _ _
      · rw [updNe _ _ _ _ hi]; exact List.prefix_refl _
    · show w.fw i <+: upd w.fw s.esAg (w.fw s.esAg ++ [fwOf (w.pend s.esAg) s.esLb]) i
      by_cases hi : i = s.esAg
      · subst hi; rw [updEq]; exact List.prefix_append _ _
      · rw [updNe _ _ _ _ hi]; exact List.prefix_refl _
    · show w.gmo <+: (if gmoEv s.esLb then w.gmo ++ [(s.esAg, (w.rows s.esAg).length)] else w.gmo)
      split
      · exact List.prefix_append _ _
      · exact List.prefix_refl _
  | land i k =>
    cases hp : (w.pend i)[k]? with
    | none =>
      simp only [nextI, hp]
      exact ⟨fun _ => List.prefix_refl _, fun _ => List.prefix_refl _, List.prefix_refl _⟩
    | some p =>
      simp only [nextI, hp]
      exact ⟨fun _ => List.prefix_refl _, fun _ => List.prefix_refl _, List.prefix_append _ _⟩

theorem stAtMono (c : CandW) (k : Nat) : ∀ n, k ≤ n →
    (∀ i, (stAt c k).rows i <+: (stAt c n).rows i) ∧ (∀ i, (stAt c k).fw i <+: (stAt c n).fw i) ∧
    (stAt c k).gmo <+: (stAt c n).gmo := by
  intro n hkn
  induction n with
  | zero =>
    have : k = 0 := by omega
    subst this
    exact ⟨fun _ => List.prefix_refl _, fun _ => List.prefix_refl _, List.prefix_refl _⟩
  | succ n ih =>
    by_cases he : k = n + 1
    · subst he; exact ⟨fun _ => List.prefix_refl _, fun _ => List.prefix_refl _, List.prefix_refl _⟩
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    cases hn : c.its[n]? with
    | none =>
      have e : stAt c (n + 1) = stAt c n := by
        show (match c.its[n]? with
          | some it => nextI (stAt c n) it
          | none => stAt c n) = _
        rw [hn]
      rw [e]; exact ⟨h1, h2, h3⟩
    | some it =>
      rw [stAtSucc c n it hn]
      obtain ⟨g1, g2, g3⟩ := nextIMono (stAt c n) it
      exact ⟨fun i => (h1 i).trans (g1 i), fun i => (h2 i).trans (g2 i), h3.trans g3⟩

/-! ## 1.4 Appending an item -/

def snocC (c : CandW) (it : Item) : CandW := ⟨c.img, c.its ++ [it]⟩

theorem stAtSnoc (c : CandW) (it : Item) : ∀ k, k ≤ c.its.length → stAt (snocC c it) k = stAt c k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    obtain ⟨it0, h0⟩ : ∃ it0, c.its[k]? = some it0 := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have h0' : (snocC c it).its[k]? = some it0 := by
      show (c.its ++ [it])[k]? = some it0
      rw [List.getElem?_append_left (by omega)]; exact h0
    rw [stAtSucc _ k it0 h0', stAtSucc _ k it0 h0, ih (by omega)]

theorem stAtSnocEnd (c : CandW) (it : Item) :
    stAt (snocC c it) (c.its.length + 1) = nextI (stAt c c.its.length) it := by
  have h : (snocC c it).its[c.its.length]? = some it := by
    show (c.its ++ [it])[c.its.length]? = some it
    simp
  rw [stAtSucc _ _ it h, stAtSnoc c it _ (Nat.le_refl _)]

theorem validSnoc (pol : SbPol) (c : CandW) (it : Item) :
    validW pol c → okI pol (stAt c c.its.length) it → validW pol (snocC c it) := by
  intro hv hok k it0 hk
  change (c.its ++ [it])[k]? = some it0 at hk
  rcases getAppInv _ _ _ _ hk with h | ⟨h1, h2⟩
  · rw [stAtSnoc c it k (Nat.le_of_lt (lookup_lt_Some h))]; exact hv k it0 h
  · subst h1; rw [h2, stAtSnoc c it _ (Nat.le_refl _)]; exact hok

/-! # 2. The walk state and its program data -/

/-- The current machine state of the walk. -/
def cur (c : CandW) : WS := stAt c c.its.length

/-- **WHAT AN EVENT ITEM OWES** of the program, at the walk state before it: from the agent's program
state `p` (at fabric `d`), the admin star (its fetches at view 0 of the LANDED log: fetches never
forward), then the label realized by one pf label or the exclusive pair, at the `SbCand` state's views,
ending at `p'` and fabric `d'`. -/
def evData (w : WS) (x : Nat) (lb : Lbl) (p : Pexv6) (d : Efab) (p' : Pexv6) (d' : Efab) : Prop :=
  ∃ (pa : Pexv6) (da : Efab) (ls : List Wlabel),
    admRunG pstepEv true p d ls pa da ∧
    (∀ (base : Int) (tvs : List (Nat × BitVec 8)), Wlabel.LIFetch base tvs ∈ ls →
      ifetchOk w.σ.ms.msImg w.σ.ms.msLog 0 base tvs) ∧
    ((∃ l, lblRealizes pclsEv pa w.σ.ms x lb l ∧ pstepEv pa da l p' d') ∨
     (∃ (pm : Pexv6) (dm : Efab) (ls2 : List Wlabel) (pm2 : Pexv6) (dm2 : Efab) (l1 l2 : Wlabel),
        lblRealizesPair pclsEv pa pm2 w.σ.ms x lb l1 l2 ∧ pstepEv pa da l1 pm dm ∧
        admRunG pstepEv false pm dm ls2 pm2 dm2 ∧ pstepEv pm2 dm2 l2 p' d'))

/-- **THE PROGRAM DATA** of a walk candidate: per event item, the agent's program moves by `evData`
(the others keep theirs); a landing moves no program and no fabric. -/
def progOk (pst : Nat → List Pexv6) (dv : Nat → Efab) (c : CandW) : Prop :=
  ∀ (k : Nat) (it : Item), c.its[k]? = some it →
    match it with
    | .ev s => ∃ p p', (pst k)[s.esAg]? = some p ∧ pst (k + 1) = (pst k).set s.esAg p' ∧
        evData (stAt c k) s.esAg s.esLb p (dv k) p' (dv (k + 1))
    | .land _ _ => pst (k + 1) = pst k ∧ dv (k + 1) = dv k

/-- **THE WALK STATE.** -/
structure St where
  c : CandW
  pst : Nat → List Pexv6
  dv : Nat → Efab

/-- **THE WALK INVARIANT**: a valid candidate under `pol`, its program data, the fabric start. -/
def ok (pol : SbPol) (d0 : Efab) (S : St) : Prop :=
  validW pol S.c ∧ progOk S.pst S.dv S.c ∧ S.dv 0 = d0

/-- Appending an event of agent `x` (new program state `pC'`, fabric `d'`). -/
def snocE (S : St) (s : Estep) (pC' : Pexv6) (d' : Efab) : St :=
  ⟨snocC S.c (.ev s),
   fun k => if k ≤ S.c.its.length then S.pst k else (S.pst S.c.its.length).set s.esAg pC',
   fun k => if k ≤ S.c.its.length then S.dv k else d'⟩

/-- Appending a landing (programs and fabric unchanged). -/
def snocL (S : St) (i k : Nat) : St :=
  ⟨snocC S.c (.land i k),
   fun j => if j ≤ S.c.its.length then S.pst j else S.pst S.c.its.length,
   fun j => if j ≤ S.c.its.length then S.dv j else S.dv S.c.its.length⟩

theorem progSnoc (pst pst' : Nat → List Pexv6) (dv dv' : Nat → Efab) (c : CandW) (it : Item) :
    progOk pst dv c → (∀ k, k ≤ c.its.length → pst' k = pst k ∧ dv' k = dv k) →
    (match it with
     | .ev s => ∃ p p', (pst' c.its.length)[s.esAg]? = some p ∧
        pst' (c.its.length + 1) = (pst' c.its.length).set s.esAg p' ∧
        evData (stAt c c.its.length) s.esAg s.esLb p (dv' c.its.length) p' (dv' (c.its.length + 1))
     | .land _ _ => pst' (c.its.length + 1) = pst' c.its.length ∧
        dv' (c.its.length + 1) = dv' c.its.length) →
    progOk pst' dv' (snocC c it) := by
  intro hp heq hnew k it0 hk
  change (c.its ++ [it])[k]? = some it0 at hk
  rcases getAppInv _ _ _ _ hk with h | ⟨h1, h2⟩
  · have hkl := lookup_lt_Some h
    have e0 := heq k (by omega)
    have e1 := heq (k + 1) (by omega)
    have hpk := hp k it0 h
    rw [stAtSnoc c it k (by omega)]
    cases it0 with
    | ev s =>
      obtain ⟨p, p', h1, h2, h3⟩ := hpk
      exact ⟨p, p', by rw [e0.1]; exact h1, by rw [e1.1, e0.1]; exact h2,
        by rw [e0.2, e1.2]; exact h3⟩
    | land i j =>
      obtain ⟨h1, h2⟩ := hpk
      exact ⟨by rw [e1.1, e0.1]; exact h1, by rw [e1.2, e0.2]; exact h2⟩
  · subst h1
    rw [h2, stAtSnoc c it _ (Nat.le_refl _)]
    exact hnew

/-- **THE ONE-STEP EXTENSION BY AN EVENT.** -/
theorem okSnocE (pol : SbPol) (d0 : Efab) (S : St) (s : Estep) (pC pC' : Pexv6) (d' : Efab) :
    ok pol d0 S → (S.pst S.c.its.length)[s.esAg]? = some pC →
    okI pol (cur S.c) (Item.ev s) →
    evData (cur S.c) s.esAg s.esLb pC (S.dv S.c.its.length) pC' d' →
    ok pol d0 (snocE S s pC' d') := by
  rintro ⟨hv, hp, hd0⟩ hpc hok hev
  have hn : ¬ S.c.its.length + 1 ≤ S.c.its.length := by omega
  refine ⟨validSnoc pol S.c (Item.ev s) hv hok, progSnoc _ _ _ _ _ (Item.ev s) hp
    (fun k hk => ⟨if_pos hk, if_pos hk⟩) ⟨pC, pC', ?_, ?_, ?_⟩, ?_⟩
  · dsimp only [snocE]; rw [if_pos (Nat.le_refl _)]; exact hpc
  · dsimp only [snocE]; rw [if_neg hn, if_pos (Nat.le_refl _)]
  · dsimp only [snocE]; rw [if_pos (Nat.le_refl _), if_neg hn]; exact hev
  · dsimp only [snocE]; rw [if_pos (Nat.zero_le _)]; exact hd0

/-- **THE ONE-STEP EXTENSION BY A LANDING.** -/
theorem okSnocL (pol : SbPol) (d0 : Efab) (S : St) (i k : Nat) :
    ok pol d0 S → okI pol (cur S.c) (Item.land i k) → ok pol d0 (snocL S i k) := by
  rintro ⟨hv, hp, hd0⟩ hok
  have hn : ¬ S.c.its.length + 1 ≤ S.c.its.length := by omega
  refine ⟨validSnoc pol S.c (Item.land i k) hv hok, progSnoc _ _ _ _ _ (Item.land i k) hp
    (fun k hk => ⟨if_pos hk, if_pos hk⟩) ⟨?_, ?_⟩, ?_⟩
  · dsimp only [snocL]; rw [if_neg hn, if_pos (Nat.le_refl _)]
  · dsimp only [snocL]; rw [if_neg hn, if_pos (Nat.le_refl _)]
  · dsimp only [snocL]; rw [if_pos (Nat.zero_le _)]; exact hd0

/-- The start: the empty walk over the image, every agent at its boot state. -/
def start (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (img : Image) : St :=
  ⟨⟨img, []⟩, fun _ => (List.range' 0 N).map boot, fun _ => d0⟩

theorem okStart (pol : SbPol) (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (img : Image) :
    ok pol d0 (start boot d0 N img) :=
  ⟨fun k it h => by simp [start] at h, fun k it h => by simp [start] at h, rfl⟩

/-- The program data keep the number of agents. -/
theorem pstLen (pst : Nat → List Pexv6) (dv : Nat → Efab) (c : CandW) (N : Nat) :
    progOk pst dv c → (pst 0).length = N → ∀ k, k ≤ c.its.length → (pst k).length = N := by
  intro hp h0 k
  induction k with
  | zero => intro _; exact h0
  | succ k ih =>
    intro hk
    obtain ⟨it, hit⟩ : ∃ it, c.its[k]? = some it := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have h := hp k it hit
    cases it with
    | ev s =>
      obtain ⟨_, _, _, h2, _⟩ := h
      rw [h2, List.length_set]; exact ih (by omega)
    | land =>
      rw [h.1]; exact ih (by omega)

/-- **EVERY EVENT'S AGENT IS BELOW `N`** (from the program data). -/
theorem agBound (pst : Nat → List Pexv6) (dv : Nat → Efab) (c : CandW) (N : Nat) :
    progOk pst dv c → (pst 0).length = N →
      ∀ (k : Nat) (s : Estep), c.its[k]? = some (Item.ev s) → s.esAg < N := by
  intro hp h0 k s hk
  obtain ⟨p, _, h1, _⟩ := hp k _ hk
  have := lookup_lt_Some h1
  rwa [pstLen pst dv c N hp h0 k (Nat.le_of_lt (lookup_lt_Some hk))] at this

end SbWalk

end Weak
