/-
Weak: **allocproc route P, increment P-W2 (2/3) — `SbAgree`, the buffered walk's MEMBER and its
AGREEMENT with GF** (`notes/weak-allocproc-routeP-design.md` §3.2 "value agreement by construction";
plan rev 55 row P-W2; [OWN.112] [OWN.113]).  Lean-only, no Rocq twin.

  §1  **THE MEMBER** `SbAgree.memberW N img w` of a walk machine state (`SbWalk.WS`): row `i` is agent
      `i`'s labels in program order; gmo is the walk's (`SbWalk.WS.gmo`): loads, AMOs, I/O at their
      EVENT, plain stores at their LANDING — so the member's WRITE order is the landed log's order
      (`memberLogOf`).  **The forwarded-byte timestamps** (left open by P-W1): `SbCand.stepE` ignores the
      label's timestamp at a forwarded byte (`SbCand.fwdMask`), so the walk TRACE may carry anything
      there (the pf label P-W6 relates it to chooses); the MEMBER label carries the forwarding store's
      member WRITE INDEX (`fixTs`: its landing position) — the member's rf at that byte is the own
      store, which is GF's source under the aligned event identities.  The fix-up touches only load
      timestamps, so every write / class / gmo fact of the member is the raw rows' (`fix*`).
  §2  the member's facts at a drained state (no pending store): **`memberGwf`**, **`memberLogOf`**
      (the landed log is the message list of the member's writes), **`memberRmwLatest`** (every AMO read
      the latest bytes of the log before its own message) — from `SbWalk.Inv` and the AMO-read
      invariant `RmwInv` (`rmwInvStAt`).  NOTE: the member does NOT satisfy `gwrowGmo` (a plain store
      lands after po-later events — the F44-1 freedom, and the epoch buffer reorders same-epoch stores to
      different bytes); route P's kill glue (P-W4) must use RVWMO's ppo instead (finding F-P-W2-2);
  §3  **THE AGREEMENT** `SbAgree.agreeX G GR X` (`X`: the exempt reads, the two `ip->ref` pcs): every
      label `lblReidx` of GF's (exact but for read timestamps) except at `X`, where both are plain loads
      of the same footprint (`lblReidxSub`); FULL co agreement on every byte.  Consequences:
      **`agreeW4OfX`** — CertZ24's `agreeW4` with `nf = True` (`L := fun _ => False`): a failed acquire
      is REPLAYED (it writes), so `agreeW4` at a real lock set `L` is FALSE for the P member (its third
      clause says no member write is a failed acquire) — its consumers move to **`agreeW3OfX`**
      (`CertZ18.agreeW3` at EVERY `L`, lock co included) or `agreeX` itself; **`lockCoOfX`**.
  §4  the walk-level PREFIX invariant `SbAgree.pfx` (each member row a GF row prefix related label by
      label, each byte's landed write list a PREFIX of GF's write list at that byte), its preservation
      by an event (`pfxEv`) and a landing (`pfxLand`) under the co-prefix condition the gate supplies,
      and **`agreeXOfPfx`**: at a COMPLETED, drained walk the prefix invariant IS `agreeX`.

Spec: FAITHFUL (proof organisation; nothing assumed of GF beyond its being a graph).  Lean-only helpers
`SbAgree.*`.
-/
import Weak.SbWalk
import Weak.CertZ24

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

namespace SbAgree

open SbWalk

/-! # 1. The member graph -/

/-- The RAW member (labels as stepped). -/
def rawG (N : Nat) (img : Image) (w : WS) : Gexec := ⟨img, (List.range' 0 N).map w.rows, w.gmo⟩

/-- The member timestamps of a load: a forwarded byte names its store's member write index. -/
def fixTs (G0 : Gexec) (i : Nat) (ts : List Nat) (f : List (Option Nat)) : List Nat :=
  ts.mapIdx (fun j t =>
    match f.getD j none with
    | some r => gwix G0 (i, r)
    | none => t)

def fixLbl (G0 : Gexec) (i : Nat) (l : Lbl) (f : List (Option Nat)) : Lbl :=
  match l with
  | LLoad aq base ts vs => LLoad aq base (fixTs G0 i ts f) vs
  | l => l

/-- Agent `i`'s member row. -/
def rowFix (N : Nat) (img : Image) (w : WS) (i : Nat) : List Lbl :=
  (w.rows i).mapIdx (fun n l => fixLbl (rawG N img w) i l ((w.fw i).getD n []))

/-- **THE MEMBER** of a walk machine state over `N` agents. -/
def memberW (N : Nat) (img : Image) (w : WS) : Gexec :=
  ⟨img, (List.range' 0 N).map (rowFix N img w), w.gmo⟩

/-- The member of a walk candidate and its (landed) log. -/
def memberP (N : Nat) (c : CandW) : Gexec := memberW N c.img (cur c)

def logP (c : CandW) : List Wmsg := (cur c).σ.ms.msLog

/-! ## 1.1 The fix-up changes nothing but load timestamps -/

theorem fixLblCases (G0 : Gexec) (i : Nat) (l : Lbl) (f : List (Option Nat)) :
    fixLbl G0 i l f = l ∨ ∃ aq base ts vs, l = LLoad aq base ts vs ∧
      fixLbl G0 i l f = LLoad aq base (fixTs G0 i ts f) vs := by
  cases l with
  | LLoad aq base ts vs => exact .inr ⟨aq, base, ts, vs, rfl, rfl⟩
  | _ => exact .inl rfl

theorem fixTsLen (G0 : Gexec) (i : Nat) (ts : List Nat) (f : List (Option Nat)) :
    (fixTs G0 i ts f).length = ts.length := by simp [fixTs]

theorem fixW (G0 : Gexec) (i : Nat) (l : Lbl) (f : List (Option Nat)) :
    lbIsW (fixLbl G0 i l f) = lbIsW l := by cases l <;> rfl

theorem fixMem (G0 : Gexec) (i : Nat) (l : Lbl) (f : List (Option Nat)) :
    lbIsMem (fixLbl G0 i l f) = lbIsMem l := by cases l <;> rfl

theorem fixWr (G0 : Gexec) (i : Nat) (l : Lbl) (f : List (Option Nat)) :
    lbWr (fixLbl G0 i l f) = lbWr l := by cases l <;> rfl

theorem fixCls (G0 : Gexec) (i : Nat) (l : Lbl) (f : List (Option Nat)) :
    lbCls (fixLbl G0 i l f) = lbCls l := by cases l <;> rfl

theorem fixShape (G0 : Gexec) (i : Nat) (l : Lbl) (f : List (Option Nat)) :
    shapeOk l → shapeOk (fixLbl G0 i l f) := by
  cases l with
  | LLoad aq base ts vs => intro h; show vs.length = (fixTs G0 i ts f).length; rw [fixTsLen]; exact h
  | _ => exact id

/-- The fix-up is a re-timing: `lblReidx` both ways. -/
theorem fixReidx (G0 : Gexec) (i : Nat) (l : Lbl) (f : List (Option Nat)) :
    lblReidx l (fixLbl G0 i l f) := by
  cases l with
  | LLoad aq base ts vs => exact ⟨rfl, rfl, rfl, fixTsLen _ _ _ _⟩
  | _ => exact lblReidxRefl _

theorem fixRmw (G0 : Gexec) (i : Nat) (l : Lbl) (f : List (Option Nat)) :
    lbIsW l = true → fixLbl G0 i l f = l := by
  cases l <;> simp [lbIsW, fixLbl]

/-! ## 1.2 Lookups -/

theorem rawLbl (N : Nat) (img : Image) (w : WS) (e : Geid) :
    gxLbl (rawG N img w) e = if e.1 < N then (w.rows e.1)[e.2]? else none := by
  unfold gxLbl rawG
  dsimp only
  rw [CertZ3.rowLookup]
  split <;> rfl

theorem memLbl (N : Nat) (img : Image) (w : WS) (e : Geid) :
    gxLbl (memberW N img w) e = if e.1 < N then
      ((w.rows e.1)[e.2]?).map (fun l => fixLbl (rawG N img w) e.1 l ((w.fw e.1).getD e.2 []))
    else none := by
  unfold gxLbl memberW
  dsimp only
  rw [CertZ3.rowLookup]
  split
  · simp only [Option.bind_some, rowFix, List.getElem?_mapIdx]
  · rfl

theorem memLblSome (N : Nat) (img : Image) (w : WS) (e : Geid) (l : Lbl) :
    e.1 < N → (w.rows e.1)[e.2]? = some l →
    gxLbl (memberW N img w) e = some (fixLbl (rawG N img w) e.1 l ((w.fw e.1).getD e.2 [])) := by
  intro h1 h2
  rw [memLbl, if_pos h1, h2]; rfl

theorem memLblInv (N : Nat) (img : Image) (w : WS) (e : Geid) (l' : Lbl) :
    gxLbl (memberW N img w) e = some l' →
    e.1 < N ∧ ∃ l, (w.rows e.1)[e.2]? = some l ∧
      l' = fixLbl (rawG N img w) e.1 l ((w.fw e.1).getD e.2 []) := by
  intro h
  rw [memLbl] at h
  split at h
  · rename_i h1
    cases h2 : (w.rows e.1)[e.2]? with
    | none => rw [h2] at h; cases h
    | some l =>
      rw [h2] at h
      simp only [Option.map_some, Option.some.injEq] at h
      exact ⟨h1, l, rfl, h.symm⟩
  · cases h

theorem gisWEq (N : Nat) (img : Image) (w : WS) :
    gisW (memberW N img w) = gisW (rawG N img w) := by
  funext e
  unfold gisW
  rw [memLbl, rawLbl]
  by_cases h : e.1 < N
  · simp only [if_pos h]
    cases (w.rows e.1)[e.2]? with
    | none => rfl
    | some l => simp only [Option.map_some, fixW]
  · simp only [if_neg h]

theorem gwritesEq (N : Nat) (img : Image) (w : WS) :
    gwrites (memberW N img w) = gwrites (rawG N img w) := by
  unfold gwrites
  rw [gisWEq]; rfl

theorem gwixEq (N : Nat) (img : Image) (w : WS) :
    gwix (memberW N img w) = gwix (rawG N img w) := by
  funext e
  unfold gwix
  rw [gwritesEq]

/-! # 2. The member's facts -/

theorem filterMapIdx {α β : Type} (f : α → Option β) (P : α → Bool) :
    ∀ (l : List α), (∀ a, a ∈ l → (f a).isSome = P a) →
      ∀ (p : Nat) (m : β), (l.filterMap f)[p]? = some m ↔ ∃ a, (l.filter P)[p]? = some a ∧ f a = some m
  | [], _, p, m => by simp
  | a :: l, h, p, m => by
    have ih := filterMapIdx f P l (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a List.mem_cons_self
    cases hf : f a with
    | none =>
      rw [hf] at ha
      have hP : P a = false := by simpa using ha.symm
      simp only [List.filterMap_cons, hf, List.filter_cons, hP, Bool.false_eq_true, if_false]
      exact ih p m
    | some b =>
      rw [hf] at ha
      have hP : P a = true := by simpa using ha.symm
      simp only [List.filterMap_cons, hf, List.filter_cons, hP, if_true]
      cases p with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq]
        exact ⟨fun h => ⟨a, rfl, by rw [hf, h]⟩, fun ⟨a', ha', hm⟩ => by subst ha'; rw [hf] at hm; exact Option.some.inj hm⟩
      | succ p => simp only [List.getElem?_cons_succ]; exact ih p m

theorem filterMapLen {α β : Type} (f : α → Option β) (P : α → Bool) :
    ∀ (l : List α), (∀ a, a ∈ l → (f a).isSome = P a) → (l.filterMap f).length = (l.filter P).length
  | [], _ => rfl
  | a :: l, h => by
    have ih := filterMapLen f P l (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a List.mem_cons_self
    cases hf : f a with
    | none =>
      rw [hf] at ha
      have hP : P a = false := by simpa using ha.symm
      simp only [List.filterMap_cons, hf, List.filter_cons, hP, Bool.false_eq_true, if_false]
      exact ih
    | some b =>
      rw [hf] at ha
      have hP : P a = true := by simpa using ha.symm
      simp only [List.filterMap_cons, hf, List.filter_cons, hP, if_true, List.length_cons]
      rw [ih]

/-- The agent bound of a walk state: an agent with a nonempty row is below `N`. -/
def agOk (N : Nat) (w : WS) : Prop := ∀ i, w.rows i ≠ [] → i < N

/-- No store is pending. -/
def drained (w : WS) : Prop := ∀ i, w.pend i = []

theorem agOfRow (N : Nat) (w : WS) (e : Geid) (l : Lbl) :
    agOk N w → (w.rows e.1)[e.2]? = some l → e.1 < N := by
  intro h hl
  refine h e.1 (fun he => ?_)
  rw [he] at hl; simp at hl

/-- A member write's message is the row's. -/
theorem gmsgEq (N : Nat) (img : Image) (w : WS) (e : Geid) :
    agOk N w → (∃ l, (w.rows e.1)[e.2]? = some l) →
    WeakRvwmoKillArms.gmsg (memberW N img w) e = wmsgOf w.rows e := by
  rintro hag ⟨l, hl⟩
  unfold WeakRvwmoKillArms.gmsg wmsgOf
  rw [memLblSome N img w e l (agOfRow N w e l hag hl) hl, hl]
  simp only [fixWr, fixCls]
  generalize lbWr l = o
  cases o with
  | none => rfl
  | some q => obtain ⟨b, v⟩ := q; rfl

theorem wmsgSome (N : Nat) (img : Image) (w : WS) (e : Geid) :
    agOk N w → (∃ l, (w.rows e.1)[e.2]? = some l) →
    (wmsgOf w.rows e).isSome = gisW (memberW N img w) e := by
  rintro hag ⟨l, hl⟩
  unfold wmsgOf gisW
  rw [memLblSome N img w e l (agOfRow N w e l hag hl) hl, hl]
  dsimp only
  rw [fixW]
  cases l <;> simp [lbWr, lbIsW]

/-- **THE MEMBER'S WRITES ARE THE LANDED LOG.** -/
theorem memberLogOf (N : Nat) (img : Image) (w : WS) :
    Inv img w → agOk N w → logOf (memberW N img w) w.σ.ms.msLog := by
  intro hI hag p m
  have hrow : ∀ e, e ∈ w.gmo → ∃ l, (w.rows e.1)[e.2]? = some l := by
    intro e he; obtain ⟨l, hl, -⟩ := hI.gmoMem e he; exact ⟨l, hl⟩
  rw [hI.log, filterMapIdx (wmsgOf w.rows) (gisW (memberW N img w)) w.gmo
    (fun e he => wmsgSome N img w e hag (hrow e he))]
  constructor
  · rintro ⟨a, ha, hm⟩
    refine ⟨a, ha, ?_⟩
    rw [gmsgEq N img w a hag (hrow a ((List.mem_filter.1 (List.mem_of_getElem? ha)).1))]
    exact hm
  · rintro ⟨a, ha, hm⟩
    have ha' : (gwrites (memberW N img w))[p]? = some a := ha
    refine ⟨a, ha', ?_⟩
    have hmem : a ∈ w.gmo := (List.mem_filter.1 (List.mem_of_getElem? ha')).1
    rw [← gmsgEq N img w a hag (hrow a hmem)]
    exact hm

/-- **THE MEMBER IS WELL-FORMED** at a drained state. -/
theorem memberGwf (N : Nat) (img : Image) (w : WS) :
    Inv img w → agOk N w → drained w → gwf (memberW N img w) := by
  intro hI hag hdr
  refine ⟨hI.gmoNd, fun e => ⟨fun he => ?_, fun ⟨l', hl', hm⟩ => ?_⟩, ?_⟩
  · obtain ⟨l, hl, hm⟩ := hI.gmoMem e he
    exact ⟨_, memLblSome N img w e l (agOfRow N w e l hag hl) hl, by rw [fixMem]; exact hm⟩
  · obtain ⟨-, l, hl, rfl⟩ := memLblInv N img w e l' hl'
    rw [fixMem] at hm
    rcases hI.memIn e.1 e.2 l hl hm with h | h
    · exact h
    · rw [hdr e.1] at h; simp at h
  · intro i p k l hp hk
    have hp' : ((List.range' 0 N).map (rowFix N img w))[i]? = some p := hp
    rw [CertZ3.rowLookup] at hp'
    split at hp'
    · cases hp'
      simp only [rowFix, List.getElem?_mapIdx] at hk
      cases hr : (w.rows i)[k]? with
      | none => rw [hr] at hk; cases hk
      | some l0 =>
        rw [hr] at hk
        simp only [Option.map_some, Option.some.injEq] at hk
        subst hk
        exact fixShape _ _ _ _ (hI.shape i k l0 hr)
    · cases hp'

/-! ## 2.1 The AMO reads -/

/-- The landed log before gmo position `j`. -/
def logBefore (w : WS) (j : Nat) : List Wmsg := (w.gmo.take j).filterMap (wmsgOf w.rows)

/-- **THE AMO-READ INVARIANT**: an AMO at gmo position `j` read the latest bytes of the log before it. -/
def RmwInv (img : Image) (w : WS) : Prop :=
  ∀ (j : Nat) (e : Geid) (aq rl : Bool) (base : Int) (ts : List Nat) (rvs wvs : List (BitVec 8))
    (kc : WmClass), w.gmo[j]? = some e → (w.rows e.1)[e.2]? = some (LRmw aq rl base ts rvs wvs kc) →
    rmwLatest img (logBefore w j) base ts ∧
    ∀ (jj t : Nat) (v : BitVec 8), ts[jj]? = some t → rvs[jj]? = some v →
      logByte img (logBefore w j) t (accAddr base jj) = some v

theorem takeAppLe {α : Type} (l m : List α) (j : Nat) : j ≤ l.length → (l ++ m).take j = l.take j := by
  intro h; simp [List.take_append_of_le_length h]

theorem logBeforeEnd (w : WS) : logBefore w w.gmo.length = w.gmo.filterMap (wmsgOf w.rows) := by
  simp [logBefore]

theorem rmwInvEv (img : Image) (w : WS) (s : Estep) :
    Inv img w → RmwInv img w → SbCand.stepE w.σ s.esAg s.esLb (SbCand.nextE w.σ s.esAg s.esLb) →
    RmwInv img (nextI w (.ev s)) := by
  intro hI hR hst j e aq rl base ts rvs wvs kc hj hl
  have hcong : ∀ e, e ∈ w.gmo → wmsgOf (nextI w (.ev s)).rows e = wmsgOf w.rows e := by
    intro e he
    obtain ⟨l', hl', -⟩ := hI.gmoMem e he
    exact wmsgEvOld w s e l' hl'
  have hlb : ∀ j, j ≤ w.gmo.length → logBefore (nextI w (.ev s)) j = logBefore w j := by
    intro j hj
    unfold logBefore
    have hg : (nextI w (.ev s)).gmo.take j = w.gmo.take j := by
      change (if gmoEv s.esLb then w.gmo ++ [(s.esAg, (w.rows s.esAg).length)] else w.gmo).take j = _
      split
      · exact takeAppLe _ _ _ hj
      · rfl
    rw [hg]
    exact filterMapCongr _ _ _ (fun e he => hcong e (List.mem_of_mem_take he))
  change (if gmoEv s.esLb then w.gmo ++ [(s.esAg, (w.rows s.esAg).length)] else w.gmo)[j]? = some e at hj
  have hold : w.gmo[j]? = some e ∨ (j = w.gmo.length ∧ e = (s.esAg, (w.rows s.esAg).length)) := by
    split at hj
    · exact getAppInv _ _ _ _ hj
    · exact .inl hj
  rcases hold with hj | ⟨rfl, rfl⟩
  · have hjl := lookup_lt_Some hj
    obtain ⟨l0, hl0, -⟩ := hI.gmoMem e (List.mem_of_getElem? hj)
    have hl0' := rowsEvOld w s e.1 e.2 l0 hl0
    rw [hl0'] at hl
    rw [hl] at hl0
    rw [hlb j (Nat.le_of_lt hjl)]
    exact hR j e aq rl base ts rvs wvs kc hj hl0
  · rcases rowsEvInv w s _ _ _ hl with h | ⟨-, -, hls⟩
    · simp at h
    · rw [hlb _ (Nat.le_refl _), logBeforeEnd, ← hI.log, ← hI.img]
      rw [← hls] at hst
      cases hst with
      | rmw _ _ _ _ _ _ _ _ _ hrd hlat _ _ _ =>
        exact ⟨hlat, fun jj t v ht hv => (hrd.2 jj t v ht hv).1⟩

theorem rmwInvLand (img : Image) (pol : SbPol) (w : WS) (i k : Nat) :
    Inv img w → RmwInv img w → pol.landOk (w.σ.sb i) k → RmwInv img (nextI w (.land i k)) := by
  intro hI hR hok j e aq rl base ts rvs wvs kc hj hl
  cases hp : (w.pend i)[k]? with
  | none => simp only [nextI, hp] at hj hl ⊢; exact hR j e aq rl base ts rvs wvs kc hj hl
  | some p =>
    simp only [nextI, hp] at hj hl ⊢
    have hlb : logBefore ⟨SbCand.nextL w.σ i k, upd w.pend i ((w.pend i).eraseIdx k), w.rows, w.fw,
        w.gmo ++ [(i, p.1)]⟩ j = logBefore w j ∨ j = w.gmo.length := by
      by_cases hjl : j ≤ w.gmo.length
      · by_cases he : j = w.gmo.length
        · exact .inr he
        · left; unfold logBefore; dsimp only; rw [takeAppLe _ _ _ hjl]
      · left
        have := lookup_lt_Some hj
        simp at this; omega
    rcases getAppInv _ _ _ _ hj with hj | ⟨-, rfl⟩
    · rcases hlb with h | h
      · rw [h]; exact hR j e aq rl base ts rvs wvs kc hj hl
      · exact absurd (lookup_lt_Some hj) (by omega)
    · have hpin : p ∈ w.pend i := List.mem_of_getElem? hp
      obtain ⟨rl', base', vs', kc', hrow, -⟩ := hI.pendSt i p hpin
      rw [hrow] at hl; cases hl

theorem rmwInvStAt (pol : SbPol) (c : CandW) : validW pol c → ∀ k, RmwInv c.img (stAt c k) := by
  intro hv k
  induction k with
  | zero => intro j e _ _ _ _ _ _ _ hj; simp [stAt, init] at hj
  | succ k ih =>
    cases hk : c.its[k]? with
    | none =>
      show RmwInv c.img (match c.its[k]? with
        | some it => nextI (stAt c k) it
        | none => stAt c k)
      rw [hk]; exact ih
    | some it =>
      rw [stAtSucc c k it hk]
      have hok := hv k it hk
      have hI := invStAt pol c hv k
      cases it with
      | ev s => exact rmwInvEv c.img _ s hI ih hok
      | land i j => exact rmwInvLand c.img pol _ i j hI ih hok

/-- The write index of a member write at gmo position `j`. -/
theorem gwixAt (N : Nat) (img : Image) (w : WS) (j : Nat) (e : Geid) :
    w.gmo.Nodup → w.gmo[j]? = some e → gisW (memberW N img w) e = true →
    gwix (memberW N img w) e = ((w.gmo.take j).filter (gisW (memberW N img w))).length + 1 := by
  intro hnd hj hW
  apply gwixOfLookup _ _ _ hnd
  show (w.gmo.filter (gisW (memberW N img w)))[_]? = some e
  obtain ⟨a, b, hab, hka⟩ := eraseIdxSplit _ _ _ hj
  rw [hab, ← hka, List.take_left, List.filter_append, List.filter_cons, if_pos hW]
  simp

/-- **EVERY MEMBER AMO READ THE LATEST BYTES** (`CertZ18.rmwLatest` at the landed log). -/
theorem memberRmwLatest (N : Nat) (img : Image) (w : WS) :
    Inv img w → RmwInv img w → agOk N w → drained w →
    CertZ18.rmwLatest (memberW N img w) w.σ.ms.msLog := by
  intro hI hR hag hdr e a t v ⟨l1, hl1, hW⟩ ⟨l0, base, ts, vs, jj, hl0, hrd, ht, hv, ha⟩
  rw [hl1, Option.some.injEq] at hl0
  subst hl0
  obtain ⟨-, l, hl, rfl⟩ := memLblInv N img w e _ hl1
  rw [fixW] at hW
  rw [fixRmw _ _ _ _ hW] at hrd
  have hmem : lbIsMem l = true := by simp [lbIsMem, hW]
  have hin : e ∈ w.gmo := by
    rcases hI.memIn e.1 e.2 l hl hmem with h | h
    · exact h
    · rw [hdr e.1] at h; simp at h
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hin
  have hWg : gisW (memberW N img w) e = true := by
    simp only [gisW, hl1, fixW, hW]
  have hrow : ∀ e', e' ∈ w.gmo → ∃ l, (w.rows e'.1)[e'.2]? = some l := by
    intro e' he; obtain ⟨l, hl, -⟩ := hI.gmoMem e' he; exact ⟨l, hl⟩
  have htake : w.σ.ms.msLog.take (gwix (memberW N img w) e - 1) = logBefore w j := by
    rw [gwixAt N img w j e hI.gmoNd hj hWg, Nat.add_sub_cancel, hI.log, logBefore]
    have hsplit : w.gmo.filterMap (wmsgOf w.rows) =
        (w.gmo.take j).filterMap (wmsgOf w.rows) ++ (w.gmo.drop j).filterMap (wmsgOf w.rows) := by
      rw [← List.filterMap_append, List.take_append_drop]
    rw [hsplit, ← filterMapLen (wmsgOf w.rows) (gisW (memberW N img w)) (w.gmo.take j)
      (fun e' he' => wmsgSome N img w e' hag (hrow e' (List.mem_of_mem_take he'))), List.take_left]
  rw [htake, show (memberW N img w).gxImg = img from rfl]
  cases l with
  | LRmw aq rl b0 ts0 rvs wvs kc =>
    simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    obtain ⟨hlat, hval⟩ := hR j e aq rl _ _ _ wvs kc hj hl
    rw [← ha]
    exact ⟨hlat jj t ht, hval jj t v ht hv⟩
  | _ => simp [lbIsW] at hW <;> simp [lbRd] at hrd

/-! # 3. The agreement -/

/-- The per-event label relation: exact but for read timestamps, or (an exempt read) a plain load of the
same footprint. -/
def lblRelX (x : Prop) (l l' : Lbl) : Prop := (¬ x ∧ lblReidx l l') ∨ (x ∧ lblReidxSub l l')

/-- **THE AGREEMENT** of the member `GR` with `G`, up to the exempt reads `X`. -/
def agreeX (G GR : Gexec) (X : Geid → Prop) : Prop :=
  GR.gxImg = G.gxImg ∧
  (∀ e, (gxLbl G e = none ∧ gxLbl GR e = none) ∨
    ∃ l l', gxLbl G e = some l ∧ gxLbl GR e = some l' ∧ lblRelX (X e) l l') ∧
  (∀ (b : Int) (x y : Geid) (vx vy : BitVec 8), gwritesByte G x b vx → gwritesByte G y b vy →
    (gwix G x < gwix G y ↔ gwix GR x < gwix GR y))

/-- A write-relevant relation is exact: an exempt label is a load. -/
theorem relXW (x : Prop) (l l' : Lbl) :
    lblRelX x l l' → (lbIsW l = true ∨ lbIsW l' = true) → l' = l ∨
      ∃ aq rl base ts ts' rvs wvs kc, l = LRmw aq rl base ts rvs wvs kc ∧
        l' = LRmw aq rl base ts' rvs wvs kc ∧ ts'.length = ts.length := by
  rintro (⟨-, h⟩ | ⟨-, h⟩) hW
  · cases l with
    | LRmw aq rl base ts rvs wvs kc =>
      cases l' with
      | LRmw aq' rl' base' ts' rvs' wvs' kc' =>
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, hl⟩ := h
        exact .inr ⟨_, _, _, _, _, _, _, _, rfl, rfl, hl⟩
      | _ => exact h.elim
    | LLoad aq base ts vs =>
      cases l' with
      | LLoad => simp [lbIsW] at hW
      | _ => exact h.elim
    | LStore => exact .inl h
    | LFence => exact .inl h
    | LIo => exact .inl h
  · cases l with
    | LLoad aq base ts vs =>
      cases l' with
      | LLoad => simp [lbIsW] at hW
      | _ => exact h.elim
    | _ => exact h.elim

theorem relXWr (x : Prop) (l l' : Lbl) : lblRelX x l l' → lbWr l' = lbWr l := by
  intro h
  by_cases hW : lbIsW l = true ∨ lbIsW l' = true
  · rcases relXW x l l' h hW with rfl | ⟨_, _, _, _, _, _, _, _, rfl, rfl, -⟩
    · rfl
    · rfl
  · have h1 : lbIsW l = false := by simpa using (not_or.1 hW).1
    have h2 : lbIsW l' = false := by simpa using (not_or.1 hW).2
    have e1 : lbWr l = none := by cases l <;> simp_all [lbIsW, lbWr]
    have e2 : lbWr l' = none := by cases l' <;> simp_all [lbIsW, lbWr]
    rw [e1, e2]

theorem relXIsW (x : Prop) (l l' : Lbl) : lblRelX x l l' → lbIsW l' = lbIsW l := by
  rintro (⟨-, h⟩ | ⟨-, h⟩)
  · cases l <;> cases l' <;> simp_all [lblReidx, lbIsW]
  · cases l <;> cases l' <;> simp_all [lblReidxSub, lbIsW]

theorem relXCls (x : Prop) (l l' : Lbl) : lblRelX x l l' → lbIsW l = true → lbCls l' = lbCls l := by
  intro h hW
  rcases relXW x l l' h (.inl hW) with rfl | ⟨_, _, _, _, _, _, _, _, rfl, rfl, -⟩
  · rfl
  · rfl

/-- The writes of `GR` are `G`'s and conversely. -/
theorem agreeWrIff (G GR : Gexec) (X : Geid → Prop) :
    agreeX G GR X → ∀ e a v, gwritesByte GR e a v ↔ gwritesByte G e a v := by
  rintro ⟨-, hl, -⟩ e a v
  constructor
  · rintro ⟨l', base, vs, j, hl', hwr, hv, ha⟩
    rcases hl e with ⟨-, h2⟩ | ⟨l, l'', h1, h2, hrel⟩
    · rw [h2] at hl'; cases hl'
    · rw [hl', Option.some.injEq] at h2; subst h2
      exact ⟨l, base, vs, j, h1, by rw [← relXWr _ l l' hrel]; exact hwr, hv, ha⟩
  · rintro ⟨l, base, vs, j, hl1, hwr, hv, ha⟩
    rcases hl e with ⟨h1, -⟩ | ⟨l0, l', h1, h2, hrel⟩
    · rw [h1] at hl1; cases hl1
    · rw [hl1, Option.some.injEq] at h1; subst h1
      exact ⟨l', base, vs, j, h2, by rw [relXWr _ l l' hrel]; exact hwr, hv, ha⟩

theorem agreeClsW (G GR : Gexec) (X : Geid → Prop) :
    agreeX G GR X → ∀ e k, gcls G e k → glblIs G e lbIsW → gcls GR e k := by
  rintro ⟨-, hl, -⟩ e k ⟨l0, hl0, hk⟩ ⟨l1, hl1, hW⟩
  rw [hl0, Option.some.injEq] at hl1; subst hl1
  rcases hl e with ⟨h1, -⟩ | ⟨l, l', h1, h2, hrel⟩
  · rw [h1] at hl0; cases hl0
  · rw [hl0, Option.some.injEq] at h1; subst h1
    exact ⟨l', h2, by rw [relXCls _ _ _ hrel hW]; exact hk⟩

/-- RMW reads agree (both directions). -/
theorem agreeRmwRd (G GR : Gexec) (X : Geid → Prop) :
    agreeX G GR X →
    (∀ e a t v, glblIs G e lbIsW → greadsByte G e a t v → ∃ t', greadsByte GR e a t' v) ∧
    (∀ e a t v, glblIs G e lbIsW → greadsByte GR e a t v → ∃ t', greadsByte G e a t' v) := by
  rintro ⟨-, hl, -⟩
  have key : ∀ e l, gxLbl G e = some l → lbIsW l = true →
      ∃ l', gxLbl GR e = some l' ∧ (l' = l ∨ ∃ aq rl base ts ts' rvs wvs kc,
        l = LRmw aq rl base ts rvs wvs kc ∧ l' = LRmw aq rl base ts' rvs wvs kc ∧
        ts'.length = ts.length) := by
    intro e l h1 hW
    rcases hl e with ⟨h, -⟩ | ⟨l0, l', h, h2, hrel⟩
    · rw [h] at h1; cases h1
    · rw [h1, Option.some.injEq] at h; subst h
      exact ⟨l', h2, relXW _ _ _ hrel (.inl hW)⟩
  refine ⟨?_, ?_⟩
  · rintro e a t v ⟨l1, hl1, hW⟩ ⟨l0, base, ts, vs, j, hl0, hrd, ht, hv, ha⟩
    rw [hl1, Option.some.injEq] at hl0; subst hl0
    obtain ⟨l', h2, h3⟩ := key e _ hl1 hW
    rcases h3 with h3 | ⟨aq, rl, b0, ts0, ts', rvs, wvs, kc, h4, h5, hlen⟩
    · subst h3
      exact ⟨t, _, base, ts, vs, j, h2, hrd, ht, hv, ha⟩
    · subst h4 h5
      simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
      obtain ⟨h6, h7, h8⟩ := hrd
      subst h6 h7 h8
      have hj : j < ts'.length := by rw [hlen]; exact lookup_lt_Some ht
      exact ⟨ts'[j], _, _, ts', _, j, h2, rfl, List.getElem?_eq_getElem hj, hv, ha⟩
  · rintro e a t v ⟨l1, hl1, hW⟩ ⟨l0, base, ts', vs, j, hl0, hrd, ht, hv, ha⟩
    obtain ⟨l', h2, h3⟩ := key e _ hl1 hW
    rw [h2, Option.some.injEq] at hl0; subst hl0
    rcases h3 with h3 | ⟨aq, rl, b0, ts0, ts1, rvs, wvs, kc, h4, h5, hlen⟩
    · subst h3
      exact ⟨t, _, base, ts', vs, j, hl1, hrd, ht, hv, ha⟩
    · subst h4 h5
      simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
      obtain ⟨h6, h7, h8⟩ := hrd
      subst h6 h7 h8
      have hj : j < ts0.length := by rw [← hlen]; exact lookup_lt_Some ht
      exact ⟨ts0[j], _, _, ts0, _, j, hl1, rfl, List.getElem?_eq_getElem hj, hv, ha⟩

/-- **FULL LOCK CO, at every lock set.** -/
theorem lockCoOfX (G GR : Gexec) (X : Geid → Prop) (L : Int → Prop) :
    agreeX G GR X → CertZ18.lockCoSP G GR L := by
  rintro ⟨-, -, hco⟩ b x y vx vy _ hx hy _ _
  exact hco b x y vx vy hx hy

/-- **CertZ18's `agreeW3` at EVERY lock set.** -/
theorem agreeW3OfX (G GR : Gexec) (X : Geid → Prop) (L : Int → Prop) :
    agreeX G GR X → CertZ18.agreeW3 G GR L := by
  intro h
  exact ⟨h.1, agreeWrIff G GR X h, agreeClsW G GR X h, agreeRmwRd G GR X h, lockCoOfX G GR X L h⟩

/-- **CertZ24's `agreeW4` with `nf = True`** (the lock set `fun _ => False`: no event is a failed
acquire of a lock byte in it).  At a real lock set `agreeW4` is false for the P member (a failed acquire
is replayed and writes); see `agreeW3OfX`. -/
theorem agreeW4OfX (G GR : Gexec) (X : Geid → Prop) :
    agreeX G GR X → CertZ24.agreeW4 G GR (fun _ => False) := by
  intro h
  have hnf : ∀ e, CertZ24.nf G (fun _ => False) e := fun _ ⟨_, hb, _⟩ => hb
  obtain ⟨h1, h2⟩ := agreeRmwRd G GR X h
  refine ⟨h.1, fun e a v hw => (agreeWrIff G GR X h e a v).1 hw, fun e _ _ _ => hnf e,
    fun e a v _ hw => (agreeWrIff G GR X h e a v).2 hw, fun e k _ hc hW => agreeClsW G GR X h e k hc hW,
    ⟨fun e a t v _ hW hr => h1 e a t v hW hr, fun e a t v hW hr => ?_⟩, lockCoOfX G GR X _ h⟩
  -- the member side: a member RMW is a GF RMW
  obtain ⟨-, hl, -⟩ := h
  obtain ⟨l', hl', hW'⟩ := hW
  rcases hl e with ⟨-, h0⟩ | ⟨l, l'', h0, h3, hrel⟩
  · rw [h0] at hl'; cases hl'
  · rw [hl', Option.some.injEq] at h3; subst h3
    exact h2 e a t v ⟨l, h0, by rw [← relXIsW _ _ _ hrel]; exact hW'⟩ hr

end SbAgree

end Weak
