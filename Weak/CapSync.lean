/-
Weak: **W11-F row 6a — A1 `syncRealized` at the route-P `SbCand` member: THE GLUE** (plan rev 55 row
6a; coordinator decision 2026-10-19: options (a-1)/(b-1) of PROGRESS-W11F-6i6m Task F taken
provisionally and queued in the MachCSL lane).  Lean-only, no Rocq twin.

`RvwmoXv6Adequacy.syncRealized GD σ j s` (`Weak/RvwmoXv6Adequacy.lean:664`) asks, at the realized
read's post-state `σ`: (a) every write `W` of hart `j` at or below `σ.top` that is the ACQUIRE entry
of a `syncHop` on a hop byte is an `.aq` read po-before-or-at the segment entry; (b) `j`'s floor at a
publication store at `r` gives a read `Y`, gmo-after a write at or after `r`, fence-covering the exit.

  §1  **THE TWO INTERIM PREMISES** (NAMED; to be discharged by the MachCSL export, row 6a (a-1)/(b-1)):
      `CapSync.lockNzExclP σ` — a hop's acquire entry was an EXCLUSIVE write (`σ.pcAt = -1`);
      `CapSync.startedFloorPcP σ lr` — a hart's positive floor at a publication byte of another writer
      was raised by a load at `main+0x16` (`lr`: the ghost load-pc record (b-1) adds to `MState`).
  §2  **the registered pc-log bridge** (PROVED, register-free): along a W4 record, a message whose
      machine pc-log entry is `-1` was appended by an exclusive pf step (`LRmw` / `LExStore`) or by
      the disk agent; an `LRmw` message is `.WCexcl` (`CapSync.pcNegExcl`, `CapSync.exclClass`) —
      `CapPcLog`'s `pcLogAgree` read backwards.
  §3  **the member's row order** (PROVED, P-W2 level): at a valid walk, two gmo-at-event events of
      one row (loads, AMOs, I/O) are in gmo order iff in program order (`CapSync.memberPoOfGmo`).
  §4  `.aq` at the member from GF's image fact (`CapSync.amoAqOfAgree`, from `SbOrd.ImgFacts` and
      `SbAgree.agreeX`); the static fence bits at `main+0x18` (`fence r,rw`, `CapSync.spinFenceBits`).
  §5  **the realization interfaces** (NAMED, P-W6's step map / OWN.115's per-cycle facts):
      `exclHopReal`, `realBefore`, `floorReadReal`, `spinFenceNext`; and **THE GLUE**
      `CapSync.syncRealizedOf` — `CapSync.syncRealizedP` (= `syncRealized` with `0 < r` in (b),
      finding F-6a-6) at the member, from §1–§4 and the interfaces;
      `CapSync.chainHypsOfSyncPathP` — W11-D's derivation consumes the corrected interface.

Findings (PROGRESS Task F): F-6a-4 `pcAt = -1` also stamps the walker's A/D write-back (an
`LExStore`), so `exclHopReal` keeps "no walker write-back on a hop acquire"; F-6a-5 (b) needs the
segment exit to be a RAM access (`fence r,rw` orders no I/O; `gfenceCovers` is RAM-only); F-6a-6
`syncRealized`'s (b) is FALSE at `r = 0` (the image entry `⟨0, 0, v⟩` of `started` names hart 0)
— the consumer only uses `r > p + 1`, so `syncRealizedP` carries `0 < r`; F-6a-7 R-b2 (the event
after the `main+0x16` load is the `main+0x18` fence) is NOT register-free: Sail's interrupt check
and the fetch at `main+0x18` read the CSR state of the program state — named `spinFenceNext`.

Spec: rule 5 (`.aq`) and rule 4 (`fence r,rw`: pr before, sr/sw after) are riscv.cat's; the
premises are xv6 run facts (FAITHFUL once discharged, WEAKER while named).  Names `CapSync.*`.
-/
import Weak.SbOrd
import Weak.LockFacts
import Weak.CapRelSite
import Weak.CapPcLog

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

/-! # 1. The two interim premises (NAMED) -/

/-- The boot spin's load of `started`: `main+0x16 c.lw a5,0(a4)` (`racyLoadPcs`). -/
def CapSync.spinLoadPc : Int := (KernelSyms.«main» : Int) + 0x16

/-- The boot fence after it: `main+0x18 fence r,rw` (`acqFencePcs`). -/
def CapSync.spinFencePc : Int := (KernelSyms.«main» : Int) + 0x18

/-- **INTERIM PREMISE (a-1)** — interim, to be discharged by the MachCSL export (a-1), row 6a: the
acquire entry of every `syncHop` on a hop byte was an EXCLUSIVE write (MachCSL stamps an exclusive
store's position `-1` in `pcAt`, `MachCSL/Lang.lean:187-188`; only `wp_s_amoswap` writes a
nonzero word into a lock region).  The hop instance of "every nonzero lock-word entry has
`pcAt = -1`". -/
def CapSync.lockNzExclP (σ : MState) : Prop :=
  ∀ (b : PAddr) (A B : CPU) (r a : Nat), Xv6.AccessDiscipline.hopByteAt σ b a →
    syncHop σ.mem b A r B a → σ.pcAt a = -1

/-- **INTERIM PREMISE (b-1)** — interim, to be discharged by the MachCSL export (b-1), row 6a:
`lr c f` is the ghost LOAD-pc record (b-1) adds to `MState` (the `PC` of the load — or walk read —
that last raised hart `c`'s coherence floor at byte `f`); a hart's POSITIVE floor at a publication
byte of ANOTHER writer was raised at the boot spin's load `main+0x16`. -/
def CapSync.startedFloorPcP (σ : MState) (lr : CPU → PAddr → Int) : Prop :=
  ∀ (f : PAddr) (w j : CPU), (Xv6.AccessDiscipline.xv6Env σ).isPub f w → j ≠ w →
    0 < (σ.hr j).coh f → lr j f = CapSync.spinLoadPc

/-! # 2. The registered pc-log bridge: `pcAt = -1` ⇒ an exclusive (or disk) append -/

/-- A recorded pc of `-1`: an appending step that is not a plain store, or whose agent has no pc. -/
theorem CapSync.recPcNeg (x : MachOfPf.PfRec) : RelSiteProvPc.recPc x = some (-1) →
    RelSiteProvPc.lbAppends x.lb = true ∧
    (RelSiteProvPc.lbStore x.lb = false ∨ x.pre.pcAgs[x.ag]? = none ∨
      ∃ ag, x.pre.pcAgs[x.ag]? = some ag ∧ RelSiteProvPc.pcOfSt ag.paSt = -1) := by
  unfold RelSiteProvPc.recPc
  intro h
  split at h
  · rename_i ha
    refine ⟨ha, ?_⟩
    simp only [Option.some.injEq] at h
    split at h
    · right
      cases hl : x.pre.pcAgs[x.ag]? with
      | none => exact .inl rfl
      | some ag => rw [hl] at h; exact .inr ⟨ag, rfl, h⟩
    · rename_i hs
      exact .inl (by simpa using hs)
  · cases h

/-- The issuing pc `-1` is the disk agent's (a hart's `PC` is a natural number). -/
theorem CapSync.pcOfStNeg (p : Pexv6) : RelSiteProvPc.pcOfSt p = -1 → ∃ d, p = .PDisk d := by
  cases p with
  | PHart cpu m rs fn ib =>
    intro h
    simp only [RelSiteProvPc.pcOfSt] at h
    have := Int.natCast_nonneg ((rs .PC).toNat)
    omega
  | PDisk d => intro _; exact ⟨d, rfl⟩

/-- `-1` at an offset of a record: message `c.pcLog.length + q` was appended by a recorded step
stamped by `pclsEv` at its pre-state, which is not a plain store or is the disk agent's. -/
theorem CapSync.pcNegOff {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {r : List MachOfPf.PfRec}
    {cN : Wpcfg Pexv6 Efab} (h : MachOfPf.contRC fok fcutT c st r cN) :
    ∀ (q : Nat) (mq : Wmsg), cN.pcLog[c.pcLog.length + q]? = some mq →
      (RelSiteProvPc.recPcLog r)[q]? = some (-1) →
      ∃ (x : MachOfPf.PfRec) (ag : Wpagent Pexv6), x ∈ r ∧ x.pre.pcAgs[x.ag]? = some ag ∧
        mq.wmAk = pclsEv ag.paSt x.lb ag.paWs ∧ RelSiteProvPc.lbAppends x.lb = true ∧
        (RelSiteProvPc.lbStore x.lb = false ∨ ∃ d, ag.paSt = .PDisk d) := by
  induction h with
  | nil => intro q mq _ hp; simp [RelSiteProvPc.recPcLog] at hp
  | cons c c' st i l k r cN hs _ _ _ _ hr ih =>
    intro q mq hm hp
    obtain ⟨h0, h1⟩ := RelSiteProvPc.stepLog _ _ _ _ _ _ hs
    rw [RelSiteProvPc.recPcLogCons] at hp
    cases ha : RelSiteProvPc.lbAppends l
    · have hp' : (RelSiteProvPc.recPcLog r)[q]? = some (-1) := by
        simpa [RelSiteProvPc.recPc, ha] using hp
      obtain ⟨x, ag, hx, h2⟩ := ih q mq (by rw [h0 ha]; exact hm) hp'
      exact ⟨x, ag, List.mem_cons_of_mem _ hx, h2⟩
    · obtain ⟨ag, m, hlk, he, hk⟩ := h1 ha
      have hpre := RelSiteProvPc.contRPrefix hr
      cases q with
      | zero =>
        have hrc : RelSiteProvPc.recPc ⟨c, i, l, k⟩ = some (if RelSiteProvPc.lbStore l then
            (c.pcAgs[i]?).elim (-1) (fun ag => RelSiteProvPc.pcOfSt ag.paSt) else -1) := by
          simp only [RelSiteProvPc.recPc, ha, if_true]
        rw [hrc] at hp
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
        rw [hp] at hrc
        obtain ⟨-, hc⟩ := CapSync.recPcNeg _ hrc
        have hm' : cN.pcLog[c.pcLog.length]? = some m := by
          rw [he] at hpre
          obtain ⟨tl, htl⟩ := hpre
          rw [← htl]
          simp
        rw [Nat.add_zero, hm'] at hm
        cases hm
        refine ⟨⟨c, i, l, k⟩, ag, List.mem_cons_self, hlk, hk, ha, ?_⟩
        rcases hc with hc | hc | ⟨ag', hag', hpc⟩
        · exact .inl hc
        · simp only at hc; rw [hlk] at hc; cases hc
        · simp only at hag'
          rw [hlk, Option.some.injEq] at hag'
          subst hag'
          exact .inr (CapSync.pcOfStNeg _ hpc)
      | succ q =>
        have hp' : (RelSiteProvPc.recPcLog r)[q]? = some (-1) := by
          simpa [RelSiteProvPc.recPc, ha] using hp
        have hlen : c'.pcLog.length = c.pcLog.length + 1 := by rw [he]; simp
        obtain ⟨x, ag', hx, h2⟩ := ih q mq (by rw [hlen, Nat.add_right_comm]; exact hm) hp'
        exact ⟨x, ag', List.mem_cons_of_mem _ hx, h2⟩

/-- **`pcAt = -1` ⇒ an exclusive (or disk) append** at a W4 record from the empty log, through the
pc-log link (a2) `CapRelSite.pcLogAgree` (`CapPcLog.machRunPc` proves it at M2's run). -/
theorem CapSync.pcNegExcl {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {r : List MachOfPf.PfRec}
    {cN : Wpcfg Pexv6 Efab} (h : MachOfPf.contRC fok fcutT c st r cN) (h0 : c.pcLog = [])
    (σ : MState) (ha2 : CapRelSite.pcLogAgree r σ) (q : Nat) (mq : Wmsg)
    (hm : cN.pcLog[q]? = some mq) (hq : q < σ.log.length) (hpc : σ.pcAt (q + 1) = -1) :
    ∃ (x : MachOfPf.PfRec) (ag : Wpagent Pexv6), x ∈ r ∧ x.pre.pcAgs[x.ag]? = some ag ∧
      mq.wmAk = pclsEv ag.paSt x.lb ag.paWs ∧ RelSiteProvPc.lbAppends x.lb = true ∧
      (RelSiteProvPc.lbStore x.lb = false ∨ ∃ d, ag.paSt = .PDisk d) := by
  have hp : (RelSiteProvPc.recPcLog r)[q]? = some (-1) := by
    rw [ha2, CapPcLog.pcLogOfEq]
    simp [hq, hpc]
  exact CapSync.pcNegOff h q mq (by rw [h0]; simpa using hm) hp

/-- The exclusive half of a pf write label (the RMW split's store half). -/
def CapSync.isExStore : Wlabel → Bool
  | .LExStore .. => true
  | _ => false

/-- An appending non-plain-store label's class: `.WCexcl` (an AMO), or it is the split's
`LExStore` (whose class is the access kind's — the walker's A/D write-back included, F-6a-4). -/
theorem CapSync.exclClass (p : Pexv6) (l : Wlabel) (ws : Wstate) :
    RelSiteProvPc.lbAppends l = true → RelSiteProvPc.lbStore l = false →
    pclsEv p l ws = .WCexcl ∨ CapSync.isExStore l = true := by
  cases l <;> simp [RelSiteProvPc.lbAppends, RelSiteProvPc.lbStore, pclsEv, CapSync.isExStore]

/-! # 3. The member's row order -/

namespace CapSync

open SbWalk SbAgree

/-- Entry `e` of the walk state is a gmo-at-event event (a load, an AMO, an I/O access). -/
def evAt (w : WS) (e : Geid) : Prop := ∃ l, (w.rows e.1)[e.2]? = some l ∧ gmoEv l = true

/-- **THE ROW-ORDER INVARIANT**: gmo entries are row events, and two gmo-at-event events of one row
are listed in program order. -/
def RowOrd (w : WS) : Prop :=
  (∀ e, e ∈ w.gmo → e.2 < (w.rows e.1).length) ∧
  w.gmo.Pairwise (fun x y => x.1 = y.1 → evAt w x → evAt w y → x.2 < y.2)

theorem rowOrdInit (img : Image) : RowOrd (init img) :=
  ⟨fun _ h => (by cases h), List.Pairwise.nil⟩

theorem rowsEvGet (w : WS) (s : Estep) (e : Geid) :
    e.2 < (w.rows e.1).length → ((nextI w (.ev s)).rows e.1)[e.2]? = (w.rows e.1)[e.2]? := by
  intro h
  show (upd w.rows s.esAg (w.rows s.esAg ++ [s.esLb]) e.1)[e.2]? = _
  by_cases hi : e.1 = s.esAg
  · rw [hi, updEq, List.getElem?_append_left (by rw [← hi]; exact h)]
  · rw [updNe _ _ _ _ hi]

theorem rowsEvLen (w : WS) (s : Estep) (i : Nat) :
    (w.rows i).length ≤ ((nextI w (.ev s)).rows i).length := by
  show _ ≤ (upd w.rows s.esAg (w.rows s.esAg ++ [s.esLb]) i).length
  by_cases hi : i = s.esAg
  · rw [hi, updEq]; simp
  · rw [updNe _ _ _ _ hi]; exact Nat.le_refl _

theorem evAtEv (w : WS) (s : Estep) (e : Geid) :
    e.2 < (w.rows e.1).length → (evAt (nextI w (.ev s)) e ↔ evAt w e) := by
  intro h
  unfold evAt
  rw [rowsEvGet w s e h]

theorem rowOrdEv (w : WS) (s : Estep) : RowOrd w → RowOrd (nextI w (.ev s)) := by
  rintro ⟨hb, hp⟩
  have hgmo : (nextI w (.ev s)).gmo =
      if gmoEv s.esLb then w.gmo ++ [(s.esAg, (w.rows s.esAg).length)] else w.gmo := rfl
  have hold : w.gmo.Pairwise (fun x y => x.1 = y.1 → evAt (nextI w (.ev s)) x →
      evAt (nextI w (.ev s)) y → x.2 < y.2) :=
    List.Pairwise.imp_of_mem (fun {x y} hx hy hr hxy ex ey =>
      hr hxy ((evAtEv w s x (hb x hx)).1 ex) ((evAtEv w s y (hb y hy)).1 ey)) hp
  have hnew : (s.esAg, (w.rows s.esAg).length).2 <
      ((nextI w (.ev s)).rows (s.esAg, (w.rows s.esAg).length).1).length := by
    show (w.rows s.esAg).length < (upd w.rows s.esAg (w.rows s.esAg ++ [s.esLb]) s.esAg).length
    rw [updEq]; simp
  refine ⟨fun e he => ?_, ?_⟩
  · rw [hgmo] at he
    split at he
    · rcases List.mem_append.1 he with he | he
      · exact Nat.lt_of_lt_of_le (hb e he) (rowsEvLen w s e.1)
      · rw [List.mem_singleton] at he; subst he; exact hnew
    · exact Nat.lt_of_lt_of_le (hb e he) (rowsEvLen w s e.1)
  · rw [hgmo]
    split
    · refine List.pairwise_append.2 ⟨hold, List.pairwise_singleton _ _, fun x hx y hy hxy _ _ => ?_⟩
      rw [List.mem_singleton] at hy
      subst hy
      have := hb x hx
      simp only at hxy ⊢
      rw [hxy] at this
      exact this
    · exact hold

theorem rowOrdLand (img : Image) (w : WS) (i k : Nat) :
    Inv img w → RowOrd w → RowOrd (nextI w (.land i k)) := by
  intro hI hR
  cases hpk : (w.pend i)[k]? with
  | none => simp only [nextI, hpk]; exact hR
  | some p =>
    obtain ⟨hb, hp⟩ := hR
    have hmem : p ∈ w.pend i := List.mem_of_getElem? hpk
    obtain ⟨rl, base, vs, kc, hlb, -⟩ := hI.pendSt i p hmem
    have heq : nextI w (.land i k) =
        ⟨SbCand.nextL w.σ i k, upd w.pend i ((w.pend i).eraseIdx k), w.rows, w.fw,
          w.gmo ++ [(i, p.1)]⟩ := by
      simp only [nextI, hpk]
    rw [heq]
    refine ⟨fun e he => ?_, ?_⟩
    · rcases List.mem_append.1 he with he | he
      · exact hb e he
      · rw [List.mem_singleton] at he; subst he
        exact (List.getElem?_eq_some_iff.1 hlb).1
    · refine List.pairwise_append.2 ⟨hp, List.pairwise_singleton _ _, fun x _ y hy _ _ ey => ?_⟩
      rw [List.mem_singleton] at hy
      subst hy
      obtain ⟨l, hl, hg⟩ := ey
      change (w.rows i)[p.1]? = some l at hl
      rw [hlb, Option.some.injEq] at hl
      subst hl
      simp [gmoEv, isSt] at hg

theorem rowOrdStAt (pol : SbPol) (c : CandW) (hv : validW pol c) : ∀ k, RowOrd (stAt c k) := by
  intro k
  induction k with
  | zero => exact rowOrdInit c.img
  | succ k ih =>
    cases hk : c.its[k]? with
    | none =>
      show RowOrd (match c.its[k]? with
        | some it => nextI (stAt c k) it
        | none => stAt c k)
      rw [hk]; exact ih
    | some it =>
      rw [stAtSucc c k it hk]
      cases it with
      | ev s => exact rowOrdEv _ s ih
      | land i j => exact rowOrdLand c.img _ i j (invStAt pol c hv k) ih

theorem pairLookup {α : Type} {R : α → α → Prop} :
    ∀ (l : List α) (i j : Nat) (x y : α), l.Pairwise R → l[i]? = some x → l[j]? = some y → i < j →
      R x y
  | [], _, _, _, _, _, h, _, _ => by simp at h
  | a :: l, i, j, x, y, hp, hx, hy, hij => by
    rw [List.pairwise_cons] at hp
    cases j with
    | zero => omega
    | succ j =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        exact hp.1 y (List.mem_of_getElem? (by simpa using hy))
      | succ i =>
        exact pairLookup l i j x y hp.2 (by simpa using hx) (by simpa using hy) (by omega)

theorem gmoEvFix (G0 : Gexec) (i : Nat) (l : Lbl) (f : List (Option Nat)) :
    gmoEv (fixLbl G0 i l f) = gmoEv l := by cases l <;> rfl

end CapSync

open SbWalk SbAgree in
/-- **THE MEMBER'S ROW ORDER** (P-W2 level): at a valid walk, two gmo-at-event events of one row
(loads, AMOs, I/O — NOT plain stores, which enter gmo at their landing) are gmo-ordered as they are
po-ordered. -/
theorem CapSync.memberPoOfGmo (pol : SbPol) (N : Nat) (c : CandW) (hv : validW pol c)
    (x y : Geid) (lx ly : Lbl) :
    gmoLt (memberP N c) x y → x.1 = y.1 → gxLbl (memberP N c) x = some lx → gmoEv lx = true →
    gxLbl (memberP N c) y = some ly → gmoEv ly = true → x.2 < y.2 := by
  intro hlt hxy hx gx hy gy
  obtain ⟨hxm, hym, hpos⟩ := hlt
  obtain ⟨-, hp⟩ := CapSync.rowOrdStAt pol c hv c.its.length
  have hgm : (memberP N c).gxGmo = (cur c).gmo := rfl
  have ev : ∀ e le, gxLbl (memberP N c) e = some le → gmoEv le = true → CapSync.evAt (cur c) e := by
    intro e le he ge
    obtain ⟨-, l, hl, rfl⟩ := memLblInv N c.img (cur c) e le he
    exact ⟨l, hl, by rw [← CapSync.gmoEvFix]; exact ge⟩
  have lx' := gposElemLookup _ x hxm
  have ly' := gposElemLookup _ y hym
  rw [hgm] at lx' ly'
  exact CapSync.pairLookup _ _ _ x y hp lx' ly' hpos hxy (ev x lx hx gx) (ev y ly hy gy)

/-! # 4. `.aq` at the member; the boot fence's bits -/

/-- Every AMO of `G` is an acquire (`SbOrd.ImgFacts.amoAq`'s statement). -/
def CapSync.amoAqAt (G : Gexec) : Prop :=
  ∀ e aq rl base ts rvs wvs kc, gxLbl G e = some (LRmw aq rl base ts rvs wvs kc) → aq = true

/-- The member's AMOs are GF's (`agreeX` keeps every write label but read timestamps). -/
theorem CapSync.amoAqOfAgree (G GR : Gexec) (X : Geid → Prop) :
    SbOrd.ImgFacts G → SbAgree.agreeX G GR X → CapSync.amoAqAt GR := by
  rintro hI ⟨-, hl, -⟩ e aq rl base ts rvs wvs kc he
  rcases hl e with ⟨-, h2⟩ | ⟨l, l', h1, h2, hrel⟩
  · rw [he] at h2; cases h2
  · rw [he, Option.some.injEq] at h2
    subst h2
    rcases SbAgree.relXW _ l _ hrel (.inr rfl) with h | ⟨aq', rl', base', ts', ts'', rvs', wvs', kc', hl1, hl2, -⟩
    · subst h; exact hI.amoAq e _ _ _ _ _ _ _ h1
    · cases hl2; exact hI.amoAq e _ _ _ _ _ _ _ (hl1 ▸ h1)

/-- The boot fence's label (`main+0x18`'s bits). -/
def CapSync.spinFenceLbl : Lbl :=
  LFence (wFencePr (kw CapSync.spinFencePc)) (wFencePw (kw CapSync.spinFencePc))
    (wFenceSr (kw CapSync.spinFencePc)) (wFenceSw (kw CapSync.spinFencePc))

/-- `main+0x18` is `fence r,rw`: `pr`, `sr`, `sw` set (the image). -/
theorem CapSync.spinFenceBits :
    wFencePr (kw CapSync.spinFencePc) = true ∧ wFenceSr (kw CapSync.spinFencePc) = true ∧
    wFenceSw (kw CapSync.spinFencePc) = true := by
  decide +kernel

/-! # 5. The realization interfaces and THE GLUE -/

/-- **REALIZATION INTERFACE (P-W6)**: at the member, a hart write stamped exclusive (`pcAt = -1`) at
its position that is a hop's acquire entry is an AMO — the step map's `CapPcLog.storeLbl` kind
(§2 gives its registered pc-log half), plus F-6a-4: no walker A/D write-back is a hop acquire. -/
def CapSync.exclHopReal (GD : Gdexec) (σ : MState) : Prop :=
  ∀ (W : Geid) (b : PAddr) (A B : CPU) (r : Nat), W ∈ gwrites GD.gdG → W.1 = hartAgent B →
    Xv6.AccessDiscipline.hopByteAt σ b (gwix GD.gdG W) → syncHop σ.mem b A r B (gwix GD.gdG W) →
    σ.pcAt (gwix GD.gdG W) = -1 →
    ∃ aq rl base ts rvs wvs kc, gxLbl GD.gdG W = some (LRmw aq rl base ts rvs wvs kc)

/-- **REALIZATION INTERFACE (P-W6)**: `σ` is the machine state right after event `e`'s walk step —
every member write at or below `σ.top` is `e` or gmo-before it. -/
def CapSync.realBefore (GD : Gdexec) (σ : MState) (e : Geid) : Prop :=
  ∀ W, W ∈ gwrites GD.gdG → gwix GD.gdG W ≤ σ.top → W = e ∨ gmoLt GD.gdG W e

/-- **REALIZATION INTERFACE (P-W6)**: hart `j`'s floor at a publication byte naming the writer's
entry at `r` was raised by a realized read `Y` of `j` (issuing pc `ipc Y` = the ghost record's
`lr j f`) of a write at or after `r`, before the segment entry. -/
def CapSync.floorReadReal (GD : Gdexec) (σ : MState) (lr : CPU → PAddr → Int) (ipc : Geid → Int)
    (j : CPU) (s : Seg) : Prop :=
  ∀ (f : PAddr) (w : CPU) (r : Nat) (v : BitVec 8) (H : Hist), j ≠ w →
    (Xv6.AccessDiscipline.xv6Env σ).isPub f w → σ.mem[f]? = some H →
    (⟨r, hartAgent w, v⟩ : HEnt) ∈ H → 0 < r → r ≤ (σ.hr j).coh f →
    ∃ (W Y : Geid), W ∈ gwrites GD.gdG ∧ r ≤ gwix GD.gdG W ∧ (W = Y ∨ gmoLt GD.gdG W Y) ∧
      Y.1 = j.val ∧ glblIs GD.gdG Y lbIsR ∧ ipc Y = lr j f ∧ WeakRvwmoGraph.gpo GD.gdG Y s.sgEntry

/-- **PER-CYCLE INTERFACE (R-b2; OWN.115's kind, F-6a-7)**: the row event after a read issued at
`main+0x16` is the `main+0x18` fence (Sail: `c.lw` emits the load, the next boundary takes no trap
and fetches `fence r,rw` — CSR state of the program state). -/
def CapSync.spinFenceNext (GD : Gdexec) (ipc : Geid → Int) : Prop :=
  ∀ Y, ipc Y = CapSync.spinLoadPc → glblIs GD.gdG Y lbIsR →
    gxLbl GD.gdG (Y.1, Y.2 + 1) = some CapSync.spinFenceLbl

/-- **`syncRealized` CORRECTED (F-6a-6)**: (b) asks `0 < r` (a publication STORE, not the image
entry `⟨0, 0, v⟩`, whose author field names hart 0); otherwise `syncRealized` verbatim. -/
def CapSync.syncRealizedP (GD : Gdexec) (σ : MState) (j : CPU) (s : Seg) : Prop :=
  (∀ (W : Geid) (b : PAddr) (C : CPU) (r : Nat), W ∈ gwrites GD.gdG → W.1 = hartAgent j →
      gwix GD.gdG W ≤ σ.top → Xv6.AccessDiscipline.hopByteAt σ b (gwix GD.gdG W) →
      syncHop σ.mem b C r j (gwix GD.gdG W) →
      glblIs GD.gdG W lbIsR ∧ glblIs GD.gdG W lbAq ∧
        (W = s.sgEntry ∨ WeakRvwmoGraph.gpo GD.gdG W s.sgEntry)) ∧
  (∀ (f : PAddr) (w : CPU) (r : Nat) (v : BitVec 8) (H : Hist), j ≠ w →
      (Xv6.AccessDiscipline.xv6Env σ).isPub f w → σ.mem[f]? = some H →
      (⟨r, hartAgent w, v⟩ : HEnt) ∈ H → 0 < r → r ≤ (σ.hr j).coh f →
      ∃ (W Y : Geid), W ∈ gwrites GD.gdG ∧ r ≤ gwix GD.gdG W ∧ (W = Y ∨ gmoLt GD.gdG W Y) ∧
        gfenceCovers GD.gdG Y s.sgExit)

/-- `syncRealized` gives the corrected interface. -/
theorem CapSync.syncRealizedPOf (GD : Gdexec) (σ : MState) (j : CPU) (s : Seg) :
    syncRealized GD σ j s → CapSync.syncRealizedP GD σ j s :=
  fun h => ⟨h.1, fun f w r v H hne hp hf he _ hr => h.2 f w r v H hne hp hf he hr⟩

/-- **THE GLUE — A1 `syncRealized` AT THE `SbCand` MEMBER**: from the two interim premises, the
member's row order, GF's `.aq` image fact, the boot fence's bits and the realization interfaces. -/
theorem CapSync.syncRealizedOf (pol : SbPol) (N : Nat) (c : SbWalk.CandW) (GD : Gdexec)
    (hG : GD.gdG = SbAgree.memberP N c) (hv : SbWalk.validW pol c)
    (σ : MState) (j : CPU) (s : Seg) (lr : CPU → PAddr → Int) (ipc : Geid → Int)
    (hAq : CapSync.amoAqAt GD.gdG)
    (hL : CapSync.lockNzExclP σ) (hP : CapSync.startedFloorPcP σ lr)
    (hRA : CapSync.exclHopReal GD σ) (hRB : CapSync.realBefore GD σ s.sgEntry)
    (hRF : CapSync.floorReadReal GD σ lr ipc j s) (hR2 : CapSync.spinFenceNext GD ipc)
    (hj : s.sgEntry.1 = j.val) (hEnt : glblIs GD.gdG s.sgEntry lbIsR)
    (hrun : s.sgEntry = s.sgExit ∨ WeakRvwmoGraph.gpo GD.gdG s.sgEntry s.sgExit)
    (hexR : glblIs GD.gdG s.sgExit lbIsR ∨ glblIs GD.gdG s.sgExit lbIsW) :
    CapSync.syncRealizedP GD σ j s := by
  refine ⟨fun W b C r hW hW1 htop hhb hsh => ?_, fun f w r v H hne hpub hf he hr0 hrle => ?_⟩
  · -- (a): the hop's acquire is an exclusive write, hence an AMO, hence `.aq`; realized in order
    have hpc := hL b C j r _ hhb hsh
    obtain ⟨aq, rl, base, ts, rvs, wvs, kc, hlb⟩ := hRA W b C j r hW hW1 hhb hsh hpc
    have haq := hAq W aq rl base ts rvs wvs kc hlb
    subst haq
    refine ⟨⟨_, hlb, rfl⟩, ⟨_, hlb, rfl⟩, ?_⟩
    rcases hRB W hW htop with h | h
    · exact .inl h
    · right
      obtain ⟨le, hle, hler⟩ := hEnt
      have hge : SbWalk.gmoEv le = true := by
        cases le <;> simp_all [lbIsR, SbWalk.gmoEv, SbWalk.isSt, lbIsMem]
      have hrow : W.1 = s.sgEntry.1 := by rw [hW1, hj]; rfl
      rw [hG] at h hlb hle
      have hlt := CapSync.memberPoOfGmo pol N c hv W s.sgEntry _ le h hrow hlb rfl hle hge
      refine ⟨hrow, hlt, ?_, ?_⟩
      · rw [hG, hlb]; rfl
      · rw [hG, hle]; rfl
  · -- (b): the floor's read is the boot spin's load, followed by `fence r,rw`
    obtain ⟨W, Y, hW, hrW, hWY, hY1, hYR, hipc, hYe⟩ := hRF f w r v H hne hpub hf he hr0 hrle
    have hlr := hP f w j hpub hne (by omega)
    have hfn := hR2 Y (by rw [hipc, hlr]) hYR
    obtain ⟨hpr, hsr, hsw⟩ := CapSync.spinFenceBits
    refine ⟨W, Y, hW, hrW, hWY, wFencePr (kw CapSync.spinFencePc), wFencePw (kw CapSync.spinFencePc),
      wFenceSr (kw CapSync.spinFencePc), wFenceSw (kw CapSync.spinFencePc), ?_, .inl ⟨hYR, hpr⟩, ?_⟩
    · obtain ⟨hYe1, hYe2, -, -⟩ := hYe
      have hx : s.sgEntry.1 = s.sgExit.1 ∧ s.sgEntry.2 ≤ s.sgExit.2 := by
        rcases hrun with h | ⟨h1, h2, -⟩
        · rw [h]; exact ⟨rfl, Nat.le_refl _⟩
        · exact ⟨h1, Nat.le_of_lt h2⟩
      have hne' : Y.2 + 1 ≠ s.sgExit.2 := by
        intro heq
        have hl : gxLbl GD.gdG s.sgExit = some CapSync.spinFenceLbl := by
          have : s.sgExit = (Y.1, Y.2 + 1) := by
            rw [heq, hYe1, hx.1]
          rw [this]; exact hfn
        rcases hexR with ⟨l, hl', hb⟩ | ⟨l, hl', hb⟩
        · rw [hl, Option.some.injEq] at hl'; subst hl'; simp [CapSync.spinFenceLbl, lbIsR] at hb
        · rw [hl, Option.some.injEq] at hl'; subst hl'; simp [CapSync.spinFenceLbl, lbIsW] at hb
      refine ⟨hYe1.trans hx.1, by omega, Y.2 + 1, by omega, by omega, ?_⟩
      exact hfn
    · rcases hexR with h | h
      · exact .inl ⟨h, hsr⟩
      · exact .inr ⟨h, hsw⟩

/-- **W11-D's derivation at the corrected interface** (`chainHypsOfSyncPath`, verbatim but for
`syncRealizedP`: the boot hop's publication store is at `r > p + 1 > 0`). -/
theorem CapSync.chainHypsOfSyncPathP (GD : Gdexec) (log : List Wmsg) (c : Wpcfg Pexv6 Efab)
    (st : List (Nat × Wlabel)) (σ : MState) (j : CPU) (pa : PAddr) (p : Nat) (m : Wmsg)
    (i : Nat) (prev : Geid) (s : Seg)
    (hrd : readAt log c st σ j pa p m) (hi : m.wmTid = some i) (hiN : i < NCPU)
    (hij : i ≠ hartAgent j) (hnb : ¬ benignAt σ pa (p + 1))
    (hwf : gwf GD.gdG) (hlog : logOf GD.gdG log) (hprev : gwriteAt GD.gdG (p + 1) = some prev)
    (hrun : s.sgEntry = s.sgExit ∨ WeakRvwmoGraph.gpo GD.gdG s.sgEntry s.sgExit)
    (hmx : gmem GD.gdG s.sgExit) (hre : CapSync.syncRealizedP GD σ j s) :
    chainHyps GD prev s := by
  obtain ⟨hR, hD, -, hpre, hp, hv, hram, hcoh, heg⟩ := hrd
  have hm := PfStepTsoMem.memEager c st σ hR heg
  have hlo := RvwmoXv6Adequacy.landedOnlyEager σ.mem σ.lp hm
  have hlo' : (Xv6.AccessDiscipline.xv6Env σ).lm = σ.mem := hlo
  have hr := hR.2.2.1
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv
  obtain ⟨hpw, hpix⟩ := gwriteAtInv GD.gdG (p + 1) prev hwf.1 hprev
  have hH := hr.1 pa hram
  have he : (⟨p + 1, i, v⟩ : HEnt) ∈ TsoOfPf.histOf c.pcImg c.pcLog (paZ pa) := by
    have := RvwmoXv6Adequacy.histOfMem c.pcImg c.pcLog (paZ pa) p m v hp hv
    rwa [hi] at this
  have h1 : ∀ b, Xv6.AccessDiscipline.custAtP σ pa (p + 1) ≠ .lockw b :=
    fun b hb' => hnb (.inl ⟨b, hb'⟩)
  have h2 : ∀ w, Xv6.AccessDiscipline.custAtP σ pa (p + 1) ≠ .pub w :=
    fun w hw => hnb (.inr (.inl ⟨w, hw⟩))
  have h3 : Xv6.AccessDiscipline.custAtP σ pa (p + 1) ≠ .pte := fun h => hnb (.inr (.inr (.inl h)))
  rw [← hcoh] at h1 h2 h3
  rcases hD.1 j pa _ ⟨p + 1, i, v⟩ hH he (by simp) (by rw [hm pa _ hH _ he, hcoh]) hiN hij h1 h2 h3
    with hs | hrc
  · rcases hs with ⟨a, ha, hc⟩ | ⟨f, w, r, v', H', hne, hpub, hf, hew, hrle, harm⟩
    · rw [hlo] at hc
      obtain ⟨⟨_, _, _, _, _, _, ht1, h1a⟩, b, C, r, hbl, hsh⟩ :=
        RvwmoXv6Adequacy.hopChainSpan hr hc
      simp only at ht1
      obtain ⟨Hb, va, hHb, hmemA⟩ := RvwmoXv6Adequacy.syncHopAcq hsh
      obtain ⟨W, hW, hix, hW1, -⟩ :=
        RvwmoXv6Adequacy.entGraph hR hpre hwf hlog hHb hmemA (by simp only; omega)
      simp only at hix hW1
      obtain ⟨hWR, hWaq, hWe⟩ := hre.1 W b C r hW hW1 (by rw [hix]; omega)
        (by rw [hix]; exact hbl) (by rw [hix]; exact hsh)
      refine ⟨W, W, hpw, hW, by rw [hix, hpix]; omega, .inl rfl, .inl ⟨hWR, hWaq, ?_⟩⟩
      rcases CatLin.CatReroute.poOrEq GD.gdG _ _ _ hWe hrun with heq | hpo
      · exact .inl heq
      · exact .inr ⟨hpo, hmx⟩
    · have hlt : p + 1 < r := by
        rcases harm with ⟨-, h⟩ | ⟨a, ha, hc⟩
        · exact h
        · rw [hlo'] at hc
          obtain ⟨⟨_, _, _, _, _, _, ht1, h1a⟩, -⟩ :=
            RvwmoXv6Adequacy.hopChainSpan (m := σ.mem) hr hc
          simp only at ht1
          omega
      have hf' : σ.mem[f]? = some H' := by rw [← hlo']; exact hf
      have hrle' : r ≤ (σ.hr j).coh f := by
        obtain ⟨q, hq, hle⟩ := hrle
        have hlr : σ.lp r = some r := hm f H' hf' _ hew
        have hlr' : (Xv6.AccessDiscipline.xv6Env σ).lp r = some r := hlr
        rw [hlr'] at hq
        cases hq
        exact hle
      obtain ⟨W, Y, hW, hrW, hWY, hfc⟩ := hre.2 f w r v' H' hne hpub hf' hew (by omega) hrle'
      exact ⟨W, Y, hpw, hW, by rw [hpix]; omega, hWY, .inr hfc⟩
  · rw [hcoh] at hrc
    exact absurd (.inr (.inr (.inr hrc))) hnb

end Weak
