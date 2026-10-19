/-
Weak: **allocproc route P — row P-W3r-f `HeldPin`: `holding+0x0` from `release+0xc` / `sched+0x14` is
NEVER BLOCKED** (plan rev 56 row P-W3r-f / NAMED-INPUTS N5; design `notes/weak-allocproc-routeP-design.md`
§3.4 per-site table; `notes/weak-allocproc-plan-review-R46.md` §3; PROGRESS-P-W3r-f + P-W3r-g.md).
Lean-only, no Rocq twin.  A PRIMED TWIN: nothing registered imports this file.

**Spec, stated first.**  riscv.cat's load value axiom: a read returns, per byte, the co-latest write among
those gmo-before or po-before it; co ⊆ gmo, and per byte the writes are totally ordered by `gwix`.  The
gated walk (`SbOrd`) lets a plain-load head go under the VALUE gate (`SbOrd.valGate`: the member's top
bytes — forwarded from the own buffer, else the latest landed byte — equal GF's bytes).  At
`holding+0x0` (`lw a5,0(a0)`) called from `release+0xc` or `sched+0x14` the CALLER HOLDS the lock: its
row's winning `amoswap.w.aq` (acquire+0x1c) is realized po-before the head, and an AMO lands at its own
step.  So per byte the landed top and GF's source both lie in the co-window from that swap to the read's
GF source; xv6's lock discipline makes every write in that window write `lkOne` (spinners' failed swaps
write 1, nobody frees the lock but its holder, who has not yet released) — the design's "top = 1 = GF".

  §1  **the value-window lemma** (generic, GF + walk invariants only): `SbHeldPin.WinVal`,
      `SbHeldPin.lastMax` (the member-latest landed write is co-latest among the landed ones),
      `SbHeldPin.lastByte` (its member byte is GF's), **`SbHeldPin.valGateOfWin`**: a plain-load head whose
      every byte has a LANDED anchor write co-before the GF source and a uniform-valued co-window from the
      anchor to the source passes the value gate.  Both members of the top are in the window: an own pending
      entry is co-after every landed write (the landed list is a gmo-prefix, `landedDown`) and po-before the
      read (so co-before-or-at its source); the member-latest landed write is co-at-or-after the anchor and,
      when the source is unlanded, co-before it.
  §2  **`HeldPin`**: `SbHeldPin.HeldRd` (the head's shape: a 4-byte plain load of the lock word `[L,L+4)`, the
      row's realized winning swap on `L` po-before it, writing `lkOne`), the NAMED GF window
      **`SbHeldPin.HeldWinGF`** and its decomposition **`SbHeldPin.heldWinOf`** (word values {0, lkOne} +
      no free write inside the window), **`SbHeldPin.heldPin`** (⇒ `valGate`), the walk-state form
      **`SbHeldPin.heldNeverBlocked`** over the NAMED transport `SbHeldPin.HeldCtx`.
  §3  image facts (`decide +kernel`): the two call contexts (`heldCallShape`).

Spec mark: FAITHFUL (proof organisation over the load value axiom, co ⊆ gmo, and the walk machine; no new
trusted text).  NAMED (FAITHFUL, WEAKER while named): `HeldCtx` (the (T) transport: label ↔ pc + "the
caller holds", P-W6) and `HeldWinGF` (the GF lock-word window; dischargers in its docstring).
Lean-only helpers `SbHeldPin.*`.
-/
import Weak.SbBlocked

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open KernelPinsDef
open Lbl SbWalk SbAgree SbReplay SbOrd

/-! # 1. The value window -/

/-- **THE VALUE WINDOW** of byte `b` from the anchor write `a` up to GF write index `t`: every GF write
of `b` whose write index lies in `[gwix a, t]` writes `v`. -/
def SbHeldPin.WinVal (G : Gexec) (b : Int) (a : Geid) (t : Nat) (v : BitVec 8) : Prop :=
  ∀ e u, gwritesByte G e b u → gwix G a ≤ gwix G e → gwix G e ≤ t → u = v

/-- The member-latest landed write of a byte is gmo-latest among the landed writes of the byte. -/
theorem SbHeldPin.lastMax (G : Gexec) (w : WS) (b : Int) (y l : Geid)
    (hpre : wrAtW w b <+: wrAtG G b) (hnd : G.gxGmo.Nodup) (hy : y ∈ wrAtW w b)
    (hlast : (wrAtW w b).getLast? = some l) : y = l ∨ gpos G y < gpos G l := by
  by_cases hyl : y = l
  · exact .inl hyl
  · right
    obtain ⟨D, hD⟩ := List.getLast?_eq_some_iff.1 hlast
    have hndW : (wrAtW w b).Nodup := (wrAtGNodup G b hnd).sublist hpre.sublist
    rw [hD] at hndW
    have hlD : l ∉ D := fun h => (List.nodup_append.1 hndW).2.2 l h l (by simp) rfl
    have hyD : y ∈ D := by
      have : y ∈ D ++ [l] := by rw [← hD]; exact hy
      rcases List.mem_append.1 this with h | h
      · exact h
      · simp at h; exact absurd h hyl
    obtain ⟨T, hT⟩ := hpre
    have hG : wrAtG G b = (D ++ [l]) ++ T := by rw [← hD, hT]
    have hyG : y ∈ wrAtG G b := by rw [hG]; simp [hyD]
    have hlG : l ∈ wrAtG G b := by rw [hG]; simp
    have p1 : posOf (wrAtG G b) y = posOf D y := by
      rw [hG, posOfApp _ _ y (List.mem_append_left _ hyD), posOfApp _ _ y hyD]
    have p2 : posOf (wrAtG G b) l = D.length := by
      rw [hG, posOfApp _ _ l (by simp), posOfAppNot _ _ l hlD]
      simp [posOf]
    have p3 := posOfLt _ y hyD
    exact (wrAtGLt G b y l hnd hyG hlG).1 (by omega)

section Inv

variable {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid} {w : WS}

/-- The member-latest landed byte of `b` is GF's byte of that write. -/
theorem SbHeldPin.lastByte (hP : PInv N img G X dev w) (b : Int) (l : Geid) (u : BitVec 8)
    (hlast : (wrAtW w b).getLast? = some l) (hw : gwritesByte G l b u) :
    ∃ t', latest img w.σ.ms.msLog b t' ∧ logByte img w.σ.ms.msLog t' b = some u := by
  obtain ⟨t', m, hlat, hm, hlb⟩ := latestOfLast img w b l hP.inv hlast
  refine ⟨t', hlat, ?_⟩
  rw [hlb]
  obtain ⟨l0, base, vs, j, hl, hwrl, hv, ha⟩ := hw
  unfold wmsgOf at hm
  cases hr : (w.rows l.1)[l.2]? with
  | none => rw [hr] at hm; cases hm
  | some l' =>
    rw [hr] at hm
    obtain ⟨l1, hl1, hrel⟩ := hP.pf.1 l.1 l.2 l' hr
    rw [show ((l.1, l.2) : Geid) = l from rfl, hl, Option.some.injEq] at hl1
    subst hl1
    dsimp only at hm
    rw [relXWr _ _ _ hrel, hwrl] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    rw [← ha, msgByteVal]; exact hv

/-- **THE VALUE-WINDOW LEMMA**: a plain-load head each of whose bytes has a LANDED anchor write `a`
(`gwix a ≤` the byte's GF source) and a uniform-valued window `[a, source]` passes the VALUE gate. -/
theorem SbHeldPin.valGateOfWin (hP : PInv N img G X dev w) (hc : CatH G) (himg : G.gxImg = img)
    (x : Nat) (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G (hd w x) = some (LLoad aq base ts vs))
    (hwin : ∀ j t v, ts[j]? = some t → vs[j]? = some v →
      ∃ a, a ∈ wrAtW w (accAddr base j) ∧ gwix G a ≤ t ∧ SbHeldPin.WinVal G (accAddr base j) a t v) :
    valGate w x base ts vs := by
  intro j v hvj
  have hlen : vs.length = ts.length := by
    unfold gxLbl at hl
    cases hr : G.gxProg[(hd w x).1]? with
    | none => rw [hr] at hl; cases hl
    | some row =>
      rw [hr] at hl
      simp only [Option.bind_some] at hl
      exact hc.wf.2.2 _ row _ _ hr hl
  obtain ⟨t, ht⟩ : ∃ t, ts[j]? = some t :=
    ⟨_, List.getElem?_eq_getElem (by rw [← hlen]; exact lookup_lt_Some hvj)⟩
  have hrd : greadsByte G (hd w x) (accAddr base j) t v := ⟨_, base, ts, vs, j, hl, rfl, ht, hvj, rfl⟩
  obtain ⟨a, haW, hat, hW⟩ := hwin j t v ht hvj
  generalize accAddr base j = b at hrd haW hW ⊢
  have hpre := hP.pf.2 b
  have hnd := hc.wf.1
  by_cases hL : landedSrc G w b t
  · obtain ⟨hf, hsl⟩ := SbBlocked.byteOfLanded hP hc x aq base ts vs hl b t v hrd hL
    refine .inr ⟨hf, ?_⟩
    rw [hP.inv.img]
    exact srcVal img G X w (hd w x) b t v hP.inv hP.pf hc.lv himg hrd hsl
  · -- the GF source `s` (not the image: `t = 0` is `landedSrc`)
    obtain ⟨s, hs, hsw⟩ : ∃ s, gwriteAt G t = some s ∧ gwritesByte G s b v := by
      obtain ⟨hsrc, -⟩ := hc.lv _ _ t v hrd
      cases t with
      | zero => exact absurd (.inl rfl) hL
      | succ n =>
        obtain ⟨s', hs', hsw', -⟩ := hsrc
        exact ⟨s', hs', hsw'⟩
    have hsix := (gwriteAtInv G t s hnd hs).2
    have hsW := gwritesOf G s b v hc.wf hsw
    have hsG : s ∈ wrAtG G b := List.mem_filter.2 ⟨(gwrBOf G s b v hc.wf hsw).2, (gwrBOf G s b v hc.wf hsw).1⟩
    have hsNW : s ∉ wrAtW w b := fun h => hL (.inr ⟨s, hs, h⟩)
    have haG : a ∈ wrAtG G b := by obtain ⟨T, hT⟩ := hpre; rw [← hT]; exact List.mem_append_left _ haW
    obtain ⟨ua, hwa⟩ := gwrBTo G a b (List.mem_filter.1 haG).2
    have haWr := gwritesOf G a b ua hc.wf hwa
    -- a GF write of `b` in the landed list is co-at-or-before the source
    have belowSrc : ∀ e u, e ∈ wrAtW w b → gwritesByte G e b u → gwix G e ≤ t := by
      intro e u heW hew
      refine Classical.byContradiction (fun hgt => ?_)
      have heWr := gwritesOf G e b u hc.wf hew
      have hgp := (gwixGposLt G s e hnd hsW heWr).1 (by omega)
      exact hsNW (landedDown G w b s e hpre hnd heW hsG hgp)
    cases hf : SbCand.fwdByte (w.σ.sb x) b with
    | some v' =>
      left
      rcases fwdRel (w.pend x) b with ⟨-, h2⟩ | ⟨p, hp, -, h2, -⟩
      · rw [← hP.inv.sb x, hf] at h2; cases h2
      · rw [← hP.inv.sb x, hf] at h2
        have hpr := pendRealized hP x p hp
        obtain ⟨rl', base', vs', kc', hl', -, -⟩ := pendLbl hP x p hp
        have hpw : gwritesByte G (x, p.1) b v' := pendWritesV hP x p _ v' hp h2.symm
        have hpW := gwritesOf G _ _ _ hc.wf hpw
        have hpo : WeakRvwmoGraph.gpo G (x, p.1) (hd w x) := SBAcq.gpoOf G _ _ _ _ hl' hl rfl hpr
        have hle := (hc.lv _ _ t v hrd).2 _ v' hpw (.inr hpo)
        have hpNW : (x, p.1) ∉ wrAtW w b := fun h' => hP.inv.pendGmo x p hp (List.mem_filter.1 h').1
        have hap : gwix G a ≤ gwix G (x, p.1) := by
          refine Classical.byContradiction (fun hlt => ?_)
          have hgp := (gwixGposLt G _ _ hnd hpW haWr).1 (by omega)
          have hpG : (x, p.1) ∈ wrAtG G b :=
            List.mem_filter.2 ⟨(gwrBOf G _ _ _ hc.wf hpw).2, (gwrBOf G _ _ _ hc.wf hpw).1⟩
          exact hpNW (landedDown G w b _ a hpre hnd haW hpG hgp)
        rw [hW _ v' hpw hap hle]
    | none =>
      right
      refine ⟨rfl, ?_⟩
      obtain ⟨l, hlast⟩ : ∃ l, (wrAtW w b).getLast? = some l := by
        cases h : (wrAtW w b).getLast? with
        | none => rw [List.getLast?_eq_none_iff] at h; rw [h] at haW; simp at haW
        | some l => exact ⟨l, rfl⟩
      have hlW : l ∈ wrAtW w b := List.mem_of_getLast? hlast
      have hlG : l ∈ wrAtG G b := by obtain ⟨T, hT⟩ := hpre; rw [← hT]; exact List.mem_append_left _ hlW
      obtain ⟨ul, hwl⟩ := gwrBTo G l b (List.mem_filter.1 hlG).2
      have hlWr := gwritesOf G l b ul hc.wf hwl
      have hal : gwix G a ≤ gwix G l := by
        rcases SbHeldPin.lastMax G w b a l hpre hnd haW hlast with h | h
        · rw [h]; exact Nat.le_refl _
        · exact Nat.le_of_lt ((gwixGposLt G a l hnd haWr hlWr).2 h)
      have hv := hW l ul hwl hal (belowSrc l ul hlW hwl)
      subst hv
      rw [hP.inv.img]
      exact SbHeldPin.lastByte hP b l _ hlast hwl

end Inv

/-! # 2. `HeldPin` -/

/-- `lkOne`'s four little-endian bytes. -/
def SbHeldPin.lkOneB : List (BitVec 8) := [1#8, 0#8, 0#8, 0#8]

/-- The free lock word's four bytes. -/
def SbHeldPin.zeroB : List (BitVec 8) := [0#8, 0#8, 0#8, 0#8]

/-- **THE HEAD'S SHAPE** (what the (T) transport delivers at `holding+0x0` called from `release+0xc` /
`sched+0x14`): `h` is a 4-byte plain load of the lock word `[L, L+4)`, and `A` is its row's WINNING
acquire swap of `L` (acquire+0x1c, `amoswap.w.aq a5,a5,(s1)` with `a5 = 1`), po-before `h`. -/
def SbHeldPin.HeldRd (G : Gexec) (h : Geid) (L : Int) (A : Geid) : Prop :=
  (∃ ts vs, gxLbl G h = some (LLoad false L ts vs) ∧ ts.length = 4) ∧
  A.1 = h.1 ∧ A.2 < h.2 ∧
  ∃ rl ts' rvs kc, gxLbl G A = some (LRmw true rl L ts' rvs SbHeldPin.lkOneB kc)

/-- **THE GF LOCK-WORD WINDOW** (NAMED; FAITHFUL, WEAKER while named): at every `HeldRd` head, every GF
write of a byte of the lock word co-at-or-after the winning swap and co-at-or-before the head's GF source
of that byte writes `lkOne`'s byte.  Truth for xv6: the window lies inside the row's critical section
(the source is co-before the row's own later `release` store, CoRW); a write of the word there is a
spinner's failed `amoswap` (acquire+0x1c, `a5 = 1`: `SilSite.spinShape`) — a FREE write there would be
another hart's release or a successful acquire inside the section (excluded by mutual exclusion, NF1′
`LockFacts3.nf1S` in the class premise `CatLin.lockDiscGFCZ`), or a plain write to a live lock word
(`initlock` / `kfree`'s fill / `memset`: excluded by publication and lifetime custody).
Dischargers: realized writes — P-W6's state map + `lockWordDiscAtP`'s `wordPin` (every landed entry since
the winning store is `lkOne`); pending / unissued writes — the (T) write-site classification (only
acquire+0x1c, `release+0x1a`'s `sw zero`, `initlock`, the page fills write a lock word) + the emission's
`a5 = 1` + NF1′ (row 6n, `l2ClaimP` kind).  Decomposed by `heldWinOf`. -/
def SbHeldPin.HeldWinGF (G : Gexec) (Held : Geid → Int → Geid → Prop) : Prop :=
  ∀ h L A, Held h L A → ∀ j t v, j < 4 → greadsByte G h (accAddr L j) t v →
    ∀ e u, gwritesByte G e (accAddr L j) u → gwix G A ≤ gwix G e → gwix G e ≤ t →
      SbHeldPin.lkOneB[j]? = some u

section Inv2

variable {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid} {w : WS}

/-- **`HeldPin` — `holding+0x0` WHILE THE CALLER HOLDS PASSES THE VALUE GATE**: the winning swap landed at
its step (an RMW is never pending), it is po-before the head (so co-at-or-before every GF source, load
value), and the window is uniform by `HeldWinGF`. -/
theorem SbHeldPin.heldPin (hP : PInv N img G X dev w) (hc : CatH G) (himg : G.gxImg = img)
    (Held : Geid → Int → Geid → Prop) (hWG : SbHeldPin.HeldWinGF G Held)
    (x : Nat) (L : Int) (A : Geid) (hH : Held (hd w x) L A) (hR : SbHeldPin.HeldRd G (hd w x) L A)
    (ts : List Nat) (vs : List (BitVec 8)) (hl : gxLbl G (hd w x) = some (LLoad false L ts vs)) :
    valGate w x L ts vs := by
  obtain ⟨⟨ts0, vs0, hl0, h40⟩, hA1, hA2, rl, ts', rvs, kc, hAl⟩ := hR
  have h4 : ts.length = 4 := by
    rw [hl, Option.some.injEq] at hl0
    injection hl0 with _ _ hts _
    rw [hts]; exact h40
  have hAr : realized w A := by
    show A.2 < (w.rows A.1).length
    rw [hA1]; exact hA2
  have hAL : SbBlocked.Landed w A := by
    refine ⟨hAr, fun p hp hp1 => ?_⟩
    obtain ⟨rl', base', vs', kc', hl', -, -⟩ := pendLbl hP A.1 p hp
    have h2 : gxLbl G (A.1, p.1) = gxLbl G A := by rw [hp1]
    rw [h2, hAl] at hl'
    cases hl'
  apply SbHeldPin.valGateOfWin hP hc himg x false L ts vs hl
  intro j t v htj hvj
  have hj : j < 4 := by rw [← h4]; exact lookup_lt_Some htj
  have hrd : greadsByte G (hd w x) (accAddr L j) t v := ⟨_, L, ts, vs, j, hl, rfl, htj, hvj, rfl⟩
  obtain ⟨uA, huA⟩ : ∃ u, SbHeldPin.lkOneB[j]? = some u :=
    ⟨_, List.getElem?_eq_getElem (by simp [SbHeldPin.lkOneB]; omega)⟩
  have hwA : gwritesByte G A (accAddr L j) uA := ⟨_, L, SbHeldPin.lkOneB, j, hAl, rfl, huA, rfl⟩
  have hpo : WeakRvwmoGraph.gpo G A (hd w x) := SBAcq.gpoOf G _ _ _ _ hAl hl hA1 hA2
  have hAt := (hc.lv _ _ t v hrd).2 A uA hwA (.inr hpo)
  refine ⟨A, SbBlocked.landedWr hP A _ hAL (gwrBOf G A _ _ hc.wf hwA).1, hAt, ?_⟩
  -- the GF source is in the window, so GF's value is `lkOne`'s byte too
  have hsrcV : SbHeldPin.lkOneB[j]? = some v := by
    obtain ⟨hsrc, -⟩ := hc.lv _ _ t v hrd
    cases t with
    | zero =>
      have := gwixPos G A (gwritesOf G A _ _ hc.wf hwA); omega
    | succ n =>
      obtain ⟨s, hs, hsw, -⟩ := hsrc
      exact hWG _ L A hH j _ v hj hrd s v hsw (by rw [(gwriteAtInv G _ s hc.wf.1 hs).2]; exact hAt)
        (Nat.le_of_eq (gwriteAtInv G _ s hc.wf.1 hs).2)
  intro e u hew hae het
  have := hWG _ L A hH j t v hj hrd e u hew hae het
  rw [hsrcV, Option.some.injEq] at this
  exact this.symm

end Inv2

/-- **THE TRANSPORT (T) AT THE HELD CONTEXTS** (NAMED; FAITHFUL, WEAKER while named; P-W6): at walk state
`w`, every head that realizes `holding+0x0` called from `release+0xc` or `sched+0x14` (`HeldHd`, the label
↔ pc map) has the `HeldRd` shape for some lock `L` and its row's winning swap `A`, and is in the `Held`
relation `HeldWinGF` speaks of.  "The caller holds": `release(L)` is called only by `L`'s holder and
`sched` with `p->lock` held — the MachCSL specs' preconditions; at the realized prefix the holder's
winning `amoswap` is a realized event of its row (P-W6's state map: `lockWordAt (some (x, _)) B W`'s
`B` is that event's landing). -/
def SbHeldPin.HeldCtx (G : Gexec) (HeldHd : Geid → Prop) (Held : Geid → Int → Geid → Prop) (w : WS) :
    Prop :=
  ∀ x, HeldHd (hd w x) → ∃ L A, Held (hd w x) L A ∧ SbHeldPin.HeldRd G (hd w x) L A

/-- **EVERY HELD-CONTEXT `holding+0x0` HEAD IS NEVER BLOCKED** (the per-site table's `HeldPin` row:
`valGate` holds, so `HeadOrdRd` is vacuous there). -/
theorem SbHeldPin.heldNeverBlocked {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop}
    {dev : List Geid} {w : WS} (hP : PInv N img G X dev w) (hc : CatH G) (himg : G.gxImg = img)
    (HeldHd : Geid → Prop) (Held : Geid → Int → Geid → Prop)
    (hT : SbHeldPin.HeldCtx G HeldHd Held w) (hWG : SbHeldPin.HeldWinGF G Held)
    (x : Nat) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G (hd w x) = some (LLoad false base ts vs)) (hH : HeldHd (hd w x)) :
    valGate w x base ts vs := by
  obtain ⟨L, A, hHe, hR⟩ := hT x hH
  have hbL : base = L := by
    obtain ⟨⟨ts0, vs0, hl0, -⟩, -⟩ := hR
    rw [hl, Option.some.injEq] at hl0
    injection hl0
  subst hbL
  exact SbHeldPin.heldPin hP hc himg Held hWG x base A hHe hR ts vs hl

/-- The footprint a GF event writes (base, bytes), off its label. -/
def SbHeldPin.wrOf (G : Gexec) (e : Geid) : Option (Int × List (BitVec 8)) := (gxLbl G e).bind lbWr

/-- **`HeldWinGF` FROM ITS TWO DISCIPLINES**: (W1) every GF write of a lock-word byte in the window is a
WORD write of `[L, L+4)` with value 0 or `lkOne` (realized: `lockDiscW`'s first clause via P-W6; pending /
unissued: the (T) write-site classification + emission values), and (W2) none of them is a FREE (zero)
write (mutual exclusion inside the critical section: NF1′ + publication / lifetime custody). -/
theorem SbHeldPin.heldWinOf (G : Gexec) (Held : Geid → Int → Geid → Prop)
    (hW1 : ∀ h L A, Held h L A → ∀ j t v, j < 4 → greadsByte G h (accAddr L j) t v →
      ∀ e u, gwritesByte G e (accAddr L j) u → gwix G A ≤ gwix G e → gwix G e ≤ t →
        ∃ vs, SbHeldPin.wrOf G e = some (L, vs) ∧ (vs = SbHeldPin.zeroB ∨ vs = SbHeldPin.lkOneB))
    (hW2 : ∀ h L A, Held h L A → ∀ j t v, j < 4 → greadsByte G h (accAddr L j) t v →
      ∀ e u, gwritesByte G e (accAddr L j) u → gwix G A ≤ gwix G e → gwix G e ≤ t →
        SbHeldPin.wrOf G e ≠ some (L, SbHeldPin.zeroB)) :
    SbHeldPin.HeldWinGF G Held := by
  intro h L A hH j t v hj hrd e u hew hae het
  obtain ⟨vs, hvs, hz | h1⟩ := hW1 h L A hH j t v hj hrd e u hew hae het
  · exact absurd (by rw [hvs, hz]) (hW2 h L A hH j t v hj hrd e u hew hae het)
  · subst h1
    obtain ⟨l, base, vs', j', hl, hwr, hv, ha⟩ := hew
    have hlw : SbHeldPin.wrOf G e = some (base, vs') := by unfold SbHeldPin.wrOf; rw [hl]; exact hwr
    rw [hvs, Option.some.injEq] at hlw
    obtain ⟨hb, hv'⟩ := Prod.mk.inj hlw
    subst hb; subst hv'
    have hjj : j' = j := by
      unfold accAddr at ha
      have := ha; omega
    subst hjj
    exact hv

/-! # 3. Image facts -/

/-- **THE TWO HELD CONTEXTS** (`decide +kernel`): `holding+0x0` is `lw a5,0(a0)`; `release+0xc` and
`sched+0x14` are direct calls of `holding` returning to `release+0x10` / `sched+0x18` (two of the three
entries of `holdingCallSites`; the third, `acquire+0x16`, is the NOT-held context of
`SbHeadHop2`'s zero / nonzero arms); `release`'s free store `release+0x1a` is `sw zero,0(s1)` (after its
`fence rw,w`) — the row's own release, po-AFTER the head, which the window of
`HeldWinGF` stays below (CoRW). -/
theorem SbHeldPin.heldCallShape :
    krole (SilSite.sym KernelSyms.«holding» 0x0) = .ORload 15 10 ∧
    kflowOf (SilSite.sym KernelSyms.«release» 0xc) = .FLcall (KernelSyms.«holding» : Int) ∧
    SilSite.sym KernelSyms.«release» 0xc + wSize (kw (SilSite.sym KernelSyms.«release» 0xc)) =
      SilSite.sym KernelSyms.«release» 0x10 ∧
    kflowOf (SilSite.sym KernelSyms.«sched» 0x14) = .FLcall (KernelSyms.«holding» : Int) ∧
    SilSite.sym KernelSyms.«sched» 0x14 + wSize (kw (SilSite.sym KernelSyms.«sched» 0x14)) =
      SilSite.sym KernelSyms.«sched» 0x18 ∧
    holdingCallSites.map Prod.fst = [SilSite.sym KernelSyms.«acquire» 0x16,
      SilSite.sym KernelSyms.«release» 0x10, SilSite.sym KernelSyms.«sched» 0x18] ∧
    krole (SilSite.sym KernelSyms.«release» 0x1a) = .ORstore 9 0 := by
  decide +kernel

end Weak
