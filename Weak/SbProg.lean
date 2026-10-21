/-
Weak: **allocproc route P, row 6m — THE LOCKSTEP-DATUM GLUE: the gated walk CARRIES ITS PROGRAMS**
(plan rev 56 row 6m "what stays is the `CertZ13` datum glue at `relT`"; design
`notes/weak-allocproc-routeP-design.md` §3.2 "the datum is the registered lockstep datum with TAINT at the
three pcs"; `PROGRESS-w3-6m.md`).  Lean-only, no Rocq twin.  A PRIMED TWIN: nothing registered imports
this file.

`SbOrd.walkRunP` (P-W3) builds the gated walk as a MACHINE walk: it never reads program states.  The
program layer `SbWalk.ok`'s `progOk` (every event item realized by its row's program: the admin star with
its fetches at view 0 of the LANDED log, then the label, `SbWalk.evData`) is what the realization (P-W6,
W4-P) consumes, as route T's `SilReplay.run` consumed `SilReplay.progOk`.  This file threads it:

  §1  the walk fabric (`devCnt`: the number of realized fabric members; the walk's fabric is
      `fab (devCnt …)` — fabric order is the gate's `fabOk`, prefix-closure is `PInv.dvP`);
  §2  the reachable states `Reach`, **THE PROGRAM INVARIANT `PrgInv`** (the program data, every row's
      program state LOCKSTEP-or-`TR`-TAINTED w.r.t. its emission `(D x).f n` — `SilSiteStep.relS TR`,
      of which `CertZ13.relT` is the instance at `TR := relTArm`, `relSRelT` —, the walk fabric), and
      the two NAMED inputs:
      * **`SailX`** — THE SAIL MEANING OF THE THREE-PC TAINT (`ip->ref` ×2 [OWN.112], `holding+0x12`
        **REVISIT [OWN.124]**): from a `TR`-tainted state, or from lockstep at an exempt read, the row's
        program realizes the member's label and ends lockstep or `TR` (`SilSiteStep.sailQ` re-hosted on
        `SbWalk`; O-P-W2-a, kept NAMED by P-W2 and P-W3r-a; it is given BOTH exempt-value facts);
      * **`FetchProg`** — FETCH PROGRESS (finding **F-6m-1**, `PROGRESS-w3-6m.md` §1): the gate does not
        look at a block's FETCHES and fetches never forward, so a head whose star fetches a byte whose
        GF source is the row's own PENDING store (user code writing its own `RWX` page, `fence.i`,
        executing it) is enabled while `fetchOk` fails; `FetchProg` says that then some enabled target
        is not fetch-blocked.  TRUE for xv6 (kernel text is never written; user text is landed by the
        `p->lock` hand-off or is own-pending with its co-predecessor's readers realized — user-page
        custody), FALSE for general code (RVWMO + Zifencei admit `s: st b; fence.i; fetch b; st c` ∥
        `ld c; fence r,r; ld b ← old`), so it is a program fact; its discharge sits with P-W6's
        O-P-W1-a (`utextDiscAtP`, Q1's no-fault export) — after P-M8;
  §3  **THE EVENT STEP `evStep`**: LOCKSTEP off the exempt reads by `SbReplay.lockBlk` (the emission's
      block re-timed; `relpAgree`; the emission's blocks `CertZ6.emBlocks` at the walk fabric — a fabric
      member is the `devCnt`-th of `gfDev`, a contact-free block runs at any fabric), `SailX` otherwise;
  §4  **`walkRunProgP`** — the gated walk, choosing a non-fetch-blocked enabled target (`noStuckP` +
      `FetchProg`), runs to a FINISHED walk with the program invariant; **`memberOfCatProg`** adds P-W3's
      member facts (`SbOrd.memberOfRun`).

Spec: FAITHFUL (proof organisation over `SbCand`'s machine and the emission datum).  Named inputs (FAITHFUL
statements, WEAKER while named): `SailX`, `FetchProg`, and P-W3's `StateIfc`.  Lean-only helpers
`SbProg.*`.
-/
import Weak.SbOrdWalk

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Lbl SbWalk SbAgree SbReplay SbOrd

namespace SbProg

/-! # 1. The walk fabric -/

/-- The number of REALIZED fabric members. -/
def devCnt (dev : List Geid) (w : WS) : Nat := (dev.filter (fun e => decide (realized w e))).length

/-- A filter whose truth is "index below `m`" keeps exactly `m` elements. -/
theorem filterLenIdx {α : Type} (P : α → Prop) [DecidablePred P] :
    ∀ (L : List α) (m : Nat), m ≤ L.length →
      (∀ (i : Nat) (h : i < L.length), (P L[i] ↔ i < m)) →
      (L.filter (fun a => decide (P a))).length = m := by
  intro L
  induction L with
  | nil => intro m hm _; simp at hm ⊢; omega
  | cons a L ih =>
    intro m hm h
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    cases m with
    | zero =>
      have ha : ¬ P a := fun hp => absurd (h0.1 hp) (Nat.lt_irrefl 0)
      rw [List.filter_cons, if_neg (by simpa using ha)]
      exact ih 0 (Nat.zero_le _) (fun i hi => by
        have := h (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        rw [this]; omega)
    | succ m =>
      have ha : P a := h0.2 (Nat.succ_pos _)
      rw [List.filter_cons, if_pos (by simpa using ha), List.length_cons]
      congr 1
      exact ih m (by simp at hm; omega) (fun i hi => by
        have := h (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        rw [this]; omega)

/-- A landing realizes nothing. -/
theorem rowsLand (w : WS) (i k : Nat) : (nextI w (.land i k)).rows = w.rows := by
  simp only [nextI]
  split <;> rfl

theorem devCntLand (dev : List Geid) (w : WS) (i k : Nat) :
    devCnt dev (nextI w (.land i k)) = devCnt dev w := by
  unfold devCnt
  congr 1
  refine List.filter_congr (fun e _ => ?_)
  simp only [decide_eq_decide]
  unfold realized
  rw [rowsLand]

/-- A contact-free event keeps the count. -/
theorem devCntEvOut (dev : List Geid) (w : WS) (s : Estep) :
    (s.esAg, (w.rows s.esAg).length) ∉ dev → devCnt dev (nextI w (.ev s)) = devCnt dev w := by
  intro hn
  unfold devCnt
  congr 1
  refine List.filter_congr (fun d hd => ?_)
  have hne : d ≠ (s.esAg, (w.rows s.esAg).length) := fun h => hn (h ▸ hd)
  simp only [decide_eq_decide]
  rw [realizedEv]
  exact ⟨fun h => h.resolve_right hne, .inl⟩

/-- At an unrealized fabric member `dev[m]` whose predecessors are realized (`fabOk`), with the realized
members prefix-closed (`dvP`), the count is `m`; realizing it makes it `m + 1` (`Nodup`). -/
theorem devCntEvIn (dev : List Geid) (w : WS) (s : Estep) (m : Nat) (hnd : dev.Nodup)
    (hm : dev[m]? = some (s.esAg, (w.rows s.esAg).length))
    (hfab : ∀ d, before dev d (s.esAg, (w.rows s.esAg).length) → realized w d)
    (hdv : ∀ d d', before dev d d' → realized w d' → realized w d) :
    devCnt dev w = m ∧ devCnt dev (nextI w (.ev s)) = m + 1 := by
  have hml : m < dev.length := lookup_lt_Some hm
  have hem : dev[m] = (s.esAg, (w.rows s.esAg).length) := (List.getElem?_eq_some_iff.1 hm).2
  have hnr : ¬ realized w (s.esAg, (w.rows s.esAg).length) := by unfold realized; simp
  have hold : ∀ (i : Nat) (h : i < dev.length), (realized w dev[i] ↔ i < m) := by
    intro i hi
    constructor
    · intro hr
      refine Classical.byContradiction (fun hlt => ?_)
      rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hlt) with h | h
      · exact hnr (hdv _ _ ⟨m, i, hm, List.getElem?_eq_getElem hi, h⟩ hr)
      · subst h; rw [hem] at hr; exact hnr hr
    · intro hlt
      exact hfab _ ⟨i, m, List.getElem?_eq_getElem hi, hm, hlt⟩
  refine ⟨filterLenIdx _ dev m (Nat.le_of_lt hml) hold, filterLenIdx _ dev (m + 1) hml (fun i hi => ?_)⟩
  rw [realizedEv, hold i hi]
  constructor
  · rintro (h | h)
    · omega
    · have : dev[i] = dev[m] := by rw [h, hem]
      have := (List.getElem_inj hnd).1 this
      omega
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
    · exact .inl h
    · subst h; exact .inr hem

/-! # 2. The program invariant and the named inputs -/

/-- The reachable states of the gated walk (P-W3's `walkRunP` hypotheses' domain). -/
structure Reach (GF : Gfexec) (N : Nat) (img : Image) (X : Geid → Prop) (rdG : RdG) (S : St) : Prop where
  imgEq : S.c.img = img
  valid : validW SbPol.epoch S.c
  gated : gatedW GF.gfGd.gdG X rdG GF.gfDev S.c
  pinv : PInv N img GF.gfGd.gdG X GF.gfDev (cur S.c)

/-- **THE PROGRAM INVARIANT**: the program data (`SbWalk.ok`), every row's program state LOCKSTEP or
`TR`-TAINTED w.r.t. its emission at the row's count, and the walk fabric. -/
structure PrgInv (d0 : Efab) (fab : Nat → Efab) (dev : List Geid) (N : Nat) (D : Nat → CertZ7.EmData)
    (TR : CertZ9.HRel) (S : St) : Prop where
  ok : SbWalk.ok SbPol.epoch d0 S
  rel : ∀ x, x < N → ∃ pC, (S.pst S.c.its.length)[x]? = some pC ∧
    SilSiteStep.relS TR x ((cur S.c).rows x).length ((D x).f ((cur S.c).rows x).length) pC
  fab : S.dv S.c.its.length = fab (devCnt dev (cur S.c))

/-- **`SailX` — THE SAIL MEANING OF THE THREE-PC TAINT (NAMED; O-P-W2-a; REVISIT [OWN.124] for
`holding+0x12`)**: at a reachable state, from a `TR`-tainted program state, or from lockstep at an EXEMPT
read, given the member's label of the row's next GF event (an `SbCand` step, related to GF's label by
`lblRelX`, both words `exValV` at an exempt read) and text custody of the emission's star, the event is
contact-free and the row's program realizes the member's label, ending LOCKSTEP or `TR`.  Its instance is
the value/bit-aware `csync` of `SilSiteTaint.siteOk` (`ipRefTaint`, `SbHoldX`'s static facts); at
`TR := relTArm TT` (register `csync`) it is FALSE-suspect at the value-ruled branch (finding F11). -/
def SailX (GF : Gfexec) (N : Nat) (img : Image) (X : Geid → Prop) (rdG : RdG) (d0 : Efab)
    (fab : Nat → Efab) (D : Nat → CertZ7.EmData) (TR : CertZ9.HRel) : Prop :=
  ∀ (S : St) (x : Nat) (pC : Pexv6) (l lb : Lbl),
    Reach GF N img X rdG S → PrgInv d0 fab GF.gfDev N D TR S → x < N →
    (S.pst S.c.its.length)[x]? = some pC →
    gxLbl GF.gfGd.gdG (hd (cur S.c) x) = some l →
    lblRelX (X (hd (cur S.c) x)) l lb →
    (X (hd (cur S.c) x) → exValL x l ∧ exValL x lb) →
    SbCand.stepE (cur S.c).σ x lb (SbCand.nextE (cur S.c).σ x lb) →
    (TR x ((cur S.c).rows x).length ((D x).f ((cur S.c).rows x).length) pC ∨
      (pC = (D x).f ((cur S.c).rows x).length ∧ X (hd (cur S.c) x))) →
    fetchOk (cur S.c) ((D x).g ((cur S.c).rows x).length) →
    hd (cur S.c) x ∉ GF.gfDev ∧
    ∃ pC', evData (cur S.c) x lb pC (S.dv S.c.its.length) pC' (S.dv S.c.its.length) ∧
      SilSiteStep.relS TR x (((cur S.c).rows x).length + 1)
        ((D x).f (((cur S.c).rows x).length + 1)) pC'

/-- Row `x`'s next block is FETCH-READY: its emission star's fetches are servable at the landed log. -/
def fetchReady (D : Nat → CertZ7.EmData) (w : WS) (x : Nat) : Prop :=
  fetchOk w ((D x).g (w.rows x).length)

/-- **`FetchProg` — FETCH PROGRESS (NAMED; finding F-6m-1)**: at a reachable state, if an enabled genuine
head is not fetch-ready, some enabled genuine target is a landing or a fetch-ready head. -/
def FetchProg (GF : Gfexec) (N : Nat) (img : Image) (X : Geid → Prop) (rdG : RdG) (d0 : Efab)
    (fab : Nat → Efab) (D : Nat → CertZ7.EmData) (TR : CertZ9.HRel) : Prop :=
  ∀ (S : St) (x : Nat), Reach GF N img X rdG S → PrgInv d0 fab GF.gfDev N D TR S →
    validT N GF.gfGd.gdG (cur S.c) (.hd x) →
    enb SbPol.epoch GF.gfGd.gdG X rdG GF.gfDev (cur S.c) (.hd x) → ¬ fetchReady D (cur S.c) x →
    ∃ T, validT N GF.gfGd.gdG (cur S.c) T ∧ enb SbPol.epoch GF.gfGd.gdG X rdG GF.gfDev (cur S.c) T ∧
      ∀ y, T = .hd y → fetchReady D (cur S.c) y

/-- `CertZ13.relT`'s tainted arm as a relation. -/
def relTArm (TT : Nat → Nat → List Nat) : CertZ9.HRel :=
  fun x n pE pC =>
    ∃ (cpu : CPU) (m1 : SailM Unit) (rs1 : RegFile) (fn1 : Option (Bool × Bool × Bool × Bool))
      (ib1 : Ibch) (m2 : SailM Unit) (rs2 : RegFile) (fn2 : Option (Bool × Bool × Bool × Bool))
      (ib2 : Ibch),
      pE = .PHart cpu m1 rs1 fn1 ib1 ∧ pC = .PHart cpu m2 rs2 fn2 ib2 ∧
      csync (TT x n) m1 rs1 fn1 ib1 m2 rs2 fn2 ib2

/-- **`CertZ13.relT` IS THE INSTANCE**: lockstep-or-`TR` at `TR := relTArm TT` is `CertZ13.relT TT`. -/
theorem relSRelT (TT : Nat → Nat → List Nat) (x n : Nat) (pE pC : Pexv6) :
    SilSiteStep.relS (relTArm TT) x n pE pC ↔ CertZ13.relT TT x n pE pC := by
  unfold SilSiteStep.relS CertZ13.relT relTArm
  exact ⟨fun h => h.elim (fun e => .inl e.symm) .inr, fun h => h.elim (fun e => .inl e.symm) .inr⟩

/-! # 3. The event step -/

/-- The read timestamps of a label. -/
def tsOfL : Lbl → List Nat
  | LLoad _ _ ts _ => ts
  | LRmw _ _ _ ts _ _ _ => ts
  | _ => []

/-- The member label of a lockstep step is GF's re-timed. -/
theorem setTsOfReidx (l lb : Lbl) : lblReidx l lb → SilSiteStep.setTs l (tsOfL lb) = lb := by
  intro h
  cases l with
  | LLoad aq base ts vs =>
    cases lb with
    | LLoad aq' base' ts' vs' =>
      obtain ⟨rfl, rfl, rfl, -⟩ := h; rfl
    | _ => exact absurd h (by simp [lblReidx])
  | LRmw aq rl base ts rvs wvs kc =>
    cases lb with
    | LRmw aq' rl' base' ts' rvs' wvs' kc' =>
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := h; rfl
    | _ => exact absurd h (by simp [lblReidx])
  | _ => have h' : lb = _ := h; subst h'; rfl

theorem tsOfLLoad (l lb : Lbl) : lblReidx l lb →
    ∀ aq base ts vs, l = .LLoad aq base ts vs → (tsOfL lb).length = ts.length := by
  intro h aq base ts vs he
  subst he
  cases lb with
  | LLoad aq' base' ts' vs' => exact h.2.2.2
  | _ => exact absurd h (by simp [lblReidx])

theorem tsOfLRmw (l lb : Lbl) : lblReidx l lb →
    ∀ aq rl base ts rvs wvs kc, l = .LRmw aq rl base ts rvs wvs kc → (tsOfL lb).length = ts.length := by
  intro h aq rl base ts rvs wvs kc he
  subst he
  cases lb with
  | LRmw aq' rl' base' ts' rvs' wvs' kc' => exact h.2.2.2.2.2.2
  | _ => exact absurd h (by simp [lblReidx])

theorem getDOf (rows : List (List Lbl)) (x : Nat) (row : List Lbl) :
    rows[x]? = some row → rows.getD x [] = row := by
  intro h; simp [List.getD, h]

/-- **THE EMISSION'S BLOCK AT THE WALK FABRIC**: at an enabled head `(x, n)` of a reachable state with
the walk fabric `fab (devCnt …)`, the emission's block starts at the walk's fabric and ends at the
fabric of the realized count after the event. -/
theorem emBlkAt (boot : Nat → Pexv6) (fab : Nat → Efab) (GF : Gfexec) (D : Nat → CertZ7.EmData)
    (hD : CertZ7.emDataOk boot fab GF D) (hnd : GF.gfDev.Nodup) (N : Nat) (img : Image)
    (X : Geid → Prop) (w : WS) (hP : PInv N img GF.gfGd.gdG X GF.gfDev w) (x : Nat) (l : Lbl)
    (hl : gxLbl GF.gfGd.gdG (hd w x) = some l) (hfo : fabOk GF.gfDev w (hd w x)) (lb : Lbl) :
    SilSiteStep.emBlk D GF.gfGd.gdG.gxProg x (w.rows x).length l (fab (devCnt GF.gfDev w))
      (fab (devCnt GF.gfDev (nextI w (.ev ⟨x, lb⟩)))) := by
  unfold gxLbl hd at hl
  cases hr : GF.gfGd.gdG.gxProg[x]? with
  | none => rw [hr] at hl; cases hl
  | some row =>
    rw [hr] at hl
    simp only [Option.bind_some] at hl
    have hgd := getDOf _ x row hr
    have hn : (w.rows x).length < row.length := lookup_lt_Some hl
    obtain ⟨em, -, hiff, hpin, -, -, hblk⟩ := hD x row hr
    unfold SilSiteStep.emBlk
    rw [hgd]
    by_cases hin : (x, (w.rows x).length) ∈ GF.gfDev
    · obtain ⟨m, hm⟩ := List.mem_iff_getElem?.1 hin
      obtain ⟨h1, h2⟩ := devCntEvIn GF.gfDev w ⟨x, lb⟩ m hnd hm (hfo hin) hP.dvP
      obtain ⟨hdi, hdo⟩ := hpin _ m hm
      rw [h1, h2, ← hdi, ← hdo]
      rcases hblk _ l hl with ⟨hfu, hb, -⟩ | ⟨hb, -⟩
      · exact .inl ⟨hfu, hb⟩
      · exact .inr hb
    · have htq : (D x).tq (w.rows x).length = false := by
        cases h : (D x).tq (w.rows x).length with
        | false => rfl
        | true => exact absurd ((hiff _ hn).2 (.inr (.inr h))) hin
      rw [devCntEvOut GF.gfDev w ⟨x, lb⟩ hin]
      rcases hblk _ l hl with ⟨hfu, -, hq⟩ | ⟨-, hq⟩
      · exact .inl ⟨hfu, hq htq _⟩
      · exact .inr (hq htq _)

/-- The validity of an appended item at the state before it. -/
theorem okIOfSnoc (c : CandW) (it : Item) : validW SbPol.epoch (snocC c it) → okI SbPol.epoch (cur c) it := by
  intro hv
  have h := hv c.its.length it (by show (c.its ++ [it])[c.its.length]? = some it; simp)
  rwa [stAtSnoc c it _ (Nat.le_refl _)] at h

/-- **THE EVENT STEP** — lockstep (`SbReplay.lockBlk`) off the exempt reads, `SailX` at tainted states and
exempt reads: the program invariant extends along an appended event of row `x`. -/
theorem evStep (GF : Gfexec) (N : Nat) (img : Image) (X : Geid → Prop) (rdG : RdG) (boot : Nat → Pexv6)
    (d0 : Efab) (fab : Nat → Efab) (D : Nat → CertZ7.EmData) (TR : CertZ9.HRel)
    (hD : CertZ7.emDataOk boot fab GF D) (hnd : GF.gfDev.Nodup) (hexG : ExValGF GF.gfGd.gdG X)
    (hsail : SailX GF N img X rdG d0 fab D TR)
    (S : St) (hR : Reach GF N img X rdG S) (hI : PrgInv d0 fab GF.gfDev N D TR S) (x : Nat) (hx : x < N)
    (s : Estep) (hs : s.esAg = x)
    (hv' : validW SbPol.epoch (snocC S.c (.ev s)))
    (hP' : PInv N img GF.gfGd.gdG X GF.gfDev (cur (snocC S.c (.ev s))))
    (he : enb SbPol.epoch GF.gfGd.gdG X rdG GF.gfDev (cur S.c) (.hd x))
    (hfr : fetchReady D (cur S.c) x) :
    ∃ pC' d', PrgInv d0 fab GF.gfDev N D TR (snocE S s pC' d') := by
  subst hs
  obtain ⟨l, hl, hfo, -⟩ := id he
  obtain ⟨pC, hpC, hrel⟩ := hI.rel s.esAg hx
  -- the member label, its relation, its exempt fact, its machine step
  have hrowsN : (cur (snocC S.c (.ev s))).rows s.esAg = (cur S.c).rows s.esAg ++ [s.esLb] := by
    rw [curSnoc, rowsEvEq, if_pos rfl]
  have hlbAt : ((cur (snocC S.c (.ev s))).rows s.esAg)[((cur S.c).rows s.esAg).length]? = some s.esLb := by
    rw [hrowsN]; simp
  obtain ⟨l0, hl0, hrx⟩ := hP'.pf.1 s.esAg ((cur S.c).rows s.esAg).length s.esLb hlbAt
  have hl0' : gxLbl GF.gfGd.gdG (hd (cur S.c) s.esAg) = some l0 := hl0
  rw [hl] at hl0'
  cases hl0'
  have hexl : X (hd (cur S.c) s.esAg) → exValL s.esAg s.esLb := fun hX => hP'.ex s.esAg ((cur S.c).rows s.esAg).length s.esLb hlbAt hX
  have hstep : SbCand.stepE (cur S.c).σ s.esAg s.esLb (SbCand.nextE (cur S.c).σ s.esAg s.esLb) := okIOfSnoc S.c _ hv'
  -- the post-state bookkeeping
  have hfin : ∀ (pC' : Pexv6) (d' : Efab),
      evData (cur S.c) s.esAg s.esLb pC (S.dv S.c.its.length) pC' d' →
      SilSiteStep.relS TR s.esAg (((cur S.c).rows s.esAg).length + 1) ((D s.esAg).f (((cur S.c).rows s.esAg).length + 1)) pC' →
      d' = fab (devCnt GF.gfDev (nextI (cur S.c) (.ev s))) →
      PrgInv d0 fab GF.gfDev N D TR (snocE S s pC' d') := by
    intro pC' d' hev hrel' hd'
    have hcur : cur (snocE S s pC' d').c = nextI (cur S.c) (.ev s) := curSnoc S.c (.ev s)
    have hlen' : (snocE S s pC' d').c.its.length = S.c.its.length + 1 := by simp [snocE, snocC]
    have hn' : ¬ S.c.its.length + 1 ≤ S.c.its.length := by omega
    refine ⟨okSnocE SbPol.epoch d0 S s pC pC' d' hI.ok hpC (okIOfSnoc S.c _ hv') hev, fun y hy => ?_, ?_⟩
    · rw [hlen', hcur]
      dsimp only [snocE]
      rw [if_neg hn', rowsEvEq]
      by_cases hys : y = s.esAg
      · subst hys
        rw [if_pos rfl, List.length_append, List.length_singleton]
        exact ⟨pC', List.getElem?_set_self (lookup_lt_Some hpC), hrel'⟩
      · rw [if_neg hys]
        obtain ⟨q, hq, hqr⟩ := hI.rel y hy
        exact ⟨q, by rw [List.getElem?_set_ne (Ne.symm hys)]; exact hq, hqr⟩
    · rw [hlen', hcur]
      dsimp only [snocE]
      rw [if_neg hn', hd']
  -- the arms
  by_cases hlock : pC = (D s.esAg).f ((cur S.c).rows s.esAg).length ∧ ¬ X (hd (cur S.c) s.esAg)
  · -- LOCKSTEP
    obtain ⟨hpe, hnX⟩ := hlock
    have hre : lblReidx l s.esLb := by
      rcases hrx with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hnX
    have hblk := emBlkAt boot fab GF D hD hnd N img X (cur S.c) hR.pinv s.esAg l hl hfo s.esLb
    have hr := relpAgree SbPol.epoch S.c GF.gfGd.gdG X s.esAg hR.valid hR.pinv.pf
    have hev := lockBlk (cur S.c) s.esAg D GF.gfGd.gdG.gxProg ((cur S.c).rows s.esAg).length l _ _ (tsOfL s.esLb) hr hblk hfr
      (tsOfLLoad l _ hre) (tsOfLRmw l _ hre)
    rw [setTsOfReidx l _ hre, ← hpe, ← hI.fab] at hev
    have hdv : devCnt GF.gfDev (nextI (cur S.c) (.ev ⟨s.esAg, s.esLb⟩)) = devCnt GF.gfDev (nextI (cur S.c) (.ev s)) := rfl
    exact ⟨_, _, hfin _ _ hev (.inl rfl) (by rw [hdv])⟩
  · -- TAINTED, or LOCKSTEP at an exempt read
    have harm : TR s.esAg ((cur S.c).rows s.esAg).length ((D s.esAg).f ((cur S.c).rows s.esAg).length) pC ∨ (pC = (D s.esAg).f ((cur S.c).rows s.esAg).length ∧ X (hd (cur S.c) s.esAg)) := by
      rcases hrel with h | h
      · exact .inr ⟨h, Classical.byContradiction (fun hn' => hlock ⟨h, hn'⟩)⟩
      · exact .inl h
    obtain ⟨hout, pC', hev, hrel'⟩ := hsail S s.esAg pC l s.esLb hR hI hx hpC hl hrx
      (fun hX => ⟨hexG _ l hX hl, hexl hX⟩) hstep harm hfr
    refine ⟨pC', _, hfin pC' _ hev hrel' ?_⟩
    rw [hI.fab, devCntEvOut GF.gfDev (cur S.c) s hout]

/-- The program invariant extends along an appended landing. -/
theorem landStep (d0 : Efab) (fab : Nat → Efab) (dev : List Geid) (N : Nat) (D : Nat → CertZ7.EmData)
    (TR : CertZ9.HRel) (S : St) (hI : PrgInv d0 fab dev N D TR S) (i k : Nat)
    (hv' : validW SbPol.epoch (snocC S.c (.land i k))) :
    PrgInv d0 fab dev N D TR (snocL S i k) := by
  have hcur : cur (snocL S i k).c = nextI (cur S.c) (.land i k) := curSnoc S.c (.land i k)
  have hlen' : (snocL S i k).c.its.length = S.c.its.length + 1 := by simp [snocL, snocC]
  have hn' : ¬ S.c.its.length + 1 ≤ S.c.its.length := by omega
  refine ⟨okSnocL SbPol.epoch d0 S i k hI.ok (okIOfSnoc S.c _ hv'), fun y hy => ?_, ?_⟩
  · rw [hlen', hcur, rowsLand]
    dsimp only [snocL]
    rw [if_neg hn']
    exact hI.rel y hy
  · rw [hlen', hcur, devCntLand]
    dsimp only [snocL]
    rw [if_neg hn']
    exact hI.fab

/-! # 4. The program-carrying walk -/

/-- The start: every row at its boot state, the boot fabric. -/
theorem prgStart (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (D : Nat → CertZ7.EmData) (TR : CertZ9.HRel) (N : Nat) (img : Image)
    (hD : CertZ7.emDataOk boot fab GF D) (hN : GF.gfGd.gdG.gxProg.length = N) (hf0 : fab 0 = d0) :
    PrgInv d0 fab GF.gfDev N D TR (start boot d0 N img) := by
  refine ⟨okStart SbPol.epoch boot d0 N img, fun x hx => ?_, ?_⟩
  · have hrow : ∃ row, GF.gfGd.gdG.gxProg[x]? = some row :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨row, hr⟩ := hrow
    obtain ⟨-, -, -, -, -, hf, -⟩ := hD x row hr
    refine ⟨boot x, ?_, .inl ?_⟩
    · simp [start, hx]
    · show boot x = (D x).f ((stAt ⟨img, []⟩ 0).rows x).length
      simp [stAt, init, hf]
  · show d0 = fab (devCnt GF.gfDev (stAt ⟨img, []⟩ 0))
    have : devCnt GF.gfDev (stAt ⟨img, []⟩ 0) = 0 := by
      unfold devCnt
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro e _
      simp [realized, stAt, init]
    rw [this, hf0]

theorem nonFinal {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid} {w : WS}
    (hP : PInv N img G X dev w)
    (hfin : ¬ ((∀ x, x < N → (w.rows x).length = (G.gxProg.getD x []).length) ∧ drained w)) :
    (∃ x, x < N ∧ (w.rows x).length < (G.gxProg.getD x []).length) ∨ (∃ i, w.pend i ≠ []) := by
  by_cases h1 : ∀ x, x < N → (w.rows x).length = (G.gxProg.getD x []).length
  · have h2 : ¬ drained w := fun h => hfin ⟨h1, h⟩
    obtain ⟨i, hi⟩ : ∃ i, w.pend i ≠ [] :=
      Classical.byContradiction (fun hn => h2 (fun i => Classical.byContradiction (fun h => hn ⟨i, h⟩)))
    exact .inr ⟨i, hi⟩
  · obtain ⟨x, hx, hne⟩ : ∃ x, x < N ∧ (w.rows x).length ≠ (G.gxProg.getD x []).length :=
      Classical.byContradiction (fun hn => h1 (fun x hx =>
        Classical.byContradiction (fun h => hn ⟨x, hx, h⟩)))
    exact .inl ⟨x, hx, by have := hP.len x; omega⟩

/-- **`walkRunProgP` — THE GATED WALK RUNS TO COMPLETION CARRYING ITS PROGRAMS**: given P-W3's global
hypotheses and per-state interfaces (`walkRunP`'s), a fitting emission datum, the GF exempt-value fact, and
the two named inputs `SailX` / `FetchProg`, a FINISHED gated walk exists (every row complete, every buffer
drained) with the program invariant — the program data `SbWalk.ok` and every row's program state
lockstep-or-`TR` with its emission's END state. -/
theorem walkRunProgP (GF : Gfexec) (N : Nat) (img : Image) (X : Geid → Prop) (rdG : RdG)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (D : Nat → CertZ7.EmData) (TR : CertZ9.HRel)
    (hW : WalkHyp GF N img X)
    (hS : ∀ c, validW SbPol.epoch c → gatedW GF.gfGd.gdG X rdG GF.gfDev c → c.img = img →
      PInv N img GF.gfGd.gdG X GF.gfDev (cur c) → StateIfc GF.gfGd.gdG X rdG GF.gfDev c)
    (hD : CertZ7.emDataOk boot fab GF D) (hf0 : fab 0 = d0) (hnd : GF.gfDev.Nodup)
    (hexG : ExValGF GF.gfGd.gdG X)
    (hsail : SailX GF N img X rdG d0 fab D TR) (hfp : FetchProg GF N img X rdG d0 fab D TR) :
    ∃ S, Reach GF N img X rdG S ∧ PrgInv d0 fab GF.gfDev N D TR S ∧
      (∀ x, x < N → ((cur S.c).rows x).length = (GF.gfGd.gdG.gxProg.getD x []).length) ∧
      drained (cur S.c) := by
  suffices H : ∀ k S, Reach GF N img X rdG S → PrgInv d0 fab GF.gfDev N D TR S →
      work N GF.gfGd.gdG (cur S.c) ≤ k →
      ∃ S', Reach GF N img X rdG S' ∧ PrgInv d0 fab GF.gfDev N D TR S' ∧
        (∀ x, x < N → ((cur S'.c).rows x).length = (GF.gfGd.gdG.gxProg.getD x []).length) ∧
        drained (cur S'.c) by
    exact H _ (start boot d0 N img)
      ⟨rfl, fun k it h => by simp [start] at h, gatedNil _ X rdG _ img, pinvInit N img _ X _⟩
      (prgStart boot d0 fab GF D TR N img hD hW.len hf0) (Nat.le_refl _)
  intro k
  induction k with
  | zero =>
    intro S hR hI hw
    by_cases hfin : (∀ x, x < N → ((cur S.c).rows x).length = (GF.gfGd.gdG.gxProg.getD x []).length) ∧
        drained (cur S.c)
    · exact ⟨S, hR, hI, hfin.1, hfin.2⟩
    · exfalso
      have hSI := hS S.c hR.valid hR.gated hR.imgEq hR.pinv
      obtain ⟨T, hT, he⟩ := noStuckP GF N img X rdG (cur S.c) hW.cat hW.io hW.wio hW.imgF hW.len hR.pinv
        hSI.mono hW.devSt hW.hart hSI.head (nonFinal hR.pinv hfin)
      have hW' : WalkHyp GF N S.c.img X := hR.imgEq ▸ hW
      have hP' : PInv N S.c.img GF.gfGd.gdG X GF.gfDev (cur S.c) := hR.imgEq ▸ hR.pinv
      obtain ⟨it, -, -, hlt, -⟩ := walkStepP GF N X rdG S.c hW' hR.valid hP' hSI T hT he
      omega
  | succ k ih =>
    intro S hR hI hw
    by_cases hfin : (∀ x, x < N → ((cur S.c).rows x).length = (GF.gfGd.gdG.gxProg.getD x []).length) ∧
        drained (cur S.c)
    · exact ⟨S, hR, hI, hfin.1, hfin.2⟩
    · have hSI := hS S.c hR.valid hR.gated hR.imgEq hR.pinv
      obtain ⟨T0, hT0, he0⟩ := noStuckP GF N img X rdG (cur S.c) hW.cat hW.io hW.wio hW.imgF hW.len
        hR.pinv hSI.mono hW.devSt hW.hart hSI.head (nonFinal hR.pinv hfin)
      -- a non-fetch-blocked enabled target
      obtain ⟨T, hT, he, hfr⟩ : ∃ T, validT N GF.gfGd.gdG (cur S.c) T ∧
          enb SbPol.epoch GF.gfGd.gdG X rdG GF.gfDev (cur S.c) T ∧
          ∀ y, T = .hd y → fetchReady D (cur S.c) y := by
        cases T0 with
        | ld i j => exact ⟨_, hT0, he0, fun y h => by cases h⟩
        | hd x =>
          by_cases hx : fetchReady D (cur S.c) x
          · exact ⟨_, hT0, he0, fun y h => by cases h; exact hx⟩
          · exact hfp S x hR hI hT0 he0 hx
      have hW' : WalkHyp GF N S.c.img X := hR.imgEq ▸ hW
      have hP0 : PInv N S.c.img GF.gfGd.gdG X GF.gfDev (cur S.c) := hR.imgEq ▸ hR.pinv
      obtain ⟨it, hv', hP', hlt, hit⟩ := walkStepP GF N X rdG S.c hW' hR.valid hP0 hSI T hT he
      have hP'' : PInv N img GF.gfGd.gdG X GF.gfDev (cur (snocC S.c it)) := hR.imgEq ▸ hP'
      have hg' : gatedW GF.gfGd.gdG X rdG GF.gfDev (snocC S.c it) :=
        gatedSnoc _ X rdG _ S.c it hR.gated (by rw [hit]; exact he)
      cases it with
      | land i j =>
        have hR' : Reach GF N img X rdG (snocL S i j) := ⟨hR.imgEq, hv', hg', hP''⟩
        exact ih (snocL S i j) hR' (landStep d0 fab GF.gfDev N D TR S hI i j hv') (by
          show work N GF.gfGd.gdG (cur (snocC S.c (.land i j))) ≤ k; omega)
      | ev s =>
        have hsx : T = .hd s.esAg := hit.symm
        subst hsx
        obtain ⟨hx, -⟩ := hT
        obtain ⟨pC', d', hI'⟩ := evStep GF N img X rdG boot d0 fab D TR hD hnd hexG hsail S hR hI
          s.esAg hx s rfl hv' hP'' he (hfr _ rfl)
        have hR' : Reach GF N img X rdG (snocE S s pC' d') := ⟨hR.imgEq, hv', hg', hP''⟩
        exact ih (snocE S s pC' d') hR' hI' (by
          show work N GF.gfGd.gdG (cur (snocC S.c (.ev s))) ≤ k; omega)

/-- **A COMPLETED, PROGRAM-CARRYING MEMBER** (`walkRunProgP` + P-W3's `memberOfRun`): the member facts of
`SbOrd.memberOfCat` and, on the same finished walk, the program invariant. -/
theorem memberOfCatProg (GF : Gfexec) (N : Nat) (img : Image) (X : Geid → Prop) (rdG : RdG)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (D : Nat → CertZ7.EmData) (TR : CertZ9.HRel)
    (hW : WalkHyp GF N img X)
    (hS : ∀ c, validW SbPol.epoch c → gatedW GF.gfGd.gdG X rdG GF.gfDev c → c.img = img →
      PInv N img GF.gfGd.gdG X GF.gfDev (cur c) → StateIfc GF.gfGd.gdG X rdG GF.gfDev c)
    (hD : CertZ7.emDataOk boot fab GF D) (hf0 : fab 0 = d0) (hnd : GF.gfDev.Nodup)
    (hexG : ExValGF GF.gfGd.gdG X)
    (hsail : SailX GF N img X rdG d0 fab D TR) (hfp : FetchProg GF N img X rdG d0 fab D TR) :
    ∃ S, S.c.img = img ∧ validW SbPol.epoch S.c ∧ drained (cur S.c) ∧
      PrgInv d0 fab GF.gfDev N D TR S ∧
      gwf (memberP N S.c) ∧ logOf (memberP N S.c) (logP S.c) ∧
      CertZ18.rmwLatest (memberP N S.c) (logP S.c) ∧ agreeX GF.gfGd.gdG (memberP N S.c) X ∧
      CertZ24.agreeW4 GF.gfGd.gdG (memberP N S.c) (fun _ => False) ∧
      (∀ L, CertZ18.agreeW3 GF.gfGd.gdG (memberP N S.c) L) ∧
      valEqX GF.gfGd.gdG (memberP N S.c) X := by
  obtain ⟨S, hR, hI, hfin, hdr⟩ :=
    walkRunProgP GF N img X rdG boot d0 fab D TR hW hS hD hf0 hnd hexG hsail hfp
  have hP0 : PInv N S.c.img GF.gfGd.gdG X GF.gfDev (cur S.c) := hR.imgEq ▸ hR.pinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := memberOfRun SbPol.epoch N GF.gfGd.gdG X GF.gfDev S.c hR.valid
    hW.cat.wf (hW.imgEq.trans hR.imgEq.symm) hW.len hP0 hfin hdr
  exact ⟨S, hR.imgEq, hR.valid, hdr, hI, h1, h2, h3, h4, h5, h6, h7 hexG⟩

end SbProg

end Weak
