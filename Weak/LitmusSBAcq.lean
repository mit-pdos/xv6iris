/-
Weak: **allocproc R44 finding F44-1, mechanically checked — a release store buffered past the
hart's next `amoswap.w.aq`** (`notes/weak-allocproc-plan-review-R44.md` PART 0, §0.1–0.3).
Lean-only, no Rocq twin.  A LEAF: nothing imports this file.

## Spec first (riscv.cat / RVWMO; the faithful model `rvwmoCatConsistent`, `Weak/AxGraphCat.lean`)

xv6's release is `fence rw,w; sw zero` (`LockFacts.relFenceBits`, `LockFacts.relStoreWord`), its
acquire `amoswap.w.aq` with `.rl` clear (`LockFacts.acqWord`), and no fence of the image lies between
a release store and the hart's next acquire (`LockFacts.fenceCensus`).  riscv.cat orders a plain store
`w` before a po-later access `x` to ANOTHER address only by rule 4 (a fence with `pw` and the matching
successor bit between them), rule 6 (`x` carries `.rl`), rule 7 (both RCsc) or a dependency rule (whose
source is a READ).  Rule 5 `[AQ];po;[M]` orders the acquire's SUCCESSORS after it, not its
predecessors.  So `w` may sit in gmo after the hart's next `amoswap.w.aq` and after the reads that
follow it.  The tree's cat model omits rules 6 and 8 (`AxGraphCat` header); both are VACUOUS on the
two witnesses below (no `.rl` bit: `SBAcq.l1NoRl`/`SBAcq.l2NoRl`; the alphabet has no LR/SC), so the
ALLOWED verdicts are riscv.cat's.  The FORBIDDEN verdicts need only rules 1/4/5/7 + load value, so
they hold a fortiori under riscv.cat.

## What is proved

* §1 generic, off load value: `SBAcq.rfLt` (an external rf-source is gmo-before its read),
  `SBAcq.frLt` (a read is gmo-before every same-byte write that is gmo-after its source).  All the
  ∀-gmo theorems assume only `SBAcq.Ok6` (gwf + the six program-order arms + load value), implied by
  BOTH the untagged and the tagged model (`SBAcq.ok6OfCat`, `SBAcq.ok6OfCatT`).
* §2 LITMUS 1 (2 harts, nested locks).  `SBAcq.l1Cat`/`SBAcq.l1CatT`: CONSISTENT (witness gmo;
  `SBAcq.l1Buffered`: both release stores are gmo-after the hart's next acquire AND its failed spin).
  `SBAcq.l1NeedsBuffer`/`SBAcq.l1NeedsBufferAcq`: in EVERY gmo with this outcome at least one release
  store is gmo-after its hart's failed `amoswap` (resp. next acquire).  Companions — the same outcome
  is FORBIDDEN once the store is ordered before the acquire: `SBAcq.l1FenceNo` (a `fence rw,rw` after
  the release store, rule 4), `SBAcq.l1RcscNo` (an RCsc `amoswap.w.rl` release, rule 7).
* §3 LITMUS 2 (3 harts, release/acquire hand-off).  `SBAcq.l2Cat`/`SBAcq.l2CatT`: CONSISTENT;
  `SBAcq.l2NeedsBuffer` (hart 2's release store of `z` is gmo-after hart 1's read of `d`, in every gmo);
  `SBAcq.l2FenceNo` (forbidden with a `fence rw,rw` after the store).  REACHABILITY CAVEAT
  `SBAcq.l2cNo`: if hart 1's read of `d` is xv6's spin in `acquire(d)`, hart 1 can release `y` only
  after its `amoswap.aq` on `d` succeeds, i.e. reads hart 2's `release(d)` store — whose `fence rw,w`
  drains the buffered store: FORBIDDEN.  So Litmus 2 is xv6-reachable only with an UNSYNCHRONIZED read
  of a store hart 2 makes after `release(z)` and before its next release fence (e.g. `procdump`'s
  unlocked `p->state` read under `cons.lock`), not with the `holding`/`amoswap` read R44 names.
* §4 THE LOCKSTEP TSO-STORE-LOG MEMBER (`SBAcq.TsoCore`: one position `p` per event, each hart's events
  in program order, every store appended at its step; a read's source already appended; a read at
  view `fl r` sees no plain store appended after its source and at or before `fl r`), with MachCSL's
  acquire floor `SBAcq.floorTop` (δ1: `tv := top` at a successful `.aq` AMO) or the weaker source floor
  `SBAcq.floorSrc` (a "δ1′": the floor only reaches the acquire's rf-source).
  `SBAcq.l1NoMember`: no member of Litmus 1 under the top floor (the cycle
  `p w′ < p A1 ≤ fl F1 < p w″ < p A2 ≤ fl F2 < p w′`).  `SBAcq.l2NoMember`: no member of Litmus 2
  under the SOURCE floor (`SBAcq.l2NoMemberTop` for the top floor).  Non-vacuity:
  `SBAcq.l1MemberSrc` — Litmus 1 HAS a member under the source floor (all of `TsoCore`, `floorSrc`
  and `srcLe`, checked by `decide +kernel`), so it is the top floor that kills Litmus 1, and Litmus 2
  is needed to kill every floor ≥ the acquire's source.

Spec: theorems about the existing model; nothing assumed.  Lean-only helpers `SBAcq.*`.
-/
import Weak.AxLitmus
import Weak.AxDeps

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl

/-! # 1. Generic facts -/

/-- What the ∀-gmo theorems use of the model: well-formedness, the six program-order arms
(rules 1, 2, 3, 4, 5, 7) and load value. -/
def SBAcq.Ok6 (G : Gexec) : Prop := gwf G ∧ gppoCat6Gmo G ∧ gloadValue G

theorem SBAcq.ok6OfCat (GD : Gdexec) : rvwmoCatConsistent GD → SBAcq.Ok6 GD.gdG :=
  fun h => ⟨h.1, fun e1 e2 hp => h.2.1 e1 e2 (Or.inl hp), h.2.2.1⟩

theorem SBAcq.ok6OfCatT (GT : GdexecT) : rvwmoCatConsistentT GT → SBAcq.Ok6 GT.gtG :=
  fun h => ⟨h.1, fun e1 e2 hp => h.2.1 e1 e2 (Or.inl hp), h.2.2.1⟩

theorem SBAcq.lblOf (G : Gexec) (prog : List (List Lbl)) (hP : G.gxProg = prog) (i k : Nat) :
    gxLbl G (i, k) = (prog[i]?).bind (fun p => p[k]?) := by
  simp only [gxLbl, hP]

theorem SBAcq.rdGmem (G : Gexec) (r : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    greadsByte G r a t v → gmem G r := by
  rintro ⟨l, base, ts, vs, j, hl, hrd, _⟩
  refine ⟨l, hl, ?_⟩
  cases l <;> simp_all [lbRd, lbIsMem, lbIsR]

/-- An EXTERNAL rf-source is gmo-before its read (load value: visible = gmo-before ∨ po-before). -/
theorem SBAcq.rfLt (G : Gexec) (r w : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    gloadValue G → greadsByte G r a t v → gwriteAt G t = some w → w.1 ≠ r.1 → gmoLt G w r := by
  intro hlv hr hw hne
  cases t with
  | zero => simp [gwriteAt] at hw
  | succ i =>
    obtain ⟨⟨w', hw', _, hvis⟩, _⟩ := hlv _ _ _ _ hr
    rw [hw, Option.some.injEq] at hw'
    subst hw'
    rcases hvis with h | ⟨hag, _⟩
    · exact h
    · exact absurd hag hne

/-- FROM-READS: a read is gmo-before every same-byte write gmo-after its source. -/
theorem SBAcq.frLt (G : Gexec) (r w w' : Geid) (a : Int) (t : Nat) (v v' : BitVec 8) :
    gwf G → gloadValue G → greadsByte G r a t v → gwriteAt G t = some w →
    gwritesByte G w' a v' → gmoLt G w w' → r ≠ w' → gmoLt G r w' := by
  intro hwf hlv hr hw hw' hww hne
  have hrm : r ∈ G.gxGmo := gwfMemGmo G r hwf (SBAcq.rdGmem G r a t v hr)
  rcases gmoLtTotal G r w' hwf.1 hrm hww.2.1 hne with h | h
  · exact h
  · exfalso
    have hmax := (hlv _ _ _ _ hr).2 w' v' hw' (Or.inl h)
    obtain ⟨hwin, hwix⟩ := gwriteAtInv G t w hwf.1 hw
    have hw'in : w' ∈ gwrites G :=
      (gwritesElemOf G w').2 ⟨hww.2.1, WeakRvwmoGraph.gwritesByteGisW G w' a v' hw'⟩
    have hlt := (gwixGposLt G w w' hwf.1 hwin hw'in).2 hww.2.2
    omega

/-! ## Label-level builders -/

theorem SBAcq.rdLd (G : Gexec) (e : Geid) (aq : Bool) (base : Int) (t : Nat) (v : BitVec 8) :
    gxLbl G e = some (LLoad aq base [t] [v]) → greadsByte G e base t v :=
  fun h => ⟨_, base, [t], [v], 0, h, rfl, rfl, rfl, by simp [accAddr]⟩

theorem SBAcq.rdRmw (G : Gexec) (e : Geid) (aq rl : Bool) (base : Int) (t : Nat) (rv : BitVec 8)
    (wvs : List (BitVec 8)) (k : WmClass) :
    gxLbl G e = some (LRmw aq rl base [t] [rv] wvs k) → greadsByte G e base t rv :=
  fun h => ⟨_, base, [t], [rv], 0, h, rfl, rfl, rfl, by simp [accAddr]⟩

theorem SBAcq.wrSt (G : Gexec) (e : Geid) (rl : Bool) (base : Int) (v : BitVec 8) (k : WmClass) :
    gxLbl G e = some (LStore rl base [v] k) → gwritesByte G e base v :=
  fun h => ⟨_, base, [v], 0, h, rfl, rfl, by simp [accAddr]⟩

theorem SBAcq.wrRmw (G : Gexec) (e : Geid) (aq rl : Bool) (base : Int) (ts : List Nat)
    (rvs : List (BitVec 8)) (v : BitVec 8) (k : WmClass) :
    gxLbl G e = some (LRmw aq rl base ts rvs [v] k) → gwritesByte G e base v :=
  fun h => ⟨_, base, [v], 0, h, rfl, rfl, by simp [accAddr]⟩

theorem SBAcq.gpoOf (G : Gexec) (e1 e2 : Geid) (l1 l2 : Lbl) :
    gxLbl G e1 = some l1 → gxLbl G e2 = some l2 → e1.1 = e2.1 → e1.2 < e2.2 →
    WeakRvwmoGraph.gpo G e1 e2 :=
  fun h1 h2 ha hk => ⟨ha, hk, by rw [h1]; rfl, by rw [h2]; rfl⟩

/-- RULE 5 edge `[AQ];po;[M]`, gmo-forward. -/
theorem SBAcq.acqLt (G : Gexec) (e1 e2 : Geid) (l1 l2 : Lbl) :
    gppoCat6Gmo G → gxLbl G e1 = some l1 → gxLbl G e2 = some l2 → e1.1 = e2.1 → e1.2 < e2.2 →
    lbIsR l1 = true → lbAq l1 = true → lbIsMem l2 = true → gmoLt G e1 e2 := by
  intro hp h1 h2 ha hk hr haq hm
  exact hp e1 e2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨SBAcq.gpoOf G e1 e2 l1 l2 h1 h2 ha hk, ⟨l1, h1, hr⟩, ⟨l1, h1, haq⟩, ⟨l2, h2, hm⟩⟩)))))

/-- RULE 4 edge (a fence with predecessor bit for `e1`'s kind, successor bit for `e2`'s). -/
theorem SBAcq.fenceLt (G : Gexec) (e1 e2 : Geid) (l1 l2 : Lbl) (kf : Nat) (pr pw sr sw : Bool) :
    gppoCat6Gmo G → gxLbl G e1 = some l1 → gxLbl G e2 = some l2 → e1.1 = e2.1 →
    e1.2 < kf → kf < e2.2 → gxLbl G (e1.1, kf) = some (LFence pr pw sr sw) →
    ((lbIsR l1 && pr) || (lbIsW l1 && pw)) = true →
    ((lbIsR l2 && sr) || (lbIsW l2 && sw)) = true → gmoLt G e1 e2 := by
  intro hp h1 h2 ha hk1 hk2 hf hpr hsc
  refine hp e1 e2 (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨pr, pw, sr, sw, ⟨ha, by omega, kf, hk1, hk2, hf⟩, ?_, ?_⟩))))
  · simp only [Bool.or_eq_true, Bool.and_eq_true] at hpr
    rcases hpr with ⟨h, h'⟩ | ⟨h, h'⟩
    · exact Or.inl ⟨⟨l1, h1, h⟩, h'⟩
    · exact Or.inr ⟨⟨l1, h1, h⟩, h'⟩
  · simp only [Bool.or_eq_true, Bool.and_eq_true] at hsc
    rcases hsc with ⟨h, h'⟩ | ⟨h, h'⟩
    · exact Or.inl ⟨⟨l2, h2, h⟩, h'⟩
    · exact Or.inr ⟨⟨l2, h2, h⟩, h'⟩

/-- RULE 7 edge `[RCsc];po;[RCsc]`. -/
theorem SBAcq.rcscLt (G : Gexec) (e1 e2 : Geid) (l1 l2 : Lbl) :
    gppoCat6Gmo G → gxLbl G e1 = some l1 → gxLbl G e2 = some l2 → e1.1 = e2.1 → e1.2 < e2.2 →
    lbRcsc l1 = true → lbRcsc l2 = true → gmoLt G e1 e2 := by
  intro hp h1 h2 ha hk hr1 hr2
  exact hp e1 e2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨SBAcq.gpoOf G e1 e2 l1 l2 h1 h2 ha hk, ⟨l1, h1, hr1⟩, ⟨l2, h2, hr2⟩⟩)))))

/-! # 2. LITMUS 1 — two harts, nested locks

R44's hart 1 is hart 0 here, its hart 2 is hart 1.  Bytes (each lock's `locked` byte; the all-zero
image = every lock free): `b` = 0, `c` = 1, `d` = 2, `e` = 3.  Hart 0: `acquire(b)` … `release(b)`
[`w′` = (0,2)]; `acquire(e)` [`A1` = (0,3), succeeds]; `acquire(d)`: `holding+0x0` reads `d.locked = 1`
[`r1` = (0,4)] and the `amoswap.w.aq` fails [`F1` = (0,5)].  Hart 1 symmetric with `d`, `c`, `b`.
`tb`/`td`: the write index the stale reads of `b`/`d` name (the outcome: they read the OTHER hart's
acquire, `(0,0)` resp. `(1,0)`). -/

def SBAcq.l1Prog (tb td : Nat) : List (List Lbl) :=
  [[LRmw true false 0 [0] [b0] [b1] .WCexcl,
    LFence true true false true,
    LStore false 0 [b0] .WCplain,
    LRmw true false 3 [0] [b0] [b1] .WCexcl,
    LLoad false 2 [td] [b1],
    LRmw true false 2 [td] [b1] [b1] .WCexcl],
   [LRmw true false 2 [0] [b0] [b1] .WCexcl,
    LFence true true false true,
    LStore false 2 [b0] .WCplain,
    LRmw true false 1 [0] [b0] [b1] .WCexcl,
    LLoad false 0 [tb] [b1],
    LRmw true false 0 [tb] [b1] [b1] .WCexcl]]

/-- The witness gmo: R44's `A_b1 A_d2 A1 A2 r1 r2 F1 F2 w′ w″` — both release stores LAST. -/
def SBAcq.l1Gmo : List Geid :=
  [(0, 0), (1, 0), (0, 3), (1, 3), (0, 4), (1, 4), (0, 5), (1, 5), (0, 2), (1, 2)]

def SBAcq.l1 : Gdexec := AxLitmus.mkgd (SBAcq.l1Prog 1 2) SBAcq.l1Gmo []

/-- **LITMUS 1 IS RVWMO-CONSISTENT** (the faithful cat model). -/
theorem SBAcq.l1Cat : rvwmoCatConsistent SBAcq.l1 := catConsistentBSound _ (by decide +kernel)

/-- The tagged model, with the spin loops' control dependencies (each `bnez` on an AMO / `holding`
result into every po-later store). -/
def SBAcq.l1Deps : List Tdep :=
  [(((0, 0), (0, 2)), Dtag.DTctrl), (((0, 0), (0, 3)), Dtag.DTctrl),
   (((0, 3), (0, 5)), Dtag.DTctrl), (((0, 4), (0, 5)), Dtag.DTctrl),
   (((1, 0), (1, 2)), Dtag.DTctrl), (((1, 0), (1, 3)), Dtag.DTctrl),
   (((1, 3), (1, 5)), Dtag.DTctrl), (((1, 4), (1, 5)), Dtag.DTctrl)]

def SBAcq.l1T : GdexecT := mkgt (SBAcq.l1Prog 1 2) SBAcq.l1Gmo SBAcq.l1Deps

theorem SBAcq.l1CatT : rvwmoCatConsistentT SBAcq.l1T := catTConsistentBSound _ (by decide +kernel)

/-- The outcome's rf: hart 0's stale reads of `d` name hart 1's acquire `(1,0)`, hart 1's of `b`
hart 0's acquire `(0,0)`. -/
theorem SBAcq.l1Rf : gwriteAt SBAcq.l1.gdG 2 = some (1, 0) ∧ gwriteAt SBAcq.l1.gdG 1 = some (0, 0) := by
  decide +kernel

/-- In the witness each release store is gmo-AFTER its hart's next acquire and failed spin. -/
theorem SBAcq.l1Buffered :
    gmoLt SBAcq.l1.gdG (0, 3) (0, 2) ∧ gmoLt SBAcq.l1.gdG (0, 5) (0, 2) ∧
    gmoLt SBAcq.l1.gdG (1, 3) (1, 2) ∧ gmoLt SBAcq.l1.gdG (1, 5) (1, 2) :=
  ⟨(gmoLtBSpec _ _ _).1 (by decide +kernel), (gmoLtBSpec _ _ _).1 (by decide +kernel),
   (gmoLtBSpec _ _ _).1 (by decide +kernel), (gmoLtBSpec _ _ _).1 (by decide +kernel)⟩

/-- Rules 6 and 8 (omitted by the tree's model) are vacuous here: no `.rl` bit. -/
theorem SBAcq.l1NoRl : (SBAcq.l1Prog 1 2).flatten.all (fun l => !lbRl l) = true := by decide +kernel

/-- THE LITMUS-1 CYCLE on any graph: each failed spin reads the OTHER hart's acquire (`F1` reads
`Ad`, `F2` reads `Ab`), so it is gmo-before that hart's release store (`frLt`); if each release store
were also gmo-before its OWN hart's failed spin, gmo would cycle `wb < F1 < wd < F2 < wb`. -/
theorem SBAcq.l1Core (G : Gexec) (hwf : gwf G) (hlv : gloadValue G)
    (b d : Int) (Ab Ad wb wd F1 F2 : Geid) (tb td : Nat) (vb vd ub ud : BitVec 8)
    (hF1 : greadsByte G F1 d td vd) (hs1 : gwriteAt G td = some Ad)
    (hwd : gwritesByte G wd d ud) (hAd : gmoLt G Ad wd) (hn1 : F1 ≠ wd)
    (hF2 : greadsByte G F2 b tb vb) (hs2 : gwriteAt G tb = some Ab)
    (hwb : gwritesByte G wb b ub) (hAb : gmoLt G Ab wb) (hn2 : F2 ≠ wb)
    (h1 : gmoLt G wb F1) (h2 : gmoLt G wd F2) : False := by
  have k1 := SBAcq.frLt G F1 Ad wd d td vd ud hwf hlv hF1 hs1 hwd hAd hn1
  have k2 := SBAcq.frLt G F2 Ab wb b tb vb ub hwf hlv hF2 hs2 hwb hAb hn2
  exact gmoLtIrrefl G wb
    (gmoLtTrans _ _ _ _ h1 (gmoLtTrans _ _ _ _ k1 (gmoLtTrans _ _ _ _ h2 k2)))

/-- **THE BUFFERING IS NECESSARY**: in EVERY gmo (any image, any deps) of Litmus 1's program with
its outcome's rf, at least one release store is gmo-after its own hart's failed spin. -/
theorem SBAcq.l1NeedsBuffer (G : Gexec) (tb td : Nat) (hP : G.gxProg = SBAcq.l1Prog tb td)
    (hok : SBAcq.Ok6 G) (hs1 : gwriteAt G td = some (1, 0)) (hs2 : gwriteAt G tb = some (0, 0)) :
    ¬ (gmoLt G (0, 2) (0, 5) ∧ gmoLt G (1, 2) (1, 5)) := by
  rintro ⟨h1, h2⟩
  obtain ⟨hwf, hp, hlv⟩ := hok
  have L00 : gxLbl G (0, 0) = some (LRmw true false 0 [0] [b0] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 0 0).trans rfl
  have L02 : gxLbl G (0, 2) = some (LStore false 0 [b0] .WCplain) :=
    (SBAcq.lblOf G _ hP 0 2).trans rfl
  have L05 : gxLbl G (0, 5) = some (LRmw true false 2 [td] [b1] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 0 5).trans rfl
  have L10 : gxLbl G (1, 0) = some (LRmw true false 2 [0] [b0] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 1 0).trans rfl
  have L12 : gxLbl G (1, 2) = some (LStore false 2 [b0] .WCplain) :=
    (SBAcq.lblOf G _ hP 1 2).trans rfl
  have L15 : gxLbl G (1, 5) = some (LRmw true false 0 [tb] [b1] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 1 5).trans rfl
  exact SBAcq.l1Core G hwf hlv 0 2 (0, 0) (1, 0) (0, 2) (1, 2) (0, 5) (1, 5) tb td b1 b1 b0 b0
    (SBAcq.rdRmw G _ _ _ _ _ _ _ _ L05) hs1 (SBAcq.wrSt G _ _ _ _ _ L12)
    (SBAcq.acqLt G _ _ _ _ hp L10 L12 rfl (by decide) rfl rfl rfl) (by decide)
    (SBAcq.rdRmw G _ _ _ _ _ _ _ _ L15) hs2 (SBAcq.wrSt G _ _ _ _ _ L02)
    (SBAcq.acqLt G _ _ _ _ hp L00 L02 rfl (by decide) rfl rfl rfl) (by decide)
    h1 h2

/-- … hence at least one release store is gmo-after its hart's NEXT ACQUIRE (`A1`/`A2`), which
rule 5 orders before the failed spin. -/
theorem SBAcq.l1NeedsBufferAcq (G : Gexec) (tb td : Nat) (hP : G.gxProg = SBAcq.l1Prog tb td)
    (hok : SBAcq.Ok6 G) (hs1 : gwriteAt G td = some (1, 0)) (hs2 : gwriteAt G tb = some (0, 0)) :
    ¬ (gmoLt G (0, 2) (0, 3) ∧ gmoLt G (1, 2) (1, 3)) := by
  rintro ⟨h1, h2⟩
  have L03 : gxLbl G (0, 3) = some (LRmw true false 3 [0] [b0] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 0 3).trans rfl
  have L05 : gxLbl G (0, 5) = some (LRmw true false 2 [td] [b1] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 0 5).trans rfl
  have L13 : gxLbl G (1, 3) = some (LRmw true false 1 [0] [b0] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 1 3).trans rfl
  have L15 : gxLbl G (1, 5) = some (LRmw true false 0 [tb] [b1] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 1 5).trans rfl
  exact SBAcq.l1NeedsBuffer G tb td hP hok hs1 hs2
    ⟨gmoLtTrans _ _ _ _ h1 (SBAcq.acqLt G _ _ _ _ hok.2.1 L03 L05 rfl (by decide) rfl rfl rfl),
     gmoLtTrans _ _ _ _ h2 (SBAcq.acqLt G _ _ _ _ hok.2.1 L13 L15 rfl (by decide) rfl rfl rfl)⟩

/-- Companion (a): a `fence rw,rw` right after each release store (indices: the acquire moves to
`(i,4)`, the failed spin to `(i,6)`). -/
def SBAcq.l1fProg (tb td : Nat) : List (List Lbl) :=
  [[LRmw true false 0 [0] [b0] [b1] .WCexcl,
    LFence true true false true,
    LStore false 0 [b0] .WCplain,
    LFence true true true true,
    LRmw true false 3 [0] [b0] [b1] .WCexcl,
    LLoad false 2 [td] [b1],
    LRmw true false 2 [td] [b1] [b1] .WCexcl],
   [LRmw true false 2 [0] [b0] [b1] .WCexcl,
    LFence true true false true,
    LStore false 2 [b0] .WCplain,
    LFence true true true true,
    LRmw true false 1 [0] [b0] [b1] .WCexcl,
    LLoad false 0 [tb] [b1],
    LRmw true false 0 [tb] [b1] [b1] .WCexcl]]

/-- **COMPANION (a): ordering the release store before the acquire (rule 4) FORBIDS the outcome**
— every gmo, any image, any deps. -/
theorem SBAcq.l1FenceNo (G : Gexec) (tb td : Nat) (hP : G.gxProg = SBAcq.l1fProg tb td)
    (hok : SBAcq.Ok6 G) (hs1 : gwriteAt G td = some (1, 0)) (hs2 : gwriteAt G tb = some (0, 0)) :
    False := by
  obtain ⟨hwf, hp, hlv⟩ := hok
  have L00 : gxLbl G (0, 0) = some (LRmw true false 0 [0] [b0] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 0 0).trans rfl
  have L02 : gxLbl G (0, 2) = some (LStore false 0 [b0] .WCplain) :=
    (SBAcq.lblOf G _ hP 0 2).trans rfl
  have L03 : gxLbl G (0, 3) = some (LFence true true true true) :=
    (SBAcq.lblOf G _ hP 0 3).trans rfl
  have L06 : gxLbl G (0, 6) = some (LRmw true false 2 [td] [b1] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 0 6).trans rfl
  have L10 : gxLbl G (1, 0) = some (LRmw true false 2 [0] [b0] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 1 0).trans rfl
  have L12 : gxLbl G (1, 2) = some (LStore false 2 [b0] .WCplain) :=
    (SBAcq.lblOf G _ hP 1 2).trans rfl
  have L13 : gxLbl G (1, 3) = some (LFence true true true true) :=
    (SBAcq.lblOf G _ hP 1 3).trans rfl
  have L16 : gxLbl G (1, 6) = some (LRmw true false 0 [tb] [b1] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 1 6).trans rfl
  exact SBAcq.l1Core G hwf hlv 0 2 (0, 0) (1, 0) (0, 2) (1, 2) (0, 6) (1, 6) tb td b1 b1 b0 b0
    (SBAcq.rdRmw G _ _ _ _ _ _ _ _ L06) hs1 (SBAcq.wrSt G _ _ _ _ _ L12)
    (SBAcq.acqLt G _ _ _ _ hp L10 L12 rfl (by decide) rfl rfl rfl) (by decide)
    (SBAcq.rdRmw G _ _ _ _ _ _ _ _ L16) hs2 (SBAcq.wrSt G _ _ _ _ _ L02)
    (SBAcq.acqLt G _ _ _ _ hp L00 L02 rfl (by decide) rfl rfl rfl) (by decide)
    (SBAcq.fenceLt G _ _ _ _ 3 _ _ _ _ hp L02 L06 rfl (by decide) (by decide) L03 rfl rfl)
    (SBAcq.fenceLt G _ _ _ _ 3 _ _ _ _ hp L12 L16 rfl (by decide) (by decide) L13 rfl rfl)

/-- Companion (b): the release is an RCsc `amoswap.w.rl zero` (Linux-style); same indices as
Litmus 1.  `tw0`/`tw1`: whatever the release AMOs read. -/
def SBAcq.l1rProg (tb td tw0 tw1 : Nat) : List (List Lbl) :=
  [[LRmw true false 0 [0] [b0] [b1] .WCexcl,
    LFence true true false true,
    LRmw false true 0 [tw0] [b1] [b0] .WCexcl,
    LRmw true false 3 [0] [b0] [b1] .WCexcl,
    LLoad false 2 [td] [b1],
    LRmw true false 2 [td] [b1] [b1] .WCexcl],
   [LRmw true false 2 [0] [b0] [b1] .WCexcl,
    LFence true true false true,
    LRmw false true 2 [tw1] [b1] [b0] .WCexcl,
    LRmw true false 1 [0] [b0] [b1] .WCexcl,
    LLoad false 0 [tb] [b1],
    LRmw true false 0 [tb] [b1] [b1] .WCexcl]]

/-- **COMPANION (b): an RCsc release (rule 7 orders it before the `.aq` AMO) FORBIDS the outcome.** -/
theorem SBAcq.l1RcscNo (G : Gexec) (tb td tw0 tw1 : Nat)
    (hP : G.gxProg = SBAcq.l1rProg tb td tw0 tw1)
    (hok : SBAcq.Ok6 G) (hs1 : gwriteAt G td = some (1, 0)) (hs2 : gwriteAt G tb = some (0, 0)) :
    False := by
  obtain ⟨hwf, hp, hlv⟩ := hok
  have L00 : gxLbl G (0, 0) = some (LRmw true false 0 [0] [b0] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 0 0).trans rfl
  have L02 : gxLbl G (0, 2) = some (LRmw false true 0 [tw0] [b1] [b0] .WCexcl) :=
    (SBAcq.lblOf G _ hP 0 2).trans rfl
  have L03 : gxLbl G (0, 3) = some (LRmw true false 3 [0] [b0] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 0 3).trans rfl
  have L05 : gxLbl G (0, 5) = some (LRmw true false 2 [td] [b1] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 0 5).trans rfl
  have L10 : gxLbl G (1, 0) = some (LRmw true false 2 [0] [b0] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 1 0).trans rfl
  have L12 : gxLbl G (1, 2) = some (LRmw false true 2 [tw1] [b1] [b0] .WCexcl) :=
    (SBAcq.lblOf G _ hP 1 2).trans rfl
  have L13 : gxLbl G (1, 3) = some (LRmw true false 1 [0] [b0] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 1 3).trans rfl
  have L15 : gxLbl G (1, 5) = some (LRmw true false 0 [tb] [b1] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 1 5).trans rfl
  exact SBAcq.l1Core G hwf hlv 0 2 (0, 0) (1, 0) (0, 2) (1, 2) (0, 5) (1, 5) tb td b1 b1 b0 b0
    (SBAcq.rdRmw G _ _ _ _ _ _ _ _ L05) hs1 (SBAcq.wrRmw G _ _ _ _ _ _ _ _ L12)
    (SBAcq.acqLt G _ _ _ _ hp L10 L12 rfl (by decide) rfl rfl rfl) (by decide)
    (SBAcq.rdRmw G _ _ _ _ _ _ _ _ L15) hs2 (SBAcq.wrRmw G _ _ _ _ _ _ _ _ L02)
    (SBAcq.acqLt G _ _ _ _ hp L00 L02 rfl (by decide) rfl rfl rfl) (by decide)
    (gmoLtTrans _ _ _ _ (SBAcq.rcscLt G _ _ _ _ hp L02 L03 rfl (by decide) rfl rfl)
      (SBAcq.acqLt G _ _ _ _ hp L03 L05 rfl (by decide) rfl rfl rfl))
    (gmoLtTrans _ _ _ _ (SBAcq.rcscLt G _ _ _ _ hp L12 L13 rfl (by decide) rfl rfl)
      (SBAcq.acqLt G _ _ _ _ hp L13 L15 rfl (by decide) rfl rfl rfl))

/-! # 3. LITMUS 2 — three harts, a release/acquire hand-off

Hart index = R44's hart number − 1.  Bytes: `z` = 0, `d` = 1, `y` = 2.  Hart 0 (R44 hart 1):
`acquire(y)` (0,0); reads `d = 1` [`r1` = (0,1)]; `release(y)` = fence rw,w (0,2) + `sw` [`R_y` = (0,3)].
Hart 1 (R44 hart 2): `acquire(z)` (1,0); `release(z)` = fence (1,1) + `sw` [`w‴` = (1,2)]; `acquire(d)`
[`A_d2` = (1,3)].  Hart 2 (R44 hart 3): `acquire(y)` [`A_y3` = (2,0), reads `R_y`]; `acquire(z)`:
`holding` reads `z = 1` stale [`r3` = (2,1)], the spin fails [(2,2)]. -/

def SBAcq.l2Prog (t1 ty t3 : Nat) : List (List Lbl) :=
  [[LRmw true false 2 [0] [b0] [b1] .WCexcl,
    LLoad false 1 [t1] [b1],
    LFence true true false true,
    LStore false 2 [b0] .WCplain],
   [LRmw true false 0 [0] [b0] [b1] .WCexcl,
    LFence true true false true,
    LStore false 0 [b0] .WCplain,
    LRmw true false 1 [0] [b0] [b1] .WCexcl],
   [LRmw true false 2 [ty] [b0] [b1] .WCexcl,
    LLoad false 0 [t3] [b1],
    LRmw true false 0 [t3] [b1] [b1] .WCexcl]]

/-- R44's witness `A_d2 < r1 < R_y < A_y3 < r3 < w‴` (with the acquires of `z`/`y` first). -/
def SBAcq.l2Gmo : List Geid :=
  [(1, 0), (0, 0), (1, 3), (0, 1), (0, 3), (2, 0), (2, 1), (2, 2), (1, 2)]

def SBAcq.l2 : Gdexec := AxLitmus.mkgd (SBAcq.l2Prog 3 4 1) SBAcq.l2Gmo []

/-- **LITMUS 2 IS RVWMO-CONSISTENT.** -/
theorem SBAcq.l2Cat : rvwmoCatConsistent SBAcq.l2 := catConsistentBSound _ (by decide +kernel)

def SBAcq.l2Deps : List Tdep :=
  [(((0, 0), (0, 3)), Dtag.DTctrl), (((0, 1), (0, 3)), Dtag.DTctrl),
   (((1, 0), (1, 2)), Dtag.DTctrl), (((1, 0), (1, 3)), Dtag.DTctrl),
   (((2, 0), (2, 2)), Dtag.DTctrl), (((2, 1), (2, 2)), Dtag.DTctrl)]

def SBAcq.l2T : GdexecT := mkgt (SBAcq.l2Prog 3 4 1) SBAcq.l2Gmo SBAcq.l2Deps

theorem SBAcq.l2CatT : rvwmoCatConsistentT SBAcq.l2T := catTConsistentBSound _ (by decide +kernel)

theorem SBAcq.l2Rf :
    gwriteAt SBAcq.l2.gdG 3 = some (1, 3) ∧ gwriteAt SBAcq.l2.gdG 4 = some (0, 3) ∧
    gwriteAt SBAcq.l2.gdG 1 = some (1, 0) := by
  decide +kernel

/-- In the witness hart 1's release store `w‴` is gmo-after its next acquire `A_d2`. -/
theorem SBAcq.l2Buffered : gmoLt SBAcq.l2.gdG (1, 3) (1, 2) := (gmoLtBSpec _ _ _).1 (by decide +kernel)

theorem SBAcq.l2NoRl : (SBAcq.l2Prog 3 4 1).flatten.all (fun l => !lbRl l) = true := by decide +kernel

/-- THE LITMUS-2 CYCLE on any graph: `r1 < R_y` (ordered), `R_y` the external source of `A_y`,
`A_y < r3` (ordered), `r3` reads `Az` stale against `w3` (gmo-after `Az`): then `w3 < r1` cycles. -/
theorem SBAcq.l2Core (G : Gexec) (hwf : gwf G) (hlv : gloadValue G)
    (Az w3 r1 Ry Ay r3 : Geid) (y z : Int) (ty t3 : Nat) (vy v3 u3 : BitVec 8)
    (hry : greadsByte G Ay y ty vy) (hsy : gwriteAt G ty = some Ry) (hhy : Ry.1 ≠ Ay.1)
    (hr3 : greadsByte G r3 z t3 v3) (hs3 : gwriteAt G t3 = some Az)
    (hw3 : gwritesByte G w3 z u3) (hAz : gmoLt G Az w3) (hn3 : r3 ≠ w3)
    (hfy : gmoLt G r1 Ry) (hAy : gmoLt G Ay r3) (h : gmoLt G w3 r1) : False := by
  have k1 := SBAcq.rfLt G Ay Ry y ty vy hlv hry hsy hhy
  have k2 := SBAcq.frLt G r3 Az w3 z t3 v3 u3 hwf hlv hr3 hs3 hw3 hAz hn3
  exact gmoLtIrrefl G w3
    (gmoLtTrans _ _ _ _ h (gmoLtTrans _ _ _ _ hfy (gmoLtTrans _ _ _ _ k1
      (gmoLtTrans _ _ _ _ hAy k2))))

/-- **THE BUFFERING IS NECESSARY (Litmus 2)**: in every gmo with the outcome's rf, `w‴` is NOT
gmo-before hart 0's read `r1` … -/
theorem SBAcq.l2NeedsBuffer (G : Gexec) (t1 ty t3 : Nat) (hP : G.gxProg = SBAcq.l2Prog t1 ty t3)
    (hok : SBAcq.Ok6 G) (hsy : gwriteAt G ty = some (0, 3)) (hs3 : gwriteAt G t3 = some (1, 0)) :
    ¬ gmoLt G (1, 2) (0, 1) := by
  intro h
  obtain ⟨hwf, hp, hlv⟩ := hok
  have L01 : gxLbl G (0, 1) = some (LLoad false 1 [t1] [b1]) := (SBAcq.lblOf G _ hP 0 1).trans rfl
  have L02 : gxLbl G (0, 2) = some (LFence true true false true) := (SBAcq.lblOf G _ hP 0 2).trans rfl
  have L03 : gxLbl G (0, 3) = some (LStore false 2 [b0] .WCplain) := (SBAcq.lblOf G _ hP 0 3).trans rfl
  have L10 : gxLbl G (1, 0) = some (LRmw true false 0 [0] [b0] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 1 0).trans rfl
  have L12 : gxLbl G (1, 2) = some (LStore false 0 [b0] .WCplain) := (SBAcq.lblOf G _ hP 1 2).trans rfl
  have L20 : gxLbl G (2, 0) = some (LRmw true false 2 [ty] [b0] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 2 0).trans rfl
  have L21 : gxLbl G (2, 1) = some (LLoad false 0 [t3] [b1]) := (SBAcq.lblOf G _ hP 2 1).trans rfl
  exact SBAcq.l2Core G hwf hlv (1, 0) (1, 2) (0, 1) (0, 3) (2, 0) (2, 1) 2 0 ty t3 b0 b1 b0
    (SBAcq.rdRmw G _ _ _ _ _ _ _ _ L20) hsy (by decide)
    (SBAcq.rdLd G _ _ _ _ _ L21) hs3 (SBAcq.wrSt G _ _ _ _ _ L12)
    (SBAcq.acqLt G _ _ _ _ hp L10 L12 rfl (by decide) rfl rfl rfl) (by decide)
    (SBAcq.fenceLt G _ _ _ _ 2 _ _ _ _ hp L01 L03 rfl (by decide) (by decide) L02 rfl rfl)
    (SBAcq.acqLt G _ _ _ _ hp L20 L21 rfl (by decide) rfl rfl rfl) h

/-- … hence (`r1` reads `A_d2`, an external source) `w‴` is gmo-after hart 1's next acquire. -/
theorem SBAcq.l2NeedsBufferAcq (G : Gexec) (t1 ty t3 : Nat) (hP : G.gxProg = SBAcq.l2Prog t1 ty t3)
    (hok : SBAcq.Ok6 G) (hs1 : gwriteAt G t1 = some (1, 3)) (hsy : gwriteAt G ty = some (0, 3))
    (hs3 : gwriteAt G t3 = some (1, 0)) :
    ¬ gmoLt G (1, 2) (1, 3) := by
  intro h
  have L01 : gxLbl G (0, 1) = some (LLoad false 1 [t1] [b1]) := (SBAcq.lblOf G _ hP 0 1).trans rfl
  exact SBAcq.l2NeedsBuffer G t1 ty t3 hP hok hsy hs3
    (gmoLtTrans _ _ _ _ h (SBAcq.rfLt G (0, 1) (1, 3) 1 t1 b1 hok.2.2 (SBAcq.rdLd G _ _ _ _ _ L01)
      hs1 (by decide)))

/-- Companion: a `fence rw,rw` after `w‴` (hart 1's acquire of `d` moves to (1,4)). -/
def SBAcq.l2fProg (t1 ty t3 : Nat) : List (List Lbl) :=
  [[LRmw true false 2 [0] [b0] [b1] .WCexcl,
    LLoad false 1 [t1] [b1],
    LFence true true false true,
    LStore false 2 [b0] .WCplain],
   [LRmw true false 0 [0] [b0] [b1] .WCexcl,
    LFence true true false true,
    LStore false 0 [b0] .WCplain,
    LFence true true true true,
    LRmw true false 1 [0] [b0] [b1] .WCexcl],
   [LRmw true false 2 [ty] [b0] [b1] .WCexcl,
    LLoad false 0 [t3] [b1],
    LRmw true false 0 [t3] [b1] [b1] .WCexcl]]

/-- **COMPANION: ordering `w‴` before the acquire FORBIDS Litmus 2's outcome.** -/
theorem SBAcq.l2FenceNo (G : Gexec) (t1 ty t3 : Nat) (hP : G.gxProg = SBAcq.l2fProg t1 ty t3)
    (hok : SBAcq.Ok6 G) (hs1 : gwriteAt G t1 = some (1, 4)) (hsy : gwriteAt G ty = some (0, 3))
    (hs3 : gwriteAt G t3 = some (1, 0)) : False := by
  obtain ⟨hwf, hp, hlv⟩ := hok
  have L01 : gxLbl G (0, 1) = some (LLoad false 1 [t1] [b1]) := (SBAcq.lblOf G _ hP 0 1).trans rfl
  have L02 : gxLbl G (0, 2) = some (LFence true true false true) := (SBAcq.lblOf G _ hP 0 2).trans rfl
  have L03 : gxLbl G (0, 3) = some (LStore false 2 [b0] .WCplain) := (SBAcq.lblOf G _ hP 0 3).trans rfl
  have L10 : gxLbl G (1, 0) = some (LRmw true false 0 [0] [b0] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 1 0).trans rfl
  have L12 : gxLbl G (1, 2) = some (LStore false 0 [b0] .WCplain) := (SBAcq.lblOf G _ hP 1 2).trans rfl
  have L13 : gxLbl G (1, 3) = some (LFence true true true true) := (SBAcq.lblOf G _ hP 1 3).trans rfl
  have L14 : gxLbl G (1, 4) = some (LRmw true false 1 [0] [b0] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 1 4).trans rfl
  have L20 : gxLbl G (2, 0) = some (LRmw true false 2 [ty] [b0] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 2 0).trans rfl
  have L21 : gxLbl G (2, 1) = some (LLoad false 0 [t3] [b1]) := (SBAcq.lblOf G _ hP 2 1).trans rfl
  have hw3 : gmoLt G (1, 2) (0, 1) :=
    gmoLtTrans _ _ _ _
      (SBAcq.fenceLt G _ _ _ _ 3 _ _ _ _ hp L12 L14 rfl (by decide) (by decide) L13 rfl rfl)
      (SBAcq.rfLt G (0, 1) (1, 4) 1 t1 b1 hlv (SBAcq.rdLd G _ _ _ _ _ L01) hs1 (by decide))
  exact SBAcq.l2Core G hwf hlv (1, 0) (1, 2) (0, 1) (0, 3) (2, 0) (2, 1) 2 0 ty t3 b0 b1 b0
    (SBAcq.rdRmw G _ _ _ _ _ _ _ _ L20) hsy (by decide)
    (SBAcq.rdLd G _ _ _ _ _ L21) hs3 (SBAcq.wrSt G _ _ _ _ _ L12)
    (SBAcq.acqLt G _ _ _ _ hp L10 L12 rfl (by decide) rfl rfl rfl) (by decide)
    (SBAcq.fenceLt G _ _ _ _ 2 _ _ _ _ hp L01 L03 rfl (by decide) (by decide) L02 rfl rfl)
    (SBAcq.acqLt G _ _ _ _ hp L20 L21 rfl (by decide) rfl rfl rfl) hw3

/-- THE REACHABILITY CAVEAT.  If hart 0's read of `d` is xv6's `acquire(d)` (`holding` load (0,1)),
hart 0 can `release(y)` only after its `amoswap.w.aq` on `d` succeeds [`S1` = (0,2)], reading a 0 at
`d` co-after hart 1's acquire — hart 1's own `release(d)` [(1,5), after `fence rw,w` (1,4)]. -/
def SBAcq.l2cProg (t1 ts ty t3 : Nat) : List (List Lbl) :=
  [[LRmw true false 2 [0] [b0] [b1] .WCexcl,
    LLoad false 1 [t1] [b1],
    LRmw true false 1 [ts] [b0] [b1] .WCexcl,
    LFence true true false true,
    LStore false 2 [b0] .WCplain],
   [LRmw true false 0 [0] [b0] [b1] .WCexcl,
    LFence true true false true,
    LStore false 0 [b0] .WCplain,
    LRmw true false 1 [0] [b0] [b1] .WCexcl,
    LFence true true false true,
    LStore false 1 [b0] .WCplain],
   [LRmw true false 2 [ty] [b0] [b1] .WCexcl,
    LLoad false 0 [t3] [b1],
    LRmw true false 0 [t3] [b1] [b1] .WCexcl]]

/-- **`SBAcq.l2cNo`: Litmus 2 with hart 0 inside `acquire(d)` is FORBIDDEN** — hart 1's
`release(d)` fence orders `w‴` before the store hart 0's successful acquire reads. -/
theorem SBAcq.l2cNo (G : Gexec) (t1 ts ty t3 : Nat) (hP : G.gxProg = SBAcq.l2cProg t1 ts ty t3)
    (hok : SBAcq.Ok6 G) (hss : gwriteAt G ts = some (1, 5)) (hsy : gwriteAt G ty = some (0, 4))
    (hs3 : gwriteAt G t3 = some (1, 0)) : False := by
  obtain ⟨hwf, hp, hlv⟩ := hok
  have L02 : gxLbl G (0, 2) = some (LRmw true false 1 [ts] [b0] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 0 2).trans rfl
  have L04 : gxLbl G (0, 4) = some (LStore false 2 [b0] .WCplain) := (SBAcq.lblOf G _ hP 0 4).trans rfl
  have L10 : gxLbl G (1, 0) = some (LRmw true false 0 [0] [b0] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 1 0).trans rfl
  have L12 : gxLbl G (1, 2) = some (LStore false 0 [b0] .WCplain) := (SBAcq.lblOf G _ hP 1 2).trans rfl
  have L14 : gxLbl G (1, 4) = some (LFence true true false true) := (SBAcq.lblOf G _ hP 1 4).trans rfl
  have L15 : gxLbl G (1, 5) = some (LStore false 1 [b0] .WCplain) := (SBAcq.lblOf G _ hP 1 5).trans rfl
  have L20 : gxLbl G (2, 0) = some (LRmw true false 2 [ty] [b0] [b1] .WCexcl) :=
    (SBAcq.lblOf G _ hP 2 0).trans rfl
  have L21 : gxLbl G (2, 1) = some (LLoad false 0 [t3] [b1]) := (SBAcq.lblOf G _ hP 2 1).trans rfl
  have hw3 : gmoLt G (1, 2) (0, 2) :=
    gmoLtTrans _ _ _ _
      (SBAcq.fenceLt G _ _ _ _ 4 _ _ _ _ hp L12 L15 rfl (by decide) (by decide) L14 rfl rfl)
      (SBAcq.rfLt G (0, 2) (1, 5) 1 ts b0 hlv (SBAcq.rdRmw G _ _ _ _ _ _ _ _ L02) hss (by decide))
  exact SBAcq.l2Core G hwf hlv (1, 0) (1, 2) (0, 2) (0, 4) (2, 0) (2, 1) 2 0 ty t3 b0 b1 b0
    (SBAcq.rdRmw G _ _ _ _ _ _ _ _ L20) hsy (by decide)
    (SBAcq.rdLd G _ _ _ _ _ L21) hs3 (SBAcq.wrSt G _ _ _ _ _ L12)
    (SBAcq.acqLt G _ _ _ _ hp L10 L12 rfl (by decide) rfl rfl rfl) (by decide)
    (SBAcq.acqLt G _ _ _ _ hp L02 L04 rfl (by decide) rfl rfl rfl)
    (SBAcq.acqLt G _ _ _ _ hp L20 L21 rfl (by decide) rfl rfl rfl) hw3

/-! # 4. The lockstep member on a TSO-store log

One position `p e` per event of GF (the member's step; a store's or AMO's log position = its step):
each hart's memory events in PROGRAM ORDER (lockstep), every store APPENDED at its step (TSO-store
log).  A read `r` of GF's source `w` (lockstep = same rf) runs at view `fl r` (MachCSL's `tvn`):
the source is already appended, and no PLAIN store to the byte appended after the source sits at or
below the view (else the read returns that store's value — `MState.readBytes` at `tvn`).  Only plain
stores are constrained, so a failed AMO that MachCSL keeps SILENT (δ1) is never a constraint.  The
floors: MachCSL δ1 `afterExcl`/`store` set `tv := top+1` = the position of a successful `.aq` AMO
(`floorTop`); the weaker "δ1′" floor reaches only an acquire's rf-SOURCE (`floorSrc`). -/

def SBAcq.isSt (l : Lbl) : Bool :=
  match l with
  | LStore .. => true
  | _ => false

structure SBAcq.TsoCore (G : Gexec) (p fl : Geid → Nat) : Prop where
  po : ∀ e1 e2, WeakRvwmoGraph.gpo G e1 e2 → gmem G e1 → gmem G e2 → p e1 < p e2
  rfSrc : ∀ r a t v w, greadsByte G r a t v → gwriteAt G t = some w → p w < p r
  stale : ∀ r a t v w w' u, greadsByte G r a t v → gwriteAt G t = some w →
    glblIs G w' SBAcq.isSt → gwritesByte G w' a u → p w < p w' → fl r < p w'

/-- MachCSL δ1: after a successful `.aq` AMO `A ∈ acqs`, every po-later read's view is ≥ `p A`. -/
def SBAcq.floorTop (G : Gexec) (p fl : Geid → Nat) (acqs : List Geid) : Prop :=
  ∀ A r, A ∈ acqs → WeakRvwmoGraph.gpo G A r → p A ≤ fl r

/-- "δ1′": an acquire only floors po-later reads at its rf-source's position. -/
def SBAcq.floorSrc (G : Gexec) (p fl : Geid → Nat) : Prop :=
  ∀ A r a t v w, WeakRvwmoGraph.gpo G A r → glblIs G A lbAq → greadsByte G A a t v →
    gwriteAt G t = some w → p w ≤ fl r

/-- A read's view is at or above its source (used only for the non-vacuity check). -/
def SBAcq.srcLe (G : Gexec) (p fl : Geid → Nat) : Prop :=
  ∀ r a t v w, greadsByte G r a t v → gwriteAt G t = some w → p w ≤ fl r

/-- **NO LOCKSTEP TSO-LOG MEMBER REPLAYS LITMUS 1** (MachCSL's top floor at the successful
acquires `A1` = (0,3), `A2` = (1,3)): `p w′ < p A1 ≤ fl F1 < p w″ < p A2 ≤ fl F2 < p w′`. -/
theorem SBAcq.l1NoMember (p fl : Geid → Nat) :
    SBAcq.TsoCore SBAcq.l1.gdG p fl → SBAcq.floorTop SBAcq.l1.gdG p fl [(0, 3), (1, 3)] → False := by
  intro hm hf
  have e1 := hm.po (0, 2) (0, 3) ((gpoBSpec _ _ _).1 (by decide +kernel)) ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩
  have e2 := hm.po (1, 2) (1, 3) ((gpoBSpec _ _ _).1 (by decide +kernel)) ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩
  have e3 := hm.po (1, 0) (1, 2) ((gpoBSpec _ _ _).1 (by decide +kernel)) ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩
  have e4 := hm.po (0, 0) (0, 2) ((gpoBSpec _ _ _).1 (by decide +kernel)) ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩
  have f1 := hf (0, 3) (0, 5) (by decide) ((gpoBSpec _ _ _).1 (by decide +kernel))
  have f2 := hf (1, 3) (1, 5) (by decide) ((gpoBSpec _ _ _).1 (by decide +kernel))
  have s1 := hm.stale (0, 5) 2 2 b1 (1, 0) (1, 2) b0 ((grbBSpec _ _ _ _ _).1 (by decide +kernel))
    SBAcq.l1Rf.1 ((glblBSpec _ _ _).1 (by decide +kernel)) ((gwbBSpec _ _ _ _).1 (by decide +kernel))
    e3
  have s2 := hm.stale (1, 5) 0 1 b1 (0, 0) (0, 2) b0 ((grbBSpec _ _ _ _ _).1 (by decide +kernel))
    SBAcq.l1Rf.2 ((glblBSpec _ _ _).1 (by decide +kernel)) ((gwbBSpec _ _ _ _).1 (by decide +kernel))
    e4
  omega

/-- **NO LOCKSTEP TSO-LOG MEMBER REPLAYS LITMUS 2, under ANY floor ≥ the acquire's source**:
`p w‴ < p A_d2 < p r1 < p R_y ≤ fl r3 < p w‴`. -/
theorem SBAcq.l2NoMember (p fl : Geid → Nat) :
    SBAcq.TsoCore SBAcq.l2.gdG p fl → SBAcq.floorSrc SBAcq.l2.gdG p fl → False := by
  intro hm hf
  have e1 := hm.po (1, 2) (1, 3) ((gpoBSpec _ _ _).1 (by decide +kernel)) ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩
  have e2 := hm.po (0, 1) (0, 3) ((gpoBSpec _ _ _).1 (by decide +kernel)) ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩
  have e3 := hm.po (1, 0) (1, 2) ((gpoBSpec _ _ _).1 (by decide +kernel)) ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩
  have r1 := hm.rfSrc (0, 1) 1 3 b1 (1, 3) ((grbBSpec _ _ _ _ _).1 (by decide +kernel)) SBAcq.l2Rf.1
  have f := hf (2, 0) (2, 1) 2 4 b0 (0, 3) ((gpoBSpec _ _ _).1 (by decide +kernel))
    ((glblBSpec _ _ _).1 (by decide +kernel)) ((grbBSpec _ _ _ _ _).1 (by decide +kernel))
    SBAcq.l2Rf.2.1
  have s := hm.stale (2, 1) 0 1 b1 (1, 0) (1, 2) b0 ((grbBSpec _ _ _ _ _).1 (by decide +kernel))
    SBAcq.l2Rf.2.2 ((glblBSpec _ _ _).1 (by decide +kernel)) ((gwbBSpec _ _ _ _).1 (by decide +kernel))
    e3
  omega

/-- … and so under MachCSL's top floor at `A_y3` too (its source `R_y` is appended before it). -/
theorem SBAcq.l2NoMemberTop (p fl : Geid → Nat) :
    SBAcq.TsoCore SBAcq.l2.gdG p fl → SBAcq.floorTop SBAcq.l2.gdG p fl [(2, 0)] → False := by
  intro hm hf
  have e1 := hm.po (1, 2) (1, 3) ((gpoBSpec _ _ _).1 (by decide +kernel)) ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩
  have e2 := hm.po (0, 1) (0, 3) ((gpoBSpec _ _ _).1 (by decide +kernel)) ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩
  have e3 := hm.po (1, 0) (1, 2) ((gpoBSpec _ _ _).1 (by decide +kernel)) ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩
  have r1 := hm.rfSrc (0, 1) 1 3 b1 (1, 3) ((grbBSpec _ _ _ _ _).1 (by decide +kernel)) SBAcq.l2Rf.1
  have ry := hm.rfSrc (2, 0) 2 4 b0 (0, 3) ((grbBSpec _ _ _ _ _).1 (by decide +kernel))
    SBAcq.l2Rf.2.1
  have f := hf (2, 0) (2, 1) (by decide) ((gpoBSpec _ _ _).1 (by decide +kernel))
  have s := hm.stale (2, 1) 0 1 b1 (1, 0) (1, 2) b0 ((grbBSpec _ _ _ _ _).1 (by decide +kernel))
    SBAcq.l2Rf.2.2 ((glblBSpec _ _ _).1 (by decide +kernel)) ((gwbBSpec _ _ _ _).1 (by decide +kernel))
    e3
  omega

/-! ## Non-vacuity: Litmus 1 HAS a member under the source floor -/

def SBAcq.memberB (G : Gexec) (p fl : Geid → Nat) : Bool :=
  (gevents G).all (fun e1 => (gevents G).all (fun e2 =>
    !(gpoB G e1 e2 && glblB G e1 lbIsMem && glblB G e2 lbIsMem) || decide (p e1 < p e2))) &&
  (gevents G).all (fun r => (grdBytes G r).all (fun x =>
    match gwriteAt G x.1.2 with
    | some w => decide (p w < p r) && decide (p w ≤ fl r) &&
        (gevents G).all (fun w' =>
          !(glblB G w' SBAcq.isSt && gwaB G w' x.1.1 && decide (p w < p w')) ||
            decide (fl r < p w'))
    | none => true)) &&
  (gevents G).all (fun A => (gevents G).all (fun r =>
    !(gpoB G A r && glblB G A lbAq) || (grdBytes G A).all (fun x =>
      match gwriteAt G x.1.2 with
      | some w => decide (p w ≤ fl r)
      | none => true)))

theorem SBAcq.memberBSound (G : Gexec) (p fl : Geid → Nat) :
    SBAcq.memberB G p fl = true →
    SBAcq.TsoCore G p fl ∧ SBAcq.floorSrc G p fl ∧ SBAcq.srcLe G p fl := by
  unfold SBAcq.memberB
  simp only [Bool.and_eq_true]
  rintro ⟨⟨hpo, hrd⟩, hfl⟩
  have hR : ∀ r a t v w, greadsByte G r a t v → gwriteAt G t = some w →
      p w < p r ∧ p w ≤ fl r ∧
      ∀ w', w' ∈ gevents G → glblB G w' SBAcq.isSt = true → gwaB G w' a = true →
        p w < p w' → fl r < p w' := by
    intro r a t v w hr hw
    have h := (forallbForallTrue _ _).1
      ((forallbForallTrue _ _).1 hrd r (greadsByteGevents G r a t v hr))
      ((a, t), v) ((greadsByteBytes G r a t v).1 hr)
    simp only [hw, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨h1, h2, fun w' hw' hs hwa hlt => ?_⟩
    have h4 := (forallbForallTrue _ _).1 h3 w' hw'
    simpa [hs, hwa, hlt] using h4
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro e1 e2 hg hm1 hm2
    obtain ⟨h1, h2⟩ := gpoGevents G e1 e2 hg
    have h := (forallbForallTrue _ _).1 ((forallbForallTrue _ _).1 hpo e1 h1) e2 h2
    have hgb := (gpoBSpec G e1 e2).2 hg
    have hb1 : glblB G e1 lbIsMem = true := (glblBSpec G e1 lbIsMem).2 hm1
    have hb2 : glblB G e2 lbIsMem = true := (glblBSpec G e2 lbIsMem).2 hm2
    simpa [hgb, hb1, hb2] using h
  · intro r a t v w hr hw
    exact (hR r a t v w hr hw).1
  · intro r a t v w w' u hr hw hst hwr hlt
    exact (hR r a t v w hr hw).2.2 w' (gwritesByteGevents G w' a u hwr)
      ((glblBSpec G w' SBAcq.isSt).2 hst) ((gwaBSpec G w' a).2 ⟨u, hwr⟩) hlt
  · intro A r a t v w hg haq hrA hw
    obtain ⟨h1, h2⟩ := gpoGevents G A r hg
    have h := (forallbForallTrue _ _).1 ((forallbForallTrue _ _).1 hfl A h1) r h2
    have hgb := (gpoBSpec G A r).2 hg
    have hab := (glblBSpec G A lbAq).2 haq
    simp only [hgb, hab, Bool.and_self, Bool.not_true, Bool.false_or] at h
    have h' := (forallbForallTrue _ _).1 h ((a, t), v) ((greadsByteBytes G A a t v).1 hrA)
    simpa [hw] using h'
  · intro r a t v w hr hw
    exact (hR r a t v w hr hw).2.1

/-- The position of `e` in an interleaving. -/
def SBAcq.posIn : List Geid → Geid → Nat
  | [], _ => 0
  | x :: xs, e => if x = e then 0 else SBAcq.posIn xs e + 1

/-- The member: `A_b1 A_d2 w′ w″ A1 A2 r1 r2 F1 F2` (stores appended in program order), reading
at views `fl` = 2 (hart 0: above `A_d2`, below `w″`) / 1 (hart 1: above `A_b1`, below `w′`). -/
def SBAcq.ord1 : List Geid :=
  [(0, 0), (1, 0), (0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (1, 4), (0, 5), (1, 5)]

def SBAcq.fl1 (e : Geid) : Nat := if e.1 = 0 then 2 else 1

/-- **NON-VACUITY**: Litmus 1 HAS a lockstep TSO-log member when acquires floor only at their
rf-source — the top floor is what `SBAcq.l1NoMember` needs. -/
theorem SBAcq.l1MemberSrc :
    SBAcq.TsoCore SBAcq.l1.gdG (SBAcq.posIn SBAcq.ord1) SBAcq.fl1 ∧
    SBAcq.floorSrc SBAcq.l1.gdG (SBAcq.posIn SBAcq.ord1) SBAcq.fl1 ∧
    SBAcq.srcLe SBAcq.l1.gdG (SBAcq.posIn SBAcq.ord1) SBAcq.fl1 :=
  SBAcq.memberBSound _ _ _ (by decide +kernel)

end Weak
