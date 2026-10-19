/-
Weak: **allocproc route P — row P-W3r-g: PTE CUSTODY AT THE REALIZED PREFIX — the 9 PTE census sites are
never blocked** (plan rev 56 row P-W3r-g / NAMED-INPUTS N9; Q-6M-PTE (a), [R45.3]; design
`notes/weak-allocproc-routeP-design.md` §3.4 per-site table; `notes/weak-allocproc-plan-review-R46.md` §3;
PROGRESS-P-W3r-f + P-W3r-g.md).  Lean-only, no Rocq twin.  A PRIMED TWIN: nothing registered imports this
file.

**Spec, stated first.**  riscv.cat orders none of the 9 PTE census loads before every later waited-on event of
its hart: 7 of them reach their `PCtrl` branch through ALU instructions only (`SbHeadHop2.ptePctrlAlu`: rule 11
orders the later WRITES, but a later READ may be satisfied first), `ismapped+0x10` crosses its `ret` (PResidue,
`SbLbFree.ismapped10RetFree`), and `uvmclear+0x10`'s only static order is rule 10 into its own `PDep` store
(`SbLbFree.uvmclearDep`, finding F-W2-LB-1: `kexec`'s later stores are not ordered after the load).  So the
per-site table cannot use static hops there: the sites must be NEVER BLOCKED.  They are, by custody: a user
page table is written only by the hart currently running its process (or the reaper after `wait`'s
`acquire(&pp->lock)`), and a process changes harts only through `p->lock` — the old hart's stores are
po-before its `release`'s `fence rw,w`, the new hart's `amoswap.w.aq` reads that release (or a later one),
so the stores have LANDED by the epoch (`SbBlocked.Hb.amo` + `Hb.epoch`, `SbBlocked.hbSound`).  A head every
byte of whose GF source is the image, an own write, or such a chain passes the value gate
(`SbBlocked.blockedIsCensus`).

  §1  image facts (`decide +kernel`): the 9 PTE census sites (`SilSite.kSites`, class `.pte`), their pins, and
      the two value-to-data sites (`uvmcopy+0x36`, `uvmclear+0x10`).
  §2  the lock HAND-OFF chain over `SbBlocked.Hb`: **`acqHop`** (a chain-realized acquire's source release is
      landed, hence every store po-before the releaser's `pw ∧ sw` fence is), **`relayAcq`** (an acquire po-before
      a landed release is chain-realized: multi-hop hand-offs), **`ownHop`** (the head's own realized acquire
      roots the chain), `handoffCls` (one hop as a `SrcCls`).
  §3  the NAMED custody classification **`SbPteCust.PteCustSrc`** and **`SbPteCust.pteNeverBlocked`**; the
      walker's exclusive A/D pair (row H5's drain-blocked read): **`SbPteCust.walkerSrcLatest`** (a chained /
      own-landed / image byte source is the member-latest) over the NAMED `SbPteCust.WalkerCustSrc`.
  §4  the table assembly **`SbPteCust.headOrdRdOfCensusPH`**: `HeadOrdRd` (value gate) from the non-census
      transport, PTE custody, `HeldPin`, and the per-head table at the REMAINING census heads only.

Spec mark: FAITHFUL (proof organisation over riscv.cat rule 4 at the release fence, rule 5 / atomicity at the
acquire, the load value axiom, as the walk machine honours them; no new trusted text).  NAMED (FAITHFUL,
WEAKER while named): `PteCustSrc`, `WalkerCustSrc` (P-W6: the realization's custody + lock hand-off chains,
from the 5th export conjunct `pteDiscAtP` and the lock discipline at the realized prefix).
Lean-only helpers `SbPteCust.*`.
-/
import Weak.SbHeldPin
import Weak.SbLbFree

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open KernelPinsDef
open Lbl SbWalk SbAgree SbReplay SbOrd

/-! # 1. Image facts -/

/-- The PTE census sites (`SilSite.kSites`, class `.pte`). -/
def SbPteCust.pteSites : List SilSite.Site :=
  SilSite.kSites.filter (fun s => decide (s.cls = SilSite.Cls.pte))

/-- **THE 9 PTE CENSUS SITES** (`decide +kernel`): their pcs in census order, each pinned in the pin table;
7 `PCtrl`, `ismapped+0x10` `PResidue`, `uvmclear+0x10` `PDep` (F-W2-LB-1); the value-to-data sites are
`uvmcopy+0x36` and `uvmclear+0x10` (route `.noTaint`). -/
theorem SbPteCust.pteSitesShape :
    SbPteCust.pteSites.map SilSite.Site.pc =
      [SilSite.sym KernelSyms.«walk» 0x32, SilSite.sym KernelSyms.«walkaddr» 0x1c,
       SilSite.sym KernelSyms.«mappages» 0x4a, SilSite.sym KernelSyms.«uvmunmap» 0x5e,
       SilSite.sym KernelSyms.«freewalk» 0x2a, SilSite.sym KernelSyms.«ismapped» 0x10,
       SilSite.sym KernelSyms.«copyout» 0x82, SilSite.sym KernelSyms.«uvmcopy» 0x36,
       SilSite.sym KernelSyms.«uvmclear» 0x10] ∧
    SbPteCust.pteSites.length = 9 ∧
    SbPteCust.pteSites.all (fun s => decide ((s.pc, s.pin) ∈ pins) && roleIsLoad (krole s.pc)) = true ∧
    (SbPteCust.pteSites.filter (fun s => decide (s.route = SilSite.Route.noTaint))).map SilSite.Site.pc =
      [SilSite.sym KernelSyms.«uvmcopy» 0x36, SilSite.sym KernelSyms.«uvmclear» 0x10] ∧
    (SilSite.sym KernelSyms.«uvmclear» 0x10, Pin.PDep 0x80001514 false) ∈ pins := by
  decide +kernel

/-! # 2. The lock hand-off chain -/

section Chain

variable {G : Gexec} {dev : List Geid} {h : Geid}

/-- **THE HEAD'S OWN REALIZED ACQUIRE ROOTS THE CHAIN.** -/
theorem SbPteCust.ownHop (A : Geid) (h1 : A.1 = h.1) (h2 : A.2 < h.2) : SbBlocked.Hb G dev h false A :=
  .root A h1 h2

/-- **ACQUIRE HOP**: a chain-realized RMW `A` reading byte `j` from the write `r` (its source release); every
event `s` of `r`'s row po-before a `pw ∧ sw` fence po-before `r` has landed (rule 4 at the release fence, as the
epoch buffer enforces it). -/
theorem SbPteCust.acqHop (A r s : Geid) (aq rl : Bool) (base : Int) (ts : List Nat)
    (rvs wvs : List (BitVec 8)) (kc : WmClass) (j t : Nat) (hA : SbBlocked.Hb G dev h false A)
    (hl : gxLbl G A = some (LRmw aq rl base ts rvs wvs kc)) (htj : ts[j]? = some t)
    (hr : gwriteAt G t = some r) (hrW : gisW G r = true) (h1 : s.1 = r.1) (hf : fenceSw G s.1 s.2 r.2) :
    SbBlocked.Hb G dev h true s :=
  .epoch r s (.amo A r aq rl base ts rvs wvs kc j t hA hl htj hr) hrW h1 hf

/-- **RELAY**: an event po-before a LANDED write of its row is chain-realized (so an earlier acquire of the
releaser roots the next hop: multi-hop hand-offs). -/
theorem SbPteCust.relayAcq (r e : Geid) (hr : SbBlocked.Hb G dev h true r) (h1 : e.1 = r.1)
    (h2 : e.2 < r.2) : SbBlocked.Hb G dev h false e :=
  .po r e (.lr r hr) h1 h2

/-- One hand-off hop as a source class: the store `s` (GF index `t'`) is po-before the releaser's fence. -/
theorem SbPteCust.handoffCls (A r s : Geid) (aq rl : Bool) (base : Int) (ts : List Nat)
    (rvs wvs : List (BitVec 8)) (kc : WmClass) (j t t' : Nat) (hA : SbBlocked.Hb G dev h false A)
    (hl : gxLbl G A = some (LRmw aq rl base ts rvs wvs kc)) (htj : ts[j]? = some t)
    (hr : gwriteAt G t = some r) (hrW : gisW G r = true) (hs : gwriteAt G t' = some s) (h1 : s.1 = r.1)
    (hf : fenceSw G s.1 s.2 r.2) : SbBlocked.SrcCls G dev h t' :=
  .inr ⟨s, hs, .inr (SbPteCust.acqHop A r s aq rl base ts rvs wvs kc j t hA hl htj hr hrW h1 hf)⟩

end Chain

/-! # 3. PTE custody: never blocked -/

/-- **PTE CUSTODY AT THE REALIZED PREFIX** (NAMED; FAITHFUL, WEAKER while named; Q-6M-PTE (a)): at walk state
`w`, every non-exempt plain-load head realizing one of the 9 PTE census sites (`PteHd`, the label ↔ pc map of
(T)) has every byte source in a source class — the image, an OWN write of its hart, or a write the chain
`SbBlocked.Hb` lands (`acqHop` / `relayAcq` hand-offs through `p->lock`; the reaper's `wait` acquire of the
child's `p->lock`; a fresh table page's zero fill by `kalloc`'s caller on the same hart = own).
Discharger: P-W6 — the realization's custody map (the 5th export conjunct `pteDiscAtP`: who may write a PTE
slot) + the lock hand-off at the realized prefix (the head's hart's `amoswap.w.aq` on `p->lock` realized and
po-before; the previous holder's PTE stores po-before its `release`'s `fence rw,w`). -/
def SbPteCust.PteCustSrc (G : Gexec) (dev : List Geid) (PteHd : Geid → Prop) (w : WS) : Prop :=
  ∀ x base ts vs, gxLbl G (hd w x) = some (LLoad false base ts vs) → PteHd (hd w x) →
    ∀ a t v, greadsByte G (hd w x) a t v → SbBlocked.SrcCls G dev (hd w x) t

/-- **THE 9 PTE SITES ARE NEVER BLOCKED** (value gate), at every reachable state of a valid candidate. -/
theorem SbPteCust.pteNeverBlocked {N : Nat} {G : Gexec} {X : Geid → Prop} {dev : List Geid}
    (PteHd : Geid → Prop) (c : CandW) (hv : validW SbPol.epoch c) (hP : PInv N c.img G X dev (cur c))
    (hc : CatH G) (himg : G.gxImg = c.img) (hT : SbPteCust.PteCustSrc G dev PteHd (cur c))
    (x : Nat) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G (hd (cur c) x) = some (LLoad false base ts vs)) (hH : PteHd (hd (cur c) x)) :
    valGate (cur c) x base ts vs :=
  SbBlocked.blockedIsCensusC c hv hP hc himg x false base ts vs hl (hT x base ts vs hl hH)

section Walker

variable {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid} {w : WS}

/-- An OWN GF source of an RMW head's byte is po-before it (rule 1; the RMW's own write is co-after its
read). -/
theorem SbPteCust.ownPoRmw (hc : CatH G) (hh : Geid) (aq rl : Bool) (base : Int) (ts : List Nat)
    (rvs wvs : List (BitVec 8)) (kc : WmClass) (hl : gxLbl G hh = some (LRmw aq rl base ts rvs wvs kc))
    (a : Int) (t : Nat) (v : BitVec 8) (hrd : greadsByte G hh a t v) (s : Geid) (hs : gwriteAt G t = some s)
    (hsx : s.1 = hh.1) : s.2 < hh.2 ∧ gwritesByte G s a v := by
  obtain ⟨hsrc, -⟩ := hc.lv hh a t v hrd
  cases t with
  | zero => simp [gwriteAt] at hs
  | succ n =>
    obtain ⟨s', hs', hsw, hvis⟩ := hsrc
    rw [hs] at hs'
    cases hs'
    refine ⟨?_, hsw⟩
    rcases hvis with hg | hg
    · refine Classical.byContradiction (fun hn => ?_)
      rcases Nat.lt_or_ge hh.2 s.2 with hlt | hge
      · obtain ⟨ls, -, -, -, hls, -⟩ := id hsw
        have hpo : WeakRvwmoGraph.gpo G hh s := SBAcq.gpoOf G hh s _ ls hl hls hsx.symm hlt
        have h2 := rule1Lt G hh s a v hc.ppo hpo (.inr ⟨_, v, hrd⟩) hsw
        exact gmoLtIrrefl G s (gmoLtTrans G s hh s hg h2)
      · have heq : s = hh := Prod.ext hsx (by omega)
        subst heq
        exact gmoLtIrrefl G s hg
    · exact hg.2.1

/-- **THE WALKER'S EXCLUSIVE PAIR** (row H5's drain-blocked exclusive read; "likewise" of Q-6M-PTE (a)): an
RMW head byte whose GF source is the image, a chain-landed write, or an own write that is not pending, is the
member-latest (`srcLatest`, the AMO gate's source condition).  An own PENDING source is H5's drain-blocked
case (edges (E6), PROVED in `SbOrd.blkAmo`). -/
theorem SbPteCust.walkerSrcLatest (hP : PInv N img G X dev w) (hc : CatH G) (hE : SbBlocked.EpochOk w)
    (hD : SbBlocked.DrainOk w) (x : Nat) (aq rl : Bool) (base : Int) (ts : List Nat)
    (rvs wvs : List (BitVec 8)) (kc : WmClass) (hl : gxLbl G (hd w x) = some (LRmw aq rl base ts rvs wvs kc))
    (j t : Nat) (htj : ts[j]? = some t)
    (hcls : SbBlocked.SrcCls G dev (hd w x) t)
    (hnp : ∀ s, gwriteAt G t = some s → s.1 = x → ∀ p, p ∈ w.pend x → p.1 ≠ s.2) :
    srcLatest G w (accAddr base j) t := by
  obtain ⟨-, -, hrl⟩ := rmwShape hc.wf (hd w x) aq rl base ts rvs wvs kc hl
  have hj : j < ts.length := lookup_lt_Some htj
  have hrd : greadsByte G (hd w x) (accAddr base j) t (rvs[j]'(by omega)) :=
    ⟨_, base, ts, rvs, j, hl, rfl, htj, List.getElem?_eq_getElem _, rfl⟩
  have he : ¬ realized w (hd w x) := fun h => by unfold realized hd at h; simp at h
  refine hP.rd _ _ t _ hrd he ?_
  have landed : ∀ s, gwriteAt G t = some s → SbBlocked.Landed w s → landedSrc G w (accAddr base j) t := by
    intro s hs hL
    obtain ⟨hsrc, -⟩ := hc.lv _ _ t _ hrd
    cases t with
    | zero => simp [gwriteAt] at hs
    | succ n =>
      obtain ⟨s', hs', hsw, -⟩ := hsrc
      rw [hs] at hs'
      cases hs'
      exact .inr ⟨s, hs, SbBlocked.landedWr hP s _ hL (gwrBOf G s _ _ hc.wf hsw).1⟩
  rcases hcls with h0 | ⟨s, hs, hown | hhb⟩
  · exact .inl h0
  · have hpo := (SbPteCust.ownPoRmw hc (hd w x) aq rl base ts rvs wvs kc hl _ t _ hrd s hs hown).1
    have hsx : s.1 = x := hown
    refine landed s hs ⟨?_, fun p hp hp1 => hnp s hs hsx p (by rw [hsx] at hp; exact hp) hp1⟩
    show s.2 < (w.rows s.1).length
    rw [hown]; exact hpo
  · exact landed s hs ((SbBlocked.hbSound hP hc hE hD x true s hhb).2 rfl)

end Walker

/-- **THE WALKER PAIR'S CUSTODY** (NAMED; FAITHFUL, WEAKER while named; P-W6): every byte source of a walker
exclusive-pair head (`WalkerHd`, the realization's map of implicit A/D updates) is in a source class — the PTE's
writers are the owning hart (own) or handed over as in `PteCustSrc`. -/
def SbPteCust.WalkerCustSrc (G : Gexec) (dev : List Geid) (WalkerHd : Geid → Prop) (w : WS) : Prop :=
  ∀ (x : Nat) (aq rl : Bool) (base : Int) (ts : List Nat) (rvs wvs : List (BitVec 8)) (kc : WmClass),
    gxLbl G (hd w x) = some (LRmw aq rl base ts rvs wvs kc) → WalkerHd (hd w x) →
    ∀ (j t : Nat), ts[j]? = some t → SbBlocked.SrcCls G dev (hd w x) t

/-- **… AT EVERY REACHABLE STATE** of a valid candidate: under `WalkerCustSrc`, a walker pair head's byte
whose source is not an own PENDING entry (H5's drain case) is the member-latest. -/
theorem SbPteCust.walkerSrcLatestC {N : Nat} {G : Gexec} {X : Geid → Prop} {dev : List Geid}
    (WalkerHd : Geid → Prop) (c : CandW) (hv : validW SbPol.epoch c) (hP : PInv N c.img G X dev (cur c))
    (hc : CatH G) (hT : SbPteCust.WalkerCustSrc G dev WalkerHd (cur c)) (x : Nat) (aq rl : Bool)
    (base : Int) (ts : List Nat) (rvs wvs : List (BitVec 8)) (kc : WmClass)
    (hl : gxLbl G (hd (cur c) x) = some (LRmw aq rl base ts rvs wvs kc)) (hH : WalkerHd (hd (cur c) x))
    (j t : Nat) (htj : ts[j]? = some t)
    (hnp : ∀ s, gwriteAt G t = some s → s.1 = x → ∀ p, p ∈ (cur c).pend x → p.1 ≠ s.2) :
    srcLatest G (cur c) (accAddr base j) t :=
  have hh := SbBlocked.histStAt c hv c.its.length
  SbPteCust.walkerSrcLatest hP hc hh.1 hh.2 x aq rl base ts rvs wvs kc hl j t htj
    (hT x aq rl base ts rvs wvs kc hl hH j t htj) hnp

/-! # 4. The table assembly -/

/-- **ROW H3 FROM THE REMAINING CENSUS ROWS**: given the non-census transport, PTE custody and `HeldPin`, the
per-head table (never blocked, or the static hops) is needed only at the census heads that are neither PTE
sites nor held-context `holding+0x0` reads. -/
theorem SbPteCust.headOrdRdOfCensusPH {N : Nat} {G : Gexec} {X : Geid → Prop} {dev : List Geid}
    (Census PteHd HeldHd : Geid → Prop) (Held : Geid → Int → Geid → Prop) (c : CandW)
    (hv : validW SbPol.epoch c) (hP : PInv N c.img G X dev (cur c)) (hc : CatH G) (himg : G.gxImg = c.img)
    (hr1 : ∀ s m, WeakRvwmoGraph.gpo G s m → gmem G s → gisIo G s = false → gisIo G m = true →
      gmoLt G s m)
    (hr2'' : ∀ s m, WeakRvwmoGraph.gpo G s m → gisIo G s = true → gisR G m = true → gmoLt G s m)
    (hNC : SbBlocked.NonCensusSrc G dev X Census (cur c))
    (hPte : SbPteCust.PteCustSrc G dev PteHd (cur c))
    (hHC : SbHeldPin.HeldCtx G HeldHd Held (cur c)) (hWG : SbHeldPin.HeldWinGF G Held)
    (hT : ∀ x base ts vs, gxLbl G (hd (cur c) x) = some (LLoad false base ts vs) → ¬ X (hd (cur c) x) →
      Census (hd (cur c) x) → ¬ PteHd (hd (cur c) x) → ¬ HeldHd (hd (cur c) x) →
      valGate (cur c) x base ts vs ∨
        (SbHeadHop.WrHop G (hd (cur c) x) ∧ SbHeadHop2.A2At G dev (cur c) x)) :
    HeadOrdRd G X valGate dev (cur c) := by
  apply SbBlocked.headOrdRdOfCensus Census c hv hP hc himg hr1 hr2'' hNC
  intro x base ts vs hl hX hC
  by_cases hp : PteHd (hd (cur c) x)
  · exact .inl (SbPteCust.pteNeverBlocked PteHd c hv hP hc himg hPte x base ts vs hl hp)
  · by_cases hh : HeldHd (hd (cur c) x)
    · exact .inl (SbHeldPin.heldNeverBlocked hP hc himg HeldHd Held hHC hWG x base ts vs hl hh)
    · exact hT x base ts vs hl hX hC hp hh

end Weak
