/-
Weak: **W11-F [OWN.102], A13 (a) increment 4 — the B5 pin chain FROM `hartConff`** (the published
bundle's per-row emission, fabric jumps between items allowed).  Lean-only, no Rocq twin.

* `CapF5.cycRunOfHartConff` — `PinCycRun.cycRunOfHartConf` from `hartConff` (its emission is a
  `prunJ` run from ANY start fabric `d0`, `hartConffPrunJ`; its fetch items untagged,
  `hartConffFeNone`); `cycWalk` runs over jump runs since increment 3.
* `CapF5.cycRunOfHartConffR` — the same with the Sail cycle fact discharged (`cySailOfWalk`,
  `PinCycRunFetch.fetchCyR1Of`, `execCyOfWalk`) and the cycle obligations from the three realization
  interfaces (`CapF2.cycFactsAt`); left: those interfaces, `walkStartRealized`, `excRetR` (header).
* `CapF5.pinSegPinStoreB5F` / `CapF5.pinSegPinCtrlB5F` — `pinSegPinStoreB5` / `pinSegPinCtrlB5` over
  `hartConff` (`PinTrap.pinSegPinStoreFreeF` / `pinSegPinCtrlFreeF`, `Weak/PinConfF.lean`).

Spec: FAITHFUL (proof organisation).  Every name is file-qualified (`CapF5.*`).
-/
import Weak.CapF2
import Weak.PinConfF

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Wlabel KernelPinsDef
open WeakRvwmoConf (Dstate dstep)
open CatLin
open WeakRvwmoPinBridge3 (preach)
open WeakRvwmoPinBridge4 (walkOwn)
open PinWalkTab PinTrap
open SailCycleOrderK PinCycRun PinDataflow

/-- **`cycRun` FROM `hartConff`** (header): `cycRunOfHartConf` at the published bundle's emission,
from any start fabric `d0`. -/
theorem CapF5.cycRunOfHartConff (G : Gexec) (i : Nat) (row : List Lbl) (p0 : Pexv6)
    (dvi dvo : Nat → Efab) (tq : Nat → Bool) (d0 : Efab)
    (em : Hemission) (pcL : Int) (w : Pin) (own : Bool)
    (hcf : hartConff i row p0 dvi dvo tq em) (hm : (pcL, w) ∈ pinsW9a) (hw : walkOwn w = some own)
    (hft : kFetchText em)
    (hsail : ∀ s n l, preach own (pinStart pcL) s n → pstep own s = some l → l ≠ [] →
      cySailAt s.psPc)
    (hfetch : ∀ s n l, preach own (pinStart pcL) s n → pstep own s = some l → l ≠ [] →
      fetchOkRF p0 d0 em s.psPc)
    (hdata : ∀ s n l, preach own (pinStart pcL) s n → pstep own s = some l → l ≠ [] →
      dataOkRF p0 d0 em s.psPc)
    (hexc : ∀ s n l, preach own (pinStart pcL) s n → pstep own s = some l → l ≠ [] →
      excRetR G i p0 d0 em s.psPc)
    (base rest : List Eitem) (hes : em.emItems = base ++ rest)
    (hstart : ∀ p d, prunJ (base.map Prod.fst) p0 d0 p d →
      ∃ (cpu : CPU) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch),
        p = .PHart cpu (.pure ()) rs fn ib ∧ kInv (pinStart pcL).psPc rs) :
    ∃ (mid rest' : List Eitem) (s : PState) (n : Nat) (p' : Pexv6) (d' : Efab),
      rest = mid ++ rest' ∧ cycRun G i em own base (pinStart pcL) mid s ∧
      preach own (pinStart pcL) s n ∧ walkBd p0 d0 em (base ++ mid) s.psPc p' d' ∧
      cycStop G i p0 d0 em own (base ++ mid) s rest' := by
  obtain ⟨dE, hrun⟩ := hartConffPrunJ i row p0 dvi dvo tq em hcf d0
  rw [hes, List.map_append] at hrun
  obtain ⟨p1, d1, h1, h2⟩ := pevrunSplit _ _ _ _ _ _ hrun
  obtain ⟨cpu, rs, fn, ib, rfl, hk⟩ := hstart _ _ h1
  have hfeN : ∀ a tvs t, (LIFetch a tvs, t) ∈ em.emItems → t = none :=
    hartConffFeNone i row p0 dvi dvo tq em hcf
  obtain ⟨mid, rest', s, n, p', d', h3, h4, h5, h6, -, h8⟩ :=
    cycWalk G i em own p0 d0 (pinStart pcL) hfeN hft
      (PinCycRun.pstepSomeOfReach pcL w own hm hw) hsail hfetch hdata hexc rest.length rest
      (Nat.le_refl _) base (pinStart pcL) 0 _ d1 _ _ (.prRefl _)
      ⟨⟨rest, hes⟩, h1, cpu, rs, fn, ib, rfl, hk⟩ hes h2
  exact ⟨mid, rest', s, n, p', d', h3, h4, h5, h6, h8⟩

/-- **`cycRun` FROM `hartConff`, ALL CYCLE OBLIGATIONS FROM THE INTERFACES** (header). -/
theorem CapF5.cycRunOfHartConffR (G : Gexec) (i : Nat) (row : List Lbl) (p0 : Pexv6)
    (dvi dvo : Nat → Efab) (tq : Nat → Bool) (d0 : Efab)
    (em : Hemission) (pcL : Int) (w : Pin) (own : Bool)
    (hcf : hartConff i row p0 dvi dvo tq em) (hm : (pcL, w) ∈ pinsW9a) (hw : walkOwn w = some own)
    (hft : kFetchText em)
    (hreal : ∀ s n l, preach own (pinStart pcL) s n → pstep own s = some l → l ≠ [] →
      PinFetchPa.fetchRealized p0 d0 em s.psPc ∧ PinDataOk.fetchOkRealized p0 d0 em s.psPc ∧
        PinDataOk.dataRealized p0 d0 em s.psPc)
    (hexc : ∀ s n l, preach own (pinStart pcL) s n → pstep own s = some l → l ≠ [] →
      excRetR G i p0 d0 em s.psPc)
    (base rest : List Eitem) (hes : em.emItems = base ++ rest)
    (hstart : walkStartRealized p0 d0 base (pinStart pcL).psPc) :
    ∃ (mid rest' : List Eitem) (s : PState) (n : Nat) (p' : Pexv6) (d' : Efab),
      rest = mid ++ rest' ∧ cycRun G i em own base (pinStart pcL) mid s ∧
      preach own (pinStart pcL) s n ∧ walkBd p0 d0 em (base ++ mid) s.psPc p' d' ∧
      cycStop G i p0 d0 em own (base ++ mid) s rest' := by
  have hfeN : ∀ a tvs t, (LIFetch a tvs, t) ∈ em.emItems → t = none :=
    hartConffFeNone i row p0 dvi dvo tq em hcf
  have hfacts : ∀ s n l, preach own (pinStart pcL) s n → pstep own s = some l → l ≠ [] →
      fetchOkRF p0 d0 em s.psPc ∧ dataOkRF p0 d0 em s.psPc := by
    intro s n l hx hp hne
    obtain ⟨h1, h2, h3⟩ := hreal s n l hx hp hne
    exact CapF2.cycFactsAt pcL w own s n l hm hw hx hp hne p0 d0 em hft hfeN h1 h2 h3
  exact CapF5.cycRunOfHartConff G i row p0 dvi dvo tq d0 em pcL w own hcf hm hw hft
    (fun s n l hs hp hne => cySailOfWalk pcL w own s n l hm hw hs hp hne
      (PinCycRunFetch.fetchCyR1Of _) (execCyOfWalk pcL w own s n l hm hw hs hp hne))
    (fun s n l hx hp hne => (hfacts s n l hx hp hne).1)
    (fun s n l hx hp hne => (hfacts s n l hx hp hne).2) hexc base rest hes
    (fun p d hr => by
      obtain ⟨cpu, rs, fn, ib, hp, hpc, hc⟩ := hstart p d hr
      exact ⟨cpu, rs, fn, ib, hp, PinCycRunFetch.kInvOfCfg _ rs hpc hc⟩)

/-- **PDep, B5, over `hartConff` (header)**: at a walk-certifying site `(pcL, w)` of the claimed pin set
`pinsW9a`, for hart `i`'s conformant emission, a segment entering at the load (row position `j`)
and exiting at the FIRST pin's store (row position `k`, the walk's pin state `s` a fed store) is
`segPinC` in the published quantifier (`forget GT`, `ad := gtAd`) — from r3's `kFetchText` and
the cycle alignment r4 (with r1, r2, FR): no `psitesA`, no `psitesT`. -/
theorem CapF5.pinSegPinStoreB5F (GT : GdexecT) (i : Nat) (row : List Lbl) (p0 : Pexv6)
    (dvi dvo : Nat → Efab) (tq : Nat → Bool) (em : Hemission) (sg : Seg) (pcL : Int) (w : Pin) (j k : Nat) (own : Bool)
    (base mid g0 post : List Eitem) (s : PState) (rl : Bool) (a : Int) (v : List (BitVec 8))
    (asrc vsrc : List Dsrc) :
    GT.gtG.gxProg[i]? = some row → hartConff i row p0 dvi dvo tq em →
    (∀ x, x ∈ rowDepsT em.emItems → (((i, x.1.1), (i, x.1.2)), x.2) ∈ GT.gtDeps) →
    sg.sgEntry = (i, j) → sg.sgExit = (i, k) →
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    (pcL, w) ∈ pinsW9a → walkOwn w = some own →
    kFetchText em →
    cycRun GT.gtG i em own base (pinStart pcL) mid s →
    em.emItems = base ++ mid ++ g0 ++ (Wlabel.LStore rl a v asrc vsrc, some k) :: post →
    g0.all provNeutralb = true →
    dsubb (depsAddr (krole s.psPc)) asrc = true → dsubb (depsVsrc (krole s.psPc)) vsrc = true →
    pstep own s = some [] → wIsFence (kw s.psPc) = false → roleIsStore (krole s.psPc) = true →
    segPinC (forget GT) (gtAd GT.gtG GT.gtDeps) sg := by
  intro hrow hcf hdeps he hx hbase hm hw hft hrun hes hg0 hca hcv hpin hf hst
  exact pinSegPinStoreFreeF GT i row p0 dvi dvo tq em sg pcL j k own base (base ++ mid) g0 post s rl a v
    asrc vsrc hrow hcf hdeps he hx hbase hes
    (psitesTOfCycRun GT.gtG i em pcL w own base mid s hm hw hft
      ⟨g0 ++ (Wlabel.LStore rl a v asrc vsrc, some k) :: post,
        by rw [hes]; simp only [List.append_assoc]⟩ hrun) hg0 hca hcv
    (WeakRvwmoPinBridge5.pinStoreFed own s hpin hf hst)

/-- **PCtrl, B5, over `hartConff` (header)**: a segment entering at the load and exiting at a store po-after the
FIRST pin's branch (the walk's pin state `s` a conditional branch, its control item `LCtrl srcs`
covering the decoded list) is `segPinC` — no `psitesA`, no `psitesT`. -/
theorem CapF5.pinSegPinCtrlB5F (GT : GdexecT) (i : Nat) (row : List Lbl) (p0 : Pexv6)
    (dvi dvo : Nat → Efab) (tq : Nat → Bool) (em : Hemission) (sg : Seg) (pcL : Int) (w : Pin) (j k : Nat) (own : Bool)
    (base mid g0 mid' post : List Eitem) (s : PState) (srcs : List Dsrc) (kc : Option Nat)
    (rl : Bool) (a : Int) (v : List (BitVec 8)) (asrc vsrc : List Dsrc) (tgt : Int) :
    GT.gtG.gxProg[i]? = some row → hartConff i row p0 dvi dvo tq em →
    (∀ x, x ∈ rowDepsT em.emItems → (((i, x.1.1), (i, x.1.2)), x.2) ∈ GT.gtDeps) →
    sg.sgEntry = (i, j) → sg.sgExit = (i, k) →
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    (pcL, w) ∈ pinsW9a → walkOwn w = some own →
    kFetchText em →
    cycRun GT.gtG i em own base (pinStart pcL) mid s →
    em.emItems = base ++ mid ++ g0 ++ (Wlabel.LCtrl srcs, kc)
      :: (mid' ++ (Wlabel.LStore rl a v asrc vsrc, some k) :: post) →
    g0.all provNeutralb = true →
    dsubb (depsCtrl (krole s.psPc)) srcs = true →
    pstep own s = some [] → wIsFence (kw s.psPc) = false → roleIsStore (krole s.psPc) = false →
    kflowOf s.psPc = .FLbranch tgt →
    segPinC (forget GT) (gtAd GT.gtG GT.gtDeps) sg := by
  intro hrow hcf hdeps he hx hbase hm hw hft hrun hes hg0 hcov hpin hf hst hk
  exact pinSegPinCtrlFreeF GT i row p0 dvi dvo tq em sg pcL j k own base (base ++ mid) g0 mid' post s srcs
    kc rl a v asrc vsrc hrow hcf hdeps he hx hbase hes
    (psitesTOfCycRun GT.gtG i em pcL w own base mid s hm hw hft
      ⟨g0 ++ (Wlabel.LCtrl srcs, kc) :: (mid' ++ (Wlabel.LStore rl a v asrc vsrc, some k) :: post),
        by rw [hes]; simp only [List.append_assoc]⟩ hrun) hg0 hcov
    (WeakRvwmoPinBridge5.pinCtrlTainted own s tgt hpin hf hst hk)

end Weak
