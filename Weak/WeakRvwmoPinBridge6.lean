/-
Weak: **W9a (B) B5 — r1 DISCHARGED in the B5 headlines** (plan `notes/weak-allocproc-plan.md`
rev 52 §D Q-B5-FETCH, §C W9a (B) "(B5) assembly"; ruling [OWN.81]).  Lean-only.

PinBridge5's cycle alignment `cycRun` (r4) carries, per retired cycle, a bare record `CycCert`
and the two NAMED fetch premises r1 `fetchAnnR1` ("the role is the arm's announced role") and r2
`fetchPaR2` ("the arm's reads are at the pc").  Here the cycle record is the hart's REAL fetch
stretch instead (`CycFetchRun`: the cycle's items begin with a `pevrun` of the hart from a cycle
start `riscvStep tick`, boot-admitted register file, to its announce node), and r1 is a THEOREM
about the Sail text (`PinFetchVal.fetchAnnOfRun`, `Weak/PinFetchVal.lean`): the announced bits
are one of Sail's four fetch arms over the stretch's own i-cache labels.  r2 stays NAMED, now
over the real labels (`fetchPaR2Run`: the cycle's `j`-th instruction-fetch read is at
`pc + 2 j`, i.e. Sail's `translateAddr (Virtaddr PC)` / `(PC + 2)` is the identity — Q-B5-FETCH
(r2-a), the next item).

§1 the real cycle record `CycFetchRun`, the named r2 `fetchPaR2Run`; §2 `certOfFetchRun`: a
real cycle with r2 IS a `CycCert` with r1 and r2 PROVED (`fetchAnnR1`, `fetchPaR2`); §3 the
alignment `cycRunR` (r4 over real cycles) and `cycRunOfR`; §4 the headlines `pinSegPinStoreB6`,
`pinSegPinCtrlB6` — PinBridge5's B5 headlines with r1 discharged.

Named premises left in the headlines: r2 `fetchPaR2Run` (inside `cycRunR`), r4 `cycRunR` itself
(the cut into real cycles, the slot scan at the announced role, the walk successor —
Q-B5-CYCLE), FR `trapFrameRf` (inside `texcRes`, Q-TRAPRES), and B2's exit-item emission shape.

Every Lean-only helper is file-qualified `WeakRvwmoPinBridge6.*`.
-/
import Weak.WeakRvwmoPinBridge5
import Weak.PinFetchVal

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open KernelPinsDef
open WeakRvwmoConf (Dstate dstep)
open CatLin
open WeakRvwmoPinBridge3 (preach)
open WeakRvwmoPinBridge4 (walkOwn)
open PinTrap
open PinFetchVal (FRd FetchShape fetchLbls frdView)

/-! # 1. The real cycle and the named r2 -/

/-- **A REAL CYCLE'S FETCH STRETCH**: the cycle's items `g` are `cfFetch ++ cfRest`, and
`cfFetch`'s labels are a run of the hart from a cycle start (`riscvStep tick`, boot-admitted
register file) to its announce node `instrAnnounce cfN cfW`, with no boundary or announce step
before it; its i-cache items are administrative (no row position). -/
structure CycFetchRun (g : List Eitem) where
  cfFetch : List Eitem
  cfRest : List Eitem
  cfSplit : g = cfFetch ++ cfRest
  cfCpu : CPU
  cfTick : Bool
  cfRs : RegFile
  cfFn : Option (Bool × Bool × Bool × Bool)
  cfIb : Ibch
  cfD : Efab
  cfN : Nat
  cfW : BitVec cfN
  cfK : Unit → SailM Unit
  cfRs2 : RegFile
  cfFn2 : Option (Bool × Bool × Bool × Bool)
  cfIb2 : Ibch
  cfD2 : Efab
  cfBoot : PinDataflow.RbootAll cfRs
  cfRun : pevrun (cfFetch.map Prod.fst) (.PHart cfCpu (riscvStep cfTick) cfRs cfFn cfIb) cfD
    (.PHart cfCpu (.impure (.ok (.instrAnnounce cfN cfW)) cfK) cfRs2 cfFn2 cfIb2) cfD2
  cfNoInstr : Wlabel.LInstr ∉ cfFetch.map Prod.fst
  cfNoSf : Wlabel.LFence false false false false ∉ cfFetch.map Prod.fst
  cfAdmin : ∀ (base : Int) (tvs : List (Nat × BitVec 8)) (t : Option Nat),
    (Wlabel.LIFetch base tvs, t) ∈ cfFetch → t = none

/-- The role of the cycle's announced bits (the channel after the announce, `pnodeStep`). -/
def CycFetchRun.role {g : List Eitem} (c : CycFetchRun g) : OpRoles :=
  depsOfIb (ibAnn (ibOfBvn c.cfW)).ibBits

/-- **r2 (NAMED, Q-B5-FETCH (r2-a))**: the cycle's `j`-th instruction-fetch read is at `pc + 2 j`
(Sail fetches at `translateAddr (Virtaddr PC)` and, for the high half of a 4-byte instruction at
`pc ≡ 2 mod 4`, at `translateAddr (Virtaddr (PC + 2))`, `Fetch.lean:217-288`; on kernel text under
the sealed Sv39 table the translation is the identity). -/
def fetchPaR2Run (pc : Int) {g : List Eitem} (c : CycFetchRun g) : Prop :=
  ∀ (j : Nat) (a : Int) (bs : List (BitVec 8)),
    (fetchLbls (c.cfFetch.map Prod.fst))[j]? = some (a, bs) → a = pc + 2 * (j : Int)

/-! # 2. A real cycle with r2 is a certified cycle, r1 PROVED -/

/-- A fetch label of the stretch is an administrative item of the cycle. -/
theorem WeakRvwmoPinBridge6.itemOfLbls (gf : List Eitem)
    (hadm : ∀ (base : Int) (tvs : List (Nat × BitVec 8)) (t : Option Nat),
      (Wlabel.LIFetch base tvs, t) ∈ gf → t = none) :
    ∀ (a : Int) (bs : List (BitVec 8)), (a, bs) ∈ fetchLbls (gf.map Prod.fst) →
      ∃ tvs, (Wlabel.LIFetch a tvs, none) ∈ gf ∧ tvs.map Prod.snd = bs := by
  induction gf with
  | nil => intro a bs h; cases h
  | cons it gf ih =>
    intro a bs h
    obtain ⟨l, t⟩ := it
    have ih' := ih (fun base tvs t' hm => hadm base tvs t' (List.mem_cons_of_mem _ hm))
    have hcons : ∀ x, x ∈ gf → x ∈ (l, t) :: gf := fun x hx => List.mem_cons_of_mem _ hx
    cases l
    case LIFetch base tvs =>
      simp only [List.map_cons, PinFetchVal.fetchLbls, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · have ht := hadm a tvs t (List.mem_cons_self ..)
        subst ht
        exact ⟨tvs, List.mem_cons_self .., rfl⟩
      · obtain ⟨tvs', hm, he⟩ := ih' a bs h
        exact ⟨tvs', hcons _ hm, he⟩
    all_goals
      obtain ⟨tvs', hm, he⟩ := ih' a bs h
      exact ⟨tvs', hcons _ hm, he⟩

/-- A shape read at a stretch index gives the cycle's fetch item of its bytes. -/
theorem WeakRvwmoPinBridge6.fetchItemOfView {g : List Eitem} (c : CycFetchRun g) (j : Nat)
    (r : FRd) (a : Int) (hj : (fetchLbls (c.cfFetch.map Prod.fst))[j]? = some (frdView r))
    (ha : r.pa = a) : fetchItem g a r.n r.v := by
  have hm : (r.pa, (List.range r.n).map (fun i => nthByte r.v i)) ∈
      fetchLbls (c.cfFetch.map Prod.fst) := List.mem_of_getElem? hj
  obtain ⟨tvs, hmem, hbs⟩ := WeakRvwmoPinBridge6.itemOfLbls c.cfFetch c.cfAdmin _ _ hm
  refine ⟨tvs, ?_, ?_, ?_⟩
  · rw [c.cfSplit, ← ha]; exact List.mem_append_left _ hmem
  · have := congrArg List.length hbs
    simpa using this
  · intro i hi
    rw [hbs, List.getElem?_map, List.getElem?_range hi]
    rfl

/-- Sail's arm of a shape (the 4-byte read split by its low halfword's `isRVC`). -/
def WeakRvwmoPinBridge6.shArm : FetchShape → FetchArm
  | .s4 _ v => if isRVC (Sail.BitVec.extractLsb v 15 0) = true then .rvc4 v else .base4 v
  | .s2 _ v => .rvc2 v
  | .s22 _ _ lo hi => .base22 lo hi

/-- The announced role and the arm's items of a shape whose `j`-th read is the stretch's `j`-th
fetch label, at `pc + 2 j`. -/
theorem WeakRvwmoPinBridge6.armOfShape {g : List Eitem} (c : CycFetchRun g) (pc : Int)
    (sh : FetchShape) (n : Nat) (w : BitVec n) (hann : sh.ann n w)
    (hidx : ∀ (j : Nat) (r : FRd), sh.reads[j]? = some r →
      (fetchLbls (c.cfFetch.map Prod.fst))[j]? = some (frdView r) ∧ r.pa = pc + 2 * (j : Int)) :
    depsOfIb (ibAnn (ibOfBvn w)).ibBits = (WeakRvwmoPinBridge6.shArm sh).annRole ∧
      (WeakRvwmoPinBridge6.shArm sh).items g pc := by
  cases sh with
  | s4 a v =>
    obtain ⟨e0, ha0⟩ := hidx 0 _ rfl
    have hit := WeakRvwmoPinBridge6.fetchItemOfView c 0 _ pc e0 (by simpa using ha0)
    rcases hann with ⟨he, hr⟩ | ⟨he, hr⟩
    · cases he
      simp only [WeakRvwmoPinBridge6.shArm, hr, Bool.false_eq_true, ↓reduceIte]
      exact ⟨rfl, hit⟩
    · cases he
      simp only [WeakRvwmoPinBridge6.shArm, hr, ↓reduceIte]
      exact ⟨rfl, hit, hr⟩
  | s2 a v =>
    obtain ⟨e0, ha0⟩ := hidx 0 _ rfl
    have hit := WeakRvwmoPinBridge6.fetchItemOfView c 0 _ pc e0 (by simpa using ha0)
    obtain ⟨he, hr⟩ := hann
    cases he
    exact ⟨rfl, hit, hr⟩
  | s22 a1 a2 lo hi =>
    obtain ⟨e0, ha0⟩ := hidx 0 _ rfl
    obtain ⟨e1, ha1⟩ := hidx 1 _ rfl
    have hit0 := WeakRvwmoPinBridge6.fetchItemOfView c 0 _ pc e0 (by simpa using ha0)
    have hit1 := WeakRvwmoPinBridge6.fetchItemOfView c 1 _ (pc + 2) e1 (by simpa using ha1)
    obtain ⟨he, -⟩ := hann
    cases he
    exact ⟨rfl, hit0, hit1⟩

/-- **r1, the certificate**: a real cycle whose fetch reads are at `pc + 2 j` (r2) is a `CycCert`
whose role is the announced role, with `fetchAnnR1` and `fetchPaR2` PROVED. -/
theorem certOfFetchRun {g : List Eitem} (c : CycFetchRun g) (pc : Int) (hpa : fetchPaR2Run pc c)
    (hscan : PinDataflow.dfScan c.role (0, true) (g.map Prod.fst) =
      ((PinDataflow.dfDests c.role).length, true)) :
    ∃ cc : CycCert g, fetchAnnR1 cc ∧ fetchPaR2 pc cc := by
  obtain ⟨sh, hv, hann⟩ := PinFetchVal.fetchAnnOfRun c.cfCpu c.cfTick c.cfRs c.cfFn c.cfIb c.cfD
    (c.cfFetch.map Prod.fst) c.cfN c.cfW c.cfK c.cfRs2 c.cfFn2 c.cfIb2 c.cfD2 c.cfBoot c.cfRun
    c.cfNoInstr c.cfNoSf
  have hidx : ∀ (j : Nat) (r : FRd), sh.reads[j]? = some r →
      (fetchLbls (c.cfFetch.map Prod.fst))[j]? = some (frdView r) ∧ r.pa = pc + 2 * (j : Int) := by
    intro j r hr
    have e : (fetchLbls (c.cfFetch.map Prod.fst))[j]? = some (frdView r) := by
      rw [← hv, List.getElem?_map, hr]; rfl
    exact ⟨e, hpa j _ _ e⟩
  have hrole : c.role = (WeakRvwmoPinBridge6.shArm sh).annRole ∧
      (WeakRvwmoPinBridge6.shArm sh).items g pc :=
    WeakRvwmoPinBridge6.armOfShape c pc sh c.cfN c.cfW hann hidx
  exact ⟨⟨pc, WeakRvwmoPinBridge6.shArm sh, c.role, hrole.2, hscan⟩, hrole.1, rfl⟩

/-! # 3. The alignment over real cycles -/

/-- **r4 OVER REAL CYCLES (NAMED, Q-B5-CYCLE)** (header): PinBridge5's `cycRun` with each retired
cycle a REAL fetch stretch (`CycFetchRun`), its slot scan full at the ANNOUNCED role, its reads
at `pc + 2 j` (r2, named), and the next walk state a `pstep` successor; an interrupted cycle a
fence-free excursion `texcRes` (with FR).  No r1: it is `PinFetchVal.fetchAnnOfRun`. -/
inductive cycRunR (G : Gexec) (i : Nat) (em : Hemission) (own : Bool) :
    List Eitem → PState → List Eitem → PState → Prop where
  | stop (pfx : List Eitem) (s : PState) : cycRunR G i em own pfx s [] s
  | step (pfx : List Eitem) (s : PState) (g : List Eitem) (l : List PState) (s' : PState)
      (mid : List Eitem) (s'' : PState) (c : CycFetchRun g) :
      fetchPaR2Run s.psPc c →
      PinDataflow.dfScan c.role (0, true) (g.map Prod.fst) =
        ((PinDataflow.dfDests c.role).length, true) →
      pstep own s = some l → s' ∈ l →
      cycRunR G i em own (pfx ++ g) s' mid s'' →
      cycRunR G i em own pfx s (g ++ mid) s''
  | trap (pfx : List Eitem) (s : PState) (gx mid : List Eitem) (s'' : PState) :
      texcRes G i em pfx gx → cycRunR G i em own (pfx ++ gx) s mid s'' →
      cycRunR G i em own pfx s (gx ++ mid) s''

/-- **The real alignment is PinBridge5's** (r1 discharged at every step). -/
theorem cycRunOfR (G : Gexec) (i : Nat) (em : Hemission) (own : Bool) :
    ∀ (pfx : List Eitem) (s : PState) (g : List Eitem) (s'' : PState),
      cycRunR G i em own pfx s g s'' → cycRun G i em own pfx s g s'' := by
  intro pfx s g s'' h
  induction h with
  | stop pfx s => exact .stop pfx s
  | step pfx s g l s' mid s'' c hpa hscan hp hm _ ih =>
    obtain ⟨cc, h1, h2⟩ := certOfFetchRun c s.psPc hpa hscan
    exact .step pfx s g l s' mid s'' cc h1 h2 hp hm ih
  | trap pfx s gx mid s'' hx _ ih => exact .trap pfx s gx mid s'' hx ih

/-! # 4. The headlines, r1 discharged -/

/-- **PDep, B5 with r1 discharged (header)**: PinBridge5's `pinSegPinStoreB5` over the real-cycle
alignment `cycRunR` — no `psitesA`, no `psitesT`, no `fetchAnnR1`. -/
theorem pinSegPinStoreB6 (GT : GdexecT) (i : Nat) (row : List Lbl) (p0 : Pexv6)
    (dv : Nat → Efab) (em : Hemission) (sg : Seg) (pcL : Int) (w : Pin) (j k : Nat) (own : Bool)
    (base mid g0 post : List Eitem) (s : PState) (rl : Bool) (a : Int) (v : List (BitVec 8))
    (asrc vsrc : List Dsrc) :
    GT.gtG.gxProg[i]? = some row → hartConf i row p0 dv em →
    (∀ x, x ∈ rowDepsT em.emItems → (((i, x.1.1), (i, x.1.2)), x.2) ∈ GT.gtDeps) →
    sg.sgEntry = (i, j) → sg.sgExit = (i, k) →
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    (pcL, w) ∈ pinsW9a → walkOwn w = some own →
    kFetchText em →
    cycRunR GT.gtG i em own base (pinStart pcL) mid s →
    em.emItems = base ++ mid ++ g0 ++ (Wlabel.LStore rl a v asrc vsrc, some k) :: post →
    g0.all provNeutralb = true →
    dsubb (depsAddr (krole s.psPc)) asrc = true → dsubb (depsVsrc (krole s.psPc)) vsrc = true →
    pstep own s = some [] → wIsFence (kw s.psPc) = false → roleIsStore (krole s.psPc) = true →
    segPinC (forget GT) (gtAd GT.gtG GT.gtDeps) sg := by
  intro hrow hcf hdeps he hx hbase hm hw hft hrun
  exact pinSegPinStoreB5 GT i row p0 dv em sg pcL w j k own base mid g0 post s rl a v asrc vsrc
    hrow hcf hdeps he hx hbase hm hw hft (cycRunOfR GT.gtG i em own base _ mid s hrun)

/-- **PCtrl, B5 with r1 discharged (header)**: PinBridge5's `pinSegPinCtrlB5` over `cycRunR`. -/
theorem pinSegPinCtrlB6 (GT : GdexecT) (i : Nat) (row : List Lbl) (p0 : Pexv6)
    (dv : Nat → Efab) (em : Hemission) (sg : Seg) (pcL : Int) (w : Pin) (j k : Nat) (own : Bool)
    (base mid g0 mid' post : List Eitem) (s : PState) (srcs : List Dsrc) (kc : Option Nat)
    (rl : Bool) (a : Int) (v : List (BitVec 8)) (asrc vsrc : List Dsrc) (tgt : Int) :
    GT.gtG.gxProg[i]? = some row → hartConf i row p0 dv em →
    (∀ x, x ∈ rowDepsT em.emItems → (((i, x.1.1), (i, x.1.2)), x.2) ∈ GT.gtDeps) →
    sg.sgEntry = (i, j) → sg.sgExit = (i, k) →
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    (pcL, w) ∈ pinsW9a → walkOwn w = some own →
    kFetchText em →
    cycRunR GT.gtG i em own base (pinStart pcL) mid s →
    em.emItems = base ++ mid ++ g0 ++ (Wlabel.LCtrl srcs, kc)
      :: (mid' ++ (Wlabel.LStore rl a v asrc vsrc, some k) :: post) →
    g0.all provNeutralb = true →
    dsubb (depsCtrl (krole s.psPc)) srcs = true →
    pstep own s = some [] → wIsFence (kw s.psPc) = false → roleIsStore (krole s.psPc) = false →
    kflowOf s.psPc = .FLbranch tgt →
    segPinC (forget GT) (gtAd GT.gtG GT.gtDeps) sg := by
  intro hrow hcf hdeps he hx hbase hm hw hft hrun
  exact pinSegPinCtrlB5 GT i row p0 dv em sg pcL w j k own base mid g0 mid' post s srcs kc rl a v
    asrc vsrc tgt hrow hcf hdeps he hx hbase hm hw hft (cycRunOfR GT.gtG i em own base _ mid s hrun)

end Weak
