/-
Weak: **allocproc route P — row H3 part (a1): THE STATIC HOPS of a gated racy read** (PROGRESS-P.md
§HEADHOP; finding F-P-W3-3 option (a); plan rev 55 row P-W3).  Lean-only, no Rocq twin.  A PRIMED
TWIN: nothing registered imports this file.

**Spec, stated first.**  riscv.cat: two plain loads of a hart to different bytes are UNORDERED (no
ppo rule; rule 11 is `ctrl; [W]` only), so a gated racy read `r` (a non-exempt plain-load head the
read gate blocks, `SbOrd.HeadOrdRd`) is gmo-before a po-later event `m` of its row only through a
ppo/residue path.  This file proves every such path the xv6 text provides and isolates what is left:
* **writes** — rule 11 (`ctrl; [W]`) through the emission's dependency edges (`rowDeps`, whose
  `dsCtl` set is CUMULATIVE: once `r`'s value reaches a branch, EVERY po-later write carries the
  edge), or rule 4 through a `fence r,*` with the `w` successor bit (`SbHeadHop.WrHop`,
  `SbHeadHop.wrHopOfCtl`, `SbHeadHop.wrHopOfFence`);
* **I/O events** — the trusted residue's (R1);
* **reads** — only past an ORDERING POINT (`SbHeadHop.OrdPt`): an `.aq` RMW (rule 11 into it, then
  rule 5 — the `amoswap.w.aq` at `acquire+0x1c` after `holding+0x0`'s zero arm), a `fence r,r*`
  (rule 4 — `main+0x18`'s `fence r,rw` after the `started` read `main+0x16`), or an I/O event
  ((R1) then (R2″) [OWN.116]).
A waited-on READ po-after a blocked head with NO ordering point between is the residue: it is NOT
RVWMO-orderable (`SbStuck.l8`), and its exclusion is part (a2) — the lock protocol at the realized
prefix, a NAMED interface of this file's reduction (`SbHeadHop.headOrdRdOf`'s `hA2`; its MachCSL
statement in PROGRESS-P.md §HEADHOP).

  §1  the generic hops at a class graph: `WrHop`, `OrdPt`, `rdOrd`, **`headOrdRdOf`** (`HeadOrdRd`
      from (A1) "every blocked head has `WrHop`" and (A2) "every waited-on pure read po-after a
      blocked head is past an ordering point").
  §2  (A1) FROM THE EMISSION: `hemitfWrItem` (a row write has a write item carrying its `dedges`),
      **`wrHopOfCtl`** (a load whose row position is in `dsCtl` at a prefix holding no later row
      position has `WrHop`, by `gdepsGmo` over the bundle's `rowDeps` clause), **`wrHopOfFence`**
      (rule 4); the pin-walk bridge **`ctlOfPsites`** (`KernelPins`' `PCtrl` certificate puts the
      read in `dsCtl` at its branch).
  §3  the image facts of the two census sites with a static hop (`decide +kernel`): `holding+0x0`'s
      `bnez` is the NEXT instruction (`holding0CtrlNext`), `main+0x16`'s next instruction is the
      `fence r,rw` (`main16FenceNext`).

Spec mark: FAITHFUL (proof organisation over riscv.cat rules 4, 5, 11 and the trusted residue's (R1),
(R2″)); no new trusted text; the named inputs are `hA1`'s per-head emission shape (the realization's
label ↔ instruction transport, like `SbOrd.ImgFacts`) and `hA2` (part (a2)).  Lean-only helpers
`SbHeadHop.*`.
-/
import Weak.SbOrd
import Weak.SilSiteTab

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open KernelPinsDef
open WeakRvwmoConf (Dstate dstep)
open Lbl SbWalk SbAgree SbReplay SbOrd

/-! # 1. The generic hops -/

/-- Every po-later WRITE of `r`'s row is gmo-after `r` (rule 11 / rule 4 at `r`'s site). -/
def SbHeadHop.WrHop (G : Gexec) (r : Geid) : Prop :=
  ∀ m, WeakRvwmoGraph.gpo G r m → gisW G m = true → gmoLt G r m

/-- An ORDERING POINT strictly between `r` and `m` on `r`'s row: an `.aq` RMW, a fence with the `r`
predecessor and `r` successor bits, or an I/O event. -/
def SbHeadHop.OrdPt (G : Gexec) (r m : Geid) : Prop :=
  ∃ o : Geid, o.1 = r.1 ∧ r.2 < o.2 ∧ o.2 < m.2 ∧
    ((∃ rl base ts rvs wvs kc, gxLbl G o = some (LRmw true rl base ts rvs wvs kc)) ∨
     (∃ pw sw, gxLbl G o = some (LFence true pw true sw)) ∨
     gisIo G o = true)

theorem SbHeadHop.gpoOfLbl (G : Gexec) (a b : Geid) (la lb : Lbl) :
    gxLbl G a = some la → gxLbl G b = some lb → a.1 = b.1 → a.2 < b.2 → WeakRvwmoGraph.gpo G a b :=
  fun ha hb h1 h2 => ⟨h1, h2, by rw [ha]; rfl, by rw [hb]; rfl⟩

/-- **A READ PAST AN ORDERING POINT** is gmo-after a plain-load `r` with `WrHop`: through an `.aq`
RMW (`WrHop` into it, rule 5 out), a `fence r,r*` (rule 4), or an I/O event ((R1), (R2″)). -/
theorem SbHeadHop.rdOrd (G : Gexec) (r m : Geid) (hc : CatH G)
    (hr1 : ∀ s m, WeakRvwmoGraph.gpo G s m → gmem G s → gisIo G s = false → gisIo G m = true →
      gmoLt G s m)
    (hr2'' : ∀ s m, WeakRvwmoGraph.gpo G s m → gisIo G s = true → gisR G m = true → gmoLt G s m)
    (hW : SbHeadHop.WrHop G r) (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G r = some (LLoad aq base ts vs)) (lm : Lbl) (hlm : gxLbl G m = some lm)
    (hrm : lbIsR lm = true) (hmx : m.1 = r.1) (hpt : SbHeadHop.OrdPt G r m) : gmoLt G r m := by
  obtain ⟨o, ho1, ho2, ho3, h⟩ := hpt
  rcases h with ⟨rl, ob, ots, orv, owv, okc, hlo⟩ | ⟨pw, sw, hlo⟩ | hio
  · have hro : gmoLt G r o :=
      hW o (SbHeadHop.gpoOfLbl G r o _ _ hl hlo ho1.symm ho2) (by unfold gisW; rw [hlo]; rfl)
    have hom : gmoLt G o m :=
      SBAcq.acqLt G o m _ lm hc.ppo hlo hlm (ho1.trans hmx.symm) ho3 rfl rfl
        (by unfold lbIsMem; rw [hrm]; rfl)
    exact gmoLtTrans _ _ _ _ hro hom
  · have hlo' : gxLbl G (r.1, o.2) = some (LFence true pw true sw) := by
      rw [← ho1]; exact hlo
    exact SBAcq.fenceLt G r m _ lm o.2 true pw true sw hc.ppo hl hlm hmx.symm ho2 ho3 hlo'
      (by simp [lbIsR]) (by simp [hrm])
  · obtain ⟨kd, ob, ovs, hlo⟩ := GraphFabResidue.gisIoLbl G o hio
    have hro : gmoLt G r o :=
      hr1 r o (SbHeadHop.gpoOfLbl G r o _ _ hl hlo ho1.symm ho2)
        ⟨_, hl, by simp [lbIsMem, lbIsR]⟩ (by unfold gisIo; rw [hl]; rfl) hio
    have hom : gmoLt G o m :=
      hr2'' o m (SbHeadHop.gpoOfLbl G o m _ _ hlo hlm (ho1.trans hmx.symm) ho3) hio
        (by unfold gisR; rw [hlm]; exact hrm)
    exact gmoLtTrans _ _ _ _ hro hom

/-- **ROW H3 FROM THE HOPS**: `HeadOrdRd` at a walk state from (A1) every read-gate-blocked
non-exempt plain-load head has `WrHop`, and (A2) every unrealized-later WAITED-ON pure read of its
row is past an ordering point.  Later I/O events: (R1); later writes: (A1); later reads: (A2) +
`rdOrd`. -/
theorem SbHeadHop.headOrdRdOf (G : Gexec) (X : Geid → Prop) (rdG : RdG) (dev : List Geid) (w : WS)
    (hc : CatH G)
    (hr1 : ∀ s m, WeakRvwmoGraph.gpo G s m → gmem G s → gisIo G s = false → gisIo G m = true →
      gmoLt G s m)
    (hr2'' : ∀ s m, WeakRvwmoGraph.gpo G s m → gisIo G s = true → gisR G m = true → gmoLt G s m)
    (hA1 : ∀ x base ts vs, gxLbl G (hd w x) = some (LLoad false base ts vs) → ¬ X (hd w x) →
      ¬ rdG w x base ts vs → SbHeadHop.WrHop G (hd w x))
    (hA2 : ∀ x base ts vs, gxLbl G (hd w x) = some (LLoad false base ts vs) → ¬ X (hd w x) →
      ¬ rdG w x base ts vs →
      ∀ m, m ∈ G.gxGmo → m.1 = x → (hd w x).2 < m.2 → waitedOn G dev w m →
        gisR G m = true → gisW G m = false → SbHeadHop.OrdPt G (hd w x) m) :
    HeadOrdRd G X rdG dev w := by
  intro x base ts vs hl hX hrd m hm hmx hlt hwo
  obtain ⟨lm, hlm, hmm⟩ := gwfGmoMem G m hc.wf hm
  have hpo : WeakRvwmoGraph.gpo G (hd w x) m :=
    SbHeadHop.gpoOfLbl G _ m _ lm hl hlm (by unfold hd; exact hmx.symm) hlt
  by_cases hio : lbIsIo lm = true
  · exact hr1 _ m hpo ⟨_, hl, by simp [lbIsMem, lbIsR]⟩ (by unfold gisIo; rw [hl]; rfl)
      (by unfold gisIo; rw [hlm]; exact hio)
  by_cases hw : lbIsW lm = true
  · exact hA1 x base ts vs hl hX hrd m hpo (by unfold gisW; rw [hlm]; exact hw)
  have hr : lbIsR lm = true := by
    unfold lbIsMem at hmm
    simp only [Bool.or_eq_true] at hmm
    rcases hmm with (h | h) | h
    · exact h
    · exact absurd h hw
    · exact absurd h hio
  exact SbHeadHop.rdOrd G _ m hc hr1 hr2'' (hA1 x base ts vs hl hX hrd) false base ts vs hl lm hlm hr
    (by unfold hd; exact hmx)
    (hA2 x base ts vs hl hX hrd m hm hmx hlt hwo (by unfold gisR; rw [hlm]; exact hr)
      (by unfold gisW; rw [hlm]; exact Bool.eq_false_iff.2 hw))

/-! # 2. (A1) from the emission -/

/-- A row WRITE has a write item in its emission, tagged with its row position, whose `dstep`
emits that position's `dedges` (an `LStore` / `LRmw` item, or a pair's `LExStore` half). -/
theorem SbHeadHop.hemitfWrItem (dvi dvo : Nat → Efab) (tq : Nat → Bool) (k : Nat) (ws : Wstate)
    (row : List Lbl) (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemitf dvi dvo tq k ws row p es pfin →
    ∀ (n : Nat) (lb : Lbl), row[n]? = some lb → lbIsW lb = true →
      ∃ (pre : List Eitem) (l : Wlabel) (post : List Eitem) (asrc vsrc : List Dsrc),
        es = pre ++ (l, some (k + n)) :: post ∧
        ∀ s, (dstep s (l, some (k + n))).2 = dedges s (k + n) asrc vsrc := by
  intro h
  induction h with
  | HFnil => intro n lb hn; simp at hn
  | HFone k ws lb row p ls pa da l p' es pfin b _ hre _ _ _ ih =>
    intro n lbn hn hw
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst hn
      have hpr := hre.2.2.2
      refine ⟨eadm ls, l, es, ?_⟩
      cases l <;> simp only [projLbl, Option.some.injEq, reduceCtorEq] at hpr <;>
        (try (subst hpr; simp [lbIsW] at hw))
      · exact ⟨_, _, by simp, fun _ => rfl⟩
      · exact ⟨_, _, by simp, fun _ => rfl⟩
      · exact ⟨_, _, by simp, fun _ => rfl⟩
    | succ n =>
      obtain ⟨pre, l', post, asrc, vsrc, hes, hd⟩ := ih n lbn hn hw
      refine ⟨eadm ls ++ (l, some k) :: pre, l', post, asrc, vsrc, ?_, ?_⟩
      · rw [hes, show k + (n + 1) = k + 1 + n by omega]; simp
      · rw [show k + (n + 1) = k + 1 + n by omega]; exact hd
  | HFpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin b1 b2 _ hre _ _ _ _ _ ih =>
    intro n lbn hn hw
    cases n with
    | zero =>
      obtain ⟨aq, rl, base, tvs, data, asrc1, asrc2, vsrc2, rfl, rfl, -, -, -⟩ := hre
      refine ⟨eadm ls1 ++ (Wlabel.LExLoad aq base tvs asrc1, some k) :: eadm ls2,
        Wlabel.LExStore rl base data asrc2 vsrc2, es, asrc2, vsrc2, by simp, fun _ => rfl⟩
    | succ n =>
      obtain ⟨pre, l', post, asrc, vsrc, hes, hd⟩ := ih n lbn hn hw
      refine ⟨eadm ls1 ++ (l1, some k) :: (eadm ls2 ++ (l2, some k) :: pre), l', post, asrc, vsrc,
        ?_, ?_⟩
      · rw [hes, show k + (n + 1) = k + 1 + n by omega]; simp
      · rw [show k + (n + 1) = k + 1 + n by omega]; exact hd

theorem SbHeadHop.lblOf (G : Gexec) (e : Geid) (l : Lbl) :
    gxLbl G e = some l → ∃ row, G.gxProg[e.1]? = some row ∧ row[e.2]? = some l := by
  unfold gxLbl
  intro h
  rcases hr : G.gxProg[e.1]? with _ | row
  · rw [hr] at h; cases h
  · rw [hr] at h; exact ⟨row, rfl, h⟩

/-- **(A1) BY RULE 11, FROM THE EMISSION**: on row `i` (emission `em`, whose `rowDeps` are dependency
edges of the graph, gmo-forward by `gdepsGmo`), a row position `j` in the `dsCtl` set at an emission
prefix `P` that carries no row position above `j` (no memory event between the read and its branch)
has `WrHop`: every po-later write's item lies after `P`, and its `dedges` carry `(j, ·)`. -/
theorem SbHeadHop.wrHopOfCtl (G : Gexec) (deps : List (Geid × Geid)) (hdg : gdepsGmo G deps)
    (i : Nat) (row : List Lbl) (hrow : G.gxProg[i]? = some row) (p0 : Pexv6) (dvi dvo : Nat → Efab)
    (tq : Nat → Bool) (em : Hemission) (hem : hartConff i row p0 dvi dvo tq em)
    (hdeps : ∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ deps)
    (j : Nat) (P R : List Eitem) (hes : em.emItems = P ++ R) (hctl : j ∈ (dsRun dsInit P).dsCtl)
    (htag : ∀ it, it ∈ P → ∀ t, it.2 = some t → t ≤ j) :
    SbHeadHop.WrHop G (i, j) := by
  intro m hpo hw
  obtain ⟨hm1, hm2, -, -⟩ := hpo
  obtain ⟨lm, hlm, hwm⟩ : ∃ lm, gxLbl G m = some lm ∧ lbIsW lm = true := by
    unfold gisW at hw
    rcases h : gxLbl G m with _ | lm
    · rw [h] at hw; cases hw
    · rw [h] at hw; exact ⟨lm, rfl, hw⟩
  obtain ⟨row', hrow', hrm⟩ := SbHeadHop.lblOf G m lm hlm
  rw [← hm1] at hrow'
  rw [hrow] at hrow'
  cases hrow'
  have hem' : hemitf dvi dvo tq 0 wsInit row p0 em.emItems em.emFin := hem
  obtain ⟨pre, l, post, asrc, vsrc, hsp, hd⟩ :=
    SbHeadHop.hemitfWrItem _ _ _ _ _ _ _ _ _ hem' m.2 lm hrm hwm
  rw [Nat.zero_add] at hsp hd
  have hjk : j < m.2 := hm2
  -- the write item lies after `P`
  have hpre : j ∈ (dsRun dsInit pre).dsCtl := by
    rw [hes] at hsp
    rcases List.append_eq_append_iff.1 hsp with ⟨a', hpa, -⟩ | ⟨c', hpc, hc'⟩
    · rw [hpa, dsRunApp]; exact dsRunCtlSub _ _ hctl
    · cases c' with
      | nil => rw [List.append_nil] at hpc; rw [← hpc]; exact hctl
      | cons x c'' =>
        simp only [List.cons_append, List.cons.injEq] at hc'
        obtain ⟨hx, -⟩ := hc'
        have hmem : x ∈ P := by rw [hpc]; simp
        have := htag x hmem m.2 (by rw [← hx])
        omega
  have hrd : (j, m.2) ∈ rowDeps em.emItems := by
    apply rowDepsItem _ pre (l, some m.2) post _ hsp
    rw [hd]
    exact dedgesCtl _ _ _ _ _ hjk hpre
  have h := hdg _ (hdeps _ hrd)
  have hm : ((i, m.2) : Geid) = m := Prod.ext hm1 rfl
  rw [hm] at h
  exact h

/-- **(A1) BY RULE 4**: a load at row position `j` followed, before any write of its row, by a fence
with the `r` predecessor and `w` successor bits has `WrHop`. -/
theorem SbHeadHop.wrHopOfFence (G : Gexec) (hc : CatH G) (i j kf : Nat) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) (pw sr : Bool)
    (hl : gxLbl G (i, j) = some (LLoad aq base ts vs))
    (hf : gxLbl G (i, kf) = some (LFence true pw sr true)) (hjf : j < kf)
    (hno : ∀ k, j < k → k < kf → gisW G (i, k) = false) :
    SbHeadHop.WrHop G (i, j) := by
  intro m hpo hw
  obtain ⟨hm1, hm2, -, -⟩ := hpo
  obtain ⟨lm, hlm, hwm⟩ : ∃ lm, gxLbl G m = some lm ∧ lbIsW lm = true := by
    unfold gisW at hw
    rcases h : gxLbl G m with _ | lm
    · rw [h] at hw; cases hw
    · rw [h] at hw; exact ⟨lm, rfl, hw⟩
  have hm : ((i, m.2) : Geid) = m := Prod.ext hm1 rfl
  rcases Nat.lt_trichotomy m.2 kf with h | h | h
  · have := hno m.2 hm2 h
    rw [hm, hw] at this
    cases this
  · rw [← hm, h, hf] at hlm
    cases hlm
    simp [lbIsW] at hwm
  · exact SBAcq.fenceLt G (i, j) m _ lm kf true pw sr true hc.ppo hl hlm hm1 hjf h hf
      (by simp [lbIsR]) (by simp [hwm])

/-- **THE PIN-WALK BRIDGE (`PCtrl`)**: at the fall-through walk alignment of `KernelPins`' control
certificate (`psites`: the emission prefix `pre` is the base plus the walk from the load to its
branch `pc'`), the branch's control item puts the load's row position in `dsCtl`
(`pctrlRowDepsSup`'s first half). -/
theorem SbHeadHop.ctlOfPsites (pcL pc' : Int) (own : Bool) (j : Nat) (base pre : List Eitem)
    (srcs : List Dsrc) (kc : Option Nat) :
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    psites pcL own base pre (Wlabel.LCtrl srcs, kc) pc' →
    dsubb (depsCtrl (krole pc')) srcs = true →
    pinnedb pinFuel pcL (.PCtrl pc' own) = true →
    j ∈ (dsRun dsInit (pre ++ [(Wlabel.LCtrl srcs, kc)])).dsCtl := by
  intro hbase hsite hcov hpin
  obtain ⟨t, hw, htn⟩ := pinnedbCtrlInv pinFuel pcL pc' own hpin
  obtain ⟨r, hr, ht⟩ := srcsTaintedReg _ _ htn
  have hj := checkerTaintSubProvProof pcL j own base (pre ++ [(Wlabel.LCtrl srcs, kc)]) hbase
    pre _ [] pc' t r rfl hsite hw ht
  rw [dsRunApp, dsRunCons, dsRunNil]
  exact dstepCtlIntro _ _ _ _ _ (dsubbElem _ _ _ hcov hr) hj

/-! # 3. The image facts of the two census sites with a static hop -/

/-- `holding+0x0` (`lw a5,0(a0)`, census row 3.1, `PCtrl`): the certifying `bnez` is the NEXT
instruction — no memory access between the read and its branch. -/
theorem SbHeadHop.holding0CtrlNext :
    (SilSite.sym KernelSyms.«holding» 0x0, Pin.PCtrl 0x80000bf4 false) ∈ pins ∧
    SilSite.sym KernelSyms.«holding» 0x0 + wSize (kw (SilSite.sym KernelSyms.«holding» 0x0)) =
      0x80000bf4 ∧
    roleIsLoad (krole (SilSite.sym KernelSyms.«holding» 0x0)) = true := by
  decide +kernel

/-- `main+0x16` (`lw` of `started`, census row 3.2, `PFence`): the next instruction is `main+0x18`'s
`fence r,rw` (predecessor `r`, successors `r` and `w`). -/
theorem SbHeadHop.main16FenceNext :
    SilSite.sym KernelSyms.«main» 0x16 + wSize (kw (SilSite.sym KernelSyms.«main» 0x16)) =
      SilSite.sym KernelSyms.«main» 0x18 ∧
    wIsFence (kw (SilSite.sym KernelSyms.«main» 0x18)) = true ∧
    wFencePr (kw (SilSite.sym KernelSyms.«main» 0x18)) = true ∧
    wFenceSr (kw (SilSite.sym KernelSyms.«main» 0x18)) = true ∧
    wFenceSw (kw (SilSite.sym KernelSyms.«main» 0x18)) = true := by
  decide +kernel

end Weak
