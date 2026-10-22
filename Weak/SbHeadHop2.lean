/-
Weak: **allocproc route P — row H3 continued: THE PER-SITE TABLE of a gated racy read**
(PROGRESS-P.md §HEADHOP2; finding F-P-W3-3 option (a); plan rev 55 row P-W3).  Lean-only, no Rocq
twin.  A PRIMED TWIN: nothing registered imports this file.

**Spec, stated first.**  riscv.cat orders a plain load `r` before a po-later event of its hart only
by rules 4 (fence), 5 (`.aq`), 9–11 (addr/data/ctrl to a WRITE; rule 9 also to reads, but the
emission carries dependency edges INTO WRITES only), 13 (`[M];addr;[M];po;[W]` — in the emission,
"the instruction's earlier loads", `dsLd`) and the trusted residue ((R1), (R2″) [OWN.116]).  Two
plain loads to different bytes are UNORDERED.  So a read-gate-blocked head `r` (`SbOrd.HeadOrdRd`)
is handled per site in one of two ways:
* **static hops** — `WrHop` (every later write gmo-after `r`) plus (A2) (every later waited-on pure
  read past an ordering point, `SbHeadHop.OrdPt`): `fenceNextHop` (the next row event is a
  `fence r,r?w`: main+0x16, vdi+0x36's fall-through, vdi+0x82's back edge — both halves at once),
  `aqNextA2` (the next row event is an `.aq` RMW: holding+0x0's zero arm in `acquire`),
  `wrHopOfCtlR` (rule 11 with READS between the load and its branch: vdi+0x4e's `lbu`),
  `diskWrHop` (a DISK-row read: rule 13's `dsLd` edges — the disk emission has no `LInstr`, so every
  earlier read of the row reaches every later write); `a2OfWindow` ((A2) when every read before the
  next `.aq` RMW is on a QUIET byte: no foreign pending entry, no AMO head — holding+0x0's nonzero
  arm, given (ii) stack custody, (a2-lkcpu) and (iii));
* **never blocked** — `srcGateOfLanded`: a head whose GF sources have all LANDED passes the read gate
  (`PInv.rd` + CoWR against own pending entries), so `HeadOrdRd` is vacuous at it (the PTE sites
  under Q-6M-PTE (a) custody, vdi+0x4e/+0x5a and vdi+0x36's taken / vdi+0x82's fall-through arm under
  the virtio index/descriptor discipline, every disk-row read under the descriptor discipline).
**`headOrdRdOfTable`** assembles `HeadOrdRd` (value gate) from the per-head disjunction.
`notWaitedOwn` is the Weak-side half of stack custody (ii): an OWN pending entry never makes a read
waited-on (its GF source is co-after the entry, hence unlanded).

  §1  `A2At`, `fenceNextHop`, `aqNextA2`, `wrHopOfCtlR`.
  §2  the disk row: `admDiskKeep`, `diskLdKeep`, `diskRdKeep`, **`diskWrHop`**, `diskWrHopCZ`.
  §3  never blocked: `SrcLanded`, **`srcGateOfLanded`**, `valGateOfLanded`; quiet bytes: `ByteQuiet`,
      **`notWaitedOwn`**, **`a2OfWindow`**; **`headOrdRdOfTable`**.
  §4  the named interfaces as statements: `HoldZero` ((iii)), `FrameQuiet` ((ii)).
  §5  image facts (`decide +kernel`): `aluTo`, `vdiShape`, `ptePctrlAlu`.

Spec mark: FAITHFUL (proof organisation over riscv.cat rules 4, 5, 11, 13 as the emission carries
them and the trusted residue; no new trusted text).  The NAMED inputs (FAITHFUL statements, WEAKER
while named) are listed in PROGRESS-P.md §HEADHOP2.  Lean-only helpers `SbHeadHop2.*`.
-/
import Weak.SbHeadHop
import Weak.SbDevSt
import Weak.WeakRvwmoPinBridge2

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open KernelPinsDef
open WeakRvwmoConf (Dstate dstep)
open Lbl SbWalk SbAgree SbReplay SbOrd

/-! # 1. Static hops at a class graph -/

/-- (A2) at row `x`'s head: every waited-on pure read po-after it is past an ordering point. -/
def SbHeadHop2.A2At (G : Gexec) (dev : List Geid) (w : WS) (x : Nat) : Prop :=
  ∀ m, m ∈ G.gxGmo → m.1 = x → (hd w x).2 < m.2 → waitedOn G dev w m →
    gisR G m = true → gisW G m = false → SbHeadHop.OrdPt G (hd w x) m

/-- **THE NEXT ROW EVENT IS A `fence r,r?w`** (rule 4): `WrHop`, and every later read is past an
ordering point (the fence).  main+0x16 (`fence r,rw`), vdi+0x36's fall-through and vdi+0x82's back
edge (both reach vdi+0x3e's `fence iorw,iorw`; the branch between is no event). -/
theorem SbHeadHop2.fenceNextHop (G : Gexec) (hc : CatH G) (i j : Nat) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) (pw : Bool)
    (hl : gxLbl G (i, j) = some (LLoad aq base ts vs))
    (hf : gxLbl G (i, j + 1) = some (LFence true pw true true)) :
    SbHeadHop.WrHop G (i, j) ∧
      ∀ m, m.1 = i → j < m.2 → gisR G m = true → SbHeadHop.OrdPt G (i, j) m := by
  refine ⟨SbHeadHop.wrHopOfFence G hc i j (j + 1) aq base ts vs pw true hl hf (by omega)
    (fun k h1 h2 => absurd h2 (by omega)), ?_⟩
  intro m hm1 hm2 hr
  have hne : m.2 ≠ j + 1 := by
    intro h
    have hm : m = (i, j + 1) := Prod.ext hm1 h
    rw [hm] at hr
    simp [gisR, hf, lbIsR] at hr
  exact ⟨(i, j + 1), rfl, by show j < j + 1; omega, by show j + 1 < m.2; omega,
    .inr (.inl ⟨pw, true, hf⟩)⟩

/-- **THE NEXT ROW EVENT IS AN `.aq` RMW** (rule 5 after it): (A2) — the RMW itself is a write, every
later read is past it.  holding+0x0's zero arm in `acquire` (`li a0,0; ret; bnez a0; mv; amoswap.w.aq`:
no event between). -/
theorem SbHeadHop2.aqNextA2 (G : Gexec) (dev : List Geid) (w : WS) (x : Nat)
    (hA : ∃ rl base ts rvs wvs kc,
      gxLbl G (x, (hd w x).2 + 1) = some (LRmw true rl base ts rvs wvs kc)) :
    SbHeadHop2.A2At G dev w x := by
  obtain ⟨rl, base, ts, rvs, wvs, kc, hA⟩ := hA
  intro m _ hm1 hm2 _ _ hw
  have hne : m.2 ≠ (hd w x).2 + 1 := by
    intro h
    have hm : m = (x, (hd w x).2 + 1) := Prod.ext hm1 h
    rw [hm] at hw
    simp [gisW, hA, lbIsW] at hw
  exact ⟨(x, (hd w x).2 + 1), rfl, by show (hd w x).2 < (hd w x).2 + 1; omega,
    by show (hd w x).2 + 1 < m.2; omega, .inl ⟨rl, base, ts, rvs, wvs, kc, hA⟩⟩

/-- **(A1) BY RULE 11 WITH READS BETWEEN** (`SbHeadHop.wrHopOfCtl` generalised): the emission prefix
`P` that puts row position `j` into `dsCtl` may carry later row positions, provided none of them is a
WRITE of the row (vdi+0x4e: the `lbu` of vdi+0x5a sits between the `lw` and the `bnez`). -/
theorem SbHeadHop2.wrHopOfCtlR (G : Gexec) (deps : List (Geid × Geid)) (hdg : gdepsGmo G deps)
    (i : Nat) (row : List Lbl) (hrow : G.gxProg[i]? = some row) (p0 : Pexv6) (dvi dvo : Nat → Efab)
    (tq : Nat → Bool) (em : Hemission) (hem : hartConff i row p0 dvi dvo tq em)
    (hdeps : ∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ deps)
    (j : Nat) (P R : List Eitem) (hes : em.emItems = P ++ R) (hctl : j ∈ (dsRun dsInit P).dsCtl)
    (htagW : ∀ it, it ∈ P → ∀ t, it.2 = some t → j < t → ∀ lb, row[t]? = some lb → lbIsW lb = false) :
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
        have := htagW x hmem m.2 (by rw [← hx]) hjk lm hrm
        rw [this] at hwm
        cases hwm
  have hrd : (j, m.2) ∈ rowDeps em.emItems := by
    apply rowDepsItem _ pre (l, some m.2) post _ hsp
    rw [hd]
    exact dedgesCtl _ _ _ _ _ hjk hpre
  have h := hdg _ (hdeps _ hrd)
  have hm : ((i, m.2) : Geid) = m := Prod.ext hm1 rfl
  rw [hm] at h
  exact h

/-! # 2. The disk row: rule 13's `dsLd` edges (no `LInstr` on the disk row) -/

/-- A disk agent's administrative run stays a disk agent and keeps `dsLd` (no `LInstr`). -/
theorem SbHeadHop2.admDiskKeep (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel) (pa : Pexv6)
    (da : Efab) (b : Bool) :
    WeakRvwmoFab.admRunT instr p d ls pa da b → (∃ dp, p = .PDisk dp) →
    (∃ dp, pa = .PDisk dp) ∧ ∀ (s : Dstate) (j : Nat), j ∈ s.dsLd → j ∈ (dsRun s (eadm ls)).dsLd := by
  intro h
  induction h with
  | ATnil p d => intro hp; exact ⟨hp, fun s j hj => hj⟩
  | ATcons p d l p1 d1 ls p' d' b _ hs _ ih =>
    intro hp
    obtain ⟨dp, rfl⟩ := hp
    obtain ⟨dp1, rfl, -⟩ := SbDevSt.stepDisk dp d l p1 d1 hs
    obtain ⟨hpa, hk⟩ := ih ⟨dp1, rfl⟩
    refine ⟨hpa, fun s j hj => ?_⟩
    have hkl : keepsLdb (l, none) = true := by
      rcases SbDevSt.stepLbl dp d l _ d1 hs with h | ⟨_, _, _, h⟩ | h | ⟨_, _, h⟩ | h <;>
        (subst h; rfl)
    show j ∈ (dsRun s ((l, none) :: eadm ls)).dsLd
    rw [dsRunCons]
    exact hk _ j (dstepLdMono s (l, none) j hkl hj)

/-- On a disk emission, a row position `j < k` in `dsLd` reaches every later write of the row. -/
theorem SbHeadHop2.diskLdKeep (dvi dvo : Nat → Efab) (tq : Nat → Bool) (k : Nat) (ws : Wstate)
    (row : List Lbl) (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemitf dvi dvo tq k ws row p es pfin → (∃ dp, p = .PDisk dp) →
    ∀ (s : Dstate) (j : Nat), j ∈ s.dsLd → j < k →
      ∀ (n : Nat) (lb : Lbl), row[n]? = some lb → lbIsW lb = true → (j, k + n) ∈ rowDepsAux s es := by
  intro h
  induction h with
  | HFnil => intro _ s j _ _ n lb hn; simp at hn
  | HFone k ws lb row p ls pa da l p' es pfin b har hre hst _ _ ih =>
    intro hp s j hj hjk n lbn hn hw
    obtain ⟨⟨dpa, rfl⟩, hk⟩ := SbHeadHop2.admDiskKeep _ _ _ _ _ _ _ har hp
    obtain ⟨dp', rfl, -⟩ := SbDevSt.stepDisk dpa da l p' (dvo k) hst
    have hj1 := hk s j hj
    rw [WeakRvwmoPinBridge.rowDepsAuxApp]
    apply List.mem_append_right
    show (j, k + n) ∈ (dstep (dsRun s (eadm ls)) (l, some k)).2 ++
      rowDepsAux (dstep (dsRun s (eadm ls)) (l, some k)).1 es
    have hpr := hre.2.2.2
    cases n with
    | zero =>
      apply List.mem_append_left
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst hn
      rcases SbDevSt.stepLbl dpa da l _ _ hst with h | ⟨aq, base, tvs, h⟩ | h | ⟨base, data, h⟩ | h
      · subst h; simp only [projLbl, Option.some.injEq] at hpr; subst hpr; simp [lbIsW] at hw
      · subst h; simp only [projLbl, Option.some.injEq] at hpr; subst hpr; simp [lbIsW] at hw
      · subst h; simp only [projLbl, Option.some.injEq] at hpr; subst hpr; simp [lbIsW] at hw
      · subst h
        show (j, k) ∈ dedges (dsRun s (eadm ls)) k [] []
        exact dedgesIntro _ _ _ _ _ hjk (by simp [dsrcsPos, hj1])
      · subst h; simp [projLbl] at hpr
    | succ n =>
      apply List.mem_append_right
      have hkl : keepsLdb (l, some k) = true := by
        rcases SbDevSt.stepLbl dpa da l _ _ hst with h | ⟨_, _, _, h⟩ | h | ⟨_, _, h⟩ | h <;>
          (subst h; rfl)
      have := ih ⟨dp', rfl⟩ (dstep (dsRun s (eadm ls)) (l, some k)).1 j (dstepLdMono _ _ j hkl hj1)
        (by omega) n lbn hn hw
      rw [show k + (n + 1) = k + 1 + n by omega]
      exact this
  | HFpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin b1 b2 har1 hre hst1 _ _ _ _ _ =>
    intro hp
    obtain ⟨⟨dp, rfl⟩, -⟩ := SbHeadHop2.admDiskKeep _ _ _ _ _ _ _ har1 hp
    exact absurd hre (SbDevSt.noPair dp da l1 pm dm pm2 ws lb l2 hst1)

/-- On a disk emission, every READ position reaches every later WRITE position (rule 13 `dsLd`). -/
theorem SbHeadHop2.diskRdKeep (dvi dvo : Nat → Efab) (tq : Nat → Bool) (k : Nat) (ws : Wstate)
    (row : List Lbl) (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemitf dvi dvo tq k ws row p es pfin → (∃ dp, p = .PDisk dp) →
    ∀ (s : Dstate) (jr jw : Nat) (lbr lbw : Lbl), jr < jw → row[jr]? = some lbr → lbIsR lbr = true →
      row[jw]? = some lbw → lbIsW lbw = true → (k + jr, k + jw) ∈ rowDepsAux s es := by
  intro h
  induction h with
  | HFnil => intro _ s jr jw lbr lbw _ hr; simp at hr
  | HFone k ws lb row p ls pa da l p' es pfin b har hre hst _ htl ih =>
    intro hp s jr jw lbr lbw hlt hr hrr hw hww
    obtain ⟨⟨dpa, rfl⟩, -⟩ := SbHeadHop2.admDiskKeep _ _ _ _ _ _ _ har hp
    obtain ⟨dp', rfl, -⟩ := SbDevSt.stepDisk dpa da l p' (dvo k) hst
    rw [WeakRvwmoPinBridge.rowDepsAuxApp]
    apply List.mem_append_right
    show (k + jr, k + jw) ∈ (dstep (dsRun s (eadm ls)) (l, some k)).2 ++
      rowDepsAux (dstep (dsRun s (eadm ls)) (l, some k)).1 es
    apply List.mem_append_right
    obtain ⟨jw', rfl⟩ : ∃ jw', jw = jw' + 1 := ⟨jw - 1, by omega⟩
    have hpr := hre.2.2.2
    cases jr with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
      subst hr
      have hkin : k ∈ (dstep (dsRun s (eadm ls)) (l, some k)).1.dsLd := by
        rcases SbDevSt.stepLbl dpa da l _ _ hst with h | ⟨aq, base, tvs, h⟩ | h | ⟨base, data, h⟩ | h
        · subst h; simp only [projLbl, Option.some.injEq] at hpr; subst hpr; simp [lbIsR] at hrr
        · subst h; exact List.mem_cons_self ..
        · subst h; simp only [projLbl, Option.some.injEq] at hpr; subst hpr; simp [lbIsR] at hrr
        · subst h; simp only [projLbl, Option.some.injEq] at hpr; subst hpr; simp [lbIsR] at hrr
        · subst h; simp [projLbl] at hpr
      have := SbHeadHop2.diskLdKeep _ _ _ _ _ _ _ _ _ htl ⟨dp', rfl⟩ _ k hkin (by omega) jw' lbw hw hww
      rw [Nat.add_zero, show k + (jw' + 1) = k + 1 + jw' by omega]
      exact this
    | succ jr =>
      have := ih ⟨dp', rfl⟩ (dstep (dsRun s (eadm ls)) (l, some k)).1 jr jw' lbr lbw (by omega) hr hrr
        hw hww
      rw [show k + (jr + 1) = k + 1 + jr by omega, show k + (jw' + 1) = k + 1 + jw' by omega]
      exact this
  | HFpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin b1 b2 har1 hre hst1 _ _ _ _ _ =>
    intro hp
    obtain ⟨⟨dp, rfl⟩, -⟩ := SbHeadHop2.admDiskKeep _ _ _ _ _ _ _ har1 hp
    exact absurd hre (SbDevSt.noPair dp da l1 pm dm pm2 ws lb l2 hst1)

/-- **(A1) FOR EVERY DISK-ROW READ** (rule 13 as the emission carries it: the disk program has no
`LInstr`, so `dsLd` accumulates every earlier read of the row and every disk store emits an edge from
each): every po-later write of the row is gmo-after the read. -/
theorem SbHeadHop2.diskWrHop (G : Gexec) (deps : List (Geid × Geid)) (hdg : gdepsGmo G deps)
    (i : Nat) (row : List Lbl) (hrow : G.gxProg[i]? = some row) (dp : Option (DM Dres))
    (dvi dvo : Nat → Efab) (tq : Nat → Bool) (em : Hemission)
    (hem : hartConff i row (.PDisk dp) dvi dvo tq em)
    (hdeps : ∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ deps)
    (j : Nat) (lbr : Lbl) (hj : row[j]? = some lbr) (hr : lbIsR lbr = true) :
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
  have hem' : hemitf dvi dvo tq 0 wsInit row (.PDisk dp) em.emItems em.emFin := hem
  have h := SbHeadHop2.diskRdKeep _ _ _ _ _ _ _ _ _ hem' ⟨dp, rfl⟩ dsInit j m.2 lbr lm hm2 hj hr hrm hwm
  rw [Nat.zero_add, Nat.zero_add] at h
  have h2 := hdg _ (hdeps _ h)
  have hm : ((i, m.2) : Geid) = m := Prod.ext hm1 rfl
  rw [hm] at h2
  exact h2

/-- `diskWrHop` at xv6's bundle (rows `≥ NCPU` boot as the idle disk). -/
theorem SbHeadHop2.diskWrHopCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (hconf : GraphFabConf.gfexecConfZF boot d0 fab GF) (hdb : ∀ i, NCPU ≤ i → boot i = .PDisk none)
    (hdg : gdepsGmo GF.gfGd.gdG GF.gfGd.gdDeps) (e : Geid) (l : Lbl) :
    NCPU ≤ e.1 → gxLbl GF.gfGd.gdG e = some l → lbIsR l = true → SbHeadHop.WrHop GF.gfGd.gdG e := by
  intro hN hl hr
  obtain ⟨row, hrow, hre⟩ := SbHeadHop.lblOf _ e l hl
  obtain ⟨em, dvi, dvo, tq, hem, -, -, -, hdep⟩ := hconf.2.2.2 e.1 row hrow
  have hem' : hartConff e.1 row (.PDisk none) dvi dvo tq em := by rw [← hdb e.1 hN]; exact hem
  exact SbHeadHop2.diskWrHop _ _ hdg e.1 row hrow none dvi dvo tq em hem' hdep e.2 l hre hr

/-! # 3. Never blocked; quiet bytes; the table -/

/-- Every GF source of event `e` has LANDED at walk state `w` (or is the image). -/
def SbHeadHop2.SrcLanded (G : Gexec) (w : WS) (e : Geid) : Prop :=
  ∀ a t v, greadsByte G e a t v → landedSrc G w a t

section Inv

variable {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid} {w : WS}

/-- **A HEAD WHOSE GF SOURCES HAVE LANDED PASSES THE SOURCE GATE**: no own pending entry covers a
read byte (its GF source would be co-after that entry, hence unlanded — CoWR + the landed list is a
gmo-prefix), and an unrealized read with a landed source reads the member-latest (`PInv.rd`). -/
theorem SbHeadHop2.srcGateOfLanded (hP : PInv N img G X dev w) (hc : CatH G) (x : Nat) (aq : Bool)
    (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G (hd w x) = some (LLoad aq base ts vs)) (hland : SbHeadHop2.SrcLanded G w (hd w x)) :
    srcGate G w x base ts vs := by
  intro j t v htj hvj
  have hrd : greadsByte G (hd w x) (accAddr base j) t v := ⟨_, base, ts, vs, j, hl, rfl, htj, hvj, rfl⟩
  have he : ¬ realized w (hd w x) := fun h => by unfold realized hd at h; simp at h
  have hL := hland _ t v hrd
  cases hf : SbCand.fwdByte (w.σ.sb x) (accAddr base j) with
  | none => exact .inr ⟨rfl, hP.rd _ _ t _ hrd he hL⟩
  | some v' =>
    exfalso
    rcases fwdRel (w.pend x) (accAddr base j) with ⟨-, h2⟩ | ⟨p, hp, -, h2, -⟩
    · rw [← hP.inv.sb x, hf] at h2; cases h2
    · rw [← hP.inv.sb x, hf] at h2
      have hpr := pendRealized hP x p hp
      unfold realized at hpr
      obtain ⟨rl', base', vs', kc', hl', -, -⟩ := pendLbl hP x p hp
      have hsw : gwritesByte G (x, p.1) (accAddr base j) v' := pendWritesV hP x p _ v' hp h2.symm
      have hsW := gwritesOf G _ _ _ hc.wf hsw
      have hsm : (x, p.1) ∈ G.gxGmo := lblGmo G _ _ hc.wf hl' rfl
      have hpo : WeakRvwmoGraph.gpo G (x, p.1) (hd w x) := SBAcq.gpoOf G _ _ _ _ hl' hl rfl hpr
      have hsNW : (x, p.1) ∉ wrAtW w (accAddr base j) :=
        fun h' => hP.inv.pendGmo x p hp (List.mem_filter.1 h').1
      have hle := (hc.lv _ _ t v hrd).2 _ v' hsw (.inr hpo)
      rcases hL with rfl | ⟨s, hs, hsl⟩
      · have := gwixPos G _ hsW; omega
      · obtain ⟨hsG, hsix⟩ := gwriteAtInv G _ s hc.wf.1 hs
        by_cases hne : s = (x, p.1)
        · rw [hne] at hsl; exact hsNW hsl
        · have hix : gwix G (x, p.1) < gwix G s := by
            rcases Nat.lt_or_ge (gwix G (x, p.1)) (gwix G s) with h | h
            · exact h
            · exact absurd (gwixInj G _ _ hc.wf.1 hsG hsW (by omega)) hne
          have hgp := (gwixGposLt G _ _ hc.wf.1 hsW hsG).1 hix
          have hsGa : (x, p.1) ∈ wrAtG G (accAddr base j) :=
            List.mem_filter.2 ⟨hsm, (gwrBOf G _ _ _ hc.wf hsw).1⟩
          exact hsNW (landedDown G w _ _ s (hP.pf.2 _) hc.wf.1 hsl hsGa hgp)

/-- ... hence the VALUE gate (`valGateMono`). -/
theorem SbHeadHop2.valGateOfLanded (hP : PInv N img G X dev w) (hc : CatH G) (himg : G.gxImg = img)
    (x : Nat) (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G (hd w x) = some (LLoad aq base ts vs)) (hland : SbHeadHop2.SrcLanded G w (hd w x)) :
    valGate w x base ts vs :=
  valGateMono hP hc.wf hc.lv himg x aq base ts vs hl
    (SbHeadHop2.srcGateOfLanded hP hc x aq base ts vs hl hland)

/-- A QUIET byte for row `x`: no OTHER row's pending entry writes it, no AMO head writes it and
([OWN.151], `SbOrd.waitedOn`'s device clause) no DEVICE-ROW STORE head writes it. -/
def SbHeadHop2.ByteQuiet (G : Gexec) (w : WS) (x : Nat) (a : Int) : Prop :=
  (∀ i p, p ∈ w.pend i → gwrB G a (i, p.1) = true → i = x) ∧
  (∀ y aq rl base ts rvs wvs kc, gxLbl G (hd w y) = some (LRmw aq rl base ts rvs wvs kc) →
    gwrB G a (hd w y) = false) ∧
  (∀ y rl base vs kc, NCPU ≤ y → gxLbl G (hd w y) = some (LStore rl base vs kc) →
    gwrB G a (hd w y) = false)

/-- **AN OWN PENDING ENTRY NEVER MAKES A READ WAITED-ON** (the Weak half of stack custody (ii) and
of (a2-lkcpu)): an unrealized pure read of row `x` (no fabric member) whose bytes are quiet for `x`
is not waited-on — an own pending entry on a byte is po-before the read, so the read's GF source is
co-at-or-after it (CoWR), hence unlanded, hence not the member-latest. -/
theorem SbHeadHop2.notWaitedOwn (hP : PInv N img G X dev w) (hc : CatH G) (m : Geid)
    (hmr : ¬ realized w m) (hdev : m ∉ dev) (hw : gisW G m = false)
    (hq : ∀ a t v, greadsByte G m a t v → SbHeadHop2.ByteQuiet G w m.1 a) :
    ¬ waitedOn G dev w m := by
  rintro (h | h | ⟨a, t, v, hrd, hsl, hwr⟩)
  · exact hdev h
  · rw [hw] at h; cases h
  · obtain ⟨hfor, hamo, hdevq⟩ := hq a t v hrd
    rcases hwr with ⟨i, p, hp, hpw⟩ | ⟨y, aq, rl, base, ts, rvs, wvs, kc, hl, hpw⟩ |
      ⟨y, rl, base, vs, kc, hy, hl, hpw⟩
    · have hi := hfor i p hp hpw
      subst hi
      obtain ⟨u, hsw⟩ := gwrBTo G _ a hpw
      have hpr := pendRealized hP m.1 p hp
      obtain ⟨rl', base', vs', kc', hl', -, -⟩ := pendLbl hP m.1 p hp
      have hsW := gwritesOf G _ _ _ hc.wf hsw
      have hsm : (m.1, p.1) ∈ G.gxGmo := lblGmo G _ _ hc.wf hl' rfl
      obtain ⟨lm, hlm⟩ : ∃ lm, gxLbl G m = some lm := by
        obtain ⟨lm, _, _, _, _, hlm, -⟩ := hrd
        exact ⟨lm, hlm⟩
      have hpo : WeakRvwmoGraph.gpo G (m.1, p.1) m :=
        SBAcq.gpoOf G _ _ _ _ hl' hlm rfl (by
          have h1 : p.1 < (w.rows m.1).length := hpr
          have h2 : ¬ m.2 < (w.rows m.1).length := hmr
          show p.1 < m.2
          omega)
      have hsNW : (m.1, p.1) ∉ wrAtW w a :=
        fun h' => hP.inv.pendGmo m.1 p hp (List.mem_filter.1 h').1
      have hle := (hc.lv _ _ t v hrd).2 _ u hsw (.inr hpo)
      rcases hsl with ⟨rfl, -⟩ | ⟨s, hs, hlast⟩
      · have := gwixPos G _ hsW; omega
      · have hsl' : s ∈ wrAtW w a := List.mem_of_getLast? hlast
        obtain ⟨hsG, hsix⟩ := gwriteAtInv G _ s hc.wf.1 hs
        by_cases hne : s = (m.1, p.1)
        · rw [hne] at hsl'; exact hsNW hsl'
        · have hix : gwix G (m.1, p.1) < gwix G s := by
            rcases Nat.lt_or_ge (gwix G (m.1, p.1)) (gwix G s) with h | h
            · exact h
            · exact absurd (gwixInj G _ _ hc.wf.1 hsG hsW (by omega)) hne
          have hgp := (gwixGposLt G _ _ hc.wf.1 hsW hsG).1 hix
          have hsGa : (m.1, p.1) ∈ wrAtG G a := List.mem_filter.2 ⟨hsm, hpw⟩
          exact hsNW (landedDown G w _ _ s (hP.pf.2 _) hc.wf.1 hsl' hsGa hgp)
    · rw [hamo y aq rl base ts rvs wvs kc hl] at hpw
      cases hpw
    · rw [hdevq y rl base vs kc hy hl] at hpw
      cases hpw

/-- **(A2) FROM A QUIET WINDOW**: if every pure read of row `x` strictly between its head and the next
`.aq` RMW (row position `kA`) reads only quiet bytes, then (A2) holds — reads in the window are not
waited-on (`notWaitedOwn`), the RMW is a write, reads after it are past it.  holding+0x0's NONZERO arm:
the window is holding's/mycpu's frame traffic and holding+0x12's `ld lk->cpu` (quiet by (ii) and
(a2-lkcpu)), and it ends at `acquire+0x1c`'s `amoswap.w.aq` exactly when holding returns 0 ((iii)). -/
theorem SbHeadHop2.a2OfWindow (hP : PInv N img G X dev w) (hc : CatH G) (x kA : Nat)
    (hxN : x < NCPU) (hdev : ∀ e, e ∈ dev → e.1 < NCPU → gisIo G e = true)
    (hA : ∃ rl base ts rvs wvs kc, gxLbl G (x, kA) = some (LRmw true rl base ts rvs wvs kc))
    (hjk : (hd w x).2 < kA)
    (hwin : ∀ m, m.1 = x → (hd w x).2 < m.2 → m.2 < kA → gisR G m = true → gisW G m = false →
      ∀ a t v, greadsByte G m a t v → SbHeadHop2.ByteQuiet G w x a) :
    SbHeadHop2.A2At G dev w x := by
  obtain ⟨rl, base, ts, rvs, wvs, kc, hA⟩ := hA
  intro m _ hm1 hm2 hwo hr hw
  rcases Nat.lt_trichotomy m.2 kA with h | h | h
  · exfalso
    have hmr : ¬ realized w m := by
      have h1 : (w.rows x).length < m.2 := hm2
      unfold realized
      rw [hm1]
      omega
    have hio : gisIo G m = false := by
      unfold gisR at hr; unfold gisIo
      cases hlm : gxLbl G m with
      | none => simp [hlm] at hr
      | some lm => rw [hlm] at hr; cases lm <;> simp_all [lbIsR, lbIsIo]
    have hmd : m ∉ dev := fun hm => by
      have := hdev m hm (by rw [hm1]; exact hxN)
      rw [hio] at this; cases this
    exact SbHeadHop2.notWaitedOwn hP hc m hmr hmd hw
      (fun a t v hrd => by rw [hm1]; exact hwin m hm1 hm2 h hr hw a t v hrd) hwo
  · exfalso
    have hm : m = (x, kA) := Prod.ext hm1 h
    rw [hm] at hw
    simp [gisW, hA, lbIsW] at hw
  · exact ⟨(x, kA), rfl, hjk, h, .inl ⟨rl, base, ts, rvs, wvs, kc, hA⟩⟩

/-- **ROW H3 FROM THE PER-HEAD TABLE** (value gate): every non-exempt plain-load head is either
NEVER BLOCKED (the value gate passes — e.g. its GF sources have landed, `valGateOfLanded`) or has the
static hops (`WrHop` and (A2)). -/
theorem SbHeadHop2.headOrdRdOfTable (hc : CatH G)
    (hr1 : ∀ s m, WeakRvwmoGraph.gpo G s m → gmem G s → gisIo G s = false → gisIo G m = true →
      gmoLt G s m)
    (hr2'' : ∀ s m, WeakRvwmoGraph.gpo G s m → gisIo G s = true → gisR G m = true → gmoLt G s m)
    (hT : ∀ x base ts vs, gxLbl G (hd w x) = some (LLoad false base ts vs) → ¬ X (hd w x) →
      valGate w x base ts vs ∨ (SbHeadHop.WrHop G (hd w x) ∧ SbHeadHop2.A2At G dev w x)) :
    HeadOrdRd G X valGate dev w := by
  apply SbHeadHop.headOrdRdOf G X valGate dev w hc hr1 hr2''
  · intro x base ts vs hl hX hrd
    rcases hT x base ts vs hl hX with h | h
    · exact absurd h hrd
    · exact h.1
  · intro x base ts vs hl hX hrd
    rcases hT x base ts vs hl hX with h | h
    · exact absurd h hrd
    · exact h.2

end Inv

/-! # 4. The named interfaces, as statements -/

/-- **(iii) "the row's `holding` returns 0 at `acquire`"** (NAMED; the panic path excluded), GF form:
every `holding+0x12` load `r` (`ld a5,16(a0)`, 8 bytes at `L + 16`) of a row inside a call from
`acquire(L)` — the predicate `AcqCpuRd r L`, the realization's label ↔ pc transport (T) — reads a
value other than its hart's own `&cpus[r.1]` (`cpuB r.1`, its 8 little-endian bytes).  Truth for
xv6 (CoWR): the hart's po-latest own store to `L + 16` before `r` is its last `release(L)`'s
`sd zero,16(s1)` (no recursive `acquire`), so `r`'s source is that store or co-later; every co-later
store is another hart's `acquire` (`sd mycpu`, its own pointer) or `release`/`initlock` (0), and the
`cpus` pointers are distinct.  PROVED at `cpuB` from its floor decomposition — `SbHoldZero.holdZeroOf`
(residuals `CpuWordWin` / `CpuFloor` / `NotHolder`, `Weak/SbHoldZero.lean`); the `lk->cpu` half of the
[OWN.124] exemption's GF side (`SbHoldX.cpuGFOfHoldZero`). -/
def SbHeadHop2.HoldZero (G : Gexec) (cpuB : Nat → List (BitVec 8)) (AcqCpuRd : Geid → Int → Prop) :
    Prop :=
  ∀ r L base ts vs, AcqCpuRd r L → gxLbl G r = some (LLoad false base ts vs) → base = L + 16 →
    vs ≠ cpuB r.1

/-- **(ii) stack custody at a walk state** (NAMED), the form `notWaitedOwn` consumes: every byte of
row `x`'s LIVE kernel-stack frames (`Frame x a`, from the realization's state map: the frame bytes
below/at the hart's `sp` of the stack it runs on) is quiet for `x` — no OTHER hart's store-buffer
entry writes it, no AMO head writes it.  Truth for xv6: a process's kernel stack is written only by
the hart running it; a hand-off goes through `p->lock` (`sched`/`scheduler`: `swtch` then
`release(&p->lock)`, a `fence rw,w` release), whose landing follows every earlier store of the old
hart (epoch order) and precedes the new hart's realized `amoswap.w.aq` (its source landed); `stack0`
slices are per hart; AMOs touch only lock words (`SilSite.amoOnlySilent`). -/
def SbHeadHop2.FrameQuiet (G : Gexec) (Frame : Nat → Int → Prop) (w : WS) : Prop :=
  ∀ x a, Frame x a → SbHeadHop2.ByteQuiet G w x a

/-! # 5. Image facts (`decide +kernel`) -/

/-- `pc`'s instruction is no load, no store, no fence and falls through. -/
def SbHeadHop2.aluAt (pc : Int) : Bool :=
  !roleIsLoad (krole pc) && !roleIsStore (krole pc) && !wIsFence (kw pc) &&
    (match kflowOf pc with
     | .FLnone => true
     | _ => false)

/-- From `pc`, only `aluAt` instructions until `b` (within `n` instructions). -/
def SbHeadHop2.aluTo : Nat → Int → Int → Bool
  | 0, _, _ => false
  | n + 1, pc, b => decide (pc = b) || (SbHeadHop2.aluAt pc && SbHeadHop2.aluTo n (pc + wSize (kw pc)) b)

/-- **THE FOUR `virtio_disk_intr` CENSUS SITES** (census §3.5): vdi+0x36's `beq` is the NEXT
instruction, its fall-through is vdi+0x3e's `fence` (iorw,iorw; taken: vdi+0x8a, `release`);
vdi+0x82's `bne` is the next instruction, its TAKEN arm is vdi+0x3e (fall-through: vdi+0x8a);
vdi+0x4e (`lw` of `used->ring[id].id`) reaches its pinned `bnez` (0x80005d86) through ALU
instructions and ONE load — vdi+0x5a's `lbu` (no store) — whose next instruction is that `bnez`. -/
theorem SbHeadHop2.vdiShape :
    SilSite.sym KernelSyms.«virtio_disk_intr» 0x36 +
        wSize (kw (SilSite.sym KernelSyms.«virtio_disk_intr» 0x36)) = 0x80005d62 ∧
      kflowOf 0x80005d62 = .FLbranch (SilSite.sym KernelSyms.«virtio_disk_intr» 0x8a) ∧
      0x80005d62 + wSize (kw 0x80005d62) = SilSite.sym KernelSyms.«virtio_disk_intr» 0x3e ∧
      wIsFence (kw (SilSite.sym KernelSyms.«virtio_disk_intr» 0x3e)) = true ∧
      wFencePr (kw (SilSite.sym KernelSyms.«virtio_disk_intr» 0x3e)) = true ∧
      wFencePw (kw (SilSite.sym KernelSyms.«virtio_disk_intr» 0x3e)) = true ∧
      wFenceSr (kw (SilSite.sym KernelSyms.«virtio_disk_intr» 0x3e)) = true ∧
      wFenceSw (kw (SilSite.sym KernelSyms.«virtio_disk_intr» 0x3e)) = true ∧
      SilSite.sym KernelSyms.«virtio_disk_intr» 0x82 +
        wSize (kw (SilSite.sym KernelSyms.«virtio_disk_intr» 0x82)) = 0x80005dae ∧
      kflowOf 0x80005dae = .FLbranch (SilSite.sym KernelSyms.«virtio_disk_intr» 0x3e) ∧
      SbHeadHop2.aluTo 8 (SilSite.sym KernelSyms.«virtio_disk_intr» 0x4e +
        wSize (kw (SilSite.sym KernelSyms.«virtio_disk_intr» 0x4e)))
        (SilSite.sym KernelSyms.«virtio_disk_intr» 0x5a) = true ∧
      roleIsLoad (krole (SilSite.sym KernelSyms.«virtio_disk_intr» 0x5a)) = true ∧
      SilSite.sym KernelSyms.«virtio_disk_intr» 0x5a +
        wSize (kw (SilSite.sym KernelSyms.«virtio_disk_intr» 0x5a)) = 0x80005d86 ∧
      roleIsBranch (krole 0x80005d86) = true := by
  decide +kernel

/-- **THE SEVEN `PCtrl` PTE SITES** (census §3.4; `ismapped+0x10` is `PResidue`, `uvmclear+0x10` is
`PDep` — no rule-11 hop to every later write): between the load and its pinned branch only ALU
instructions. -/
theorem SbHeadHop2.ptePctrlAlu :
    [(SilSite.sym KernelSyms.«walk» 0x32, (0x80000fe8 : Int)),
      (SilSite.sym KernelSyms.«walkaddr» 0x1c, 0x8000106e),
      (SilSite.sym KernelSyms.«mappages» 0x4a, 0x800010d0),
      (SilSite.sym KernelSyms.«uvmunmap» 0x5e, 0x800012c4),
      (SilSite.sym KernelSyms.«freewalk» 0x2a, 0x80001408),
      (SilSite.sym KernelSyms.«copyout» 0x82, 0x80001648),
      (SilSite.sym KernelSyms.«uvmcopy» 0x36, 0x800014a4)].all
      (fun pb => SbHeadHop2.aluTo 8 (pb.1 + wSize (kw pb.1)) pb.2 && roleIsBranch (krole pb.2)) =
      true := by
  decide +kernel

end Weak
