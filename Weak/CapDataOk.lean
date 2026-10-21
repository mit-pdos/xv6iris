/-
Weak: **W11-F row 6d (the DATA half), part 2 — `dataOkRF` and `fetchOkRF` (ii) FROM THE EXPORTED
NON-STUCKNESS** ([OWN.115] (a), plan rev 57 row 6d; `PROGRESS-6d.md`).  Lean-only, no Rocq twin.

The merged route took the cycle obligations from the run interfaces `PinDataOk.dataRealized` /
`PinDataOk.fetchOkRealized` (`Weak/PinDataOk.lean:149`, `Weak/PinDataOkIF4.lean:203`: satp, TLB, PMP,
MPRV, the base register, the PTE answers — facts that live only inside each hart's WP and are NOT
exported).  [OWN.115] made a kernel-mode synchronous exception STUCK in the machine
(`MachCSL.kExcWrite`, `MachCSL/Lang.lean:1337`), so the exported `Reducible` refutes one at every
realized state (`MState.excOk_of_reducible`, `Lang.lean:1858`; armed by `nsteps_kArm`,
`MachCSL/DiskOf.lean:293`).  This file turns that into the two cycle obligations, with NO
`dataRealized`/`fetchOkRealized`:

* §1 **`CapDataOk.cycReal`** (NAMED, the SimRel transport = P-W6's state map read at the member, the
  kind of `CapFrame.floorByteReal`): every in-cycle state of a walk cycle is realized by a MachCSL
  configuration reachable from power-on — the same Sail monad on a live hart thread, the same
  `cur_privilege`.  `CapDataOk.causeIntrOf`: at such a configuration a cause write from Supervisor mode
  carries bit 63.
* §2 **`CapDataOk.matchedAll`**: from the cycle's start every realized in-cycle state is matched by
  `CapDataTrap.cyPSailOf`'s predicate (no exception stop is reached: a stop is in Supervisor mode, hence
  refuted) — a strong induction over the run's prefixes supplying `cyDRun`'s per-read premise.
* §3 **`CapDataOk.noExcAt`** (no realized walk-cycle state is at an exception's cause write),
  **`CapDataOk.dataOkRFOfReal`**, **`CapDataOk.fetchOkRFiiOfReal`**, **`CapDataOk.cycFactsAtQ1`** (the
  `CapF2.cycFactsAt` replacement) and **`CapDataOk.cycRunOfHartConffQ1`** (the `CapF5.cycRunOfHartConffR`
  replacement): `fetchOkRealized` and `dataRealized` are GONE; what stays is `fetchRealized` (the
  fetch-address half `fetchOkRF` (i), Q1-c [OWN.144]) and `cycReal`.

What it consumes: `fetchOkRF` (i) — the fetch-address oracle `kAa` (without it the fetched word need not
be the kernel's and the decoded instruction could write `cur_privilege`), exactly as the merged
`PinDataOk.dataOkRFOf` does.

Spec: FAITHFUL — the stuck instrument removes only transitions the WP proves are never needed
([OWN.115]); `cycReal` is a run fact of the realized member (TRUE under route P: MachCSL's `hartStep`
admits every boundary tick and every `choose` answer, so every pf run of the member's labels is realized
by the member's schedule — `PROGRESS-6d.md` §0 (3), F-6d-1).  Every name is `Weak.CapDataOk.*`.
-/
import Weak.CapDataTrap
import Weak.CapF5
import Weak.MachOfPf

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Wlabel KernelPinsDef
open WeakRvwmoPinBridge3 (preach)
open WeakRvwmoPinBridge4 (walkOwn)
open PinWalkTab PinTrap
open SailCycleOrderK PinCycRun PinDataflow
open MachOfPf (MRun)
open Iris.ProgramLogic

namespace CapDataOk
open PinDataOk CapDataTrap

/-! ## 1. The transport (NAMED) and the machine fact -/

/-- **THE REALIZATION OF A WALK CYCLE (NAMED INTERFACE, header; P-W6's state map at the member)**:
every in-cycle state of a walk cycle at `pc` (started at the boundary's first `LInstr`) is realized
by a MachCSL configuration reachable from `([power], g0)`: the hart's thread runs the same Sail monad,
live, with the same `cur_privilege`. -/
def cycReal (g0 : GState) (p0 : Pexv6) (d0 : Efab) (em : Hemission) (pc : Int) : Prop :=
  ∀ (pfx : List Eitem) (ls0 : List Wlabel) (q : Pexv6) (d1 : Efab) (ls1 : List Wlabel) (cpu : CPU)
    (m : SailM Unit) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (dm : Efab),
    LInstr ∉ ls0 → cycStart p0 d0 em pfx pc ls0 q d1 → cycIn em pfx ls0 ls1 →
    irun ls1 q d1 (.PHart cpu m rs fn ib) dm →
    ∃ (n : Nat) (κ : List Obs) (t : List Expr) (g : GState) (gen : Nat),
      MRun n ([Expr.power], g0) κ (t, g) ∧ Expr.hart gen cpu m ∈ t ∧ threadLive g gen ∧
      g.m.regs cpu .cur_privilege = rs .cur_privilege

/-- The exported non-stuckness (`MachOfPf.HypsC.safe`'s shape). -/
def safeFrom (g0 : GState) : Prop :=
  ∀ (n : Nat) (κs : List Obs) (t : List Expr) (g : GState),
    MRun n ([Expr.power], g0) κs (t, g) → ∀ e, e ∈ t → PrimStep.Reducible (e, g)

/-- **[OWN.115] AT A REALIZED STATE** (header): at a configuration reachable from a powered-off
`g0`, a live hart thread about to write a cause register from Supervisor mode writes the interrupt
bit. -/
theorem causeIntrOf {g0 : GState} (hp0 : g0.pow = false) (hsafe : safeFrom g0) {n : Nat}
    {κ : List Obs} {t : List Expr} {g : GState} {gen : Nat} {cpu : CPU} {r : Register}
    {v : RegisterType r} {k : Unit → SailM Unit} (hm : MRun n ([Expr.power], g0) κ (t, g))
    (he : Expr.hart gen cpu (.impure (.ok (.regWrite r v)) k) ∈ t) (hl : threadLive g gen)
    (hS : g.m.regs cpu .cur_privilege = Privilege.Supervisor) (hc : cyS r = true) :
    causeBit r v = true := by
  have hok := MState.excOk_of_reducible hl (hsafe n κ t g hm _ he)
  have harm : g.m.kArm = true :=
    nsteps_kArm hm (fun h => absurd (h.symm.trans hp0) (by decide)) hl.1
  have hk := hok harm
  simp only [cyS, Bool.or_eq_true, decide_eq_true_eq] at hc
  rcases hc with rfl | rfl
  · have e : (!(v.getLsbD 63) && privSup (g.m.regs cpu .cur_privilege)) = false := hk
    rw [hS] at e
    show v.getLsbD 63 = true
    simpa [privSup] using e
  · have e : (!(v.getLsbD 63) && privSup (g.m.regs cpu .cur_privilege)) = false := hk
    rw [hS] at e
    show v.getLsbD 63 = true
    simpa [privSup] using e

/-! ## 2. Every realized in-cycle state is matched -/

/-- The run's matched-state conclusion. -/
def matched (pc : Int) (cpu : CPU) (pm : Pexv6) : Prop :=
  ∃ (m1 : SailM Unit) (rs1 : RegFile) (fn1 : Option (Bool × Bool × Bool × Bool)) (ib1 : Ibch)
    (st1 : CySt), pm = .PHart cpu m1 rs1 fn1 ib1 ∧
    cyDB gB dT kA (kAa pc) privS (fun _ _ => True) m1 st1 ∧ cyMatch st1 rs1 ib1

theorem labDT (l : Wlabel) : labD dT l := by
  cases l <;> first | exact fun _ _ _ _ _ => trivial | trivial

set_option maxHeartbeats 4000000 in
/-- **EVERY REALIZED IN-CYCLE STATE IS MATCHED** (header). -/
theorem matchedAll (p0 : Pexv6) (d0 : Efab) (em : Hemission) (pc : Int)
    (htext : textLo ≤ pc ∧ pc + 3 < textHi) (a : instruction) (hdec : PinWalkTab.decS pc = some a)
    (hfetch1 : fetchCyR1 pc) (hexec : execCyAt pc) (hnw : dfNwRole (krole pc)) (hft : kFetchText em)
    (hfeN : ∀ a tvs t, (LIFetch a tvs, t) ∈ em.emItems → t = none)
    (hfi : PinFetchPa.fetchOkRFi p0 d0 em pc)
    (g0 : GState) (hp0 : g0.pow = false) (hsafe : safeFrom g0) (hreal : cycReal g0 p0 d0 em pc)
    (pfx : List Eitem) (ls0 : List Wlabel) (q : Pexv6) (d1 : Efab) (hni : LInstr ∉ ls0)
    (hcs : cycStart p0 d0 em pfx pc ls0 q d1) :
    ∃ cpu : CPU, ∀ (ls1 : List Wlabel) (pm : Pexv6) (dm : Efab), cycIn em pfx ls0 ls1 →
      irun ls1 q d1 pm dm → matched pc cpu pm := by
  have hcs0 := hcs
  obtain ⟨p, d, hbd, hrun0, cpu, tick, rs', rfl⟩ := hcs
  obtain ⟨-, -, cpu0, rs, fn, ib, rfl, hkinv⟩ := hbd
  rcases pureSplit _ _ _ _ _ hrun0 cpu0 rs fn ib rfl hkinv.2.2 with hni' |
    ⟨ls0', ls1', rs'', tick', d1'', hls, -, -, hr0, hr1, hag, hrb'⟩
  · exact absurd (List.mem_append_right _ List.mem_cons_self) hni'
  obtain ⟨hs1, hs2⟩ := splitLast LInstr ls0 ls0' ls1' hni hls
  subst ls0'
  subst ls1'
  obtain ⟨hq, -⟩ := pevrunNil hr1
  rw [hq] at hcs0 ⊢
  clear hq
  have hkinv' : kInv pc rs'' := PinCycRun.kInvAgree pc rs rs'' hag hrb' hkinv
  let st0 : CySt := ⟨rs'', [], false, ⟨OpRoles.ORnone, [], 0, true⟩⟩
  have hcy0 := cyPSailOf pc htext a hdec hfetch1 hexec hnw tick' st0 ⟨hkinv', rfl, rfl, rfl⟩
  have hm0 : cyMatch st0 rs'' ibNone := ⟨fun _ _ => rfl, hrb', hrb', rfl, rfl, rfl⟩
  refine ⟨cpu0, ?_⟩
  -- a realized exception stop is refuted
  have hstop : ∀ (la : List Wlabel) (m1 : SailM Unit) (rs1 : RegFile)
      (fn1 : Option (Bool × Bool × Bool × Bool)) (ib1 : Ibch) (dd : Efab) (st1 : CySt),
      cycIn em pfx ls0 la → irun la (.PHart cpu0 (riscvStep tick') rs'' none ibNone) d1
        (.PHart cpu0 m1 rs1 fn1 ib1) dd →
      cyDStopAt privS st1 m1 → cyMatch st1 rs1 ib1 → False := by
    intro la m1 rs1 fn1 ib1 dd st1 hcin hira hst hm1
    obtain ⟨r, v, k, rfl, hsr, hcb, hT⟩ := hst
    obtain ⟨n, κ, t, g, gen, hmr, he, hl, hpr⟩ := hreal pfx ls0 _ d1 la cpu0 _ rs1 fn1 ib1 dd hni hcs0 hcin hira
    have hS : g.m.regs cpu0 .cur_privilege = Privilege.Supervisor := by
      rw [hpr, hm1.1 .cur_privilege (by decide)]; exact hT
    have := causeIntrOf hp0 hsafe hmr he hl hS hsr
    rw [hcb] at this; cases this
  suffices H : ∀ (n : Nat) (ls1 : List Wlabel), ls1.length ≤ n → cycIn em pfx ls0 ls1 →
      ∀ (pm : Pexv6) (dm : Efab), irun ls1 (.PHart cpu0 (riscvStep tick') rs'' none ibNone) d1 pm dm →
        matched pc cpu0 pm from fun ls1 pm dm hcin hir => H ls1.length ls1 (Nat.le_refl _) hcin pm dm hir
  intro n
  induction n with
  | zero =>
    intro ls1 hlen hcin pm dm hir
    have e : ls1 = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hlen)
    subst e
    have hp : pm = .PHart cpu0 (riscvStep tick') rs'' none ibNone :=
      PinRunJ.prunJNil (irunPrunJ _ _ _ _ _ hir)
    exact ⟨_, _, _, _, st0, hp, hcy0, hm0⟩
  | succ n ih =>
    intro ls1 hlen hcin pm dm hir
    obtain ⟨rest, hes, hpre⟩ := hcin
    have hsub : ∀ l', l' ∈ ls1 → l' ∈ em.emItems.map Prod.fst := by
      intro l' hl'
      obtain ⟨t, ht⟩ := hpre
      rw [hes, List.map_append]
      refine List.mem_append_right _ ?_
      rw [← ht]
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ hl'))
    have hP : ∀ ls1a l ls2 pmm dmm, ls1 = ls1a ++ l :: ls2 →
        irun ls1a (.PHart cpu0 (riscvStep tick') rs'' none ibNone) d1 pmm dmm →
        runPrem gB dT kA (kAa pc) st0.fe.length pmm ls1a l := by
      intro ls1a l ls2 pmm dmm e hira
      have hla : ls1a.length ≤ n := by
        have := congrArg List.length e
        simp only [List.length_append, List.length_cons] at this
        omega
      obtain ⟨m1, rs1, fn1, ib1, st1, hpm, -, hm1⟩ :=
        ih ls1a hla (cycInPrefix em pfx ls0 ls1 ls1a ls2 l ⟨rest, hes, hpre⟩ e) pmm dmm hira
      refine ⟨?_, labDT l, ?_⟩
      · intro cpu r k rs fn ib hpe
        rw [hpm] at hpe
        injection hpe with e1 e2 e3 e4 e5
        subst e3
        exact hm1.2.1 r
      · intro a' tvs hl'
        subst hl'
        refine ⟨?_, PinCycRun.kAOfText em hft hfeN a' tvs (hsub _ (by rw [e]; simp))⟩
        show a' = pc + 2 * ((0 + (feLabs ls1a).length : Nat) : Int)
        rw [Nat.zero_add]
        have hir' : irun ((ls1a ++ [LIFetch a' tvs]) ++ ls2)
            (.PHart cpu0 (riscvStep tick') rs'' none ibNone) d1 pm dm := by
          rw [e] at hir; simpa using hir
        obtain ⟨pm', dm', hira'⟩ := PinCycRun.irunPrefix _ ls2 _ _ _ _ hir'
        exact hfi pfx ls0 _ d1 ls1a pm' dm' a' tvs hni hcs0
          ⟨rest, hes, List.IsPrefix.trans ⟨ls2, by rw [e]; simp⟩ hpre⟩ hira'
    rcases cyDRun ls1 _ d1 pm dm hir cpu0 (riscvStep tick') rs'' none ibNone st0 rfl hcy0 hm0 hP
        (fun _ _ _ _ => trivial) with
      ⟨la, lb, m1, rs1, fn1, ib1, dd, st1, hl, hira, hst, hm1⟩ |
      ⟨m1, rs1, fn1, ib1, st1, rfl, hc, hm1⟩
    · exact (hstop la m1 rs1 fn1 ib1 dd st1
        (cycInOfPrefix em pfx ls0 ls1 la ⟨rest, hes, hpre⟩ ⟨lb, hl.symm⟩) hira hst hm1).elim
    · exact ⟨m1, rs1, fn1, ib1, st1, rfl, hc, hm1⟩

/-! ## 3. The cycle obligations -/

/-- **NO REALIZED WALK-CYCLE STATE IS AT AN EXCEPTION'S CAUSE WRITE** (header): at every walk pc
(not only the load/store ones). -/
theorem noExcAt (p0 : Pexv6) (d0 : Efab) (em : Hemission) (pc : Int)
    (htext : textLo ≤ pc ∧ pc + 3 < textHi) (a : instruction) (hdec : PinWalkTab.decS pc = some a)
    (hfetch1 : fetchCyR1 pc) (hexec : execCyAt pc) (hnw : dfNwRole (krole pc)) (hft : kFetchText em)
    (hfeN : ∀ a tvs t, (LIFetch a tvs, t) ∈ em.emItems → t = none)
    (hfi : PinFetchPa.fetchOkRFi p0 d0 em pc)
    (g0 : GState) (hp0 : g0.pow = false) (hsafe : safeFrom g0) (hreal : cycReal g0 p0 d0 em pc) :
    ∀ (pfx : List Eitem) (ls0 : List Wlabel) (q : Pexv6) (d1 : Efab) (ls1 : List Wlabel)
      (pm : Pexv6) (dm : Efab),
      LInstr ∉ ls0 → cycStart p0 d0 em pfx pc ls0 q d1 → cycIn em pfx ls0 ls1 →
      irun ls1 q d1 pm dm → ¬ atCause false pm := by
  intro pfx ls0 q d1 ls1 pm dm hni hcs hcin hir hac
  obtain ⟨cpu0, hM⟩ := matchedAll p0 d0 em pc htext a hdec hfetch1 hexec hnw hft hfeN hfi g0 hp0
    hsafe hreal pfx ls0 q d1 hni hcs
  obtain ⟨m1, rs1, fn1, ib1, st1, hpm, hc, hm1⟩ := hM ls1 pm dm hcin hir
  rw [hpm] at hir
  obtain ⟨n, κ, t, g, gen, hmr, he, hl, hpr⟩ := hreal pfx ls0 q d1 ls1 _ _ _ _ _ dm hni hcs hcin hir
  obtain ⟨cpu, r, v, k, rs, fn, ib, hpe, hsr, hcb⟩ := hac
  rw [hpm] at hpe
  injection hpe with e1 e2 e3 e4 e5
  subst e2
  have hT : privS st1 r v := hc.1 hsr hcb
  have hS : g.m.regs cpu0 .cur_privilege = Privilege.Supervisor := by
    rw [hpr, hm1.1 .cur_privilege (by decide)]; exact hT
  have := causeIntrOf hp0 hsafe hmr he hl hS hsr
  rw [hcb] at this; cases this

/-- **`dataOkRF` FROM THE EXPORT** (header; replaces `PinDataOk.dataOkRFOf`'s `dataRealized`). -/
theorem dataOkRFOfReal (p0 : Pexv6) (d0 : Efab) (em : Hemission) (pc : Int)
    (htext : textLo ≤ pc ∧ pc + 3 < textHi) (a : instruction) (hdec : PinWalkTab.decS pc = some a)
    (hfetch1 : fetchCyR1 pc) (hexec : execCyAt pc) (hnw : dfNwRole (krole pc)) (hft : kFetchText em)
    (hfeN : ∀ a tvs t, (LIFetch a tvs, t) ∈ em.emItems → t = none)
    (hfi : PinFetchPa.fetchOkRFi p0 d0 em pc)
    (g0 : GState) (hp0 : g0.pow = false) (hsafe : safeFrom g0) (hreal : cycReal g0 p0 d0 em pc) :
    dataOkRF p0 d0 em pc :=
  fun _ => noExcAt p0 d0 em pc htext a hdec hfetch1 hexec hnw hft hfeN hfi g0 hp0 hsafe hreal

/-- **`fetchOkRF` (ii) FROM THE EXPORT** (header; replaces `PinDataOk.fetchOkRFiiOf`'s
`fetchOkRealized`): vacuously — no realized walk-cycle state is at an exception's cause write. -/
theorem fetchOkRFiiOfReal (p0 : Pexv6) (d0 : Efab) (em : Hemission) (pc : Int)
    (htext : textLo ≤ pc ∧ pc + 3 < textHi) (a : instruction) (hdec : PinWalkTab.decS pc = some a)
    (hfetch1 : fetchCyR1 pc) (hexec : execCyAt pc) (hnw : dfNwRole (krole pc)) (hft : kFetchText em)
    (hfeN : ∀ a tvs t, (LIFetch a tvs, t) ∈ em.emItems → t = none)
    (hfi : PinFetchPa.fetchOkRFi p0 d0 em pc)
    (g0 : GState) (hp0 : g0.pow = false) (hsafe : safeFrom g0) (hreal : cycReal g0 p0 d0 em pc) :
    fetchOkRFii p0 d0 em pc :=
  fun pfx ls0 q d1 ls1 pm dm hni hcs hcin hir hac =>
    absurd hac (noExcAt p0 d0 em pc htext a hdec hfetch1 hexec hnw hft hfeN hfi g0 hp0 hsafe hreal
      pfx ls0 q d1 ls1 pm dm hni hcs hcin hir)

/-- **`fetchOkRF ∧ dataOkRF` AT A REACHED NON-PIN WALK STATE** (header; `CapF2.cycFactsAt` with
`fetchOkRealized` and `dataRealized` replaced by the export + `cycReal`). -/
theorem cycFactsAtQ1 (pc : Int) (w : Pin) (own : Bool) (x : PState) (n : Nat) (l : List PState)
    (hm : (pc, w) ∈ pinsW9a) (hw : walkOwn w = some own) (hx : preach own (pinStart pc) x n)
    (hp : pstep own x = some l) (hne : l ≠ [])
    (p0 : Pexv6) (d0 : Efab) (em : Hemission) (hft : kFetchText em)
    (hfeN : ∀ a tvs t, (LIFetch a tvs, t) ∈ em.emItems → t = none)
    (hfr : PinFetchPa.fetchRealized p0 d0 em x.psPc)
    (g0 : GState) (hp0 : g0.pow = false) (hsafe : safeFrom g0)
    (hreal : cycReal g0 p0 d0 em x.psPc) :
    fetchOkRF p0 d0 em x.psPc ∧ dataOkRF p0 d0 em x.psPc := by
  have ht := walkText pc w own x n l hm hw hx hp hne
  obtain ⟨h0, hlt⟩ := CapF2.walkBounds pc w own x n l hm hw hx hp hne
  obtain ⟨a, hdec, -⟩ := walkDec pc w own x n l hm hw hx hp hne
  have hnw := walkNw pc w own x n l hm hw hx hp hne
  have hexec := execCyOfWalk pc w own x n l hm hw hx hp hne
  have hr1 := PinCycRunFetch.fetchCyR1Of x.psPc
  have hfi := PinFetchPa.fetchOkRFiOf p0 d0 em x.psPc h0 hlt hfr
  exact ⟨fetchOkRFOfParts p0 d0 em x.psPc hfi
      (fetchOkRFiiOfReal p0 d0 em x.psPc ht a hdec hr1 hexec hnw hft hfeN hfi g0 hp0 hsafe hreal),
    dataOkRFOfReal p0 d0 em x.psPc ht a hdec hr1 hexec hnw hft hfeN hfi g0 hp0 hsafe hreal⟩

/-- **`cycRun` FROM `hartConff`, THE DATA HALF FROM THE EXPORT** (header): `CapF5.cycRunOfHartConffR`
with `fetchOkRealized` and `dataRealized` gone — left: `fetchRealized` (Q1-c), `cycReal` (P-W6),
`excRetR`, `walkStartRealized` (6c). -/
theorem cycRunOfHartConffQ1 (G : Gexec) (i : Nat) (row : List Lbl) (p0 : Pexv6)
    (dvi dvo : Nat → Efab) (tq : Nat → Bool) (d0 : Efab)
    (em : Hemission) (pcL : Int) (w : Pin) (own : Bool)
    (hcf : hartConff i row p0 dvi dvo tq em) (hm : (pcL, w) ∈ pinsW9a) (hw : walkOwn w = some own)
    (hft : kFetchText em) (g0 : GState) (hp0 : g0.pow = false) (hsafe : safeFrom g0)
    (hreal : ∀ s n l, preach own (pinStart pcL) s n → pstep own s = some l → l ≠ [] →
      PinFetchPa.fetchRealized p0 d0 em s.psPc ∧ cycReal g0 p0 d0 em s.psPc)
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
    obtain ⟨h1, h2⟩ := hreal s n l hx hp hne
    exact cycFactsAtQ1 pcL w own s n l hm hw hx hp hne p0 d0 em hft hfeN h1 g0 hp0 hsafe h2
  exact CapF5.cycRunOfHartConff G i row p0 dvi dvo tq d0 em pcL w own hcf hm hw hft
    (fun s n l hs hp hne => cySailOfWalk pcL w own s n l hm hw hs hp hne
      (PinCycRunFetch.fetchCyR1Of _) (execCyOfWalk pcL w own s n l hm hw hs hp hne))
    (fun s n l hx hp hne => (hfacts s n l hx hp hne).1)
    (fun s n l hx hp hne => (hfacts s n l hx hp hne).2) hexc base rest hes
    (fun p d hr => by
      obtain ⟨cpu, rs, fn, ib, hp, hpc, hc⟩ := hstart p d hr
      exact ⟨cpu, rs, fn, ib, hp, PinCycRunFetch.kInvOfCfg _ rs hpc hc⟩)

end CapDataOk
end Weak
