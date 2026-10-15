/-
Weak: **W11-C2′ (a3) relArmed — THE ASSEMBLY** (`PROGRESS-relArmed.md`).  Lean-only.

`relArmedOf`: on W4's record, `WbPrimed.relArmed` holds given the run interface
`relRunRealized` (W11-F's obligation, of `syncRealized`'s kind). That interface says: before every
recorded release store, the hart's own last two instruction cycles are
* the arming fence's cycle at `pc − 4`, then the store's cycle at `pc`;
* each fetching the kernel text at its pc (r1/r2: bytes `kA`, addresses `kAa`);
* with no trap in either (interrupts masked, no fault);
* started from a boundary in the kernel configuration;
* the store writing 4 bytes (the lock word / `started` is aligned).

Everything else is proved:
* the fence arms (`fenceCycle`);
* nothing between the barrier and the store consumes the flag (`amB`'s run soundness `amRun`;
  `swCycle`: the prelude, fetch and translation write only exclusive A/D updates; a 4-byte piece
  only unsplit);
* the boundary steps keep it (`bdSegArm`);
* the record's fold is the hart-local fold (`armFoldEq`, `htrPrefix`).

Every helper is `Weak.PinRelArm.*`.
-/
import Weak.PinRelArmRec

namespace Weak
open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open Wlabel KernelPinsDef MachOfPf RelSiteProvPc

namespace PinRelArm
open SailCycleOrderK PinCycRun PinRelArmFp PinDataflow

/-- The release sites: (arming fence, release store). -/
def relPairs : List (Int × Int) :=
  [((KernelSyms.«release» : Int) + 0x16, (KernelSyms.«release» : Int) + 0x1a),
   ((KernelSyms.«main» : Int) + 0xac, (KernelSyms.«main» : Int) + 0xb0)]

theorem relPairsMem (fpc pc : Int) (h : (fpc, pc) ∈ relPairs) :
    fpc ∈ relFencePcs ∧ pc ∈ releasePcs := by
  simp only [relPairs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨by simp [relFencePcs], by simp [releasePcs]⟩
  · exact ⟨by simp [relFencePcs], by simp [releasePcs]⟩

/-- Every fetch label of a cycle segment is admitted at `pc` as its cycle's `k`-th fetch read
(r1's text bytes `kA`, r2's addresses `kAa pc`). -/
def feAdmSeg (pc : Int) (t : List (Pexv6 × Wlabel)) : Prop :=
  ∀ t1 pm l t2, t = t1 ++ (pm, l) :: t2 → feAdm kA (kAa pc) (feLabs (t1.map Prod.snd)).length l

/-- **THE RELEASE STRETCH, REALIZED (INTERFACE, header; W11-F's obligation)**: before every
recorded plain store at a release pc, the agent's own trace ends with a boundary segment `b1`
(from a boundary in the kernel configuration), the arming fence's cycle `c1` (fetching at
`fpc = pc − 4`), a boundary segment `b2`, and the store's cycle `c2` up to the store (fetching at
`pc`); no trap in either cycle; the store writes 4 bytes. -/
def relRunRealized (r : List PfRec) : Prop :=
  ∀ (n : Nat) (x : PfRec) (ag : Wpagent Pexv6), r[n]? = some x → lbStore x.lb = true →
    x.pre.pcAgs[x.ag]? = some ag → pcOfSt ag.paSt ∈ releasePcs →
    ∃ (t0 b1 c1 b2 c2 : List (Pexv6 × Wlabel)) (fpc : Int),
      jtrace x.ag (r.take n) = t0 ++ (b1 ++ (c1 ++ (b2 ++ c2))) ∧
      (fpc, pcOfSt ag.paSt) ∈ relPairs ∧
      (∃ (q : Pexv6) (cpu : CPU) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch)
          (l : Wlabel) (b1' : List (Pexv6 × Wlabel)),
        b1 = (q, l) :: b1' ∧ q = .PHart cpu (.pure ()) rs fn ib ∧ RbootAll rs ∧ cfgAg rs) ∧
      bdSeg b1 ∧ b2 ≠ [] ∧ bdSeg b2 ∧ c1 ≠ [] ∧ inCyc c1 ∧ inCyc c2 ∧ ¬ atStopC ag.paSt ∧
      feAdmSeg fpc c1 ∧ feAdmSeg (pcOfSt ag.paSt) c2 ∧ lbSt4 x.lb

section asm
variable {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
  {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}

/-- An agent of an entry's pre-configuration is an agent of the record's start. -/
theorem contRLookup {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {r : List PfRec}
    {cN : Wpcfg Pexv6 Efab} (h : contRC fok fcutT c st r cN) :
    ∀ (n : Nat) (x : PfRec) (j : Nat) (ag : Wpagent Pexv6), r[n]? = some x →
      x.pre.pcAgs[j]? = some ag → ∃ ag0, c.pcAgs[j]? = some ag0 := by
  induction h with
  | nil => intro n x _ _ hx; simp at hx
  | cons c c' st i l k r cN hs _ _ _ _ _ ih =>
    intro n x j ag hx hag
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx; exact ⟨ag, hag⟩
    | succ n =>
      simp only [List.getElem?_cons_succ] at hx
      obtain ⟨ag1, h1⟩ := ih n x j ag hx hag
      have hlen := wpPfStepAgsLen pstepEv pclsEv i l c c' hs
      have hlt : j < c'.pcAgs.length := (List.getElem?_eq_some_iff.1 h1).1
      rw [hlen] at hlt
      exact ⟨_, List.getElem?_eq_getElem hlt⟩


theorem htrJoin : ∀ (p : Pexv6) (t1 : List (Pexv6 × Wlabel)) (q : Pexv6), htr p t1 q →
    ∀ (t2 : List (Pexv6 × Wlabel)) (r : Pexv6), htr q t2 r → htr p (t1 ++ t2) r := by
  intro p t1 q h
  induction h with
  | nil p => intro t2 r h2; exact h2
  | cons hs hr ih => intro t2 r h2; exact .cons hs (ih t2 r h2)

/-- The fetch admission along a cycle segment followed by a non-fetch step (and, if more follows,
a boundary state, which `inCyc` excludes). -/
theorem admPair (pc : Int) (c : List (Pexv6 × Wlabel)) (pm : Pexv6) (l2 : Wlabel)
    (b' : List (Pexv6 × Wlabel)) (hfa : feAdmSeg pc c) (hl2 : isFeLab l2 = false)
    (hpm : b' = [] ∨ atPureS pm) :
    ∀ t1 pm' l t2, c ++ (pm, l2) :: b' = t1 ++ (pm', l) :: t2 → inCyc t1 →
      feAdm kA (kAa pc) (([] : List FeEnt).length + (feLabs (t1.map Prod.snd)).length) l := by
  intro t1 pm' l t2 e hin
  rw [List.length_nil, Nat.zero_add]
  rcases List.append_eq_append_iff.1 e with ⟨a', rfl, he⟩ | ⟨c', rfl, he⟩
  · cases a' with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at he
      obtain ⟨⟨-, rfl⟩, -⟩ := he
      intro a tvs hl; subst hl; simp [isFeLab] at hl2
    | cons y a'' =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      rcases hpm with rfl | hp
      · simp at he
      · exact absurd hp (hin pm (by simp)).1
  · cases c' with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at he
      obtain ⟨⟨-, rfl⟩, -⟩ := he
      intro a tvs hl; subst hl; simp [isFeLab] at hl2
    | cons y c'' =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      exact hfa t1 pm' l c'' rfl

theorem inCycSnoc (t : List (Pexv6 × Wlabel)) (q : Pexv6) (l : Wlabel) (h : inCyc t)
    (h1 : ¬ atPureS q) (h2 : ¬ atStopC q) : inCyc (t ++ [(q, l)]) := by
  intro x hx
  simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact h x hx
  · exact ⟨h1, h2⟩

set_option maxHeartbeats 4000000 in
/-- **(a3) DISCHARGED** (header): on W4's record, `WbPrimed.relArmed` from the run interface
`relRunRealized`. -/
theorem relArmedOf {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {r : List PfRec}
    {cN : Wpcfg Pexv6 Efab} (h : contRC fok fcutT c st r cN) (hreal : relRunRealized r) :
    WbPrimed.relArmed r := by
  intro n x hx hst ag hag hpc
  obtain ⟨t0, b1, c1, b2, c2, fpc, hdec, hpair, ⟨q, cpu, rs, fn, ib, l1, b1', hb1e, hq, hrb, hcfg⟩,
    hb1, hb2ne, hb2, hc1ne, hc1, hc2, hns, hfa1, hfa2, h4⟩ := hreal n x ag hx hst hag hpc
  obtain ⟨hfpc, hpc'⟩ := relPairsMem fpc _ hpair
  obtain ⟨ag0, h0⟩ := contRLookup h n x x.ag ag hx hag
  have htr0 := htrPrefix x.ag h n x ag0 ag hx h0 hag
  rw [hdec] at htr0
  obtain ⟨q0, -, htr1⟩ := htrApp t0 _ _ _ htr0
  obtain ⟨q1, hb1t, htr2⟩ := htrApp b1 _ _ _ htr1
  obtain ⟨q2, hc1t, htr3⟩ := htrApp c1 _ _ _ htr2
  obtain ⟨q3, hb2t, hc2t⟩ := htrApp b2 _ _ _ htr3
  -- the start of `b1` is the boundary `q`
  have hq0 : q0 = q := by
    rw [hb1e] at hb1t; cases hb1t; rfl
  subst hq0
  subst hq
  -- `b1` ends with the boundary step into the fence cycle
  have hc1s : ¬ atPureS q1 := by
    obtain ⟨⟨p, l⟩, c1', rfl⟩ := List.exists_cons_of_ne_nil hc1ne
    cases hc1t
    exact (hc1 _ List.mem_cons_self).1
  obtain ⟨tick1, rs1, rfl, hrb1, hcfg1⟩ : ∃ tick rs', q1 = .PHart cpu (riscvStep tick) rs' none ibNone ∧
      RbootAll rs' ∧ cfgAg rs' := by
    rcases bdSegArm _ _ _ hb1t hb1 cpu rs fn ib false rfl hrb hcfg with
      ⟨rs', fn', ib', rfl, -⟩ | ⟨tick, rs', e, h1, h2, -⟩
    · exact absurd ⟨cpu, rs', fn', ib', rfl⟩ hc1s
    · exact ⟨tick, rs', e, h1, h2⟩
  -- the fence cycle, up to the boundary that starts `b2`
  obtain ⟨⟨pm, l2⟩, b2', rfl⟩ := List.exists_cons_of_ne_nil hb2ne
  have hq2 : q2 = pm := by cases hb2t; rfl
  subst hq2
  have hpm : atPureS q2 := hb2 q2 List.mem_cons_self
  have hl2 : isFeLab l2 = false := by
    cases hb2t with
    | cons hs _ =>
      obtain ⟨d, d', hst⟩ := hs
      obtain ⟨c0, r0, f0, i0, rfl⟩ := hpm
      exact (pureStepLab _ _ _ _ _ _ _ _ hst).1
  obtain ⟨-, hii1⟩ := amRun kA (kAa fpc) (fun _ st' => true = true → st'.armed = true) _ _ _
    (htrJoin _ _ _ hc1t _ _ hb2t) cpu (riscvStep tick1) rs1 none ibNone ⟨[], false, false⟩
    (afold b1 (afold t0 false)) rfl
    (fenceCycle fpc hfpc tick1 _ rfl rfl) rfl hrb1 hcfg1 (fun h => by cases h)
    (admPair fpc c1 q2 l2 b2' hfa1 hl2 (Or.inr hpm))
  obtain ⟨st1, fn1, hP1, harm1, cpu2, rs2, ib2, e2, hrb2, hcfg2⟩ :=
    hii1 c1 q2 l2 b2' rfl hc1 hpm
  have hfold1 : afold c1 (afold b1 (afold t0 false)) = true ∨ parkArms fn1 := by
    rcases harm1 (hP1 rfl) with h | h
    · exact Or.inl h
    · exact Or.inr h
  -- the store's own step
  obtain ⟨c', hstep⟩ := contRStepAt h n x hx
  obtain ⟨ag', p', d', ws', hl', hps, -⟩ := wpPfStepInv pstepEv pclsEv _ _ _ _ hstep
  rw [hag] at hl'
  cases hl'
  have hnp : ¬ atPureS ag.paSt := by
    rintro ⟨cc, rr, ff, ii, e⟩
    rw [e] at hps
    have := (pureStepLab _ _ _ _ _ _ _ _ hps).2
    rw [this] at hst; cases hst
  -- `b2` ends with the boundary step into the store's cycle
  have hq3np : ¬ atPureS q3 := by
    cases c2 with
    | cons y c2' =>
      obtain ⟨p, l⟩ := y
      cases hc2t
      exact (hc2 _ List.mem_cons_self).1
    | nil => cases hc2t; exact hnp
  obtain ⟨tick3, rs3, rfl, hrb3, hcfg3, hfold2⟩ : ∃ tick rs', q3 = .PHart cpu2 (riscvStep tick) rs' none ibNone ∧
      RbootAll rs' ∧ cfgAg rs' ∧ afold ((q2, l2) :: b2') (afold c1 (afold b1 (afold t0 false))) = true := by
    rcases bdSegArm _ _ _ hb2t hb2 cpu2 rs2 fn1 ib2 (afold c1 (afold b1 (afold t0 false))) e2 hrb2 hcfg2 with
      ⟨rs', fn', ib', rfl, -⟩ | ⟨tick, rs', e, h1, h2, h3⟩
    · exact absurd ⟨cpu2, rs', fn', ib', rfl⟩ hq3np
    · exact ⟨tick, rs', e, h1, h2, h3 hfold1⟩
  have hfe : isFeLab x.lb = false := by
    obtain ⟨rl, a, data, asrc, vsrc, e, -⟩ := h4
    rw [e]; rfl
  obtain ⟨hi2, -⟩ := amRun kA (kAa (pcOfSt ag.paSt)) (fun _ st' => false = true → st'.armed = true)
    _ _ _ (htrSnoc _ _ _ hc2t x.lb p' x.pre.pcDev d' hps) cpu2 (riscvStep tick3) rs3 none ibNone
    ⟨[], true, false⟩ _ rfl (swCycle _ hpc' tick3 _ rfl rfl rfl) rfl hrb3 hcfg3
    (fun _ => Or.inl hfold2) (admPair _ c2 ag.paSt x.lb [] hfa2 hfe (Or.inl rfl))
  have hfin := hi2 c2 ag.paSt x.lb [] rfl (inCycSnoc c2 _ _ hc2 hnp hns) h4
  rw [armFoldEq, hdec]
  simp only [afoldApp]
  exact hfin

end asm

end PinRelArm
end Weak
