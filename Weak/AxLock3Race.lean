/-
Weak: **`raceWpdUnprovable`: ownership is load-bearing for the NEW (tierA/`AxLock3`) lock
protocol**, the way `AxLockRace`/`AxLockRace3` made it load-bearing for the OLD (`AxProtLock`)
one (AxSL tier).

Rocq: `iris/AxLock3Race.v` @ xxvzwolszwmp.

## The Rocq header, in substance

A concrete, kernel-checked-`rvwmoCatConsistent` 3-hart race graph `race3`: hart A (0) runs the
lock3s WRITER row (`l3pWRow`, genesis acquire, writes `vA := b1` to `x`); hart B (1) runs the
lock3s READER row (`l3pRRow`, acquire SOURCED FROM A's release, but whose OWN load of `x` reads
from hart C's write instead of A's); hart C (2) runs a single, bare, protocol-EXTERNAL plain
store `x := vC := b2 ≠ vA`, placed gmo-coherence-AFTER A's write to `x`.

`raceWpdUnprovable`: hart C's own program (its bare store) CANNOT be verified at the SAME
concrete protocol instance (`axGA2` at `lock3ObStInterp0`) the real writer/reader capstones
(`wpdWriterHart`, `wpdReaderHartRel`) use — for EVERY choice of invariant/annotation instance
and protocol name `nm`.  Reductio: an assumed verification of C, combined with the two real
capstones into one 3-hart `Hwp`, feeds `tierAAdequacyAnn`; at hart B this derives
`PreaderPure L x race3 1 b2`, whose first conjunct at `j := 0` forces `b2 = b1` — refuted by
`WeakLitmus.b1NeB2`.

SANITY TWIN (`raceCWpdTrivial`, §4): the SAME program, graph, hart, stuckness and postcondition
DO verify at a TRIVIAL `axGA2` instance (`N := Unit`, `obSt0 := Unit`, `obStInterp0 := True`,
`init := emp`) — so the failure is due to the lock protocol's ownership, not to the WPd
framework or the graph.

**Fetches.** None: the three programs are hand-built monad terms with no fetch node.

## Deviations from Rocq

1. NAMES: camelCase (map below).  No name of this file is in the duplicated-name table.
   Lean-only helpers (file-qualified): `AxLock3Race.twpdc` (Rocq's local notation `TWPDc s`),
   `AxLock3Race.gconstPureC`/`AxLock3Race.localTrivC`/`AxLock3Race.obTrivC` (the trivial
   instance's graph pin is `⌜GD' = race3⌝`, its local and protocol interpretations `True`).  Rocq's hart-index NOTATIONS `A3`/`B3`/`C3`
   are the literals `0`/`1`/`2`.
2. O2 STAGE C: the fetch oracle `T` is gone everywhere (`AxOpsem.astepProg`, `tierAWpd`,
   `tierAAstep`, the capstones), so Rocq's `Tempty` and `HTx3 : ¬ Tempty x3r` are DROPPED (no
   statement can mention them; no downstream Rocq file imports AxLock3Race).
   `l3pCAstepWrite0` has no `T`/`img` arguments; `l3pCRun`'s unused `axirisG Σ` context is
   dropped.  The `WPd` step clause's image-pin premise is ignored.
3. `init_regstate` ↦ `zeroRegs` (ExecLib) in `l3pCP0`/`l3pCPfin`/`s03`/`sN3`; `dev0_state` ↦
   `OpaxWit.wtD0`; `z_pa` ↦ `BitVec.ofNat 64`; `CPU` literal `0%fin` ↦ `⟨0, _⟩`.
4. THE INSTANCES: Rocq's `Local Instance AxGA2_trivC` ↦ the named `@[reducible] def axGA2TrivC`;
   the policy (Rocq's global `lock_axpol`) ↦ the named `lockAxpol`, passed explicitly (also in
   the twin).  The twin's section `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc`
   (`raceCWpdTrivial` is stated hlc-generic, stronger); `raceWpdUnprovable` stays at
   `.hasNoLC` (the shape `tierAAdequacyAnn`'s `Hwp` quantifies).  Rocq's twin context
   `axannotG Σ` is the `AxannotGS` instance's own field.
5. STATEMENT SHAPES (as AxLock3Writer deviation 4): `Interface.Ret tt` ↦ `.pure ()`;
   `base.NoDup` ↦ `List.Nodup`; `∈` on lists ↦ `List.Mem`.
6. PROOF ROUTE (not statements): concrete graph facts by `decide +kernel` through the boolean
   specs (`grbBSpec`/`gwbBSpec`/`grfeBSpec`); `astepProgCWriteInv` is
   `AxLock3Writer`'s `astepProgPlainWriteInv` instantiated; `wpdcSkipStepOfLater` is proved
   directly (Rocq routes through `wp_skip_step_mono`).

**Rocq → Lean name map.**  `Lpa3` `Lpa3`, `xpa3` `xpa3`, `HLram3` `HLram3`, `Hxram3`
`Hxram3`, `cpu3` `cpu3`, `L3r` `L3r`, `x3r` `x3r`, `Hxy3` `Hxy3`, `l3p_c_m0` `l3pCM0`,
`l3p_c_p0` `l3pCP0`, `l3p_c_pfin` `l3pCPfin`, `l3p_c_row` `l3pCRow`, `l3p_c_astep_write0`
`l3pCAstepWrite0`, `l3p_c_run` `l3pCRun`, `acqA/w_xA/relA/acqB/r_xB/relB/w_xC`
`acqA/wXA/relA/acqB/rXB/relB/wXC`, `race3` `race3`, `race3_cat` `race3Cat`, `Hrow_A/B/C`
`HrowA/B/C`, `Himg3` `Himg3`, `Hrd0_A` `Hrd0A`, `Hwrel_wb0` `HwrelWb0`, `Hw_xA_b1` `HwXAB1`,
`Hread_acqB` `HreadAcqB`, `Hgwriteat4` `Hgwriteat4`, `Hgrfe_relAB` `HgrfeRelAB`,
`Hgob_relAB` `HgobRelAB`, `Hacq_wb1` `HacqWb1`, `Hrfe_relAB` `HrfeRelAB`, `harts3` `harts3`,
`s0_3` `s03`, `sN_3` `sN3`, `n_3` `n3`, `post3` `post3`, `Hnd3` `Hnd3`, `Hharts3` `Hharts3`,
`HA3in/HB3in/HC3in` `HA3in/HB3in/HC3in`, `Hk03` `Hk03`, `Hend3` `Hend3`, `Hrun3` `Hrun3`,
`race_wpd_unprovable` `raceWpdUnprovable`, `AxGA2_trivC` `axGA2TrivC`,
`wpdc_skip_step_of_later` `wpdcSkipStepOfLater`, `wpdc_row_end` `wpdcRowEnd`,
`astep_prog_c_write_inv` `astepProgCWriteInv`, `race3_gd_c` `race3GdC`, `wpdc_start`
`wpdcStart`, `race_c_wpd_trivial` `raceCWpdTrivial`.

**Dropped:** `Tempty`, `HTx3` (deviation 2).  Rocq 59 definitions/lemmas; Lean 57 + 4 Lean-only.  **Not ported:** the `Print Assumptions` lines (the
lint's axiom check covers them).
-/
import Weak.AxLock3Reader2
import Weak.AxGraphWit
import Weak.ExecLib

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! # 0. Three concrete RAM addresses/harts -/

def Lpa3 : PAddr := BitVec.ofNat 64 0x80001000
def xpa3 : PAddr := BitVec.ofNat 64 0x80002000

theorem HLram3 : devAddr Lpa3 = false := by decide +kernel
theorem Hxram3 : devAddr xpa3 = false := by decide +kernel

def cpu3 : CPU := ⟨0, by decide⟩

def L3r : Int := l3pLbase Lpa3
def x3r : Int := l3pXbase xpa3

theorem Hxy3 : x3r ≠ L3r := by decide +kernel

/-! # 1. Hart C's program: a single hand-built plain store `x := v` -/

def l3pCM0 (v : BitVec 8) : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP xpa3 v))) (fun _ => .pure ())
def l3pCP0 (v : BitVec 8) : Pexv6 := .PHart cpu3 (l3pCM0 v) zeroRegs none ibNone
def l3pCPfin : Pexv6 := .PHart cpu3 (.pure ()) zeroRegs none ibNone

def l3pCRow (v : BitVec 8) : List Lbl :=
  [.LStore false x3r [v] .WCplain]

theorem l3pCAstepWrite0 (row : List Lbl) (v : BitVec 8) :
    row[0]? = some (.LStore false x3r [v] .WCplain) →
    AxOpsem.astepProg row ⟨l3pCP0 v, 0⟩
      (LStore false x3r (WeakInterpProj.wbytes 1 v) [] [])
      ⟨l3pCPfin, 1⟩ := by
  intro hrow
  refine .AStepWrite _ 0 OpaxWit.wtD0 _ _ _ OpaxWit.wtD0 hrow rfl rfl ?_ ?_
  · simp only [wlWdata, lblData, l3pWbytes1]
  · exact l3pWritePlainStep cpu3 xpa3 Hxram3 v (fun _ => .pure ()) zeroRegs ibNone OpaxWit.wtD0

theorem l3pCRun (GD : Gdexec) (i : Agent) (v : BitVec 8)
    (Hrow : AxOpsem.grow GD i = l3pCRow v) :
    nsteps (astepAnyNfGv GD i) 1 ⟨l3pCP0 v, 0⟩ ⟨l3pCPfin, 1⟩ := by
  have hl0 : (AxOpsem.grow GD i)[0]? = some (.LStore false x3r [v] .WCplain) := by
    rw [Hrow]; rfl
  refine nsteps_l (astepAnyNfGv.ANFGVProg _ _
    ⟨_, l3pCAstepWrite0 _ v hl0, trivial⟩) ?_
  exact nsteps_O _

/-! # 2. The concrete 3-hart race graph

gmo = `[acqA; wXA; wXC; relA; acqB; rXB; relB]` — writes, in gmo order: acqA=1, wXA=2, wXC=3,
relA=4, acqB=5, relB=6.  `acqB`'s ts `4` names `relA`; `rXB`'s ts `3` names `wXC`. -/

def acqA : Geid := (0, 0)
def wXA : Geid := (0, 1)
def relA : Geid := (0, 3)
def acqB : Geid := (1, 0)
def rXB : Geid := (1, 1)
def relB : Geid := (1, 3)
def wXC : Geid := (2, 0)

def race3 : Gdexec :=
  AxGraphWit.mkgd
    [l3pWRow Lpa3 xpa3 0 b0 b1,
     l3pRRow Lpa3 xpa3 4 b0 3 b2,
     l3pCRow b2]
    [acqA, wXA, wXC, relA, acqB, rXB, relB]
    []

theorem race3Cat : rvwmoCatConsistent race3 := catConsistentBSound _ (by decide +kernel)

theorem HrowA : AxOpsem.grow race3 0 = l3pWRow Lpa3 xpa3 0 b0 b1 := rfl
theorem HrowB : AxOpsem.grow race3 1 = l3pRRow Lpa3 xpa3 4 b0 3 b2 := rfl
theorem HrowC : AxOpsem.grow race3 2 = l3pCRow b2 := rfl

theorem Himg3 : race3.gdG.gxImg L3r = some b0 := rfl

theorem Hrd0A : greadsByte race3.gdG acqA L3r 0 b0 :=
  (grbBSpec _ _ _ _ _).1 (by decide +kernel)

theorem HwrelWb0 : gwritesByte race3.gdG relA L3r b0 :=
  (gwbBSpec _ _ _ _).1 (by decide +kernel)

theorem HwXAB1 : gwritesByte race3.gdG wXA x3r b1 :=
  (gwbBSpec _ _ _ _).1 (by decide +kernel)

theorem HreadAcqB : greadsByte race3.gdG acqB L3r 4 b0 :=
  (grbBSpec _ _ _ _ _).1 (by decide +kernel)

theorem Hgwriteat4 : gwriteAt race3.gdG 4 = some relA := by decide +kernel

theorem HgrfeRelAB : grfe race3.gdG relA acqB :=
  (grfeBSpec _ _ _).1 (by decide +kernel)

theorem HgobRelAB : gobCat race3 relA acqB :=
  gobCatStep _ _ _ (.inr (.inr (.inl HgrfeRelAB)))

/-- `lockExtRmwReader`'s third conjunct is about the ACQUIRE `acqB` being write-shaped. -/
theorem HacqWb1 : gwritesByte race3.gdG acqB L3r b1 :=
  (gwbBSpec _ _ _ _).1 (by decide +kernel)

theorem HrfeRelAB : lockExtRmwReader L3r race3 relA acqB :=
  ⟨⟨4, b0, HreadAcqB, Hgwriteat4⟩, by decide, ⟨b1, HacqWb1⟩⟩

/-! # 3. The assembly: `raceWpdUnprovable`, at the same `axGA2`/`lock3ObStInterp0` instance the
real capstones use -/

section Assembly

variable {GF : BundledGFunctors.{0,0,0}} [AxlogG GF Hent] [AxLockG GF] [AxannotG GF]
  [InvGpreS GF]

def harts3 : List Agent := [0, 1, 2]

def s03 (i : Agent) : Athread :=
  match i with
  | 0 => ⟨l3pWP0 Lpa3 xpa3 cpu3 zeroRegs b1, 0⟩
  | 1 => ⟨l3pRP0 Lpa3 xpa3 cpu3 zeroRegs, 0⟩
  | _ => ⟨l3pCP0 b2, 0⟩

def sN3 (i : Agent) : Athread :=
  match i with
  | 0 => ⟨l3pWPfin cpu3 zeroRegs, 4⟩
  | 1 => ⟨l3pRPfin cpu3 zeroRegs (wordOfBytes 1 [b2]), 4⟩
  | _ => ⟨l3pCPfin, 1⟩

def n3 (i : Agent) : Nat :=
  match i with
  | 0 => 5
  | 1 => 6
  | _ => 1

def post3 (i : Agent) (_ : Athread) : Prop :=
  match i with
  | 1 => PreaderPure L3r x3r race3 1 b2
  | _ => True

theorem Hnd3 : harts3.Nodup := by decide

theorem Hharts3 : ∀ e, e ∈ race3.gdG.gxGmo → e.1 ∈ harts3 := by decide +kernel

theorem HA3in : (0 : Agent) ∈ harts3 := by decide
theorem HB3in : (1 : Agent) ∈ harts3 := by decide
theorem HC3in : (2 : Agent) ∈ harts3 := by decide

theorem Hk03 : ∀ i, i ∈ harts3 → (s03 i).atK = 0 := by
  intro i _
  unfold s03
  split <;> rfl

theorem Hend3 : ∀ i, i ∈ harts3 → (sN3 i).atK = (AxOpsem.grow race3 i).length := by
  intro i Hi
  simp only [harts3, List.mem_cons, List.not_mem_nil, or_false] at Hi
  rcases Hi with rfl | rfl | rfl <;> rfl

theorem Hrun3 : ∀ (_ : AxannotGS GF) (nm : lock3N) (i : Agent), i ∈ harts3 →
    nsteps (tierAAstep race3 nm i) (n3 i) (s03 i) (sN3 i) := by
  intro _ nm i Hi
  unfold tierAAstep
  simp only [harts3, List.mem_cons, List.not_mem_nil, or_false] at Hi
  rcases Hi with rfl | rfl | rfl
  · exact l3pWRun Lpa3 xpa3 cpu3 zeroRegs HLram3 Hxram3 race3 0 0 b0 b1 HrowA
  · exact l3pRRun Lpa3 xpa3 cpu3 zeroRegs HLram3 Hxram3 race3 1 4 b0 3 b2 HrowB
  · exact l3pCRun race3 2 b2 HrowC

/-- THE THEOREM. -/
theorem raceWpdUnprovable :
    ¬ (∀ [InvGS_gen .hasNoLC GF] [AxannotGS GF] (nm : lock3N),
        ⊢ lock3Init (GF := GF) nm 2 -∗
          @tierAWpd GF .hasNoLC _ _ lockAxpol race3 lock3N lock3ObSt0 (lock3ObStInterp0 L3r x3r)
            nm ⟨l3pCP0 b2, 0⟩ .MaybeStuck 2 (fun _ => iprop(True))) := by
  intro Hverif
  have Hinit0 : ∀ (nm : lock3N) (i : Agent), ⊢ (lock3Init (GF := GF) nm i) := by
    intro nm i
    unfold lock3Init
    iempintro
  have Hwp : ∀ [InvGS_gen .hasNoLC GF] [AxannotGS GF] (nm : lock3N),
      ⊢ ([∗list] i ∈ harts3, lock3Init (GF := GF) nm i) -∗
        [∗list] i ∈ harts3, @tierAWpd GF .hasNoLC _ _ lockAxpol race3 lock3N lock3ObSt0
          (lock3ObStInterp0 L3r x3r) nm (s03 i) .MaybeStuck i (fun s => iprop(⌜post3 i s⌝)) := by
    intro _ _ nm
    have HA0 := wpdWriterHart (GF := GF) (hlc := .hasNoLC) L3r x3r race3 nm Lpa3 xpa3 cpu3 0 0
      b0 b1 Hxy3 HLram3 Hxram3 rfl rfl HrowA race3Cat Himg3 Hrd0A zeroRegs
    have HA : ⊢ @tierAWpd GF .hasNoLC _ _ lockAxpol race3 lock3N lock3ObSt0
        (lock3ObStInterp0 L3r x3r) nm (s03 0) .MaybeStuck 0 (fun s => iprop(⌜post3 0 s⌝)) := by
      have h : ⊢ AxLock3Writer.twpd GF .hasNoLC L3r x3r race3 nm 0
          ⟨l3pWP0 Lpa3 xpa3 cpu3 zeroRegs b1, 0⟩ :=
        (Hinit0 nm 0).trans (wand_entails HA0)
      unfold AxLock3Writer.twpd tierAWpd at h
      unfold tierAWpd
      exact h.trans (@wpdMono .hasNoLC GF _
        (axGA2 race3 lock3N lock3ObSt0 (lock3ObStInterp0 L3r x3r) nm) lockAxpol _ _ _ _ _
        (fun _ => pure_intro trivial))
    have HB0 := wpdReaderHartRel (GF := GF) (hlc := .hasNoLC) L3r x3r race3 nm Lpa3 xpa3 cpu3 1 4
      b0 3 b2 Hxy3 HLram3 Hxram3 rfl rfl HrowB race3Cat relA HwrelWb0 HgobRelAB HrfeRelAB 0 0
      b0 b1 rfl HrowA zeroRegs
    have HB : ⊢ @tierAWpd GF .hasNoLC _ _ lockAxpol race3 lock3N lock3ObSt0
        (lock3ObStInterp0 L3r x3r) nm (s03 1) .MaybeStuck 1 (fun s => iprop(⌜post3 1 s⌝)) :=
      (Hinit0 nm 1).trans (wand_entails HB0)
    have HC : ⊢ @tierAWpd GF .hasNoLC _ _ lockAxpol race3 lock3N lock3ObSt0
        (lock3ObStInterp0 L3r x3r) nm (s03 2) .MaybeStuck 2 (fun s => iprop(⌜post3 2 s⌝)) := by
      have h := (Hinit0 nm 2).trans (wand_entails (Hverif nm))
      unfold tierAWpd at h
      unfold tierAWpd
      exact h.trans (@wpdMono .hasNoLC GF _
        (axGA2 race3 lock3N lock3ObSt0 (lock3ObStInterp0 L3r x3r) nm) lockAxpol _ _ _ _ _
        (fun _ => pure_intro trivial))
    unfold harts3
    iintro -
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iapply HA
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iapply HB
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iapply HC
    iapply BigSepL.bigSepL_nil.2
    iempintro
  have Hpost := @tierAAdequacyAnn GF _ _ lockAxpol race3 lock3N lock3ObSt0
    (lock3ObStInterp0 L3r x3r) (lock3Init (GF := GF)) lockAxpolWf race3Cat harts3 Hnd3 Hharts3
    s03 sN3 n3 Hrun3 Hk03 Hend3 post3 Hwp (lockHobAlloc L3r x3r Hxy3 race3 harts3)
    (lockAxpolHsPolSub race3) (lockAxpolHlobpSub race3) 1 HB3in
  have Hfst := Hpost.1 0 b1 HgrfeRelAB HwXAB1
  exact b1NeB2 Hfst.symm

end Assembly

/-! # 4. Sanity twin — `raceCWpdTrivial`: hart C's program verifies at a TRIVIAL instance -/

section TwinC

variable {GF : BundledGFunctors.{0,0,0}} {hlc : HasLC} [InvGS_gen hlc GF] [AxannotGS GF]
  (nm : Unit)

/-- Rocq `Local Instance AxGA2_trivC`: `axGA2` at `N := Unit`, `obSt0 := Unit`, `obStInterp0 :=
True` (deviation 4: a named reducible def). -/
@[reducible] def axGA2TrivC : AxirisG GF :=
  axGA2 race3 Unit Unit (fun _ _ _ _ => iprop(True)) nm

/-- Lean-only: Rocq's local notation `TWPDc s`. -/
def AxLock3Race.twpdc (GF : BundledGFunctors.{0,0,0}) (hlc : HasLC) [InvGS_gen hlc GF]
    [AxannotGS GF] (nm : Unit) (s : Athread) : IProp GF :=
  @tierAWpd GF hlc _ _ lockAxpol race3 Unit Unit (fun _ _ _ _ => iprop(True)) nm s .MaybeStuck 2
    (fun _ => iprop(True))

/-- Lean-only: the trivial instance's graph pin is the pure equation. -/
theorem AxLock3Race.gconstPureC (GD' : Gdexec) :
    AxirisG.gconstInterp (self := axGA2TrivC (GF := GF) nm) GD' ⊢ iprop(⌜GD' = race3⌝) :=
  .rfl

/-- Lean-only: the trivial instance's local interpretation is `True`. -/
theorem AxLock3Race.localTrivC (GD' : Gdexec) (j : Agent) (k : Nat) :
    ⊢ AxirisG.localInterp (self := axGA2TrivC (GF := GF) nm) GD' j k () :=
  true_intro

/-- Lean-only: the trivial instance's protocol interpretation is `True`. -/
theorem AxLock3Race.obTrivC (GD' : Gdexec) (σ : Unit) (s : GSet Geid) :
    ⊢ AxirisG.obStInterp (self := axGA2TrivC (GF := GF) nm) GD' σ s :=
  true_intro

theorem wpdcSkipStepOfLater (k' : Nat) (Ψ : IProp GF) :
    ⊢ ▷ Ψ -∗ @wpSkipStep GF (axGA2TrivC nm) race3 2 k' Ψ := by
  unfold wpSkipStep
  iintro HΨ %na Hna
  imodintro
  inext
  imodintro
  iexists ()
  isplitl [Hna]
  · iexact Hna
  isplitr
  · iapply AxLock3Race.localTrivC
  · iexact HΨ

theorem wpdcRowEnd (k0 : Nat) (Hend : (AxOpsem.grow race3 2).length ≤ k0) (p : Pexv6) :
    ⊢ AxLock3Race.twpdc GF hlc nm ⟨p, k0⟩ := by
  have Hnone : (AxOpsem.grow race3 2)[k0]? = none := List.getElem?_eq_none Hend
  have H : ⊢ ∀ p : Pexv6, AxLock3Race.twpdc GF hlc nm ⟨p, k0⟩ := by
    iloeb as IH
    iintro %p
    unfold AxLock3Race.twpdc tierAWpd
    iapply (@AxWpD.wpdMUnfoldStep hlc GF _ (axGA2TrivC nm) lockAxpol rvwmoCatConsistent
      .MaybeStuck 2 _ _).2
    isplit
    · iapply (@progressOblMaybestuck GF (axGA2TrivC nm) lockAxpol 2 _).2
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, -⟩
    ihave %Hg := AxLock3Race.gconstPureC nm GD' $$ Hg
    subst GD'
    isplit
    · iintro %id %K %Hst
      obtain ⟨lb, Hlb, -⟩ := Hst
      simp only at Hlb
      rw [Hnone] at Hlb
      cases Hlb
    isplit
    · iintro %l %s' %Hst %-
      obtain ⟨Hadm, Hk', -⟩ := astepProgRowEndShape _ _ l s' Hnone Hst
      rw [lbAdminWlWdataNone l Hadm]
      obtain ⟨p', k1⟩ := s'
      simp only at Hk'
      subst Hk'
      iapply wpdcSkipStepOfLater (GF := GF) nm
      inext
      iapply IH $$ %p'
    isplit
    · iintro %s' %Hw
      obtain ⟨p', k1⟩ := s'
      obtain ⟨Hk, -⟩ := Hw
      simp only at Hk
      subst Hk
      iapply wpdcSkipStepOfLater (GF := GF) nm
      inext
      iapply IH $$ %p'
    · iintro %-
      iapply (@postLiftingTrue GF (axGA2TrivC nm) lockAxpol _ 2 _ true_intro)
  iapply H $$ %p

theorem astepProgCWriteInv (rs : RegFile) (s : Athread)
    (Heqp : s.atP = .PHart cpu3 (l3pCM0 b2) rs none ibNone) (Heqk : s.atK = 0) (l : Wlabel)
    (s' : Athread) :
    AxOpsem.astepProg (AxOpsem.grow race3 2) s l s' →
    l = LStore false (paZ xpa3) (WeakInterpProj.wbytes 1 b2)
          (depsAsrc (depsOfIb ibNone.ibBits)) (depsVsrc (depsOfIb ibNone.ibBits)) ∧
    s' = ⟨.PHart cpu3 (.pure ()) rs none ibNone, 1⟩ :=
  astepProgPlainWriteInv race3 cpu3 2 xpa3 Hxram3 b2 (fun _ => .pure ()) rs 0 s Heqp Heqk l s'

theorem race3GdC : graphData race3 (2, 0) = some (WeakInterpProj.wbytes 1 b2) := by
  decide +kernel

theorem wpdcStart :
    ⊢ ∀ rs : RegFile, AxLock3Race.twpdc GF hlc nm ⟨.PHart cpu3 (l3pCM0 b2) rs none ibNone, 0⟩ := by
  iloeb as IH
  iintro %rs
  unfold AxLock3Race.twpdc tierAWpd
  iapply (@AxWpD.wpdMUnfoldStep hlc GF _ (axGA2TrivC nm) lockAxpol rvwmoCatConsistent
    .MaybeStuck 2 _ _).2
  isplit
  · iapply (@progressOblMaybestuck GF (axGA2TrivC nm) lockAxpol 2 _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD' %ls ⟨%Hc, #Hg, -⟩
  ihave %Hg := AxLock3Race.gconstPureC nm GD' $$ Hg
  subst GD'
  isplit
  · iintro %id %K %Hst
    have hfalse : False := by
      obtain ⟨lb, Hlb, Hid, Hsome, -⟩ := Hst
      simp only at Hlb
      rw [HrowC] at Hlb
      simp only [l3pCRow, List.getElem?_cons_zero, Option.some.injEq] at Hlb
      subst Hlb Hid
      simp [aident, aidentRd] at Hsome
    exact hfalse.elim
  isplit
  · iintro %l %s' %Hst %-
    obtain ⟨rfl, rfl⟩ := astepProgCWriteInv rs _ rfl rfl l s' Hst
    simp only [wlWdata]
    unfold wpEvStep naAtProgress
    iintro %na ⟨%Hprog, Hannot⟩
    have Hnin : ((2 : Agent), 0) ∉ (FiniteMap.dom_set na : GSet Geid) := by
      intro Hin
      have Hf : ((2 : Agent), 0) ∈ FiniteSet.filter (fun e : Geid => decide (e.1 = 2))
          (FiniteMap.dom_set na : GSet Geid) := elemOfFilter.2 ⟨by simp, Hin⟩
      rw [Hprog, elemOfEidsBefore] at Hf
      exact Nat.not_lt_zero _ Hf.2.1
    imod (annotAlloc na (2, 0) iprop(True) Hnin) $$ Hannot with ⟨Hannot', -⟩
    imodintro
    inext
    imodintro
    iexists (), iprop(True), (∅ : Mea GF), (∅ : Mea GF), ()
    isplitr
    · ipureintro
      trivial
    isplitr
    · unfold naSplittingWf
      isplitr
      · ipureintro
        rw [domEmpty]
        exact LawfulSet.empty_subset
      · iapply (BigSepM2.bigSepM2_empty _).2
        itrivial
    isplitr
    · unfold flowEqDyn
      iintro %σ %sOb %Hsub %Hnin' - -
      iapply fupd_mask_intro LawfulSet.empty_subset
      iintro Hclose
      inext
      imod Hclose
      imodintro
      iexists σ
      isplitr
      · iapply AxLock3Race.obTrivC
      isplitr
      · itrivial
      · ipureintro
        exact race3GdC
    isplitl [Hannot']
    · rw [AxLockWp.annotInsertEq]
      iexact Hannot'
    isplitr
    · iapply AxLock3Race.localTrivC
    · have Hend := wpdcRowEnd (GF := GF) (hlc := hlc) nm (0 + 1) (by rw [HrowC]; simp [l3pCRow])
        (.PHart cpu3 (.pure ()) rs none ibNone)
      unfold AxLock3Race.twpdc tierAWpd at Hend
      dsimp only
      iapply Hend
  isplit
  · iintro %s' %Hw
    obtain ⟨rs', rfl⟩ := l3pAwireRsOnly cpu3 (l3pCM0 b2) rs none ibNone 0 s' Hw
    iapply wpdcSkipStepOfLater (GF := GF) nm
    inext
    iapply IH $$ %rs'
  · iintro %-
    iapply (@postLiftingTrue GF (axGA2TrivC nm) lockAxpol _ 2 _ true_intro)

end TwinC

/-- THE TWIN THEOREM. -/
theorem raceCWpdTrivial {GF : BundledGFunctors.{0,0,0}} {hlc : HasLC} :
    ∀ [InvGS_gen hlc GF] [AxannotGS GF] (nm : Unit),
      ⊢ (iprop(emp) : IProp GF) -∗
        @tierAWpd GF hlc _ _ lockAxpol race3 Unit Unit (fun _ _ _ _ => iprop(True)) nm
          ⟨l3pCP0 b2, 0⟩ .MaybeStuck 2 (fun _ => iprop(True)) := by
  intro _ _ nm
  iintro -
  have h := wpdcStart (GF := GF) (hlc := hlc) nm
  unfold AxLock3Race.twpdc at h
  unfold l3pCP0
  iapply h $$ %zeroRegs

end Weak
