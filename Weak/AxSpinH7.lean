/-
Weak: **Phase 2b, part 4 of the spinlock plan -- CERTIFICATE 2: the critical section NEVER TOUCHES
the protected 4-byte word, so its handle is still AT THE CLAIM when the lock is released** (the
`AxSpinH2` `ex ≠ c` gap).
  B: acquire; lw lk (the holder's `holding` read); fence rw,w; sw lk ← 0
  A: acquire; fence rw,w; sw lk ← 0
both at `spinOb6 ya (clRange xa 4) [ca] cv5` (`AxSpinH6`'s instance).  B's WPd `wpdB7` uses only
the handle surface: `wpdAcquireH6`; `wpdAnnotEntail`/`wpdAnnotSplit` (the claim fragment
`locked ∗ lk->cpu` split, OUTSIDE any step, into `locked` and `lk->cpu`); `wpdLkreadHeld6` (the
`lw lk` draws `locked` -- ppo rule 5 -- and deposits `v ≠ 0`); `wpdAnnotMerge` (lk->cpu and the
UNTOUCHED word handle, two fragments at the claim, merged into one anchor); `wpdReleaseGen6`
(anchors {the read, the claim}).  A's WPd `wpdA7` is `wpdAcquireH6` + `wpdReleaseH6Same` (the
canonical contract for a CS that never touches the word).  The post `⌜vl ≠ 0⌝` is READ BACK at
the row end from the `lw`'s annotation.

Rocq: `iris/AxSpinH7.v` @ xxvzwolszwmp.

## The Rocq header, in substance

PROVED
  `csUntouched`: for ANY hart A with a WPd at `spinOb6 …` from `spinInit6` and any run, on every
    tagged-consistent ctrl-closed 2-hart graph where B's row is `b7Row t1 tl vl`: `vl ≠ 0`.
  (a) `gs7Premises` / `gs7Shape` / `gs7Sound`: every premise on the concrete `gs7` (A = `a7`,
    PROVED at the real protocol with `wpdReleaseH6Same`); B claims A's release and its `lw lk`
    reads its own claim's 1.
  No race twin for this one (task scope).  NOTE the conclusion is about the LOCK word, whose
  holder-read fact comes from the lock protocol (HELD_NZ), not from the word handle -- this
  certificate exercises the release-side plumbing (handle at the claim, split/merge outside a
  step), not word ownership (certificate 1, `AxSpinH6`, does that, with its race twin).
  MILESTONE aspects: hand rows, one-byte lock, deps are graph data.

## Deviations from Rocq

1. O2 STAGE C (as `AxSpinH6` deviation 1): no text oracle -- Rocq's `Tf` arguments of
   `tierA_astep`/`tierA_wpd`/`AxGA2` are gone.
2. CONTEXTS (as `AxSpinH6` deviation 2): Rocq section variables are explicit leading arguments
   in Rocq's order (`wpdA7`: `GT nm cpu Hcons tA Hrow`; `wpdB7`: `GT nm cpu Hcons t1 tl vl
   Hrow`); `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc`.  The local instance `g7_G`
   and the policy `l6_pol` ↦ `splPol GT` passed explicitly; the Rocq notations `XS6`/`OB6`/`R6`/
   `TW6`/`LK`/`ΦB`/`TWB` are unfolded (`TWA`/`TWB` file-local notations).  Section `runs7`'s
   unused `axirisG Σ` is dropped.  The proof-local `set m` of `wpdB7` is the Lean-only def
   `AxSpinH7.relMap`; the capstone's `set` locals are the Lean-only defs
   `AxSpinH7.cS0`/`cSN`/`cN`/`cPost`; `HwpA` and the certificate statements take
   `[InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF]` instance binders; `spinΣ` ↦ `spinGF`.
3. lean-sail shapes (as `AxSpinH6` deviation 3): `ld_m` ↦ `AxSpinProt7.ldM`; `B0/B1` ↦
   `b0/b1`; `init_regstate` ↦ `zeroRegs`; `gt_g GT` ↦ `GT.gtG`; `vm_compute`/`vmr` ↦
   `decide +kernel`.
4. `harts6_tac` (Rocq Ltac of `AxSpinH6`): `gs7Harts` is one kernel-decided `List.all` check.

**Rocq → Lean name map.**  `b7_cs` `b7Cs`, `b7_m0` `b7M0`, `b7_row` `b7Row`, `a7_cs` `a7Cs`,
`a7_m0` `a7M0`, `a7_row` `a7Row`, `b7_run` `b7Run`, `a7_run` `a7Run`, `wpdA7` `wpdA7`, `wpdB7`
`wpdB7`, `cs_untouched` `csUntouched`, `b7_deps` `b7Deps`, `gs7` `gs7`, `gs7_cat_t` `gs7CatT`,
`gs7_ctrl_closed` `gs7CtrlClosed`, `gs7_harts` `gs7Harts`, `gs7_shape` `gs7Shape`, `a7_wpd_at`
`a7WpdAt`, `a7_run_at` `a7RunAt`, `gs7_premises` `gs7Premises`, `gs7_sound` `gs7Sound`.
Lean-only (file-qualified): `AxSpinH7.relMap`, `AxSpinH7.cS0`/`cSN`/`cN`/`cPost`.

**Dropped:** the local instance `g7_G` (inlined), the §5 `Check`/`Print Assumptions` lines (the
lint's axiom check covers them).  (22 Rocq items = 21 decls + 1 instance; 26 Lean = 21 + 5
Lean-only.)
-/
import Weak.AxSpinH6

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Dtag

/-! # 1. Programs, rows, runs -/

abbrev b7Cs : SailM Unit := AxSpinProt7.ldM ypaM (fenceM (relM hlt))
abbrev b7M0 : SailM Unit := acqRmw b7Cs hlt
def b7Row (t1 tl : Nat) (vl : BitVec 8) : List Lbl :=
  [.LRmw true false ya [t1] [b0] [b1] .WCplain,
   .LLoad false ya [tl] [vl],
   .LFence true true false true,
   .LStore false ya [b0] .WCrel]

abbrev a7Cs : SailM Unit := fenceM (relM hlt)
abbrev a7M0 : SailM Unit := acqRmw a7Cs hlt
def a7Row (tA : Nat) : List Lbl :=
  [.LRmw true false ya [tA] [b0] [b1] .WCplain,
   .LFence true true false true,
   .LStore false ya [b0] .WCrel]

section runs7
variable (cpu : CPU)

theorem b7Run (GD : Gdexec) (t1 tl : Nat) (vl : BitVec 8)
    (Hrow : AxOpsem.grow GD hB = b7Row t1 tl vl) :
    nsteps (astepAnyNfGv GD hB) 5 ⟨hp cpu b7M0 zeroRegs, 0⟩ ⟨hp cpu hlt zeroRegs, 4⟩ := by
  refine nsteps_l (runRmwRead cpu GD hB 0 ypaM ypaMRam t1 b0 .WCplain (acqK b7Cs hlt) zeroRegs
    (by rw [Hrow]; rfl)) ?_
  have Hw := runRmwWrite cpu GD hB 0 ypaM ypaMRam t1 b0 .WCplain
    (if b0 = b0 then b7Cs else hlt) zeroRegs (by rw [Hrow]; rfl)
  rw [if_pos rfl] at Hw
  refine nsteps_l Hw ?_
  refine nsteps_l (spRunRead cpu GD hB ypaM ypaMRam [tl] vl (fun _ => fenceM (relM hlt))
    zeroRegs 1 (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (runFence cpu GD hB 2 (relM hlt) zeroRegs (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (spRunWrite cpu GD hB ypaM ypaMRam b0 hlt zeroRegs 3 .WCrel
    (by rw [Hrow]; rfl)) ?_
  exact nsteps_O _

theorem a7Run (GD : Gdexec) (tA : Nat) (Hrow : AxOpsem.grow GD hA = a7Row tA) :
    nsteps (astepAnyNfGv GD hA) 4 ⟨hp cpu a7M0 zeroRegs, 0⟩ ⟨hp cpu hlt zeroRegs, 3⟩ := by
  refine nsteps_l (runRmwRead cpu GD hA 0 ypaM ypaMRam tA b0 .WCplain (acqK a7Cs hlt) zeroRegs
    (by rw [Hrow]; rfl)) ?_
  have Hw := runRmwWrite cpu GD hA 0 ypaM ypaMRam tA b0 .WCplain
    (if b0 = b0 then a7Cs else hlt) zeroRegs (by rw [Hrow]; rfl)
  rw [if_pos rfl] at Hw
  refine nsteps_l Hw ?_
  refine nsteps_l (runFence cpu GD hA 1 (relM hlt) zeroRegs (by rw [Hrow]; rfl)) ?_
  refine nsteps_l (spRunWrite cpu GD hA ypaM ypaMRam b0 hlt zeroRegs 2 .WCrel
    (by rw [Hrow]; rfl)) ?_
  exact nsteps_O _

end runs7

/-! # 2. The WPds -/

section wpds7
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxlogG GF Hent] [SpinlockG GF]

set_option hygiene false in
local notation:max "TWA " s:max => @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
  (spinOb6 ya (clRange xa 4) [ca] cv5) nm s .MaybeStuck hA (fun _ => iprop(True))

/-- HART A: the CS is empty -- the word handle never leaves the claim; released by the
SAME-ANCHOR contract. -/
theorem wpdA7 (GT : GdexecT) (nm : spinN) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (tA : Nat) (Hrow : AxOpsem.grow (gtAdGd GT) hA = a7Row tA) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR6 (clRange xa 4) [ca] nm (gtAdGd GT)) -∗
      notheld nm.2 ya hA -∗ TWA ⟨hp cpu a7M0 zeroRegs, 0⟩ := by
  have Hlen : (AxOpsem.grow (gtAdGd GT) hA).length = 3 := by rw [Hrow]; rfl
  have H0 : ⊢ isLock (GF := GF) nm.2 ya (spinR6 (clRange xa 4) [ca] nm (gtAdGd GT)) -∗
      notheld nm.2 ya hA -∗
      (⌜lkClaim ya (gtAdGd GT).gdG (hA, 0) (gwriteAt (gtAdGd GT).gdG tA)⌝ -∗
        AxAnnot.annotOwn (hA, 0)
          iprop(locked nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [ca] (hA, 0)) -∗
        hdlw GT nm 1 xa 4 (hA, 0) [] -∗
        ∀ rs : RegFile, TWA ⟨hp cpu a7Cs rs, 1⟩) -∗
      ∀ rs : RegFile, TWA ⟨hp cpu a7M0 rs, 0⟩ :=
    wpdAcquireH6 (hlc := hlc) xa 4 [ca] cv5 GT nm cpu Hcons yaNX6 hA 0 tA a7Cs hlt _
      (by rw [Hlen]; decide) (by rw [Hrow]; rfl)
  have H1 : ⊢ isLock (GF := GF) nm.2 ya (spinR6 (clRange xa 4) [ca] nm (gtAdGd GT)) -∗
      AxAnnot.annotOwn (hA, 0)
        iprop(locked nm.2 ya hA (hA, 0) ∗ RL nm.1 (gtAdGd GT) [ca] (hA, 0)) -∗
      hdlw GT nm 1 xa 4 (hA, 0) [] -∗
      (AxAnnot.annotOwn (hA, 2) (notheld nm.2 ya hA) -∗
        ∀ rs : RegFile, TWA ⟨hp cpu hlt rs, 3⟩) -∗
      ∀ rs : RegFile, TWA ⟨hp cpu a7Cs rs, 1⟩ :=
    wpdReleaseH6Same (hlc := hlc) xa 4 [ca] cv5 GT nm cpu Hcons yaNX6 hA 1 hlt (hA, 0) [] _
      (by rw [Hlen]; decide) (by rw [Hlen]; decide) (by rw [Hrow]; rfl) (by rw [Hrow]; rfl)
      ⟨rfl, by decide, _, by rw [Hrow]; rfl, rfl⟩
  have H2 : ⊢ ∀ rs : RegFile, TWA ⟨hp cpu hlt rs, 3⟩ :=
    shHltTrue (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
      (spinOb6 ya (clRange xa 4) [ca] cv5) nm cpu hA 3
  iintro #Hil Hnh
  iapply H0 $$ Hil Hnh [] %zeroRegs
  iintro %_ Hc Hx %rs
  iapply H1 $$ Hil Hc Hx [] %rs
  iintro _ %rs
  iapply H2 $$ %rs

/-- Lean-only (Rocq's proof-local `set m` of `wpdB7`): the release anchors -- `locked` (with a
`True` frame) at the read, `lk->cpu ∗` the untouched word at the claim. -/
abbrev AxSpinH7.relMap (GT : GdexecT) (nm : spinN) : Mea GF :=
  insert ({[((hB, 0) : Geid) := iprop(RL (GF := GF) nm.1 (gtAdGd GT) [ca] (hB, 0) ∗
      RbN nm.1 (gtAdGd GT) 1 (clRange xa 4) (hB, 0) [])]} : Mea GF) ((hB, 1) : Geid)
    iprop(locked nm.2 ya hB (hB, 0) ∗ True)

set_option hygiene false in
local notation:max "TWB " s:max => @tierAWpd GF hlc _ _ (splPol GT) (gtAdGd GT) spinN Unit
  (spinOb6 ya (clRange xa 4) [ca] cv5) nm s .MaybeStuck hB (fun _ => iprop(⌜vl ≠ b0⌝))

theorem wpdB7 (GT : GdexecT) (nm : spinN) (cpu : CPU) (Hcons : rvwmoCatConsistent (gtAdGd GT))
    (t1 tl : Nat) (vl : BitVec 8) (Hrow : AxOpsem.grow (gtAdGd GT) hB = b7Row t1 tl vl) :
    ⊢ isLock (GF := GF) nm.2 ya (spinR6 (clRange xa 4) [ca] nm (gtAdGd GT)) -∗
      notheld nm.2 ya hB -∗ TWB ⟨hp cpu b7M0 zeroRegs, 0⟩ := by
  have Hlen : (AxOpsem.grow (gtAdGd GT) hB).length = 4 := by rw [Hrow]; rfl
  -- acquire, handle form
  have H0 : ⊢ isLock (GF := GF) nm.2 ya (spinR6 (clRange xa 4) [ca] nm (gtAdGd GT)) -∗
      notheld nm.2 ya hB -∗
      (⌜lkClaim ya (gtAdGd GT).gdG (hB, 0) (gwriteAt (gtAdGd GT).gdG t1)⌝ -∗
        AxAnnot.annotOwn (hB, 0)
          iprop(locked nm.2 ya hB (hB, 0) ∗ RL nm.1 (gtAdGd GT) [ca] (hB, 0)) -∗
        hdlw GT nm 1 xa 4 (hB, 0) [] -∗
        ∀ rs : RegFile, TWB ⟨hp cpu b7Cs rs, 1⟩) -∗
      ∀ rs : RegFile, TWB ⟨hp cpu b7M0 rs, 0⟩ :=
    wpdAcquireH6 (hlc := hlc) xa 4 [ca] cv5 GT nm cpu Hcons yaNX6 hB 0 t1 b7Cs hlt _
      (by rw [Hlen]; decide) (by rw [Hrow]; rfl)
  -- split `locked` off the claim's `locked ∗ lk->cpu` fragment -- outside any step
  have HPQ : (iprop(locked (GF := GF) nm.2 ya hB (hB, 0) ∗ RL nm.1 (gtAdGd GT) [ca] (hB, 0))) ⊢
      iprop((locked nm.2 ya hB (hB, 0) ∗ True) ∗ RL nm.1 (gtAdGd GT) [ca] (hB, 0)) := by
    iintro ⟨Hl, Hr⟩
    isplitl [Hl]
    · isplitl [Hl]
      · iexact Hl
      · itrivial
    · iexact Hr
  have Hen : ∀ rs : RegFile, ⊢ AxAnnot.annotOwn (GF := GF) (hB, 0)
      iprop(locked nm.2 ya hB (hB, 0) ∗ RL nm.1 (gtAdGd GT) [ca] (hB, 0)) -∗
      (AxAnnot.annotOwn (hB, 0)
        iprop((locked nm.2 ya hB (hB, 0) ∗ True) ∗ RL nm.1 (gtAdGd GT) [ca] (hB, 0)) -∗
        TWB ⟨hp cpu b7Cs rs, 1⟩) -∗
      TWB ⟨hp cpu b7Cs rs, 1⟩ := fun rs =>
    wpdAnnotEntail (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
      (spinOb6 ya (clRange xa 4) [ca] cv5) nm hB _ ⟨hp cpu b7Cs rs, 1⟩ (hB, 0) _ _ HPQ
  have Hsp : ∀ rs : RegFile, ⊢ AxAnnot.annotOwn (GF := GF) (hB, 0)
      iprop((locked nm.2 ya hB (hB, 0) ∗ True) ∗ RL nm.1 (gtAdGd GT) [ca] (hB, 0)) -∗
      (AxAnnot.annotOwn (hB, 0) iprop(locked nm.2 ya hB (hB, 0) ∗ True) -∗
        AxAnnot.annotOwn (hB, 0) (RL nm.1 (gtAdGd GT) [ca] (hB, 0)) -∗
        TWB ⟨hp cpu b7Cs rs, 1⟩) -∗
      TWB ⟨hp cpu b7Cs rs, 1⟩ := fun rs =>
    wpdAnnotSplit (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
      (spinOb6 ya (clRange xa 4) [ca] cv5) nm hB _ ⟨hp cpu b7Cs rs, 1⟩ (hB, 0) _ _
  -- merge lk->cpu with the UNTOUCHED word handle: two fragments at the claim
  have Hmg : ∀ rs : RegFile, ⊢ AxAnnot.annotOwn (GF := GF) (hB, 0)
      (RL nm.1 (gtAdGd GT) [ca] (hB, 0)) -∗
      hdlw GT nm 1 xa 4 (hB, 0) [] -∗
      (AxAnnot.annotOwn (hB, 0) iprop(RL nm.1 (gtAdGd GT) [ca] (hB, 0) ∗
          RbN nm.1 (gtAdGd GT) 1 (clRange xa 4) (hB, 0) []) -∗
        TWB ⟨hp cpu b7Cs rs, 1⟩) -∗
      TWB ⟨hp cpu b7Cs rs, 1⟩ := fun rs =>
    wpdAnnotMerge (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
      (spinOb6 ya (clRange xa 4) [ca] cv5) nm hB _ ⟨hp cpu b7Cs rs, 1⟩ (hB, 0) _ _
  -- lw lk: the holder's read draws `locked` (ppo rule 5), deposits `v ≠ 0`
  have Hnl : nolk ya (gtAdGd GT).gdG (hB, 0) (hB, 1) := by
    rintro w v - ⟨-, H1, -⟩ ⟨-, H2, -⟩
    dsimp only at H1 H2
    omega
  have H1 : ⊢ AxAnnot.annotOwn (GF := GF) (hB, 0) iprop(locked nm.2 ya hB (hB, 0) ∗ True) -∗
      (AxAnnot.annotOwn (hB, 1) iprop(locked nm.2 ya hB (hB, 0) ∗ True) -∗
        AxAnnot.annotOwn (hB, 1) iprop(⌜vl ≠ b0⌝) -∗
        ∀ rs : RegFile, TWB ⟨hp cpu (fenceM (relM hlt)) rs, 2⟩) -∗
      ∀ rs : RegFile, TWB ⟨hp cpu b7Cs rs, 1⟩ :=
    wpdLkreadHeld6 (hlc := hlc) xa 4 [ca] cv5 GT nm cpu Hcons yaNX6 hB 0 1
      (fun _ => fenceM (relM hlt)) t1 tl vl iprop(True) _ (by rw [Hlen]; decide)
      (by rw [Hrow]; rfl) (by decide) (by rw [Hrow]; rfl) Hnl
  -- release: anchors {the read (locked), the claim (lk->cpu ∗ the word)}
  have hnone : get? ({[((hB, 0) : Geid) := iprop(RL (GF := GF) nm.1 (gtAdGd GT) [ca] (hB, 0) ∗
      RbN nm.1 (gtAdGd GT) 1 (clRange xa 4) (hB, 0) [])]} : Mea GF) ((hB, 1) : Geid) = none :=
    lookupSingletonNe (by decide)
  have Hdom : ∀ e, e ∈ (FiniteMap.dom_set (AxSpinH7.relMap (GF := GF) GT nm) : GSet Geid) →
      e.1 = hB ∧ e.2 < 2 ∧
        ∃ l, (AxOpsem.grow (gtAdGd GT) hB)[e.2]? = some l ∧ lbIsMem l = true := by
    intro e He
    rw [domInsert, domSingleton] at He
    rcases elemOfUnion.1 He with h | h
    · rw [elemOfSingleton.1 h]
      exact ⟨rfl, by decide, _, by rw [Hrow]; rfl, rfl⟩
    · rw [elemOfSingleton.1 h]
      exact ⟨rfl, by decide, _, by rw [Hrow]; rfl, rfl⟩
  have H0In : ((hB, 0) : Geid) ∈
      (FiniteMap.dom_set (AxSpinH7.relMap (GF := GF) GT nm) : GSet Geid) := by
    rw [domInsert, domSingleton]
    exact elemOfUnionR (elemOfSingleton.2 rfl)
  have Hmk : ⊢ AxAnnot.annotOwn (GF := GF) (hB, 1) iprop(locked nm.2 ya hB (hB, 0) ∗ True) -∗
      AxAnnot.annotOwn (hB, 0) iprop(RL nm.1 (gtAdGd GT) [ca] (hB, 0) ∗
        RbN nm.1 (gtAdGd GT) 1 (clRange xa 4) (hB, 0) []) -∗
      [∗map] e ↦ P ∈ AxSpinH7.relMap (GF := GF) GT nm, AxAnnot.annotOwn e P := by
    iintro Ha Hb
    iapply (BigSepM.bigSepM_insert hnone).2
    isplitl [Ha]
    · iexact Ha
    · iapply BigSepM.bigSepM_singleton.2
      iexact Hb
  have Hsplit : ⊢ ([∗map] Rin ∈ AxSpinH7.relMap (GF := GF) GT nm, Rin) -∗
      iprop(locked nm.2 ya hB (hB, 0) ∗
        (∃ (a : Geid), ⌜a ∈ (FiniteMap.dom_set (AxSpinH7.relMap (GF := GF) GT nm) : GSet Geid)⌝ ∗
          RL nm.1 (gtAdGd GT) (clRange xa 4) a) ∗
        (∃ (a : Geid), ⌜a ∈ (FiniteMap.dom_set (AxSpinH7.relMap (GF := GF) GT nm) : GSet Geid)⌝ ∗
          RL nm.1 (gtAdGd GT) [ca] a)) := by
    iintro H
    icases (BigSepM.bigSepM_insert hnone).1 $$ H with ⟨⟨Hlk, -⟩, HX⟩
    ihave HX := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ HX
    icases HX with ⟨HC, HX⟩
    isplitl [Hlk]
    · iexact Hlk
    isplitl [HX]
    · iexists (hB, 0)
      isplitr
      · ipureintro
        exact H0In
      · iapply (RbNRL nm.1 (gtAdGd GT) (clRange xa 4) (hB, 0) []) $$ HX
    · iexists (hB, 0)
      isplitr
      · ipureintro
        exact H0In
      · iexact HC
  have H2 : ⊢ isLock (GF := GF) nm.2 ya (spinR6 (clRange xa 4) [ca] nm (gtAdGd GT)) -∗
      ([∗map] e ↦ P ∈ AxSpinH7.relMap (GF := GF) GT nm, AxAnnot.annotOwn e P) -∗
      (([∗map] P ∈ AxSpinH7.relMap (GF := GF) GT nm, P) -∗
        locked nm.2 ya hB (hB, 0) ∗
        (∃ (a : Geid), ⌜a ∈ (FiniteMap.dom_set (AxSpinH7.relMap (GF := GF) GT nm) : GSet Geid)⌝ ∗
          RL nm.1 (gtAdGd GT) (clRange xa 4) a) ∗
        (∃ (a : Geid), ⌜a ∈ (FiniteMap.dom_set (AxSpinH7.relMap (GF := GF) GT nm) : GSet Geid)⌝ ∗
          RL nm.1 (gtAdGd GT) [ca] a)) -∗
      (AxAnnot.annotOwn (hB, 3) (notheld nm.2 ya hB) -∗
        ∀ rs : RegFile, TWB ⟨hp cpu hlt rs, 4⟩) -∗
      ∀ rs : RegFile, TWB ⟨hp cpu (fenceM (relM hlt)) rs, 2⟩ :=
    wpdReleaseGen6 (hlc := hlc) (GF := GF) xa 4 [ca] cv5 GT nm cpu Hcons yaNX6 hB 2 hlt (hB, 0)
      (AxSpinH7.relMap GT nm) _ (by rw [Hlen]; decide) (by rw [Hlen]; decide)
      (by rw [Hrow]; rfl) (by rw [Hrow]; rfl) Hdom
  -- row end: `vl ≠ 0` READ BACK from the `lw`'s annotation
  have H3 : ⊢ AxAnnot.annotOwn (GF := GF) (hB, 1) iprop(⌜vl ≠ b0⌝) -∗
      ∀ rs : RegFile, TWB ⟨hp cpu hlt rs, 4⟩ :=
    shHltReadback (hlc := hlc) (pol := splPol GT) (gtAdGd GT) spinN Unit
      (spinOb6 ya (clRange xa 4) [ca] cv5) nm cpu hB 4 (hB, 1) rfl _ (vl ≠ b0) .rfl
  iintro #Hil Hnh
  iapply H0 $$ Hil Hnh [] %zeroRegs
  iintro %_ Hc Hx %rs
  iapply (Hen rs) $$ Hc
  iintro Hc
  iapply (Hsp rs) $$ Hc
  iintro Hlk Hcpu
  iapply (Hmg rs) $$ Hcpu Hx
  iintro Hcx
  iapply H1 $$ Hlk [Hcx] %rs
  iintro Hr Hv %rs
  ihave Hm := Hmk $$ Hr Hcx
  ihave Hw := Hsplit
  iapply H2 $$ Hil Hm Hw [Hv] %rs
  iintro _ %rs
  iapply H3 $$ Hv %rs

end wpds7

/-! # 3. THE CAPSTONE -/

/-- Lean-only (Rocq `set s0`). -/
def AxSpinH7.cS0 (sA0 : Athread) (i : Agent) : Athread :=
  if i = hA then sA0 else ⟨hp cpu0 b7M0 zeroRegs, 0⟩
/-- Lean-only (Rocq `set sN`). -/
def AxSpinH7.cSN (sAN : Athread) (i : Agent) : Athread :=
  if i = hA then sAN else ⟨hp cpu0 hlt zeroRegs, 4⟩
/-- Lean-only (Rocq `set nf`). -/
def AxSpinH7.cN (nA : Nat) (i : Agent) : Nat := if i = hA then nA else 5
/-- Lean-only (Rocq `set post`). -/
def AxSpinH7.cPost (vl : BitVec 8) (i : Agent) (_ : Athread) : Prop :=
  if i = hB then vl ≠ b0 else True

theorem csUntouched (GT : GdexecT)
    (HconsT : rvwmoCatConsistentT GT) (Hcl : ctrlClosed GT)
    (Hharts : ∀ e, e ∈ GT.gtG.gxGmo → e.1 = hA ∨ e.1 = hB)
    (t1 tl : Nat) (vl : BitVec 8)
    (HrowB : AxOpsem.grow (gtAdGd GT) hB = b7Row t1 tl vl)
    (sA0 sAN : Athread) (nA : Nat)
    (HrunA : ∀ (_ : AxannotGS spinGF) (nm : spinN),
      nsteps (tierAAstep (gtAdGd GT) nm hA) nA sA0 sAN)
    (HkA : sA0.atK = 0) (HendA : sAN.atK = (AxOpsem.grow (gtAdGd GT) hA).length)
    (HwpA : ∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : spinN),
      ⊢ spinInit6 ya (clRange xa 4) [ca] (gtAdGd GT) nm hA -∗
        @tierAWpd spinGF .hasNoLC _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xa 4) [ca] cv5) nm sA0 .MaybeStuck hA (fun _ => iprop(True))) :
    vl ≠ b0 := by
  have Hin01 : ∀ i : Agent, i ∈ [hA, hB] → i = hA ∨ i = hB := by
    intro i Hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hi
    exact Hi
  have Hnd : [hA, hB].Nodup := by decide
  have Hharts' : ∀ e, e ∈ GT.gtG.gxGmo → e.1 ∈ [hA, hB] := by
    intro e He
    rcases Hharts e He with H | H <;> rw [H] <;> simp
  have Hcons := catTAd GT HconsT
  have Hrun : ∀ (_ : AxannotGS spinGF) (nm : spinN) i, i ∈ [hA, hB] →
      nsteps (tierAAstep (gtAdGd GT) nm i) (AxSpinH7.cN nA i) (AxSpinH7.cS0 sA0 i)
        (AxSpinH7.cSN sAN i) := by
    intro Hann nm i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact HrunA Hann nm
    · exact b7Run cpu0 (gtAdGd GT) t1 tl vl HrowB
  have Hk0 : ∀ i, i ∈ [hA, hB] → (AxSpinH7.cS0 sA0 i).atK = 0 := by
    intro i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact HkA
    · rfl
  have Hend : ∀ i, i ∈ [hA, hB] →
      (AxSpinH7.cSN sAN i).atK = (AxOpsem.grow (gtAdGd GT) i).length := by
    intro i Hi
    rcases Hin01 i Hi with rfl | rfl
    · exact HendA
    · show 4 = (AxOpsem.grow (gtAdGd GT) hB).length
      rw [HrowB]
      rfl
  have Hwp : ∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : spinN),
      ⊢ ([∗list] i ∈ [hA, hB], spinInit6 ya (clRange xa 4) [ca] (gtAdGd GT) nm i) -∗
        [∗list] i ∈ [hA, hB],
          @tierAWpd spinGF .hasNoLC _ _ (splPol GT) (gtAdGd GT) spinN Unit
            (spinOb6 ya (clRange xa 4) [ca] cv5) nm (AxSpinH7.cS0 sA0 i) .MaybeStuck i
            (fun s => iprop(⌜AxSpinH7.cPost vl i s⌝)) := by
    intro Hinv Hann nm
    iintro HI
    icases (AxTokLedgerMp.bigSepLPair hA hB
      (fun i => spinInit6 (GF := spinGF) ya (clRange xa 4) [ca] (gtAdGd GT) nm i)).1 $$ HI
      with ⟨HA, HB⟩
    iapply (AxTokLedgerMp.bigSepLPair hA hB _).2
    rw [show AxSpinH7.cS0 sA0 hA = sA0 from if_pos rfl,
      show AxSpinH7.cS0 sA0 hB = ⟨hp cpu0 b7M0 zeroRegs, 0⟩ from if_neg (by decide)]
    isplitl [HA]
    · iapply (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb6 ya (clRange xa 4) [ca] cv5) nm sA0 .MaybeStuck hA (fun _ => iprop(True))
        (fun s => iprop(⌜AxSpinH7.cPost vl hA s⌝))
        (fun _ => pure_mono (fun _ => by
          unfold AxSpinH7.cPost; rw [if_neg (by decide)]; trivial)))
      iapply HwpA nm $$ HA
    · iapply (AxSpinWit.tierAWpdMono (hlc := .hasNoLC) (pol := splPol GT) (gtAdGd GT) spinN Unit
        (spinOb6 ya (clRange xa 4) [ca] cv5) nm ⟨hp cpu0 b7M0 zeroRegs, 0⟩ .MaybeStuck hB
        (fun _ => iprop(⌜vl ≠ b0⌝))
        (fun s => iprop(⌜AxSpinH7.cPost vl hB s⌝))
        (fun _ => pure_mono (fun Hv => by
          unfold AxSpinH7.cPost; rw [if_pos rfl]; exact Hv)))
      unfold spinInit6
      icases HB with ⟨Hil, Hnh⟩
      iapply (wpdB7 (hlc := .hasNoLC) (GF := spinGF) GT nm cpu0 Hcons t1 tl vl HrowB) $$ Hil Hnh
  have HndC : [ca].Nodup := by simp
  have Hfin := @tierAAdequacyAnnGateT spinGF _ _ (splPol GT) GT spinN Unit
    (spinOb6 ya (clRange xa 4) [ca] cv5) (spinInit6 ya (clRange xa 4) [ca] (gtAdGd GT))
    (splAxpolWf GT) HconsT [hA, hB] Hnd Hharts' (AxSpinH7.cS0 sA0) (AxSpinH7.cSN sAN)
    (AxSpinH7.cN nA) Hrun Hk0 Hend (AxSpinH7.cPost vl) Hwp
    (spinHobAlloc6 (GF := spinGF) ya (clRange xa 4) [ca] cv5 (gtAdGd GT) [hA, hB] Hnd XS6Nodup
      HndC XS6Disj)
    (splHok GT HconsT Hcl) hB (by simp)
  exact (if_pos rfl : AxSpinH7.cPost vl hB _ = (vl ≠ b0)) ▸ Hfin

/-! # 4. SATISFIABILITY -/

def b7Deps : List Tdep := [(((hB, 0), (hB, 3)), DTctrl)]

/-- A claims (image) and releases; B claims A's release, its `lw lk` reads its own claim's 1,
B releases. -/
def gs7 : GdexecT :=
  mkgt [a7Row 0, b7Row 2 3 b1] [(hA, 0), (hA, 2), (hB, 0), (hB, 1), (hB, 3)] b7Deps

theorem gs7CatT : rvwmoCatConsistentT gs7 := catTConsistentBSound _ (by decide +kernel)
theorem gs7CtrlClosed : ctrlClosed gs7 := ctrlClosedBSound _ gs7CatT.1 (by decide +kernel)

theorem gs7Harts : ∀ e, e ∈ gs7.gtG.gxGmo → e.1 = hA ∨ e.1 = hB := by
  intro e He
  have h : gs7.gtG.gxGmo.all (fun e : Geid => decide (e.1 = hA ∨ e.1 = hB)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.1 h e He)

theorem gs7Shape :
    grfAt gs7.gtG ya (hA, 2) (hB, 0) ∧ grfAt gs7.gtG ya (hB, 0) (hB, 1) :=
  ⟨(grfAtBSpec _ _ _ _).1 (by decide +kernel), (grfAtBSpec _ _ _ _).1 (by decide +kernel)⟩

theorem a7WpdAt (GT : GdexecT) (Hc : rvwmoCatConsistentT GT)
    (Hr : AxOpsem.grow (gtAdGd GT) hA = a7Row 0) :
    ∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : spinN),
      ⊢ spinInit6 ya (clRange xa 4) [ca] (gtAdGd GT) nm hA -∗
        @tierAWpd spinGF .hasNoLC _ _ (splPol GT) (gtAdGd GT) spinN Unit
          (spinOb6 ya (clRange xa 4) [ca] cv5) nm ⟨hp cpu0 a7M0 zeroRegs, 0⟩ .MaybeStuck hA
          (fun _ => iprop(True)) := by
  intro _ _ nm
  unfold spinInit6
  iintro ⟨Hil, Hnh⟩
  iapply (wpdA7 (hlc := .hasNoLC) (GF := spinGF) GT nm cpu0 (catTAd GT Hc) 0 Hr) $$ Hil Hnh

theorem a7RunAt (GT : GdexecT) (Hr : AxOpsem.grow (gtAdGd GT) hA = a7Row 0) :
    ∀ (_ : AxannotGS spinGF) (nm : spinN),
      nsteps (tierAAstep (gtAdGd GT) nm hA) 4
        ⟨hp cpu0 a7M0 zeroRegs, 0⟩ ⟨hp cpu0 hlt zeroRegs, 3⟩ :=
  fun _ _ => a7Run cpu0 (gtAdGd GT) 0 Hr

theorem gs7Premises :
    rvwmoCatConsistentT gs7 ∧ ctrlClosed gs7 ∧
    (∀ e, e ∈ gs7.gtG.gxGmo → e.1 = hA ∨ e.1 = hB) ∧
    AxOpsem.grow (gtAdGd gs7) hB = b7Row 2 3 b1 ∧
    (∀ (_ : AxannotGS spinGF) (nm : spinN),
      nsteps (tierAAstep (gtAdGd gs7) nm hA) 4
        ⟨hp cpu0 a7M0 zeroRegs, 0⟩ ⟨hp cpu0 hlt zeroRegs, 3⟩) ∧
    (⟨hp cpu0 a7M0 zeroRegs, 0⟩ : Athread).atK = 0 ∧
    (⟨hp cpu0 hlt zeroRegs, 3⟩ : Athread).atK = (AxOpsem.grow (gtAdGd gs7) hA).length ∧
    (∀ [InvGS_gen .hasNoLC spinGF] [AxannotGS spinGF] (nm : spinN),
      ⊢ spinInit6 ya (clRange xa 4) [ca] (gtAdGd gs7) nm hA -∗
        @tierAWpd spinGF .hasNoLC _ _ (splPol gs7) (gtAdGd gs7) spinN Unit
          (spinOb6 ya (clRange xa 4) [ca] cv5) nm ⟨hp cpu0 a7M0 zeroRegs, 0⟩ .MaybeStuck hA
          (fun _ => iprop(True))) :=
  ⟨gs7CatT, gs7CtrlClosed, gs7Harts, rfl, a7RunAt gs7 rfl, rfl, rfl, a7WpdAt gs7 gs7CatT rfl⟩

/-- The capstone fires on `gs7`; the conclusion (`1 ≠ 0`) is TRUE there. -/
theorem gs7Sound : b1 ≠ b0 :=
  csUntouched gs7 gs7CatT gs7CtrlClosed gs7Harts 2 3 b1 rfl _ _ 4 (a7RunAt gs7 rfl) rfl rfl
    (a7WpdAt gs7 gs7CatT rfl)

end Weak
