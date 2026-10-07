/-
Weak: **Phase 1b, part 2 of the spinlock plan -- the 1b INSTANCE `spinOb5` and its RULES.**
(Files: `AxSpinProt5` the rule ingredients and the lk->cpu pure layer; this one; `AxSpinProt7`
hand programs/runs/WPds; `AxSpinProt8` the capstone.)

Rocq: `iris/AxSpinProt6.v` @ xxvzwolszwmp.

## The Rocq header, in substance

INSTANCE `spinOb5 lk x Cl cv` = `⌜WC ∧ CPUOK⌝ ∗ ownInv X5` (owned bytes `X5 = {x} ∪ Cl`, one
history ghost) `∗ lkInv` (the Phase-1a lock component, unchanged).  The lock's `R` = `spinR5`
= `RL [x] ∗ RL Cl`: TWO components, lk->cpu's history auths travelling inside `R` with the lock
(D2).  `spinHobAlloc5`: genesis, all histories `[]`, `R` parked in σ0's genesis box (F4), every
hart `notheld`.

RULES (each a `flowEqDyn` ∀σ ∀ processed set; nothing about σ assumed beyond its own conjuncts;
`fe5Build` re-establishes `WC` and `CPUOK` and DEMANDS Φ_cpu (`cpuOk e`) of every event):
  `fe5Neutral`      acquire-fail RMW;
  `fe5Claim`        acquire-success, `notheld` in hand;
  `fe5Claim'`       REQUIRED (2): `notheld` drawn through `flowIn` (the previous release's
                    annotation);
  `fe5Release'`     REQUIRED (1): each component from `flowIn` at its own anchor; deposits
                    `notheld` (REQUIRED (2)'s source).  No read-fact conjunct;
  `fe5LkreadHeld`   REQUIRED (3): `locked i c` through `flowIn` (rule 5), deposits `locked ∗ Q`
                    and `⌜v ≠ b0⌝` AT THE READ;
  `fe5Lkread`       anyone's plain lock-word read (frame);
  `fe5RLwrite`      the OWNED write of a component (`[x]` or lk->cpu, full width) WITH Φ_cpu as
                    side condition;
  `fe5Rbread`       the owned PLACEMENT read of a component byte;
  `fe5Cpuread`      the RACY lk->cpu read (holder or not): deposits `rdFact` AT THE READ.
Policy: `AxSpinProt2.splPol` (admissible by `splHok`).

## Deviations from Rocq

1. VOCABULARY (as `AxSpinProt5` deviation 1): `Z` ↦ `Int`, `agent` ↦ `Nat` (= `Agent`), `bv 8`
   ↦ `BitVec 8`, `gset` ↦ `GSet`, `list_to_set` ↦ `LawfulSet.ofList`, `gd_g GD` ↦ `GD.gdG`,
   `B0`/`B1` ↦ `b0`/`b1`, `base.NoDup` ↦ `List.Nodup`, `S j` ↦ `j + 1`.
2. CONTEXTS: Rocq section variables are explicit leading arguments in Rocq's order, only where
   Rocq's section mechanism includes them (§1 `lk x Cl cv`; §2 `lk x Cl cv GT nm`, then `Hcons`
   / `HlkX` where `Proof using` names them).  O2 STAGE C (as `AxSpinProt2` deviation 1): Rocq's
   `Tf` argument of `AxGA2` is gone.  `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any
   `hlc`; `axannotG Σ`+`axannotGS Σ` ↦ `[AxannotGS GF]`.  The local instance `s5_pol` is
   inlined as `splPol GT` (passed explicitly); `s5_G` is the reducible def `s5G lk x Cl cv GT
   nm` (passed explicitly, as `AxSpinProt2.splG`).
3. STATEMENT SHAPES (as `AxSpinProt2`/`AxSpinProt5`): wand chains ↦ `⊢ A -∗ B -∗ …`; pure
   premises stay `→`; `Forall P Rs` ↦ `∀ Rj, Rj ∈ Rs → P Rj`; the Rocq notations `OWN`/`LK`/`R5`
   are unfolded.

**Rocq → Lean name map.**  `X5` `X5`, `spin_ob5` `spinOb5`, `spin_R5` `spinR5`, `spin_init5`
`spinInit5`, `spin_R5_transportable` `spinR5Transportable`, `spin_Hob_alloc5` `spinHobAlloc5`,
`s5_G` `s5G`, `fe5_build` `fe5Build`, `lkw_nX` `lkwNX`, `lkw_cpu` `lkwCpu`, `nw_nX` `nwNX`,
`nw_cpu` `nwCpu`, `fe5_neutral` `fe5Neutral`, `fe5_claim` `fe5Claim`, `fe5_claim'` `fe5Claim'`,
`fe5_release'` `fe5Release'`, `fe5_lkread_held` `fe5LkreadHeld`, `fe5_lkread` `fe5Lkread`,
`fe5_RLwrite` `fe5RLwrite`, `fe5_Rbread` `fe5Rbread`, `fe5_cpuread` `fe5Cpuread`.
Lean-only (file-qualified): `AxSpinProt6.nwb` (a non-write writes no byte).

**Dropped:** none (21 Rocq decls incl. the local instance `s5_G`; `s5_pol` inlined; 22 Lean =
21 + 1 Lean-only).
-/
import Weak.AxSpinProt5

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 1. THE INSTANCE `spinOb5`: lock word + owned bytes `x` and lk->cpu (`Cl`) with Φ_cpu -/

def X5 (x : Int) (Cl : List Int) : GSet Int := ({x} : GSet Int) ∪ LawfulSet.ofList Cl

section inst5
variable {GF : BundledGFunctors} [AxlogG GF Hent] [SpinlockG GF]

def spinOb5 (lk x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (nm : spinN)
    (GD : Gdexec) (_ : Unit) (s : GSet Geid) : IProp GF :=
  iprop(⌜WC GD.gdG s ∧ CPUOK Cl cv GD.gdG s⌝ ∗ ownInv (X5 x Cl) nm.1 GD s ∗ lkInv nm.2 lk GD s)

/-- The lock's resource: TWO components -- `x` (value-generic) and lk->cpu. -/
def spinR5 (x : Int) (Cl : List Int) (nm : spinN) (GD : Gdexec) (e : Geid) : IProp GF :=
  iprop(RL nm.1 GD [x] e ∗ RL nm.1 GD Cl e)

def spinInit5 (lk x : Int) (Cl : List Int) (GD : Gdexec) (nm : spinN) (i : Agent) : IProp GF :=
  iprop(isLock nm.2 lk (spinR5 x Cl nm GD) ∗ notheld nm.2 lk i)

theorem spinR5Transportable (x : Int) (Cl : List Int) (nm : spinN) (GD : Gdexec) :
    rvwmoCatConsistent GD → lkTransportable GD (spinR5 (GF := GF) x Cl nm GD) := by
  intro Hcons e e' Hob
  unfold spinR5
  iintro ⟨H1, H2⟩
  isplitl [H1]
  · iapply (RLTransportable nm.1 GD [x] Hcons e e' Hob) $$ H1
  · iapply (RLTransportable nm.1 GD Cl Hcons e e' Hob) $$ H2

/-- GENESIS: all histories empty, `R5` parked in σ0's genesis box. -/
theorem spinHobAlloc5 (lk x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GD : Gdexec)
    (harts : List Agent) :
    harts.Nodup → x ∉ Cl → Cl.Nodup →
    ⊢ iprop(|==> ∃ (nm : spinN) (σ0 : Unit), spinOb5 (GF := GF) lk x Cl cv nm GD σ0 ∅ ∗
      [∗list] i ∈ harts, spinInit5 lk x Cl GD nm i) := by
  intro Hnd HxC HndC
  have Hdisj : ({x} : GSet Int) ## LawfulSet.ofList Cl :=
    LawfulSet.disjoint_singleton_left.2 (fun h => HxC (LawfulSet.mem_ofList.2 h))
  imod histAlloc (GF := GF) (X5 x Cl) ([] : List Hent) with ⟨%γx, H⟩
  unfold X5
  icases (BigSepS.bigSepS_union Hdisj).1 $$ H with ⟨Hx, HC⟩
  ihave Hx := BigSepS.bigSepS_singleton.1 $$ Hx
  ihave HC := (BigSepS.bigSepS_of_list HndC).1 $$ HC
  ihave Hx := (BigSepL.bigSepL_singleton
    (Φ := fun _ a => histAuth (GF := GF) γx a 1 ([] : List Hent))).2 $$ Hx
  ihave HRx := RLGenesis γx GD [x] $$ Hx
  ihave HRC := RLGenesis γx GD Cl $$ HC
  imod (lkInvAlloc lk GD harts (fun e => iprop(RL γx GD [x] e ∗ RL γx GD Cl e)) Hnd)
    $$ [HRx HRC] with ⟨%reg, Hinv, #Hil, Hnh⟩
  · iintro %e
    isplitl [HRx]
    · iapply HRx
    · iapply HRC
  imodintro
  iexists ((γx, reg) : spinN), ()
  isplitl [Hinv]
  · unfold spinOb5
    isplitr
    · ipureintro
      exact ⟨fun e w He => absurd He notElemOfEmpty, fun w Hw => absurd Hw notElemOfEmpty⟩
    isplitr [Hinv]
    · unfold ownInv
      iapply BigSepS.bigSepS_empty.2
      iempintro
    · iexact Hinv
  · iapply (BigSepL.bigSepL_impl (Φ := fun _ i => notheld (GF := GF) reg lk i)
      (Ψ := fun _ i => spinInit5 (GF := GF) lk x Cl GD (γx, reg) i)) $$ Hnh
    imodintro
    iintro %k %i %_ Hi
    unfold spinInit5 spinR5
    isplitl []
    · iexact Hil
    · iexact Hi

end inst5

/-- Rocq `#[local] Instance s5_G` (a named reducible def). -/
@[reducible] def s5G {GF : BundledGFunctors.{0,0,0}} [AxannotGS GF] [AxlogG GF Hent]
    [SpinlockG GF] (lk x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) : AxirisG GF :=
  shG (gtAdGd GT) spinN Unit (spinOb5 lk x Cl cv) nm

/-! # 2. THE RULE LEMMAS at `spinOb5` (flow equations, ∀σ, ∀ processed set; policy
`AxSpinProt2.splPol`, admissible by `splHok`) -/

/-- (Lean-only) A non-write writes no byte. -/
theorem AxSpinProt6.nwb (G : Gexec) (r : Geid) :
    gisW G r = false → ∀ a v, ¬ gwritesByte G r a v := by
  intro Hnw a v Hw
  have h := WeakRvwmoGraph.gwritesByteGisW _ _ _ _ Hw
  rw [Hnw] at h
  cases h

section rules5
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxlogG GF Hent] [SpinlockG GF]

/-- THE BUILDER: re-establishes `WC` and `CPUOK`, demanding Φ_cpu of the event. -/
theorem fe5Build (lk x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (e : Geid) (flowIn : Mea GF) (R : IProp GF) :
    ⊢ (∀ s : GSet Geid, ⌜e ∉ s⌝ -∗ ⌜WC (gtAdGd GT).gdG s⌝ -∗ ⌜WPh (gtAdGd GT).gdG s e⌝ -∗
        ⌜spSpol GT (gtAdGd GT) e ⊆ s⌝ -∗ ⌜CPUOK Cl cv (gtAdGd GT).gdG s⌝ -∗
        ownInv (X5 x Cl) nm.1 (gtAdGd GT) s -∗ lkInv nm.2 lk (gtAdGd GT) s -∗
        ([∗map] Rin ∈ flowIn, Rin) ==∗
        ▷ |==> (⌜cpuOk Cl cv (gtAdGd GT).gdG e⌝ ∗
          ownInv (X5 x Cl) nm.1 (gtAdGd GT) (({e} : GSet Geid) ∪ s) ∗
          lkInv nm.2 lk (gtAdGd GT) (({e} : GSet Geid) ∪ s) ∗ R)) -∗
      @flowEqDyn hlc GF _ (s5G lk x Cl cv GT nm) (gtAdGd GT) e
        (@Axpol.sPol (splPol GT) (gtAdGd GT) e) flowIn R := by
  iintro H
  unfold flowEqDyn
  iintro %σ %s %Hsub %Hnin Hob Hfi
  have Hwp := spolWP GT (gtAdGd GT) e s Hsub
  ihave Hob := (show @AxirisG.obStInterp GF (s5G lk x Cl cv GT nm) (gtAdGd GT) σ s ⊢
    spinOb5 lk x Cl cv nm (gtAdGd GT) σ s from .rfl) $$ Hob
  unfold spinOb5
  icases Hob with ⟨%Hp, Ho, Hl⟩
  obtain ⟨Hwc, Hok⟩ := Hp
  imod H $$ %s %Hnin %Hwc %Hwp %Hsub %Hok Ho Hl Hfi with H
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imod H with ⟨%He, Ho, Hl, HR⟩
  imodintro
  iexists σ
  isplitl [Ho Hl]
  · iapply (show spinOb5 lk x Cl cv nm (gtAdGd GT) σ (({e} : GSet Geid) ∪ s) ⊢
      @AxirisG.obStInterp GF (s5G lk x Cl cv GT nm) (gtAdGd GT) σ (({e} : GSet Geid) ∪ s)
      from .rfl)
    unfold spinOb5
    isplitr
    · ipureintro
      exact ⟨WCInsert _ s e Hwc Hwp, CPUOKInsert Cl cv _ s e Hok He⟩
    isplitl [Ho]
    · iexact Ho
    · iexact Hl
  · iexact HR

theorem lkwNX (lk x : Int) (Cl : List Int) (GT : GdexecT) (HlkX : lk ∉ X5 x Cl) (e : Geid) :
    (∀ a v, gwritesByte (gtAdGd GT).gdG e a v → a = lk) →
    ∀ a v, a ∈ X5 x Cl → ¬ gwritesByte (gtAdGd GT).gdG e a v := by
  intro Hsg a v Ha Hw
  rw [Hsg a v Hw] at Ha
  exact HlkX Ha

theorem lkwCpu (lk x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (HlkX : lk ∉ X5 x Cl) (e : Geid) :
    (∀ a v, gwritesByte (gtAdGd GT).gdG e a v → a = lk) → cpuOk Cl cv (gtAdGd GT).gdG e := by
  intro Hsg
  apply cpuOkNw
  intro a v Ha Hw
  apply HlkX
  rw [← Hsg a v Hw]
  exact elemOfUnionR (LawfulSet.mem_ofList.1 Ha)

theorem nwNX (x : Int) (Cl : List Int) (GT : GdexecT) (e : Geid) :
    gisW (gtAdGd GT).gdG e = false → ∀ a v, a ∈ X5 x Cl → ¬ gwritesByte (gtAdGd GT).gdG e a v :=
  fun Hnw a v _ => AxSpinProt6.nwb _ e Hnw a v

theorem nwCpu (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT) (e : Geid) :
    gisW (gtAdGd GT).gdG e = false → cpuOk Cl cv (gtAdGd GT).gdG e :=
  fun Hnw => cpuOkNw Cl cv _ e (fun a v _ => AxSpinProt6.nwb _ e Hnw a v)

/-- ACQUIRE-FAIL (neutral RMW). -/
theorem fe5Neutral (lk x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (_Hcons : rvwmoCatConsistent (gtAdGd GT)) (HlkX : lk ∉ X5 x Cl) (e : Geid)
    (t : Nat) (v : BitVec 8) :
    greadsByte (gtAdGd GT).gdG e lk t v → v ≠ b0 → gwritesByte (gtAdGd GT).gdG e lk b1 →
    (∀ a v', gwritesByte (gtAdGd GT).gdG e a v' → a = lk) →
    ⊢ @flowEqDyn hlc GF _ (s5G lk x Cl cv GT nm) (gtAdGd GT) e
        (@Axpol.sPol (splPol GT) (gtAdGd GT) e) (∅ : Mea GF) iprop(True) := by
  intro Hr Hv Hw Hsg
  iapply fe5Build
  iintro %s %Hn %_ %_ %_ %_ Ho Hl _
  imodintro
  inext
  imodintro
  isplitr
  · ipureintro
    exact lkwCpu lk x Cl cv GT HlkX e Hsg
  isplitl [Ho]
  · iapply (ownInvOther (X5 x Cl) nm.1 (gtAdGd GT) s e Hn (lkwNX lk x Cl GT HlkX e Hsg)) $$ Ho
  isplitl [Hl]
  · iapply (lkInvNeutral nm.2 lk (gtAdGd GT) s e t v Hn Hr Hv Hw) $$ Hl
  · itrivial

/-- ACQUIRE-SUCCESS, first acquisition: `notheld` IN HAND. -/
theorem fe5Claim (lk x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (Hcons : rvwmoCatConsistent (gtAdGd GT)) (HlkX : lk ∉ X5 x Cl) (c : Geid)
    (oz : Option Geid) :
    lkClaim lk (gtAdGd GT).gdG c oz → (∀ a v', gwritesByte (gtAdGd GT).gdG c a v' → a = lk) →
    ⊢ notheld nm.2 lk c.1 -∗ isLock nm.2 lk (spinR5 x Cl nm (gtAdGd GT)) -∗
      @flowEqDyn hlc GF _ (s5G lk x Cl cv GT nm) (gtAdGd GT) c
        (@Axpol.sPol (splPol GT) (gtAdGd GT) c) (∅ : Mea GF)
        iprop(locked nm.2 lk c.1 c ∗ spinR5 x Cl nm (gtAdGd GT) c) := by
  intro Hcl Hsg
  iintro Hnh #Hil
  iapply fe5Build
  iintro %s %Hn %Hwc %Hwp %_ %_ Ho Hl _
  imod (lkInvClaim nm.2 lk (gtAdGd GT) s c oz (spinR5 x Cl nm (gtAdGd GT)) Hcons Hwc Hwp Hn Hcl
    (spinR5Transportable x Cl nm (gtAdGd GT) Hcons)) $$ [$Hl $Hnh $Hil] with H
  imodintro
  inext
  icases H with ⟨Hl, Hlk, HR⟩
  imodintro
  isplitr
  · ipureintro
    exact lkwCpu lk x Cl cv GT HlkX c Hsg
  isplitl [Ho]
  · iapply (ownInvOther (X5 x Cl) nm.1 (gtAdGd GT) s c Hn (lkwNX lk x Cl GT HlkX c Hsg)) $$ Ho
  isplitl [Hl]
  · iexact Hl
  isplitl [Hlk]
  · iexact Hlk
  · iexact HR

/-- REQUIRED (2): ACQUIRE-SUCCESS with `notheld` drawn through `flowIn`. -/
theorem fe5Claim' (lk x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (Hcons : rvwmoCatConsistent (gtAdGd GT)) (HlkX : lk ∉ X5 x Cl) (c : Geid)
    (oz : Option Geid) (Q : IProp GF) (flowIn : Mea GF) :
    lkClaim lk (gtAdGd GT).gdG c oz → (∀ a v', gwritesByte (gtAdGd GT).gdG c a v' → a = lk) →
    ⊢ isLock nm.2 lk (spinR5 x Cl nm (gtAdGd GT)) -∗
      (([∗map] Rin ∈ flowIn, Rin) -∗ notheld nm.2 lk c.1 ∗ Q) -∗
      @flowEqDyn hlc GF _ (s5G lk x Cl cv GT nm) (gtAdGd GT) c
        (@Axpol.sPol (splPol GT) (gtAdGd GT) c) flowIn
        iprop((locked nm.2 lk c.1 c ∗ spinR5 x Cl nm (gtAdGd GT) c) ∗ Q) := by
  intro Hcl Hsg
  iintro #Hil Hfi
  iapply fe5Build
  iintro %s %Hn %Hwc %Hwp %_ %_ Ho Hl Hin
  ihave ⟨Hnh, HQ⟩ := Hfi $$ Hin
  imod (lkInvClaim nm.2 lk (gtAdGd GT) s c oz (spinR5 x Cl nm (gtAdGd GT)) Hcons Hwc Hwp Hn Hcl
    (spinR5Transportable x Cl nm (gtAdGd GT) Hcons)) $$ [$Hl $Hnh $Hil] with H
  imodintro
  inext
  icases H with ⟨Hl, Hlk, HR⟩
  imodintro
  isplitr
  · ipureintro
    exact lkwCpu lk x Cl cv GT HlkX c Hsg
  isplitl [Ho]
  · iapply (ownInvOther (X5 x Cl) nm.1 (gtAdGd GT) s c Hn (lkwNX lk x Cl GT HlkX c Hsg)) $$ Ho
  isplitl [Hl]
  · iexact Hl
  isplitl [Hlk HR]
  · isplitl [Hlk]
    · iexact Hlk
    · iexact HR
  · iexact HQ

/-- REQUIRED (1): THE RELEASE, each component of `R` drawn from `flowIn` at ITS OWN anchor;
deposits `notheld i`. -/
theorem fe5Release' (lk x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (Hcons : rvwmoCatConsistent (gtAdGd GT)) (HlkX : lk ∉ X5 x Cl) (w : Geid)
    (i : Nat) (c : Geid) (R : Geid → IProp GF) (Rs : List (Geid → IProp GF)) (flowIn : Mea GF) :
    zw lk (gtAdGd GT).gdG w → (∀ t v, ¬ greadsByte (gtAdGd GT).gdG w lk t v) →
    (∀ a v', gwritesByte (gtAdGd GT).gdG w a v' → a = lk) →
    (∀ Rj, Rj ∈ Rs → lkTransportable (gtAdGd GT) Rj) → (([∗list] Rj ∈ Rs, Rj w) ⊢ R w) →
    ⊢ isLock nm.2 lk R -∗
      (([∗map] Rin ∈ flowIn, Rin) -∗
        locked nm.2 lk i c ∗ [∗list] Rj ∈ Rs, ∃ a, ⌜gobCat (gtAdGd GT) a w⌝ ∗ Rj a) -∗
      @flowEqDyn hlc GF _ (s5G lk x Cl cv GT nm) (gtAdGd GT) w
        (@Axpol.sPol (splPol GT) (gtAdGd GT) w) flowIn iprop(notheld nm.2 lk i) := by
  intro Hzw Hnr Hsg Htr HRs
  iintro #Hil Hfi
  iapply fe5Build
  iintro %s %Hn %Hwc %Hwp %_ %_ Ho Hl Hin
  ihave ⟨Hlk, HRc⟩ := Hfi $$ Hin
  ihave HRc := (transportComps (gtAdGd GT) Rs w Htr) $$ HRc
  ihave HR := HRs $$ HRc
  ihave H := (lkInvRelease nm.2 lk (gtAdGd GT) s w i c R Hcons Hwc Hn Hzw Hnr)
    $$ [$Hl $Hlk $Hil $HR]
  imodintro
  inext
  imod H with ⟨Hl, Hnh, -⟩
  imodintro
  isplitr
  · ipureintro
    exact lkwCpu lk x Cl cv GT HlkX w Hsg
  isplitl [Ho]
  · iapply (ownInvOther (X5 x Cl) nm.1 (gtAdGd GT) s w Hn (lkwNX lk x Cl GT HlkX w Hsg)) $$ Ho
  isplitl [Hl]
  · iexact Hl
  · iexact Hnh

/-- REQUIRED (3): THE HOLDER's plain read of the lock byte, `locked i c` drawn through
`flowIn`: deposits `locked ∗ Q` back and `⌜v ≠ b0⌝` AT THE READ. -/
theorem fe5LkreadHeld (lk x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (Hcons : rvwmoCatConsistent (gtAdGd GT)) (_HlkX : lk ∉ X5 x Cl) (r : Geid)
    (i : Nat) (c : Geid) (Q : IProp GF) (flowIn : Mea GF) :
    gisW (gtAdGd GT).gdG r = false → WeakRvwmoGraph.gpo (gtAdGd GT).gdG c r →
    nolk lk (gtAdGd GT).gdG c r →
    ⊢ (([∗map] Rin ∈ flowIn, Rin) -∗ locked nm.2 lk i c ∗ Q) -∗
      @flowEqDyn hlc GF _ (s5G lk x Cl cv GT nm) (gtAdGd GT) r
        (@Axpol.sPol (splPol GT) (gtAdGd GT) r) flowIn
        iprop((locked nm.2 lk i c ∗ Q) ∗
          ⌜∀ t v, greadsByte (gtAdGd GT).gdG r lk t v → v ≠ b0⌝) := by
  intro Hnw Hpo Hnl
  iintro Hfi
  iapply fe5Build
  iintro %s %Hn %Hwc %Hwp %_ %_ Ho Hl Hin
  ihave ⟨Hlk, HQ⟩ := Hfi $$ Hin
  icases (lkInvReadHeld nm.2 lk (gtAdGd GT) s r i c Hcons Hwp Hn Hnw Hpo Hnl) $$ [$Hl $Hlk]
    with ⟨Hl, Hlk, %Hf⟩
  imodintro
  inext
  imodintro
  isplitr
  · ipureintro
    exact nwCpu Cl cv GT r Hnw
  isplitl [Ho]
  · iapply (ownInvOther (X5 x Cl) nm.1 (gtAdGd GT) s r Hn (nwNX x Cl GT r Hnw)) $$ Ho
  isplitl [Hl]
  · iexact Hl
  · isplitl [Hlk HQ]
    · isplitl [Hlk]
      · iexact Hlk
      · iexact HQ
    · ipureintro
      exact Hf

/-- A plain read of the lock byte by anyone (frame; records nothing). -/
theorem fe5Lkread (lk x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (Hcons : rvwmoCatConsistent (gtAdGd GT)) (_HlkX : lk ∉ X5 x Cl) (r : Geid) :
    gisW (gtAdGd GT).gdG r = false →
    ⊢ @flowEqDyn hlc GF _ (s5G lk x Cl cv GT nm) (gtAdGd GT) r
        (@Axpol.sPol (splPol GT) (gtAdGd GT) r) (∅ : Mea GF) iprop(True) := by
  intro Hnw
  iapply fe5Build
  iintro %s %Hn %Hwc %Hwp %_ %_ Ho Hl _
  imodintro
  inext
  imodintro
  isplitr
  · ipureintro
    exact nwCpu Cl cv GT r Hnw
  isplitl [Ho]
  · iapply (ownInvOther (X5 x Cl) nm.1 (gtAdGd GT) s r Hn (nwNX x Cl GT r Hnw)) $$ Ho
  isplitl [Hl]
  · iapply (lkInvRead nm.2 lk (gtAdGd GT) s r Hcons Hwp Hn Hnw) $$ Hl
  · itrivial

/-- THE OWNED WRITE of a component `RL Cw` (`Cw = [x]`, or `Cw = Cl` = lk->cpu, aligned full
width), WITH Φ_cpu AS SIDE CONDITION. -/
theorem fe5RLwrite (lk x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (_Hcons : rvwmoCatConsistent (gtAdGd GT)) (_HlkX : lk ∉ X5 x Cl) (w e : Geid)
    (Cw : List Int) (Q : IProp GF) (flowIn : Mea GF) :
    gisW (gtAdGd GT).gdG w = true → gmoLt (gtAdGd GT).gdG e w →
    (∀ a, a ∈ Cw → ∃ v, gwritesByte (gtAdGd GT).gdG w a v) →
    (∀ a v, gwritesByte (gtAdGd GT).gdG w a v → a ∈ Cw) → lk ∉ Cw →
    cpuOk Cl cv (gtAdGd GT).gdG w →
    ⊢ (([∗map] Rin ∈ flowIn, Rin) -∗ Q ∗ RL nm.1 (gtAdGd GT) Cw e) -∗
      @flowEqDyn hlc GF _ (s5G lk x Cl cv GT nm) (gtAdGd GT) w
        (@Axpol.sPol (splPol GT) (gtAdGd GT) w) flowIn
        iprop(Q ∗ RL nm.1 (gtAdGd GT) Cw w) := by
  intro Hisw Hew Hall Honly Hnlk Hok
  iintro Hfi
  iapply fe5Build
  iintro %s %Hn %_ %_ %_ %_ Ho Hl Hin
  ihave ⟨HQ, HR⟩ := Hfi $$ Hin
  imod (RLWrite nm.1 (gtAdGd GT) (X5 x Cl) Cw s e w Hn Hew Hall Honly) $$ [$Ho $HR]
    with ⟨Ho, HR⟩
  imodintro
  inext
  imodintro
  isplitr
  · ipureintro
    exact Hok
  isplitl [Ho]
  · iexact Ho
  isplitl [Hl]
  · iapply (lkInvOther nm.2 lk (gtAdGd GT) s w Hn (fun v Hv => Hnlk (Honly lk v Hv))
      (fun ⟨_, Hnw⟩ => by rw [Hisw] at Hnw; cases Hnw)) $$ Hl
  · isplitl [HQ]
    · iexact HQ
    · iexact HR

/-- THE OWNED PLACEMENT READ of byte `a` under `RL [a] e` (the holder's read of a
lock-protected byte; `Q` framed). -/
theorem fe5Rbread (lk x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (Hcons : rvwmoCatConsistent (gtAdGd GT)) (_HlkX : lk ∉ X5 x Cl) (r e : Geid)
    (a : Int) (t : Nat) (v : BitVec 8) (Q : IProp GF) (flowIn : Mea GF) :
    a ∈ X5 x Cl → gisW (gtAdGd GT).gdG r = false → ¬ lkread lk (gtAdGd GT).gdG r →
    (∀ w v', gwritesByte (gtAdGd GT).gdG w a v' → w.1 = r.1 → False) →
    greadsByte (gtAdGd GT).gdG r a t v → gmoLt (gtAdGd GT).gdG e r →
    ⊢ (([∗map] Rin ∈ flowIn, Rin) -∗ Q ∗ RL nm.1 (gtAdGd GT) [a] e) -∗
      @flowEqDyn hlc GF _ (s5G lk x Cl cv GT nm) (gtAdGd GT) r
        (@Axpol.sPol (splPol GT) (gtAdGd GT) r) flowIn
        iprop((Q ∗ RL nm.1 (gtAdGd GT) [a] e) ∗
          ⌜t = 0 ∨ ∃ w, gwriteAt (gtAdGd GT).gdG t = some w ∧
            gwritesByte (gtAdGd GT).gdG w a v ∧ (w = e ∨ gmoLt (gtAdGd GT).gdG w e)⌝) := by
  intro HaX Hnw Hnr Hnpo Hrd Her
  iintro Hfi
  iapply fe5Build
  iintro %s %Hn %Hwc %Hwp %_ %_ #Ho Hl Hin
  ihave ⟨HQ, HR⟩ := Hfi $$ Hin
  unfold RL
  ihave HR := BigSepL.bigSepL_singleton.1 $$ HR
  ihave ⟨HR, %Hv⟩ := (RbReadPlace nm.1 (gtAdGd GT) (X5 x Cl) a s e r t v Hcons HaX Hnpo Hrd Her
    Hwp) $$ [$Ho $HR]
  ihave HR := (BigSepL.bigSepL_singleton
    (Φ := fun _ b => Rb (GF := GF) nm.1 (gtAdGd GT) b e)).2 $$ HR
  imodintro
  inext
  imodintro
  isplitr
  · ipureintro
    exact nwCpu Cl cv GT r Hnw
  isplitl []
  · iapply (ownInvOther (X5 x Cl) nm.1 (gtAdGd GT) s r Hn (nwNX x Cl GT r Hnw)) $$ Ho
  isplitl [Hl]
  · iapply (lkInvOther nm.2 lk (gtAdGd GT) s r Hn
      (fun v' => AxSpinProt6.nwb _ r Hnw lk v') Hnr) $$ Hl
  · isplitl [HQ HR]
    · isplitl [HQ]
      · iexact HQ
      · iexact HR
    · ipureintro
      exact Hv

/-- THE RACY READ of lk->cpu (any hart, holder or not): deposits the two-case fact `rdFact`
AT THE READ. -/
theorem fe5Cpuread (lk x : Int) (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (Hcons : rvwmoCatConsistent (gtAdGd GT)) (_HlkX : lk ∉ X5 x Cl) (r : Geid) :
    gisW (gtAdGd GT).gdG r = false → ¬ lkread lk (gtAdGd GT).gdG r →
    ⊢ @flowEqDyn hlc GF _ (s5G lk x Cl cv GT nm) (gtAdGd GT) r
        (@Axpol.sPol (splPol GT) (gtAdGd GT) r) (∅ : Mea GF)
        iprop(⌜rdFact Cl cv (gtAdGd GT).gdG r⌝) := by
  intro Hnw Hnr
  iapply fe5Build
  iintro %s %Hn %Hwc %Hwp %_ %Hok Ho Hl _
  have Hf : rdFact Cl cv (gtAdGd GT).gdG r := by
    intro a t v _ Hrd
    have Hs := (Hcons.2.2.1 r a t v Hrd).1
    cases t with
    | zero => exact Or.inl ⟨rfl, Hs⟩
    | succ j =>
      right
      obtain ⟨w, Hat, Hw, Hvis⟩ := Hs
      refine ⟨w, Hat, Hw, ?_⟩
      by_cases Heq : w.1 = r.1
      · exact Or.inr ⟨Heq, Hvis⟩
      · refine Or.inl ⟨Heq, Hok w (Hwp w (WeakRvwmoGraph.gwritesByteGisW _ _ _ _ Hw) ?_)⟩
        exact catGrfeGmo (gtAdGd GT) w r Hcons ⟨⟨a, j + 1, v, Hrd, Hat⟩, Heq⟩
  imodintro
  inext
  imodintro
  isplitr
  · ipureintro
    exact nwCpu Cl cv GT r Hnw
  isplitl [Ho]
  · iapply (ownInvOther (X5 x Cl) nm.1 (gtAdGd GT) s r Hn (nwNX x Cl GT r Hnw)) $$ Ho
  isplitl [Hl]
  · iapply (lkInvOther nm.2 lk (gtAdGd GT) s r Hn
      (fun v' => AxSpinProt6.nwb _ r Hnw lk v') Hnr) $$ Hl
  · ipureintro
    exact Hf

end rules5

end Weak
