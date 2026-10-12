/-
Weak: **Phase 1a, part 2 of the spinlock plan -- the CONCRETE INSTANCE** (lock word at `lk` + one
owned byte `x`) at the gated tagged route's `axGA2`, its POLICY, the policy's `Hok` for
`AxSpinGate.tierAAdequacyAnnGateT`, the allocation `spinHobAlloc`, and the RULE LEMMAS as flow
equations (`flowEqDyn`, ∀σ, ∀ processed set) -- the shape `AxSpinWit` uses.  Then WPd shells for
the exclusive RMW halves (consumed by `AxSpinProt3`).

Rocq: `iris/AxSpinProt2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

POLICY `splPol GT`: `sPol` = `AxSpinWit.spSpol` (gmo-earlier writes ∪ tagged gate sources);
`lobp` = same-hart po-earlier memory events gmo-before (`splLobp`).
RULE LEMMAS (§3; each a `flowEqDyn` at the instance, every protocol fact DERIVED inside, nothing
about σ assumed):
  `AxSpinProt2.feNeutral`  RMW reading `≠ b0`, writing `b1`: hands nothing;
  `feClaim`    RMW reading `b0` (ACQUIRE SUCCESS): captures the hart's `notheld` (+ persistent
               `isLock R`), deposits `locked i c ∗ R c`;
  `feRelease`  the zero-store: consumes `locked i c ∗ R a` (from the flow-in annotations),
               `gobCat a w`; parks `R w`; deposits `notheld i` and THE GATE-DELIVERED READ FACT
               (every plain read `r` of `lk` in the handout with `gpo c r` and no lock write
               po-between reads `≠ b0`);
  `feLkread`   a plain read of `lk`; `feOtherRead` any other non-write non-lock read;
  `feXwrite`/`feXread`  the owned byte under the lock's `R` (`AxSpinProt.Rx`).
The ACQUIRE-FAIL of the spin loop is `feNeutral` (an amoswap that reads 1).
§4 generic step facts at the exclusive RMW hand nodes (read half / write half / fence);
§5 WPd shells for the RMW halves at any `axGA2` instance.

## Deviations from Rocq

1. O2 STAGE C (as `AxSpinWit` deviation 1 / `AxClsStep2` deviation 2): no text oracle -- Rocq's
   `Tf`/`T`/`img` arguments are gone (`rmwAstepWrite`, `rmwWriteInv`, `fenceAstep`, the
   instance `splG`, `tierAWpd`).  `rdAstepVacuous` (Rocq: under the empty text `Tf`, at
   section `GD`) takes `(classify ak).akIfetch = false` and no `GD` (a fetch is an admin step in
   Lean).  `AxOpsem.astepProg`'s program arm in `wpdMPreStepDef` carries the image pin premise
   (ignored by the shells).
2. CONTEXTS: Rocq section variables are explicit leading arguments in Rocq's order, only where
   Rocq's section mechanism includes them (`lk x [Hxl] GT nm [Hcons]` in §3; `cpu` in §4; `GD N
   obSt0 obi nm cpu` in §5).  `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc`;
   `GF : BundledGFunctors.{0,0,0}`; `axannotG Σ`+`axannotGS Σ` ↦ `[AxannotGS GF]`.  Rocq's local
   instances `spl_pol_i` (inlined as `splPol GT`, passed explicitly) and `spl_G` (the reducible
   def `splG`); `shG2` is `AxSpinWit.shG` (the same `axGA2` record).  §4's `runs2` drops the
   unused `axirisG Σ` context.  The policy binder of §5 is the named `[pol : Axpol]`.
3. STATEMENT SHAPES (as `AxSpinWit`): wand chains `A -∗ B` ↦ `⊢ A -∗ B`; pure premises stay `→`;
   `B0`/`B1` ↦ `b0`/`b1`; `S k` ↦ `k + 1`; `l !! k` ↦ `l[k]?`; `inl (b, None)` ↦ `.Ok (b, none)`;
   `base.NoDup` ↦ `List.Nodup`.  `spin_N` is the abbrev `spinN`.
4. `readInvAny` inverts the Lean read step's two RAM arms (`akLatest` false/true); its i-cache
   arm is refuted from `areadStep`'s `wlRd` (no premise needed).  `wob1`'s proof uses
   `nthByteBv8` (AxClsStep2).

**Rocq → Lean name map.**  `spl_lobp` `splLobp`, `spl_pol` `splPol`, `elem_of_spl_lobp`
`elemOfSplLobp`, `spl_axpol_wf` `splAxpolWf`, `spl_Hok` `splHok`, `spol_WP` `spolWP`, `spin_N`
`spinN`, `spin_ob` `spinOb`, `spin_R` `spinR`, `spin_init` `spinInit`, `spin_Hob_alloc`
`spinHobAlloc`, `spl_G` `splG`, `fe_build` `feBuild`, `nx_of` `nxOf`, `fe_neutral`
`AxSpinProt2.feNeutral` (duplicated Rocq name), `fe_claim` `feClaim`, `fe_release` `feRelease`,
`fe_lkread` `feLkread`, `fe_other_read` `feOtherRead`, `fe_xwrite` `feXwrite`, `fe_xread`
`feXread`, `wob1` `wob1`, `read_inv_any` `readInvAny`, `rmw_aread` `rmwAread`,
`rmw_astep_write` `rmwAstepWrite`, `rmw_write_inv` `rmwWriteInv`, `no_read_at_xwrite`
`noReadAtXwrite`, `fence_astep` `fenceAstep`, `run_rmw_read` `runRmwRead`, `run_rmw_write`
`runRmwWrite`, `run_fence` `runFence`, `sh_skip2` `shSkip2`, `rd_astep_vacuous`
`rdAstepVacuous`, `sh_rmw_read` `shRmwRead`, `sh_rmw_write` `shRmwWrite`.

**Dropped:** none.  (`spl_pol_i`/`shG2` local instances inlined, deviation 2.)
-/
import Weak.AxSpinWit
import Weak.AxSpinProt

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 1. THE POLICY -/

def splLobp (GD : Gdexec) (e : Geid) : GSet Geid :=
  LawfulSet.ofList (GD.gdG.gxGmo.filter (fun e' =>
    gmemB GD.gdG e' && gpoB GD.gdG e' e && gmoLtB GD.gdG e' e))

@[reducible] def splPol (GT : GdexecT) : Axpol where
  sPol := spSpol GT
  lobp := splLobp

theorem elemOfSplLobp (GD : Gdexec) (e e' : Geid) :
    e' ∈ splLobp GD e ↔ e' ∈ GD.gdG.gxGmo ∧ gmemB GD.gdG e' = true ∧
      WeakRvwmoGraph.gpo GD.gdG e' e ∧ gmoLt GD.gdG e' e := by
  unfold splLobp
  rw [elemOfListToSet, List.mem_filter]
  simp only [Bool.and_eq_true, gpoBSpec, gmoLtBSpec]
  constructor
  · rintro ⟨h, ⟨ha, hb⟩, hc⟩
    exact ⟨h, ha, hb, hc⟩
  · rintro ⟨h, ha, hb, hc⟩
    exact ⟨h, ⟨ha, hb⟩, hc⟩

theorem splAxpolWf (GT : GdexecT) : @axpolWf (splPol GT) := by
  intro GD i k e' He'
  obtain ⟨-, Hm, ⟨Hh, Hlt, -, -⟩, -⟩ := (elemOfSplLobp GD (i, k) e').1 He'
  exact (elemOfEidsBefore GD i k e').2 ⟨Hh, Hlt, Hm⟩

/-- `Hok`: writes gmo-before (`polDS` via `gsrcTReal'`, i.e. `ctrlClosed`), gate sources (the
gate arm), and po-earlier gmo-before lob-predecessors (`polDS` via `gsrcTMono`). -/
theorem splHok (GT : GdexecT) (HconsT : rvwmoCatConsistentT GT) (Hcl : ctrlClosed GT) :
    ∀ e e', e' ∈ @Axpol.sPol (splPol GT) (gtAdGd GT) e ∪ @Axpol.lobp (splPol GT) (gtAdGd GT) e →
      polDS GT.gtG (gsrcT GT) e' e ∨ e' ∈ gsrcT GT e := by
  intro e e' Hin
  rcases elemOfUnion.1 Hin with Hin | Hin
  · exact spHok GT HconsT Hcl e e' (elemOfUnionL Hin)
  · left
    obtain ⟨-, -, Hpo, Hlt⟩ := (elemOfSplLobp _ e e').1 Hin
    refine ⟨Hlt, fun s Hs => .inr ⟨?_, Hpo⟩⟩
    exact gsrcTMono GT e' e Hpo s Hs

theorem spolWP (GT : GdexecT) (GD : Gdexec) (e : Geid) (s : GSet Geid) :
    spSpol GT GD e ⊆ s → WPh GD.gdG s e := by
  intro Hsub w Hw Hlt
  refine Hsub w (elemOfUnionL (elemOfListToSet.2 (List.mem_filter.2 ⟨Hlt.1, ?_⟩)))
  rw [Hw, (gmoLtBSpec _ _ _).2 Hlt]

/-! # 2. THE INSTANCE: `spinOb` = WC ∗ own component ∗ lock component -/

abbrev spinN : Type := GName × GName

section inst
variable {GF : BundledGFunctors} [AxlogG GF Hent] [SpinlockG GF]

/-- `nm.1` = the owned bytes' history name, `nm.2` = the lock registry. -/
def spinOb (lk x : Int) (nm : spinN) (GD : Gdexec) (_ : Unit) (s : GSet Geid) : IProp GF :=
  iprop(⌜WC GD.gdG s⌝ ∗ ownInv ({x} : GSet Int) nm.1 GD s ∗ lkInv nm.2 lk GD s)

/-- The lock's protected resource for the certificates: `x` owned, its locked history writing
only `b1`. -/
def spinR (x : Int) (nm : spinN) (GD : Gdexec) : Geid → IProp GF := Rx nm.1 x GD

def spinInit (lk x : Int) (GD : Gdexec) (nm : spinN) (i : Agent) : IProp GF :=
  iprop(isLock nm.2 lk (spinR x nm GD) ∗ notheld nm.2 lk i)

theorem spinHobAlloc (lk x : Int) (GD : Gdexec) (harts : List Agent) (Hnd : harts.Nodup) :
    ⊢ iprop(|==> ∃ (nm : spinN) (σ0 : Unit), spinOb (GF := GF) lk x nm GD σ0 ∅ ∗
      [∗list] i ∈ harts, spinInit lk x GD nm i) := by
  imod histAlloc (GF := GF) ({x} : GSet Int) ([] : List Hent) with ⟨%γx, H⟩
  ihave H := BigSepS.bigSepS_singleton.1 $$ H
  ihave HR := RxGenesis γx x GD $$ H
  imod (lkInvAlloc lk GD harts (Rx γx x GD) Hnd) $$ HR with ⟨%reg, Hinv, #Hil, Hnh⟩
  imodintro
  iexists ((γx, reg) : spinN), ()
  isplitl [Hinv]
  · unfold spinOb
    isplitr
    · ipureintro
      intro e w He
      exact absurd He notElemOfEmpty
    isplitr [Hinv]
    · unfold ownInv
      iapply BigSepS.bigSepS_empty.2
      iempintro
    · iexact Hinv
  · iapply (BigSepL.bigSepL_impl (Φ := fun _ i => notheld (GF := GF) reg lk i)
      (Ψ := fun _ i => spinInit (GF := GF) lk x GD (γx, reg) i)) $$ Hnh
    imodintro
    iintro %k %i %_ Hi
    unfold spinInit spinR
    isplitl []
    · iexact Hil
    · iexact Hi

end inst

/-- Rocq `Local Instance spl_G` (a named reducible def). -/
@[reducible] def splG {GF : BundledGFunctors.{0,0,0}} [AxannotGS GF] [AxlogG GF Hent]
    [SpinlockG GF] (lk x : Int) (GT : GdexecT) (nm : spinN) : AxirisG GF :=
  shG (gtAdGd GT) spinN Unit (spinOb lk x) nm

/-! # 3. THE RULE LEMMAS (flow equations at the instance) -/

section rules
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxlogG GF Hent] [SpinlockG GF]

/-- THE BUILDER: a flow equation from a per-component step. -/
theorem feBuild (lk x : Int) (GT : GdexecT) (nm : spinN) (e : Geid) (flowIn : Mea GF)
    (R : IProp GF) :
    ⊢ (∀ s : GSet Geid, ⌜e ∉ s⌝ -∗ ⌜WC (gtAdGd GT).gdG s⌝ -∗ ⌜WPh (gtAdGd GT).gdG s e⌝ -∗
        ⌜spSpol GT (gtAdGd GT) e ⊆ s⌝ -∗ ownInv ({x} : GSet Int) nm.1 (gtAdGd GT) s -∗
        lkInv nm.2 lk (gtAdGd GT) s -∗ ([∗map] Rin ∈ flowIn, Rin) ==∗
        ▷ |==> (ownInv ({x} : GSet Int) nm.1 (gtAdGd GT) (({e} : GSet Geid) ∪ s) ∗
          lkInv nm.2 lk (gtAdGd GT) (({e} : GSet Geid) ∪ s) ∗ R)) -∗
      @flowEqDyn hlc GF _ (splG lk x GT nm) (gtAdGd GT) e
        (@Axpol.sPol (splPol GT) (gtAdGd GT) e) flowIn R := by
  iintro H
  unfold flowEqDyn
  iintro %σ %s %Hsub %Hnin Hob Hfi
  have Hwp := spolWP GT (gtAdGd GT) e s Hsub
  ihave Hob := (show @AxirisG.obStInterp GF (splG lk x GT nm) (gtAdGd GT) σ s ⊢
    spinOb lk x nm (gtAdGd GT) σ s from .rfl) $$ Hob
  unfold spinOb
  icases Hob with ⟨%Hwc, Ho, Hl⟩
  imod H $$ %s %Hnin %Hwc %Hwp %Hsub Ho Hl Hfi with H
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imod H with ⟨Ho, Hl, HR⟩
  imodintro
  iexists σ
  isplitl [Ho Hl]
  · iapply (show spinOb lk x nm (gtAdGd GT) σ (({e} : GSet Geid) ∪ s) ⊢
      @AxirisG.obStInterp GF (splG lk x GT nm) (gtAdGd GT) σ (({e} : GSet Geid) ∪ s) from .rfl)
    unfold spinOb
    isplitr
    · ipureintro
      exact WCInsert _ s e Hwc Hwp
    isplitl [Ho]
    · iexact Ho
    · iexact Hl
  · iexact HR

/-- WIDTH-GENERIC side condition of the lock arms: the event does not write the owned byte. -/
theorem nxOf (x : Int) (GT : GdexecT) (e : Geid) :
    (∀ v', ¬ gwritesByte (gtAdGd GT).gdG e x v') →
    ∀ a v', a ∈ ({x} : GSet Int) → ¬ gwritesByte (gtAdGd GT).gdG e a v' := by
  intro Hs a v' Ha Hw
  rw [elemOfSingleton.1 Ha] at Hw
  exact Hs _ Hw

/-- ACQUIRE-FAIL (and every neutral RMW). -/
theorem AxSpinProt2.feNeutral (lk x : Int) (GT : GdexecT) (nm : spinN) (e : Geid) (t : Nat)
    (v : BitVec 8) :
    greadsByte (gtAdGd GT).gdG e lk t v → v ≠ b0 → gwritesByte (gtAdGd GT).gdG e lk b1 →
    (∀ v', ¬ gwritesByte (gtAdGd GT).gdG e x v') →
    ⊢ @flowEqDyn hlc GF _ (splG lk x GT nm) (gtAdGd GT) e
        (@Axpol.sPol (splPol GT) (gtAdGd GT) e) (∅ : Mea GF) iprop(True) := by
  intro Hr Hv Hw Hs
  iapply feBuild
  iintro %s %Hn %_ %_ %_ Ho Hl _
  imodintro
  inext
  imodintro
  isplitl [Ho]
  · iapply (ownInvOther ({x} : GSet Int) nm.1 (gtAdGd GT) s e Hn (nxOf x GT e Hs)) $$ Ho
  isplitl [Hl]
  · iapply (lkInvNeutral nm.2 lk (gtAdGd GT) s e t v Hn Hr Hv Hw) $$ Hl
  · itrivial

/-- ACQUIRE-SUCCESS (the claim). -/
theorem feClaim (lk x : Int) (GT : GdexecT) (nm : spinN)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (c : Geid) (oz : Option Geid)
    (R : Geid → IProp GF) :
    lkClaim lk (gtAdGd GT).gdG c oz → lkTransportable (gtAdGd GT) R →
    (∀ v', ¬ gwritesByte (gtAdGd GT).gdG c x v') →
    ⊢ notheld nm.2 lk c.1 -∗ isLock nm.2 lk R -∗
      @flowEqDyn hlc GF _ (splG lk x GT nm) (gtAdGd GT) c
        (@Axpol.sPol (splPol GT) (gtAdGd GT) c) (∅ : Mea GF)
        iprop(locked nm.2 lk c.1 c ∗ R c) := by
  intro Hcl Htr Hs
  iintro Hnh #Hil
  iapply feBuild
  iintro %s %Hn %Hwc %Hwp %_ Ho Hl _
  imod (lkInvClaim nm.2 lk (gtAdGd GT) s c oz R Hcons Hwc Hwp Hn Hcl Htr) $$ [$Hl $Hnh $Hil]
    with H
  imodintro
  inext
  icases H with ⟨Hl, Hlk, HR⟩
  imodintro
  isplitl [Ho]
  · iapply (ownInvOther ({x} : GSet Int) nm.1 (gtAdGd GT) s c Hn (nxOf x GT c Hs)) $$ Ho
  isplitl [Hl]
  · iexact Hl
  isplitl [Hlk]
  · iexact Hlk
  · iexact HR

/-- THE RELEASE (the only zero-writing arm), with the GATE-DELIVERED read fact over its
handout. -/
theorem feRelease (lk x : Int) (GT : GdexecT) (nm : spinN)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (w : Geid) (i : Nat) (c a : Geid)
    (R : Geid → IProp GF) (flowIn : Mea GF) :
    zw lk (gtAdGd GT).gdG w → (∀ t v, ¬ greadsByte (gtAdGd GT).gdG w lk t v) →
    (∀ v', ¬ gwritesByte (gtAdGd GT).gdG w x v') →
    gobCat (gtAdGd GT) a w → lkTransportable (gtAdGd GT) R →
    ⊢ isLock nm.2 lk R -∗
      (([∗map] Rin ∈ flowIn, Rin) -∗ locked nm.2 lk i c ∗ R a) -∗
      @flowEqDyn hlc GF _ (splG lk x GT nm) (gtAdGd GT) w
        (@Axpol.sPol (splPol GT) (gtAdGd GT) w) flowIn
        iprop(notheld nm.2 lk i ∗
          ⌜∀ r, r ∈ spSpol GT (gtAdGd GT) w → lkread lk (gtAdGd GT).gdG r →
            WeakRvwmoGraph.gpo (gtAdGd GT).gdG c r → nolk lk (gtAdGd GT).gdG c r →
            ∀ t v, greadsByte (gtAdGd GT).gdG r lk t v → v ≠ b0⌝) := by
  intro Hzw Hnr Hs Hob Htr
  iintro #Hil Hfi
  iapply feBuild
  iintro %s %Hn %Hwc %Hwp %Hsub Ho Hl Hin
  ihave ⟨Hlk, HR⟩ := Hfi $$ Hin
  icases (lkInvGateNz nm.2 lk (gtAdGd GT) s i c) $$ [$Hl $Hlk] with ⟨Hl, Hlk, %Hnz⟩
  ihave HR := (Htr a w Hob) $$ HR
  ihave H := (lkInvRelease nm.2 lk (gtAdGd GT) s w i c R Hcons Hwc Hn Hzw Hnr)
    $$ [$Hl $Hlk $Hil $HR]
  imodintro
  inext
  imod H with ⟨Hl, Hnh, -⟩
  imodintro
  isplitl [Ho]
  · iapply (ownInvOther ({x} : GSet Int) nm.1 (gtAdGd GT) s w Hn (nxOf x GT w Hs)) $$ Ho
  isplitl [Hl]
  · iexact Hl
  isplitl [Hnh]
  · iexact Hnh
  · ipureintro
    intro r Hr
    exact Hnz r (Hsub r Hr)

/-- A plain read of the lock byte (the holder's `lw`, or anyone's). -/
theorem feLkread (lk x : Int) (GT : GdexecT) (nm : spinN)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (r : Geid) :
    gisW (gtAdGd GT).gdG r = false →
    ⊢ @flowEqDyn hlc GF _ (splG lk x GT nm) (gtAdGd GT) r
        (@Axpol.sPol (splPol GT) (gtAdGd GT) r) (∅ : Mea GF) iprop(True) := by
  intro Hnw
  have Hnwb : ∀ a v, ¬ gwritesByte (gtAdGd GT).gdG r a v := by
    intro a v Hw
    have h := WeakRvwmoGraph.gwritesByteGisW _ _ _ _ Hw
    rw [Hnw] at h
    cases h
  iapply feBuild
  iintro %s %Hn %Hwc %Hwp %_ Ho Hl _
  imodintro
  inext
  imodintro
  isplitl [Ho]
  · iapply (ownInvOther ({x} : GSet Int) nm.1 (gtAdGd GT) s r Hn
      (fun a v _ => Hnwb a v)) $$ Ho
  isplitl [Hl]
  · iapply (lkInvRead nm.2 lk (gtAdGd GT) s r Hcons Hwp Hn Hnw) $$ Hl
  · itrivial

/-- Any other non-write event not reading the lock byte (racy reads elsewhere): a frame. -/
theorem feOtherRead (lk x : Int) (GT : GdexecT) (nm : spinN) (r : Geid) :
    gisW (gtAdGd GT).gdG r = false → ¬ lkread lk (gtAdGd GT).gdG r →
    ⊢ @flowEqDyn hlc GF _ (splG lk x GT nm) (gtAdGd GT) r
        (@Axpol.sPol (splPol GT) (gtAdGd GT) r) (∅ : Mea GF) iprop(True) := by
  intro Hnw Hnr
  have Hnwb : ∀ a v, ¬ gwritesByte (gtAdGd GT).gdG r a v := by
    intro a v Hw
    have h := WeakRvwmoGraph.gwritesByteGisW _ _ _ _ Hw
    rw [Hnw] at h
    cases h
  iapply feBuild
  iintro %s %Hn %Hwc %Hwp %_ Ho Hl _
  imodintro
  inext
  imodintro
  isplitl [Ho]
  · iapply (ownInvOther ({x} : GSet Int) nm.1 (gtAdGd GT) s r Hn
      (fun a v _ => Hnwb a v)) $$ Ho
  isplitl [Hl]
  · iapply (lkInvOther nm.2 lk (gtAdGd GT) s r Hn (fun v => Hnwb lk v) Hnr) $$ Hl
  · itrivial

/-- THE OWNED WRITE of `x` under the lock (`R` = `Rx`). -/
theorem feXwrite (lk x : Int) (Hxl : x ≠ lk) (GT : GdexecT) (nm : spinN) (w a : Geid)
    (Q : IProp GF) (flowIn : Mea GF) :
    gmoLt (gtAdGd GT).gdG a w → gwritesByte (gtAdGd GT).gdG w x b1 →
    (∀ a' v', gwritesByte (gtAdGd GT).gdG w a' v' → a' = x) →
    ⊢ (([∗map] Rin ∈ flowIn, Rin) -∗ Q ∗ Rx nm.1 x (gtAdGd GT) a) -∗
      @flowEqDyn hlc GF _ (splG lk x GT nm) (gtAdGd GT) w
        (@Axpol.sPol (splPol GT) (gtAdGd GT) w) flowIn
        iprop(Q ∗ Rx nm.1 x (gtAdGd GT) w) := by
  intro Haw Hw Hs
  have Hisw := WeakRvwmoGraph.gwritesByteGisW _ _ _ _ Hw
  iintro Hfi
  iapply feBuild
  iintro %s %Hn %Hwc %Hwp %_ Ho Hl Hin
  ihave ⟨HQ, HR⟩ := Hfi $$ Hin
  imod (RxWrite nm.1 x (gtAdGd GT) s a w Hn Haw Hw Hs) $$ [$Ho $HR] with ⟨Ho, HR⟩
  imodintro
  inext
  imodintro
  isplitl [Ho]
  · iexact Ho
  isplitl [Hl]
  · iapply (lkInvOther nm.2 lk (gtAdGd GT) s w Hn (fun v Hv => Hxl (Hs _ _ Hv).symm)
      (fun ⟨_, Hnw⟩ => by rw [Hisw] at Hnw; cases Hnw)) $$ Hl
  isplitl [HQ]
  · iexact HQ
  · iexact HR

/-- THE OWNED READ of `x` under the lock. -/
theorem feXread (lk x : Int) (GT : GdexecT) (nm : spinN)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (r e : Geid) (t : Nat) (v : BitVec 8)
    (Q : IProp GF) (flowIn : Mea GF) :
    gisW (gtAdGd GT).gdG r = false → ¬ lkread lk (gtAdGd GT).gdG r →
    (∀ w v', gwritesByte (gtAdGd GT).gdG w x v' → w.1 = r.1 → False) →
    greadsByte (gtAdGd GT).gdG r x t v → gmoLt (gtAdGd GT).gdG e r →
    ⊢ (([∗map] Rin ∈ flowIn, Rin) -∗ Q ∗ Rx nm.1 x (gtAdGd GT) e) -∗
      @flowEqDyn hlc GF _ (splG lk x GT nm) (gtAdGd GT) r
        (@Axpol.sPol (splPol GT) (gtAdGd GT) r) flowIn
        iprop((Q ∗ Rx nm.1 x (gtAdGd GT) e) ∗ ⌜v = b1 ∨ (gtAdGd GT).gdG.gxImg x = some v⌝) := by
  intro Hnw Hnr Hnpo Hrd Her
  have Hnwb : ∀ a v', ¬ gwritesByte (gtAdGd GT).gdG r a v' := by
    intro a v' Hw
    have h := WeakRvwmoGraph.gwritesByteGisW _ _ _ _ Hw
    rw [Hnw] at h
    cases h
  iintro Hfi
  iapply feBuild
  iintro %s %Hn %Hwc %Hwp %_ #Ho Hl Hin
  ihave ⟨HQ, HR⟩ := Hfi $$ Hin
  ihave ⟨HR, %Hv⟩ := (RxRead nm.1 x (gtAdGd GT) s e r t v Hcons Hnpo Hrd Her Hwp) $$ [$Ho $HR]
  imodintro
  inext
  imodintro
  isplitl []
  · iapply (ownInvOther ({x} : GSet Int) nm.1 (gtAdGd GT) s r Hn
      (fun a v' _ => Hnwb a v')) $$ Ho
  isplitl [Hl]
  · iapply (lkInvOther nm.2 lk (gtAdGd GT) s r Hn (fun v' => Hnwb lk v') Hnr) $$ Hl
  · isplitl [HQ HR]
    · isplitl [HQ]
      · iexact HQ
      · iexact HR
    · ipureintro
      exact Hv

end rules

/-! # 4. GENERIC STEP FACTS for the exclusive RMW halves (hand nodes) -/

theorem wob1 (b : BitVec 8) : wordOfBytes 1 [b] = b := by
  have H := wordOfBytesByte 1 [b] 0 rfl (by omega)
  rw [nthByteBv8] at H
  exact H

section rmwSteps
variable (cpu : CPU)

/-- The READ inversion at a 1-byte RAM `memRead` node, ANY access kind (both `akLatest` arms). -/
theorem readInvAny (row : List Lbl) (ak : AK) (pa : PAddr) (Hdev : devAddr pa = false)
    (KK : Result (BitVec (8 * 1) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (k : Nat)
    (id : AidentT) (K : List (BitVec 8) → Athread) (v : List (BitVec 8)) :
    areadStep row ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq ak pa))) KK) rs, k⟩ id K →
    v.length = aidentN id →
    ∃ lb b, row[k]? = some lb ∧ aident lb = id ∧ v = [b] ∧
      K v = ⟨hp cpu (KK (.Ok (b, none))) rs, k + aidentAdvRd id⟩ := by
  rintro ⟨lb, Hlk, Hid, Hsome, Hvs⟩ Hlen
  obtain ⟨l, d, d', Hrd, Hrv, Hst, Hk⟩ := Hvs v Hlen
  rcases HKv : K v with ⟨p', k'⟩
  rw [HKv] at Hst Hk
  simp only at Hst Hk
  cases p' with
  | PDisk _ => exact Hst.elim
  | PHart cpu' m'' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, Hrs, Hib, Hn, -⟩ := Hst
    have hpa : devAddr (l3pRreq ak pa).pa = false := Hdev
    simp only [pstepNode, pnodeStep, hpa, Bool.false_eq_true, ↓reduceIte] at Hn
    rcases Hn with ⟨-, w, tvs, -, -, rfl, -⟩ |
      ⟨-, ⟨-, w, tvs, hlen, hby, rfl, rfl, rfl, rfl, -, rfl, -⟩ |
        ⟨-, w, tvs, hlen, hby, rfl, rfl, rfl, rfl, -, rfl, -⟩⟩
    · rw [← Hrd] at Hsome
      simp [wlRd] at Hsome
    · simp only [Option.getD_none] at Hrs Hib
      subst Hrs Hib Hk
      rcases tvs with _ | ⟨⟨t0, c⟩, _ | _⟩ <;> simp at hlen
      have hc : c = w := by
        have h0 := hby 0 (by omega)
        simp only [List.map_cons, List.map_nil, List.getElem?_cons_zero, Option.some.injEq] at h0
        rw [h0, nthByteBv8]
      subst hc
      exact ⟨lb, c, Hlk, Hid, Hrv.symm, rfl⟩
    · simp only [Option.getD_none] at Hrs Hib
      subst Hrs Hib Hk
      rcases tvs with _ | ⟨⟨t0, c⟩, _ | _⟩ <;> simp at hlen
      have hc : c = w := by
        have h0 := hby 0 (by omega)
        simp only [List.map_cons, List.map_nil, List.getElem?_cons_zero, Option.some.injEq] at h0
        rw [h0, nthByteBv8]
      subst hc
      exact ⟨lb, c, Hlk, Hid, Hrv.symm, rfl⟩

theorem rmwAread (row : List Lbl) (k : Nat) (pa : PAddr) (Hdev : devAddr pa = false) (t : Nat)
    (old : BitVec 8) (cls : WmClass)
    (KK : Result (BitVec (8 * 1) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile) :
    row[k]? = some (.LRmw true false (paZ pa) [t] [old] [b1] cls) →
    areadStep row ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq l3pAkXaq pa))) KK) rs, k⟩
      (.IRmw true false (paZ pa) 1)
      (fun vs => ⟨hp cpu (KK (.Ok (wordOfBytes 1 vs, none))) rs, k⟩) := by
  intro hrow
  refine ⟨_, hrow, rfl, rfl, ?_⟩
  intro vs hvs
  refine ⟨rdLabel false true (classify l3pAkXaq).akSync (paZ pa) (tagVals vs)
      (rdAsrc true ibNone), OpaxWit.wtD0, OpaxWit.wtD0, ?_, ?_,
    l3pReadStep cpu l3pAkXaq pa Hdev rfl _ rs ibNone OpaxWit.wtD0 vs hvs, ?_⟩
  · simp only [rdLabel, wlRd, aidentRd, tagValsLength, Bool.false_eq_true, ↓reduceIte]
    rw [hvs]; rfl
  · rw [rdLabelRvals _ _ _ _ _ _ rfl, tagValsSnd]
  · rfl

theorem rmwAstepWrite (row : List Lbl) (k : Nat) (pa : PAddr) (Hdev : devAddr pa = false)
    (t : Nat) (old : BitVec 8) (cls : WmClass) (m' : SailM Unit) (rs : RegFile) :
    row[k]? = some (.LRmw true false (paZ pa) [t] [old] [b1] cls) →
    AxOpsem.astepProg row
      ⟨hp cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkXpl pa b1))) (fun _ => m')) rs, k⟩
      (.LExStore false (paZ pa) (WeakInterpProj.wbytes 1 b1) [] [])
      ⟨hp cpu m' rs, k + 1⟩ := by
  intro hrow
  refine .AStepWrite _ k OpaxWit.wtD0 _ _ _ OpaxWit.wtD0 hrow rfl rfl ?_ ?_
  · simp only [wlWdata, lblData, l3pWbytes1]
  · exact l3pWriteExclStep cpu pa Hdev b1 (fun _ => m') rs ibNone OpaxWit.wtD0

theorem rmwWriteInv (row : List Lbl) (pa : PAddr) (Hdev : devAddr pa = false) (val : BitVec 8)
    (m' : SailM Unit) (rs : RegFile) (k : Nat) (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg row
      ⟨hp cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkXpl pa val))) (fun _ => m')) rs, k⟩
      l s' →
    (wlWdata l = some (WeakInterpProj.wbytes 1 val) ∧ s' = ⟨hp cpu m' rs, k + 1⟩) ∨
    (l = .LSilent ∧
      s' = ⟨hp cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkXpl pa val))) (fun _ => m')) rs,
        k⟩) := by
  intro Hst
  generalize hs : (Athread.AThread
    (hp cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkXpl pa val))) (fun _ => m')) rs) k) = s
    at Hst
  cases Hst with
  | AStepAdmin p k0 d l0 p' d' Hadm Hps =>
    cases hs
    rcases l3pWriteExclDet cpu pa Hdev val _ rs ibNone d _ _ _ Hps with
      ⟨rfl, -, -⟩ | ⟨rfl, rfl, -⟩
    · simp [AxOpsem.lbAdminAx] at Hadm
    · exact .inr ⟨rfl, rfl⟩
  | AStepWrite p k0 d l0 lb p' d' Hlk Hwr Heqwr Hwdat Hps =>
    cases hs
    rcases l3pWriteExclDet cpu pa Hdev val _ rs ibNone d _ _ _ Hps with
      ⟨rfl, rfl, -⟩ | ⟨rfl, -, -⟩
    · exact .inl ⟨by simp [wlWdata], rfl⟩
    · simp [wlWr] at Hwr
  | AStepFence p k0 d l0 lb p' d' _ Hfe _ Hps =>
    cases hs
    rcases l3pWriteExclDet cpu pa Hdev val _ rs ibNone d _ _ _ Hps with
      ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ <;> simp [wlFence] at Hfe

theorem noReadAtXwrite (row : List Lbl) (pa : PAddr) (Hdev : devAddr pa = false) (val : BitVec 8)
    (m' : SailM Unit) (rs : RegFile) (k : Nat) (id : AidentT) (K : List (BitVec 8) → Athread) :
    ¬ areadStep row
      ⟨hp cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkXpl pa val))) (fun _ => m')) rs, k⟩
      id K := by
  rintro ⟨lb, -, -, Hsome, Hvs⟩
  obtain ⟨l, d, d', Hrd, -, Hst, -⟩ := Hvs (List.replicate (aidentN id) b0) List.length_replicate
  rcases l3pWriteExclDet cpu pa Hdev val _ rs ibNone d _ _ _ Hst with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
  · rw [← Hrd] at Hsome
    simp [wlRd] at Hsome

theorem fenceAstep (row : List Lbl) (k : Nat) (m' : SailM Unit) (rs : RegFile) :
    row[k]? = some (.LFence true true false true) →
    AxOpsem.astepProg row
      ⟨hp cpu (.impure (.ok (.barrier .Barrier_RISCV_rw_w)) (fun _ => m')) rs, k⟩
      (.LFence true true false true) ⟨hp cpu m' rs, k + 1⟩ := by
  intro hrow
  exact .AStepFence _ k OpaxWit.wtD0 _ _ _ OpaxWit.wtD0 hrow rfl rfl
    (l3pFenceStep cpu (fun _ => m') rs ibNone OpaxWit.wtD0)

end rmwSteps

section runs2
variable (cpu : CPU)

theorem runRmwRead (GD : Gdexec) (i : Agent) (k : Nat) (pa : PAddr) (Hdev : devAddr pa = false)
    (t : Nat) (old : BitVec 8) (cls : WmClass)
    (KK : Result (BitVec (8 * 1) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile) :
    (AxOpsem.grow GD i)[k]? = some (.LRmw true false (paZ pa) [t] [old] [b1] cls) →
    astepAnyNfGv GD i
      ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq l3pAkXaq pa))) KK) rs, k⟩
      ⟨hp cpu (KK (.Ok (old, none))) rs, k⟩ := by
  intro Hl
  have Hrd := rmwAread cpu (AxOpsem.grow GD i) k pa Hdev t old cls KK rs Hl
  have Hgv : graphValue GD (i, k) = some [old] := by
    unfold graphValue
    rw [gxLblGrow, Hl]
    rfl
  have H := astepAnyNfGv.ANFGVRead _ _ _ [old] Hrd Hgv rfl
  simp only [wob1] at H
  exact H

theorem runRmwWrite (GD : Gdexec) (i : Agent) (k : Nat) (pa : PAddr) (Hdev : devAddr pa = false)
    (t : Nat) (old : BitVec 8) (cls : WmClass) (m' : SailM Unit) (rs : RegFile) :
    (AxOpsem.grow GD i)[k]? = some (.LRmw true false (paZ pa) [t] [old] [b1] cls) →
    astepAnyNfGv GD i
      ⟨hp cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkXpl pa b1))) (fun _ => m')) rs, k⟩
      ⟨hp cpu m' rs, k + 1⟩ := by
  intro Hl
  exact .ANFGVProg _ _ ⟨_, rmwAstepWrite cpu _ k pa Hdev t old cls m' rs Hl, trivial⟩

theorem runFence (GD : Gdexec) (i : Agent) (k : Nat) (m' : SailM Unit) (rs : RegFile) :
    (AxOpsem.grow GD i)[k]? = some (.LFence true true false true) →
    astepAnyNfGv GD i
      ⟨hp cpu (.impure (.ok (.barrier .Barrier_RISCV_rw_w)) (fun _ => m')) rs, k⟩
      ⟨hp cpu m' rs, k + 1⟩ := by
  intro Hl
  exact .ANFGVProg _ _ ⟨_, fenceAstep cpu _ k m' rs Hl, trivial⟩

end runs2

/-! # 5. WPd SHELLS for the exclusive RMW halves (at any `axGA2` instance) -/

section shells2
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [pol : Axpol]

theorem shSkip2 (GD : Gdexec) (N obSt0 : Type) (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF)
    (nm : N) (i : Agent) (k' : Nat) (Ψ : IProp GF) :
    ⊢ ▷ Ψ -∗ @wpSkipStep GF (shG GD N obSt0 obi nm) GD i k' Ψ :=
  shSkip GD N obSt0 obi nm i k' Ψ

/-- No program step at a RAM read node (Stage C: an i-fetch access kind is excluded). -/
theorem rdAstepVacuous (row : List Lbl) (cpu : CPU) (ak : AK) (pa : PAddr)
    (Hdev : devAddr pa = false) (Hfe : (classify ak).akIfetch = false)
    (KK : Result (BitVec (8 * 1) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (k : Nat)
    (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg row ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq ak pa))) KK) rs, k⟩ l s' →
    False :=
  readNodeNoAstep cpu row ak pa Hdev Hfe KK rs k l s'

/-- The RMW's READ half: pinned to the row's read value, no flow equation (the write half posts
the event's single annotation). -/
theorem shRmwRead (GD : Gdexec) (N obSt0 : Type)
    (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N) (cpu : CPU) (i : Agent)
    (Φ : Athread → IProp GF) (pa : PAddr) (Hdev : devAddr pa = false)
    (KK : Result (BitVec (8 * 1) × Option Bool) Arch.abort → SailM Unit) (k : Nat) (t : Nat)
    (old : BitVec 8) (cls : WmClass)
    (Hne : k ≠ (AxOpsem.grow GD i).length)
    (Hrow : (AxOpsem.grow GD i)[k]? = some (.LRmw true false (paZ pa) [t] [old] [b1] cls))
    (P : IProp GF)
    (Hcont : ∀ rs : RegFile, ⊢ P -∗ tierAWpd (hlc := hlc) GD N obSt0 obi nm
      ⟨hp cpu (KK (.Ok (old, none))) rs, k⟩ .MaybeStuck i Φ) :
    ⊢ P -∗ ∀ rs : RegFile, tierAWpd (hlc := hlc) GD N obSt0 obi nm
      ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq l3pAkXaq pa))) KK) rs, k⟩ .MaybeStuck i Φ := by
  have H : ⊢ ∀ rs : RegFile, P -∗ tierAWpd (hlc := hlc) GD N obSt0 obi nm
      ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq l3pAkXaq pa))) KK) rs, k⟩ .MaybeStuck i Φ := by
    iloeb as IH
    iintro %rs HP
    iapply (AxSpinWit.twUnfold (hlc := hlc) GD N obSt0 obi nm _ i Φ).2
    isplit
    · simp only [progressObl]
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, Hloc⟩
    ihave Hok := AxSpinWit.gconstEq GD N obSt0 obi nm GD' $$ Hg
    icases Hok with %HGD
    subst GD'
    isplit
    · iintro %id %K %Hst
      have Hst' := Hst
      obtain ⟨lb, Hlk, Hidlb, _, -⟩ := Hst
      have Hlk' : (AxOpsem.grow GD i)[k]? = some lb := Hlk
      rw [Hrow] at Hlk'
      cases Hlk'
      have Hadv0 : aidentAdvRd id = 0 := by rw [← Hidlb]; rfl
      rw [if_neg (by rw [Hadv0]; decide)]
      iintro %v %Hgv %Hlen
      obtain ⟨lb', b, -, -, rfl, HK⟩ :=
        readInvAny cpu _ l3pAkXaq pa Hdev KK rs k id K v Hst' Hlen
      have Hb : b = old := by
        have Hgv' : graphValue GD (i, k) = some [b] := Hgv
        unfold graphValue at Hgv'
        rw [gxLblGrow, Hrow] at Hgv'
        simp only [Option.bind_some, lblValue, Option.some.injEq, List.cons.injEq,
          and_true] at Hgv'
        exact Hgv'.symm
      rw [HK, Hadv0, Nat.add_zero, Hb]
      iapply shSkip
      inext
      iapply (Hcont rs) $$ HP
    isplit
    · iintro %l %s' %Hst %_
      exact (rdAstepVacuous _ cpu l3pAkXaq pa Hdev rfl KK rs k l s' Hst).elim
    isplit
    · iintro %s' %Hw
      obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu _ rs k s' Hw
      iapply shSkip
      inext
      iapply IH $$ %rs' HP
    · iintro %Heq
      exact (Hne Heq).elim
  iintro HP %rs
  iapply H $$ %rs HP

/-- The RMW's WRITE half (with the store-conditional retry self-loop). -/
theorem shRmwWrite (GD : Gdexec) (N obSt0 : Type)
    (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N) (cpu : CPU) (i : Agent)
    (Φ : Athread → IProp GF) (pa : PAddr) (Hdev : devAddr pa = false) (m' : SailM Unit)
    (k : Nat) (Hne : k ≠ (AxOpsem.grow GD i).length) (P : IProp GF)
    (Hb : ∀ rs : RegFile, ⊢ P -∗
      @wpEvStep hlc GF _ (shG GD N obSt0 obi nm) pol Unit GD i k (fun _ => True)
        (fun _ => graphData GD (i, k) = some (WeakInterpProj.wbytes 1 b1)) (fun _ => k + 1)
        (fun _ => tierAWpd (hlc := hlc) GD N obSt0 obi nm ⟨hp cpu m' rs, k + 1⟩ .MaybeStuck i Φ)) :
    ⊢ P -∗ ∀ rs : RegFile, tierAWpd (hlc := hlc) GD N obSt0 obi nm
      ⟨hp cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkXpl pa b1))) (fun _ => m')) rs, k⟩
      .MaybeStuck i Φ := by
  have H : ⊢ ∀ rs : RegFile, P -∗ tierAWpd (hlc := hlc) GD N obSt0 obi nm
      ⟨hp cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkXpl pa b1))) (fun _ => m')) rs, k⟩
      .MaybeStuck i Φ := by
    iloeb as IH
    iintro %rs HP
    iapply (AxSpinWit.twUnfold (hlc := hlc) GD N obSt0 obi nm _ i Φ).2
    isplit
    · simp only [progressObl]
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, Hloc⟩
    ihave Hok := AxSpinWit.gconstEq GD N obSt0 obi nm GD' $$ Hg
    icases Hok with %HGD
    subst GD'
    isplit
    · iintro %id %K %Hst
      exact (noReadAtXwrite cpu _ pa Hdev b1 m' rs k id K Hst).elim
    isplit
    · iintro %l %s' %Hst %_
      rcases rmwWriteInv cpu _ pa Hdev b1 m' rs k l s' Hst with ⟨Hwd, rfl⟩ | ⟨rfl, rfl⟩
      · rw [Hwd]
        dsimp only
        iapply (Hb rs) $$ HP
      · dsimp only [wlWdata]
        iapply shSkip
        inext
        iapply IH $$ %rs HP
    isplit
    · iintro %s' %Hw
      obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu _ rs k s' Hw
      iapply shSkip
      inext
      iapply IH $$ %rs' HP
    · iintro %Heq
      exact (Hne Heq).elim
  iintro HP %rs
  iapply H $$ %rs HP

end shells2

end Weak
