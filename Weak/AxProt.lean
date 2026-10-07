/-
Weak: **THE PROTOCOL STATE INTERPRETATION** (AxSL tier): the L1↔L2 glue between `Weak.AxWp`'s
`obSt`/`obStInterp` hook and `Weak.AxToken`'s owned points-to.

Rocq: `iris/AxProt.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`AxirisG`'s `obSt`/`obStInterp` fields are the base WP's protocol-state hook; this file
instantiates them with the L2 owned-points-to ghost.  `protInv` (the design's universal protocol,
specialised to the Own/read-only classes; Lock/Flag are out of scope, left as hooks) is an
`obStInterp`; the pure phase-2 bookkeeping lemmas (`protInvPrefixCov`/`protInvWriteStep`/
`protInvReadStep`) produce exactly the coverage/deposit shapes `AxGhost.ownedReadGhost`/
`AxToken.ownedReadRule`/`ownedWriteRule` consume; the two flow equations
(`flowEqOwnedRead`/`flowEqOwnedWrite`) discharge `AxWp.flowEqDyn` for an owned event.

Granularity: every ghost fact is PER BYTE.  `ΦOwn` is byte-general (one `∀` over every `(a, v)`
a write event's label touches); the phase-2 lemmas are stated for a write that is ITSELF
single-byte (one hypothesis pins the footprint to one address); the multi-byte lift is the
instruction-rule composition's job.

The `AxirisG` instantiation is BY HYPOTHESIS: the flow equations are stated for an ARBITRARY
ambient `AxirisG GF` together with the bridging hypothesis `Hob_eq : ∀ GD σ s, obStInterp GD σ s
⊣⊢ protInv γ GD s`; §5 discharges it for `AxWp`'s own `skelAxirisG γg (ΦpOwn γ)`.
The flow equation's `R` is the BARE pure fact (the token handed in through `flowIn` is spent by
`ownedReadRule`; a hart's own continued ownership travels on ordinary WP resources).
`flowEqOwnedWrite` takes `graphData GD w = some data` as an explicit hypothesis (Rocq: STALE since
the store-byte fix, `AStepWrite` now checks the data; not dropped).

§1 `ΦOwn`/`ΦRo`/`ΦpOwn`/`protInv`; §2 coverage (`protInvPrefixCov(Mem)(Byte)`); §3 the phase-2
steps; §4 the flow equations; §5 non-vacuity on `AxGraphWit`'s `fwd` (write `(0,0)` then the
forwarded read `(0,1)`): the read's flow equation discharges the real forwarded value `b1`.

**Fetches.** Nothing here depends on instruction fetches: the file speaks of `gwritesByte`/
`greadsByte`/`gisW`/`gmoLt`/`gpo` over graph labels (`Lbl` has no fetch constructor) and of
`flowEqDyn` at a given event.

## Deviations from Rocq

1. NAMES: camelCase (map below).  Duplicated Rocq name, file-qualified: `AxProt.gwritesByteGisW`
   (proved by `WeakRvwmoGraph.gwritesByteGisW`).  Lean-only helpers, file-qualified:
   `AxProt.ΦpOwnW`, `AxProt.ΦpOwnNotW` (the two branches of `ΦpOwn`, as equations).
2. VOCABULARY (as `AxToken` deviation 2): `last l` ↦ `l.getLast?`; `H.*1` ↦ `H.map Prod.fst`;
   `dom S` ↦ `(FiniteMap.dom_set S : GSet Geid)`; `gmap geid Qp` ↦ `GMapF Geid Qp`;
   `gd_g GD` ↦ `GD.gdG`; `gx_gmo` ↦ `.gxGmo`; `gpo` ↦ `WeakRvwmoGraph.gpo`; `list_to_set l` ↦
   `(LawfulSet.ofList l : GSet Geid)`; `{[e]} ∪ s` ↦ `({e} : GSet Geid) ∪ s`; `mea Σ` ↦
   `Mea GF`; `WeakLitmus.b1` ↦ `b1`; `bv 8` ↦ `BitVec 8`; `Z` ↦ `Int`.
3. `ΦOwn`'s pure implication `⌜φ⌝ → P` is `∀ _ : φ, P` (equivalent, `BI.pure_imp_forall`):
   iris-lean has no `BIPlainly` instance for `IProp`, so `impl_persistent` does not apply, while
   `forall_persistent` does.
4. STATEMENT SHAPES (as `AxToken` deviation 4): `P -∗ Q` ↦ `P ⊢ Q`, `P -∗ Q ==∗ R` ↦
   `P ∗ Q ⊢ |==> R`; pure premises stay `→`.
5. CONTEXTS: `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc` (as `AxWp` deviation 6);
   Rocq's section context `axpol` is unused by every statement and dropped; the section variables
   `γ`/`Hob_eq` are explicit leading arguments of the §4 lemmas (as Rocq after the section);
   `axirisG Σ` is the named instance argument `axG` (so §5 passes `(axG := skelAxirisG …)`, Rocq's
   `Local Instance nonvacuity_axirisG`, which has no counterpart: the statements name the
   instance, as `AxWp` deviation 8).
6. PROOFS: `vm_compute`/`vmr` are `decide +kernel` on the boolean twins (`gpoBSpec`/`gwbBSpec`/
   `grbBSpec`/`gmoLtBSpec`) and on `gwrBytes`/`gmoPrefix`/`gisW`.  `protInvPrefixCov` is derived
   from `protInvPrefixCovByte` (Rocq proves both directly).

**Rocq → Lean name map.**  `gwrites_byte_gis_w` `AxProt.gwritesByteGisW`, `Φ_own` `ΦOwn`,
`Φ_own_persistent` `ΦOwn_persistent`, `Φ_ro` `ΦRo`, `Φ_ro_persistent` `ΦRo_persistent`, `Φp_own`
`ΦpOwn`, `Φp_own_persistent` `ΦpOwn_persistent`, `prot_inv` `protInv`, `prot_inv_persistent`
`protInv_persistent`, `prot_inv_insert` `protInvInsert`, `prot_inv_prefix_cov` `protInvPrefixCov`,
`prot_inv_prefix_cov_mem` `protInvPrefixCovMem`, `prot_inv_prefix_cov_byte`
`protInvPrefixCovByte`, `prot_inv_prefix_cov_mem_byte` `protInvPrefixCovMemByte`,
`prot_inv_write_step` `protInvWriteStep`, `prot_inv_write_step_auth` `protInvWriteStepAuth`,
`prot_inv_read_step` `protInvReadStep`, `flow_eq_owned_read` `flowEqOwnedRead`,
`flow_eq_owned_read_byte` `flowEqOwnedReadByte`, `flow_eq_owned_write` `flowEqOwnedWrite`,
`nonvacuity_axirisG` (none, see deviation 5), `nonvacuity_hob_eq` `nonvacuityHobEq`,
`fwd_gwrites_byte_0` `fwdGwritesByte0`, `fwd_gwrites_byte_single` `fwdGwritesByteSingle`,
`fwd_greads_byte_0` `fwdGreadsByte0`, `prot_nonvacuity` `protNonvacuity`.

**Not ported:** the §6 `Print Assumptions` audit (the lint's axiom check covers it).
-/
import Weak.AxToken
import Weak.AxWp2
import Weak.AxBridge
import Weak.WeakRvwmoLock
import Weak.WeakRvwmoDec
import Weak.WeakRvwmoAcyc

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. THE UNIVERSAL PROTOCOL, specialised to Own/read-only -/

/-- A write event's byte footprint makes it a write event of `gisW`. -/
theorem AxProt.gwritesByteGisW (G : Gexec) (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte G e a v → gisW G e = true :=
  WeakRvwmoGraph.gwritesByteGisW G e a v

section protDefs

variable {GF : BundledGFunctors} [AxlogG GF Hent]

/-- THE OWN-CLASS PROTOCOL CONTENT at a write event `e`: for every byte `e` touches, a snapshot of
that byte's history whose LAST entry is `e`'s own write. -/
def ΦOwn (γ : GName) (GD : Gdexec) (e : Geid) : IProp GF :=
  iprop(∀ (a : Int) (v : BitVec 8), ∀ _ : gwritesByte GD.gdG e a v,
    ∃ H : List Hent, histSnap γ a H ∗ ⌜H.getLast? = some (e, v)⌝)

instance ΦOwn_persistent (γ : GName) (GD : Gdexec) (e : Geid) :
    Persistent (ΦOwn (GF := GF) γ GD e) := by
  unfold ΦOwn; infer_instance

/-- THE READ-ONLY HOOK: byte `a` is never written anywhere in the graph (a pure fact; never
consulted by `protInv`). -/
def ΦRo (GD : Gdexec) (a : Int) : IProp GF :=
  iprop(⌜∀ w v, ¬ gwritesByte GD.gdG w a v⌝)

instance ΦRo_persistent (GD : Gdexec) (a : Int) : Persistent (ΦRo (GF := GF) GD a) := by
  unfold ΦRo; infer_instance

/-- THE PER-EVENT PROTOCOL CONTENT: Own-class at a write, nothing elsewhere. -/
def ΦpOwn (γ : GName) (GD : Gdexec) (e : Geid) : IProp GF :=
  if gisW GD.gdG e then ΦOwn γ GD e else iprop(emp)

instance ΦpOwn_persistent (γ : GName) (GD : Gdexec) (e : Geid) :
    Persistent (ΦpOwn (GF := GF) γ GD e) := by
  unfold ΦpOwn
  cases gisW GD.gdG e <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

/-- Lean-only: the write branch of `ΦpOwn`. -/
theorem AxProt.ΦpOwnW (γ : GName) (GD : Gdexec) (e : Geid) (h : gisW GD.gdG e = true) :
    ΦpOwn (GF := GF) γ GD e = ΦOwn γ GD e := by
  unfold ΦpOwn; simp only [h, ↓reduceIte]

/-- Lean-only: the non-write branch of `ΦpOwn`. -/
theorem AxProt.ΦpOwnNotW (γ : GName) (GD : Gdexec) (e : Geid) (h : gisW GD.gdG e = false) :
    ΦpOwn (GF := GF) γ GD e = iprop(emp) := by
  unfold ΦpOwn; simp only [h, Bool.false_eq_true, ↓reduceIte]

/-- THE PROTOCOL STATE over the validated event set `s`. -/
def protInv (γ : GName) (GD : Gdexec) (s : GSet Geid) : IProp GF :=
  iprop([∗set] e ∈ s, ΦpOwn γ GD e)

instance protInv_persistent (γ : GName) (GD : Gdexec) (s : GSet Geid) :
    Persistent (protInv (GF := GF) γ GD s) := by
  unfold protInv; infer_instance

theorem protInvInsert (γ : GName) (GD : Gdexec) (e : Geid) (s : GSet Geid) :
    e ∉ s → protInv (GF := GF) γ GD (({e} : GSet Geid) ∪ s) ⊣⊢ ΦpOwn γ GD e ∗ protInv γ GD s := by
  intro hnin
  unfold protInv
  have hdisj : ({e} : GSet Geid) ## s := by
    rw [elemOfDisjoint]
    intro x hx hx'
    rw [elemOfSingleton.1 hx] at hx'
    exact hnin hx'
  refine (BigSepS.bigSepS_union hdisj).trans ?_
  exact BI.sep_congr BigSepS.bigSepS_singleton .rfl

/-! # 2. THE COVERAGE LEMMA -/

/-- BYTE-RESTRICTED coverage: the covering hypothesis over byte-`a` writes gmo-before `r`. -/
theorem protInvPrefixCovByte (γ : GName) (GD : Gdexec) (s : GSet Geid) (r : Geid) (a : Int) :
    (∀ w v, gwritesByte GD.gdG w a v → gmoLt GD.gdG w r → w ∈ s) →
    protInv (GF := GF) γ GD s ⊢
      ∀ w v, ⌜gwritesByte GD.gdG w a v⌝ -∗ ⌜gmoLt GD.gdG w r⌝ -∗
        ∃ Hw : List Hent, histSnap γ a Hw ∗ ⌜Hw.getLast? = some (w, v)⌝ := by
  intro hcov
  iintro #Hinv %w %v %hwb %hmo
  have h1 : protInv (GF := GF) γ GD s ⊢ ΦpOwn γ GD w :=
    BigSepS.bigSepS_elem_of (Φ := ΦpOwn γ GD) (hcov w v hwb hmo)
  rw [AxProt.ΦpOwnW γ GD w (AxProt.gwritesByteGisW _ _ _ _ hwb)] at h1
  unfold ΦOwn at h1
  ihave Hw := h1 $$ Hinv
  ihave Hw2 := Hw $$ %a %v %hwb
  iexact Hw2

/-- Coverage in the "last"-form, from `gmoPrefix r ⊆ s`. -/
theorem protInvPrefixCov (γ : GName) (GD : Gdexec) (s : GSet Geid) (r : Geid) (a : Int) :
    gwf GD.gdG → r ∈ GD.gdG.gxGmo →
    (LawfulSet.ofList (gmoPrefix GD.gdG r) : GSet Geid) ⊆ s →
    protInv (GF := GF) γ GD s ⊢
      ∀ w v, ⌜gwritesByte GD.gdG w a v⌝ -∗ ⌜gmoLt GD.gdG w r⌝ -∗
        ∃ Hw : List Hent, histSnap γ a Hw ∗ ⌜Hw.getLast? = some (w, v)⌝ := by
  intro hwf hrgmo hsub
  exact protInvPrefixCovByte γ GD s r a fun w _ _ hmo =>
    hsub w (elemOfListToSet.2 ((gmoPrefixSpec GD.gdG r w hwf hrgmo).2 hmo))

/-- The membership form `AxToken.ownedReadRule` takes as its coverage wand. -/
theorem protInvPrefixCovMem (γ : GName) (GD : Gdexec) (s : GSet Geid) (r : Geid) (a : Int) :
    gwf GD.gdG → r ∈ GD.gdG.gxGmo →
    (LawfulSet.ofList (gmoPrefix GD.gdG r) : GSet Geid) ⊆ s →
    protInv (GF := GF) γ GD s ⊢
      ∀ w v, ⌜gwritesByte GD.gdG w a v⌝ -∗ ⌜gmoLt GD.gdG w r⌝ -∗
        ∃ H' : List Hent, ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap γ a H' := by
  intro hwf hrgmo hsub
  iintro Hinv %w %v %hwb %hmo
  ihave Hc := protInvPrefixCov γ GD s r a hwf hrgmo hsub $$ Hinv
  icases Hc $$ %w %v %hwb %hmo with ⟨%Hw, Hs, %hl⟩
  iexists Hw
  isplitl []
  · ipureintro
    exact histSnapLastIn Hw w v hl
  · iexact Hs

/-- ... and the byte-restricted membership form. -/
theorem protInvPrefixCovMemByte (γ : GName) (GD : Gdexec) (s : GSet Geid) (r : Geid) (a : Int) :
    (∀ w v, gwritesByte GD.gdG w a v → gmoLt GD.gdG w r → w ∈ s) →
    protInv (GF := GF) γ GD s ⊢
      ∀ w v, ⌜gwritesByte GD.gdG w a v⌝ -∗ ⌜gmoLt GD.gdG w r⌝ -∗
        ∃ H' : List Hent, ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap γ a H' := by
  intro hcov
  iintro Hinv %w %v %hwb %hmo
  ihave Hc := protInvPrefixCovByte γ GD s r a hcov $$ Hinv
  icases Hc $$ %w %v %hwb %hmo with ⟨%Hw, Hs, %hl⟩
  iexists Hw
  isplitl []
  · ipureintro
    exact histSnapLastIn Hw w v hl
  · iexact Hs

/-! # 3. THE PHASE-2 STEPS -/

/-- THE WRITE STEP: a single-byte write `w` with the FULL fraction deposits its snapshot into
`protInv` and re-ties the token at `w`. -/
theorem protInvWriteStep (γ : GName) (GD : Gdexec) (s : GSet Geid) (w : Geid) (a : Int)
    (v : BitVec 8) (H : List Hent) :
    w ∉ s →
    gwritesByte GD.gdG w a v →
    (∀ a' v', gwritesByte GD.gdG w a' v' → a' = a) →
    protInv (GF := GF) γ GD s ∗ histAuth γ a 1 H ⊢
      |==> (protInv γ GD (({w} : GSet Geid) ∪ s) ∗
        tokTie GD γ a (H ++ [(w, v)]) {[w := (1 : Qp)]}) := by
  intro hnin hwb hsingle
  have hdep : histSnap (GF := GF) γ a (H ++ [(w, v)]) ⊢ ΦpOwn γ GD w := by
    rw [AxProt.ΦpOwnW γ GD w (AxProt.gwritesByteGisW _ _ _ _ hwb)]
    unfold ΦOwn
    iintro #Hs %a' %v' %hwb'
    obtain rfl := hsingle a' v' hwb'
    obtain rfl := gwritesByteDet _ _ _ _ _ hwb' hwb
    iexists H ++ [(w, v')]
    isplitl []
    · iexact Hs
    · ipureintro
      simp
  iintro ⟨#Hinv, Hauth⟩
  imod histAppend γ a H (w, v) $$ Hauth with Hauth
  ihave #Hsnap := histSnapGet γ a 1 (H ++ [(w, v)]) $$ Hauth
  imodintro
  isplitr [Hauth]
  · iapply (protInvInsert γ GD w s hnin).2
    isplitl []
    · iapply hdep
      iexact Hsnap
    · iexact Hinv
  · unfold tokTie
    isplitl [Hauth]
    · iapply (tokSingleton γ a (H ++ [(w, v)]) w 1).2
      iexact Hauth
    · ipureintro
      intro e he
      rw [domSingleton, elemOfSingleton] at he
      subst he
      exact tieWrite GD.gdG H e v

/-- The bare-`histAuth` form (no re-tie). -/
theorem protInvWriteStepAuth (γ : GName) (GD : Gdexec) (s : GSet Geid) (w : Geid) (a : Int)
    (v : BitVec 8) (H : List Hent) :
    w ∉ s →
    gwritesByte GD.gdG w a v →
    (∀ a' v', gwritesByte GD.gdG w a' v' → a' = a) →
    protInv (GF := GF) γ GD s ∗ histAuth γ a 1 H ⊢
      |==> (protInv γ GD (({w} : GSet Geid) ∪ s) ∗ histAuth γ a 1 (H ++ [(w, v)])) := by
  intro hnin hwb hsingle
  iintro HH
  imod protInvWriteStep γ GD s w a v H hnin hwb hsingle $$ HH with ⟨Hinv, Htie⟩
  imodintro
  unfold tokTie
  icases Htie with ⟨Ht, -⟩
  isplitl [Hinv]
  · iexact Hinv
  · iapply (tokSingleton γ a (H ++ [(w, v)]) w 1).1
    iexact Ht

/-- THE READ STEP: a read deposits nothing. -/
theorem protInvReadStep (γ : GName) (GD : Gdexec) (s : GSet Geid) (r : Geid) :
    r ∉ s → gisW GD.gdG r = false →
    protInv (GF := GF) γ GD s ⊢ protInv γ GD (({r} : GSet Geid) ∪ s) := by
  intro hnin hr
  refine BI.emp_sep.2.trans ((BI.sep_mono_left ?_).trans (protInvInsert γ GD r s hnin).2)
  rw [AxProt.ΦpOwnNotW γ GD r hr]

end protDefs

/-! # 4. THE FLOW EQUATIONS -/

section flowEqs

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [axG : AxirisG GF]
  [AxlogG GF Hent]

/-- THE READ FLOW EQUATION. -/
theorem flowEqOwnedRead (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (r : Geid) (a : Int) (Hl : List Hent) (S : GMapF Geid Qp) (wl : Geid)
    (vl : BitVec 8) (sOb0 : GSet Geid) (flowIn : Mea GF) :
    rvwmoCatConsistent GD →
    r ∈ GD.gdG.gxGmo → gisW GD.gdG r = false →
    (∀ p, p ∈ Hl → gwritesByte GD.gdG p.1 a p.2) →
    chainWith (gmoLt GD.gdG) (Hl.map Prod.fst) →
    (∀ w v, gwritesByte GD.gdG w a v → WeakRvwmoGraph.gpo GD.gdG w r → w ∈ Hl.map Prod.fst) →
    Hl.getLast? = some (wl, vl) →
    (∃ t v, greadsByte GD.gdG r a t v) →
    ((∃ e, e ∈ (FiniteMap.dom_set S : GSet Geid) ∧ gmoLt GD.gdG e r)
     ∨
     (wl ∈ (FiniteMap.dom_set S : GSet Geid) ∧
      (∀ e, e ∈ (FiniteMap.dom_set S : GSet Geid) → ¬ gmoLt GD.gdG e r) ∧
      WeakRvwmoGraph.gpo GD.gdG wl r ∧
      (∀ w' v', gwritesByte GD.gdG w' a v' →
        WeakRvwmoGraph.gpo GD.gdG wl w' → WeakRvwmoGraph.gpo GD.gdG w' r → False))) →
    (LawfulSet.ofList (gmoPrefix GD.gdG r) : GSet Geid) ⊆ sOb0 →
    iprop(([∗map] Rin ∈ flowIn, Rin) -∗ tokTie GD γ a Hl S) ⊢
      flowEqDyn GD r sOb0 flowIn iprop(⌜∀ t v, greadsByte GD.gdG r a t v → v = vl⌝) := by
  intro hcons hrgmo hnw hwr hch hown hlast hrd hcase hpref
  unfold flowEqDyn
  iintro Hflowin %σ %sOb %Hsub %Hnin Hob Hflow
  ihave Hob := (Hob_eq GD σ sOb).1 $$ Hob
  icases Hob with #Hob
  ihave Htie := Hflowin $$ Hflow
  have hkey : tokTie (GF := GF) GD γ a Hl S ∗ protInv γ GD sOb ⊢
      ⌜grfAt GD.gdG a wl r ∧ ∀ t v, greadsByte GD.gdG r a t v → v = vl⌝ :=
    (BI.sep_mono_right (protInvPrefixCovMem γ GD sOb r a hcons.1 hrgmo
      (subseteqTrans hpref Hsub))).trans
      (ownedReadRule GD a r γ Hl S wl vl hcons hwr hch hown hlast hrd hcase)
  ihave %hres := hkey $$ [$Htie $Hob]
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ
  isplitl []
  · iapply (Hob_eq GD σ (({r} : GSet Geid) ∪ sOb)).2
    iapply protInvReadStep γ GD sOb r Hnin hnw
    iexact Hob
  · ipureintro
    exact hres.2

/-- THE BYTE-RESTRICTED READ FLOW EQUATION (coverage over byte-`a` writes only). -/
theorem flowEqOwnedReadByte (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (r : Geid) (a : Int) (Hl : List Hent) (S : GMapF Geid Qp) (wl : Geid)
    (vl : BitVec 8) (sOb0 : GSet Geid) (flowIn : Mea GF) :
    rvwmoCatConsistent GD →
    r ∈ GD.gdG.gxGmo → gisW GD.gdG r = false →
    (∀ p, p ∈ Hl → gwritesByte GD.gdG p.1 a p.2) →
    chainWith (gmoLt GD.gdG) (Hl.map Prod.fst) →
    (∀ w v, gwritesByte GD.gdG w a v → WeakRvwmoGraph.gpo GD.gdG w r → w ∈ Hl.map Prod.fst) →
    Hl.getLast? = some (wl, vl) →
    (∃ t v, greadsByte GD.gdG r a t v) →
    ((∃ e, e ∈ (FiniteMap.dom_set S : GSet Geid) ∧ gmoLt GD.gdG e r)
     ∨
     (wl ∈ (FiniteMap.dom_set S : GSet Geid) ∧
      (∀ e, e ∈ (FiniteMap.dom_set S : GSet Geid) → ¬ gmoLt GD.gdG e r) ∧
      WeakRvwmoGraph.gpo GD.gdG wl r ∧
      (∀ w' v', gwritesByte GD.gdG w' a v' →
        WeakRvwmoGraph.gpo GD.gdG wl w' → WeakRvwmoGraph.gpo GD.gdG w' r → False))) →
    (∀ w v, gwritesByte GD.gdG w a v → gmoLt GD.gdG w r → w ∈ sOb0) →
    iprop(([∗map] Rin ∈ flowIn, Rin) -∗ tokTie GD γ a Hl S) ⊢
      flowEqDyn GD r sOb0 flowIn iprop(⌜∀ t v, greadsByte GD.gdG r a t v → v = vl⌝) := by
  intro hcons _hrgmo hnw hwr hch hown hlast hrd hcase hbytecov
  unfold flowEqDyn
  iintro Hflowin %σ %sOb %Hsub %Hnin Hob Hflow
  ihave Hob := (Hob_eq GD σ sOb).1 $$ Hob
  icases Hob with #Hob
  ihave Htie := Hflowin $$ Hflow
  have hkey : tokTie (GF := GF) GD γ a Hl S ∗ protInv γ GD sOb ⊢
      ⌜grfAt GD.gdG a wl r ∧ ∀ t v, greadsByte GD.gdG r a t v → v = vl⌝ :=
    (BI.sep_mono_right (protInvPrefixCovMemByte γ GD sOb r a
      (fun w v hwb hmo => Hsub w (hbytecov w v hwb hmo)))).trans
      (ownedReadRule GD a r γ Hl S wl vl hcons hwr hch hown hlast hrd hcase)
  ihave %hres := hkey $$ [$Htie $Hob]
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ
  isplitl []
  · iapply (Hob_eq GD σ (({r} : GSet Geid) ∪ sOb)).2
    iapply protInvReadStep γ GD sOb r Hnin hnw
    iexact Hob
  · ipureintro
    exact hres.2

/-- THE WRITE FLOW EQUATION (`graphData GD w = some data` an explicit hypothesis). -/
theorem flowEqOwnedWrite (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (w : Geid) (a : Int) (v : BitVec 8) (Hl : List Hent) (sOb0 : GSet Geid)
    (flowIn : Mea GF) (data : List (BitVec 8)) :
    gwritesByte GD.gdG w a v →
    (∀ a' v', gwritesByte GD.gdG w a' v' → a' = a) →
    graphData GD w = some data →
    iprop(([∗map] Rin ∈ flowIn, Rin) -∗ histAuth γ a 1 Hl) ⊢
      flowEqDyn GD w sOb0 flowIn iprop(⌜graphData GD w = some data⌝) := by
  intro hwb hsingle hgd
  unfold flowEqDyn
  iintro Hflowin %σ %sOb %Hsub %Hnin Hob Hflow
  ihave Hob := (Hob_eq GD σ sOb).1 $$ Hob
  ihave Hauth := Hflowin $$ Hflow
  imod protInvWriteStepAuth γ GD sOb w a v Hl Hnin hwb hsingle $$ [$Hob $Hauth]
    with ⟨Hinv, -⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists σ
  isplitl [Hinv]
  · iapply (Hob_eq GD σ (({w} : GSet Geid) ∪ sOb)).2
    iexact Hinv
  · ipureintro
    exact hgd

end flowEqs

/-! # 5. NON-VACUITY

On `AxGraphWit.fwd` (hart 0: `W x=1 (0,0); R.aq x (0,1)` reading its own store, forwarded;
`R y (0,2)`; the write `(0,0)` is gmo-LAST): allocate, write-step, and `flowEqOwnedRead`'s
instance at the read `(0,1)` discharges the real forwarded value `b1`. -/

section nonvacuity

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxannotGS GF] [AxgraphG GF]
  [AxlogG GF Hent] (γg γ : GName)

/-- The discharge of §4's `Hob_eq` at `AxWp`'s skeleton instance. -/
theorem nonvacuityHobEq :
    ∀ (GD : Gdexec) (σ : @AxirisG.obSt GF (skelAxirisG γg (ΦpOwn γ)))
      (s : GSet Geid),
      AxirisG.obStInterp (self := skelAxirisG γg (ΦpOwn γ)) GD σ s ⊣⊢
        protInv γ GD s :=
  fun _ _ _ => BIBase.BiEntails.rfl

theorem fwdGwritesByte0 : gwritesByte fwd.gdG (0, 0) 0 b1 :=
  (gwbBSpec _ _ _ _).1 (by decide +kernel)

theorem fwdGwritesByteSingle (a' : Int) (v' : BitVec 8) :
    gwritesByte fwd.gdG (0, 0) a' v' → a' = 0 := by
  intro h
  have h' := (gwritesByteBytes _ _ _ _).1 h
  have hb : gwrBytes fwd.gdG (0, 0) = [(0, b1)] := by decide +kernel
  rw [hb, List.mem_singleton] at h'
  exact (Prod.mk.inj h').1

theorem fwdGreadsByte0 : greadsByte fwd.gdG (0, 1) 0 3 b1 :=
  (grbBSpec _ _ _ _ _).1 (by decide +kernel)

/-- THE CLOSED THEOREM: write-step at `fwd`'s write, then `flowEqOwnedRead` at the read, whose
pure conclusion is the REAL forwarded value `b1`. -/
theorem protNonvacuity :
    histAuth (GF := GF) γ 0 1 [] ⊢ |==>
      @flowEqDyn hlc GF _ (skelAxirisG γg (ΦpOwn γ)) fwd (0, 1) ∅
        {[(0, 0) := tokTie fwd γ 0 [((0, 0), b1)] {[(0, 0) := (1 : Qp)]}]}
        iprop(⌜∀ t v, greadsByte fwd.gdG (0, 1) 0 t v → v = b1⌝) := by
  have h0 : ⊢ protInv (GF := GF) γ fwd (∅ : GSet Geid) := by
    unfold protInv
    exact BigSepS.bigSepS_empty.2
  have hrd := fwdGreadsByte0
  have hcore := flowEqOwnedRead (hlc := hlc) (GF := GF) (axG := skelAxirisG γg (ΦpOwn γ)) γ
    (nonvacuityHobEq γg γ) fwd (0, 1) 0 [((0, 0), b1)] {[(0, 0) := (1 : Qp)]} (0, 0) b1 ∅
    {[(0, 0) := tokTie fwd γ 0 [((0, 0), b1)] {[(0, 0) := (1 : Qp)]}]} AxGraphWit.fwdCat
    (greadsByteGmo _ _ _ _ _ AxGraphWit.fwdCat.1 hrd)
    (by decide +kernel)
    (by
      intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact fwdGwritesByte0)
    (by
      intro i w1 w2 _ hj
      cases i <;> simp at hj)
    (by
      rintro ⟨wi, wk⟩ v' _ ⟨heq, hlt, _, _⟩
      dsimp only at heq hlt
      have hk : wk = 0 := by omega
      subst heq hk
      simp)
    rfl
    ⟨3, b1, hrd⟩
    (by
      refine Or.inr ⟨?_, ?_, ?_, ?_⟩
      · rw [domSingleton, elemOfSingleton]
      · intro e he hmo
        rw [domSingleton, elemOfSingleton] at he
        subst he
        have h' := (gmoLtBSpec _ _ _).2 hmo
        have hf : gmoLtB fwd.gdG (0, 0) (0, 1) = false := by decide +kernel
        rw [hf] at h'
        cases h'
      · exact (gpoBSpec _ _ _).1 (by decide +kernel)
      · rintro w' v' _ ⟨_, hlt, _⟩ ⟨_, hlt', _⟩
        dsimp only at hlt hlt'
        omega)
    (by
      have hp : gmoPrefix fwd.gdG (0, 1) = [] := by decide +kernel
      rw [hp, listToSetNil])
  iintro H
  ihave Hi := h0
  imod protInvWriteStep γ fwd ∅ (0, 0) 0 b1 [] notElemOfEmpty fwdGwritesByte0
    fwdGwritesByteSingle $$ [$Hi $H] with ⟨-, -⟩
  imodintro
  iapply hcore
  iintro Hf
  iapply (BigSepM.bigSepM_singleton (Φ := fun (_ : Geid) (R : IProp GF) => R)).1
  iexact Hf

end nonvacuity

end Weak
