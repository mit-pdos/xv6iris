/-
Weak: **THE GENERIC (kind-indexed) LOCK PROTOCOL INSTANCE** (AxSL tier; LB/AxSL lock slice):
the lock policy and annotation maps built UNIFORMLY BY EVENT KIND over an arbitrary completed
scheduler run, and the adequacy theorem wired through `AxSchedGD.schedProcAdequate`.

Rocq: `iris/AxLockGen.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Replaces `AxLockAdeq`'s per-event (four/five-event) maps by maps built by event KIND
(plain `L`-release, plain `L`-acquire, a write to the owned byte `x`, everything else) with
`list_to_map` over `gxGmo`, as `AxProtCov3` does.  Scope: a graph writing `x` and `L`, one write
of `x` per critical section.  A write's predecessor is its gco-predecessor when that is in the
same critical section, else the acquire opening it (a `gacqPo` / rule-5 edge, free).  A
release's predecessor is the po-latest of (its section's `x`-write, the opening acquire); its
ordering before the release needs a covering fence, so that ONE edge is the named hypothesis
`HrelFence`.  An acquire's predecessor is its gco-predecessor w.r.t. `L` (free, `gco` arm).

  §0 `list_to_map` lookup lemmas;  §1 kind classification (`isRelL`/`isAcqL`/`isWx`, booleans);
  §2 the predecessor functions and `lockPred`;  §3 `axlockPol` (the concrete `Axpol`, LOCAL:
  a reducible `def`, never a global instance, passed explicitly / by `letI`);  §4 the per-kind
  flow obligation `axlockPredSubFlow` + corollaries;  §5 the annotation maps `naOf`/`eaOf` and
  their domain / `HeaLob` lemmas;  §6 `lockAdequateGhost`.

  WHAT REMAINS OPEN (as in Rocq): §6 takes `HflowInit` (the initial `ordEaTodoL … gxGmo 0`
  entailment from the run's starting `histAuth … 1 []` at both bytes) as a NAMED hypothesis.

**Fetches / WP step clause.**  Nothing here mentions fetches or the WP step clause: the policy is
over graph labels (`Lbl` has no fetch constructor, Stage C) and §6 only applies
`AxSchedGD.schedProcAdequate` as a black box, so the pending Q8 `fetchPin` rework of the step
clause does not touch this file.

## Deviations from Rocq

1. NAMES: camelCase (map below).  Duplicated Rocq names (with `AxLockN`/`AxProtCov3`/
   `AxProtGate`/`AxLockAdeq`) are file-qualified `AxLockGen.*`.  No Lean-only helpers.
2. VOCABULARY (as `AxSchedGD`/`AxProt`): `gd_g GD` ↦ `GD.gdG`, `last` ↦ `List.getLast?`,
   `filter` ↦ `List.filter`, `list_to_map` ↦ `PartialMap.ofList`, `list_to_set` ↦
   `LawfulSet.ofList`, `dom` ↦ `FiniteMap.dom_set`, `gset geid` ↦ `GSet Geid`, `mea Σ`/`sra Σ` ↦
   `Mea GF`/`Sra GF`, `Z` ↦ `Int`, `WeakLitmus.b0/b1` ↦ `b0`/`b1`, `{[x; L]}` ↦
   `({x} : GSet Int) ∪ {L}`, `from_option id emp` ↦ `AxWp.fromOption (fun P => P) iprop(emp)`,
   `|={⊤}[∅]▷=>^n` ↦ `|={⊤}[∅]▷=>^[n]`.
3. SECTION VARIABLES are explicit leading arguments, each lemma taking exactly the variables its
   Rocq `Proof using` / body mentions (`Hxl` is kept where Rocq's `Proof using` lists it, unused as
   in Rocq).  `axlockPol` is a `@[reducible] def`, not an instance (Rocq: `Local Instance`):
   statements over `ordEaTodoL` bind it by `letI`, `Axpol.sPol`/`lobp` are applied at it by `@`.
4. `lockAdequateGhost`: Rocq's `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc` (as
   `AxSchedGD.schedProcAdequate`); wand chains stated `⊢ A -∗ B -∗ C`, `HflowInit` as `A ⊢ B`.
   Rocq's section context `ax_lockG Σ`, `γc`, `ob_D`, `ob_hm`, `Hob_eq'` are NOT premises of any
   Rocq statement (not in any body or `Proof using`), so they are not arguments here either; no
   `AxLockG` is needed.  `Hdefer` is unused, as in Rocq.
5. `lgMapOfFunLookupSome`/`None` and `lgFmapFstPair` are stated at `GMapF Geid V`.

**Rocq → Lean name map.**  `lg_fmap_fst_pair` `AxLockGen.lgFmapFstPair`,
`lg_map_of_fun_lookup_some` `AxLockGen.lgMapOfFunLookupSome`, `lg_map_of_fun_lookup_none`
`AxLockGen.lgMapOfFunLookupNone`, `is_relL` `AxLockGen.isRelL`, `is_acqL` `AxLockGen.isAcqL`,
`is_wx` `AxLockGen.isWx`, `co_pred` `AxLockGen.coPred`, `acq_before` `AxLockGen.acqBefore`,
`xw_pred_o` `AxLockGen.xwPredO`, `rel_pred_o` `AxLockGen.relPredO`, `acq_pred_o`
`AxLockGen.acqPredO`, `opt_singleton` `AxLockGen.optSingleton`, `lock_pred`
`AxLockGen.lockPred`, `axlock_pol` `axlockPol`, `co_pred_gco` `AxLockGen.coPredGco`,
`acq_before_gpo` `AxLockGen.acqBeforeGpo`, `acq_before_is_acqL` `AxLockGen.acqBeforeIsAcqL`,
`gco_sub_flow` `AxLockGen.gcoSubFlow`, `gacq_po_sub_flow` `AxLockGen.gacqPoSubFlow`,
`axlock_pred_sub_flow` `axlockPredSubFlow`, `axlock_pred_sub_flow_spol` `axlockPredSubFlowSpol`,
`axlock_pred_sub_flow_lobp` `axlockPredSubFlowLobp`, `axlock_axpol_wf_L` `axlockAxpolWfL`,
`axlock_sched_axpol_wf_proc` `axlockSchedAxpolWfProc`, `na_val` `AxLockGen.naVal`, `ea_val`
`AxLockGen.eaVal`, `na_of` `AxLockGen.naOf`, `ea_of` `AxLockGen.eaOf`, `na_of_dom`
`AxLockGen.naOfDom`, `ea_of_dom` `AxLockGen.eaOfDom`, `na_ea_dom_eq` `naEaDomEq`, `Hea_lob0`
`AxLockGen.HeaLob0`, `Hea_lob0_lobp` `AxLockGen.HeaLob0Lobp`, `lock_adequate_ghost`
`lockAdequateGhost`.

**Dropped:** nothing (no weak Rocq file imports `AxLockGen`).
-/
import Weak.AxSchedGD
import Weak.AxGraphDec
import Weak.AxToken
import Weak.AxGhost
import Weak.WeakRvwmoLock
import Weak.WeakLitmus
import MachCSL.StdppMap
import MachCSL.StdppSet
import MachCSL.StdppList

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 0. Generic `list_to_map` lookup lemmas -/

theorem AxLockGen.lgFmapFstPair {A B : Type} (f : A → B) (l : List A) :
    ((l.map fun x => (x, f x)).map Prod.fst) = l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, ih]

theorem AxLockGen.lgMapOfFunLookupSome {V : Type} (f : Geid → V) (K : List Geid) (Hnd : K.Nodup)
    (e : Geid) (He : e ∈ K) :
    get? (PartialMap.ofList (K.map fun e0 => (e0, f e0)) : GMapF Geid V) e = some (f e) := by
  apply elemOfListToMap1
  · rw [AxLockGen.lgFmapFstPair]; exact Hnd
  · exact List.mem_map.2 ⟨e, He, rfl⟩

theorem AxLockGen.lgMapOfFunLookupNone {V : Type} (f : Geid → V) (K : List Geid) (e : Geid)
    (He : e ∉ K) :
    get? (PartialMap.ofList (K.map fun e0 => (e0, f e0)) : GMapF Geid V) e = none := by
  apply notElemOfListToMap.1
  rw [AxLockGen.lgFmapFstPair]; exact He

/-! # 1. Kind classification -/

def AxLockGen.isRelL (GD : Gdexec) (L : Int) (e : Geid) : Bool := gwbB GD.gdG e L b0
def AxLockGen.isAcqL (GD : Gdexec) (L : Int) (e : Geid) : Bool := gwbB GD.gdG e L b1
def AxLockGen.isWx (GD : Gdexec) (x : Int) (e : Geid) : Bool := gwaB GD.gdG e x

/-! # 2. The predecessor functions, and `lockPred` -/

/-- The gco-immediate predecessor of `e` w.r.t. whichever byte `e` writes. -/
def AxLockGen.coPred (GD : Gdexec) (e : Geid) : Option Geid :=
  (GD.gdG.gxGmo.filter fun w => gcoB GD.gdG w e).getLast?

/-- The last `isAcqL` event program-order-before `e`: the acquire opening `e`'s section. -/
def AxLockGen.acqBefore (GD : Gdexec) (L : Int) (e : Geid) : Option Geid :=
  (GD.gdG.gxGmo.filter fun w => gpoB GD.gdG w e && AxLockGen.isAcqL GD L w).getLast?

/-- `e` writes `x`: its token predecessor. -/
def AxLockGen.xwPredO (GD : Gdexec) (L : Int) (e : Geid) : Option Geid :=
  match AxLockGen.coPred GD e with
  | none => none
  | some w0 =>
    some (match AxLockGen.acqBefore GD L e with
          | some a0 => if gmoLtB GD.gdG w0 a0 then a0 else w0
          | none => w0)

/-- `e` releases `L`: the po-latest of its section's `x`-write or opening acquire. -/
def AxLockGen.relPredO (GD : Gdexec) (L x : Int) (e : Geid) : Option Geid :=
  (GD.gdG.gxGmo.filter fun w =>
    gpoB GD.gdG w e && (AxLockGen.isWx GD x w || AxLockGen.isAcqL GD L w)).getLast?

/-- `e` acquires `L`: the release it reads from. -/
def AxLockGen.acqPredO (GD : Gdexec) (e : Geid) : Option Geid := AxLockGen.coPred GD e

def AxLockGen.optSingleton (o : Option Geid) : GSet Geid :=
  match o with
  | some p => {p}
  | none => ∅

/-- THE POLICY: kind-indexed. -/
def AxLockGen.lockPred (GD : Gdexec) (L x : Int) (e : Geid) : GSet Geid :=
  if AxLockGen.isRelL GD L e then AxLockGen.optSingleton (AxLockGen.relPredO GD L x e)
  else if AxLockGen.isAcqL GD L e then AxLockGen.optSingleton (AxLockGen.acqPredO GD e)
  else if AxLockGen.isWx GD x e then AxLockGen.optSingleton (AxLockGen.xwPredO GD L e)
  else ∅

/-! # 3. The concrete `Axpol` (Rocq `Local Instance`; here a reducible def) -/

@[reducible] def axlockPol (GD : Gdexec) (L x : Int) : Axpol :=
  ⟨fun _ => AxLockGen.lockPred GD L x, fun _ => AxLockGen.lockPred GD L x⟩

/-! # 4. The per-kind flow obligation -/

theorem AxLockGen.coPredGco (GD : Gdexec) (e w0 : Geid) :
    AxLockGen.coPred GD e = some w0 → gco GD.gdG w0 e := by
  intro Hl
  have Hin := List.mem_of_getLast? Hl
  rw [List.mem_filter] at Hin
  exact (gcoBSpec _ _ _).1 Hin.2

theorem AxLockGen.acqBeforeGpo (GD : Gdexec) (L : Int) (e a0 : Geid) :
    AxLockGen.acqBefore GD L e = some a0 → WeakRvwmoGraph.gpo GD.gdG a0 e := by
  intro Hl
  have Hin := List.mem_of_getLast? Hl
  rw [List.mem_filter, Bool.and_eq_true] at Hin
  exact (gpoBSpec _ _ _).1 Hin.2.1

theorem AxLockGen.acqBeforeIsAcqL (GD : Gdexec) (L : Int) (e a0 : Geid) :
    AxLockGen.acqBefore GD L e = some a0 → AxLockGen.isAcqL GD L a0 = true := by
  intro Hl
  have Hin := List.mem_of_getLast? Hl
  rw [List.mem_filter, Bool.and_eq_true] at Hin
  exact Hin.2.2

theorem AxLockGen.gcoSubFlow (GD : Gdexec) (w e : Geid) : gco GD.gdG w e → gobCatFlow GD w e :=
  fun Hco => .single (Or.inr (Or.inr (Or.inr (Or.inl Hco))))

theorem AxLockGen.gacqPoSubFlow (GD : Gdexec) (L : Int)
    (HacqRead : ∀ e', AxLockGen.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockGen.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (a0 e : Geid) :
    WeakRvwmoGraph.gpo GD.gdG a0 e → AxLockGen.isAcqL GD L a0 = true → gmem GD.gdG e →
    gobCatFlow GD a0 e :=
  fun Hpo Hacq Hmem =>
    .single (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨Hpo, HacqRead a0 Hacq, HacqAq a0 Hacq, Hmem⟩)))))))

set_option linter.unusedVariables false in
theorem axlockPredSubFlow (GD : Gdexec) (L x : Int) (Hxl : x ≠ L)
    (HrelFence : ∀ e p, AxLockGen.isRelL GD L e = true → AxLockGen.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockGen.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockGen.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (e e' : Geid) :
    e' ∈ AxLockGen.lockPred GD L x e → gobCatFlow GD e' e := by
  unfold AxLockGen.lockPred
  cases Hrel : AxLockGen.isRelL GD L e
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases Hacq : AxLockGen.isAcqL GD L e
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases Hwx : AxLockGen.isWx GD x e
      · simp only [Bool.false_eq_true, ↓reduceIte]
        intro h; exact absurd h notElemOfEmpty
      · simp only [↓reduceIte]
        unfold AxLockGen.optSingleton AxLockGen.xwPredO
        cases Hco : AxLockGen.coPred GD e with
        | none => intro h; exact absurd h notElemOfEmpty
        | some w0 =>
          have Hmem : gmem GD.gdG e := by
            obtain ⟨v, Hwb⟩ := (gwaBSpec _ _ _).1 Hwx
            exact WeakRvwmoGraph.glblIsWGmem _ _ (gwritesByteGlblW _ _ _ _ Hwb)
          cases Hab : AxLockGen.acqBefore GD L e with
          | none =>
            intro h; rw [elemOfSingleton.1 h]
            exact AxLockGen.gcoSubFlow GD w0 e (AxLockGen.coPredGco GD e w0 Hco)
          | some a0 =>
            cases Hlt : gmoLtB GD.gdG w0 a0
            · intro h
              simp only [Hlt, Bool.false_eq_true, ↓reduceIte] at h
              rw [elemOfSingleton.1 h]
              exact AxLockGen.gcoSubFlow GD w0 e (AxLockGen.coPredGco GD e w0 Hco)
            · intro h
              simp only [Hlt, ↓reduceIte] at h
              rw [elemOfSingleton.1 h]
              exact AxLockGen.gacqPoSubFlow GD L HacqRead HacqAq a0 e
                (AxLockGen.acqBeforeGpo GD L e a0 Hab) (AxLockGen.acqBeforeIsAcqL GD L e a0 Hab)
                Hmem
    · simp only [↓reduceIte]
      unfold AxLockGen.optSingleton AxLockGen.acqPredO
      cases Hco : AxLockGen.coPred GD e with
      | none => intro h; exact absurd h notElemOfEmpty
      | some w0 =>
        intro h; rw [elemOfSingleton.1 h]
        exact AxLockGen.gcoSubFlow GD w0 e (AxLockGen.coPredGco GD e w0 Hco)
  · simp only [↓reduceIte]
    unfold AxLockGen.optSingleton
    cases Hp : AxLockGen.relPredO GD L x e with
    | none => intro h; exact absurd h notElemOfEmpty
    | some p =>
      intro h; rw [elemOfSingleton.1 h]
      exact HrelFence e p Hrel Hp

/-- Restated at the literal `sPol` projection of `axlockPol`. -/
theorem axlockPredSubFlowSpol (GD : Gdexec) (L x : Int) (Hxl : x ≠ L)
    (HrelFence : ∀ e p, AxLockGen.isRelL GD L e = true → AxLockGen.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockGen.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockGen.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (e e' : Geid) :
    e' ∈ @Axpol.sPol (axlockPol GD L x) GD e → gobCatFlow GD e' e :=
  axlockPredSubFlow GD L x Hxl HrelFence HacqRead HacqAq e e'

/-- Restated at the literal `lobp` projection of `axlockPol`. -/
theorem axlockPredSubFlowLobp (GD : Gdexec) (L x : Int) (Hxl : x ≠ L)
    (HrelFence : ∀ e p, AxLockGen.isRelL GD L e = true → AxLockGen.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockGen.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockGen.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (e e' : Geid) :
    e' ∈ @Axpol.lobp (axlockPol GD L x) GD e → gobCatFlow GD e' e :=
  axlockPredSubFlow GD L x Hxl HrelFence HacqRead HacqAq e e'

theorem axlockAxpolWfL (GD : Gdexec) (L x : Int) (Hxl : x ≠ L)
    (HrelFence : ∀ e p, AxLockGen.isRelL GD L e = true → AxLockGen.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockGen.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockGen.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (L0 : List Geid) (Hpc : LPredClosedFlow GD L0) :
    @axpolWfL (axlockPol GD L x) GD L0 :=
  @axpolWfLOfPredClosedFlow (axlockPol GD L x) GD L0
    (axlockPredSubFlowSpol GD L x Hxl HrelFence HacqRead HacqAq)
    (axlockPredSubFlowLobp GD L x Hxl HrelFence HacqRead HacqAq) Hpc

theorem axlockSchedAxpolWfProc (GD : Gdexec) (L x : Int) (Hxl : x ≠ L)
    (Hcons : rvwmoCatConsistent GD)
    (HrelFence : ∀ e p, AxLockGen.isRelL GD L e = true → AxLockGen.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockGen.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockGen.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅) :
    @axpolWfProc (axlockPol GD L x) GD st.sProc :=
  @schedAxpolWfProc (axlockPol GD L x) GD Hcons st Hrun Hfull Hdone
    (axlockPredSubFlowSpol GD L x Hxl HrelFence HacqRead HacqAq)
    (axlockPredSubFlowLobp GD L x Hxl HrelFence HacqRead HacqAq)

/-! # 5. The kind-indexed annotation maps -/

section annot

variable {GF : BundledGFunctors} [AxlogG GF Hent]

def AxLockGen.naVal (GD : Gdexec) (L x : Int) (γ : GName) (e : Geid) : IProp GF :=
  if AxLockGen.isWx GD x e then
    iprop(∃ (H : List Hent) (v : BitVec 8) (data : List (BitVec 8)),
      tokTie GD γ x H {[e := (1 : Qp)]} ∗ ⌜gwritesByte GD.gdG e x v⌝ ∗
      ⌜graphData GD e = some data⌝)
  else if AxLockGen.isRelL GD L e then
    iprop(∃ (H_L : List Hent), histSnap γ L H_L)
  else iprop(emp)

def AxLockGen.eaVal (GD : Gdexec) (L x : Int) (γ : GName) (e : Geid) : Mea GF :=
  if AxLockGen.isRelL GD L e then
    match AxLockGen.relPredO GD L x e with
    | some p => {[p := iprop(∃ (H : List Hent), tokTie GD γ x H {[e := (1 : Qp)]})]}
    | none => ∅
  else if AxLockGen.isAcqL GD L e then
    match AxLockGen.acqPredO GD e with
    | some p => {[p := iprop(⌜gwritesByte GD.gdG p L b0⌝ ∗
                  ∃ (H : List Hent), tokTie GD γ x H {[e := (1 : Qp)]})]}
    | none => ∅
  else ∅

def AxLockGen.naOf (GD : Gdexec) (L x : Int) (γ : GName) : Mea GF :=
  PartialMap.ofList (GD.gdG.gxGmo.map fun e => (e, AxLockGen.naVal GD L x γ e))

def AxLockGen.eaOf (GD : Gdexec) (L x : Int) (γ : GName) : Sra GF :=
  PartialMap.ofList (GD.gdG.gxGmo.map fun e => (e, AxLockGen.eaVal GD L x γ e))

theorem AxLockGen.naOfDom (GD : Gdexec) (L x : Int) (Hcons : rvwmoCatConsistent GD) (γ : GName) :
    (FiniteMap.dom_set (AxLockGen.naOf (GF := GF) GD L x γ) : GSet Geid) =
      LawfulSet.ofList GD.gdG.gxGmo := by
  have Hnd := (schedHGwf GD Hcons).1
  rw [setEq]
  intro e
  rw [elemOfDom, elemOfListToSet]
  constructor
  · intro Hv
    by_cases Hin : e ∈ GD.gdG.gxGmo
    · exact Hin
    · unfold AxLockGen.naOf at Hv
      rw [AxLockGen.lgMapOfFunLookupNone _ _ e Hin] at Hv
      exact absurd Hv Bool.false_ne_true
  · intro Hin
    unfold AxLockGen.naOf
    rw [AxLockGen.lgMapOfFunLookupSome _ _ Hnd e Hin]
    rfl

theorem AxLockGen.eaOfDom (GD : Gdexec) (L x : Int) (Hcons : rvwmoCatConsistent GD) (γ : GName) :
    (FiniteMap.dom_set (AxLockGen.eaOf (GF := GF) GD L x γ) : GSet Geid) =
      LawfulSet.ofList GD.gdG.gxGmo := by
  have Hnd := (schedHGwf GD Hcons).1
  rw [setEq]
  intro e
  rw [elemOfDom, elemOfListToSet]
  constructor
  · intro Hv
    by_cases Hin : e ∈ GD.gdG.gxGmo
    · exact Hin
    · unfold AxLockGen.eaOf at Hv
      rw [AxLockGen.lgMapOfFunLookupNone _ _ e Hin] at Hv
      exact absurd Hv Bool.false_ne_true
  · intro Hin
    unfold AxLockGen.eaOf
    rw [AxLockGen.lgMapOfFunLookupSome _ _ Hnd e Hin]
    rfl

theorem naEaDomEq (GD : Gdexec) (L x : Int) (Hcons : rvwmoCatConsistent GD) (γ : GName) :
    (FiniteMap.dom_set (AxLockGen.eaOf (GF := GF) GD L x γ) : GSet Geid) =
      FiniteMap.dom_set (AxLockGen.naOf (GF := GF) GD L x γ) := by
  rw [AxLockGen.eaOfDom GD L x Hcons, AxLockGen.naOfDom GD L x Hcons]

set_option linter.unusedVariables false in
theorem AxLockGen.HeaLob0 (GD : Gdexec) (L x : Int) (Hxl : x ≠ L) (Hcons : rvwmoCatConsistent GD)
    (HrelFence : ∀ e p, AxLockGen.isRelL GD L e = true → AxLockGen.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockGen.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockGen.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (γ : GName) :
    ∀ e0 gm, get? (AxLockGen.eaOf (GF := GF) GD L x γ) e0 = some gm →
      (FiniteMap.dom_set gm : GSet Geid) ⊆ AxLockGen.lockPred GD L x e0 := by
  have Hnd := (schedHGwf GD Hcons).1
  intro e0 gm Hea
  by_cases Hin : e0 ∈ GD.gdG.gxGmo
  · unfold AxLockGen.eaOf at Hea
    rw [AxLockGen.lgMapOfFunLookupSome _ _ Hnd e0 Hin] at Hea
    cases Option.some.inj Hea
    unfold AxLockGen.eaVal AxLockGen.lockPred
    cases Hrel : AxLockGen.isRelL GD L e0
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases Hacq : AxLockGen.isAcqL GD L e0
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [domEmpty]; exact emptySubseteq
      · simp only [↓reduceIte]
        unfold AxLockGen.optSingleton
        cases AxLockGen.acqPredO GD e0 with
        | none => rw [domEmpty]
        | some p => rw [domSingleton]
    · simp only [↓reduceIte]
      unfold AxLockGen.optSingleton
      cases AxLockGen.relPredO GD L x e0 with
      | none => rw [domEmpty]
      | some p => rw [domSingleton]
  · unfold AxLockGen.eaOf at Hea
    rw [AxLockGen.lgMapOfFunLookupNone _ _ e0 Hin] at Hea
    cases Hea

/-- Restated at the literal `lobp` projection. -/
theorem AxLockGen.HeaLob0Lobp (GD : Gdexec) (L x : Int) (Hxl : x ≠ L)
    (Hcons : rvwmoCatConsistent GD)
    (HrelFence : ∀ e p, AxLockGen.isRelL GD L e = true → AxLockGen.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockGen.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockGen.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (γ : GName) :
    ∀ e0 gm, get? (AxLockGen.eaOf (GF := GF) GD L x γ) e0 = some gm →
      (FiniteMap.dom_set gm : GSet Geid) ⊆ @Axpol.lobp (axlockPol GD L x) GD e0 :=
  AxLockGen.HeaLob0 GD L x Hxl Hcons HrelFence HacqRead HacqAq γ

end annot

/-! # 6. `lockAdequateGhost` — the adequacy theorem -/

section adequate

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [AxlogG GF Hent]

set_option linter.unusedVariables false in
theorem lockAdequateGhost (GD : Gdexec) (L x : Int) (Hxl : x ≠ L)
    (Hcons : rvwmoCatConsistent GD)
    (HrelFence : ∀ e p, AxLockGen.isRelL GD L e = true → AxLockGen.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockGen.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockGen.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (γ : GName)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (Hdefer : ∀ r, deferredSnapAvail GD st.sEverD r)
    (HflowInit :
      ([∗set] a ∈ (({x} : GSet Int) ∪ {L}), histAuth (GF := GF) γ a 1 []) ⊢
        letI := axlockPol GD L x
        ordEaTodoL GD (AxLockGen.eaOf GD L x γ) (AxLockGen.naOf GD L x γ) GD.gdG.gxGmo 0)
    (σ0 : AxirisG.obSt GF) :
    ⊢ ([∗set] a ∈ (({x} : GSet Int) ∪ {L}), histAuth (GF := GF) γ a 1 []) -∗
      AxirisG.obStInterp GD σ0 ∅ -∗
      |={⊤}[∅]▷=>^[st.sProc.length]
        ∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList st.sProc) ∗
          [∗set] e0 ∈ (LawfulSet.ofList st.sProc : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? (AxLockGen.naOf GD L x γ) e0) := by
  letI := axlockPol GD L x
  have HGw := schedHGwf GD Hcons
  have HC6 := schedHCat6gmo GD Hcons
  obtain ⟨Hmemiff, HndP, _⟩ := schedCorrect GD.gdG HGw HC6 st Hrun Hfull Hdone
  have Hperm : st.sProc.Perm GD.gdG.gxGmo := NoDup_Permutation HndP HGw.1 Hmemiff
  have Htodo : ([∗set] a ∈ (({x} : GSet Int) ∪ {L}), histAuth (GF := GF) γ a 1 []) ⊢
      ordEaTodoL GD (AxLockGen.eaOf GD L x γ) (AxLockGen.naOf GD L x γ) st.sProc 0 := by
    refine HflowInit.trans ?_
    unfold ordEaTodoL
    simp only [List.drop_zero]
    exact (BigSepL.bigSepL_perm Hperm.symm).1
  have Hdom : (LawfulSet.ofList st.sProc : GSet Geid) ⊆
      FiniteMap.dom_set (AxLockGen.naOf (GF := GF) GD L x γ) := by
    rw [AxLockGen.naOfDom GD L x Hcons]
    intro e' He'
    rw [elemOfListToSet] at He' ⊢
    exact (Hmemiff e').1 He'
  have Had := schedProcAdequate GD Hcons st Hrun Hfull Hdone
    (axlockPredSubFlowSpol GD L x Hxl HrelFence HacqRead HacqAq)
    (axlockPredSubFlowLobp GD L x Hxl HrelFence HacqRead HacqAq)
    (AxLockGen.naOf GD L x γ) (AxLockGen.eaOf GD L x γ)
    (naEaDomEq GD L x Hcons γ) Hdom
    (AxLockGen.HeaLob0Lobp GD L x Hxl Hcons HrelFence HacqRead HacqAq γ) Hdefer σ0
  iintro Hb Hob
  ihave Ht := Htodo $$ Hb
  iapply Had $$ Ht Hob

end adequate

end Weak
