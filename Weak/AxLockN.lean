/-
Weak: **THE LOCK DISCIPLINE, EXTRACTED** (AxSL tier; LB/AxSL lock slice):
`lockDiscGeneric` / `lockNSound`, plus the two certificates and the honesty flag.

Rocq: `iris/AxLockN.v` @ xxvzwolszwmp.

## The Rocq header, in substance

(1) `lockDiscGeneric` extracts, as a plain Prop via soundness (`Iris.pure_soundness` +
`step_fupdN_soundness_close`, the same extraction as `AxLockAdeq2.lockSliceSound'`/
`AxLockRace3.twoFullWriteObligationsContradict`), the pure discipline `csHandoffLast` needs:
every write to the shared byte `x` belongs to SOME critical section on `L`
(`AxLockN.xwIsCsWrite`).  (2) `lockNSound` composes it with `AxLockSerial.csHandoffLast`.
(3) certificates: (a) `lock3sHscope` — `lock3s` satisfies `lockNSound`'s `Hscope`;
(b) `raceNotVerifiable'` — the 2-slot program-verifies premise of `AxLockRace3`, now at the
concrete `protInvLock'`-based instance `AxLockN.axGRace`, is contradictory (C's write, fixed to
the owned-write rule, collides with `w_x`'s already-deposited token).

`naVal'` is `AxLockGen.naVal` with ONE extra pure conjunct `⌜xwIsCsWrite GD L e⌝` at the `isWx`
branch; `HflowInit'` is the hypothesis a concrete instantiation owes.  As in Rocq, the file does
not reuse `AxLockGen`: every generic helper is re-derived, fully explicit in `GD`/`L`/`x`.  The
concrete instance `AxLockN.axGnInst` is `AxLockAdeq2.axGInst`'s idiom (`obStInterp :=
protInvLock'`), so no ob-state bridge hypothesis is needed.

VACUITY (Rocq §7/§10, advisor 2026-09-27): `HflowInit'` — required by `lockDiscGeneric` and
`lockNSound` — is UNSATISFIABLE for `lock3s` (`lockNPremiseRefutedLock3s`, the machine-checked
honesty flag) and for every graph with a disciplined `x`-write followed by its section's
release: `naVal'` demands a FULL `tokTie … {[w := 1]}` as the write's own fact while `eaVal`
demands a second full one deposited to the release; `ownedWriteExcluded` refutes both.  The
fix is `AxLockN2`.  Do not build new work on `HflowInit'`.

**Ghost state allocated** (inside the soundness continuations, by `AxLockAdeq2.lockInitialAlloc`):
the history log (`AxlogG GF Hent`, name `γ`) at `x` and `L` with empty histories and the
claimed-set authority (`AxLockG GF`, name `γc`) at `∅`.

**Fetches / Q8.** No fetch content (graph labels only; the WP step clause is never used).

## Deviations from Rocq

1. NAMES: camelCase (map below).  Duplicated Rocq names are file-qualified `AxLockN.*`
   (`isRelL`, `isAcqL`, `isWx`, `coPred`, `acqBefore`, `xwPredO`, `relPredO`, `acqPredO`,
   `optSingleton`, `lockPred`, `coPredGco`, `acqBeforeGpo`, `acqBeforeIsAcqL`, `gcoSubFlow`,
   `gacqPoSubFlow`, `naVal'`, `eaVal`, `naOf'`, `eaOf`, `lgFmapFstPair`,
   `lgMapOfFunLookupSome`/`None`, `naOf'Dom`, `eaOfDom`, `HeaLob0`, `HeaLob0Lobp`, `l2r`,
   `axGn3Inst`).  Lean-only helpers (file-qualified): `AxLockN.bytesIntro` (the two initial
   `histAuth`s as the `{x} ∪ {L}` big-sep), `AxLockN.obInitLock` (the empty `protInvLock'` from
   the empty claimed authority), `AxLockN.naBagCs` (the final bag projection of
   `lockDiscGeneric`), `AxLockN.neXC`/`neXRel`/`neCRel` (the race events' distinctness),
   `AxLockN.lock3sRelC3s`/`lock3sRelPredC3s` (the kernel facts `isRelL … eRelC3s = true`,
   `relPredO … eRelC3s = some eWC3s`, shared by §10's lemmas).
2. VOCABULARY as `AxLockGen` deviation 2 (`list_to_map` ↦ `PartialMap.ofList`, `last` ↦
   `getLast?`, `dom` ↦ `FiniteMap.dom_set`, `<[k := v]> m` ↦ `insert m k v`, `bool_decide (e =
   w)` ↦ `if e = w`, `tt` ↦ `()`, `vm_compute` ↦ `decide +kernel` on the Bool/Option facts),
   `step_fupdN_soundness_no_lc'` ↦ `step_fupdN_soundness_close (hlc := .hasNoLC)`.
3. SECTION VARIABLES are explicit leading arguments (`GD L x Hxl Hcons HrelFence HacqRead
   HacqAq`, then `γ γc`), each lemma taking those its Rocq body uses.  `axlockn_pol_inst`
   (Rocq's section-local `Local Instance`) is not a declaration: `axlocknPol GD L x` is a
   `@[reducible] def` passed explicitly (`@ordEaTodoL (axlocknPol GD L x) …`, `@Axpol.sPol`),
   as are the concrete `AxirisG` records (`axGnInst`, `axGRace`, `axGn3Inst`, Rocq instances)
   and `racePol`/`lock3sPol` (Rocq `Local Instance`s).  `AxirisG` has no `ax_text` field
   (Stage C).
4. `lockAdequateGhost'` is stated at `[InvGS_gen hlc GF]` for any `hlc` (Rocq `HasNoLc`), as
   `AxLockGen.lockAdequateGhost`; wand chains as `⊢ A -∗ B -∗ C -∗ D`, `HflowInit'` as `A ⊢ B`.
5. `lockDiscGeneric`: Rocq destructs the step count to `S k`; here `∃ k, length = k + 1` and
   the step-fupd is unfolded once (`rfl`) around the `imod` of `lockInitialAlloc`.

**Rocq → Lean name map.**  `is_relL` `AxLockN.isRelL`, `is_acqL` `AxLockN.isAcqL`, `is_wx`
`AxLockN.isWx`, `co_pred` `AxLockN.coPred`, `acq_before` `AxLockN.acqBefore`, `xw_pred_o`
`AxLockN.xwPredO`, `rel_pred_o` `AxLockN.relPredO`, `acq_pred_o` `AxLockN.acqPredO`,
`opt_singleton` `AxLockN.optSingleton`, `lock_pred` `AxLockN.lockPred`, `axlockn_pol`
`axlocknPol`, `co_pred_gco` `AxLockN.coPredGco`, `acq_before_gpo` `AxLockN.acqBeforeGpo`,
`acq_before_is_acqL` `AxLockN.acqBeforeIsAcqL`, `gco_sub_flow` `AxLockN.gcoSubFlow`,
`gacq_po_sub_flow` `AxLockN.gacqPoSubFlow`, `axlockn_pred_sub_flow` `axlocknPredSubFlow`,
`axlockn_pred_sub_flow_spol` `axlocknPredSubFlowSpol`, `axlockn_pred_sub_flow_lobp`
`axlocknPredSubFlowLobp`, `xw_is_cs_write` `AxLockN.xwIsCsWrite`, `gmo_perm_of_run`
`gmoPermOfRun`, `na_val'` `AxLockN.naVal'`, `ea_val` `AxLockN.eaVal`, `na_of'` `AxLockN.naOf'`,
`ea_of` `AxLockN.eaOf`, `lg_fmap_fst_pair` `AxLockN.lgFmapFstPair`, `lg_map_of_fun_lookup_some`
`AxLockN.lgMapOfFunLookupSome`, `lg_map_of_fun_lookup_none` `AxLockN.lgMapOfFunLookupNone`,
`na_of'_dom` `AxLockN.naOf'Dom`, `ea_of_dom` `AxLockN.eaOfDom`, `na_ea_dom_eq'` `naEaDomEq'`,
`Hea_lob0` `AxLockN.HeaLob0`, `Hea_lob0_lobp` `AxLockN.HeaLob0Lobp`, `axlockn_pol_inst` (folded,
deviation 3), `AxGn_inst` `AxLockN.axGnInst`, `AxGn_ob_st_interp_unfold` `axGnObStInterpUnfold`,
`lock_adequate_ghost'` `lockAdequateGhost'`, `lock_disc_generic` `lockDiscGeneric`,
`lockN_sound` `lockNSound`, `lock3s_Hscope` `lock3sHscope`, `race_pol` `AxLockN.racePol`,
`race_lob_succ_wx` `raceLobSuccWx`, `race_spol_wx` `raceSpolWx`, `race_spol_wc` `raceSpolWc`,
`L2r` `AxLockN.l2r`, `L2r_0` `l2r0`, `L2r_1` `l2r1`, `na_r` `naR`, `ea_r` `eaR`, `na_r_wx`
`naRWx`, `na_r_wc` `naRWc`, `ea_r_wx` `eaRWx`, `ea_r_wc` `eaRWc`, `ea_r_wrel` `eaRWrel`,
`AxG_race` `AxLockN.axGRace`, `race_Hxl` `raceHxl`, `race_not_verifiable'`
`raceNotVerifiable'`, `lock3s_pol` `AxLockN.lock3sPol`, `lock3s_wC3s_spol` `lock3sWC3sSpol`,
`lock3s_e_wC3s_succ` `lock3sEWC3sSucc`, `AxGn3_inst` `AxLockN.axGn3Inst`, `lock3s_ea_relC3s`
`lock3sEaRelC3s`, `lockN_premise_refuted_lock3s` `lockNPremiseRefutedLock3s`.

**Dropped:** nothing.
-/
import Weak.AxLockAdeq2
import Weak.AxSchedGD
import Weak.AxLock3
import Weak.AxGraphDec
import Weak.AxToken
import MachCSL.StdppMap
import MachCSL.StdppSet
import MachCSL.StdppList

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. Kind classification and the predecessor functions -/

def AxLockN.isRelL (GD : Gdexec) (L : Int) (e : Geid) : Bool := gwbB GD.gdG e L b0
def AxLockN.isAcqL (GD : Gdexec) (L : Int) (e : Geid) : Bool := gwbB GD.gdG e L b1
def AxLockN.isWx (GD : Gdexec) (x : Int) (e : Geid) : Bool := gwaB GD.gdG e x

def AxLockN.coPred (GD : Gdexec) (e : Geid) : Option Geid :=
  (GD.gdG.gxGmo.filter fun w => gcoB GD.gdG w e).getLast?

def AxLockN.acqBefore (GD : Gdexec) (L : Int) (e : Geid) : Option Geid :=
  (GD.gdG.gxGmo.filter fun w => gpoB GD.gdG w e && AxLockN.isAcqL GD L w).getLast?

def AxLockN.xwPredO (GD : Gdexec) (L : Int) (e : Geid) : Option Geid :=
  match AxLockN.coPred GD e with
  | none => none
  | some w0 =>
    some (match AxLockN.acqBefore GD L e with
          | some a0 => if gmoLtB GD.gdG w0 a0 then a0 else w0
          | none => w0)

def AxLockN.relPredO (GD : Gdexec) (L x : Int) (e : Geid) : Option Geid :=
  (GD.gdG.gxGmo.filter fun w =>
    gpoB GD.gdG w e && (AxLockN.isWx GD x w || AxLockN.isAcqL GD L w)).getLast?

def AxLockN.acqPredO (GD : Gdexec) (e : Geid) : Option Geid := AxLockN.coPred GD e

def AxLockN.optSingleton (o : Option Geid) : GSet Geid :=
  match o with
  | some p => {p}
  | none => ∅

def AxLockN.lockPred (GD : Gdexec) (L x : Int) (e : Geid) : GSet Geid :=
  if AxLockN.isRelL GD L e then AxLockN.optSingleton (AxLockN.relPredO GD L x e)
  else if AxLockN.isAcqL GD L e then AxLockN.optSingleton (AxLockN.acqPredO GD e)
  else if AxLockN.isWx GD x e then AxLockN.optSingleton (AxLockN.xwPredO GD L e)
  else ∅

/-- The policy (Rocq `Instance axlockn_pol`; a reducible def, passed explicitly). -/
@[reducible] def axlocknPol (GD : Gdexec) (L x : Int) : Axpol :=
  ⟨fun _ => AxLockN.lockPred GD L x, fun _ => AxLockN.lockPred GD L x⟩

/-! # 2. The per-kind flow obligation -/

theorem AxLockN.coPredGco (GD : Gdexec) (e w0 : Geid) :
    AxLockN.coPred GD e = some w0 → gco GD.gdG w0 e := by
  intro Hl
  have Hin := List.mem_of_getLast? Hl
  rw [List.mem_filter] at Hin
  exact (gcoBSpec _ _ _).1 Hin.2

theorem AxLockN.acqBeforeGpo (GD : Gdexec) (L : Int) (e a0 : Geid) :
    AxLockN.acqBefore GD L e = some a0 → WeakRvwmoGraph.gpo GD.gdG a0 e := by
  intro Hl
  have Hin := List.mem_of_getLast? Hl
  rw [List.mem_filter, Bool.and_eq_true] at Hin
  exact (gpoBSpec _ _ _).1 Hin.2.1

theorem AxLockN.acqBeforeIsAcqL (GD : Gdexec) (L : Int) (e a0 : Geid) :
    AxLockN.acqBefore GD L e = some a0 → AxLockN.isAcqL GD L a0 = true := by
  intro Hl
  have Hin := List.mem_of_getLast? Hl
  rw [List.mem_filter, Bool.and_eq_true] at Hin
  exact Hin.2.2

theorem AxLockN.gcoSubFlow (GD : Gdexec) (w e : Geid) : gco GD.gdG w e → gobCatFlow GD w e :=
  fun Hco => .single (Or.inr (Or.inr (Or.inr (Or.inl Hco))))

theorem AxLockN.gacqPoSubFlow (GD : Gdexec) (L : Int)
    (HacqRead : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (a0 e : Geid) :
    WeakRvwmoGraph.gpo GD.gdG a0 e → AxLockN.isAcqL GD L a0 = true → gmem GD.gdG e →
    gobCatFlow GD a0 e :=
  fun Hpo Hacq Hmem =>
    .single (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨Hpo, HacqRead a0 Hacq, HacqAq a0 Hacq, Hmem⟩)))))))

theorem axlocknPredSubFlow (GD : Gdexec) (L x : Int) (Hxl : x ≠ L)
    (HrelFence : ∀ e p, AxLockN.isRelL GD L e = true → AxLockN.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (e e' : Geid) :
    e' ∈ AxLockN.lockPred GD L x e → gobCatFlow GD e' e := by
  unfold AxLockN.lockPred
  cases Hrel : AxLockN.isRelL GD L e
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases Hacq : AxLockN.isAcqL GD L e
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases Hwx : AxLockN.isWx GD x e
      · simp only [Bool.false_eq_true, ↓reduceIte]
        intro h; exact absurd h notElemOfEmpty
      · simp only [↓reduceIte]
        unfold AxLockN.optSingleton AxLockN.xwPredO
        cases Hco : AxLockN.coPred GD e with
        | none => intro h; exact absurd h notElemOfEmpty
        | some w0 =>
          have Hmem : gmem GD.gdG e := by
            obtain ⟨v, Hwb⟩ := (gwaBSpec _ _ _).1 Hwx
            exact WeakRvwmoGraph.glblIsWGmem _ _ (gwritesByteGlblW _ _ _ _ Hwb)
          cases Hab : AxLockN.acqBefore GD L e with
          | none =>
            intro h; rw [elemOfSingleton.1 h]
            exact AxLockN.gcoSubFlow GD w0 e (AxLockN.coPredGco GD e w0 Hco)
          | some a0 =>
            cases Hlt : gmoLtB GD.gdG w0 a0
            · intro h
              simp only [Hlt, Bool.false_eq_true, ↓reduceIte] at h
              rw [elemOfSingleton.1 h]
              exact AxLockN.gcoSubFlow GD w0 e (AxLockN.coPredGco GD e w0 Hco)
            · intro h
              simp only [Hlt, ↓reduceIte] at h
              rw [elemOfSingleton.1 h]
              exact AxLockN.gacqPoSubFlow GD L HacqRead HacqAq a0 e
                (AxLockN.acqBeforeGpo GD L e a0 Hab) (AxLockN.acqBeforeIsAcqL GD L e a0 Hab)
                Hmem
    · simp only [↓reduceIte]
      unfold AxLockN.optSingleton AxLockN.acqPredO
      cases Hco : AxLockN.coPred GD e with
      | none => intro h; exact absurd h notElemOfEmpty
      | some w0 =>
        intro h; rw [elemOfSingleton.1 h]
        exact AxLockN.gcoSubFlow GD w0 e (AxLockN.coPredGco GD e w0 Hco)
  · simp only [↓reduceIte]
    unfold AxLockN.optSingleton
    cases Hp : AxLockN.relPredO GD L x e with
    | none => intro h; exact absurd h notElemOfEmpty
    | some p =>
      intro h; rw [elemOfSingleton.1 h]
      exact HrelFence e p Hrel Hp

/-- Restated at the literal `sPol` projection of `axlocknPol`. -/
theorem axlocknPredSubFlowSpol (GD : Gdexec) (L x : Int) (Hxl : x ≠ L)
    (HrelFence : ∀ e p, AxLockN.isRelL GD L e = true → AxLockN.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (e e' : Geid) :
    e' ∈ @Axpol.sPol (axlocknPol GD L x) GD e → gobCatFlow GD e' e :=
  axlocknPredSubFlow GD L x Hxl HrelFence HacqRead HacqAq e e'

/-- Restated at the literal `lobp` projection of `axlocknPol`. -/
theorem axlocknPredSubFlowLobp (GD : Gdexec) (L x : Int) (Hxl : x ≠ L)
    (HrelFence : ∀ e p, AxLockN.isRelL GD L e = true → AxLockN.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (e e' : Geid) :
    e' ∈ @Axpol.lobp (axlocknPol GD L x) GD e → gobCatFlow GD e' e :=
  axlocknPredSubFlow GD L x Hxl HrelFence HacqRead HacqAq e e'

/-! # 3. `xwIsCsWrite` and the scheduler-run permutation fact -/

/-- THE PURE DISCIPLINE `csHandoffLast` needs: `e` lies in some critical section on `L`. -/
def AxLockN.xwIsCsWrite (GD : Gdexec) (L : Int) (e : Geid) : Prop :=
  ∃ acqk relk, lockCs GD.gdG L acqk relk ∧ glblIs GD.gdG acqk lbAq ∧
    WeakRvwmoGraph.gpo GD.gdG acqk e ∧ gppoCat GD e relk

theorem gmoPermOfRun (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅) :
    st.sProc.Perm GD.gdG.gxGmo := by
  have HGw := schedHGwf GD Hcons
  have HC6 := schedHCat6gmo GD Hcons
  obtain ⟨Hmemiff, HndP, _⟩ := schedCorrect GD.gdG HGw HC6 st Hrun Hfull Hdone
  exact NoDup_Permutation HndP HGw.1 Hmemiff

/-! # 4. `naVal'`/`eaVal`/`naOf'`/`eaOf` -/

theorem AxLockN.lgFmapFstPair {A B : Type} (f : A → B) (l : List A) :
    ((l.map fun x => (x, f x)).map Prod.fst) = l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, ih]

theorem AxLockN.lgMapOfFunLookupSome {V : Type} (f : Geid → V) (K : List Geid) (Hnd : K.Nodup)
    (e : Geid) (He : e ∈ K) :
    get? (PartialMap.ofList (K.map fun e0 => (e0, f e0)) : GMapF Geid V) e = some (f e) := by
  apply elemOfListToMap1
  · rw [AxLockN.lgFmapFstPair]; exact Hnd
  · exact List.mem_map.2 ⟨e, He, rfl⟩

theorem AxLockN.lgMapOfFunLookupNone {V : Type} (f : Geid → V) (K : List Geid) (e : Geid)
    (He : e ∉ K) :
    get? (PartialMap.ofList (K.map fun e0 => (e0, f e0)) : GMapF Geid V) e = none := by
  apply notElemOfListToMap.1
  rw [AxLockN.lgFmapFstPair]; exact He

section annot

variable {GF : BundledGFunctors} [AxlogG GF Hent]

/-- `AxLockGen.naVal` with the extra pure conjunct `⌜xwIsCsWrite GD L e⌝` at `isWx`. -/
def AxLockN.naVal' (GD : Gdexec) (L x : Int) (γ : GName) (e : Geid) : IProp GF :=
  if AxLockN.isWx GD x e then
    iprop(∃ (H : List Hent) (v : BitVec 8) (data : List (BitVec 8)),
      tokTie GD γ x H {[e := (1 : Qp)]} ∗ ⌜gwritesByte GD.gdG e x v⌝ ∗
      ⌜graphData GD e = some data⌝ ∗ ⌜AxLockN.xwIsCsWrite GD L e⌝)
  else if AxLockN.isRelL GD L e then
    iprop(∃ (H_L : List Hent), histSnap γ L H_L)
  else iprop(emp)

def AxLockN.eaVal (GD : Gdexec) (L x : Int) (γ : GName) (e : Geid) : Mea GF :=
  if AxLockN.isRelL GD L e then
    match AxLockN.relPredO GD L x e with
    | some p => {[p := iprop(∃ (H : List Hent), tokTie GD γ x H {[e := (1 : Qp)]})]}
    | none => ∅
  else if AxLockN.isAcqL GD L e then
    match AxLockN.acqPredO GD e with
    | some p => {[p := iprop(⌜gwritesByte GD.gdG p L b0⌝ ∗
                  ∃ (H : List Hent), tokTie GD γ x H {[e := (1 : Qp)]})]}
    | none => ∅
  else ∅

def AxLockN.naOf' (GD : Gdexec) (L x : Int) (γ : GName) : Mea GF :=
  PartialMap.ofList (GD.gdG.gxGmo.map fun e => (e, AxLockN.naVal' GD L x γ e))

def AxLockN.eaOf (GD : Gdexec) (L x : Int) (γ : GName) : Sra GF :=
  PartialMap.ofList (GD.gdG.gxGmo.map fun e => (e, AxLockN.eaVal GD L x γ e))

theorem AxLockN.naOf'Dom (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (L x : Int) (γ : GName) :
    (FiniteMap.dom_set (AxLockN.naOf' (GF := GF) GD L x γ) : GSet Geid) =
      LawfulSet.ofList GD.gdG.gxGmo := by
  have Hnd := (schedHGwf GD Hcons).1
  rw [setEq]
  intro e
  rw [elemOfDom, elemOfListToSet]
  constructor
  · intro Hv
    by_cases Hin : e ∈ GD.gdG.gxGmo
    · exact Hin
    · unfold AxLockN.naOf' at Hv
      rw [AxLockN.lgMapOfFunLookupNone _ _ e Hin] at Hv
      exact absurd Hv Bool.false_ne_true
  · intro Hin
    unfold AxLockN.naOf'
    rw [AxLockN.lgMapOfFunLookupSome _ _ Hnd e Hin]
    rfl

theorem AxLockN.eaOfDom (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (L x : Int) (γ : GName) :
    (FiniteMap.dom_set (AxLockN.eaOf (GF := GF) GD L x γ) : GSet Geid) =
      LawfulSet.ofList GD.gdG.gxGmo := by
  have Hnd := (schedHGwf GD Hcons).1
  rw [setEq]
  intro e
  rw [elemOfDom, elemOfListToSet]
  constructor
  · intro Hv
    by_cases Hin : e ∈ GD.gdG.gxGmo
    · exact Hin
    · unfold AxLockN.eaOf at Hv
      rw [AxLockN.lgMapOfFunLookupNone _ _ e Hin] at Hv
      exact absurd Hv Bool.false_ne_true
  · intro Hin
    unfold AxLockN.eaOf
    rw [AxLockN.lgMapOfFunLookupSome _ _ Hnd e Hin]
    rfl

theorem naEaDomEq' (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (L x : Int) (γ : GName) :
    (FiniteMap.dom_set (AxLockN.eaOf (GF := GF) GD L x γ) : GSet Geid) =
      FiniteMap.dom_set (AxLockN.naOf' (GF := GF) GD L x γ) := by
  rw [AxLockN.eaOfDom GD Hcons L x, AxLockN.naOf'Dom GD Hcons L x]

theorem AxLockN.HeaLob0 (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (L x : Int) (Hxl : x ≠ L)
    (HrelFence : ∀ e p, AxLockN.isRelL GD L e = true → AxLockN.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (γ : GName) :
    ∀ e0 gm, get? (AxLockN.eaOf (GF := GF) GD L x γ) e0 = some gm →
      (FiniteMap.dom_set gm : GSet Geid) ⊆ AxLockN.lockPred GD L x e0 := by
  have Hnd := (schedHGwf GD Hcons).1
  intro e0 gm Hea
  by_cases Hin : e0 ∈ GD.gdG.gxGmo
  · unfold AxLockN.eaOf at Hea
    rw [AxLockN.lgMapOfFunLookupSome _ _ Hnd e0 Hin] at Hea
    cases Option.some.inj Hea
    unfold AxLockN.eaVal AxLockN.lockPred
    cases Hrel : AxLockN.isRelL GD L e0
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases Hacq : AxLockN.isAcqL GD L e0
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [domEmpty]; exact emptySubseteq
      · simp only [↓reduceIte]
        unfold AxLockN.optSingleton
        cases AxLockN.acqPredO GD e0 with
        | none => rw [domEmpty]
        | some p => rw [domSingleton]
    · simp only [↓reduceIte]
      unfold AxLockN.optSingleton
      cases AxLockN.relPredO GD L x e0 with
      | none => rw [domEmpty]
      | some p => rw [domSingleton]
  · unfold AxLockN.eaOf at Hea
    rw [AxLockN.lgMapOfFunLookupNone _ _ e0 Hin] at Hea
    cases Hea

/-- Restated at the literal `lobp` projection. -/
theorem AxLockN.HeaLob0Lobp (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (L x : Int)
    (Hxl : x ≠ L)
    (HrelFence : ∀ e p, AxLockN.isRelL GD L e = true → AxLockN.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (γ : GName) :
    ∀ e0 gm, get? (AxLockN.eaOf (GF := GF) GD L x γ) e0 = some gm →
      (FiniteMap.dom_set gm : GSet Geid) ⊆ @Axpol.lobp (axlocknPol GD L x) GD e0 :=
  AxLockN.HeaLob0 GD Hcons L x Hxl HrelFence HacqRead HacqAq γ

end annot

/-! # 5. The fixed concrete instance -/

section fixedInst

variable {GF : BundledGFunctors} [AxlogG GF Hent] [AxLockG GF]

/-- THE CONCRETE `AxirisG` RECORD (Rocq `AxGn_inst`): `obStInterp` IS `protInvLock'`. -/
@[reducible] def AxLockN.axGnInst (L x : Int) (γ γc : GName) : AxirisG GF where
  annotInterp := fun _ => iprop(True)
  gconstInterp := fun _ => iprop(True)
  obSt := GSet Geid × GMapF Geid (List Hent)
  obStInterp := fun GD0 σ s => protInvLock' L x γ γc GD0 s σ.1 σ.2
  logTsT := Unit
  localInterp := fun _ _ _ _ => iprop(True)

theorem axGnObStInterpUnfold (L x : Int) (γ γc : GName) (GD0 : Gdexec)
    (σ : GSet Geid × GMapF Geid (List Hent)) (s : GSet Geid) :
    AxirisG.obStInterp (self := AxLockN.axGnInst (GF := GF) L x γ γc) GD0 σ s ⊣⊢
      protInvLock' L x γ γc GD0 s σ.1 σ.2 :=
  ⟨.rfl, .rfl⟩

/-- Lean-only: the empty `protInvLock'`, from the empty claimed authority. -/
theorem AxLockN.obInitLock (L x : Int) (γ γc : GName) (GD : Gdexec) :
    claimedAuth γc (∅ : GSet Geid) ⊢ protInvLock' (GF := GF) L x γ γc GD ∅ ∅ ∅ := by
  iintro Hc
  iapply (protInvLockUnfold' L x γ γc GD ∅ ∅ ∅).2
  isplitl [Hc]
  · iexact Hc
  isplitl []
  · unfold protInv
    iapply BigSepS.bigSepS_empty.2
    itrivial
  · iapply BigSepS.bigSepS_empty.2
    itrivial

/-- Lean-only: the two initial histories as the `{x} ∪ {L}` big-sep. -/
theorem AxLockN.bytesIntro (x L : Int) (Hxl : x ≠ L) (γ : GName) :
    histAuth (GF := GF) γ x 1 ([] : List Hent) ∗ histAuth γ L 1 ([] : List Hent) ⊢
      [∗set] a ∈ (({x} : GSet Int) ∪ {L}), histAuth (GF := GF) γ a 1 ([] : List Hent) := by
  have hdisj : ({x} : GSet Int) ## {L} := by
    rw [elemOfDisjoint]
    intro y hy hy'
    rw [elemOfSingleton.1 hy] at hy'
    exact Hxl (elemOfSingleton.1 hy')
  iintro ⟨Hx, HL⟩
  iapply (BigSepS.bigSepS_union (Φ := fun a => histAuth (GF := GF) γ a 1 []) hdisj).2
  isplitl [Hx]
  · iapply BigSepS.bigSepS_singleton.2
    iexact Hx
  · iapply BigSepS.bigSepS_singleton.2
    iexact HL

end fixedInst

section adequate

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxlogG GF Hent] [AxLockG GF]

/-- `AxLockGen.lockAdequateGhost` at `naOf'`, at the concrete instance, with the initial
ob-state `(∅, ∅)` built by hand. -/
theorem lockAdequateGhost' (GD : Gdexec) (L x : Int) (Hxl : x ≠ L)
    (Hcons : rvwmoCatConsistent GD)
    (HrelFence : ∀ e p, AxLockN.isRelL GD L e = true → AxLockN.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (γ γc : GName)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (Hdefer : ∀ r, deferredSnapAvail GD st.sEverD r)
    (HflowInit' :
      ([∗set] a ∈ (({x} : GSet Int) ∪ {L}), histAuth (GF := GF) γ a 1 ([] : List Hent)) ⊢
        @ordEaTodoL (axlocknPol GD L x) hlc GF _ (AxLockN.axGnInst L x γ γc) GD
          (AxLockN.eaOf GD L x γ) (AxLockN.naOf' GD L x γ) GD.gdG.gxGmo 0) :
    ⊢ histAuth (GF := GF) γ x 1 ([] : List Hent) -∗ histAuth γ L 1 ([] : List Hent) -∗
      claimedAuth γc (∅ : GSet Geid) -∗
      |={⊤}[∅]▷=>^[st.sProc.length]
        ∃ (σ : GSet Geid × GMapF Geid (List Hent)),
          AxirisG.obStInterp (self := AxLockN.axGnInst L x γ γc) GD σ
            (LawfulSet.ofList st.sProc) ∗
          [∗set] e0 ∈ (LawfulSet.ofList st.sProc : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? (AxLockN.naOf' GD L x γ) e0) := by
  have Hperm := gmoPermOfRun GD Hcons st Hrun Hfull Hdone
  have Htodo : ([∗set] a ∈ (({x} : GSet Int) ∪ {L}), histAuth (GF := GF) γ a 1 []) ⊢
      @ordEaTodoL (axlocknPol GD L x) hlc GF _ (AxLockN.axGnInst L x γ γc) GD
        (AxLockN.eaOf GD L x γ) (AxLockN.naOf' GD L x γ) st.sProc 0 := by
    refine HflowInit'.trans ?_
    unfold ordEaTodoL
    simp only [List.drop_zero]
    exact (BigSepL.bigSepL_perm Hperm.symm).1
  have Hdom : (LawfulSet.ofList st.sProc : GSet Geid) ⊆
      FiniteMap.dom_set (AxLockN.naOf' (GF := GF) GD L x γ) := by
    rw [AxLockN.naOf'Dom GD Hcons L x]
    intro e' He'
    rw [elemOfListToSet] at He' ⊢
    exact Hperm.mem_iff.1 He'
  have Had : ⊢ @ordEaTodoL (axlocknPol GD L x) hlc GF _ (AxLockN.axGnInst L x γ γc) GD
        (AxLockN.eaOf GD L x γ) (AxLockN.naOf' GD L x γ) st.sProc 0 -∗
      AxirisG.obStInterp (self := AxLockN.axGnInst L x γ γc) GD
        ((∅, ∅) : GSet Geid × GMapF Geid (List Hent)) ∅ -∗
      |={⊤}[∅]▷=>^[st.sProc.length]
        ∃ (σ : GSet Geid × GMapF Geid (List Hent)),
          AxirisG.obStInterp (self := AxLockN.axGnInst L x γ γc) GD σ
            (LawfulSet.ofList st.sProc) ∗
          [∗set] e0 ∈ (LawfulSet.ofList st.sProc : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? (AxLockN.naOf' GD L x γ) e0) :=
    @schedProcAdequate hlc GF _ (AxLockN.axGnInst L x γ γc) (axlocknPol GD L x)
      GD Hcons st Hrun Hfull Hdone
      (axlocknPredSubFlowSpol GD L x Hxl HrelFence HacqRead HacqAq)
      (axlocknPredSubFlowLobp GD L x Hxl HrelFence HacqRead HacqAq)
      (AxLockN.naOf' GD L x γ) (AxLockN.eaOf GD L x γ)
      (naEaDomEq' GD Hcons L x γ) Hdom
      (AxLockN.HeaLob0Lobp GD Hcons L x Hxl HrelFence HacqRead HacqAq γ) Hdefer
      ((∅, ∅) : GSet Geid × GMapF Geid (List Hent))
  have Hob0 : claimedAuth γc (∅ : GSet Geid) ⊢
      AxirisG.obStInterp (self := AxLockN.axGnInst (GF := GF) L x γ γc) GD
        ((∅, ∅) : GSet Geid × GMapF Geid (List Hent)) ∅ :=
    AxLockN.obInitLock L x γ γc GD
  iintro Hx HL Hc
  ihave Hb := AxLockN.bytesIntro x L Hxl γ $$ [Hx HL]
  · isplitl [Hx]
    · iexact Hx
    · iexact HL
  ihave Ht := Htodo $$ Hb
  ihave Hob := Hob0 $$ Hc
  iapply Had $$ Ht Hob

end adequate

/-! # 6. `lockDiscGeneric` — the Prop-level extraction -/

section disc

variable {GF : BundledGFunctors} [AxlogG GF Hent]

/-- Lean-only: the final bag entry at an `x`-write yields the discipline fact. -/
theorem AxLockN.naBagCs (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (L x : Int) (γ : GName)
    (w : Geid) (vw : BitVec 8) (Hw : gwritesByte GD.gdG w x vw) :
    AxWp.fromOption (fun P => P) iprop(emp) (get? (AxLockN.naOf' (GF := GF) GD L x γ) w) ⊢
      ⌜AxLockN.xwIsCsWrite GD L w⌝ := by
  have Hnd := (schedHGwf GD Hcons).1
  have HinGmo : w ∈ GD.gdG.gxGmo := gwritesByteGmo _ _ _ _ (schedHGwf GD Hcons) Hw
  have Hisx : AxLockN.isWx GD x w = true := (gwaBSpec _ _ _).2 ⟨vw, Hw⟩
  unfold AxLockN.naOf'
  rw [AxLockN.lgMapOfFunLookupSome _ _ Hnd w HinGmo]
  simp only [AxWp.fromOption]
  unfold AxLockN.naVal'
  rw [if_pos Hisx]
  iintro ⟨%H, %v, %data, -, -, -, %Hcs⟩
  ipureintro
  exact Hcs

end disc

theorem lockDiscGeneric {GF : BundledGFunctors} [InvGpreS GF] [AxlogG GF Hent] [AxLockG GF]
    (GD : Gdexec) (L x : Int) (Hxl : x ≠ L) (Hcons : rvwmoCatConsistent GD)
    (HrelFence : ∀ e p, AxLockN.isRelL GD L e = true → AxLockN.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (Hdefer : ∀ r, deferredSnapAvail GD st.sEverD r)
    (HflowInit' : ∀ (Hinv : InvGS_gen .hasNoLC GF) (γ γc : GName),
      ([∗set] a ∈ (({x} : GSet Int) ∪ {L}), histAuth (GF := GF) γ a 1 ([] : List Hent)) ⊢
        @ordEaTodoL (axlocknPol GD L x) .hasNoLC GF Hinv (AxLockN.axGnInst L x γ γc) GD
          (AxLockN.eaOf GD L x γ) (AxLockN.naOf' GD L x γ) GD.gdG.gxGmo 0)
    (w : Geid) (vw : BitVec 8) :
    gwritesByte GD.gdG w x vw → AxLockN.xwIsCsWrite GD L w := by
  intro Hw
  have Hperm := gmoPermOfRun GD Hcons st Hrun Hfull Hdone
  have HinGmo : w ∈ GD.gdG.gxGmo := gwritesByteGmo _ _ _ _ (schedHGwf GD Hcons) Hw
  have HinProc : w ∈ st.sProc := Hperm.mem_iff.2 HinGmo
  obtain ⟨k, hk⟩ : ∃ k, st.sProc.length = k + 1 := by
    cases h : st.sProc with
    | nil => rw [h] at HinProc; cases HinProc
    | cons a l => exact ⟨l.length, rfl⟩
  have Hin : w ∈ (LawfulSet.ofList st.sProc : GSet Geid) := elemOfListToSet.2 HinProc
  apply Iris.pure_soundness (PROP := IProp GF)
  refine step_fupdN_soundness_close (hlc := HasLC.hasNoLC)
    (P := iprop(⌜AxLockN.xwIsCsWrite GD L w⌝)) (k + 1) 0 ?_
  intro Hinv
  iintro _
  have hs : ∀ (P : IProp GF),
      iprop(|={⊤}[∅]▷=>^[k + 1] P) = iprop(|={⊤}[∅]▷=> |={⊤}[∅]▷=>^[k] P) := fun _ => rfl
  rw [hs]
  imod lockInitialAlloc (GF := GF) x L Hxl with ⟨%γ, %γc, Hx, HL, Hc⟩
  rw [← hs]
  have Hfinal := lockAdequateGhost' (hlc := .hasNoLC) GD L x Hxl Hcons HrelFence HacqRead
    HacqAq γ γc st Hrun Hfull Hdone Hdefer (HflowInit' Hinv γ γc)
  rw [hk] at Hfinal
  ihave Hfin := Hfinal $$ Hx HL Hc
  iapply step_fupdN_wand $$ Hfin
  iintro ⟨%σ, -, Hbag⟩
  ihave Hw' := BigSepS.bigSepS_elem_of (Φ := fun e0 =>
    AxWp.fromOption (fun P => P) iprop(emp) (get? (AxLockN.naOf' (GF := GF) GD L x γ) e0))
    Hin $$ Hbag
  iapply AxLockN.naBagCs GD Hcons L x γ w vw Hw $$ Hw'

/-! # 7. `lockNSound` — VACUOUS (see the header and §10); kept for the record -/

theorem lockNSound {GF : BundledGFunctors} [InvGpreS GF] [AxlogG GF Hent] [AxLockG GF]
    (GD : Gdexec) (L x : Int) (Hxl : x ≠ L) (Hcons : rvwmoCatConsistent GD)
    (HrelFence : ∀ e p, AxLockN.isRelL GD L e = true → AxLockN.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (Hdefer : ∀ r, deferredSnapAvail GD st.sEverD r)
    (HflowInit' : ∀ (Hinv : InvGS_gen .hasNoLC GF) (γ γc : GName),
      ([∗set] a ∈ (({x} : GSet Int) ∪ {L}), histAuth (GF := GF) γ a 1 ([] : List Hent)) ⊢
        @ordEaTodoL (axlocknPol GD L x) .hasNoLC GF Hinv (AxLockN.axGnInst L x γ γc) GD
          (AxLockN.eaOf GD L x γ) (AxLockN.naOf' GD L x γ) GD.gdG.gxGmo 0)
    (acqA relA acqB relB w_x r_x : Geid) (vx v v0 : BitVec 8) (t_B t : Nat)
    (Hpat : lockPattern GD.gdG L) (Hpair : lockPaired GD.gdG L)
    (HcsA : lockCs GD.gdG L acqA relA) (HaqA : glblIs GD.gdG acqA lbAq)
    (Hwx : gwritesByte GD.gdG w_x x vx)
    (Hwx_po : WeakRvwmoGraph.gpo GD.gdG acqA w_x) (Hcov_wx : gppoCat GD w_x relA)
    (HcsB : lockCs GD.gdG L acqB relB) (HaqB : glblIs GD.gdG acqB lbAq)
    (Hharts : acqA.1 ≠ acqB.1)
    (Hrd_acqB : greadsByte GD.gdG acqB L t_B v0)
    (Hsrc_acqB : gwriteAt GD.gdG t_B = some relA)
    (Hacq_po : WeakRvwmoGraph.gpo GD.gdG acqB r_x) (Hrd : greadsByte GD.gdG r_x x t v)
    (Hcov_rx : gppoCat GD r_x relB)
    (Hscope : ∀ w vw, w ≠ w_x → gwritesByte GD.gdG w x vw →
      ∀ acqk relk, lockCs GD.gdG L acqk relk → glblIs GD.gdG acqk lbAq →
        WeakRvwmoGraph.gpo GD.gdG acqk w → gppoCat GD w relk →
        acqk.1 ≠ acqA.1 ∧ acqk.1 ≠ acqB.1) :
    WeakRvwmoAcyc.grf GD.gdG w_x r_x ∧ v = vx := by
  have Hdisc_x : ∀ w vw, gwritesByte GD.gdG w x vw → w = w_x ∨
      (∃ acqk relk, lockCs GD.gdG L acqk relk ∧ glblIs GD.gdG acqk lbAq ∧
        acqk.1 ≠ acqA.1 ∧ acqk.1 ≠ acqB.1 ∧
        WeakRvwmoGraph.gpo GD.gdG acqk w ∧ gppoCat GD w relk) := by
    intro w vw Hw
    by_cases Hne : w = w_x
    · exact Or.inl Hne
    · right
      obtain ⟨acqk, relk, Hcsk, Haqk, Hpok, Hcovk⟩ :=
        lockDiscGeneric GD L x Hxl Hcons HrelFence HacqRead HacqAq st Hrun Hfull Hdone Hdefer
          HflowInit' w vw Hw
      obtain ⟨HneA, HneB⟩ := Hscope w vw Hne Hw acqk relk Hcsk Haqk Hpok Hcovk
      exact ⟨acqk, relk, Hcsk, Haqk, HneA, HneB, Hpok, Hcovk⟩
  exact csHandoffLast GD L x acqA relA acqB relB w_x r_x vx v v0 t_B t
    Hcons Hpat Hpair HcsA HaqA Hwx Hwx_po Hcov_wx HcsB HaqB Hharts
    Hrd_acqB Hsrc_acqB Hacq_po Hrd Hcov_rx Hdisc_x

/-! # 8. CERTIFICATE (a): `lockNSound`'s `Hscope` holds for `lock3s`

`AxLock3.hdiscX3s` already supplies `csHandoffLast`'s full `Hdisc_x` directly; this shows the
`Hscope` decomposition is also available.  What remains of `HflowInit'` for `lock3s` is the
Iris-level construction (and a completed scheduler run), out of scope as in Rocq. -/

theorem lock3sHscope :
    ∀ w vw, w ≠ eWxA3s → gwritesByte lock3s.gdG w x3 vw →
      ∀ acqk relk, lockCs lock3s.gdG AxLock3.l3 acqk relk →
        glblIs lock3s.gdG acqk lbAq →
        WeakRvwmoGraph.gpo lock3s.gdG acqk w → gppoCat lock3s w relk →
        acqk.1 ≠ eAcqA3s.1 ∧ acqk.1 ≠ eAcqB3s.1 := by
  intro w vw Hne Hw acqk relk _ _ Hpok _
  rcases hwonlyX3s w vw Hw with h | h
  · subst h
    obtain ⟨Hag, -⟩ := Hpok
    rw [Hag]
    exact ⟨by decide, by decide⟩
  · exact (Hne h).elim

/-! # 9. CERTIFICATE (b): `raceNotVerifiable'` — the premise fails for `AxLockRace.race` at the
concrete `protInvLock'`-based instance

SANITY CHECK (recorded, not restated — Rocq's convention): replacing `naR`'s `wCR` entry by
`emp` leaves step 2 with no `histAuth` to collide, and only the last step breaks. -/

/-- Rocq `Local Instance race_pol` (a reducible def, passed explicitly). -/
@[reducible] def AxLockN.racePol : Axpol :=
  ⟨fun _ e => if e = wRelR then {wXR} else ∅, fun _ e => if e = wRelR then {wXR} else ∅⟩

theorem raceLobSuccWx : wRelR ∈ @lobSuccOf AxLockN.racePol race wXR := by
  refine (@elemOfLobSuccOf AxLockN.racePol race wXR wRelR).2 ⟨?_, ?_⟩
  · show wXR ∈ (if wRelR = wRelR then ({wXR} : GSet Geid) else ∅)
    rw [if_pos rfl]
    exact elemOfSingleton.2 rfl
  · decide +kernel

theorem raceSpolWx : @Axpol.sPol AxLockN.racePol race wXR ⊆ (∅ : GSet Geid) := by
  show (if wXR = wRelR then ({wXR} : GSet Geid) else ∅) ⊆ ∅
  rw [if_neg (by decide)]

theorem raceSpolWc : @Axpol.sPol AxLockN.racePol race wCR ⊆ (∅ : GSet Geid) := by
  show (if wCR = wRelR then ({wXR} : GSet Geid) else ∅) ⊆ ∅
  rw [if_neg (by decide)]

def AxLockN.l2r : List Geid := [wXR, wCR]

theorem l2r0 : AxLockN.l2r[0]? = some wXR := rfl
theorem l2r1 : AxLockN.l2r[1]? = some wCR := rfl

section raceFixed

variable {GF : BundledGFunctors} [AxlogG GF Hent] [AxLockG GF]

def naR (γ : GName) : Mea GF :=
  insert (insert (∅ : Mea GF) wCR iprop(∃ Hl_c : List Hent, histAuth γ AxLockRace.xr 1 Hl_c))
    wXR iprop(emp)

def eaR (γ : GName) : Sra GF :=
  insert
    (insert
      (insert (∅ : Sra GF) wRelR
        (insert (∅ : Mea GF) wXR
          (tokTie race γ AxLockRace.xr [(wXR, b1)] {[wXR := (1 : Qp)]})))
      wCR (∅ : Mea GF))
    wXR (∅ : Mea GF)

theorem AxLockN.neXC : wXR ≠ wCR := by decide
theorem AxLockN.neXRel : wXR ≠ wRelR := by decide
theorem AxLockN.neCRel : wCR ≠ wRelR := by decide

theorem naRWx (γ : GName) : get? (naR (GF := GF) γ) wXR = some iprop(emp) := by
  unfold naR; exact lookupInsert

theorem naRWc (γ : GName) :
    get? (naR (GF := GF) γ) wCR =
      some iprop(∃ Hl_c : List Hent, histAuth γ AxLockRace.xr 1 Hl_c) := by
  unfold naR; rw [lookupInsertNe AxLockN.neXC]; exact lookupInsert

theorem eaRWx (γ : GName) : get? (eaR (GF := GF) γ) wXR = some (∅ : Mea GF) := by
  unfold eaR; exact lookupInsert

theorem eaRWc (γ : GName) : get? (eaR (GF := GF) γ) wCR = some (∅ : Mea GF) := by
  unfold eaR; rw [lookupInsertNe AxLockN.neXC]; exact lookupInsert

theorem eaRWrel (γ : GName) :
    get? (eaR (GF := GF) γ) wRelR =
      some (insert (∅ : Mea GF) wXR
        (tokTie race γ AxLockRace.xr [(wXR, b1)] {[wXR := (1 : Qp)]})) := by
  unfold eaR; rw [lookupInsertNe AxLockN.neXRel, lookupInsertNe AxLockN.neCRel]
  exact lookupInsert

/-- Rocq `AxG_race`: `obStInterp` is `protInvLock' lr xr γ γc race s ∅ ∅`. -/
@[reducible] def AxLockN.axGRace (γ γc : GName) : AxirisG GF where
  annotInterp := fun _ => iprop(True)
  gconstInterp := fun _ => iprop(True)
  obSt := Unit
  obStInterp := fun _ _ s => protInvLock' lr AxLockRace.xr γ γc race s ∅ ∅
  logTsT := Unit
  localInterp := fun _ _ _ _ => iprop(True)

theorem raceHxl : AxLockRace.xr ≠ lr := by decide

/-- THE CERTIFICATE: the 2-slot program does NOT verify at the concrete `protInvLock'`-based
instance, for ANY invariant world. -/
theorem raceNotVerifiable' [InvGpreS GF]
    (Hverif : ∀ (Hinv : InvGS_gen .hasNoLC GF) (γ γc : GName),
      histAuth (GF := GF) γ AxLockRace.xr 1 ([] : List Hent) ⊢
        @ordEaTodoL AxLockN.racePol .hasNoLC GF Hinv (AxLockN.axGRace γ γc) race
          (eaR γ) (naR γ) AxLockN.l2r 0) :
    False := by
  apply Iris.pure_soundness (PROP := IProp GF)
  refine step_fupdN_soundness_close (hlc := .hasNoLC) 2 0 (fun Hinv => ?_)
  have hsS : ∀ (n : Nat) (P : IProp GF),
      iprop(|={⊤}[∅]▷=>^[n + 1] P) = iprop(|={⊤}[∅]▷=> |={⊤}[∅]▷=>^[n] P) := fun _ _ => rfl
  have hs0 : ∀ (P : IProp GF), iprop(|={⊤}[∅]▷=>^[0] P) = P := fun _ => rfl
  have Hnin_wx : wXR ∉ (∅ : GSet Geid) := notElemOfEmpty
  have Hsub_wc : @Axpol.sPol AxLockN.racePol race wCR ⊆ (({wXR} : GSet Geid) ∪ ∅) :=
    fun y hy => (notElemOfEmpty (raceSpolWc y hy)).elim
  have Hnin_wc : wCR ∉ (({wXR} : GSet Geid) ∪ ∅) := by
    intro h
    rcases elemOfUnion.1 h with h | h
    · exact AxLockN.neXC (elemOfSingleton.1 h).symm
    · exact notElemOfEmpty h
  rw [hsS, hsS, hs0]
  iintro _
  imod lockInitialAlloc (GF := GF) AxLockRace.xr lr raceHxl with ⟨%γ, %γc, Hx, -, Hc⟩
  ihave Htodo := (Hverif Hinv γ γc) $$ Hx
  icases (@ordEaTodoLCons AxLockN.racePol .hasNoLC GF Hinv (AxLockN.axGRace γ γc) race _ _ _ 0
    wXR l2r0).1 $$ Htodo with ⟨Hhd, Htodo⟩
  isimp only [naRWx γ, eaRWx γ, AxWp.fromOption] at Hhd
  iunfold flowEqEa, flowEqDyn at Hhd
  ihave Hob0 := AxLockN.obInitLock lr AxLockRace.xr γ γc race $$ Hc
  ihave Hemp0 := (BigSepM.bigSepM_empty (Φ := fun (_ : Geid) (Rin : IProp GF) => Rin)).2 $$ []
  · itrivial
  imod Hhd $$ %() %(∅ : GSet Geid) %raceSpolWx %Hnin_wx Hob0 Hemp0 with Hstep1
  imodintro
  inext
  imod Hstep1 with ⟨%σ1, Hob1, -, Hdep⟩
  iunfold eaDeposit at Hdep
  icases (BigSepS.bigSepS_delete (Φ := fun eOut =>
    AxLifting.depAt (eaR (GF := GF) γ) wXR eOut) raceLobSuccWx).1 $$ Hdep with ⟨Hpiece, -⟩
  rw [@AxLifting.depAtSomeSome GF (AxLockN.axGRace γ γc) AxLockN.racePol _ wXR wRelR
    _ _ (eaRWrel γ) lookupInsert]
  imodintro
  icases (@ordEaTodoLCons AxLockN.racePol .hasNoLC GF Hinv (AxLockN.axGRace γ γc) race _ _ _ 1
    wCR l2r1).1 $$ Htodo with ⟨Hhd, -⟩
  isimp only [naRWc γ, eaRWc γ, AxWp.fromOption] at Hhd
  iunfold flowEqEa, flowEqDyn at Hhd
  ihave Hemp1 := (BigSepM.bigSepM_empty (Φ := fun (_ : Geid) (Rin : IProp GF) => Rin)).2 $$ []
  · itrivial
  imod Hhd $$ %σ1 %(({wXR} : GSet Geid) ∪ ∅) %Hsub_wc %Hnin_wc Hob1 Hemp1 with Hstep2
  imodintro
  inext
  imod Hstep2 with ⟨%σ2, -, ⟨%Hl_c, Hauth⟩, -⟩
  imodintro
  iexfalso
  iapply ownedWriteExcluded race γ AxLockRace.xr [(wXR, b1)] wXR Hl_c
  isplitl [Hpiece]
  · iexact Hpiece
  · iexact Hauth

end raceFixed

/-! # 10. `lockNPremiseRefutedLock3s` — THE MACHINE-CHECKED HONESTY FLAG

`HflowInit'` at `lock3s`/`l3`/`x3` is UNSATISFIABLE: `eWC3s` (the co-first writer of `x3`,
`xwPredO = none`, so its `sPol` is `∅`) must produce both `naVal'`'s full `tokTie … {[eWC3s :=
1]}` and the deposit `eaVal` owes `eRelC3s` (`relPredO eRelC3s = some eWC3s`), a second full
`tokTie … {[eRelC3s := 1]}`; `ownedWriteExcluded` refutes them. -/

/-- Rocq `Local Instance lock3s_pol`. -/
@[reducible] def AxLockN.lock3sPol : Axpol := axlocknPol lock3s AxLock3.l3 x3

theorem lock3sWC3sSpol : @Axpol.sPol AxLockN.lock3sPol lock3s eWC3s = ∅ := by
  have h1 : AxLockN.isRelL lock3s AxLock3.l3 eWC3s = false := by decide +kernel
  have h2 : AxLockN.isAcqL lock3s AxLock3.l3 eWC3s = false := by decide +kernel
  have h3 : AxLockN.isWx lock3s x3 eWC3s = true := by decide +kernel
  have h4 : AxLockN.xwPredO lock3s AxLock3.l3 eWC3s = none := by decide +kernel
  show AxLockN.lockPred lock3s AxLock3.l3 x3 eWC3s = ∅
  unfold AxLockN.lockPred
  simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte]
  rw [h4]
  rfl

theorem AxLockN.lock3sRelC3s : AxLockN.isRelL lock3s AxLock3.l3 eRelC3s = true := by
  decide +kernel

theorem AxLockN.lock3sRelPredC3s : AxLockN.relPredO lock3s AxLock3.l3 x3 eRelC3s = some eWC3s := by
  decide +kernel

theorem lock3sEWC3sSucc : eRelC3s ∈ @lobSuccOf AxLockN.lock3sPol lock3s eWC3s := by
  refine (@elemOfLobSuccOf AxLockN.lock3sPol lock3s eWC3s eRelC3s).2 ⟨?_, ?_⟩
  · show eWC3s ∈ AxLockN.lockPred lock3s AxLock3.l3 x3 eRelC3s
    unfold AxLockN.lockPred
    rw [if_pos AxLockN.lock3sRelC3s, AxLockN.lock3sRelPredC3s]
    exact elemOfSingleton.2 rfl
  · decide +kernel

section lock3Refuted

variable {GF : BundledGFunctors} [AxlogG GF Hent] [AxLockG GF]

/-- Rocq `AxGn3_inst` (= `AxLockN.axGnInst` at `l3`/`x3`). -/
@[reducible] def AxLockN.axGn3Inst (γ γc : GName) : AxirisG GF where
  annotInterp := fun _ => iprop(True)
  gconstInterp := fun _ => iprop(True)
  obSt := GSet Geid × GMapF Geid (List Hent)
  obStInterp := fun GD0 σ s => protInvLock' AxLock3.l3 x3 γ γc GD0 s σ.1 σ.2
  logTsT := Unit
  localInterp := fun _ _ _ _ => iprop(True)

theorem lock3sEaRelC3s (γ : GName) :
    AxLockN.eaVal (GF := GF) lock3s AxLock3.l3 x3 γ eRelC3s =
      {[eWC3s := iprop(∃ (H : List Hent), tokTie lock3s γ x3 H {[eRelC3s := (1 : Qp)]})]} := by
  unfold AxLockN.eaVal
  rw [if_pos AxLockN.lock3sRelC3s, AxLockN.lock3sRelPredC3s]

theorem lockNPremiseRefutedLock3s [InvGpreS GF]
    (HflowInit' : ∀ (Hinv : InvGS_gen .hasNoLC GF) (γ γc : GName),
      ([∗set] a ∈ (({x3} : GSet Int) ∪ {AxLock3.l3}),
          histAuth (GF := GF) γ a 1 ([] : List Hent)) ⊢
        @ordEaTodoL AxLockN.lock3sPol .hasNoLC GF Hinv (AxLockN.axGn3Inst γ γc) lock3s
          (AxLockN.eaOf lock3s AxLock3.l3 x3 γ) (AxLockN.naOf' lock3s AxLock3.l3 x3 γ)
          lock3s.gdG.gxGmo 0) :
    False := by
  apply Iris.pure_soundness (PROP := IProp GF)
  refine step_fupdN_soundness_close (hlc := .hasNoLC) 1 0 (fun Hinv => ?_)
  have hsS : ∀ (n : Nat) (P : IProp GF),
      iprop(|={⊤}[∅]▷=>^[n + 1] P) = iprop(|={⊤}[∅]▷=> |={⊤}[∅]▷=>^[n] P) := fun _ _ => rfl
  have hs0 : ∀ (P : IProp GF), iprop(|={⊤}[∅]▷=>^[0] P) = P := fun _ => rfl
  have Hnd := (schedHGwf lock3s lock3sCat).1
  have Hlk0 : lock3s.gdG.gxGmo[0]? = some eAcqC3s := by decide +kernel
  have Hlk1 : lock3s.gdG.gxGmo[1]? = some eWC3s := by decide +kernel
  have HinWC : eWC3s ∈ lock3s.gdG.gxGmo := by decide +kernel
  have HinRelC : eRelC3s ∈ lock3s.gdG.gxGmo := by decide +kernel
  have Hwx : AxLockN.isWx lock3s x3 eWC3s = true := by decide +kernel
  have h1 : AxLockN.isRelL lock3s AxLock3.l3 eWC3s = false := by decide +kernel
  have h2 : AxLockN.isAcqL lock3s AxLock3.l3 eWC3s = false := by decide +kernel
  have Hsub : @Axpol.sPol AxLockN.lock3sPol lock3s eWC3s ⊆ (∅ : GSet Geid) := by
    rw [lock3sWC3sSpol]
  have Hnin : eWC3s ∉ (∅ : GSet Geid) := notElemOfEmpty
  rw [hsS, hs0]
  iintro _
  imod lockInitialAlloc (GF := GF) x3 AxLock3.l3 hxl3 with ⟨%γ, %γc, Hx, HL, Hc⟩
  have Hna : get? (AxLockN.naOf' (GF := GF) lock3s AxLock3.l3 x3 γ) eWC3s =
      some (AxLockN.naVal' lock3s AxLock3.l3 x3 γ eWC3s) := by
    unfold AxLockN.naOf'; exact AxLockN.lgMapOfFunLookupSome _ _ Hnd _ HinWC
  have Hea : get? (AxLockN.eaOf (GF := GF) lock3s AxLock3.l3 x3 γ) eWC3s = some ∅ := by
    unfold AxLockN.eaOf
    rw [AxLockN.lgMapOfFunLookupSome _ _ Hnd _ HinWC]
    unfold AxLockN.eaVal
    simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
  have HeaRel : get? (AxLockN.eaOf (GF := GF) lock3s AxLock3.l3 x3 γ) eRelC3s =
      some {[eWC3s := iprop(∃ (H : List Hent), tokTie lock3s γ x3 H {[eRelC3s := (1 : Qp)]})]} := by
    unfold AxLockN.eaOf
    rw [AxLockN.lgMapOfFunLookupSome _ _ Hnd _ HinRelC, lock3sEaRelC3s]
  ihave Hbytes := AxLockN.bytesIntro x3 AxLock3.l3 hxl3 γ $$ [Hx HL]
  · isplitl [Hx]
    · iexact Hx
    · iexact HL
  ihave Htodo0 := (HflowInit' Hinv γ γc) $$ Hbytes
  icases (@ordEaTodoLCons AxLockN.lock3sPol .hasNoLC GF Hinv (AxLockN.axGn3Inst γ γc) lock3s
    _ _ _ 0 eAcqC3s Hlk0).1 $$ Htodo0 with ⟨-, Htodo1⟩
  icases (@ordEaTodoLCons AxLockN.lock3sPol .hasNoLC GF Hinv (AxLockN.axGn3Inst γ γc) lock3s
    _ _ _ 1 eWC3s Hlk1).1 $$ Htodo1 with ⟨Hhd, -⟩
  isimp only [Hna, Hea, AxWp.fromOption] at Hhd
  iunfold flowEqEa, flowEqDyn at Hhd
  ihave Hob0 := AxLockN.obInitLock AxLock3.l3 x3 γ γc lock3s $$ Hc
  ihave Hemp0 := (BigSepM.bigSepM_empty (Φ := fun (_ : Geid) (Rin : IProp GF) => Rin)).2 $$ []
  · itrivial
  imod Hhd $$ %((∅, ∅) : GSet Geid × GMapF Geid (List Hent)) %(∅ : GSet Geid) %Hsub %Hnin
    Hob0 Hemp0 with Hstep
  imodintro
  inext
  imod Hstep with ⟨%σ1, -, Hna_wC, Hdep⟩
  iunfold AxLockN.naVal' at Hna_wC
  isimp only [Hwx, ↓reduceIte] at Hna_wC
  icases Hna_wC with ⟨%H1, %v, %data, Htie_wC, -⟩
  iunfold eaDeposit at Hdep
  icases (BigSepS.bigSepS_delete (Φ := fun eOut =>
    AxLifting.depAt (AxLockN.eaOf (GF := GF) lock3s AxLock3.l3 x3 γ) eWC3s eOut)
    lock3sEWC3sSucc).1 $$ Hdep with ⟨Hpiece, -⟩
  rw [@AxLifting.depAtSomeSome GF (AxLockN.axGn3Inst γ γc) AxLockN.lock3sPol _ eWC3s
    eRelC3s _ _ HeaRel lookupSingleton]
  icases Hpiece with ⟨%H2, Htie2⟩
  ihave Htok2 := tokTieTok lock3s γ x3 H2 _ $$ Htie2
  ihave Hauth2 := (tokSingleton γ x3 H2 eRelC3s 1).1 $$ Htok2
  imodintro
  iexfalso
  iapply ownedWriteExcluded lock3s γ x3 H1 eWC3s H2
  isplitl [Htie_wC]
  · iexact Htie_wC
  · iexact Hauth2

end lock3Refuted

end Weak
