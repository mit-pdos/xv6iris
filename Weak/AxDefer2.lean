/-
Weak: **constraint F, concrete** — a DEFERRED read on a consistent MP+fence+ctrl graph
`gdefer`; the three certificates of `AxDefer`'s header items (C)-(E) (AxSL tier).

Rocq: `iris/AxDefer2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

THE GRAPH (`gdefer`, addresses x=0, f=1, y=2; all-zero image `vimg`):
  hart 1:  (1,0) sd x 1 (plain) ; (1,1) fence rw,w ; (1,2) sd.rl-class f 1
  hart 0:  (0,0) r := ld f → 1 (from (1,2))
           -- bnez r (a ctrl GATE on a PLAIN load) --
           (0,1) d := ld x → 0 (the INITIAL value: stale)
           (0,2) sd y 1 (after the branch: ctrl dep (0,0)→(0,2))
  gmo = [d; Wx; Wf; r; w] — d is gmo-BEFORE its gate's source r (RVWMO does not order R→R
  across a ctrl dependency).  Consistent (`gdeferCat`).  The classic MP+fence+ctrl weak
  outcome: r sees the flag, d still sees stale data.

§2 NEGATIVE (item D): `naiveGatedStmt` = `adequacyOrdG` with `L := gxGmo` and `gsrcBefore`
   replaced by a REAL ctrl gate (`gateReal`) and gmo-bounded handouts (here the full gmo
   prefix, K1-ledger).  `naiveGatedRefuted : ¬ naiveGatedStmt`: at a 3-line instance every
   premise is proved on `gdefer` and the conclusion — "r's flag implies d's data is fresh" —
   is FALSE.  `gdeferNoLedgerOrder`: with the ledger's policy no processing order satisfies
   `adequacyOrdG`'s premises either.
§3 POSITIVE (item C/4): `gdeferAdequate` — `adequacyOrdG` APPLIED on `gdefer` with the
   deferral-safe policy `PSafe` over `Lproc = [Wx; Wf; r; d; w]` (d deferred past r), closed by
   soundness.  A satisfiability certificate (premises jointly satisfiable WITH a deferred read).
§4 LEDGER (item E): `ledgerHistOkL` (a ledger history walked in an arbitrary processing
   order); `ledgerLOkGdefer` (in `Lproc` order `gdefer` HAS a legal ledger);
   `ledgerGmoNoneGdefer` (in gmo order NO legal ledger exists).

**Fetches (Stage C).** `gdefer` has no fetch row (only 1-byte data loads/stores).

## Deviations from Rocq

1. Vocabulary as `AxDefer` deviation 1 (`list_to_set` ↦ `LawfulSet.ofList`, `dom` ↦
   `FiniteMap.dom_set`, `list_to_map` ↦ `PartialMap.ofList`, `elements` ↦ `FiniteSet.toList`,
   `forallb` ↦ `List.all`, `≡ₚ` ↦ `List.Perm`, `vm_compute` ↦ `decide +kernel`,
   `|={⊤}[∅]▷=>^n` ↦ `|={⊤}[∅]▷=>^[n]`, `S k` ↦ `k + 1`, `!!` ↦ `get?`/`[k]?`).
2. Rocq's `Notation`s `r_e d_e w_e wx_e wf_e` are reducible defs `AxDefer2.rE`/`dE`/`wE`/
   `wxE`/`wfE` (opened in this file).
3. Instances: Rocq's `A_ref`/`P_ref`/`A_pos`/`P_safe` + `Local Existing Instances` ↦
   reducible defs `ARef`/`PRef`/`APos`/`PSafe` made `local instance`s in their sections (and
   passed explicitly with `@` elsewhere).  Lean's `AxirisG` has no `ax_text` field (O2
   Stage C).  `ARef`/`APos`/the maps take no `invGS` (unused in Rocq).
4. `refΣ = #[invΣ]` ↦ `refGF`, a 4-slot `BundledGFunctors` (wsat + credits, as `Xv6.xv6GF`'s
   first four slots) with its `InvGpreS` instance; `step_fupdN_soundness_no_lc'` ↦
   `step_fupdN_soundness_close (hlc := .hasNoLC)`, `uPred.pure_soundness` ↦
   `Iris.pure_soundness`.  `posPure`/`posDomEq`/`posDom`/`posLob` are stated for every `GF`
   (Rocq: at `refΣ`).
5. `naiveGatedStmt` binds `invGS_gen HasNoLc Σ` as `[InvGS_gen .hasNoLC GF]`.
6. Lean-only helpers (file-qualified): `AxDefer2.bigSepLIntro` (a big-sep of provable
   conjuncts), `AxDefer2.obRefUnfold`/`obPosUnfold` (the instances' interpretations),
   `AxDefer2.lobSuccEmpty` (both policies have empty `lobp`), `AxDefer2.polSafeGdefer` (the
   safe policy on `gdefer` with the gate sources computed), `AxDefer2.lsingGet0`; the `refGF` instances `AxDefer2.refInvMap`/`refEnabled`/`refDisabled`/`refCredit`/`refInvGpreS`.
7. `OC_x` is a duplicated Rocq name: `AxDefer2.OCX`.

**Rocq → Lean name map.**  `gdefer` `gdefer`, `gdefer_cat` `gdeferCat`, `gdefer_gmo`
`gdeferGmo`, `gdefer_deferred` `gdeferDeferred`, `gsrc_d` `gsrcD`, `gsrc_d_spec` `gsrcDSpec`,
`gate_real` `gateReal`, `gdefer_gate_real` `gdeferGateReal`, `mpc_fresh` `mpcFresh`,
`gdefer_stale` `gdeferStale`, `umap` `umap`, `umap_fst` `umapFst`, `umap_lookup` `umapLookup`,
`umap_dom` `umapDom`, `gmo_prefix_lt` `gmoPrefixLt`, `naive_gated_stmt` `naiveGatedStmt`,
`A_ref` `ARef`, `P_ref` `PRef`, `Rref` `Rref`, `na_ref` `naRef`, `ea_ref` `eaRef`, `φ_ref`
`φRef`, `gdefer_nd` `gdeferNd`, `ref_fe` `refFe`, `ref_todo` `refTodo`, `refΣ` `refGF`,
`naive_gated_refuted` `naiveGatedRefuted`, `gdefer_no_ledger_order` `gdeferNoLedgerOrder`,
`pol_safe_s` `polSafeS`, `P_safe` `PSafe`, `Lproc` `Lproc`, `Lproc_perm` `LprocPerm`,
`Lproc_before` `LprocBefore`, `Lproc_pol` `LprocPol`, `Pr` `Pr`, `gdefer_Pr` `gdeferPr`,
`A_pos` `APos`, `Rpos` `Rpos`, `na_pos` `naPos`, `ea_pos` `eaPos`, `φ_pos` `φPos`, `pos_fe`
`posFe`, `pos_todo` `posTodo`, `pos_pure` `posPure`, `pos_dom_eq` `posDomEq`, `pos_dom`
`posDom`, `pos_lob` `posLob`, `gdefer_adequate` `gdeferAdequate`, `ledger_hist_ok_L`
`ledgerHistOkL`, `ledger_hist_ok_L_gmo` `ledgerHistOkLGmo`, `OC_x` `AxDefer2.OCX`, `lsing`
`lsing`, `LHp` `LHp`, `no_acc` `noAcc`, `ledger_L_ok_gdefer` `ledgerLOkGdefer`,
`ledger_gmo_none_gdefer` `ledgerGmoNoneGdefer`.

**Dropped:** only the `Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxDefer
import Weak.AxTokLedger

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp COFE
open Lbl

/-! # 1. THE GRAPH -/

def gdefer : Gdexec :=
  ⟨⟨vimg, [[LLoad false 1 [2] [b1],
            LLoad false 0 [0] [b0],
            LStore false 2 [b1] .WCplain],
           [LStore false 0 [b1] .WCplain,
            LFence true true false true,
            LStore false 1 [b1] .WCrel]],
    [(0, 1), (1, 0), (1, 2), (0, 0), (0, 2)]⟩,
   [((0, 0), (0, 2))], []⟩

@[reducible] def AxDefer2.rE : Geid := (0, 0)
@[reducible] def AxDefer2.dE : Geid := (0, 1)
@[reducible] def AxDefer2.wE : Geid := (0, 2)
@[reducible] def AxDefer2.wxE : Geid := (1, 0)
@[reducible] def AxDefer2.wfE : Geid := (1, 2)

open AxDefer2

theorem gdeferCat : rvwmoCatConsistent gdefer :=
  catConsistentBSound _ (by decide +kernel)

theorem gdeferGmo : gdefer.gdG.gxGmo = [dE, wxE, wfE, rE, wE] := rfl

/-- d is gmo-before its gate's source r: a DEFERRED read. -/
theorem gdeferDeferred : gmoLt gdefer.gdG dE rE :=
  (gmoLtBSpec _ _ _).1 (by decide +kernel)

/-- The gate: the branch on r gates d and w. -/
def gsrcD (e : Geid) : GSet Geid :=
  if e = dE ∨ e = wE then {rE} else ∅

theorem gsrcDSpec (e r : Geid) : r ∈ gsrcD e ↔ (e = dE ∨ e = wE) ∧ r = rE := by
  unfold gsrcD
  by_cases h : e = dE ∨ e = wE
  · rw [if_pos h, elemOfSingleton]
    exact ⟨fun hr => ⟨h, hr⟩, fun hr => hr.2⟩
  · rw [if_neg h]
    exact ⟨fun hr => absurd hr notElemOfEmpty, fun hr => absurd hr.1 h⟩

/-- A REAL ctrl gate: sources are po-earlier reads, and every gated WRITE carries the ctrl
dependency edge (riscv.cat rule 11). -/
def gateReal (GD : Gdexec) (gsrc : Geid → GSet Geid) : Prop :=
  ∀ e r, r ∈ gsrc e →
    WeakRvwmoGraph.gpo GD.gdG r e ∧ glblIs GD.gdG r lbIsR ∧
    (glblIs GD.gdG e lbIsW → gdepsRel GD r e)

theorem gdeferGateReal : gateReal gdefer gsrcD := by
  intro e r hr
  obtain ⟨He, rfl⟩ := (gsrcDSpec e r).1 hr
  rcases He with rfl | rfl
  · refine ⟨⟨rfl, by decide, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ?_⟩
    rintro ⟨l, hl, hw⟩
    cases hl
    exact absurd hw (by decide)
  · refine ⟨⟨rfl, by decide, rfl, rfl⟩, ⟨_, rfl, rfl⟩, fun _ => ?_⟩
    unfold gdepsRel
    decide

/-- "The data read returned 1" — the MP guarantee ctrl does NOT give. -/
def mpcFresh (GD : Gdexec) : Prop := ∃ t, greadsByte GD.gdG dE 0 t b1

theorem gdeferStale : ¬ mpcFresh gdefer := by
  rintro ⟨t, l, base, ts, vs, j, hl, hrd, _, hv, _⟩
  cases hl
  cases hrd
  rcases j with _ | j
  · exact absurd (Option.some.inj hv) (by decide)
  · cases hv

/-- Uniform maps over the gmo events. -/
def umap {V : Type _} (f : Geid → V) (l : List Geid) : GMapF Geid V :=
  PartialMap.ofList (l.map fun e => (e, f e))

theorem umapFst {V : Type _} (f : Geid → V) (l : List Geid) :
    (l.map fun e => (e, f e)).map Prod.fst = l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons]; rw [ih]

theorem umapLookup {V : Type _} (f : Geid → V) (l : List Geid) (e : Geid) :
    l.Nodup → e ∈ l → get? (umap f l) e = some (f e) := by
  intro hnd he
  apply elemOfListToMap1
  · rw [umapFst]; exact hnd
  · exact List.mem_map.2 ⟨e, he, rfl⟩

theorem umapDom {V : Type _} (f : Geid → V) (l : List Geid) :
    (FiniteMap.dom_set (umap f l) : GSet Geid) = LawfulSet.ofList l := by
  unfold umap
  rw [domListToMap, umapFst]

theorem gmoPrefixLt (G : Gexec) (Hwf : gwf G) (e e' : Geid) :
    e' ∈ gmoPrefix G e → gmoLt G e' e := by
  intro hin
  by_cases he : e ∈ G.gxGmo
  · exact (gmoPrefixSpec G e e' Hwf he).1 hin
  · exfalso
    have h0 : gpos G e = 0 := by
      unfold gpos
      cases hf : listFind (fun e' => decide (e' = e)) G.gxGmo with
      | none => rfl
      | some q =>
        obtain ⟨i, x⟩ := q
        obtain ⟨hi, hx, _⟩ := list_find_Some.1 hf
        have : x = e := of_decide_eq_true hx
        subst this
        exact absurd (elem_of_list_lookup_2 hi) he
    unfold gmoPrefix at hin
    rw [h0, List.take_zero] at hin
    cases hin

/-- Lean-only: a big separating conjunction of provable conjuncts. -/
theorem AxDefer2.bigSepLIntro {GF : BundledGFunctors} (Φ : Geid → IProp GF) :
    ∀ l : List Geid, (∀ x, x ∈ l → ⊢ Φ x) → ⊢ [∗list] x ∈ l, Φ x
  | [], _ => BigSepL.bigSepL_nil.2
  | x :: l, h =>
    (emp_sep.2.trans (sep_mono (h x List.mem_cons_self)
      (AxDefer2.bigSepLIntro Φ l fun y hy => h y (List.mem_cons_of_mem _ hy)))).trans
      (BigSepL.bigSepL_cons (Φ := fun _ y => Φ y)).2

/-- Lean-only: with an empty `lobp`, no event has a lob′-successor. -/
theorem AxDefer2.lobSuccEmpty [Axpol] (GD : Gdexec) (Hlob : ∀ e, Axpol.lobp GD e = ∅)
    (e eOut : Geid) : eOut ∉ lobSuccOf GD e := by
  intro h
  have h1 := ((elemOfLobSuccOf GD e eOut).1 h).1
  rw [Hlob] at h1
  exact notElemOfEmpty h1

/-! # 2. NEGATIVE: gated phase 2 in gmo order with gmo-bounded handouts -/

def naiveGatedStmt : Prop :=
  ∀ (GF : BundledGFunctors) [InvGS_gen .hasNoLC GF] [AxirisG GF] [Axpol]
    (GD : Gdexec) (gsrc : Geid → GSet Geid) (φ : Geid → Prop)
    (na : Mea GF) (ea : Sra GF) (σ0 : AxirisG.obSt GF),
    rvwmoCatConsistent GD →
    (∀ e e', e' ∈ Axpol.sPol GD e → gmoLt GD.gdG e' e) →
    (∀ e e', e' ∈ Axpol.lobp GD e → gmoLt GD.gdG e' e) →
    gateReal GD gsrc →
    gateSrcPure na gsrc φ →
    (FiniteMap.dom_set ea : GSet Geid) = FiniteMap.dom_set na →
    (LawfulSet.ofList GD.gdG.gxGmo : GSet Geid) ⊆ FiniteMap.dom_set na →
    (∀ e0 gm, get? ea e0 = some gm → (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0) →
    (iprop(ordEaTodoG (hlc := .hasNoLC) GD gsrc φ ea na GD.gdG.gxGmo 0 ∗
        AxirisG.obStInterp GD σ0 ∅) ⊢
      iprop(|={⊤}[∅]▷=>^[GD.gdG.gxGmo.length]
        ⌜∀ e, e ∈ GD.gdG.gxGmo → gateOk gsrc φ e⌝))

/-- The instance: "once d is validated, the data read was fresh". -/
@[reducible] def ARef {GF : BundledGFunctors} : AxirisG GF where
  annotInterp := fun _ => iprop(True)
  gconstInterp := fun _ => iprop(True)
  obSt := Unit
  obStInterp := fun GD _ s => iprop(⌜dE ∈ s → mpcFresh GD⌝)
  logTsT := Unit
  localInterp := fun _ _ _ _ => iprop(True)

/-- The K1 ledger's policy: the full gmo prefix. -/
@[reducible] def PRef : Axpol where
  sPol := fun GD e => LawfulSet.ofList (gmoPrefix GD.gdG e)
  lobp := fun _ _ => ∅

theorem AxDefer2.obRefUnfold {GF : BundledGFunctors} (GD : Gdexec) (σ : Unit) (s : GSet Geid) :
    AxirisG.obStInterp (self := ARef (GF := GF)) GD σ s ⊣⊢ iprop(⌜dE ∈ s → mpcFresh GD⌝) :=
  ⟨.rfl, .rfl⟩

theorem gdeferNd : gdefer.gdG.gxGmo.Nodup := gdeferCat.1.1

section refute
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF]

attribute [local instance high] ARef PRef

def Rref (e : Geid) : IProp GF := iprop(⌜e = rE → mpcFresh gdefer⌝)
def naRef : Mea GF := umap Rref gdefer.gdG.gxGmo
def eaRef : Sra GF := umap (fun _ => (∅ : Mea GF)) gdefer.gdG.gxGmo
def φRef (_ : Geid) : Prop := mpcFresh gdefer

theorem refFe (e : Geid) :
    ⊢ iprop(⌜gateOk gsrcD φRef e⌝ -∗
      flowEqEa gdefer e (Axpol.sPol gdefer e) (∅ : Mea GF) eaRef (Rref e)) := by
  iintro %Hgate
  unfold flowEqEa flowEqDyn
  iintro %σ %s %Hsub %Hnin Hob _
  icases (AxDefer2.obRefUnfold gdefer σ s).1 $$ Hob with %Hs
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists ()
  isplitl []
  · iapply (AxDefer2.obRefUnfold gdefer () _).2
    ipureintro
    intro Hd
    by_cases hne : e = dE
    · subst hne
      exact Hgate rE ((gsrcDSpec _ _).2 ⟨.inl rfl, rfl⟩)
    · rcases elemOfUnion.1 Hd with h | h
      · exact absurd (elemOfSingleton.1 h).symm hne
      · exact Hs h
  isplitl []
  · unfold Rref
    ipureintro
    intro hr
    subst hr
    apply Hs
    apply Hsub
    show dE ∈ (LawfulSet.ofList (gmoPrefix gdefer.gdG rE) : GSet Geid)
    rw [elemOfListToSet]
    decide
  · iapply (eaDepositEmp (GF := GF) eaRef (lobSuccOf gdefer e) e
      (fun eOut h => absurd h (AxDefer2.lobSuccEmpty gdefer (fun _ => rfl) e eOut)))

theorem refTodo :
    ⊢ ordEaTodoG gdefer gsrcD φRef (eaRef (GF := GF)) naRef gdefer.gdG.gxGmo 0 := by
  unfold ordEaTodoG
  rw [List.drop_zero]
  refine AxDefer2.bigSepLIntro _ _ fun e He => ?_
  rw [naRef, eaRef, umapLookup _ _ e gdeferNd He, umapLookup _ _ e gdeferNd He]
  exact refFe e

end refute

/-! ## `refGF`: the invariant-only functor list (Rocq `refΣ = #[invΣ]`) -/

def refGF : BundledGFunctors :=
  BundledGFunctors.default
  |>.set 0 ⟨InvMapF, inferInstance⟩
  |>.set 1 ⟨constOF CoPsetDisjL, inferInstance⟩
  |>.set 2 ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  |>.set 3 ⟨Auth.AuthURF (constOF Credit), inferInstance⟩

instance AxDefer2.refInvMap : ElemG refGF InvMapF := ⟨0, rfl⟩
instance AxDefer2.refEnabled : ElemG refGF (constOF CoPsetDisjL) := ⟨1, rfl⟩
instance AxDefer2.refDisabled : ElemG refGF (constOF (DisjointLeibnizSet PosSet)) := ⟨2, rfl⟩
instance AxDefer2.refCredit : ElemG refGF (Auth.AuthURF (constOF Credit)) := ⟨3, rfl⟩

instance AxDefer2.refInvGpreS : InvGpreS refGF :=
  ⟨⟨inferInstance, inferInstance, inferInstance⟩, ⟨inferInstance⟩⟩

/-- THE REFUTATION: the naive gated adequacy proves the stale MP+ctrl data read fresh. -/
theorem naiveGatedRefuted : ¬ naiveGatedStmt := by
  intro Hnaive
  apply gdeferStale
  suffices Hall : ∀ e, e ∈ gdefer.gdG.gxGmo → gateOk gsrcD φRef e by
    exact Hall dE (by decide) rE ((gsrcDSpec _ _).2 ⟨.inl rfl, rfl⟩)
  apply Iris.pure_soundness (PROP := IProp refGF)
  refine step_fupdN_soundness_close (hlc := .hasNoLC) gdefer.gdG.gxGmo.length 0
    (fun Hinv => ?_)
  have H := @Hnaive refGF Hinv ARef PRef gdefer gsrcD φRef naRef eaRef () gdeferCat
    (fun e e' he' => gmoPrefixLt _ gdeferCat.1 e e' (elemOfListToSet.1 he'))
    (fun _ _ he' => absurd he' notElemOfEmpty)
    gdeferGateReal
    (fun e r hr => by
      obtain ⟨_, rfl⟩ := (gsrcDSpec e r).1 hr
      refine ⟨Rref rE, umapLookup _ _ _ gdeferNd (by decide), ?_⟩
      exact pure_elim' fun h => pure_intro (h rfl))
    (by rw [eaRef, naRef, umapDom, umapDom])
    (by rw [naRef, umapDom])
    (fun e0 gm hgm => by
      have hm := elemOfListToMap2 hgm
      obtain ⟨x, _, hx⟩ := List.mem_map.1 hm
      cases hx
      intro y hy
      exact absurd hy (by
        rw [domEmpty]
        exact notElemOfEmpty))
  iintro _
  iapply H
  isplitl []
  · iapply (refTodo (hlc := .hasNoLC) (GF := refGF))
  · iapply (AxDefer2.obRefUnfold (GF := refGF) gdefer () ∅).2
    ipureintro
    intro h
    exact absurd h notElemOfEmpty

/-- With the ledger's policy no processing order satisfies `adequacyOrdG`'s two order premises
on `gdefer` either. -/
theorem gdeferNoLedgerOrder (L : List Geid) (Hperm : L.Perm gdefer.gdG.gxGmo) :
    ¬ (gsrcBefore L gsrcD ∧ @axpolWfL PRef gdefer L) :=
  @noOrderPrefixPol PRef gdefer gdeferCat L Hperm gsrcD (fun _ _ _ h => h) dE rE
    ((gsrcDSpec _ _).2 ⟨.inl rfl, rfl⟩) gdeferDeferred

/-! # 3. POSITIVE: `adequacyOrdG` applied, d deferred past r -/

/-- The deferral-safe policy: the gmo prefix MINUS every event some of whose gate sources are
not gmo-before the recipient. -/
def polSafeS (gsrc : Geid → GSet Geid) (GD : Gdexec) (e : Geid) : GSet Geid :=
  LawfulSet.ofList ((gmoPrefix GD.gdG e).filter fun e' =>
    (FiniteSet.toList (gsrc e')).all fun r => gmoLtB GD.gdG r e)

@[reducible] def PSafe : Axpol where
  sPol := polSafeS gsrcD
  lobp := fun _ _ => ∅

def Lproc : List Geid := [wxE, wfE, rE, dE, wE]

theorem LprocPerm : Lproc.Perm gdefer.gdG.gxGmo := by
  rw [gdeferGmo]
  decide

theorem LprocBefore : gsrcBefore Lproc gsrcD := by
  intro n e hn r hr
  obtain ⟨He, rfl⟩ := (gsrcDSpec e r).1 hr
  unfold takeL
  rw [elemOfListToSet]
  rcases n with _ | _ | _ | _ | _ | n
  · cases hn; rcases He with h | h <;> cases h
  · cases hn; rcases He with h | h <;> cases h
  · cases hn; rcases He with h | h <;> cases h
  · cases hn; decide
  · cases hn; decide
  · cases hn

/-- Lean-only: the safe policy on `gdefer`, the gate sources computed. -/
theorem AxDefer2.polSafeGdefer (e : Geid) :
    polSafeS gsrcD gdefer e = LawfulSet.ofList ((gmoPrefix gdefer.gdG e).filter fun e' =>
      !(decide (e' = dE ∨ e' = wE)) || gmoLtB gdefer.gdG rE e) := by
  unfold polSafeS
  congr 1
  apply List.filter_congr
  intro e' _
  rw [Bool.eq_iff_iff, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not]
  constructor
  · intro h
    by_cases hc : e' = dE ∨ e' = wE
    · exact .inr (h rE (elemOfElements.2 ((gsrcDSpec _ _).2 ⟨hc, rfl⟩)))
    · exact .inl hc
  · intro h r hr
    obtain ⟨hc, rfl⟩ := (gsrcDSpec _ _).1 (elemOfElements.1 hr)
    rcases h with h | h
    · exact absurd hc h
    · exact h

theorem LprocPol : @axpolWfL PSafe gdefer Lproc := by
  intro n e hn
  refine ⟨?_, fun _ h => absurd h notElemOfEmpty⟩
  show polSafeS gsrcD gdefer e ⊆ takeL Lproc n
  rw [AxDefer2.polSafeGdefer]
  unfold takeL
  intro x hx
  rw [elemOfListToSet] at hx ⊢
  revert x
  rcases n with _ | _ | _ | _ | _ | n
  · cases hn; decide +kernel
  · cases hn; decide +kernel
  · cases hn; decide +kernel
  · cases hn; decide +kernel
  · cases hn; decide +kernel
  · cases hn

def Pr (GD : Gdexec) : Prop := greadsByte GD.gdG rE 1 2 b1

theorem gdeferPr : Pr gdefer := (grbBSpec _ _ _ _ _).1 (by decide +kernel)

@[reducible] def APos {GF : BundledGFunctors} : AxirisG GF where
  annotInterp := fun _ => iprop(True)
  gconstInterp := fun _ => iprop(True)
  obSt := Unit
  obStInterp := fun GD _ s => iprop(⌜rE ∈ s → Pr GD⌝)
  logTsT := Unit
  localInterp := fun _ _ _ _ => iprop(True)

theorem AxDefer2.obPosUnfold {GF : BundledGFunctors} (GD : Gdexec) (σ : Unit) (s : GSet Geid) :
    AxirisG.obStInterp (self := APos (GF := GF)) GD σ s ⊣⊢ iprop(⌜rE ∈ s → Pr GD⌝) :=
  ⟨.rfl, .rfl⟩

/-- r's annotation: its flag read; d's: the SAME fact, derived under the gate (the deferred
read's flow equation consumes the gate fact). -/
def Rpos {GF : BundledGFunctors} (e : Geid) : IProp GF := iprop(⌜e = rE ∨ e = dE → Pr gdefer⌝)
def naPos {GF : BundledGFunctors} : Mea GF := umap Rpos gdefer.gdG.gxGmo
def eaPos {GF : BundledGFunctors} : Sra GF := umap (fun _ => (∅ : Mea GF)) gdefer.gdG.gxGmo
def φPos (_ : Geid) : Prop := Pr gdefer

section positive
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF]

attribute [local instance high] APos PSafe

theorem posFe (e : Geid) :
    ⊢ iprop(⌜gateOk gsrcD φPos e⌝ -∗
      flowEqEa gdefer e (Axpol.sPol gdefer e) (∅ : Mea GF) eaPos (Rpos e)) := by
  iintro %Hgate
  unfold flowEqEa flowEqDyn
  iintro %σ %s %Hsub %Hnin Hob _
  icases (AxDefer2.obPosUnfold gdefer σ s).1 $$ Hob with %Hs
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists ()
  isplitl []
  · iapply (AxDefer2.obPosUnfold gdefer () _).2
    ipureintro
    intro Hr
    by_cases hne : e = rE
    · exact gdeferPr
    · rcases elemOfUnion.1 Hr with h | h
      · exact absurd (elemOfSingleton.1 h).symm hne
      · exact Hs h
  isplitl []
  · unfold Rpos
    ipureintro
    rintro (rfl | rfl)
    · exact gdeferPr
    · -- THE DEFERRED READ: its fact comes from the gate.
      exact Hgate rE ((gsrcDSpec _ _).2 ⟨.inl rfl, rfl⟩)
  · iapply (eaDepositEmp (GF := GF) eaPos (lobSuccOf gdefer e) e
      (fun eOut h => absurd h (AxDefer2.lobSuccEmpty gdefer (fun _ => rfl) e eOut)))

theorem posTodo :
    ⊢ ordEaTodoG gdefer gsrcD φPos (eaPos (GF := GF)) naPos Lproc 0 := by
  unfold ordEaTodoG
  rw [List.drop_zero]
  refine AxDefer2.bigSepLIntro _ _ fun e He => ?_
  have He' : e ∈ gdefer.gdG.gxGmo := LprocPerm.mem_iff.1 He
  rw [naPos, eaPos, umapLookup _ _ e gdeferNd He', umapLookup _ _ e gdeferNd He']
  exact posFe e

end positive

theorem posPure {GF : BundledGFunctors} : gateSrcPure (naPos (GF := GF)) gsrcD φPos := by
  intro e r hr
  obtain ⟨_, rfl⟩ := (gsrcDSpec e r).1 hr
  refine ⟨Rpos rE, umapLookup _ _ _ gdeferNd (by decide), ?_⟩
  exact pure_elim' fun h => pure_intro (h (.inl rfl))

theorem posDomEq {GF : BundledGFunctors} :
    (FiniteMap.dom_set (eaPos (GF := GF)) : GSet Geid) = FiniteMap.dom_set (naPos (GF := GF)) := by
  rw [eaPos, naPos, umapDom, umapDom]

theorem posDom {GF : BundledGFunctors} :
    (LawfulSet.ofList Lproc : GSet Geid) ⊆ FiniteMap.dom_set (naPos (GF := GF)) := by
  rw [naPos, umapDom]
  intro x hx
  rw [elemOfListToSet] at hx ⊢
  exact LprocPerm.mem_iff.1 hx

theorem posLob {GF : BundledGFunctors} :
    ∀ e0 gm, get? (eaPos (GF := GF)) e0 = some gm →
      (FiniteMap.dom_set gm : GSet Geid) ⊆ @Axpol.lobp PSafe gdefer e0 := by
  intro e0 gm hgm
  have hm := elemOfListToMap2 hgm
  obtain ⟨x, _, hx⟩ := List.mem_map.1 hm
  cases hx
  intro y hy
  rw [domEmpty] at hy
  exact absurd hy notElemOfEmpty

/-- `adequacyOrdG` closed on `gdefer`, with d processed AFTER r. -/
theorem gdeferAdequate : ∀ e, e ∈ Lproc → gateOk gsrcD φPos e := by
  apply Iris.pure_soundness (PROP := IProp refGF)
  refine step_fupdN_soundness_close (hlc := .hasNoLC) Lproc.length 0 (fun Hinv => ?_)
  have H := @adequacyOrdG PSafe .hasNoLC refGF Hinv APos gdefer gdeferCat Lproc LprocPerm
    LprocPol gsrcD φPos LprocBefore naPos eaPos posPure posDomEq posDom posLob ()
  have hpost :
      iprop(∃ (σ : Unit),
          AxirisG.obStInterp (self := APos (GF := refGF)) gdefer σ (LawfulSet.ofList Lproc) ∗
          ([∗set] e0 ∈ (LawfulSet.ofList Lproc : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? (naPos (GF := refGF)) e0)) ∗
          ⌜∀ e, e ∈ Lproc → gateOk gsrcD φPos e⌝) ⊢
      iprop(⌜∀ e, e ∈ Lproc → gateOk gsrcD φPos e⌝) := by
    iintro ⟨%σ, -, -, %Hall⟩
    ipureintro
    exact Hall
  iintro _
  iapply (AxDefer.stepFupdNMono (hlc := .hasNoLC) (n := Lproc.length) hpost)
  iapply H
  · iapply (posTodo (hlc := .hasNoLC) (GF := refGF))
  · iapply (AxDefer2.obPosUnfold (GF := refGF) gdefer () ∅).2
    ipureintro
    intro h
    exact absurd h notElemOfEmpty

/-! # 4. LEDGER: processing-order histories do not re-sort to gmo order -/

def ledgerHistOkL (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (L : List Geid)
    (LH : List Ledger) : Prop :=
  LH.length = L.length + 1 ∧
  ∀ k e L0 L1, L[k]? = some e → LH[k]? = some L0 → LH[k + 1]? = some L1 →
    AxTokLedger.ledgerStep OC nh GD e L0 L1

/-- At `L := gxGmo` it IS the ledger's own list form. -/
theorem ledgerHistOkLGmo (OC : Int → Prop) (nh : Nat) (GD : Gdexec) (LH : List Ledger) :
    ledgerHistOkL OC nh GD GD.gdG.gxGmo LH ↔ ledgerHistOkList OC nh GD LH := Iff.rfl

def AxDefer2.OCX (a : Int) : Prop := a = 0

def lsing (h : Holder) : Ledger := {[0 := h]}

def LHp : List Ledger :=
  [lsing (.held 1), lsing (.held 1), lsing (.pending wfE),
   lsing (.held 0), lsing (.held 0), lsing (.held 0)]

theorem AxDefer2.lsingGet0 (h : Holder) : get? (lsing h) 0 = some h := by
  unfold lsing; exact lookupSingleton

theorem noAcc (e : Geid) (a : Int) :
    gaccB gdefer.gdG e a = false → ¬ gaccesses gdefer.gdG e a := by
  intro hb ha
  rw [(gaccBSpec _ _ _).2 ha] at hb
  cases hb

theorem ledgerLOkGdefer : ledgerHistOkL AxDefer2.OCX 2 gdefer Lproc LHp := by
  refine ⟨rfl, ?_⟩
  intro k e L0 L1 hk h0 h1
  rcases k with _ | _ | _ | _ | _ | k
  · -- Wx: hart 1 writes x holding it
    cases hk; cases h0; cases h1
    refine ledgerStepOfMoves _ _ _ _ _ _ (ledgerMovesRefl _ _ _) ?_
    intro a ha _ _
    cases ha
    exact .inl (AxDefer2.lsingGet0 _)
  · -- Wf: release x
    cases hk; cases h0; cases h1
    refine ledgerStepOfMoves _ _ _ _ _ _ ?_ ?_
    · intro a
      by_cases ha : a = 0
      · subst ha
        rw [AxDefer2.lsingGet0, AxDefer2.lsingGet0]
        exact .lmRelease ⟨_, rfl, by decide +kernel⟩
      · have e1 : get? (lsing (.held 1)) a = none := by
          unfold lsing; exact lookupSingletonNe (Ne.symm ha)
        have e2 : get? (lsing (.pending wfE)) a = none := by
          unfold lsing; exact lookupSingletonNe (Ne.symm ha)
        rw [e1, e2]
        exact .lmSame _
    · intro a ha _ hacc
      cases ha
      exact absurd hacc (noAcc _ _ (by decide +kernel))
  · -- r: acquire x along rf from the release
    cases hk; cases h0; cases h1
    refine ledgerStepOfMoves _ _ _ _ _ _ ?_ ?_
    · intro a
      by_cases ha : a = 0
      · subst ha
        rw [AxDefer2.lsingGet0, AxDefer2.lsingGet0]
        exact .lmAcquire wfE (.inl ⟨1, (grfAtBSpec _ _ _ _).1 (by decide +kernel)⟩)
      · have e1 : get? (lsing (.pending wfE)) a = none := by
          unfold lsing; exact lookupSingletonNe (Ne.symm ha)
        have e2 : get? (lsing (.held 0)) a = none := by
          unfold lsing; exact lookupSingletonNe (Ne.symm ha)
        rw [e1, e2]
        exact .lmSame _
    · intro a ha _ hacc
      cases ha
      exact absurd hacc (noAcc _ _ (by decide +kernel))
  · -- d: reads x, held by hart 0 — in THIS order
    cases hk; cases h0; cases h1
    refine ledgerStepOfMoves _ _ _ _ _ _ (ledgerMovesRefl _ _ _) ?_
    intro a ha _ _
    cases ha
    exact .inl (AxDefer2.lsingGet0 _)
  · -- w: y is not tracked
    cases hk; cases h0; cases h1
    refine ledgerStepOfMoves _ _ _ _ _ _ (ledgerMovesRefl _ _ _) ?_
    intro a ha _ hacc
    cases ha
    exact absurd hacc (noAcc _ _ (by decide +kernel))
  · cases hk

theorem ledgerGmoNoneGdefer : ¬ ∃ LH, ledgerHistOkList AxDefer2.OCX 2 gdefer LH := by
  rintro ⟨LH, hlen, hstep⟩
  rw [gdeferGmo] at hlen
  rcases LH with _ | ⟨L0, _ | ⟨L1, LH⟩⟩
  · cases hlen
  · cases hlen
  -- gmo slot 0: d accesses x
  obtain ⟨hmv0, hacc0⟩ := hstep 0 dE L0 L1 rfl rfl rfl
  have hL1 : get? L1 0 = some (.held 0) := by
    rcases hacc0 0 rfl ⟨0, rfl, by omega⟩ ((gaccBSpec _ _ _).1 (by decide +kernel)) with
      hL0 | ⟨w, _, hL1⟩
    · have hm := hmv0 0
      rw [hL0] at hm
      rcases ledgerMoveHeldInv _ _ _ _ hm with h | ⟨_, _, hrel⟩
      · exact h
      · obtain ⟨l, hl, hb⟩ := hrel
        cases hl
        exact absurd hb (by decide)
    · exact hL1
  -- gmo slot 1: Wx (hart 1) accesses x, which hart 0 holds
  rcases LH with _ | ⟨L2, LH⟩
  · simp at hlen
  obtain ⟨_, hacc1⟩ := hstep 1 wxE L1 L2 rfl rfl rfl
  rcases hacc1 0 rfl ⟨1, rfl, by omega⟩ ((gaccBSpec _ _ _).1 (by decide +kernel)) with
    hL | ⟨w, hL, _⟩
  · rw [hL1] at hL
    cases hL
  · rw [hL1] at hL
    cases hL

end Weak
