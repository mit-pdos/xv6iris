/-
Weak: **OWNER DECISION D5 — the store CLASS pinned to the instruction that emits it, and K1
restated at PROGRAM level.**

Rocq: `iris/AxClsStep.v` @ xxvzwolszwmp.

## The Rocq header, in substance

THE GAP.  `AxOpsem.astepProg`'s `AStepWrite` checks a store's identity (kind / rl / base / width)
and its bytes against the row item, but NEVER its class (`aident` erases it).  So one program
realizes a row with `WCrel` and its twin with `WCplain`, and `AxTokLedgerWp.ledgerVerified nh GD`
is a per-GRAPH notion.

WHERE THE CLASS COMES FROM.  The language stamps the class at the store's append:
`WeakEvInst.pclsEv p l ws` — `wmClassOf (classify ak) ws` at a hart's `memWrite` node
(`akLatest` ⇒ `WCexcl`; `akSync` or the release-pending flag `wRelp` ⇒ `WCrel`; else `WCplain`),
`WCexcl` for a fused RMW, `ddevClass` for the disk.  It reads the view ONLY through `wRelp`.
`wRelp` evolves per label by `WeakEvCapstone.pfWs`: set by a `pw ∧ sw` fence, cleared by every
(non-empty) store / RMW, kept by everything else.  The class is the only unpinned field.

§1 `relpWs`, `lcls p l r := pclsEv p l (relpWs r)`, faithfulness `lclsFaithful`; `relpUpd` and
`relpUpdFaithful` (to `pfWs`, non-empty stores).
§2 the derived step `clsStep GD i` on `Athread × Bool`: `astepAnyNfGv`'s three arms, the program
arm additionally requiring, at a write, `lbCls (row[k]?) = lcls (atP s) l r`.  Refinement:
`clsStepGv` / `clsNstepsGv` / `clsNstepsTierA`.
§3 programs `Aprog` and `progRealizes P GD`.
§4 program-level K1: `progLedgerVerified nh P`, `progLedgerVerifiedLv`, `progViolFree`,
`progNotVerifiedOfViol`.

HONESTY (as Rocq): `relpUpd`'s faithfulness is to `pfWs`, label by label; the base protocol is
still a function of the graph, so a ∀-GD proof may still case on the graph, but must cover EVERY
graph the program realizes.

## Deviations from Rocq

1. NAMES: camelCase (map below); `Z` ↦ `Int`; `l !! k` ↦ `l[k]?`; `is_Some o` ↦
   `o.isSome = true`; `gx_img (gd_g GD)` ↦ `GD.gdG.gxImg`; record `aprog`/`AProg` ↦ structure
   `Aprog` (fields `apHarts`/`apS0`/`apImg`); `prog_ledger_verified` an inductive Prop with
   constructor `progLedgerVerified.mk` (as `ledgerVerified.mk`: `GF : BundledGFunctors.{0,0,0}`,
   classes as instance binders).
2. O2 STAGE C (as AxWpDSteps/AxTierA2/AxTokLedgerWp): there is no text oracle `T`/`ax_text`.
   `clsStep GD i` has no `T` parameter; `Aprog` has no `ap_T` field; `clsStepGv`/`clsNstepsGv`
   need no `AxirisG` instance (Rocq: at any `axirisG` with `ax_text = T`), `clsNstepsTierA` no
   `T`/annotation instances, and `progRealizesGv` drops its `ax_text = ap_T P` premise.  The
   program arm `CSProg` replaces Rocq's `wlabel_is_fetch l = false` by the boot-image pin
   `WeakAxRealize.fetchPin GD.gdG.gxImg l` (the arm is `astepAnyNfGv`'s `astepProgNf` arm, whose
   step carries that pin; a fetch is an admin step, not excluded).
3. `relpUpd` has an `LIFetch` arm (keeps the flag, as `pfWs` keeps the view).
4. `nsteps` is iris-lean's tail-built `Relation.Iterate` (`MachCSL.Rel`): `clsNstepsGv` is by
   induction on the last step.

**Rocq → Lean name map.**  `relp_ws` `relpWs`, `lcls` `lcls`, `pcls_ev_relp`
`AxClsStep.pclsEvRelp` (duplicated, file-qualified),
`lcls_faithful` `lclsFaithful`, `relp_upd` `relpUpd`, `relp_upd_faithful` `relpUpdFaithful`,
`cls_step` `clsStep` (`CSProg`/`CSWire`/`CSRead`), `cls_step_gv` `clsStepGv`, `cls_nsteps_gv`
`clsNstepsGv`, `cls_nsteps_tierA` `clsNstepsTierA`, `aprog` `Aprog` (`ap_harts` `apHarts`,
`ap_s0` `apS0`, `ap_img` `apImg`), `prog_realizes` `progRealizes`, `prog_realizes_gv`
`progRealizesGv`, `prog_ledger_verified` `progLedgerVerified` (`ProgLedgerVerified`
`progLedgerVerified.mk`), `prog_ledger_verified_lv` `progLedgerVerifiedLv`, `prog_viol_free`
`progViolFree`, `prog_not_verified_of_viol` `progNotVerifiedOfViol`.

**Dropped:** the field `ap_T` (deviation 2); the §5 `Print Assumptions` block (the lint's axiom
check covers it).  Lean-only helper: `AxClsStep.loadPostRunRelp`.
-/
import Weak.AxTokLedgerWp
import Weak.WeakEvCapstone

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Wlabel

/-! # 1. THE PROGRAM-DETERMINED CLASS AND THE RELEASE-PENDING FLAG -/

/-- A view whose only relevant field is `wRelp`. -/
def relpWs (r : Bool) : Wstate :=
  { wCoh := ∅, wVrOld := 0, wVwOld := 0, wVrNew := 0, wVwNew := 0, wVRel := 0, wFwd := ∅,
    wPub := 0, wRelp := r, wRegv := ∅, wVcap := 0, wLdv := 0, wRes := none, wTbank := 0 }

/-- The class the LANGUAGE stamps on the message label `l` appends, at program node `p`, with
release-pending flag `r`. -/
def lcls (p : Pexv6) (l : Wlabel) (r : Bool) : WmClass :=
  pclsEv p l (relpWs r)

/-- `pclsEv` reads the view only through `wRelp` (every arm). -/
theorem AxClsStep.pclsEvRelp (p : Pexv6) (l : Wlabel) (ws ws' : Wstate) :
    ws.wRelp = ws'.wRelp → pclsEv p l ws = pclsEv p l ws' := by
  intro hrelp
  cases l <;> simp only [pclsEv] <;>
    first
    | rfl
    | (cases p with
        | PHart _ m _ _ _ => exact pnodeWclassRelp m ws ws' hrelp
        | PDisk _ => simp only [ddevClass, wmClassOf, hrelp])

/-- FAITHFULNESS: `lcls` IS the language's class. -/
theorem lclsFaithful (p : Pexv6) (l : Wlabel) (ws : Wstate) :
    pclsEv p l ws = lcls p l ws.wRelp :=
  AxClsStep.pclsEvRelp p l ws _ rfl

/-- How a label moves the release-pending flag. -/
def relpUpd (l : Wlabel) (r : Bool) : Bool :=
  match l with
  | LFence _ pw _ sw => if (pw && sw) then true else r
  | LStore .. | LExStore .. | LRmw .. => false
  | _ => r

/-- Lean-only: `loadPostRun` keeps `wRelp`. -/
theorem AxClsStep.loadPostRunRelp (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) :
    (loadPostRun ws aq base ts).wRelp = ws.wRelp := by
  rw [← loadPostRunD0]
  exact loadPostRunDRelp _ _ _ _ _

/-- FAITHFULNESS of `relpUpd` to the promise-free machine's view update
(`WeakEvCapstone.pfWs`), for non-empty stores (`pfOk` demands it). -/
theorem relpUpdFaithful {P D : Type} (cfg : Wpcfg P D) (ag : Wpagent P) (l : Wlabel) :
    (∀ d, wlWdata l = some d → d ≠ []) →
    (∀ aq rl base tvs data asrc vsrc, l = LRmw aq rl base tvs data asrc vsrc → data ≠ []) →
    (pfWs cfg ag l).wRelp = relpUpd l ag.paWs.wRelp := by
  intro Hst Hrmw
  cases l with
  | LSilent => rfl
  | LDev => rfl
  | LIFetch _ _ => rfl
  | LLoad aq _ base tvs _ => exact AxClsStep.loadPostRunRelp _ _ _ _
  | LExLoad aq base tvs asrc => exact exloadPostRunDRelp _ _ _ _ _
  | LFence pr pw sr sw => rfl
  | LRegW rd srcs => rfl
  | LCtrl srcs => exact ctrlPostRelp _ _
  | LInstr => rfl
  | LStore rl base data asrc vsrc =>
    have h := Hst data rfl
    apply storePostRunDRelp
    cases data with
    | nil => exact absurd rfl h
    | cons _ _ => simp
  | LExStore rl base data asrc vsrc =>
    have h := Hst data rfl
    apply storePostRunDRelp
    cases data with
    | nil => exact absurd rfl h
    | cons _ _ => simp
  | LRmw aq rl base tvs data asrc vsrc =>
    have h := Hrmw aq rl base tvs data asrc vsrc rfl
    apply storePostRunDRelp
    cases data with
    | nil => exact absurd rfl h
    | cons _ _ => simp

/-! # 2. THE CLASS-PINNED STEP RELATION (derived; `AxOpsem` untouched) -/

section cls
variable (GD : Gdexec) (i : Agent)

/-- `astepAnyNfGv`'s arms over `Athread × Bool`; a WRITE step must produce the row item's
class. -/
inductive clsStep : Athread × Bool → Athread × Bool → Prop where
  | CSProg (s : Athread) (l : Wlabel) (s' : Athread) (r : Bool) :
      AxOpsem.astepProg (AxOpsem.grow GD i) s l s' →
      WeakAxRealize.fetchPin GD.gdG.gxImg l →
      (∀ lb, (wlWr l).isSome = true → (AxOpsem.grow GD i)[s.atK]? = some lb →
        lbCls lb = lcls s.atP l r) →
      clsStep (s, r) (s', relpUpd l r)
  | CSWire (s s' : Athread) (r : Bool) : awire s s' → clsStep (s, r) (s', r)
  | CSRead (s : Athread) (id : AidentT) (K : List (BitVec 8) → Athread) (v : List (BitVec 8))
      (r : Bool) :
      areadStep (AxOpsem.grow GD i) s id K →
      graphValue GD (i, s.atK) = some v →
      v.length = aidentN id →
      clsStep (s, r) (K v, r)

end cls

/-- REFINEMENT: a class-pinned step is an `astepAnyNfGv` step. -/
theorem clsStepGv (GD : Gdexec) (i : Agent) (x y : Athread × Bool) :
    clsStep GD i x y → astepAnyNfGv GD i x.1 y.1
  | .CSProg s l s' _ hst hpin _ => .ANFGVProg _ _ ⟨l, hst, hpin⟩
  | .CSWire _ _ _ hw => .ANFGVWire _ _ hw
  | .CSRead _ id K v _ hrd hgv hlen => .ANFGVRead _ id K v hrd hgv hlen

theorem clsNstepsGv (GD : Gdexec) (i : Agent) (n : Nat) (x y : Athread × Bool) :
    nsteps (clsStep GD i) n x y → nsteps (astepAnyNfGv GD i) n x.1 y.1 := by
  intro h
  induction h with
  | rfl => exact nsteps_O _
  | tail w _ hs ih => exact nsteps_r ih (clsStepGv GD i _ _ hs)

/-- … in the `tierAAstep` form `ledgerVerified`'s `Hrun` takes. -/
theorem clsNstepsTierA (GD : Gdexec) {N : Type} (nm : N) (i : Agent) (n : Nat)
    (x y : Athread × Bool) :
    nsteps (clsStep GD i) n x y → nsteps (tierAAstep GD nm i) n x.1 y.1 :=
  clsNstepsGv GD i n x y

/-! # 3. PROGRAMS AND THE GRAPHS THEY REALIZE -/

/-- A program: its harts, each hart's start thread (pexv6 node, row position 0) and the initial
memory image (Stage C: no text oracle). -/
structure Aprog where
  AProg ::
  apHarts : List Agent
  apS0 : Agent → Athread
  apImg : Image

/-- `P` REALIZES `GD`: every hart has a CLASS-PINNED run from its start thread (release-pending
flag initially clear) that consumes its whole row; the graph's initial image is the program's; no
gmo event outside `P`'s harts. -/
def progRealizes (P : Aprog) (GD : Gdexec) : Prop :=
  P.apHarts.Nodup ∧
  GD.gdG.gxImg = P.apImg ∧
  (∀ e, e ∈ GD.gdG.gxGmo → e.1 ∈ P.apHarts) ∧
  (∀ i, i ∈ P.apHarts → (P.apS0 i).atK = 0) ∧
  ∃ (n : Agent → Nat) (sN : Agent → Athread) (rN : Agent → Bool),
    ∀ i, i ∈ P.apHarts →
      nsteps (clsStep GD i) (n i) (P.apS0 i, false) (sN i, rN i) ∧
      (sN i).atK = (AxOpsem.grow GD i).length

/-- The old (class-blind) runs follow. -/
theorem progRealizesGv (P : Aprog) (GD : Gdexec) :
    progRealizes P GD →
    ∀ i, i ∈ P.apHarts → ∃ n sN,
      nsteps (astepAnyNfGv GD i) n (P.apS0 i) sN ∧ sN.atK = (AxOpsem.grow GD i).length := by
  intro ⟨_, _, _, _, n, sN, rN, Hr⟩ i Hi
  obtain ⟨Hrun, Hend⟩ := Hr i Hi
  exact ⟨n i, sN i, clsNstepsGv GD i _ _ _ Hrun, Hend⟩

/-! # 4. PROGRAM-LEVEL K1 -/

/-- `progLedgerVerified nh P`: ONE choice of resources, policy, Own class `OC`, base protocol,
initial resources and post for the PROGRAM; then, for EVERY consistent graph `P` realizes, the
`ledgerVerified` premises minus the runs (which `progRealizes` supplies). -/
inductive progLedgerVerified (nh : Nat) (P : Aprog) : Prop where
  | mk (GF : BundledGFunctors.{0,0,0}) [HannG : AxannotG GF] [HlG : LedgerG GF]
      [Hpre : InvGpreS GF] [pol : Axpol] (OC : Int → Prop)
      (N0 obSt0 : Type) (base0 : N0 → Gdexec → obSt0 → GSet Geid → IProp GF)
      (init : N0 × GName → Agent → IProp GF)
      (post : Agent → Athread → Prop)
      (Hwf : axpolWf)
      (Hver : ∀ GD, progRealizes P GD → rvwmoCatConsistent GD →
        (∀ w a v, w ∈ GD.gdG.gxGmo → tidHart nh (some w.1) →
          glblIs GD.gdG w lbPlain → gwritesByte GD.gdG w a v → OC a) ∧
        (∀ [InvGS_gen .hasNoLC GF] [AxannotGS GF] (nm : N0 × GName),
          ⊢ ([∗list] i ∈ P.apHarts, init nm i) -∗
            [∗list] i ∈ P.apHarts,
              tierAWpd GD (N0 × GName) obSt0 (obStInterpL OC nh base0) nm (P.apS0 i)
                .MaybeStuck i (fun s => iprop(⌜post i s⌝))) ∧
        (⊢ |==> ∃ (nm : N0 × GName) (σ0 : obSt0),
          obStInterpL OC nh base0 nm GD σ0 ∅ ∗ [∗list] i ∈ P.apHarts, init nm i) ∧
        (∀ e e', e' ∈ Axpol.sPol GD e → gmoLt GD.gdG e' e) ∧
        (∀ e e', e' ∈ Axpol.lobp GD e → gmoLt GD.gdG e' e))

/-- A program-level verification is a per-graph one at every realized consistent graph. -/
theorem progLedgerVerifiedLv (nh : Nat) (P : Aprog) (GD : Gdexec) :
    progLedgerVerified nh P → progRealizes P GD → rvwmoCatConsistent GD →
    ledgerVerified nh GD := by
  intro Hv Hreal Hcons
  refine progLedgerVerified.casesOn (motive := fun _ => _) Hv ?_
  intro GF HannG HlG Hpre pol OC N0 obSt0 base0 init post Hwf Hver
  obtain ⟨Hplain, Hwp, Hob, Hs, Hl⟩ := Hver GD Hreal Hcons
  obtain ⟨Hnd, _, Hharts, Hk0, n, sN, rN, Hr⟩ := Hreal
  exact @ledgerVerified.mk nh GD GF HannG HlG Hpre pol OC N0 obSt0 base0 init P.apHarts P.apS0
    sN n post Hplain Hwf Hnd Hharts
    (fun _ nm i Hi => clsNstepsTierA GD nm i (n i) (P.apS0 i, false) (sN i, rN i) (Hr i Hi).1)
    Hk0 (fun i Hi => (Hr i Hi).2) Hwp Hob Hs Hl

/-- PROGRAM-LEVEL K1: no graph the verified program realizes has a violation. -/
theorem progViolFree (nh : Nat) (P : Aprog) :
    progLedgerVerified nh P →
    ∀ GD, progRealizes P GD → rvwmoCatConsistent GD → ¬ gdviolationHart nh GD := by
  intro Hv GD Hreal Hcons
  exact adequacyViolFreeLedger nh GD Hcons (progLedgerVerifiedLv nh P GD Hv Hreal Hcons)

/-- THE NEGATIVE FORM: one realized consistent violating graph refutes program-level
verification. -/
theorem progNotVerifiedOfViol (nh : Nat) (P : Aprog) (GD : Gdexec) :
    progRealizes P GD → rvwmoCatConsistent GD → gdviolationHart nh GD →
    ¬ progLedgerVerified nh P :=
  fun Hr Hc Hv Hver => progViolFree nh P Hver GD Hr Hc Hv

end Weak
