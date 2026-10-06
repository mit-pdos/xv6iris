/-
Weak: **the route-B conformance vocabulary** (stage B0b-1).

Rocq: `iris/WeakRvwmoConf.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Design `claude-notes/design/weak-memory-route-b.md` §2/§4 (B0b).  This file bridges the two
worlds route B's capstone clause speaks about at once: the GRAPH world (`WeakRvwmoGraph`'s
`Gexec`/`Gdexec`, whose per-hart ROWS are lists of fused axiomatic labels `Lbl`, and
`WeakRvwmoNorm`'s renaming `lblRen`/`rowsRel`) and the INSTANCE world (`WeakEvInst.pstepEv` /
`pclsEv` over `WeakEvPf.Pexv6`, and T1-D's supply vocabulary in `WeakAxRealize`: `lbNobarex`,
`latFree`, `lbRfoldfree`, `lbAdmin`, `admStar`).  It is the one Rvwmo leaf that imports the
instance band.

WHAT IS HERE.
(1) `rowDeps` — the SYNTACTIC REGISTER-DATAFLOW relation of an emitted instance label sequence
    (RVWMO rules 9/10/11/13, store halves): the (source, target) ROW-position pairs a hart's
    own labels induce.
(2) `hartConf` — PER-HART ROW EMITTABILITY: the hart's program emits the row in po order, one
    `admRun`-then-realizing-step block per row event, with the exclusive PAIR as the second
    block shape (`WeakAxRealize.execProgOk'`'s per-event disjunction).
(3) the two STABILITY lemmas — `hartConfRen` (the emission survives the normalization's ts
    renaming; no side condition on `π`) and `hartConfPrefix`.
(4) `gdexecConf` — the bundle (every hart's row is emittable and the emission's syntactic deps
    are in the graph's dep set) and `gdexecConfRen`, its transport along `rowsRel`.

SCOPE DECISIONS (Rocq (S-a)…(S-d)).  (S-a) reversed at `dedges` (route-b §4d.1 F5): the W-TV
translation-order edges ARE emitted, from `dsLd`.  (S-a') F5': a load's result write is
`LRegW rd (DLdRes :: the load's address sources)` (`WeakDeps.depsRd`), so `dprov rd` carries
address chains.  (S-a'') the SATP-provenance edge: `dedges` adds `dprov s wsatp` to every
store's / RMW's sources (DEC-5; stronger, it only adds edges).  (S-a''') other CSRs reach a
store through paths `rowDeps` already has (`sret`'s `LCtrl [DReg wsepc]`).  (S-b) an emission
item carries its row position explicitly (`Eitem`), since the exclusive pair puts two
projecting labels at ONE position.  (S-c) `rowDeps` emits only strictly-increasing edges (the
pair's internal (k, k) edge is filtered).  (S-d) the fabric is a per-row-position parameter
`dv : Nat → Efab`, which makes `hartConfPrefix` carry the same `dv`.

THE CLASS EQUATION IS ts-INDEPENDENT: the per-hart projection equation is read at
`rowWs row k`, a REPRESENTATIVE `Wstate` folded from the row's own labels; `pclsEv` reads the
`Wstate` only through `wRelp` (`WeakRvwmoConf.pclsEvRelp`), and `wRelp` of the fold depends only
on fence bits and on whether a write writes a byte (`rowWsRelp`, `lpostRelpRen`).

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below); `tvs.*1`/`.*2` ↦ `tvs.map Prod.fst`/`Prod.snd`;
   `f <$> l` ↦ `l.map f` (and `Option.map` for `proj_lbl`'s square); `S k` ↦ `k + 1`;
   `l !! n` ↦ `l[n]?`; `prefix_of` ↦ `<+:`; `mjoin` ↦ `List.flatten`; `agent` ↦ `Nat`;
   `dev_state` ↦ `Efab` (the event instance's fabric, `WeakEvPf` deviation 9 / owner decision
   Q1: the device states plus the residual UART/PLIC programs).  The four duplicated Rocq names are file-qualified
   (`WeakRvwmoConf.pclsEvRelp`, `WeakRvwmoConf.loadPostRunRelp`, `WeakRvwmoConf.Dstate`,
   `WeakRvwmoConf.dstep`).  The wlabel constructors are the unqualified ones (`open Wlabel`, as
   Rocq's import order makes them); graph labels are written `Lbl.LLoad` / `.LLoad`.
2. `ds_prov : gmap wreg (list nat)` ↦ the TOTAL FUNCTION `dsProv : Nat → List Nat` (`∅` ↦
   `fun _ => []`, `<[rd := v]>` ↦ `dprovSet`, Lean-only); `dprov s r` (Rocq `default [] (ds_prov
   s !! r)`) is the application.  Every consumer goes through `dprov`/`∈`, as in Rocq.
3. O2 — THE INSTRUCTION FETCH (Lean-only label `LIFetch base tvs`; owner decision D1: the fetch
   STAYS a graph read, `projLbl (LIFetch ..) = some (LLoad false ..)`).  Rocq's fetch was an
   `LLoad false` item; the Lean one is `LIFetch`, treated EXACTLY as that `LLoad`:
   - `wlblRen` renames its `tvs` (the projection square `projLblWren` needs it), and
     `pstepEvWren`'s arm is `WeakEvInst.pstepEvTsIfetch`;
   - `elbIsR (LIFetch ..) = true` (it projects to a read), and `dstep`'s `LIFetch` arm is the
     `LLoad` arm (a tagged fetch is pushed to `dsLd`; the model's announce `LInstr`, which
     follows every fetch, resets it).
   - `hlblRealizes` is Rocq's FOUR-conjunct relation; `WeakAxRealize.lblRealizes` has the
     Lean-only fifth conjunct `lbFetchInert σ i l` (its deviation 4), which reads the AXIOMATIC
     `Wstate`'s coherence/views and is therefore NOT stable under `rowWs`'s representative
     state or the ts renaming.  So the definitional seam `hlbl_realizes_ax` is restated as
     `hlblRealizesAx : lblRealizes pclsEv p σ i lb l ↔ hlblRealizes p (σ.msWs i) lb l ∧
     lbFetchInert σ i l` (vacuous for every non-fetch label: `lbFetchInert` is `True` there,
     `hlblRealizesAxNoFetch`, Lean-only).  The consumer (B0b-2) supplies `lbFetchInert` at the
     machine's state, where it lives.  `hlblRealizesPairAx` is unchanged (`Iff.rfl`).
4. PROOFS: per-constructor case analysis (Rocq `destruct l; simpl; try done`); the smoke tests
   (Rocq `Example … vm_compute`) are named `theorem`s closed by `decide`.
5. Lean-only helpers: `dprovSet`, `dedgesSnd`, `hlblRealizesAxNoFetch`, and the `dstepWithin`
   sub-lemmas `dsWithinPush`/`dsWithinInstr`/`dsWithinRegw`/`dsWithinCtrl`.

**Rocq → Lean name map.**  `pcls_ev_relp` `WeakRvwmoConf.pclsEvRelp`, `tv_ren` `tvRen`,
`wlbl_ren` `wlblRen`, `tv_ren_fst` `tvRenFst`, `tv_ren_snd` `tvRenSnd`, `tv_ren_length`
`tvRenLength`, `wlbl_ren_nobarex` `wlblRenNobarex`, `wlbl_ren_lat_free` `wlblRenLatFree`,
`wlbl_ren_rfoldfree` `wlblRenRfoldfree`, `wlbl_ren_admin` `wlblRenAdmin`, `proj_lbl_wren`
`projLblWren`, `pcls_ev_wren` `pclsEvWren`, `pstep_ev_wren` `pstepEvWren`, `lbl_post` `lblPost`,
`row_ws_aux` `rowWsAux`, `row_ws` `rowWs`, `lpost_relp` `lpostRelp`, `load_post_run_relp`
`WeakRvwmoConf.loadPostRunRelp`, `store_post_run_relp` `storePostRunRelp`, `lbl_post_relp`
`lblPostRelp`, `row_ws_aux_relp` `rowWsAuxRelp`, `row_ws_relp` `rowWsRelp`, `lpost_relp_ren`
`lpostRelpRen`, `lbl_post_relp_ren` `lblPostRelpRen`, `row_ws_aux_relp_ren` `rowWsAuxRelpRen`,
`row_ws_relp_ren` `rowWsRelpRen`, `hlbl_realizes` `hlblRealizes`, `hlbl_realizes_pair`
`hlblRealizesPair`, `hlbl_realizes_ax` `hlblRealizesAx`, `hlbl_realizes_pair_ax`
`hlblRealizesPairAx`, `hlbl_realizes_notadm` `hlblRealizesNotadm`, `hlbl_realizes_ren`
`hlblRealizesRen`, `hlbl_realizes_pair_ren` `hlblRealizesPairRen`, `adm_run` `admRun` (`ARnil`,
`ARcons`), `adm_run_star` `admRunStar`, `adm_run_admin` `admRunAdmin`, `adm_run_mono`
`admRunMono`, `adm_run_ren` `admRunRen`, `eitem` `Eitem`, `eadm` `eadm`, `eitem_ren` `eitemRen`,
`eitem_ren_eadm` `eitemRenEadm`, `eitem_ren_block` `eitemRenBlock`, `elb_is_r` `elbIsR`,
`elb_is_w` `elbIsW`, `elb_is_r_ren` `elbIsRRen`, `elb_is_w_ren` `elbIsWRen`, `dstate`
`WeakRvwmoConf.Dstate` (`DSt` `WeakRvwmoConf.Dstate.DSt`, `ds_prov`/`ds_ld`/`ds_ctl`
`dsProv`/`dsLd`/`dsCtl`), `ds_init` `dsInit`, `dprov` `dprov`, `dsrc_pos` `dsrcPos`, `dsrcs_pos`
`dsrcsPos`, `dedges` `dedges`, `dstep` `WeakRvwmoConf.dstep`, `row_deps_aux` `rowDepsAux`,
`row_deps` `rowDeps`, `dedges_lt` `dedgesLt`, `row_deps_aux_lt` `rowDepsAuxLt`, `row_deps_lt`
`rowDepsLt`, `row_deps_aux_tgt` `rowDepsAuxTgt`, `row_deps_tgt` `rowDepsTgt`, `ds_within`
`dsWithin`, `eread_ok` `ereadOk`, `ds_within_init` `dsWithinInit`, `dsrcs_pos_within`
`dsrcsPosWithin`, `dstep_within` `dstepWithin`, `row_deps_aux_within` `rowDepsAuxWithin`,
`row_deps_src` `rowDepsSrc`, `dstep_ren` `dstepRen`, `row_deps_aux_ren` `rowDepsAuxRen`,
`row_deps_ren` `rowDepsRen`, `hemit` `hemit` (`HEnil`/`HEone`/`HEpair`), `hemission`
`Hemission` (`HEm`, `em_items` `emItems`, `em_fin` `emFin`), `em_labels` `emLabels`, `em_ren`
`emRen`, `em_labels_ren` `emLabelsRen`, `hart_conf` `hartConf`, `row_ws_aux_snoc`
`rowWsAuxSnoc`, `row_ws_step` `rowWsStep`, `hlbl_realizes_kind` `hlblRealizesKind`,
`hemit_tag_lbl` `hemitTagLbl`, `hart_conf_tag_lbl` `hartConfTagLbl`, `hart_conf_row_deps_wf`
`hartConfRowDepsWf`, `hemit_ren` `hemitRen`, `hart_conf_ren` `hartConfRen`, `prefix_block`
`prefixBlock`, `hemit_prefix` `hemitPrefix`, `hart_conf_prefix` `hartConfPrefix`,
`gdexec_conf` `gdexecConf`, `gdexec_conf_deps_wf` `gdexecConfDepsWf`, `gdexec_conf_ren`
`gdexecConfRen`, `row_deps_chain` `rowDepsChain`, `row_deps_addr_chain` `rowDepsAddrChain`,
`row_deps_addr_chain_before` `rowDepsAddrChainBefore`, `row_deps_amo_selfedge`
`rowDepsAmoSelfedge`, `row_deps_wtv` `rowDepsWtv`, `row_deps_wtv_reset` `rowDepsWtvReset`,
`row_deps_satp_chain` `rowDepsSatpChain`, `row_deps_satp_chain_before`
`rowDepsSatpChainBefore`, `row_deps_satp_read` `rowDepsSatpRead`, `row_deps_sret_chain`
`rowDepsSretChain`, `row_deps_sret_chain_before` `rowDepsSretChainBefore`,
`row_deps_csr_readback` `rowDepsCsrReadback`, `hart_conf_nil` `hartConfNil`.

**Not ported:** nothing — every Rocq definition and lemma has a Lean twin.
-/
import Weak.WeakDeps
import Weak.WeakRvwmoNorm
import Weak.WeakAxRealize
import Weak.WeakEvInst

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Wlabel

/-! ## 1. The class function reads only `wRelp` -/

theorem WeakRvwmoConf.pclsEvRelp (p : Pexv6) (l : Wlabel) (we wi : Wstate) :
    we.wRelp = wi.wRelp → pclsEv p l we = pclsEv p l wi := by
  intro h
  cases l <;> simp only [pclsEv] <;>
    first
    | rfl
    | (cases p with
        | PHart _ m _ _ _ => exact pnodeWclassRelp m we wi h
        | PDisk _ => simp only [ddevClass, wmClassOf, h])

/-! ## 2. Renaming a wlabel's timestamp columns -/

def tvRen (π : Nat → Nat) (tv : Nat × BitVec 8) : Nat × BitVec 8 := (π tv.1, tv.2)

def wlblRen (π : Nat → Nat) (l : Wlabel) : Wlabel :=
  match l with
  | LLoad aq lat base tvs asrc => LLoad aq lat base (tvs.map (tvRen π)) asrc
  | LRmw aq rl base tvs data asrc vsrc => LRmw aq rl base (tvs.map (tvRen π)) data asrc vsrc
  | LExLoad aq base tvs asrc => LExLoad aq base (tvs.map (tvRen π)) asrc
  | LIFetch base tvs => LIFetch base (tvs.map (tvRen π))
  | LSilent => LSilent
  | LStore rl base data asrc vsrc => LStore rl base data asrc vsrc
  | LFence pr pw sr sw => LFence pr pw sr sw
  | LDev => LDev
  | LRegW rd srcs => LRegW rd srcs
  | LCtrl srcs => LCtrl srcs
  | LInstr => LInstr
  | LExStore rl base data asrc vsrc => LExStore rl base data asrc vsrc

theorem tvRenFst (π : Nat → Nat) (tvs : List (Nat × BitVec 8)) :
    (tvs.map (tvRen π)).map Prod.fst = (tvs.map Prod.fst).map π := by
  induction tvs with
  | nil => rfl
  | cons tv tvs ih => simp only [List.map_cons, ih]; rfl

theorem tvRenSnd (π : Nat → Nat) (tvs : List (Nat × BitVec 8)) :
    (tvs.map (tvRen π)).map Prod.snd = tvs.map Prod.snd := by
  induction tvs with
  | nil => rfl
  | cons tv tvs ih => simp only [List.map_cons, ih]; rfl

theorem tvRenLength (π : Nat → Nat) (tvs : List (Nat × BitVec 8)) :
    (tvs.map (tvRen π)).length = tvs.length := List.length_map _

/-- The renaming is invisible to the three T1-D label gates ... -/
theorem wlblRenNobarex (π : Nat → Nat) (l : Wlabel) : lbNobarex (wlblRen π l) ↔ lbNobarex l := by
  cases l <;> exact Iff.rfl

theorem wlblRenLatFree (π : Nat → Nat) (l : Wlabel) : latFree (wlblRen π l) ↔ latFree l := by
  cases l <;> exact Iff.rfl

theorem wlblRenRfoldfree (π : Nat → Nat) (l : Wlabel) :
    lbRfoldfree (wlblRen π l) ↔ lbRfoldfree l := by
  cases l <;> exact Iff.rfl

/-- ... and to the administrative alphabet, on which it is the identity. -/
theorem wlblRenAdmin (π : Nat → Nat) (instr : Bool) (l : Wlabel) :
    lbAdmin instr l → wlblRen π l = l := by
  cases l <;> intro h <;> first | rfl | exact h.elim

/-- THE PROJECTION SQUARE: renaming a wlabel renames its axiomatic image. -/
theorem projLblWren (k : WmClass) (π : Nat → Nat) (l : Wlabel) :
    projLbl k (wlblRen π l) = (projLbl k l).map (lblRen π) := by
  cases l <;> simp only [wlblRen, projLbl, Option.map, lblRen, tvRenFst, tvRenSnd]

/-- ... and it does not move the class the machine stamps. -/
theorem pclsEvWren (p : Pexv6) (π : Nat → Nat) (l : Wlabel) (we wi : Wstate) :
    we.wRelp = wi.wRelp → pclsEv p (wlblRen π l) we = pclsEv p l wi := by
  intro h
  have : pclsEv p (wlblRen π l) we = pclsEv p l we := by cases l <;> rfl
  rw [this]
  exact WeakRvwmoConf.pclsEvRelp p l we wi h

/-- THE TIMESTAMP-OBLIVIOUSNESS OF THE PROGRAM, at the renaming (every arm is one of
`WeakEvInst`'s `ts_oblivious` exports; the fetch arm is deviation 3). -/
theorem pstepEvWren (π : Nat → Nat) (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6)
    (d' : Efab) :
    latFree l → lbRfoldfree l → pstepEv p d l p' d' → pstepEv p d (wlblRen π l) p' d' := by
  cases l with
  | LLoad aq lat base tvs asrc =>
    intro hl hr h
    simp only [latFree] at hl
    simp only [lbRfoldfree] at hr
    subst hl hr
    exact pstepEvTsLoad p d aq base tvs _ p' d' h (tvRenSnd π tvs)
  | LRmw aq rl base tvs data asrc vsrc =>
    intro _ _ h
    exact pstepEvTsRmw p d aq rl base tvs _ data asrc vsrc p' d' h (tvRenSnd π tvs)
  | LExLoad aq base tvs asrc =>
    intro _ _ h
    exact pstepEvTsExload p d aq base tvs _ asrc p' d' h (tvRenSnd π tvs)
  | LIFetch base tvs =>
    intro _ _ h
    exact pstepEvTsIfetch p d base tvs _ p' d' h (tvRenSnd π tvs)
  | _ => intro _ _ h; exact h

/-! ## 3. The row's representative wstate fold -/

def lblPost (t : Nat) (ws : Wstate) (l : Lbl) : Wstate :=
  match l with
  | .LLoad aq base ts _ => loadPostRun ws aq base ts
  | .LStore rl base vs _ => storePostRun ws rl base vs.length (t + 1)
  | .LFence pr pw sr sw => fencePost ws pr pw sr sw
  | .LRmw aq rl base ts _ wvs _ =>
      storePostRun (loadPostRun ws aq base ts) rl base wvs.length (t + 1)

def rowWsAux (t : Nat) (ws : Wstate) (r : List Lbl) : Wstate :=
  match r with
  | [] => ws
  | l :: r' => rowWsAux (t + 1) (lblPost t ws l) r'

def rowWs (row : List Lbl) (k : Nat) : Wstate :=
  rowWsAux 0 wsInit (row.take k)

/-! ### 3.1 `wRelp` of the fold, computed -/

def lpostRelp (b : Bool) (l : Lbl) : Bool :=
  match l with
  | .LLoad _ _ _ _ => b
  | .LStore _ _ vs _ => match vs with | [] => b | _ => false
  | .LFence _ pw _ sw => if (pw && sw) then true else b
  | .LRmw _ _ _ _ _ wvs _ => match wvs with | [] => b | _ => false

theorem WeakRvwmoConf.loadPostRunRelp (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) :
    (loadPostRun ws aq base ts).wRelp = ws.wRelp := by
  rw [← loadPostRunD0]
  exact loadPostRunDRelp _ _ _ _ _

theorem storePostRunRelp (ws : Wstate) (rl : Bool) (base : Int) (n t : Nat) :
    (storePostRun ws rl base n t).wRelp = (match n with | 0 => ws.wRelp | _ + 1 => false) := by
  cases n with
  | zero => rfl
  | succ m =>
    rw [← storePostRunD0]
    exact storePostRunDRelp _ _ _ _ _ _ _ (by omega)

theorem lblPostRelp (t : Nat) (ws : Wstate) (l : Lbl) :
    (lblPost t ws l).wRelp = lpostRelp ws.wRelp l := by
  cases l with
  | LLoad aq base ts vs => exact WeakRvwmoConf.loadPostRunRelp _ _ _ _
  | LStore rl base vs k =>
    simp only [lblPost, lpostRelp]
    rw [storePostRunRelp]
    cases vs <;> rfl
  | LFence pr pw sr sw => rfl
  | LRmw aq rl base ts rvs wvs k =>
    simp only [lblPost, lpostRelp]
    rw [storePostRunRelp]
    cases wvs <;> simp only [List.length_nil, List.length_cons, WeakRvwmoConf.loadPostRunRelp]

theorem rowWsAuxRelp (t : Nat) (ws : Wstate) (r : List Lbl) :
    (rowWsAux t ws r).wRelp = r.foldl lpostRelp ws.wRelp := by
  induction r generalizing t ws with
  | nil => rfl
  | cons l r ih => simp only [rowWsAux, List.foldl_cons, ih, lblPostRelp]

/-- THE CHARACTERIZATION: `rowWs`'s release-pending bit is a fold of the row's own labels. -/
theorem rowWsRelp (row : List Lbl) (k : Nat) :
    (rowWs row k).wRelp = (row.take k).foldl lpostRelp false := by
  unfold rowWs
  rw [rowWsAuxRelp]
  rfl

/-! ### 3.2 The renaming does not move it -/

theorem lpostRelpRen (π : Nat → Nat) (b : Bool) (l : Lbl) :
    lpostRelp b (lblRen π l) = lpostRelp b l := by
  cases l <;> rfl

theorem lblPostRelpRen (π : Nat → Nat) (t : Nat) (ws ws' : Wstate) (l : Lbl) :
    ws'.wRelp = ws.wRelp →
    (lblPost t ws' (lblRen π l)).wRelp = (lblPost t ws l).wRelp := by
  intro h
  rw [lblPostRelp, lblPostRelp, h, lpostRelpRen]

theorem rowWsAuxRelpRen (π : Nat → Nat) (t : Nat) (ws ws' : Wstate) (r : List Lbl) :
    ws'.wRelp = ws.wRelp →
    (rowWsAux t ws' (r.map (lblRen π))).wRelp = (rowWsAux t ws r).wRelp := by
  induction r generalizing t ws ws' with
  | nil => intro h; exact h
  | cons l r ih =>
    intro h
    simp only [List.map_cons, rowWsAux]
    exact ih _ _ _ (lblPostRelpRen π t ws ws' l h)

/-- THE ts-GENERICITY OF THE PROJECTION EQUATION'S WSTATE. -/
theorem rowWsRelpRen (π : Nat → Nat) (row : List Lbl) (k : Nat) :
    (rowWs (row.map (lblRen π)) k).wRelp = (rowWs row k).wRelp := by
  unfold rowWs
  rw [← List.map_take]
  exact rowWsAuxRelpRen π 0 wsInit wsInit _ rfl

/-! ## 4. The per-hart realization relations -/

/-- Rocq's four-conjunct `hlbl_realizes` (deviation 3: no fetch-inertness conjunct). -/
def hlblRealizes (p : Pexv6) (ws : Wstate) (lb : Lbl) (l : Wlabel) : Prop :=
  lbNobarex l ∧ latFree l ∧ lbRfoldfree l ∧ projLbl (pclsEv p l ws) l = some lb

def hlblRealizesPair (_p pm : Pexv6) (ws : Wstate) (lb : Lbl) (l1 l2 : Wlabel) : Prop :=
  ∃ (aq rl : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (data : List (BitVec 8))
    (asrc1 asrc2 vsrc2 : List Dsrc),
    l1 = LExLoad aq base tvs asrc1 ∧
    l2 = LExStore rl base data asrc2 vsrc2 ∧
    data ≠ [] ∧ tvs.length = data.length ∧
    lb = Lbl.LRmw aq rl base (tvs.map Prod.fst) (tvs.map Prod.snd) data
           (pclsEv pm l2 (loadPostRun ws aq base (tvs.map Prod.fst)))

/-- The seam back to T1-D's vocabulary (deviation 3: plus the fetch-inertness conjunct). -/
theorem hlblRealizesAx (p : Pexv6) (σ : Mstate) (i : Nat) (lb : Lbl) (l : Wlabel) :
    lblRealizes pclsEv p σ i lb l ↔ hlblRealizes p (σ.msWs i) lb l ∧ lbFetchInert σ i l := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨h1, h2, h3, h4⟩, h5⟩
  · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
    exact ⟨h1, h2, h3, h4, h5⟩

/-- (Lean-only) Off the fetch, the seam is Rocq's. -/
theorem hlblRealizesAxNoFetch (p : Pexv6) (σ : Mstate) (i : Nat) (lb : Lbl) (l : Wlabel) :
    lbNoFetch l → (hlblRealizes p (σ.msWs i) lb l ↔ lblRealizes pclsEv p σ i lb l) := by
  intro hnf
  rw [hlblRealizesAx]
  have : lbFetchInert σ i l := by
    cases l <;> first | trivial | exact hnf.elim
  exact ⟨fun h => ⟨h, this⟩, fun h => h.1⟩

theorem hlblRealizesPairAx (p pm : Pexv6) (σ : Mstate) (i : Nat) (lb : Lbl) (l1 l2 : Wlabel) :
    hlblRealizesPair p pm (σ.msWs i) lb l1 l2 ↔ lblRealizesPair pclsEv p pm σ i lb l1 l2 :=
  Iff.rfl

/-- The realizing wlabel's shape is pinned by its axiomatic image. -/
theorem hlblRealizesNotadm (p : Pexv6) (ws : Wstate) (lb : Lbl) (l : Wlabel) (instr : Bool) :
    hlblRealizes p ws lb l → ¬ lbAdmin instr l := by
  rintro ⟨_, _, _, hpr⟩ ha
  rw [lbAdminProj _ instr l ha] at hpr
  simp at hpr

/-! ### 4.1 ts-genericity of both -/

theorem hlblRealizesRen (π : Nat → Nat) (p : Pexv6) (ws ws' : Wstate) (lb : Lbl) (l : Wlabel) :
    ws'.wRelp = ws.wRelp →
    hlblRealizes p ws lb l → hlblRealizes p ws' (lblRen π lb) (wlblRen π l) := by
  rintro hr ⟨hnb, hlat, hrf, hpr⟩
  refine ⟨(wlblRenNobarex π l).2 hnb, (wlblRenLatFree π l).2 hlat, (wlblRenRfoldfree π l).2 hrf,
    ?_⟩
  rw [pclsEvWren p π l ws' ws hr, projLblWren, hpr]
  rfl

theorem hlblRealizesPairRen (π : Nat → Nat) (p pm : Pexv6) (ws ws' : Wstate) (lb : Lbl)
    (l1 l2 : Wlabel) :
    ws'.wRelp = ws.wRelp →
    hlblRealizesPair p pm ws lb l1 l2 →
    hlblRealizesPair p pm ws' (lblRen π lb) (wlblRen π l1) (wlblRen π l2) := by
  rintro hr ⟨aq, rl, base, tvs, data, asrc1, asrc2, vsrc2, rfl, rfl, hne, hlen, rfl⟩
  refine ⟨aq, rl, base, tvs.map (tvRen π), data, asrc1, asrc2, vsrc2, rfl, rfl, hne,
    by rw [tvRenLength]; exact hlen, ?_⟩
  simp only [lblRen, wlblRen, tvRenFst, tvRenSnd]
  congr 1
  apply WeakRvwmoConf.pclsEvRelp
  rw [WeakRvwmoConf.loadPostRunRelp, WeakRvwmoConf.loadPostRunRelp, hr]

/-! ## 5. The label-carrying administrative run -/

inductive admRun (instr : Bool) : Pexv6 → Efab → List Wlabel → Pexv6 → Efab → Prop where
  | ARnil (p : Pexv6) (d : Efab) : admRun instr p d [] p d
  | ARcons (p : Pexv6) (d : Efab) (l : Wlabel) (p1 : Pexv6) (d1 : Efab)
      (ls : List Wlabel) (p' : Pexv6) (d' : Efab) :
      lbAdmin instr l → pstepEv p d l p1 d1 →
      admRun instr p1 d1 ls p' d' →
      admRun instr p d (l :: ls) p' d'

theorem admRunStar (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel) (p' : Pexv6)
    (d' : Efab) :
    admRun instr p d ls p' d' → admStar pstepEv instr p d p' d' := by
  intro h
  induction h with
  | ARnil p d => exact admStarRefl pstepEv instr p d
  | ARcons p d l p1 d1 ls p' d' ha hs _ ih => exact admStarL pstepEv instr p d l p1 d1 p' d' ha hs ih

theorem admRunAdmin (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel) (p' : Pexv6)
    (d' : Efab) :
    admRun instr p d ls p' d' → ∀ l, l ∈ ls → lbAdmin instr l := by
  intro h
  induction h with
  | ARnil p d => intro l hl; exact absurd hl List.not_mem_nil
  | ARcons p d l p1 d1 ls p' d' ha _ _ ih =>
    intro l0 hl0
    rcases List.mem_cons.1 hl0 with rfl | hl0
    · exact ha
    · exact ih l0 hl0

theorem admRunMono (p : Pexv6) (d : Efab) (ls : List Wlabel) (p' : Pexv6) (d' : Efab) :
    admRun false p d ls p' d' → ∀ instr, admRun instr p d ls p' d' := by
  intro h
  induction h with
  | ARnil p d => intro instr; exact .ARnil p d
  | ARcons p d l p1 d1 ls p' d' ha hs _ ih =>
    intro instr
    exact .ARcons p d l p1 d1 ls p' d' (lbAdminMono instr l ha) hs (ih instr)

theorem admRunRen (π : Nat → Nat) (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel)
    (p' : Pexv6) (d' : Efab) :
    admRun instr p d ls p' d' → admRun instr p d (ls.map (wlblRen π)) p' d' := by
  intro h
  induction h with
  | ARnil p d => exact .ARnil p d
  | ARcons p d l p1 d1 ls p' d' ha hs _ ih =>
    rw [List.map_cons, wlblRenAdmin π instr l ha]
    exact .ARcons p d l p1 d1 _ p' d' ha hs ih

/-! ## 6. Emission items and `rowDeps` -/

/-- An ITEM: one instance label with the ROW POSITION it realizes (`none`: administrative). -/
abbrev Eitem : Type := Wlabel × Option Nat

def eadm (ls : List Wlabel) : List Eitem := ls.map (fun l => (l, none))

def eitemRen (π : Nat → Nat) (it : Eitem) : Eitem := (wlblRen π it.1, it.2)

theorem eitemRenEadm (π : Nat → Nat) (ls : List Wlabel) :
    (eadm ls).map (eitemRen π) = eadm (ls.map (wlblRen π)) := by
  simp only [eadm, List.map_map]
  rfl

/-- The shape one emission BLOCK has. -/
theorem eitemRenBlock (π : Nat → Nat) (ls : List Wlabel) (l : Wlabel) (k : Nat)
    (es : List Eitem) :
    (eadm ls ++ (l, some k) :: es).map (eitemRen π)
    = eadm (ls.map (wlblRen π)) ++ (wlblRen π l, some k) :: es.map (eitemRen π) := by
  rw [List.map_append, List.map_cons, eitemRenEadm]
  rfl

/-- The label's memory role, at the INSTANCE alphabet (deviation 3: the fetch reads). -/
def elbIsR (l : Wlabel) : Bool :=
  match l with
  | LLoad .. | LExLoad .. | LRmw .. | LIFetch .. => true
  | _ => false

def elbIsW (l : Wlabel) : Bool :=
  match l with
  | LStore .. | LExStore .. | LRmw .. => true
  | _ => false

theorem elbIsRRen (π : Nat → Nat) (l : Wlabel) : elbIsR (wlblRen π l) = elbIsR l := by
  cases l <;> rfl

theorem elbIsWRen (π : Nat → Nat) (l : Wlabel) : elbIsW (wlblRen π l) = elbIsW l := by
  cases l <;> rfl

/-! ### 6.1 The dataflow state (deviation 2: `dsProv` is a total function) -/

structure WeakRvwmoConf.Dstate where
  DSt ::
  dsProv : Nat → List Nat
  dsLd : List Nat
  dsCtl : List Nat

open WeakRvwmoConf (Dstate)

def dsInit : Dstate := ⟨fun _ => [], [], []⟩

def dprov (s : Dstate) (r : Nat) : List Nat := s.dsProv r

/-- (Lean-only) `<[rd := v]> (ds_prov s)`. -/
def dprovSet (f : Nat → List Nat) (rd : Nat) (v : List Nat) : Nat → List Nat :=
  fun r => if r = rd then v else f r

def dsrcPos (s : Dstate) (x : Dsrc) : List Nat :=
  match x with
  | .DReg r => dprov s r
  | .DLdRes => s.dsLd

def dsrcsPos (s : Dstate) (xs : List Dsrc) : List Nat :=
  (xs.map (dsrcPos s)).flatten

/-- THE EDGES A WRITE AT ROW POSITION `k` EMITS: address (rule 9), data (rule 10), control
(rule 11), the instruction's earlier loads (rule 13, F5) and the SATP provenance (§4e), each
source paired with `k`, minus the self-edges (S-c). -/
def dedges (s : Dstate) (k : Nat) (asrc vsrc : List Dsrc) : List (Nat × Nat) :=
  ((dsrcsPos s asrc ++ (dsrcsPos s vsrc ++ (s.dsCtl ++ (s.dsLd ++ dprov s wsatp)))).filter
    (fun j => decide (j < k))).map (fun j => (j, k))

def WeakRvwmoConf.dstep (s : Dstate) (it : Eitem) : Dstate × List (Nat × Nat) :=
  match it.1 with
  | LSilent | LDev | LFence _ _ _ _ => (s, [])
  | LInstr => (⟨s.dsProv, [], s.dsCtl⟩, [])
  | LRegW rd srcs => (⟨dprovSet s.dsProv rd (dsrcsPos s srcs), s.dsLd, s.dsCtl⟩, [])
  | LCtrl srcs => (⟨s.dsProv, s.dsLd, s.dsCtl ++ dsrcsPos s srcs⟩, [])
  | LLoad _ _ _ _ _ | LExLoad _ _ _ _ | LIFetch _ _ =>
      match it.2 with
      | some k => (⟨s.dsProv, k :: s.dsLd, s.dsCtl⟩, [])
      | none => (s, [])
  | LStore _ _ _ asrc vsrc | LExStore _ _ _ asrc vsrc =>
      match it.2 with
      | some k => (s, dedges s k asrc vsrc)
      | none => (s, [])
  | LRmw _ _ _ _ _ asrc vsrc =>
      match it.2 with
      | some k => (⟨s.dsProv, k :: s.dsLd, s.dsCtl⟩, dedges s k asrc vsrc)
      | none => (s, [])

open WeakRvwmoConf (dstep)

def rowDepsAux (s : Dstate) (es : List Eitem) : List (Nat × Nat) :=
  match es with
  | [] => []
  | it :: es' => (dstep s it).2 ++ rowDepsAux (dstep s it).1 es'

/-- THE REGISTER-DATAFLOW RELATION of an emission. -/
def rowDeps (es : List Eitem) : List (Nat × Nat) := rowDepsAux dsInit es

/-! ### 6.2 Sanity: every edge runs from a READ position strictly below a WRITE position -/

theorem dedgesLt (s : Dstate) (k : Nat) (asrc vsrc : List Dsrc) (jk : Nat × Nat) :
    jk ∈ dedges s k asrc vsrc → jk.1 < jk.2 := by
  simp only [dedges, List.mem_map, List.mem_filter, decide_eq_true_eq]
  rintro ⟨j, ⟨_, hlt⟩, rfl⟩
  exact hlt

/-- (Lean-only) the target of a `dedges` edge is `k`. -/
theorem dedgesSnd (s : Dstate) (k : Nat) (asrc vsrc : List Dsrc) (jk : Nat × Nat) :
    jk ∈ dedges s k asrc vsrc → jk.2 = k := by
  simp only [dedges, List.mem_map]
  rintro ⟨j, _, rfl⟩
  rfl

theorem rowDepsAuxLt (s : Dstate) (es : List Eitem) (jk : Nat × Nat) :
    jk ∈ rowDepsAux s es → jk.1 < jk.2 := by
  induction es generalizing s with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons it es ih =>
    intro h
    simp only [rowDepsAux, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨l, ok⟩ := it
      cases l <;> cases ok <;> simp only [dstep, List.not_mem_nil] at h <;>
        exact dedgesLt _ _ _ _ _ h
    · exact ih _ h

theorem rowDepsLt (es : List Eitem) (jk : Nat × Nat) : jk ∈ rowDeps es → jk.1 < jk.2 :=
  rowDepsAuxLt _ _ _

/-- The TARGET of an edge is the row position of a WRITE item. -/
theorem rowDepsAuxTgt (s : Dstate) (es : List Eitem) (jk : Nat × Nat) :
    jk ∈ rowDepsAux s es → ∃ it, it ∈ es ∧ it.2 = some jk.2 ∧ elbIsW it.1 = true := by
  induction es generalizing s with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons it es ih =>
    intro h
    simp only [rowDepsAux, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨l, ok⟩ := it
      cases l <;> cases ok <;> simp only [dstep, List.not_mem_nil] at h <;>
        exact ⟨_, List.mem_cons_self .., by rw [dedgesSnd _ _ _ _ _ h], rfl⟩
    · obtain ⟨it0, hin, hpos, hw⟩ := ih _ h
      exact ⟨it0, List.mem_cons_of_mem _ hin, hpos, hw⟩

theorem rowDepsTgt (es : List Eitem) (jk : Nat × Nat) :
    jk ∈ rowDeps es → ∃ it, it ∈ es ∧ it.2 = some jk.2 ∧ elbIsW it.1 = true :=
  rowDepsAuxTgt _ _ _

/-- The SOURCE of an edge is the row position of a READ item. -/
def dsWithin (P : Nat → Prop) (s : Dstate) : Prop :=
  (∀ r j, j ∈ dprov s r → P j) ∧ (∀ j, j ∈ s.dsLd → P j) ∧ (∀ j, j ∈ s.dsCtl → P j)

def ereadOk (P : Nat → Prop) (es : List Eitem) : Prop :=
  ∀ it k, it ∈ es → it.2 = some k → elbIsR it.1 = true → P k

theorem dsWithinInit (P : Nat → Prop) : dsWithin P dsInit :=
  ⟨fun _ _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
   fun _ h => absurd h List.not_mem_nil⟩

theorem dsrcsPosWithin (P : Nat → Prop) (s : Dstate) (xs : List Dsrc) (j : Nat) :
    dsWithin P s → j ∈ dsrcsPos s xs → P j := by
  rintro ⟨hp, hl, _⟩ hj
  simp only [dsrcsPos, List.mem_flatten, List.mem_map] at hj
  obtain ⟨_, ⟨x, _, rfl⟩, hj⟩ := hj
  cases x with
  | DReg r => exact hp r j hj
  | DLdRes => exact hl j hj

theorem dsWithinPush (P : Nat → Prop) (s : Dstate) (k : Nat) :
    dsWithin P s → P k → dsWithin P ⟨s.dsProv, k :: s.dsLd, s.dsCtl⟩ := by
  rintro ⟨hp, hl, hc⟩ hk
  refine ⟨hp, ?_, hc⟩
  intro j hj
  rcases List.mem_cons.1 hj with rfl | hj
  · exact hk
  · exact hl j hj

theorem dsWithinInstr (P : Nat → Prop) (s : Dstate) :
    dsWithin P s → dsWithin P ⟨s.dsProv, [], s.dsCtl⟩ := by
  rintro ⟨hp, _, hc⟩
  exact ⟨hp, fun _ h => absurd h List.not_mem_nil, hc⟩

theorem dsWithinRegw (P : Nat → Prop) (s : Dstate) (rd : Nat) (srcs : List Dsrc) :
    dsWithin P s → dsWithin P ⟨dprovSet s.dsProv rd (dsrcsPos s srcs), s.dsLd, s.dsCtl⟩ := by
  intro hs
  obtain ⟨hp, hl, hc⟩ := hs
  refine ⟨?_, hl, hc⟩
  intro r j hj
  simp only [dprov, dprovSet] at hj
  split at hj
  · exact dsrcsPosWithin P s srcs j ⟨hp, hl, hc⟩ hj
  · exact hp r j hj

theorem dsWithinCtrl (P : Nat → Prop) (s : Dstate) (srcs : List Dsrc) :
    dsWithin P s → dsWithin P ⟨s.dsProv, s.dsLd, s.dsCtl ++ dsrcsPos s srcs⟩ := by
  intro hs
  obtain ⟨hp, hl, hc⟩ := hs
  refine ⟨hp, hl, ?_⟩
  intro j hj
  rcases List.mem_append.1 hj with hj | hj
  · exact hc j hj
  · exact dsrcsPosWithin P s srcs j ⟨hp, hl, hc⟩ hj

theorem dstepWithin (P : Nat → Prop) (s : Dstate) (it : Eitem) :
    dsWithin P s →
    (∀ k, it.2 = some k → elbIsR it.1 = true → P k) →
    dsWithin P (dstep s it).1 ∧ (∀ jk, jk ∈ (dstep s it).2 → P jk.1) := by
  intro hs hr
  have hedges : ∀ k asrc vsrc, ∀ jk, jk ∈ dedges s k asrc vsrc → P jk.1 := by
    intro k asrc vsrc jk h
    simp only [dedges, List.mem_map, List.mem_filter, List.mem_append] at h
    obtain ⟨j, ⟨hj, _⟩, rfl⟩ := h
    rcases hj with hj | hj | hj | hj | hj
    · exact dsrcsPosWithin P s _ j hs hj
    · exact dsrcsPosWithin P s _ j hs hj
    · exact hs.2.2 j hj
    · exact hs.2.1 j hj
    · exact hs.1 _ j hj
  have hnil : ∀ jk : Nat × Nat, jk ∈ ([] : List (Nat × Nat)) → P jk.1 :=
    fun _ h => absurd h List.not_mem_nil
  obtain ⟨l, ok⟩ := it
  cases l <;> cases ok <;> simp only [dstep] <;>
    first
    | exact ⟨hs, hnil⟩
    | exact ⟨hs, hedges _ _ _⟩
    | exact ⟨dsWithinInstr P s hs, hnil⟩
    | exact ⟨dsWithinRegw P s _ _ hs, hnil⟩
    | exact ⟨dsWithinCtrl P s _ hs, hnil⟩
    | exact ⟨dsWithinPush P s _ hs (hr _ rfl rfl), hnil⟩
    | exact ⟨dsWithinPush P s _ hs (hr _ rfl rfl), hedges _ _ _⟩

theorem rowDepsAuxWithin (P : Nat → Prop) (s : Dstate) (es : List Eitem) (jk : Nat × Nat) :
    dsWithin P s → ereadOk P es → jk ∈ rowDepsAux s es → P jk.1 := by
  induction es generalizing s with
  | nil => intro _ _ h; exact absurd h List.not_mem_nil
  | cons it es ih =>
    intro hs hok h
    obtain ⟨hs', he⟩ := dstepWithin P s it hs
      (fun k hk hr => hok it k (List.mem_cons_self ..) hk hr)
    simp only [rowDepsAux, List.mem_append] at h
    rcases h with h | h
    · exact he jk h
    · exact ih _ hs' (fun it0 k hin => hok it0 k (List.mem_cons_of_mem _ hin)) h

theorem rowDepsSrc (es : List Eitem) (jk : Nat × Nat) :
    jk ∈ rowDeps es → ∃ it, it ∈ es ∧ it.2 = some jk.1 ∧ elbIsR it.1 = true := by
  intro h
  exact rowDepsAuxWithin (fun j => ∃ it, it ∈ es ∧ it.2 = some j ∧ elbIsR it.1 = true)
    dsInit es jk (dsWithinInit _) (fun it k hin hpos hr => ⟨it, hin, hpos, hr⟩) h

/-! ### 6.3 `rowDeps` is ts-blind -/

theorem dstepRen (π : Nat → Nat) (s : Dstate) (it : Eitem) :
    dstep s (eitemRen π it) = dstep s it := by
  obtain ⟨l, k⟩ := it
  cases l <;> rfl

theorem rowDepsAuxRen (π : Nat → Nat) (s : Dstate) (es : List Eitem) :
    rowDepsAux s (es.map (eitemRen π)) = rowDepsAux s es := by
  induction es generalizing s with
  | nil => rfl
  | cons it es ih => simp only [List.map_cons, rowDepsAux, dstepRen, ih]

theorem rowDepsRen (π : Nat → Nat) (es : List Eitem) :
    rowDeps (es.map (eitemRen π)) = rowDeps es :=
  rowDepsAuxRen π _ _

/-! ## 7. `hartConf`: per-hart row emittability -/

inductive hemit (dv : Nat → Efab) :
    Nat → Wstate → List Lbl → Pexv6 → List Eitem → Pexv6 → Prop where
  | HEnil (k : Nat) (ws : Wstate) (p : Pexv6) : hemit dv k ws [] p [] p
  | HEone (k : Nat) (ws : Wstate) (lb : Lbl) (row : List Lbl) (p : Pexv6) (ls : List Wlabel)
      (pa : Pexv6) (da : Efab) (l : Wlabel) (p' : Pexv6) (es : List Eitem) (pfin : Pexv6) :
      admRun true p (dv k) ls pa da →
      hlblRealizes pa ws lb l →
      pstepEv pa da l p' (dv (k + 1)) →
      hemit dv (k + 1) (lblPost k ws lb) row p' es pfin →
      hemit dv k ws (lb :: row) p (eadm ls ++ (l, some k) :: es) pfin
  | HEpair (k : Nat) (ws : Wstate) (lb : Lbl) (row : List Lbl) (p : Pexv6) (ls1 : List Wlabel)
      (pa : Pexv6) (da : Efab) (l1 : Wlabel) (pm : Pexv6) (dm : Efab)
      (ls2 : List Wlabel) (pm2 : Pexv6) (dm2 : Efab) (l2 : Wlabel) (p' : Pexv6)
      (es : List Eitem) (pfin : Pexv6) :
      admRun true p (dv k) ls1 pa da →
      hlblRealizesPair pa pm2 ws lb l1 l2 →
      pstepEv pa da l1 pm dm →
      admRun false pm dm ls2 pm2 dm2 →
      pstepEv pm2 dm2 l2 p' (dv (k + 1)) →
      hemit dv (k + 1) (lblPost k ws lb) row p' es pfin →
      hemit dv k ws (lb :: row) p
        (eadm ls1 ++ (l1, some k) :: (eadm ls2 ++ (l2, some k) :: es)) pfin

/-- THE EMISSION: the item sequence and the program state it ends at. -/
structure Hemission where
  HEm ::
  emItems : List Eitem
  emFin : Pexv6

def emLabels (em : Hemission) : List Wlabel := em.emItems.map Prod.fst

def emRen (π : Nat → Nat) (em : Hemission) : Hemission :=
  ⟨em.emItems.map (eitemRen π), em.emFin⟩

theorem emLabelsRen (π : Nat → Nat) (em : Hemission) :
    emLabels (emRen π em) = (emLabels em).map (wlblRen π) := by
  simp only [emLabels, emRen, List.map_map]
  rfl

/-- `_i` is carried for the caller's benefit (the hart the row belongs to). -/
def hartConf (_i : Nat) (row : List Lbl) (p0 : Pexv6) (dv : Nat → Efab) (em : Hemission) :
    Prop :=
  hemit dv 0 wsInit row p0 em.emItems em.emFin

theorem rowWsAuxSnoc (t : Nat) (ws : Wstate) (r : List Lbl) (n : Nat) (l : Lbl) :
    r[n]? = some l →
    rowWsAux t ws (r.take (n + 1)) = lblPost (t + n) (rowWsAux t ws (r.take n)) l := by
  induction r generalizing t ws n with
  | nil => intro h; simp at h
  | cons l0 r ih =>
    intro h
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [List.take, rowWsAux, Nat.add_zero]
    | succ n =>
      simp only [List.getElem?_cons_succ] at h
      simp only [List.take, rowWsAux]
      rw [ih (t + 1) (lblPost t ws l0) n h]
      congr 1
      omega

theorem rowWsStep (row : List Lbl) (n : Nat) (l : Lbl) :
    row[n]? = some l → rowWs row (n + 1) = lblPost n (rowWs row n) l := by
  intro h
  unfold rowWs
  rw [rowWsAuxSnoc 0 _ row n l h, Nat.zero_add]

/-! ### 7.1 The row events' kinds, read off the emission -/

theorem hlblRealizesKind (p : Pexv6) (ws : Wstate) (lb : Lbl) (l : Wlabel) :
    hlblRealizes p ws lb l →
    (elbIsR l = true → lbIsR lb = true) ∧ (elbIsW l = true → lbIsW lb = true) := by
  rintro ⟨_, _, _, hpr⟩
  cases l <;> simp only [projLbl, Option.some.injEq, reduceCtorEq] at hpr <;> subst hpr <;>
    exact ⟨fun h => by first | rfl | exact h, fun h => by first | rfl | exact h⟩

theorem hemitTagLbl (dv : Nat → Efab) (k : Nat) (ws : Wstate) (row : List Lbl) (p : Pexv6)
    (es : List Eitem) (pfin : Pexv6) (it : Eitem) (j : Nat) :
    hemit dv k ws row p es pfin → it ∈ es → it.2 = some j →
    ∃ lb, k ≤ j ∧ row[j - k]? = some lb ∧
      (elbIsR it.1 = true → lbIsR lb = true) ∧ (elbIsW it.1 = true → lbIsW lb = true) := by
  intro h
  induction h with
  | HEnil k ws p => intro hit; exact absurd hit List.not_mem_nil
  | HEone k ws lb row p ls pa da l p' es pfin _ hre _ _ ih =>
    intro hit hj
    rcases List.mem_append.1 hit with hit | hit
    · simp only [eadm, List.mem_map] at hit
      obtain ⟨_, _, rfl⟩ := hit
      simp at hj
    rcases List.mem_cons.1 hit with rfl | hit
    · simp only [Option.some.injEq] at hj
      subst hj
      obtain ⟨hr, hw⟩ := hlblRealizesKind pa ws lb l hre
      exact ⟨lb, Nat.le_refl _, by simp, hr, hw⟩
    · obtain ⟨lb0, hle, hlk, hr, hw⟩ := ih hit hj
      refine ⟨lb0, by omega, ?_, hr, hw⟩
      rw [show j - k = (j - (k + 1)) + 1 by omega, List.getElem?_cons_succ]
      exact hlk
  | HEpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin _ hre _ _ _ _ ih =>
    intro hit hj
    obtain ⟨aq, rl, base, tvs, data, asrc1, asrc2, vsrc2, rfl, rfl, _, _, hlb⟩ := hre
    rcases List.mem_append.1 hit with hit | hit
    · simp only [eadm, List.mem_map] at hit
      obtain ⟨_, _, rfl⟩ := hit
      simp at hj
    rcases List.mem_cons.1 hit with rfl | hit
    · simp only [Option.some.injEq] at hj
      subst hj
      exact ⟨lb, Nat.le_refl _, by simp, fun _ => by rw [hlb]; rfl, fun _ => by rw [hlb]; rfl⟩
    rcases List.mem_append.1 hit with hit | hit
    · simp only [eadm, List.mem_map] at hit
      obtain ⟨_, _, rfl⟩ := hit
      simp at hj
    rcases List.mem_cons.1 hit with rfl | hit
    · simp only [Option.some.injEq] at hj
      subst hj
      exact ⟨lb, Nat.le_refl _, by simp, fun _ => by rw [hlb]; rfl, fun _ => by rw [hlb]; rfl⟩
    · obtain ⟨lb0, hle, hlk, hr, hw⟩ := ih hit hj
      refine ⟨lb0, by omega, ?_, hr, hw⟩
      rw [show j - k = (j - (k + 1)) + 1 by omega, List.getElem?_cons_succ]
      exact hlk

theorem hartConfTagLbl (i : Nat) (row : List Lbl) (p0 : Pexv6) (dv : Nat → Efab)
    (em : Hemission) (it : Eitem) (j : Nat) :
    hartConf i row p0 dv em → it ∈ em.emItems → it.2 = some j →
    ∃ lb, row[j]? = some lb ∧
      (elbIsR it.1 = true → lbIsR lb = true) ∧ (elbIsW it.1 = true → lbIsW lb = true) := by
  intro hem hit hj
  obtain ⟨lb, _, hlk, hr, hw⟩ := hemitTagLbl dv 0 wsInit row p0 _ _ it j hem hit hj
  rw [Nat.sub_zero] at hlk
  exact ⟨lb, hlk, hr, hw⟩

/-- THE `gdepsWf` SHAPE, at row level. -/
theorem hartConfRowDepsWf (i : Nat) (row : List Lbl) (p0 : Pexv6) (dv : Nat → Efab)
    (em : Hemission) (jk : Nat × Nat) :
    hartConf i row p0 dv em → jk ∈ rowDeps em.emItems →
    jk.1 < jk.2 ∧
    (∃ lb, row[jk.1]? = some lb ∧ lbIsR lb = true) ∧
    (∃ lb, row[jk.2]? = some lb ∧ lbIsW lb = true) := by
  intro hem hjk
  refine ⟨rowDepsLt _ _ hjk, ?_, ?_⟩
  · obtain ⟨it, hit, hpos, hr⟩ := rowDepsSrc _ _ hjk
    obtain ⟨lb, hlk, hrr, _⟩ := hartConfTagLbl i row p0 dv em it jk.1 hem hit hpos
    exact ⟨lb, hlk, hrr hr⟩
  · obtain ⟨it, hit, hpos, hw⟩ := rowDepsTgt _ _ hjk
    obtain ⟨lb, hlk, _, hww⟩ := hartConfTagLbl i row p0 dv em it jk.2 hem hit hpos
    exact ⟨lb, hlk, hww hw⟩

/-! ### 7.2 Stability (1): the normalization orbit (no side condition on `π`) -/

theorem hemitRen (π : Nat → Nat) (dv : Nat → Efab) (k : Nat) (ws : Wstate) (row : List Lbl)
    (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemit dv k ws row p es pfin →
    ∀ ws', ws'.wRelp = ws.wRelp →
    hemit dv k ws' (row.map (lblRen π)) p (es.map (eitemRen π)) pfin := by
  intro h
  induction h with
  | HEnil k ws p => intro _ _; exact .HEnil _ _ _
  | HEone k ws lb row p ls pa da l p' es pfin har hre hst _ ih =>
    intro ws' hrelp
    rw [eitemRenBlock, List.map_cons]
    have hlat := hre.2.1
    have hrf := hre.2.2.1
    exact .HEone _ _ _ _ _ _ _ _ _ _ _ _ (admRunRen π true _ _ _ _ _ har)
      (hlblRealizesRen π pa ws ws' lb l hrelp hre) (pstepEvWren π _ _ _ _ _ hlat hrf hst)
      (ih _ (lblPostRelpRen π k ws ws' lb hrelp))
  | HEpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin har1 hre hst1 har2 hst2 _
      ih =>
    intro ws' hrelp
    rw [eitemRenBlock, eitemRenBlock, List.map_cons]
    have hre' := hlblRealizesPairRen π pa pm2 ws ws' lb l1 l2 hrelp hre
    obtain ⟨aq, rl, base, tvs, data, asrc1, asrc2, vsrc2, rfl, rfl, _, _, _⟩ := hre
    exact .HEpair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (admRunRen π true _ _ _ _ _ har1) hre'
      (pstepEvWren π _ _ _ _ _ trivial trivial hst1) (admRunRen π false _ _ _ _ _ har2)
      (pstepEvWren π _ _ _ _ _ trivial trivial hst2)
      (ih _ (lblPostRelpRen π k ws ws' _ hrelp))

theorem hartConfRen (π : Nat → Nat) (i : Nat) (row : List Lbl) (p0 : Pexv6)
    (dv : Nat → Efab) (em : Hemission) :
    hartConf i row p0 dv em → hartConf i (row.map (lblRen π)) p0 dv (emRen π em) :=
  fun hem => hemitRen π dv 0 wsInit row p0 _ _ hem wsInit rfl

/-! ### 7.3 Stability (2): prefix restriction (the fabric parameter is unchanged) -/

/-- A prefix inside one emission BLOCK. -/
theorem prefixBlock {A : Type _} (a : List A) (x : A) (b c : List A) :
    b <+: c → a ++ x :: b <+: a ++ x :: c := by
  rintro ⟨t, rfl⟩
  exact ⟨t, by simp⟩

theorem hemitPrefix (dv : Nat → Efab) (k : Nat) (ws : Wstate) (row : List Lbl) (p : Pexv6)
    (es : List Eitem) (pfin : Pexv6) :
    hemit dv k ws row p es pfin →
    ∀ n, ∃ es' pfin', es' <+: es ∧ hemit dv k ws (row.take n) p es' pfin' := by
  intro h
  induction h with
  | HEnil k ws p =>
    intro n
    exact ⟨[], p, List.nil_prefix, by rw [List.take_nil]; exact .HEnil _ _ _⟩
  | HEone k ws lb row p ls pa da l p' es pfin har hre hst _ ih =>
    intro n
    cases n with
    | zero => exact ⟨[], p, List.nil_prefix, .HEnil _ _ _⟩
    | succ n =>
      obtain ⟨es', pfin', hpre, hem'⟩ := ih n
      exact ⟨eadm ls ++ (l, some k) :: es', pfin', prefixBlock _ _ _ _ hpre,
        by rw [List.take_succ_cons]; exact .HEone _ _ _ _ _ _ _ _ _ _ _ _ har hre hst hem'⟩
  | HEpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin har1 hre hst1 har2 hst2 _
      ih =>
    intro n
    cases n with
    | zero => exact ⟨[], p, List.nil_prefix, .HEnil _ _ _⟩
    | succ n =>
      obtain ⟨es', pfin', hpre, hem'⟩ := ih n
      exact ⟨eadm ls1 ++ (l1, some k) :: (eadm ls2 ++ (l2, some k) :: es'), pfin',
        prefixBlock _ _ _ _ (prefixBlock _ _ _ _ hpre),
        by rw [List.take_succ_cons]
           exact .HEpair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ har1 hre hst1 har2 hst2 hem'⟩

theorem hartConfPrefix (i : Nat) (row : List Lbl) (p0 : Pexv6) (dv : Nat → Efab)
    (em : Hemission) (n : Nat) :
    hartConf i row p0 dv em →
    ∃ em', hartConf i (row.take n) p0 dv em' ∧ em'.emItems <+: em.emItems := by
  intro hem
  obtain ⟨es', pfin', hpre, hem'⟩ := hemitPrefix dv 0 wsInit row p0 _ _ hem n
  exact ⟨⟨es', pfin'⟩, hem', hpre⟩

/-! ## 8. The conformance bundle -/

def gdexecConf (boot : Nat → Pexv6) (dvp : Nat → Nat → Efab) (GD : Gdexec) : Prop :=
  ∀ i row, GD.gdG.gxProg[i]? = some row →
    ∃ em, hartConf i row (boot i) (dvp i) em ∧
      ∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ GD.gdDeps

/-- THE CONFORMANCE EDGES SATISFY `gdepsWf`'s clause (per edge). -/
theorem gdexecConfDepsWf (boot : Nat → Pexv6) (dvp : Nat → Nat → Efab) (GD : Gdexec)
    (i : Nat) (row : List Lbl) (em : Hemission) (jk : Nat × Nat) :
    GD.gdG.gxProg[i]? = some row →
    hartConf i row (boot i) (dvp i) em →
    jk ∈ rowDeps em.emItems →
    (i, jk.1).1 = (i, jk.2).1 ∧ (i, jk.1).2 < (i, jk.2).2 ∧
    glblIs GD.gdG (i, jk.1) lbIsR ∧ glblIs GD.gdG (i, jk.2) lbIsW := by
  intro hrow hem hjk
  obtain ⟨hlt, ⟨lb1, hl1, hr1⟩, ⟨lb2, hl2, hw2⟩⟩ :=
    hartConfRowDepsWf i row (boot i) (dvp i) em jk hem hjk
  refine ⟨rfl, hlt, ⟨lb1, ?_, hr1⟩, ⟨lb2, ?_, hw2⟩⟩
  · simp only [gxLbl, hrow, Option.bind_some]; exact hl1
  · simp only [gxLbl, hrow, Option.bind_some]; exact hl2

/-- THE ORBIT TRANSPORT. -/
theorem gdexecConfRen (π : Nat → Nat) (boot : Nat → Pexv6) (dvp : Nat → Nat → Efab)
    (GD GD' : Gdexec) :
    rowsRel π GD.gdG GD'.gdG →
    GD'.gdDeps = GD.gdDeps →
    gdexecConf boot dvp GD → gdexecConf boot dvp GD' := by
  intro hrr hdeps hconf i row' hrow'
  obtain ⟨_, hprog, _⟩ := hrr
  rw [hprog, List.getElem?_map] at hrow'
  cases hrow0 : GD.gdG.gxProg[i]? with
  | none => rw [hrow0] at hrow'; simp at hrow'
  | some row =>
    rw [hrow0] at hrow'
    simp only [Option.map_some, Option.some.injEq] at hrow'
    subst hrow'
    obtain ⟨em, hem, hdep⟩ := hconf i row hrow0
    refine ⟨emRen π em, hartConfRen π i row (boot i) (dvp i) em hem, ?_⟩
    intro jk hjk
    rw [hdeps]
    apply hdep
    simp only [emRen] at hjk
    rw [rowDepsRen] at hjk
    exact hjk

/-! ## 9. Smoke tests -/

/-- The load;regw;store chain of RVWMO rule 10. -/
theorem rowDepsChain :
    rowDeps [ (LInstr, none),
              (LLoad false false 0 [(0, 0#8)] [], some 0),
              (LRegW 5 [.DLdRes], none),
              (LInstr, none),
              (LStore false 8 [0#8] [.DReg 5] [], some 1) ]
    = [(0, 1)] := by decide

/-- F5' — transitive provenance through load addresses. -/
theorem rowDepsAddrChain :
    rowDeps [ (LInstr, none),
              (LLoad false false 0 [(0, 0#8)] [], some 0),
              (LRegW 1 [.DLdRes, .DReg 9], none),
              (LInstr, none),
              (LLoad false false 8 [(1, 0#8)] [], some 1),
              (LRegW 2 [.DLdRes, .DReg 1], none),
              (LInstr, none),
              (LStore false 16 [0#8] [] [.DReg 2], some 2) ]
    = [(1, 2), (0, 2)] := by decide

/-- THE "BEFORE": with the pre-F5' emission the first load is not a dep source. -/
theorem rowDepsAddrChainBefore :
    rowDeps [ (LInstr, none),
              (LLoad false false 0 [(0, 0#8)] [], some 0),
              (LRegW 1 [.DLdRes], none),
              (LInstr, none),
              (LLoad false false 8 [(1, 0#8)] [], some 1),
              (LRegW 2 [.DLdRes], none),
              (LInstr, none),
              (LStore false 16 [0#8] [] [.DReg 2], some 2) ]
    = [(1, 2)] := by decide

/-- Scope note (S-c): the exclusive pair's internal edge is filtered out. -/
theorem rowDepsAmoSelfedge :
    rowDeps [ (LExLoad false 0 [(0, 0#8)] [], some 0),
              (LRegW 5 [.DLdRes], none),
              (LExStore false 0 [0#8] [] [.DReg 5], some 0) ]
    = [] := by decide

/-- THE W-TV ARM (rule 13): within one instruction the load feeds the store. -/
theorem rowDepsWtv :
    rowDeps [ (LInstr, none),
              (LLoad false false 0 [(0, 0#8)] [], some 0),
              (LStore false 8 [0#8] [] [], some 1) ]
    = [(0, 1)] := by decide

/-- ... and the `LInstr` reset cuts it. -/
theorem rowDepsWtvReset :
    rowDeps [ (LInstr, none),
              (LLoad false false 0 [(0, 0#8)] [], some 0),
              (LInstr, none),
              (LStore false 8 [0#8] [] [], some 1) ]
    = [] := by decide

/-- THE SATP-PROVENANCE EDGE (route-b §4e / DEC-5). -/
theorem rowDepsSatpChain :
    rowDeps [ (LInstr, none),
              (LLoad false false 0 [(0, 0#8)] [], some 0),
              (LRegW 10 [.DLdRes], none),
              (LInstr, none),
              (LRegW wsatp [.DReg 10], none),
              (LInstr, none),
              (LStore false 8 [0#8] [] [], some 1) ]
    = [(0, 1)] := by decide

/-- The twin without the `csrw`: no edge. -/
theorem rowDepsSatpChainBefore :
    rowDeps [ (LInstr, none),
              (LLoad false false 0 [(0, 0#8)] [], some 0),
              (LRegW 10 [.DLdRes], none),
              (LInstr, none),
              (LInstr, none),
              (LStore false 8 [0#8] [] [], some 1) ]
    = [] := by decide

/-- `csrr rd,satp` transfers the context's provenance; a later `csrw satp` overwrites it. -/
theorem rowDepsSatpRead :
    rowDeps [ (LInstr, none),
              (LLoad false false 0 [(0, 0#8)] [], some 0),
              (LRegW 10 [.DLdRes], none),
              (LInstr, none),
              (LRegW wsatp [.DReg 10], none),
              (LInstr, none),
              (LRegW 14 [.DReg wsatp], none),
              (LInstr, none),
              (LLoad false false 8 [(1, 0#8)] [], some 1),
              (LRegW 11 [.DLdRes], none),
              (LInstr, none),
              (LRegW wsatp [.DReg 11], none),
              (LInstr, none),
              (LStore false 16 [0#8] [.DReg 14] [], some 2) ]
    = [(0, 2), (1, 2)] := by decide

/-- CONTROL THROUGH `sepc` (DEC-6). -/
theorem rowDepsSretChain :
    rowDeps [ (LInstr, none),
              (LLoad false false 0 [(0, 0#8)] [], some 0),
              (LRegW 10 [.DLdRes], none),
              (LInstr, none),
              (LRegW (wcsr SEPC) [.DReg 10], none),
              (LInstr, none),
              (LCtrl [.DReg (wcsr SEPC)], none),
              (LInstr, none),
              (LStore false 8 [0#8] [] [], some 1) ]
    = [(0, 1)] := by decide

/-- The twin without the `csrw sepc`: no dependency. -/
theorem rowDepsSretChainBefore :
    rowDeps [ (LInstr, none),
              (LLoad false false 0 [(0, 0#8)] [], some 0),
              (LRegW 10 [.DLdRes], none),
              (LInstr, none),
              (LInstr, none),
              (LCtrl [.DReg (wcsr SEPC)], none),
              (LInstr, none),
              (LStore false 8 [0#8] [] [], some 1) ]
    = [] := by decide

/-- THE TWO-DESTINATION FORM (`csrrci a5,sstatus,2`, DEC-6). -/
theorem rowDepsCsrReadback :
    rowDeps [ (LInstr, none),
              (LLoad false false 0 [(0, 0#8)] [], some 0),
              (LRegW 15 [.DLdRes], none),
              (LInstr, none),
              (LRegW (wcsr MSTATUS) [.DReg 15], none),
              (LInstr, none),
              (LRegW (wcsr MSTATUS) [.DReg (wcsr MSTATUS)], none),
              (LRegW 15 [.DReg (wcsr MSTATUS)], none),
              (LInstr, none),
              (LStore false 8 [0#8] [.DReg 15] [], some 1) ]
    = [(0, 1)] := by decide

/-- The empty row is emittable. -/
theorem hartConfNil (i : Nat) (p0 : Pexv6) (dv : Nat → Efab) :
    hartConf i [] p0 dv ⟨[], p0⟩ :=
  .HEnil _ _ _

end Weak
