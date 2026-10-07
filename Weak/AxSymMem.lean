/-
Weak: **the symbolic WPd engine X extended to DATA LOADS and STORES** (slice 3 of
`AxSymEngine*`; nothing existing is edited).

Rocq: `iris/AxSymMem.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 THE CERTIFICATE `EvD img dok kind QE Q d m t`: `EvA` plus ONE data event per instruction,
tracked by the index `d : AxSymMem.Dstate` (`DPend` = the data event is still to come,
`DDone vs` = it happened with bytes `vs`):
- a DATA READ (`kind = true`) at a plain, non-device, non-latest RAM `memRead` whose request
  satisfies `dok` (the regime's data region) is DEMONIC: the continuation must hold for EVERY
  answer `vs` of the right length and moves `DPend ↦ DDone vs`;
- a DATA WRITE (`kind = false`) at a plain RAM `memWrite` moves `DPend ↦ DDone (wbytes n v)` —
  the row validates the stored bytes itself (`AStepWrite`: `wlWdata l = lblData lb`);
- page-table / text reads stay IMAGE reads (answered from the fixed image, D3), in any `d`;
  every other node is `EvA`'s.
Kit: `EvDMono`, `EvDBind(0)`, `EvDTryCatch`, `EvDLiftRAny`, `EvDCatchEarlyReturn`, `EvDOfEvA`
(every `EvA` fact embeds, at the same `d`), `EvDOfEvA'`.
§2 THE BRIDGE `wpdOfEvD(M)` / `wpdInstrOfEvD(M)`: the fine-row-end bridge of `AxSymEngine3`
(`Hmid`, `Hb`) with two new node lemmas `wpdDreadNode(M)` / `wpdDwriteNode(M)`.  The DATA
EVENT'S FLOW is a CALLER RESOURCE `FldM … Out` / `FstM … Out` quantified over EVERY row
position `k`, handing an OUTPUT `Out k vs` to the continuation.  `DResM d` is the resource for
state `d`: `DResM DPend = FkM`, `DResM (DDone vs) = ∃ k, Out k vs`.  The one degenerate graph
where a plain load node matches an RMW row item (`aidentAdvRd = 0`) is refuted by the instance
premise `HnoRmw`.

## Deviations from Rocq

1. O2 STAGE C (as `AxSymEngine3` deviation 1, `AxLdspWpd` deviation 1).  The section premise
   `Hloc` is DROPPED (the bridge's fetch is a pinned admin step at the same row position), and
   so is `Hntext : ∀ a n, dok a n → 0 < n ∧ ¬ ax_text a` (there is no `ax_text`/`AStepFetch`;
   Rocq used it only to refute `AStepFetch` at a data read).  In its place `EvD.evdDrd` takes
   `(classify req.access_kind).akIfetch = false` (a RAM read node's only non-read step is the
   admin `LIFetch` of an `akIfetch` node).  `EvD.evdMrd` drops Rocq's `ak_coh = false`, as
   `EvA.evMrd` (it is `wpdMreadNode3M`: a fetch at `k`, a graph read to `k + 1`).  Premises of
   §2: `G HG Hmid Htext Hflow HnoRmw` (+ `Out`) after `M img dok kind i Φ cpu`.
2. LEAN-SAIL WRITE VALUES ARE `Option` (`AxEpiLedgerSd.storeNodePstep`): `EvD.evdDwr` takes
   `v` with `req.value = some v` and moves to `DDone (WeakInterpProj.wbytes n v)`; the store's
   answer is `.Ok (some true)` (Rocq `inl None`).  Read answers `.Ok (wordOfBytes n vs, none)`.
3. THE PINS (`AxRunClose` deviation 1): `seip_reg` ↦ `AxRunClose.pinReg`; Q7: `EvD.evdIa` takes
   `sfAnnB n w = false` (as `EvA.evIa`); extra outcomes ↦ `.impure (.error e)` (`evdExt`);
   `Defs.try_catch` ↦ `PreSail.tryCatchAll`; `EvDLiftRAny` is stated on `ExceptT.run (liftM m)`
   (result `.ok x ↦ Q`, `.error _` excluded; failures stay failures, mapped by `HE`), and
   `EvDCatchEarlyReturn` as `EvACatchEarlyReturn` (AxSymEngine deviation 4).
4. Types as `AxSymEngine` deviation 5.  `dstate` is in the duplicated-name table:
   `AxSymMem.Dstate` (constructors `.DPend`/`.DDone`).  Rocq's §2 `Definition … := …M
   rvwmo_cat_consistent` ↦ `Fld`/`Fst` defs, `Fk`/`DRes` abbrevs (Rocq notations), and
   theorems restating the `…M` lemmas at `rvwmoCatConsistent` (with `wpd`).  The defs
   `dflowO`/`rowRd`/`rowWr`/`FldM`/`FstM`/`FkM`/`DResM` take their Rocq section variables
   explicitly (`FldM M dok i Out`, `DResM M dok kind i Out d`, `dflowO i GD k O`,
   `rowRd i GD k base n`).

**Rocq → Lean name map.**  `dstate` `AxSymMem.Dstate` (`DPend`, `DDone`), `EvD` `EvD`
(constructors `evd_ret` `evdRet`, `evd_rd` `evdRd`, `evd_wr` `evdWr`, `evd_mrd` `evdMrd`,
`evd_drd` `evdDrd`, `evd_dwr` `evdDwr`, `evd_ia` `evdIa`, `evd_ba` `evdBa`, `evd_co` `evdCo`,
`evd_tl` `evdTl`, `evd_te` `evdTe`, `evd_rx` `evdRx`, `evd_ts` `evdTs`, `evd_tx` `evdTx`,
`evd_cc` `evdCc`, `evd_msg` `evdMsg`, `evd_gcc` `evdGcc`, `evd_ext` `evdExt`), `EvD_mono`
`EvDMono`, `EvD_bind` `EvDBind`, `EvD_bind0` `EvDBind0`, `EvD_try_catch` `EvDTryCatch`,
`EvD_liftR_any` `EvDLiftRAny`, `EvD_catch_early_return` `EvDCatchEarlyReturn`, `EvD_of_EvA`
`EvDOfEvA`, `EvD_of_EvA'` `EvDOfEvA'`, `dflowO` `dflowO`, `row_rd` `rowRd`, `row_wr` `rowWr`,
`FldM` `FldM`, `FstM` `FstM`, `FkM` `FkM`, `DResM` `DResM`, `wpd_dread_nodeM` `wpdDreadNodeM`,
`wpd_dwrite_nodeM` `wpdDwriteNodeM`, `wpd_of_EvDM` `wpdOfEvDM`, `wpd_instr_of_EvDM`
`wpdInstrOfEvDM`, `Fld` `Fld`, `Fst` `Fst`, `Fk` `Fk`, `DRes` `DRes`, `wpd_dread_node`
`wpdDreadNode`, `wpd_dwrite_node` `wpdDwriteNode`, `wpd_of_EvD` `wpdOfEvD`, `wpd_instr_of_EvD`
`wpdInstrOfEvD`.

**Dropped:** nothing (Rocq 27 definitions/lemmas + 2 notations + the `evd_ctor`/`silent_ps_d`
Ltacs, replaced by explicit cases / `AxSymEngine3.wpdSilentNode3M`; Lean 29).  The section
premise `Hntext` is dropped (deviation 1).
**Not ported:** the `Print Assumptions` line (the lint's axiom check covers it).
-/
import Weak.AxSymEngine3
import Weak.AxEpiLedgerSd
import Weak.AxLdspWpd

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! # 1. The certificate `EvD` -/

/-- The data-event state: still to come, or done with these bytes. -/
inductive AxSymMem.Dstate where
  | DPend
  | DDone (vs : List (BitVec 8))

/-- THE CERTIFICATE (see the header).  `dok base n`: the regime's data region; `kind = true`:
the instruction's data event is a load, `false`: a store. -/
inductive EvD (img : Image) (dok : Int → Nat → Prop) (kind : Bool) {X : Type}
    (QE : AxSymMem.Dstate → Sail.Error exception → ExecSt → Prop)
    (Q : AxSymMem.Dstate → X → ExecSt → Prop) : AxSymMem.Dstate → SailM X → ExecSt → Prop where
  | evdRet (d : AxSymMem.Dstate) (x : X) (t : ExecSt) : Q d x t → EvD img dok kind QE Q d (.pure x) t
  | evdRd (d : AxSymMem.Dstate) (r : Register) (k : RegisterType r → SailM X) (t : ExecSt) :
      (AxRunClose.pinReg r → ∀ v, EvD img dok kind QE Q d (k v) t) →
      (¬ AxRunClose.pinReg r → EvD img dok kind QE Q d (k (t.regs r)) t) →
      EvD img dok kind QE Q d (.impure (.ok (.regRead r)) k) t
  | evdWr (d : AxSymMem.Dstate) (r : Register) (v : RegisterType r) (k : PUnit → SailM X)
      (t : ExecSt) :
      ¬ AxRunClose.pinReg r → EvD img dok kind QE Q d (k PUnit.unit) (t.setReg r v) →
      EvD img dok kind QE Q d (.impure (.ok (.regWrite r v)) k) t
  | evdMrd (d : AxSymMem.Dstate) (n va : Nat)
      (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt)
      (vs : List (BitVec 8)) :
      devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      imgBytes img (paZ req.pa) n = some vs →
      EvD img dok kind QE Q d (k (.Ok (wordOfBytes n vs, none))) t →
      EvD img dok kind QE Q d (.impure (.ok (.memRead n va req)) k) t
  | evdDrd (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt) :
      kind = true → devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      (classify req.access_kind).akIfetch = false →
      dok (paZ req.pa) n →
      (∀ vs : List (BitVec 8), vs.length = n →
        EvD img dok kind QE Q (.DDone vs) (k (.Ok (wordOfBytes n vs, none))) t) →
      EvD img dok kind QE Q .DPend (.impure (.ok (.memRead n va req)) k) t
  | evdDwr (n va : Nat) (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (Option Bool) Arch.abort → SailM X) (t : ExecSt) (v : BitVec (8 * n)) :
      kind = false → devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      req.value = some v →
      dok (paZ req.pa) n →
      EvD img dok kind QE Q (.DDone (WeakInterpProj.wbytes n v)) (k (.Ok (some true))) t →
      EvD img dok kind QE Q .DPend (.impure (.ok (.memWrite n va req)) k) t
  | evdIa (d : AxSymMem.Dstate) (n : Nat) (w : BitVec n) (k : Unit → SailM X) (t : ExecSt) :
      sfAnnB n w = false → EvD img dok kind QE Q d (k ()) t →
      EvD img dok kind QE Q d (.impure (.ok (.instrAnnounce n w)) k) t
  | evdBa (d : AxSymMem.Dstate) (n : Nat) (a : BitVec n) (k : Unit → SailM X) (t : ExecSt) :
      EvD img dok kind QE Q d (k ()) t →
      EvD img dok kind QE Q d (.impure (.ok (.branchAnnounce n a)) k) t
  | evdCo (d : AxSymMem.Dstate) (c : Arch.cache_op) (k : Unit → SailM X) (t : ExecSt) :
      EvD img dok kind QE Q d (k ()) t → EvD img dok kind QE Q d (.impure (.ok (.cacheOp c)) k) t
  | evdTl (d : AxSymMem.Dstate) (c : Arch.tlb_op) (k : Unit → SailM X) (t : ExecSt) :
      EvD img dok kind QE Q d (k ()) t → EvD img dok kind QE Q d (.impure (.ok (.tlbi c)) k) t
  | evdTe (d : AxSymMem.Dstate) (f : Arch.fault) (k : Unit → SailM X) (t : ExecSt) :
      EvD img dok kind QE Q d (k ()) t →
      EvD img dok kind QE Q d (.impure (.ok (.takeException f)) k) t
  | evdRx (d : AxSymMem.Dstate) (a : Arch.pa) (k : Unit → SailM X) (t : ExecSt) :
      EvD img dok kind QE Q d (k ()) t →
      EvD img dok kind QE Q d (.impure (.ok (.returnException a)) k) t
  | evdTs (d : AxSymMem.Dstate) (a : Arch.trans_start) (k : Unit → SailM X) (t : ExecSt) :
      EvD img dok kind QE Q d (k ()) t →
      EvD img dok kind QE Q d (.impure (.ok (.translationStart a)) k) t
  | evdTx (d : AxSymMem.Dstate) (a : Arch.trans_end) (k : Unit → SailM X) (t : ExecSt) :
      EvD img dok kind QE Q d (k ()) t →
      EvD img dok kind QE Q d (.impure (.ok (.translationEnd a)) k) t
  | evdCc (d : AxSymMem.Dstate) (k : Unit → SailM X) (t : ExecSt) :
      EvD img dok kind QE Q d (k ()) t → EvD img dok kind QE Q d (.impure (.ok .cycleCount) k) t
  | evdMsg (d : AxSymMem.Dstate) (a : String) (k : Unit → SailM X) (t : ExecSt) :
      EvD img dok kind QE Q d (k ()) t → EvD img dok kind QE Q d (.impure (.ok (.message a)) k) t
  | evdGcc (d : AxSymMem.Dstate) (k : Nat → SailM X) (t : ExecSt) :
      EvD img dok kind QE Q d (k (0 : Nat)) t →
      EvD img dok kind QE Q d (.impure (.ok .getCycleCount) k) t
  | evdExt (d : AxSymMem.Dstate) (e : Sail.Error exception) (k : Empty → SailM X) (t : ExecSt) :
      QE d e t → EvD img dok kind QE Q d (.impure (.error e) k) t

section evd
variable (img : Image) (dok : Int → Nat → Prop) (kind : Bool)

theorem EvDMono {X : Type} (QE QE' : AxSymMem.Dstate → Sail.Error exception → ExecSt → Prop)
    (Q Q' : AxSymMem.Dstate → X → ExecSt → Prop) (d : AxSymMem.Dstate) (m : SailM X) (t : ExecSt) :
    (∀ d e t', QE d e t' → QE' d e t') → (∀ d x t', Q d x t' → Q' d x t') →
    EvD img dok kind QE Q d m t → EvD img dok kind QE' Q' d m t := by
  intro HE HQ h
  induction h with
  | evdRet d x t h => exact .evdRet d x t (HQ d x t h)
  | evdExt d e k t h => exact .evdExt d e k t (HE d e t h)
  | evdRd d r k t _ _ ihs ihn => exact .evdRd d r k t ihs ihn
  | evdWr d r v k t hr _ ih => exact .evdWr d r v k t hr ih
  | evdMrd d n va req k t vs h1 h2 h3 _ ih => exact .evdMrd d n va req k t vs h1 h2 h3 ih
  | evdDrd n va req k t h1 h2 h3 h4 h5 _ ih => exact .evdDrd n va req k t h1 h2 h3 h4 h5 ih
  | evdDwr n va req k t v h1 h2 h3 h4 h5 _ ih => exact .evdDwr n va req k t v h1 h2 h3 h4 h5 ih
  | evdIa d n w k t hs _ ih => exact .evdIa d n w k t hs ih
  | evdBa d n a k t _ ih => exact .evdBa d n a k t ih
  | evdCo d c k t _ ih => exact .evdCo d c k t ih
  | evdTl d c k t _ ih => exact .evdTl d c k t ih
  | evdTe d f k t _ ih => exact .evdTe d f k t ih
  | evdRx d a k t _ ih => exact .evdRx d a k t ih
  | evdTs d a k t _ ih => exact .evdTs d a k t ih
  | evdTx d a k t _ ih => exact .evdTx d a k t ih
  | evdCc d k t _ ih => exact .evdCc d k t ih
  | evdMsg d a k t _ ih => exact .evdMsg d a k t ih
  | evdGcc d k t _ ih => exact .evdGcc d k t ih

theorem EvDBind {X Y : Type} (QE : AxSymMem.Dstate → Sail.Error exception → ExecSt → Prop)
    (Q : AxSymMem.Dstate → Y → ExecSt → Prop) (m : SailM X) (f : X → SailM Y)
    (d : AxSymMem.Dstate) (t : ExecSt) :
    EvD img dok kind QE (fun d' x t' => EvD img dok kind QE Q d' (f x) t') d m t →
    EvD img dok kind QE Q d (m >>= f) t := by
  intro h
  induction h with
  | evdRet d x t h => exact h
  | evdExt d e k t h => exact .evdExt d e _ t h
  | evdRd d r k t _ _ ihs ihn => exact .evdRd d r _ t ihs ihn
  | evdWr d r v k t hr _ ih => exact .evdWr d r v _ t hr ih
  | evdMrd d n va req k t vs h1 h2 h3 _ ih => exact .evdMrd d n va req _ t vs h1 h2 h3 ih
  | evdDrd n va req k t h1 h2 h3 h4 h5 _ ih => exact .evdDrd n va req _ t h1 h2 h3 h4 h5 ih
  | evdDwr n va req k t v h1 h2 h3 h4 h5 _ ih => exact .evdDwr n va req _ t v h1 h2 h3 h4 h5 ih
  | evdIa d n w k t hs _ ih => exact .evdIa d n w _ t hs ih
  | evdBa d n a k t _ ih => exact .evdBa d n a _ t ih
  | evdCo d c k t _ ih => exact .evdCo d c _ t ih
  | evdTl d c k t _ ih => exact .evdTl d c _ t ih
  | evdTe d f k t _ ih => exact .evdTe d f _ t ih
  | evdRx d a k t _ ih => exact .evdRx d a _ t ih
  | evdTs d a k t _ ih => exact .evdTs d a _ t ih
  | evdTx d a k t _ ih => exact .evdTx d a _ t ih
  | evdCc d k t _ ih => exact .evdCc d _ t ih
  | evdMsg d a k t _ ih => exact .evdMsg d a _ t ih
  | evdGcc d k t _ ih => exact .evdGcc d _ t ih

theorem EvDBind0 {Y : Type} (QE : AxSymMem.Dstate → Sail.Error exception → ExecSt → Prop)
    (Q : AxSymMem.Dstate → Y → ExecSt → Prop) (m : SailM Unit) (n : SailM Y)
    (d : AxSymMem.Dstate) (t : ExecSt) :
    EvD img dok kind QE (fun d' _ t' => EvD img dok kind QE Q d' n t') d m t →
    EvD img dok kind QE Q d (m >>= fun _ => n) t :=
  EvDBind img dok kind QE Q m (fun _ => n) d t

theorem EvDTryCatch {X : Type} (QE1 QE2 : AxSymMem.Dstate → Sail.Error exception → ExecSt → Prop)
    (Q : AxSymMem.Dstate → X → ExecSt → Prop) (m : SailM X) (h : Sail.Error exception → SailM X)
    (d : AxSymMem.Dstate) (t : ExecSt) :
    (∀ d' e t', QE1 d' e t' → EvD img dok kind QE2 Q d' (h e) t') →
    EvD img dok kind QE1 Q d m t → EvD img dok kind QE2 Q d (PreSail.tryCatchAll m h) t := by
  intro Hh H
  induction H with
  | evdRet d x t h => exact .evdRet d x t h
  | evdExt d e k t he => exact Hh d e t he
  | evdRd d r k t _ _ ihs ihn => exact .evdRd d r _ t ihs ihn
  | evdWr d r v k t hr _ ih => exact .evdWr d r v _ t hr ih
  | evdMrd d n va req k t vs h1 h2 h3 _ ih => exact .evdMrd d n va req _ t vs h1 h2 h3 ih
  | evdDrd n va req k t h1 h2 h3 h4 h5 _ ih => exact .evdDrd n va req _ t h1 h2 h3 h4 h5 ih
  | evdDwr n va req k t v h1 h2 h3 h4 h5 _ ih => exact .evdDwr n va req _ t v h1 h2 h3 h4 h5 ih
  | evdIa d n w k t hs _ ih => exact .evdIa d n w _ t hs ih
  | evdBa d n a k t _ ih => exact .evdBa d n a _ t ih
  | evdCo d c k t _ ih => exact .evdCo d c _ t ih
  | evdTl d c k t _ ih => exact .evdTl d c _ t ih
  | evdTe d f k t _ ih => exact .evdTe d f _ t ih
  | evdRx d a k t _ ih => exact .evdRx d a _ t ih
  | evdTs d a k t _ ih => exact .evdTs d a _ t ih
  | evdTx d a k t _ ih => exact .evdTx d a _ t ih
  | evdCc d k t _ ih => exact .evdCc d _ t ih
  | evdMsg d a k t _ ih => exact .evdMsg d a _ t ih
  | evdGcc d k t _ ih => exact .evdGcc d _ t ih

theorem EvDLiftRAny {R X : Type} (QE QE' : AxSymMem.Dstate → Sail.Error exception → ExecSt → Prop)
    (Q : AxSymMem.Dstate → X → ExecSt → Prop) (m : SailM X) (d : AxSymMem.Dstate) (t : ExecSt) :
    (∀ d e t', QE d e t' → QE' d e t') →
    EvD img dok kind QE Q d m t →
    EvD img dok kind QE'
      (fun d' (r : Except (Sail.Error exception ⊕ R) X) t' =>
        match r with
        | .ok x => Q d' x t'
        | .error _ => False)
      d (ExceptT.run (liftM m : SailME R X)) t := by
  intro HE H
  have e : ExceptT.run (liftM m : SailME R X) = m >>= fun a => pure (Except.ok a) := rfl
  rw [e]
  apply EvDBind
  exact EvDMono img dok kind QE QE' Q _ d m t HE (fun d x t' h => .evdRet d _ t' h) H

theorem EvDCatchEarlyReturn {X : Type} (QE : AxSymMem.Dstate → Sail.Error exception → ExecSt → Prop)
    (Q : AxSymMem.Dstate → X → ExecSt → Prop) (m : SailME X X) (d : AxSymMem.Dstate) (t : ExecSt) :
    EvD img dok kind QE
      (fun d' (r : Except (Sail.Error exception ⊕ X) X) t' =>
        match r with
        | .ok x => Q d' x t'
        | .error (.inr x) => Q d' x t'
        | .error (.inl e) => QE d' e t')
      d (ExceptT.run m) t →
    EvD img dok kind QE Q d (SailME.run m) t := by
  intro H
  show EvD img dok kind QE Q d (ExceptT.run m >>= _) t
  apply EvDBind
  refine EvDMono img dok kind QE QE _ _ d _ t (fun _ _ _ h => h) ?_ H
  intro d' r t' hr
  rcases r with (e | x) | x
  · exact .evdExt d' e _ t' hr
  · exact .evdRet d' x t' hr
  · exact .evdRet d' x t' hr

/-- Every `EvA` fact embeds at a FIXED data state. -/
theorem EvDOfEvA {X : Type} (QE : Sail.Error exception → ExecSt → Prop) (Q : X → ExecSt → Prop)
    (d : AxSymMem.Dstate) (m : SailM X) (t : ExecSt) :
    EvA img QE Q m t →
    EvD img dok kind (fun d' e t' => d' = d ∧ QE e t') (fun d' x t' => d' = d ∧ Q x t') d m t := by
  intro h
  induction h with
  | evRet x t h => exact .evdRet d x t ⟨rfl, h⟩
  | evExt e k t h => exact .evdExt d e k t ⟨rfl, h⟩
  | evRd r k t _ _ ihs ihn => exact .evdRd d r k t ihs ihn
  | evWr r v k t hr _ ih => exact .evdWr d r v k t hr ih
  | evMrd n va req k t vs h1 h2 h3 _ ih => exact .evdMrd d n va req k t vs h1 h2 h3 ih
  | evIa n w k t hs _ ih => exact .evdIa d n w k t hs ih
  | evBa n a k t _ ih => exact .evdBa d n a k t ih
  | evCo c k t _ ih => exact .evdCo d c k t ih
  | evTl c k t _ ih => exact .evdTl d c k t ih
  | evTe f k t _ ih => exact .evdTe d f k t ih
  | evRx a k t _ ih => exact .evdRx d a k t ih
  | evTs a k t _ ih => exact .evdTs d a k t ih
  | evTx a k t _ ih => exact .evdTx d a k t ih
  | evCc k t _ ih => exact .evdCc d k t ih
  | evMsg a k t _ ih => exact .evdMsg d a k t ih
  | evGcc k t _ ih => exact .evdGcc d k t ih

theorem EvDOfEvA' {X : Type} (QE : AxSymMem.Dstate → Sail.Error exception → ExecSt → Prop)
    (Q : AxSymMem.Dstate → X → ExecSt → Prop) (QE0 : Sail.Error exception → ExecSt → Prop)
    (Q0 : X → ExecSt → Prop) (d : AxSymMem.Dstate) (m : SailM X) (t : ExecSt) :
    (∀ e t', QE0 e t' → QE d e t') → (∀ x t', Q0 x t' → Q d x t') →
    EvA img QE0 Q0 m t → EvD img dok kind QE Q d m t := by
  intro HE HQ H
  refine EvDMono img dok kind _ _ _ _ d m t ?_ ?_ (EvDOfEvA img dok kind QE0 Q0 d m t H)
  · rintro _ e t' ⟨rfl, h⟩
    exact HE e t' h
  · rintro _ x t' ⟨rfl, h⟩
    exact HQ x t' h

end evd

/-! # 2. THE BRIDGE: `EvD` ⇒ `wpd` -/

section bridgeDefs
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- The data event's flow with an OUTPUT `O` handed to the continuation. -/
def dflowO (i : Agent) (GD : Gdexec) (k : Nat) (O : IProp GF) : IProp GF :=
  iprop(∀ na, naAtProgress GD i k na ∗ AxirisG.annotInterp na -∗ |==> ▷ |==>
    ∃ (R : IProp GF) (naUsed naUnused : Mea GF) (ls' : AxirisG.logTsT GF),
      naSplittingWf (Axpol.lobp GD (i, k)) na naUsed naUnused ∗
      flowEqDyn GD (i, k) (Axpol.sPol GD (i, k)) naUsed R ∗
      AxirisG.annotInterp (PartialMap.union (PartialMap.union {[(i, k) := R]} naUnused) na) ∗
      AxirisG.localInterp GD i (k + 1) ls' ∗ O)

/-- Row item `k` of hart `i` reads `n` bytes at `base`. -/
def rowRd (i : Agent) (GD : Gdexec) (k : Nat) (base : Int) (n : Nat) : Prop :=
  ∃ lb aq, (AxOpsem.grow GD i)[k]? = some lb ∧ aidentRd (aident lb) = some (aq, base, n)

/-- Row item `k` of hart `i` writes `n` bytes at `base`. -/
def rowWr (i : Agent) (GD : Gdexec) (k : Nat) (base : Int) (n : Nat) : Prop :=
  ∃ lb rl, (AxOpsem.grow GD i)[k]? = some lb ∧ aidentWr (aident lb) = some (rl, base, n)

/-- The caller's flow resource for a LOAD: at every graph, row position and graph value. -/
def FldM (M : Gdexec → Prop) (dok : Int → Nat → Prop) (i : Agent)
    (Out : Nat → List (BitVec 8) → IProp GF) : IProp GF :=
  iprop(∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (k : Nat) (v : List (BitVec 8)) (base : Int)
      (n : Nat),
    ⌜M GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
    ⌜graphValue GD (i, k) = some v⌝ -∗ ⌜dok base n ∧ rowRd i GD k base n⌝ -∗
    dflowO i GD k (Out k v))

/-- The caller's flow resource for a STORE: at every graph, row position and data. -/
def FstM (M : Gdexec → Prop) (dok : Int → Nat → Prop) (i : Agent)
    (Out : Nat → List (BitVec 8) → IProp GF) : IProp GF :=
  iprop(∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (k : Nat) (data : List (BitVec 8)) (base : Int)
      (n : Nat),
    ⌜M GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
    ⌜graphData GD (i, k) = some data⌝ -∗ ⌜dok base n ∧ rowWr i GD k base data.length⌝ -∗
    dflowO i GD k (Out k data))

def FkM (M : Gdexec → Prop) (dok : Int → Nat → Prop) (kind : Bool) (i : Agent)
    (Out : Nat → List (BitVec 8) → IProp GF) : IProp GF :=
  if kind then FldM M dok i Out else FstM M dok i Out

/-- The resource for data state `d`. -/
def DResM (M : Gdexec → Prop) (dok : Int → Nat → Prop) (kind : Bool) (i : Agent)
    (Out : Nat → List (BitVec 8) → IProp GF) (d : AxSymMem.Dstate) : IProp GF :=
  match d with
  | .DPend => FkM M dok kind i Out
  | .DDone vs => iprop(∃ k, Out k vs)

end bridgeDefs

section bridgeD
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (M : Gdexec → Prop)
variable (img : Image) (dok : Int → Nat → Prop) (kind : Bool)
variable (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
variable (G : Gdexec → Prop) (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
  ⊢ postLifting Φ i s)
variable (Htext : ∀ GD, M GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, M GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
/- no RMW row item of hart `i` reads a data-region address (the data region is not an AMO
target) — refutes the one degenerate matching of a plain data load against an RMW row item. -/
variable (HnoRmw : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat), (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n →
    ¬ dok base n⌝)
variable (Out : Nat → List (BitVec 8) → IProp GF)

include HG Hmid HnoRmw in
/-- THE DATA READ node, demonic in the answer. -/
theorem wpdDreadNodeM (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hkind : kind = true)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hnf : (classify req.access_kind).akIfetch = false)
    (Hdok : dok (paZ req.pa) n) :
    ⊢ ∀ rs, ⌜A rs⌝ -∗ DResM M dok kind i Out .DPend -∗
      (∀ (vs : List (BitVec 8)) (rs' : RegFile) (k' : Nat), ⌜vs.length = n⌝ -∗ ⌜A rs'⌝ -∗
         DResM M dok kind i Out (.DDone vs) -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs' none ib, k'⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ Φ := by
  have eF : DResM M dok kind i Out .DPend = FldM M dok i Out := by subst Hkind; rfl
  rw [eF]
  simp only [DResM]
  unfold FldM dflowO
  iloeb as IH
  iintro %rs %HP F C
  iapply (AxWpD.wpdMUnfoldStep M .MaybeStuck i _ Φ).2
  isplit
  · iapply (progressOblMaybestuck (GF := GF) i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
  ihave HGD := (HG GD Hc) $$ Hg
  icases HGD with %HGD
  ihave Hnr := (HnoRmw GD Hc) $$ Hg
  icases Hnr with %Hnr
  isplit
  · -- (a) THE DATA READ, demonic
    iintro %id %K %Hst
    obtain ⟨lb, Hlb, Hid, -, HK⟩ := Hst
    simp only at Hlb
    subst Hid
    obtain ⟨l0, d0, d0', Hl0, -, Hps0, -⟩ :=
      HK (List.replicate (aidentN (aident lb)) 0) List.length_replicate
    obtain ⟨tvs0, Htl0, rfl, -⟩ :=
      AxLdspWpd.loadStepInv cpu n va req KK rs ib d0 _ _ d0' Hdev Hlat Hnf Hps0
    simp only [wlRd, Htl0] at Hl0
    have Hadv0 : aidentAdvRd (aident lb) = 1 := by
      cases hid : aident lb with
      | IRmw aq rl base n' =>
        exfalso
        rw [hid] at Hl0
        simp only [aidentRd, Option.some.injEq, Prod.mk.injEq] at Hl0
        obtain ⟨-, hb, hn⟩ := Hl0
        subst hb
        subst hn
        exact Hnr k lb aq rl _ _ Hlb hid Hdok
      | IRead _ _ _ => rfl
      | IWrite _ _ _ => rfl
      | IFence _ _ _ _ => rfl
    simp only [Hadv0, ↓reduceIte]
    iintro %v %Hv %Hlenv
    obtain ⟨l, d, d', -, Hrv, Hps, Hk'⟩ := HK v Hlenv
    obtain ⟨tvs, Htl, rfl, Hp'⟩ :=
      AxLdspWpd.loadStepInv cpu n va req KK rs ib d _ _ d' Hdev Hlat Hnf Hps
    simp only [wlRvals] at Hrv
    subst Hrv
    rw [Hadv0] at Hk'
    have hKv : K (tvs.map Prod.snd) =
        ⟨.PHart cpu (KK (.Ok (wordOfBytes n (tvs.map Prod.snd), none))) rs none ib, k + 1⟩ := by
      cases hK : K (tvs.map Prod.snd) with
      | AThread p' k' =>
        rw [hK] at Hp' Hk'
        simp only at Hp' Hk'
        rw [Hp', Hk']
    rw [hKv]
    unfold wpEvStep
    iintro %na Hpg
    ihave Hf := F $$ %GD %ls %k %(tvs.map Prod.snd) %(paZ req.pa) %n %Hc Hg Hloc %Hv
      %⟨Hdok, lb, _, Hlb, Hl0.symm⟩
    imod Hf $$ %na Hpg with Hf
    imodintro
    inext
    imod Hf with ⟨%R, %nu, %nuu, %ls', Hs, Hfe, Hna, Hl, HO⟩
    imodintro
    iexists (), R, nu, nuu, ls'
    isplitr
    · ipureintro
      trivial
    iframe Hs Hna Hl
    isplitl [Hfe]
    · iapply (flowEqDynMono GD (i, k) _ nu R
        iprop(R ∗ ⌜graphValue GD (i, k) = some (tvs.map Prod.snd)⌝))
      · inext
        iintro HR
        iframe HR
        ipureintro
        exact Hv
      · iexact Hfe
    · iapply C $$ %(tvs.map Prod.snd) %rs %(k + 1)
      · ipureintro
        rw [List.length_map]
        exact Htl
      · ipureintro
        exact HP
      · iexists k
        iexact HO
  isplit
  · -- (b) no program step at a data read (`akIfetch = false`: no admin fetch)
    iintro %l %s' %Hst %Hpin
    have hfalse : False := by
      obtain ⟨d, d', hps⟩ := astepProgPstep _ _ _ _ Hst
      obtain ⟨tvs, -, hl, -⟩ :=
        AxLdspWpd.loadStepInv cpu n va req KK rs ib d l _ d' Hdev Hlat Hnf hps
      subst hl
      cases Hst with
      | AStepAdmin _ _ _ _ _ _ hadm _ => exact hadm
      | AStepWrite _ _ _ _ _ _ _ _ hwr _ _ _ => simp [wlWr] at hwr
      | AStepFence _ _ _ _ _ _ _ _ hf _ _ => simp [wlFence] at hf
    exact hfalse.elim
  isplit
  · -- (c) the PLIC wire
    iintro %s' %Hw
    obtain ⟨hk, hp⟩ := awireAeqv _ _ Hw
    obtain ⟨p', k'⟩ := s'
    simp only at hk hp
    subst hk
    match p', hp with
    | .PHart c m' rs' fn' ib', hp =>
      obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := hp
      unfold wpSkipStep
      iintro %na Hna
      imodintro
      inext
      imodintro
      iexists ls
      iframe Hna Hloc
      iapply IH $$ %rs' %(HA rs rs' HP hag) F C
  · -- (d) row end: a mid-instruction state
    iintro %Heq
    iapply (Hmid GD _ HGD (by exact trivial) Heq)

include HG Hmid in
/-- THE DATA WRITE node: `AStepWrite` only; the row validates the data. -/
theorem wpdDwriteNodeM (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat) (v : BitVec (8 * n))
    (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hkind : kind = false)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hval : req.value = some v)
    (Hdok : dok (paZ req.pa) n) :
    ⊢ ∀ rs, ⌜A rs⌝ -∗ DResM M dok kind i Out .DPend -∗
      (∀ (rs' : RegFile) (k' : Nat), ⌜A rs'⌝ -∗
         DResM M dok kind i Out (.DDone (WeakInterpProj.wbytes n v)) -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (KK (.Ok (some true))) rs' none ib, k'⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memWrite n va req)) KK) rs none ib, k⟩ Φ := by
  have eF : DResM M dok kind i Out .DPend = FstM M dok i Out := by subst Hkind; rfl
  rw [eF]
  simp only [DResM]
  unfold FstM dflowO
  iloeb as IH
  iintro %rs %HP F C
  iapply (AxWpD.wpdMUnfoldStep M .MaybeStuck i _ Φ).2
  isplit
  · iapply (progressOblMaybestuck (GF := GF) i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
  ihave HGD := (HG GD Hc) $$ Hg
  icases HGD with %HGD
  isplit
  · -- (a) no read at a store node
    iintro %id %K %Hst
    exact (AxEpiLedgerSd.storeNoRead _ cpu n va req KK rs ib k id K Hdev Hlat Hst).elim
  isplit
  · -- (b) THE WRITE
    iintro %l %s' %Hst %Hpin
    obtain ⟨v', hv', hl, hs'⟩ :=
      AxEpiLedgerSd.storeAstepInv _ cpu n va req KK rs ib k l s' Hdev Hlat Hst
    have hvv : v' = v := by
      rw [Hval] at hv'
      exact (Option.some.inj hv').symm
    subst hvv
    have Hgd : graphData GD (i, k) = some (WeakInterpProj.wbytes n v') ∧
        rowWr i GD k (paZ req.pa) (WeakInterpProj.wbytes n v').length := by
      cases Hst with
      | AStepAdmin _ _ _ _ _ _ hadm _ =>
        rw [hl] at hadm
        exact (hadm : False).elim
      | AStepWrite _ _ _ _ lb _ _ hrow _ hwr hwd _ =>
        rw [hl] at hwr hwd
        simp only [wlWr] at hwr
        simp only [wlWdata] at hwd
        refine ⟨?_, lb, _, hrow, hwr.symm⟩
        unfold graphData
        rw [AxWp.growLookup _ _ _ _ hrow, Option.bind_some, ← hwd]
      | AStepFence _ _ _ _ _ _ _ _ hf _ _ =>
        rw [hl] at hf
        simp [wlFence] at hf
    rw [hl, hs']
    simp only [wlWdata]
    unfold wpEvStep
    iintro %na Hpg
    ihave Hf := F $$ %GD %ls %k %(WeakInterpProj.wbytes n v') %(paZ req.pa) %n %Hc Hg Hloc
      %Hgd.1 %⟨Hdok, Hgd.2⟩
    imod Hf $$ %na Hpg with Hf
    imodintro
    inext
    imod Hf with ⟨%R, %nu, %nuu, %ls', Hs, Hfe, Hna, Hl, HO⟩
    imodintro
    iexists (), R, nu, nuu, ls'
    isplitr
    · ipureintro
      trivial
    iframe Hs Hna Hl
    isplitl [Hfe]
    · iapply (flowEqDynMono GD (i, k) _ nu R
        iprop(R ∗ ⌜graphData GD (i, k) = some (WeakInterpProj.wbytes n v')⌝))
      · inext
        iintro HR
        iframe HR
        ipureintro
        exact Hgd.1
      · iexact Hfe
    · iapply C $$ %rs %(k + 1)
      · ipureintro
        exact HP
      · iexists k
        iexact HO
  isplit
  · -- (c) the PLIC wire
    iintro %s' %Hw
    obtain ⟨hk, hp⟩ := awireAeqv _ _ Hw
    obtain ⟨p', k'⟩ := s'
    simp only at hk hp
    subst hk
    match p', hp with
    | .PHart c m' rs' fn' ib', hp =>
      obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := hp
      unfold wpSkipStep
      iintro %na Hna
      imodintro
      inext
      imodintro
      iexists ls
      iframe Hna Hloc
      iapply IH $$ %rs' %(HA rs rs' HP hag) F C
  · iintro %Heq
    iapply (Hmid GD _ HGD (by exact trivial) Heq)

include HG Hmid Htext Hflow HnoRmw in
/-- THE BRIDGE. -/
theorem wpdOfEvDM (Q : AxSymMem.Dstate → Unit → ExecSt → Prop) (m : SailM Unit)
    (d : AxSymMem.Dstate) (t : ExecSt) :
    EvD img dok kind (fun _ _ _ => False) Q d m t →
    ∀ rs ib k, regsAgree AxRunClose.pinReg rs t.regs →
    ⊢ DResM M dok kind i Out d -∗
      (∀ d' t' rs' ib' k', ⌜Q d' () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         DResM M dok kind i Out d' -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu m rs none ib, k⟩ Φ := by
  intro H
  induction H with
  | evdRet d x t HQ =>
    intro rs ib kk Hag
    iintro Hd C
    iapply C $$ %d %t %rs %ib %kk %HQ %Hag Hd
  | evdExt d e k t he => exact he.elim
  | evdRd d r k t _ _ IHs IHn =>
    intro rs ib kk Hag
    iintro Hd C
    iapply (wpdAdminNode3M M i Φ cpu G HG Hmid _ ?_ kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun s2 => ∃ rs1 ib1, s2 = ⟨.PHart cpu (k (rs1 r)) rs1 none ib1, kk⟩ ∧
        regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs1 ib1 d l p' d' HA1 Hp
      obtain ⟨rfl, rfl⟩ := pstepRdInv cpu r k rs1 ib1 d l p' d' Hp
      exact ⟨trivial, rs1, _, rfl, HA1⟩
    · iintro %s2 %HN
      obtain ⟨rs1, ib1, rfl, HA1⟩ := HN
      by_cases Hs : AxRunClose.pinReg r
      · iapply (IHs Hs (rs1 r) rs1 ib1 kk HA1) $$ Hd C
      · have h := IHn Hs rs1 ib1 kk HA1
        rw [← HA1 r Hs] at h
        iapply h $$ Hd C
  | evdWr d r v k t Hr _ IH =>
    intro rs ib kk Hag
    iintro Hd C
    iapply (wpdAdminNode3M M i Φ cpu G HG Hmid _ ?_ kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun s2 => ∃ rs1 ib1, s2 = ⟨.PHart cpu (k PUnit.unit) (rs1.set r v) none ib1, kk⟩ ∧
        regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs1 ib1 d l p' d' HA1 Hp
      obtain ⟨Hl, rfl⟩ := pstepWrInv cpu r v k rs1 ib1 d l p' d' Hp
      exact ⟨Hl, rs1, ib1, rfl, HA1⟩
    · iintro %s2 %HN
      obtain ⟨rs1, ib1, rfl, HA1⟩ := HN
      iapply (IH (rs1.set r v) ib1 kk (regsAgreeSet _ _ _ r v HA1)) $$ Hd C
  | evdMrd d n va req k t vs Hdev Hlat Hvs _ IH =>
    intro rs ib kk Hag
    iintro Hd C
    iapply (wpdMreadNode3M M img i Φ cpu G HG Hmid Htext Hflow n va req k ib kk vs
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hvs) $$ %rs %Hag
    iintro %rs' %HA'
    iapply (IH rs' ib _ HA') $$ Hd C
  | evdDrd n va req k t Hkd Hdev Hlat Hnf Hdok _ IH =>
    intro rs ib kk Hag
    iintro Hd C
    iapply (wpdDreadNodeM M dok kind i Φ cpu G HG Hmid HnoRmw Out n va req k ib kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hkd Hdev Hlat Hnf Hdok) $$ %rs %Hag Hd
    iintro %vs %rs' %k' %Hlen %HA' Hd
    iapply (IH vs Hlen rs' ib k' HA') $$ Hd C
  | evdDwr n va req k t v Hkd Hdev Hlat Hval Hdok _ IH =>
    intro rs ib kk Hag
    iintro Hd C
    iapply (wpdDwriteNodeM M dok kind i Φ cpu G HG Hmid Out n va req k ib kk v
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hkd Hdev Hlat Hval Hdok) $$ %rs %Hag Hd
    iintro %rs' %k' %HA' Hd
    iapply (IH rs' ib k' HA') $$ Hd C
  | evdIa d n w k t Hsf _ IH =>
    intro rs ib kk Hag
    iintro Hd C
    iapply (AxSymEngine3.wpdSilentNode3M M i Φ cpu G HG Hmid _ (k ()) ?_ kk t ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs ib d l m' ors fn' d' oib obar h
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := h
      rw [annLabelNot Hsf]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · iintro %rs1 %ib1 %HA1
      iapply (IH rs1 ib1 kk HA1) $$ Hd C
  | evdBa d _ _ k t _ IH | evdCo d _ k t _ IH | evdTl d _ k t _ IH | evdTe d _ k t _ IH
  | evdRx d _ k t _ IH | evdTs d _ k t _ IH | evdTx d _ k t _ IH | evdCc d k t _ IH
  | evdMsg d _ k t _ IH | evdGcc d k t _ IH =>
    intro rs ib kk Hag
    iintro Hd C
    iapply (AxSymEngine3.wpdSilentNode3M M i Φ cpu G HG Hmid _ _ ?_ kk t ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs ib d l m' ors fn' d' oib obar h
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := h
      exact ⟨trivial, rfl, rfl, rfl⟩
    · iintro %rs1 %ib1 %HA1
      iapply (IH rs1 ib1 kk HA1) $$ Hd C

include HG Hmid Htext Hflow HnoRmw in
/-- ONE INSTRUCTION from a `.pure ()` boundary, `DPend` at the start. -/
theorem wpdInstrOfEvDM (Q : AxSymMem.Dstate → Unit → ExecSt → Prop) (rs : RegFile) (k : Nat)
    (s : Athread) (Hs : RetX cpu rs k s)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1)
    (Hcert : ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
       EvD img dok kind (fun _ _ _ => False) Q .DPend (riscvStep tick) t) :
    ⊢ DResM M dok kind i Out .DPend -∗
      (∀ d' t' rs' ib' k', ⌜Q d' () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         DResM M dok kind i Out d' -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM M .MaybeStuck i s Φ := by
  iintro Hd C
  iapply (wpdRetNode3M M i Φ cpu G HG rs k s Hs Hb)
  iintro %s2 %HN
  obtain ⟨tick, rs', Hag, rfl⟩ := HN
  iapply (wpdOfEvDM M img dok kind i Φ cpu G HG Hmid Htext Hflow HnoRmw Out Q _ .DPend
    ⟨rs', fun _ => none, testDevs⟩
    (Hcert tick ⟨rs', fun _ => none, testDevs⟩ (regsAgreeSym _ _ _ Hag)) rs' ibNone k
    (regsAgreeRefl _ _)) $$ Hd C

end bridgeD

/-! ### The riscv.cat instances under the Rocq names (`…M` at `rvwmoCatConsistent`) -/

section bridgeDCat
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

def Fld (dok : Int → Nat → Prop) (i : Agent) (Out : Nat → List (BitVec 8) → IProp GF) :
    IProp GF :=
  FldM rvwmoCatConsistent dok i Out

def Fst (dok : Int → Nat → Prop) (i : Agent) (Out : Nat → List (BitVec 8) → IProp GF) :
    IProp GF :=
  FstM rvwmoCatConsistent dok i Out

/-- (Rocq notation) -/
abbrev Fk (dok : Int → Nat → Prop) (kind : Bool) (i : Agent)
    (Out : Nat → List (BitVec 8) → IProp GF) : IProp GF :=
  FkM rvwmoCatConsistent dok kind i Out

/-- (Rocq notation) -/
abbrev DRes (dok : Int → Nat → Prop) (kind : Bool) (i : Agent)
    (Out : Nat → List (BitVec 8) → IProp GF) (d : AxSymMem.Dstate) : IProp GF :=
  DResM rvwmoCatConsistent dok kind i Out d

variable (img : Image) (dok : Int → Nat → Prop) (kind : Bool)
variable (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
variable (G : Gdexec → Prop)
  (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
  ⊢ postLifting Φ i s)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
variable (HnoRmw : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat), (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n →
    ¬ dok base n⌝)
variable (Out : Nat → List (BitVec 8) → IProp GF)

include HG Hmid HnoRmw in
theorem wpdDreadNode (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hkind : kind = true)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hnf : (classify req.access_kind).akIfetch = false)
    (Hdok : dok (paZ req.pa) n) :
    ⊢ ∀ rs, ⌜A rs⌝ -∗ DRes dok kind i Out .DPend -∗
      (∀ (vs : List (BitVec 8)) (rs' : RegFile) (k' : Nat), ⌜vs.length = n⌝ -∗ ⌜A rs'⌝ -∗
         DRes dok kind i Out (.DDone vs) -∗
         wpd .MaybeStuck i ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs' none ib, k'⟩ Φ) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ Φ :=
  wpdDreadNodeM rvwmoCatConsistent dok kind i Φ cpu G HG Hmid HnoRmw Out n va req KK ib k A HA
    Hkind Hdev Hlat Hnf Hdok

include HG Hmid in
theorem wpdDwriteNode (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat) (v : BitVec (8 * n))
    (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hkind : kind = false)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hval : req.value = some v)
    (Hdok : dok (paZ req.pa) n) :
    ⊢ ∀ rs, ⌜A rs⌝ -∗ DRes dok kind i Out .DPend -∗
      (∀ (rs' : RegFile) (k' : Nat), ⌜A rs'⌝ -∗
         DRes dok kind i Out (.DDone (WeakInterpProj.wbytes n v)) -∗
         wpd .MaybeStuck i ⟨.PHart cpu (KK (.Ok (some true))) rs' none ib, k'⟩ Φ) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memWrite n va req)) KK) rs none ib, k⟩ Φ :=
  wpdDwriteNodeM rvwmoCatConsistent dok kind i Φ cpu G HG Hmid Out n va req KK ib k v A HA
    Hkind Hdev Hlat Hval Hdok

include HG Hmid Htext Hflow HnoRmw in
theorem wpdOfEvD (Q : AxSymMem.Dstate → Unit → ExecSt → Prop) (m : SailM Unit)
    (d : AxSymMem.Dstate) (t : ExecSt)
    (H : EvD img dok kind (fun _ _ _ => False) Q d m t) :
    ∀ rs ib k, regsAgree AxRunClose.pinReg rs t.regs →
    ⊢ DRes dok kind i Out d -∗
      (∀ d' t' rs' ib' k', ⌜Q d' () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         DRes dok kind i Out d' -∗
         wpd .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpd .MaybeStuck i ⟨.PHart cpu m rs none ib, k⟩ Φ :=
  wpdOfEvDM rvwmoCatConsistent img dok kind i Φ cpu G HG Hmid Htext Hflow HnoRmw Out Q m d t H

include HG Hmid Htext Hflow HnoRmw in
theorem wpdInstrOfEvD (Q : AxSymMem.Dstate → Unit → ExecSt → Prop) (rs : RegFile) (k : Nat)
    (s : Athread) (Hs : RetX cpu rs k s)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1)
    (Hcert : ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
       EvD img dok kind (fun _ _ _ => False) Q .DPend (riscvStep tick) t) :
    ⊢ DRes dok kind i Out .DPend -∗
      (∀ d' t' rs' ib' k', ⌜Q d' () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         DRes dok kind i Out d' -∗
         wpd .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpd .MaybeStuck i s Φ :=
  wpdInstrOfEvDM rvwmoCatConsistent img dok kind i Φ cpu G HG Hmid Htext Hflow HnoRmw Out Q rs k
    s Hs Hb Hcert

end bridgeDCat

end Weak
