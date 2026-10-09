/-
Weak: **THE ONE CERTIFICATE of the symbolic WPd engine X** (constraint C of the 2026-09-30
constraints review; consolidation of `EvA` / `EvB` / `EvD`; nothing existing is edited — the old
certificates stay, other files use them, and every one of them EMBEDS here, §3).

Rocq: `iris/AxCert.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 `AxCert.Cert img dok kind QE Q s m t` — an INDUCTIVE, all-paths, big-step predicate on Sail
trees, indexed by a CERTIFICATE STATE `s = ⟨d, b, r⟩ : Cst`:
- `d : Cdata` — the instruction's DATA EVENT: `CPend` (still to come), `CLd vs` (a load returned
  `vs`), `CSt vs c` (a store wrote `vs` with class `c`), `CRmwR aq rvs` (the exclusive read half
  of an RMW returned `rvs`; `aq` its acquire bit), `CRmw aq rl rvs wvs c` (the RMW is complete);
- `b : Bud` — the READ BUDGET: `BInf` = no counting (EvD / EvA mode), `BFin n` = exactly `n` row
  items left; graph image reads, data reads, data writes, fences and the RMW WRITE half consume
  one unit (`bsucc`); the fused RMW's read half consumes none; at `BFin 0` a plain RAM graph read
  is accepted without continuation (`cEnd` — the row ended);
- `r : Bool` — the RELEASE-PENDING flag, moved EXACTLY as `relpUpd` moves it (a fence with
  `pw && sw` arms it, a store / exclusive store clears it); a store records the class the
  language stamps on it, `wcls ak r` = `lcls` at the store node (`wclsFaithful(Ex)`) — so a
  `fence rw,w; sw` pair certifies the store as `WCrel`.
Node constructors: EvA's register / image-read / silent / failure nodes; EvD's data read / data
write; NEW: `cFence` (a `barrier` node whose kind parks nothing — every kind but `fence.tso`),
`cXrd` / `cXwr` (the exclusive read half / exclusive write half of an AMO or LR/SC pair —
`akLatest` access kinds; the read half DEMONIC at the graph value).  `dok` is the regime's data
region, `kind : Dkind` the instruction's data event kind.
§2 THE KIT: `CertMono`, `CertBind(0)`, `CertFact`, `CertTryCatch`, `CertLiftRAny`,
`CertCatchEarlyReturn`, `CertReadReg`, `CertWriteReg`, `CertRet`.
§3 EMBEDDINGS: `CertOfEvA` (at `BInf`, any fixed data state and flag), `CertOfEvB` (at `BFin b`,
the budget left reported), `CertOfEvD` (kind `true ↦ DKLd`, `false ↦ DKSt`; the data state
forgotten through `cdOf`), `CertOfRfF` / `CertOfRfFPost` — the SC-certificate transfer through
the FAIL-TOLERANT footprint `rfF`: an SC `exec` run of an `rfF` tree is a `Cert` at every state.
§4 CLASSES: `wcls` and its faithfulness to `lcls`; `wclsRmw` — the DERIVED class of an RMW
write that respects an `.rl` bit (`wmClassOf` answers `WCexcl` at `akLatest` FIRST).
The WPd bridge is `AxCert2`.

## Deviations from Rocq

1. O2 STAGE C (fetch = pinned admin step; `AxSymCtl` deviation 1, `AxSymMem` deviation 1).  In
   Rocq every plain (`ak_coh = false`) RAM read — the instruction fetch included — is a row item
   (`c_mrd`, `bsucc`).  In Lean an `akIfetch` read is the pinned admin step at the SAME row
   position.  So `Cert.cMrd` is the GRAPH image read (premise `akIfetch = false`, Rocq's
   `ak_coh = false` renamed) and consumes one unit, and the Lean-only constructor `Cert.cIf` is
   an image FETCH (`akIfetch = true`) that KEEPS the budget (as `EvB.ebIf`).  `cEnd` and `cDrd`
   take `akIfetch = false` (as `EvB.ebEnd` / `EvD.evdDrd`: a fetch at the row end is not stuck,
   a data read is never a fetch).  `CertOfEvA`/`CertOfEvD` split `EvA.evMrd`/`EvD.evdMrd` (which
   cover both kinds) on `akIfetch`.
2. THE PINS (`AxRunClose` deviation 1): `seip_reg` ↦ `AxRunClose.pinReg` in `cRd`/`cWr`.
3. Q7: `Cert.cIa` takes `sfAnnB n w = false` (as `EvA.evIa`).
4. LEAN-SAIL OUTCOMES / MONADS (as `AxSymEngine` deviation 4, `AxSymCtl` deviation 4): `Cert` is
   on `SailM X`; Rocq's extra outcome type `E` ↦ the failure node `.impure (.error e)` with
   `e : Sail.Error exception` (`cExt`).  `CertTryCatch` has one error type
   (`Defs.try_catch` ↦ `PreSail.tryCatchAll`).  `CertLiftRAny` is stated on
   `ExceptT.run (liftM m)` (result `.ok x ↦ Q`, `.error _` excluded; failure nodes stay failure
   nodes over the same error type, mapped by `HE : QE ⊆ QE'` — Rocq's `inr` injection).
   `CertCatchEarlyReturn` takes the certificate of `ExceptT.run m` with `.ok x`/`.error (.inr x)`
   ↦ `Q`, `.error (.inl e)` ↦ `QE` (as `EvBCatchEarlyReturn`).
5. LEAN-SAIL WRITE VALUES ARE `Option` (`AxSymMem` deviation 2): `cDwr`/`cXwr` take `v` with
   `req.value = some v`, record `WeakInterpProj.wbytes n v`, and continue at the answer
   `.Ok (some true)` (Rocq `inl None`).  Read answers are `.Ok (wordOfBytes n vs, none)`.
6. `CertOfRfF`: Rocq's `RiscvExec.exec` ↦ `Weak.exec` (`Weak/Exec.lean`).
7. TYPES (as `AxSymEngine` deviation 5): `Z → option (bv 8)` ↦ `Image`, `mstate` ↦ `ExecSt`,
   `register_lookup r t.(sregs)` ↦ `t.regs r`, `set_reg` ↦ `ExecSt.setReg`, `N.to_nat n` ↦
   `n : Nat`, `S n` ↦ `n + 1`, `Interface.accessKind` ↦ `AK`, `wm_class` ↦ `WmClass`.
   Rocq `Record cst := CS {…}` ↦ `structure Cst` with constructor `Cst.CS`.
8. NAME CLASH: Rocq `Cert` is declared `AxCert.Cert` (constructors `AxCert.Cert.cRet` …) —
   `Weak.Cert` already exists (`WeakRvwmoKillArms`, Rocq `cert`).
9. Q16 (owner ruling): `EvB` gained the Lean-only stuck end `EvB.ebNf` (an i-fetch with no image
   bytes, accepted only where `QE` accepts every stuck end; `AxSymCtl` deviation 7), which `Cert`
   has no counterpart for.  `CertOfEvB` takes `HQE : ∀ t', ¬ ∀ e, QE e t'` (no state accepts
   every stuck end — e.g. `QE := fun _ _ => False`, the only form Rocq's users (`AxSpinE`) embed;
   dischargeable by `fun _ h => h .Exit`), which rules `ebNf` out.
10. Q19 (provisional): the Lean-only constructor `Cert.cSf` certifies an SFENCE.VMA announce
   (`sfAnnB n w = true`): under Q7 that node is the graph's sfence MARKER
   `LFence false false false false` (`WeakEvLang.annLabel`), so it consumes ONE row item
   (`bsucc`, as `cFence`) and leaves the data event and the release flag unchanged (the
   all-false fence arms nothing).  Rocq has no counterpart (there the marker is the fetch row
   item).  Its bridge case is `AxCert2.wpdSfNodeM`.
11. (Lean-only, Theorem 2 / P4, owner Q-P4-1) the constructor `Cert.cWrEnd` is the WRITE twin
   of `cEnd`: at `BFin 0` (the row has ended) a plain (`akLatest = false`) RAM write is accepted
   without continuation — it is stuck (no row item ⇒ no `AStepWrite`).  Its bridge case is
   `AxCert2.wpdStuckWriteM`.  Rocq has no counterpart.

**Rocq → Lean name map.**  `bud` `Bud` (`BInf`, `BFin`), `bsucc` `bsucc`, `dkind` `Dkind`
(`DKLd`, `DKSt`, `DKRmw`), `cdata` `Cdata` (`CPend`, `CLd`, `CSt`, `CRmwR`, `CRmw`), `cst` `Cst`
(`CS`; fields `cs_d` `csD`, `cs_b` `csB`, `cs_r` `csR`), `wcls` `wcls`, `Cert` `AxCert.Cert`
(constructors `c_ret` `cRet`, `c_rd` `cRd`, `c_wr` `cWr`, `c_mrd` `cMrd`, `c_end` `cEnd`, `c_drd`
`cDrd`, `c_dwr` `cDwr`, `c_fence` `cFence`, `c_xrd` `cXrd`, `c_xwr` `cXwr`, `c_ia` `cIa`, `c_ba`
`cBa`, `c_co` `cCo`, `c_tl` `cTl`, `c_te` `cTe`, `c_rx` `cRx`, `c_ts` `cTs`, `c_tx` `cTx`, `c_cc`
`cCc`, `c_msg` `cMsg`, `c_gcc` `cGcc`, `c_ext` `cExt`; Lean-only `cIf`, `cSf`, `cWrEnd`), `Cert_mono`
`CertMono`, `Cert_bind` `CertBind`, `Cert_bind0` `CertBind0`, `Cert_fact` `CertFact`, `Cert_ret` `CertRet`,
`Cert_read_reg` `CertReadReg`, `Cert_write_reg` `CertWriteReg`, `Cert_try_catch` `CertTryCatch`,
`Cert_liftR_any` `CertLiftRAny`, `Cert_catch_early_return` `CertCatchEarlyReturn`, `Cert_of_EvA`
`CertOfEvA`, `Cert_of_EvB` `CertOfEvB`, `dk_of` `dkOf`, `cd_of` `cdOf`, `cd_of_pend` `cdOfPend`,
`Cert_of_EvD` `CertOfEvD`, `Cert_of_rfF` `CertOfRfF`, `Cert_of_rfF_post` `CertOfRfFPost`,
`wcls_faithful` `wclsFaithful`, `wcls_faithful_ex` `wclsFaithfulEx`, `wcls_latest` `wclsLatest`,
`wcls_armed` `wclsArmed`, `relp_upd_rw_w` `relpUpdRwW`, `wcls_rmw` `wclsRmw`, `wcls_rmw_norl`
`wclsRmwNorl`.  None is in the duplicated-name table.

**Dropped:** nothing (Rocq 32 definitions/lemmas; Lean 32, + the Lean-only constructors `cIf`,
`cSf`, `cWrEnd`).
**Not ported:** the section-local Ltac `cert_ctor` (Lean proofs name the constructor per case).
-/
import Weak.AxSymCtlb
import Weak.AxSymMem
import Weak.AxClsStep

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! # 1. The certificate -/

inductive Bud where
  | BInf
  | BFin (n : Nat)

def bsucc (b : Bud) : Bud :=
  match b with
  | .BInf => .BInf
  | .BFin n => .BFin (n + 1)

inductive Dkind where
  | DKLd
  | DKSt
  | DKRmw

inductive Cdata where
  | CPend
  | CLd (vs : List (BitVec 8))
  | CSt (vs : List (BitVec 8)) (c : WmClass)
  | CRmwR (aq : Bool) (rvs : List (BitVec 8))
  | CRmw (aq rl : Bool) (rvs wvs : List (BitVec 8)) (c : WmClass)

structure Cst where
  CS ::
  csD : Cdata
  csB : Bud
  csR : Bool

/-- The class the language stamps on a (plain or conditional) store of access kind `ak` at
release-pending flag `r` (§4: = `lcls`). -/
def wcls (ak : AK) (r : Bool) : WmClass :=
  wmClassOf (classify ak) (relpWs r)

namespace AxCert

/-- THE CERTIFICATE (see the header; deviation 1: `cMrd` a graph image read, `cIf` a fetch). -/
inductive Cert (img : Image) (dok : Int → Nat → Prop) (kind : Dkind) {X : Type}
    (QE : Cst → Sail.Error exception → ExecSt → Prop) (Q : Cst → X → ExecSt → Prop) :
    Cst → SailM X → ExecSt → Prop where
  | cRet (s : Cst) (x : X) (t : ExecSt) : Q s x t → Cert img dok kind QE Q s (.pure x) t
  | cRd (s : Cst) (r : Register) (k : RegisterType r → SailM X) (t : ExecSt) :
      (AxRunClose.pinReg r → ∀ v, Cert img dok kind QE Q s (k v) t) →
      (¬ AxRunClose.pinReg r → Cert img dok kind QE Q s (k (t.regs r)) t) →
      Cert img dok kind QE Q s (.impure (.ok (.regRead r)) k) t
  | cWr (s : Cst) (r : Register) (v : RegisterType r) (k : PUnit → SailM X) (t : ExecSt) :
      ¬ AxRunClose.pinReg r → Cert img dok kind QE Q s (k PUnit.unit) (t.setReg r v) →
      Cert img dok kind QE Q s (.impure (.ok (.regWrite r v)) k) t
  /-- an IMAGE graph read (page tables, D3): one row item -/
  | cMrd (d : Cdata) (b : Bud) (r : Bool) (n va : Nat)
      (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt)
      (vs : List (BitVec 8)) :
      devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      (classify req.access_kind).akIfetch = false →
      imgBytes img (paZ req.pa) n = some vs →
      Cert img dok kind QE Q ⟨d, b, r⟩ (k (.Ok (wordOfBytes n vs, none))) t →
      Cert img dok kind QE Q ⟨d, bsucc b, r⟩ (.impure (.ok (.memRead n va req)) k) t
  /-- (Lean-only, deviation 1) an image FETCH: the pinned admin step, no row item -/
  | cIf (s : Cst) (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt)
      (vs : List (BitVec 8)) :
      devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      (classify req.access_kind).akIfetch = true →
      imgBytes img (paZ req.pa) n = some vs →
      Cert img dok kind QE Q s (k (.Ok (wordOfBytes n vs, none))) t →
      Cert img dok kind QE Q s (.impure (.ok (.memRead n va req)) k) t
  /-- the row has ended: a plain RAM graph read there is stuck -/
  | cEnd (d : Cdata) (r : Bool) (n va : Nat)
      (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt) :
      devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      (classify req.access_kind).akIfetch = false →
      Cert img dok kind QE Q ⟨d, .BFin 0, r⟩ (.impure (.ok (.memRead n va req)) k) t
  /-- the DATA read — demonic -/
  | cDrd (b : Bud) (r : Bool) (n va : Nat)
      (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt) :
      kind = .DKLd → devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      (classify req.access_kind).akIfetch = false →
      dok (paZ req.pa) n →
      (∀ vs : List (BitVec 8), vs.length = n →
        Cert img dok kind QE Q ⟨.CLd vs, b, r⟩ (k (.Ok (wordOfBytes n vs, none))) t) →
      Cert img dok kind QE Q ⟨.CPend, bsucc b, r⟩ (.impure (.ok (.memRead n va req)) k) t
  /-- the DATA write — the row checks the bytes; class recorded, flag cleared -/
  | cDwr (b : Bud) (r : Bool) (n va : Nat)
      (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (Option Bool) Arch.abort → SailM X) (t : ExecSt) (v : BitVec (8 * n)) :
      kind = .DKSt → devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      req.value = some v →
      dok (paZ req.pa) n →
      Cert img dok kind QE Q
        ⟨.CSt (WeakInterpProj.wbytes n v) (wcls req.access_kind r), b, false⟩
        (k (.Ok (some true))) t →
      Cert img dok kind QE Q ⟨.CPend, bsucc b, r⟩ (.impure (.ok (.memWrite n va req)) k) t
  /-- THE BARRIER ARM: a fence event, one row item; the flag moves as `relpUpd` of the
  barrier's label -/
  | cFence (d : Cdata) (b : Bud) (r : Bool) (bk : barrier_kind) (k : Unit → SailM X)
      (t : ExecSt) :
      ebarPark bk = none →
      Cert img dok kind QE Q ⟨d, b, relpUpd (ebarLabel bk) r⟩ (k ()) t →
      Cert img dok kind QE Q ⟨d, bsucc b, r⟩ (.impure (.ok (.barrier bk)) k) t
  /-- THE RMW ARM, read half: exclusive read, demonic, no row item consumed -/
  | cXrd (b : Bud) (r : Bool) (n va : Nat)
      (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt) :
      kind = .DKRmw → devAddr req.pa = false → (classify req.access_kind).akLatest = true →
      dok (paZ req.pa) n →
      (∀ vs : List (BitVec 8), vs.length = n →
        Cert img dok kind QE Q ⟨.CRmwR (classify req.access_kind).akSync vs, b, r⟩
          (k (.Ok (wordOfBytes n vs, none))) t) →
      Cert img dok kind QE Q ⟨.CPend, b, r⟩ (.impure (.ok (.memRead n va req)) k) t
  /-- THE RMW ARM, write half: exclusive write (success branch), one row item -/
  | cXwr (aq : Bool) (rvs : List (BitVec 8)) (b : Bud) (r : Bool) (n va : Nat)
      (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (Option Bool) Arch.abort → SailM X) (t : ExecSt) (v : BitVec (8 * n)) :
      kind = .DKRmw → devAddr req.pa = false → (classify req.access_kind).akLatest = true →
      req.value = some v →
      dok (paZ req.pa) n →
      Cert img dok kind QE Q
        ⟨.CRmw aq (classify req.access_kind).akSync rvs (WeakInterpProj.wbytes n v)
          (wcls req.access_kind r), b, false⟩
        (k (.Ok (some true))) t →
      Cert img dok kind QE Q ⟨.CRmwR aq rvs, bsucc b, r⟩ (.impure (.ok (.memWrite n va req)) k) t
  | cIa (s : Cst) (n : Nat) (w : BitVec n) (k : Unit → SailM X) (t : ExecSt) :
      sfAnnB n w = false → Cert img dok kind QE Q s (k ()) t →
      Cert img dok kind QE Q s (.impure (.ok (.instrAnnounce n w)) k) t
  /-- (Lean-only, Q19) THE SFENCE.VMA ANNOUNCE: the marker `LFence false false false false`
  (`WeakEvLang.annLabel`), one row item; the release flag is unchanged -/
  | cSf (d : Cdata) (b : Bud) (r : Bool) (n : Nat) (w : BitVec n) (k : Unit → SailM X)
      (t : ExecSt) :
      sfAnnB n w = true → Cert img dok kind QE Q ⟨d, b, r⟩ (k ()) t →
      Cert img dok kind QE Q ⟨d, bsucc b, r⟩ (.impure (.ok (.instrAnnounce n w)) k) t
  | cBa (s : Cst) (n : Nat) (a : BitVec n) (k : Unit → SailM X) (t : ExecSt) :
      Cert img dok kind QE Q s (k ()) t →
      Cert img dok kind QE Q s (.impure (.ok (.branchAnnounce n a)) k) t
  | cCo (s : Cst) (c : Arch.cache_op) (k : Unit → SailM X) (t : ExecSt) :
      Cert img dok kind QE Q s (k ()) t → Cert img dok kind QE Q s (.impure (.ok (.cacheOp c)) k) t
  | cTl (s : Cst) (c : Arch.tlb_op) (k : Unit → SailM X) (t : ExecSt) :
      Cert img dok kind QE Q s (k ()) t → Cert img dok kind QE Q s (.impure (.ok (.tlbi c)) k) t
  | cTe (s : Cst) (f : Arch.fault) (k : Unit → SailM X) (t : ExecSt) :
      Cert img dok kind QE Q s (k ()) t →
      Cert img dok kind QE Q s (.impure (.ok (.takeException f)) k) t
  | cRx (s : Cst) (a : Arch.pa) (k : Unit → SailM X) (t : ExecSt) :
      Cert img dok kind QE Q s (k ()) t →
      Cert img dok kind QE Q s (.impure (.ok (.returnException a)) k) t
  | cTs (s : Cst) (a : Arch.trans_start) (k : Unit → SailM X) (t : ExecSt) :
      Cert img dok kind QE Q s (k ()) t →
      Cert img dok kind QE Q s (.impure (.ok (.translationStart a)) k) t
  | cTx (s : Cst) (a : Arch.trans_end) (k : Unit → SailM X) (t : ExecSt) :
      Cert img dok kind QE Q s (k ()) t →
      Cert img dok kind QE Q s (.impure (.ok (.translationEnd a)) k) t
  | cCc (s : Cst) (k : Unit → SailM X) (t : ExecSt) :
      Cert img dok kind QE Q s (k ()) t → Cert img dok kind QE Q s (.impure (.ok .cycleCount) k) t
  | cMsg (s : Cst) (a : String) (k : Unit → SailM X) (t : ExecSt) :
      Cert img dok kind QE Q s (k ()) t → Cert img dok kind QE Q s (.impure (.ok (.message a)) k) t
  | cGcc (s : Cst) (k : Nat → SailM X) (t : ExecSt) :
      Cert img dok kind QE Q s (k (0 : Nat)) t →
      Cert img dok kind QE Q s (.impure (.ok .getCycleCount) k) t
  | cExt (s : Cst) (e : Sail.Error exception) (k : Empty → SailM X) (t : ExecSt) :
      QE s e t → Cert img dok kind QE Q s (.impure (.error e) k) t
  /-- (Lean-only, deviation 11) the row has ended: a plain RAM WRITE there is stuck (the write
  twin of `cEnd`) -/
  | cWrEnd (d : Cdata) (r : Bool) (n va : Nat)
      (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (Option Bool) Arch.abort → SailM X) (t : ExecSt) :
      devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      Cert img dok kind QE Q ⟨d, .BFin 0, r⟩ (.impure (.ok (.memWrite n va req)) k) t

end AxCert

/-! # 2. The kit -/

section cert
variable (img : Image) (dok : Int → Nat → Prop) (kind : Dkind)

theorem CertMono {X : Type} (QE QE' : Cst → Sail.Error exception → ExecSt → Prop)
    (Q Q' : Cst → X → ExecSt → Prop) (s : Cst) (m : SailM X) (t : ExecSt) :
    (∀ s' e t', QE s' e t' → QE' s' e t') → (∀ s' x t', Q s' x t' → Q' s' x t') →
    AxCert.Cert img dok kind QE Q s m t → AxCert.Cert img dok kind QE' Q' s m t := by
  intro HE HQ h
  induction h with
  | cRet s x t h => exact .cRet s x t (HQ s x t h)
  | cExt s e k t h => exact .cExt s e k t (HE s e t h)
  | cRd s r k t _ _ ihs ihn => exact .cRd s r k t ihs ihn
  | cWr s r v k t hr _ ih => exact .cWr s r v k t hr ih
  | cMrd d b r n va req k t vs h1 h2 h3 h4 _ ih => exact .cMrd d b r n va req k t vs h1 h2 h3 h4 ih
  | cIf s n va req k t vs h1 h2 h3 h4 _ ih => exact .cIf s n va req k t vs h1 h2 h3 h4 ih
  | cEnd d r n va req k t h1 h2 h3 => exact .cEnd d r n va req k t h1 h2 h3
  | cWrEnd d r n va req k t h1 h2 => exact .cWrEnd d r n va req k t h1 h2
  | cDrd b r n va req k t h1 h2 h3 h4 h5 _ ih => exact .cDrd b r n va req k t h1 h2 h3 h4 h5 ih
  | cDwr b r n va req k t v h1 h2 h3 h4 h5 _ ih => exact .cDwr b r n va req k t v h1 h2 h3 h4 h5 ih
  | cFence d b r bk k t h1 _ ih => exact .cFence d b r bk k t h1 ih
  | cXrd b r n va req k t h1 h2 h3 h4 _ ih => exact .cXrd b r n va req k t h1 h2 h3 h4 ih
  | cXwr aq rvs b r n va req k t v h1 h2 h3 h4 h5 _ ih =>
    exact .cXwr aq rvs b r n va req k t v h1 h2 h3 h4 h5 ih
  | cIa s n w k t hs _ ih => exact .cIa s n w k t hs ih
  | cSf d b r n w k t hs _ ih => exact .cSf d b r n w k t hs ih
  | cBa s n a k t _ ih => exact .cBa s n a k t ih
  | cCo s c k t _ ih => exact .cCo s c k t ih
  | cTl s c k t _ ih => exact .cTl s c k t ih
  | cTe s f k t _ ih => exact .cTe s f k t ih
  | cRx s a k t _ ih => exact .cRx s a k t ih
  | cTs s a k t _ ih => exact .cTs s a k t ih
  | cTx s a k t _ ih => exact .cTx s a k t ih
  | cCc s k t _ ih => exact .cCc s k t ih
  | cMsg s a k t _ ih => exact .cMsg s a k t ih
  | cGcc s k t _ ih => exact .cGcc s k t ih

theorem CertBind {X Y : Type} (QE : Cst → Sail.Error exception → ExecSt → Prop)
    (Q : Cst → Y → ExecSt → Prop) (m : SailM X) (f : X → SailM Y) (s : Cst) (t : ExecSt) :
    AxCert.Cert img dok kind QE (fun s' x t' => AxCert.Cert img dok kind QE Q s' (f x) t') s m t →
    AxCert.Cert img dok kind QE Q s (m >>= f) t := by
  intro h
  induction h with
  | cRet s x t h => exact h
  | cExt s e k t h => exact .cExt s e _ t h
  | cRd s r k t _ _ ihs ihn => exact .cRd s r _ t ihs ihn
  | cWr s r v k t hr _ ih => exact .cWr s r v _ t hr ih
  | cMrd d b r n va req k t vs h1 h2 h3 h4 _ ih => exact .cMrd d b r n va req _ t vs h1 h2 h3 h4 ih
  | cIf s n va req k t vs h1 h2 h3 h4 _ ih => exact .cIf s n va req _ t vs h1 h2 h3 h4 ih
  | cEnd d r n va req k t h1 h2 h3 => exact .cEnd d r n va req _ t h1 h2 h3
  | cWrEnd d r n va req k t h1 h2 => exact .cWrEnd d r n va req _ t h1 h2
  | cDrd b r n va req k t h1 h2 h3 h4 h5 _ ih => exact .cDrd b r n va req _ t h1 h2 h3 h4 h5 ih
  | cDwr b r n va req k t v h1 h2 h3 h4 h5 _ ih => exact .cDwr b r n va req _ t v h1 h2 h3 h4 h5 ih
  | cFence d b r bk k t h1 _ ih => exact .cFence d b r bk _ t h1 ih
  | cXrd b r n va req k t h1 h2 h3 h4 _ ih => exact .cXrd b r n va req _ t h1 h2 h3 h4 ih
  | cXwr aq rvs b r n va req k t v h1 h2 h3 h4 h5 _ ih =>
    exact .cXwr aq rvs b r n va req _ t v h1 h2 h3 h4 h5 ih
  | cIa s n w k t hs _ ih => exact .cIa s n w _ t hs ih
  | cSf d b r n w k t hs _ ih => exact .cSf d b r n w _ t hs ih
  | cBa s n a k t _ ih => exact .cBa s n a _ t ih
  | cCo s c k t _ ih => exact .cCo s c _ t ih
  | cTl s c k t _ ih => exact .cTl s c _ t ih
  | cTe s f k t _ ih => exact .cTe s f _ t ih
  | cRx s a k t _ ih => exact .cRx s a _ t ih
  | cTs s a k t _ ih => exact .cTs s a _ t ih
  | cTx s a k t _ ih => exact .cTx s a _ t ih
  | cCc s k t _ ih => exact .cCc s _ t ih
  | cMsg s a k t _ ih => exact .cMsg s a _ t ih
  | cGcc s k t _ ih => exact .cGcc s _ t ih

theorem CertBind0 {Y : Type} (QE : Cst → Sail.Error exception → ExecSt → Prop)
    (Q : Cst → Y → ExecSt → Prop) (m : SailM Unit) (n : SailM Y) (s : Cst) (t : ExecSt) :
    AxCert.Cert img dok kind QE (fun s' _ t' => AxCert.Cert img dok kind QE Q s' n t') s m t →
    AxCert.Cert img dok kind QE Q s (m >>= fun _ => n) t :=
  CertBind img dok kind QE Q m (fun _ => n) s t

theorem CertFact {X Y : Type} (QE : Cst → Sail.Error exception → ExecSt → Prop)
    (P : Cst → X → ExecSt → Prop) (Q : Cst → Y → ExecSt → Prop) (m : SailM X)
    (f : X → SailM Y) (s : Cst) (t : ExecSt) :
    AxCert.Cert img dok kind QE P s m t →
    (∀ s' x t', P s' x t' → AxCert.Cert img dok kind QE Q s' (f x) t') →
    AxCert.Cert img dok kind QE Q s (m >>= f) t := by
  intro Hm Hf
  exact CertBind img dok kind QE Q m f s t (CertMono img dok kind _ _ _ _ s m t (fun _ _ _ h => h) Hf Hm)

theorem CertRet {X : Type} (QE : Cst → Sail.Error exception → ExecSt → Prop)
    (Q : Cst → X → ExecSt → Prop) (s : Cst) (x : X) (t : ExecSt) :
    Q s x t → AxCert.Cert img dok kind QE Q s (pure x : SailM X) t :=
  fun h => .cRet s x t h

theorem CertReadReg (QE : Cst → Sail.Error exception → ExecSt → Prop) (r : Register)
    (Q : Cst → RegisterType r → ExecSt → Prop) (s : Cst) (t : ExecSt) :
    ¬ AxRunClose.pinReg r → Q s (t.regs r) t →
    AxCert.Cert img dok kind QE Q s (readReg r : SailM _) t :=
  fun hr hq => .cRd s r _ t (fun h => absurd h hr) (fun _ => .cRet _ _ t hq)

theorem CertWriteReg (QE : Cst → Sail.Error exception → ExecSt → Prop)
    (Q : Cst → PUnit → ExecSt → Prop) (r : Register) (v : RegisterType r) (s : Cst) (t : ExecSt) :
    ¬ AxRunClose.pinReg r → Q s PUnit.unit (t.setReg r v) →
    AxCert.Cert img dok kind QE Q s (writeReg r v : SailM _) t :=
  fun hr hq => .cWr s r v _ t hr (.cRet _ _ _ hq)

theorem CertTryCatch {X : Type} (QE1 QE2 : Cst → Sail.Error exception → ExecSt → Prop)
    (Q : Cst → X → ExecSt → Prop) (m : SailM X) (h : Sail.Error exception → SailM X) (s : Cst)
    (t : ExecSt) :
    (∀ s' e t', QE1 s' e t' → AxCert.Cert img dok kind QE2 Q s' (h e) t') →
    AxCert.Cert img dok kind QE1 Q s m t →
    AxCert.Cert img dok kind QE2 Q s (PreSail.tryCatchAll m h) t := by
  intro Hh H
  induction H with
  | cRet s x t h => exact .cRet s x t h
  | cExt s e k t he => exact Hh s e t he
  | cRd s r k t _ _ ihs ihn => exact .cRd s r _ t ihs ihn
  | cWr s r v k t hr _ ih => exact .cWr s r v _ t hr ih
  | cMrd d b r n va req k t vs h1 h2 h3 h4 _ ih => exact .cMrd d b r n va req _ t vs h1 h2 h3 h4 ih
  | cIf s n va req k t vs h1 h2 h3 h4 _ ih => exact .cIf s n va req _ t vs h1 h2 h3 h4 ih
  | cEnd d r n va req k t h1 h2 h3 => exact .cEnd d r n va req _ t h1 h2 h3
  | cWrEnd d r n va req k t h1 h2 => exact .cWrEnd d r n va req _ t h1 h2
  | cDrd b r n va req k t h1 h2 h3 h4 h5 _ ih => exact .cDrd b r n va req _ t h1 h2 h3 h4 h5 ih
  | cDwr b r n va req k t v h1 h2 h3 h4 h5 _ ih => exact .cDwr b r n va req _ t v h1 h2 h3 h4 h5 ih
  | cFence d b r bk k t h1 _ ih => exact .cFence d b r bk _ t h1 ih
  | cXrd b r n va req k t h1 h2 h3 h4 _ ih => exact .cXrd b r n va req _ t h1 h2 h3 h4 ih
  | cXwr aq rvs b r n va req k t v h1 h2 h3 h4 h5 _ ih =>
    exact .cXwr aq rvs b r n va req _ t v h1 h2 h3 h4 h5 ih
  | cIa s n w k t hs _ ih => exact .cIa s n w _ t hs ih
  | cSf d b r n w k t hs _ ih => exact .cSf d b r n w _ t hs ih
  | cBa s n a k t _ ih => exact .cBa s n a _ t ih
  | cCo s c k t _ ih => exact .cCo s c _ t ih
  | cTl s c k t _ ih => exact .cTl s c _ t ih
  | cTe s f k t _ ih => exact .cTe s f _ t ih
  | cRx s a k t _ ih => exact .cRx s a _ t ih
  | cTs s a k t _ ih => exact .cTs s a _ t ih
  | cTx s a k t _ ih => exact .cTx s a _ t ih
  | cCc s k t _ ih => exact .cCc s _ t ih
  | cMsg s a k t _ ih => exact .cMsg s a _ t ih
  | cGcc s k t _ ih => exact .cGcc s _ t ih

theorem CertLiftRAny {R X : Type} (QE QE' : Cst → Sail.Error exception → ExecSt → Prop)
    (Q : Cst → X → ExecSt → Prop) (m : SailM X) (s : Cst) (t : ExecSt) :
    (∀ s' e t', QE s' e t' → QE' s' e t') →
    AxCert.Cert img dok kind QE Q s m t →
    AxCert.Cert img dok kind QE'
      (fun s' (r : Except (Sail.Error exception ⊕ R) X) t' =>
        match r with
        | .ok x => Q s' x t'
        | .error _ => False)
      s (ExceptT.run (liftM m : SailME R X)) t := by
  intro HE H
  have e : ExceptT.run (liftM m : SailME R X) = m >>= fun a => pure (Except.ok a) := rfl
  rw [e]
  apply CertBind
  exact CertMono img dok kind QE QE' Q _ s m t HE (fun s' x t' h => .cRet _ _ t' h) H

theorem CertCatchEarlyReturn {X : Type} (QE : Cst → Sail.Error exception → ExecSt → Prop)
    (Q : Cst → X → ExecSt → Prop) (m : SailME X X) (s : Cst) (t : ExecSt) :
    AxCert.Cert img dok kind QE
      (fun s' (r : Except (Sail.Error exception ⊕ X) X) t' =>
        match r with
        | .ok x => Q s' x t'
        | .error (.inr x) => Q s' x t'
        | .error (.inl e) => QE s' e t')
      s (ExceptT.run m) t →
    AxCert.Cert img dok kind QE Q s (SailME.run m) t := by
  intro H
  show AxCert.Cert img dok kind QE Q s (ExceptT.run m >>= _) t
  apply CertBind
  refine CertMono img dok kind QE QE _ _ s _ t (fun _ _ _ h => h) ?_ H
  intro s' r t' hr
  rcases r with (e | x) | x
  · exact .cExt s' e _ t' hr
  · exact .cRet s' x t' hr
  · exact .cRet s' x t' hr

end cert

/-! # 3. EMBEDDINGS: EvA, EvB, EvD are special cases -/

/-- `EvA` embeds at `BInf`, at any fixed data state `d` and flag `r` (deviation 1: an `evMrd`
node is a `cIf` fetch or a `cMrd` graph read, by its `akIfetch`). -/
theorem CertOfEvA (img : Image) (dok : Int → Nat → Prop) (kind : Dkind) {X : Type}
    (QE : Sail.Error exception → ExecSt → Prop) (Q : X → ExecSt → Prop) (d : Cdata) (r : Bool)
    (m : SailM X) (t : ExecSt) :
    EvA img QE Q m t →
    AxCert.Cert img dok kind (fun s e t' => s = ⟨d, .BInf, r⟩ ∧ QE e t')
      (fun s x t' => s = ⟨d, .BInf, r⟩ ∧ Q x t') ⟨d, .BInf, r⟩ m t := by
  intro h
  induction h with
  | evRet x t h => exact .cRet _ x t ⟨rfl, h⟩
  | evExt e k t h => exact .cExt _ e k t ⟨rfl, h⟩
  | evRd r0 k t _ _ ihs ihn => exact .cRd _ r0 k t ihs ihn
  | evWr r0 v k t hr _ ih => exact .cWr _ r0 v k t hr ih
  | evMrd n va req k t vs h1 h2 h3 _ ih =>
    cases hf : (classify req.access_kind).akIfetch with
    | true => exact .cIf _ n va req k t vs h1 h2 hf h3 ih
    | false => exact .cMrd d .BInf r n va req k t vs h1 h2 hf h3 ih
  | evIa n w k t hs _ ih => exact .cIa _ n w k t hs ih
  | evBa n a k t _ ih => exact .cBa _ n a k t ih
  | evCo c k t _ ih => exact .cCo _ c k t ih
  | evTl c k t _ ih => exact .cTl _ c k t ih
  | evTe f k t _ ih => exact .cTe _ f k t ih
  | evRx a k t _ ih => exact .cRx _ a k t ih
  | evTs a k t _ ih => exact .cTs _ a k t ih
  | evTx a k t _ ih => exact .cTx _ a k t ih
  | evCc k t _ ih => exact .cCc _ k t ih
  | evMsg a k t _ ih => exact .cMsg _ a k t ih
  | evGcc k t _ ih => exact .cGcc _ k t ih

/-- `EvB` embeds at `BFin b`; the budget left at a `pure` is reported. -/
theorem CertOfEvB (img : Image) (dok : Int → Nat → Prop) (kind : Dkind) {X : Type}
    (QE : Sail.Error exception → ExecSt → Prop) (Q : Nat → X → ExecSt → Prop) (d : Cdata)
    (r : Bool) (m : SailM X) (t : ExecSt) (b : Nat)
    (HQE : ∀ t', ¬ ∀ e, QE e t') :
    EvB img QE Q m t b →
    AxCert.Cert img dok kind (fun s e t' => ∃ b', s = ⟨d, .BFin b', r⟩ ∧ QE e t')
      (fun s x t' => ∃ b', s = ⟨d, .BFin b', r⟩ ∧ Q b' x t') ⟨d, .BFin b, r⟩ m t := by
  intro h
  induction h with
  | ebNf _ _ _ _ t _ _ _ _ hq => exact absurd hq (HQE t)
  | ebRet x t b h => exact .cRet _ x t ⟨b, rfl, h⟩
  | ebExt e k t b h => exact .cExt _ e k t ⟨b, rfl, h⟩
  | ebRd r0 k t b _ _ ihs ihn => exact .cRd _ r0 k t ihs ihn
  | ebWr r0 v k t b hr _ ih => exact .cWr _ r0 v k t hr ih
  | ebMrd n va req k t b vs h1 h2 h3 h4 _ ih => exact .cMrd d (.BFin b) r n va req k t vs h1 h2 h3 h4 ih
  | ebIf n va req k t b vs h1 h2 h3 h4 _ ih => exact .cIf _ n va req k t vs h1 h2 h3 h4 ih
  | ebEnd n va req k t h1 h2 h3 => exact .cEnd d r n va req k t h1 h2 h3
  | ebIa n w k t b hs _ ih => exact .cIa _ n w k t hs ih
  | ebBa n a k t b _ ih => exact .cBa _ n a k t ih
  | ebCo c k t b _ ih => exact .cCo _ c k t ih
  | ebTl c k t b _ ih => exact .cTl _ c k t ih
  | ebTe f k t b _ ih => exact .cTe _ f k t ih
  | ebRx a k t b _ ih => exact .cRx _ a k t ih
  | ebTs a k t b _ ih => exact .cTs _ a k t ih
  | ebTx a k t b _ ih => exact .cTx _ a k t ih
  | ebCc k t b _ ih => exact .cCc _ k t ih
  | ebMsg a k t b _ ih => exact .cMsg _ a k t ih
  | ebGcc k t b _ ih => exact .cGcc _ k t ih

/-- `EvD`'s kind flag as a `Dkind`. -/
def dkOf (kb : Bool) : Dkind := if kb then .DKLd else .DKSt

/-- The data state, forgotten to `EvD`'s. -/
def cdOf (d : Cdata) : AxSymMem.Dstate :=
  match d with
  | .CPend => .DPend
  | .CLd vs | .CSt vs _ | .CRmwR _ vs | .CRmw _ _ _ vs _ => .DDone vs

theorem cdOfPend (d : Cdata) : cdOf d = .DPend → d = .CPend := by
  cases d <;> simp [cdOf]

/-- `EvD` embeds at `BInf`: the data state is forgotten through `cdOf`. -/
theorem CertOfEvD (img : Image) (dok : Int → Nat → Prop) (kb : Bool) {X : Type}
    (QE : AxSymMem.Dstate → Sail.Error exception → ExecSt → Prop)
    (Q : AxSymMem.Dstate → X → ExecSt → Prop) (d : AxSymMem.Dstate) (m : SailM X) (t : ExecSt) :
    EvD img dok kb QE Q d m t →
    ∀ cd r, cdOf cd = d →
    AxCert.Cert img dok (dkOf kb) (fun s e t' => QE (cdOf s.csD) e t')
      (fun s x t' => Q (cdOf s.csD) x t') ⟨cd, .BInf, r⟩ m t := by
  intro h
  induction h with
  | evdRet d x t h => intro cd r hcd; exact .cRet _ x t (by simp only []; rw [hcd]; exact h)
  | evdExt d e k t h => intro cd r hcd; exact .cExt _ e k t (by simp only []; rw [hcd]; exact h)
  | evdRd d r0 k t _ _ ihs ihn =>
    intro cd r hcd
    exact .cRd _ r0 k t (fun hp v => ihs hp v cd r hcd) (fun hp => ihn hp cd r hcd)
  | evdWr d r0 v k t hr _ ih => intro cd r hcd; exact .cWr _ r0 v k t hr (ih cd r hcd)
  | evdMrd d n va req k t vs h1 h2 h3 _ ih =>
    intro cd r hcd
    cases hf : (classify req.access_kind).akIfetch with
    | true => exact .cIf _ n va req k t vs h1 h2 hf h3 (ih cd r hcd)
    | false => exact .cMrd cd .BInf r n va req k t vs h1 h2 hf h3 (ih cd r hcd)
  | evdDrd n va req k t hk h1 h2 h3 h4 _ ih =>
    intro cd r hcd
    rw [cdOfPend cd hcd]
    exact .cDrd .BInf r n va req k t (by rw [hk]; rfl) h1 h2 h3 h4
      (fun vs hvs => ih vs hvs (.CLd vs) r rfl)
  | evdDwr n va req k t v hk h1 h2 h3 h4 _ ih =>
    intro cd r hcd
    rw [cdOfPend cd hcd]
    exact .cDwr .BInf r n va req k t v (by rw [hk]; rfl) h1 h2 h3 h4
      (ih (.CSt (WeakInterpProj.wbytes n v) (wcls req.access_kind r)) false rfl)
  | evdIa d n w k t hs _ ih => intro cd r hcd; exact .cIa _ n w k t hs (ih cd r hcd)
  | evdBa d n a k t _ ih => intro cd r hcd; exact .cBa _ n a k t (ih cd r hcd)
  | evdCo d c k t _ ih => intro cd r hcd; exact .cCo _ c k t (ih cd r hcd)
  | evdTl d c k t _ ih => intro cd r hcd; exact .cTl _ c k t (ih cd r hcd)
  | evdTe d f k t _ ih => intro cd r hcd; exact .cTe _ f k t (ih cd r hcd)
  | evdRx d a k t _ ih => intro cd r hcd; exact .cRx _ a k t (ih cd r hcd)
  | evdTs d a k t _ ih => intro cd r hcd; exact .cTs _ a k t (ih cd r hcd)
  | evdTx d a k t _ ih => intro cd r hcd; exact .cTx _ a k t (ih cd r hcd)
  | evdCc d k t _ ih => intro cd r hcd; exact .cCc _ k t (ih cd r hcd)
  | evdMsg d a k t _ ih => intro cd r hcd; exact .cMsg _ a k t (ih cd r hcd)
  | evdGcc d k t _ ih => intro cd r hcd; exact .cGcc _ k t (ih cd r hcd)

/-- THE SC TRANSFER, through `rfF` (fail-tolerant): an `rfF` tree's successful SC `exec` run is
a `Cert` at every state, the state unchanged (no row item, no data event, no fence). -/
theorem CertOfRfF (img : Image) (dok : Int → Nat → Prop) (kind : Dkind) {X : Type}
    (QE : Cst → Sail.Error exception → ExecSt → Prop) (m : SailM X) :
    rfF m → ∀ s t x t', exec m t = some (x, t') →
    AxCert.Cert img dok kind QE (fun s' x' t'' => s' = s ∧ x' = x ∧ t'' = t') s m t := by
  induction m with
  | pure y =>
    intro _ s t x t' he
    simp only [exec, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact .cRet s y t ⟨rfl, rfl, rfl⟩
  | impure call k ih =>
    intro hrf s t x t' he
    cases call with
    | error e => cases he
    | ok o =>
      cases o
      case regRead r =>
        exact .cRd s r k t (fun hp => absurd hp hrf.1) (fun _ => ih _ (hrf.2 _) s t x t' he)
      case regWrite r v => exact .cWr s r v k t hrf.1 (ih _ hrf.2 s _ x t' he)
      case memRead => exact False.elim hrf
      case memWrite => exact False.elim hrf
      case barrier => exact False.elim hrf
      case instrAnnounce n w => exact .cIa s n w k t hrf.1 (ih _ hrf.2 s t x t' he)
      case choose => cases he
      case readRam => cases he
      case writeRam => cases he
      case cacheOp c => exact .cCo s c k t (ih _ hrf s t x t' he)
      case tlbi c => exact .cTl s c k t (ih _ hrf s t x t' he)
      case translationStart a => exact .cTs s a k t (ih _ hrf s t x t' he)
      case translationEnd a => exact .cTx s a k t (ih _ hrf s t x t' he)
      case takeException f => exact .cTe s f k t (ih _ hrf s t x t' he)
      case returnException a => exact .cRx s a k t (ih _ hrf s t x t' he)
      case cycleCount => exact .cCc s k t (ih _ hrf s t x t' he)
      case getCycleCount => exact .cGcc s k t (ih _ hrf s t x t' he)
      case message a => exact .cMsg s a k t (ih _ hrf s t x t' he)
      case branchAnnounce n a => exact .cBa s n a k t (ih _ hrf s t x t' he)

/-- The same, keeping ANY post the run's end state satisfies. -/
theorem CertOfRfFPost (img : Image) (dok : Int → Nat → Prop) (kind : Dkind) {X : Type}
    (QE : Cst → Sail.Error exception → ExecSt → Prop) (Q : Cst → X → ExecSt → Prop)
    (m : SailM X) (s : Cst) (t : ExecSt) (x : X) (t' : ExecSt) :
    rfF m → exec m t = some (x, t') → Q s x t' → AxCert.Cert img dok kind QE Q s m t := by
  intro Hrf He HQ
  refine CertMono img dok kind QE QE _ Q s m t (fun _ _ _ h => h) ?_
    (CertOfRfF img dok kind QE m Hrf s t x t' He)
  rintro _ _ _ ⟨rfl, rfl, rfl⟩
  exact HQ

/-! # 4. Classes -/

/-- FAITHFULNESS: at a plain store node, the class the language stamps (`lcls`) is `wcls`. -/
theorem wclsFaithful (cpu : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (K : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (rl : Bool) (base : Int)
    (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (r : Bool) :
    lcls (.PHart cpu (.impure (.ok (.memWrite n va req)) K) rs fn ib)
      (LStore rl base data asrc vsrc) r = wcls req.access_kind r := rfl

/-- … and at an exclusive store node. -/
theorem wclsFaithfulEx (cpu : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (K : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (rl : Bool) (base : Int)
    (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (r : Bool) :
    lcls (.PHart cpu (.impure (.ok (.memWrite n va req)) K) rs fn ib)
      (LExStore rl base data asrc vsrc) r = wcls req.access_kind r := rfl

/-- An exclusive write is `WCexcl`. -/
theorem wclsLatest (ak : AK) (r : Bool) : (classify ak).akLatest = true → wcls ak r = .WCexcl := by
  intro H
  simp only [wcls, wmClassOf, H, ↓reduceIte]

/-- A plain store after a `pw && sw` fence (flag armed) is `WCrel`. -/
theorem wclsArmed (ak : AK) : (classify ak).akLatest = false → wcls ak true = .WCrel := by
  intro H
  simp only [wcls, wmClassOf, H, relpWs, Bool.true_or, Bool.false_eq_true, ↓reduceIte]

/-- `relpUpd` at a barrier label: `fence rw,w` arms the flag. -/
theorem relpUpdRwW (r : Bool) : relpUpd (ebarLabel .Barrier_RISCV_rw_w) r = true := rfl

/-- THE DERIVED RMW CLASS (constraint I, `.aqrl` AMOs): `wmClassOf` checks `akLatest` before
`akSync`, so an RMW write is `WCexcl` even when it carries `.rl`; `wclsRmw` lets the `.rl` bit
win.  Not used by the bridge; for `amoswap.w.aq` the two agree (`wclsRmwNorl`). -/
def wclsRmw (ak : AK) (r : Bool) : WmClass :=
  if (classify ak).akSync then .WCrel else wcls ak r

theorem wclsRmwNorl (ak : AK) (r : Bool) :
    (classify ak).akSync = false → wclsRmw ak r = wcls ak r := by
  intro H
  simp only [wclsRmw, H, Bool.false_eq_true, ↓reduceIte]

end Weak
