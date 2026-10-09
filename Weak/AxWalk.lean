/-
Weak: **constraint A, ENGINE SIDE: the POSITIONAL multi-event certificate** `CertWP` — the
`CertW` of `AxDataX9` made position-exact.

Rocq: `iris/AxWalk.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`CertWP … ws s k m t` is `CertW` with
- an exact ROW POSITION index `k` (the opax thread's `atK`): every row-consuming node moves
  `k ↦ k + 1` (graph image read, data read / write, fence, the RMW write halves, walker reads);
  the fused RMW read halves (`pXrd`, `pWxrd`) keep `k` (`aidentAdvRd (.IRmw …) = 0`);
- walker events recorded WITH their row position: `ws : List (Nat × Wev)` — `(k, .WRd a vs)` is
  the walker read at row position `k`, `(k, .WRmwR a vs)` / `(k, .WRmw a rvs wvs)` the two halves
  of the walker's fused A/D RMW at row position `k` (the `IRmw` item); the TAG IS THE
  CONSTRUCTOR (Sail tags walker reads like data loads);
- POSITIONAL side conditions in place of the region-wide `HnoRmw` / `HnoSplit`: a plain read
  node (data `pDrd` or walker `pWrd`) at `k` carries `pR D k` ("the row item at `k` is no fused
  RMW at a `D` address"), an exclusive read node (`pXrd` / `pWxrd`) carries `pX D k` ("the row
  item at `k` is no plain read at a `D` address").  The bridge (AxWalk2) instantiates
  `pR := posR G i`, `pX := posX G i` (§2) — the region form is the special case
  `∀ k, posR G i D k` (`CertWPOfCertW`, §4);
- PINS for walker reads: a plain walker read's continuation may assume `wpin k a vs` (delivered
  by the walker FLOW's output, AxWalk2), the fused RMW read half's continuation may assume
  `xpin k a vs`.  With `wpin := xpin := fun _ _ _ => True` the walker reads are fully demonic.

§1 the inductive; §3 the kit (`CertWPMono`, `CertWPBind(0)`, `CertWPFact`, `CertWPTryCatch`,
`CertWPLiftR(Any)`, `CertWPCatchEarlyReturn`, read/write reg, `CertWPExecARfF` — a
register-only (`rfF`) `execA` fact is a certificate at the SAME position, which makes the
position-exact replay possible without `EvA`'s image reads); §2 `posR`/`posX`/`wtagOf`; §4 the
region-form embedding `CertWPOfCertW`.

## Deviations from Rocq

1. AS `AxDataX9` deviation 1 (and `AxCert` deviations 1–5, 7): `CertWP` is on `SailM X`; Rocq's
   extra-outcome type `E` ↦ the failure node `.impure (.error e)` with `e : Sail.Error exception`
   (`pExt`, continuation `Empty → SailM X`); `seip_reg` ↦ `AxRunClose.pinReg`; register events
   carry no access kind; `pMrd` is the GRAPH image read (`akIfetch = false`, Rocq `ak_coh = false`
   renamed; one row item, `k ↦ k + 1`), and the Lean-only constructor `pIf` is an image FETCH
   (`akIfetch = true`, the pinned admin step: budget, position `k` and `ws` kept — needed so
   `CertWPOfCertW` covers `CertW.wIf`); `pEnd`, `pDrd` and `pWrd` take `akIfetch = false`
   (`pWrd`: O2 Stage C, `AxDataX9` deviation 2); `pIa` takes `sfAnnB n w = false`; writes
   (`pDwr`, `pXwr`, `pWxwr`) take `v` with `req.value = some v`, record
   `WeakInterpProj.wbytes n v` and continue at `.Ok (some true)` (Rocq `inl None`); read answers
   are `.Ok (wordOfBytes n vs, none)`.
   Q19 (provisional, as `AxCert` deviation 10): the Lean-only constructor `pSf` (an SFENCE.VMA
   announce, `sfAnnB n w = true`: the marker fence, one row item `k ↦ k + 1`, `ws` kept), so
   that `CertWPOfCertW` covers `CertW.wSf`.
2. THE KIT on one error type (as `AxCert` deviation 4): `CertWPTryCatch` is about
   `PreSail.tryCatchAll`; `CertWPLiftRAny` / `CertWPLiftR` are stated on
   `ExceptT.run (liftM m : SailME R X)` (result `.ok x ↦ Q`, `.error _` excluded; failure nodes
   mapped by `HE : QE ⊆ QE'`, Rocq's `inr` injection); `CertWPCatchEarlyReturn` takes the
   certificate of `ExceptT.run m` (`.ok x`/`.error (.inr x)` ↦ `Q`, `.error (.inl e)` ↦ `QE`) and
   concludes on `SailME.run m`.  `Defs.bind0 m n` ↦ `m >>= fun _ => n`, `returnm` ↦ `pure`,
   `read_reg`/`write_reg` ↦ `readReg`/`writeReg`.
3. `CertWPExecARfF` / `CertWPExecARfFPost`: `sregs`/`mem`/`mdev` ↦ `regs`/`mem`/`dev`;
   `MState r m d` ↦ the `ExecSt` literal `⟨r, m, d⟩`.
4. `wtagOf`: Rocq `list_find` (index and element) ↦ `List.find?` (the element; Rocq projects the
   index away).  `posR`/`posX`: `gdexec` ↦ `Gdexec`, `agent` ↦ `Nat`, `grow GD i !! k` ↦
   `(AxOpsem.grow GD i)[k]?`.
5. TYPES: `Z` ↦ `Int`, `list (bv 8)` ↦ `List (BitVec 8)`, `N.to_nat n` ↦ `n : Nat`, `S k` ↦
   `k + 1`, `pa_z` ↦ `paZ`, `img_bytes` ↦ `imgBytes`, `map snd` ↦ `List.map Prod.snd`.

**Rocq → Lean name map.**  `CertWP` `CertWP` (constructors `p_ret` `pRet`, `p_rd` `pRd`, `p_wr`
`pWr`, `p_mrd` `pMrd`, `p_end` `pEnd`, `p_drd` `pDrd`, `p_dwr` `pDwr`, `p_fence` `pFence`, `p_xrd`
`pXrd`, `p_xwr` `pXwr`, `p_ia` `pIa`, `p_ba` `pBa`, `p_co` `pCo`, `p_tl` `pTl`, `p_te` `pTe`,
`p_rx` `pRx`, `p_ts` `pTs`, `p_tx` `pTx`, `p_cc` `pCc`, `p_msg` `pMsg`, `p_gcc` `pGcc`, `p_ext`
`pExt`, `p_wrd` `pWrd`, `p_wxrd` `pWxrd`, `p_wxwr` `pWxwr`; Lean-only `pIf`, `pSf`),
`CertWP_mono` `CertWPMono`, `CertWP_bind` `CertWPBind`, `CertWP_bind0` `CertWPBind0`, `CertWP_fact`
`CertWPFact`, `CertWP_ret` `CertWPRet`, `CertWP_read_reg` `CertWPReadReg`, `CertWP_write_reg`
`CertWPWriteReg`, `CertWP_try_catch` `CertWPTryCatch`, `CertWP_liftR_any` `CertWPLiftRAny`,
`CertWP_liftR` `CertWPLiftR`, `CertWP_catch_early_return` `CertWPCatchEarlyReturn`,
`CertWP_execA_rfF` `CertWPExecARfF`, `CertWP_execA_rfF_post` `CertWPExecARfFPost`, `posR` `posR`,
`posX` `posX`, `posR_anti` `posRAnti`, `posX_anti` `posXAnti`, `wtag_of` `wtagOf`,
`CertWP_of_CertW` `CertWPOfCertW`.  None is in the duplicated-name table.

**Dropped:** nothing (Rocq 1 inductive + 3 definitions + 16 lemmas; Lean the same, + the
Lean-only constructors `pIf`, `pSf`).  **Not ported:** the section-local Ltac `certwp_ctor` (Lean proofs
name the constructor per case) and the `Print Assumptions` lines.
-/
import Weak.AxDataX9
import Weak.AxSpineOk

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D

/-! # 1. The positional certificate -/

/-- THE POSITIONAL MULTI-EVENT CERTIFICATE (see the header). -/
inductive CertWP (img : Image) (dok wok : Int → Nat → Prop) (kind : Dkind)
    (pR pX : (Int → Nat → Prop) → Nat → Prop) (wpin xpin : Nat → Int → List (BitVec 8) → Prop)
    {X : Type}
    (QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop)
    (Q : List (Nat × Wev) → Cst → Nat → X → ExecSt → Prop) :
    List (Nat × Wev) → Cst → Nat → SailM X → ExecSt → Prop where
  | pRet (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (x : X) (t : ExecSt) :
      Q ws s k x t → CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (.pure x) t
  | pRd (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (r : Register) (kk : RegisterType r → SailM X)
      (t : ExecSt) :
      (AxRunClose.pinReg r → ∀ v, CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (kk v) t) →
      (¬ AxRunClose.pinReg r →
        CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (kk (t.regs r)) t) →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (.impure (.ok (.regRead r)) kk) t
  | pWr (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (r : Register) (v : RegisterType r)
      (kk : PUnit → SailM X) (t : ExecSt) :
      ¬ AxRunClose.pinReg r →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (kk PUnit.unit) (t.setReg r v) →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (.impure (.ok (.regWrite r v)) kk) t
  /-- an IMAGE graph read: one row item -/
  | pMrd (ws : List (Nat × Wev)) (d : Cdata) (b : Bud) (r : Bool) (k : Nat) (n va : Nat)
      (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (kk : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt)
      (vs : List (BitVec 8)) :
      devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      (classify req.access_kind).akIfetch = false →
      imgBytes img (paZ req.pa) n = some vs →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws ⟨d, b, r⟩ (k + 1)
        (kk (.Ok (wordOfBytes n vs, none))) t →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws ⟨d, bsucc b, r⟩ k
        (.impure (.ok (.memRead n va req)) kk) t
  /-- (Lean-only, deviation 1) an image FETCH: the pinned admin step, no row item -/
  | pIf (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (n va : Nat)
      (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (kk : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt)
      (vs : List (BitVec 8)) :
      devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      (classify req.access_kind).akIfetch = true →
      imgBytes img (paZ req.pa) n = some vs →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (kk (.Ok (wordOfBytes n vs, none))) t →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (.impure (.ok (.memRead n va req)) kk) t
  /-- the row has ended: a plain RAM graph read there is stuck -/
  | pEnd (ws : List (Nat × Wev)) (d : Cdata) (r : Bool) (k : Nat) (n va : Nat)
      (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (kk : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt) :
      devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      (classify req.access_kind).akIfetch = false →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws ⟨d, .BFin 0, r⟩ k
        (.impure (.ok (.memRead n va req)) kk) t
  /-- the DATA read — demonic, positional `pR` -/
  | pDrd (ws : List (Nat × Wev)) (b : Bud) (r : Bool) (k : Nat) (n va : Nat)
      (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (kk : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt) :
      kind = .DKLd → devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      (classify req.access_kind).akIfetch = false →
      dok (paZ req.pa) n → pR dok k →
      (∀ vs : List (BitVec 8), vs.length = n →
        CertWP img dok wok kind pR pX wpin xpin QE Q ws ⟨.CLd vs, b, r⟩ (k + 1)
          (kk (.Ok (wordOfBytes n vs, none))) t) →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws ⟨.CPend, bsucc b, r⟩ k
        (.impure (.ok (.memRead n va req)) kk) t
  /-- the DATA write -/
  | pDwr (ws : List (Nat × Wev)) (b : Bud) (r : Bool) (k : Nat) (n va : Nat)
      (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
      (kk : Result (Option Bool) Arch.abort → SailM X) (t : ExecSt) (v : BitVec (8 * n)) :
      kind = .DKSt → devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      req.value = some v →
      dok (paZ req.pa) n →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws
        ⟨.CSt (WeakInterpProj.wbytes n v) (wcls req.access_kind r), b, false⟩ (k + 1)
        (kk (.Ok (some true))) t →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws ⟨.CPend, bsucc b, r⟩ k
        (.impure (.ok (.memWrite n va req)) kk) t
  /-- a fence event, one row item -/
  | pFence (ws : List (Nat × Wev)) (d : Cdata) (b : Bud) (r : Bool) (k : Nat) (bk : barrier_kind)
      (kk : Unit → SailM X) (t : ExecSt) :
      ebarPark bk = none →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws ⟨d, b, relpUpd (ebarLabel bk) r⟩ (k + 1)
        (kk ()) t →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws ⟨d, bsucc b, r⟩ k
        (.impure (.ok (.barrier bk)) kk) t
  /-- the RMW read half: exclusive read, demonic, no row item consumed, positional `pX` -/
  | pXrd (ws : List (Nat × Wev)) (b : Bud) (r : Bool) (k : Nat) (n va : Nat)
      (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (kk : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt) :
      kind = .DKRmw → devAddr req.pa = false → (classify req.access_kind).akLatest = true →
      dok (paZ req.pa) n → pX dok k →
      (∀ vs : List (BitVec 8), vs.length = n →
        CertWP img dok wok kind pR pX wpin xpin QE Q ws
          ⟨.CRmwR (classify req.access_kind).akSync vs, b, r⟩ k
          (kk (.Ok (wordOfBytes n vs, none))) t) →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws ⟨.CPend, b, r⟩ k
        (.impure (.ok (.memRead n va req)) kk) t
  /-- the RMW write half: exclusive write (success branch), one row item -/
  | pXwr (ws : List (Nat × Wev)) (aq : Bool) (rvs : List (BitVec 8)) (b : Bud) (r : Bool)
      (k : Nat) (n va : Nat)
      (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
      (kk : Result (Option Bool) Arch.abort → SailM X) (t : ExecSt) (v : BitVec (8 * n)) :
      kind = .DKRmw → devAddr req.pa = false → (classify req.access_kind).akLatest = true →
      req.value = some v →
      dok (paZ req.pa) n →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws
        ⟨.CRmw aq (classify req.access_kind).akSync rvs (WeakInterpProj.wbytes n v)
          (wcls req.access_kind r), b, false⟩ (k + 1)
        (kk (.Ok (some true))) t →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws ⟨.CRmwR aq rvs, bsucc b, r⟩ k
        (.impure (.ok (.memWrite n va req)) kk) t
  | pIa (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (n : Nat) (w : BitVec n) (kk : Unit → SailM X)
      (t : ExecSt) :
      sfAnnB n w = false → CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (kk ()) t →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (.impure (.ok (.instrAnnounce n w)) kk) t
  /-- (Lean-only, Q19) the SFENCE.VMA announce: the marker fence, one row item -/
  | pSf (ws : List (Nat × Wev)) (d : Cdata) (b : Bud) (r : Bool) (k : Nat) (n : Nat)
      (w : BitVec n) (kk : Unit → SailM X) (t : ExecSt) :
      sfAnnB n w = true →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws ⟨d, b, r⟩ (k + 1) (kk ()) t →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws ⟨d, bsucc b, r⟩ k
        (.impure (.ok (.instrAnnounce n w)) kk) t
  | pBa (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (n : Nat) (a : BitVec n) (kk : Unit → SailM X)
      (t : ExecSt) :
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (kk ()) t →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k
        (.impure (.ok (.branchAnnounce n a)) kk) t
  | pCo (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (c : Arch.cache_op) (kk : Unit → SailM X)
      (t : ExecSt) :
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (kk ()) t →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (.impure (.ok (.cacheOp c)) kk) t
  | pTl (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (c : Arch.tlb_op) (kk : Unit → SailM X)
      (t : ExecSt) :
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (kk ()) t →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (.impure (.ok (.tlbi c)) kk) t
  | pTe (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (f : Arch.fault) (kk : Unit → SailM X)
      (t : ExecSt) :
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (kk ()) t →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (.impure (.ok (.takeException f)) kk) t
  | pRx (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (a : Arch.pa) (kk : Unit → SailM X)
      (t : ExecSt) :
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (kk ()) t →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (.impure (.ok (.returnException a)) kk) t
  | pTs (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (a : Arch.trans_start) (kk : Unit → SailM X)
      (t : ExecSt) :
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (kk ()) t →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k
        (.impure (.ok (.translationStart a)) kk) t
  | pTx (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (a : Arch.trans_end) (kk : Unit → SailM X)
      (t : ExecSt) :
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (kk ()) t →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (.impure (.ok (.translationEnd a)) kk) t
  | pCc (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (kk : Unit → SailM X) (t : ExecSt) :
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (kk ()) t →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (.impure (.ok .cycleCount) kk) t
  | pMsg (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (a : String) (kk : Unit → SailM X)
      (t : ExecSt) :
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (kk ()) t →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (.impure (.ok (.message a)) kk) t
  | pGcc (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (kk : Nat → SailM X) (t : ExecSt) :
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (kk (0 : Nat)) t →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (.impure (.ok .getCycleCount) kk) t
  | pExt (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (e : Sail.Error exception)
      (kk : Empty → SailM X) (t : ExecSt) :
      QE ws s k e t → CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (.impure (.error e) kk) t
  /-- THE WALKER ARM, position-exact: a walker read at row position `k`, recorded with `k` -/
  | pWrd (ws : List (Nat × Wev)) (d : Cdata) (b : Bud) (r : Bool) (k : Nat) (n va : Nat)
      (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (kk : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt) :
      devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      (classify req.access_kind).akIfetch = false →
      wok (paZ req.pa) n → pR wok k →
      (∀ vs : List (BitVec 8), vs.length = n → wpin k (paZ req.pa) vs →
        CertWP img dok wok kind pR pX wpin xpin QE Q (ws ++ [(k, .WRd (paZ req.pa) vs)])
          ⟨d, b, r⟩ (k + 1) (kk (.Ok (wordOfBytes n vs, none))) t) →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws ⟨d, bsucc b, r⟩ k
        (.impure (.ok (.memRead n va req)) kk) t
  /-- the walker's A/D write-back, exclusive re-read half (fused: position kept) -/
  | pWxrd (ws : List (Nat × Wev)) (d : Cdata) (b : Bud) (r : Bool) (k : Nat) (n va : Nat)
      (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (kk : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt) :
      devAddr req.pa = false → (classify req.access_kind).akLatest = true →
      wok (paZ req.pa) n → pX wok k →
      (∀ vs : List (BitVec 8), vs.length = n → xpin k (paZ req.pa) vs →
        CertWP img dok wok kind pR pX wpin xpin QE Q (ws ++ [(k, .WRmwR (paZ req.pa) vs)])
          ⟨d, b, r⟩ k (kk (.Ok (wordOfBytes n vs, none))) t) →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws ⟨d, b, r⟩ k
        (.impure (.ok (.memRead n va req)) kk) t
  /-- the walker's A/D write-back, conditional-write half (one row item) -/
  | pWxwr (ws : List (Nat × Wev)) (rvs : List (BitVec 8)) (d : Cdata) (b : Bud) (r : Bool)
      (k : Nat) (n va : Nat)
      (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
      (kk : Result (Option Bool) Arch.abort → SailM X) (t : ExecSt) (v : BitVec (8 * n)) :
      devAddr req.pa = false → (classify req.access_kind).akLatest = true →
      req.value = some v →
      wok (paZ req.pa) n →
      (∃ ws0 k0, ws = ws0 ++ [(k0, .WRmwR (paZ req.pa) rvs)]) →
      CertWP img dok wok kind pR pX wpin xpin QE Q
        (ws ++ [(k, .WRmw (paZ req.pa) rvs (WeakInterpProj.wbytes n v))]) ⟨d, b, r⟩ (k + 1)
        (kk (.Ok (some true))) t →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws ⟨d, bsucc b, r⟩ k
        (.impure (.ok (.memWrite n va req)) kk) t
  /-- (Lean-only, P4; as `AxCert.Cert.cWrEnd`) the row has ended: a plain RAM write there is
  stuck -/
  | pWrEnd (ws : List (Nat × Wev)) (d : Cdata) (r : Bool) (k : Nat) (n va : Nat)
      (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
      (kk : Result (Option Bool) Arch.abort → SailM X) (t : ExecSt) :
      devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws ⟨d, .BFin 0, r⟩ k
        (.impure (.ok (.memWrite n va req)) kk) t

/-! # 3. The kit -/

section certwp
variable (img : Image) (dok wok : Int → Nat → Prop) (kind : Dkind)
variable (pR pX : (Int → Nat → Prop) → Nat → Prop) (wpin xpin : Nat → Int → List (BitVec 8) → Prop)

theorem CertWPMono {X : Type}
    (QE QE' : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop)
    (Q Q' : List (Nat × Wev) → Cst → Nat → X → ExecSt → Prop) (ws : List (Nat × Wev)) (s : Cst)
    (k : Nat) (m : SailM X) (t : ExecSt) :
    (∀ ws' s' k' e t', QE ws' s' k' e t' → QE' ws' s' k' e t') →
    (∀ ws' s' k' x t', Q ws' s' k' x t' → Q' ws' s' k' x t') →
    CertWP img dok wok kind pR pX wpin xpin QE Q ws s k m t →
    CertWP img dok wok kind pR pX wpin xpin QE' Q' ws s k m t := by
  intro HE HQ h
  induction h with
  | pRet ws s k x t h => exact .pRet ws s k x t (HQ ws s k x t h)
  | pExt ws s k e kk t h => exact .pExt ws s k e kk t (HE ws s k e t h)
  | pRd ws s k r kk t _ _ ihs ihn => exact .pRd ws s k r kk t ihs ihn
  | pWr ws s k r v kk t hr _ ih => exact .pWr ws s k r v kk t hr ih
  | pMrd ws d b r k n va req kk t vs h1 h2 h3 h4 _ ih =>
    exact .pMrd ws d b r k n va req kk t vs h1 h2 h3 h4 ih
  | pIf ws s k n va req kk t vs h1 h2 h3 h4 _ ih =>
    exact .pIf ws s k n va req kk t vs h1 h2 h3 h4 ih
  | pEnd ws d r k n va req kk t h1 h2 h3 => exact .pEnd ws d r k n va req kk t h1 h2 h3
  | pWrEnd ws d r k n va req kk t h1 h2 => exact .pWrEnd ws d r k n va req kk t h1 h2
  | pDrd ws b r k n va req kk t h1 h2 h3 h4 h5 h6 _ ih =>
    exact .pDrd ws b r k n va req kk t h1 h2 h3 h4 h5 h6 ih
  | pDwr ws b r k n va req kk t v h1 h2 h3 h4 h5 _ ih =>
    exact .pDwr ws b r k n va req kk t v h1 h2 h3 h4 h5 ih
  | pFence ws d b r k bk kk t h1 _ ih => exact .pFence ws d b r k bk kk t h1 ih
  | pXrd ws b r k n va req kk t h1 h2 h3 h4 h5 _ ih =>
    exact .pXrd ws b r k n va req kk t h1 h2 h3 h4 h5 ih
  | pXwr ws aq rvs b r k n va req kk t v h1 h2 h3 h4 h5 _ ih =>
    exact .pXwr ws aq rvs b r k n va req kk t v h1 h2 h3 h4 h5 ih
  | pIa ws s k n w kk t hs _ ih => exact .pIa ws s k n w kk t hs ih
  | pSf ws d b r k n w kk t hs _ ih => exact .pSf ws d b r k n w kk t hs ih
  | pBa ws s k n a kk t _ ih => exact .pBa ws s k n a kk t ih
  | pCo ws s k c kk t _ ih => exact .pCo ws s k c kk t ih
  | pTl ws s k c kk t _ ih => exact .pTl ws s k c kk t ih
  | pTe ws s k f kk t _ ih => exact .pTe ws s k f kk t ih
  | pRx ws s k a kk t _ ih => exact .pRx ws s k a kk t ih
  | pTs ws s k a kk t _ ih => exact .pTs ws s k a kk t ih
  | pTx ws s k a kk t _ ih => exact .pTx ws s k a kk t ih
  | pCc ws s k kk t _ ih => exact .pCc ws s k kk t ih
  | pMsg ws s k a kk t _ ih => exact .pMsg ws s k a kk t ih
  | pGcc ws s k kk t _ ih => exact .pGcc ws s k kk t ih
  | pWrd ws d b r k n va req kk t h1 h2 h3 h4 h5 _ ih =>
    exact .pWrd ws d b r k n va req kk t h1 h2 h3 h4 h5 ih
  | pWxrd ws d b r k n va req kk t h1 h2 h3 h4 _ ih =>
    exact .pWxrd ws d b r k n va req kk t h1 h2 h3 h4 ih
  | pWxwr ws rvs d b r k n va req kk t v h1 h2 h3 h4 h5 _ ih =>
    exact .pWxwr ws rvs d b r k n va req kk t v h1 h2 h3 h4 h5 ih

theorem CertWPBind {X Y : Type}
    (QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop)
    (Q : List (Nat × Wev) → Cst → Nat → Y → ExecSt → Prop) (m : SailM X) (f : X → SailM Y)
    (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (t : ExecSt) :
    CertWP img dok wok kind pR pX wpin xpin QE
      (fun ws' s' k' x t' => CertWP img dok wok kind pR pX wpin xpin QE Q ws' s' k' (f x) t')
      ws s k m t →
    CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (m >>= f) t := by
  intro h
  induction h with
  | pRet ws s k x t h => exact h
  | pExt ws s k e kk t h => exact .pExt ws s k e _ t h
  | pRd ws s k r kk t _ _ ihs ihn => exact .pRd ws s k r _ t ihs ihn
  | pWr ws s k r v kk t hr _ ih => exact .pWr ws s k r v _ t hr ih
  | pMrd ws d b r k n va req kk t vs h1 h2 h3 h4 _ ih =>
    exact .pMrd ws d b r k n va req _ t vs h1 h2 h3 h4 ih
  | pIf ws s k n va req kk t vs h1 h2 h3 h4 _ ih =>
    exact .pIf ws s k n va req _ t vs h1 h2 h3 h4 ih
  | pEnd ws d r k n va req kk t h1 h2 h3 => exact .pEnd ws d r k n va req _ t h1 h2 h3
  | pWrEnd ws d r k n va req kk t h1 h2 => exact .pWrEnd ws d r k n va req _ t h1 h2
  | pDrd ws b r k n va req kk t h1 h2 h3 h4 h5 h6 _ ih =>
    exact .pDrd ws b r k n va req _ t h1 h2 h3 h4 h5 h6 ih
  | pDwr ws b r k n va req kk t v h1 h2 h3 h4 h5 _ ih =>
    exact .pDwr ws b r k n va req _ t v h1 h2 h3 h4 h5 ih
  | pFence ws d b r k bk kk t h1 _ ih => exact .pFence ws d b r k bk _ t h1 ih
  | pXrd ws b r k n va req kk t h1 h2 h3 h4 h5 _ ih =>
    exact .pXrd ws b r k n va req _ t h1 h2 h3 h4 h5 ih
  | pXwr ws aq rvs b r k n va req kk t v h1 h2 h3 h4 h5 _ ih =>
    exact .pXwr ws aq rvs b r k n va req _ t v h1 h2 h3 h4 h5 ih
  | pIa ws s k n w kk t hs _ ih => exact .pIa ws s k n w _ t hs ih
  | pSf ws d b r k n w kk t hs _ ih => exact .pSf ws d b r k n w _ t hs ih
  | pBa ws s k n a kk t _ ih => exact .pBa ws s k n a _ t ih
  | pCo ws s k c kk t _ ih => exact .pCo ws s k c _ t ih
  | pTl ws s k c kk t _ ih => exact .pTl ws s k c _ t ih
  | pTe ws s k f kk t _ ih => exact .pTe ws s k f _ t ih
  | pRx ws s k a kk t _ ih => exact .pRx ws s k a _ t ih
  | pTs ws s k a kk t _ ih => exact .pTs ws s k a _ t ih
  | pTx ws s k a kk t _ ih => exact .pTx ws s k a _ t ih
  | pCc ws s k kk t _ ih => exact .pCc ws s k _ t ih
  | pMsg ws s k a kk t _ ih => exact .pMsg ws s k a _ t ih
  | pGcc ws s k kk t _ ih => exact .pGcc ws s k _ t ih
  | pWrd ws d b r k n va req kk t h1 h2 h3 h4 h5 _ ih =>
    exact .pWrd ws d b r k n va req _ t h1 h2 h3 h4 h5 ih
  | pWxrd ws d b r k n va req kk t h1 h2 h3 h4 _ ih =>
    exact .pWxrd ws d b r k n va req _ t h1 h2 h3 h4 ih
  | pWxwr ws rvs d b r k n va req kk t v h1 h2 h3 h4 h5 _ ih =>
    exact .pWxwr ws rvs d b r k n va req _ t v h1 h2 h3 h4 h5 ih

theorem CertWPBind0 {Y : Type}
    (QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop)
    (Q : List (Nat × Wev) → Cst → Nat → Y → ExecSt → Prop) (m : SailM Unit) (n : SailM Y)
    (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (t : ExecSt) :
    CertWP img dok wok kind pR pX wpin xpin QE
      (fun ws' s' k' _ t' => CertWP img dok wok kind pR pX wpin xpin QE Q ws' s' k' n t')
      ws s k m t →
    CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (m >>= fun _ => n) t :=
  CertWPBind img dok wok kind pR pX wpin xpin QE Q m (fun _ => n) ws s k t

theorem CertWPFact {X Y : Type}
    (QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop)
    (P : List (Nat × Wev) → Cst → Nat → X → ExecSt → Prop)
    (Q : List (Nat × Wev) → Cst → Nat → Y → ExecSt → Prop) (m : SailM X) (f : X → SailM Y)
    (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (t : ExecSt) :
    CertWP img dok wok kind pR pX wpin xpin QE P ws s k m t →
    (∀ ws' s' k' x t', P ws' s' k' x t' →
      CertWP img dok wok kind pR pX wpin xpin QE Q ws' s' k' (f x) t') →
    CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (m >>= f) t := by
  intro Hm Hf
  exact CertWPBind img dok wok kind pR pX wpin xpin QE Q m f ws s k t
    (CertWPMono img dok wok kind pR pX wpin xpin _ _ _ _ ws s k m t (fun _ _ _ _ _ h => h) Hf Hm)

theorem CertWPRet {X : Type}
    (QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop)
    (Q : List (Nat × Wev) → Cst → Nat → X → ExecSt → Prop) (ws : List (Nat × Wev)) (s : Cst)
    (k : Nat) (x : X) (t : ExecSt) :
    Q ws s k x t → CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (pure x : SailM X) t :=
  fun h => .pRet ws s k x t h

theorem CertWPReadReg
    (QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop) (r : Register)
    (Q : List (Nat × Wev) → Cst → Nat → RegisterType r → ExecSt → Prop) (ws : List (Nat × Wev))
    (s : Cst) (k : Nat) (t : ExecSt) :
    ¬ AxRunClose.pinReg r → Q ws s k (t.regs r) t →
    CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (readReg r : SailM _) t :=
  fun hr hq => .pRd ws s k r _ t (fun h => absurd h hr) (fun _ => .pRet _ _ _ _ t hq)

theorem CertWPWriteReg
    (QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop)
    (Q : List (Nat × Wev) → Cst → Nat → PUnit → ExecSt → Prop) (r : Register)
    (v : RegisterType r) (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (t : ExecSt) :
    ¬ AxRunClose.pinReg r → Q ws s k PUnit.unit (t.setReg r v) →
    CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (writeReg r v : SailM _) t :=
  fun hr hq => .pWr ws s k r v _ t hr (.pRet _ _ _ _ _ hq)

theorem CertWPTryCatch {X : Type}
    (QE1 QE2 : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop)
    (Q : List (Nat × Wev) → Cst → Nat → X → ExecSt → Prop) (m : SailM X)
    (h : Sail.Error exception → SailM X) (ws : List (Nat × Wev)) (s : Cst) (k : Nat)
    (t : ExecSt) :
    (∀ ws' s' k' e t', QE1 ws' s' k' e t' →
      CertWP img dok wok kind pR pX wpin xpin QE2 Q ws' s' k' (h e) t') →
    CertWP img dok wok kind pR pX wpin xpin QE1 Q ws s k m t →
    CertWP img dok wok kind pR pX wpin xpin QE2 Q ws s k (PreSail.tryCatchAll m h) t := by
  intro Hh H
  induction H with
  | pRet ws s k x t h => exact .pRet ws s k x t h
  | pExt ws s k e kk t he => exact Hh ws s k e t he
  | pRd ws s k r kk t _ _ ihs ihn => exact .pRd ws s k r _ t ihs ihn
  | pWr ws s k r v kk t hr _ ih => exact .pWr ws s k r v _ t hr ih
  | pMrd ws d b r k n va req kk t vs h1 h2 h3 h4 _ ih =>
    exact .pMrd ws d b r k n va req _ t vs h1 h2 h3 h4 ih
  | pIf ws s k n va req kk t vs h1 h2 h3 h4 _ ih =>
    exact .pIf ws s k n va req _ t vs h1 h2 h3 h4 ih
  | pEnd ws d r k n va req kk t h1 h2 h3 => exact .pEnd ws d r k n va req _ t h1 h2 h3
  | pWrEnd ws d r k n va req kk t h1 h2 => exact .pWrEnd ws d r k n va req _ t h1 h2
  | pDrd ws b r k n va req kk t h1 h2 h3 h4 h5 h6 _ ih =>
    exact .pDrd ws b r k n va req _ t h1 h2 h3 h4 h5 h6 ih
  | pDwr ws b r k n va req kk t v h1 h2 h3 h4 h5 _ ih =>
    exact .pDwr ws b r k n va req _ t v h1 h2 h3 h4 h5 ih
  | pFence ws d b r k bk kk t h1 _ ih => exact .pFence ws d b r k bk _ t h1 ih
  | pXrd ws b r k n va req kk t h1 h2 h3 h4 h5 _ ih =>
    exact .pXrd ws b r k n va req _ t h1 h2 h3 h4 h5 ih
  | pXwr ws aq rvs b r k n va req kk t v h1 h2 h3 h4 h5 _ ih =>
    exact .pXwr ws aq rvs b r k n va req _ t v h1 h2 h3 h4 h5 ih
  | pIa ws s k n w kk t hs _ ih => exact .pIa ws s k n w _ t hs ih
  | pSf ws d b r k n w kk t hs _ ih => exact .pSf ws d b r k n w _ t hs ih
  | pBa ws s k n a kk t _ ih => exact .pBa ws s k n a _ t ih
  | pCo ws s k c kk t _ ih => exact .pCo ws s k c _ t ih
  | pTl ws s k c kk t _ ih => exact .pTl ws s k c _ t ih
  | pTe ws s k f kk t _ ih => exact .pTe ws s k f _ t ih
  | pRx ws s k a kk t _ ih => exact .pRx ws s k a _ t ih
  | pTs ws s k a kk t _ ih => exact .pTs ws s k a _ t ih
  | pTx ws s k a kk t _ ih => exact .pTx ws s k a _ t ih
  | pCc ws s k kk t _ ih => exact .pCc ws s k _ t ih
  | pMsg ws s k a kk t _ ih => exact .pMsg ws s k a _ t ih
  | pGcc ws s k kk t _ ih => exact .pGcc ws s k _ t ih
  | pWrd ws d b r k n va req kk t h1 h2 h3 h4 h5 _ ih =>
    exact .pWrd ws d b r k n va req _ t h1 h2 h3 h4 h5 ih
  | pWxrd ws d b r k n va req kk t h1 h2 h3 h4 _ ih =>
    exact .pWxrd ws d b r k n va req _ t h1 h2 h3 h4 ih
  | pWxwr ws rvs d b r k n va req kk t v h1 h2 h3 h4 h5 _ ih =>
    exact .pWxwr ws rvs d b r k n va req _ t v h1 h2 h3 h4 h5 ih

theorem CertWPLiftRAny {R X : Type}
    (QE QE' : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop)
    (Q : List (Nat × Wev) → Cst → Nat → X → ExecSt → Prop) (m : SailM X)
    (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (t : ExecSt) :
    (∀ ws' s' k' e t', QE ws' s' k' e t' → QE' ws' s' k' e t') →
    CertWP img dok wok kind pR pX wpin xpin QE Q ws s k m t →
    CertWP img dok wok kind pR pX wpin xpin QE'
      (fun ws' s' k' (r : Except (Sail.Error exception ⊕ R) X) t' =>
        match r with
        | .ok x => Q ws' s' k' x t'
        | .error _ => False)
      ws s k (ExceptT.run (liftM m : SailME R X)) t := by
  intro HE H
  have e : ExceptT.run (liftM m : SailME R X) = m >>= fun a => pure (Except.ok a) := rfl
  rw [e]
  apply CertWPBind
  exact CertWPMono img dok wok kind pR pX wpin xpin QE QE' Q _ ws s k m t HE
    (fun ws' s' k' x t' h => .pRet _ _ _ _ t' h) H

theorem CertWPLiftR {R X : Type}
    (QE' : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop)
    (Q : List (Nat × Wev) → Cst → Nat → X → ExecSt → Prop) (m : SailM X)
    (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (t : ExecSt) :
    CertWP img dok wok kind pR pX wpin xpin (fun _ _ _ _ _ => False) Q ws s k m t →
    CertWP img dok wok kind pR pX wpin xpin QE'
      (fun ws' s' k' (r : Except (Sail.Error exception ⊕ R) X) t' =>
        match r with
        | .ok x => Q ws' s' k' x t'
        | .error _ => False)
      ws s k (ExceptT.run (liftM m : SailME R X)) t :=
  CertWPLiftRAny img dok wok kind pR pX wpin xpin _ QE' Q m ws s k t
    (fun _ _ _ _ _ h => h.elim)

theorem CertWPCatchEarlyReturn {X : Type}
    (QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop)
    (Q : List (Nat × Wev) → Cst → Nat → X → ExecSt → Prop) (m : SailME X X)
    (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (t : ExecSt) :
    CertWP img dok wok kind pR pX wpin xpin QE
      (fun ws' s' k' (r : Except (Sail.Error exception ⊕ X) X) t' =>
        match r with
        | .ok x => Q ws' s' k' x t'
        | .error (.inr x) => Q ws' s' k' x t'
        | .error (.inl e) => QE ws' s' k' e t')
      ws s k (ExceptT.run m) t →
    CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (SailME.run m) t := by
  intro H
  show CertWP img dok wok kind pR pX wpin xpin QE Q ws s k (ExceptT.run m >>= _) t
  apply CertWPBind
  refine CertWPMono img dok wok kind pR pX wpin xpin QE QE _ _ ws s k _ t
    (fun _ _ _ _ _ h => h) ?_ H
  intro ws' s' k' r t' hr
  rcases r with (e | x) | x
  · exact .pExt ws' s' k' e _ t' hr
  · exact .pRet ws' s' k' x t' hr
  · exact .pRet ws' s' k' x t' hr

/-- THE POSITION-EXACT TRANSFER: a register-only (`rfF`) tree's `execA` run at ANY state with
the thread's registers is a certificate at the SAME position, walker list and certificate state
(no row item: `rfF` excludes every memory / barrier node). -/
theorem CertWPExecARfF {X : Type}
    (QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop) (m : SailM X) :
    rfF m → ∀ (s0 : ExecSt) (x : X) (s1 : ExecSt), execA m s0 = some (x, s1) →
    ∀ (t : ExecSt), t.regs = s0.regs → ∀ (ws : List (Nat × Wev)) (s : Cst) (k : Nat),
    CertWP img dok wok kind pR pX wpin xpin QE
      (fun ws' s' k' x' t' => ws' = ws ∧ s' = s ∧ k' = k ∧ x' = x ∧
        t'.regs = s1.regs ∧ t'.mem = t.mem ∧ t'.dev = t.dev) ws s k m t := by
  induction m with
  | pure y =>
    intro _ s0 x s1 h t ht ws s k
    simp only [execA, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .pRet ws s k y t ⟨rfl, rfl, rfl, rfl, ht, rfl, rfl⟩
  | impure call kk ih =>
    intro hrf s0 x s1 h t ht ws s k
    cases call with
    | error e => cases h
    | ok o =>
      cases o
      case regRead r =>
        simp only [execA] at h
        split at h
        · cases h
        · rename_i hr
          refine .pRd ws s k r kk t (fun hp => absurd hp hr) (fun _ => ?_)
          rw [ht]
          exact ih _ (hrf.2 _) s0 x s1 h t ht ws s k
      case regWrite r v =>
        simp only [execA] at h
        split at h
        · cases h
        · rename_i hr
          refine .pWr ws s k r v kk t hr ?_
          have HI := ih PUnit.unit hrf.2 (s0.setReg r v) x s1 h (t.setReg r v)
            (by simp [ExecSt.setReg, ht]) ws s k
          exact CertWPMono img dok wok kind pR pX wpin xpin _ _ _ _ _ _ _ _ _
            (fun _ _ _ _ _ h => h)
            (fun _ _ _ _ _ ⟨h1, h2, h3, h4, h5, h6, h7⟩ => ⟨h1, h2, h3, h4, h5, h6, h7⟩) HI
      case memRead => exact hrf.elim
      case memWrite => exact hrf.elim
      case barrier => exact hrf.elim
      case instrAnnounce n w =>
        simp only [execA] at h
        split at h
        · cases h
        · exact .pIa ws s k n w kk t hrf.1 (ih _ hrf.2 s0 x s1 h t ht ws s k)
      case choose => cases h
      case readRam => cases h
      case writeRam => cases h
      case branchAnnounce => exact .pBa ws s k _ _ kk t (ih _ hrf s0 x s1 h t ht ws s k)
      case cacheOp => exact .pCo ws s k _ kk t (ih _ hrf s0 x s1 h t ht ws s k)
      case tlbi => exact .pTl ws s k _ kk t (ih _ hrf s0 x s1 h t ht ws s k)
      case takeException => exact .pTe ws s k _ kk t (ih _ hrf s0 x s1 h t ht ws s k)
      case returnException => exact .pRx ws s k _ kk t (ih _ hrf s0 x s1 h t ht ws s k)
      case translationStart => exact .pTs ws s k _ kk t (ih _ hrf s0 x s1 h t ht ws s k)
      case translationEnd => exact .pTx ws s k _ kk t (ih _ hrf s0 x s1 h t ht ws s k)
      case cycleCount => exact .pCc ws s k kk t (ih _ hrf s0 x s1 h t ht ws s k)
      case message => exact .pMsg ws s k _ kk t (ih _ hrf s0 x s1 h t ht ws s k)
      case getCycleCount => exact .pGcc ws s k kk t (ih _ hrf s0 x s1 h t ht ws s k)

/-- Keeping any post the run's end state satisfies (the thread state after = the thread's
memory with the run's registers). -/
theorem CertWPExecARfFPost {X : Type}
    (QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop)
    (Q : List (Nat × Wev) → Cst → Nat → X → ExecSt → Prop) (m : SailM X) (s0 : ExecSt) (x : X)
    (s1 : ExecSt) (t : ExecSt) (ws : List (Nat × Wev)) (s : Cst) (k : Nat) :
    rfF m → execA m s0 = some (x, s1) → t.regs = s0.regs →
    Q ws s k x ⟨s1.regs, t.mem, t.dev⟩ →
    CertWP img dok wok kind pR pX wpin xpin QE Q ws s k m t := by
  intro Hrf He Ht HQ
  refine CertWPMono img dok wok kind pR pX wpin xpin QE QE _ Q ws s k m t (fun _ _ _ _ _ h => h)
    ?_ (CertWPExecARfF img dok wok kind pR pX wpin xpin QE m Hrf s0 x s1 He t Ht ws s k)
  rintro _ _ _ _ ⟨r', m', d'⟩ ⟨rfl, rfl, rfl, rfl, hr, hm, hd⟩
  simp only [] at hr hm hd
  subst hr hm hd
  exact HQ

end certwp

/-! # 2. The positional premises the bridge discharges (pure, row level) -/

/-- The row item of hart `i` at `k` is no FUSED RMW at a `D` address (refutes the degenerate
matching of a plain read against an `IRmw`). -/
def posR (G : Gdexec → Prop) (i : Nat) (D : Int → Nat → Prop) (k : Nat) : Prop :=
  ∀ GD, G GD → ∀ (lb : Lbl) (aq rl : Bool) (base : Int) (m : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base m → ¬ D base m

/-- The row item of hart `i` at `k` is no PLAIN read at a `D` address (refutes the split
matching of an exclusive read against an `IRead`). -/
def posX (G : Gdexec → Prop) (i : Nat) (D : Int → Nat → Prop) (k : Nat) : Prop :=
  ∀ GD, G GD → ∀ (lb : Lbl) (aq : Bool) (base : Int) (m : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base m → ¬ D base m

theorem posRAnti (G : Gdexec → Prop) (i : Nat) (D D' : Int → Nat → Prop) (k : Nat) :
    (∀ a n, D' a n → D a n) → posR G i D k → posR G i D' k :=
  fun HD H GD HG lb aq rl base m Hl Hid HD' => H GD HG lb aq rl base m Hl Hid (HD _ _ HD')

theorem posXAnti (G : Gdexec → Prop) (i : Nat) (D D' : Int → Nat → Prop) (k : Nat) :
    (∀ a n, D' a n → D a n) → posX G i D k → posX G i D' k :=
  fun HD H GD HG lb aq base m Hl Hid HD' => H GD HG lb aq base m Hl Hid (HD _ _ HD')

/-- The gp_for-style TAGGING of the row: the walker events' row positions as a map
`k ↦ the walker event at k` (deviation 4). -/
def wtagOf (ws : List (Nat × Wev)) (k : Nat) : Option Wev :=
  (ws.find? (fun kw => decide (kw.1 = k))).map Prod.snd

/-! # 4. The region-form embedding: `CertW` is `CertWP` with every positional premise holding
everywhere and no pins -/

theorem CertWPOfCertW (img : Image) (dok wok : Int → Nat → Prop) (kind : Dkind)
    (pR pX : (Int → Nat → Prop) → Nat → Prop) (wpin xpin : Nat → Int → List (BitVec 8) → Prop)
    (HR : ∀ k, pR dok k ∧ pR wok k) (HX : ∀ k, pX dok k ∧ pX wok k) {X : Type}
    (QE : List Wev → Cst → Sail.Error exception → ExecSt → Prop)
    (Q : List Wev → Cst → X → ExecSt → Prop) (ws : List Wev) (s : Cst) (m : SailM X)
    (t : ExecSt) :
    CertW img dok wok kind QE Q ws s m t →
    ∀ (wsp : List (Nat × Wev)) (k : Nat), wsp.map Prod.snd = ws →
    CertWP img dok wok kind pR pX wpin xpin (fun wsp' s' _ e t' => QE (wsp'.map Prod.snd) s' e t')
      (fun wsp' s' _ x t' => Q (wsp'.map Prod.snd) s' x t') wsp s k m t := by
  intro h
  induction h with
  | wRet ws s x t h => intro wsp k hm; subst hm; exact .pRet _ _ _ _ _ h
  | wExt ws s e kk t h => intro wsp k hm; subst hm; exact .pExt _ _ _ _ _ _ h
  | wRd ws s r kk t _ _ ihs ihn =>
    intro wsp k hm
    exact .pRd _ _ _ _ _ _ (fun hp v => ihs hp v wsp k hm) (fun hp => ihn hp wsp k hm)
  | wWr ws s r v kk t hr _ ih => intro wsp k hm; exact .pWr _ _ _ _ _ _ _ hr (ih wsp k hm)
  | wMrd ws d b r n va req kk t vs h1 h2 h3 h4 _ ih =>
    intro wsp k hm; exact .pMrd _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 (ih wsp (k + 1) hm)
  | wIf ws s n va req kk t vs h1 h2 h3 h4 _ ih =>
    intro wsp k hm; exact .pIf _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 (ih wsp k hm)
  | wEnd ws d r n va req kk t h1 h2 h3 =>
    intro wsp k _; exact .pEnd _ _ _ _ _ _ _ _ _ h1 h2 h3
  | wWrEnd ws d r n va req kk t h1 h2 =>
    intro wsp k _; exact .pWrEnd _ _ _ _ _ _ _ _ _ h1 h2
  | wDrd ws b r n va req kk t h1 h2 h3 h4 h5 _ ih =>
    intro wsp k hm
    exact .pDrd _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 (HR k).1
      (fun vs hl => ih vs hl wsp (k + 1) hm)
  | wDwr ws b r n va req kk t v h1 h2 h3 h4 h5 _ ih =>
    intro wsp k hm; exact .pDwr _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 (ih wsp (k + 1) hm)
  | wFence ws d b r bk kk t h1 _ ih =>
    intro wsp k hm; exact .pFence _ _ _ _ _ _ _ _ h1 (ih wsp (k + 1) hm)
  | wXrd ws b r n va req kk t h1 h2 h3 h4 _ ih =>
    intro wsp k hm
    exact .pXrd _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 (HX k).1 (fun vs hl => ih vs hl wsp k hm)
  | wXwr ws aq rvs b r n va req kk t v h1 h2 h3 h4 h5 _ ih =>
    intro wsp k hm; exact .pXwr _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 (ih wsp (k + 1) hm)
  | wIa ws s n w kk t hs _ ih => intro wsp k hm; exact .pIa _ _ _ _ _ _ _ hs (ih wsp k hm)
  | wSf ws d b r n w kk t hs _ ih =>
    intro wsp k hm; exact .pSf _ _ _ _ _ _ _ _ _ hs (ih wsp (k + 1) hm)
  | wBa ws s n a kk t _ ih => intro wsp k hm; exact .pBa _ _ _ _ _ _ _ (ih wsp k hm)
  | wCo ws s c kk t _ ih => intro wsp k hm; exact .pCo _ _ _ _ _ _ (ih wsp k hm)
  | wTl ws s c kk t _ ih => intro wsp k hm; exact .pTl _ _ _ _ _ _ (ih wsp k hm)
  | wTe ws s f kk t _ ih => intro wsp k hm; exact .pTe _ _ _ _ _ _ (ih wsp k hm)
  | wRx ws s a kk t _ ih => intro wsp k hm; exact .pRx _ _ _ _ _ _ (ih wsp k hm)
  | wTs ws s a kk t _ ih => intro wsp k hm; exact .pTs _ _ _ _ _ _ (ih wsp k hm)
  | wTx ws s a kk t _ ih => intro wsp k hm; exact .pTx _ _ _ _ _ _ (ih wsp k hm)
  | wCc ws s kk t _ ih => intro wsp k hm; exact .pCc _ _ _ _ _ (ih wsp k hm)
  | wMsg ws s a kk t _ ih => intro wsp k hm; exact .pMsg _ _ _ _ _ _ (ih wsp k hm)
  | wGcc ws s kk t _ ih => intro wsp k hm; exact .pGcc _ _ _ _ _ (ih wsp k hm)
  | wWrd ws d b r n va req kk t h1 h2 h3 h4 _ ih =>
    intro wsp k hm
    exact .pWrd _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 (HR k).2
      (fun vs hl _ => ih vs hl _ (k + 1) (by rw [List.map_append, hm]; rfl))
  | wWxrd ws d b r n va req kk t h1 h2 h3 _ ih =>
    intro wsp k hm
    exact .pWxrd _ _ _ _ _ _ _ _ _ _ h1 h2 h3 (HX k).2
      (fun vs hl _ => ih vs hl _ k (by rw [List.map_append, hm]; rfl))
  | wWxwr ws rvs d b r n va req kk t v h1 h2 h3 h4 h5 _ ih =>
    intro wsp k hm
    refine .pWxwr _ _ _ _ _ _ _ _ _ _ _ v h1 h2 h3 h4 ?_
      (ih _ (k + 1) (by rw [List.map_append, hm]; rfl))
    obtain ⟨ws0, hws0⟩ := h5
    rcases List.eq_nil_or_concat wsp with hnil | ⟨L, ⟨k0, w0⟩, hL⟩
    · subst hnil
      rw [← hm] at hws0
      cases ws0 <;> cases hws0
    · rw [List.concat_eq_append] at hL
      subst hL
      rw [← hm, List.map_append] at hws0
      have hlast := (List.append_inj' hws0 rfl).2
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hlast
      subst hlast
      exact ⟨L, k0, rfl⟩

end Weak
