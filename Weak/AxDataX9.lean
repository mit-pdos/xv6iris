/-
Weak: **THE MULTI-EVENT DATA CHANNEL** (constraint A's engine prerequisite): `CertW`, the
certificate `AxCert.Cert` extended by an ordered list of TAGGED WALKER EVENTS `ws : List Wev`
beside the instruction's one data event (`csD`).

Rocq: `iris/AxDataX9.v` @ xxvzwolszwmp.

## The Rocq header, in substance

The walker events: `WRd a vs` — a page-table-walker READ (demonic, one row item); `WRmwR a vs` —
the walker's A/D write-back, exclusive re-read half (demonic, NO row item: the fused `LRmw`);
`WRmw a rvs wvs` — its conditional-write half (one row item), required to follow its `WRmwR` at
the same slot.  The walk addresses depend on earlier read words because the continuation is
parametric in each `vs` (the next node's address is computed from it) — the DATA DEPENDENCY the
PT protocol needs (AxPtProt §INTERFACE (a)).  Walker events are distinguishable from explicit
loads by their TAG (the constructor used, recorded in `ws`), not by the access kind.  IMAGE reads
(`wMrd`) remain: the A/D-preset / immutable-PT case is the special case `ws` constant
(`CertWOfCert`, §2).  NOT HERE: the WPd bridge for `CertW` (`wWrd` is meant to be
`AxCert2`'s data-read node at `dok := wok` with a PERSISTENT walker flow, the RMW pair the
`xrd`/`xwr` nodes at `wok`); the Sv39 walk REPLAYED with demonic walker reads.
§1 `CertW` and its kit `CertWMono`, `CertWBind`.  §2 `CertWOfCert`.

## Deviations from Rocq

1. AS `AxCert` (deviations 1–5, 7): `CertW` is on `SailM X`; Rocq's extra-outcome type `E` ↦ the
   failure node `.impure (.error e)` with `e : Sail.Error exception` (`wExt`, continuation
   `Empty → SailM X`); `seip_reg` ↦ `AxRunClose.pinReg`; register events carry no access kind;
   `wMrd` is the GRAPH image read (`akIfetch = false`, Rocq `ak_coh = false` renamed), and the
   Lean-only constructor `wIf` is an image FETCH (`akIfetch = true`, the pinned admin step, budget
   and `ws` kept — needed so `CertWOfCert` covers `AxCert.Cert.cIf`); `wEnd` and `wDrd` take
   `akIfetch = false`; `wIa` takes `sfAnnB n w = false`; writes (`wDwr`, `wXwr`, `wWxwr`) take
   `v` with `req.value = some v`, record `WeakInterpProj.wbytes n v` and continue at
   `.Ok (some true)` (Rocq `inl None`); read answers are `.Ok (wordOfBytes n vs, none)`.
2. O2 STAGE C: the walker READ `wWrd` takes `(classify req.access_kind).akIfetch = false` (Rocq:
   no `ak_coh` premise) — a fetch is not a row item in Lean, so it cannot be a walker event (the
   Lean model's walker reads are `Read_ttw`, not fetches).  `wWxrd` / `wWxwr` need nothing extra
   (`akLatest = true` excludes a fetch).
3. TYPES: `Z` ↦ `Int`, `list (bv 8)` ↦ `List (BitVec 8)`, `N.to_nat n` ↦ `n : Nat`,
   `pa_z` ↦ `paZ`, `img_bytes` ↦ `imgBytes`, `Defs.bind` ↦ `>>=`.
4. Q19 (provisional, as `AxCert` deviation 10): the Lean-only constructor `wSf` (an SFENCE.VMA
   announce, `sfAnnB n w = true`: the marker fence, one row item, `ws` kept), so that
   `CertWOfCert` covers `AxCert.Cert.cSf`.

**Rocq → Lean name map.**  `wev` `Wev` (constructors `WRd`, `WRmwR`, `WRmw` kept), `CertW`
`CertW` (constructors `w_ret` `wRet`, `w_rd` `wRd`, `w_wr` `wWr`, `w_mrd` `wMrd`, `w_end` `wEnd`,
`w_drd` `wDrd`, `w_dwr` `wDwr`, `w_fence` `wFence`, `w_xrd` `wXrd`, `w_xwr` `wXwr`, `w_ia` `wIa`,
`w_ba` `wBa`, `w_co` `wCo`, `w_tl` `wTl`, `w_te` `wTe`, `w_rx` `wRx`, `w_ts` `wTs`, `w_tx` `wTx`,
`w_cc` `wCc`, `w_msg` `wMsg`, `w_gcc` `wGcc`, `w_ext` `wExt`, `w_wrd` `wWrd`, `w_wxrd` `wWxrd`,
`w_wxwr` `wWxwr`; Lean-only `wIf`, `wSf`), `CertW_mono` `CertWMono`, `CertW_bind` `CertWBind`,
`CertW_of_Cert` `CertWOfCert`.  None is in the duplicated-name table.

**Dropped:** nothing (Rocq 2 inductives + 3 lemmas; Lean 2 + 3, + the Lean-only constructors
`wIf`, `wSf`).  **Not ported:** the section-local Ltac `certw_ctor` (Lean proofs name the constructor per
case) and `Print Assumptions`.
-/
import Weak.AxCert

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D

/-! # 1. The multi-event certificate -/

/-- A tagged walker event. -/
inductive Wev where
  | WRd (a : Int) (vs : List (BitVec 8))
  | WRmwR (a : Int) (vs : List (BitVec 8))
  | WRmw (a : Int) (rvs wvs : List (BitVec 8))

/-- THE MULTI-EVENT CERTIFICATE (see the header). -/
inductive CertW (img : Image) (dok wok : Int → Nat → Prop) (kind : Dkind) {X : Type}
    (QE : List Wev → Cst → Sail.Error exception → ExecSt → Prop)
    (Q : List Wev → Cst → X → ExecSt → Prop) :
    List Wev → Cst → SailM X → ExecSt → Prop where
  | wRet (ws : List Wev) (s : Cst) (x : X) (t : ExecSt) :
      Q ws s x t → CertW img dok wok kind QE Q ws s (.pure x) t
  | wRd (ws : List Wev) (s : Cst) (r : Register) (k : RegisterType r → SailM X) (t : ExecSt) :
      (AxRunClose.pinReg r → ∀ v, CertW img dok wok kind QE Q ws s (k v) t) →
      (¬ AxRunClose.pinReg r → CertW img dok wok kind QE Q ws s (k (t.regs r)) t) →
      CertW img dok wok kind QE Q ws s (.impure (.ok (.regRead r)) k) t
  | wWr (ws : List Wev) (s : Cst) (r : Register) (v : RegisterType r) (k : PUnit → SailM X)
      (t : ExecSt) :
      ¬ AxRunClose.pinReg r → CertW img dok wok kind QE Q ws s (k PUnit.unit) (t.setReg r v) →
      CertW img dok wok kind QE Q ws s (.impure (.ok (.regWrite r v)) k) t
  /-- an IMAGE graph read (text / page tables, D3): one row item -/
  | wMrd (ws : List Wev) (d : Cdata) (b : Bud) (r : Bool) (n va : Nat)
      (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt)
      (vs : List (BitVec 8)) :
      devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      (classify req.access_kind).akIfetch = false →
      imgBytes img (paZ req.pa) n = some vs →
      CertW img dok wok kind QE Q ws ⟨d, b, r⟩ (k (.Ok (wordOfBytes n vs, none))) t →
      CertW img dok wok kind QE Q ws ⟨d, bsucc b, r⟩ (.impure (.ok (.memRead n va req)) k) t
  /-- (Lean-only, deviation 1) an image FETCH: the pinned admin step, no row item -/
  | wIf (ws : List Wev) (s : Cst) (n va : Nat)
      (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt)
      (vs : List (BitVec 8)) :
      devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      (classify req.access_kind).akIfetch = true →
      imgBytes img (paZ req.pa) n = some vs →
      CertW img dok wok kind QE Q ws s (k (.Ok (wordOfBytes n vs, none))) t →
      CertW img dok wok kind QE Q ws s (.impure (.ok (.memRead n va req)) k) t
  /-- the row has ended: a plain RAM graph read there is stuck -/
  | wEnd (ws : List Wev) (d : Cdata) (r : Bool) (n va : Nat)
      (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt) :
      devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      (classify req.access_kind).akIfetch = false →
      CertW img dok wok kind QE Q ws ⟨d, .BFin 0, r⟩ (.impure (.ok (.memRead n va req)) k) t
  /-- the DATA read — demonic -/
  | wDrd (ws : List Wev) (b : Bud) (r : Bool) (n va : Nat)
      (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt) :
      kind = .DKLd → devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      (classify req.access_kind).akIfetch = false →
      dok (paZ req.pa) n →
      (∀ vs : List (BitVec 8), vs.length = n →
        CertW img dok wok kind QE Q ws ⟨.CLd vs, b, r⟩ (k (.Ok (wordOfBytes n vs, none))) t) →
      CertW img dok wok kind QE Q ws ⟨.CPend, bsucc b, r⟩ (.impure (.ok (.memRead n va req)) k) t
  /-- the DATA write — the row checks the bytes; class recorded, flag cleared -/
  | wDwr (ws : List Wev) (b : Bud) (r : Bool) (n va : Nat)
      (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (Option Bool) Arch.abort → SailM X) (t : ExecSt) (v : BitVec (8 * n)) :
      kind = .DKSt → devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      req.value = some v →
      dok (paZ req.pa) n →
      CertW img dok wok kind QE Q ws
        ⟨.CSt (WeakInterpProj.wbytes n v) (wcls req.access_kind r), b, false⟩
        (k (.Ok (some true))) t →
      CertW img dok wok kind QE Q ws ⟨.CPend, bsucc b, r⟩ (.impure (.ok (.memWrite n va req)) k) t
  /-- THE BARRIER ARM: a fence event, one row item; the flag moves as `relpUpd` of the
  barrier's label -/
  | wFence (ws : List Wev) (d : Cdata) (b : Bud) (r : Bool) (bk : barrier_kind)
      (k : Unit → SailM X) (t : ExecSt) :
      ebarPark bk = none →
      CertW img dok wok kind QE Q ws ⟨d, b, relpUpd (ebarLabel bk) r⟩ (k ()) t →
      CertW img dok wok kind QE Q ws ⟨d, bsucc b, r⟩ (.impure (.ok (.barrier bk)) k) t
  /-- THE RMW ARM, read half: exclusive read, demonic, no row item consumed -/
  | wXrd (ws : List Wev) (b : Bud) (r : Bool) (n va : Nat)
      (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt) :
      kind = .DKRmw → devAddr req.pa = false → (classify req.access_kind).akLatest = true →
      dok (paZ req.pa) n →
      (∀ vs : List (BitVec 8), vs.length = n →
        CertW img dok wok kind QE Q ws ⟨.CRmwR (classify req.access_kind).akSync vs, b, r⟩
          (k (.Ok (wordOfBytes n vs, none))) t) →
      CertW img dok wok kind QE Q ws ⟨.CPend, b, r⟩ (.impure (.ok (.memRead n va req)) k) t
  /-- THE RMW ARM, write half: exclusive write (success branch), one row item -/
  | wXwr (ws : List Wev) (aq : Bool) (rvs : List (BitVec 8)) (b : Bud) (r : Bool) (n va : Nat)
      (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (Option Bool) Arch.abort → SailM X) (t : ExecSt) (v : BitVec (8 * n)) :
      kind = .DKRmw → devAddr req.pa = false → (classify req.access_kind).akLatest = true →
      req.value = some v →
      dok (paZ req.pa) n →
      CertW img dok wok kind QE Q ws
        ⟨.CRmw aq (classify req.access_kind).akSync rvs (WeakInterpProj.wbytes n v)
          (wcls req.access_kind r), b, false⟩
        (k (.Ok (some true))) t →
      CertW img dok wok kind QE Q ws ⟨.CRmwR aq rvs, bsucc b, r⟩
        (.impure (.ok (.memWrite n va req)) k) t
  | wIa (ws : List Wev) (s : Cst) (n : Nat) (w : BitVec n) (k : Unit → SailM X) (t : ExecSt) :
      sfAnnB n w = false → CertW img dok wok kind QE Q ws s (k ()) t →
      CertW img dok wok kind QE Q ws s (.impure (.ok (.instrAnnounce n w)) k) t
  /-- (Lean-only, Q19) the SFENCE.VMA announce: the marker fence, one row item -/
  | wSf (ws : List Wev) (d : Cdata) (b : Bud) (r : Bool) (n : Nat) (w : BitVec n)
      (k : Unit → SailM X) (t : ExecSt) :
      sfAnnB n w = true → CertW img dok wok kind QE Q ws ⟨d, b, r⟩ (k ()) t →
      CertW img dok wok kind QE Q ws ⟨d, bsucc b, r⟩ (.impure (.ok (.instrAnnounce n w)) k) t
  | wBa (ws : List Wev) (s : Cst) (n : Nat) (a : BitVec n) (k : Unit → SailM X) (t : ExecSt) :
      CertW img dok wok kind QE Q ws s (k ()) t →
      CertW img dok wok kind QE Q ws s (.impure (.ok (.branchAnnounce n a)) k) t
  | wCo (ws : List Wev) (s : Cst) (c : Arch.cache_op) (k : Unit → SailM X) (t : ExecSt) :
      CertW img dok wok kind QE Q ws s (k ()) t →
      CertW img dok wok kind QE Q ws s (.impure (.ok (.cacheOp c)) k) t
  | wTl (ws : List Wev) (s : Cst) (c : Arch.tlb_op) (k : Unit → SailM X) (t : ExecSt) :
      CertW img dok wok kind QE Q ws s (k ()) t →
      CertW img dok wok kind QE Q ws s (.impure (.ok (.tlbi c)) k) t
  | wTe (ws : List Wev) (s : Cst) (f : Arch.fault) (k : Unit → SailM X) (t : ExecSt) :
      CertW img dok wok kind QE Q ws s (k ()) t →
      CertW img dok wok kind QE Q ws s (.impure (.ok (.takeException f)) k) t
  | wRx (ws : List Wev) (s : Cst) (a : Arch.pa) (k : Unit → SailM X) (t : ExecSt) :
      CertW img dok wok kind QE Q ws s (k ()) t →
      CertW img dok wok kind QE Q ws s (.impure (.ok (.returnException a)) k) t
  | wTs (ws : List Wev) (s : Cst) (a : Arch.trans_start) (k : Unit → SailM X) (t : ExecSt) :
      CertW img dok wok kind QE Q ws s (k ()) t →
      CertW img dok wok kind QE Q ws s (.impure (.ok (.translationStart a)) k) t
  | wTx (ws : List Wev) (s : Cst) (a : Arch.trans_end) (k : Unit → SailM X) (t : ExecSt) :
      CertW img dok wok kind QE Q ws s (k ()) t →
      CertW img dok wok kind QE Q ws s (.impure (.ok (.translationEnd a)) k) t
  | wCc (ws : List Wev) (s : Cst) (k : Unit → SailM X) (t : ExecSt) :
      CertW img dok wok kind QE Q ws s (k ()) t →
      CertW img dok wok kind QE Q ws s (.impure (.ok .cycleCount) k) t
  | wMsg (ws : List Wev) (s : Cst) (a : String) (k : Unit → SailM X) (t : ExecSt) :
      CertW img dok wok kind QE Q ws s (k ()) t →
      CertW img dok wok kind QE Q ws s (.impure (.ok (.message a)) k) t
  | wGcc (ws : List Wev) (s : Cst) (k : Nat → SailM X) (t : ExecSt) :
      CertW img dok wok kind QE Q ws s (k (0 : Nat)) t →
      CertW img dok wok kind QE Q ws s (.impure (.ok .getCycleCount) k) t
  | wExt (ws : List Wev) (s : Cst) (e : Sail.Error exception) (k : Empty → SailM X)
      (t : ExecSt) :
      QE ws s e t → CertW img dok wok kind QE Q ws s (.impure (.error e) k) t
  /-- THE WALKER ARM (constraint A): a page-table-walker read — a plain RAM graph read at a
  `wok` address, DEMONIC, one row item, recorded as the tagged walker event `WRd a vs`
  (deviation 2: never a fetch) -/
  | wWrd (ws : List Wev) (d : Cdata) (b : Bud) (r : Bool) (n va : Nat)
      (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt) :
      devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      (classify req.access_kind).akIfetch = false →
      wok (paZ req.pa) n →
      (∀ vs : List (BitVec 8), vs.length = n →
        CertW img dok wok kind QE Q (ws ++ [.WRd (paZ req.pa) vs]) ⟨d, b, r⟩
          (k (.Ok (wordOfBytes n vs, none))) t) →
      CertW img dok wok kind QE Q ws ⟨d, bsucc b, r⟩ (.impure (.ok (.memRead n va req)) k) t
  /-- the walker's A/D write-back, exclusive re-read half (fused: no row item) -/
  | wWxrd (ws : List Wev) (d : Cdata) (b : Bud) (r : Bool) (n va : Nat)
      (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt) :
      devAddr req.pa = false → (classify req.access_kind).akLatest = true →
      wok (paZ req.pa) n →
      (∀ vs : List (BitVec 8), vs.length = n →
        CertW img dok wok kind QE Q (ws ++ [.WRmwR (paZ req.pa) vs]) ⟨d, b, r⟩
          (k (.Ok (wordOfBytes n vs, none))) t) →
      CertW img dok wok kind QE Q ws ⟨d, b, r⟩ (.impure (.ok (.memRead n va req)) k) t
  /-- the walker's A/D write-back, conditional-write half (one row item), right after its
  re-read at the same slot -/
  | wWxwr (ws : List Wev) (rvs : List (BitVec 8)) (d : Cdata) (b : Bud) (r : Bool) (n va : Nat)
      (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (Option Bool) Arch.abort → SailM X) (t : ExecSt) (v : BitVec (8 * n)) :
      devAddr req.pa = false → (classify req.access_kind).akLatest = true →
      req.value = some v →
      wok (paZ req.pa) n →
      (∃ ws0, ws = ws0 ++ [.WRmwR (paZ req.pa) rvs]) →
      CertW img dok wok kind QE Q (ws ++ [.WRmw (paZ req.pa) rvs (WeakInterpProj.wbytes n v)])
        ⟨d, b, r⟩ (k (.Ok (some true))) t →
      CertW img dok wok kind QE Q ws ⟨d, bsucc b, r⟩ (.impure (.ok (.memWrite n va req)) k) t

section certw
variable (img : Image) (dok wok : Int → Nat → Prop) (kind : Dkind)

theorem CertWMono {X : Type} (QE QE' : List Wev → Cst → Sail.Error exception → ExecSt → Prop)
    (Q Q' : List Wev → Cst → X → ExecSt → Prop) (ws : List Wev) (s : Cst) (m : SailM X)
    (t : ExecSt) :
    (∀ ws' s' e t', QE ws' s' e t' → QE' ws' s' e t') →
    (∀ ws' s' x t', Q ws' s' x t' → Q' ws' s' x t') →
    CertW img dok wok kind QE Q ws s m t → CertW img dok wok kind QE' Q' ws s m t := by
  intro HE HQ h
  induction h with
  | wRet ws s x t h => exact .wRet ws s x t (HQ ws s x t h)
  | wExt ws s e k t h => exact .wExt ws s e k t (HE ws s e t h)
  | wRd ws s r k t _ _ ihs ihn => exact .wRd ws s r k t ihs ihn
  | wWr ws s r v k t hr _ ih => exact .wWr ws s r v k t hr ih
  | wMrd ws d b r n va req k t vs h1 h2 h3 h4 _ ih =>
    exact .wMrd ws d b r n va req k t vs h1 h2 h3 h4 ih
  | wIf ws s n va req k t vs h1 h2 h3 h4 _ ih => exact .wIf ws s n va req k t vs h1 h2 h3 h4 ih
  | wEnd ws d r n va req k t h1 h2 h3 => exact .wEnd ws d r n va req k t h1 h2 h3
  | wDrd ws b r n va req k t h1 h2 h3 h4 h5 _ ih =>
    exact .wDrd ws b r n va req k t h1 h2 h3 h4 h5 ih
  | wDwr ws b r n va req k t v h1 h2 h3 h4 h5 _ ih =>
    exact .wDwr ws b r n va req k t v h1 h2 h3 h4 h5 ih
  | wFence ws d b r bk k t h1 _ ih => exact .wFence ws d b r bk k t h1 ih
  | wXrd ws b r n va req k t h1 h2 h3 h4 _ ih => exact .wXrd ws b r n va req k t h1 h2 h3 h4 ih
  | wXwr ws aq rvs b r n va req k t v h1 h2 h3 h4 h5 _ ih =>
    exact .wXwr ws aq rvs b r n va req k t v h1 h2 h3 h4 h5 ih
  | wIa ws s n w k t hs _ ih => exact .wIa ws s n w k t hs ih
  | wSf ws d b r n w k t hs _ ih => exact .wSf ws d b r n w k t hs ih
  | wBa ws s n a k t _ ih => exact .wBa ws s n a k t ih
  | wCo ws s c k t _ ih => exact .wCo ws s c k t ih
  | wTl ws s c k t _ ih => exact .wTl ws s c k t ih
  | wTe ws s f k t _ ih => exact .wTe ws s f k t ih
  | wRx ws s a k t _ ih => exact .wRx ws s a k t ih
  | wTs ws s a k t _ ih => exact .wTs ws s a k t ih
  | wTx ws s a k t _ ih => exact .wTx ws s a k t ih
  | wCc ws s k t _ ih => exact .wCc ws s k t ih
  | wMsg ws s a k t _ ih => exact .wMsg ws s a k t ih
  | wGcc ws s k t _ ih => exact .wGcc ws s k t ih
  | wWrd ws d b r n va req k t h1 h2 h3 h4 _ ih =>
    exact .wWrd ws d b r n va req k t h1 h2 h3 h4 ih
  | wWxrd ws d b r n va req k t h1 h2 h3 _ ih => exact .wWxrd ws d b r n va req k t h1 h2 h3 ih
  | wWxwr ws rvs d b r n va req k t v h1 h2 h3 h4 h5 _ ih =>
    exact .wWxwr ws rvs d b r n va req k t v h1 h2 h3 h4 h5 ih

theorem CertWBind {X Y : Type} (QE : List Wev → Cst → Sail.Error exception → ExecSt → Prop)
    (Q : List Wev → Cst → Y → ExecSt → Prop) (m : SailM X) (f : X → SailM Y) (ws : List Wev)
    (s : Cst) (t : ExecSt) :
    CertW img dok wok kind QE (fun ws' s' x t' => CertW img dok wok kind QE Q ws' s' (f x) t')
      ws s m t →
    CertW img dok wok kind QE Q ws s (m >>= f) t := by
  intro h
  induction h with
  | wRet ws s x t h => exact h
  | wExt ws s e k t h => exact .wExt ws s e _ t h
  | wRd ws s r k t _ _ ihs ihn => exact .wRd ws s r _ t ihs ihn
  | wWr ws s r v k t hr _ ih => exact .wWr ws s r v _ t hr ih
  | wMrd ws d b r n va req k t vs h1 h2 h3 h4 _ ih =>
    exact .wMrd ws d b r n va req _ t vs h1 h2 h3 h4 ih
  | wIf ws s n va req k t vs h1 h2 h3 h4 _ ih => exact .wIf ws s n va req _ t vs h1 h2 h3 h4 ih
  | wEnd ws d r n va req k t h1 h2 h3 => exact .wEnd ws d r n va req _ t h1 h2 h3
  | wDrd ws b r n va req k t h1 h2 h3 h4 h5 _ ih =>
    exact .wDrd ws b r n va req _ t h1 h2 h3 h4 h5 ih
  | wDwr ws b r n va req k t v h1 h2 h3 h4 h5 _ ih =>
    exact .wDwr ws b r n va req _ t v h1 h2 h3 h4 h5 ih
  | wFence ws d b r bk k t h1 _ ih => exact .wFence ws d b r bk _ t h1 ih
  | wXrd ws b r n va req k t h1 h2 h3 h4 _ ih => exact .wXrd ws b r n va req _ t h1 h2 h3 h4 ih
  | wXwr ws aq rvs b r n va req k t v h1 h2 h3 h4 h5 _ ih =>
    exact .wXwr ws aq rvs b r n va req _ t v h1 h2 h3 h4 h5 ih
  | wIa ws s n w k t hs _ ih => exact .wIa ws s n w _ t hs ih
  | wSf ws d b r n w k t hs _ ih => exact .wSf ws d b r n w _ t hs ih
  | wBa ws s n a k t _ ih => exact .wBa ws s n a _ t ih
  | wCo ws s c k t _ ih => exact .wCo ws s c _ t ih
  | wTl ws s c k t _ ih => exact .wTl ws s c _ t ih
  | wTe ws s f k t _ ih => exact .wTe ws s f _ t ih
  | wRx ws s a k t _ ih => exact .wRx ws s a _ t ih
  | wTs ws s a k t _ ih => exact .wTs ws s a _ t ih
  | wTx ws s a k t _ ih => exact .wTx ws s a _ t ih
  | wCc ws s k t _ ih => exact .wCc ws s _ t ih
  | wMsg ws s a k t _ ih => exact .wMsg ws s a _ t ih
  | wGcc ws s k t _ ih => exact .wGcc ws s _ t ih
  | wWrd ws d b r n va req k t h1 h2 h3 h4 _ ih =>
    exact .wWrd ws d b r n va req _ t h1 h2 h3 h4 ih
  | wWxrd ws d b r n va req k t h1 h2 h3 _ ih => exact .wWxrd ws d b r n va req _ t h1 h2 h3 ih
  | wWxwr ws rvs d b r n va req k t v h1 h2 h3 h4 h5 _ ih =>
    exact .wWxwr ws rvs d b r n va req _ t v h1 h2 h3 h4 h5 ih

end certw

/-! # 2. The one-event certificate is the special case `ws` constant -/

theorem CertWOfCert (img : Image) (dok wok : Int → Nat → Prop) (kind : Dkind) {X : Type}
    (QE : Cst → Sail.Error exception → ExecSt → Prop) (Q : Cst → X → ExecSt → Prop)
    (ws : List Wev) (s : Cst) (m : SailM X) (t : ExecSt) :
    AxCert.Cert img dok kind QE Q s m t →
    CertW img dok wok kind (fun ws' s' e t' => ws' = ws ∧ QE s' e t')
      (fun ws' s' x t' => ws' = ws ∧ Q s' x t') ws s m t := by
  intro h
  induction h with
  | cRet s x t h => exact .wRet ws s x t ⟨rfl, h⟩
  | cExt s e k t h => exact .wExt ws s e k t ⟨rfl, h⟩
  | cRd s r k t _ _ ihs ihn => exact .wRd ws s r k t ihs ihn
  | cWr s r v k t hr _ ih => exact .wWr ws s r v k t hr ih
  | cMrd d b r n va req k t vs h1 h2 h3 h4 _ ih =>
    exact .wMrd ws d b r n va req k t vs h1 h2 h3 h4 ih
  | cIf s n va req k t vs h1 h2 h3 h4 _ ih => exact .wIf ws s n va req k t vs h1 h2 h3 h4 ih
  | cEnd d r n va req k t h1 h2 h3 => exact .wEnd ws d r n va req k t h1 h2 h3
  | cDrd b r n va req k t h1 h2 h3 h4 h5 _ ih =>
    exact .wDrd ws b r n va req k t h1 h2 h3 h4 h5 ih
  | cDwr b r n va req k t v h1 h2 h3 h4 h5 _ ih =>
    exact .wDwr ws b r n va req k t v h1 h2 h3 h4 h5 ih
  | cFence d b r bk k t h1 _ ih => exact .wFence ws d b r bk k t h1 ih
  | cXrd b r n va req k t h1 h2 h3 h4 _ ih => exact .wXrd ws b r n va req k t h1 h2 h3 h4 ih
  | cXwr aq rvs b r n va req k t v h1 h2 h3 h4 h5 _ ih =>
    exact .wXwr ws aq rvs b r n va req k t v h1 h2 h3 h4 h5 ih
  | cIa s n w k t hs _ ih => exact .wIa ws s n w k t hs ih
  | cSf d b r n w k t hs _ ih => exact .wSf ws d b r n w k t hs ih
  | cBa s n a k t _ ih => exact .wBa ws s n a k t ih
  | cCo s c k t _ ih => exact .wCo ws s c k t ih
  | cTl s c k t _ ih => exact .wTl ws s c k t ih
  | cTe s f k t _ ih => exact .wTe ws s f k t ih
  | cRx s a k t _ ih => exact .wRx ws s a k t ih
  | cTs s a k t _ ih => exact .wTs ws s a k t ih
  | cTx s a k t _ ih => exact .wTx ws s a k t ih
  | cCc s k t _ ih => exact .wCc ws s k t ih
  | cMsg s a k t _ ih => exact .wMsg ws s a k t ih
  | cGcc s k t _ ih => exact .wGcc ws s k t ih

end Weak
