/-
Weak: **r2 glue (C) — THE FETCH-ADDRESS CYCLE PREDICATE `cyFB`** (`PROGRESS-r2glue.md`).
Lean-only.

`cyFB D Aa P m st` follows the hart's own step along every path of a Sail tree like w1's
`PinCycRun.cyB` / the filtered `PinDataOk.cyDB` (the register MIRROR `st.rv`, the fetch log
`st.fe`, the announce flag), with three changes:
* there is NO stop: every register write (a cause write included) writes an `Rboot`-admitted
  value and continues — the predicate follows the WHOLE cycle, trap handlers included;
* a RAM instruction-fetch read OWES its address: `Aa |fe| (paZ pa)` (in the instance `kAa pc`:
  the `k`-th fetch read is at `pc + 2k`) — an obligation, where `cyB` assumes it;
* every memory read is answered by a value the answer filter `D` admits (`tvAns` of the fetch's
  configurations), a memory write `.Ok (some true)` (the only answer `pnodeStep` gives).
§1 the predicate; §2 the kit; §3 the lifts from W-SCO's strict footprint `fp` (no fetch read: the
obligation is vacuous; the mirror is lost but for `Rboot`, the log and the flag) and from w1's
`pf` × our `xf` (the mirror keeps the protected registers — `PC` — and `satp`/`tlb`).  Every helper
is `Weak.PinFetchPa.*`.
-/
import Weak.PinDataOkCy
import Weak.PinFetchPaRun
import Weak.PinCycRunLift

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinFetchPa
open SailCycleOrderK PinCycRun PinDataflow
open PinCycRunFp (pfB pfProt pfRegOk pfW)

/-! ## 1. The predicate -/

/-- **THE FETCH-ADDRESS CYCLE PREDICATE** (header). -/
def cyFB {X : Type} (D : BitVec 64 → (n : Nat) → BitVec (8 * n) → Prop) (Aa : Nat → Int → Prop)
    (P : X → CySt → Prop) : SailM X → CySt → Prop
  | .pure x, st => P x st
  | .impure (.error _) _, _ => True
  | .impure (.ok o) k, st =>
    match o, k with
    | .regRead r, k => ∀ v, PinCycRun.rdOk st r v → cyFB D Aa P (k v) (cyRd st r)
    | .regWrite r v, k => Rboot r v ∧ ∀ u, cyFB D Aa P (k u) (cyWr st r v)
    | .memRead n _ req, k =>
        (devAddr req.pa = false → (classify req.access_kind).akIfetch = true →
          Aa st.fe.length (paZ req.pa) ∧
          ∀ w : BitVec (8 * n), D req.pa n w → cyFB D Aa P (k (.Ok (w, none))) (cyFe st (paZ req.pa) n w)) ∧
        ((devAddr req.pa = false → (classify req.access_kind).akIfetch = false) →
          ∀ w : BitVec (8 * n), D req.pa n w → cyFB D Aa P (k (.Ok (w, none))) st)
    | .instrAnnounce n w, k => st.an = false ∧ ∀ u, cyFB D Aa P (k u) (cyAnn st n w)
    | .memWrite .., k => cyFB D Aa P (k (.Ok (some true))) st
    | .getCycleCount, k => cyFB D Aa P (k (0 : Nat)) st
    | .barrier _, k => ∀ v, cyFB D Aa P (k v) st
    | .branchAnnounce .., k => ∀ v, cyFB D Aa P (k v) st
    | .cacheOp _, k => ∀ v, cyFB D Aa P (k v) st
    | .tlbi _, k => ∀ v, cyFB D Aa P (k v) st
    | .takeException _, k => ∀ v, cyFB D Aa P (k v) st
    | .returnException _, k => ∀ v, cyFB D Aa P (k v) st
    | .translationStart _, k => ∀ v, cyFB D Aa P (k v) st
    | .translationEnd _, k => ∀ v, cyFB D Aa P (k v) st
    | .cycleCount, k => ∀ v, cyFB D Aa P (k v) st
    | .message _, k => ∀ v, cyFB D Aa P (k v) st
    | .choose _, k => ∀ v, cyFB D Aa P (k v) st
    | .readRam .., k => ∀ v, cyFB D Aa P (k v) st
    | .writeRam .., k => ∀ v, cyFB D Aa P (k v) st

/-! ## 2. The kit -/

section kit
variable {D : BitVec 64 → (n : Nat) → BitVec (8 * n) → Prop} {Aa : Nat → Int → Prop}

theorem cyFBind {X Y : Type} (Q : X → CySt → Prop) (P : Y → CySt → Prop) (m : SailM X)
    (f : X → SailM Y) :
    ∀ st, cyFB D Aa Q m st → (∀ x st', Q x st' → cyFB D Aa P (f x) st') → cyFB D Aa P (m >>= f) st := by
  induction m with
  | pure y => intro st hm hf; exact hf y st hm
  | impure call k ih =>
    intro st hm hf
    cases call with
    | error e => trivial
    | ok o =>
      show cyFB D Aa P (FreeM.impure (.ok o) (fun v => k v >>= f)) st
      cases o
      case regRead => exact fun v hv => ih v _ (hm v hv) hf
      case regWrite => exact ⟨hm.1, fun u => ih u _ (hm.2 u) hf⟩
      case memRead =>
        exact ⟨fun h1 h2 => ⟨(hm.1 h1 h2).1, fun w hd => ih _ _ ((hm.1 h1 h2).2 w hd) hf⟩,
          fun h w hd => ih _ _ (hm.2 h w hd) hf⟩
      case instrAnnounce => exact ⟨hm.1, fun u => ih u _ (hm.2 u) hf⟩
      case memWrite => exact ih _ _ hm hf
      case getCycleCount => exact ih _ _ hm hf
      all_goals exact fun v => ih v _ (hm v) hf

theorem cyFMono {X : Type} (P P' : X → CySt → Prop) (hP : ∀ x st, P x st → P' x st) :
    ∀ (m : SailM X) st, cyFB D Aa P m st → cyFB D Aa P' m st := by
  intro m
  induction m with
  | pure y => exact fun st h => hP y st h
  | impure call k ih =>
    intro st hm
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead => exact fun v hv => ih v _ (hm v hv)
      case regWrite => exact ⟨hm.1, fun u => ih u _ (hm.2 u)⟩
      case memRead =>
        exact ⟨fun h1 h2 => ⟨(hm.1 h1 h2).1, fun w hd => ih _ _ ((hm.1 h1 h2).2 w hd)⟩,
          fun h w hd => ih _ _ (hm.2 h w hd)⟩
      case instrAnnounce => exact ⟨hm.1, fun u => ih u _ (hm.2 u)⟩
      case memWrite => exact ih _ _ hm
      case getCycleCount => exact ih _ _ hm
      all_goals exact fun v => ih v _ (hm v)

theorem cyFReadBind {Y : Type} (Q : Y → CySt → Prop) (r : Register) (f : RegisterType r → SailM Y)
    (st : CySt) (h : ∀ v, PinCycRun.rdOk st r v → cyFB D Aa Q (f v) (cyRd st r)) :
    cyFB D Aa Q (readReg r >>= f) st := h

theorem cyFWriteBind {Y : Type} (Q : Y → CySt → Prop) (r : Register) (v : RegisterType r)
    (f : PUnit → SailM Y) (st : CySt) (hb : Rboot r v) (h : cyFB D Aa Q (f ()) (cyWr st r v)) :
    cyFB D Aa Q (writeReg r v >>= f) st :=
  ⟨hb, fun u => by cases u; exact h⟩

theorem cyFPureBind {X Y : Type} (Q : Y → CySt → Prop) (x : X) (f : X → SailM Y) (st : CySt)
    (h : cyFB D Aa Q (f x) st) : cyFB D Aa Q ((pure x : SailM X) >>= f) st := h

theorem cyFAnnBind {Y : Type} (Q : Y → CySt → Prop) {n : Nat} (w : BitVec n) (f : Unit → SailM Y)
    (st : CySt) (han : st.an = false) (h : cyFB D Aa Q (f ()) (cyAnn st n w)) :
    cyFB D Aa Q (instr_announce w >>= f) st :=
  ⟨han, fun u => by cases u; exact h⟩

end kit

/-! ## 3. The lifts -/

section lift
variable {D : BitVec 64 → (n : Nat) → BitVec (8 * n) → Prop} {Aa : Nat → Int → Prop}

/-- What a strict-footprint stretch keeps: the log, the flag, the mirror `Rboot`-admitted. -/
def fpKeep (st st' : CySt) : Prop := st'.fe = st.fe ∧ st'.an = st.an ∧ RbootAll st'.rv

/-- **THE `fp` LIFT** (header): a W-SCO strict footprint (no fetch read, no announce, `Rboot`
reads and writes) satisfies `cyFB` with its post and `fpKeep`. -/
theorem cyFOfFp {X : Type} (S : X → Prop) :
    ∀ (m : SailM X) (st : CySt), SailCycleOrderFp.fp S m → RbootAll st.rv →
      cyFB D Aa (fun x st' => S x ∧ fpKeep st st') m st := by
  intro m
  induction m with
  | pure x => intro st hp hrb; exact ⟨hp, rfl, rfl, hrb⟩
  | impure call k ih =>
    intro st hp hrb
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead r =>
        intro v hv
        exact cyFMono _ _ (fun x s' h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩) _ _
          (ih v (cyRd st r) (hp v (PinCycRun.rdRboot st r v hrb hv)) hrb)
      case regWrite r v =>
        obtain ⟨hb, hk⟩ := hp
        refine ⟨hb, fun u => ?_⟩
        exact cyFMono _ _ (fun x s' h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩) _ _
          (ih u (cyWr st r v) (hk u) (rbootAllSet _ r v hrb hb))
      case memRead n va req =>
        obtain ⟨hif, hk⟩ := hp
        refine ⟨fun _ h2 => ?_, fun _ w _ => ih _ st (hk _) hrb⟩
        exact absurd h2 (by simp only [SailCycleOrderFp.ifOk] at hif; simp [classify, hif])
      case instrAnnounce => exact hp.elim
      case barrier b => exact fun v => ih v st hp.2 hrb
      case memWrite => exact ih _ st (hp _) hrb
      case getCycleCount => exact ih _ st (hp _) hrb
      all_goals exact fun v => ih v st (hp v) hrb

/-- A strict-footprint head of a bind. -/
theorem cyFFpBind {X Y : Type} (S : X → Prop) (P : Y → CySt → Prop) (m : SailM X) (f : X → SailM Y)
    (st : CySt) (hm : SailCycleOrderFp.fp S m) (hrb : RbootAll st.rv)
    (hf : ∀ x st', S x → fpKeep st st' → cyFB D Aa P (f x) st') : cyFB D Aa P (m >>= f) st :=
  cyFBind _ P m f st (cyFOfFp S m st hm hrb) (fun x st' h => hf x st' h.1 h.2)

/-- The registers the fetch's walk needs kept before it: w1's protected set (`PC` among them) and
`satp`/`tlb`. -/
def fkProt (r : Register) : Prop := pfProt r = true ∨ PinFetchPaFp.xfProt r = true

/-- What a `pf` × `xf` stretch keeps: `fpKeep` and the mirror at `fkProt`. -/
def pxKeep (st st' : CySt) : Prop := fpKeep st st' ∧ ∀ r, fkProt r → st'.rv r = st.rv r

theorem pxKeepRefl (st : CySt) (h : RbootAll st.rv) : pxKeep st st := ⟨⟨rfl, rfl, h⟩, fun _ _ => rfl⟩

theorem pxKeepTrans (s1 s2 s3 : CySt) (h1 : pxKeep s1 s2) (h2 : pxKeep s2 s3) : pxKeep s1 s3 :=
  ⟨⟨h2.1.1.trans h1.1.1, h2.1.2.1.trans h1.1.2.1, h2.1.2.2⟩, fun r hr => (h2.2 r hr).trans (h1.2 r hr)⟩

/-- **THE `pf` × `xf` LIFT** (header): a tree that is both a w1 strict footprint (no protected
write) and an `xf` footprint (no `satp`/`tlb` write) keeps the mirror at `fkProt`. -/
theorem cyFOfPfXf {X : Type} (S S' : X → Prop) :
    ∀ (m : SailM X) (st : CySt), pfB false S m → PinFetchPaFp.xf S' m → RbootAll st.rv →
      cyFB D Aa (fun x st' => S x ∧ pxKeep st st') m st := by
  intro m
  induction m with
  | pure x => intro st hp _ hrb; exact ⟨hp, pxKeepRefl st hrb⟩
  | impure call k ih =>
    intro st hp hx hrb
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead r =>
        intro v hv
        have hb := PinCycRun.rdRboot st r v hrb hv
        exact cyFMono _ _ (fun x s' h => ⟨h.1, pxKeepTrans _ _ _ (pxKeepRefl st hrb) h.2⟩) _ _
          (ih v (cyRd st r) (hp v hb) (hx v hb) hrb)
      case regWrite r v =>
        obtain ⟨⟨hb, hok⟩, hk⟩ := hp
        obtain ⟨⟨-, hok'⟩, hk'⟩ := hx
        refine ⟨hb, fun u => ?_⟩
        have hrb' : RbootAll (cyWr st r v).rv := rbootAllSet _ r v hrb hb
        have hkp : pxKeep st (cyWr st r v) := by
          refine ⟨⟨rfl, rfl, hrb'⟩, fun r' hr' => ?_⟩
          have e : r' ≠ r := by
            rintro rfl
            rcases hr' with h | h
            · simp [pfRegOk, h] at hok
            · simp [PinFetchPaFp.xfRegOk, h] at hok'
          exact RegFile.set_other _ _ _ _ e
        exact cyFMono _ _ (fun x s' h => ⟨h.1, pxKeepTrans _ _ _ hkp h.2⟩) _ _
          (ih u (cyWr st r v) (hk u) (hk' u) hrb')
      case memRead n va req =>
        obtain ⟨hif, hk⟩ := hp
        refine ⟨fun _ h2 => ?_, fun _ w _ => ih _ st (hk _) (hx.2 _) hrb⟩
        exact absurd h2 (by simp only [PinCycRunFp.ifOk] at hif; simp [classify, hif])
      case instrAnnounce => exact hp.elim
      case barrier b => exact fun v => ih v st hp.2 hx.2 hrb
      case memWrite => exact ih _ st (hp _) (hx _) hrb
      case getCycleCount => exact ih _ st (hp _) (hx _) hrb
      all_goals exact fun v => ih v st (hp v) (hx v) hrb

end lift

end PinFetchPa
end Weak
