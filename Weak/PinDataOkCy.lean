/-
Weak: **`dataOkR` (4a) — the FILTERED cycle predicate `cyDB`** (`PROGRESS-dataOk.md`).  Lean-only.

`cyDB G D A Aa T P m st` is w1's cycle predicate `PinCycRun.cyB` (`Weak/PinCycRun.lean`, with the
stop set `cyS`) with three changes:
* a register read is answered by the mirror AND by a value the read filter `G` admits (the
  interface's `dG`: justified per read by the run, `dataRealized`);
* a memory read (fetch or not) is answered by a value the answer filter `D` admits (`dAns`);
  a memory write is answered `.Ok (some true)` (the only answer `WeakEvInst.pnodeStep` gives);
* the STOP is value-dependent: a cause write (`cyS`) of an EXCEPTION (`causeBit` false) ends the
  obligation with the stop post `T`; an INTERRUPT's cause write (`causeBit` true) continues like
  any other write — so a run is followed through an interrupt's trap handler.
§1 the predicate; §2 the kit; §3 the lift from `cyB` (whose stops are all exceptions' —
`causeBit` false in its stop post); §4 the product with the state-free `dkB` (the data access).
Every helper is `Weak.PinDataOk.*`.
-/
import Weak.PinDataOkExec
import Weak.PinCycRunAsm

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinDataOk
open SailCycleOrderK PinCycRun

/-! ## 1. The predicate -/

/-- **THE FILTERED CYCLE PREDICATE** (header). -/
def cyDB {X : Type} (G : (r : Register) → RegisterType r → Prop)
    (D : BitVec 64 → (n : Nat) → BitVec (8 * n) → Prop) (A : Int → BitVec 8 → Prop)
    (Aa : Nat → Int → Prop) (T : CySt → (r : Register) → RegisterType r → Prop)
    (P : X → CySt → Prop) : SailM X → CySt → Prop
  | .pure x, st => P x st
  | .impure (.error _) _, _ => True
  | .impure (.ok o) k, st =>
    match o, k with
    | .regRead r, k => ∀ v, PinCycRun.rdOk st r v → G r v → cyDB G D A Aa T P (k v) (cyRd st r)
    | .regWrite r v, k =>
        (cyS r = true → causeBit r v = false → T st r v) ∧
        ((cyS r = false ∨ causeBit r v = true) → Rboot r v ∧ ∀ u, cyDB G D A Aa T P (k u) (cyWr st r v))
    | .memRead n _ req, k =>
        (devAddr req.pa = false → (classify req.access_kind).akIfetch = true →
          Aa st.fe.length (paZ req.pa) →
          ∀ w : BitVec (8 * n), (∀ j, j < n → A (paZ req.pa + (j : Int)) (nthByte w j)) →
            D req.pa n w → cyDB G D A Aa T P (k (.Ok (w, none))) (cyFe st (paZ req.pa) n w)) ∧
        ((devAddr req.pa = false → (classify req.access_kind).akIfetch = false) →
          ∀ w : BitVec (8 * n), D req.pa n w → cyDB G D A Aa T P (k (.Ok (w, none))) st)
    | .instrAnnounce n w, k => st.an = false ∧ ∀ u, cyDB G D A Aa T P (k u) (cyAnn st n w)
    | .memWrite .., k => cyDB G D A Aa T P (k (.Ok (some true))) st
    | .getCycleCount, k => cyDB G D A Aa T P (k (0 : Nat)) st
    | .barrier _, k => ∀ v, cyDB G D A Aa T P (k v) st
    | .branchAnnounce .., k => ∀ v, cyDB G D A Aa T P (k v) st
    | .cacheOp _, k => ∀ v, cyDB G D A Aa T P (k v) st
    | .tlbi _, k => ∀ v, cyDB G D A Aa T P (k v) st
    | .takeException _, k => ∀ v, cyDB G D A Aa T P (k v) st
    | .returnException _, k => ∀ v, cyDB G D A Aa T P (k v) st
    | .translationStart _, k => ∀ v, cyDB G D A Aa T P (k v) st
    | .translationEnd _, k => ∀ v, cyDB G D A Aa T P (k v) st
    | .cycleCount, k => ∀ v, cyDB G D A Aa T P (k v) st
    | .message _, k => ∀ v, cyDB G D A Aa T P (k v) st
    | .choose _, k => ∀ v, cyDB G D A Aa T P (k v) st
    | .readRam .., k => ∀ v, cyDB G D A Aa T P (k v) st
    | .writeRam .., k => ∀ v, cyDB G D A Aa T P (k v) st

/-! ## 2. The kit -/

section kit
variable {G : (r : Register) → RegisterType r → Prop} {D : BitVec 64 → (n : Nat) → BitVec (8 * n) → Prop}
  {A : Int → BitVec 8 → Prop} {Aa : Nat → Int → Prop} {T : CySt → (r : Register) → RegisterType r → Prop}

theorem cyDBind {X Y : Type} (Q : X → CySt → Prop) (P : Y → CySt → Prop) (m : SailM X)
    (f : X → SailM Y) :
    ∀ st, cyDB G D A Aa T Q m st → (∀ x st', Q x st' → cyDB G D A Aa T P (f x) st') →
      cyDB G D A Aa T P (m >>= f) st := by
  induction m with
  | pure y => intro st hm hf; exact hf y st hm
  | impure call k ih =>
    intro st hm hf
    cases call with
    | error e => trivial
    | ok o =>
      show cyDB G D A Aa T P (FreeM.impure (.ok o) (fun v => k v >>= f)) st
      cases o
      case regRead => exact fun v hv hg => ih v _ (hm v hv hg) hf
      case regWrite => exact ⟨hm.1, fun h => ⟨(hm.2 h).1, fun u => ih u _ ((hm.2 h).2 u) hf⟩⟩
      case memRead =>
        exact ⟨fun h1 h2 ha w hw hd => ih _ _ (hm.1 h1 h2 ha w hw hd) hf,
          fun h w hd => ih _ _ (hm.2 h w hd) hf⟩
      case instrAnnounce => exact ⟨hm.1, fun u => ih u _ (hm.2 u) hf⟩
      case memWrite => exact ih _ _ hm hf
      case getCycleCount => exact ih _ _ hm hf
      all_goals exact fun v => ih v _ (hm v) hf

theorem cyDMono {X : Type} (P P' : X → CySt → Prop) (hP : ∀ x st, P x st → P' x st) :
    ∀ (m : SailM X) st, cyDB G D A Aa T P m st → cyDB G D A Aa T P' m st := by
  intro m
  induction m with
  | pure y => exact fun st h => hP y st h
  | impure call k ih =>
    intro st hm
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead => exact fun v hv hg => ih v _ (hm v hv hg)
      case regWrite => exact ⟨hm.1, fun h => ⟨(hm.2 h).1, fun u => ih u _ ((hm.2 h).2 u)⟩⟩
      case memRead =>
        exact ⟨fun h1 h2 ha w hw hd => ih _ _ (hm.1 h1 h2 ha w hw hd), fun h w hd => ih _ _ (hm.2 h w hd)⟩
      case instrAnnounce => exact ⟨hm.1, fun u => ih u _ (hm.2 u)⟩
      case memWrite => exact ih _ _ hm
      case getCycleCount => exact ih _ _ hm
      all_goals exact fun v => ih v _ (hm v)

theorem cyDReadBind {Y : Type} (Q : Y → CySt → Prop) (r : Register) (f : RegisterType r → SailM Y)
    (st : CySt) (h : ∀ v, PinCycRun.rdOk st r v → G r v → cyDB G D A Aa T Q (f v) (cyRd st r)) :
    cyDB G D A Aa T Q (readReg r >>= f) st := h

theorem cyDWriteBind {Y : Type} (Q : Y → CySt → Prop) (r : Register) (v : RegisterType r)
    (f : PUnit → SailM Y) (st : CySt) (hs : cyS r = false ∨ causeBit r v = true) (hb : Rboot r v)
    (h : cyDB G D A Aa T Q (f ()) (cyWr st r v)) : cyDB G D A Aa T Q (writeReg r v >>= f) st := by
  refine ⟨fun h1 h2 => ?_, fun _ => ⟨hb, fun u => by cases u; exact h⟩⟩
  rcases hs with hs | hs
  · rw [hs] at h1; cases h1
  · rw [hs] at h2; cases h2

theorem cyDPureBind {X Y : Type} (Q : Y → CySt → Prop) (x : X) (f : X → SailM Y) (st : CySt)
    (h : cyDB G D A Aa T Q (f x) st) : cyDB G D A Aa T Q ((pure x : SailM X) >>= f) st := h

/-! ## 3. The lift from `cyB` -/

/-- **The lift**: a `cyB` fact whose stops are exceptions' (`causeBit` false) is a `cyDB` fact
(more filters, the write answer fixed, an interrupt's cause write never a `cyB` stop of it). -/
theorem cyDOfCyB {X : Type} (P : X → CySt → Prop) :
    ∀ (m : SailM X) st, cyB A Aa cyS (fun st r v => causeBit r v = false ∧ T st r v) P m st →
      cyDB G D A Aa T P m st := by
  intro m
  induction m with
  | pure y => exact fun st h => h
  | impure call k ih =>
    intro st hm
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead => exact fun v hv _ => ih v _ (hm v hv)
      case regWrite r v =>
        refine ⟨fun hs _ => (hm.1 hs).2, fun h => ?_⟩
        cases hs : cyS r with
        | false => exact ⟨(hm.2 hs).1, fun u => ih u _ ((hm.2 hs).2 u)⟩
        | true =>
          rcases h with h | h
          · rw [hs] at h; cases h
          · have := (hm.1 hs).1; rw [h] at this; cases this
      case memRead =>
        exact ⟨fun h1 h2 ha w hw _ => ih _ _ (hm.1 h1 h2 ha w hw), fun h w _ => ih _ _ (hm.2 h w)⟩
      case instrAnnounce => exact ⟨hm.1, fun u => ih u _ (hm.2 u)⟩
      case memWrite => exact ih _ _ (hm _)
      case getCycleCount => exact ih _ _ hm
      all_goals exact fun v => ih v _ (hm v)

end kit

/-! ## 4. The product with the data access -/

/-- **The product**: a `cyDB` fact at the interface's filters and a `dkB` fact of the same tree. -/
theorem cyDAndDk (c : DCfg) {A : Int → BitVec 8 → Prop} {Aa : Nat → Int → Prop}
    {T : CySt → (r : Register) → RegisterType r → Prop} {X : Type} (Q : X → CySt → Prop) (R : X → Prop) :
    ∀ (m : SailM X) st, cyDB (dG c) (dAns c) A Aa T Q m st → dkB c R m →
      cyDB (dG c) (dAns c) A Aa T (fun x st' => Q x st' ∧ R x) m st := by
  intro m
  induction m with
  | pure y => exact fun st h1 h2 => ⟨h1, h2⟩
  | impure call k ih =>
    intro st h1 h2
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead => exact fun v hv hg => ih v _ (h1 v hv hg) (h2 v hg)
      case regWrite => exact ⟨h1.1, fun h => ⟨(h1.2 h).1, fun u => ih u _ ((h1.2 h).2 u) (h2 u)⟩⟩
      case memRead =>
        exact ⟨fun a1 a2 a3 w hw hd => ih _ _ (h1.1 a1 a2 a3 w hw hd) (h2 w hd),
          fun a w hd => ih _ _ (h1.2 a w hd) (h2 w hd)⟩
      case instrAnnounce => exact ⟨h1.1, fun u => ih u _ (h1.2 u) (h2 u)⟩
      case memWrite => exact ih _ _ h1 h2
      case getCycleCount => exact ih _ _ h1 (h2 _)
      all_goals exact fun v => ih v _ (h1 v) (h2 v)

end PinDataOk
end Weak
