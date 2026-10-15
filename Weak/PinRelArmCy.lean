/-
Weak: **W11-C2′ (a3) relArmed — the ARMED-FLAG cycle predicate `amB`** (`PROGRESS-relArmed.md`).
Lean-only (no Rocq source).

`PinRelArm.amB A Aa P m st` is an all-paths predicate on a hart's Sail tree whose state tracks
the fetch log (w1's `FeEnt`, the cycle predicate's fetch filter `A` / address oracle `Aa`), the
hart's RELEASE FLAG as the primed machine folds it (`WbPrimed.armStep`: armed by
`LFence _ true _ true`, cleared by `LStore` and by `LExStore` outside a write-back node), and
whether the announced instruction is an AMO (`WbPrimed.ibAmo`, the write-back bit).  Along every
path of `m`, mirroring the hart's node dispatch `pnodeStep` (`WeakEvInst.lean:294`):
* a register read continues for every `Rboot`-admitted answer that agrees with the register's
  pin (`drefH`: the supervisor configuration the decoder reads, and `hart_state` active); a
  register write to a cause register (`cyS`: `scause`/`mcause`) is a STOP (no obligation), any
  other writes an `Rboot`-admitted value to an UNPINNED register and continues;
* a RAM instruction-fetch read owes nothing but is answered only by `A`-admitted bytes at the
  oracle's address, and LOGGED; every other read continues for every successful answer;
* a device write continues; a plain RAM write (`LStore`) of 4 bytes OWES the flag armed, and
  clears it; an exclusive RAM write (`LExStore`) clears it iff the instruction is an AMO;
* a barrier applies its label and its parked fence to the flag (`armBar`);
* an announce records the AMO bit; every other node continues for every answer.

Every helper is `Weak.PinRelArm.*`.
-/
import Weak.PinRelArmMem
import Weak.PinCycRunFetch
import Weak.WbPrimedArm

namespace Weak
open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open Wlabel

namespace PinRelArm
open SailCycleOrderK PinCycRun PinRelArmFp

/-! ## 1. The predicate -/

/-- The pinned registers: the decoder's supervisor configuration (`MachCSL.drefS`: privilege,
`misa`, `menvcfg`, `mseccfg`) and the active hart state. -/
def drefH : (r : Register) → Option (RegisterType r)
  | .hart_state => some (HartState.HART_ACTIVE ())
  | r => drefS r

/-- A register value agrees with its pin (if any). -/
def gOk (r : Register) (v : RegisterType r) : Prop := ∀ v0, drefH r = some v0 → v = v0

/-- An unprotected register (`zfB`'s writes) carries no pin. -/
theorem zfDref (r : Register) (h : zfRegOk r = true) : drefH r = none := by
  unfold drefH
  split
  · simp [zfRegOk, zfProt] at h
  · unfold drefS
    split <;> simp_all [zfRegOk, zfProt]

/-- The tracked state: the fetch log, the release flag, the announced instruction's AMO bit. -/
structure AmSt where
  fe : List FeEnt
  armed : Bool
  amo : Bool

def amFe (st : AmSt) (a : Int) (n : Nat) (w : BitVec (8 * n)) : AmSt :=
  { st with fe := st.fe ++ [⟨a, n, w⟩] }

/-- The flag after a barrier node (`ebarLabel b`) and its parked fence (`ebarPark b`). -/
def armBar (b : barrier_kind) (a : Bool) : Bool :=
  match ebarPark b with
  | some (pr, pw, sr, sw) => WbPrimed.armStep true (LFence pr pw sr sw)
      (WbPrimed.armStep true (ebarLabel b) a)
  | none => WbPrimed.armStep true (ebarLabel b) a

/-- **THE ARMED-FLAG PREDICATE** (header). -/
def amB {X : Type} (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop) (P : X → AmSt → Prop) :
    SailM X → AmSt → Prop
  | .pure x, st => P x st
  | .impure (.error _) _, _ => True
  | .impure (.ok o) k, st =>
    match o, k with
    | .regRead r, k => ∀ v, Rboot r v → gOk r v → amB A Aa P (k v) st
    | .regWrite r v, k => cyS r = false → Rboot r v ∧ drefH r = none ∧ ∀ u, amB A Aa P (k u) st
    | .memRead n _ req, k =>
        (devAddr req.pa = false → (classify req.access_kind).akIfetch = true →
          Aa st.fe.length (paZ req.pa) →
          ∀ w : BitVec (8 * n), (∀ j, j < n → A (paZ req.pa + (j : Int)) (nthByte w j)) →
            amB A Aa P (k (.Ok (w, none))) (amFe st (paZ req.pa) n w)) ∧
        ((devAddr req.pa = false → (classify req.access_kind).akIfetch = false) →
          ∀ w : BitVec (8 * n), amB A Aa P (k (.Ok (w, none))) st)
    | .memWrite n _ req, k =>
        (devAddr req.pa = true → amB A Aa P (k (.Ok (some true))) st) ∧
        (devAddr req.pa = false → akExcl req.access_kind = false →
          (n = 4 → st.armed = true) ∧ amB A Aa P (k (.Ok (some true))) { st with armed := false }) ∧
        (devAddr req.pa = false → akExcl req.access_kind = true →
          amB A Aa P (k (.Ok (some true))) { st with armed := st.armed && !st.amo })
    | .barrier b, k => amB A Aa P (k ()) { st with armed := armBar b st.armed }
    | .instrAnnounce _ w, k =>
        ∀ u, amB A Aa P (k u) { st with amo := WbPrimed.ibAmo (ibAnn (ibOfBvn w)) }
    | .branchAnnounce .., k => ∀ v, amB A Aa P (k v) st
    | .cacheOp _, k => ∀ v, amB A Aa P (k v) st
    | .tlbi _, k => ∀ v, amB A Aa P (k v) st
    | .takeException _, k => ∀ v, amB A Aa P (k v) st
    | .returnException _, k => ∀ v, amB A Aa P (k v) st
    | .translationStart _, k => ∀ v, amB A Aa P (k v) st
    | .translationEnd _, k => ∀ v, amB A Aa P (k v) st
    | .cycleCount, k => ∀ v, amB A Aa P (k v) st
    | .getCycleCount, k => amB A Aa P (k (0 : Nat)) st
    | .message _, k => ∀ v, amB A Aa P (k v) st
    | .choose _, k => ∀ v, amB A Aa P (k v) st
    | .readRam .., k => ∀ v, amB A Aa P (k v) st
    | .writeRam .., k => ∀ v, amB A Aa P (k v) st

/-! ## 2. The kit -/

section kit
variable {A : Int → BitVec 8 → Prop} {Aa : Nat → Int → Prop}

theorem amBind {X Y : Type} (Q : X → AmSt → Prop) (P : Y → AmSt → Prop) (m : SailM X)
    (f : X → SailM Y) :
    ∀ st, amB A Aa Q m st → (∀ x st', Q x st' → amB A Aa P (f x) st') →
      amB A Aa P (m >>= f) st := by
  induction m with
  | pure y => intro st hm hf; exact hf y st hm
  | impure call k ih =>
    intro st hm hf
    cases call with
    | error e => trivial
    | ok o =>
      show amB A Aa P (FreeM.impure (.ok o) (fun v => k v >>= f)) st
      cases o
      case regRead => exact fun v hv hg => ih v _ (hm v hv hg) hf
      case regWrite => exact fun h => ⟨(hm h).1, (hm h).2.1, fun u => ih u _ ((hm h).2.2 u) hf⟩
      case memRead =>
        exact ⟨fun h1 h2 ha w hw => ih _ _ (hm.1 h1 h2 ha w hw) hf, fun h w => ih _ _ (hm.2 h w) hf⟩
      case memWrite =>
        exact ⟨fun h => ih _ _ (hm.1 h) hf, fun h1 h2 => ⟨(hm.2.1 h1 h2).1, ih _ _ (hm.2.1 h1 h2).2 hf⟩,
          fun h1 h2 => ih _ _ (hm.2.2 h1 h2) hf⟩
      case barrier => exact ih _ _ hm hf
      case instrAnnounce => exact fun u => ih u _ (hm u) hf
      case getCycleCount => exact ih _ _ hm hf
      all_goals exact fun v => ih v _ (hm v) hf

theorem amPure {X : Type} (P : X → AmSt → Prop) (x : X) (st : AmSt) :
    P x st → amB A Aa P (pure x : SailM X) st := fun h => h

/-- `armBar` never clears the flag. -/
theorem armBarMono (b : barrier_kind) (a : Bool) (h : a = true) : armBar b a = true := by
  subst h
  unfold armBar WbPrimed.armStep
  cases b <;> simp [ebarPark, ebarLabel, ebarNow, WbPrimed.lbArms, WbPrimed.lbConsumes]

/-- **THE `zfB` LIFT** (header): a strict `zfB` footprint, started with no AMO announced, keeps
the log and the AMO bit and never lowers the flag. -/
theorem amOfZf {X : Type} (P : X → Prop) (Q : X → AmSt → Prop) :
    ∀ (m : SailM X) (st : AmSt), zfB false P m → st.amo = false →
      (∀ x st', P x → st'.fe = st.fe → st'.amo = false → (st.armed = true → st'.armed = true) →
        Q x st') → amB A Aa Q m st := by
  intro m
  induction m with
  | pure x => intro st hp ha hq; exact hq x st hp rfl ha id
  | impure call k ih =>
    intro st hp ha hq
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead r => exact fun v hv _ => ih v st (hp v hv) ha hq
      case regWrite r v => exact fun _ => ⟨hp.1.1, zfDref r hp.1.2, fun u => ih u st (hp.2 u) ha hq⟩
      case memRead n va req =>
        obtain ⟨hif, hk⟩ := hp
        refine ⟨fun _ h2 => ?_, fun _ w => ih _ st (hk _) ha hq⟩
        exact absurd h2 (by simp only [PinRelArmFp.ifOk] at hif; simp [classify, hif])
      case memWrite n va req =>
        obtain ⟨hw, hk⟩ := hp
        refine ⟨fun _ => ih _ st (hk _) ha hq, fun h1 h2 => ?_, fun _ _ => ?_⟩
        · rcases hw with h | h
          · rw [h1] at h; cases h
          · rw [h2] at h; cases h
        · refine ih _ _ (hk _) ha (fun x st' e1 e2 e3 e4 => hq x st' e1 e2 e3 (fun h => e4 ?_))
          show (st.armed && !st.amo) = true
          rw [h, ha]; rfl
      case instrAnnounce => exact hp.elim
      case barrier b =>
        exact ih _ _ hp.2 ha (fun x st' e1 e2 e3 e4 => hq x st' e1 e2 e3
          (fun h => e4 (armBarMono b _ h)))
      case getCycleCount => exact ih _ st (hp _) ha hq
      all_goals exact fun v => ih v st (hp v) ha hq

end kit

end PinRelArm
end Weak
