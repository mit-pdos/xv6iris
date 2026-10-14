/-
Weak: **W9a (B) B5 r2 part (B) — the fetch translation's VALUE predicate `tvB`** (plan
`notes/weak-allocproc-plan.md` rev 52 §D Q-B5-FETCH (r2-a); rulings [OWN.81] [OWN.92];
`PROGRESS-r2.md`).  Lean-only (no Rocq source).

`PinFetchPa.tvB c P m` is an all-paths predicate on a Sail tree, B1/r1-shaped (`PinFetchVal.faB`
without its state), for the Sv39 translation of a kernel-text fetch under the configuration `c`
(root page `b`, level-1 page `b1`, level-0 page `b0`, the fetch's `vpn`).  Along every path of `m`:
* a memory read is answered by every value the PTE filter `tvAns c` admits: an 8-byte read at the
  walk's level-2 / level-1 slot answers the pointer `kPtr b1` / `kPtr b0`, at the level-0 slot an
  A/D variant of the identity `R|X` leaf `kLeaf (idPpn vpn) .rx a d`, anywhere else anything
  (the values `Xv6.kptTextAt` gives at the graph);
* a register read is answered by every value the register filter `tvRk c` admits: `Rboot`, and
  `satp` is the kernel's `kSatp b` (Sv39, ASID 0, root `b`; kernel/riscv.h `MAKE_SATP`), and the
  `tlb` is `tlbIdOk` (every resident entry matching `vpn` at ASID 0 gives the identity ppn);
* a register write writes a `tvRk`-admitted value; every other node continues for every answer; a
  failure is stuck (`True`); at `.pure x`, `P x`.
§1 the filters and the predicate; §2 the kit: bind, monotonicity, pure, and the lift from the
`satp`/`tlb`-free footprint `PinFetchPaFp.xf` (its writes never touch the filtered registers).

Spec: Sail is the reference for the tree (`Vmem.lean`, `VmemTlb.lean`, `Fetch.lean`); the filters
are what the run (part (C)) and the graph (`kptTextAt`, W11) must deliver.  FAITHFUL (proof
organisation).  Every helper is `Weak.PinFetchPa.*`.
-/
import Weak.PinFetchPaFp
import MachCSL.PtTree
import MachCSL.KMap

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinFetchPa
open SailCycleOrderK PinFetchPaFp

/-! ## 1. The filters and the predicate -/

/-- The fetch translation's configuration: the three pages of the walk and the fetch's vpn. -/
structure TCfg where
  b : BitVec 44
  b1 : BitVec 44
  b0 : BitVec 44
  vpn : BitVec 27

/-- The kernel's `satp`: mode Sv39 (8), ASID 0, root page `b` (`MAKE_SATP`). -/
def kSatp (b : BitVec 44) : BitVec 64 := 8#4 ++ 0#16 ++ b

/-- **The TLB filter**: every resident entry that matches `vpn` at ASID 0 gives the identity ppn. -/
def tlbIdOk (vpn : BitVec 27) (tlb : Tlb) : Prop :=
  ∀ (i : Nat) (hi : i < 2 ^ 6) (ent : TLB_Entry), tlb[i] = some ent →
    match_TLB_Entry ent 0#16 (sign_extend (m := 45) vpn) = true → tlb_get_ppn 39 ent vpn = idPpn vpn

/-- The filtered registers' clause: `satp` is `kSatp b`, the `tlb` is `tlbIdOk`. -/
def tvFix (c : TCfg) (r : Register) (v : RegisterType r) : Prop :=
  (∀ h : r = .satp, cast (congrArg RegisterType h) v = kSatp c.b) ∧
  (∀ h : r = .tlb, tlbIdOk c.vpn (cast (congrArg RegisterType h) v))

/-- **The register filter**: boot-admitted, and the filtered registers' clause. -/
def tvRk (c : TCfg) (r : Register) (v : RegisterType r) : Prop := Rboot r v ∧ tvFix c r v

/-- **The PTE filter**: an 8-byte read at a walk slot answers the slot's value. -/
def tvAns (c : TCfg) (pa : BitVec 64) (n : Nat) (w : BitVec (8 * n)) : Prop :=
  n = 8 →
    (pa = pteAddr c.b (vpnIdx c.vpn 2) → w.toNat = (kPtr c.b1).toNat) ∧
    (pa = pteAddr c.b1 (vpnIdx c.vpn 1) → w.toNat = (kPtr c.b0).toNat) ∧
    (pa = pteAddr c.b0 (vpnIdx c.vpn 0) →
      ∃ a d : BitVec 1, w.toNat = (kLeaf (idPpn c.vpn) .rx a d).toNat)

/-- **THE FETCH-TRANSLATION VALUE PREDICATE** (header). -/
def tvB (c : TCfg) {X : Type} (P : X → Prop) : SailM X → Prop
  | .pure x => P x
  | .impure (.error _) _ => True
  | .impure (.ok o) k =>
    match o, k with
    | .memRead n _ req, k => ∀ w : BitVec (8 * n), tvAns c req.pa n w → tvB c P (k (.Ok (w, none)))
    | .instrAnnounce .., k => ∀ v, tvB c P (k v)
    | .regRead r, k => ∀ v, tvRk c r v → tvB c P (k v)
    | .regWrite r v, k => tvRk c r v ∧ ∀ u, tvB c P (k u)
    | .barrier _, k => ∀ v, tvB c P (k v)
    | .memWrite .., k => ∀ v, tvB c P (k v)
    | .branchAnnounce .., k => ∀ v, tvB c P (k v)
    | .cacheOp _, k => ∀ v, tvB c P (k v)
    | .tlbi _, k => ∀ v, tvB c P (k v)
    | .takeException _, k => ∀ v, tvB c P (k v)
    | .returnException _, k => ∀ v, tvB c P (k v)
    | .translationStart _, k => ∀ v, tvB c P (k v)
    | .translationEnd _, k => ∀ v, tvB c P (k v)
    | .cycleCount, k => ∀ v, tvB c P (k v)
    | .getCycleCount, k => ∀ v, tvB c P (k v)
    | .message _, k => ∀ v, tvB c P (k v)
    | .choose _, k => ∀ v, tvB c P (k v)
    | .readRam .., k => ∀ v, tvB c P (k v)
    | .writeRam .., k => ∀ v, tvB c P (k v)

/-- A `satp` answer is the kernel's. -/
theorem tvRkSatp {c : TCfg} {v : RegisterType .satp} (h : tvRk c .satp v) : v = kSatp c.b :=
  h.2.1 rfl

/-- A `tlb` answer is `tlbIdOk`. -/
theorem tvRkTlb {c : TCfg} {v : RegisterType .tlb} (h : tvRk c .tlb v) : tlbIdOk c.vpn v :=
  h.2.2 rfl

/-- A write the `satp`/`tlb`-free footprint admits is `tvRk`-admitted. -/
theorem tvRkOfW (c : TCfg) (r : Register) (v : RegisterType r) (h : xfW r v) : tvRk c r v := by
  refine ⟨h.1, fun hs => ?_, fun ht => ?_⟩
  · subst hs; exact absurd h.2 (by decide)
  · subst ht; exact absurd h.2 (by decide)

/-! ## 2. The kit -/

variable {c : TCfg}

theorem tvBind {X Y : Type} (Q : X → Prop) (P : Y → Prop) (m : SailM X) (f : X → SailM Y) :
    tvB c Q m → (∀ x, Q x → tvB c P (f x)) → tvB c P (m >>= f) := by
  induction m with
  | pure y => intro hm hf; exact hf y hm
  | impure call k ih =>
    intro hm hf
    cases call with
    | error e => trivial
    | ok o =>
      show tvB c P (FreeM.impure (.ok o) (fun v => k v >>= f))
      cases o
      case memRead => exact fun w hw => ih _ (hm w hw) hf
      case regRead => exact fun v hv => ih v (hm v hv) hf
      case regWrite => exact ⟨hm.1, fun u => ih u (hm.2 u) hf⟩
      all_goals exact fun v => ih v (hm v) hf

theorem tvMono {X : Type} (P P' : X → Prop) (hP : ∀ x, P x → P' x) :
    ∀ (m : SailM X), tvB c P m → tvB c P' m := by
  intro m
  induction m with
  | pure y => exact hP y
  | impure call k ih =>
    intro hm
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case memRead => exact fun w hw => ih _ (hm w hw)
      case regRead => exact fun v hv => ih v (hm v hv)
      case regWrite => exact ⟨hm.1, fun u => ih u (hm.2 u)⟩
      all_goals exact fun v => ih v (hm v)

theorem tvPure {X : Type} (P : X → Prop) (x : X) : P x → tvB c P (pure x : SailM X) := fun h => h

/-- **The lift**: a `satp`/`tlb`-free footprint tree satisfies the value predicate with its post. -/
theorem tvOfXf {X : Type} (S : X → Prop) : ∀ (m : SailM X), xf S m → tvB c S m := by
  intro m
  induction m with
  | pure y => intro h; exact h
  | impure call k ih =>
    intro hm
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case memRead n va req => exact fun w _ => ih _ (hm.2 _)
      case instrAnnounce => exact hm.elim
      case barrier => exact fun v => ih v hm.2
      case regRead r => exact fun v hv => ih v (hm v hv.1)
      case regWrite r v => exact ⟨tvRkOfW c r v hm.1, fun u => ih u (hm.2 u)⟩
      all_goals exact fun v => ih v (hm v)

/-- A footprint head of a bind. -/
theorem tvXfBind {X Y : Type} (S : X → Prop) (P : Y → Prop) (m : SailM X) (f : X → SailM Y)
    (hm : xf S m) (hf : ∀ x, S x → tvB c P (f x)) : tvB c P (m >>= f) :=
  tvBind S P m f (tvOfXf S m hm) hf

end PinFetchPa
end Weak
