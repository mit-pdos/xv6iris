/-
Weak: **r2 glue (ii) — `fetch ()` takes no fault** (`PROGRESS-r2glue.md`).  Lean-only.

`dk2B c1 c2 pc P m`: the data-access value predicate at TWO fetch configurations (`c1` for `PC`,
`c2` for `PC + 2`): register reads answered by values both `dG c1` and `dG c2` admit, `PC` by `pc`,
`misa` by the kernel's (both justified by the mirror at the product: protected registers), memory
reads by both `dAns`, a memory write `.Ok (some true)`.  Headline `dkFetchOk`: at an even kernel-text
`pc`, `fetch ()` (`Fetch.lean:233-288`) answers neither `F_Error` nor `F_Ext_Error` — the alignment
checks pass (`pc` even, `Zca` on: `misa.C`), each `fetch_bytes` succeeds (`dkFetchBytesOk`).
Every helper is `Weak.PinDataOk.*`.
-/
import Weak.PinDataOkIF
import Weak.PinFetchPaFqF

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinDataOk
open SailCycleOrderK PinCycRun

/-- The kernel's `misa` (`kCfg`). -/
def kMisa : BitVec 64 := 0x8000000000141105#64

/-- The two configurations' register filter, with `PC = pc` and the kernel's `misa`. -/
def dG2 (c1 c2 : DCfg) (pc : Int) (r : Register) (v : RegisterType r) : Prop :=
  dG c1 r v ∧ dG c2 r v ∧ (∀ h : r = .PC, cast (congrArg RegisterType h) v = BitVec.ofInt 64 pc) ∧
  (∀ h : r = .misa, cast (congrArg RegisterType h) v = kMisa)

/-- **THE TWO-CONFIGURATION ACCESS PREDICATE** (header). -/
def dk2B (c1 c2 : DCfg) (pc : Int) {X : Type} (P : X → Prop) : SailM X → Prop
  | .pure x => P x
  | .impure (.error _) _ => True
  | .impure (.ok o) k =>
    match o, k with
    | .memRead n _ req, k =>
        ∀ w : BitVec (8 * n), dAns c1 req.pa n w → dAns c2 req.pa n w → dk2B c1 c2 pc P (k (.Ok (w, none)))
    | .memWrite .., k => dk2B c1 c2 pc P (k (.Ok (some true)))
    | .regRead r, k => ∀ v, dG2 c1 c2 pc r v → dk2B c1 c2 pc P (k v)
    | .regWrite _ _, k => ∀ u, dk2B c1 c2 pc P (k u)
    | .instrAnnounce .., k => ∀ v, dk2B c1 c2 pc P (k v)
    | .barrier _, k => ∀ v, dk2B c1 c2 pc P (k v)
    | .branchAnnounce .., k => ∀ v, dk2B c1 c2 pc P (k v)
    | .cacheOp _, k => ∀ v, dk2B c1 c2 pc P (k v)
    | .tlbi _, k => ∀ v, dk2B c1 c2 pc P (k v)
    | .takeException _, k => ∀ v, dk2B c1 c2 pc P (k v)
    | .returnException _, k => ∀ v, dk2B c1 c2 pc P (k v)
    | .translationStart _, k => ∀ v, dk2B c1 c2 pc P (k v)
    | .translationEnd _, k => ∀ v, dk2B c1 c2 pc P (k v)
    | .cycleCount, k => ∀ v, dk2B c1 c2 pc P (k v)
    | .getCycleCount, k => ∀ v, dk2B c1 c2 pc P (k v)
    | .message _, k => ∀ v, dk2B c1 c2 pc P (k v)
    | .choose _, k => ∀ v, dk2B c1 c2 pc P (k v)
    | .readRam .., k => ∀ v, dk2B c1 c2 pc P (k v)
    | .writeRam .., k => ∀ v, dk2B c1 c2 pc P (k v)

section kit
variable {c1 c2 : DCfg} {pc : Int}

theorem dk2Bind {X Y : Type} (Q : X → Prop) (P : Y → Prop) (m : SailM X) (f : X → SailM Y) :
    dk2B c1 c2 pc Q m → (∀ x, Q x → dk2B c1 c2 pc P (f x)) → dk2B c1 c2 pc P (m >>= f) := by
  induction m with
  | pure y => intro hm hf; exact hf y hm
  | impure call k ih =>
    intro hm hf
    cases call with
    | error e => trivial
    | ok o =>
      show dk2B c1 c2 pc P (FreeM.impure (.ok o) (fun v => k v >>= f))
      cases o
      case memRead => exact fun w h1 h2 => ih _ (hm w h1 h2) hf
      case memWrite => exact ih _ hm hf
      case regRead => exact fun v hv => ih v (hm v hv) hf
      all_goals exact fun v => ih v (hm v) hf

/-- The lift from one configuration's `dkB`. -/
theorem dk2OfDk (c : DCfg) (hc : c = c1 ∨ c = c2) {X : Type} (P : X → Prop) :
    ∀ (m : SailM X), dkB c P m → dk2B c1 c2 pc P m := by
  intro m
  induction m with
  | pure y => intro h; exact h
  | impure call k ih =>
    intro hm
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case memRead => exact fun w h1 h2 => ih _ (hm w (by rcases hc with rfl | rfl <;> assumption))
      case memWrite => exact ih _ hm
      case regRead => exact fun v hv => ih v (hm v (by rcases hc with rfl | rfl; exact hv.1; exact hv.2.1))
      all_goals exact fun v => ih v (hm v)

theorem dk2XfBind {X Y : Type} (S : X → Prop) (P : Y → Prop) (m : SailM X) (f : X → SailM Y)
    (hm : PinFetchPaFp.xf S m) (hf : ∀ x, S x → dk2B c1 c2 pc P (f x)) : dk2B c1 c2 pc P (m >>= f) :=
  dk2Bind S P m f (dk2OfDk c1 (Or.inl rfl) S m (dkOfXf S m hm)) hf

theorem dk2ReadPC {Y : Type} (P : Y → Prop) (f : BitVec 64 → SailM Y)
    (h : dk2B c1 c2 pc P (f (BitVec.ofInt 64 pc))) : dk2B c1 c2 pc P (readReg .PC >>= f) := by
  intro v hv
  have e : v = BitVec.ofInt 64 pc := hv.2.2.1 rfl
  subst e
  exact h

theorem dk2Leaf {X : Type} (P : X → Prop) (x : X) (h : P x) : dk2B c1 c2 pc P (pure x) := h

set_option maxHeartbeats 4000000 in
/-- `Zca` is on (the kernel's `misa.C`). -/
theorem dk2Zca {Y : Type} (P : Y → Prop) (f : Bool → SailM Y) (h : dk2B c1 c2 pc P (f true)) :
    dk2B c1 c2 pc P (currentlyEnabled .Ext_Zca >>= f) := by
  have hz : hartSupports .Ext_Zca = true := by decide +kernel
  have hc : hartSupports .Ext_C = true := by decide +kernel
  simp only [currentlyEnabled, hz, hc, ↓reduceIte, bind_assoc]
  intro v hv
  have e : v = kMisa := hv.2.2.2 rfl
  subst e
  exact h

end kit

/-- The fetch's answer is neither a fault nor an extension error. -/
def frNoFault (fr : FetchResult) : Prop :=
  match fr with
  | .F_Error _ => False
  | .F_Ext_Error _ => False
  | _ => True

/-- The four-byte arm after its `PC` reads. -/
macro "dk_arm4" c1:term:max hr1:term:max hp1:term:max hva1:term:max hv1:term:max hal:term:max : tactic =>
  `(tactic| (
  refine dk2Bind _ _ _ _ (dk2OfDk $c1 (Or.inl rfl) _ _
    (dkFetchBytesOk $c1 $hr1 $hp1 _ _ 4 (Or.inr rfl) $hva1 $hv1 $hal)) (fun r hr => ?_)
  cases r with
  | FetchBytes_Ext_Error e => exact hr.elim
  | FetchBytes_Exception e => exact hr.elim
  | FetchBytes_Success b =>
    simp only []
    split <;> exact trivial))

/-- The two-byte arm after its `PC` reads. -/
macro "dk_arm2" c1:term:max hr1:term:max hp1:term:max hva1:term:max hv1:term:max hal1:term:max
    c2:term:max hr2:term:max hp2:term:max hva2:term:max hv2:term:max hal2:term:max : tactic =>
  `(tactic| (
  refine dk2Bind _ _ _ _ (dk2OfDk $c1 (Or.inl rfl) _ _
    (dkFetchBytesOk $c1 $hr1 $hp1 _ _ 2 (Or.inl rfl) $hva1 $hv1 $hal1)) (fun r hr => ?_)
  cases r with
  | FetchBytes_Ext_Error e => exact hr.elim
  | FetchBytes_Exception e => exact hr.elim
  | FetchBytes_Success b =>
    simp only []
    split
    · exact trivial
    · simp only [ExceptT.run_bind, run_liftM, bind_assoc, ExceptT.run_pure, pure_bind]
      refine dk2ReadPC _ _ (dk2ReadPC _ _ ?_)
      refine dk2Bind _ _ _ _ (dk2OfDk $c2 (Or.inr rfl) _ _
        (dkFetchBytesOk $c2 $hr2 $hp2 _ _ 2 (Or.inl rfl) $hva2 $hv2 $hal2)) (fun r hr => ?_)
      cases r with
      | FetchBytes_Ext_Error e => exact hr.elim
      | FetchBytes_Exception e => exact hr.elim
      | FetchBytes_Success b' => exact trivial))

set_option maxHeartbeats 40000000 in
/-- **THE FETCH TAKES NO FAULT** (header). -/
theorem dkFetchOk (c1 c2 : DCfg) (pc : Int) (h0 : 0 ≤ pc) (hlt : pc + 2 < 2 ^ 38) (hev : pc % 2 = 0)
    (hr1 : c1.ram) (hp1 : c1.perm = .rx) (hv1 : c1.vpn = vpnOf (BitVec.ofInt 64 pc))
    (hr2 : c2.ram) (hp2 : c2.perm = .rx) (hv2 : c2.vpn = vpnOf (BitVec.addInt (BitVec.ofInt 64 pc) 2)) :
    dk2B c1 c2 pc frNoFault (fetch ()) := by
  have ht1 := PinFetchPa.toNatOfInt pc h0 (by omega)
  have ht2 := PinFetchPa.toNatOfInt2 pc h0 (by omega)
  have hva1 : (BitVec.ofInt 64 pc).toNat < 2 ^ 38 := by omega
  have hva2 : (BitVec.addInt (BitVec.ofInt 64 pc) 2).toNat < 2 ^ 38 := by omega
  have hal1 : (BitVec.ofInt 64 pc).toNat % 2 = 0 := by omega
  have hal2 : (BitVec.addInt (BitVec.ofInt 64 pc) 2).toNat % 2 = 0 := by omega
  have hb0 : (BitVec.access (BitVec.ofInt 64 pc) 0 != 0#1) = false := by
    generalize BitVec.ofInt 64 pc = x at hal1
    have hx : x.getLsbD 0 = false := by
      rw [BitVec.getLsbD, Nat.testBit_zero]; simp only [decide_eq_false_iff_not]; omega
    simp only [BitVec.access, bne_eq_false_iff_eq]
    have e : x[0]! = x.getLsbD 0 := by simp [BitVec.getLsbD_eq_getElem]
    rw [e, hx]; rfl
  have hal4 : ∀ h : is_aligned_vaddr (virtaddr.Virtaddr (BitVec.ofInt 64 pc)) 4 = true,
      (BitVec.ofInt 64 pc).toNat % 4 = 0 := by
    intro h
    simp only [is_aligned_vaddr, BitVec.toNatInt, beq_iff_eq] at h
    rw [Int.ofNat_eq_natCast, ← Int.ofNat_tmod] at h
    omega
  simp only [fetch, ext_fetch_check_pc, get_config_rvfi, SailME.run, PreSail.PreSailME.run,
    ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, Bool.false_eq_true, ↓reduceIte]
  refine dk2ReadPC _ _ ?_
  refine dk2ReadPC _ _ ?_
  refine dk2ReadPC _ _ ?_
  refine dk2Bind (fun r => match r with
    | .ok x => frNoFault x | .error (.inr x) => frNoFault x | .error (.inl _) => True) _ _ _ ?_ ?_
  rotate_left
  · intro r hr
    rcases r with (e | e) | e
    · exact trivial
    · exact hr
    · exact hr
  simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, ExceptT.run_pure,
    PinFetchVal.runIte, PinFetchVal.iteBind, Bool.false_eq_true, ↓reduceIte, hb0]
  refine dk2ReadPC _ _ ?_
  try simp only []
  split
  · refine dk2Zca _ _ ?_
    simp only [Functions.not, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine dk2ReadPC _ _ ?_
    try simp only []
    split
    · next ha =>
      refine dk2XfBind _ _ _ _ (PinFetchPaFp.xfCurrentlyEnabled _) (fun _ _ => ?_)
      split
      · refine dk2ReadPC _ _ (dk2ReadPC _ _ ?_)
        dk_arm4 c1 hr1 hp1 hva1 hv1 (hal4 ha)
      · refine dk2ReadPC _ _ (dk2ReadPC _ _ ?_)
        dk_arm2 c1 hr1 hp1 hva1 hv1 hal1 c2 hr2 hp2 hva2 hv2 hal2
    · refine dk2ReadPC _ _ (dk2ReadPC _ _ ?_)
      dk_arm2 c1 hr1 hp1 hva1 hv1 hal1 c2 hr2 hp2 hva2 hv2 hal2
  · refine dk2ReadPC _ _ ?_
    try simp only []
    split
    · next ha =>
      refine dk2XfBind _ _ _ _ (PinFetchPaFp.xfCurrentlyEnabled _) (fun _ _ => ?_)
      split
      · refine dk2ReadPC _ _ (dk2ReadPC _ _ ?_)
        dk_arm4 c1 hr1 hp1 hva1 hv1 (hal4 ha)
      · refine dk2ReadPC _ _ (dk2ReadPC _ _ ?_)
        dk_arm2 c1 hr1 hp1 hva1 hv1 hal1 c2 hr2 hp2 hva2 hv2 hal2
    · refine dk2ReadPC _ _ (dk2ReadPC _ _ ?_)
      dk_arm2 c1 hr1 hp1 hva1 hv1 hal1 c2 hr2 hp2 hva2 hv2 hal2

end PinDataOk
end Weak
