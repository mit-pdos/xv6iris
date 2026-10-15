/-
Weak: **r2 glue (C) — THE FETCH IN THE CYCLE PREDICATE** (`PROGRESS-r2glue.md`).  Lean-only.

`cyFOfPfFq` is the product of two walks of the same Sail text: w1's relaxed frame footprint `pfB
true` (no protected register written — `PC` among them — `Rboot` writes) and the fetch-address
predicate `fqB` (reads answered by `tvRk c` / `PC = pc`, its writes `tvRk c`-admitted, the `k`-th
fetch read at `pc + 2k`).  Along the product the MIRROR justifies `fqB`'s read filter: `PC` is kept
(protected), every register `tvRk c`-admitted (`tvRkAll`, kept by `fqB`'s writes), and the fetch
log's length is the count.  Headline `cyFFetch`: `fetch ()` under `cyFB` with the obligation
`kAa pc` discharged, from w1's `pfFetch` and our `fqFetch`.  Every helper is `Weak.PinFetchPa.*`.
-/
import Weak.PinFetchPaFqF
import Weak.PinCycRunFetch

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinFetchPa
open SailCycleOrderK PinCycRun PinDataflow
open PinCycRunFp (pfB pfProt pfRegOk pfW)

/-- The fetch's mirror invariant relative to its start `st0`, at count `i`. -/
def fxInv (c : TCfg) (pc : Int) (st0 st : CySt) (i : Nat) : Prop :=
  (∀ r, pfProt r = true → st.rv r = st0.rv r) ∧ tvRkAll c st.rv ∧ st.fe.length = i ∧
  st.an = st0.an ∧ st.rv .PC = BitVec.ofInt 64 pc

theorem fxRd (c : TCfg) (pc : Int) (st0 st : CySt) (i : Nat) (r : Register) (h : fxInv c pc st0 st i) :
    fxInv c pc st0 (cyRd st r) i := h

/-- A mirror read is `tvRk c`-admitted (a wire register: `Rboot`, never `satp`/`tlb`). -/
theorem tvRkOfRd (c : TCfg) (st : CySt) (r : Register) (v : RegisterType r) (hall : tvRkAll c st.rv)
    (hv : PinCycRun.rdOk st r v) : tvRk c r v := by
  cases hw : wireReg r
  · rw [hv hw]; exact hall r
  · unfold wireReg at hw
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hw
    rcases hw with rfl | rfl <;>
      exact ⟨trivial, (⟨fun h => (by cases h), fun h => (by cases h)⟩ : tvFix c _ v)⟩

section prod
variable (c : TCfg) (D : BitVec 64 → (n : Nat) → BitVec (8 * n) → Prop) (pc : Int) (st0 : CySt)

set_option maxHeartbeats 4000000 in
/-- **THE PRODUCT** (header). -/
theorem cyFOfPfFq {X : Type} (P : X → Nat → Prop) (S : X → Prop) (Q : X → CySt → Prop) :
    ∀ (m : SailM X) (st : CySt) (i : Nat), pfB true S m → fqB c D pc P m i → fxInv c pc st0 st i →
      (∀ x st' i', P x i' → S x → fxInv c pc st0 st' i' → Q x st') →
      cyFB D (kAa pc) Q m st := by
  intro m
  induction m with
  | pure x => intro st i hp hq hi hk; exact hk x st i hq hp hi
  | impure call k ih =>
    intro st i hp hq hi hk
    obtain ⟨hpr, hall, hlen, han, hpc⟩ := hi
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead r =>
        intro v hv
        have ht := tvRkOfRd c st r v hall hv
        have hP : ∀ h : r = .PC, cast (congrArg RegisterType h) v = BitVec.ofInt 64 pc := by
          intro h
          subst h
          rw [hv (by decide)]
          exact hpc
        exact ih v (cyRd st r) i (hp v ht.1) (hq v ht hP) ⟨hpr, hall, hlen, han, hpc⟩ hk
      case regWrite r v =>
        obtain ⟨⟨hb, hok⟩, hkp⟩ := hp
        obtain ⟨ht, hkq⟩ := hq
        have hpf : pfProt r = false := by simpa [pfRegOk] using hok
        refine ⟨hb, fun u => ih u (cyWr st r v) i (hkp u) (hkq u) ⟨fun r' h' => ?_,
          tvRkAllSet _ r v hall ht, hlen, han, ?_⟩ hk⟩
        · have e : r' ≠ r := by rintro rfl; rw [hpf] at h'; cases h'
          show (st.rv.set r v) r' = _
          rw [RegFile.set_other _ _ _ _ e]; exact hpr r' h'
        · have e : Register.PC ≠ r := by rintro rfl; cases hpf
          show (st.rv.set r v) .PC = _
          rw [RegFile.set_other _ _ _ _ e]; exact hpc
      case memRead n va req =>
        refine ⟨fun hdev hif => ?_, fun h w hd => ?_⟩
        · obtain ⟨-, ha, hkq⟩ := hq.1 hif
          refine ⟨?_, fun w _ => ih _ (cyFe st (paZ req.pa) n w) (i + 1) (hp.2 _) (hkq w)
            ⟨hpr, hall, ?_, han, hpc⟩ hk⟩
          · show paZ req.pa = pc + 2 * (st.fe.length : Int)
            rw [hlen]; exact ha
          · simp [cyFe, hlen]
        · cases hif : (classify req.access_kind).akIfetch with
          | false => exact ih _ st i (hp.2 _) (hq.2 hif w hd) ⟨hpr, hall, hlen, han, hpc⟩ hk
          | true =>
            have := h (hq.1 hif).1
            rw [hif] at this; cases this
      case instrAnnounce => exact hq.elim
      case barrier b => exact fun v => ih v st i hp.2 (hq v) ⟨hpr, hall, hlen, han, hpc⟩ hk
      case memWrite => exact ih _ st i (hp _) (hq _) ⟨hpr, hall, hlen, han, hpc⟩ hk
      case getCycleCount => exact ih _ st i (hp _) (hq _) ⟨hpr, hall, hlen, han, hpc⟩ hk
      all_goals exact fun v => ih v st i (hp v) (hq v) ⟨hpr, hall, hlen, han, hpc⟩ hk

end prod

/-- The fetch's post in the cycle: never an extension error, the protected mirror and the flag
kept, the mirror `Rboot`-admitted. -/
def fetchPostF (st : CySt) (fr : FetchResult) (st' : CySt) : Prop :=
  PinCycRunFp.PinCycRunFetch.frOk fr ∧ (∀ r, pfProt r = true → st'.rv r = st.rv r) ∧
  st'.an = st.an ∧ RbootAll st'.rv

/-- **THE FETCH IN THE CYCLE** (header): from an empty log at `PC = pc`, every register
`tvRk c`-admitted, the fetch's two configurations given, `fetch ()` satisfies `cyFB` with its
address obligation `kAa pc` discharged. -/
theorem cyFFetch (c : TCfg) (D : BitVec 64 → (n : Nat) → BitVec (8 * n) → Prop) (pc : Int)
    (h0 : 0 ≤ pc) (hlt : pc + 2 < 2 ^ 64) (c1 c2 : TCfg)
    (hc1 : fqCfg c D (BitVec.ofInt 64 pc) c1) (hc2 : fqCfg c D (BitVec.addInt (BitVec.ofInt 64 pc) 2) c2)
    (st : CySt) (hfe : st.fe = []) (hpc : st.rv .PC = BitVec.ofInt 64 pc) (hall : tvRkAll c st.rv) :
    cyFB D (kAa pc) (fetchPostF st) (fetch ()) st :=
  cyFOfPfFq c D pc st (fun _ _ => True) _ _ (fetch ()) st 0 PinCycRunFp.PinCycRunFetch.pfFetch
    (fqFetch pc h0 hlt c1 c2 hc1 hc2) ⟨fun _ _ => rfl, hall, by rw [hfe]; rfl, rfl, hpc⟩
    (fun fr st' _ _ hok hi => ⟨hok, hi.1, hi.2.2.2.1, fun r => (hi.2.1 r).1⟩)

end PinFetchPa
end Weak
