/-
Weak: **PHASE 5, stage 3: THE POSITIONAL LOAD LEAF INTERFACE `XLd`** for holding's two SHARED
loads (`lk->locked`, `lk->cpu`), and its instance `XxLdO` from ANY flow resource (`FldM`) at the
joint instance Ixv6.

Rocq: `iris/AxSpinHd7.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`XLd k pc rs1 rd imm w vb Out` (an iProp: it may own resources, e.g. a holder's claim
annotation): from any boundary at row position `k` at `pc` (regime, warm TLB on the text page and
on the data VA `vb + imm`, base register `rs1` = `vb`), the compressed plain load
`LOAD (imm, rs1, rd, false, w)` hands its continuation the boundary after the load with
`rd := ldRes false w vs` (`GoodB`), the read's graph value `vs` and the CALLER'S output `Out vs`.
This is the CALLER-INDEXED slot: `AxSpinHdA.wpd_holding` is stated over two such leaves, and each
call site supplies the read rule its protocol position allows (AxSpinHdB).

`XxLdO`: `XLd` from a flow resource `FldM (dokAt pa w) i Out` over `AxSpinE4.XBk` +
`AxSpinE2.CertBLoadS` (the `AxSpinE6.XxLd` script with the private slot rule replaced by the
parameter).  Its premises are the engine's: the data translation (`dataAtS`), the address is not
fetch region, and THE ENGINE'S GLOBAL no-RMW PREMISE `Hnormw` (no RMW row item of hart `i`, at ANY
position, at the read's address and width).  `Hnormw` is satisfiable for `lk->cpu` but FALSE for
the lock word on any row containing acquire's `amoswap.w.aq lk` (the positional variant with the
premise only at the data slot is `AxSpinXP.XxLdP`).  Also here: `dflowOMono`, `FldMRow` (a flow
resource can always add the row/graph facts it is handed to its output).

## Deviations from Rocq

1. O2 STAGE C COUNT SHIFT (`AxSpinE4` deviation 1, as `AxSpinE6.XxLd` / `AxSpinXP.XxLdP`): the
   instruction's fetch consumes NO row item.  The load's data event is AT `k` (Rocq `k + 1`):
   `XLd`'s continuation gets `graphValue GD0 (i, k)` and is at `k + 1` (Rocq `k + 2`), its
   premise is `k + 1 ≤ LEN` (Rocq `k + 2 ≤ LEN`), and `XxLdO` concludes `XLd … (Out k)` (Rocq
   `Out (S k)`).  Rocq's fetch premise `Hnrk` (the row item at `k`, the fetch, is not a read of
   `w` bytes) is DROPPED: under Stage C row item `k` IS the load's data read, so the premise
   would be unsatisfiable; its one use (ruling out `kd = k`) is now arithmetic.  Rocq's `Hntext`
   assertion is not built (`XBk` does not take it); the premise `¬ L.xlText (paZ pa)` is kept
   for caller compatibility and is unused.
2. TYPES / INSTANCES (as `AxSpinXP` deviation 2): `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]`
   (any `hlc`); `xv6G Σ` ↦ `[AxSpinX.Xv6G GF]`; the local instances `h7_pol := e_pol GT` /
   `h7_G := e_G L GT nm` are inlined as `xv6Pol GT` / `AxSpinX2.xG L GT nm` (as `AxSpinE6`),
   passed with `@`.  `Z` widths ↦ `Nat` (`Z.to_nat w` ↦ `w`, `(1 ≤ w ≤ 8)%Z` ↦ `1 ≤ w → w ≤ 8`),
   `uint pa` ↦ `paZ pa`, `uint rd ≠ 0` ↦ `rd.toNat ≠ 0`, `add_vec vb (sign_extend' 64 imm)` ↦
   `vb + sign_extend (m := 64) imm`, `register_lookup PC rs` ↦ `rs .PC`, `l !! k` ↦ `l[k]?`.
   Section variables are explicit arguments: `XLd L GT nm T satp0 i cpu Ψ`, `dflowOMono L GT nm
   i`, `OutR GT i`, `FldMRow L GT nm i`; `XxLdO` takes
   `L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid` first.
3. The trailing `Print Assumptions` line is not ported (the lint's axiom check covers it).

**Rocq → Lean name map.**  `dok_at` `dokAt`, `vw4` `AxSpinHd7.vw4` (duplicated name: also
AxSpinPOx), `XLd` `XLd`, `dflowO_mono` `dflowOMono`, `OutR` `OutR`, `FldM_row` `FldMRow`,
`Xx_ldO` `XxLdO`.  No Lean-only declarations.

**Dropped:** nothing (Rocq 7 definitions/lemmas + the 2 local instances `h7_pol` / `h7_G`,
inlined; Lean 7).
-/
import Weak.AxSpinE6

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `dok_at`. -/
def dokAt (pa : Int) (n : Nat) : Int → Nat → Prop := fun b m => b = pa ∧ m = n

/-- Rocq `vw4` (duplicated name: file-qualified). -/
theorem AxSpinHd7.vw4 : vmemWidth 4 := Or.inr (Or.inr (Or.inl rfl))

section ldO
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

/-- Rocq `XLd`: THE CALLER-INDEXED LOAD SLOT (deviation 1: data event at `k`, continuation at
`k + 1`). -/
def XLd (L : Xlay) (GT : GdexecT) (nm : Xv6N) (T : PTree) (satp0 : BitVec 64) (i : Agent)
    (cpu : CPU) (Ψ : Athread → IProp GF) (k : Nat) (pc : BitVec 64) (rs1 rd : BitVec 5)
    (imm : BitVec 12) (w : Nat) (vb : BitVec 64) (Out : List (BitVec 8) → IProp GF) :
    IProp GF :=
  iprop(∀ (s : Athread) (rs : RegFile),
    ⌜RetX cpu rs k s ∧ ctrlOkSW T satp0 rs ∧ rs .PC = pc ∧ hitW rs pc ∧
      gprVal rs rs1 = vb ∧ hitW rs (vb + sign_extend (m := 64) imm) ∧
      k + 1 ≤ (AxOpsem.grow (gtAdGd GT) i).length⌝ -∗
    (∀ (vs : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch), ⌜vs.length = w⌝ -∗
      ⌜GoodB T satp0 rs pc true none (some (rd, ldRes false w vs)) rs'⌝ -∗
      ⌜graphValue (gtAdGd GT) (i, k) = some vs⌝ -∗ Out vs -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs' none ib', k + 1⟩ Ψ) -∗
    @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ)

/-- Rocq `dflowO_mono`. -/
theorem dflowOMono (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent) (GD : Gdexec) (k : Nat)
    (O O' : IProp GF) :
    ⊢ (O -∗ O') -∗ @dflowO hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) i GD k O -∗
      @dflowO hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) i GD k O' := by
  iintro HOO F
  unfold dflowO
  iintro %na Hna
  imod F $$ %na Hna with F
  imodintro
  inext
  imod F with ⟨%R, %nu, %nuu, %ls', Hs, Hfe, Hna, Hl, HO⟩
  imodintro
  iexists R, nu, nuu, ls'
  isplitl [Hs]
  · iexact Hs
  isplitl [Hfe]
  · iexact Hfe
  isplitl [Hna]
  · iexact Hna
  isplitl [Hl]
  · iexact Hl
  iapply HOO $$ HO

/-- Rocq `OutR`: the output plus the row / graph facts the flow resource is handed. -/
def OutR (GT : GdexecT) (i : Agent) (pa : Int) (n : Nat)
    (Out : Nat → List (BitVec 8) → IProp GF) (k : Nat) (v : List (BitVec 8)) : IProp GF :=
  iprop(⌜graphValue (gtAdGd GT) (i, k) = some v ∧
    ∃ lb aq, (AxOpsem.grow (gtAdGd GT) i)[k]? = some lb ∧
      aidentRd (aident lb) = some (aq, pa, n)⌝ ∗ Out k v)

/-- Rocq `FldM_row`. -/
theorem FldMRow (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent) (pa : Int) (n : Nat)
    (Out : Nat → List (BitVec 8) → IProp GF) :
    ⊢ @FldM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAt pa n) i Out -∗
      @FldM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAt pa n) i
        (OutR GT i pa n Out) := by
  iintro F
  unfold FldM
  iintro %GD %ls %k %v %base %n' %Hc #Hg Hloc %Hgv %Hd
  ihave %Heq := (HGX L GT nm GD Hc) $$ Hg
  subst Heq
  obtain ⟨⟨rfl, rfl⟩, Hrd⟩ := Hd
  ihave F2 := F $$ %(gtAdGd GT) %ls %k %v %base %n' %Hc Hg Hloc %Hgv %⟨⟨rfl, rfl⟩, Hrd⟩
  iapply (dflowOMono L GT nm i (gtAdGd GT) k _ _) $$ [] F2
  iintro HO
  unfold OutR
  isplitr
  · ipureintro
    exact ⟨Hgv, Hrd⟩
  · iexact HO

/-- Rocq `Xx_ldO`: `XLd` from a flow resource (deviation 1: data event at `k`, `Out k`; Rocq's
fetch premise `Hnrk` is dropped). -/
theorem XxLdO (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (i : Agent) (cpu : CPU) (Hfix : textFixed (gtAdGd GT) i (imgS σi))
    (Ψ : Athread → IProp GF)
    (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
      ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)
    (k : Nat) (pc : BitVec 64) (imm : BitVec 12) (rs1 rd : BitVec 5) (w : Nat)
    (vb pa : BitVec 64) (Out : Nat → List (BitVec 8) → IProp GF) :
    textOkB σi T satp0 pc true (.LOAD (imm, .Regidx rs1, .Regidx rd, false, w)) →
    rd.toNat ≠ 0 → vmemWidth w → 1 ≤ w → w ≤ 8 →
    dataAtS σi T (.Load .Data) (vb + sign_extend (m := 64) imm) w pa →
    ¬ L.xlText (paZ pa) →
    (∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (n : Nat), (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb →
      aident lb = .IRmw aq rl (paZ pa) n → n ≠ w) →
    ⊢ @FldM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAt (paZ pa) w) i
        Out -∗
      XLd (hlc := hlc) L GT nm T satp0 i cpu Ψ k pc rs1 rd imm w vb (Out k) := by
  intro Htx hrd hvw hw1 hw8 hda _ Hnormw
  have HnoRmw : Dkind.DKLd = .DKLd → ∀ GD, rvwmoCatConsistent GD →
      @AxirisG.gconstInterp GF (AxSpinX2.xG L GT nm) GD ⊢
      ⌜∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat),
        (AxOpsem.grow GD i)[k']? = some lb → aident lb = .IRmw aq rl base n →
        ¬ dokAt (paZ pa) w base n⌝ := by
    intro _ GD Hc'
    iintro Hg
    ihave %Heq := (HGX L GT nm GD Hc') $$ Hg
    subst Heq
    ipureintro
    rintro k' lb aq rl base n Hlb Hid ⟨rfl, rfl⟩
    exact Hnormw k' lb aq rl _ Hlb Hid rfl
  iintro F
  unfold XLd
  iintro %s %rs %Hpre C
  obtain ⟨HRet, Hc, HPC, Hhit, Hvb, Hhv, Hle⟩ := Hpre
  have H := @XBk hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) σi T satp0 hmode hasid hppn i cpu
    (fun GD => GD = gtAdGd GT) (HGX L GT nm) (AxOpsem.grow (gtAdGd GT) i).length (HL0 GT i)
    (HGex0 GT) Ψ (AxSpinE6.Hmid0 L GT nm i Ψ HΨmid) (HtextX L GT nm (imgS σi) i Hfix)
    (HflowX L GT nm HL Hcons (imgS σi) i) (HlocX L GT nm i)
    (dokAt (paZ pa) w) .DKLd HnoRmw (by intro h; cases h) (OutR GT i (paZ pa) w Out)
    s rs k pc true _ 1 none (owLdB rd false w) .CPend false
    (fun d r' => ∃ vs, d = .CLd vs ∧ vs.length = w ∧ r' = false)
    HRet Hc HPC Hhit Htx (by rintro d r ⟨vs, rfl, -, -⟩; exact hrd)
    (CertBLoadS σi T satp0 hmode hasid hppn (dokAt (paZ pa) w) rs pc true imm rs1 rd false w
      (vb + sign_extend (m := 64) imm) pa false hrd hvw hw1 hw8 (by rw [Hvb]) hda Hhv ⟨rfl, rfl⟩)
    (by omega) (by omega)
  iapply H $$ [F] [C]
  · simp only [CResK, CFkM]
    iapply (FldMRow L GT nm i (paZ pa) w Out)
    iexact F
  · iintro %d %r %rs' %ib' %HPX %HGB HO
    obtain ⟨vs, rfl, Hvs, rfl⟩ := HPX
    simp only [CResK]
    icases HO with ⟨%kd, %Hkd, HO⟩
    obtain rfl : kd = k := by omega
    unfold OutR
    icases HO with ⟨%Hgv, HO⟩
    iapply C $$ %vs %rs' %ib' %Hvs %HGB %Hgv.1 HO

end ldO

end Weak
