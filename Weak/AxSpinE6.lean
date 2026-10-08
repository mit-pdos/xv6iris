/-
Weak: **PHASE 5 POSITIONAL ENGINE, part 6: the positional leaves at Ixv6** that `mycpu` needs,
and the c.ret leaf.

Rocq: `iris/AxSpinE6.v` @ xxvzwolszwmp.

## The Rocq header, in substance

All leaves are at the joint instance (`AxSpinX2.xG L GT nm`, policy `xv6Pol GT`) over the pinned
graph `gtAdGd GT`, S-mode data regime `ctrlOkSW`, WARM TLB (`hitW`), any postcondition `Ψ` that
is trivial at mid-instruction row ends (`HΨmid`).  Each reports the EXACT continuation position:
`XxReg` (register-only / control, `CertC` + `rfF`), `XxSt` (store to hart `i`'s private 8-byte
slot; the continuation learns `graphData` = the stored bytes), `XxLd` (RELOAD of the slot spilled
at `kw`; the continuation learns `graphValue` and holds the annotation "reload bytes = spill's row
bytes"), `XxRet` (c.ret = `c.jr ra`).  `vaCanon`/`vaRd` are Rocq's canonical-VA first-read
vocabulary (kept as faithful definitions; their consumer `va_first_read` is dropped, below).

## Deviations from Rocq

1. TYPES: `uint (fetch_pa pte v)` ↦ `paZ (AxSpinE6.fetchPa pte v)`; `PPN_of_PTE` autocast to 44
   bits ↦ `ppn0`; `bits_of_virtaddr (Virtaddr v)` ↦ `v`; `va_canon` is spelled as `textAtS`'s
   canonicality conjunct; `svpn_of` ↦ `WeakKpt.svpnOf`, `ptree_maps` ↦ `AxPtProt.ptreeMaps`;
   `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg`; `uint rd ≠ 0` ↦ `rd.toNat ≠ 0`;
   `add_vec (gpr_val rs rs1) (sign_extend' 64 imm)` ↦ `gprVal rs rs1 + sign_extend (m := 64) imm`;
   `l !! k` ↦ `l[k]?`; `(i, k) ↦ₐ P` ↦ `AxAnnot.annotOwn (i, k) P`; `zeros' 12` ↦ `0#12`, `zreg`
   ↦ `.Regidx 0#5`; `gpr` ↦ `AxSymEngine3.gpr`.
2. INSTANCES / SECTION (as `AxSpinE5` deviation 2, `AxSpinXP` deviation 2): `invGS_gen HasNoLc Σ`
   ↦ `[InvGS_gen hlc GF]` (any `hlc`); the local instances `x6_pol`/`x6_G` are inlined as
   `xv6Pol GT` / `AxSpinX2.xG L GT nm`, passed with `@`.  Section variables are explicit arguments:
   `HGex0 GT`, `HL0 GT i`, `ctrlOkSWSeip σi T satp0 hmode hasid hppn`; `AxSpinE6.Hmid0 L GT nm i Ψ
   HΨmid`; the leaves take `L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid` first.
3. O2 STAGE C COUNT SHIFT (`AxSpinE4` deviation 1): the instruction's fetch consumes NO row item.
   * `XxReg` (`e = 0`): continuation at `k` (Rocq `k + 1`); premise `k < LEN` (Rocq `k + 1 ≤ LEN`).
   * `XxSt`: the data event is AT `k` (Rocq `k + 1`): the fact is `graphData (i, k)`; continuation
     at `k + 1` (Rocq `k + 2`); premise `k + 1 ≤ LEN`.  Rocq's `Hnw` ("the row item at `k` — the
     fetch — is not a write") is DROPPED: under Stage C row item `k` IS the store, so the premise
     would be unsatisfiable; its one use (ruling out `kd = k`) is now arithmetic.
   * `XxLd`: the reload is AT `k` (Rocq `S k`): `kw < k`, the between-window `kw < k' < k`, the
     facts `graphValue (i, k)` and the annotation at `(i, k)`; continuation at `k + 1`; premise
     `k + 1 ≤ LEN`.  Rocq's `Hnr8` (row item `k`, the fetch, is not an 8-byte read) is DROPPED for
     the same reason.  Rocq's `Hntext` assertion is not built (`XBk` does not take it, `AxSpinE4`);
     the premise `¬ L.xlText (paZ pa)` is kept for caller compatibility and is unused.
4. `XxRet` RESTATED UNDER STAGE C (owner question Q20', provisional Option V,
   `notes/weak-port-q20-offrow.md`; protocol "Cross-file facts" Q20' entry).  Rocq's `Xx_ret`
   pins the return FETCH by a row item (`Hpin`: the row item at `S k` reads `nret ∈ {2,4}` bytes
   at `pret`), calls the continuation only when the target is `ret`, and proves every other
   target row-stuck through `AxSpinE3.wpd_offrowM` from the Sail premise `va_first_read` and the
   page-table facts `Hinj`/`Hstv`.  Under Stage C no row item pins a fetch (a fetch is an admin
   step answered by the boot image), so that argument has no Lean counterpart: `va_first_read` is
   unsatisfiable (a TLB-hit register-only step does an image-answered fetch and returns with no
   graph read), and a diverted c.ret into kernel text or to the trap vector is not stuck under any
   image restriction (design note §B).  The Lean `XxRet` therefore has the statement of the
   Lean-only `AxSpinE6.xxRetTgt`: premises `RetX`, `ctrlOkSW`, `PC = pc`, `hitW`, `textOkB`, `rfF`
   and `k < LEN` (Rocq `k + 2 ≤ LEN`); NO `ret`/`pret`/`nret`, `Hpin`, `Hn`, `Hinj`, `Hstv`; the
   continuation is at `k` (Rocq `k + 1`) with `GoodB … (some (jalrTgt 0#12 (gpr 1 rs))) none`
   (Rocq: `some ret`), and there is no stuck branch.  Control flow is pinned downstream by a GRAPH
   VALUE premise on the `ra` reload (AxSpinE8's `Hval`), not here.  Proof = `certJALR` +
   `linkOwZero` + `XxReg` (as Rocq's first half).
5. The trailing `Print Assumptions` lines are not ported (the lint's axiom check covers them).

**Rocq → Lean name map.**  `fetch_pa` `AxSpinE6.fetchPa` (`Weak.fetchPa` exists in ExecSC5),
`va_canon` `vaCanon`, `va_rd` `vaRd`, `vw8` `vw8`, `ctl_regime_SW` `AxSpinE6.ctlRegimeSW`,
`HGex0` `HGex0`, `HL0` `HL0`, `Hmid0` `AxSpinE6.Hmid0` (duplicated name), `ctrl_ok_SW_seip`
`ctrlOkSWSeip`, `Xx_reg` `XxReg`, `Xx_st` `XxSt`, `Xx_ld` `XxLd`, `Xx_ret` `XxRet` (restated,
deviation 4).  Lean-only: `AxSpinE6.xxRetTgt` (the Stage C c.ret leaf; `XxRet` is it).

**Dropped:** the section context `stv` and `va_first_read` (deviation 4: "Stage C: no row item
pins a fetch"); the optional `AxSpinE6.retStuckNoImg` of the design note is not added (no
consumer).  `vaCanon`/`vaRd`/`ctrlOkSWSeip` are kept (faithful, consumer-less here).  Rocq 13
definitions/lemmas, Lean 14 (13 + `AxSpinE6.xxRetTgt`).
-/
import Weak.AxSpinE5
import Weak.AxSpinE2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `fetch_pa`: the fetch address a VA's 4 KiB mapping gives (the `textAtS` form). -/
def AxSpinE6.fetchPa (pte v : BitVec 64) : BitVec 64 :=
  zero_extend (m := 64) (ppn0 pte +++ Sail.BitVec.extractLsb v (Functions.pagesize_bits - 1) 0)

/-- Rocq `va_canon`: Sv39 canonicality, spelled as Sail's `translateAddr` check. -/
def vaCanon (va : BitVec 64) : Prop :=
  (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false

/-- Rocq `va_rd`: the possible first reads of an instruction fetched at VA `v`. -/
def vaRd (T : PTree) (v : BitVec 64) (pa : Int) (n : Nat) : Prop :=
  n = 8 ∨ ((n = 2 ∨ n = 4) ∧ vaCanon v ∧
    ∃ p2 p1 pte, AxPtProt.ptreeMaps T (WeakKpt.svpnOf v) p2 p1 pte ∧
      pa = paZ (AxSpinE6.fetchPa pte v))

theorem vw8 : vmemWidth 8 := Or.inr (Or.inr (Or.inr rfl))

theorem AxSpinE6.ctlRegimeSW (T : PTree) (satp0 : BitVec 64) : ctlRegime (ctrlOkSW T satp0) :=
  fun s hc => ctlRegimeS T satp0 s hc.1

theorem HGex0 (GT : GdexecT) : ∃ GD, GD = gtAdGd GT := ⟨_, rfl⟩

theorem HL0 (GT : GdexecT) (i : Agent) :
    ∀ GD, GD = gtAdGd GT → (AxOpsem.grow GD i).length = (AxOpsem.grow (gtAdGd GT) i).length := by
  intro GD h
  rw [h]

theorem ctrlOkSWSeip (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base) (rs rs' : RegFile) :
    ctrlOkSW T satp0 rs → regsAgree AxRunClose.pinReg rs' rs → ctrlOkSW T satp0 rs' :=
  fun Hc Hag => (SpineOkTSW σi T satp0 hmode hasid hppn).sptSeip rs rs' Hc Hag

/-! # The positional leaves at Ixv6 -/

section ixleaves
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]
variable (L : Xlay) (GT : GdexecT) (nm : Xv6N)
variable (HL : xlayOk L) (Hcons : rvwmoCatConsistent (gtAdGd GT))
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
variable (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
variable (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (i : Agent) (cpu : CPU)
variable (Hfix : textFixed (gtAdGd GT) i (imgS σi))
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

include HΨmid in
/-- Rocq `Hmid0` (duplicated name: file-qualified). -/
theorem AxSpinE6.Hmid0 :
    ∀ GD s, GD = gtAdGd GT → midState s → s.atK = (AxOpsem.grow GD i).length →
      ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s := by
  rintro GD s rfl Hm Hk
  exact HΨmid s Hm Hk

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- Rocq `Xx_reg`: a register-only / control instruction.  Stage C: the continuation is at `k`
(Rocq `k + 1`), premise `k < LEN` (Rocq `k + 1 ≤ LEN`). -/
theorem XxReg (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (ins : instruction) (ot : Option (BitVec 64)) (ow : Option (BitVec 5 × BitVec 64)) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc ins → owOk ow → rfF (execute ins) →
    CertC (ctrlOkSW T satp0) rs pc is_rvc ins ot ow → k < (AxOpsem.grow (gtAdGd GT) i).length →
    ⊢ (∀ (rs' : RegFile) (ib' : Ibch), ⌜GoodB T satp0 rs pc is_rvc ot ow rs'⌝ -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro HRet Hc HPC Hhit Htx How Hrf Hcert Hle
  have H := @XBk hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) σi T satp0 hmode hasid hppn i cpu
    (fun GD => GD = gtAdGd GT) (HGX L GT nm) (AxOpsem.grow (gtAdGd GT) i).length (HL0 GT i)
    (HGex0 GT) Ψ (AxSpinE6.Hmid0 L GT nm i Ψ HΨmid) (HtextX L GT nm (imgS σi) i Hfix)
    (HflowX L GT nm HL Hcons (imgS σi) i) (HlocX L GT nm i)
    dok0 .DKSt (by intro h; cases h) (by intro h; cases h) (fun _ _ => iprop(True))
    s rs k pc is_rvc ins 0 ot (fun _ => ow) .CPend false (fun d r => d = .CPend ∧ r = false)
    HRet Hc HPC Hhit Htx (fun _ _ _ => How)
    (CertBOfCertC σi T satp0 dok0 .DKSt rs pc is_rvc ins ot ow .CPend false Hrf Hcert)
    Hle (by omega)
  iintro C
  iapply H $$ [] [C]
  · simp only [CResK, CFkM]
    letI : AxirisG GF := AxSpinX2.xG L GT nm
    letI : Axpol := xv6Pol GT
    iapply (FstDok0M (GF := GF) rvwmoCatConsistent i)
  · iintro %d %r %rs' %ib' %_ %HGB -
    iapply C $$ %rs' %ib' %HGB

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- Rocq `Xx_st`: a store to hart `i`'s private slot at `pa`.  Stage C: the data event is AT `k`
(Rocq `k + 1`), the continuation at `k + 1` (Rocq `k + 2`), premise `k + 1 ≤ LEN`; Rocq's `Hnw`
(row item `k`, the fetch, is not a write) is DROPPED (row item `k` IS the store). -/
theorem XxSt (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (imm : BitVec 12) (rs2 rs1 : BitVec 5) (va pa : BitVec 64) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)) →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Store .Data) va 8 pa → hitW rs va →
    (∀ j : Nat, j < 8 → priv L (paZ pa + (j : Int)) i) →
    (∀ (k' : Nat) (lb : Lbl) (rl : Bool) (b : Int) (m : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aidentWr (aident lb) = some (rl, b, m) →
      m ≤ 8) →
    k + 1 ≤ (AxOpsem.grow (gtAdGd GT) i).length →
    ⊢ (∀ (rs' : RegFile) (ib' : Ibch), ⌜GoodB T satp0 rs pc is_rvc none none rs'⌝ -∗
        ⌜graphData (gtAdGd GT) (i, k) = some (stBytes 8 (gprVal rs rs2))⌝ -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 1⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro HRet Hc HPC Hhit Htx Hva Hda Hhv Hpriv Hw8 Hle
  have H := @XBk hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) σi T satp0 hmode hasid hppn i cpu
    (fun GD => GD = gtAdGd GT) (HGX L GT nm) (AxOpsem.grow (gtAdGd GT) i).length (HL0 GT i)
    (HGex0 GT) Ψ (AxSpinE6.Hmid0 L GT nm i Ψ HΨmid) (HtextX L GT nm (imgS σi) i Hfix)
    (HflowX L GT nm HL Hcons (imgS σi) i) (HlocX L GT nm i)
    (dokSlot (paZ pa)) .DKSt (by intro h; cases h) (by intro h; cases h) (OutSt GT i (paZ pa))
    s rs k pc is_rvc _ 1 none (fun _ => none) .CPend false _
    HRet Hc HPC Hhit Htx (fun _ _ _ => trivial)
    (CertBStoreS σi T satp0 hmode hasid hppn (dokSlot (paZ pa)) rs pc is_rvc imm rs2 rs1 8 va pa
      false vw8 (by omega) (by omega) Hva Hda Hhv ⟨rfl, rfl⟩)
    (by omega) Hle
  iintro C
  iapply H $$ [] [C]
  · simp only [CResK, CFkM]
    iapply (FstSlot L GT nm HL Hcons i (paZ pa) Hpriv Hw8)
  · iintro %d %r %rs' %ib' %HPX %HGB HO
    obtain ⟨rfl, rfl⟩ := HPX
    simp only [CResK]
    icases HO with ⟨%kd, %Hkd, HO⟩
    obtain rfl : kd = k := by omega
    unfold OutSt
    icases HO with %Hgd
    iapply C $$ %rs' %ib' %HGB %Hgd.1

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- Rocq `Xx_ld`: the RELOAD of hart `i`'s private slot at `pa`, spilled at `kw`.  Stage C: the
reload is AT `k` (Rocq `k + 1`), the continuation at `k + 1` (Rocq `k + 2`), `kw < k` and the
between-window `kw < k' < k` (Rocq `S k`), premise `k + 1 ≤ LEN`; Rocq's `Hnr8` (row item `k`,
the fetch, is not an 8-byte read) is DROPPED (row item `k` IS the reload). -/
theorem XxLd (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (imm : BitVec 12) (rs1 rd : BitVec 5) (va pa : BitVec 64) (kw : Nat)
    (vw : List (BitVec 8)) (cls : WmClass) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)) →
    rd.toNat ≠ 0 →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Load .Data) va 8 pa → hitW rs va →
    (∀ j : Nat, j < 8 → priv L (paZ pa + (j : Int)) i) → ¬ L.xlText (paZ pa) →
    (∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (n : Nat),
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb → aident lb = .IRmw aq rl (paZ pa) n → n ≠ 8) →
    (AxOpsem.grow (gtAdGd GT) i)[kw]? = some (.LStore false (paZ pa) vw cls) → vw.length = 8 →
    kw < k →
    (∀ (k' : Nat) (lb' : Lbl) (rl : Bool) (b : Int) (m : Nat), kw < k' ∧ k' < k →
      (AxOpsem.grow (gtAdGd GT) i)[k']? = some lb' → aidentWr (aident lb') = some (rl, b, m) →
      b + (m : Int) ≤ paZ pa ∨ paZ pa + 8 ≤ b) →
    k + 1 ≤ (AxOpsem.grow (gtAdGd GT) i).length →
    ⊢ (∀ (vs : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch), ⌜vs.length = 8⌝ -∗
        ⌜GoodB T satp0 rs pc is_rvc none (some (rd, ldRes false 8 vs)) rs'⌝ -∗
        ⌜graphValue (gtAdGd GT) (i, k) = some vs⌝ -∗
        AxAnnot.annotOwn (GF := GF) (i, k) iprop(⌜RLfact GT i (paZ pa) k vw⌝) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 1⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro HRet Hc HPC Hhit Htx Hrd Hva Hda Hhv Hpriv _ Hnormw Hw Hlen Hkw Hbetween Hle
  have HnoRmw : Dkind.DKLd = .DKLd → ∀ GD, rvwmoCatConsistent GD →
      @AxirisG.gconstInterp GF (AxSpinX2.xG L GT nm) GD ⊢
      ⌜∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat),
        (AxOpsem.grow GD i)[k']? = some lb → aident lb = .IRmw aq rl base n →
        ¬ dokSlot (paZ pa) base n⌝ := by
    intro _ GD Hc'
    iintro Hg
    ihave %Heq := (HGX L GT nm GD Hc') $$ Hg
    subst Heq
    ipureintro
    rintro k' lb aq rl base n Hlb Hid ⟨rfl, rfl⟩
    exact Hnormw k' lb aq rl 8 Hlb Hid rfl
  have H := @XBk hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) σi T satp0 hmode hasid hppn i cpu
    (fun GD => GD = gtAdGd GT) (HGX L GT nm) (AxOpsem.grow (gtAdGd GT) i).length (HL0 GT i)
    (HGex0 GT) Ψ (AxSpinE6.Hmid0 L GT nm i Ψ HΨmid) (HtextX L GT nm (imgS σi) i Hfix)
    (HflowX L GT nm HL Hcons (imgS σi) i) (HlocX L GT nm i)
    (dokSlot (paZ pa)) .DKLd HnoRmw (by intro h; cases h) (OutLd GT i (paZ pa) k vw)
    s rs k pc is_rvc _ 1 none (owLdB rd false 8) .CPend false _
    HRet Hc HPC Hhit Htx (by rintro d r ⟨vs, rfl, -, -⟩; exact Hrd)
    (CertBLoadS σi T satp0 hmode hasid hppn (dokSlot (paZ pa)) rs pc is_rvc imm rs1 rd false 8 va
      pa false Hrd vw8 (by omega) (by omega) Hva Hda Hhv ⟨rfl, rfl⟩)
    (by omega) Hle
  iintro C
  iapply H $$ [] [C]
  · simp only [CResK, CFkM]
    iapply (FldSlot L GT nm HL Hcons i (paZ pa) k kw vw cls Hpriv Hnormw Hw Hlen Hkw Hbetween)
  · iintro %d %r %rs' %ib' %HPX %HGB HO
    obtain ⟨vs, rfl, Hvs, rfl⟩ := HPX
    simp only [CResK]
    icases HO with ⟨%kd, %Hkd, HO⟩
    obtain rfl : kd = k := by omega
    unfold OutLd
    rw [show RLann GT i (paZ pa) kd vw kd = iprop(⌜RLfact GT i (paZ pa) kd vw⌝) from if_pos rfl]
    icases HO with ⟨%Hgv, HO⟩
    iapply C $$ %vs %rs' %ib' %Hvs %HGB %Hgv.1 HO

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- (Lean-only, Q20' Option V) THE c.ret LEAF UNDER STAGE C: `c.jr ra` is register-only, so the
continuation is at `k` with `PC = jalrTgt 0 (gpr 1 rs)`; no stuck branch. -/
theorem AxSpinE6.xxRetTgt (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc true (.JALR (0#12, .Regidx 1#5, .Regidx 0#5)) →
    rfF (execute (.JALR (0#12, .Regidx 1#5, .Regidx 0#5))) →
    k < (AxOpsem.grow (gtAdGd GT) i).length →
    ⊢ (∀ (rs' : RegFile) (ib' : Ibch),
        ⌜GoodB T satp0 rs pc true (some (jalrTgt 0#12 (AxSymEngine3.gpr 1#5 rs))) none rs'⌝ -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro HRet Hc HPC Hhit Htx Hrf Hle
  have Hcj := certJALR (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs pc true 0#12 1#5 0#5
    (by decide)
  rw [linkOwZero 0#5 _ (by decide)] at Hcj
  exact XxReg L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid s rs k pc true _
    (some (jalrTgt 0#12 (uxaXget rs 1#5))) none HRet Hc HPC Hhit Htx trivial Hrf Hcj Hle

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- Rocq `Xx_ret`, RESTATED under Stage C (Q20' Option V; see the header): the statement of
`AxSpinE6.xxRetTgt`. -/
theorem XxRet (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc true (.JALR (0#12, .Regidx 1#5, .Regidx 0#5)) →
    rfF (execute (.JALR (0#12, .Regidx 1#5, .Regidx 0#5))) →
    k < (AxOpsem.grow (gtAdGd GT) i).length →
    ⊢ (∀ (rs' : RegFile) (ib' : Ibch),
        ⌜GoodB T satp0 rs pc true (some (jalrTgt 0#12 (AxSymEngine3.gpr 1#5 rs))) none rs'⌝ -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ :=
  AxSpinE6.xxRetTgt L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid s rs k pc

end ixleaves

end Weak
