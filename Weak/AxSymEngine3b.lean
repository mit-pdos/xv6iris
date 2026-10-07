/-
Weak: **the symbolic WPd engine X, slice 2 — part 2 of 2** (Lean-only split of
`iris/AxSymEngine3.v`, §5–§6; part 1 is `Weak.AxSymEngine3`).

Rocq: `iris/AxSymEngine3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§5 INSTANCE PREMISES DISCHARGED: `HtextGa2`/`HflowGa2`/`HlocGa2` at `axGA2` for ANY read-neutral
base protocol (the real `protInv`: `protInvReadNeutral`); `HtextLedger`/`HflowLedger`/
`HlocLedger` at the ledger-extended instance (`obStInterpL`; the fetch takes a NEUTRAL ledger
step, given: `gwf`, fetches are gmo events, full gmo-prefix handout, no Own-class byte fetched).
`textFixedOfFetchGdOk`: `textFixed` from AxEpi*-style `fetchGdOk` facts.
§6 NON-VACUITY.  `wpdBlockCmvCaddiw` / `wpdBlockGa2`: the block `c.mv a0,ra ; c.addiw a0,imm`
through X twice at a SYMBOLIC pc, regfile and control state, post `ΦRet cpu (PBlk pc rs0 imm)`,
all row-end premises discharged.  Concrete: `nv2BlockFalse/True` — the REAL `riscvStep` twice
(all 4 tick combinations, every pin answer) at `AxEpiProbe.tAt 0x80000002` satisfies exactly
`PBlk`'s equation; `nv2Fetch2`/`nv2DecodeExpand2`/`nv2Rf0` the second instruction's `textOkDB`
facts.  4-byte arm: `nv4*` (add a0, ra, zero).  FINDING (as Rocq): at a 4-byte-ALIGNED pc the
model's fetch reads four bytes even for an RVC instruction, so the image covers the following
halfword too.

## Deviations from Rocq

1. `axGA2` (Lean `AxTierA2`) has no `T` parameter; Rocq's `Local Instance sym_ga2`/`sym_gaL` are
   not declared — statements pass the instance explicitly (`(self := axGA2 …)`,
   `@fetchFlow hlc GF _ (axGA2 …) pol …`); `blk_ga2` is the reducible def `blkGa2` (passed with
   `@`).  `{GF : BundledGFunctors.{0,0,0}}` as `axGA2` requires.  `{[e]} ∪ s` ↦
   `({e} : GSet Geid) ∪ s`.  `HlocGa2`/`HlocLedger` are kept although Lean's bridge no longer
   takes `Hloc` (AxSymEngine3 deviation 1).
2. Types as `AxSymEngine3` deviation 4; Rocq `gpr` ↦ `AxSymEngine3.gpr` (= `uxaXget`;
   file-qualified because `MachCSL.gpr` is open), `zero_reg` ↦ `0#64`.
3. `vm_compute; reflexivity` ↦ `decide +kernel`; `bool_decide (x = I_caddiw …)` /
   `bool_decide (x = I_add4)` ↦ match projections on the immediate and register indices (the
   model's `instruction` has no `DecidableEq`); `nv2Mid` is `noncomputable` (`riscvStep` is).
4. Lean-only (file-qualified): `AxSymEngine3.naSplittingWfEmpty` / `AxSymEngine3.annotInsertEq`
   (copies of the `AxTokLedgerWp` lemmas without `LedgerG`).

**Rocq → Lean name map.**  `text_fixed_of_fetch_gd_ok` `textFixedOfFetchGdOk`, `row_read_not_w`
`rowReadNotW`, `row_read_lbl` `rowReadLbl`, `Htext_ga2` `HtextGa2`, `Hloc_ga2` `HlocGa2`,
`Hflow_ga2` `HflowGa2`, `prot_inv_read_neutral` `protInvReadNeutral`, `Hflow_ledger`
`HflowLedger`, `Htext_ledger` `HtextLedger`, `Hloc_ledger` `HlocLedger`, `add_vec_int_ne`
`addVecIntNe`, `add_vec_int_22_ne` `addVecInt22Ne`, `ra5` `ra5`, `a05` `a05`, `I_cmv` `ICmv`,
`I_caddiw` `ICaddiw`, `gpr` `AxSymEngine3.gpr`, `blk_w1` `blkW1`, `blk_w2` `blkW2`, `blk_end`
`blkEnd`, `P_blk` `PBlk`, `cert_cmv` `certCmv`, `cert_caddiw` `certCaddiw`,
`wpd_block_cmv_caddiw` `wpdBlockCmvCaddiw`, `blk_ga2` `blkGa2`, `wpd_block_ga2` `wpdBlockGa2`,
`nv2_imm` `nv2Imm`, `nv2_img` `nv2Img`, `nv2_final` `nv2Final`, `nv2_mid` `nv2Mid`,
`nv2_block_false/true` `nv2BlockFalse/True`, `nv2_fetch2` `nv2Fetch2`, `nv2_decode_expand2`
`nv2DecodeExpand2`, `nv2_rf0` `nv2Rf0`, `nv2_blk_end` `nv2BlkEnd`, `nv4_img` `nv4Img`, `I_add4`
`IAdd4`, `nv4_post` `nv4Post`, `nv4_step_false/true` `nv4StepFalse/True`, `nv4_fetch`
`nv4Fetch`, `nv4_decode` `nv4Decode`, `nv4_nlpad` `nv4Nlpad`, `nv4_rf0` `nv4Rf0`, `nv2_cert`
`nv2Cert`, `nv4_cert` `nv4Cert`.

**Dropped:** nothing (this part: Rocq 49 definitions/lemmas incl. 3 local instances; Lean 47 —
`sym_ga2`/`sym_gaL` not declared, deviation 1 — + 2 Lean-only).
**Not ported:** the `Print Assumptions` lines.
-/
import Weak.AxSymEngine3
import Weak.AxTokLedgerWp
import Weak.AxProt

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 5. THE INSTANCE PREMISES DISCHARGED: `axGA2` (`protInv` or any read-neutral base) and the
LEDGER-extended `axGA2` (`obStInterpL`) -/

/-- `textFixed` from per-position `fetchGdOk` facts (the AxEpi* form). -/
theorem textFixedOfFetchGdOk (GD : Gdexec) (i : Agent) (img : Image)
    (Himg : ∀ a b, img a = some b → GD.gdG.gxImg a = some b)
    (Hgd : ∀ k lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb →
       aidentRd (aident lb) = some (aq, base, n) → imgBytes img base n = some vs →
       fetchGdOk GD i k base vs) :
    textFixed GD i img := by
  refine ⟨Himg, ?_⟩
  intro k lb aq base n vs Hlb Hrd Hvs
  obtain ⟨⟨lb', Hlb', Hid⟩, Hgv, -⟩ := Hgd k lb aq base n vs Hlb Hrd Hvs
  rw [Hlb] at Hlb'
  cases Hlb'
  refine ⟨?_, Hgv⟩
  rw [Hid] at Hrd ⊢
  simp only [aidentRd, Option.some.injEq, Prod.mk.injEq] at Hrd
  obtain ⟨rfl, -, rfl⟩ := Hrd
  rfl

/-- A row item that is a plain read is not a write. -/
theorem rowReadNotW (GD : Gdexec) (i : Agent) (k : Nat) (lb : Lbl) (aq : Bool) (base : Int)
    (n : Nat) :
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base n →
    gisW GD.gdG (i, k) = false := by
  intro Hlb Hid
  unfold gisW gxLbl
  unfold AxOpsem.grow growG at Hlb
  cases hp : GD.gdG.gxProg[i]? with
  | none => rw [hp] at Hlb; simp at Hlb
  | some p =>
    rw [hp] at Hlb
    simp only [Option.getD_some] at Hlb
    simp only [Option.bind_some, Hlb]
    cases lb <;> simp [aident] at Hid <;> rfl

theorem rowReadLbl (GD : Gdexec) (i : Agent) (k : Nat) (lb : Lbl) :
    (AxOpsem.grow GD i)[k]? = some lb → gxLbl GD.gdG (i, k) = some lb := by
  unfold gxLbl AxOpsem.grow growG
  cases hp : GD.gdG.gxProg[i]? with
  | none => simp
  | some p => simp

section instGa2
variable {GF : BundledGFunctors.{0,0,0}} [AxannotGS GF]

/-- (Lean-only, copy of `AxTokLedgerWp.naSplittingWfEmpty` without `LedgerG`). -/
theorem AxSymEngine3.naSplittingWfEmpty [AxirisG GF] (sLob : GSet Geid) (na : Mea GF) :
    ⊢ naSplittingWf sLob na (∅ : Mea GF) (∅ : Mea GF) := by
  unfold naSplittingWf
  isplitr
  · ipureintro
    rw [domEmpty]
    exact LawfulSet.empty_subset
  · iapply (BigSepM2.bigSepM2_empty _).2
    itrivial

open Iris.Std.PartialMap MachCSL.Stdpp in
/-- (Lean-only, copy of `AxTokLedgerWp.annotInsertEq` without `LedgerG`). -/
theorem AxSymEngine3.annotInsertEq (na : Mea GF) (e : Geid) (R : IProp GF) :
    PartialMap.union (PartialMap.union {[e := R]} (∅ : Mea GF)) na = insert na e R := by
  have h1 : PartialMap.union ({[e := R]} : Mea GF) (∅ : Mea GF) = {[e := R]} :=
    mapUnionEmptyR (M := GMapF Geid)
  rw [h1]
  exact (insertUnionSingletonL (M := GMapF Geid)).symm

variable (GD0 : Gdexec) (N obSt0 : Type) (interp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF)
  (nm : N)
variable (img : Image) (i : Agent)

theorem HtextGa2 (Hfix : textFixed GD0 i img) :
    ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (self := axGA2 GD0 N obSt0 interp0 nm) GD ⊢ ⌜textFixed GD i img⌝ := by
  intro GD _
  show iprop(⌜GD = GD0⌝) ⊢ _
  iintro %h
  subst h
  ipureintro
  exact Hfix

theorem HlocGa2 :
    ∀ GD (ls : @AxirisG.logTsT GF (axGA2 GD0 N obSt0 interp0 nm)) k, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (self := axGA2 GD0 N obSt0 interp0 nm) GD ∗
          AxirisG.localInterp (self := axGA2 GD0 N obSt0 interp0 nm) GD i k ls ⊢
        |==> ∃ ls' : @AxirisG.logTsT GF (axGA2 GD0 N obSt0 interp0 nm),
          AxirisG.localInterp (self := axGA2 GD0 N obSt0 interp0 nm) GD i (k + 1) ls' := by
  intro GD _ k _
  have hloc : ⊢ AxirisG.localInterp (self := axGA2 GD0 N obSt0 interp0 nm) GD i (k + 1) () := by
    show ⊢ iprop(True)
    itrivial
  iintro -
  imodintro
  iexists ()
  iapply hloc

/-- The fetch deposit (`True`) at ANY read-neutral base protocol (`AxEpiAdeq.fetchFlowGa2`'s
proof with `protInvReadStep` ↦ `Hrd0`, uniformly in the row position). -/
theorem HflowGa2 {hlc : HasLC} [InvGS_gen hlc GF] [pol : Axpol]
    (Hrd0 : ∀ GD σ s e, e ∉ s → gisW GD.gdG e = false →
       interp0 nm GD σ s ⊢ interp0 nm GD σ (({e} : GSet Geid) ∪ s)) :
    ∀ GD (ls : @AxirisG.logTsT GF (axGA2 GD0 N obSt0 interp0 nm)) k, rvwmoCatConsistent GD →
      (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
         imgBytes img base n = some vs) →
      AxirisG.gconstInterp (self := axGA2 GD0 N obSt0 interp0 nm) GD ∗
          AxirisG.localInterp (self := axGA2 GD0 N obSt0 interp0 nm) GD i k ls ⊢
        @fetchFlow hlc GF _ (axGA2 GD0 N obSt0 interp0 nm) pol GD i k := by
  intro GD ls k _ ⟨lb, aq, base, n, vs, Hlb, Hid, _⟩
  have Hnw := rowReadNotW GD i k lb aq base n Hlb Hid
  show iprop(⌜GD = GD0⌝ ∗ True) ⊢ _
  iintro ⟨%Heq, -⟩
  subst Heq
  have hloc : ⊢ AxirisG.localInterp (self := axGA2 GD N obSt0 interp0 nm) GD i (k + 1) () := by
    show ⊢ iprop(True)
    itrivial
  letI : AxirisG GF := axGA2 GD N obSt0 interp0 nm
  unfold fetchFlow
  iintro %na ⟨Hpg, Hannot⟩
  ihave %Hnin := naAtProgressNotElemOf GD i k na $$ Hpg
  imod (annotAlloc na (i, k) iprop(True) Hnin) $$ Hannot with ⟨Hannot, -⟩
  imodintro
  inext
  imodintro
  iexists iprop(True), (∅ : Mea GF), (∅ : Mea GF), ()
  isplitr
  · iapply AxSymEngine3.naSplittingWfEmpty
  isplitr
  · unfold flowEqDyn
    iintro %σ %sOb %Hsub %Hnin' Hob -
    iapply fupd_mask_intro LawfulSet.empty_subset
    iintro Hclose
    inext
    imod Hclose
    imodintro
    iexists σ
    isplitl [Hob]
    · iapply Hrd0 GD σ sOb (i, k) Hnin' Hnw
      iexact Hob
    · itrivial
  isplitl [Hannot]
  · rw [AxSymEngine3.annotInsertEq]
    iexact Hannot
  · iapply hloc

end instGa2

/-- The REAL protocol (`protInv`) is read-neutral. -/
theorem protInvReadNeutral {GF : BundledGFunctors} [AxlogG GF Hent] :
    ∀ (γ : GName) GD (σ : Unit) s e, e ∉ s → gisW GD.gdG e = false →
      (fun (γ : GName) (GD : Gdexec) (_ : Unit) (s : GSet Geid) => protInv (GF := GF) γ GD s)
          γ GD σ s ⊢
        (fun (γ : GName) (GD : Gdexec) (_ : Unit) (s : GSet Geid) => protInv (GF := GF) γ GD s)
          γ GD σ (({e} : GSet Geid) ∪ s) :=
  fun γ GD _ s e Hnin Hnw => protInvReadStep γ GD s e Hnin Hnw

section instLedger
variable {GF : BundledGFunctors.{0,0,0}} [AxannotGS GF] [LedgerG GF]
variable (GD0 : Gdexec) (OC : Int → Prop) (nh : Nat) (N0 obSt0 : Type)
  (base0 : N0 → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N0 × GName)
variable (img : Image) (i : Agent)

/-- At the ledger instance a fetch must ALSO take one legal (here: neutral) ledger step. -/
theorem HflowLedger {hlc : HasLC} [InvGS_gen hlc GF] [pol : Axpol]
    (Hrd0 : ∀ GD σ s e, e ∉ s → gisW GD.gdG e = false →
       base0 nm.1 GD σ s ⊢ base0 nm.1 GD σ (({e} : GSet Geid) ∪ s))
    (Hwf : gwf GD0.gdG)
    (Hgmo : ∀ k lb aq base n, (AxOpsem.grow GD0 i)[k]? = some lb → aident lb = .IRead aq base n →
       (i, k) ∈ GD0.gdG.gxGmo)
    (Hpref : ∀ k lb aq base n, (AxOpsem.grow GD0 i)[k]? = some lb → aident lb = .IRead aq base n →
       (LawfulSet.ofList (gmoPrefix GD0.gdG (i, k)) : GSet Geid) ⊆ Axpol.sPol GD0 (i, k))
    (Hnoc : ∀ k lb aq base n a, (AxOpsem.grow GD0 i)[k]? = some lb → aident lb = .IRead aq base n →
       OC a → tidHart nh (some i) → gaccesses GD0.gdG (i, k) a → False) :
    ∀ GD (ls : @AxirisG.logTsT GF (axGA2 GD0 (N0 × GName) obSt0 (obStInterpL OC nh base0) nm)) k,
      rvwmoCatConsistent GD →
      (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
         imgBytes img base n = some vs) →
      AxirisG.gconstInterp (self := axGA2 GD0 (N0 × GName) obSt0 (obStInterpL OC nh base0) nm) GD ∗
          AxirisG.localInterp (self := axGA2 GD0 (N0 × GName) obSt0 (obStInterpL OC nh base0) nm)
            GD i k ls ⊢
        @fetchFlow hlc GF _ (axGA2 GD0 (N0 × GName) obSt0 (obStInterpL OC nh base0) nm) pol
          GD i k := by
  intro GD ls k _ ⟨lb, aq, base, n, vs, Hlb, Hid, _⟩
  show iprop(⌜GD = GD0⌝ ∗ True) ⊢ _
  iintro ⟨%Heq, -⟩
  subst Heq
  have Hnw := rowReadNotW GD i k lb aq base n Hlb Hid
  have hloc : ⊢ AxirisG.localInterp (self := axGA2 GD (N0 × GName) obSt0 (obStInterpL OC nh base0) nm)
      GD i (k + 1) () := by
    show ⊢ iprop(True)
    itrivial
  letI : AxirisG GF := axGA2 GD (N0 × GName) obSt0 (obStInterpL OC nh base0) nm
  have HobExt := axGA2LedgerObExt GD OC nh N0 obSt0 base0 nm
  have Hfe := flowEqLedger OC nh nm.2 (base0 nm.1) HobExt GD (i, k) (Axpol.sPol GD (i, k))
    (∅ : Mea GF) iprop(True) iprop(True) iprop(True) Hwf (Hgmo k lb aq base n Hlb Hid)
    (Hpref k lb aq base n Hlb Hid)
  have Hact := ledgerActNeutral (GF := GF) OC nh nm.2 GD (i, k) iprop(True)
    (fun a HOC Hh Hacc => Hnoc k lb aq base n a Hlb Hid HOC Hh Hacc)
  have Hbase : ⊢ flowEqBase (base0 nm.1) GD (i, k) (Axpol.sPol GD (i, k)) (∅ : Mea GF)
      iprop(True ∗ True) := by
    unfold flowEqBase
    iintro %σ %sOb %Hsub %Hnin' Hob -
    iapply fupd_mask_intro LawfulSet.empty_subset
    iintro Hclose
    inext
    imod Hclose
    imodintro
    iexists σ
    isplitl [Hob]
    · iapply Hrd0 GD σ sOb (i, k) Hnin' Hnw
      iexact Hob
    · isplitl <;> itrivial
  unfold fetchFlow
  iintro %na ⟨Hpg, Hannot⟩
  ihave %Hnin := naAtProgressNotElemOf GD i k na $$ Hpg
  imod (annotAlloc na (i, k) iprop(True ∗ True) Hnin) $$ Hannot with ⟨Hannot, -⟩
  imodintro
  inext
  imodintro
  iexists iprop(True ∗ True), (∅ : Mea GF), (∅ : Mea GF), ()
  isplitr
  · iapply AxTokLedgerWp.naSplittingWfEmpty
  isplitr
  · iapply Hfe
    · iapply Hbase
    · iapply Hact
  isplitl [Hannot]
  · rw [AxTokLedgerWp.annotInsertEq]
    iexact Hannot
  · iapply hloc

theorem HtextLedger (Hfix : textFixed GD0 i img) :
    ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (self := axGA2 GD0 (N0 × GName) obSt0 (obStInterpL OC nh base0) nm) GD ⊢
        ⌜textFixed GD i img⌝ :=
  HtextGa2 (GF := GF) GD0 (N0 × GName) obSt0 (obStInterpL OC nh base0) nm img i Hfix

theorem HlocLedger :
    ∀ GD (ls : @AxirisG.logTsT GF (axGA2 GD0 (N0 × GName) obSt0 (obStInterpL OC nh base0) nm)) k,
      rvwmoCatConsistent GD →
      AxirisG.gconstInterp (self := axGA2 GD0 (N0 × GName) obSt0 (obStInterpL OC nh base0) nm) GD ∗
          AxirisG.localInterp (self := axGA2 GD0 (N0 × GName) obSt0 (obStInterpL OC nh base0) nm)
            GD i k ls ⊢
        |==> ∃ ls' : @AxirisG.logTsT GF (axGA2 GD0 (N0 × GName) obSt0 (obStInterpL OC nh base0) nm),
          AxirisG.localInterp (self := axGA2 GD0 (N0 × GName) obSt0 (obStInterpL OC nh base0) nm)
            GD i (k + 1) ls' :=
  HlocGa2 (GF := GF) GD0 (N0 × GName) obSt0 (obStInterpL OC nh base0) nm i

end instLedger


/-! # 6. NON-VACUITY: a composed 2-instruction block through X (`c.mv a0, ra ; c.addiw a0, imm`)
at a SYMBOLIC pc / regfile -/

theorem addVecIntNe (pc : BitVec 64) (j : Int) : 0 < j ∧ j < 4096 → BitVec.addInt pc j ≠ pc := by
  intro ⟨h1, h2⟩ E
  unfold BitVec.addInt at E
  generalize hx : BitVec.ofInt 64 j = x at E
  have h : x = 0#64 := by bv_omega
  subst h
  have h3 := congrArg BitVec.toNat hx
  rw [BitVec.toNat_ofInt] at h3
  have h0 : (0#64).toNat = 0 := rfl
  rw [h0] at h3
  omega

theorem addVecInt22Ne (pc : BitVec 64) : BitVec.addInt (BitVec.addInt pc 2) 2 ≠ pc := by
  intro E
  unfold BitVec.addInt at E
  have h2 : BitVec.ofInt 64 2 = 2#64 := by decide
  rw [h2] at E
  bv_omega

def ra5 : BitVec 5 := 1#5
def a05 : BitVec 5 := 10#5
def ICmv : instruction := .RTYPE (.Regidx ra5, zreg, .Regidx a05, .ADD)
def ICaddiw (imm : BitVec 6) : instruction :=
  .ADDIW (sign_extend (m := 12) imm, .Regidx a05, .Regidx a05)
/-- Rocq `gpr` (file-qualified: `MachCSL.gpr` is the SC points-to). -/
def AxSymEngine3.gpr (r : BitVec 5) (rs : RegFile) : BitVec 64 := uxaXget rs r
def blkW1 (rs0 : RegFile) : BitVec 64 := 0#64 + AxSymEngine3.gpr ra5 rs0
def blkW2 (rs0 : RegFile) (imm : BitVec 6) : BitVec 64 :=
  sign_extend (m := 64) (Sail.BitVec.extractLsb
    (blkW1 rs0 + sign_extend (m := 64) (sign_extend (m := 12) imm)) 31 0)
def blkEnd (pc : BitVec 64) : BitVec 64 := BitVec.addInt (BitVec.addInt pc 2) 2

/-- THE BLOCK'S POST: at the block-end boundary, a0 holds the composed value, every other GPR its
start value. -/
def PBlk (pc : BitVec 64) (rs0 : RegFile) (imm : BitVec 6) (rs : RegFile) : Prop :=
  rs .PC = blkEnd pc →
  ∀ r : BitVec 5, r.toNat ≠ 0 →
    AxSymEngine3.gpr r rs = if r = a05 then blkW2 rs0 imm else AxSymEngine3.gpr r rs0

theorem certCmv (rs0 : RegFile) (s_pc : ExecSt) :
    gprAgree s_pc.regs rs0 →
    exec (execute ICmv) s_pc = some (RETIRE_SUCCESS, s_pc.setGpr a05 (blkW1 rs0)) := by
  intro Hag
  show exec (execute_RTYPE (.Regidx ra5) (.Regidx 0#5) (.Regidx a05) .ADD) s_pc = _
  rw [execExecuteRTYPEADDGpr ra5 0#5 a05 s_pc]
  unfold gprRdVal
  have h : s_pc.gpr ra5 = AxSymEngine3.gpr ra5 rs0 := Hag ra5 (by decide)
  rw [h]
  rfl

theorem certCaddiw (rs1 : RegFile) (v : BitVec 64) (imm : BitVec 6) (s_pc : ExecSt) :
    AxSymEngine3.gpr a05 rs1 = v →
    gprAgree s_pc.regs rs1 →
    exec (execute (ICaddiw imm)) s_pc = some (RETIRE_SUCCESS, s_pc.setGpr a05
      (sign_extend (m := 64) (Sail.BitVec.extractLsb
        (v + sign_extend (m := 64) (sign_extend (m := 12) imm)) 31 0))) := by
  intro Hv Hag
  rw [ICaddiw, execExecuteADDIWGpr a05 a05 (sign_extend (m := 12) imm) s_pc]
  unfold gprAddiwVal
  have h : s_pc.gpr a05 = v := (Hag a05 (by decide)).trans Hv
  rw [h]

section block
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (img : Image) (i : Agent) (cpu : CPU)
variable (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
  (textAt4 : BitVec 64 → BitVec 32 → Prop)
variable (Hsp : SpineOk img ctrlOk textAt) (Hf4 : SpineFetch4 img ctrlOk textAt4)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)

include Hsp Hf4 Htext Hflow in
/-- THE BLOCK, through X twice, at a symbolic pc / regfile / control state, for the REAL post
`ΦRet cpu (PBlk pc rs0 imm)`; every row-end premise discharged. -/
theorem wpdBlockCmvCaddiw (pc : BitVec 64) (imm : BitVec 6) (s0 : Athread) (rs0 : RegFile)
    (k0 : Nat) :
    RetX cpu rs0 k0 s0 → ctrlOk rs0 → rs0 .PC = pc →
    textOkDB img ctrlOk textAt textAt4 pc true ICmv →
    textOkDB img ctrlOk textAt textAt4 (BitVec.addInt pc 2) true (ICaddiw imm) →
    ⊢ (∀ s' rs' k', ⌜RetX cpu rs' k' s'⌝ -∗ ⌜ctrlOk rs'⌝ -∗
         ⌜rs' .PC = blkEnd pc⌝ -∗
         ⌜∀ r : BitVec 5, r.toNat ≠ 0 →
            AxSymEngine3.gpr r rs' = if r = a05 then blkW2 rs0 imm else AxSymEngine3.gpr r rs0⌝ -∗
         wpd .MaybeStuck i s' (ΦRet (GF := GF) cpu (PBlk pc rs0 imm))) -∗
       wpd .MaybeStuck i s0 (ΦRet (GF := GF) cpu (PBlk pc rs0 imm)) := by
  intro HR0 Hc0 HPC0 Htx1 Htx2
  have HX := XGprWriteΦHolds img i cpu ctrlOk textAt textAt4 Hsp Hf4 Htext Hflow (fun _ => True)
    (fun _ _ => BI.pure_intro trivial) (ΦRet (GF := GF) cpu (PBlk pc rs0 imm)) (ΦRetMid i cpu _ _)
  have Hbnd : ∀ rs k s1, rs .PC ≠ blkEnd pc → RetX cpu rs k s1 →
      ⊢ postLifting (ΦRet (GF := GF) cpu (PBlk pc rs0 imm)) i s1 :=
    fun rs k s1 Hne HR => ΦRetBoundary i cpu _ rs k s1
      (fun rs' Hag Hpc => (Hne
        ((Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))).symm.trans Hpc)).elim) HR
  iintro C
  iapply (HX s0 rs0 k0 pc true ICmv a05 (blkW1 rs0) HR0 Hc0 HPC0 Htx1 (by decide)
    (fun s_pc _ Hag => certCmv rs0 s_pc Hag)
    (fun _ s1 _ HR _ => Hbnd rs0 k0 s1 (by rw [HPC0]; exact (addVecInt22Ne pc).symm) HR))
  iintro %s1 %rs1 %k1 %HR1 %Hc1 %HPC1 %Hg1
  have Hv1 : AxSymEngine3.gpr a05 rs1 = blkW1 rs0 := by
    have h := Hg1 a05 (by decide)
    rw [if_pos rfl] at h
    exact h
  have Hne1 : rs1 .PC ≠ blkEnd pc := by
    rw [HPC1]
    exact (addVecIntNe (BitVec.addInt pc 2) 2 ⟨by decide, by decide⟩).symm
  iapply (HX s1 rs1 k1 (pc + instrLen true) true (ICaddiw imm) a05 (blkW2 rs0 imm) HR1 Hc1 HPC1
    Htx2 (by decide)
    (fun s_pc _ Hag => certCaddiw rs1 _ imm s_pc Hv1 Hag)
    (fun _ s2 _ HR _ => Hbnd rs1 k1 s2 Hne1 HR))
  iintro %s2 %rs2 %k2 %HR2 %Hc2 %HPC2 %Hg2
  have Hg : ∀ r : BitVec 5, r.toNat ≠ 0 →
      AxSymEngine3.gpr r rs2 = if r = a05 then blkW2 rs0 imm else AxSymEngine3.gpr r rs0 := by
    intro r Hr
    have h2 := Hg2 r Hr
    by_cases E : r = a05
    · rw [if_pos E] at h2
      rw [if_pos E]
      exact h2
    · rw [if_neg E] at h2
      rw [if_neg E]
      have h1 := Hg1 r Hr
      rw [if_neg E] at h1
      exact h2.trans h1
  iapply C $$ %s2 %rs2 %k2 %HR2 %Hc2 %HPC2 %Hg

end block

/-- The block's `axGA2` instance with the real protocol (Rocq `Local Instance blk_ga2`). -/
@[reducible] def blkGa2 {GF : BundledGFunctors.{0,0,0}} [AxannotGS GF] [AxlogG GF Hent]
    (GD0 : Gdexec) (γ : GName) : AxirisG GF :=
  axGA2 GD0 GName Unit (fun (γ : GName) (GD : Gdexec) (_ : Unit) (s : GSet Geid) => protInv γ GD s) γ

section blockGa2
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [pol : Axpol] [AxlogG GF Hent]
variable (GD0 : Gdexec) (γ : GName)
variable (img : Image) (i : Agent) (cpu : CPU)
variable (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
  (textAt4 : BitVec 64 → BitVec 32 → Prop)
variable (Hsp : SpineOk img ctrlOk textAt) (Hf4 : SpineFetch4 img ctrlOk textAt4)
variable (Hfix : textFixed GD0 i img)

include Hsp Hf4 Hfix in
/-- The block at the REAL Tier-A instance `axGA2` with the real protocol `protInv`. -/
theorem wpdBlockGa2 (pc : BitVec 64) (imm : BitVec 6) (s0 : Athread) (rs0 : RegFile) (k0 : Nat) :
    RetX cpu rs0 k0 s0 → ctrlOk rs0 → rs0 .PC = pc →
    textOkDB img ctrlOk textAt textAt4 pc true ICmv →
    textOkDB img ctrlOk textAt textAt4 (BitVec.addInt pc 2) true (ICaddiw imm) →
    ⊢ (∀ s' rs' k', ⌜RetX cpu rs' k' s'⌝ -∗ ⌜ctrlOk rs'⌝ -∗
         ⌜rs' .PC = blkEnd pc⌝ -∗
         ⌜∀ r : BitVec 5, r.toNat ≠ 0 →
            AxSymEngine3.gpr r rs' = if r = a05 then blkW2 rs0 imm else AxSymEngine3.gpr r rs0⌝ -∗
         @wpd hlc GF _ (blkGa2 GD0 γ) pol .MaybeStuck i s' (ΦRet (GF := GF) cpu (PBlk pc rs0 imm))) -∗
       @wpd hlc GF _ (blkGa2 GD0 γ) pol .MaybeStuck i s0 (ΦRet (GF := GF) cpu (PBlk pc rs0 imm)) :=
  @wpdBlockCmvCaddiw hlc GF _ (blkGa2 GD0 γ) pol img i cpu ctrlOk textAt textAt4 Hsp Hf4
    (HtextGa2 GD0 GName Unit _ γ img i Hfix)
    (fun GD ls k hc hx => HflowGa2 GD0 GName Unit _ γ img i
      (fun GD σ s e Hnin Hnw => protInvReadStep γ GD s e Hnin Hnw) GD ls k hc hx)
    pc imm s0 rs0 k0

end blockGa2


/-! ### Concrete instantiation at `AxEpiProbe`'s M-mode state -/

/-- c.mv a0, ra (0x8506) at `nvPc`; c.addiw a0, 1 (0x2505) at `nvPc + 2`; FINDING: at the
4-byte-ALIGNED `nvPc + 2` the model's fetch reads 4 bytes, so the image also covers the next
halfword (c.nop 0x0001). -/
def nv2Imm : BitVec 6 := 1#6

def nv2Img (a : Int) : Option (BitVec 8) :=
  if a = nvPc then some 0x06#8
  else if a = nvPc + 1 then some 0x85#8
  else if a = nvPc + 2 then some 0x05#8
  else if a = nvPc + 3 then some 0x25#8
  else if a = nvPc + 4 then some 0x01#8
  else if a = nvPc + 5 then some 0x00#8 else none

/-- The block's post `PBlk` as a boolean at the block end, at `rs0 := nvT`. -/
def nv2Final (_ : Unit) (t' : ExecSt) : Bool :=
  (t'.regs .PC == blkEnd (AxEpiProbe.w64 nvPc)) &&
  (AxSymEngine3.gpr a05 t'.regs == blkW2 nvT.regs nv2Imm) &&
  (AxSymEngine3.gpr ra5 t'.regs == AxSymEngine3.gpr ra5 nvT.regs)

/-- After the first instruction, BOTH ticks of the second. -/
noncomputable def nv2Mid (_ : Unit) (t1 : ExecSt) : Bool :=
  evb nv2Img nv2Final (riscvStep false) t1 && evb nv2Img nv2Final (riscvStep true) t1

theorem nv2BlockFalse : evb nv2Img nv2Mid (riscvStep false) nvT = true := by decide +kernel

theorem nv2BlockTrue : evb nv2Img nv2Mid (riscvStep true) nvT = true := by decide +kernel

theorem nv2Fetch2 : evb nv2Img (fun r _ => match r with
      | .F_RVC h => h == 0x2505#16
      | _ => false)
    (fetch ()) (tAt (nvPc + 2)) = true := by decide +kernel

theorem nv2DecodeExpand2 :
    evb nv2Img (fun r _ => match r with
      | .ExecuteAs (.ADDIW (imm, .Regidx a, .Regidx b)) =>
        imm == sign_extend (m := 12) nv2Imm && a == a05 && b == a05
      | _ => false)
      (ext_decode_compressed 0x2505#16 >>= execute) (tAt (nvPc + 2)) = true := by decide +kernel

theorem nv2Rf0 : rf0 (execute (ICaddiw nv2Imm)) :=
  rf0ExecuteADDIW a05 a05 (sign_extend (m := 12) nv2Imm)

theorem nv2BlkEnd : blkEnd (AxEpiProbe.w64 nvPc) = AxEpiProbe.w64 (nvPc + 4) := by decide +kernel

/-! ### The 4-byte arm on the real model: `add a0, ra, zero` (0x00008533) -/

def nv4Img (a : Int) : Option (BitVec 8) :=
  if a = nvPc then some 0x33#8
  else if a = nvPc + 1 then some 0x85#8
  else if a = nvPc + 2 then some 0x00#8
  else if a = nvPc + 3 then some 0x00#8 else none

def IAdd4 : instruction := .RTYPE (.Regidx 0#5, .Regidx ra5, .Regidx a05, .ADD)

def nv4Post (_ : Unit) (t' : ExecSt) : Bool :=
  (t'.regs .PC == AxEpiProbe.w64 (nvPc + 4)) &&
  (AxSymEngine3.gpr a05 t'.regs == AxSymEngine3.gpr ra5 nvT.regs)

theorem nv4StepFalse : evb nv4Img nv4Post (riscvStep false) nvT = true := by decide +kernel

theorem nv4StepTrue : evb nv4Img nv4Post (riscvStep true) nvT = true := by decide +kernel

theorem nv4Fetch : evb nv4Img (fun r _ => match r with
      | .F_Base w => w == 0x00008533#32
      | _ => false)
    (fetch ()) nvT = true := by decide +kernel

theorem nv4Decode : evb nv4Img (fun x _ => match x with
      | .RTYPE (.Regidx a, .Regidx b, .Regidx c, .ADD) => a == 0#5 && b == ra5 && c == a05
      | _ => false)
    (ext_decode 0x00008533#32) nvT = true := by decide +kernel

theorem nv4Nlpad : is_lpad_instruction IAdd4 = false := by decide +kernel

theorem nv4Rf0 : rf0 (execute IAdd4) := rf0ExecuteRTYPEADD 0#5 ra5 a05

/-- The checker's soundness turns each into the `EvA` premise itself. -/
theorem nv2Cert (tick : Bool) :
    EvA nv2Img (fun _ _ => False) (fun x t' => nv2Mid x t' = true) (riscvStep tick) nvT := by
  apply evbSound
  cases tick
  · exact nv2BlockFalse
  · exact nv2BlockTrue

theorem nv4Cert (tick : Bool) :
    EvA nv4Img (fun _ _ => False) (fun x t' => nv4Post x t' = true) (riscvStep tick) nvT := by
  apply evbSound
  cases tick
  · exact nv4StepFalse
  · exact nv4StepTrue

end Weak
