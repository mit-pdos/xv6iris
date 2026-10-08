/-
Weak: **S-mode X LEAVES for xv6's lock code, part 2: the WPd leaves** (continuation form, the
`AxCert4.XFence` / `XAmo` shape), all 4-BYTE, all through ONE generic bridge.

Rocq: `iris/AxLeafS2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`XCertT`: a boundary at `pc` holding the 4-byte word `w` that decodes to `ins`, whose `execute`
has a TLB-FRAMED certificate (`CertXT` — the data walk may fill the TLB, unlike
`AxCert4.CertX` / `CertAmo`, which are FALSE on a TLB miss) ⇒ the WPd, given the continuation at
the next boundary (PC + 4, GPRs by `ow`, regime kept, the data event's flow output).  Proof:
`spineCertXT` (AxDataX5) + `wpdInstrOfCert` (AxCert2).
`CertXTAnd`: a certificate at `C` is one at `C ∧ P` for a side predicate `P` of AxLeafS's
`pDep` class (the walk only touches the TLB) — so the LOAD certificates of AxDataX4 (at the
fetch regime `ctrlOkS`) serve at the data regime `ctrlOkSW`.

S-MODE INSTANCES at `ctrlOkSW` (section `xS`; spine `SpineOkTSW`, fetch `SpineFetch4TSW`):
`XLoadS` (`XLdS` = `ld`, `XLwS` = `lw`): read DEMONIC, rd := `ldRes u wd vs`; `XStoreS`
(`XSdS` = `sd`, `XSwS` = `sw`): bytes = `stBytes wd rs2`, the store class from the entry
release flag `r`; `XAmoswapS` (`amoswap.w{.aq}`): exclusive read DEMONIC, exclusive write of
rs2's low word, rd := the sign-extended read value (`CertXTAmoswapS`); `XFenceSW` (`fence rw,w`,
`AxCert4.XFence` at the data regime; the continuation learns the release flag is ARMED).
Premises left per leaf: the decode fact of the word (`Hdec`, an `EvA` fact) and the page facts
(`textAt4S` / `dataAtS`); per instance: the bridge's `Htext` / `Hflow` / `Hloc` / `HG` / `Hmid`
and the data-region side conditions `HnoRmw` (loads) / `HnoSplit` (AMO).  NOT HERE (as Rocq):
the SIE-agnostic (interrupt-arm) versions.

## Deviations from Rocq

1. O2 STAGE C (as `AxCert2` deviation 1): the section premise `Hntext` (generic `XCertT`; the
   `loads` section) is DROPPED — `wpdInstrOfCertM` no longer takes it.
2. Q7 (as `AxCert4` / `AxDataX5` deviation 1): every 4-byte leaf takes
   `Hsf : sfAnnB 32 w = false` right after `Htx : textAt4 pc w` (`spineCertXT` needs it).
3. SPELLING as AxCert4 / AxDataX4 / AxLeafS: `register_lookup PC rs = pc` ↦ `rs .PC = pc`,
   `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg`, `uint rd ≠ 0` ↦ `rd.toNat ≠ 0`,
   `dok (uint pa) (Z.to_nat wd)` ↦ `dok (paZ pa) wd` with `wd : Nat` (`vmemWidth wd`, Rocq's
   `(1 ≤ wd ≤ 8)%Z` ↦ `1 ≤ wd ∧ wd ≤ 8`), `add_vec x (sign_extend' 64 imm)` ↦
   `x + sign_extend (m := 64) imm`, `zeros' 64` ↦ `zeros (n := 64)`, `ld_res` ↦ `ldRes`,
   `st_bytes` ↦ `stBytes`, `ow_ld` ↦ `owLd`, `ak_plain` ↦ `AxDataX.akPlain`, `CS d b r` ↦
   `⟨d, b, r⟩`, `WPd … @ MaybeStuck; i {{ Φ }}` ↦ `wpdM rvwmoCatConsistent .MaybeStuck i … Φ`,
   `Interface.Ret tt` ↦ `.pure ()`; `iProp` statements are `⊢ … -∗ …`.
4. Section variables / hypotheses are explicit arguments (each declaration takes those it uses,
   as Rocq's section discharge).  Rocq's `Definition`s `X_ld_S` … `X_sw_S`, `X_fence_SW`
   (partial applications) are theorems typed `type_of%`.

**Rocq → Lean name map.**  `CertXT_and` `CertXTAnd`, `X_certT` `XCertT`, `X_load_S` `XLoadS`,
`X_ld_S` `XLdS`, `X_lw_S` `XLwS`, `X_store_S` `XStoreS`, `X_sd_S` `XSdS`, `X_sw_S` `XSwS`,
`X_amoswap_S` `XAmoswapS`, `ctrl_ok_SW_priv` `ctrlOkSWPriv`, `X_fence_SW` `XFenceSW`.  None is
in the duplicated-name table.

**Dropped:** nothing (Rocq 11 definitions/lemmas; Lean 11).  **Not ported:** the section
notations `boundary` / `decodes` / `Hb_at` / `WPK` / `img` / `ctrl_ok` / `Hsp` / `Hf4` (written
out) and the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxLeafS
import Weak.AxDataX5
import Weak.AxCert2

namespace Weak

open Iris Iris.BI Iris.ProofMode MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `CertXT_and`: a certificate at `C` is one at `C ∧ P`. -/
theorem CertXTAnd (img : Image) (dok : Int → Nat → Prop) (kind : Dkind) (C P : RegFile → Prop)
    (HP : pDep P) (rs : RegFile) (pc : BitVec 64) (ins : instruction)
    (ow : Cst → Option (BitVec 5 × BitVec 64)) (s0 : Cst) (PX : Cst → Prop) :
    CertXT img dok kind C rs pc ins ow s0 PX →
    CertXT img dok kind (fun rs => C rs ∧ P rs) rs pc ins ow s0 PX := by
  intro H tpc ⟨hc, hp⟩ HPC Hnpc Hag
  refine CertMono img dok kind _ _ _ _ _ _ tpc (fun _ _ _ h => h) ?_ (H tpc hc HPC Hnpc Hag)
  rintro s x t' ⟨rfl, HPX, t0, Hfr, Hc0, rfl⟩
  exact ⟨rfl, HPX, t0, Hfr, ⟨Hc0, pTlbFrame P HP _ _ Hfr hp⟩, rfl⟩

/-! # 1. The generic TLB-framed X leaf -/

section xT
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (img : Image) (i : Agent) (cpu : CPU)
variable (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
  (textAt4 : BitVec 64 → BitVec 32 → Prop)
variable (Hsp : SpineOkT img ctrlOk textAt) (Hf4 : SpineFetch4T img ctrlOk textAt4)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
variable (Hloc : ∀ GD ls k, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢
    |==> ∃ ls', AxirisG.localInterp GD i (k + 1) ls')
variable (G : Gdexec → Prop)
  (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (Φ : Athread → IProp GF)
variable (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
  ⊢ postLifting Φ i s)
variable (dok : Int → Nat → Prop) (kind : Dkind) (Out : Nat → List (BitVec 8) → IProp GF)
variable (HnoRmw : kind = .DKLd → ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n → ¬ dok base n⌝)
variable (HnoSplit : kind = .DKRmw → ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base n → ¬ dok base n⌝)

include Hsp Hf4 Htext Hflow Hloc HG Hmid HnoRmw HnoSplit in
/-- Rocq `X_certT`: THE GENERIC TLB-FRAMED X LEAF. -/
theorem XCertT (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (w : BitVec 32)
    (ins : instruction) (ow : Cst → Option (BitVec 5 × BitVec 64)) (d0 : Cdata) (r0 : Bool)
    (PX : Cst → Prop)
    (HRet : RetX cpu rs k s) (Hctrl : ctrlOk rs) (HPC : rs .PC = pc) (Htx : textAt4 pc w)
    (Hsf : sfAnnB 32 w = false)
    (Hdec : ∀ t : ExecSt, ctrlOk t.regs →
      EvA img (fun _ _ => False) (fun x t' => x = ins ∧ t' = t) (ext_decode w) t)
    (How : ∀ s', PX s' → owOk (ow s')) (HPXb : ∀ s', PX s' → s'.csB = .BInf)
    (Hcert : CertXT img dok kind ctrlOk rs pc ins ow ⟨d0, .BInf, r0⟩ PX)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) :
    ⊢ CRes dok kind i Out d0 -∗
      (∀ (s' : Cst) (t' : ExecSt) (rs' : RegFile) (ib' : Ibch) (k' : Nat), ⌜PX s'⌝ -∗
        ⌜GoodC ctrlOk false rs pc none (ow s') t'.regs⌝ -∗
        ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗ CRes dok kind i Out s'.csD -∗
        wpdM rvwmoCatConsistent .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM rvwmoCatConsistent .MaybeStuck i s Φ := by
  have Hc : ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
      AxCert.Cert img dok kind (fun _ _ _ => False)
        (fun s' _ t' => PX s' ∧ GoodC ctrlOk false rs pc none (ow s') t'.regs)
        ⟨d0, .BInf, r0⟩ (riscvStep tick) t :=
    fun tick t Hag => spineCertXT img dok kind ctrlOk textAt textAt4 Hsp Hf4 rs pc w ins ow d0
      r0 PX Hctrl HPC Htx Hsf Hdec How HPXb Hcert tick t Hag
  have Hbr : CRes dok kind i Out d0 ⊢
      CResM rvwmoCatConsistent dok kind i Out (⟨d0, .BInf, r0⟩ : Cst).csD := .rfl
  iintro D C
  ihave D := Hbr $$ D
  iapply (wpdInstrOfCertM rvwmoCatConsistent img dok kind i Φ cpu G HG Hmid Htext Hflow Hloc
    HnoRmw HnoSplit Out _ ⟨d0, .BInf, r0⟩ rs k s HRet trivial Hb Hc) $$ D
  iintro %s' %t' %rs' %ib' %k' %HQ %Hag %_ HD
  obtain ⟨HP, HG'⟩ := HQ
  iapply C $$ %s' %t' %rs' %ib' %k' %HP %HG' %Hag HD

end xT

/-! # 2. The S-mode instances at the data regime `ctrlOkSW` -/

section xS
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
  (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
  (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (i : Agent) (cpu : CPU)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i (imgS σi)⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes (imgS σi) base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
variable (Hloc : ∀ GD ls k, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢
    |==> ∃ ls', AxirisG.localInterp GD i (k + 1) ls')
variable (G : Gdexec → Prop)
  (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (Φ : Athread → IProp GF)
variable (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
  ⊢ postLifting Φ i s)
variable (dok : Int → Nat → Prop) (Out : Nat → List (BitVec 8) → IProp GF)

/-! ## Loads (`ld` / `lw`) -/

section loads
variable (HnoRmw : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n → ¬ dok base n⌝)

include hmode hasid hppn Htext Hflow Hloc HG Hmid HnoRmw in
/-- Rocq `X_load_S`. -/
theorem XLoadS (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (w32 : BitVec 32)
    (imm : BitVec 12) (rs1 rd : BitVec 5) (u : Bool) (wd : Nat) (va pa : BitVec 64)
    (HRet : RetX cpu rs k s) (Hctrl : ctrlOkSW T satp0 rs) (HPC : rs .PC = pc)
    (Htx : textAt4S σi T pc w32) (Hsf : sfAnnB 32 w32 = false)
    (Hdec : ∀ t : ExecSt, ctrlOkSW T satp0 t.regs →
      EvA (imgS σi) (fun _ _ => False)
        (fun x t' => x = .LOAD (imm, .Regidx rs1, .Regidx rd, u, wd) ∧ t' = t) (ext_decode w32) t)
    (Hrd : rd.toNat ≠ 0) (Hvw : vmemWidth wd) (Hw : 1 ≤ wd ∧ wd ≤ 8)
    (Hva : va = gprVal rs rs1 + sign_extend (m := 64) imm)
    (Hda : dataAtS σi T (.Load .Data) va wd pa) (Hdok : dok (paZ pa) wd)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) :
    ⊢ Fld dok i Out -∗
      (∀ (vs : List (BitVec 8)) (t' : ExecSt) (rs' : RegFile) (ib' : Ibch) (k' : Nat),
        ⌜vs.length = wd⌝ -∗
        ⌜GoodC (ctrlOkSW T satp0) false rs pc none (some (rd, ldRes u wd vs)) t'.regs⌝ -∗
        ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗ (∃ kd, Out kd vs) -∗
        wpdM rvwmoCatConsistent .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM rvwmoCatConsistent .MaybeStuck i s Φ := by
  have Hcert : CertXT (imgS σi) dok .DKLd (ctrlOkSW T satp0) rs pc
      (.LOAD (imm, .Regidx rs1, .Regidx rd, u, wd)) (owLd rd u wd) ⟨.CPend, .BInf, false⟩
      (fun s' => ∃ vs, s' = ⟨.CLd vs, .BInf, false⟩ ∧ vs.length = wd) :=
    CertXTAnd (imgS σi) dok .DKLd (ctrlOkS T satp0) pmpW pmpWDep _ _ _ _ _ _
      (CertXTLoadS σi T satp0 hmode hasid hppn dok rs pc imm rs1 rd u wd va pa false
        Hrd Hvw Hw.1 Hw.2 Hva Hda Hdok)
  have How : ∀ s', (∃ vs, s' = (⟨.CLd vs, .BInf, false⟩ : Cst) ∧ vs.length = wd) →
      owOk (owLd rd u wd s') := by
    rintro _ ⟨_, rfl, _⟩
    exact Hrd
  have HPXb : ∀ s', (∃ vs, s' = (⟨.CLd vs, .BInf, false⟩ : Cst) ∧ vs.length = wd) →
      s'.csB = .BInf := by
    rintro _ ⟨_, rfl, _⟩
    rfl
  have Hbr : Fld dok i Out ⊢ CRes dok .DKLd i Out .CPend := .rfl
  iintro F C
  ihave F := Hbr $$ F
  iapply (XCertT (imgS σi) i cpu (ctrlOkSW T satp0) (textAtS σi T) (textAt4S σi T)
    (SpineOkTSW σi T satp0 hmode hasid hppn) (SpineFetch4TSW σi T satp0 hmode hasid hppn)
    Htext Hflow Hloc G HG Φ Hmid dok .DKLd Out (fun _ => HnoRmw) (fun h => nomatch h)
    s rs k pc w32 _ (owLd rd u wd) .CPend false _ HRet Hctrl HPC Htx Hsf Hdec How HPXb Hcert
    Hb) $$ F
  iintro %s' %t' %rs' %ib' %k' %HP %HG' %Hag HD
  obtain ⟨vs, rfl, Hlen⟩ := HP
  have Hbr2 : CRes dok .DKLd i Out (⟨.CLd vs, .BInf, false⟩ : Cst).csD ⊢
      iprop(∃ kd, Out kd vs) := .rfl
  ihave HD := Hbr2 $$ HD
  iapply C $$ %vs %t' %rs' %ib' %k' %Hlen %HG' %Hag HD

include hmode hasid hppn Htext Hflow Hloc HG Hmid HnoRmw in
/-- Rocq `X_ld_S`. -/
theorem XLdS (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (w32 : BitVec 32)
    (imm : BitVec 12) (rs1 rd : BitVec 5) (va pa : BitVec 64) :
    type_of% (XLoadS (hlc := hlc) (GF := GF) σi T satp0 hmode hasid hppn i cpu Htext Hflow Hloc
      G HG Φ Hmid dok Out HnoRmw s rs k pc w32 imm rs1 rd false 8 va pa) :=
  XLoadS σi T satp0 hmode hasid hppn i cpu Htext Hflow Hloc G HG Φ Hmid dok Out HnoRmw
    s rs k pc w32 imm rs1 rd false 8 va pa

include hmode hasid hppn Htext Hflow Hloc HG Hmid HnoRmw in
/-- Rocq `X_lw_S`. -/
theorem XLwS (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (w32 : BitVec 32)
    (imm : BitVec 12) (rs1 rd : BitVec 5) (va pa : BitVec 64) :
    type_of% (XLoadS (hlc := hlc) (GF := GF) σi T satp0 hmode hasid hppn i cpu Htext Hflow Hloc
      G HG Φ Hmid dok Out HnoRmw s rs k pc w32 imm rs1 rd false 4 va pa) :=
  XLoadS σi T satp0 hmode hasid hppn i cpu Htext Hflow Hloc G HG Φ Hmid dok Out HnoRmw
    s rs k pc w32 imm rs1 rd false 4 va pa

end loads

/-! ## Stores (`sd` / `sw`); `r` = the certificate's release-pending flag at entry (true after
an armed `fence rw,w`: the store is then `WCrel`, AxCert.wclsArmed) -/

include hmode hasid hppn Htext Hflow Hloc HG Hmid in
/-- Rocq `X_store_S`. -/
theorem XStoreS (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (w32 : BitVec 32)
    (imm : BitVec 12) (rs2 rs1 : BitVec 5) (wd : Nat) (va pa : BitVec 64) (r : Bool)
    (HRet : RetX cpu rs k s) (Hctrl : ctrlOkSW T satp0 rs) (HPC : rs .PC = pc)
    (Htx : textAt4S σi T pc w32) (Hsf : sfAnnB 32 w32 = false)
    (Hdec : ∀ t : ExecSt, ctrlOkSW T satp0 t.regs →
      EvA (imgS σi) (fun _ _ => False)
        (fun x t' => x = .STORE (imm, .Regidx rs2, .Regidx rs1, wd) ∧ t' = t) (ext_decode w32) t)
    (Hvw : vmemWidth wd) (Hw : 1 ≤ wd ∧ wd ≤ 8)
    (Hva : va = gprVal rs rs1 + sign_extend (m := 64) imm)
    (Hda : dataAtS σi T (.Store .Data) va wd pa) (Hdok : dok (paZ pa) wd)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) :
    ⊢ Fst dok i Out -∗
      (∀ (t' : ExecSt) (rs' : RegFile) (ib' : Ibch) (k' : Nat),
        ⌜GoodC (ctrlOkSW T satp0) false rs pc none none t'.regs⌝ -∗
        ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
        (∃ kd, Out kd (stBytes wd (gprVal rs rs2))) -∗
        wpdM rvwmoCatConsistent .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM rvwmoCatConsistent .MaybeStuck i s Φ := by
  have Hcert := CertXTStoreS σi T satp0 hmode hasid hppn dok rs pc imm rs2 rs1 wd va pa r
    Hvw Hw.1 Hw.2 Hva Hda Hdok
  have Hbr : Fst dok i Out ⊢ CRes dok .DKSt i Out .CPend := .rfl
  iintro F C
  ihave F := Hbr $$ F
  iapply (XCertT (imgS σi) i cpu (ctrlOkSW T satp0) (textAtS σi T) (textAt4S σi T)
    (SpineOkTSW σi T satp0 hmode hasid hppn) (SpineFetch4TSW σi T satp0 hmode hasid hppn)
    Htext Hflow Hloc G HG Φ Hmid dok .DKSt Out (fun h => nomatch h) (fun h => nomatch h)
    s rs k pc w32 _ (fun _ => none) .CPend r _ HRet Hctrl HPC Htx Hsf Hdec
    (fun _ _ => trivial) (fun _ h => by subst h; rfl) Hcert Hb) $$ F
  iintro %s' %t' %rs' %ib' %k' %HP %HG' %Hag HD
  subst HP
  have Hbr2 : CRes dok .DKSt i Out
      (⟨.CSt (stBytes wd (gprVal rs rs2)) (wcls AxDataX.akPlain r), .BInf, false⟩ : Cst).csD ⊢
      iprop(∃ kd, Out kd (stBytes wd (gprVal rs rs2))) := .rfl
  ihave HD := Hbr2 $$ HD
  iapply C $$ %t' %rs' %ib' %k' %HG' %Hag HD

include hmode hasid hppn Htext Hflow Hloc HG Hmid in
/-- Rocq `X_sd_S`. -/
theorem XSdS (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (w32 : BitVec 32)
    (imm : BitVec 12) (rs2 rs1 : BitVec 5) (va pa : BitVec 64) (r : Bool) :
    type_of% (XStoreS (hlc := hlc) (GF := GF) σi T satp0 hmode hasid hppn i cpu Htext Hflow Hloc
      G HG Φ Hmid dok Out s rs k pc w32 imm rs2 rs1 8 va pa r) :=
  XStoreS σi T satp0 hmode hasid hppn i cpu Htext Hflow Hloc G HG Φ Hmid dok Out
    s rs k pc w32 imm rs2 rs1 8 va pa r

include hmode hasid hppn Htext Hflow Hloc HG Hmid in
/-- Rocq `X_sw_S`. -/
theorem XSwS (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (w32 : BitVec 32)
    (imm : BitVec 12) (rs2 rs1 : BitVec 5) (va pa : BitVec 64) (r : Bool) :
    type_of% (XStoreS (hlc := hlc) (GF := GF) σi T satp0 hmode hasid hppn i cpu Htext Hflow Hloc
      G HG Φ Hmid dok Out s rs k pc w32 imm rs2 rs1 4 va pa r) :=
  XStoreS σi T satp0 hmode hasid hppn i cpu Htext Hflow Hloc G HG Φ Hmid dok Out
    s rs k pc w32 imm rs2 rs1 4 va pa r

/-! ## The AMO (`amoswap.w{.aq}`) -/

section amo
variable (HnoSplit : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base n → ¬ dok base n⌝)

include hmode hasid hppn Htext Hflow Hloc HG Hmid HnoSplit in
/-- Rocq `X_amoswap_S`. -/
theorem XAmoswapS (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (w32 : BitVec 32)
    (aq : Bool) (rs2 rs1 rd : BitVec 5) (va pa : BitVec 64)
    (HRet : RetX cpu rs k s) (Hctrl : ctrlOkSW T satp0 rs) (HPC : rs .PC = pc)
    (Htx : textAt4S σi T pc w32) (Hsf : sfAnnB 32 w32 = false)
    (Hdec : ∀ t : ExecSt, ctrlOkSW T satp0 t.regs →
      EvA (imgS σi) (fun _ _ => False)
        (fun x t' => x = .AMO (.AMOSWAP, aq, false, .Regidx rs2, .Regidx rs1, 4, .Regidx rd) ∧
          t' = t) (ext_decode w32) t)
    (Hrd : rd.toNat ≠ 0)
    (Hva : va = gprVal rs rs1 + zeros (n := 64))
    (Hda : dataAtS σi T (accAmo aq) va 4 pa) (Hdok : dok (paZ pa) 4)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) :
    ⊢ Fst dok i Out -∗
      (∀ (vs : List (BitVec 8)) (t' : ExecSt) (rs' : RegFile) (ib' : Ibch) (k' : Nat),
        ⌜vs.length = 4⌝ -∗
        ⌜GoodC (ctrlOkSW T satp0) false rs pc none (some (rd, amoLdv 4 vs)) t'.regs⌝ -∗
        ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
        (∃ kd, Out kd (AxDataX.wrb 4 (amoStv 4 (gprVal rs rs2)))) -∗
        wpdM rvwmoCatConsistent .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM rvwmoCatConsistent .MaybeStuck i s Φ := by
  have Hcert := CertXTAmoswapS σi T satp0 hmode hasid hppn dok rs pc aq rs2 rs1 rd va pa false
    Hrd Hva Hda Hdok
  have How : ∀ s', (∃ vs, s' = (⟨.CRmw aq false vs (AxDataX.wrb 4 (amoStv 4 (gprVal rs rs2)))
      (wcls akXc false), .BInf, false⟩ : Cst) ∧ vs.length = 4) → owOk (owAmo rd s') := by
    rintro _ ⟨_, rfl, _⟩
    exact Hrd
  have HPXb : ∀ s', (∃ vs, s' = (⟨.CRmw aq false vs (AxDataX.wrb 4 (amoStv 4 (gprVal rs rs2)))
      (wcls akXc false), .BInf, false⟩ : Cst) ∧ vs.length = 4) → s'.csB = .BInf := by
    rintro _ ⟨_, rfl, _⟩
    rfl
  have Hbr : Fst dok i Out ⊢ CRes dok .DKRmw i Out .CPend := .rfl
  iintro F C
  ihave F := Hbr $$ F
  iapply (XCertT (imgS σi) i cpu (ctrlOkSW T satp0) (textAtS σi T) (textAt4S σi T)
    (SpineOkTSW σi T satp0 hmode hasid hppn) (SpineFetch4TSW σi T satp0 hmode hasid hppn)
    Htext Hflow Hloc G HG Φ Hmid dok .DKRmw Out (fun h => nomatch h) (fun _ => HnoSplit)
    s rs k pc w32 _ (owAmo rd) .CPend false _ HRet Hctrl HPC Htx Hsf Hdec How HPXb Hcert
    Hb) $$ F
  iintro %s' %t' %rs' %ib' %k' %HP %HG' %Hag HD
  obtain ⟨vs, rfl, Hlen⟩ := HP
  have Hbr2 : CRes dok .DKRmw i Out (⟨.CRmw aq false vs (AxDataX.wrb 4 (amoStv 4 (gprVal rs rs2)))
      (wcls akXc false), .BInf, false⟩ : Cst).csD ⊢
      iprop(∃ kd, Out kd (AxDataX.wrb 4 (amoStv 4 (gprVal rs rs2)))) := .rfl
  ihave HD := Hbr2 $$ HD
  iapply C $$ %vs %t' %rs' %ib' %k' %Hlen %HG' %Hag HD

end amo

/-! ## `fence rw,w` at the data regime -/

omit [InvGS_gen hlc GF] [AxirisG GF] [Axpol] in
/-- Rocq `ctrl_ok_SW_priv`. -/
theorem ctrlOkSWPriv (rs : RegFile) : ctrlOkSW T satp0 rs → rs .cur_privilege = .Supervisor :=
  fun h => h.1.1

include hmode hasid hppn Htext Hflow Hloc HG Hmid in
/-- Rocq `X_fence_SW`. -/
theorem XFenceSW :
    type_of% (XFence (hlc := hlc) (GF := GF) (imgS σi) i cpu (ctrlOkSW T satp0) (textAtS σi T)
      (textAt4S σi T) (SpineOkTSW σi T satp0 hmode hasid hppn)
      (SpineFetch4TSW σi T satp0 hmode hasid hppn) (ctrlOkSWPriv T satp0) Htext Hflow Hloc G HG
      Φ Hmid) :=
  XFence (imgS σi) i cpu (ctrlOkSW T satp0) (textAtS σi T) (textAt4S σi T)
    (SpineOkTSW σi T satp0 hmode hasid hppn) (SpineFetch4TSW σi T satp0 hmode hasid hppn)
    (ctrlOkSWPriv T satp0) Htext Hflow Hloc G HG Φ Hmid

end xS

end Weak
