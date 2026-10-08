/-
Weak: **the remaining positional leaves `push_off` / `pop_off` need**, at the joint instance
Ixv6 (S-mode data regime `ctrlOkSW`, WARM TLB).

Rocq: `iris/AxSpinPOx.v` @ xxvzwolszwmp.

## The Rocq header, in substance (as restated under Stage C)

§1 pure: `CertC` facts of `andi` / `srli` with symbolic register values, and the read
   footprints (`rfF`) of andi, srli, JAL (any link register) and every BTYPE.
§2 the PRIVATE 4-BYTE cpu FIELDS (`cpus[i].noff` / `cpus[i].intena`, hart `i`'s private bytes):
   a store leaf `XxSt4` (Phase 1c's private write rule; the continuation learns
   `graphData (i, k)` = the stored bytes), and a load leaf `XxLd4` through the FRAME rule (the
   continuation learns the physical bytes = `graphValue (i, k)`; NO reload annotation is
   deposited — the field's latest earlier store is generally outside the window).
   Row premises: every write of hart `i` at the field is at most 4 bytes (`rowWle`); no fused
   RMW of 4 bytes at the field (`noRmwn`).
§3 `XxPin`: a register-only / control instruction whose physical next pc `tgtOf ot pc is_rvc`
   is the VA `nxt` the caller expects (Rocq: FOLLOWED BY A PINNED FETCH; see deviation 3).

## Deviations from Rocq

1. O2 STAGE C COUNT SHIFT (`AxSpinE6` deviation 3): the instruction's fetch consumes NO row item.
   * `XxSt4`: the store is AT `k` (Rocq `S k`): the fact is `graphData (i, k)`; continuation at
     `k + 1` (Rocq `k + 2`); premise `k + 1 ≤ LEN` (Rocq `k + 2 ≤ LEN`).  Rocq's premise "row
     item `k` (the fetch) is not a write" is DROPPED (under Stage C row item `k` IS the store,
     so it would be unsatisfiable); its one use (ruling out `kd = k`) is now arithmetic.
   * `XxLd4`: the load is AT `k`: `graphValue (i, k)`; continuation at `k + 1`; premise
     `k + 1 ≤ LEN`.  Rocq's premise "row item `k` (the fetch) is not a 4-byte read" is DROPPED
     for the same reason.  Rocq's `Hntext` assertion is not built (`XBk` does not take it,
     `AxSpinE4`); the premise `¬ L.xlText (paZ pa)` is kept for caller compatibility and is
     unused (as `AxSpinE6.XxLd`).
2. INSTANCES / SECTION (as `AxSpinE6` deviation 2): `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]`
   (any `hlc`); the local instances `xf_pol`/`xf_G`/`xp_pol`/`xp_G` are inlined as `xv6Pol GT` /
   `AxSpinX2.xG L GT nm`, passed with `@`.  Section variables are explicit arguments in
   `AxSpinE6`'s order (`L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid`).
   `HL0p`/`HGex0p` take `GT i` / `GT`, `Hmid0p` takes `L GT nm i Ψ HΨmid`, `ctrlSeip` takes
   `σi T satp0 hmode hasid hppn` (Rocq section context).
3. `XxPin` RESTATED UNDER STAGE C (Q20', provisional Option V, `notes/weak-port-q20-offrow.md`
   §C.2 item 4; protocol "Cross-file facts" Q20' entry).  Rocq's `Xx_pin` pins the NEXT FETCH by
   a row item (`Hpin`: row item `S k` reads `nn ∈ {2,4}` bytes at `pn`, `fpin T stv nxt pn`),
   calls the continuation when `tgt_of ot pc is_rvc = nxt` and proves every other target
   row-stuck through `AxSpinE3.wpd_offrowM` from the Sail section premise `va_first_read`.
   Under Stage C no row item pins a fetch, so that off-row argument has no Lean counterpart
   (as `AxSpinE6.XxRet`).  The Lean `XxPin` keeps `nxt` and the continuation's conjunct
   `tgtOf ot pc is_rvc = nxt`, but takes it as a PREMISE `Htgt : tgtOf ot pc is_rvc = nxt` (the
   caller decides the arm from a GRAPH VALUE pin — e.g. PO1's `beqz` from `graphValue … = some vn`
   — a plain case on the value, no stuck branch).  DROPPED: `pn`, `nn`, `Hpin`, `Hn`, the `fpin`
   premise, the section context `stv` and `va_first_read` ("Stage C: no row item pins a fetch").
   The continuation is at `k` (Rocq `k + 1`) and the length premise is `k < LEN` (Rocq
   `k + 2 ≤ LEN`; `XxReg`'s premise).
4. TYPES / SPELLING (`AxSpinE6` deviation 1): `uint P` ↦ `paZ P`; `uint rd ≠ 0` ↦ `rd.toNat ≠ 0`;
   `add_vec (gpr_val rs rs1) (sign_extend' 64 imm)` ↦ `gprVal rs rs1 + sign_extend (m := 64) imm`;
   `and_vec` ↦ `&&&`; `subrange_vec_dec shamt (log2_xlen - 1) 0` ↦
   `Sail.BitVec.extractLsb shamt (Functions.log2_xlen -i 1) 0`; `l !! k` ↦ `l[k]?`;
   `register_lookup PC rs` ↦ `rs .PC`; `Interface.Ret tt` ↦ `.pure ()`; `length vs = Z.to_nat 4`
   ↦ `vs.length = 4`.  `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg`.
5. The trailing `Print Assumptions` lines are not ported (the lint's axiom check covers them).

**Rocq → Lean name map.**  `cert_andi` `certAndi`, `cert_srli` `certSrli`, `rfF_andi` `rfFAndi`,
`rfF_srli` `rfFSrli`, `rfF_wXr` `rfFWXr`, `rfF_jal` `AxSpinPOx.rfFJal` (duplicated name),
`rfF_btype` `rfFBtype`, `vw4` `AxSpinPOx.vw4` (duplicated name), `row_wle` `rowWle`, `no_rmwn`
`noRmwn`, `dok_fld` `dokFld`, `Fst_fld` `FstFld`, `OutLdF` `OutLdF`, `Fld_fld` `FldFld`, `HL0p`
`HL0p`, `HGex0p` `HGex0p`, `Hmid0p` `Hmid0p`, `ctrl_seip` `ctrlSeip`, `Xx_st4` `XxSt4`, `Xx_ld4`
`XxLd4`, `Xx_pin` `XxPin` (restated, deviation 3).  The local instances `xf_pol`, `xf_G`,
`xp_pol`, `xp_G` are inlined (deviation 2).  No Lean-only declarations.

**Dropped:** the section context `stv` and `va_first_read` (deviation 3).  Rocq 21
definitions/lemmas (+ 4 local instances); Lean 21.
-/
import Weak.AxSpinPOr
import Weak.AxSymCtl4

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. Certificates and footprints -/

section certs
variable (ctrlOk : RegFile → Prop)

/-- Rocq `cert_andi`. -/
theorem certAndi (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (rs1 rd : BitVec 5)
    (imm : BitVec 12) :
    rd.toNat ≠ 0 →
    CertC ctrlOk rs pc is_rvc (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ANDI)) none
      (some (rd, gprVal rs rs1 &&& sign_extend (m := 64) imm)) := by
  intro _ s_pc _ _ _ Hag
  rw [execExecuteITYPEANDIGpr]
  unfold gprAndiVal
  have h : s_pc.gpr rs1 = gprVal rs rs1 := gprValAgree _ _ rs1 Hag
  rw [h]
  rfl

/-- Rocq `cert_srli`. -/
theorem certSrli (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (rs1 rd : BitVec 5)
    (shamt : BitVec 6) :
    rd.toNat ≠ 0 →
    CertC ctrlOk rs pc is_rvc (.SHIFTIOP (shamt, .Regidx rs1, .Regidx rd, .SRLI)) none
      (some (rd, shift_bits_right (gprVal rs rs1)
        (Sail.BitVec.extractLsb shamt (Functions.log2_xlen -i 1) 0))) := by
  intro _ s_pc _ _ _ Hag
  rw [execExecuteSHIFTIOPSRLIGpr]
  unfold gprSrliVal gprSrc
  have h : s_pc.gpr rs1 = gprVal rs rs1 := gprValAgree _ _ rs1 Hag
  rw [h]
  rfl

end certs

/-- Rocq `rfF_andi`. -/
theorem rfFAndi (rs1 rd : regidx) (imm : BitVec 12) : rfF (execute (.ITYPE (imm, rs1, rd, .ANDI))) := by
  cases rs1; cases rd
  refine rfFOfRf0 _ ?_
  show rf0 (execute_ITYPE imm (.Regidx _) (.Regidx _) .ANDI)
  unfold execute_ITYPE
  ax_sym2_rf0_solve

/-- Rocq `rfF_srli`. -/
theorem rfFSrli (rs1 rd : regidx) (shamt : BitVec 6) :
    rfF (execute (.SHIFTIOP (shamt, rs1, rd, .SRLI))) := by
  cases rs1; cases rd
  refine rfFOfRf0 _ ?_
  show rf0 (execute_SHIFTIOP shamt (.Regidx _) (.Regidx _) .SRLI)
  unfold execute_SHIFTIOP
  ax_sym2_rf0_solve

/-- Rocq `rfF_wXr`. -/
theorem rfFWXr (rd : regidx) (v : BitVec 64) : rfF (wX_bits rd v) := by
  cases rd
  exact rfFOfRf0 _ (rf0WXBits _ _)

/-- Rocq `rfF_jal` (duplicated name: file-qualified). -/
theorem AxSpinPOx.rfFJal (imm : BitVec 21) (rd : regidx) : rfF (execute (.JAL (imm, rd))) := by
  show rfF (execute_JAL imm rd)
  unfold execute_JAL get_next_pc
  refine rfFBind _ _ (rfFReadReg _ (AxSymEngine2.notPin _ (by decide) (by decide))) (fun _ => ?_)
  refine rfFBind _ _ (rfFReadReg _ (AxSymEngine2.notPin _ (by decide) (by decide))) (fun _ => ?_)
  refine rfFBind _ _ (rfFJumpTo _) (fun r => ?_)
  cases r
  · exact rfFBind0 _ _ (rfFWXr _ _) trivial
  all_goals exact trivial

/-- Rocq `rfF_btype`. -/
theorem rfFBtype (imm : BitVec 13) (rs2 rs1 : regidx) (op : bop) :
    rfF (execute (.BTYPE (imm, rs2, rs1, op))) := by
  cases rs1; cases rs2
  show rfF (execute_BTYPE imm (.Regidx _) (.Regidx _) op)
  unfold execute_BTYPE
  refine rfFBind _ _ ?_ (fun taken => ?_)
  · cases op <;>
      exact rfFBind _ _ (rfFOfRf0 _ (rf0RXBits _)) (fun _ =>
        rfFBind _ _ (rfFOfRf0 _ (rf0RXBits _)) (fun _ => trivial))
  · cases taken
    · exact trivial
    · exact rfFBind _ _ (rfFReadReg _ (AxSymEngine2.notPin _ (by decide) (by decide)))
        (fun _ => rfFJumpTo _)

/-- Rocq `vw4` (duplicated name: file-qualified). -/
theorem AxSpinPOx.vw4 : vmemWidth 4 := Or.inr (Or.inr (Or.inl rfl))

/-- Rocq `row_wle`: every write of the row at `pa` is at most `n` bytes. -/
def rowWle (row : List Lbl) (pa : Int) (n : Nat) : Prop :=
  ∀ (k : Nat) (lb : Lbl) (rl : Bool) (m : Nat), row[k]? = some lb →
    aidentWr (aident lb) = some (rl, pa, m) → m ≤ n

/-- Rocq `no_rmwn`: no fused RMW of `n` bytes at `pa` in the row. -/
def noRmwn (row : List Lbl) (pa : Int) (n : Nat) : Prop :=
  ∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (m : Nat), row[k]? = some lb →
    aident lb = .IRmw aq rl pa m → m ≠ n

/-! # 2. The private fields -/

/-- Rocq `dok_fld`. -/
def dokFld (pa : Int) (n : Nat) : Int → Nat → Prop := fun base m => base = pa ∧ m = n

section fld
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

/-- Rocq `Fst_fld`. -/
theorem FstFld (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (i : Agent) (pa : Int) (n : Nat)
    (Hpriv : ∀ j : Nat, j < n → priv L (pa + (j : Int)) i)
    (Hwn : rowWle (AxOpsem.grow (gtAdGd GT) i) pa n) :
    ⊢ @FstM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokFld pa n) i
        (OutSt GT i pa) := by
  unfold FstM
  iintro %GD %ls %k %data %base %m %Hc #Hg _ %Hgd %Hd
  ihave %Heq := (HGX L GT nm GD Hc) $$ Hg
  subst Heq
  obtain ⟨⟨Hb, -⟩, lb, rl, Hlb, Hid⟩ := Hd
  rw [Hb] at Hid
  have Hisw : gisW (gtAdGd GT).gdG (i, k) = true := by
    unfold gisW
    rw [lblOfRow _ _ _ _ Hlb]
    cases lb <;> simp [aident, aidentWr] at Hid ⊢ <;> rfl
  have Hsg : ∀ a v, gwritesByte (gtAdGd GT).gdG (i, k) a v → priv L a (i, k).1 := by
    intro a v Hw
    obtain ⟨rl', b, m', j, Hid', Hj, rfl⟩ := gwbIdent _ _ _ _ _ (lblOfRow _ _ _ _ Hlb) Hw
    rw [Hid] at Hid'
    simp only [Option.some.injEq, Prod.mk.injEq] at Hid'
    obtain ⟨rfl, rfl, rfl⟩ := Hid'
    have Hm := Hwn k lb rl data.length Hlb Hid
    exact Hpriv j (by omega)
  unfold dflowO
  iintro %na ⟨Hpg, Hannot⟩
  ihave %Hnin := naAtProgressNotElemOf (gtAdGd GT) i k na $$ Hpg
  imod annotAlloc na (i, k) iprop(True) Hnin $$ Hannot with ⟨Hannot, -⟩
  imodintro
  inext
  imodintro
  iexists iprop(True), (∅ : Mea GF), (∅ : Mea GF), (() : Unit)
  isplitr
  · iapply (naWfEmpty L GT nm (i, k) na)
  isplitr
  · iapply (fxPrivWrite L GT nm HL Hcons (i, k) Hisw Hsg)
  isplitl [Hannot]
  · rw [AxLockWp.annotInsertEq na (i, k) iprop(True)]
    iexact Hannot
  isplitr
  · iapply (AxSpinWit.localTrue (gtAdGd GT) Xv6N Unit (protXv6 L) nm (gtAdGd GT) i (k + 1) ())
  · unfold OutSt
    ipureintro
    exact ⟨Hgd, lb, rl, Hlb, Hid⟩

/-- Rocq `OutLdF`: the load's output — the physical bytes are the graph value (frame rule). -/
def OutLdF (GT : GdexecT) (i : Agent) (pa : Int) (n : Nat) (k : Nat) (v : List (BitVec 8)) :
    IProp GF :=
  iprop(⌜graphValue (gtAdGd GT) (i, k) = some v ∧
    ∃ lb aq, (AxOpsem.grow (gtAdGd GT) i)[k]? = some lb ∧ aidentRd (aident lb) = some (aq, pa, n)⌝)

/-- Rocq `Fld_fld`. -/
theorem FldFld (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (i : Agent) (pa : Int) (n : Nat)
    (Hnr : noRmwn (AxOpsem.grow (gtAdGd GT) i) pa n) :
    ⊢ @FldM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokFld pa n) i
        (OutLdF GT i pa n) := by
  unfold FldM
  iintro %GD %ls %k %v %base %m %Hc #Hg _ %Hgv %Hd
  ihave %Heq := (HGX L GT nm GD Hc) $$ Hg
  subst Heq
  obtain ⟨⟨Hb, Hm⟩, lb, aq, Hlb, Hid⟩ := Hd
  rw [Hb, Hm] at Hid
  have Hnw : gisW (gtAdGd GT).gdG (i, k) = false := by
    cases lb with
    | LLoad aq' b ts vs =>
      unfold gisW
      rw [lblOfRow _ _ _ _ Hlb]
      rfl
    | LStore _ _ _ _ => simp [aident, aidentRd] at Hid
    | LFence _ _ _ _ => simp [aident, aidentRd] at Hid
    | LRmw aq' rl b ts rvs wvs cls' =>
      simp only [aident, aidentRd, Option.some.injEq, Prod.mk.injEq] at Hid
      obtain ⟨rfl, rfl, Hn⟩ := Hid
      exact absurd Hn (Hnr k _ aq' rl wvs.length Hlb rfl)
  unfold dflowO
  iintro %na ⟨Hpg, Hannot⟩
  ihave %Hnin := naAtProgressNotElemOf (gtAdGd GT) i k na $$ Hpg
  imod annotAlloc na (i, k) iprop(True) Hnin $$ Hannot with ⟨Hannot, -⟩
  imodintro
  inext
  imodintro
  iexists iprop(True), (∅ : Mea GF), (∅ : Mea GF), (() : Unit)
  isplitr
  · iapply (naWfEmpty L GT nm (i, k) na)
  isplitr
  · iapply (fxRead L GT nm HL Hcons (i, k) Hnw)
  isplitl [Hannot]
  · rw [AxLockWp.annotInsertEq na (i, k) iprop(True)]
    iexact Hannot
  isplitr
  · iapply (AxSpinWit.localTrue (gtAdGd GT) Xv6N Unit (protXv6 L) nm (gtAdGd GT) i (k + 1) ())
  · unfold OutLdF
    ipureintro
    exact ⟨Hgv, lb, aq, Hlb, Hid⟩

end fld

/-! # 3. The leaves at Ixv6 -/

/-- Rocq `HL0p`. -/
theorem HL0p (GT : GdexecT) (i : Agent) :
    ∀ GD, GD = gtAdGd GT → (AxOpsem.grow GD i).length = (AxOpsem.grow (gtAdGd GT) i).length := by
  intro GD h
  rw [h]

/-- Rocq `HGex0p`. -/
theorem HGex0p (GT : GdexecT) : ∃ GD, GD = gtAdGd GT := ⟨_, rfl⟩

/-- Rocq `ctrl_seip`. -/
theorem ctrlSeip (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base) (rs rs' : RegFile) :
    ctrlOkSW T satp0 rs → regsAgree AxRunClose.pinReg rs' rs → ctrlOkSW T satp0 rs' :=
  fun Hc Hag => (SpineOkTSW σi T satp0 hmode hasid hppn).sptSeip rs rs' Hc Hag

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
/-- Rocq `Hmid0p`. -/
theorem Hmid0p :
    ∀ GD s, GD = gtAdGd GT → midState s → s.atK = (AxOpsem.grow GD i).length →
      ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s := by
  rintro GD s rfl Hm Hk
  exact HΨmid s Hm Hk

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- Rocq `Xx_st4`: a 4-byte store to a private field.  Stage C (deviation 1): the store is AT
`k`, the continuation at `k + 1`; Rocq's "row item `k` is not a write" premise is dropped. -/
theorem XxSt4 (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (imm : BitVec 12) (rs2 rs1 : BitVec 5) (va pa : BitVec 64) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc (.STORE (imm, .Regidx rs2, .Regidx rs1, 4)) →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Store .Data) va 4 pa → hitW rs va →
    (∀ j : Nat, j < 4 → priv L (paZ pa + (j : Int)) i) →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ pa) 4 →
    k + 1 ≤ (AxOpsem.grow (gtAdGd GT) i).length →
    ⊢ (∀ (rs' : RegFile) (ib' : Ibch), ⌜GoodB T satp0 rs pc is_rvc none none rs'⌝ -∗
        ⌜graphData (gtAdGd GT) (i, k) = some (stBytes 4 (gprVal rs rs2))⌝ -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 1⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro HRet Hc HPC Hhit Htx Hva Hda Hhv Hpriv Hw4 Hle
  have H := @XBk hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) σi T satp0 hmode hasid hppn i cpu
    (fun GD => GD = gtAdGd GT) (HGX L GT nm) (AxOpsem.grow (gtAdGd GT) i).length (HL0p GT i)
    (HGex0p GT) Ψ (Hmid0p L GT nm i Ψ HΨmid) (HtextX L GT nm (imgS σi) i Hfix)
    (HflowX L GT nm HL Hcons (imgS σi) i) (HlocX L GT nm i)
    (dokFld (paZ pa) 4) .DKSt (by intro h; cases h) (by intro h; cases h) (OutSt GT i (paZ pa))
    s rs k pc is_rvc _ 1 none (fun _ => none) .CPend false _
    HRet Hc HPC Hhit Htx (fun _ _ _ => trivial)
    (CertBStoreS σi T satp0 hmode hasid hppn (dokFld (paZ pa) 4) rs pc is_rvc imm rs2 rs1 4 va pa
      false AxSpinPOx.vw4 (by omega) (by omega) Hva Hda Hhv ⟨rfl, rfl⟩)
    (by omega) Hle
  iintro C
  iapply H $$ [] [C]
  · simp only [CResK, CFkM]
    iapply (FstFld L GT nm HL Hcons i (paZ pa) 4 Hpriv Hw4)
  · iintro %d %r %rs' %ib' %HPX %HGB HO
    obtain ⟨rfl, rfl⟩ := HPX
    simp only [CResK]
    icases HO with ⟨%kd, %Hkd, HO⟩
    obtain rfl : kd = k := by omega
    unfold OutSt
    icases HO with %Hgd
    iapply C $$ %rs' %ib' %HGB %Hgd.1

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- Rocq `Xx_ld4`: a 4-byte load of a private field (frame rule: no annotation).  Stage C
(deviation 1): the load is AT `k`, the continuation at `k + 1`; Rocq's "row item `k` is not a
4-byte read" premise is dropped. -/
theorem XxLd4 (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (imm : BitVec 12) (rs1 rd : BitVec 5) (va pa : BitVec 64) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 4)) →
    rd.toNat ≠ 0 →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Load .Data) va 4 pa → hitW rs va → ¬ L.xlText (paZ pa) →
    noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ pa) 4 →
    k + 1 ≤ (AxOpsem.grow (gtAdGd GT) i).length →
    ⊢ (∀ (vs : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch), ⌜vs.length = 4⌝ -∗
        ⌜GoodB T satp0 rs pc is_rvc none (some (rd, ldRes false 4 vs)) rs'⌝ -∗
        ⌜graphValue (gtAdGd GT) (i, k) = some vs⌝ -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 1⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro HRet Hc HPC Hhit Htx Hrd Hva Hda Hhv _ Hnr Hle
  have HnoRmw : Dkind.DKLd = .DKLd → ∀ GD, rvwmoCatConsistent GD →
      @AxirisG.gconstInterp GF (AxSpinX2.xG L GT nm) GD ⊢
      ⌜∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat),
        (AxOpsem.grow GD i)[k']? = some lb → aident lb = .IRmw aq rl base n →
        ¬ dokFld (paZ pa) 4 base n⌝ := by
    intro _ GD Hc'
    iintro Hg
    ihave %Heq := (HGX L GT nm GD Hc') $$ Hg
    subst Heq
    ipureintro
    rintro k' lb aq rl base n Hlb Hid ⟨rfl, rfl⟩
    exact Hnr k' lb aq rl 4 Hlb Hid rfl
  have H := @XBk hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) σi T satp0 hmode hasid hppn i cpu
    (fun GD => GD = gtAdGd GT) (HGX L GT nm) (AxOpsem.grow (gtAdGd GT) i).length (HL0p GT i)
    (HGex0p GT) Ψ (Hmid0p L GT nm i Ψ HΨmid) (HtextX L GT nm (imgS σi) i Hfix)
    (HflowX L GT nm HL Hcons (imgS σi) i) (HlocX L GT nm i)
    (dokFld (paZ pa) 4) .DKLd HnoRmw (by intro h; cases h) (OutLdF GT i (paZ pa) 4)
    s rs k pc is_rvc _ 1 none (owLdB rd false 4) .CPend false _
    HRet Hc HPC Hhit Htx (by rintro d r ⟨vs, rfl, -, -⟩; exact Hrd)
    (CertBLoadS σi T satp0 hmode hasid hppn (dokFld (paZ pa) 4) rs pc is_rvc imm rs1 rd false 4 va
      pa false Hrd AxSpinPOx.vw4 (by omega) (by omega) Hva Hda Hhv ⟨rfl, rfl⟩)
    (by omega) Hle
  iintro C
  iapply H $$ [] [C]
  · simp only [CResK, CFkM]
    iapply (FldFld L GT nm HL Hcons i (paZ pa) 4 Hnr)
  · iintro %d %r %rs' %ib' %HPX %HGB HO
    obtain ⟨vs, rfl, Hvs, rfl⟩ := HPX
    simp only [CResK]
    icases HO with ⟨%kd, %Hkd, HO⟩
    obtain rfl : kd = k := by omega
    unfold OutLdF
    icases HO with %Hgv
    iapply C $$ %vs %rs' %ib' %Hvs %HGB %Hgv.1

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- Rocq `Xx_pin`, RESTATED under Stage C (deviation 3): a control instruction whose next pc is
the expected `nxt` (a premise, decided by the caller from a graph-value pin); continuation at
`k`, no stuck branch. -/
theorem XxPin (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (ins : instruction) (ot : Option (BitVec 64)) (ow : Option (BitVec 5 × BitVec 64))
    (nxt : BitVec 64) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc ins → owOk ow → rfF (execute ins) →
    CertC (ctrlOkSW T satp0) rs pc is_rvc ins ot ow → k < (AxOpsem.grow (gtAdGd GT) i).length →
    tgtOf ot pc is_rvc = nxt →
    ⊢ (∀ (rs' : RegFile) (ib' : Ibch),
        ⌜GoodB T satp0 rs pc is_rvc ot ow rs' ∧ tgtOf ot pc is_rvc = nxt⌝ -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro HRet Hc HPC Hhit Htx How Hrf Hcert Hle Htgt
  have H := XxReg L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid s rs k pc
    is_rvc ins ot ow HRet Hc HPC Hhit Htx How Hrf Hcert Hle
  iintro C
  iapply H
  iintro %rs' %ib' %HG
  iapply C $$ %rs' %ib' %⟨HG, Htgt⟩

end ixleaves

end Weak
