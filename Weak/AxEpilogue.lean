/-
Weak: **the kernel epilogue thin slice** (LB/AxSL rev 7): `epilogueRetTarget` and its variants —
the reload `c.ldsp ra` of the spill `c.sdsp ra` delivers the spilled bytes (`graphValue GD rLd =
some Vs`), and the `c.jr ra` that follows jumps to `retPc (wordOfBytes 8 Vs)`.

Rocq: `iris/AxEpilogue.v` @ xxvzwolszwmp.

## The Rocq header, in substance

THE COMPOSITION.  §1 `epiReloadValue`: an owned read's rf-source is `ownedExpectedWriteb` for the
value it reads (`AxProtBytes.greadsByteOwnedExpectedWriteb`), the read's own rf-edge names the
spill (`HreadRf`), and a write's byte value is functional (`gwritesByteDet`) — so byte by byte
`vs0[j]? = Vs[j]?`.  §2 `epiCjrPcTarget`: `WeakLeafJump.execEffExecuteCretZca` plus the
read-back of the `nextPC` just set.  §3 the capstone `epilogueRetTarget`; §3.5
`epilogueRetTargetRun` (the advisor's restatement: a SEGMENTED, CONNECTED run and a bridge about
the run's actual final register file instead of free endpoints; the PROOF is unchanged — the run
premises are carried, not consumed).  §4-7 the OWNERSHIP forms: `HreadRf` replaced by the token
`tokn γ GD a Hs S` and its coverage wand (`readnPureFacts` + `greadsByteDet`); §5 the coverage
wand opened from a live `protInv` (`protInvPrefixCovMem`); §6 `Hcase` derived from the token's
own completeness/chaining plus `S = {[rSd := 1]}` and `gpo rSd rLd` (`epiHcaseDerived`); §7 the
spill's deposited history `writenHist rSd Vs HsBefore` composed with the reload capstone
(`epilogueRetTargetSpillReload`), with the "register-only middle" named as `HmidNoW`.

**RESIDUAL HYPOTHESES (carried explicitly, as in Rocq; not discharged here).**
`Hcons` (cat consistency); the row shapes `HwriteShape`/`HreadShape`/`HtsLen`/`HvsLen`/`Hlen8`;
`HreadRf` (§1/§3/§3.5: the C6 ownership-coverage fact); `Hra`/`Hpriv`/`Hsec`/`HC` (the M-mode
tower of `execEffExecuteCretZca`); `Hbridge` (C7 reg_bridge: the concrete Sail register `ra`
holds `wordOfBytes 8 Vs`); `Hwelldef` (§3, §4-7: contentless, never consumed — Rocq's own
finding); the §3.5 run pieces `HsdspRun`/`HmidRun`/`Haread`/`HVsObs`/`HcontRun`/`HtEnd`/`HregsEq`
(carried, not consumed); §4 the token-side `HlastSpill`/`Hwr`/`Hch`/`Hown`/`Hcase` and the
coverage wand; §5 `Hrgmo`/`Hpref` and the `protInv` resource; §6 `HpoSdLd`; §7 `HsBefore`'s
`HwrBefore`/`HchBefore`/`HownBefore`/`HlinkBefore` and `HmidNoW`.

**Fetches.** Graph events only (Stage C): the program-step relation `AxOpsem.astepProg row` has
no oracle parameters.

## Deviations from Rocq

1. NAMES: camelCase (map below); none is in the duplicated-name table.  Lean-only helpers are
   file-qualified `AxEpilogue.*`.
2. STAGE C: Rocq's `astep_prog row Tt img` ↦ `AxOpsem.astepProg row` — the `Tt : Z → Prop` and
   `img : Z → option (bv 8)` binders of `epilogue_ret_target*` are dropped (the Lean relation has
   no fetch oracle).
3. SAIL VOCABULARY (as `WeakLeafJump` deviation 1/7): `mstate` ↦ `ExecSt`, `s.(sregs)` ↦
   `s.regs`, `register_lookup r s.(sregs)` ↦ `s.regs r`, `set_reg` ↦ `ExecSt.setReg`,
   `register_lookup (R_bitvector_64 (gpr_of_Z (uint ra))) s.(sregs)` ↦ `s.gpr ra` (equal under
   `ra.toNat ≠ 0`), `uint ra <> 0` ↦ `ra.toNat ≠ 0`, `mword_of_int 0` ↦ `0#64`,
   `eq_vec (_get_Misa_C …) 'b"1"` ↦ `(_get_Misa_C … == 1#1) = true`, `ret_pc` ↦
   `WeakLeafMret.retPc`, `word_of_bytes 8%N` ↦ `wordOfBytes 8`, `zeros' 12` ↦ `zeros (n := 12)`.
   `regstate` ↦ `RegFile`, `oib32` ↦ `Ibch`, `Interface.Ret tt` ↦ `.pure ()`, `AThread p k` ↦
   `⟨p, k⟩`.
4. GRAPH VOCABULARY (as `AxProtBytes` deviation 3): `Hs !! j` ↦ `Hs[j]?`, `Z.of_nat j` ↦
   `(j : Int)`, `last` ↦ `List.getLast?`, `.*1` ↦ `List.map Prod.fst`, `dom` ↦
   `FiniteMap.dom_set`, `list_to_set` ↦ `LawfulSet.ofList`, `gpo` ↦ `WeakRvwmoGraph.gpo`,
   `Vs !!! j` ↦ `Vs.getD j 0`.
5. CONTEXT (as `AxProtBytes` deviation 2): the section `EpilogueOwn` context (`γ`, `GD`, `Hcons`)
   becomes explicit arguments, each declaration taking the ones it uses; `Hob_eq` and the
   `invGS_gen`/`axirisG` instances are used by no declaration and are dropped; `axlogG Σ hent` ↦
   `[AxlogG GF Hent]`.
6. STATEMENT SHAPES: wand chains `⊢ A -∗ B -∗ ⌜φ⌝`.  `epilogueRetTargetOwnInv` consumes
   `protInv` once (no persistence needed: the coverage family is proved inside one `∀ j`).

**Rocq → Lean name map.**  `epi_reload_value` `epiReloadValue`, `epi_cjr_pc_target`
`epiCjrPcTarget`, `epilogue_ret_target` `epilogueRetTarget`, `epilogue_ret_target_run`
`epilogueRetTargetRun`, `epi_reload_value_own` `epiReloadValueOwn`, `epilogue_ret_target_own`
`epilogueRetTargetOwn`, `epilogue_ret_target_own_inv` `epilogueRetTargetOwnInv`,
`epi_hcase_derived` `epiHcaseDerived`, `epilogue_ret_target_own2` `epilogueRetTargetOwn2`,
`chain_with_snoc` `chainWithSnoc`, `epilogue_ret_target_spill_reload`
`epilogueRetTargetSpillReload`.  Lean-only: `AxEpilogue.greadsOfLoad`, `AxEpilogue.gwritesOfStore`,
`AxEpilogue.listEq8`, `AxEpilogue.getDSome`.

**Dropped:** nothing (Rocq 11 lemmas; Lean 11 theorems + 4 Lean-only).
-/
import Weak.AxProtBytes
import Weak.WeakLeafJump

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail LeanRV64D LeanRV64D.Functions

/-! # 0. Lean-only helpers -/

/-- Lean-only: a load label's byte `j` witness. -/
theorem AxEpilogue.greadsOfLoad (G : Gexec) (r : Geid) (aq : Bool) (a : Int) (ts0 : List Nat)
    (vs0 : List (BitVec 8)) (j t : Nat) (v : BitVec 8)
    (Hl : gxLbl G r = some (.LLoad aq a ts0 vs0)) (Ht : ts0[j]? = some t) (Hv : vs0[j]? = some v) :
    greadsByte G r (a + (j : Int)) t v :=
  ⟨_, a, ts0, vs0, j, Hl, rfl, Ht, Hv, rfl⟩

/-- Lean-only: a store label's byte `j` witness. -/
theorem AxEpilogue.gwritesOfStore (G : Gexec) (w : Geid) (rl : Bool) (a : Int)
    (Vs : List (BitVec 8)) (k : WmClass) (j : Nat) (v : BitVec 8)
    (Hl : gxLbl G w = some (.LStore rl a Vs k)) (Hv : Vs[j]? = some v) :
    gwritesByte G w (a + (j : Int)) v :=
  ⟨_, a, Vs, j, Hl, rfl, Hv, rfl⟩

/-- Lean-only: two 8-element lists agreeing below 8 are equal. -/
theorem AxEpilogue.listEq8 (l1 l2 : List (BitVec 8)) (h1 : l1.length = 8) (h2 : l2.length = 8)
    (h : ∀ j, j < 8 → l1[j]? = l2[j]?) : l1 = l2 := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < 8
  · exact h j hj
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- Lean-only: an in-range `getD` is the lookup. -/
theorem AxEpilogue.getDSome (Vs : List (BitVec 8)) (j : Nat) (h : j < Vs.length) :
    Vs[j]? = some (Vs.getD j 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-! # 1. THE VALUE-DELIVERY HALF -/

theorem epiReloadValue (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (rSd rLd : Geid) (a : Int)
    (rl : Bool) (kCls : WmClass) (Vs : List (BitVec 8)) (Hlen8 : Vs.length = 8)
    (HwriteShape : gxLbl GD.gdG rSd = some (.LStore rl a Vs kCls))
    (aq : Bool) (ts0 : List Nat) (vs0 : List (BitVec 8))
    (HreadShape : gxLbl GD.gdG rLd = some (.LLoad aq a ts0 vs0))
    (HtsLen : ts0.length = 8) (HvsLen : vs0.length = 8)
    (HreadRf : ∀ j, j < 8 → ∃ t, ts0[j]? = some t ∧ gwriteAt GD.gdG t = some rSd) :
    graphValue GD rLd = some Vs := by
  have Heq : vs0 = Vs := by
    apply AxEpilogue.listEq8 _ _ HvsLen Hlen8
    intro j hj
    obtain ⟨t, Hts, Hwrat⟩ := HreadRf j hj
    obtain ⟨v0, Hv0⟩ := someOfIsSome (lookup_lt_is_Some_2 (l := vs0) (i := j) (by omega))
    obtain ⟨vw, Hvw⟩ := someOfIsSome (lookup_lt_is_Some_2 (l := Vs) (i := j) (by omega))
    have Hgb := AxEpilogue.greadsOfLoad GD.gdG rLd aq a ts0 vs0 j t v0 HreadShape Hts Hv0
    have Hoe := greadsByteOwnedExpectedWriteb GD Hcons rLd _ t v0 rSd Hgb Hwrat
    have Hwb0 : gwritesByte GD.gdG rSd (a + (j : Int)) v0 := by
      rcases Hoe with ⟨Hwb0', _⟩ | ⟨⟨Hwb0', _⟩, _⟩ <;> exact Hwb0'
    have Hwb1 := AxEpilogue.gwritesOfStore GD.gdG rSd rl a Vs kCls j vw HwriteShape Hvw
    rw [Hv0, Hvw, gwritesByteDet _ _ _ _ _ Hwb0 Hwb1]
  rw [graphValue, HreadShape, Heq]
  rfl

/-! # 2. THE PC-TARGET HALF -/

theorem epiCjrPcTarget (ra : BitVec 5) (s : ExecSt) (Hra : ra.toNat ≠ 0)
    (Hpriv : s.regs .cur_privilege = .Machine) (Hsec : s.regs .mseccfg = 0#64)
    (HC : (_get_Misa_C (s.regs .misa) == 1#1) = true) :
    execEff (execute (.JALR (zeros (n := 12), .Regidx ra, zreg))) s =
      some (RETIRE_SUCCESS, s.setReg .nextPC (WeakLeafMret.retPc (s.gpr ra)), []) ∧
    (s.setReg .nextPC (WeakLeafMret.retPc (s.gpr ra))).regs .nextPC =
      WeakLeafMret.retPc (s.gpr ra) := by
  refine ⟨execEffExecuteCretZca ra s Hra Hpriv Hsec HC, ?_⟩
  simp only [ExecSt.setReg_regs, RegFile.set_same]

/-! # 3. THE CAPSTONE -/

theorem epilogueRetTarget (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (row : List Lbl) (tBegin tEnd : Athread)
    (Hwelldef : rtc (fun s1 s2 => ∃ l, AxOpsem.astepProg row s1 l s2) tBegin tEnd)
    (rSd rLd : Geid) (a : Int) (rl : Bool) (kCls : WmClass)
    (Vs : List (BitVec 8)) (Hlen8 : Vs.length = 8)
    (HwriteShape : gxLbl GD.gdG rSd = some (.LStore rl a Vs kCls))
    (aq : Bool) (ts0 : List Nat) (vs0 : List (BitVec 8))
    (HreadShape : gxLbl GD.gdG rLd = some (.LLoad aq a ts0 vs0))
    (HtsLen : ts0.length = 8) (HvsLen : vs0.length = 8)
    (HreadRf : ∀ j, j < 8 → ∃ t, ts0[j]? = some t ∧ gwriteAt GD.gdG t = some rSd)
    (ra : BitVec 5) (Hra : ra.toNat ≠ 0) (s : ExecSt)
    (Hpriv : s.regs .cur_privilege = .Machine) (Hsec : s.regs .mseccfg = 0#64)
    (HC : (_get_Misa_C (s.regs .misa) == 1#1) = true)
    (Hbridge : s.gpr ra = wordOfBytes 8 Vs) :
    graphValue GD rLd = some Vs ∧
    execEff (execute (.JALR (zeros (n := 12), .Regidx ra, zreg))) s =
      some (RETIRE_SUCCESS, s.setReg .nextPC (WeakLeafMret.retPc (wordOfBytes 8 Vs)), []) ∧
    (s.setReg .nextPC (WeakLeafMret.retPc (wordOfBytes 8 Vs))).regs .nextPC =
      WeakLeafMret.retPc (wordOfBytes 8 Vs) := by
  have h := epiCjrPcTarget ra s Hra Hpriv Hsec HC
  rw [Hbridge] at h
  exact ⟨epiReloadValue GD Hcons rSd rLd a rl kCls Vs Hlen8 HwriteShape aq ts0 vs0 HreadShape
    HtsLen HvsLen HreadRf, h⟩

/-! # 3.5 The segmented, connected run -/

theorem epilogueRetTargetRun (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (row : List Lbl)
    (rSd rLd : Geid) (a : Int) (rl : Bool) (kCls : WmClass)
    (Vs : List (BitVec 8)) (Hlen8 : Vs.length = 8)
    (HwriteShape : gxLbl GD.gdG rSd = some (.LStore rl a Vs kCls))
    (aq : Bool) (ts0 : List Nat) (vs0 : List (BitVec 8))
    (HreadShape : gxLbl GD.gdG rLd = some (.LLoad aq a ts0 vs0))
    (HtsLen : ts0.length = 8) (HvsLen : vs0.length = 8)
    (HreadRf : ∀ j, j < 8 → ∃ t, ts0[j]? = some t ∧ gwriteAt GD.gdG t = some rSd)
    (tBegin tMid1 tMid2 : Athread)
    (HsdspRun : rtc (fun s1 s2 => ∃ l, AxOpsem.astepProg row s1 l s2) tBegin tMid1)
    (HmidRun : rtc (fun s1 s2 => ∃ l, AxOpsem.astepProg row s1 l s2) tMid1 tMid2)
    (ident : AidentT) (K : List (BitVec 8) → Athread)
    (Haread : areadStep row tMid2 ident K)
    (t' tEnd : Athread)
    (HVsObs : t' = K Vs)
    (HcontRun : rtc (fun s1 s2 => ∃ l, AxOpsem.astepProg row s1 l s2) t' tEnd)
    (cpu' : CPU) (regsEnd : RegFile) (ibEnd : Ibch) (kEnd : Nat)
    (HtEnd : tEnd = ⟨.PHart cpu' (.pure ()) regsEnd none ibEnd, kEnd⟩)
    (ra : BitVec 5) (Hra : ra.toNat ≠ 0) (sM : ExecSt)
    (HregsEq : sM.regs = regsEnd)
    (Hpriv : sM.regs .cur_privilege = .Machine) (Hsec : sM.regs .mseccfg = 0#64)
    (HC : (_get_Misa_C (sM.regs .misa) == 1#1) = true)
    (Hbridge : sM.gpr ra = wordOfBytes 8 Vs) :
    graphValue GD rLd = some Vs ∧
    execEff (execute (.JALR (zeros (n := 12), .Regidx ra, zreg))) sM =
      some (RETIRE_SUCCESS, sM.setReg .nextPC (WeakLeafMret.retPc (wordOfBytes 8 Vs)), []) ∧
    (sM.setReg .nextPC (WeakLeafMret.retPc (wordOfBytes 8 Vs))).regs .nextPC =
      WeakLeafMret.retPc (wordOfBytes 8 Vs) := by
  have h := epiCjrPcTarget ra sM Hra Hpriv Hsec HC
  rw [Hbridge] at h
  exact ⟨epiReloadValue GD Hcons rSd rLd a rl kCls Vs Hlen8 HwriteShape aq ts0 vs0 HreadShape
    HtsLen HvsLen HreadRf, h⟩

/-! # 4. `HreadRf` REPLACED BY OWNERSHIP -/

section epilogueOwn

variable {GF : BundledGFunctors} [AxlogG GF Hent]

theorem epiReloadValueOwn (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (rSd rLd : Geid) (a : Int) (Vs : List (BitVec 8)) (Hlen8 : Vs.length = 8)
    (Hs : List (List Hent)) (Hlens : Hs.length = 8) (S : GMapF Geid Qp)
    (HlastSpill : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∃ v, H.getLast? = some (rSd, v) ∧ Vs[j]? = some v)
    (aq : Bool) (ts0 : List Nat) (vs0 : List (BitVec 8))
    (HreadShape : gxLbl GD.gdG rLd = some (.LLoad aq a ts0 vs0))
    (HtsLen : ts0.length = 8) (HvsLen : vs0.length = 8)
    (Hwr : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ p, p ∈ H → gwritesByte GD.gdG p.1 (a + (j : Int)) p.2)
    (Hch : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H → chainWith (gmoLt GD.gdG) (H.map Prod.fst))
    (Hown : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ w v, gwritesByte GD.gdG w (a + (j : Int)) v → WeakRvwmoGraph.gpo GD.gdG w rLd →
        w ∈ H.map Prod.fst)
    (Hcase : ∀ (j : Nat) (H : List Hent) wl vl, Hs[j]? = some H → H.getLast? = some (wl, vl) →
      (∃ e, e ∈ (FiniteMap.dom_set S : GSet Geid) ∧ gmoLt GD.gdG e rLd)
      ∨
      (wl ∈ (FiniteMap.dom_set S : GSet Geid) ∧
       (∀ e, e ∈ (FiniteMap.dom_set S : GSet Geid) → ¬ gmoLt GD.gdG e rLd) ∧
       WeakRvwmoGraph.gpo GD.gdG wl rLd ∧
       (∀ w' v', gwritesByte GD.gdG w' (a + (j : Int)) v' →
         WeakRvwmoGraph.gpo GD.gdG wl w' → WeakRvwmoGraph.gpo GD.gdG w' rLd → False))) :
    ⊢ (∀ (j : Nat) (w : Geid) (v : BitVec 8), ⌜gwritesByte GD.gdG w (a + (j : Int)) v⌝ -∗
        ⌜gmoLt GD.gdG w rLd⌝ -∗
        ∃ H' : List Hent, ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap (GF := GF) γ (a + (j : Int)) H') -∗
      tokn γ GD a Hs S -∗
      ⌜graphValue GD rLd = some Vs⌝ := by
  have Hrd : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∃ t v, greadsByte GD.gdG rLd (a + (j : Int)) t v := by
    intro j H HjH
    have Hj8 : j < 8 := by have := lookup_lt_Some HjH; omega
    obtain ⟨t0, Ht0⟩ := someOfIsSome (lookup_lt_is_Some_2 (l := ts0) (i := j) (by omega))
    obtain ⟨v0, Hv0⟩ := someOfIsSome (lookup_lt_is_Some_2 (l := vs0) (i := j) (by omega))
    exact ⟨t0, v0, AxEpilogue.greadsOfLoad GD.gdG rLd aq a ts0 vs0 j t0 v0 HreadShape Ht0 Hv0⟩
  iintro Hcov Htoks
  ihave %HPall := readnPureFacts γ GD Hcons a Hs S rLd Hwr Hch Hown Hrd Hcase $$ Hcov Htoks
  ipureintro
  have Heq : vs0 = Vs := by
    apply AxEpilogue.listEq8 _ _ HvsLen Hlen8
    intro j hj
    obtain ⟨H, HjH⟩ := someOfIsSome (lookup_lt_is_Some_2 (l := Hs) (i := j) (by omega))
    obtain ⟨v, Hlast, HjV⟩ := HlastSpill j H HjH
    obtain ⟨_, tOwn, HgbOwn⟩ := HPall j H HjH rSd v Hlast
    obtain ⟨v0, Hv0⟩ := someOfIsSome (lookup_lt_is_Some_2 (l := vs0) (i := j) (by omega))
    obtain ⟨t0, Ht0⟩ := someOfIsSome (lookup_lt_is_Some_2 (l := ts0) (i := j) (by omega))
    have HgbLbl := AxEpilogue.greadsOfLoad GD.gdG rLd aq a ts0 vs0 j t0 v0 HreadShape Ht0 Hv0
    have Heqv := (greadsByteDet GD.gdG rLd _ tOwn v t0 v0 HgbOwn HgbLbl).2
    rw [Hv0, HjV, Heqv]
  rw [graphValue, HreadShape, Heq]
  rfl

/-- THE CAPSTONE, ownership form. -/
theorem epilogueRetTargetOwn (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (row : List Lbl) (tBegin tEnd : Athread)
    (Hwelldef : rtc (fun s1 s2 => ∃ l, AxOpsem.astepProg row s1 l s2) tBegin tEnd)
    (rSd rLd : Geid) (a : Int) (Vs : List (BitVec 8)) (Hlen8 : Vs.length = 8)
    (Hs : List (List Hent)) (Hlens : Hs.length = 8) (S : GMapF Geid Qp)
    (HlastSpill : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∃ v, H.getLast? = some (rSd, v) ∧ Vs[j]? = some v)
    (aq : Bool) (ts0 : List Nat) (vs0 : List (BitVec 8))
    (HreadShape : gxLbl GD.gdG rLd = some (.LLoad aq a ts0 vs0))
    (HtsLen : ts0.length = 8) (HvsLen : vs0.length = 8)
    (Hwr : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ p, p ∈ H → gwritesByte GD.gdG p.1 (a + (j : Int)) p.2)
    (Hch : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H → chainWith (gmoLt GD.gdG) (H.map Prod.fst))
    (Hown : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ w v, gwritesByte GD.gdG w (a + (j : Int)) v → WeakRvwmoGraph.gpo GD.gdG w rLd →
        w ∈ H.map Prod.fst)
    (Hcase : ∀ (j : Nat) (H : List Hent) wl vl, Hs[j]? = some H → H.getLast? = some (wl, vl) →
      (∃ e, e ∈ (FiniteMap.dom_set S : GSet Geid) ∧ gmoLt GD.gdG e rLd)
      ∨
      (wl ∈ (FiniteMap.dom_set S : GSet Geid) ∧
       (∀ e, e ∈ (FiniteMap.dom_set S : GSet Geid) → ¬ gmoLt GD.gdG e rLd) ∧
       WeakRvwmoGraph.gpo GD.gdG wl rLd ∧
       (∀ w' v', gwritesByte GD.gdG w' (a + (j : Int)) v' →
         WeakRvwmoGraph.gpo GD.gdG wl w' → WeakRvwmoGraph.gpo GD.gdG w' rLd → False)))
    (ra : BitVec 5) (Hra : ra.toNat ≠ 0) (s : ExecSt)
    (Hpriv : s.regs .cur_privilege = .Machine) (Hsec : s.regs .mseccfg = 0#64)
    (HC : (_get_Misa_C (s.regs .misa) == 1#1) = true)
    (Hbridge : s.gpr ra = wordOfBytes 8 Vs) :
    ⊢ (∀ (j : Nat) (w : Geid) (v : BitVec 8), ⌜gwritesByte GD.gdG w (a + (j : Int)) v⌝ -∗
        ⌜gmoLt GD.gdG w rLd⌝ -∗
        ∃ H' : List Hent, ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap (GF := GF) γ (a + (j : Int)) H') -∗
      tokn γ GD a Hs S -∗
      ⌜graphValue GD rLd = some Vs ∧
        execEff (execute (.JALR (zeros (n := 12), .Regidx ra, zreg))) s =
          some (RETIRE_SUCCESS, s.setReg .nextPC (WeakLeafMret.retPc (wordOfBytes 8 Vs)), []) ∧
        (s.setReg .nextPC (WeakLeafMret.retPc (wordOfBytes 8 Vs))).regs .nextPC =
          WeakLeafMret.retPc (wordOfBytes 8 Vs)⌝ := by
  iintro Hcov Htoks
  ihave %Hval := epiReloadValueOwn γ GD Hcons rSd rLd a Vs Hlen8 Hs Hlens S HlastSpill aq ts0 vs0
    HreadShape HtsLen HvsLen Hwr Hch Hown Hcase $$ Hcov Htoks
  ipureintro
  have h := epiCjrPcTarget ra s Hra Hpriv Hsec HC
  rw [Hbridge] at h
  exact ⟨Hval, h⟩

/-! # 5. `Hcov` opened from the live protocol invariant -/

theorem epilogueRetTargetOwnInv (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (row : List Lbl) (tBegin tEnd : Athread)
    (Hwelldef : rtc (fun s1 s2 => ∃ l, AxOpsem.astepProg row s1 l s2) tBegin tEnd)
    (rSd rLd : Geid) (a : Int) (Vs : List (BitVec 8)) (Hlen8 : Vs.length = 8)
    (Hs : List (List Hent)) (Hlens : Hs.length = 8) (S : GMapF Geid Qp)
    (HlastSpill : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∃ v, H.getLast? = some (rSd, v) ∧ Vs[j]? = some v)
    (aq : Bool) (ts0 : List Nat) (vs0 : List (BitVec 8))
    (HreadShape : gxLbl GD.gdG rLd = some (.LLoad aq a ts0 vs0))
    (HtsLen : ts0.length = 8) (HvsLen : vs0.length = 8)
    (Hwr : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ p, p ∈ H → gwritesByte GD.gdG p.1 (a + (j : Int)) p.2)
    (Hch : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H → chainWith (gmoLt GD.gdG) (H.map Prod.fst))
    (Hown : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ w v, gwritesByte GD.gdG w (a + (j : Int)) v → WeakRvwmoGraph.gpo GD.gdG w rLd →
        w ∈ H.map Prod.fst)
    (Hcase : ∀ (j : Nat) (H : List Hent) wl vl, Hs[j]? = some H → H.getLast? = some (wl, vl) →
      (∃ e, e ∈ (FiniteMap.dom_set S : GSet Geid) ∧ gmoLt GD.gdG e rLd)
      ∨
      (wl ∈ (FiniteMap.dom_set S : GSet Geid) ∧
       (∀ e, e ∈ (FiniteMap.dom_set S : GSet Geid) → ¬ gmoLt GD.gdG e rLd) ∧
       WeakRvwmoGraph.gpo GD.gdG wl rLd ∧
       (∀ w' v', gwritesByte GD.gdG w' (a + (j : Int)) v' →
         WeakRvwmoGraph.gpo GD.gdG wl w' → WeakRvwmoGraph.gpo GD.gdG w' rLd → False)))
    (ra : BitVec 5) (Hra : ra.toNat ≠ 0) (sM : ExecSt)
    (Hpriv : sM.regs .cur_privilege = .Machine) (Hsec : sM.regs .mseccfg = 0#64)
    (HC : (_get_Misa_C (sM.regs .misa) == 1#1) = true)
    (Hbridge : sM.gpr ra = wordOfBytes 8 Vs)
    (sOb : GSet Geid) (Hrgmo : rLd ∈ GD.gdG.gxGmo)
    (Hpref : (LawfulSet.ofList (gmoPrefix GD.gdG rLd) : GSet Geid) ⊆ sOb) :
    ⊢ protInv (GF := GF) γ GD sOb -∗
      tokn γ GD a Hs S -∗
      ⌜graphValue GD rLd = some Vs ∧
        execEff (execute (.JALR (zeros (n := 12), .Regidx ra, zreg))) sM =
          some (RETIRE_SUCCESS, sM.setReg .nextPC (WeakLeafMret.retPc (wordOfBytes 8 Vs)), []) ∧
        (sM.setReg .nextPC (WeakLeafMret.retPc (wordOfBytes 8 Vs))).regs .nextPC =
          WeakLeafMret.retPc (wordOfBytes 8 Vs)⌝ := by
  iintro Hinv Htoks
  ihave Hcov : ∀ (j : Nat) (w : Geid) (v : BitVec 8), ⌜gwritesByte GD.gdG w (a + (j : Int)) v⌝ -∗
      ⌜gmoLt GD.gdG w rLd⌝ -∗
      ∃ H' : List Hent, ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap (GF := GF) γ (a + (j : Int)) H'
    $$ [Hinv]
  · iintro %j %w %v %Hwb %Hmo
    ihave Hspec := protInvPrefixCovMem γ GD sOb rLd (a + (j : Int)) Hcons.1 Hrgmo Hpref $$ Hinv
    ihave Hres := Hspec $$ %w %v %Hwb %Hmo
    iexact Hres
  ihave Hfin := epilogueRetTargetOwn γ GD Hcons row tBegin tEnd Hwelldef rSd rLd a Vs Hlen8 Hs
    Hlens S HlastSpill aq ts0 vs0 HreadShape HtsLen HvsLen Hwr Hch Hown Hcase ra Hra sM Hpriv Hsec
    HC Hbridge $$ Hcov Htoks
  iexact Hfin

end epilogueOwn

/-! # 6. `Hcase` derived -/

theorem epiHcaseDerived (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (rLd rSd : Geid) (a : Int)
    (Vs : List (BitVec 8)) (Hs : List (List Hent))
    (Hwr : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ p, p ∈ H → gwritesByte GD.gdG p.1 (a + (j : Int)) p.2)
    (Hch : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H → chainWith (gmoLt GD.gdG) (H.map Prod.fst))
    (Hown : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ w v, gwritesByte GD.gdG w (a + (j : Int)) v → WeakRvwmoGraph.gpo GD.gdG w rLd →
        w ∈ H.map Prod.fst)
    (HlastSpill : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∃ v, H.getLast? = some (rSd, v) ∧ Vs[j]? = some v)
    (HpoSdLd : WeakRvwmoGraph.gpo GD.gdG rSd rLd) :
    ∀ (j : Nat) (H : List Hent) wl vl, Hs[j]? = some H → H.getLast? = some (wl, vl) →
      (∃ e, e ∈ (FiniteMap.dom_set ({[rSd := (1 : Qp)]} : GMapF Geid Qp) : GSet Geid) ∧
        gmoLt GD.gdG e rLd)
      ∨
      (wl ∈ (FiniteMap.dom_set ({[rSd := (1 : Qp)]} : GMapF Geid Qp) : GSet Geid) ∧
       (∀ e, e ∈ (FiniteMap.dom_set ({[rSd := (1 : Qp)]} : GMapF Geid Qp) : GSet Geid) →
         ¬ gmoLt GD.gdG e rLd) ∧
       WeakRvwmoGraph.gpo GD.gdG wl rLd ∧
       (∀ w' v', gwritesByte GD.gdG w' (a + (j : Int)) v' →
         WeakRvwmoGraph.gpo GD.gdG wl w' → WeakRvwmoGraph.gpo GD.gdG w' rLd → False)) := by
  intro j H wl vl HjH Hlast
  obtain ⟨v0, Hlast0, _⟩ := HlastSpill j H HjH
  rw [Hlast0, Option.some.injEq, Prod.mk.injEq] at Hlast
  obtain ⟨Heqwl, _⟩ := Hlast
  subst Heqwl
  have HdomIn : rSd ∈ (FiniteMap.dom_set ({[rSd := (1 : Qp)]} : GMapF Geid Qp) : GSet Geid) := by
    rw [domSingleton, elemOfSingleton]
  have Hrule1 : ∀ e1 e2, gppo1 GD.gdG e1 e2 → gmoLt GD.gdG e1 e2 :=
    fun e1 e2 h => Hcons.2.1 e1 e2 (Or.inl (Or.inl h))
  by_cases Hmo : gmoLt GD.gdG rSd rLd
  · exact Or.inl ⟨rSd, HdomIn, Hmo⟩
  refine Or.inr ⟨HdomIn, fun e He => ?_, HpoSdLd, ?_⟩
  · rw [domSingleton, elemOfSingleton] at He
    subst He
    exact Hmo
  intro w' v' Hwb' Hpo1 Hpo2
  have Hw'H := Hown j H HjH w' v' Hwb' Hpo2
  obtain ⟨H0, rfl⟩ := List.getLast?_eq_some_iff.1 Hlast0
  have HmemSd : (rSd, v0) ∈ H0 ++ [(rSd, v0)] := List.mem_append_right _ (List.mem_singleton_self _)
  have HwbSd := Hwr j _ HjH (rSd, v0) HmemSd
  have HmoSdW' : gmoLt GD.gdG rSd w' :=
    Hrule1 rSd w' ⟨Hpo1, a + (j : Int), Or.inl ⟨v0, HwbSd⟩, v', Hwb'⟩
  rw [List.map_append, List.mem_append] at Hw'H
  rcases Hw'H with Hin | Hin
  · obtain ⟨i, hi, Hi⟩ := List.mem_iff_getElem.1 Hin
    have Hch' := Hch j _ HjH
    rw [List.map_append] at Hch'
    have Hl : (H0.map Prod.fst ++ (([(rSd, v0)] : List Hent).map Prod.fst))[(H0.map Prod.fst).length]?
        = some rSd := by
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    have Hi' : (H0.map Prod.fst ++ (([(rSd, v0)] : List Hent).map Prod.fst))[i]? = some w' := by
      rw [List.getElem?_append_left hi, List.getElem?_eq_getElem hi, Hi]
    have HmoW'Sd := chainWithGmo GD.gdG (gmoLt GD.gdG) _ i _ w' rSd (fun _ _ h => h) Hch' Hi' Hl hi
    exact gmoLtIrrefl GD.gdG w' (gmoLtTrans GD.gdG w' rSd w' HmoW'Sd HmoSdW')
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at Hin
    subst Hin
    exact gmoLtIrrefl GD.gdG _ HmoSdW'

section epilogueOwn2

variable {GF : BundledGFunctors} [AxlogG GF Hent]

theorem epilogueRetTargetOwn2 (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (row : List Lbl) (tBegin tEnd : Athread)
    (Hwelldef : rtc (fun s1 s2 => ∃ l, AxOpsem.astepProg row s1 l s2) tBegin tEnd)
    (rSd rLd : Geid) (a : Int) (Vs : List (BitVec 8)) (Hlen8 : Vs.length = 8)
    (Hs : List (List Hent)) (Hlens : Hs.length = 8)
    (HlastSpill : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∃ v, H.getLast? = some (rSd, v) ∧ Vs[j]? = some v)
    (aq : Bool) (ts0 : List Nat) (vs0 : List (BitVec 8))
    (HreadShape : gxLbl GD.gdG rLd = some (.LLoad aq a ts0 vs0))
    (HtsLen : ts0.length = 8) (HvsLen : vs0.length = 8)
    (Hwr : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ p, p ∈ H → gwritesByte GD.gdG p.1 (a + (j : Int)) p.2)
    (Hch : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H → chainWith (gmoLt GD.gdG) (H.map Prod.fst))
    (Hown : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∀ w v, gwritesByte GD.gdG w (a + (j : Int)) v → WeakRvwmoGraph.gpo GD.gdG w rLd →
        w ∈ H.map Prod.fst)
    (HpoSdLd : WeakRvwmoGraph.gpo GD.gdG rSd rLd)
    (ra : BitVec 5) (Hra : ra.toNat ≠ 0) (sM : ExecSt)
    (Hpriv : sM.regs .cur_privilege = .Machine) (Hsec : sM.regs .mseccfg = 0#64)
    (HC : (_get_Misa_C (sM.regs .misa) == 1#1) = true)
    (Hbridge : sM.gpr ra = wordOfBytes 8 Vs) :
    ⊢ (∀ (j : Nat) (w : Geid) (v : BitVec 8), ⌜gwritesByte GD.gdG w (a + (j : Int)) v⌝ -∗
        ⌜gmoLt GD.gdG w rLd⌝ -∗
        ∃ H' : List Hent, ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap (GF := GF) γ (a + (j : Int)) H') -∗
      tokn γ GD a Hs ({[rSd := (1 : Qp)]} : GMapF Geid Qp) -∗
      ⌜graphValue GD rLd = some Vs ∧
        execEff (execute (.JALR (zeros (n := 12), .Regidx ra, zreg))) sM =
          some (RETIRE_SUCCESS, sM.setReg .nextPC (WeakLeafMret.retPc (wordOfBytes 8 Vs)), []) ∧
        (sM.setReg .nextPC (WeakLeafMret.retPc (wordOfBytes 8 Vs))).regs .nextPC =
          WeakLeafMret.retPc (wordOfBytes 8 Vs)⌝ :=
  epilogueRetTargetOwn γ GD Hcons row tBegin tEnd Hwelldef rSd rLd a Vs Hlen8 Hs Hlens
    ({[rSd := (1 : Qp)]} : GMapF Geid Qp) HlastSpill aq ts0 vs0 HreadShape HtsLen HvsLen Hwr Hch
    Hown (epiHcaseDerived GD Hcons rLd rSd a Vs Hs Hwr Hch Hown HlastSpill HpoSdLd)
    ra Hra sM Hpriv Hsec HC Hbridge

end epilogueOwn2

/-! # 7. The spill's deposit composed with the reload -/

/-- `chainWith` extends across one appended element, given the old last entry (if any) is
`R`-related to the new one. -/
theorem chainWithSnoc (R : Geid → Geid → Prop) (Hl0 : List Geid) (wl : Geid)
    (Hch0 : chainWith R Hl0) (Hlink : ∀ wlast, Hl0.getLast? = some wlast → R wlast wl) :
    chainWith R (Hl0 ++ [wl]) := by
  intro i w1 w2 h1 h2
  by_cases hlt : i + 1 < Hl0.length
  · rw [List.getElem?_append_left (by omega)] at h1
    rw [List.getElem?_append_left hlt] at h2
    exact Hch0 i w1 w2 h1 h2
  · have hlen := lookup_lt_Some h2
    simp only [List.length_append, List.length_singleton] at hlen
    have hi : i + 1 = Hl0.length := by omega
    rw [List.getElem?_append_right (by omega), hi, Nat.sub_self] at h2
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h2
    subst h2
    rw [List.getElem?_append_left (by omega)] at h1
    apply Hlink
    rw [List.getLast?_eq_getElem?]
    have he : Hl0.length - 1 = i := by omega
    rw [he]
    exact h1

section epilogueSpill

variable {GF : BundledGFunctors} [AxlogG GF Hent]

theorem epilogueRetTargetSpillReload (γ : GName) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (row : List Lbl) (tBegin tEnd : Athread)
    (Hwelldef : rtc (fun s1 s2 => ∃ l, AxOpsem.astepProg row s1 l s2) tBegin tEnd)
    (rSd rLd : Geid) (a : Int) (rl : Bool) (kCls : WmClass)
    (Vs : List (BitVec 8)) (Hlen8 : Vs.length = 8)
    (HwriteShape : gxLbl GD.gdG rSd = some (.LStore rl a Vs kCls))
    (aq : Bool) (ts0 : List Nat) (vs0 : List (BitVec 8))
    (HreadShape : gxLbl GD.gdG rLd = some (.LLoad aq a ts0 vs0))
    (HtsLen : ts0.length = 8) (HvsLen : vs0.length = 8)
    (HpoSdLd : WeakRvwmoGraph.gpo GD.gdG rSd rLd)
    (HsBefore : List (List Hent)) (HlensBefore : HsBefore.length = 8)
    (HwrBefore : ∀ (j : Nat) (H : List Hent), HsBefore[j]? = some H →
      ∀ p, p ∈ H → gwritesByte GD.gdG p.1 (a + (j : Int)) p.2)
    (HchBefore : ∀ (j : Nat) (H : List Hent), HsBefore[j]? = some H →
      chainWith (gmoLt GD.gdG) (H.map Prod.fst))
    (HownBefore : ∀ (j : Nat) (H : List Hent), HsBefore[j]? = some H →
      ∀ w v, gwritesByte GD.gdG w (a + (j : Int)) v → WeakRvwmoGraph.gpo GD.gdG w rSd →
        w ∈ H.map Prod.fst)
    (HlinkBefore : ∀ (j : Nat) (H : List Hent) wlast vlast, HsBefore[j]? = some H →
      H.getLast? = some (wlast, vlast) → WeakRvwmoGraph.gpo GD.gdG wlast rSd)
    (HmidNoW : ∀ (j : Nat) w v, j < 8 → gwritesByte GD.gdG w (a + (j : Int)) v →
      WeakRvwmoGraph.gpo GD.gdG rSd w → WeakRvwmoGraph.gpo GD.gdG w rLd → False)
    (ra : BitVec 5) (Hra : ra.toNat ≠ 0) (sM : ExecSt)
    (Hpriv : sM.regs .cur_privilege = .Machine) (Hsec : sM.regs .mseccfg = 0#64)
    (HC : (_get_Misa_C (sM.regs .misa) == 1#1) = true)
    (Hbridge : sM.gpr ra = wordOfBytes 8 Vs) :
    ⊢ (∀ (j : Nat) (w : Geid) (v : BitVec 8), ⌜gwritesByte GD.gdG w (a + (j : Int)) v⌝ -∗
        ⌜gmoLt GD.gdG w rLd⌝ -∗
        ∃ H' : List Hent, ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap (GF := GF) γ (a + (j : Int)) H') -∗
      tokn γ GD a (writenHist rSd Vs HsBefore) ({[rSd := (1 : Qp)]} : GMapF Geid Qp) -∗
      ⌜graphValue GD rLd = some Vs ∧
        execEff (execute (.JALR (zeros (n := 12), .Regidx ra, zreg))) sM =
          some (RETIRE_SUCCESS, sM.setReg .nextPC (WeakLeafMret.retPc (wordOfBytes 8 Vs)), []) ∧
        (sM.setReg .nextPC (WeakLeafMret.retPc (wordOfBytes 8 Vs))).regs .nextPC =
          WeakLeafMret.retPc (wordOfBytes 8 Vs)⌝ := by
  have Hj8Of : ∀ (j : Nat) (Hb0 : List Hent), HsBefore[j]? = some Hb0 → j < 8 := by
    intro j Hb0 h
    have := lookup_lt_Some h
    omega
  have HgwbSd : ∀ (j : Nat), j < 8 → gwritesByte GD.gdG rSd (a + (j : Int)) (Vs.getD j 0) :=
    fun j hj => AxEpilogue.gwritesOfStore GD.gdG rSd rl a Vs kCls j _ HwriteShape
      (AxEpilogue.getDSome Vs j (by omega))
  have Hrule1 : ∀ e1 e2, gppo1 GD.gdG e1 e2 → gmoLt GD.gdG e1 e2 :=
    fun e1 e2 h => Hcons.2.1 e1 e2 (Or.inl (Or.inl h))
  have Hinv := AxProtBytes.writenHistLookupInv rSd Vs HsBefore
  have Hlens : (writenHist rSd Vs HsBefore).length = 8 := by
    rw [writenHistLength]; exact HlensBefore
  have HlastSpill : ∀ (j : Nat) (H : List Hent), (writenHist rSd Vs HsBefore)[j]? = some H →
      ∃ v, H.getLast? = some (rSd, v) ∧ Vs[j]? = some v := by
    intro j H HjH
    obtain ⟨Hb0, HbEq, rfl⟩ := Hinv j H HjH
    exact ⟨Vs.getD j 0, List.getLast?_concat, AxEpilogue.getDSome Vs j (by have := Hj8Of j Hb0 HbEq; omega)⟩
  have Hwr : ∀ (j : Nat) (H : List Hent), (writenHist rSd Vs HsBefore)[j]? = some H →
      ∀ p, p ∈ H → gwritesByte GD.gdG p.1 (a + (j : Int)) p.2 := by
    intro j H HjH p Hp
    obtain ⟨Hb0, HbEq, rfl⟩ := Hinv j H HjH
    rcases List.mem_append.1 Hp with Hp | Hp
    · exact HwrBefore j Hb0 HbEq p Hp
    · rw [List.mem_singleton] at Hp
      subst Hp
      exact HgwbSd j (Hj8Of j Hb0 HbEq)
  have Hch : ∀ (j : Nat) (H : List Hent), (writenHist rSd Vs HsBefore)[j]? = some H →
      chainWith (gmoLt GD.gdG) (H.map Prod.fst) := by
    intro j H HjH
    obtain ⟨Hb0, HbEq, rfl⟩ := Hinv j H HjH
    rw [List.map_append]
    apply chainWithSnoc _ _ _ (HchBefore j Hb0 HbEq)
    intro wlast HlastW
    cases Hlast0 : Hb0.getLast? with
    | none =>
      rw [List.getLast?_eq_none_iff] at Hlast0
      subst Hlast0
      simp at HlastW
    | some p =>
      obtain ⟨wl0, vl0⟩ := p
      obtain ⟨Hb0', rfl⟩ := List.getLast?_eq_some_iff.1 Hlast0
      have Hwl : wl0 = wlast := by
        rw [List.map_append] at HlastW
        simp only [List.map_cons, List.map_nil, List.getLast?_concat, Option.some.injEq] at HlastW
        exact HlastW
      subst Hwl
      have Hmem : (wl0, vl0) ∈ Hb0' ++ [(wl0, vl0)] :=
        List.mem_append_right _ (List.mem_singleton_self _)
      have HwbWlast := HwrBefore j _ HbEq (wl0, vl0) Hmem
      have HgpoWlastSd := HlinkBefore j _ wl0 vl0 HbEq Hlast0
      exact Hrule1 wl0 rSd ⟨HgpoWlastSd, a + (j : Int), Or.inl ⟨vl0, HwbWlast⟩, Vs.getD j 0,
        HgwbSd j (Hj8Of j _ HbEq)⟩
  have Hown : ∀ (j : Nat) (H : List Hent), (writenHist rSd Vs HsBefore)[j]? = some H →
      ∀ w v, gwritesByte GD.gdG w (a + (j : Int)) v → WeakRvwmoGraph.gpo GD.gdG w rLd →
        w ∈ H.map Prod.fst := by
    intro j H HjH w v Hwb HpoWRld
    obtain ⟨Hb0, HbEq, rfl⟩ := Hinv j H HjH
    rw [List.map_append, List.mem_append]
    by_cases Hne : w = rSd
    · subst Hne
      exact Or.inr (List.mem_singleton_self _)
    have Hw1 : w.1 = rSd.1 := HpoWRld.1.trans HpoSdLd.1.symm
    have Hwlbl := WeakRvwmoLock.gwritesByteLbl _ _ _ _ Hwb
    have Hsdlbl : (gxLbl GD.gdG rSd).isSome := by rw [HwriteShape]; rfl
    by_cases Hlt2 : w.2 < rSd.2
    · exact Or.inl (HownBefore j Hb0 HbEq w v Hwb ⟨Hw1, Hlt2, Hwlbl, Hsdlbl⟩)
    · have Hw2ne : w.2 ≠ rSd.2 := fun Heq2 => Hne (Prod.ext Hw1 Heq2)
      have Hgt2 : rSd.2 < w.2 := by omega
      exact (HmidNoW j w v (Hj8Of j Hb0 HbEq) Hwb ⟨Hw1.symm, Hgt2, Hsdlbl, Hwlbl⟩ HpoWRld).elim
  exact epilogueRetTargetOwn2 γ GD Hcons row tBegin tEnd Hwelldef rSd rLd a Vs Hlen8
    (writenHist rSd Vs HsBefore) Hlens HlastSpill aq ts0 vs0 HreadShape HtsLen HvsLen Hwr Hch Hown
    HpoSdLd ra Hra sM Hpriv Hsec HC Hbridge

end epilogueSpill

end Weak
