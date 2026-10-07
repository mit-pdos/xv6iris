/-
Weak: **the `c.ldsp → c.jr` handoff of the J0 epilogue** — the load's EXACT exit, and the c.jr
`wpd` at every such exit, for both tick bits.

Rocq: `iris/AxEpiLdJr.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 EXACT LOAD EXIT.  `ldFinal t … u' u o w` recomputes the load's path (boundary pin answers;
`o = none`: tick = false, `epure` tail; `o = some (u2', u2)`: tick = true, `toPin` to the tick's
pin reads answered `u2'`/`u2`, then `epure`) with the data read returning the bytes `w`.  The case
index is `Ldc` (the store's boundary answers, the load's boundary answers, the tick tail);
`ldOut c w` is the register file at the `.pure ()`.  `wpdCldspAfterSdExact`: after the c.sdsp
(registers `tAfterSd v' v`), `riscvStep tick` owes its continuation only at
`RetX cpu (ldOut c w)` with the case's store answers `v' v` and tick bit `tick` (row end unchanged:
`ldAfterSdInv`).  `ldOutX1`: x1 of the exit is `ldVal (wordOfBytes 8 w)`.  No `RegFile` equality is
stated downstream: the other registers are pinned by agreement facts.
§2 c.jr AT EVERY EXIT.  tick = false: `wpdCjrFrame` (`ldOutAgreeJr`: agreement with `probeRegs
pcJr` on `AJrFix`).  tick = true: the reference is the real exit at a fixed word, `ldRef c ra`
(`ldOutAgreeRef`); after an UNticked load the c.jr tick has the usual pin re-reads
(`CjrTickFrameFacts`); after a TICKED load `mtime ≥ mtimecmp` already has MTIP pending, mip does
not change, and the c.jr's `clint_dispatch` reads NO pin — a flat `epure` tail, for which this file
adds the general-tick ledger `AxEpiModelFactsG` / `CjrFrameFactsG` / `AxEpiLdJr.ledgerInvG`
(`wpdCjrStepOfLedgerG`, `wpdCjrFrameGenG`, `ledgerInvGReachesRet`).  Packaged:
`wpdCjrAfterLd c w tick` with row-end set `cjrAfterLdInv` (sanity `cjrAfterLdInvReachesRet`).

## Deviations from Rocq

1. THE TWO-PIN BOUNDARY (`AxEpiLedger` deviation 1, the CONVENTION).  Every Rocq `to_seip` split is
   the `sig_meip` split then the `sig_seip` split, at the instruction boundary AND in the load's
   tick tail.  So `ldFinal` takes the two boundary answers `u' u` and `ldTail`'s tick answer is a
   PAIR `o : Option (BitVec 1 × BitVec 1)` (meip, seip); `Ldc` has the fields `lcV' lcV` (store),
   `lcU' lcU` (load), `lcT` (Rocq `lc_v`, `lc_u`, `lc_t`): 4·4·5 = 80 cases (Rocq 12);
   `wpdCldspAfterSdExact` takes `v' v` and its exit fixes `c.lcV' = v'`, `c.lcV = v`;
   `TailX` quantifies both tail answers; `seipAtG`/`branchAtG`/`branchAtAgG` walk the two pin
   nodes, `branchAtG`/`branchAtAgG` take `v' v`, the G-ledgers add `…MeipDr`/`…MeipD` and have four
   branch fields `…00/01/10/11`; `AxEpiLdJr.ledgerInvG` is `AxEpiLedger.ledgerInv` at a general tick (the
   meip-level `Pseip` disjunct, the seip node per meip answer); `branchRefNone`/`branchRefSome`
   take both answers `a' a`; `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg`.
2. O2 STAGE C (`AxEpiLedger` deviation 3): the fetch is a pinned admin step at the SAME row
   position.  `Hgd` states `AxCjrWpd.fetchImgOk` (Rocq `fetch_gd_ok`); `Hflow`/`Hloc` are dropped;
   `Hntext` is dropped (the load ledgers check `akIfetch = false`, `AxEpiLedgerTick` deviation 3);
   positions: c.jr `RetS`/`RetP`, the post-fetch `Pbefore` of `AxEpiLdJr.ledgerInvG` at `kk` (Rocq `S kk`);
   load `Hrow` and flow at `kk`, `LdRetX`/`RetX`/the tick tail at `kk + 1` (Rocq `S (S kk)`);
   `wpdLoadThenTickExact`'s tail at `k + 1` (Rocq `S k`), `wpdFetchThenLoadTickExact`'s at
   `k + 1` (Rocq `S (S k)`).  Generic `hlc` (Rocq `HasNoLc`).
3. THE PINS AS FOOTPRINT (`AxEpiCjrFrame` deviation 3): `LJrT` is `AJrT` minus `x1` — Rocq's list
   minus `sig_meip` (a pin in Lean, not in `AJr`).  `AJrTSub` states the list inclusion
   `AJrT.filter (· ≠ x1) ⊆ LJrT` (Rocq `A_jr_t ∖ {[x1]} ⊆ list_to_set L_jr_t`).
4. THE KERNEL ROUTE.  Rocq proves `ld_out_x1`, `ld_out_agree_jr`, `ld_out_agree_ref` per case
   (`vm_compute`, `change_no_check`) and the four ref ledgers by `cjr_frame_tac` at `ld_ref`
   itself.  Lean (80 cases): the exit does not depend on the pin answers (no interrupt is enabled
   in M-mode with `mstatus.MIE = 0`, and the pins are only read), which the kernel checks as
   Lean-only COLLAPSE equations `AxEpiLdJr.tAfterSdEq` (store answers) and `AxEpiLdJr.ldFinalEq`
   (load answers and tick answers), giving `AxEpiLdJr.ldOutCanon : ldOut c w = ldOut (canon c) w`;
   so every per-case fact is two kernel checks (tick = false / true) with the loaded bytes `w`
   free (`ax_epi_ledger_krfl`), stated as one equation of register OBSERVATIONS
   (`AxEpiLdJr.obsL L rs`, the list of dependent pairs `⟨r, rs r⟩`, `r ∈ L`;
   `AxEpiLdJr.agreeOfObsL`/`allEqOfObsL` turn it into `agreeOn`/`allEq`).  The ref ledgers
   `cjrRefFactsNone`/`cjrRefFactsSome` are not re-run at `ldRef` (the kernel would recompute the
   whole load at every spine step): they are TRANSFERRED from frames at small reference states
   (`AxEpiCjrFrame.epiFrameCjrTick` at `tFrameT`, and the Lean-only `AxEpiLdJr.epiFrameCjrTickG`
   at `AxEpiLdJr.tFrameS` = `tFrameT` with the ticked load's `mtime = 1`, `mip = MTIP`, checked
   by `ax_epi_cjr_frame_tac`) along agreement on `AJrT`, by Lean-only TRACKED-TO-TRACKED transfer
   lemmas (`AxEpiLdJr.toPinAgAg` … `AxEpiLdJr.tickFrameFactsAg`, `AxEpiLdJr.frameFactsGAg`);
   `branchRefNone`/`branchRefSome` are read off the transferred ledgers (Rocq: the converse
   order).
5. TYPES (as `AxEpiCjrFrame` deviation 5): `gset register` ↦ `List Register`, `register_lookup r
   rs` ↦ `rs r`, `register_set x1 ra rs` ↦ `rs.set .x1 ra`, `MState rs probe_mem dev0_state` ↦
   `⟨rs, probeMem, testDevs⟩`, `Dr_noseip` ↦ `AxEpiProbe.drNopin`, `D_post` ↦ `DPost`, `ld_vs` ↦
   `AxEpiLedger.ldVs`, `default d o` ↦ `o.getD d`, `inl (w, None)` ↦ `.Ok (w, none)`, `Ret tt` ↦
   `.pure ()`, `BV 8 0` ↦ `0#8`; `all_eq` is a structural `def` over `List Register`;
   `agree_on_all_eq` concludes `agreeOn L` (Rocq `list_to_set L`); `agree_on_set_x1` takes the
   filtered list (Rocq `A ∖ {[x1]}`); `ld_out_x1_unsigned` states `toNat`.
   `wpdCldspStepOfLedgerAgreeExact`'s word-to-bytes step uses `WeakInterpProj.wbytes` /
   `wordOfBytesWbytes` (Rocq `word_of_bytes_wbytes`).
6. Not ported: the Ltacs `case_ldc` and `reg_cases` (proof-local; no downstream use), the
   `Print Assumptions` block (the lint's axiom check covers it), `Set Printing Depth`.

**Rocq → Lean name map.**  `ld_tail` `ldTail`, `ld_after_load` `ldAfterLoad`, `ld_after_fetch`
`ldAfterFetch`, `tick_of` `tickOf`, `ld_final` `ldFinal`, `ldc`/`LdC` `Ldc`/`Ldc.LdC` (fields
`lcV'`, `lcV`, `lcU'`, `lcU`, `lcT`), `ld_out` `ldOut`, `w0` `AxEpiLdJr.w0` (dup), `ld_ref`
`ldRef`, `seip_at_g` `seipAtG`, `branch_at_g` `branchAtG`, `AxEpiModelFactsG` `AxEpiModelFactsG`
(`lfg*`), `ledger_inv_g` `AxEpiLdJr.ledgerInvG`, `ledger_branch_g` `ledgerBranchG`,
`ledger_inv_g_reaches_ret` `ledgerInvGReachesRet`, `branch_at_ag_g` `branchAtAgG`,
`CjrFrameFactsG` `CjrFrameFactsG` (`cfg*`), `frame_facts_transfer_g` `frameFactsTransferG`,
`wpd_cjr_step_of_ledger_g` `wpdCjrStepOfLedgerG`, `wpd_cjr_frame_gen_g` `wpdCjrFrameGenG`,
`ld_final_chain` `ldFinalChain`, `LdRetX` `LdRetX`, `TailX` `TailX`,
`wpd_cldsp_step_of_ledger_agree_exact` `wpdCldspStepOfLedgerAgreeExact`, `wpd_tick_tail_exact`
`wpdTickTailExact`, `wpd_load_then_tick_exact` `wpdLoadThenTickExact`,
`wpd_fetch_then_load_tick_exact` `wpdFetchThenLoadTickExact`,
`wpd_cldsp_step_of_ledger_tick_exact` `wpdCldspStepOfLedgerTickExact`,
`wpd_cldsp_after_sd_exact` `wpdCldspAfterSdExact`, `ld_out_x1` `ldOutX1`, `ld_out_x1_unsigned`
`ldOutX1Unsigned`, `ld_out_agree_jr` `ldOutAgreeJr`, `all_eq` `allEq`, `agree_on_all_eq`
`agreeOnAllEq`, `agree_on_mono` `agreeOnMono`, `agree_on_set_x1` `agreeOnSetX1`, `L_jr_t` `LJrT`,
`A_jr_t_sub` `AJrTSub`, `ld_out_agree_ref` `ldOutAgreeRef`, `branch_ref_none` `branchRefNone`,
`cjr_ref_facts_none` `cjrRefFactsNone`, `branch_ref_some` `branchRefSome`, `cjr_ref_facts_some`
`cjrRefFactsSome`, `ra_of` `raOf`, `ld_out_agree_ref'` `ldOutAgreeRef'`, `cjr_after_ld_inv`
`cjrAfterLdInv`, `rtc_ledger_ld_step` `rtcLedgerLdStep`, `cjr_after_ld_inv_reaches_ret`
`cjrAfterLdInvReachesRet`, `wpd_cjr_after_ld` `wpdCjrAfterLd`.  Only `w0` is in the
duplicated-name table.  Lean-only (file-qualified, `AxEpiLdJr.*`): `seipAtGSpec`, `seipAtGNext`,
`branchAtGEq`, `canon`, `tAfterSdEq`, `ldFinalEq`, `ldOutCanon`, `obsL`, `agreeOfObsL`,
`allEqOfObsL`, `LFix`, `fixSub`, `obsFixEq`, `obsRefEq`, `LNone`, `noneSub`, `obsNoneEq`,
`agreeTFrameT`, `LSome`, `someSub`, `obsSomeEq`, `tFrameS`, `agreeTFrameS`, `branchFrameTickGSym`,
`epiFrameCjrTickG`, the tracked-to-tracked transfers `toPinAgAg`, `erdAgAg`, `epureAgAg`,
`fetchOkAgAg`, `branchOkAgAg`, `seipAfterAgAg`, `seipAtAgAg`, `branchAtAgGAg`, `tickRetOkAgAg`,
`tickAfterMeipAgAg`, `tickPostOkAgAg`, `fetchOkTickAgAg`, `branchOkTickAgAg`,
`branchAtTickAgAg`, `tickFrameFactsAg`, `frameFactsGAg`.

**Dropped:** nothing (Rocq 49 definitions/lemmas/records; Lean 49 + 41 Lean-only helpers above).
Builds in about 90 s.
-/
import Weak.AxEpiCjrFrame
import Weak.AxEpiLdX1
import Weak.AxEpiLedgerTick2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! # 1. The exact exit of the load -/

/-- The load's tail after the data read: `none` — tick = false, `epure`; `some (u2', u2)` — tick
= true, `toPin` to the tick's `sig_meip` read (answered `u2'`), `toPin` to its `sig_seip` read
(answered `u2`), then `epure`. -/
def ldTail (D : List Register) (o : Option (BitVec 1 × BitVec 1)) (m : SailM Unit) (t : ExecSt) :
    Option ExecSt :=
  match o with
  | none =>
    match epure D m t with
    | some (_, s) => some s
    | none => none
  | some (u2', u2) =>
    match AxEpiLedger.toPin m t with
    | some (m1, t4) =>
      match AxEpiLedger.toPin (AxEpiLedger.ansMeip m1 u2') t4 with
      | some (m2, t5) =>
        match epure D (ansSeip m2 u2) t5 with
        | some (_, s) => some s
        | none => none
      | none => none
    | none => none

def ldAfterLoad (D : List Register) (o : Option (BitVec 1 × BitVec 1)) (w : List (BitVec 8))
    (ml : SailM Unit) (tl : ExecSt) : Option ExecSt :=
  match ml with
  | .impure (.ok (.memRead nl _ _)) KK => ldTail D o (KK (.Ok (wordOfBytes nl w, none))) tl
  | _ => none

def ldAfterFetch (Dr Dw D : List Register) (vs : List (BitVec 8))
    (o : Option (BitVec 1 × BitVec 1)) (w : List (BitVec 8)) (mf : SailM Unit) (t2 : ExecSt) :
    Option ExecSt :=
  match mf with
  | .impure (.ok (.memRead n _ _)) KKf =>
    match erd Dr Dw (KKf (.Ok (wordOfBytes n vs, none))) t2 with
    | some (ml, tl) => ldAfterLoad D o w ml tl
    | none => none
  | _ => none

def tickOf (o : Option (BitVec 1 × BitVec 1)) : Bool :=
  match o with
  | some _ => true
  | none => false

/-- The load's final state for the boundary answers `u'` (`sig_meip`), `u` (`sig_seip`), the
tick tail `o` and the read bytes `w`. -/
noncomputable def ldFinal (t : ExecSt) (Dr Dw D : List Register) (vs : List (BitVec 8))
    (u' u : BitVec 1) (o : Option (BitVec 1 × BitVec 1)) (w : List (BitVec 8)) : Option ExecSt :=
  match AxEpiLedger.toPin (riscvStep (tickOf o)) t with
  | some (m0, t0) =>
    match AxEpiLedger.toPin (AxEpiLedger.ansMeip m0 u') t0 with
    | some (m1, t1) =>
      match erd Dr Dw (ansSeip m1 u) t1 with
      | some (mf, t2) => ldAfterFetch Dr Dw D vs o w mf t2
      | none => none
    | none => none
  | none => none

/-- The case index: the store's boundary answers, the load's boundary answers, the tick tail. -/
structure Ldc where
  LdC ::
  lcV' : BitVec 1
  lcV : BitVec 1
  lcU' : BitVec 1
  lcU : BitVec 1
  lcT : Option (BitVec 1 × BitVec 1)

noncomputable def ldOut (c : Ldc) (w : List (BitVec 8)) : RegFile :=
  ((ldFinal (tAfterSd c.lcV' c.lcV) AxEpiProbe.drNopin DwAll DPost AxEpiLedger.ldVs c.lcU' c.lcU
    c.lcT w).getD (tAt pcLd)).regs

def AxEpiLdJr.w0 : List (BitVec 8) := List.replicate 8 0#8

noncomputable def ldRef (c : Ldc) (ra : BitVec 64) : ExecSt :=
  ⟨(ldOut c AxEpiLdJr.w0).set .x1 ra, probeMem, testDevs⟩

/-! # 2. The c.jr ledger at a GENERAL tick bit with an `epure` tail -/

/-- The boundary walk of `riscvStep tick` (two pin nodes, deviation 1). -/
noncomputable def seipAtG (tick : Bool) (t : ExecSt) : Bool :=
  match AxEpiLedger.toPin (riscvStep tick) t with
  | some (m0, t0) =>
    AxEpiLedger.isMeipNode m0 && AxEpiLedger.seipAfter m0 t0 0#1 &&
      AxEpiLedger.seipAfter m0 t0 1#1
  | none => false

noncomputable def branchAtG (tick : Bool) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (post : RegFile → Bool) (t : ExecSt) (v' v : BitVec 1) : Bool :=
  match AxEpiLedger.toPin (riscvStep tick) t with
  | some (m0, t0) =>
    match AxEpiLedger.toPin (AxEpiLedger.ansMeip m0 v') t0 with
    | some (m1, t1) => branchOk Dr Dw D base vs post (ansSeip m1 v) t1
    | none => false
  | none => false

structure AxEpiModelFactsG (tick : Bool) (t : ExecSt) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (post : RegFile → Bool) : Prop where
  lfgSeipDr : decide (Register.sig_seip ∈ Dr) = false
  lfgMeipDr : decide (Register.sig_meip ∈ Dr) = false
  lfgSeipD : decide (Register.sig_seip ∈ D) = false
  lfgMeipD : decide (Register.sig_meip ∈ D) = false
  lfgToSeip : seipAtG tick t = true
  lfgBranch00 : branchAtG tick Dr Dw D base vs post t 0#1 0#1 = true
  lfgBranch01 : branchAtG tick Dr Dw D base vs post t 0#1 1#1 = true
  lfgBranch10 : branchAtG tick Dr Dw D base vs post t 1#1 0#1 = true
  lfgBranch11 : branchAtG tick Dr Dw D base vs post t 1#1 1#1 = true

/-- `AxEpiLedger.ledgerInv` at a general tick bit. -/
def AxEpiLdJr.ledgerInvG (tick : Bool) (t : ExecSt) (Dr Dw D : List Register) (vs : List (BitVec 8))
    (cpu : CPU) (kk : Nat) (s1 : Athread) : Prop :=
  ∃ (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt) (ib0 : Ibch),
    AxEpiLedger.toPin (riscvStep tick) t
      = some (.impure (.ok (.regRead Register.sig_meip)) km, t0) ∧
    (Pseip (AxEpiLedger.meipNode cpu km t0.regs ib0 kk) (AxEpiLedger.seipExit cpu km t0 kk) s1 ∨
     ∃ (v' : BitVec 1) (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt)
       (ib1 : Ibch),
       AxEpiLedger.toPin (km v') t0 = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) ∧
       (Pseip (seipNode cpu k0 t1.regs ib1 kk) (erdExit Dr Dw cpu k0 t1 kk) s1 ∨
        ∃ (v : BitVec 1) (n va : Nat)
          (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
          (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit)
          (t2 t3 : ExecSt) (ib3 : Ibch),
          erd Dr Dw (k0 v) t1 = some (.impure (.ok (.memRead n va req)) KK, t2) ∧
          epure D (KK (.Ok (wordOfBytes n vs, none))) t2 = some ((), t3) ∧
          Pbefore ⟨.PHart cpu (.pure ()) t3.regs none ib3, kk⟩ s1))

/-- (Lean-only) The `seipAtG` walk: the first pin node is the `sig_meip` read. -/
theorem AxEpiLdJr.seipAtGSpec (tick : Bool) (t : ExecSt) (H : seipAtG tick t = true) :
    ∃ (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt),
      AxEpiLedger.toPin (riscvStep tick) t
        = some (.impure (.ok (.regRead Register.sig_meip)) km, t0) := by
  unfold seipAtG at H
  cases h : AxEpiLedger.toPin (riscvStep tick) t with
  | none => rw [h] at H; exact absurd H Bool.false_ne_true
  | some p =>
    obtain ⟨m0, t0⟩ := p
    rw [h] at H
    simp only [Bool.and_eq_true] at H
    obtain ⟨km, rfl⟩ := AxEpiLedger.isMeipNodeShape m0 H.1.1
    exact ⟨km, t0, rfl⟩

/-- (Lean-only) The `seipAtG` walk: after either `sig_meip` answer, the `sig_seip` node. -/
theorem AxEpiLdJr.seipAtGNext (tick : Bool) (t : ExecSt)
    (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt) (H : seipAtG tick t = true)
    (Hts : AxEpiLedger.toPin (riscvStep tick) t
      = some (.impure (.ok (.regRead Register.sig_meip)) km, t0)) (v' : BitVec 1) :
    ∃ (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt),
      AxEpiLedger.toPin (km v') t0
        = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) := by
  unfold seipAtG at H
  rw [Hts] at H
  simp only [Bool.and_eq_true] at H
  have Hv : AxEpiLedger.seipAfter (.impure (.ok (.regRead Register.sig_meip)) km) t0 v' = true := by
    rcases bv1Cases v' with rfl | rfl
    · exact H.1.2
    · exact H.2
  unfold AxEpiLedger.seipAfter at Hv
  rw [AxEpiLedger.ansMeipNode] at Hv
  cases h : AxEpiLedger.toPin (km v') t0 with
  | none => rw [h] at Hv; exact absurd Hv Bool.false_ne_true
  | some p =>
    obtain ⟨m1, t1⟩ := p
    rw [h] at Hv
    obtain ⟨k0, rfl⟩ := isSeipNodeShape m1 Hv
    exact ⟨k0, t1, rfl⟩

/-- (Lean-only) `branchAtG` at the two computed pin nodes. -/
theorem AxEpiLdJr.branchAtGEq (tick : Bool) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (post : RegFile → Bool) (t : ExecSt)
    (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt) (v' : BitVec 1)
    (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt) (v : BitVec 1)
    (Hts : AxEpiLedger.toPin (riscvStep tick) t
      = some (.impure (.ok (.regRead Register.sig_meip)) km, t0))
    (Hts1 : AxEpiLedger.toPin (km v') t0
      = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1)) :
    branchAtG tick Dr Dw D base vs post t v' v = branchOk Dr Dw D base vs post (k0 v) t1 := by
  unfold branchAtG
  rw [Hts]
  simp only []
  rw [AxEpiLedger.ansMeipNode, Hts1]
  simp only []
  rw [AxEpiLedger.ansSeipNode]

theorem ledgerBranchG (tick : Bool) (t : ExecSt) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (post : RegFile → Bool)
    (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt) (v' : BitVec 1)
    (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt) :
    AxEpiModelFactsG tick t Dr Dw D base vs post →
    AxEpiLedger.toPin (riscvStep tick) t
      = some (.impure (.ok (.regRead Register.sig_meip)) km, t0) →
    AxEpiLedger.toPin (km v') t0
      = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) →
    ∀ v, branchOk Dr Dw D base vs post (k0 v) t1 = true := by
  intro L Hts Hts1 v
  rw [← AxEpiLdJr.branchAtGEq tick Dr Dw D base vs post t km t0 v' k0 t1 v Hts Hts1]
  rcases bv1Cases v' with rfl | rfl <;> rcases bv1Cases v with rfl | rfl
  · exact L.lfgBranch00
  · exact L.lfgBranch01
  · exact L.lfgBranch10
  · exact L.lfgBranch11

/-- SANITY: the general-tick row-end set reaches `.pure ()`. -/
theorem ledgerInvGReachesRet (tick : Bool) (t : ExecSt) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (post : RegFile → Bool) (cpu : CPU) (kk : Nat) (s1 : Athread) :
    AxEpiModelFactsG tick t Dr Dw D base vs post →
    AxEpiLdJr.ledgerInvG tick t Dr Dw D vs cpu kk s1 →
    ∃ t0 s', aeqv s1 t0 ∧ rtc (AxEpiLedger.ledgerStep cpu vs) t0 s' ∧ RetS cpu post kk s' := by
  intro L ⟨km, t0, ib0, Hts, Hc⟩
  have HDr := of_decide_eq_false L.lfgSeipDr
  have HDrm := of_decide_eq_false L.lfgMeipDr
  have HD := of_decide_eq_false L.lfgSeipD
  have HDm := of_decide_eq_false L.lfgMeipD
  have Hall : ∀ v', ∃ (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt),
      AxEpiLedger.toPin (km v') t0
        = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) ∧
      ∀ v, branchOk Dr Dw D base vs post (k0 v) t1 = true := by
    intro v'
    obtain ⟨k0, t1, Hts1⟩ := AxEpiLdJr.seipAtGNext tick t km t0 L.lfgToSeip Hts v'
    exact ⟨k0, t1, Hts1, ledgerBranchG tick t Dr Dw D base vs post km t0 v' k0 t1 L Hts Hts1⟩
  rcases Hc with Hc | ⟨v', k0, t1, ib1, Hts1, Hc⟩
  · obtain ⟨sm, Hrm, Hsm⟩ :=
      AxEpiLedger.meipReaches Dr Dw D base vs post cpu kk km t0 ib0 HDr HDrm HD HDm Hall
    rcases Hc with ⟨t', Ha, Htc⟩ | Ha | ⟨q, ⟨v', k0, t1, ib1, Hts1, rfl⟩, t', Ha, Htc⟩
    · exact ⟨t', sm, Ha, rtc_transitive (rtcGstepLedgerStep cpu vs _ _ (tc_rtc Htc)) Hrm, Hsm⟩
    · exact ⟨_, sm, Ha, Hrm, Hsm⟩
    · have Hb := ledgerBranchG tick t Dr Dw D base vs post km t0 v' k0 t1 L Hts Hts1
      obtain ⟨s', Hr, Hs'⟩ :=
        AxEpiLedger.seipReaches Dr Dw D base vs post cpu kk k0 t1 ib1 HDr HDrm HD HDm Hb
      exact ⟨t', s', Ha, rtc_transitive (rtcGstepLedgerStep cpu vs _ _ (tc_rtc Htc)) Hr, Hs'⟩
  · have Hb := ledgerBranchG tick t Dr Dw D base vs post km t0 v' k0 t1 L Hts Hts1
    obtain ⟨ss, Hrs, Hss⟩ :=
      AxEpiLedger.seipReaches Dr Dw D base vs post cpu kk k0 t1 ib1 HDr HDrm HD HDm Hb
    rcases Hc with Hc | ⟨v, n, va, req, KK, t2, t3, ib3, He, Hep, t', Ha, Htc⟩
    · rcases Hc with ⟨t', Ha, Htc⟩ | Ha | ⟨q, ⟨v, qm, t2, ib2, He, rfl, -⟩, t', Ha, Htc⟩
      · exact ⟨t', ss, Ha, rtc_transitive (rtcGstepLedgerStep cpu vs _ _ (tc_rtc Htc)) Hrs, Hss⟩
      · exact ⟨_, ss, Ha, Hrs, Hss⟩
      · have Hbv := Hb v
        unfold branchOk at Hbv
        rw [He] at Hbv
        obtain ⟨n, va, req, KK, t3, rfl, -⟩ := fetchOkSpec _ _ _ _ _ _ Hbv
        obtain ⟨s', Hr, Hs'⟩ :=
          ledgerFetchReaches D base vs post cpu kk n va req KK t2 ib2 HD HDm Hbv
        exact ⟨t', s', Ha, rtc_transitive (rtcGstepLedgerStep cpu vs _ _ (tc_rtc Htc)) Hr, Hs'⟩
    · have Hbv := Hb v
      unfold branchOk at Hbv
      rw [He] at Hbv
      exact ⟨t', _, Ha, rtcGstepLedgerStep cpu vs _ _ (tc_rtc Htc),
        t3.regs, ib3, fetchOkMem D base vs post n va req KK t2 t3 Hbv Hep, aeqvHartRefl ..⟩

/-- The tracked general-tick branch. -/
noncomputable def branchAtAgG (tick : Bool) (A Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (P : List Register) (post : RegFile → Bool) (t : ExecSt)
    (v' v : BitVec 1) : Bool :=
  match toPinAg A (riscvStep tick) t with
  | some (m0, t0, A0) =>
    match toPinAg A0 (AxEpiLedger.ansMeip m0 v') t0 with
    | some (m1, t1, A1) => branchOkAg A1 Dr Dw D base vs P post (ansSeip m1 v) t1
    | none => false
  | none => false

structure CjrFrameFactsG (tick : Bool) (t : ExecSt) (A Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (P : List Register) (post : RegFile → Bool) : Prop where
  cfgSeipDr : decide (Register.sig_seip ∈ Dr) = false
  cfgMeipDr : decide (Register.sig_meip ∈ Dr) = false
  cfgSeipD : decide (Register.sig_seip ∈ D) = false
  cfgMeipD : decide (Register.sig_meip ∈ D) = false
  cfgToSeip : seipAtAg A tick t = true
  cfgBranch00 : branchAtAgG tick A Dr Dw D base vs P post t 0#1 0#1 = true
  cfgBranch01 : branchAtAgG tick A Dr Dw D base vs P post t 0#1 1#1 = true
  cfgBranch10 : branchAtAgG tick A Dr Dw D base vs P post t 1#1 0#1 = true
  cfgBranch11 : branchAtAgG tick A Dr Dw D base vs P post t 1#1 1#1 = true

theorem frameFactsTransferG (tick : Bool) (t : ExecSt) (A Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (P : List Register) (post : RegFile → Bool) (t' : ExecSt) :
    CjrFrameFactsG tick t A Dr Dw D base vs P post → postLocal P post →
    agreeOn A t.regs t'.regs → AxEpiModelFactsG tick t' Dr Dw D base vs post := by
  intro F Hpl Hag
  obtain ⟨m0, t0, A0, t0', hts, hts', hag0, Hs⟩ :=
    AxEpiCjrFrame.seipAtAgTransfer A tick t t' F.cfgToSeip Hag
  have Hbr : ∀ v' v, branchAtAgG tick A Dr Dw D base vs P post t v' v = true →
      branchAtG tick Dr Dw D base vs post t' v' v = true := by
    intro v' v H
    unfold branchAtAgG at H
    rw [hts] at H
    unfold branchAtG
    rw [hts']
    simp only [] at H ⊢
    cases h2 : toPinAg A0 (AxEpiLedger.ansMeip m0 v') t0 with
    | none => rw [h2] at H; exact absurd H Bool.false_ne_true
    | some q =>
      obtain ⟨m1, t1, A1⟩ := q
      rw [h2] at H
      obtain ⟨t1', h2', hag1⟩ := toPinAgSound _ A0 t0 t0' m1 t1 A1 h2 hag0
      rw [h2']
      exact branchOkAgTransfer A1 Dr Dw D base vs P post _ t1 t1' Hpl H hag1
  exact {
    lfgSeipDr := F.cfgSeipDr
    lfgMeipDr := F.cfgMeipDr
    lfgSeipD := F.cfgSeipD
    lfgMeipD := F.cfgMeipD
    lfgToSeip := by unfold seipAtG; rw [hts']; exact Hs
    lfgBranch00 := Hbr _ _ F.cfgBranch00
    lfgBranch01 := Hbr _ _ F.cfgBranch01
    lfgBranch10 := Hbr _ _ F.cfgBranch10
    lfgBranch11 := Hbr _ _ F.cfgBranch11 }

section ledgerG
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- The whole-instruction c.jr `wpd` from the general-tick ledger. -/
theorem wpdCjrStepOfLedgerG (tick : Bool) (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
    (ib : Ibch) (kk : Nat) (t : ExecSt) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (post : RegFile → Bool)
    (L : AxEpiModelFactsG tick t Dr Dw D base vs post)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk base vs⌝) :
    ⊢ ((∀ s', ⌜RetS cpu post kk s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1, ⌜AxEpiLdJr.ledgerInvG tick t Dr Dw D vs cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep tick) t.regs none ib, kk⟩ Φ := by
  have HDr := of_decide_eq_false L.lfgSeipDr
  have HDrm := of_decide_eq_false L.lfgMeipDr
  have HD := of_decide_eq_false L.lfgSeipD
  have HDm := of_decide_eq_false L.lfgMeipD
  obtain ⟨km, t0, Hts⟩ := AxEpiLdJr.seipAtGSpec tick t L.lfgToSeip
  have Hnext := AxEpiLdJr.seipAtGNext tick t km t0 L.lfgToSeip Hts
  obtain ⟨ib0, Hr0⟩ := AxEpiLedger.toPinGstep _ t ib _ _ Hts cpu kk
  iintro R
  iapply (AxEpiLedger.wpdOfSplitFrom i Φ _ _ _
    (AxEpiLedger.pseipStart cpu _ t.regs ib kk _ (AxEpiLedger.seipExit cpu km t0 kk) Hr0)
    (AxEpiLedger.meipN0Ok cpu km t0 ib0 kk Hnext))
  isplit
  · iintro %s2 %HQ
    obtain ⟨q, ⟨v', k0, t1, ib1, Hts1, rfl⟩, Hq⟩ := HQ
    have Hb := ledgerBranchG tick t Dr Dw D base vs post km t0 v' k0 t1 L Hts Hts1
    iapply (AxEpiLedger.wpdOfSplitFrom i Φ s2 _ (erdExit Dr Dw cpu k0 t1 kk) (.inr (.inl Hq))
      (AxEpiLedger.seipN0Ok cpu k0 t1 ib1 kk Dr Dw HDr HDrm
        (fun v => AxEpiLedger.erdOfBranch Dr Dw D base vs post _ t1 (Hb v))))
    isplit
    · iintro %s3 %HQ3
      obtain ⟨q3, ⟨v, qm, t2, ib2, He, rfl, -⟩, Hs3⟩ := HQ3
      have Hbv := Hb v
      unfold branchOk at Hbv
      rw [He] at Hbv
      obtain ⟨n, va, req, KK, t3, rfl, Hdev, Hfe, Hpa, Hlen, Hep, Hpost⟩ :=
        fetchOkSpec _ _ _ _ _ _ Hbv
      subst Hpa
      obtain ⟨p3, k3⟩ := s3
      obtain ⟨hk, hp⟩ := Hs3
      simp only at hk hp
      subst k3
      match p3, hp with
      | .PHart c3 m3 rs3 fn3 ib3', hp =>
        obtain ⟨hc, hm, hf, hi, hag⟩ := hp
        subst c3 m3 fn3 ib3'
        obtain ⟨ib3, Hrun⟩ := epureGstepRtc D HD HDm _ _ _ _ Hep cpu ib2 kk
        iapply (wpdFetchThenRunAgree Φ i cpu n va req KK ib2 kk vs t2.regs rs3 _ Hdev Hfe
          Hlen Hgd (regsAgreeSym _ _ _ hag) Hrun)
        isplit
        · icases R with ⟨R, -⟩
          iintro %s' %Hs'
          iapply R $$ %s' %⟨t3.regs, ib3, Hpost, Hs'⟩
        · icases R with ⟨-, R⟩
          iintro %GD %s1 %Hs1 %Hlen1
          iapply R $$ %GD %s1
            %⟨km, t0, ib0, Hts, .inr ⟨v', k0, t1, ib1, Hts1,
              .inr ⟨v, n, va, req, KK, t2, t3, ib3, He, Hep, Hs1⟩⟩⟩ %Hlen1
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %Hs1 %Hlen1
      iapply R $$ %GD %s1 %⟨km, t0, ib0, Hts, .inr ⟨v', k0, t1, ib1, Hts1, .inl Hs1⟩⟩ %Hlen1
  · icases R with ⟨-, R⟩
    iintro %GD %s1 %Hs1 %Hlen1
    iapply R $$ %GD %s1 %⟨km, t0, ib0, Hts, .inl Hs1⟩ %Hlen1

theorem wpdCjrFrameGenG (tick : Bool) (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
    (ib : Ibch) (kk : Nat) (t0 : ExecSt) (A Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (P : List Register) (post : RegFile → Bool)
    (F : CjrFrameFactsG tick t0 A Dr Dw D base vs P post) (Hpl : postLocal P post)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk base vs⌝)
    (rs : RegFile) (Hag : agreeOn A rs t0.regs) :
    ⊢ ((∀ s', ⌜RetS cpu post kk s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜AxEpiLdJr.ledgerInvG tick ⟨rs, t0.mem, t0.dev⟩ Dr Dw D vs cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep tick) rs none ib, kk⟩ Φ :=
  wpdCjrStepOfLedgerG tick i Φ cpu ib kk ⟨rs, t0.mem, t0.dev⟩ _ _ _ _ _ _
    (frameFactsTransferG tick t0 A Dr Dw D base vs P post ⟨rs, t0.mem, t0.dev⟩ F Hpl
      (agreeOnSym _ _ _ Hag)) Hgd

end ledgerG

/-! # 3. The c.ldsp with an EXACT exit -/

theorem ldFinalChain (t : ExecSt) (Dr Dw D : List Register) (vs : List (BitVec 8))
    (u' u : BitVec 1) (o : Option (BitVec 1 × BitVec 1)) (w : List (BitVec 8))
    (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt)
    (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt)
    (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KKf : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (t2 : ExecSt)
    (nl val : Nat) (reql : Mem_read_request nl val Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * nl) × Option Bool) Arch.abort → SailM Unit) (tl t3 : ExecSt) :
    AxEpiLedger.toPin (riscvStep (tickOf o)) t
      = some (.impure (.ok (.regRead Register.sig_meip)) km, t0) →
    AxEpiLedger.toPin (km u') t0 = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) →
    erd Dr Dw (k0 u) t1 = some (.impure (.ok (.memRead n va req)) KKf, t2) →
    erd Dr Dw (KKf (.Ok (wordOfBytes n vs, none))) t2
      = some (.impure (.ok (.memRead nl val reql)) KK, tl) →
    ldTail D o (KK (.Ok (wordOfBytes nl w, none))) tl = some t3 →
    ldFinal t Dr Dw D vs u' u o w = some t3 := by
  intro Hts Hts1 He He2 Ht
  unfold ldFinal
  rw [Hts]
  dsimp only
  rw [AxEpiLedger.ansMeipNode, Hts1]
  dsimp only
  rw [ansSeipNode, He]
  dsimp only [ldAfterFetch]
  rw [He2]
  dsimp only [ldAfterLoad]
  exact Ht

/-- The exact exit set of the load: the `.pure ()` node at the register file `ldFinal` computes,
for some boundary answers `u' u`, tick tail `o` and read bytes `w`. -/
def LdRetX (t : ExecSt) (Dr Dw D : List Register) (vs : List (BitVec 8)) (tick : Bool) (cpu : CPU)
    (k : Nat) (s : Athread) : Prop :=
  ∃ (u' u : BitVec 1) (o : Option (BitVec 1 × BitVec 1)) (w : List (BitVec 8)) (t3 : ExecSt),
    tickOf o = tick ∧ ldFinal t Dr Dw D vs u' u o w = some t3 ∧ RetX cpu t3.regs k s

/-- The exact exit of the tick tail (both tail pin answers). -/
def TailX (D : List Register) (cpu : CPU) (m : SailM Unit) (tl : ExecSt) (k : Nat)
    (s : Athread) : Prop :=
  ∃ (u2' u2 : BitVec 1) (t5 : ExecSt), ldTail D (some (u2', u2)) m tl = some t5 ∧
    RetX cpu t5.regs k s

section ldExact
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem wpdCldspStepOfLedgerAgreeExact (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
    (ib : Ibch) (kk : Nat) (t : ExecSt) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (postLd : Int → RegFile → Prop)
    (Rv : Gdexec → List (BitVec 8) → IProp GF)
    (L : AxLdModelFacts t Dr Dw D base vs ldaddr postLd)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk base vs⌝)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i kk⌝)
    (rs : RegFile) (Hag0 : regsAgree AxRunClose.pinReg t.regs rs) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i kk ls -∗
         ⌜graphValue GD (i, kk) = some v⌝ -∗ loadFlow GD i kk (Rv GD v)) -∗
      ((∀ s', ⌜LdRetX t Dr Dw D vs false cpu (kk + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1, ⌜ledgerLdInv t Dr Dw D vs cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) rs none ib, kk⟩ Φ := by
  have HDr := of_decide_eq_false L.lgSeipDr
  have HDrm := of_decide_eq_false L.lgMeipDr
  have HD := of_decide_eq_false L.lgSeipD
  have HDm := of_decide_eq_false L.lgMeipD
  obtain ⟨km, t0, Hts⟩ := AxEpiLedger.seipAtSpec t L.lgToSeip
  have Hnext := AxEpiLedger.seipAtNext t km t0 L.lgToSeip Hts
  obtain ⟨ib0, Hr0⟩ := AxEpiLedger.toPinGstep _ t ib _ _ Hts cpu kk
  iintro F R
  iapply (wpdOfSeipSplitRtc i Φ _ _ _ (AxEpiLedger.seipExit cpu km t0 kk)
    (aeqvOfAgree cpu (riscvStep false) rs t.regs none ib kk Hag0) Hr0
    (AxEpiLedger.meipN0Ok cpu km t0 ib0 kk Hnext))
  isplit
  · iintro %s2 %HQ
    obtain ⟨q, ⟨v', k0, t1, ib1, Hts1, rfl⟩, Hq⟩ := HQ
    have Hb := ldLedgerBranch t Dr Dw D base vs ldaddr postLd km t0 v' k0 t1 L Hts Hts1
    have Herd : ∀ v, ∃ q t2, erd Dr Dw (k0 v) t1 = some (q, t2) := by
      intro v
      obtain ⟨_, _, _, _, _, He, _⟩ := ldBranchOkNode _ _ _ _ _ _ _ _ _ (Hb v)
      exact ⟨_, _, He⟩
    iapply (AxEpiLedger.wpdOfSplitFrom i Φ s2 _ (erdExit Dr Dw cpu k0 t1 kk) (.inr (.inl Hq))
      (AxEpiLedger.seipN0Ok cpu k0 t1 ib1 kk Dr Dw HDr HDrm Herd))
    isplit
    · iintro %s3 %HQ3
      obtain ⟨q3, ⟨v, qm, t2, ib2, He, rfl, -⟩, Hs3⟩ := HQ3
      obtain ⟨n, va, req, KKf, t2', He', Hf⟩ := ldBranchOkNode _ _ _ _ _ _ _ _ _ (Hb v)
      rw [He, Option.some.injEq, Prod.mk.injEq] at He'
      obtain ⟨rfl, rfl⟩ := He'
      obtain ⟨Hdev, Hfe, Hpa, Hlen, nl, val, reql, KK, tl, He2, Hl⟩ :=
        ldFetchOkNode _ _ _ _ _ _ _ _ _ _ _ _ Hf
      obtain ⟨Hdevl, Hlatl, Hnfl, Hpal, Hn, Hx⟩ := ldLoadOkNode _ _ _ _ _ _ _ _ Hl
      subst Hpa
      obtain ⟨p3, k3⟩ := s3
      obtain ⟨hk, hp⟩ := Hs3
      simp only at hk hp
      subst k3
      match p3, hp with
      | .PHart c3 m3 rs3 fn3 ib3', hp =>
        obtain ⟨hc, hm, hf, hi, hag⟩ := hp
        subst c3 m3 fn3 ib3'
        obtain ⟨ibLd, -, -, HrunPre⟩ := erdGstep Dr Dw _ HDr HDrm t2 ib2 _ _ He2 cpu kk
        have Hpost : ∀ x : BitVec (8 * nl), ∃ sEnd : ExecSt,
            epure D (KK (.Ok (x, none))) tl = some ((), sEnd) := by
          intro x
          obtain ⟨sEnd, Hep, -⟩ := Hx x
          exact ⟨sEnd, Hep⟩
        iapply (wpdFetchThenLoad Φ i cpu n va req KKf ib2 kk vs t2.regs rs3 nl val reql KK ibLd
          tl D Rv Hdev Hfe Hlen Hgd (regsAgreeSym _ _ _ hag) HrunPre Hdevl Hlatl Hn Hnfl
          Hrow HD HDm Hpost) $$ F
        isplit
        · isplit
          · icases R with ⟨R, -⟩
            iintro %x %sEnd %ib3 %s' %Hep %Hs'
            have Ht : ldTail D none
                (KK (.Ok (wordOfBytes nl (WeakInterpProj.wbytes nl x), none))) tl = some sEnd := by
              rw [wordOfBytesWbytes]
              simp only [ldTail, Hep]
            iapply R $$ %s' %⟨v', v, none, WeakInterpProj.wbytes nl x, sEnd, rfl,
              ldFinalChain t Dr Dw D vs v' v none _ km t0 k0 t1 n va req KKf t2 nl val reql KK
                tl sEnd Hts Hts1 He He2 Ht, ib3, Hs'⟩
          · icases R with ⟨-, R⟩
            iintro %x %sEnd %ib3 %GD %s1 %Hep %Hs1 %Hlen1
            iapply R $$ %GD %s1
              %⟨km, t0, ib0, Hts, .inr ⟨v', k0, t1, ib1, Hts1,
                .inr ⟨v, n, va, req, KKf, t2, nl, val, reql, KK, tl, ibLd, He, He2,
                  .inr ⟨x, sEnd, ib3, Hep, Hs1⟩⟩⟩⟩ %Hlen1
        · icases R with ⟨-, R⟩
          iintro %GD %s1 %Hs1 %Hlen1
          iapply R $$ %GD %s1
            %⟨km, t0, ib0, Hts, .inr ⟨v', k0, t1, ib1, Hts1,
              .inr ⟨v, n, va, req, KKf, t2, nl, val, reql, KK, tl, ibLd, He, He2, .inl Hs1⟩⟩⟩
            %Hlen1
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %Hs1 %Hlen1
      iapply R $$ %GD %s1 %⟨km, t0, ib0, Hts, .inr ⟨v', k0, t1, ib1, Hts1, .inl Hs1⟩⟩ %Hlen1
  · icases R with ⟨-, R⟩
    iintro %GD %s1 %Hs1 %Hlen1
    iapply R $$ %GD %s1 %⟨km, t0, ib0, Hts, .inl Hs1⟩ %Hlen1

theorem wpdTickTailExact (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (m : SailM Unit)
    (tl : ExecSt) (ib : Ibch) (k : Nat) (D : List Register) (post : RegFile → Prop)
    (HD : Register.sig_seip ∉ D) (HDm : Register.sig_meip ∉ D) (Hok : tickPostOk D post m tl)
    (rs : RegFile) (Hag : regsAgree AxRunClose.pinReg tl.regs rs) :
    ⊢ ((∀ s', ⌜TailX D cpu m tl k s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1, ⌜tickTailInv D cpu m tl k s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu m rs none ib, k⟩ Φ := by
  obtain ⟨km1, t4, Hts⟩ := tickPostOkShape D post m tl Hok
  have Hnext := AxEpiLedgerTick.tickPostOkNext D post m tl km1 t4 Hts Hok
  obtain ⟨ib4, Hr⟩ := AxEpiLedger.toPinGstep m tl ib _ _ Hts cpu k
  iintro R
  iapply (wpdOfSeipSplitRtc i Φ _ _ _ (AxEpiLedger.seipExit cpu km1 t4 k)
    (aeqvOfAgree cpu m rs tl.regs none ib k Hag) Hr (AxEpiLedger.meipN0Ok cpu km1 t4 ib4 k Hnext))
  isplit
  · iintro %s2 %HQ
    obtain ⟨q, ⟨v', k1, t5, ib5, Hts1, rfl⟩, Hq⟩ := HQ
    have Hk1 := tickPostOkAt D post m tl km1 t4 v' k1 t5 Hts Hts1 Hok
    have Hn0 : n0Ok (seipNode cpu k1 t5.regs ib5 k) (tickExit D cpu k1 t5 k) := by
      refine n0OkSeipRead cpu k1 t5.regs ib5 k _ (fun v => ?_)
      obtain ⟨t6, Hep, -⟩ := Hk1 v
      obtain ⟨ib6, Hr6⟩ := epureGstepRtc D HD HDm _ _ _ _ Hep cpu (ibRd ib5 Register.sig_seip) k
      exact ⟨_, ⟨v, t6, ib6, Hep, rfl⟩, Hr6⟩
    iapply (AxEpiLedger.wpdOfSplitFrom i Φ s2 _ _ (.inr (.inl Hq)) Hn0)
    isplit
    · icases R with ⟨R, -⟩
      iintro %s3 %HQ3
      obtain ⟨q3, ⟨v, t6, ib6, Hep, rfl⟩, Hq3⟩ := HQ3
      have Ht : ldTail D (some (v', v)) m tl = some t6 := by
        simp only [ldTail, Hts, AxEpiLedger.ansMeipNode, Hts1, ansSeipNode, Hep]
      iapply R $$ %s3 %⟨v', v, t6, Ht, ib6, Hq3⟩
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %Hs1 %Hl
      iapply R $$ %GD %s1 %⟨km1, t4, ib4, Hts, .inr ⟨v', k1, t5, ib5, Hts1, Hs1⟩⟩ %Hl
  · icases R with ⟨-, R⟩
    iintro %GD %s1 %Hs1 %Hl
    iapply R $$ %GD %s1 %⟨km1, t4, ib4, Hts, .inl Hs1⟩ %Hl

theorem wpdLoadThenTickExact (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (nl va : Nat)
    (req : Mem_read_request nl va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * nl) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (sLd : ExecSt) (D : List Register) (postLd : Int → RegFile → Prop)
    (Rv : Gdexec → List (BitVec 8) → IProp GF)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hn : 0 < nl) (Hnf : (classify req.access_kind).akIfetch = false)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i k⌝)
    (HD : Register.sig_seip ∉ D) (HDm : Register.sig_meip ∉ D)
    (Hx : ∀ x : BitVec (8 * nl), tickPostOk D (postLd (x.toNat : Int)) (KK (.Ok (x, none))) sLd) :
    ⊢ ∀ s2, ⌜Qat ⟨.PHart cpu (.impure (.ok (.memRead nl va req)) KK) sLd.regs none ib, k⟩ s2⌝ -∗
      (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
         ⌜graphValue GD (i, k) = some v⌝ -∗ loadFlow GD i k (Rv GD v)) -∗
      ((∀ s', ⌜∃ w, TailX D cpu (KK (.Ok (wordOfBytes nl w, none))) sLd (k + 1) s'⌝ -∗
          wpd .MaybeStuck i s' Φ) ∧
       (∀ (x : BitVec (8 * nl)) (GD : Gdexec) (s1 : Athread),
          ⌜tickTailInv D cpu (KK (.Ok (x, none))) sLd (k + 1) s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i s2 Φ := by
  iintro %s2 %Hq F R
  obtain ⟨p2, k2⟩ := s2
  obtain ⟨hk, hp⟩ := Hq
  simp only at hk hp
  subst k2
  match p2, hp with
  | .PHart c2 m2 rs2 fn2 ib2, hp =>
    obtain ⟨hc, hm, hf, hi, hag⟩ := hp
    subst c2 m2 fn2 ib2
    iapply (wpdLoadStep Φ i cpu nl va req KK ib k sLd.regs Rv Hdev Hlat Hn Hnf Hrow) $$
      %rs2 %(regsAgreeSym _ _ _ hag) F
    iintro %v %rs' %Hlv %hag'
    iapply (wpdTickTailExact i Φ cpu _ sLd ib (k + 1) D _ HD HDm (Hx (wordOfBytes nl v)) rs' hag')
    isplit
    · icases R with ⟨R, -⟩
      iintro %s' %Hs'
      iapply R $$ %s' %⟨v, Hs'⟩
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %Hs1 %Hl
      iapply R $$ %(wordOfBytes nl v) %GD %s1 %Hs1 %Hl

theorem wpdFetchThenLoadTickExact (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KKf : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (vs : List (BitVec 8)) (rs0 rs : RegFile) (nl val : Nat)
    (reql : Mem_read_request nl val Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * nl) × Option Bool) Arch.abort → SailM Unit) (ibLd : Ibch)
    (tl : ExecSt) (D : List Register) (postLd : Int → RegFile → Prop)
    (Rv : Gdexec → List (BitVec 8) → IProp GF)
    (Hdev : devAddr req.pa = false) (Hfe : (classify req.access_kind).akIfetch = true)
    (Hlen : vs.length = n)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i k (paZ req.pa) vs⌝)
    (Hag : regsAgree AxRunClose.pinReg rs0 rs)
    (HrunPre : rtc gstep
      ⟨.PHart cpu (KKf (.Ok (wordOfBytes n vs, none))) rs0 none ib, k⟩
      ⟨.PHart cpu (.impure (.ok (.memRead nl val reql)) KK) tl.regs none ibLd, k⟩)
    (Hdevl : devAddr reql.pa = false) (Hlatl : (classify reql.access_kind).akLatest = false)
    (Hn : 0 < nl) (Hnfl : (classify reql.access_kind).akIfetch = false)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i k⌝)
    (HD : Register.sig_seip ∉ D) (HDm : Register.sig_meip ∉ D)
    (Hx : ∀ x : BitVec (8 * nl), tickPostOk D (postLd (x.toNat : Int)) (KK (.Ok (x, none))) tl) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
         ⌜graphValue GD (i, k) = some v⌝ -∗ loadFlow GD i k (Rv GD v)) -∗
      (((∀ s', ⌜∃ w, TailX D cpu (KK (.Ok (wordOfBytes nl w, none))) tl (k + 1) s'⌝ -∗
           wpd .MaybeStuck i s' Φ) ∧
        (∀ (x : BitVec (8 * nl)) (GD : Gdexec) (s1 : Athread),
           ⌜tickTailInv D cpu (KK (.Ok (x, none))) tl (k + 1) s1⌝ -∗
           ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) ∧
       (∀ (GD : Gdexec) (s1 : Athread),
          ⌜Pbefore ⟨.PHart cpu (.impure (.ok (.memRead nl val reql)) KK) tl.regs none ibLd, k⟩
            s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KKf) rs none ib, k⟩ Φ := by
  iintro F R
  iapply (wpdFetchStep Φ i cpu n va req KKf ib k vs rs0 Hdev Hfe Hlen Hgd) $$ %rs %Hag
  iintro %rs' %hag
  iapply (wpdRunTo Φ i _ _ HrunPre) $$
    %⟨.PHart cpu (KKf (.Ok (wordOfBytes n vs, none))) rs' none ib, k⟩
    %⟨rfl, rfl, rfl, rfl, rfl, regsAgreeSym _ _ _ hag⟩
  isplit
  · icases R with ⟨R, -⟩
    iintro %s3 %Hq3
    iapply (wpdLoadThenTickExact Φ i cpu nl val reql KK ibLd k tl D postLd Rv Hdevl Hlatl Hn
      Hnfl Hrow HD HDm Hx) $$ %s3 %Hq3 F R
  · icases R with ⟨-, R⟩
    iexact R

theorem wpdCldspStepOfLedgerTickExact (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
    (ib : Ibch) (kk : Nat) (t : ExecSt) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (postLd : Int → RegFile → Prop)
    (Rv : Gdexec → List (BitVec 8) → IProp GF)
    (L : AxLdTickFacts t Dr Dw D base vs ldaddr postLd)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk base vs⌝)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i kk⌝)
    (rs : RegFile) (Hag0 : regsAgree AxRunClose.pinReg t.regs rs) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i kk ls -∗
         ⌜graphValue GD (i, kk) = some v⌝ -∗ loadFlow GD i kk (Rv GD v)) -∗
      ((∀ s', ⌜LdRetX t Dr Dw D vs true cpu (kk + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1, ⌜ledgerLdtInv t Dr Dw D vs cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep true) rs none ib, kk⟩ Φ := by
  have HDr := of_decide_eq_false L.ltSeipDr
  have HDrm := of_decide_eq_false L.ltMeipDr
  have HD := of_decide_eq_false L.ltSeipD
  have HDm := of_decide_eq_false L.ltMeipD
  obtain ⟨km, t0, Hts⟩ := AxEpiLedgerTick.seipAtTickSpec t L.ltToSeip
  have Hnext := AxEpiLedgerTick.seipAtTickNext t km t0 L.ltToSeip Hts
  obtain ⟨ib0, Hr0⟩ := AxEpiLedger.toPinGstep _ t ib _ _ Hts cpu kk
  iintro F R
  iapply (wpdOfSeipSplitRtc i Φ _ _ _ (AxEpiLedger.seipExit cpu km t0 kk)
    (aeqvOfAgree cpu (riscvStep true) rs t.regs none ib kk Hag0) Hr0
    (AxEpiLedger.meipN0Ok cpu km t0 ib0 kk Hnext))
  isplit
  · iintro %s2 %HQ
    obtain ⟨q, ⟨v', k0, t1, ib1, Hts1, rfl⟩, Hq⟩ := HQ
    have Hb := ldtLedgerBranch t Dr Dw D base vs ldaddr postLd km t0 v' k0 t1 L Hts Hts1
    iapply (AxEpiLedger.wpdOfSplitFrom i Φ s2 _ (erdExit Dr Dw cpu k0 t1 kk) (.inr (.inl Hq))
      (AxEpiLedger.seipN0Ok cpu k0 t1 ib1 kk Dr Dw HDr HDrm
        (fun v => AxEpiLedgerTick.erdOfLdtBranch Dr Dw D base vs ldaddr postLd _ t1 (Hb v))))
    isplit
    · iintro %s3 %HQ3
      obtain ⟨q3, ⟨v, qm, t2, ib2, He, rfl, -⟩, Hs3⟩ := HQ3
      obtain ⟨n, va, req, KKf, t2', He', Hf⟩ := ldtBranchOkNode _ _ _ _ _ _ _ _ _ (Hb v)
      rw [He, Option.some.injEq, Prod.mk.injEq] at He'
      obtain ⟨rfl, rfl⟩ := He'
      obtain ⟨Hdev, Hfe, Hpa, Hlen, nl, val, reql, KK, tl, He2, Hl⟩ :=
        ldtFetchOkNode _ _ _ _ _ _ _ _ _ _ _ _ Hf
      obtain ⟨Hdevl, Hlatl, Hnfl, Hpal, Hn, Hx⟩ := ldtLoadOkNode _ _ _ _ _ _ _ _ Hl
      subst Hpa
      obtain ⟨p3, k3⟩ := s3
      obtain ⟨hk, hp⟩ := Hs3
      simp only at hk hp
      subst k3
      match p3, hp with
      | .PHart c3 m3 rs3 fn3 ib3', hp =>
        obtain ⟨hc, hm, hf, hi, hag⟩ := hp
        subst c3 m3 fn3 ib3'
        obtain ⟨ibLd, -, -, HrunPre⟩ := erdGstep Dr Dw _ HDr HDrm t2 ib2 _ _ He2 cpu kk
        iapply (wpdFetchThenLoadTickExact Φ i cpu n va req KKf ib2 kk vs t2.regs rs3 nl val reql
          KK ibLd tl D postLd Rv Hdev Hfe Hlen Hgd (regsAgreeSym _ _ _ hag) HrunPre Hdevl Hlatl
          Hn Hnfl Hrow HD HDm Hx) $$ F
        isplit
        · isplit
          · icases R with ⟨R, -⟩
            iintro %s' %Hs'
            obtain ⟨w, u2', u2, t5, Ht, Hr⟩ := Hs'
            iapply R $$ %s' %⟨v', v, some (u2', u2), w, t5, rfl,
              ldFinalChain t Dr Dw D vs v' v (some (u2', u2)) w km t0 k0 t1 n va req KKf t2 nl
                val reql KK tl t5 Hts Hts1 He He2 Ht, Hr⟩
          · icases R with ⟨-, R⟩
            iintro %x %GD %s1 %Hs1 %Hlen1
            iapply R $$ %GD %s1
              %⟨km, t0, ib0, Hts, .inr ⟨v', k0, t1, ib1, Hts1,
                .inr ⟨v, n, va, req, KKf, t2, nl, val, reql, KK, tl, ibLd, He, He2,
                  .inr ⟨x, Hs1⟩⟩⟩⟩ %Hlen1
        · icases R with ⟨-, R⟩
          iintro %GD %s1 %Hs1 %Hlen1
          iapply R $$ %GD %s1
            %⟨km, t0, ib0, Hts, .inr ⟨v', k0, t1, ib1, Hts1,
              .inr ⟨v, n, va, req, KKf, t2, nl, val, reql, KK, tl, ibLd, He, He2, .inl Hs1⟩⟩⟩
            %Hlen1
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %Hs1 %Hlen1
      iapply R $$ %GD %s1 %⟨km, t0, ib0, Hts, .inr ⟨v', k0, t1, ib1, Hts1, .inl Hs1⟩⟩ %Hlen1
  · icases R with ⟨-, R⟩
    iintro %GD %s1 %Hs1 %Hlen1
    iapply R $$ %GD %s1 %⟨km, t0, ib0, Hts, .inl Hs1⟩ %Hlen1

/-- (1) THE c.ldsp AFTER THE c.sdsp, BOTH TICKS, EXACT EXIT: the continuation is owed only at the
`.pure ()` node whose register file IS `ldOut c w` for a case `c` (with the store's answers
`v' v` and the tick bit `tick`) and the read bytes `w`. -/
theorem wpdCldspAfterSdExact (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch)
    (kk : Nat) (v' v : BitVec 1) (Rv : Gdexec → List (BitVec 8) → IProp GF)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢
        ⌜AxCjrWpd.fetchImgOk GD i kk (pcLd : Int) AxEpiLedger.ldVs⌝)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i kk⌝)
    (tick : Bool) (rs : RegFile) (Hag : regsAgree AxRunClose.pinReg (tAfterSd v' v).regs rs) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (w : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i kk ls -∗
         ⌜graphValue GD (i, kk) = some w⌝ -∗ loadFlow GD i kk (Rv GD w)) -∗
      ((∀ s', ⌜∃ (c : Ldc) (w : List (BitVec 8)), c.lcV' = v' ∧ c.lcV = v ∧
            tickOf c.lcT = tick ∧ RetX cpu (ldOut c w) (kk + 1) s'⌝ -∗
          wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1, ⌜ldAfterSdInv tick v' v cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep tick) rs none ib, kk⟩ Φ := by
  have Hc : ∀ s', LdRetX (tAfterSd v' v) AxEpiProbe.drNopin DwAll DPost AxEpiLedger.ldVs tick cpu
      (kk + 1) s' → ∃ (c : Ldc) (w : List (BitVec 8)), c.lcV' = v' ∧ c.lcV = v ∧
        tickOf c.lcT = tick ∧ RetX cpu (ldOut c w) (kk + 1) s' := by
    rintro s' ⟨u', u, o, w, t3, Htk, Hf, Hr⟩
    refine ⟨⟨v', v, u', u, o⟩, w, rfl, rfl, Htk, ?_⟩
    unfold ldOut
    dsimp only
    rw [Hf]
    exact Hr
  cases tick
  · simp only [ldAfterSdInv, Bool.false_eq_true, ↓reduceIte]
    iintro F R
    iapply (wpdCldspStepOfLedgerAgreeExact i Φ cpu ib kk (tAfterSd v' v) _ _ _ _ _ _ _ Rv
      (epiLedgerCldspAfterSd v' v) Hgd Hrow rs Hag) $$ F
    isplit
    · icases R with ⟨R, -⟩
      iintro %s' %Hs'
      iapply R $$ %s' %(Hc s' Hs')
    · icases R with ⟨-, R⟩
      iexact R
  · simp only [ldAfterSdInv, ↓reduceIte]
    iintro F R
    iapply (wpdCldspStepOfLedgerTickExact i Φ cpu ib kk (tAfterSd v' v) _ _ _ _ _ _ _ Rv
      (epiLedgerCldspTick v' v) Hgd Hrow rs Hag) $$ F
    isplit
    · icases R with ⟨R, -⟩
      iintro %s' %Hs'
      iapply R $$ %s' %(Hc s' Hs')
    · icases R with ⟨-, R⟩
      iexact R

end ldExact

/-! # 4. The collapse: the exit does not depend on the pin answers (deviation 4) -/

/-- (Lean-only) The canonical case: every pin answer `0`, the tick bit kept. -/
def AxEpiLdJr.canon (c : Ldc) : Ldc := ⟨0#1, 0#1, 0#1, 0#1, c.lcT.map fun _ => (0#1, 0#1)⟩

theorem AxEpiLdJr.tAfterSdEq (v' v : BitVec 1) : tAfterSd v' v = tAfterSd 0#1 0#1 := by
  rcases bv1Cases v' with rfl | rfl <;> rcases bv1Cases v with rfl | rfl <;> ax_epi_ledger_krfl

theorem AxEpiLdJr.ldFinalEq (u' u : BitVec 1) (o : Option (BitVec 1 × BitVec 1))
    (w : List (BitVec 8)) :
    ldFinal (tAfterSd 0#1 0#1) AxEpiProbe.drNopin DwAll DPost AxEpiLedger.ldVs u' u o w =
      ldFinal (tAfterSd 0#1 0#1) AxEpiProbe.drNopin DwAll DPost AxEpiLedger.ldVs 0#1 0#1
        (o.map fun _ => (0#1, 0#1)) w := by
  rcases o with _ | ⟨a, b⟩
  · rcases bv1Cases u' with rfl | rfl <;> rcases bv1Cases u with rfl | rfl <;> ax_epi_ledger_krfl
  · rcases bv1Cases u' with rfl | rfl <;> rcases bv1Cases u with rfl | rfl <;>
      rcases bv1Cases a with rfl | rfl <;> rcases bv1Cases b with rfl | rfl <;> ax_epi_ledger_krfl

theorem AxEpiLdJr.ldOutCanon (c : Ldc) (w : List (BitVec 8)) :
    ldOut c w = ldOut (AxEpiLdJr.canon c) w := by
  unfold ldOut
  rw [AxEpiLdJr.tAfterSdEq c.lcV' c.lcV, AxEpiLdJr.ldFinalEq]
  rfl

/-! # 5. x1 after the load, per case -/

/-- x1 of the exact exit is the model's sign-extended loaded word. -/
theorem ldOutX1 (c : Ldc) (w : List (BitVec 8)) : (ldOut c w) .x1 = ldVal (wordOfBytes 8 w) := by
  rw [AxEpiLdJr.ldOutCanon]
  obtain ⟨v', v, u', u, o⟩ := c
  cases o <;> ax_epi_ledger_krfl

theorem ldOutX1Unsigned (c : Ldc) (w : List (BitVec 8)) :
    ((ldOut c w) .x1).toNat = (wordOfBytes 8 w).toNat := by
  rw [ldOutX1]
  exact ldValId _

/-! # 6. Register observations -/

/-- (Lean-only) The registers of `L` with their values. -/
def AxEpiLdJr.obsL (L : List Register) (rs : RegFile) : List (Σ r : Register, RegisterType r) :=
  L.map fun r => ⟨r, rs r⟩

theorem AxEpiLdJr.agreeOfObsL (L : List Register) (rs rs' : RegFile)
    (h : AxEpiLdJr.obsL L rs = AxEpiLdJr.obsL L rs') : agreeOn L rs rs' := by
  induction L with
  | nil => intro r hr; exact absurd hr List.not_mem_nil
  | cons a L ih =>
    simp only [AxEpiLdJr.obsL, List.map_cons, List.cons.injEq, Sigma.mk.injEq, true_and] at h
    obtain ⟨h0, h1⟩ := h
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact eq_of_heq h0
    · exact ih h1 r hr

/-! # 7. The c.jr at the load's exact exit, both ticks -/

/-- (Lean-only) `AJrFix` without `x1`. -/
def AxEpiLdJr.LFix : List Register :=
  [.mseccfg, .elp, .htif_tohost_base, .pmpaddr_n, .pmpcfg_n, .pma_regions, .PC, .mstatus, .mie,
   .mideleg, .misa, .hart_state, .minstretcfg, .mcountinhibit, .cur_privilege]

theorem AxEpiLdJr.fixSub : ∀ r ∈ AJrFix, r ≠ .x1 → r ∈ AxEpiLdJr.LFix := by decide +kernel

theorem AxEpiLdJr.obsFixEq (c : Ldc) (w : List (BitVec 8)) :
    AxEpiLdJr.obsL AxEpiLdJr.LFix (ldOut c w) = AxEpiLdJr.obsL AxEpiLdJr.LFix (probeRegs pcJr) := by
  rw [AxEpiLdJr.ldOutCanon]
  obtain ⟨v', v, u', u, o⟩ := c
  cases o <;> ax_epi_ledger_krfl

theorem ldOutAgreeJr (c : Ldc) (w : List (BitVec 8)) :
    agreeOn AJrFix (ldOut c w) ((probeRegs pcJr).set .x1 ((ldOut c w) .x1)) := by
  intro r Hr
  by_cases Hne : r = .x1
  · subst Hne
    simp only [RegFile.set_same]
  · rw [RegFile.set_other _ _ _ _ Hne]
    exact AxEpiLdJr.agreeOfObsL _ _ _ (AxEpiLdJr.obsFixEq c w) r (AxEpiLdJr.fixSub r Hr Hne)

/-- Rocq `all_eq`. -/
def allEq : List Register → RegFile → RegFile → Prop
  | [], _, _ => True
  | r :: L, rs, rs' => rs r = rs' r ∧ allEq L rs rs'

theorem agreeOnAllEq (L : List Register) (rs rs' : RegFile) : allEq L rs rs' → agreeOn L rs rs' := by
  induction L with
  | nil => intro _ r hr; exact absurd hr List.not_mem_nil
  | cons r0 L ih =>
    intro H r hr
    obtain ⟨H0, H⟩ := H
    rcases List.mem_cons.1 hr with rfl | hr
    · exact H0
    · exact ih H r hr

theorem agreeOnMono (A B : List Register) (rs rs' : RegFile) :
    A ⊆ B → agreeOn B rs rs' → agreeOn A rs rs' :=
  fun HAB H r Hr => H r (HAB Hr)

theorem agreeOnSetX1 (A : List Register) (rs rs0 : RegFile) :
    agreeOn (A.filter fun r => !decide (r = .x1)) rs rs0 →
    agreeOn A rs (rs0.set .x1 (rs .x1)) := by
  intro H r Hr
  by_cases Hne : r = .x1
  · subst Hne
    simp only [RegFile.set_same]
  · rw [RegFile.set_other _ _ _ _ Hne]
    exact H r (List.mem_filter.2 ⟨Hr, by simp [Hne]⟩)

/-- Rocq `L_jr_t`: `AJrT` without `x1` (deviation 3). -/
def LJrT : List Register :=
  [.minstret, .mseccfg, .elp, .htif_tohost_base, .pmpaddr_n, .pmpcfg_n, .pma_regions, .PC,
   .mstatus, .mie, .mip, .mideleg, .misa, .hart_state, .minstretcfg, .mcountinhibit,
   .cur_privilege, .menvcfg, .mtimecmp, .mtime, .mcycle, .mcyclecfg]

theorem AJrTSub : (AJrT.filter fun r => !decide (r = .x1)) ⊆ LJrT := by decide +kernel

theorem AxEpiLdJr.allEqOfObsL (L : List Register) (rs rs' : RegFile)
    (h : AxEpiLdJr.obsL L rs = AxEpiLdJr.obsL L rs') : allEq L rs rs' := by
  induction L with
  | nil => trivial
  | cons a L ih =>
    simp only [AxEpiLdJr.obsL, List.map_cons, List.cons.injEq, Sigma.mk.injEq, true_and] at h
    exact ⟨eq_of_heq h.1, ih h.2⟩

theorem AxEpiLdJr.obsRefEq (c : Ldc) (w : List (BitVec 8)) :
    AxEpiLdJr.obsL LJrT (ldOut c w) = AxEpiLdJr.obsL LJrT (ldOut c AxEpiLdJr.w0) := by
  rw [AxEpiLdJr.ldOutCanon c w, AxEpiLdJr.ldOutCanon c AxEpiLdJr.w0]
  obtain ⟨v', v, u', u, o⟩ := c
  cases o <;> ax_epi_ledger_krfl

/-- The tick = true reference file: the real exit at the fixed word `w0`, x1 := ra.  The real
exit agrees with it on ALL of `AJrT`. -/
theorem ldOutAgreeRef (c : Ldc) (w : List (BitVec 8)) :
    agreeOn AJrT (ldOut c w) ((ldOut c AxEpiLdJr.w0).set .x1 ((ldOut c w) .x1)) := by
  apply agreeOnSetX1
  apply agreeOnMono _ _ _ _ AJrTSub
  apply agreeOnAllEq
  exact AxEpiLdJr.allEqOfObsL _ _ _ (AxEpiLdJr.obsRefEq c w)

/-! ## Tracked-to-tracked transfer (Lean-only, deviation 4) -/

theorem AxEpiLdJr.toPinAgAg (m : SailM Unit) :
    ∀ (A : List Register) (t t' : ExecSt) (m0 : SailM Unit) (t1 : ExecSt) (A1 : List Register),
      toPinAg A m t = some (m0, t1, A1) → agreeOn A t.regs t'.regs →
      ∃ t1', toPinAg A m t' = some (m0, t1', A1) ∧ agreeOn A1 t1.regs t1'.regs := by
  induction m with
  | pure x =>
    intro A t t' m0 t1 A1 h
    simp [toPinAg] at h
  | impure call k ih =>
    intro A t t' m0 t1 A1 h hag
    cases call with
    | error e => simp [toPinAg] at h
    | ok o =>
      cases o
      case regRead r =>
        by_cases hr : r = .sig_seip ∨ r = .sig_meip
        · simp only [toPinAg, if_pos hr, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨t', by simp only [toPinAg, if_pos hr], hag⟩
        · by_cases hA : r ∈ A
          · simp only [toPinAg, if_neg hr, if_pos hA] at h
            obtain ⟨t1', h1, h2⟩ := ih _ A t t' m0 t1 A1 h hag
            refine ⟨t1', ?_, h2⟩
            simp only [toPinAg, if_neg hr, if_pos hA]
            rw [← hag r hA]
            exact h1
          · simp only [toPinAg, if_neg hr, if_neg hA, reduceCtorEq] at h
      case regWrite r v =>
        simp only [toPinAg] at h
        obtain ⟨t1', h1, h2⟩ := ih _ (r :: A) _ (t'.setReg r v) m0 t1 A1 h
          (agreeOnSetReg A t t' r v hag)
        exact ⟨t1', by simp only [toPinAg]; exact h1, h2⟩
      case instrAnnounce nw w =>
        cases hsw : sfAnnB nw w <;>
          simp only [toPinAg, hsw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
        obtain ⟨t1', h1, h2⟩ := ih _ A t t' m0 t1 A1 h hag
        exact ⟨t1', by simp only [toPinAg, hsw, Bool.false_eq_true, ↓reduceIte]; exact h1, h2⟩
      all_goals first
        | (simp [toPinAg] at h; done)
        | (simp only [toPinAg] at h
           obtain ⟨t1', h1, h2⟩ := ih _ A t t' m0 t1 A1 h hag
           exact ⟨t1', by simp only [toPinAg]; exact h1, h2⟩)

theorem AxEpiLdJr.erdAgAg (Dr Dw : List Register) (m : SailM Unit) :
    ∀ (A : List Register) (t t' : ExecSt) (mf : SailM Unit) (t2 : ExecSt) (A2 : List Register),
      erdAg Dr Dw A m t = some (mf, t2, A2) → agreeOn A t.regs t'.regs →
      ∃ t2', erdAg Dr Dw A m t' = some (mf, t2', A2) ∧ agreeOn A2 t2.regs t2'.regs := by
  induction m with
  | pure x =>
    intro A t t' mf t2 A2 h
    simp [erdAg] at h
  | impure call k ih =>
    intro A t t' mf t2 A2 h hag
    cases call with
    | error e => simp [erdAg] at h
    | ok o =>
      cases o
      case regRead r =>
        by_cases hD : r ∈ Dr
        · by_cases hA : r ∈ A
          · simp only [erdAg, if_pos hD, if_pos hA] at h
            obtain ⟨t2', h1, h2⟩ := ih _ A t t' mf t2 A2 h hag
            refine ⟨t2', ?_, h2⟩
            simp only [erdAg, if_pos hD, if_pos hA]
            rw [← hag r hA]
            exact h1
          · simp only [erdAg, if_pos hD, if_neg hA, reduceCtorEq] at h
        · simp only [erdAg, if_neg hD, reduceCtorEq] at h
      case regWrite r v =>
        by_cases hD : r ∈ Dw
        · simp only [erdAg, if_pos hD] at h
          obtain ⟨t2', h1, h2⟩ := ih _ (r :: A) _ (t'.setReg r v) mf t2 A2 h
            (agreeOnSetReg A t t' r v hag)
          exact ⟨t2', by simp only [erdAg, if_pos hD]; exact h1, h2⟩
        · simp only [erdAg, if_neg hD, reduceCtorEq] at h
      case memRead n va req =>
        by_cases hd : devAddr req.pa = true
        · simp [erdAg, hd] at h
        · simp only [erdAg, hd, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨t', by simp only [erdAg, hd, Bool.false_eq_true, ↓reduceIte], hag⟩
      case instrAnnounce nw w =>
        cases hsw : sfAnnB nw w <;>
          simp only [erdAg, hsw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
        obtain ⟨t2', h1, h2⟩ := ih _ A t t' mf t2 A2 h hag
        exact ⟨t2', by simp only [erdAg, hsw, Bool.false_eq_true, ↓reduceIte]; exact h1, h2⟩
      all_goals first
        | (simp [erdAg] at h; done)
        | (simp only [erdAg] at h
           obtain ⟨t2', h1, h2⟩ := ih _ A t t' mf t2 A2 h hag
           exact ⟨t2', by simp only [erdAg]; exact h1, h2⟩)

theorem AxEpiLdJr.epureAgAg {X : Type} (D : List Register) (m : SailM X) :
    ∀ (A : List Register) (t t' : ExecSt) (x : X) (t3 : ExecSt) (A3 : List Register),
      epureAg D A m t = some (x, t3, A3) → agreeOn A t.regs t'.regs →
      ∃ t3', epureAg D A m t' = some (x, t3', A3) ∧ agreeOn A3 t3.regs t3'.regs := by
  induction m with
  | pure y =>
    intro A t t' x t3 A3 h hag
    simp only [epureAg, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨t', rfl, hag⟩
  | impure call k ih =>
    intro A t t' x t3 A3 h hag
    cases call with
    | error e => simp [epureAg] at h
    | ok o =>
      cases o
      case regRead r =>
        by_cases hD : r ∈ D
        · by_cases hA : r ∈ A
          · simp only [epureAg, if_pos hD, if_pos hA] at h
            obtain ⟨t3', h1, h2⟩ := ih _ A t t' x t3 A3 h hag
            refine ⟨t3', ?_, h2⟩
            simp only [epureAg, if_pos hD, if_pos hA]
            rw [← hag r hA]
            exact h1
          · simp only [epureAg, if_pos hD, if_neg hA, reduceCtorEq] at h
        · simp only [epureAg, if_neg hD, reduceCtorEq] at h
      case regWrite r v =>
        by_cases hD : r ∈ D
        · simp only [epureAg, if_pos hD] at h
          obtain ⟨t3', h1, h2⟩ := ih _ (r :: A) _ (t'.setReg r v) x t3 A3 h
            (agreeOnSetReg A t t' r v hag)
          exact ⟨t3', by simp only [epureAg, if_pos hD]; exact h1, h2⟩
        · simp only [epureAg, if_neg hD, reduceCtorEq] at h
      case instrAnnounce nw w =>
        cases hsw : sfAnnB nw w <;>
          simp only [epureAg, hsw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
        obtain ⟨t3', h1, h2⟩ := ih _ A t t' x t3 A3 h hag
        exact ⟨t3', by simp only [epureAg, hsw, Bool.false_eq_true, ↓reduceIte]; exact h1, h2⟩
      all_goals first
        | (simp [epureAg] at h; done)
        | (simp only [epureAg] at h
           obtain ⟨t3', h1, h2⟩ := ih _ A t t' x t3 A3 h hag
           exact ⟨t3', by simp only [epureAg]; exact h1, h2⟩)

theorem AxEpiLdJr.fetchOkAgAg (A D : List Register) (base : Int) (vs : List (BitVec 8))
    (P : List Register) (post : RegFile → Bool) (mf : SailM Unit) (t2 t2' : ExecSt) :
    postLocal P post → fetchOkAg A D base vs P post mf t2 = true →
    agreeOn A t2.regs t2'.regs → fetchOkAg A D base vs P post mf t2' = true := by
  intro Hpl H Hag
  cases mf with
  | pure _ => exact absurd H Bool.false_ne_true
  | impure call KK =>
    cases call with
    | error _ => exact absurd H Bool.false_ne_true
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [fetchOkAg, Bool.and_eq_true] at H
        obtain ⟨h1, h5⟩ := H
        cases he : epureAg D A (KK (.Ok (wordOfBytes n vs, none))) t2 with
        | none => rw [he] at h5; exact absurd h5 Bool.false_ne_true
        | some p =>
          obtain ⟨x, t3, A3⟩ := p
          rw [he] at h5
          simp only [Bool.and_eq_true] at h5
          obtain ⟨hPb, hp⟩ := h5
          have hP : ∀ r ∈ P, r ∈ A3 := fun r hr =>
            of_decide_eq_true (List.all_eq_true.1 hPb r hr)
          obtain ⟨t3', he', hag3⟩ := AxEpiLdJr.epureAgAg D _ A t2 t2' x t3 A3 he Hag
          simp only [fetchOkAg, he', Bool.and_eq_true]
          refine ⟨h1, hPb, ?_⟩
          rw [← Hpl _ _ (fun r hr => hag3 r (hP r hr))]
          exact hp
      all_goals exact absurd H Bool.false_ne_true

theorem AxEpiLdJr.branchOkAgAg (A Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (P : List Register) (post : RegFile → Bool) (m : SailM Unit) (t1 t1' : ExecSt) :
    postLocal P post → branchOkAg A Dr Dw D base vs P post m t1 = true →
    agreeOn A t1.regs t1'.regs → branchOkAg A Dr Dw D base vs P post m t1' = true := by
  intro Hpl H Hag
  unfold branchOkAg at H ⊢
  cases he : erdAg Dr Dw A m t1 with
  | none => rw [he] at H; exact absurd H Bool.false_ne_true
  | some p =>
    obtain ⟨mf, t2, A2⟩ := p
    rw [he] at H
    obtain ⟨t2', he', hag2⟩ := AxEpiLdJr.erdAgAg Dr Dw m A t1 t1' mf t2 A2 he Hag
    rw [he']
    exact AxEpiLdJr.fetchOkAgAg A2 D base vs P post mf t2 t2' Hpl H hag2

theorem AxEpiLdJr.seipAfterAgAg (A : List Register) (m0 : SailM Unit) (t0 t0' : ExecSt)
    (v' : BitVec 1) :
    AxEpiCjrFrame.seipAfterAg A m0 t0 v' = true → agreeOn A t0.regs t0'.regs →
    AxEpiCjrFrame.seipAfterAg A m0 t0' v' = true := by
  intro H Hag
  unfold AxEpiCjrFrame.seipAfterAg at H ⊢
  cases he : toPinAg A (AxEpiLedger.ansMeip m0 v') t0 with
  | none => rw [he] at H; exact absurd H Bool.false_ne_true
  | some p =>
    obtain ⟨m1, t1, A1⟩ := p
    rw [he] at H
    obtain ⟨t1', he', -⟩ := AxEpiLdJr.toPinAgAg _ A t0 t0' m1 t1 A1 he Hag
    rw [he']
    exact H

theorem AxEpiLdJr.seipAtAgAg (A : List Register) (tick : Bool) (t t' : ExecSt) :
    seipAtAg A tick t = true → agreeOn A t.regs t'.regs → seipAtAg A tick t' = true := by
  intro H Hag
  unfold seipAtAg at H ⊢
  cases hts : toPinAg A (riscvStep tick) t with
  | none => rw [hts] at H; exact absurd H Bool.false_ne_true
  | some p =>
    obtain ⟨m0, t0, A0⟩ := p
    rw [hts] at H
    simp only [Bool.and_eq_true] at H
    obtain ⟨⟨hm, h0⟩, h1⟩ := H
    obtain ⟨t0', hts', hag0⟩ := AxEpiLdJr.toPinAgAg _ A t t' m0 t0 A0 hts Hag
    rw [hts']
    simp only [Bool.and_eq_true]
    exact ⟨⟨hm, AxEpiLdJr.seipAfterAgAg A0 m0 t0 t0' 0#1 h0 hag0⟩,
      AxEpiLdJr.seipAfterAgAg A0 m0 t0 t0' 1#1 h1 hag0⟩

theorem AxEpiLdJr.branchAtAgGAg (tick : Bool) (A Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (P : List Register) (post : RegFile → Bool) (t t' : ExecSt)
    (v' v : BitVec 1) :
    postLocal P post → branchAtAgG tick A Dr Dw D base vs P post t v' v = true →
    agreeOn A t.regs t'.regs → branchAtAgG tick A Dr Dw D base vs P post t' v' v = true := by
  intro Hpl H Hag
  unfold branchAtAgG at H ⊢
  cases h1 : toPinAg A (riscvStep tick) t with
  | none => rw [h1] at H; exact absurd H Bool.false_ne_true
  | some p =>
    obtain ⟨m0, t0, A0⟩ := p
    rw [h1] at H
    obtain ⟨t0', h1', hag0⟩ := AxEpiLdJr.toPinAgAg _ A t t' m0 t0 A0 h1 Hag
    rw [h1']
    simp only [] at H ⊢
    cases h2 : toPinAg A0 (AxEpiLedger.ansMeip m0 v') t0 with
    | none => rw [h2] at H; exact absurd H Bool.false_ne_true
    | some q =>
      obtain ⟨m1, t1, A1⟩ := q
      rw [h2] at H
      obtain ⟨t1', h2', hag1⟩ := AxEpiLdJr.toPinAgAg _ A0 t0 t0' m1 t1 A1 h2 hag0
      rw [h2']
      exact AxEpiLdJr.branchOkAgAg A1 Dr Dw D base vs P post _ t1 t1' Hpl H hag1

theorem AxEpiLdJr.tickRetOkAgAg (A D P : List Register) (post : RegFile → Bool) (m : SailM Unit)
    (t t' : ExecSt) :
    postLocal P post → tickRetOkAg A D P post m t = true → agreeOn A t.regs t'.regs →
    tickRetOkAg A D P post m t' = true := by
  intro Hpl H Hag
  unfold tickRetOkAg at H ⊢
  cases he : epureAg D A m t with
  | none => rw [he] at H; exact absurd H Bool.false_ne_true
  | some p =>
    obtain ⟨x, s, A5⟩ := p
    rw [he] at H
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at H
    obtain ⟨hP, hp⟩ := H
    obtain ⟨s', he', hag5⟩ := AxEpiLdJr.epureAgAg D m A t t' x s A5 he Hag
    rw [he']
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    refine ⟨hP, ?_⟩
    rw [← Hpl _ _ (fun r hr => hag5 r (hP r hr))]
    exact hp

theorem AxEpiLdJr.tickAfterMeipAgAg (A D P : List Register) (post : RegFile → Bool)
    (m1 : SailM Unit) (t4 t4' : ExecSt) (v' : BitVec 1) :
    postLocal P post → AxEpiCjrFrame.tickAfterMeipAg A D P post m1 t4 v' = true →
    agreeOn A t4.regs t4'.regs → AxEpiCjrFrame.tickAfterMeipAg A D P post m1 t4' v' = true := by
  intro Hpl H Hag
  unfold AxEpiCjrFrame.tickAfterMeipAg at H ⊢
  cases he : toPinAg A (AxEpiLedger.ansMeip m1 v') t4 with
  | none => rw [he] at H; exact absurd H Bool.false_ne_true
  | some p =>
    obtain ⟨m2, t5, A5⟩ := p
    rw [he] at H
    simp only [Bool.and_eq_true] at H
    obtain ⟨⟨hs, r0⟩, r1⟩ := H
    obtain ⟨t5', he', hag5⟩ := AxEpiLdJr.toPinAgAg _ A t4 t4' m2 t5 A5 he Hag
    rw [he']
    simp only [Bool.and_eq_true]
    exact ⟨⟨hs, AxEpiLdJr.tickRetOkAgAg A5 D P post _ t5 t5' Hpl r0 hag5⟩,
      AxEpiLdJr.tickRetOkAgAg A5 D P post _ t5 t5' Hpl r1 hag5⟩

theorem AxEpiLdJr.tickPostOkAgAg (A D P : List Register) (post : RegFile → Bool) (m : SailM Unit)
    (t t' : ExecSt) :
    postLocal P post → tickPostOkAg A D P post m t = true → agreeOn A t.regs t'.regs →
    tickPostOkAg A D P post m t' = true := by
  intro Hpl H Hag
  unfold tickPostOkAg at H ⊢
  cases hts : toPinAg A m t with
  | none => rw [hts] at H; exact absurd H Bool.false_ne_true
  | some p =>
    obtain ⟨m1, t4, A4⟩ := p
    rw [hts] at H
    simp only [Bool.and_eq_true] at H
    obtain ⟨⟨hm, h0⟩, h1⟩ := H
    obtain ⟨t4', hts', hag4⟩ := AxEpiLdJr.toPinAgAg _ A t t' m1 t4 A4 hts Hag
    rw [hts']
    simp only [Bool.and_eq_true]
    exact ⟨⟨hm, AxEpiLdJr.tickAfterMeipAgAg A4 D P post m1 t4 t4' 0#1 Hpl h0 hag4⟩,
      AxEpiLdJr.tickAfterMeipAgAg A4 D P post m1 t4 t4' 1#1 Hpl h1 hag4⟩

theorem AxEpiLdJr.fetchOkTickAgAg (A D : List Register) (base : Int) (vs : List (BitVec 8))
    (P : List Register) (post : RegFile → Bool) (mf : SailM Unit) (t2 t2' : ExecSt) :
    postLocal P post → fetchOkTickAg A D base vs P post mf t2 = true →
    agreeOn A t2.regs t2'.regs → fetchOkTickAg A D base vs P post mf t2' = true := by
  intro Hpl H Hag
  cases mf with
  | pure _ => exact absurd H Bool.false_ne_true
  | impure call KK =>
    cases call with
    | error _ => exact absurd H Bool.false_ne_true
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [fetchOkTickAg, Bool.and_eq_true] at H ⊢
        obtain ⟨h1, h5⟩ := H
        exact ⟨h1, AxEpiLdJr.tickPostOkAgAg A D P post _ t2 t2' Hpl h5 Hag⟩
      all_goals exact absurd H Bool.false_ne_true

theorem AxEpiLdJr.branchOkTickAgAg (A Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (P : List Register) (post : RegFile → Bool) (m : SailM Unit)
    (t1 t1' : ExecSt) :
    postLocal P post → branchOkTickAg A Dr Dw D base vs P post m t1 = true →
    agreeOn A t1.regs t1'.regs → branchOkTickAg A Dr Dw D base vs P post m t1' = true := by
  intro Hpl H Hag
  unfold branchOkTickAg at H ⊢
  cases he : erdAg Dr Dw A m t1 with
  | none => rw [he] at H; exact absurd H Bool.false_ne_true
  | some p =>
    obtain ⟨mf, t2, A2⟩ := p
    rw [he] at H
    obtain ⟨t2', he', hag2⟩ := AxEpiLdJr.erdAgAg Dr Dw m A t1 t1' mf t2 A2 he Hag
    rw [he']
    exact AxEpiLdJr.fetchOkTickAgAg A2 D base vs P post mf t2 t2' Hpl H hag2

theorem AxEpiLdJr.branchAtTickAgAg (A Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (P : List Register) (post : RegFile → Bool) (t t' : ExecSt)
    (v' v : BitVec 1) :
    postLocal P post → branchAtTickAg A Dr Dw D base vs P post t v' v = true →
    agreeOn A t.regs t'.regs → branchAtTickAg A Dr Dw D base vs P post t' v' v = true := by
  intro Hpl H Hag
  unfold branchAtTickAg at H ⊢
  cases h1 : toPinAg A (riscvStep true) t with
  | none => rw [h1] at H; exact absurd H Bool.false_ne_true
  | some p =>
    obtain ⟨m0, t0, A0⟩ := p
    rw [h1] at H
    obtain ⟨t0', h1', hag0⟩ := AxEpiLdJr.toPinAgAg _ A t t' m0 t0 A0 h1 Hag
    rw [h1']
    simp only [] at H ⊢
    cases h2 : toPinAg A0 (AxEpiLedger.ansMeip m0 v') t0 with
    | none => rw [h2] at H; exact absurd H Bool.false_ne_true
    | some q =>
      obtain ⟨m1, t1, A1⟩ := q
      rw [h2] at H
      obtain ⟨t1', h2', hag1⟩ := AxEpiLdJr.toPinAgAg _ A0 t0 t0' m1 t1 A1 h2 hag0
      rw [h2']
      exact AxEpiLdJr.branchOkTickAgAg A1 Dr Dw D base vs P post _ t1 t1' Hpl H hag1

theorem AxEpiLdJr.tickFrameFactsAg (t : ExecSt) (A Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (P : List Register) (post : RegFile → Bool) (t' : ExecSt)
    (F : CjrTickFrameFacts t A Dr Dw D base vs P post) (Hpl : postLocal P post)
    (Hag : agreeOn A t.regs t'.regs) : CjrTickFrameFacts t' A Dr Dw D base vs P post where
  cftSeipDr := F.cftSeipDr
  cftMeipDr := F.cftMeipDr
  cftSeipD := F.cftSeipD
  cftMeipD := F.cftMeipD
  cftToSeip := AxEpiLdJr.seipAtAgAg A true t t' F.cftToSeip Hag
  cftBranch00 := AxEpiLdJr.branchAtTickAgAg A Dr Dw D base vs P post t t' _ _ Hpl F.cftBranch00 Hag
  cftBranch01 := AxEpiLdJr.branchAtTickAgAg A Dr Dw D base vs P post t t' _ _ Hpl F.cftBranch01 Hag
  cftBranch10 := AxEpiLdJr.branchAtTickAgAg A Dr Dw D base vs P post t t' _ _ Hpl F.cftBranch10 Hag
  cftBranch11 := AxEpiLdJr.branchAtTickAgAg A Dr Dw D base vs P post t t' _ _ Hpl F.cftBranch11 Hag

theorem AxEpiLdJr.frameFactsGAg (tick : Bool) (t : ExecSt) (A Dr Dw D : List Register)
    (base : Int) (vs : List (BitVec 8)) (P : List Register) (post : RegFile → Bool) (t' : ExecSt)
    (F : CjrFrameFactsG tick t A Dr Dw D base vs P post) (Hpl : postLocal P post)
    (Hag : agreeOn A t.regs t'.regs) : CjrFrameFactsG tick t' A Dr Dw D base vs P post where
  cfgSeipDr := F.cfgSeipDr
  cfgMeipDr := F.cfgMeipDr
  cfgSeipD := F.cfgSeipD
  cfgMeipD := F.cfgMeipD
  cfgToSeip := AxEpiLdJr.seipAtAgAg A tick t t' F.cfgToSeip Hag
  cfgBranch00 := AxEpiLdJr.branchAtAgGAg tick A Dr Dw D base vs P post t t' _ _ Hpl F.cfgBranch00 Hag
  cfgBranch01 := AxEpiLdJr.branchAtAgGAg tick A Dr Dw D base vs P post t t' _ _ Hpl F.cfgBranch01 Hag
  cfgBranch10 := AxEpiLdJr.branchAtAgGAg tick A Dr Dw D base vs P post t t' _ _ Hpl F.cfgBranch10 Hag
  cfgBranch11 := AxEpiLdJr.branchAtAgGAg tick A Dr Dw D base vs P post t t' _ _ Hpl F.cfgBranch11 Hag

/-! ## The ref ledgers -/

/-- (Lean-only) `AJrT` without `x1`, `minstret`, `mcycle` (the registers `tFrameT` pins to
`probeRegs pcJr`). -/
def AxEpiLdJr.LNone : List Register :=
  [.mseccfg, .elp, .htif_tohost_base, .pmpaddr_n, .pmpcfg_n, .pma_regions, .PC,
   .mstatus, .mie, .mip, .mideleg, .misa, .hart_state, .minstretcfg, .mcountinhibit,
   .cur_privilege, .menvcfg, .mtimecmp, .mtime, .mcyclecfg]

theorem AxEpiLdJr.noneSub :
    ∀ r ∈ AJrT, r ≠ .mcycle → r ≠ .minstret → r ≠ .x1 → r ∈ AxEpiLdJr.LNone := by decide +kernel

theorem AxEpiLdJr.obsNoneEq (v' v u' u : BitVec 1) :
    AxEpiLdJr.obsL AxEpiLdJr.LNone (ldOut ⟨v', v, u', u, none⟩ AxEpiLdJr.w0) =
      AxEpiLdJr.obsL AxEpiLdJr.LNone (probeRegs pcJr) := by
  rw [AxEpiLdJr.ldOutCanon]
  ax_epi_ledger_krfl

theorem AxEpiLdJr.agreeTFrameT (v' v u' u : BitVec 1) (ra : BitVec 64) :
    agreeOn AJrT
      (tFrameT ra ((ldOut ⟨v', v, u', u, none⟩ AxEpiLdJr.w0) .minstret)
        ((ldOut ⟨v', v, u', u, none⟩ AxEpiLdJr.w0) .mcycle)).regs
      (ldRef ⟨v', v, u', u, none⟩ ra).regs := by
  have hobs := AxEpiLdJr.agreeOfObsL _ _ _ (AxEpiLdJr.obsNoneEq v' v u' u)
  intro r Hr
  show ((((probeRegs pcJr).set .x1 ra).set .minstret _).set .mcycle _) r =
    ((ldOut ⟨v', v, u', u, none⟩ AxEpiLdJr.w0).set .x1 ra) r
  by_cases h1 : r = .mcycle
  · subst h1
    rw [RegFile.set_same, RegFile.set_other _ _ _ _ (show Register.mcycle ≠ Register.x1 by decide)]
  · rw [RegFile.set_other _ _ _ _ h1]
    by_cases h2 : r = .minstret
    · subst h2
      rw [RegFile.set_same,
        RegFile.set_other _ _ _ _ (show Register.minstret ≠ Register.x1 by decide)]
    · rw [RegFile.set_other _ _ _ _ h2]
      by_cases h3 : r = .x1
      · subst h3
        rw [RegFile.set_same, RegFile.set_same]
      · rw [RegFile.set_other _ _ _ _ h3, RegFile.set_other _ _ _ _ h3]
        exact (hobs r (AxEpiLdJr.noneSub r Hr h1 h2 h3)).symm

/-- After an UNticked load, the c.jr tick ledger at the reference `ldRef` (transferred from
`epiFrameCjrTick`, deviation 4). -/
theorem cjrRefFactsNone (v' v u' u : BitVec 1) (ra : BitVec 64) :
    CjrTickFrameFacts (ldRef ⟨v', v, u', u, none⟩ ra) AJrT AxEpiProbe.drNopin DwAll DPost
      (pcJr : Int) cjrVs4 PPc (postRaSym ra) :=
  AxEpiLdJr.tickFrameFactsAg _ _ _ _ _ _ _ _ _ _ (epiFrameCjrTick ra _ _) (postRaSymLocal ra)
    (AxEpiLdJr.agreeTFrameT v' v u' u ra)

theorem branchRefNone (v' v u' u : BitVec 1) (ra : BitVec 64) (a' a : BitVec 1) :
    branchAtTickAg AJrT AxEpiProbe.drNopin DwAll DPost (pcJr : Int) cjrVs4 PPc (postRaSym ra)
      (ldRef ⟨v', v, u', u, none⟩ ra) a' a = true := by
  have F := cjrRefFactsNone v' v u' u ra
  rcases bv1Cases a' with rfl | rfl <;> rcases bv1Cases a with rfl | rfl
  · exact F.cftBranch00
  · exact F.cftBranch01
  · exact F.cftBranch10
  · exact F.cftBranch11

/-- (Lean-only) The reference state after a TICKED load: `tFrameT` with the load's tick applied
(`mtime = 1`, MTIP pending in `mip`). -/
def AxEpiLdJr.tFrameS (ra mi mc : BitVec 64) : ExecSt :=
  ⟨(((((probeRegs pcJr).set .x1 ra).set .minstret mi).set .mcycle mc).set .mtime 1#64).set .mip
    0x80#64, probeMem, testDevs⟩

set_option maxHeartbeats 4000000 in
theorem AxEpiLdJr.branchFrameTickGSym (ra mi mc : BitVec 64) (v' v : BitVec 1) :
    branchAtAgG true AJrT AxEpiProbe.drNopin DwAll DPost (pcJr : Int) cjrVs4 PPc (postRaSym ra)
      (AxEpiLdJr.tFrameS ra mi mc) v' v = true := by
  unfold branchAtAgG
  ax_epi_cjr_frame_tac v' v

theorem AxEpiLdJr.epiFrameCjrTickG (ra mi mc : BitVec 64) :
    CjrFrameFactsG true (AxEpiLdJr.tFrameS ra mi mc) AJrT AxEpiProbe.drNopin DwAll DPost
      (pcJr : Int) cjrVs4 PPc (postRaSym ra) where
  cfgSeipDr := by decide +kernel
  cfgMeipDr := by decide +kernel
  cfgSeipD := by decide +kernel
  cfgMeipD := by decide +kernel
  cfgToSeip := by ax_epi_ledger_krfl
  cfgBranch00 := AxEpiLdJr.branchFrameTickGSym ra mi mc _ _
  cfgBranch01 := AxEpiLdJr.branchFrameTickGSym ra mi mc _ _
  cfgBranch10 := AxEpiLdJr.branchFrameTickGSym ra mi mc _ _
  cfgBranch11 := AxEpiLdJr.branchFrameTickGSym ra mi mc _ _

/-- (Lean-only) `AJrT` without `x1`, `minstret`, `mcycle`, `mtime`, `mip`. -/
def AxEpiLdJr.LSome : List Register :=
  [.mseccfg, .elp, .htif_tohost_base, .pmpaddr_n, .pmpcfg_n, .pma_regions, .PC,
   .mstatus, .mie, .mideleg, .misa, .hart_state, .minstretcfg, .mcountinhibit,
   .cur_privilege, .menvcfg, .mtimecmp, .mcyclecfg]

theorem AxEpiLdJr.someSub :
    ∀ r ∈ AJrT, r ≠ .mip → r ≠ .mtime → r ≠ .mcycle → r ≠ .minstret → r ≠ .x1 →
      r ∈ AxEpiLdJr.LSome := by decide +kernel

theorem AxEpiLdJr.obsSomeEq (v' v u' u u2' u2 : BitVec 1) :
    ((ldOut ⟨v', v, u', u, some (u2', u2)⟩ AxEpiLdJr.w0) .mip,
      (ldOut ⟨v', v, u', u, some (u2', u2)⟩ AxEpiLdJr.w0) .mtime,
      AxEpiLdJr.obsL AxEpiLdJr.LSome (ldOut ⟨v', v, u', u, some (u2', u2)⟩ AxEpiLdJr.w0)) =
    (0x80#64, 1#64, AxEpiLdJr.obsL AxEpiLdJr.LSome (probeRegs pcJr)) := by
  rw [AxEpiLdJr.ldOutCanon]
  ax_epi_ledger_krfl

theorem AxEpiLdJr.agreeTFrameS (v' v u' u u2' u2 : BitVec 1) (ra : BitVec 64) :
    agreeOn AJrT
      (AxEpiLdJr.tFrameS ra ((ldOut ⟨v', v, u', u, some (u2', u2)⟩ AxEpiLdJr.w0) .minstret)
        ((ldOut ⟨v', v, u', u, some (u2', u2)⟩ AxEpiLdJr.w0) .mcycle)).regs
      (ldRef ⟨v', v, u', u, some (u2', u2)⟩ ra).regs := by
  have H := AxEpiLdJr.obsSomeEq v' v u' u u2' u2
  simp only [Prod.mk.injEq] at H
  obtain ⟨hmip, hmtime, hobs⟩ := H
  have hag := AxEpiLdJr.agreeOfObsL _ _ _ hobs
  intro r Hr
  show (((((probeRegs pcJr).set .x1 ra).set .minstret _).set .mcycle _).set .mtime 1#64).set .mip
    0x80#64 r = ((ldOut ⟨v', v, u', u, some (u2', u2)⟩ AxEpiLdJr.w0).set .x1 ra) r
  by_cases h0 : r = .mip
  · subst h0
    rw [RegFile.set_same, RegFile.set_other _ _ _ _ (show Register.mip ≠ Register.x1 by decide),
      hmip]
  · rw [RegFile.set_other _ _ _ _ h0]
    by_cases h4 : r = .mtime
    · subst h4
      rw [RegFile.set_same,
        RegFile.set_other _ _ _ _ (show Register.mtime ≠ Register.x1 by decide), hmtime]
    · rw [RegFile.set_other _ _ _ _ h4]
      by_cases h1 : r = .mcycle
      · subst h1
        rw [RegFile.set_same,
          RegFile.set_other _ _ _ _ (show Register.mcycle ≠ Register.x1 by decide)]
      · rw [RegFile.set_other _ _ _ _ h1]
        by_cases h2 : r = .minstret
        · subst h2
          rw [RegFile.set_same,
            RegFile.set_other _ _ _ _ (show Register.minstret ≠ Register.x1 by decide)]
        · rw [RegFile.set_other _ _ _ _ h2]
          by_cases h3 : r = .x1
          · subst h3
            rw [RegFile.set_same, RegFile.set_same]
          · rw [RegFile.set_other _ _ _ _ h3, RegFile.set_other _ _ _ _ h3]
            exact (hag r (AxEpiLdJr.someSub r Hr h0 h4 h1 h2 h3)).symm

/-- After a TICKED load, the c.jr's tick reads no pin: the general-tick ledger at `ldRef`
(transferred from `AxEpiLdJr.epiFrameCjrTickG`, deviation 4). -/
theorem cjrRefFactsSome (v' v u' u u2' u2 : BitVec 1) (ra : BitVec 64) :
    CjrFrameFactsG true (ldRef ⟨v', v, u', u, some (u2', u2)⟩ ra) AJrT AxEpiProbe.drNopin DwAll
      DPost (pcJr : Int) cjrVs4 PPc (postRaSym ra) :=
  AxEpiLdJr.frameFactsGAg _ _ _ _ _ _ _ _ _ _ _ (AxEpiLdJr.epiFrameCjrTickG ra _ _)
    (postRaSymLocal ra) (AxEpiLdJr.agreeTFrameS v' v u' u u2' u2 ra)

theorem branchRefSome (v' v u' u u2' u2 : BitVec 1) (ra : BitVec 64) (a' a : BitVec 1) :
    branchAtAgG true AJrT AxEpiProbe.drNopin DwAll DPost (pcJr : Int) cjrVs4 PPc (postRaSym ra)
      (ldRef ⟨v', v, u', u, some (u2', u2)⟩ ra) a' a = true := by
  have F := cjrRefFactsSome v' v u' u u2' u2 ra
  rcases bv1Cases a' with rfl | rfl <;> rcases bv1Cases a with rfl | rfl
  · exact F.cfgBranch00
  · exact F.cfgBranch01
  · exact F.cfgBranch10
  · exact F.cfgBranch11

/-! ## The packaged c.jr `wpd` at the load's exact exit -/

/-- The return address the c.jr jumps to: x1 of the exit. -/
noncomputable def raOf (c : Ldc) (w : List (BitVec 8)) : BitVec 64 := (ldOut c w) .x1

theorem ldOutAgreeRef' (c : Ldc) (w : List (BitVec 8)) :
    agreeOn AJrT (ldOut c w) (ldRef c (raOf c w)).regs :=
  ldOutAgreeRef c w

/-- The c.jr row-end set per case and tick: after a ticked load the c.jr's tick = true step has a
flat tail (`AxEpiLdJr.ledgerInvG`), otherwise the usual sets. -/
noncomputable def cjrAfterLdInv (c : Ldc) (w : List (BitVec 8)) (tick : Bool) (cpu : CPU)
    (kk : Nat) (s1 : Athread) : Prop :=
  if tick then
    match c.lcT with
    | none => ledgerCjrtInv ⟨ldOut c w, probeMem, testDevs⟩ AxEpiProbe.drNopin DwAll DPost cjrVs4
        cpu kk s1
    | some _ => AxEpiLdJr.ledgerInvG true ⟨ldOut c w, probeMem, testDevs⟩ AxEpiProbe.drNopin DwAll DPost
        cjrVs4 cpu kk s1
  else
    AxEpiLedger.ledgerInv ⟨ldOut c w, probeMem, testDevs⟩ AxEpiProbe.drNopin DwAll DPost cjrVs4
      cpu kk s1

theorem rtcLedgerLdStep (cpu : CPU) (vs : List (BitVec 8)) (s s' : Athread) :
    rtc (AxEpiLedger.ledgerStep cpu vs) s s' → rtc (ldStep cpu vs) s s' :=
  rtc_subrel (fun _ _ h => .inl h)

/-- SANITY: the c.jr row-end set at every exact exit reaches `.pure ()`. -/
theorem cjrAfterLdInvReachesRet (c : Ldc) (w : List (BitVec 8)) (tick : Bool) (cpu : CPU)
    (kk : Nat) (s1 : Athread) :
    cjrAfterLdInv c w tick cpu kk s1 →
    ∃ t0 s', aeqv s1 t0 ∧ rtc (ldStep cpu cjrVs4) t0 s' ∧
      RetP cpu (fun rs3 => postRaSym (raOf c w) rs3 = true) kk s' := by
  obtain ⟨v', v, u', u, o⟩ := c
  cases tick
  · simp only [cjrAfterLdInv, Bool.false_eq_true, ↓reduceIte]
    intro H
    exact cjrFrameInvReachesRet' false (raOf _ w) (ldOut _ w) cpu kk s1 (ldOutAgreeJr _ w) H
  · cases o with
    | none =>
      simp only [cjrAfterLdInv, ↓reduceIte]
      intro H
      exact ledgerCjrtInvReachesRet _ _ _ _ (pcJr : Int) _ _ cpu kk s1
        (tickFrameFactsTransfer _ _ _ _ _ _ _ _ _ ⟨ldOut _ w, probeMem, testDevs⟩
          (cjrRefFactsNone v' v u' u (raOf _ w)) (postRaSymLocal _)
          (agreeOnSym _ _ _ (ldOutAgreeRef' _ w))) H
    | some p =>
      obtain ⟨u2', u2⟩ := p
      simp only [cjrAfterLdInv, ↓reduceIte]
      intro H
      have F := frameFactsTransferG true _ _ _ _ _ _ _ _ _ ⟨ldOut _ w, probeMem, testDevs⟩
        (cjrRefFactsSome v' v u' u u2' u2 (raOf _ w)) (postRaSymLocal _)
        (agreeOnSym _ _ _ (ldOutAgreeRef' _ w))
      obtain ⟨t0, s', Ha, Hr, Hs⟩ := ledgerInvGReachesRet _ _ _ _ _ _ _ _ _ _ _ F H
      exact ⟨t0, s', Ha, rtcLedgerLdStep _ _ _ _ Hr, Hs⟩

section cjrAfterLd
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- (2) THE c.jr AT EVERY EXACT EXIT OF THE c.ldsp, BOTH TICKS, EVERY LOADED WORD: from register
file `ldOut c w`, `riscvStep tick` runs the c.jr to `.pure ()` with PC = `jalrTarget (raOf c w)`. -/
theorem wpdCjrAfterLd (c : Ldc) (w : List (BitVec 8)) (tick : Bool) (i : Agent)
    (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch) (kk : Nat)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk (pcJr : Int) cjrVs4⌝) :
    ⊢ ((∀ s', ⌜RetP cpu (fun rs3 => postRaSym (raOf c w) rs3 = true) kk s'⌝ -∗
          wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1, ⌜cjrAfterLdInv c w tick cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep tick) (ldOut c w) none ib, kk⟩ Φ := by
  obtain ⟨v', v, u', u, o⟩ := c
  cases tick
  · simp only [cjrAfterLdInv, Bool.false_eq_true, ↓reduceIte]
    iintro R
    iapply (wpdCjrFrame (raOf _ w) i Φ cpu ib kk Hgd _ (ldOutAgreeJr _ w))
    isplit
    · icases R with ⟨R, -⟩
      iintro %s' %Hs'
      iapply R $$ %s' %Hs'
    · icases R with ⟨-, R⟩
      iexact R
  · cases o with
    | none =>
      simp only [cjrAfterLdInv, ↓reduceIte]
      exact wpdCjrFrameTickGen i Φ cpu ib kk _ _ _ _ _ _ _ _ _
        (cjrRefFactsNone v' v u' u (raOf _ w)) (postRaSymLocal _) Hgd _ (ldOutAgreeRef' _ w)
    | some p =>
      obtain ⟨u2', u2⟩ := p
      simp only [cjrAfterLdInv, ↓reduceIte]
      exact wpdCjrFrameGenG true i Φ cpu ib kk _ _ _ _ _ _ _ _ _
        (cjrRefFactsSome v' v u' u u2' u2 (raOf _ w)) (postRaSymLocal _) Hgd _
        (ldOutAgreeRef' _ w)

end cjrAfterLd

end Weak
