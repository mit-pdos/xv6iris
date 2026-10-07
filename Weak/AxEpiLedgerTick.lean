/-
Weak: **the `c.sdsp → c.ldsp` handoff of the J0 epilogue, and the `c.ldsp` `wpd` for BOTH tick
bits.**

Rocq: `iris/AxEpiLedgerTick.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 HANDOFF.  `sdFinal t … v' v` recomputes, from the same terms `AxEpiLedgerSd.epiLedgerCsdsp`
checks, the state the store's post-fetch run ends in (answers `v'`/`v` of the boundary pin
reads); `tAfterSd v' v` is that state at `tAt pcSd`.  `RegFile` has no decidable equality, so the
post is pinned by a NEW exit set, not a boolean `post`: `wpdCsdspStepExact` is
`wpdCsdspStepOfLedger` with the continuation owed only on `SdRetX` (the `.pure ()` node at the
register file `sdFinal` computes), and `sdPostExact` turns that into
`RetX cpu (tAfterSd v' v).regs`.  The handoff is indexed by the answers; the load is verified at
EVERY `tAfterSd v' v`.  Memory: no ledger reads model memory (the fetch bytes are a parameter);
`tAfterSdText` checks the text still holds `0x60a2` at `pcLd`.
§2 `wpdOfSeipSplitRtc`: the boundary split from any `aeqv` start and an `rtc` prefix (the
previous `.pure ()` is only up to `aeqv`); `wpdCldspStepOfLedgerAgree`: the tick = false load from
any register file agreeing with the ledger state off the pins.
§3/§4 tick = true: `AxLdTickFacts` — the post-load segment runs (`toPin`) to the SECOND pin
reads (`tick_clock`), and per answer has an `epure` certificate to `.pure ()`;
`wpdCldspStepOfLedgerTick`; row end only on `ledgerLdtInv` (sanity `ledgerLdtInvReachesRet`).
§5 `wpdCldspAfterSd`: ∀ tick (in `Weak.AxEpiLedgerTick2`).

## Deviations from Rocq

1. THE TWO-PIN BOUNDARY (`AxEpiLedger` deviation 1, the CONVENTION of its header).  Every Rocq
   `to_seip` split is the `sig_meip` split then the `sig_seip` split — at the instruction
   boundary AND in the tick's `clint_dispatch` (Lean's `read_mip IncludePlatformInterrupts`
   reads `sig_meip` then `sig_seip`, `AxEpiProbe`'s finding).  So: `sdFinal`/`tAfterSd`/`SdRetX`
   carry the two answers `v' v` (`sdPostExact` gives `∃ v' v`; the §5 lemmas quantify `v' v`);
   `sdFinalChain` takes the two pin nodes; `seipAtTick` checks the meip node and the seip node
   after both meip answers; `ldtBranchAt` takes `v' v`; `AxLdTickFacts` has the fields
   `ltSeipDr`, `ltMeipDr`, `ltSeipD`, `ltMeipD`, `ltToSeip`, `ltBranch00/01/10/11` (Rocq
   `lt_branch0/1`); `tickPostOk` is `toPin` to the tick's meip node, then (Lean-only
   `AxEpiLedgerTick.tickAfterMeip`, per meip answer) `toPin` to its seip node, then the two
   `tickRetOk`; `tickPostOkAt` takes the two tail pin nodes (and Lean-only
   `AxEpiLedgerTick.tickPostOkNext` gives the second from the first), `tickPostOkShape` returns
   the meip node; `tickTailInv` and `ledgerLdtInv` have the meip-level `Pseip` disjunct and
   quantify the seip node per meip answer; `wpdTickTail` splits twice
   (`AxEpiLedger.meipN0Ok`, then `n0OkSeipRead` with exit `tickExit`).
2. THE PINS (`AxRunClose` deviation 1): `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg`;
   the sanity and `wpd` lemmas take both pins `∉ D`; the concrete instances use
   `AxEpiProbe.drNopin` for Rocq's `Dr_noseip`.
3. O2 STAGE C (`AxEpiLedger` deviation 3, `AxEpiLedgerSd` deviation 3): the fetch is a pinned
   admin step at the SAME row position.  `ldtFetchOk` checks `akIfetch = true` (Rocq
   `negb ak_latest`); `ldtLoadOk` adds `akIfetch = false` (replaces `Hntext`, dropped from
   `wpdCldspStepOfLedgerAgree/Tick`, `wpdCldspAfterSd*`; `wpdLoadThenTick` and
   `wpdFetchThenLoadTick` take `Hnf`); `Hgd` states `AxCjrWpd.fetchImgOk`; the fetch's
   `Hflow`/`Hloc` are dropped.  Positions: the store/load node, `Hrow`, `F` at `kk` (Rocq
   `S kk`); `RetX`/`SdRetX`/`RetLd`, the post-load tail and `tickTailInv` at `kk + 1` (Rocq
   `S (S kk)`).
4. TYPES (as `AxEpiLedger` deviation 4 / `AxEpiLedgerSd` deviation 5): `mstate` ↦ `ExecSt`,
   `regstate` ↦ `RegFile`, `gset` ↦ `List Register`, `bool_decide` ↦ `decide`, the request
   types carry the bound `va`, the write answer `inl None` ↦ `.Ok (some true)`, `Ret tt` ↦ `.pure ()`,
   `default d o` ↦ `o.getD d`; post-load predicates take `x.toNat` (Rocq `bv_unsigned x`);
   `ldtLoadReaches` uses the word `0`.  `sdFinalSome` states `(sdFinal …).isSome = true` (Rocq's
   `match … with Some _ => true | None => false`).  `text_ld_obs` reads with `bmRead` and
   returns `Option Nat` (`AxEpiProbe` deviation 2).  `wpd_of_seip_split_rtc` is proved through
   `AxEpiLedger.wpdOfSplitFrom` (Rocq: `wpd_of_closed_run` inline).
5. `vm_compute` ↦ `decide +kernel`.  The load ledgers' branch fields quantify over the loaded
   word: as in `AxEpiLedger` deviation 5, they go through boolean twins at ONE free 64-bit word,
   checked with `ax_epi_ledger_krfl` (`AxEpiLedger`'s twins for the tick = false ledger; Lean-only
   `AxEpiLedgerTick.tickRetB/tickAfterMeipB/tickPostB/ldtLoadB/ldtFetchB/ldtBranchB/ldtBranchAtB`
   and the bridges `…OfB` for the tick ledger).
6. Lean-only helpers (file-qualified, `AxEpiLedgerTick.*`): `tickAfterMeip`, `tickPostOkNext`,
   `tickPostOkAll`, `seipAtTickSpec`, `seipAtTickNext`, `ldtBranchAtEq`, `tailFromMeip`,
   `ldtSeipReaches`, `ldtMeipReaches`, `erdOfLdtBranch`, and the twins of deviation 5.

**Rocq → Lean name map.**  `sd_after_store` `sdAfterStore`, `sd_after_fetch` `sdAfterFetch`,
`sd_final` `sdFinal`, `t_after_sd` `tAfterSd`, `RetX` `RetX`, `SdRetX` `SdRetX`, `ans_seip_node`
`ansSeipNode`, `sd_final_chain` `sdFinalChain`, `sd_final_some` `sdFinalSome`, `t_after_sd_pc`
`tAfterSdPc`, `t_after_sd_post` `tAfterSdPost`, `sd_post_exact` `sdPostExact`, `aeqv_of_agree`
`aeqvOfAgree`, `wpd_csdsp_step_exact` `wpdCsdspStepExact`, `wpd_csdsp_concrete'`
`wpdCsdspConcrete'`, `wpd_of_seip_split_rtc` `wpdOfSeipSplitRtc`, `wpd_boundary_erd_rtc`
`wpdBoundaryErdRtc`, `wpd_cldsp_step_of_ledger_agree` `wpdCldspStepOfLedgerAgree`,
`text_ld_obs` `textLdObs`, `t_after_sd_text` `tAfterSdText`, `epi_ledger_cldsp_after_sd`
`epiLedgerCldspAfterSd`, `tick_ret_ok` `tickRetOk`, `tick_post_ok` `tickPostOk`, `ldt_load_ok`
`ldtLoadOk`, `ldt_fetch_ok` `ldtFetchOk`, `ldt_branch_ok` `ldtBranchOk`, `seip_at_tick`
`seipAtTick`, `ldt_branch_at` `ldtBranchAt`, `AxLdTickFacts` `AxLdTickFacts` (`lt*`),
`epi_ledger_cldsp_tick` `epiLedgerCldspTick`, `tick_post_ok_at` `tickPostOkAt`,
`tick_post_ok_shape` `tickPostOkShape`, `ldt_load_ok_node` `ldtLoadOkNode`, `ldt_fetch_ok_node`
`ldtFetchOkNode`, `ldt_branch_ok_node` `ldtBranchOkNode`, `RetP` `RetP`, `tick_exit` `tickExit`,
`tick_tail_inv` `tickTailInv`, `ledger_ldt_inv` `ledgerLdtInv`, `tail_from_seip` `tailFromSeip`,
`tail_reaches_start` `tailReachesStart`, `tail_reaches_inv` `tailReachesInv`, `ldt_load_reaches`
`ldtLoadReaches`, `ldt_fetch_reaches` `ldtFetchReaches`, `ldt_branch_reaches`
`ldtBranchReaches`, `ldt_ledger_branch` `ldtLedgerBranch`, `ledger_ldt_inv_reaches_ret`
`ledgerLdtInvReachesRet`, `wpd_tick_tail` `wpdTickTail`, `wpd_load_then_tick` `wpdLoadThenTick`,
`wpd_fetch_then_load_tick` `wpdFetchThenLoadTick`, `wpd_cldsp_step_of_ledger_tick`
`wpdCldspStepOfLedgerTick`, `ld_after_sd_inv` `ldAfterSdInv`, `ld_after_sd_inv_reaches_ret`
`ldAfterSdInvReachesRet`, `wpd_cldsp_after_sd_false` `wpdCldspAfterSdFalse`,
`wpd_cldsp_after_sd_true` `wpdCldspAfterSdTrue`, `wpd_cldsp_after_sd` `wpdCldspAfterSd`.  None is
in the duplicated-name table.

**Split** (build time): `text_ld_obs`, `t_after_sd_text`, `epi_ledger_cldsp_after_sd`,
`epi_ledger_cldsp_tick` and §5 (`ld_after_sd_inv` … `wpd_cldsp_after_sd`) live in
`Weak.AxEpiLedgerTick2` (about 95 s; this file about 20 s).

**Dropped:** nothing (Rocq 56 definitions/lemmas; Lean 56 over the two files, 47 here and 9 in
`AxEpiLedgerTick2`, + 24 Lean-only helpers here).  **Not ported:** the `Print Assumptions`
block (the lint's axiom check covers it).
-/
import Weak.AxEpiLedgerSd

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! # 1. The handoff -/

def sdAfterStore (D : List Register) (mw : SailM Unit) (tw : ExecSt) : Option ExecSt :=
  match mw with
  | .impure (.ok (.memWrite _ _ _)) KK =>
    match epure D (KK (.Ok (some true))) tw with
    | some (_, t3) => some t3
    | none => none
  | _ => none

def sdAfterFetch (Dr Dw D : List Register) (vs : List (BitVec 8)) (mf : SailM Unit)
    (t2 : ExecSt) : Option ExecSt :=
  match mf with
  | .impure (.ok (.memRead n _ _)) KKf =>
    match ewr Dr Dw (KKf (.Ok (wordOfBytes n vs, none))) t2 with
    | some (mw, tw) => sdAfterStore D mw tw
    | none => none
  | _ => none

/-- The store's final state for the boundary answers `v'` (`sig_meip`) and `v` (`sig_seip`). -/
noncomputable def sdFinal (t : ExecSt) (Dr Dw D : List Register) (vs : List (BitVec 8))
    (v' v : BitVec 1) : Option ExecSt :=
  match AxEpiLedger.toPin (riscvStep false) t with
  | some (m0, t0) =>
    match AxEpiLedger.toPin (AxEpiLedger.ansMeip m0 v') t0 with
    | some (m1, t1) =>
      match erd Dr Dw (ansSeip m1 v) t1 with
      | some (mf, t2) => sdAfterFetch Dr Dw D vs mf t2
      | none => none
    | none => none
  | none => none

noncomputable def tAfterSd (v' v : BitVec 1) : ExecSt :=
  (sdFinal (tAt pcSd) AxEpiProbe.drNopin DwAll DPost sdVs v' v).getD (tAt pcSd)

/-- The pinned exit: the `.pure ()` node at register file `rs`, up to `aeqv`. -/
def RetX (cpu : CPU) (rs : RegFile) (k : Nat) (s : Athread) : Prop :=
  ∃ ib', Qat ⟨.PHart cpu (.pure ()) rs none ib', k⟩ s

/-- The exact exit set of the store: the `.pure ()` node at the register file `sdFinal`
computes, for some answers `v' v` of the boundary pin reads. -/
def SdRetX (t : ExecSt) (Dr Dw D : List Register) (vs : List (BitVec 8)) (cpu : CPU) (k : Nat)
    (s : Athread) : Prop :=
  ∃ v' v t3, sdFinal t Dr Dw D vs v' v = some t3 ∧ RetX cpu t3.regs k s

theorem ansSeipNode (k0 : RegisterType Register.sig_seip → SailM Unit) (v : BitVec 1) :
    ansSeip (.impure (.ok (.regRead Register.sig_seip)) k0) v = k0 v :=
  AxEpiLedger.ansSeipNode k0 v

theorem sdFinalChain (t : ExecSt) (Dr Dw D : List Register) (vs : List (BitVec 8))
    (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt) (v' : BitVec 1)
    (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt) (v : BitVec 1)
    (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KKf : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (t2 : ExecSt)
    (nw vaw : Nat) (reqw : Mem_write_request nw vaw Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (tw t3 : ExecSt) :
    AxEpiLedger.toPin (riscvStep false) t
      = some (.impure (.ok (.regRead Register.sig_meip)) km, t0) →
    AxEpiLedger.toPin (km v') t0 = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) →
    erd Dr Dw (k0 v) t1 = some (.impure (.ok (.memRead n va req)) KKf, t2) →
    ewr Dr Dw (KKf (.Ok (wordOfBytes n vs, none))) t2
      = some (.impure (.ok (.memWrite nw vaw reqw)) KK, tw) →
    epure D (KK (.Ok (some true))) tw = some ((), t3) →
    sdFinal t Dr Dw D vs v' v = some t3 := by
  intro Hts Hts1 He He2 Hep
  unfold sdFinal
  rw [Hts]
  dsimp only
  rw [AxEpiLedger.ansMeipNode, Hts1]
  dsimp only
  rw [ansSeipNode, He]
  dsimp only [sdAfterFetch]
  rw [He2]
  dsimp only [sdAfterStore]
  rw [Hep]

/-! Handoff sanity (small observables only). -/

theorem sdFinalSome (v' v : BitVec 1) :
    (sdFinal (tAt pcSd) AxEpiProbe.drNopin DwAll DPost sdVs v' v).isSome = true := by
  rcases bv1Cases v' with rfl | rfl <;> rcases bv1Cases v with rfl | rfl <;> decide +kernel

theorem tAfterSdPc (v' v : BitVec 1) : AxEpiProbe.pcOf (tAfterSd v' v) = pcLd := by
  rcases bv1Cases v' with rfl | rfl <;> rcases bv1Cases v with rfl | rfl <;> decide +kernel

theorem tAfterSdPost (v' v : BitVec 1) : sdPost (tAfterSd v' v).regs = true := by
  rcases bv1Cases v' with rfl | rfl <;> rcases bv1Cases v with rfl | rfl <;> decide +kernel

/-- THE HANDOFF: the store's exact exit IS the `.pure ()` node at `tAfterSd v' v`. -/
theorem sdPostExact (cpu : CPU) (k : Nat) (s : Athread) :
    SdRetX (tAt pcSd) AxEpiProbe.drNopin DwAll DPost sdVs cpu k s →
    ∃ v' v, RetX cpu (tAfterSd v' v).regs k s := by
  rintro ⟨v', v, t3, Hf, Hr⟩
  refine ⟨v', v, ?_⟩
  unfold tAfterSd
  rw [Hf]
  exact Hr

theorem aeqvOfAgree (c : CPU) (m : SailM Unit) (rs rs' : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (k : Nat) :
    regsAgree AxRunClose.pinReg rs' rs →
    aeqv ⟨.PHart c m rs fn ib, k⟩ ⟨.PHart c m rs' fn ib, k⟩ :=
  fun h => ⟨rfl, rfl, rfl, rfl, rfl, regsAgreeSym _ _ _ h⟩

section sdExact
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- `wpdCsdspStepOfLedger` with the EXACT exit `SdRetX`. -/
theorem wpdCsdspStepExact (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch)
    (kk : Nat) (t : ExecSt) (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (staddr : Int) (data : List (BitVec 8)) (post : RegFile → Bool)
    (L : AxSdModelFacts t Dr Dw D base vs staddr data post)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk base vs⌝)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜storeRowOk GD i kk⌝) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i kk ls -∗
         storeFlow GD i kk data) -∗
      ((∀ s', ⌜SdRetX t Dr Dw D vs cpu (kk + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1, ⌜ledgerSdInv t Dr Dw D vs cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) t.regs none ib, kk⟩ Φ := by
  have HDr := of_decide_eq_false L.lsSeipDr
  have HDrm := of_decide_eq_false L.lsMeipDr
  have HD := of_decide_eq_false L.lsSeipD
  have HDm := of_decide_eq_false L.lsMeipD
  obtain ⟨km, t0, Hts⟩ := AxEpiLedger.seipAtSpec t L.lsToSeip
  have Hnext := AxEpiLedger.seipAtNext t km t0 L.lsToSeip Hts
  obtain ⟨ib0, Hr0⟩ := AxEpiLedger.toPinGstep _ t ib _ _ Hts cpu kk
  iintro F R
  iapply (AxEpiLedger.wpdOfSplitFrom i Φ _ _ _
    (AxEpiLedger.pseipStart cpu _ t.regs ib kk _ (AxEpiLedger.seipExit cpu km t0 kk) Hr0)
    (AxEpiLedger.meipN0Ok cpu km t0 ib0 kk Hnext))
  isplit
  · iintro %s2 %HQ
    obtain ⟨q, ⟨v', k0, t1, ib1, Hts1, rfl⟩, Hq⟩ := HQ
    have Hb := sdLedgerBranch t Dr Dw D base vs staddr data post km t0 v' k0 t1 L Hts Hts1
    iapply (AxEpiLedger.wpdOfSplitFrom i Φ s2 _ (erdExit Dr Dw cpu k0 t1 kk) (.inr (.inl Hq))
      (AxEpiLedger.seipN0Ok cpu k0 t1 ib1 kk Dr Dw HDr HDrm
        (fun v => AxEpiLedgerSd.erdOfSdBranch Dr Dw D base vs staddr data post _ t1 (Hb v))))
    isplit
    · iintro %s3 %HQ3
      obtain ⟨q3, ⟨v, qm, t2, ib2, He, rfl, -⟩, Hs3⟩ := HQ3
      have Hbv := Hb v
      unfold sdBranchOk at Hbv
      rw [He] at Hbv
      obtain ⟨n, va, req, KKf, rfl⟩ := sdFetchOkShape _ _ _ _ _ _ _ _ _ _ Hbv
      obtain ⟨Hdev, Hfe, Hpa, Hlen, mw, tw, He2, Hs⟩ := sdFetchOkNode _ _ _ _ _ _ _ _ _ _ _ _ _ Hbv
      obtain ⟨nw, vaw, reqw, KK, rfl⟩ := sdStoreOkShape _ _ _ _ _ _ Hs
      obtain ⟨Hdevw, Hlatw, -, Hdataw, t3, Hep, -⟩ := sdStoreOkNode _ _ _ _ _ _ _ _ _ Hs
      subst Hpa
      obtain ⟨p3, k3⟩ := s3
      obtain ⟨hk, hp⟩ := Hs3
      simp only at hk hp
      subst k3
      match p3, hp with
      | .PHart c3 m3 rs3 fn3 ib3', hp =>
        obtain ⟨hc, hm, hf, hi, hag⟩ := hp
        subst c3 m3 fn3 ib3'
        obtain ⟨ibW, HrunPre⟩ := ewrGstep Dr Dw _ HDr HDrm t2 ib2 _ _ He2 cpu kk
        iapply (wpdFetchThenStore Φ i cpu n va req KKf ib2 kk vs t2.regs rs3 nw vaw reqw KK ibW
          tw D data t3 Hdev Hfe Hlen Hgd (regsAgreeSym _ _ _ hag) HrunPre Hdevw Hlatw Hdataw
          Hrow HD HDm Hep) $$ F
        isplit
        · isplit
          · icases R with ⟨R, -⟩
            iintro %ib3 %s' %Hs'
            iapply R $$ %s'
              %⟨v', v, t3, sdFinalChain t Dr Dw D vs km t0 v' k0 t1 v n va req KKf t2 nw vaw
                reqw KK tw t3 Hts Hts1 He He2 Hep, ib3, Hs'⟩
          · icases R with ⟨-, R⟩
            iintro %ib3 %GD %s1 %Hs1 %Hlen1
            iapply R $$ %GD %s1
              %⟨km, t0, ib0, Hts, .inr ⟨v', k0, t1, ib1, Hts1,
                .inr ⟨v, n, va, req, KKf, t2, nw, vaw, reqw, KK, tw, ibW, He, He2,
                  .inr ⟨t3, ib3, Hep, Hs1⟩⟩⟩⟩ %Hlen1
        · icases R with ⟨-, R⟩
          iintro %GD %s1 %Hs1 %Hlen1
          iapply R $$ %GD %s1
            %⟨km, t0, ib0, Hts, .inr ⟨v', k0, t1, ib1, Hts1,
              .inr ⟨v, n, va, req, KKf, t2, nw, vaw, reqw, KK, tw, ibW, He, He2, .inl Hs1⟩⟩⟩
            %Hlen1
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %Hs1 %Hlen1
      iapply R $$ %GD %s1 %⟨km, t0, ib0, Hts, .inr ⟨v', k0, t1, ib1, Hts1, .inl Hs1⟩⟩ %Hlen1
  · icases R with ⟨-, R⟩
    iintro %GD %s1 %Hs1 %Hlen1
    iapply R $$ %GD %s1 %⟨km, t0, ib0, Hts, .inl Hs1⟩ %Hlen1

/-- The concrete store with the PINNED post: the continuation is owed only at the `.pure ()`
node whose registers ARE `tAfterSd v' v`'s. -/
theorem wpdCsdspConcrete' (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch)
    (kk : Nat)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk (pcSd : Int) sdVs⌝)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜storeRowOk GD i kk⌝) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i kk ls -∗
         storeFlow GD i kk sdData) -∗
      ((∀ v' v s', ⌜RetX cpu (tAfterSd v' v).regs (kk + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜ledgerSdInv (tAt pcSd) AxEpiProbe.drNopin DwAll DPost sdVs cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ib, kk⟩ Φ := by
  show ⊢ _ -∗ _ -∗ wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) (tAt pcSd).regs none ib, kk⟩ Φ
  iintro F R
  iapply (wpdCsdspStepExact i Φ cpu ib kk (tAt pcSd) _ _ _ _ _ _ _ _ epiLedgerCsdsp Hgd Hrow) $$ F
  isplit
  · icases R with ⟨R, -⟩
    iintro %s' %Hs'
    obtain ⟨v', v, Hv⟩ := sdPostExact cpu (kk + 1) s' Hs'
    iapply R $$ %v' %v %s' %Hv
  · icases R with ⟨-, R⟩
    iexact R

end sdExact

/-! # 2. The boundary split from an `aeqv` start and an `rtc` prefix -/

section splitRtc
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem wpdOfSeipSplitRtc (i : Agent) (Φ : Athread → IProp GF) (s s0 n0 : Athread)
    (Qs : Athread → Prop) (Ha : aeqv s s0) (Hrun0 : rtc gstep s0 n0) (Hn0 : n0Ok n0 Qs) :
    ⊢ ((∀ s2, ⌜QaS Qs s2⌝ -∗ wpd .MaybeStuck i s2 Φ) ∧
       (∀ (GD : Gdexec) s1, ⌜Pseip n0 Qs s1⌝ -∗ ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗
          postLifting Φ i s1)) -∗
      wpd .MaybeStuck i s Φ := by
  have HP : Pseip n0 Qs s := by
    rcases rtc_inv Hrun0 with h | ⟨y, hy, hr⟩
    · subst h
      exact .inr (.inl Ha)
    · exact .inl ⟨s0, Ha, tcOfStepRtc hy hr⟩
  exact AxEpiLedger.wpdOfSplitFrom i Φ s n0 Qs HP Hn0

theorem wpdBoundaryErdRtc (i : Agent) (Φ : Athread → IProp GF) (s s0 : Athread) (cpu : CPU)
    (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt) (ib1 : Ibch) (kk : Nat)
    (Dr Dw : List Register)
    (Hseip : Register.sig_seip ∉ Dr) (Hmeip : Register.sig_meip ∉ Dr)
    (Ha : aeqv s s0)
    (Hrun0 : rtc gstep s0 (seipNode cpu k0 t1.regs ib1 kk))
    (Herd : ∀ v, ∃ q t2, erd Dr Dw (k0 v) t1 = some (q, t2)) :
    ⊢ ((∀ s2, ⌜QaS (erdExit Dr Dw cpu k0 t1 kk) s2⌝ -∗ wpd .MaybeStuck i s2 Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜Pseip (seipNode cpu k0 t1.regs ib1 kk) (erdExit Dr Dw cpu k0 t1 kk) s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i s Φ :=
  wpdOfSeipSplitRtc i Φ s s0 _ _ Ha Hrun0
    (AxEpiLedger.seipN0Ok cpu k0 t1 ib1 kk Dr Dw Hseip Hmeip Herd)

/-- `wpdCldspStepOfLedger` from any register file agreeing with the ledger state's off the pins
(the `.pure ()` exit of the previous instruction is only up to `aeqv`). -/
theorem wpdCldspStepOfLedgerAgree (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch)
    (kk : Nat) (t : ExecSt) (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (ldaddr : Int) (postLd : Int → RegFile → Prop) (Rv : Gdexec → List (BitVec 8) → IProp GF)
    (L : AxLdModelFacts t Dr Dw D base vs ldaddr postLd)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk base vs⌝)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i kk⌝)
    (rs : RegFile) (Hag0 : regsAgree AxRunClose.pinReg t.regs rs) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i kk ls -∗
         ⌜graphValue GD (i, kk) = some v⌝ -∗ loadFlow GD i kk (Rv GD v)) -∗
      ((∀ s', ⌜RetLd cpu postLd (kk + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
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
            obtain ⟨sEnd', Hep', Hpost'⟩ := Hx x
            rw [Hep, Option.some.injEq, Prod.mk.injEq] at Hep'
            obtain ⟨-, rfl⟩ := Hep'
            iapply R $$ %s' %⟨_, sEnd.regs, ib3, Hpost', Hs'⟩
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

end splitRtc

/-! # 3. The tick = true ledger -/

def tickRetOk (D : List Register) (post : RegFile → Prop) (m : SailM Unit) (t : ExecSt) : Prop :=
  match epure D m t with
  | some (_, s) => post s.regs
  | none => False

/-- (Lean-only, deviation 1) After the tick's `sig_meip` node `m1` is answered `v'`, the walk
reaches the tick's `sig_seip` node, and both of its answers `epure` to `post`. -/
def AxEpiLedgerTick.tickAfterMeip (D : List Register) (post : RegFile → Prop) (m1 : SailM Unit)
    (t4 : ExecSt) (v' : BitVec 1) : Prop :=
  match AxEpiLedger.toPin (AxEpiLedger.ansMeip m1 v') t4 with
  | some (m2, t5) =>
    isSeipNode m2 = true ∧ tickRetOk D post (ansSeip m2 0#1) t5 ∧
      tickRetOk D post (ansSeip m2 1#1) t5
  | none => False

def tickPostOk (D : List Register) (post : RegFile → Prop) (m : SailM Unit) (t : ExecSt) : Prop :=
  match AxEpiLedger.toPin m t with
  | some (m1, t4) =>
    AxEpiLedger.isMeipNode m1 = true ∧ AxEpiLedgerTick.tickAfterMeip D post m1 t4 0#1 ∧
      AxEpiLedgerTick.tickAfterMeip D post m1 t4 1#1
  | none => False

def ldtLoadOk (D : List Register) (ldaddr : Int) (postLd : Int → RegFile → Prop)
    (ml : SailM Unit) (tl : ExecSt) : Prop :=
  match ml with
  | .impure (.ok (.memRead nl _ reql)) KK =>
    devAddr reql.pa = false ∧ (classify reql.access_kind).akLatest = false ∧
    (classify reql.access_kind).akIfetch = false ∧
    paZ reql.pa = ldaddr ∧ 0 < nl ∧
    ∀ x : BitVec (8 * nl), tickPostOk D (postLd (x.toNat : Int)) (KK (.Ok (x, none))) tl
  | _ => False

def ldtFetchOk (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8)) (ldaddr : Int)
    (postLd : Int → RegFile → Prop) (mf : SailM Unit) (t2 : ExecSt) : Prop :=
  match mf with
  | .impure (.ok (.memRead n _ req)) KKf =>
    devAddr req.pa = false ∧ (classify req.access_kind).akIfetch = true ∧
    paZ req.pa = base ∧ vs.length = n ∧
    match erd Dr Dw (KKf (.Ok (wordOfBytes n vs, none))) t2 with
    | some (ml, tl) => ldtLoadOk D ldaddr postLd ml tl
    | none => False
  | _ => False

def ldtBranchOk (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8)) (ldaddr : Int)
    (postLd : Int → RegFile → Prop) (m : SailM Unit) (t1 : ExecSt) : Prop :=
  match erd Dr Dw m t1 with
  | some (mf, t2) => ldtFetchOk Dr Dw D base vs ldaddr postLd mf t2
  | none => False

/-- The boundary walk of `riscvStep true` (as `seipAt`, deviation 1). -/
noncomputable def seipAtTick (t : ExecSt) : Bool :=
  match AxEpiLedger.toPin (riscvStep true) t with
  | some (m0, t0) =>
    AxEpiLedger.isMeipNode m0 && AxEpiLedger.seipAfter m0 t0 0#1 &&
      AxEpiLedger.seipAfter m0 t0 1#1
  | none => false

noncomputable def ldtBranchAt (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (ldaddr : Int) (postLd : Int → RegFile → Prop) (t : ExecSt) (v' v : BitVec 1) : Prop :=
  match AxEpiLedger.toPin (riscvStep true) t with
  | some (m0, t0) =>
    match AxEpiLedger.toPin (AxEpiLedger.ansMeip m0 v') t0 with
    | some (m1, t1) => ldtBranchOk Dr Dw D base vs ldaddr postLd (ansSeip m1 v) t1
    | none => False
  | none => False

/-- THE TICK LOAD LEDGER. -/
structure AxLdTickFacts (t : ExecSt) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (postLd : Int → RegFile → Prop) : Prop where
  ltSeipDr : decide (Register.sig_seip ∈ Dr) = false
  ltMeipDr : decide (Register.sig_meip ∈ Dr) = false
  ltSeipD : decide (Register.sig_seip ∈ D) = false
  ltMeipD : decide (Register.sig_meip ∈ D) = false
  ltToSeip : seipAtTick t = true
  ltBranch00 : ldtBranchAt Dr Dw D base vs ldaddr postLd t 0#1 0#1
  ltBranch01 : ldtBranchAt Dr Dw D base vs ldaddr postLd t 0#1 1#1
  ltBranch10 : ldtBranchAt Dr Dw D base vs ldaddr postLd t 1#1 0#1
  ltBranch11 : ldtBranchAt Dr Dw D base vs ldaddr postLd t 1#1 1#1

/-! ## Boolean twins of the tick ledger (Lean-only, deviation 5) -/

def AxEpiLedgerTick.tickRetB (D : List Register) (postB : RegFile → Bool) (m : SailM Unit)
    (t : ExecSt) : Bool :=
  match epure D m t with
  | some (_, s) => postB s.regs
  | none => false

def AxEpiLedgerTick.tickAfterMeipB (D : List Register) (postB : RegFile → Bool)
    (m1 : SailM Unit) (t4 : ExecSt) (v' : BitVec 1) : Bool :=
  match AxEpiLedger.toPin (AxEpiLedger.ansMeip m1 v') t4 with
  | some (m2, t5) =>
    isSeipNode m2 && AxEpiLedgerTick.tickRetB D postB (ansSeip m2 0#1) t5 &&
      AxEpiLedgerTick.tickRetB D postB (ansSeip m2 1#1) t5
  | none => false

def AxEpiLedgerTick.tickPostB (D : List Register) (postB : RegFile → Bool) (m : SailM Unit)
    (t : ExecSt) : Bool :=
  match AxEpiLedger.toPin m t with
  | some (m1, t4) =>
    AxEpiLedger.isMeipNode m1 && AxEpiLedgerTick.tickAfterMeipB D postB m1 t4 0#1 &&
      AxEpiLedgerTick.tickAfterMeipB D postB m1 t4 1#1
  | none => false

def AxEpiLedgerTick.ldtLoadB (D : List Register) (ldaddr : Int) (postB : RegFile → Bool)
    (ml : SailM Unit) (tl : ExecSt) (x : BitVec 64) : Bool :=
  match ml with
  | .impure (.ok (.memRead nl _ reql)) KK =>
    !devAddr reql.pa && !(classify reql.access_kind).akLatest &&
    !(classify reql.access_kind).akIfetch && decide (paZ reql.pa = ldaddr) &&
    (if h : nl = 8 then
      AxEpiLedgerTick.tickPostB D postB (KK (.Ok (x.cast (by omega), none))) tl
    else false)
  | _ => false

def AxEpiLedgerTick.ldtFetchB (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (ldaddr : Int) (postB : RegFile → Bool) (mf : SailM Unit) (t2 : ExecSt) (x : BitVec 64) :
    Bool :=
  match mf with
  | .impure (.ok (.memRead n _ req)) KKf =>
    !devAddr req.pa && (classify req.access_kind).akIfetch &&
    decide (paZ req.pa = base) && decide (vs.length = n) &&
    match erd Dr Dw (KKf (.Ok (wordOfBytes n vs, none))) t2 with
    | some (ml, tl) => AxEpiLedgerTick.ldtLoadB D ldaddr postB ml tl x
    | none => false
  | _ => false

def AxEpiLedgerTick.ldtBranchB (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (ldaddr : Int) (postB : RegFile → Bool) (m : SailM Unit) (t1 : ExecSt) (x : BitVec 64) :
    Bool :=
  match erd Dr Dw m t1 with
  | some (mf, t2) => AxEpiLedgerTick.ldtFetchB Dr Dw D base vs ldaddr postB mf t2 x
  | none => false

noncomputable def AxEpiLedgerTick.ldtBranchAtB (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (postB : RegFile → Bool) (t : ExecSt) (v' v : BitVec 1)
    (x : BitVec 64) : Bool :=
  match AxEpiLedger.toPin (riscvStep true) t with
  | some (m0, t0) =>
    match AxEpiLedger.toPin (AxEpiLedger.ansMeip m0 v') t0 with
    | some (m1, t1) =>
      AxEpiLedgerTick.ldtBranchB Dr Dw D base vs ldaddr postB (ansSeip m1 v) t1 x
    | none => false
  | none => false

theorem AxEpiLedgerTick.tickRetOfB (D : List Register) (postB : RegFile → Bool)
    (post : RegFile → Prop) (Hp : ∀ rs, postB rs = true → post rs) (m : SailM Unit)
    (t : ExecSt) (H : AxEpiLedgerTick.tickRetB D postB m t = true) : tickRetOk D post m t := by
  unfold AxEpiLedgerTick.tickRetB at H
  unfold tickRetOk
  cases he : epure D m t with
  | none => rw [he] at H; exact absurd H Bool.false_ne_true
  | some p =>
    obtain ⟨u, s⟩ := p
    rw [he] at H
    exact Hp _ H

theorem AxEpiLedgerTick.tickAfterMeipOfB (D : List Register) (postB : RegFile → Bool)
    (post : RegFile → Prop) (Hp : ∀ rs, postB rs = true → post rs) (m1 : SailM Unit)
    (t4 : ExecSt) (v' : BitVec 1)
    (H : AxEpiLedgerTick.tickAfterMeipB D postB m1 t4 v' = true) :
    AxEpiLedgerTick.tickAfterMeip D post m1 t4 v' := by
  unfold AxEpiLedgerTick.tickAfterMeipB at H
  unfold AxEpiLedgerTick.tickAfterMeip
  cases he : AxEpiLedger.toPin (AxEpiLedger.ansMeip m1 v') t4 with
  | none => rw [he] at H; exact absurd H Bool.false_ne_true
  | some p =>
    obtain ⟨m2, t5⟩ := p
    rw [he] at H
    simp only [Bool.and_eq_true] at H
    obtain ⟨⟨h1, h2⟩, h3⟩ := H
    exact ⟨h1, AxEpiLedgerTick.tickRetOfB D postB post Hp _ t5 h2,
      AxEpiLedgerTick.tickRetOfB D postB post Hp _ t5 h3⟩

theorem AxEpiLedgerTick.tickPostOfB (D : List Register) (postB : RegFile → Bool)
    (post : RegFile → Prop) (Hp : ∀ rs, postB rs = true → post rs) (m : SailM Unit)
    (t : ExecSt) (H : AxEpiLedgerTick.tickPostB D postB m t = true) : tickPostOk D post m t := by
  unfold AxEpiLedgerTick.tickPostB at H
  unfold tickPostOk
  cases he : AxEpiLedger.toPin m t with
  | none => rw [he] at H; exact absurd H Bool.false_ne_true
  | some p =>
    obtain ⟨m1, t4⟩ := p
    rw [he] at H
    simp only [Bool.and_eq_true] at H
    obtain ⟨⟨h1, h2⟩, h3⟩ := H
    exact ⟨h1, AxEpiLedgerTick.tickAfterMeipOfB D postB post Hp _ t4 _ h2,
      AxEpiLedgerTick.tickAfterMeipOfB D postB post Hp _ t4 _ h3⟩

theorem AxEpiLedgerTick.ldtLoadOfB (D : List Register) (ldaddr : Int) (postB : RegFile → Bool)
    (postLd : Int → RegFile → Prop) (Hp : ∀ z rs, postB rs = true → postLd z rs)
    (ml : SailM Unit) (tl : ExecSt)
    (H : ∀ x : BitVec 64, AxEpiLedgerTick.ldtLoadB D ldaddr postB ml tl x = true) :
    ldtLoadOk D ldaddr postLd ml tl := by
  cases ml with
  | pure _ => exact absurd (H 0) Bool.false_ne_true
  | impure call KK =>
    cases call with
    | error _ => exact absurd (H 0) Bool.false_ne_true
    | ok o =>
      cases o
      case memRead nl va reql =>
        have h0 := H 0
        simp only [AxEpiLedgerTick.ldtLoadB, Bool.and_eq_true, Bool.not_eq_true',
          decide_eq_true_eq] at h0
        obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h0
        by_cases hn : nl = 8
        · subst hn
          simp only [ldtLoadOk]
          refine ⟨h1, h2, h3, h4, by omega, fun x => ?_⟩
          have hx := H (x.cast (by omega))
          simp only [AxEpiLedgerTick.ldtLoadB, dite_true, BitVec.cast_eq,
            Bool.and_eq_true] at hx
          exact AxEpiLedgerTick.tickPostOfB D postB _ (Hp _) _ tl hx.2
        · simp only [hn, dite_false] at h5
          exact absurd h5 Bool.false_ne_true
      all_goals exact absurd (H 0) Bool.false_ne_true

theorem AxEpiLedgerTick.ldtFetchOfB (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (postB : RegFile → Bool)
    (postLd : Int → RegFile → Prop) (Hp : ∀ z rs, postB rs = true → postLd z rs)
    (mf : SailM Unit) (t2 : ExecSt)
    (H : ∀ x : BitVec 64, AxEpiLedgerTick.ldtFetchB Dr Dw D base vs ldaddr postB mf t2 x = true) :
    ldtFetchOk Dr Dw D base vs ldaddr postLd mf t2 := by
  cases mf with
  | pure _ => exact absurd (H 0) Bool.false_ne_true
  | impure call KKf =>
    cases call with
    | error _ => exact absurd (H 0) Bool.false_ne_true
    | ok o =>
      cases o
      case memRead n va req =>
        cases he : erd Dr Dw (KKf (.Ok (wordOfBytes n vs, none))) t2 with
        | none =>
          have h0 := H 0
          simp only [AxEpiLedgerTick.ldtFetchB, he, Bool.and_false] at h0
          exact absurd h0 Bool.false_ne_true
        | some p =>
          obtain ⟨ml, tl⟩ := p
          have h0 := H 0
          simp only [AxEpiLedgerTick.ldtFetchB, he, Bool.and_eq_true, Bool.not_eq_true',
            decide_eq_true_eq] at h0
          obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩ := h0
          simp only [ldtFetchOk, he]
          refine ⟨h1, h2, h3, h4, AxEpiLedgerTick.ldtLoadOfB D ldaddr postB postLd Hp ml tl
            (fun x => ?_)⟩
          have hx := H x
          simp only [AxEpiLedgerTick.ldtFetchB, he, Bool.and_eq_true] at hx
          exact hx.2
      all_goals exact absurd (H 0) Bool.false_ne_true

theorem AxEpiLedgerTick.ldtBranchOfB (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (postB : RegFile → Bool)
    (postLd : Int → RegFile → Prop) (Hp : ∀ z rs, postB rs = true → postLd z rs)
    (m : SailM Unit) (t1 : ExecSt)
    (H : ∀ x : BitVec 64, AxEpiLedgerTick.ldtBranchB Dr Dw D base vs ldaddr postB m t1 x = true) :
    ldtBranchOk Dr Dw D base vs ldaddr postLd m t1 := by
  unfold ldtBranchOk
  cases he : erd Dr Dw m t1 with
  | none =>
    have h0 := H 0
    simp only [AxEpiLedgerTick.ldtBranchB, he] at h0
    exact absurd h0 Bool.false_ne_true
  | some p =>
    obtain ⟨mf, t2⟩ := p
    refine AxEpiLedgerTick.ldtFetchOfB Dr Dw D base vs ldaddr postB postLd Hp mf t2
      (fun x => ?_)
    have hx := H x
    simp only [AxEpiLedgerTick.ldtBranchB, he] at hx
    exact hx

theorem AxEpiLedgerTick.ldtBranchAtOfB (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (postB : RegFile → Bool)
    (postLd : Int → RegFile → Prop) (Hp : ∀ z rs, postB rs = true → postLd z rs) (t : ExecSt)
    (v' v : BitVec 1)
    (H : ∀ x : BitVec 64,
      AxEpiLedgerTick.ldtBranchAtB Dr Dw D base vs ldaddr postB t v' v x = true) :
    ldtBranchAt Dr Dw D base vs ldaddr postLd t v' v := by
  unfold ldtBranchAt
  cases h1 : AxEpiLedger.toPin (riscvStep true) t with
  | none =>
    have h0 := H 0
    simp only [AxEpiLedgerTick.ldtBranchAtB, h1] at h0
    exact absurd h0 Bool.false_ne_true
  | some p =>
    obtain ⟨m0, t0⟩ := p
    dsimp only
    cases h2 : AxEpiLedger.toPin (AxEpiLedger.ansMeip m0 v') t0 with
    | none =>
      have h0 := H 0
      simp only [AxEpiLedgerTick.ldtBranchAtB, h1, h2] at h0
      exact absurd h0 Bool.false_ne_true
    | some p2 =>
      obtain ⟨m1, t1⟩ := p2
      dsimp only
      refine AxEpiLedgerTick.ldtBranchOfB Dr Dw D base vs ldaddr postB postLd Hp _ t1
        (fun x => ?_)
      have hx := H x
      simp only [AxEpiLedgerTick.ldtBranchAtB, h1, h2] at hx
      exact hx

/-! ## Pure bridges of the tick ledger -/

/-- (Lean-only) The walk to the tick's `sig_meip` node `km1` continues, after either answer,
to the tick's `sig_seip` node. -/
theorem AxEpiLedgerTick.tickPostOkNext (D : List Register) (post : RegFile → Prop)
    (m : SailM Unit) (tl : ExecSt) (km1 : RegisterType Register.sig_meip → SailM Unit)
    (t4 : ExecSt)
    (Hts : AxEpiLedger.toPin m tl = some (.impure (.ok (.regRead Register.sig_meip)) km1, t4))
    (Hok : tickPostOk D post m tl) (v' : BitVec 1) :
    ∃ (k1 : RegisterType Register.sig_seip → SailM Unit) (t5 : ExecSt),
      AxEpiLedger.toPin (km1 v') t4 = some (.impure (.ok (.regRead Register.sig_seip)) k1, t5) := by
  unfold tickPostOk at Hok
  rw [Hts] at Hok
  obtain ⟨-, H0, H1⟩ := Hok
  have Hv : AxEpiLedgerTick.tickAfterMeip D post
      (.impure (.ok (.regRead Register.sig_meip)) km1) t4 v' := by
    rcases bv1Cases v' with rfl | rfl
    · exact H0
    · exact H1
  unfold AxEpiLedgerTick.tickAfterMeip at Hv
  rw [AxEpiLedger.ansMeipNode] at Hv
  cases h : AxEpiLedger.toPin (km1 v') t4 with
  | none => rw [h] at Hv; exact Hv.elim
  | some p =>
    obtain ⟨m2, t5⟩ := p
    rw [h] at Hv
    obtain ⟨k1, rfl⟩ := isSeipNodeShape m2 Hv.1
    exact ⟨k1, t5, rfl⟩

theorem tickPostOkAt (D : List Register) (post : RegFile → Prop) (m : SailM Unit) (tl : ExecSt)
    (km1 : RegisterType Register.sig_meip → SailM Unit) (t4 : ExecSt) (v' : BitVec 1)
    (k1 : RegisterType Register.sig_seip → SailM Unit) (t5 : ExecSt) :
    AxEpiLedger.toPin m tl = some (.impure (.ok (.regRead Register.sig_meip)) km1, t4) →
    AxEpiLedger.toPin (km1 v') t4 = some (.impure (.ok (.regRead Register.sig_seip)) k1, t5) →
    tickPostOk D post m tl →
    ∀ v, ∃ t6 : ExecSt, epure D (k1 v) t5 = some ((), t6) ∧ post t6.regs := by
  intro Hts Hts1 Hok v
  unfold tickPostOk at Hok
  rw [Hts] at Hok
  obtain ⟨-, H0, H1⟩ := Hok
  have Hv : AxEpiLedgerTick.tickAfterMeip D post
      (.impure (.ok (.regRead Register.sig_meip)) km1) t4 v' := by
    rcases bv1Cases v' with rfl | rfl
    · exact H0
    · exact H1
  unfold AxEpiLedgerTick.tickAfterMeip at Hv
  rw [AxEpiLedger.ansMeipNode, Hts1] at Hv
  obtain ⟨-, R0, R1⟩ := Hv
  have Hr : tickRetOk D post (k1 v) t5 := by
    rcases bv1Cases v with rfl | rfl
    · rw [ansSeipNode] at R0; exact R0
    · rw [ansSeipNode] at R1; exact R1
  unfold tickRetOk at Hr
  cases he : epure D (k1 v) t5 with
  | none => rw [he] at Hr; exact Hr.elim
  | some p =>
    obtain ⟨⟨⟩, t6⟩ := p
    rw [he] at Hr
    exact ⟨t6, rfl, Hr⟩

theorem tickPostOkShape (D : List Register) (post : RegFile → Prop) (m : SailM Unit)
    (tl : ExecSt) :
    tickPostOk D post m tl →
    ∃ (km1 : RegisterType Register.sig_meip → SailM Unit) (t4 : ExecSt),
      AxEpiLedger.toPin m tl = some (.impure (.ok (.regRead Register.sig_meip)) km1, t4) := by
  intro H
  unfold tickPostOk at H
  cases h : AxEpiLedger.toPin m tl with
  | none => rw [h] at H; exact H.elim
  | some p =>
    obtain ⟨m1, t4⟩ := p
    rw [h] at H
    obtain ⟨km1, rfl⟩ := AxEpiLedger.isMeipNodeShape m1 H.1
    exact ⟨km1, t4, rfl⟩

theorem ldtLoadOkNode (D : List Register) (ldaddr : Int) (postLd : Int → RegFile → Prop)
    (nl val : Nat) (reql : Mem_read_request nl val Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * nl) × Option Bool) Arch.abort → SailM Unit) (tl : ExecSt) :
    ldtLoadOk D ldaddr postLd (.impure (.ok (.memRead nl val reql)) KK) tl →
    devAddr reql.pa = false ∧ (classify reql.access_kind).akLatest = false ∧
    (classify reql.access_kind).akIfetch = false ∧ paZ reql.pa = ldaddr ∧ 0 < nl ∧
    ∀ x : BitVec (8 * nl), tickPostOk D (postLd (x.toNat : Int)) (KK (.Ok (x, none))) tl := by
  intro H
  simp only [ldtLoadOk] at H
  exact H

theorem ldtFetchOkNode (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (ldaddr : Int) (postLd : Int → RegFile → Prop) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KKf : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (t2 : ExecSt) :
    ldtFetchOk Dr Dw D base vs ldaddr postLd (.impure (.ok (.memRead n va req)) KKf) t2 →
    devAddr req.pa = false ∧ (classify req.access_kind).akIfetch = true ∧
    paZ req.pa = base ∧ vs.length = n ∧
    ∃ (nl val : Nat) (reql : Mem_read_request nl val Arch.pa Arch.translation Arch.arch_ak)
      (KK : Result (BitVec (8 * nl) × Option Bool) Arch.abort → SailM Unit) (tl : ExecSt),
      erd Dr Dw (KKf (.Ok (wordOfBytes n vs, none))) t2
        = some (.impure (.ok (.memRead nl val reql)) KK, tl) ∧
      ldtLoadOk D ldaddr postLd (.impure (.ok (.memRead nl val reql)) KK) tl := by
  intro H
  simp only [ldtFetchOk] at H
  obtain ⟨h1, h2, h3, h4, hl⟩ := H
  refine ⟨h1, h2, h3, h4, ?_⟩
  cases he : erd Dr Dw (KKf (.Ok (wordOfBytes n vs, none))) t2 with
  | none => rw [he] at hl; exact hl.elim
  | some p =>
    obtain ⟨ml, tl⟩ := p
    rw [he] at hl
    cases ml with
    | pure _ => exact (hl : False).elim
    | impure call KK =>
      cases call with
      | error _ => exact (hl : False).elim
      | ok o =>
        cases o
        case memRead nl val reql => exact ⟨nl, val, reql, KK, tl, rfl, hl⟩
        all_goals exact (hl : False).elim

theorem ldtBranchOkNode (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (ldaddr : Int) (postLd : Int → RegFile → Prop) (m : SailM Unit) (t1 : ExecSt) :
    ldtBranchOk Dr Dw D base vs ldaddr postLd m t1 →
    ∃ (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (KKf : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (t2 : ExecSt),
      erd Dr Dw m t1 = some (.impure (.ok (.memRead n va req)) KKf, t2) ∧
      ldtFetchOk Dr Dw D base vs ldaddr postLd (.impure (.ok (.memRead n va req)) KKf) t2 := by
  intro H
  unfold ldtBranchOk at H
  cases he : erd Dr Dw m t1 with
  | none => rw [he] at H; exact H.elim
  | some p =>
    obtain ⟨mf, t2⟩ := p
    rw [he] at H
    cases mf with
    | pure _ => exact (H : False).elim
    | impure call KKf =>
      cases call with
      | error _ => exact (H : False).elim
      | ok o =>
        cases o
        case memRead n va req => exact ⟨n, va, req, KKf, t2, rfl, H⟩
        all_goals exact (H : False).elim

/-- (Lean-only) `ldtBranchOk` gives the `erd` exit. -/
theorem AxEpiLedgerTick.erdOfLdtBranch (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (postLd : Int → RegFile → Prop) (m : SailM Unit)
    (t1 : ExecSt) (Hb : ldtBranchOk Dr Dw D base vs ldaddr postLd m t1) :
    ∃ q t2, erd Dr Dw m t1 = some (q, t2) := by
  obtain ⟨_, _, _, _, _, He, _⟩ := ldtBranchOkNode _ _ _ _ _ _ _ _ _ Hb
  exact ⟨_, _, He⟩

/-- (Lean-only) The `seipAtTick` walk: the first pin node is the `sig_meip` read. -/
theorem AxEpiLedgerTick.seipAtTickSpec (t : ExecSt) (H : seipAtTick t = true) :
    ∃ (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt),
      AxEpiLedger.toPin (riscvStep true) t
        = some (.impure (.ok (.regRead Register.sig_meip)) km, t0) := by
  unfold seipAtTick at H
  cases h : AxEpiLedger.toPin (riscvStep true) t with
  | none => rw [h] at H; exact absurd H Bool.false_ne_true
  | some p =>
    obtain ⟨m0, t0⟩ := p
    rw [h] at H
    simp only [Bool.and_eq_true] at H
    obtain ⟨km, rfl⟩ := AxEpiLedger.isMeipNodeShape m0 H.1.1
    exact ⟨km, t0, rfl⟩

/-- (Lean-only) The `seipAtTick` walk: after either `sig_meip` answer, the `sig_seip` node. -/
theorem AxEpiLedgerTick.seipAtTickNext (t : ExecSt)
    (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt) (H : seipAtTick t = true)
    (Hts : AxEpiLedger.toPin (riscvStep true) t
      = some (.impure (.ok (.regRead Register.sig_meip)) km, t0)) (v' : BitVec 1) :
    ∃ (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt),
      AxEpiLedger.toPin (km v') t0
        = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) := by
  unfold seipAtTick at H
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

/-- (Lean-only) `ldtBranchAt` at the two computed pin nodes. -/
theorem AxEpiLedgerTick.ldtBranchAtEq (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (postLd : Int → RegFile → Prop) (t : ExecSt)
    (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt) (v' : BitVec 1)
    (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt) (v : BitVec 1)
    (Hts : AxEpiLedger.toPin (riscvStep true) t
      = some (.impure (.ok (.regRead Register.sig_meip)) km, t0))
    (Hts1 : AxEpiLedger.toPin (km v') t0
      = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1)) :
    ldtBranchAt Dr Dw D base vs ldaddr postLd t v' v =
      ldtBranchOk Dr Dw D base vs ldaddr postLd (k0 v) t1 := by
  unfold ldtBranchAt
  rw [Hts]
  simp only []
  rw [AxEpiLedger.ansMeipNode, Hts1]
  simp only []
  rw [AxEpiLedger.ansSeipNode]

/-! ## The post-load tail: `gstep`s to the tick's pin reads, then per answer an `epure` run to
`.pure ()` -/

def RetP (cpu : CPU) (post : RegFile → Prop) (k : Nat) (s : Athread) : Prop :=
  ∃ (rs3 : RegFile) (ib' : Ibch), post rs3 ∧ Qat ⟨.PHart cpu (.pure ()) rs3 none ib', k⟩ s

def tickExit (D : List Register) (cpu : CPU) (k1 : RegisterType Register.sig_seip → SailM Unit)
    (t4 : ExecSt) (k : Nat) (q : Athread) : Prop :=
  ∃ (v : BitVec 1) (t5 : ExecSt) (ib5 : Ibch), epure D (k1 v) t4 = some ((), t5) ∧
    q = ⟨.PHart cpu (.pure ()) t5.regs none ib5, k⟩

/-- The tail's reachable invariant: the split sets at the tick's two pin nodes. -/
def tickTailInv (D : List Register) (cpu : CPU) (m : SailM Unit) (tl : ExecSt) (k : Nat)
    (s1 : Athread) : Prop :=
  ∃ (km1 : RegisterType Register.sig_meip → SailM Unit) (t4 : ExecSt) (ib4 : Ibch),
    AxEpiLedger.toPin m tl = some (.impure (.ok (.regRead Register.sig_meip)) km1, t4) ∧
    (Pseip (AxEpiLedger.meipNode cpu km1 t4.regs ib4 k) (AxEpiLedger.seipExit cpu km1 t4 k) s1 ∨
     ∃ (v' : BitVec 1) (k1 : RegisterType Register.sig_seip → SailM Unit) (t5 : ExecSt)
       (ib5 : Ibch),
       AxEpiLedger.toPin (km1 v') t4 = some (.impure (.ok (.regRead Register.sig_seip)) k1, t5) ∧
       Pseip (seipNode cpu k1 t5.regs ib5 k) (tickExit D cpu k1 t5 k) s1)

/-- The tick load's row-end invariant. -/
def ledgerLdtInv (t : ExecSt) (Dr Dw D : List Register) (vs : List (BitVec 8)) (cpu : CPU)
    (kk : Nat) (s1 : Athread) : Prop :=
  ∃ (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt) (ib0 : Ibch),
    AxEpiLedger.toPin (riscvStep true) t
      = some (.impure (.ok (.regRead Register.sig_meip)) km, t0) ∧
    (Pseip (AxEpiLedger.meipNode cpu km t0.regs ib0 kk) (AxEpiLedger.seipExit cpu km t0 kk) s1 ∨
     ∃ (v' : BitVec 1) (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt)
       (ib1 : Ibch),
       AxEpiLedger.toPin (km v') t0 = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) ∧
       (Pseip (seipNode cpu k0 t1.regs ib1 kk) (erdExit Dr Dw cpu k0 t1 kk) s1 ∨
        ∃ (v : BitVec 1) (n va : Nat)
          (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
          (KKf : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (t2 : ExecSt)
          (nl val : Nat) (reql : Mem_read_request nl val Arch.pa Arch.translation Arch.arch_ak)
          (KK : Result (BitVec (8 * nl) × Option Bool) Arch.abort → SailM Unit) (tl : ExecSt)
          (ibLd : Ibch),
          erd Dr Dw (k0 v) t1 = some (.impure (.ok (.memRead n va req)) KKf, t2) ∧
          erd Dr Dw (KKf (.Ok (wordOfBytes n vs, none))) t2
            = some (.impure (.ok (.memRead nl val reql)) KK, tl) ∧
          (Pbefore ⟨.PHart cpu (.impure (.ok (.memRead nl val reql)) KK) tl.regs none ibLd, kk⟩
              s1 ∨
           ∃ x : BitVec (8 * nl), tickTailInv D cpu (KK (.Ok (x, none))) tl (kk + 1) s1)))

/-! ## Sanity: the invariants reach `.pure ()` -/

theorem tailFromSeip (D : List Register) (post : RegFile → Prop) (cpu : CPU)
    (vs : List (BitVec 8)) (k1 : RegisterType Register.sig_seip → SailM Unit) (t5 : ExecSt)
    (ib5 : Ibch) (k : Nat) :
    Register.sig_seip ∉ D → Register.sig_meip ∉ D →
    (∀ v, ∃ t6 : ExecSt, epure D (k1 v) t5 = some ((), t6) ∧ post t6.regs) →
    ∃ s', rtc (ldStep cpu vs) (seipNode cpu k1 t5.regs ib5 k) s' ∧ RetP cpu post k s' := by
  intro HD HDm Hk1
  obtain ⟨t6, Hep, Hp⟩ := Hk1 0#1
  obtain ⟨ib6, Hr⟩ := epureGstepRtc D HD HDm _ _ _ _ Hep cpu (ibRd ib5 Register.sig_seip) k
  exact ⟨_, rtc_l (.inl (.inr (.inl ⟨k1, t5.regs, ib5, 0#1, _, k, rfl, rfl⟩)))
    (rtcGstepLdStep cpu vs _ _ Hr), t6.regs, ib6, Hp, aeqvHartRefl ..⟩

/-- (Lean-only) From the tick's `sig_meip` node, `RetP` is reached. -/
theorem AxEpiLedgerTick.tailFromMeip (D : List Register) (post : RegFile → Prop) (cpu : CPU)
    (vs : List (BitVec 8)) (km1 : RegisterType Register.sig_meip → SailM Unit) (t4 : ExecSt)
    (ib4 : Ibch) (k : Nat) (HD : Register.sig_seip ∉ D) (HDm : Register.sig_meip ∉ D)
    (H : ∀ v', ∃ (k1 : RegisterType Register.sig_seip → SailM Unit) (t5 : ExecSt),
      AxEpiLedger.toPin (km1 v') t4
        = some (.impure (.ok (.regRead Register.sig_seip)) k1, t5) ∧
      ∀ v, ∃ t6 : ExecSt, epure D (k1 v) t5 = some ((), t6) ∧ post t6.regs) :
    ∃ s', rtc (ldStep cpu vs) (AxEpiLedger.meipNode cpu km1 t4.regs ib4 k) s' ∧
      RetP cpu post k s' := by
  obtain ⟨k1, t5, Hts1, Hk1⟩ := H 0#1
  obtain ⟨ib5, Hr⟩ := AxEpiLedger.toPinGstep _ t4 (ibRd ib4 Register.sig_meip) _ _ Hts1 cpu k
  obtain ⟨s', Hr', Hs'⟩ := tailFromSeip D post cpu vs k1 t5 ib5 k HD HDm Hk1
  exact ⟨s', rtc_l (.inl (.inr (.inr (.inr ⟨km1, t4.regs, ib4, 0#1, _, k, rfl, rfl⟩))))
    (rtc_transitive (rtcGstepLdStep cpu vs _ _ Hr) Hr'), Hs'⟩

/-- (Lean-only) The per-meip-answer facts `tailFromMeip` consumes, from `tickPostOk`. -/
theorem AxEpiLedgerTick.tickPostOkAll (D : List Register) (post : RegFile → Prop)
    (m : SailM Unit) (tl : ExecSt) (km1 : RegisterType Register.sig_meip → SailM Unit)
    (t4 : ExecSt)
    (Hts : AxEpiLedger.toPin m tl = some (.impure (.ok (.regRead Register.sig_meip)) km1, t4))
    (Hok : tickPostOk D post m tl) :
    ∀ v', ∃ (k1 : RegisterType Register.sig_seip → SailM Unit) (t5 : ExecSt),
      AxEpiLedger.toPin (km1 v') t4
        = some (.impure (.ok (.regRead Register.sig_seip)) k1, t5) ∧
      ∀ v, ∃ t6 : ExecSt, epure D (k1 v) t5 = some ((), t6) ∧ post t6.regs := by
  intro v'
  obtain ⟨k1, t5, Hts1⟩ := AxEpiLedgerTick.tickPostOkNext D post m tl km1 t4 Hts Hok v'
  exact ⟨k1, t5, Hts1, tickPostOkAt D post m tl km1 t4 v' k1 t5 Hts Hts1 Hok⟩

theorem tailReachesStart (D : List Register) (post : RegFile → Prop) (cpu : CPU)
    (vs : List (BitVec 8)) (m : SailM Unit) (tl : ExecSt) (ib : Ibch) (k : Nat) :
    Register.sig_seip ∉ D → Register.sig_meip ∉ D → tickPostOk D post m tl →
    ∃ s', rtc (ldStep cpu vs) ⟨.PHart cpu m tl.regs none ib, k⟩ s' ∧ RetP cpu post k s' := by
  intro HD HDm Hok
  obtain ⟨km1, t4, Hts⟩ := tickPostOkShape D post m tl Hok
  obtain ⟨ib4, Hr⟩ := AxEpiLedger.toPinGstep m tl ib _ _ Hts cpu k
  obtain ⟨s', Hr', Hs'⟩ := AxEpiLedgerTick.tailFromMeip D post cpu vs km1 t4 ib4 k HD HDm
    (AxEpiLedgerTick.tickPostOkAll D post m tl km1 t4 Hts Hok)
  exact ⟨s', rtc_transitive (rtcGstepLdStep cpu vs _ _ Hr) Hr', Hs'⟩

theorem tailReachesInv (D : List Register) (post : RegFile → Prop) (cpu : CPU)
    (vs : List (BitVec 8)) (m : SailM Unit) (tl : ExecSt) (k : Nat) (s1 : Athread) :
    Register.sig_seip ∉ D → Register.sig_meip ∉ D → tickPostOk D post m tl →
    tickTailInv D cpu m tl k s1 →
    ∃ t0 s', aeqv s1 t0 ∧ rtc (ldStep cpu vs) t0 s' ∧ RetP cpu post k s' := by
  intro HD HDm Hok ⟨km1, t4, ib4, Hts, Hc⟩
  have Hall := AxEpiLedgerTick.tickPostOkAll D post m tl km1 t4 Hts Hok
  rcases Hc with Hc | ⟨v', k1, t5, ib5, Hts1, Hc⟩
  · obtain ⟨sm, Hrm, Hsm⟩ :=
      AxEpiLedgerTick.tailFromMeip D post cpu vs km1 t4 ib4 k HD HDm Hall
    rcases Hc with ⟨t', Ha, Htc⟩ | Ha | ⟨q, ⟨v', k1, t5, ib5, Hts1, rfl⟩, t', Ha, Htc⟩
    · exact ⟨t', sm, Ha, rtc_transitive (rtcGstepLdStep cpu vs _ _ (tc_rtc Htc)) Hrm, Hsm⟩
    · exact ⟨_, sm, Ha, Hrm, Hsm⟩
    · obtain ⟨s', Hr, Hs'⟩ := tailFromSeip D post cpu vs k1 t5 ib5 k HD HDm
        (tickPostOkAt D post m tl km1 t4 v' k1 t5 Hts Hts1 Hok)
      exact ⟨t', s', Ha, rtc_transitive (rtcGstepLdStep cpu vs _ _ (tc_rtc Htc)) Hr, Hs'⟩
  · have Hk1 := tickPostOkAt D post m tl km1 t4 v' k1 t5 Hts Hts1 Hok
    obtain ⟨ss, Hrs, Hss⟩ := tailFromSeip D post cpu vs k1 t5 ib5 k HD HDm Hk1
    rcases Hc with ⟨t', Ha, Htc⟩ | Ha | ⟨q, ⟨v, t6, ib6, Hep, rfl⟩, t', Ha, Htc⟩
    · exact ⟨t', ss, Ha, rtc_transitive (rtcGstepLdStep cpu vs _ _ (tc_rtc Htc)) Hrs, Hss⟩
    · exact ⟨_, ss, Ha, Hrs, Hss⟩
    · obtain ⟨t6', Hep', Hp⟩ := Hk1 v
      rw [Hep, Option.some.injEq, Prod.mk.injEq] at Hep'
      obtain ⟨-, rfl⟩ := Hep'
      exact ⟨t', _, Ha, rtcGstepLdStep cpu vs _ _ (tc_rtc Htc), t6.regs, ib6, Hp,
        aeqvHartRefl ..⟩

theorem ldtLoadReaches (D : List Register) (ldaddr : Int) (postLd : Int → RegFile → Prop)
    (cpu : CPU) (vs : List (BitVec 8)) (nl val : Nat)
    (reql : Mem_read_request nl val Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * nl) × Option Bool) Arch.abort → SailM Unit) (tl : ExecSt)
    (ib : Ibch) (k : Nat) :
    Register.sig_seip ∉ D → Register.sig_meip ∉ D →
    ldtLoadOk D ldaddr postLd (.impure (.ok (.memRead nl val reql)) KK) tl →
    ∃ s', rtc (ldStep cpu vs)
        ⟨.PHart cpu (.impure (.ok (.memRead nl val reql)) KK) tl.regs none ib, k⟩ s' ∧
      RetLd cpu postLd (k + 1) s' := by
  intro HD HDm H
  obtain ⟨-, -, -, -, -, Hx⟩ := ldtLoadOkNode _ _ _ _ _ _ _ _ H
  obtain ⟨s', Hr, rs3, ib', Hp, Hq⟩ :=
    tailReachesStart D _ cpu vs _ tl ib (k + 1) HD HDm (Hx (BitVec.ofNat (8 * nl) 0))
  exact ⟨s', rtc_l (.inr ⟨nl, val, reql, KK, tl.regs, ib, ib, k, _, rfl, rfl⟩) Hr,
    _, rs3, ib', Hp, Hq⟩

theorem ldtFetchReaches (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (ldaddr : Int) (postLd : Int → RegFile → Prop) (cpu : CPU) (kk n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KKf : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (t2 : ExecSt)
    (ib2 : Ibch) :
    Register.sig_seip ∉ Dr → Register.sig_meip ∉ Dr →
    Register.sig_seip ∉ D → Register.sig_meip ∉ D →
    ldtFetchOk Dr Dw D base vs ldaddr postLd (.impure (.ok (.memRead n va req)) KKf) t2 →
    ∃ s', rtc (ldStep cpu vs)
        ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KKf) t2.regs none ib2, kk⟩ s' ∧
      RetLd cpu postLd (kk + 1) s' := by
  intro HDr HDrm HD HDm H
  obtain ⟨-, -, -, -, nl, val, reql, KK, tl, He2, Hl⟩ :=
    ldtFetchOkNode _ _ _ _ _ _ _ _ _ _ _ _ H
  obtain ⟨ibLd, -, -, Hr⟩ := erdGstep Dr Dw _ HDr HDrm t2 ib2 _ _ He2 cpu kk
  obtain ⟨s', Hr', Hs'⟩ :=
    ldtLoadReaches D ldaddr postLd cpu vs nl val reql KK tl ibLd kk HD HDm Hl
  exact ⟨s', rtc_l (.inl (.inr (.inr (.inl ⟨n, va, req, KKf, t2.regs, ib2, ib2, kk, rfl, rfl⟩))))
    (rtc_transitive (rtcGstepLdStep cpu vs _ _ Hr) Hr'), Hs'⟩

theorem ldtBranchReaches (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (ldaddr : Int) (postLd : Int → RegFile → Prop) (cpu : CPU) (kk : Nat) (m : SailM Unit)
    (t1 : ExecSt) (ib : Ibch) :
    Register.sig_seip ∉ Dr → Register.sig_meip ∉ Dr →
    Register.sig_seip ∉ D → Register.sig_meip ∉ D →
    ldtBranchOk Dr Dw D base vs ldaddr postLd m t1 →
    ∃ s', rtc (ldStep cpu vs) ⟨.PHart cpu m t1.regs none ib, kk⟩ s' ∧
      RetLd cpu postLd (kk + 1) s' := by
  intro HDr HDrm HD HDm Hb
  obtain ⟨n, va, req, KKf, t2, He, Hf⟩ := ldtBranchOkNode _ _ _ _ _ _ _ _ _ Hb
  obtain ⟨ib2, -, -, Hr⟩ := erdGstep Dr Dw m HDr HDrm t1 ib _ _ He cpu kk
  obtain ⟨s', Hr', Hs'⟩ :=
    ldtFetchReaches Dr Dw D base vs ldaddr postLd cpu kk n va req KKf t2 ib2 HDr HDrm HD HDm Hf
  exact ⟨s', rtc_transitive (rtcGstepLdStep cpu vs _ _ Hr) Hr', Hs'⟩

theorem ldtLedgerBranch (t : ExecSt) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (postLd : Int → RegFile → Prop)
    (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt) (v' : BitVec 1)
    (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt) :
    AxLdTickFacts t Dr Dw D base vs ldaddr postLd →
    AxEpiLedger.toPin (riscvStep true) t
      = some (.impure (.ok (.regRead Register.sig_meip)) km, t0) →
    AxEpiLedger.toPin (km v') t0
      = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) →
    ∀ v, ldtBranchOk Dr Dw D base vs ldaddr postLd (k0 v) t1 := by
  intro L Hts Hts1 v
  rw [← AxEpiLedgerTick.ldtBranchAtEq Dr Dw D base vs ldaddr postLd t km t0 v' k0 t1 v Hts Hts1]
  rcases bv1Cases v' with rfl | rfl <;> rcases bv1Cases v with rfl | rfl
  · exact L.ltBranch00
  · exact L.ltBranch01
  · exact L.ltBranch10
  · exact L.ltBranch11

/-- (Lean-only) From the boundary `sig_seip` node of a certified tick branch, `RetLd`. -/
theorem AxEpiLedgerTick.ldtSeipReaches (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (postLd : Int → RegFile → Prop) (cpu : CPU)
    (kk : Nat) (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt) (ib1 : Ibch)
    (HDr : Register.sig_seip ∉ Dr) (HDrm : Register.sig_meip ∉ Dr)
    (HD : Register.sig_seip ∉ D) (HDm : Register.sig_meip ∉ D)
    (Hb : ∀ v, ldtBranchOk Dr Dw D base vs ldaddr postLd (k0 v) t1) :
    ∃ s', rtc (ldStep cpu vs) (seipNode cpu k0 t1.regs ib1 kk) s' ∧
      RetLd cpu postLd (kk + 1) s' := by
  obtain ⟨s', Hr, Hs'⟩ := ldtBranchReaches Dr Dw D base vs ldaddr postLd cpu kk (k0 0#1) t1
    (ibRd ib1 Register.sig_seip) HDr HDrm HD HDm (Hb _)
  exact ⟨s', rtc_l (.inl (.inr (.inl ⟨k0, t1.regs, ib1, 0#1, _, kk, rfl, rfl⟩))) Hr, Hs'⟩

/-- (Lean-only) From the boundary `sig_meip` node of a certified tick ledger, `RetLd`. -/
theorem AxEpiLedgerTick.ldtMeipReaches (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (postLd : Int → RegFile → Prop) (cpu : CPU)
    (kk : Nat) (km : RegisterType Register.sig_meip → SailM Unit) (t0 : ExecSt) (ib0 : Ibch)
    (HDr : Register.sig_seip ∉ Dr) (HDrm : Register.sig_meip ∉ Dr)
    (HD : Register.sig_seip ∉ D) (HDm : Register.sig_meip ∉ D)
    (H : ∀ v', ∃ (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt),
      AxEpiLedger.toPin (km v') t0
        = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) ∧
      ∀ v, ldtBranchOk Dr Dw D base vs ldaddr postLd (k0 v) t1) :
    ∃ s', rtc (ldStep cpu vs) (AxEpiLedger.meipNode cpu km t0.regs ib0 kk) s' ∧
      RetLd cpu postLd (kk + 1) s' := by
  obtain ⟨k0, t1, Hts1, Hb⟩ := H 0#1
  obtain ⟨ib1, Hr⟩ := AxEpiLedger.toPinGstep _ t0 (ibRd ib0 Register.sig_meip) _ _ Hts1 cpu kk
  obtain ⟨s', Hr', Hs'⟩ := AxEpiLedgerTick.ldtSeipReaches Dr Dw D base vs ldaddr postLd cpu kk
    k0 t1 ib1 HDr HDrm HD HDm Hb
  exact ⟨s', rtc_l (.inl (.inr (.inr (.inr ⟨km, t0.regs, ib0, 0#1, _, kk, rfl, rfl⟩))))
    (rtc_transitive (rtcGstepLdStep cpu vs _ _ Hr) Hr'), Hs'⟩

/-- SANITY (non-vacuity of the tick load's row-end premise). -/
theorem ledgerLdtInvReachesRet (t : ExecSt) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (postLd : Int → RegFile → Prop) (cpu : CPU)
    (kk : Nat) (s1 : Athread) :
    AxLdTickFacts t Dr Dw D base vs ldaddr postLd →
    ledgerLdtInv t Dr Dw D vs cpu kk s1 →
    ∃ t0 s', aeqv s1 t0 ∧ rtc (ldStep cpu vs) t0 s' ∧ RetLd cpu postLd (kk + 1) s' := by
  intro L ⟨km, t0, ib0, Hts, Hc⟩
  have HDr := of_decide_eq_false L.ltSeipDr
  have HDrm := of_decide_eq_false L.ltMeipDr
  have HD := of_decide_eq_false L.ltSeipD
  have HDm := of_decide_eq_false L.ltMeipD
  have Hall : ∀ v', ∃ (k0 : RegisterType Register.sig_seip → SailM Unit) (t1 : ExecSt),
      AxEpiLedger.toPin (km v') t0
        = some (.impure (.ok (.regRead Register.sig_seip)) k0, t1) ∧
      ∀ v, ldtBranchOk Dr Dw D base vs ldaddr postLd (k0 v) t1 := by
    intro v'
    obtain ⟨k0, t1, Hts1⟩ := AxEpiLedgerTick.seipAtTickNext t km t0 L.ltToSeip Hts v'
    exact ⟨k0, t1, Hts1, ldtLedgerBranch t Dr Dw D base vs ldaddr postLd km t0 v' k0 t1 L Hts
      Hts1⟩
  rcases Hc with Hc | ⟨v', k0, t1, ib1, Hts1, Hc⟩
  · obtain ⟨sm, Hrm, Hsm⟩ :=
      AxEpiLedgerTick.ldtMeipReaches Dr Dw D base vs ldaddr postLd cpu kk km t0 ib0 HDr HDrm HD
        HDm Hall
    rcases Hc with ⟨t', Ha, Htc⟩ | Ha | ⟨q, ⟨v', k0, t1, ib1, Hts1, rfl⟩, t', Ha, Htc⟩
    · exact ⟨t', sm, Ha, rtc_transitive (rtcGstepLdStep cpu vs _ _ (tc_rtc Htc)) Hrm, Hsm⟩
    · exact ⟨_, sm, Ha, Hrm, Hsm⟩
    · have Hb := ldtLedgerBranch t Dr Dw D base vs ldaddr postLd km t0 v' k0 t1 L Hts Hts1
      obtain ⟨s', Hr, Hs'⟩ := AxEpiLedgerTick.ldtSeipReaches Dr Dw D base vs ldaddr postLd cpu
        kk k0 t1 ib1 HDr HDrm HD HDm Hb
      exact ⟨t', s', Ha, rtc_transitive (rtcGstepLdStep cpu vs _ _ (tc_rtc Htc)) Hr, Hs'⟩
  · have Hb := ldtLedgerBranch t Dr Dw D base vs ldaddr postLd km t0 v' k0 t1 L Hts Hts1
    obtain ⟨ss, Hrs, Hss⟩ := AxEpiLedgerTick.ldtSeipReaches Dr Dw D base vs ldaddr postLd cpu
      kk k0 t1 ib1 HDr HDrm HD HDm Hb
    rcases Hc with Hc | ⟨v, n, va, req, KKf, t2, nl, val, reql, KK, tl, ibLd, He, He2, Hc⟩
    · rcases Hc with ⟨t', Ha, Htc⟩ | Ha | ⟨q, ⟨v, qm, t2, ib2, He, rfl, -⟩, t', Ha, Htc⟩
      · exact ⟨t', ss, Ha, rtc_transitive (rtcGstepLdStep cpu vs _ _ (tc_rtc Htc)) Hrs, Hss⟩
      · exact ⟨_, ss, Ha, Hrs, Hss⟩
      · obtain ⟨n, va, req, KKf, t2', He', Hf⟩ := ldtBranchOkNode _ _ _ _ _ _ _ _ _ (Hb v)
        rw [He, Option.some.injEq, Prod.mk.injEq] at He'
        obtain ⟨rfl, rfl⟩ := He'
        obtain ⟨s', Hr, Hs'⟩ :=
          ldtFetchReaches Dr Dw D base vs ldaddr postLd cpu kk n va req KKf t2 ib2 HDr HDrm HD
            HDm Hf
        exact ⟨t', s', Ha, rtc_transitive (rtcGstepLdStep cpu vs _ _ (tc_rtc Htc)) Hr, Hs'⟩
    · have Hl : ldtLoadOk D ldaddr postLd (.impure (.ok (.memRead nl val reql)) KK) tl := by
        have Hbv := Hb v
        unfold ldtBranchOk at Hbv
        rw [He] at Hbv
        simp only [ldtFetchOk] at Hbv
        rw [He2] at Hbv
        exact Hbv.2.2.2.2
      rcases Hc with ⟨t', Ha, Htc⟩ | ⟨x, Htail⟩
      · obtain ⟨s', Hr, Hs'⟩ := ldtLoadReaches D ldaddr postLd cpu vs nl val reql KK tl ibLd kk
          HD HDm Hl
        exact ⟨t', s', Ha, rtc_transitive (rtcGstepLdStep cpu vs _ _ (tc_rtc Htc)) Hr, Hs'⟩
      · obtain ⟨-, -, -, -, -, Hx⟩ := ldtLoadOkNode _ _ _ _ _ _ _ _ Hl
        obtain ⟨t', s', Ha, Hr, rs3, ib', Hp, Hq⟩ :=
          tailReachesInv D _ cpu vs _ tl (kk + 1) s1 HD HDm (Hx x) Htail
        exact ⟨t', s', Ha, Hr, _, rs3, ib', Hp, Hq⟩

/-! # 4. The tick = true composition -/

section ldtLedger
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- Post-load: `gstep`s (`toPin`) to the tick's `sig_meip` node, split there, then at each
tick `sig_seip` node, split again; per answer the `epure` run to `.pure ()`. -/
theorem wpdTickTail (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (m : SailM Unit)
    (tl : ExecSt) (ib : Ibch) (k : Nat) (D : List Register) (post : RegFile → Prop)
    (HD : Register.sig_seip ∉ D) (HDm : Register.sig_meip ∉ D) (Hok : tickPostOk D post m tl)
    (rs : RegFile) (Hag : regsAgree AxRunClose.pinReg tl.regs rs) :
    ⊢ ((∀ s', ⌜RetP cpu post k s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
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
      obtain ⟨t6', Hep', Hp⟩ := Hk1 v
      rw [Hep, Option.some.injEq, Prod.mk.injEq] at Hep'
      obtain ⟨-, rfl⟩ := Hep'
      iapply R $$ %s3 %⟨t6.regs, ib6, Hp, Hq3⟩
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %Hs1 %Hl
      iapply R $$ %GD %s1 %⟨km1, t4, ib4, Hts, .inr ⟨v', k1, t5, ib5, Hts1, Hs1⟩⟩ %Hl
  · icases R with ⟨-, R⟩
    iintro %GD %s1 %Hs1 %Hl
    iapply R $$ %GD %s1 %⟨km1, t4, ib4, Hts, .inl Hs1⟩ %Hl

/-- The data load node, then the split tail, for every loaded word. -/
theorem wpdLoadThenTick (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (nl va : Nat)
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
      ((∀ s', ⌜RetLd cpu postLd (k + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
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
    iapply (wpdTickTail i Φ cpu _ sLd ib (k + 1) D _ HD HDm (Hx (wordOfBytes nl v)) rs' hag')
    isplit
    · icases R with ⟨R, -⟩
      iintro %s' %Hs'
      obtain ⟨rs3, ib', Hp, Hq'⟩ := Hs'
      iapply R $$ %s' %⟨_, rs3, ib', Hp, Hq'⟩
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %Hs1 %Hl
      iapply R $$ %(wordOfBytes nl v) %GD %s1 %Hs1 %Hl

/-- Fetch (any width, bytes `vs`) → pre-load `gstep` run → the data load → the split tail. -/
theorem wpdFetchThenLoadTick (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (n va : Nat)
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
      (((∀ s', ⌜RetLd cpu postLd (k + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
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
    iapply (wpdLoadThenTick Φ i cpu nl val reql KK ibLd k tl D postLd Rv Hdevl Hlatl Hn Hnfl
      Hrow HD HDm Hx) $$ %s3 %Hq3 F R
  · icases R with ⟨-, R⟩
    iexact R

/-- THE WHOLE-INSTRUCTION `wpd` OF A DATA LOAD AT `riscvStep true`, from any register file
agreeing with the ledger state's off the pins. -/
theorem wpdCldspStepOfLedgerTick (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch)
    (kk : Nat) (t : ExecSt) (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (ldaddr : Int) (postLd : Int → RegFile → Prop) (Rv : Gdexec → List (BitVec 8) → IProp GF)
    (L : AxLdTickFacts t Dr Dw D base vs ldaddr postLd)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk base vs⌝)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i kk⌝)
    (rs : RegFile) (Hag0 : regsAgree AxRunClose.pinReg t.regs rs) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i kk ls -∗
         ⌜graphValue GD (i, kk) = some v⌝ -∗ loadFlow GD i kk (Rv GD v)) -∗
      ((∀ s', ⌜RetLd cpu postLd (kk + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
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
        iapply (wpdFetchThenLoadTick Φ i cpu n va req KKf ib2 kk vs t2.regs rs3 nl val reql KK
          ibLd tl D postLd Rv Hdev Hfe Hlen Hgd (regsAgreeSym _ _ _ hag) HrunPre Hdevl Hlatl Hn
          Hnfl Hrow HD HDm Hx) $$ F
        isplit
        · isplit
          · icases R with ⟨R, -⟩
            iexact R
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

end ldtLedger

end Weak
