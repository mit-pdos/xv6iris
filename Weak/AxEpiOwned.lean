/-
Weak: **the one-hart `wpd` for the concrete `c.sdsp ; c.ldsp` program at the REAL ownership
protocol**, the reload's annotation carrying `⌜v = sdData⌝` (the reload value IS the spilled
bytes).

Rocq: `iris/AxEpiOwned.v` @ xxvzwolszwmp.

## The Rocq header, in substance

THE HANDOFF (Finding F2 of `AxLdspWpd`): the spill's write rule deposits the byte tokens in the
SPILL's own annotation; the reload pulls them as `flowIn` via `annotDetach`, which needs the
fragment `annotOwn (i, kk) Rsd`.  That fragment is produced by `annotAlloc` INSIDE the store's
flow (after the store step), so it cannot be an upfront thread resource.  §1 restates the store
chain of `AxEpiLedgerSd`/`AxEpiLedgerTick`/`AxEpiChainSdLd` with a resource-carrying store flow
`storeFlowRes GD i k data X`: the flow RETURNS `X` to the thread, and the load flow is supplied
as `X -∗ (load flow)`.

THE DEPOSIT `sdTok`: `tokn γ GD ..` mentions `GD` only in `tokTie`'s pure tie fact, which for a
freshly-written history (`writenHist w ..`, last entry `w`) holds at EVERY graph (`tieWrite`).
So the spill deposits the GD-free `sdTok` (the per-byte `tok`s), and the reload re-ties it at its
own `GD` (`sdTokTokn`) — no cross-`GD` agreement premise needed.

§1 `storeFlowRes`, `wpdStoreStepRes` .. `wpdEpiSdLdRes` (generic `AxirisG`/`Axpol`).
§2 `storeFlowOwned` (the spill's flow at the real protocol) and the capstone `wpdEpiSdLdOwned`.

## Deviations from Rocq

1. O2 STAGE C (`AxEpiLedgerSd` deviation 3, `AxEpiChainSdLd` deviation 1): the fetches are
   pinned admin steps with no row item.  The row is `[sd @kk; ld @kk + 1]`:
   - `wpdFetchThenStoreRes` follows Lean `wpdFetchThenStore`: the fetch, the pre-store run and
     the store all sit at `k`, the `.pure ()` at `k + 1` (Rocq `S k` / `S (S k)`); `Hlat` of the
     fetch ↦ `Hfe : akIfetch = true`; `Hgd` states `AxCjrWpd.fetchImgOk`; the fetch's
     `Hflow`/`Hloc` are DROPPED; `Hrow`/`F` at `k` (Rocq `S k`).
   - `wpdCsdspStepExactRes`/`wpdCsdspConcreteRes`/`wpdEpiSdLdRes`/`wpdEpiSdLdOwned`: the store's
     `Hrow_sd`, flow `F`, `Hw_sd`, `Hloc_st` at `kk` (Rocq `S kk`); the store's exit
     `SdRetX`/`RetX` at `kk + 1` (Rocq `S (S kk)`); the load's `Hgd_ld`/`Hrow_ld`/flow/`Hok_ld`
     at `kk + 1` (Rocq fetch `S (S kk)`, load `S (S (S kk))`), the reload's `Hloc_ldv` from
     `kk + 1` to `kk + 2`; the spill event is `(i, kk)` (Rocq `(i, S kk)`); `Hlen` is
     `length = kk + 2` (Rocq `kk + 4`).  `Hflow_sd`, `Hloc_sd`, `Hflow_ld`, `Hloc_ld` and
     `Hntext` are DROPPED (the callees no longer take them).
2. THE TWO-PIN BOUNDARY (`AxEpiLedger` deviation 1): `wpdCsdspStepExactRes` is
   `wpdCsdspStepExact` (two pin splits; `SdRetX` indexed by both answers); the store's
   continuation in `wpdCsdspConcreteRes` is `X -∗ ∀ v' v s', …` (Rocq `∀ v s'`).
3. THE PINS (`AxRunClose` deviation 1): `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg`;
   `wpdStoreThenRetRes`/`wpdFetchThenStoreRes` take both `sig_seip ∉ D` and `sig_meip ∉ D`.
4. TYPES (as `AxEpiLedgerSd` deviation 5): the request types carry the bound `va`; the write's
   answer `inl None` ↦ `.Ok (some true)`; Rocq's `wbytes nw (WriteReq.value reqw) = data` ↦
   `reqw.value.map (WeakInterpProj.wbytes nw) = some data`; `Ret tt` ↦ `.pure ()`; `S k` ↦
   `k + 1`; `WPd … @ MaybeStuck; i {{ Φ }}` ↦ `wpd .MaybeStuck i s Φ`; `invGS_gen HasNoLc Σ` ↦
   `[InvGS_gen hlc GF]`; `A -∗ B` ↦ `⊢ A -∗ B`; `(i, k) ↦ₐ P` ↦ `AxAnnot.annotOwn (i, k) P`;
   `Z.of_nat j` ↦ `(j : Int)`; `stdpp.list_basics.last H` ↦ `H.getLast?`; `Vs !!! j` (inside
   `writenHist`) ↦ `Vs.getD j 0`.  §2 is at `GF : BundledGFunctors.{0,0,0}` (`AxannotGS`).
5. §2's section context `γ`, `Hob_eq`, `Hann_eq` are explicit arguments (as `AxLdspWpd`
   deviation 4), each lemma taking only what it uses: `sdTok`, `toknSdTok`, `sdTokTokn`,
   `ownTokTieAfterWriteSnap`, `ownBigSepLReindex` take `γ` only (and no `AxirisG`/`Axpol`);
   `ownFlowEqWritenSnap` takes `Hob_eq` (Rocq `Proof using Hob_eq Hann_eq`; `Hann_eq` unused);
   `storeFlowOwned`/`wpdEpiSdLdOwned` take both.
6. The three "local copies" (`own_tok_tie_after_write_snap`, `own_big_sepL_reindex`,
   `own_flow_eq_writen_snap`) existed in Rocq only because the originals' section captured a
   read-oracle context spuriously.  The Lean originals (`tokTieAfterWriteSnap`,
   `bigSepLReindex`, `flowEqOwnedWritenChainSnap` in `AxProtBytes`) do not, so the copies are
   ported as one-line instances of them (same statements as Rocq's copies).

**Rocq → Lean name map.**  `store_flow_res` `storeFlowRes`, `wpd_store_step_res`
`wpdStoreStepRes`, `wpd_store_then_ret_res` `wpdStoreThenRetRes`, `wpd_fetch_then_store_res`
`wpdFetchThenStoreRes`, `wpd_csdsp_step_exact_res` `wpdCsdspStepExactRes`,
`wpd_csdsp_concrete_res` `wpdCsdspConcreteRes`, `wpd_epi_sd_ld_res` `wpdEpiSdLdRes`,
`sd_write_ok` `sdWriteOk`, `sd_data_length` `sdDataLength`, `writen_hist_last_spill`
`writenHistLastSpill`, `sd_tok` `sdTok`, `tokn_sd_tok` `toknSdTok`, `sd_tok_tokn` `sdTokTokn`,
`own_tok_tie_after_write_snap` `ownTokTieAfterWriteSnap`, `own_big_sepL_reindex`
`ownBigSepLReindex`, `own_flow_eq_writen_snap` `ownFlowEqWritenSnap`, `store_flow_owned`
`storeFlowOwned`, `wpd_epi_sd_ld_owned` `wpdEpiSdLdOwned`.  None is in the duplicated-name table.

**Dropped:** nothing (Rocq 18 definitions/lemmas; Lean 18).  **Not ported:** the
`Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxEpiChainSdLd
import Weak.AxLdspWpd
import Weak.AxProtBytes

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Wlabel

/-! # 1. THE RESOURCE-CARRYING STORE CHAIN -/

section res
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- `storeFlow` that additionally hands `X` back to the thread. -/
def storeFlowRes (GD : Gdexec) (i : Agent) (k : Nat) (data : List (BitVec 8)) (X : IProp GF) :
    IProp GF :=
  iprop(∀ na, naAtProgress GD i k na ∗ AxirisG.annotInterp na -∗ |==> ▷ |==>
    ∃ (R : IProp GF) (naUsed naUnused : Mea GF) (ls' : AxirisG.logTsT GF),
      naSplittingWf (Axpol.lobp GD (i, k)) na naUsed naUnused ∗
      flowEqDyn GD (i, k) (Axpol.sPol GD (i, k)) naUsed iprop(R ∗ ⌜graphData GD (i, k) = some data⌝) ∗
      AxirisG.annotInterp (PartialMap.union (PartialMap.union {[(i, k) := R]} naUnused) na) ∗
      AxirisG.localInterp GD i (k + 1) ls' ∗ X)

theorem wpdStoreStepRes (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat) (rs0 : RegFile)
    (data : List (BitVec 8)) (X : IProp GF)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hdata : req.value.map (WeakInterpProj.wbytes n) = some data)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜storeRowOk GD i k⌝) :
    ⊢ ∀ rs, ⌜regsAgree AxRunClose.pinReg rs0 rs⌝ -∗
      (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
         storeFlowRes GD i k data X) -∗
      (X -∗ ∀ rs', ⌜regsAgree AxRunClose.pinReg rs0 rs'⌝ -∗
         wpd .MaybeStuck i ⟨.PHart cpu (KK (.Ok (some true))) rs' none ib, k + 1⟩ Φ) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memWrite n va req)) KK) rs none ib, k⟩ Φ := by
  unfold storeFlowRes
  iloeb as IH
  iintro %rs %HP F C
  iapply (AxWpD.wpdMUnfoldStep rvwmoCatConsistent .MaybeStuck i _ Φ).2
  isplit
  · iapply (progressOblMaybestuck (GF := GF) i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
  ihave Hok := (Hrow GD Hc) $$ Hg
  icases Hok with %Hok
  obtain ⟨lb0, Hlb0⟩ := Hok
  isplit
  · -- (a) no read at a store node
    iintro %id %K %Hst
    exact (AxEpiLedgerSd.storeNoRead _ cpu n va req KK rs ib k id K Hdev Hlat Hst).elim
  isplit
  · -- (b) THE WRITE: `AStepWrite` only
    iintro %l %s' %Hst %Hpin
    obtain ⟨v, hv, rfl, rfl⟩ :=
      AxEpiLedgerSd.storeAstepInv _ cpu n va req KK rs ib k l s' Hdev Hlat Hst
    have hd : WeakInterpProj.wbytes n v = data := by
      rw [hv] at Hdata
      exact Option.some.inj Hdata
    subst hd
    simp only [wlWdata]
    unfold wpEvStep
    iintro %na Hpg
    ihave Hf := F $$ %GD %ls %Hc Hg Hloc
    imod Hf $$ %na Hpg with Hf
    imodintro
    inext
    imod Hf with ⟨%R, %nu, %nuu, %ls', Hs, Hfe, Hna, Hl, HX⟩
    imodintro
    iexists (), R, nu, nuu, ls'
    isplitr
    · ipureintro
      trivial
    iframe Hs Hfe Hna Hl
    iapply C $$ HX %rs %HP
  isplit
  · -- (c) the PLIC wire: back to the store node, Löb
    iintro %s' %Hw
    obtain ⟨hk, hp⟩ := awireAeqv _ _ Hw
    obtain ⟨p', k'⟩ := s'
    simp only at hk hp
    subst hk
    match p', hp with
    | .PHart c m' rs' fn' ib', hp =>
      obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := hp
      unfold wpSkipStep
      iintro %na Hna
      imodintro
      inext
      imodintro
      iexists ls
      iframe Hna Hloc
      iapply IH $$ %rs' %(regsAgreeTrans _ _ _ _ HP (regsAgreeSym _ _ _ hag)) F C
  · -- (d) row end: the store item sits at `k`
    iintro %Heq
    have h1 := lookup_lt_Some Hlb0
    simp only at Heq
    omega

theorem wpdStoreThenRetRes (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat) (sW : ExecSt)
    (D : List Register) (data : List (BitVec 8)) (sEnd : ExecSt) (X : IProp GF)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hdata : req.value.map (WeakInterpProj.wbytes n) = some data)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜storeRowOk GD i k⌝)
    (Hseip : Register.sig_seip ∉ D) (Hmeip : Register.sig_meip ∉ D)
    (Hep : epure D (KK (.Ok (some true))) sW = some ((), sEnd)) :
    ⊢ ∀ s2, ⌜Qat ⟨.PHart cpu (.impure (.ok (.memWrite n va req)) KK) sW.regs none ib, k⟩ s2⌝ -∗
      (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
         storeFlowRes GD i k data X) -∗
      ((X -∗ ∀ (ib' : Ibch) (s' : Athread),
          ⌜Qat ⟨.PHart cpu (.pure ()) sEnd.regs none ib', k + 1⟩ s'⌝ -∗
          wpd .MaybeStuck i s' Φ) ∧
       (∀ (ib' : Ibch) (GD : Gdexec) (s1 : Athread),
          ⌜Pbefore ⟨.PHart cpu (.pure ()) sEnd.regs none ib', k + 1⟩ s1⌝ -∗
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
    iapply (wpdStoreStepRes Φ i cpu n va req KK ib k sW.regs data X Hdev Hlat Hdata Hrow) $$
      %rs2 %(regsAgreeSym _ _ _ hag) F
    iintro HX %rs' %hag'
    obtain ⟨ib', Hrun⟩ := epureGstepRtc D Hseip Hmeip _ _ _ _ Hep cpu ib (k + 1)
    iapply (wpdRunTo Φ i _ _ Hrun) $$
      %⟨.PHart cpu (KK (.Ok (some true))) rs' none ib, k + 1⟩
      %⟨rfl, rfl, rfl, rfl, rfl, regsAgreeSym _ _ _ hag'⟩
    isplit
    · icases R with ⟨R, -⟩
      iintro %s3 %Hq3
      iapply R $$ HX %ib' %s3 %Hq3
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %Hb %Hend
      iapply R $$ %ib' %GD %s1 %Hb %Hend

theorem wpdFetchThenStoreRes (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KKf : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (vs : List (BitVec 8)) (rs0 rs : RegFile) (nw vaw : Nat)
    (reqw : Mem_write_request nw vaw Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (ibW : Ibch) (tw : ExecSt)
    (D : List Register) (data : List (BitVec 8)) (sEnd : ExecSt) (X : IProp GF)
    (Hdev : devAddr req.pa = false) (Hfe : (classify req.access_kind).akIfetch = true)
    (Hlen : vs.length = n)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i k (paZ req.pa) vs⌝)
    (Hag : regsAgree AxRunClose.pinReg rs0 rs)
    (HrunPre : rtc gstep
      ⟨.PHart cpu (KKf (.Ok (wordOfBytes n vs, none))) rs0 none ib, k⟩
      ⟨.PHart cpu (.impure (.ok (.memWrite nw vaw reqw)) KK) tw.regs none ibW, k⟩)
    (Hdevw : devAddr reqw.pa = false) (Hlatw : (classify reqw.access_kind).akLatest = false)
    (Hdata : reqw.value.map (WeakInterpProj.wbytes nw) = some data)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜storeRowOk GD i k⌝)
    (Hseip : Register.sig_seip ∉ D) (Hmeip : Register.sig_meip ∉ D)
    (Hep : epure D (KK (.Ok (some true))) tw = some ((), sEnd)) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
         storeFlowRes GD i k data X) -∗
      (((X -∗ ∀ (ib' : Ibch) (s' : Athread),
           ⌜Qat ⟨.PHart cpu (.pure ()) sEnd.regs none ib', k + 1⟩ s'⌝ -∗
           wpd .MaybeStuck i s' Φ) ∧
        (∀ (ib' : Ibch) (GD : Gdexec) (s1 : Athread),
           ⌜Pbefore ⟨.PHart cpu (.pure ()) sEnd.regs none ib', k + 1⟩ s1⌝ -∗
           ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) ∧
       (∀ (GD : Gdexec) (s1 : Athread),
          ⌜Pbefore ⟨.PHart cpu (.impure (.ok (.memWrite nw vaw reqw)) KK) tw.regs none ibW, k⟩
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
    iapply (wpdStoreThenRetRes Φ i cpu nw vaw reqw KK ibW k tw D data sEnd X Hdevw Hlatw Hdata
      Hrow Hseip Hmeip Hep) $$ %s3 %Hq3 F R
  · icases R with ⟨-, R⟩
    iexact R

/-- `wpdCsdspStepExact` with the store flow returning `X`. -/
theorem wpdCsdspStepExactRes (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch)
    (kk : Nat) (t : ExecSt) (Dr Dw D : List Register) (base : Int) (vs : List (BitVec 8))
    (staddr : Int) (data : List (BitVec 8)) (post : RegFile → Bool) (X : IProp GF)
    (L : AxSdModelFacts t Dr Dw D base vs staddr data post)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk base vs⌝)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜storeRowOk GD i kk⌝) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i kk ls -∗
         storeFlowRes GD i kk data X) -∗
      ((X -∗ ∀ s', ⌜SdRetX t Dr Dw D vs cpu (kk + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
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
        iapply (wpdFetchThenStoreRes Φ i cpu n va req KKf ib2 kk vs t2.regs rs3 nw vaw reqw KK
          ibW tw D data t3 X Hdev Hfe Hlen Hgd (regsAgreeSym _ _ _ hag) HrunPre Hdevw Hlatw
          Hdataw Hrow HD HDm Hep) $$ F
        isplit
        · isplit
          · icases R with ⟨R, -⟩
            iintro HX %ib3 %s' %Hs'
            iapply R $$ HX %s'
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

theorem wpdCsdspConcreteRes (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch)
    (kk : Nat) (X : IProp GF)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk (pcSd : Int) sdVs⌝)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜storeRowOk GD i kk⌝) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i kk ls -∗
         storeFlowRes GD i kk sdData X) -∗
      ((X -∗ ∀ v' v s', ⌜RetX cpu (tAfterSd v' v).regs (kk + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜ledgerSdInv (tAt pcSd) AxEpiProbe.drNopin DwAll DPost sdVs cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ib, kk⟩ Φ := by
  show ⊢ _ -∗ _ -∗ wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) (tAt pcSd).regs none ib, kk⟩ Φ
  iintro F R
  iapply (wpdCsdspStepExactRes i Φ cpu ib kk (tAt pcSd) _ _ _ _ _ _ _ _ X epiLedgerCsdsp Hgd
    Hrow) $$ F
  isplit
  · icases R with ⟨R, -⟩
    iintro HX %s' %Hs'
    obtain ⟨v', v, Hv⟩ := sdPostExact cpu (kk + 1) s' Hs'
    iapply R $$ HX %v' %v %s' %Hv
  · icases R with ⟨-, R⟩
    iexact R

/-- `wpdEpiSdLd` with the store flow returning `X` and the load flow supplied from `X`. -/
theorem wpdEpiSdLdRes (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch) (kk : Nat)
    (Rv : Gdexec → List (BitVec 8) → IProp GF) (X : IProp GF)
    -- c.sdsp: the store at `kk`
    (Hgd_sd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk (pcSd : Int) sdVs⌝)
    (Hrow_sd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜storeRowOk GD i kk⌝)
    -- c.ldsp: the load at `kk + 1`
    (Hgd_ld : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢
        ⌜AxCjrWpd.fetchImgOk GD i (kk + 1) (pcLd : Int) AxEpiLedger.ldVs⌝)
    (Hrow_ld : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i (kk + 1)⌝)
    -- the row is EXACTLY these two events
    (Hlen : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜(AxOpsem.grow GD i).length = kk + 2⌝) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i kk ls -∗
         storeFlowRes GD i kk sdData X) -∗
      (X -∗ ∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (w : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗
         AxirisG.localInterp GD i (kk + 1) ls -∗
         ⌜graphValue GD (i, kk + 1) = some w⌝ -∗ loadFlow GD i (kk + 1) (Rv GD w)) -∗
      (∀ (GD : Gdexec) s1, ⌜epiSdLdInv cpu kk s1⌝ -∗
         ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ib, kk⟩ Φ := by
  have HlenLe : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜(AxOpsem.grow GD i).length ≤ kk + 2⌝ := by
    intro GD Hc
    refine (Hlen GD Hc).trans ?_
    iintro %h
    ipureintro
    omega
  have HE : ∀ s0, RetLd cpu ldPost (kk + 2) s0 → s0.atK = kk + 2 := by
    rintro s0 ⟨x, rs3, ib', -, Hk, -⟩
    exact Hk
  iintro Fs Fl R
  iapply (wpdCsdspConcreteRes i Φ cpu ib kk X Hgd_sd Hrow_sd) $$ Fs
  isplit
  · iintro HX %v' %v %s' %Hs'
    iapply (wpdRetBoundary i Φ cpu _ (kk + 1) (kk + 2) s' Hs' Hlen (by omega))
    iintro %s2 %Hs2
    obtain ⟨tick, rs', Hag, rfl⟩ := Hs2
    ihave Fl2 := Fl $$ HX
    iapply (wpdCldspAfterSd i Φ cpu ibNone (kk + 1) v' v Rv Hgd_ld Hrow_ld tick rs' Hag) $$ Fl2
    isplit
    · iintro %s3 %Hs3
      iapply (wpdPastRowEnd i Φ (RetLd cpu ldPost (kk + 2)) (kk + 2) s3 Hs3 HE HlenLe)
      iintro %GD %s1 %Hp %Heq
      iapply R $$ %GD %s1 %(Or.inr (Or.inr Hp)) %Heq
    · iintro %GD %s1 %Hs1 %Heq
      iapply R $$ %GD %s1 %(Or.inr (Or.inl ⟨tick, v', v, Hs1⟩)) %Heq
  · iintro %GD %s1 %Hs1 %Heq
    iapply R $$ %GD %s1 %(Or.inl Hs1) %Heq

end res

/-! # 2. AT THE REAL OWNERSHIP PROTOCOL -/

/-- The spill's pure write facts at `(i, k)`: a write, whose bytes are exactly `sdData` at
`a .. a + 7`, with graph data `sdData`. -/
def sdWriteOk (GD : Gdexec) (i : Agent) (k : Nat) (a : Int) : Prop :=
  gisW GD.gdG (i, k) = true ∧
  (∀ a' v', gwritesByte GD.gdG (i, k) a' v' →
     ∃ j : Nat, sdData[j]? = some v' ∧ a' = a + (j : Int)) ∧
  graphData GD (i, k) = some sdData

theorem sdDataLength : sdData.length = 8 := rfl

/-- The spill history list's last entries are the spill's own bytes. -/
theorem writenHistLastSpill (w : Geid) (Vs : List (BitVec 8)) (Hs0 : List (List Hent)) :
    Hs0.length = Vs.length →
    ∀ (j : Nat) (H : List Hent), (writenHist w Vs Hs0)[j]? = some H →
      ∃ v, H.getLast? = some (w, v) ∧ Vs[j]? = some v := by
  intro Hl j H hH
  obtain ⟨H0, h0, rfl⟩ := AxProtBytes.writenHistLookupInv w Vs Hs0 j H hH
  have hj : j < Vs.length := Hl ▸ (List.getElem?_eq_some_iff.1 h0).1
  refine ⟨Vs.getD j 0, List.getLast?_concat, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

section tokSec
variable {GF : BundledGFunctors} [AxlogG GF Hent]

/-- The GD-free deposit: per-byte singleton tokens of the spill `w`. -/
def sdTok (γ : GName) (a : Int) (Hs : List (List Hent)) (w : Geid) : IProp GF :=
  iprop([∗list] j ↦ H ∈ Hs, tok γ (a + (j : Int)) H ({[w := (1 : Qp)]} : GMapF Geid Qp))

theorem toknSdTok (γ : GName) (GD : Gdexec) (a : Int) (Hs : List (List Hent)) (w : Geid) :
    tokn (GF := GF) γ GD a Hs ({[w := (1 : Qp)]} : GMapF Geid Qp) ⊢ sdTok γ a Hs w := by
  unfold tokn sdTok
  exact BigSepL.bigSepL_mono fun {j H} _ => tokTieTok GD γ (a + (j : Int)) H _

/-- Re-tying at ANY graph: the tie of a freshly-written history is graph-independent
(`tieWrite`). -/
theorem sdTokTokn (γ : GName) (GD : Gdexec) (a : Int) (Hs0 : List (List Hent)) (w : Geid)
    (Vs : List (BitVec 8)) :
    sdTok (GF := GF) γ a (writenHist w Vs Hs0) w ⊢
      tokn γ GD a (writenHist w Vs Hs0) ({[w := (1 : Qp)]} : GMapF Geid Qp) := by
  unfold tokn sdTok
  refine BigSepL.bigSepL_mono fun {j H} hk => ?_
  obtain ⟨H0, -, rfl⟩ := AxProtBytes.writenHistLookupInv w Vs Hs0 j H hk
  unfold tokTie
  iintro Ht
  isplitl [Ht]
  · iexact Ht
  · ipureintro
    intro e he
    rw [domSingleton, elemOfSingleton] at he
    subst he
    exact tieWrite GD.gdG H0 e _

/-- Local copy of `AxProtBytes.tok_tie_after_write_snap` (deviation 6). -/
theorem ownTokTieAfterWriteSnap (γ : GName) (GD : Gdexec) (a' : Int) (Hl : List Hent) (w : Geid)
    (v : BitVec 8) :
    histAuth (GF := GF) γ a' 1 Hl ⊢
      |==> (histSnap γ a' (Hl ++ [(w, v)]) ∗ tokTie GD γ a' (Hl ++ [(w, v)]) {[w := (1 : Qp)]}) :=
  tokTieAfterWriteSnap γ GD a' Hl w v

/-- Generic reindexing along two equal-length lists, for a body that only depends on the index
(deviation 6). -/
theorem ownBigSepLReindex {A B : Type _} (Φ : Nat → IProp GF) (l : List A) (l' : List B) :
    l.length = l'.length →
    iprop([∗list] j ↦ _x ∈ l, Φ j) ⊢ iprop([∗list] j ↦ _x ∈ l', Φ j) :=
  bigSepLReindex Φ l l'

end tokSec

section owned
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [axG : AxirisG GF]
  [Axpol] [AxlogG GF Hent] [AxannotGS GF]

/-- Local copy of `AxProtBytes.flow_eq_owned_writen_chain_snap` (deviation 6). -/
theorem ownFlowEqWritenSnap (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (GD : Gdexec) (_Hcons : rvwmoCatConsistent GD) (w : Geid) (a : Int) (Hs : List (List Hent))
    (Vs : List (BitVec 8)) (sOb0 : GSet Geid) (flowIn : Mea GF) (data : List (BitVec 8))
    (Hlen : Hs.length = Vs.length)
    (Hisw : gisW GD.gdG w = true)
    (Hcompl : ∀ a' v', gwritesByte GD.gdG w a' v' →
      ∃ j : Nat, Vs[j]? = some v' ∧ a' = a + (j : Int))
    (Hgd : graphData GD w = some data) :
    iprop(([∗map] Rin ∈ flowIn, Rin) -∗
        [∗list] j ↦ H ∈ Hs, histAuth γ (a + (j : Int)) 1 H) ⊢
      flowEqDyn GD w sOb0 flowIn
        iprop((tokn γ GD a (writenHist w Vs Hs) {[w := (1 : Qp)]} ∗
          ([∗list] j ↦ H' ∈ writenHist w Vs Hs, histSnap γ (a + (j : Int)) H')) ∗
          ⌜graphData GD w = some data⌝) :=
  flowEqOwnedWritenChainSnap γ Hob_eq GD w a Hs Vs sOb0 flowIn data Hlen Hisw Hcompl Hgd

/-- THE SPILL'S FLOW at the real protocol: from the eight `histAuth`s, the write's flow
equation; the deposit `sdTok` is allocated at `(i, k)` and its FRAGMENT is handed back to the
thread. -/
theorem storeFlowOwned (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (Hann_eq : ∀ m : Mea GF, AxirisG.annotInterp m ⊣⊢ AxAnnot.annotInterp m)
    (i : Agent) (k : Nat) (a : Int) (Hs0 : List (List Hent))
    (Hlen0 : Hs0.length = sdData.length)
    (Hw : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜sdWriteOk GD i k a⌝)
    (Hloc : ∀ GD ls, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢
        |==> ∃ ls', AxirisG.localInterp GD i (k + 1) ls') :
    iprop([∗list] j ↦ H ∈ Hs0, histAuth (GF := GF) γ (a + (j : Int)) 1 H) ⊢
      ∀ (GD : Gdexec) (ls : AxirisG.logTsT GF),
        ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
        storeFlowRes GD i k sdData
          (AxAnnot.annotOwn (i, k) (sdTok γ a (writenHist (i, k) sdData Hs0) (i, k))) := by
  have hw : iprop([∗list] j ↦ H ∈ Hs0, histAuth (GF := GF) γ (a + (j : Int)) 1 H) ⊢
      iprop(([∗map] Rin ∈ (∅ : Mea GF), Rin) -∗
        [∗list] j ↦ H ∈ Hs0, histAuth (GF := GF) γ (a + (j : Int)) 1 H) := by
    iintro Ht _
    iexact Ht
  iintro Hauths %GD %ls %Hc #Hg Hl0
  ihave %Hwok := (Hw GD Hc) $$ Hg
  obtain ⟨Hisw, Hcompl, Hgd⟩ := Hwok
  unfold storeFlowRes
  iintro %na ⟨Hpg, Hannot⟩
  ihave %Hnin := naAtProgressNotElemOf GD i k na $$ Hpg
  ihave Hl1 : iprop(|==> ∃ ls', AxirisG.localInterp GD i (k + 1) ls') $$ [Hl0]
  · iapply (Hloc GD ls Hc)
    isplitl []
    · iexact Hg
    · iexact Hl0
  imod Hl1 with ⟨%ls', Hl1⟩
  ihave Hannot := (Hann_eq na).1 $$ Hannot
  imod (annotAlloc na (i, k) (sdTok γ a (writenHist (i, k) sdData Hs0) (i, k)) Hnin) $$ Hannot
    with ⟨Hannot, Hfrag⟩
  have Hfeq := hw.trans (ownFlowEqWritenSnap γ Hob_eq GD Hc (i, k) a Hs0 sdData
    (Axpol.sPol GD (i, k)) ∅ sdData Hlen0 Hisw Hcompl Hgd)
  ihave Hfe := Hfeq $$ Hauths
  imodintro
  inext
  imodintro
  iexists (sdTok γ a (writenHist (i, k) sdData Hs0) (i, k)), (∅ : Mea GF), (∅ : Mea GF), ls'
  isplitr
  · iapply AxProtGate.naSplittingWfEmpty
  isplitl [Hfe]
  · iapply (flowEqDynMono GD (i, k) (Axpol.sPol GD (i, k)) (∅ : Mea GF) _ _) $$ [] Hfe
    inext
    iintro ⟨⟨Ht, -⟩, Hp⟩
    isplitl [Ht]
    · iapply (toknSdTok γ GD a _ (i, k))
      iexact Ht
    · iexact Hp
  isplitl [Hannot]
  · iapply (Hann_eq _).2
    rw [AxProtGate.annotInsertEq]
    iexact Hannot
  isplitl [Hl1]
  · iexact Hl1
  · iexact Hfrag

/-- THE CAPSTONE: `c.sdsp ; c.ldsp` at the real protocol.  The only resource is the eight slot
bytes' `histAuth`s (pre-spill histories `Hs0`); the reload's annotation is `⌜v = sdData⌝`. -/
theorem wpdEpiSdLdOwned (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (Hann_eq : ∀ m : Mea GF, AxirisG.annotInterp m ⊣⊢ AxAnnot.annotInterp m)
    (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch) (kk : Nat) (a : Int)
    (Hs0 : List (List Hent))
    -- c.sdsp: the store at `kk`
    (Hgd_sd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk (pcSd : Int) sdVs⌝)
    (Hrow_sd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜storeRowOk GD i kk⌝)
    (Hw_sd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜sdWriteOk GD i kk a⌝)
    (Hloc_st : ∀ GD ls, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i kk ls ⊢
        |==> ∃ ls', AxirisG.localInterp GD i (kk + 1) ls')
    -- c.ldsp: the load at `kk + 1`
    (Hgd_ld : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢
        ⌜AxCjrWpd.fetchImgOk GD i (kk + 1) (pcLd : Int) AxEpiLedger.ldVs⌝)
    (Hrow_ld : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i (kk + 1)⌝)
    (Hok_ld : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢
        ⌜ldspOwnOk GD i (kk + 1) (i, kk) a (writenHist (i, kk) sdData Hs0)⌝)
    (Hloc_ldv : ∀ GD ls, rvwmoCatConsistent GD →
      AxirisG.localInterp (GF := GF) GD i (kk + 1) ls ⊢
        |==> ∃ ls', AxirisG.localInterp GD i (kk + 1 + 1) ls')
    (Hlens0 : Hs0.length = 8)
    -- the row is EXACTLY these two events
    (Hlen : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜(AxOpsem.grow GD i).length = kk + 2⌝) :
    ⊢ ([∗list] j ↦ H ∈ Hs0, histAuth γ (a + (j : Int)) 1 H) -∗
      (∀ (GD : Gdexec) s1, ⌜epiSdLdInv cpu kk s1⌝ -∗
         ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ib, kk⟩ Φ := by
  have Hlen0 : Hs0.length = sdData.length := by rw [Hlens0]; rfl
  have Hlens1 : (writenHist (i, kk) sdData Hs0).length = 8 := by
    rw [writenHistLength]; exact Hlens0
  have Hlast := writenHistLastSpill (i, kk) sdData Hs0 Hlen0
  have Htok : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢
        sdTok γ a (writenHist (i, kk) sdData Hs0) (i, kk) -∗
          tokn γ GD a (writenHist (i, kk) sdData Hs0)
            ({[(i, kk) := (1 : Qp)]} : GMapF Geid Qp) := by
    intro GD _
    iintro _ Ht
    iapply (sdTokTokn γ GD a Hs0 (i, kk) sdData)
    iexact Ht
  iintro Hauths R
  iapply (wpdEpiSdLdRes i Φ cpu ib kk (fun _ w => iprop(⌜w = sdData⌝))
    (AxAnnot.annotOwn (i, kk) (sdTok γ a (writenHist (i, kk) sdData Hs0) (i, kk)))
    Hgd_sd Hrow_sd Hgd_ld Hrow_ld Hlen) $$ [Hauths] [] R
  · iapply (storeFlowOwned γ Hob_eq Hann_eq i kk a Hs0 Hlen0 Hw_sd Hloc_st)
    iexact Hauths
  · iintro Hf
    iapply (ldspFlowOwned γ Hob_eq Hann_eq i (kk + 1) (i, kk)
      (sdTok γ a (writenHist (i, kk) sdData Hs0) (i, kk)) a (writenHist (i, kk) sdData Hs0)
      sdData sdDataLength Hlens1 Hlast Hok_ld Htok Hloc_ldv)
    iexact Hf

end owned

end Weak
