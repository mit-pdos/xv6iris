/-
Weak: **c.sdsp ; c.ldsp ; c.jr through the logic: the register-level capstone
`epiRetSound2 : epiRetSound2Stmt`** (`AxEpiRetCert`'s statement, unchanged).

Rocq: `iris/AxEpiRet.v` @ xxvzwolszwmp.  Split (Lean-only): this file holds the Rocq §1–§3 WPd
lemmas; `Weak/AxEpiRetb.lean` the staged forward region, §4 (`axGA2`), §5 (adequacy), §6, §8.

## What the port proves (both files)

`epiRetSound2` (AxEpiRetb §8): 2 harts, hart 1 ARBITRARY with its own slot-`b` WPd (`Hwp1`);
hart 0 = c.sdsp ; c.ldsp ; c.jr (row `[SD; LD]`, Stage C); ANY run of hart 0 to an instruction
boundary at the row end (position 2) reached after the c.jr (`Hafter : PC ≠ pcJr`) has
PC = `jalrTarget sdWord`.  One adequacy run (`epiRetAdeq`, at `axGA2` with the real ownership
protocol) gives BOTH `graphValue GD (0,1) = some sdData` and the PC post (`epiRetPost2`).
OWNERSHIP IS LOAD-BEARING: `raceRetNoWpd1` refutes, with no hypothesis, the racing hart's WPd at
`AxEpiRetCert.raceRet`; non-vacuity: `AxEpiRetCert.okRetAllPremisesAndConcl`.  Keeps `Hlob_gmo`
(forwarding excluded; cf. `AxEpiSoundFwd`).  `epiRetReloadSound` / `epiRetStmtPremisesReload`:
the reload fact alone.

HOW THE PC IS REACHED (Lean, deviation 1).  `wpdEpiRetOwnedRb` applies `AxCjrReach.wpdReachRtc`
at hart 0's START, so every row-end obligation is owed only on states forward-reachable by
`rstep (· = GD0) 0`.  The post-reload obligation receives the readback (`ldRbv`, `w = sdData`
inside `postLifting`) and the reachability fact; the pure `epiRetReachPc` closes it by the
STAGED REGION of AxEpiRetb: an invariant `AxEpiRet.Inv` (ten `chk` stages from the start through
the target's c.sdsp store, cut at instruction boundaries against canonical register files,
15 `decide +kernel` certificates) preserved by `rstep` at graphs with `AxEpiRet.GFacts`
(`AxEpiRet.invStep`), and at a row-end boundary PC is `pcJr` or the target (`AxEpiRet.invGood`).

§1 the resource-carrying load whose resource `X w` is indexed by the READ BYTES and whose exit
is the `.pure ()` at `ldOut c w` for the SAME `w` (`wpdCldspAfterSdResv`).  §2 the c.jr at a
pin-agreeing copy of the load's exit, row end over any state (`wpdCjrAfterLdAg`).  §3 the
reload's fragment at the read bytes (`ldRbv`, `ldspFlowOwnedResv`) and the program WPd at the
real protocol (`wpdEpiRetOwnedRb`).

## Deviations from Rocq

1. O2 STAGE C + OWNER Q11/Q15 (the KEY change).  In Rocq the c.jr's boundary s4 sits at row
   position 4 (before the c.jr's fetch event) and `wpd_reach_rtc` is applied there, the c.ldsp's
   post-load obligations being restricted to positions ≤ 4.  Under Stage C fetches are no row
   items: the c.ldsp's post-load states, the c.jr and the next instruction all sit at position 2
   = the row end, and the ledger lemmas owe `postLifting Φ` on BACKWARD closures there
   (`Pbefore`, incl. arbitrary-fetch runs of `riscvStep` from any PC), so the PC post is
   unprovable at the c.jr boundary.  Hence:
   (a) `wpdEpiRetOwnedRb` (Rocq: reach at s4, then `wpd_cjr_after_ld_ag` + `wpd_past_row_end`)
       applies the reach at the START (`G`, `HG` arguments; `Rpost` is owed at
       `fun s' => ⌜rtc (rstep G i) s0 s'⌝ -∗ Φ s'`, over any row-end state after the reload);
       everything after the reload is past the row end (`wpdPastRowEnd`), so it does not call
       §2 (`wpdCjrAfterLdAg` is ported for `AxEpiRetFwd`).  `Rpre` (positions ≤ 1, plain `Φ`)
       is as Rocq.  It covers the two-instruction row (`Hgd_jr` is not a premise: the c.jr text
       enters only through `epiRetReachPc`).
   (b) `epiRetReachPc` is restated: from hart 0's start, over `rstep G 0` at any `G` with
       `∀ GD, G GD → AxEpiRet.GFacts GD`, at position 2 with PC ≠ `pcJr` (Rocq: from the c.jr
       boundary at a load exit with `w = sdData`, over `Gf 4`, position 5).
   (c) `chk_pre_exits` is DROPPED and REPLACED by AxEpiRetb's staged certificates
       (`AxEpiRet.certSd/certLd/certJr/certTg`): under Stage C `AxCjrReach.chkPre` is FALSE at
       the c.jr boundary (a `chkNext` walk cannot pass the target's fetch, AxCjrReach
       deviation 1(d)); the stages carry a second pinned fetch at the target (`ramTg`, Q11),
       continued to its store (the next data access, stuck at the row end).
   (d) Posts: `epiRetPost GD i s := i = 0 → s.atK = 2 → graphValue GD (0, 1) = some sdData`
       (Rocq position 5, event `(0,3)`); `epiRetPcPost` at position 2 with the extra premise
       `rs .PC ≠ BitVec.ofNat 64 pcJr` (Q15, `AxEpiRetCert` deviation 1(b)).
   (e) Positions and premises as `AxEpiAdeq` deviation 1: row `[SD @0; LD @1]`, length 2;
       `fetchImgOk` for `fetch_gd_ok`; the fetches' `Hflow`/`Hloc`, `Hntext` and the `Hnw_*`
       (`gis_w` of fetch events) are DROPPED; §1: the fetch, the pre-load run and the load at
       `k`, the `.pure ()`/tick tail at `k + 1` (Rocq `S k`/`S (S k)`), pre-load bound
       `atK ≤ kk` (Rocq `≤ S kk`); `wpdCjrAfterLdAg`'s `Hgd`/`RetP` at `kk` (AxEpiLdJr
       deviation 2).  §4–§6 take the target's text `Hgd_tg` (`AxEpiRetCert` deviation 1(c));
       `epiRetStmtPremisesReload` takes `Hafter` (the capstone's premise list).
2. THE TWO PINS (`AxEpiLedger` deviation 1, `AxRunClose` deviation 1): `LdRetXw` quantifies both
   boundary answers `u' u`; `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg`;
   `seipNotinAJrFix`/`seipNotinAJrT` state that NEITHER pin is in the footprint
   (`∀ r ∈ A, ¬ AxRunClose.pinReg r`; Rocq `sig_seip ∉ A`), and `agreeOnSeip` takes that form.
3. TEXT (`AxEpiSound2` deviation 1): no `T`/`ax_text`; `Hntext` gone everywhere.
4. INSTANCES/CONTEXTS (as `AxEpiAdeq` deviations 4–5, `AxEpiSound2` deviation 2): §3's
   section context `γ`, `Hob_eq`, `Hann_eq` are explicit arguments; `ldRbv` takes none.
   Rocq's `Local Instance epi_ret_ga2 := epi_ga2 GD0 T γ` is AxEpiAdeq's reducible `epiGa2 GD0 γ`
   (not redeclared); `wpdEpiRetGa2` is stated at an arbitrary `[Axpol]` (Rocq: `epi_pol`), the
   adequacy passes `epiPol`.  `Hrun0`/`Hrun1` are `∀ (_ : AxannotGS epiGF) (nm : GName)`, `Hwp1`
   `∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] nm`.
5. TYPES: `inl (w, None)` ↦ `.Ok (w, none)`, `Ret tt` ↦ `.pure ()`, `S k` ↦ `k + 1`,
   `register_lookup PC rs` ↦ `rs .PC`, `(i, k) ↦ₐ P` ↦ `AxAnnot.annotOwn (i, k) P`; the race's
   `vm_compute` on `bv_unsigned` images ↦ `decide` on the byte lists.

**Rocq → Lean name map.**  §1 `LdRetXw` `LdRetXw`, `tick_tail_inv_at_k` `tickTailInvAtK`,
`wpd_load_step_resv` `wpdLoadStepResv`, `wpd_load_then_ret_resv` `wpdLoadThenRetResv`,
`wpd_fetch_then_load_resv` `wpdFetchThenLoadResv`, `wpd_cldsp_agree_resv` `wpdCldspAgreeResv`,
`wpd_load_then_tick_resv` `wpdLoadThenTickResv`, `wpd_fetch_then_load_tick_resv`
`wpdFetchThenLoadTickResv`, `wpd_cldsp_tick_resv` `wpdCldspTickResv`,
`wpd_cldsp_after_sd_resv` `wpdCldspAfterSdResv`.  §2 `seip_notin_A_jr_fix` `seipNotinAJrFix`,
`seip_notin_A_jr_t` `seipNotinAJrT`, `agree_on_seip` `agreeOnSeip`, `wpd_cjr_after_ld_ag`
`wpdCjrAfterLdAg`.  §3 `ld_rbv` `ldRbv`, `ldsp_flow_owned_resv` `ldspFlowOwnedResv`,
`wpd_epi_ret_owned_rb` `wpdEpiRetOwnedRb`.  (AxEpiRetb) §4 `epi_ret_post` `epiRetPost`,
`epi_ret_pc_post` `epiRetPcPost`, `epi_ret_post2` `epiRetPost2`, `post_ra_sym_seip`
`postRaSymSeip`, `epi_ret_reach_pc` `epiRetReachPc`, `epi_ret_ga2` ↦ `epiGa2` (AxEpiAdeq),
`wpd_epi_ret_ga2` `wpdEpiRetGa2`; §5 `epi_ret_adeq` `epiRetAdeq`, `epi_ret_reload_sound`
`epiRetReloadSound`; §6 `epi_ret_stmt_premises_reload` `epiRetStmtPremisesReload`,
`race_ret_no_wpd1` `raceRetNoWpd1`; §8 `epi_ret_sound2` `epiRetSound2`.  None is in the
duplicated-name table.  Lean-only (AxEpiRetb, all in `namespace Weak.AxEpiRet`): the staged
region (`W`, `wq`, `eqW`, `tgt`, `QA`, `QB`, `exitRam`, `fetchCont`, `loadCont`, `storeCont`,
`cut`, `C0`, `mkW`, `exitOf`, `Cld`, `CjrF`, `CjrT`, `CjrL`, `CtgL`, the stages `sdA sdB sdC ldA
ldB ldC jrA jrB tgA tgB` and `ramTg`, the certificates `certSd certLd certJr certTg`), the
bookkeeping (`notPin`, `mkWOff`, `eqWSpec`, `offW`, `cutAgree`, `cldOff`, `cjrOff`, `ctgOff`),
pin-insensitivity (`qaIns qbIns exitIns fetchContIns loadContIns storeContIns cutIns` and the ten
`*Ins`), the invariant (`stageAt`, `Inv`, `stageAgree`, `adminHalves`, `orsCases`, `offWStep`,
`memReadStep`, `progOrRead`, `stageStep`, `fetchContSpec`, `loadContSpec`, `storeContSpec`,
`fetchNext`, `GFacts`, `rowEnd2`, `hQA`, `hQB`, `invStep`, `rtcInv`, `invStart`, `invGood`).

**Dropped:** `chk_pre_exits` (deviation 1(c): false under Stage C; replaced).  **Not ported:**
the `Print Assumptions` lines (the lint's axiom check covers them; `#print axioms` of
`epiRetSound2`/`raceRetNoWpd1`: `propext`, `Classical.choice`, `Quot.sound`).  Rocq 30
declarations (incl. the local instance); Lean 28 + 81 Lean-only.
-/
import Weak.AxEpiAdeq
import Weak.AxEpiLdJr
import Weak.AxCjrReach

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Wlabel

/-! # 1. THE EXACT, RESOURCE-CARRYING LOAD -/

/-- The exact exit for a FIXED read `w`. -/
def LdRetXw (t : ExecSt) (Dr Dw D : List Register) (vs : List (BitVec 8)) (tick : Bool)
    (cpu : CPU) (k : Nat) (w : List (BitVec 8)) (s : Athread) : Prop :=
  ∃ (u' u : BitVec 1) (o : Option (BitVec 1 × BitVec 1)) (t3 : ExecSt),
    tickOf o = tick ∧ ldFinal t Dr Dw D vs u' u o w = some t3 ∧ RetX cpu t3.regs k s

theorem tickTailInvAtK (D : List Register) (cpu : CPU) (m : SailM Unit) (tl : ExecSt) (k : Nat)
    (s1 : Athread) : tickTailInv D cpu m tl k s1 → s1.atK = k := by
  rintro ⟨km1, t4, ib4, -, H | ⟨v', k1, t5, ib5, -, H⟩⟩
  · exact AxEpiAdeq.pseipMeipAtK _ _ _ _ _ _ _ H
  · rcases H with H | H | ⟨q, ⟨v, t6, ib6, -, rfl⟩, H⟩
    · exact pbeforeAtK _ _ H
    · exact H.1
    · exact pbeforeAtK _ _ H

section resv
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem wpdLoadStepResv (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (rs0 : RegFile) (Rv : Gdexec → List (BitVec 8) → IProp GF)
    (X : List (BitVec 8) → IProp GF)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hn : 0 < n) (Hnf : (classify req.access_kind).akIfetch = false)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i k⌝) :
    ⊢ ∀ rs, ⌜regsAgree AxRunClose.pinReg rs0 rs⌝ -∗
      (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
         ⌜graphValue GD (i, k) = some v⌝ -∗ loadFlowRes GD i k (Rv GD v) (X v)) -∗
      (∀ (v : List (BitVec 8)) (rs' : RegFile), ⌜v.length = n⌝ -∗
         ⌜regsAgree AxRunClose.pinReg rs0 rs'⌝ -∗ X v -∗
         wpd .MaybeStuck i ⟨.PHart cpu (KK (.Ok (wordOfBytes n v, none))) rs' none ib, k + 1⟩ Φ) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ Φ := by
  unfold loadFlowRes
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
  obtain ⟨lb0, Hlb0, Hadv0⟩ := Hok
  isplit
  · -- (a) THE DATA READ, demonic
    iintro %id %K %Hst
    obtain ⟨lb, Hlb, Hid, -, HK⟩ := Hst
    simp only at Hlb
    rw [Hlb0, Option.some.injEq] at Hlb
    subst Hlb Hid
    simp only [Hadv0, ↓reduceIte]
    iintro %v %Hv %Hlenv
    obtain ⟨l, d, d', -, Hrv, Hps, Hk'⟩ := HK v Hlenv
    obtain ⟨tvs, Htl, rfl, Hp'⟩ :=
      AxLdspWpd.loadStepInv cpu n va req KK rs ib d l _ d' Hdev Hlat Hnf Hps
    simp only [wlRvals] at Hrv
    subst Hrv
    rw [Hadv0] at Hk'
    have hKv : K (tvs.map Prod.snd) =
        ⟨.PHart cpu (KK (.Ok (wordOfBytes n (tvs.map Prod.snd), none))) rs none ib, k + 1⟩ := by
      cases hK : K (tvs.map Prod.snd) with
      | AThread p' k' =>
        rw [hK] at Hp' Hk'
        simp only at Hp' Hk'
        rw [Hp', Hk']
    rw [hKv]
    unfold wpEvStep
    iintro %na Hpg
    ihave Hf := F $$ %GD %ls %(tvs.map Prod.snd) %Hc Hg Hloc %Hv
    imod Hf $$ %na Hpg with Hf
    imodintro
    inext
    imod Hf with ⟨%nu, %nuu, %ls', Hs, Hfe, Hna, Hl, HX⟩
    imodintro
    iexists (), Rv GD (tvs.map Prod.snd), nu, nuu, ls'
    isplitr
    · ipureintro
      trivial
    iframe Hs Hna Hl
    isplitl [Hfe]
    · iapply (flowEqDynMono GD (i, k) _ nu (Rv GD (tvs.map Prod.snd))
        iprop(Rv GD (tvs.map Prod.snd) ∗ ⌜graphValue GD (i, k) = some (tvs.map Prod.snd)⌝))
      · inext
        iintro HR
        iframe HR
        ipureintro
        exact Hv
      · iexact Hfe
    · iapply C $$ %(tvs.map Prod.snd) %rs
      · ipureintro
        rw [List.length_map]
        exact Htl
      · ipureintro
        exact HP
      · iexact HX
  isplit
  · -- (b) no program step exists at a data-load node
    iintro %l %s' %Hst %Hpin
    have hfalse : False := by
      obtain ⟨d, d', hps⟩ := astepProgPstep _ _ _ _ Hst
      obtain ⟨tvs, -, hl, -⟩ :=
        AxLdspWpd.loadStepInv cpu n va req KK rs ib d l _ d' Hdev Hlat Hnf hps
      subst hl
      cases Hst with
      | AStepAdmin _ _ _ _ _ _ hadm _ => exact hadm
      | AStepWrite _ _ _ _ _ _ _ _ hwr _ _ _ => simp [wlWr] at hwr
      | AStepFence _ _ _ _ _ _ _ _ hf _ _ => simp [wlFence] at hf
    exact hfalse.elim
  isplit
  · -- (c) the PLIC wire: back to the load node, Löb
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
  · -- (d) row end: the load item sits at `k`
    iintro %Heq
    have h1 := lookup_lt_Some Hlb0
    simp only at Heq
    omega

/-- tick = false tail: `epure` to `.pure ()`, exit indexed by the read bytes. -/
theorem wpdLoadThenRetResv (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (nl va : Nat)
    (req : Mem_read_request nl va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * nl) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (sLd : ExecSt) (D : List Register) (Rv : Gdexec → List (BitVec 8) → IProp GF)
    (X : List (BitVec 8) → IProp GF)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hn : 0 < nl) (Hnf : (classify req.access_kind).akIfetch = false)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i k⌝)
    (Hseip : Register.sig_seip ∉ D) (Hmeip : Register.sig_meip ∉ D)
    (Hpost : ∀ x : BitVec (8 * nl), ∃ sEnd : ExecSt,
      epure D (KK (.Ok (x, none))) sLd = some ((), sEnd)) :
    ⊢ ∀ s2, ⌜Qat ⟨.PHart cpu (.impure (.ok (.memRead nl va req)) KK) sLd.regs none ib, k⟩ s2⌝ -∗
      (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
         ⌜graphValue GD (i, k) = some v⌝ -∗ loadFlowRes GD i k (Rv GD v) (X v)) -∗
      (∀ v, X v -∗
       ((∀ (sEnd : ExecSt) (ib' : Ibch) (s' : Athread),
          ⌜epure D (KK (.Ok (wordOfBytes nl v, none))) sLd = some ((), sEnd)⌝ -∗
          ⌜Qat ⟨.PHart cpu (.pure ()) sEnd.regs none ib', k + 1⟩ s'⌝ -∗
          wpd .MaybeStuck i s' Φ) ∧
        (∀ (GD : Gdexec) (s1 : Athread), ⌜s1.atK = k + 1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1))) -∗
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
    iapply (wpdLoadStepResv Φ i cpu nl va req KK ib k sLd.regs Rv X Hdev Hlat Hn Hnf Hrow) $$
      %rs2 %(regsAgreeSym _ _ _ hag) F
    iintro %v %rs' %Hlv %hag' HX
    ihave R := R $$ %v HX
    obtain ⟨sEnd, Hep⟩ := Hpost (wordOfBytes nl v)
    obtain ⟨ib', Hrun⟩ := epureGstepRtc D Hseip Hmeip _ _ _ _ Hep cpu ib (k + 1)
    iapply (wpdRunTo Φ i _ _ Hrun) $$
      %⟨.PHart cpu (KK (.Ok (wordOfBytes nl v, none))) rs' none ib, k + 1⟩
      %⟨rfl, rfl, rfl, rfl, rfl, regsAgreeSym _ _ _ hag'⟩
    isplit
    · icases R with ⟨R, -⟩
      iintro %s3 %Hq3
      iapply R $$ %sEnd %ib' %s3 %Hep %Hq3
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %Hb %Hend
      have hk1 : s1.atK = k + 1 := pbeforeAtK _ _ Hb
      iapply R $$ %GD %s1 %hk1 %Hend

theorem wpdFetchThenLoadResv (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KKf : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (vs : List (BitVec 8)) (rs0 rs : RegFile) (nl val : Nat)
    (reql : Mem_read_request nl val Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * nl) × Option Bool) Arch.abort → SailM Unit) (ibLd : Ibch)
    (tl : ExecSt) (D : List Register) (Rv : Gdexec → List (BitVec 8) → IProp GF)
    (X : List (BitVec 8) → IProp GF)
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
    (Hseip : Register.sig_seip ∉ D) (Hmeip : Register.sig_meip ∉ D)
    (Hpost : ∀ x : BitVec (8 * nl), ∃ sEnd : ExecSt,
      epure D (KK (.Ok (x, none))) tl = some ((), sEnd)) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
         ⌜graphValue GD (i, k) = some v⌝ -∗ loadFlowRes GD i k (Rv GD v) (X v)) -∗
      ((∀ v, X v -∗
        ((∀ (sEnd : ExecSt) (ib' : Ibch) (s' : Athread),
           ⌜epure D (KK (.Ok (wordOfBytes nl v, none))) tl = some ((), sEnd)⌝ -∗
           ⌜Qat ⟨.PHart cpu (.pure ()) sEnd.regs none ib', k + 1⟩ s'⌝ -∗
           wpd .MaybeStuck i s' Φ) ∧
         (∀ (GD : Gdexec) (s1 : Athread), ⌜s1.atK = k + 1⌝ -∗
           ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1))) ∧
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
    iapply (wpdLoadThenRetResv Φ i cpu nl val reql KK ibLd k tl D Rv X Hdevl Hlatl Hn Hnfl Hrow
      Hseip Hmeip Hpost) $$ %s3 %Hq3 F R
  · icases R with ⟨-, R⟩
    iexact R

/-- tick = false c.ldsp, exact exit at the read bytes. -/
theorem wpdCldspAgreeResv (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
    (ib : Ibch) (kk : Nat) (t : ExecSt) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (postLd : Int → RegFile → Prop)
    (Rv : Gdexec → List (BitVec 8) → IProp GF) (X : List (BitVec 8) → IProp GF)
    (L : AxLdModelFacts t Dr Dw D base vs ldaddr postLd)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk base vs⌝)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i kk⌝)
    (rs : RegFile) (Hag0 : regsAgree AxRunClose.pinReg t.regs rs) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i kk ls -∗
         ⌜graphValue GD (i, kk) = some v⌝ -∗ loadFlowRes GD i kk (Rv GD v) (X v)) -∗
      ((∀ w, X w -∗
          ((∀ s', ⌜LdRetXw t Dr Dw D vs false cpu (kk + 1) w s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
           (∀ (GD : Gdexec) s1, ⌜s1.atK = kk + 1⌝ -∗ ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗
              postLifting Φ i s1))) ∧
       (∀ (GD : Gdexec) s1, ⌜s1.atK ≤ kk⌝ -∗
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
        iapply (wpdFetchThenLoadResv Φ i cpu n va req KKf ib2 kk vs t2.regs rs3 nl val reql KK
          ibLd tl D Rv X Hdev Hfe Hlen Hgd (regsAgreeSym _ _ _ hag) HrunPre Hdevl Hlatl Hn Hnfl
          Hrow HD HDm Hpost) $$ F
        isplit
        · icases R with ⟨R, -⟩
          iintro %w HX
          ihave R := R $$ %w HX
          isplit
          · icases R with ⟨R, -⟩
            iintro %sEnd %ib3 %s' %Hep %Hs'
            have Ht : ldTail D none (KK (.Ok (wordOfBytes nl w, none))) tl = some sEnd := by
              simp only [ldTail, Hep]
            iapply R $$ %s' %⟨v', v, none, sEnd, rfl,
              ldFinalChain t Dr Dw D vs v' v none w km t0 k0 t1 n va req KKf t2 nl val reql KK
                tl sEnd Hts Hts1 He He2 Ht, ib3, Hs'⟩
          · icases R with ⟨-, R⟩
            iexact R
        · icases R with ⟨-, R⟩
          iintro %GD %s1 %Hs1 %Hlen1
          iapply R $$ %GD %s1 %(Nat.le_of_eq (pbeforeAtK _ _ Hs1)) %Hlen1
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %Hs1 %Hlen1
      iapply R $$ %GD %s1 %(Nat.le_of_eq (pseipErdAtK _ _ _ _ _ _ _ _ _ Hs1)) %Hlen1
  · icases R with ⟨-, R⟩
    iintro %GD %s1 %Hs1 %Hlen1
    iapply R $$ %GD %s1 %(Nat.le_of_eq (AxEpiAdeq.pseipMeipAtK _ _ _ _ _ _ _ Hs1)) %Hlen1

/-- tick = true tail. -/
theorem wpdLoadThenTickResv (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (nl va : Nat)
    (req : Mem_read_request nl va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * nl) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (sLd : ExecSt) (D : List Register) (postLd : Int → RegFile → Prop)
    (Rv : Gdexec → List (BitVec 8) → IProp GF) (X : List (BitVec 8) → IProp GF)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hn : 0 < nl) (Hnf : (classify req.access_kind).akIfetch = false)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i k⌝)
    (HD : Register.sig_seip ∉ D) (HDm : Register.sig_meip ∉ D)
    (Hx : ∀ x : BitVec (8 * nl), tickPostOk D (postLd (x.toNat : Int)) (KK (.Ok (x, none))) sLd) :
    ⊢ ∀ s2, ⌜Qat ⟨.PHart cpu (.impure (.ok (.memRead nl va req)) KK) sLd.regs none ib, k⟩ s2⌝ -∗
      (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
         ⌜graphValue GD (i, k) = some v⌝ -∗ loadFlowRes GD i k (Rv GD v) (X v)) -∗
      (∀ v, X v -∗
       ((∀ s', ⌜TailX D cpu (KK (.Ok (wordOfBytes nl v, none))) sLd (k + 1) s'⌝ -∗
          wpd .MaybeStuck i s' Φ) ∧
        (∀ (GD : Gdexec) (s1 : Athread), ⌜s1.atK = k + 1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1))) -∗
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
    iapply (wpdLoadStepResv Φ i cpu nl va req KK ib k sLd.regs Rv X Hdev Hlat Hn Hnf Hrow) $$
      %rs2 %(regsAgreeSym _ _ _ hag) F
    iintro %v %rs' %Hlv %hag' HX
    ihave R := R $$ %v HX
    iapply (wpdTickTailExact i Φ cpu _ sLd ib (k + 1) D _ HD HDm (Hx (wordOfBytes nl v)) rs' hag')
    isplit
    · icases R with ⟨R, -⟩
      iexact R
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %Hs1 %Hl
      iapply R $$ %GD %s1 %(tickTailInvAtK _ _ _ _ _ _ Hs1) %Hl

theorem wpdFetchThenLoadTickResv (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KKf : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (vs : List (BitVec 8)) (rs0 rs : RegFile) (nl val : Nat)
    (reql : Mem_read_request nl val Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * nl) × Option Bool) Arch.abort → SailM Unit) (ibLd : Ibch)
    (tl : ExecSt) (D : List Register) (postLd : Int → RegFile → Prop)
    (Rv : Gdexec → List (BitVec 8) → IProp GF) (X : List (BitVec 8) → IProp GF)
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
         ⌜graphValue GD (i, k) = some v⌝ -∗ loadFlowRes GD i k (Rv GD v) (X v)) -∗
      ((∀ v, X v -∗
        ((∀ s', ⌜TailX D cpu (KK (.Ok (wordOfBytes nl v, none))) tl (k + 1) s'⌝ -∗
           wpd .MaybeStuck i s' Φ) ∧
         (∀ (GD : Gdexec) (s1 : Athread), ⌜s1.atK = k + 1⌝ -∗
           ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1))) ∧
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
    iapply (wpdLoadThenTickResv Φ i cpu nl val reql KK ibLd k tl D postLd Rv X Hdevl Hlatl Hn
      Hnfl Hrow HD HDm Hx) $$ %s3 %Hq3 F R
  · icases R with ⟨-, R⟩
    iexact R

theorem wpdCldspTickResv (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
    (ib : Ibch) (kk : Nat) (t : ExecSt) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (postLd : Int → RegFile → Prop)
    (Rv : Gdexec → List (BitVec 8) → IProp GF) (X : List (BitVec 8) → IProp GF)
    (L : AxLdTickFacts t Dr Dw D base vs ldaddr postLd)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk base vs⌝)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i kk⌝)
    (rs : RegFile) (Hag0 : regsAgree AxRunClose.pinReg t.regs rs) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i kk ls -∗
         ⌜graphValue GD (i, kk) = some v⌝ -∗ loadFlowRes GD i kk (Rv GD v) (X v)) -∗
      ((∀ w, X w -∗
          ((∀ s', ⌜LdRetXw t Dr Dw D vs true cpu (kk + 1) w s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
           (∀ (GD : Gdexec) s1, ⌜s1.atK = kk + 1⌝ -∗ ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗
              postLifting Φ i s1))) ∧
       (∀ (GD : Gdexec) s1, ⌜s1.atK ≤ kk⌝ -∗
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
        iapply (wpdFetchThenLoadTickResv Φ i cpu n va req KKf ib2 kk vs t2.regs rs3 nl val reql
          KK ibLd tl D postLd Rv X Hdev Hfe Hlen Hgd (regsAgreeSym _ _ _ hag) HrunPre Hdevl Hlatl
          Hn Hnfl Hrow HD HDm Hx) $$ F
        isplit
        · icases R with ⟨R, -⟩
          iintro %w HX
          ihave R := R $$ %w HX
          isplit
          · icases R with ⟨R, -⟩
            iintro %s' %Hs'
            obtain ⟨u2', u2, t5, Ht, Hr⟩ := Hs'
            iapply R $$ %s' %⟨v', v, some (u2', u2), t5, rfl,
              ldFinalChain t Dr Dw D vs v' v (some (u2', u2)) w km t0 k0 t1 n va req KKf t2 nl
                val reql KK tl t5 Hts Hts1 He He2 Ht, Hr⟩
          · icases R with ⟨-, R⟩
            iexact R
        · icases R with ⟨-, R⟩
          iintro %GD %s1 %Hs1 %Hlen1
          iapply R $$ %GD %s1 %(Nat.le_of_eq (pbeforeAtK _ _ Hs1)) %Hlen1
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %Hs1 %Hlen1
      iapply R $$ %GD %s1 %(Nat.le_of_eq (pseipErdAtK _ _ _ _ _ _ _ _ _ Hs1)) %Hlen1
  · icases R with ⟨-, R⟩
    iintro %GD %s1 %Hs1 %Hlen1
    iapply R $$ %GD %s1 %(Nat.le_of_eq (AxEpiAdeq.pseipMeipAtK _ _ _ _ _ _ _ Hs1)) %Hlen1

/-- THE c.ldsp AFTER THE c.sdsp, BOTH TICKS: exact exit `ldOut c w` at the SAME read bytes `w`
whose resource `X w` the load handed back. -/
theorem wpdCldspAfterSdResv (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch)
    (kk : Nat) (v' v : BitVec 1) (Rv : Gdexec → List (BitVec 8) → IProp GF)
    (X : List (BitVec 8) → IProp GF)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢
        ⌜AxCjrWpd.fetchImgOk GD i kk (pcLd : Int) AxEpiLedger.ldVs⌝)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i kk⌝)
    (tick : Bool) (rs : RegFile) (Hag : regsAgree AxRunClose.pinReg (tAfterSd v' v).regs rs) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (w : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i kk ls -∗
         ⌜graphValue GD (i, kk) = some w⌝ -∗ loadFlowRes GD i kk (Rv GD w) (X w)) -∗
      ((∀ w, X w -∗
          ((∀ (c : Ldc) s', ⌜c.lcV' = v' ∧ c.lcV = v ∧ tickOf c.lcT = tick ∧
               RetX cpu (ldOut c w) (kk + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
           (∀ (GD : Gdexec) s1, ⌜s1.atK = kk + 1⌝ -∗ ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗
              postLifting Φ i s1))) ∧
       (∀ (GD : Gdexec) s1, ⌜s1.atK ≤ kk⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep tick) rs none ib, kk⟩ Φ := by
  have Hc : ∀ w s', LdRetXw (tAfterSd v' v) AxEpiProbe.drNopin DwAll DPost AxEpiLedger.ldVs tick
      cpu (kk + 1) w s' → ∃ c : Ldc, c.lcV' = v' ∧ c.lcV = v ∧ tickOf c.lcT = tick ∧
        RetX cpu (ldOut c w) (kk + 1) s' := by
    rintro w s' ⟨u', u, o, t3, Htk, Hf, Hr⟩
    refine ⟨⟨v', v, u', u, o⟩, rfl, rfl, Htk, ?_⟩
    unfold ldOut
    dsimp only
    rw [Hf]
    exact Hr
  iintro F R
  have HR : ⊢ ((∀ w, X w -∗
          ((∀ (c : Ldc) s', ⌜c.lcV' = v' ∧ c.lcV = v ∧ tickOf c.lcT = tick ∧
               RetX cpu (ldOut c w) (kk + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
           (∀ (GD : Gdexec) s1, ⌜s1.atK = kk + 1⌝ -∗ ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗
              postLifting Φ i s1))) ∧
       (∀ (GD : Gdexec) s1, ⌜s1.atK ≤ kk⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      ((∀ w, X w -∗
          ((∀ s', ⌜LdRetXw (tAfterSd v' v) AxEpiProbe.drNopin DwAll DPost AxEpiLedger.ldVs tick
               cpu (kk + 1) w s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
           (∀ (GD : Gdexec) s1, ⌜s1.atK = kk + 1⌝ -∗ ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗
              postLifting Φ i s1))) ∧
       (∀ (GD : Gdexec) s1, ⌜s1.atK ≤ kk⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) := by
    iintro R
    isplit
    · icases R with ⟨R, -⟩
      iintro %w HX
      ihave R := R $$ %w HX
      isplit
      · icases R with ⟨R, -⟩
        iintro %s' %Hs'
        obtain ⟨c, Hc1⟩ := Hc w s' Hs'
        iapply R $$ %c %s' %Hc1
      · icases R with ⟨-, R⟩
        iexact R
    · icases R with ⟨-, R⟩
      iexact R
  ihave R := HR $$ R
  cases tick
  · iapply (wpdCldspAgreeResv i Φ cpu ib kk (tAfterSd v' v) _ _ _ _ _ _ _ Rv X
      (epiLedgerCldspAfterSd v' v) Hgd Hrow rs Hag) $$ F R
  · iapply (wpdCldspTickResv i Φ cpu ib kk (tAfterSd v' v) _ _ _ _ _ _ _ Rv X
      (epiLedgerCldspTick v' v) Hgd Hrow rs Hag) $$ F R

end resv

/-! # 2. THE c.jr AT A PIN-AGREEING COPY OF THE LOAD'S EXIT -/

theorem seipNotinAJrFix : ∀ r ∈ AJrFix, ¬ AxRunClose.pinReg r := by
  intro r hr hp
  rcases hp with rfl | rfl <;> exact absurd hr (by decide +kernel)

theorem seipNotinAJrT : ∀ r ∈ AJrT, ¬ AxRunClose.pinReg r := by
  intro r hr hp
  rcases hp with rfl | rfl <;> exact absurd hr (by decide +kernel)

theorem agreeOnSeip (A : List Register) (rs0 rs ref : RegFile)
    (HA : ∀ r ∈ A, ¬ AxRunClose.pinReg r) (Hag : regsAgree AxRunClose.pinReg rs0 rs)
    (H : agreeOn A rs0 ref) : agreeOn A rs ref :=
  fun r hr => (Hag r (HA r hr)).symm.trans (H r hr)

section cjrAg
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem wpdCjrAfterLdAg (c : Ldc) (w : List (BitVec 8)) (tick : Bool) (i : Agent)
    (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch) (kk : Nat)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk (pcJr : Int) cjrVs4⌝)
    (rs : RegFile) (Hag : regsAgree AxRunClose.pinReg (ldOut c w) rs) :
    ⊢ ((∀ s', ⌜RetP cpu (fun rs3 => postRaSym (raOf c w) rs3 = true) kk s'⌝ -∗
          wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1, ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep tick) rs none ib, kk⟩ Φ := by
  obtain ⟨v', v, u', u, o⟩ := c
  cases tick
  · iintro R
    iapply (wpdCjrFrame (raOf _ w) i Φ cpu ib kk Hgd rs
      (agreeOnSeip _ _ _ _ seipNotinAJrFix Hag (ldOutAgreeJr _ w)))
    isplit
    · icases R with ⟨R, -⟩
      iintro %s' %Hs'
      iapply R $$ %s' %Hs'
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %_ %Hl
      iapply R $$ %GD %s1 %Hl
  · cases o with
    | none =>
      iintro R
      iapply (wpdCjrFrameTickGen i Φ cpu ib kk _ _ _ _ _ _ _ _ _
        (cjrRefFactsNone v' v u' u (raOf _ w)) (postRaSymLocal _) Hgd rs
        (agreeOnSeip _ _ _ _ seipNotinAJrT Hag (ldOutAgreeRef' _ w)))
      isplit
      · icases R with ⟨R, -⟩
        iintro %s' %Hs'
        iapply R $$ %s' %Hs'
      · icases R with ⟨-, R⟩
        iintro %GD %s1 %_ %Hl
        iapply R $$ %GD %s1 %Hl
    | some p =>
      obtain ⟨u2', u2⟩ := p
      iintro R
      iapply (wpdCjrFrameGenG true i Φ cpu ib kk _ _ _ _ _ _ _ _ _
        (cjrRefFactsSome v' v u' u u2' u2 (raOf _ w)) (postRaSymLocal _) Hgd rs
        (agreeOnSeip _ _ _ _ seipNotinAJrT Hag (ldOutAgreeRef' _ w)))
      isplit
      · icases R with ⟨R, -⟩
        iintro %s' %Hs'
        iapply R $$ %s' %Hs'
      · icases R with ⟨-, R⟩
        iintro %GD %s1 %_ %Hl
        iapply R $$ %GD %s1 %Hl

end cjrAg

/-! # 3. AT THE REAL OWNERSHIP PROTOCOL: c.sdsp ; c.ldsp, the reload's fragment indexed by the
read bytes, the reach at the start -/

section ownedRet
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [axG : AxirisG GF]
  [Axpol] [AxlogG GF Hent] [AxannotGS GF]

/-- `ldRb` at the read bytes `w` themselves. -/
def ldRbv (i : Agent) (k : Nat) (Vs w : List (BitVec 8)) : IProp GF :=
  iprop(∃ (GD : Gdexec),
    AxAnnot.annotOwn (i, k) iprop(⌜w = Vs⌝) ∗ ⌜graphValue GD (i, k) = some w⌝ ∗
      □ AxirisG.gconstInterp GD)

theorem ldspFlowOwnedResv (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (Hann_eq : ∀ m : Mea GF, AxirisG.annotInterp m ⊣⊢ AxAnnot.annotInterp m)
    (i : Agent) (k : Nat) (eSd : Geid) (Rsd : IProp GF) (a : Int) (Hs : List (List Hent))
    (Vs : List (BitVec 8)) (Hlen8 : Vs.length = 8) (Hlens : Hs.length = 8)
    (HlastSpill : ∀ (j : Nat) (H : List Hent), Hs[j]? = some H →
      ∃ v, H.getLast? = some (eSd, v) ∧ Vs[j]? = some v)
    (Hok : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜ldspOwnOk GD i k eSd a Hs⌝)
    (Htok : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢
        Rsd -∗ tokn γ GD a Hs ({[eSd := (1 : Qp)]} : GMapF Geid Qp))
    (Hloc : ∀ GD ls, rvwmoCatConsistent GD →
      AxirisG.localInterp (GF := GF) GD i k ls ⊢ |==> ∃ ls', AxirisG.localInterp GD i (k + 1) ls') :
    AxAnnot.annotOwn eSd Rsd ⊢
      ∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
        ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
        ⌜graphValue GD (i, k) = some v⌝ -∗ loadFlowRes GD i k iprop(⌜v = Vs⌝) (ldRbv i k Vs v) := by
  iintro Hfrag %GD %ls %v %Hc #Hg Hloc %Hgv
  ihave %Hok' := (Hok GD Hc) $$ Hg
  obtain ⟨Hlob, Hbef, Hrgmo, Hnw, Hpref, ⟨aq, ts0, vs0, Hlbl, Hts, Hvs⟩, Hwr, Hch, Hown, Hpo⟩ :=
    Hok'
  ihave Htok := (Htok GD Hc) $$ Hg
  unfold loadFlowRes naAtProgress
  iintro %na ⟨%Hprog, Hannot⟩
  ihave Hloc := (Hloc GD ls Hc) $$ Hloc
  imod Hloc with ⟨%ls', Hloc⟩
  have Hsd2 : eSd.2 < k := ((elemOfEidsBefore GD i k eSd).1 Hbef).2.1
  have Hin : eSd ∈ (FiniteMap.dom_set na : GSet Geid) := by
    rw [← Hprog] at Hbef
    exact (elemOfFilter.1 Hbef).2
  obtain ⟨P', HP'⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 Hin)
  ihave Hannot := (Hann_eq na).1 $$ Hannot
  have Hdet : ⊢ AxAnnot.annotInterp na -∗ AxAnnot.annotOwn eSd Rsd ==∗
      ∃ R, AxAnnot.annotInterp (insert na eSd R) ∗ iprop(▷ □ (P' -∗ Rsd ∗ R)) := by
    have h := annotDetach na eSd Rsd
    rw [HP'] at h
    exact h
  imod Hdet $$ Hannot Hfrag with ⟨%R, Hannot', Hwand⟩
  have Hnin : (i, k) ∉ (FiniteMap.dom_set (insert na eSd R) : GSet Geid) := by
    rw [domInsert, elemOfUnion, elemOfSingleton]
    rintro (Heq | Hik)
    · rw [← Heq] at Hsd2
      exact Nat.lt_irrefl _ Hsd2
    · have Hf : (i, k) ∈ FiniteSet.filter (fun e : Geid => decide (e.1 = i))
          (FiniteMap.dom_set na : GSet Geid) := elemOfFilter.2 ⟨by simp, Hik⟩
      rw [Hprog, elemOfEidsBefore] at Hf
      exact Nat.lt_irrefl _ Hf.2.1
  imod (annotAlloc (insert na eSd R) (i, k) iprop(⌜v = Vs⌝) Hnin) $$ Hannot' with
    ⟨Hannot'', Hfrag'⟩
  imodintro
  inext
  imodintro
  iexists {[eSd := Rsd]}, {[eSd := R]}, ls'
  isplitl [Hwand]
  · unfold naSplittingWf
    isplitr
    · ipureintro
      rw [domSingleton]
      exact singletonSubseteqL.2 Hlob
    · iapply (BigSepM2.bigSepM2_singleton _ eSd Rsd R).2
      simp only [HP', AxWp.fromOption]
      inext
      iexact Hwand
  isplitl [Htok]
  · unfold flowEqDyn
    iintro %σ %sOb %Hsub %Hnin' Hob Hin
    ihave Hin := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ Hin
    ihave Htoks := Htok $$ Hin
    ihave Hob := (Hob_eq GD σ sOb).1 $$ Hob
    icases Hob with #Hob
    ihave Hcovall : ∀ (j : Nat) (w : Geid) (v' : BitVec 8),
        ⌜gwritesByte GD.gdG w (a + (j : Int)) v'⌝ -∗ ⌜gmoLt GD.gdG w (i, k)⌝ -∗
        ∃ H' : List Hent, ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap (GF := GF) γ (a + (j : Int)) H' $$ []
    · iintro %j %w %v' %hwb %hmo
      ihave Hspec := protInvPrefixCovMem γ GD sOb (i, k) (a + (j : Int)) Hc.1 Hrgmo
        (subseteqTrans Hpref Hsub) $$ Hob
      ihave Hs2 := Hspec $$ %w %v' %hwb %hmo
      iexact Hs2
    have Hcase := epiHcaseDerived GD Hc (i, k) eSd a Vs Hs Hwr Hch Hown HlastSpill Hpo
    ihave %Hgv' := epiReloadValueOwn γ GD Hc eSd (i, k) a Vs Hlen8 Hs Hlens _ HlastSpill
      aq ts0 vs0 Hlbl Hts Hvs Hwr Hch Hown Hcase $$ Hcovall Htoks
    iapply fupd_mask_intro LawfulSet.empty_subset
    iintro Hclose
    inext
    imod Hclose
    imodintro
    iexists σ
    isplitl []
    · iapply (Hob_eq GD σ (({(i, k)} : GSet Geid) ∪ sOb)).2
      iapply protInvReadStep γ GD sOb (i, k) Hnin' Hnw
      iexact Hob
    · ipureintro
      rw [Hgv] at Hgv'
      exact Option.some.inj Hgv'
  isplitl [Hannot'']
  · iapply (Hann_eq _).2
    rw [← AxLdspWpd.annotEq]
    iexact Hannot''
  isplitl [Hloc]
  · iexact Hloc
  · unfold ldRbv
    iexists GD
    isplitl [Hfrag']
    · iexact Hfrag'
    isplitr
    · ipureintro
      exact Hgv
    · iexact Hg

/-- THE PROGRAM c.sdsp ; c.ldsp (; c.jr ; …) at the real protocol, REACH-STRENGTHENED AT THE
START (deviation 1): every row-end state at or after the reload receives `ldRbv i 1 sdData w`
for the bytes `w` the reload read, and owes `Φ` only if it is forward-reachable (`rstep G i`)
from the start state. -/
theorem wpdEpiRetOwnedRb (γ : GName)
    (Hob_eq : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
      AxirisG.obStInterp GD σ s ⊣⊢ protInv γ GD s)
    (Hann_eq : ∀ m : Mea GF, AxirisG.annotInterp m ⊣⊢ AxAnnot.annotInterp m)
    (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch) (a : Int)
    (Hs0 : List (List Hent))
    (Hgd_sd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i 0 (pcSd : Int) sdVs⌝)
    (Hrow_sd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜storeRowOk GD i 0⌝)
    (Hw_sd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜sdWriteOk GD i 0 a⌝)
    (Hloc_st : ∀ GD ls, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i 0 ls ⊢
        |==> ∃ ls', AxirisG.localInterp GD i 1 ls')
    (Hgd_ld : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢
        ⌜AxCjrWpd.fetchImgOk GD i 1 (pcLd : Int) AxEpiLedger.ldVs⌝)
    (Hrow_ld : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i 1⌝)
    (Hok_ld : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢
        ⌜ldspOwnOk GD i 1 (i, 0) a (writenHist (i, 0) sdData Hs0)⌝)
    (Hloc_ldv : ∀ GD ls, rvwmoCatConsistent GD →
      AxirisG.localInterp (GF := GF) GD i 1 ls ⊢ |==> ∃ ls', AxirisG.localInterp GD i 2 ls')
    (Hlens0 : Hs0.length = 8)
    (Hlen : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜(AxOpsem.grow GD i).length = 2⌝)
    (G : Gdexec → Prop)
    (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝) :
    ⊢ ([∗list] j ↦ H ∈ Hs0, histAuth γ (a + (j : Int)) 1 H) -∗
      (∀ (GD : Gdexec) s1, ⌜s1.atK ≤ 1⌝ -∗
         ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1) -∗
      (∀ w, ldRbv i 1 sdData w -∗ ∀ (GD : Gdexec) s1, ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗
         postLifting (fun s' => iprop(⌜rtc (rstep G i)
           ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ib, 0⟩ s'⌝ -∗ Φ s')) i s1) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ib, 0⟩ Φ := by
  have Hlen0 : Hs0.length = sdData.length := by rw [Hlens0]; rfl
  have Hlens1 : (writenHist (i, 0) sdData Hs0).length = 8 := by
    rw [writenHistLength]; exact Hlens0
  have Hlast := writenHistLastSpill (i, 0) sdData Hs0 Hlen0
  have Htok : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢
        sdTok γ a (writenHist (i, 0) sdData Hs0) (i, 0) -∗
          tokn γ GD a (writenHist (i, 0) sdData Hs0)
            ({[(i, 0) := (1 : Qp)]} : GMapF Geid Qp) := by
    intro GD _
    iintro _ Ht
    iapply (sdTokTokn γ GD a Hs0 (i, 0) sdData)
    iexact Ht
  have HlenLe : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜(AxOpsem.grow GD i).length ≤ 2⌝ := by
    intro GD Hc
    refine (Hlen GD Hc).trans ?_
    iintro %h
    ipureintro
    omega
  have HE : ∀ (rs : RegFile) (s0 : Athread), RetX cpu rs 2 s0 → s0.atK = 2 := by
    rintro rs s0 ⟨ib', Hk, -⟩
    exact Hk
  iintro Hauths Rpre Rpost
  iapply (wpdReachRtc .MaybeStuck i G Φ _ HG)
  iapply (wpdCsdspConcreteRes i _ cpu ib 0
    (AxAnnot.annotOwn (i, 0) (sdTok γ a (writenHist (i, 0) sdData Hs0) (i, 0))) Hgd_sd Hrow_sd)
    $$ [Hauths]
  · iapply (storeFlowOwned γ Hob_eq Hann_eq i 0 a Hs0 Hlen0 Hw_sd Hloc_st)
    iexact Hauths
  isplit
  · iintro HX %v' %v %s' %Hs'
    iapply (wpdRetBoundary i _ cpu _ 1 2 s' Hs' Hlen (by omega))
    iintro %s2 %Hs2
    obtain ⟨tick, rs', Hag, rfl⟩ := Hs2
    iapply (wpdCldspAfterSdResv i _ cpu ibNone 1 v' v (fun _ w => iprop(⌜w = sdData⌝))
      (ldRbv i 1 sdData) Hgd_ld Hrow_ld tick rs' Hag) $$ [HX]
    · iapply (ldspFlowOwnedResv γ Hob_eq Hann_eq i 1 (i, 0)
        (sdTok γ a (writenHist (i, 0) sdData Hs0) (i, 0)) a (writenHist (i, 0) sdData Hs0)
        sdData sdDataLength Hlens1 Hlast Hok_ld Htok Hloc_ldv)
      iexact HX
    isplit
    · iintro %w HXl
      ihave Rpost := Rpost $$ %w HXl
      isplit
      · iintro %c %s3 %Hs3
        iapply (wpdPastRowEnd i _ (RetX cpu (ldOut c w) 2) 2 s3 Hs3.2.2.2 (HE _) HlenLe)
        iintro %GD %s1 %_ %Heq
        iapply Rpost $$ %GD %s1 %Heq
      · iintro %GD %s1 %_ %Heq
        iapply Rpost $$ %GD %s1 %Heq
    · iintro %GD %s1 %Hb %Heq
      ihave H := Rpre $$ %GD %s1 %Hb %Heq
      iapply (postLiftingStrongMono Φ _ i s1) $$ H
      iintro %k Hk
      imodintro
      iintro _
      iexact Hk
  · iintro %GD %s1 %Hs1 %Heq
    ihave H := Rpre $$ %GD %s1 %(ledgerSdInvAtK _ _ _ _ _ _ _ _ Hs1) %Heq
    iapply (postLiftingStrongMono Φ _ i s1) $$ H
    iintro %k Hk
    imodintro
    iintro _
    iexact Hk

end ownedRet

end Weak
