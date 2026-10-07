/-
Weak: **`epiReloadSound`: a PIPELINE MILESTONE, NOT A SEPARATION RESULT.**

Rocq: `iris/AxEpiAdeq.v` @ xxvzwolszwmp.

## The Rocq header, in substance

With one hart the conclusion already follows from `graphValue` + `Hw_sd` + `Hok_ld` (Rocq
`AxEpiTrivial.epi_reload_trivial_1hart`, proved without WPd/`Hrun`).  What this theorem
certifies is that the conclusion is DERIVED THROUGH the logic and adequacy on the real Sail
model; it does not show ownership is needed.  Ownership becomes load-bearing only with a second
hart (Rocq: `epi_reload_sound2` / race2).

For every RVWMO-consistent graph `GD` whose hart-0 row is the concrete `c.sdsp ; c.ldsp`
program's events (plus the pure premises below), if hart 0's run reaches the row end, the reload
reads the spilled bytes: `graphValue GD (0, 1) = some sdData` (Lean positions, deviation 1).
Obtained from `tierAAdequacyAnnGmo` at `axGA2` with `obStInterp0 := fun γ GD _ s => protInv γ
GD s` (`N := GName`).

THE READBACK (why §1/§2 exist).  `postLifting` hands `Φ` the hart's bag for an ARBITRARY `na`;
to read the reload's deposit out of it one needs the annotation FRAGMENT
`annotOwn (0, 1) ⌜v = sdData⌝` at the row end (`annotAgree`, as `AxLock3Reader`'s readback).
`AxLdspWpd.ldspFlowOwned` allocates that fragment and DISCARDS it, and `loadFlow` has no channel
to hand it back.  So §1 restates the post-spill load chain (`wpdLoadStep` ..
`AxEpiOwned.wpdEpiSdLdRes`) with a RESOURCE-CARRYING load flow `loadFlowRes .. X` whose `X`
reaches the thread (mirroring `AxEpiOwned.storeFlowRes`), and whose row-end obligations are
split: states BEFORE the load get a plain obligation with an `atK` bound; states AFTER it get
`X`.  §2 is `ldspFlowOwned` keeping the fragment, and the capstone `wpdEpiSdLdOwnedRb`.

§3 instantiates adequacy at `axGA2` (`epiGa2`): `HobAlloc` (fresh `γ` + the 8 empty slot
histories), the policy `epiPol`, the readback, and the concrete camera list `epiGF`.  §4
(`EpiAdeqSat`): non-vacuity of the PURE premises at `AxEpiSdLdSat.gsdld`.

## Deviations from Rocq

1. O2 STAGE C (fetches are not graph events; `AxEpiOwned` deviation 1, `AxEpiSdLdSat`
   deviation 1): the row is `[sd @kk; ld @kk + 1]` (Rocq `[F0; SD; F1; LD]`).
   - §1 follows the Lean callees: `wpdLoadStepRes` is `wpdLoadStep` (`Hntext` ↦
     `Hnf : akIfetch = false`); `wpdLoadThenRetNRes`/`wpdLoadThenTickRes` are
     `wpdLoadThenRetN`/`wpdLoadThenTick`; `wpdFetchThenLoadRes`/`wpdFetchThenLoadTickRes` follow
     `wpdFetchThenLoad`/`wpdFetchThenLoadTick` (the fetch, the pre-load run and the load all at
     `k`, the `.pure ()`/tick tail at `k + 1`; `Hlat` of the fetch ↦ `Hfe : akIfetch = true`;
     `Hgd` states `AxCjrWpd.fetchImgOk`; the fetch's `Hflow`/`Hloc` DROPPED; `Hrow`/`F` at `k`,
     Rocq `S k`).  `wpdCldspStepOfLedgerAgreeRes`/`…TickRes`/`wpdCldspAfterSdRes`: `Hgd`,
     `Hrow`, `F` at `kk` (Rocq fetch `kk`, load `S kk`); `RetLd` at `kk + 1` (Rocq `S (S kk)`);
     the pre-load bound is `atK ≤ kk` (Rocq `≤ S kk`: the load's position either way);
     `Hflow`, `Hloc`, `Hntext` DROPPED.
   - `ledgerSdInvAtK`: `≤ kk + 1` (Rocq `≤ S (S kk)`: the store's `.pure ()` position).
   - `wpdEpiSdLdRes2`/`wpdEpiSdLdOwnedRb`: positions as `AxEpiOwned.wpdEpiSdLdRes`/
     `wpdEpiSdLdOwned` (store at `kk`, load at `kk + 1`, `Hlen = kk + 2`); the pre-load bound is
     `atK ≤ kk + 1` (Rocq `≤ S (S (S kk))`); `ldRb i (kk + 1) sdData` (Rocq `S (S (S kk))`);
     `Hflow_sd`, `Hloc_sd`, `Hflow_ld`, `Hloc_ld`, `Hntext` DROPPED.
   - §3: `epiPost GD i s := s.atK = 2 → graphValue GD (0, 1) = some sdData` (Rocq position 4,
     event `(0,3)`); `wpdEpiGa2`/`epiReloadSound` take `fetchImgOk GD 0 0 pcSd sdVs`,
     `storeRowOk GD 0 0`, `sdWriteOk GD 0 0 a`, `fetchImgOk GD 0 1 pcLd ldVs`,
     `loadRowOk GD 0 1`, `ldspOwnOk GD 0 1 (0,0) a (writenHist (0,0) sdData epiHs0)`,
     `length (grow GD 0) = 2`, `Hlob_gmo : gmoLt (0,0) (0,1)` (Rocq `fetch_gd_ok … 0 0`,
     `store_row_ok … 0 1`, `sd_write_ok … 0 1`, `fetch_gd_ok … 0 2`, `load_row_ok … 0 3`,
     `ldsp_own_ok … 0 3 (0,1)`, length 4, `gmo_lt (0,1) (0,3)`).  The fetch-event premises
     `Hnw_sd`/`Hnw_ld` (`gis_w` of `(0,0)`/`(0,2)`) and `Hntext` are DROPPED (no fetch event,
     no `ax_text`), and the text parameter `T` is gone (`axGA2`/`tierAAstep` have none, AxTierA2
     deviation 2).
   - `fetchFlowGa2` is ported (downstream Rocq files use it) though no Lean callee takes a fetch
     flow any more; `fetchFlow` is `AxCjrWpd`'s (kept verbatim there).
   - §4: `gsdldSdWriteOk : sdWriteOk gsdld 0 0 ldAddr`, `gsdldLdspOwnOk` at `0 1 (0,0)`,
     `gsdldHs1` at `(0,0)`; `epiReloadPremisesGsdld` bundles exactly `epiReloadSound`'s pure
     premises (so the two `gis_w` fetch conjuncts and `¬ sdld_text ld_addr` are dropped, as in
     deviation 1).
2. THE TWO-PIN BOUNDARY (`AxEpiLedger` deviation 1): the store's exit is indexed by `v' v`
   (`wpdCldspAfterSdRes` takes `v' v`), the ledger splits run as in the Lean non-`Res` lemmas.
3. THE PINS (`AxRunClose` deviation 1): `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg`;
   the `epure` lemmas take both `sig_seip ∉ D` and `sig_meip ∉ D`.
4. TYPES (as `AxEpiOwned` deviation 4): request types carry `va`; `inl (w, None)` ↦
   `.Ok (w, none)`; `Ret tt` ↦ `.pure ()`; `S k` ↦ `k + 1`; `WPd … @ MaybeStuck; i {{ Φ }}` ↦
   `wpd .MaybeStuck i s Φ`; `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` (§3's `Hwp` at
   `.hasNoLC`); `A -∗ B` ↦ `⊢ A -∗ B`; `(i, k) ↦ₐ P` ↦ `AxAnnot.annotOwn (i, k) P`; `Z.of_nat j`
   ↦ `(j : Int)`; `replicate 8 []` ↦ `List.replicate 8 []`.  §2/§3 are at
   `GF : BundledGFunctors.{0,0,0}`.
5. CONTEXTS: §2's section context `γ`, `Hob_eq`, `Hann_eq` are explicit arguments (as
   `AxEpiOwned` deviation 5); `ldRb` takes none of them.  §3: Rocq's section `GD0 T γ` ↦
   explicit `GD0 γ`; Rocq's `Local Instance epi_ga2` is the reducible def `epiGa2 GD0 γ`, passed
   explicitly; `Local Existing Instance EpiSat.epi_pol` is NOT replicated — §3's lemmas are
   stated at an arbitrary `[Axpol]` (a generalisation: Rocq's statements are their `epiPol`
   instances), and `epiReloadSound` passes `epiPol` explicitly to `tierAAdequacyAnnGmo`.
6. CAMERAS: `epiΣ := #[invΣ; axlogΣ hent; axannotΣ]` ↦ `epiGF`, an explicit slot table over
   `BundledGFunctors.default` (as `AxTokLedgerMp.mprGF`): wsat + credits at 0–3, the byte logs
   `AxlogRF Hent` at 4, the annotation cameras at 5–7; instances `AxEpiAdeq.epiGF*`.
   `epiHobAlloc` ALLOCATES the slot histories (`histAlloc` over the 8 slot addresses).
7. `epiReloadSound`'s `Hrun` is `∀ (_ : AxannotGS epiGF) (nm : GName), nsteps (tierAAstep GD nm
   0) n s0 sN` (Rocq `tierA_astep (Hann:=Hann) GD T gname unit epi_ob_interp nm 0`; Lean's
   `tierAAstep` takes neither the instance nor `T`).
8. PROOF ROUTE (not statements): `vm_compute` ↦ `decide +kernel`.

**Rocq → Lean name map.**  §1 `load_flow_res` `loadFlowRes`, `wpd_load_step_res`
`wpdLoadStepRes`, `wpd_load_then_ret_n_res` `wpdLoadThenRetNRes`, `wpd_fetch_then_load_res`
`wpdFetchThenLoadRes`, `wpd_cldsp_step_of_ledger_agree_res` `wpdCldspStepOfLedgerAgreeRes`,
`wpd_load_then_tick_res` `wpdLoadThenTickRes`, `wpd_fetch_then_load_tick_res`
`wpdFetchThenLoadTickRes`, `wpd_cldsp_step_of_ledger_tick_res` `wpdCldspStepOfLedgerTickRes`,
`wpd_cldsp_after_sd_res` `wpdCldspAfterSdRes`, `ledger_sd_inv_at_k` `ledgerSdInvAtK`,
`wpd_epi_sd_ld_res2` `wpdEpiSdLdRes2`.  §2 `ld_rb` `ldRb`, `ldsp_flow_owned_res`
`ldspFlowOwnedRes`, `wpd_epi_sd_ld_owned_rb` `wpdEpiSdLdOwnedRb`.  §3 `epiΣ` `epiGF`, `epi_Hs0`
`epiHs0`, `epi_init` `epiInit`, `epi_ob_interp` `epiObInterp`, `epi_post` `epiPost`, `epi_ga2`
`epiGa2`, `pin_ga2` `pinGa2`, `loc_ga2` `locGa2`, `loc_ga2'` `locGa2'`, `ob_eq_ga2` `obEqGa2`,
`ann_eq_ga2` `annEqGa2`, `fetch_flow_ga2` `fetchFlowGa2`, `wpd_epi_ga2` `wpdEpiGa2`,
`epi_Hob_alloc` `epiHobAlloc`, `epi_reload_sound` `epiReloadSound`.  §4 (`Module EpiAdeqSat` ↦
plain names) `gsdld_Hs1` `gsdldHs1`, `gsdld_Hs1_lookup` `gsdldHs1Lookup`, `gsdld_sd_write_ok`
`gsdldSdWriteOk`, `gsdld_ldsp_own_ok` `gsdldLdspOwnOk`, `epi_reload_premises_gsdld`
`epiReloadPremisesGsdld`.  None is in the duplicated-name table.  Lean-only (file-qualified):
`AxEpiAdeq.pseipMeipAtK`, `AxEpiAdeq.epiInit0`, the seven `AxEpiAdeq.epiGF*` instances.

**Dropped:** nothing (Rocq 34 definitions/lemmas; Lean 34 + 2 Lean-only helpers + 7 instances).  **Not ported:**
the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxEpiOwned
import Weak.AxEpiSdLdSat
import Weak.AxEpiSat

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Wlabel

/-! # 1. THE RESOURCE-CARRYING LOAD CHAIN (generic `AxirisG`/`Axpol`) -/

/-- (Lean-only) The `sig_meip` split's states sit at the instruction's position. -/
theorem AxEpiAdeq.pseipMeipAtK (cpu : CPU) (km : RegisterType Register.sig_meip → SailM Unit)
    (t0 : ExecSt) (rs : RegFile) (ib : Ibch) (kk : Nat) (s : Athread) :
    Pseip (AxEpiLedger.meipNode cpu km rs ib kk) (AxEpiLedger.seipExit cpu km t0 kk) s →
    s.atK = kk := by
  rintro (H | H | ⟨q, ⟨v', k0, t1, ib1, -, rfl⟩, H⟩)
  · exact pbeforeAtK _ _ H
  · exact H.1
  · exact pbeforeAtK _ _ H

section resLd
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- `loadFlow` that additionally hands `X` back to the thread. -/
def loadFlowRes (GD : Gdexec) (i : Agent) (k : Nat) (R X : IProp GF) : IProp GF :=
  iprop(∀ na, naAtProgress GD i k na ∗ AxirisG.annotInterp na -∗ |==> ▷ |==>
    ∃ (naUsed naUnused : Mea GF) (ls' : AxirisG.logTsT GF),
      naSplittingWf (Axpol.lobp GD (i, k)) na naUsed naUnused ∗
      flowEqDyn GD (i, k) (Axpol.sPol GD (i, k)) naUsed R ∗
      AxirisG.annotInterp (PartialMap.union (PartialMap.union {[(i, k) := R]} naUnused) na) ∗
      AxirisG.localInterp GD i (k + 1) ls' ∗ X)

theorem wpdLoadStepRes (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (rs0 : RegFile) (Rv : Gdexec → List (BitVec 8) → IProp GF) (X : IProp GF)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hn : 0 < n) (Hnf : (classify req.access_kind).akIfetch = false)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i k⌝) :
    ⊢ ∀ rs, ⌜regsAgree AxRunClose.pinReg rs0 rs⌝ -∗
      (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
         ⌜graphValue GD (i, k) = some v⌝ -∗ loadFlowRes GD i k (Rv GD v) X) -∗
      (∀ (v : List (BitVec 8)) (rs' : RegFile), ⌜v.length = n⌝ -∗
         ⌜regsAgree AxRunClose.pinReg rs0 rs'⌝ -∗ X -∗
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

theorem wpdLoadThenRetNRes (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (nl va : Nat)
    (req : Mem_read_request nl va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * nl) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (sLd : ExecSt) (D : List Register) (Rv : Gdexec → List (BitVec 8) → IProp GF)
    (X : IProp GF)
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
         ⌜graphValue GD (i, k) = some v⌝ -∗ loadFlowRes GD i k (Rv GD v) X) -∗
      (X -∗
       ((∀ (x : BitVec (8 * nl)) (sEnd : ExecSt) (ib' : Ibch) (s' : Athread),
          ⌜epure D (KK (.Ok (x, none))) sLd = some ((), sEnd)⌝ -∗
          ⌜Qat ⟨.PHart cpu (.pure ()) sEnd.regs none ib', k + 1⟩ s'⌝ -∗
          wpd .MaybeStuck i s' Φ) ∧
        (∀ (x : BitVec (8 * nl)) (sEnd : ExecSt) (ib' : Ibch) (GD : Gdexec) (s1 : Athread),
          ⌜epure D (KK (.Ok (x, none))) sLd = some ((), sEnd)⌝ -∗
          ⌜Pbefore ⟨.PHart cpu (.pure ()) sEnd.regs none ib', k + 1⟩ s1⌝ -∗
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
    iapply (wpdLoadStepRes Φ i cpu nl va req KK ib k sLd.regs Rv X Hdev Hlat Hn Hnf Hrow) $$
      %rs2 %(regsAgreeSym _ _ _ hag) F
    iintro %v %rs' %Hlv %hag' HX
    ihave R := R $$ HX
    obtain ⟨sEnd, Hep⟩ := Hpost (wordOfBytes nl v)
    obtain ⟨ib', Hrun⟩ := epureGstepRtc D Hseip Hmeip _ _ _ _ Hep cpu ib (k + 1)
    iapply (wpdRunTo Φ i _ _ Hrun) $$
      %⟨.PHart cpu (KK (.Ok (wordOfBytes nl v, none))) rs' none ib, k + 1⟩
      %⟨rfl, rfl, rfl, rfl, rfl, regsAgreeSym _ _ _ hag'⟩
    isplit
    · icases R with ⟨R, -⟩
      iintro %s3 %Hq3
      iapply R $$ %(wordOfBytes nl v) %sEnd %ib' %s3 %Hep %Hq3
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %Hb %Hend
      iapply R $$ %(wordOfBytes nl v) %sEnd %ib' %GD %s1 %Hep %Hb %Hend

theorem wpdFetchThenLoadRes (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KKf : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (vs : List (BitVec 8)) (rs0 rs : RegFile) (nl val : Nat)
    (reql : Mem_read_request nl val Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * nl) × Option Bool) Arch.abort → SailM Unit) (ibLd : Ibch)
    (tl : ExecSt) (D : List Register) (Rv : Gdexec → List (BitVec 8) → IProp GF) (X : IProp GF)
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
         ⌜graphValue GD (i, k) = some v⌝ -∗ loadFlowRes GD i k (Rv GD v) X) -∗
      ((X -∗
        ((∀ (x : BitVec (8 * nl)) (sEnd : ExecSt) (ib' : Ibch) (s' : Athread),
           ⌜epure D (KK (.Ok (x, none))) tl = some ((), sEnd)⌝ -∗
           ⌜Qat ⟨.PHart cpu (.pure ()) sEnd.regs none ib', k + 1⟩ s'⌝ -∗
           wpd .MaybeStuck i s' Φ) ∧
         (∀ (x : BitVec (8 * nl)) (sEnd : ExecSt) (ib' : Ibch) (GD : Gdexec) (s1 : Athread),
           ⌜epure D (KK (.Ok (x, none))) tl = some ((), sEnd)⌝ -∗
           ⌜Pbefore ⟨.PHart cpu (.pure ()) sEnd.regs none ib', k + 1⟩ s1⌝ -∗
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
    iapply (wpdLoadThenRetNRes Φ i cpu nl val reql KK ibLd k tl D Rv X Hdevl Hlatl Hn Hnfl Hrow
      Hseip Hmeip Hpost) $$ %s3 %Hq3 F R
  · icases R with ⟨-, R⟩
    iexact R

/-- `wpdCldspStepOfLedgerAgree` with the resource-carrying load: states before the load get a
plain obligation with the bound `atK ≤ kk`; states after it get `X`. -/
theorem wpdCldspStepOfLedgerAgreeRes (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
    (ib : Ibch) (kk : Nat) (t : ExecSt) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (postLd : Int → RegFile → Prop)
    (Rv : Gdexec → List (BitVec 8) → IProp GF) (X : IProp GF)
    (L : AxLdModelFacts t Dr Dw D base vs ldaddr postLd)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk base vs⌝)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i kk⌝)
    (rs : RegFile) (Hag0 : regsAgree AxRunClose.pinReg t.regs rs) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i kk ls -∗
         ⌜graphValue GD (i, kk) = some v⌝ -∗ loadFlowRes GD i kk (Rv GD v) X) -∗
      ((X -∗ ((∀ s', ⌜RetLd cpu postLd (kk + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
               (∀ (GD : Gdexec) s1, ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗
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
        iapply (wpdFetchThenLoadRes Φ i cpu n va req KKf ib2 kk vs t2.regs rs3 nl val reql KK
          ibLd tl D Rv X Hdev Hfe Hlen Hgd (regsAgreeSym _ _ _ hag) HrunPre Hdevl Hlatl Hn Hnfl
          Hrow HD HDm Hpost) $$ F
        isplit
        · icases R with ⟨R, -⟩
          iintro HX
          ihave R := R $$ HX
          isplit
          · icases R with ⟨R, -⟩
            iintro %x %sEnd %ib3 %s' %Hep %Hs'
            obtain ⟨sEnd', Hep', Hpost'⟩ := Hx x
            rw [Hep, Option.some.injEq, Prod.mk.injEq] at Hep'
            obtain ⟨-, rfl⟩ := Hep'
            iapply R $$ %s' %⟨_, sEnd.regs, ib3, Hpost', Hs'⟩
          · icases R with ⟨-, R⟩
            iintro %x %sEnd %ib3 %GD %s1 %Hep %Hs1 %Hlen1
            iapply R $$ %GD %s1 %Hlen1
        · icases R with ⟨-, R⟩
          iintro %GD %s1 %Hs1 %Hlen1
          iapply R $$ %GD %s1 %(Nat.le_of_eq (pbeforeAtK _ _ Hs1)) %Hlen1
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %Hs1 %Hlen1
      iapply R $$ %GD %s1 %(Nat.le_of_eq (pseipErdAtK _ _ _ _ _ _ _ _ _ Hs1)) %Hlen1
  · icases R with ⟨-, R⟩
    iintro %GD %s1 %Hs1 %Hlen1
    iapply R $$ %GD %s1 %(Nat.le_of_eq (AxEpiAdeq.pseipMeipAtK _ _ _ _ _ _ _ Hs1)) %Hlen1

theorem wpdLoadThenTickRes (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (nl va : Nat)
    (req : Mem_read_request nl va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * nl) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (sLd : ExecSt) (D : List Register) (postLd : Int → RegFile → Prop)
    (Rv : Gdexec → List (BitVec 8) → IProp GF) (X : IProp GF)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hn : 0 < nl) (Hnf : (classify req.access_kind).akIfetch = false)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i k⌝)
    (HD : Register.sig_seip ∉ D) (HDm : Register.sig_meip ∉ D)
    (Hx : ∀ x : BitVec (8 * nl), tickPostOk D (postLd (x.toNat : Int)) (KK (.Ok (x, none))) sLd) :
    ⊢ ∀ s2, ⌜Qat ⟨.PHart cpu (.impure (.ok (.memRead nl va req)) KK) sLd.regs none ib, k⟩ s2⌝ -∗
      (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
         ⌜graphValue GD (i, k) = some v⌝ -∗ loadFlowRes GD i k (Rv GD v) X) -∗
      (X -∗
       ((∀ s', ⌜RetLd cpu postLd (k + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
        (∀ (x : BitVec (8 * nl)) (GD : Gdexec) (s1 : Athread),
          ⌜tickTailInv D cpu (KK (.Ok (x, none))) sLd (k + 1) s1⌝ -∗
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
    iapply (wpdLoadStepRes Φ i cpu nl va req KK ib k sLd.regs Rv X Hdev Hlat Hn Hnf Hrow) $$
      %rs2 %(regsAgreeSym _ _ _ hag) F
    iintro %v %rs' %Hlv %hag' HX
    ihave R := R $$ HX
    iapply (wpdTickTail i Φ cpu _ sLd ib (k + 1) D _ HD HDm (Hx (wordOfBytes nl v)) rs' hag')
    isplit
    · icases R with ⟨R, -⟩
      iintro %s' %Hs'
      obtain ⟨rs3, ib', Hp, Hq'⟩ := Hs'
      iapply R $$ %s' %⟨_, rs3, ib', Hp, Hq'⟩
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %Hs1 %Hl
      iapply R $$ %(wordOfBytes nl v) %GD %s1 %Hs1 %Hl

theorem wpdFetchThenLoadTickRes (Φ : Athread → IProp GF) (i : Agent) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KKf : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (vs : List (BitVec 8)) (rs0 rs : RegFile) (nl val : Nat)
    (reql : Mem_read_request nl val Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * nl) × Option Bool) Arch.abort → SailM Unit) (ibLd : Ibch)
    (tl : ExecSt) (D : List Register) (postLd : Int → RegFile → Prop)
    (Rv : Gdexec → List (BitVec 8) → IProp GF) (X : IProp GF)
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
         ⌜graphValue GD (i, k) = some v⌝ -∗ loadFlowRes GD i k (Rv GD v) X) -∗
      ((X -∗
        ((∀ s', ⌜RetLd cpu postLd (k + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
         (∀ (x : BitVec (8 * nl)) (GD : Gdexec) (s1 : Athread),
           ⌜tickTailInv D cpu (KK (.Ok (x, none))) tl (k + 1) s1⌝ -∗
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
    iapply (wpdLoadThenTickRes Φ i cpu nl val reql KK ibLd k tl D postLd Rv X Hdevl Hlatl Hn
      Hnfl Hrow HD HDm Hx) $$ %s3 %Hq3 F R
  · icases R with ⟨-, R⟩
    iexact R

theorem wpdCldspStepOfLedgerTickRes (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
    (ib : Ibch) (kk : Nat) (t : ExecSt) (Dr Dw D : List Register) (base : Int)
    (vs : List (BitVec 8)) (ldaddr : Int) (postLd : Int → RegFile → Prop)
    (Rv : Gdexec → List (BitVec 8) → IProp GF) (X : IProp GF)
    (L : AxLdTickFacts t Dr Dw D base vs ldaddr postLd)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk base vs⌝)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i kk⌝)
    (rs : RegFile) (Hag0 : regsAgree AxRunClose.pinReg t.regs rs) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (v : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i kk ls -∗
         ⌜graphValue GD (i, kk) = some v⌝ -∗ loadFlowRes GD i kk (Rv GD v) X) -∗
      ((X -∗ ((∀ s', ⌜RetLd cpu postLd (kk + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
               (∀ (GD : Gdexec) s1, ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗
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
        iapply (wpdFetchThenLoadTickRes Φ i cpu n va req KKf ib2 kk vs t2.regs rs3 nl val reql KK
          ibLd tl D postLd Rv X Hdev Hfe Hlen Hgd (regsAgreeSym _ _ _ hag) HrunPre Hdevl Hlatl Hn
          Hnfl Hrow HD HDm Hx) $$ F
        isplit
        · icases R with ⟨R, -⟩
          iintro HX
          ihave R := R $$ HX
          isplit
          · icases R with ⟨R, -⟩
            iexact R
          · icases R with ⟨-, R⟩
            iintro %x %GD %s1 %Hs1 %Hlen1
            iapply R $$ %GD %s1 %Hlen1
        · icases R with ⟨-, R⟩
          iintro %GD %s1 %Hs1 %Hlen1
          iapply R $$ %GD %s1 %(Nat.le_of_eq (pbeforeAtK _ _ Hs1)) %Hlen1
    · icases R with ⟨-, R⟩
      iintro %GD %s1 %Hs1 %Hlen1
      iapply R $$ %GD %s1 %(Nat.le_of_eq (pseipErdAtK _ _ _ _ _ _ _ _ _ Hs1)) %Hlen1
  · icases R with ⟨-, R⟩
    iintro %GD %s1 %Hs1 %Hlen1
    iapply R $$ %GD %s1 %(Nat.le_of_eq (AxEpiAdeq.pseipMeipAtK _ _ _ _ _ _ _ Hs1)) %Hlen1

/-- Both ticks, right after the c.sdsp. -/
theorem wpdCldspAfterSdRes (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch)
    (kk : Nat) (v' v : BitVec 1) (Rv : Gdexec → List (BitVec 8) → IProp GF) (X : IProp GF)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢
        ⌜AxCjrWpd.fetchImgOk GD i kk (pcLd : Int) AxEpiLedger.ldVs⌝)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i kk⌝)
    (tick : Bool) (rs : RegFile) (Hag : regsAgree AxRunClose.pinReg (tAfterSd v' v).regs rs) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (w : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i kk ls -∗
         ⌜graphValue GD (i, kk) = some w⌝ -∗ loadFlowRes GD i kk (Rv GD w) X) -∗
      ((X -∗ ((∀ s', ⌜RetLd cpu ldPost (kk + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
               (∀ (GD : Gdexec) s1, ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗
                  postLifting Φ i s1))) ∧
       (∀ (GD : Gdexec) s1, ⌜s1.atK ≤ kk⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep tick) rs none ib, kk⟩ Φ := by
  cases tick
  · exact wpdCldspStepOfLedgerAgreeRes i Φ cpu ib kk (tAfterSd v' v) _ _ _ _ _ _ _ Rv X
      (epiLedgerCldspAfterSd v' v) Hgd Hrow rs Hag
  · exact wpdCldspStepOfLedgerTickRes i Φ cpu ib kk (tAfterSd v' v) _ _ _ _ _ _ _ Rv X
      (epiLedgerCldspTick v' v) Hgd Hrow rs Hag

end resLd

/-- The store's row-end states sit at or before the store's `.pure ()`. -/
theorem ledgerSdInvAtK (t : ExecSt) (Dr Dw D : List Register) (vs : List (BitVec 8)) (cpu : CPU)
    (kk : Nat) (s1 : Athread) :
    ledgerSdInv t Dr Dw D vs cpu kk s1 → s1.atK ≤ kk + 1 := by
  rintro ⟨km, t0, ib0, -, Hp | ⟨v', k0, t1, ib1, -, Hp | ⟨v, n, va, req, KKf, t2, nw, vaw, reqw,
    KK, tw, ibW, -, -, Hp | ⟨t3, ib', -, Hp⟩⟩⟩⟩
  · have := AxEpiAdeq.pseipMeipAtK _ _ _ _ _ _ _ Hp; omega
  · have := pseipErdAtK _ _ _ _ _ _ _ _ _ Hp; omega
  · have := pbeforeAtK _ _ Hp; simp only at this; omega
  · have := pbeforeAtK _ _ Hp; simp only at this; omega

section resLd2
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- `AxEpiOwned.wpdEpiSdLdRes` with the load flow ALSO returning a resource `Xl`, delivered to
every post-load row-end state. -/
theorem wpdEpiSdLdRes2 (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch) (kk : Nat)
    (Rv : Gdexec → List (BitVec 8) → IProp GF) (Xs Xl : IProp GF)
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
         storeFlowRes GD i kk sdData Xs) -∗
      (Xs -∗ ∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (w : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗
         AxirisG.localInterp GD i (kk + 1) ls -∗
         ⌜graphValue GD (i, kk + 1) = some w⌝ -∗ loadFlowRes GD i (kk + 1) (Rv GD w) Xl) -∗
      (∀ (GD : Gdexec) s1, ⌜s1.atK ≤ kk + 1⌝ -∗
         ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1) -∗
      (Xl -∗ ∀ (GD : Gdexec) s1, ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1) -∗
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
  iintro Fs Fl Rpre Rpost
  iapply (wpdCsdspConcreteRes i Φ cpu ib kk Xs Hgd_sd Hrow_sd) $$ Fs
  isplit
  · iintro HX %v' %v %s' %Hs'
    iapply (wpdRetBoundary i Φ cpu _ (kk + 1) (kk + 2) s' Hs' Hlen (by omega))
    iintro %s2 %Hs2
    obtain ⟨tick, rs', Hag, rfl⟩ := Hs2
    ihave Fl2 := Fl $$ HX
    iapply (wpdCldspAfterSdRes i Φ cpu ibNone (kk + 1) v' v Rv Xl Hgd_ld Hrow_ld tick rs' Hag) $$
      Fl2
    isplit
    · iintro HXl
      ihave Rpost := Rpost $$ HXl
      isplit
      · iintro %s3 %Hs3
        iapply (wpdPastRowEnd i Φ (RetLd cpu ldPost (kk + 2)) (kk + 2) s3 Hs3 HE HlenLe)
        iintro %GD %s1 %_ %Heq
        iapply Rpost $$ %GD %s1 %Heq
      · iexact Rpost
    · iintro %GD %s1 %Hb %Heq
      iapply Rpre $$ %GD %s1 %Hb %Heq
  · iintro %GD %s1 %Hs1 %Heq
    iapply Rpre $$ %GD %s1 %(ledgerSdInvAtK _ _ _ _ _ _ _ _ Hs1) %Heq

end resLd2

/-! # 2. AT THE REAL OWNERSHIP PROTOCOL: the reload KEEPS its fragment -/

section ownedRb
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [axG : AxirisG GF]
  [Axpol] [AxlogG GF Hent] [AxannotGS GF]

/-- What the reload hands back: its own annotation fragment, the graph value it was made at,
and that graph's `gconstInterp`. -/
def ldRb (i : Agent) (k : Nat) (Vs : List (BitVec 8)) : IProp GF :=
  iprop(∃ (GD : Gdexec) (v : List (BitVec 8)),
    AxAnnot.annotOwn (i, k) iprop(⌜v = Vs⌝) ∗ ⌜graphValue GD (i, k) = some v⌝ ∗
      □ AxirisG.gconstInterp GD)

/-- `AxLdspWpd.ldspFlowOwned`, keeping the reload's fragment. -/
theorem ldspFlowOwnedRes (γ : GName)
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
        ⌜graphValue GD (i, k) = some v⌝ -∗ loadFlowRes GD i k iprop(⌜v = Vs⌝) (ldRb i k Vs) := by
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
  · unfold ldRb
    iexists GD, v
    isplitl [Hfrag']
    · iexact Hfrag'
    isplitr
    · ipureintro
      exact Hgv
    · iexact Hg

/-- THE CAPSTONE WITH READBACK: `AxEpiOwned.wpdEpiSdLdOwned` whose post-reload row-end
obligation receives `ldRb`. -/
theorem wpdEpiSdLdOwnedRb (γ : GName)
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
      (∀ (GD : Gdexec) s1, ⌜s1.atK ≤ kk + 1⌝ -∗
         ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1) -∗
      (ldRb i (kk + 1) sdData -∗
         ∀ (GD : Gdexec) s1, ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1) -∗
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
  iintro Hauths Rpre Rpost
  iapply (wpdEpiSdLdRes2 i Φ cpu ib kk (fun _ w => iprop(⌜w = sdData⌝))
    (AxAnnot.annotOwn (i, kk) (sdTok γ a (writenHist (i, kk) sdData Hs0) (i, kk)))
    (ldRb i (kk + 1) sdData) Hgd_sd Hrow_sd Hgd_ld Hrow_ld Hlen) $$ [Hauths] [] Rpre Rpost
  · iapply (storeFlowOwned γ Hob_eq Hann_eq i kk a Hs0 Hlen0 Hw_sd Hloc_st)
    iexact Hauths
  · iintro Hf
    iapply (ldspFlowOwnedRes γ Hob_eq Hann_eq i (kk + 1) (i, kk)
      (sdTok γ a (writenHist (i, kk) sdData Hs0) (i, kk)) a (writenHist (i, kk) sdData Hs0)
      sdData sdDataLength Hlens1 Hlast Hok_ld Htok Hloc_ldv)
    iexact Hf

end ownedRb

/-! # 3. ADEQUACY AT `axGA2` -/

section epiGFSec
open Iris Iris.BI Iris.Std Std MachCSL COFE

/-- Rocq `epiΣ := #[invΣ; axlogΣ hent; axannotΣ]` (header deviation 6). -/
def epiGF : BundledGFunctors :=
  BundledGFunctors.default
  |>.set 0 ⟨InvMapF, inferInstance⟩
  |>.set 1 ⟨constOF CoPsetDisjL, inferInstance⟩
  |>.set 2 ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  |>.set 3 ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  |>.set 4 ⟨AxlogRF Hent, inferInstance⟩
  |>.set 5 ⟨DFracAgree.DFracAgreeRF (LaterOF IdOF), inferInstance⟩
  |>.set 6 ⟨constOF (HeapView Geid (Agree (DiscreteO GName)) (GMapF Geid)), inferInstance⟩
  |>.set 7 ⟨constOF AxannotSetR, inferInstance⟩

instance AxEpiAdeq.epiGFInvMap : ElemG epiGF InvMapF := ⟨0, rfl⟩
instance AxEpiAdeq.epiGFEnabled : ElemG epiGF (constOF CoPsetDisjL) := ⟨1, rfl⟩
instance AxEpiAdeq.epiGFDisabled : ElemG epiGF (constOF (DisjointLeibnizSet PosSet)) :=
  ⟨2, rfl⟩
instance AxEpiAdeq.epiGFCredit : ElemG epiGF (Auth.AuthURF (constOF Credit)) := ⟨3, rfl⟩
instance AxEpiAdeq.epiGFInvGpreS : InvGpreS epiGF :=
  ⟨⟨inferInstance, inferInstance, inferInstance⟩, ⟨inferInstance⟩⟩
instance AxEpiAdeq.epiGFAxlogG : AxlogG epiGF Hent := ⟨⟨4, rfl⟩⟩
instance AxEpiAdeq.epiGFAxannotG : AxannotG epiGF :=
  { axannotSavedG := { elemG := ⟨5, rfl⟩ }, axannotMapG := ⟨⟨6, rfl⟩⟩, axannotSetG := ⟨7, rfl⟩ }

end epiGFSec

/-- The 8 empty pre-spill histories of the slot bytes. -/
def epiHs0 : List (List Hent) := List.replicate 8 []

def epiInit {GF : BundledGFunctors} [AxlogG GF Hent] (a : Int) (γ : GName) (i : Agent) :
    IProp GF :=
  if i = 0 then iprop([∗list] j ↦ H ∈ epiHs0, histAuth γ (a + (j : Int)) 1 H) else iprop(emp)

/-- (Lean-only) hart 0's initial resources. -/
theorem AxEpiAdeq.epiInit0 {GF : BundledGFunctors} [AxlogG GF Hent] (a : Int) (γ : GName) :
    epiInit (GF := GF) a γ 0 ⊣⊢ iprop([∗list] j ↦ H ∈ epiHs0, histAuth γ (a + (j : Int)) 1 H) :=
  .rfl

/-- The protocol state as the adequacy instance's ob-state interpretation (an `abbrev`, so the
proof mode sees `protInv` through it). -/
abbrev epiObInterp {GF : BundledGFunctors} [AxlogG GF Hent] (γ : GName) (GD : Gdexec) (_ : Unit)
    (s : GSet Geid) : IProp GF :=
  protInv γ GD s

/-- The post: at the row end (position 2), the reload read the spill. -/
def epiPost (GD : Gdexec) (_i : Agent) (s : Athread) : Prop :=
  s.atK = 2 → graphValue GD (0, 1) = some sdData

section ga2
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxlogG GF Hent] [pol : Axpol]

/-- Rocq `Local Instance epi_ga2` (a named reducible def here). -/
@[reducible] def epiGa2 (GD0 : Gdexec) (γ : GName) : AxirisG GF :=
  axGA2 GD0 GName Unit epiObInterp γ

theorem pinGa2 (GD0 : Gdexec) (γ : GName) (P : Gdexec → Prop) (HP : P GD0) :
    ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (self := epiGa2 (GF := GF) GD0 γ) GD ⊢ ⌜P GD⌝ := by
  intro GD _
  show iprop(⌜GD = GD0⌝) ⊢ iprop(⌜P GD⌝)
  iintro %h
  subst h
  ipureintro
  exact HP

theorem locGa2 (GD0 : Gdexec) (γ : GName) (GD : Gdexec) (i : Agent) (k : Nat)
    (ls : @AxirisG.logTsT GF (epiGa2 GD0 γ)) :
    AxirisG.gconstInterp (self := epiGa2 (GF := GF) GD0 γ) GD ∗
        AxirisG.localInterp (self := epiGa2 (GF := GF) GD0 γ) GD i k ls ⊢
      |==> ∃ ls', AxirisG.localInterp (self := epiGa2 (GF := GF) GD0 γ) GD i (k + 1) ls' := by
  show iprop(⌜GD = GD0⌝ ∗ True) ⊢ iprop(|==> ∃ _ls' : Unit, True)
  iintro _
  imodintro
  iexists ()
  itrivial

theorem locGa2' (GD0 : Gdexec) (γ : GName) (GD : Gdexec) (i : Agent) (k : Nat)
    (ls : @AxirisG.logTsT GF (epiGa2 GD0 γ)) :
    AxirisG.localInterp (self := epiGa2 (GF := GF) GD0 γ) GD i k ls ⊢
      |==> ∃ ls', AxirisG.localInterp (self := epiGa2 (GF := GF) GD0 γ) GD i (k + 1) ls' := by
  show iprop(True) ⊢ iprop(|==> ∃ _ls' : Unit, True)
  iintro _
  imodintro
  iexists ()
  itrivial

theorem obEqGa2 (GD0 : Gdexec) (γ : GName) :
    ∀ (GD : Gdexec) (σ : @AxirisG.obSt GF (epiGa2 GD0 γ)) (s : GSet Geid),
      AxirisG.obStInterp (self := epiGa2 (GF := GF) GD0 γ) GD σ s ⊣⊢ protInv γ GD s :=
  fun _ _ _ => .rfl

theorem annEqGa2 (GD0 : Gdexec) (γ : GName) :
    ∀ m : Mea GF, AxirisG.annotInterp (self := epiGa2 (GF := GF) GD0 γ) m ⊣⊢
      AxAnnot.annotInterp m :=
  fun _ => .rfl

/-- A fetch (a non-write) deposits `True`: `protInvReadStep`. -/
theorem fetchFlowGa2 (GD0 : Gdexec) (γ : GName) (i : Agent) (k : Nat)
    (Hnw : gisW GD0.gdG (i, k) = false) :
    ∀ (GD : Gdexec) (ls : @AxirisG.logTsT GF (epiGa2 GD0 γ)), rvwmoCatConsistent GD →
      AxirisG.gconstInterp (self := epiGa2 (GF := GF) GD0 γ) GD ∗
          AxirisG.localInterp (self := epiGa2 (GF := GF) GD0 γ) GD i k ls ⊢
        @fetchFlow hlc GF _ (epiGa2 GD0 γ) pol GD i k := by
  intro GD ls _
  show iprop(⌜GD = GD0⌝ ∗ True) ⊢ _
  iintro ⟨%Heq, -⟩
  subst Heq
  have hloc : ⊢ AxirisG.localInterp (self := epiGa2 (GF := GF) GD γ) GD i (k + 1) () := by
    show ⊢ iprop(True)
    itrivial
  letI : AxirisG GF := epiGa2 GD γ
  unfold fetchFlow
  iintro %na ⟨Hpg, Hannot⟩
  ihave %Hnin := naAtProgressNotElemOf GD i k na $$ Hpg
  imod (annotAlloc na (i, k) iprop(True) Hnin) $$ Hannot with ⟨Hannot, -⟩
  imodintro
  inext
  imodintro
  iexists iprop(True), (∅ : Mea GF), (∅ : Mea GF), ()
  isplitr
  · iapply AxProtGate.naSplittingWfEmpty
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
    · iapply protInvReadStep γ GD sOb (i, k) Hnin' Hnw
      iexact Hob
    · itrivial
  isplitl [Hannot]
  · rw [AxProtGate.annotInsertEq]
    iexact Hannot
  · iapply hloc

/-- The per-hart `wpd` at `axGA2`, `Φ := ⌜epiPost GD0 0 ·⌝`. -/
theorem wpdEpiGa2 (GD0 : Gdexec) (γ : GName) (cpu : CPU) (ib : Ibch) (a : Int)
    (Hgd_sd : AxCjrWpd.fetchImgOk GD0 0 0 pcSd sdVs)
    (Hrow_sd : storeRowOk GD0 0 0)
    (Hw_sd : sdWriteOk GD0 0 0 a)
    (Hgd_ld : AxCjrWpd.fetchImgOk GD0 0 1 pcLd AxEpiLedger.ldVs)
    (Hrow_ld : loadRowOk GD0 0 1)
    (Hok_ld : ldspOwnOk GD0 0 1 (0, 0) a (writenHist (0, 0) sdData epiHs0))
    (Hlen : (AxOpsem.grow GD0 0).length = 2) :
    ⊢ ([∗list] j ↦ H ∈ epiHs0, histAuth (GF := GF) γ (a + (j : Int)) 1 H) -∗
      @wpd hlc GF _ (epiGa2 GD0 γ) pol .MaybeStuck 0
        ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ib, 0⟩
        (fun s => iprop(⌜epiPost GD0 0 s⌝)) := by
  have Hpre : ⊢ ∀ (GD : Gdexec) (s1 : Athread), ⌜s1.atK ≤ 0 + 1⌝ -∗
      ⌜s1.atK = (AxOpsem.grow GD 0).length⌝ -∗
      @postLifting GF (epiGa2 GD0 γ) (fun s => iprop(⌜epiPost GD0 0 s⌝)) 0 s1 := by
    iintro %GD %s1 %Hle %_
    iapply (@postLiftingTrue GF (epiGa2 GD0 γ) pol (fun s => iprop(⌜epiPost GD0 0 s⌝)) 0 s1)
    iintro _
    ipureintro
    intro h
    omega
  have hg : ∀ GD', AxirisG.gconstInterp (self := epiGa2 (GF := GF) GD0 γ) GD' ⊢ ⌜GD' = GD0⌝ := by
    intro GD'
    show iprop(⌜GD' = GD0⌝) ⊢ iprop(⌜GD' = GD0⌝)
    iintro %h
    ipureintro
    exact h
  have Hpost : ⊢ ldRb (axG := epiGa2 GD0 γ) 0 (0 + 1) sdData -∗
      ∀ (GD : Gdexec) (s1 : Athread), ⌜s1.atK = (AxOpsem.grow GD 0).length⌝ -∗
        @postLifting GF (epiGa2 GD0 γ) (fun s => iprop(⌜epiPost GD0 0 s⌝)) 0 s1 := by
    unfold ldRb
    iintro ⟨%GD', %v, Hfrag, %Hgv, #Hg⟩ %GD %s1 %_
    ihave %HGD := hg GD' $$ Hg
    rw [HGD] at Hgv
    unfold postLifting
    iintro %na Hna
    have hag : AxirisG.annotInterp (self := epiGa2 (GF := GF) GD0 γ) na ∗
        AxAnnot.annotOwn (0, 0 + 1) iprop(⌜v = sdData⌝) ⊢
        iprop(⌜(0, 0 + 1) ∈ (FiniteMap.dom_set na : GSet Geid)⌝ ∗
          AxWp.fromOption (fun P' => iprop(▷ □ (P' -∗ ⌜v = sdData⌝))) iprop(emp)
            (get? na (0, 0 + 1))) := by
      iintro ⟨Hna, Hp⟩
      iapply annotAgree na (0, 0 + 1) iprop(⌜v = sdData⌝) $$ Hna Hp
    cases hget : get? na (0, 0 + 1) with
    | none =>
      rw [hget] at hag
      simp only [AxWp.fromOption] at hag
      icases persistent_entails_left hag $$ [$Hna $Hfrag] with ⟨-, %Hdom, -⟩
      have h := elemOfDom.1 Hdom
      rw [hget] at h
      cases h
    | some P0 =>
      rw [hget] at hag
      simp only [AxWp.fromOption] at hag
      icases persistent_entails_left hag $$ [$Hna $Hfrag] with ⟨⟨Hna, -⟩, %Hdom, #Hw⟩
      imodintro
      isplitl [Hna]
      · iexact Hna
      iintro Hbig
      have Hlk : ([∗map] e ↦ R ∈ na, if e.1 = 0 then R else iprop(True)) ⊢ P0 :=
        (BigSepM.bigSepM_lookup (Φ := fun e R => if e.1 = 0 then R else iprop(True)) hget).trans
          (by dsimp only; rw [if_pos rfl])
      ihave HP0 := Hlk $$ Hbig
      inext
      ihave Hpp := Hw $$ HP0
      icases Hpp with %Hv
      imodintro
      ipureintro
      intro _
      rw [← Hv]
      exact Hgv
  iintro Hauths
  iapply (wpdEpiSdLdOwnedRb (axG := epiGa2 GD0 γ) γ (obEqGa2 GD0 γ) (annEqGa2 GD0 γ) 0 _ cpu ib
    0 a epiHs0
    (pinGa2 GD0 γ (fun GD => AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs) Hgd_sd)
    (pinGa2 GD0 γ (fun GD => storeRowOk GD 0 0) Hrow_sd)
    (pinGa2 GD0 γ (fun GD => sdWriteOk GD 0 0 a) Hw_sd)
    (fun GD ls _ => locGa2 GD0 γ GD 0 0 ls)
    (pinGa2 GD0 γ (fun GD => AxCjrWpd.fetchImgOk GD 0 (0 + 1) pcLd AxEpiLedger.ldVs) Hgd_ld)
    (pinGa2 GD0 γ (fun GD => loadRowOk GD 0 (0 + 1)) Hrow_ld)
    (pinGa2 GD0 γ (fun GD => ldspOwnOk GD 0 (0 + 1) (0, 0) a (writenHist (0, 0) sdData epiHs0))
      Hok_ld)
    (fun GD ls _ => locGa2' GD0 γ GD 0 (0 + 1) ls) rfl
    (pinGa2 GD0 γ (fun GD => (AxOpsem.grow GD 0).length = 0 + 2) Hlen)) $$ Hauths [] []
  · iapply Hpre
  · iapply Hpost

end ga2

/-- `HobAlloc`: a fresh `γ` with the 8 empty slot histories. -/
theorem epiHobAlloc {GF : BundledGFunctors} [AxlogG GF Hent] (a : Int) (GD : Gdexec) :
    ⊢@{IProp GF} |==> ∃ (nm : GName) (σ0 : Unit),
      epiObInterp nm GD σ0 ∅ ∗ [∗list] i ∈ [0], epiInit a nm i := by
  have Hinj : Function.Injective (fun j : Nat => a + (j : Int)) := by
    intro x y h
    simp only at h
    omega
  have Hnd : (([0, 1, 2, 3, 4, 5, 6, 7] : List Nat).map (fun j : Nat => a + (j : Int))).Nodup :=
    List.Pairwise.map (R := fun x y : Nat => x ≠ y) _ (fun _ _ h hxy => h (Hinj hxy)) (by decide)
  have Hconv : ∀ γ : GName, iprop([∗set] x ∈ (LawfulSet.ofList
        (([0, 1, 2, 3, 4, 5, 6, 7] : List Nat).map (fun j : Nat => a + (j : Int))) : GSet Int),
        histAuth (GF := GF) γ x 1 ([] : List Hent)) ⊢
      iprop([∗list] j ↦ H ∈ epiHs0, histAuth (GF := GF) γ (a + (j : Int)) 1 H) := by
    intro γ
    refine (BigSepS.bigSepS_of_list Hnd).1.trans ?_
    rw [BigSepL.bigSepL_map]
    exact .rfl
  ihave Halloc := histAlloc (GF := GF) (LawfulSet.ofList
    (([0, 1, 2, 3, 4, 5, 6, 7] : List Nat).map (fun j : Nat => a + (j : Int))) : GSet Int)
    ([] : List Hent)
  imod Halloc with ⟨%γ, H⟩
  imodintro
  iexists γ, ()
  isplitr
  · unfold epiObInterp protInv
    iapply BigSepS.bigSepS_empty.2
    iempintro
  · iapply BigSepL.bigSepL_singleton.2
    iapply (AxEpiAdeq.epiInit0 a γ).2
    iapply Hconv γ
    iexact H

/-- PIPELINE MILESTONE, NOT A SEPARATION RESULT (see the header).  The run of hart 0 to its row
end, through the logic and adequacy on the real Sail model, certifies that the reload reads the
spilled bytes. -/
theorem epiReloadSound (GD : Gdexec) (cpu : CPU) (a : Int)
    (Hcons : rvwmoCatConsistent GD)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 = 0)
    -- the row: c.sdsp = spill (0,0); c.ldsp = reload (0,1)
    (Hgd_sd : AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs)
    (Hrow_sd : storeRowOk GD 0 0)
    (Hw_sd : sdWriteOk GD 0 0 a)
    (Hgd_ld : AxCjrWpd.fetchImgOk GD 0 1 pcLd AxEpiLedger.ldVs)
    (Hrow_ld : loadRowOk GD 0 1)
    (Hok_ld : @ldspOwnOk epiPol GD 0 1 (0, 0) a (writenHist (0, 0) sdData epiHs0))
    (Hlen : (AxOpsem.grow GD 0).length = 2)
    -- the policy's one `lobp` edge is gmo-ordered
    (Hlob_gmo : gmoLt GD.gdG (0, 0) (0, 1))
    -- the run
    (sN : Athread) (n : Nat)
    (Hrun : ∀ (_ : AxannotGS epiGF) (nm : GName),
      nsteps (tierAAstep GD nm 0) n
        ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ sN)
    (Hend : sN.atK = (AxOpsem.grow GD 0).length) :
    graphValue GD (0, 1) = some sdData := by
  have Hharts' : ∀ e, e ∈ GD.gdG.gxGmo → e.1 ∈ [0] := by
    intro e He
    rw [Hharts e He]
    exact List.mem_singleton.2 rfl
  have Hs_pol : ∀ e e', e' ∈ Axpol.sPol (self := epiPol) GD e → gmoLt GD.gdG e' e :=
    fun e e' he' => gmoPrefixGmoLt _ Hcons.1 e e' (elemOfListToSet.1 he')
  have Hlobp : ∀ e e', e' ∈ Axpol.lobp (self := epiPol) GD e → gmoLt GD.gdG e' e := by
    intro e e' he'
    change e' ∈ epiLobp GD e at he'
    unfold epiLobp at he'
    split at he'
    · rename_i heq
      subst heq
      have h1 := elemOfSingleton.1 (elemOfIntersection.1 he').1
      subst h1
      exact Hlob_gmo
    · exact absurd he' notElemOfEmpty
  have Hwp : ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ ([∗list] i ∈ [0], epiInit a nm i) -∗
        [∗list] i ∈ [0],
          @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm
            ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ .MaybeStuck i
            (fun s => iprop(⌜epiPost GD i s⌝)) := by
    intro _ _ nm
    iintro Hi
    ihave Hi := BigSepL.bigSepL_singleton.1 $$ Hi
    ihave Hi := (AxEpiAdeq.epiInit0 a nm).1 $$ Hi
    iapply BigSepL.bigSepL_singleton.2
    unfold tierAWpd
    iapply (wpdEpiGa2 (pol := epiPol) GD nm cpu ibNone a Hgd_sd Hrow_sd Hw_sd Hgd_ld Hrow_ld
      Hok_ld Hlen) $$ Hi
  have Hfin := @tierAAdequacyAnnGmo epiGF _ _ epiPol GD GName Unit epiObInterp (epiInit a)
    epiAxpolWf Hcons [0] (by decide) Hharts'
    (fun _ => ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩) (fun _ => sN)
    (fun _ => n)
    (fun Hann nm i Hi => by rw [List.mem_singleton.1 Hi]; exact Hrun Hann nm)
    (fun _ _ => rfl)
    (fun i Hi => by rw [List.mem_singleton.1 Hi]; exact Hend)
    (epiPost GD) Hwp (epiHobAlloc a GD) Hs_pol Hlobp 0 (List.mem_singleton.2 rfl)
  exact Hfin (by rw [Hend, Hlen])

/-! # 4. NON-VACUITY of the PURE premises (not `Hrun`) at `AxEpiSdLdSat.gsdld`, with
`a := ldAddr` -/

theorem gsdldHs1 :
    writenHist (0, 0) sdData epiHs0 = sdData.map (fun v => [((0, 0), v)]) := rfl

theorem gsdldHs1Lookup (j : Nat) (H : List Hent) :
    (writenHist (0, 0) sdData epiHs0)[j]? = some H →
    ∃ v, H = [((0, 0), v)] ∧ sdData[j]? = some v := by
  rw [gsdldHs1, List.getElem?_map]
  cases hv : sdData[j]? with
  | none => intro h; cases h
  | some v => intro h; cases h; exact ⟨v, rfl, rfl⟩

theorem gsdldSdWriteOk : sdWriteOk gsdld 0 0 ldAddr := by
  refine ⟨by decide +kernel, ?_, rfl⟩
  rintro a' v' ⟨l, base, vs, j, Hl, Hw, Hv, Ha⟩
  have Hl0 : gxLbl gsdld.gdG (0, 0) = some (Lbl.LStore false sdAddr sdData .WCplain) := rfl
  rw [Hl0, Option.some.injEq] at Hl
  subst Hl
  simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hw
  obtain ⟨rfl, rfl⟩ := Hw
  exact ⟨j, Hv, Ha.symm⟩

theorem gsdldLdspOwnOk :
    @ldspOwnOk epiPol gsdld 0 1 (0, 0) ldAddr (writenHist (0, 0) sdData epiHs0) := by
  have hbef : ((0, 0) : Geid) ∈ eidsBefore gsdld 0 1 :=
    (elemOfEidsBefore _ _ _ _).2 ⟨rfl, by decide, by decide +kernel⟩
  refine ⟨?_, hbef, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ((0, 0) : Geid) ∈ epiLobp gsdld (0, 1)
    unfold epiLobp
    split
    · exact elemOfIntersection.2 ⟨elemOfSingleton.2 rfl, hbef⟩
    · rename_i hne
      exact absurd rfl hne
  · decide +kernel
  · decide +kernel
  · intro x hx
    exact hx
  · exact ⟨false, [1, 1, 1, 1, 1, 1, 1, 1], sdData, rfl, rfl, rfl⟩
  · intro j H hH p hp
    obtain ⟨v, rfl, hv⟩ := gsdldHs1Lookup j H hH
    rw [List.mem_singleton] at hp
    subst hp
    exact AxEpilogue.gwritesOfStore _ (0, 0) false sdAddr sdData .WCplain j v rfl hv
  · intro j H hH n w1 w2 _ hw2
    obtain ⟨v, rfl, _⟩ := gsdldHs1Lookup j H hH
    cases n <;> simp at hw2
  · intro j H hH w v' _ hpo
    obtain ⟨v, rfl, _⟩ := gsdldHs1Lookup j H hH
    obtain ⟨w1, w2⟩ := w
    obtain ⟨h1, h2, _, _⟩ := hpo
    simp only at h1 h2
    have hw2 : w2 = 0 := by omega
    subst h1 hw2
    exact List.mem_singleton.2 rfl
  · exact (gpoBSpec _ _ _).1 (by decide +kernel)

theorem epiReloadPremisesGsdld :
    rvwmoCatConsistent gsdld ∧
    (∀ e, e ∈ gsdld.gdG.gxGmo → e.1 = 0) ∧
    AxCjrWpd.fetchImgOk gsdld 0 0 pcSd sdVs ∧
    storeRowOk gsdld 0 0 ∧
    sdWriteOk gsdld 0 0 ldAddr ∧
    AxCjrWpd.fetchImgOk gsdld 0 1 pcLd AxEpiLedger.ldVs ∧
    loadRowOk gsdld 0 1 ∧
    @ldspOwnOk epiPol gsdld 0 1 (0, 0) ldAddr (writenHist (0, 0) sdData epiHs0) ∧
    (AxOpsem.grow gsdld 0).length = 2 ∧
    gmoLt gsdld.gdG (0, 0) (0, 1) := by
  refine ⟨gsdldCat, ?_, gsdldFetchSd, gsdldStoreRow, gsdldSdWriteOk, gsdldFetchLd, gsdldLoadRow,
    gsdldLdspOwnOk, rfl, (gmoLtBSpec _ _ _).1 (by decide +kernel)⟩
  intro e He
  have hg : gsdld.gdG.gxGmo = [(0, 0), (0, 1)] := rfl
  rw [hg] at He
  simp only [List.mem_cons, List.not_mem_nil, or_false] at He
  rcases He with rfl | rfl <;> rfl

end Weak

