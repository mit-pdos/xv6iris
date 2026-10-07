/-
Weak: **THE GLUE — `cycleKill` modulo the per-site classification** (route B, stage B2e-3c).

Rocq: `iris/WeakRvwmoGlue.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Design `claude-notes/design/weak-memory-route-b.md` §4d.2(3).  `WeakRvwmoLinInd.cycleKill` is the
one obligation T2-LIN's induction leaves open; `WeakRvwmoKillArms.cycleKillArms` kills a cycle
already presented as a list of CERTIFIED segments.  This file is everything between the two:

  §1  THE SEGMENT DECOMPOSITION.  `cycleSegments`: a `racyD` cycle IS a nonempty chain of
      segments — same-hart runs joined by cross-hart `gcross` edges.  The same-hart arms (`gpow`,
      `gppo`, `gdDeps`) are absorbed into the segments; the decomposition is total because a
      cycle made of those arms alone is impossible (`rsameAcyclic`: each is strictly
      po-increasing inside one hart).
  §2  THE PIN STATUS.  A segment's run gives `gmoLt entry exit` only when PINNED (`gacqPo`,
      `gfenceCovers`, `gdDeps`); `segPinGmo` is the discharge.
  §3  THE CUT.  `cutOk` = `hullOk` ∧ `wcutClosed` ∧ `properCut`; the middle clause makes `hren`
      the identity, so a certified prefix of the hull is one of `G` (`cutOkCtrace`).
  §4  THE REALIZATION ROUTE (route (c)): `WeakRvwmoCert4.hullRealizableRowsG`, the residual
      renaming a single function `rho` confined to the row equation of `RunData`.
  §5  THE RUN AND THE EXPORTS.  `runErased`: T1 ∘ the language lift with the ERASED run exposed
      and the LOG IDENTIFICATION kept; the exports of `WeakEvAdequacy` at its final state.
  §6  THE CLAIM AND THE GLUE.  `l2Claim` (the L2′ per-site classification); `cycleKillOfL2`
      discharges `cycleKill` from it; `t2linOfL2` composes with `t2linOfCycleKill`.
  §7  NON-VACUITY: the LB witness decomposes (`lbgdSegments`); the claim holds at the
      `racyD`-acyclic `mpgd` (`l2ClaimMpgd`).

§8 (the `Print Assumptions` audit) and §9 (the ledger of the four open premises (G-1) `l2Claim`,
(G-2) `cutSupply`, (G-3) `certSupply`, (G-4) `bootTie`'s third conjunct) are Rocq
commands/comments, not declarations.  A LEAF: nothing imports this file.

## Deviations from Rocq

1. NAMES / VOCABULARY: camelCase (map below); `Rsame` ↦ `rsame`, `Crun` ↦ `crun`, `RacyD` ↦
   `racyD`, `gpo` ↦ `WeakRvwmoGraph.gpo`, `chain` ↦ `WeakRvwmoKillArms.chain`, `cert` ↦ `Cert`;
   `Seg e.1 e b` ↦ `⟨e.1, e, b⟩`; `seq 0 N` ↦ `List.range' 0 N`; `l !! i` ↦ `l[i]?`;
   `default d o` ↦ `o.getD d`; `agent` ↦ `Nat`; `dev_state` ↦ `Efab` (WeakEvPf deviation 9);
   `Z` ↦ `Int`; `namespace` ↦ `Namespace`; `rtc erased_step` ↦ `-·->ₜₚ*`.  The record
   `run_data` (constructor `RunData`) is the structure `RunData` (constructor `RunData.mk`,
   fields `rdCons`/`rdImg`/`rdPst0`/`rdDv0`/`rdProg`).
2. THE BOOT DEVICE STATE (WeakSrvwmoCapstone deviation 2): Rocq's `d0 = wgdev σ0` (in
   `runErased` and `bootTie`) is `d0 = efInit σ0.wgdev` (the fabric with every residual device
   program at `.pure ()`).
3. THE WP PACKAGES (WeakEvAdequacy deviations 2, 3): `Σ`/`riscvGpreS`/`weakGpreS` ↦ explicit
   `hlc GF` with `[MachGpreS hlc GF] [WeakGpreS GF]`; `D : CPU → List Register` and the theorems
   that call the adequacy exports (`protRegOfRun`, `noBadRun`, `cycleKillOfL2`, `t2linOfL2`)
   take `hD : ∀ c, (D c).Nodup`; the device fragments are `[∗list] d ∈ DevId.all, devFragAt …`.
4. O2 — THE FETCH-VIEW PREMISE (WeakEvCapstone deviation 2 / WeakSrvwmoCapstone deviation 3):
   the language lift `wpPfRtcEpfRtc` needs `efetchItvOk` at every `epfRun`-reachable state, so
   `runErased`, `cycleKillOfL2` and `t2linOfL2` CARRY the Lean-only premise
   `∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2` (dischargeable by
   `WeakEvCapstone.efetchItvOkRunOfUnwritten`; nothing here proves the text unwritten).
5. O2 / STAGE C — THE PINNED LTS (WeakRvwmoCert4 deviation 3 / WeakRvwmoSupply deviation 2).
   The fetch is an administrative label of the graph tier whose only content (the bytes are
   the boot image at timestamp 0) is the pin `WeakAxRealize.fetchPin`.  `RunData.rdProg` is
   therefore stated at the pinned program LTS `pstepPin c.cdImg pstepEv` (the form
   `hullRealizableRowsG` and `WeakRvwmoCert4.cstOk` deliver, unconditionally), and `runErased`
   replays it through `WeakAxRealize.execWfPfRunPin` (projected back to `pstepEv`).  The Stage-B
   Lean-only premise `WeakRvwmoGlue.hullRunFetchInert` is DELETED: `hullRun`, `cycleKillOfL2`
   and `t2linOfL2` carry only the fetch-view premise of deviation 4; conclusions are Rocq's.
6. PROOFS: `tc`/`rtc` inductions split at the LAST step (MachCSL.Rel deviation 1), so
   `crunRawChain` builds the chain by appending (Lean-only `WeakRvwmoGlue.rawChainSnoc`) and
   `racyDDecompose` / `crunAppend` case on the last step; the statements are Rocq's.

**Rocq → Lean name map.**  `Rsame` `rsame`, `RacyD_split` `racyDSplit`, `gppo_lex` `gppoLex`,
`Rsame_lex` `rsameLex`, `tc_Rsame_lex` `tcRsameLex`, `Rsame_acyclic` `rsameAcyclic`, `seg_run`
`segRun`, `raw_chain` `rawChain`, `Crun` `crun`, `Crun_raw_chain` `crunRawChain`,
`Crun_append` `crunAppend`, `racyD_decompose` `racyDDecompose`, `cycle_segments`
`cycleSegments`, `seg_pin` `segPin`, `seg_pin_gmo` `segPinGmo`, `seg_pin_cert` `segPinCert`,
`cut_ok` `cutOk`, `cut_ok_proper` `cutOkProper`, `cut_ok_lbl` `cutOkLbl`, `cut_ok_ctrace`
`cutOkCtrace`, `run_data` `RunData`, `hull_run` `hullRun`, `fresh_era` `freshEra`,
`run_erased` `runErased`, `wp_package` `wpPackage`, `wp_package_prot` `wpPackageProt`,
`prot_reg` `protReg`, `prot_reg_of_run` `protRegOfRun`, `bad_run` `badRun`, `no_bad_run`
`noBadRun`, `cs_hyps` `csHyps`, `cs_hyps_cert` `csHypsCert`, `l2_claim_at` `l2ClaimAt`,
`l2_claim` `l2Claim`, `raw_chain_chain` `rawChainChain`, `cut_supply` `cutSupply`,
`cert_supply` `certSupply`, `boot_tie` `bootTie`, `cycle_kill_of_l2` `cycleKillOfL2`,
`t2lin_of_l2` `t2linOfL2`, `Rsame_RacyD` `rsameRacyD`, `rtc_Rsame_RacyD` `rtcRsameRacyD`,
`raw_chain_tc` `rawChainTc`, `lbgd_segments` `lbgdSegments`, `l2_claim_mpgd` `l2ClaimMpgd`.
Lean-only (file-qualified): `WeakRvwmoGlue.rawChainSnoc`.

**File-qualified Rocq names:** none (no name of this file is in `notes/weak-port-dupnames.json`).

**Dropped:** none (Rocq 45 declarations; Lean 46 = 45 + the 1 Lean-only).
-/
import Weak.WeakRvwmoCert4
import Weak.WeakRvwmoKillArms
import Weak.WeakEvCapstone
import Weak.WeakAxRealize
import Weak.WeakAxiomatic3
import Weak.WeakEvAdequacy

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! # 1. THE SEGMENT DECOMPOSITION -/

/-- The SAME-HART arms of `racyD`. -/
def rsame (GD : Gdexec) (x y : Geid) : Prop :=
  gpow GD.gdG x y ∨ gppo GD.gdG x y ∨ (x, y) ∈ GD.gdDeps

theorem racyDSplit (GD : Gdexec) (x y : Geid) :
    racyD GD x y → rsame GD x y ∨ gcross GD.gdG x y := by
  rintro ((h | h | h | h | h) | h)
  · exact .inl (.inl h)
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))
  · exact .inl (.inr (.inl h))
  · exact .inl (.inr (.inr h))

/-- Every same-hart arm is strictly po-increasing inside ONE hart. -/
theorem gppoLex (G : Gexec) (x y : Geid) : gppo G x y → x.1 = y.1 ∧ x.2 < y.2 := by
  rintro (⟨⟨h1, h2, -⟩, -⟩ | ⟨-, -, -, -, ⟨h1, h2, -⟩, -, -⟩ | ⟨⟨h1, h2, -⟩, -⟩ |
    ⟨⟨h1, h2, -⟩, -⟩) <;> exact ⟨h1, h2⟩

theorem rsameLex (GD : Gdexec) (x y : Geid) :
    gdepsWf GD.gdG GD.gdDeps → rsame GD x y → x.1 = y.1 ∧ x.2 < y.2 := by
  rintro hwf (⟨⟨h1, h2, -⟩, -⟩ | h | h)
  · exact ⟨h1, h2⟩
  · exact gppoLex GD.gdG x y h
  · obtain ⟨h1, h2, -, -⟩ := hwf (x, y) h
    exact ⟨h1, h2⟩

theorem tcRsameLex (GD : Gdexec) (x y : Geid) :
    gdepsWf GD.gdG GD.gdDeps → tc (rsame GD) x y → x.1 = y.1 ∧ x.2 < y.2 := by
  intro hwf h
  induction h with
  | single h => exact rsameLex GD _ _ hwf h
  | tail _ h ih =>
    obtain ⟨h1, h2⟩ := rsameLex GD _ _ hwf h
    exact ⟨ih.1.trans h1, by omega⟩

/-- … so a cycle made of same-hart arms alone is impossible. -/
theorem rsameAcyclic (GD : Gdexec) (x : Geid) :
    gdepsWf GD.gdG GD.gdDeps → ¬ tc (rsame GD) x x := by
  intro hwf hc
  have := tcRsameLex GD x x hwf hc
  omega

/-- A SEGMENT's run: its entry reaches its exit by same-hart arms only. -/
def segRun (GD : Gdexec) (s : Seg) : Prop :=
  rtc (rsame GD) s.sgEntry s.sgExit

/-- THE RAW CHAIN: a cross edge into each entry, and a same-hart run from entry to exit. -/
def rawChain (GD : Gdexec) (x y : Geid) : List Seg → Prop
  | [] => x = y
  | s :: ss => gcross GD.gdG x s.sgEntry ∧ segRun GD s ∧ rawChain GD s.sgExit y ss

/-- One "cross then run" step. -/
def crun (GD : Gdexec) (u v : Geid) : Prop :=
  ∃ e, gcross GD.gdG u e ∧ rtc (rsame GD) e v

/-- Lean-only (deviation 6): appending one segment to a raw chain. -/
theorem WeakRvwmoGlue.rawChainSnoc (GD : Gdexec) (x u e b : Geid) (ss : List Seg) :
    rawChain GD x u ss → gcross GD.gdG u e → rtc (rsame GD) e b →
    rawChain GD x b (ss ++ [⟨e.1, e, b⟩]) := by
  induction ss generalizing x with
  | nil =>
    intro h hx hr
    have h' : x = u := h
    subst h'
    show gcross GD.gdG x e ∧ segRun GD ⟨e.1, e, b⟩ ∧ rawChain GD b b []
    exact ⟨hx, hr, rfl⟩
  | cons s ss ih =>
    intro h hx hr
    obtain ⟨h1, h2, h3⟩ := h
    show gcross GD.gdG x s.sgEntry ∧ segRun GD s ∧ rawChain GD s.sgExit b (ss ++ [⟨e.1, e, b⟩])
    exact ⟨h1, h2, ih _ h3 hx hr⟩

theorem crunRawChain (GD : Gdexec) (a b : Geid) :
    tc (crun GD) a b → ∃ ss, ss ≠ [] ∧ rawChain GD a b ss := by
  intro h
  induction h with
  | single h =>
    obtain ⟨e, hx, hr⟩ := h
    exact ⟨[] ++ [⟨e.1, e, _⟩], by simp,
      WeakRvwmoGlue.rawChainSnoc GD _ _ e _ [] (show rawChain GD a a [] from rfl) hx hr⟩
  | tail _ h ih =>
    obtain ⟨ss, -, hch⟩ := ih
    obtain ⟨e, hx, hr⟩ := h
    exact ⟨ss ++ [⟨e.1, e, _⟩], by simp, WeakRvwmoGlue.rawChainSnoc GD _ _ e _ ss hch hx hr⟩

/-- Appending a same-hart tail to a `crun` chain. -/
theorem crunAppend (GD : Gdexec) (a b c : Geid) :
    tc (crun GD) a b → rtc (rsame GD) b c → tc (crun GD) a c := by
  intro h hbc
  cases h with
  | single h =>
    obtain ⟨e, hx, hr⟩ := h
    exact tc_once ⟨e, hx, rtc_transitive hr hbc⟩
  | tail h1 h2 =>
    obtain ⟨e, hx, hr⟩ := h2
    exact tc_r h1 ⟨e, hx, rtc_transitive hr hbc⟩

/-- THE DECOMPOSITION LEMMA. -/
theorem racyDDecompose (GD : Gdexec) (a b : Geid) :
    tc (racyD GD) a b →
    tc (rsame GD) a b ∨ ∃ y, rtc (rsame GD) a y ∧ tc (crun GD) y b := by
  intro h
  induction h with
  | single h =>
    rcases racyDSplit GD _ _ h with hs | hx
    · exact .inl (tc_once hs)
    · exact .inr ⟨a, rtc_refl _, tc_once ⟨_, hx, rtc_refl _⟩⟩
  | tail _ h ih =>
    rcases racyDSplit GD _ _ h with hs | hx
    · rcases ih with ih | ⟨y, hry, hty⟩
      · exact .inl (tc_r ih hs)
      · exact .inr ⟨y, hry, crunAppend GD _ _ _ hty (rtc_once hs)⟩
    · rcases ih with ih | ⟨y, hry, hty⟩
      · exact .inr ⟨_, tc_rtc ih, tc_once ⟨_, hx, rtc_refl _⟩⟩
      · exact .inr ⟨y, hry, tc_r hty ⟨_, hx, rtc_refl _⟩⟩

/-- THE THEOREM.  An `racyD` cycle is a nonempty raw chain from some event back to itself. -/
theorem cycleSegments (GD : Gdexec) (x : Geid) :
    gdepsWf GD.gdG GD.gdDeps →
    tc (racyD GD) x x →
    ∃ z ss, ss ≠ [] ∧ rawChain GD z z ss := by
  intro hwf hcyc
  rcases racyDDecompose GD x x hcyc with hbad | ⟨y, hry, hty⟩
  · exact absurd hbad (rsameAcyclic GD x hwf)
  · exact ⟨y, crunRawChain GD y y (crunAppend GD _ _ _ hty hry)⟩

/-! # 2. THE PIN STATUS -/

def segPin (GD : Gdexec) (s : Seg) : Prop :=
  gacqPo GD.gdG s.sgEntry s.sgExit ∨
  gfenceCovers GD.gdG s.sgEntry s.sgExit ∨
  (s.sgEntry, s.sgExit) ∈ GD.gdDeps

theorem segPinGmo (GD : Gdexec) (s : Seg) :
    rvwmoMinusDepsConsistent GD → segPin GD s →
    gmoLt GD.gdG s.sgEntry s.sgExit := by
  rintro ⟨hcons, -, hdg⟩ (h | h | h)
  · exact hcons.2.1 _ _ (.inr (.inr (.inl h)))
  · exact hcons.2.1 _ _ (.inr (.inl h))
  · exact hdg _ h

/-- A pinned segment, with the cross edge its raw chain carries, IS a `Pinned` certificate. -/
theorem segPinCert (GD : Gdexec) (prev : Geid) (s : Seg) :
    rvwmoMinusDepsConsistent GD →
    gcross GD.gdG prev s.sgEntry → segPin GD s →
    Cert GD.gdG prev s :=
  fun hcons hx hp => .Pinned hx (segPinGmo GD s hcons hp)

/-! # 3. THE CUT: the write-closed causal past -/

def cutOk (G : Gexec) (cs : List Nat) : Prop :=
  hullOk G cs ∧ wcutClosed G cs ∧ properCut G cs

theorem cutOkProper (G : Gexec) (cs : List Nat) : cutOk G cs → properCut G cs :=
  fun h => h.2.2

theorem cutOkLbl (G : Gexec) (cs : List Nat) (e : Geid) :
    gwf G → cutOk G cs → gcut cs e = true →
    gxLbl (gxHull G cs) e = gxLbl G e :=
  fun hwf hc he => gxhLblEq G cs e hwf hc.1 hc.2.1 he

theorem cutOkCtrace (G : Gexec) (cs : List Nat) (c : Cand) (ev : Nat → Geid)
    (W : Geid → Prop) :
    gwf G → cutOk G cs →
    (∀ p s, c.cdTr[p]? = some s → gcut cs (ev p) = true) →
    CtracePrefix (gxHull G cs) c ev W →
    CtracePrefix G c ev W :=
  fun hwf hc hcut hgt => ctracePrefixOfHull G cs c ev W hwf hc.1 hc.2.1 hcut hgt

/-! # 4. THE REALIZATION ROUTE (route (c), see the Rocq note) -/

structure RunData (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec) (c : Cand)
    (pst : Nat → List Pexv6) (dv : Nat → Efab) : Prop where
  rdCons : srvwmoConsistent c
  rdImg : c.cdImg = G.gxImg
  rdPst0 : pst 0 = (List.range' 0 N).map boot
  rdDv0 : dv 0 = d0
  /-- Deviation 5: at the pinned program LTS. -/
  rdProg : execProgOk' (pstepPin c.cdImg pstepEv) pclsEv pst dv (candExec c)

/-- THE ROUTE, assembled. -/
theorem hullRun (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat)
    (GD : Gdexec) (cs : List Nat) (N : Nat) :
    rvwmoMinusDepsConsistent GD →
    gdexecQconf boot d0 im nh GD →
    cutOk GD.gdG cs →
    (∀ x, ¬ tc (racyD (gdHull GD cs)) x x) →
    GD.gdG.gxProg.length ≤ N →
    ∃ (c : Cand) (pst : Nat → List Pexv6) (rho : Nat → Nat),
      RunData boot d0 N GD.gdG c pst (fun _ => d0) ∧
      (∀ i, (c.cdTr.filter (fun s => decide (s.esAg = i))).map (fun s => s.esLb) =
        (List.take ((cs[i]?).getD 0) ((GD.gdG.gxProg[i]?).getD [])).map (lblRen rho)) := by
  intro hcons hq hcut hacy hN
  obtain ⟨c, pst, rho, hc, himg, hpst0, hprog, hrow⟩ :=
    hullRealizableRowsG boot d0 im nh GD cs N hcons hq (cutOkProper _ _ hcut) hacy hN
  exact ⟨c, pst, rho, ⟨hc, himg, hpst0, rfl, hprog⟩, hrow⟩

/-! # 5. THE RUN AND THE EXPORTS -/

section run

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

def freshEra (gen : Nat) (σ0 : WGState) : Prop :=
  gen = 0 ∧ σ0.wgpow = true ∧ σ0.wggen = 0 ∧ σ0.wglog = [] ∧ (∀ cc : CPU, σ0.wgws cc = wsInit)

/-- Rocq `run_erased` (deviations 2, 4, 5). -/
theorem runErased (gen : Nat) (σ0 : WGState) (boot : Nat → Pexv6) (d0 : Efab) (N : Nat)
    (G : Gexec) (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab) :
    freshEra gen σ0 →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    G.gxImg = imgZ σ0.wgimg →
    RunData boot d0 N G c pst dv →
    ∃ (t2 : List EExpr) (σ2 : WGState),
      (epowerFork gen, σ0) -·->ₜₚ* (t2, σ2) ∧
      σ2.wglog = cdLog c c.cdTr.length := by
  rintro ⟨hgen, hpow, hgen0, hlog, hws⟩ hcov hb1 hb2 hb3 ⟨hcons, himg, hpst0, hdv0, hprog⟩
  have hlive : ethreadLive σ0 gen := ⟨hpow, by rw [hgen0, hgen]⟩
  obtain ⟨hwf, -, heximg⟩ := srvwmoRealizable c hcons
  obtain ⟨cf, hrun, -, -, hm⟩ :=
    execWfPfRunPin pstepEv pclsEv c.cdImg pst dv (candExec c) pclsEvEqr heximg hwf hprog
  rw [heximg, himg, hb3, hpst0, hb1, hdv0, hb2, ← ecfgOfInit gen σ0 hlog hws] at hrun
  obtain ⟨P', σ', hr, heq⟩ := wpPfRtcEpfRtc (epInit gen) σ0 cf hlive hcov hrun
  refine ⟨epoolList P', σ', ?_, ?_⟩
  · have he := epfRtcErased (epInit gen, σ0) (P', σ') hr
    rw [show (epInit gen, σ0).1 = epInit gen from rfl, epoolListInit] at he
    exact he
  · obtain ⟨-, hlg, -⟩ := hm
    rw [← ecfgOfLog P' σ', heq, ← hlg, candExTr]
    exact candElog c c.cdTr.length (Nat.le_refl _)

/-! ## 5.1 THE WP PACKAGE, in the two flavours the exports need (deviation 3) -/

def wpPackage (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) : Prop :=
  ∀ [MachGS hlc GF] [WeakGS GF],
    (([∗list] cc ∈ cpus, [∗list] r ∈ D cc, regPointsTo cc r (DFrac.own 1) (σ0.wgregs cc r)) ∗
      bigSepM (M := GMapF PAddr) (fun a b => wlatPointsto (paZ a) (DFrac.own 1) 0 b) σ0.wgimg ∗
      ([∗list] cc ∈ cpus, hartView cc) ∗
      wlogLb [] ∗
      ([∗list] d ∈ DevId.all, devFragAt (MachGS.era (hlc := hlc) (GF := GF)) d (σ0.wgdev.st d)))
    ⊢@{IProp GF} |={⊤}=> ([∗list] e ∈ epowerFork gen, ewpTriv (hlc := hlc) (GF := GF) ⊤ e)

def wpPackageProt (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (Nm : Namespace) (a base : Int) :
    Prop :=
  ∀ [MachGS hlc GF] [WeakGS GF],
    (([∗list] cc ∈ cpus, [∗list] r ∈ D cc, regPointsTo cc r (DFrac.own 1) (σ0.wgregs cc r)) ∗
      bigSepM (M := GMapF PAddr) (fun a0 b => wlatPointsto (paZ a0) (DFrac.own 1) 0 b)
        σ0.wgimg ∗
      ([∗list] cc ∈ cpus, hartView cc) ∗
      wlogLb [] ∗
      ([∗list] d ∈ DevId.all, devFragAt (MachGS.era (hlc := hlc) (GF := GF)) d (σ0.wgdev.st d)))
    ⊢@{IProp GF} |={⊤}=>
      (wprotRegd (hlc := hlc) Nm a base ∗
        [∗list] e ∈ epowerFork gen, ewpTriv (hlc := hlc) (GF := GF) ⊤ e)

/-! ## 5.2 THE EXPORTS AT THE CERTIFIED RUN'S LOG -/

def protReg (P : Int → Int → Prop) (log : List Wmsg) : Prop :=
  ∀ a base, P a base →
    ∃ (n0 r0 : Nat) (h : Option Nat),
      wprotAt log a base n0 r0 ∧ wlpAt log base base n0 ∧ wlpAlt log base n0 h

theorem protRegOfRun (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (t2 : List EExpr) (σ2 : WGState) :
    freshEra gen σ0 →
    (∀ a base, P a base → wpPackageProt hlc GF gen σ0 D (Nm a base) a base) →
    (epowerFork gen, σ0) -·->ₜₚ* (t2, σ2) →
    protReg P σ2.wglog := by
  rintro ⟨hgen, hpow, hgen0, hlog, hws⟩ hwp hrtc a base hP
  obtain ⟨-, n0, r0, h, hpr, hat, halt⟩ :=
    weakEvAdequacyProt (hlc := hlc) (GF := GF) gen σ0 D hD (Nm a base) a base hgen hpow hgen0
      hlog hws (hwp a base hP) t2 σ2 hrtc
  exact ⟨n0, r0, h, hpr, hat, halt⟩

/-- φ, at the same run: the BAD arm's refutation. -/
def badRun (gen : Nat) (σ0 : WGState) : Prop :=
  ∃ ρ, rtc epfRun (epInit gen, σ0) ρ ∧ violationHart clsOf pubOf nDisk (ecfgOf ρ.1 ρ.2)

theorem noBadRun (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup) :
    freshEra gen σ0 → wpPackage hlc GF gen σ0 D → ¬ badRun gen σ0 := by
  rintro ⟨hgen, hpow, hgen0, hlog, hws⟩ hwp ⟨ρ, hr, hv⟩
  exact weakEvPfViolationFree (hlc := hlc) (GF := GF) gen σ0 D hD hgen hpow hgen0 hlog hws hwp
    ρ hr hv

end run

/-! # 6. THE L2′ CLAIM AND THE GLUE -/

/-! ## 6.1 The CS-chained hypothesis bundle -/

def csHyps (GD : Gdexec) (P : Int → Int → Prop) (log : List Wmsg) (prev : Geid) (s : Seg) :
    Prop :=
  ∃ (b a : Int) (ACQ REL : Geid),
    -- the byte is a REGISTERED protected byte of the lock word at `b`
    P a b ∧
    lockWordByte log b ∧
    -- the previous exit: an owned plain write of the protected byte, inside the log, not
    -- touching the lock word
    (∃ v, gwritesByte GD.gdG prev a v) ∧ gcls GD.gdG prev .WCplain ∧
    gwix GD.gdG prev ≤ log.length ∧
    (∀ v, ¬ gwritesByte GD.gdG prev b v) ∧
    -- the reader's row: its acquire, its section, its release fence
    lockAcq GD.gdG b ACQ ∧ acqRow GD.gdG b ACQ ∧
    glblIs GD.gdG ACQ lbAq ∧
    gwix GD.gdG ACQ ≤ log.length ∧
    lockCs GD.gdG b ACQ REL ∧
    WeakRvwmoGraph.gpo GD.gdG ACQ s.sgEntry ∧
    gfenceCovers GD.gdG s.sgEntry REL ∧
    WeakRvwmoGraph.gpo GD.gdG ACQ s.sgExit ∧ gmem GD.gdG s.sgExit ∧
    ACQ.1 ≠ prev.1 ∧
    -- the registration/protection side conditions, at whatever points the export names
    (∀ n0 r0, wprotAt log a b n0 r0 →
       r0 < gwix GD.gdG prev ∧ n0 < gwix GD.gdG ACQ)

theorem csHypsCert (GD : Gdexec) (P : Int → Int → Prop) (log : List Wmsg) (prev : Geid)
    (s : Seg) :
    rvwmoMinusDepsConsistent GD → logOf GD.gdG log → protReg P log →
    csHyps GD P log prev s → gcross GD.gdG prev s.sgEntry →
    Cert GD.gdG prev s := by
  rintro ⟨hcons, -, -⟩ hlog hpr
    ⟨b, a, ACQ, REL, hP, hlwb, hwa, hcl, hlew, hnob, hacq, hrow, haq, hleA, hcs, hpoe, hfen,
      hpox, hmx, hhart, hside⟩ hx
  obtain ⟨n0, r0, h, hprot, -, halt⟩ := hpr a b hP
  obtain ⟨hr0, hn0A⟩ := hside n0 r0 hprot
  exact .CSchained (csChained GD.gdG log b a n0 r0 h prev s.sgEntry s.sgExit ACQ REL hcons hlog
    hlwb halt hrow hprot hwa hcl hr0 hlew hnob hacq haq hn0A hleA hcs hpoe hfen hx hpox hmx hhart)

/-! ## 6.2 THE L2′ CLAIM -/

def l2ClaimAt (GD : Gdexec) (P : Int → Int → Prop) (Bad : Prop) : Prop :=
  ∀ (log : List Wmsg) (z : Geid) (ss : List Seg),
    rvwmoMinusDepsConsistent GD →
    logOf GD.gdG log →
    protReg P log →
    ss ≠ [] → rawChain GD z z ss →
    ∀ (prev : Geid) (s : Seg),
      s ∈ ss → gcross GD.gdG prev s.sgEntry → segRun GD s →
      segPin GD s ∨ csHyps GD P log prev s ∨ Bad

def l2Claim (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat)
    (P : Int → Int → Prop) (Bad : Prop) : Prop :=
  ∀ GD, gdexecQconf boot d0 im nh GD → l2ClaimAt GD P Bad

/-- A classified raw chain IS a `WeakRvwmoKillArms.chain`. -/
theorem rawChainChain (GD : Gdexec) (P : Int → Int → Prop) (log : List Wmsg) (Bad : Prop)
    (ss : List Seg) :
    rvwmoMinusDepsConsistent GD → logOf GD.gdG log → protReg P log →
    ¬ Bad →
    (∀ prev s, s ∈ ss → gcross GD.gdG prev s.sgEntry → segRun GD s →
       segPin GD s ∨ csHyps GD P log prev s ∨ Bad) →
    ∀ (x y : Geid) (ss' : List Seg),
      ss' ⊆ ss → rawChain GD x y ss' → WeakRvwmoKillArms.chain GD.gdG x y ss' := by
  intro hcons hlog hpr hnB hcl x y ss'
  induction ss' generalizing x with
  | nil => intro _ hch; exact hch
  | cons s ss' ih =>
    intro hsub hch
    obtain ⟨hx, hrun, hrest⟩ := hch
    have hs : s ∈ ss := hsub (by simp)
    have hsub' : ss' ⊆ ss := by
      intro t ht
      exact hsub (List.mem_cons_of_mem s ht)
    show Cert GD.gdG x s ∧ WeakRvwmoKillArms.chain GD.gdG s.sgExit y ss'
    refine ⟨?_, ih _ hsub' hrest⟩
    rcases hcl x s hs hx hrun with hp | hc | hb
    · exact segPinCert GD x s hcons hx hp
    · exact csHypsCert GD P log x s hcons hlog hpr hc hx
    · exact absurd hb hnB

/-! ## 6.3 THE TWO SUPPLIES B2e-3b OWES, named -/

def cutSupply (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) : Prop :=
  ∀ (GD : Gdexec) (z : Geid) (ss : List Seg),
    rvwmoMinusDepsConsistent GD → gdexecQconf boot d0 im nh GD →
    ss ≠ [] → rawChain GD z z ss →
    ∃ cs, cutOk GD.gdG cs

def certSupply (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (N : Nat) : Prop :=
  ∀ (GD : Gdexec) (cs : List Nat) (c0 : Cand) (pst0 : Nat → List Pexv6)
    (z : Geid) (ss : List Seg),
    rvwmoMinusDepsConsistent GD → gdexecQconf boot d0 im nh GD →
    cutOk GD.gdG cs →
    RunData boot d0 N GD.gdG c0 pst0 (fun _ => d0) →
    ss ≠ [] → rawChain GD z z ss →
    ∃ (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab),
      RunData boot d0 N GD.gdG c pst dv ∧
      logOf GD.gdG (cdLog c c.cdTr.length)

/-! ## 6.4 THE BOOT TIE (deviation 2) -/

def bootTie (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (N : Nat)
    (σ0 : WGState) : Prop :=
  (List.range' 0 N).map boot = epsInit σ0 ∧
  d0 = efInit σ0.wgdev ∧
  (∀ GD, gdexecQconf boot d0 im nh GD →
     GD.gdG.gxImg = imgZ σ0.wgimg ∧ GD.gdG.gxProg.length ≤ N)

/-! ## 6.5 THE GLUE -/

section glue

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- Rocq `cycle_kill_of_l2` (deviations 3, 4: `hD` and the fetch-view premise). -/
theorem cycleKillOfL2 (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (N : Nat) :
    freshEra gen σ0 →
    bootTie boot d0 im nh N σ0 →
    -- (b) THE WP PACKAGE, in the two flavours the exports need
    wpPackage hlc GF gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF gen σ0 D (Nm a base) a base) →
    -- (b') THE FETCH-VIEW PREMISE (deviation 4)
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    -- the two certification supplies (§6.3)
    cutSupply boot d0 im nh →
    certSupply boot d0 im nh N →
    -- THE L2′ CLAIM
    l2Claim boot d0 im nh P (badRun gen σ0) →
    cycleKill boot d0 im nh := by
  rintro hfr ⟨hb1, hb2, hb3⟩ hwp hwpp hcov hcut hcert hl2
  intro GD hcons hq hIH x hcyc
  -- (1) the cycle, as segments
  obtain ⟨z, ss, hne, hch⟩ := cycleSegments GD x hcons.2.1 hcyc
  -- (2) the cut, and the realized causal past
  obtain ⟨cs, hcutok⟩ := hcut GD z ss hcons hq hne hch
  obtain ⟨himg, hN⟩ := hb3 GD hq
  obtain ⟨c0, pst0, -, hrd0, -⟩ :=
    hullRun boot d0 im nh GD cs N hcons hq hcutok (hIH cs (cutOkProper _ _ hcutok)) hN
  -- (3) the certified configuration
  obtain ⟨c, pst, dv, hrd, hlog⟩ := hcert GD cs c0 pst0 z ss hcons hq hcutok hrd0 hne hch
  -- (4) the erased run, and the exports at its log
  obtain ⟨t2, σ2, hrtc, hlgeq⟩ :=
    runErased gen σ0 boot d0 N GD.gdG c pst dv hfr hcov hb1 hb2 himg hrd
  have hpr : protReg P (cdLog c c.cdTr.length) := by
    rw [← hlgeq]
    exact protRegOfRun hlc GF gen σ0 D hD Nm P t2 σ2 hfr hwpp hrtc
  -- (5) the per-site classification, and the kill
  have hnB : ¬ badRun gen σ0 := noBadRun hlc GF gen σ0 D hD hfr hwp
  exact cycleKillArms GD.gdG z ss hcons.1 hne
    (rawChainChain GD P (cdLog c c.cdTr.length) (badRun gen σ0) ss hcons hlog hpr hnB
      (hl2 GD hq (cdLog c c.cdTr.length) z ss hcons hlog hpr hne hch) z z ss
      (fun _ h => h) hch)

/-- … and T2-LIN itself. -/
theorem t2linOfL2 (hlc : HasLC) (GF : BundledGFunctors) [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (N : Nat) :
    freshEra gen σ0 →
    bootTie boot d0 im nh N σ0 →
    wpPackage hlc GF gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    cutSupply boot d0 im nh →
    certSupply boot d0 im nh N →
    l2Claim boot d0 im nh P (badRun gen σ0) →
    ∀ GD : Gdexec,
      rvwmoMinusDepsConsistent GD →
      gdexecQconf boot d0 im nh GD →
      ∀ x, ¬ tc (racyD GD) x x := by
  intro hfr hbt hwp hwpp hcov hcut hcert hl2
  exact t2linOfCycleKill boot d0 im nh
    (cycleKillOfL2 hlc GF gen σ0 D hD Nm P boot d0 im nh N hfr hbt hwp hwpp hcov hcut hcert hl2)

end glue

/-! # 7. NON-VACUITY, ON BOTH SIDES -/

theorem rsameRacyD (GD : Gdexec) (x y : Geid) : rsame GD x y → racyD GD x y := by
  rintro (h | h | h)
  · exact .inl (.inl h)
  · exact .inl (.inr (.inr (.inr (.inr h))))
  · exact .inr h

theorem rtcRsameRacyD (GD : Gdexec) (x y : Geid) : rtc (rsame GD) x y → rtc (racyD GD) x y := by
  intro h
  induction h with
  | refl => exact rtc_refl _
  | tail _ h ih => exact rtc_r ih (rsameRacyD GD _ _ h)

theorem rawChainTc (GD : Gdexec) (x y : Geid) (ss : List Seg) :
    ss ≠ [] → rawChain GD x y ss → tc (racyD GD) x y := by
  induction ss generalizing x with
  | nil => intro hne; exact absurd rfl hne
  | cons s ss ih =>
    intro _ hch
    obtain ⟨hx, hrun, hrest⟩ := hch
    have hstep : tc (racyD GD) x s.sgExit :=
      tc_rtc_r (tc_once (.inl (gcrossRacy GD.gdG _ _ hx))) (rtcRsameRacyD GD _ _ hrun)
    cases ss with
    | nil =>
      have hy : s.sgExit = y := hrest
      rw [← hy]
      exact hstep
    | cons s' ss' => exact tc_transitive hstep (ih _ (by simp) hrest)

/-- (a) THE DECOMPOSITION FIRES on a real cycle. -/
theorem lbgdSegments : ∃ z ss, ss ≠ [] ∧ rawChain lbgd z z ss := by
  obtain ⟨x, hx⟩ := lbgdCycle
  exact cycleSegments lbgd x (fun _ h => by simp [lbgd] at h) hx

/-- (b) THE CLAIM IS SATISFIABLE at the `racyD`-acyclic `mpgd`. -/
theorem l2ClaimMpgd (P : Int → Int → Prop) (Bad : Prop) : l2ClaimAt mpgd P Bad := by
  intro log z ss _ _ _ hne hch
  exact absurd (rawChainTc mpgd z z ss hne hch) (mpgdAcyclic z)

end Weak
