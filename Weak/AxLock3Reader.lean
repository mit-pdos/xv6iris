/-
Weak: **A7-T2c capstone (reader), part 1: `wpdReaderHartRel`, the per-hart `WPd` Löb induction
for the lock3s READER row** (`AxLock3Prog.l3pRRow`), release-sourced acquire, at the
`AxTierA2.axGA2` adequacy instance (AxSL tier).  The genesis-sourced capstone (`wpdReaderHart`,
Rocq §15–16) is in `Weak/AxLock3Reader2.lean`.

Rocq: `iris/AxLock3Reader.v` @ xxvzwolszwmp (§1–§14 here; §15–§16 in AxLock3Reader2).

## The Rocq header, in substance

The program-level post is HONEST: `PreaderPure` says the loaded byte `vB` is pinned by the
release that sources the reader's acquire, through that release's own hart's row-position-1
write to `x` (`∀ j v, grfe (j,3) (i,0) → gwritesByte (j,1) x v → vB = v`), and is `x`'s image
byte when the acquire reads `L`'s own image (genesis).  The file mirrors `AxLock3Writer`
(same section shape, the same `flowEqDynExistsSingleton` existential plumbing for the
release-sourced acquire), reusing its Φ-independent helpers (`wpdSkipStepOfLater`,
`gacqPoGobCat`, `gfenceCoversGobCat`, `gwritesByteOfStore`/`OfRmw`, the step inversions
`astepProgPlainWriteInv`/`astepProgFenceInv`/`astepProgRowEndShape`, `lbAdminWlWdataNone`) and
re-proving the Φ-dependent scaffolding: `wpdrPosShell` (clause (d) discharged by
`k ≠ row length`) and `wpdrRowEnd` (the row-end Löb, NONTRIVIAL: it carries the annotation
token `PpureTok` and reads the pure fact back off `postLifting`'s per-event big-sep via
`annotAgree`).

ROW SHAPE (`l3pRRow`): `LRmw(acq); LLoad x; LFence rw,w; LStore L unlocked(rel)`, plus one
ADMINISTRATIVE program point (the `regWrite` recording the loaded byte into `x10`) inside row
position 2, before the fence's own step.

Structure: §1 the register-generic monad states `rM0..rM4`; §2 `PreaderPure`/`Φreader`/
`Ppure`/`PpureTok`; §3 `wpdrPosShell`; §4 `wpdrRowEnd`; §5 position 3 (the release; the reader
never writes `x`, so its release hands the token back UNCHANGED, `e_last` the READ (i,1)); §6
position 2 (fence) and the admin `regWrite`; §7 position-0/1 graph and step facts; §8 the
release-sourced section: the source hart `j0`'s row (`l3pWRow`-shaped), `wrelPoLatestPin`,
THE OWNED READ `r1FlowEq` (`AxLockOwn.lockReadOwn` + `AxProtLock.tokRetieOb`, re-tying the
acquire's token to the read, and `protInvReadStep`), the bridge `PreaderPureHolds`, `wpdrW1`
(the read position: clause (a) is a real `wpEvStep` depositing `R1e ∗ ⌜PreaderPure⌝`, split by
`annotSplit` into `(i,1) ↦ₐ R1e` and `PpureTok`), position 0 and the capstone
`wpdReaderHartRel`.

**Fetches.** None: the reader's programs are hand-built monad terms with no fetch node.  The
step clause's boot-image pin premise (`WeakAxRealize.fetchPin`, owner Q8) is never needed.

## Deviations from Rocq

1. NAMES: camelCase (map below).  `r_m0` and `R1e` are in the duplicated-name table, hence
   `AxLock3Reader.rM0`/`AxLock3Reader.R1e`.  Lean-only helper (file-qualified):
   `AxLock3Reader.twpdr` (Rocq's local notation `TWPDr s`).
2. THE INSTANCE: Rocq's `Local Instance AxGA2_lock3R` ↦ the named `axGA2Lock3 L x GD nm`
   (AxLock3Wp), passed explicitly; the policy `lock_axpol` ↦ the named `lockAxpol`
   (AxProtLock3).  `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc`.
3. O2 STAGE C: Rocq's fetch oracle `T` and the section hypothesis `HTx : ¬ T x` are GONE
   (`AxOpsem.astepProg` has no fetch constructor; Rocq used `HTx` only to refute the fetch arm of
   `r1_astep_prog_vacuous`).  The step clause (b) of `WPd` takes the image pin premise, ignored.
4. SECTION CONTEXT: Rocq's `Hxy HLram Hxram HLeq Hxeq Hrow Hcons` and the `RRel` context
   `w_rel Hwrel_wb0 Hgob_rel Hrfe_rel j0 t0 old0 v0 Heq_wrel Hrow_j0` are explicit arguments of
   exactly the lemmas whose statements or proofs use them, in that order.  `Preader_pure`/
   `Φreader`/`Ppure`/`Ppure_tok` are top-level definitions over `L x GD i vB`.
5. STATEMENT SHAPES (as AxLock3Writer deviation 4): `P -∗ Q` ↦ `P ⊢ Q`; `s_pol GD e` ↦
   `lockPolS GD e`; `lobp` ↦ `@Axpol.lobp lockAxpol`; `e ↦ₐ P` ↦ `AxAnnot.annotOwn e P`;
   `Interface.Ret tt` ↦ `.pure ()`; Rocq's `RegWrite (R_bitvector_64 x10) None
   (Z_to_bv 64 (bv_unsigned vw))` ↦ lean-sail `.regWrite .x10 (BitVec.ofNat 64 vw.toNat)` (no
   access-kind argument), as `AxLock3Prog.l3pRM2b`; `register_set` ↦ `RegFile.set`;
   `dev0_state` ↦ an arbitrary `Efab` in `rPstepRegw` (stronger).
6. The capstone: Rocq's `init_regstate` ↦ an arbitrary register file `rs` (AxLock3Prog
   deviation 4): `wpdReaderHartRel` is stated at `l3pRP0 Lpa xpa cpu rs` for every `rs`.
7. PROOF ROUTE (not statements): `r3FlowEq` is derived from `AxLock3Wp.lockRelFlowEq3A`
   (via `tokTieXTok`) instead of Rocq's self-contained copy of its script (Rocq copied it only to
   avoid guessing post-section argument orders); `fedsR` is `flowEqDynExistsSingleton`; the
   row-shape facts `r3Wb`/`r3Single`/`r0Wb`/`r0Single` use `AxLock3Writer.gwritesByteOfStore`/
   `OfRmw`; `r1NoXwriteHartI` reuses `rNoXwriteBeforeRel`; `r1FlowEq` keeps the token across the
   value derivation by `persistent_entails_left` (Rocq: a persistent `iAssert`), and its pure
   rf-source facts are derived before the protocol state is opened.

**Rocq → Lean name map.**  `r_m4/m3/m2b/m2/m1` `rM4/rM3/rM2b/rM2/rM1`, `r_m0`
`AxLock3Reader.rM0`, `Preader_pure` `PreaderPure`, `Φreader` `Φreader`, `Ppure` `Ppure`,
`Ppure_tok` `PpureTok`, `Φreader_of_Ppure` `ΦreaderOfPpure`, `wpdr_pos_shell` `wpdrPosShell`,
`wpdr_row_end` `wpdrRowEnd`, `wpdr_w4` `wpdrW4`, `r_lbl2` `rLbl2`, `r_gmem1` `rGmem1`,
`r_gfence_covers_xread_rel` `rGfenceCoversXreadRel`, `r_xread_in_lobp_rel` `rXreadInLobpRel`,
`r3_lbl3/wb/single/gd/gob` `r3Lbl3/Wb/Single/Gd/Gob`, `lock3_ob_st_interp_Ar`
`lock3ObStInterpAr`, `r_no_xwrite_before_rel` `rNoXwriteBeforeRel`, `r3_po_latest`
`r3PoLatest`, `R1e` `AxLock3Reader.R1e`, `r3_flow_eq` `r3FlowEq`, `feds_r` `fedsR`,
`r3_flow_eq_e` `r3FlowEqE`, `wpdr_w3` `wpdrW3`, `wpdr_w2` `wpdrW2`, `r_pstep_regw`
`rPstepRegw`, `r_regw_det` `rRegwDet`, `r_regw_inv` `rRegwInv`, `wpdr_w2b` `wpdrW2b`,
`r0_lbl0/wb/single/gd` `r0Lbl0/Wb/Single/Gd`, `r1_lbl1` `r1Lbl1`, `r1_rd_ex` `r1RdEx`,
`r1_gacq_po` `r1GacqPo`, `r1_gis_w` `r1GisW`, `r1_no_write` `r1NoWrite`,
`r1_no_xwrite_hart_i` `r1NoXwriteHartI`, `r0_only_reads_L` `r0OnlyReadsL`, `r1_rd_concrete`
`r1RdConcrete`, `r1_read_det` `r1ReadDet`, `r1_astep_prog_vacuous` `r1AstepProgVacuous`,
`r0_read_det` `r0ReadDet`, `astep_prog_write0_rel_inv` `astepProgWrite0RelInv`,
`astep_prog_read0_rel_vacuous` `astepProgRead0RelVacuous`, `j0_lbl1/2/3` `j0Lbl1/2/3`,
`j0_wb1` `j0Wb1`, `j0_gpo13` `j0Gpo13`, `j0_no_xwrite_between` `j0NoXwriteBetween`,
`wrel_po_latest_pin` `wrelPoLatestPin`, `R0er` `R0er`, `r1_flow_eq` `r1FlowEq`, `grfe_to_L`
`grfeToL`, `wrel_grfe` `wrelGrfe`, `Preader_pure_holds` `PreaderPureHolds`,
`r1_flow_eq_bundled` `r1FlowEqBundled`, `r1_flow_eq_e` `r1FlowEqE`, `r1_flow_eq_wp`
`r1FlowEqWp`, `wpdr_w1` `wpdrW1`, `r0_flow_eq_rel` `r0FlowEqRel`, `wpdr_w0_write_rel`
`wpdrW0WriteRel`, `wpdr_w0_read_rel` `wpdrW0ReadRel`, `wpd_reader_hart_rel`
`wpdReaderHartRel`.  (§15–16: see AxLock3Reader2.)

**Dropped:** nothing (Rocq 85 definitions/lemmas plus the `Local Instance` (deviation 2):
73 here, 12 in AxLock3Reader2; Lean-only: `AxLock3Reader.twpdr`).  **Not ported:** the `Print Assumptions`
lines (the lint's axiom check covers them).
-/
import Weak.AxLock3Writer

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! ## 2. The postcondition -/

/-- THE REAL, PROGRAM-LEVEL POST: `vB` is pinned by the release sourcing the acquire, through
that release's hart's position-1 `x`-write; and is `x`'s image byte on a genesis acquire. -/
def PreaderPure (L x : Int) (GD : Gdexec) (i : Agent) (vB : BitVec 8) : Prop :=
  (∀ (j : Agent) (v : BitVec 8), grfe GD.gdG (j, 3) (i, 0) → gwritesByte GD.gdG (j, 1) x v →
    vB = v) ∧
  (greadsByte GD.gdG (i, 0) L 0 b0 → ∀ bx, GD.gdG.gxImg x = some bx → vB = bx)

abbrev Φreader {GF : BundledGFunctors} (L x : Int) (GD : Gdexec) (i : Agent) (vB : BitVec 8)
    (_s : Athread) : IProp GF :=
  iprop(⌜PreaderPure L x GD i vB⌝)

/-- 2.1 The bare ownership fact. -/
abbrev Ppure {GF : BundledGFunctors} (L x : Int) (GD : Gdexec) (i : Agent) (vB : BitVec 8) :
    IProp GF :=
  iprop(⌜PreaderPure L x GD i vB⌝)

/-- The annotation-backed carrier for `Ppure`, deposited at `(i,1)` alongside `R1e`. -/
abbrev PpureTok {GF : BundledGFunctors} [AxannotGS GF] (L x : Int) (GD : Gdexec) (i : Agent)
    (vB : BitVec 8) : IProp GF :=
  AxAnnot.annotOwn (i, 1) (Ppure L x GD i vB)

theorem ΦreaderOfPpure {GF : BundledGFunctors} (L x : Int) (GD : Gdexec) (i : Agent)
    (vB : BitVec 8) (s : Athread) : Ppure (GF := GF) L x GD i vB ⊢ Φreader L x GD i vB s :=
  .rfl

/-- Lean-only: Rocq's local notation `TWPDr s` — `tierAWpd` at the lock3s protocol,
stuckness `MaybeStuck`, hart `i`, the postcondition `Φreader`. -/
def AxLock3Reader.twpdr (GF : BundledGFunctors.{0,0,0}) [AxlogG GF Hent] [AxLockG GF]
    (hlc : HasLC) [InvGS_gen hlc GF] [AxannotGS GF] (L x : Int) (GD : Gdexec) (nm : lock3N)
    (i : Agent) (vB : BitVec 8) (s : Athread) : IProp GF :=
  @tierAWpd GF hlc _ _ lockAxpol GD lock3N lock3ObSt0 (lock3ObStInterp0 L x) nm s .MaybeStuck i
    (Φreader L x GD i vB)

section reader

variable {GF : BundledGFunctors.{0,0,0}} [AxlogG GF Hent] [AxLockG GF] (L x : Int)
variable {hlc : HasLC} [InvGS_gen hlc GF] [AxannotGS GF] (GD : Gdexec) (nm : lock3N)
variable (Lpa xpa : PAddr) (cpu : CPU) (i : Agent) (t : Nat) (old : BitVec 8) (tx : Nat)
  (vB : BitVec 8)

/-! ## 1. The reader's own monad states (register-generic) -/

def rM4 : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP Lpa b0))) (fun _ => .pure ())
def rM3 : SailM Unit :=
  .impure (.ok (.barrier .Barrier_RISCV_rw_w)) (fun _ => rM4 Lpa)
def rM2b (vw : BitVec 8) : SailM Unit :=
  .impure (.ok (.regWrite .x10 (BitVec.ofNat 64 vw.toNat))) (fun _ => rM3 Lpa)
def rM2 : SailM Unit :=
  .impure (.ok (.memRead 1 64 (l3pRreq l3pAkP xpa)))
    (fun ans => rM2b Lpa (match ans with | .Ok (w, _) => w | .Err _ => b0))
def rM1 : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkXpl Lpa b1))) (fun _ => rM2 Lpa xpa)
def AxLock3Reader.rM0 : SailM Unit :=
  .impure (.ok (.memRead 1 64 (l3pRreq l3pAkXaq Lpa))) (fun _ => rM1 Lpa xpa)

/-! ## 3. The position shell at `Φreader` -/

/-- Clauses (a)/(c) as `AxLock3Writer.wpdPosShell`; clause (d) vacuous (`k` is not the row
end); clause (b) supplied as `Hb`. -/
theorem wpdrPosShell (P : IProp GF) (k : Nat) (m : SailM Unit)
    (Hne : k ≠ (AxOpsem.grow GD i).length)
    (Hrowk_nonread : ∀ lb, (AxOpsem.grow GD i)[k]? = some lb → aidentRd (aident lb) = none)
    (Hb : ∀ (rs : RegFile) (l : Wlabel) (s' : Athread),
      AxOpsem.astepProg (AxOpsem.grow GD i) ⟨.PHart cpu m rs none ibNone, k⟩ l s' →
      P ⊢ match wlWdata l with
        | some data =>
            @wpEvStep hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol Unit GD i k (fun _ => True)
              (fun _ => graphData GD (i, k) = some data) (fun _ => s'.atK)
              (fun _ => AxLock3Reader.twpdr GF hlc L x GD nm i vB s')
        | none => @wpSkipStep GF (axGA2Lock3 L x GD nm) GD i s'.atK
            (AxLock3Reader.twpdr GF hlc L x GD nm i vB s')) :
    P ⊢ ∀ rs : RegFile,
      AxLock3Reader.twpdr GF hlc L x GD nm i vB ⟨.PHart cpu m rs none ibNone, k⟩ := by
  have H : ⊢ ∀ rs : RegFile, P -∗
      AxLock3Reader.twpdr GF hlc L x GD nm i vB ⟨.PHart cpu m rs none ibNone, k⟩ := by
    iloeb as IH
    iintro %rs HP
    unfold AxLock3Reader.twpdr tierAWpd
    iapply (@AxWpD.wpdMUnfoldStep hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol rvwmoCatConsistent
      .MaybeStuck i _ _).2
    isplit
    · iapply (@progressOblMaybestuck GF (axGA2Lock3 L x GD nm) lockAxpol i _).2
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, -⟩
    ihave %Hg := AxLock3Writer.gconstPure L x GD nm GD' $$ Hg
    subst GD'
    isplit
    · iintro %id %K %Hst
      obtain ⟨lb, Hlk, Hid, Hsome, -⟩ := Hst
      have Hnone : aidentRd id = none := by rw [← Hid]; exact Hrowk_nonread lb Hlk
      rw [Hnone] at Hsome
      cases Hsome
    isplit
    · iintro %l %s' %Hst %-
      have Hb' := Hb rs l s' Hst
      unfold AxLock3Reader.twpdr tierAWpd at Hb'
      dsimp only
      iapply Hb' $$ HP
    isplit
    · iintro %s' %Hw
      obtain ⟨rs', rfl⟩ := l3pAwireRsOnly cpu m rs none ibNone k s' Hw
      iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
      inext
      iapply IH $$ %rs' HP
    · iintro %Heq
      exact (Hne Heq).elim
  iintro HP %rs
  iapply H $$ %rs HP

/-! ## 4. The row end, NONTRIVIAL Φ -/

/-- 4. THE ROW END: past the row every step is administrative; at `postLifting` the token
`PpureTok` agrees with the annotation map and the per-event big-sep exposes `Ppure`. -/
theorem wpdrRowEnd (k0 : Nat) (Hend : (AxOpsem.grow GD i).length ≤ k0) (p : Pexv6) :
    PpureTok (GF := GF) L x GD i vB ⊢ AxLock3Reader.twpdr GF hlc L x GD nm i vB ⟨p, k0⟩ := by
  have Hnone : (AxOpsem.grow GD i)[k0]? = none := List.getElem?_eq_none Hend
  have H : ⊢ ∀ p : Pexv6, PpureTok (GF := GF) L x GD i vB -∗
      AxLock3Reader.twpdr GF hlc L x GD nm i vB ⟨p, k0⟩ := by
    iloeb as IH
    iintro %p Hp
    unfold AxLock3Reader.twpdr tierAWpd
    iapply (@AxWpD.wpdMUnfoldStep hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol rvwmoCatConsistent
      .MaybeStuck i _ _).2
    isplit
    · iapply (@progressOblMaybestuck GF (axGA2Lock3 L x GD nm) lockAxpol i _).2
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, -⟩
    ihave %Hg := AxLock3Writer.gconstPure L x GD nm GD' $$ Hg
    subst GD'
    isplit
    · iintro %id %K %Hst
      obtain ⟨lb, Hlb, -⟩ := Hst
      simp only at Hlb
      rw [Hnone] at Hlb
      cases Hlb
    isplit
    · iintro %l %s' %Hst %-
      obtain ⟨Hadm, Hk', -⟩ := astepProgRowEndShape _ _ l s' Hnone Hst
      rw [lbAdminWlWdataNone l Hadm]
      obtain ⟨p', k1⟩ := s'
      simp only at Hk'
      subst Hk'
      iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
      inext
      iapply IH $$ %p' Hp
    isplit
    · iintro %s' %Hw
      obtain ⟨p', k1⟩ := s'
      obtain ⟨Hk, -⟩ := Hw
      simp only at Hk
      subst Hk
      iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
      inext
      iapply IH $$ %p' Hp
    · iintro %-
      unfold postLifting
      iintro %na Hna
      have hag : AxirisG.annotInterp (self := axGA2Lock3 (GF := GF) L x GD nm) na ∗
          PpureTok (GF := GF) L x GD i vB ⊢
          iprop(⌜(i, 1) ∈ (FiniteMap.dom_set na : GSet Geid)⌝ ∗
            AxWp.fromOption (fun P' => iprop(▷ □ (P' -∗ Ppure (GF := GF) L x GD i vB)))
              iprop(emp) (get? na (i, 1))) := by
        iintro ⟨Hna, Hp⟩
        iapply annotAgree na (i, 1) (Ppure (GF := GF) L x GD i vB) $$ Hna Hp
      cases hget : get? na (i, 1) with
      | none =>
        rw [hget] at hag
        simp only [AxWp.fromOption] at hag
        icases persistent_entails_left hag $$ [$Hna $Hp] with ⟨-, %Hdom, -⟩
        have h := elemOfDom.1 Hdom
        rw [hget] at h
        cases h
      | some P0 =>
        rw [hget] at hag
        simp only [AxWp.fromOption] at hag
        icases persistent_entails_left hag $$ [$Hna $Hp] with ⟨⟨Hna, -⟩, %Hdom, #Hw⟩
        imodintro
        isplitl [Hna]
        · iexact Hna
        iintro Hbig
        have Hlk : ([∗map] e ↦ R ∈ na, if e.1 = i then R else iprop(True)) ⊢ P0 :=
          (BigSepM.bigSepM_lookup (Φ := fun e R => if e.1 = i then R else iprop(True)) hget).trans
            (by dsimp only; rw [if_pos rfl])
        ihave HP0 := Hlk $$ Hbig
        inext
        ihave Hpp := Hw $$ HP0
        imodintro
        iexact Hpp
  iintro Hp
  iapply H $$ %p Hp

theorem wpdrW4 (p : Pexv6) :
    PpureTok (GF := GF) L x GD i vB ⊢
      AxLock3Reader.twpdr GF hlc L x GD nm i vB ⟨p, (AxOpsem.grow GD i).length⟩ :=
  wpdrRowEnd L x GD nm i vB _ (Nat.le_refl _) p

/-! ## 5. Position 3 — the release -/

theorem rLbl2 (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) :
    gxLbl GD.gdG (i, 2) = some (.LFence true true false true) :=
  AxWp.growLookup GD i 2 _ (by rw [Hrow]; rfl)

theorem rGmem1 (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) :
    gmem GD.gdG (i, 1) :=
  ⟨_, l3pRLbl1 Lpa xpa GD i t old tx vB Hrow, rfl⟩

/-- RULE 4 at the release: the READ is `pr`-covered by the row's own `rw,w` fence. -/
theorem rGfenceCoversXreadRel (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) :
    gfenceCovers GD.gdG (i, 1) (i, 3) :=
  ⟨true, true, false, true,
    ⟨rfl, by simp, 2, by simp, by simp, rLbl2 GD Lpa xpa i t old tx vB Hrow⟩,
    .inl ⟨⟨_, l3pRLbl1 Lpa xpa GD i t old tx vB Hrow, rfl⟩, rfl⟩,
    .inr ⟨⟨_, l3pRLbl3 Lpa xpa GD i t old tx vB Hrow, rfl⟩, rfl⟩⟩

theorem rXreadInLobpRel (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB)
    (Hcons : rvwmoCatConsistent GD) : (i, 1) ∈ @Axpol.lobp lockAxpol GD (i, 3) :=
  l3pLobpIntro GD _ _ Hcons.1 (rGmem1 GD Lpa xpa i t old tx vB Hrow)
    (.inr (.inr (.inr (.inl (rGfenceCoversXreadRel GD Lpa xpa i t old tx vB Hrow)))))

theorem r3Lbl3 (HLeq : L = l3pLbase Lpa) (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) :
    gxLbl GD.gdG (i, 3) = some (.LStore false L [b0] .WCplain) := by
  rw [HLeq]
  exact l3pRLbl3 Lpa xpa GD i t old tx vB Hrow

theorem r3Wb (HLeq : L = l3pLbase Lpa) (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) :
    gwritesByte GD.gdG (i, 3) L b0 :=
  (gwritesByteOfStore GD (i, 3) L b0 .WCplain (r3Lbl3 L GD Lpa xpa i t old tx vB HLeq Hrow)).1

theorem r3Single (HLeq : L = l3pLbase Lpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) :
    ∀ a' v', gwritesByte GD.gdG (i, 3) a' v' → a' = L :=
  (gwritesByteOfStore GD (i, 3) L b0 .WCplain (r3Lbl3 L GD Lpa xpa i t old tx vB HLeq Hrow)).2

theorem r3Gd (HLeq : L = l3pLbase Lpa) (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) :
    graphData GD (i, 3) = some [b0] := by
  simp only [graphData, r3Lbl3 L GD Lpa xpa i t old tx vB HLeq Hrow, Option.bind_some, lblData]

theorem r3Gob (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) :
    gobCat GD (i, 1) (i, 3) :=
  gfenceCoversGobCat GD _ _ (rGfenceCoversXreadRel GD Lpa xpa i t old tx vB Hrow)

theorem lock3ObStInterpAr (g : Bool) (D : GSet Geid) (hm : GMapF Geid (List Hent))
    (s : GSet Geid) :
    AxirisG.obStInterp (self := axGA2Lock3 (GF := GF) L x GD nm) GD
        ((g, D, hm) : Bool × GSet Geid × GMapF Geid (List Hent)) s ⊣⊢
      protInvLock3 L x nm.1 nm.2 GD s D hm g :=
  .rfl

/-- 5.0 THE READER'S ROW LEMMA: the row never writes `x` before its release. -/
theorem rNoXwriteBeforeRel (hxy : x ≠ L) (HLeq : L = l3pLbase Lpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (w' : Geid) (v' : BitVec 8) :
    gwritesByte GD.gdG w' x v' → WeakRvwmoGraph.gpo GD.gdG w' (i, 3) → False := by
  intro Hwb ⟨Heq1, Hlt, _, _⟩
  obtain ⟨j, k⟩ := w'
  simp only at Heq1 Hlt
  subst Heq1
  obtain ⟨l, base, vs, jj, Hl, Hwr, Hvs, Hacc⟩ := Hwb
  match k, Hlt with
  | 0, _ =>
    rw [l3pRLbl0 Lpa xpa GD j t old tx vB Hrow, Option.some.injEq] at Hl
    subst Hl
    simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hwr
    obtain ⟨rfl, rfl⟩ := Hwr
    cases jj with
    | zero =>
      simp only [accAddr] at Hacc
      exact hxy (by rw [HLeq]; omega)
    | succ jj => simp at Hvs
  | 1, _ =>
    rw [l3pRLbl1 Lpa xpa GD j t old tx vB Hrow, Option.some.injEq] at Hl
    subst Hl
    simp [lbWr] at Hwr
  | 2, _ =>
    rw [rLbl2 GD Lpa xpa j t old tx vB Hrow, Option.some.injEq] at Hl
    subst Hl
    simp [lbWr] at Hwr
  | k + 3, Hlt => exact absurd Hlt (by omega)

theorem r3PoLatest (hxy : x ≠ L) (HLeq : L = l3pLbase Lpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hl : List Hent) :
    lockHhPoLatest x GD Hl (i, 3) := by
  intro w' v' Hwb Hpo
  exact (rNoXwriteBeforeRel L x GD Lpa xpa i t old tx vB hxy HLeq Hrow w' v' Hwb Hpo).elim

/-- The acquire's re-tied token, moved to the read `(i,1)`, with the history's
well-formedness. -/
def AxLock3Reader.R1e : IProp GF :=
  iprop(∃ Hl : List Hent, tokTie GD nm.1 x Hl {[(i, 1) := (1 : Qp)]} ∗ ⌜histXWf x GD Hl⌝)

/-- 5.1 The release's flow equation, the token handed back UNCHANGED from the read. -/
theorem r3FlowEq (hxy : x ≠ L) (HLeq : L = l3pLbase Lpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hcons : rvwmoCatConsistent GD)
    (Hl : List Hent) :
    ⊢ @flowEqDyn hlc GF _ (axGA2Lock3 L x GD nm) GD (i, 3) (lockPolS GD (i, 3))
        {[(i, 1) := iprop(tokTie GD nm.1 x Hl {[(i, 1) := (1 : Qp)]} ∗ ⌜histXWf x GD Hl⌝)]}
        iprop(True ∗ ⌜graphData GD (i, 3) = some [b0]⌝) := by
  have Hr := lockRelFlowEq3A (hlc := hlc) L x GD nm GD (i, 3) (i, 1) Hl
    {[(i, 1) := iprop(tokTie (GF := GF) GD nm.1 x Hl {[(i, 1) := (1 : Qp)]} ∗
      ⌜histXWf x GD Hl⌝)]} Hcons
    (r3Wb L GD Lpa xpa i t old tx vB HLeq Hrow)
    (r3Single L GD Lpa xpa i t old tx vB HLeq Hrow) (r3Gob GD Lpa xpa i t old tx vB Hrow)
  iapply (@flowEqDynMono hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol GD (i, 3) (lockPolS GD (i, 3))
    _ iprop(True) iprop(True ∗ ⌜graphData GD (i, 3) = some [b0]⌝))
  · inext
    iintro -
    isplitr
    · itrivial
    · ipureintro
      exact r3Gd L GD Lpa xpa i t old tx vB HLeq Hrow
  · iapply Hr
    iintro Hin
    ihave Hin := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ Hin
    icases Hin with ⟨Htie, %Hxwf⟩
    isplitl [Htie]
    · iapply tokTieXTok
      iexact Htie
    · ipureintro
      exact ⟨Hxwf, r3PoLatest L x GD Lpa xpa i t old tx vB hxy HLeq Hrow Hl⟩

/-- `AxLock3Writer.flowEqDynExistsSingleton`, under the reader's name. -/
theorem fedsR {A : Type} (k : Geid) (Pk Q : A → IProp GF) (e : Geid) (sOb0 : GSet Geid) :
    (∀ a : A, ⊢ @flowEqDyn hlc GF _ (axGA2Lock3 L x GD nm) GD e sOb0 {[k := Pk a]} (Q a)) →
    ⊢ @flowEqDyn hlc GF _ (axGA2Lock3 L x GD nm) GD e sOb0 {[k := iprop(∃ a, Pk a)]}
        iprop(∃ a, Q a) :=
  flowEqDynExistsSingleton L x GD nm k Pk Q e sOb0

theorem r3FlowEqE (hxy : x ≠ L) (HLeq : L = l3pLbase Lpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hcons : rvwmoCatConsistent GD) :
    ⊢ @flowEqDyn hlc GF _ (axGA2Lock3 L x GD nm) GD (i, 3) (lockPolS GD (i, 3))
        {[(i, 1) := AxLock3Reader.R1e (GF := GF) x GD nm i]}
        iprop(True ∗ ⌜graphData GD (i, 3) = some [b0]⌝) := by
  iapply (@flowEqDynMono hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol GD (i, 3) (lockPolS GD (i, 3))
    _ iprop(∃ _Hl : List Hent, True ∗ ⌜graphData GD (i, 3) = some [b0]⌝)
    iprop(True ∗ ⌜graphData GD (i, 3) = some [b0]⌝))
  · inext
    iintro ⟨%_, H⟩
    iexact H
  · unfold AxLock3Reader.R1e
    iapply (fedsR (hlc := hlc) L x GD nm (i, 1)
      (fun Hl => iprop(tokTie (GF := GF) GD nm.1 x Hl {[(i, 1) := (1 : Qp)]} ∗
        ⌜histXWf x GD Hl⌝))
      (fun _ => iprop(True ∗ ⌜graphData GD (i, 3) = some [b0]⌝)) (i, 3) (lockPolS GD (i, 3))
      (fun Hl => r3FlowEq L x GD nm Lpa xpa i t old tx vB hxy HLeq Hrow Hcons Hl))

/-- 5.2 Position 3 assembled. -/
theorem wpdrW3 (hxy : x ≠ L) (HLram : devAddr Lpa = false) (HLeq : L = l3pLbase Lpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hcons : rvwmoCatConsistent GD) :
    iprop(AxAnnot.annotOwn (i, 1) (AxLock3Reader.R1e (GF := GF) x GD nm i) ∗
        PpureTok (GF := GF) L x GD i vB) ⊢
      ∀ rs : RegFile,
        AxLock3Reader.twpdr GF hlc L x GD nm i vB ⟨.PHart cpu (rM4 Lpa) rs none ibNone, 3⟩ := by
  apply wpdrPosShell L x GD nm cpu i vB _ 3 (rM4 Lpa) (by rw [Hrow]; simp [l3pRRow])
  · intro lb Hlk
    rw [Hrow] at Hlk
    simp only [l3pRRow, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
      at Hlk
    subst Hlk
    rfl
  · intro rs l s' Hstep
    obtain ⟨rfl, rfl⟩ := astepProgPlainWriteInv GD cpu i Lpa HLram b0 (fun _ => .pure ()) rs 3
      ⟨.PHart cpu (rM4 Lpa) rs none ibNone, 3⟩ rfl rfl l s' Hstep
    simp only [wlWdata, l3pWbytes1]
    unfold wpEvStep naAtProgress
    iintro ⟨Hpt1, Hpp⟩ %na ⟨%Hprog, Hannot⟩
    have Hin1 : (i, 1) ∈ (FiniteMap.dom_set na : GSet Geid) := by
      have h : (i, 1) ∈ eidsBefore GD i 3 :=
        (elemOfEidsBefore GD i 3 _).2 ⟨rfl, by simp, by
          simp only [gmemB, l3pRLbl1 Lpa xpa GD i t old tx vB Hrow]; rfl⟩
      rw [← Hprog] at h
      exact (elemOfFilter.1 h).2
    obtain ⟨P', HP'⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 Hin1)
    have Hdet : ⊢ AxAnnot.annotInterp na -∗
        AxAnnot.annotOwn (i, 1) (AxLock3Reader.R1e (GF := GF) x GD nm i) ==∗
        ∃ R, AxAnnot.annotInterp (insert na (i, 1) R) ∗
          iprop(▷ □ (P' -∗ AxLock3Reader.R1e (GF := GF) x GD nm i ∗ R)) := by
      have h := annotDetach na (i, 1) (AxLock3Reader.R1e (GF := GF) x GD nm i)
      rw [HP'] at h
      exact h
    imod Hdet $$ Hannot Hpt1 with ⟨%R, Hannot', Hwand⟩
    ihave Hfeq := r3FlowEqE (hlc := hlc) L x GD nm Lpa xpa i t old tx vB hxy HLeq Hrow Hcons
    have Hnin : (i, 3) ∉ (FiniteMap.dom_set (insert na (i, 1) R) : GSet Geid) := by
      rw [domInsert, elemOfUnion, elemOfSingleton]
      rintro (Heq | Hik)
      · simp at Heq
      · have Hf : (i, 3) ∈ FiniteSet.filter (fun e : Geid => decide (e.1 = i))
            (FiniteMap.dom_set na : GSet Geid) := elemOfFilter.2 ⟨by simp, Hik⟩
        rw [Hprog, elemOfEidsBefore] at Hf
        exact Nat.lt_irrefl _ Hf.2.1
    imod (annotAlloc (insert na (i, 1) R) (i, 3) iprop(True) Hnin) $$ Hannot' with ⟨Hannot'', -⟩
    imodintro
    inext
    imodintro
    iexists (), iprop(True), {[(i, 1) := AxLock3Reader.R1e (GF := GF) x GD nm i]},
      {[(i, 1) := R]}, ()
    isplitr
    · ipureintro
      trivial
    isplitl [Hwand]
    · unfold naSplittingWf
      isplitr
      · ipureintro
        rw [domSingleton]
        exact singletonSubseteqL.2 (rXreadInLobpRel GD Lpa xpa i t old tx vB Hrow Hcons)
      · iapply (BigSepM2.bigSepM2_singleton _ (i, 1)
          (AxLock3Reader.R1e (GF := GF) x GD nm i) R).2
        simp only [HP', AxWp.fromOption]
        inext
        iexact Hwand
    isplitl [Hfeq]
    · iexact Hfeq
    isplitl [Hannot'']
    · rw [← AxLock3Writer.annotEq]
      iexact Hannot''
    isplitr
    · iapply AxLock3Writer.localTriv
    · ihave H := (wpdrRowEnd (hlc := hlc) L x GD nm i vB (3 + 1) (by rw [Hrow]; simp [l3pRRow])
        (.PHart cpu (.pure ()) rs none ibNone)) $$ Hpp
      iexact H

/-! ## 6. Position 2 — the fence, and the admin `regWrite` -/

theorem wpdrW2 (hxy : x ≠ L) (HLram : devAddr Lpa = false) (HLeq : L = l3pLbase Lpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hcons : rvwmoCatConsistent GD) :
    iprop(AxAnnot.annotOwn (i, 1) (AxLock3Reader.R1e (GF := GF) x GD nm i) ∗
        PpureTok (GF := GF) L x GD i vB) ⊢
      ∀ rs : RegFile,
        AxLock3Reader.twpdr GF hlc L x GD nm i vB ⟨.PHart cpu (rM3 Lpa) rs none ibNone, 2⟩ := by
  apply wpdrPosShell L x GD nm cpu i vB _ 2 (rM3 Lpa) (by rw [Hrow]; simp [l3pRRow])
  · intro lb Hlk
    rw [Hrow] at Hlk
    simp only [l3pRRow, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
      at Hlk
    subst Hlk
    rfl
  · intro rs l s' Hstep
    obtain ⟨rfl, rfl⟩ := astepProgFenceInv GD cpu i (fun _ => rM4 Lpa) rs 2
      ⟨.PHart cpu (rM3 Lpa) rs none ibNone, 2⟩ rfl rfl l s' Hstep
    simp only [wlWdata]
    iintro HP
    iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
    inext
    ihave H := (wpdrW3 (hlc := hlc) L x GD nm Lpa xpa cpu i t old tx vB hxy HLram HLeq Hrow
      Hcons) $$ HP
    iapply H

theorem rPstepRegw (vw : BitVec 8) (rs : RegFile) (d : Efab) :
    pstepProg (.PHart cpu (rM2b Lpa vw) rs none ibNone) d (erwLabel (erwOf .ORnone [] .x10))
      (.PHart cpu (rM3 Lpa) (rs.set .x10 (BitVec.ofNat 64 vw.toNat)) none ibNone) d :=
  ⟨rfl, some (rs.set .x10 (BitVec.ofNat 64 vw.toNat)), none, none, rfl, rfl,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

/-- The `regWrite` head redex's determinism. -/
theorem rRegwDet (vw : BitVec 8) (rs : RegFile) (d : Efab) (l0 : Wlabel) (p' : Pexv6)
    (d' : Efab) :
    pstepProg (.PHart cpu (rM2b Lpa vw) rs none ibNone) d l0 p' d' →
    l0 = erwLabel (erwOf .ORnone [] .x10) ∧
    p' = .PHart cpu (rM3 Lpa) (rs.set .x10 (BitVec.ofNat 64 vw.toNat)) none ibNone ∧ d' = d := by
  intro h
  cases p' with
  | PDisk _ => exact False.elim h
  | PHart cpu' m' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hn, hd⟩ := h
    obtain ⟨rfl, rfl, rfl, rfl, hdd, rfl, rfl⟩ := hn
    exact ⟨rfl, rfl, by rw [hd, hdd]⟩

/-- `astepProg`'s inversion at the admin `regWrite`. -/
theorem rRegwInv (vw : BitVec 8) (rs : RegFile) (s : Athread)
    (Heqp : s.atP = .PHart cpu (rM2b Lpa vw) rs none ibNone) (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg (AxOpsem.grow GD i) s l s' →
    l = erwLabel (erwOf .ORnone [] .x10) ∧
    s' = ⟨.PHart cpu (rM3 Lpa) (rs.set .x10 (BitVec.ofNat 64 vw.toNat)) none ibNone, s.atK⟩ := by
  intro h
  cases h with
  | AStepAdmin p k0 d l0 p' d' _ hst =>
    simp only at Heqp
    subst Heqp
    obtain ⟨rfl, rfl, -⟩ := rRegwDet Lpa cpu vw rs d l p' d' hst
    exact ⟨rfl, rfl⟩
  | AStepWrite p k0 d l0 lb p' d' _ hwr _ _ hst =>
    simp only at Heqp
    subst Heqp
    obtain ⟨rfl, -, -⟩ := rRegwDet Lpa cpu vw rs d l p' d' hst
    revert hwr
    cases erwOf .ORnone [] .x10 <;> simp [erwLabel, wlWr]
  | AStepFence p k0 d l0 lb p' d' _ hfe _ hst =>
    simp only at Heqp
    subst Heqp
    obtain ⟨rfl, -, -⟩ := rRegwDet Lpa cpu vw rs d l p' d' hst
    revert hfe
    cases erwOf .ORnone [] .x10 <;> simp [erwLabel, wlFence]

theorem wpdrW2b (hxy : x ≠ L) (HLram : devAddr Lpa = false) (HLeq : L = l3pLbase Lpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hcons : rvwmoCatConsistent GD)
    (vw : BitVec 8) :
    iprop(AxAnnot.annotOwn (i, 1) (AxLock3Reader.R1e (GF := GF) x GD nm i) ∗
        PpureTok (GF := GF) L x GD i vB) ⊢
      ∀ rs : RegFile,
        AxLock3Reader.twpdr GF hlc L x GD nm i vB
          ⟨.PHart cpu (rM2b Lpa vw) rs none ibNone, 2⟩ := by
  apply wpdrPosShell L x GD nm cpu i vB _ 2 (rM2b Lpa vw) (by rw [Hrow]; simp [l3pRRow])
  · intro lb Hlk
    rw [Hrow] at Hlk
    simp only [l3pRRow, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
      at Hlk
    subst Hlk
    rfl
  · intro rs l s' Hstep
    obtain ⟨rfl, rfl⟩ := rRegwInv GD Lpa cpu i vw rs
      ⟨.PHart cpu (rM2b Lpa vw) rs none ibNone, 2⟩ rfl l s' Hstep
    have hwd : wlWdata (erwLabel (erwOf .ORnone [] .x10)) = none := by
      cases erwOf .ORnone [] .x10 <;> rfl
    rw [hwd]
    iintro HP
    iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
    inext
    ihave H := (wpdrW2 (hlc := hlc) L x GD nm Lpa xpa cpu i t old tx vB hxy HLram HLeq Hrow
      Hcons) $$ HP
    iapply H

/-! ## 7. Positions 0/1: graph and step facts -/

theorem r0Lbl0 (HLeq : L = l3pLbase Lpa) (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) :
    gxLbl GD.gdG (i, 0) = some (.LRmw true false L [t] [old] [b1] .WCplain) := by
  rw [HLeq]
  exact l3pRLbl0 Lpa xpa GD i t old tx vB Hrow

theorem r0Wb (HLeq : L = l3pLbase Lpa) (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) :
    gwritesByte GD.gdG (i, 0) L b1 :=
  (gwritesByteOfRmw GD (i, 0) L [t] [old] b1 true false
    (r0Lbl0 L GD Lpa xpa i t old tx vB HLeq Hrow)).1

theorem r0Single (HLeq : L = l3pLbase Lpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) :
    ∀ a' v', gwritesByte GD.gdG (i, 0) a' v' → a' = L :=
  (gwritesByteOfRmw GD (i, 0) L [t] [old] b1 true false
    (r0Lbl0 L GD Lpa xpa i t old tx vB HLeq Hrow)).2

theorem r0Gd (HLeq : L = l3pLbase Lpa) (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) :
    graphData GD (i, 0) = some [b1] := by
  simp only [graphData, r0Lbl0 L GD Lpa xpa i t old tx vB HLeq Hrow, Option.bind_some, lblData]

theorem r1Lbl1 (Hxeq : x = l3pXbase xpa) (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) :
    gxLbl GD.gdG (i, 1) = some (.LLoad false x [tx] [vB]) := by
  rw [Hxeq]
  exact l3pRLbl1 Lpa xpa GD i t old tx vB Hrow

theorem r1RdConcrete (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) :
    greadsByte GD.gdG (i, 1) x tx vB :=
  ⟨_, x, [tx], [vB], 0, r1Lbl1 x GD Lpa xpa i t old tx vB Hxeq Hrow, rfl, rfl, rfl,
    by simp [accAddr]⟩

theorem r1RdEx (Hxeq : x = l3pXbase xpa) (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) :
    ∃ tv v, greadsByte GD.gdG (i, 1) x tv v :=
  ⟨tx, vB, r1RdConcrete x GD Lpa xpa i t old tx vB Hxeq Hrow⟩

theorem r1GacqPo (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) :
    gacqPo GD.gdG (i, 0) (i, 1) :=
  l3pRGacqPoXread Lpa xpa GD i t old tx vB Hrow

theorem r1GisW (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) :
    gisW GD.gdG (i, 1) = false := by
  simp only [gisW, l3pRLbl1 Lpa xpa GD i t old tx vB Hrow]
  rfl

/-- Position 1 is a LOAD: it writes no byte. -/
theorem r1NoWrite (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (a : Int)
    (v' : BitVec 8) : gwritesByte GD.gdG (i, 1) a v' → False := by
  intro Hwb
  have h := AxProt.gwritesByteGisW _ _ _ _ Hwb
  rw [r1GisW GD Lpa xpa i t old tx vB Hrow] at h
  cases h

/-- HART `i` NEVER WRITES `x` anywhere in its row (and has no event past it). -/
theorem r1NoXwriteHartI (hxy : x ≠ L) (HLeq : L = l3pLbase Lpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (k : Nat) (v' : BitVec 8) :
    gwritesByte GD.gdG (i, k) x v' → False := by
  intro Hwb
  have Hsome : (gxLbl GD.gdG (i, k)).isSome = true := by
    obtain ⟨l, _, _, _, Hl, _⟩ := Hwb
    simp [Hl]
  have Hlen : k < (AxOpsem.grow GD i).length := (progressIsValidGrowG GD.gdG i k).1 Hsome
  rw [Hrow] at Hlen
  simp only [l3pRRow, List.length_cons, List.length_nil] at Hlen
  by_cases hk : k < 3
  · exact rNoXwriteBeforeRel L x GD Lpa xpa i t old tx vB hxy HLeq Hrow (i, k) v' Hwb
      ⟨rfl, hk, Hsome, by rw [l3pRLbl3 Lpa xpa GD i t old tx vB Hrow]; rfl⟩
  · have hk3 : k = 3 := by omega
    subst hk3
    exact hxy (r3Single L GD Lpa xpa i t old tx vB HLeq Hrow x v' Hwb)

theorem r0OnlyReadsL (HLeq : L = l3pLbase Lpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (a : Int) (tv : Nat)
    (v : BitVec 8) : greadsByte GD.gdG (i, 0) a tv v → a = L := by
  intro ⟨l, base, ts, vs, jj, Hl0, Hrd, Hts, Hvs, Hacc⟩
  rw [l3pRLbl0 Lpa xpa GD i t old tx vB Hrow, Option.some.injEq] at Hl0
  subst Hl0
  simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at Hrd
  obtain ⟨rfl, rfl, rfl⟩ := Hrd
  cases jj with
  | zero =>
    simp only [accAddr] at Hacc
    rw [HLeq]
    omega
  | succ jj => simp at Hvs

theorem r1ReadDet (Hxram : devAddr xpa = false) (rs : RegFile) (d : Efab) (l : Wlabel)
    (p' : Pexv6) (d' : Efab) :
    pstepProg (.PHart cpu (rM2 Lpa xpa) rs none ibNone) d l p' d' →
    ∃ vw : BitVec 8, p' = .PHart cpu (rM2b Lpa vw) rs none ibNone ∧ d' = d := by
  intro h
  cases p' with
  | PDisk _ => exact False.elim h
  | PHart cpu' m' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hn, hd⟩ := h
    have hpa : devAddr (l3pRreq l3pAkP xpa).pa = false := Hxram
    have hfe : (classify (l3pRreq l3pAkP xpa).access_kind).akIfetch = false := rfl
    simp only [rM2, pstepNode, pnodeStep, hpa, Bool.false_eq_true, ↓reduceIte] at hn
    rcases hn with ⟨hif, _⟩ | ⟨_, ⟨_, w, tvs, _, _, _, hm, hors, hfn, hdd, hoib, _⟩ |
      ⟨_, w, tvs, _, _, _, hm, hors, hfn, hdd, hoib, _⟩⟩
    · rw [hfe] at hif
      cases hif
    all_goals
      subst hm hors hfn hoib
      exact ⟨_, rfl, by rw [hd, hdd]⟩

/-- `astepProg` never fires at `rM2` (position 1): a `memRead` node steps only by a read. -/
theorem r1AstepProgVacuous (Hxram : devAddr xpa = false) (rs : RegFile) (s : Athread)
    (Heqp : s.atP = .PHart cpu (rM2 Lpa xpa) rs none ibNone) (_Heqk : s.atK = 1) (l : Wlabel)
    (s' : Athread) :
    AxOpsem.astepProg (AxOpsem.grow GD i) s l s' → False := by
  intro h
  obtain ⟨d, d', hst⟩ := astepProgPstep _ _ _ _ h
  rw [Heqp] at hst
  obtain ⟨hrd, -⟩ := pstepProgMemreadLbl cpu 1 64 (l3pRreq l3pAkP xpa) _ rs ibNone d l s'.atP
    d' Hxram rfl hst
  rcases l3pAstepProgShape _ s l s' h with hadm | hwr | hfn
  · exact l3pRdExclAdmin l hrd hadm
  · exact l3pRdExclWr l hrd hwr
  · exact l3pRdExclFence l hrd hfn

theorem r0ReadDet (HLram : devAddr Lpa = false) (rs : RegFile) (d : Efab) (l : Wlabel)
    (p' : Pexv6) (d' : Efab) :
    pstepProg (.PHart cpu (AxLock3Reader.rM0 Lpa xpa) rs none ibNone) d l p' d' →
    p' = .PHart cpu (rM1 Lpa xpa) rs none ibNone ∧ d' = d := by
  intro h
  cases p' with
  | PDisk _ => exact False.elim h
  | PHart cpu' m' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hn, hd⟩ := h
    have hpa : devAddr (l3pRreq l3pAkXaq Lpa).pa = false := HLram
    have hfe : (classify (l3pRreq l3pAkXaq Lpa).access_kind).akIfetch = false := rfl
    simp only [AxLock3Reader.rM0, pstepNode, pnodeStep, hpa, Bool.false_eq_true, ↓reduceIte]
      at hn
    rcases hn with ⟨hif, _⟩ | ⟨_, ⟨_, w, tvs, _, _, _, hm, hors, hfn, hdd, hoib, _⟩ |
      ⟨_, w, tvs, _, _, _, hm, hors, hfn, hdd, hoib, _⟩⟩
    · rw [hfe] at hif
      cases hif
    all_goals
      subst hm hors hfn hoib
      exact ⟨rfl, by rw [hd, hdd]⟩

theorem astepProgWrite0RelInv (HLram : devAddr Lpa = false) (rs : RegFile) (s : Athread)
    (Heqp : s.atP = .PHart cpu (rM1 Lpa xpa) rs none ibNone) (Heqk : s.atK = 0)
    (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg (AxOpsem.grow GD i) s l s' →
    (wlWdata l = some (WeakInterpProj.wbytes 1 b1) ∧
      s' = ⟨.PHart cpu (rM2 Lpa xpa) rs none ibNone, 1⟩) ∨
    (l = LSilent ∧ s' = ⟨.PHart cpu (rM1 Lpa xpa) rs none ibNone, 0⟩) := by
  intro h
  cases h with
  | AStepAdmin p k0 d l p' d' hadm hst =>
    simp only at Heqp Heqk
    subst Heqp Heqk
    rcases l3pWriteExclDet cpu Lpa HLram b1 (fun _ => rM2 Lpa xpa) rs ibNone d l p' d' hst with
      ⟨rfl, -, -⟩ | ⟨rfl, rfl, -⟩
    · simp [lbAdmin] at hadm
    · exact .inr ⟨rfl, rfl⟩
  | AStepWrite p k0 d l lb p' d' _ hwr _ _ hst =>
    simp only at Heqp Heqk
    subst Heqp Heqk
    rcases l3pWriteExclDet cpu Lpa HLram b1 (fun _ => rM2 Lpa xpa) rs ibNone d l p' d' hst with
      ⟨rfl, rfl, -⟩ | ⟨rfl, -, -⟩
    · exact .inl ⟨rfl, rfl⟩
    · simp [wlWr] at hwr
  | AStepFence p k0 d l lb p' d' _ hfe _ hst =>
    simp only at Heqp Heqk
    subst Heqp Heqk
    rcases l3pWriteExclDet cpu Lpa HLram b1 (fun _ => rM2 Lpa xpa) rs ibNone d l p' d' hst with
      ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ <;> simp [wlFence] at hfe

theorem astepProgRead0RelVacuous (HLram : devAddr Lpa = false) (rs : RegFile) (s : Athread)
    (Heqp : s.atP = .PHart cpu (AxLock3Reader.rM0 Lpa xpa) rs none ibNone) (_Heqk : s.atK = 0)
    (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg (AxOpsem.grow GD i) s l s' → False := by
  intro h
  obtain ⟨d, d', hst⟩ := astepProgPstep _ _ _ _ h
  rw [Heqp] at hst
  obtain ⟨hrd, -⟩ := pstepProgMemreadLbl cpu 1 64 (l3pRreq l3pAkXaq Lpa)
    (fun _ => rM1 Lpa xpa) rs ibNone d l s'.atP d' HLram rfl hst
  rcases l3pAstepProgShape _ s l s' h with hadm | hwr | hfn
  · exact l3pRdExclAdmin l hrd hadm
  · exact l3pRdExclWr l hrd hwr
  · exact l3pRdExclFence l hrd hfn

/-! ## 8. The release-sourced acquire (Rocq section `RRel`) -/

section RRel

theorem j0Lbl1 (Hxeq : x = l3pXbase xpa) (j0 : Agent) (t0 : Nat) (old0 v0 : BitVec 8)
    (Hrow_j0 : AxOpsem.grow GD j0 = l3pWRow Lpa xpa t0 old0 v0) :
    gxLbl GD.gdG (j0, 1) = some (.LStore false x [v0] .WCplain) := by
  rw [Hxeq]
  exact l3pWLbl1 Lpa xpa GD j0 t0 old0 v0 Hrow_j0

theorem j0Lbl2 (j0 : Agent) (t0 : Nat) (old0 v0 : BitVec 8)
    (Hrow_j0 : AxOpsem.grow GD j0 = l3pWRow Lpa xpa t0 old0 v0) :
    gxLbl GD.gdG (j0, 2) = some (.LFence true true false true) :=
  l3pWLbl2 Lpa xpa GD j0 t0 old0 v0 Hrow_j0

theorem j0Lbl3 (HLeq : L = l3pLbase Lpa) (j0 : Agent) (t0 : Nat) (old0 v0 : BitVec 8)
    (Hrow_j0 : AxOpsem.grow GD j0 = l3pWRow Lpa xpa t0 old0 v0) :
    gxLbl GD.gdG (j0, 3) = some (.LStore false L [b0] .WCplain) := by
  rw [HLeq]
  exact l3pWLbl3 Lpa xpa GD j0 t0 old0 v0 Hrow_j0

theorem j0Wb1 (Hxeq : x = l3pXbase xpa) (j0 : Agent) (t0 : Nat) (old0 v0 : BitVec 8)
    (Hrow_j0 : AxOpsem.grow GD j0 = l3pWRow Lpa xpa t0 old0 v0) :
    gwritesByte GD.gdG (j0, 1) x v0 :=
  (gwritesByteOfStore GD (j0, 1) x v0 .WCplain (j0Lbl1 x GD Lpa xpa Hxeq j0 t0 old0 v0 Hrow_j0)).1

theorem j0Gpo13 (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa) (j0 : Agent) (t0 : Nat)
    (old0 v0 : BitVec 8) (Hrow_j0 : AxOpsem.grow GD j0 = l3pWRow Lpa xpa t0 old0 v0) :
    WeakRvwmoGraph.gpo GD.gdG (j0, 1) (j0, 3) :=
  ⟨rfl, by simp, by rw [j0Lbl1 x GD Lpa xpa Hxeq j0 t0 old0 v0 Hrow_j0]; rfl,
    by rw [j0Lbl3 L GD Lpa xpa HLeq j0 t0 old0 v0 Hrow_j0]; rfl⟩

/-- The only event gpo-between `(j0,1)` and `(j0,3)` is the fence: no `x`-write. -/
theorem j0NoXwriteBetween (j0 : Agent) (t0 : Nat) (old0 v0 : BitVec 8)
    (Hrow_j0 : AxOpsem.grow GD j0 = l3pWRow Lpa xpa t0 old0 v0) (w'' : Geid) (v'' : BitVec 8) :
    gwritesByte GD.gdG w'' x v'' → WeakRvwmoGraph.gpo GD.gdG (j0, 1) w'' →
    WeakRvwmoGraph.gpo GD.gdG w'' (j0, 3) → False := by
  intro ⟨l, base, vs, jj, Hl0, Hwr, Hvs, Hacc⟩ ⟨Heq1, Hlt1, _, _⟩ ⟨Heq2, Hlt2, _, _⟩
  obtain ⟨j, k⟩ := w''
  simp only at Heq1 Heq2 Hlt1 Hlt2
  subst Heq2
  have hk : k = 2 := by omega
  subst hk
  rw [j0Lbl2 GD Lpa xpa j t0 old0 v0 Hrow_j0, Option.some.injEq] at Hl0
  subst Hl0
  simp [lbWr] at Hwr

/-- `w_rel`'s po-latest `x`-write is EXACTLY `((j0,1), v0)`. -/
theorem wrelPoLatestPin (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa) (w_rel : Geid)
    (j0 : Agent) (t0 : Nat) (old0 v0 : BitVec 8) (Heq_wrel : w_rel = (j0, 3))
    (Hrow_j0 : AxOpsem.grow GD j0 = l3pWRow Lpa xpa t0 old0 v0) (Hh : List Hent)
    (Hpl : lockHhPoLatest x GD Hh w_rel) : Hh.getLast? = some ((j0, 1), v0) := by
  rw [Heq_wrel] at Hpl
  rcases Hpl (j0, 1) v0 (j0Wb1 x GD Lpa xpa Hxeq j0 t0 old0 v0 Hrow_j0)
      (j0Gpo13 L x GD Lpa xpa HLeq Hxeq j0 t0 old0 v0 Hrow_j0) with
    Hlast | ⟨w'', v'', Hwb'', Hg1, Hg2⟩
  · exact Hlast
  · exact (j0NoXwriteBetween x GD Lpa xpa j0 t0 old0 v0 Hrow_j0 w'' v'' Hwb'' Hg1 Hg2).elim

/-- The release-sourced acquire's deposit: the re-tied token, with well-formedness and the
po-latest clause relative to `w_rel`. -/
def R0er (w_rel : Geid) : IProp GF :=
  iprop(∃ Hh : List Hent, tokTie GD nm.1 x Hh {[(i, 0) := (1 : Qp)]} ∗
    ⌜histXWf x GD Hh ∧ lockHhPoLatest x GD Hh w_rel⌝)

/-- 8.1 THE OWNED READ, release-sourced: the value read is pinned to `v0` (via
`lockReadOwn`), and the acquire's token is re-tied to the read (`tokRetieOb`). -/
theorem r1FlowEq (hxy : x ≠ L) (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hcons : rvwmoCatConsistent GD)
    (w_rel : Geid) (Hrfe_rel : lockExtRmwReader L GD w_rel (i, 0)) (j0 : Agent) (t0 : Nat)
    (old0 v0 : BitVec 8) (Heq_wrel : w_rel = (j0, 3))
    (Hrow_j0 : AxOpsem.grow GD j0 = l3pWRow Lpa xpa t0 old0 v0) (Hh : List Hent)
    (Hxwf : histXWf x GD Hh) (Hpl : lockHhPoLatest x GD Hh w_rel) :
    ⊢ @flowEqDyn hlc GF _ (axGA2Lock3 L x GD nm) GD (i, 1) (lockPolS GD (i, 1))
        {[(i, 0) := tokTie GD nm.1 x Hh {[(i, 0) := (1 : Qp)]}]}
        iprop(AxLock3Reader.R1e (GF := GF) x GD nm i ∗
          ⌜∀ tv v, greadsByte GD.gdG (i, 1) x tv v → v = v0⌝) := by
  have Hwf : gwf GD.gdG := Hcons.1
  have Hlast : Hh.getLast? = some ((j0, 1), v0) :=
    wrelPoLatestPin L x GD Lpa xpa HLeq Hxeq w_rel j0 t0 old0 v0 Heq_wrel Hrow_j0 Hh Hpl
  have Hown : ∀ w v, gwritesByte GD.gdG w x v → WeakRvwmoGraph.gpo GD.gdG w (i, 1) →
      w ∈ Hh.map Prod.fst := by
    intro w v Hwb ⟨Heq1, Hlt1, _, _⟩
    exfalso
    obtain ⟨j, k⟩ := w
    simp only at Heq1 Hlt1
    subst Heq1
    have hk : k = 0 := by omega
    subst hk
    exact r1NoXwriteHartI L x GD Lpa xpa j t old tx vB hxy HLeq Hrow 0 v Hwb
  have Hgacq := r1GacqPo GD Lpa xpa i t old tx vB Hrow
  -- the read's external rf-source, from the acquire's own tie base
  have Hsrc : tieBase GD.gdG (Hh.map Prod.fst) (i, 0) →
      ∃ w0, grfAt GD.gdG x w0 (i, 1) ∧ w0.1 ≠ (i, 1).1 := by
    intro Htb0
    have Hmo01 : gmoLt GD.gdG (i, 0) (i, 1) :=
      Hcons.2.1 _ _ (.inl (.inr (.inr (.inr (.inr (.inl Hgacq))))))
    have Htb1 := tieLob GD.gdG _ _ _ Htb0 Hmo01
    have Hfst := hentLastFst Hh (j0, 1) v0 Hlast
    have Hmo_j0_1 : gmoLt GD.gdG (j0, 1) (i, 1) := by
      rcases Htb1 with Heq | ⟨wl, Hlast', Hmo⟩
      · exfalso
        rw [Hfst, Option.some.injEq] at Heq
        obtain ⟨-, Hhart, -⟩ := Hrfe_rel
        rw [Heq_wrel] at Hhart
        exact Hhart (Prod.mk.inj Heq).1
      · rw [Hfst, Option.some.injEq] at Hlast'
        subst Hlast'
        exact Hmo
    obtain ⟨tv0, v0', Hrd0⟩ := r1RdEx x GD Lpa xpa i t old tx vB Hxeq Hrow
    have Hj0wb := j0Wb1 x GD Lpa xpa Hxeq j0 t0 old0 v0 Hrow_j0
    obtain ⟨Hmain, Hmaxim⟩ := Hcons.2.2.1 (i, 1) x tv0 v0' Hrd0
    have Htv0 := Hmaxim (j0, 1) v0 Hj0wb (.inl Hmo_j0_1)
    have Hpos := WeakRvwmoGraph.gwixPos GD.gdG (j0, 1)
      (gwritesByteGwrites GD.gdG (j0, 1) x v0 Hwf Hj0wb)
    cases tv0 with
    | zero => omega
    | succ tv0' =>
      obtain ⟨w0, Hat0, Hwb0, -⟩ := Hmain
      refine ⟨w0, ⟨tv0' + 1, v0', Hrd0, Hat0⟩, ?_⟩
      obtain ⟨j, k⟩ := w0
      intro Heq
      simp only at Heq
      subst Heq
      exact r1NoXwriteHartI L x GD Lpa xpa j t old tx vB hxy HLeq Hrow k v0' Hwb0
  unfold flowEqDyn
  iintro %σ %sOb %Hsub %Hnin Hob Hflow
  ihave Htie := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ Hflow
  have htb : tokTie (GF := GF) GD nm.1 x Hh {[(i, 0) := (1 : Qp)]} ⊢
      ⌜tieBase GD.gdG (Hh.map Prod.fst) (i, 0)⌝ := by
    unfold tokTie
    iintro ⟨-, %h⟩
    ipureintro
    exact h _ (by rw [domSingleton]; exact elemOfSingleton.2 rfl)
  icases persistent_entails_left htb $$ Htie with ⟨Htie, %Htb0⟩
  obtain ⟨w0, Hrf0, Hext0⟩ := Hsrc Htb0
  have hgrf0 : WeakRvwmoAcyc.grf GD.gdG w0 (i, 1) := grfAtGrf _ _ _ _ Hrf0
  have hgrfe0 : grfe GD.gdG w0 (i, 1) := ⟨hgrf0, Hext0⟩
  have hw0gmo : w0 ∈ GD.gdG.gxGmo := grfSrcGxGmo GD.gdG w0 (i, 1) hgrf0
  have hcov : ∀ w v, gwritesByte GD.gdG w x v → gmoLt GD.gdG w (i, 1) →
      w ∈ lockPolS GD (i, 1) := by
    intro w v hwb hmo
    rcases xWritesGmoBeforeRead GD x (i, 1) w w0 v Hcons Hrf0 hwb hmo with h | hco
    · rw [h]
      exact lockPolSIntro GD w0 (i, 1) hw0gmo hgrfe0
    · exact lockPolSIntro2 GD w w0 (i, 1) (gwritesByteGxGmo GD.gdG Hwf w x v hwb) hco hgrfe0
  obtain ⟨g, D, hm⟩ := σ
  icases ((lock3ObStInterpAr L x GD nm g D hm sOb).trans
    (protInvLock3Unfold L x nm.1 nm.2 GD sOb D hm g)).1 $$ Hob with ⟨Hlock'', Hgen⟩
  icases (AxProtLock2.protInvLockUnfold'' L x nm.1 nm.2 GD sOb D hm).1 $$ Hlock''
    with ⟨Hlock', HHL, %Hclaims, %Hhmc⟩
  icases (protInvLockUnfold' L x nm.1 nm.2 GD sOb D hm).1 $$ Hlock' with ⟨Hc, Hpo, Hlocks⟩
  have hres : protInv (GF := GF) nm.1 GD sOb ∗ tokTie GD nm.1 x Hh {[(i, 0) := (1 : Qp)]} ⊢
      ⌜grfAt GD.gdG x (j0, 1) (i, 1) ∧ ∀ t v, greadsByte GD.gdG (i, 1) x t v → v = v0⌝ := by
    iintro ⟨Hpo, Htie⟩
    ihave Hsn := protInvPrefixCovMemByte nm.1 GD sOb (i, 1) x
      (fun w v hwb hmo => Hsub _ (hcov w v hwb hmo)) $$ Hpo
    iapply lockReadOwn GD nm.1 x Hh (j0, 1) (i, 0) (i, 1) v0 Hcons Hxwf.1 Hxwf.2 Hown Hlast
      Hgacq (r1RdEx x GD Lpa xpa i t old tx vB Hxeq Hrow)
    isplitl [Htie]
    · iexact Htie
    · iexact Hsn
  icases persistent_entails_left hres $$ [$Hpo $Htie] with ⟨⟨Hpo, Htie⟩, %Hval⟩
  ihave Htie' := tokRetieOb GD nm.1 x Hh (i, 0) (i, 1) Hcons (gacqPoGobCat GD _ _ Hgacq) $$ Htie
  ihave Hpo' := protInvReadStep nm.1 GD sOb (i, 1) Hnin
    (r1GisW GD Lpa xpa i t old tx vB Hrow) $$ Hpo
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists ((g, D, hm) : Bool × GSet Geid × GMapF Geid (List Hent))
  isplitl [Hc Hpo' Hlocks HHL Hgen]
  · iapply ((lock3ObStInterpAr L x GD nm g D hm (({(i, 1)} : GSet Geid) ∪ sOb)).trans
      (protInvLock3Unfold L x nm.1 nm.2 GD (({(i, 1)} : GSet Geid) ∪ sOb) D hm g)).2
    isplitl [Hc Hpo' Hlocks HHL]
    · iapply (AxProtLock2.protInvLockUnfold'' L x nm.1 nm.2 GD (({(i, 1)} : GSet Geid) ∪ sOb)
        D hm).2
      isplitl [Hc Hpo' Hlocks]
      · iapply (protInvLockUnfold' L x nm.1 nm.2 GD (({(i, 1)} : GSet Geid) ∪ sOb) D hm).2
        isplitl [Hc]
        · iexact Hc
        isplitl [Hpo']
        · iexact Hpo'
        iapply (AxProtLock.bigSepSUnionSingleton
          (Φ := fun e => ΦLock' L x nm.1 nm.2 GD e ((get? hm e).getD [])) Hnin).2
        isplitl []
        · iapply AxProtLock.ΦLock'Vacuous L x nm.1 nm.2 GD (i, 1) _
            (r1NoWrite GD Lpa xpa i t old tx vB Hrow L b0)
        · iexact Hlocks
      · isplitl [HHL]
        · iexact HHL
        · isplitl []
          · ipureintro
            intro r hr
            obtain ⟨e, he, hre⟩ := Hclaims r hr
            exact ⟨e, elemOfUnionR he, hre⟩
          · ipureintro
            intro w hw hwb0'
            rcases elemOfUnion.1 hw with hw | hw
            · rw [elemOfSingleton.1 hw] at hwb0'
              exact (r1NoWrite GD Lpa xpa i t old tx vB Hrow L b0 hwb0').elim
            · exact Hhmc w hw hwb0'
    · iapply lockGenesisMono L x nm.1 GD g sOb (({(i, 1)} : GSet Geid) ∪ sOb)
        (fun _ h => elemOfUnionR h)
      iexact Hgen
  · isplitl [Htie']
    · unfold AxLock3Reader.R1e
      iexists Hh
      isplitl [Htie']
      · iexact Htie'
      · ipureintro
        exact Hxwf
    · ipureintro
      exact Hval.2

/-! ### 8.2 Bridging the concrete value fact to `PreaderPure` -/

theorem grfeToL (HLeq : L = l3pLbase Lpa) (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB)
    (w : Geid) : grfe GD.gdG w (i, 0) → grfAt GD.gdG L w (i, 0) := by
  intro ⟨⟨a, tv, v, Hrd, Hat⟩, _⟩
  have Ha := r0OnlyReadsL L GD Lpa xpa i t old tx vB HLeq Hrow a tv v Hrd
  rw [Ha] at Hrd
  exact ⟨tv, v, Hrd, Hat⟩

theorem wrelGrfe (w_rel : Geid) (Hrfe_rel : lockExtRmwReader L GD w_rel (i, 0)) :
    grfe GD.gdG w_rel (i, 0) := by
  obtain ⟨⟨tv, v, Hrd, Hat⟩, Hhart, _⟩ := Hrfe_rel
  exact ⟨⟨L, tv, v, Hrd, Hat⟩, Hhart⟩

theorem PreaderPureHolds (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (w_rel : Geid)
    (Hrfe_rel : lockExtRmwReader L GD w_rel (i, 0)) (j0 : Agent) (t0 : Nat) (old0 v0 : BitVec 8)
    (Heq_wrel : w_rel = (j0, 3)) (Hrow_j0 : AxOpsem.grow GD j0 = l3pWRow Lpa xpa t0 old0 v0)
    (Hval : ∀ tv v, greadsByte GD.gdG (i, 1) x tv v → v = v0) :
    PreaderPure L x GD i vB := by
  have HvBeq := Hval tx vB (r1RdConcrete x GD Lpa xpa i t old tx vB Hxeq Hrow)
  refine ⟨?_, ?_⟩
  · intro j v Hgrfe Hwb
    have Hgrf_j3 := grfeToL L GD Lpa xpa i t old tx vB HLeq Hrow (j, 3) Hgrfe
    have Hgrf_wrel := grfeToL L GD Lpa xpa i t old tx vB HLeq Hrow w_rel
      (wrelGrfe L GD i w_rel Hrfe_rel)
    rw [Heq_wrel] at Hgrf_wrel
    have Heqj := grfAtDet GD.gdG L (j, 3) (j0, 3) (i, 0) Hgrf_j3 Hgrf_wrel
    simp only [Prod.mk.injEq, and_true] at Heqj
    subst Heqj
    rw [HvBeq]
    exact (gwritesByteDet GD.gdG (j, 1) x v v0 Hwb
      (j0Wb1 x GD Lpa xpa Hxeq j t0 old0 v0 Hrow_j0)).symm
  · intro Hread_img bx _
    exfalso
    obtain ⟨⟨tv', v', Hrd', Hat'⟩, _, _⟩ := Hrfe_rel
    obtain ⟨Ht, -⟩ := greadsByteDet GD.gdG (i, 0) L 0 b0 tv' v' Hread_img Hrd'
    subst Ht
    simp [gwriteAt] at Hat'

/-! ### 8.3 The existential lift and the `graphValue` obligation -/

theorem r1FlowEqBundled (hxy : x ≠ L) (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hcons : rvwmoCatConsistent GD)
    (w_rel : Geid) (Hrfe_rel : lockExtRmwReader L GD w_rel (i, 0)) (j0 : Agent) (t0 : Nat)
    (old0 v0 : BitVec 8) (Heq_wrel : w_rel = (j0, 3))
    (Hrow_j0 : AxOpsem.grow GD j0 = l3pWRow Lpa xpa t0 old0 v0) (Hh : List Hent) :
    ⊢ @flowEqDyn hlc GF _ (axGA2Lock3 L x GD nm) GD (i, 1) (lockPolS GD (i, 1))
        {[(i, 0) := iprop(tokTie GD nm.1 x Hh {[(i, 0) := (1 : Qp)]} ∗
          ⌜histXWf x GD Hh ∧ lockHhPoLatest x GD Hh w_rel⌝)]}
        iprop(AxLock3Reader.R1e (GF := GF) x GD nm i ∗
          ⌜∀ tv v, greadsByte GD.gdG (i, 1) x tv v → v = v0⌝) := by
  unfold flowEqDyn
  iintro %σ %sOb %Hsub %Hnin Hob Hflow
  ihave Hflow := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ Hflow
  icases Hflow with ⟨Htie, %Hpure⟩
  obtain ⟨Hxwf, Hpl⟩ := Hpure
  have Hbb := r1FlowEq (GF := GF) (hlc := hlc) L x GD nm Lpa xpa i t old tx vB hxy HLeq Hxeq Hrow Hcons
    w_rel Hrfe_rel j0 t0 old0 v0 Heq_wrel Hrow_j0 Hh Hxwf Hpl
  unfold flowEqDyn at Hbb
  ihave Hbb := Hbb
  ihave H := Hbb $$ %σ %sOb %Hsub %Hnin Hob
  iapply H
  iapply (BigSepM.bigSepM_singleton (M := GMapF Geid)).2
  iexact Htie

theorem r1FlowEqE (hxy : x ≠ L) (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hcons : rvwmoCatConsistent GD)
    (w_rel : Geid) (Hrfe_rel : lockExtRmwReader L GD w_rel (i, 0)) (j0 : Agent) (t0 : Nat)
    (old0 v0 : BitVec 8) (Heq_wrel : w_rel = (j0, 3))
    (Hrow_j0 : AxOpsem.grow GD j0 = l3pWRow Lpa xpa t0 old0 v0) :
    ⊢ @flowEqDyn hlc GF _ (axGA2Lock3 L x GD nm) GD (i, 1) (lockPolS GD (i, 1))
        {[(i, 0) := R0er (GF := GF) x GD nm i w_rel]}
        iprop(AxLock3Reader.R1e (GF := GF) x GD nm i ∗
          ⌜∀ tv v, greadsByte GD.gdG (i, 1) x tv v → v = v0⌝) := by
  iapply (@flowEqDynMono hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol GD (i, 1) (lockPolS GD (i, 1))
    _ iprop(∃ _Hh : List Hent, AxLock3Reader.R1e (GF := GF) x GD nm i ∗
      ⌜∀ tv v, greadsByte GD.gdG (i, 1) x tv v → v = v0⌝)
    iprop(AxLock3Reader.R1e (GF := GF) x GD nm i ∗
      ⌜∀ tv v, greadsByte GD.gdG (i, 1) x tv v → v = v0⌝))
  · inext
    iintro ⟨%_, H⟩
    iexact H
  · unfold R0er
    iapply (fedsR (hlc := hlc) L x GD nm (i, 0)
      (fun Hh => iprop(tokTie (GF := GF) GD nm.1 x Hh {[(i, 0) := (1 : Qp)]} ∗
        ⌜histXWf x GD Hh ∧ lockHhPoLatest x GD Hh w_rel⌝))
      (fun _ => iprop(AxLock3Reader.R1e (GF := GF) x GD nm i ∗
        ⌜∀ tv v, greadsByte GD.gdG (i, 1) x tv v → v = v0⌝)) (i, 1) (lockPolS GD (i, 1))
      (fun Hh => r1FlowEqBundled L x GD nm Lpa xpa i t old tx vB hxy HLeq Hxeq Hrow Hcons w_rel
        Hrfe_rel j0 t0 old0 v0 Heq_wrel Hrow_j0 Hh))

theorem r1FlowEqWp (hxy : x ≠ L) (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hcons : rvwmoCatConsistent GD)
    (w_rel : Geid) (Hrfe_rel : lockExtRmwReader L GD w_rel (i, 0)) (j0 : Agent) (t0 : Nat)
    (old0 v0 : BitVec 8) (Heq_wrel : w_rel = (j0, 3))
    (Hrow_j0 : AxOpsem.grow GD j0 = l3pWRow Lpa xpa t0 old0 v0) (v : List (BitVec 8))
    (Hgv : graphValue GD (i, 1) = some v) :
    ⊢ @flowEqDyn hlc GF _ (axGA2Lock3 L x GD nm) GD (i, 1) (lockPolS GD (i, 1))
        {[(i, 0) := R0er (GF := GF) x GD nm i w_rel]}
        iprop((AxLock3Reader.R1e (GF := GF) x GD nm i ∗ ⌜PreaderPure L x GD i vB⌝) ∗
          ⌜graphValue GD (i, 1) = some v⌝) := by
  iapply (@flowEqDynMono hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol GD (i, 1) (lockPolS GD (i, 1))
    _ iprop(AxLock3Reader.R1e (GF := GF) x GD nm i ∗
      ⌜∀ tv v', greadsByte GD.gdG (i, 1) x tv v' → v' = v0⌝)
    iprop((AxLock3Reader.R1e (GF := GF) x GD nm i ∗ ⌜PreaderPure L x GD i vB⌝) ∗
      ⌜graphValue GD (i, 1) = some v⌝))
  · inext
    iintro ⟨HR1e, %Hval⟩
    isplitl [HR1e]
    · isplitl [HR1e]
      · iexact HR1e
      · ipureintro
        exact PreaderPureHolds L x GD Lpa xpa i t old tx vB HLeq Hxeq Hrow w_rel Hrfe_rel j0 t0
          old0 v0 Heq_wrel Hrow_j0 Hval
    · ipureintro
      exact Hgv
  · iapply (r1FlowEqE (hlc := hlc) L x GD nm Lpa xpa i t old tx vB hxy HLeq Hxeq Hrow Hcons w_rel
      Hrfe_rel j0 t0 old0 v0 Heq_wrel Hrow_j0)

/-! ### 8.4 Position 1 assembled: the read's clause (a) is a real `wpEvStep` -/

theorem wpdrW1 (hxy : x ≠ L) (HLram : devAddr Lpa = false) (Hxram : devAddr xpa = false)
    (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hcons : rvwmoCatConsistent GD)
    (w_rel : Geid) (Hrfe_rel : lockExtRmwReader L GD w_rel (i, 0)) (j0 : Agent) (t0 : Nat)
    (old0 v0 : BitVec 8) (Heq_wrel : w_rel = (j0, 3))
    (Hrow_j0 : AxOpsem.grow GD j0 = l3pWRow Lpa xpa t0 old0 v0) :
    AxAnnot.annotOwn (i, 0) (R0er (GF := GF) x GD nm i w_rel) ⊢
      ∀ rs : RegFile,
        AxLock3Reader.twpdr GF hlc L x GD nm i vB ⟨.PHart cpu (rM2 Lpa xpa) rs none ibNone, 1⟩ := by
  have H : ⊢ ∀ rs : RegFile, AxAnnot.annotOwn (i, 0) (R0er (GF := GF) x GD nm i w_rel) -∗
      AxLock3Reader.twpdr GF hlc L x GD nm i vB ⟨.PHart cpu (rM2 Lpa xpa) rs none ibNone, 1⟩ := by
    iloeb as IH
    iintro %rs HP
    unfold AxLock3Reader.twpdr tierAWpd
    iapply (@AxWpD.wpdMUnfoldStep hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol rvwmoCatConsistent
      .MaybeStuck i _ _).2
    isplit
    · iapply (@progressOblMaybestuck GF (axGA2Lock3 L x GD nm) lockAxpol i _).2
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, -⟩
    ihave %Hg := AxLock3Writer.gconstPure L x GD nm GD' $$ Hg
    subst GD'
    isplit
    · iintro %id %K %Hst
      obtain ⟨lb, Hlb, Hid, -, HK⟩ := Hst
      simp only at Hlb
      rw [Hrow] at Hlb
      simp only [l3pRRow, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
        at Hlb
      subst Hlb Hid
      simp only [aident, aidentAdvRd, ↓reduceIte]
      iintro %v %Hgv %Hlen
      obtain ⟨l0, d0, d0', -, -, Hpst, Hatk⟩ := HK v Hlen
      obtain ⟨vw, Hp, -⟩ := r1ReadDet Lpa xpa cpu Hxram rs d0 l0 _ d0' Hpst
      have Hk2 : (K v).atK = 2 := by rw [Hatk]; rfl
      have HKv : K v = ⟨.PHart cpu (rM2b Lpa vw) rs none ibNone, 2⟩ := by
        rcases hk : K v with ⟨p'', k''⟩
        rw [hk] at Hp Hk2
        simp only at Hp Hk2
        rw [Hp, Hk2]
      rw [HKv]
      unfold wpEvStep naAtProgress
      iintro %na ⟨%Hprog, Hannot⟩
      have Hin0 : (i, 0) ∈ (FiniteMap.dom_set na : GSet Geid) := by
        have h : (i, 0) ∈ eidsBefore GD i 1 :=
          (elemOfEidsBefore GD i 1 _).2 ⟨rfl, by simp, by
            simp only [gmemB, l3pRLbl0 Lpa xpa GD i t old tx vB Hrow]; rfl⟩
        rw [← Hprog] at h
        exact (elemOfFilter.1 h).2
      obtain ⟨P0', HP0'⟩ := Option.isSome_iff_exists.1 (elemOfDom.1 Hin0)
      have Hdet : ⊢ AxAnnot.annotInterp na -∗
          AxAnnot.annotOwn (i, 0) (R0er (GF := GF) x GD nm i w_rel) ==∗
          ∃ R, AxAnnot.annotInterp (insert na (i, 0) R) ∗
            iprop(▷ □ (P0' -∗ R0er (GF := GF) x GD nm i w_rel ∗ R)) := by
        have h := annotDetach na (i, 0) (R0er (GF := GF) x GD nm i w_rel)
        rw [HP0'] at h
        exact h
      imod Hdet $$ Hannot HP with ⟨%R, Hannot', Hwand⟩
      ihave Hfeq := r1FlowEqWp (hlc := hlc) L x GD nm Lpa xpa i t old tx vB hxy HLeq Hxeq Hrow
        Hcons w_rel Hrfe_rel j0 t0 old0 v0 Heq_wrel Hrow_j0 v Hgv
      have Hnin : (i, 1) ∉ (FiniteMap.dom_set (insert na (i, 0) R) : GSet Geid) := by
        rw [domInsert, elemOfUnion, elemOfSingleton]
        rintro (Heq | Hik)
        · simp at Heq
        · have Hf : (i, 1) ∈ FiniteSet.filter (fun e : Geid => decide (e.1 = i))
              (FiniteMap.dom_set na : GSet Geid) := elemOfFilter.2 ⟨by simp, Hik⟩
          rw [Hprog, elemOfEidsBefore] at Hf
          exact Nat.lt_irrefl _ Hf.2.1
      imod (annotAlloc (insert na (i, 0) R) (i, 1)
        iprop(AxLock3Reader.R1e (GF := GF) x GD nm i ∗ ⌜PreaderPure L x GD i vB⌝) Hnin)
        $$ Hannot' with ⟨Hannot'', Hpt1⟩
      imod (annotSplit (i, 1) (AxLock3Reader.R1e (GF := GF) x GD nm i)
        iprop(⌜PreaderPure L x GD i vB⌝)) $$ Hpt1 %_ Hannot'' with ⟨⟨Hpt1a, Hpt1b⟩, Hannot2⟩
      imodintro
      inext
      imodintro
      iexists (), iprop(AxLock3Reader.R1e (GF := GF) x GD nm i ∗ ⌜PreaderPure L x GD i vB⌝),
        {[(i, 0) := R0er (GF := GF) x GD nm i w_rel]}, {[(i, 0) := R]}, ()
      isplitr
      · ipureintro
        trivial
      isplitl [Hwand]
      · unfold naSplittingWf
        isplitr
        · ipureintro
          rw [domSingleton]
          exact singletonSubseteqL.2 (l3pRAcqInLobpXread Lpa xpa GD i t old tx vB Hrow Hcons.1)
        · iapply (BigSepM2.bigSepM2_singleton _ (i, 0)
            (R0er (GF := GF) x GD nm i w_rel) R).2
          simp only [HP0', AxWp.fromOption]
          inext
          iexact Hwand
      isplitl [Hfeq]
      · iexact Hfeq
      isplitl [Hannot2]
      · rw [← AxLock3Writer.annotEq]
        iexact Hannot2
      isplitr
      · iapply AxLock3Writer.localTriv
      · have Hw2 := wpdrW2b (GF := GF) (hlc := hlc) L x GD nm Lpa xpa cpu i t old tx vB hxy HLram
          HLeq Hrow Hcons vw
        unfold AxLock3Reader.twpdr tierAWpd at Hw2
        ihave H := Hw2 $$ [$Hpt1a $Hpt1b]
        iapply H $$ %rs
    isplit
    · iintro %l %s' %Hst %-
      exact (r1AstepProgVacuous GD Lpa xpa cpu i Hxram rs _ rfl rfl l s' Hst).elim
    isplit
    · iintro %s' %Hw
      obtain ⟨rs', rfl⟩ := l3pAwireRsOnly cpu (rM2 Lpa xpa) rs none ibNone 1 s' Hw
      iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
      inext
      iapply IH $$ %rs' HP
    · iintro %Heq
      have hf : False := by
        rw [Hrow] at Heq
        simp [l3pRRow] at Heq
      exact hf.elim
  iintro HP %rs
  iapply H $$ %rs HP

/-! ### 8.5 Position 0, release-sourced -/

theorem r0FlowEqRel (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hcons : rvwmoCatConsistent GD)
    (w_rel : Geid) (Hwrel_wb0 : gwritesByte GD.gdG w_rel L b0)
    (Hgob_rel : gobCat GD w_rel (i, 0)) (Hrfe_rel : lockExtRmwReader L GD w_rel (i, 0))
    (j0 : Agent) (t0 : Nat) (old0 v0 : BitVec 8) (Heq_wrel : w_rel = (j0, 3))
    (Hrow_j0 : AxOpsem.grow GD j0 = l3pWRow Lpa xpa t0 old0 v0) :
    ⊢ @flowEqDyn hlc GF _ (axGA2Lock3 L x GD nm) GD (i, 0) (lockPolS GD (i, 0)) (∅ : Mea GF)
        iprop(R0er (GF := GF) x GD nm i w_rel ∗ ⌜graphData GD (i, 0) = some [b1]⌝) := by
  iapply (@flowEqDynMono hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol GD (i, 0) (lockPolS GD (i, 0))
    _ iprop(∃ Hh, xTok GD nm.1 x Hh (i, 0) ∗
      ⌜histXWf x GD Hh ∧ lockHhPoLatest x GD Hh w_rel⌝)
    iprop(R0er (GF := GF) x GD nm i w_rel ∗ ⌜graphData GD (i, 0) = some [b1]⌝))
  · inext
    iintro ⟨%Hh, Htie, %Hp⟩
    have Hlast1 := wrelPoLatestPin L x GD Lpa xpa HLeq Hxeq w_rel j0 t0 old0 v0 Heq_wrel Hrow_j0
      Hh Hp.2
    isplitl [Htie]
    · unfold R0er
      iexists Hh
      iunfold xTok at Htie
      icases Htie with (Htie | ⟨%Heq, -⟩)
      · isplitl [Htie]
        · iexact Htie
        · ipureintro
          exact Hp
      · rw [Heq] at Hlast1
        cases Hlast1
    · ipureintro
      exact r0Gd L GD Lpa xpa i t old tx vB HLeq Hrow
  · iapply (lockAcqFlowEq3A (hlc := hlc) L x GD nm GD w_rel (i, 0) ∅ Hcons Hwrel_wb0
      (r0Wb L GD Lpa xpa i t old tx vB HLeq Hrow) (r0Single L GD Lpa xpa i t old tx vB HLeq Hrow)
      Hgob_rel Hrfe_rel)

/-- Position 0's write half (release-sourced): Löb over the register file (the SC retry
self-loop and the wire). -/
theorem wpdrW0WriteRel (hxy : x ≠ L) (HLram : devAddr Lpa = false) (Hxram : devAddr xpa = false)
    (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hcons : rvwmoCatConsistent GD)
    (w_rel : Geid) (Hwrel_wb0 : gwritesByte GD.gdG w_rel L b0)
    (Hgob_rel : gobCat GD w_rel (i, 0)) (Hrfe_rel : lockExtRmwReader L GD w_rel (i, 0))
    (j0 : Agent) (t0 : Nat) (old0 v0 : BitVec 8) (Heq_wrel : w_rel = (j0, 3))
    (Hrow_j0 : AxOpsem.grow GD j0 = l3pWRow Lpa xpa t0 old0 v0)
    (s : Athread) (rs : RegFile) (Heqp : s.atP = .PHart cpu (rM1 Lpa xpa) rs none ibNone)
    (Heqk : s.atK = 0) :
    ⊢ AxLock3Reader.twpdr GF hlc L x GD nm i vB s := by
  obtain ⟨p, k⟩ := s
  simp only at Heqp Heqk
  subst Heqp Heqk
  have H : ⊢ ∀ rs : RegFile,
      AxLock3Reader.twpdr GF hlc L x GD nm i vB ⟨.PHart cpu (rM1 Lpa xpa) rs none ibNone, 0⟩ := by
    iloeb as IH
    iintro %rs
    unfold AxLock3Reader.twpdr tierAWpd
    iapply (@AxWpD.wpdMUnfoldStep hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol rvwmoCatConsistent
      .MaybeStuck i _ _).2
    isplit
    · iapply (@progressOblMaybestuck GF (axGA2Lock3 L x GD nm) lockAxpol i _).2
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, -⟩
    ihave %Hg := AxLock3Writer.gconstPure L x GD nm GD' $$ Hg
    subst GD'
    isplit
    · iintro %id %K %Hst
      have hfalse : False := by
        obtain ⟨lb, Hlb, Hid, Hsome, HK⟩ := Hst
        simp only at Hlb
        rw [Hrow] at Hlb
        simp only [l3pRRow, List.getElem?_cons_zero, Option.some.injEq] at Hlb
        subst Hlb Hid
        obtain ⟨l0, d0, d0', Hwlrd, -, Hpst, -⟩ := HK [old] rfl
        rcases l3pWriteExclDet cpu Lpa HLram b1 (fun _ => rM2 Lpa xpa) rs ibNone d0 l0 _ d0'
          Hpst with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ <;> simp [wlRd, aident, aidentRd] at Hwlrd
      exact hfalse.elim
    isplit
    · iintro %l %s' %Hst %-
      rcases astepProgWrite0RelInv GD Lpa xpa cpu i HLram rs _ rfl rfl l s' Hst with
        ⟨Hwd, rfl⟩ | ⟨rfl, rfl⟩
      · rw [Hwd, l3pWbytes1]
        dsimp only
        unfold wpEvStep naAtProgress
        iintro %na ⟨%Hprog, Hannot⟩
        have Hnin0 : (i, 0) ∉ (FiniteMap.dom_set na : GSet Geid) := by
          intro Hin
          have Hf : (i, 0) ∈ FiniteSet.filter (fun e : Geid => decide (e.1 = i))
              (FiniteMap.dom_set na : GSet Geid) := elemOfFilter.2 ⟨by simp, Hin⟩
          rw [Hprog, elemOfEidsBefore] at Hf
          exact Nat.not_lt_zero _ Hf.2.1
        imod (annotAlloc na (i, 0) (R0er (GF := GF) x GD nm i w_rel) Hnin0) $$ Hannot
          with ⟨Hannot', Hpt0⟩
        ihave Hfeq0 := r0FlowEqRel (hlc := hlc) L x GD nm Lpa xpa i t old tx vB HLeq Hxeq Hrow
          Hcons w_rel Hwrel_wb0 Hgob_rel Hrfe_rel j0 t0 old0 v0 Heq_wrel Hrow_j0
        imodintro
        inext
        imodintro
        iexists (), R0er (GF := GF) x GD nm i w_rel, (∅ : Mea GF), (∅ : Mea GF), ()
        isplitr
        · ipureintro
          trivial
        isplitr
        · unfold naSplittingWf
          isplitr
          · ipureintro
            rw [domEmpty]
            exact LawfulSet.empty_subset
          · iapply (BigSepM2.bigSepM2_empty _).2
            itrivial
        isplitl [Hfeq0]
        · iexact Hfeq0
        isplitl [Hannot']
        · rw [AxLockWp.annotInsertEq]
          iexact Hannot'
        isplitr
        · iapply AxLock3Writer.localTriv
        · have Hw1 := wpdrW1 (GF := GF) (hlc := hlc) L x GD nm Lpa xpa cpu i t old tx vB hxy HLram
            Hxram HLeq Hxeq Hrow Hcons w_rel Hrfe_rel j0 t0 old0 v0 Heq_wrel Hrow_j0
          unfold AxLock3Reader.twpdr tierAWpd at Hw1
          ihave H := Hw1 $$ Hpt0
          dsimp only
          iapply H
      · simp only [wlWdata]
        iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
        inext
        iapply IH $$ %rs
    isplit
    · iintro %s' %Hw
      obtain ⟨rs', rfl⟩ := l3pAwireRsOnly cpu (rM1 Lpa xpa) rs none ibNone 0 s' Hw
      iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
      inext
      iapply IH $$ %rs'
    · iintro %Heq
      have hf : False := by
        rw [Hrow] at Heq
        simp [l3pRRow] at Heq
      exact hf.elim
  iapply H $$ %rs

/-- Position 0's read half (release-sourced): the real (demonic) read, pinned to `rM1`. -/
theorem wpdrW0ReadRel (hxy : x ≠ L) (HLram : devAddr Lpa = false) (Hxram : devAddr xpa = false)
    (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hcons : rvwmoCatConsistent GD)
    (w_rel : Geid) (Hwrel_wb0 : gwritesByte GD.gdG w_rel L b0)
    (Hgob_rel : gobCat GD w_rel (i, 0)) (Hrfe_rel : lockExtRmwReader L GD w_rel (i, 0))
    (j0 : Agent) (t0 : Nat) (old0 v0 : BitVec 8) (Heq_wrel : w_rel = (j0, 3))
    (Hrow_j0 : AxOpsem.grow GD j0 = l3pWRow Lpa xpa t0 old0 v0) :
    ⊢ ∀ rs : RegFile,
      AxLock3Reader.twpdr GF hlc L x GD nm i vB
        ⟨.PHart cpu (AxLock3Reader.rM0 Lpa xpa) rs none ibNone, 0⟩ := by
  iloeb as IH
  iintro %rs
  unfold AxLock3Reader.twpdr tierAWpd
  iapply (@AxWpD.wpdMUnfoldStep hlc GF _ (axGA2Lock3 L x GD nm) lockAxpol rvwmoCatConsistent
    .MaybeStuck i _ _).2
  isplit
  · iapply (@progressOblMaybestuck GF (axGA2Lock3 L x GD nm) lockAxpol i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD' %ls ⟨%Hc, #Hg, -⟩
  ihave %Hg := AxLock3Writer.gconstPure L x GD nm GD' $$ Hg
  subst GD'
  isplit
  · iintro %id %K %Hst
    obtain ⟨lb, Hlb, Hid, -, HK⟩ := Hst
    simp only at Hlb
    rw [Hrow] at Hlb
    simp only [l3pRRow, List.getElem?_cons_zero, Option.some.injEq] at Hlb
    subst Hlb Hid
    simp only [aident, aidentAdvRd, Nat.zero_ne_one, ↓reduceIte]
    iintro %gv %Hgv %Hlen
    obtain ⟨l0, d0, d0', -, -, Hpst, Hatk⟩ := HK gv Hlen
    have Hp := (r0ReadDet Lpa xpa cpu HLram rs d0 l0 _ d0' Hpst).1
    have Hk0 : (K gv).atK = 0 := by rw [Hatk]; rfl
    iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
    inext
    have Hw0 := wpdrW0WriteRel (GF := GF) (hlc := hlc) L x GD nm Lpa xpa cpu i t old tx vB hxy
      HLram Hxram HLeq Hxeq Hrow Hcons w_rel Hwrel_wb0 Hgob_rel Hrfe_rel j0 t0 old0 v0 Heq_wrel
      Hrow_j0 (K gv) rs Hp Hk0
    unfold AxLock3Reader.twpdr tierAWpd at Hw0
    iapply Hw0
  isplit
  · iintro %l %s' %Hst %-
    exact (astepProgRead0RelVacuous GD Lpa xpa cpu i HLram rs _ rfl rfl l s' Hst).elim
  isplit
  · iintro %s' %Hw
    obtain ⟨rs', rfl⟩ := l3pAwireRsOnly cpu (AxLock3Reader.rM0 Lpa xpa) rs none ibNone 0 s' Hw
    iapply wpdSkipStepOfLater (GF := GF) L x GD nm i
    inext
    iapply IH $$ %rs'
  · iintro %Heq
    have hf : False := by
      rw [Hrow] at Heq
      simp [l3pRRow] at Heq
    exact hf.elim

/-- 14. THE CAPSTONE (release-sourced acquire): from `lock3Init nm i` (`emp`). -/
theorem wpdReaderHartRel (hxy : x ≠ L) (HLram : devAddr Lpa = false)
    (Hxram : devAddr xpa = false) (HLeq : L = l3pLbase Lpa) (Hxeq : x = l3pXbase xpa)
    (Hrow : AxOpsem.grow GD i = l3pRRow Lpa xpa t old tx vB) (Hcons : rvwmoCatConsistent GD)
    (w_rel : Geid) (Hwrel_wb0 : gwritesByte GD.gdG w_rel L b0)
    (Hgob_rel : gobCat GD w_rel (i, 0)) (Hrfe_rel : lockExtRmwReader L GD w_rel (i, 0))
    (j0 : Agent) (t0 : Nat) (old0 v0 : BitVec 8) (Heq_wrel : w_rel = (j0, 3))
    (Hrow_j0 : AxOpsem.grow GD j0 = l3pWRow Lpa xpa t0 old0 v0) (rs : RegFile) :
    ⊢ lock3Init (GF := GF) nm i -∗
      AxLock3Reader.twpdr GF hlc L x GD nm i vB ⟨l3pRP0 Lpa xpa cpu rs, 0⟩ := by
  have heq : l3pRP0 Lpa xpa cpu rs = .PHart cpu (AxLock3Reader.rM0 Lpa xpa) rs none ibNone := rfl
  rw [heq]
  iintro -
  ihave H := wpdrW0ReadRel (hlc := hlc) L x GD nm Lpa xpa cpu i t old tx vB hxy HLram Hxram HLeq
    Hxeq Hrow Hcons w_rel Hwrel_wb0 Hgob_rel Hrfe_rel j0 t0 old0 v0 Heq_wrel Hrow_j0
  iapply H $$ %rs

end RRel

end reader

end Weak
