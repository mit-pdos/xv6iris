/-
Weak: **RUN PAIRING** for the AxSL-style base logic (§§1–9; §10, the real store, is `AxPair2`).

Rocq: `iris/AxPair.v` @ xxvzwolszwmp (lines 1–1621 here; 1622–1977 in `Weak/AxPair2.lean`).

## The Rocq header, in substance

The base logic runs each hart's Sail program on EXPECTED read values; `hart_conf` is about the
REAL run.  Adequacy needs the two runs to emit labels equal in IDENTITY (kind, address, size,
dependency sources, aq/rl) at every event whose identity does not depend on a mismatched read, and
equal outright once the data sources are validated.  `WeakEvProv2.tpar` is the semantic law this
rests on; this file restates it at the identity/data split.

  §1 `AxPair.Ident` / `lblIdent` / `identEq`: the identity projection of a memory label (values,
     timestamps dropped); `lblModdata`: "equal except possibly in store data"; `AxPair.lblWdata`:
     the data.  Identity is a function of the modulo-data class (`lblModdataIdent`); class + data
     pin the label (`lblModdataData`).
  §2 `tpid T`: `tpar T` plus ONE arm `tpiMw`, a memory WRITE of possibly DIFFERENT data at the
     SAME identity (same address and access kind, RAM), continuations pointwise.
  §3 `tpidStep`: one paired step -- EITHER a tainted-carrier read at a `tpar`-related pair (the
     STOP), OR the second run steps with a `lblModdata`-equal label, same annotations / channel /
     fabric, nodes still `tpid`-related, register files still agreeing off `T`.
  §4 `pairIdent`, THE IDENTITY-STOP LEMMA: any run splits at its FIRST tainted read; the prefix is
     hit-free and PAIRED; `pairIdentFull`; `pairResume` (a stop node is a `regRead` of the tainted
     carrier on BOTH sides); `pairAfterValidation`.
  §5 Non-vacuity: (a) THE REAL TAIL of `lw a5,0(a4)` (`laPairIdent`, `T = [15]`); (b) a
     HAND-BUILT `sd a5,0(a4)` (real encoding `0x00f73023`, decoded by the tree's `depsOfIb` to
     `asrc = [DReg 14]`, `vsrc = [DReg 15]`): read `x15`, write its eight bytes to RAM, write `PC`
     (`swPair`, `swTwoWords`); `swNotTpar`: `tpar` has no arm for two different `memWrite`s.
  §6 `tpdg` / `tpdd`, THE TAINTED-DATA PAIRING: six arms (`tgConv`, `tgGen`, `tgWrEq`, `tgWr`,
     `tgRd` -- a `regRead` of a tainted carrier whose continuations are related at EVERY PAIR of
     values -- and `tgMw`, two `memWrite`s of the same pa and access kind); `tparTpdd`,
     `tpidTpdd`, `tpdgMono`, `tpdgBoundary`.
  §7 `tpddStep`: READ STOP (`stopRead`), FABRIC STOP (`stopMmio`, an MMIO write pair), or PAIRED;
     `pnodeStepPairR` (`WeakEvProv2.pnodeStepPair` with the relation abstracted), `tpddStepRd`.
  §8 `pairIdentDd` / `pairIdentDdFull` / `pairResumeDd`, and the validation forms
     `pairDataValidated` / `pairEventValidated` / `tpddShrink`.
  §9 `swMTpdd` / `swPairDd`: the hand-built store through its divergent data read.

The Rocq corrections (1)-(4) to the commissioned statements carry over verbatim (stops are at the
tainted `regRead`, not at a label; the different-data store is the new arm `tpiMw` plus the resume
protocol; register writes need no strengthening; the runs coincide only at a re-converged pair).

## Deviations from Rocq

1. NAMES / VOCABULARY: camelCase (map below) and `WeakEvProv2`'s vocabulary (`M unit` ↦ `SailM
   Unit`, `regstate` ↦ `RegFile`, `register_lookup r rs` ↦ `rs r`, `register_set r v rs` ↦
   `rs.set r v`, `oib32` ↦ `Ibch`, `wreg` ↦ `Nat`, `dev_state` ↦ `Efab` (`DevStates` at the
   `pnodeStep` tier), `default x o` ↦ `o.getD x`, `Z` ↦ `Int`, `bv n` ↦ `BitVec n`,
   `fmap` ↦ `List.map`, `Forall2` ↦ `List.Forall₂`).  `ikind`'s / `ident`'s `EqDecision`
   instances are `deriving DecidableEq`.
2. lean-sail's `regRead r` / `regWrite r v` carry NO access kind (Rocq `RegRead r ak`,
   `RegWrite r ak v`): `tgWrEq`/`tgWr`/`tgRd`, `stopRead`, `tparStopShape`, `regreadStep(Inv)`,
   `pairResume(Dd)`, `tpddStepRd` drop their `ak`s.  `memWrite` is indexed by the width AND the
   VA width (`n va`); the write continuation is `Result (Option Bool) Arch.abort → …`.
3. lean-sail's write request value is an `Option` (`req.value = some v` steps; `none` is stuck):
   `tpiMw` and `tgMw` take `rq1.value.isSome = rq2.value.isSome` (so the second run steps when the
   first does), and `pnodeStepStore` takes `rq.value = some v` and is stated at that `v`.
4. `obar` (`WeakEvInst` deviation 4): every step lemma carries the executed barrier `obar`, the
   same in both runs; `regreadStepInv` / `pairResume` / `pairResumeDd` also conclude
   `obar = none`.
5. `tpdg` is generic in the RESULT type only (`SailM A`): Rocq's extra-outcome family `Ex` exists
   for its early-return monad `MR R A`, which in lean-sail is `ExceptT … (SailM …)`, i.e. a
   `SailM` at another result type.  `tpdd` is the `abbrev` `tpdg Unit` (Rocq `Notation`).
   `oc_wr` is over `Outcome Register RegisterType` (Lean's `.error` node is stuck; no arm).
6. O2 Stage C (`notes/weak-port-o2-stageC.md`, owner Q-C1): Lean's `LIFetch base tvs` (Rocq: a
   plain `LLoad false … []` fetch, finding F7) is an ADMINISTRATIVE label of the graph tier (no row
   item, no identity, no edges), so `lblIdent (LIFetch base tvs) = none` (Rocq: the identity of
   that `LLoad`).  `lblModdata` / `AxPair.lblWdata` are unchanged (a fetch has no data and is not
   a store).
7. Lean-only helpers (file-qualified): `AxPair.pnodeStepMwIff` (the RAM `memWrite` arm of
   `pnodeStep` at a known value, as an iff), `AxPair.mwStepPairR` (`mwStepPair` with the relation
   abstracted: `tpidStep` and `tpddStep` both use it), `AxPair.genReadShape` (the `tpGen`/`tgGen`
   case of a tainted read, shared by `tparStopShape` and `tpddStep`), `AxPair.swPcLbl` (the `PC`
   write's label is `LSilent`), `AxPair.swMRds` (`pnodeRds swM = [15]`).
8. COMPUTATIONS: Rocq's `vm_compute` facts (`sw_bits_*`, `sw_pa_ram`, `sw_l_differ`'s `wdata_z`
   inequality) are `decide +kernel`; `mw_value` returns `Option Nat` (`rq.value.map toNat`,
   Rocq `Some (bv_unsigned …)`), `wdata_z` `Option (List Nat)`.  `Example sw_two_words` ↦
   `theorem`; §11's `Print Assumptions` are dropped (the lint's axiom/sorry ban is the audit).
9. `tpdg_mono`'s `T ⊆ T'` is `List.Subset`; `tpdd_shrink`'s `filter (∈ rds)` is
   `T.filter (fun n => decide (n ∈ rds))`.

**File-qualified names** (`notes/weak-port-dupnames.json`): `ident` ↦ `AxPair.Ident` (fields
`idKind idAq idRl idBase idBytes idAsrc idVsrc`, constructor `AxPair.Ident.mk`), `lbl_wdata` ↦
`AxPair.lblWdata`; (§10, `AxPair2`) `phrun_app` ↦ `AxPair.phrunApp`.

Q7 (owner ruling, `notes/weak-port-q7-sfence.md` route (a), Lean-only): the real-tail pair passes `WeakEvProv2.laLsNoMark` to `WeakEvProv.phrunNoInstr`.

**Rocq → Lean name map.**  `ikind` `Ikind` (`IKload/IKstore/IKrmw/IKexload/IKexstore` the same),
`ident_eq` `identEq`, `ident_eq_spec` `identEqSpec`, `lbl_ident` `lblIdent`, `lbl_moddata`
`lblModdata`, `lbl_moddata_refl/ident/data` `lblModdataRefl/Ident/Data`, `Forall2_moddata_ident`
`forall2ModdataIdent`, `tpid` `tpid` (`tpi_par/mw` `tpiPar/tpiMw`), `tpid_conv` `tpidConv`,
`tpid_boundary` `tpidBoundary`, `rds_hit` `rdsHit`, `rds_ok_or_hit` `rdsOkOrHit`,
`pnode_step_store` `pnodeStepStore`, `mw_step_pair` `mwStepPair`, `tpid_step` `tpidStep`,
`stop_at` `stopAt`, `pair_ident` `pairIdent`, `pair_ident_full` `pairIdentFull`,
`tpar_stop_shape` `tparStopShape`, `regread_step_inv` `regreadStepInv`, `regread_step`
`regreadStep`, `pair_resume` `pairResume`, `pair_after_validation` `pairAfterValidation`,
`la_pair_ident` `laPairIdent`, `sw_bits` `swBits`, `sw_bits_roles/asrc/vsrc`
`swBitsRoles/Asrc/Vsrc`, `sw_pa` `swPa`, `sw_pa_ram` `swPaRam`, `sw_ak` `swAk`, `sw_ak_plain`
`swAkPlain`, `sw_req` `swReq`, `sw_k` `swK`, `sw_tail` `swTail`, `sw_m` `swM`, `sw_ib` `swIb`,
`sw_ib'` `swIb'`, `sw_ib'_bits` `swIb'Bits`, `sw_l` `swL`, `sw_tail_tpid` `swTailTpid`,
`mw_value` `mwValue`, `sw_not_tpar` `swNotTpar`, `sw_tail_run` `swTailRun`, `sw_stop` `swStop`,
`sw_pair` `swPair`, `sw_l_moddata` `swLModdata`, `wdata_z` `wdataZ`, `sw_l_differ` `swLDiffer`,
`sw_two_words` `swTwoWords`, `oc_wr` `ocWr`, `tpdg` `tpdg` (`tg_conv/gen/wr_eq/wr/rd/mw`
`tgConv/tgGen/tgWrEq/tgWr/tgRd/tgMw`), `tpdd` `tpdd`, `tpdd_conv` `tpddConv`, `pnode_wrs_oc_wr`
`pnodeWrsOcWr`, `tpar_tpdd` `tparTpdd`, `tpid_tpdd` `tpidTpdd`, `tpdg_mono` `tpdgMono`,
`tpdg_boundary` `tpdgBoundary`, `stop_read` `stopRead`, `stop_mmio` `stopMmio`,
`pnode_rds_shape` `pnodeRdsShape`, `pnode_step_pair_R` `pnodeStepPairR`, `tpdd_step_rd`
`tpddStepRd`, `tpdd_step` `tpddStep`, `pair_ident_dd` `pairIdentDd`, `pair_ident_dd_full`
`pairIdentDdFull`, `pair_resume_dd` `pairResumeDd`, `pair_data_validated` `pairDataValidated`,
`pair_event_validated` `pairEventValidated`, `tpdd_shrink` `tpddShrink`, `sw_tail_tpdd`
`swTailTpdd`, `sw_m_tpdd` `swMTpdd`, `sw_pair_dd` `swPairDd`.

**Dropped:** nothing (Rocq §§1–9: 78 declarations, plus the two `EqDecision` instances, now
`deriving`; Lean 78 + 5 Lean-only helpers).
-/
import Weak.WeakEvProv2

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! ## 1. THE IDENTITY OF A MEMORY LABEL -/

inductive Ikind where
  | IKload
  | IKstore
  | IKrmw
  | IKexload
  | IKexstore
  deriving DecidableEq, Repr

/-- Kind, aq/rl bits, base address, byte count, address and data sources.  Values and timestamps
are dropped; `LLoad`'s `lat` is a hardwired `false` in the program half and is dropped too. -/
structure AxPair.Ident where
  idKind : Ikind
  idAq : Bool
  idRl : Bool
  idBase : Int
  idBytes : Nat
  idAsrc : List Dsrc
  idVsrc : List Dsrc
  deriving DecidableEq

def identEq (i j : AxPair.Ident) : Bool := decide (i = j)

theorem identEqSpec (i j : AxPair.Ident) : identEq i j = true ↔ i = j := by
  unfold identEq
  exact decide_eq_true_iff

/-- The identity of a label (deviation 6: a fetch is an admin label and has none). -/
def lblIdent (l : Wlabel) : Option AxPair.Ident :=
  match l with
  | LLoad aq _ base tvs asrc => some ⟨.IKload, aq, false, base, tvs.length, asrc, []⟩
  | LStore rl base data asrc vsrc => some ⟨.IKstore, false, rl, base, data.length, asrc, vsrc⟩
  | LRmw aq rl base _ data asrc vsrc => some ⟨.IKrmw, aq, rl, base, data.length, asrc, vsrc⟩
  | LExLoad aq base tvs asrc => some ⟨.IKexload, aq, false, base, tvs.length, asrc, []⟩
  | LExStore rl base data asrc vsrc =>
      some ⟨.IKexstore, false, rl, base, data.length, asrc, vsrc⟩
  | _ => none

/-- The DATA of a write label. -/
def AxPair.lblWdata (l : Wlabel) : Option (List (BitVec 8)) :=
  match l with
  | LStore _ _ data _ _ | LRmw _ _ _ _ data _ _ | LExStore _ _ data _ _ => some data
  | _ => none

/-- "EQUAL EXCEPT POSSIBLY IN STORE DATA". -/
def lblModdata (l1 l2 : Wlabel) : Prop :=
  l1 = l2 ∨
  (∃ (rl : Bool) (base : Int) (d1 d2 : List (BitVec 8)) (asrc vsrc : List Dsrc),
     d1.length = d2.length ∧ l1 = LStore rl base d1 asrc vsrc ∧ l2 = LStore rl base d2 asrc vsrc) ∨
  (∃ (rl : Bool) (base : Int) (d1 d2 : List (BitVec 8)) (asrc vsrc : List Dsrc),
     d1.length = d2.length ∧ l1 = LExStore rl base d1 asrc vsrc ∧
       l2 = LExStore rl base d2 asrc vsrc)

theorem lblModdataRefl (l : Wlabel) : lblModdata l l := Or.inl rfl

theorem lblModdataIdent (l1 l2 : Wlabel) : lblModdata l1 l2 → lblIdent l1 = lblIdent l2 := by
  rintro (rfl | ⟨rl, base, d1, d2, asrc, vsrc, hlen, rfl, rfl⟩ |
    ⟨rl, base, d1, d2, asrc, vsrc, hlen, rfl, rfl⟩)
  · rfl
  · simp only [lblIdent, hlen]
  · simp only [lblIdent, hlen]

theorem lblModdataData (l1 l2 : Wlabel) :
    lblModdata l1 l2 → AxPair.lblWdata l1 = AxPair.lblWdata l2 → l1 = l2 := by
  rintro (rfl | ⟨rl, base, d1, d2, asrc, vsrc, -, rfl, rfl⟩ |
    ⟨rl, base, d1, d2, asrc, vsrc, -, rfl, rfl⟩) hd
  · rfl
  · simp only [AxPair.lblWdata, Option.some.injEq] at hd
    rw [hd]
  · simp only [AxPair.lblWdata, Option.some.injEq] at hd
    rw [hd]

theorem forall2ModdataIdent (ls1 ls2 : List Wlabel) :
    List.Forall₂ lblModdata ls1 ls2 → ls1.map lblIdent = ls2.map lblIdent := by
  intro h
  induction h with
  | nil => rfl
  | cons hl _ ih => simp only [List.map_cons, lblModdataIdent _ _ hl, ih]

/-! ## 2. THE IDENTITY PAIRING -/

inductive tpid (T : List Nat) : SailM Unit → SailM Unit → Prop where
  /-- `tpar`'s four arms, verbatim. -/
  | tpiPar (m1 m2 : SailM Unit) : tpar T m1 m2 → tpid T m1 m2
  /-- THE ONE NEW ARM: a memory write of possibly DIFFERENT data at the SAME identity -- same
  address, same access kind, in RAM.  Continuations pointwise. -/
  | tpiMw (n va : Nat) (rq1 rq2 : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k1 k2 : Result (Option Bool) Arch.abort → SailM Unit) :
      rq1.pa = rq2.pa → rq1.access_kind = rq2.access_kind → devAddr rq1.pa = false →
      rq1.value.isSome = rq2.value.isSome →
      (∀ a, tpid T (k1 a) (k2 a)) →
      tpid T (.impure (.ok (.memWrite n va rq1)) k1) (.impure (.ok (.memWrite n va rq2)) k2)

theorem tpidConv (T : List Nat) (m : SailM Unit) : tpid T m m := .tpiPar _ _ (.tpConv _)

/-- The boundary is shared, as for `tpar`. -/
theorem tpidBoundary (T : List Nat) (y : Unit) (m : SailM Unit) :
    tpid T (.pure y) m → m = .pure y := by
  intro h
  cases h with
  | tpiPar _ _ hp => exact tparBoundary T y m hp

/-! ## 3. ONE PAIRED STEP -/

/-- A read set that HITS the taint set. -/
def rdsHit (T rds : List Nat) : Prop := ∃ n, n ∈ rds ∧ n ∈ T

theorem rdsOkOrHit (T rds : List Nat) : rdsOk (fun n => n ∉ T) rds ∨ rdsHit T rds := by
  rcases Classical.em (∃ n, n ∈ rds ∧ n ∈ T) with h | h
  · exact Or.inr h
  · exact Or.inl (fun n hn hnT => h ⟨n, hn, hnT⟩)

/-- (Lean-only, deviation 7) the RAM `memWrite` arm of `pnodeStep` at a known value. -/
theorem AxPair.pnodeStepMwIff (n va : Nat)
    (rq : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates)
    (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) (v : BitVec (8 * n)) :
    devAddr rq.pa = false → rq.value = some v →
    (pnodeStep (.impure (.ok (.memWrite n va rq)) k) rs ib d l m' ors fn' d' oib obar ↔
      n ≠ 0 ∧
      (((classify rq.access_kind).akLatest = false ∧
         l = LStore (classify rq.access_kind).akSync (paZ rq.pa) (WeakInterpProj.wbytes n v)
               (depsAsrc (depsOfIb ib.ibBits)) (depsVsrc (depsOfIb ib.ibBits)) ∧
         m' = k (.Ok (some true)) ∧ ors = none ∧ fn' = none ∧ d' = d ∧ oib = none ∧
         obar = none)
       ∨
       ((classify rq.access_kind).akLatest = true ∧
         ((l = LExStore (classify rq.access_kind).akSync (paZ rq.pa)
                 (WeakInterpProj.wbytes n v) (depsAsrc (depsOfIb ib.ibBits))
                 (depsVsrc (depsOfIb ib.ibBits)) ∧
            m' = k (.Ok (some true)) ∧ ors = none ∧ fn' = none ∧ d' = d ∧ oib = none ∧
            obar = none)
          ∨
          (l = LSilent ∧ m' = .impure (.ok (.memWrite n va rq)) k ∧ ors = none ∧
            fn' = none ∧ d' = d ∧ oib = none ∧ obar = none))))) := by
  intro hdev hv
  simp only [pnodeStep, hdev, hv, Bool.false_eq_true, if_false]

/-- The plain-RAM-store arm of `pnodeStep`, as an introduction rule (deviation 3). -/
theorem pnodeStepStore (n va : Nat)
    (rq : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak) (v : BitVec (8 * n))
    (k : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch)
    (d : DevStates) :
    devAddr rq.pa = false → rq.value = some v → n ≠ 0 →
    (classify rq.access_kind).akLatest = false →
    pnodeStep (.impure (.ok (.memWrite n va rq)) k) rs ib d
      (LStore (classify rq.access_kind).akSync (paZ rq.pa) (WeakInterpProj.wbytes n v)
        (depsAsrc (depsOfIb ib.ibBits)) (depsVsrc (depsOfIb ib.ibBits)))
      (k (.Ok (some true))) none none d none none := by
  intro hdev hv hn hlat
  exact (AxPair.pnodeStepMwIff n va rq k rs ib d _ _ _ _ _ _ _ v hdev hv).2
    ⟨hn, Or.inl ⟨hlat, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- (Lean-only, deviation 7) THE STEP OUT OF A DIFFERENT-DATA WRITE PAIR, for any relation `R`
holding of the continuations and of the pair itself (the retry self-loop). -/
theorem AxPair.mwStepPairR (R : SailM Unit → SailM Unit → Prop) (n va : Nat)
    (rq1 rq2 : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k1 k2 : Result (Option Bool) Arch.abort → SailM Unit) (rs1 rs2 : RegFile) (ib : Ibch)
    (d : DevStates) (l : Wlabel) (m1' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    rq1.pa = rq2.pa → rq1.access_kind = rq2.access_kind → devAddr rq1.pa = false →
    rq1.value.isSome = rq2.value.isSome →
    (∀ a, R (k1 a) (k2 a)) →
    R (.impure (.ok (.memWrite n va rq1)) k1) (.impure (.ok (.memWrite n va rq2)) k2) →
    pnodeStep (.impure (.ok (.memWrite n va rq1)) k1) rs1 ib d l m1' ors fn' d' oib obar →
    ors = none ∧
    ∃ (l2 : Wlabel) (m2' : SailM Unit),
      pnodeStep (.impure (.ok (.memWrite n va rq2)) k2) rs2 ib d l2 m2' none fn' d' oib obar ∧
      lblModdata l l2 ∧ R m1' m2' := by
  intro hpa hak hdev hval hk hloop h
  have hdev2 : devAddr rq2.pa = false := hpa ▸ hdev
  cases hv1 : rq1.value with
  | none => simp only [pnodeStep, hdev, hv1, Bool.false_eq_true, if_false] at h
  | some v1 =>
    cases hv2 : rq2.value with
    | none => rw [hv1, hv2] at hval; cases hval
    | some v2 =>
      rw [AxPair.pnodeStepMwIff n va rq1 k1 rs1 ib d l m1' ors fn' d' oib obar v1 hdev hv1] at h
      have H2 := AxPair.pnodeStepMwIff n va rq2 k2 rs2 ib d
      rw [← hpa, ← hak] at H2
      rcases h with ⟨hn0, ⟨hlat, rfl, rfl, rfl, h4, h5, h6, h7⟩ |
        ⟨hlat, ⟨rfl, rfl, rfl, h4, h5, h6, h7⟩ | ⟨rfl, rfl, rfl, h4, h5, h6, h7⟩⟩⟩
      · -- the plain store: identity equal, data may differ
        refine ⟨rfl, _, _, (H2 _ _ _ _ _ _ _ v2 hdev hv2).2
          ⟨hn0, Or.inl ⟨hlat, rfl, rfl, rfl, h4, h5, h6, h7⟩⟩, ?_, hk _⟩
        exact Or.inr (Or.inl ⟨_, _, _, _, _, _, by rw [wbytesLength, wbytesLength], rfl, rfl⟩)
      · -- the conditional store
        refine ⟨rfl, _, _, (H2 _ _ _ _ _ _ _ v2 hdev hv2).2
          ⟨hn0, Or.inr ⟨hlat, Or.inl ⟨rfl, rfl, rfl, h4, h5, h6, h7⟩⟩⟩, ?_, hk _⟩
        exact Or.inr (Or.inr ⟨_, _, _, _, _, _, by rw [wbytesLength, wbytesLength], rfl, rfl⟩)
      · -- the retry self-loop: both nodes stay
        exact ⟨rfl, _, _, (H2 _ _ _ _ _ _ _ v2 hdev hv2).2
          ⟨hn0, Or.inr ⟨hlat, Or.inr ⟨rfl, rfl, rfl, h4, h5, h6, h7⟩⟩⟩, Or.inl rfl, hloop⟩

/-- The step out of a `tpiMw` pair, at the node arm. -/
theorem mwStepPair (T : List Nat) (n va : Nat)
    (rq1 rq2 : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k1 k2 : Result (Option Bool) Arch.abort → SailM Unit) (rs1 rs2 : RegFile) (ib : Ibch)
    (d : DevStates) (l : Wlabel) (m1' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    rq1.pa = rq2.pa → rq1.access_kind = rq2.access_kind → devAddr rq1.pa = false →
    rq1.value.isSome = rq2.value.isSome →
    (∀ a, tpid T (k1 a) (k2 a)) →
    pnodeStep (.impure (.ok (.memWrite n va rq1)) k1) rs1 ib d l m1' ors fn' d' oib obar →
    ors = none ∧
    ∃ (l2 : Wlabel) (m2' : SailM Unit),
      pnodeStep (.impure (.ok (.memWrite n va rq2)) k2) rs2 ib d l2 m2' none fn' d' oib obar ∧
      lblModdata l l2 ∧ tpid T m1' m2' :=
  fun hpa hak hdev hval hk =>
    AxPair.mwStepPairR (tpid T) n va rq1 rq2 k1 k2 rs1 rs2 ib d l m1' ors fn' d' oib obar hpa
      hak hdev hval hk (.tpiMw n va rq1 rq2 k1 k2 hpa hak hdev hval hk)

/-- THE PAIRED STEP. -/
theorem tpidStep (T : List Nat) (cpu : CPU) (m1 m2 : SailM Unit) (rs1 rs2 : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (l : Wlabel)
    (rds : List Nat) (ws : List Register) (ann : Bool) (m1' : SailM Unit)
    (ors1 : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (d' : Efab)
    (oib : Option Ibch) (obar : Option barrier_kind) :
    pstepHw cpu m1 rs1 fn ib d l rds ws ann m1' ors1 fn' d' oib obar →
    tpid T m1 m2 →
    dregAgree (fun n => n ∉ T) rs1 rs2 →
    (tpar T m1 m2 ∧ rdsHit T rds) ∨
    (rdsOk (fun n => n ∉ T) rds ∧
     ∃ (l2 : Wlabel) (m2' : SailM Unit) (ors2 : Option RegFile),
       pstepHw cpu m2 rs2 fn ib d l2 rds ws ann m2' ors2 fn' d' oib obar ∧
       lblModdata l l2 ∧
       tpid T m1' m2' ∧
       dregAgree (fun n => n ∉ T) (ors1.getD rs1) (ors2.getD rs2)) := by
  intro hhw htp hag
  cases htp with
  | tpiPar _ _ hpar =>
    -- `tpar`'s arms: `tparStep` when the read set is clean
    rcases rdsOkOrHit T rds with hok | hhit
    · obtain ⟨m2', ors2, hst2, htp2, hag2⟩ :=
        tparStep T cpu _ _ rs1 rs2 fn ib d l rds ws ann m1' ors1 fn' d' oib obar hhw hpar hok hag
      exact Or.inr ⟨hok, l, m2', ors2, hst2, Or.inl rfl, .tpiPar _ _ htp2, hag2⟩
    · exact Or.inl ⟨hpar, hhit⟩
  | tpiMw n va rq1 rq2 k1 k2 hpa hak hdev hval hk =>
    -- the write arm: a memory node reads no register
    rcases hhw with ⟨rfl, ⟨hst, hd⟩, rfl, rfl, rfl⟩ |
      ⟨pr, pw, sr, sw, rfl, ⟨hst, hd⟩, rfl, rfl, rfl⟩ | ⟨hp, rfl, rfl, rfl⟩
    · -- the node
      obtain ⟨rfl, l2, m2', hst2, hmod, htp2⟩ :=
        mwStepPair T n va rq1 rq2 k1 k2 rs1 rs2 ib d.efDev l m1' ors1 fn' d'.efDev oib obar hpa
          hak hdev hval hk hst
      exact Or.inr ⟨fun _ h => by simp [pnodeRds] at h, l2, m2', none,
        Or.inl ⟨rfl, ⟨hst2, hd⟩, rfl, rfl, rfl⟩, hmod, htp2, hag⟩
    · -- the parked fence: neither node moves
      obtain ⟨h1, rfl, rfl, h4, h5, h6, h7⟩ := hst
      exact Or.inr ⟨fun _ h => by simp at h, l, _, none,
        Or.inr (Or.inl ⟨pr, pw, sr, sw, rfl, ⟨⟨h1, rfl, rfl, h4, h5, h6, h7⟩, hd⟩, rfl, rfl, rfl⟩),
        Or.inl rfl, .tpiMw n va rq1 rq2 k1 k2 hpa hak hdev hval hk, hag⟩
    · -- the PLIC wire: neither node moves, the same pin is written
      obtain ⟨mm, b, k, hk', h1, rfl, h3, h4, h5, h6, rfl⟩ := hp
      refine Or.inr ⟨fun _ h => by simp at h, l, _, some (pinSet rs2 mm b),
        Or.inr (Or.inr ⟨⟨mm, b, k, hk', h1, rfl, h3, h4, h5, h6, rfl⟩, rfl, rfl, rfl⟩),
        Or.inl rfl, .tpiMw n va rq1 rq2 k1 k2 hpa hak hdev hval hk, ?_⟩
      cases mm
      · exact dregAgreeSet _ rs1 rs2 _ _ hag
      · exact dregAgreeSet _ rs1 rs2 _ _ hag

/-! ## 4. THE IDENTITY-STOP LEMMA, AND THE RESUME PROTOCOL -/

/-- THE STOP: the node at `fn = none` reads a tainted carrier and that read is in the remainder's
read set. -/
def stopAt (T : List Nat) (fn : Option (Bool × Bool × Bool × Bool)) (m : SailM Unit)
    (rdsb : List Nat) : Prop :=
  fn = none ∧
  ∃ rdsHead rdsRest : List Nat,
    rdsb = rdsHead ++ rdsRest ∧ rdsHead = pnodeRds m ∧ rdsHit T rdsHead

/-- THE IDENTITY-STOP LEMMA. -/
theorem pairIdent (T : List Nat) (cpu : CPU) (ls : List Wlabel) (rds : List Nat)
    (ws : List Register) (ann : Bool) (m1 : SailM Unit) (rs1 : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (m1' : SailM Unit)
    (rs1' : RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (ib' : Ibch) (d' : Efab)
    (m2 : SailM Unit) (rs2 : RegFile) :
    phrun cpu ls rds ws ann m1 rs1 fn ib d m1' rs1' fn' ib' d' →
    tpid T m1 m2 →
    dregAgree (fun n => n ∉ T) rs1 rs2 →
    ∃ (lsa lsb : List Wlabel) (rdsa rdsb : List Nat) (wsa wsb : List Register)
      (anna annb : Bool) (ma : SailM Unit) (rsa : RegFile)
      (fna : Option (Bool × Bool × Bool × Bool)) (iba : Ibch) (da : Efab)
      (ls2 : List Wlabel) (m2a : SailM Unit) (rs2a : RegFile),
      ls = lsa ++ lsb ∧ rds = rdsa ++ rdsb ∧ ws = wsa ++ wsb ∧ ann = (anna || annb) ∧
      phrun cpu lsa rdsa wsa anna m1 rs1 fn ib d ma rsa fna iba da ∧
      phrun cpu lsb rdsb wsb annb ma rsa fna iba da m1' rs1' fn' ib' d' ∧
      rdsOk (fun n => n ∉ T) rdsa ∧
      List.Forall₂ lblModdata lsa ls2 ∧
      phrun cpu ls2 rdsa wsa anna m2 rs2 fn ib d m2a rs2a fna iba da ∧
      tpid T ma m2a ∧
      dregAgree (fun n => n ∉ T) rsa rs2a ∧
      (lsb = [] ∨ (tpar T ma m2a ∧ stopAt T fna ma rdsb)) := by
  intro hrun
  induction hrun generalizing m2 rs2 with
  | nil m rs fn ib d =>
    intro htp hag
    exact ⟨[], [], [], [], [], [], false, false, m, rs, fn, ib, d, [], m2, rs2, rfl, rfl, rfl, rfl,
      phrun.nil _ _ _ _ _, phrun.nil _ _ _ _ _, fun _ h => by simp at h, List.Forall₂.nil,
      phrun.nil _ _ _ _ _, htp, hag, Or.inl rfl⟩
  | @more l ls rds rds' ws ws' ann ann' m rs fn ib d ma ors fn1 oib obar d1 mb rsb fn2 ib2 d2
      hstep hrun' ih =>
    intro htp hag
    rcases tpidStep T cpu m m2 rs rs2 fn ib d l rds ws ann ma ors fn1 d1 oib obar hstep htp hag with
      ⟨hpar, hhit⟩ | ⟨hok, l2, mb1, orsb, hstepb, hmod, htp1, hagb⟩
    · -- THE STOP: split here, the prefix is empty
      refine ⟨[], l :: ls, [], rds ++ rds', [], ws ++ ws', false, ann || ann', m, rs, fn, ib, d, [],
        m2, rs2, rfl, rfl, rfl, by simp, phrun.nil _ _ _ _ _, phrun.more hstep hrun',
        fun _ h => by simp at h, List.Forall₂.nil, phrun.nil _ _ _ _ _, htp, hag,
        Or.inr ⟨hpar, ?_⟩⟩
      -- a hit means the node arm: `fn = none`, `rds = pnodeRds m`
      rcases hstep with ⟨rfl, _, rfl, _⟩ | ⟨_, _, _, _, _, _, rfl, _⟩ | ⟨_, rfl, _⟩
      · exact ⟨rfl, pnodeRds m, rds', rfl, rfl, hhit⟩
      · obtain ⟨n, hn, _⟩ := hhit
        simp at hn
      · obtain ⟨n, hn, _⟩ := hhit
        simp at hn
    · -- PAIRED: one more step on the prefix
      obtain ⟨lsa, lsb, rdsa, rdsb, wsa, wsb, anna, annb, ma', rsa, fna, iba, da, ls2, m2b, rs2b,
        rfl, rfl, rfl, rfl, hruna, hrunb, hoka, hf2, hrun2, htpa, haga, hstop⟩ :=
        ih mb1 (orsb.getD rs2) htp1 hagb
      exact ⟨l :: lsa, lsb, rds ++ rdsa, rdsb, ws ++ wsa, wsb, ann || anna, annb, ma', rsa, fna,
        iba, da, l2 :: ls2, m2b, rs2b, rfl, (List.append_assoc _ _ _).symm,
        (List.append_assoc _ _ _).symm, (Bool.or_assoc _ _ _).symm, phrun.more hstep hruna, hrunb,
        fun n hn => (List.mem_append.1 hn).elim (hok n) (hoka n), List.Forall₂.cons hmod hf2,
        phrun.more hstepb hrun2, htpa, haga, hstop⟩

/-- NO TAINTED READ ⇒ PAIRED TO THE END. -/
theorem pairIdentFull (T : List Nat) (cpu : CPU) (ls : List Wlabel) (rds : List Nat)
    (ws : List Register) (ann : Bool) (m1 : SailM Unit) (rs1 : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (m1' : SailM Unit)
    (rs1' : RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (ib' : Ibch) (d' : Efab)
    (m2 : SailM Unit) (rs2 : RegFile) :
    phrun cpu ls rds ws ann m1 rs1 fn ib d m1' rs1' fn' ib' d' →
    tpid T m1 m2 →
    rdsOk (fun n => n ∉ T) rds →
    dregAgree (fun n => n ∉ T) rs1 rs2 →
    ∃ (ls2 : List Wlabel) (m2' : SailM Unit) (rs2' : RegFile),
      List.Forall₂ lblModdata ls ls2 ∧
      phrun cpu ls2 rds ws ann m2 rs2 fn ib d m2' rs2' fn' ib' d' ∧
      tpid T m1' m2' ∧ dregAgree (fun n => n ∉ T) rs1' rs2' := by
  intro hrun htp hok hag
  obtain ⟨lsa, lsb, rdsa, rdsb, wsa, wsb, anna, annb, ma, rsa, fna, iba, da, ls2, m2a, rs2a,
    rfl, rfl, rfl, rfl, hruna, hrunb, -, hf2, hrun2, htpa, haga, hstop⟩ :=
    pairIdent T cpu ls rds ws ann m1 rs1 fn ib d m1' rs1' fn' ib' d' m2 rs2 hrun htp hag
  rcases hstop with rfl | ⟨-, -, rdsh, rdsr, rfl, rfl, n, hn, hnT⟩
  · -- the remainder is empty: the prefix is the run
    cases hrunb
    simp only [List.append_nil, Bool.or_false]
    exact ⟨ls2, m2a, rs2a, hf2, hrun2, htpa, haga⟩
  · exact absurd hnT (hok n (List.mem_append_right _ (List.mem_append_left _ hn)))

/-- (Lean-only, deviation 7) the `tpGen`/`tgGen` case of a tainted read: the outcome is that
`regRead`, the continuations are the pair's. -/
theorem AxPair.genReadShape (R : SailM Unit → SailM Unit → Prop)
    (o : Outcome Register RegisterType) (k1 k2 : Outcome.ret o → SailM Unit) (n : Nat) :
    n ∈ pnodeRds (.impure (.ok o) k1) → (∀ v, R (k1 v) (k2 v)) →
    ∃ (r : Register) (k1' k2' : RegisterType r → SailM Unit),
      (FreeM.impure (.ok o) k1 : SailM Unit) = .impure (.ok (.regRead r)) k1' ∧
      (FreeM.impure (.ok o) k2 : SailM Unit) = .impure (.ok (.regRead r)) k2' ∧
      eregNum r = some n ∧ ∀ v, R (k1' v) (k2' v) := by
  intro hn hk
  cases o with
  | regRead r =>
    cases hr : eregNum r with
    | none => simp [pnodeRds, hr] at hn
    | some n' =>
      simp [pnodeRds, hr] at hn
      subst hn
      exact ⟨r, k1, k2, rfl, rfl, hr, hk⟩
  | _ => simp [pnodeRds] at hn

/-- A node whose read set holds `n` is a `regRead` of the carrier `n`. -/
theorem pnodeRdsShape (m : SailM Unit) (n : Nat) :
    n ∈ pnodeRds m →
    ∃ (r : Register) (k : RegisterType r → SailM Unit),
      m = .impure (.ok (.regRead r)) k ∧ eregNum r = some n ∧ pnodeRds m = [n] := by
  intro hn
  match m, hn with
  | .pure _, hn => simp [pnodeRds] at hn
  | .impure (.error _) _, hn => simp [pnodeRds] at hn
  | .impure (.ok o) k, hn =>
    cases o with
    | regRead r =>
      cases hr : eregNum r with
      | none => simp [pnodeRds, hr] at hn
      | some n' =>
        simp [pnodeRds, hr] at hn
        subst hn
        exact ⟨r, k, rfl, hr, by simp [pnodeRds, hr]⟩
    | _ => simp [pnodeRds] at hn

/-- WHAT A STOP NODE IS. -/
theorem tparStopShape (T : List Nat) (m1 m2 : SailM Unit) (n : Nat) :
    tpar T m1 m2 → n ∈ pnodeRds m1 → n ∈ T →
    ∃ (r : Register) (k1 k2 : RegisterType r → SailM Unit),
      m1 = .impure (.ok (.regRead r)) k1 ∧
      m2 = .impure (.ok (.regRead r)) k2 ∧
      eregNum r = some n ∧
      (∀ v, tpar T (k1 v) (k2 v)) := by
  intro htp hn _
  cases htp with
  | tpConv =>
    obtain ⟨r, k, rfl, hr, -⟩ := pnodeRdsShape _ n hn
    exact ⟨r, k, k, rfl, rfl, hr, fun _ => .tpConv _⟩
  | tpGen o k1 k2 _ hk => exact AxPair.genReadShape (tpar T) o k1 k2 n hn hk
  | tpWrEq => simp [pnodeRds] at hn
  | tpWr => simp [pnodeRds] at hn

/-- … and how a `regRead` node steps at the node arm. -/
theorem regreadStepInv (cpu : CPU) (r : Register) (k : RegisterType r → SailM Unit)
    (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (l : Wlabel)
    (rds : List Nat) (ws : List Register) (ann : Bool) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : Efab) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    pstepHw cpu (.impure (.ok (.regRead r)) k) rs fn ib d l rds ws ann m' ors fn' d' oib obar →
    rds ≠ [] →
    fn = none ∧ l = LSilent ∧ m' = k (rs r) ∧ ors = none ∧ fn' = none ∧ d' = d ∧
    oib = some (ibRd ib r) ∧ obar = none ∧
    rds = pnodeRds (.impure (.ok (.regRead r)) k) ∧ ws = [] ∧ ann = false := by
  rintro (⟨rfl, ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, hd⟩, rfl, rfl, rfl⟩ |
    ⟨_, _, _, _, _, _, rfl, _, _⟩ | ⟨_, rfl, _, _⟩) hne
  · refine ⟨rfl, h1, h2, h3, h4, ?_, h6, h7, rfl, rfl, rfl⟩
    rw [h5] at hd
    exact hd
  · exact absurd rfl hne
  · exact absurd rfl hne

theorem regreadStep (cpu : CPU) (r : Register) (k : RegisterType r → SailM Unit) (rs : RegFile)
    (ib : Ibch) (d : Efab) :
    pstepHw cpu (.impure (.ok (.regRead r)) k) rs none ib d LSilent
      (pnodeRds (.impure (.ok (.regRead r)) k)) [] false (k (rs r)) none none d
      (some (ibRd ib r)) none :=
  Or.inl ⟨rfl, ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, rfl, rfl, rfl⟩

/-- THE RESUME PROTOCOL (deviation 4: also `obar = none`). -/
theorem pairResume (T : List Nat) (cpu : CPU) (m1 m2 : SailM Unit) (rs1 rs2 : RegFile)
    (ib : Ibch) (d : Efab) (l : Wlabel) (rds : List Nat) (ws : List Register) (ann : Bool)
    (m1' : SailM Unit) (ors1 : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : Efab) (oib : Option Ibch) (obar : Option barrier_kind) (n : Nat) :
    tpar T m1 m2 → n ∈ pnodeRds m1 → n ∈ T →
    pstepHw cpu m1 rs1 none ib d l rds ws ann m1' ors1 fn' d' oib obar →
    rds ≠ [] →
    ∃ (r : Register) (k1 k2 : RegisterType r → SailM Unit),
      m1 = .impure (.ok (.regRead r)) k1 ∧
      m2 = .impure (.ok (.regRead r)) k2 ∧
      eregNum r = some n ∧ (∀ v, tpar T (k1 v) (k2 v)) ∧
      l = LSilent ∧ m1' = k1 (rs1 r) ∧ ors1 = none ∧
      fn' = none ∧ d' = d ∧ oib = some (ibRd ib r) ∧ obar = none ∧ ws = [] ∧ ann = false ∧
      pstepHw cpu m2 rs2 none ib d LSilent rds ws ann (k2 (rs2 r)) none none d
        (some (ibRd ib r)) none := by
  intro htp hn hnT hst hne
  obtain ⟨r, k1, k2, rfl, rfl, hr, hk⟩ := tparStopShape T m1 m2 n htp hn hnT
  obtain ⟨-, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ :=
    regreadStepInv cpu r k1 rs1 none ib d l rds ws ann m1' ors1 fn' d' oib obar hst hne
  exact ⟨r, k1, k2, rfl, rfl, hr, hk, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    regreadStep cpu r k2 rs2 ib _⟩

/-- VALIDATION: at full agreement a run from ONE node is reproduced label for label. -/
theorem pairAfterValidation (T : List Nat) (cpu : CPU) (ls : List Wlabel) (rds : List Nat)
    (ws : List Register) (ann : Bool) (m : SailM Unit) (rs1 : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (m' : SailM Unit)
    (rs1' : RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (ib' : Ibch) (d' : Efab)
    (rs2 : RegFile) :
    phrun cpu ls rds ws ann m rs1 fn ib d m' rs1' fn' ib' d' →
    dregAgree (fun n => n ∉ T) rs1 rs2 →
    (∀ (r : Register) (n : Nat), eregNum r = some n → n ∈ T → rs1 r = rs2 r) →
    ∃ rs2' : RegFile,
      phrun cpu ls rds ws ann m rs2 fn ib d m' rs2' fn' ib' d' ∧
      dregAgree (fun _ => True) rs1' rs2' := by
  intro hrun hag hval
  have hfull : dregAgree (fun _ => True) rs1 rs2 := by
    intro r _
    cases hr : eregNum r with
    | none => exact hag r (fun n' hn' => by simp [hr] at hn')
    | some n =>
      by_cases hnT : n ∈ T
      · exact hval r n hr hnT
      · exact hag r (fun n' hn' => by
          rw [hr] at hn'
          obtain rfl := Option.some.inj hn'
          exact hnT)
  exact phrunDagree _ cpu ls rds ws ann m rs1 fn ib d m' rs1' fn' ib' d' hrun (fun _ _ => trivial)
    rs2 hfull

/-! ## 5. NON-VACUITY -/

/-! ### 5(a) THE REAL TAIL of `lw a5,0(a4)` at two loaded words, `T = [15]` -/

theorem laPairIdent (cpu : CPU) (d : Efab) (w1 w2 : BitVec 32) :
    ∃ (ls ls2 : List Wlabel) (rds : List Nat) (ws : List Register) (ann : Bool)
      (rs2' : RegFile),
      ls.length = 9 ∧
      phrun cpu ls rds ws ann (laTl w1) (ahRs laX2) none (ahIb laX2) d
        (.pure ()) (ahRs (laEnd w1)) none (ahIb (laEnd w1)) d ∧
      phrun cpu ls2 rds ws ann (laTl w2) (ahRs laX2) none (ahIb laX2) d
        (.pure ()) rs2' none (ahIb (laEnd w1)) d ∧
      ls.map lblIdent = ls2.map lblIdent ∧
      dregAgree (fun n => n ∉ [15]) (ahRs (laEnd w1)) rs2' := by
  obtain ⟨rds, ws, ann, hrun1⟩ := laPhrun cpu d w1
  have hann := phrunNoInstr cpu _ rds ws ann _ _ _ _ _ _ _ _ _ _ hrun1 (laLsNoInstr w1)
    (WeakEvProv2.laLsNoMark w1)
  have hok : rdsOk (fun n => n ∉ [15]) rds := by
    intro n hn
    apply laEndUntainted w1
    rw [phrunIbRds cpu _ rds ws ann _ _ _ _ _ _ _ _ _ _ hrun1 hann]
    exact List.mem_append_right _ hn
  obtain ⟨ls2, m2', rs2', hf2, hrun2, htp2, hag2⟩ :=
    pairIdentFull [15] cpu _ rds ws ann _ _ _ _ _ _ _ _ _ _ (laTl w2) (ahRs laX2) hrun1
      (.tpiPar _ _ (laTpar w1 w2)) hok (dregAgreeRefl _ _)
  rw [tpidBoundary [15] () m2' htp2] at hrun2
  exact ⟨_, ls2, rds, ws, ann, rs2', laLsLen w1, hrun1, hrun2, forall2ModdataIdent _ _ hf2, hag2⟩

/-! ### 5(b) A HAND-BUILT `sd a5,0(a4)` -/

def swBits : BitVec 32 := BitVec.ofNat 32 0x00f73023   -- sd a5,0(a4)

theorem swBitsRoles : depsOfIb (some swBits) = .ORstore 14 15 := by decide +kernel

theorem swBitsAsrc : depsAsrc (depsOfIb (some swBits)) = [.DReg 14] := by decide +kernel

theorem swBitsVsrc : depsVsrc (depsOfIb (some swBits)) = [.DReg 15] := by decide +kernel

def swPa : PAddr := BitVec.ofNat 64 0x80001000

theorem swPaRam : devAddr swPa = false := by decide +kernel

def swAk : AK := .AK_explicit ⟨.AV_plain, .AS_normal⟩

theorem swAkPlain : classify swAk = ⟨false, false, false⟩ := rfl

def swReq (v : BitVec 64) : Mem_write_request 8 64 Arch.pa Arch.translation Arch.arch_ak :=
  { access_kind := swAk, va := none, pa := swPa, translation := (), size := 8, value := some v,
    tag := none }

/-- The continuation after the write, the tail after the data read at data `v`, the program. -/
def swK : Result (Option Bool) Arch.abort → SailM Unit :=
  fun _ => .impure (.ok (.regWrite .PC (BitVec.ofNat 64 4))) (fun _ => .pure ())

def swTail (v : BitVec 64) : SailM Unit := .impure (.ok (.memWrite 8 64 (swReq v))) swK

def swM : SailM Unit := .impure (.ok (.regRead .x15)) swTail

/-- The channel: the announced instruction, and it after the data read. -/
def swIb : Ibch := ibAnn swBits

def swIb' : Ibch := ibRd swIb .x15

theorem swIb'Bits : swIb'.ibBits = some swBits := ibRdBits _ _

/-- The store's label at data `v`. -/
def swL (v : BitVec 64) : Wlabel :=
  LStore false (paZ swPa) (WeakInterpProj.wbytes 8 v) [.DReg 14] [.DReg 15]

/-- THE TWO TAILS ARE IDENTITY-PAIRED at any two data words, for any `T`. -/
theorem swTailTpid (T : List Nat) (v1 v2 : BitVec 64) : tpid T (swTail v1) (swTail v2) :=
  .tpiMw 8 64 _ _ swK swK rfl rfl swPaRam rfl (fun _ => tpidConv _ _)

/-- A total projection of a node: the written value. -/
def mwValue (m : SailM Unit) : Option Nat :=
  match m with
  | .impure (.ok (.memWrite _ _ rq)) _ => rq.value.map BitVec.toNat
  | _ => none

/-- … and NOT `tpar`-related when the words differ. -/
theorem swNotTpar (T : List Nat) (v1 v2 : BitVec 64) :
    tpar T (swTail v1) (swTail v2) → v1 = v2 := by
  intro htp
  have hval : ∀ v : BitVec 64, mwValue (swTail v) = some v.toNat := fun _ => rfl
  generalize e1 : swTail v1 = m1 at htp
  generalize e2 : swTail v2 = m2 at htp
  cases htp with
  | tpConv m =>
    have h := congrArg mwValue (e1.trans e2.symm)
    rw [hval, hval] at h
    exact BitVec.eq_of_toNat_eq (Option.some.inj h)
  | tpGen o k1 k2 _ _ =>
    have h : mwValue (.impure (.ok o) k1) = mwValue (.impure (.ok o) k2) := by cases o <;> rfl
    rw [← e1, ← e2, hval, hval] at h
    exact BitVec.eq_of_toNat_eq (Option.some.inj h)
  | tpWrEq r v k1 k2 _ =>
    have h := congrArg mwValue e1
    rw [hval] at h
    simp [mwValue] at h
  | tpWr r n w1 w2 k1 k2 _ _ _ =>
    have h := congrArg mwValue e1
    rw [hval] at h
    simp [mwValue] at h

/-- (Lean-only, deviation 7) the `PC` write's label: `PC` is not a carrier. -/
theorem AxPair.swPcLbl :
    erwLabel (erwOf (depsOfIb swIb'.ibBits) swIb'.ibRds .PC) = LSilent := by
  rw [swIb'Bits, swBitsRoles]
  rfl

/-- THE RUN of a tail from any register file, at the channel after the data read. -/
theorem swTailRun (cpu : CPU) (rs : RegFile) (v : BitVec 64) (d : Efab) :
    ∃ (rds : List Nat) (ws : List Register) (ann : Bool),
      phrun cpu [swL v, LSilent] rds ws ann (swTail v) rs none swIb' d
        (.pure ()) (rs.set .PC (BitVec.ofNat 64 4)) none swIb' d ∧
      rds = [] ∧ ws = [(.PC : Register)] ∧ ann = false := by
  have hst := pnodeStepStore 8 64 (swReq v) v swK rs swIb' d.efDev swPaRam rfl (by decide) rfl
  rw [swIb'Bits, swBitsAsrc, swBitsVsrc] at hst
  refine ⟨_, _, _, phrun.more (Or.inl ⟨rfl, ⟨hst, rfl⟩, rfl, rfl, rfl⟩)
    (phrun.more (Or.inl ⟨rfl, ⟨⟨AxPair.swPcLbl.symm, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, rfl, rfl,
      rfl⟩) (phrun.nil _ _ _ _ _)), rfl, rfl, rfl⟩

/-- (Lean-only, deviation 7) the program's head reads `x15`. -/
theorem AxPair.swMRds : pnodeRds swM = [15] := by
  simp [swM, pnodeRds, laRdCarrier]

theorem swStop : stopAt [15] none swM [15] :=
  ⟨rfl, [15], [], rfl, AxPair.swMRds.symm, 15, List.mem_singleton_self _,
    List.mem_singleton_self _⟩

/-- THE PAIRING, through the general machinery. -/
theorem swPair (cpu : CPU) (rs1 rs2 : RegFile) (d : Efab) :
    dregAgree (fun n => n ∉ [15]) rs1 rs2 →
    ∃ (ls1 ls2 : List Wlabel) (rds : List Nat) (ws : List Register) (ann : Bool)
      (rs1' rs2' : RegFile),
      phrun cpu ls1 rds ws ann swM rs1 none swIb d (.pure ()) rs1' none swIb' d ∧
      phrun cpu ls2 rds ws ann swM rs2 none swIb d (.pure ()) rs2' none swIb' d ∧
      List.Forall₂ lblModdata ls1 ls2 ∧
      ls1.map lblIdent = ls2.map lblIdent ∧
      dregAgree (fun n => n ∉ [15]) rs1' rs2' := by
  intro hag
  obtain ⟨rds, ws, ann, ht1, rfl, rfl, rfl⟩ := swTailRun cpu rs1 (rs1 .x15) d
  obtain ⟨ls2, m2', rs2', hf2, hrun2, htp2, hag2⟩ :=
    pairIdentFull [15] cpu _ [] [(.PC : Register)] false (swTail (rs1 .x15)) rs1 none swIb' d
      (.pure ()) _ none swIb' d (swTail (rs2 .x15)) rs2 ht1 (swTailTpid _ _ _)
      (fun _ h => by simp at h) hag
  rw [tpidBoundary [15] () m2' htp2] at hrun2
  have hf : List.Forall₂ lblModdata (LSilent :: [swL (rs1 .x15), LSilent]) (LSilent :: ls2) :=
    .cons (Or.inl rfl) hf2
  exact ⟨_, _, _, _, _, _, rs2', phrun.more (regreadStep cpu .x15 swTail rs1 swIb d) ht1,
    phrun.more (regreadStep cpu .x15 swTail rs2 swIb d) hrun2, hf,
    forall2ModdataIdent _ _ hf, hag2⟩

/-- THE TWO WORDS 0 AND 1. -/
theorem swLModdata (v1 v2 : BitVec 64) : lblModdata (swL v1) (swL v2) :=
  Or.inr (Or.inl ⟨_, _, _, _, _, _, by rw [wbytesLength, wbytesLength], rfl, rfl⟩)

def wdataZ (l : Wlabel) : Option (List Nat) := (AxPair.lblWdata l).map (List.map BitVec.toNat)

theorem swLDiffer : swL (BitVec.ofNat 64 0) ≠ swL (BitVec.ofNat 64 1) := by
  have hz : wdataZ (swL (BitVec.ofNat 64 0)) ≠ wdataZ (swL (BitVec.ofNat 64 1)) := by
    decide +kernel
  intro h
  exact hz (by rw [h])

theorem swTwoWords (cpu : CPU) (rs : RegFile) (d : Efab) :
    ∃ (ls1 ls2 : List Wlabel) (rds : List Nat) (ws : List Register) (ann : Bool)
      (rs1' rs2' : RegFile),
      phrun cpu ls1 rds ws ann swM (rs.set .x15 (BitVec.ofNat 64 0)) none swIb d
        (.pure ()) rs1' none swIb' d ∧
      phrun cpu ls2 rds ws ann swM (rs.set .x15 (BitVec.ofNat 64 1)) none swIb d
        (.pure ()) rs2' none swIb' d ∧
      List.Forall₂ lblModdata ls1 ls2 ∧
      ls1.map lblIdent = ls2.map lblIdent ∧
      ls1 ≠ ls2 := by
  obtain ⟨rds, ws, ann, ht1, rfl, rfl, rfl⟩ :=
    swTailRun cpu (rs.set .x15 (BitVec.ofNat 64 0)) (BitVec.ofNat 64 0) d
  obtain ⟨rds', ws', ann', ht2, rfl, rfl, rfl⟩ :=
    swTailRun cpu (rs.set .x15 (BitVec.ofNat 64 1)) (BitVec.ofNat 64 1) d
  have hs1 := regreadStep cpu .x15 swTail (rs.set .x15 (BitVec.ofNat 64 0)) swIb d
  have hs2 := regreadStep cpu .x15 swTail (rs.set .x15 (BitVec.ofNat 64 1)) swIb d
  rw [RegFile.set_same] at hs1 hs2
  have hf : List.Forall₂ lblModdata [LSilent, swL (BitVec.ofNat 64 0), LSilent]
      [LSilent, swL (BitVec.ofNat 64 1), LSilent] :=
    .cons (Or.inl rfl) (.cons (swLModdata _ _) (.cons (Or.inl rfl) .nil))
  refine ⟨_, _, _, _, _, _, _, phrun.more hs1 ht1, phrun.more hs2 ht2, hf,
    forall2ModdataIdent _ _ hf, ?_⟩
  intro h
  apply swLDiffer
  have h' := congrArg (fun ls : List Wlabel => ls[1]?) h
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h'
  exact h'

/-! ## 6. THE TAINTED-DATA PAIRING `tpdg` / `tpdd` -/

/-- Whether an outcome is a register write. -/
def ocWr (o : Outcome Register RegisterType) : Bool :=
  match o with
  | .regWrite _ _ => true
  | _ => false

inductive tpdg (A : Type) (T : List Nat) : SailM A → SailM A → Prop where
  /-- the same node (re-converged; the shared prefix) -/
  | tgConv (m : SailM A) : tpdg A T m m
  /-- the same non-writing outcome, continuations pointwise -/
  | tgGen (o : Outcome Register RegisterType) (k1 k2 : Outcome.ret o → SailM A) :
      ocWr o = false →
      (∀ v, tpdg A T (k1 v) (k2 v)) →
      tpdg A T (.impure (.ok o) k1) (.impure (.ok o) k2)
  /-- a register write of the same value -/
  | tgWrEq (r : Register) (v : RegisterType r) (k1 k2 : PUnit → SailM A) :
      tpdg A T (k1 PUnit.unit) (k2 PUnit.unit) →
      tpdg A T (.impure (.ok (.regWrite r v)) k1) (.impure (.ok (.regWrite r v)) k2)
  /-- a register write of different values into a tainted carrier -/
  | tgWr (r : Register) (n : Nat) (v1 v2 : RegisterType r) (k1 k2 : PUnit → SailM A) :
      eregNum r = some n → n ∈ T →
      tpdg A T (k1 PUnit.unit) (k2 PUnit.unit) →
      tpdg A T (.impure (.ok (.regWrite r v1)) k1) (.impure (.ok (.regWrite r v2)) k2)
  /-- THE DIVERGENT READ: continuations related at EVERY PAIR of values -/
  | tgRd (r : Register) (n : Nat) (k1 k2 : RegisterType r → SailM A) :
      eregNum r = some n → n ∈ T →
      (∀ v1 v2, tpdg A T (k1 v1) (k2 v2)) →
      tpdg A T (.impure (.ok (.regRead r)) k1) (.impure (.ok (.regRead r)) k2)
  /-- THE DIVERGENT WRITE: same pa and access kind, any data; NO RAM side condition -/
  | tgMw (n va : Nat) (rq1 rq2 : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k1 k2 : Result (Option Bool) Arch.abort → SailM A) :
      rq1.pa = rq2.pa → rq1.access_kind = rq2.access_kind →
      rq1.value.isSome = rq2.value.isSome →
      (∀ a, tpdg A T (k1 a) (k2 a)) →
      tpdg A T (.impure (.ok (.memWrite n va rq1)) k1) (.impure (.ok (.memWrite n va rq2)) k2)

/-- The `SailM Unit` instance -- the one the step lemma is about. -/
abbrev tpdd : List Nat → SailM Unit → SailM Unit → Prop := tpdg Unit

theorem tpddConv (T : List Nat) (m : SailM Unit) : tpdd T m m := tpdg.tgConv m

theorem pnodeWrsOcWr (o : Outcome Register RegisterType) (k : Outcome.ret o → SailM Unit) :
    pnodeWrs (.impure (.ok o) k) = [] → ocWr o = false := by
  cases o <;> simp [pnodeWrs, ocWr]

/-- `tpar ⊆ tpdd`. -/
theorem tparTpdd (T : List Nat) (m1 m2 : SailM Unit) : tpar T m1 m2 → tpdd T m1 m2 := by
  intro h
  induction h with
  | tpConv m => exact tpdg.tgConv m
  | tpGen o k1 k2 hnw _ ih => exact tpdg.tgGen o k1 k2 (pnodeWrsOcWr o k1 hnw) ih
  | tpWrEq r v k1 k2 _ ih => exact tpdg.tgWrEq r v k1 k2 ih
  | tpWr r n v1 v2 k1 k2 hn hnT _ ih => exact tpdg.tgWr r n v1 v2 k1 k2 hn hnT ih

/-- `tpid ⊆ tpdd`: `tpiMw` is `tgMw` with its RAM condition dropped. -/
theorem tpidTpdd (T : List Nat) (m1 m2 : SailM Unit) : tpid T m1 m2 → tpdd T m1 m2 := by
  intro h
  induction h with
  | tpiPar m1 m2 hpar => exact tparTpdd T m1 m2 hpar
  | tpiMw n va rq1 rq2 k1 k2 hpa hak _ hval _ ih => exact tpdg.tgMw n va rq1 rq2 k1 k2 hpa hak hval ih

/-- A LARGER taint set is a WEAKER relation. -/
theorem tpdgMono (A : Type) (T T' : List Nat) (m1 m2 : SailM A) :
    T ⊆ T' → tpdg A T m1 m2 → tpdg A T' m1 m2 := by
  intro hsub h
  induction h with
  | tgConv m => exact .tgConv m
  | tgGen o k1 k2 hnw _ ih => exact .tgGen o k1 k2 hnw ih
  | tgWrEq r v k1 k2 _ ih => exact .tgWrEq r v k1 k2 ih
  | tgWr r n v1 v2 k1 k2 hn hnT _ ih => exact .tgWr r n v1 v2 k1 k2 hn (hsub hnT) ih
  | tgRd r n k1 k2 hn hnT _ ih => exact .tgRd r n k1 k2 hn (hsub hnT) ih
  | tgMw n va rq1 rq2 k1 k2 hpa hak hval _ ih => exact .tgMw n va rq1 rq2 k1 k2 hpa hak hval ih

/-- The boundary is shared. -/
theorem tpdgBoundary (A : Type) (T : List Nat) (y : A) (m : SailM A) :
    tpdg A T (.pure y) m → m = .pure y := by
  intro h
  cases h
  rfl

/-! ## 7. ONE PAIRED STEP OVER `tpdd` -/

/-- THE READ STOP. -/
def stopRead (T : List Nat) (m1 m2 : SailM Unit) (rds : List Nat) : Prop :=
  ∃ (r : Register) (k1 k2 : RegisterType r → SailM Unit) (n : Nat),
    m1 = .impure (.ok (.regRead r)) k1 ∧
    m2 = .impure (.ok (.regRead r)) k2 ∧
    eregNum r = some n ∧ n ∈ T ∧ rds = [n] ∧
    (∀ v, tpdd T (k1 v) (k2 v))

/-- THE FABRIC STOP: a `tgMw` pair at an MMIO address. -/
def stopMmio (m1 m2 : SailM Unit) : Prop :=
  ∃ (n va : Nat) (rq1 rq2 : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k1 k2 : Result (Option Bool) Arch.abort → SailM Unit),
    m1 = .impure (.ok (.memWrite n va rq1)) k1 ∧
    m2 = .impure (.ok (.memWrite n va rq2)) k2 ∧
    rq1.pa = rq2.pa ∧ devAddr rq1.pa = true

/-- ONE NON-WRITING NODE, paired, for ANY relation `R` closed under the retry self-loop. -/
theorem pnodeStepPairR (R : SailM Unit → SailM Unit → Prop) (T : List Nat)
    (o : Outcome Register RegisterType) (k1 k2 : Outcome.ret o → SailM Unit) (rs1 rs2 : RegFile)
    (ib : Ibch) (d : DevStates) (l : Wlabel) (m1' : SailM Unit) (ors1 : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    ocWr o = false →
    rdsOk (fun n => n ∉ T) (pnodeRds (.impure (.ok o) k1)) →
    (∀ v, R (k1 v) (k2 v)) →
    (∀ (nn va : Nat) (rq : Mem_write_request nn va Arch.pa Arch.translation Arch.arch_ak)
       (k1 k2 : Result (Option Bool) Arch.abort → SailM Unit),
       (∀ v, R (k1 v) (k2 v)) →
       R (.impure (.ok (.memWrite nn va rq)) k1) (.impure (.ok (.memWrite nn va rq)) k2)) →
    dregAgree (fun n => n ∉ T) rs1 rs2 →
    pnodeStep (.impure (.ok o) k1) rs1 ib d l m1' ors1 fn' d' oib obar →
    ors1 = none ∧
    ∃ m2' : SailM Unit,
      pnodeStep (.impure (.ok o) k2) rs2 ib d l m2' none fn' d' oib obar ∧ R m1' m2' := by
  intro hw hrds hk hloop hag h
  cases o with
  | regRead r =>
    have hlk : rs1 r = rs2 r := hag r (fun n hn => pnodeRdsRead r k1 _ n hrds hn)
    obtain ⟨h1, rfl, rfl, h4, h5, h6, h7⟩ := h
    exact ⟨rfl, _, ⟨h1, rfl, rfl, h4, h5, h6, h7⟩, by rw [hlk]; exact hk _⟩
  | regWrite r v => simp [ocWr] at hw
  | memRead n va req =>
    cases hdev : devAddr req.pa
    · simp only [pnodeStep, hdev, Bool.false_eq_true, if_false] at h ⊢
      rcases h with ⟨hif, w, tvs, hlen, hb, h1, rfl, rfl, h4, h5, h6, h7⟩ |
        ⟨hif, ⟨hlat, w, tvs, hlen, hb, h1, rfl, rfl, h4, h5, h6, h7⟩ |
          ⟨hlat, w, tvs, hlen, hb, h1, rfl, rfl, h4, h5, h6, h7⟩⟩
      · exact ⟨rfl, _, Or.inl ⟨hif, w, tvs, hlen, hb, h1, rfl, trivial, h4, h5, h6, h7⟩, hk _⟩
      · exact ⟨rfl, _, Or.inr ⟨hif, Or.inl ⟨hlat, w, tvs, hlen, hb, h1, rfl, trivial, h4, h5, h6,
          h7⟩⟩, hk _⟩
      · exact ⟨rfl, _, Or.inr ⟨hif, Or.inr ⟨hlat, w, tvs, hlen, hb, h1, rfl, trivial, h4, h5, h6,
          h7⟩⟩, hk _⟩
    · simp only [pnodeStep, hdev, if_true] at h ⊢
      obtain ⟨w, h1, h2, rfl, rfl, h5, h6, h7⟩ := h
      exact ⟨rfl, _, ⟨w, h1, h2, rfl, trivial, h5, h6, h7⟩, hk _⟩
  | memWrite n va req =>
    cases hdev : devAddr req.pa <;> cases hv : req.value <;>
      simp only [pnodeStep, hdev, hv, Bool.false_eq_true, if_false, if_true] at h ⊢
    · rcases h with ⟨hn0, ⟨hlat, h1, rfl, rfl, h4, h5, h6, h7⟩ |
        ⟨hlat, ⟨h1, rfl, rfl, h4, h5, h6, h7⟩ | ⟨h1, rfl, rfl, h4, h5, h6, h7⟩⟩⟩
      · exact ⟨rfl, _, ⟨hn0, Or.inl ⟨hlat, h1, rfl, trivial, h4, h5, h6, h7⟩⟩, hk _⟩
      · exact ⟨rfl, _, ⟨hn0, Or.inr ⟨hlat, Or.inl ⟨h1, rfl, trivial, h4, h5, h6, h7⟩⟩⟩, hk _⟩
      · -- THE RETRY SELF-LOOP: the successor is the node itself
        exact ⟨rfl, _, ⟨hn0, Or.inr ⟨hlat, Or.inr ⟨h1, rfl, trivial, h4, h5, h6, h7⟩⟩⟩,
          hloop n va req k1 k2 hk⟩
    · obtain ⟨h1, h2, rfl, rfl, h5, h6, h7⟩ := h
      exact ⟨rfl, _, ⟨h1, h2, rfl, trivial, h5, h6, h7⟩, hk _⟩
  | readRam => exact h.elim
  | writeRam => exact h.elim
  | choose p =>
    obtain ⟨ch, h1, rfl, rfl, h4, h5, h6, h7⟩ := h
    exact ⟨rfl, _, ⟨ch, h1, rfl, rfl, h4, h5, h6, h7⟩, hk _⟩
  | _ =>
    obtain ⟨h1, rfl, rfl, h4, h5, h6, h7⟩ := h
    exact ⟨rfl, _, ⟨h1, rfl, rfl, h4, h5, h6, h7⟩, hk _⟩

/-- THE `tgRd` STEP, directly. -/
theorem tpddStepRd (T : List Nat) (cpu : CPU) (r : Register) (n : Nat)
    (k1 k2 : RegisterType r → SailM Unit) (rs1 rs2 : RegFile) (ib : Ibch) (d : Efab) :
    eregNum r = some n → n ∈ T →
    (∀ v1 v2, tpdd T (k1 v1) (k2 v2)) →
    pstepHw cpu (.impure (.ok (.regRead r)) k1) rs1 none ib d LSilent [n] [] false
      (k1 (rs1 r)) none none d (some (ibRd ib r)) none ∧
    pstepHw cpu (.impure (.ok (.regRead r)) k2) rs2 none ib d LSilent [n] [] false
      (k2 (rs2 r)) none none d (some (ibRd ib r)) none ∧
    tpdd T (k1 (rs1 r)) (k2 (rs2 r)) := by
  intro hn _ hk
  have hrds1 : pnodeRds (.impure (.ok (.regRead r)) k1) = [n] := by simp [pnodeRds, hn]
  have hrds2 : pnodeRds (.impure (.ok (.regRead r)) k2) = [n] := by simp [pnodeRds, hn]
  refine ⟨?_, ?_, hk _ _⟩
  · rw [← hrds1]; exact regreadStep cpu r k1 rs1 ib d
  · rw [← hrds2]; exact regreadStep cpu r k2 rs2 ib d

/-- THE PAIRED STEP: read stop, fabric stop, or paired. -/
theorem tpddStep (T : List Nat) (cpu : CPU) (m1 m2 : SailM Unit) (rs1 rs2 : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (l : Wlabel)
    (rds : List Nat) (ws : List Register) (ann : Bool) (m1' : SailM Unit)
    (ors1 : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (d' : Efab)
    (oib : Option Ibch) (obar : Option barrier_kind) :
    pstepHw cpu m1 rs1 fn ib d l rds ws ann m1' ors1 fn' d' oib obar →
    tpdd T m1 m2 →
    dregAgree (fun n => n ∉ T) rs1 rs2 →
    (fn = none ∧ stopRead T m1 m2 rds) ∨
    (fn = none ∧ l = LDev ∧ stopMmio m1 m2) ∨
    (∃ (l2 : Wlabel) (m2' : SailM Unit) (ors2 : Option RegFile),
      pstepHw cpu m2 rs2 fn ib d l2 rds ws ann m2' ors2 fn' d' oib obar ∧
      lblModdata l l2 ∧
      tpdd T m1' m2' ∧
      dregAgree (fun n => n ∉ T) (ors1.getD rs1) (ors2.getD rs2)) := by
  intro hhw htp hag
  rcases hhw with ⟨rfl, ⟨hst, hd⟩, rfl, rfl, rfl⟩ |
    ⟨pr, pw, sr, sw, rfl, ⟨hst, hd⟩, rfl, rfl, rfl⟩ | ⟨hp, rfl, rfl, rfl⟩
  · -- THE MONAD NODE
    cases htp with
    | tgConv =>
      -- RE-CONVERGED
      rcases rdsOkOrHit T (pnodeRds m1) with hok | ⟨n, hn, hnT⟩
      · obtain ⟨ors2, hst2, hag2⟩ := pnodeStepDagree _ m1 rs1 rs2 ib d.efDev l m1' ors1 fn'
          d'.efDev oib obar hok hag hst
        exact Or.inr (Or.inr ⟨l, m1', ors2, Or.inl ⟨rfl, ⟨hst2, hd⟩, rfl, rfl, rfl⟩, Or.inl rfl,
          tpdg.tgConv _, hag2⟩)
      · obtain ⟨r, k, rfl, hr, hrds⟩ := pnodeRdsShape m1 n hn
        exact Or.inl ⟨rfl, r, k, k, n, rfl, rfl, hr, hnT, hrds, fun _ => tpdg.tgConv _⟩
    | tgGen o k1 k2 hnw hk =>
      -- THE SAME NON-WRITING OUTCOME
      rcases rdsOkOrHit T (pnodeRds (.impure (.ok o) k1)) with hok | ⟨n, hn, hnT⟩
      · obtain ⟨rfl, m2', hst2, htp2⟩ := pnodeStepPairR (tpdd T) T o k1 k2 rs1 rs2 ib d.efDev l
          m1' ors1 fn' d'.efDev oib obar hnw hok hk
          (fun nn va rq k1' k2' hk' => tpdg.tgMw nn va rq rq k1' k2' rfl rfl rfl hk') hag hst
        exact Or.inr (Or.inr ⟨l, m2', none, Or.inl ⟨rfl, ⟨hst2, hd⟩,
          WeakEvProv2.pnodeRdsCongr o k1 k2, WeakEvProv2.pnodeWrsCongr o k1 k2,
          WeakEvProv2.ibnAnnCongr o k1 k2⟩, Or.inl rfl, htp2, hag⟩)
      · obtain ⟨r, k1', k2', he1, he2, hr, hk'⟩ := AxPair.genReadShape (tpdd T) o k1 k2 n hn hk
        refine Or.inl ⟨rfl, r, k1', k2', n, he1, he2, hr, hnT, ?_, hk'⟩
        rw [he1]
        simp [pnodeRds, hr]
    | tgWrEq r v k1 k2 hk =>
      -- THE SAME VALUE WRITTEN
      obtain ⟨h1, rfl, rfl, h4, h5, h6, h7⟩ := hst
      exact Or.inr (Or.inr ⟨l, k2 PUnit.unit, some (rs2.set r v),
        Or.inl ⟨rfl, ⟨⟨h1, rfl, rfl, h4, h5, h6, h7⟩, hd⟩, rfl, rfl, rfl⟩, Or.inl rfl, hk,
        dregAgreeSet _ rs1 rs2 r v hag⟩)
    | tgWr r n v1 v2 k1 k2 hn hnT hk =>
      -- DIFFERENT VALUES INTO A TAINTED CARRIER
      obtain ⟨h1, rfl, rfl, h4, h5, h6, h7⟩ := hst
      exact Or.inr (Or.inr ⟨l, k2 PUnit.unit, some (rs2.set r v2),
        Or.inl ⟨rfl, ⟨⟨h1, rfl, rfl, h4, h5, h6, h7⟩, hd⟩, rfl, rfl, rfl⟩, Or.inl rfl, hk,
        dregAgreeExcl2 _ rs1 rs2 r v1 v2 ⟨n, hn, fun hno => hno hnT⟩ hag⟩)
    | tgRd r n k1 k2 hn hnT hk =>
      -- THE DIVERGENT READ
      obtain ⟨h1, rfl, rfl, h4, h5, h6, h7⟩ := hst
      exact Or.inr (Or.inr ⟨l, k2 (rs2 r), none,
        Or.inl ⟨rfl, ⟨⟨h1, rfl, rfl, h4, h5, h6, h7⟩, hd⟩,
          WeakEvProv2.pnodeRdsCongr (.regRead r) k1 k2, rfl, rfl⟩, Or.inl rfl, hk _ _, hag⟩)
    | tgMw n va rq1 rq2 k1 k2 hpa hak hval hk =>
      -- THE DIVERGENT WRITE
      cases hdev : devAddr rq1.pa
      · obtain ⟨rfl, l2, m2', hst2, hmod, htp2⟩ := AxPair.mwStepPairR (tpdd T) n va rq1 rq2 k1 k2
          rs1 rs2 ib d.efDev l m1' ors1 fn' d'.efDev oib obar hpa hak hdev hval hk
          (tpdg.tgMw n va rq1 rq2 k1 k2 hpa hak hval hk) hst
        exact Or.inr (Or.inr ⟨l2, m2', none, Or.inl ⟨rfl, ⟨hst2, hd⟩, rfl, rfl, rfl⟩, hmod, htp2,
          hag⟩)
      · -- MMIO: the fabric stop
        refine Or.inr (Or.inl ⟨rfl, ?_, n, va, rq1, rq2, k1, k2, rfl, rfl, hpa, hdev⟩)
        cases hv : rq1.value with
        | none => simp only [pnodeStep, hdev, hv, if_true] at hst
        | some v =>
          simp only [pnodeStep, hdev, hv, if_true] at hst
          exact hst.2.1
  · -- THE PARKED FENCE: the node does not move
    obtain ⟨h1, rfl, rfl, h4, h5, h6, h7⟩ := hst
    exact Or.inr (Or.inr ⟨l, m2, none,
      Or.inr (Or.inl ⟨pr, pw, sr, sw, rfl, ⟨⟨h1, rfl, rfl, h4, h5, h6, h7⟩, hd⟩, rfl, rfl, rfl⟩),
      Or.inl rfl, htp, hag⟩)
  · -- THE PLIC WIRE: the node does not move, the same pin is written
    obtain ⟨mm, b, k, hk, h1, rfl, h3, h4, h5, h6, rfl⟩ := hp
    refine Or.inr (Or.inr ⟨l, m2, some (pinSet rs2 mm b),
      Or.inr (Or.inr ⟨⟨mm, b, k, hk, h1, rfl, h3, h4, h5, h6, rfl⟩, rfl, rfl, rfl⟩), Or.inl rfl,
      htp, ?_⟩)
    cases mm
    · exact dregAgreeSet _ rs1 rs2 _ _ hag
    · exact dregAgreeSet _ rs1 rs2 _ _ hag

/-! ## 8. THE IDENTITY-STOP LEMMA OVER `tpdd`, AND THE VALIDATION FORMS -/

/-- THE IDENTITY-STOP LEMMA, DATA-TOLERANT. -/
theorem pairIdentDd (T : List Nat) (cpu : CPU) (ls : List Wlabel) (rds : List Nat)
    (ws : List Register) (ann : Bool) (m1 : SailM Unit) (rs1 : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (m1' : SailM Unit)
    (rs1' : RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (ib' : Ibch) (d' : Efab)
    (m2 : SailM Unit) (rs2 : RegFile) :
    phrun cpu ls rds ws ann m1 rs1 fn ib d m1' rs1' fn' ib' d' →
    tpdd T m1 m2 →
    dregAgree (fun n => n ∉ T) rs1 rs2 →
    ∃ (lsa lsb : List Wlabel) (rdsa rdsb : List Nat) (wsa wsb : List Register)
      (anna annb : Bool) (ma : SailM Unit) (rsa : RegFile)
      (fna : Option (Bool × Bool × Bool × Bool)) (iba : Ibch) (da : Efab)
      (ls2 : List Wlabel) (m2a : SailM Unit) (rs2a : RegFile),
      ls = lsa ++ lsb ∧ rds = rdsa ++ rdsb ∧ ws = wsa ++ wsb ∧ ann = (anna || annb) ∧
      phrun cpu lsa rdsa wsa anna m1 rs1 fn ib d ma rsa fna iba da ∧
      phrun cpu lsb rdsb wsb annb ma rsa fna iba da m1' rs1' fn' ib' d' ∧
      List.Forall₂ lblModdata lsa ls2 ∧
      phrun cpu ls2 rdsa wsa anna m2 rs2 fn ib d m2a rs2a fna iba da ∧
      tpdd T ma m2a ∧
      dregAgree (fun n => n ∉ T) rsa rs2a ∧
      (lsb = [] ∨
       (fna = none ∧ ∃ rdsh rdsr, rdsb = rdsh ++ rdsr ∧ stopRead T ma m2a rdsh) ∨
       (fna = none ∧ ∃ lsr, lsb = LDev :: lsr ∧ stopMmio ma m2a)) := by
  intro hrun
  induction hrun generalizing m2 rs2 with
  | nil m rs fn ib d =>
    intro htp hag
    exact ⟨[], [], [], [], [], [], false, false, m, rs, fn, ib, d, [], m2, rs2, rfl, rfl, rfl, rfl,
      phrun.nil _ _ _ _ _, phrun.nil _ _ _ _ _, List.Forall₂.nil, phrun.nil _ _ _ _ _, htp, hag,
      Or.inl rfl⟩
  | @more l ls rds rds' ws ws' ann ann' m rs fn ib d ma ors fn1 oib obar d1 mb rsb fn2 ib2 d2
      hstep hrun' ih =>
    intro htp hag
    rcases tpddStep T cpu m m2 rs rs2 fn ib d l rds ws ann ma ors fn1 d1 oib obar hstep htp hag with
      ⟨rfl, hstop⟩ | ⟨rfl, rfl, hstop⟩ | ⟨l2, mb1, orsb, hstepb, hmod, htp1, hagb⟩
    · -- THE READ STOP: split here, the prefix is empty
      exact ⟨[], l :: ls, [], rds ++ rds', [], ws ++ ws', false, ann || ann', m, rs, none, ib, d,
        [], m2, rs2, rfl, rfl, rfl, by simp, phrun.nil _ _ _ _ _, phrun.more hstep hrun',
        List.Forall₂.nil, phrun.nil _ _ _ _ _, htp, hag, Or.inr (Or.inl ⟨rfl, rds, rds', rfl, hstop⟩)⟩
    · -- THE FABRIC STOP
      exact ⟨[], LDev :: ls, [], rds ++ rds', [], ws ++ ws', false, ann || ann', m, rs, none, ib,
        d, [], m2, rs2, rfl, rfl, rfl, by simp, phrun.nil _ _ _ _ _, phrun.more hstep hrun',
        List.Forall₂.nil, phrun.nil _ _ _ _ _, htp, hag, Or.inr (Or.inr ⟨rfl, ls, rfl, hstop⟩)⟩
    · -- PAIRED: one more step on the prefix
      obtain ⟨lsa, lsb, rdsa, rdsb, wsa, wsb, anna, annb, ma', rsa, fna, iba, da, ls2, m2b, rs2b,
        rfl, rfl, rfl, rfl, hruna, hrunb, hf2, hrun2, htpa, haga, hstop⟩ :=
        ih mb1 (orsb.getD rs2) htp1 hagb
      exact ⟨l :: lsa, lsb, rds ++ rdsa, rdsb, ws ++ wsa, wsb, ann || anna, annb, ma', rsa, fna,
        iba, da, l2 :: ls2, m2b, rs2b, rfl, (List.append_assoc _ _ _).symm,
        (List.append_assoc _ _ _).symm, (Bool.or_assoc _ _ _).symm, phrun.more hstep hruna, hrunb,
        List.Forall₂.cons hmod hf2, phrun.more hstepb hrun2, htpa, haga, hstop⟩

/-- NO STOP ⇒ PAIRED TO THE END. -/
theorem pairIdentDdFull (T : List Nat) (cpu : CPU) (ls : List Wlabel) (rds : List Nat)
    (ws : List Register) (ann : Bool) (m1 : SailM Unit) (rs1 : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (m1' : SailM Unit)
    (rs1' : RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (ib' : Ibch) (d' : Efab)
    (m2 : SailM Unit) (rs2 : RegFile) :
    phrun cpu ls rds ws ann m1 rs1 fn ib d m1' rs1' fn' ib' d' →
    tpdd T m1 m2 →
    rdsOk (fun n => n ∉ T) rds →
    LDev ∉ ls →
    dregAgree (fun n => n ∉ T) rs1 rs2 →
    ∃ (ls2 : List Wlabel) (m2' : SailM Unit) (rs2' : RegFile),
      List.Forall₂ lblModdata ls ls2 ∧
      phrun cpu ls2 rds ws ann m2 rs2 fn ib d m2' rs2' fn' ib' d' ∧
      tpdd T m1' m2' ∧ dregAgree (fun n => n ∉ T) rs1' rs2' := by
  intro hrun htp hok hdev hag
  obtain ⟨lsa, lsb, rdsa, rdsb, wsa, wsb, anna, annb, ma, rsa, fna, iba, da, ls2, m2a, rs2a,
    rfl, rfl, rfl, rfl, hruna, hrunb, hf2, hrun2, htpa, haga, hstop⟩ :=
    pairIdentDd T cpu ls rds ws ann m1 rs1 fn ib d m1' rs1' fn' ib' d' m2 rs2 hrun htp hag
  rcases hstop with rfl | ⟨-, rdsh, rdsr, rfl, r, k1, k2, n, -, -, -, hnT, rfl, -⟩ |
    ⟨-, lsr, rfl, -⟩
  · cases hrunb
    simp only [List.append_nil, Bool.or_false]
    exact ⟨ls2, m2a, rs2a, hf2, hrun2, htpa, haga⟩
  · exact absurd hnT
      (hok n (List.mem_append_right _ (List.mem_append_left _ (List.mem_singleton_self _))))
  · exact absurd (List.mem_append_right _ List.mem_cons_self) hdev

/-- THE RESUME PROTOCOL AT A READ STOP (deviation 4: also `obar = none`). -/
theorem pairResumeDd (T : List Nat) (cpu : CPU) (m1 m2 : SailM Unit) (rs1 rs2 : RegFile)
    (ib : Ibch) (d : Efab) (l : Wlabel) (rds : List Nat) (ws : List Register) (ann : Bool)
    (m1' : SailM Unit) (ors1 : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : Efab) (oib : Option Ibch) (obar : Option barrier_kind) :
    stopRead T m1 m2 rds →
    pstepHw cpu m1 rs1 none ib d l rds ws ann m1' ors1 fn' d' oib obar →
    ∃ (r : Register) (k1 k2 : RegisterType r → SailM Unit) (n : Nat),
      m1 = .impure (.ok (.regRead r)) k1 ∧
      m2 = .impure (.ok (.regRead r)) k2 ∧
      eregNum r = some n ∧ n ∈ T ∧ rds = [n] ∧ (∀ v, tpdd T (k1 v) (k2 v)) ∧
      l = LSilent ∧ m1' = k1 (rs1 r) ∧ ors1 = none ∧
      fn' = none ∧ d' = d ∧ oib = some (ibRd ib r) ∧ obar = none ∧ ws = [] ∧ ann = false ∧
      pstepHw cpu m2 rs2 none ib d LSilent rds ws ann (k2 (rs2 r)) none none d
        (some (ibRd ib r)) none := by
  rintro ⟨r, k1, k2, n, rfl, rfl, hr, hnT, rfl, hk⟩ hst
  obtain ⟨-, rfl, rfl, rfl, rfl, rfl, rfl, rfl, -, rfl, rfl⟩ :=
    regreadStepInv cpu r k1 rs1 none ib d l [n] ws ann m1' ors1 fn' d' oib obar hst (by simp)
  have hrds2 : pnodeRds (.impure (.ok (.regRead r)) k2) = [n] := by simp [pnodeRds, hr]
  refine ⟨r, k1, k2, n, rfl, rfl, hr, hnT, rfl, hk, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ?_⟩
  rw [← hrds2]
  exact regreadStep cpu r k2 rs2 ib _

/-- VALIDATION, PER STRETCH. -/
theorem pairDataValidated (T : List Nat) (cpu : CPU) (ls : List Wlabel) (rds : List Nat)
    (ws : List Register) (ann : Bool) (m : SailM Unit) (rs1 : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (m' : SailM Unit)
    (rs1' : RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (ib' : Ibch) (d' : Efab)
    (rs2 : RegFile) :
    phrun cpu ls rds ws ann m rs1 fn ib d m' rs1' fn' ib' d' →
    dregAgree (fun n => n ∉ T) rs1 rs2 →
    (∀ (r : Register) (n : Nat), eregNum r = some n → n ∈ T → n ∈ rds → rs1 r = rs2 r) →
    ∃ rs2' : RegFile,
      phrun cpu ls rds ws ann m rs2 fn ib d m' rs2' fn' ib' d' ∧
      dregAgree (fun n => n ∉ T ∨ n ∈ rds) rs1' rs2' := by
  intro hrun hag hval
  have hag' : dregAgree (fun n => n ∉ T ∨ n ∈ rds) rs1 rs2 := by
    intro r hr
    cases hn : eregNum r with
    | none => exact hag r (fun n' hn' => by simp [hn] at hn')
    | some n =>
      have hnot : n ∉ T → rs1 r = rs2 r := fun hnT => hag r (fun n' hn' => by
        rw [hn] at hn'
        obtain rfl := Option.some.inj hn'
        exact hnT)
      rcases hr n hn with hnT | hin
      · exact hnot hnT
      · by_cases hnT : n ∈ T
        · exact hval r n hn hnT hin
        · exact hnot hnT
  exact phrunDagree _ cpu ls rds ws ann m rs1 fn ib d m' rs1' fn' ib' d' hrun
    (fun _ hn => Or.inr hn) rs2 hag'

/-- … AT ONE EVENT. -/
theorem pairEventValidated (T : List Nat) (cpu : CPU) (ls0 : List Wlabel) (l : Wlabel)
    (rds : List Nat) (ws : List Register) (ann : Bool) (m : SailM Unit) (rs1 : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (m' : SailM Unit)
    (rs1' : RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (ib' : Ibch) (d' : Efab)
    (rs2 : RegFile) :
    phrun cpu (ls0 ++ [l]) rds ws ann m rs1 fn ib d m' rs1' fn' ib' d' →
    dregAgree (fun n => n ∉ T) rs1 rs2 →
    (∀ (r : Register) (n : Nat), eregNum r = some n → n ∈ T → n ∈ rds → rs1 r = rs2 r) →
    ∃ rs2' : RegFile,
      phrun cpu (ls0 ++ [l]) rds ws ann m rs2 fn ib d m' rs2' fn' ib' d' ∧
      AxPair.lblWdata l = AxPair.lblWdata l := by
  intro hrun hag hval
  obtain ⟨rs2', hrun2, -⟩ :=
    pairDataValidated T cpu (ls0 ++ [l]) rds ws ann m rs1 fn ib d m' rs1' fn' ib' d' rs2 hrun hag
      hval
  exact ⟨rs2', hrun2, rfl⟩

/-- The taint set may be SHRUNK to what a stretch reads. -/
theorem tpddShrink (T rds : List Nat) (m1 m2 : SailM Unit) :
    tpdd (T.filter (fun n => decide (n ∈ rds))) m1 m2 → tpdd T m1 m2 :=
  tpdgMono Unit _ T m1 m2 (fun _ hn => (List.mem_filter.1 hn).1)

/-! ## 9. NON-VACUITY OF `tpdd`: THE HAND-BUILT `sd a5,0(a4)` THROUGH ITS DIVERGENT DATA READ -/

theorem swTailTpdd (T : List Nat) (v1 v2 : BitVec 64) : tpdd T (swTail v1) (swTail v2) :=
  tpdg.tgMw 8 64 _ _ swK swK rfl rfl rfl (fun _ => tpdg.tgConv _)

theorem swMTpdd : tpdd [15] swM swM :=
  tpdg.tgRd .x15 15 swTail swTail laRdCarrier (List.mem_singleton_self _)
    (fun v1 v2 => swTailTpdd _ v1 v2)

theorem swPairDd (cpu : CPU) (rs1 rs2 : RegFile) (d : Efab) :
    dregAgree (fun n => n ∉ [15]) rs1 rs2 →
    ∃ (ls1 ls2 : List Wlabel) (rds : List Nat) (ws : List Register) (ann : Bool)
      (rs1' rs2' : RegFile),
      phrun cpu ls1 rds ws ann swM rs1 none swIb d (.pure ()) rs1' none swIb' d ∧
      phrun cpu ls2 rds ws ann swM rs2 none swIb d (.pure ()) rs2' none swIb' d ∧
      List.Forall₂ lblModdata ls1 ls2 ∧
      ls1.map lblIdent = ls2.map lblIdent ∧
      dregAgree (fun n => n ∉ [15]) rs1' rs2' := by
  intro hag
  obtain ⟨hs1, hs2, -⟩ := tpddStepRd [15] cpu .x15 15 swTail swTail rs1 rs2 swIb d laRdCarrier
    (List.mem_singleton_self _) (fun v1 v2 => swTailTpdd _ v1 v2)
  obtain ⟨rds, ws, ann, ht1, rfl, rfl, rfl⟩ := swTailRun cpu rs1 (rs1 .x15) d
  obtain ⟨ls2, m2', rs2', hf2, hrun2, htp2, hag2⟩ :=
    pairIdentDdFull [15] cpu _ [] [(.PC : Register)] false (swTail (rs1 .x15)) rs1 none swIb' d
      (.pure ()) _ none swIb' d (swTail (rs2 .x15)) rs2 ht1 (swTailTpdd _ _ _)
      (fun _ h => by simp at h) (by simp [swL]) hag
  rw [tpdgBoundary _ _ () m2' htp2] at hrun2
  have hf : List.Forall₂ lblModdata (LSilent :: [swL (rs1 .x15), LSilent]) (LSilent :: ls2) :=
    .cons (Or.inl rfl) hf2
  exact ⟨_, _, _, _, _, _, rs2', phrun.more hs1 ht1, phrun.more hs2 hrun2, hf,
    forall2ModdataIdent _ _ hf, hag2⟩

end Weak
