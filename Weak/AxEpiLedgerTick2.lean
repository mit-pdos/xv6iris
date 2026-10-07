/-
Weak: **the concrete `c.ldsp` ledgers after the `c.sdsp` handoff, and the `c.ldsp` `wpd` for
BOTH tick bits** — the kernel-heavy second half of `Weak.AxEpiLedgerTick` (split for build time:
the two files together type-check about 290 s of kernel work).

Rocq: `iris/AxEpiLedgerTick.v` @ xxvzwolszwmp (its `text_ld_obs`, `t_after_sd_text`,
`epi_ledger_cldsp_after_sd`, `epi_ledger_cldsp_tick` and §5).  Header, deviations and the
name map: `Weak.AxEpiLedgerTick`.  In substance: at every `tAfterSd v' v` the text still holds
`0x60a2` at `pcLd` (`tAfterSdText`); the tick = false load ledger (`epiLedgerCldspAfterSd`,
`AxEpiLedger`'s boolean twins) and the tick = true ledger (`epiLedgerCldspTick`, the
`AxEpiLedgerTick.*B` twins) hold there, closed by the kernel with the loaded word free
(`ax_epi_ledger_krfl`); §5 `wpdCldspAfterSd` composes them for either tick bit.  The §5 lemmas
quantify both boundary answers `v' v` of the store (two-pin boundary) and drop Rocq's `Hflow`,
`Hloc`, `Hntext` (Stage C; `AxEpiLedgerTick` deviations 1 and 3).
-/
import Weak.AxEpiLedgerTick

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! # The concrete ledgers at `tAfterSd v' v` -/

def textLdObs (t : ExecSt) : Option Nat :=
  (bmRead t.mem (AxEpiProbe.w64 pcLd) 2).map BitVec.toNat

theorem tAfterSdText (v' v : BitVec 1) : textLdObs (tAfterSd v' v) = some 0x60a2 := by
  rcases bv1Cases v' with rfl | rfl <;> rcases bv1Cases v with rfl | rfl <;> decide +kernel

theorem epiLedgerCldspAfterSd (v' v : BitVec 1) :
    AxLdModelFacts (tAfterSd v' v) AxEpiProbe.drNopin DwAll DPost (pcLd : Int)
      AxEpiLedger.ldVs ldAddr ldPost := by
  rcases bv1Cases v' with rfl | rfl <;> rcases bv1Cases v with rfl | rfl <;>
  exact {
    lgSeipDr := by decide +kernel
    lgMeipDr := by decide +kernel
    lgSeipD := by decide +kernel
    lgMeipD := by decide +kernel
    lgHead := by decide +kernel
    lgToSeip := by decide +kernel
    lgBranch00 := AxEpiLedger.ldBranchAtOfB _ _ _ _ _ _ AxEpiLedger.ldPostB _
      AxEpiLedger.ldPostOfB _ _ _ (by intro x; ax_epi_ledger_krfl)
    lgBranch01 := AxEpiLedger.ldBranchAtOfB _ _ _ _ _ _ AxEpiLedger.ldPostB _
      AxEpiLedger.ldPostOfB _ _ _ (by intro x; ax_epi_ledger_krfl)
    lgBranch10 := AxEpiLedger.ldBranchAtOfB _ _ _ _ _ _ AxEpiLedger.ldPostB _
      AxEpiLedger.ldPostOfB _ _ _ (by intro x; ax_epi_ledger_krfl)
    lgBranch11 := AxEpiLedger.ldBranchAtOfB _ _ _ _ _ _ AxEpiLedger.ldPostB _
      AxEpiLedger.ldPostOfB _ _ _ (by intro x; ax_epi_ledger_krfl) }


theorem epiLedgerCldspTick (v' v : BitVec 1) :
    AxLdTickFacts (tAfterSd v' v) AxEpiProbe.drNopin DwAll DPost (pcLd : Int)
      AxEpiLedger.ldVs ldAddr ldPost := by
  rcases bv1Cases v' with rfl | rfl <;> rcases bv1Cases v with rfl | rfl <;>
  exact {
    ltSeipDr := by decide +kernel
    ltMeipDr := by decide +kernel
    ltSeipD := by decide +kernel
    ltMeipD := by decide +kernel
    ltToSeip := by decide +kernel
    ltBranch00 := AxEpiLedgerTick.ldtBranchAtOfB _ _ _ _ _ _ AxEpiLedger.ldPostB _
      AxEpiLedger.ldPostOfB _ _ _ (by intro x; ax_epi_ledger_krfl)
    ltBranch01 := AxEpiLedgerTick.ldtBranchAtOfB _ _ _ _ _ _ AxEpiLedger.ldPostB _
      AxEpiLedger.ldPostOfB _ _ _ (by intro x; ax_epi_ledger_krfl)
    ltBranch10 := AxEpiLedgerTick.ldtBranchAtOfB _ _ _ _ _ _ AxEpiLedger.ldPostB _
      AxEpiLedger.ldPostOfB _ _ _ (by intro x; ax_epi_ledger_krfl)
    ltBranch11 := AxEpiLedgerTick.ldtBranchAtOfB _ _ _ _ _ _ AxEpiLedger.ldPostB _
      AxEpiLedger.ldPostOfB _ _ _ (by intro x; ax_epi_ledger_krfl) }


/-! # 5. The concrete c.ldsp right after the c.sdsp, for both ticks -/

/-- The reachable row-end set, per tick. -/
noncomputable def ldAfterSdInv (tick : Bool) (v' v : BitVec 1) (cpu : CPU) (kk : Nat)
    (s1 : Athread) : Prop :=
  if tick then ledgerLdtInv (tAfterSd v' v) AxEpiProbe.drNopin DwAll DPost AxEpiLedger.ldVs cpu kk s1
  else ledgerLdInv (tAfterSd v' v) AxEpiProbe.drNopin DwAll DPost AxEpiLedger.ldVs cpu kk s1

theorem ldAfterSdInvReachesRet (tick : Bool) (v' v : BitVec 1) (cpu : CPU) (kk : Nat)
    (s1 : Athread) :
    ldAfterSdInv tick v' v cpu kk s1 →
    ∃ t0 s', aeqv s1 t0 ∧ rtc (ldStep cpu AxEpiLedger.ldVs) t0 s' ∧
      RetLd cpu ldPost (kk + 1) s' := by
  cases tick <;> intro H
  · exact ledgerLdInvReachesRet _ _ _ _ _ _ _ _ _ _ _ (epiLedgerCldspAfterSd v' v) H
  · exact ledgerLdtInvReachesRet _ _ _ _ _ _ _ _ _ _ _ (epiLedgerCldspTick v' v) H

section ldAfterSd
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem wpdCldspAfterSdFalse (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch)
    (kk : Nat) (v' v : BitVec 1) (Rv : Gdexec → List (BitVec 8) → IProp GF)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢
        ⌜AxCjrWpd.fetchImgOk GD i kk (pcLd : Int) AxEpiLedger.ldVs⌝)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i kk⌝)
    (rs : RegFile) (Hag : regsAgree AxRunClose.pinReg (tAfterSd v' v).regs rs) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (w : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i kk ls -∗
         ⌜graphValue GD (i, kk) = some w⌝ -∗ loadFlow GD i kk (Rv GD w)) -∗
      ((∀ s', ⌜RetLd cpu ldPost (kk + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜ledgerLdInv (tAfterSd v' v) AxEpiProbe.drNopin DwAll DPost AxEpiLedger.ldVs cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) rs none ib, kk⟩ Φ :=
  wpdCldspStepOfLedgerAgree i Φ cpu ib kk (tAfterSd v' v) _ _ _ _ _ _ _ Rv
    (epiLedgerCldspAfterSd v' v) Hgd Hrow rs Hag

theorem wpdCldspAfterSdTrue (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch)
    (kk : Nat) (v' v : BitVec 1) (Rv : Gdexec → List (BitVec 8) → IProp GF)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢
        ⌜AxCjrWpd.fetchImgOk GD i kk (pcLd : Int) AxEpiLedger.ldVs⌝)
    (Hrow : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i kk⌝)
    (rs : RegFile) (Hag : regsAgree AxRunClose.pinReg (tAfterSd v' v).regs rs) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (w : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i kk ls -∗
         ⌜graphValue GD (i, kk) = some w⌝ -∗ loadFlow GD i kk (Rv GD w)) -∗
      ((∀ s', ⌜RetLd cpu ldPost (kk + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜ledgerLdtInv (tAfterSd v' v) AxEpiProbe.drNopin DwAll DPost AxEpiLedger.ldVs cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep true) rs none ib, kk⟩ Φ :=
  wpdCldspStepOfLedgerTick i Φ cpu ib kk (tAfterSd v' v) _ _ _ _ _ _ _ Rv
    (epiLedgerCldspTick v' v) Hgd Hrow rs Hag

/-- BOTH TICKS: after the c.sdsp's `.pure ()` (registers `tAfterSd v' v`, up to the pins), the
next program `riscvStep tick` has a whole-instruction `wpd` for either tick bit. -/
theorem wpdCldspAfterSd (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch)
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
      ((∀ s', ⌜RetLd cpu ldPost (kk + 1) s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1, ⌜ldAfterSdInv tick v' v cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep tick) rs none ib, kk⟩ Φ := by
  cases tick
  · exact wpdCldspAfterSdFalse i Φ cpu ib kk v' v Rv Hgd Hrow rs Hag
  · exact wpdCldspAfterSdTrue i Φ cpu ib kk v' v Rv Hgd Hrow rs Hag

end ldAfterSd

end Weak
