/-
Weak: **W10-4 [OWN.94] (N2′), increment 4 — the exclusive pair under taint** (`PROGRESS-W10N2p.md`).
Lean-only, no Rocq twin.

The AMO (xv6's `amoswap.w.aq` acquire, `amoswap.w` release) is an `LExLoad`/`LExStore` pair block
(`GraphFetchBlocks.blkPair`).  Under taint it is mirrored piece by piece (`CertZ11.stepMirror` for the
two exclusive steps, `phrunDagree` for the `LInstr`-free star between them), the exclusive read
re-answered by the latest bytes, which must AGREE in value (an RMW has no poisoned arm:
`lblReidxW` keeps an RMW's read values):

  **`CertZ12.pairT`** — from `clockstep`-related nodes, the pair's certified run with the machine label,
  `clockstep` after it (the write verbatim).

Spec: FAITHFUL.  Lean-only helpers file-qualified (`CertZ12.*`).
-/
import Weak.CertZ11

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Wlabel

local notation "Ofence" => Option (Bool × Bool × Bool × Bool)

/-- The pair's star between its exclusive steps reads no tainted register. -/
def CertZ12.runUntainted (T : List Nat) (cpu : CPU) (ls : List Wlabel) (m : SailM Unit)
    (rs : RegFile) (fn : Ofence) (ib : Ibch) (d : Efab) (m' : SailM Unit) (rs' : RegFile)
    (fn' : Ofence) (ib' : Ibch) (d' : Efab) : Prop :=
  ∀ rds wrs ann, phrun cpu ls rds wrs ann m rs fn ib d m' rs' fn' ib' d' →
    rdsOk (fun n => n ∉ T) rds

/-- **`CertZ12.pairT` — THE EXCLUSIVE PAIR UNDER TAINT.** -/
theorem CertZ12.pairT (c : Cand) (T : List Nat) (cpu : CPU) (ma : SailM Unit)
    (rsa rsa2 : RegFile) (fna : Ofence) (iba : Ibch) (da : Efab) (ws ws' : Wstate) (lb : Lbl)
    (l1 l2 : Wlabel) (pm : Pexv6) (dm : Efab) (ls2 : List Wlabel) (pm2 : Pexv6) (dm2 : Efab)
    (pE' : Pexv6) (d' : Efab) :
    ws'.wRelp = ws.wRelp →
    hlblRealizesPair (.PHart cpu ma rsa fna iba) pm2 ws lb l1 l2 →
    pstepEv (.PHart cpu ma rsa fna iba) da l1 pm dm →
    admRunG pstepEv false pm dm ls2 pm2 dm2 →
    pstepEv pm2 dm2 l2 pE' d' →
    (∀ mm rsm fnm ibm, pm = .PHart cpu mm rsm fnm ibm →
      CertZ11.stepUntainted T cpu l1 ma rsa fna iba da mm rsm fnm ibm dm) →
    (∀ mm rsm fnm ibm mm2 rsm2 fnm2 ibm2, pm = .PHart cpu mm rsm fnm ibm →
      pm2 = .PHart cpu mm2 rsm2 fnm2 ibm2 →
      CertZ12.runUntainted T cpu ls2 mm rsm fnm ibm dm mm2 rsm2 fnm2 ibm2 dm2) →
    (∀ mm2 rsm2 fnm2 ibm2 m' rs' fn' ib', pm2 = .PHart cpu mm2 rsm2 fnm2 ibm2 →
      pE' = .PHart cpu m' rs' fn' ib' →
      CertZ11.stepUntainted T cpu l2 mm2 rsm2 fnm2 ibm2 dm2 m' rs' fn' ib' d') →
    dregAgree (fun n => n ∉ T) rsa rsa2 →
    (∀ aq rl base ts rvs wvs kc, lb = .LRmw aq rl base ts rvs wvs kc →
      lrdVs c base ts.length = rvs) →
    ∃ (l1' : Wlabel) (pmC : Pexv6) (pm2C : Pexv6) (m' : SailM Unit) (rs' rs2' : RegFile)
      (fn' : Ofence) (ib' : Ibch),
      pE' = .PHart cpu m' rs' fn' ib' ∧
      hlblRealizesPair (.PHart cpu ma rsa2 fna iba) pm2C ws' (CertZ4.machLbl c lb) l1' l2 ∧
      pstepEv (.PHart cpu ma rsa2 fna iba) da l1' pmC dm ∧
      admRunG pstepEv false pmC dm ls2 pm2C dm2 ∧
      pstepEv pm2C dm2 l2 (.PHart cpu m' rs2' fn' ib') d' ∧
      dregAgree (fun n => n ∉ T) rs' rs2' := by
  intro hr hpair hst1 hrun2 hst2 hu1 hu2 hu3 hag hval
  obtain ⟨mm, rsm, fnm, ibm, rfl⟩ := pstepEvPhart cpu ma rsa fna iba da l1 pm dm hst1
  obtain ⟨mm2, rsm2, fnm2, ibm2, rfl⟩ :=
    admRunPhart false _ _ dm ls2 dm2 (CertZ10.admRunOfG false _ dm ls2 _ dm2 hrun2) cpu mm rsm fnm
      ibm rfl
  obtain ⟨m', rs', fn', ib', rfl⟩ := pstepEvPhart cpu mm2 rsm2 fnm2 ibm2 dm2 l2 pE' d' hst2
  -- the three pieces, mirrored
  obtain ⟨rsmC, hst1C, hag1⟩ := CertZ11.stepMirror T cpu l1 ma rsa rsa2 fna iba da mm rsm fnm ibm dm
    hst1 (hu1 mm rsm fnm ibm rfl) hag
  obtain ⟨rds2, wrs2, ann2, hrunP⟩ := pevrunPhrun ls2 _ dm _ dm2
    (admRunPevrun false _ dm ls2 _ dm2 (CertZ10.admRunOfG false _ dm ls2 _ dm2 hrun2)) cpu mm rsm
    fnm ibm mm2 rsm2 fnm2 ibm2 rfl rfl
  obtain ⟨rsm2C, hrunPC, hag2⟩ := phrunDagree _ cpu ls2 rds2 wrs2 ann2 mm rsm fnm ibm dm mm2 rsm2
    fnm2 ibm2 dm2 hrunP (hu2 mm rsm fnm ibm mm2 rsm2 fnm2 ibm2 rfl rfl _ _ _ hrunP) rsmC hag1
  obtain ⟨rs2', hst2C, hag3⟩ := CertZ11.stepMirror T cpu l2 mm2 rsm2 rsm2C fnm2 ibm2 dm2 m' rs' fn'
    ib' d' hst2 (hu3 mm2 rsm2 fnm2 ibm2 m' rs' fn' ib' rfl rfl) hag2
  have hadm2 : ∀ l0, l0 ∈ ls2 → lbAdmin false l0 :=
    admRunAdmin false _ dm ls2 _ dm2 (CertZ10.admRunOfG false _ dm ls2 _ dm2 hrun2)
  -- the realization at the certified states, re-answered
  have hpairC := hlblRealizesPairRs cpu ma rsa rsa2 fna fna iba iba cpu mm2 rsm2 rsm2C fnm2 fnm2
    ibm2 ibm2 ws lb l1 l2 hpair
  obtain ⟨l1', hpair', hstT⟩ := CertZ5.pairRet c _ _ ws ws' lb l1 l2 hr hpairC hval
  exact ⟨l1', _, _, m', rs', rs2', fn', ib', rfl, hpair', hstT da _ dm hst1C,
    CertZ10.admRunGOf false _ dm ls2 _ dm2 (CertZ10.admRunOfPhrun false cpu ls2 rds2 wrs2 ann2 mm
      rsmC fnm ibm dm mm2 rsm2C fnm2 ibm2 dm2 hrunPC hadm2), hst2C, hag3⟩

end Weak
