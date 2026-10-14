/-
Weak: **W10-4 [OWN.94] (N2′), increment 3 — the realizing step under taint, and POISONING**
(`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

Pinned twins: `WeakRvwmoCert2.certStepMirror`/`certStepReindex`/`certStepWitness` (a node that reads no
tainted register runs on agreeing register files; a load re-timed in the log; a load WITNESSED — any
bytes — whose continuation differs) and Cert3b's `csync` bookkeeping.  At the Z blocks:

  §1  the untainted single step (`CertZ11.stepUntainted`, the site datum's register clause for the
      realizing node) and its mirror (`CertZ11.stepMirror`, `pstepEvDagree`);
  §2  the POISON datum of a load site (`CertZ11.loadTail`: after a plain load at this node, for ANY
      answered bytes, the rest of the instruction is a silent tail off the grown taint — the Sail fact
      `witnessInstrTailSilent` relies on, per site);
  §3  **`CertZ11.realizeT`** — THE FUSED REALIZING STEP UNDER TAINT: from `clockstep`-related nodes the
      certified hart takes the machine label (a load re-answered with the latest bytes: same values ⇒
      same continuation, `clockstep`; different values ⇒ POISONED, `lblReidxSub`, both continuations
      in the silent tail, `csync`'s tail arm off the grown taint); a write is VERBATIM (the mirror).

Spec: FAITHFUL; the poison datum is a fact of the program at the site (W10-4 per pc).  Lean-only
helpers file-qualified (`CertZ11.*`).
-/
import Weak.CertZ10

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Wlabel

local notation "Ofence" => Option (Bool × Bool × Bool × Bool)

/-! # 1. The untainted single step -/

/-- The realizing node reads no tainted register (on every annotation of its step). -/
def CertZ11.stepUntainted (T : List Nat) (cpu : CPU) (l : Wlabel) (m : SailM Unit) (rs : RegFile)
    (fn : Ofence) (ib : Ibch) (d : Efab) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence)
    (ib' : Ibch) (d' : Efab) : Prop :=
  ∀ rds wrs ann, phrun cpu [l] rds wrs ann m rs fn ib d m' rs' fn' ib' d' →
    rdsOk (fun n => n ∉ T) rds

theorem CertZ11.phrunOne (cpu : CPU) (l : Wlabel) (m : SailM Unit) (rs : RegFile) (fn : Ofence)
    (ib : Ibch) (d : Efab) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch)
    (d' : Efab) :
    pstepEv (.PHart cpu m rs fn ib) d l (.PHart cpu m' rs' fn' ib') d' →
    ∃ rds wrs ann, phrun cpu [l] rds wrs ann m rs fn ib d m' rs' fn' ib' d' :=
  fun h => pevrunPhrun [l] _ d _ d' (pevrun.more h (pevrun.nil _ _)) cpu m rs fn ib m' rs' fn' ib'
    rfl rfl

/-- **THE MIRROR** of an untainted step (`certStepMirror` at a Z fabric). -/
theorem CertZ11.stepMirror (T : List Nat) (cpu : CPU) (l : Wlabel) (m : SailM Unit)
    (rs rs2 : RegFile) (fn : Ofence) (ib : Ibch) (d : Efab) (m' : SailM Unit) (rs' : RegFile)
    (fn' : Ofence) (ib' : Ibch) (d' : Efab) :
    pstepEv (.PHart cpu m rs fn ib) d l (.PHart cpu m' rs' fn' ib') d' →
    CertZ11.stepUntainted T cpu l m rs fn ib d m' rs' fn' ib' d' →
    dregAgree (fun n => n ∉ T) rs rs2 →
    ∃ rs2', pstepEv (.PHart cpu m rs2 fn ib) d l (.PHart cpu m' rs2' fn' ib') d' ∧
      dregAgree (fun n => n ∉ T) rs' rs2' := by
  intro hst hunt hag
  obtain ⟨rds, wrs, ann, hrun⟩ := CertZ11.phrunOne cpu l m rs fn ib d m' rs' fn' ib' d' hst
  obtain ⟨rs2', hrun2, hag2⟩ :=
    phrunDagree _ cpu [l] rds wrs ann m rs fn ib d m' rs' fn' ib' d' hrun (hunt _ _ _ hrun) rs2 hag
  exact ⟨rs2', pevrunSingleInv l _ d _ d' (phrunPevrun cpu [l] rds wrs ann m rs2 fn ib d m' rs2' fn'
    ib' d' hrun2), hag2⟩

/-! # 2. The poison datum of a load site -/

/-- **THE POISON DATUM** at a load node: whatever bytes a plain load at this node answers, its
continuation is a silent tail (off `T`) with no parked fence. -/
def CertZ11.loadTail (T : List Nat) (cpu : CPU) (m : SailM Unit) : Prop :=
  ∀ (rs : RegFile) (fn : Ofence) (ib : Ibch) (d : Efab) (aq : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (m2 : SailM Unit) (rs2 : RegFile) (fn2 : Ofence) (ib2 : Ibch)
    (d2 : Efab),
    pstepEv (.PHart cpu m rs fn ib) d (LLoad aq false base tvs []) (.PHart cpu m2 rs2 fn2 ib2) d2 →
    fn2 = none ∧ tailSilent T m2

/-! # 3. The fused realizing step under taint -/

/-- The read-value agreement of a row label at the candidate. -/
def CertZ11.readAgree (c : Cand) (lb : Lbl) : Prop :=
  (∀ aq base ts vs, lb = .LLoad aq base ts vs → lrdVs c base ts.length = vs) ∧
  (∀ aq rl base ts rvs wvs kc, lb = .LRmw aq rl base ts rvs wvs kc → lrdVs c base ts.length = rvs)

/-- **`CertZ11.realizeT` — THE FUSED REALIZING STEP UNDER TAINT.** -/
theorem CertZ11.realizeT (c : Cand) (T T' : List Nat) (cpu : CPU) (ma : SailM Unit)
    (rsa rsa2 : RegFile) (fna : Ofence) (iba : Ibch) (da : Efab) (ws ws' : Wstate) (lb : Lbl)
    (l : Wlabel) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) (d' : Efab) :
    T ⊆ T' → ws'.wRelp = ws.wRelp → lbFused l →
    hlblRealizes (.PHart cpu ma rsa fna iba) ws lb l →
    pstepEv (.PHart cpu ma rsa fna iba) da l (.PHart cpu m' rs' fn' ib') d' →
    CertZ11.stepUntainted T cpu l ma rsa fna iba da m' rs' fn' ib' d' →
    dregAgree (fun n => n ∉ T) rsa rsa2 →
    (CertZ11.readAgree c lb ∨
      (∃ base ts vs, lb = .LLoad false base ts vs ∧ CertZ11.loadTail T' cpu ma)) →
    ∃ (l' : Wlabel) (m2 : SailM Unit) (rs2' : RegFile) (fn2 : Ofence) (ib2 : Ibch),
      lbFused l' ∧ hlblRealizes (.PHart cpu ma rsa2 fna iba) ws' (CertZ4.machLbl c lb) l' ∧
      pstepEv (.PHart cpu ma rsa2 fna iba) da l' (.PHart cpu m2 rs2' fn2 ib2) d' ∧
      lblReidxW lb (CertZ4.machLbl c lb) ∧
      csync T' m' rs' fn' ib' m2 rs2' fn2 ib2 := by
  intro hTT hr hf hre hst hunt hag hval
  -- the mirror
  obtain ⟨rs2', hst2, hag2⟩ :=
    CertZ11.stepMirror T cpu l ma rsa rsa2 fna iba da m' rs' fn' ib' d' hst hunt hag
  have hag2' := dregAgreeTaintMono T T' rs' rs2' hTT hag2
  have hre2 : hlblRealizes (.PHart cpu ma rsa2 fna iba) ws' lb l :=
    CertZ5.hlblRealizesRelp _ ws ws' lb l hr
      (hlblRealizesRs cpu ma rsa rsa2 fna fna iba iba ws lb l hre)
  rcases hval with ⟨hvl, hvr⟩ | ⟨base, ts, vs, hlbE, htail⟩
  · -- values agree: re-answered, same continuation
    obtain ⟨l', hf', hre', hst'⟩ := CertZ5.oneRet c _ da ws' ws' lb l _ d' rfl hf hre2 hst2 hvl
    exact ⟨l', m', rs2', fn', ib', hf', hre', hst', CertZ4.machLblReidx c lb hvl hvr,
      .inl ⟨rfl, rfl, rfl, hag2'⟩⟩
  · -- POISONED: the latest bytes, a different continuation, both in the silent tail
    subst hlbE
    obtain ⟨hnb, hlat, hrf, hpr⟩ := hre2
    cases l with
    | LLoad aq lat base0 tvs asrc =>
      simp only [latFree] at hlat
      simp only [lbRfoldfree] at hrf
      subst hlat hrf
      simp only [projLbl, Option.some.injEq, Lbl.LLoad.injEq] at hpr
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hpr
      obtain ⟨m2, hst3⟩ := pstepEvLoadSubst cpu ma rsa2 fna iba da false base0 tvs
        (witTvs c base0 tvs.length) m' rs2' fn' ib' d' hst2 (witTvsLength c base0 tvs.length)
      obtain ⟨hfn1, hts1⟩ := htail rsa fna iba da false base0 tvs m' rs' fn' ib' d' hst
      obtain ⟨-, hts2⟩ := htail rsa2 fna iba da false base0 _ m2 rs2' fn' ib' d' hst3
      refine ⟨.LLoad false false base0 (witTvs c base0 tvs.length) [], m2, rs2', fn', ib', trivial,
        ⟨trivial, rfl, rfl, ?_⟩, hst3, ?_, .inr ⟨hfn1, hfn1, hts1, hts2, hag2'⟩⟩
      · simp only [projLbl, CertZ4.machLbl, List.length_map, witTvsFst, witTvsSnd]
      · refine Or.inr (Or.inl ?_)
        show false = false ∧ false = false ∧ base0 = base0 ∧
          (lrdTs c base0 (tvs.map Prod.fst).length).length = (tvs.map Prod.fst).length ∧
          (lrdVs c base0 (tvs.map Prod.fst).length).length =
            (lrdTs c base0 (tvs.map Prod.fst).length).length
        simp [lrdTs, lrdVs]
    | LExLoad => exact absurd hf (by simp [lbFused])
    | _ => simp [projLbl] at hpr

end Weak
