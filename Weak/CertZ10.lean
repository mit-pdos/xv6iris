/-
Weak: **W10-4 [OWN.94] (N2′), increment 2 — the TAINTED star: re-convergence at the instruction
boundary at a moving fabric** (`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

Pinned twin: `WeakRvwmoCert3b.csyncAdvance` (the two runs `csync`-related — the same node, or both in
the same instruction's silent tail — re-converge at the next boundary) and `WeakRvwmoCert2`'s
`certBlockMirror` (an untainted block runs step for step).  Both are stated at a fabric `d0` that
the silent tail does not move, so they hold at the block's START fabric `d` of a Z block
(`GraphFetchBlocks.blkOne`/`blkPair`); this file packages them for the Z blocks:

  §1  `CertZ10.syncSplit` — `csyncAdvance` with the emission's star SPLIT exactly (`ls = lsq ++ lsc`:
      its silent tail to the boundary, then the rest from the convergence point `mc`);
  §2  **`CertZ10.syncStar`** — the certified hart's star: its own silent tail to the boundary, then the
      emission's rest MIRRORED (`phrunDagree`) when the emission's star reads no tainted register; the
      two runs reach the realizing node with registers agreeing off the taint; the certified star's
      fetches are among the emission's (its tail is fetch-free);
  §3  the conversions `admRun` ↔ `admRunG pstepEv` (the Z blocks' star form).

Spec: proof organisation over the merged Sail-level lemmas (FAITHFUL).  Lean-only helpers
file-qualified (`CertZ10.*`).
-/
import Weak.CertZ9

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Wlabel

/-- The parked-fence field, abbreviated (as in `WeakRvwmoCert2`). -/
local notation "Ofence" => Option (Bool × Bool × Bool × Bool)

/-! # 3 (first). `admRun` and `admRunG pstepEv` -/

theorem CertZ10.admRunOfG (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel) (p' : Pexv6)
    (d' : Efab) : admRunG pstepEv instr p d ls p' d' → admRun instr p d ls p' d' := by
  intro h
  induction h with
  | nil p d => exact .ARnil p d
  | cons p d l p1 d1 ls p' d' ha hs _ ih => exact .ARcons p d l p1 d1 ls p' d' ha hs ih

theorem CertZ10.admRunGOf (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel) (p' : Pexv6)
    (d' : Efab) : admRun instr p d ls p' d' → admRunG pstepEv instr p d ls p' d' := by
  intro h
  induction h with
  | ARnil p d => exact .nil p d
  | ARcons p d l p1 d1 ls p' d' ha hs _ ih => exact .cons p d l p1 d1 ls p' d' ha hs ih

/-- A phrun of administrative labels is an `admRun`. -/
theorem CertZ10.admRunOfPhrun (instr : Bool) (cpu : CPU) (ls : List Wlabel) (rds : List Nat)
    (wrs : List Register) (ann : Bool) (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch)
    (d : Efab) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) (d' : Efab) :
    phrun cpu ls rds wrs ann m rs fn ib d m' rs' fn' ib' d' → (∀ l0, l0 ∈ ls → lbAdmin instr l0) →
    admRun instr (.PHart cpu m rs fn ib) d ls (.PHart cpu m' rs' fn' ib') d' :=
  fun h hadm => pevrunAdmRun instr _ d ls _ d'
    (phrunPevrun cpu ls rds wrs ann m rs fn ib d m' rs' fn' ib' d' h) hadm

theorem CertZ10.admRunApp (instr : Bool) (p : Pexv6) (d : Efab) (ls1 : List Wlabel) (p1 : Pexv6)
    (d1 : Efab) (ls2 : List Wlabel) (p2 : Pexv6) (d2 : Efab) :
    admRun instr p d ls1 p1 d1 → admRun instr p1 d1 ls2 p2 d2 →
    admRun instr p d (ls1 ++ ls2) p2 d2 := by
  intro h1
  induction h1 with
  | ARnil => intro h2; exact h2
  | ARcons p d l p1' d1' ls p' d' ha hs _ ih =>
    intro h2
    exact .ARcons p d l p1' d1' _ _ _ ha hs (ih h2)

/-! # 1. The split -/

theorem CertZ10.noDevOfAdmin (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel)
    (p' : Pexv6) (d' : Efab) :
    admRun instr p d ls p' d' → ∀ kd ba bs sa sv, LDev kd ba bs sa sv ∉ ls := by
  intro h kd ba bs sa sv hin
  have := admRunAdmin instr p d ls p' d' h _ hin
  simp [lbAdmin] at this

/-- **`CertZ10.syncSplit`** (`csyncAdvance` with the split exact): from `csync`-related states, the
emission's star (from the block's start fabric `d`) is its silent tail to the boundary `lsq` then
the rest `lsc` from the convergence node `mc`; the certified hart has its own silent tail `lspre`
to `mc`; registers agree off the taint at `mc`. -/
theorem CertZ10.syncSplit (T : List Nat) (cpu : CPU) (d : Efab)
    (m1 : SailM Unit) (rs1 : RegFile) (fn1 : Ofence) (ib1 : Ibch)
    (m2 : SailM Unit) (rs2 : RegFile) (fn2 : Ofence) (ib2 : Ibch)
    (ls : List Wlabel) (ma : SailM Unit) (rsa : RegFile) (fna : Ofence) (iba : Ibch) (da : Efab)
    (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    csync T m1 rs1 fn1 ib1 m2 rs2 fn2 ib2 →
    admRun true (.PHart cpu m1 rs1 fn1 ib1) d ls (.PHart cpu ma rsa fna iba) da →
    ¬ lbAdmin true l → (∀ kd ba bs sa sv, l ≠ LDev kd ba bs sa sv) →
    pstepEv (.PHart cpu ma rsa fna iba) da l p' d' →
    ∃ (mc : SailM Unit) (rs1c rs2c : RegFile) (fnc : Ofence) (ibc : Ibch)
      (lsc lspre lsq : List Wlabel) (rdsp rdsq : List Nat) (wrsp wrsq : List Register)
      (annp annq : Bool),
      ls = lsq ++ lsc ∧
      admRun true (.PHart cpu mc rs1c fnc ibc) d lsc (.PHart cpu ma rsa fna iba) da ∧
      (∀ l0, l0 ∈ lspre → lbAdmin true l0) ∧
      phrun cpu lspre rdsp wrsp annp m2 rs2 fn2 ib2 d mc rs2c fnc ibc d ∧
      phrun cpu lsq rdsq wrsq annq m1 rs1 fn1 ib1 d mc rs1c fnc ibc d ∧
      dregAgree (fun n => n ∉ T) rs1c rs2c ∧
      (∀ l0, l0 ∈ lspre → ∀ im, WeakAxRealize.fetchPin im l0) := by
  rintro (⟨rfl, rfl, rfl, hag⟩ | ⟨rfl, rfl, hts1, hts2, hag⟩) hadm hre hld hst
  · exact ⟨_, rs1, rs2, _, _, ls, [], [], [], [], [], [], false, false, rfl, hadm,
      fun _ h => absurd h List.not_mem_nil, phrun.nil _ _ _ _ _, phrun.nil _ _ _ _ _, hag,
      fun _ h => absurd h List.not_mem_nil⟩
  · have hni := CertZ10.noDevOfAdmin true _ d ls _ da hadm
    obtain ⟨ls1, ls2, rds1, wrs1, ann1, rsb, ibb, tick, hsp, hrun1, hws1, hadm2⟩ :=
      witnessInstrTailSilent T cpu m1 rs1 ib1 d da ls ma rsa fna iba l p' d' hts1 hni hadm hre
        hld hst
    obtain ⟨lsq, rdsq, wrsq, annq, rs2b, ib2b, hadmq, _, hrunq, hwsq, hpinq⟩ :=
      tailSilentRun T cpu d m2 hts2 rs2 ib2
    refine ⟨riscvStep tick, rsb, rs2b, none, ibNone, ls2, lsq ++ [LInstr], ls1 ++ [LInstr],
      _, _, _, _, _, _, by rw [hsp]; simp, hadm2, ?_,
      WeakRvwmoCert3.phrunApp hrunq (WeakRvwmoCert3.phrunBoundary cpu rs2b ib2b d tick),
      WeakRvwmoCert3.phrunApp hrun1 (WeakRvwmoCert3.phrunBoundary cpu rsb ibb d tick), ?_, ?_⟩
    · intro l0 hl0
      rcases List.mem_append.1 hl0 with h | h
      · exact hadmq l0 h
      · rw [List.mem_singleton.1 h]; rfl
    · refine taintClosure (fun n => n ∉ T) cpu ls1 rds1 wrs1 ann1 m1 rs1 none ib1 d (.pure ()) rsb
        none ibb d cpu lsq rdsq wrsq annq m2 rs2 none ib2 d (.pure ()) rs2b none ib2b d hag
        hrun1 hrunq ?_
      intro r hr
      rcases List.mem_append.1 hr with h | h
      · obtain ⟨n, hn, hin⟩ := hws1 r h
        exact ⟨n, hn, fun hno => hno hin⟩
      · obtain ⟨n, hn, hin⟩ := hwsq r h
        exact ⟨n, hn, fun hno => hno hin⟩
    · intro l0 hl0 im
      rcases List.mem_append.1 hl0 with h | h
      · exact hpinq l0 h im
      · rw [List.mem_singleton.1 h]; trivial

/-! # 2. The certified star -/

/-- **The emission's star READS NO TAINTED REGISTER** (the site datum's register clause, on every
annotation of the run: the reads are the visited nodes'). -/
def CertZ10.starUntainted (T : List Nat) (cpu : CPU) (ls : List Wlabel) (m : SailM Unit)
    (rs : RegFile) (fn : Ofence) (ib : Ibch) (d : Efab) (m' : SailM Unit) (rs' : RegFile)
    (fn' : Ofence) (ib' : Ibch) (d' : Efab) : Prop :=
  ∀ rds wrs ann, phrun cpu ls rds wrs ann m rs fn ib d m' rs' fn' ib' d' →
    rdsOk (fun n => n ∉ T) rds

/-- A label pinned at EVERY image is not a fetch with bytes. -/
theorem CertZ10.pinAllNoFetch (l : Wlabel) :
    (∀ im, WeakAxRealize.fetchPin im l) →
    ∀ base tvs, l = LIFetch base tvs → tvs = [] := by
  intro h base tvs he
  subst he
  obtain ⟨-, h2⟩ := h (fun _ => none)
  cases tvs with
  | nil => rfl
  | cons tv tvs =>
    have := h2 0 (by simp)
    simp at this

/-- **`CertZ10.syncStar` — THE CERTIFIED STAR**: from `csync`-related states and the emission's star
(reading no tainted register), the certified hart has a star to the emission's realizing node
`ma`, with registers agreeing off the taint, whose fetches carry bytes only where the emission's
do (its own silent tail is fetch-free). -/
theorem CertZ10.syncStar (T : List Nat) (cpu : CPU) (d : Efab)
    (m1 : SailM Unit) (rs1 : RegFile) (fn1 : Ofence) (ib1 : Ibch)
    (m2 : SailM Unit) (rs2 : RegFile) (fn2 : Ofence) (ib2 : Ibch)
    (ls : List Wlabel) (ma : SailM Unit) (rsa : RegFile) (fna : Ofence) (iba : Ibch) (da : Efab)
    (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    csync T m1 rs1 fn1 ib1 m2 rs2 fn2 ib2 →
    admRun true (.PHart cpu m1 rs1 fn1 ib1) d ls (.PHart cpu ma rsa fna iba) da →
    CertZ10.starUntainted T cpu ls m1 rs1 fn1 ib1 d ma rsa fna iba da →
    ¬ lbAdmin true l → (∀ kd ba bs sa sv, l ≠ LDev kd ba bs sa sv) →
    pstepEv (.PHart cpu ma rsa fna iba) da l p' d' →
    ∃ (ls2 : List Wlabel) (rsa2 : RegFile),
      admRun true (.PHart cpu m2 rs2 fn2 ib2) d ls2 (.PHart cpu ma rsa2 fna iba) da ∧
      dregAgree (fun n => n ∉ T) rsa rsa2 ∧
      ∀ base tvs, LIFetch base tvs ∈ ls2 → tvs = [] ∨ LIFetch base tvs ∈ ls := by
  intro hcs hadm hunt hre hld hst
  obtain ⟨mc, rs1c, rs2c, fnc, ibc, lsc, lspre, lsq, rdsp, rdsq, wrsp, wrsq, annp, annq, hsp,
    hadmc, hpadm, hrunp, hrunq, hag, hpin⟩ :=
    CertZ10.syncSplit T cpu d m1 rs1 fn1 ib1 m2 rs2 fn2 ib2 ls ma rsa fna iba da l p' d' hcs hadm
      hre hld hst
  -- the emission's rest as an annotated run, untainted
  obtain ⟨rdsc, wrsc, annc, hrunc⟩ := pevrunPhrun lsc _ d _ da (admRunPevrun true _ d lsc _ da hadmc)
    cpu mc rs1c fnc ibc ma rsa fna iba rfl rfl
  have hwhole := WeakRvwmoCert3.phrunApp hrunq hrunc
  rw [← hsp] at hwhole
  have hrdsc : rdsOk (fun n => n ∉ T) rdsc := (rdsOkApp _ _ _ (hunt _ _ _ hwhole)).2
  obtain ⟨rsa2, hrun2, hag2⟩ := phrunDagree (fun n => n ∉ T) cpu lsc rdsc wrsc annc mc rs1c fnc
    ibc d ma rsa fna iba da hrunc hrdsc rs2c hag
  have hadmc' : ∀ l0, l0 ∈ lsc → lbAdmin true l0 := fun l0 h =>
    admRunAdmin true _ d lsc _ da hadmc l0 h
  refine ⟨lspre ++ lsc, rsa2,
    CertZ10.admRunApp true _ d lspre _ d lsc _ da (CertZ10.admRunOfPhrun true cpu lspre rdsp wrsp
      annp m2 rs2 fn2 ib2 d mc rs2c fnc ibc d hrunp hpadm)
      (CertZ10.admRunOfPhrun true cpu lsc rdsc wrsc annc mc rs2c fnc ibc d ma rsa2 fna iba da
        hrun2 hadmc'), hag2, fun base tvs hm => ?_⟩
  rcases List.mem_append.1 hm with h | h
  · exact .inl (CertZ10.pinAllNoFetch _ (hpin _ h) base tvs rfl)
  · exact .inr (by rw [hsp]; exact List.mem_append_right _ h)

end Weak
