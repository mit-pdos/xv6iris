/-
Weak: **allocproc route P, row P-W6 — THE ADMIN STAR of a walk event, realized** (`SbWalk.evData`'s
`admRunG pstepEv true` star; `PROGRESS-PW6.md` §3 row "hart rows").  Lean-only, no Rocq twin.  A PRIMED
TWIN: nothing registered imports this file.

An event item's program data opens with the hart's ADMIN star: register reads and writes, the silent
outcomes (`cacheOp`, `tlbi`, `translation*`, exceptions, `message`, `choose`, the cycle counter, branch
announces), the non-`sfence.vma` instruction announce, the exclusive write's memory-blind RETRY, and the
instruction FETCHES.  **`SbRealPEv.adminEvP`**: one admin pf node step (`WeakEvInst.pnodeStep` with an
`lbAdmin true` label) of hart `cpu` at a MachCSL state `σ` whose register file is the pf's is either the
retry (MachCSL takes no step: W4's "lost-SC retry = 0 steps") or ONE `evStep` answering the same outcome
with the pf's answer — the post-state's registers the pf's, the other harts' and the devices unchanged,
and `rmemP` kept AT THE SAME TWIN STATE (an admin step moves no twin memory).  Its premises are the matrix
cells' (`notes/twin-machine-conformance.md` o, p): the armed register-write instrument (`excOk`, HSafe as
W4's (5)), and at a FETCH the fetch cut **in MachCSL's own terms** — the fetched word is the landed bytes
at some `itv ≤ tvn ≤ ltop`, the RAM footprint and the fetch guard (`fetchOk`, HSafe as W4's (6)): that is
P-W6's `FetchCutP` (`PROGRESS-PW6.md` F-PW6-4; discharged by rows 6h/6m/(t3)).

Spec: FAITHFUL (proof organisation; the premises are named plan items).  Lean-only helpers
`SbRealPEv.*`.
-/
import Weak.SbRealPHart

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D
open Lbl PfStepTsoMem SbRealP SbRealPHart

namespace SbRealPEv

/-- **`FetchCutP` at one fetch outcome** (stated in MachCSL's terms, F-PW6-4): the pf's fetched word `w`
of a RAM fetch is MachCSL's landed bytes at a cut `itv ≤ tvn ≤ ltop`, the footprint is DRAM and the armed
fetch guard allows it. -/
def FetchCutAt (cpu : CPU) (σ : MState) (o : Outcome Register RegisterType) : Prop :=
  ∀ (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak) (w : BitVec (8 * n)),
    o = .memRead n va req → akIfetch req.access_kind = true → devAddr req.pa = false →
    ramBytes req.pa n ∧ σ.fetchOk cpu req.pa ∧
      ∃ tvn, σ.itv cpu ≤ tvn ∧ tvn ≤ σ.ltop ∧ σ.mem.readBytesP σ.lp (ifetchAgent cpu) tvn req.pa n w

/-- What an answered admin outcome leaves: the pf's continuation, the pf's registers for the hart, the
other harts and the devices untouched, `rmemP` at the same twin state. -/
def AdminPost (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (o : Outcome Register RegisterType)
    (k : o.ret → SailM Unit) (rs : RegFile) (m' : SailM Unit) (ors : Option RegFile) : Prop :=
  ∃ (v : o.ret) (σ' : MState), m' = k v ∧ evStep cpu o σ v σ' ∧ σ'.regs cpu = ors.getD rs ∧
    (∀ c', c' ≠ cpu → σ'.regs c' = σ.regs c') ∧ σ'.devs = σ.devs ∧ rmemP img c σ'

theorem postSame (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU)
    (o : Outcome Register RegisterType) (k : o.ret → SailM Unit) (v : o.ret) (hR : rmemP img c σ)
    (hst : evStep cpu o σ v σ) : AdminPost img c σ cpu o k (σ.regs cpu) (k v) none :=
  ⟨v, σ, rfl, hst, rfl, fun _ _ => rfl, rfl, hR⟩

/-- **ONE ADMIN NODE STEP, REALIZED**: the exclusive write's memory-blind retry (no MachCSL step), or one
`evStep` with the pf's answer (`AdminPost`). -/
theorem adminEvP (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU)
    (o : Outcome Register RegisterType) (k : o.ret → SailM Unit) (rs : RegFile) (ib : Ibch)
    (d : DevStates) (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind)
    (hst : pnodeStep (.impure (.ok o) k) rs ib d l m' ors fn' d' oib obar)
    (had : lbAdmin true l) (hR : rmemP img c σ) (hrs : σ.regs cpu = rs)
    (hex : ∀ r v, o = .regWrite r v → σ.excOk cpu r v) (hcut : FetchCutAt cpu σ o) :
    (m' = .impure (.ok o) k ∧ ors = none) ∨ AdminPost img c σ cpu o k rs m' ors := by
  cases o with
  | regRead r =>
    obtain ⟨-, rfl, rfl, -⟩ := hst
    right; subst hrs; exact postSame img c σ cpu _ k _ hR (evRegReadP cpu σ r)
  | regWrite r v =>
    obtain ⟨-, rfl, rfl, -⟩ := hst
    right
    refine ⟨(), σ.setReg cpu r v, rfl, evRegWriteP cpu σ r v (hex r v rfl), ?_, fun c' hc => ?_, rfl,
      (rmemPSetReg img c σ cpu r v).2 hR⟩
    · show (if cpu = cpu then (σ.regs cpu).set r v else σ.regs cpu) = _
      rw [if_pos rfl, hrs]; rfl
    · show (if c' = cpu then (σ.regs cpu).set r v else σ.regs c') = _
      rw [if_neg hc]
  | memRead n va req =>
    simp only [pnodeStep] at hst
    split at hst
    · obtain ⟨w, -, rfl, -⟩ := hst
      exact absurd had (by simp [lbAdmin])
    · rename_i hda
      rcases hst with ⟨hif, w, tvs, hlen, hbytes, rfl, rfl, rfl, -⟩ | ⟨-, ⟨-, w, tvs, -, -, rfl, -⟩ | ⟨-, w, tvs, -, -, rfl, -⟩⟩
      · right
        obtain ⟨hram, hfo, hc⟩ := hcut n va req w rfl hif (by simpa using hda)
        exact ⟨_, σ, rfl, evFetchP cpu σ n va req w hram hif hfo hc, hrs, fun _ _ => rfl, rfl, hR⟩
      · exact absurd had (by simp [lbAdmin])
      · exact absurd had (by simp [lbAdmin])
  | memWrite n va req =>
    simp only [pnodeStep] at hst
    split at hst
    · split at hst
      · obtain ⟨-, rfl, -⟩ := hst
        exact absurd had (by simp [lbAdmin])
      · exact hst.elim
    · split at hst
      · obtain ⟨-, ⟨-, rfl, -⟩ | ⟨-, ⟨rfl, -⟩ | ⟨-, rfl, rfl, -⟩⟩⟩ := hst
        · exact absurd had (by simp [lbAdmin])
        · exact absurd had (by simp [lbAdmin])
        · exact .inl ⟨rfl, rfl⟩
      · exact hst.elim
  | readRam => exact hst.elim
  | writeRam => exact hst.elim
  | barrier b =>
    obtain ⟨rfl, -⟩ := hst
    unfold ebarLabel at had
    split at had <;> exact absurd had (by simp [lbAdmin])
  | cacheOp op =>
    obtain ⟨-, rfl, rfl, -⟩ := hst
    right; subst hrs; exact postSame img c σ cpu _ k () hR rfl
  | tlbi op =>
    obtain ⟨-, rfl, rfl, -⟩ := hst
    right; subst hrs; exact postSame img c σ cpu _ k () hR rfl
  | translationStart ts =>
    obtain ⟨-, rfl, rfl, -⟩ := hst
    right; subst hrs; exact postSame img c σ cpu _ k () hR rfl
  | translationEnd te =>
    obtain ⟨-, rfl, rfl, -⟩ := hst
    right; subst hrs; exact postSame img c σ cpu _ k () hR rfl
  | takeException f =>
    obtain ⟨-, rfl, rfl, -⟩ := hst
    right; subst hrs; exact postSame img c σ cpu _ k () hR rfl
  | returnException pa =>
    obtain ⟨-, rfl, rfl, -⟩ := hst
    right; subst hrs; exact postSame img c σ cpu _ k () hR rfl
  | cycleCount =>
    obtain ⟨-, rfl, rfl, -⟩ := hst
    right; subst hrs; exact postSame img c σ cpu _ k () hR rfl
  | getCycleCount =>
    obtain ⟨-, rfl, rfl, -⟩ := hst
    right; subst hrs; exact postSame img c σ cpu _ k (0 : Nat) hR ⟨rfl, rfl⟩
  | message msg =>
    obtain ⟨-, rfl, rfl, -⟩ := hst
    right; subst hrs; exact postSame img c σ cpu _ k () hR rfl
  | choose p =>
    obtain ⟨ch, -, rfl, rfl, -⟩ := hst
    right; subst hrs; exact postSame img c σ cpu _ k ch hR rfl
  | instrAnnounce n w =>
    obtain ⟨-, rfl, rfl, -⟩ := hst
    right; subst hrs; exact postSame img c σ cpu _ k () hR rfl
  | branchAnnounce n pc =>
    obtain ⟨-, rfl, rfl, -⟩ := hst
    right; subst hrs; exact postSame img c σ cpu _ k () hR rfl

/-- **THE BOUNDARY** (`hartStep`'s `.pure` arm; the pf's `LInstr` reset point): the reservation drops,
`rmemP` is kept. -/
theorem boundaryP (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (hR : rmemP img c σ) :
    rmemP img c (σ.dropResv cpu) := rmemPDropResv img c σ cpu hR

#print axioms Weak.SbRealPEv.adminEvP

end SbRealPEv

end Weak
