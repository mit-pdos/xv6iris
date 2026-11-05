/-
Weak/Prom: **E-b4: E-a4's LOCK LIFECYCLE TEST ON TRACK (b) — THE VERDICT** (stage E-b4; owner ruling [OWN.P16],
context.md item 24: "you should probably run the same experiment on track b").

`own_be4` has EXACTLY `own_e4`'s statement (checked below by `type_of%`): in every valid run of `t7` — two lifetimes
of ONE lock at ONE address (hart 0: kfree junk, initlock `sw zero`, field init, publication, done-byte waits,
xv6's acquire/release at pipeclose, kfree junk again — THE DEATH — and a SECOND initlock at the same address;
harts 1, 2: xv6's acquire/release around `ld; addi; sd` in each lifetime) — every hart's memory-event trace satisfies
`q7` (per critical section mutual exclusion (1c), no field load reads junk or the image (4)).
Proved in TRACK (b)'s logic: lock-scoped pull promises over the NF_R replay lemma (`nfRF`, NfrFetch.lean) through
the trace-property adequacy `ownAdeqT` (B-0, OwnBE4Adeq.lean); the client state interpretation `XX`
(OwnBE4Iris.lean) holds the pure lifecycle protocol (OwnBE4Defs.lean) and half of each hart's stage record.
0 named inputs (`hnoinv` is the front end's machine fact `x_noInvalT`); finite runs (S3d separate, [OWN.P4]).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnBE4H0

namespace Weak.Prom.OB.E4

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Own (OSt upd)
open Weak.Prom.Own.X (xOW)
open Weak.Prom.OA (XI xOf xStep x_noInvalT Lk)
open Weak.Prom.OA.E4 (q7 img7 xs7 t7 b0 bA fI p0 pA)
open Weak.Prom.PF (PFRun memEv Trace progs_get)
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y Z)
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

section harts

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF Loc] [InvGS_gen hlc GF]

theorem fI0 : fI psInit := fun a tf vf h => by rw [show psInit.wFwd = ∅ from rfl, lookupEmpty] at h; cases h

/-- Hart 0, both rounds. -/
theorem h0Wp (M : List PMsg) (γ : Nat → GName) (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) (s : LP)
    (hs : s.prog = b0 ∧ s.q = [] ∧ s.pc = 0 ∧ RV s (rB 1)) :
    gl (γ 0) l00 ⊢ wpH (hlc := hlc) (GF := GF) M γ 0 s psInit := by
  iintro Hl
  ihave H1 := h0Round (hlc := hlc) (GF := GF) M γ hnoinv 1 (.inl rfl)
  iapply H1 $$ %s %psInit %l00 %0 %0 %⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, fI0, ⟨rfl, rfl, rfl, rfl, rfl⟩,
    Nat.zero_le _, Nat.zero_le _⟩ Hl
  iintro %s' %ws' %l' %u' %cf' %⟨_, h1, h2, h3, h4, h5, h6, h7, h8⟩ Hl
  ihave H2 := h0Round (hlc := hlc) (GF := GF) M γ hnoinv 2 (.inr rfl)
  iapply H2 $$ %s' %ws' %l' %u' %cf' %⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ Hl
  iintro %s'' %ws'' %l'' %u'' %cf'' %⟨h, _⟩
  exact absurd rfl h

/-- An acquirer, both rounds. -/
theorem hAWp (M : List PMsg) (γ : Nat → GName) (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) (i : Nat)
    (hi : i = 1 ∨ i = 2) (s : LP) (hs : s.prog = bA ∧ s.q = [] ∧ s.pc = 0 ∧ RV s (rA i 1)) :
    gl (γ i) lA0 ⊢ wpH (hlc := hlc) (GF := GF) M γ i s psInit := by
  iintro Hl
  ihave H1 := acqRound (hlc := hlc) (GF := GF) M γ i hi hnoinv 1 (.inl rfl)
  iapply H1 $$ %s %psInit %lA0 %⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, fI0, rfl, rfl, rfl⟩ Hl
  iintro %s' %ws' %l' %⟨_, h1, h2, h3, h4, h5, h6, h7, h8⟩ Hl
  ihave H2 := acqRound (hlc := hlc) (GF := GF) M γ i hi hnoinv 2 (.inr rfl)
  iapply H2 $$ %s' %ws' %l' %⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ Hl
  iintro %s'' %ws'' %l'' %⟨h, _⟩
  exact absurd rfl h

end harts

/-- The initial register files. -/
theorem init_rv {h : Nat} {p : LP} (hp : (progs t7)[h]? = some p) (r v : Nat) (hr : 0 < r ∧ r < 32)
    (hv : (((t7.regs0[h]?).getD []).lookup r).getD 0 % two64 = v) : p.rd r = v := by
  rw [(progs_get hp).2.2.2.2 r hr.1 hr.2, hv]

/-- **E-b4: THE LOCK LIFECYCLE ON TRACK (b)** (see the header). -/
theorem own_be4 (M : List PMsg) (run : PFRun LP Unit)
    (hrun : PF.validRun (xStep xs7) img7 () (progs t7) M run) : ∀ h, q7 M (memEv (run.trace h)) := by
  have hnoinv := x_noInvalT hrun
  obtain ⟨p0', p1, p2, hps⟩ : ∃ p0 p1 p2 : LP, progs t7 = [p0, p1, p2] := ⟨_, _, _, rfl⟩
  have hg0 : (progs t7)[0]? = some p0' := by rw [hps]; rfl
  have hg1 : (progs t7)[1]? = some p1 := by rw [hps]; rfl
  have hg2 : (progs t7)[2]? = some p2 := by rw [hps]; rfl
  obtain ⟨hpr0, hpc0, hq0, hl0, _⟩ := progs_get hg0
  obtain ⟨hpr1, hpc1, hq1, hl1, _⟩ := progs_get hg1
  obtain ⟨hpr2, hpc2, hq2, hl2, _⟩ := progs_get hg2
  have hs0 : p0'.prog = b0 ∧ p0'.q = [] ∧ p0'.pc = 0 ∧ RV p0' (rB 1) := ⟨hpr0, hq0, hpc0, hl0, fun q hq => by
    simp only [rB, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with e | e | e | e | e <;> rw [e] <;> exact init_rv hg0 _ _ ⟨by decide, by decide⟩ rfl⟩
  have hsA : ∀ (i : Nat) (p : LP), (progs t7)[i]? = some p → (i = 1 ∨ i = 2) →
      p.prog = bA ∧ p.q = [] ∧ p.pc = 0 ∧ RV p (rA i 1) := by
    intro i p hg hi
    obtain ⟨hpr, hpc, hq, hl, _⟩ := progs_get hg
    refine ⟨by rcases hi with rfl | rfl <;> exact hpr, hq, hpc, hl, fun q hq => ?_⟩
    simp only [rA, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hi with rfl | rfl <;>
    rcases hq with e | e | e | e | e | e <;> rw [e] <;> exact init_rv hg _ _ ⟨by decide, by decide⟩ rfl
  have key := ownAdeqT (hlc := .hasLC) (GF := ebGF) (w := xOW xs7 img7 M) (ps := progs t7) (fun _ => q7 M)
    (fun _ => Weak.Prom.OA.E4.q7_noLd Weak.Prom.OA.E2.noLd_nil) (fun {_} => by
      iintro
      imod ghost_var_alloc l00 with ⟨%γ0, H0⟩
      imod ghost_var_alloc lA0 with ⟨%γ1, H1⟩
      imod ghost_var_alloc lA0 with ⟨%γ2, H2⟩
      have s1 := ghost_var_split (GF := ebGF) γ0 l00 (1 : Qp).half (1 : Qp).half
      have s2 := ghost_var_split (GF := ebGF) γ1 lA0 (1 : Qp).half (1 : Qp).half
      have s3 := ghost_var_split (GF := ebGF) γ2 lA0 (1 : Qp).half (1 : Qp).half
      rw [Qp.half_add_half] at s1 s2 s3
      ihave ⟨H01, H02⟩ := s1 $$ H0
      ihave ⟨H11, H12⟩ := s2 $$ H1
      ihave ⟨H21, H22⟩ := s3 $$ H2
      let γ : Nat → GName := fun h => if h = 0 then γ0 else if h = 1 then γ1 else γ2
      imodintro
      iexists XX M γ
      isplitl [H01 H11 H21]
      · iexists S0, ls0
        rw [show γ 0 = γ0 from rfl, show γ 1 = γ1 from rfl, show γ 2 = γ2 from rfl, show ls0 0 = l00 from rfl,
          show ls0 1 = lA0 from rfl, show ls0 2 = lA0 from rfl]
        unfold gl
        iframe
        ipureintro; exact inv_init M
      isplitr
      · iapply agentX
      isplitl [H02 H12 H22]
      · rw [hps]
        simp only [hartsFromT]
        iapply BigSepL.bigSepL_cons.2
        isplitl [H02]
        · iapply h0Wp (hlc := .hasLC) M γ hnoinv p0' hs0; rw [show γ 0 = γ0 from rfl]; unfold gl; iexact H02
        iapply BigSepL.bigSepL_cons.2
        isplitl [H12]
        · iapply hAWp (hlc := .hasLC) M γ hnoinv 1 (.inl rfl) p1 (hsA 1 p1 hg1 (.inl rfl)); rw [show γ 1 = γ1 from rfl]; unfold gl; iexact H12
        iapply BigSepL.bigSepL_cons.2
        isplitl [H22]
        · iapply hAWp (hlc := .hasLC) M γ hnoinv 2 (.inr rfl) p2 (hsA 2 p2 hg2 (.inr rfl)); rw [show γ 2 = γ2 from rfl]; unfold gl; iexact H22
        exact BigSepL.bigSepL_nil_intro
      · iintro %σ %hf HX
        imod finalX $$ %σ %hf HX with %hq
        ipureintro
        intro h hh; rw [hps] at hh; exact hq h hh) hrun
  exact key

#print axioms own_be4

end Weak.Prom.OB.E4
