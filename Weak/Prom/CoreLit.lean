/-
Weak/Prom: **litmus verdicts proved IN THE LOGIC** (stage S2; plan rev 7 §2 "The LB trio, derived step by step from
A0's exports", §5 rows 1–3, §8 S2).

The programs are the S0/S1 rows of `Weak/Prom/RefTests.lean` (`Weak.Prom.Ref.Lit.lbdd` = row 2, `Lit.lbDatas` = row 3, `Lit.lb` =
row 1) run by the litmus front end `litStep` (MachCert.lean §1) on machine v2, from `testImg`.  As in the
repository tests they use `lw`/`sw` (4 bytes) at `x = 0x1000`, `y = 0x2000`; row 3 is the repository's `LB+datas`
(`xor t,a,a; ori t,t,1`, the same syntactic source lists as the plan's `xor; addi`).  The plan's 8-byte `ld`/`sd`
becomes a 4-byte width in (P1)/(P4).

* `lit_lbdd` (row 2, FORBIDDEN) and `lit_lbfd` (row 3, FORBIDDEN): `∀ M run, PF.validRun … M run →
  ¬ (run.obsLoad 0 0 = some 1 ∧ run.obsLoad 1 0 = some 1)`, exactly plan §2's derivations:
  - π is the trivial family (PO-img, PO-ad outright), Φ is `True`, `devFreeProg` holds (no fabric);
  - Ψ is (P0)–(P4) (`ΨLB`, CoreLitBase.lean), proved by each hart step by step through the leaf rules: LOAD gives
    (X4) `wLdv ≥ s`, REGW (X5) `regv a0 ≥ s` (row 3: `xor`'s `[a0, a0]`, `ori`'s `[t]`), INSTR keeps it, FULFIL
    (X6) `s ≤ vd ≤ pv < t`; every obligation at V = 0;
  - the contradiction is `lb_contra` (CoreLitBase.lean), from A0's exports (ii), (iii), (v) only.
* Row 1 LB (ALLOWED) is NOT derivable as forbidden: `lit_lb_allowed` is machine v2's certificate `mach_lb`
  (MachCerts.lean), a valid run with the outcome; see its docstring for why no Ψ either hart can prove excludes it.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreLitBase
import Weak.Prom.MachCerts

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. One LB+data hart, in the logic -/

section hart

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [InvGS_gen hlc GF]

theorem lp_rd_wr {s : LP} {r r' v : Nat} (h : r ≠ r') : ({ s with regs := s.wr r' v } : LP).rd r = s.rd r := by
  unfold LP.rd LP.wr
  by_cases h0 : r = 0
  · simp [h0]
  · by_cases h0' : r' = 0
    · simp [h0, h0']
    · simp only [h0, h0', if_false]; rw [List.getElem?_set_ne (Ne.symm h)]

/-- The trace so far has no timestamped entry. -/
theorem noTs_cons {τ : Trace} {e : PEv} (h : ∀ e ∈ τ, e.2 = none) (he : e.2 = none) :
    ∀ e' ∈ τ ++ [e], e'.2 = none := by
  intro e' he'
  rcases List.mem_append.1 he' with he' | he'
  · exact h e' he'
  · rw [List.mem_singleton] at he'; subst he'; exact he

theorem loadLike_regw (rd : Nat) (srcs : List Dsrc) : loadLikeTvs (LRegW rd srcs) = none := rfl
theorem loadLike_instr : loadLikeTvs LInstr = none := rfl

/-- The hart state after `lw rd,(rs1)` (MachCert.lean `instrNext`'s `.load` arm, signed). -/
@[reducible] def ldS1 (s0 : LP) (rd : Nat) (tvs : List (Nat × BitVec 8)) : LP :=
  { s0 with regs := s0.wr rd (if true then sext 4 (ofBytes (tvs.map Prod.snd)) else ofBytes (tvs.map Prod.snd)),
            pc := s0.pc + 1, q := regWL rd [.DLdRes] ++ [LInstr] }

/-- **The LB+data+data hart in the logic** (plan §2, H0's proof a–c): `lw a0,(x); sw a0,(y)` proves Ψ = (P0)–(P4)
at every step (V = 0) and `True` at its end. -/
theorem lbdd_hart (s0 : LP) (x y : Nat) (img : Image) (M : List PMsg) (h : Nat)
    (hprog : s0.prog = [.load 4 true 5 6 0, .store 4 5 8 0]) (hpc : s0.pc = 0) (hq : s0.q = [])
    (hx : s0.rd 6 = x) (hy : s0.rd 8 = y) (hxa : x % 4 = 0) (hya : y % 4 = 0) (hxl : x < two64)
    (hyl : y < two64) :
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩ (ΨLB x y 4) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  unfold wpPF
  iintro %γ %P0 %_ Hst
  -- a. `lw a0,(x)`
  have hxa' : aligned ((s0.rd 6 + 0) % two64) 4 = true := by
    rw [hx, Nat.add_zero, Nat.mod_eq_of_lt hxl]; simp [aligned, hxa]
  have hxx : (((s0.rd 6 + 0) % two64 : Nat) : Int) = (x : Int) := by rw [hx, Nat.add_zero, Nat.mod_eq_of_lt hxl]
  iapply (wpH_load (s := s0) (aq := false) (rl := false) (base := (x : Int)) (asrc := [.DReg 6])
    (k := ldS1 s0 5) (C := fun tvs => tvs.length = 4) (litDone_pc (by rw [hprog, hpc]; decide))
    (fun l s' hs => by
      obtain ⟨tvs, h1, h2, h3⟩ := litNext_load hq (by rw [hprog, hpc]; rfl) hxa' (anyFab_lit.1 hs)
      exact ⟨tvs, by rw [h1, hxx]; rfl, h2, h3⟩))
  iframe Hst
  inext
  iintro %tvs %hC %hlo _
  have ψ1 := psiLB_load (psiLB_nil (x : Int) (y : Int) 4) (fun _ h => by cases h) tvs [.DReg 6] hC
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ1⟩
  iintro Hst
  -- b. `LRegW a0 [DLdRes]`, `LInstr`
  have hq1 : (ldS1 s0 5 tvs).q = LRegW 5 [.DLdRes] :: [LInstr] := by simp [ldS1, regWL]
  iapply (wpH_regw (s := ldS1 s0 5 tvs) (rd := 5) (srcs := [.DLdRes]) (litDone_q (by rw [hq1]; simp))
    (fun l s' hs => litNext_q hq1 (anyFab_lit.1 hs)))
  iframe Hst
  inext
  iintro _
  have ψ2 := psiLB_quiet ψ1 _ (loadLike_regw 5 [.DLdRes]) (fun _ _ _ _ _ _ h => by cases h)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ2⟩
  iintro Hst
  iapply (wpH_instr (s := { ldS1 s0 5 tvs with q := [LInstr] })
    (litDone_q (s := { ldS1 s0 5 tvs with q := [LInstr] }) (by simp))
    (fun l s' hs => litNext_q rfl (anyFab_lit.1 hs)))
  iframe Hst
  inext
  iintro _
  have ψ3 := psiLB_quiet ψ2 _ loadLike_instr (fun _ _ _ _ _ _ h => by cases h)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ3⟩
  iintro Hst
  -- c. `sw a0,(y)`: (X6) `s ≤ regv a0 ≤ vd ≤ pv < t`
  have hy3 : ({ { ldS1 s0 5 tvs with q := [LInstr] } with q := [] } : LP).rd 8 = y := by
    rw [← hy]; exact lp_rd_wr (r := 8) (r' := 5) (by decide)
  have hya' : aligned ((({ { ldS1 s0 5 tvs with q := [LInstr] } with q := [] } : LP).rd 8 + 0) % two64) 4 = true := by
    rw [hy3, Nat.add_zero, Nat.mod_eq_of_lt hyl]; simp [aligned, hya]
  have hyy : (((({ { ldS1 s0 5 tvs with q := [LInstr] } with q := [] } : LP).rd 8 + 0) % two64 : Nat) : Int)
      = (y : Int) := by rw [hy3, Nat.add_zero, Nat.mod_eq_of_lt hyl]
  iapply (wpH_store (s := { { ldS1 s0 5 tvs with q := [LInstr] } with q := [] }) (aq := false) (rl := false)
    (base := (y : Int)) (data := toBytes (({ { ldS1 s0 5 tvs with q := [LInstr] } with q := [] } : LP).rd 5) 4)
    (asrc := [.DReg 8]) (vsrc := [.DReg 5])
    (k := { { { ldS1 s0 5 tvs with q := [LInstr] } with q := [] } with pc := s0.pc + 1 + 1, q := [LInstr] })
    (litDone_pc (s := { { ldS1 s0 5 tvs with q := [LInstr] } with q := [] }) (by simp [ldS1, hprog, hpc]))
    (fun l s' hs => by
      obtain ⟨h1, h2⟩ := litNext_store (s := { { ldS1 s0 5 tvs with q := [LInstr] } with q := [] })
        (sz := 4) (rs2 := 5) (rs1 := 8) (off := 0) rfl
        (by simp [ldS1, hprog, hpc]) hya' (anyFab_lit.1 hs)
      exact ⟨by rw [h1, hyy]; rfl, h2⟩))
  iframe Hst
  inext
  iintro %ts %_ %_ %_ %hext _
  have hlt : ∀ e ∈ ((([] : Trace) ++ [(LLoad false false (x : Int) tvs [.DReg 6], none)]) ++ [(LRegW 5 [.DLdRes], none)]) ++
      [(LInstr, none)], ∀ aq rl base tv tvs' asrc, e.1 = LLoad aq rl base (tv :: tvs') asrc → tv.1 < ts := by
    intro e he aq rl base tv tvs' asrc hl
    simp only [List.nil_append, List.mem_append, List.mem_singleton] at he
    rcases he with (rfl | rfl) | rfl
    · simp only [LLoad.injEq] at hl
      obtain ⟨_, _, _, rfl, _⟩ := hl
      refine Nat.lt_of_le_of_lt ?_ (Nat.lt_of_le_of_lt (store_ext _ _ _ _ _) hext)
      refine Nat.le_trans ?_ (Nat.le_max_right _ _)
      rw [srcsView_reg, regv_instr, regv_regW, srcsView_ldres]
      exact loadRun_ldv0 (fwdHit_empty lookupEmpty)
    · cases hl
    · cases hl
  have hnt3 : ∀ e ∈ ((([] : Trace) ++ [(LLoad false false (x : Int) tvs [.DReg 6], none)]) ++ [(LRegW 5 [.DLdRes], none)]) ++
      [(LInstr, none)], e.2 = none := by
    intro e he
    simp only [List.nil_append, List.mem_append, List.mem_singleton] at he
    rcases he with (rfl | rfl) | rfl <;> rfl
  have ψ4 := psiLB_store ψ3 hnt3 false false
    (toBytes (({ { ldS1 s0 5 tvs with q := [LInstr] } with q := [] } : LP).rd 5) 4) [.DReg 8] [.DReg 5] ts
    (toBytes_length _ _) hlt
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ4⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro Hst
  iapply (wpH_instr (s := { { { ldS1 s0 5 tvs with q := [LInstr] } with q := [] } with
      pc := s0.pc + 1 + 1, q := [LInstr] })
    (litDone_q (s := { { { ldS1 s0 5 tvs with q := [LInstr] } with q := [] } with
      pc := s0.pc + 1 + 1, q := [LInstr] }) (by simp))
    (fun l s' hs => litNext_q rfl (anyFab_lit.1 hs)))
  iframe Hst
  inext
  iintro _
  have ψ5 := psiLB_quiet ψ4 _ loadLike_instr (fun _ _ _ _ _ _ h => by cases h)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ5⟩
  iintro Hst
  -- the end: no step, the value `()`
  iapply (wpH_done (v := ()) (s := { { { { ldS1 s0 5 tvs with q := [LInstr] } with q := [] } with
      pc := s0.pc + 1 + 1, q := [LInstr] } with q := [] }) (by simp [litDone, ldS1, hprog, hpc])
    (fun l s' hs => by
      rw [anyFab_lit, litNext_end rfl (by simp [ldS1, hprog, hpc])] at hs; cases hs))
  iframe Hst
  iintro _
  imodintro
  ipureintro
  exact ⟨0, grd_intro trivial⟩

/-- The LB+fakedep hart's states after `xor` (S4), its `LInstr` (S5), `ori` (S6), its `LInstr` (S7), the store
(S8) and its `LInstr` (S9). -/
@[reducible] def fdS3 (s0 : LP) (tvs : List (Nat × BitVec 8)) : LP := { { ldS1 s0 5 tvs with q := [LInstr] } with q := [] }
@[reducible] def fdS4 (s0 : LP) (tvs : List (Nat × BitVec 8)) : LP :=
  { fdS3 s0 tvs with regs := (fdS3 s0 tvs).wr 7 (aluOp .xor ((fdS3 s0 tvs).rd 5) ((fdS3 s0 tvs).rd 5)),
                     pc := (fdS3 s0 tvs).pc + 1, q := [LInstr] }
@[reducible] def fdS5 (s0 : LP) (tvs : List (Nat × BitVec 8)) : LP := { fdS4 s0 tvs with q := [] }
@[reducible] def fdS6 (s0 : LP) (tvs : List (Nat × BitVec 8)) : LP :=
  { fdS5 s0 tvs with regs := (fdS5 s0 tvs).wr 7 (aluOp .or ((fdS5 s0 tvs).rd 7) 1),
                     pc := (fdS5 s0 tvs).pc + 1, q := [LInstr] }
@[reducible] def fdS7 (s0 : LP) (tvs : List (Nat × BitVec 8)) : LP := { fdS6 s0 tvs with q := [] }
@[reducible] def fdS8 (s0 : LP) (tvs : List (Nat × BitVec 8)) : LP := { fdS7 s0 tvs with pc := (fdS7 s0 tvs).pc + 1, q := [LInstr] }
@[reducible] def fdS9 (s0 : LP) (tvs : List (Nat × BitVec 8)) : LP := { fdS8 s0 tvs with q := [] }

/-- **The LB+fakedep hart in the logic** (plan §2, H0's proof with step b′): `lw a0,(x); xor t,a0,a0; ori t,t,1;
sw t,(y)`.  `xor` emits `LRegW t [a0, a0]` (§rvwmo: "Most non-memory instructions carry a dependency from each of
their source registers to each of their destination registers"), `ori` emits `LRegW t [t]`, so `regv t ≥ s` (X5)
although `t` is always 1: the view is syntactic. -/
theorem lbfd_hart (s0 : LP) (x y : Nat) (img : Image) (M : List PMsg) (h : Nat)
    (hprog : s0.prog = [.load 4 true 5 6 0, .alu .xor 7 5 5, .alui .or 7 7 1, .store 4 7 8 0]) (hpc : s0.pc = 0)
    (hq : s0.q = []) (hx : s0.rd 6 = x) (hy : s0.rd 8 = y) (hxa : x % 4 = 0) (hya : y % 4 = 0) (hxl : x < two64)
    (hyl : y < two64) :
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩ (ΨLB x y 4) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  unfold wpPF
  iintro %γ %P0 %_ Hst
  -- a. `lw a0,(x)`
  have hxa' : aligned ((s0.rd 6 + 0) % two64) 4 = true := by
    rw [hx, Nat.add_zero, Nat.mod_eq_of_lt hxl]; simp [aligned, hxa]
  have hxx : (((s0.rd 6 + 0) % two64 : Nat) : Int) = (x : Int) := by rw [hx, Nat.add_zero, Nat.mod_eq_of_lt hxl]
  iapply (wpH_load (s := s0) (aq := false) (rl := false) (base := (x : Int)) (asrc := [.DReg 6])
    (k := ldS1 s0 5) (C := fun tvs => tvs.length = 4) (litDone_pc (by rw [hprog, hpc]; decide))
    (fun l s' hs => by
      obtain ⟨tvs, h1, h2, h3⟩ := litNext_load hq (by rw [hprog, hpc]; rfl) hxa' (anyFab_lit.1 hs)
      exact ⟨tvs, by rw [h1, hxx]; rfl, h2, h3⟩))
  iframe Hst
  inext
  iintro %tvs %hC %hlo _
  have ψ1 := psiLB_load (psiLB_nil (x : Int) (y : Int) 4) (fun _ h => by cases h) tvs [.DReg 6] hC
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ1⟩
  iintro Hst
  have hq1 : (ldS1 s0 5 tvs).q = LRegW 5 [.DLdRes] :: [LInstr] := by simp [ldS1, regWL]
  iapply (wpH_regw (s := ldS1 s0 5 tvs) (rd := 5) (srcs := [.DLdRes]) (litDone_q (by rw [hq1]; simp))
    (fun l s' hs => litNext_q hq1 (anyFab_lit.1 hs)))
  iframe Hst
  inext
  iintro _
  have ψ2 := psiLB_quiet ψ1 _ (loadLike_regw 5 [.DLdRes]) (fun _ _ _ _ _ _ h => by cases h)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ2⟩
  iintro Hst
  iapply (wpH_instr (s := { ldS1 s0 5 tvs with q := [LInstr] })
    (litDone_q (s := { ldS1 s0 5 tvs with q := [LInstr] }) (by simp))
    (fun l s' hs => litNext_q rfl (anyFab_lit.1 hs)))
  iframe Hst
  inext
  iintro _
  have ψ3 := psiLB_quiet ψ2 _ loadLike_instr (fun _ _ _ _ _ _ h => by cases h)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ3⟩
  iintro Hst
  -- b′. `xor t,a0,a0`: `LRegW t [a0, a0]`
  iapply (wpH_regw (s := fdS3 s0 tvs) (rd := 7) (srcs := [.DReg 5, .DReg 5]) (k := fdS4 s0 tvs)
    (litDone_pc (s := fdS3 s0 tvs) (by simp [fdS3, ldS1, hprog, hpc]))
    (fun l s' hs => by
      obtain ⟨h1, h2⟩ := litNext_alu (s := fdS3 s0 tvs) (op := .xor) (rd := 7) (rs1 := 5) (rs2 := 5) rfl
        (by simp [fdS3, ldS1, hprog, hpc]) (by decide) (anyFab_lit.1 hs)
      exact ⟨h1, h2⟩))
  iframe Hst
  inext
  iintro _
  have ψ4 := psiLB_quiet ψ3 _ (loadLike_regw 7 [.DReg 5, .DReg 5]) (fun _ _ _ _ _ _ h => by cases h)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ4⟩
  iintro Hst
  iapply (wpH_instr (s := fdS4 s0 tvs) (litDone_q (s := fdS4 s0 tvs) (by simp [fdS4]))
    (fun l s' hs => litNext_q rfl (anyFab_lit.1 hs)))
  iframe Hst
  inext
  iintro _
  have ψ5 := psiLB_quiet ψ4 _ loadLike_instr (fun _ _ _ _ _ _ h => by cases h)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ5⟩
  iintro Hst
  -- `ori t,t,1`: `LRegW t [t]`
  iapply (wpH_regw (s := fdS5 s0 tvs) (rd := 7) (srcs := [.DReg 7]) (k := fdS6 s0 tvs)
    (litDone_pc (s := fdS5 s0 tvs) (by simp [fdS5, fdS4, fdS3, ldS1, hprog, hpc]))
    (fun l s' hs => by
      obtain ⟨h1, h2⟩ := litNext_alui (s := fdS5 s0 tvs) (op := .or) (rd := 7) (rs1 := 7) (imm := 1) rfl
        (by simp [fdS5, fdS4, fdS3, ldS1, hprog, hpc]) (by decide) (anyFab_lit.1 hs)
      exact ⟨h1, h2⟩))
  iframe Hst
  inext
  iintro _
  have ψ6 := psiLB_quiet ψ5 _ (loadLike_regw 7 [.DReg 7]) (fun _ _ _ _ _ _ h => by cases h)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ6⟩
  iintro Hst
  iapply (wpH_instr (s := fdS6 s0 tvs) (litDone_q (s := fdS6 s0 tvs) (by simp [fdS6]))
    (fun l s' hs => litNext_q rfl (anyFab_lit.1 hs)))
  iframe Hst
  inext
  iintro _
  have ψ7 := psiLB_quiet ψ6 _ loadLike_instr (fun _ _ _ _ _ _ h => by cases h)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ7⟩
  iintro Hst
  -- `sw t,(y)`: (X6)
  have hy7 : (fdS7 s0 tvs).rd 8 = y := by
    rw [← hy]
    show ({ fdS5 s0 tvs with regs := (fdS5 s0 tvs).wr 7 _ } : LP).rd 8 = _
    rw [lp_rd_wr (r := 8) (r' := 7) (by decide)]
    show ({ fdS3 s0 tvs with regs := (fdS3 s0 tvs).wr 7 _ } : LP).rd 8 = _
    rw [lp_rd_wr (r := 8) (r' := 7) (by decide)]
    exact lp_rd_wr (r := 8) (r' := 5) (by decide)
  have hya' : aligned (((fdS7 s0 tvs).rd 8 + 0) % two64) 4 = true := by
    rw [hy7, Nat.add_zero, Nat.mod_eq_of_lt hyl]; simp [aligned, hya]
  have hyy : ((((fdS7 s0 tvs).rd 8 + 0) % two64 : Nat) : Int) = (y : Int) := by
    rw [hy7, Nat.add_zero, Nat.mod_eq_of_lt hyl]
  iapply (wpH_store (s := fdS7 s0 tvs) (aq := false) (rl := false) (base := (y : Int))
    (data := toBytes ((fdS7 s0 tvs).rd 7) 4) (asrc := [.DReg 8]) (vsrc := [.DReg 7]) (k := fdS8 s0 tvs)
    (litDone_pc (s := fdS7 s0 tvs) (by simp [fdS7, fdS6, fdS5, fdS4, fdS3, ldS1, hprog, hpc]))
    (fun l s' hs => by
      obtain ⟨h1, h2⟩ := litNext_store (s := fdS7 s0 tvs) (sz := 4) (rs2 := 7) (rs1 := 8) (off := 0) rfl
        (by simp [fdS7, fdS6, fdS5, fdS4, fdS3, ldS1, hprog, hpc]) hya' (anyFab_lit.1 hs)
      exact ⟨by rw [h1, hyy]; rfl, h2⟩))
  iframe Hst
  inext
  iintro %ts %_ %_ %_ %hext _
  have hlt : ∀ e ∈ ((((((([] : Trace) ++ [(LLoad false false (x : Int) tvs [.DReg 6], none)]) ++
      [(LRegW 5 [.DLdRes], none)]) ++ [(LInstr, none)]) ++ [(LRegW 7 [.DReg 5, .DReg 5], none)]) ++
      [(LInstr, none)]) ++ [(LRegW 7 [.DReg 7], none)]) ++ [(LInstr, none)],
      ∀ aq rl base tv tvs' asrc, e.1 = LLoad aq rl base (tv :: tvs') asrc → tv.1 < ts := by
    intro e he aq rl base tv tvs' asrc hl
    simp only [List.nil_append, List.mem_append, List.mem_singleton] at he
    rcases he with ((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
    · simp only [LLoad.injEq] at hl
      obtain ⟨_, _, _, rfl, _⟩ := hl
      refine Nat.lt_of_le_of_lt ?_ (Nat.lt_of_le_of_lt (store_ext _ _ _ _ _) hext)
      refine Nat.le_trans ?_ (Nat.le_max_right _ _)
      have key : tv.1 ≤ (loadRun psInit false false (srcsView psInit [.DReg 6]) (x : Int) (tv :: tvs')).wLdv :=
        loadRun_ldv0 (fwdHit_empty lookupEmpty)
      rw [srcsView_reg, regv_instr, regv_regW, srcsView_reg, regv_instr, regv_regW, srcsView_cons]
      refine Nat.le_trans ?_ (Nat.le_max_left _ _)
      show tv.1 ≤ regv _ 5
      rw [regv_instr, regv_regW, srcsView_ldres]
      exact key
    all_goals cases hl
  have hnt7 : ∀ e ∈ ((((((([] : Trace) ++ [(LLoad false false (x : Int) tvs [.DReg 6], none)]) ++
      [(LRegW 5 [.DLdRes], none)]) ++ [(LInstr, none)]) ++ [(LRegW 7 [.DReg 5, .DReg 5], none)]) ++
      [(LInstr, none)]) ++ [(LRegW 7 [.DReg 7], none)]) ++ [(LInstr, none)], e.2 = none := by
    intro e he
    simp only [List.nil_append, List.mem_append, List.mem_singleton] at he
    rcases he with ((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) <;> rfl
  have ψ8 := psiLB_store ψ7 hnt7 false false (toBytes ((fdS7 s0 tvs).rd 7) 4) [.DReg 8] [.DReg 7] ts
    (toBytes_length _ _) hlt
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ8⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro Hst
  iapply (wpH_instr (s := fdS8 s0 tvs) (litDone_q (s := fdS8 s0 tvs) (by simp [fdS8]))
    (fun l s' hs => litNext_q rfl (anyFab_lit.1 hs)))
  iframe Hst
  inext
  iintro _
  have ψ9 := psiLB_quiet ψ8 _ loadLike_instr (fun _ _ _ _ _ _ h => by cases h)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ9⟩
  iintro Hst
  iapply (wpH_done (v := ()) (s := fdS9 s0 tvs)
    (by simp [litDone, fdS9, fdS8, fdS7, fdS6, fdS5, fdS4, fdS3, ldS1, hprog, hpc])
    (fun l s' hs => by
      rw [anyFab_lit, litNext_end rfl (by simp [fdS9, fdS8, fdS7, fdS6, fdS5, fdS4, fdS3, ldS1, hprog, hpc])] at hs
      cases hs))
  iframe Hst
  iintro _
  imodintro
  ipureintro
  exact ⟨0, grd_intro trivial⟩

/-- The LB+ctrl hart's states after `bne` (C4), its `LInstr` (C5), the store (C6), its `LInstr` (C7). -/
@[reducible] def ctS4 (s0 : LP) (tvs : List (Nat × BitVec 8)) : LP :=
  { fdS3 s0 tvs with
      pc := if brEval Weak.Prom.Ref.BrC.ne ((fdS3 s0 tvs).rd 5) ((fdS3 s0 tvs).rd 0) then 2 else (fdS3 s0 tvs).pc + 1,
      q := [LInstr] }
@[reducible] def ctS5 (s0 : LP) (tvs : List (Nat × BitVec 8)) : LP := { ctS4 s0 tvs with q := [] }
@[reducible] def ctS6 (s0 : LP) (tvs : List (Nat × BitVec 8)) : LP :=
  { ctS5 s0 tvs with pc := (ctS5 s0 tvs).pc + 1, q := [LInstr] }
@[reducible] def ctS7 (s0 : LP) (tvs : List (Nat × BitVec 8)) : LP := { ctS6 s0 tvs with q := [] }

theorem vcap_le_stPreA (ws : PState) (aq rl : Bool) (va vd : Nat) : ws.wVcap ≤ stPreA ws aq rl va vd := by
  unfold stPreA stPre; omega

/-- **The LB+ctrl hart in the logic** (plan §2 "LB+ctrl", rule 11): `lw a0,(x); bne a0,x0,L; L: sw t,(y)`.  The
branch emits `LCtrl [a0]`, so `vcap ≥ regv a0 ≥ s`, and the store's pre-view contains `vcap`: `s ≤ vcap ≤ pv < t`.
Both branch outcomes reach the same store (the target is the next instruction). -/
theorem lbctrl_hart (s0 : LP) (x y : Nat) (img : Image) (M : List PMsg) (h : Nat)
    (hprog : s0.prog = [.load 4 true 5 6 0, .br .ne 5 0 2, .store 4 7 8 0]) (hpc : s0.pc = 0)
    (hq : s0.q = []) (hx : s0.rd 6 = x) (hy : s0.rd 8 = y) (hxa : x % 4 = 0) (hya : y % 4 = 0) (hxl : x < two64)
    (hyl : y < two64) :
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩ (ΨLB x y 4) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  unfold wpPF
  iintro %γ %P0 %_ Hst
  have hxa' : aligned ((s0.rd 6 + 0) % two64) 4 = true := by
    rw [hx, Nat.add_zero, Nat.mod_eq_of_lt hxl]; simp [aligned, hxa]
  have hxx : (((s0.rd 6 + 0) % two64 : Nat) : Int) = (x : Int) := by rw [hx, Nat.add_zero, Nat.mod_eq_of_lt hxl]
  iapply (wpH_load (s := s0) (aq := false) (rl := false) (base := (x : Int)) (asrc := [.DReg 6])
    (k := ldS1 s0 5) (C := fun tvs => tvs.length = 4) (litDone_pc (by rw [hprog, hpc]; decide))
    (fun l s' hs => by
      obtain ⟨tvs, h1, h2, h3⟩ := litNext_load hq (by rw [hprog, hpc]; rfl) hxa' (anyFab_lit.1 hs)
      exact ⟨tvs, by rw [h1, hxx]; rfl, h2, h3⟩))
  iframe Hst
  inext
  iintro %tvs %hC %hlo _
  have ψ1 := psiLB_load (psiLB_nil (x : Int) (y : Int) 4) (fun _ h => by cases h) tvs [.DReg 6] hC
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ1⟩
  iintro Hst
  have hq1 : (ldS1 s0 5 tvs).q = LRegW 5 [.DLdRes] :: [LInstr] := by simp [regWL]
  iapply (wpH_regw (s := ldS1 s0 5 tvs) (rd := 5) (srcs := [.DLdRes]) (litDone_q (by rw [hq1]; simp))
    (fun l s' hs => litNext_q hq1 (anyFab_lit.1 hs)))
  iframe Hst
  inext
  iintro _
  have ψ2 := psiLB_quiet ψ1 _ (loadLike_regw 5 [.DLdRes]) (fun _ _ _ _ _ _ h => by cases h)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ2⟩
  iintro Hst
  iapply (wpH_instr (s := { ldS1 s0 5 tvs with q := [LInstr] })
    (litDone_q (s := { ldS1 s0 5 tvs with q := [LInstr] }) (by simp))
    (fun l s' hs => litNext_q rfl (anyFab_lit.1 hs)))
  iframe Hst
  inext
  iintro _
  have ψ3 := psiLB_quiet ψ2 _ loadLike_instr (fun _ _ _ _ _ _ h => by cases h)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ3⟩
  iintro Hst
  -- `bne a0,x0,L`: `LCtrl [a0]` (rule 11)
  iapply (wpH_ctrl (s := fdS3 s0 tvs) (srcs := [.DReg 5]) (k := ctS4 s0 tvs)
    (litDone_pc (s := fdS3 s0 tvs) (by simp [hprog, hpc]))
    (fun l s' hs => by
      obtain ⟨h1, h2⟩ := litNext_br (s := fdS3 s0 tvs) (c := .ne) (rs1 := 5) (rs2 := 0) (tgt := 2) rfl
        (by simp [hprog, hpc]) (by simp [hprog, hpc]) (anyFab_lit.1 hs)
      exact ⟨h1, h2⟩))
  iframe Hst
  inext
  iintro _
  have ψ4 := psiLB_quiet ψ3 (LCtrl [.DReg 5]) rfl (fun _ _ _ _ _ _ h => by cases h)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ4⟩
  iintro Hst
  iapply (wpH_instr (s := ctS4 s0 tvs) (litDone_q (s := ctS4 s0 tvs) (by simp))
    (fun l s' hs => litNext_q rfl (anyFab_lit.1 hs)))
  iframe Hst
  inext
  iintro _
  have ψ5 := psiLB_quiet ψ4 _ loadLike_instr (fun _ _ _ _ _ _ h => by cases h)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ5⟩
  iintro Hst
  -- `sw t,(y)`: the pre-view contains `vcap`
  have hpc5 : (ctS5 s0 tvs).pc = 2 := by simp [hpc]
  have hy5 : (ctS5 s0 tvs).rd 8 = y := by
    rw [← hy]; exact lp_rd_wr (s := s0) (r := 8) (r' := 5) (by decide)
  have hya' : aligned (((ctS5 s0 tvs).rd 8 + 0) % two64) 4 = true := by
    rw [hy5, Nat.add_zero, Nat.mod_eq_of_lt hyl]; simp [aligned, hya]
  have hyy : ((((ctS5 s0 tvs).rd 8 + 0) % two64 : Nat) : Int) = (y : Int) := by
    rw [hy5, Nat.add_zero, Nat.mod_eq_of_lt hyl]
  iapply (wpH_store (s := ctS5 s0 tvs) (aq := false) (rl := false) (base := (y : Int))
    (data := toBytes ((ctS5 s0 tvs).rd 7) 4) (asrc := [.DReg 8]) (vsrc := [.DReg 7]) (k := ctS6 s0 tvs)
    (litDone_pc (s := ctS5 s0 tvs) (by rw [hpc5]; simp [hprog]))
    (fun l s' hs => by
      obtain ⟨h1, h2⟩ := litNext_store (s := ctS5 s0 tvs) (sz := 4) (rs2 := 7) (rs1 := 8) (off := 0) rfl
        (by rw [hpc5]; simp [hprog]) hya' (anyFab_lit.1 hs)
      exact ⟨by rw [h1, hyy]; rfl, h2⟩))
  iframe Hst
  inext
  iintro %ts %_ %_ %_ %hext _
  have hlt : ∀ e ∈ ((((([] : Trace) ++ [(LLoad false false (x : Int) tvs [.DReg 6], none)]) ++
      [(LRegW 5 [.DLdRes], none)]) ++ [(LInstr, none)]) ++ [(LCtrl [.DReg 5], none)]) ++ [(LInstr, none)],
      ∀ aq rl base tv tvs' asrc, e.1 = LLoad aq rl base (tv :: tvs') asrc → tv.1 < ts := by
    intro e he aq rl base tv tvs' asrc hl
    simp only [List.nil_append, List.mem_append, List.mem_singleton] at he
    rcases he with ((((rfl | rfl) | rfl) | rfl) | rfl)
    · simp only [LLoad.injEq] at hl
      obtain ⟨_, _, _, rfl, _⟩ := hl
      refine Nat.lt_of_le_of_lt ?_ (Nat.lt_of_le_of_lt (vcap_le_stPreA _ _ _ _ _) hext)
      have key : tv.1 ≤ (loadRun psInit false false (srcsView psInit [.DReg 6]) (x : Int) (tv :: tvs')).wLdv :=
        loadRun_ldv0 (fwdHit_empty lookupEmpty)
      refine Nat.le_trans ?_ (Nat.le_max_left _ _)
      rw [srcsView_reg, regv_instr, regv_regW, srcsView_ldres]
      exact key
    all_goals cases hl
  have hnt : ∀ e ∈ ((((([] : Trace) ++ [(LLoad false false (x : Int) tvs [.DReg 6], none)]) ++
      [(LRegW 5 [.DLdRes], none)]) ++ [(LInstr, none)]) ++ [(LCtrl [.DReg 5], none)]) ++ [(LInstr, none)],
      e.2 = none := by
    intro e he
    simp only [List.nil_append, List.mem_append, List.mem_singleton] at he
    rcases he with ((((rfl | rfl) | rfl) | rfl) | rfl) <;> rfl
  have ψ6 := psiLB_store ψ5 hnt false false (toBytes ((ctS5 s0 tvs).rd 7) 4) [.DReg 8] [.DReg 7] ts
    (toBytes_length _ _) hlt
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ6⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro Hst
  iapply (wpH_instr (s := ctS6 s0 tvs) (litDone_q (s := ctS6 s0 tvs) (by simp))
    (fun l s' hs => litNext_q rfl (anyFab_lit.1 hs)))
  iframe Hst
  inext
  iintro _
  have ψ7 := psiLB_quiet ψ6 _ loadLike_instr (fun _ _ _ _ _ _ h => by cases h)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ7⟩
  iintro Hst
  have hpc7 : (ctS7 s0 tvs).pc = 3 := by simp [hpc]
  iapply (wpH_done (v := ()) (s := ctS7 s0 tvs) (by simp [litDone, hprog, hpc])
    (fun l s' hs => by
      rw [anyFab_lit, litNext_end rfl (by simp [hprog, hpc])] at hs
      cases hs))
  iframe Hst
  iintro _
  imodintro
  ipureintro
  exact ⟨0, grd_intro trivial⟩

end hart

/-! ## 2. The verdicts -/

open Weak.Prom.Ref.Lit (X Y)

/-- Ψ of the two-hart LB rows: (P0)–(P4) at `x`/`y` for hart 0, swapped for hart 1, the empty trace for every other
hart index (no program). -/
def ΨLB2 (x y : Int) : Nat → Trace → Prop
  | 0 => ΨLB x y 4
  | 1 => ΨLB y x 4
  | _ => fun τ => τ = []

theorem ΨLB2_nil (x y : Int) : ∀ h, ΨLB2 x y h []
  | 0 => psiLB_nil _ _ _
  | 1 => psiLB_nil _ _ _
  | _ + 2 => rfl

theorem devFree_lit (ps : List LP) : devFreeProg litStep ps := by
  intro _ _ _ _ _ d l p' d' hs
  cases d; cases d'
  exact ⟨rfl, fun d0 => by cases d0; exact hs⟩

theorem byteAt_YX (m : PMsg) (hpa : m.pa = (Y : Int)) : m.byteAt (X : Int) = none := by
  unfold PMsg.byteAt; rw [hpa, if_neg (by decide)]

theorem byteAt_XY (m : PMsg) (hpa : m.pa = (X : Int)) (hl : m.data.length = 4) : m.byteAt (Y : Int) = none := by
  unfold PMsg.byteAt; rw [hpa, if_pos (by decide)]
  apply List.getElem?_eq_none; rw [hl]; decide

/-- From A0 for a two-hart LB-shaped test: the contradiction of plan §2, given the two harts' wps. -/
theorem lb_verdict {T : Test} {M : List PMsg} {run : PFRun LP Unit}
    (hrun : validRun litStep (testImg T) () (progs T) M run)
    (hx0 : testImg T (X : Int) = some 0) (hy0 : testImg T (Y : Int) = some 0)
    (hwp : ∀ h p, (progs T)[h]? = some p → ∀ [InvGS_gen HasLC.hasLC pfGF],
      ⊢@{IProp pfGF} wpPF Proto.triv ⟨litStep, litDone, testImg T, M, h⟩ (ΨLB2 X Y h) p
        (fun v => iprop(⌜∃ V, grd Proto.triv (testImg T) M V ((fun (_ : Nat) (_ : Unit) => True) h v)⌝))) :
    ¬ (run.obsLoad 0 0 = some 1 ∧ run.obsLoad 1 0 = some 1) := by
  obtain ⟨_, hii, hpart, _, _, hwf, _⟩ := adequacy (hlc := HasLC.hasLC) (GF := pfGF) (pdone := litDone)
    Proto.triv (fun _ _ => True) (ΨLB2 X Y) trivial (PO_ad_all _ _ _) (ΨLB2_nil _ _) (devFree_lit _) hwp hrun
  have himg : run.cfg.pcImg = testImg T := validRun_img hrun.1
  have hfin : ∀ h, ΨLB2 X Y h (run.trace h) := fun h => by simpa using hii h (run.trace h).length
  refine lb_contra himg hx0 hy0 (fun m hpa _ => byteAt_YX m hpa) (fun m hpa hl => byteAt_XY m hpa hl)
    (hfin 0) (hfin 1) (fun h h2 => ?_) hpart hwf
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 2 := ⟨h - 2, by omega⟩
  exact hfin (n + 2)

/-- **ROW 2, LB+data+data: FORBIDDEN, in the logic** (plan §0 `LBdd.forbidden`, §2 derivation).  Over every final
memory and every valid run of machine v2: not both 0th loads return 1. -/
theorem lit_lbdd : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.lbdd) () (progs Weak.Prom.Ref.Lit.lbdd) M run →
    ¬ (run.obsLoad 0 0 = some 1 ∧ run.obsLoad 1 0 = some 1) := by
  intro M run hrun
  refine lb_verdict hrun rfl rfl (fun h p hp _ => ?_)
  have hlen : (progs Weak.Prom.Ref.Lit.lbdd).length = 2 := rfl
  match h, hp with
  | 0, hp =>
    rw [List.getElem?_eq_getElem (by rw [hlen]; decide)] at hp
    cases hp
    exact lbdd_hart _ X Y _ M 0 rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
  | 1, hp =>
    rw [List.getElem?_eq_getElem (by rw [hlen]; decide)] at hp
    cases hp
    exact lbdd_hart _ Y X _ M 1 rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
  | n + 2, hp =>
    rw [List.getElem?_eq_none (by rw [hlen]; omega)] at hp
    cases hp

/-- **ROW 3, LB+fakedep (repository `LB+datas`): FORBIDDEN, in the logic** (plan §2 derivation; Promising'17
allows it, RVWMO forbids it through syntactic dependencies).  Over every final memory and every valid run of
machine v2: not both 0th loads return 1. -/
theorem lit_lbfd : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.lbDatas) () (progs Weak.Prom.Ref.Lit.lbDatas) M run →
    ¬ (run.obsLoad 0 0 = some 1 ∧ run.obsLoad 1 0 = some 1) := by
  intro M run hrun
  refine lb_verdict hrun rfl rfl (fun h p hp _ => ?_)
  have hlen : (progs Weak.Prom.Ref.Lit.lbDatas).length = 2 := rfl
  match h, hp with
  | 0, hp =>
    rw [List.getElem?_eq_getElem (by rw [hlen]; decide)] at hp
    cases hp
    exact lbfd_hart _ X Y _ M 0 rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
  | 1, hp =>
    rw [List.getElem?_eq_getElem (by rw [hlen]; decide)] at hp
    cases hp
    exact lbfd_hart _ Y X _ M 1 rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
  | n + 2, hp =>
    rw [List.getElem?_eq_none (by rw [hlen]; omega)] at hp
    cases hp

/-- **ROW 4, LB+ctrl+ctrl (repository `LB+ctrls`): FORBIDDEN, in the logic** (plan §2 "LB+ctrl", rule 11). -/
theorem lit_lbctrl : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.lbCtrls) () (progs Weak.Prom.Ref.Lit.lbCtrls) M run →
    ¬ (run.obsLoad 0 0 = some 1 ∧ run.obsLoad 1 0 = some 1) := by
  intro M run hrun
  refine lb_verdict hrun rfl rfl (fun h p hp _ => ?_)
  have hlen : (progs Weak.Prom.Ref.Lit.lbCtrls).length = 2 := rfl
  match h, hp with
  | 0, hp =>
    rw [List.getElem?_eq_getElem (by rw [hlen]; decide)] at hp
    cases hp
    exact lbctrl_hart _ X Y _ M 0 rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
  | 1, hp =>
    rw [List.getElem?_eq_getElem (by rw [hlen]; decide)] at hp
    cases hp
    exact lbctrl_hart _ Y X _ M 1 rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
  | n + 2, hp =>
    rw [List.getElem?_eq_none (by rw [hlen]; omega)] at hp
    cases hp

/-- **ROW 1, LB: ALLOWED — the logic does not forbid it** (plan §2 "LB (ALLOWED)"; S2 states it as machine v2's
certificate plus a remark).  `mach_lb` (MachCerts.lean) is a valid run of `Lit.lb` reaching `a0 = a1 = 1`: both
harts read the other's not-yet-executed store (`WPPromise` first; each load returns the other hart's promised
message; each store fulfils with `pv = 0 < t`).

Why no proof in the logic can exclude it: the only order fact a hart can record about its store is (X6) `pv < t`,
and here `pv` does not contain the load's view (`sw t,(y)` has sources `[x8]`, `[x7]`, neither written from the
load, and no `LCtrl`), so no Ψ the hart proves at every step can relate its load's source `s` to its fulfil `t`;
the run above (`s0 = 2 > t0 = 1`) satisfies every Ψ either hart can prove, and A0 holds of it like of every valid
run.  The forbidding contradiction `lb_contra` needs exactly (P3) `s < t`, which rows 2–4 prove from (X4)–(X6) and
row 1 cannot. -/
theorem lit_lb_allowed : allowedMach Weak.Prom.Ref.Lit.lb := Weak.Prom.Mach.Certs.mach_lb

end Weak.Prom.PF

