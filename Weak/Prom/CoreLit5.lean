/-
Weak/Prom: **row 5, LB+lrsc, proved IN THE LOGIC** (stage S2; plan rev 7 §5 row 5, §8 S2 K2c).

The manual's `litmus_lb_lrsc` (mm-explanatory.adoc:932–948, `Lit.lbLrsc` of RefTests.lean): init `(x) = (z) = 1`;
H0 `ld a0,(x); lr.d a1,(y); sc.d a2,a0,(y); sd a2,(z)` ‖ H1 `ld a3,(z); sd a3,(x)`; outcome `a0 = 0 ∧ a3 = 0`
FORBIDDEN (manual: "outcome forbidden"; the dependency is through the SUCCESSFUL SC's result register, M4).
Row 5 is not vacuous: S1M's row-31 witness `mach_lrsc` (MachCerts.lean) shows an SC can succeed on machine v2.

The derivation (in the style of §2's rows 2–3):
* H1 is an LB+data hart (8 bytes, `ld a3,(z); sd a3,(x)`): Ψ = (P0)–(P4) at `z`/`x` (`ΨLB z x 8`), proved by
  `lb8_hart` exactly as rows 2–3: (X4)–(X6) give `s1 < t1`.
* H0's Ψ is `ΨLS` (CoreLitBase.lean): (Q0) every timestamped entry is an `st` or an `exst`; (Q1) every `st` is at
  `z`, every `exst` at `y`, 8 bytes; (Q3) every `ld`'s byte-0 source is below every `st` whose byte 0 is 0; (Q4) the
  0th load-like entry is an 8-byte `ld` at `x`.  (Q3) is the SC's dependency: on the success branch the SC's EXT
  gives `s0 ≤ regv a0 ≤ pv_sc < t_sc`, the success register's view is `≥ t_sc` (M4, `wLdv ⊔= ts`, then
  `LRegW a2 [DLdRes]`), so the `sd a2,(z)` has `t_sc ≤ vd ≤ pv < t_z`; on the failure branch `a2 = 1`, so the
  `st`'s byte 0 is 1 and (Q3) is vacuous.  Ψ speaks of the value because the failure branch has no dependency.
* `lrsc_contra` (CoreLitBase.lean): H0's `ld x` read 0 (the image holds 1) from H1's `sd x` (`s0 = t1`); H1's
  `ld z` read 0 from H0's `sd z` with byte 0 = 0 (`s1 = t_z`); so `t1 = s0 < t_z = s1 < t1`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreLit

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

section hart

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [InvGS_gen hlc GF]

/-- The hart state after an `sz`-byte signed load into `rd`. -/
@[reducible] def ldSz (s0 : LP) (sz rd : Nat) (tvs : List (Nat × BitVec 8)) : LP :=
  { s0 with regs := s0.wr rd (if true then sext sz (ofBytes (tvs.map Prod.snd)) else ofBytes (tvs.map Prod.snd)),
            pc := s0.pc + 1, q := regWL rd [.DLdRes] ++ [LInstr] }

@[reducible] def ldSz3 (s0 : LP) (sz rd : Nat) (tvs : List (Nat × BitVec 8)) : LP :=
  { { ldSz s0 sz rd tvs with q := [LInstr] } with q := [] }

theorem regv_setRes (ws : PState) (x : Option PResv) (r : Nat) : regv { ws with wRes := x } r = regv ws r := rfl

/-- **An 8-byte LB+data hart in the logic** (H1 of row 5): `ld rd,(ra); sd rd,(rb)`, as `lbdd_hart`. -/
theorem lb8_hart (s0 : LP) (rd ra rb x y : Nat) (img : Image) (M : List PMsg) (h : Nat)
    (hprog : s0.prog = [.load 8 true rd ra 0, .store 8 rd rb 0]) (hpc : s0.pc = 0) (hq : s0.q = [])
    (hrd : rd ≠ 0) (hrb : rb ≠ rd) (hra0 : ra ≠ 0) (hrb0 : rb ≠ 0)
    (hx : s0.rd ra = x) (hy : s0.rd rb = y) (hxa : x % 8 = 0) (hya : y % 8 = 0) (hxl : x < two64)
    (hyl : y < two64) :
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩ (ΨLB x y 8) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  unfold wpPF
  iintro %γ %P0 %_ Hst
  have hxa' : aligned ((s0.rd ra + 0) % two64) 8 = true := by
    rw [hx, Nat.add_zero, Nat.mod_eq_of_lt hxl]; simp [aligned, hxa]
  have hxx : (((s0.rd ra + 0) % two64 : Nat) : Int) = (x : Int) := by rw [hx, Nat.add_zero, Nat.mod_eq_of_lt hxl]
  have hsra : srcR ra = [.DReg ra] := by simp [srcR, hra0]
  have hsrb : srcR rb = [.DReg rb] := by simp [srcR, hrb0]
  have hsrd : srcR rd = [.DReg rd] := by simp [srcR, hrd]
  iapply (wpH_load (s := s0) (aq := false) (rl := false) (base := (x : Int)) (asrc := [.DReg ra])
    (k := ldSz s0 8 rd) (C := fun tvs => tvs.length = 8) (litDone_pc (by rw [hprog, hpc]; simp))
    (fun l s' hs => by
      obtain ⟨tvs, h1, h2, h3⟩ := litNext_load hq (by rw [hprog, hpc]; rfl) hxa' (anyFab_lit.1 hs)
      exact ⟨tvs, by rw [h1, hxx, hsra], h2, h3⟩))
  iframe Hst
  inext
  iintro %tvs %hC %hlo _
  have ψ1 := psiLB_load (psiLB_nil (x : Int) (y : Int) 8) (fun _ h => by cases h) tvs [.DReg ra] hC
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ1⟩
  iintro Hst
  have hq1 : (ldSz s0 8 rd tvs).q = LRegW rd [.DLdRes] :: [LInstr] := by simp [regWL, hrd]
  iapply (wpH_regw (s := ldSz s0 8 rd tvs) (rd := rd) (srcs := [.DLdRes]) (litDone_q (by rw [hq1]; simp))
    (fun l s' hs => litNext_q hq1 (anyFab_lit.1 hs)))
  iframe Hst
  inext
  iintro _
  have ψ2 := psiLB_quiet ψ1 _ (loadLike_regw rd [.DLdRes]) (fun _ _ _ _ _ _ h => by cases h)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ2⟩
  iintro Hst
  iapply (wpH_instr (s := { ldSz s0 8 rd tvs with q := [LInstr] })
    (litDone_q (s := { ldSz s0 8 rd tvs with q := [LInstr] }) (by simp))
    (fun l s' hs => litNext_q rfl (anyFab_lit.1 hs)))
  iframe Hst
  inext
  iintro _
  have ψ3 := psiLB_quiet ψ2 _ loadLike_instr (fun _ _ _ _ _ _ h => by cases h)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ3⟩
  iintro Hst
  have hy3 : (ldSz3 s0 8 rd tvs).rd rb = y := by
    rw [← hy]; exact lp_rd_wr (s := s0) (r := rb) (r' := rd) hrb
  have hya' : aligned (((ldSz3 s0 8 rd tvs).rd rb + 0) % two64) 8 = true := by
    rw [hy3, Nat.add_zero, Nat.mod_eq_of_lt hyl]; simp [aligned, hya]
  have hyy : ((((ldSz3 s0 8 rd tvs).rd rb + 0) % two64 : Nat) : Int) = (y : Int) := by
    rw [hy3, Nat.add_zero, Nat.mod_eq_of_lt hyl]
  iapply (wpH_store (s := ldSz3 s0 8 rd tvs) (aq := false) (rl := false) (base := (y : Int))
    (data := toBytes ((ldSz3 s0 8 rd tvs).rd rd) 8) (asrc := [.DReg rb]) (vsrc := [.DReg rd])
    (k := { ldSz3 s0 8 rd tvs with pc := (ldSz3 s0 8 rd tvs).pc + 1, q := [LInstr] })
    (litDone_pc (s := ldSz3 s0 8 rd tvs) (by simp [hprog, hpc]))
    (fun l s' hs => by
      obtain ⟨h1, h2⟩ := litNext_store (s := ldSz3 s0 8 rd tvs) (sz := 8) (rs2 := rd) (rs1 := rb) (off := 0) rfl
        (by simp [hprog, hpc]) hya' (anyFab_lit.1 hs)
      exact ⟨by rw [h1, hyy, hsrb, hsrd], h2⟩))
  iframe Hst
  inext
  iintro %ts %_ %_ %_ %hext _
  have hlt : ∀ e ∈ ((([] : Trace) ++ [(LLoad false false (x : Int) tvs [.DReg ra], none)]) ++
      [(LRegW rd [.DLdRes], none)]) ++ [(LInstr, none)],
      ∀ aq rl base tv tvs' asrc, e.1 = LLoad aq rl base (tv :: tvs') asrc → tv.1 < ts := by
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
  have hnt : ∀ e ∈ ((([] : Trace) ++ [(LLoad false false (x : Int) tvs [.DReg ra], none)]) ++
      [(LRegW rd [.DLdRes], none)]) ++ [(LInstr, none)], e.2 = none := by
    intro e he
    simp only [List.nil_append, List.mem_append, List.mem_singleton] at he
    rcases he with (rfl | rfl) | rfl <;> rfl
  have ψ4 := psiLB_store ψ3 hnt false false (toBytes ((ldSz3 s0 8 rd tvs).rd rd) 8) [.DReg rb] [.DReg rd] ts
    (toBytes_length _ _) hlt
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ4⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro Hst
  iapply (wpH_instr (s := { ldSz3 s0 8 rd tvs with pc := (ldSz3 s0 8 rd tvs).pc + 1, q := [LInstr] })
    (litDone_q (s := { ldSz3 s0 8 rd tvs with pc := (ldSz3 s0 8 rd tvs).pc + 1, q := [LInstr] }) (by simp))
    (fun l s' hs => litNext_q rfl (anyFab_lit.1 hs)))
  iframe Hst
  inext
  iintro _
  have ψ5 := psiLB_quiet ψ4 _ loadLike_instr (fun _ _ _ _ _ _ h => by cases h)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ5⟩
  iintro Hst
  iapply (wpH_done (v := ()) (s := { { ldSz3 s0 8 rd tvs with pc := (ldSz3 s0 8 rd tvs).pc + 1, q := [LInstr] }
      with q := [] }) (by simp [litDone, hprog, hpc])
    (fun l s' hs => by
      rw [anyFab_lit, litNext_end rfl (by simp [hprog, hpc])] at hs
      cases hs))
  iframe Hst
  iintro _
  imodintro
  ipureintro
  exact ⟨0, grd_intro trivial⟩

/-- The program of row 5's H0. -/
def lsProg : List Instr := [.load 8 true 10 8 0, .lr 8 false false 11 9, .sc 8 false false 12 10 9, .store 8 12 18 0]

/-- "Every `ld` entry's byte-0 source is at most `B`". -/
def ldBelow (B : Nat) (e : PEv) : Prop := ∀ aq rl base tv tvs asrc, e.1 = LLoad aq rl base (tv :: tvs) asrc → tv.1 ≤ B

theorem forall_snoc {Q : PEv → Prop} {τ : Trace} {e : PEv} (h : ∀ e ∈ τ, Q e) (he : Q e) :
    ∀ e' ∈ τ ++ [e], Q e' := by
  intro e' he'
  rcases mem_snoc he' with he' | rfl
  · exact h e' he'
  · exact he

theorem ldBelow_regw (B rd : Nat) (srcs : List Dsrc) : ldBelow B (LRegW rd srcs, none) := by
  intro _ _ _ _ _ _ h; cases h
theorem ldBelow_instr (B : Nat) : ldBelow B (LInstr, none) := by intro _ _ _ _ _ _ h; cases h
theorem ldBelow_exfail (B : Nat) : ldBelow B (LExFail, none) := by intro _ _ _ _ _ _ h; cases h

theorem psiLS_regw {x y z : Int} {τ : Trace} (h : ΨLS x y z τ) (rd : Nat) (srcs : List Dsrc) :
    ΨLS x y z (τ ++ [(LRegW rd srcs, none)]) :=
  psiLS_quiet h _ rfl (fun _ _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ h => by cases h)
theorem psiLS_instr {x y z : Int} {τ : Trace} (h : ΨLS x y z τ) : ΨLS x y z (τ ++ [(LInstr, none)]) :=
  psiLS_quiet h _ rfl (fun _ _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ h => by cases h)
theorem psiLS_exfail {x y z : Int} {τ : Trace} (h : ΨLS x y z τ) : ΨLS x y z (τ ++ [(LExFail, none)]) :=
  psiLS_quiet h _ rfl (fun _ _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ h => by cases h)

/-- **The tail of row 5's H0**: from `pc = 3` (after the SC), `sd a2,(z)`, its `LInstr`, the end.  If the stored
byte 0 is 0, the store's data view (`regv a2`) is above every `ld`'s byte-0 source bound `B` (the SC's dependency,
success branch). -/
theorem lrsc_tail (T : LP) (x y z : Int) (zn : Nat) (img : Image) (M : List PMsg) (h : Nat) (B : Nat)
    (hprog : T.prog = lsProg) (hpc : T.pc = 3) (hq : T.q = []) (hz : T.rd 18 = zn) (hzz : (zn : Int) = z)
    (hza : zn % 8 = 0) (hzl : zn < two64)
    {γ : GName} {ws : PState} {pr : GSet Nat} {τ : Trace} (hψ : ΨLS x y z τ) (hld : ∀ e ∈ τ, ldBelow B e)
    (hB : (toBytes (T.rd 12) 8)[0]? = some 0 → B < srcsView ws [.DReg 12]) :
    hartSt γ ws pr τ ⊢@{IProp GF} wpH γ Proto.triv ⟨litStep, litDone, img, M, h⟩ (ΨLS x y z) T
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  iintro Hst
  have hza' : aligned ((T.rd 18 + 0) % two64) 8 = true := by
    rw [hz, Nat.add_zero, Nat.mod_eq_of_lt hzl]; simp [aligned, hza]
  have hzz' : (((T.rd 18 + 0) % two64 : Nat) : Int) = z := by rw [hz, Nat.add_zero, Nat.mod_eq_of_lt hzl, hzz]
  iapply (wpH_store (s := T) (aq := false) (rl := false) (base := z) (data := toBytes (T.rd 12) 8)
    (asrc := [.DReg 18]) (vsrc := [.DReg 12]) (k := { T with pc := T.pc + 1, q := [LInstr] })
    (litDone_pc (s := T) (by rw [hprog, hpc]; decide))
    (fun l s' hs => by
      obtain ⟨h1, h2⟩ := litNext_store (s := T) (sz := 8) (rs2 := 12) (rs1 := 18) (off := 0) hq
        (by rw [hprog, hpc]; rfl) hza' (anyFab_lit.1 hs)
      exact ⟨by rw [h1, hzz']; rfl, h2⟩))
  iframe Hst
  inext
  iintro %ts %_ %_ %_ %hext _
  have ψ1 := psiLS_st hψ false false (toBytes (T.rd 12) 8) [.DReg 18] [.DReg 12] ts (toBytes_length _ _)
    (fun hd e he aq rl base tv tvs asrc hl => by
      have h1 := hld e he aq rl base tv tvs asrc hl
      have h2 := hB hd
      have h3 := store_ext ws false false (srcsView ws [.DReg 18]) (srcsView ws [.DReg 12])
      omega)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ1⟩
  isplitr
  · ipureintro; exact grd_intro trivial
  iintro Hst
  iapply (wpH_instr (s := { T with pc := T.pc + 1, q := [LInstr] })
    (litDone_q (s := { T with pc := T.pc + 1, q := [LInstr] }) (by simp))
    (fun l s' hs => litNext_q rfl (anyFab_lit.1 hs)))
  iframe Hst
  inext
  iintro _
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro (psiLS_instr ψ1)⟩
  iintro Hst
  iapply (wpH_done (v := ()) (s := { { T with pc := T.pc + 1, q := [LInstr] } with q := [] })
    (by simp [litDone, hprog, hpc, lsProg])
    (fun l s' hs => by
      rw [anyFab_lit, litNext_end rfl (by simp [hprog, hpc, lsProg])] at hs
      cases hs))
  iframe Hst
  iintro _
  imodintro
  ipureintro
  exact ⟨0, grd_intro trivial⟩

/-- States of row 5's H0 after the LR (A4), its `LInstr` (A6), and the SC's two outcomes (S7 success, F7 failure). -/
@[reducible] def lrA4 (s0 : LP) (tvs tvs' : List (Nat × BitVec 8)) : LP :=
  { ldSz3 s0 8 10 tvs with
      regs := (ldSz3 s0 8 10 tvs).wr 11 (sext 8 (ofBytes (tvs'.map Prod.snd))),
      pc := (ldSz3 s0 8 10 tvs).pc + 1,
      q := regWL 11 [.DLdRes] ++ [LInstr] }
@[reducible] def lrA6 (s0 : LP) (tvs tvs' : List (Nat × BitVec 8)) : LP :=
  { { lrA4 s0 tvs tvs' with q := [LInstr] } with q := [] }
@[reducible] def scS7 (s0 : LP) (tvs tvs' : List (Nat × BitVec 8)) (b : Nat) (q : List PLabel) : LP :=
  { lrA6 s0 tvs tvs' with
      regs := (lrA6 s0 tvs tvs').wr 12 b,
      pc := (lrA6 s0 tvs tvs').pc + 1,
      q := q }

theorem lp_rd_wr_self {s : LP} {r v : Nat} (h0 : r ≠ 0) (hl : r < s.regs.length) :
    ({ s with regs := s.wr r v } : LP).rd r = v % two64 := by
  unfold LP.rd LP.wr
  simp only [h0, if_false]
  rw [List.getElem?_set_self hl]; rfl

theorem lp_rd_regs {s s' : LP} {r r' v : Nat} (h : s'.regs = s.wr r' v) (hne : r ≠ r') : s'.rd r = s.rd r := by
  have : s'.rd r = ({ s with regs := s.wr r' v } : LP).rd r := by unfold LP.rd; rw [h]
  rw [this, lp_rd_wr hne]

theorem lp_rd_regs_self {s s' : LP} {r v : Nat} (h : s'.regs = s.wr r v) (h0 : r ≠ 0) (hl : r < s.regs.length) :
    s'.rd r = v % two64 := by
  have : s'.rd r = ({ s with regs := s.wr r v } : LP).rd r := by unfold LP.rd; rw [h]
  rw [this, lp_rd_wr_self h0 hl]

/-- **Row 5's H0 in the logic**: `ld a0,(x); lr.d a1,(y); sc.d a2,a0,(y); sd a2,(z)` proves ΨLS (V = 0 throughout).
On the SC's success branch (Q3) comes from EXT and M4; on its failure branch the stored byte 0 is 1. -/
theorem lrsc_hart (s0 : LP) (x y z : Nat) (img : Image) (M : List PMsg) (h : Nat)
    (hprog : s0.prog = lsProg) (hpc : s0.pc = 0) (hq : s0.q = []) (hlen : 12 < s0.regs.length)
    (hx : s0.rd 8 = x) (hy : s0.rd 9 = y) (hz : s0.rd 18 = z) (hxa : x % 8 = 0) (hya : y % 8 = 0)
    (hza : z % 8 = 0) (hxl : x < two64) (hzl : z < two64) :
    ⊢@{IProp GF} wpPF Proto.triv ⟨litStep, litDone, img, M, h⟩ (ΨLS x y z) s0
      (fun _ => iprop(⌜∃ V, grd Proto.triv img M V True⌝)) := by
  unfold wpPF
  iintro %γ %P0 %_ Hst
  -- `ld a0,(x)`
  have hxa' : aligned ((s0.rd 8 + 0) % two64) 8 = true := by
    rw [hx, Nat.add_zero, Nat.mod_eq_of_lt hxl]; simp [aligned, hxa]
  have hxx : (((s0.rd 8 + 0) % two64 : Nat) : Int) = (x : Int) := by rw [hx, Nat.add_zero, Nat.mod_eq_of_lt hxl]
  iapply (wpH_load (s := s0) (aq := false) (rl := false) (base := (x : Int)) (asrc := [.DReg 8])
    (k := ldSz s0 8 10) (C := fun tvs => tvs.length = 8) (litDone_pc (by rw [hprog, hpc]; decide))
    (fun l s' hs => by
      obtain ⟨tvs, h1, h2, h3⟩ := litNext_load hq (by rw [hprog, hpc]; rfl) hxa' (anyFab_lit.1 hs)
      exact ⟨tvs, by rw [h1, hxx]; rfl, h2, h3⟩))
  iframe Hst
  inext
  iintro %tvs %hC %_ _
  obtain ⟨tv0, r0, rfl⟩ : ∃ tv r, tvs = tv :: r := by
    cases tvs with
    | nil => cases hC
    | cons tv r => exact ⟨tv, r, rfl⟩
  have ψ1 := psiLS_ld (psiLS_nil (x : Int) (y : Int) (z : Int)) rfl (fun _ h => by cases h) (tv0 :: r0) [.DReg 8] hC
  have hld1 : ∀ e ∈ ([] : Trace) ++ [(LLoad false false (x : Int) (tv0 :: r0) [.DReg 8], none)], ldBelow tv0.1 e := by
    intro e he aq rl base tv tvs asrc hl
    simp only [List.nil_append, List.mem_singleton] at he
    subst he
    simp only [LLoad.injEq, List.cons.injEq] at hl
    obtain ⟨_, _, _, ⟨rfl, _⟩, _⟩ := hl
    exact Nat.le_refl _
  have key : tv0.1 ≤ (loadRun psInit false false (srcsView psInit [.DReg 8]) (x : Int) (tv0 :: r0)).wLdv :=
    loadRun_ldv0 (fwdHit_empty lookupEmpty)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ1⟩
  iintro Hst
  -- `LRegW a0 [DLdRes]`, `LInstr`
  have hq1 : (ldSz s0 8 10 (tv0 :: r0)).q = LRegW 10 [.DLdRes] :: [LInstr] := by simp [regWL]
  iapply (wpH_regw (s := ldSz s0 8 10 (tv0 :: r0)) (rd := 10) (srcs := [.DLdRes]) (litDone_q (by rw [hq1]; simp))
    (fun l s' hs => litNext_q hq1 (anyFab_lit.1 hs)))
  iframe Hst
  inext
  iintro _
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro (psiLS_regw ψ1 _ _)⟩
  iintro Hst
  iapply (wpH_instr (s := { ldSz s0 8 10 (tv0 :: r0) with q := [LInstr] })
    (litDone_q (s := { ldSz s0 8 10 (tv0 :: r0) with q := [LInstr] }) (by simp))
    (fun l s' hs => litNext_q rfl (anyFab_lit.1 hs)))
  iframe Hst
  inext
  iintro _
  have ψ3 := psiLS_instr (psiLS_regw ψ1 10 [.DLdRes])
  have hld3 := forall_snoc (forall_snoc hld1 (ldBelow_regw tv0.1 10 [.DLdRes])) (ldBelow_instr tv0.1)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ3⟩
  iintro Hst
  -- `lr.d a1,(y)`
  have hy3 : (ldSz3 s0 8 10 (tv0 :: r0)).rd 9 = y := by
    rw [← hy]; exact lp_rd_wr (s := s0) (r := 9) (r' := 10) (by decide)
  have hyl' : aligned ((ldSz3 s0 8 10 (tv0 :: r0)).rd 9) 8 = true := by rw [hy3]; simp [aligned, hya]
  iapply (wpH_lr (s := ldSz3 s0 8 10 (tv0 :: r0)) (aq := false) (rl := false) (base := (y : Int))
    (asrc := [.DReg 9]) (k := lrA4 s0 (tv0 :: r0)) (C := fun _ => True)
    (litDone_pc (s := ldSz3 s0 8 10 (tv0 :: r0)) (by simp [hprog, hpc, lsProg]))
    (fun l s' hs => by
      obtain ⟨tvs', h1, h2, _⟩ := litNext_lr (s := ldSz3 s0 8 10 (tv0 :: r0)) (sz := 8) (rd := 11) (rs1 := 9) rfl
        (by simp [hprog, hpc, lsProg]) hyl' (anyFab_lit.1 hs)
      exact ⟨tvs', by rw [h1, hy3]; rfl, h2, trivial⟩))
  iframe Hst
  inext
  iintro %tvs' %_ %_ _
  have hnl : loadsOf (((([] : Trace) ++ [(LLoad false false (x : Int) (tv0 :: r0) [.DReg 8], none)]) ++
      [(LRegW 10 [.DLdRes], none)]) ++ [(LInstr, none)]) ≠ [] := by
    simp [loadsOf, loadLikeTvs]
  have ψ4 := psiLS_lr ψ3 hnl false false (y : Int) tvs' [.DReg 9]
  have hld4 := forall_snoc hld3 (e := (LExLoad false false (y : Int) tvs' [.DReg 9], none))
    (fun _ _ _ _ _ _ h => by cases h)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ4⟩
  iintro Hst
  have hq4 : (lrA4 s0 (tv0 :: r0) tvs').q = LRegW 11 [.DLdRes] :: [LInstr] := by simp [regWL]
  iapply (wpH_regw (s := lrA4 s0 (tv0 :: r0) tvs') (rd := 11) (srcs := [.DLdRes]) (litDone_q (by rw [hq4]; simp))
    (fun l s' hs => litNext_q hq4 (anyFab_lit.1 hs)))
  iframe Hst
  inext
  iintro _
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro (psiLS_regw ψ4 _ _)⟩
  iintro Hst
  iapply (wpH_instr (s := { lrA4 s0 (tv0 :: r0) tvs' with q := [LInstr] })
    (litDone_q (s := { lrA4 s0 (tv0 :: r0) tvs' with q := [LInstr] }) (by simp))
    (fun l s' hs => litNext_q rfl (anyFab_lit.1 hs)))
  iframe Hst
  inext
  iintro _
  have ψ6 := psiLS_instr (psiLS_regw ψ4 11 [.DLdRes])
  have hld6 := forall_snoc (forall_snoc hld4 (ldBelow_regw tv0.1 11 [.DLdRes])) (ldBelow_instr tv0.1)
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ψ6⟩
  iintro Hst
  -- `sc.d a2,a0,(y)`: success or failure
  have hy6 : (lrA6 s0 (tv0 :: r0) tvs').rd 9 = y := by
    show ({ ldSz3 s0 8 10 (tv0 :: r0) with regs := (ldSz3 s0 8 10 (tv0 :: r0)).wr 11 _ } : LP).rd 9 = y
    rw [lp_rd_wr (r := 9) (r' := 11) (by decide)]; exact hy3
  have hyl6 : aligned ((lrA6 s0 (tv0 :: r0) tvs').rd 9) 8 = true := by rw [hy6]; simp [aligned, hya]
  have hz6 : (lrA6 s0 (tv0 :: r0) tvs').rd 18 = z := by
    show ({ ldSz3 s0 8 10 (tv0 :: r0) with regs := (ldSz3 s0 8 10 (tv0 :: r0)).wr 11 _ } : LP).rd 18 = z
    rw [lp_rd_wr (r := 18) (r' := 11) (by decide)]
    rw [← hz]; exact lp_rd_wr (s := s0) (r := 18) (r' := 10) (by decide)
  have hlen6 : 12 < (lrA6 s0 (tv0 :: r0) tvs').regs.length := by simp [LP.wr, hlen]
  iapply (wpH_sc (s := lrA6 s0 (tv0 :: r0) tvs') (aq := false) (rl := false) (base := (y : Int))
    (data := toBytes ((lrA6 s0 (tv0 :: r0) tvs').rd 10) 8) (asrc := [.DReg 9]) (vsrc := [.DReg 10])
    (kS := scS7 s0 (tv0 :: r0) tvs' 0 (regWL 12 [.DLdRes] ++ [LExFail, LInstr]))
    (kF := scS7 s0 (tv0 :: r0) tvs' 1 (regWL 12 [] ++ [LExFail, LInstr]))
    (litDone_pc (s := lrA6 s0 (tv0 :: r0) tvs') (by simp [hprog, hpc, lsProg]))
    (fun l s' hs => by
      rcases litNext_sc (s := lrA6 s0 (tv0 :: r0) tvs') (sz := 8) (rd := 12) (rs2 := 10) (rs1 := 9) rfl
        (by simp [hprog, hpc, lsProg]) hyl6 (anyFab_lit.1 hs) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact .inl ⟨by rw [h1, hy6]; rfl, h2⟩
      · exact .inr ⟨h1, h2⟩))
  iframe Hst
  inext
  isplit
  · -- success: EXT gives `s0 ≤ regv a0 < t_sc`; M4 gives `regv a2 ≥ t_sc`
    iintro %ts %R %_ %_ %_ %_ %_ %_ %hext _
    have key2 : tv0.1 < ts := by
      refine Nat.lt_of_le_of_lt ?_ (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hext)
      refine Nat.le_trans ?_ (store_ext _ _ _ _ _)
      refine Nat.le_trans ?_ (Nat.le_max_right _ _)
      rw [srcsView_reg, regv_instr, regv_regW_ne _ _ (by decide : (11 : Nat) ≠ 10), regv_setRes,
        loadRun_regv, regv_instr, regv_regW, srcsView_ldres]
      exact key
    have ψ7 := psiLS_exst ψ6 false false (toBytes ((lrA6 s0 (tv0 :: r0) tvs').rd 10) 8) [.DReg 9] [.DReg 10] ts
      (toBytes_length _ _)
    have hld7 := forall_snoc hld6
      (e := (LExStore false false (y : Int) (toBytes ((lrA6 s0 (tv0 :: r0) tvs').rd 10) 8) [.DReg 9] [.DReg 10],
        some ts)) (fun _ _ _ _ _ _ h => by cases h)
    imodintro
    isplitr
    · ipureintro; exact ⟨0, grd_intro ψ7⟩
    isplitr
    · ipureintro; exact grd_intro trivial
    iintro Hst
    have hq7 : (scS7 s0 (tv0 :: r0) tvs' 0 (regWL 12 [.DLdRes] ++ [LExFail, LInstr])).q =
        LRegW 12 [.DLdRes] :: [LExFail, LInstr] := by simp [regWL]
    iapply (wpH_regw (s := scS7 s0 (tv0 :: r0) tvs' 0 (regWL 12 [.DLdRes] ++ [LExFail, LInstr])) (rd := 12)
      (srcs := [.DLdRes]) (litDone_q (by rw [hq7]; simp)) (fun l s' hs => litNext_q hq7 (anyFab_lit.1 hs)))
    iframe Hst
    inext
    iintro _
    imodintro
    isplitr
    · ipureintro; exact ⟨0, grd_intro (psiLS_regw ψ7 _ _)⟩
    iintro Hst
    iapply (wpH_exfail (s := { scS7 s0 (tv0 :: r0) tvs' 0 (regWL 12 [.DLdRes] ++ [LExFail, LInstr]) with
        q := [LExFail, LInstr] })
      (litDone_q (s := { scS7 s0 (tv0 :: r0) tvs' 0 (regWL 12 [.DLdRes] ++ [LExFail, LInstr]) with
        q := [LExFail, LInstr] }) (by simp))
      (fun l s' hs => litNext_q rfl (anyFab_lit.1 hs)))
    iframe Hst
    inext
    iintro _
    imodintro
    isplitr
    · ipureintro; exact ⟨0, grd_intro (psiLS_exfail (psiLS_regw ψ7 _ _))⟩
    iintro Hst
    iapply (wpH_instr (s := { { scS7 s0 (tv0 :: r0) tvs' 0 (regWL 12 [.DLdRes] ++ [LExFail, LInstr]) with
        q := [LExFail, LInstr] } with q := [LInstr] })
      (litDone_q (s := { { scS7 s0 (tv0 :: r0) tvs' 0 (regWL 12 [.DLdRes] ++ [LExFail, LInstr]) with
        q := [LExFail, LInstr] } with q := [LInstr] }) (by simp))
      (fun l s' hs => litNext_q rfl (anyFab_lit.1 hs)))
    iframe Hst
    inext
    iintro _
    imodintro
    isplitr
    · ipureintro; exact ⟨0, grd_intro (psiLS_instr (psiLS_exfail (psiLS_regw ψ7 _ _)))⟩
    iintro Hst
    iapply (lrsc_tail { { { scS7 s0 (tv0 :: r0) tvs' 0 (regWL 12 [.DLdRes] ++ [LExFail, LInstr]) with
        q := [LExFail, LInstr] } with q := [LInstr] } with q := [] }
      (x : Int) (y : Int) (z : Int) z img M h tv0.1 (by simp [hprog]) (by simp [hpc]) rfl
      ((lp_rd_regs (s := lrA6 s0 (tv0 :: r0) tvs') (r := 18) (r' := 12) (v := 0) rfl (by decide)).trans hz6)
      rfl hza hzl
      (psiLS_instr (psiLS_exfail (psiLS_regw ψ7 _ _)))
      (forall_snoc (forall_snoc (forall_snoc hld7 (ldBelow_regw _ _ _)) (ldBelow_exfail _)) (ldBelow_instr _))
      ?_)
    rotate_left
    · iexact Hst
    · intro _
      rw [srcsView_reg, regv_instr, regv_setRes, regv_regW, srcsView_ldres]
      exact Nat.lt_of_lt_of_le key2 (Nat.le_max_right _ _)
  · -- failure: `a2 = 1`, the stored byte 0 is 1
    iintro _
    have ψ7 := psiLS_exfail ψ6
    imodintro
    isplitr
    · ipureintro; exact ⟨0, grd_intro ψ7⟩
    iintro Hst
    have hq7 : (scS7 s0 (tv0 :: r0) tvs' 1 (regWL 12 [] ++ [LExFail, LInstr])).q =
        LRegW 12 [] :: [LExFail, LInstr] := by simp [regWL]
    iapply (wpH_regw (s := scS7 s0 (tv0 :: r0) tvs' 1 (regWL 12 [] ++ [LExFail, LInstr])) (rd := 12)
      (srcs := []) (litDone_q (by rw [hq7]; simp)) (fun l s' hs => litNext_q hq7 (anyFab_lit.1 hs)))
    iframe Hst
    inext
    iintro _
    imodintro
    isplitr
    · ipureintro; exact ⟨0, grd_intro (psiLS_regw ψ7 _ _)⟩
    iintro Hst
    iapply (wpH_exfail (s := { scS7 s0 (tv0 :: r0) tvs' 1 (regWL 12 [] ++ [LExFail, LInstr]) with
        q := [LExFail, LInstr] })
      (litDone_q (s := { scS7 s0 (tv0 :: r0) tvs' 1 (regWL 12 [] ++ [LExFail, LInstr]) with
        q := [LExFail, LInstr] }) (by simp))
      (fun l s' hs => litNext_q rfl (anyFab_lit.1 hs)))
    iframe Hst
    inext
    iintro _
    imodintro
    isplitr
    · ipureintro; exact ⟨0, grd_intro (psiLS_exfail (psiLS_regw ψ7 _ _))⟩
    iintro Hst
    iapply (wpH_instr (s := { { scS7 s0 (tv0 :: r0) tvs' 1 (regWL 12 [] ++ [LExFail, LInstr]) with
        q := [LExFail, LInstr] } with q := [LInstr] })
      (litDone_q (s := { { scS7 s0 (tv0 :: r0) tvs' 1 (regWL 12 [] ++ [LExFail, LInstr]) with
        q := [LExFail, LInstr] } with q := [LInstr] }) (by simp))
      (fun l s' hs => litNext_q rfl (anyFab_lit.1 hs)))
    iframe Hst
    inext
    iintro _
    imodintro
    isplitr
    · ipureintro; exact ⟨0, grd_intro (psiLS_instr (psiLS_exfail (psiLS_regw ψ7 _ _)))⟩
    iintro Hst
    have h12 := lp_rd_regs_self (s := lrA6 s0 (tv0 :: r0) tvs') (s' := { { { scS7 s0 (tv0 :: r0) tvs' 1
        (regWL 12 [] ++ [LExFail, LInstr]) with q := [LExFail, LInstr] } with q := [LInstr] } with q := [] })
      (r := 12) (v := 1) rfl (by decide) hlen6
    iapply (lrsc_tail { { { scS7 s0 (tv0 :: r0) tvs' 1 (regWL 12 [] ++ [LExFail, LInstr]) with
        q := [LExFail, LInstr] } with q := [LInstr] } with q := [] }
      (x : Int) (y : Int) (z : Int) z img M h tv0.1 (by simp [hprog]) (by simp [hpc]) rfl
      ((lp_rd_regs (s := lrA6 s0 (tv0 :: r0) tvs') (r := 18) (r' := 12) (v := 1) rfl (by decide)).trans hz6)
      rfl hza hzl
      (psiLS_instr (psiLS_exfail (psiLS_regw ψ7 _ _)))
      (forall_snoc (forall_snoc (forall_snoc (forall_snoc hld6 (ldBelow_exfail _)) (ldBelow_regw _ _ _))
        (ldBelow_exfail _)) (ldBelow_instr _))
      ?_)
    · rw [h12]
      intro hd
      exact absurd hd (by decide)
    · iexact Hst

end hart

open Weak.Prom.Ref.Lit (X Y Z)

/-- Ψ of row 5: ΨLS at `x`/`y`/`z` for H0, (P0)–(P4) at `z`/`x` (8 bytes) for H1, the empty trace otherwise. -/
def ΨR5 : Nat → Trace → Prop
  | 0 => ΨLS X Y Z
  | 1 => ΨLB Z X 8
  | _ => fun τ => τ = []

theorem ΨR5_nil : ∀ h, ΨR5 h []
  | 0 => psiLS_nil _ _ _
  | 1 => psiLB_nil _ _ _
  | _ + 2 => rfl

theorem byteAt_lt {m : PMsg} {a : Int} (h : a < m.pa) : m.byteAt a = none := by
  unfold PMsg.byteAt; rw [if_neg (by omega)]

theorem byteAt_far {m : PMsg} {a : Int} (h : m.pa + 8 ≤ a) (hl : m.data.length = 8) : m.byteAt a = none := by
  unfold PMsg.byteAt; rw [if_pos (by omega)]
  apply List.getElem?_eq_none; rw [hl]; omega

theorem byteAt_base (m : PMsg) : m.byteAt m.pa = m.data[0]? := by
  unfold PMsg.byteAt; rw [if_pos (Int.le_refl _)]; simp

/-- **ROW 5, LB+lrsc (manual `litmus_lb_lrsc`): FORBIDDEN, in the logic.**  Over every final memory and every
valid run of machine v2: not both H0's 0th load (`ld a0,(x)`) and H1's 0th load (`ld a3,(z)`) return 0.  Not
vacuous: `mach_lrsc` (row 31) is a machine-v2 run in which an SC succeeds. -/
theorem lit_lbLrsc : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun litStep (testImg Weak.Prom.Ref.Lit.lbLrsc) () (progs Weak.Prom.Ref.Lit.lbLrsc) M run →
    ¬ (run.obsLoad 0 0 = some 0 ∧ run.obsLoad 1 0 = some 0) := by
  intro M run hrun
  have hlen : (progs Weak.Prom.Ref.Lit.lbLrsc).length = 2 := rfl
  obtain ⟨_, hii, hpart, _, _, hwf, _⟩ := adequacy (hlc := HasLC.hasLC) (GF := pfGF) (pdone := litDone)
    Proto.triv (fun _ _ => True) ΨR5 trivial (PO_ad_all _ _ _) ΨR5_nil (devFree_lit _) (fun h p hp _ => by
      match h, hp with
      | 0, hp =>
        rw [List.getElem?_eq_getElem (by rw [hlen]; decide)] at hp
        cases hp
        exact lrsc_hart _ X Y Z _ M 0 rfl rfl rfl (Nat.lt_of_lt_of_le (by decide : 12 < 32) (Nat.le_of_eq rfl))
          rfl rfl rfl (by decide) (by decide) (by decide)
          (by decide) (by decide)
      | 1, hp =>
        rw [List.getElem?_eq_getElem (by rw [hlen]; decide)] at hp
        cases hp
        exact lb8_hart _ 13 18 8 Z X _ M 1 rfl rfl rfl (by decide) (by decide) (by decide) (by decide) rfl rfl
          (by decide) (by decide) (by decide) (by decide)
      | n + 2, hp =>
        rw [List.getElem?_eq_none (by rw [hlen]; omega)] at hp
        cases hp) hrun
  have himg : run.cfg.pcImg = testImg Weak.Prom.Ref.Lit.lbLrsc := validRun_img hrun.1
  have hfin : ∀ h, ΨR5 h (run.trace h) := fun h => by simpa using hii h (run.trace h).length
  refine lrsc_contra himg rfl rfl (fun m hpa => byteAt_lt (by rw [hpa]; decide))
    (fun m hpa => byteAt_lt (by rw [hpa]; decide)) (fun m hpa hl => byteAt_far (by rw [hpa]; decide) hl)
    (fun m hpa hl => byteAt_far (by rw [hpa]; decide) hl) (fun m hpa => by rw [← hpa]; exact byteAt_base m)
    (hfin 0) (hfin 1) (fun h h2 => ?_) hpart hwf
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 2 := ⟨h - 2, by omega⟩
  exact hfin (n + 2)

end Weak.Prom.PF

#print axioms Weak.Prom.PF.adequacy
#print axioms Weak.Prom.PF.lit_lbdd
#print axioms Weak.Prom.PF.lit_lbfd
#print axioms Weak.Prom.PF.lit_lbctrl
#print axioms Weak.Prom.PF.lit_lbLrsc
