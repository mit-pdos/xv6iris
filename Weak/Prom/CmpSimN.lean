/-
Weak/Prom: **completeness S3a — simulating the instructions without memory operations** (ALU, `csrr`, jumps,
`nop`, `fence.i`, branches) and the order lemmas every step uses.

* `pf_po` / `pf_mem`: a past event (an earlier memory operation named by a taint) is po-before every future event;
* `gB_r11` (rule 11) is what a branch's control capture `vcap ⊔= view(srcs)` needs: every later store has the
  branch's sources in its control dependencies.
* `sim_alui`, `sim_alu`, `sim_csrr`, `sim_jmp`, `sim_nop`, `sim_fencei`, `sim_br`: `StepOk` for each.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CmpInv

namespace Weak.Prom.Cmp

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref
open PLabel

variable {T : Test} {trs : List SSt} {ν : Val} {X : Exec} {h : Nat} {sf : SSt}

/-! ## 1. Past and future events -/

/-- The event of `sf` at a past index of `s`. -/
theorem past_ev {s : SSt} (hfut : Future s sf) {d : Nat} (hd : okIdx s.evs d) :
    ∃ se, sf.evs[d]? = some se ∧ s.evs[d]? = some se ∧ se.sk.kind.isMem = true := by
  obtain ⟨se, hse, hm⟩ := hd
  obtain ⟨tl, htl⟩ := hfut.evs
  refine ⟨se, ?_, hse, hm⟩
  rw [← htl, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hse).1]; exact hse

/-- A past memory operation is a memory operation of `X`, po-before every future event. -/
theorem pf_po (c : HCtx T trs ν X h sf) {s : SSt} (hwf : SymWf s) (hfut : Future s sf) {d : Nat}
    (hd : okIdx s.evs d) {j : Nat} (hj : s.evs.length ≤ j) (hjl : j < sf.evs.length) :
    (h, d) ∈ X.ids ∧ (X.sk (h, d)).kind.isMem = true ∧ poX X (h, d) (h, j) = true := by
  obtain ⟨se, hsf, hs, hm⟩ := past_ev hfut hd
  have hsej : sf.evs[j]? = some sf.evs[j] := List.getElem?_eq_getElem hjl
  have h1 := hwf.iiLt d se hs
  have h2 := (hfut.later j _ hj hsej).1
  exact ⟨c.id hsf, by rw [c.sk hsf]; exact hm, c.po_of hsf hsej (by omega)⟩

/-- Index facts of a future event. -/
theorem fut_ev (c : HCtx T trs ν X h sf) {j : Nat} (hjl : j < sf.evs.length) :
    (h, j) ∈ X.ids ∧ X.sk (h, j) = sf.evs[j].sk ∧ X.ev (h, j) = concEv ν h j sf.evs[j] :=
  ⟨c.id (List.getElem?_eq_getElem hjl), c.sk (List.getElem?_eq_getElem hjl),
    c.ev (List.getElem?_eq_getElem hjl)⟩

theorem vo_le_of_gB {X : Exec} {a b : EvId} (h : gB X.gmo a b = true) : vo X a ≤ vo X b :=
  (voG_mono X X.gmo a b h).1

theorem vo_lt_of_gB {X : Exec} {a b : EvId} (h : gB X.gmo a b = true) (hs : (X.sk b).kind.isStore = true) :
    vo X a < vo X b := (voG_mono X X.gmo a b h).2 hs

/-- Rule 11 for a branch: every taint member of the branch's sources is below every later store. -/
theorem ctl_lt (c : HCtx T trs ν X h sf) {s s' : SSt} (hwf : SymWf s) (hfut : Future s sf)
    (hfut' : Future s' sf) (hii : s.ii < s'.ii) (hn : s.evs.length ≤ s'.evs.length) {d : Nat}
    (hd : okIdx s.evs d) (hdc : d ∈ s'.ctl) {j : Nat} (hj : s'.evs.length ≤ j) (hjl : j < sf.evs.length)
    (hst : (X.sk (h, j)).kind.isStore = true) : vo X (h, d) < vo X (h, j) := by
  obtain ⟨hid, hmem, hpo⟩ := pf_po c hwf hfut hd (by omega) hjl
  obtain ⟨hjid, hsk, _⟩ := fut_ev c hjl
  have hcd : d ∈ (X.sk (h, j)).cdep := by
    rw [hsk]
    exact (hfut'.later j _ hj (List.getElem?_eq_getElem hjl)).2 (by rw [← hsk]; exact hst) d hdc
  exact vo_lt_of_gB (gB_of_ppo c.ref c.io hid hjid (ppo_r11 hmem hst hpo hcd)) hst

/-! ## 2. Register values -/

theorem eval_bin_c {ν : Val} {op : Alu} {e1 : Ex} {imm : Nat} (he : e1.eval ν < two64) (himm : imm < two64) :
    (Ex.bin op e1 (Ex.c imm)).eval ν = aluOp op (e1.eval ν) imm ∧ aluOp op (e1.eval ν) imm < two64 := by
  have : (Ex.c imm).eval ν = imm := Nat.mod_eq_of_lt himm
  simp only [Ex.eval] at this ⊢
  rw [this]
  exact ⟨rfl, aluOp_lt op he himm⟩

theorem lp_after (lp : LP) (regs : List Nat) (pc : Nat) :
    ({ lp with regs := regs, pc := pc, q := [] } : LP).prog = lp.prog := rfl

/-- Register views after `regWE` against the taints after `wr`. -/
theorem regv_wr {X : Exec} {h : Nat} {s : SSt} {ws : PState}
    (hregv : ∀ r, 0 < r → r < 32 → domF (fun j => vo X (h, j)) (· ∈ (s.rd r).2) (regv ws r))
    (hlen : s.regs.length = 32) (rd : Nat) (srcs : List Dsrc) (e : Ex × List Nat)
    (hsv : domF (fun j => vo X (h, j)) (· ∈ e.2) (srcsView ws srcs)) :
    ∀ r, 0 < r → r < 32 → domF (fun j => vo X (h, j)) (· ∈ ((s.wr rd e).rd r).2) (regv (regWE ws rd srcs) r) := by
  intro r h0 h32
  rw [regv_regWE, SSt.rd_wr, hlen]
  by_cases hc : rd ≠ 0 ∧ r = rd
  · rw [if_pos hc, if_pos ⟨hc.1, hc.2, by omega⟩]; exact hsv
  · rw [if_neg hc, if_neg (fun h' => hc ⟨h'.1, h'.2.1⟩)]; exact hregv r h0 h32

/-! ## 3. The instructions -/

section instrs

variable {s : SSt} {lp : LP} {ws : PState} {prom : GSet Nat}

theorem lpi_of (hinv : SimInv T X ν h sf s lp ws prom) {ins : Instr} (hi : (T.prog h)[s.pc]? = some ins) :
    lp.prog[lp.pc]? = some ins := by rw [hinv.prog, hinv.pc]; exact hi

/-- An ALU instruction with an immediate. -/
theorem sim_alui (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom) {op : Alu} {rd rs1 imm : Nat}
    (hi : (T.prog h)[s.pc]? = some (.alui op rd rs1 imm)) (hok : instrS3a (.alui op rd rs1 imm) = true)
    {s' : SSt} (hs : stepI h (T.prog h).length s (.alui op rd rs1 imm) = .next s') (hfut : Future s' sf) :
    StepOk T X ν h sf s lp ws prom s' := by
  have hwf' := (symWf_step h _ hinv.wf _).1 s' hs
  simp only [instrS3a, rOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨_, hrs⟩, himm⟩ := hok
  have hev1 := hinv.regEq rs1
  have hlt1 := hinv.regLt rs1
  rcases hr1 : s.rd rs1 with ⟨e1, t1⟩
  rw [hr1] at hev1 hlt1
  simp only [stepI, hr1, Ref.StepR.next.injEq] at hs
  subst hs
  have hsolo := solo_go1' (testImg T) (memOf X) h lp ws prom _ (lp.wr rd (aluOp op (lp.rd rs1) imm)) (lp.pc + 1)
    (regWL rd (srcR rs1) ++ [LInstr]) (regWL_ne _ _) hinv.q (lpi_of hinv hi) (fun l => rfl) (regWL_af _ _)
  rw [foldl_regWL] at hsolo
  obtain ⟨hv, hvlt⟩ := eval_bin_c (op := op) hlt1 himm
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := regWE_fields ws rd (srcR rs1)
  refine ⟨_, _, _, _, hsolo, by rw [machRow_af _ (regWL_af _ _)]; simp [rowSeg_self], ?_⟩
  refine inv_nomem hinv hwf' hfut (by simp) (fun j h1 h2 => by simp at h2; omega) (by rw [lp_after, hinv.prog])
    (by simp [hinv.pc]) rfl (by simp [LP.wr_len, hinv.lpLen]) ?_ ?_ ?_ f1 f2 ?_ ?_ ?_ (fun x => f7 x) f6 rfl rfl
  · intro r
    rw [LP.rd_set, SSt.adv_rd]
    exact regs_wr hinv.lpLen hinv.wf.len hinv.regEq rd _ _ (by rw [hv, hev1, Nat.mod_eq_of_lt (hev1 ▸ hvlt)]) r
  · intro r; rw [SSt.adv_rd]; exact regsLt_wr hinv.regLt rd _ (by rw [hv]; exact hvlt) r
  · intro r h0 h32
    rw [SSt.adv_rd]
    exact regv_wr hinv.regv hinv.wf.len rd _ _ (by have := domF_srcR hinv.regv hrs; rwa [hr1] at this) r h0 h32
  · intro j h1 h2 h3; simp only [instrE, f3]; exact hinv.vrNew j (by simpa using h1) h2 h3
  · intro j h1 h2 h3; simp only [instrE, f4]; exact hinv.vwNew j (by simpa using h1) h2 h3
  · intro j h1 h2 h3; simp only [instrE, f5]; exact hinv.vcap j (by simpa using h1) h2 h3

/-- A register–register ALU instruction. -/
theorem sim_alu (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom) {op : Alu} {rd rs1 rs2 : Nat}
    (hi : (T.prog h)[s.pc]? = some (.alu op rd rs1 rs2)) (hok : instrS3a (.alu op rd rs1 rs2) = true)
    {s' : SSt} (hs : stepI h (T.prog h).length s (.alu op rd rs1 rs2) = .next s') (hfut : Future s' sf) :
    StepOk T X ν h sf s lp ws prom s' := by
  have hwf' := (symWf_step h _ hinv.wf _).1 s' hs
  simp only [instrS3a, rOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨_, hrs1⟩, hrs2⟩ := hok
  have hev1 := hinv.regEq rs1
  have hlt1 := hinv.regLt rs1
  have hev2 := hinv.regEq rs2
  have hlt2 := hinv.regLt rs2
  rcases hr1 : s.rd rs1 with ⟨e1, t1⟩
  rcases hr2 : s.rd rs2 with ⟨e2, t2⟩
  rw [hr1] at hev1 hlt1
  rw [hr2] at hev2 hlt2
  simp only [stepI, hr1, hr2, Ref.StepR.next.injEq] at hs
  subst hs
  have hsolo := solo_go1' (testImg T) (memOf X) h lp ws prom _ (lp.wr rd (aluOp op (lp.rd rs1) (lp.rd rs2)))
    (lp.pc + 1) (regWL rd (srcR rs1 ++ srcR rs2) ++ [LInstr]) (regWL_ne _ _) hinv.q (lpi_of hinv hi)
    (fun l => rfl) (regWL_af _ _)
  rw [foldl_regWL] at hsolo
  have hvlt : aluOp op (e1.eval ν) (e2.eval ν) < two64 := aluOp_lt op hlt1 hlt2
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := regWE_fields ws rd (srcR rs1 ++ srcR rs2)
  refine ⟨_, _, _, _, hsolo, by rw [machRow_af _ (regWL_af _ _)]; simp [rowSeg_self], ?_⟩
  refine inv_nomem hinv hwf' hfut (by simp) (fun j h1 h2 => by simp at h2; omega) (by rw [lp_after, hinv.prog])
    (by simp [hinv.pc]) rfl (by simp [LP.wr_len, hinv.lpLen]) ?_ ?_ ?_ f1 f2 ?_ ?_ ?_ (fun x => f7 x) f6 rfl rfl
  · intro r
    rw [LP.rd_set, SSt.adv_rd]
    exact regs_wr hinv.lpLen hinv.wf.len hinv.regEq rd _ _
      (by show _ = aluOp op (e1.eval ν) (e2.eval ν); rw [hev1, hev2, Nat.mod_eq_of_lt hvlt]) r
  · intro r; rw [SSt.adv_rd]; exact regsLt_wr hinv.regLt rd (Ex.bin op e1 e2, t1 ++ t2) hvlt r
  · intro r h0 h32
    rw [SSt.adv_rd]
    refine regv_wr hinv.regv hinv.wf.len rd _ _ ?_ r h0 h32
    rw [srcsView_append]
    have d1 := domF_srcR hinv.regv hrs1
    have d2 := domF_srcR hinv.regv hrs2
    rw [hr1] at d1; rw [hr2] at d2
    exact domF_max (domF_mono d1 (fun j hj => List.mem_append_left _ hj))
      (domF_mono d2 (fun j hj => List.mem_append_right _ hj))
  · intro j h1 h2 h3; simp only [instrE, f3]; exact hinv.vrNew j (by simpa using h1) h2 h3
  · intro j h1 h2 h3; simp only [instrE, f4]; exact hinv.vwNew j (by simpa using h1) h2 h3
  · intro j h1 h2 h3; simp only [instrE, f5]; exact hinv.vcap j (by simpa using h1) h2 h3

/-- `csrr rd, csr` of a never-written CSR (no dependency). -/
theorem sim_csrr (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom) {rd v : Nat}
    (hi : (T.prog h)[s.pc]? = some (.csrr rd v)) {s' : SSt}
    (hs : stepI h (T.prog h).length s (.csrr rd v) = .next s') (hfut : Future s' sf) :
    StepOk T X ν h sf s lp ws prom s' := by
  have hwf' := (symWf_step h _ hinv.wf _).1 s' hs
  simp only [stepI, Ref.StepR.next.injEq] at hs
  subst hs
  have hsolo := solo_go1' (testImg T) (memOf X) h lp ws prom _ (lp.wr rd v) (lp.pc + 1)
    (regWL rd [] ++ [LInstr]) (regWL_ne _ _) hinv.q (lpi_of hinv hi) (fun l => rfl) (regWL_af _ _)
  rw [foldl_regWL] at hsolo
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := regWE_fields ws rd []
  refine ⟨_, _, _, _, hsolo, by rw [machRow_af _ (regWL_af _ _)]; simp [rowSeg_self], ?_⟩
  refine inv_nomem hinv hwf' hfut (by simp) (fun j h1 h2 => by simp at h2; omega) (by rw [lp_after, hinv.prog])
    (by simp [hinv.pc]) rfl (by simp [LP.wr_len, hinv.lpLen]) ?_ ?_ ?_ f1 f2 ?_ ?_ ?_ (fun x => f7 x) f6 rfl rfl
  · intro r
    rw [LP.rd_set, SSt.adv_rd]
    exact regs_wr hinv.lpLen hinv.wf.len hinv.regEq rd _ _ rfl r
  · intro r; rw [SSt.adv_rd]; exact regsLt_wr hinv.regLt rd _ (eval_c_lt v ν) r
  · intro r h0 h32
    rw [SSt.adv_rd]
    exact regv_wr hinv.regv hinv.wf.len rd _ _ (by rw [srcsView_nil]; exact domF_zero _ _) r h0 h32
  · intro j h1 h2 h3; simp only [instrE, f3]; exact hinv.vrNew j (by simpa using h1) h2 h3
  · intro j h1 h2 h3; simp only [instrE, f4]; exact hinv.vwNew j (by simpa using h1) h2 h3
  · intro j h1 h2 h3; simp only [instrE, f5]; exact hinv.vcap j (by simpa using h1) h2 h3

/-- The shared tail of the register-free instructions: the machine state changes only by `ws'`. -/
theorem sim_plain (hinv : SimInv T X ν h sf s lp ws prom) {ins : Instr} (hi : (T.prog h)[s.pc]? = some ins)
    {s' : SSt} (hwf' : SymWf s') (hfut : Future s' sf) (hevs : s'.evs = s.evs) (hregs : s'.regs = s.regs)
    (pc' : Nat) (hpc' : pc' = s'.pc) (labs : List PLabel) (hne : labs ≠ [])
    (hn : ∀ l, instrNext lp.prog.length lp ins l = go1 lp lp.regs pc' labs l) (hok : ∀ l ∈ labs, afOk l = true)
    (hws : (labs.foldl afEff ws).wVrOld = ws.wVrOld ∧ (labs.foldl afEff ws).wVwOld = ws.wVwOld ∧
      (labs.foldl afEff ws).wVrNew = ws.wVrNew ∧ (labs.foldl afEff ws).wVwNew = ws.wVwNew ∧
      (labs.foldl afEff ws).wFwd = ws.wFwd ∧ (∀ x, coh (labs.foldl afEff ws) x = coh ws x) ∧
      (labs.foldl afEff ws).wRegv = ws.wRegv ∧ (labs.foldl afEff ws).wLdv = 0 ∧ (labs.foldl afEff ws).wIfv = 0)
    (hcap : ∀ j, s'.evs.length ≤ j → j < sf.evs.length → (X.sk (h, j)).kind.isStore = true →
      (labs.foldl afEff ws).wVcap < vo X (h, j)) :
    StepOk T X ν h sf s lp ws prom s' := by
  have hsolo := solo_go1' (testImg T) (memOf X) h lp ws prom ins lp.regs pc' labs hne hinv.q (lpi_of hinv hi) hn hok
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := hws
  have hrd : ∀ r, s'.rd r = s.rd r := fun r => by unfold SSt.rd; rw [hregs]
  refine ⟨_, _, _, _, hsolo, by rw [machRow_af _ hok, hevs, rowSeg_self], ?_⟩
  refine inv_nomem hinv hwf' hfut (by rw [hevs]; exact Nat.le_refl _) (fun j h1 h2 => by rw [hevs] at h2; omega)
    (by rw [lp_after, hinv.prog]) hpc' rfl hinv.lpLen ?_ ?_ ?_ f1 f2 ?_ ?_ hcap f6 f5 f8 f9
  · intro r; rw [hrd]; exact hinv.regEq r
  · intro r; rw [hrd]; exact hinv.regLt r
  · intro r h0 h32; rw [hrd]; unfold regv; rw [f7]; exact hinv.regv r h0 h32
  · intro j h1 h2 h3; rw [f3]; exact hinv.vrNew j (by rw [hevs] at h1; exact h1) h2 h3
  · intro j h1 h2 h3; rw [f4]; exact hinv.vwNew j (by rw [hevs] at h1; exact h1) h2 h3

theorem fold_instr (ws : PState) : [LInstr].foldl afEff ws = instrE ws := rfl

/-- `jal x0, tgt`. -/
theorem sim_jmp (hinv : SimInv T X ν h sf s lp ws prom) {tgt : Nat}
    (hi : (T.prog h)[s.pc]? = some (.jmp tgt)) {s' : SSt}
    (hs : stepI h (T.prog h).length s (.jmp tgt) = .next s') (hfut : Future s' sf) :
    StepOk T X ν h sf s lp ws prom s' := by
  have hwf' := (symWf_step h _ hinv.wf _).1 s' hs
  simp only [stepI] at hs
  split at hs
  · cases hs
  · rename_i hc
    simp only [Ref.StepR.next.injEq] at hs
    subst hs
    refine sim_plain hinv hi hwf' hfut rfl rfl tgt rfl [LInstr] (by simp) (fun l => ?_) (by simp [afOk])
      ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl⟩
      (fun j h1 h2 h3 => hinv.vcap j h1 h2 h3)
    simp only [instrNext, hinv.pc, hinv.prog]
    rw [if_neg hc]

/-- `nop`. -/
theorem sim_nop (hinv : SimInv T X ν h sf s lp ws prom) (hi : (T.prog h)[s.pc]? = some .nop) {s' : SSt}
    (hs : stepI h (T.prog h).length s .nop = .next s') (hfut : Future s' sf) :
    StepOk T X ν h sf s lp ws prom s' := by
  have hwf' := (symWf_step h _ hinv.wf _).1 s' hs
  simp only [stepI, Ref.StepR.next.injEq] at hs
  subst hs
  exact sim_plain hinv hi hwf' hfut rfl rfl (lp.pc + 1) (by simp [hinv.pc]) [LInstr] (by simp) (fun l => rfl)
    (by simp [afOk]) ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl⟩
    (fun j h1 h2 h3 => hinv.vcap j h1 h2 h3)

/-- `fence.i` (no data-memory ordering; its fetch floor `wIfl` is not in the invariant). -/
theorem sim_fencei (hinv : SimInv T X ν h sf s lp ws prom) (hi : (T.prog h)[s.pc]? = some .fencei) {s' : SSt}
    (hs : stepI h (T.prog h).length s .fencei = .next s') (hfut : Future s' sf) :
    StepOk T X ν h sf s lp ws prom s' := by
  have hwf' := (symWf_step h _ hinv.wf _).1 s' hs
  simp only [stepI, Ref.StepR.next.injEq] at hs
  subst hs
  exact sim_plain hinv hi hwf' hfut rfl rfl (lp.pc + 1) (by simp [hinv.pc]) [LFenceI, LInstr] (by simp)
    (fun l => rfl) (by simp [afOk]) ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl⟩
    (fun j h1 h2 h3 => hinv.vcap j h1 h2 h3)

/-- A conditional branch, given the successor's shape: `vcap` captures the sources (rule 11). -/
theorem sim_brCore (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom) {cc : BrC}
    {rs1 rs2 tgt : Nat} (hi : (T.prog h)[s.pc]? = some (.br cc rs1 rs2 tgt)) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32)
    (hc : ¬(tgt ≤ s.pc ∨ (T.prog h).length < tgt)) {s' : SSt} (hwf' : SymWf s') (hfut : Future s' sf)
    (hevs : s'.evs = s.evs) (hregs : s'.regs = s.regs) (hii : s'.ii = s.ii + 1)
    (hctl : s'.ctl = s.ctl ++ (s.rd rs1).2 ++ (s.rd rs2).2)
    (hpc : s'.pc = if brEval cc ((s.rd rs1).1.eval ν) ((s.rd rs2).1.eval ν) then tgt else s.pc + 1) :
    StepOk T X ν h sf s lp ws prom s' := by
  have hev1 := hinv.regEq rs1
  have hev2 := hinv.regEq rs2
  have hpc' : (if brEval cc (lp.rd rs1) (lp.rd rs2) then tgt else lp.pc + 1) = s'.pc := by
    rw [hev1, hev2, hinv.pc, hpc]
  refine sim_plain hinv hi hwf' hfut hevs hregs _ hpc' [LCtrl (srcR rs1 ++ srcR rs2), LInstr] (by simp)
    (fun l => ?_) (by simp [afOk]) ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl⟩ ?_
  · simp only [instrNext, hinv.pc, hinv.prog]
    rw [if_neg hc]
  · intro j h1 h2 h3
    have hsv : (List.foldl afEff ws [LCtrl (srcR rs1 ++ srcR rs2), LInstr]).wVcap =
        max (srcsView ws (srcR rs1 ++ srcR rs2)) ws.wVcap := rfl
    rw [hsv]
    have hcapj := hinv.vcap j (by rw [hevs] at h1; exact h1) h2 h3
    have hsrc : srcsView ws (srcR rs1 ++ srcR rs2) < vo X (h, j) := by
      rw [srcsView_append]
      have hb : ∀ r, r < 32 → (∀ d ∈ (s.rd r).2, d ∈ (s.rd rs1).2 ++ (s.rd rs2).2) →
          srcsView ws (srcR r) < vo X (h, j) := by
        intro r hr hsub
        refine domF_lt (domF_srcR hinv.regv hr) (fun d hd => ?_) (by omega)
        refine ctl_lt c hinv.wf hinv.fut hfut (by omega) (by rw [hevs]; exact Nat.le_refl _)
          (hinv.wf.taint r d hd) ?_ h1 h2 h3
        rw [hctl, List.append_assoc]
        exact List.mem_append_right _ (hsub d hd)
      have e1 := hb rs1 hrs1 (fun d hd => List.mem_append_left _ hd)
      have e2 := hb rs2 hrs2 (fun d hd => List.mem_append_right _ hd)
      omega
    omega

/-- A conditional branch: the machine takes the direction the reference path took (its condition holds,
`condsOk`). -/
theorem sim_br (c : HCtx T trs ν X h sf) (hinv : SimInv T X ν h sf s lp ws prom) {cc : BrC} {rs1 rs2 tgt : Nat}
    (hi : (T.prog h)[s.pc]? = some (.br cc rs1 rs2 tgt)) (hok : instrS3a (.br cc rs1 rs2 tgt) = true)
    {t f : SSt} (hs : stepI h (T.prog h).length s (.br cc rs1 rs2 tgt) = .fork t f) (b : Bool)
    (hfut : Future (if b then t else f) sf) : StepOk T X ν h sf s lp ws prom (if b then t else f) := by
  have hwfs := (symWf_step h _ hinv.wf _).2 t f hs
  simp only [instrS3a, rOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hrs1, hrs2⟩ := hok
  simp only [stepI] at hs
  split at hs
  · cases hs
  · rename_i hc
    simp only [Ref.StepR.fork.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    have hall := (c.condsSf).1
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false] at hfut ⊢
      have hmem : (cc, (s.rd rs1).1, (s.rd rs2).1, false) ∈ sf.conds := hfut.conds.subset (by simp)
      have hcond := List.all_eq_true.1 hall _ hmem
      simp only [beq_iff_eq] at hcond
      exact sim_brCore c hinv hi hrs1 hrs2 hc hwfs.2 hfut rfl rfl rfl rfl (by simp [hcond])
    | true =>
      simp only [if_true] at hfut ⊢
      have hmem : (cc, (s.rd rs1).1, (s.rd rs2).1, true) ∈ sf.conds := hfut.conds.subset (by simp)
      have hcond := List.all_eq_true.1 hall _ hmem
      simp only [beq_iff_eq] at hcond
      exact sim_brCore c hinv hi hrs1 hrs2 hc hwfs.1 hfut rfl rfl rfl rfl (by simp [hcond])

end instrs

end Weak.Prom.Cmp
