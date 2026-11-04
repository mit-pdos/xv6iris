/-
Weak/Prom: **the noninterference simulation and NOTA** (S0-P part (2), milestone 2b, statement 5 in corrected form;
definitions in `Weak/Prom/MachNota.lean`).

* `ni_step` — one solo step whose post-`vcap` is below `θ` has a matching free step (same label up to the answers
  of HIGH loads and the data of stores from high registers) keeping `agree` and `fwdInv`.
* `ni_final` — the step fulfilling `θ` itself is a free step with the SAME label (its address, data and control
  views are below `θ` by EXT; an AMO's read bytes are below `θ` by COH).
* `nota` — NOTA: with a closed domain containing the image, every byte of the final memory is in the domain.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.MachNota

namespace Weak.Prom.Mach

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal)
open PLabel

theorem srcsView_ld (ws : PState) : srcsView ws [.DLdRes] = ws.wLdv := by
  show max ws.wLdv 0 = ws.wLdv; omega

theorem go1_s' {s' : LP} {regs' : List Nat} {pc' : Nat} {labs : List PLabel} {l : PLabel} {rest : List PLabel}
    (h : labs = l :: rest) : go1 s' regs' pc' labs l = some { s' with regs := regs', pc := pc', q := rest } := by
  subst h; simp [go1]

theorem fwd_store_inD {img : Image} {M : List PMsg} {D : Int → List (BitVec 8)} {ts : Nat} {m : PMsg}
    (hpos : 0 < ts) (hmsg : M[ts - 1]? = some m) (hin : msgIn D m) {b : Int} {x : BitVec 8}
    (hx : memByte img M ts b = some x) : x ∈ D b := by
  obtain ⟨k, rfl⟩ : ∃ k, ts = k + 1 := ⟨ts - 1, by omega⟩
  simp only [memByte] at hx
  simp only [Nat.add_sub_cancel] at hmsg
  rw [hmsg] at hx
  exact msgIn_byteAt hin hx

theorem acqPost_wRegv (ws : PState) (aq : Bool) (ts : Nat) : (acqPost ws aq ts).wRegv = ws.wRegv := rfl
theorem amoPost_wRegv (ws : PState) (aq : Bool) (ts : Nat) : (amoPost ws aq ts).wRegv = ws.wRegv := rfl
theorem storeRun_wRegv (ws : PState) (rl : Bool) (va fv : Nat) (base : Int) (n ts : Nat) :
    (storeRun ws rl va fv base n ts).wRegv = ws.wRegv := (storeBytes_fields ws base n ts fv).1
theorem loadRun_wRegv (ws : PState) (aq rl : Bool) (va : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    (loadRun ws aq rl va base tvs).wRegv = ws.wRegv := (loadBytes_fields aq (ldPre ws aq rl va) ws base tvs).2.1

theorem loadRunV_wRegv (ws : PState) (aq rl : Bool) (va vi : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    (loadRunV ws aq rl va vi base tvs).wRegv = ws.wRegv :=
  (loadBytes_fields aq (max (ldPre ws aq rl va) vi) ws base tvs).2.1   -- MachFix-R-b5

theorem fwdInv_storeRun {img : Image} {M : List PMsg} {D : Int → List (BitVec 8)} {θ : Nat} {ws ws0 : PState}
    {w : List PMsg} (hf : fwdInv img M D θ ws w) (hw : ws0.wFwd = ws.wFwd) {rl : Bool} {va fv : Nat} {base : Int}
    {n ts : Nat} {m : PMsg} (hpa : m.pa = base) (hlen : m.data.length = n)
    (hin : fv < θ → ∀ b x, memByte img M ts b = some x → x ∈ D b ∨ m.byteAt b = some x) :
    fwdInv img M D θ (storeRun ws0 rl va fv base n ts) (w ++ [m]) :=
  fwdInv_store hf (fun b => by rw [storeRun_fwd, hw]) hpa hlen hin

theorem toBytes_len (v sz : Nat) : (toBytes v sz).length = sz := by simp [toBytes, byteList]

theorem noRegW_tso : ∀ x ∈ [LFence false true false true, LInstr], isRegW x = false := by simp [isRegW]

/-- ONE STEP OF THE SIMULATION. -/
theorem ni_step {img : Image} {M : List PMsg} {D : Int → List (BitVec 8)} {i θ : Nat}
    (hlow : lowM img M D θ) (hD : ∀ a, D a ≠ [])
    {s s1 : LP} {ws ws1 : PState} {prom prom1 : GSet Nat} {l : PLabel} {ots : Option Nat}
    (hl : litNext s l = some s1) (hm : memStep img M i prom ws l ots ws1 prom1)
    (hpos : ∀ t ∈ prom, 0 < t) (hq : qOk s.q) (hv : ws1.wVcap < θ)
    {s' : LP} {w' : List PMsg} (ha : agree θ ws s s') (hf : fwdInv img M D θ ws w') :
    ∃ l' s1', litNextF s' l' = some s1' ∧ freeOk D w' l' ∧ agree θ ws1 s1 s1' ∧
      fwdInv img M D θ ws1 (w' ++ (labelMsg i l').toList) := by
  unfold litNext at hl
  cases hqs : s.q with
  | cons l0 rest =>
    rw [hqs] at hl hq
    simp only at hl
    split at hl
    · rename_i he
      subst he
      cases hl
      have hq0 := hq.1 l (List.mem_cons_self ..)
      have hrest : ∀ x ∈ rest, isRegW x = false := hq.2
      have hlit : litNextF s' l = some { s' with q := rest } := by
        unfold litNextF; rw [ha.q, hqs]; simp
      have hag : ∀ ws1 : PState, (∀ r, effView ws (l :: rest) r = regv ws1 r) →
          agree θ ws1 { s with q := rest } { s' with q := rest } := by
        intro ws1 he
        refine ⟨ha.prog, ha.pc, rfl, ha.len, fun r hr hlt => ?_⟩
        simp only at hlt ⊢
        rw [effView_noRegW hrest, ← he] at hlt
        exact ha.regs r hr (by rw [hqs]; exact hlt)
      cases l <;> simp only [qLab, Bool.false_eq_true] at hq0
      case LFence pr pw sr sw =>
        cases hm
        exact ⟨_, _, hlit, freeOk_none rfl, hag _ (fun r => rfl), fwdInv_nomsg rfl hf⟩
      case LRegW rd srcs =>
        cases hm
        exact ⟨_, _, hlit, freeOk_none rfl, hag _ (fun r => by rw [regv_insert]; rfl), fwdInv_nomsg rfl hf⟩
      case LInstr =>
        cases hm
        exact ⟨_, _, hlit, freeOk_none rfl, hag _ (fun r => rfl), fwdInv_nomsg rfl hf⟩
      case LExFail =>
        cases hm
        exact ⟨_, _, hlit, freeOk_none rfl, hag _ (fun r => rfl), fwdInv_nomsg rfl hf⟩
    · cases hl
  | nil =>
    rw [hqs] at hl
    simp only at hl
    cases hp : s.prog[s.pc]? with
    | none => rw [hp] at hl; cases hl
    | some ins =>
      rw [hp] at hl
      simp only at hl
      have hst : ∀ l', litNextF s' l' = insNextF s.prog.length s' ins l' := by
        intro l'; unfold litNextF; rw [ha.q, hqs]; simp only; rw [ha.prog, ha.pc, hp]
      have hpc1 : s'.pc + 1 = s.pc + 1 := by rw [ha.pc]
      cases ins with
      | alui op rd rs1 imm =>
        simp only [instrNext] at hl
        obtain ⟨rest, hlabs, rfl⟩ := go1_eq hl
        have hlit : litNextF s' l = some { s' with regs := s'.wr rd (aluOp op (s'.rd rs1) imm), pc := s'.pc + 1, q := rest } := by
          rw [hst]; simp only [insNextF, instrNext]; exact go1_s' hlabs
        rcases regWL_cons hlabs with ⟨hrd, h⟩ | ⟨hrd, h, hrest⟩
        · simp only [List.cons.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          cases hm
          exact ⟨_, _, hlit, freeOk_none rfl,
            agree_wr_now ha hqs noRegW_nil hpc1 (fun r _ => rfl) (fun h => absurd hrd h), fwdInv_nomsg rfl hf⟩
        · subst h hrest
          cases hm
          refine ⟨_, _, hlit, freeOk_none rfl, agree_wr_now ha hqs noRegW_LInstr hpc1
            (fun r hr => by rw [regv_insert, if_neg (Ne.symm hr)]) (fun _ hlt => ?_), fwdInv_nomsg rfl hf⟩
          rw [regv_insert, if_pos rfl] at hlt
          rw [agree_src ha hqs hlt]
      | alu op rd rs1 rs2 =>
        simp only [instrNext] at hl
        obtain ⟨rest, hlabs, rfl⟩ := go1_eq hl
        have hlit : litNextF s' l = some { s' with regs := s'.wr rd (aluOp op (s'.rd rs1) (s'.rd rs2)), pc := s'.pc + 1, q := rest } := by
          rw [hst]; simp only [insNextF, instrNext]; exact go1_s' hlabs
        rcases regWL_cons hlabs with ⟨hrd, h⟩ | ⟨hrd, h, hrest⟩
        · simp only [List.cons.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          cases hm
          exact ⟨_, _, hlit, freeOk_none rfl,
            agree_wr_now ha hqs noRegW_nil hpc1 (fun r _ => rfl) (fun h => absurd hrd h), fwdInv_nomsg rfl hf⟩
        · subst h hrest
          cases hm
          refine ⟨_, _, hlit, freeOk_none rfl, agree_wr_now ha hqs noRegW_LInstr hpc1
            (fun r hr => by rw [regv_insert, if_neg (Ne.symm hr)]) (fun _ hlt => ?_), fwdInv_nomsg rfl hf⟩
          rw [regv_insert, if_pos rfl, srcsView_append] at hlt
          rw [agree_src ha hqs (by omega : srcsView ws (srcR rs1) < θ),
            agree_src ha hqs (by omega : srcsView ws (srcR rs2) < θ)]
      | csrr rd v =>
        simp only [instrNext] at hl
        obtain ⟨rest, hlabs, rfl⟩ := go1_eq hl
        have hlit : litNextF s' l = some { s' with regs := s'.wr rd v, pc := s'.pc + 1, q := rest } := by
          rw [hst]; simp only [insNextF, instrNext]; exact go1_s' hlabs
        rcases regWL_cons hlabs with ⟨hrd, h⟩ | ⟨hrd, h, hrest⟩
        · simp only [List.cons.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          cases hm
          exact ⟨_, _, hlit, freeOk_none rfl,
            agree_wr_now ha hqs noRegW_nil hpc1 (fun r _ => rfl) (fun h => absurd hrd h), fwdInv_nomsg rfl hf⟩
        · subst h hrest
          cases hm
          exact ⟨_, _, hlit, freeOk_none rfl, agree_wr_now ha hqs noRegW_LInstr hpc1
            (fun r hr => by rw [regv_insert, if_neg (Ne.symm hr)]) (fun _ _ => rfl), fwdInv_nomsg rfl hf⟩
      | fence f =>
        simp only [instrNext] at hl
        obtain ⟨rest, hlabs, rfl⟩ := go1_eq hl
        have hlit : litNextF s' l = some { s' with regs := s'.regs, pc := s'.pc + 1, q := rest } := by
          rw [hst]; simp only [insNextF, instrNext]; exact go1_s' hlabs
        simp only [List.cons.injEq] at hlabs
        obtain ⟨rfl, rfl⟩ := hlabs
        cases hm
        exact ⟨_, _, hlit, freeOk_none rfl, agree_same ha hqs noRegW_LInstr hpc1 (fun r => rfl), fwdInv_nomsg rfl hf⟩
      | fenceTso =>
        simp only [instrNext] at hl
        obtain ⟨rest, hlabs, rfl⟩ := go1_eq hl
        have hlit : litNextF s' l = some { s' with regs := s'.regs, pc := s'.pc + 1, q := rest } := by
          rw [hst]; simp only [insNextF, instrNext]; exact go1_s' hlabs
        simp only [List.cons.injEq] at hlabs
        obtain ⟨rfl, rfl⟩ := hlabs
        cases hm
        exact ⟨_, _, hlit, freeOk_none rfl, agree_same ha hqs noRegW_tso hpc1 (fun r => rfl), fwdInv_nomsg rfl hf⟩
      | fencei =>
        simp only [instrNext] at hl
        obtain ⟨rest, hlabs, rfl⟩ := go1_eq hl
        have hlit : litNextF s' l = some { s' with regs := s'.regs, pc := s'.pc + 1, q := rest } := by
          rw [hst]; simp only [insNextF, instrNext]; exact go1_s' hlabs
        simp only [List.cons.injEq] at hlabs
        obtain ⟨rfl, rfl⟩ := hlabs
        cases hm
        exact ⟨_, _, hlit, freeOk_none rfl, agree_same ha hqs noRegW_LInstr hpc1 (fun r => rfl), fwdInv_nomsg rfl hf⟩
      | nop =>
        simp only [instrNext] at hl
        obtain ⟨rest, hlabs, rfl⟩ := go1_eq hl
        have hlit : litNextF s' l = some { s' with regs := s'.regs, pc := s'.pc + 1, q := rest } := by
          rw [hst]; simp only [insNextF, instrNext]; exact go1_s' hlabs
        simp only [List.cons.injEq] at hlabs
        obtain ⟨rfl, rfl⟩ := hlabs
        cases hm
        exact ⟨_, _, hlit, freeOk_none rfl, agree_same ha hqs noRegW_nil hpc1 (fun r => rfl), fwdInv_nomsg rfl hf⟩
      | jmp tgt =>
        replace hl := ite_none_some' hl
        obtain ⟨hg, hl⟩ := hl
        obtain ⟨rest, hlabs, rfl⟩ := go1_eq hl
        have hlit : litNextF s' l = some { s' with regs := s'.regs, pc := tgt, q := rest } := by
          rw [hst]; simp only [insNextF, instrNext]; rw [ha.pc, if_neg hg]; exact go1_s' hlabs
        simp only [List.cons.injEq] at hlabs
        obtain ⟨rfl, rfl⟩ := hlabs
        cases hm
        exact ⟨_, _, hlit, freeOk_none rfl, agree_same ha hqs noRegW_nil rfl (fun r => rfl), fwdInv_nomsg rfl hf⟩
      | br c rs1 rs2 tgt =>
        replace hl := ite_none_some' hl
        obtain ⟨hg, hl⟩ := hl
        obtain ⟨rest, hlabs, rfl⟩ := go1_eq hl
        have hlit : litNextF s' l = some { s' with regs := s'.regs, pc := if brEval c (s'.rd rs1) (s'.rd rs2) then tgt else s'.pc + 1, q := rest } := by
          rw [hst]; simp only [insNextF, instrNext]; rw [ha.pc, if_neg hg, ← ha.pc]; exact go1_s' hlabs
        simp only [List.cons.injEq] at hlabs
        obtain ⟨rfl, rfl⟩ := hlabs
        cases hm
        have hv' : srcsView ws (srcR rs1 ++ srcR rs2) < θ := by simp only at hv; omega
        rw [srcsView_append] at hv'
        have h1 := agree_src ha hqs (by omega : srcsView ws (srcR rs1) < θ)
        have h2 := agree_src ha hqs (by omega : srcsView ws (srcR rs2) < θ)
        exact ⟨_, _, hlit, freeOk_none rfl,
          agree_same ha hqs noRegW_LInstr (by rw [h1, h2, ha.pc]) (fun r => rfl), fwdInv_nomsg rfl hf⟩
      | load sz sgn rd rs1 off =>
        replace hl := ite_none_some' hl
        obtain ⟨hal, hl⟩ := hl
        cases l
        all_goals try (simp only [reduceCtorEq] at hl; done)
        rename_i aq rl b tvs asrc
        obtain ⟨⟨h1, h2, h3, h4, h5⟩, rfl⟩ := ite_some_none hl
        subst h1 h2 h3 h5
        cases hm with
        | load _ _ _ _ _ hok vi _ =>   -- MachFix-R-b5
          have hv' := hv
          rw [loadRunV_vcap] at hv'
          have hrs1 : s'.rd rs1 = s.rd rs1 := agree_src ha hqs (by omega)
          have hfw : fwdInv img M D θ
              (loadRunV ws false false (srcsView ws (srcR rs1)) vi (↑((s.rd rs1 + off) % two64)) tvs) w' := by
            intro a' tf vf hg; rw [loadRunV_fwd] at hg; exact hf a' tf vf hg
          by_cases hc : (loadRunV ws false false (srcsView ws (srcR rs1)) vi (↑((s.rd rs1 + off) % two64)) tvs).wLdv < θ
          · refine ⟨LLoad false false (↑((s.rd rs1 + off) % two64)) tvs (srcR rs1),
              { s' with regs := s'.wr rd (if sgn then sext sz (ofBytes (tvs.map Prod.snd)) else ofBytes (tvs.map Prod.snd)), pc := s'.pc + 1, q := regWL rd [.DLdRes] ++ [LInstr] },
              ?_, ?_, ?_, fwdInv_nomsg rfl hfw⟩
            · rw [hst]; simp only [insNextF, instrNext]; rw [hrs1]; simp [hal, h4]
            · intro base tvs' hr
              simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hr
              obtain ⟨rfl, rfl⟩ := hr
              exact lowLoadV hlow hf hok (Nat.le_refl _) hc
            · exact agree_wrq ha hqs noRegW_LInstr hpc1 (fun r => loadRunV_regv _ _ _ _ _ _ _ r) (fun _ _ => rfl)
          · refine ⟨LLoad false false (↑((s.rd rs1 + off) % two64))
                (canonRun D (↑((s.rd rs1 + off) % two64)) sz) (srcR rs1),
              { s' with regs := s'.wr rd (if sgn then sext sz (ofBytes ((canonRun D (↑((s.rd rs1 + off) % two64)) sz).map Prod.snd)) else ofBytes ((canonRun D (↑((s.rd rs1 + off) % two64)) sz).map Prod.snd)), pc := s'.pc + 1, q := regWL rd [.DLdRes] ++ [LInstr] }, ?_, ?_, ?_, fwdInv_nomsg rfl hfw⟩
            · rw [hst]; simp only [insNextF, instrNext]; rw [hrs1]; simp [hal, canonRun_len]
            · intro base tvs' hr
              simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hr
              obtain ⟨rfl, rfl⟩ := hr
              exact canonRun_inD hD _ _
            · exact agree_wrq ha hqs noRegW_LInstr hpc1 (fun r => loadRunV_regv _ _ _ _ _ _ _ r)
                (fun _ hlt => absurd (by rw [srcsView_ld] at hlt; exact hlt) hc)
      | loadAq sz rl0 rd rs1 =>
        replace hl := ite_none_some' hl
        obtain ⟨hal, hl⟩ := hl
        cases l
        all_goals try (simp only [reduceCtorEq] at hl; done)
        rename_i aq rl b tvs asrc
        obtain ⟨⟨h1, h2, h3, h4, h5⟩, rfl⟩ := ite_some_none hl
        subst h1 h2 h3 h5
        cases hm with
        | load _ _ _ _ _ hok vi _ =>   -- MachFix-R-b5
          have hv' := hv
          rw [loadRunV_vcap] at hv'
          have hrs1 : s'.rd rs1 = s.rd rs1 := agree_src ha hqs (by omega)
          have hfw : fwdInv img M D θ (loadRunV ws true rl (srcsView ws (srcR rs1)) vi (↑(s.rd rs1)) tvs) w' := by
            intro a' tf vf hg; rw [loadRunV_fwd] at hg; exact hf a' tf vf hg
          by_cases hc : (loadRunV ws true rl (srcsView ws (srcR rs1)) vi (↑(s.rd rs1)) tvs).wLdv < θ
          · refine ⟨LLoad true rl (↑(s.rd rs1)) tvs (srcR rs1),
              { s' with regs := s'.wr rd (sext sz (ofBytes (tvs.map Prod.snd))), pc := s'.pc + 1, q := regWL rd [.DLdRes] ++ [LInstr] }, ?_, ?_, ?_, fwdInv_nomsg rfl hfw⟩
            · rw [hst]; simp only [insNextF, instrNext]; rw [hrs1]; simp [hal, h4]
            · intro base tvs' hr
              simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hr
              obtain ⟨rfl, rfl⟩ := hr
              exact lowLoadV hlow hf hok (Nat.le_refl _) hc
            · exact agree_wrq ha hqs noRegW_LInstr hpc1 (fun r => loadRunV_regv _ _ _ _ _ _ _ r) (fun _ _ => rfl)
          · refine ⟨LLoad true rl (↑(s.rd rs1)) (canonRun D (↑(s.rd rs1)) sz) (srcR rs1),
              { s' with regs := s'.wr rd (sext sz (ofBytes ((canonRun D (↑(s.rd rs1)) sz).map Prod.snd))), pc := s'.pc + 1, q := regWL rd [.DLdRes] ++ [LInstr] }, ?_, ?_, ?_, fwdInv_nomsg rfl hfw⟩
            · rw [hst]; simp only [insNextF, instrNext]; rw [hrs1]; simp [hal, canonRun_len]
            · intro base tvs' hr
              simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hr
              obtain ⟨rfl, rfl⟩ := hr
              exact canonRun_inD hD _ _
            · exact agree_wrq ha hqs noRegW_LInstr hpc1 (fun r => loadRunV_regv _ _ _ _ _ _ _ r)
                (fun _ hlt => absurd (by rw [srcsView_ld] at hlt; exact hlt) hc)
      | lr sz aq0 rl0 rd rs1 =>
        replace hl := ite_none_some' hl
        obtain ⟨hal, hl⟩ := hl
        cases l
        all_goals try (simp only [reduceCtorEq] at hl; done)
        rename_i aq rl b tvs asrc
        obtain ⟨⟨h1, h2, h3, h4, h5⟩, rfl⟩ := ite_some_none hl
        subst h1 h2 h3 h5
        cases hm with
        | lr _ _ _ _ _ hok vi _ =>   -- MachFix-R-b5
          have hv' : (loadRunV ws aq (aq && rl0) (srcsView ws (srcR rs1)) vi (↑(s.rd rs1)) tvs).wVcap < θ := hv
          rw [loadRunV_vcap] at hv'
          have hrs1 : s'.rd rs1 = s.rd rs1 := agree_src ha hqs (by omega)
          have hfw : fwdInv img M D θ { loadRunV ws aq (aq && rl0) (srcsView ws (srcR rs1)) vi (↑(s.rd rs1)) tvs with wRes := some ⟨↑(s.rd rs1), tvs.map Prod.fst, readViewV ws aq (aq && rl0) (srcsView ws (srcR rs1)) vi (↑(s.rd rs1)) tvs⟩ } w' := by
            intro a' tf vf hg
            have hg' : get? (loadRunV ws aq (aq && rl0) (srcsView ws (srcR rs1)) vi (↑(s.rd rs1)) tvs).wFwd a' =
              some (tf, vf) := hg
            rw [loadRunV_fwd] at hg'; exact hf a' tf vf hg'
          have hreg : ∀ r, regv { loadRunV ws aq (aq && rl0) (srcsView ws (srcR rs1)) vi (↑(s.rd rs1)) tvs with wRes := some ⟨↑(s.rd rs1), tvs.map Prod.fst, readViewV ws aq (aq && rl0) (srcsView ws (srcR rs1)) vi (↑(s.rd rs1)) tvs⟩ } r = regv ws r :=
            fun r => loadRunV_regv _ _ _ _ _ _ _ r
          by_cases hc : (loadRunV ws aq (aq && rl0) (srcsView ws (srcR rs1)) vi (↑(s.rd rs1)) tvs).wLdv < θ
          · refine ⟨LExLoad aq (aq && rl0) (↑(s.rd rs1)) tvs (srcR rs1),
              { s' with regs := s'.wr rd (sext sz (ofBytes (tvs.map Prod.snd))), pc := s'.pc + 1, q := regWL rd [.DLdRes] ++ [LInstr] }, ?_, ?_, ?_, fwdInv_nomsg rfl hfw⟩
            · rw [hst]; simp only [insNextF, instrNext]; rw [hrs1]; simp [hal, h4]
            · intro base tvs' hr
              simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hr
              obtain ⟨rfl, rfl⟩ := hr
              exact lowLoadV hlow hf hok (Nat.le_refl _) hc
            · exact agree_wrq ha hqs noRegW_LInstr hpc1 hreg (fun _ _ => rfl)
          · refine ⟨LExLoad aq (aq && rl0) (↑(s.rd rs1)) (canonRun D (↑(s.rd rs1)) sz) (srcR rs1),
              { s' with regs := s'.wr rd (sext sz (ofBytes ((canonRun D (↑(s.rd rs1)) sz).map Prod.snd))), pc := s'.pc + 1, q := regWL rd [.DLdRes] ++ [LInstr] }, ?_, ?_, ?_, fwdInv_nomsg rfl hfw⟩
            · rw [hst]; simp only [insNextF, instrNext]; rw [hrs1]; simp [hal, canonRun_len]
            · intro base tvs' hr
              simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hr
              obtain ⟨rfl, rfl⟩ := hr
              exact canonRun_inD hD _ _
            · exact agree_wrq ha hqs noRegW_LInstr hpc1 hreg
                (fun _ hlt => absurd (by rw [srcsView_ld] at hlt; exact hlt) hc)
      | store sz rs2 rs1 off =>
        replace hl := ite_none_some' hl
        obtain ⟨hal, hl⟩ := hl
        cases l
        all_goals try (simp only [reduceCtorEq] at hl; done)
        rename_i aq rl b data asrc vsrc
        obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, rfl⟩ := ite_some_none hl
        subst h1 h2 h3 h4 h5 h6
        cases hm with
        | store _ _ _ _ _ _ ts hts hmsg hcoh hpv =>
          have hv' : (storeRun ws false (srcsView ws (srcR rs1))
              (max (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2))) (↑((s.rd rs1 + off) % two64))
              (toBytes (s.rd rs2) sz).length ts).wVcap < θ := hv
          rw [storeRun_vcap] at hv'
          have hrs1 : s'.rd rs1 = s.rd rs1 := agree_src ha hqs (by omega)
          have hlit : litNextF s' (LStore false false (↑((s.rd rs1 + off) % two64)) (toBytes (s'.rd rs2) sz)
              (srcR rs1) (srcR rs2)) = some { s' with pc := s'.pc + 1, q := [LInstr] } := by
            rw [hst]; simp only [insNextF, instrNext]; rw [hrs1]; simp [hal]
          refine ⟨_, _, hlit, freeOk_none rfl,
            agree_same ha hqs noRegW_LInstr hpc1 (fun r => by unfold regv; simp only [acqPost_wRegv, storeRun_wRegv]), ?_⟩
          refine fwdInv_storeRun (ws0 := ws) (rl := false) (va := srcsView ws (srcR rs1)) hf rfl rfl (by simp [toBytes_len]) (fun hvf b x hx => ?_)
          have hrs2 : s'.rd rs2 = s.rd rs2 := agree_src ha hqs (by omega)
          right
          rw [hrs2]
          exact memByte_msg (hpos ts hts) hmsg hx
      | storeRl sz aq0 rs2 rs1 =>
        replace hl := ite_none_some' hl
        obtain ⟨hal, hl⟩ := hl
        cases l
        all_goals try (simp only [reduceCtorEq] at hl; done)
        rename_i aq rl b data asrc vsrc
        obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, rfl⟩ := ite_some_none hl
        subst h1 h2 h3 h4 h5 h6
        cases hm with
        | store _ _ _ _ _ _ ts hts hmsg hcoh hpv =>
          have hv' : (storeRun ws true (srcsView ws (srcR rs1))
              (max (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2))) (↑(s.rd rs1))
              (toBytes (s.rd rs2) sz).length ts).wVcap < θ := hv
          rw [storeRun_vcap] at hv'
          have hrs1 : s'.rd rs1 = s.rd rs1 := agree_src ha hqs (by omega)
          have hlit : litNextF s' (LStore aq true (↑(s.rd rs1)) (toBytes (s'.rd rs2) sz)
              (srcR rs1) (srcR rs2)) = some { s' with pc := s'.pc + 1, q := [LInstr] } := by
            rw [hst]; simp only [insNextF, instrNext]; rw [hrs1]; simp [hal]
          refine ⟨_, _, hlit, freeOk_none rfl,
            agree_same ha hqs noRegW_LInstr hpc1 (fun r => by unfold regv; simp only [acqPost_wRegv, storeRun_wRegv]), ?_⟩
          refine fwdInv_storeRun (ws0 := ws) (rl := true) (va := srcsView ws (srcR rs1)) hf rfl rfl (by simp [toBytes_len]) (fun hvf b x hx => ?_)
          have hrs2 : s'.rd rs2 = s.rd rs2 := agree_src ha hqs (by omega)
          right
          rw [hrs2]
          exact memByte_msg (hpos ts hts) hmsg hx
      | sc sz aq0 rl0 rd rs2 rs1 =>
        replace hl := ite_none_some' hl
        obtain ⟨hal, hl⟩ := hl
        cases l
        all_goals try (simp only [reduceCtorEq] at hl; done)
        · rename_i aq rl b data asrc vsrc
          obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, rfl⟩ := ite_some_none hl
          subst h1 h2 h3 h4 h5 h6
          cases hm with
          | sc _ _ _ _ _ _ ts R hR hts hmsg hx hlt hcoh hpv =>
            have hv' : (storeRun ws rl (srcsView ws (srcR rs1)) ts (↑(s.rd rs1))
                (toBytes (s.rd rs2) sz).length ts).wVcap < θ := hv
            rw [storeRun_vcap] at hv'
            have hrs1 : s'.rd rs1 = s.rd rs1 := agree_src ha hqs (by omega)
            have hlit : litNextF s' (LExStore (aq0 && rl) rl (↑(s.rd rs1)) (toBytes (s'.rd rs2) sz)
                (srcR rs1) (srcR rs2)) = some { s' with regs := s'.wr rd 0, pc := s'.pc + 1, q := regWL rd [.DLdRes] ++ [LExFail, LInstr] } := by
              rw [hst]; simp only [insNextF, scNextF]; rw [hrs1]; simp
            refine ⟨_, _, hlit, freeOk_none rfl,
              agree_wrq ha hqs noRegW_fail hpc1 (fun r => by unfold regv; simp only [acqPost_wRegv, storeRun_wRegv]) (fun _ _ => rfl), ?_⟩
            exact fwdInv_storeRun (ws0 := ws) (rl := rl) (va := srcsView ws (srcR rs1)) hf rfl rfl (by simp [toBytes_len])
              (fun hvf b x hx => .inl (hlow _ hvf b x hx))
        · cases hl
          cases hm
          have hlit : litNextF s' LExFail = some { s' with regs := s'.wr rd 1, pc := s'.pc + 1, q := regWL rd [] ++ [LExFail, LInstr] } := by
            rw [hst]; simp only [insNextF, scNextF]
          exact ⟨_, _, hlit, freeOk_none rfl,
            agree_wrq ha hqs noRegW_fail hpc1 (fun r => rfl) (fun _ _ => rfl), fwdInv_nomsg rfl hf⟩
      | amo op sz aq0 rl0 rd rs2 rs1 =>
        replace hl := ite_none_some' hl
        obtain ⟨hal, hl⟩ := hl
        cases l
        all_goals try (simp only [reduceCtorEq] at hl; done)
        rename_i aq rl b tvs data asrc vsrc
        obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, rfl⟩ := ite_some_none hl
        subst h1 h2 h3 h5 h6 h7
        cases hm with
        | rmw _ _ _ _ _ _ _ ts hlen hts hmsg hok hx hcoh hpv vi _ _ =>   -- MachFix-R-b5
          have hv' : (storeRun (loadRunV ws aq false (srcsView ws (srcR rs1)) vi (↑(s.rd rs1)) tvs) rl
              (srcsView ws (srcR rs1)) ts (↑(s.rd rs1)) (toBytes (amoOp op sz (ofBytes (tvs.map Prod.snd))
                (s.rd rs2 % 2 ^ (8 * sz))) sz).length ts).wVcap < θ := hv
          rw [storeRun_vcap, loadRunV_vcap] at hv'
          have hrs1 : s'.rd rs1 = s.rd rs1 := agree_src ha hqs (by omega)
          have hreg : ∀ r, regv (amoPost (storeRun (loadRunV ws aq false (srcsView ws (srcR rs1)) vi (↑(s.rd rs1)) tvs)
              rl (srcsView ws (srcR rs1)) ts (↑(s.rd rs1)) (toBytes (amoOp op sz (ofBytes (tvs.map Prod.snd))
                (s.rd rs2 % 2 ^ (8 * sz))) sz).length ts) aq ts) r = regv ws r := by
            intro r
            unfold regv; simp only [amoPost_wRegv, storeRun_wRegv, loadRunV_wRegv]
          have hfw : ∀ m : PMsg, m.pa = ↑(s.rd rs1) →
              m.data.length = (toBytes (amoOp op sz (ofBytes (tvs.map Prod.snd)) (s.rd rs2 % 2 ^ (8 * sz))) sz).length →
              fwdInv img M D θ (amoPost (storeRun (loadRunV ws aq false (srcsView ws (srcR rs1)) vi               (↑(s.rd rs1)) tvs) rl (srcsView ws (srcR rs1)) ts (↑(s.rd rs1))
              (toBytes (amoOp op sz (ofBytes (tvs.map Prod.snd)) (s.rd rs2 % 2 ^ (8 * sz))) sz).length ts)
              aq ts) (w' ++ [m]) := fun m hpa hlen =>
            fwdInv_storeRun (rl := rl) (va := srcsView ws (srcR rs1)) hf (loadRunV_fwd _ _ _ _ _ _ _) hpa hlen (fun hvf b x hx => .inl (hlow _ hvf b x hx))
          have hld : (loadRunV ws aq false (srcsView ws (srcR rs1)) vi (↑(s.rd rs1)) tvs).wLdv ≤
              (amoPost (storeRun (loadRunV ws aq false (srcsView ws (srcR rs1)) vi (↑(s.rd rs1)) tvs) rl
                (srcsView ws (srcR rs1)) ts (↑(s.rd rs1)) (toBytes (amoOp op sz (ofBytes (tvs.map Prod.snd))
                  (s.rd rs2 % 2 ^ (8 * sz))) sz).length ts) aq ts).wLdv := by
            simp only [amoPost, storeRun_ldv]; omega
          by_cases hc : (amoPost (storeRun (loadRunV ws aq false (srcsView ws (srcR rs1)) vi (↑(s.rd rs1)) tvs) rl
                (srcsView ws (srcR rs1)) ts (↑(s.rd rs1)) (toBytes (amoOp op sz (ofBytes (tvs.map Prod.snd))
                  (s.rd rs2 % 2 ^ (8 * sz))) sz).length ts) aq ts).wLdv < θ
          · refine ⟨LRmw aq rl (↑(s.rd rs1)) tvs (toBytes (amoOp op sz (ofBytes (tvs.map Prod.snd))
                (s'.rd rs2 % 2 ^ (8 * sz))) sz) (srcR rs1) (srcR rs2),
              { s' with regs := s'.wr rd (sext sz (ofBytes (tvs.map Prod.snd))), pc := s'.pc + 1, q := regWL rd [.DLdRes] ++ [LInstr] }, ?_, ?_, ?_, hfw _ rfl (by simp [toBytes_len])⟩
            · rw [hst]; simp only [insNextF, instrNext]; rw [hrs1]; simp [hal, h4]
            · intro base tvs' hr
              simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hr
              obtain ⟨rfl, rfl⟩ := hr
              exact lowLoadV hlow hf hok hld hc
            · exact agree_wrq ha hqs noRegW_LInstr hpc1 hreg (fun _ _ => rfl)
          · refine ⟨LRmw aq rl (↑(s.rd rs1)) (canonRun D (↑(s.rd rs1)) sz)
                (toBytes (amoOp op sz (ofBytes ((canonRun D (↑(s.rd rs1)) sz).map Prod.snd))
                  (s'.rd rs2 % 2 ^ (8 * sz))) sz) (srcR rs1) (srcR rs2),
              { s' with regs := s'.wr rd (sext sz (ofBytes ((canonRun D (↑(s.rd rs1)) sz).map Prod.snd))), pc := s'.pc + 1, q := regWL rd [.DLdRes] ++ [LInstr] }, ?_, ?_, ?_, hfw _ rfl (by simp [toBytes_len])⟩
            · rw [hst]; simp only [insNextF, instrNext]; rw [hrs1]; simp [hal, canonRun_len]
            · intro base tvs' hr
              simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hr
              obtain ⟨rfl, rfl⟩ := hr
              exact canonRun_inD hD _ _
            · exact agree_wrq ha hqs noRegW_LInstr hpc1 hreg
                (fun _ hlt => absurd (by rw [srcsView_ld] at hlt; exact hlt) hc)
      | loadAqPc => cases hl
      | storeRlPc => cases hl

/-! ## The fulfilling step -/

theorem memStep_some_msg {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ts : Nat} {ws' : PState} {prom' : GSet Nat} (h : memStep img log i prom ws l (some ts) ws' prom') :
    labelMsg i l ≠ none := by
  cases h <;> simp [labelMsg]

theorem go1_noMsg {s : LP} {regs' : List Nat} {pc' : Nat} {labs : List PLabel} {l : PLabel} {s' : LP} {i : Nat}
    (h : go1 s regs' pc' labs l = some s') (hl : ∀ x ∈ labs.take 1, labelMsg i x = none) : labelMsg i l = none :=
  hl l (go1_mem h)

theorem regWL_noMsg (i rd : Nat) (srcs : List Dsrc) : ∀ x ∈ (regWL rd srcs ++ [LInstr]).take 1, labelMsg i x = none := by
  unfold regWL; split <;> simp [labelMsg]

/-- THE FULFILLING STEP: its label is a free step of the agreeing free state. -/
theorem ni_final {img : Image} {M : List PMsg} {D : Int → List (BitVec 8)} {i θ : Nat}
    (hlow : lowM img M D θ)
    {s s1 : LP} {ws ws1 : PState} {prom prom1 : GSet Nat} {l : PLabel}
    (hl : litNext s l = some s1) (hm : memStep img M i prom ws l (some θ) ws1 prom1) (hq : qOk s.q)
    {s' : LP} {w' : List PMsg} (ha : agree θ ws s s') (hf : fwdInv img M D θ ws w') :
    ∃ s1', litNextF s' l = some s1' ∧ freeOk D w' l := by
  have hmsg := memStep_some_msg hm
  unfold litNext at hl
  cases hqs : s.q with
  | cons l0 rest =>
    rw [hqs] at hl hq
    simp only at hl
    split at hl
    · rename_i he
      subst he
      have hq0 := hq.1 l (List.mem_cons_self ..)
      cases l <;> simp only [qLab, Bool.false_eq_true] at hq0 <;> simp [labelMsg] at hmsg
    · cases hl
  | nil =>
    rw [hqs] at hl
    simp only at hl
    cases hp : s.prog[s.pc]? with
    | none => rw [hp] at hl; cases hl
    | some ins =>
      rw [hp] at hl
      simp only at hl
      have hst : ∀ l', litNextF s' l' = insNextF s.prog.length s' ins l' := by
        intro l'; unfold litNextF; rw [ha.q, hqs]; simp only; rw [ha.prog, ha.pc, hp]
      cases ins with
      | alui op rd rs1 imm => simp only [instrNext] at hl; exact absurd (go1_noMsg hl (regWL_noMsg _ _ _)) hmsg
      | alu op rd rs1 rs2 => simp only [instrNext] at hl; exact absurd (go1_noMsg hl (regWL_noMsg _ _ _)) hmsg
      | csrr rd v => simp only [instrNext] at hl; exact absurd (go1_noMsg hl (regWL_noMsg _ _ _)) hmsg
      | fence f =>
        simp only [instrNext] at hl; exact absurd (go1_noMsg hl (by simp [labelMsg])) hmsg
      | fenceTso =>
        simp only [instrNext] at hl; exact absurd (go1_noMsg hl (by simp [labelMsg])) hmsg
      | fencei =>
        simp only [instrNext] at hl; exact absurd (go1_noMsg hl (by simp [labelMsg])) hmsg
      | nop =>
        simp only [instrNext] at hl; exact absurd (go1_noMsg hl (by simp [labelMsg])) hmsg
      | jmp tgt =>
        replace hl := ite_none_some hl
        exact absurd (go1_noMsg hl (by simp [labelMsg])) hmsg
      | br c rs1 rs2 tgt =>
        replace hl := ite_none_some hl
        exact absurd (go1_noMsg hl (by simp [labelMsg])) hmsg
      | load sz sgn rd rs1 off =>
        replace hl := ite_none_some hl
        cases l
        all_goals try (simp only [reduceCtorEq] at hl; done)
        cases hm
      | loadAq sz rl0 rd rs1 =>
        replace hl := ite_none_some hl
        cases l
        all_goals try (simp only [reduceCtorEq] at hl; done)
        cases hm
      | lr sz aq0 rl0 rd rs1 =>
        replace hl := ite_none_some hl
        cases l
        all_goals try (simp only [reduceCtorEq] at hl; done)
        cases hm
      | loadAqPc => cases hl
      | storeRlPc => cases hl
      | store sz rs2 rs1 off =>
        replace hl := ite_none_some' hl
        obtain ⟨hal, hl⟩ := hl
        cases l
        all_goals try (simp only [reduceCtorEq] at hl; done)
        rename_i aq rl b data asrc vsrc
        obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, rfl⟩ := ite_some_none hl
        subst h1 h2 h3 h4 h5 h6
        cases hm with
        | store _ _ _ _ _ _ ts hts hmsg' hcoh hpv =>
          have h0 := stPre_ge ws false (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2))
          have h00 := stPreA_ge ws false false (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2))
          have hrs1 : s'.rd rs1 = s.rd rs1 := agree_src ha hqs (by omega)
          have hrs2 : s'.rd rs2 = s.rd rs2 := agree_src ha hqs (by omega)
          refine ⟨{ s' with pc := s'.pc + 1, q := [LInstr] }, ?_, freeOk_none rfl⟩
          rw [hst]; simp only [insNextF, instrNext]; rw [hrs1, hrs2]; simp [hal]
      | storeRl sz aq0 rs2 rs1 =>
        replace hl := ite_none_some' hl
        obtain ⟨hal, hl⟩ := hl
        cases l
        all_goals try (simp only [reduceCtorEq] at hl; done)
        rename_i aq rl b data asrc vsrc
        obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, rfl⟩ := ite_some_none hl
        subst h1 h2 h3 h4 h5 h6
        cases hm with
        | store _ _ _ _ _ _ ts hts hmsg' hcoh hpv =>
          have h0 := stPre_ge ws true (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2))
          have h00 := stPreA_ge ws aq true (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2))
          have hrs1 : s'.rd rs1 = s.rd rs1 := agree_src ha hqs (by omega)
          have hrs2 : s'.rd rs2 = s.rd rs2 := agree_src ha hqs (by omega)
          refine ⟨{ s' with pc := s'.pc + 1, q := [LInstr] }, ?_, freeOk_none rfl⟩
          rw [hst]; simp only [insNextF, instrNext]; rw [hrs1, hrs2]; simp [hal]
      | sc sz aq0 rl0 rd rs2 rs1 =>
        replace hl := ite_none_some' hl
        obtain ⟨hal, hl⟩ := hl
        cases l
        all_goals try (simp only [reduceCtorEq] at hl; done)
        · rename_i aq rl b data asrc vsrc
          obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, rfl⟩ := ite_some_none hl
          subst h1 h2 h3 h4 h5 h6
          cases hm with
          | sc _ _ _ _ _ _ ts R hR hts hmsg' hx hlt hcoh hpv =>
            have h0 := stPre_ge ws rl (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2))
            have h00 := stPreA_ge ws (aq0 && rl) rl (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2))
            have hrs1 : s'.rd rs1 = s.rd rs1 := agree_src ha hqs (by omega)
            have hrs2 : s'.rd rs2 = s.rd rs2 := agree_src ha hqs (by omega)
            refine ⟨{ s' with regs := s'.wr rd 0, pc := s'.pc + 1, q := regWL rd [.DLdRes] ++ [LExFail, LInstr] }, ?_, freeOk_none rfl⟩
            rw [hst]; simp only [insNextF, scNextF]; rw [hrs1, hrs2]; simp
        · cases hm
      | amo op sz aq0 rl0 rd rs2 rs1 =>
        replace hl := ite_none_some' hl
        obtain ⟨hal, hl⟩ := hl
        cases l
        all_goals try (simp only [reduceCtorEq] at hl; done)
        rename_i aq rl b tvs data asrc vsrc
        obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, rfl⟩ := ite_some_none hl
        subst h1 h2 h3 h5 h6 h7
        cases hm with
        | rmw _ _ _ _ _ _ _ ts hlen hts hmsg' hok hx hcoh hpv =>
          have h0 := stPre_ge (loadRun ws aq false (srcsView ws (srcR rs1)) (↑(s.rd rs1)) tvs) rl
            (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2))
          have hrs1 : s'.rd rs1 = s.rd rs1 := agree_src ha hqs (by omega)
          have hrs2 : s'.rd rs2 = s.rd rs2 := agree_src ha hqs (by omega)
          refine ⟨{ s' with regs := s'.wr rd (sext sz (ofBytes (tvs.map Prod.snd))), pc := s'.pc + 1, q := regWL rd [.DLdRes] ++ [LInstr] }, ?_, ?_⟩
          · rw [hst]; simp only [insNextF, instrNext]; rw [hrs1, hrs2]; simp [hal, h4]
          · intro base tvs' hr
            simp only [labelReads, Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl⟩ := hr
            have hc := (loadBytes_coh aq (ldPre ws aq false (srcsView ws (srcR rs1))) ws (↑(s.rd rs1)) tvs).2
            have hc' : bytesAll (fun x u _ => fwdView ws aq x u ≤ coh (loadRun ws aq false (srcsView ws (srcR rs1))
                (↑(s.rd rs1)) tvs) x) (↑(s.rd rs1)) tvs :=
              bytesAll_mono (fun _ _ _ h => h.1) _ _ hc
            rw [← hlen] at hcoh
            have hlt := cohBelow_bytes _ _ hcoh hc'
            exact vals_inD (aq := aq) hlow hf _ _
              (bytesAll_and _ _ (bytesAll_mono (fun _ _ _ hp => hp.1) _ _ hok) hlt)

/-! ## The simulation along a run, and NOTA -/

theorem agree_refl (θ : Nat) (ws : PState) (s : LP) : agree θ ws s s := ⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

theorem fwdInv_init (img : Image) (M : List PMsg) (D : Int → List (BitVec 8)) (θ : Nat) (w : List PMsg) :
    fwdInv img M D θ psInit w := by
  intro a tf vf h
  simp [psInit, lookupEmpty] at h

theorem ni_run {img : Image} {M : List PMsg} {D : Int → List (BitVec 8)} {i θ : Nat}
    (hlow : lowM img M D θ) (hD : ∀ a, D a ≠ []) {s0 : LP} :
    ∀ {x z : LP × PState × GSet Nat} {tr : List (PLabel × Option Nat)},
      soloSteps litStep img M i x tr z → z.2.1.wVcap < θ → (∀ t ∈ x.2.2, 0 < t) → qOk x.1.q →
      ∀ {s' : LP} {w' : List PMsg} {ls : List PLabel}, freeSteps D i (s0, []) ls (s', w') →
        agree θ x.2.1 x.1 s' → fwdInv img M D θ x.2.1 w' →
      ∃ s'' w'' ls', freeSteps D i (s0, []) ls' (s'', w'') ∧ agree θ z.2.1 z.1 s'' ∧
        fwdInv img M D θ z.2.1 w'' ∧ qOk z.1.q := by
  intro x z tr h
  induction h with
  | refl x => intro _ _ hq s' w' ls hfs ha hf; exact ⟨s', w', ls, hfs, ha, hf, hq⟩
  | step x l ots p' ws' prom' tr y hp hm hrest ih =>
    intro hvy hpos hq s' w' ls hfs ha hf
    have hv1 : ws'.wVcap < θ := Nat.lt_of_le_of_lt (solo_vcap hrest) hvy
    obtain ⟨l', s1', h1, h2, h3, h4⟩ := ni_step hlow hD hp hm hpos hq hv1 ha hf
    have hpos' : ∀ t ∈ prom', 0 < t := by
      rcases memStep_prom hm with ⟨_, he⟩ | ⟨ts, _, _, he⟩
      · rw [he]; exact hpos
      · rw [he]; exact fun t ht => hpos t (elemOfDifference.1 ht).1
    exact ih hvy hpos' (litNext_q hq hp) (freeSteps_snoc hfs h1 h2) h3 h4

/-- **NOTA** (statement 5, corrected form): if the domain `D` holds the image and is closed for every hart, then
every byte of the final memory `M` of a family of solo runs (one per hart, each from its initial state with every
own message of `M` promised, each fulfilling all of them) is in `D`. -/
theorem nota {img : Image} {M : List PMsg} {D : Int → List (BitVec 8)} {ps : List LP}
    (hD : ∀ a, D a ≠ []) (himg : ∀ a b, img a = some b → b ∈ D a)
    (hcl : ∀ (h : Nat) (p : LP), ps[h]? = some p → closedFrom D h p)
    (hq : ∀ (h : Nat) (p : LP), ps[h]? = some p → qOk p.q)
    (hown : ∀ (k : Nat) (m : PMsg), M[k]? = some m → ∃ (h : Nat) (p : LP), m.tid = some h ∧ ps[h]? = some p)
    (hruns : ∀ (h : Nat) (p : LP), ps[h]? = some p → ∃ (P0 : GSet Nat) (y : LP × PState × GSet Nat)
      (tr : List (PLabel × Option Nat)), (∀ t, t ∈ P0 ↔ 0 < t ∧ ownTs M h t) ∧
      soloSteps litStep img M h (p, psInit, P0) tr y ∧ ∀ t, t ∉ y.2.2) :
    ∀ t a b, memByte img M t a = some b → b ∈ D a := by
  have key : ∀ θ, lowM img M D θ := by
    intro θ
    induction θ with
    | zero => intro t ht; omega
    | succ θ ih =>
      intro t ht a b hb
      rcases Nat.lt_or_ge t θ with h1 | h1
      · exact ih t h1 a b hb
      · have e : t = θ := by omega
        subst e
        cases t with
        | zero => exact himg a b hb
        | succ k =>
          simp only [memByte] at hb
          cases hk : M[k]? with
          | none => rw [hk] at hb; cases hb
          | some m =>
            rw [hk] at hb
            obtain ⟨h, p, htid, hp⟩ := hown k m hk
            obtain ⟨P0, y, tr, hP0, hrun, hend⟩ := hruns h p hp
            have hin : k + 1 ∈ P0 := (hP0 _).2 ⟨by omega, m, by simpa using hk, htid⟩
            obtain ⟨z, tr1, l, p', ws', prom', k1, k2, k3⟩ := solo_fulfil hrun hin (hend _)
            have hvz := fulfil_vcap k3
            obtain ⟨s'', w'', ls', hfs, ha, hf, hqz⟩ := ni_run ih hD k1 hvz
              (fun t ht => ((hP0 t).1 ht).1) (hq h p hp) (.refl _) (agree_refl _ _ _) (fwdInv_init _ _ _ _ _)
            obtain ⟨s1', hlit, hok⟩ := ni_final ih k2 k3 hqz ha hf
            have hm := (memStep_msg k3).1 _ rfl
            simp only [Nat.add_sub_cancel] at hm
            rw [hk] at hm
            have hin' := hcl h p hp _ _ (freeSteps_snoc hfs hlit hok) m (by rw [← hm]; simp)
            exact msgIn_byteAt hin' hb
  intro t a b hb
  exact key (t + 1) t (by omega) a b hb

/-- **NOTA, depth form**: for a chain of domains `Ds 0 ⊆ Ds 1 ⊆ …` holding the image, in which free runs over
`Ds j` only emit messages in `Ds (j + 1)`, every byte at timestamp `t` of the final memory is in `Ds t`: a
message's value has a justification chain no longer than its timestamp. -/
theorem nota_depth {img : Image} {M : List PMsg} {Ds : Nat → Int → List (BitVec 8)} {ps : List LP} {N : Nat}
    (hD : ∀ j a, Ds j a ≠ []) (himg : ∀ a b, img a = some b → b ∈ Ds 0 a)
    (hmono : ∀ j a b, b ∈ Ds j a → b ∈ Ds (j + 1) a)
    (hcl : ∀ (j h : Nat) (p : LP), j < N → ps[h]? = some p → closedInto (Ds j) (Ds (j + 1)) h p)
    (hq : ∀ (h : Nat) (p : LP), ps[h]? = some p → qOk p.q)
    (hown : ∀ (k : Nat) (m : PMsg), M[k]? = some m → ∃ (h : Nat) (p : LP), m.tid = some h ∧ ps[h]? = some p)
    (hruns : ∀ (h : Nat) (p : LP), ps[h]? = some p → ∃ (P0 : GSet Nat) (y : LP × PState × GSet Nat)
      (tr : List (PLabel × Option Nat)), (∀ t, t ∈ P0 ↔ 0 < t ∧ ownTs M h t) ∧
      soloSteps litStep img M h (p, psInit, P0) tr y ∧ ∀ t, t ∉ y.2.2) :
    ∀ t a b, t ≤ N → memByte img M t a = some b → b ∈ Ds t a := by
  have hle : ∀ j k a b, j ≤ k → b ∈ Ds j a → b ∈ Ds k a := by
    intro j k a b hjk hb
    induction k with
    | zero =>
      have : j = 0 := by omega
      subst this; exact hb
    | succ k ih =>
      rcases Nat.lt_or_ge j (k + 1) with h1 | h1
      · exact hmono k a b (ih (by omega))
      · have : j = k + 1 := by omega
        subst this; exact hb
  have key : ∀ θ, ∀ t, t < θ → ∀ a b, t ≤ N → memByte img M t a = some b → b ∈ Ds t a := by
    intro θ
    induction θ with
    | zero => intro t ht; omega
    | succ θ ih =>
      intro t ht a b htN hb
      rcases Nat.lt_or_ge t θ with h1 | h1
      · exact ih t h1 a b htN hb
      · have e : t = θ := by omega
        subst e
        cases t with
        | zero => exact himg a b hb
        | succ k =>
          simp only [memByte] at hb
          cases hk : M[k]? with
          | none => rw [hk] at hb; cases hb
          | some m =>
            rw [hk] at hb
            have hlow : lowM img M (Ds k) (k + 1) := fun t ht a b hb =>
              hle t k a b (by omega) (ih t ht a b (by omega) hb)
            obtain ⟨h, p, htid, hp⟩ := hown k m hk
            obtain ⟨P0, y, tr, hP0, hrun, hend⟩ := hruns h p hp
            have hin : k + 1 ∈ P0 := (hP0 _).2 ⟨by omega, m, by simpa using hk, htid⟩
            obtain ⟨z, tr1, l, p', ws', prom', k1, k2, k3⟩ := solo_fulfil hrun hin (hend _)
            have hvz := fulfil_vcap k3
            obtain ⟨s'', w'', ls', hfs, ha, hf, hqz⟩ := ni_run hlow (hD k) k1 hvz
              (fun t ht => ((hP0 t).1 ht).1) (hq h p hp) (.refl _) (agree_refl _ _ _) (fwdInv_init _ _ _ _ _)
            obtain ⟨s1', hlit, hok⟩ := ni_final hlow k2 k3 hqz ha hf
            have hm := (memStep_msg k3).1 _ rfl
            simp only [Nat.add_sub_cancel] at hm
            rw [hk] at hm
            have hin' := hcl k h p (by omega) hp _ _ (freeSteps_snoc hfs hlit hok) m (by rw [← hm]; simp)
            exact msgIn_byteAt hin' hb
  intro t a b htN hb
  exact key (t + 1) t (by omega) a b htN hb

end Weak.Prom.Mach
