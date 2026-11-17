/-
Weak/Mini: **E2 part 2 — the front ends agree** (mini plan rev 4 §2 L2, E2).

Labels, sources and program states of MiniMach as machine v2's (`embL`, `embSs`, `embF`), and THE FRONT-END
EQUATION `xNext_emb`: on a hart of an F program, the full loop front end `xNext P.xs` (OwnAFront.lean:59) at the
embedded state answers the embedded label exactly as the mini front end `Mach.mNext` does, and `xNext_image`: every
UNTORN label the full front end accepts there is an embedded one.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.EqMachBytes

namespace MiniEq

open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert Weak.Prom.OA
open Weak.Prom.Ref (Instr)
open Weak (Dsrc)
open Weak.Mini
open PLabel

/-! ## 1. Embeddings -/

def embS : Mach.MSrc → Dsrc
  | .reg r => .DReg r
  | .ldres => .DLdRes

def embSs (l : List Mach.MSrc) : List Dsrc := l.map embS

/-- A mini label as a machine v2 label (MachCert.lean `instrNext`'s label shapes). -/
def embL (P : MProg) : Mach.MLab → PLabel
  | .load a t v asrc => LLoad false false (a : Int) ((wordB P v).map (fun b => (t, b))) (embSs asrc)
  | .store a v asrc vsrc => LStore false false (a : Int) (wordB P v) (embSs asrc) (embSs vsrc)
  | .fence pr pw sr sw => LFence pr pw sr sw
  | .regW rd srcs => LRegW rd (embSs srcs)
  | .ctrl srcs => LCtrl (embSs srcs)
  | .instr => LInstr

/-- Hart `i`'s text as full instructions (`(P.toTest cond).prog i`, `progF_eq`). -/
def progF (P : MProg) (i : Nat) : List Instr := (P.prog i).map (MI.toInstr P.sz)

/-- A mini program state as a litmus program state (MachCert.lean `LP`). -/
def embF (P : MProg) (i : Nat) (f : Mach.MFront) : LP := ⟨progF P i, f.pc, f.regs, f.q.map (embL P)⟩

/-- The answer-free labels an instruction queues. -/
def quiet : Mach.MLab → Bool
  | .fence .. | .regW .. | .ctrl .. | .instr => true
  | _ => false

def qOk (q : List Mach.MLab) : Prop := ∀ l ∈ q, quiet l = true

/-- A memory label at an aligned word with an in-range value. -/
def labOk (P : MProg) : Mach.MLab → Prop
  | .load a _ v _ => a % P.sz = 0 ∧ v < Mach.wordW P
  | .store a v _ _ => a % P.sz = 0 ∧ v < Mach.wordW P
  | _ => True

/-- A label carries untorn answers (plan §2 L2 `untorn`, per label). -/
def untornL (l : PLabel) : Prop := ∀ tvs, PF.loadLikeTvs l = some tvs → ∀ p ∈ tvs, ∀ q ∈ tvs, p.1 = q.1

/-! ## 2. Injectivity and small commutations -/

theorem embS_inj : Function.Injective embS := by
  intro a b h; cases a <;> cases b <;> simp_all [embS]

theorem embSs_inj : ∀ {a b : List Mach.MSrc}, embSs a = embSs b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [embSs] at h
  | _ :: _, [], h => by simp [embSs] at h
  | x :: a, y :: b, h => by
    simp only [embSs, List.map_cons, List.cons.injEq] at h
    rw [embS_inj h.1, embSs_inj (a := a) (b := b) h.2]

theorem map_pair_inj {t1 t2 : Nat} {bs1 bs2 : List (BitVec 8)} (hne : bs1 ≠ [])
    (h : bs1.map (fun b => (t1, b)) = bs2.map (fun b => (t2, b))) : t1 = t2 ∧ bs1 = bs2 := by
  have h2 := congrArg (List.map Prod.snd) h
  simp only [List.map_map] at h2
  have hs : ∀ (t : Nat) (l : List (BitVec 8)), l.map (Prod.snd ∘ fun b => (t, b)) = l := fun t l => by
    rw [show (Prod.snd ∘ fun b => (t, b)) = id from rfl, List.map_id]
  rw [hs, hs] at h2
  subst h2
  cases bs1 with
  | nil => exact absurd rfl hne
  | cons b r => simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h; exact ⟨h.1.1, rfl⟩

theorem embL_inj {P : MProg} (hsz : 0 < P.sz) {l1 l2 : Mach.MLab} (h : embL P l1 = embL P l2) : l1 = l2 := by
  cases l1 <;> cases l2 <;> simp only [embL, PLabel.LLoad.injEq, PLabel.LStore.injEq, PLabel.LFence.injEq,
    PLabel.LRegW.injEq, PLabel.LCtrl.injEq, reduceCtorEq, Int.ofNat_inj, true_and] at h
  case load.load a t v s a' t' v' s' =>
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨ht, hb⟩ := map_pair_inj (wordB_ne_nil hsz v) h2
    rw [h1, ht, wordB_inj hb, embSs_inj h3]
  case store.store a v s1 s2 a' v' s1' s2' =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    rw [h1, wordB_inj h2, embSs_inj h3, embSs_inj h4]
  case regW.regW => rw [h.1, embSs_inj h.2]
  case ctrl.ctrl => rw [embSs_inj h]
  case fence.fence => obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl
  case instr.instr => rfl

theorem srcR_emb (r : Nat) : embSs (Weak.Mini.Mach.srcR r) = Weak.Prom.Mach.srcR r := by
  unfold Weak.Mini.Mach.srcR Weak.Prom.Mach.srcR embSs; split <;> rfl

theorem srcR2_emb (r s : Nat) :
    embSs (Weak.Mini.Mach.srcR r ++ Weak.Mini.Mach.srcR s) = Weak.Prom.Mach.srcR r ++ Weak.Prom.Mach.srcR s := by
  rw [← srcR_emb, ← srcR_emb]; simp [embSs]

theorem regWL_emb (P : MProg) (rd : Nat) (srcs : List Mach.MSrc) :
    (Weak.Mini.Mach.regWL rd srcs).map (embL P) = Weak.Prom.Mach.regWL rd (embSs srcs) := by
  unfold Weak.Mini.Mach.regWL Weak.Prom.Mach.regWL; split <;> rfl

theorem aluOp_eq (op : MAlu) (a b : Nat) : Mach.aluOp op a b = Weak.Prom.Ref.aluOp op.toAlu a b := by
  cases op <;> rfl

theorem brEval_eq (c : MBrC) (a b : Nat) : Mach.brEval c a b = Weak.Prom.Ref.brEval c.toBrC a b := by
  cases c <;> rfl

theorem go1_emb (P : MProg) (hsz : 0 < P.sz) (i : Nat) (f : Mach.MFront) (regs' : List Nat) (pc' : Nat)
    (labs : List Mach.MLab) (ml : Mach.MLab) :
    Cert.go1 (embF P i f) regs' pc' (labs.map (embL P)) (embL P ml) =
      (Mach.go1 f regs' pc' labs ml).map (embF P i) := by
  cases labs with
  | nil => rfl
  | cons l0 rest =>
    simp only [Cert.go1, Mach.go1, List.map_cons]
    by_cases h : ml = l0
    · subst h; simp; rfl
    · rw [if_neg (fun h' => h (embL_inj hsz h')), if_neg h]; rfl

theorem go1_img {P : MProg} {i : Nat} {f : Mach.MFront} {regs' : List Nat} {pc' : Nat} {labs : List Mach.MLab}
    {l : PLabel} {s' : LP} (h : Cert.go1 (embF P i f) regs' pc' (labs.map (embL P)) l = some s') :
    ∃ ml, l = embL P ml := by
  cases labs with
  | nil => cases h
  | cons l0 rest =>
    simp only [Cert.go1, List.map_cons] at h
    split at h
    · next he => exact ⟨l0, he⟩
    · cases h

/-! ## 3. The hart's text -/

theorem progF_eq (P : MProg) (cond : Weak.Prom.Ref.OC) (i : Nat) : (P.toTest cond).prog i = progF P i := by
  simp only [Weak.Prom.Ref.Test.prog, MProg.toTest, progF, MProg.prog, List.getElem?_map]
  cases P.harts[i]? <;> rfl

theorem xOf_progF (P : MProg) {i : Nat} (hi : i < P.harts.length) :
    xOf P.xs (progF P i) = some ((progF P i).map XI.i) := by
  unfold xOf
  have hmem : (progF P i).map XI.i ∈ P.xs := by
    unfold MProg.xs progF MProg.prog
    rw [List.mem_map]
    refine ⟨P.harts[i], List.getElem_mem hi, ?_⟩
    simp [List.getElem?_eq_getElem hi, List.map_map]
  cases h : P.xs.find? (fun X => decide (X.map XI.base = progF P i)) with
  | none =>
    have := List.find?_eq_none.1 h _ hmem
    simp only [List.map_map, decide_eq_true_eq] at this
    exact absurd (by rw [show XI.base ∘ XI.i = id from rfl, List.map_id]) this
  | some X =>
    have h1 := List.find?_some h
    have h2 := List.mem_of_find?_eq_some h
    unfold MProg.xs at h2
    obtain ⟨Y, -, rfl⟩ := List.mem_map.1 h2
    simp only [decide_eq_true_eq, List.map_map] at h1
    rw [← h1, List.map_map]
    rfl

theorem xNext_nil (P : MProg) {i : Nat} (hi : i < P.harts.length) (f : Mach.MFront) (hq : f.q = []) (l : PLabel) :
    xNext P.xs (embF P i f) l =
      match ((P.prog i)[f.pc]?).map (MI.toInstr P.sz) with
      | some (.br c rs1 rs2 tgt) =>
          if (progF P i).length < tgt then none else
          Cert.go1 (embF P i f) f.regs
            (if Weak.Prom.Ref.brEval c ((embF P i f).rd rs1) ((embF P i f).rd rs2) then tgt else f.pc + 1)
            [LCtrl (Weak.Prom.Mach.srcR rs1 ++ Weak.Prom.Mach.srcR rs2), LInstr] l
      | some (.jmp tgt) => if (progF P i).length < tgt then none else Cert.go1 (embF P i f) f.regs tgt [LInstr] l
      | some ins => instrNext (progF P i).length (embF P i f) ins l
      | none => none := by
  have hq' : (embF P i f).q = [] := by simp [embF, hq]
  unfold xNext
  rw [hq']
  simp only
  rw [show (embF P i f).prog = progF P i from rfl, xOf_progF P hi, Option.bind_some, List.getElem?_map]
  rw [show (embF P i f).pc = f.pc from rfl, progF, List.getElem?_map]
  cases hp : (P.prog i)[f.pc]? with
  | none => simp [litNext, embF, progF, List.getElem?_map, hp, hq]
  | some mi =>
    have hlit : litNext (embF P i f) l = instrNext (progF P i).length (embF P i f) (MI.toInstr P.sz mi) l := by
      simp [litNext, embF, progF, List.getElem?_map, hp, hq]
    cases mi <;> simp only [Option.map_some, MI.toInstr] <;> first | rfl | exact hlit

/-! ## 4. The front-end equation -/

theorem two64_eq : Weak.Prom.Ref.two64 = Mach.two64 := rfl

theorem aligned_iff {P : MProg} (hsz : 0 < P.sz) (x : Nat) : aligned x P.sz = decide (x % P.sz = 0) := by
  simp only [aligned, Bool.or_eq_decide, beq_iff_eq]
  have : P.sz ≠ 0 := by omega
  simp [this]

theorem labs_alui (P : MProg) (rd rs1 : Nat) :
    Weak.Prom.Mach.regWL rd (Weak.Prom.Mach.srcR rs1) ++ [LInstr] =
      (Weak.Mini.Mach.regWL rd (Weak.Mini.Mach.srcR rs1) ++ [Mach.MLab.instr]).map (embL P) := by
  rw [List.map_append, regWL_emb, srcR_emb]; rfl

theorem labs_alu (P : MProg) (rd rs1 rs2 : Nat) :
    Weak.Prom.Mach.regWL rd (Weak.Prom.Mach.srcR rs1 ++ Weak.Prom.Mach.srcR rs2) ++ [LInstr] =
      (Weak.Mini.Mach.regWL rd (Weak.Mini.Mach.srcR rs1 ++ Weak.Mini.Mach.srcR rs2) ++ [Mach.MLab.instr]).map
        (embL P) := by
  rw [List.map_append, regWL_emb, srcR2_emb]; rfl

theorem labs_ld (P : MProg) (rd : Nat) :
    Weak.Prom.Mach.regWL rd [.DLdRes] ++ [LInstr] =
      (Weak.Mini.Mach.regWL rd [.ldres] ++ [Mach.MLab.instr]).map (embL P) := by
  rw [List.map_append, regWL_emb]; rfl

theorem labs_br (P : MProg) (rs1 rs2 : Nat) :
    [LCtrl (Weak.Prom.Mach.srcR rs1 ++ Weak.Prom.Mach.srcR rs2), LInstr] =
      [Mach.MLab.ctrl (Weak.Mini.Mach.srcR rs1 ++ Weak.Mini.Mach.srcR rs2), Mach.MLab.instr].map (embL P) := by
  simp only [List.map_cons, List.map_nil, embL, srcR2_emb]

theorem untorn_map {t : Nat} : ∀ {tvs : List (Nat × BitVec 8)}, (∀ p ∈ tvs, p.1 = t) →
    (tvs.map Prod.snd).map (fun b => (t, b)) = tvs
  | [], _ => rfl
  | p :: r, h => by
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨by rw [← h p (List.mem_cons_self ..)], untorn_map (fun q hq => h q (List.mem_cons_of_mem _ hq))⟩

/-- **THE FRONT-END EQUATION**: at an embedded state of hart `i` of a well-formed F program, the full loop front end
answers an embedded label exactly as the mini front end. -/
theorem xNext_emb (P : MProg) (hwf : Mach.progWf P) {i : Nat} (hi : i < P.harts.length) (f : Mach.MFront)
    (ml : Mach.MLab) : xNext P.xs (embF P i f) (embL P ml) = (Mach.mNext P i f ml).map (embF P i) := by
  have hsz := hwf.1
  cases hq : f.q with
  | cons l0 rest =>
    have he : (embF P i f).q = embL P l0 :: rest.map (embL P) := by simp [embF, hq]
    rw [xNext_q (by rw [he]; simp)]
    unfold litNext Mach.mNext
    rw [he, hq]
    simp only
    by_cases h : ml = l0
    · subst h; simp only [if_true]; rfl
    · rw [if_neg (fun h' => h (embL_inj hsz h')), if_neg h]; rfl
  | nil =>
    rw [xNext_nil P hi f hq]
    unfold Mach.mNext
    rw [hq]
    simp only
    cases hp : (P.prog i)[f.pc]? with
    | none => rfl
    | some mi =>
      simp only [Option.map_some]
      cases mi with
      | alui op rd rs1 imm =>
        simp only [MI.toInstr, instrNext, Mach.instrNext, labs_alui P, aluOp_eq]
        exact go1_emb P hsz i f _ _ _ ml
      | alu op rd rs1 rs2 =>
        simp only [MI.toInstr, instrNext, Mach.instrNext, labs_alu P, aluOp_eq]
        exact go1_emb P hsz i f _ _ _ ml
      | fence fs =>
        simp only [MI.toInstr, instrNext, Mach.instrNext]
        exact go1_emb P hsz i f _ _ [.fence fs.pr fs.pw fs.sr fs.sw, .instr] ml
      | nop =>
        simp only [MI.toInstr, instrNext, Mach.instrNext]
        exact go1_emb P hsz i f _ _ [.instr] ml
      | jmp tgt =>
        simp only [MI.toInstr, Mach.instrNext, progF, List.length_map]
        split
        · rfl
        · exact go1_emb P hsz i f _ _ [.instr] ml
      | br c rs1 rs2 tgt =>
        simp only [MI.toInstr, Mach.instrNext, progF, List.length_map, labs_br P, brEval_eq]
        split
        · rfl
        · exact go1_emb P hsz i f _ _ _ ml
      | load sgn rd rs1 off =>
        simp only [MI.toInstr, instrNext, Mach.instrNext, aligned_iff hsz, two64_eq]
        have hrd : (embF P i f).rd rs1 = f.rd rs1 := rfl
        rw [hrd]
        by_cases ha : (f.rd rs1 + off) % Mach.two64 % P.sz = 0
        · simp only [ha, decide_true, Bool.not_true, Bool.false_eq_true, if_false, ne_eq, not_true_eq_false]
          cases ml with
          | load b t v asrc =>
            simp only [embL]
            split
            · next hc =>
              obtain ⟨-, -, hb, hl, hs⟩ := hc
              have hb' := Int.ofNat_inj.1 hb
              have hv : v < Mach.wordW P := wordB_len.1 (by rwa [List.length_map] at hl)
              have hs' := embSs_inj (hs.trans (srcR_emb rs1).symm)
              subst hb' hs'
              simp only [hv, and_self, if_true, Option.map_some, List.map_map]
              have hs : (wordB P v).map (Prod.snd ∘ fun b => (t, b)) = wordB P v := by
                rw [show (Prod.snd ∘ fun b => (t, b)) = id from rfl, List.map_id]
              rw [hs, ofBytes_wordB, labs_ld P]
              rfl
            · next hc =>
              rw [if_neg]
              · rfl
              rintro ⟨rfl, hv, rfl⟩
              exact hc ⟨trivial, trivial, rfl, by rw [List.length_map, wordB_len.2 hv], srcR_emb rs1⟩
          | _ => rfl
        · simp only [ha, decide_false, Bool.not_false, if_true, ne_eq, not_false_eq_true]
          rfl
      | store rs2 rs1 off =>
        simp only [MI.toInstr, instrNext, Mach.instrNext, aligned_iff hsz, two64_eq]
        have hrd : ∀ r, (embF P i f).rd r = f.rd r := fun _ => rfl
        rw [hrd, hrd]
        by_cases ha : (f.rd rs1 + off) % Mach.two64 % P.sz = 0
        · simp only [ha, decide_true, Bool.not_true, Bool.false_eq_true, if_false, ne_eq, not_true_eq_false]
          cases ml with
          | store b v asrc vsrc =>
            simp only [embL]
            split
            · next hc =>
              obtain ⟨-, -, hb, hd, hs1, hs2⟩ := hc
              have hb' := Int.ofNat_inj.1 hb
              rw [← wordB_mod P] at hd
              have hd' := wordB_inj hd
              have hs1' := embSs_inj (hs1.trans (srcR_emb rs1).symm)
              have hs2' := embSs_inj (hs2.trans (srcR_emb rs2).symm)
              subst hb' hd' hs1' hs2'
              simp only [and_self, if_true, Option.map_some]
              rfl
            · next hc =>
              rw [if_neg]
              · rfl
              rintro ⟨rfl, rfl, rfl, rfl⟩
              exact hc ⟨trivial, trivial, rfl, wordB_mod P _, srcR_emb rs1, srcR_emb rs2⟩
          | _ => rfl
        · simp only [ha, decide_false, Bool.not_false, if_true, ne_eq, not_false_eq_true]
          rfl

/-- **THE FRONT-END IMAGE**: every untorn label the full front end accepts at an embedded state is embedded. -/
theorem xNext_image (P : MProg) (hwf : Mach.progWf P) {i : Nat} (hi : i < P.harts.length) (f : Mach.MFront)
    {l : PLabel} {s' : LP} (h : xNext P.xs (embF P i f) l = some s') (hu : untornL l) : ∃ ml, l = embL P ml := by
  have hsz := hwf.1
  cases hq : f.q with
  | cons l0 rest =>
    have he : (embF P i f).q = embL P l0 :: rest.map (embL P) := by simp [embF, hq]
    rw [xNext_q (by rw [he]; simp)] at h
    unfold litNext at h
    rw [he] at h
    simp only at h
    split at h
    · next h' => exact ⟨l0, h'⟩
    · cases h
  | nil =>
    rw [xNext_nil P hi f hq] at h
    cases hp : (P.prog i)[f.pc]? with
    | none => rw [hp] at h; cases h
    | some mi =>
      rw [hp] at h
      simp only [Option.map_some] at h
      cases mi with
      | alui op rd rs1 imm =>
        simp only [MI.toInstr, instrNext, labs_alui P] at h
        exact go1_img h
      | alu op rd rs1 rs2 =>
        simp only [MI.toInstr, instrNext, labs_alu P] at h
        exact go1_img h
      | fence fs =>
        simp only [MI.toInstr, instrNext] at h
        exact go1_img (labs := [.fence fs.pr fs.pw fs.sr fs.sw, .instr]) h
      | nop =>
        simp only [MI.toInstr, instrNext] at h
        exact go1_img (labs := [.instr]) h
      | jmp tgt =>
        simp only [MI.toInstr] at h
        split at h
        · cases h
        · exact go1_img (labs := [.instr]) h
      | br c rs1 rs2 tgt =>
        simp only [MI.toInstr, labs_br P] at h
        split at h
        · cases h
        · exact go1_img h
      | load sgn rd rs1 off =>
        simp only [MI.toInstr, instrNext] at h
        split at h
        · cases h
        split at h
        · next aq rl b tvs asrc =>
          split at h
          · next hc =>
            obtain ⟨rfl, rfl, rfl, hlen, rfl⟩ := hc
            have hne : 0 < tvs.length := by omega
            have hut : ∀ p ∈ tvs, p.1 = (tvs[0]'hne).1 :=
              fun p hp => hu tvs rfl p hp _ (List.getElem_mem hne)
            have hl2 : (tvs.map Prod.snd).length = P.sz := by rw [List.length_map, hlen]
            have hv : ofBytes (tvs.map Prod.snd) < Mach.wordW P := by
              have := ofBytes_lt (tvs.map Prod.snd); rw [hl2] at this; exact this
            refine ⟨.load ((f.rd rs1 + off) % Mach.two64) (tvs[0]'hne).1 (ofBytes (tvs.map Prod.snd))
              (Weak.Mini.Mach.srcR rs1), ?_⟩
            simp only [embL, srcR_emb]
            rw [wordB_lt hv, ← hl2, toBytes_ofBytes, untorn_map hut]
            rfl
          · cases h
        · cases h
      | store rs2 rs1 off =>
        simp only [MI.toInstr, instrNext] at h
        split at h
        · cases h
        split at h
        · next aq rl b dat asrc vsrc =>
          split at h
          · next hc =>
            obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hc
            refine ⟨.store ((f.rd rs1 + off) % Mach.two64) (f.rd rs2 % Mach.wordW P) (Weak.Mini.Mach.srcR rs1)
              (Weak.Mini.Mach.srcR rs2), ?_⟩
            simp only [embL, srcR_emb, wordB_mod]
            rfl
          · cases h
        · cases h

/-! ## 5. Mini front-end facts -/

theorem go1_ok {f f' : Mach.MFront} {regs' : List Nat} {pc' : Nat} {labs : List Mach.MLab} {ml : Mach.MLab}
    (h : Mach.go1 f regs' pc' labs ml = some f') (hq : qOk labs) : qOk f'.q ∧ quiet ml = true := by
  cases labs with
  | nil => cases h
  | cons l0 rest =>
    simp only [Mach.go1] at h
    split at h
    · next he =>
      cases h; subst he
      exact ⟨fun l hl => hq l (List.mem_cons_of_mem _ hl), hq _ (List.mem_cons_self ..)⟩
    · cases h

theorem quiet_labOk {P : MProg} {ml : Mach.MLab} (h : quiet ml = true) : labOk P ml := by
  cases ml <;> simp_all [quiet, labOk]

theorem qOk_regWL (rd : Nat) (srcs : List Mach.MSrc) (rest : List Mach.MLab) (hr : qOk rest) :
    qOk (Weak.Mini.Mach.regWL rd srcs ++ rest) := by
  intro l hl
  unfold Weak.Mini.Mach.regWL at hl
  split at hl
  · exact hr l hl
  · simp only [List.singleton_append, List.mem_cons] at hl
    rcases hl with rfl | hl
    · rfl
    · exact hr l hl

theorem qOk_cons {l : Mach.MLab} {r : List Mach.MLab} (h1 : quiet l = true) (h2 : qOk r) : qOk (l :: r) := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact h1
  · exact h2 x hx

theorem qOk_nil : qOk [] := fun _ h => nomatch h

/-- The mini front end keeps its queue answer-free, and every memory label it emits is at an aligned word with an
in-range value. -/
theorem mNext_ok {P : MProg} {i : Nat} {f f' : Mach.MFront} {ml : Mach.MLab} (hq : qOk f.q)
    (h : Mach.mNext P i f ml = some f') : qOk f'.q ∧ labOk P ml := by
  unfold Mach.mNext at h
  cases hfq : f.q with
  | cons l0 rest =>
    rw [hfq] at h hq
    simp only at h
    split at h
    · next he =>
      cases h; subst he
      exact ⟨fun l hl => hq l (List.mem_cons_of_mem _ hl), quiet_labOk (hq _ (List.mem_cons_self ..))⟩
    · cases h
  | nil =>
    rw [hfq] at h
    simp only at h
    split at h
    · next ins hins =>
      have hi := qOk_cons (l := Mach.MLab.instr) rfl qOk_nil
      cases ins with
      | alui op rd rs1 imm =>
        simp only [Mach.instrNext] at h
        have := go1_ok h (qOk_regWL _ _ _ hi); exact ⟨this.1, quiet_labOk this.2⟩
      | alu op rd rs1 rs2 =>
        simp only [Mach.instrNext] at h
        have := go1_ok h (qOk_regWL _ _ _ hi); exact ⟨this.1, quiet_labOk this.2⟩
      | fence fs =>
        simp only [Mach.instrNext] at h
        have := go1_ok h (qOk_cons (l := Mach.MLab.fence fs.pr fs.pw fs.sr fs.sw) rfl hi)
        exact ⟨this.1, quiet_labOk this.2⟩
      | nop =>
        simp only [Mach.instrNext] at h
        have := go1_ok h hi; exact ⟨this.1, quiet_labOk this.2⟩
      | jmp tgt =>
        simp only [Mach.instrNext] at h
        split at h
        · cases h
        · have := go1_ok h hi; exact ⟨this.1, quiet_labOk this.2⟩
      | br c rs1 rs2 tgt =>
        simp only [Mach.instrNext] at h
        split at h
        · cases h
        · have := go1_ok h (qOk_cons (l := Mach.MLab.ctrl _) rfl hi); exact ⟨this.1, quiet_labOk this.2⟩
      | load sgn rd rs1 off =>
        simp only [Mach.instrNext] at h
        split at h
        · cases h
        · next ha =>
          split at h
          · next b t v asrc =>
            split at h
            · next hc =>
              cases h
              obtain ⟨rfl, hv, -⟩ := hc
              exact ⟨qOk_regWL _ _ _ hi, by simpa using ha, hv⟩
            · cases h
          · cases h
      | store rs2 rs1 off =>
        simp only [Mach.instrNext] at h
        split at h
        · cases h
        · next ha =>
          split at h
          · next b v asrc vsrc =>
            split at h
            · next hc =>
              cases h
              obtain ⟨rfl, rfl, -, -⟩ := hc
              exact ⟨hi, by simpa using ha, Nat.mod_lt _ (wordW_pos P)⟩
            · cases h
          · cases h
    · cases h

end MiniEq
