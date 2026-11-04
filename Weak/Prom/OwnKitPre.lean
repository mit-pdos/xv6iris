/-
Weak/Prom: **track (b)'s litmus kit over NF_R with the PRE-STATE RELEASE CLASS** (stage S4b part 3, tag S4b3).  A
copy of OwnKit.lean's step facts and instruction rules over OwnWpPre.lean's `wpO`, with `relClassPre` for
`relClass` in the fulfil facts.  Reused unchanged from OwnKit.lean: `litOW`, `litDoneR`, `fulO`, `rmwOk`,
`take_msg`, `memStep_*_inv`, `upd_pr_same`, `wrPre_quiet`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnWpPre
import Weak.Prom.OwnKit

namespace Weak.Prom.Own.Pre

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr.Pre Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.PF (quietL qPost qPosts LPstep LPstep_wr LPstep_same ldVal instrR quiet_inv quiet_regWL pc_lt amoD
  litNext_fence litNext_amo litDone litDone_q litDone_pc litNext_q litNext_end litNext_load litNext_store
  litNext_alui litNext_br)
open Weak.Prom.Ref (Instr two64 aluOp brEval amoOp sext)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

theorem relClassPre_none {ws : PState} {l : PLabel} (h : Nfr.wrPre ws l = none) : ¬ relClassPre ws l := by
  rintro ⟨pv, hpv, _⟩; rw [h] at hpv; cases hpv

/-- THE TWO CASES of an NF_R hart step (OwnLang.lean `hstepO`), as one disjunction. -/
theorem hstepO_cases {V P : Type} {w : OW P V} {h : Nat} {σ σ' : OSt V} {s s' : P} {ws ws' : PState}
    {l : PLabel} {ots : Option Nat} (hs : hstepO w h σ s ws l ots s' ws' σ') :
    w.pstep s () l s' () ∧
    ((∃ pr', memStep w.img (w.M.take σ.n) h (σ.pr h) ws l ots ws' pr' ∧ ¬ relClassPre ws l ∧
        σ' = { σ with pr := upd σ.pr h pr' }) ∨
     (∃ pr', σ.n < w.M.length ∧ authorAt w.M σ.n = some h ∧ relClassPre ws l ∧ ots = some (σ.n + 1) ∧
        memStep w.img (w.M.take (σ.n + 1)) h ({σ.n + 1} ∪ σ.pr h) ws l (some (σ.n + 1)) ws' pr' ∧
        σ' = { σ with n := σ.n + 1, pr := upd σ.pr h pr' })) := by
  cases hs
  · exact ⟨‹_›, .inl ⟨_, ‹_›, ‹_›, rfl⟩⟩
  · exact ⟨‹_›, .inr ⟨_, ‹_›, ‹_›, ‹_›, rfl, ‹_›, rfl⟩⟩

theorem hstepO_pstep {V P : Type} {w : OW P V} {h : Nat} {σ σ' : OSt V} {s s' : P} {ws ws' : PState} {l : PLabel}
    {ots : Option Nat} (hs : hstepO w h σ s ws l ots s' ws' σ') : w.pstep s () l s' () := (hstepO_cases hs).1

/-- A QUIET LABEL's NF_R step: no fulfil, the quiet post, no change of the language state. -/
theorem hstepO_quiet {V P : Type} {w : OW P V} {h : Nat} {σ σ' : OSt V} {s s' : P} {ws ws' : PState}
    {l : PLabel} {ots : Option Nat} (hq : quietL l = true) (hs : hstepO w h σ s ws l ots s' ws' σ') :
    ots = none ∧ ws' = qPost ws l ∧ σ' = σ := by
  rcases (hstepO_cases hs).2 with ⟨pr', hm, _, rfl⟩ | ⟨_, _, _, hrc, _⟩
  · obtain ⟨h1, h2, h3⟩ := quiet_inv hq hm
    subst h1 h2 h3
    exact ⟨rfl, rfl, upd_pr_same σ h⟩
  · exact absurd hrc (relClassPre_none (wrPre_quiet hq))

/-- A STORE's NF_R step. -/
theorem hstepO_store {V P : Type} {w : OW P V} {h : Nat} {σ σ' : OSt V} {s s' : P} {ws ws' : PState}
    {aq rl : Bool} {base : Int} {data : List (BitVec 8)} {asrc vsrc : List Dsrc} {ots : Option Nat}
    (hs : hstepO w h σ s ws (LStore aq rl base data asrc vsrc) ots s' ws' σ') :
    ∃ ts, ots = some ts ∧ fulO w.M h σ (relClassPre ws (LStore aq rl base data asrc vsrc)) ts σ' ∧
      (w.M.take σ'.n)[ts - 1]? = some ⟨base, data, some h, stClass rl⟩ ∧
      cohBelow ws base data.length ts ∧ stPreA ws aq rl (srcsView ws asrc) (srcsView ws vsrc) < ts ∧
      ws' = acqPost (storeRun ws rl (srcsView ws asrc) (max (srcsView ws asrc) (srcsView ws vsrc)) base
        data.length ts) aq ts := by
  rcases (hstepO_cases hs).2 with ⟨pr', hm, hnr, rfl⟩ | ⟨pr', hn, hau, hrc, rfl, hm, rfl⟩
  · obtain ⟨ts, rfl, hts, hmsg, hcoh, hext, rfl, rfl⟩ := memStep_store_inv hm
    exact ⟨ts, rfl, .inl ⟨hnr, hts, rfl⟩, hmsg, hcoh, hext, rfl⟩
  · obtain ⟨ts, hts, _, hmsg, hcoh, hext, rfl, rfl⟩ := memStep_store_inv hm
    cases hts
    exact ⟨σ.n + 1, rfl, .inr ⟨hrc, hn, hau, rfl, rfl⟩, hmsg, hcoh, hext, rfl⟩

/-- A FUSED AMO's NF_R step. -/
theorem hstepO_rmw {V P : Type} {w : OW P V} {h : Nat} {σ σ' : OSt V} {s s' : P} {ws ws' : PState}
    {aq rl : Bool} {base : Int} {tvs : List (Nat × BitVec 8)} {data : List (BitVec 8)} {asrc vsrc : List Dsrc}
    {ots : Option Nat} (hs : hstepO w h σ s ws (LRmw aq rl base tvs data asrc vsrc) ots s' ws' σ') :
    ∃ ts, ots = some ts ∧ fulO w.M h σ (relClassPre ws (LRmw aq rl base tvs data asrc vsrc)) ts σ' ∧
      rmwOk w.img (w.M.take σ'.n) h ws aq rl base tvs data (srcsView ws asrc) (srcsView ws vsrc) ts ∧
      ws' = amoPost (storeRun (loadRun ws aq false (srcsView ws asrc) base tvs) rl (srcsView ws asrc) ts base
        data.length ts) aq ts := by
  rcases (hstepO_cases hs).2 with ⟨pr', hm, hnr, rfl⟩ | ⟨pr', hn, hau, hrc, rfl, hm, rfl⟩
  · obtain ⟨ts, rfl, hts, hok, rfl, rfl⟩ := memStep_rmw_inv hm
    exact ⟨ts, rfl, .inl ⟨hnr, hts, rfl⟩, hok, rfl⟩
  · obtain ⟨ts, hts, _, hok, rfl, rfl⟩ := memStep_rmw_inv hm
    cases hts
    exact ⟨σ.n + 1, rfl, .inr ⟨hrc, hn, hau, rfl, rfl⟩, hok, rfl⟩

/-- A LOAD's NF_R step (loads are never release-class): against the current prefix, no state change. -/
theorem hstepO_load {V P : Type} {w : OW P V} {h : Nat} {σ σ' : OSt V} {s s' : P} {ws ws' : PState}
    {aq rl : Bool} {base : Int} {tvs : List (Nat × BitVec 8)} {asrc : List Dsrc} {ots : Option Nat}
    (hs : hstepO w h σ s ws (LLoad aq rl base tvs asrc) ots s' ws' σ') :
    loadOk w.img (w.M.take σ.n) ws (ldPre ws aq rl (srcsView ws asrc)) base tvs ∧ ots = none ∧
      ws' = loadRun ws aq rl (srcsView ws asrc) base tvs ∧ σ' = σ := by
  rcases (hstepO_cases hs).2 with ⟨pr', hm, _, rfl⟩ | ⟨_, _, _, hrc, _⟩
  · obtain ⟨hlo, rfl, rfl, rfl⟩ := memStep_load_inv hm
    exact ⟨hlo, rfl, rfl, upd_pr_same σ h⟩
  · exact absurd hrc (relClassPre_none rfl)

/-! ## 2. The kit wp and its rules -/

section kit

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF]
variable {X : OSt (List Nat) → IProp GF} {img : Image} {M : List PMsg} {h : Nat} {Φ : List Nat → IProp GF}

/-- **`wpT X img M h s ws Φ`**: hart `h` of the litmus world at program state `s`, machine state `ws`, any trace. -/
abbrev wpT (X : OSt (List Nat) → IProp GF) (img : Image) (M : List PMsg) (h : Nat) (s : LP) (ws : PState)
    (Φ : List Nat → IProp GF) : IProp GF :=
  iprop(∀ τ, wpO (hlc := hlc) X (.hart (litOW img M) h s ws τ) Φ)

/-- ANY STEP of a hart that is not done. -/
theorem wpT_any {s : LP} {ws : PState} (hd : litDoneR s = none) :
    ▷ (∀ σ l ots s' ws' σ', ⌜hstepO (litOW img M) h σ s ws l ots s' ws' σ'⌝ -∗ X σ -∗ £ 1 -∗
        |={⊤}=> X σ' ∗ wpT (hlc := hlc) X img M h s' ws' Φ) ⊢ wpT X img M h s ws Φ := by
  iintro Hk %τ
  iapply wpO_hart_lift
  inext
  isplit
  · iintro %v %σ %hv
    exfalso
    have : litDoneR s = some v := hv
    rw [hd] at this; cases this
  · iintro %σ %l %ots %s' %ws' %σ' %hs HX Hc
    imod Hk $$ %σ %l %ots %s' %ws' %σ' %hs HX Hc with ⟨HX, Hk⟩
    imodintro
    iframe HX
    iapply Hk

/-- A QUEUE OF QUIET LABELS, drained (no client step). -/
theorem wpT_drain : ∀ (labs : List PLabel) (s : LP) (ws wsf : PState), (∀ l ∈ labs, quietL l = true) → s.q = labs →
    qPosts ws labs = wsf →
    wpT (hlc := hlc) X img M h { s with q := [] } wsf Φ ⊢ wpT X img M h s ws Φ
  | [], s, ws, wsf, _, hs, hf => by
    have e : ({ s with q := [] } : LP) = s := by cases s; simp only at hs; subst hs; rfl
    rw [e, ← hf]; exact .rfl
  | l0 :: r, s, ws, wsf, hql, hs, hf => by
    have ih : wpT (hlc := hlc) X img M h { s with q := [] } wsf Φ ⊢ wpT X img M h { s with q := r } (qPost ws l0) Φ :=
      wpT_drain r { s with q := r } (qPost ws l0) wsf (fun l hl => hql l (List.mem_cons_of_mem _ hl)) rfl hf
    iintro H
    iapply (wpT_any (litDoneR_q (by rw [hs]; simp)))
    inext
    iintro %σ %l %ots %s' %ws' %σ' %hst HX _
    obtain ⟨rfl, rfl⟩ := litNext_q hs (hstepO_pstep hst)
    obtain ⟨_, rfl, rfl⟩ := hstepO_quiet (hql l (List.mem_cons_self ..)) hst
    imodintro
    iframe HX
    iapply ih
    iexact H

/-- AN INSTRUCTION ALL OF WHOSE LABELS ARE QUIET (`fence`, `addi`, `bnez`, …): drained without the client. -/
theorem wpT_quietI {s k : LP} {ws wsf : PState} {l0 : PLabel} {rest : List PLabel} (hd : litDoneR s = none)
    (hl : ∀ l s', litNext s l = some s' → l = l0 ∧ s' = k) (hk : k.q = rest)
    (hq : ∀ l ∈ l0 :: rest, quietL l = true) (hf : qPosts ws (l0 :: rest) = wsf) :
    wpT (hlc := hlc) X img M h { k with q := [] } wsf Φ ⊢ wpT X img M h s ws Φ := by
  have hd' : wpT (hlc := hlc) X img M h { k with q := [] } wsf Φ ⊢ wpT X img M h k (qPost ws l0) Φ :=
    wpT_drain rest k (qPost ws l0) wsf (fun l hl => hq l (List.mem_cons_of_mem _ hl)) hk hf
  iintro H
  iapply (wpT_any hd)
  inext
  iintro %σ %l %ots %s' %ws' %σ' %hst HX _
  obtain ⟨rfl, rfl⟩ := hl l s' (hstepO_pstep hst)
  obtain ⟨_, rfl, rfl⟩ := hstepO_quiet (hq l (List.mem_cons_self ..)) hst
  imodintro
  iframe HX
  iapply hd'
  iexact H

/-- **LOAD instruction** `l{b,h,w,d} rd, off(rs1)` against the current prefix. -/
theorem wpT_ld {s : LP} {sz rd rs1 off : Nat} {sgn : Bool} {ws : PState} (hq : s.q = [])
    (hp : s.prog[s.pc]? = some (.load sz sgn rd rs1 off)) (ha : aligned ((s.rd rs1 + off) % two64) sz = true) :
    ▷ (∀ σ tvs, ⌜tvs.length = sz⌝ -∗
        ⌜loadOk img (M.take σ.n) ws (ldPre ws false false (srcsView ws (srcR rs1)))
          (((s.rd rs1 + off) % two64 : Nat) : Int) tvs⌝ -∗ X σ -∗ £ 1 -∗
        |={⊤}=> X σ ∗ ∀ s', ⌜LPstep s s' (s.pc + 1) rd (ldVal sgn sz tvs)⌝ -∗
          wpT (hlc := hlc) X img M h s' (qPosts (loadRun ws false false (srcsView ws (srcR rs1))
            (((s.rd rs1 + off) % two64 : Nat) : Int) tvs) (regWL rd [.DLdRes] ++ [LInstr])) Φ)
    ⊢ wpT X img M h s ws Φ := by
  iintro Hk
  iapply (wpT_any (litDoneR_pc (pc_lt hp)))
  inext
  iintro %σ %l %ots %s' %ws' %σ' %hst HX Hc
  obtain ⟨tvs, rfl, rfl, hlen⟩ := litNext_load hq hp ha (hstepO_pstep hst)
  obtain ⟨hlo, rfl, rfl, e⟩ := hstepO_load hst
  subst σ'
  imod Hk $$ %σ %tvs %hlen %hlo HX Hc with ⟨HX, Hk⟩
  imodintro
  iframe HX
  iapply (wpT_drain (regWL rd [.DLdRes] ++ [LInstr]) _ _ _ (quiet_regWL rd _ (by simp [quietL])) rfl rfl)
  iapply Hk
  ipureintro
  exact LPstep_wr s rd _ _

/-- **STORE instruction** `s{b,h,w,d} rs2, off(rs1)`: the fulfil fact, against the prefix after the step. -/
theorem wpT_sd {s : LP} {sz rs2 rs1 off : Nat} {ws : PState} (hq : s.q = [])
    (hp : s.prog[s.pc]? = some (.store sz rs2 rs1 off)) (ha : aligned ((s.rd rs1 + off) % two64) sz = true) :
    ▷ (∀ σ ts σ', ⌜fulO M h σ (relClassPre ws (LStore false false (((s.rd rs1 + off) % two64 : Nat) : Int)
          (toBytes (s.rd rs2) sz) (srcR rs1) (srcR rs2))) ts σ'⌝ -∗
        ⌜(M.take σ'.n)[ts - 1]? = some ⟨(((s.rd rs1 + off) % two64 : Nat) : Int), toBytes (s.rd rs2) sz, some h, .plain⟩⌝ -∗
        ⌜cohBelow ws (((s.rd rs1 + off) % two64 : Nat) : Int) (toBytes (s.rd rs2) sz).length ts⌝ -∗
        ⌜stPreA ws false false (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2)) < ts⌝ -∗ X σ -∗ £ 1 -∗
        |={⊤}=> X σ' ∗ ∀ s', ⌜LPstep s s' (s.pc + 1) 0 0⌝ -∗
          wpT (hlc := hlc) X img M h s' (instrR (storeRun ws false (srcsView ws (srcR rs1))
            (max (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2))) (((s.rd rs1 + off) % two64 : Nat) : Int)
            (toBytes (s.rd rs2) sz).length ts)) Φ)
    ⊢ wpT X img M h s ws Φ := by
  iintro Hk
  iapply (wpT_any (litDoneR_pc (pc_lt hp)))
  inext
  iintro %σ %l %ots %s' %ws' %σ' %hst HX Hc
  obtain ⟨rfl, rfl⟩ := litNext_store hq hp ha (hstepO_pstep hst)
  obtain ⟨ts, rfl, hful, hmsg, hcoh, hext, rfl⟩ := hstepO_store hst
  imod Hk $$ %σ %ts %σ' %hful %hmsg %hcoh %hext HX Hc with ⟨HX, Hk⟩
  imodintro
  iframe HX
  rw [PF.acqPost_false]
  iapply (wpT_drain [LInstr] _ _ _ (by simp [quietL]) rfl rfl)
  simp only [qPosts, qPost]
  iapply Hk
  ipureintro
  exact LPstep_same s _

/-- **FUSED AMO instruction** `amo<op>.{w,d}[.aq][.rl] rd, rs2, (rs1)`: the fulfil fact and the AMO's admissibility
`rmwOk`, against the prefix after the step. -/
theorem wpT_amo {s : LP} {op : Weak.Prom.Ref.AmoOp} {sz : Nat} {aq rl : Bool} {rd rs2 rs1 : Nat} {ws : PState}
    (hq : s.q = []) (hp : s.prog[s.pc]? = some (.amo op sz aq rl rd rs2 rs1)) (ha : aligned (s.rd rs1) sz = true) :
    ▷ (∀ σ tvs ts σ', ⌜tvs.length = sz⌝ -∗
        ⌜fulO M h σ (relClassPre ws (LRmw aq rl ((s.rd rs1 : Nat) : Int) tvs (amoD op sz (s.rd rs2) tvs) (srcR rs1)
          (srcR rs2))) ts σ'⌝ -∗
        ⌜rmwOk img (M.take σ'.n) h ws aq rl ((s.rd rs1 : Nat) : Int) tvs (amoD op sz (s.rd rs2) tvs)
          (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2)) ts⌝ -∗ X σ -∗ £ 1 -∗
        |={⊤}=> X σ' ∗ ∀ s', ⌜LPstep s s' (s.pc + 1) rd (sext sz (ofBytes (tvs.map Prod.snd)))⌝ -∗
          wpT (hlc := hlc) X img M h s' (qPosts (amoPost (storeRun (loadRun ws aq false (srcsView ws (srcR rs1))
            ((s.rd rs1 : Nat) : Int) tvs) rl (srcsView ws (srcR rs1)) ts ((s.rd rs1 : Nat) : Int)
            (amoD op sz (s.rd rs2) tvs).length ts) aq ts) (regWL rd [.DLdRes] ++ [LInstr])) Φ)
    ⊢ wpT X img M h s ws Φ := by
  iintro Hk
  iapply (wpT_any (litDoneR_pc (pc_lt hp)))
  inext
  iintro %σ %l %ots %s' %ws' %σ' %hst HX Hc
  obtain ⟨tvs, rfl, rfl, hlen⟩ := litNext_amo hq hp ha (hstepO_pstep hst)
  obtain ⟨ts, rfl, hful, hok, rfl⟩ := hstepO_rmw hst
  imod Hk $$ %σ %tvs %ts %σ' %hlen %hful %hok HX Hc with ⟨HX, Hk⟩
  imodintro
  iframe HX
  iapply (wpT_drain (regWL rd [.DLdRes] ++ [LInstr]) _ _ _ (quiet_regWL rd _ (by simp [quietL])) rfl rfl)
  iapply Hk
  ipureintro
  exact LPstep_wr s rd _ _

/-- **FENCE instruction**. -/
theorem wpT_fence {s : LP} {f : Weak.Prom.Ref.FenceSet} {ws : PState} (hq : s.q = [])
    (hp : s.prog[s.pc]? = some (.fence f)) :
    (∀ s', ⌜LPstep s s' (s.pc + 1) 0 0⌝ -∗ wpT (hlc := hlc) X img M h s' (instrR (fencePost ws f.pr f.pw f.sr f.sw)) Φ)
    ⊢ wpT X img M h s ws Φ := by
  iintro Hk
  iapply (wpT_quietI (litDoneR_pc (pc_lt hp)) (fun l s' hs => litNext_fence hq hp hs) rfl (by simp [quietL]) rfl)
  simp only [qPosts, qPost]
  iapply Hk
  ipureintro
  exact LPstep_same s _

/-- **ALU-IMMEDIATE instruction** `op rd, rs1, imm` (`addi`, `li`, …), `rd ≠ x0`. -/
theorem wpT_alui {s : LP} {op : Weak.Prom.Ref.Alu} {rd rs1 imm : Nat} {ws : PState} (hq : s.q = [])
    (hp : s.prog[s.pc]? = some (.alui op rd rs1 imm)) (hrd : rd ≠ 0) :
    (∀ s', ⌜LPstep s s' (s.pc + 1) rd (aluOp op (s.rd rs1) imm)⌝ -∗
        wpT (hlc := hlc) X img M h s' (instrR (PF.regWP ws rd (srcR rs1))) Φ)
    ⊢ wpT X img M h s ws Φ := by
  iintro Hk
  iapply (wpT_quietI (litDoneR_pc (pc_lt hp)) (fun l s' hs => litNext_alui hq hp hrd hs) rfl (by simp [quietL]) rfl)
  simp only [qPosts, qPost]
  iapply Hk
  ipureintro
  exact LPstep_wr s rd _ _

/-- **FORWARD BRANCH** `b<c> rs1, rs2, tgt`. -/
theorem wpT_br {s : LP} {c : Weak.Prom.Ref.BrC} {rs1 rs2 tgt : Nat} {ws : PState} (hq : s.q = [])
    (hp : s.prog[s.pc]? = some (.br c rs1 rs2 tgt)) (ht : ¬ (tgt ≤ s.pc ∨ s.prog.length < tgt)) :
    (∀ s', ⌜LPstep s s' (if brEval c (s.rd rs1) (s.rd rs2) then tgt else s.pc + 1) 0 0⌝ -∗
        wpT (hlc := hlc) X img M h s' (instrR (PF.ctrlP ws (srcR rs1 ++ srcR rs2))) Φ)
    ⊢ wpT X img M h s ws Φ := by
  iintro Hk
  iapply (wpT_quietI (litDoneR_pc (pc_lt hp)) (fun l s' hs => litNext_br hq hp ht hs) rfl (by simp [quietL]) rfl)
  simp only [qPosts, qPost]
  iapply Hk
  ipureintro
  exact LPstep_same s _

/-- **THE END** of a litmus hart: it records its register file once its promise set is empty. -/
theorem wpT_end {s : LP} {ws : PState} (hq : s.q = []) (hpc : s.prog.length ≤ s.pc) :
    (∀ σ, ⌜σ.pr h = ∅⌝ -∗ X σ -∗ |={⊤}=> X { σ with done := upd σ.done h (some s.regs) } ∗ Φ s.regs)
    ⊢ wpT (hlc := hlc) X img M h s ws Φ := by
  iintro Hk %τ
  iapply wpO_hart_lift
  inext
  isplit
  · iintro %v %σ %hv %hpr HX
    have : litDoneR s = some v := hv
    rw [litDoneR_end hq hpc] at this; cases this
    iapply Hk $$ %σ %hpr HX
  · iintro %σ %l %ots %s' %ws' %σ' %hs
    exfalso
    have := hstepO_pstep hs
    change litNext s l = some s' at this
    rw [litNext_end hq (List.getElem?_eq_none hpc)] at this; cases this

end kit

end Weak.Prom.Own.Pre
