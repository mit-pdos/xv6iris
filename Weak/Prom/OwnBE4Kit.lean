/-
Weak/Prom: **E-b4, B-0 — track (b)'s loop-front-end kit over the trace-carrying language** (stage E-b4; owner ruling
[OWN.P16]; G4-review3.md §5 B-0).

RE-TYPINGS of OwnKitX.lean's rules (and OwnKit.lean's `wpT_any`/`wpT_end`) onto OwnBE4Adeq.lean's `wpB` (each tagged
`-- [retype <Old.name>]`).  The world is OwnKitX's `xOW Xs img M` (REUSED); the pure step facts (`hstepO_store`,
`hstepO_rmw`, `hstepO_load`, `hstepO_quiet`, `fulO`, `rmwOk`) are OwnKit.lean's, REUSED verbatim.  The only change:
the client's state interpretation sees the hart's memory-event trace grow — a load appends
`(LLoad …, none)`, a store `(LStore …, some ts)`, an AMO `(LRmw …, some ts)`; quiet labels record nothing
(`memEv` drops them), so the kit still drains them without the client.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnBE4Adeq
import Weak.Prom.OwnKitX

namespace Weak.Prom.OB.E4

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Own (OSt OW hstepO upd upd_eq upd_ne fulO rmwOk hstepO_pstep hstepO_quiet hstepO_load hstepO_store
  hstepO_rmw litDoneR)
open Weak.Prom.Own.X (xOW XP xlit)
open Weak.Prom.OA (XI xOf xNext xStep xNext_q xNext_plain xNext_br xNext_addiw addiwV pc_lt_x)
open Weak.Prom.PF (quietL qPost qPosts LPstep LPstep_wr LPstep_same ldVal instrR quiet_inv quiet_regWL pc_lt amoD
  litNext_fence litNext_amo litNext_q litNext_end litNext_load litNext_store litNext_alui litNext_br memEv keepE
  Trace PEv)
open Weak.Prom.Ref (Instr two64 aluOp brEval amoOp sext)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-- A quiet step records nothing. -/
theorem recE_quiet {τ : Trace} {l : PLabel} (hq : quietL l = true) : recE τ (l, none) = τ := by
  simp [recE, keepE, hq]

/-- A kept entry is appended. -/
theorem recE_keep {τ : Trace} {e : PEv} (hk : keepE e = true) : recE τ e = τ ++ [e] := by
  simp [recE, hk]

theorem tst_same {V : Type} (σ : TSt V) (h : Nat) : (⟨σ.o, upd σ.tr h (σ.tr h)⟩ : TSt V) = σ := by
  cases σ; simp only [TSt.mk.injEq, true_and]; funext j; by_cases e : j = h <;> simp [upd, e]

/-- The state after a kept entry `e` of hart `h`, OwnLang state `o'`. -/
abbrev nxT {V : Type} (σ : TSt V) (h : Nat) (o' : OSt V) (e : PEv) : TSt V := ⟨o', upd σ.tr h (σ.tr h ++ [e])⟩

section kit

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF]
variable {Xs : List (List XI)} {X' : TSt (List Nat) → IProp GF} {img : Image} {M : List PMsg} {h : Nat}

/-- **`wpX Xs X' img M h s ws`**: hart `h` of the loop-front-end world at program state `s`, machine state `ws`. -/
abbrev wpX (Xs : List (List XI)) (X' : TSt (List Nat) → IProp GF) (img : Image) (M : List PMsg) (h : Nat) (s : LP)   -- [retype Own.X.wpT]
    (ws : PState) : IProp GF :=
  wpB (hlc := hlc) X' (.hart (xOW Xs img M) h s ws)

/-- ANY STEP. -/
theorem wpX_any {s : LP} {ws : PState} :   -- [retype Own.X.wpT_any]
    ▷ (∀ σ l ots s' ws' o', ⌜hstepO (xOW Xs img M) h σ.o s ws l ots s' ws' o'⌝ -∗ X' σ -∗ £ 1 -∗
        |={⊤}=> X' ⟨o', upd σ.tr h (recE (σ.tr h) (l, ots))⟩ ∗ wpX (hlc := hlc) Xs X' img M h s' ws')
    ⊢ wpX Xs X' img M h s ws := wpB_hart_lift

/-- A QUEUE OF QUIET LABELS, drained (no client step). -/
theorem wpX_drain : ∀ (labs : List PLabel) (s : LP) (ws wsf : PState), (∀ l ∈ labs, quietL l = true) → s.q = labs →   -- [retype Own.X.wpT_drain]
    qPosts ws labs = wsf →
    wpX (hlc := hlc) Xs X' img M h { s with q := [] } wsf ⊢ wpX Xs X' img M h s ws
  | [], s, ws, wsf, _, hs, hf => by
    have e : ({ s with q := [] } : LP) = s := by cases s; simp only at hs; subst hs; rfl
    rw [e, ← hf]; exact .rfl
  | l0 :: r, s, ws, wsf, hql, hs, hf => by
    have ih : wpX (hlc := hlc) Xs X' img M h { s with q := [] } wsf ⊢ wpX Xs X' img M h { s with q := r } (qPost ws l0) :=
      wpX_drain r { s with q := r } (qPost ws l0) wsf (fun l hl => hql l (List.mem_cons_of_mem _ hl)) rfl hf
    iintro H
    iapply wpX_any
    inext
    iintro %σ %l %ots %s' %ws' %o' %hst HX _
    obtain ⟨rfl, rfl⟩ := litNext_q hs (by rw [← xNext_q (by rw [hs]; simp) l]; exact hstepO_pstep hst)
    obtain ⟨rfl, rfl, rfl⟩ := hstepO_quiet (hql l (List.mem_cons_self ..)) hst
    rw [recE_quiet (hql l (List.mem_cons_self ..)), tst_same]
    imodintro
    iframe HX
    iapply ih
    iexact H

/-- AN INSTRUCTION ALL OF WHOSE LABELS ARE QUIET, drained without the client. -/
theorem wpX_quietI {s k : LP} {ws wsf : PState} {l0 : PLabel} {rest : List PLabel}   -- [retype Own.X.wpT_quietI]
    (hl : ∀ l s', xNext Xs s l = some s' → l = l0 ∧ s' = k) (hk : k.q = rest)
    (hq : ∀ l ∈ l0 :: rest, quietL l = true) (hf : qPosts ws (l0 :: rest) = wsf) :
    wpX (hlc := hlc) Xs X' img M h { k with q := [] } wsf ⊢ wpX Xs X' img M h s ws := by
  have hd' : wpX (hlc := hlc) Xs X' img M h { k with q := [] } wsf ⊢ wpX Xs X' img M h k (qPost ws l0) :=
    wpX_drain rest k (qPost ws l0) wsf (fun l hl => hq l (List.mem_cons_of_mem _ hl)) hk hf
  iintro H
  iapply wpX_any
  inext
  iintro %σ %l %ots %s' %ws' %o' %hst HX _
  obtain ⟨rfl, rfl⟩ := hl l s' (hstepO_pstep hst)
  obtain ⟨rfl, rfl, rfl⟩ := hstepO_quiet (hq l (List.mem_cons_self ..)) hst
  rw [recE_quiet (hq l (List.mem_cons_self ..)), tst_same]
  imodintro
  iframe HX
  iapply hd'
  iexact H

/-- **LOAD instruction** against the current prefix; the load is recorded. -/
theorem wpX_ld {s : LP} {sz rd rs1 off : Nat} {sgn : Bool} {ws : PState} (hq : s.q = []) (hpl : XP Xs s)   -- [retype Own.X.wpT_ld]
    (hp : s.prog[s.pc]? = some (.load sz sgn rd rs1 off)) (ha : aligned ((s.rd rs1 + off) % two64) sz = true)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a := by assumption) :
    ▷ (∀ σ tvs, ⌜tvs.length = sz⌝ -∗
        ⌜loadOk img (M.take σ.o.n) ws (ldPre ws false false (srcsView ws (srcR rs1)))
          (((s.rd rs1 + off) % two64 : Nat) : Int) tvs⌝ -∗ X' σ -∗ £ 1 -∗
        |={⊤}=> X' (nxT σ h σ.o (LLoad false false (((s.rd rs1 + off) % two64 : Nat) : Int) tvs (srcR rs1), none)) ∗
          ∀ s', ⌜LPstep s s' (s.pc + 1) rd (ldVal sgn sz tvs)⌝ -∗
          wpX (hlc := hlc) Xs X' img M h s' (qPosts (loadRun ws false false (srcsView ws (srcR rs1))
            (((s.rd rs1 + off) % two64 : Nat) : Int) tvs) (regWL rd [.DLdRes] ++ [LInstr])))
    ⊢ wpX Xs X' img M h s ws := by
  iintro Hk
  iapply wpX_any
  inext
  iintro %σ %l %ots %s' %ws' %o' %hst HX Hc
  obtain ⟨tvs, rfl, rfl, hlen⟩ := litNext_load hq hp ha (xlit hq hpl (hstepO_pstep hst))
  obtain ⟨hlo, rfl, rfl, e⟩ := hstepO_load hst
  subst o'
  rw [recE_keep (by simp [keepE, quietL])]
  imod Hk $$ %σ %tvs %hlen %hlo HX Hc with ⟨HX, Hk⟩
  imodintro
  iframe HX
  iapply (wpX_drain (regWL rd [.DLdRes] ++ [LInstr]) _ _ _ (quiet_regWL rd _ (by simp [quietL])) rfl rfl)
  iapply Hk
  ipureintro
  exact LPstep_wr s rd _ _

/-- **STORE instruction**: the fulfil fact, against the prefix after the step; the store is recorded. -/
theorem wpX_sd {s : LP} {sz rs2 rs1 off : Nat} {ws : PState} (hq : s.q = []) (hpl : XP Xs s)   -- [retype Own.X.wpT_sd]
    (hp : s.prog[s.pc]? = some (.store sz rs2 rs1 off)) (ha : aligned ((s.rd rs1 + off) % two64) sz = true) :
    ▷ (∀ σ ts o', ⌜fulO M h σ.o (relClass ws (LStore false false (((s.rd rs1 + off) % two64 : Nat) : Int)
          (toBytes (s.rd rs2) sz) (srcR rs1) (srcR rs2))) ts o'⌝ -∗
        ⌜(M.take o'.n)[ts - 1]? = some ⟨(((s.rd rs1 + off) % two64 : Nat) : Int), toBytes (s.rd rs2) sz, some h, .plain⟩⌝ -∗
        ⌜cohBelow ws (((s.rd rs1 + off) % two64 : Nat) : Int) (toBytes (s.rd rs2) sz).length ts⌝ -∗
        ⌜stPreA ws false false (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2)) < ts⌝ -∗ X' σ -∗ £ 1 -∗
        |={⊤}=> X' (nxT σ h o' (LStore false false (((s.rd rs1 + off) % two64 : Nat) : Int) (toBytes (s.rd rs2) sz)
            (srcR rs1) (srcR rs2), some ts)) ∗ ∀ s', ⌜LPstep s s' (s.pc + 1) 0 0⌝ -∗
          wpX (hlc := hlc) Xs X' img M h s' (instrR (storeRun ws false (srcsView ws (srcR rs1))
            (max (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2))) (((s.rd rs1 + off) % two64 : Nat) : Int)
            (toBytes (s.rd rs2) sz).length ts)))
    ⊢ wpX Xs X' img M h s ws := by
  iintro Hk
  iapply wpX_any
  inext
  iintro %σ %l %ots %s' %ws' %o' %hst HX Hc
  obtain ⟨rfl, rfl⟩ := litNext_store hq hp ha (xlit hq hpl (hstepO_pstep hst))
  obtain ⟨ts, rfl, hful, hmsg, hcoh, hext, rfl⟩ := hstepO_store hst
  rw [recE_keep (by simp [keepE])]
  imod Hk $$ %σ %ts %o' %hful %hmsg %hcoh %hext HX Hc with ⟨HX, Hk⟩
  imodintro
  iframe HX
  rw [PF.acqPost_false]
  iapply (wpX_drain [LInstr] _ _ _ (by simp [quietL]) rfl rfl)
  simp only [qPosts, qPost]
  iapply Hk
  ipureintro
  exact LPstep_same s _

/-- **FUSED AMO instruction**: the fulfil fact and `rmwOk`; the AMO is recorded. -/
theorem wpX_amo {s : LP} {op : Weak.Prom.Ref.AmoOp} {sz : Nat} {aq rl : Bool} {rd rs2 rs1 : Nat} {ws : PState}   -- [retype Own.X.wpT_amo]
    (hq : s.q = []) (hpl : XP Xs s) (hp : s.prog[s.pc]? = some (.amo op sz aq rl rd rs2 rs1))
    (ha : aligned (s.rd rs1) sz = true)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a := by assumption) :
    ▷ (∀ σ tvs ts o', ⌜tvs.length = sz⌝ -∗
        ⌜fulO M h σ.o (relClass ws (LRmw aq rl ((s.rd rs1 : Nat) : Int) tvs (amoD op sz (s.rd rs2) tvs) (srcR rs1)
          (srcR rs2))) ts o'⌝ -∗
        ⌜rmwOk img (M.take o'.n) h ws aq rl ((s.rd rs1 : Nat) : Int) tvs (amoD op sz (s.rd rs2) tvs)
          (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2)) ts⌝ -∗ X' σ -∗ £ 1 -∗
        |={⊤}=> X' (nxT σ h o' (LRmw aq rl ((s.rd rs1 : Nat) : Int) tvs (amoD op sz (s.rd rs2) tvs) (srcR rs1)
            (srcR rs2), some ts)) ∗ ∀ s', ⌜LPstep s s' (s.pc + 1) rd (sext sz (ofBytes (tvs.map Prod.snd)))⌝ -∗
          wpX (hlc := hlc) Xs X' img M h s' (qPosts (amoPost (storeRun (loadRun ws aq false (srcsView ws (srcR rs1))
            ((s.rd rs1 : Nat) : Int) tvs) rl (srcsView ws (srcR rs1)) ts ((s.rd rs1 : Nat) : Int)
            (amoD op sz (s.rd rs2) tvs).length ts) aq ts) (regWL rd [.DLdRes] ++ [LInstr])))
    ⊢ wpX Xs X' img M h s ws := by
  iintro Hk
  iapply wpX_any
  inext
  iintro %σ %l %ots %s' %ws' %o' %hst HX Hc
  obtain ⟨tvs, rfl, rfl, hlen⟩ := litNext_amo hq hp ha (xlit hq hpl (hstepO_pstep hst))
  obtain ⟨ts, rfl, hful, hok, rfl⟩ := hstepO_rmw hst
  rw [recE_keep (by simp [keepE])]
  imod Hk $$ %σ %tvs %ts %o' %hlen %hful %hok HX Hc with ⟨HX, Hk⟩
  imodintro
  iframe HX
  iapply (wpX_drain (regWL rd [.DLdRes] ++ [LInstr]) _ _ _ (quiet_regWL rd _ (by simp [quietL])) rfl rfl)
  iapply Hk
  ipureintro
  exact LPstep_wr s rd _ _

/-- **FENCE instruction**. -/
theorem wpX_fence {s : LP} {f : Weak.Prom.Ref.FenceSet} {ws : PState} (hq : s.q = []) (hpl : XP Xs s)   -- [retype Own.X.wpT_fence]
    (hp : s.prog[s.pc]? = some (.fence f)) :
    (∀ s', ⌜LPstep s s' (s.pc + 1) 0 0⌝ -∗ wpX (hlc := hlc) Xs X' img M h s' (instrR (fencePost ws f.pr f.pw f.sr f.sw)))
    ⊢ wpX Xs X' img M h s ws := by
  iintro Hk
  iapply (wpX_quietI (fun l s' hs => litNext_fence hq hp (xlit hq hpl hs)) rfl (by simp [quietL]) rfl)
  simp only [qPosts, qPost]
  iapply Hk
  ipureintro
  exact LPstep_same s _

/-- **ALU-IMMEDIATE instruction**, `rd ≠ x0`. -/
theorem wpX_alui {s : LP} {op : Weak.Prom.Ref.Alu} {rd rs1 imm : Nat} {ws : PState} (hq : s.q = []) (hpl : XP Xs s)   -- [retype Own.X.wpT_alui]
    (hp : s.prog[s.pc]? = some (.alui op rd rs1 imm)) (hrd : rd ≠ 0) :
    (∀ s', ⌜LPstep s s' (s.pc + 1) rd (aluOp op (s.rd rs1) imm)⌝ -∗
        wpX (hlc := hlc) Xs X' img M h s' (instrR (PF.regWP ws rd (srcR rs1))))
    ⊢ wpX Xs X' img M h s ws := by
  iintro Hk
  iapply (wpX_quietI (fun l s' hs => litNext_alui hq hp hrd (xlit hq hpl hs)) rfl (by simp [quietL]) rfl)
  simp only [qPosts, qPost]
  iapply Hk
  ipureintro
  exact LPstep_wr s rd _ _

/-- **BRANCH, ANY TARGET**. -/
theorem wpX_brx {s : LP} {XX : List XI} {c : Weak.Prom.Ref.BrC} {rs1 rs2 tgt : Nat} {ws : PState} (hq : s.q = [])   -- [retype Own.X.wpT_brx]
    (hX : xOf Xs s.prog = some XX) (hx : XX[s.pc]? = some (.i (.br c rs1 rs2 tgt))) (ht : tgt ≤ s.prog.length) :
    (∀ s', ⌜LPstep s s' (if brEval c (s.rd rs1) (s.rd rs2) then tgt else s.pc + 1) 0 0⌝ -∗
        wpX (hlc := hlc) Xs X' img M h s' (instrR (PF.ctrlP ws (srcR rs1 ++ srcR rs2))))
    ⊢ wpX Xs X' img M h s ws := by
  iintro Hk
  iapply (wpX_quietI (fun l s' hs => xNext_br hq hX hx ht hs) rfl (by simp [quietL]) rfl)
  simp only [qPosts, qPost]
  iapply Hk
  ipureintro
  exact LPstep_same s _

/-- **`addiw rd, rs1, imm`**, `rd ≠ x0`. -/
theorem wpX_addiw {s : LP} {XX : List XI} {rd rs1 imm : Nat} {ws : PState} (hq : s.q = [])   -- [retype Own.X.wpT_addiw]
    (hX : xOf Xs s.prog = some XX) (hx : XX[s.pc]? = some (.addiw rd rs1 imm)) (hrd : rd ≠ 0) :
    (∀ s', ⌜LPstep s s' (s.pc + 1) rd (addiwV (s.rd rs1) imm)⌝ -∗
        wpX (hlc := hlc) Xs X' img M h s' (instrR (PF.regWP ws rd (srcR rs1))))
    ⊢ wpX Xs X' img M h s ws := by
  iintro Hk
  iapply (wpX_quietI (fun l s' hs => xNext_addiw hq hX hx hrd hs) rfl (by simp [quietL]) rfl)
  simp only [qPosts, qPost]
  iapply Hk
  ipureintro
  exact LPstep_wr s rd _ _

/-- **THE END** of a hart: no step is possible, nothing to prove. -/
theorem wpX_end {s : LP} {ws : PState} (hq : s.q = []) (hpc : s.prog.length ≤ s.pc) :   -- [retype Own.X.wpT_end]
    ⊢ wpX (hlc := hlc) Xs X' img M h s ws := by
  iapply wpX_any
  inext
  iintro %σ %l %ots %s' %ws' %o' %hs
  exfalso
  have := hstepO_pstep hs
  change xNext Xs s l = some s' at this
  rw [xNext_plain hq (Own.X.xp_end hpc), litNext_end hq (List.getElem?_eq_none hpc)] at this; cases this

/-- A fancy update before a step. -/
theorem wpX_fupd {s : LP} {ws : PState} :
    (|={⊤}=> wpX (hlc := hlc) Xs X' img M h s ws) ⊢ wpX Xs X' img M h s ws := wpB_fupd

end kit

end Weak.Prom.OB.E4
