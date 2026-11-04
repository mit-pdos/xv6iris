/-
Weak/Prom: **track (b)'s kit over the LOOP FRONT END** (stage S4b part 3, tag S4b3; plan rev 7 §4 "Gate G4" (1c):
xv6's exact acquire/release text needs backward branches and `sext.w` = `addiw rd, rs1, 0`).

The program half is track (a)'s loop front end `xStep Xs` (OwnAFront.lean, REUSED read-only: `XI`, `xNext`,
`xOf`, `xNext_q`, `xNext_plain`, `xNext_br`, `xNext_addiw`), so both tracks verify the same text under the same
program half.  The language is OwnLang.lean's (plan §3's release class); `xOW Xs img M` is its world.
* `wpT` and the rules of OwnKit.lean, over `xOW`: at a PLAIN text instruction (`XP`: the hart's `XI` text holds a
  plain instruction at its pc) `xNext` is `litNext` (`xlit`), so every litmus rule transfers with one extra
  premise `hpl : XP Xs s`; queued labels as `litNext` (`xNext_q`); `wpT_brx` (any target), `wpT_addiw`; the end.
* `x_fetchBounded`, `x_invalFree`: every valid run of the loop front end is fetch-bounded (no `LIFetch`) and
  `invalFree` (no `LCmo`), program-agnostically (as OwnLitSide.lean for `litStep`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnLitSide
import Weak.Prom.OwnAFront

namespace Weak.Prom.Own.X

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.OA (XI xOf xNext xStep xNext_q xNext_plain xNext_br xNext_addiw addiwV pc_lt_x base_len xOf_spec)
open Weak.Prom.PF (quietL qPost qPosts LPstep LPstep_wr LPstep_same ldVal instrR quiet_inv quiet_regWL pc_lt amoD
  litNext_fence litNext_amo litDone litDone_q litDone_pc litNext_q litNext_end litNext_load litNext_store
  litNext_alui litNext_br)
open Weak.Prom.Ref (Instr two64 aluOp brEval amoOp sext)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The world, pure facts -/

/-- THE LOOP-FRONT-END WORLD of track (b): `xStep Xs`, `litDoneR`, the image, the final memory. -/
abbrev xOW (Xs : List (List XI)) (img : Image) (M : List PMsg) : OW LP (List Nat) := ⟨xStep Xs, litDoneR, img, M⟩

/-- The hart's text holds a PLAIN instruction (or none) at its pc. -/
def XP (Xs : List (List XI)) (s : LP) : Prop :=
  ∀ x, (xOf Xs s.prog).bind (fun X => X[s.pc]?) = some x → x.plain = true

theorem xp_of {Xs : List (List XI)} {s : LP} {X : List XI} {x : XI} (hX : xOf Xs s.prog = some X)
    (hx : X[s.pc]? = some x) (h : x.plain = true) : XP Xs s := by
  intro y hy; rw [hX] at hy; simp only [Option.bind_some, hx] at hy; cases hy; exact h

theorem xp_end {Xs : List (List XI)} {s : LP} (hpc : s.prog.length ≤ s.pc) : XP Xs s := by
  intro y hy
  cases hX : xOf Xs s.prog with
  | none => rw [hX] at hy; cases hy
  | some X =>
    rw [hX] at hy
    simp only [Option.bind_some] at hy
    have := (List.getElem?_eq_some_iff.1 hy).1
    rw [base_len (xOf_spec hX)] at this
    omega

theorem xlit {Xs : List (List XI)} {s s' : LP} {l : PLabel} (hq : s.q = []) (hpl : XP Xs s)
    (h : xStep Xs s () l s' ()) : litNext s l = some s' := by
  rw [← xNext_plain hq hpl l]; exact h

theorem go1_nf {s s' : LP} {regs' : List Nat} {pc' : Nat} {labs : List PLabel} {l : PLabel}
    (hql : qOk labs.tail) (hnl : ∀ x ∈ labs, nfL x = true) (hg : go1 s regs' pc' labs l = some s') :
    ((∀ b tvs, l ≠ LIFetch b tvs) ∧ (∀ k b len asrc, l ≠ LCmo k b len asrc)) ∧ qOk s'.q := by
  obtain ⟨rest, rfl, rfl⟩ := go1_eq hg
  have key := hnl l (List.mem_cons_self ..)
  exact ⟨⟨fun b tvs e => by subst e; simp [nfL] at key, fun k b len asrc e => by subst e; simp [nfL] at key⟩, hql⟩

theorem qOk_tail' : ∀ {L : List PLabel}, qOk L → qOk L.tail
  | [], h => h
  | _ :: _, h => qOk_tail h

/-- `xNext` emits no fetch and no cache-block operation from a well-formed queue, and keeps the queue
well-formed. -/
theorem xNext_nf {Xs : List (List XI)} {s s' : LP} {l : PLabel} (hq : qOk s.q) (h : xNext Xs s l = some s') :
    ((∀ b tvs, l ≠ LIFetch b tvs) ∧ (∀ k b len asrc, l ≠ LCmo k b len asrc)) ∧ qOk s'.q := by
  cases hq' : s.q with
  | cons l0 rest =>
    rw [xNext_q (by rw [hq']; simp) l] at h
    exact ⟨litNext_nf hq h, litNext_q hq h⟩
  | nil =>
    have hq0 : qOk s.q := by rw [hq']; exact qOk_nil
    unfold xNext at h
    rw [hq'] at h
    simp only at h
    split at h
    · refine go1_nf (qOk_tail' (qOk_regWL1 _ _)) (fun x hx => ?_) h
      unfold regWL at hx; split at hx <;> simp at hx
      · subst hx; rfl
      · rcases hx with rfl | rfl <;> rfl
    · split at h
      · cases h
      · exact go1_nf ⟨fun x hx => by simp at hx; subst hx; rfl, fun x hx => by simp at hx⟩
          (fun x hx => by simp at hx; rcases hx with rfl | rfl <;> rfl) h
    · split at h
      · cases h
      · exact go1_nf (labs := [LInstr]) qOk_nil (fun x hx => by simp at hx; subst hx; rfl) h
    · exact ⟨litNext_nf hq0 h, litNext_q hq0 h⟩

theorem xsolo_nf {Xs : List (List XI)} {img : Image} {M : List PMsg} {h : Nat} :
    ∀ {x y : LP × PState × GSet Nat} {τ : List (PLabel × Option Nat)},
      soloSteps (xStep Xs) img M h x τ y → qOk x.1.q →
      ∀ e ∈ τ, (∀ b tvs, e.1 ≠ LIFetch b tvs) ∧ (∀ k b len asrc, e.1 ≠ LCmo k b len asrc) := by
  intro x y τ hs
  induction hs with
  | refl => intro _ e he; cases he
  | step x l ots p' ws' prom' tr y hp _ _ ih =>
    intro hq e he
    rcases List.mem_cons.1 he with rfl | he
    · exact (xNext_nf hq hp).1
    · exact ih (xNext_nf hq hp).2 e he

theorem xsolo_q {Xs : List (List XI)} {img : Image} {M : List PMsg} {h : Nat} :
    ∀ {x y : LP × PState × GSet Nat} {τ : List (PLabel × Option Nat)},
      soloSteps (xStep Xs) img M h x τ y → qOk x.1.q → qOk y.1.q := by
  intro x y τ hs
  induction hs with
  | refl => exact id
  | step x l ots p' ws' prom' tr y hp _ _ ih => exact fun hq => ih (xNext_nf hq hp).2

/-- **PO-fetch for every program of the loop front end.** -/
theorem x_fetchBounded {Xs : List (List XI)} {img : Image} {ps : List LP} {evs : List PEvt} {cfg : PCfg LP Unit}
    (hv : validRun (xStep Xs) img () ps evs cfg) (hps : ∀ p ∈ ps, p.q = []) :
    fetchBounded (xStep Xs) img ps cfg.pcLog evs := by
  apply fetchBounded_ofImg
  intro hh e he base tvs hl
  rcases Nat.lt_or_ge hh ps.length with hlt | hge
  · obtain ⟨ag, _, P0, _, hs⟩ := validRun_solo hv hh _ (List.getElem?_eq_getElem hlt)
    have hq : qOk ps[hh].q := by rw [hps _ (List.getElem_mem hlt)]; exact qOk_nil
    exact absurd hl ((xsolo_nf hs hq e he).1 base tvs)
  · rw [PF.validRun_traceNone hv (List.getElem?_eq_none hge)] at he
    cases he

/-- **`invalFree` for every program of the loop front end.** -/
theorem x_invalFree {Xs : List (List XI)} {img : Image} {ps : List LP} {evs : List PEvt} {cfg : PCfg LP Unit}
    (hv : validRun (xStep Xs) img () ps evs cfg) (hps : ∀ p ∈ ps, p.q = []) : invalFree cfg.pcLog := by
  intro t a hc
  obtain ⟨m, k, len, hm, hcls, _⟩ := hc
  have hm1 : cfg.pcLog[(t - 1 + 1) - 1]? = some m := by simpa using hm
  have hwf := pmSteps_wf hv.1 (pmInit_wf img () ps)
  obtain ⟨_, i, hti, hil⟩ := hwf.2 m (List.mem_of_getElem? hm)
  rw [PF.validRun_len hv] at hil
  obtain ⟨ag, hag, P0, hP0, hs⟩ := validRun_solo hv i _ (List.getElem?_eq_getElem hil)
  have hin : t - 1 + 1 ∈ P0 := (hP0 _).2 ⟨by omega, m, hm1, hti⟩
  have hout : t - 1 + 1 ∉ ag.paProm := by rw [hv.2 i ag hag]; exact notElemOfEmpty
  obtain ⟨z, tr1, l, p', ws', prom', hpre, hp, hmm⟩ := solo_fulfil hs hin hout
  have hq : qOk ps[i].q := by rw [hps _ (List.getElem_mem hil)]; exact qOk_nil
  have hqz : qOk z.1.q := xsolo_q hpre hq
  obtain ⟨h1, _⟩ := memStep_msg hmm
  have hmsg := h1 _ rfl
  rw [hm1] at hmsg
  have hnc := (xNext_nf hqz hp).1.2
  cases l <;> simp [labelMsg] at hmsg <;> subst hmsg <;> simp [stClass] at hcls
  · split at hcls <;> cases hcls
  · exact hnc _ _ _ _ rfl

/-! ## 2. The kit -/

section kit

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF]
variable {Xs : List (List XI)} {X' : OSt (List Nat) → IProp GF} {img : Image} {M : List PMsg} {h : Nat}
  {Φ : List Nat → IProp GF}

/-- **`wpT Xs X' img M h s ws Φ`** over the loop front end (`Xs` the harts' texts). -/
abbrev wpT (Xs : List (List XI)) (X' : OSt (List Nat) → IProp GF) (img : Image) (M : List PMsg) (h : Nat) (s : LP)
    (ws : PState) (Φ : List Nat → IProp GF) : IProp GF :=
  iprop(∀ τ, wpO (hlc := hlc) X' (.hart (xOW Xs img M) h s ws τ) Φ)

/-- ANY STEP of a hart that is not done. -/
theorem wpT_any {s : LP} {ws : PState} (hd : litDoneR s = none) :
    ▷ (∀ σ l ots s' ws' σ', ⌜hstepO (xOW Xs img M) h σ s ws l ots s' ws' σ'⌝ -∗ X' σ -∗ £ 1 -∗
        |={⊤}=> X' σ' ∗ wpT (hlc := hlc) Xs X' img M h s' ws' Φ) ⊢ wpT Xs X' img M h s ws Φ := by
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
    wpT (hlc := hlc) Xs X' img M h { s with q := [] } wsf Φ ⊢ wpT Xs X' img M h s ws Φ
  | [], s, ws, wsf, _, hs, hf => by
    have e : ({ s with q := [] } : LP) = s := by cases s; simp only at hs; subst hs; rfl
    rw [e, ← hf]; exact .rfl
  | l0 :: r, s, ws, wsf, hql, hs, hf => by
    have ih : wpT (hlc := hlc) Xs X' img M h { s with q := [] } wsf Φ ⊢ wpT Xs X' img M h { s with q := r } (qPost ws l0) Φ :=
      wpT_drain r { s with q := r } (qPost ws l0) wsf (fun l hl => hql l (List.mem_cons_of_mem _ hl)) rfl hf
    iintro H
    iapply (wpT_any (litDoneR_q (by rw [hs]; simp)))
    inext
    iintro %σ %l %ots %s' %ws' %σ' %hst HX _
    obtain ⟨rfl, rfl⟩ := litNext_q hs (by rw [← xNext_q (by rw [hs]; simp) l]; exact hstepO_pstep hst)
    obtain ⟨_, rfl, rfl⟩ := hstepO_quiet (hql l (List.mem_cons_self ..)) hst
    imodintro
    iframe HX
    iapply ih
    iexact H

/-- AN INSTRUCTION ALL OF WHOSE LABELS ARE QUIET (`fence`, `addi`, `bnez`, …): drained without the client. -/
theorem wpT_quietI {s k : LP} {ws wsf : PState} {l0 : PLabel} {rest : List PLabel} (hd : litDoneR s = none)
    (hl : ∀ l s', xNext Xs s l = some s' → l = l0 ∧ s' = k) (hk : k.q = rest)
    (hq : ∀ l ∈ l0 :: rest, quietL l = true) (hf : qPosts ws (l0 :: rest) = wsf) :
    wpT (hlc := hlc) Xs X' img M h { k with q := [] } wsf Φ ⊢ wpT Xs X' img M h s ws Φ := by
  have hd' : wpT (hlc := hlc) Xs X' img M h { k with q := [] } wsf Φ ⊢ wpT Xs X' img M h k (qPost ws l0) Φ :=
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
theorem wpT_ld {s : LP} {sz rd rs1 off : Nat} {sgn : Bool} {ws : PState} (hq : s.q = []) (hpl : XP Xs s)
    (hp : s.prog[s.pc]? = some (.load sz sgn rd rs1 off)) (ha : aligned ((s.rd rs1 + off) % two64) sz = true)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a := by assumption) :   -- [rebase-repair] MachFix-R-b5: `vi = 0`
    ▷ (∀ σ tvs, ⌜tvs.length = sz⌝ -∗
        ⌜loadOk img (M.take σ.n) ws (ldPre ws false false (srcsView ws (srcR rs1)))
          (((s.rd rs1 + off) % two64 : Nat) : Int) tvs⌝ -∗ X' σ -∗ £ 1 -∗
        |={⊤}=> X' σ ∗ ∀ s', ⌜LPstep s s' (s.pc + 1) rd (ldVal sgn sz tvs)⌝ -∗
          wpT (hlc := hlc) Xs X' img M h s' (qPosts (loadRun ws false false (srcsView ws (srcR rs1))
            (((s.rd rs1 + off) % two64 : Nat) : Int) tvs) (regWL rd [.DLdRes] ++ [LInstr])) Φ)
    ⊢ wpT Xs X' img M h s ws Φ := by
  iintro Hk
  iapply (wpT_any (litDoneR_pc (pc_lt hp)))
  inext
  iintro %σ %l %ots %s' %ws' %σ' %hst HX Hc
  obtain ⟨tvs, rfl, rfl, hlen⟩ := litNext_load hq hp ha (xlit hq hpl (hstepO_pstep hst))
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
theorem wpT_sd {s : LP} {sz rs2 rs1 off : Nat} {ws : PState} (hq : s.q = []) (hpl : XP Xs s)
    (hp : s.prog[s.pc]? = some (.store sz rs2 rs1 off)) (ha : aligned ((s.rd rs1 + off) % two64) sz = true) :
    ▷ (∀ σ ts σ', ⌜fulO M h σ (relClass ws (LStore false false (((s.rd rs1 + off) % two64 : Nat) : Int)
          (toBytes (s.rd rs2) sz) (srcR rs1) (srcR rs2))) ts σ'⌝ -∗
        ⌜(M.take σ'.n)[ts - 1]? = some ⟨(((s.rd rs1 + off) % two64 : Nat) : Int), toBytes (s.rd rs2) sz, some h, .plain⟩⌝ -∗
        ⌜cohBelow ws (((s.rd rs1 + off) % two64 : Nat) : Int) (toBytes (s.rd rs2) sz).length ts⌝ -∗
        ⌜stPreA ws false false (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2)) < ts⌝ -∗ X' σ -∗ £ 1 -∗
        |={⊤}=> X' σ' ∗ ∀ s', ⌜LPstep s s' (s.pc + 1) 0 0⌝ -∗
          wpT (hlc := hlc) Xs X' img M h s' (instrR (storeRun ws false (srcsView ws (srcR rs1))
            (max (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2))) (((s.rd rs1 + off) % two64 : Nat) : Int)
            (toBytes (s.rd rs2) sz).length ts)) Φ)
    ⊢ wpT Xs X' img M h s ws Φ := by
  iintro Hk
  iapply (wpT_any (litDoneR_pc (pc_lt hp)))
  inext
  iintro %σ %l %ots %s' %ws' %σ' %hst HX Hc
  obtain ⟨rfl, rfl⟩ := litNext_store hq hp ha (xlit hq hpl (hstepO_pstep hst))
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
    (hq : s.q = []) (hpl : XP Xs s) (hp : s.prog[s.pc]? = some (.amo op sz aq rl rd rs2 rs1))
    (ha : aligned (s.rd rs1) sz = true)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a := by assumption) :   -- [rebase-repair] MachFix-R-b5: `vi = 0`
    ▷ (∀ σ tvs ts σ', ⌜tvs.length = sz⌝ -∗
        ⌜fulO M h σ (relClass ws (LRmw aq rl ((s.rd rs1 : Nat) : Int) tvs (amoD op sz (s.rd rs2) tvs) (srcR rs1)
          (srcR rs2))) ts σ'⌝ -∗
        ⌜rmwOk img (M.take σ'.n) h ws aq rl ((s.rd rs1 : Nat) : Int) tvs (amoD op sz (s.rd rs2) tvs)
          (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2)) ts⌝ -∗ X' σ -∗ £ 1 -∗
        |={⊤}=> X' σ' ∗ ∀ s', ⌜LPstep s s' (s.pc + 1) rd (sext sz (ofBytes (tvs.map Prod.snd)))⌝ -∗
          wpT (hlc := hlc) Xs X' img M h s' (qPosts (amoPost (storeRun (loadRun ws aq false (srcsView ws (srcR rs1))
            ((s.rd rs1 : Nat) : Int) tvs) rl (srcsView ws (srcR rs1)) ts ((s.rd rs1 : Nat) : Int)
            (amoD op sz (s.rd rs2) tvs).length ts) aq ts) (regWL rd [.DLdRes] ++ [LInstr])) Φ)
    ⊢ wpT Xs X' img M h s ws Φ := by
  iintro Hk
  iapply (wpT_any (litDoneR_pc (pc_lt hp)))
  inext
  iintro %σ %l %ots %s' %ws' %σ' %hst HX Hc
  obtain ⟨tvs, rfl, rfl, hlen⟩ := litNext_amo hq hp ha (xlit hq hpl (hstepO_pstep hst))
  obtain ⟨ts, rfl, hful, hok, rfl⟩ := hstepO_rmw hst
  imod Hk $$ %σ %tvs %ts %σ' %hlen %hful %hok HX Hc with ⟨HX, Hk⟩
  imodintro
  iframe HX
  iapply (wpT_drain (regWL rd [.DLdRes] ++ [LInstr]) _ _ _ (quiet_regWL rd _ (by simp [quietL])) rfl rfl)
  iapply Hk
  ipureintro
  exact LPstep_wr s rd _ _

/-- **FENCE instruction**. -/
theorem wpT_fence {s : LP} {f : Weak.Prom.Ref.FenceSet} {ws : PState} (hq : s.q = []) (hpl : XP Xs s)
    (hp : s.prog[s.pc]? = some (.fence f)) :
    (∀ s', ⌜LPstep s s' (s.pc + 1) 0 0⌝ -∗ wpT (hlc := hlc) Xs X' img M h s' (instrR (fencePost ws f.pr f.pw f.sr f.sw)) Φ)
    ⊢ wpT Xs X' img M h s ws Φ := by
  iintro Hk
  iapply (wpT_quietI (litDoneR_pc (pc_lt hp)) (fun l s' hs => litNext_fence hq hp (xlit hq hpl hs)) rfl (by simp [quietL]) rfl)
  simp only [qPosts, qPost]
  iapply Hk
  ipureintro
  exact LPstep_same s _

/-- **ALU-IMMEDIATE instruction** `op rd, rs1, imm` (`addi`, `li`, …), `rd ≠ x0`. -/
theorem wpT_alui {s : LP} {op : Weak.Prom.Ref.Alu} {rd rs1 imm : Nat} {ws : PState} (hq : s.q = []) (hpl : XP Xs s)
    (hp : s.prog[s.pc]? = some (.alui op rd rs1 imm)) (hrd : rd ≠ 0) :
    (∀ s', ⌜LPstep s s' (s.pc + 1) rd (aluOp op (s.rd rs1) imm)⌝ -∗
        wpT (hlc := hlc) Xs X' img M h s' (instrR (PF.regWP ws rd (srcR rs1))) Φ)
    ⊢ wpT Xs X' img M h s ws Φ := by
  iintro Hk
  iapply (wpT_quietI (litDoneR_pc (pc_lt hp)) (fun l s' hs => litNext_alui hq hp hrd (xlit hq hpl hs)) rfl (by simp [quietL]) rfl)
  simp only [qPosts, qPost]
  iapply Hk
  ipureintro
  exact LPstep_wr s rd _ _

/-- **BRANCH, ANY TARGET** `b<c> rs1, rs2, tgt` (the loop front end, OwnAFront.lean `xNext_br`). -/
theorem wpT_brx {s : LP} {XX : List XI} {c : Weak.Prom.Ref.BrC} {rs1 rs2 tgt : Nat} {ws : PState} (hq : s.q = [])
    (hX : xOf Xs s.prog = some XX) (hx : XX[s.pc]? = some (.i (.br c rs1 rs2 tgt))) (ht : tgt ≤ s.prog.length) :
    (∀ s', ⌜LPstep s s' (if brEval c (s.rd rs1) (s.rd rs2) then tgt else s.pc + 1) 0 0⌝ -∗
        wpT (hlc := hlc) Xs X' img M h s' (instrR (PF.ctrlP ws (srcR rs1 ++ srcR rs2))) Φ)
    ⊢ wpT Xs X' img M h s ws Φ := by
  iintro Hk
  iapply (wpT_quietI (litDoneR_pc (pc_lt_x hX hx)) (fun l s' hs => xNext_br hq hX hx ht hs) rfl (by simp [quietL]) rfl)
  simp only [qPosts, qPost]
  iapply Hk
  ipureintro
  exact LPstep_same s _

/-- **`addiw rd, rs1, imm`** (`sext.w rd, rs1` = `addiw rd, rs1, 0`; OwnAFront.lean `xNext_addiw`), `rd ≠ x0`. -/
theorem wpT_addiw {s : LP} {XX : List XI} {rd rs1 imm : Nat} {ws : PState} (hq : s.q = [])
    (hX : xOf Xs s.prog = some XX) (hx : XX[s.pc]? = some (.addiw rd rs1 imm)) (hrd : rd ≠ 0) :
    (∀ s', ⌜LPstep s s' (s.pc + 1) rd (addiwV (s.rd rs1) imm)⌝ -∗
        wpT (hlc := hlc) Xs X' img M h s' (instrR (PF.regWP ws rd (srcR rs1))) Φ)
    ⊢ wpT Xs X' img M h s ws Φ := by
  iintro Hk
  iapply (wpT_quietI (litDoneR_pc (pc_lt_x hX hx)) (fun l s' hs => xNext_addiw hq hX hx hrd hs) rfl
    (by simp [quietL]) rfl)
  simp only [qPosts, qPost]
  iapply Hk
  ipureintro
  exact LPstep_wr s rd _ _

/-- **THE END** of a litmus hart: it records its register file once its promise set is empty. -/
theorem wpT_end {s : LP} {ws : PState} (hq : s.q = []) (hpc : s.prog.length ≤ s.pc) :
    (∀ σ, ⌜σ.pr h = ∅⌝ -∗ X' σ -∗ |={⊤}=> X' { σ with done := upd σ.done h (some s.regs) } ∗ Φ s.regs)
    ⊢ wpT (hlc := hlc) Xs X' img M h s ws Φ := by
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
    change xNext Xs s l = some s' at this
    rw [xNext_plain hq (xp_end hpc), litNext_end hq (List.getElem?_eq_none hpc)] at this; cases this

end kit

end Weak.Prom.Own.X
