/-
Weak/Prom: **track (b)'s litmus kit over `wpO`** (stage S4b part 2; plan rev 7 §4 "Pull rule", §2 "Leaf rules", §7
"Leaf interface").  Removes part 1's fidelity caveat "label-level program half": the G4 targets of track (b) now run
through the REAL litmus program half `litStep` (MachCert.lean §1, the label table of MachLitmus.lean), with the
programs' real access widths and the tests' images.

* `litOW img M` — the prophecy world of a litmus test: program half `litStep`, value of a finished hart = its final
  register file (`litDoneR`: `litDone`, MachCert.lean `allDone`'s per-hart conjunct).
* `wpT X img M h s ws Φ` — `wpO` of hart `h` at program state `s`, machine state `ws`, for every trace.
* `wpT_any` — the hart lifting lemma (OwnWp.lean `wpO_hart_lift`) without the value branch.
* quiet labels (`LRegW`, `LInstr`, `LFence`, `LCtrl`, …; CoreKit.lean `quietL`) are never write steps, so never
  release-class: their NF_R step changes no language state (`hstepO_quiet`), and the kit drains them without the
  client (`wpT_drain`, `wpT_quietI`).
* instruction rules `wpT_ld`, `wpT_sd`, `wpT_amo`, `wpT_fence`, `wpT_alui`, `wpT_br`, `wpT_end`: the client sees the
  memory step of the instruction's one memory label against the CURRENT PREFIX `M.take σ.n` (a load) or the
  prefix after the step (a write), and, for a write, the FULFIL FACT `fulO` (plan §4 NF_R): a non-release-class write
  fulfils its own promise in the prefix; a release-class write appends `M[n]` and fulfils it IN PLACE.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnWp
import Weak.Prom.CoreKitV

namespace Weak.Prom.Own

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Nfr Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.PF (quietL qPost qPosts LPstep LPstep_wr LPstep_same ldVal instrR quiet_inv quiet_regWL pc_lt amoD
  litNext_fence litNext_amo litDone litDone_q litDone_pc litNext_q litNext_end litNext_load litNext_store
  litNext_alui litNext_br)
open Weak.Prom.Ref (Instr two64 aluOp brEval amoOp sext)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The litmus world, pure step facts -/

/-- A finished litmus hart's value: its final register file. -/
def litDoneR (s : LP) : Option (List Nat) := (litDone s).map (fun _ => s.regs)

/-- THE LITMUS WORLD of track (b): `litStep`, `litDoneR`, the image, the final memory. -/
abbrev litOW (img : Image) (M : List PMsg) : OW LP (List Nat) := ⟨litStep, litDoneR, img, M⟩

theorem litDoneR_q {s : LP} (h : s.q ≠ []) : litDoneR s = none := by simp [litDoneR, litDone_q h]
theorem litDoneR_pc {s : LP} (h : s.pc < s.prog.length) : litDoneR s = none := by simp [litDoneR, litDone_pc h]
theorem litDoneR_end {s : LP} (hq : s.q = []) (hpc : s.prog.length ≤ s.pc) : litDoneR s = some s.regs := by
  simp [litDoneR, litDone, hq, hpc]

theorem upd_pr_same {V : Type} (σ : OSt V) (h : Nat) : ({ σ with pr := upd σ.pr h (σ.pr h) } : OSt V) = σ := by
  cases σ; simp only [OSt.mk.injEq, and_true, true_and]; funext j; by_cases e : j = h <;> simp [upd, e]

theorem relClass_none {ws : PState} {l : PLabel} (h : wrPre ws l = none) : ¬ relClass ws l := by
  rintro ⟨pv, hpv, _⟩; rw [h] at hpv; cases hpv

theorem wrPre_quiet {ws : PState} {l : PLabel} (hq : quietL l = true) : wrPre ws l = none := by
  cases l <;> simp_all [quietL, wrPre]

/-- THE TWO CASES of an NF_R hart step (OwnLang.lean `hstepO`) of a NON-FETCH label, as one disjunction.
[E-b] premise `hnf`: the prophecy-fed fetch constructor `hstepO.fetch` only has fetch labels. -/
theorem hstepO_cases {V P : Type} {w : OW P V} {h : Nat} {σ σ' : OSt V} {s s' : P} {ws ws' : PState}
    {l : PLabel} {ots : Option Nat} (hs : hstepO w h σ s ws l ots s' ws' σ')
    (hnf : ∀ b tvs, l ≠ LIFetch b tvs := by intro _ _ e; cases e) :
    w.pstep s () l s' () ∧
    ((∃ pr', memStep w.img (w.M.take σ.n) h (σ.pr h) ws l ots ws' pr' ∧ ¬ relClass ws l ∧
        σ' = { σ with pr := upd σ.pr h pr' }) ∨
     (∃ pr', σ.n < w.M.length ∧ authorAt w.M σ.n = some h ∧ relClass ws l ∧ ots = some (σ.n + 1) ∧
        memStep w.img (w.M.take (σ.n + 1)) h ({σ.n + 1} ∪ σ.pr h) ws l (some (σ.n + 1)) ws' pr' ∧
        σ' = { σ with n := σ.n + 1, pr := upd σ.pr h pr' })) := by
  cases hs
  · exact ⟨‹_›, .inl ⟨_, ‹_›, ‹_›, rfl⟩⟩
  · exact ⟨‹_›, .inr ⟨_, ‹_›, ‹_›, ‹_›, rfl, ‹_›, rfl⟩⟩
  · exact (hnf _ _ rfl).elim   -- [E-b]

theorem hstepO_pstep {V P : Type} {w : OW P V} {h : Nat} {σ σ' : OSt V} {s s' : P} {ws ws' : PState} {l : PLabel}
    {ots : Option Nat} (hs : hstepO w h σ s ws l ots s' ws' σ') : w.pstep s () l s' () := by
  cases hs <;> assumption   -- [E-b] (was `(hstepO_cases hs).1`)

/-- A QUIET LABEL's NF_R step: no fulfil, the quiet post, no change of the language state. -/
theorem hstepO_quiet {V P : Type} {w : OW P V} {h : Nat} {σ σ' : OSt V} {s s' : P} {ws ws' : PState}
    {l : PLabel} {ots : Option Nat} (hq : quietL l = true) (hs : hstepO w h σ s ws l ots s' ws' σ') :
    ots = none ∧ ws' = qPost ws l ∧ σ' = σ := by
  -- [E-b] fetch labels are not quiet
  rcases (hstepO_cases hs (fun _ _ e => by subst e; simp [quietL] at hq)).2 with ⟨pr', hm, _, rfl⟩ | ⟨_, _, _, hrc, _⟩
  · obtain ⟨h1, h2, h3⟩ := quiet_inv hq hm
    subst h1 h2 h3
    exact ⟨rfl, rfl, upd_pr_same σ h⟩
  · exact absurd hrc (relClass_none (wrPre_quiet hq))

theorem memStep_load_inv {img : Image} {log : List PMsg} {i : Nat} {pr pr' : GSet Nat} {ws ws' : PState}
    {aq rl : Bool} {base : Int} {tvs : List (Nat × BitVec 8)} {asrc : List Dsrc} {ots : Option Nat}
    (hm : memStep img log i pr ws (LLoad aq rl base tvs asrc) ots ws' pr')
    (hnoinv : ∀ t a, ¬ cmoAt log isInvalK t a := by assumption) :   -- MachFix-R-b5: `vi = 0`
    loadOk img log ws (ldPre ws aq rl (srcsView ws asrc)) base tvs ∧ ots = none ∧
      ws' = loadRun ws aq rl (srcsView ws asrc) base tvs ∧ pr' = pr := by
  cases hm with
  | load _ _ _ _ _ hlo vi hci =>
    obtain rfl := invalCite_vi0 hnoinv hci
    exact ⟨hlo, rfl, loadRunV_zero .., rfl⟩

theorem memStep_store_inv {img : Image} {log : List PMsg} {i : Nat} {pr pr' : GSet Nat} {ws ws' : PState}
    {aq rl : Bool} {base : Int} {data : List (BitVec 8)} {asrc vsrc : List Dsrc} {ots : Option Nat}
    (hm : memStep img log i pr ws (LStore aq rl base data asrc vsrc) ots ws' pr') :
    ∃ ts, ots = some ts ∧ ts ∈ pr ∧ log[ts - 1]? = some ⟨base, data, some i, stClass rl⟩ ∧
      cohBelow ws base data.length ts ∧ stPreA ws aq rl (srcsView ws asrc) (srcsView ws vsrc) < ts ∧
      ws' = acqPost (storeRun ws rl (srcsView ws asrc) (max (srcsView ws asrc) (srcsView ws vsrc)) base
        data.length ts) aq ts ∧ pr' = pr \ {ts} := by
  cases hm with
  | store _ _ _ _ _ _ ts hts hmsg hcoh hext => exact ⟨ts, rfl, hts, hmsg, hcoh, hext, rfl, rfl⟩

/-- The admissibility facts of a fused AMO step (Machine.lean `memStep.rmw`) against log `L`. -/
def rmwOk (img : Image) (L : List PMsg) (h : Nat) (ws : PState) (aq rl : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (data : List (BitVec 8)) (va vd ts : Nat) : Prop :=
  tvs.length = data.length ∧ L[ts - 1]? = some ⟨base, data, some h, .excl⟩ ∧
    loadOk img L ws (ldPre ws aq false va) base tvs ∧ exclOk L h base (tvs.map Prod.fst) ts ∧
    cohBelow (loadRun ws aq false va base tvs) base data.length ts ∧
    stPre (loadRun ws aq false va base tvs) rl va vd < ts

theorem memStep_rmw_inv {img : Image} {log : List PMsg} {i : Nat} {pr pr' : GSet Nat} {ws ws' : PState}
    {aq rl : Bool} {base : Int} {tvs : List (Nat × BitVec 8)} {data : List (BitVec 8)} {asrc vsrc : List Dsrc}
    {ots : Option Nat} (hm : memStep img log i pr ws (LRmw aq rl base tvs data asrc vsrc) ots ws' pr')
    (hnoinv : ∀ t a, ¬ cmoAt log isInvalK t a := by assumption) :   -- MachFix-R-b5: `vi = 0`
    ∃ ts, ots = some ts ∧ ts ∈ pr ∧ rmwOk img log i ws aq rl base tvs data (srcsView ws asrc) (srcsView ws vsrc) ts ∧
      ws' = amoPost (storeRun (loadRun ws aq false (srcsView ws asrc) base tvs) rl (srcsView ws asrc) ts base
        data.length ts) aq ts ∧ pr' = pr \ {ts} := by
  cases hm with
  | rmw _ _ _ _ _ _ _ ts hlen hts hmsg hlo hex hcoh hext vi hci _ =>
    obtain rfl := invalCite_vi0 hnoinv hci
    exact ⟨ts, rfl, hts, ⟨hlen, hmsg, hlo, hex, hcoh, hext⟩, by rw [loadRunV_zero], rfl⟩

/-- THE FULFIL FACT of a write step of hart `h` (plan §4 NF_R): a non-release-class write (`¬ rc`) fulfils its own
promise `ts` of the prefix; a release-class write appends `M[n]` (authored by `h`) and fulfils it IN PLACE. -/
def fulO {V : Type} (M : List PMsg) (h : Nat) (σ : OSt V) (rc : Prop) (ts : Nat) (σ' : OSt V) : Prop :=
  (¬ rc ∧ ts ∈ σ.pr h ∧ σ' = { σ with pr := upd σ.pr h (σ.pr h \ {ts}) }) ∨
  (rc ∧ σ.n < M.length ∧ authorAt M σ.n = some h ∧ ts = σ.n + 1 ∧
    σ' = { σ with n := σ.n + 1, pr := upd σ.pr h (({σ.n + 1} ∪ σ.pr h) \ {σ.n + 1}) })

/-- A STORE's NF_R step. -/
theorem hstepO_store {V P : Type} {w : OW P V} {h : Nat} {σ σ' : OSt V} {s s' : P} {ws ws' : PState}
    {aq rl : Bool} {base : Int} {data : List (BitVec 8)} {asrc vsrc : List Dsrc} {ots : Option Nat}
    (hs : hstepO w h σ s ws (LStore aq rl base data asrc vsrc) ots s' ws' σ') :
    ∃ ts, ots = some ts ∧ fulO w.M h σ (relClass ws (LStore aq rl base data asrc vsrc)) ts σ' ∧
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
    {ots : Option Nat} (hs : hstepO w h σ s ws (LRmw aq rl base tvs data asrc vsrc) ots s' ws' σ')
    (hnoinv : ∀ t a, ¬ cmoAt w.M isInvalK t a := by assumption) :   -- MachFix-R-b5: `vi = 0`
    ∃ ts, ots = some ts ∧ fulO w.M h σ (relClass ws (LRmw aq rl base tvs data asrc vsrc)) ts σ' ∧
      rmwOk w.img (w.M.take σ'.n) h ws aq rl base tvs data (srcsView ws asrc) (srcsView ws vsrc) ts ∧
      ws' = amoPost (storeRun (loadRun ws aq false (srcsView ws asrc) base tvs) rl (srcsView ws asrc) ts base
        data.length ts) aq ts := by
  have hn1 := noInval_take hnoinv σ.n
  have hn2 := noInval_take hnoinv (σ.n + 1)
  rcases (hstepO_cases hs).2 with ⟨pr', hm, hnr, rfl⟩ | ⟨pr', hn, hau, hrc, rfl, hm, rfl⟩
  · obtain ⟨ts, rfl, hts, hok, rfl, rfl⟩ := memStep_rmw_inv hm
    exact ⟨ts, rfl, .inl ⟨hnr, hts, rfl⟩, hok, rfl⟩
  · obtain ⟨ts, hts, _, hok, rfl, rfl⟩ := memStep_rmw_inv hm
    cases hts
    exact ⟨σ.n + 1, rfl, .inr ⟨hrc, hn, hau, rfl, rfl⟩, hok, rfl⟩

/-- A LOAD's NF_R step (loads are never release-class): against the current prefix, no state change. -/
theorem hstepO_load {V P : Type} {w : OW P V} {h : Nat} {σ σ' : OSt V} {s s' : P} {ws ws' : PState}
    {aq rl : Bool} {base : Int} {tvs : List (Nat × BitVec 8)} {asrc : List Dsrc} {ots : Option Nat}
    (hs : hstepO w h σ s ws (LLoad aq rl base tvs asrc) ots s' ws' σ')
    (hnoinv : ∀ t a, ¬ cmoAt w.M isInvalK t a := by assumption) :   -- MachFix-R-b5: `vi = 0`
    loadOk w.img (w.M.take σ.n) ws (ldPre ws aq rl (srcsView ws asrc)) base tvs ∧ ots = none ∧
      ws' = loadRun ws aq rl (srcsView ws asrc) base tvs ∧ σ' = σ := by
  have hn1 := noInval_take hnoinv σ.n
  rcases (hstepO_cases hs).2 with ⟨pr', hm, _, rfl⟩ | ⟨_, _, _, hrc, _⟩
  · obtain ⟨hlo, rfl, rfl, rfl⟩ := memStep_load_inv hm
    exact ⟨hlo, rfl, rfl, upd_pr_same σ h⟩
  · exact absurd hrc (relClass_none rfl)

/-- The message of a fulfil, read from the step's log. -/
theorem take_msg {M : List PMsg} {n ts : Nat} {m : PMsg} (h : (M.take n)[ts - 1]? = some m) :
    M[ts - 1]? = some m ∧ ts - 1 < n := by
  rw [List.getElem?_take] at h
  split at h
  · exact ⟨h, by omega⟩
  · cases h

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
    (hp : s.prog[s.pc]? = some (.load sz sgn rd rs1 off)) (ha : aligned ((s.rd rs1 + off) % two64) sz = true)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a := by assumption) :   -- MachFix-R-b5: `vi = 0`
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
    ▷ (∀ σ ts σ', ⌜fulO M h σ (relClass ws (LStore false false (((s.rd rs1 + off) % two64 : Nat) : Int)
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
    (hq : s.q = []) (hp : s.prog[s.pc]? = some (.amo op sz aq rl rd rs2 rs1)) (ha : aligned (s.rd rs1) sz = true)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a := by assumption) :   -- MachFix-R-b5: `vi = 0`
    ▷ (∀ σ tvs ts σ', ⌜tvs.length = sz⌝ -∗
        ⌜fulO M h σ (relClass ws (LRmw aq rl ((s.rd rs1 : Nat) : Int) tvs (amoD op sz (s.rd rs2) tvs) (srcR rs1)
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

end Weak.Prom.Own
