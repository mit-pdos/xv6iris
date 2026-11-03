/-
Weak/Prom: **the litmus kit of the ownership-free core** (stage S2; plan rev 7 §2 "Leaf rules", "wp shape",
§8 S2 "`lit_<test>` for every FORBIDDEN row").

This file adds NO rule to the logic: every lemma here is a composition of the leaf rules of `CoreRules.lean`
(`wpH_any`, `wpH_load`, `wpH_store`, `wpH_sc`, `wpH_done`, all proved from the one lifting lemma `wpH_lift`), packaged
at the granularity of ONE LITMUS INSTRUCTION of the label-level front end `litStep` (MachCert.lean §1), so that the
per-hart proofs of the §5 rows stay short.  Plan §2: "Each rule is an iProp lemma over the exact ws"; the
instruction rules below hand the client the exact post-state of every label the instruction emits (`qPost`), and the
client states the view facts it needs ((X4)–(X6) and the fence / acquire / release / coherence facts of
`CoreView.lean`) about it.

* `memEv τ` — the MEMORY ENTRIES of a trace: every entry except the answer-free, timestamp-free bookkeeping labels
  (`LRegW`, `LInstr`, `LFence`, `LCtrl`, `LExFail`, `LFenceI`; `quietL`).  A hart's trace invariant is stated over
  them: `ΨK M Q τ := Q (memEv τ) ∧ wrOk M τ` (plan §2 "Ψ : List PEv → Prop is a trace invariant").  `wrOk` records
  that every fulfilled message is not a cache-block operation (the class the FULFIL arm checks), which is what
  rules out the invalidate clause `invalRead` of the load-value axiom in the litmus contradictions (`noCmo`).
* `lh γ π w Q ws P ev` — `hartSt γ ws P τ` for some trace `τ` with `memEv τ = ev`, `wrOk M τ` and the guarded
  invariant `⟦V⟧⌜Q ev⌝` (plan §2 [R2.6]); quiet steps re-use it, memory steps prove it of `ev ++ [e]`.
* One-label rules (`wpK_q1`, `wpK_drain`, `wpK_load1`, `wpK_store1`, `wpK_rmw1`, `wpK_lr1`, `wpK_sc1`) and
  instruction rules (`wpK_ld`, `wpK_sw`, `wpK_alu`, `wpK_alui`, `wpK_fence`, `wpK_br`, `wpK_amo`, `wpK_lr`,
  `wpK_sc`, `wpK_end`) for a world whose program half agrees with `litNext` (`LitAg`, `LitW`); the client's view of
  the program state after an instruction is the abstract `LPstep` (program, pc, empty queue, registers).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreLit6

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. Memory entries, `wrOk`, `ΨK` -/

/-- The answer-free, timestamp-free bookkeeping labels (no memory access, no fulfil). -/
def quietL : PLabel → Bool
  | LRegW _ _ => true
  | LInstr => true
  | LFence _ _ _ _ => true
  | LCtrl _ => true
  | LExFail => true
  | LFenceI => true
  | _ => false

/-- An entry kept by `memEv`: it carries a timestamp, or its label is not quiet. -/
def keepE (e : PEv) : Bool := e.2.isSome || !quietL e.1

/-- THE MEMORY ENTRIES of a trace. -/
def memEv (τ : Trace) : Trace := τ.filter keepE

theorem memEv_quiet (τ : Trace) (l : PLabel) (hq : quietL l = true) : memEv (τ ++ [(l, none)]) = memEv τ := by
  simp [memEv, List.filter_append, keepE, hq]

theorem memEv_snoc (τ : Trace) (e : PEv) (hk : keepE e = true) : memEv (τ ++ [e]) = memEv τ ++ [e] := by
  simp [memEv, List.filter_append, hk]

theorem memEv_of_ts {τ : Trace} {e : PEv} {t : Nat} (he : e ∈ τ) (ht : e.2 = some t) : e ∈ memEv τ := by
  unfold memEv; rw [List.mem_filter]; exact ⟨he, by simp [keepE, ht]⟩

theorem mem_of_memEv {τ : Trace} {e : PEv} (he : e ∈ memEv τ) : e ∈ τ := (List.mem_filter.1 he).1

theorem loadLike_quiet {l : PLabel} (hq : quietL l = true) : loadLikeTvs l = none := by
  cases l <;> simp_all [quietL, loadLikeTvs]

theorem loadsOf_memEv (τ : Trace) : loadsOf (memEv τ) = loadsOf τ := by
  induction τ with
  | nil => rfl
  | cons e r ih =>
    unfold memEv loadsOf at *
    rw [List.filter_cons]
    split
    · rw [List.filterMap_cons, List.filterMap_cons, ih]
    · next hk =>
      rw [List.filterMap_cons, ih]
      have hq : quietL e.1 = true := by simp [keepE] at hk; exact hk.2
      rw [loadLike_quiet hq]

/-- Not a cache-block-operation class. -/
def notCmo : PClass → Bool
  | .cmo _ _ => false
  | _ => true

/-- Every fulfilled message of the trace is not a cache-block operation. -/
def wrOk (M : List PMsg) (τ : Trace) : Prop :=
  ∀ e ∈ τ, ∀ t, e.2 = some t → ∀ m, msgAt M t = some m → notCmo m.cls = true

theorem wrOk_nil (M : List PMsg) : wrOk M [] := fun _ h => by cases h

theorem wrOk_snoc_none {M : List PMsg} {τ : Trace} {l : PLabel} (h : wrOk M τ) : wrOk M (τ ++ [(l, none)]) := by
  intro e he t ht
  rcases mem_snoc he with he | rfl
  · exact h e he t ht
  · cases ht

theorem wrOk_snoc_some {M : List PMsg} {τ : Trace} {l : PLabel} {ts : Nat} {m0 : PMsg} (h : wrOk M τ)
    (hm : M[ts - 1]? = some m0) (h1 : 1 ≤ ts) (hc : notCmo m0.cls = true) : wrOk M (τ ++ [(l, some ts)]) := by
  intro e he t ht m hmt
  rcases mem_snoc he with he | rfl
  · exact h e he t ht m hmt
  · cases ht
    obtain ⟨k, rfl⟩ : ∃ k, ts = k + 1 := ⟨ts - 1, by omega⟩
    simp only [msgAt] at hmt
    simp only [Nat.add_sub_cancel] at hm
    rw [hm] at hmt; cases hmt; exact hc

/-- No message of `M` is a cache-block operation. -/
def noCmo (M : List PMsg) : Prop := ∀ (k : Nat) (m : PMsg), M[k]? = some m → notCmo m.cls = true

/-- Without cache-block operations the invalidate clause of the load-value axiom never applies. -/
theorem noInval {M : List PMsg} (hnc : noCmo M) {a : Int} {t fl : Nat} : ¬ invalRead M a t fl := by
  rintro ⟨ti, ⟨m, k, len, hm, hcls, _⟩, _⟩
  have := hnc (ti - 1) m hm
  rw [hcls] at this; cases this

/-- THE KIT TRACE INVARIANT: `Q` of the memory entries, and `wrOk`. -/
def ΨK (M : List PMsg) (Q : Trace → Prop) (τ : Trace) : Prop := Q (memEv τ) ∧ wrOk M τ

/-! ## 2. The quiet labels' posts -/

/-- `LRegW rd srcs`'s post (an assignment of the sources' view, (X5)). -/
def regWP (ws : PState) (rd : Nat) (srcs : List Dsrc) : PState :=
  { ws with wRegv := insert ws.wRegv rd (srcsView ws srcs) }

/-- `LInstr`'s post (resets `wLdv`, the AMO slot and the fetch view). -/
def instrR (ws : PState) : PState := { ws with wLdv := 0, wRmw := none, wIfv := 0 }

/-- `LCtrl srcs`'s post (rule 11). -/
def ctrlP (ws : PState) (srcs : List Dsrc) : PState := { ws with wVcap := max (srcsView ws srcs) ws.wVcap }

/-- The post of a quiet label. -/
def qPost (ws : PState) : PLabel → PState
  | LRegW rd srcs => regWP ws rd srcs
  | LInstr => instrR ws
  | LFence pr pw sr sw => fencePost ws pr pw sr sw
  | LCtrl srcs => ctrlP ws srcs
  | LExFail => { ws with wRes := none }
  | LFenceI => fenceIPost ws
  | _ => ws

/-- The post of a sequence of quiet labels. -/
def qPosts : PState → List PLabel → PState
  | ws, [] => ws
  | ws, l :: r => qPosts (qPost ws l) r

/-- A quiet label's memory step is its post, with no fulfil. -/
theorem quiet_inv {img : Image} {log : List PMsg} {i : Nat} {pr : GSet Nat} {ws : PState} {l : PLabel}
    {ots : Option Nat} {ws' : PState} {pr' : GSet Nat} (hq : quietL l = true)
    (hm : memStep img log i pr ws l ots ws' pr') : ots = none ∧ ws' = qPost ws l ∧ pr' = pr := by
  cases hm <;> simp_all [quietL, qPost, regWP, instrR, ctrlP]

/-! ## 3. Litmus worlds and program states -/

section worlds

variable {V : Type}

/-- The world's program half agrees with `litNext` at `s`. -/
def LitAg (w : HW LP Unit V) (s : LP) : Prop := ∀ l s', anyFab w.pstep s () l s' () ↔ litNext s l = some s'

/-- A litmus world: the program half agrees with `litNext` wherever a label is queued, and no state with a queued
label or a remaining instruction is a value. -/
def LitW (w : HW LP Unit V) : Prop :=
  (∀ s, s.q ≠ [] → LitAg w s) ∧ (∀ s, (s.q ≠ [] ∨ s.pc < s.prog.length) → w.pdone s = none)

theorem litAg_lit (pdone : LP → Option V) (img : Image) (M : List PMsg) (h : Nat) (s : LP) :
    LitAg (⟨litStep, pdone, img, M, h⟩ : HW LP Unit V) s := fun _ _ => anyFab_lit

theorem litW_lit (img : Image) (M : List PMsg) (h : Nat) :
    LitW (⟨litStep, litDone, img, M, h⟩ : HW LP Unit Unit) := by
  refine ⟨fun s _ => litAg_lit _ _ _ _ s, fun s hs => ?_⟩
  rcases hs with hs | hs
  · exact litDone_q hs
  · exact litDone_pc hs

end worlds

/-- The value a load writes to `rd`. -/
def ldVal (sgn : Bool) (sz : Nat) (tvs : List (Nat × BitVec 8)) : Nat :=
  if sgn then sext sz (ofBytes (tvs.map Prod.snd)) else ofBytes (tvs.map Prod.snd)

/-- THE CLIENT'S VIEW OF THE NEXT PROGRAM STATE: same program, pc `pc`, nothing queued, and register `rd` written
with `v` (no write when `rd = 0`). -/
def LPstep (s s' : LP) (pc rd v : Nat) : Prop :=
  s'.prog = s.prog ∧ s'.pc = pc ∧ s'.q = [] ∧ s'.regs.length = s.regs.length ∧
    ∀ r, s'.rd r = if r = rd ∧ rd ≠ 0 ∧ rd < s.regs.length then v % two64 else s.rd r

theorem lp_wr_len (s : LP) (rd v : Nat) : (s.wr rd v).length = s.regs.length := by
  unfold LP.wr; split <;> simp

theorem lp_rd_wr_gen (s : LP) (rd v r : Nat) :
    ({ s with regs := s.wr rd v } : LP).rd r = if r = rd ∧ rd ≠ 0 ∧ rd < s.regs.length then v % two64 else s.rd r := by
  by_cases h : r = rd ∧ rd ≠ 0 ∧ rd < s.regs.length
  · obtain ⟨rfl, h0, hl⟩ := h
    rw [if_pos ⟨rfl, h0, hl⟩]; exact lp_rd_wr_self h0 hl
  · rw [if_neg h]
    by_cases hr : r = rd
    · subst hr
      by_cases h0 : r = 0
      · unfold LP.rd LP.wr; simp [h0]
      · have hl : ¬ r < s.regs.length := fun hl => h ⟨rfl, h0, hl⟩
        unfold LP.rd LP.wr
        simp [h0, List.getElem?_set, hl]
    · exact lp_rd_wr hr

theorem LPstep_wr (s : LP) (rd v pc : Nat) : LPstep s { s with regs := s.wr rd v, pc := pc, q := [] } pc rd v :=
  ⟨rfl, rfl, rfl, lp_wr_len s rd v, fun r => lp_rd_wr_gen s rd v r⟩

theorem LPstep_same (s : LP) (pc : Nat) : LPstep s { s with pc := pc, q := [] } pc 0 0 :=
  ⟨rfl, rfl, rfl, rfl, fun r => by rw [if_neg (by simp)]; rfl⟩

/-! ## 4. The rules -/

section rules

variable {V : Type}
variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [InvGS_gen hlc GF]

/-- `lh γ π w Q ws P ev`: the hart's exact state and promise set, some trace whose memory entries are `ev`, with
`wrOk` and the guarded invariant `⟦V⟧⌜Q ev⌝`. -/
abbrev lh (γ : GName) (π : Proto) (w : HW LP Unit V) (Q : Trace → Prop) (ws : PState) (pr : GSet Nat) (ev : Trace) :
    IProp GF :=
  iprop(∃ τ, hartSt γ ws pr τ ∗ ⌜memEv τ = ev ∧ wrOk w.M τ ∧ ∃ V, grd π w.img w.M V (Q ev)⌝)

/-- The kit wp: `wpH` with the trace invariant `ΨK`. -/
abbrev wpK (γ : GName) (π : Proto) (w : HW LP Unit V) (Q : Trace → Prop) (s : LP) (Φ : V → IProp GF) : IProp GF :=
  wpH γ π w (ΨK w.M Q) s Φ

variable {γ : GName} {π : Proto} {w : HW LP Unit V} {Q : Trace → Prop} {Φ : V → IProp GF}

/-- From `wpPF` to the kit resource. -/
theorem wpK_start {s0 : LP} (hQ0 : Q []) :
    (∀ γ P0, lh γ π w Q psInit P0 [] -∗ wpK γ π w Q s0 Φ) ⊢ wpPF π w (ΨK w.M Q) s0 Φ := by
  iintro Hk
  unfold wpPF
  iintro %γ' %P0 %_ Hst
  iapply Hk $$ %γ' %P0
  unfold lh
  iexists []
  iframe Hst
  ipureintro
  exact ⟨rfl, wrOk_nil _, 0, grd_intro hQ0⟩

/-- ONE QUIET LABEL. -/
theorem wpK_q1 {s k : LP} {ws ws1 : PState} {pr : GSet Nat} {ev : Trace} {l0 : PLabel} (hq : quietL l0 = true)
    (hd : w.pdone s = none) (hl : ∀ l s', anyFab w.pstep s () l s' () → l = l0 ∧ s' = k)
    (hpost : qPost ws l0 = ws1) :
    lh γ π w Q ws pr ev ∗ ▷ (lh γ π w Q ws1 pr ev -∗ wpK γ π w Q k Φ) ⊢ wpK γ π w Q s Φ := by
  subst hpost
  iintro ⟨⟨%τ, Hst, %hinv⟩, Hk⟩
  iapply wpH_any hd
  iframe Hst
  inext
  iintro %l %ots %s' %ws' %pr' %hp %hm Hc
  obtain ⟨hl0, hk0⟩ := hl l s' hp
  subst hl0 hk0
  obtain ⟨rfl, rfl, rfl⟩ := quiet_inv hq hm
  obtain ⟨he, hw, V', hg⟩ := hinv
  imodintro
  isplitr
  · ipureintro
    refine ⟨⟨V', fun hv => ⟨by rw [memEv_quiet _ _ hq, he]; exact hg hv, wrOk_snoc_none hw⟩⟩, fun t ht => by cases ht⟩
  · iintro Hst
    iapply Hk
    unfold lh
    iexists τ ++ [(l, none)]
    iframe Hst
    ipureintro
    exact ⟨by rw [memEv_quiet _ _ hq, he], wrOk_snoc_none hw, V', hg⟩

/-- A QUEUE OF QUIET LABELS, drained. -/
theorem wpK_drain (hw : LitW w) {pr : GSet Nat} {ev : Trace} :
    ∀ (labs : List PLabel) (l0 : PLabel) (s k : LP) (ws wsf : PState), (∀ l ∈ l0 :: labs, quietL l = true) →
      s.q = l0 :: labs → k = { s with q := [] } → qPosts ws (l0 :: labs) = wsf →
      lh γ π w Q ws pr ev ∗ ▷ (lh γ π w Q wsf pr ev -∗ wpK γ π w Q k Φ) ⊢ wpK γ π w Q s Φ := by
  intro labs
  induction labs with
  | nil =>
    intro l0 s k ws wsf hql hs hk hf
    subst hk
    iintro ⟨Hl, Hk⟩
    iapply (wpK_q1 (k := { s with q := [] }) (ws1 := wsf) (hql l0 (List.mem_cons_self ..))
      (hw.2 s (.inl (by rw [hs]; simp)))
      (fun l s' hp => litNext_q hs (((hw.1 s (by rw [hs]; simp)) l s').1 hp)) hf)
    iframe Hl
    iexact Hk
  | cons l1 r ih =>
    intro l0 s k ws wsf hql hs hk hf
    iintro ⟨Hl, Hk⟩
    iapply (wpK_q1 (k := { s with q := l1 :: r }) (ws1 := qPost ws l0) (hql l0 (List.mem_cons_self ..))
      (hw.2 s (.inl (by rw [hs]; simp)))
      (fun l s' hp => litNext_q hs (((hw.1 s (by rw [hs]; simp)) l s').1 hp)) rfl)
    iframe Hl
    inext
    iintro Hl
    iapply (ih l1 { s with q := l1 :: r } k (qPost ws l0) wsf (fun l hl => hql l (List.mem_cons_of_mem _ hl)) rfl
      (by rw [hk]) hf)
    iframe Hl
    inext
    iexact Hk

/-- ONE LOAD LABEL. -/
theorem wpK_load1 {s : LP} {ws : PState} {pr : GSet Nat} {ev : Trace} {aq rl : Bool} {base : Int}
    {asrc : List Dsrc} {k : List (Nat × BitVec 8) → LP} {C : List (Nat × BitVec 8) → Prop} (hd : w.pdone s = none)
    (hl : ∀ l s', anyFab w.pstep s () l s' () → ∃ tvs, l = LLoad aq rl base tvs asrc ∧ s' = k tvs ∧ C tvs) :
    lh γ π w Q ws pr ev ∗
    ▷ (∀ tvs, ⌜C tvs⌝ -∗ ⌜loadOk w.img w.M ws (ldPre ws aq rl (srcsView ws asrc)) base tvs⌝ -∗
        |={⊤}=> ⌜∃ V, grd π w.img w.M V (Q (ev ++ [(LLoad aq rl base tvs asrc, none)]))⌝ ∗
          (lh γ π w Q (loadRun ws aq rl (srcsView ws asrc) base tvs) pr (ev ++ [(LLoad aq rl base tvs asrc, none)]) -∗
            wpK γ π w Q (k tvs) Φ))
    ⊢ wpK γ π w Q s Φ := by
  iintro ⟨⟨%τ, Hst, %hinv⟩, Hk⟩
  obtain ⟨he, hw, _⟩ := hinv
  iapply (wpH_load (Ψ := ΨK w.M Q) hd hl)
  iframe Hst
  inext
  iintro %tvs %hC %hlo _
  imod Hk $$ %tvs %hC %hlo with ⟨%hQ, Hk⟩
  obtain ⟨V', hg⟩ := hQ
  imodintro
  isplitr
  · ipureintro
    exact ⟨V', fun hv => ⟨by rw [memEv_snoc _ _ rfl, he]; exact hg hv, wrOk_snoc_none hw⟩⟩
  · iintro Hst
    iapply Hk
    unfold lh
    iexists τ ++ [(LLoad aq rl base tvs asrc, none)]
    iframe Hst
    ipureintro
    exact ⟨by rw [memEv_snoc _ _ rfl, he], wrOk_snoc_none hw, V', hg⟩

/-- ONE STORE LABEL (FULFIL). -/
theorem wpK_store1 {s k : LP} {ws : PState} {pr : GSet Nat} {ev : Trace} {aq rl : Bool} {base : Int}
    {data : List (BitVec 8)} {asrc vsrc : List Dsrc} (hd : w.pdone s = none)
    (hl : ∀ l s', anyFab w.pstep s () l s' () → l = LStore aq rl base data asrc vsrc ∧ s' = k) :
    lh γ π w Q ws pr ev ∗
    ▷ (∀ ts, ⌜ts ∈ pr⌝ -∗ ⌜w.M[ts - 1]? = some ⟨base, data, some w.h, stClass rl⟩⌝ -∗
        ⌜cohBelow ws base data.length ts⌝ -∗
        ⌜stPreA ws aq rl (srcsView ws asrc) (srcsView ws vsrc) < ts⌝ -∗
        |={⊤}=> ⌜∃ V, grd π w.img w.M V (Q (ev ++ [(LStore aq rl base data asrc vsrc, some ts)]))⌝ ∗
          ⌜grd π w.img w.M (stPreA ws aq rl (srcsView ws asrc) (srcsView ws vsrc))
            (π.okMsg ⟨base, data, some w.h, stClass rl⟩)⌝ ∗
          (lh γ π w Q (acqPost (storeRun ws rl (srcsView ws asrc) (max (srcsView ws asrc) (srcsView ws vsrc)) base
              data.length ts) aq ts) (pr \ {ts}) (ev ++ [(LStore aq rl base data asrc vsrc, some ts)]) -∗
            wpK γ π w Q k Φ))
    ⊢ wpK γ π w Q s Φ := by
  iintro ⟨⟨%τ, Hst, %hinv⟩, Hk⟩
  obtain ⟨he, hw, _⟩ := hinv
  iapply (wpH_store (Ψ := ΨK w.M Q) hd hl)
  iframe Hst
  inext
  iintro %ts %hts %hmsg %hcoh %hext _
  imod Hk $$ %ts %hts %hmsg %hcoh %hext with ⟨%hQ, %hp, Hk⟩
  obtain ⟨V', hg⟩ := hQ
  have hw' : wrOk w.M (τ ++ [(LStore aq rl base data asrc vsrc, some ts)]) :=
    wrOk_snoc_some hw hmsg (by omega) (by cases rl <;> rfl)
  imodintro
  isplitr
  · ipureintro
    exact ⟨V', fun hv => ⟨by rw [memEv_snoc _ _ rfl, he]; exact hg hv, hw'⟩⟩
  isplitr
  · ipureintro; exact hp
  · iintro Hst
    iapply Hk
    unfold lh
    iexists τ ++ [(LStore aq rl base data asrc vsrc, some ts)]
    iframe Hst
    ipureintro
    exact ⟨by rw [memEv_snoc _ _ rfl, he], hw', V', hg⟩

/-- ONE FUSED AMO LABEL (M0). -/
theorem wpK_rmw1 {s : LP} {ws : PState} {pr : GSet Nat} {ev : Trace} {aq rl : Bool} {base : Int}
    {asrc vsrc : List Dsrc} {dat : List (Nat × BitVec 8) → List (BitVec 8)} {k : List (Nat × BitVec 8) → LP}
    {C : List (Nat × BitVec 8) → Prop} (hd : w.pdone s = none)
    (hl : ∀ l s', anyFab w.pstep s () l s' () → ∃ tvs, l = LRmw aq rl base tvs (dat tvs) asrc vsrc ∧ s' = k tvs ∧
      C tvs) :
    lh γ π w Q ws pr ev ∗
    ▷ (∀ tvs ts, ⌜C tvs⌝ -∗ ⌜tvs.length = (dat tvs).length⌝ -∗ ⌜ts ∈ pr⌝ -∗
        ⌜w.M[ts - 1]? = some ⟨base, dat tvs, some w.h, .excl⟩⌝ -∗
        ⌜loadOk w.img w.M ws (ldPre ws aq false (srcsView ws asrc)) base tvs⌝ -∗
        ⌜exclOk w.M w.h base (tvs.map Prod.fst) ts⌝ -∗
        ⌜cohBelow (loadRun ws aq false (srcsView ws asrc) base tvs) base (dat tvs).length ts⌝ -∗
        ⌜stPre (loadRun ws aq false (srcsView ws asrc) base tvs) rl (srcsView ws asrc) (srcsView ws vsrc) < ts⌝ -∗
        |={⊤}=> ⌜∃ V, grd π w.img w.M V (Q (ev ++ [(LRmw aq rl base tvs (dat tvs) asrc vsrc, some ts)]))⌝ ∗
          ⌜grd π w.img w.M (stPre (loadRun ws aq false (srcsView ws asrc) base tvs) rl (srcsView ws asrc)
            (srcsView ws vsrc)) (π.okMsg ⟨base, dat tvs, some w.h, .excl⟩)⌝ ∗
          (lh γ π w Q (amoPost (storeRun (loadRun ws aq false (srcsView ws asrc) base tvs) rl (srcsView ws asrc) ts base
              (dat tvs).length ts) aq ts) (pr \ {ts})
              (ev ++ [(LRmw aq rl base tvs (dat tvs) asrc vsrc, some ts)]) -∗
            wpK γ π w Q (k tvs) Φ))
    ⊢ wpK γ π w Q s Φ := by
  iintro ⟨⟨%τ, Hst, %hinv⟩, Hk⟩
  obtain ⟨he, hw, _⟩ := hinv
  iapply wpH_any hd
  iframe Hst
  inext
  iintro %l %ots %s' %ws' %pr' %hp %hm Hc
  obtain ⟨tvs, rfl, rfl, hC⟩ := hl l s' hp
  cases hm with
  | rmw _ _ _ _ _ _ _ ts hlen hts hmsg hlo hex hcoh hext =>
    imod Hk $$ %tvs %ts %hC %hlen %hts %hmsg %hlo %hex %hcoh %hext with ⟨%hQ, %hpv, Hk⟩
    obtain ⟨V', hg⟩ := hQ
    have hw' : wrOk w.M (τ ++ [(LRmw aq rl base tvs (dat tvs) asrc vsrc, some ts)]) :=
      wrOk_snoc_some hw hmsg (by omega) rfl
    imodintro
    isplitr
    · ipureintro
      refine ⟨⟨V', fun hv => ⟨by rw [memEv_snoc _ _ rfl, he]; exact hg hv, hw'⟩⟩, fun t ht m hm => ?_⟩
      cases ht
      obtain ⟨k', rfl⟩ : ∃ k', ts = k' + 1 := ⟨ts - 1, by omega⟩
      simp only [msgAt] at hm
      simp only [Nat.add_sub_cancel] at hmsg
      rw [hmsg] at hm; cases hm
      exact hpv
    · iintro Hst
      iapply Hk
      unfold lh
      iexists τ ++ [(LRmw aq rl base tvs (dat tvs) asrc vsrc, some ts)]
      iframe Hst
      ipureintro
      exact ⟨by rw [memEv_snoc _ _ rfl, he], hw', V', hg⟩

/-- ONE LR LABEL (M16). -/
theorem wpK_lr1 {s : LP} {ws : PState} {pr : GSet Nat} {ev : Trace} {aq rl : Bool} {base : Int}
    {asrc : List Dsrc} {k : List (Nat × BitVec 8) → LP} {C : List (Nat × BitVec 8) → Prop} (hd : w.pdone s = none)
    (hl : ∀ l s', anyFab w.pstep s () l s' () → ∃ tvs, l = LExLoad aq rl base tvs asrc ∧ s' = k tvs ∧ C tvs) :
    lh γ π w Q ws pr ev ∗
    ▷ (∀ tvs, ⌜C tvs⌝ -∗ ⌜loadOk w.img w.M ws (ldPre ws aq rl (srcsView ws asrc)) base tvs⌝ -∗
        |={⊤}=> ⌜∃ V, grd π w.img w.M V (Q (ev ++ [(LExLoad aq rl base tvs asrc, none)]))⌝ ∗
          (lh γ π w Q { loadRun ws aq rl (srcsView ws asrc) base tvs with
              wRes := some ⟨base, tvs.map Prod.fst, readView ws aq rl (srcsView ws asrc) base tvs⟩ } pr
              (ev ++ [(LExLoad aq rl base tvs asrc, none)]) -∗
            wpK γ π w Q (k tvs) Φ))
    ⊢ wpK γ π w Q s Φ := by
  iintro ⟨⟨%τ, Hst, %hinv⟩, Hk⟩
  obtain ⟨he, hw, _⟩ := hinv
  iapply (wpH_lr (Ψ := ΨK w.M Q) hd hl)
  iframe Hst
  inext
  iintro %tvs %hC %hlo _
  imod Hk $$ %tvs %hC %hlo with ⟨%hQ, Hk⟩
  obtain ⟨V', hg⟩ := hQ
  imodintro
  isplitr
  · ipureintro
    exact ⟨V', fun hv => ⟨by rw [memEv_snoc _ _ rfl, he]; exact hg hv, wrOk_snoc_none hw⟩⟩
  · iintro Hst
    iapply Hk
    unfold lh
    iexists τ ++ [(LExLoad aq rl base tvs asrc, none)]
    iframe Hst
    ipureintro
    exact ⟨by rw [memEv_snoc _ _ rfl, he], wrOk_snoc_none hw, V', hg⟩

/-- ONE SC LABEL (M16): the success `LExStore` (continuation `kS`) or the failure `LExFail` (continuation `kF`). -/
theorem wpK_sc1 {s kS kF : LP} {ws : PState} {pr : GSet Nat} {ev : Trace} {aq rl : Bool} {base : Int}
    {data : List (BitVec 8)} {asrc vsrc : List Dsrc} (hd : w.pdone s = none)
    (hl : ∀ l s', anyFab w.pstep s () l s' () →
      (l = LExStore aq rl base data asrc vsrc ∧ s' = kS) ∨ (l = LExFail ∧ s' = kF)) :
    lh γ π w Q ws pr ev ∗
    ▷ ((∀ ts R, ⌜ws.wRes = some R⌝ -∗ ⌜ts ∈ pr⌝ -∗ ⌜w.M[ts - 1]? = some ⟨base, data, some w.h, .excl⟩⌝ -∗
          ⌜exclOk w.M w.h R.rvBase R.rvTs ts⌝ -∗ ⌜∀ t ∈ R.rvTs, t < ts⌝ -∗ ⌜cohBelow ws base data.length ts⌝ -∗
          ⌜max (stPreA ws aq rl (srcsView ws asrc) (srcsView ws vsrc)) R.rvView < ts⌝ -∗
          |={⊤}=> ⌜∃ V, grd π w.img w.M V (Q (ev ++ [(LExStore aq rl base data asrc vsrc, some ts)]))⌝ ∗
            ⌜grd π w.img w.M (max (stPreA ws aq rl (srcsView ws asrc) (srcsView ws vsrc)) R.rvView)
              (π.okMsg ⟨base, data, some w.h, .excl⟩)⌝ ∗
            (lh γ π w Q { acqPost (storeRun ws rl (srcsView ws asrc) ts base data.length ts) aq ts with
                wLdv := max (storeRun ws rl (srcsView ws asrc) ts base data.length ts).wLdv ts
                wRes := none } (pr \ {ts}) (ev ++ [(LExStore aq rl base data asrc vsrc, some ts)]) -∗
              wpK γ π w Q kS Φ)) ∧
       (lh γ π w Q { ws with wRes := none } pr ev -∗ wpK γ π w Q kF Φ))
    ⊢ wpK γ π w Q s Φ := by
  iintro ⟨⟨%τ, Hst, %hinv⟩, Hk⟩
  obtain ⟨he, hw, V0, hg0⟩ := hinv
  iapply (wpH_sc (Ψ := ΨK w.M Q) hd hl)
  iframe Hst
  inext
  isplit
  · icases Hk with ⟨Hk, -⟩
    iintro %ts %R %hR %hts %hmsg %hex %hlt %hcoh %hext _
    imod Hk $$ %ts %R %hR %hts %hmsg %hex %hlt %hcoh %hext with ⟨%hQ, %hp, Hk⟩
    obtain ⟨V', hg⟩ := hQ
    have hw' : wrOk w.M (τ ++ [(LExStore aq rl base data asrc vsrc, some ts)]) :=
      wrOk_snoc_some hw hmsg (by omega) rfl
    imodintro
    isplitr
    · ipureintro
      exact ⟨V', fun hv => ⟨by rw [memEv_snoc _ _ rfl, he]; exact hg hv, hw'⟩⟩
    isplitr
    · ipureintro; exact hp
    · iintro Hst
      iapply Hk
      unfold lh
      iexists τ ++ [(LExStore aq rl base data asrc vsrc, some ts)]
      iframe Hst
      ipureintro
      exact ⟨by rw [memEv_snoc _ _ rfl, he], hw', V', hg⟩
  · icases Hk with ⟨-, Hk⟩
    iintro _
    imodintro
    isplitr
    · ipureintro
      exact ⟨V0, fun hv => ⟨by rw [memEv_quiet _ _ rfl, he]; exact hg0 hv, wrOk_snoc_none hw⟩⟩
    · iintro Hst
      iapply Hk
      unfold lh
      iexists τ ++ [(LExFail, none)]
      iframe Hst
      ipureintro
      exact ⟨by rw [memEv_quiet _ _ rfl, he], wrOk_snoc_none hw, V0, hg0⟩

/-- THE END: a value state with no step. -/
theorem wpK_done {s : LP} {ws : PState} {pr : GSet Nat} {ev : Trace} {v : V} (hdv : w.pdone s = some v)
    (hns : ∀ l s', ¬ anyFab w.pstep s () l s' ()) :
    lh γ π w Q ws pr ev ∗ (|={⊤}=> Φ v) ⊢ wpK γ π w Q s Φ := by
  iintro ⟨⟨%τ, Hst, %_⟩, Hk⟩
  iapply (wpH_done (Ψ := ΨK w.M Q) hdv hns)
  iframe Hst
  iintro _
  iexact Hk

end rules

/-! ## 5. Instruction rules (one litmus instruction) -/

/-- The data an AMO writes (MachCert.lean `instrNext`'s `.amo` arm). -/
def amoD (op : Weak.Prom.Ref.AmoOp) (sz b : Nat) (tvs : List (Nat × BitVec 8)) : List (BitVec 8) :=
  toBytes (amoOp op sz (ofBytes (tvs.map Prod.snd)) (b % 2 ^ (8 * sz))) sz

theorem litNext_fence {s : LP} {f : Weak.Prom.Ref.FenceSet} (hq : s.q = []) (hp : s.prog[s.pc]? = some (.fence f))
    {l : PLabel} {s' : LP} (h : litNext s l = some s') :
    l = LFence f.pr f.pw f.sr f.sw ∧ s' = { s with regs := s.regs, pc := s.pc + 1, q := [LInstr] } := by
  unfold litNext at h
  rw [hq] at h
  simp only [hp, instrNext, go1] at h
  split at h
  · next he => cases h; exact ⟨he, rfl⟩
  · cases h

theorem litNext_amo {s : LP} {op : Weak.Prom.Ref.AmoOp} {sz : Nat} {aq rl : Bool} {rd rs2 rs1 : Nat} (hq : s.q = [])
    (hp : s.prog[s.pc]? = some (.amo op sz aq rl rd rs2 rs1)) (ha : aligned (s.rd rs1) sz = true)
    {l : PLabel} {s' : LP} (h : litNext s l = some s') :
    ∃ tvs, l = LRmw aq rl ((s.rd rs1 : Nat) : Int) tvs (amoD op sz (s.rd rs2) tvs) (srcR rs1) (srcR rs2) ∧
      s' = { s with regs := s.wr rd (sext sz (ofBytes (tvs.map Prod.snd))), pc := s.pc + 1,
                    q := regWL rd [.DLdRes] ++ [LInstr] } ∧ tvs.length = sz := by
  unfold litNext at h
  rw [hq] at h
  simp only [hp, instrNext, ha, Bool.not_true, Bool.false_eq_true, if_false] at h
  split at h
  · next aq' rl' b tvs data asrc vsrc =>
    split at h
    · next hc =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hc
      subst h1 h2 h3 h5 h6 h7
      cases h
      exact ⟨tvs, rfl, rfl, h4⟩
    · cases h
  · cases h

theorem pc_lt {s : LP} {ins : Instr} (hp : s.prog[s.pc]? = some ins) : s.pc < s.prog.length :=
  (List.getElem?_eq_some_iff.1 hp).1

theorem quiet_regWL (rd : Nat) (srcs : List Dsrc) {tl : List PLabel} (ht : ∀ l ∈ tl, quietL l = true) :
    ∀ l ∈ regWL rd srcs ++ tl, quietL l = true := by
  intro l hl
  unfold regWL at hl
  split at hl
  · exact ht l (by simpa using hl)
  · rcases List.mem_append.1 hl with hl | hl
    · rw [List.mem_singleton] at hl; subst hl; rfl
    · exact ht l hl

section instr

variable {V : Type}
variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [InvGS_gen hlc GF]
variable {γ : GName} {π : Proto} {w : HW LP Unit V} {Q : Trace → Prop} {Φ : V → IProp GF}

/-- A non-empty queue of quiet labels, drained. -/
theorem wpK_drainA (hw : LitW w) {pr : GSet Nat} {ev : Trace} (labs : List PLabel) (s k : LP) (ws wsf : PState)
    (hne : labs ≠ []) (hql : ∀ l ∈ labs, quietL l = true) (hs : s.q = labs) (hk : k = { s with q := [] })
    (hf : qPosts ws labs = wsf) :
    lh γ π w Q ws pr ev ∗ ▷ (lh γ π w Q wsf pr ev -∗ wpK γ π w Q k Φ) ⊢ wpK γ π w Q s Φ := by
  cases labs with
  | nil => exact absurd rfl hne
  | cons l0 r => exact wpK_drain hw r l0 s k ws wsf hql hs hk hf

/-- **LOAD instruction** `l{b,h,w,d} rd, off(rs1)`: `LLoad`, then `LRegW rd [DLdRes]` (unless `rd = x0`), `LInstr`. -/
theorem wpK_ld (hw : LitW w) {s : LP} {sz rd rs1 off : Nat} {sgn : Bool} {base : Int} {ws : PState}
    {pr : GSet Nat} {ev : Trace} (hag : LitAg w s) (hq : s.q = []) (hp : s.prog[s.pc]? = some (.load sz sgn rd rs1 off))
    (ha : aligned ((s.rd rs1 + off) % two64) sz = true) (hb : (((s.rd rs1 + off) % two64 : Nat) : Int) = base) :
    lh γ π w Q ws pr ev ∗
    ▷ (∀ tvs, ⌜tvs.length = sz⌝ -∗ ⌜loadOk w.img w.M ws (ldPre ws false false (srcsView ws (srcR rs1))) base tvs⌝ -∗
        |={⊤}=> ⌜∃ V, grd π w.img w.M V (Q (ev ++ [(LLoad false false base tvs (srcR rs1), none)]))⌝ ∗
          (∀ s', ⌜LPstep s s' (s.pc + 1) rd (ldVal sgn sz tvs)⌝ -∗
            lh γ π w Q (qPosts (loadRun ws false false (srcsView ws (srcR rs1)) base tvs) (regWL rd [.DLdRes] ++ [LInstr]))
              pr (ev ++ [(LLoad false false base tvs (srcR rs1), none)]) -∗ wpK γ π w Q s' Φ))
    ⊢ wpK γ π w Q s Φ := by
  iintro ⟨Hl, Hk⟩
  iapply (wpK_load1
    (k := fun tvs => { s with regs := s.wr rd (ldVal sgn sz tvs), pc := s.pc + 1, q := regWL rd [.DLdRes] ++ [LInstr] })
    (C := fun tvs => tvs.length = sz) (hw.2 s (.inr (pc_lt hp)))
    (fun l s' hs => by
      obtain ⟨tvs, h1, h2, h3⟩ := litNext_load hq hp ha ((hag l s').1 hs)
      exact ⟨tvs, by rw [h1, hb], by rw [h2]; rfl, h3⟩))
  iframe Hl
  inext
  iintro %tvs %hC %hlo
  imod Hk $$ %tvs %hC %hlo with ⟨%hQ, Hk⟩
  imodintro
  isplitr
  · ipureintro; exact hQ
  · iintro Hl
    iapply (wpK_drainA hw (regWL rd [.DLdRes] ++ [LInstr]) _
      { s with regs := s.wr rd (ldVal sgn sz tvs), pc := s.pc + 1, q := [] } _ _ (by simp)
      (quiet_regWL rd _ (by simp [quietL])) rfl rfl rfl)
    iframe Hl
    inext
    iintro Hl
    iapply Hk $$ %_ %(LPstep_wr s rd _ _) Hl

/-- **STORE instruction** `s{b,h,w,d} rs2, off(rs1)`: `LStore` (FULFIL), then `LInstr`. -/
theorem wpK_sw (hw : LitW w) {s : LP} {sz rs2 rs1 off : Nat} {base : Int} {ws : PState} {pr : GSet Nat}
    {ev : Trace} (hag : LitAg w s) (hq : s.q = []) (hp : s.prog[s.pc]? = some (.store sz rs2 rs1 off))
    (ha : aligned ((s.rd rs1 + off) % two64) sz = true) (hb : (((s.rd rs1 + off) % two64 : Nat) : Int) = base) :
    lh γ π w Q ws pr ev ∗
    ▷ (∀ ts, ⌜ts ∈ pr⌝ -∗ ⌜w.M[ts - 1]? = some ⟨base, toBytes (s.rd rs2) sz, some w.h, .plain⟩⌝ -∗
        ⌜cohBelow ws base (toBytes (s.rd rs2) sz).length ts⌝ -∗
        ⌜stPreA ws false false (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2)) < ts⌝ -∗
        |={⊤}=> ⌜∃ V, grd π w.img w.M V
            (Q (ev ++ [(LStore false false base (toBytes (s.rd rs2) sz) (srcR rs1) (srcR rs2), some ts)]))⌝ ∗
          ⌜grd π w.img w.M (stPreA ws false false (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2)))
            (π.okMsg ⟨base, toBytes (s.rd rs2) sz, some w.h, .plain⟩)⌝ ∗
          (∀ s', ⌜LPstep s s' (s.pc + 1) 0 0⌝ -∗
            lh γ π w Q (instrR (acqPost (storeRun ws false (srcsView ws (srcR rs1))
                (max (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2))) base (toBytes (s.rd rs2) sz).length ts) false ts))
              (pr \ {ts}) (ev ++ [(LStore false false base (toBytes (s.rd rs2) sz) (srcR rs1) (srcR rs2), some ts)]) -∗
            wpK γ π w Q s' Φ))
    ⊢ wpK γ π w Q s Φ := by
  iintro ⟨Hl, Hk⟩
  iapply (wpK_store1 (k := { s with pc := s.pc + 1, q := [LInstr] }) (hw.2 s (.inr (pc_lt hp)))
    (fun l s' hs => by
      obtain ⟨h1, h2⟩ := litNext_store hq hp ha ((hag l s').1 hs)
      exact ⟨by rw [h1, hb], h2⟩))
  iframe Hl
  inext
  iintro %ts %hts %hmsg %hcoh %hext
  imod Hk $$ %ts %hts %hmsg %hcoh %hext with ⟨%hQ, %hpv, Hk⟩
  imodintro
  isplitr
  · ipureintro; exact hQ
  isplitr
  · ipureintro; exact hpv
  · iintro Hl
    iapply (wpK_drainA hw [LInstr] _ { s with pc := s.pc + 1, q := [] } _
      (instrR (acqPost (storeRun ws false (srcsView ws (srcR rs1))
        (max (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2))) base (toBytes (s.rd rs2) sz).length ts) false ts))
      (by simp) (by simp [quietL]) rfl rfl rfl)
    iframe Hl
    inext
    iintro Hl
    iapply Hk $$ %_ %(LPstep_same s _) Hl

/-- **ALU instruction** `op rd, rs1, rs2` (`rd ≠ x0`): `LRegW rd (rs1 ++ rs2)`, `LInstr`. -/
theorem wpK_alu (hw : LitW w) {s : LP} {op : Weak.Prom.Ref.Alu} {rd rs1 rs2 : Nat} {ws : PState} {pr : GSet Nat}
    {ev : Trace} (hag : LitAg w s) (hq : s.q = []) (hp : s.prog[s.pc]? = some (.alu op rd rs1 rs2)) (hrd : rd ≠ 0) :
    lh γ π w Q ws pr ev ∗
    ▷ (∀ s', ⌜LPstep s s' (s.pc + 1) rd (aluOp op (s.rd rs1) (s.rd rs2))⌝ -∗
        lh γ π w Q (instrR (regWP ws rd (srcR rs1 ++ srcR rs2))) pr ev -∗ wpK γ π w Q s' Φ)
    ⊢ wpK γ π w Q s Φ := by
  iintro ⟨Hl, Hk⟩
  iapply (wpK_q1 (k := { s with regs := s.wr rd (aluOp op (s.rd rs1) (s.rd rs2)), pc := s.pc + 1, q := [LInstr] })
    (l0 := LRegW rd (srcR rs1 ++ srcR rs2)) (ws1 := regWP ws rd (srcR rs1 ++ srcR rs2)) rfl (hw.2 s (.inr (pc_lt hp)))
    (fun l s' hs => litNext_alu hq hp hrd ((hag l s').1 hs)) rfl)
  iframe Hl
  inext
  iintro Hl
  iapply (wpK_drainA hw [LInstr] _ { s with regs := s.wr rd (aluOp op (s.rd rs1) (s.rd rs2)), pc := s.pc + 1, q := [] }
    _ (instrR (regWP ws rd (srcR rs1 ++ srcR rs2))) (by simp) (by simp [quietL]) rfl rfl rfl)
  iframe Hl
  inext
  iintro Hl
  iapply Hk $$ %_ %(LPstep_wr s rd _ _) Hl

/-- **ALU-immediate instruction** `op rd, rs1, imm` (`rd ≠ x0`; `li rd, v` is `addi rd, x0, v`). -/
theorem wpK_alui (hw : LitW w) {s : LP} {op : Weak.Prom.Ref.Alu} {rd rs1 imm : Nat} {ws : PState} {pr : GSet Nat}
    {ev : Trace} (hag : LitAg w s) (hq : s.q = []) (hp : s.prog[s.pc]? = some (.alui op rd rs1 imm)) (hrd : rd ≠ 0) :
    lh γ π w Q ws pr ev ∗
    ▷ (∀ s', ⌜LPstep s s' (s.pc + 1) rd (aluOp op (s.rd rs1) imm)⌝ -∗
        lh γ π w Q (instrR (regWP ws rd (srcR rs1))) pr ev -∗ wpK γ π w Q s' Φ)
    ⊢ wpK γ π w Q s Φ := by
  iintro ⟨Hl, Hk⟩
  iapply (wpK_q1 (k := { s with regs := s.wr rd (aluOp op (s.rd rs1) imm), pc := s.pc + 1, q := [LInstr] })
    (l0 := LRegW rd (srcR rs1)) (ws1 := regWP ws rd (srcR rs1)) rfl (hw.2 s (.inr (pc_lt hp)))
    (fun l s' hs => litNext_alui hq hp hrd ((hag l s').1 hs)) rfl)
  iframe Hl
  inext
  iintro Hl
  iapply (wpK_drainA hw [LInstr] _ { s with regs := s.wr rd (aluOp op (s.rd rs1) imm), pc := s.pc + 1, q := [] }
    _ (instrR (regWP ws rd (srcR rs1))) (by simp) (by simp [quietL]) rfl rfl rfl)
  iframe Hl
  inext
  iintro Hl
  iapply Hk $$ %_ %(LPstep_wr s rd _ _) Hl

/-- **FENCE instruction** `fence pred, succ`: `LFence`, `LInstr`. -/
theorem wpK_fence (hw : LitW w) {s : LP} {f : Weak.Prom.Ref.FenceSet} {ws : PState} {pr : GSet Nat} {ev : Trace}
    (hag : LitAg w s) (hq : s.q = []) (hp : s.prog[s.pc]? = some (.fence f)) :
    lh γ π w Q ws pr ev ∗
    ▷ (∀ s', ⌜LPstep s s' (s.pc + 1) 0 0⌝ -∗ lh γ π w Q (instrR (fencePost ws f.pr f.pw f.sr f.sw)) pr ev -∗
        wpK γ π w Q s' Φ)
    ⊢ wpK γ π w Q s Φ := by
  iintro ⟨Hl, Hk⟩
  iapply (wpK_q1 (k := { s with regs := s.regs, pc := s.pc + 1, q := [LInstr] })
    (l0 := LFence f.pr f.pw f.sr f.sw) (ws1 := fencePost ws f.pr f.pw f.sr f.sw) rfl (hw.2 s (.inr (pc_lt hp)))
    (fun l s' hs => litNext_fence hq hp ((hag l s').1 hs)) rfl)
  iframe Hl
  inext
  iintro Hl
  iapply (wpK_drainA hw [LInstr] _ { s with pc := s.pc + 1, q := [] } _ (instrR (fencePost ws f.pr f.pw f.sr f.sw))
    (by simp) (by simp [quietL]) rfl rfl rfl)
  iframe Hl
  inext
  iintro Hl
  iapply Hk $$ %_ %(LPstep_same s _) Hl

/-- **BRANCH instruction** `b<c> rs1, rs2, tgt` (forward target): `LCtrl (rs1 ++ rs2)` (rule 11), `LInstr`. -/
theorem wpK_br (hw : LitW w) {s : LP} {c : Weak.Prom.Ref.BrC} {rs1 rs2 tgt : Nat} {ws : PState} {pr : GSet Nat}
    {ev : Trace} (hag : LitAg w s) (hq : s.q = []) (hp : s.prog[s.pc]? = some (.br c rs1 rs2 tgt))
    (ht : ¬ (tgt ≤ s.pc ∨ s.prog.length < tgt)) :
    lh γ π w Q ws pr ev ∗
    ▷ (∀ s', ⌜LPstep s s' (if brEval c (s.rd rs1) (s.rd rs2) then tgt else s.pc + 1) 0 0⌝ -∗
        lh γ π w Q (instrR (ctrlP ws (srcR rs1 ++ srcR rs2))) pr ev -∗ wpK γ π w Q s' Φ)
    ⊢ wpK γ π w Q s Φ := by
  iintro ⟨Hl, Hk⟩
  iapply (wpK_q1
    (k := { s with regs := s.regs, pc := if brEval c (s.rd rs1) (s.rd rs2) then tgt else s.pc + 1, q := [LInstr] })
    (l0 := LCtrl (srcR rs1 ++ srcR rs2)) (ws1 := ctrlP ws (srcR rs1 ++ srcR rs2)) rfl (hw.2 s (.inr (pc_lt hp)))
    (fun l s' hs => litNext_br hq hp ht ((hag l s').1 hs)) rfl)
  iframe Hl
  inext
  iintro Hl
  iapply (wpK_drainA hw [LInstr] _ { s with pc := if brEval c (s.rd rs1) (s.rd rs2) then tgt else s.pc + 1, q := [] }
    _ (instrR (ctrlP ws (srcR rs1 ++ srcR rs2))) (by simp) (by simp [quietL]) rfl rfl rfl)
  iframe Hl
  inext
  iintro Hl
  iapply Hk $$ %_ %(LPstep_same s _) Hl

/-- **AMO instruction** `amo<op>.<sz>[.aq][.rl] rd, rs2, (rs1)` (fused, M0): `LRmw`, `LRegW rd [DLdRes]`, `LInstr`. -/
theorem wpK_amo (hw : LitW w) {s : LP} {op : Weak.Prom.Ref.AmoOp} {sz : Nat} {aq rl : Bool} {rd rs2 rs1 : Nat}
    {base : Int} {ws : PState} {pr : GSet Nat} {ev : Trace} (hag : LitAg w s) (hq : s.q = [])
    (hp : s.prog[s.pc]? = some (.amo op sz aq rl rd rs2 rs1)) (ha : aligned (s.rd rs1) sz = true)
    (hb : ((s.rd rs1 : Nat) : Int) = base) :
    lh γ π w Q ws pr ev ∗
    ▷ (∀ tvs ts, ⌜tvs.length = sz⌝ -∗ ⌜ts ∈ pr⌝ -∗
        ⌜w.M[ts - 1]? = some ⟨base, amoD op sz (s.rd rs2) tvs, some w.h, .excl⟩⌝ -∗
        ⌜loadOk w.img w.M ws (ldPre ws aq false (srcsView ws (srcR rs1))) base tvs⌝ -∗
        ⌜exclOk w.M w.h base (tvs.map Prod.fst) ts⌝ -∗
        ⌜cohBelow (loadRun ws aq false (srcsView ws (srcR rs1)) base tvs) base (amoD op sz (s.rd rs2) tvs).length ts⌝ -∗
        ⌜stPre (loadRun ws aq false (srcsView ws (srcR rs1)) base tvs) rl (srcsView ws (srcR rs1))
          (srcsView ws (srcR rs2)) < ts⌝ -∗
        |={⊤}=> ⌜∃ V, grd π w.img w.M V
            (Q (ev ++ [(LRmw aq rl base tvs (amoD op sz (s.rd rs2) tvs) (srcR rs1) (srcR rs2), some ts)]))⌝ ∗
          ⌜grd π w.img w.M (stPre (loadRun ws aq false (srcsView ws (srcR rs1)) base tvs) rl (srcsView ws (srcR rs1))
            (srcsView ws (srcR rs2))) (π.okMsg ⟨base, amoD op sz (s.rd rs2) tvs, some w.h, .excl⟩)⌝ ∗
          (∀ s', ⌜LPstep s s' (s.pc + 1) rd (sext sz (ofBytes (tvs.map Prod.snd)))⌝ -∗
            lh γ π w Q (qPosts (amoPost (storeRun (loadRun ws aq false (srcsView ws (srcR rs1)) base tvs) rl
                (srcsView ws (srcR rs1)) ts base (amoD op sz (s.rd rs2) tvs).length ts) aq ts)
                (regWL rd [.DLdRes] ++ [LInstr])) (pr \ {ts})
              (ev ++ [(LRmw aq rl base tvs (amoD op sz (s.rd rs2) tvs) (srcR rs1) (srcR rs2), some ts)]) -∗
            wpK γ π w Q s' Φ))
    ⊢ wpK γ π w Q s Φ := by
  iintro ⟨Hl, Hk⟩
  iapply (wpK_rmw1 (dat := amoD op sz (s.rd rs2))
    (k := fun tvs =>
      { s with regs := s.wr rd (sext sz (ofBytes (tvs.map Prod.snd))), pc := s.pc + 1, q := regWL rd [.DLdRes] ++ [LInstr] })
    (C := fun tvs => tvs.length = sz) (hw.2 s (.inr (pc_lt hp)))
    (fun l s' hs => by
      obtain ⟨tvs, h1, h2, h3⟩ := litNext_amo hq hp ha ((hag l s').1 hs)
      exact ⟨tvs, by rw [h1, hb], h2, h3⟩))
  iframe Hl
  inext
  iintro %tvs %ts %hC %_ %hts %hmsg %hlo %hex %hcoh %hext
  imod Hk $$ %tvs %ts %hC %hts %hmsg %hlo %hex %hcoh %hext with ⟨%hQ, %hpv, Hk⟩
  imodintro
  isplitr
  · ipureintro; exact hQ
  isplitr
  · ipureintro; exact hpv
  · iintro Hl
    iapply (wpK_drainA hw (regWL rd [.DLdRes] ++ [LInstr]) _
      { s with regs := s.wr rd (sext sz (ofBytes (tvs.map Prod.snd))), pc := s.pc + 1, q := [] } _ _ (by simp)
      (quiet_regWL rd _ (by simp [quietL])) rfl rfl rfl)
    iframe Hl
    inext
    iintro Hl
    iapply Hk $$ %_ %(LPstep_wr s rd _ _) Hl

/-- **LR instruction** `lr.<sz> rd, (rs1)` (no annotation): `LExLoad`, `LRegW rd [DLdRes]`, `LInstr`. -/
theorem wpK_lr (hw : LitW w) {s : LP} {sz rd rs1 : Nat} {base : Int} {ws : PState} {pr : GSet Nat} {ev : Trace}
    (hag : LitAg w s) (hq : s.q = []) (hp : s.prog[s.pc]? = some (.lr sz false false rd rs1))
    (ha : aligned (s.rd rs1) sz = true) (hb : ((s.rd rs1 : Nat) : Int) = base) :
    lh γ π w Q ws pr ev ∗
    ▷ (∀ tvs, ⌜tvs.length = sz⌝ -∗ ⌜loadOk w.img w.M ws (ldPre ws false false (srcsView ws (srcR rs1))) base tvs⌝ -∗
        |={⊤}=> ⌜∃ V, grd π w.img w.M V (Q (ev ++ [(LExLoad false false base tvs (srcR rs1), none)]))⌝ ∗
          (∀ s', ⌜LPstep s s' (s.pc + 1) rd (sext sz (ofBytes (tvs.map Prod.snd)))⌝ -∗
            lh γ π w Q (qPosts { loadRun ws false false (srcsView ws (srcR rs1)) base tvs with
                wRes := some ⟨base, tvs.map Prod.fst, readView ws false false (srcsView ws (srcR rs1)) base tvs⟩ }
                (regWL rd [.DLdRes] ++ [LInstr]))
              pr (ev ++ [(LExLoad false false base tvs (srcR rs1), none)]) -∗ wpK γ π w Q s' Φ))
    ⊢ wpK γ π w Q s Φ := by
  iintro ⟨Hl, Hk⟩
  iapply (wpK_lr1
    (k := fun tvs =>
      { s with regs := s.wr rd (sext sz (ofBytes (tvs.map Prod.snd))), pc := s.pc + 1, q := regWL rd [.DLdRes] ++ [LInstr] })
    (C := fun tvs => tvs.length = sz) (hw.2 s (.inr (pc_lt hp)))
    (fun l s' hs => by
      obtain ⟨tvs, h1, h2, h3⟩ := litNext_lr hq hp ha ((hag l s').1 hs)
      exact ⟨tvs, by rw [h1, hb], h2, h3⟩))
  iframe Hl
  inext
  iintro %tvs %hC %hlo
  imod Hk $$ %tvs %hC %hlo with ⟨%hQ, Hk⟩
  imodintro
  isplitr
  · ipureintro; exact hQ
  · iintro Hl
    iapply (wpK_drainA hw (regWL rd [.DLdRes] ++ [LInstr]) _
      { s with regs := s.wr rd (sext sz (ofBytes (tvs.map Prod.snd))), pc := s.pc + 1, q := [] } _ _ (by simp)
      (quiet_regWL rd _ (by simp [quietL])) rfl rfl rfl)
    iframe Hl
    inext
    iintro Hl
    iapply Hk $$ %_ %(LPstep_wr s rd _ _) Hl

/-- **SC instruction** `sc.<sz> rd, rs2, (rs1)` (no annotation): the success `LExStore` (then `LRegW rd [DLdRes]`,
`LExFail`, `LInstr`; `rd := 0`) or the failure `LExFail` (then `LRegW rd []`, `LExFail`, `LInstr`; `rd := 1`). -/
theorem wpK_sc (hw : LitW w) {s : LP} {sz rd rs2 rs1 : Nat} {base : Int} {ws : PState} {pr : GSet Nat} {ev : Trace}
    (hag : LitAg w s) (hq : s.q = []) (hp : s.prog[s.pc]? = some (.sc sz false false rd rs2 rs1))
    (ha : aligned (s.rd rs1) sz = true) (hb : ((s.rd rs1 : Nat) : Int) = base) :
    lh γ π w Q ws pr ev ∗
    ▷ ((∀ ts R, ⌜ws.wRes = some R⌝ -∗ ⌜ts ∈ pr⌝ -∗
          ⌜w.M[ts - 1]? = some ⟨base, toBytes (s.rd rs2) sz, some w.h, .excl⟩⌝ -∗
          ⌜exclOk w.M w.h R.rvBase R.rvTs ts⌝ -∗ ⌜∀ t ∈ R.rvTs, t < ts⌝ -∗
          ⌜cohBelow ws base (toBytes (s.rd rs2) sz).length ts⌝ -∗
          ⌜max (stPreA ws false false (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2))) R.rvView < ts⌝ -∗
          |={⊤}=> ⌜∃ V, grd π w.img w.M V
              (Q (ev ++ [(LExStore false false base (toBytes (s.rd rs2) sz) (srcR rs1) (srcR rs2), some ts)]))⌝ ∗
            ⌜grd π w.img w.M (max (stPreA ws false false (srcsView ws (srcR rs1)) (srcsView ws (srcR rs2))) R.rvView)
              (π.okMsg ⟨base, toBytes (s.rd rs2) sz, some w.h, .excl⟩)⌝ ∗
            (∀ s', ⌜LPstep s s' (s.pc + 1) rd 0⌝ -∗
              lh γ π w Q (qPosts { acqPost (storeRun ws false (srcsView ws (srcR rs1)) ts base
                    (toBytes (s.rd rs2) sz).length ts) false ts with
                  wLdv := max (storeRun ws false (srcsView ws (srcR rs1)) ts base (toBytes (s.rd rs2) sz).length ts).wLdv ts
                  wRes := none } (regWL rd [.DLdRes] ++ [LExFail, LInstr])) (pr \ {ts})
                (ev ++ [(LExStore false false base (toBytes (s.rd rs2) sz) (srcR rs1) (srcR rs2), some ts)]) -∗
              wpK γ π w Q s' Φ)) ∧
       (∀ s', ⌜LPstep s s' (s.pc + 1) rd 1⌝ -∗
          lh γ π w Q (qPosts { ws with wRes := none } (regWL rd [] ++ [LExFail, LInstr])) pr ev -∗ wpK γ π w Q s' Φ))
    ⊢ wpK γ π w Q s Φ := by
  iintro ⟨Hl, Hk⟩
  iapply (wpK_sc1 (kS := { s with regs := s.wr rd 0, pc := s.pc + 1, q := regWL rd [.DLdRes] ++ [LExFail, LInstr] })
    (kF := { s with regs := s.wr rd 1, pc := s.pc + 1, q := regWL rd [] ++ [LExFail, LInstr] })
    (hw.2 s (.inr (pc_lt hp)))
    (fun l s' hs => by
      rcases litNext_sc hq hp ha ((hag l s').1 hs) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact .inl ⟨by rw [h1, hb], h2⟩
      · exact .inr ⟨h1, h2⟩))
  iframe Hl
  inext
  isplit
  · icases Hk with ⟨Hk, -⟩
    iintro %ts %R %hR %hts %hmsg %hex %hlt %hcoh %hext
    imod Hk $$ %ts %R %hR %hts %hmsg %hex %hlt %hcoh %hext with ⟨%hQ, %hpv, Hk⟩
    imodintro
    isplitr
    · ipureintro; exact hQ
    isplitr
    · ipureintro; exact hpv
    · iintro Hl
      iapply (wpK_drainA hw (regWL rd [.DLdRes] ++ [LExFail, LInstr]) _
        { s with regs := s.wr rd 0, pc := s.pc + 1, q := [] } _ _ (by simp)
        (quiet_regWL rd _ (by simp [quietL])) rfl rfl rfl)
      iframe Hl
      inext
      iintro Hl
      iapply Hk $$ %_ %(LPstep_wr s rd _ _) Hl
  · icases Hk with ⟨-, Hk⟩
    iintro Hl
    iapply (wpK_drainA hw (regWL rd [] ++ [LExFail, LInstr]) _
      { s with regs := s.wr rd 1, pc := s.pc + 1, q := [] } _ _ (by simp)
      (quiet_regWL rd _ (by simp [quietL])) rfl rfl rfl)
    iframe Hl
    inext
    iintro Hl
    iapply Hk $$ %_ %(LPstep_wr s rd _ _) Hl

/-- **THE END** of a litmus hart: nothing queued, no instruction left. -/
theorem wpK_end {s : LP} {ws : PState} {pr : GSet Nat} {ev : Trace} {v : V} (hag : LitAg w s) (hq : s.q = [])
    (hpc : s.prog.length ≤ s.pc) (hdv : w.pdone s = some v) :
    lh γ π w Q ws pr ev ∗ (|={⊤}=> Φ v) ⊢ wpK γ π w Q s Φ :=
  wpK_done hdv (fun l s' hs => by
    rw [hag l s', litNext_end hq (List.getElem?_eq_none hpc)] at hs; cases hs)

end instr

end Weak.Prom.PF
