/-
Weak/Prom: **S5a — the Sail-level wp `swpP` and the register / PC / CSR event leaves** over the hart lift
(HartLift.lean; plan rev 7 §7 "`swp` CPS wp (Wp.lean:557) SURVIVES — generic over `wpHart`").

* `swpP cpu m Φ` — MachCSL's `swp` (Wp.lean:557), verbatim over `wpHP`: CPS over every monadic context `C`
  (MachCSL's `MCtx`), so the bind law is free.  `swpP_ret`, `swpP_mono`, `swpP_bind`, `swpP_wpHP` are MachCSL's
  `swp_ret`, `swp_mono`, `swp_bind`, `swp_wpHart` with the same statements and proofs.
* The per-event rules (MachCSL Wp.lean:873–1650), each proved from `wpHP_liftQ` (one `▷`, one `£ 1` per event):
  `swpP_readReg`, `swpP_readReg_any`, `swpP_writeReg`, `swpP_instrAnnounce`, `swpP_branchAnnounce`,
  `swpP_cycleCount`, `swpP_printEffect`, `swpP_getCycleCount`, `swpP_choose`, `swpP_barrier`, and the hart-level
  `wpHP_park` (the parked FENCE.TSO half, M6) and `wpLoopP_restart` (the instruction boundary `LInstr`; MachCSL
  `wpLoop_restartC`).  CSRs are Sail registers: a CSR read or write IS `swpP_readReg` / `swpP_writeReg` (the
  Zicsr old-value capture, FIX S0rest-F1, is the read's label `rdLab`).

STATEMENT CHANGES against MachCSL (each forced by emission v2, Emit.lean; listed in PROGRESS-S5a.md):
1. every event rule takes the hart's CORE `coreP cpu c` (channel + track (a)'s exact state) with `c.fn = none`
   and hands back the core after the step (`qStep`: same promises, the trace extended by the event's label, the
   views as `memStep` moves them; the channel as the emission updates it).  MachCSL has no per-instruction channel
   and keeps its views in `machInterp`.
2. `swpP_writeReg` has NO side condition (MachCSL: `hq` — the write is not an observed privilege crossing / `satp`
   write, NI M2-W1 — and `hk` — no exclusive-reservation kill): emission v2 observes nothing at a register write
   and machine v2's reservation is in the views (`wRes`), untouched by `LRegW`.  WEAKER premises, same conclusion.
3. `swpP_getCycleCount` hands the continuation EVERY answer (`∀ c`; [OWN.P1] C-S constant row, Emit.lean); MachCSL
   answers `0` (`swp_get_cycle_count`).
4. `swpP_barrier` parks FENCE.TSO's second half (`c'.fn = ebarPark b`), applied by `wpHP_park` before the next
   event (M6); MachCSL's barrier is one event (and blocks on a non-empty store buffer, route P).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.HartLift

namespace Weak.Prom.HL

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc depsCtrl ibOfBvn eregNum ebarPark)
open Weak.Prom Weak.Prom.PF Weak.Prom.OA
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D

section swp

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostMapG GF Nat RegVal RegMapF] [GhostVarG GF Chan]
  [GhostVarG GF HSt] [GhostVarG GF Bool] [InvGS_gen hlc GF] [E : PromEnv]

/-! ## 1. `swpP` and its structural rules (MachCSL Wp.lean:557–596) -/

/-- **`swpP cpu m Φ`** (MachCSL `swp`, the paper's `wp Sail(m) {Φ}`): for every monadic context, a continuation
safe at every answer makes the context safe at `m`. -/
def swpP (cpu : CPU) {X : Type} (m : SailM X) (Φ : X → IProp GF) : IProp GF :=
  iprop(∀ C : SailM X → SailM Unit, ⌜MCtx C⌝ →
    (∀ v : X, Φ v -∗ wpHP (hlc := hlc) cpu (C (pure v))) -∗ wpHP (hlc := hlc) cpu (C m))

theorem swpP_ret (cpu : CPU) {X : Type} (x : X) (Φ : X → IProp GF) :
    Φ x ⊢ swpP (hlc := hlc) cpu (pure x) Φ := by
  unfold swpP
  iintro HΦ %C %_ H
  iapply H $$ HΦ

theorem swpP_mono (cpu : CPU) {X : Type} (m : SailM X) (Φ Ψ : X → IProp GF) :
    (∀ v, Φ v -∗ Ψ v) ∗ swpP (hlc := hlc) cpu m Φ ⊢ swpP (hlc := hlc) cpu m Ψ := by
  unfold swpP
  iintro ⟨HΦΨ, Hswp⟩ %C %hC H
  iapply Hswp $$ %C %hC
  iintro %v HΦ
  iapply H
  iapply HΦΨ $$ HΦ

/-- The bind law (MachCSL `swp_bind`). -/
theorem swpP_bind (cpu : CPU) {X Y : Type} (m : SailM X) (f : X → SailM Y) (Φ : Y → IProp GF) :
    swpP (hlc := hlc) cpu m (fun v => swpP (hlc := hlc) cpu (f v) Φ) ⊢ swpP (hlc := hlc) cpu (m >>= f) Φ := by
  unfold swpP
  iintro Hswp %C %hC H
  iapply Hswp $$ %(fun m' : SailM X => C (m' >>= f)) %(MCtx.bind f C hC)
  iintro %v Hinner
  isimp only [pure_bind]
  iapply Hinner $$ %C %hC H

/-- Closing a cycle (MachCSL `swp_wpHart`). -/
theorem swpP_wpHP (cpu : CPU) (m : SailM Unit) :
    swpP (hlc := hlc) cpu m (fun _ => wpLoopP (hlc := hlc) (GF := GF) cpu) ⊢ wpHP (hlc := hlc) cpu m := by
  unfold swpP wpLoopP
  iintro Hswp
  iapply Hswp $$ %(fun m => m) %MCtx.id
  iintro %v HΦ
  isimp only []
  iexact HΦ

/-! ## 2. The generic quiet-event rule -/

/-- **A quiet event `o` with answers in `A`** (MachCSL `swp_event`/`swp_silent`): if emission v2 steps the event
(with no parked fence half) only with label `lab` (quiet), any answer `a ∈ A`, the register file unchanged and the
channel `(fn', ix')`, then the continuation at every possible answer, from the new core, suffices. -/
theorem swpP_ev (cpu : CPU) (o : Outcome Register RegisterType) (A : o.ret → Prop) (lab : PLabel)
    (fn' : Option (Bool × Bool × Bool × Bool)) (ix' : Ix) (c : Core) (hfn : c.fn = none) (hq : quietLab lab = true)
    (hst : ∀ (rs : RegFile) (d : DevStates) (l : PLabel) (h' : HState) (d' : DevStates)
      (k : o.ret → SailM Unit), pstepV2 ⟨cpu, .impure (.ok o) k, rs, none, c.ix⟩ d l h' d' →
        l = lab ∧ ∃ a, A a ∧ h' = ⟨cpu, k a, rs, fn', ix'⟩)
    (Φ : o.ret → IProp GF) :
    coreP cpu c ∗ ▷ (∀ a c', ⌜A a ∧ qStep cpu c lab c' ∧ c'.fn = fn' ∧ c'.ix = ix'⌝ -∗ coreP cpu c' -∗ Φ a)
    ⊢ swpP (hlc := hlc) cpu (FreeM.impure (.ok o) (fun v => FreeM.pure v)) Φ := by
  unfold swpP
  iintro ⟨Hc, HΦ⟩ %C %hC Hcont
  rw [hC]
  iapply wpHP_liftQ cpu _ c (fun rs l h' hp => by
    obtain ⟨d, d', hp⟩ := hp
    rw [hfn] at hp
    rw [(hst rs d l h' d' _ hp).1]; exact hq)
  isplitl [Hc]
  · iexact Hc
  iintro %rs Hra
  inext
  iintro %l %h' %ws' %hp %hm _
  obtain ⟨d, d', hp⟩ := hp
  rw [hfn] at hp
  obtain ⟨rfl, a, ha, rfl⟩ := hst rs d l h' d' _ hp
  imodintro
  isplitl [Hra]
  · iexact Hra
  iintro Hc'
  iapply Hcont
  iapply HΦ $$ %a %(⟨fn', ix', ws', c.pr, c.τ ++ [(l, none)]⟩ : Core) %⟨ha, ⟨rfl, rfl, hm⟩, rfl, rfl⟩ Hc'

/-! ## 3. Registers (and CSRs) -/

/-- **Read a register** (MachCSL `swp_readReg`): the cell pins the value; the label is `rdLab` (silent, or the
Zicsr old-value capture). -/
theorem swpP_readReg (cpu : CPU) (r : Register) (dq : DFrac) (v : RegisterType r) (c : Core) (hfn : c.fn = none)
    (Φ : RegisterType r → IProp GF) :
    coreP cpu c ∗ regP cpu r dq v ∗
    ▷ (∀ c', ⌜qStep cpu c (rdLab c.ix r) c' ∧ c'.fn = none ∧ c'.ix = rdIx c.ix r⌝ -∗ coreP cpu c' -∗
        regP cpu r dq v -∗ Φ v)
    ⊢ swpP (hlc := hlc) cpu (readReg r) Φ := by
  unfold swpP readReg PreSail.readReg PreSail.emit
  iintro ⟨Hc, Hr, HΦ⟩ %C %hC Hcont
  rw [hC]
  iapply wpHP_liftQ cpu _ c (fun rs l h' hp => by
    obtain ⟨d, d', hp⟩ := hp
    rw [hfn] at hp
    rw [(pstepV2_regRead hp).1]; exact rdLab_q _ _)
  isplitl [Hc]
  · iexact Hc
  iintro %rs Hra
  ihave %Hv : ⌜rs r = v⌝ $$ [Hra Hr]
  · icases regP_valid cpu rs r dq v $$ [$Hra $Hr] with %_
    itrivial
  inext
  iintro %l %h' %ws' %hp %hm _
  obtain ⟨d, d', hp⟩ := hp
  rw [hfn] at hp
  obtain ⟨rfl, rfl⟩ := pstepV2_regRead hp
  imodintro
  isplitl [Hra]
  · iexact Hra
  iintro Hc'
  rw [Hv]
  iapply Hcont
  iapply HΦ $$ %(⟨none, rdIx c.ix r, ws', c.pr, c.τ ++ [(rdLab c.ix r, none)]⟩ : Core) %⟨⟨rfl, rfl, hm⟩, rfl, rfl⟩ Hc' Hr

theorem swpP_readReg_bind (cpu : CPU) {X : Type} (r : Register) (dq : DFrac) (v : RegisterType r) (c : Core)
    (hfn : c.fn = none) (f : RegisterType r → SailM X) (Φ : X → IProp GF) :
    coreP cpu c ∗ regP cpu r dq v ∗
    ▷ (∀ c', ⌜qStep cpu c (rdLab c.ix r) c' ∧ c'.fn = none ∧ c'.ix = rdIx c.ix r⌝ -∗ coreP cpu c' -∗
        regP cpu r dq v -∗ swpP (hlc := hlc) cpu (f v) Φ)
    ⊢ swpP (hlc := hlc) cpu (readReg r >>= f) Φ := by
  iintro H
  iapply swpP_bind
  iapply (swpP_readReg cpu r dq v c hfn (fun x => swpP (hlc := hlc) cpu (f x) Φ))
  iexact H

/-- **Read a register WITHOUT owning it** (MachCSL `swp_readReg_any`): the answer is ∀-bound. -/
theorem swpP_readReg_any (cpu : CPU) (r : Register) (c : Core) (hfn : c.fn = none)
    (Φ : RegisterType r → IProp GF) :
    coreP cpu c ∗
    ▷ (∀ v c', ⌜qStep cpu c (rdLab c.ix r) c' ∧ c'.fn = none ∧ c'.ix = rdIx c.ix r⌝ -∗ coreP cpu c' -∗ Φ v)
    ⊢ swpP (hlc := hlc) cpu (readReg r) Φ := by
  unfold swpP readReg PreSail.readReg PreSail.emit
  iintro ⟨Hc, HΦ⟩ %C %hC Hcont
  rw [hC]
  iapply wpHP_liftQ cpu _ c (fun rs l h' hp => by
    obtain ⟨d, d', hp⟩ := hp
    rw [hfn] at hp
    rw [(pstepV2_regRead hp).1]; exact rdLab_q _ _)
  isplitl [Hc]
  · iexact Hc
  iintro %rs Hra
  inext
  iintro %l %h' %ws' %hp %hm _
  obtain ⟨d, d', hp⟩ := hp
  rw [hfn] at hp
  obtain ⟨rfl, rfl⟩ := pstepV2_regRead hp
  imodintro
  isplitl [Hra]
  · iexact Hra
  iintro Hc'
  iapply Hcont
  iapply HΦ $$ %(rs r) %(⟨none, rdIx c.ix r, ws', c.pr, c.τ ++ [(rdLab c.ix r, none)]⟩ : Core) %⟨⟨rfl, rfl, hm⟩, rfl, rfl⟩ Hc'

/-- **Write a register** (MachCSL `swp_writeReg`, with NO side condition, header item 2): the full cell is updated;
the label is `wrLab` (`LCtrl` for `nextPC`, `LRegW` for a tracked register, else silent); a write of
`mcause`/`scause` marks the trap (`wrIx`). -/
theorem swpP_writeReg (cpu : CPU) (r : Register) (v w : RegisterType r) (c : Core) (hfn : c.fn = none)
    (Φ : PUnit → IProp GF) :
    coreP cpu c ∗ regP cpu r (DFrac.own 1) v ∗
    ▷ (∀ c', ⌜qStep cpu c (wrLab c.ix r) c' ∧ c'.fn = none ∧ c'.ix = wrIx c.ix r⌝ -∗ coreP cpu c' -∗
        regP cpu r (DFrac.own 1) w -∗ Φ ())
    ⊢ swpP (hlc := hlc) cpu (writeReg r w) Φ := by
  unfold swpP writeReg PreSail.writeReg PreSail.emit
  iintro ⟨Hc, Hr, HΦ⟩ %C %hC Hcont
  rw [hC]
  iapply wpHP_liftQ cpu _ c (fun rs l h' hp => by
    obtain ⟨d, d', hp⟩ := hp
    rw [hfn] at hp
    rw [(pstepV2_regWrite hp).1]; exact wrLab_q _ _)
  isplitl [Hc]
  · iexact Hc
  iintro %rs Hra
  inext
  iintro %l %h' %ws' %hp %hm _
  obtain ⟨d, d', hp⟩ := hp
  rw [hfn] at hp
  obtain ⟨rfl, rfl⟩ := pstepV2_regWrite hp
  imod regP_update cpu rs r v w $$ [Hra Hr] with ⟨Hra, Hr⟩
  · iframe Hra Hr
  imodintro
  isplitl [Hra]
  · iexact Hra
  iintro Hc'
  iapply Hcont
  iapply HΦ $$ %(⟨none, wrIx c.ix r, ws', c.pr, c.τ ++ [(wrLab c.ix r, none)]⟩ : Core) %⟨⟨rfl, rfl, hm⟩, rfl, rfl⟩ Hc' Hr

theorem swpP_writeReg_bind (cpu : CPU) {X : Type} (r : Register) (v w : RegisterType r) (c : Core)
    (hfn : c.fn = none) (f : PUnit → SailM X) (Φ : X → IProp GF) :
    coreP cpu c ∗ regP cpu r (DFrac.own 1) v ∗
    ▷ (∀ c', ⌜qStep cpu c (wrLab c.ix r) c' ∧ c'.fn = none ∧ c'.ix = wrIx c.ix r⌝ -∗ coreP cpu c' -∗
        regP cpu r (DFrac.own 1) w -∗ swpP (hlc := hlc) cpu (f ()) Φ)
    ⊢ swpP (hlc := hlc) cpu (writeReg r w >>= f) Φ := by
  iintro H
  iapply swpP_bind
  iapply (swpP_writeReg cpu r v w c hfn (fun x => swpP (hlc := hlc) cpu (f x) Φ))
  iexact H

/-! ## 4. The silent and nondeterministic events (MachCSL Wp.lean:1601–1660) -/

/-- The instruction announcement banks the bits (Emit.lean: "the announce banks the bits and resets nothing"). -/
theorem swpP_instrAnnounce (cpu : CPU) {n : Nat} (w : BitVec n) (c : Core) (hfn : c.fn = none)
    (Φ : Unit → IProp GF) :
    coreP cpu c ∗
    ▷ (∀ c', ⌜qStep cpu c LSilent c' ∧ c'.fn = none ∧ c'.ix = { c.ix with bits := some (ibOfBvn w) }⌝ -∗
        coreP cpu c' -∗ Φ ())
    ⊢ swpP (hlc := hlc) cpu (LeanRV64D.Functions.instr_announce w) Φ := by
  refine Entails.trans ?_ (swpP_ev cpu (.instrAnnounce n w) (· = ()) LSilent none { c.ix with bits := some (ibOfBvn w) } c hfn rfl
    (fun rs d l h' d' k hp => by
      obtain ⟨h1, h2⟩ := pstepV2_instrAnnounce hp
      exact ⟨h1, (), rfl, h2⟩) Φ)
  iintro ⟨Hc, HΦ⟩
  iframe Hc
  inext
  iintro %a %c' %⟨ha, h⟩ Hc'
  subst ha
  iapply HΦ $$ %c' %h Hc'

theorem swpP_branchAnnounce (cpu : CPU) (n : Nat) (pc : BitVec n) (c : Core) (hfn : c.fn = none)
    (Φ : Unit → IProp GF) :
    coreP cpu c ∗ ▷ (∀ c', ⌜qStep cpu c LSilent c' ∧ c'.fn = none ∧ c'.ix = c.ix⌝ -∗ coreP cpu c' -∗ Φ ())
    ⊢ swpP (hlc := hlc) cpu (LeanRV64D.Functions.branch_announce n pc) Φ := by
  refine Entails.trans ?_ (swpP_ev cpu (.branchAnnounce n pc) (· = ()) LSilent none c.ix c hfn rfl
    (fun rs d l h' d' k hp => by
      obtain ⟨h1, h2⟩ := pstepV2_branchAnnounce hp
      exact ⟨h1, (), rfl, h2⟩) Φ)
  iintro ⟨Hc, HΦ⟩
  iframe Hc
  inext
  iintro %a %c' %⟨ha, h⟩ Hc'
  subst ha
  iapply HΦ $$ %c' %h Hc'

theorem swpP_cycleCount (cpu : CPU) (c : Core) (hfn : c.fn = none) (Φ : Unit → IProp GF) :
    coreP cpu c ∗ ▷ (∀ c', ⌜qStep cpu c LSilent c' ∧ c'.fn = none ∧ c'.ix = c.ix⌝ -∗ coreP cpu c' -∗ Φ ())
    ⊢ swpP (hlc := hlc) cpu (cycle_count ()) Φ := by
  refine Entails.trans ?_ (swpP_ev cpu .cycleCount (· = ()) LSilent none c.ix c hfn rfl
    (fun rs d l h' d' k hp => by
      obtain ⟨h1, h2⟩ := pstepV2_cycleCount hp
      exact ⟨h1, (), rfl, h2⟩) Φ)
  iintro ⟨Hc, HΦ⟩
  iframe Hc
  inext
  iintro %a %c' %⟨ha, h⟩ Hc'
  subst ha
  iapply HΦ $$ %c' %h Hc'

theorem swpP_printEffect (cpu : CPU) (s : String) (c : Core) (hfn : c.fn = none) (Φ : Unit → IProp GF) :
    coreP cpu c ∗ ▷ (∀ c', ⌜qStep cpu c LSilent c' ∧ c'.fn = none ∧ c'.ix = c.ix⌝ -∗ coreP cpu c' -∗ Φ ())
    ⊢ swpP (hlc := hlc) cpu (print_effect s) Φ := by
  refine Entails.trans ?_ (swpP_ev cpu (.message s) (· = ()) LSilent none c.ix c hfn rfl
    (fun rs d l h' d' k hp => by
      obtain ⟨h1, h2⟩ := pstepV2_message hp
      exact ⟨h1, (), rfl, h2⟩) Φ)
  iintro ⟨Hc, HΦ⟩
  iframe Hc
  inext
  iintro %a %c' %⟨ha, h⟩ Hc'
  subst ha
  iapply HΦ $$ %c' %h Hc'

/-- **The cycle counter answers ANY value** ([OWN.P1]; header item 3: MachCSL answers `0`). -/
theorem swpP_getCycleCount (cpu : CPU) (c : Core) (hfn : c.fn = none) (Φ : Nat → IProp GF) :
    coreP cpu c ∗
    ▷ (∀ (n : Nat) c', ⌜qStep cpu c LSilent c' ∧ c'.fn = none ∧ c'.ix = c.ix⌝ -∗ coreP cpu c' -∗ Φ n)
    ⊢ swpP (hlc := hlc) cpu (get_cycle_count ()) Φ := by
  refine Entails.trans ?_ (swpP_ev cpu .getCycleCount (fun _ => True) LSilent none c.ix c hfn rfl
    (fun rs d l h' d' k hp => by
      obtain ⟨h1, n, h2⟩ := pstepV2_getCycleCount hp
      exact ⟨h1, n, trivial, h2⟩) Φ)
  iintro ⟨Hc, HΦ⟩
  iframe Hc
  inext
  iintro %a %c' %⟨_, h⟩ Hc'
  iapply HΦ $$ %a %c' %h Hc'

/-- A nondeterministic choice (MachCSL `swp_choose`): every answer. -/
theorem swpP_choose (cpu : CPU) (p : Sail.Primitive) (c : Core) (hfn : c.fn = none) (Φ : p.reflect → IProp GF) :
    coreP cpu c ∗
    ▷ (∀ ch c', ⌜qStep cpu c LSilent c' ∧ c'.fn = none ∧ c'.ix = c.ix⌝ -∗ coreP cpu c' -∗ Φ ch)
    ⊢ swpP (hlc := hlc) cpu (PreSail.choose p) Φ := by
  unfold PreSail.choose PreSail.emit
  refine Entails.trans ?_ (swpP_ev cpu (.choose p) (fun _ => True) LSilent none c.ix c hfn rfl
    (fun rs d l h' d' k hp => by
      obtain ⟨h1, ch, h2⟩ := pstepV2_choose hp
      exact ⟨h1, ch, trivial, h2⟩) Φ)
  iintro ⟨Hc, HΦ⟩
  iframe Hc
  inext
  iintro %a %c' %⟨_, h⟩ Hc'
  iapply HΦ $$ %a %c' %h Hc'

/-- **A barrier** (header item 4): its applied-now half (`barLabel b`; `LFenceI` for FENCE.I), FENCE.TSO's second
half parked in the core. -/
theorem swpP_barrier (cpu : CPU) (b : barrier_kind) (c : Core) (hfn : c.fn = none) (Φ : Unit → IProp GF) :
    coreP cpu c ∗
    ▷ (∀ c', ⌜qStep cpu c (barLabel b) c' ∧ c'.fn = ebarPark b ∧ c'.ix = c.ix⌝ -∗ coreP cpu c' -∗ Φ ())
    ⊢ swpP (hlc := hlc) cpu (FreeM.impure (.ok (.barrier b)) (fun v => FreeM.pure v)) Φ := by
  refine Entails.trans ?_ (swpP_ev cpu (.barrier b) (· = ()) (barLabel b) (ebarPark b) c.ix c hfn (barLabel_q b)
    (fun rs d l h' d' k hp => by
      obtain ⟨h1, h2⟩ := pstepV2_barrier hp
      exact ⟨h1, (), rfl, h2⟩) Φ)
  iintro ⟨Hc, HΦ⟩
  iframe Hc
  inext
  iintro %a %c' %⟨ha, h⟩ Hc'
  subst ha
  iapply HΦ $$ %c' %h Hc'

/-! ## 5. The parked fence half and the instruction boundary -/

/-- **THE PARKED FENCE HALF** (M6): with `c.fn = some f`, the next hart step is `LFence f`, whatever `m` is. -/
theorem wpHP_park (cpu : CPU) (m : SailM Unit) (c : Core) (f : Bool × Bool × Bool × Bool) (hfn : c.fn = some f) :
    coreP (GF := GF) cpu c ∗
    ▷ (∀ c', ⌜qStep cpu c (LFence f.1 f.2.1 f.2.2.1 f.2.2.2) c' ∧ c'.fn = none ∧ c'.ix = c.ix⌝ -∗ coreP cpu c' -∗
        wpHP (hlc := hlc) cpu m)
    ⊢ wpHP (hlc := hlc) cpu m := by
  iintro ⟨Hc, HΦ⟩
  iapply wpHP_liftQ cpu m c (fun rs l h' hp => by
    obtain ⟨d, d', hp⟩ := hp
    rw [hfn] at hp
    rw [(pstepV2_park hp).1]; rfl)
  isplitl [Hc]
  · iexact Hc
  iintro %rs Hra
  inext
  iintro %l %h' %ws' %hp %hm _
  obtain ⟨d, d', hp⟩ := hp
  rw [hfn] at hp
  obtain ⟨rfl, rfl⟩ := pstepV2_park hp
  imodintro
  isplitl [Hra]
  · iexact Hra
  iintro Hc'
  iapply HΦ $$ %(⟨none, c.ix, ws', c.pr, c.τ ++ [(LFence f.1 f.2.1 f.2.2.1 f.2.2.2, none)]⟩ : Core)
    %⟨⟨rfl, rfl, hm⟩, rfl, rfl⟩ Hc'

theorem swpP_park (cpu : CPU) {X : Type} (m : SailM X) (Φ : X → IProp GF) (c : Core)
    (f : Bool × Bool × Bool × Bool) (hfn : c.fn = some f) :
    coreP cpu c ∗
    ▷ (∀ c', ⌜qStep cpu c (LFence f.1 f.2.1 f.2.2.1 f.2.2.2) c' ∧ c'.fn = none ∧ c'.ix = c.ix⌝ -∗ coreP cpu c' -∗
        swpP (hlc := hlc) cpu m Φ)
    ⊢ swpP (hlc := hlc) cpu m Φ := by
  iintro ⟨Hc, HΦ⟩
  unfold swpP
  iintro %C %hC Hcont
  iapply wpHP_park cpu (C m) c f hfn
  iframe Hc
  inext
  iintro %c' %h Hc'
  iapply HΦ $$ %c' %h Hc' %C %hC Hcont

/-- **THE INSTRUCTION BOUNDARY** (MachCSL `wpLoop_restartC`): at a clean boundary (`bndClean`: no end-of-SC,
`amocas` write-back or Zicbom operation pending; `ixNone` and every finished register-only instruction are clean)
the hart steps `LInstr` (machine v2 resets `wLdv`, the AMO slot and the fetch view) to the next cycle
`riscvStep tick`, for the tick the hart chooses, the channel reset. -/
theorem wpLoopP_restart (cpu : CPU) (c : Core) (hfn : c.fn = none) (hcl : bndClean c.ix) :
    coreP (GF := GF) cpu c ∗
    ▷ (∀ (tick : Bool) c', ⌜qStep cpu c LInstr c' ∧ c'.fn = none ∧ c'.ix = ixNone⌝ -∗ coreP cpu c' -∗
        wpHP (hlc := hlc) cpu (riscvStep tick))
    ⊢ wpLoopP (hlc := hlc) cpu := by
  iintro ⟨Hc, HΦ⟩
  unfold wpLoopP
  iapply wpHP_liftQ cpu (.pure ()) c (fun rs l h' hp => by
    obtain ⟨d, d', hp⟩ := hp
    rw [hfn] at hp
    rw [(pstepV2_bnd hcl hp).1]; rfl)
  isplitl [Hc]
  · iexact Hc
  iintro %rs Hra
  inext
  iintro %l %h' %ws' %hp %hm _
  obtain ⟨d, d', hp⟩ := hp
  rw [hfn] at hp
  obtain ⟨rfl, tick, rfl⟩ := pstepV2_bnd hcl hp
  imodintro
  isplitl [Hra]
  · iexact Hra
  iintro Hc'
  iapply HΦ $$ %tick %(⟨none, ixNone, ws', c.pr, c.τ ++ [(LInstr, none)]⟩ : Core) %⟨⟨rfl, rfl, hm⟩, rfl, rfl⟩ Hc'

/-! ## 6. Scope hazard: states machine v2 cannot step are VACUOUSLY safe

`wpA` is `MaybeStuck` (plan §2), so `wpHP` holds at every state emission v2 cannot step: a remaining Sail
`.error` site (HAVOC at run level, [OWN.P8]–[OWN.P10], MachHavoc.lean) and a page-walk read (`AK_ttw`; no arm with
translation off, [OWN.P3]).  A leaf whose Sail run passes such a state is therefore TRIVIALLY true from there on:
an S-mode leaf at the `kpt` tier (the fetch translates through `satp`) would be provable and meaningless.  These
two lemmas make the hazard explicit; leaves must stay inside `translationOff` (Emit.lean §5). -/

/-- No step of the hart: its wp holds (any core with no parked fence half). -/
theorem wpHP_noStep (cpu : CPU) (m : SailM Unit) (c : Core) (hfn : c.fn = none)
    (hns : ∀ rs d l h' d', ¬ pstepV2 ⟨cpu, m, rs, none, c.ix⟩ d l h' d') :
    coreP (GF := GF) cpu c ⊢ wpHP (hlc := hlc) cpu m := by
  iintro Hc
  iapply wpHP_lift cpu m c
  iframe Hc
  iintro %rs _
  inext
  iintro %l %ots %h' %ws' %pr' %hp
  obtain ⟨d, d', hp⟩ := hp
  rw [hfn] at hp
  exact absurd hp (hns rs d l h' d')

/-- A Sail `.error` node (HAVOC): vacuously safe. -/
theorem wpHP_error (cpu : CPU) (m : SailM Unit) (hm : ∃ e k, m = FreeM.impure (Except.error e) k) (c : Core)
    (hfn : c.fn = none) : coreP (GF := GF) cpu c ⊢ wpHP (hlc := hlc) cpu m := by
  apply wpHP_noStep cpu _ c hfn
  intro rs d l h' d' hp
  obtain ⟨e, k, rfl⟩ := hm
  obtain ⟨_, hp⟩ := pstepV2_node hp
  simp only [hnodeStep] at hp

/-- A PAGE-WALK READ (translation on): vacuously safe — the hazard of a `kpt`-tier leaf. -/
theorem wpHP_walk (cpu : CPU) {n va : Nat}
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k : Result ((BitVec (8 * n)) × Option Bool) Unit → SailM Unit) (c : Core) (hfn : c.fn = none)
    (hd : devAddr req.pa = false) (ht : isTtw req.access_kind = true) :
    coreP (GF := GF) cpu c ⊢ wpHP (hlc := hlc) cpu (.impure (.ok (.memRead n va req)) k) := by
  apply wpHP_noStep cpu _ c hfn
  intro rs d l h' d' hp
  obtain ⟨_, hp⟩ := pstepV2_node hp
  simp only [hnodeStep, hd] at hp
  obtain ⟨_, hr⟩ := hp
  unfold ramRead at hr
  rw [ht] at hr
  exact Bool.false_ne_true hr.1.symm

end swp

end Weak.Prom.HL
