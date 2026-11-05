/-
Weak/Prom: **S5a — the hart lift** (plan rev 7 `~/dev/weak-orch/promising/plan.md` §7 "Leaf interface the new logic
must supply": `wpHartP_lift`, "the statement shape of `wpHart_lift` (Wp.lean:432–435), with `machInterp` replaced by
the Prom state interpretation"; §8 S5 first item; owner ruling [OWN.P14]: S5 builds on track (a)).

Track (a)'s concurrent wp `wpA` (OwnAWp.lean) is generic in the program half.  This file instantiates it with the
REAL Sail emission of machine v2 (Emit.lean `pstepV2`: one hart step per Sail event, the hart's state `HState` =
residual Sail monad, register file, parked FENCE.TSO half, per-instruction channel `Ix`) and gives it MachCSL's
hart-level surface:

* `wpHP cpu m` — the hart wp at residual `m` (MachCSL `wpHart cpu m`, Wp.lean:157): the register file and the
  channel are ghost-owned (`regAuth` / `chanAuth`, one half each), so the wp is indexed by `m` only, as MachCSL's.
  `wpLoopP cpu := wpHP cpu (pure ())` (MachCSL `wpLoop`).
* `coreP cpu c` — the hart's CORE: the other half of the channel and track (a)'s `hartA` (exact views, promise set,
  trace).  MachCSL keeps its views in `machInterp`; here they are a client resource, so a memory leaf (S5b) knows
  the exact pre-state of its event (plan §7: "`kctx` must absorb `hartSt`'s register views").
* `regP cpu r dq v` — register points-to (MachCSL `r ↦ᵣ[cpu]{dq} v`, Resources.lean:563–574: the SAME construction,
  `ghost_map_elem` at `regIdx r` of a per-hart register map).  NA-15 option (ii): the seam needs only these
  functors and names (`PromEnv`), not `MachGS`.
* `wpHP_lift` — THE LIFTING LEMMA (MachCSL `wpHart_lift`): one `▷` and `£ 1` per Sail event; the callback is
  handed the register file, the label/next state the emission allows, the machine-v2 memory step, track (a)'s
  pre-state facts and frontier, and returns the step's obligations (`stepOk`, `fulT` at a fulfil).  Proved from
  `wpA_lift` only.
* `wpHP_liftQ` — the lifting lemma for QUIET labels (`quietLab`: no message, no view read: `LSilent`, `LRegW`,
  `LCtrl`, `LInstr`, `LFence`, `LFenceI`, `LExFail`): the obligations are discharged once here (`memStep_q`,
  `stepOk_q`; the trace invariant must be stable under quiet labels, `PromEnv.ψq`).

Inversions of `pstepV2` at each event head (§4) feed the per-event rules of HartSwp.lean.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.Emit
import Weak.Prom.OwnAAdeq
import MachCSL.Resources
import Iris.Instances.Lib.GhostMap

namespace Weak.Prom.HL

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc depsCtrl ibOfBvn eregNum ebarPark)
open Weak.Prom Weak.Prom.PF Weak.Prom.OA
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D

/-! ## 1. Quiet labels -/

/-- The hart's per-instruction channel together with its parked FENCE.TSO half (the non-register part of
`HState`). -/
abbrev Chan : Type := Option (Bool × Bool × Bool × Bool) × Ix

/-- QUIET labels: machine v2 steps them with no message (`ots = none`), no promise consumed, and no read of memory
(Machine.lean `memStep`: `silent`, `regW`, `ctrl`, `instr`, `fence`, `fenceI`, `scFail`). -/
def quietLab : PLabel → Bool
  | LSilent => true
  | LRegW _ _ => true
  | LCtrl _ => true
  | LInstr => true
  | LFence _ _ _ _ => true
  | LFenceI => true
  | LExFail => true
  | _ => false

/-- A quiet label's memory step fulfils nothing and keeps the promise set. -/
theorem memStep_q {img : Image} {log : List PMsg} {i : Nat} {prom : GSet Nat} {ws : PState} {l : PLabel}
    {ots : Option Nat} {ws' : PState} {prom' : GSet Nat} (hq : quietLab l = true)
    (h : memStep img log i prom ws l ots ws' prom') : ots = none ∧ prom' = prom := by
  cases h <;> simp_all [quietLab]

/-- A quiet step's obligation (`stepOk`) from the pre-state facts, for a trace invariant stable under it. -/
theorem stepOk_q {π : Proto} {img : Image} {M : List PMsg} {Ψ : Trace → Prop} {ws : PState} {pr : GSet Nat}
    {τ : Trace} {l : PLabel} (hst : Ψ τ → Ψ (τ ++ [(l, none)]))
    (hf : hartFacts π img M Ψ (ws, pr, τ)) : stepOk π img M Ψ ws τ l none := by
  obtain ⟨⟨V, hV⟩, _⟩ := hf
  exact ⟨⟨V, fun hv => hst (hV hv)⟩, fun t ht => by cases ht⟩

/-! ## 2. The ambient environment and the resources -/

/-- THE AMBIENT ENVIRONMENT of the hart lift (the analogue of `MachGS`'s ambient era): track (a)'s ghost names and
parameters (`g`, `π`, the image, the final memory `M`, the trace invariant `Ψ`), the per-hart register-map and
channel ghost names.  `ψq`: the trace invariant is stable under quiet labels (true for `Ψ = True`; a litmus `Ψ`
records memory events only). -/
class PromEnv where
  g : AGN
  π : Proto
  img : Image
  M : List PMsg
  Ψ : Nat → Trace → Prop
  ψq : ∀ h τ l, quietLab l = true → Ψ h τ → Ψ h (τ ++ [(l, none)])
  rn : CPU → GName
  cn : CPU → GName

section res

variable {GF : BundledGFunctors} [GhostMapG GF Nat RegVal RegMapF]

/-- A register file's interpretation at register map `γ` (MachCSL `regInterpAt`, Resources.lean:589). -/
def regAuthAt (γ : GName) (f : RegFile) : IProp GF :=
  iprop(∃ m : RegMapF RegVal, (γ ↪●MAP m) ∗ ⌜regAgree m f⌝)

/-- Register `r` of the map `γ` holds `v` (MachCSL `regPointsToAt`, Resources.lean:563). -/
def regPtAt (γ : GName) (r : Register) (dq : DFrac) (v : RegisterType r) : IProp GF :=
  ghost_map_elem γ dq (regIdx r) (⟨r, v⟩ : RegVal)

/-- Reading: a register cell pins the file's value (MachCSL `reg_valid_at`, Resources.lean:4296). -/
theorem regAuthAt_valid (γ : GName) (f : RegFile) (r : Register) (dq : DFrac) (v : RegisterType r) :
    regAuthAt γ f ∗ regPtAt γ r dq v ⊢@{IProp GF} ⌜f r = v⌝ := by
  unfold regAuthAt regPtAt
  iintro ⟨⟨%m, Hauth, %Hag⟩, Hr⟩
  ihave %Hlook := ghost_map_lookup $$ Hauth Hr
  ipureintro
  have := Hag r
  rw [Hlook] at this
  exact (regVal_inj (Option.some.inj this)).symm

/-- Writing: a full cell is updated together with the file (MachCSL `reg_update_at`, Resources.lean:4307). -/
theorem regAuthAt_update (γ : GName) (f : RegFile) (r : Register) (v w : RegisterType r) :
    regAuthAt γ f ∗ regPtAt γ r (DFrac.own 1) v ⊢@{IProp GF}
      |==> (regAuthAt γ (f.set r w) ∗ regPtAt γ r (DFrac.own 1) w) := by
  unfold regAuthAt regPtAt
  iintro ⟨⟨%m, Hauth, %Hag⟩, Hr⟩
  imod ghost_map_update (⟨r, w⟩ : RegVal) $$ Hauth Hr with ⟨Hauth, Hr⟩
  imodintro
  iframe Hr
  iexists _
  iframe Hauth
  ipureintro
  intro r'
  by_cases h : r' = r
  · subst h
    simp [LawfulPartialMap.get?_insert_eq]
  · rw [LawfulPartialMap.get?_insert_ne (fun h' => h (regIdx_injective h').symm)]
    rw [Hag r', RegFile.set_other _ _ _ _ h]

variable [GhostVarG GF Chan] [E : PromEnv]

/-- Hart `cpu`'s register `r` holds `v` (MachCSL `r ↦ᵣ[cpu]{dq} v`). -/
def regP (cpu : CPU) (r : Register) (dq : DFrac) (v : RegisterType r) : IProp GF := regPtAt (E.rn cpu) r dq v

instance (cpu : CPU) (r : Register) (v : RegisterType r) : Persistent (regP (GF := GF) cpu r DFrac.discard v) := by
  unfold regP regPtAt; infer_instance

/-- Hart `cpu`'s register file (the wp's half; MachCSL `regInterp cpu f`). -/
def regAuth (cpu : CPU) (f : RegFile) : IProp GF := regAuthAt (E.rn cpu) f

/-- The wp's half of hart `cpu`'s channel. -/
def chanAuth (cpu : CPU) (c : Chan) : IProp GF := ghost_var (E.cn cpu) (.own (1 : Qp).half) c

/-- THE PROGRAM COUNTER at a cycle boundary (MachCSL `pcIs`, Boot.lean:20: `PC` and `nextPC` agree). -/
def pcIsP (cpu : CPU) (pc : BitVec 64) : IProp GF :=
  iprop(regP cpu Register.PC (DFrac.own 1) pc ∗ regP cpu Register.nextPC (DFrac.own 1) pc)

theorem regP_valid (cpu : CPU) (f : RegFile) (r : Register) (dq : DFrac) (v : RegisterType r) :
    regAuth (GF := GF) cpu f ∗ regP cpu r dq v ⊢ ⌜f r = v⌝ := regAuthAt_valid _ f r dq v

theorem regP_update (cpu : CPU) (f : RegFile) (r : Register) (v w : RegisterType r) :
    regAuth (GF := GF) cpu f ∗ regP cpu r (DFrac.own 1) v ⊢
      |==> (regAuth cpu (f.set r w) ∗ regP cpu r (DFrac.own 1) w) := regAuthAt_update _ f r v w

end res

/-- THE HART'S CORE: parked fence half, channel, and track (a)'s exact state (views, promise set, trace). -/
structure Core where
  fn : Option (Bool × Bool × Bool × Bool)
  ix : Ix
  ws : PState
  pr : GSet Nat
  τ : Trace

section core

variable {GF : BundledGFunctors} [GhostVarG GF Chan] [GhostVarG GF HSt] [GhostVarG GF Bool] [E : PromEnv]

/-- THE CORE RESOURCE of hart `cpu` (the client's half of the channel ∗ track (a)'s `hartA`). -/
def coreP (cpu : CPU) (c : Core) : IProp GF :=
  iprop(ghost_var (E.cn cpu) (.own (1 : Qp).half) ((c.fn, c.ix) : Chan) ∗ hartA E.g cpu.val c.ws c.pr c.τ)

/-- The core after a QUIET step with label `l`: same promises, the trace extended, the views as machine v2's
`memStep` moves them (no message). -/
def qStep (cpu : CPU) (c : Core) (l : PLabel) (c' : Core) : Prop :=
  c'.pr = c.pr ∧ c'.τ = c.τ ++ [(l, none)] ∧ memStep E.img E.M cpu.val c.pr c.ws l none c'.ws c.pr

end core

/-! ## 3. The hart wp and its lifting lemma -/

section wp

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostMapG GF Nat RegVal RegMapF] [GhostVarG GF Chan]
  [GhostVarG GF HSt] [GhostVarG GF Bool] [InvGS_gen hlc GF] [E : PromEnv]

/-- Hart `cpu`'s world: emission v2's program step, no value (a hart runs forever, as MachCSL's), the image, the
final memory, the hart index `cpu.val`. -/
abbrev hwS (cpu : CPU) : HW HState DevStates Empty := ⟨pstepV2, fun _ => none, E.img, E.M, cpu.val⟩

theorem hwS_eq (cpu : CPU) : hwS cpu = hw pstepV2 (fun _ => none) E.img E.M cpu.val := rfl

/-- **THE HART WP** at residual `m` (MachCSL `wpHart cpu m`): for the register file and channel the ghost halves
pin, track (a)'s wp of hart `cpu`'s thread at the machine-v2 state `⟨cpu, m, rs, fn, ix⟩`. -/
def wpHP (cpu : CPU) (m : SailM Unit) : IProp GF :=
  iprop(∀ (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool)) (ix : Ix),
    regAuth cpu rs -∗ chanAuth cpu (fn, ix) -∗
    wpA (hlc := hlc) E.g E.π (hwS cpu) E.Ψ (⟨cpu, m, rs, fn, ix⟩ : HState) (fun _ => iprop(True)))

/-- The cycle boundary (MachCSL `wpLoop cpu := wpHart cpu (pure ())`). -/
def wpLoopP (cpu : CPU) : IProp GF := wpHP (hlc := hlc) cpu (.pure ())

/-- A state is its fields (the CPU is fixed by `pstepV2`). -/
theorem hstate_eta (h : HState) (cpu : CPU) (hc : h.cpu = cpu) : h = ⟨cpu, h.m, h.rs, h.fn, h.ix⟩ := by
  cases h; simp only at hc; subst hc; rfl

/-- **THE LIFTING LEMMA** (plan §7 `wpHartP_lift`; MachCSL `wpHart_lift`, Wp.lean:432): from the core, the hart may
take any step emission v2 and machine v2 allow; one `▷` for the step, `£ 1` for the continuation.  The callback is
handed the register file (`regAuth`), the label `l`, the timestamp `ots`, the successor `h'`, the memory step, the
pre-state facts (or doom) and THE FRONTIER RULE at the pre-state; it returns the step's obligation (or doom),
`fulT` for a fulfil, the register file of `h'`, and the continuation from the new core. -/
theorem wpHP_lift (cpu : CPU) (m : SailM Unit) (c : Core) :
    coreP cpu c ∗
    (∀ rs, regAuth cpu rs -∗ ▷ ∀ (l : PLabel) (ots : Option Nat) (h' : HState) (ws' : PState) (pr' : GSet Nat),
      ⌜anyFab pstepV2 (⟨cpu, m, rs, c.fn, c.ix⟩ : HState) () l h' ()⌝ -∗
      ⌜memStep E.img E.M cpu.val c.pr c.ws l ots ws' pr'⌝ -∗
      (⌜hartFacts E.π E.img E.M (E.Ψ cpu.val) (c.ws, c.pr, c.τ)⌝ ∨ dshot E.g) -∗
      frontA E.g E.π E.img E.M c.ws -∗ (£ 1 : IProp GF) -∗
      |={⊤}=> (⌜stepOk E.π E.img E.M (E.Ψ cpu.val) c.ws c.τ l ots⌝ ∨ dshot E.g) ∗
        (∀ t, ⌜ots = some t⌝ → fulT E.g t) ∗ regAuth cpu h'.rs ∗
        (coreP cpu ⟨h'.fn, h'.ix, ws', pr', c.τ ++ [(l, ots)]⟩ -∗ wpHP (hlc := hlc) cpu h'.m))
    ⊢ wpHP (hlc := hlc) cpu m := by
  iintro ⟨Hc, H⟩
  unfold coreP
  icases Hc with ⟨Hch, Hst⟩
  unfold wpHP
  iintro %rs %fn %ix Hr Hca
  unfold chanAuth
  ihave %Heq := ghost_var_agree _ _ _ _ _ $$ Hca Hch
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨h1, h2⟩ := Heq
  subst h1 h2
  ispecialize H $$ %rs Hr
  iapply wpA_lift (w := hwS cpu) (ws := c.ws) (pr := c.pr) (τ := c.τ)
  isplitl [Hst]
  · iexact Hst
  inext
  isplit
  · iintro %v %_
    exact v.elim
  · iintro %l %ots %s' %ws' %pr' %hp %hm Hf Hfr Hc
    imod H $$ %l %ots %s' %ws' %pr' %hp %hm Hf Hfr Hc with ⟨Hok, Hfu, Hr', Hk⟩
    imod ghost_var_update_halves ((s'.fn, s'.ix) : Chan) _ _ _ $$ Hca Hch with ⟨Hca, Hch⟩
    imodintro
    iframe Hok Hfu
    iintro Hst'
    have hcpu : s'.cpu = cpu := by
      obtain ⟨d, d', hps⟩ := hp
      exact hps.1
    rw [hstate_eta s' cpu hcpu]
    iapply Hk $$ [Hch Hst'] %s'.rs %s'.fn %s'.ix Hr' Hca
    isplitl [Hch]
    · iexact Hch
    · iexact Hst'

/-- **THE QUIET LIFTING LEMMA**: when every step emission v2 allows is quiet (`quietLab`), the obligations are
discharged here (no fulfil; `stepOk` by `PromEnv.ψq`, or doom), and the callback only re-establishes the register
file and continues from the new core (same promises, the trace extended, the views as `memStep` moves them). -/
theorem wpHP_liftQ (cpu : CPU) (m : SailM Unit) (c : Core)
    (hq : ∀ rs l h', anyFab pstepV2 (⟨cpu, m, rs, c.fn, c.ix⟩ : HState) () l h' () → quietLab l = true) :
    coreP cpu c ∗
    (∀ rs, regAuth cpu rs -∗ ▷ ∀ (l : PLabel) (h' : HState) (ws' : PState),
      ⌜anyFab pstepV2 (⟨cpu, m, rs, c.fn, c.ix⟩ : HState) () l h' ()⌝ -∗
      ⌜memStep E.img E.M cpu.val c.pr c.ws l none ws' c.pr⌝ -∗ (£ 1 : IProp GF) -∗
      |={⊤}=> regAuth cpu h'.rs ∗
        (coreP cpu ⟨h'.fn, h'.ix, ws', c.pr, c.τ ++ [(l, none)]⟩ -∗ wpHP (hlc := hlc) cpu h'.m))
    ⊢ wpHP (hlc := hlc) cpu m := by
  iintro ⟨Hc, H⟩
  iapply wpHP_lift cpu m c
  iframe Hc
  iintro %rs Hr
  ispecialize H $$ %rs Hr
  inext
  iintro %l %ots %h' %ws' %pr' %hp %hm Hf _ Hcr
  have hql := hq rs l h' hp
  obtain ⟨h1, h2⟩ := memStep_q hql hm
  subst h1 h2
  imod H $$ %l %h' %ws' %hp %hm Hcr with ⟨Hr, Hk⟩
  imodintro
  isplitl [Hf]
  · icases Hf with (%Hf | #Hd)
    · ileft; ipureintro
      exact stepOk_q (E.ψq cpu.val c.τ l hql) Hf
    · iright; iexact Hd
  isplitr
  · iintro %t %ht
    cases ht
  iframe Hr Hk

end wp

/-! ## 4. Inversions of emission v2 at each event head (pure) -/

/-- The label of a register read (FIX S0rest-F1: the first read of a Zicsr read-modify-write's CSR captures the old
CSR view into `csrOldKey`; every other read is silent). -/
def rdLab (ix : Ix) (r : Register) : PLabel :=
  match csrCapture ix r with
  | some n => LRegW csrOldKey [.DReg n]
  | none => LSilent

/-- The channel after a register read. -/
def rdIx (ix : Ix) (r : Register) : Ix :=
  match csrCapture ix r with
  | some _ => { ix with csrOld := true }
  | none => ix

/-- The label of a register write (M19, FC-4): `nextPC` ↦ the syntactic control label, a tracked register ↦
`LRegW` with its sources, any other register ↦ `LSilent`. -/
def wrLab (ix : Ix) (r : Register) : PLabel :=
  if r = .nextPC then LCtrl (depsCtrl (v2Roles ix.bits))
  else match eregNum r with
    | some num => LRegW num (regSrcs ix.bits ix.scOk num)
    | none => LSilent

/-- The channel after a register write (FC-5: a write of `mcause`/`scause` marks the trap). -/
def wrIx (ix : Ix) (r : Register) : Ix :=
  { ix with trapped := ix.trapped || decide (r = .mcause ∨ r = .scause) }

theorem rdLab_q (ix : Ix) (r : Register) : quietLab (rdLab ix r) = true := by
  unfold rdLab; split <;> rfl

theorem wrLab_q (ix : Ix) (r : Register) : quietLab (wrLab ix r) = true := by
  unfold wrLab; split
  · rfl
  · split <;> rfl

theorem barLabel_q (b : barrier_kind) : quietLab (barLabel b) = true := by
  unfold barLabel; split
  · rfl
  · split <;> rfl

section inv

variable {cpu : CPU} {rs : RegFile} {ix : Ix} {d d' : DevStates} {l : PLabel} {h' : HState}

/-- With no parked fence half, the hart step is the node dispatch. -/
theorem pstepV2_node {m : SailM Unit} (h : pstepV2 ⟨cpu, m, rs, none, ix⟩ d l h' d') :
    h'.cpu = cpu ∧ hnodeStep ⟨cpu, m, rs, none, ix⟩ d l h' d' := h

/-- THE PARKED FENCE HALF (M6): with `fn = some f`, the only step is `LFence f`, nothing else changes. -/
theorem pstepV2_park {m : SailM Unit} {f : Bool × Bool × Bool × Bool}
    (h : pstepV2 ⟨cpu, m, rs, some f, ix⟩ d l h' d') :
    l = LFence f.1 f.2.1 f.2.2.1 f.2.2.2 ∧ h' = ⟨cpu, m, rs, none, ix⟩ := by
  obtain ⟨_, h⟩ := h
  obtain ⟨p1, p2, p3, p4⟩ := f
  simp only [hstep] at h
  obtain ⟨h1, _, h3⟩ := h
  exact ⟨h1, h3⟩

theorem pstepV2_regRead {r : Register} {k : RegisterType r → SailM Unit}
    (h : pstepV2 ⟨cpu, .impure (.ok (.regRead r)) k, rs, none, ix⟩ d l h' d') :
    l = rdLab ix r ∧ h' = ⟨cpu, k (rs r), rs, none, rdIx ix r⟩ := by
  obtain ⟨_, h⟩ := pstepV2_node h
  simp only [hnodeStep] at h
  obtain ⟨_, h⟩ := h
  unfold rdLab rdIx
  split at h
  · rename_i n hn
    rw [hn]
    obtain ⟨h1, h2⟩ := h
    exact ⟨h1, h2⟩
  · rename_i hn
    rw [hn]
    obtain ⟨h1, h2⟩ := h
    exact ⟨h1, h2⟩

theorem pstepV2_regWrite {r : Register} {v : RegisterType r} {k : PUnit → SailM Unit}
    (h : pstepV2 ⟨cpu, .impure (.ok (.regWrite r v)) k, rs, none, ix⟩ d l h' d') :
    l = wrLab ix r ∧ h' = ⟨cpu, k PUnit.unit, rs.set r v, none, wrIx ix r⟩ := by
  obtain ⟨_, h⟩ := pstepV2_node h
  simp only [hnodeStep] at h
  obtain ⟨_, h2, h3⟩ := h
  refine ⟨?_, h2⟩
  unfold wrLab
  split at h3
  · rename_i hr; rw [if_pos hr]; exact h3
  · rename_i hr; rw [if_neg hr]
    split at h3
    · rename_i num hn; rw [hn]; exact h3
    · rename_i hn; rw [hn]; exact h3

/-- A silent event of the dispatch (the announces and markers): `LSilent`, the continuation at `()`. -/
theorem pstepV2_instrAnnounce {n : Nat} {w : BitVec n} {k : Unit → SailM Unit}
    (h : pstepV2 ⟨cpu, .impure (.ok (.instrAnnounce n w)) k, rs, none, ix⟩ d l h' d') :
    l = LSilent ∧ h' = ⟨cpu, k (), rs, none, { ix with bits := some (ibOfBvn w) }⟩ := by
  obtain ⟨_, h⟩ := pstepV2_node h
  simp only [hnodeStep] at h
  exact ⟨h.1, h.2.2⟩

theorem pstepV2_branchAnnounce {n : Nat} {a : BitVec n} {k : Unit → SailM Unit}
    (h : pstepV2 ⟨cpu, .impure (.ok (.branchAnnounce n a)) k, rs, none, ix⟩ d l h' d') :
    l = LSilent ∧ h' = ⟨cpu, k (), rs, none, ix⟩ := by
  obtain ⟨_, h⟩ := pstepV2_node h
  simp only [hnodeStep] at h
  exact ⟨h.1, h.2.2⟩

theorem pstepV2_cycleCount {k : Unit → SailM Unit}
    (h : pstepV2 ⟨cpu, .impure (.ok .cycleCount) k, rs, none, ix⟩ d l h' d') :
    l = LSilent ∧ h' = ⟨cpu, k (), rs, none, ix⟩ := by
  obtain ⟨_, h⟩ := pstepV2_node h
  simp only [hnodeStep] at h
  exact ⟨h.1, h.2.2⟩

theorem pstepV2_message {s : String} {k : Unit → SailM Unit}
    (h : pstepV2 ⟨cpu, .impure (.ok (.message s)) k, rs, none, ix⟩ d l h' d') :
    l = LSilent ∧ h' = ⟨cpu, k (), rs, none, ix⟩ := by
  obtain ⟨_, h⟩ := pstepV2_node h
  simp only [hnodeStep] at h
  exact ⟨h.1, h.2.2⟩

/-- [OWN.P1] C-S constant row: the cycle counter answers ANY value (MachCSL: `0`). -/
theorem pstepV2_getCycleCount {k : Nat → SailM Unit}
    (h : pstepV2 ⟨cpu, .impure (.ok .getCycleCount) k, rs, none, ix⟩ d l h' d') :
    l = LSilent ∧ ∃ c : Nat, h' = ⟨cpu, k c, rs, none, ix⟩ := by
  obtain ⟨_, h⟩ := pstepV2_node h
  simp only [hnodeStep] at h
  obtain ⟨c, h1, _, h3⟩ := h
  exact ⟨h1, c, h3⟩

theorem pstepV2_choose {p : Sail.Primitive} {k : p.reflect → SailM Unit}
    (h : pstepV2 ⟨cpu, .impure (.ok (.choose p)) k, rs, none, ix⟩ d l h' d') :
    l = LSilent ∧ ∃ ch, h' = ⟨cpu, k ch, rs, none, ix⟩ := by
  obtain ⟨_, h⟩ := pstepV2_node h
  simp only [hnodeStep] at h
  obtain ⟨ch, h1, _, h3⟩ := h
  exact ⟨h1, ch, h3⟩

/-- A barrier: its applied-now label (M6), the FENCE.TSO second half parked. -/
theorem pstepV2_barrier {b : barrier_kind} {k : Unit → SailM Unit}
    (h : pstepV2 ⟨cpu, .impure (.ok (.barrier b)) k, rs, none, ix⟩ d l h' d') :
    l = barLabel b ∧ h' = ⟨cpu, k (), rs, ebarPark b, ix⟩ := by
  obtain ⟨_, h⟩ := pstepV2_node h
  simp only [hnodeStep] at h
  exact ⟨h.1, h.2.2⟩

/-- THE BOUNDARY IS CLEAN: no end-of-instruction event is pending (the end-of-SC `LExFail`, the failed-`amocas`
write-back, the Zicbom operation; Emit.lean `bndStep`'s first three arms). -/
def bndClean (ix : Ix) : Prop :=
  (isSC ix.bits = false ∨ ix.trapped = true ∨ ix.scEnd = true) ∧
  ((cboKind ix.bits).isNone = true ∨ ix.trapped = true ∨ ix.cmoDone = true) ∧
  (isAmocas ix.bits = false ∨ ix.amoRd = none ∨ ix.amoWr = true ∨ ix.wbDone = true ∨ ix.trapped = true)

/-- `ixNone` is clean. -/
theorem bndClean_none : bndClean ixNone := by
  refine ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

/-- AT A CLEAN BOUNDARY the only step is `LInstr` to the next `riscvStep tick` (any `tick`), the channel reset. -/
theorem pstepV2_bnd {u : Unit} (hc : bndClean ix)
    (h : pstepV2 ⟨cpu, .pure u, rs, none, ix⟩ d l h' d') :
    l = LInstr ∧ ∃ tick : Bool, h' = ⟨cpu, riscvStep tick, rs, none, ixNone⟩ := by
  obtain ⟨_, h⟩ := pstepV2_node h
  simp only [hnodeStep] at h
  obtain ⟨_, h⟩ := h
  obtain ⟨c1, c2, c3⟩ := hc
  unfold bndStep at h
  rcases h with ⟨h1, h2, h3, _⟩ | ⟨b, old, h1, h2, h3, h4, h5, _⟩ | ⟨kk, w, h1, h2, h3, h4, _⟩ | ⟨tick, _, _, h1, h2⟩
  · simp only at h1 h2 h3
    rcases c1 with c | c | c <;> simp_all
  · simp only at h1 h2 h3 h4 h5
    rcases c3 with c | c | c | c | c <;> simp_all
  · simp only at h1 h2 h3 h4
    rcases c2 with c | c | c <;> simp_all
  · exact ⟨h1, tick, h2⟩

end inv

end Weak.Prom.HL
