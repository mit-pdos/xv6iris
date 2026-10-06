/-
Weak: **DEPENDENCY-PROVENANCE SOUNDNESS** (B2e-3b, slices 2a/2b).

Rocq: `iris/WeakEvProv.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Design `claude-notes/design/weak-memory-route-b.md` §4e ("TWO SHAPES", DECIDED (ii) DYNAMIC
PROVENANCE).  The certification step claims that a SOLO RUN of the verified program emits a given
write with the graph's label whenever every read feeding it reads its true source — a
VALUE-DETERMINISM property of the emission.  Slice 2a's answer (DEC-7, `WeakEvLang`): the
emission's source lists are the per-instruction READ SET the machine accumulates in the channel
(`Ibch.ibRds`), appended to at every `regRead` of a carrier register and reset at the two
instruction boundaries.  Coverage holds by construction; what is left is the GENERIC determinism
fact proved here: two runs of the SAME Sail continuation from register files that agree on the
registers the run actually reads are IDENTICAL.

  (1) PER STEP: `pnodeStepDagree` (and its `regRead` case `pnodeStepRegreadAgree`).
  (2) PER SILENT STRETCH: `erunSilentDagree`, along `WeakEvLift.erunSilent`, with the stretch's
      read set (`erunRds`) as the footprint.
  (3) THE COVERAGE BRIDGE: `pnodeStepChannel` / `erunIbRds` — the channel's read set is exactly
      the carriers the stretch read (when it crosses no instruction boundary, `erunAnn`).

Slice 2b (§§6-10): the per-instruction lemma over a hart's `pstepEv` chain (`pevrun`), annotated
(`phrun`) with the carriers READ, the registers WRITTEN and the BOUNDARY flag:
  (A) `instrDagree` / `instrDagreeEv` — the LOCKSTEP half (existential in the second run: `choose`
      and the boundary's tick are invisible in the label, so equal labels do not pin equal runs);
  (B) `phrunFrame` / `taintClosure` / `taintClosureLoad` — the DIVERGENT half (the frame law: the
      taint set grows by exactly what the remainders wrote; a write to a NON-carrier, e.g. the PC,
      cannot be absorbed, `eregNum r = some n` is demanded).
§10 is the non-vacuity witness (reads `x15`, writes `x14`).

## Deviations from Rocq

1. NAMES / TYPES: camelCase; `M unit` ↦ `SailM Unit`; `regstate` ↦ `RegFile` (`register_lookup r
   rs` ↦ `rs r`, `register_set r v rs` ↦ `rs.set r v`); `dev_state` ↦ `DevStates` / `Efab` (deviation 7); `oib32` ↦
   `Ibch`; `wreg` ↦ `Nat`; `gset register` ↦ `List Register` (as `WeakEvLift.esilNode`);
   `default x o` ↦ `o.getD x`; `ereg_num` ↦ `eregNum`.  Lean's `RegRead` has no `dir` argument.
2. `obar` (WeakEvInst deviation 4): every program-half relation carries the executed barrier
   `obar`; `pstepHw` takes it as a final argument, `phrun.more` binds it (it is invisible to the
   annotations), and `pstepEv`'s existential `obar` is threaded through `pstepEvDagree` /
   `phrunPevrun` / `pevrunPhrun`.
3. Lean's `.impure (.error _)` node (stuck in `pnodeStep`): `pnodeRds`/`pnodeWrs` `[]`, `ibnStep`
   the identity, `ibnAnn` `false`.  The read set of `pnodeRds` is read off `.regRead r` exactly
   as Rocq.
4. THE PLIC WIRE (WeakEvInst deviation 5): Lean's wire sets EITHER pin (`pinSet rs mm b`), so the
   wire arm of `pstepHw` writes `plicWrs = [.sig_meip, .sig_seip]` (Rocq `[sig_seip]`), a sound
   over-approximation by one register.  ALL use of `pstepPlic`'s internals is isolated in three
   Lean-only lemmas, `pstepPlicDagree`, `pstepPlicWrs`, `pstepPlicOib` (so a change to the device
   arms is absorbed there).
5. PROOF SHAPE: the four per-node facts Rocq proves by four separate `destruct oc; repeat …`
   (`pnode_step_channel`, `pnode_step_ors`, `pnode_step_ann`, `pnode_step_store_det`) come from
   one Lean-only case analysis `pnodeStepFacts`; the store-determinism clause goes through the
   Lean-only `pnodeStoreLbl` (the store label as a function of the node and channel).
   Lean-only helpers: `dregAgreeGetD`, `wlIsStoreErw`, `wlIsStoreEbar`, `erwLabelNeInstr`.
6. Constructors `pevrun_nil/more` ↦ `pevrun.nil/more`, `phrun_nil/more` ↦ `phrun.nil/more`
   (the `more` binders implicit).  `Example instr_dagree_nonvacuous` ↦ `theorem`.
7. THE FABRIC TYPE (owner decision Q1; `WeakEvPf` deviation 9, `WeakEvInst` deviation 5): the
   instance's fabric is `Efab` (the device states plus the residual UART/PLIC programs), so
   `dev_state` ↦ `Efab` from §5 on (`pstepPlic*`, `pstepHart*`, `pstepEv*`, `pstepHw*`,
   `pevrun`, `phrun`, §§7–10); the `pnodeStep`-level lemmas keep `DevStates`.  `pstepHw`'s two
   node arms read `d.efDev` and add `d' = { d with efDev := d'.efDev }` (as `pstepHart`'s), and
   `pstepPlic` now carries the PLIC program's `setPin` node (`∃ mm b k, d.efPlic = …`): only the
   three isolated lemmas of deviation 4 and the node-arm patterns changed.

**File-qualified names:** none (no name of this file is in `notes/weak-port-dupnames.json`).

**Rocq → Lean name map.**  `pnode_rds` `pnodeRds`, `dreg_agree` `dregAgree`, `rds_ok` `rdsOk`,
`rds_ok_app` `rdsOkApp`, `dreg_agree_refl/sym/trans/mono/set/excl/read`
`dregAgreeRefl/Sym/Trans/Mono/Set/Excl/Read`, `pnode_rds_read` `pnodeRdsRead`,
`pnode_step_regread_agree` `pnodeStepRegreadAgree`, `pnode_step_dagree` `pnodeStepDagree`,
`ibn_step` `ibnStep`, `ibn_ann` `ibnAnn`, `pnode_step_channel` `pnodeStepChannel`, `ibn_step_rds`
`ibnStepRds`, `erun_rds` `erunRds`, `erun_ib` `erunIb`, `erun_ann` `erunAnn`, `esil_node_none`
`esilNodeNone`, `esil_node_dagree` `esilNodeDagree`, `erun_silent_dagree` `erunSilentDagree`,
`erun_ib_rds` `erunIbRds`, `erun_silent_dagree_channel` `erunSilentDagreeChannel`,
`pstep_hart_dagree` `pstepHartDagree`, `pstep_ev_dagree` `pstepEvDagree`, `pnode_wrs`
`pnodeWrs`, `pnode_step_ors` `pnodeStepOrs`, `pnode_step_ann` `pnodeStepAnn`, `pstep_hw`
`pstepHw`, `pstep_hw_hart` `pstepHwHart`, `pstep_hart_hw` `pstepHartHw`, `pstep_hw_ann`
`pstepHwAnn`, `pstep_hw_channel` `pstepHwChannel`, `pstep_hw_frame` `pstepHwFrame`,
`pstep_hw_dagree` `pstepHwDagree`, `pevrun` `pevrun`, `phrun` `phrun`, `phrun_pevrun`
`phrunPevrun`, `pevrun_phrun` `pevrunPhrun`, `phrun_ib_rds` `phrunIbRds`, `phrun_ann` `phrunAnn`,
`phrun_no_instr` `phrunNoInstr`, `phrun_dagree` `phrunDagree`, `instr_dagree` `instrDagree`,
`instr_dagree_ev` `instrDagreeEv`, `wl_is_store` `wlIsStore`, `pnode_step_store_det`
`pnodeStepStoreDet`, `phrun_frame` `phrunFrame`, `taint_closure` `taintClosure`,
`taint_closure_load` `taintClosureLoad`, `wit_m` `witM`, `wit_run` `witRun`,
`instr_dagree_nonvacuous` `instrDagreeNonvacuous`.  Lean-only: `plicWrs`, `pstepPlicDagree`,
`pstepPlicWrs`, `pstepPlicOib`, `pnodeStoreLbl`, `pnodeStepFacts`, and deviation 5's helpers.

**Dropped:** nothing.

**WeakEvInst device-arm dependencies:** `pstepPlic` and `pinSet` (only inside `pstepPlicDagree`,
`pstepPlicWrs`, `pstepPlicOib`); `pnodeStep`'s MMIO arms (`devRead`/`devWrite`) only through
"`ors = none`, `oib = none`, label `LDev`" inside `pnodeStepFacts`.  No disk/UART arm is used.
-/
import Weak.WeakEvInst
import Weak.WeakEvLift

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! ## 1. The footprint -/

/-- THE REGISTERS ONE NODE READS, as the channel records them. -/
def pnodeRds (m : SailM Unit) : List Nat :=
  match m with
  | .impure (.ok (.regRead r)) _ =>
      match eregNum r with
      | some n => [n]
      | none => []
  | _ => []

/-- AGREEMENT AT A READ SET: agreement on every non-carrier and on every carrier allowed by `P`. -/
def dregAgree (P : Nat → Prop) (rs1 rs2 : RegFile) : Prop :=
  ∀ r : Register, (∀ n : Nat, eregNum r = some n → P n) → rs1 r = rs2 r

/-- "every register this stretch read is allowed by `P`". -/
def rdsOk (P : Nat → Prop) (l : List Nat) : Prop :=
  ∀ n : Nat, n ∈ l → P n

theorem rdsOkApp (P : Nat → Prop) (l1 l2 : List Nat) :
    rdsOk P (l1 ++ l2) → rdsOk P l1 ∧ rdsOk P l2 := by
  intro h
  exact ⟨fun n hn => h n (List.mem_append_left _ hn), fun n hn => h n (List.mem_append_right _ hn)⟩

theorem dregAgreeRefl (P : Nat → Prop) (rs : RegFile) : dregAgree P rs rs :=
  fun _ _ => rfl

theorem dregAgreeSym (P : Nat → Prop) (rs1 rs2 : RegFile) :
    dregAgree P rs1 rs2 → dregAgree P rs2 rs1 :=
  fun h r hr => (h r hr).symm

theorem dregAgreeTrans (P : Nat → Prop) (rs1 rs2 rs3 : RegFile) :
    dregAgree P rs1 rs2 → dregAgree P rs2 rs3 → dregAgree P rs1 rs3 :=
  fun h1 h2 r hr => (h1 r hr).trans (h2 r hr)

theorem dregAgreeMono (P P' : Nat → Prop) (rs1 rs2 : RegFile) :
    (∀ n, P n → P' n) → dregAgree P' rs1 rs2 → dregAgree P rs1 rs2 :=
  fun hsub hag r hr => hag r (fun n hn => hsub n (hr n hn))

theorem dregAgreeSet (P : Nat → Prop) (rs1 rs2 : RegFile) (r : Register) (v : RegisterType r) :
    dregAgree P rs1 rs2 → dregAgree P (rs1.set r v) (rs2.set r v) := by
  intro hag r' hr'
  by_cases he : r' = r
  · subst he; simp only [RegFile.set_same]
  · rw [RegFile.set_other _ _ _ _ he, RegFile.set_other _ _ _ _ he]; exact hag r' hr'

theorem dregAgreeExcl (P : Nat → Prop) (rs : RegFile) (r : Register) (v : RegisterType r) :
    (∃ n, eregNum r = some n ∧ ¬ P n) → dregAgree P rs (rs.set r v) := by
  rintro ⟨n, hn, hP⟩ r' hr'
  by_cases he : r' = r
  · subst he; exact absurd (hr' n hn) hP
  · rw [RegFile.set_other _ _ _ _ he]

theorem dregAgreeRead (P : Nat → Prop) (rs1 rs2 : RegFile) (r : Register) :
    (∀ n : Nat, eregNum r = some n → P n) → dregAgree P rs1 rs2 → rs1 r = rs2 r :=
  fun hr hag => hag r hr

/-- Lean-only: an optional register update preserves agreement when both sides take it. -/
theorem dregAgreeGetD (P : Nat → Prop) (rs1 rs2 : RegFile) (o : Option RegFile) :
    dregAgree P rs1 rs2 → dregAgree P (o.getD rs1) (o.getD rs2) := by
  intro hag
  cases o with
  | none => exact hag
  | some x => exact dregAgreeRefl P x

theorem pnodeRdsRead (r : Register) (k) (P : Nat → Prop) (n : Nat) :
    rdsOk P (pnodeRds (.impure (.ok (.regRead r)) k)) → eregNum r = some n → P n := by
  intro hsub hn
  apply hsub
  simp [pnodeRds, hn]

/-! ## 2. PER STEP -/

theorem pnodeStepRegreadAgree (r : Register) (k) (rs1 rs2 : RegFile) (ib : Ibch) (d : DevStates)
    (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    rs1 r = rs2 r →
    pnodeStep (.impure (.ok (.regRead r)) k) rs1 ib d l m' ors fn' d' oib obar →
    pnodeStep (.impure (.ok (.regRead r)) k) rs2 ib d l m' ors fn' d' oib obar := by
  intro hlk h
  obtain ⟨h1, rfl, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, by rw [hlk], h3, h4, h5, h6, h7⟩

theorem pnodeStepDagree (P : Nat → Prop) (m : SailM Unit) (rs1 rs2 : RegFile) (ib : Ibch)
    (d : DevStates) (l : Wlabel) (m' : SailM Unit) (ors1 : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    rdsOk P (pnodeRds m) → dregAgree P rs1 rs2 →
    pnodeStep m rs1 ib d l m' ors1 fn' d' oib obar →
    ∃ ors2 : Option RegFile,
      pnodeStep m rs2 ib d l m' ors2 fn' d' oib obar ∧
      dregAgree P (ors1.getD rs1) (ors2.getD rs2) := by
  intro hsub hag h
  match m, h with
  | .pure _, h => exact ⟨ors1, h, dregAgreeGetD P rs1 rs2 ors1 hag⟩
  | .impure (.error _) _, h => exact h.elim
  | .impure (.ok o) k, h =>
    cases o with
    | regRead r =>
      have hlk : rs1 r = rs2 r := hag r (fun n hn => pnodeRdsRead r k P n hsub hn)
      exact ⟨ors1, pnodeStepRegreadAgree r k rs1 rs2 ib d l m' ors1 fn' d' oib obar hlk h,
        dregAgreeGetD P rs1 rs2 ors1 hag⟩
    | regWrite r v =>
      obtain ⟨h1, h2, rfl, h4, h5, h6, h7⟩ := h
      exact ⟨some (rs2.set r v), ⟨h1, h2, rfl, h4, h5, h6, h7⟩, dregAgreeSet P rs1 rs2 r v hag⟩
    | _ => exact ⟨ors1, h, dregAgreeGetD P rs1 rs2 ors1 hag⟩

/-! ## 3. THE COVERAGE BRIDGE -/

/-- The channel's move at one node, as a FUNCTION of the node. -/
def ibnStep (m : SailM Unit) (ib : Ibch) : Ibch :=
  match m with
  | .pure _ => ibNone
  | .impure (.ok (.regRead r)) _ => ibRd ib r
  | .impure (.ok (.instrAnnounce _ w)) _ => ibAnn (ibOfBvn w)
  | _ => ib

/-- Whether the node is an INSTRUCTION BOUNDARY. -/
def ibnAnn (m : SailM Unit) : Bool :=
  match m with
  | .pure _ => true
  | .impure (.ok (.instrAnnounce _ _)) _ => true
  | _ => false

/-- THE REGISTERS ONE NODE WRITES (Rocq §6; placed here for `pnodeStepFacts`). -/
def pnodeWrs (m : SailM Unit) : List Register :=
  match m with
  | .impure (.ok (.regWrite r _)) _ => [r]
  | _ => []

/-- Rocq §8's store predicate (placed here for `pnodeStepFacts`). -/
def wlIsStore (l : Wlabel) : Bool :=
  match l with
  | LStore .. | LExStore .. => true
  | _ => false

/-- Lean-only (deviation 5): the store label a `memWrite` node emits, a function of the node and
the channel. -/
def pnodeStoreLbl (m : SailM Unit) (ib : Ibch) : Wlabel :=
  match m with
  | .impure (.ok (.memWrite n _ req)) _ =>
      match req.value with
      | some v =>
          if (classify req.access_kind).akLatest then
            LExStore (classify req.access_kind).akSync (paZ req.pa) (WeakInterpProj.wbytes n v)
              (depsAsrc (depsOfIb ib.ibBits)) (depsVsrc (depsOfIb ib.ibBits))
          else
            LStore (classify req.access_kind).akSync (paZ req.pa) (WeakInterpProj.wbytes n v)
              (depsAsrc (depsOfIb ib.ibBits)) (depsVsrc (depsOfIb ib.ibBits))
      | none => LSilent
  | _ => LSilent

theorem wlIsStoreErw (w : ErwKind) : wlIsStore (erwLabel w) = false := by
  cases w <;> rfl

theorem wlIsStoreEbar (b : barrier_kind) : wlIsStore (ebarLabel b) = false := by
  obtain ⟨_, _, _, _, h⟩ := ebarLabelFence b
  rw [h]; rfl

theorem erwLabelNeInstr (w : ErwKind) : erwLabel w ≠ LInstr := by
  cases w <;> nofun

/-- Lean-only (deviation 5): the four per-node facts, from one case analysis. -/
theorem pnodeStepFacts (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : DevStates) (oib : Option Ibch) (obar : Option barrier_kind) :
    pnodeStep m rs ib d l m' ors fn' d' oib obar →
    oib.getD ib = ibnStep m ib ∧
    (ors = none ∨ ∃ (r : Register) (v : RegisterType r), r ∈ pnodeWrs m ∧ ors = some (rs.set r v)) ∧
    (ibnAnn m = true → l = LInstr) ∧
    (wlIsStore l = true → l = pnodeStoreLbl m ib) := by
  intro h
  match m, h with
  | .pure _, h =>
    obtain ⟨_, rfl, _, rfl, _, _, rfl, _⟩ := h
    exact ⟨rfl, Or.inl rfl, fun _ => rfl, fun h => by simp [wlIsStore] at h⟩
  | .impure (.error _) _, h => exact h.elim
  | .impure (.ok o) k, h =>
    cases o with
    | regRead r =>
      obtain ⟨rfl, _, rfl, _, _, rfl, _⟩ := h
      exact ⟨rfl, Or.inl rfl, fun h => by simp [ibnAnn] at h, fun h => by simp [wlIsStore] at h⟩
    | regWrite r v =>
      obtain ⟨rfl, _, rfl, _, _, rfl, _⟩ := h
      refine ⟨rfl, Or.inr ⟨r, v, by simp [pnodeWrs], rfl⟩, fun h => by simp [ibnAnn] at h,
        fun h => ?_⟩
      rw [wlIsStoreErw] at h; cases h
    | memRead n va req =>
      simp only [pnodeStep] at h
      split at h
      · obtain ⟨_, _, rfl, _, rfl, _, rfl, _⟩ := h
        exact ⟨rfl, Or.inl rfl, fun h => by simp [ibnAnn] at h, fun h => by simp [wlIsStore] at h⟩
      · rcases h with ⟨_, _, _, _, _, rfl, _, rfl, _, _, rfl, _⟩ |
          ⟨_, ⟨_, _, _, _, _, rfl, _, rfl, _, _, rfl, _⟩ | ⟨_, _, _, _, _, rfl, _, rfl, _, _, rfl, _⟩⟩
        all_goals
          exact ⟨rfl, Or.inl rfl, fun h => by simp [ibnAnn] at h,
            fun h => by simp [wlIsStore] at h⟩
    | memWrite n va req =>
      simp only [pnodeStep] at h
      split at h
      · split at h
        · obtain ⟨_, rfl, _, rfl, _, rfl, _⟩ := h
          exact ⟨rfl, Or.inl rfl, fun h => by simp [ibnAnn] at h,
            fun h => by simp [wlIsStore] at h⟩
        · exact h.elim
      · split at h
        · rename_i v hv
          rcases h with ⟨_, ⟨hlat, rfl, _, rfl, _, _, rfl, _⟩ |
            ⟨hlat, ⟨rfl, _, rfl, _, _, rfl, _⟩ | ⟨rfl, _, rfl, _, _, rfl, _⟩⟩⟩
          · exact ⟨rfl, Or.inl rfl, fun h => by simp [ibnAnn] at h,
              fun _ => by simp [pnodeStoreLbl, hv, hlat]⟩
          · exact ⟨rfl, Or.inl rfl, fun h => by simp [ibnAnn] at h,
              fun _ => by simp [pnodeStoreLbl, hv, hlat]⟩
          · exact ⟨rfl, Or.inl rfl, fun h => by simp [ibnAnn] at h,
              fun h => by simp [wlIsStore] at h⟩
        · exact h.elim
    | readRam => exact h.elim
    | writeRam => exact h.elim
    | barrier b =>
      obtain ⟨rfl, _, rfl, _, _, rfl, _⟩ := h
      refine ⟨rfl, Or.inl rfl, fun h => by simp [ibnAnn] at h, fun h => ?_⟩
      rw [wlIsStoreEbar] at h; cases h
    | instrAnnounce n w =>
      obtain ⟨rfl, _, rfl, _, _, rfl, _⟩ := h
      exact ⟨rfl, Or.inl rfl, fun _ => rfl, fun h => by simp [wlIsStore] at h⟩
    | choose p =>
      obtain ⟨_, rfl, _, rfl, _, _, rfl, _⟩ := h
      exact ⟨rfl, Or.inl rfl, fun h => by simp [ibnAnn] at h, fun h => by simp [wlIsStore] at h⟩
    | _ =>
      obtain ⟨rfl, _, rfl, _, _, rfl, _⟩ := h
      exact ⟨rfl, Or.inl rfl, fun h => by simp [ibnAnn] at h, fun h => by simp [wlIsStore] at h⟩

theorem pnodeStepChannel (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : DevStates) (oib : Option Ibch) (obar : Option barrier_kind) :
    pnodeStep m rs ib d l m' ors fn' d' oib obar → oib.getD ib = ibnStep m ib :=
  fun h => (pnodeStepFacts m rs ib d l m' ors fn' d' oib obar h).1

/-- THE ACCUMULATION LAW. -/
theorem ibnStepRds (m : SailM Unit) (ib : Ibch) :
    ibnAnn m = false → (ibnStep m ib).ibRds = ib.ibRds ++ pnodeRds m := by
  intro hann
  match m, hann with
  | .pure _, hann => cases hann
  | .impure (.error _) _, _ => simp [ibnStep, pnodeRds]
  | .impure (.ok o) k, hann =>
    cases o with
    | regRead r =>
      simp only [ibnStep, pnodeRds, ibRd]
      cases eregNum r <;> simp [ibRead]
    | instrAnnounce n w => cases hann
    | _ => simp [ibnStep, pnodeRds]

/-! ## 4. PER SILENT STRETCH -/

def erunRds : Nat → List Register → RegFile → SailM Unit → List Nat
  | 0, _, _, _ => []
  | n + 1, D, rs, m =>
    match esilNode D rs m with
    | some (rs', m') => pnodeRds m ++ erunRds n D rs' m'
    | none => []

def erunIb : Nat → List Register → RegFile → SailM Unit → Ibch → Ibch
  | 0, _, _, _, ib => ib
  | n + 1, D, rs, m, ib =>
    match esilNode D rs m with
    | some (rs', m') => erunIb n D rs' m' (ibnStep m ib)
    | none => ib

def erunAnn : Nat → List Register → RegFile → SailM Unit → Bool
  | 0, _, _, _ => false
  | n + 1, D, rs, m =>
    match esilNode D rs m with
    | some (rs', m') => ibnAnn m || erunAnn n D rs' m'
    | none => false

theorem esilNodeNone (D : List Register) (rs1 rs2 : RegFile) (m : SailM Unit) :
    esilNode D rs1 m = none → esilNode D rs2 m = none := by
  intro h
  match m, h with
  | .pure _, _ => rfl
  | .impure (.error _) _, _ => rfl
  | .impure (.ok o) k, h =>
    cases o with
    | regRead r =>
      simp only [esilNode] at h ⊢
      split at h
      · simp at h
      · rename_i hr; rw [if_neg hr]
    | regWrite r v =>
      simp only [esilNode] at h ⊢
      split at h
      · simp at h
      · rename_i hr; rw [if_neg hr]
    | _ => first | rfl | simp [esilNode] at h

theorem esilNodeDagree (D : List Register) (P : Nat → Prop) (rs1 rs2 : RegFile) (m : SailM Unit)
    (rs1' : RegFile) (m1 : SailM Unit) :
    rdsOk P (pnodeRds m) → dregAgree P rs1 rs2 → esilNode D rs1 m = some (rs1', m1) →
    ∃ rs2' : RegFile, esilNode D rs2 m = some (rs2', m1) ∧ dregAgree P rs1' rs2' := by
  intro hsub hag h
  match m, h with
  | .pure _, h => simp [esilNode] at h
  | .impure (.error _) _, h => simp [esilNode] at h
  | .impure (.ok o) k, h =>
    cases o with
    | regRead r =>
      have hlk : rs1 r = rs2 r := hag r (fun n hn => pnodeRdsRead r k P n hsub hn)
      simp only [esilNode] at h ⊢
      split at h
      · rename_i hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rs2, by rw [if_pos hr, hlk], hag⟩
      · simp at h
    | regWrite r v =>
      simp only [esilNode] at h ⊢
      split at h
      · rename_i hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rs2.set r v, by rw [if_pos hr], dregAgreeSet P rs1 rs2 r v hag⟩
      · simp at h
    | memRead => simp [esilNode] at h
    | memWrite => simp [esilNode] at h
    | readRam => simp [esilNode] at h
    | writeRam => simp [esilNode] at h
    | barrier => simp [esilNode] at h
    | choose => simp [esilNode] at h
    | _ =>
      simp only [esilNode, Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rs2, ⟨rfl, rfl⟩, hag⟩

/-- THE SILENT-RUN LEMMA, at the DYNAMIC footprint. -/
theorem erunSilentDagree (n : Nat) (D : List Register) (P : Nat → Prop) (rs1 rs2 : RegFile)
    (m : SailM Unit) (rs1' : RegFile) (m1 : SailM Unit) :
    rdsOk P (erunRds n D rs1 m) → dregAgree P rs1 rs2 → erunSilent n D rs1 m = (rs1', m1) →
    ∃ rs2' : RegFile, erunSilent n D rs2 m = (rs2', m1) ∧ dregAgree P rs1' rs2' := by
  induction n generalizing rs1 rs2 m with
  | zero =>
    intro _ hag hrun
    simp only [erunSilent, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨rs2, rfl, hag⟩
  | succ n ih =>
    intro hsub hag hrun
    simp only [erunSilent, erunRds] at hrun hsub ⊢
    cases hnode : esilNode D rs1 m with
    | none =>
      simp only [hnode, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      rw [esilNodeNone D rs1 rs2 m hnode]
      exact ⟨rs2, rfl, hag⟩
    | some p =>
      obtain ⟨rs1a, m1a⟩ := p
      simp only [hnode] at hrun hsub
      obtain ⟨hs1, hs2⟩ := rdsOkApp P _ _ hsub
      obtain ⟨rs2a, hnode2, hag2⟩ := esilNodeDagree D P rs1 rs2 m rs1a m1a hs1 hag hnode
      simp only [hnode2]
      exact ih rs1a rs2a m1a hs2 hag2 hrun

/-- THE COVERAGE STATEMENT, at the stretch. -/
theorem erunIbRds (n : Nat) (D : List Register) (rs : RegFile) (m : SailM Unit) (ib : Ibch) :
    erunAnn n D rs m = false → (erunIb n D rs m ib).ibRds = ib.ibRds ++ erunRds n D rs m := by
  induction n generalizing rs m ib with
  | zero => intro _; simp [erunIb, erunRds]
  | succ n ih =>
    intro hann
    simp only [erunAnn, erunIb, erunRds] at hann ⊢
    cases hnode : esilNode D rs m with
    | none => simp
    | some p =>
      obtain ⟨rs1, m1⟩ := p
      simp only [hnode, Bool.or_eq_false_iff] at hann ⊢
      rw [ih rs1 m1 (ibnStep m ib) hann.2, ibnStepRds m ib hann.1, List.append_assoc]

theorem erunSilentDagreeChannel (n : Nat) (D : List Register) (rs1 rs2 : RegFile) (m : SailM Unit)
    (ib : Ibch) (rs1' : RegFile) (m1 : SailM Unit) :
    erunAnn n D rs1 m = false →
    dregAgree (fun w => w ∈ (erunIb n D rs1 m ib).ibRds) rs1 rs2 →
    erunSilent n D rs1 m = (rs1', m1) →
    ∃ rs2' : RegFile, erunSilent n D rs2 m = (rs2', m1) ∧
      dregAgree (fun w => w ∈ (erunIb n D rs1 m ib).ibRds) rs1' rs2' := by
  intro hann hag hrun
  refine erunSilentDagree n D _ rs1 rs2 m rs1' m1 ?_ hag hrun
  intro x hx
  rw [erunIbRds n D rs1 m ib hann]
  exact List.mem_append_right _ hx

/-! ## 5. THE INSTANCE-LEVEL STATEMENT -/

/-- Lean-only (deviation 4): the PLIC wire at two agreeing register files. -/
theorem pstepPlicDagree (P : Nat → Prop) (cpu : CPU) (m : SailM Unit) (rs1 rs2 : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (l : Wlabel)
    (m' : SailM Unit) (ors1 : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : Efab) (oib : Option Ibch) (obar : Option barrier_kind) :
    dregAgree P rs1 rs2 →
    pstepPlic cpu m rs1 fn ib d l m' ors1 fn' d' oib obar →
    ∃ ors2 : Option RegFile, pstepPlic cpu m rs2 fn ib d l m' ors2 fn' d' oib obar ∧
      dregAgree P (ors1.getD rs1) (ors2.getD rs2) := by
  intro hag h
  obtain ⟨mm, b, k, hk, h1, h2, h3, h4, h5, h6, rfl⟩ := h
  refine ⟨some (pinSet rs2 mm b), ⟨mm, b, k, hk, h1, h2, h3, h4, h5, h6, rfl⟩, ?_⟩
  cases mm
  · exact dregAgreeSet P rs1 rs2 _ _ hag
  · exact dregAgreeSet P rs1 rs2 _ _ hag

/-- Lean-only (deviation 4): the registers the PLIC wire may write. -/
def plicWrs : List Register := [.sig_meip, .sig_seip]

theorem pstepPlicWrs (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : Efab) (oib : Option Ibch) (obar : Option barrier_kind) :
    pstepPlic cpu m rs fn ib d l m' ors fn' d' oib obar →
    ∃ (r : Register) (v : RegisterType r), r ∈ plicWrs ∧ ors = some (rs.set r v) := by
  intro h
  obtain ⟨mm, b, _, _, _, _, _, _, _, _, rfl⟩ := h
  cases mm
  · exact ⟨.sig_seip, if b then 1#1 else 0#1, by simp [plicWrs], rfl⟩
  · exact ⟨.sig_meip, if b then 1#1 else 0#1, by simp [plicWrs], rfl⟩

theorem pstepPlicOib (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : Efab) (oib : Option Ibch) (obar : Option barrier_kind) :
    pstepPlic cpu m rs fn ib d l m' ors fn' d' oib obar → oib = none :=
  fun h => by obtain ⟨_, _, _, _, _, _, _, _, h, _⟩ := h; exact h

theorem pstepHartDagree (P : Nat → Prop) (cpu : CPU) (m : SailM Unit) (rs1 rs2 : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (l : Wlabel)
    (m' : SailM Unit) (ors1 : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : Efab) (oib : Option Ibch) (obar : Option barrier_kind) :
    rdsOk P (pnodeRds m) → dregAgree P rs1 rs2 →
    pstepHart cpu m rs1 fn ib d l m' ors1 fn' d' oib obar →
    ∃ ors2 : Option RegFile, pstepHart cpu m rs2 fn ib d l m' ors2 fn' d' oib obar ∧
      dregAgree P (ors1.getD rs1) (ors2.getD rs2) := by
  intro hsub hag h
  rcases h with ⟨hn, hd⟩ | hp
  · cases fn with
    | some f =>
      obtain ⟨pr, pw, sr, sw⟩ := f
      exact ⟨ors1, Or.inl ⟨hn, hd⟩, dregAgreeGetD P rs1 rs2 ors1 hag⟩
    | none =>
      obtain ⟨ors2, h2, hag2⟩ := pnodeStepDagree P m rs1 rs2 ib d.efDev l m' ors1 fn' d'.efDev
        oib obar hsub hag hn
      exact ⟨ors2, Or.inl ⟨h2, hd⟩, hag2⟩
  · obtain ⟨ors2, h2, hag2⟩ := pstepPlicDagree P cpu m rs1 rs2 fn ib d l m' ors1 fn' d' oib obar
      hag hp
    exact ⟨ors2, Or.inr h2, hag2⟩

theorem pstepEvDagree (P : Nat → Prop) (cpu : CPU) (m : SailM Unit) (rs1 rs2 : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (l : Wlabel)
    (m' : SailM Unit) (rs1' : RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (ib' : Ibch)
    (d' : Efab) :
    rdsOk P (pnodeRds m) → dregAgree P rs1 rs2 →
    pstepEv (.PHart cpu m rs1 fn ib) d l (.PHart cpu m' rs1' fn' ib') d' →
    ∃ rs2' : RegFile,
      pstepEv (.PHart cpu m rs2 fn ib) d l (.PHart cpu m' rs2' fn' ib') d' ∧
      dregAgree P rs1' rs2' := by
  intro hsub hag h
  obtain ⟨_, ors1, oib, obar, rfl, rfl, hst⟩ := h
  obtain ⟨ors2, hst2, hag2⟩ := pstepHartDagree P cpu m rs1 rs2 fn ib d l m' ors1 fn' d' oib obar
    hsub hag hst
  exact ⟨ors2.getD rs2, ⟨rfl, ors2, oib, obar, rfl, rfl, hst2⟩, hag2⟩

/-! ## 6. SLICE 2b: THE ANNOTATED HART STEP -/

theorem pnodeStepOrs (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : DevStates) (oib : Option Ibch) (obar : Option barrier_kind) :
    pnodeStep m rs ib d l m' ors fn' d' oib obar →
    ors = none ∨ ∃ (r : Register) (v : RegisterType r), r ∈ pnodeWrs m ∧ ors = some (rs.set r v) :=
  fun h => (pnodeStepFacts m rs ib d l m' ors fn' d' oib obar h).2.1

/-- THE BOUNDARY IS VISIBLE IN THE LABEL. -/
theorem pnodeStepAnn (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : DevStates) (oib : Option Ibch) (obar : Option barrier_kind) :
    pnodeStep m rs ib d l m' ors fn' d' oib obar → ibnAnn m = true → l = LInstr :=
  fun h => (pnodeStepFacts m rs ib d l m' ors fn' d' oib obar h).2.2.1

/-- `pstepHart` with the three annotations (read list, written list, boundary flag). -/
def pstepHw (cpu : CPU) (m : SailM Unit) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool))
    (ib : Ibch) (d : Efab) (l : Wlabel) (rds : List Nat) (ws : List Register) (ann : Bool)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : Efab) (oib : Option Ibch) (obar : Option barrier_kind) : Prop :=
  (fn = none ∧ (pnodeStep m rs ib d.efDev l m' ors fn' d'.efDev oib obar ∧
      d' = { d with efDev := d'.efDev }) ∧
    rds = pnodeRds m ∧ ws = pnodeWrs m ∧ ann = ibnAnn m)
  ∨ (∃ pr pw sr sw, fn = some (pr, pw, sr, sw) ∧
      (pstepNode cpu m rs fn ib d.efDev l m' ors fn' d'.efDev oib obar ∧
        d' = { d with efDev := d'.efDev }) ∧ rds = [] ∧ ws = [] ∧ ann = false)
  ∨ (pstepPlic cpu m rs fn ib d l m' ors fn' d' oib obar ∧
      rds = [] ∧ ws = plicWrs ∧ ann = false)

theorem pstepHwHart (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (l : Wlabel)
    (rds : List Nat) (ws : List Register) (ann : Bool) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : Efab) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    pstepHw cpu m rs fn ib d l rds ws ann m' ors fn' d' oib obar →
    pstepHart cpu m rs fn ib d l m' ors fn' d' oib obar := by
  rintro (⟨rfl, H, -⟩ | ⟨_, _, _, _, rfl, H, -⟩ | ⟨H, -⟩)
  · exact Or.inl H
  · exact Or.inl H
  · exact Or.inr H

theorem pstepHartHw (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : Efab) (oib : Option Ibch) (obar : Option barrier_kind) :
    pstepHart cpu m rs fn ib d l m' ors fn' d' oib obar →
    ∃ rds ws ann, pstepHw cpu m rs fn ib d l rds ws ann m' ors fn' d' oib obar := by
  rintro (hn | hp)
  · cases fn with
    | some f =>
      obtain ⟨pr, pw, sr, sw⟩ := f
      exact ⟨[], [], false, Or.inr (Or.inl ⟨pr, pw, sr, sw, rfl, hn, rfl, rfl, rfl⟩)⟩
    | none => exact ⟨pnodeRds m, pnodeWrs m, ibnAnn m, Or.inl ⟨rfl, hn, rfl, rfl, rfl⟩⟩
  · exact ⟨[], plicWrs, false, Or.inr (Or.inr ⟨hp, rfl, rfl, rfl⟩)⟩

theorem pstepHwAnn (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (l : Wlabel)
    (rds : List Nat) (ws : List Register) (ann : Bool) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : Efab) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    pstepHw cpu m rs fn ib d l rds ws ann m' ors fn' d' oib obar → ann = true → l = LInstr := by
  rintro (⟨-, ⟨H, -⟩, -, -, rfl⟩ | ⟨_, _, _, _, -, -, -, -, rfl⟩ | ⟨-, -, -, rfl⟩) hann
  · exact pnodeStepAnn m rs ib _ l m' ors fn' _ oib obar H hann
  · cases hann
  · cases hann

theorem pstepHwChannel (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (l : Wlabel)
    (rds : List Nat) (ws : List Register) (ann : Bool) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : Efab) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    pstepHw cpu m rs fn ib d l rds ws ann m' ors fn' d' oib obar → ann = false →
    (oib.getD ib).ibRds = ib.ibRds ++ rds := by
  rintro (⟨-, ⟨H, -⟩, rfl, -, rfl⟩ | ⟨_, _, _, _, rfl, ⟨H, -⟩, rfl, -, -⟩ | ⟨H, rfl, -, -⟩) hann
  · rw [pnodeStepChannel m rs ib _ l m' ors fn' _ oib obar H]
    exact ibnStepRds m ib hann
  · obtain ⟨_, _, _, _, _, rfl, _⟩ := H
    simp
  · rw [pstepPlicOib cpu m rs fn ib d l m' ors fn' d' oib obar H]
    simp

theorem pstepHwFrame (P : Nat → Prop) (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (l : Wlabel)
    (rds : List Nat) (ws : List Register) (ann : Bool) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : Efab) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    pstepHw cpu m rs fn ib d l rds ws ann m' ors fn' d' oib obar →
    (∀ r, r ∈ ws → ∃ n, eregNum r = some n ∧ ¬ P n) →
    dregAgree P rs (ors.getD rs) := by
  rintro (⟨-, ⟨H, -⟩, -, rfl, -⟩ | ⟨_, _, _, _, rfl, ⟨H, -⟩, -, rfl, -⟩ | ⟨H, -, rfl, -⟩) hws
  · rcases pnodeStepOrs m rs ib _ l m' ors fn' _ oib obar H with rfl | ⟨r, v, hr, rfl⟩
    · exact dregAgreeRefl P rs
    · exact dregAgreeExcl P rs r v (hws r hr)
  · obtain ⟨_, _, rfl, _⟩ := H
    exact dregAgreeRefl P rs
  · obtain ⟨r, v, hr, rfl⟩ := pstepPlicWrs cpu m rs fn ib d l m' ors fn' d' oib obar H
    exact dregAgreeExcl P rs r v (hws r hr)

/-- THE STEP'S OWN AGREEMENT LEMMA, annotations carried unchanged. -/
theorem pstepHwDagree (P : Nat → Prop) (cpu : CPU) (m : SailM Unit) (rs1 rs2 : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (l : Wlabel)
    (rds : List Nat) (ws : List Register) (ann : Bool) (m' : SailM Unit) (ors1 : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : Efab) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    pstepHw cpu m rs1 fn ib d l rds ws ann m' ors1 fn' d' oib obar →
    rdsOk P rds → dregAgree P rs1 rs2 →
    ∃ ors2, pstepHw cpu m rs2 fn ib d l rds ws ann m' ors2 fn' d' oib obar ∧
      dregAgree P (ors1.getD rs1) (ors2.getD rs2) := by
  rintro (⟨rfl, H, rfl, rfl, rfl⟩ | ⟨pr, pw, sr, sw, rfl, H, rfl, rfl, rfl⟩ | ⟨H, rfl, rfl, rfl⟩)
    hrds hag
  · obtain ⟨ors2, H2, hag2⟩ := pnodeStepDagree P m rs1 rs2 ib d.efDev l m' ors1 fn' d'.efDev oib
      obar hrds hag H.1
    exact ⟨ors2, Or.inl ⟨rfl, ⟨H2, H.2⟩, rfl, rfl, rfl⟩, hag2⟩
  · exact ⟨ors1, Or.inr (Or.inl ⟨pr, pw, sr, sw, rfl, H, rfl, rfl, rfl⟩),
      dregAgreeGetD P rs1 rs2 ors1 hag⟩
  · obtain ⟨ors2, H2, hag2⟩ := pstepPlicDagree P cpu m rs1 rs2 fn ib d l m' ors1 fn' d' oib obar
      hag H
    exact ⟨ors2, Or.inr (Or.inr ⟨H2, rfl, rfl, rfl⟩), hag2⟩

/-! ## 7. THE RUN -/

/-- THE PLAIN CHAIN, at Layer 1's own type. -/
inductive pevrun : List Wlabel → Pexv6 → Efab → Pexv6 → Efab → Prop where
  | nil (p : Pexv6) (d : Efab) : pevrun [] p d p d
  | more {l : Wlabel} {ls : List Wlabel} {p : Pexv6} {d : Efab} {p1 : Pexv6}
      {d1 : Efab} {p2 : Pexv6} {d2 : Efab} :
      pstepEv p d l p1 d1 → pevrun ls p1 d1 p2 d2 → pevrun (l :: ls) p d p2 d2

/-- THE ANNOTATED CHAIN of ONE hart. -/
inductive phrun (cpu : CPU) : List Wlabel → List Nat → List Register → Bool → SailM Unit →
    RegFile → Option (Bool × Bool × Bool × Bool) → Ibch → Efab → SailM Unit → RegFile →
    Option (Bool × Bool × Bool × Bool) → Ibch → Efab → Prop where
  | nil (m : SailM Unit) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch)
      (d : Efab) : phrun cpu [] [] [] false m rs fn ib d m rs fn ib d
  | more {l : Wlabel} {ls : List Wlabel} {rds rds' : List Nat} {ws ws' : List Register}
      {ann ann' : Bool} {m : SailM Unit} {rs : RegFile} {fn : Option (Bool × Bool × Bool × Bool)}
      {ib : Ibch} {d : Efab} {m1 : SailM Unit} {ors : Option RegFile}
      {fn1 : Option (Bool × Bool × Bool × Bool)} {oib : Option Ibch} {obar : Option barrier_kind}
      {d1 : Efab} {m2 : SailM Unit} {rs2 : RegFile}
      {fn2 : Option (Bool × Bool × Bool × Bool)} {ib2 : Ibch} {d2 : Efab} :
      pstepHw cpu m rs fn ib d l rds ws ann m1 ors fn1 d1 oib obar →
      phrun cpu ls rds' ws' ann' m1 (ors.getD rs) fn1 (oib.getD ib) d1 m2 rs2 fn2 ib2 d2 →
      phrun cpu (l :: ls) (rds ++ rds') (ws ++ ws') (ann || ann') m rs fn ib d m2 rs2 fn2 ib2 d2

theorem phrunPevrun (cpu : CPU) (ls : List Wlabel) (rds : List Nat) (ws : List Register)
    (ann : Bool) (m : SailM Unit) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool))
    (ib : Ibch) (d : Efab) (m' : SailM Unit) (rs' : RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (ib' : Ibch) (d' : Efab) :
    phrun cpu ls rds ws ann m rs fn ib d m' rs' fn' ib' d' →
    pevrun ls (.PHart cpu m rs fn ib) d (.PHart cpu m' rs' fn' ib') d' := by
  intro h
  induction h with
  | nil m rs fn ib d => exact pevrun.nil _ _
  | @more l ls rds rds' ws ws' ann ann' m rs fn ib d m1 ors fn1 oib obar d1 m2 rs2 fn2 ib2 d2
      hstep _ ih =>
    refine pevrun.more (p1 := .PHart cpu m1 (ors.getD rs) fn1 (oib.getD ib)) (d1 := d1) ?_ ih
    exact ⟨rfl, ors, oib, obar, rfl, rfl,
      pstepHwHart cpu m rs fn ib d l rds ws ann m1 ors fn1 d1 oib obar hstep⟩

theorem pevrunPhrun (ls : List Wlabel) (p : Pexv6) (d : Efab) (p' : Pexv6) (d' : Efab) :
    pevrun ls p d p' d' →
    ∀ cpu m rs fn ib m' rs' fn' ib',
      p = .PHart cpu m rs fn ib → p' = .PHart cpu m' rs' fn' ib' →
      ∃ rds ws ann, phrun cpu ls rds ws ann m rs fn ib d m' rs' fn' ib' d' := by
  intro h
  induction h with
  | nil p d =>
    intro cpu m rs fn ib m' rs' fn' ib' hp hp'
    subst hp
    cases hp'
    exact ⟨[], [], false, phrun.nil m rs fn ib d⟩
  | @more l ls p d p1 d1 p2 d2 hstep _ ih =>
    intro cpu m rs fn ib m' rs' fn' ib' hp hp'
    subst hp
    cases p1 with
    | PDisk dp => exact (show False from hstep).elim
    | PHart cpu1 m1 rs1 fn1 ib1 =>
      obtain ⟨hc, ors, oib, obar, rfl, rfl, hst⟩ := hstep
      subst cpu1
      obtain ⟨rds, ws, ann, hhw⟩ := pstepHartHw cpu m rs fn ib d l m1 ors fn1 d1 oib obar hst
      obtain ⟨rds', ws', ann', hrun'⟩ :=
        ih cpu m1 (ors.getD rs) fn1 (oib.getD ib) m' rs' fn' ib' rfl hp'
      exact ⟨_, _, _, phrun.more hhw hrun'⟩

theorem phrunIbRds (cpu : CPU) (ls : List Wlabel) (rds : List Nat) (ws : List Register)
    (ann : Bool) (m : SailM Unit) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool))
    (ib : Ibch) (d : Efab) (m' : SailM Unit) (rs' : RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (ib' : Ibch) (d' : Efab) :
    phrun cpu ls rds ws ann m rs fn ib d m' rs' fn' ib' d' →
    ann = false → ib'.ibRds = ib.ibRds ++ rds := by
  intro h
  induction h with
  | nil => intro _; simp
  | @more l ls rds rds' ws ws' ann ann' m rs fn ib d m1 ors fn1 oib obar d1 m2 rs2 fn2 ib2 d2
      hstep _ ih =>
    intro hann
    rw [Bool.or_eq_false_iff] at hann
    have hc := pstepHwChannel cpu m rs fn ib d l rds ws ann m1 ors fn1 d1 oib obar hstep hann.1
    rw [ih hann.2, hc, List.append_assoc]

theorem phrunAnn (cpu : CPU) (ls : List Wlabel) (rds : List Nat) (ws : List Register)
    (ann : Bool) (m : SailM Unit) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool))
    (ib : Ibch) (d : Efab) (m' : SailM Unit) (rs' : RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (ib' : Ibch) (d' : Efab) :
    phrun cpu ls rds ws ann m rs fn ib d m' rs' fn' ib' d' →
    ann = true → LInstr ∈ ls := by
  intro h
  induction h with
  | nil => intro hann; cases hann
  | @more l ls rds rds' ws ws' ann ann' m rs fn ib d m1 ors fn1 oib obar d1 m2 rs2 fn2 ib2 d2
      hstep _ ih =>
    intro hann
    rcases Bool.or_eq_true_iff.1 hann with ha | hb
    · rw [pstepHwAnn cpu m rs fn ib d l rds ws ann m1 ors fn1 d1 oib obar hstep ha]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hb)

theorem phrunNoInstr (cpu : CPU) (ls : List Wlabel) (rds : List Nat) (ws : List Register)
    (ann : Bool) (m : SailM Unit) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool))
    (ib : Ibch) (d : Efab) (m' : SailM Unit) (rs' : RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (ib' : Ibch) (d' : Efab) :
    phrun cpu ls rds ws ann m rs fn ib d m' rs' fn' ib' d' →
    LInstr ∉ ls → ann = false := by
  intro hrun hni
  cases ann with
  | false => rfl
  | true => exact absurd (phrunAnn cpu ls rds ws true m rs fn ib d m' rs' fn' ib' d' hrun rfl) hni

/-! ## 8. (A) THE PER-INSTRUCTION SOUNDNESS LEMMA -/

theorem phrunDagree (P : Nat → Prop) (cpu : CPU) (ls : List Wlabel) (rds : List Nat)
    (ws : List Register) (ann : Bool) (m : SailM Unit) (rs1 : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (m' : SailM Unit)
    (rs1' : RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (ib' : Ibch) (d' : Efab) :
    phrun cpu ls rds ws ann m rs1 fn ib d m' rs1' fn' ib' d' →
    rdsOk P rds →
    ∀ rs2, dregAgree P rs1 rs2 →
    ∃ rs2', phrun cpu ls rds ws ann m rs2 fn ib d m' rs2' fn' ib' d' ∧ dregAgree P rs1' rs2' := by
  intro h
  induction h with
  | nil m rs fn ib d =>
    intro _ rsb hag
    exact ⟨rsb, phrun.nil m rsb fn ib d, hag⟩
  | @more l ls rds rds' ws ws' ann ann' m rs fn ib d m1 ors fn1 oib obar d1 m2 rs2 fn2 ib2 d2
      hstep _ ih =>
    intro hrds rsb hag
    obtain ⟨hrds1, hrds2⟩ := rdsOkApp P rds rds' hrds
    obtain ⟨orsb, hstepb, hagb⟩ :=
      pstepHwDagree P cpu m rs rsb fn ib d l rds ws ann m1 ors fn1 d1 oib obar hstep hrds1 hag
    obtain ⟨rsb', hrunb, hagb'⟩ := ih hrds2 (orsb.getD rsb) hagb
    exact ⟨rsb', phrun.more hstepb hrunb, hagb'⟩

/-- THE HEADLINE, at the channel. -/
theorem instrDagree (T : List Nat) (cpu : CPU) (ls : List Wlabel) (rds : List Nat)
    (ws : List Register) (ann : Bool) (m : SailM Unit) (rs1 : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (m' : SailM Unit)
    (rs1' : RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (ib' : Ibch) (d' : Efab) :
    phrun cpu ls rds ws ann m rs1 fn ib d m' rs1' fn' ib' d' →
    LInstr ∉ ls →
    (∀ n, n ∈ ib'.ibRds → n ∉ T) →
    ∀ rs2, dregAgree (fun n => n ∉ T) rs1 rs2 →
    ∃ rs2', phrun cpu ls rds ws ann m rs2 fn ib d m' rs2' fn' ib' d' ∧
      dregAgree (fun n => n ∉ T) rs1' rs2' := by
  intro hrun hni hib rs2 hag
  have hann := phrunNoInstr cpu ls rds ws ann m rs1 fn ib d m' rs1' fn' ib' d' hrun hni
  have hcov := phrunIbRds cpu ls rds ws ann m rs1 fn ib d m' rs1' fn' ib' d' hrun hann
  refine phrunDagree _ cpu ls rds ws ann m rs1 fn ib d m' rs1' fn' ib' d' hrun ?_ rs2 hag
  intro n hn
  apply hib
  rw [hcov]
  exact List.mem_append_right _ hn

theorem instrDagreeEv (T : List Nat) (cpu : CPU) (ls : List Wlabel) (m : SailM Unit)
    (rs1 : RegFile) (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab)
    (m' : SailM Unit) (rs1' : RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (ib' : Ibch)
    (d' : Efab) :
    pevrun ls (.PHart cpu m rs1 fn ib) d (.PHart cpu m' rs1' fn' ib') d' →
    LInstr ∉ ls →
    (∀ n, n ∈ ib'.ibRds → n ∉ T) →
    ∀ rs2, dregAgree (fun n => n ∉ T) rs1 rs2 →
    ∃ rs2', pevrun ls (.PHart cpu m rs2 fn ib) d (.PHart cpu m' rs2' fn' ib') d' ∧
      dregAgree (fun n => n ∉ T) rs1' rs2' := by
  intro hrun hni hib rs2 hag
  obtain ⟨rds, ws, ann, hh⟩ := pevrunPhrun ls _ d _ d' hrun cpu m rs1 fn ib m' rs1' fn' ib' rfl rfl
  obtain ⟨rs2', hh2, hag2⟩ :=
    instrDagree T cpu ls rds ws ann m rs1 fn ib d m' rs1' fn' ib' d' hh hni hib rs2 hag
  exact ⟨rs2', phrunPevrun cpu ls rds ws ann m rs2 fn ib d m' rs2' fn' ib' d' hh2, hag2⟩

/-- THE WRITE LABEL IS A FUNCTION OF THE NODE AND THE CHANNEL. -/
theorem pnodeStepStoreDet (m : SailM Unit) (rs1 rs2 : RegFile) (ib : Ibch) (d : DevStates)
    (l1 l2 : Wlabel) (m1 m2 : SailM Unit) (ors1 ors2 : Option RegFile)
    (fn1 fn2 : Option (Bool × Bool × Bool × Bool)) (d1 d2 : DevStates) (oib1 oib2 : Option Ibch)
    (obar1 obar2 : Option barrier_kind) :
    pnodeStep m rs1 ib d l1 m1 ors1 fn1 d1 oib1 obar1 →
    pnodeStep m rs2 ib d l2 m2 ors2 fn2 d2 oib2 obar2 →
    wlIsStore l1 = true → wlIsStore l2 = true → l1 = l2 := by
  intro h1 h2 hs1 hs2
  rw [(pnodeStepFacts _ _ _ _ _ _ _ _ _ _ _ h1).2.2.2 hs1,
    (pnodeStepFacts _ _ _ _ _ _ _ _ _ _ _ h2).2.2.2 hs2]

/-! ## 9. (B) THE TAINT CLOSURE -/

theorem phrunFrame (P : Nat → Prop) (cpu : CPU) (ls : List Wlabel) (rds : List Nat)
    (ws : List Register) (ann : Bool) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (m' : SailM Unit)
    (rs' : RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (ib' : Ibch) (d' : Efab) :
    phrun cpu ls rds ws ann m rs fn ib d m' rs' fn' ib' d' →
    (∀ r, r ∈ ws → ∃ n, eregNum r = some n ∧ ¬ P n) →
    dregAgree P rs rs' := by
  intro h
  induction h with
  | nil m rs => intro _; exact dregAgreeRefl P rs
  | @more l ls rds rds' ws ws' ann ann' m rs fn ib d m1 ors fn1 oib obar d1 m2 rs2 fn2 ib2 d2
      hstep _ ih =>
    intro hws
    refine dregAgreeTrans P _ _ _ ?_ (ih fun r hr => hws r (List.mem_append_right _ hr))
    exact pstepHwFrame P cpu m rs fn ib d l rds ws ann m1 ors fn1 d1 oib obar hstep
      fun r hr => hws r (List.mem_append_left _ hr)

/-- THE CLOSURE, for two runs that have parted company. -/
theorem taintClosure (P : Nat → Prop) (cpu1 : CPU) (ls1 : List Wlabel) (rds1 : List Nat)
    (ws1 : List Register) (ann1 : Bool) (m1 : SailM Unit) (rs1 : RegFile)
    (fn1 : Option (Bool × Bool × Bool × Bool)) (ib1 : Ibch) (d1 : Efab) (m1' : SailM Unit)
    (rs1' : RegFile) (fn1' : Option (Bool × Bool × Bool × Bool)) (ib1' : Ibch) (d1' : Efab)
    (cpu2 : CPU) (ls2 : List Wlabel) (rds2 : List Nat) (ws2 : List Register) (ann2 : Bool)
    (m2 : SailM Unit) (rs2 : RegFile) (fn2 : Option (Bool × Bool × Bool × Bool)) (ib2 : Ibch)
    (d2 : Efab) (m2' : SailM Unit) (rs2' : RegFile)
    (fn2' : Option (Bool × Bool × Bool × Bool)) (ib2' : Ibch) (d2' : Efab) :
    dregAgree P rs1 rs2 →
    phrun cpu1 ls1 rds1 ws1 ann1 m1 rs1 fn1 ib1 d1 m1' rs1' fn1' ib1' d1' →
    phrun cpu2 ls2 rds2 ws2 ann2 m2 rs2 fn2 ib2 d2 m2' rs2' fn2' ib2' d2' →
    (∀ r, r ∈ ws1 ++ ws2 → ∃ n, eregNum r = some n ∧ ¬ P n) →
    dregAgree P rs1' rs2' := by
  intro hag hr1 hr2 hws
  have h1 := phrunFrame P cpu1 ls1 rds1 ws1 ann1 m1 rs1 fn1 ib1 d1 m1' rs1' fn1' ib1' d1' hr1
    fun r hr => hws r (List.mem_append_left _ hr)
  have h2 := phrunFrame P cpu2 ls2 rds2 ws2 ann2 m2 rs2 fn2 ib2 d2 m2' rs2' fn2' ib2' d2' hr2
    fun r hr => hws r (List.mem_append_right _ hr)
  exact dregAgreeTrans P _ _ _ (dregAgreeSym P _ _ h1) (dregAgreeTrans P _ _ _ hag h2)

/-- ... in the form §4e quotes: a load whose answers differ taints its destination `rd`. -/
theorem taintClosureLoad (T : List Nat) (rd : Nat) (cpu1 : CPU) (ls1 : List Wlabel)
    (rds1 : List Nat) (ws1 : List Register) (ann1 : Bool) (m1 : SailM Unit) (rs1 : RegFile)
    (fn1 : Option (Bool × Bool × Bool × Bool)) (ib1 : Ibch) (d1 : Efab) (m1' : SailM Unit)
    (rs1' : RegFile) (fn1' : Option (Bool × Bool × Bool × Bool)) (ib1' : Ibch) (d1' : Efab)
    (cpu2 : CPU) (ls2 : List Wlabel) (rds2 : List Nat) (ws2 : List Register) (ann2 : Bool)
    (m2 : SailM Unit) (rs2 : RegFile) (fn2 : Option (Bool × Bool × Bool × Bool)) (ib2 : Ibch)
    (d2 : Efab) (m2' : SailM Unit) (rs2' : RegFile)
    (fn2' : Option (Bool × Bool × Bool × Bool)) (ib2' : Ibch) (d2' : Efab) :
    dregAgree (fun n => n ∉ T) rs1 rs2 →
    phrun cpu1 ls1 rds1 ws1 ann1 m1 rs1 fn1 ib1 d1 m1' rs1' fn1' ib1' d1' →
    phrun cpu2 ls2 rds2 ws2 ann2 m2 rs2 fn2 ib2 d2 m2' rs2' fn2' ib2' d2' →
    (∀ r, r ∈ ws1 ++ ws2 → ∃ n, eregNum r = some n ∧ n ∈ rd :: T) →
    dregAgree (fun n => n ∉ rd :: T) rs1' rs2' := by
  intro hag hr1 hr2 hws
  refine taintClosure _ cpu1 ls1 rds1 ws1 ann1 m1 rs1 fn1 ib1 d1 m1' rs1' fn1' ib1' d1'
    cpu2 ls2 rds2 ws2 ann2 m2 rs2 fn2 ib2 d2 m2' rs2' fn2' ib2' d2' ?_ hr1 hr2 ?_
  · exact dregAgreeMono _ _ rs1 rs2 (fun n hn hin => hn (List.mem_cons_of_mem _ hin)) hag
  · intro r hr
    obtain ⟨n, hn, hin⟩ := hws r hr
    exact ⟨n, hn, fun hno => hno hin⟩

/-! ## 10. NON-VACUITY -/

/-- A two-node fragment that reads `x15` and writes `x14`. -/
def witM : SailM Unit :=
  .impure (.ok (.regRead .x15)) (fun v => .impure (.ok (.regWrite .x14 v)) (fun _ => .pure ()))

theorem witRun (cpu : CPU) (rs : RegFile) (d : Efab) :
    ∃ ls rds ws ann m' ib' rs',
      phrun cpu ls rds ws ann witM rs none ibNone d m' rs' none ib' d ∧
      rds = [15] ∧ ws = [(.x14 : Register)] ∧ ann = false ∧ LInstr ∉ ls ∧ ib'.ibRds = [15] := by
  refine ⟨_, _, _, _, _, _, _,
    phrun.more (Or.inl ⟨rfl, ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, rfl, rfl, rfl⟩)
      (phrun.more (Or.inl ⟨rfl, ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, rfl, rfl, rfl⟩)
        (phrun.nil _ _ _ _ _)), rfl, rfl, rfl, ?_, rfl⟩
  intro hin
  rcases List.mem_cons.1 hin with h | h
  · cases h
  · rcases List.mem_cons.1 h with h | h
    · exact erwLabelNeInstr _ h.symm
    · cases h

theorem instrDagreeNonvacuous (cpu : CPU) (rs1 rs2 : RegFile) (d : Efab) :
    dregAgree (fun n => n ∉ [14]) rs1 rs2 →
    ∃ ls m' ib' rs1' rs2',
      phrun cpu ls [15] [(.x14 : Register)] false witM rs1 none ibNone d m' rs1' none ib' d ∧
      phrun cpu ls [15] [(.x14 : Register)] false witM rs2 none ibNone d m' rs2' none ib' d ∧
      dregAgree (fun n => n ∉ [14]) rs1' rs2' := by
  intro hag
  obtain ⟨ls, rds, ws, ann, m', ib', rs1', hrun, rfl, rfl, rfl, hni, hib⟩ := witRun cpu rs1 d
  obtain ⟨rs2', hrun2, hag2⟩ :=
    instrDagree [14] cpu ls [15] [.x14] false witM rs1 none ibNone d m' rs1' none ib' d hrun hni
      (by rw [hib]; intro n hn; simp at hn; subst hn; decide) rs2 hag
  exact ⟨ls, m', ib', rs1', rs2', hrun, hrun2, hag2⟩

end Weak
