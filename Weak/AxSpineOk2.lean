/-
Weak: **the register-only callees of the S-mode fetch chain** — their `rfF` footprints (so every
SC `exec` lemma about them transfers to `execA` by `execAOfRfF`, unchanged); the RAM-read
footprint `rfM` and the RAM leaf `execAReadRamPlain`; the tactic `to_a` (SC exec fact ⇒ `execA`
fact).

Rocq: `iris/AxSpineOk2.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. MONADS (as `AxSpineOk` deviation 4): `Defs.try_catch` ↦ `PreSail.tryCatchAll`
   (`rfFTryCatch`); Lean-only twin for the model's own `sailTryCatch`
   (`AxSpineOk2.rfFSailTryCatch`).  `catch_early_return` ↦ `SailME.run`, stated on
   `rfF (ExceptT.run m)` (`rfFCatchEarlyReturn`).  Lean-only `AxSpineOk2.rfFRBind` (bind in the
   early-return monad) and `AxSpineOk2.rfFRThrow`.
2. LOOPS: Rocq `foreach_ZM_up'` (fuel `n`) / `foreach_ZM_up` ↦ lean-sail's `IntRange` loop
   `IntRange.forIn'.loop` / `forIn` at step 1 (`rfFForeachZMUp'` / `rfFForeachZMUp`, in `SailM`);
   Lean-only `SailME` twins `AxSpineOk2.rfFRForInLoop` / `AxSpineOk2.rfFRForIn` (`pmpCheck`'s loop
   is in the early-return monad).  The Rocq fuel argument is replaced by the start index.
3. `rfM` (as `rfF`, `AxSpineOk` deviations 2–4): the pins are `AxRunClose.pinReg`; the announce
   arm demands `sfAnnB n w = false` (`execA` is stuck at an sfence announce); failure nodes,
   `choose`, `readRam`, `writeRam` are allowed (`True`, as Rocq's `_ => True`).
4. `execAReadRamPlain`: Rocq's `0 ≤ n` is dropped (`n : Nat`); `uint addr + n ≤ 2^64` ↦
   `paZ addr + n ≤ 2^64`; the result meta is `default_meta`.
5. Callee arguments are lean-sail's: `lookup_TLB`/`add_to_TLB`/`get_satp`/`check_leaf_pte` take
   the `sv_width : Nat` first (Rocq: the `w` argument); `check_PTE_permission` takes the trailing
   `_ext_ptw : Unit`.
6. Tactics: Rocq `head_of`/`rfF_unf`/`rfF_acc`/`rfF_cer` ↦ ONE dispatcher `rff_step` on the
   head of the tree (binds, `if`s, lifts, `SailME.run`, try-catch and loops by their lemmas; a
   heading `match` by `split`, else `cases` on its variable discriminant; leaves by `True.intro`;
   any other constant unfolded; a `SailME` tree that lost its `ExceptT.run` re-wrapped).  Lean
   has no `Acc`-recursion artefacts to destruct.  `rfF_auto` ↦ `rff_auto`, `toA` ↦ `to_a H`.
   `split` is only used at a heading `match` (an inner `match` multiplies the goals: `pmaCheck`).
7. `rfFCheckPmaWithPmpPriority` is proved compositionally through the Lean-only
   `AxSpineOk2.rfFPmaCheck` and `rfFPmpCheck` (Rocq: `rfF_auto` over the whole tree).
8. `execAAssertExpTrue`: Rocq's `assert_exp' true msg` returns `eq_refl`; lean-sail's
   `assert true msg` returns `()`.

**Rocq → Lean name map.**  `rfF_try_catch` `rfFTryCatch`, `rfF_catch_early_return`
`rfFCatchEarlyReturn`, `rfF_foreach_ZM_up'` `rfFForeachZMUp'`, `rfF_foreach_ZM_up`
`rfFForeachZMUp`, `rfF_<callee>` `rfF<Callee>` (camel-cased: `rfFEffectivePrivilege`,
`rfFIsShadowStackAccess`, `rfFWithinClint`, `rfFWithinSig`, `rfFWithinHtifReadable`,
`rfFPteIsInvalid`, `rfFLookupTLB`, `rfFAddToTLB`, `rfFTlbGetPbmt`, `rfFTranslationMode`,
`rfFGetSatp`, `rfFCurrentlyEnabledZca`, `rfFCurrentlyEnabledZiccif`, `rfFCheckPTEPermission`,
`rfFReadKindOfFlags`, `rfFSatpModeWidthForwards`, `rfFSplitMisaligned`, `rfFCheckLeafPte`,
`rfFPmpCheck`, `rfFCheckPmaWithPmpPriority`, `rfFWithinMmioReadable`, `rfFShouldIncMinstret`),
`rfM` `rfM`, `rfM_bind` `rfMBind`, `execA_of_rfM` `execAOfRfM`, `execA_read_ram_plain`
`execAReadRamPlain`, `execA_assert_exp'_true` `execAAssertExpTrue`; tactics `head_of`/`rfF_unf`/
`rfF_acc`/`rfF_cer` ↦ `rff_step`, `rfF_auto` ↦ `rff_auto`, `toA` ↦ `to_a`.  None is in the duplicated-name table.
Lean-only (file-qualified): `AxSpineOk2.rfFSailTryCatch`, `AxSpineOk2.rfFRBind`,
`AxSpineOk2.rfFRThrow`, `AxSpineOk2.rfFRForInLoop`, `AxSpineOk2.rfFRForIn`, the automation leaves
`AxSpineOk2.rfFPure`/`rfFRPure`/`rfFFail`/`rfFThrow`/`rfFSailThrow`/`rfFIte`/`rfFRIte`/`rfFDite`/
`rfFRDite`/`rfFFreeBind`/`rfFLiftSelf`, `AxSpineOk2.rfFPmaCheck`; tactic `rff_step`.

**Dropped:** none.
-/
import Weak.AxSpineOk

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 1. Combinators -/

theorem rfFTryCatch {X : Type} (m : SailM X) (h : Sail.Error exception → SailM X) :
    rfF m → (∀ e, rfF (h e)) → rfF (PreSail.tryCatchAll m h) := by
  induction m with
  | pure y => intro _ _; trivial
  | impure call k ih =>
    intro hm hh
    cases call with
    | error e => exact hh e
    | ok o =>
      show rfF (FreeM.impure (.ok o) (fun r => PreSail.tryCatchAll (k r) h))
      cases o
      case regRead r => exact ⟨hm.1, fun v => ih v (hm.2 v) hh⟩
      case regWrite r v => exact ⟨hm.1, ih _ hm.2 hh⟩
      case instrAnnounce n w => exact ⟨hm.1, ih _ hm.2 hh⟩
      all_goals first | exact hm | trivial | exact ih _ hm hh

/-- (Lean-only, deviation 1) The model's own `try … catch`. -/
theorem AxSpineOk2.rfFSailTryCatch {X : Type} (m : SailM X) (h : exception → SailM X) :
    rfF m → (∀ e, rfF (h e)) → rfF (PreSail.sailTryCatch m h) := by
  induction m with
  | pure y => intro _ _; trivial
  | impure call k ih =>
    intro hm hh
    cases call with
    | error e =>
      cases e
      case User u => exact hh u
      all_goals trivial
    | ok o =>
      show rfF (FreeM.impure (.ok o) (fun r => PreSail.sailTryCatch (k r) h))
      cases o
      case regRead r => exact ⟨hm.1, fun v => ih v (hm.2 v) hh⟩
      case regWrite r v => exact ⟨hm.1, ih _ hm.2 hh⟩
      case instrAnnounce n w => exact ⟨hm.1, ih _ hm.2 hh⟩
      all_goals first | exact hm | trivial | exact ih _ hm hh

/-- (Lean-only, deviation 1) Bind in the early-return monad. -/
theorem AxSpineOk2.rfFRBind {R X Y : Type} (m : SailME R X) (f : X → SailME R Y) :
    rfF (ExceptT.run m) → (∀ x, rfF (ExceptT.run (f x))) → rfF (ExceptT.run (m >>= f)) := by
  intro hm hf
  rw [ExceptT.run_bind]
  refine rfFBind _ _ hm (fun e => ?_)
  cases e with
  | ok x => exact hf x
  | error e => trivial

/-- (Lean-only, deviation 1) An early return. -/
theorem AxSpineOk2.rfFRThrow {R X : Type} (r : R) :
    rfF (ExceptT.run (PreSail.PreSailME.throw r : SailME R X)) := trivial

theorem rfFCatchEarlyReturn {X : Type} (m : SailME X X) :
    rfF (ExceptT.run m) → rfF (SailME.run m) := by
  intro hm
  show rfF (ExceptT.run m >>= _)
  refine rfFBind _ _ hm (fun e => ?_)
  rcases e with (e | r) | x <;> trivial

/-- Rocq `rfF_foreach_ZM_up'` (deviation 2): the step-1 `IntRange` loop from any index. -/
theorem rfFForeachZMUp' {β : Type} (range : IntRange) (hstep : range.step = 1)
    (f : Int → β → SailM (ForInStep β)) (hf : ∀ i b, rfF (f i b)) :
    ∀ (i : Int) (hs : (i - range.start) % range.step = 0) (b : β),
      rfF (IntRange.forIn'.loop range (fun a _ b => f a b) b i hs) := by
  suffices H : ∀ (n : Nat) (i : Int) (hs : (i - range.start) % range.step = 0) (b : β),
      (range.stop - i + 1).toNat = n →
      rfF (IntRange.forIn'.loop range (fun a _ b => f a b) b i hs) from
    fun i hs b => H _ i hs b rfl
  intro n
  induction n with
  | zero =>
    intro i hs b hn
    rw [IntRange.loop_unfold]
    have hni : ¬ i ∈ range := by
      intro h
      simp only [Membership.mem, hstep, show (1 : Int) > 0 from by decide, ite_true] at h
      have := Int.toNat_eq_zero.mp hn
      omega
    simp only [dif_neg hni]
    trivial
  | succ n ih =>
    intro i hs b hn
    rw [IntRange.loop_unfold]
    by_cases h : i ∈ range
    · simp only [dif_pos h]
      refine rfFBind _ _ (hf i b) (fun r => ?_)
      cases r with
      | done b' => trivial
      | yield b' =>
        have hn' : (range.stop - (i + range.step) + 1).toNat = n := by
          simp only [Membership.mem, hstep, show (1 : Int) > 0 from by decide, ite_true] at h
          rw [hstep]
          omega
        exact ih _ _ b' hn'
    · simp only [dif_neg h]
      trivial

theorem rfFForeachZMUp {β : Type} (range : IntRange) (hstep : range.step = 1) (b : β)
    (f : Int → β → SailM (ForInStep β)) (hf : ∀ i b, rfF (f i b)) : rfF (forIn range b f) :=
  rfFForeachZMUp' range hstep f hf range.start (by simp) b

/-- (Lean-only, deviation 2) The loop in the early-return monad. -/
theorem AxSpineOk2.rfFRForInLoop {R β : Type} (range : IntRange) (hstep : range.step = 1)
    (f : Int → β → SailME R (ForInStep β)) (hf : ∀ i b, rfF (ExceptT.run (f i b))) :
    ∀ (i : Int) (hs : (i - range.start) % range.step = 0) (b : β),
      rfF (ExceptT.run (IntRange.forIn'.loop range (fun a _ b => f a b) b i hs)) := by
  suffices H : ∀ (n : Nat) (i : Int) (hs : (i - range.start) % range.step = 0) (b : β),
      (range.stop - i + 1).toNat = n →
      rfF (ExceptT.run (IntRange.forIn'.loop range (fun a _ b => f a b) b i hs)) from
    fun i hs b => H _ i hs b rfl
  intro n
  induction n with
  | zero =>
    intro i hs b hn
    rw [IntRange.loop_unfold]
    have hni : ¬ i ∈ range := by
      intro h
      simp only [Membership.mem, hstep, show (1 : Int) > 0 from by decide, ite_true] at h
      have := Int.toNat_eq_zero.mp hn
      omega
    simp only [dif_neg hni]
    trivial
  | succ n ih =>
    intro i hs b hn
    rw [IntRange.loop_unfold]
    by_cases h : i ∈ range
    · simp only [dif_pos h]
      refine AxSpineOk2.rfFRBind _ _ (hf i b) (fun r => ?_)
      cases r with
      | done b' => trivial
      | yield b' =>
        have hn' : (range.stop - (i + range.step) + 1).toNat = n := by
          simp only [Membership.mem, hstep, show (1 : Int) > 0 from by decide, ite_true] at h
          rw [hstep]
          omega
        exact ih _ _ b' hn'
    · simp only [dif_neg h]
      trivial

theorem AxSpineOk2.rfFRForIn {R β : Type} (range : IntRange) (hstep : range.step = 1) (b : β)
    (f : Int → β → SailME R (ForInStep β)) (hf : ∀ i b, rfF (ExceptT.run (f i b))) :
    rfF (ExceptT.run (forIn range b f)) :=
  AxSpineOk2.rfFRForInLoop range hstep f hf range.start (by simp) b

/-! # 2. Automation -/

/-- (Lean-only) Leaf facts for the automation. -/
theorem AxSpineOk2.rfFPure {X : Type} (x : X) : rfF (pure x : SailM X) := trivial
theorem AxSpineOk2.rfFRPure {R X : Type} (x : X) : rfF (ExceptT.run (pure x : SailME R X)) :=
  trivial
theorem AxSpineOk2.rfFFail {X : Type} (e : Sail.Error exception) :
    rfF (PreSail.fail e : SailM X) := trivial
theorem AxSpineOk2.rfFThrow {X : Type} (e : Sail.Error exception) :
    rfF (throw e : SailM X) := trivial
theorem AxSpineOk2.rfFSailThrow {X : Type} (e : exception) :
    rfF (PreSail.sailThrow e : SailM X) := trivial
theorem AxSpineOk2.rfFIte {X : Type} (c : Prop) [Decidable c] (a b : SailM X)
    (ha : rfF a) (hb : rfF b) : rfF (if c then a else b) := by
  by_cases h : c
  · rw [if_pos h]; exact ha
  · rw [if_neg h]; exact hb
theorem AxSpineOk2.rfFRIte {R X : Type} (c : Prop) [Decidable c] (a b : SailME R X)
    (ha : rfF (ExceptT.run a)) (hb : rfF (ExceptT.run b)) :
    rfF (ExceptT.run (if c then a else b)) := by
  by_cases h : c
  · rw [if_pos h]; exact ha
  · rw [if_neg h]; exact hb
theorem AxSpineOk2.rfFFreeBind {X Y : Type} (m : SailM X) (f : X → SailM Y) :
    rfF m → (∀ x, rfF (f x)) → rfF (FreeM.bind m f) := rfFBind m f
theorem AxSpineOk2.rfFLiftSelf {X : Type} (m : SailM X) (h : rfF m) :
    rfF (monadLift m : SailM X) := h

theorem AxSpineOk2.rfFDite {X : Type} (c : Prop) [Decidable c] (a : c → SailM X)
    (b : ¬ c → SailM X) (ha : ∀ h, rfF (a h)) (hb : ∀ h, rfF (b h)) :
    rfF (if h : c then a h else b h) := by
  by_cases h : c
  · rw [dif_pos h]; exact ha h
  · rw [dif_neg h]; exact hb h
theorem AxSpineOk2.rfFRDite {R X : Type} (c : Prop) [Decidable c] (a : c → SailME R X)
    (b : ¬ c → SailME R X) (ha : ∀ h, rfF (ExceptT.run (a h))) (hb : ∀ h, rfF (ExceptT.run (b h))) :
    rfF (ExceptT.run (if h : c then a h else b h)) := by
  by_cases h : c
  · rw [dif_pos h]; exact ha h
  · rw [dif_neg h]; exact hb h

open Lean Elab Tactic Meta in
/-- Rocq `rfF_step`/`rfF_unf`/`rfF_cer` (with `head_of`), as one dispatcher on the head of the
tree in an `rfF` goal (`ExceptT.run` stripped): binds, `if`s, lifts, early-return runs,
try-catch and loops by their lemmas; a heading `match` by `split`; leaves by `True.intro`;
any other constant is unfolded.  A `SailME` tree that lost its `ExceptT.run` (after `split`)
is re-wrapped first. -/
elab "rff_step" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt := (← instantiateMVars (← g.getType)).consumeMData
  unless tgt.isAppOf ``Weak.rfF do throwError "rff_step: not an rfF goal"
  let t0 := tgt.appArg!
  let wrapped := t0.isAppOf ``ExceptT.run
  let t := if wrapped then t0.appArg! else t0
  let args := t.getAppArgs
  let isE (e : Lean.Expr) : MetaM Bool := do
    return (← whnfR (← instantiateMVars e)).consumeMData.isAppOf ``ExceptT
  let ev (stx : TacticM (TSyntax `tactic)) : TacticM Unit := do evalTactic (← stx)
  let hd := t.getAppFn.constName?
  -- re-wrap a bare early-return tree
  if !wrapped then
    let isET ← if (hd == some ``Bind.bind || hd == some ``Pure.pure) && args.size > 0 then
        isE args[0]!
      else if (hd == some ``ite || hd == some ``dite) && args.size > 0 then
        (do let a ← whnfR args[0]!; return a.isApp && (← isE a.appFn!))
      else (do let ty ← inferType t; return ty.isApp && (← isE ty.appFn!))
    if isET then
      let ng ← mkAppM ``Weak.rfF #[← mkAppM ``ExceptT.run #[t]]
      replaceMainGoal [← g.replaceTargetDefEq ng]
      return
  match hd with
  | some c =>
    if c == ``Bind.bind || c == ``FreeM.bind then
      if wrapped then ev `(tactic| (apply AxSpineOk2.rfFRBind <;> try intro _))
      else if c == ``FreeM.bind then ev `(tactic| (apply AxSpineOk2.rfFFreeBind <;> try intro _))
      else ev `(tactic| (apply rfFBind <;> try intro _))
    else if c == ``ite then
      if wrapped then ev `(tactic| apply AxSpineOk2.rfFRIte) else ev `(tactic| apply AxSpineOk2.rfFIte)
    else if c == ``dite then
      if wrapped then ev `(tactic| (apply AxSpineOk2.rfFRDite <;> intro _))
      else ev `(tactic| (apply AxSpineOk2.rfFDite <;> intro _))
    else if c == ``liftM || c == ``monadLift || c == ``MonadLiftT.monadLift then
      if wrapped then ev `(tactic| apply rfFLiftR) else ev `(tactic| apply AxSpineOk2.rfFLiftSelf)
    else if c == ``SailME.run then ev `(tactic| apply rfFCatchEarlyReturn)
    else if c == ``PreSail.tryCatchAll then ev `(tactic| (apply rfFTryCatch <;> try intro _))
    else if c == ``PreSail.sailTryCatch then
      ev `(tactic| (apply AxSpineOk2.rfFSailTryCatch <;> try intro _))
    else if c == ``ForIn.forIn then
      if wrapped then ev `(tactic| (apply AxSpineOk2.rfFRForIn _ rfl <;> intro _ _))
      else ev `(tactic| (apply rfFForeachZMUp _ rfl <;> intro _ _))
    else if c == ``Pure.pure || c == ``FreeM.pure then ev `(tactic| exact True.intro)
    else if c == ``FreeM.impure then
      if wrapped then ev `(tactic| first | exact True.intro | simp only [ExceptT.run])
      else ev `(tactic| first | exact True.intro | simp only [rfF])
    else if c == ``readReg || c == ``writeReg then
      ev `(tactic| simp only [readReg, writeReg, PreSail.readReg, PreSail.writeReg, PreSail.emit])
    else if c == ``letFun then ev `(tactic| dsimp only)
    else if ← isMatcher c then
      try ev `(tactic| split)
      catch _ =>
        let some info ← getMatcherInfo? c | throwError "rff_step: no matcher info"
        let ds := args.extract (info.numParams + 1) (info.numParams + 1 + info.numDiscrs)
        let some d := ds.find? (·.isFVar) | throwError "rff_step: no variable discriminant"
        let x ← d.fvarId!.getUserName
        let _ := x
        let gs ← g.cases d.fvarId!
        replaceMainGoal (gs.map (·.mvarId)).toList
        evalTactic (← `(tactic| all_goals (try dsimp only)))
    else
      try ev `(tactic| unfold $(mkIdent c):ident)
      catch _ => ev `(tactic| exact True.intro)
  | none =>
    if t.isLet then ev `(tactic| dsimp only) else throwError "rff_step: no constant head"

/-- Rocq `rfF_auto`. -/
syntax "rff_auto" : tactic
macro_rules
  | `(tactic| rff_auto) => `(tactic| repeat (first
      | rff_step
      | (refine ⟨?_, ?_⟩)
      | (intro h; rcases h with h | h <;> cases h)
      | (intro _)
      | exact True.intro
      | rfl))

/-! # 3. The register-only callees -/

theorem rfFEffectivePrivilege (acc : MemoryAccessType mem_payload) (ms : BitVec 64)
    (p : Privilege) : rfF (effectivePrivilege acc ms p) := by rff_auto
theorem rfFIsShadowStackAccess (acc : MemoryAccessType mem_payload) :
    rfF (is_shadow_stack_access acc) := by rff_auto
theorem rfFWithinClint (pa : physaddr) (w : Nat) : rfF (within_clint pa w) := by rff_auto
theorem rfFWithinSig (pa : physaddr) (w : Nat) : rfF (within_sig pa w) := by rff_auto
theorem rfFWithinHtifReadable (pa : physaddr) (w : Nat) : rfF (within_htif_readable pa w) := by
  rff_auto
theorem rfFPteIsInvalid (f : BitVec 8) (e : BitVec 10) : rfF (pte_is_invalid f e) := by rff_auto
theorem rfFLookupTLB (w : Nat) (asid : BitVec 16) (vpn : BitVec (w - 12)) :
    rfF (lookup_TLB w asid vpn) := by rff_auto
theorem rfFTlbGetPbmt (ent : TLB_Entry) : rfF (tlb_get_pbmt ent) := by rff_auto
theorem rfFTranslationMode (p : Privilege) : rfF (translationMode p) := by rff_auto
theorem rfFGetSatp (w : Nat) : rfF (get_satp w) := by rff_auto
theorem rfFCurrentlyEnabledZca : rfF (currentlyEnabled .Ext_Zca) := by rff_auto
theorem rfFCurrentlyEnabledZiccif : rfF (currentlyEnabled .Ext_Ziccif) := by rff_auto
theorem rfFReadKindOfFlags (a b c : Bool) : rfF (read_kind_of_flags a b c) := by rff_auto
theorem rfFSatpModeWidthForwards (m : SATPMode) : rfF (satp_mode_width_forwards m) := by rff_auto
theorem rfFSplitMisaligned (pa : physaddr) (w g : Nat) (sp : Splittability) :
    rfF (split_misaligned pa w g sp) := by rff_auto
theorem rfFPmpCheck (pa : physaddr) (w : Nat) (acc : MemoryAccessType mem_payload)
    (p : Privilege) : rfF (pmpCheck pa w acc p) := by rff_auto
theorem rfFWithinMmioReadable (pa : physaddr) (w : Nat) : rfF (within_mmio_readable pa w) := by
  rff_auto
theorem rfFShouldIncMinstret (p : Privilege) : rfF (should_inc_minstret p) := by rff_auto
theorem rfFAddToTLB (w : Nat) (asid : BitVec 16) (vpn : BitVec (w - 12))
    (ppn : BitVec (if (w = 32 : Bool) then 22 else 44))
    (pte : BitVec (if (w = 32 : Bool) then 32 else 64)) (pa : physaddr) (lvl : Nat) (g : Bool) :
    rfF (add_to_TLB w asid vpn ppn pte pa lvl g) := by rff_auto
theorem rfFCheckPTEPermission (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr sum : Bool) (f : BitVec 8) (e : BitVec 10) (x : Unit) :
    rfF (check_PTE_permission acc p mxr sum f e x) := by rff_auto
theorem rfFCheckLeafPte (sv : Nat) (vpn : BitVec (sv - 12)) (acc : MemoryAccessType mem_payload)
    (p : Privilege) (mxr sum : Bool) (pte : BitVec (if (sv = 32 : Bool) then 32 else 64))
    (pa : physaddr) (lvl : Nat) (x : Unit) :
    rfF (check_leaf_pte sv vpn acc p mxr sum pte pa lvl x) := by rff_auto
/-- (Lean-only) `pmaCheck`, the first half of `check_pma_with_pmp_priority`. -/
theorem AxSpineOk2.rfFPmaCheck (pa : physaddr) (w : Nat) (acc : MemoryAccessType mem_payload)
    (pb : page_based_mem_type) (r : Bool) : rfF (pmaCheck pa w acc pb r) := by
  rff_auto
theorem rfFCheckPmaWithPmpPriority (acc : MemoryAccessType mem_payload)
    (pb : page_based_mem_type) (p : Privilege) (pa : physaddr) (w : Nat) (r : Bool) :
    rfF (check_pma_with_pmp_priority acc pb p pa w r) := by
  unfold check_pma_with_pmp_priority
  refine rfFBind _ _ (AxSpineOk2.rfFPmaCheck _ _ _ _ _) (fun x => ?_)
  split
  · trivial
  · exact rfFBind _ _ (rfFPmpCheck _ _ _ _) (fun y => by split <;> trivial)


/-! # 4. `rfM`: `rfF` plus syntactically `ramOk` RAM reads -/

/-- Rocq `rfM` (deviation 3): `rfF` plus RAM reads whose request is `ramOk` in the tree. -/
def rfM {X : Type} : SailM X → Prop
  | .pure _ => True
  | .impure (.error _) _ => True
  | .impure (.ok o) k =>
    match o, k with
    | .regRead r, k => ¬ AxRunClose.pinReg r ∧ ∀ v, rfM (k v)
    | .regWrite r _, k => ¬ AxRunClose.pinReg r ∧ rfM (k PUnit.unit)
    | .memRead n _ req, k => ramOk req.pa req.access_kind n = true ∧ ∀ v, rfM (k v)
    | .memWrite .., _ => False
    | .barrier _, _ => False
    | .cacheOp _, k => rfM (k ())
    | .tlbi _, k => rfM (k ())
    | .translationStart _, k => rfM (k ())
    | .translationEnd _, k => rfM (k ())
    | .takeException _, k => rfM (k ())
    | .returnException _, k => rfM (k ())
    | .cycleCount, k => rfM (k ())
    | .getCycleCount, k => rfM (k (0 : Nat))
    | .message _, k => rfM (k ())
    | .instrAnnounce n w, k => sfAnnB n w = false ∧ rfM (k ())
    | .branchAnnounce _ _, k => rfM (k ())
    | .choose _, _ => True
    | .readRam .., _ => True
    | .writeRam .., _ => True

theorem rfMBind {X Y : Type} (m : SailM X) (f : X → SailM Y) :
    rfM m → (∀ x, rfM (f x)) → rfM (m >>= f) := by
  induction m with
  | pure y => intro _ hf; exact hf y
  | impure call k ih =>
    intro hm hf
    cases call with
    | error e => trivial
    | ok o =>
      show rfM (FreeM.impure (.ok o) (fun v => k v >>= f))
      cases o
      case regRead r => exact ⟨hm.1, fun v => ih v (hm.2 v) hf⟩
      case regWrite r v => exact ⟨hm.1, ih _ hm.2 hf⟩
      case memRead n va req => exact ⟨hm.1, fun v => ih v (hm.2 v) hf⟩
      case instrAnnounce n w => exact ⟨hm.1, ih _ hm.2 hf⟩
      all_goals first | exact hm | trivial | exact ih _ hm hf

theorem execAOfRfM {X : Type} (m : SailM X) :
    rfM m → ∀ s r, exec m s = some r → execA m s = some r := by
  induction m with
  | pure y => intro _ s r h; exact h
  | impure call k ih =>
    intro hrf s r h
    cases call with
    | error e => cases h
    | ok o =>
      cases o
      case regRead r' =>
        simp only [execA, hrf.1, ↓reduceIte]
        exact ih _ (hrf.2 _) _ _ h
      case regWrite r' v =>
        simp only [execA, hrf.1, ↓reduceIte]
        exact ih _ hrf.2 _ _ h
      case instrAnnounce n w =>
        simp only [execA, hrf.1, Bool.false_eq_true, ↓reduceIte]
        exact ih _ hrf.2 _ _ h
      case memRead n va req =>
        have hd := (AxSpineOk.ramOkSpec _ _ _ hrf.1).1
        have hm : mmioAcc req.pa n = false := by simp [mmioAcc, hd]
        rw [execMemRead n va req k s hm] at h
        simp only [execA, hrf.1, ↓reduceIte]
        split at h
        · rename_i w hw; rw [hw]; exact ih _ (hrf.2 _) _ _ h
        · cases h
      case memWrite => exact hrf.elim
      case barrier => exact hrf.elim
      all_goals first | cases h | exact ih _ hrf _ _ h

theorem execAReadRamPlain (addr : BitVec 64) (n : Nat) (w : BitVec (8 * n)) (s : ExecSt)
    (hdev : devAddr addr = false) (hwf : paZ addr + n ≤ 2 ^ 64)
    (h : exec (read_ram .Read_plain (.Physaddr addr) n false) s = some ((w, default_meta), s)) :
    execA (read_ram .Read_plain (.Physaddr addr) n false) s = some ((w, default_meta), s) := by
  refine execAOfRfM _ ?_ s _ h
  simp only [read_ram, PreSail.sail_mem_read, PreSail.emit]
  refine ⟨?_, fun v => ?_⟩
  · simp only [ramOk, hdev, Bool.not_false, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨rfl, hwf⟩
  · rcases v with ⟨x, y⟩ | a <;> trivial

theorem execAAssertExpTrue (msg : String) (s : ExecSt) :
    execA (assert true msg : SailM Unit) s = some ((), s) := rfl

/-- Rocq `toA`: turn an SC fact `exec m s = some r` (hypothesis `H`) into its `execA` twin, the
register-only footprint by `rff_auto`. -/
syntax "to_a " ident : tactic
macro_rules
  | `(tactic| to_a $H:ident) =>
    `(tactic| replace $H:ident := execAOfRfF _ (by rff_auto) _ _ $H:ident)

end Weak

namespace Weak
open MachCSL Sail LeanRV64D LeanRV64D.Functions
example (pa : physaddr) (s : ExecSt) (b : Bool) (h : exec (within_clint pa 4) s = some (b, s)) :
    execA (within_clint pa 4) s = some (b, s) := by
  to_a h
  exact h
end Weak
