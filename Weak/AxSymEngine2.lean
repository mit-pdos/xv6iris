/-
Weak: **the SC engine's structure ported onto `AxSymEngine.EvA`**, and
`AxReuseProbe2.XGprWrite` PROVED from it.

Rocq: `iris/AxSymEngine2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 `rf0`: the SYNTACTIC register-only footprint of a tree (all branches: register reads/writes off
the pins and silent outcomes only).  `rf0EvA`: `rf0` + an `exec` fact ⇒ an `EvA` fact with the SAME
value and state — how an SC `exec` certificate is REUSED verbatim.  Instances
`rf0ExecuteRTYPEADD`, `rf0ExecuteADDIW` (symbolic registers).
§2 THE SPINE MIRROR (the `EvA` twins of the SC `run_hart_active` RVC progress lemma and
`exec_riscv_step_hart_active` + the tick): `EvAHartActiveRvc`, `EvATryStepActive`,
`EvARiscvStep` — SYMBOLIC state throughout, the sub-facts as hypotheses.
§3 register bookkeeping (`gidx`, `gprRegNe`, `ctrlFree`, `keepRegs`).
§4 `SpineOk ctrlOk textAt img`: the instruction-INDEPENDENT sub-facts at every state of the control
regime (dispatch with the demonic pin reads, THE FETCH "textAt pc h ⇒ fetch returns F_RVC h",
inc/lpad/zca/tick helpers, frame conditions).  `textOkD`: the WPd reading of
`instr pc true ins`.  `spineCert`: SC exec certificate + footprint + spine ⇒ `EvA (riscvStep tick)`.
§5 `XGprWriteHolds`: THE LIFTING THEOREM X of `AxReuseProbe2`, UNCHANGED, at `ctrlOk`/`textOkD`,
from `SpineOk` + the bridge's instance premises; `wpCmvDReal`/`wpCaddiwDReal`.  §5b `spLpadOf`.
§6 NON-VACUITY: `evb` (boolean `EvA` checker, `evbSound`); at the concrete M-mode state
`AxEpiProbe.tAt 0x80000002` with the image holding `c.mv a0, ra`: `nvCert` — the bridge's
certificate premise for the REAL `riscvStep`, BOTH ticks, all pin answers (post: PC+2, a0 = ra);
`nvDisp`/`nvFetch`/`nvLpad`/`nvZca`/`nvDecodeExpand`/`nvRf0` — each `SpineOk`/`textOkD` field's
instance at that state.  NOT a proof of `SpineOk` (a ∀-state interface): that is THE REMAINING
PIECE.  `textOkD` requires `is_rvc = true` (the 4-byte arm is not done, as in Rocq).

## Deviations from Rocq

1. O2 STAGE C (as `AxSymEngine` deviation 1): `EvA.evMrd` covers fetches too, so `evb` drops
   Rocq's `ak_coh` test; the bridge's section premise `Hloc` is DROPPED from §5 (only `Htext`,
   `Hflow`; `Hend` is `postLiftingΦ0`).
2. THE PINS (`AxRunClose` deviation 1): `seip_reg` ↦ `AxRunClose.pinReg` (`sig_seip` or
   `sig_meip`) in `rf0`, `SpineOk.spSeip` and every `regs_agree`; `evb` answers a pin read with
   both pins set to `0#1`, then both to `1#1` (Rocq: `sig_seip` false/true).
3. Q7: `rf0` of an `instrAnnounce n w` requires `sfAnnB n w = false` (as `EvA.evIa`).
4. LEAN-SAIL (as `AxSymEngine` deviation 4): `rf0`/`evb` are on `SailM`; a failure node is
   `False`/`false` (Rocq's extra outcomes fall in `_ => False`).  The early-return monad is
   `ExceptT … SailM`: `EvALiftRAny`'s post is the `Except` match of `EvALiftR`, `EvAFactLift` is
   over `ExceptT.run (liftM m >>= f)`.  Rocq's tactics `ev_step`/`ev_go`/`ev_use` ↦ the
   Lean-only kit lemmas `AxSymEngine2.ev*` plus the tactic `ax_sym2_ev_go`; `rf0_solve` ↦
   `ax_sym2_rf0_solve`; `nseip` ↦ `AxSymEngine2.notPin`; `lk` ↦ `RegFile.set_same`/`set_other`
   rewrites.  Lean's `do` produces join points and nested binds: the kit has `evRAssoc`/
   `evFactAssoc` (`bind_assoc`).
5. REGISTERS (Lean's are an enum; `AxReuseProbe2` deviation 1): `R_bitvector_64 (gpr_of_Z (uint
   i))` ↦ the Lean-only `AxSymEngine2.gprReg i`; `gidx` is over `Register`, `gidxGpr` is stated
   for a `BitVec 5` index with `toNat ≠ 0` (Rocq `0 < a < 32`); `ctrlFree`'s GPR disjunct is
   `r ∈ uxaGprs`; `keepRegs`'s and `Good`'s GPR clauses are over `uxaXget` at `BitVec 5` indices
   (`Z.eqb (uint r) (uint rd)` ↦ `r = rd`); the exec certificate's
   `set_reg s (gpr rd) (regval_into_reg wval)` ↦ `s.setGpr rd wval`, `gpr_agree` ↦ `gprAgree`;
   `uint5_cases` is stated on `toNat`.
6. TYPES (as `AxSymEngine` deviation 5): `mstate` ↦ `ExecSt`, `register_lookup r rs` ↦ `rs r`,
   `set_reg` ↦ `ExecSt.setReg`, `add_vec_int pc 2` ↦ `BitVec.addInt pc 2` (defeq to
   `pc + instrLen true`, which `XGprWrite` uses), `zero_extend' 32 h` ↦ `zero_extend (m := 32) h`,
   `eq_vec a b = false` ↦ `(a == b) = false`, `Z → option (bv 8)` ↦ `Image`.
7. §5: Rocq's `Definition wp_cmv_d_real := wp_cmv_d … X_gpr_write_holds` (and `wp_caddiw_d_real`)
   ↦ theorems restating `AxReuseProbe2.wpCmvD`/`wpCaddiwD` at `textOk := textOkD img ctrlOk
   textAt`; `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` (any `hlc`); `GenId` dropped (as
   `AxReuseProbe2` deviation 4).
8. §6: `vm_compute; reflexivity` ↦ `decide +kernel`; `mword1_cases` is over `BitVec 1`;
   `nv_post`/`nv_fetch` use `==` on bit vectors; `nv_decode_expand`'s `bool_decide (ins = RTYPE
   (…))` ↦ a match projection on the three register indices (the model's `instruction` has no
   `BEq`/`DecidableEq`).  All checks take well under a second; the file builds in about 4 s.

**Rocq → Lean name map.**  `rf0` `rf0`, `rf0_EvA` `rf0EvA`, `rf0_bind` `rf0Bind`, `rf0_bind0`
`rf0Bind0`, `uint5_cases` `uint5Cases`, `rf0_rX_bits` `rf0RXBits`, `rf0_wX_bits` `rf0WXBits`,
`rf0_execute_RTYPE_ADD` `rf0ExecuteRTYPEADD`, `rf0_execute_ADDIW` `rf0ExecuteADDIW`,
`EvA_liftR_any` `EvALiftRAny`, `EvA_fact` `EvAFact`, `EvA_fact_lift` `EvAFactLift`,
`EvA_hart_active_rvc` `EvAHartActiveRvc`, `tfinal` `tfinal`, `EvA_try_step_active`
`EvATryStepActive`, `EvA_riscv_step` `EvARiscvStep`, `gidx` `gidx`, `gidx_gpr` `gidxGpr`,
`gpr_reg_ne` `gprRegNe`, `gpr_ne_simple` `gprNeSimple`, `ctrl_free` `ctrlFree`, `keep_regs`
`keepRegs`, `SpineOk` `SpineOk` (fields `sp_seip` `spSeip`, `sp_hart` `spHart`, `sp_frame`
`spFrame`, `sp_inc` `spInc`, `sp_disp` `spDisp`, `sp_fetch` `spFetch`, `sp_lpad` `spLpad`,
`sp_zca` `spZca`, `sp_tick` `spTick`), `text_ok_d` `textOkD`, `Good` `Good`, `spine_cert`
`spineCert`, `post_lifting_Φ0` `postLiftingΦ0`, `X_gpr_write_holds` `XGprWriteHolds`,
`wp_cmv_d_real` `wpCmvDReal`, `wp_caddiw_d_real` `wpCaddiwDReal`, `sp_lpad_of` `spLpadOf`,
`mword1_cases` `mword1Cases`, `evb` `evb`, `evb_sound` `evbSound`, `nv_pc` `nvPc`, `nv_img`
`nvImg`, `nv_t` `nvT`, `nv_post` `nvPost`, `nv_step_false` `nvStepFalse`, `nv_step_true`
`nvStepTrue`, `nv_cert` `nvCert`, `nv_eqpost` `nvEqpost`, `nv_disp` `nvDisp`, `nv_fetch`
`nvFetch`, `nv_lpad` `nvLpad`, `nv_zca` `nvZca`, `nv_decode_expand` `nvDecodeExpand`, `nv_rf0`
`nvRf0`.  None is in the duplicated-name table.  Lean-only (file-qualified `AxSymEngine2.*`):
`notPin`, `rf0Pure`, `rf0ReadPure`, `rf0WritePure`, `evRBind`, `evInstrAnnounce16`, `evRPure`,
`evFactRead`, `evFactWrite`, `evFactPure`, `evFactQ`, `evFactUse`, `evRRead`, `evRWrite`,
`evRPureBind`, `evRUse`, `evRAnn16`, `evFactAssoc`, `evRAssoc`, `gprReg`, `gprNotPin`,
`uxaXgetAgree`, `uxaXgetSetNe`, `setGprRegsNe`, `ctrlOkSetGpr`.

**Dropped:** nothing (Rocq 48 definitions/lemmas + 6 Ltacs; Lean 48 + 2 tactics + 25 Lean-only).
**Not ported:** the `Print Assumptions`/`Check` lines (the lint's axiom check covers them).
-/
import Weak.AxSymEngine
import Weak.AxReuseProbe2
import Weak.AxEpiProbe
import Weak.AxFetch3c

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 1. The syntactic register-only footprint -/

def rf0 {X : Type} : SailM X → Prop
  | .pure _ => True
  | .impure (.error _) _ => False
  | .impure (.ok o) k =>
    match o, k with
    | .regRead r, k => ¬ AxRunClose.pinReg r ∧ ∀ v, rf0 (k v)
    | .regWrite r _, k => ¬ AxRunClose.pinReg r ∧ rf0 (k PUnit.unit)
    | .instrAnnounce n w, k => sfAnnB n w = false ∧ rf0 (k ())
    | .branchAnnounce _ _, k => rf0 (k ())
    | .cacheOp _, k => rf0 (k ())
    | .tlbi _, k => rf0 (k ())
    | .takeException _, k => rf0 (k ())
    | .returnException _, k => rf0 (k ())
    | .translationStart _, k => rf0 (k ())
    | .translationEnd _, k => rf0 (k ())
    | .cycleCount, k => rf0 (k ())
    | .message _, k => rf0 (k ())
    | .getCycleCount, k => rf0 (k (0 : Nat))
    | _, _ => False

/-- (Lean-only) A register off both pins. -/
theorem AxSymEngine2.notPin (r : Register) (h1 : r ≠ .sig_seip) (h2 : r ≠ .sig_meip) :
    ¬ AxRunClose.pinReg r := by
  rintro (h | h) <;> contradiction

theorem rf0EvA (img : Image) {X : Type} (QE : Sail.Error exception → ExecSt → Prop) (m : SailM X) :
    rf0 m → ∀ t x t', exec m t = some (x, t') →
      EvA img QE (fun x' t'' => x' = x ∧ t'' = t') m t := by
  induction m with
  | pure y =>
    intro _ t x t' he
    simp only [exec, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact .evRet _ _ ⟨rfl, rfl⟩
  | impure call k ih =>
    intro hrf t x t' he
    cases call with
    | error e => exact hrf.elim
    | ok o =>
      cases o
      case regRead r =>
        obtain ⟨hp, hk⟩ := hrf
        exact .evRd r k t (fun h => absurd h hp) (fun _ => ih _ (hk _) t x t' he)
      case regWrite r v =>
        obtain ⟨hp, hk⟩ := hrf
        exact .evWr r v k t hp (ih _ hk _ x t' he)
      case instrAnnounce n w =>
        obtain ⟨hp, hk⟩ := hrf
        exact .evIa n w k t hp (ih _ hk t x t' he)
      case branchAnnounce n a => exact .evBa n a k t (ih _ hrf t x t' he)
      case cacheOp c => exact .evCo c k t (ih _ hrf t x t' he)
      case tlbi c => exact .evTl c k t (ih _ hrf t x t' he)
      case takeException c => exact .evTe c k t (ih _ hrf t x t' he)
      case returnException c => exact .evRx c k t (ih _ hrf t x t' he)
      case translationStart c => exact .evTs c k t (ih _ hrf t x t' he)
      case translationEnd c => exact .evTx c k t (ih _ hrf t x t' he)
      case cycleCount => exact .evCc k t (ih _ hrf t x t' he)
      case message c => exact .evMsg c k t (ih _ hrf t x t' he)
      case getCycleCount => exact .evGcc k t (ih _ hrf t x t' he)
      all_goals exact hrf.elim

theorem rf0Bind {X Y : Type} (m : SailM X) (f : X → SailM Y) :
    rf0 m → (∀ x, rf0 (f x)) → rf0 (m >>= f) := by
  induction m with
  | pure y => intro _ hf; exact hf y
  | impure call k ih =>
    intro hm hf
    cases call with
    | error e => exact hm.elim
    | ok o =>
      cases o
      case regRead r => exact ⟨hm.1, fun v => ih v (hm.2 v) hf⟩
      case regWrite r v => exact ⟨hm.1, ih _ hm.2 hf⟩
      case instrAnnounce n w => exact ⟨hm.1, ih _ hm.2 hf⟩
      case branchAnnounce n a => exact ih _ hm hf
      case cacheOp c => exact ih _ hm hf
      case tlbi c => exact ih _ hm hf
      case takeException c => exact ih _ hm hf
      case returnException c => exact ih _ hm hf
      case translationStart c => exact ih _ hm hf
      case translationEnd c => exact ih _ hm hf
      case cycleCount => exact ih _ hm hf
      case message c => exact ih _ hm hf
      case getCycleCount => exact ih _ hm hf
      all_goals exact hm.elim

theorem rf0Bind0 {Y : Type} (m : SailM Unit) (n : SailM Y) :
    rf0 m → rf0 n → rf0 (m >>= fun _ => n) :=
  fun hm hn => rf0Bind m (fun _ => n) hm (fun _ => hn)

/-- (Lean-only) `rf0` leaves. -/
theorem AxSymEngine2.rf0Pure {X : Type} (x : X) : rf0 (FreeM.pure x : SailM X) := trivial

theorem AxSymEngine2.rf0ReadPure {X : Type} (r : Register) (h : ¬ AxRunClose.pinReg r)
    (f : RegisterType r → X) :
    rf0 (FreeM.impure (.ok (.regRead r)) (fun v => FreeM.pure (f v)) : SailM X) :=
  (⟨h, fun _ => trivial⟩ : ¬ AxRunClose.pinReg r ∧ ∀ _ : RegisterType r, True)

theorem AxSymEngine2.rf0WritePure {X : Type} (r : Register) (v : RegisterType r)
    (h : ¬ AxRunClose.pinReg r) (x : X) :
    rf0 (FreeM.impure (.ok (.regWrite r v)) (fun _ => FreeM.pure x) : SailM X) :=
  (⟨h, trivial⟩ : ¬ AxRunClose.pinReg r ∧ True)

theorem uint5Cases (i : BitVec 5) :
    i.toNat = 0 ∨ i.toNat = 1 ∨ i.toNat = 2 ∨ i.toNat = 3 ∨ i.toNat = 4 ∨ i.toNat = 5 ∨
    i.toNat = 6 ∨ i.toNat = 7 ∨ i.toNat = 8 ∨ i.toNat = 9 ∨ i.toNat = 10 ∨ i.toNat = 11 ∨
    i.toNat = 12 ∨ i.toNat = 13 ∨ i.toNat = 14 ∨ i.toNat = 15 ∨ i.toNat = 16 ∨ i.toNat = 17 ∨
    i.toNat = 18 ∨ i.toNat = 19 ∨ i.toNat = 20 ∨ i.toNat = 21 ∨ i.toNat = 22 ∨ i.toNat = 23 ∨
    i.toNat = 24 ∨ i.toNat = 25 ∨ i.toNat = 26 ∨ i.toNat = 27 ∨ i.toNat = 28 ∨ i.toNat = 29 ∨
    i.toNat = 30 ∨ i.toNat = 31 := by
  have := i.isLt
  simp only [Nat.reducePow] at this
  omega

theorem rf0RXBits (i : BitVec 5) : rf0 (rX_bits (.Regidx i)) := by
  rcases uxa_bv5_cases i with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact AxSymEngine2.rf0Pure _
    | exact AxSymEngine2.rf0ReadPure _ (AxSymEngine2.notPin _ (by decide) (by decide)) _

theorem rf0WXBits (i : BitVec 5) (v : BitVec 64) : rf0 (wX_bits (.Regidx i) v) := by
  rcases uxa_bv5_cases i with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact AxSymEngine2.rf0Pure _
    | exact AxSymEngine2.rf0WritePure _ _ (AxSymEngine2.notPin _ (by decide) (by decide)) _

/-- Rocq `rf0_solve` (file-qualified tactic name). -/
macro "ax_sym2_rf0_solve" : tactic => `(tactic| repeat (first
  | exact AxSymEngine2.rf0Pure _
  | exact rf0RXBits _
  | exact rf0WXBits _ _
  | intro _
  | apply rf0Bind))

theorem rf0ExecuteRTYPEADD (rs2 rs1 rd : BitVec 5) :
    rf0 (execute (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .ADD))) := by
  show rf0 (execute_RTYPE (.Regidx rs2) (.Regidx rs1) (.Regidx rd) .ADD)
  unfold execute_RTYPE
  ax_sym2_rf0_solve

theorem rf0ExecuteADDIW (rs1 rd : BitVec 5) (imm : BitVec 12) :
    rf0 (execute (.ADDIW (imm, .Regidx rs1, .Regidx rd))) := by
  show rf0 (execute_ADDIW imm (.Regidx rs1) (.Regidx rd))
  unfold execute_ADDIW
  ax_sym2_rf0_solve

/-! # 2. THE SPINE MIRROR -/

section spine
variable (img : Image)

theorem EvALiftRAny {R X : Type} (QE : Sail.Error exception → ExecSt → Prop)
    (Q : X → ExecSt → Prop) (m : SailM X) (t : ExecSt) :
    EvA img (fun _ _ => False) Q m t →
    EvA img QE
      (fun (r : Except (Sail.Error exception ⊕ R) X) t' =>
        match r with
        | .ok x => Q x t'
        | .error _ => False)
      (ExceptT.run (liftM m : SailME R X)) t := by
  intro H
  exact EvAMono img _ _ _ _ _ t (fun _ _ h => h.elim) (fun _ _ h => h) (EvALiftR img _ Q m t H)

theorem EvAFact {X Y : Type} (QE : Sail.Error exception → ExecSt → Prop) (P : X → ExecSt → Prop)
    (Q : Y → ExecSt → Prop) (m : SailM X) (f : X → SailM Y) (t : ExecSt) :
    EvA img QE P m t → (∀ x t', P x t' → EvA img QE Q (f x) t') →
    EvA img QE Q (m >>= f) t := by
  intro Hm Hf
  exact EvABind img QE Q m f t (EvAMono img _ _ _ _ m t (fun _ _ h => h) Hf Hm)

/-- (Lean-only) The early-return monad's bind, through `ExceptT.run`. -/
theorem AxSymEngine2.evRBind {R X Y : Type} (QE : Sail.Error exception → ExecSt → Prop)
    (Q : Except (Sail.Error exception ⊕ R) X → ExecSt → Prop) (m : SailME R Y)
    (f : Y → SailME R X) (t : ExecSt) :
    EvA img QE (fun r t' => match r with
      | .ok a => EvA img QE Q (ExceptT.run (f a)) t'
      | .error e => Q (.error e) t') (ExceptT.run m) t →
    EvA img QE Q (ExceptT.run (m >>= f)) t := by
  intro H
  rw [ExceptT.run_bind]
  apply EvABind
  refine EvAMono img _ _ _ _ _ t (fun _ _ h => h) ?_ H
  intro r t' h
  cases r with
  | ok a => exact h
  | error e => exact .evRet _ _ h

theorem EvAFactLift {R X Y : Type} (QE : Sail.Error exception → ExecSt → Prop)
    (P : X → ExecSt → Prop) (Q : Except (Sail.Error exception ⊕ R) Y → ExecSt → Prop)
    (m : SailM X) (f : X → SailME R Y) (t : ExecSt) :
    EvA img (fun _ _ => False) P m t →
    (∀ x t', P x t' → EvA img QE Q (ExceptT.run (f x)) t') →
    EvA img QE Q (ExceptT.run (liftM m >>= f)) t := by
  intro Hm Hf
  apply AxSymEngine2.evRBind
  refine EvAMono img _ _ _ _ _ t (fun _ _ h => h) ?_ (EvALiftRAny img QE P m t Hm)
  intro r t' h
  cases r with
  | ok a => exact Hf a t' h
  | error e => exact h.elim

/-- (Lean-only) The announce of a compressed instruction is silent (never an sfence word). -/
theorem AxSymEngine2.evInstrAnnounce16 (QE : Sail.Error exception → ExecSt → Prop) (h : BitVec 16)
    (t : ExecSt) : EvA img QE (fun _ t' => t' = t) (instr_announce h : SailM Unit) t :=
  .evIa 16 h _ t rfl (.evRet _ _ rfl)

/-- (Lean-only) `pure` in the early-return monad. -/
theorem AxSymEngine2.evRPure {R X : Type} (QE : Sail.Error exception → ExecSt → Prop)
    (Q : Except (Sail.Error exception ⊕ R) X → ExecSt → Prop) (x : X) (t : ExecSt) :
    Q (.ok x) t → EvA img QE Q (ExceptT.run (pure x : SailME R X)) t :=
  fun h => .evRet _ _ h

end spine

/-! ### (Lean-only) the stepping kit (Rocq's `ev_step`/`ev_go`/`ev_use` tactics, as lemmas) -/

section kit
variable {img : Image} {QE : Sail.Error exception → ExecSt → Prop}

theorem AxSymEngine2.evFactRead {Y : Type} {Q : Y → ExecSt → Prop} {r : Register}
    {f : RegisterType r → SailM Y} {t : ExecSt} (hr : ¬ AxRunClose.pinReg r)
    (H : EvA img QE Q (f (t.regs r)) t) : EvA img QE Q (readReg r >>= f) t :=
  EvABind img QE Q _ f t (EvAReadReg img QE r _ t hr H)

theorem AxSymEngine2.evFactWrite {Y : Type} {Q : Y → ExecSt → Prop} {r : Register}
    {v : RegisterType r} {f : PUnit → SailM Y} {t : ExecSt} (hr : ¬ AxRunClose.pinReg r)
    (H : EvA img QE Q (f PUnit.unit) (t.setReg r v)) : EvA img QE Q (writeReg r v >>= f) t :=
  EvABind img QE Q _ f t (EvAWriteReg img QE _ r v t hr H)

theorem AxSymEngine2.evFactPure {X Y : Type} {Q : Y → ExecSt → Prop} {x : X}
    {f : X → SailM Y} {t : ExecSt} (H : EvA img QE Q (f x) t) :
    EvA img QE Q (pure x >>= f) t := H

theorem AxSymEngine2.evFactQ {X Y : Type} {P : X → ExecSt → Prop} {Q : Y → ExecSt → Prop}
    {m : SailM X} {f : X → SailM Y} {t : ExecSt} (Hm : EvA img (fun _ _ => False) P m t)
    (Hf : ∀ x t', P x t' → EvA img QE Q (f x) t') : EvA img QE Q (m >>= f) t :=
  EvABind img QE Q m f t (EvAMono img _ _ _ _ m t (fun _ _ h => h.elim) Hf Hm)

theorem AxSymEngine2.evFactUse {X Y : Type} {Q : Y → ExecSt → Prop} {m : SailM X}
    {f : X → SailM Y} {t t1 : ExecSt} {a : X}
    (Hm : EvA img (fun _ _ => False) (fun x t' => x = a ∧ t' = t1) m t)
    (H : EvA img QE Q (f a) t1) : EvA img QE Q (m >>= f) t :=
  AxSymEngine2.evFactQ Hm (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact H)

theorem AxSymEngine2.evRRead {R X : Type} {Q : Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {r : Register} {f : RegisterType r → SailME R X} {t : ExecSt} (hr : ¬ AxRunClose.pinReg r)
    (H : EvA img QE Q (ExceptT.run (f (t.regs r))) t) :
    EvA img QE Q (ExceptT.run (liftM (readReg r) >>= f)) t :=
  EvAFactLift img QE (fun x t' => x = t.regs r ∧ t' = t) Q _ f t
    (EvAReadReg img _ r _ t hr ⟨rfl, rfl⟩) (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact H)

theorem AxSymEngine2.evRWrite {R X : Type} {Q : Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {r : Register} {v : RegisterType r} {f : PUnit → SailME R X} {t : ExecSt}
    (hr : ¬ AxRunClose.pinReg r) (H : EvA img QE Q (ExceptT.run (f PUnit.unit)) (t.setReg r v)) :
    EvA img QE Q (ExceptT.run (liftM (writeReg r v) >>= f)) t :=
  EvAFactLift img QE (fun _ t' => t' = t.setReg r v) Q _ f t
    (EvAWriteReg img _ _ r v t hr rfl) (fun _ _ h => by subst h; exact H)

theorem AxSymEngine2.evRPureBind {R X Y : Type}
    {Q : Except (Sail.Error exception ⊕ R) X → ExecSt → Prop} {x : Y} {f : Y → SailME R X}
    {t : ExecSt} (H : EvA img QE Q (ExceptT.run (f x)) t) :
    EvA img QE Q (ExceptT.run (pure x >>= f)) t := H

theorem AxSymEngine2.evRUse {R X Y : Type} {Q : Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {m : SailM Y} {f : Y → SailME R X} {t t1 : ExecSt} {a : Y}
    (Hm : EvA img (fun _ _ => False) (fun x t' => x = a ∧ t' = t1) m t)
    (H : EvA img QE Q (ExceptT.run (f a)) t1) :
    EvA img QE Q (ExceptT.run (liftM m >>= f)) t :=
  EvAFactLift img QE _ Q m f t Hm (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact H)

theorem AxSymEngine2.evRAnn16 {R X : Type} {Q : Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {h : BitVec 16} {f : Unit → SailME R X} {t : ExecSt}
    (H : EvA img QE Q (ExceptT.run (f ())) t) :
    EvA img QE Q (ExceptT.run (liftM (instr_announce h : SailM Unit) >>= f)) t :=
  EvAFactLift img QE (fun _ t' => t' = t) Q _ f t (AxSymEngine2.evInstrAnnounce16 img _ h t)
    (fun _ _ h => by subst h; exact H)

theorem AxSymEngine2.evFactAssoc {X Y Z : Type} {Q : Z → ExecSt → Prop} {m : SailM X}
    {f : X → SailM Y} {g : Y → SailM Z} {t : ExecSt}
    (H : EvA img QE Q (m >>= fun x => f x >>= g) t) : EvA img QE Q ((m >>= f) >>= g) t := by
  rw [bind_assoc]; exact H

theorem AxSymEngine2.evRAssoc {R X Y Z : Type}
    {Q : Except (Sail.Error exception ⊕ R) Z → ExecSt → Prop} {m : SailME R X}
    {f : X → SailME R Y} {g : Y → SailME R Z} {t : ExecSt}
    (H : EvA img QE Q (ExceptT.run (m >>= fun x => f x >>= g)) t) :
    EvA img QE Q (ExceptT.run ((m >>= f) >>= g)) t := by
  rw [bind_assoc]; exact H

end kit

/-- Rocq's `ev_go` (file-qualified tactic name): run the register reads/writes, `pure`s and
closed guards. -/
macro "ax_sym2_ev_go" : tactic => `(tactic| repeat (first
  | ((with_reducible refine AxSymEngine2.evRRead ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | ((with_reducible refine AxSymEngine2.evRWrite ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | with_reducible refine AxSymEngine2.evRAnn16 ?_
  | with_reducible refine AxSymEngine2.evRPureBind ?_
  | with_reducible refine AxSymEngine2.evRAssoc ?_
  | with_reducible refine AxSymEngine2.evFactAssoc ?_
  | ((with_reducible refine AxSymEngine2.evFactRead ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | ((with_reducible refine AxSymEngine2.evFactWrite ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | with_reducible refine AxSymEngine2.evFactPure ?_
  | (simp (config := { decide := true }) only [↓reduceIte, Bool.false_eq_true,
      get_config_print_instr, get_config_rvfi, ext_fetch_hook, RETIRE_SUCCESS, tick_pc,
      hart_is_active, assert, PreSail.assert])))

section spine2
variable (img : Image)

theorem EvAHartActiveRvc (t : ExecSt) (h : BitVec 16) (i0 ins : instruction) (pc : BitVec 64)
    (Qx : ExecSt → Prop) :
    EvA img (fun _ _ => False) (fun r t' => r = none ∧ t' = t)
      (dispatchInterrupt (t.regs .cur_privilege)) t →
    EvA img (fun _ _ => False) (fun r t' => r = .F_RVC h ∧ t' = t) (fetch ()) t →
    EvA img (fun _ _ => False) (fun x t' => x = i0 ∧ t' = t) (ext_decode_compressed h) t →
    EvA img (fun _ _ => False) (fun x t' => x = false ∧ t' = t) (is_landing_pad_expected ()) t →
    EvA img (fun _ _ => False) (fun x t' => x = true ∧ t' = t) (currentlyEnabled .Ext_Zca) t →
    t.regs .PC = pc →
    EvA img (fun _ _ => False)
      (fun x t' => x = .ExecuteAs ins ∧ t' = t.setReg .nextPC (BitVec.addInt pc 2))
      (execute i0) (t.setReg .nextPC (BitVec.addInt pc 2)) →
    EvA img (fun _ _ => False) (fun x t' => x = RETIRE_SUCCESS ∧ Qx t') (execute ins)
      (t.setReg .nextPC (BitVec.addInt pc 2)) →
    EvA img (fun _ _ => False)
      (fun x t' => x = .Step_Execute (RETIRE_SUCCESS, zero_extend (m := 32) h) ∧ Qx t')
      (run_hart_active 0) t := by
  intro Hdisp Hfetch Hdec Hlpad Hzca HPC Hexp Hexec
  subst HPC
  unfold run_hart_active
  apply EvACatchEarlyReturn
  ax_sym2_ev_go
  refine AxSymEngine2.evRUse Hdisp ?_
  ax_sym2_ev_go
  refine AxSymEngine2.evRUse Hfetch ?_
  ax_sym2_ev_go
  refine AxSymEngine2.evRUse Hdec ?_
  ax_sym2_ev_go
  refine AxSymEngine2.evRUse Hlpad ?_
  ax_sym2_ev_go
  refine AxSymEngine2.evRUse Hzca ?_
  ax_sym2_ev_go
  refine AxSymEngine2.evRUse Hexp ?_
  ax_sym2_ev_go
  refine EvAFactLift img _ _ _ _ _ _ Hexec ?_
  rintro _ t' ⟨rfl, hq⟩
  exact .evRet _ _ ⟨rfl, hq⟩

def tfinal (b : Bool) (tx : ExecSt) : ExecSt :=
  let sTick := tx.setReg .PC (tx.regs .nextPC)
  if b then sTick.setReg .minstret (BitVec.addInt (sTick.regs .minstret) 1) else sTick

theorem EvATryStepActive (t : ExecSt) (b : Bool) (bits : BitVec 32) (Qx Qf : ExecSt → Prop) :
    EvA img (fun _ _ => False) (fun x t' => x = b ∧ t' = t)
      (should_inc_minstret (t.regs .cur_privilege)) t →
    (t.setReg .minstret_increment b).regs .hart_state = .HART_ACTIVE () →
    EvA img (fun _ _ => False) (fun x t' => x = .Step_Execute (RETIRE_SUCCESS, bits) ∧ Qx t')
      (run_hart_active 0) (t.setReg .minstret_increment b) →
    (∀ tx, Qx tx → tx.regs .hart_state = .HART_ACTIVE () ∧
      tx.regs .minstret_increment = b ∧ Qf (tfinal b tx)) →
    EvA img (fun _ _ => False) (fun x t' => x = false ∧ Qf t') (try_step 0 false) t := by
  intro Hsi Hha Hrun Hfin
  unfold try_step
  dsimp only
  ax_sym2_ev_go
  refine AxSymEngine2.evFactUse Hsi ?_
  ax_sym2_ev_go
  apply EvABind
  ax_sym2_ev_go
  simp only [Hha]
  refine EvAMono img _ _ _ _ _ _ (fun _ _ h => h) ?_ Hrun
  rintro _ tx ⟨rfl, HQ⟩
  obtain ⟨Hhx, Hmix, HQf⟩ := Hfin tx HQ
  ax_sym2_ev_go
  simp only [Hhx]
  ax_sym2_ev_go
  simp only [Hhx]
  ax_sym2_ev_go
  have hmi : (tx.setReg .PC (tx.regs .nextPC)).regs .minstret_increment = b := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]
    exact Hmix
  simp only [hmi]
  cases b <;> ax_sym2_ev_go <;> exact .evRet _ _ ⟨rfl, HQf⟩

theorem EvARiscvStep (tick : Bool) (t : ExecSt) (Qf Q : ExecSt → Prop) :
    EvA img (fun _ _ => False) (fun _ t' => Qf t') (try_step 0 false) t →
    (∀ t', Qf t' → if tick then EvA img (fun _ _ => False) (fun _ t'' => Q t'') (tick_clock ()) t'
      else Q t') →
    EvA img (fun _ _ => False) (fun _ t' => Q t') (riscvStep tick) t := by
  intro Ht Hk
  unfold riscvStep
  refine EvAFact img _ _ _ _ _ t Ht ?_
  intro _ t' Hq
  have Hk' := Hk t' Hq
  cases tick with
  | true => exact Hk'
  | false => exact .evRet _ _ Hk'

end spine2


/-! # 3. Register bookkeeping -/

/-- (Lean-only) Rocq `R_bitvector_64 (gpr_of_Z (uint i))`: the GPR register of an index (`x0`,
which has no register, maps to `x31`; every use takes `i.toNat ≠ 0`). -/
def AxSymEngine2.gprReg (i : BitVec 5) : Register := uxaGprs.getD (i.toNat - 1) .x31

def gidx (r : Register) : Nat :=
  if r = .x1 then 1 else if r = .x2 then 2 else if r = .x3 then 3 else if r = .x4 then 4
  else if r = .x5 then 5 else if r = .x6 then 6 else if r = .x7 then 7 else if r = .x8 then 8
  else if r = .x9 then 9 else if r = .x10 then 10 else if r = .x11 then 11
  else if r = .x12 then 12 else if r = .x13 then 13 else if r = .x14 then 14
  else if r = .x15 then 15 else if r = .x16 then 16 else if r = .x17 then 17
  else if r = .x18 then 18 else if r = .x19 then 19 else if r = .x20 then 20
  else if r = .x21 then 21 else if r = .x22 then 22 else if r = .x23 then 23
  else if r = .x24 then 24 else if r = .x25 then 25 else if r = .x26 then 26
  else if r = .x27 then 27 else if r = .x28 then 28 else if r = .x29 then 29
  else if r = .x30 then 30 else if r = .x31 then 31 else 0

theorem gidxGpr (a : BitVec 5) : a.toNat ≠ 0 → gidx (AxSymEngine2.gprReg a) = a.toNat := by
  rcases uxa_bv5_cases a with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals intro h; first | exact absurd rfl h | decide

theorem gprRegNe (r rd : BitVec 5) :
    r.toNat ≠ 0 → rd.toNat ≠ 0 → r.toNat ≠ rd.toNat →
    AxSymEngine2.gprReg r ≠ AxSymEngine2.gprReg rd := by
  intro H1 H2 H3 Heq
  apply H3
  rw [← gidxGpr r H1, ← gidxGpr rd H2, Heq]

theorem gprNeSimple (z : BitVec 5) (r : Register) :
    (∀ w, r ≠ AxSymEngine2.gprReg w) → AxSymEngine2.gprReg z ≠ r :=
  fun H Heq => H z Heq.symm

/-- Registers the control regime does NOT constrain. -/
def ctrlFree (r : Register) : Prop :=
  r = .PC ∨ r = .nextPC ∨ r = .minstret_increment ∨ r = .minstret ∨ r ∈ uxaGprs

def keepRegs (a b : RegFile) : Prop :=
  b .PC = a .PC ∧ ∀ z : BitVec 5, uxaXget b z = uxaXget a z

/-- (Lean-only) GPRs are off the pins. -/
theorem AxSymEngine2.gprNotPin (r : Register) (h : r ∈ uxaGprs) : ¬ AxRunClose.pinReg r := by
  rintro (rfl | rfl) <;> exact absurd h (by decide)

/-- (Lean-only) GPR values agree between files agreeing off the pins. -/
theorem AxSymEngine2.uxaXgetAgree (a b : RegFile) (h : regsAgree AxRunClose.pinReg a b)
    (i : BitVec 5) : uxaXget a i = uxaXget b i :=
  (uxaXget_congr b a (fun r hr => h r (AxSymEngine2.gprNotPin r hr)) i)

/-- (Lean-only) A non-GPR write leaves the GPR values alone. -/
theorem AxSymEngine2.uxaXgetSetNe (f : RegFile) (r : Register) (v : RegisterType r)
    (h : r ∉ uxaGprs) (i : BitVec 5) : uxaXget (f.set r v) i = uxaXget f i :=
  uxaXget_congr f (f.set r v)
    (fun _ hr' => RegFile.set_other _ _ _ _ (fun e => h (e ▸ hr'))) i

/-- (Lean-only) A GPR write leaves every non-GPR register alone. -/
theorem AxSymEngine2.setGprRegsNe (s : ExecSt) (i : BitVec 5) (v : BitVec 64) (r : Register)
    (h : r ∉ uxaGprs) : (s.setGpr i v).regs r = s.regs r := by
  unfold ExecSt.setGpr
  split <;> first | rfl | exact RegFile.set_other _ _ _ _ (fun e => h (e ▸ by decide))

/-- (Lean-only) A frame property survives a GPR write. -/
theorem AxSymEngine2.ctrlOkSetGpr (C : RegFile → Prop)
    (Hf : ∀ rs (r : Register) (v : RegisterType r), ctrlFree r → C rs → C (rs.set r v))
    (s : ExecSt) (i : BitVec 5) (v : BitVec 64) : C s.regs → C (s.setGpr i v).regs := by
  intro h
  unfold ExecSt.setGpr
  split <;> first | exact h | exact Hf _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))) h

/-! # 4. The instruction-independent SPINE interface, and `textOkD` -/

section regime
variable (img : Image)

/-- THE SPINE (see the header). -/
structure SpineOk (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop) : Prop where
  spSeip : ∀ rs rs', ctrlOk rs → regsAgree AxRunClose.pinReg rs' rs → ctrlOk rs'
  spHart : ∀ rs, ctrlOk rs → rs .hart_state = .HART_ACTIVE ()
  spFrame : ∀ rs (r : Register) (v : RegisterType r), ctrlFree r → ctrlOk rs → ctrlOk (rs.set r v)
  spInc : ∀ t : ExecSt, ctrlOk t.regs → ∃ b, EvA img (fun _ _ => False) (fun x t' => x = b ∧ t' = t)
    (should_inc_minstret (t.regs .cur_privilege)) t
  spDisp : ∀ t : ExecSt, ctrlOk t.regs → EvA img (fun _ _ => False) (fun r t' => r = none ∧ t' = t)
    (dispatchInterrupt (t.regs .cur_privilege)) t
  spFetch : ∀ (t : ExecSt) pc h, ctrlOk t.regs → t.regs .PC = pc → textAt pc h →
    EvA img (fun _ _ => False) (fun r t' => r = .F_RVC h ∧ t' = t) (fetch ()) t
  spLpad : ∀ t : ExecSt, ctrlOk t.regs →
    EvA img (fun _ _ => False) (fun x t' => x = false ∧ t' = t) (is_landing_pad_expected ()) t
  spZca : ∀ t : ExecSt, ctrlOk t.regs →
    EvA img (fun _ _ => False) (fun x t' => x = true ∧ t' = t) (currentlyEnabled .Ext_Zca) t
  spTick : ∀ t : ExecSt, ctrlOk t.regs →
    EvA img (fun _ _ => False) (fun _ t' => ctrlOk t'.regs ∧ keepRegs t.regs t'.regs) (tick_clock ()) t

/-- The WPd reading of `instr pc is_rvc ins`. -/
def textOkD (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
    (pc : BitVec 64) (is_rvc : Bool) (ins : instruction) : Prop :=
  is_rvc = true ∧ ∃ h i0, textAt pc h ∧
    (∀ t : ExecSt, ctrlOk t.regs →
      EvA img (fun _ _ => False) (fun x t' => x = i0 ∧ t' = t) (ext_decode_compressed h) t) ∧
    (∀ t : ExecSt, EvA img (fun _ _ => False) (fun x t' => x = .ExecuteAs ins ∧ t' = t)
      (execute i0) t) ∧
    rf0 (execute ins)

def Good (ctrlOk : RegFile → Prop) (rs : RegFile) (pc : BitVec 64) (rd : BitVec 5)
    (wval : BitVec 64) (rs' : RegFile) : Prop :=
  ctrlOk rs' ∧ rs' .PC = BitVec.addInt pc 2 ∧
    ∀ r : BitVec 5, r.toNat ≠ 0 → uxaXget rs' r = if r = rd then wval else uxaXget rs r

/-- THE WHOLE-INSTRUCTION CERTIFICATE, symbolic. -/
theorem spineCert (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
    (Hsp : SpineOk img ctrlOk textAt) (rs : RegFile) (pc : BitVec 64) (ins : instruction)
    (rd : BitVec 5) (wval : BitVec 64) :
    ctrlOk rs → rs .PC = pc → textOkD img ctrlOk textAt pc true ins → rd.toNat ≠ 0 →
    (∀ s_pc : ExecSt,
       s_pc.regs .nextPC = BitVec.addInt pc 2 →
       gprAgree s_pc.regs rs →
       exec (execute ins) s_pc = some (RETIRE_SUCCESS, s_pc.setGpr rd wval)) →
    ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
      EvA img (fun _ _ => False) (fun _ t' => Good ctrlOk rs pc rd wval t'.regs) (riscvStep tick) t := by
  intro Hct HPC ⟨_, h, i0, Hat, Hdec, Hexp, Hrf⟩ Hrd Hcert tick t Hag
  have Hct_t : ctrlOk t.regs := Hsp.spSeip _ _ Hct Hag
  have HPC_t : t.regs .PC = pc := by
    rw [Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))]; exact HPC
  obtain ⟨b, Hb⟩ := Hsp.spInc t Hct_t
  have Hct_a : ctrlOk (t.setReg .minstret_increment b).regs :=
    Hsp.spFrame _ _ _ (Or.inr (Or.inr (Or.inl rfl))) Hct_t
  have HPC_a : (t.setReg .minstret_increment b).regs .PC = pc := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC_t
  have Hgag : gprAgree ((t.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)).regs rs := by
    intro r _
    simp only [ExecSt.setReg_regs]
    rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide), AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]
    exact AxSymEngine2.uxaXgetAgree _ _ Hag r
  have Hexec : EvA img (fun _ _ => False)
      (fun x t' => x = RETIRE_SUCCESS ∧
        t' = ((t.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)).setGpr rd wval)
      (execute ins) ((t.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)) :=
    rf0EvA img _ _ Hrf _ _ _ (Hcert _ (by simp only [ExecSt.setReg_regs, RegFile.set_same]) Hgag)
  have Hrun := EvAHartActiveRvc img (t.setReg .minstret_increment b) h i0 ins pc
    (fun t' => t' = ((t.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)).setGpr rd wval)
    (Hsp.spDisp _ Hct_a) (Hsp.spFetch _ pc h Hct_a HPC_a Hat) (Hdec _ Hct_a) (Hsp.spLpad _ Hct_a)
    (Hsp.spZca _ Hct_a) HPC_a (Hexp _) Hexec
  refine EvARiscvStep img tick t (fun t' => Good ctrlOk rs pc rd wval t'.regs) _ ?_ ?_
  · have HT := EvATryStepActive img t b (zero_extend (m := 32) h)
      (fun t' => t' = ((t.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)).setGpr rd wval)
      (fun t' => Good ctrlOk rs pc rd wval t'.regs) Hb (Hsp.spHart _ Hct_a) Hrun ?_
    · exact EvAMono img _ _ _ _ _ t (fun _ _ h => h) (fun _ _ h => h.2) HT
    · rintro _ rfl
      have Hx := AxSymEngine2.setGprRegsNe
        ((t.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)) rd wval
      refine ⟨?_, ?_, ?_⟩
      · rw [Hx _ (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide)]
        exact Hsp.spHart _ Hct_a
      · rw [Hx _ (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide), RegFile.set_same]
      · have Hct_x := AxSymEngine2.ctrlOkSetGpr ctrlOk Hsp.spFrame
          ((t.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)) rd wval
          (Hsp.spFrame _ _ _ (Or.inr (Or.inl rfl)) Hct_a)
        refine ⟨?_, ?_, ?_⟩
        · unfold tfinal
          cases b
          · exact Hsp.spFrame _ _ _ (Or.inl rfl) Hct_x
          · exact Hsp.spFrame _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
              (Hsp.spFrame _ _ _ (Or.inl rfl) Hct_x)
        · unfold tfinal
          cases b <;> simp only [ExecSt.setReg_regs, Bool.false_eq_true, ↓reduceIte] <;>
            (try rw [RegFile.set_other _ _ _ _ (by decide)]) <;>
            rw [RegFile.set_same, Hx _ (by decide)] <;>
            simp only [ExecSt.setReg_regs, RegFile.set_same]
        · intro r Hr
          have e : uxaXget (tfinal b (((t.setReg .minstret_increment b).setReg .nextPC
              (BitVec.addInt pc 2)).setGpr rd wval)).regs r =
              ((((t.setReg .minstret_increment b).setReg .nextPC
                (BitVec.addInt pc 2)).setGpr rd wval)).gpr r := by
            unfold tfinal ExecSt.gpr
            cases b <;> simp only [ExecSt.setReg_regs, Bool.false_eq_true, ↓reduceIte] <;>
              (try rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]) <;>
              rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]
          rw [e]
          by_cases E : r = rd
          · subst E
            simp only [if_true]
            exact AxFetch3c.gprSetGprSame _ r wval Hrd
          · simp only [E, if_false]
            rw [AxFetch3c.gprSetGprNe _ rd r wval E]
            exact Hgag r Hr
  · intro t' HG
    cases tick with
    | false => exact HG
    | true =>
      refine EvAMono img _ _ _ _ _ t' (fun _ _ h => h) ?_ (Hsp.spTick t' HG.1)
      rintro _ t'' ⟨Hc, Hk1, Hk2⟩
      obtain ⟨-, HG2, HG3⟩ := HG
      exact ⟨Hc, Hk1.trans HG2, fun r Hr => (Hk2 r).trans (HG3 r Hr)⟩

end regime

/-! # 5. X PROVED, and the real leaves -/

section xproof
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (img : Image) (i : Agent) (cpu : CPU)
variable (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
variable (Hsp : SpineOk img ctrlOk textAt)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)

theorem postLiftingΦ0 (s : Athread) : ⊢ postLifting (Φ0 (GF := GF)) i s :=
  postLiftingTrue _ i s (by unfold Φ0; exact .rfl)

include Hsp Htext Hflow in
/-- THE LIFTING THEOREM X (`AxReuseProbe2.XGprWrite`, verbatim). -/
theorem XGprWriteHolds : XGprWrite (GF := GF) i cpu ctrlOk (textOkD img ctrlOk textAt) := by
  unfold XGprWrite
  intro s rs k pc is_rvc ins rd wval HRet Hctrl HPC Htx Hrd Hcert
  have e : is_rvc = true := Htx.1
  subst e
  iintro C
  iapply (wpdInstrOfEvA img i Φ0 cpu (postLiftingΦ0 i) Htext Hflow
    (fun _ t' => Good ctrlOk rs pc rd wval t'.regs) rs k s HRet
    (spineCert img ctrlOk textAt Hsp rs pc ins rd wval Hctrl HPC Htx Hrd
      (fun s_pc h1 h2 => Hcert s_pc h1 h2)))
  iintro %t' %rs' %ib' %k' %HG %Hag
  obtain ⟨Hc, Hpc, Hg⟩ := HG
  have HRet' : RetX cpu rs' k' ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ :=
    ⟨ib', rfl, rfl, rfl, rfl, rfl, regsAgreeRefl _ _⟩
  have Hc' : ctrlOk rs' := Hsp.spSeip _ _ Hc Hag
  have Hpc' : rs' .PC = pc + instrLen true :=
    (Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))).trans Hpc
  have Hg' : ∀ r : BitVec 5, r.toNat ≠ 0 →
      uxaXget rs' r = if r = rd then wval else uxaXget rs r :=
    fun r Hr => (AxSymEngine2.uxaXgetAgree _ _ Hag r).trans (Hg r Hr)
  iapply C $$ %_ %rs' %k' %HRet' %Hc' %Hpc' %Hg'

variable [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64)] (cid : CPU) (γm γp : GName)

include Hsp Htext Hflow in
/-- `AxReuseProbe2.wpCmvD` with its X premise DISCHARGED. -/
theorem wpCmvDReal (pc : BitVec 64) (rd rs2 : BitVec 5)
    (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) :
    rd.toNat ≠ 0 →
    MachCSL.rdOk rd →
    ⊢ sieCapD (GF := GF) γm cid m n b p -∗
      pcIsD (GF := GF) γp pc -∗
      instrD (GF := GF) (textOkD img ctrlOk textAt) pc true
        (.RTYPE (.Regidx rs2, zreg, .Regidx rd, .ADD)) -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCapD γm cpu' (m.set rd (0#64 + rget cid m rs2)) n b p -∗
        pcIsD γp (pc + 2#64) -∗
        goalD i cid cpu γm γp ctrlOk)) -∗
      goalD i cid cpu γm γp ctrlOk :=
  wpCmvD i cid cpu γm γp ctrlOk (textOkD img ctrlOk textAt)
    (XGprWriteHolds img i cpu ctrlOk textAt Hsp Htext Hflow) pc rd rs2 m n b p

include Hsp Htext Hflow in
/-- `AxReuseProbe2.wpCaddiwD` with its X premise DISCHARGED. -/
theorem wpCaddiwDReal (pc : BitVec 64) (rd : BitVec 5) (imm : BitVec 6)
    (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) :
    rd.toNat ≠ 0 →
    MachCSL.rdOk rd →
    ⊢ sieCapD (GF := GF) γm cid m n b p -∗
      pcIsD (GF := GF) γp pc -∗
      instrD (GF := GF) (textOkD img ctrlOk textAt) pc true
        (.ADDIW (sign_extend (m := 12) imm, .Regidx rd, .Regidx rd)) -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCapD γm cpu' (m.set rd (sign_extend (m := 64) (Sail.BitVec.extractLsb
          (rget cid m rd + sign_extend (m := 64) (sign_extend (m := 12) imm)) 31 0))) n b p -∗
        pcIsD γp (pc + 2#64) -∗
        goalD i cid cpu γm γp ctrlOk)) -∗
      goalD i cid cpu γm γp ctrlOk :=
  wpCaddiwD i cid cpu γm γp ctrlOk (textOkD img ctrlOk textAt)
    (XGprWriteHolds img i cpu ctrlOk textAt Hsp Htext Hflow) pc rd imm m n b p

end xproof

/-! # 5b. Discharging the cheap `SpineOk` fields -/

theorem spLpadOf (img : Image) (ctrlOk : RegFile → Prop)
    (Help : ∀ rs, ctrlOk rs → (rs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false) :
    ∀ t : ExecSt, ctrlOk t.regs →
      EvA img (fun _ _ => False) (fun x t' => x = false ∧ t' = t) (is_landing_pad_expected ()) t := by
  intro t Ht
  unfold is_landing_pad_expected
  refine AxSymEngine2.evFactRead (AxSymEngine2.notPin _ (by decide) (by decide)) ?_
  exact .evRet _ _ ⟨Help _ Ht, rfl⟩

/-! # 6. NON-VACUITY: a boolean checker for `EvA`, at a concrete state -/

theorem mword1Cases (v : BitVec 1) : v = bool_to_bit false ∨ v = bool_to_bit true := by
  revert v; decide

/-- The boolean `EvA` checker (deviation: no `akIfetch` test, as `EvA.evMrd`; both pins answered
both ways). -/
def evb {X : Type} (img : Image) (Qb : X → ExecSt → Bool) : SailM X → ExecSt → Bool
  | .pure x, t => Qb x t
  | .impure (.error _) _, _ => false
  | .impure (.ok o) k, t =>
    match o, k with
    | .regRead r, k =>
      if r = .sig_seip ∨ r = .sig_meip then
        evb img Qb (k (((t.regs.set .sig_seip 0#1).set .sig_meip 0#1) r)) t &&
        evb img Qb (k (((t.regs.set .sig_seip 1#1).set .sig_meip 1#1) r)) t
      else evb img Qb (k (t.regs r)) t
    | .regWrite r v, k =>
      if r = .sig_seip ∨ r = .sig_meip then false else evb img Qb (k PUnit.unit) (t.setReg r v)
    | .memRead n _ req, k =>
      if devAddr req.pa then false
      else if (classify req.access_kind).akLatest then false
      else match imgBytes img (paZ req.pa) n with
        | some vs => evb img Qb (k (.Ok (wordOfBytes n vs, none))) t
        | none => false
    | .instrAnnounce n w, k => if sfAnnB n w then false else evb img Qb (k ()) t
    | .branchAnnounce _ _, k => evb img Qb (k ()) t
    | .cacheOp _, k => evb img Qb (k ()) t
    | .tlbi _, k => evb img Qb (k ()) t
    | .takeException _, k => evb img Qb (k ()) t
    | .returnException _, k => evb img Qb (k ()) t
    | .translationStart _, k => evb img Qb (k ()) t
    | .translationEnd _, k => evb img Qb (k ()) t
    | .cycleCount, k => evb img Qb (k ()) t
    | .message _, k => evb img Qb (k ()) t
    | .getCycleCount, k => evb img Qb (k (0 : Nat)) t
    | _, _ => false

theorem evbSound {X : Type} (img : Image) (Qb : X → ExecSt → Bool) (m : SailM X) :
    ∀ t, evb img Qb m t = true → EvA img (fun _ _ => False) (fun x t' => Qb x t' = true) m t := by
  induction m with
  | pure y => intro t hb; exact .evRet _ _ hb
  | impure call k ih =>
    intro t hb
    cases call with
    | error e => simp [evb] at hb
    | ok o =>
      cases o
      case regRead r =>
        simp only [evb] at hb
        refine .evRd r k t ?_ ?_
        · intro hp v
          have hp' : r = .sig_seip ∨ r = .sig_meip := hp
          rw [if_pos hp', Bool.and_eq_true] at hb
          rcases hp with rfl | rfl <;> rcases bv1_cases v with rfl | rfl
          · exact ih _ _ (by simpa [RegFile.set_same, RegFile.set_other] using hb.1)
          · exact ih _ _ (by simpa [RegFile.set_same, RegFile.set_other] using hb.2)
          · exact ih _ _ (by simpa [RegFile.set_same] using hb.1)
          · exact ih _ _ (by simpa [RegFile.set_same] using hb.2)
        · intro hp
          have hp' : ¬ (r = .sig_seip ∨ r = .sig_meip) := hp
          rw [if_neg hp'] at hb
          exact ih _ _ hb
      case regWrite r v =>
        simp only [evb] at hb
        by_cases hp : r = .sig_seip ∨ r = .sig_meip
        · rw [if_pos hp] at hb; cases hb
        · rw [if_neg hp] at hb
          exact .evWr r v k t hp (ih _ _ hb)
      case memRead n va req =>
        simp only [evb] at hb
        cases hd : devAddr req.pa
        · cases hl : (classify req.access_kind).akLatest
          · cases hv : imgBytes img (paZ req.pa) n with
            | none => simp [hd, hl, hv] at hb
            | some vs =>
              simp only [hd, hl, hv, Bool.false_eq_true, ↓reduceIte] at hb
              exact .evMrd n va req k t vs hd hl hv (ih _ _ hb)
          · simp [hd, hl] at hb
        · simp [hd] at hb
      case instrAnnounce n w =>
        simp only [evb] at hb
        cases hs : sfAnnB n w
        · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hb
          exact .evIa n w k t hs (ih _ _ hb)
        · simp [hs] at hb
      case branchAnnounce n a => exact .evBa n a k t (ih _ _ hb)
      case cacheOp c => exact .evCo c k t (ih _ _ hb)
      case tlbi c => exact .evTl c k t (ih _ _ hb)
      case takeException c => exact .evTe c k t (ih _ _ hb)
      case returnException c => exact .evRx c k t (ih _ _ hb)
      case translationStart c => exact .evTs c k t (ih _ _ hb)
      case translationEnd c => exact .evTx c k t (ih _ _ hb)
      case cycleCount => exact .evCc k t (ih _ _ hb)
      case message c => exact .evMsg c k t (ih _ _ hb)
      case getCycleCount => exact .evGcc k t (ih _ _ hb)
      all_goals simp [evb] at hb

/-- The concrete instance: `AxEpiProbe.tAt` (M-mode), the text image holding `c.mv a0, ra`
(0x8506) at 0x80000002. -/
def nvPc : Nat := 0x80000002

def nvImg (a : Int) : Option (BitVec 8) :=
  if a = nvPc then some 0x06#8 else if a = nvPc + 1 then some 0x85#8 else none

def nvT : ExecSt := tAt nvPc

/-- The whole instruction's post: PC advanced by 2, a0 := ra. -/
def nvPost (_ : Unit) (t' : ExecSt) : Bool :=
  (t'.regs .PC == AxEpiProbe.w64 (nvPc + 2)) && (t'.regs .x10 == AxEpiProbe.w64 raVal)

theorem nvStepFalse : evb nvImg nvPost (riscvStep false) nvT = true := by decide +kernel

theorem nvStepTrue : evb nvImg nvPost (riscvStep true) nvT = true := by decide +kernel

/-- THE BRIDGE'S CERTIFICATE PREMISE HOLDS at a concrete state, for both ticks. -/
theorem nvCert (tick : Bool) :
    EvA nvImg (fun _ _ => False) (fun x t' => nvPost x t' = true) (riscvStep tick) nvT := by
  apply evbSound
  cases tick
  · exact nvStepFalse
  · exact nvStepTrue

def nvEqpost {X : Type} (eqb : X → X → Bool) (x0 : X) (x : X) (_ : ExecSt) : Bool := eqb x x0

theorem nvDisp : evb nvImg (fun r _ => match r with | none => true | some _ => false)
    (dispatchInterrupt .Machine) nvT = true := by decide +kernel

theorem nvFetch : evb nvImg (fun r _ => match r with
      | .F_RVC h => h == 0x8506#16
      | _ => false)
    (fetch ()) nvT = true := by decide +kernel

theorem nvLpad : evb nvImg (fun x _ => !x) (is_landing_pad_expected ()) nvT = true := by
  decide +kernel

theorem nvZca : evb nvImg (fun x _ => x) (currentlyEnabled .Ext_Zca) nvT = true := by
  decide +kernel

theorem nvDecodeExpand :
    evb nvImg (fun r _ => match r with
      | .ExecuteAs (.RTYPE (.Regidx a, .Regidx b, .Regidx c, .ADD)) =>
        a == 1#5 && b == 0#5 && c == 10#5
      | _ => false)
      (ext_decode_compressed 0x8506#16 >>= execute) nvT = true := by decide +kernel

theorem nvRf0 : rf0 (execute (.RTYPE (.Regidx 1#5, zreg, .Regidx 10#5, .ADD))) :=
  rf0ExecuteRTYPEADD 1#5 0#5 10#5

end Weak
