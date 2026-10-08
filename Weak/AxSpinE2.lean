/-
Weak: **PHASE 5 POSITIONAL ENGINE, part 2 (pure, Sail-level)**: the COUNTED data chain —
`execute (LOAD …)` / `execute (STORE …)` as `AxCert.Cert`s at `BFin` that consume EXACTLY ONE row
item (the data event) when the TLB hits the data page — and their `CertB` instances.

Rocq: `iris/AxSpinE2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

WHY A COPY.  `AxDataX`'s data chain is proved ONCE over an abstract kit, but the kit's `cEvA`
field ("every `EvA` fact is a `C` fact at the SAME certificate state") is FALSE for `Cert` at
`BFin`: an `EvA` derivation may contain image reads (even zero-byte ones), which consume budget.
The chain is therefore replayed here directly at `Cert` with the two embeddings the chain
actually needs: `CertRf` (an `execA` fact of an `rfF` (read-free) tree keeps the state, any
budget) and `CertExecA0` (an `execA` fact with read count 0 — the translation on a TLB HIT).
The scripts are `AxDataX`'s, with `x_use` / `x_useT` replaced.
§1 embeddings (`CertExecA0`, `CertRf`, `CertUntilMT1`).
§2 the read chain (`XBReadRam` … `XBExecuteLOAD`): the data read is DEMONIC (`cDrd`), state
   `⟨CPend, BFin (b + 1), r⟩ ↦ ⟨CLd vs, BFin b, r⟩`.
§3 the write chain (`XBWriteRam` … `XBExecuteSTORE`): `cDwr`,
   `⟨CPend, BFin (b + 1), r⟩ ↦ ⟨CSt bytes (wcls akPlain r), BFin b, false⟩`.
§4 S-mode: `dataTranslateHitS` (the data walk on a TLB HIT: state unchanged, 0 reads —
   `cntTranslateAddrImg`'s hit arm); `CertBLoadS` / `CertBStoreS`: the `CertB` (e = 1) of a
   load / store whose data page is warm (`hitW`).

## Deviations from Rocq

1. THE AxDataX DEVIATIONS CARRY OVER (the scripts are `AxDataX`'s): lean-sail monads (the
   early-return monad through `ExceptT.run`; `CertUntilMT1` is lean-sail's `untilFuelM 1`, no
   `measure` premise, as `AxDataX.CUntilMT1` / `AxDataX7.CertUntilMT1'`); `Z` widths ↦ `Nat`, the
   chain's `0 < w` ↦ `vmemWidth w`; the Lean model's `checked_mem_read` reads with `Read_plain` /
   `Read_ttw` by access class, so the data node used by the chain is the Lean-only
   `AxSpinE2.xbReadRamK` and `XBCheckedMemRead` / `XBMemRead` take `hacc : acc ≠
   .InstructionFetch ()`; the data nodes take `akIfetch = false` / `req.value = some v` (Stage
   C / Option write values, absorbed by `rfl`); spellings `tσ`, `rrv`, `AxDataX.wrb`,
   `AxDataX.stData w (t.gpr rs2)` (Rocq `v2`'s autocast subrange), `t1.setGpr rd v` (Rocq
   `set_reg t1 (R_bitvector_64 …)`), `paZ`, `rd.toNat ≠ 0`.
2. BUDGETS.  Rocq `BFin (S b)` ↦ `.BFin (b + 1)`.  `CertB`'s `BFin (e + b)` at `e = 1` is
   `BFin (1 + b)` (rewritten by `Nat.add_comm` in the leaves).
3. THE `rfF` SIDE CONDITIONS of Rocq `xb_use` (Ltac `rfs`) are explicit arguments of the Lean-only
   stepping lemmas (`AxSpinE2.cRUse` …), discharged by the tactic `ax_spin_e2_rfs` (the named
   `rfF` lemmas, else `rff_auto`).  The `wX_bits` / `rX_bits` steps go through `rf0EvA` +
   `nrdOfRf0` (as `AxDataX`), via `AxSpinE2.certEvANrd` (the `EvA` embedding of a read-free tree
   at ANY certificate state) — Rocq: `Cert_execA0` of the `toA`'d SC fact.
4. Section variables / hypotheses (`img dok kind`, `Hkind`, `σ Himg acc pbmt w pa Hw`,
   `σi T satp0 Hmode Hasid Hppn dok`) are explicit arguments in the section order; `Hkind` is
   `hkind : kind = .DKLd` / `.DKSt`; `XBMemWriteEa` takes no `hkind` / width (as Rocq).
   Rocq's statement-level `let t1` / `let v2` / `let tσ` are inlined.
5. (Lean-only hygiene) before each `bv_decide` the proofs `clear` `hkind`, `kind` (and the
   theorem's own auxiliary local), so `bv_decide` never meets the enum `Dkind` and adds no
   `Dkind.enumToBitVec` auxiliaries (AxWalk3 adds them; the two must be importable together).
6. Ltac `nseipE2` dropped (pin tests decided).  `CertBLoadS` / `CertBStoreS` take `1 ≤ w → w ≤ 8`
   for Rocq's `(1 ≤ w ≤ 8)%Z`; the satp hypotheses have `AxSpinE`'s shapes.

**Rocq → Lean name map.**  `Cert_execA0` `CertExecA0`, `Cert_rf` `CertRf`, `Cert_untilMT_1`
`CertUntilMT1`, `XB_read_ram` `XBReadRam`, `XB_checked_mem_read` `XBCheckedMemRead`,
`XB_mem_read` `XBMemRead`, `XB_translate_and_read` `XBTranslateAndRead`, `XB_vmem_read_addr`
`XBVmemReadAddr`, `XB_vmem_read` `XBVmemRead`, `XB_execute_LOAD` `XBExecuteLOAD`,
`XB_write_ram` `XBWriteRam`, `XB_checked_mem_write` `XBCheckedMemWrite`, `XB_mem_write_value`
`XBMemWriteValue`, `XB_mem_write_ea` `XBMemWriteEa`, `XB_vmem_write_addr` `XBVmemWriteAddr`,
`XB_vmem_write` `XBVmemWrite`, `XB_execute_STORE` `XBExecuteSTORE`, `data_translate_hit_S`
`dataTranslateHitS`, `ow_ldB` `owLdB`, `CertB_load_S` `CertBLoadS`, `CertB_store_S`
`CertBStoreS`; Ltacs `rfs` ↦ `ax_spin_e2_rfs`, `xb_use` / `xb_useT` ↦ the lemmas below.  None is
in the duplicated-name table.  Lean-only (file-qualified): `AxSpinE2.certEvANrd`,
`AxSpinE2.cRUse`, `AxSpinE2.cRUseT`, `AxSpinE2.cFactUse`, `AxSpinE2.cFactUseT`,
`AxSpinE2.cFactEvA`, `AxSpinE2.cRLiftLast`, `AxSpinE2.xbReadRamK`.

**Dropped:** nothing (Rocq 21 definitions/lemmas + 4 Ltacs; Lean 21 + 8 Lean-only + 1 tactic).
**Not ported:** the Ltacs `nseipE2`, `xb_use`, `xb_useT` (deviations 3, 5; `rfs` is
`ax_spin_e2_rfs`); the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxSpinE

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 1. Embeddings -/

section emb
variable (img : Image) (dok : Int → Nat → Prop) (kind : Dkind)

/-- Rocq `Cert_execA0`: an `execA` fact with read count 0, at ANY certificate state. -/
theorem CertExecA0 {X : Type} (Q : Cst → X → ExecSt → Prop) (σ : ExecSt) (m : SailM X) (x : X)
    (s1 : ExecSt) (s : Cst) (t : ExecSt) :
    img = imgOf σ →
    execA m ⟨t.regs, σ.mem, t.dev⟩ = some (x, s1) →
    cntA m ⟨t.regs, σ.mem, t.dev⟩ = 0 →
    Q s x ⟨s1.regs, t.mem, t.dev⟩ →
    AxCert.Cert img dok kind (fun _ _ _ => False) Q s m t := by
  intro hi he hc hq
  obtain ⟨d, b, r⟩ := s
  cases b with
  | BInf =>
    subst hi
    have HE := execAEvA m _ x s1 he t rfl
    refine CertMono (imgOf σ) dok kind _ _ _ _ _ m t (fun _ _ _ h => h.2.elim) ?_
      (CertOfEvA (imgOf σ) dok kind _ _ d r m t HE)
    rintro s' x' ⟨r', m', d'⟩ ⟨rfl, rfl, hr, hm, hd⟩
    simp only at hr hm hd
    subst hr hm hd
    exact hq
  | BFin b =>
    exact CertExecACnt img dok kind Q σ m x s1 0 d r b t hi he hc hq

/-- Rocq `Cert_rf`: a read-free (`rfF`) `execA` fact at the image state, state kept. -/
theorem CertRf {X : Type} (Q : Cst → X → ExecSt → Prop) (σ : ExecSt) (m : SailM X) (x : X)
    (s : Cst) (t : ExecSt) :
    img = imgOf σ →
    execA m ⟨t.regs, σ.mem, t.dev⟩ = some (x, ⟨t.regs, σ.mem, t.dev⟩) →
    rfF m → Q s x t → AxCert.Cert img dok kind (fun _ _ _ => False) Q s m t := by
  intro hi he hrf hq
  exact CertExecA0 img dok kind Q σ m x _ s t hi he (cntARfF m hrf _) (by cases t; exact hq)

/-- Rocq `Cert_untilMT_1` (lean-sail `untilFuelM 1`, in the early-return monad; deviation 1). -/
theorem CertUntilMT1 {R Vars : Type} (QE : Cst → Sail.Error exception → ExecSt → Prop)
    (Q : Cst → Except (Sail.Error exception ⊕ R) Vars → ExecSt → Prop) (vars : Vars)
    (cond : Vars → SailME R Bool) (body : Vars → SailME R Vars) (s : Cst) (t : ExecSt) :
    AxCert.Cert img dok kind QE (fun s' r t' => match r with
      | .ok v => AxCert.Cert img dok kind QE (fun s'' r' t'' => match r' with
          | .ok b => b = true ∧ Q s'' (.ok v) t''
          | .error e => Q s'' (.error e) t'') s' (ExceptT.run (cond v)) t'
      | .error e => Q s' (.error e) t') s (ExceptT.run (body vars)) t →
    AxCert.Cert img dok kind QE Q s (ExceptT.run (untilFuelM 1 cond vars body)) t := by
  intro Hb
  unfold untilFuelM untilFuelM.go
  rw [ExceptT.run_bind]
  apply CertBind
  refine CertMono img dok kind _ _ _ _ s _ t (fun _ _ _ h => h) ?_ Hb
  intro s' r t' hr
  rcases r with e | v
  · exact .cRet s' _ t' hr
  · show AxCert.Cert img dok kind QE Q s'
      (ExceptT.run (cond v >>= fun b => if b then pure v else _)) t'
    rw [ExceptT.run_bind]
    apply CertBind
    refine CertMono img dok kind _ _ _ _ s' _ t' (fun _ _ _ h => h) ?_ hr
    intro s'' r' t'' hr'
    rcases r' with e | b
    · exact .cRet s'' _ t'' hr'
    · obtain ⟨rfl, hq⟩ := hr'
      exact .cRet s'' _ t'' hq

/-- (Lean-only, deviation 3) a read-free `EvA` fact embeds at ANY certificate state. -/
theorem AxSpinE2.certEvANrd {X : Type} (P : X → ExecSt → Prop) (m : SailM X) (s : Cst)
    (t : ExecSt) :
    EvA img (fun _ _ => False) P m t → nrd m →
    AxCert.Cert img dok kind (fun _ _ _ => False) (fun s' x t' => s' = s ∧ P x t') s m t := by
  intro H Hn
  obtain ⟨d, b, r⟩ := s
  cases b with
  | BInf => exact CertEvA img dok kind P m d r t H
  | BFin b => exact CertNrd img dok kind P m d b r t H Hn

end emb

/-! ### (Lean-only) the stepping kit: Rocq's `xb_use` / `xb_useT` -/

section kit
variable {img : Image} {dok : Int → Nat → Prop} {kind : Dkind}
  {QE : Cst → Sail.Error exception → ExecSt → Prop}

/-- Rocq `xb_use σ H` in the early-return monad (the `rfF` side condition explicit). -/
theorem AxSpinE2.cRUse {σ : ExecSt} (himg : img = imgOf σ) {R X Y : Type}
    {Q : Cst → Except (Sail.Error exception ⊕ R) Y → ExecSt → Prop}
    {m : SailM X} {f : X → SailME R Y} {s : Cst} {t : ExecSt} {a : X}
    (He : execA m (tσ σ t) = some (a, tσ σ t)) (Hrf : rfF m)
    (H : AxCert.Cert img dok kind QE Q s (ExceptT.run (f a)) t) :
    AxCert.Cert img dok kind QE Q s (ExceptT.run (liftM m >>= f)) t :=
  AxCert4.cFactLift
    (CertRf img dok kind (fun s' x t' => s' = s ∧ x = a ∧ t' = t) σ m a s t himg He Hrf
      ⟨rfl, rfl, rfl⟩)
    (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H)

/-- Rocq `xb_useT σ H Hc` in the early-return monad: read count 0, the registers change. -/
theorem AxSpinE2.cRUseT {σ : ExecSt} (himg : img = imgOf σ) {R X Y : Type}
    {Q : Cst → Except (Sail.Error exception ⊕ R) Y → ExecSt → Prop}
    {m : SailM X} {f : X → SailME R Y} {s : Cst} {t s1 : ExecSt} {a : X}
    (He : execA m (tσ σ t) = some (a, s1)) (Hc : cntA m (tσ σ t) = 0)
    (H : AxCert.Cert img dok kind QE Q s (ExceptT.run (f a)) ⟨s1.regs, t.mem, t.dev⟩) :
    AxCert.Cert img dok kind QE Q s (ExceptT.run (liftM m >>= f)) t :=
  AxCert4.cFactLift
    (CertExecA0 img dok kind (fun s' x t' => s' = s ∧ x = a ∧ t' = ⟨s1.regs, t.mem, t.dev⟩) σ m a
      s1 s t himg He Hc ⟨rfl, rfl, rfl⟩)
    (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H)

/-- Rocq `xb_use σ H` in the base monad. -/
theorem AxSpinE2.cFactUse {σ : ExecSt} (himg : img = imgOf σ) {X Y : Type}
    {Q : Cst → Y → ExecSt → Prop} {m : SailM X} {f : X → SailM Y} {s : Cst} {t : ExecSt} {a : X}
    (He : execA m (tσ σ t) = some (a, tσ σ t)) (Hrf : rfF m)
    (H : AxCert.Cert img dok kind QE Q s (f a) t) :
    AxCert.Cert img dok kind QE Q s (m >>= f) t :=
  AxCert4.cFactQ
    (CertRf img dok kind (fun s' x t' => s' = s ∧ x = a ∧ t' = t) σ m a s t himg He Hrf
      ⟨rfl, rfl, rfl⟩)
    (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H)

/-- Rocq `xb_useT σ H Hc` in the base monad. -/
theorem AxSpinE2.cFactUseT {σ : ExecSt} (himg : img = imgOf σ) {X Y : Type}
    {Q : Cst → Y → ExecSt → Prop} {m : SailM X} {f : X → SailM Y} {s : Cst} {t s1 : ExecSt}
    {a : X} (He : execA m (tσ σ t) = some (a, s1)) (Hc : cntA m (tσ σ t) = 0)
    (H : AxCert.Cert img dok kind QE Q s (f a) ⟨s1.regs, t.mem, t.dev⟩) :
    AxCert.Cert img dok kind QE Q s (m >>= f) t :=
  AxCert4.cFactQ
    (CertExecA0 img dok kind (fun s' x t' => s' = s ∧ x = a ∧ t' = ⟨s1.regs, t.mem, t.dev⟩) σ m a
      s1 s t himg He Hc ⟨rfl, rfl, rfl⟩)
    (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H)

/-- A read-free `EvA` fact with a determined result and state, then the continuation (any
certificate state). -/
theorem AxSpinE2.cFactEvA {X Y : Type} {Q : Cst → Y → ExecSt → Prop} {m : SailM X}
    {f : X → SailM Y} {s : Cst} {t t1 : ExecSt} {a : X}
    (Hm : EvA img (fun _ _ => False) (fun x t' => x = a ∧ t' = t1) m t) (Hn : nrd m)
    (H : AxCert.Cert img dok kind QE Q s (f a) t1) :
    AxCert.Cert img dok kind QE Q s (m >>= f) t :=
  AxCert4.cFactQ (AxSpinE2.certEvANrd img dok kind _ m s t Hm Hn)
    (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H)

/-- A lifted base-monad tree ending a `SailME.run` block. -/
theorem AxSpinE2.cRLiftLast {X : Type} {Q : Cst → X → ExecSt → Prop} {m : SailM X} {s : Cst}
    {t : ExecSt} (Hm : AxCert.Cert img dok kind (fun _ _ _ => False) Q s m t) :
    AxCert.Cert img dok kind QE (fun s' (r : Except (Sail.Error exception ⊕ X) X) t' =>
        match r with
        | .ok x => Q s' x t'
        | .error (.inr x) => Q s' x t'
        | .error (.inl e) => QE s' e t')
      s (ExceptT.run (liftM m : SailME X X)) t :=
  CertMono img dok kind _ _ _ _ s _ t (fun _ _ _ h => h) (fun s' r t' h => by
    rcases r with (e | x) | x
    · exact h.elim
    · exact h.elim
    · exact h) (CertLiftRM img dok kind QE Q m s t Hm)

end kit

/-- Rocq `rfs`: the `rfF` side conditions of the stepping lemmas. -/
macro "ax_spin_e2_rfs" : tactic => `(tactic| first
  | exact True.intro
  | exact rfFCheckPmaWithPmpPriority _ _ _ _ _ _
  | exact rfFSplitMisaligned _ _ _ _
  | exact rfFPmpCheck _ _ _ _
  | exact rfFWithinMmioReadable _ _
  | exact rfFEffectivePrivilege _ _ _
  | exact rfFTranslationMode _
  | exact rfFReadKindOfFlags _ _ _
  | rff_auto)

/-! # 2. The read chain at `BFin` -/

section rdB
variable (img : Image) (dok : Int → Nat → Prop) (kind : Dkind) (hkind : kind = .DKLd)
include hkind

/-- (Lean-only, deviation 1) the data node at a non-latest RAM read kind. -/
theorem AxSpinE2.xbReadRamK (rk : read_kind) (hrk : rk = .Read_plain ∨ rk = .Read_ttw) (w : Nat)
    (QE : Cst → Sail.Error exception → ExecSt → Prop)
    (Q : Cst → (BitVec (8 * w) × Unit) → ExecSt → Prop) (pa : BitVec 64) (b : Nat) (r : Bool)
    (t : ExecSt) :
    devAddr pa = false → dok (paZ pa) w →
    (∀ vs : List (BitVec 8), vs.length = w → Q ⟨.CLd vs, .BFin b, r⟩ (rrv w vs, default_meta) t) →
    AxCert.Cert img dok kind QE Q ⟨.CPend, .BFin (b + 1), r⟩ (read_ram rk (.Physaddr pa) w false) t := by
  intro hdev hdok hq
  rcases hrk with rfl | rfl <;>
  · simp only [read_ram, PreSail.sail_mem_read, PreSail.emit]
    exact .cDrd (.BFin b) r w 64 _ _ t hkind hdev rfl rfl hdok
      (fun vs hvs => .cRet _ _ _ (hq vs hvs))

/-- Rocq `XB_read_ram`: THE DATA NODE (demonic; one row item). -/
theorem XBReadRam (w : Nat) (QE : Cst → Sail.Error exception → ExecSt → Prop)
    (Q : Cst → (BitVec (8 * w) × Unit) → ExecSt → Prop) (pa : BitVec 64) (b : Nat) (r : Bool)
    (t : ExecSt) :
    devAddr pa = false → dok (paZ pa) w →
    (∀ vs : List (BitVec 8), vs.length = w → Q ⟨.CLd vs, .BFin b, r⟩ (rrv w vs, default_meta) t) →
    AxCert.Cert img dok kind QE Q ⟨.CPend, .BFin (b + 1), r⟩
      (read_ram .Read_plain (.Physaddr pa) w false) t :=
  AxSpinE2.xbReadRamK img dok kind hkind _ (Or.inl rfl) w QE Q pa b r t

section cmr
variable (σ : ExecSt) (himg : img = imgOf σ) (acc : MemoryAccessType mem_payload)
  (pbmt : page_based_mem_type) (w : Nat) (pa : BitVec 64) (hw : vmemWidth w)
  (hacc : acc ≠ .InstructionFetch ())
include himg hw hacc

/-- Rocq `XB_checked_mem_read`. -/
theorem XBCheckedMemRead
    (Q : Cst → Result (BitVec (8 * w) × Unit) (physaddr × ExceptionType) → ExecSt → Prop)
    (b : Nat) (r : Bool) (t : ExecSt) :
    execA (check_pma_with_pmp_priority acc pbmt .Supervisor (.Physaddr pa) w false) (tσ σ t)
      = some (.Ok pmaOkAligned, tσ σ t) →
    execA (pmpCheck (.Physaddr pa) w acc .Supervisor) (tσ σ t) = some (none, tσ σ t) →
    execA (within_mmio_readable (.Physaddr pa) w) (tσ σ t) = some (false, tσ σ t) →
    devAddr pa = false → dok (paZ pa) w →
    (∀ vs : List (BitVec 8), vs.length = w →
      Q ⟨.CLd vs, .BFin b, r⟩ (.Ok (rrv w vs, default_meta)) t) →
    AxCert.Cert img dok kind (fun _ _ _ => False) Q ⟨.CPend, .BFin (b + 1), r⟩
      (checked_mem_read acc pbmt .Supervisor (.Physaddr pa) w false false false false) t := by
  intro hcp hpmp hmm hdev hdok hq
  unfold checked_mem_read
  apply CertCatchEarlyReturn
  refine AxCert4.cRAssoc ?_
  refine AxSpinE2.cRUse himg hcp (by ax_spin_e2_rfs) ?_
  refine AxCert4.cRPureBind ?_
  refine AxSpinE2.cRUse himg (a := ((1 : Int), (w : Int))) rfl (by ax_spin_e2_rfs) ?_
  simp only [misaligned_order, sys_misaligned_order_decreasing, ↓reduceIte, Bool.false_eq_true,
    Int.reduceSub, Int.toNat_zero]
  rcases hw with rfl | rfl | rfl | rfl
  all_goals
    cases acc <;> (try (rename_i p; cases p))
  all_goals try exact absurd rfl hacc
  all_goals
    simp only [read_kind_of_flags]
    first
    | refine AxSpinE2.cRUse himg rfl (by ax_spin_e2_rfs) ?_
    | refine AxCert4.cRPureBind ?_
    refine AxCert4.cRAssoc ?_
    refine AxCert4.cRBind ?_
    refine CertUntilMT1 img dok kind _ _ _ _ _ _ t ?_
    refine AxSpinE2.cRUse himg rfl (by ax_spin_e2_rfs) ?_
    simp only [bits_of_physaddr, Int.cast_ofNat_Int, Int.zero_mul, addIntZero, Int.toNat_one,
      Int.mul_one]
    refine AxSpinE2.cRUse himg hpmp (by ax_spin_e2_rfs) ?_
    dsimp only
    refine AxSpinE2.cRUse himg hmm (by ax_spin_e2_rfs) ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine AxCert4.cRAssoc ?_
    refine AxCert4.cFactLift
      (P := fun s' x t' => ∃ vs : List (BitVec 8), vs.length = _ ∧ s' = ⟨.CLd vs, .BFin b, r⟩ ∧
        x = (rrv _ vs, default_meta) ∧ t' = t)
      (AxSpinE2.xbReadRamK img dok kind hkind _ (by simp) _ _ _ pa b r t hdev hdok
        (fun vs hvs => ⟨vs, hvs, rfl, rfl, rfl⟩)) ?_
    rintro s' x t' ⟨vs, hvs, rfl, rfl, rfl⟩
    refine AxCert4.cRPureBind ?_
    refine AxDataX7.cRPure ?_
    refine AxDataX7.cRPure ⟨rfl, ?_⟩
    refine AxCert4.cRPureBind ?_
    refine AxDataX7.cRPure ?_
    refine AxDataX.substArg (fun v => Q _ v _) ?_ (hq vs hvs)
    simp only [Result.Ok.injEq, Prod.mk.injEq, and_true, Nat.reduceMul, Int.reduceMul, Int.reduceAdd,
      Int.reduceSub, Int.reduceToNat, BitVec.setWidth_eq]
    try simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.updateSubrange]
    clear hkind
    clear kind
    try bv_decide

/-- Rocq `XB_mem_read`. -/
theorem XBMemRead (Q : Cst → Result (BitVec (8 * w)) (physaddr × ExceptionType) → ExecSt → Prop)
    (b : Nat) (r : Bool) (t : ExecSt) :
    rdFacts σ acc pbmt w pa t → devAddr pa = false → dok (paZ pa) w →
    (∀ vs : List (BitVec 8), vs.length = w → Q ⟨.CLd vs, .BFin b, r⟩ (.Ok (rrv w vs)) t) →
    AxCert.Cert img dok kind (fun _ _ _ => False) Q ⟨.CPend, .BFin (b + 1), r⟩
      (mem_read acc pbmt (.Physaddr pa) w false false false) t := by
  rintro ⟨heff, hcp, hpmp, hmm⟩ hdev hdok hq
  unfold mem_read
  ax_cert4_go
  refine AxSpinE2.cFactUse himg heff (by ax_spin_e2_rfs) ?_
  unfold mem_read_priv mem_read_priv_meta
  ax_cert4_go
  refine AxCert4.cFactQ (XBCheckedMemRead img dok kind hkind σ himg acc pbmt w pa hw hacc
    (fun s' r' t' => ∃ vs : List (BitVec 8), vs.length = w ∧ s' = ⟨.CLd vs, .BFin b, r⟩ ∧
      r' = .Ok (rrv w vs, default_meta) ∧ t' = t) b r t hcp hpmp hmm hdev hdok
    (fun vs hvs => ⟨vs, hvs, rfl, rfl, rfl⟩)) ?_
  rintro s' x t' ⟨vs, hvs, rfl, rfl, rfl⟩
  ax_cert4_go
  exact .cRet _ _ _ (hq vs hvs)

end cmr

/-- Rocq `XB_translate_and_read`: translate (an `execA` fact with read count 0: a TLB HIT) then
read. -/
theorem XBTranslateAndRead (σ : ExecSt) (himg : img = imgOf σ) (va pa : BitVec 64) (w : Nat)
    (Q : Cst → Result (physaddr × BitVec (8 * w)) ExecutionResult → ExecSt → Prop) (b : Nat)
    (r : Bool) (t s1 : ExecSt) :
    vmemWidth w →
    execA (translateAddr (.Virtaddr va) (.Load .Data)) (tσ σ t)
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1) →
    cntA (translateAddr (.Virtaddr va) (.Load .Data)) (tσ σ t) = 0 →
    rdFacts σ (.Load .Data) .PBMT_PMA w pa ⟨s1.regs, t.mem, t.dev⟩ → devAddr pa = false →
    dok (paZ pa) w →
    (∀ vs : List (BitVec 8), vs.length = w →
      Q ⟨.CLd vs, .BFin b, r⟩ (.Ok (.Physaddr pa, rrv w vs)) ⟨s1.regs, t.mem, t.dev⟩) →
    AxCert.Cert img dok kind (fun _ _ _ => False) Q ⟨.CPend, .BFin (b + 1), r⟩
      (translate_and_read_value (.Virtaddr va) w (.Load .Data) false false false) t := by
  intro hw htr htrc hrf hdev hdok hq
  unfold translate_and_read_value
  refine AxSpinE2.cFactUseT himg htr htrc ?_
  dsimp only
  refine AxCert4.cFactQ (XBMemRead img dok kind hkind σ himg (.Load .Data) .PBMT_PMA w pa hw
    (by intro h; cases h) (fun s' r' t' => ∃ vs : List (BitVec 8), vs.length = w ∧
      s' = ⟨.CLd vs, .BFin b, r⟩ ∧ r' = .Ok (rrv w vs) ∧ t' = ⟨s1.regs, t.mem, t.dev⟩) b r _ hrf
    hdev hdok (fun vs hvs => ⟨vs, hvs, rfl, rfl, rfl⟩)) ?_
  rintro s' x t' ⟨vs, hvs, rfl, rfl, rfl⟩
  dsimp only
  exact .cRet _ _ _ (hq vs hvs)

/-- Rocq `XB_vmem_read_addr`. -/
theorem XBVmemReadAddr (σ : ExecSt) (himg : img = imgOf σ) (va pa : BitVec 64) (w : Nat)
    (md : SATPMode) (Q : Cst → Result (BitVec (8 * w)) ExecutionResult → ExecSt → Prop) (b : Nat)
    (r : Bool) (t s1 : ExecSt) :
    vmemWidth w →
    is_aligned_vaddr (.Virtaddr va) w = true →
    execA (effectivePrivilege (.Load .Data) (t.regs .mstatus) (t.regs .cur_privilege)) (tσ σ t)
      = some (.Supervisor, tσ σ t) →
    execA (translationMode .Supervisor) (tσ σ t) = some (md, tσ σ t) →
    execA (translateAddr (.Virtaddr va) (.Load .Data)) (tσ σ t)
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1) →
    cntA (translateAddr (.Virtaddr va) (.Load .Data)) (tσ σ t) = 0 →
    rdFacts σ (.Load .Data) .PBMT_PMA w pa ⟨s1.regs, t.mem, t.dev⟩ → devAddr pa = false →
    dok (paZ pa) w →
    (∀ vs : List (BitVec 8), vs.length = w →
      Q ⟨.CLd vs, .BFin b, r⟩ (.Ok (rrv w vs)) ⟨s1.regs, t.mem, t.dev⟩) →
    AxCert.Cert img dok kind (fun _ _ _ => False) Q ⟨.CPend, .BFin (b + 1), r⟩
      (vmem_read_addr (.Virtaddr va) w (.Load .Data) false false false) t := by
  intro hw hal heff htm htr htrc hrf hdev hdok hq
  have hsp := splitOnPageBoundaryAlignedEq va w hw hal
  unfold vmem_read_addr
  simp only [bits_of_virtaddr, hsp, pure_bind, hal, Functions.not, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  apply CertCatchEarlyReturn
  ax_cert4_go
  refine AxSpinE2.cRUse himg rfl (by ax_spin_e2_rfs) ?_
  ax_cert4_go
  refine AxSpinE2.cRUse himg heff (by ax_spin_e2_rfs) ?_
  refine AxSpinE2.cRUse himg htm (by ax_spin_e2_rfs) ?_
  cases md <;>
  · dsimp only [iteNoSplitBare, iteNoSplitSv32, iteNoSplitSv39, iteNoSplitSv48, iteNoSplitSv57,
      Int.toNat_natCast, sys_misaligned_order_decreasing, Bool.false_and]
    refine AxCert4.cRPureBind ?_
    refine AxCert4.cRAssoc ?_
    refine AxCert4.cFactLift (XBTranslateAndRead img dok kind hkind σ himg va pa w
      (fun s' r' t' => ∃ vs : List (BitVec 8), vs.length = w ∧ s' = ⟨.CLd vs, .BFin b, r⟩ ∧
        r' = .Ok (.Physaddr pa, rrv w vs) ∧ t' = ⟨s1.regs, t.mem, t.dev⟩) b r t s1 hw htr htrc
      hrf hdev hdok (fun vs hvs => ⟨vs, hvs, rfl, rfl, rfl⟩)) ?_
    rintro s' x t' ⟨vs, hvs, rfl, rfl, rfl⟩
    dsimp only
    refine AxCert4.cRPureBind ?_
    refine AxCert4.cRPureBind ?_
    refine AxDataX7.cRPure ?_
    refine AxDataX.substArg (fun v => Q _ v _) ?_ (hq vs hvs)
    simp only [Result.Ok.injEq]
    rcases hw with rfl | rfl | rfl | rfl <;>
    · simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.updateSubrange,
        zeros, Int.cast_ofNat_Int, Int.reduceMul, Int.reduceSub, Int.reduceToNat, Nat.reduceSub,
        Nat.reduceAdd, BitVec.setWidth_eq]
      clear hkind
      clear XBVmemReadAddr kind
      bv_decide

/-- Rocq `XB_vmem_read`. -/
theorem XBVmemRead (σ : ExecSt) (himg : img = imgOf σ) (rs1 : BitVec 5) (offset va pa : BitVec 64)
    (w : Nat) (md : SATPMode) (Q : Cst → Result (BitVec (8 * w)) ExecutionResult → ExecSt → Prop)
    (b : Nat) (r : Bool) (t s1 : ExecSt) :
    execA (get_transformed_data_addr (.Regidx rs1) offset (.Load .Data) w) (tσ σ t)
      = some (.Ext_DataAddr_OK (.Virtaddr va), tσ σ t) →
    vmemWidth w →
    is_aligned_vaddr (.Virtaddr va) w = true →
    execA (effectivePrivilege (.Load .Data) (t.regs .mstatus) (t.regs .cur_privilege)) (tσ σ t)
      = some (.Supervisor, tσ σ t) →
    execA (translationMode .Supervisor) (tσ σ t) = some (md, tσ σ t) →
    execA (translateAddr (.Virtaddr va) (.Load .Data)) (tσ σ t)
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1) →
    cntA (translateAddr (.Virtaddr va) (.Load .Data)) (tσ σ t) = 0 →
    rdFacts σ (.Load .Data) .PBMT_PMA w pa ⟨s1.regs, t.mem, t.dev⟩ → devAddr pa = false →
    dok (paZ pa) w →
    (∀ vs : List (BitVec 8), vs.length = w →
      Q ⟨.CLd vs, .BFin b, r⟩ (.Ok (rrv w vs)) ⟨s1.regs, t.mem, t.dev⟩) →
    AxCert.Cert img dok kind (fun _ _ _ => False) Q ⟨.CPend, .BFin (b + 1), r⟩
      (vmem_read (.Regidx rs1) offset w (.Load .Data) false false false) t := by
  intro hgta hw hal heff htm htr htrc hrf hdev hdok hq
  unfold vmem_read
  apply CertCatchEarlyReturn
  ax_cert4_go
  refine AxSpinE2.cRUse himg hgta (by ax_spin_e2_rfs) ?_
  dsimp only
  ax_cert4_go
  exact AxSpinE2.cRLiftLast (XBVmemReadAddr img dok kind hkind σ himg va pa w md Q b r t s1 hw hal
    heff htm htr htrc hrf hdev hdok hq)

/-- Rocq `XB_execute_LOAD`: THE LOAD at `BFin`, one row item (the demonic data read). -/
theorem XBExecuteLOAD (σ : ExecSt) (himg : img = imgOf σ) (imm : BitVec 12) (rs1 rd : BitVec 5)
    (is_unsigned : Bool) (w : Nat) (va pa : BitVec 64) (md : SATPMode)
    (Q : Cst → ExecutionResult → ExecSt → Prop) (b : Nat) (r : Bool) (t s1 : ExecSt) :
    w ≤ 8 → rd.toNat ≠ 0 →
    execA (get_transformed_data_addr (.Regidx rs1) (sign_extend (m := 64) imm) (.Load .Data) w)
      (tσ σ t) = some (.Ext_DataAddr_OK (.Virtaddr va), tσ σ t) →
    vmemWidth w →
    is_aligned_vaddr (.Virtaddr va) w = true →
    execA (effectivePrivilege (.Load .Data) (t.regs .mstatus) (t.regs .cur_privilege)) (tσ σ t)
      = some (.Supervisor, tσ σ t) →
    execA (translationMode .Supervisor) (tσ σ t) = some (md, tσ σ t) →
    execA (translateAddr (.Virtaddr va) (.Load .Data)) (tσ σ t)
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1) →
    cntA (translateAddr (.Virtaddr va) (.Load .Data)) (tσ σ t) = 0 →
    rdFacts σ (.Load .Data) .PBMT_PMA w pa ⟨s1.regs, t.mem, t.dev⟩ → devAddr pa = false →
    dok (paZ pa) w →
    (∀ vs : List (BitVec 8), vs.length = w →
      Q ⟨.CLd vs, .BFin b, r⟩ RETIRE_SUCCESS
        ((⟨s1.regs, t.mem, t.dev⟩ : ExecSt).setGpr rd (extend_value is_unsigned (rrv w vs)))) →
    AxCert.Cert img dok kind (fun _ _ _ => False) Q ⟨.CPend, .BFin (b + 1), r⟩
      (execute (.LOAD (imm, .Regidx rs1, .Regidx rd, is_unsigned, w))) t := by
  intro hw8 _hrd hgta hw hal heff htm htr htrc hrf hdev hdok hq
  show AxCert.Cert img dok kind _ Q _ (execute_LOAD imm (.Regidx rs1) (.Regidx rd) is_unsigned w) t
  unfold execute_LOAD
  have h8 : (w ≤b Functions.xlen_bytes) = true := by
    simp only [Functions.xlen_bytes, decide_eq_true_eq]; omega
  simp only [h8]
  refine AxSpinE2.cFactUse himg (execAAssertExpTrue _ _) (by ax_spin_e2_rfs) ?_
  refine AxCert4.cFactQ (XBVmemRead img dok kind hkind σ himg rs1 _ va pa w md
    (fun s' r' t' => ∃ vs : List (BitVec 8), vs.length = w ∧ s' = ⟨.CLd vs, .BFin b, r⟩ ∧
      r' = .Ok (rrv w vs) ∧ t' = ⟨s1.regs, t.mem, t.dev⟩) b r t s1 hgta hw hal heff htm htr htrc
    hrf hdev hdok (fun vs hvs => ⟨vs, hvs, rfl, rfl, rfl⟩)) ?_
  rintro s' x t' ⟨vs, hvs, rfl, rfl, rfl⟩
  dsimp only
  refine AxSpinE2.cFactEvA (rf0EvA img _ _ (rf0WXBits rd _) _ _ _ (execWXBitsGpr rd _ _))
    (nrdOfRf0 _ (rf0WXBits rd _)) ?_
  exact .cRet _ _ _ (hq vs hvs)

end rdB

/-! # 3. The write chain at `BFin` -/

section wrB
variable (img : Image) (dok : Int → Nat → Prop) (kind : Dkind) (hkind : kind = .DKSt)

include hkind in
/-- Rocq `XB_write_ram`: THE DATA WRITE (one row item; class recorded, flag cleared). -/
theorem XBWriteRam (w : Nat) (QE : Cst → Sail.Error exception → ExecSt → Prop)
    (Q : Cst → Bool → ExecSt → Prop) (pa : BitVec 64) (data : BitVec (8 * w)) (b : Nat) (r : Bool)
    (t : ExecSt) :
    devAddr pa = false → dok (paZ pa) w →
    Q ⟨.CSt (AxDataX.wrb w data) (wcls AxDataX.akPlain r), .BFin b, false⟩ true t →
    AxCert.Cert img dok kind QE Q ⟨.CPend, .BFin (b + 1), r⟩
      (write_ram .Write_plain (.Physaddr pa) w data ()) t := by
  intro hdev hdok hq
  simp only [write_ram, PreSail.sail_mem_write, PreSail.emit]
  exact .cDwr (.BFin b) r w 64 _ _ t data hkind hdev rfl rfl hdok (.cRet _ _ _ hq)

section cmw
variable (σ : ExecSt) (himg : img = imgOf σ) (acc : MemoryAccessType mem_payload)
  (pbmt : page_based_mem_type) (w : Nat) (pa : BitVec 64) (hw : vmemWidth w)
include himg

include hkind hw in
/-- Rocq `XB_checked_mem_write`. -/
theorem XBCheckedMemWrite (data : BitVec (8 * w))
    (Q : Cst → Result Bool (physaddr × ExceptionType) → ExecSt → Prop) (b : Nat) (r : Bool)
    (t : ExecSt) :
    execA (check_pma_with_pmp_priority acc pbmt .Supervisor (.Physaddr pa) w false) (tσ σ t)
      = some (.Ok pmaOkAligned, tσ σ t) →
    execA (pmpCheck (.Physaddr pa) w acc .Supervisor) (tσ σ t) = some (none, tσ σ t) →
    execA (within_mmio_writable (.Physaddr pa) w) (tσ σ t) = some (false, tσ σ t) →
    devAddr pa = false → dok (paZ pa) w →
    Q ⟨.CSt (AxDataX.wrb w data) (wcls AxDataX.akPlain r), .BFin b, false⟩ (.Ok true) t →
    AxCert.Cert img dok kind (fun _ _ _ => False) Q ⟨.CPend, .BFin (b + 1), r⟩
      (checked_mem_write (.Physaddr pa) w data acc pbmt .Supervisor () false false false) t := by
  intro hcp hpmp hmm hdev hdok hq
  unfold checked_mem_write
  apply CertCatchEarlyReturn
  refine AxCert4.cRAssoc ?_
  refine AxSpinE2.cRUse himg hcp (by ax_spin_e2_rfs) ?_
  refine AxCert4.cRPureBind ?_
  refine AxSpinE2.cRUse himg (a := ((1 : Int), (w : Int))) rfl (by ax_spin_e2_rfs) ?_
  simp only [misaligned_order, sys_misaligned_order_decreasing, ↓reduceIte, Bool.false_eq_true,
    Int.reduceSub, Int.toNat_zero, write_kind_of_flags]
  refine AxSpinE2.cRUse himg rfl (by ax_spin_e2_rfs) ?_
  refine AxCert4.cRBind ?_
  refine CertUntilMT1 img dok kind _ _ _ _ _ _ t ?_
  refine AxSpinE2.cRUse himg rfl (by ax_spin_e2_rfs) ?_
  simp only [bits_of_physaddr, Int.cast_ofNat_Int, Int.zero_mul, addIntZero, Int.toNat_natCast]
  refine AxSpinE2.cRUse himg hpmp (by ax_spin_e2_rfs) ?_
  dsimp only
  refine AxCert4.cRAssoc ?_
  refine AxSpinE2.cRUse himg hmm (by ax_spin_e2_rfs) ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine AxCert4.cRAssoc ?_
  refine AxCert4.cFactLift (P := fun s' x t' =>
      s' = ⟨.CSt (AxDataX.wrb w _) (wcls AxDataX.akPlain r), .BFin b, false⟩ ∧ x = true ∧ t' = t)
    (XBWriteRam img dok kind hkind w _ _ pa _ b r t hdev hdok ⟨rfl, rfl, rfl⟩) ?_
  rintro s' x t' ⟨rfl, rfl, rfl⟩
  refine AxCert4.cRPureBind ?_
  refine AxDataX7.cRPure ?_
  refine AxDataX7.cRPure ⟨rfl, ?_⟩
  refine AxDataX7.cRPure ?_
  refine AxDataX.substArg
    (fun z => Q ⟨.CSt z (wcls AxDataX.akPlain r), .BFin b, false⟩ _ _) ?_ hq
  refine congrArg (AxDataX.wrb w) ?_
  rcases hw with rfl | rfl | rfl | rfl <;>
  · simp only [Sail.BitVec.extractLsb, Int.cast_ofNat_Int, Int.reduceMul, Int.reduceSub,
      Int.reduceToNat, Int.reduceAdd, Nat.reduceMul]
    clear hkind
    clear kind
    bv_decide

include hkind hw in
/-- Rocq `XB_mem_write_value`. -/
theorem XBMemWriteValue (data : BitVec (8 * w))
    (Q : Cst → Result Bool (physaddr × ExceptionType) → ExecSt → Prop) (b : Nat) (r : Bool)
    (t : ExecSt) :
    wrFacts σ acc pbmt w pa t → devAddr pa = false → dok (paZ pa) w →
    Q ⟨.CSt (AxDataX.wrb w data) (wcls AxDataX.akPlain r), .BFin b, false⟩ (.Ok true) t →
    AxCert.Cert img dok kind (fun _ _ _ => False) Q ⟨.CPend, .BFin (b + 1), r⟩
      (mem_write_value (.Physaddr pa) w data acc pbmt false false false) t := by
  rintro ⟨heff, hcp, hpmp, hmm⟩ hdev hdok hq
  unfold mem_write_value mem_write_value_meta
  ax_cert4_go
  refine AxSpinE2.cFactUse himg heff (by ax_spin_e2_rfs) ?_
  unfold mem_write_value_priv_meta
  ax_cert4_go
  refine AxCert4.cFactQ (XBCheckedMemWrite img dok kind hkind σ himg acc pbmt w pa hw data
    (fun s' r' t' => s' = ⟨.CSt (AxDataX.wrb w data) (wcls AxDataX.akPlain r), .BFin b, false⟩ ∧
      r' = .Ok true ∧ t' = t) b r t hcp hpmp hmm hdev hdok ⟨rfl, rfl, rfl⟩) ?_
  rintro s' x t' ⟨rfl, rfl, rfl⟩
  ax_cert4_go
  exact .cRet _ _ _ hq

/-- Rocq `XB_mem_write_ea`: register-only (PMA/PMP checks, the split loop's address
announcement), at ANY certificate state. -/
theorem XBMemWriteEa (Q : Cst → Result Unit (physaddr × ExceptionType) → ExecSt → Prop) (s : Cst)
    (t : ExecSt) :
    wrFacts σ acc pbmt w pa t → Q s (.Ok ()) t →
    AxCert.Cert img dok kind (fun _ _ _ => False) Q s
      (mem_write_ea (.Physaddr pa) w acc pbmt false false false) t := by
  rintro ⟨heff, hcp, hpmp, _⟩ hq
  unfold mem_write_ea
  apply CertCatchEarlyReturn
  ax_cert4_go
  refine AxSpinE2.cRUse himg heff (by ax_spin_e2_rfs) ?_
  ax_cert4_go
  refine AxSpinE2.cRUse himg hcp (by ax_spin_e2_rfs) ?_
  ax_cert4_go
  refine AxSpinE2.cRUse himg (a := ((1 : Int), (w : Int))) rfl (by ax_spin_e2_rfs) ?_
  simp only [misaligned_order, sys_misaligned_order_decreasing, ↓reduceIte, Bool.false_eq_true,
    Int.reduceSub, Int.toNat_zero, write_kind_of_flags]
  refine AxSpinE2.cRUse himg rfl (by ax_spin_e2_rfs) ?_
  refine AxCert4.cRBind ?_
  refine CertUntilMT1 img dok kind _ _ _ _ _ _ t ?_
  refine AxSpinE2.cRUse himg rfl (by ax_spin_e2_rfs) ?_
  simp only [bits_of_physaddr, Int.cast_ofNat_Int, Int.zero_mul, addIntZero, Int.toNat_natCast]
  refine AxSpinE2.cRUse himg hpmp (by ax_spin_e2_rfs) ?_
  dsimp only
  refine AxDataX7.cRPure ?_
  refine AxDataX7.cRPure ⟨rfl, ?_⟩
  refine AxDataX7.cRPure ?_
  exact hq

end cmw

include hkind

/-- Rocq `XB_vmem_write_addr`. -/
theorem XBVmemWriteAddr (σ : ExecSt) (himg : img = imgOf σ) (va pa : BitVec 64) (w : Nat)
    (data : BitVec (8 * w)) (md : SATPMode)
    (Q : Cst → Result Bool ExecutionResult → ExecSt → Prop) (b : Nat) (r : Bool) (t s1 : ExecSt) :
    vmemWidth w →
    is_aligned_vaddr (.Virtaddr va) w = true →
    execA (effectivePrivilege (.Store .Data) (t.regs .mstatus) (t.regs .cur_privilege)) (tσ σ t)
      = some (.Supervisor, tσ σ t) →
    execA (translationMode .Supervisor) (tσ σ t) = some (md, tσ σ t) →
    execA (translateAddr (.Virtaddr va) (.Store .Data)) (tσ σ t)
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1) →
    cntA (translateAddr (.Virtaddr va) (.Store .Data)) (tσ σ t) = 0 →
    wrFacts σ (.Store .Data) .PBMT_PMA w pa ⟨s1.regs, t.mem, t.dev⟩ → devAddr pa = false →
    dok (paZ pa) w →
    Q ⟨.CSt (AxDataX.wrb w data) (wcls AxDataX.akPlain r), .BFin b, false⟩ (.Ok true)
      ⟨s1.regs, t.mem, t.dev⟩ →
    AxCert.Cert img dok kind (fun _ _ _ => False) Q ⟨.CPend, .BFin (b + 1), r⟩
      (vmem_write_addr (.Virtaddr va) w data (.Store .Data) false false false) t := by
  intro hw hal heff htm htr htrc hwf hdev hdok hq
  have hsp := splitOnPageBoundaryAlignedEq va w hw hal
  unfold vmem_write_addr
  simp only [bits_of_virtaddr, hsp, pure_bind, hal, Functions.not, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  apply CertCatchEarlyReturn
  ax_cert4_go
  refine AxSpinE2.cRUse himg rfl (by ax_spin_e2_rfs) ?_
  ax_cert4_go
  refine AxSpinE2.cRUse himg heff (by ax_spin_e2_rfs) ?_
  refine AxSpinE2.cRUse himg htm (by ax_spin_e2_rfs) ?_
  cases md <;>
  · dsimp only [iteNoSplitBare, iteNoSplitSv32, iteNoSplitSv39, iteNoSplitSv48, iteNoSplitSv57,
      Int.toNat_natCast, sys_misaligned_order_decreasing, Bool.false_and]
    refine AxCert4.cRPureBind ?_
    refine AxCert4.cRAssoc ?_
    refine AxSpinE2.cRUseT himg htr htrc ?_
    dsimp only
    refine AxCert4.cRAssoc ?_
    refine AxSpinE2.cRUse himg rfl (by ax_spin_e2_rfs) ?_
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    refine AxCert4.cRAssoc ?_
    refine AxCert4.cFactLift (XBMemWriteEa img dok kind σ himg (.Store .Data) .PBMT_PMA w pa
      (fun s' r' t' => s' = ⟨.CPend, .BFin (b + 1), r⟩ ∧ r' = .Ok () ∧
        t' = ⟨s1.regs, t.mem, t.dev⟩) _ _ hwf ⟨rfl, rfl, rfl⟩) ?_
    rintro s' x t' ⟨hs, rfl, rfl⟩
    subst s'
    dsimp only
    refine AxCert4.cRAssoc ?_
    refine AxCert4.cFactLift (XBMemWriteValue img dok kind hkind σ himg (.Store .Data) .PBMT_PMA w pa
      hw _ (fun s' r' t' => s' = ⟨.CSt (AxDataX.wrb w _) (wcls AxDataX.akPlain r), .BFin b, false⟩ ∧
        r' = .Ok true ∧ t' = ⟨s1.regs, t.mem, t.dev⟩) b r _ hwf hdev hdok ⟨rfl, rfl, rfl⟩) ?_
    rintro s' x t' ⟨rfl, rfl, rfl⟩
    dsimp only
    refine AxCert4.cRPureBind ?_
    refine AxDataX7.cRPure ?_
    refine AxDataX.substArg
      (fun z => Q ⟨.CSt z (wcls AxDataX.akPlain r), .BFin b, false⟩ _ _) ?_ hq
    refine congrArg (AxDataX.wrb w) ?_
    rcases hw with rfl | rfl | rfl | rfl <;>
    · simp only [Sail.BitVec.extractLsb, Int.cast_ofNat_Int, Int.reduceMul, Int.reduceSub,
        Int.reduceToNat, Nat.reduceMul]
      clear hkind
      clear XBVmemWriteAddr kind
      bv_decide

/-- Rocq `XB_vmem_write`. -/
theorem XBVmemWrite (σ : ExecSt) (himg : img = imgOf σ) (rs1 : BitVec 5) (offset va pa : BitVec 64)
    (w : Nat) (data : BitVec (8 * w)) (md : SATPMode)
    (Q : Cst → Result Bool ExecutionResult → ExecSt → Prop) (b : Nat) (r : Bool) (t s1 : ExecSt) :
    execA (get_transformed_data_addr (.Regidx rs1) offset (.Store .Data) w) (tσ σ t)
      = some (.Ext_DataAddr_OK (.Virtaddr va), tσ σ t) →
    vmemWidth w →
    is_aligned_vaddr (.Virtaddr va) w = true →
    execA (effectivePrivilege (.Store .Data) (t.regs .mstatus) (t.regs .cur_privilege)) (tσ σ t)
      = some (.Supervisor, tσ σ t) →
    execA (translationMode .Supervisor) (tσ σ t) = some (md, tσ σ t) →
    execA (translateAddr (.Virtaddr va) (.Store .Data)) (tσ σ t)
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1) →
    cntA (translateAddr (.Virtaddr va) (.Store .Data)) (tσ σ t) = 0 →
    wrFacts σ (.Store .Data) .PBMT_PMA w pa ⟨s1.regs, t.mem, t.dev⟩ → devAddr pa = false →
    dok (paZ pa) w →
    Q ⟨.CSt (AxDataX.wrb w data) (wcls AxDataX.akPlain r), .BFin b, false⟩ (.Ok true)
      ⟨s1.regs, t.mem, t.dev⟩ →
    AxCert.Cert img dok kind (fun _ _ _ => False) Q ⟨.CPend, .BFin (b + 1), r⟩
      (vmem_write (.Regidx rs1) offset w data (.Store .Data) false false false) t := by
  intro hgta hw hal heff htm htr htrc hwf hdev hdok hq
  unfold vmem_write
  apply CertCatchEarlyReturn
  ax_cert4_go
  refine AxSpinE2.cRUse himg hgta (by ax_spin_e2_rfs) ?_
  dsimp only
  ax_cert4_go
  exact AxSpinE2.cRLiftLast (XBVmemWriteAddr img dok kind hkind σ himg va pa w data md Q b r t s1
    hw hal heff htm htr htrc hwf hdev hdok hq)

/-- Rocq `XB_execute_STORE`: THE STORE at `BFin`, one row item (the data write of rs2's low `w`
bytes); no GPR written. -/
theorem XBExecuteSTORE (σ : ExecSt) (himg : img = imgOf σ) (imm : BitVec 12) (rs2 rs1 : BitVec 5)
    (w : Nat) (va pa : BitVec 64) (md : SATPMode) (Q : Cst → ExecutionResult → ExecSt → Prop)
    (b : Nat) (r : Bool) (t s1 : ExecSt) :
    w ≤ 8 →
    execA (get_transformed_data_addr (.Regidx rs1) (sign_extend (m := 64) imm) (.Store .Data) w)
      (tσ σ t) = some (.Ext_DataAddr_OK (.Virtaddr va), tσ σ t) →
    vmemWidth w →
    is_aligned_vaddr (.Virtaddr va) w = true →
    execA (effectivePrivilege (.Store .Data) (t.regs .mstatus) (t.regs .cur_privilege)) (tσ σ t)
      = some (.Supervisor, tσ σ t) →
    execA (translationMode .Supervisor) (tσ σ t) = some (md, tσ σ t) →
    execA (translateAddr (.Virtaddr va) (.Store .Data)) (tσ σ t)
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1) →
    cntA (translateAddr (.Virtaddr va) (.Store .Data)) (tσ σ t) = 0 →
    wrFacts σ (.Store .Data) .PBMT_PMA w pa ⟨s1.regs, t.mem, t.dev⟩ → devAddr pa = false →
    dok (paZ pa) w →
    Q ⟨.CSt (AxDataX.wrb w (AxDataX.stData w (t.gpr rs2))) (wcls AxDataX.akPlain r), .BFin b,
      false⟩ RETIRE_SUCCESS ⟨s1.regs, t.mem, t.dev⟩ →
    AxCert.Cert img dok kind (fun _ _ _ => False) Q ⟨.CPend, .BFin (b + 1), r⟩
      (execute (.STORE (imm, .Regidx rs2, .Regidx rs1, w))) t := by
  intro hw8 hgta hw hal heff htm htr htrc hwf hdev hdok hq
  show AxCert.Cert img dok kind _ Q _ (execute_STORE imm (.Regidx rs2) (.Regidx rs1) w) t
  unfold execute_STORE
  have h8 : (w ≤b Functions.xlen_bytes) = true := by
    simp only [Functions.xlen_bytes, decide_eq_true_eq]; omega
  simp only [h8]
  refine AxSpinE2.cFactUse himg (execAAssertExpTrue _ _) (by ax_spin_e2_rfs) ?_
  refine AxSpinE2.cFactEvA (rf0EvA img _ _ (rf0RXBits rs2) _ _ _ (execRXBitsGpr rs2 t))
    (nrdOfRf0 _ (rf0RXBits rs2)) ?_
  refine AxCert4.cFactPure ?_
  refine AxCert4.cFactQ (XBVmemWrite img dok kind hkind σ himg rs1 _ va pa w
    (AxDataX.stData w (t.gpr rs2)) md
    (fun s' r' t' => s' = ⟨.CSt (AxDataX.wrb w (AxDataX.stData w (t.gpr rs2)))
        (wcls AxDataX.akPlain r), .BFin b, false⟩ ∧ r' = .Ok true ∧ t' = ⟨s1.regs, t.mem, t.dev⟩)
    b r t s1 hgta hw hal heff htm htr htrc hwf hdev hdok ⟨rfl, rfl, rfl⟩) ?_
  rintro s' x t' ⟨rfl, rfl, rfl⟩
  dsimp only
  exact .cRet _ _ _ hq

end wrB

/-! # 4. The S-mode data side on a TLB HIT, and the `CertB` leaves -/

section dataHit
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)

/-- Rocq `data_translate_hit_S`: the data walk on a TLB HIT — no read, state kept. -/
theorem dataTranslateHitS (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (acc : MemoryAccessType mem_payload) (t : ExecSt) (va : BitVec 64) (w : Nat) (pa : BitVec 64) :
    ctrlOkS T satp0 t.regs → dataAtS σi T acc va w pa → hitW t.regs va →
    exec (effectivePrivilege acc (t.regs .mstatus) .Supervisor) (tσ σi t)
      = some (.Supervisor, tσ σi t) →
    exec (is_shadow_stack_access acc) (tσ σi t) = some (false, tσ σi t) →
    execA (translateAddr (.Virtaddr va) acc) (tσ σi t)
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), tσ σi t) ∧
    cntA (translateAddr (.Virtaddr va) acc) (tσ σi t) = 0 := by
  intro hc hda hhit heff hss
  obtain ⟨p2, p1, pte, hmaps, hs2, hs1, hs0, hchk, hupd, hpb, hcanon, hout, -⟩ := hda
  let σ : ExecSt := tσ σi t
  have hc0 := hc
  obtain ⟨hpriv, -, hmisa, hmenv, hhtif, -, hpma, hms, -, -, hsatp, htlbx, hA, hord, -, hR, hcov⟩ :=
    hc0
  obtain ⟨-, hSXL, -⟩ := hms
  have htm := execTranslationModeSSv39 satp0 σ hSXL hsatp hmode
  have hpmar : WeakKpt.pmaAllowsPteRead (σ.regs .pma_regions) := by
    show WeakKpt.pmaAllowsPteRead (t.regs .pma_regions)
    rw [hpma]; exact WeakKpt.pmaAllowsBootPteRead
  have hs2' : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr2 T (WeakKpt.svpnOf va)) p2 := hs2
  have hs1' : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr1 p2 (WeakKpt.svpnOf va)) p1 := hs1
  have hs0' : WeakWalkEff.ptSlotMem σ (AxPtProt.ptAddr0 p1 (WeakKpt.svpnOf va)) pte := hs0
  obtain ⟨htr, htrc⟩ := cntTranslateAddrImg acc .Supervisor T.base va pte pa
    satp0 T (σ.regs .tlb) p2 p1 σ hchk hupd hcanon hout hpb rfl hmaps htlbx hs2' hs1' hs0' hmisa
    hmenv hhtif hpriv htm heff hss hsatp hppn hasid rfl hA hord hR hcov hpmar
  have hhit' : tlbHitv (σ.regs .tlb) (WeakKpt.svpnOf va) = true := hhit
  rw [hhit'] at htr htrc
  simp only [↓reduceIte] at htr htrc
  exact ⟨htr, htrc⟩

/-- Rocq `ow_ldB`: the load leaf's GPR write, read off the final data state. -/
def owLdB (rd : BitVec 5) (u : Bool) (w : Nat) (d : Cdata) : Option (BitVec 5 × BitVec 64) :=
  match d with
  | .CLd vs => some (rd, ldRes u w vs)
  | _ => none

/-- Rocq `CertB_load_S`: THE LOAD LEAF'S CERTIFICATE — one row item (the demonic data read). -/
theorem CertBLoadS (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (dok : Int → Nat → Prop) (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12)
    (rs1 rd : BitVec 5) (u : Bool) (w : Nat) (va pa : BitVec 64) (r : Bool) :
    rd.toNat ≠ 0 → vmemWidth w → 1 ≤ w → w ≤ 8 →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Load .Data) va w pa → hitW rs va → dok (paZ pa) w →
    CertB σi T satp0 dok .DKLd rs pc is_rvc (.LOAD (imm, .Regidx rs1, .Regidx rd, u, w)) 1 none
      (owLdB rd u w) .CPend r (fun d r' => ∃ vs, d = .CLd vs ∧ vs.length = w ∧ r' = r) := by
  intro hrd hvw hw1 hw8 hva hda hhit hdok t ⟨hc, _⟩ _ _ hag htl b
  have hva' : va = gprVal t.regs rs1 + sign_extend (m := 64) imm := by
    rw [gprValAgree _ _ _ hag]; exact hva
  have hhitT : hitW t.regs va := hitWAgree _ _ _ htl hhit
  have hc0 := hc
  obtain ⟨hpriv, -, -, hmenv, -, -, -, hms, -, -, hsatp, -⟩ := hc0
  obtain ⟨hMPRV, hSXL, hMXR, -⟩ := hms
  let σ : ExecSt := tσ σi t
  have heff : exec (effectivePrivilege (.Load .Data) (t.regs .mstatus) .Supervisor) σ
      = some (.Supervisor, σ) := execEffectivePrivilegeLoadS _ σ hMPRV
  have hss : exec (is_shadow_stack_access (.Load .Data)) σ = some (false, σ) := rfl
  obtain ⟨htr, htrc⟩ :=
    dataTranslateHitS σi T satp0 hmode hasid hppn (.Load .Data) t va w pa hc hda hhitT heff hss
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hram, hal, hpal⟩ := hda
  obtain ⟨hrf, hdev⟩ := rdFactsS σi T satp0 ⟨σ.regs, t.mem, t.dev⟩ pa w hc hw1 hw8 hram hpal
  have hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (σ.regs .menvcfg)) = .PMM_Disabled := by
    show pmm_mode_backwards (_get_MEnvcfg_PMM (t.regs .menvcfg)) = .PMM_Disabled
    rw [hmenv]
    first
    | rfl
    | decide +kernel
  have hg : exec (get_transformed_data_addr (.Regidx rs1) (sign_extend (m := 64) imm) (.Load .Data) w)
      σ = some (.Ext_DataAddr_OK (.Virtaddr va), σ) := by
    unfold get_transformed_data_addr
    rw [execBindSome _ _ _ _ _ (execExtDataGetAddrGpr rs1 _ (.Load .Data) w σ)]
    dsimp only
    rw [execBindSome _ _ _ _ _ (execTransformEffectiveAddressLoadS _ satp0 σ hpriv hSXL hsatp hmode
      hMPRV hMXR hpmm)]
    rw [AxDataX3.pmTransformVA0, hva']
    rfl
  to_a hg
  have heffA : execA (effectivePrivilege (.Load .Data) (t.regs .mstatus) (t.regs .cur_privilege)) σ
      = some (.Supervisor, σ) := by
    rw [hpriv]
    to_a heff
    exact heff
  have htm := execTranslationModeSSv39 satp0 σ hSXL hsatp hmode
  to_a htm
  rw [Nat.add_comm]
  refine XBExecuteLOAD (imgS σi) dok .DKLd rfl σi rfl imm rs1 rd u w va pa .Sv39 _ b r t σ hw8 hrd
    hg hvw hal heffA htm htr htrc hrf hdev hdok ?_
  intro vs hvs
  refine ⟨rfl, .CLd vs, r, rfl, ⟨vs, rfl, hvs, rfl⟩, ?_⟩
  cases t
  rfl

/-- Rocq `CertB_store_S`: THE STORE LEAF'S CERTIFICATE — one row item (the data write). -/
theorem CertBStoreS (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (dok : Int → Nat → Prop) (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12)
    (rs2 rs1 : BitVec 5) (w : Nat) (va pa : BitVec 64) (r : Bool) :
    vmemWidth w → 1 ≤ w → w ≤ 8 →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Store .Data) va w pa → hitW rs va → dok (paZ pa) w →
    CertB σi T satp0 dok .DKSt rs pc is_rvc (.STORE (imm, .Regidx rs2, .Regidx rs1, w)) 1 none
      (fun _ => none) .CPend r
      (fun d r' => d = .CSt (stBytes w (gprVal rs rs2)) (wcls AxDataX.akPlain r) ∧ r' = false) := by
  intro hvw hw1 hw8 hva hda hhit hdok t ⟨hc, hW⟩ _ _ hag htl b
  have hva' : va = gprVal t.regs rs1 + sign_extend (m := 64) imm := by
    rw [gprValAgree _ _ _ hag]; exact hva
  have hhitT : hitW t.regs va := hitWAgree _ _ _ htl hhit
  have hc0 := hc
  obtain ⟨hpriv, -, -, hmenv, -, -, -, hms, -, -, hsatp, -⟩ := hc0
  obtain ⟨hMPRV, hSXL, hMXR, -⟩ := hms
  let σ : ExecSt := tσ σi t
  have heff : exec (effectivePrivilege (.Store .Data) (t.regs .mstatus) .Supervisor) σ
      = some (.Supervisor, σ) := execEffectivePrivilegeStoreS _ σ hMPRV
  have hss : exec (is_shadow_stack_access (.Store .Data)) σ = some (false, σ) := rfl
  obtain ⟨htr, htrc⟩ :=
    dataTranslateHitS σi T satp0 hmode hasid hppn (.Store .Data) t va w pa hc hda hhitT heff hss
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hram, hal, hpal⟩ := hda
  obtain ⟨hwf, hdev⟩ := wrFactsS σi T satp0 ⟨σ.regs, t.mem, t.dev⟩ pa w hc hW hw1 hw8 hram hpal
  have hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (σ.regs .menvcfg)) = .PMM_Disabled := by
    show pmm_mode_backwards (_get_MEnvcfg_PMM (t.regs .menvcfg)) = .PMM_Disabled
    rw [hmenv]
    first
    | rfl
    | decide +kernel
  have hg : exec (get_transformed_data_addr (.Regidx rs1) (sign_extend (m := 64) imm) (.Store .Data) w)
      σ = some (.Ext_DataAddr_OK (.Virtaddr va), σ) := by
    unfold get_transformed_data_addr
    rw [execBindSome _ _ _ _ _ (execExtDataGetAddrGpr rs1 _ (.Store .Data) w σ)]
    dsimp only
    rw [execBindSome _ _ _ _ _ (execTransformEffectiveAddressStoreS _ satp0 σ hpriv hSXL hsatp hmode
      hMPRV hMXR hpmm)]
    rw [hva']
    rfl
  to_a hg
  have heffA : execA (effectivePrivilege (.Store .Data) (t.regs .mstatus) (t.regs .cur_privilege))
      σ = some (.Supervisor, σ) := by
    rw [hpriv]
    to_a heff
    exact heff
  have htm := execTranslationModeSSv39 satp0 σ hSXL hsatp hmode
  to_a htm
  rw [Nat.add_comm]
  refine XBExecuteSTORE (imgS σi) dok .DKSt rfl σi rfl imm rs2 rs1 w va pa .Sv39 _ b r t σ hw8 hg
    hvw hal heffA htm htr htrc hwf hdev hdok ?_
  refine ⟨rfl, _, false, rfl, ⟨?_, rfl⟩, ?_⟩
  · unfold stBytes
    rw [← gprValAgree _ _ _ hag]
    rfl
  · cases t
    rfl

end dataHit

end Weak
