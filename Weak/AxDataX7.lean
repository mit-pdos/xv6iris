/-
Weak: **THE AMO DATA CHAIN at `AxCert.Cert` (RMW arm), symbolic** —
`execute (AMO (AMOSWAP, aq, rl := false, rs2, rs1, w, rd))` performs the EXCLUSIVE read
(demonic, `Cert.cXrd`: no row item) and the EXCLUSIVE write of rs2's low `w` bytes
(`Cert.cXwr`), rd := the sign-extended read value, the walk (Atomic access) as an `execA` fact
at the image.

Rocq: `iris/AxDataX7.v` @ xxvzwolszwmp.

## The Rocq header, in substance

The Cert-level nodes: `CertReadRamXa` (`Read_RISCV_reserved_acquire` / `Read_RISCV_reserved`),
`CertWriteRamXc` (`Write_RISCV_conditional`); the register-only checks are `execA` facts
(`amoFacts`).  The chain `CertCheckedMemReadX` / `CertMemReadX` / `CertMemWriteEaX` /
`CertCheckedMemWriteX` / `CertMemWriteValueX`, and `CertExecuteAMOSWAP`: the whole `execute`,
state `⟨CPend, BInf, r⟩ ↦ ⟨CRmw aq false rvs wvs (wcls akXc r), BInf, false⟩`.
The embeddings of `execA` facts: `CertExecASame` / `CertExecA`; the one-iteration split loop
`CertUntilMT1'`.

## Deviations from Rocq

1. LEAN-SAIL MONADS (as `AxDataX` deviation 2).  The early-return monad `SailME R X` is reached
   through `ExceptT.run`; `CertUntilMT1'` is lean-sail's `untilFuelM 1` in the early-return
   monad (where the model's split loops live), stated as `AxDataX.CUntilMT1` (no `measure`
   premise: the fuel is literally 1).  Rocq's Ltacs `a_use` / `a_useT` are the Lean-only
   stepping lemmas `AxDataX7.cRUse` / `cRUseT` (early-return monad) and `AxDataX7.cFactUse`
   (base monad), built on `CertExecASame` / `CertExecA` and `AxCert4`'s kit (`ax_cert4_go`
   = Rocq `c_go`).
2. WIDTHS (as `AxDataX` deviation 4).  `Z` widths ↦ `Nat`; the chain's section hypothesis
   `0 < w` and `Cert_execute_AMOSWAP`'s `0 < w → w ≤ 8` ↦ `vmemWidth w` (the model's
   accumulator / extract casts are closed per width: the proofs case on the four widths for the
   final bit-vector equation).  `rrv w vs` = `wordOfBytes w vs`; Rocq's `usvd_zeros_full_gen` /
   `subrange_full_gen_cast` rewrites are the per-width `bv_decide` closings.
3. LEAN MODEL SHAPES.  `checked_mem_read` picks the read kind by a match on `(access, res)`
   (Rocq: always `read_kind_of_flags`), so the read-chain proofs case on `acc` (every arm is the
   reserved kind at `res = true`).  The Lean `execute_AMO` passes `aq && rl` / `rl` to the
   memory calls; at `rl = false` the proof rewrites `aq && false` to `false` (Rocq
   `andb_false_r`), so the chain lemmas are stated at Rocq's flags.  The CAS guard is the inline
   `if op == AMOCAS` (no `and_boolM`); the width assert is an `execA` fact by `rfl` at each width.  The rd write is one `wX_bits` step for every `rd` (the SC
   fact `execWXBitsGpr` is uniform; Rocq splits `uint rd = 0`); since the continuation premise
   quantifies over every final state, nothing is lost.
4. SPELLING (as `AxDataX` deviation 5).  `mstate` ↦ `ExecSt`, `tσ σ t` / `img_of` ↦ `tσ` /
   `imgOf`, `MState s1.(sregs) t.(mem) t.(mdev)` ↦ `⟨s1.regs, t.mem, t.dev⟩`,
   `register_lookup r t.(sregs)` ↦ `t.regs r`, `uint pa` ↦ `paZ pa`, `Z.to_nat w` ↦ `w`,
   `zeros' 64` ↦ `zeros (n := 64)`, `init_ext_ptw` / `tt` ↦ `()`, `Interface.accessKind` ↦ `AK`,
   `wrb` ↦ `AxDataX.wrb`.  Rocq's `CM` notation (QE `False`, kind `DKRmw`) is written out; the
   section variables `img dok σ Himg` are explicit binders (implicit for the Lean-only kit);
   `amoFacts` takes `σ` first (as `rdFacts`).  `Cert_execute_AMOSWAP`'s statement-level `let`s
   (`acc`, `t1`) are inlined.

**Rocq → Lean name map.**  `ak_xa` `akXa`, `ak_xc` `akXc`, `Cert_execA_same` `CertExecASame`,
`Cert_execA` `CertExecA`, `Cert_untilMT_1'` `CertUntilMT1'`, `Cert_read_ram_xa` `CertReadRamXa`,
`Cert_write_ram_xc` `CertWriteRamXc`, `amo_facts` `amoFacts`, `Cert_checked_mem_read_x`
`CertCheckedMemReadX`, `Cert_mem_read_x` `CertMemReadX`, `Cert_mem_write_ea_x` `CertMemWriteEaX`,
`Cert_checked_mem_write_x` `CertCheckedMemWriteX`, `Cert_mem_write_value_x` `CertMemWriteValueX`,
`Cert_execute_AMOSWAP` `CertExecuteAMOSWAP`.  None is in the duplicated-name table.
Lean-only (file-qualified): `AxDataX7.cRUse`, `AxDataX7.cRUseT`, `AxDataX7.cFactUse`,
`AxDataX7.cRPure`, `AxDataX7.readKindFlagsX` (the reserved read kind as one `execA` fact, so the
read chain stays generic in `aq`).

**Dropped:** nothing (Rocq 3 definitions + 11 lemmas (+2 Ltacs); Lean 3 definitions +
11 theorems + 5 Lean-only lemmas).
**Not ported:** the Ltacs `a_use` / `a_useT` (deviation 1).
-/
import Weak.AxCert4
import Weak.AxDataX2

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- The access kind of the exclusive read (`aq` = the acquire bit). -/
def akXa (aq : Bool) : AK :=
  .AK_explicit ⟨.AV_exclusive, if aq then .AS_rel_or_acq else .AS_normal⟩

/-- The access kind of the exclusive (conditional) write. -/
def akXc : AK := .AK_explicit ⟨.AV_exclusive, .AS_normal⟩

/-- The register-only facts of an AMO access at `pa` (Rocq section variable `σ` explicit). -/
def amoFacts (σ : ExecSt) (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type)
    (w : Nat) (pa : BitVec 64) (t : ExecSt) : Prop :=
  execA (effectivePrivilege acc (t.regs .mstatus) (t.regs .cur_privilege)) (tσ σ t)
    = some (.Supervisor, tσ σ t) ∧
  execA (check_pma_with_pmp_priority acc pbmt .Supervisor (.Physaddr pa) w true) (tσ σ t)
    = some (.Ok pmaOkAligned, tσ σ t) ∧
  execA (pmpCheck (.Physaddr pa) w acc .Supervisor) (tσ σ t) = some (none, tσ σ t) ∧
  execA (within_mmio_readable (.Physaddr pa) w) (tσ σ t) = some (false, tσ σ t) ∧
  execA (within_mmio_writable (.Physaddr pa) w) (tσ σ t) = some (false, tσ σ t)

section amo
variable (img : Image) (dok : Int → Nat → Prop) (σ : ExecSt) (himg : img = imgOf σ)
include himg

theorem CertExecA {X : Type} (Q : Cst → X → ExecSt → Prop) (m : SailM X) (x : X) (d : Cdata)
    (r : Bool) (t s1 : ExecSt) :
    execA m (tσ σ t) = some (x, s1) → Q ⟨d, .BInf, r⟩ x ⟨s1.regs, t.mem, t.dev⟩ →
    AxCert.Cert img dok .DKRmw (fun _ _ _ => False) Q ⟨d, .BInf, r⟩ m t := by
  intro he hq
  subst himg
  have HE := execAEvA m _ x s1 he t rfl
  refine CertMono (imgOf σ) dok .DKRmw _ _ _ _ _ m t (fun _ _ _ h => h.elim) ?_
    (CertEvA (imgOf σ) dok .DKRmw _ m d r t HE)
  rintro s x' ⟨r', m', d'⟩ ⟨rfl, rfl, hr, hm, hd⟩
  simp only at hr hm hd
  subst hr hm hd
  exact hq

theorem CertExecASame {X : Type} (Q : Cst → X → ExecSt → Prop) (m : SailM X) (x : X) (d : Cdata)
    (r : Bool) (t : ExecSt) :
    execA m (tσ σ t) = some (x, tσ σ t) → Q ⟨d, .BInf, r⟩ x t →
    AxCert.Cert img dok .DKRmw (fun _ _ _ => False) Q ⟨d, .BInf, r⟩ m t :=
  fun he hq => CertExecA img dok σ himg Q m x d r t _ he hq

end amo

/-! ### (Lean-only) the stepping kit: Rocq's `a_use` / `a_useT` -/

section kit
variable {img : Image} {dok : Int → Nat → Prop} {σ : ExecSt} (himg : img = imgOf σ)
  {QE : Cst → Sail.Error exception → ExecSt → Prop}
include himg

theorem AxDataX7.cRUse {R X Y : Type}
    {Q : Cst → Except (Sail.Error exception ⊕ R) Y → ExecSt → Prop}
    {m : SailM X} {f : X → SailME R Y} {d : Cdata} {r : Bool} {t : ExecSt} {a : X}
    (He : execA m (tσ σ t) = some (a, tσ σ t))
    (H : AxCert.Cert img dok .DKRmw QE Q ⟨d, .BInf, r⟩ (ExceptT.run (f a)) t) :
    AxCert.Cert img dok .DKRmw QE Q ⟨d, .BInf, r⟩ (ExceptT.run (liftM m >>= f)) t :=
  AxCert4.cFactLift
    (CertExecASame img dok σ himg (fun s' x t' => s' = ⟨d, .BInf, r⟩ ∧ x = a ∧ t' = t) m a d r t
      He ⟨rfl, rfl, rfl⟩)
    (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H)

theorem AxDataX7.cRUseT {R X Y : Type}
    {Q : Cst → Except (Sail.Error exception ⊕ R) Y → ExecSt → Prop}
    {m : SailM X} {f : X → SailME R Y} {d : Cdata} {r : Bool} {t s1 : ExecSt} {a : X}
    (He : execA m (tσ σ t) = some (a, s1))
    (H : AxCert.Cert img dok .DKRmw QE Q ⟨d, .BInf, r⟩ (ExceptT.run (f a)) ⟨s1.regs, t.mem, t.dev⟩) :
    AxCert.Cert img dok .DKRmw QE Q ⟨d, .BInf, r⟩ (ExceptT.run (liftM m >>= f)) t :=
  AxCert4.cFactLift
    (CertExecA img dok σ himg (fun s' x t' => s' = ⟨d, .BInf, r⟩ ∧ x = a ∧
      t' = ⟨s1.regs, t.mem, t.dev⟩) m a d r t s1 He ⟨rfl, rfl, rfl⟩)
    (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H)

theorem AxDataX7.cFactUse {X Y : Type} {Q : Cst → Y → ExecSt → Prop}
    {m : SailM X} {f : X → SailM Y} {d : Cdata} {r : Bool} {t : ExecSt} {a : X}
    (He : execA m (tσ σ t) = some (a, tσ σ t))
    (H : AxCert.Cert img dok .DKRmw QE Q ⟨d, .BInf, r⟩ (f a) t) :
    AxCert.Cert img dok .DKRmw QE Q ⟨d, .BInf, r⟩ (m >>= f) t :=
  AxCert4.cFactQ
    (CertExecASame img dok σ himg (fun s' x t' => s' = ⟨d, .BInf, r⟩ ∧ x = a ∧ t' = t) m a d r t
      He ⟨rfl, rfl, rfl⟩)
    (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H)

end kit

/-- (Lean-only) `pure` in the early-return monad. -/
theorem AxDataX7.cRPure {img : Image} {dok : Int → Nat → Prop} {kind : Dkind} {R X : Type}
    {QE : Cst → Sail.Error exception → ExecSt → Prop}
    {Q : Cst → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop} {x : X} {s : Cst} {t : ExecSt}
    (H : Q s (.ok x) t) : AxCert.Cert img dok kind QE Q s (ExceptT.run (pure x : SailME R X)) t :=
  .cRet _ _ _ H

section loop
variable (img : Image) (dok : Int → Nat → Prop)

/-- Rocq `Cert_untilMT_1'` (lean-sail `untilFuelM 1`, in the early-return monad). -/
theorem CertUntilMT1' {R Vars : Type} (QE : Cst → Sail.Error exception → ExecSt → Prop)
    (Q : Cst → Except (Sail.Error exception ⊕ R) Vars → ExecSt → Prop) (vars : Vars)
    (cond : Vars → SailME R Bool) (body : Vars → SailME R Vars) (s : Cst) (t : ExecSt) :
    AxCert.Cert img dok .DKRmw QE (fun s' r t' => match r with
      | .ok v => AxCert.Cert img dok .DKRmw QE (fun s'' r' t'' => match r' with
          | .ok b => b = true ∧ Q s'' (.ok v) t''
          | .error e => Q s'' (.error e) t'') s' (ExceptT.run (cond v)) t'
      | .error e => Q s' (.error e) t') s (ExceptT.run (body vars)) t →
    AxCert.Cert img dok .DKRmw QE Q s (ExceptT.run (untilFuelM 1 cond vars body)) t := by
  intro Hb
  unfold untilFuelM untilFuelM.go
  rw [ExceptT.run_bind]
  apply CertBind
  refine CertMono img dok .DKRmw _ _ _ _ s _ t (fun _ _ _ h => h) ?_ Hb
  intro s' r t' hr
  rcases r with e | v
  · exact .cRet s' _ t' hr
  · show AxCert.Cert img dok .DKRmw QE Q s'
      (ExceptT.run (cond v >>= fun b => if b then pure v else _)) t'
    rw [ExceptT.run_bind]
    apply CertBind
    refine CertMono img dok .DKRmw _ _ _ _ s' _ t' (fun _ _ _ h => h) ?_ hr
    intro s'' r' t'' hr'
    rcases r' with e | b
    · exact .cRet s'' _ t'' hr'
    · obtain ⟨rfl, hq⟩ := hr'
      exact .cRet s'' _ t'' hq

/-- THE EXCLUSIVE READ NODE (acquire bit `aq`). -/
theorem CertReadRamXa (aq : Bool) (w : Nat) (QE : Cst → Sail.Error exception → ExecSt → Prop)
    (Q : Cst → (BitVec (8 * w) × Unit) → ExecSt → Prop) (pa : BitVec 64) (r : Bool) (t : ExecSt) :
    devAddr pa = false → dok (paZ pa) w →
    (∀ vs : List (BitVec 8), vs.length = w → Q ⟨.CRmwR aq vs, .BInf, r⟩ (rrv w vs, default_meta) t) →
    AxCert.Cert img dok .DKRmw QE Q ⟨.CPend, .BInf, r⟩
      (read_ram (if aq then .Read_RISCV_reserved_acquire else .Read_RISCV_reserved) (.Physaddr pa) w
        false) t := by
  intro hdev hdok hq
  cases aq <;>
  · simp only [read_ram, PreSail.sail_mem_read, PreSail.emit, ↓reduceIte, Bool.false_eq_true]
    refine .cXrd .BInf r w 64 _ _ t rfl hdev rfl hdok (fun vs hvs => ?_)
    exact .cRet _ _ _ (hq vs hvs)

/-- THE EXCLUSIVE (conditional) WRITE NODE. -/
theorem CertWriteRamXc (w : Nat) (QE : Cst → Sail.Error exception → ExecSt → Prop)
    (Q : Cst → Bool → ExecSt → Prop) (pa : BitVec 64) (data : BitVec (8 * w)) (aq : Bool)
    (rvs : List (BitVec 8)) (r : Bool) (t : ExecSt) :
    devAddr pa = false → dok (paZ pa) w →
    Q ⟨.CRmw aq false rvs (AxDataX.wrb w data) (wcls akXc r), .BInf, false⟩ true t →
    AxCert.Cert img dok .DKRmw QE Q ⟨.CRmwR aq rvs, .BInf, r⟩
      (write_ram .Write_RISCV_conditional (.Physaddr pa) w data ()) t := by
  intro hdev hdok hq
  simp only [write_ram, PreSail.sail_mem_write, PreSail.emit]
  refine .cXwr aq rvs .BInf r w 64 _ _ t data rfl hdev rfl rfl hdok ?_
  exact .cRet _ _ _ hq

end loop

/-- (Lean-only) The reserved read kind of `read_kind_of_flags aq false true`. -/
theorem AxDataX7.readKindFlagsX (aq : Bool) (s : ExecSt) :
    execA (read_kind_of_flags aq false true) s =
      some (if aq then .Read_RISCV_reserved_acquire else .Read_RISCV_reserved, s) := by
  cases aq <;> rfl

section chain
variable (img : Image) (dok : Int → Nat → Prop) (σ : ExecSt) (himg : img = imgOf σ)
  (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type) (w : Nat) (pa : BitVec 64)
  (hw : vmemWidth w)
include himg

include hw in
theorem CertCheckedMemReadX (aq : Bool)
    (Q : Cst → Result (BitVec (8 * w) × Unit) (physaddr × ExceptionType) → ExecSt → Prop)
    (r : Bool) (t : ExecSt) :
    amoFacts σ acc pbmt w pa t → devAddr pa = false → dok (paZ pa) w →
    (∀ vs : List (BitVec 8), vs.length = w →
      Q ⟨.CRmwR aq vs, .BInf, r⟩ (.Ok (rrv w vs, default_meta)) t) →
    AxCert.Cert img dok .DKRmw (fun _ _ _ => False) Q ⟨.CPend, .BInf, r⟩
      (checked_mem_read acc pbmt .Supervisor (.Physaddr pa) w aq false true false) t := by
  rintro ⟨_, hcp, hpmp, hmm, _⟩ hdev hdok hq
  unfold checked_mem_read
  apply CertCatchEarlyReturn
  refine AxCert4.cRAssoc ?_
  refine AxDataX7.cRUse himg hcp ?_
  refine AxCert4.cRPureBind ?_
  refine AxDataX7.cRUse himg (a := ((1 : Int), (w : Int))) rfl ?_
  simp only [misaligned_order, sys_misaligned_order_decreasing, ↓reduceIte, Bool.false_eq_true,
    Int.reduceSub, Int.toNat_zero]
  rcases hw with rfl | rfl | rfl | rfl
  all_goals
    cases acc <;> (try (rename_i p; cases p))
  all_goals
    · try dsimp only
      refine AxDataX7.cRUse himg (AxDataX7.readKindFlagsX aq _) ?_
      refine AxCert4.cRAssoc ?_
      refine AxCert4.cRBind ?_
      refine CertUntilMT1' img dok _ _ _ _ _ _ t ?_
      refine AxDataX7.cRUse himg rfl ?_
      simp only [bits_of_physaddr, Int.cast_ofNat_Int, Int.zero_mul, addIntZero, Int.toNat_one,
        Int.mul_one]
      refine AxDataX7.cRUse himg hpmp ?_
      dsimp only
      refine AxDataX7.cRUse himg hmm ?_
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine AxCert4.cRAssoc ?_
      refine AxCert4.cFactLift
        (P := fun s' x t' => ∃ vs : List (BitVec 8), vs.length = _ ∧ s' = ⟨.CRmwR _ vs, .BInf, r⟩ ∧
          x = (rrv _ vs, default_meta) ∧ t' = t)
        (CertReadRamXa img dok _ _ _ _ pa r t hdev hdok
          (fun vs hvs => ⟨vs, hvs, rfl, rfl, rfl⟩)) ?_
      rintro s' x t' ⟨vs, hvs, rfl, rfl, rfl⟩
      refine AxCert4.cRPureBind ?_
      refine AxDataX7.cRPure ?_
      refine AxDataX7.cRPure ⟨rfl, ?_⟩
      refine AxCert4.cRPureBind ?_
      refine AxDataX7.cRPure ?_
      refine AxDataX.substArg (fun v => Q _ v _) ?_ (hq vs hvs)
      simp only [Result.Ok.injEq, Prod.mk.injEq, and_true, Nat.reduceMul, Int.reduceMul,
        Int.reduceAdd, Int.reduceSub, Int.reduceToNat, BitVec.setWidth_eq]
      try simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.updateSubrange]
      try bv_decide

include hw in
theorem CertMemReadX (aq : Bool)
    (Q : Cst → Result (BitVec (8 * w)) (physaddr × ExceptionType) → ExecSt → Prop)
    (r : Bool) (t : ExecSt) :
    amoFacts σ acc pbmt w pa t → devAddr pa = false → dok (paZ pa) w →
    (∀ vs : List (BitVec 8), vs.length = w → Q ⟨.CRmwR aq vs, .BInf, r⟩ (.Ok (rrv w vs)) t) →
    AxCert.Cert img dok .DKRmw (fun _ _ _ => False) Q ⟨.CPend, .BInf, r⟩
      (mem_read acc pbmt (.Physaddr pa) w aq false true) t := by
  intro hf hdev hdok hq
  have heff := hf.1
  unfold mem_read
  ax_cert4_go
  refine AxDataX7.cFactUse himg heff ?_
  unfold mem_read_priv mem_read_priv_meta
  cases aq <;>
  · ax_cert4_go
    refine AxCert4.cFactQ (CertCheckedMemReadX img dok σ himg acc pbmt w pa hw _
      (fun s' x t' => ∃ vs : List (BitVec 8), vs.length = w ∧ s' = ⟨.CRmwR _ vs, .BInf, r⟩ ∧
        x = .Ok (rrv w vs, default_meta) ∧ t' = t) r t hf hdev hdok
      (fun vs hvs => ⟨vs, hvs, rfl, rfl, rfl⟩)) ?_
    rintro s' x t' ⟨vs, hvs, rfl, rfl, rfl⟩
    ax_cert4_go
    exact .cRet _ _ _ (hq vs hvs)

theorem CertMemWriteEaX (Q : Cst → Result Unit (physaddr × ExceptionType) → ExecSt → Prop)
    (d : Cdata) (r : Bool) (t : ExecSt) :
    amoFacts σ acc pbmt w pa t → Q ⟨d, .BInf, r⟩ (.Ok ()) t →
    AxCert.Cert img dok .DKRmw (fun _ _ _ => False) Q ⟨d, .BInf, r⟩
      (mem_write_ea (.Physaddr pa) w acc pbmt false false true) t := by
  rintro ⟨heff, hcp, hpmp, _⟩ hq
  unfold mem_write_ea
  apply CertCatchEarlyReturn
  ax_cert4_go
  refine AxDataX7.cRUse himg heff ?_
  ax_cert4_go
  refine AxDataX7.cRUse himg hcp ?_
  ax_cert4_go
  refine AxDataX7.cRUse himg (a := ((1 : Int), (w : Int))) rfl ?_
  simp only [misaligned_order, sys_misaligned_order_decreasing, ↓reduceIte, Bool.false_eq_true,
    Int.reduceSub, Int.toNat_zero, write_kind_of_flags]
  refine AxDataX7.cRUse himg rfl ?_
  refine AxCert4.cRBind ?_
  refine CertUntilMT1' img dok _ _ _ _ _ _ t ?_
  refine AxDataX7.cRUse himg rfl ?_
  simp only [bits_of_physaddr, Int.cast_ofNat_Int, Int.zero_mul, addIntZero, Int.toNat_natCast]
  refine AxDataX7.cRUse himg hpmp ?_
  dsimp only
  refine AxDataX7.cRPure ?_
  refine AxDataX7.cRPure ⟨rfl, ?_⟩
  refine AxDataX7.cRPure ?_
  exact hq

include hw in
theorem CertCheckedMemWriteX (data : BitVec (8 * w))
    (Q : Cst → Result Bool (physaddr × ExceptionType) → ExecSt → Prop) (aq : Bool)
    (rvs : List (BitVec 8)) (r : Bool) (t : ExecSt) :
    amoFacts σ acc pbmt w pa t → devAddr pa = false → dok (paZ pa) w →
    Q ⟨.CRmw aq false rvs (AxDataX.wrb w data) (wcls akXc r), .BInf, false⟩ (.Ok true) t →
    AxCert.Cert img dok .DKRmw (fun _ _ _ => False) Q ⟨.CRmwR aq rvs, .BInf, r⟩
      (checked_mem_write (.Physaddr pa) w data acc pbmt .Supervisor () false false true) t := by
  rintro ⟨_, hcp, hpmp, _, hmm⟩ hdev hdok hq
  unfold checked_mem_write
  apply CertCatchEarlyReturn
  refine AxCert4.cRAssoc ?_
  refine AxDataX7.cRUse himg hcp ?_
  refine AxCert4.cRPureBind ?_
  refine AxDataX7.cRUse himg (a := ((1 : Int), (w : Int))) rfl ?_
  simp only [misaligned_order, sys_misaligned_order_decreasing, ↓reduceIte, Bool.false_eq_true,
    Int.reduceSub, Int.toNat_zero, write_kind_of_flags]
  refine AxDataX7.cRUse himg rfl ?_
  refine AxCert4.cRBind ?_
  refine CertUntilMT1' img dok _ _ _ _ _ _ t ?_
  refine AxDataX7.cRUse himg rfl ?_
  simp only [bits_of_physaddr, Int.cast_ofNat_Int, Int.zero_mul, addIntZero, Int.toNat_natCast]
  refine AxDataX7.cRUse himg hpmp ?_
  dsimp only
  refine AxCert4.cRAssoc ?_
  refine AxDataX7.cRUse himg hmm ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine AxCert4.cRAssoc ?_
  refine AxCert4.cFactLift (P := fun s' b t' =>
      s' = ⟨.CRmw aq false rvs (AxDataX.wrb w _) (wcls akXc r), .BInf, false⟩ ∧ b = true ∧ t' = t)
    (CertWriteRamXc img dok w _ _ pa _ aq rvs r t hdev hdok ⟨rfl, rfl, rfl⟩) ?_
  rintro s' x t' ⟨rfl, rfl, rfl⟩
  refine AxCert4.cRPureBind ?_
  refine AxDataX7.cRPure ?_
  refine AxDataX7.cRPure ⟨rfl, ?_⟩
  refine AxDataX7.cRPure ?_
  refine AxDataX.substArg
    (fun z => Q ⟨.CRmw aq false rvs z (wcls akXc r), .BInf, false⟩ _ _) ?_ hq
  refine congrArg (AxDataX.wrb w) ?_
  rcases hw with rfl | rfl | rfl | rfl <;>
  · simp only [Sail.BitVec.extractLsb, Int.cast_ofNat_Int, Int.reduceMul, Int.reduceSub,
      Int.reduceToNat, Int.reduceAdd, Nat.reduceMul]
    bv_decide

include hw in
theorem CertMemWriteValueX (data : BitVec (8 * w))
    (Q : Cst → Result Bool (physaddr × ExceptionType) → ExecSt → Prop) (aq : Bool)
    (rvs : List (BitVec 8)) (r : Bool) (t : ExecSt) :
    amoFacts σ acc pbmt w pa t → devAddr pa = false → dok (paZ pa) w →
    Q ⟨.CRmw aq false rvs (AxDataX.wrb w data) (wcls akXc r), .BInf, false⟩ (.Ok true) t →
    AxCert.Cert img dok .DKRmw (fun _ _ _ => False) Q ⟨.CRmwR aq rvs, .BInf, r⟩
      (mem_write_value (.Physaddr pa) w data acc pbmt false false true) t := by
  intro hf hdev hdok hq
  have heff := hf.1
  unfold mem_write_value mem_write_value_meta
  ax_cert4_go
  refine AxDataX7.cFactUse himg heff ?_
  unfold mem_write_value_priv_meta
  ax_cert4_go
  refine AxCert4.cFactQ (CertCheckedMemWriteX img dok σ himg acc pbmt w pa hw data
    (fun s' x t' => s' = ⟨.CRmw aq false rvs (AxDataX.wrb w data) (wcls akXc r), .BInf, false⟩ ∧
      x = .Ok true ∧ t' = t) aq rvs r t hf hdev hdok ⟨rfl, rfl, rfl⟩) ?_
  rintro s' x t' ⟨rfl, rfl, rfl⟩
  ax_cert4_go
  exact .cRet _ _ _ hq

end chain

section top
variable (img : Image) (dok : Int → Nat → Prop) (σ : ExecSt) (himg : img = imgOf σ)
include himg

/-- THE AMO: `execute (AMO (AMOSWAP, aq, false, rs2, rs1, w, rd))`. -/
theorem CertExecuteAMOSWAP (aq : Bool) (rs2 rs1 rd : BitVec 5) (w : Nat) (va pa : BitVec 64)
    (Q : Cst → ExecutionResult → ExecSt → Prop) (r : Bool) (t s1 : ExecSt) :
    vmemWidth w →
    execA (get_transformed_data_addr (.Regidx rs1) (zeros (n := 64))
      (.Atomic (.AMOSWAP, aq, false, .Data, .Data)) w) (tσ σ t)
      = some (.Ext_DataAddr_OK (.Virtaddr va), tσ σ t) →
    is_aligned_vaddr (.Virtaddr va) w = true →
    execA (translateAddr (.Virtaddr va) (.Atomic (.AMOSWAP, aq, false, .Data, .Data))) (tσ σ t)
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1) →
    amoFacts σ (.Atomic (.AMOSWAP, aq, false, .Data, .Data)) .PBMT_PMA w pa
      ⟨s1.regs, t.mem, t.dev⟩ →
    devAddr pa = false → dok (paZ pa) w →
    (∀ vs : List (BitVec 8), vs.length = w → ∀ wvs t2,
      Q ⟨.CRmw aq false vs wvs (wcls akXc r), .BInf, false⟩ RETIRE_SUCCESS t2) →
    AxCert.Cert img dok .DKRmw (fun _ _ _ => False) Q ⟨.CPend, .BInf, r⟩
      (execute (.AMO (.AMOSWAP, aq, false, .Regidx rs2, .Regidx rs1, w, .Regidx rd))) t := by
  intro hw hgta hal htr hf hdev hdok hq
  show AxCert.Cert img dok .DKRmw _ Q _
    (execute_AMO .AMOSWAP aq false (.Regidx rs2) (.Regidx rs1) w (.Regidx rd)) t
  unfold execute_AMO
  apply CertCatchEarlyReturn
  have hw0 := hw
  rcases hw0 with rfl | rfl | rfl | rfl
  all_goals
    simp only [Bool.and_false]
    ax_cert4_go
    refine AxDataX7.cRUse himg (a := ()) rfl ?_
    ax_cert4_go
    refine AxDataX7.cRUse himg hgta ?_
    ax_cert4_go
    simp only [hal, Functions.not, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    ax_cert4_go
    refine AxDataX7.cRUseT himg htr ?_
    ax_cert4_go
    refine AxCert4.cFactLift (CertMemWriteEaX img dok σ himg _ .PBMT_PMA _ pa
      (fun s' x t' => s' = ⟨.CPend, .BInf, r⟩ ∧ x = .Ok () ∧ t' = ⟨s1.regs, t.mem, t.dev⟩)
      .CPend r _ hf ⟨rfl, rfl, rfl⟩) ?_
    rintro s' x t' ⟨rfl, rfl, rfl⟩
    ax_cert4_go
    refine AxCert4.cFactLift (CertMemReadX img dok σ himg _ .PBMT_PMA _ pa hw aq
      (fun s' x t' => ∃ vs : List (BitVec 8), vs.length = _ ∧ s' = ⟨.CRmwR aq vs, .BInf, r⟩ ∧
        x = .Ok (rrv _ vs) ∧ t' = ⟨s1.regs, t.mem, t.dev⟩) r _ hf hdev hdok
      (fun vs hvs => ⟨vs, hvs, rfl, rfl, rfl⟩)) ?_
    rintro s' x t' ⟨vs, hvs, rfl, rfl, rfl⟩
    ax_cert4_go
    refine AxCert4.cRUse (rf0EvA img _ _ (rf0RXBits rs2) _ _ _ (execRXBitsGpr rs2 _)) ?_
    ax_cert4_go
    refine AxCert4.cFactLift (CertMemWriteValueX img dok σ himg _ .PBMT_PMA _ pa hw _
      (fun s' x t' => ∃ wvs, s' = ⟨.CRmw aq false vs wvs (wcls akXc r), .BInf, false⟩ ∧
        x = .Ok true ∧ t' = ⟨s1.regs, t.mem, t.dev⟩) aq vs r _ hf hdev hdok ⟨_, rfl, rfl, rfl⟩) ?_
    rintro s' x t' ⟨wvs, rfl, rfl, rfl⟩
    ax_cert4_go
    refine AxCert4.cRUse (rf0EvA img _ _ (rf0WXBits rd _) _ _ _ (execWXBitsGpr rd _ _)) ?_
    ax_cert4_go
    exact .cRet _ _ _ (hq vs hvs wvs _)

end top

end Weak
