/-
Weak: **acquire's AMOSWAP on the POSITIONAL ENGINE, part 1 (pure, Sail-level)**: the AMO data
chain at `BFin` and the `CertB` of `amoswap.w{.aq} rd, rs2, (rs1)` whose data page is warm
(`hitW`).

Rocq: `iris/AxSpinAm.v` @ xxvzwolszwmp.

## The Rocq header, in substance

WHY A COPY.  `AxDataX7`'s AMO chain (`CertExecuteAMOSWAP` / `AxLeafS.CertExecuteAMOSWAPX`) is
proved at budget `BInf` through `CertExecASame` / `CertExecA` (`EvA` embeddings), which are FALSE
at `BFin` (an `EvA` derivation may read the image, consuming budget).  Exactly as `AxSpinE2` did
for loads / stores, the chain is replayed with the two `BFin`-sound embeddings `CertRf` (read-free
`execA` fact, any budget) and `CertExecA0` (read count 0 — the translation on a TLB HIT,
`dataTranslateHitS`).  The scripts are AxDataX7's with the stepping lemmas replaced.

ROW CONSUMPTION.  The exclusive read (`cXrd`) consumes NO row item and leaves the budget; the
exclusive write (`cXwr`) consumes ONE: `⟨CPend, BFin (b + 1), r⟩ ↦
⟨CRmw aq false rvs wvs (wcls akXc r), BFin b, false⟩` — the fused RMW is ONE row item.  The final
states `PXamo` are `CRmw` (never the half state `CRmwR`).

GENERIC over `aq` and the three registers (rl = false: xv6's release uses no AMO).  `rd ≠ x0` is
assumed (acquire's rd is a5).

§1 the chain `XBReadRamXa` … `XBExecuteAMOSWAP`;
§2 `CertBAmoswapS` (e = 1, symbolic registers: the read bytes `vs` demonic, rd := `amoLdv 4 vs`,
   written bytes `wrb 4 (amoStv 4 (gprVal rs rs2))`);
§3 `tokAmo`: `textOkB` of the real word `0x0cf4a7af` (`amoswap.w.aq a5, a5, (s1)`, acquire +
   0x1c), GENERIC IN THE PC.

KERNEL CROSS-CHECK: `Xv6/KernelImage.lean` has `⟨0x80000c74, 4, 0x0cf4a7af⟩` (acquire = 0x80000c58,
+ 0x1c) — no drift for this word.

## Deviations from Rocq

1. THE AxDataX7 / AxSpinE2 DEVIATIONS CARRY OVER (the scripts are theirs): lean-sail monads
   (early-return monad through `ExceptT.run`, `untilFuelM 1` via `AxSpinE2`'s `CertUntilMT1`),
   the Lean `checked_mem_read`'s match on the access (the read proofs case on `acc`; every arm is
   the reserved kind at `res = true`), `Z` widths ↦ `Nat` with the chain's `0 < w` (and
   `XBExecuteAMOSWAP`'s `0 < w → w ≤ 8`) ↦ `vmemWidth w`, per-width `bv_decide` closings for
   Rocq's `usvd_zeros_full_gen` / `subrange_full_gen_cast`; spellings `tσ`, `rrv`,
   `AxDataX.wrb`, `paZ`, `rd.toNat ≠ 0`, `zeros (n := 64)`, `accAmo`, `amoStv` / `amoLdv`,
   `wrOpt`, `gprVal`.  The rd write is the one uniform `wX_bits` step (AxDataX7 deviation 3), so
   `XBExecuteAMOSWAP`'s `rd.toNat ≠ 0` is kept but unused.
2. BUDGETS.  Rocq `BFin (S b)` ↦ `.BFin (b + 1)`; `CertB`'s `BFin (1 + b)` is rewritten by
   `Nat.add_comm`.
3. THE `rfF` SIDE CONDITIONS of Rocq `xb_use` are discharged by `AxSpinE2`'s `ax_spin_e2_rfs`;
   the `rX_bits` / `wX_bits` steps go through `rf0EvA` + `nrdOfRf0` and the Lean-only
   `AxSpinAm.cRUseNrd` (the `AxSpinE2.certEvANrd` embedding in the early-return monad).
4. Section variables / hypotheses (`img dok kind`, `Hkind` ↦ `hkind : kind = .DKRmw`,
   `σ Himg acc pbmt w pa Hw`, `σi T satp0 Hmode Hasid Hppn dok`) are explicit arguments in the
   section order (each declaration takes those its Rocq proof uses).  Rocq's statement-level
   `let t1` is inlined.  Before each `bv_decide` the proofs `clear` `hkind` / `kind` (AxSpinE2
   deviation 5: no `Dkind.enumToBitVec` auxiliaries).
5. §3: Rocq's `amoswap_acq_ast` (SC `WpAmo`) has no Lean SC constant: it is the Lean-only
   `AxSpinAm.amoswapAcqAst` (= `AxLeafS3.insAmo`, not imported).  `W_amoA` is a `BitVec 32`
   constant (Rocq `Z`, used only as `mword_of_int W_amoA : mword 32`).  Rocq's decode by
   `amodec` ↦ two kernel walks of the decoder (`AxSpinAm.walkAmoAM` on `drefM`,
   `AxSpinAm.walkAmoAS` on `WkEntryNew.drefS0`) combined by `WkEntryNew.execAnyCfg`, as
   `AxSpinE7.dec12`; `tokB`'s extra `sfAnnB 32 w = false` premise (AxSpinE7 deviation 4) is
   decided inside `tokAmo`, whose statement is Rocq's.

**Rocq → Lean name map.**  `XB_read_ram_xa` `XBReadRamXa`, `XB_write_ram_xc` `XBWriteRamXc`,
`XB_checked_mem_read_x` `XBCheckedMemReadX`, `XB_mem_read_x` `XBMemReadX`, `XB_mem_write_ea_x`
`XBMemWriteEaX`, `XB_checked_mem_write_x` `XBCheckedMemWriteX`, `XB_mem_write_value_x`
`XBMemWriteValueX`, `XB_execute_AMOSWAP` `XBExecuteAMOSWAP`, `ow_amoB` `owAmoB`, `PXamo` `PXamo`,
`CertB_amoswap_S` `CertBAmoswapS`, `W_amoA` `wAmoA`, `rfF_dec_amoA` `rfFDecAmoA`, `tok_amo`
`tokAmo`.  None is in the duplicated-name table.  Lean-only (file-qualified):
`AxSpinAm.cRUseNrd`, `AxSpinAm.amoswapAcqAst`, `AxSpinAm.walkAmoAM`, `AxSpinAm.walkAmoAS`,
`AxSpinAm.decAmoA`.

**Dropped:** nothing (Rocq 14 definitions/lemmas; Lean 14 + 5 Lean-only).
**Not ported:** the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxSpinE2
import Weak.AxSpinE7

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- (Lean-only, deviation 3) a read-free `EvA` fact with a determined result and state in the
early-return monad, at ANY certificate state. -/
theorem AxSpinAm.cRUseNrd {img : Image} {dok : Int → Nat → Prop} {kind : Dkind}
    {QE : Cst → Sail.Error exception → ExecSt → Prop} {R X Y : Type}
    {Q : Cst → Except (Sail.Error exception ⊕ R) Y → ExecSt → Prop}
    {m : SailM X} {f : X → SailME R Y} {s : Cst} {t t1 : ExecSt} {a : X}
    (Hm : EvA img (fun _ _ => False) (fun x t' => x = a ∧ t' = t1) m t) (Hn : nrd m)
    (H : AxCert.Cert img dok kind QE Q s (ExceptT.run (f a)) t1) :
    AxCert.Cert img dok kind QE Q s (ExceptT.run (liftM m >>= f)) t :=
  AxCert4.cFactLift (AxSpinE2.certEvANrd img dok kind _ m s t Hm Hn)
    (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H)

/-! # 1. The AMO chain at `BFin` -/

section amoB
variable (img : Image) (dok : Int → Nat → Prop) (kind : Dkind) (hkind : kind = .DKRmw)

include hkind in
/-- Rocq `XB_read_ram_xa`: THE EXCLUSIVE READ NODE — no row item, budget kept. -/
theorem XBReadRamXa (aq : Bool) (w : Nat) (QE : Cst → Sail.Error exception → ExecSt → Prop)
    (Q : Cst → (BitVec (8 * w) × Unit) → ExecSt → Prop) (pa : BitVec 64) (b : Bud) (r : Bool)
    (t : ExecSt) :
    devAddr pa = false → dok (paZ pa) w →
    (∀ vs : List (BitVec 8), vs.length = w → Q ⟨.CRmwR aq vs, b, r⟩ (rrv w vs, default_meta) t) →
    AxCert.Cert img dok kind QE Q ⟨.CPend, b, r⟩
      (read_ram (if aq then .Read_RISCV_reserved_acquire else .Read_RISCV_reserved) (.Physaddr pa) w
        false) t := by
  intro hdev hdok hq
  cases aq <;>
  · simp only [read_ram, PreSail.sail_mem_read, PreSail.emit, ↓reduceIte, Bool.false_eq_true]
    refine .cXrd b r w 64 _ _ t hkind hdev rfl hdok (fun vs hvs => ?_)
    exact .cRet _ _ _ (hq vs hvs)

include hkind in
/-- Rocq `XB_write_ram_xc`: THE EXCLUSIVE (conditional) WRITE NODE — one row item. -/
theorem XBWriteRamXc (w : Nat) (QE : Cst → Sail.Error exception → ExecSt → Prop)
    (Q : Cst → Bool → ExecSt → Prop) (pa : BitVec 64) (data : BitVec (8 * w)) (aq : Bool)
    (rvs : List (BitVec 8)) (b : Nat) (r : Bool) (t : ExecSt) :
    devAddr pa = false → dok (paZ pa) w →
    Q ⟨.CRmw aq false rvs (AxDataX.wrb w data) (wcls akXc r), .BFin b, false⟩ true t →
    AxCert.Cert img dok kind QE Q ⟨.CRmwR aq rvs, .BFin (b + 1), r⟩
      (write_ram .Write_RISCV_conditional (.Physaddr pa) w data ()) t := by
  intro hdev hdok hq
  simp only [write_ram, PreSail.sail_mem_write, PreSail.emit]
  exact .cXwr aq rvs (.BFin b) r w 64 _ _ t data hkind hdev rfl rfl hdok (.cRet _ _ _ hq)

section chain
variable (σ : ExecSt) (himg : img = imgOf σ) (acc : MemoryAccessType mem_payload)
  (pbmt : page_based_mem_type) (w : Nat) (pa : BitVec 64) (hw : vmemWidth w)
include himg

include hkind hw in
/-- Rocq `XB_checked_mem_read_x`. -/
theorem XBCheckedMemReadX (aq : Bool)
    (Q : Cst → Result (BitVec (8 * w) × Unit) (physaddr × ExceptionType) → ExecSt → Prop)
    (b : Bud) (r : Bool) (t : ExecSt) :
    amoFacts σ acc pbmt w pa t → devAddr pa = false → dok (paZ pa) w →
    (∀ vs : List (BitVec 8), vs.length = w →
      Q ⟨.CRmwR aq vs, b, r⟩ (.Ok (rrv w vs, default_meta)) t) →
    AxCert.Cert img dok kind (fun _ _ _ => False) Q ⟨.CPend, b, r⟩
      (checked_mem_read acc pbmt .Supervisor (.Physaddr pa) w aq false true false) t := by
  rintro ⟨_, hcp, hpmp, hmm, _⟩ hdev hdok hq
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
  all_goals
    · try dsimp only
      refine AxSpinE2.cRUse himg (AxDataX7.readKindFlagsX aq _) (by ax_spin_e2_rfs) ?_
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
        (P := fun s' x t' => ∃ vs : List (BitVec 8), vs.length = _ ∧ s' = ⟨.CRmwR _ vs, b, r⟩ ∧
          x = (rrv _ vs, default_meta) ∧ t' = t)
        (XBReadRamXa img dok kind hkind _ _ _ _ pa b r t hdev hdok
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
      clear hkind
      clear kind
      try bv_decide

include hkind hw in
/-- Rocq `XB_mem_read_x`. -/
theorem XBMemReadX (aq : Bool)
    (Q : Cst → Result (BitVec (8 * w)) (physaddr × ExceptionType) → ExecSt → Prop)
    (b : Bud) (r : Bool) (t : ExecSt) :
    amoFacts σ acc pbmt w pa t → devAddr pa = false → dok (paZ pa) w →
    (∀ vs : List (BitVec 8), vs.length = w → Q ⟨.CRmwR aq vs, b, r⟩ (.Ok (rrv w vs)) t) →
    AxCert.Cert img dok kind (fun _ _ _ => False) Q ⟨.CPend, b, r⟩
      (mem_read acc pbmt (.Physaddr pa) w aq false true) t := by
  intro hf hdev hdok hq
  have heff := hf.1
  unfold mem_read
  ax_cert4_go
  refine AxSpinE2.cFactUse himg heff (by ax_spin_e2_rfs) ?_
  unfold mem_read_priv mem_read_priv_meta
  cases aq <;>
  · ax_cert4_go
    refine AxCert4.cFactQ (XBCheckedMemReadX img dok kind hkind σ himg acc pbmt w pa hw _
      (fun s' x t' => ∃ vs : List (BitVec 8), vs.length = w ∧ s' = ⟨.CRmwR _ vs, b, r⟩ ∧
        x = .Ok (rrv w vs, default_meta) ∧ t' = t) b r t hf hdev hdok
      (fun vs hvs => ⟨vs, hvs, rfl, rfl, rfl⟩)) ?_
    rintro s' x t' ⟨vs, hvs, rfl, rfl, rfl⟩
    ax_cert4_go
    exact .cRet _ _ _ (hq vs hvs)

/-- Rocq `XB_mem_write_ea_x`: register-only, at ANY certificate state. -/
theorem XBMemWriteEaX (Q : Cst → Result Unit (physaddr × ExceptionType) → ExecSt → Prop)
    (s : Cst) (t : ExecSt) :
    amoFacts σ acc pbmt w pa t → Q s (.Ok ()) t →
    AxCert.Cert img dok kind (fun _ _ _ => False) Q s
      (mem_write_ea (.Physaddr pa) w acc pbmt false false true) t := by
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

include hkind hw in
/-- Rocq `XB_checked_mem_write_x`. -/
theorem XBCheckedMemWriteX (data : BitVec (8 * w))
    (Q : Cst → Result Bool (physaddr × ExceptionType) → ExecSt → Prop) (aq : Bool)
    (rvs : List (BitVec 8)) (b : Nat) (r : Bool) (t : ExecSt) :
    amoFacts σ acc pbmt w pa t → devAddr pa = false → dok (paZ pa) w →
    Q ⟨.CRmw aq false rvs (AxDataX.wrb w data) (wcls akXc r), .BFin b, false⟩ (.Ok true) t →
    AxCert.Cert img dok kind (fun _ _ _ => False) Q ⟨.CRmwR aq rvs, .BFin (b + 1), r⟩
      (checked_mem_write (.Physaddr pa) w data acc pbmt .Supervisor () false false true) t := by
  rintro ⟨_, hcp, hpmp, _, hmm⟩ hdev hdok hq
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
  refine AxCert4.cFactLift (P := fun s' b' t' =>
      s' = ⟨.CRmw aq false rvs (AxDataX.wrb w _) (wcls akXc r), .BFin b, false⟩ ∧ b' = true ∧
        t' = t)
    (XBWriteRamXc img dok kind hkind w _ _ pa _ aq rvs b r t hdev hdok ⟨rfl, rfl, rfl⟩) ?_
  rintro s' x t' ⟨rfl, rfl, rfl⟩
  refine AxCert4.cRPureBind ?_
  refine AxDataX7.cRPure ?_
  refine AxDataX7.cRPure ⟨rfl, ?_⟩
  refine AxDataX7.cRPure ?_
  refine AxDataX.substArg
    (fun z => Q ⟨.CRmw aq false rvs z (wcls akXc r), .BFin b, false⟩ _ _) ?_ hq
  refine congrArg (AxDataX.wrb w) ?_
  rcases hw with rfl | rfl | rfl | rfl <;>
  · simp only [Sail.BitVec.extractLsb, Int.cast_ofNat_Int, Int.reduceMul, Int.reduceSub,
      Int.reduceToNat, Int.reduceAdd, Nat.reduceMul]
    clear hkind
    clear kind
    bv_decide

include hkind hw in
/-- Rocq `XB_mem_write_value_x`. -/
theorem XBMemWriteValueX (data : BitVec (8 * w))
    (Q : Cst → Result Bool (physaddr × ExceptionType) → ExecSt → Prop) (aq : Bool)
    (rvs : List (BitVec 8)) (b : Nat) (r : Bool) (t : ExecSt) :
    amoFacts σ acc pbmt w pa t → devAddr pa = false → dok (paZ pa) w →
    Q ⟨.CRmw aq false rvs (AxDataX.wrb w data) (wcls akXc r), .BFin b, false⟩ (.Ok true) t →
    AxCert.Cert img dok kind (fun _ _ _ => False) Q ⟨.CRmwR aq rvs, .BFin (b + 1), r⟩
      (mem_write_value (.Physaddr pa) w data acc pbmt false false true) t := by
  intro hf hdev hdok hq
  have heff := hf.1
  unfold mem_write_value mem_write_value_meta
  ax_cert4_go
  refine AxSpinE2.cFactUse himg heff (by ax_spin_e2_rfs) ?_
  unfold mem_write_value_priv_meta
  ax_cert4_go
  refine AxCert4.cFactQ (XBCheckedMemWriteX img dok kind hkind σ himg acc pbmt w pa hw data
    (fun s' x t' => s' = ⟨.CRmw aq false rvs (AxDataX.wrb w data) (wcls akXc r), .BFin b, false⟩ ∧
      x = .Ok true ∧ t' = t) aq rvs b r t hf hdev hdok ⟨rfl, rfl, rfl⟩) ?_
  rintro s' x t' ⟨rfl, rfl, rfl⟩
  ax_cert4_go
  exact .cRet _ _ _ hq

end chain

include hkind in
/-- Rocq `XB_execute_AMOSWAP`: THE AMO at `BFin`,
`⟨CPend, BFin (b + 1), r⟩ ↦ ⟨CRmw …, BFin b, false⟩` (deviation 1). -/
theorem XBExecuteAMOSWAP (σ : ExecSt) (himg : img = imgOf σ) (aq : Bool) (rs2 rs1 rd : BitVec 5)
    (w : Nat) (va pa : BitVec 64) (Q : Cst → ExecutionResult → ExecSt → Prop) (b : Nat) (r : Bool)
    (t s1 : ExecSt) :
    vmemWidth w → rd.toNat ≠ 0 →
    execA (get_transformed_data_addr (.Regidx rs1) (zeros (n := 64)) (accAmo aq) w) (tσ σ t)
      = some (.Ext_DataAddr_OK (.Virtaddr va), tσ σ t) →
    is_aligned_vaddr (.Virtaddr va) w = true →
    execA (translateAddr (.Virtaddr va) (accAmo aq)) (tσ σ t)
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1) →
    cntA (translateAddr (.Virtaddr va) (accAmo aq)) (tσ σ t) = 0 →
    amoFacts σ (accAmo aq) .PBMT_PMA w pa ⟨s1.regs, t.mem, t.dev⟩ →
    devAddr pa = false → dok (paZ pa) w →
    (∀ vs : List (BitVec 8), vs.length = w →
      Q ⟨.CRmw aq false vs (AxDataX.wrb w (amoStv w (gprVal s1.regs rs2))) (wcls akXc r),
          .BFin b, false⟩
        RETIRE_SUCCESS (wrOpt (some (rd, amoLdv w vs)) ⟨s1.regs, t.mem, t.dev⟩)) →
    AxCert.Cert img dok kind (fun _ _ _ => False) Q ⟨.CPend, .BFin (b + 1), r⟩
      (execute (.AMO (.AMOSWAP, aq, false, .Regidx rs2, .Regidx rs1, w, .Regidx rd))) t := by
  intro hw _hrd hgta hal htr htrc hf hdev hdok hq
  show AxCert.Cert img dok kind _ Q _
    (execute_AMO .AMOSWAP aq false (.Regidx rs2) (.Regidx rs1) w (.Regidx rd)) t
  unfold execute_AMO
  apply CertCatchEarlyReturn
  have hw0 := hw
  rcases hw0 with rfl | rfl | rfl | rfl
  all_goals
    simp only [Bool.and_false]
    ax_cert4_go
    refine AxSpinE2.cRUse himg (a := ()) rfl (by ax_spin_e2_rfs) ?_
    ax_cert4_go
    refine AxSpinE2.cRUse himg hgta (by ax_spin_e2_rfs) ?_
    ax_cert4_go
    simp only [hal, Functions.not, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    ax_cert4_go
    refine AxSpinE2.cRUseT himg htr htrc ?_
    ax_cert4_go
    refine AxCert4.cFactLift (XBMemWriteEaX img dok kind σ himg _ .PBMT_PMA _ pa
      (fun s' x t' => s' = ⟨.CPend, .BFin (b + 1), r⟩ ∧ x = .Ok () ∧
        t' = ⟨s1.regs, t.mem, t.dev⟩) _ _ hf ⟨rfl, rfl, rfl⟩) ?_
    rintro s' x t' ⟨rfl, rfl, rfl⟩
    ax_cert4_go
    refine AxCert4.cFactLift (XBMemReadX img dok kind hkind σ himg _ .PBMT_PMA _ pa hw aq
      (fun s' x t' => ∃ vs : List (BitVec 8), vs.length = _ ∧
        s' = ⟨.CRmwR aq vs, .BFin (b + 1), r⟩ ∧ x = .Ok (rrv _ vs) ∧
        t' = ⟨s1.regs, t.mem, t.dev⟩) _ r _ hf hdev hdok
      (fun vs hvs => ⟨vs, hvs, rfl, rfl, rfl⟩)) ?_
    rintro s' x t' ⟨vs, hvs, rfl, rfl, rfl⟩
    ax_cert4_go
    refine AxSpinAm.cRUseNrd (rf0EvA img _ _ (rf0RXBits rs2) _ _ _ (execRXBitsGpr rs2 _))
      (nrdOfRf0 _ (rf0RXBits rs2)) ?_
    ax_cert4_go
    refine AxCert4.cFactLift (XBMemWriteValueX img dok kind hkind σ himg _ .PBMT_PMA _ pa hw _
      (fun s' x t' => s' = ⟨.CRmw aq false vs (AxDataX.wrb _ (amoStv _ (gprVal s1.regs rs2)))
          (wcls akXc r), .BFin b, false⟩ ∧
        x = .Ok true ∧ t' = ⟨s1.regs, t.mem, t.dev⟩) aq vs b r _ hf hdev hdok ⟨rfl, rfl, rfl⟩) ?_
    rintro s' x t' ⟨rfl, rfl, rfl⟩
    ax_cert4_go
    refine AxSpinAm.cRUseNrd (rf0EvA img _ _ (rf0WXBits rd _) _ _ _ (execWXBitsGpr rd _ _))
      (nrdOfRf0 _ (rf0WXBits rd _)) ?_
    ax_cert4_go
    exact .cRet _ _ _ (hq vs hvs)

end amoB

/-! # 2. The `CertB` of `amoswap.w{.aq}` on a warm data page -/

/-- Rocq `ow_amoB`: rd := the sign-extended read word, in the RMW's final state. -/
def owAmoB (rd : BitVec 5) (d : Cdata) : Option (BitVec 5 × BitVec 64) :=
  match d with
  | .CRmw _ _ rvs _ _ => some (rd, amoLdv 4 rvs)
  | _ => none

/-- Rocq `PXamo`: the final data states — the fused RMW, read bytes `vs` demonic, written bytes
rs2's low word, class `wcls akXc r`, release flag cleared. -/
def PXamo (aq : Bool) (rs : RegFile) (rs2 : BitVec 5) (r : Bool) : Cdata → Bool → Prop :=
  fun d r' => ∃ vs, d = .CRmw aq false vs (AxDataX.wrb 4 (amoStv 4 (gprVal rs rs2))) (wcls akXc r) ∧
    vs.length = 4 ∧ r' = false

section certB
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)

/-- Rocq `CertB_amoswap_S`: THE AMO LEAF'S CERTIFICATE — one row item (the fused exclusive
write). -/
theorem CertBAmoswapS (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (dok : Int → Nat → Prop) (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (aq : Bool)
    (rs2 rs1 rd : BitVec 5) (va pa : BitVec 64) (r : Bool) :
    rd.toNat ≠ 0 →
    va = gprVal rs rs1 + zeros (n := 64) →
    dataAtS σi T (accAmo aq) va 4 pa → hitW rs va → dok (paZ pa) 4 →
    CertB σi T satp0 dok .DKRmw rs pc is_rvc
      (.AMO (.AMOSWAP, aq, false, .Regidx rs2, .Regidx rs1, 4, .Regidx rd)) 1 none
      (owAmoB rd) .CPend r (PXamo aq rs rs2 r) := by
  intro hrd hva hda hhit hdok t ⟨hc, hW⟩ _ _ hag htl b
  have hva' : va = gprVal t.regs rs1 + zeros (n := 64) := by
    rw [gprValAgree _ _ _ hag]; exact hva
  have hhitT : hitW t.regs va := hitWAgree _ _ _ htl hhit
  have hc0 := hc
  obtain ⟨hpriv, -, -, hmenv, -, -, -, hms, -, -, hsatp, -⟩ := hc0
  obtain ⟨hMPRV, hSXL, hMXR, -⟩ := hms
  let σ : ExecSt := tσ σi t
  have heff : exec (effectivePrivilege (accAmo aq) (t.regs .mstatus) .Supervisor) σ
      = some (.Supervisor, σ) := execEffectivePrivilegeAmoS _ aq false σ hMPRV
  have hss : exec (is_shadow_stack_access (accAmo aq)) σ = some (false, σ) :=
    execIsShadowStackAmo aq false σ
  obtain ⟨htr, htrc⟩ :=
    dataTranslateHitS σi T satp0 hmode hasid hppn (accAmo aq) t va 4 pa hc hda hhitT heff hss
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hram, hal, hpal⟩ := hda
  obtain ⟨haf, hdev⟩ :=
    amoFactsS σi T satp0 aq ⟨σ.regs, t.mem, t.dev⟩ pa ⟨hc, hW⟩ hram hpal
  have hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (σ.regs .menvcfg)) = .PMM_Disabled := by
    show pmm_mode_backwards (_get_MEnvcfg_PMM (t.regs .menvcfg)) = .PMM_Disabled
    rw [hmenv]
    first
    | rfl
    | decide +kernel
  have hg : exec (get_transformed_data_addr (.Regidx rs1) (zeros (n := 64)) (accAmo aq) 4) σ
      = some (.Ext_DataAddr_OK (.Virtaddr va), σ) := by
    unfold get_transformed_data_addr
    rw [execBindSome _ _ _ _ _ (execExtDataGetAddrGpr rs1 _ (accAmo aq) 4 σ)]
    dsimp only
    rw [execBindSome _ _ _ _ _ (execTransformEffectiveAddressAmoS satp0 hmode aq _ σ hpriv hSXL
      hsatp hMPRV hMXR hpmm)]
    rw [hva']
    rfl
  to_a hg
  rw [Nat.add_comm]
  refine XBExecuteAMOSWAP (imgS σi) dok .DKRmw rfl σi rfl aq rs2 rs1 rd 4 va pa _ b r t σ
    (Or.inr (Or.inr (Or.inl rfl))) hrd hg hal htr htrc haf hdev hdok ?_
  intro vs hvs
  refine ⟨rfl, _, false, rfl, ⟨vs, ?_, hvs, rfl⟩, ?_⟩
  · rw [← gprValAgree _ _ _ hag]
  · cases t
    rfl

end certB

/-! # 3. The real word's `textOkB` -/

/-- Rocq `W_amoA`: `amoswap.w.aq a5, a5, (s1)` (acquire + 0x1c). -/
def wAmoA : BitVec 32 := 0x0cf4a7af#32

/-- (Lean-only, deviation 5; Rocq `WpAmo.amoswap_acq_ast`) `amoswap.w.aq a5, a5, (s1)`. -/
def AxSpinAm.amoswapAcqAst : instruction :=
  .AMO (.AMOSWAP, true, false, .Regidx 15#5, .Regidx 9#5, 4, .Regidx 15#5)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Rocq `rfF_dec_amoA`. -/
theorem rfFDecAmoA : rfF (ext_decode wAmoA) := by
  unfold wAmoA ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

section walks
attribute [local semireducible] LeanRV64D.Functions.hartSupports
  LeanRV64D.Functions.currentlyEnabled

/-- (Lean-only, deviation 5) the decode walk of `W_amoA` on the machine reference map. -/
theorem AxSpinAm.walkAmoAM :
    runRead drefM (ext_decode wAmoA) = some (AxSpinAm.amoswapAcqAst, true) := by kernel_rfl
/-- (Lean-only, deviation 5) the decode walk of `W_amoA` on the supervisor reference map. -/
theorem AxSpinAm.walkAmoAS :
    runRead WkEntryNew.drefS0 (ext_decode wAmoA) = some (AxSpinAm.amoswapAcqAst, true) := by
  kernel_rfl

end walks

/-- (Lean-only, deviation 5; Rocq `amodec`) the decode of `W_amoA`. -/
theorem AxSpinAm.decAmoA (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode wAmoA) s = some (AxSpinAm.amoswapAcqAst, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAm.walkAmoAM AxSpinAm.walkAmoAS s

/-- Rocq `tok_amo`: `amoswap.w.aq a5, a5, (s1)` at ANY pc whose 4-byte text word is
`0x0cf4a7af`. -/
theorem tokAmo (σi : ExecSt) (T : PTree) (satp0 : BitVec 64) (pc : BitVec 64) :
    textAt4S σi T pc wAmoA → textOkB σi T satp0 pc false AxSpinAm.amoswapAcqAst :=
  fun H => tokB σi T satp0 pc wAmoA _ H (by decide) rfFDecAmoA AxSpinAm.decAmoA

end Weak
