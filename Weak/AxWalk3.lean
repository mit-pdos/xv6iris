/-
Weak: **THE DEMONIC SV39 WALK at `CertWP`** — the Sv39 walk of `AxSpineOk4` (an `execA` replay
answered from the image) restated with each PTE read a DEMONIC, TAGGED walker read
(`CertWP.pWrd`: one row item, recorded as `(k, .WRd a vs)` at row position `k`), the three read
words pinned through `wpin` to `p2`, `p1` and the leaf class `P0`.

Rocq: `iris/AxWalk3.v` @ xxvzwolszwmp.

§1 the walker data node `PReadRamW`, `PCheckedMemReadW`, `PReadPte`; §1b the walker's
EXCLUSIVE nodes of the fused Svadu write-back (`PReadRamWx`/`PCheckedMemReadWx`/`PReadPteX`:
the re-read, fused read half `pWxrd`, no row item, pinned by `xpin`; `PWriteRamWxc`/
`PCheckedMemWriteWx`/`PWritePteCond`: the conditional write, fused write half `pWxwr`, one row
item); §2 the walk `PRecWalkLeaf`/`PRecWalkL1`/`PPtWalk`; §3 the miss, A/D-preset branch
`PTranslateTLBMissNoupd` (post TLB = `AxWalk3.tlbFill` with the READ leaf; `tlbAgreesAfterWalk`
preserves `AxPtProt.tlbOkPt`); §4 `PUpdateAndWritePteUpd` and `PTranslateTLBMiss` (BOTH
branches of the demonic leaf word).

## Deviations from Rocq

1. SPELLING (as `AxDataX`/`AxSpineOk4`): `mstate` ↦ `ExecSt`, `MState t.(sregs) σ.(mem)
   t.(mdev)` ↦ `⟨t.regs, σ.mem, t.dev⟩` (`tm`, an `abbrev`, = `AxDataX`'s `tσ`), `uint pa` ↦
   `paZ pa`, `Z.to_nat w` ↦ `w : Nat`, `S k` ↦ `k + 1`, `CS d b r` ↦ `⟨d, b, r⟩`, `rrv`/`wrb`
   from `AxDataX` (`wrb` = `AxDataX.wrb`, the bytes `pWxwr` records), `tt` ↦ `()`,
   `register_lookup r t.(sregs)` ↦ `t.regs .r`, `set_reg`/`vec_update_dec`/`tlb_hash (__id 39)`
   ↦ `setReg`/`vectorUpdate`/`tlb_hash 39`, `autocast (PPN_of_PTE q)` ↦ `ppn0 q`,
   `zero_extend' 64` ↦ `zero_extend (m := 64)`, `MISA_C` ↦ `misaC`, `eq_vec x 'b"0"` ↦
   `(x == 0#1) = true`, `PtAdBits.pte_set_ad` ↦ `pteSetAD`, `tlb_ok_pt`/`ptree_maps` ↦
   `AxPtProt.tlbOkPt`/`AxPtProt.ptreeMaps`, `PtTree.tlb_ok_pt_fill` ↦ `AxPtProt.tlbOkPtFill`.
2. READ KINDS: the Lean model's `checked_mem_read` reads a PTE with `Read_ttw` (Rocq:
   `Read_plain`), so `PReadRamW` takes `rk` with `rk = .Read_plain ∨ rk = .Read_ttw`, and
   `PCheckedMemReadW` takes `acc ≠ .InstructionFetch ()` (a fetch is not a walker event; as
   `AxDataX.XCheckedMemRead`). `PCheckedMemReadWx` needs no such premise (at `res = true` every
   access reads `Read_RISCV_reserved`).
3. `rfFAndInv`/`nlTrue`: Lean's model has no `and_boolM`; both are stated on the shape
   `pte_is_invalid f e >>= fun w1 => pure (not w1 && c)`. The walk proofs do not use `nlTrue`:
   the model lifts the test before an `if`, reduced directly (`AxWalk3.pFactUse` + `if_pos`).
4. `CertWPUntilMT1`: Rocq `untilMT` with measure 1 ↦ lean-sail `untilFuelM 1` in the
   early-return monad (as `AxDataX.CUntilMT1`).
5. Widths: Rocq's `0 < w` ↦ `vmemWidth w` (as `AxDataX` deviation 4).
6. TACTICS: Rocq `p_step`/`p_go`/`p_use`/`rff`/`nseipW` ↦ the Lean-only lemmas `AxWalk3.p*`
   and the tactic `ax_walk3_go`; `rfF` premises are passed explicitly.
7. Section `UserWalkP`'s hypotheses are the `ExecSC9` predicates (as `AxSpineOk4`):
   `H2i : pteValid p2`, `H2nl : ptePtr p2`, `H1i`/`H1nl` likewise, `H0i : ∀ q, P0 q → pteValid
   q`, `H0nl : … → pteLeaf q`, `Hchk0 : … → pteCheckOk acc p mxr do_sum q`, `H0N : … →
   (_get_PTE_Ext_N (ext_bits_of_PTE q) == 1#1) = false`; each theorem `include`s exactly the ones
   its Rocq proof uses.
8. THE WALK: Lean's `pt_walk` recurses on itself (no `_rec_pt_walk`, no `Acc` argument):
   `PRecWalkLeaf`/`PRecWalkL1` are stated on `pt_walk … (uNextBase p1) 0 g ()` /
   `(uNextBase p2) 1 g ()`; `PAssertTrue` is over lean-sail's `assert` (continuation on `()`,
   not on the proof). `ptwOut q g` = `uWalkOut (waddr0 vpn p1) q g`. The `translate_TLB_miss`
   posts are `.Ok (ppn0 q, .PBMT_PMA, ())`.
9. `update_PTE_Bits` premises are stated at the read word's width (`BitVec (8 * 8)`, Rocq
   `autocast … : mword 64`).

**Rocq → Lean name map.**  `rfF_within_mmio_writable` `rfFWithinMmioWritable`,
`rfF_currentlyEnabled_Svadu` `rfFCurrentlyEnabledSvadu`, `execA_currentlyEnabled_Svadu`
`execACurrentlyEnabledSvadu`, `tm` `tm`, `sregs_tm` `sregsTm`, `CertWP_execA_same`
`CertWPExecASame`, `rfF_and_inv` `rfFAndInv`, `CertWP_untilMT_1` `CertWPUntilMT1`,
`P_read_ram_w` `PReadRamW`, `P_checked_mem_read_w` `PCheckedMemReadW`, `P_read_pte` `PReadPte`,
`P_read_ram_wx` `PReadRamWx`, `P_write_ram_wxc` `PWriteRamWxc`, `P_checked_mem_read_wx`
`PCheckedMemReadWx`, `P_checked_mem_write_wx` `PCheckedMemWriteWx`, `pte_x_ok` `pteXOk`,
`P_read_pte_x` `PReadPteX`, `P_write_pte_cond` `PWritePteCond`, `pte_rd_ok` `pteRdOk`,
`waddr2/1/0` `waddr2/1/0`, `ptw_out` `ptwOut`, `P_assert_true` `PAssertTrue`,
`P_rec_walk_leaf` `PRecWalkLeaf`, `nl_true` `nlTrue`, `P_rec_walk_l1` `PRecWalkL1`,
`P_pt_walk` `PPtWalk`, `tlb_fill` `AxWalk3.tlbFill` (duplicated name: AxSymCtl4),
`P_translate_TLB_miss_noupd` `PTranslateTLBMissNoupd`, `P_update_and_write_pte_upd`
`PUpdateAndWritePteUpd`, `execA_add_to_TLB_gen` `execAAddToTLBGen`, `P_translate_TLB_miss`
`PTranslateTLBMiss`, `tlb_agrees_after_walk` `tlbAgreesAfterWalk`.
Lean-only (file-qualified): `AxWalk3.pFact`, `pFactRead`, `pFactPure`, `pFactAssoc`, `pFactUse`,
`pRBind`, `pRLift`, `pRRead`, `pRPureBind`, `pRAssoc`, `pRPure`, `pRUse`; tactic `ax_walk3_go`.

**Dropped:** none.
-/
import Weak.AxWalk
import Weak.AxDataX
import Weak.AxSpineOk4
import Weak.AxPtProt

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- Rocq `rfF_within_mmio_writable`. -/
theorem rfFWithinMmioWritable (pa : physaddr) (w : Nat) : rfF (within_mmio_writable pa w) := by
  rff_auto

/-- Rocq `rfF_currentlyEnabled_Svadu`. -/
theorem rfFCurrentlyEnabledSvadu : rfF (currentlyEnabled .Ext_Svadu) := by rff_auto

/-- Rocq `execA_currentlyEnabled_Svadu`. -/
theorem execACurrentlyEnabledSvadu (s : ExecSt) :
    execA (currentlyEnabled .Ext_Svadu) s = some (true, s) :=
  execAOfRfF _ rfFCurrentlyEnabledSvadu s _ (execCurrentlyEnabledSvadu s)

/-- Rocq `tm`: the image state `σ`'s memory at the thread's registers and devices. -/
abbrev tm (σ t : ExecSt) : ExecSt := ⟨t.regs, σ.mem, t.dev⟩

/-- Rocq `sregs_tm`. -/
theorem sregsTm (σ t : ExecSt) : t.regs = (tm σ t).regs := rfl

/-- Rocq `CertWP_execA_same`: a register-only `execA` fact that leaves the state alone. -/
theorem CertWPExecASame (img : Image) (dok wok : Int → Nat → Prop) (kind : Dkind)
    (pR pX : (Int → Nat → Prop) → Nat → Prop) (wpin xpin : Nat → Int → List (BitVec 8) → Prop)
    {X : Type} (QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop)
    (Q : List (Nat × Wev) → Cst → Nat → X → ExecSt → Prop) (m : SailM X) (s0 : ExecSt) (x : X)
    (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (t : ExecSt) :
    rfF m → execA m s0 = some (x, s0) → t.regs = s0.regs → Q ws s k x t →
    CertWP img dok wok kind pR pX wpin xpin QE Q ws s k m t := by
  intro Hrf He Ht HQ
  refine CertWPExecARfFPost img dok wok kind pR pX wpin xpin QE Q m s0 x s0 t ws s k Hrf He Ht ?_
  rw [← Ht]
  exact HQ

/-! # 0. (Lean-only) the stepping kit at `CertWP` (Rocq's `p_step` / `p_go` / `p_use`) -/

section kit
variable {img : Image} {dok wok : Int → Nat → Prop} {kind : Dkind}
  {pR pX : (Int → Nat → Prop) → Nat → Prop} {wpin xpin : Nat → Int → List (BitVec 8) → Prop}

local notation "CW" => CertWP img dok wok kind pR pX wpin xpin

theorem AxWalk3.pFact {X Y : Type}
    {QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop}
    {P : List (Nat × Wev) → Cst → Nat → X → ExecSt → Prop}
    {Q : List (Nat × Wev) → Cst → Nat → Y → ExecSt → Prop}
    {m : SailM X} {f : X → SailM Y} {ws : List (Nat × Wev)} {s : Cst} {k : Nat} {t : ExecSt}
    (Hm : CW (fun _ _ _ _ _ => False) P ws s k m t)
    (Hf : ∀ ws' s' k' x t', P ws' s' k' x t' → CW QE Q ws' s' k' (f x) t') :
    CW QE Q ws s k (m >>= f) t :=
  CertWPBind img dok wok kind pR pX wpin xpin QE Q m f ws s k t
    (CertWPMono img dok wok kind pR pX wpin xpin _ _ _ _ ws s k m t (fun _ _ _ _ _ h => h.elim) Hf
      Hm)

theorem AxWalk3.pFactRead {Y : Type}
    {QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop}
    {Q : List (Nat × Wev) → Cst → Nat → Y → ExecSt → Prop} {r : Register}
    {f : RegisterType r → SailM Y} {ws : List (Nat × Wev)} {s : Cst} {k : Nat} {t : ExecSt}
    (hr : ¬ AxRunClose.pinReg r) (H : CW QE Q ws s k (f (t.regs r)) t) :
    CW QE Q ws s k (readReg r >>= f) t :=
  .pRd ws s k r _ t (fun h => absurd h hr) (fun _ => H)

theorem AxWalk3.pFactPure {X Y : Type}
    {QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop}
    {Q : List (Nat × Wev) → Cst → Nat → Y → ExecSt → Prop} {x : X} {f : X → SailM Y}
    {ws : List (Nat × Wev)} {s : Cst} {k : Nat} {t : ExecSt}
    (H : CW QE Q ws s k (f x) t) : CW QE Q ws s k (pure x >>= f) t := H

theorem AxWalk3.pFactAssoc {X Y Z : Type}
    {QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop}
    {Q : List (Nat × Wev) → Cst → Nat → Z → ExecSt → Prop} {m : SailM X} {f : X → SailM Y}
    {g : Y → SailM Z} {ws : List (Nat × Wev)} {s : Cst} {k : Nat} {t : ExecSt}
    (H : CW QE Q ws s k (m >>= fun x => f x >>= g) t) : CW QE Q ws s k ((m >>= f) >>= g) t := by
  rw [bind_assoc]; exact H

/-- Rocq `p_use` (base monad): a register-only `execA` fact at the image state `tm μ t`. -/
theorem AxWalk3.pFactUse {X Y : Type}
    {QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop}
    {Q : List (Nat × Wev) → Cst → Nat → Y → ExecSt → Prop} {μ : ExecSt} {m : SailM X}
    {f : X → SailM Y} {ws : List (Nat × Wev)} {s : Cst} {k : Nat} {t : ExecSt} {a : X}
    (hrf : rfF m) (He : execA m (tm μ t) = some (a, tm μ t)) (H : CW QE Q ws s k (f a) t) :
    CW QE Q ws s k (m >>= f) t :=
  AxWalk3.pFact (P := fun ws' s' k' x t' => ws' = ws ∧ s' = s ∧ k' = k ∧ x = a ∧ t' = t)
    (CertWPExecASame img dok wok kind pR pX wpin xpin _ _ m (tm μ t) a ws s k t hrf He rfl
      ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (fun _ _ _ _ _ h => by obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h; exact H)

/-- The early-return monad's bind, through `ExceptT.run`. -/
theorem AxWalk3.pRBind {R X Y : Type}
    (QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop)
    (Q : List (Nat × Wev) → Cst → Nat → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop)
    (m : SailME R Y) (f : Y → SailME R X) (ws : List (Nat × Wev)) (s : Cst) (k : Nat)
    (t : ExecSt) :
    CW QE (fun ws' s' k' r t' => match r with
      | .ok a => CW QE Q ws' s' k' (ExceptT.run (f a)) t'
      | .error e => Q ws' s' k' (.error e) t') ws s k (ExceptT.run m) t →
    CW QE Q ws s k (ExceptT.run (m >>= f)) t := by
  intro H
  rw [ExceptT.run_bind]
  apply CertWPBind
  refine CertWPMono img dok wok kind pR pX wpin xpin _ _ _ _ ws s k _ t (fun _ _ _ _ _ h => h) ?_ H
  intro ws' s' k' r t' h
  cases r with
  | ok a => exact h
  | error e => exact .pRet _ _ _ _ _ h

theorem AxWalk3.pRLift {R X Y : Type}
    {QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop}
    {P : List (Nat × Wev) → Cst → Nat → X → ExecSt → Prop}
    {Q : List (Nat × Wev) → Cst → Nat → Except (Sail.Error exception ⊕ R) Y → ExecSt → Prop}
    {m : SailM X} {f : X → SailME R Y} {ws : List (Nat × Wev)} {s : Cst} {k : Nat} {t : ExecSt}
    (Hm : CW (fun _ _ _ _ _ => False) P ws s k m t)
    (Hf : ∀ ws' s' k' x t', P ws' s' k' x t' → CW QE Q ws' s' k' (ExceptT.run (f x)) t') :
    CW QE Q ws s k (ExceptT.run (liftM m >>= f)) t := by
  apply AxWalk3.pRBind
  refine CertWPMono img dok wok kind pR pX wpin xpin _ _ _ _ ws s k _ t (fun _ _ _ _ _ h => h) ?_
    (CertWPLiftR img dok wok kind pR pX wpin xpin QE P m ws s k t Hm)
  intro ws' s' k' r t' h
  cases r with
  | ok a => exact Hf ws' s' k' a t' h
  | error e => exact h.elim

theorem AxWalk3.pRRead {R X : Type}
    {QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop}
    {Q : List (Nat × Wev) → Cst → Nat → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {r : Register} {f : RegisterType r → SailME R X} {ws : List (Nat × Wev)} {s : Cst} {k : Nat}
    {t : ExecSt} (hr : ¬ AxRunClose.pinReg r) (H : CW QE Q ws s k (ExceptT.run (f (t.regs r))) t) :
    CW QE Q ws s k (ExceptT.run (liftM (readReg r) >>= f)) t :=
  AxWalk3.pRLift (P := fun ws' s' k' x t' => ws' = ws ∧ s' = s ∧ k' = k ∧ x = t.regs r ∧ t' = t)
    (CertWPReadReg img dok wok kind pR pX wpin xpin _ r _ ws s k t hr ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (fun _ _ _ _ _ h => by obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h; exact H)

theorem AxWalk3.pRPureBind {R X Y : Type}
    {QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop}
    {Q : List (Nat × Wev) → Cst → Nat → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {x : Y} {f : Y → SailME R X} {ws : List (Nat × Wev)} {s : Cst} {k : Nat} {t : ExecSt}
    (H : CW QE Q ws s k (ExceptT.run (f x)) t) : CW QE Q ws s k (ExceptT.run (pure x >>= f)) t := H

theorem AxWalk3.pRAssoc {R X Y Z : Type}
    {QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop}
    {Q : List (Nat × Wev) → Cst → Nat → Except (Sail.Error exception ⊕ R) Z → ExecSt → Prop}
    {m : SailME R X} {f : X → SailME R Y} {g : Y → SailME R Z} {ws : List (Nat × Wev)} {s : Cst}
    {k : Nat} {t : ExecSt} (H : CW QE Q ws s k (ExceptT.run (m >>= fun x => f x >>= g)) t) :
    CW QE Q ws s k (ExceptT.run ((m >>= f) >>= g)) t := by
  rw [bind_assoc]; exact H

theorem AxWalk3.pRPure {R X : Type}
    {QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop}
    {Q : List (Nat × Wev) → Cst → Nat → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {x : X} {ws : List (Nat × Wev)} {s : Cst} {k : Nat} {t : ExecSt} (H : Q ws s k (.ok x) t) :
    CW QE Q ws s k (ExceptT.run (pure x : SailME R X)) t :=
  .pRet _ _ _ _ _ H

/-- Rocq `p_use` (early-return monad). -/
theorem AxWalk3.pRUse {R X Y : Type}
    {QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop}
    {Q : List (Nat × Wev) → Cst → Nat → Except (Sail.Error exception ⊕ R) Y → ExecSt → Prop}
    {μ : ExecSt} {m : SailM X} {f : X → SailME R Y} {ws : List (Nat × Wev)} {s : Cst} {k : Nat}
    {t : ExecSt} {a : X} (hrf : rfF m) (He : execA m (tm μ t) = some (a, tm μ t))
    (H : CW QE Q ws s k (ExceptT.run (f a)) t) : CW QE Q ws s k (ExceptT.run (liftM m >>= f)) t :=
  AxWalk3.pRLift (P := fun ws' s' k' x t' => ws' = ws ∧ s' = s ∧ k' = k ∧ x = a ∧ t' = t)
    (CertWPExecASame img dok wok kind pR pX wpin xpin _ _ m (tm μ t) a ws s k t hrf He rfl
      ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (fun _ _ _ _ _ h => by obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h; exact H)

end kit

/-- (Lean-only) Rocq `p_go`: run the register reads, `pure`s and re-associate binds, in both
monads. -/
macro "ax_walk3_go" : tactic => `(tactic| repeat (first
  | ((with_reducible refine AxWalk3.pRRead ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | with_reducible refine AxWalk3.pRPureBind ?_
  | with_reducible refine AxWalk3.pRAssoc ?_
  | with_reducible refine AxWalk3.pFactAssoc ?_
  | ((with_reducible refine AxWalk3.pFactRead ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | with_reducible refine AxWalk3.pFactPure ?_))

section walk
variable (img : Image) (dok wok : Int → Nat → Prop) (kind : Dkind)
variable (pR pX : (Int → Nat → Prop) → Nat → Prop) (wpin xpin : Nat → Int → List (BitVec 8) → Prop)

local notation "CW" => CertWP img dok wok kind pR pX wpin xpin

/-- Rocq `rfF_and_inv` (deviation 3): the valid-and-test's footprint. -/
theorem rfFAndInv (f : BitVec 8) (e : BitVec 10) (c : Bool) :
    rfF (pte_is_invalid f e >>= fun w1 => pure (Functions.not w1 && c)) :=
  rfFBind _ _ (rfFPteIsInvalid f e) (fun _ => trivial)

/-- Rocq `CertWP_untilMT_1` (deviation 4): lean-sail `untilFuelM 1`, in the early-return
monad. -/
theorem CertWPUntilMT1 {R Vars : Type}
    (QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop)
    (Q : List (Nat × Wev) → Cst → Nat → Except (Sail.Error exception ⊕ R) Vars → ExecSt → Prop)
    (vars : Vars) (cond : Vars → SailME R Bool) (body : Vars → SailME R Vars)
    (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (t : ExecSt) :
    CW QE (fun ws' s' k' r t' => match r with
      | .ok v => CW QE (fun ws'' s'' k'' r' t'' => match r' with
          | .ok b => b = true ∧ Q ws'' s'' k'' (.ok v) t''
          | .error e => Q ws'' s'' k'' (.error e) t'') ws' s' k' (ExceptT.run (cond v)) t'
      | .error e => Q ws' s' k' (.error e) t') ws s k (ExceptT.run (body vars)) t →
    CW QE Q ws s k (ExceptT.run (untilFuelM 1 cond vars body)) t := by
  intro Hb
  unfold untilFuelM untilFuelM.go
  rw [ExceptT.run_bind]
  apply CertWPBind
  refine CertWPMono img dok wok kind pR pX wpin xpin _ _ _ _ ws s k _ t (fun _ _ _ _ _ h => h) ?_ Hb
  intro ws' s' k' r t' hr
  rcases r with e | v
  · exact .pRet _ _ _ _ _ hr
  · show CW QE Q ws' s' k' (ExceptT.run (cond v >>= fun b => if b then pure v else _)) t'
    rw [ExceptT.run_bind]
    apply CertWPBind
    refine CertWPMono img dok wok kind pR pX wpin xpin _ _ _ _ ws' s' k' _ t'
      (fun _ _ _ _ _ h => h) ?_ hr
    intro ws'' s'' k'' r' t'' hr'
    rcases r' with e | b
    · exact .pRet _ _ _ _ _ hr'
    · obtain ⟨rfl, hq⟩ := hr'
      exact .pRet _ _ _ _ _ hq

/-! # 1. The walker read chain -/

/-- Rocq `P_read_ram_w` (deviation 2): the walker data node at a non-latest, non-fetch RAM read
kind (the Lean model's walker reads are `Read_ttw`). -/
theorem PReadRamW (rk : read_kind) (hrk : rk = .Read_plain ∨ rk = .Read_ttw) (w : Nat)
    (QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop)
    (Q : List (Nat × Wev) → Cst → Nat → (BitVec (8 * w) × Unit) → ExecSt → Prop)
    (pa : BitVec 64) (ws : List (Nat × Wev)) (d : Cdata) (b : Bud) (r : Bool) (k : Nat)
    (t : ExecSt) :
    devAddr pa = false → wok (paZ pa) w → pR wok k →
    (∀ vs : List (BitVec 8), vs.length = w → wpin k (paZ pa) vs →
      Q (ws ++ [(k, .WRd (paZ pa) vs)]) ⟨d, b, r⟩ (k + 1) (rrv w vs, default_meta) t) →
    CW QE Q ws ⟨d, bsucc b, r⟩ k (read_ram rk (.Physaddr pa) w false) t := by
  intro hdev hwok hp hq
  rcases hrk with rfl | rfl <;>
  · simp only [read_ram, PreSail.sail_mem_read, PreSail.emit]
    exact .pWrd ws d b r k w 64 _ _ t hdev rfl rfl hwok hp
      (fun vs hvs hpin => .pRet _ _ _ _ _ (hq vs hvs hpin))

/-- Rocq `P_checked_mem_read_w` (deviations 2, 5). -/
theorem PCheckedMemReadW (μ : ExecSt) (acc : MemoryAccessType mem_payload)
    (pbmt : page_based_mem_type) (w : Nat) (pa : BitVec 64) (hw : vmemWidth w)
    (hacc : acc ≠ .InstructionFetch ())
    (Q : List (Nat × Wev) → Cst → Nat → Result (BitVec (8 * w) × Unit) (physaddr × ExceptionType) →
      ExecSt → Prop)
    (ws : List (Nat × Wev)) (d : Cdata) (b : Bud) (r : Bool) (k : Nat) (t : ExecSt) :
    execA (check_pma_with_pmp_priority acc pbmt .Supervisor (.Physaddr pa) w false) (tm μ t)
      = some (.Ok pmaOkAligned, tm μ t) →
    execA (pmpCheck (.Physaddr pa) w acc .Supervisor) (tm μ t) = some (none, tm μ t) →
    execA (within_mmio_readable (.Physaddr pa) w) (tm μ t) = some (false, tm μ t) →
    devAddr pa = false → wok (paZ pa) w → pR wok k →
    (∀ vs : List (BitVec 8), vs.length = w → wpin k (paZ pa) vs →
      Q (ws ++ [(k, .WRd (paZ pa) vs)]) ⟨d, b, r⟩ (k + 1) (.Ok (rrv w vs, default_meta)) t) →
    CW (fun _ _ _ _ _ => False) Q ws ⟨d, bsucc b, r⟩ k
      (checked_mem_read acc pbmt .Supervisor (.Physaddr pa) w false false false false) t := by
  intro hcp hpmp hmm hdev hwok hp hq
  unfold checked_mem_read
  apply CertWPCatchEarlyReturn
  refine AxWalk3.pRAssoc ?_
  refine AxWalk3.pRUse (μ := μ) (rfFCheckPmaWithPmpPriority _ _ _ _ _ _) hcp ?_
  refine AxWalk3.pRPureBind ?_
  refine AxWalk3.pRUse (μ := μ) (a := ((1 : Int), (w : Int))) (rfFSplitMisaligned _ _ _ _) rfl ?_
  simp only [misaligned_order, sys_misaligned_order_decreasing, ↓reduceIte, Bool.false_eq_true,
    Int.reduceSub, Int.toNat_zero]
  rcases hw with rfl | rfl | rfl | rfl
  all_goals
    cases acc <;> (try (rename_i p; cases p))
  all_goals try exact absurd rfl hacc
  all_goals
    simp only [read_kind_of_flags]
    first
      | refine AxWalk3.pRUse (μ := μ) (rfFReadKindOfFlags _ _ _) rfl ?_
      | refine AxWalk3.pRPureBind ?_
    refine AxWalk3.pRAssoc ?_
    refine AxWalk3.pRBind _ _ _ _ _ _ _ _ ?_
    refine CertWPUntilMT1 img dok wok kind pR pX wpin xpin _ _ _ _ _ _ _ _ _ ?_
    refine AxWalk3.pRUse (μ := μ) (by trivial) rfl ?_
    simp only [bits_of_physaddr, Int.cast_ofNat_Int, Int.zero_mul, addIntZero, Int.toNat_one,
      Int.mul_one]
    refine AxWalk3.pRUse (μ := μ) (rfFPmpCheck _ _ _ _) hpmp ?_
    dsimp only
    refine AxWalk3.pRUse (μ := μ) (rfFWithinMmioReadable _ _) hmm ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine AxWalk3.pRAssoc ?_
    refine AxWalk3.pRLift
      (P := fun ws' s' k' x t' => ∃ vs : List (BitVec 8), vs.length = _ ∧ wpin k (paZ pa) vs ∧
        ws' = ws ++ [(k, .WRd (paZ pa) vs)] ∧ s' = ⟨d, b, r⟩ ∧ k' = k + 1 ∧
        x = (rrv _ vs, default_meta) ∧ t' = t)
      (PReadRamW img dok wok kind pR pX wpin xpin _ (by simp) _ _ _ pa ws d b r k t hdev hwok hp
        (fun vs hvs hpin => ⟨vs, hvs, hpin, rfl, rfl, rfl, rfl, rfl⟩)) ?_
    rintro ws' s' k' x t' ⟨vs, hvs, hpin, rfl, rfl, rfl, rfl, rfl⟩
    refine AxWalk3.pRPureBind ?_
    refine AxWalk3.pRPure ?_
    refine AxWalk3.pRPure ⟨rfl, ?_⟩
    refine AxWalk3.pRPureBind ?_
    refine AxWalk3.pRPure ?_
    refine AxDataX.substArg (fun v => Q _ _ _ v _) ?_ (hq vs hvs hpin)
    simp only [Result.Ok.injEq, Prod.mk.injEq, and_true, Nat.reduceMul, Int.reduceMul,
      Int.reduceAdd, Int.reduceSub, Int.reduceToNat, BitVec.setWidth_eq]
    try simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.updateSubrange]
    try bv_decide

/-- THE DEMONIC PTE READ (Rocq `P_read_pte`, 8 bytes): one walker row item. -/
theorem PReadPte (μ : ExecSt) (pa : BitVec 64)
    (Q : List (Nat × Wev) → Cst → Nat → Result (BitVec (8 * 8)) (physaddr × ExceptionType) →
      ExecSt → Prop)
    (ws : List (Nat × Wev)) (d : Cdata) (b : Bud) (r : Bool) (k : Nat) (t : ExecSt) :
    execA (check_pma_with_pmp_priority (.Load .PageTableEntry) .PBMT_PMA .Supervisor
      (.Physaddr pa) 8 false) (tm μ t) = some (.Ok pmaOkAligned, tm μ t) →
    execA (pmpCheck (.Physaddr pa) 8 (.Load .PageTableEntry) .Supervisor) (tm μ t)
      = some (none, tm μ t) →
    execA (within_mmio_readable (.Physaddr pa) 8) (tm μ t) = some (false, tm μ t) →
    devAddr pa = false → wok (paZ pa) 8 → pR wok k →
    (∀ vs : List (BitVec 8), vs.length = 8 → wpin k (paZ pa) vs →
      Q (ws ++ [(k, .WRd (paZ pa) vs)]) ⟨d, b, r⟩ (k + 1) (.Ok (rrv 8 vs)) t) →
    CW (fun _ _ _ _ _ => False) Q ws ⟨d, bsucc b, r⟩ k (read_pte (.Physaddr pa) 8) t := by
  intro hcp hpmp hmm hdev hwok hp hq
  unfold read_pte mem_read_priv mem_read_priv_meta
  ax_walk3_go
  refine AxWalk3.pFact (PCheckedMemReadW img dok wok kind pR pX wpin xpin μ _ _ 8 pa
    (by simp [vmemWidth]) (by intro h; cases h)
    (fun ws' s' k' x t' => ∃ vs : List (BitVec 8), vs.length = 8 ∧ wpin k (paZ pa) vs ∧
      ws' = ws ++ [(k, .WRd (paZ pa) vs)] ∧ s' = ⟨d, b, r⟩ ∧ k' = k + 1 ∧
      x = .Ok (rrv 8 vs, default_meta) ∧ t' = t)
    ws d b r k t hcp hpmp hmm hdev hwok hp
    (fun vs hvs hpin => ⟨vs, hvs, hpin, rfl, rfl, rfl, rfl, rfl⟩)) ?_
  rintro ws' s' k' x t' ⟨vs, hvs, hpin, rfl, rfl, rfl, rfl, rfl⟩
  ax_walk3_go
  exact .pRet _ _ _ _ _ (hq vs hvs hpin)

/-! # 1b. The walker's EXCLUSIVE nodes (Svadu write-back, fused) -/

/-- Rocq `P_read_ram_wx`: the fused read half (no row item, pinned by `xpin`). -/
theorem PReadRamWx (w : Nat)
    (QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop)
    (Q : List (Nat × Wev) → Cst → Nat → (BitVec (8 * w) × Unit) → ExecSt → Prop)
    (pa : BitVec 64) (ws : List (Nat × Wev)) (d : Cdata) (b : Bud) (r : Bool) (k : Nat)
    (t : ExecSt) :
    devAddr pa = false → wok (paZ pa) w → pX wok k →
    (∀ vs : List (BitVec 8), vs.length = w → xpin k (paZ pa) vs →
      Q (ws ++ [(k, .WRmwR (paZ pa) vs)]) ⟨d, b, r⟩ k (rrv w vs, default_meta) t) →
    CW QE Q ws ⟨d, b, r⟩ k (read_ram .Read_RISCV_reserved (.Physaddr pa) w false) t := by
  intro hdev hwok hp hq
  simp only [read_ram, PreSail.sail_mem_read, PreSail.emit]
  exact .pWxrd ws d b r k w 64 _ _ t hdev rfl hwok hp
    (fun vs hvs hpin => .pRet _ _ _ _ _ (hq vs hvs hpin))

/-- Rocq `P_write_ram_wxc`: the fused write half (one row item). -/
theorem PWriteRamWxc (w : Nat)
    (QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop)
    (Q : List (Nat × Wev) → Cst → Nat → Bool → ExecSt → Prop)
    (pa : BitVec 64) (data : BitVec (8 * w)) (rvs : List (BitVec 8)) (ws : List (Nat × Wev))
    (d : Cdata) (b : Bud) (r : Bool) (k : Nat) (t : ExecSt) :
    devAddr pa = false → wok (paZ pa) w →
    (∃ ws0 k0, ws = ws0 ++ [(k0, .WRmwR (paZ pa) rvs)]) →
    Q (ws ++ [(k, .WRmw (paZ pa) rvs (AxDataX.wrb w data))]) ⟨d, b, r⟩ (k + 1) true t →
    CW QE Q ws ⟨d, bsucc b, r⟩ k
      (write_ram .Write_RISCV_conditional (.Physaddr pa) w data ()) t := by
  intro hdev hwok hlast hq
  simp only [write_ram, PreSail.sail_mem_write, PreSail.emit]
  exact .pWxwr ws rvs d b r k w 64 _ _ t data hdev rfl rfl hwok hlast (.pRet _ _ _ _ _ hq)

/-- Rocq `P_checked_mem_read_wx` (deviation 5). -/
theorem PCheckedMemReadWx (μ : ExecSt) (acc : MemoryAccessType mem_payload)
    (pbmt : page_based_mem_type) (w : Nat) (pa : BitVec 64) (hw : vmemWidth w)
    (Q : List (Nat × Wev) → Cst → Nat → Result (BitVec (8 * w) × Unit) (physaddr × ExceptionType) →
      ExecSt → Prop)
    (ws : List (Nat × Wev)) (d : Cdata) (b : Bud) (r : Bool) (k : Nat) (t : ExecSt) :
    execA (check_pma_with_pmp_priority acc pbmt .Supervisor (.Physaddr pa) w true) (tm μ t)
      = some (.Ok pmaOkAligned, tm μ t) →
    execA (pmpCheck (.Physaddr pa) w acc .Supervisor) (tm μ t) = some (none, tm μ t) →
    execA (within_mmio_readable (.Physaddr pa) w) (tm μ t) = some (false, tm μ t) →
    devAddr pa = false → wok (paZ pa) w → pX wok k →
    (∀ vs : List (BitVec 8), vs.length = w → xpin k (paZ pa) vs →
      Q (ws ++ [(k, .WRmwR (paZ pa) vs)]) ⟨d, b, r⟩ k (.Ok (rrv w vs, default_meta)) t) →
    CW (fun _ _ _ _ _ => False) Q ws ⟨d, b, r⟩ k
      (checked_mem_read acc pbmt .Supervisor (.Physaddr pa) w false false true false) t := by
  intro hcp hpmp hmm hdev hwok hp hq
  unfold checked_mem_read
  apply CertWPCatchEarlyReturn
  refine AxWalk3.pRAssoc ?_
  refine AxWalk3.pRUse (μ := μ) (rfFCheckPmaWithPmpPriority _ _ _ _ _ _) hcp ?_
  refine AxWalk3.pRPureBind ?_
  refine AxWalk3.pRUse (μ := μ) (a := ((1 : Int), (w : Int))) (rfFSplitMisaligned _ _ _ _) rfl ?_
  simp only [misaligned_order, sys_misaligned_order_decreasing, ↓reduceIte, Bool.false_eq_true,
    Int.reduceSub, Int.toNat_zero]
  rcases hw with rfl | rfl | rfl | rfl
  all_goals
    cases acc <;> (try (rename_i p; cases p))
  all_goals
    first
      | refine AxWalk3.pRUse (μ := μ) (rfFReadKindOfFlags _ _ _) rfl ?_
      | refine AxWalk3.pRPureBind ?_
    refine AxWalk3.pRAssoc ?_
    refine AxWalk3.pRBind _ _ _ _ _ _ _ _ ?_
    refine CertWPUntilMT1 img dok wok kind pR pX wpin xpin _ _ _ _ _ _ _ _ _ ?_
    refine AxWalk3.pRUse (μ := μ) (by trivial) rfl ?_
    simp only [bits_of_physaddr, Int.cast_ofNat_Int, Int.zero_mul, addIntZero, Int.toNat_one,
      Int.mul_one]
    refine AxWalk3.pRUse (μ := μ) (rfFPmpCheck _ _ _ _) hpmp ?_
    dsimp only
    refine AxWalk3.pRUse (μ := μ) (rfFWithinMmioReadable _ _) hmm ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine AxWalk3.pRAssoc ?_
    refine AxWalk3.pRLift
      (P := fun ws' s' k' x t' => ∃ vs : List (BitVec 8), vs.length = _ ∧ xpin k (paZ pa) vs ∧
        ws' = ws ++ [(k, .WRmwR (paZ pa) vs)] ∧ s' = ⟨d, b, r⟩ ∧ k' = k ∧
        x = (rrv _ vs, default_meta) ∧ t' = t)
      (PReadRamWx img dok wok kind pR pX wpin xpin _ _ _ pa ws d b r k t hdev hwok hp
        (fun vs hvs hpin => ⟨vs, hvs, hpin, rfl, rfl, rfl, rfl, rfl⟩)) ?_
    rintro ws' s' k' x t' ⟨vs, hvs, hpin, rfl, rfl, rfl, rfl, rfl⟩
    refine AxWalk3.pRPureBind ?_
    refine AxWalk3.pRPure ?_
    refine AxWalk3.pRPure ⟨rfl, ?_⟩
    refine AxWalk3.pRPureBind ?_
    refine AxWalk3.pRPure ?_
    refine AxDataX.substArg (fun v => Q _ _ _ v _) ?_ (hq vs hvs hpin)
    simp only [Result.Ok.injEq, Prod.mk.injEq, and_true, Nat.reduceMul, Int.reduceMul,
      Int.reduceAdd, Int.reduceSub, Int.reduceToNat, BitVec.setWidth_eq]
    try simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.updateSubrange]
    try bv_decide

/-- Rocq `P_checked_mem_write_wx` (deviation 5). -/
theorem PCheckedMemWriteWx (μ : ExecSt) (acc : MemoryAccessType mem_payload)
    (pbmt : page_based_mem_type) (w : Nat) (pa : BitVec 64) (hw : vmemWidth w)
    (data : BitVec (8 * w))
    (Q : List (Nat × Wev) → Cst → Nat → Result Bool (physaddr × ExceptionType) → ExecSt → Prop)
    (rvs : List (BitVec 8)) (ws : List (Nat × Wev)) (d : Cdata) (b : Bud) (r : Bool) (k : Nat)
    (t : ExecSt) :
    execA (check_pma_with_pmp_priority acc pbmt .Supervisor (.Physaddr pa) w true) (tm μ t)
      = some (.Ok pmaOkAligned, tm μ t) →
    execA (pmpCheck (.Physaddr pa) w acc .Supervisor) (tm μ t) = some (none, tm μ t) →
    execA (within_mmio_writable (.Physaddr pa) w) (tm μ t) = some (false, tm μ t) →
    devAddr pa = false → wok (paZ pa) w →
    (∃ ws0 k0, ws = ws0 ++ [(k0, .WRmwR (paZ pa) rvs)]) →
    Q (ws ++ [(k, .WRmw (paZ pa) rvs (AxDataX.wrb w data))]) ⟨d, b, r⟩ (k + 1) (.Ok true) t →
    CW (fun _ _ _ _ _ => False) Q ws ⟨d, bsucc b, r⟩ k
      (checked_mem_write (.Physaddr pa) w data acc pbmt .Supervisor () false false true) t := by
  intro hcp hpmp hmm hdev hwok hlast hq
  unfold checked_mem_write
  apply CertWPCatchEarlyReturn
  refine AxWalk3.pRAssoc ?_
  refine AxWalk3.pRUse (μ := μ) (rfFCheckPmaWithPmpPriority _ _ _ _ _ _) hcp ?_
  refine AxWalk3.pRPureBind ?_
  refine AxWalk3.pRUse (μ := μ) (a := ((1 : Int), (w : Int))) (rfFSplitMisaligned _ _ _ _) rfl ?_
  simp only [misaligned_order, sys_misaligned_order_decreasing, ↓reduceIte, Bool.false_eq_true,
    Int.reduceSub, Int.toNat_zero, write_kind_of_flags]
  refine AxWalk3.pRUse (μ := μ) (by trivial) rfl ?_
  refine AxWalk3.pRBind _ _ _ _ _ _ _ _ ?_
  refine CertWPUntilMT1 img dok wok kind pR pX wpin xpin _ _ _ _ _ _ _ _ _ ?_
  refine AxWalk3.pRUse (μ := μ) (by trivial) rfl ?_
  simp only [bits_of_physaddr, Int.cast_ofNat_Int, Int.zero_mul, addIntZero, Int.toNat_natCast]
  refine AxWalk3.pRUse (μ := μ) (rfFPmpCheck _ _ _ _) hpmp ?_
  dsimp only
  refine AxWalk3.pRAssoc ?_
  refine AxWalk3.pRUse (μ := μ) (rfFWithinMmioWritable _ _) hmm ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine AxWalk3.pRAssoc ?_
  refine AxWalk3.pRLift
    (P := fun ws' s' k' x t' => ws' = ws ++ [(k, .WRmw (paZ pa) rvs (AxDataX.wrb w data))] ∧
      s' = ⟨d, b, r⟩ ∧ k' = k + 1 ∧ x = true ∧ t' = t)
    (PWriteRamWxc img dok wok kind pR pX wpin xpin w _ _ pa _ rvs ws d b r k t hdev hwok hlast
      ⟨?_, rfl, rfl, rfl, rfl⟩) ?_
  · refine congrArg (fun z => ws ++ [(k, Wev.WRmw (paZ pa) rvs (AxDataX.wrb w z))]) ?_
    rcases hw with rfl | rfl | rfl | rfl <;>
    · simp only [Sail.BitVec.extractLsb, Int.cast_ofNat_Int, Int.reduceMul, Int.reduceSub,
        Int.reduceToNat, Int.reduceAdd, Nat.reduceMul]
      bv_decide
  rintro ws' s' k' x t' ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine AxWalk3.pRPureBind ?_
  refine AxWalk3.pRPure ?_
  refine AxWalk3.pRPure ⟨rfl, ?_⟩
  refine AxWalk3.pRPure ?_
  exact hq

/-- Rocq `pte_x_ok`: the register-only facts of the walker's write-back at `pa`. -/
def pteXOk (μ t : ExecSt) (pa : BitVec 64) : Prop :=
  execA (check_pma_with_pmp_priority (.Load .PageTableEntry) .PBMT_PMA .Supervisor
      (.Physaddr pa) 8 true) (tm μ t) = some (.Ok pmaOkAligned, tm μ t) ∧
  execA (pmpCheck (.Physaddr pa) 8 (.Load .PageTableEntry) .Supervisor) (tm μ t)
    = some (none, tm μ t) ∧
  execA (within_mmio_readable (.Physaddr pa) 8) (tm μ t) = some (false, tm μ t) ∧
  execA (check_pma_with_pmp_priority (.Store .PageTableEntry) .PBMT_PMA .Supervisor
      (.Physaddr pa) 8 true) (tm μ t) = some (.Ok pmaOkAligned, tm μ t) ∧
  execA (pmpCheck (.Physaddr pa) 8 (.Store .PageTableEntry) .Supervisor) (tm μ t)
    = some (none, tm μ t) ∧
  execA (within_mmio_writable (.Physaddr pa) 8) (tm μ t) = some (false, tm μ t) ∧
  devAddr pa = false ∧ wok (paZ pa) 8

/-- Rocq `P_read_pte_x`: Sail's `read_pte_exclusive`, the FUSED read half, no row item. -/
theorem PReadPteX (μ : ExecSt) (pa : BitVec 64)
    (Q : List (Nat × Wev) → Cst → Nat → Result (BitVec (8 * 8)) (physaddr × ExceptionType) →
      ExecSt → Prop)
    (ws : List (Nat × Wev)) (d : Cdata) (b : Bud) (r : Bool) (k : Nat) (t : ExecSt) :
    pteXOk wok μ t pa → pX wok k →
    (∀ vs : List (BitVec 8), vs.length = 8 → xpin k (paZ pa) vs →
      Q (ws ++ [(k, .WRmwR (paZ pa) vs)]) ⟨d, b, r⟩ k (.Ok (rrv 8 vs)) t) →
    CW (fun _ _ _ _ _ => False) Q ws ⟨d, b, r⟩ k (read_pte_exclusive (.Physaddr pa) 8) t := by
  rintro ⟨hcp, hpmp, hmm, -, -, -, hdev, hwok⟩ hp hq
  unfold read_pte_exclusive mem_read_priv mem_read_priv_meta
  ax_walk3_go
  refine AxWalk3.pFact (PCheckedMemReadWx img dok wok kind pR pX wpin xpin μ _ _ 8 pa
    (by simp [vmemWidth])
    (fun ws' s' k' x t' => ∃ vs : List (BitVec 8), vs.length = 8 ∧ xpin k (paZ pa) vs ∧
      ws' = ws ++ [(k, .WRmwR (paZ pa) vs)] ∧ s' = ⟨d, b, r⟩ ∧ k' = k ∧
      x = .Ok (rrv 8 vs, default_meta) ∧ t' = t)
    ws d b r k t hcp hpmp hmm hdev hwok hp
    (fun vs hvs hpin => ⟨vs, hvs, hpin, rfl, rfl, rfl, rfl, rfl⟩)) ?_
  rintro ws' s' k' x t' ⟨vs, hvs, hpin, rfl, rfl, rfl, rfl, rfl⟩
  ax_walk3_go
  exact .pRet _ _ _ _ _ (hq vs hvs hpin)

/-- Rocq `P_write_pte_cond`: Sail's `write_pte_conditional`, the FUSED write half, one row
item. -/
theorem PWritePteCond (μ : ExecSt) (pa : BitVec 64) (data : BitVec (8 * 8))
    (Q : List (Nat × Wev) → Cst → Nat → Result Bool (physaddr × ExceptionType) → ExecSt → Prop)
    (rvs : List (BitVec 8)) (ws : List (Nat × Wev)) (d : Cdata) (b : Bud) (r : Bool) (k : Nat)
    (t : ExecSt) :
    pteXOk wok μ t pa →
    (∃ ws0 k0, ws = ws0 ++ [(k0, .WRmwR (paZ pa) rvs)]) →
    Q (ws ++ [(k, .WRmw (paZ pa) rvs (AxDataX.wrb 8 data))]) ⟨d, b, r⟩ (k + 1) (.Ok true) t →
    CW (fun _ _ _ _ _ => False) Q ws ⟨d, bsucc b, r⟩ k
      (write_pte_conditional (.Physaddr pa) 8 data) t := by
  rintro ⟨-, -, -, hcp, hpmp, hmm, hdev, hwok⟩ hlast hq
  unfold write_pte_conditional mem_write_value_priv mem_write_value_priv_meta
  ax_walk3_go
  refine AxWalk3.pFact (PCheckedMemWriteWx img dok wok kind pR pX wpin xpin μ _ _ 8 pa
    (by simp [vmemWidth]) data
    (fun ws' s' k' x t' => ws' = ws ++ [(k, .WRmw (paZ pa) rvs (AxDataX.wrb 8 data))] ∧
      s' = ⟨d, b, r⟩ ∧ k' = k + 1 ∧ x = .Ok true ∧ t' = t)
    rvs ws d b r k t hcp hpmp hmm hdev hwok hlast ⟨rfl, rfl, rfl, rfl, rfl⟩) ?_
  rintro ws' s' k' x t' ⟨rfl, rfl, rfl, rfl, rfl⟩
  ax_walk3_go
  exact .pRet _ _ _ _ _ hq

/-- Rocq `pte_rd_ok`: the register-only facts of one PTE read at `pa`. -/
def pteRdOk (μ t : ExecSt) (pa : BitVec 64) : Prop :=
  execA (check_pma_with_pmp_priority (.Load .PageTableEntry) .PBMT_PMA .Supervisor
      (.Physaddr pa) 8 false) (tm μ t) = some (.Ok pmaOkAligned, tm μ t) ∧
  execA (pmpCheck (.Physaddr pa) 8 (.Load .PageTableEntry) .Supervisor) (tm μ t)
    = some (none, tm μ t) ∧
  execA (within_mmio_readable (.Physaddr pa) 8) (tm μ t) = some (false, tm μ t) ∧
  devAddr pa = false ∧ wok (paZ pa) 8

/-! # 2. The walk, demonic and pinned -/

section UserWalkP
variable (μ : ExecSt) (vpn : BitVec 27) (root : BitVec 44) (p2 p1 : BitVec 64)
  (P0 : BitVec 64 → Prop) (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr do_sum : Bool)
-- levels 2 and 1: valid non-leaf PTEs (the PINNED pointer words)
variable (H2i : pteValid p2) (H2nl : ptePtr p2) (H1i : pteValid p1) (H1nl : ptePtr p1)
-- level 0: EVERY member of the leaf class passes the leaf checks
variable (H0i : ∀ q, P0 q → pteValid q) (H0nl : ∀ q, P0 q → pteLeaf q)
  (Hchk0 : ∀ q, P0 q → pteCheckOk acc p mxr do_sum q)
  (H0N : ∀ q, P0 q → (_get_PTE_Ext_N (ext_bits_of_PTE q) == 1#1) = false)

/-- Rocq `waddr2`. -/
def waddr2 : BitVec 64 := uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)
/-- Rocq `waddr1`. -/
def waddr1 : BitVec 64 := uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)
/-- Rocq `waddr0`. -/
def waddr0 : BitVec 64 := uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)

/-- Rocq `ptw_out`: the level-0 walk output at the leaf word `q` (= `uWalkOut`). -/
def ptwOut (q : BitVec 64) (g : Bool) : PTW_Output 39 := uWalkOut (waddr0 vpn p1) q g

/-- Rocq `P_assert_true` (lean-sail's `assert` returns `()`). -/
theorem PAssertTrue {X : Type}
    (QE : List (Nat × Wev) → Cst → Nat → Sail.Error exception → ExecSt → Prop)
    (Q : List (Nat × Wev) → Cst → Nat → X → ExecSt → Prop) (b0 : Bool) (Hb0 : b0 = true)
    (msg : String) (f : Unit → SailM X) (ws : List (Nat × Wev)) (s : Cst) (k : Nat)
    (t : ExecSt) :
    CW QE Q ws s k (f ()) t → CW QE Q ws s k (assert b0 msg >>= f) t := by
  intro H
  subst Hb0
  exact H

include H0i H0nl Hchk0 H0N in
/-- Rocq `P_rec_walk_leaf`: level 0, the leaf. -/
theorem PRecWalkLeaf (g : Bool) (menvcfg0 : BitVec 64)
    (Q : List (Nat × Wev) → Cst → Nat → Result (PTW_Output 39 × Unit) (PTW_Error × Unit) →
      ExecSt → Prop)
    (ws : List (Nat × Wev)) (d : Cdata) (b : Bud) (r : Bool) (k : Nat) (t : ExecSt) :
    t.regs .misa = misaC → t.regs .menvcfg = menvcfg0 →
    (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true →
    pteRdOk wok μ t (waddr0 vpn p1) → pR wok k →
    (∀ vs : List (BitVec 8), vs.length = 8 → wpin k (paZ (waddr0 vpn p1)) vs → P0 (rrv 8 vs)) →
    (∀ vs : List (BitVec 8), vs.length = 8 → P0 (rrv 8 vs) →
      Q (ws ++ [(k, .WRd (paZ (waddr0 vpn p1)) vs)]) ⟨d, b, r⟩ (k + 1)
        (.Ok (ptwOut vpn p1 (rrv 8 vs) (g || uGbit (rrv 8 vs)), ())) t) →
    CW (fun _ _ _ _ _ => False) Q ws ⟨d, bsucc b, r⟩ k
      (pt_walk 39 vpn acc p mxr do_sum (uNextBase p1) 0 g ()) t := by
  rintro hmisa hmenv hpbmte ⟨hcp, hpmp, hmm, hdev, hwok⟩ hp hpin hq
  rw [pt_walk]
  refine PAssertTrue img dok wok kind pR pX wpin xpin _ _ _ rfl _ _ _ _ _ _ ?_
  refine AxWalk3.pFact (PReadPte img dok wok kind pR pX wpin xpin μ (waddr0 vpn p1)
    (fun ws' s' k' x t' => ∃ vs : List (BitVec 8), vs.length = 8 ∧ wpin k (paZ (waddr0 vpn p1)) vs ∧
      ws' = ws ++ [(k, .WRd (paZ (waddr0 vpn p1)) vs)] ∧ s' = ⟨d, b, r⟩ ∧ k' = k + 1 ∧
      x = .Ok (rrv 8 vs) ∧ t' = t)
    ws d b r k t hcp hpmp hmm hdev hwok hp
    (fun vs hvs hpin => ⟨vs, hvs, hpin, rfl, rfl, rfl, rfl, rfl⟩)) ?_
  rintro ws' s' k' x t' ⟨vs, hvs, hpn, rfl, rfl, rfl, rfl, rfl⟩
  have HP0 := hpin vs hvs hpn
  have HQ0 := hq vs hvs HP0
  clear hq hpin hpn
  generalize rrv 8 vs = q at HP0 HQ0 ⊢
  refine AxWalk3.pFactUse (μ := μ) (rfFPteIsInvalid _ _) (h0iA q (H0i q HP0) (tm μ t')) ?_
  rw [if_neg (by simp)]
  refine AxWalk3.pFactUse (μ := μ) (rfFCheckLeafPte _ _ _ _ _ _ _ _ _ _)
    (execACheckLeafPteLeaf0 vpn acc p mxr do_sum q (H0i q HP0) (H0nl q HP0) (Hchk0 q HP0)
      (H0N q HP0) _ menvcfg0 (tm μ t') hmisa hmenv hpbmte) ?_
  exact .pRet _ _ _ _ _ HQ0

/-- Rocq `nl_true` (deviation 3: the shape of `rfFAndInv`): the valid-non-leaf test at a pinned
pointer word. -/
theorem nlTrue (w : BitVec 64) (lv : Nat) (s0 : ExecSt) :
    pteValid w → ptePtr w → (lv >b 0) = true →
    execA (pte_is_invalid (Mk_PTE_Flags (Sail.BitVec.extractLsb w 7 0)) (ext_bits_of_PTE w) >>=
      fun w1 => pure (Functions.not w1 &&
        (pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb w 7 0)) && (lv >b 0)))) s0
      = some (true, s0) := by
  intro hi hnl hlv
  rw [execABindSome _ _ s0 false s0 (h0iA w hi s0)]
  unfold ptePtr at hnl
  simp only [Functions.not, Bool.not_false, Bool.true_and, hnl, hlv]
  rfl

include H1i H1nl H0i H0nl Hchk0 H0N in
/-- Rocq `P_rec_walk_l1`: level 1, a valid non-leaf step into the leaf. -/
theorem PRecWalkL1 (g : Bool) (menvcfg0 : BitVec 64)
    (Q : List (Nat × Wev) → Cst → Nat → Result (PTW_Output 39 × Unit) (PTW_Error × Unit) →
      ExecSt → Prop)
    (ws : List (Nat × Wev)) (d : Cdata) (b : Bud) (r : Bool) (k : Nat) (t : ExecSt) :
    t.regs .misa = misaC → t.regs .menvcfg = menvcfg0 →
    (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true →
    pteRdOk wok μ t (waddr1 vpn p2) → pteRdOk wok μ t (waddr0 vpn p1) → pR wok k → pR wok (k + 1) →
    (∀ vs : List (BitVec 8), vs.length = 8 → wpin k (paZ (waddr1 vpn p2)) vs → rrv 8 vs = p1) →
    (∀ vs : List (BitVec 8), vs.length = 8 → wpin (k + 1) (paZ (waddr0 vpn p1)) vs →
      P0 (rrv 8 vs)) →
    (∀ vs1 vs0 : List (BitVec 8), vs1.length = 8 → vs0.length = 8 → rrv 8 vs1 = p1 →
      P0 (rrv 8 vs0) →
      Q ((ws ++ [(k, .WRd (paZ (waddr1 vpn p2)) vs1)]) ++ [(k + 1, .WRd (paZ (waddr0 vpn p1)) vs0)])
        ⟨d, b, r⟩ (k + 1 + 1)
        (.Ok (ptwOut vpn p1 (rrv 8 vs0) ((g || uGbit p1) || uGbit (rrv 8 vs0)), ())) t) →
    CW (fun _ _ _ _ _ => False) Q ws ⟨d, bsucc (bsucc b), r⟩ k
      (pt_walk 39 vpn acc p mxr do_sum (uNextBase p2) 1 g ()) t := by
  rintro hmisa hmenv hpbmte ⟨hcp, hpmp, hmm, hdev, hwok⟩ hrd0 hp1 hp0 hpin1 hpin0 hq
  rw [pt_walk]
  refine PAssertTrue img dok wok kind pR pX wpin xpin _ _ _ rfl _ _ _ _ _ _ ?_
  refine AxWalk3.pFact (PReadPte img dok wok kind pR pX wpin xpin μ (waddr1 vpn p2)
    (fun ws' s' k' x t' => ∃ vs : List (BitVec 8), vs.length = 8 ∧
      wpin k (paZ (waddr1 vpn p2)) vs ∧
      ws' = ws ++ [(k, .WRd (paZ (waddr1 vpn p2)) vs)] ∧ s' = ⟨d, bsucc b, r⟩ ∧ k' = k + 1 ∧
      x = .Ok (rrv 8 vs) ∧ t' = t)
    ws d (bsucc b) r k t hcp hpmp hmm hdev hwok hp1
    (fun vs hvs hpin => ⟨vs, hvs, hpin, rfl, rfl, rfl, rfl, rfl⟩)) ?_
  rintro ws' s' k' x t' ⟨vs1, hvs1, hpn1, rfl, rfl, rfl, rfl, rfl⟩
  have Heq1 := hpin1 vs1 hvs1 hpn1
  rw [Heq1]
  refine AxWalk3.pFactUse (μ := μ) (rfFPteIsInvalid _ _) (h1iA p1 H1i (tm μ t')) ?_
  rw [if_pos (by simp only [Functions.not, Bool.not_false, Bool.true_and, Bool.and_eq_true]; exact ⟨H1nl, by decide⟩)]
  exact PRecWalkLeaf (img := img) (dok := dok) (wok := wok) (kind := kind) (pR := pR) (pX := pX)
    (wpin := wpin) (xpin := xpin) (μ := μ) (vpn := vpn) (p1 := p1) (P0 := P0) (acc := acc)
    (p := p) (mxr := mxr) (do_sum := do_sum) (H0i := H0i) (H0nl := H0nl) (Hchk0 := Hchk0)
    (H0N := H0N) (g || uGbit p1) menvcfg0 Q _ d b r (k + 1) t' hmisa hmenv hpbmte hrd0 hp0 hpin0
    (fun vs0 hvs0 HP0 => hq vs1 vs0 hvs1 hvs0 Heq1 HP0)

include H2i H2nl H1i H1nl H0i H0nl Hchk0 H0N in
/-- Rocq `P_pt_walk`: level 2, the full walk. -/
theorem PPtWalk (menvcfg0 : BitVec 64)
    (Q : List (Nat × Wev) → Cst → Nat → Result (PTW_Output 39 × Unit) (PTW_Error × Unit) →
      ExecSt → Prop)
    (ws : List (Nat × Wev)) (d : Cdata) (b : Bud) (r : Bool) (k : Nat) (t : ExecSt) :
    t.regs .misa = misaC → t.regs .menvcfg = menvcfg0 →
    (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true →
    pteRdOk wok μ t (waddr2 vpn root) → pteRdOk wok μ t (waddr1 vpn p2) →
    pteRdOk wok μ t (waddr0 vpn p1) →
    pR wok k → pR wok (k + 1) → pR wok (k + 1 + 1) →
    (∀ vs : List (BitVec 8), vs.length = 8 → wpin k (paZ (waddr2 vpn root)) vs → rrv 8 vs = p2) →
    (∀ vs : List (BitVec 8), vs.length = 8 → wpin (k + 1) (paZ (waddr1 vpn p2)) vs →
      rrv 8 vs = p1) →
    (∀ vs : List (BitVec 8), vs.length = 8 → wpin (k + 1 + 1) (paZ (waddr0 vpn p1)) vs →
      P0 (rrv 8 vs)) →
    (∀ vs2 vs1 vs0 : List (BitVec 8), vs2.length = 8 → vs1.length = 8 → vs0.length = 8 →
      rrv 8 vs2 = p2 → rrv 8 vs1 = p1 → P0 (rrv 8 vs0) →
      Q (((ws ++ [(k, .WRd (paZ (waddr2 vpn root)) vs2)]) ++
          [(k + 1, .WRd (paZ (waddr1 vpn p2)) vs1)]) ++
          [(k + 1 + 1, .WRd (paZ (waddr0 vpn p1)) vs0)]) ⟨d, b, r⟩ (k + 1 + 1 + 1)
        (.Ok (ptwOut vpn p1 (rrv 8 vs0) (uGlobal p2 p1 (rrv 8 vs0)), ())) t) →
    CW (fun _ _ _ _ _ => False) Q ws ⟨d, bsucc (bsucc (bsucc b)), r⟩ k
      (pt_walk 39 vpn acc p mxr do_sum root 2 false ()) t := by
  rintro hmisa hmenv hpbmte ⟨hcp, hpmp, hmm, hdev, hwok⟩ hrd1 hrd0 hp2 hp1 hp0 hpin2 hpin1 hpin0
    hq
  rw [pt_walk]
  refine PAssertTrue img dok wok kind pR pX wpin xpin _ _ _ rfl _ _ _ _ _ _ ?_
  refine AxWalk3.pFact (PReadPte img dok wok kind pR pX wpin xpin μ (waddr2 vpn root)
    (fun ws' s' k' x t' => ∃ vs : List (BitVec 8), vs.length = 8 ∧
      wpin k (paZ (waddr2 vpn root)) vs ∧
      ws' = ws ++ [(k, .WRd (paZ (waddr2 vpn root)) vs)] ∧ s' = ⟨d, bsucc (bsucc b), r⟩ ∧
      k' = k + 1 ∧ x = .Ok (rrv 8 vs) ∧ t' = t)
    ws d (bsucc (bsucc b)) r k t hcp hpmp hmm hdev hwok hp2
    (fun vs hvs hpin => ⟨vs, hvs, hpin, rfl, rfl, rfl, rfl, rfl⟩)) ?_
  rintro ws' s' k' x t' ⟨vs2, hvs2, hpn2, rfl, rfl, rfl, rfl, rfl⟩
  have Heq2 := hpin2 vs2 hvs2 hpn2
  rw [Heq2]
  refine AxWalk3.pFactUse (μ := μ) (rfFPteIsInvalid _ _) (h2iA p2 H2i (tm μ t')) ?_
  rw [if_pos (by simp only [Functions.not, Bool.not_false, Bool.true_and, Bool.and_eq_true]; exact ⟨H2nl, by decide⟩)]
  exact PRecWalkL1 (img := img) (dok := dok) (wok := wok) (kind := kind) (pR := pR) (pX := pX)
    (wpin := wpin) (xpin := xpin) (μ := μ) (vpn := vpn) (p2 := p2) (p1 := p1) (P0 := P0)
    (acc := acc) (p := p) (mxr := mxr) (do_sum := do_sum) (H1i := H1i) (H1nl := H1nl)
    (H0i := H0i) (H0nl := H0nl) (Hchk0 := Hchk0) (H0N := H0N) (false || uGbit p2) menvcfg0 Q _ d
    b r (k + 1) t' hmisa hmenv hpbmte hrd1 hrd0 hp1 hp0 hpin1 hpin0
    (fun vs1 vs0 hvs1 hvs0 Heq1 HP0 => hq vs2 vs1 vs0 hvs2 hvs1 hvs0 Heq2 Heq1 HP0)

/-- Rocq `tlb_fill` (duplicated name, file-qualified): the post TLB of a fill with the READ
leaf word. -/
def AxWalk3.tlbFill (t : ExecSt) (asid : BitVec 16) (q0 : BitVec 64) : ExecSt :=
  t.setReg .tlb (vectorUpdate (t.regs .tlb) (tlb_hash 39 vpn)
    (some (uWalkEntry vpn p2 p1 q0 asid)))

include H2i H2nl H1i H1nl H0i H0nl Hchk0 H0N in
/-- THE MISS, A/D-preset branch (Rocq `P_translate_TLB_miss_noupd`): three demonic pinned
walker reads, no write-back, the TLB filled with the READ leaf. -/
theorem PTranslateTLBMissNoupd (asid : BitVec 16) (menvcfg0 : BitVec 64)
    (Q : List (Nat × Wev) → Cst → Nat →
      Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) → ExecSt → Prop)
    (ws : List (Nat × Wev)) (d : Cdata) (b : Bud) (r : Bool) (k : Nat) (t : ExecSt) :
    t.regs .misa = misaC → t.regs .menvcfg = menvcfg0 →
    (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true →
    pteRdOk wok μ t (waddr2 vpn root) → pteRdOk wok μ t (waddr1 vpn p2) →
    pteRdOk wok μ t (waddr0 vpn p1) →
    pR wok k → pR wok (k + 1) → pR wok (k + 1 + 1) →
    (∀ vs : List (BitVec 8), vs.length = 8 → wpin k (paZ (waddr2 vpn root)) vs → rrv 8 vs = p2) →
    (∀ vs : List (BitVec 8), vs.length = 8 → wpin (k + 1) (paZ (waddr1 vpn p2)) vs →
      rrv 8 vs = p1) →
    (∀ vs : List (BitVec 8), vs.length = 8 → wpin (k + 1 + 1) (paZ (waddr0 vpn p1)) vs →
      P0 (rrv 8 vs)) →
    (∀ q, P0 q → update_PTE_Bits q acc = none) →
    (∀ vs2 vs1 vs0 : List (BitVec 8), vs2.length = 8 → vs1.length = 8 → vs0.length = 8 →
      rrv 8 vs2 = p2 → rrv 8 vs1 = p1 → P0 (rrv 8 vs0) →
      Q (((ws ++ [(k, .WRd (paZ (waddr2 vpn root)) vs2)]) ++
          [(k + 1, .WRd (paZ (waddr1 vpn p2)) vs1)]) ++
          [(k + 1 + 1, .WRd (paZ (waddr0 vpn p1)) vs0)]) ⟨d, b, r⟩ (k + 1 + 1 + 1)
        (.Ok (ppn0 (rrv 8 vs0), .PBMT_PMA, ())) (AxWalk3.tlbFill vpn p2 p1 t asid (rrv 8 vs0))) →
    CW (fun _ _ _ _ _ => False) Q ws ⟨d, bsucc (bsucc (bsucc b)), r⟩ k
      (translate_TLB_miss 39 asid root vpn acc p mxr do_sum ()) t := by
  intro hmisa hmenv hpbmte R2 R1 R0 hp2 hp1 hp0 hpin2 hpin1 hpin0 hnoupd hq
  unfold translate_TLB_miss
  refine AxWalk3.pFact (PPtWalk (img := img) (dok := dok) (wok := wok) (kind := kind) (pR := pR)
    (pX := pX) (wpin := wpin) (xpin := xpin) (μ := μ) (vpn := vpn) (root := root) (p2 := p2)
    (p1 := p1) (P0 := P0) (acc := acc) (p := p) (mxr := mxr) (do_sum := do_sum) (H2i := H2i)
    (H2nl := H2nl) (H1i := H1i) (H1nl := H1nl) (H0i := H0i) (H0nl := H0nl) (Hchk0 := Hchk0)
    (H0N := H0N) menvcfg0
    (fun ws' s' k' x t' => ∃ vs2 vs1 vs0 : List (BitVec 8), vs2.length = 8 ∧ vs1.length = 8 ∧
      vs0.length = 8 ∧ rrv 8 vs2 = p2 ∧ rrv 8 vs1 = p1 ∧ P0 (rrv 8 vs0) ∧
      ws' = ((ws ++ [(k, .WRd (paZ (waddr2 vpn root)) vs2)]) ++
          [(k + 1, .WRd (paZ (waddr1 vpn p2)) vs1)]) ++
          [(k + 1 + 1, .WRd (paZ (waddr0 vpn p1)) vs0)] ∧ s' = ⟨d, b, r⟩ ∧ k' = k + 1 + 1 + 1 ∧
      x = .Ok (ptwOut vpn p1 (rrv 8 vs0) (uGlobal p2 p1 (rrv 8 vs0)), ()) ∧ t' = t)
    ws d b r k t hmisa hmenv hpbmte R2 R1 R0 hp2 hp1 hp0 hpin2 hpin1 hpin0
    (fun vs2 vs1 vs0 h2 h1 h0 e2 e1 HP0 =>
      ⟨vs2, vs1, vs0, h2, h1, h0, e2, e1, HP0, rfl, rfl, rfl, rfl, rfl⟩)) ?_
  rintro ws' s' k' x t' ⟨vs2, vs1, vs0, h2, h1, h0, e2, e1, HP0, rfl, rfl, rfl, rfl, rfl⟩
  have HQ0 := hq vs2 vs1 vs0 h2 h1 h0 e2 e1 HP0
  clear hq
  generalize rrv 8 vs0 = q0 at HP0 HQ0 ⊢
  dsimp only [ptwOut, uWalkOut]
  have hu : update_and_write_pte 39 vpn (.Physaddr (waddr0 vpn p1)) q0 0 acc p mxr do_sum ()
      = pure (.Ok (none, ())) := by
    unfold update_and_write_pte
    erw [hnoupd q0 HP0]
  rw [hu]
  refine AxWalk3.pFactPure ?_
  refine CertWPBind0 img dok wok kind pR pX wpin xpin _ _ _ _ _ _ _ _ ?_
  refine CertWPExecARfFPost img dok wok kind pR pX wpin xpin _ _ _ t' () _ t' _ _ _
    (rfFAddToTLB _ _ _ _ _ _ _ _) (execAAddToTLBUser vpn p2 p1 q0 asid t') rfl ?_
  exact .pRet _ _ _ _ _ HQ0

include H0i H0nl Hchk0 H0N in
/-- THE SVADU WRITE-BACK at the leaf slot (Rocq `P_update_and_write_pte_upd`): Sail's exclusive
RE-READ (fused read half, pinned by `xpin`: the re-read word is in the leaf class and still
needs the update) and its conditional write (the fused write half, one row item), both at the
leaf's row position. -/
theorem PUpdateAndWritePteUpd (menvcfg0 : BitVec 64) (q0 u0 : BitVec 64)
    (Q : List (Nat × Wev) → Cst → Nat → Result (Option (BitVec 64) × Unit) (PTW_Error × Unit) →
      ExecSt → Prop)
    (ws : List (Nat × Wev)) (d : Cdata) (b : Bud) (r : Bool) (k : Nat) (t : ExecSt) :
    t.regs .misa = misaC → t.regs .menvcfg = menvcfg0 →
    (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true →
    (_get_MEnvcfg_ADUE menvcfg0 == 1#1) = true →
    update_PTE_Bits q0 acc = some u0 →
    pteXOk wok μ t (waddr0 vpn p1) → pX wok k →
    (∀ vs : List (BitVec 8), vs.length = 8 → xpin k (paZ (waddr0 vpn p1)) vs →
      P0 (rrv 8 vs) ∧ ∃ w' : BitVec (8 * 8), update_PTE_Bits (rrv 8 vs) acc = some w') →
    (∀ (vs : List (BitVec 8)) (w' : BitVec (8 * 8)), vs.length = 8 → P0 (rrv 8 vs) →
      update_PTE_Bits (rrv 8 vs) acc = some w' →
      Q ((ws ++ [(k, .WRmwR (paZ (waddr0 vpn p1)) vs)]) ++
          [(k, .WRmw (paZ (waddr0 vpn p1)) vs (AxDataX.wrb 8 w'))])
        ⟨d, b, r⟩ (k + 1) (.Ok (some w', ())) t) →
    CW (fun _ _ _ _ _ => False) Q ws ⟨d, bsucc b, r⟩ k
      (update_and_write_pte 39 vpn (.Physaddr (waddr0 vpn p1)) q0 0 acc p mxr do_sum ()) t := by
  intro hmisa hmenv hpbmte hadue hupd0 hx hpx hxpin hq
  unfold update_and_write_pte
  erw [hupd0]
  dsimp only
  refine AxWalk3.pFactUse (μ := μ) rfFCurrentlyEnabledSvadu (execACurrentlyEnabledSvadu (tm μ t))
    ?_
  rw [if_pos rfl]
  refine AxWalk3.pFactRead ?_ ?_
  · exact AxSymEngine2.notPin _ (by decide) (by decide)
  rw [hmenv]
  refine AxWalk3.pFactPure ?_
  rw [if_pos hadue]
  refine AxWalk3.pFactPure ?_
  rw [if_pos rfl]
  refine AxWalk3.pFact (PReadPteX img dok wok kind pR pX wpin xpin μ (waddr0 vpn p1)
    (fun ws' s' k' x t' => ∃ vs : List (BitVec 8), vs.length = 8 ∧
      xpin k (paZ (waddr0 vpn p1)) vs ∧
      ws' = ws ++ [(k, .WRmwR (paZ (waddr0 vpn p1)) vs)] ∧ s' = ⟨d, bsucc b, r⟩ ∧ k' = k ∧
      x = .Ok (rrv 8 vs) ∧ t' = t)
    ws d (bsucc b) r k t hx hpx
    (fun vs hvs hpin => ⟨vs, hvs, hpin, rfl, rfl, rfl, rfl, rfl⟩)) ?_
  rintro ws' s' k' x t' ⟨vs, hvs, hxp, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨HP', w', hw'⟩ := hxpin vs hvs hxp
  have HQ0 := hq vs w' hvs HP' hw'
  dsimp only
  refine AxWalk3.pFactUse (μ := μ) (rfFCheckLeafPte _ _ _ _ _ _ _ _ _ _)
    (execACheckLeafPteLeaf0 vpn acc p mxr do_sum (rrv 8 vs) (H0i _ HP') (H0nl _ HP') (Hchk0 _ HP')
      (H0N _ HP') _ menvcfg0 (tm μ t') hmisa hmenv hpbmte) ?_
  dsimp only
  erw [hw']
  dsimp only
  refine AxWalk3.pFact (PWritePteCond img dok wok kind pR pX wpin xpin μ (waddr0 vpn p1) w'
    (fun ws'' s'' k'' x t'' => ws'' = (ws ++ [(k', .WRmwR (paZ (waddr0 vpn p1)) vs)]) ++
        [(k', .WRmw (paZ (waddr0 vpn p1)) vs (AxDataX.wrb 8 w'))] ∧ s'' = ⟨d, b, r⟩ ∧
      k'' = k' + 1 ∧ x = .Ok true ∧ t'' = t')
    vs _ d b r k' t' hx ⟨ws, k', rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩) ?_
  rintro ws'' s'' k'' x t'' ⟨rfl, rfl, rfl, rfl, rfl⟩
  exact .pRet _ _ _ _ _ HQ0

/-- Rocq `execA_add_to_TLB_gen`: a level-0 fill installs SOME entry with the given PTE and slot
address. -/
theorem execAAddToTLBGen (asid : BitVec 16) (ppn : BitVec 44) (pte : BitVec 64) (pa : physaddr)
    (g : Bool) (s : ExecSt) :
    ∃ ent : TLB_Entry,
      execA (add_to_TLB 39 asid vpn ppn pte pa 0 g) s =
        some ((), s.setReg .tlb (vectorUpdate (s.regs .tlb) (tlb_hash 39 vpn) (some ent))) ∧
      ent.pte = zero_extend (m := 64) pte ∧ ent.pteAddr = pa :=
  ⟨ptFillEnt asid vpn ppn pte pa g,
    execAOfRfF _ (rfFAddToTLB _ _ _ _ _ _ _ _) s _ (execAddToTLBPt asid vpn ppn pte pa g s), rfl, rfl⟩

include H2i H2nl H1i H1nl H0i H0nl Hchk0 H0N in
/-- THE MISS, BOTH BRANCHES (Rocq `P_translate_TLB_miss`): three demonic pinned walker reads;
then the READ leaf `q0` (demonic in the class) decides — A/D already set: no write-back, TLB
filled with `q0`; A/D needed: the fused Svadu RMW at the next row position (re-read pinned by
`xpin`, write-back of `update_PTE_Bits q'` one row item), TLB filled with the WRITTEN word. -/
theorem PTranslateTLBMiss (asid : BitVec 16) (menvcfg0 : BitVec 64)
    (Q : List (Nat × Wev) → Cst → Nat →
      Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) → ExecSt → Prop)
    (ws : List (Nat × Wev)) (d : Cdata) (b : Bud) (r : Bool) (k : Nat) (t : ExecSt) :
    t.regs .misa = misaC → t.regs .menvcfg = menvcfg0 →
    (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true →
    (_get_MEnvcfg_ADUE menvcfg0 == 1#1) = true →
    pteRdOk wok μ t (waddr2 vpn root) → pteRdOk wok μ t (waddr1 vpn p2) →
    pteRdOk wok μ t (waddr0 vpn p1) → pteXOk wok μ t (waddr0 vpn p1) →
    pR wok k → pR wok (k + 1) → pR wok (k + 1 + 1) → pX wok (k + 1 + 1 + 1) →
    (∀ n, b = .BFin n → 0 < n) →
    (∀ vs : List (BitVec 8), vs.length = 8 → wpin k (paZ (waddr2 vpn root)) vs → rrv 8 vs = p2) →
    (∀ vs : List (BitVec 8), vs.length = 8 → wpin (k + 1) (paZ (waddr1 vpn p2)) vs →
      rrv 8 vs = p1) →
    (∀ vs : List (BitVec 8), vs.length = 8 → wpin (k + 1 + 1) (paZ (waddr0 vpn p1)) vs →
      P0 (rrv 8 vs)) →
    (∀ vs : List (BitVec 8), vs.length = 8 → xpin (k + 1 + 1 + 1) (paZ (waddr0 vpn p1)) vs →
      P0 (rrv 8 vs) ∧ ∃ w' : BitVec (8 * 8), update_PTE_Bits (rrv 8 vs) acc = some w') →
    -- no write-back
    (∀ vs2 vs1 vs0 : List (BitVec 8), vs2.length = 8 → vs1.length = 8 → vs0.length = 8 →
      rrv 8 vs2 = p2 → rrv 8 vs1 = p1 → P0 (rrv 8 vs0) →
      update_PTE_Bits (rrv 8 vs0) acc = none →
      Q (((ws ++ [(k, .WRd (paZ (waddr2 vpn root)) vs2)]) ++
          [(k + 1, .WRd (paZ (waddr1 vpn p2)) vs1)]) ++
          [(k + 1 + 1, .WRd (paZ (waddr0 vpn p1)) vs0)]) ⟨d, b, r⟩ (k + 1 + 1 + 1)
        (.Ok (ppn0 (rrv 8 vs0), .PBMT_PMA, ())) (AxWalk3.tlbFill vpn p2 p1 t asid (rrv 8 vs0))) →
    -- the fused Svadu write-back
    (∀ (vs2 vs1 vs0 : List (BitVec 8)) (u0 : BitVec (8 * 8)) (vs : List (BitVec 8))
      (w' : BitVec (8 * 8)) (b' : Bud), b = bsucc b' →
      vs2.length = 8 → vs1.length = 8 → vs0.length = 8 → vs.length = 8 →
      rrv 8 vs2 = p2 → rrv 8 vs1 = p1 → P0 (rrv 8 vs0) →
      update_PTE_Bits (rrv 8 vs0) acc = some u0 →
      P0 (rrv 8 vs) → update_PTE_Bits (rrv 8 vs) acc = some w' →
      ∀ ent : TLB_Entry, ent.pte = zero_extend (m := 64) w' →
      ent.pteAddr = .Physaddr (waddr0 vpn p1) →
      Q (((((ws ++ [(k, .WRd (paZ (waddr2 vpn root)) vs2)]) ++
          [(k + 1, .WRd (paZ (waddr1 vpn p2)) vs1)]) ++
          [(k + 1 + 1, .WRd (paZ (waddr0 vpn p1)) vs0)]) ++
          [(k + 1 + 1 + 1, .WRmwR (paZ (waddr0 vpn p1)) vs)]) ++
          [(k + 1 + 1 + 1, .WRmw (paZ (waddr0 vpn p1)) vs (AxDataX.wrb 8 w'))])
        ⟨d, b', r⟩ (k + 1 + 1 + 1 + 1)
        (.Ok (ppn0 (rrv 8 vs0), .PBMT_PMA, ()))
        (t.setReg .tlb (vectorUpdate (t.regs .tlb) (tlb_hash 39 vpn) (some ent)))) →
    CW (fun _ _ _ _ _ => False) Q ws ⟨d, bsucc (bsucc (bsucc b)), r⟩ k
      (translate_TLB_miss 39 asid root vpn acc p mxr do_sum ()) t := by
  intro hmisa hmenv hpbmte hadue R2 R1 R0 RX hp2 hp1 hp0 hpX hroom hpin2 hpin1 hpin0 hxpin HQn
    HQu
  unfold translate_TLB_miss
  refine AxWalk3.pFact (PPtWalk (img := img) (dok := dok) (wok := wok) (kind := kind) (pR := pR)
    (pX := pX) (wpin := wpin) (xpin := xpin) (μ := μ) (vpn := vpn) (root := root) (p2 := p2)
    (p1 := p1) (P0 := P0) (acc := acc) (p := p) (mxr := mxr) (do_sum := do_sum) (H2i := H2i)
    (H2nl := H2nl) (H1i := H1i) (H1nl := H1nl) (H0i := H0i) (H0nl := H0nl) (Hchk0 := Hchk0)
    (H0N := H0N) menvcfg0
    (fun ws' s' k' x t' => ∃ vs2 vs1 vs0 : List (BitVec 8), vs2.length = 8 ∧ vs1.length = 8 ∧
      vs0.length = 8 ∧ rrv 8 vs2 = p2 ∧ rrv 8 vs1 = p1 ∧ P0 (rrv 8 vs0) ∧
      ws' = ((ws ++ [(k, .WRd (paZ (waddr2 vpn root)) vs2)]) ++
          [(k + 1, .WRd (paZ (waddr1 vpn p2)) vs1)]) ++
          [(k + 1 + 1, .WRd (paZ (waddr0 vpn p1)) vs0)] ∧ s' = ⟨d, b, r⟩ ∧ k' = k + 1 + 1 + 1 ∧
      x = .Ok (ptwOut vpn p1 (rrv 8 vs0) (uGlobal p2 p1 (rrv 8 vs0)), ()) ∧ t' = t)
    ws d b r k t hmisa hmenv hpbmte R2 R1 R0 hp2 hp1 hp0 hpin2 hpin1 hpin0
    (fun vs2 vs1 vs0 h2 h1 h0 e2 e1 HP0 =>
      ⟨vs2, vs1, vs0, h2, h1, h0, e2, e1, HP0, rfl, rfl, rfl, rfl, rfl⟩)) ?_
  rintro ws' s' k' x t' ⟨vs2, vs1, vs0, h2, h1, h0, e2, e1, HP0, rfl, rfl, rfl, rfl, rfl⟩
  have HQn0 := HQn vs2 vs1 vs0 h2 h1 h0 e2 e1 HP0
  have HQu0 := HQu vs2 vs1 vs0
  clear HQn HQu
  generalize rrv 8 vs0 = q0 at HP0 HQn0 HQu0 ⊢
  dsimp only [ptwOut, uWalkOut]
  cases hu : update_PTE_Bits q0 acc with
  | none =>
    have hw : update_and_write_pte 39 vpn (.Physaddr (waddr0 vpn p1)) q0 0 acc p mxr do_sum ()
        = pure (.Ok (none, ())) := by
      unfold update_and_write_pte
      erw [hu]
    rw [hw]
    refine AxWalk3.pFactPure ?_
    refine CertWPBind0 img dok wok kind pR pX wpin xpin _ _ _ _ _ _ _ _ ?_
    refine CertWPExecARfFPost img dok wok kind pR pX wpin xpin _ _ _ t' () _ t' _ _ _
      (rfFAddToTLB _ _ _ _ _ _ _ _) (execAAddToTLBUser vpn p2 p1 q0 asid t') rfl ?_
    exact .pRet _ _ _ _ _ (HQn0 hu)
  | some u0 =>
    obtain ⟨b', rfl⟩ : ∃ b', b = bsucc b' := by
      cases b with
      | BInf => exact ⟨.BInf, rfl⟩
      | BFin n =>
        cases n with
        | zero => exact absurd (hroom 0 rfl) (Nat.lt_irrefl 0)
        | succ n' => exact ⟨.BFin n', rfl⟩
    refine AxWalk3.pFact (PUpdateAndWritePteUpd (img := img) (dok := dok) (wok := wok)
      (kind := kind) (pR := pR) (pX := pX) (wpin := wpin) (xpin := xpin) (μ := μ) (vpn := vpn)
      (p1 := p1) (P0 := P0) (acc := acc) (p := p) (mxr := mxr) (do_sum := do_sum) (H0i := H0i)
      (H0nl := H0nl) (Hchk0 := Hchk0) (H0N := H0N) menvcfg0 q0 u0
      (fun ws'' s'' k'' x t'' => ∃ (vs : List (BitVec 8)) (w' : BitVec (8 * 8)), vs.length = 8 ∧
        P0 (rrv 8 vs) ∧ update_PTE_Bits (rrv 8 vs) acc = some w' ∧
        ws'' = ((((ws ++ [(k, .WRd (paZ (waddr2 vpn root)) vs2)]) ++
          [(k + 1, .WRd (paZ (waddr1 vpn p2)) vs1)]) ++
          [(k + 1 + 1, .WRd (paZ (waddr0 vpn p1)) vs0)]) ++
          [(k + 1 + 1 + 1, .WRmwR (paZ (waddr0 vpn p1)) vs)]) ++
          [(k + 1 + 1 + 1, .WRmw (paZ (waddr0 vpn p1)) vs (AxDataX.wrb 8 w'))] ∧
        s'' = ⟨d, b', r⟩ ∧ k'' = k + 1 + 1 + 1 + 1 ∧ x = .Ok (some w', ()) ∧ t'' = t')
      _ d b' r (k + 1 + 1 + 1) t' hmisa hmenv hpbmte hadue hu RX hpX hxpin
      (fun vs w' hvs HP' hw' => ⟨vs, w', hvs, HP', hw', rfl, rfl, rfl, rfl, rfl⟩)) ?_
    rintro ws'' s'' k'' x t'' ⟨vs, w', hvs, HP', hw', rfl, rfl, rfl, rfl, rfl⟩
    dsimp only
    obtain ⟨ent, He, Hpte, Hpa⟩ := execAAddToTLBGen vpn asid (ppn0 q0) w'
      (.Physaddr (waddr0 vpn p1)) (uGlobal p2 p1 q0) t''
    refine CertWPBind0 img dok wok kind pR pX wpin xpin _ _ _ _ _ _ _ _ ?_
    refine CertWPExecARfFPost img dok wok kind pR pX wpin xpin _ _ _ t'' () _ t'' _ _ _
      (rfFAddToTLB _ _ _ _ _ _ _ _) He rfl ?_
    exact .pRet _ _ _ _ _
      (HQu0 u0 vs w' b' rfl h2 h1 h0 hvs e2 e1 HP0 hu HP' hw' ent Hpte Hpa)

/-- Rocq `tlb_agrees_after_walk`: `tlbOkPt` (AxPtProt) is preserved by the fill with the READ
leaf whenever the leaf is pinned in the class `pteSetAD p0` — the replacement of
`AxSpineOk4.tlbExact`. -/
theorem tlbAgreesAfterWalk (T : PTree) (asid : BitVec 16) (p0 q0 : BitVec 64) (t : ExecSt) :
    AxPtProt.ptreeMaps T vpn p2 p1 p0 → (∃ a d : BitVec 1, q0 = pteSetAD p0 a d) →
    AxPtProt.tlbOkPt asid T (t.regs .tlb) →
    AxPtProt.tlbOkPt asid T ((AxWalk3.tlbFill vpn p2 p1 t asid q0).regs .tlb) := by
  intro hm hv hok
  simp only [AxWalk3.tlbFill, ExecSt.setReg_regs, RegFile.set_same]
  exact AxPtProt.tlbOkPtFill asid T _ vpn p2 p1 p0 q0 hm hv hok

end UserWalkP

end walk

end Weak
