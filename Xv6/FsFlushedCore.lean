/-
**THE DURABILITY RECEIPT `flushed b D`, AT AN ALTITUDE THE WAL CAN SEE** -- a
port of Rocq `FsFlushedCore.v` (`/shared/xv6rocq/iris/FsFlushedCore.v`).
Crash batch C-1, agent CG.

WHAT THE RECEIPT IS (Rocq's header).  A PERSISTENT, MONOTONE, STATE-SHAPED
receipt -- "batches `≤ b` are on disk" -- whose VALUE is a copy of the
committed map.  It adds NO ghost state: the value is `fsReceipt`'s committed
map `D` (the history mono-list's lower bound the commit already mints), and the
BOUND `b` is that lower bound's own prefix LENGTH, so index `b` IS the `b`-th
commit.  `fsBank` (`Xv6/FsCrashSeam.lean`) is the COPY a WAL write leaves for a
reader that writes no block (sys_sync); `flushed_ofBank` names its index, and
from there it is `LogInv`'s `log_flushed_bank` (batch C-2b).

## DEVIATIONS from Rocq

1. Rocq's two sections bind `lockG` / `CurCtx` / the durable snapshot's
   classes because they copy `FsCrash`'s binder lists verbatim; the Lean
   sections bind only what the statements use (`MonoListG GF BlockMap` for the
   history, `MachFixedGS` for the seam equations).

## NOT PORTED (crash brief D36; uses checked over `/shared/xv6rocq/iris/*.v`)

* `flushed_at_agree`, `flushed_at_earlier`, `P_fs_flushed_lookup`,
  `P_fs_flushed_now`, `P_fs_flushed_holds`, `flushed_earlier` -- no code use
  outside this file (SpecSysSync.v / LogInv.v name `flushed_earlier` and
  `P_fs_flushed_now` in comments only).
* Transitively: `fs_hist_lb_prefix` (only `flushed_at_earlier`) and
  `fs_hist_lb_compare` (only `flushed_at_agree`).
-/
import Xv6.FsCrashSeam

namespace Xv6

open Iris Iris.BI Iris.ProofMode Std MachCSL

set_option linter.unusedSectionVars false

/-! ## 1. The receipt, at the crash record's own gnames -/

section
variable {GF : BundledGFunctors} [MonoListG GF BlockMap]

/-- "`D` is the `b`-th committed state" (Rocq `flushed_at`). -/
def flushedAt (γs : FsCrashNames) (b : Nat) (D : BlockMap) : IProp GF :=
  iprop(∃ l : List BlockMap, ⌜l.length = b⌝ ∗ fsHistLb γs.hist (l ++ [D]))

instance flushedAt_persistent (γs : FsCrashNames) (b : Nat) (D : BlockMap) :
    Persistent (flushedAt (GF := GF) γs b D) := by
  unfold flushedAt; infer_instance

/-- Rocq `flushed_at_receipt`. -/
theorem flushedAt_receipt (γs : FsCrashNames) (b : Nat) (D : BlockMap) :
    flushedAt (GF := GF) γs b D ⊢ fsReceipt γs D := by
  unfold flushedAt fsReceipt
  iintro ⟨%l, -, Hlb⟩
  iexists l
  iexact Hlb

/-- Rocq `flushed_at_of_receipt`: the index is exactly what `fsReceipt`
existentially closes. -/
theorem flushedAt_ofReceipt (γs : FsCrashNames) (D : BlockMap) :
    fsReceipt (GF := GF) γs D ⊢ ∃ b : Nat, flushedAt γs b D := by
  unfold flushedAt fsReceipt
  iintro ⟨%l, Hlb⟩
  iexists l.length, l
  iframe Hlb
  ipureintro; rfl

end

/-! ## 2. The client-facing receipt -/

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachFixedGS hlc GF] [MonoListG GF BlockMap]

/-- `fsReceiptAny` with the batch NUMBER exposed (Rocq `flushed`). -/
def flushed (b : Nat) (D : BlockMap) : IProp GF :=
  iprop(∃ γs : FsCrashNames,
    ⌜γs.swap = MachFixedGS.swapName (hlc := hlc) (GF := GF) ∧
      γs.reg = MachFixedGS.registryName (hlc := hlc) (GF := GF) ∧
      γs.start = MachFixedGS.startName (hlc := hlc) (GF := GF)⌝ ∗ flushedAt γs b D)

instance flushed_persistent (b : Nat) (D : BlockMap) :
    Persistent (flushed (hlc := hlc) (GF := GF) b D) := by
  unfold flushed; infer_instance

/-- Rocq `flushed_receipt_any`. -/
theorem flushed_receiptAny (b : Nat) (D : BlockMap) :
    flushed (hlc := hlc) (GF := GF) b D ⊢ fsReceiptAny (hlc := hlc) D := by
  unfold flushed fsReceiptAny
  iintro ⟨%γs, %hseam, Hf⟩
  iexists γs
  isplitr
  · ipureintro; exact hseam
  iapply flushedAt_receipt γs b D $$ Hf

/-- THE BANKABLE FORM (Rocq `flushed_of_receipt_any`). -/
theorem flushed_ofReceiptAny (D : BlockMap) :
    fsReceiptAny (hlc := hlc) (GF := GF) D ⊢ ∃ b : Nat, flushed (hlc := hlc) b D := by
  unfold flushed fsReceiptAny
  iintro ⟨%γs, %hseam, Hr⟩
  ihave ⟨%b, Hf⟩ := flushedAt_ofReceipt γs D $$ Hr
  iexists b, γs
  iframe Hf
  ipureintro; exact hseam

/-- THE BANK, WITH ITS INDEX NAMED (Rocq `flushed_of_bank`). -/
theorem flushed_ofBank :
    fsBank (hlc := hlc) (GF := GF) ⊢
      ∃ (b : Nat) (D : BlockMap), flushed (hlc := hlc) b D ∗ ⌜snapHolds D⌝ := by
  unfold fsBank
  iintro ⟨%D, Hr, %hh⟩
  ihave ⟨%b, Hf⟩ := flushed_ofReceiptAny D $$ Hr
  iexists b, D
  iframe Hf
  ipureintro; exact hh

end

end Xv6
