(* ====================================================================== *)
(* VBoot.v -- THE POWER-ON REGISTER FILE AS A WITNESS PARAMETER.           *)
(*                                                                         *)
(* [VTest.start] boots from [init_regstate], which is ONE choice, and the   *)
(* model does not pin it.  [RiscvLang.boot_facts]'s register clause reads   *)
(*                                                                         *)
(*   forall c, exists rs0 rs1, run (boot_prog ...) (MState rs0 ∅ dev0) tt   *)
(*                                (MState rs1 ∅ dev0) /\ gregs c = rs1      *)
(*                                                                         *)
(* with [rs0] EXISTENTIALLY quantified, and ArchReset.v's header says so in *)
(* as many words: the power-on model is "arbitrary garbage in every         *)
(* register, plus board_init's short list of explicit board-guaranteed      *)
(* writes, plus the privileged spec's own reset".  Narrowing it to the      *)
(* simulator's own initial file would put real hardware -- which has        *)
(* garbage in unreset registers -- outside the theorem.                     *)
(*                                                                         *)
(* SO [rs0] IS A SECOND SOURCE OF NONDETERMINISM, exactly like the device   *)
(* schedule, and a register test controls it the same way: as a WITNESS.    *)
(* When QEMU shows a register value the model's default boot does not       *)
(* produce, the question is not "do they disagree" but "is there an [rs0]   *)
(* that produces it".                                                       *)
(*                                                                         *)
(* THE PROCEDURE a register test follows:                                   *)
(*                                                                         *)
(*   1. run with [rs0 = init_regstate] and diff against QEMU;               *)
(*   2. for each register that differs, re-run with that register PRESET in *)
(*      [rs0] to QEMU's value ([register_set r v init_regstate], or         *)
(*      [poison] below for a whole batch);                                  *)
(*   3. if the model now matches, the register is one the boot chain leaves *)
(*      alone -- the model ADMITS QEMU's value and there is no finding, only *)
(*      a witness;                                                          *)
(*   4. if it still differs, the boot chain PINS that register to something *)
(*      the hardware does not, and THAT is a finding.                       *)
(*                                                                         *)
(* Step 4 is the only interesting outcome, and the point of the exercise is *)
(* that steps 1-3 cannot be skipped: a raw diff against the default boot    *)
(* would report every scratch register as a divergence.                     *)
(* ====================================================================== *)
From stdpp Require Import gmap bitvector.definitions list.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d.
Require Import RiscvModelBytes RiscvExec DevModel ArchReset.
Require Export VTest.
Local Open Scope Z_scope.

(* The machine after the model's OWN boot chain, run from an arbitrary
   power-on file.  [None] means the chain itself got stuck at [rs0], which
   is a fact about the chain worth seeing rather than hiding. *)
Definition boot_from (hid : Z) (rs0 : regstate) : option regstate :=
  match exec (ArchReset.boot_prog (SailStdpp.Values.mword_of_int hid) pma_boot)
             (MState rs0 ∅ dev0_state) with
  | Some (_, s) => Some (sregs s)
  | None => None
  end.

(* [VTest.start_with], with the power-on file supplied instead of assumed. *)
Definition start_from (hid : Z) (rs0 : regstate) (text : list Z)
    (rs : list region) : option mstate :=
  match boot_from hid rs0 with
  | Some r => Some (MState r (mem_of text rs) dev0_state)
  | None => None
  end.

Definition run_from (n : nat) (hid : Z) (rs0 : regstate) (text : list Z)
    (rs : list region) : option mstate :=
  match start_from hid rs0 text rs with
  | Some s => run_until n s
  | None => None
  end.

Definition status_from (n : nat) (hid : Z) (rs0 : regstate) (text : list Z)
    (rs : list region) : vstatus :=
  match start_from hid rs0 text rs with
  | Some s => run_status n s
  | None => VStuck
  end.

(* THE DEFAULT IS ONE POINT OF THE SPACE, not the specification.
   [start_default] is what [VTest.start] uses, spelled here so a test can say
   "the default boot gives X, and a different legal power-on gives Y". *)
Definition start_default : regstate := init_regstate.

(* A batch of presets, applied left to right.  A register test builds its
   witness [rs0] with this: [poison [pset x1 v; pset misa w] init_regstate].
   The dependent type is why this is a list of ALREADY-APPLIED functions
   rather than of (register, value) pairs -- [register_set]'s value type
   depends on the register, so the pair would need a sigma and every test
   would have to spell it. *)
Definition pset (f : regstate -> regstate) : regstate -> regstate := f.
Definition poison (fs : list (regstate -> regstate)) (rs : regstate) : regstate :=
  foldl (fun r f => f r) rs fs.
