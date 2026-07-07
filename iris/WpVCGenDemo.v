(* ====================================================================== *)
(* WpVCGenDemo.v -- the WpVCGen block executor, exercised on the first four *)
(* instructions of xv6's mycpu() @ 0x800018d6.                             *)
(*                                                                         *)
(*   +0x00  1141  c.addi     sp, sp, -16     (allocate 16-byte frame)      *)
(*   +0x02  e406  c.sdsp     ra, 8(sp)       (save return address)         *)
(*   +0x04  e022  c.sdsp     s0, 0(sp)       (save frame pointer)          *)
(*   +0x06  0800  c.addi4spn s0, sp, 16      (s0 := new frame base)        *)
(*                                                                         *)
(* WHAT THIS SHOWS.  The existing mycpu proof (WpMycpu.v) discharges these  *)
(* four instructions with four separate CSL weakest-precondition lemmas     *)
(* ([myi_00]..[myi_06]), each chaining fetch/decode/execute THROUGH the      *)
(* Iris separation logic.  Here the entire four-instruction block's          *)
(* fetch -> decode -> PMP/PMA -> execute -> writeback semantics is           *)
(* discharged by a SINGLE [vm_compute] of [stepN 4] on a concrete machine    *)
(* state (RISC-V "C" enabled, a whole-memory RWX PMA region, Machine mode    *)
(* so the fetch skips address translation).  The observable effect of the    *)
(* block -- PC advances 8 bytes, sp drops by 16, s0 becomes the new frame    *)
(* base -- is then read straight off the computed final state.               *)
(*                                                                         *)
(* [mycpu4_project] closes the loop with the Iris engine: it peels the one   *)
(* batched [stepN 4] run into the FOUR per-instruction                       *)
(* [exec riscv_step s_i = Some (tt, s_i+1)] facts that the four layers of    *)
(* [wp_stepN] (WpVCGen.v) consume -- one computation, N cheap Iris steps.    *)
(*                                                                         *)
(* IMPORT NOTE.  [mword_of_int] and friends live in the SailStdpp.Base       *)
(* cluster, whose import flips [Arch.pa]'s canonical [Countable] instance.   *)
(* [mstate.mem]'s element instance was frozen (to [bv_countable]) when        *)
(* RiscvLang.v was compiled, so [code] below is left WITHOUT a [gmap ...]     *)
(* type annotation: it then infers that same frozen instance and unifies      *)
(* with [MState]'s field, instead of re-elaborating to [Countable_mword].     *)
(* ====================================================================== *)

From xv6iris Require Import RiscvLang RiscvExec WpVCGen.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import stdpp.gmap stdpp.bitvector.definitions.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. The concrete initial machine state.                                  *)
(* ---------------------------------------------------------------------- *)

Definition mycpu_pc : mword 64 := mword_of_int 0x80000000.   (* code base   *)
Definition mycpu_sp : mword 64 := mword_of_int 0x80100000.   (* initial sp  *)

(* the four compressed opcodes, little-endian, laid down at [mycpu_pc]. *)
Definition mycpu_code :=
  write_bytes (write_bytes (write_bytes (write_bytes ∅
    mycpu_pc                 2 (mword_of_int 0x1141 : mword 16))
    (add_vec_int mycpu_pc 2) 2 (mword_of_int 0xe406 : mword 16))
    (add_vec_int mycpu_pc 4) 2 (mword_of_int 0xe022 : mword 16))
    (add_vec_int mycpu_pc 6) 2 (mword_of_int 0x0800 : mword 16).

(* one PMA region spanning all of physical memory, executable+readable+writable
   -- the [matching_pma_region] the fetch and the two stores need. *)
Definition mycpu_rwx : PMA :=
  {[ {[ {[ inhabitant with PMA_executable := true ]}
             with PMA_readable := true ]}
             with PMA_writable := true ]}.
Definition mycpu_region : PMA_Region :=
  Build_PMA_Region (mword_of_int 0) (mword_of_int 0xFFFFFFFFFFFFFFFF) mycpu_rwx false.

Definition mycpu_regs : regstate :=
  register_set x2 mycpu_sp
   (register_set pma_regions (mycpu_region :: nil)
    (register_set misa (_update_Misa_C (register_lookup misa init_regstate) ('b"1"))
     (register_set PC mycpu_pc
      (register_set cur_privilege Machine
       (register_set hart_state (HART_ACTIVE tt) init_regstate))))).

Definition mycpu_s0 : mstate := MState mycpu_regs mycpu_code.

(* ---------------------------------------------------------------------- *)
(* 2. The block runs to completion, and its observable effect is correct.  *)
(*    All four proofs are ONE [vm_compute] of [stepN 4] -- no per-          *)
(*    instruction lemmas, no separation-logic chaining.                     *)
(* ---------------------------------------------------------------------- *)

(* the whole four-instruction block executes without faulting. *)
Lemma mycpu4_runs : is_Some (stepN 4 mycpu_s0).
Proof. vm_compute. eauto. Qed.

(* PC advanced by 8 bytes: four compressed (2-byte) instructions retired. *)
Lemma mycpu4_pc :
  match stepN 4 mycpu_s0 with
  | Some s => uint (register_lookup PC s.(sregs))
  | None => 0
  end = 0x80000008.
Proof. vm_compute. reflexivity. Qed.

(* sp := sp - 16 : the 16-byte stack frame was allocated (c.addi sp,-16). *)
Lemma mycpu4_sp :
  match stepN 4 mycpu_s0 with
  | Some s => match exec (rX_bits (Regidx (mword_of_int 2))) s with
              | Some (v, _) => uint v | None => 0 end
  | None => 0
  end = 0x800FFFF0.
Proof. vm_compute. reflexivity. Qed.

(* s0 := sp + 16 : the frame pointer is the new frame base (c.addi4spn). *)
Lemma mycpu4_s0 :
  match stepN 4 mycpu_s0 with
  | Some s => match exec (rX_bits (Regidx (mword_of_int 8))) s with
              | Some (v, _) => uint v | None => 0 end
  | None => 0
  end = 0x80100000.
Proof. vm_compute. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. Bridge to the Iris engine.  The single batched [stepN 4] run projects *)
(*    into the four per-instruction [exec riscv_step] facts -- exactly the  *)
(*    obligations the four telescope layers of [wp_stepN] (WpVCGen.v)        *)
(*    consume.  This is the "one [vm_compute], N cheap steps" payoff on a    *)
(*    real instruction block.                                                *)
(* ---------------------------------------------------------------------- *)
Lemma mycpu4_project s4 :
  stepN 4 mycpu_s0 = Some s4 ->
  exists s1 s2 s3,
    exec riscv_step mycpu_s0 = Some (tt, s1) /\
    exec riscv_step s1       = Some (tt, s2) /\
    exec riscv_step s2       = Some (tt, s3) /\
    exec riscv_step s3       = Some (tt, s4).
Proof.
  intro H.
  apply stepN_S_inv in H as (s1 & E0 & H).
  apply stepN_S_inv in H as (s2 & E1 & H).
  apply stepN_S_inv in H as (s3 & E2 & H).
  apply stepN_S_inv in H as (s4' & E3 & H).
  cbn [stepN] in H. injection H as <-.
  exists s1, s2, s3. eauto.
Qed.
