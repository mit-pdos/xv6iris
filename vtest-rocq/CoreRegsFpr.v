(* ======================================================================= *)
(* CoreRegsFpr.v -- THE FLOATING-POINT REGISTER FILE, AND THE MODEL HAS NO  *)
(* WAY TO REACH IT.                                                         *)
(*                                                                          *)
(* Source: tools/vtest/tests/core_regs_fpr.S.  Capture: CoreRegsFprGen.v.    *)
(*                                                                          *)
(* THE IMAGE: set mstatus.FS = Initial (fp state is Off at boot on both      *)
(* machines and every fp access with FS = Off is an illegal instruction),    *)
(* then `fsd f<i>, 8+8*i(s11)` for i = 0..31, then the three fp CSRs.        *)
(* QEMU runs it and reports all 32 registers zero.                          *)
(*                                                                          *)
(* THE MODEL DOES NOT GET PAST THE FIRST STORE.  It executes the FS write    *)
(* (and executes it correctly -- mstatus is 0xA_0000_2000 afterwards, which  *)
(* is what the hardware also produces; CoreRegsFcsr.v states that half as an *)
(* equation) and then takes an ILLEGAL-INSTRUCTION trap on `fsd`.            *)
(*                                                                          *)
(* WHY: the generated model has no fp INSTRUCTIONS at all.                   *)
(* model-xv6iris/sail-modules.txt lists [FD_core], which supplies the fp     *)
(* registers, fcsr and the fp CSR plumbing, but NOT the F/D instruction      *)
(* modules, so there is no encdec clause for the fp load/store opcodes and   *)
(* none for fp arithmetic: `grep 0100111` over rv64d.v finds nothing.  The   *)
(* decoder therefore returns ILLEGAL and the model traps.                    *)
(*                                                                          *)
(* AND MISA SAYS OTHERWISE, which is the sharp end of this.  The model's own *)
(* misa is 0x8000_0000_0014_112D -- bit 3 (D) and bit 5 (F) SET, because     *)
(* sail-config-rv64d.json answers `supported: true` for both and             *)
(* [reset_misa] writes one bit per [hartSupports] answer (CoreRegsMcsr.v §1  *)
(* pins the value).  So the modelled machine ADVERTISES F and D in the one   *)
(* register software is told to consult, and then refuses every instruction  *)
(* those bits promise.  A guest that does the architecturally correct thing  *)
(* -- read misa, see D, use `fsd` -- has no model execution.                 *)
(*                                                                          *)
(* CLASSIFICATION: INCOMPLETENESS, not unsoundness.  The model produces no   *)
(* value the hardware does not; it refuses a program the hardware runs.  It  *)
(* cannot make a theorem about xv6 wrong -- xv6's kernel is compiled without *)
(* fp and the system theorem proves the kernel never gets stuck, so these    *)
(* states are unreachable for it -- but it does mean no fp-using guest can   *)
(* be verified in this tree, and it means the misa bits are not to be read   *)
(* as a statement about what the model can execute.  Two ways to close it,   *)
(* and the choice is the same one ColdBoot.v's header records for B and V:   *)
(* add the F/D instruction modules to sail-modules.txt and regenerate, or    *)
(* set `supported: false` for F and D in the config so misa stops claiming   *)
(* them.  The second is a one-line change and makes the model honest; the    *)
(* first makes it bigger.  Neither is mine to make -- both files are outside *)
(* this test's remit -- so this file records the fact and pins it.           *)
(*                                                                          *)
(* NOTE ON THE STATUS CODE.  The run reports [VBudget], not [VStuck], and    *)
(* that is not a budget that was set too low.  mtvec is 0 at boot (see       *)
(* CoreRegsMcsr.v), so the trap sends the pc to 0; address 0 is not a        *)
(* declared region, so the FETCH there raises an access fault, which traps   *)
(* to mtvec = 0 again.  The machine spins in that two-line loop forever      *)
(* without ever getting stuck.  §1 shows the pc is 0 both eight and three    *)
(* hundred steps in, so the [VBudget] below is a LOOP and not slow progress. *)
(* ======================================================================= *)
From Stdlib Require Import List ZArith.
From stdpp Require Import bitvector.definitions list.
Import ListNotations.
Require Import RiscvExec RiscvModelBytes DevModel VTest CoreRegsFprGen.
Local Open Scope Z_scope.

(* n steps of the harness's own stepper, so the state at a named instruction
   can be inspected.  Same body as [VTest.run_until] without the flag test. *)
Fixpoint stepn (n : nat) (s : mstate) : option mstate :=
  match n with
  | 0%nat => Some s
  | S n' => match exec (riscv_step false) s with
            | Some (_, s') => stepn n' (settle dev_fuel s')
            | None => None
            end
  end.

Definition rd (r : register_bitvector_64) (o : option mstate) : Z :=
  match o with
  | Some s => bv_unsigned (register_lookup (R_bitvector_64 r) (sregs s))
  | None => -2
  end.

Definition fpr_start : mstate := start core_regs_fpr_text.

(* ---------------------------------------------------------------------- *)
(* 1. WHERE IT GOES.  The prologue is 11 instructions and the `jal` is the  *)
(*    11th, so after 13 steps the pc is at the FIRST fp store; after 14 it  *)
(*    is at 0 and stays there.                                             *)
(*                                                                         *)
(*    0x80000054 is `fsd ft0,8(s11)`, encoding 0x000db427 -- checked        *)
(*    against `riscv64-linux-gnu-objdump -d                                *)
(*    tools/vtest/build/core_regs_fpr.elf`, which is the check that this is *)
(*    a refused CSR/instruction and not an address-materialising load that  *)
(*    went outside a declared region.  mtval carries that same word, which  *)
(*    is the model naming the instruction it refused.                       *)
(* ---------------------------------------------------------------------- *)

Definition fpr_trap : Z * Z * Z * Z * Z * Z * Z :=
  (0x80000054,      (* pc at step 13: the first fsd                    *)
   0xA00002000,     (* ...and mstatus there: FS = Initial, so the fp   *)
                    (*    state IS enabled and that is not the reason  *)
   0,               (* pc at step 14: trapped, and mtvec is 0          *)
   2,               (* mcause: Illegal Instruction                     *)
   0x80000054,      (* mepc: the fsd                                   *)
   0x000DB427,      (* mtval: the fsd's encoding, per objdump          *)
   0).              (* pc at step 300: still 0 -- a trap loop          *)

Lemma core_regs_fpr_model_traps :
  (rd PC (stepn 13 fpr_start),
   rd mstatus (stepn 13 fpr_start),
   rd PC (stepn 14 fpr_start),
   rd mcause (stepn 14 fpr_start),
   rd mepc (stepn 14 fpr_start),
   rd mtval (stepn 14 fpr_start),
   rd PC (stepn 300 fpr_start)) = fpr_trap.
Proof. solve_vtest fpr_trap. Qed.

(* ...so the model never publishes a result. *)
Lemma core_regs_fpr_model_never_finishes :
  run_status 600 fpr_start = VBudget.
Proof. vm_cast_no_check (eq_refl VBudget). Qed.

Lemma core_regs_fpr_model_no_result : result_of (run_until 600 fpr_start) = [].
Proof. vm_cast_no_check (eq_refl (@nil Z)). Qed.

(* ---------------------------------------------------------------------- *)
(* 2. WHAT THE HARDWARE DID, so the divergence is pinned on both sides.    *)
(*    QEMU completed the image and every one of the 32 fp registers was     *)
(*    zero at boot -- which is the answer the model cannot produce, not     *)
(*    because it disagrees about the value but because it cannot run the    *)
(*    program that asks.                                                   *)
(* ---------------------------------------------------------------------- *)

Definition fpr_offs : list nat :=
  [8; 16; 24; 32; 40; 48; 56; 64; 72; 80; 88; 96; 104; 112; 120; 128;
   136; 144; 152; 160; 168; 176; 184; 192; 200; 208; 216; 224; 232; 240;
   248; 256]%nat.

Lemma core_regs_fpr_qemu_all_zero :
  (fun o => cap_word core_regs_fpr_qemu_result o) <$> fpr_offs
  = replicate 32 0.
Proof. reflexivity. Qed.

(* and QEMU DID finish: the done word is the magic, so the zeros above are a
   published result and not an unwritten region *)
Lemma core_regs_fpr_qemu_finished :
  cap_word core_regs_fpr_qemu_result 0%nat = 0x444f4e45.
Proof. reflexivity. Qed.

Lemma core_regs_fpr_disk : core_regs_fpr_qemu_disk = [].
Proof. reflexivity. Qed.
