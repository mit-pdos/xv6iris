(* ====================================================================== *)
(* ArchReset.v -- THE PROGRAM A POWER-ON RUNS, with the one platform hook   *)
(* the interpreters cannot step lifted to a parameter.                      *)
(*                                                                          *)
(* [RiscvLang.boot_facts] states the per-hart register side of a power-on as *)
(* "the model's own boot chain RAN, from some power-on register file", so    *)
(* the chain has to be nameable BELOW the language file -- hence this file,  *)
(* which requires nothing but the generated model.  [ColdBoot.v] runs the    *)
(* same program from the closed [init_regstate] (the compiled evidence       *)
(* layer) and [BootReset.v] runs it over an ARBITRARY power-on file.         *)
(*                                                                          *)
(* THE CHAIN, and it is the model's own ([rv64d]'s last three definitions):  *)
(*   [sail_model_init]        the compiled register initializers            *)
(*   the BOARD's two hooks    [set_pc_reset_address] (virt's reset vector,   *)
(*                            0x80000000) and this hart's [mhartid]; the     *)
(*                            model writes 0 for both and the platform is    *)
(*                            what supplies them -- and they must be written *)
(*                            HERE, before [init_model], because [reset_sys] *)
(*                            reads pc_reset_address and                     *)
(*                            [init_boot_requirements] reads mhartid         *)
(*   [init_model ""]          the config-validity assert + [reset]           *)
(*   [init_boot_requirements] the firmware step: a0 := mhartid, a1 := DTB    *)
(*                                                                          *)
(* THE ONE PLATFORM HOOK THE INTERPRETERS CANNOT STEP.  [reset_sys] calls    *)
(* [cancel_reservation], which rv64d declares as an *Axiom* (the LR/SC       *)
(* reservation is platform state, outside [regstate]).  An opaque element of *)
(* the monad is not a constructor application, so [run]/[exec] -- both       *)
(* structural fixpoints on the program -- are STUCK on it: neither an        *)
(* interpretation of [reset] nor a case analysis of one can exist without a  *)
(* further axiom about the hook, and the boot cone deliberately has none     *)
(* (contrast [UserMemAccess.exec_cancel_reservation], which is why the       *)
(* U-mode tier can step an LR/SC).  So §1 copies the model's [reset_sys]     *)
(* with the hook as a PARAMETER and [reset_sys_at_split] proves, by          *)
(* [reflexivity], that the copy at [cancel_reservation tt] IS [reset_sys] -- *)
(* the copy's fidelity is kernel-checked, and the elision is provably the    *)
(* only difference.  Same for [reset] and [init_model].  The hook is then    *)
(* instantiated with a state no-op ([plat_hook]), which is what the model    *)
(* documents it to be.                                                      *)
(*                                                                          *)
(* IMPORT ORDER TRAP: [SailStdpp.Base] re-exports Prompt_monad's [read_reg]  *)
(* / [write_reg], so [Import Defs] must come LAST or none of the copy's      *)
(* effects unify with [M].  (Import is not transitive, so requiring this     *)
(* file does NOT leak Base's canonical [mword] instances into the language   *)
(* file -- see RiscvLang.v's note about [mstate.mem]'s type.)                *)
(* ====================================================================== *)
From stdpp Require Import gmap finite bitvector.definitions.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Import Defs.
Import ListNotations.
Open Scope string.
Open Scope bool.
Open Scope Z.

(* ---------------------------------------------------------------------- *)
(* 1. The model's own [reset_sys] / [reset] / [init_model], with the ONE    *)
(*    platform hook lifted to a parameter.  Each [_split] lemma is the      *)
(*    kernel's check that the copy beside it is the model's code verbatim.   *)
(* ---------------------------------------------------------------------- *)

Definition reset_sys_at (hook : M unit) : M (unit) :=
   write_reg cur_privilege Machine >>
   ((read_reg mstatus)  : M (mword 64)) >>= fun (w__0 : mword 64) =>
   write_reg mstatus (update_subrange_vec_dec (w__0) (3) (3) (('b"0"))) >>
   ((read_reg mstatus)  : M (mword 64)) >>= fun (w__1 : mword 64) =>
   write_reg mstatus (update_subrange_vec_dec (w__1) (17) (17) (('b"0"))) >>
   (reset_tvecs (tt)) >>
   ((read_reg mstatus)  : M (mword 64)) >>= fun (w__2 : mword 64) =>
   (long_csr_write_callback ("mstatus") ("mstatush") (w__2)) >>
   (reset_misa (tt)) >>
   hook >>
   ((read_reg pc_reset_address)  : M (mword 64)) >>= fun (w__3 : mword 64) =>
   write_reg PC w__3 >>
   ((read_reg pc_reset_address)  : M (mword 64)) >>= fun (w__4 : mword 64) =>
   write_reg nextPC w__4 >>
   write_reg mcause (zeros' (64)) >>
   ((read_reg mcause)  : M (mword 64)) >>= fun (w__5 : mword 64) =>
   (csr_name_write_callback ("mcause") (w__5)) >>
   (reset_pmp (tt)) >>
   ((read_reg mseccfg)  : M (mword 64)) >>= fun (w__6 : mword 64) =>
   write_reg mseccfg (update_subrange_vec_dec (w__6) (9) (9) ((bool_to_bit ((false  : bool))))) >>
   ((read_reg mseccfg)  : M (mword 64)) >>= fun (w__7 : mword 64) =>
   write_reg mseccfg (update_subrange_vec_dec (w__7) (8) (8) ((bool_to_bit ((false  : bool))))) >>
   (hartSupports (Ext_Zicfilp)) >>= fun (w__8 : bool) =>
   (if w__8 return M (unit) then
      ((read_reg mseccfg)  : M (mword 64)) >>= fun (w__9 : mword 64) =>
      write_reg mseccfg (update_subrange_vec_dec (w__9) (10) (10) (('b"0")))
       : M (unit)
    else returnM (tt)) >>
   (reset_stateen (tt)) >>
   write_reg vstart (zeros' (64)) >>
   write_reg vl (zeros' (64)) >>
   ((read_reg vcsr)  : M (mword 3)) >>= fun (w__10 : mword 3) =>
   write_reg vcsr (update_subrange_vec_dec (w__10) (2) (1) (('b"00"))) >>
   ((read_reg vcsr)  : M (mword 3)) >>= fun (w__11 : mword 3) =>
   write_reg vcsr (update_subrange_vec_dec (w__11) (0) (0) (('b"0"))) >>
   ((read_reg vtype)  : M (mword 64)) >>= fun (w__12 : mword 64) =>
   write_reg vtype (update_subrange_vec_dec (w__12) ((Z.sub (64) (1))) ((Z.sub (64) (1))) (('b"1"))) >>
   ((read_reg vtype)  : M (mword 64)) >>= fun (w__13 : mword 64) =>
   write_reg
     vtype
     (update_subrange_vec_dec (w__13) ((Z.sub (64) (2))) (8) ((zeros' ((Z.sub (64) (9)))))) >>
   ((read_reg vtype)  : M (mword 64)) >>= fun (w__14 : mword 64) =>
   write_reg vtype (update_subrange_vec_dec (w__14) (7) (7) (('b"0"))) >>
   ((read_reg vtype)  : M (mword 64)) >>= fun (w__15 : mword 64) =>
   write_reg vtype (update_subrange_vec_dec (w__15) (6) (6) (('b"0"))) >>
   ((read_reg vtype)  : M (mword 64)) >>= fun (w__16 : mword 64) =>
   write_reg vtype (update_subrange_vec_dec (w__16) (5) (3) (('b"000"))) >>
   ((read_reg vtype)  : M (mword 64)) >>= fun (w__17 : mword 64) =>
   write_reg vtype (update_subrange_vec_dec (w__17) (2) (0) (('b"000")))
    : M (unit).


Lemma reset_sys_at_split : reset_sys tt = reset_sys_at (cancel_reservation tt).
Proof. reflexivity. Qed.

Definition reset_at (hook : M unit) : M (unit) :=
   write_reg hart_state (HART_ACTIVE (tt)) >>
   (reset_sys_at hook) >> (reset_vmem (tt)) >> (reset_elp (tt)) >> returnM ((ext_reset (tt))).

Lemma reset_at_split : reset tt = reset_at (cancel_reservation tt).
Proof. reflexivity. Qed.

Definition init_model_at (config_filename : string) (hook : M unit) : M (unit) :=
   (config_is_valid (tt)) >>= fun (w__0 : bool) =>
   assert_exp' w__0 (String.append
                       ((if generic_eq (config_filename) ("") then "Default config"
                         else String.append ("Config in ") (config_filename))) (" is invalid.")) >>= fun _ =>
   (reset_at hook)
    : M (unit).

Lemma init_model_at_split (config_filename : string) :
  init_model config_filename = init_model_at config_filename (cancel_reservation tt).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. THE BOOT PROGRAM.                                                    *)
(*                                                                         *)
(*    [hid] is the hart id the platform wires to this hart; the program is   *)
(*    parametric in it (the chain only stores it and copies it into a0).     *)
(* ---------------------------------------------------------------------- *)

(* the reservation hook, as the model documents it: it moves no machine state *)
Definition plat_hook : M unit := returnm tt.

(* virt's reset vector.  Spelled with the model's own [mword_of_int] because
   [RiscvLang.boot_w64] is above this file; the two are the same function, so
   [reset_regs]' PC pin and this write are definitionally the same value. *)
Definition reset_vector : mword 64 := SailStdpp.Values.mword_of_int 0x80000000.

(* the chain's PRE-[init_model] half: the compiled register initializers plus
   the board's two writes.  Split out because the config assert lives at
   exactly this state -- [config_is_valid] reads [pma_regions], which
   [sail_model_init] has by then written and which [reset] never touches. *)
Definition boot_pre (hid : mword 64) : M unit :=
  sail_model_init tt >>
  set_pc_reset_address reset_vector >>
  write_reg mhartid hid.

Definition boot_prog (hid : mword 64) : M unit :=
  boot_pre hid >>
  init_model_at "" plat_hook >>
  init_boot_requirements tt.
