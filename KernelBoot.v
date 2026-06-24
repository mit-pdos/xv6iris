(* ====================================================================== *)
(* KernelBoot.v                                                            *)
(*                                                                         *)
(* SCAFFOLDING: a weakest-precondition over the first two instructions of  *)
(* the real xv6-riscv kernel image, executed through the Sail `try_step`.  *)
(*                                                                         *)
(*   0x80000000:  auipc sp,0xa       (enc 0xa117)                          *)
(*   0x80000004:  ld   sp,472(sp)    (enc 0x1d813103)                      *)
(*                                                                         *)
(* The kernel image (instructions + symbols) is imported from the dumped   *)
(* `Kernel.*` modules produced by tools/dump_kernel.py.  The WP statement   *)
(* mirrors `wp_add_real_final` (points-to over the booting-Machine config)  *)
(* and is intended to be discharged via the PROVEN `wp_exec_step` rule,     *)
(* one application per instruction.  The two per-instruction `exec`         *)
(* reductions (auipc, ld) are the remaining frontier -- see the comment     *)
(* above `wp_kernel_first_two`.                                             *)
(* ====================================================================== *)

From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import RiscvAddTryStep.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
From Kernel Require KernelInstrs KernelData KernelSyms.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. The kernel image, imported from the dump.                            *)
(* ---------------------------------------------------------------------- *)

(* Entry address, taken from the dumped symbol table. *)
Definition kentry : Z := 0x80000000.

Lemma kentry_is_entry : KernelSyms.sym "_entry"%string = kentry.
Proof. vm_compute. reflexivity. Qed.

(* The first two instruction encodings, read straight off the dumped image
   (head of chunk 0).  [option_map ki_enc (nth_error _ i)] avoids forcing the
   8423-element tail, so these check by [reflexivity]. *)
Lemma kernel_first_two_encs :
  option_map KernelInstrs.ki_enc
    (List.nth_error KernelInstrs.kernel_instrs_chunk0 0) = Some 0xa117 /\
  option_map KernelInstrs.ki_enc
    (List.nth_error KernelInstrs.kernel_instrs_chunk0 1) = Some 0x1d813103.
Proof. split; reflexivity. Qed.

(* The instruction words handed to the Sail decoder (little-endian integer
   exactly as [ki_enc]). *)
Definition w_auipc : mword 32 := mword_of_int 0xa117.       (* auipc sp,0xa     *)
Definition w_ld    : mword 32 := mword_of_int 0x1d813103.   (* ld sp,472(sp)    *)

(* Program counters across the two-instruction window (both are 4-byte). *)
Definition kpc0 : mword 64 := mword_of_int  kentry.         (* 0x80000000 *)
Definition kpc1 : mword 64 := mword_of_int (kentry + 4).    (* 0x80000004 *)
Definition kpc2 : mword 64 := mword_of_int (kentry + 8).    (* 0x80000008 *)

(* auipc sp,0xa writes sp := pc + (0xa << 12) = 0x80000000 + 0xa000. *)
Definition sp_auipc : mword 64 := mword_of_int 0x8000a000.

(* ---------------------------------------------------------------------- *)
(* 2. The two-instruction WP (scaffolding).                                *)
(* ---------------------------------------------------------------------- *)

Section KernelBootWP.
  Context `{!riscvGS Σ}.

  (* Booting-Machine config (same shape as [wp_add_real_final]'s bundle).   *)
  Context (sp0 mst0 mstatus0 : mword 64) (mi0 : bool) (elp0 : mword 1).

  (* The value the `ld` loads from the GOT slot at sp_auipc+472 = 0x8000a1d8;
     left abstract here (it depends on the kernel's data/relocations, which
     `forward_exec_ld` below will read out of the owned memory bytes). *)
  Context (gotval mstF : mword 64) (miF : bool).

  (* ====================================================================== *)
  (* wp_kernel_first_two                                                     *)
  (*                                                                         *)
  (* Owning the booting-Machine state with PC at the kernel entry, two       *)
  (* `Loop` steps of the real `try_step` execute `auipc sp,0xa` then         *)
  (* `ld sp,472(sp)`, leaving PC at entry+8 and sp holding the loaded value. *)
  (*                                                                         *)
  (* PROOF ROUTE (frontier): discharge exactly like `wp_add_real_final` —    *)
  (*   `iApply wp_exec_step` once per instruction, each time supplying        *)
  (*   `exec riscv_step s = Some (tt, s')` for the concrete step.  Those two  *)
  (*   reductions are the per-instruction analogues of the PROVEN             *)
  (*   `forward_exec_final` (for `add`): the fetch subsystem                  *)
  (*   (`run_fetch_F_Base`/`exec_fetch_done`, instruction-agnostic) is        *)
  (*   reusable at the concrete `kpc0`/`kpc1`; only the decode wall           *)
  (*   (`encdec_backwards` for AUIPC / LOAD) and the per-instruction          *)
  (*   `execute` clause are new.  Building `forward_exec_auipc` and           *)
  (*   `forward_exec_ld` is the next milestone — hence this statement is      *)
  (*   admitted for now.                                                      *)
  (* ====================================================================== *)
  Lemma wp_kernel_first_two E (Φ : mval -> iProp Σ) :
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ kpc0 -∗
    (R_bitvector_64 x2) ↦ᵣ sp0 -∗
    nextPC ↦ᵣ kpc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗
    minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗
    (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗
    ▷ ( PC ↦ᵣ kpc2 -∗
        (R_bitvector_64 x2) ↦ᵣ gotval -∗
        nextPC ↦ᵣ kpc2 -∗
        (R_bool minstret_increment) ↦ᵣ miF -∗
        minstret ↦ᵣ mstF -∗
        cur_privilege ↦ᵣ Machine -∗
        hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗
        (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    (* FRONTIER: see the comment above.  Discharge via [wp_exec_step] x2 once
       [forward_exec_auipc] / [forward_exec_ld] are proven. *)
  Admitted.

End KernelBootWP.
