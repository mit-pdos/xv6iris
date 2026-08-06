(* CodeMycpuAux.v -- whole-function WP for xv6's mycpu() in S-mode.
   mycpu() @ 0x800018d6 returns a0 = &cpus[cpuid] (cpuid = tp register),
   using its own 16-byte stack frame (saves/restores ra,s0).  Built by
   composing the S-mode instruction lemmas (existing framework ones plus the
   new arithmetic/auipc lemmas in WpPushOff.v), following the stack-geometry
   composition pattern of ProofKernelvec (wp_kernelvec) / WpMemsetS.

   Disassembly (KernelInstrs.v, symbol mycpu @ 0x800018d6):
     +0x00  800018d6  1141      c.addi   sp,sp,-16    frame alloc
     +0x02  800018d8  e406      c.sdsp   ra,8(sp)
     +0x04  800018da  e022      c.sdsp   s0,0(sp)
     +0x06  800018dc  0800      c.addi4spn s0,sp,16
     +0x08  800018de  8792      c.mv     a5,tp        a5 = cpuid
     +0x0a  800018e0  2781      c.addiw  a5,0         sext.w a5
     +0x0c  800018e2  079e      c.slli   a5,a5,0x7    a5 = cpuid<<7
     +0x0e  800018e4  00011517  auipc    a0,0x11
     +0x12  800018e8  a9450513  addi     a0,a0,-1388  a0 = &cpus
     +0x16  800018ec  953e      c.add    a0,a0,a5     a0 = &cpus[cpuid]
     +0x18  800018ee  60a2      c.ldsp   ra,8(sp)
     +0x1a  800018f0  6402      c.ldsp   s0,0(sp)
     +0x1c  800018f2  0141      c.addi   sp,sp,16     frame free
     +0x1e  800018f4  8082      c.ret                                        *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Values.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import InstrBytes.
Require Import ExecCommon KernelText WpAuipc.
Require Import WpMmodeLeafBase.
Require Import KernelBaseDecode.
Require Import KernelRvcDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
From iris.base_logic.lib Require Import invariants.
Require Import CodeMycpu.
Local Open Scope Z_scope.
Import Defs.

(* [callee_saved] ignores ra (x1), so a preceding jal link-write on the input
   map is irrelevant: this lets a mycpu caller state its callee_saved post
   against the pre-jal map [m] while [wp_mycpu] proves it against the post-jal
   [<[ra:=..]> m]. *)

(* ===================================================================== *)
(* Decode templates.                                                      *)
(* ===================================================================== *)
Local Ltac my_ast :=
  first [ reflexivity
        | repeat f_equal;
          first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] ].

Local Ltac my_close1 s HmisaC :=
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; my_ast
  | apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |];
    apply exec_currentlyEnabled_Zca; exact HmisaC ].

Local Ltac my_close2 s HmisaC :=
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (Defs.and_boolM (returnM _)
                          (currentlyEnabled Ext_Zca))) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; my_ast
  | apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |];
    apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |];
    apply exec_currentlyEnabled_Zca; exact HmisaC ].

(* ---- mycpu's own decodes (bit patterns not shared with memset).  The
   c.mv a5,tp / sext.w / c.slli a5,7 triple that materializes &cpus[cpuid] used
   to live here too and was imported by three decode files -- from a file that
   holds a WEAKEST PRECONDITION; it is now [cdec_8792]/[cdec_2781]/[cdec_079e]
   in KernelRvcDecode.v. ---- *)
(* +0x16  953e  c.add a0,a0,a5 -- [cdec_953e] (KernelRvcDecode.v) *)

(* ===================================================================== *)
(* The closed-form return value a0 = &cpus[cpuid].                        *)
(* ===================================================================== *)
Definition mycpu_a5 (tp0 : mword 64) : mword 64 :=
  shift_bits_left
    (sign_extend' 64 (subrange_vec_dec
       (add_vec (add_vec zero_reg tp0)
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))
    (subrange_vec_dec (mword_of_int 7 : mword 6) (Z.sub log2_xlen 1) 0).

Definition mycpu_ret (tp0 : mword 64) : mword 64 :=
  add_vec
    (add_vec
       (add_vec (add_vec_int (mword_of_int KernelSyms.mycpu : mword 64) 14)
                (auipc_off (mword_of_int 0x11 : mword 20)))
       (sign_extend' 64 (mword_of_int 0xa86 : mword 12)))
    (mycpu_a5 tp0).

(* ---------------------------------------------------------------------- *)
(* The two straight-line blocks of mycpu, in the VCgen's alphabet.          *)
(* ---------------------------------------------------------------------- *)

(* variable convention: xk ↦ SX k 0 (from vregs_init); 33/34 = the two
   stack-slot contents at block entry. *)

(* the epilogue runs with sp already at sp' (the decremented value), so its
   stack slots sit at sp+8 / sp+0. *)

Section CodeMycpuAux.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* [instr] facts for the fourteen mycpu instructions from [kernel_text]. *)
  (* ------------------------------------------------------------------- *)

  (* =================================================================== *)
  (*  THE CAPSTONE: a WP for the entire mycpu(), entry (0x800018d6) through *)
  (*  its return to the caller (PC = ra0 with the low bit cleared).         *)
  (*  Registers: ra=x1 sp=x2 tp=x4 s0=x8 a0=x10 a5=x15.                      *)
  (*  On exit a0 = &cpus[cpuid] = mycpu_ret (m0 !!! Regidx (mword_of_int 4)) *)
  (*  (the [a0] slot of the returned register file m11 equals mycpu_ret tp0),*)
  (*  a5 is clobbered, and ra/sp/s0 are restored (callee-saved).            *)
  (* =================================================================== *)
  (* the prologue's / epilogue's [instr] facts, from kernel_text via the
     existing CodeMycpu decode templates. *)

  (* ------------------------------------------------------------------- *)

End CodeMycpuAux.
