(* CodeHoldingAux.v -- decode/leaf lemmas for xv6's holding() in S-mode: one
   [instr] lemma per instruction of holding() (hi_00/hi_02/hi_04/hi_06 for the
   fast-path prefix, his_08 .. his_2a for the full frame/mycpu()/compare
   sequence) plus the underlying decode/execute facts they build on
   (hdec_*, hexec_*, seqz_sub_neq, po_mycpu_out_a0, ...):

     holding @ 0x80000b94 (KernelInstrs.kernel_bytes):
       +0x0  411c  c.lw  a5,0(a0)     a5 := sext32(lk->locked)
       +0x2  e399  c.bnez a5,+0x8     NOT taken (locked = 0)
       +0x4  4501  c.li  a0,0         a0 := 0
       +0x6  8082  c.ret              return to ra

   These are consumed by WpHoldingInv.wp_holding_lockinv{,_locked}, the CSL
   holding() specs against [is_lock] that supersede the plain-ownership
   whole-function WP formerly proved in this file (see WpHoldingInv.v's
   header for the current top-level story). The composition follows
   CodeMycpu.v; the c.bnez fall-through leaf [wp_cbnez_fall_s] mirrors
   WpMemsetS.wp_cbeqz_fall_s_config with BNE. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import InstrBytes.
Require Import WpDecode ExecCommon KernelText.
Require Import WpMmodeLeafBase.
Require Import KernelRvcDecode.
Require Import WpRvcBridge.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
Require Import CodeHolding.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Decode lemmas (podec-style; the tactics mirror CodePushOff's).        *)
(* ===================================================================== *)
Local Ltac h_ast :=
  first [ reflexivity
        | repeat f_equal;
          first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] ].

Local Ltac h_close1 s HmisaC :=
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; h_ast
  | apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |];
    apply exec_currentlyEnabled_Zca; exact HmisaC ].

Local Ltac h_close0 s HmisaC :=
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (currentlyEnabled Ext_Zca) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; h_ast
  | apply (exec_currentlyEnabled_Zca s HmisaC) ].

(* +0x0  0x411c  c.lw a5,0(a0) *)

(* +0x2  0xe399  c.bnez a5,+0x8 *)

(* +0x6  0x8082  c.ret: reuse CodePushOff.cdec_8082 *)

(* [hexec_bnez] moved to WpMmodeLeafBase as [exec_execute_C_BNEZ] (shared
   compressed-BNEZ exec fact; also used by pop_off/acquire retry loops). *)

(* ===================================================================== *)
(* holding()'s SLOW path (lock word nonzero): frame alloc, a5 := lk->cpu, *)
(* mycpu(), a0 := (lk->cpu == mycpu()), frame free, ret.                  *)
(*   +0x08 1101 c.addi sp,-32    +0x0a ec06 c.sdsp ra,24(sp)              *)
(*   +0x0c e822 c.sdsp s0,16(sp) +0x0e e426 c.sdsp s1,8(sp)               *)
(*   +0x10 1000 c.addi4spn s0,32 +0x12 691c c.ld a5,16(a0)                *)
(*   +0x14 84be c.mv s1,a5       +0x16 52d000ef jal ra,mycpu              *)
(*   +0x1a 40a48533 sub a0,s1,a0 +0x1e 00153513 seqz a0,a0                *)
(*   +0x22..0x2a: ldsp ra/s0/s1, addi16sp 32, ret                          *)
(* ===================================================================== *)

(* +0x12  0x691c  c.ld a5,16(a0) *)

Local Ltac h_dbase s Hpriv :=
  decode_pause_prefix s Hpriv;
  match goal with |- ?lhs = ?rhs =>
    let l := eval vm_compute in lhs in change_no_check (l = rhs) end;
  h_ast.

(* +0x16  0x52d000ef  jal ra,mycpu (offset +0xd2c) *)

(* +0x1a  0x40a48533  sub a0,s1,a0 *)

(* +0x1e  0x00153513  seqz a0,a0 (sltiu a0,a0,1) *)

(* gpr_sub_val/gpr_sltiu_val + exec_execute_RTYPE_SUB_gpr/ITYPE_SLTIU_gpr relocated to WpMmodeLeafBase.v *)

(* seqz on (a - b) is 0 when a <> b *)
Lemma seqz_sub_neq (a b : mword 64) :
  eq_vec a b = false ->
  zero_extend' 64 (bool_to_bit (zopz0zI_u (sub_vec a b)
    (sign_extend' 64 (mword_of_int 1 : mword 12)))) = (mword_of_int 0 : mword 64).
Proof.
  intro Hne.
  replace (sign_extend' 64 (mword_of_int 1 : mword 12)) with (mword_of_int 1 : mword 64)
    by (apply bv_eq; vm_compute; reflexivity).
  assert (Hab : a <> b) by (apply eq_vec_false_iff; exact Hne).
  destruct (zopz0zI_u (sub_vec a b) (mword_of_int 1)) eqn:Hlt.
  - exfalso. apply Hab.
    unfold zopz0zI_u in Hlt.
    apply Z.ltb_lt in Hlt.
    change (uint (mword_of_int 1 : mword 64)) with 1 in Hlt.
    rewrite uint_unsigned in Hlt.
    pose proof (bv_unsigned_in_range _ (sub_vec a b)) as [Hlo _].
    assert (H0 : bv_unsigned (sub_vec a b) = 0) by lia.
    apply bv_eq.
    rewrite sub_vec64_unsigned in H0.
    pose proof (bv_unsigned_in_range _ a) as Ha.
    pose proof (bv_unsigned_in_range _ b) as Hb.
    unfold bv_wrap in H0.
    assert (M : bv_modulus 64 = 18446744073709551616) by reflexivity.
    rewrite M in H0. rewrite M in Ha. rewrite M in Hb.
    apply Z.mod_divide in H0; [| lia].
    destruct H0 as [q Hq].
    assert (Hq0 : q = 0) by lia.
    lia.
  - apply bv_eq. vm_compute. reflexivity.
Qed.

Section CodeHoldingAux.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* c.bnez rs NOT taken (rs = 0): fall through to pc+2.  Mirrors          *)
  (* WpMemsetS.wp_cbeqz_fall_s_config with BEQ -> BNE.                     *)
  (* ------------------------------------------------------------------- *)

  (* ------------------------------------------------------------------- *)
  (* [instr] facts for the four fast-path instructions.                    *)
  (* ------------------------------------------------------------------- *)

End CodeHoldingAux.
