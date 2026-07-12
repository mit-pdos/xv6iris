(* WpRelease.v -- whole-function WP for xv6's release() in S-mode, against
   the CSL lock invariant of WpLock.v: the caller supplies [is_lock γ lk R],
   the ownership token [locked γ] and the protected resource [R]; release()
   stores them back into the invariant when its [sw zero,0(s1)] clears the
   lock word (WpLockLeaves.wp_sw_zero_lockinv).

     release @ 0x80000c82 (KernelInstrs.kernel_bytes):
       +0x00 1101      c.addi sp,-32
       +0x02 ec06      c.sdsp ra,24(sp)
       +0x04 e822      c.sdsp s0,16(sp)
       +0x06 e426      c.sdsp s1,8(sp)
       +0x08 1000      c.addi4spn s0,sp,32
       +0x0a 84aa      c.mv s1,a0
       +0x0c f07ff0ef  jal ra,holding      returns 1 (the token refutes 0)
       +0x10 cd11      c.beqz a0,+0x1c     NOT taken
       +0x12 0004b823  sd zero,16(s1)      lk->cpu := 0
       +0x16 0310000f  fence rw,w
       +0x1a 0004a023  sw zero,0(s1)       lk->locked := 0  (invariant closes)
       +0x1e f9bff0ef  jal ra,pop_off
       +0x22 60e2 / +0x24 6442 / +0x26 64a2 / +0x28 6105 / +0x2a 8082  epilogue *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import WpGprCsrwCommon.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpDecode WpEntryNew.
Require Import WpGpr WpGprRvc.
Require Import SmodeCore WpSmodeGpr WpMemsetS WpKernelvecNew.
Require Import WpMycpu WpPushOffTop WpAcquireTop.
Require Import WpLock WpLockLeaves WpHoldingInv WpPopOff.
Require Import StackOwn.
Require Import CalleeSaved.
(* subrange_full / mSIE_lower / sie_bit for the sstatus-SIE bridge; kept
   QUALIFIED so the WpGprCsrwC namespace doesn't shadow anything. *)
Require WpGprCsrwC.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Decode lemmas.                                                         *)
(* ===================================================================== *)

Local Ltac rl_ast :=
  first [ reflexivity
        | repeat f_equal;
          first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] ].

Local Ltac rl_dbase s Hpriv :=
  decode_pause_prefix s Hpriv;
  match goal with |- ?lhs = ?rhs =>
    let l := eval vm_compute in lhs in change_no_check (l = rhs) end;
  rl_ast.

(* +0x0c  0xf07ff0ef  jal ra,holding (offset -0xfa) *)
Lemma rldec_jal_holding s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf07ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 0x1fff06 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; rl_dbase s Hpriv ]. Qed.

(* +0x1e  0xf9bff0ef  jal ra,pop_off (offset -0x66) *)
Lemma rldec_jal_popoff s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf9bff0ef : mword 32)) s
  = Some (JAL (mword_of_int 0x1fff9a : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; rl_dbase s Hpriv ]. Qed.

(* +0x12  0x0004b823  sd zero,16(s1) *)
Lemma rldec_sd_zero s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0004b823 : mword 32)) s
  = Some (STORE (mword_of_int 16, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; rl_dbase s Hpriv ]. Qed.

(* +0x1a  0x0004a023  sw zero,0(s1) *)
Lemma rldec_sw_zero s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0004a023 : mword 32)) s
  = Some (STORE (mword_of_int 0, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; rl_dbase s Hpriv ]. Qed.

(* ===================================================================== *)
(* [instr] facts.                                                         *)
(* ===================================================================== *)
Section WpReleaseInstr.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Local Ltac mk_rvc4 A h w pc ast decname expname :=
    let Hlpad := fresh "Hlpad" in let H2al := fresh "H2al" in
    let H4al := fresh "H4al" in let Hrvc := fresh "Hrvc" in
    let Hsub := fresh "Hsub" in let Hbytes := fresh "Hbytes" in
    assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
    assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
    assert (H4al : is_aligned_vaddr (Virtaddr pc) 4 = true) by (vm_compute; reflexivity);
    assert (Hrvc : isRVC h = true) by (vm_compute; reflexivity);
    assert (Hsub : subrange_vec_dec w 15 0 = h) by (apply bv_eq; vm_compute; reflexivity);
    assert (Hbytes : forall j, (j < 4)%nat ->
        KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte w j))
      by (intros j Hj;
          do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
    iIntros "#Ht"; rewrite /instr;
    iSplitR; [iPureIntro; exact Hlpad|];
    iExists (F_RVC h);
    iSplitR; [iPureIntro; reflexivity|];
    iSplitL "";
    [ iApply (instr_bytes_rvc4 pc h w H2al H4al Hrvc Hsub);
      iApply (kernel_window_pc A w 4 pc eq_refl Hbytes with "Ht")
    | iIntros (?) "_"; iPureIntro; intros; cbn [fetch_is_rvc];
      eexists; (split; [ apply decname; assumption
                       | split; [ vm_compute; reflexivity
                                | intro; apply expname ] ]) ].

  Local Ltac mk_rvc2 A h pc ast decname expname :=
    let Hlpad := fresh "Hlpad" in let H2al := fresh "H2al" in
    let H4al := fresh "H4al" in let Hrvc := fresh "Hrvc" in
    let Hbytes := fresh "Hbytes" in
    assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
    assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
    assert (H4al : is_aligned_vaddr (Virtaddr pc) 4 = false) by (vm_compute; reflexivity);
    assert (Hrvc : isRVC h = true) by (vm_compute; reflexivity);
    assert (Hbytes : forall j, (j < 2)%nat ->
        KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte h j))
      by (intros j Hj;
          do 2 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
    iIntros "#Ht"; rewrite /instr;
    iSplitR; [iPureIntro; exact Hlpad|];
    iExists (F_RVC h);
    iSplitR; [iPureIntro; reflexivity|];
    iSplitL "";
    [ iApply (instr_bytes_rvc2 pc h H2al H4al Hrvc);
      iApply (kernel_window_pc A h 2 pc eq_refl Hbytes with "Ht")
    | iIntros (?) "_"; iPureIntro; intros; cbn [fetch_is_rvc];
      eexists; (split; [ apply decname; assumption
                       | split; [ vm_compute; reflexivity
                                | intro; apply expname ] ]) ].

  Local Ltac mk_base A w pc ast decname :=
    let Hlpad := fresh "Hlpad" in let H2al := fresh "H2al" in
    let Hnrvc := fresh "Hnrvc" in let Hbytes := fresh "Hbytes" in
    assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
    assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
    assert (Hnrvc : isRVC (subrange_vec_dec w 15 0) = false) by (vm_compute; reflexivity);
    assert (Hbytes : forall j, (j < 4)%nat ->
        KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte w j))
      by (intros j Hj;
          do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
    iIntros "#Ht"; rewrite /instr;
    iSplitR; [iPureIntro; exact Hlpad|];
    iExists (F_Base w);
    iSplitR; [iPureIntro; reflexivity|];
    iSplitL "";
    [ iApply (instr_bytes_base pc w H2al Hnrvc);
      iApply (kernel_window_pc A w 4 pc eq_refl Hbytes with "Ht")
    | iIntros (?) "_"; iPureIntro; intros; apply decname; assumption ].

  Notation RL := KernelSyms.release.

  Lemma rli_00 : kernel_text -∗ instr (mword_of_int (RL + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc2 (RL + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (RL + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) podec_00 exec_execute_C_ADDI. Qed.

  Lemma rli_02 : kernel_text -∗ instr (mword_of_int (RL + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc4 (RL + 0x02)%Z (mword_of_int 0xec06 : mword 16) (mword_of_int 0xe822ec06 : mword 32)
    (mword_of_int (RL + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) podec_02 exec_execute_C_SDSP. Qed.

  Lemma rli_04 : kernel_text -∗ instr (mword_of_int (RL + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc2 (RL + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (RL + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) podec_04 exec_execute_C_SDSP. Qed.

  Lemma rli_06 : kernel_text -∗ instr (mword_of_int (RL + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc4 (RL + 0x06)%Z (mword_of_int 0xe426 : mword 16) (mword_of_int 0x1000e426 : mword 32)
    (mword_of_int (RL + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) podec_06 exec_execute_C_SDSP. Qed.

  Lemma rli_08 : kernel_text -∗ instr (mword_of_int (RL + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc2 (RL + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (RL + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) podec_08 exec_execute_C_ADDI4SPN. Qed.

  Lemma rli_0a : kernel_text -∗ instr (mword_of_int (RL + 0x0a) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc4 (RL + 0x0a)%Z (mword_of_int 0x84aa : mword 16) (mword_of_int 0xf0ef84aa : mword 32)
    (mword_of_int (RL + 0x0a) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) aqdec_mv_s1_a0 exec_execute_C_MV. Qed.

  Lemma rli_0c : kernel_text -∗ instr (mword_of_int (RL + 0x0c) : mword 64) false (JAL (mword_of_int 0x1fff06 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (RL + 0x0c)%Z (mword_of_int 0xf07ff0ef : mword 32)
    (mword_of_int (RL + 0x0c) : mword 64) (JAL (mword_of_int 0x1fff06 : mword 21, Regidx (mword_of_int 1))) rldec_jal_holding. Qed.

  Lemma rli_10 : kernel_text -∗ instr (mword_of_int (RL + 0x10) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 14 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc2 (RL + 0x10)%Z (mword_of_int 0xcd11 : mword 16)
    (mword_of_int (RL + 0x10) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 14 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) ppdec_beqz1c exec_execute_C_BEQZ. Qed.

  Lemma rli_12 : kernel_text -∗ instr (mword_of_int (RL + 0x12) : mword 64) false (STORE (mword_of_int 16, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 8)).
  Proof. mk_base (RL + 0x12)%Z (mword_of_int 0x0004b823 : mword 32)
    (mword_of_int (RL + 0x12) : mword 64) (STORE (mword_of_int 16, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 8)) rldec_sd_zero. Qed.

  Lemma rli_16 : kernel_text -∗ instr (mword_of_int (RL + 0x16) : mword 64) false (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 1 : mword 4, Regidx (mword_of_int 0), Regidx (mword_of_int 0))).
  Proof. mk_base (RL + 0x16)%Z (mword_of_int 0x0310000f : mword 32)
    (mword_of_int (RL + 0x16) : mword 64) (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 1 : mword 4, Regidx (mword_of_int 0), Regidx (mword_of_int 0))) ppdec_fence. Qed.

  Lemma rli_1a : kernel_text -∗ instr (mword_of_int (RL + 0x1a) : mword 64) false (STORE (mword_of_int 0, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4)).
  Proof. mk_base (RL + 0x1a)%Z (mword_of_int 0x0004a023 : mword 32)
    (mword_of_int (RL + 0x1a) : mword 64) (STORE (mword_of_int 0, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4)) rldec_sw_zero. Qed.

  Lemma rli_1e : kernel_text -∗ instr (mword_of_int (RL + 0x1e) : mword 64) false (JAL (mword_of_int 0x1fff9a : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (RL + 0x1e)%Z (mword_of_int 0xf9bff0ef : mword 32)
    (mword_of_int (RL + 0x1e) : mword 64) (JAL (mword_of_int 0x1fff9a : mword 21, Regidx (mword_of_int 1))) rldec_jal_popoff. Qed.

  Lemma rli_22 : kernel_text -∗ instr (mword_of_int (RL + 0x22) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc4 (RL + 0x22)%Z (mword_of_int 0x60e2 : mword 16) (mword_of_int 0x644260e2 : mword 32)
    (mword_of_int (RL + 0x22) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) podec_22 exec_execute_C_LDSP. Qed.

  Lemma rli_24 : kernel_text -∗ instr (mword_of_int (RL + 0x24) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc2 (RL + 0x24)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (RL + 0x24) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) podec_24 exec_execute_C_LDSP. Qed.

  Lemma rli_26 : kernel_text -∗ instr (mword_of_int (RL + 0x26) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc4 (RL + 0x26)%Z (mword_of_int 0x64a2 : mword 16) (mword_of_int 0x610564a2 : mword 32)
    (mword_of_int (RL + 0x26) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) podec_26 exec_execute_C_LDSP. Qed.

  Lemma rli_28 : kernel_text -∗ instr (mword_of_int (RL + 0x28) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc2 (RL + 0x28)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (RL + 0x28) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) podec_28 exec_execute_C_ADDI16SP. Qed.

  Lemma rli_2a : kernel_text -∗ instr (mword_of_int (RL + 0x2a) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc4 (RL + 0x2a)%Z (mword_of_int 0x8082 : mword 16) (mword_of_int 0x65178082 : mword 32)
    (mword_of_int (RL + 0x2a) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) podec_2a exec_execute_C_JR. Qed.

End WpReleaseInstr.

(* ===================================================================== *)
(* JAL with a 2-mod-4 target, legal under Zca (pop_off sits at 0x...c3a). *)
(* ===================================================================== *)

Lemma exec_execute_JAL_gpr_zca (imm : mword 21) (rd : mword 5) s :
  uint rd <> 0 ->
  eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  exec (execute_JAL imm (Regidx rd)) s
  = Some (RETIRE_SUCCESS,
          set_reg (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))
                  (R_bitvector_64 (gpr_of_Z (uint rd)))
                  (regval_into_reg (register_lookup nextPC s.(sregs)))).
Proof.
  intros Hrd Halign Hzca.
  unfold execute_JAL, get_next_pc.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg nextPC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_jump_to_zca _ s Halign Hzca)).
  cbn match.
  match goal with |- context[Defs.bind0 ?wx _] =>
    assert (Hwx : exec wx (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))
                  = Some (tt, set_reg (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))
                                (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg (register_lookup nextPC s.(sregs)))))
  end.
  { rewrite (exec_wX_bits_gpr rd (register_lookup nextPC s.(sregs)) _).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hwx).
  apply exec_returnm.
Qed.

Section WpJalZca.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_jal_gpr_s_zca (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 21)
      (m : gmap regidx (mword 64))
      (q : Qp) :
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    hw_config -∗
    smode_config γ (DfracOwn q) -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (JAL (imm, Regidx rd)) -∗
    ( smode_config γ (DfracOwn q) -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec_int pc 4)]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hrd Hal0)
      "#Hhw Hsm Htlbinv [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iApply (wp_instr_s_tlbinv root_ppn γ E Φ pc false (JAL (imm, Regidx rd))

              HN
              with "Hsm Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    assert (Hpcv : register_lookup PC
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = pc).
    { unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    assert (Hlink : register_lookup nextPC
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = add_vec_int pc 4).
    { unfold set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    assert (Lmisa1 : register_lookup misa (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = misa0).
    { unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lmisa | vm_compute; reflexivity ]. }
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm))
            with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec_int pc 4))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec_int pc 4))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                        nextPC (add_vec pc (sign_extend' 64 imm)))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (add_vec_int pc 4))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (JAL (imm, Regidx rd))) with (execute_JAL imm (Regidx rd)).
      rewrite (exec_execute_JAL_gpr_zca imm rd (set_reg σ nextPC (add_vec_int pc 4))
                 Hrd ltac:(rewrite Hpcv; exact Hal0)
                 (exec_currentlyEnabled_Zca (set_reg σ nextPC (add_vec_int pc 4)) ltac:(rewrite Lmisa1; exact HmisaC))).
      rewrite Hpcv. rewrite Hlink. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hsm' Htlbinv' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                         nextPC (add_vec pc (sign_extend' 64 imm)))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (add_vec_int pc 4))).(sregs)
             = add_vec pc (sign_extend' 64 imm)).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hsm' Htlbinv' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

End WpJalZca.

(* ===================================================================== *)
(* Bridge: SIE=0 on mstatus ==> pop_off's sstatus SIE-bit precondition.    *)
(* Lets wp_release/callers derive the [neq_vec (and_vec (sstatus_read      *)
(* mstatus0) 2) zero_reg = false] pop_off premise from the SIE=0 fact that  *)
(* now lives folded inside smode_config (so mstatus0 stays hidden).        *)
(* ===================================================================== *)
Lemma mword1_zero_of_ne_one (x : mword 1) :
  eq_vec x ('b"1") = false -> x = ('b"0" : mword 1).
Proof.
  intro H. apply eq_vec_false_iff in H. apply bv_eq.
  pose proof (bv_unsigned_in_range _ x) as Hr.
  assert (Hmod : bv_modulus 1 = 2) by (vm_compute; reflexivity).
  rewrite Hmod in Hr.
  assert (H1 : bv_unsigned ('b"1" : mword 1) = 1) by (vm_compute; reflexivity).
  assert (H0 : bv_unsigned ('b"0" : mword 1) = 0) by (vm_compute; reflexivity).
  rewrite H0.
  assert (Hne : bv_unsigned x <> 1).
  { intro Hc. apply H. apply bv_eq. rewrite H1. exact Hc. }
  lia.
Qed.

Lemma sstatus_sie_clear_neq (m : mword 64) :
  eq_vec (_get_Mstatus_SIE m) ('b"1") = false ->
  neq_vec (and_vec (sstatus_read m)
             (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))) zero_reg = false.
Proof.
  intro HSIE.
  unfold neq_vec. apply negb_false_iff. apply eq_vec_true_iff.
  assert (Hz : _get_Mstatus_SIE m = ('b"0" : mword 1))
    by (apply mword1_zero_of_ne_one; exact HSIE).
  assert (Hb1 : Z.testbit (bv_unsigned (sstatus_read m)) 1 = false).
  { unfold sstatus_read. rewrite WpGprCsrwC.subrange_full.
    apply WpGprCsrwC.sie_bit. rewrite WpGprCsrwC.mSIE_lower. exact Hz. }
  assert (Hmask : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)) : mword 64) = 2)
    by (vm_compute; reflexivity).
  assert (Hzr : bv_unsigned (zero_reg : mword 64) = 0) by (vm_compute; reflexivity).
  apply bv_eq. rewrite WpGprCsrwC.and_vec_unsigned. rewrite Hmask. rewrite Hzr.
  apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec. rewrite Z.bits_0.
  destruct (decide (j = 1)) as [->|Hne].
  - rewrite Hb1. reflexivity.
  - assert (Ht2 : Z.testbit 2 j = false).
    { destruct (Z.eq_dec j 0) as [->|Hj0].
      - reflexivity.
      - apply Z.bits_above_log2; [lia|]. change (Z.log2 2) with 1. lia. }
    rewrite Ht2. apply andb_false_r.
Qed.

(* ===================================================================== *)
(* wp_release -- the CSL release spec: the caller supplies the lock       *)
(* [is_lock γ lka R], the ownership token [locked γ] and the protected    *)
(* resource [R]; both are returned INTO the invariant by the lock-word    *)
(* clear.  Requires lk->cpu = mycpu() (so holding() returns 1), plus      *)
(* pop_off()'s preconditions (SIE = 0, noff >= 1, intena = 0).            *)
(* ===================================================================== *)
Section WpReleaseTop.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Notation RL := KernelSyms.release.

  Lemma wp_release_words (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (γ : gname) (γc : gname) (b : mword 1) (lka : mword 64) (R : iProp Σ)
      (m : gmap regidx (mword 64))
      (cpuold : mword 64) (noffv intenav : mword 32)
      (vr24 vr16 vr8 vh24 vh16 vh8 vh0 vhra vhs0 : bv 64)
      {dqi : dfrac} :
    let pcE : mword 64 := mword_of_int RL in
    let lk0 := m !!! Regidx (mword_of_int 10 : mword 5) in
    let a_cpu := add_vec lk0 (sign_extend' 64 (mword_of_int 16 : mword 12)) in
    let spr := add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    let a_r24 := add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) in
    let a_r16 := add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let a_r8  := add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let spdh := add_vec spr (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    let a_h24 := add_vec spdh (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) in
    let a_h16 := add_vec spdh (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let a_h8  := add_vec spdh (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let a_h0  := add_vec spdh (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let mch := add_vec spdh (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) in
    let a_hfra := add_vec mch (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let a_hfs0 := add_vec mch (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let cpuv := mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) in
    let a_noff := add_vec cpuv (sign_extend' 64 (mword_of_int 120 : mword 12)) in
    let a_int := add_vec cpuv (sign_extend' 64 (mword_of_int 124 : mword 12)) in
    let nv1 := sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 noffv) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0) in
    let storeval_noff := (autocast (T := mword) (subrange_vec_dec nv1 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    ↑minstretN ⊆ E ->
    ↑lockN ⊆ E ->
    (* the lock word (through the invariant) and the data slots *)
    add_vec lk0 (sign_extend' 64 (mword_of_int 0 : mword 12)) = lka ->
    (* lk/cpu/noff/int slot geometry DERIVED in the leaves/pop_off from the
       lock invariant and the owned points-to -- no po_slot_geom premise. *)
    (* THIS cpu holds the lock: lk->cpu = mycpu() *)
    eq_vec cpuold cpuv = true ->
    (* pop_off preconditions (the sstatus SIE-bit fact is derived from the
       SIE=0 fact folded into smode_config, so mstatus0 stays hidden) *)
    zopz0zKzJ_s zero_reg (sign_extend' 64 noffv) = false ->
    eq_vec (sign_extend' 64 intenav) zero_reg = true ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    smode_config γc (DfracOwn 1) -∗
    ghost_var γc (1/2) b -∗
    tlb_inv root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m -∗
    is_lock γ lka R -∗
    locked γ -∗
    R -∗
    a_cpu ↦₈ cpuold -∗
    a_noff ↦₄ noffv -∗
    a_int ↦₄{ dqi } intenav -∗
    a_r24 ↦₈ vr24 -∗
    a_r16 ↦₈ vr16 -∗
    a_r8 ↦₈ vr8 -∗
    a_h24 ↦₈ vh24 -∗
    a_h16 ↦₈ vh16 -∗
    a_h8 ↦₈ vh8 -∗
    a_h0 ↦₈ vh0 -∗
    a_hfra ↦₈ vhra -∗
    a_hfs0 ↦₈ vhs0 -∗
    ( ∀ mr,
      smode_config γc (DfracOwn 1) -∗
      ghost_var γc (1/2) b -∗
      tlb_inv root_ppn -∗
      pc_is ret_tgt -∗
      gpr_file mr -∗
      ⌜ callee_saved m mr ⌝ -∗
      a_cpu ↦₈ (zero_reg : mword 64) -∗
      a_noff ↦₄ storeval_noff -∗
      a_int ↦₄{ dqi } intenav -∗
      (∃ (u1 u2 u3 u4 u5 u6 u7 u8 u9 : bv 64),
        a_r24 ↦₈ u1 ∗
        a_r16 ↦₈ u2 ∗
        a_r8 ↦₈ u3 ∗
        a_h24 ↦₈ u4 ∗
        a_h16 ↦₈ u5 ∗
        a_h8 ↦₈ u6 ∗
        a_h0 ↦₈ u7 ∗
        a_hfra ↦₈ u8 ∗
        a_hfs0 ↦₈ u9) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros pcE lk0 a_cpu spr a_r24 a_r16 a_r8 spdh a_h24 a_h16 a_h8 a_h0 mch a_hfra a_hfs0
      cpuv a_noff a_int nv1 storeval_noff ret_tgt
      HN HNl
      Hlkeq
      Hmine Hnoffpos Hint Hal0.
    iIntros "Hcfg Htoken Htlbinv
             #Htext Hpc Hfile #Hlock Htok HRes Hcpu Hnoff Hint
             Hr24 Hr16 Hr8 Hh24 Hh16 Hh8 Hh0 Hhfra Hhfs0 Hcont".
    (* unbundle the ambient S-mode config: recovers the raw cells, the folded
       facts, and smode_config's half of the SIE ghost var (Hgc). *)
    iDestruct (smode_config_unbundle γc (DfracOwn 1) with "Hcfg")
      as "(Hhw & Hinv & Hhs & Hpriv & Hmsb & Hmieb & Hmenvb)".
    iDestruct "Hhw" as "#Hhw". iDestruct "Hinv" as "#Hinv".
    iDestruct "Hmsb" as (mstatus0) "(Hms & Hgc & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %HFIOM & %Hmenvval0)".
    (* pop_off's sstatus SIE-bit precondition, derived from the folded SIE=0 *)
    assert (Hsst2 : neq_vec (and_vec (sstatus_read mstatus0)
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))) zero_reg = false)
      by (apply sstatus_sie_clear_neq; exact HSIE).
    iPoseProof (rli_00 with "Htext") as "Hi00".
    iPoseProof (rli_02 with "Htext") as "Hi02".
    iPoseProof (rli_04 with "Htext") as "Hi04".
    iPoseProof (rli_06 with "Htext") as "Hi06".
    iPoseProof (rli_08 with "Htext") as "Hi08".
    iPoseProof (rli_0a with "Htext") as "Hi0a".
    iPoseProof (rli_0c with "Htext") as "Hi0c".
    iPoseProof (rli_10 with "Htext") as "Hi10".
    iPoseProof (rli_12 with "Htext") as "Hi12".
    iPoseProof (rli_16 with "Htext") as "Hi16".
    iPoseProof (rli_1a with "Htext") as "Hi1a".
    iPoseProof (rli_1e with "Htext") as "Hi1e".
    iPoseProof (rli_22 with "Htext") as "Hi22".
    iPoseProof (rli_24 with "Htext") as "Hi24".
    iPoseProof (rli_26 with "Htext") as "Hi26".
    iPoseProof (rli_28 with "Htext") as "Hi28".
    iPoseProof (rli_2a with "Htext") as "Hi2a".
    (* +0x00 c.addi sp,-32 *)
    iApply (wp_caddi_gpr_s_config root_ppn E Φ pcE csp_rs1 (mword_of_int 32 : mword 6) m
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi00 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr)
      by (rewrite /R1; apply lookup_total_insert).
    assert (Hpp02 : add_vec_int pcE 2 = mword_of_int (RL + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,24(sp) *)
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (RL + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              R1 vr24 mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi02 [Hr24] [-]").
    { iEval (rewrite HspR1). iExact "Hr24". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hr24".
    assert (HraR1 : R1 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /R1; rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HspR1 HraR1) in "Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (RL + 0x02) : mword 64) 2 = mword_of_int (RL + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,16(sp) *)
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (RL + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              R1 vr16 mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi04 [Hr16] [-]").
    { iEval (rewrite HspR1). iExact "Hr16". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hr16".
    assert (Hs0R1 : R1 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /R1; rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HspR1 Hs0R1) in "Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (RL + 0x04) : mword 64) 2 = mword_of_int (RL + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,8(sp) *)
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (RL + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              R1 vr8 mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi06 [Hr8] [-]").
    { iEval (rewrite HspR1). iExact "Hr8". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hr8".
    assert (Hs1R1 : R1 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /R1; rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HspR1 Hs1R1) in "Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (RL + 0x06) : mword 64) 2 = mword_of_int (RL + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_gpr_s_config root_ppn E Φ (mword_of_int (RL + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              R1 mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi08 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (Hpp0a : add_vec_int (mword_of_int (RL + 0x08) : mword 64) 2 = mword_of_int (RL + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.mv s1,a0 *)
    iApply (wp_cmv_gpr_s_config root_ppn E Φ (mword_of_int (RL + 0x0a)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              R2 mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi0a [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    set (R3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (R2 !!! Regidx (mword_of_int 10 : mword 5)))]> R2).
    assert (Hpp0c : add_vec_int (mword_of_int (RL + 0x0a) : mword 64) 2 = mword_of_int (RL + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c jal ra,holding *)
    iDestruct (kv_cfg_split γc mstatus0 mie_v mdv0 menvcfg0 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe HFIOM Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hgc Hmie Hmdl Hmenv")
      as "(Hsm & Hhs2 & Hpriv2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2)".
    iApply (wp_jal_gpr_s root_ppn γc E Φ (mword_of_int (RL + 0x0c)) (mword_of_int 1 : mword 5) (mword_of_int 0x1fff06 : mword 21)
              R3 (1/2)%Qp
              HN ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hsm Htlbinv Hpc Hfile Hi0c [-]").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iDestruct (kv_cfg_recombine γc mstatus0 mie_v mdv0 menvcfg0
                 with "Hsm Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2")
      as "(Hhs & Hpriv & Hms & Hgc & Hmie & Hmdl & Hmenv)".
    set (R4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (RL + 0x0c) : mword 64) 4)]> R3).
    assert (Htgth : add_vec (mword_of_int (RL + 0x0c) : mword 64) (sign_extend' 64 (mword_of_int 0x1fff06 : mword 21)) = mword_of_int KernelSyms.holding)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgth) in "Hpc".
    (* ---- holding(): the token forces the slow path, a0 := 1 ---- *)
    assert (Ha0R4 : R4 !!! Regidx (mword_of_int 10 : mword 5) = lk0).
    { rewrite /R4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HspR4 : R4 !!! Regidx csp_rs1 = spr).
    { rewrite /R4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HspR1. }
    assert (HtpR4 : R4 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /R4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HR4s2 : R4 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5)).
    { rewrite /R4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HR4s3 : R4 !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5)).
    { rewrite /R4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HR4s4 : R4 !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5)).
    { rewrite /R4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HR4s5 : R4 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5)).
    { rewrite /R4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HR4s6 : R4 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5)).
    { rewrite /R4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HR4s7 : R4 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5)).
    { rewrite /R4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HR4s8 : R4 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5)).
    { rewrite /R4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HR4s9 : R4 !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5)).
    { rewrite /R4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HR4s10 : R4 !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5)).
    { rewrite /R4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HR4s11 : R4 !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5)).
    { rewrite /R4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HraR4 : R4 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (RL + 0x0c) : mword 64) 4)
      by (rewrite /R4; apply lookup_total_insert).
    iDestruct (smode_config_rebuild γc (DfracOwn 1) mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe HFIOM Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hgc Hmie Hmdl Hmenv") as "Hcfg".
    iApply (wp_holding_lockinv_locked root_ppn γc E Φ γ lka R R4 cpuold
              vh24 vh16 vh8 vhra vhs0
              (dqc:=DfracOwn 1)
              HN HNl ltac:(rewrite Ha0R4; exact Hlkeq)
              ltac:(rewrite HtpR4; exact Hmine)
              ltac:(rewrite HraR4; vm_compute; reflexivity)
              with "Hcfg Htlbinv Htext Hpc Hfile Hlock Htok
                    [Hcpu] [Hh24] [Hh16] [Hh8] [Hhfra] [Hhfs0] [-]").
    { iEval (rewrite Ha0R4). iExact "Hcpu". }
    { iEval (rewrite HspR4). iExact "Hh24". }
    { iEval (rewrite HspR4). iExact "Hh16". }
    { iEval (rewrite HspR4). iExact "Hh8". }
    { iEval (rewrite HspR4). iExact "Hhfra". }
    { iEval (rewrite HspR4). iExact "Hhfs0". }
    iIntros (mh) "Hcfg Htlbinv Hpc Htok Hfile %Hmhf Hcpu Hjunk".
    clear HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe HFIOM Hmenvval0 Hsst2 mstatus0 mie_v mdv0 menvcfg0.
    iDestruct (smode_config_unbundle γc (DfracOwn 1) with "Hcfg")
      as "(_ & _ & Hhs & Hpriv & Hmsb & Hmieb & Hmenvb)".
    iDestruct "Hmsb" as (mstatus0) "(Hms & Hgc & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %HFIOM & %Hmenvval0)".
    iEval (rewrite Ha0R4) in "Hcpu".
    destruct Hmhf as (Hmcs & Hma0).
    unfold callee_saved in Hmcs.
    destruct Hmcs as (Hmsp & Hmtp & Hms0 & Hms1 & Hms2 & Hms3 & Hms4 & Hms5 & Hms6 & Hms7 & Hms8 & Hms9 & Hms10 & Hms11).
    iDestruct "Hjunk" as (w24 w16 w8 wra ws0) "(Hh24 & Hh16 & Hh8 & Hhfra & Hhfs0)".
    iEval (rewrite HspR4) in "Hh24". iEval (rewrite HspR4) in "Hh16".
    iEval (rewrite HspR4) in "Hh8". iEval (rewrite HspR4) in "Hhfra".
    iEval (rewrite HspR4) in "Hhfs0".
    assert (Hpc10 : update_vec_dec (add_vec (R4 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                    = mword_of_int (RL + 0x10)).
    { rewrite HraR4. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc10) in "Hpc".
    (* +0x10 c.beqz a0 NOT taken (a0 = 1) *)
    iApply (wp_cbeqz_fall_s root_ppn E Φ (mword_of_int (RL + 0x10)) (mword_of_int 14) (Cregidx (mword_of_int 2)) (mword_of_int 10)
              mh mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hma0; vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi10 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    assert (Hpp12 : add_vec_int (mword_of_int (RL + 0x10) : mword 64) 2 = mword_of_int (RL + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* +0x12 sd zero,16(s1): lk->cpu := 0 *)
    assert (Hs1mh : mh !!! Regidx (mword_of_int 9 : mword 5) = lk0).
    { rewrite Hms1. rewrite /R4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3. rewrite lookup_total_insert.
      rewrite /R2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      apply aq_addv_zero_l. }
    assert (HAcpu : add_vec (mh !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 16 : mword 12)) = a_cpu)
      by (rewrite Hs1mh; reflexivity).
    iApply (wp_sd_zero_s root_ppn E Φ (mword_of_int (RL + 0x12)) (mword_of_int 9)
              (mword_of_int 16) mh cpuold mstatus0 mie_v mdv0 menvcfg0
              (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi12 [Hcpu] [-]").
    { iEval (rewrite HAcpu). iExact "Hcpu". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hcpu".
    iEval (rewrite HAcpu) in "Hcpu".
    assert (Hpp16 : add_vec_int (mword_of_int (RL + 0x12) : mword 64) 4 = mword_of_int (RL + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* +0x16 fence rw,w *)
    iApply (wp_fence_s root_ppn E Φ (mword_of_int (RL + 0x16)) mh
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 HFIOM 
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi16 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    assert (Hpp1a : add_vec_int (mword_of_int (RL + 0x16) : mword 64) 4 = mword_of_int (RL + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a sw zero,0(s1): the lock word clears, [locked γ ∗ R] re-enter the invariant *)
    assert (HAlk : add_vec (mh !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = lka)
      by (rewrite Hs1mh; exact Hlkeq).
    iApply (wp_sw_zero_lockinv root_ppn E Φ γ lka R (mword_of_int (RL + 0x1a)) (mword_of_int 9)
              (mword_of_int 0) mh mstatus0 mie_v mdv0 menvcfg0
              (dq:=DfracOwn 1)
              HN HNl HAlk HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi1a Hlock Htok HRes [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    assert (Hpp1e : add_vec_int (mword_of_int (RL + 0x1a) : mword 64) 4 = mword_of_int (RL + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e jal ra,pop_off *)
    iDestruct (kv_cfg_split γc mstatus0 mie_v mdv0 menvcfg0 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe HFIOM Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hgc Hmie Hmdl Hmenv")
      as "(Hsm & Hhs2 & Hpriv2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2)".
    iApply (wp_jal_gpr_s_zca root_ppn γc E Φ (mword_of_int (RL + 0x1e)) (mword_of_int 1 : mword 5) (mword_of_int 0x1fff9a : mword 21)
              mh (1/2)%Qp
              HN ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hsm Htlbinv Hpc Hfile Hi1e [-]").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iDestruct (kv_cfg_recombine γc mstatus0 mie_v mdv0 menvcfg0
                 with "Hsm Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2")
      as "(Hhs & Hpriv & Hms & Hgc & Hmie & Hmdl & Hmenv)".
    set (M1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (RL + 0x1e) : mword 64) 4)]> mh).
    assert (Htgtp : add_vec (mword_of_int (RL + 0x1e) : mword 64) (sign_extend' 64 (mword_of_int 0x1fff9a : mword 21)) = mword_of_int KernelSyms.pop_off)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtp) in "Hpc".
    (* ---- pop_off() ---- *)
    assert (HspM1 : M1 !!! Regidx csp_rs1 = spr).
    { rewrite /M1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hmsp. exact HspR4. }
    assert (HtpM1 : M1 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /M1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hmtp. exact HtpR4. }
    assert (HM1s2 : M1 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5)).
    { rewrite /M1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hms2. exact HR4s2. }
    assert (HM1s3 : M1 !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5)).
    { rewrite /M1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hms3. exact HR4s3. }
    assert (HM1s4 : M1 !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5)).
    { rewrite /M1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hms4. exact HR4s4. }
    assert (HM1s5 : M1 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5)).
    { rewrite /M1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hms5. exact HR4s5. }
    assert (HM1s6 : M1 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5)).
    { rewrite /M1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hms6. exact HR4s6. }
    assert (HM1s7 : M1 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5)).
    { rewrite /M1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hms7. exact HR4s7. }
    assert (HM1s8 : M1 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5)).
    { rewrite /M1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hms8. exact HR4s8. }
    assert (HM1s9 : M1 !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5)).
    { rewrite /M1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hms9. exact HR4s9. }
    assert (HM1s10 : M1 !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5)).
    { rewrite /M1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hms10. exact HR4s10. }
    assert (HM1s11 : M1 !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5)).
    { rewrite /M1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hms11. exact HR4s11. }
    assert (HraM1 : M1 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (RL + 0x1e) : mword 64) 4)
      by (rewrite /M1; apply lookup_total_insert).
    (* pop_off's frame slots coincide with (parts of) holding's dead frame *)
    assert (EQp8 : add_vec (add_vec spr (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = a_h24).
    { rewrite /a_h24 /spdh !po_addv_assoc. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (EQp0 : add_vec (add_vec spr (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = a_h16).
    { rewrite /a_h16 /spdh !po_addv_assoc. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (EQpfra : add_vec (add_vec (add_vec spr (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = a_h8).
    { rewrite /a_h8 /spdh !po_addv_assoc. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (EQpfs0 : add_vec (add_vec (add_vec spr (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = a_h0).
    { rewrite /a_h0 /spdh !po_addv_assoc. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iDestruct (smode_config_rebuild γc (DfracOwn 1) mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe HFIOM Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hgc Hmie Hmdl Hmenv") as "Hcfg".
    iApply (wp_pop_off_words root_ppn γc E Φ M1 noffv intenav
              w24 w16 w8 vh0 (dqi:=dqi)
              HN Hnoffpos Hint
              ltac:(rewrite HraM1; vm_compute; reflexivity)
              with "Hcfg Htlbinv Htext Hpc Hfile
                    [Hh24] [Hh16] [Hh8] [Hh0] [Hnoff] [Hint] [-]").
    { iEval (rewrite HspM1 EQp8). iExact "Hh24". }
    { iEval (rewrite HspM1 EQp0). iExact "Hh16". }
    { iEval (rewrite HspM1 EQpfra). iExact "Hh8". }
    { iEval (rewrite HspM1 EQpfs0). iExact "Hh0". }
    { iEval (rewrite HtpM1). iExact "Hnoff". }
    { iEval (rewrite HtpM1). iExact "Hint". }
    iIntros (mf) "Hcfg Htlbinv Hpc Hfile %Hmff Hnoff Hint Hjunk".
    clear mstatus0 mie_v mdv0 menvcfg0 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe HFIOM Hmenvval0.
    iDestruct (smode_config_unbundle γc (DfracOwn 1) with "Hcfg")
      as "(_ & _ & Hhs & Hpriv & Hmsb & Hmieb & Hmenvb)".
    iDestruct "Hmsb" as (mstatus0) "(Hms & Hgc & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %HFIOM & %Hmenvval0)".
    iEval (rewrite HtpM1) in "Hnoff". iEval (rewrite HtpM1) in "Hint".
    unfold callee_saved in Hmff.
    destruct Hmff as (Hfsp & Hftp & Hfs0 & Hfs1 & Hfs2 & Hfs3 & Hfs4 & Hfs5 & Hfs6 & Hfs7 & Hfs8 & Hfs9 & Hfs10 & Hfs11).
    iDestruct "Hjunk" as (u8 u0 ura us0) "(Hh24 & Hh16 & Hh8 & Hh0)".
    iEval (rewrite HspM1 EQp8) in "Hh24". iEval (rewrite HspM1 EQp0) in "Hh16".
    iEval (rewrite HspM1 EQpfra) in "Hh8". iEval (rewrite HspM1 EQpfs0) in "Hh0".
    assert (Hpc22 : update_vec_dec (add_vec (M1 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                    = mword_of_int (RL + 0x22)).
    { rewrite HraM1. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc22) in "Hpc".
    (* ---- epilogue ---- *)
    assert (HspMf : mf !!! Regidx csp_rs1 = spr) by (rewrite Hfsp; exact HspM1).
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (RL + 0x22)) (mword_of_int 3) (mword_of_int 1 : mword 5)
              mf (m !!! Regidx (mword_of_int 1 : mword 5))
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi22 [Hr24]").
    { iEval (rewrite HspMf). iExact "Hr24". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hr24".
    iEval (rewrite HspMf) in "Hr24".
    set (Q1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mf).
    assert (HspQ1 : Q1 !!! Regidx csp_rs1 = spr)
      by (rewrite /Q1; rewrite lookup_total_insert_ne; [ exact HspMf | vm_compute; discriminate ]).
    assert (Hpp24 : add_vec_int (mword_of_int (RL + 0x22) : mword 64) 2 = mword_of_int (RL + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (RL + 0x24)) (mword_of_int 2) (mword_of_int 8 : mword 5)
              Q1 (m !!! Regidx (mword_of_int 8 : mword 5))
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi24 [Hr16]").
    { iEval (rewrite HspQ1). iExact "Hr16". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hr16".
    iEval (rewrite HspQ1) in "Hr16".
    set (Q2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> Q1).
    assert (HspQ2 : Q2 !!! Regidx csp_rs1 = spr)
      by (rewrite /Q2; rewrite lookup_total_insert_ne; [ exact HspQ1 | vm_compute; discriminate ]).
    assert (Hpp26 : add_vec_int (mword_of_int (RL + 0x24) : mword 64) 2 = mword_of_int (RL + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (RL + 0x26)) (mword_of_int 1) (mword_of_int 9 : mword 5)
              Q2 (m !!! Regidx (mword_of_int 9 : mword 5))
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi26 [Hr8]").
    { iEval (rewrite HspQ2). iExact "Hr8". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hr8".
    iEval (rewrite HspQ2) in "Hr8".
    set (Q3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> Q2).
    assert (HspQ3 : Q3 !!! Regidx csp_rs1 = spr)
      by (rewrite /Q3; rewrite lookup_total_insert_ne; [ exact HspQ2 | vm_compute; discriminate ]).
    assert (Hpp28 : add_vec_int (mword_of_int (RL + 0x26) : mword 64) 2 = mword_of_int (RL + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    (* +0x28 c.addi16sp sp,32 *)
    iDestruct (kv_cfg_split γc mstatus0 mie_v mdv0 menvcfg0 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe HFIOM Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hgc Hmie Hmdl Hmenv")
      as "(Hsm & Hhs2 & Hpriv2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2)".
    iApply (wp_caddi16sp_gpr_s root_ppn γc E Φ (mword_of_int (RL + 0x28)) (mword_of_int 2 : mword 6) Q3
              (1/2)%Qp HN
              with "Hsm Htlbinv Hpc Hfile Hi28 [-]").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iDestruct (kv_cfg_recombine γc mstatus0 mie_v mdv0 menvcfg0
                 with "Hsm Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2")
      as "(Hhs & Hpriv & Hms & Hgc & Hmie & Hmdl & Hmenv)".
    set (Q4 := <[Regidx csp_rs1 := regval_into_reg (add_vec (Q3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q3).
    assert (Hpp2a : add_vec_int (mword_of_int (RL + 0x28) : mword 64) 2 = mword_of_int (RL + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2a) in "Hpc".
    (* +0x2a c.ret *)
    assert (HraQ4 : Q4 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /Q4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /Q1. apply lookup_total_insert. }
    iApply (wp_cret_s_zca root_ppn E Φ (mword_of_int (RL + 0x2a)) (mword_of_int 1) Q4
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 ltac:(vm_compute; discriminate) Hlpe
              ltac:(rewrite HraQ4; exact Hal0)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi2a [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iEval (rewrite HraQ4) in "Hpc".
    (* re-bundle the ambient config for the postcondition; return the SIE token *)
    iDestruct (smode_config_rebuild γc (DfracOwn 1) mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe HFIOM Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hgc Hmie Hmdl Hmenv") as "Hcfg".
    iApply ("Hcont" $! Q4 with "Hcfg Htoken Htlbinv Hpc Hfile [%] Hcpu Hnoff Hint
                          [Hr24 Hr16 Hr8 Hh24 Hh16 Hh8 Hh0 Hhfra Hhfs0]").
    { unfold callee_saved. repeat split.
      - (* sp *)
        rewrite /Q4. rewrite lookup_total_insert. rewrite HspQ3.
        rewrite /spr po_addv_assoc.
        replace (add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                         (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))
          with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
        apply kv_addv_zero.
      - (* tp *)
        rewrite /Q4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hftp. exact HtpM1.
      - (* s0 (x8) *)
        rewrite /Q4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q2. apply lookup_total_insert.
      - (* s1 (x9) *)
        rewrite /Q4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q3. apply lookup_total_insert.
      - (* s2 (x18) *)
        rewrite /Q4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hfs2. exact HM1s2.
      - (* s3 (x19) *)
        rewrite /Q4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hfs3. exact HM1s3.
      - (* s4 (x20) *)
        rewrite /Q4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hfs4. exact HM1s4.
      - (* s5 (x21) *)
        rewrite /Q4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hfs5. exact HM1s5.
      - (* s6 (x22) *)
        rewrite /Q4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hfs6. exact HM1s6.
      - (* s7 (x23) *)
        rewrite /Q4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hfs7. exact HM1s7.
      - (* s8 (x24) *)
        rewrite /Q4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hfs8. exact HM1s8.
      - (* s9 (x25) *)
        rewrite /Q4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hfs9. exact HM1s9.
      - (* s10 (x26) *)
        rewrite /Q4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hfs10. exact HM1s10.
      - (* s11 (x27) *)
        rewrite /Q4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hfs11. exact HM1s11.
    }
    iExists _, _, _, _, _, _, _, _, _.
    iFrame "Hr24 Hr16 Hr8 Hh24 Hh16 Hh8 Hh0 Hhfra Hhfs0".
  Qed.

  (* [stack_own] wrapper over [wp_release_words]: release's two save frames
     ([sp0-8..sp0-24] = its own r-slots, [sp0-40..sp0-80] = the pop_off/mycpu
     h-slots) plus the [sp0-32] gap between them form one contiguous
     [stack_own sp0 n] (n >= 10).  a_cpu (lock field) / a_noff / a_int
     (cpu struct) stay explicit.  release's post already existentialises all
     9 saved slots, so the whole region rebundles as [stack_own sp0 n]. *)
  Lemma wp_release (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (γ : gname) (γc : gname) (b : mword 1) (lka : mword 64) (R : iProp Σ)
      (m : gmap regidx (mword 64))
      (cpuold : mword 64) (noffv intenav : mword 32)
      (n : nat)
      {dqi : dfrac} :
    let pcE : mword 64 := mword_of_int RL in
    let sp0 := m !!! Regidx csp_rs1 in
    let lk0 := m !!! Regidx (mword_of_int 10 : mword 5) in
    let a_cpu := add_vec lk0 (sign_extend' 64 (mword_of_int 16 : mword 12)) in
    let cpuv := mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) in
    let a_noff := add_vec cpuv (sign_extend' 64 (mword_of_int 120 : mword 12)) in
    let a_int := add_vec cpuv (sign_extend' 64 (mword_of_int 124 : mword 12)) in
    let nv1 := sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 noffv) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0) in
    let storeval_noff := (autocast (T := mword) (subrange_vec_dec nv1 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    (10 ≤ n)%nat ->
    ↑minstretN ⊆ E ->
    ↑lockN ⊆ E ->
    add_vec lk0 (sign_extend' 64 (mword_of_int 0 : mword 12)) = lka ->
    eq_vec cpuold cpuv = true ->
    zopz0zKzJ_s zero_reg (sign_extend' 64 noffv) = false ->
    eq_vec (sign_extend' 64 intenav) zero_reg = true ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    smode_config γc (DfracOwn 1) -∗
    ghost_var γc (1/2) b -∗
    tlb_inv root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m -∗
    is_lock γ lka R -∗
    locked γ -∗
    R -∗
    a_cpu ↦₈ cpuold -∗
    a_noff ↦₄ noffv -∗
    a_int ↦₄{ dqi } intenav -∗
    stack_own sp0 n -∗
    ( ∀ mr,
      smode_config γc (DfracOwn 1) -∗
      ghost_var γc (1/2) b -∗
      tlb_inv root_ppn -∗
      pc_is ret_tgt -∗
      gpr_file mr -∗
      ⌜ callee_saved m mr ⌝ -∗
      a_cpu ↦₈ (zero_reg : mword 64) -∗
      a_noff ↦₄ storeval_noff -∗
      a_int ↦₄{ dqi } intenav -∗
      stack_own sp0 n -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros pcE sp0 lk0 a_cpu cpuv a_noff a_int nv1 storeval_noff ret_tgt
      Hn HN HNl Hlkeq Hmine Hnoffpos Hint Hal0.
    iIntros "Hcfg Htoken Htlbinv #Htext Hpc Hfile #Hlock Htok HRes Hcpu Hnoff Hint Hstk Hcont".
    (* peel the top 10 slots, frame the deeper region *)
    iDestruct (stack_own_split_1 sp0 10 n ltac:(lia) with "Hstk") as "[Htop Hdeep]".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Htop".
    iDestruct "Htop" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & _)".
    iDestruct "S1" as (vr24) "Hr24".   iDestruct "S2" as (vr16) "Hr16".
    iDestruct "S3" as (vr8) "Hr8".     iDestruct "S4" as (vgap) "Hgap".
    iDestruct "S5" as (vh24) "Hh24".   iDestruct "S6" as (vh16) "Hh16".
    iDestruct "S7" as (vh8) "Hh8".     iDestruct "S8" as (vh0) "Hh0".
    iDestruct "S9" as (vhra) "Hhfra".  iDestruct "S10" as (vhs0) "Hhfs0".
    (* bridges: clean [pa_stk sp0 k] = raw slot spelling [wp_release_words] uses *)
    assert (Hb1 : add_vec (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec (add_vec (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec (add_vec (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb7 : add_vec (add_vec (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 7).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb8 : add_vec (add_vec (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 8).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb9 : add_vec (add_vec (add_vec (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 9).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb10 : add_vec (add_vec (add_vec (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 10).
    { unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hr24".  iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".   iEval (rewrite -Hb5) in "Hh24".
    iEval (rewrite -Hb6) in "Hh16".  iEval (rewrite -Hb7) in "Hh8".
    iEval (rewrite -Hb8) in "Hh0".   iEval (rewrite -Hb9) in "Hhfra".
    iEval (rewrite -Hb10) in "Hhfs0".
    iApply (wp_release_words root_ppn E Φ γ γc b lka R m cpuold noffv intenav
              vr24 vr16 vr8 vh24 vh16 vh8 vh0 vhra vhs0 (dqi:=dqi)
              HN HNl Hlkeq Hmine Hnoffpos Hint Hal0
              with "Hcfg Htoken Htlbinv Htext Hpc Hfile Hlock Htok HRes Hcpu Hnoff Hint [Hr24] [Hr16] [Hr8] [Hh24] [Hh16] [Hh8] [Hh0] [Hhfra] [Hhfs0] [-]").
    { iExact "Hr24". } { iExact "Hr16". } { iExact "Hr8". }
    { iExact "Hh24". } { iExact "Hh16". } { iExact "Hh8". } { iExact "Hh0". }
    { iExact "Hhfra". } { iExact "Hhfs0". }
    iIntros (mr) "Hcfg Htoken Htlbinv Hpc Hmr %Hcs Hcpu Hnoff Hint Hblk".
    iDestruct "Hblk" as (u1 u2 u3 u4 u5 u6 u7 u8 u9) "(Hr24 & Hr16 & Hr8 & Hh24 & Hh16 & Hh8 & Hh0 & Hhfra & Hhfs0)".
    iEval (rewrite Hb1) in "Hr24".  iEval (rewrite Hb2) in "Hr16".
    iEval (rewrite Hb3) in "Hr8".   iEval (rewrite Hb5) in "Hh24".
    iEval (rewrite Hb6) in "Hh16".  iEval (rewrite Hb7) in "Hh8".
    iEval (rewrite Hb8) in "Hh0".   iEval (rewrite Hb9) in "Hhfra".
    iEval (rewrite Hb10) in "Hhfs0".
    iAssert (stack_own sp0 10) with "[Hr24 Hr16 Hr8 Hgap Hh24 Hh16 Hh8 Hh0 Hhfra Hhfs0]" as "Htop".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24"; [by iExists _|]. iSplitL "Hr16"; [by iExists _|].
      iSplitL "Hr8"; [by iExists _|].  iSplitL "Hgap"; [by iExists _|].
      iSplitL "Hh24"; [by iExists _|]. iSplitL "Hh16"; [by iExists _|].
      iSplitL "Hh8"; [by iExists _|].  iSplitL "Hh0"; [by iExists _|].
      iSplitL "Hhfra"; [by iExists _|]. iSplitL "Hhfs0"; [by iExists _|]. done. }
    iDestruct (stack_own_split_2 sp0 10 n ltac:(lia) with "[$Htop $Hdeep]") as "Hstk".
    iApply ("Hcont" $! mr with "Hcfg Htoken Htlbinv Hpc Hmr [%] Hcpu Hnoff Hint Hstk").
    exact Hcs.
  Qed.

End WpReleaseTop.
