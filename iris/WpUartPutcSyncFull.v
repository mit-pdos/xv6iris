(* WpUartPutcSyncFull.v -- the prologue/epilogue frame handling for
   uartputc_sync, on top of the body [wp_uartputc_body] (WpUartPutcSync.v),
   assembled into the whole-function WP [wp_uartputc].

   The prologue's three stack STORES (c.sdsp) and the epilogue's three stack
   LOADS (c.ldsp) have only [_scfg] (smode_config) leaves, so they are run
   through the VCgen (VcGenS.v) as [vop_s] blocks -- exactly as WpMycpu.v runs
   its prologue/epilogue.  The three instructions that are neither ordinary
   value-ALU ops nor stack-slot VCgen ops are handled by dedicated [_scfg]
   leaves (each threads the same [smode_config] bundle):
     - c.mv  s1,a0     (0x96c) : [wp_cmv_gpr_s_config_scfg] (WpSmodeRtype)
     - c.addi16sp sp,32 (0x9ae): [wp_caddi16sp_gpr_s]       (WpSmodeGpr; +32
       is out of c.addi's range so it cannot be folded into the VCgen block)
     - c.ret           (0x9b0) : [wp_cret_s_zca_scfg]       (WpSmodeJalr) *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes DevModel.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import MinstretInv InstrBytes.
Require Import WpRvcBridge KernelText StackOwn.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import WpMmodeLeafBase.
Require Import WpSmodeRtype WpSmodeJalr WpSmodeGpr.
Require Import WpMemsetInstr KernelRvcDecode.
Require Import VcGen VcGenS.
Require Import CalleeSaved.
Require Import WpUart.
Require Import WpUartPutcSync.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Import Defs.

Notation UPS := KernelSyms.uartputc_sync.

(* ===================================================================== *)
(*  Decode facts for the three "structural" RVC instructions that are not  *)
(*  in the device-core / panic-check set.  (c.ret reuses [mdec_cf0].)      *)
(* ===================================================================== *)

(* 0x96c  84aa  c.mv s1,a0 *)
Lemma uprvc_84aa s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x84aa : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 9), Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x9ae  6105  c.addi16sp sp,32 *)
Lemma uprvc_6105 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6105 : mword 16)) s
  = Some (C_ADDI16SP (mword_of_int 2), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* The prologue's [c.addi sp,-32] then the epilogue's [c.addi16sp sp,32]
   restore sp exactly.  Proved abstractly in [X] (mirror of [mycpu_frame_cancel]);
   the only [vm_compute]s are on the two CONCRETE 64-bit offsets, never on the
   symbolic base [X] -- keeping this out of the whole-function proof's final
   goal (where [X] would be an opaque [gpr_file] lookup and [vm_compute] over it
   diverges). *)
Lemma ups_frame_cancel (X : mword 64) :
  add_vec (add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
          (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = X.
Proof.
  assert (add_vec_unsigned : forall x y : mword 64,
            bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y)).
  { intros x y. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned. reflexivity. }
  apply bv_eq. rewrite !add_vec_unsigned. rewrite bv_wrap_add_idemp_l.
  assert (HA : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)) : mword 64)
             = 18446744073709551584) by (vm_compute; reflexivity).
  assert (HB : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)) : mword 64)
             = 32) by (vm_compute; reflexivity).
  rewrite HA HB. rewrite <- Z.add_assoc.
  replace (18446744073709551584 + 32) with (bv_modulus 64) by (vm_compute; reflexivity).
  rewrite bv_wrap_add_modulus_1. apply bv_wrap_bv_unsigned.
Qed.

Section WpUartPutcSyncFull.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{!uartGhostG Σ}.
  Context `{CID : CpuId}.

  (* [instr]-builder templates, copied verbatim from WpUartPutcSync.v. *)
  (* --- [instr] facts for the three structural RVC instructions --- *)
  Lemma upi_0a : kernel_text -∗ instr (mword_of_int (UPS + 0x0a) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (UPS + 0x0a)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (UPS + 0x0a) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) uprvc_84aa exec_execute_C_MV. Qed.

  Lemma upi_4c : kernel_text -∗ instr (mword_of_int (UPS + 0x4c) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2), sp, sp, ADDI)).
  Proof. mk_rvc (UPS + 0x4c)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (UPS + 0x4c) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2), sp, sp, ADDI)) uprvc_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma upi_4e : kernel_text -∗ instr (mword_of_int (UPS + 0x4e) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (UPS + 0x4e)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (UPS + 0x4e) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) mdec_cf0 exec_execute_C_JR. Qed.

  (* --- prologue frame [instr] facts (0x00 c.addi · 0x02/04/06 sd · 0x08 addi4spn) --- *)
  Lemma upi_00 : kernel_text -∗ instr (mword_of_int (UPS + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (UPS + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (UPS + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) podec_00 exec_execute_C_ADDI. Qed.

  Lemma upi_02 : kernel_text -∗ instr (mword_of_int (UPS + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (UPS + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (UPS + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) podec_02 exec_execute_C_SDSP. Qed.

  Lemma upi_04 : kernel_text -∗ instr (mword_of_int (UPS + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (UPS + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (UPS + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) podec_04 exec_execute_C_SDSP. Qed.

  Lemma upi_06 : kernel_text -∗ instr (mword_of_int (UPS + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (UPS + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (UPS + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) podec_06 exec_execute_C_SDSP. Qed.

  Lemma upi_08 : kernel_text -∗ instr (mword_of_int (UPS + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (UPS + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (UPS + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) podec_08 exec_execute_C_ADDI4SPN. Qed.

  (* --- epilogue frame [instr] facts (0x46/48/4a ld) --- *)
  Lemma upi_46 : kernel_text -∗ instr (mword_of_int (UPS + 0x46) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (UPS + 0x46)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (UPS + 0x46) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) podec_22 exec_execute_C_LDSP. Qed.

  Lemma upi_48 : kernel_text -∗ instr (mword_of_int (UPS + 0x48) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (UPS + 0x48)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (UPS + 0x48) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) podec_24 exec_execute_C_LDSP. Qed.

  Lemma upi_4a : kernel_text -∗ instr (mword_of_int (UPS + 0x4a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (UPS + 0x4a)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (UPS + 0x4a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) podec_26 exec_execute_C_LDSP. Qed.

  (* ===================================================================== *)
  (*  Local three-slot frame elim/intro (the library ships only the         *)
  (*  one- and two-slot forms; building them here avoids re-staling the      *)
  (*  whole WP stack by editing StackOwn.v).                                 *)
  (* ===================================================================== *)
  Lemma stack_own_3_elim (sp0 : Arch.pa) :
    stack_own sp0 3 ⊢ ∃ w1 w2 w3 : bv 64,
      word_pointsto (pa_stk sp0 1) (DfracOwn 1) w1 ∗
      word_pointsto (pa_stk sp0 2) (DfracOwn 1) w2 ∗
      word_pointsto (pa_stk sp0 3) (DfracOwn 1) w3.
  Proof.
    rewrite (stack_own_app sp0 1 2) stack_own_1.
    iIntros "[H1 H23]". iDestruct "H1" as (w1) "H1".
    iDestruct (stack_own_2_elim with "H23") as (w2 w3) "[H2 H3]".
    rewrite (pa_stk_assoc sp0 1 1) (pa_stk_assoc sp0 1 2).
    iExists w1, w2, w3. iFrame.
  Qed.

  Lemma stack_own_3_intro (sp0 : Arch.pa) (w1 w2 w3 : bv 64) :
    word_pointsto (pa_stk sp0 1) (DfracOwn 1) w1 -∗
    word_pointsto (pa_stk sp0 2) (DfracOwn 1) w2 -∗
    word_pointsto (pa_stk sp0 3) (DfracOwn 1) w3 -∗
    stack_own sp0 3.
  Proof.
    iIntros "H1 H2 H3". rewrite (stack_own_app sp0 1 2). iSplitL "H1".
    - by iApply stack_own_1_intro.
    - rewrite -(pa_stk_assoc sp0 1 1) -(pa_stk_assoc sp0 1 2).
      iApply (stack_own_2_intro with "H2 H3").
  Qed.

  Local Open Scope Z_scope.

  (* ------------------------------------------------------------------- *)
  (* Prologue 0x962..0x96a as a VCgen block (the c.mv s1,a0 at 0x96c is    *)
  (* NOT a vop_s -- handled by [wp_cmv_gpr_s_config] after the block):     *)
  (*   c.addi  sp,-32   ·  sd ra,24(sp) · sd s0,16(sp) · sd s1,8(sp)       *)
  (*   · c.addi4spn s0,sp,32                                                *)
  (* ------------------------------------------------------------------- *)
  Definition ups_prologue : list vop_s :=
    [ VScaddi (mword_of_int 32) csp_rs1;                                  (* c.addi sp,-32   *)
      VScsdsp (mword_of_int 3) (mword_of_int 1);                          (* sd ra,24(sp)    *)
      VScsdsp (mword_of_int 2) (mword_of_int 8);                          (* sd s0,16(sp)    *)
      VScsdsp (mword_of_int 1) (mword_of_int 9);                          (* sd s1,8(sp)     *)
      VScaddi4spn (Cregidx (mword_of_int 0)) (mword_of_int 8)
                  (mword_of_int 8) ].                                     (* addi s0,sp,32   *)

  (* the three saved slots, at OLD-sp -8 / -16 / -24 (= NEW-sp +24/+16/+8) *)
  Definition ups_pro_heap0 : list (sval * sval) :=
    [ (SX 2 (wrap64 (-8)),  SX 33 0);
      (SX 2 (wrap64 (-16)), SX 34 0);
      (SX 2 (wrap64 (-24)), SX 35 0) ].
  Definition ups_pro_heap1 : list (sval * sval) :=
    [ (SX 2 (wrap64 (-8)),  SX 1 0);
      (SX 2 (wrap64 (-16)), SX 8 0);
      (SX 2 (wrap64 (-24)), SX 9 0) ].
  Definition ups_pro_regs1 : gmap regidx sval :=
    <[Regidx (mword_of_int 8 : mword 5) := SX 2 0]>
      (<[Regidx csp_rs1 := SX 2 (wrap64 (-32))]> vregs_init).

  Lemma ups_prologue_run :
    vc_block_s (VSt UPS vregs_init ups_pro_heap0 []) ups_prologue
    = Some (VSt (UPS + 10) ups_pro_regs1 ups_pro_heap1 []).
  Proof. vm_compute. reflexivity. Qed.

  (* ------------------------------------------------------------------- *)
  (* Epilogue 0x9a8..0x9ac as a VCgen block (the c.addi16sp sp,32 at 0x9ae *)
  (* is NOT a vop_s -- +32 exceeds c.addi's range; the ret at 0x9b0 is a    *)
  (* leaf too):  ld ra,24(sp) · ld s0,16(sp) · ld s1,8(sp)                  *)
  (* ------------------------------------------------------------------- *)
  Definition ups_epilogue : list vop_s :=
    [ VScldsp (mword_of_int 3) (mword_of_int 1);                          (* ld ra,24(sp)    *)
      VScldsp (mword_of_int 2) (mword_of_int 8);                          (* ld s0,16(sp)    *)
      VScldsp (mword_of_int 1) (mword_of_int 9) ].                        (* ld s1,8(sp)     *)

  (* the epilogue runs with sp already decremented; the slots sit at
     CURRENT-sp +24/+16/+8. *)
  Definition ups_epi_heap : list (sval * sval) :=
    [ (SX 2 24, SX 33 0);
      (SX 2 16, SX 34 0);
      (SX 2 8,  SX 35 0) ].
  Definition ups_epi_regs1 : gmap regidx sval :=
    <[Regidx (mword_of_int 9 : mword 5) := SX 35 0]>
      (<[Regidx (mword_of_int 8 : mword 5) := SX 34 0]>
         (<[Regidx (mword_of_int 1 : mword 5) := SX 33 0]> vregs_init)).

  Lemma ups_epilogue_run :
    vc_block_s (VSt (UPS + 0x46) vregs_init ups_epi_heap []) ups_epilogue
    = Some (VSt (UPS + 0x46 + 6) ups_epi_regs1 ups_epi_heap []).
  Proof. vm_compute. reflexivity. Qed.

  (* the prologue's / epilogue's block_instrs, from kernel_text. *)
  Lemma ups_prologue_instrs :
    kernel_text -∗ block_instrs_s UPS ups_prologue.
  Proof.
    iIntros "#Ht". cbn [block_instrs_s ups_prologue vop_s_ast].
    replace (UPS + 2 + 2) with (UPS + 4) by lia.
    replace (UPS + 4 + 2) with (UPS + 6) by lia.
    replace (UPS + 6 + 2) with (UPS + 8) by lia.
    iSplitR; [by iApply upi_00|].
    iSplitR; [by iApply upi_02|].
    iSplitR; [by iApply upi_04|].
    iSplitR; [by iApply upi_06|].
    iSplitR.
    { assert (Hcreg : creg2reg_idx (Cregidx (mword_of_int 0 : mword 3))
                      = Regidx (mword_of_int 8 : mword 5))
        by (vm_compute; reflexivity).
      rewrite -Hcreg. by iApply upi_08. }
    done.
  Qed.

  Lemma ups_epilogue_instrs :
    kernel_text -∗ block_instrs_s (UPS + 0x46) ups_epilogue.
  Proof.
    iIntros "#Ht". cbn [block_instrs_s ups_epilogue vop_s_ast].
    replace (UPS + 0x46 + 2) with (UPS + 0x48) by lia.
    replace (UPS + 0x48 + 2) with (UPS + 0x4a) by lia.
    iSplitR; [by iApply upi_46|].
    iSplitR; [by iApply upi_48|].
    iSplitR; [by iApply upi_4a|].
    done.
  Qed.

  (* =================================================================== *)
  (*  THE CAPSTONE: a WP for the ENTIRE uartputc_sync, entry (0x80000962)  *)
  (*  through its return to the caller (PC = ra with the low bit cleared). *)
  (*  Registers: ra=x1 sp=x2 s0=x8 s1=x9 a0=x10.  The panic path taken is   *)
  (*  panicking != 0 && panicked == 0 (so no push_off/pop_off, no infinite  *)
  (*  spin); the UART is THRE-ready so the wait loop exits immediately and   *)
  (*  the low byte of the char [a0] is written to THR.                      *)
  (*  On exit every callee-saved register holds its entry value             *)
  (*  ([callee_saved m0 mf]: sp/tp/s0/s1/s2..s11 -- sp/s0/s1 by way of the   *)
  (*  32-byte stack frame, the rest because nothing on the path writes       *)
  (*  them), and so does ra, which the frame also saves and restores.        *)
  (* =================================================================== *)
  (* [gpr_matches] from the [vregs_den] equality (the block runner's entry
     interface wants the former; my ρ setup proves the latter). *)
  Lemma gpr_matches_of_den (ρ : nat -> mword 64) (vr : gmap regidx sval)
      (m : gmap regidx (mword 64)) :
    vregs_den ρ vr = m -> gpr_matches ρ vr m.
  Proof.
    intros <- r sv Hr. unfold vregs_den.
    rewrite lookup_total_alt lookup_fmap Hr. reflexivity.
  Qed.

  Lemma wp_uartputc (root_ppn : mword 44) (γ : gname) (γd : uart_names)
      (Φ : mval -> iProp Σ)
      (m0 : gmap regidx (mword 64)) (n : nat) (q : Qp)
      (l : list (bv 8)) (pv pkv : mword 32)
      {dqm dqm2 : dfrac} :
    let ra_idx : mword 5 := mword_of_int 1 in
    let a0_idx : mword 5 := mword_of_int 10 in
    let pcE := mword_of_int UPS in
    let sp0 := m0 !!! Regidx csp_rs1 in
    let ra0 := m0 !!! Regidx ra_idx in
    let a00 := m0 !!! Regidx a0_idx in
    let ret_tgt := update_vec_dec (add_vec ra0 (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    (* the byte written to THR: the low 8 bits of the char in a0 *)
    let sb : mword 8 := autocast (T := mword)
       (subrange_vec_dec (and_vec (add_vec zero_reg a00)
          (sign_extend' 64 (mword_of_int 255 : mword 12))) 7 0) in
    (3 ≤ n)%nat ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    smode_config γ (DfracOwn q) -∗
    tlb_inv root_ppn -∗ kernel_text -∗
    pc_is pcE -∗ gpr_file m0 -∗
    stack_own sp0 n -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    dev_inv γd -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
    ( ∀ mf,
      smode_config γ (DfracOwn q) -∗
      tlb_inv root_ppn -∗
      pc_is ret_tgt -∗
      gpr_file mf -∗
      ⌜ callee_saved m0 mf /\ mf !!! Regidx ra_idx = ra0 ⌝ -∗
      stack_own sp0 n -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_tx_own γd (l ++ [sb]) -∗ uart_sent γd (l ++ [sb]) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros ra_idx a0_idx pcE sp0 ra0 a00 ret_tgt sb.
    intros Hn3 Hal0 Hpv Hpkv.
    (* Frame geometry and the two saved s-registers: proof-local, since the
       statement itself no longer mentions them. *)
    pose (s0_idx := (mword_of_int 8 : mword 5)).
    pose (s1_idx := (mword_of_int 9 : mword 5)).
    pose (sp' := add_vec (m0 !!! Regidx csp_rs1)
                   (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    pose (s00 := m0 !!! Regidx s0_idx).
    pose (s10 := m0 !!! Regidx s1_idx).
    set (ea_ra := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    set (ea_s0 := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    set (ea_s1 := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    iIntros "Hsm Htlbinv #Htext Hpc Hfile Hstk Hpk Hpkd #Hdinv Hown #Hoff Hcont".
    (* peel the three-slot frame off the abstract stack ownership. *)
    iDestruct (stack_own_split_1 sp0 3 n ltac:(lia) with "Hstk") as "[Htop Hdeep]".
    iDestruct (stack_own_3_elim with "Htop") as (raold s0old s1old) "(Hbra & Hbs0 & Hbs1)".
    (* the three slots sit at the raw SP-relative addresses the stores use. *)
    assert (Hpra : ea_ra = pa_stk sp0 1).
    { unfold ea_ra, sp', sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; apply bv_eq; vm_compute; reflexivity. }
    assert (Hps0 : ea_s0 = pa_stk sp0 2).
    { unfold ea_s0, sp', sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; apply bv_eq; vm_compute; reflexivity. }
    assert (Hps1 : ea_s1 = pa_stk sp0 3).
    { unfold ea_s1, sp', sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpra) in "Hbra".
    iEval (rewrite -Hps0) in "Hbs0".
    iEval (rewrite -Hps1) in "Hbs1".
    assert (Hcsp2 : Regidx (mword_of_int 2 : mword 5) = Regidx csp_rs1)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    (* ------------------------------------------------------------------ *)
    (* SEAM 1: run the prologue block (smode_config threaded as one bundle).*)
    (* ------------------------------------------------------------------ *)
    iDestruct (gpr_file_dom with "Hfile") as "[%Hdom0 Hfile]".
    iDestruct (gpr_file_x0 m0 (mword_of_int 0) ltac:(vm_compute; reflexivity)
                 with "Hfile") as "[%Hx00 Hfile]".
    set (ρA := fun k : nat =>
           if (k <? 32)%nat
           then m0 !!! Regidx (mword_of_int (Z.of_nat k) : mword 5)
           else if Nat.eqb k 33 then (raold : mword 64)
                else if Nat.eqb k 34 then (s0old : mword 64)
                else (s1old : mword 64)).
    assert (HdenA : vregs_den ρA vregs_init = m0).
    { apply (vregs_den_init_agree _ _ Hdom0 Hx00). intros k Hk.
      unfold ρA. rewrite (proj2 (Nat.ltb_lt k 32) Hk). reflexivity. }
    assert (HmA : gpr_matches ρA vregs_init m0) by (apply gpr_matches_of_den; exact HdenA).
    (* the three block cells ARE the three stack words *)
    assert (Hara : sval_den ρA (SX 2 (wrap64 (-8))) = ea_ra).
    { cbn [sval_den].
      replace (ρA 2%nat) with (m0 !!! Regidx (mword_of_int 2 : mword 5))
        by (unfold ρA; reflexivity).
      rewrite Hcsp2. unfold ea_ra, sp'. rewrite add_vec_off2.
      f_equal; f_equal; vm_compute; reflexivity. }
    assert (Has0 : sval_den ρA (SX 2 (wrap64 (-16))) = ea_s0).
    { cbn [sval_den].
      replace (ρA 2%nat) with (m0 !!! Regidx (mword_of_int 2 : mword 5))
        by (unfold ρA; reflexivity).
      rewrite Hcsp2. unfold ea_s0, sp'. rewrite add_vec_off2.
      f_equal; f_equal; vm_compute; reflexivity. }
    assert (Has1 : sval_den ρA (SX 2 (wrap64 (-24))) = ea_s1).
    { cbn [sval_den].
      replace (ρA 2%nat) with (m0 !!! Regidx (mword_of_int 2 : mword 5))
        by (unfold ρA; reflexivity).
      rewrite Hcsp2. unfold ea_s1, sp'. rewrite add_vec_off2.
      f_equal; f_equal; vm_compute; reflexivity. }
    assert (Hvra : sval_den ρA (SX 33 0) = (raold : mword 64)).
    { rewrite sval_den_SX0. unfold ρA. reflexivity. }
    assert (Hvs0 : sval_den ρA (SX 34 0) = (s0old : mword 64)).
    { rewrite sval_den_SX0. unfold ρA. reflexivity. }
    assert (Hvs1 : sval_den ρA (SX 35 0) = (s1old : mword 64)).
    { rewrite sval_den_SX0. unfold ρA. reflexivity. }
    iDestruct (ups_prologue_instrs with "Htext") as "Hbi".
    iApply (wp_vc_block_s root_ppn ups_prologue Φ
              (VSt UPS vregs_init ups_pro_heap0 [])
              (VSt (UPS + 10) ups_pro_regs1 ups_pro_heap1 [])
              ρA m0 γ (dq:=DfracOwn q)
 ups_prologue_run HmA
              with "Hsm Htlbinv Hpc Hfile Hbi [Hbra Hbs0 Hbs1] []").
    { rewrite /vheap_own. cbn [vheap]. rewrite /ups_pro_heap0.
      cbn [big_opL fst snd]. rewrite Hara Has0 Has1 Hvra Hvs0 Hvs1.
      iFrame "Hbra Hbs0 Hbs1". }
    { rewrite /vheap4_own. cbn [vheap4]. done. }
    iIntros (M1) "%HmM1 Hsm Htlbinv Hpc Hfile Hheap _".
    (* keep [agree_off]: it pins every register the prologue does not write. *)
    destruct HmM1 as [HmM1 HaoM1].
    (* the stored words: den (SX 1 0) = ra0, (SX 8 0) = s00, (SX 9 0) = s10 *)
    assert (Hvra0 : sval_den ρA (SX 1 0) = ra0).
    { rewrite sval_den_SX0. unfold ρA. reflexivity. }
    assert (Hvs00 : sval_den ρA (SX 8 0) = s00).
    { rewrite sval_den_SX0. unfold ρA. reflexivity. }
    assert (Hvs10 : sval_den ρA (SX 9 0) = s10).
    { rewrite sval_den_SX0. unfold ρA. reflexivity. }
    iEval (rewrite /vheap_own; cbn [vheap]; rewrite /ups_pro_heap1;
           cbn [big_opL fst snd];
           rewrite Hara Has0 Has1 Hvra0 Hvs00 Hvs10) in "Hheap".
    iDestruct "Hheap" as "(Hbra & Hbs0 & Hbs1 & _)".
    iEval (cbn [vpc]) in "Hpc".
    (* read off the post-block registers I need downstream (sp, a0). *)
    assert (HspM1 : M1 !!! Regidx csp_rs1 = sp').
    { assert (Hl : ups_pro_regs1 !! Regidx csp_rs1 = Some (SX 2 (wrap64 (-32))))
        by (vm_compute; reflexivity).
      rewrite (HmM1 _ _ Hl). cbn [sval_den].
      replace (ρA 2%nat) with (m0 !!! Regidx (mword_of_int 2 : mword 5))
        by (unfold ρA; reflexivity).
      rewrite Hcsp2. unfold sp'. f_equal; apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0M1 : M1 !!! Regidx a0_idx = a00).
    { assert (Hl : ups_pro_regs1 !! Regidx a0_idx = Some (SX 10 0))
        by (vm_compute; reflexivity).
      rewrite (HmM1 _ _ Hl) sval_den_SX0. unfold ρA, a00, a0_idx. reflexivity. }
    (* ------------------------------------------------------------------ *)
    (* c.mv s1,a0 at 0x96c: s1 := a0.                                       *)
    (* ------------------------------------------------------------------ *)
    iPoseProof (upi_0a with "Htext") as "Hi0a".
    iApply (wp_cmv_gpr_s_config_scfg root_ppn γ Φ (mword_of_int (UPS + 0x0a)) s1_idx a0_idx M1
              (dq:=DfracOwn q)
 ltac:(vm_compute; discriminate)
              with "Hsm Htlbinv Hpc Hfile Hi0a [-]").
    iIntros "Hsm Htlbinv Hpc Hfile".
    (* ------------------------------------------------------------------ *)
    (* the body (0x96e -> 0x9a8) via [wp_uartputc_body].                    *)
    (* ------------------------------------------------------------------ *)
    assert (Hpc0c : add_vec_int (mword_of_int (UPS + 0x0a)) 2
                    = (mword_of_int (UPS + 0x0c) : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    set (m3 := <[Regidx s1_idx := regval_into_reg (add_vec zero_reg (M1 !!! Regidx a0_idx))]> M1).
    assert (HR9m3 : m3 !!! Regidx (mword_of_int 9) = add_vec zero_reg a00).
    { unfold m3. change (Regidx s1_idx) with (Regidx (mword_of_int 9)).
      rewrite lookup_total_insert. unfold regval_into_reg. rewrite Ha0M1. reflexivity. }
    (* the body's store byte is about m3!!!s1 = add_vec zero_reg a00 = our sb *)
    assert (Hsbm3 : (autocast (T := mword)
                      (subrange_vec_dec (and_vec (m3 !!! Regidx (mword_of_int 9))
                         (sign_extend' 64 (mword_of_int 255 : mword 12))) 7 0) : mword 8) = sb).
    { unfold sb. rewrite HR9m3. reflexivity. }
    iApply (wp_uartputc_body root_ppn γ γd Φ m3 l pv pkv
              (dq:=DfracOwn q) (dqm:=dqm) (dqm2:=dqm2)
 Hpv Hpkv
              with "Hsm Htlbinv Htext Hpc Hfile Hpk Hpkd Hdinv Hown Hoff").
    iIntros (mf) "Hsm Htlbinv Hpc Hfile %Hcs_body Hpk Hpkd Hown Hsent".
    iEval (rewrite Hsbm3) in "Hown". iEval (rewrite Hsbm3) in "Hsent".
    destruct Hcs_body as (B2 & B4 & B8 & B9 & B18 & B19 & B20 & B21
                          & B22 & B23 & B24 & B25 & B26 & B27).
    (* [mf]'s sp agrees with the body input (== sp'). *)
    assert (Hmf_sp : mf !!! Regidx (mword_of_int 2) = sp').
    { change (Regidx (mword_of_int 2)) with (Regidx csp_rs1).
      rewrite B2. unfold m3.
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HspM1. }
    (* ------------------------------------------------------------------ *)
    (* SEAM 2: run the epilogue load block from [mf].                       *)
    (* ------------------------------------------------------------------ *)
    iDestruct (gpr_file_dom with "Hfile") as "[%Hdomf Hfile]".
    iDestruct (gpr_file_x0 mf (mword_of_int 0) ltac:(vm_compute; reflexivity)
                 with "Hfile") as "[%Hxf0 Hfile]".
    set (ρB := fun k : nat =>
           if (k <? 32)%nat
           then mf !!! Regidx (mword_of_int (Z.of_nat k) : mword 5)
           else if Nat.eqb k 33 then ra0
                else if Nat.eqb k 34 then s00 else s10).
    assert (HdenB : vregs_den ρB vregs_init = mf).
    { apply (vregs_den_init_agree _ _ Hdomf Hxf0). intros k Hk.
      unfold ρB. rewrite (proj2 (Nat.ltb_lt k 32) Hk). reflexivity. }
    assert (HmB : gpr_matches ρB vregs_init mf) by (apply gpr_matches_of_den; exact HdenB).
    assert (HspB : ρB 2%nat = sp').
    { replace (ρB 2%nat) with (mf !!! Regidx (mword_of_int 2 : mword 5))
        by (unfold ρB; reflexivity). exact Hmf_sp. }
    assert (HaraB : sval_den ρB (SX 2 24) = ea_ra).
    { cbn [sval_den]. rewrite HspB. unfold ea_ra.
      f_equal; apply bv_eq; vm_compute; reflexivity. }
    assert (Has0B : sval_den ρB (SX 2 16) = ea_s0).
    { cbn [sval_den]. rewrite HspB. unfold ea_s0.
      f_equal; apply bv_eq; vm_compute; reflexivity. }
    assert (Has1B : sval_den ρB (SX 2 8) = ea_s1).
    { cbn [sval_den]. rewrite HspB. unfold ea_s1.
      f_equal; apply bv_eq; vm_compute; reflexivity. }
    assert (HvraB : sval_den ρB (SX 33 0) = ra0).
    { rewrite sval_den_SX0. unfold ρB. reflexivity. }
    assert (Hvs0B : sval_den ρB (SX 34 0) = s00).
    { rewrite sval_den_SX0. unfold ρB. reflexivity. }
    assert (Hvs1B : sval_den ρB (SX 35 0) = s10).
    { rewrite sval_den_SX0. unfold ρB. reflexivity. }
    iDestruct (ups_epilogue_instrs with "Htext") as "Hbi2".
    iApply (wp_vc_block_s root_ppn ups_epilogue Φ
              (VSt (UPS + 0x46) vregs_init ups_epi_heap [])
              (VSt (UPS + 0x46 + 6) ups_epi_regs1 ups_epi_heap [])
              ρB mf γ (dq:=DfracOwn q)
 ups_epilogue_run HmB
              with "Hsm Htlbinv Hpc Hfile Hbi2 [Hbra Hbs0 Hbs1] []").
    { rewrite /vheap_own. cbn [vheap]. rewrite /ups_epi_heap.
      cbn [big_opL fst snd]. rewrite HaraB Has0B Has1B HvraB Hvs0B Hvs1B.
      rewrite Hpra Hps0 Hps1. iFrame "Hbra Hbs0 Hbs1". }
    { rewrite /vheap4_own. cbn [vheap4]. done. }
    iIntros (M2) "%HmM2 Hsm Htlbinv Hpc Hfile Hheap _".
    destruct HmM2 as [HmM2 HaoM2].
    iEval (rewrite /vheap_own; cbn [vheap]; rewrite /ups_epi_heap;
           cbn [big_opL fst snd];
           rewrite HaraB Has0B Has1B HvraB Hvs0B Hvs1B) in "Hheap".
    iDestruct "Hheap" as "(Hbra & Hbs0 & Hbs1 & _)".
    iEval (cbn [vpc]) in "Hpc".
    (* read off M2's ra (= ra0) and sp (= sp'); s0/s1 are read in the finale. *)
    assert (HraM2 : M2 !!! Regidx (mword_of_int 1) = ra0).
    { assert (Hl : ups_epi_regs1 !! Regidx (mword_of_int 1) = Some (SX 33 0))
        by (vm_compute; reflexivity).
      rewrite (HmM2 _ _ Hl). exact HvraB. }
    assert (HspM2 : M2 !!! Regidx csp_rs1 = sp').
    { assert (Hl : ups_epi_regs1 !! Regidx csp_rs1 = Some (SX 2 0))
        by (vm_compute; reflexivity).
      rewrite (HmM2 _ _ Hl) sval_den_SX0. exact HspB. }
    (* ------------------------------------------------------------------ *)
    (* c.addi16sp sp,32 at 0x9ae: sp := sp + 32 = sp0.                      *)
    (* ------------------------------------------------------------------ *)
    iPoseProof (upi_4c with "Htext") as "Hi4c".
    assert (Hpc4c : (mword_of_int (UPS + 0x46 + 6) : mword 64)
                    = (mword_of_int (UPS + 0x4c) : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc4c) in "Hpc".
    iApply (wp_caddi16sp_gpr_s root_ppn γ Φ (mword_of_int (UPS + 0x4c)) (mword_of_int 2) M2 q
              with "Hsm Htlbinv Hpc Hfile Hi4c [-]").
    iIntros "Hsm Htlbinv Hpc Hfile".
    set (m_epi2 := <[Regidx csp_rs1 := regval_into_reg
                      (add_vec (M2 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2))))]> M2).
    change (<[Regidx csp_rs1 := regval_into_reg
              (add_vec (M2 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2))))]> M2) with m_epi2.
    (* ------------------------------------------------------------------ *)
    (* c.ret at 0x9b0: PC := ra (= ra0).                                    *)
    (* ------------------------------------------------------------------ *)
    iPoseProof (upi_4e with "Htext") as "Hi4e".
    assert (Hra_final : m_epi2 !!! Regidx (mword_of_int 1) = ra0).
    { unfold m_epi2.
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HraM2. }
    assert (Hpc4e : add_vec_int (mword_of_int (UPS + 0x4c)) 2
                    = (mword_of_int (UPS + 0x4e) : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc4e) in "Hpc".
    iApply (wp_cret_s_zca_scfg root_ppn γ Φ (mword_of_int (UPS + 0x4e)) (mword_of_int 1) m_epi2
              (dq:=DfracOwn q)
 ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra_final; exact Hal0)
              with "Hsm Htlbinv Hpc Hfile Hi4e [-]").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iEval (rewrite Hra_final) in "Hpc".
    (* rebundle the frame: the cells hold ra0/s00/s10 at pa_stk 1/2/3. *)
    iEval (rewrite Hpra) in "Hbra".
    iEval (rewrite Hps0) in "Hbs0".
    iEval (rewrite Hps1) in "Hbs1".
    iDestruct (stack_own_3_intro with "Hbra Hbs0 Hbs1") as "Htop".
    iDestruct (stack_own_split_2 sp0 3 n ltac:(lia) with "[$Htop $Hdeep]") as "Hstk".
    (* A block leaves every register it does not write at its [vregs_init]
       entry, so that register's post-block value is exactly its pre-block one:
       the block's [gpr_matches] reads the entry off [vregs_init], and the
       [vregs_den] identity that set the block up denotes it back to the input
       file.  (An entry outside [vregs_init] is impossible for an [mword 5], but
       [agree_off] discharges that branch without a case analysis.) *)
    assert (Hagree_pro : forall r : mword 5,
              ups_pro_regs1 !! Regidx r = vregs_init !! Regidx r ->
              M1 !!! Regidx r = m0 !!! Regidx r).
    { intros r Hr. destruct (vregs_init !! Regidx r) as [sv|] eqn:Hv.
      - rewrite (HmM1 _ _ Hr) -HdenA.
        symmetry. exact (vregs_den_lookup ρA vregs_init _ _ Hv).
      - exact (HaoM1 _ Hr). }
    assert (Hagree_epi : forall r : mword 5,
              ups_epi_regs1 !! Regidx r = vregs_init !! Regidx r ->
              M2 !!! Regidx r = mf !!! Regidx r).
    { intros r Hr. destruct (vregs_init !! Regidx r) as [sv|] eqn:Hv.
      - rewrite (HmM2 _ _ Hr) -HdenB.
        symmetry. exact (vregs_den_lookup ρB vregs_init _ _ Hv).
      - exact (HaoM2 _ Hr). }
    (* A register that neither block writes, that the body preserves, and that
       neither the [c.mv s1,a0] nor the [c.addi16sp sp,32] touches, still holds
       its entry value at the return. *)
    assert (Huntouched : forall r : mword 5,
              ups_epi_regs1 !! Regidx r = vregs_init !! Regidx r ->
              ups_pro_regs1 !! Regidx r = vregs_init !! Regidx r ->
              Regidx csp_rs1 <> Regidx r ->
              Regidx s1_idx <> Regidx r ->
              mf !!! Regidx r = m3 !!! Regidx r ->
              m_epi2 !!! Regidx r = m0 !!! Regidx r).
    { intros r He Hp Hne1 Hne2 Hbody.
      unfold m_epi2. rewrite lookup_total_insert_ne; [| exact Hne1].
      rewrite (Hagree_epi _ He) Hbody. unfold m3.
      rewrite lookup_total_insert_ne; [| exact Hne2].
      exact (Hagree_pro _ Hp). }
    iApply ("Hcont" $! m_epi2 with "Hsm Htlbinv Hpc Hfile [%] Hstk Hpk Hpkd Hown Hsent").
    split; [| exact Hra_final].
    unfold callee_saved. repeat split.
    (* every callee-saved register except sp/s0/s1 is simply never written *)
    all: try (apply Huntouched;
                [ vm_compute; reflexivity | vm_compute; reflexivity
                | vm_compute; discriminate | vm_compute; discriminate
                | first [ exact B4  | exact B18 | exact B19 | exact B20
                        | exact B21 | exact B22 | exact B23 | exact B24
                        | exact B25 | exact B26 | exact B27 ] ]).
    (* sp/s0/s1: spilled to the frame by the prologue, reloaded by the epilogue *)
    - (* sp: the -32/+32 frame adjustment cancels *)
      unfold m_epi2. rewrite lookup_total_insert.
      unfold regval_into_reg. rewrite HspM2. unfold sp'.
      change (caddi16sp_imm (mword_of_int 2)) with (caddi16sp_imm (mword_of_int 2 : mword 6)).
      apply ups_frame_cancel.
    - (* s0: reloaded from the frame slot holding the entry s0 *)
      unfold m_epi2.
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      etransitivity; [ apply (HmM2 _ (SX 34 0)); vm_compute; reflexivity |].
      exact Hvs0B.
    - (* s1: likewise *)
      unfold m_epi2.
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      etransitivity; [ apply (HmM2 _ (SX 35 0)); vm_compute; reflexivity |].
      exact Hvs1B.
  Qed.

End WpUartPutcSyncFull.
