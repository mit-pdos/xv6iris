(* WpMycpu.v -- whole-function WP for xv6's mycpu() in S-mode.
   mycpu() @ 0x800018d6 returns a0 = &cpus[cpuid] (cpuid = tp register),
   using its own 16-byte stack frame (saves/restores ra,s0).  Built by
   composing the S-mode instruction lemmas (existing framework ones plus the
   new arithmetic/auipc lemmas in WpPushOff.v), following the stack-geometry
   composition pattern of WpKernelvecNew (wp_kernelvec) / WpMemsetS.

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
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry WpEntryNew WpAuipc.
Require Import WpGpr WpGprAddi WpGprRvc WpGprShift WpGprJalr WpGprStore WpGprLogic WpGprAuipc.
Require Import SmodeCore WpSmodeGpr WpMemsetS WpSpinNew WpKernelvecNew WpPushOff.
Require Import WpTimerinit WpMemsetInstr.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Decode templates (mirrors of WpMemsetInstr's m_reg_step / m_open_rvc). *)
(* ===================================================================== *)
Local Ltac my_reg_step name w hi lo s :=
  assert (name : exec (encdec_reg_backwards (subrange_vec_dec w hi lo)) s
              = Some (Regidx (autocast (T := mword)
                        (subrange_vec_dec (subrange_vec_dec w hi lo)
                           (Z.sub regidx_bit_width 1) 0)), s));
  [ unfold encdec_reg_backwards;
    match goal with |- context[if ?g then returnM (Regidx _) else _] =>
      replace g with true by (vm_compute; reflexivity) end; cbn match; apply exec_returnM
  | idtac ].

Local Ltac my_open_rvc s HmisaC :=
  unfold ext_decode_compressed, encdec_compressed_backwards; cbv beta; cbn zeta;
  skip_pure_clause; repeat (dstep s HmisaC);
  match goal with |- context[if ?g then _ else returnM None] =>
    replace g with true by (vm_compute; reflexivity) end;
  cbn match; rewrite exec_bind.

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

(* ---- the six fresh decodes (bit patterns not shared with memset) ---- *)
(* +0x08  8792  c.mv a5,tp *)
Lemma mydec_mv s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8792 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 15), Regidx (mword_of_int 4)), s).
Proof.
  intro H. my_reg_step Hr1 (mword_of_int 0x8792 : mword 16) 11 7 s.
  my_reg_step Hr2 (mword_of_int 0x8792 : mword 16) 6 2 s.
  my_open_rvc s H.
  rewrite (exec_bind_Some _ _ _ _ _ Hr1). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ Hr2). cbn beta.
  my_close1 s H.
Qed.

(* +0x0a  2781  c.addiw a5,0 (sext.w) *)
Lemma mydec_addiw s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x2781 : mword 16)) s
  = Some (C_ADDIW (mword_of_int 0, Regidx (mword_of_int 15)), s).
Proof.
  intro H. my_reg_step Hr (mword_of_int 0x2781 : mword 16) 11 7 s.
  my_open_rvc s H.
  match goal with |- context[Defs.and_boolM (Defs.and_boolM (returnM ?b32) (currentlyEnabled Ext_Zca)) (returnM ?p)] =>
    assert (HJ : exec (Defs.and_boolM (Defs.and_boolM (returnM b32) (currentlyEnabled Ext_Zca)) (returnM p)) s = Some (false, s))
      by (rewrite (exec_and_boolM_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM b32) (currentlyEnabled Ext_Zca)) s = Some (false, s)));
          [ reflexivity
          | rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM b32 s));
            replace b32 with false by (vm_compute; reflexivity); reflexivity ])
  end.
  rewrite HJ. cbn match.
  rewrite exec_bind.
  rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
  my_close2 s H.
Qed.

(* +0x0c  079e  c.slli a5,7 *)
Lemma mydec_slli s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x079e : mword 16)) s
  = Some (C_SLLI (mword_of_int 7, Regidx (mword_of_int 15)), s).
Proof.
  intro H. my_reg_step Hr (mword_of_int 0x079e : mword 16) 11 7 s.
  my_open_rvc s H.
  rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
  my_close1 s H.
Qed.

(* +0x16  953e  c.add a0,a0,a5 *)
Lemma mydec_add s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x953e : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 10), Regidx (mword_of_int 15)), s).
Proof.
  intro H. my_reg_step Hr1 (mword_of_int 0x953e : mword 16) 11 7 s.
  my_reg_step Hr2 (mword_of_int 0x953e : mword 16) 6 2 s.
  my_open_rvc s H.
  rewrite (exec_bind_Some _ _ _ _ _ Hr1). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ Hr2). cbn beta.
  my_close1 s H.
Qed.

(* +0x0e  00011517  auipc a0,0x11 *)
Lemma mydec_auipc s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0x00011517 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.

(* +0x12  a9450513  addi a0,a0,-1388 *)
Lemma mydec_addi s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0xa9450513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xa94 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.

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
       (sign_extend' 64 (mword_of_int 0xa94 : mword 12)))
    (mycpu_a5 tp0).

Section WpMycpu.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* [instr] facts for the fourteen mycpu instructions from [kernel_text]. *)
  (* ------------------------------------------------------------------- *)
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

  Lemma myi_00 : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc2 (KernelSyms.mycpu + 0x00)%Z (mword_of_int 0x1141 : mword 16)
    (mword_of_int (KernelSyms.mycpu + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_ccc exec_execute_C_ADDI. Qed.

  Lemma myi_02 : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc4 (KernelSyms.mycpu + 0x02)%Z (mword_of_int 0xe406 : mword 16) (mword_of_int 0xe022e406 : mword 32)
    (mword_of_int (KernelSyms.mycpu + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) mdec_cce exec_execute_C_SDSP. Qed.

  Lemma myi_04 : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc2 (KernelSyms.mycpu + 0x04)%Z (mword_of_int 0xe022 : mword 16)
    (mword_of_int (KernelSyms.mycpu + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) mdec_cd0 exec_execute_C_SDSP. Qed.

  Lemma myi_06 : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc4 (KernelSyms.mycpu + 0x06)%Z (mword_of_int 0x0800 : mword 16) (mword_of_int 0x87920800 : mword 32)
    (mword_of_int (KernelSyms.mycpu + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) mdec_cd2 exec_execute_C_ADDI4SPN. Qed.

  Lemma myi_08 : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x08) : mword 64) true (RTYPE (Regidx (mword_of_int 4), zreg, Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc2 (KernelSyms.mycpu + 0x08)%Z (mword_of_int 0x8792 : mword 16)
    (mword_of_int (KernelSyms.mycpu + 0x08) : mword 64) (RTYPE (Regidx (mword_of_int 4), zreg, Regidx (mword_of_int 15), ADD)) mydec_mv exec_execute_C_MV. Qed.

  Lemma myi_0a : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x0a) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc4 (KernelSyms.mycpu + 0x0a)%Z (mword_of_int 0x2781 : mword 16) (mword_of_int 0x079e2781 : mword 32)
    (mword_of_int (KernelSyms.mycpu + 0x0a) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) mydec_addiw exec_execute_C_ADDIW. Qed.

  Lemma myi_0c : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x0c) : mword 64) true (SHIFTIOP (mword_of_int 7 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_rvc2 (KernelSyms.mycpu + 0x0c)%Z (mword_of_int 0x079e : mword 16)
    (mword_of_int (KernelSyms.mycpu + 0x0c) : mword 64) (SHIFTIOP (mword_of_int 7 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)) mydec_slli exec_execute_C_SLLI. Qed.

  Lemma myi_0e : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x0e) : mword 64) false (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (KernelSyms.mycpu + 0x0e)%Z (mword_of_int 0x00011517 : mword 32)
    (mword_of_int (KernelSyms.mycpu + 0x0e) : mword 64) (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 10), AUIPC)) mydec_auipc. Qed.

  Lemma myi_12 : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x12) : mword 64) false (ITYPE (mword_of_int 0xa94 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (KernelSyms.mycpu + 0x12)%Z (mword_of_int 0xa9450513 : mword 32)
    (mword_of_int (KernelSyms.mycpu + 0x12) : mword 64) (ITYPE (mword_of_int 0xa94 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) mydec_addi. Qed.

  Lemma myi_16 : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x16) : mword 64) true (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc4 (KernelSyms.mycpu + 0x16)%Z (mword_of_int 0x953e : mword 16) (mword_of_int 0x60a2953e : mword 32)
    (mword_of_int (KernelSyms.mycpu + 0x16) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADD)) mydec_add exec_execute_C_ADD. Qed.

  Lemma myi_18 : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x18) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc2 (KernelSyms.mycpu + 0x18)%Z (mword_of_int 0x60a2 : mword 16)
    (mword_of_int (KernelSyms.mycpu + 0x18) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) mdec_cea exec_execute_C_LDSP. Qed.

  Lemma myi_1a : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x1a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc4 (KernelSyms.mycpu + 0x1a)%Z (mword_of_int 0x6402 : mword 16) (mword_of_int 0x01416402 : mword 32)
    (mword_of_int (KernelSyms.mycpu + 0x1a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) mdec_cec exec_execute_C_LDSP. Qed.

  Lemma myi_1c : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x1c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc2 (KernelSyms.mycpu + 0x1c)%Z (mword_of_int 0x0141 : mword 16)
    (mword_of_int (KernelSyms.mycpu + 0x1c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_cee exec_execute_C_ADDI. Qed.

  Lemma myi_1e : kernel_text -∗ instr (mword_of_int (KernelSyms.mycpu + 0x1e) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc4 (KernelSyms.mycpu + 0x1e)%Z (mword_of_int 0x8082 : mword 16) (mword_of_int 0x11018082 : mword 32)
    (mword_of_int (KernelSyms.mycpu + 0x1e) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) mdec_cf0 exec_execute_C_JR. Qed.

  (* =================================================================== *)
  (*  THE CAPSTONE: a WP for the entire mycpu(), entry (0x800018d6) through *)
  (*  its return to the caller (PC = ra0 with the low bit cleared).         *)
  (*  Registers: ra=x1 sp=x2 tp=x4 s0=x8 a0=x10 a5=x15.                      *)
  (*  On exit a0 = &cpus[cpuid] = mycpu_ret (m0 !!! Regidx (mword_of_int 4)) *)
  (*  (the [a0] slot of the returned register file m11 equals mycpu_ret tp0),*)
  (*  a5 is clobbered, and ra/sp/s0 are restored (callee-saved).            *)
  (* =================================================================== *)
  Lemma wp_mycpu (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (m0 : gmap regidx (mword 64))
      (raold s0old : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq : dfrac} :
    let ra_idx : mword 5 := mword_of_int 1 in
    let tp_idx : mword 5 := mword_of_int 4 in
    let s0_idx : mword 5 := mword_of_int 8 in
    let a0_idx : mword 5 := mword_of_int 10 in
    let a5_idx : mword 5 := mword_of_int 15 in
    let pcE := mword_of_int KernelSyms.mycpu in
    let imm_entry : mword 6 := mword_of_int 48 in
    let imm_dealloc : mword 6 := mword_of_int 16 in
    let nzimm_s0 : mword 8 := mword_of_int 4 in
    let imm_auipc : mword 20 := mword_of_int 0x11 in
    let imm_addi : mword 12 := mword_of_int 0xa94 in
    let shamt_slli : mword 6 := mword_of_int 7 in
    let imm_addiw : mword 6 := mword_of_int 0 in
    let sp' := add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry)) in
    let ra0 := m0 !!! Regidx ra_idx in
    let s00 := m0 !!! Regidx s0_idx in
    let ea_ra := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let a8_ra := ea_ra in
    let pa_ra := a8_ra in
    let ea_s0 := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let a8_s0 := ea_s0 in
    let pa_s0 := a8_s0 in
    let m1 := <[Regidx csp_rs1 := regval_into_reg sp']> m0 in
    let m2 := <[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1 in
    let m3 := <[Regidx a5_idx := regval_into_reg (add_vec zero_reg (m2 !!! Regidx tp_idx))]> m2 in
    let m4 := <[Regidx a5_idx := regval_into_reg (sign_extend' 64 (subrange_vec_dec (add_vec (m3 !!! Regidx a5_idx) (sign_extend' 64 (sign_extend' 12 imm_addiw))) 31 0))]> m3 in
    let m5 := <[Regidx a5_idx := regval_into_reg (shift_bits_left (m4 !!! Regidx a5_idx) (subrange_vec_dec shamt_slli (Z.sub log2_xlen 1) 0))]> m4 in
    let m6 := <[Regidx a0_idx := regval_into_reg (add_vec (add_vec_int pcE 14) (auipc_off imm_auipc))]> m5 in
    let m7 := <[Regidx a0_idx := regval_into_reg (add_vec (m6 !!! Regidx a0_idx) (sign_extend' 64 imm_addi))]> m6 in
    let m8 := <[Regidx a0_idx := regval_into_reg (add_vec (m7 !!! Regidx a0_idx) (m7 !!! Regidx a5_idx))]> m7 in
    let m9 := <[Regidx ra_idx := regval_into_reg ra0]> m8 in
    let m10 := <[Regidx s0_idx := regval_into_reg s00]> m9 in
    let m11 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m10 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)))]> m10 in
    let ret_tgt := update_vec_dec (add_vec ra0 (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    kv_fetch_geom pcE -> kv_fetch_geom (add_vec_int pcE 2) -> kv_fetch_geom (add_vec_int pcE 4) ->
    kv_fetch_geom (add_vec_int pcE 6) -> kv_fetch_geom (add_vec_int pcE 8) -> kv_fetch_geom (add_vec_int pcE 10) ->
    kv_fetch_geom (add_vec_int pcE 12) -> kv_fetch_geom (add_vec_int pcE 14) -> kv_fetch_geom (add_vec_int pcE 16) ->
    kv_fetch_geom (add_vec_int pcE 18) -> kv_fetch_geom (add_vec_int pcE 20) -> kv_fetch_geom (add_vec_int pcE 22) ->
    kv_fetch_geom (add_vec_int pcE 24) -> kv_fetch_geom (add_vec_int pcE 26) -> kv_fetch_geom (add_vec_int pcE 28) ->
    kv_fetch_geom (add_vec_int pcE 30) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pcE ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 (add_vec_int pcE 2) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 (add_vec_int pcE 4) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 (add_vec_int pcE 6) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 (add_vec_int pcE 8) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 (add_vec_int pcE 10) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 (add_vec_int pcE 12) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 (add_vec_int pcE 14) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 (add_vec_int pcE 18) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 (add_vec_int pcE 22) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 (add_vec_int pcE 24) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 (add_vec_int pcE 26) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 (add_vec_int pcE 28) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 (add_vec_int pcE 30) ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec ret_tgt 1) = false ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (* the single "PMP TOR entry 0 covers all of RAM" config fact *)
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    (* sp-alignment for the ra frame slot (8(sp')) *)
    is_aligned_vaddr (Virtaddr a8_ra) 8 = true ->
    is_aligned_paddr (Physaddr pa_ra) 8 = true ->
    (* sp-alignment for the s0 frame slot (0(sp')) *)
    is_aligned_vaddr (Virtaddr a8_s0) 8 = true ->
    is_aligned_paddr (Physaddr pa_s0) 8 = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m0 -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa_ra j) ↦ₘ nth_byte raold j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa_s0 j) ↦ₘ nth_byte s0old j) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is ret_tgt -∗ gpr_file m11 -∗
      ([∗ list] j ∈ seq 0 8, (pa_add pa_ra j) ↦ₘ nth_byte ra0 j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add pa_s0 j) ↦ₘ nth_byte s00 j) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ra_idx tp_idx s0_idx a0_idx a5_idx pcE imm_entry imm_dealloc nzimm_s0
      imm_auipc imm_addi shamt_slli imm_addiw sp' ra0 s00
      ea_ra a8_ra pa_ra ea_s0 a8_s0 pa_s0
      m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 ret_tgt
      HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe
      Hg0 Hg2 Hg4 Hg6 Hg8 Hg10 Hg12 Hg14 Hg16 Hg18 Hg20 Hg22 Hg24 Hg26 Hg28 Hg30
      Hp0 Hp2 Hp4 Hp6 Hp8 Hp10 Hp12 Hp14 Hp18 Hp22 Hp24 Hp26 Hp28 Hp30
      Hpmpp Hpteregion Halignp Hal0 Hal1 HW HR Hramcov
      HalignR HpalignR HalignS HpalignS.
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = sp')
      by (unfold m1; rewrite lookup_total_insert; reflexivity).
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
             #Htext Hpc Hfile Hbra Hbs0 Hcont".
    (* derive the fourteen instr resources from the text image *)
    iPoseProof (myi_00 with "Htext") as "Hi00".
    iPoseProof (myi_02 with "Htext") as "Hi02".
    iPoseProof (myi_04 with "Htext") as "Hi04".
    iPoseProof (myi_06 with "Htext") as "Hi06".
    iPoseProof (myi_08 with "Htext") as "Hi08".
    iPoseProof (myi_0a with "Htext") as "Hi0a".
    iPoseProof (myi_0c with "Htext") as "Hi0c".
    iPoseProof (myi_0e with "Htext") as "Hi0e".
    iPoseProof (myi_12 with "Htext") as "Hi12".
    iPoseProof (myi_16 with "Htext") as "Hi16".
    iPoseProof (myi_18 with "Htext") as "Hi18".
    iPoseProof (myi_1a with "Htext") as "Hi1a".
    iPoseProof (myi_1c with "Htext") as "Hi1c".
    iPoseProof (myi_1e with "Htext") as "Hi1e".
    (* +0x00 c.addi sp,-16 : sp := sp' *)
    iApply (wp_caddi_gpr_s_config root_ppn E Φ pcE csp_rs1 imm_entry m0
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hg0 Hp0 Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi00 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry)))]> m0) with m1.
    (* +0x02 c.sdsp ra,8(sp) : store ra0 to 8(sp') *)
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (add_vec_int pcE 2) (mword_of_int 1) ra_idx m1 raold
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hg2 Hp2
              Hpmpp Hpteregion Halignp
              Hramcov HW
              ltac:(rewrite Hsp1; exact HalignR) ltac:(rewrite Hsp1; exact HpalignR)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi02 [Hbra]").
    { rewrite Hsp1. iExact "Hbra". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hbra".
    assert (Hra_eq : m1 !!! Regidx ra_idx = ra0)
      by (unfold m1; rewrite lookup_total_insert_ne; [ reflexivity | vm_compute; discriminate ]).
    iEval (rewrite Hsp1 Hra_eq) in "Hbra".
    (* +0x04 c.sdsp s0,0(sp) : store s00 to 0(sp') *)
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (add_vec_int pcE 4) (mword_of_int 0) s0_idx m1 s0old
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hg4 Hp4
              Hpmpp Hpteregion Halignp
              Hramcov HW
              ltac:(rewrite Hsp1; exact HalignS) ltac:(rewrite Hsp1; exact HpalignS)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi04 [Hbs0]").
    { rewrite Hsp1. iExact "Hbs0". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hbs0".
    assert (Hs0_eq : m1 !!! Regidx s0_idx = s00)
      by (unfold m1; rewrite lookup_total_insert_ne; [ reflexivity | vm_compute; discriminate ]).
    iEval (rewrite Hsp1 Hs0_eq) in "Hbs0".
    (* +0x06 c.addi4spn s0,sp,16 : s0 := sp'+16 *)
    iApply (wp_caddi4spn_gpr_s_config root_ppn E Φ (add_vec_int pcE 6) (Cregidx (mword_of_int 0)) nzimm_s0 s0_idx m1
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hg6 Hp6 Hpmpp Hpteregion Halignp ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi06 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1) with m2.
    (* +0x08 c.mv a5,tp : a5 := tp *)
    iApply (wp_cmv_gpr_s_config root_ppn E Φ (add_vec_int pcE 8) a5_idx tp_idx m2
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hg8 Hp8 Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi08 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx a5_idx := regval_into_reg (add_vec zero_reg (m2 !!! Regidx tp_idx))]> m2) with m3.
    (* +0x0a c.addiw a5,0 : a5 := sext32(a5) *)
    iApply (wp_caddiw_s root_ppn E Φ (add_vec_int pcE 10) a5_idx imm_addiw m3
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hg10 Hp10 Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi0a [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx a5_idx := regval_into_reg (sign_extend' 64 (subrange_vec_dec (add_vec (m3 !!! Regidx a5_idx) (sign_extend' 64 (sign_extend' 12 imm_addiw))) 31 0))]> m3) with m4.
    (* +0x0c c.slli a5,7 : a5 := a5 << 7 *)
    iApply (wp_cslli_gpr_s_config root_ppn E Φ (add_vec_int pcE 12) (Regidx a5_idx) a5_idx shamt_slli m4
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hg12 Hp12 Hpmpp Hpteregion Halignp ltac:(reflexivity) ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi0c [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx a5_idx := regval_into_reg (shift_bits_left (m4 !!! Regidx a5_idx) (subrange_vec_dec shamt_slli (Z.sub log2_xlen 1) 0))]> m4) with m5.
    (* +0x0e auipc a0,0x11 : a0 := pc + off *)
    iApply (wp_auipc_s root_ppn E Φ (add_vec_int pcE 14) a0_idx imm_auipc m5
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hg14 Hg16 Hp14 Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi0e [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx a0_idx := regval_into_reg (add_vec (add_vec_int pcE 14) (auipc_off imm_auipc))]> m5) with m6.
    replace (add_vec_int (add_vec_int pcE 14) 4) with (add_vec_int pcE 18) by (vm_compute; reflexivity).
    (* +0x12 addi a0,a0,-1388 : a0 := &cpus *)
    iApply (wp_addi4_s root_ppn E Φ (add_vec_int pcE 18) a0_idx a0_idx imm_addi m6
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hg18 Hg20 Hp18 Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi12 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx a0_idx := regval_into_reg (add_vec (m6 !!! Regidx a0_idx) (sign_extend' 64 imm_addi))]> m6) with m7.
    replace (add_vec_int (add_vec_int pcE 18) 4) with (add_vec_int pcE 22) by (vm_compute; reflexivity).
    (* +0x16 c.add a0,a0,a5 : a0 := &cpus[cpuid] *)
    iApply (wp_cadd_s root_ppn E Φ (add_vec_int pcE 22) a0_idx a5_idx m7
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hg22 Hp22 Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi16 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx a0_idx := regval_into_reg (add_vec (m7 !!! Regidx a0_idx) (m7 !!! Regidx a5_idx))]> m7) with m8.
    assert (Hsp8 : m8 !!! Regidx csp_rs1 = sp').
    { unfold m8, m7, m6, m5, m4, m3, m2, m1.
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite lookup_total_insert. reflexivity. }
    (* +0x18 c.ldsp ra,8(sp) : ra := ra0 *)
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (add_vec_int pcE 24) (mword_of_int 1) ra_idx m8 ra0
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq) (dqm:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hg24 Hp24
              Hpmpp Hpteregion Halignp
              Hramcov HR
              ltac:(rewrite Hsp8; exact HalignR) ltac:(rewrite Hsp8; exact HpalignR)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi18 [Hbra]").
    { rewrite Hsp8. iExact "Hbra". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hbra".
    change (<[Regidx ra_idx := regval_into_reg ra0]> m8) with m9.
    iEval (rewrite Hsp8) in "Hbra".
    assert (Hsp9 : m9 !!! Regidx csp_rs1 = sp')
      by (unfold m9; rewrite lookup_total_insert_ne; [ exact Hsp8 | vm_compute; discriminate ]).
    (* +0x1a c.ldsp s0,0(sp) : s0 := s00 *)
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (add_vec_int pcE 26) (mword_of_int 0) s0_idx m9 s00
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq) (dqm:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hg26 Hp26
              Hpmpp Hpteregion Halignp
              Hramcov HR
              ltac:(rewrite Hsp9; exact HalignS) ltac:(rewrite Hsp9; exact HpalignS)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi1a [Hbs0]").
    { rewrite Hsp9. iExact "Hbs0". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hbs0".
    change (<[Regidx s0_idx := regval_into_reg s00]> m9) with m10.
    iEval (rewrite Hsp9) in "Hbs0".
    assert (Hsp10 : m10 !!! Regidx csp_rs1 = sp')
      by (unfold m10; rewrite lookup_total_insert_ne; [ exact Hsp9 | vm_compute; discriminate ]).
    (* +0x1c c.addi sp,16 : sp := sp'+16 *)
    iApply (wp_caddi_gpr_s_config root_ppn E Φ (add_vec_int pcE 28) csp_rs1 imm_dealloc m10
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hg28 Hp28 Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi1c [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (m10 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)))]> m10) with m11.
    assert (Hra_final : m11 !!! Regidx ra_idx = ra0).
    { unfold m11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      unfold m10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      unfold m9. rewrite lookup_total_insert. reflexivity. }
    (* +0x1e c.ret : PC := ra0 (low bit cleared) *)
    iApply (wp_cret_s root_ppn E Φ (add_vec_int pcE 30) ra_idx m11
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hg30 Hp30 Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate) Hlpe
              ltac:(rewrite Hra_final; exact Hal0) ltac:(rewrite Hra_final; exact Hal1)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi1e [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    iEval (rewrite Hra_final) in "Hpc".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile [Hbra] [Hbs0]").
    - iExact "Hbra".
    - iExact "Hbs0".
  Qed.

End WpMycpu.
