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
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Values.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpDecode WpLeafCommon WpEntryNew WpAuipc.
Require Import WpGpr WpGprRvc.
Require Import SmodeCore WpPushOff.
Require Import WpMemsetInstr.
Require Import WpRvcBridge.
Require Import StackOwn.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
Require Import VcGen VcGenS.
Require Import CalleeSaved.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.
Import Defs.

(* mycpu's balanced frame: entry [addi sp,sp,-16] (imm 48 = -16 in 6-bit) and
   exit [addi sp,sp,+16] (imm 16) cancel, so sp returns to its entry value.
   (A local clone of WpMemsetPage.add_vec_frame_cancel, which lives downstream.) *)
Lemma mycpu_frame_cancel (X : mword 64) :
  add_vec (add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = X.
Proof.
  assert (add_vec_unsigned : forall x y : mword 64,
            bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y)).
  { intros x y. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned. reflexivity. }
  apply bv_eq. rewrite !add_vec_unsigned. rewrite bv_wrap_add_idemp_l.
  assert (HA : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)) : mword 64)
             = 18446744073709551600) by (vm_compute; reflexivity).
  assert (HB : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)) : mword 64)
             = 16) by (vm_compute; reflexivity).
  rewrite HA HB. rewrite <- Z.add_assoc.
  replace (18446744073709551600 + 16) with (bv_modulus 64) by (vm_compute; reflexivity).
  rewrite bv_wrap_add_modulus_1. apply bv_wrap_bv_unsigned.
Qed.

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

(* ---- the six fresh decodes (bit patterns not shared with memset) ---- *)
(* +0x08  8792  c.mv a5,tp *)
Lemma mydec_mv s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8792 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 15), Regidx (mword_of_int 4)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x0a  2781  c.addiw a5,0 (sext.w) *)
Lemma mydec_addiw s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x2781 : mword 16)) s
  = Some (C_ADDIW (mword_of_int 0, Regidx (mword_of_int 15)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x0c  079e  c.slli a5,7 *)
Lemma mydec_slli s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x079e : mword 16)) s
  = Some (C_SLLI (mword_of_int 7, Regidx (mword_of_int 15)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x16  953e  c.add a0,a0,a5 *)
Lemma mydec_add s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x953e : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 10), Regidx (mword_of_int 15)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x0e  00011517  auipc a0,0x11 *)
Lemma mydec_auipc s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00011517 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x12  a9450513  addi a0,a0,-1388 *)
Lemma mydec_addi s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa9450513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xa94 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

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


(* ---------------------------------------------------------------------- *)
(* The two straight-line blocks of mycpu, in the VCgen's alphabet.          *)
(* ---------------------------------------------------------------------- *)
Definition mycpu_prologue : list vop_s :=
  [ VScaddi (mword_of_int 48) csp_rs1;                                  (* c.addi sp,-16      *)
    VScsdsp (mword_of_int 1) (mword_of_int 1);                          (* sd ra,8(sp)        *)
    VScsdsp (mword_of_int 0) (mword_of_int 8);                          (* sd s0,0(sp)        *)
    VScaddi4spn (Cregidx (mword_of_int 0)) (mword_of_int 4)
                (mword_of_int 8) ].                                     (* addi s0,sp,16      *)

Definition mycpu_epilogue : list vop_s :=
  [ VScldsp (mword_of_int 1) (mword_of_int 1);                          (* ld ra,8(sp)        *)
    VScldsp (mword_of_int 0) (mword_of_int 8);                          (* ld s0,0(sp)        *)
    VScaddi (mword_of_int 16) csp_rs1 ].                                (* c.addi sp,16       *)

(* variable convention: xk ↦ SX k 0 (from vregs_init); 33/34 = the two
   stack-slot contents at block entry. *)
Definition mycpu_pro_heap0 : list (sval * sval) :=
  [ (SX 2 (wrap64 (-8)),  SX 33 0);
    (SX 2 (wrap64 (-16)), SX 34 0) ].
Definition mycpu_pro_heap1 : list (sval * sval) :=
  [ (SX 2 (wrap64 (-8)),  SX 1 0);
    (SX 2 (wrap64 (-16)), SX 8 0) ].
Definition mycpu_pro_regs1 : gmap regidx sval :=
  <[Regidx (mword_of_int 8 : mword 5) := SX 2 0]>
    (<[Regidx csp_rs1 := SX 2 (wrap64 (-16))]> vregs_init).

Lemma mycpu_prologue_run :
  vc_block_s (VSt KernelSyms.mycpu vregs_init mycpu_pro_heap0 []) mycpu_prologue
  = Some (VSt (KernelSyms.mycpu + 8) mycpu_pro_regs1 mycpu_pro_heap1 []).
Proof. vm_compute. reflexivity. Qed.

(* the epilogue runs with sp already at sp' (the decremented value), so its
   stack slots sit at sp+8 / sp+0. *)
Definition mycpu_epi_heap : list (sval * sval) :=
  [ (SX 2 8, SX 33 0);
    (SX 2 0, SX 34 0) ].
Definition mycpu_epi_regs1 : gmap regidx sval :=
  <[Regidx csp_rs1 := SX 2 16]>
    (<[Regidx (mword_of_int 8 : mword 5) := SX 34 0]>
       (<[Regidx (mword_of_int 1 : mword 5) := SX 33 0]> vregs_init)).

Lemma mycpu_epilogue_run :
  vc_block_s (VSt (KernelSyms.mycpu + 24) vregs_init mycpu_epi_heap []) mycpu_epilogue
  = Some (VSt (KernelSyms.mycpu + 30) mycpu_epi_regs1 mycpu_epi_heap []).
Proof. vm_compute. reflexivity. Qed.
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
  (* the prologue's / epilogue's [instr] facts, from kernel_text via the
     existing WpMycpu decode templates. *)
  Lemma mycpu_prologue_instrs :
    kernel_text -∗ block_instrs_s KernelSyms.mycpu mycpu_prologue.
  Proof.
    iIntros "#Ht". cbn [block_instrs_s mycpu_prologue vop_s_ast].
    replace (KernelSyms.mycpu + 2 + 2) with (KernelSyms.mycpu + 4) by lia.
    replace (KernelSyms.mycpu + 4 + 2) with (KernelSyms.mycpu + 6) by lia.
    iSplitR; [by iApply myi_00|].
    iSplitR; [by iApply myi_02|].
    iSplitR; [by iApply myi_04|].
    iSplitR.
    { assert (Hcreg : creg2reg_idx (Cregidx (mword_of_int 0 : mword 3))
                      = Regidx (mword_of_int 8 : mword 5))
        by (vm_compute; reflexivity).
      rewrite -Hcreg. by iApply myi_06. }
    done.
  Qed.

  Lemma mycpu_epilogue_instrs :
    kernel_text -∗ block_instrs_s (KernelSyms.mycpu + 24) mycpu_epilogue.
  Proof.
    iIntros "#Ht". cbn [block_instrs_s mycpu_epilogue vop_s_ast].
    replace (KernelSyms.mycpu + 24 + 2) with (KernelSyms.mycpu + 26) by lia.
    replace (KernelSyms.mycpu + 26 + 2) with (KernelSyms.mycpu + 28) by lia.
    iSplitR; [by iApply myi_18|].
    iSplitR; [by iApply myi_1a|].
    iSplitR; [by iApply myi_1c|].
    done.
  Qed.

  (* ------------------------------------------------------------------- *)
  Lemma wp_mycpu (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (m0 : gmap regidx (mword 64))
      (n : nat)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
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
    let sp0 := m0 !!! Regidx csp_rs1 in
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
    (2 ≤ n)%nat ->
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    (* the single "PMP TOR entry 0 covers all of RAM" config fact *)
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m0 -∗
    stack_own sp0 n -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is ret_tgt -∗ gpr_file m11 -∗
      stack_own sp0 n -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ra_idx tp_idx s0_idx a0_idx a5_idx pcE imm_entry imm_dealloc nzimm_s0
      imm_auipc imm_addi shamt_slli imm_addiw sp0 sp' ra0 s00
      ea_ra a8_ra pa_ra ea_s0 a8_s0 pa_s0
      m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 ret_tgt
      Hn2 HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 Hlpe Hal0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             #Htext Hpc Hfile Hstk Hcont".
    (* peel mycpu's two-slot frame off the abstract stack ownership and thread
       the concrete slots through the instruction chain; the caller's extra
       depth [n-2] rides along untouched in [Hdeep]. *)
    iDestruct (stack_own_split_1 sp0 2 n ltac:(lia) with "Hstk") as "[Htop Hdeep]".
    iDestruct (stack_own_2_elim with "Htop") as (raold s0old) "[Hbra Hbs0]".
    (* the two slots sit at the raw SP-relative addresses mycpu's stores use. *)
    assert (Hpra : add_vec (add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hps0 : add_vec (add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpra) in "Hbra".
    iEval (rewrite -Hps0) in "Hbs0".
    (* register-index / offset spelling bridges (pure, concrete) *)
    assert (Hcsp2 : Regidx (mword_of_int 2 : mword 5) = Regidx csp_rs1)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    (* ------------------------------------------------------------------ *)
    (* SEAM 1: enter the prologue block.                                    *)
    (* ------------------------------------------------------------------ *)
    iDestruct (gpr_file_dom with "Hfile") as "[%Hdom0 Hfile]".
    iDestruct (gpr_file_x0 m0 (mword_of_int 0) ltac:(vm_compute; reflexivity)
                 with "Hfile") as "[%Hx00 Hfile]".
    set (ρA := fun k : nat =>
           if (k <? 32)%nat
           then m0 !!! Regidx (mword_of_int (Z.of_nat k) : mword 5)
           else if Nat.eqb k 33 then (raold : mword 64) else (s0old : mword 64)).
    assert (HdenA : vregs_den ρA vregs_init = m0).
    { apply (vregs_den_init_agree _ _ Hdom0 Hx00). intros k Hk.
      unfold ρA. rewrite (proj2 (Nat.ltb_lt k 32) Hk). reflexivity. }
    (* the block's two cells ARE the two stack words *)
    assert (Hara : sval_den ρA (SX 2 (wrap64 (-8))) = pa_ra).
    { cbn [sval_den].
      replace (ρA 2%nat) with (m0 !!! Regidx (mword_of_int 2 : mword 5))
        by (unfold ρA; reflexivity).
      rewrite Hcsp2.
      unfold pa_ra, a8_ra, ea_ra, sp'. rewrite add_vec_off2.
      f_equal; f_equal; vm_compute; reflexivity. }
    assert (Has0 : sval_den ρA (SX 2 (wrap64 (-16))) = pa_s0).
    { cbn [sval_den].
      replace (ρA 2%nat) with (m0 !!! Regidx (mword_of_int 2 : mword 5))
        by (unfold ρA; reflexivity).
      rewrite Hcsp2.
      unfold pa_s0, a8_s0, ea_s0, sp'. rewrite add_vec_off2.
      f_equal; f_equal; vm_compute; reflexivity. }
    assert (Hvra : sval_den ρA (SX 33 0) = (raold : mword 64)).
    { cbn [sval_den].
      replace (ρA 33%nat) with (raold : mword 64) by (unfold ρA; reflexivity).
      change (add_vec (raold : mword 64) (mword_of_int 0))
        with (add_vec_int (raold : mword 64) 0).
      apply avi0. }
    assert (Hvs0 : sval_den ρA (SX 34 0) = (s0old : mword 64)).
    { cbn [sval_den].
      replace (ρA 34%nat) with (s0old : mword 64) by (unfold ρA; reflexivity).
      change (add_vec (s0old : mword 64) (mword_of_int 0))
        with (add_vec_int (s0old : mword 64) 0).
      apply avi0. }
    iDestruct (mycpu_prologue_instrs with "Htext") as "Hbi".
    iEval (rewrite -HdenA) in "Hfile".
    iApply (wp_vc_block_s_den root_ppn mycpu_prologue E Φ
              (VSt KernelSyms.mycpu vregs_init mycpu_pro_heap0 [])
              (VSt (KernelSyms.mycpu + 8) mycpu_pro_regs1 mycpu_pro_heap1 [])
              ρA mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 mycpu_prologue_run
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                    Hpc Hfile Hbi [Hbra Hbs0] []").
    { rewrite /vheap_own. cbn [vheap].
      rewrite /mycpu_pro_heap0.
      cbn [big_opL fst snd]. rewrite Hara Has0 Hvra Hvs0.
      iFrame "Hbra Hbs0". }
    { rewrite /vheap4_own. cbn [vheap4]. done. }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hheap _".
    (* SEAM 1 exit: the symbolic post-state denotes to m2 / the stored words *)
    assert (Hspv : sval_den ρA (SX 2 (wrap64 (-16))) = sp').
    { cbn [sval_den].
      replace (ρA 2%nat) with (m0 !!! Regidx (mword_of_int 2 : mword 5))
        by (unfold ρA; reflexivity).
      rewrite Hcsp2. unfold sp'. f_equal;
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hs0v : sval_den ρA (SX 2 0)
                   = add_vec (m1 !!! Regidx csp_rs1)
                             (sign_extend' 64 (caddi4spn_imm nzimm_s0))).
    { cbn [sval_den].
      replace (ρA 2%nat) with (m0 !!! Regidx (mword_of_int 2 : mword 5))
        by (unfold ρA; reflexivity).
      rewrite Hcsp2.
      unfold m1. rewrite lookup_total_insert. unfold regval_into_reg, sp'.
      rewrite add_vec_off2.
      f_equal; f_equal; vm_compute; reflexivity. }
    assert (Hm2den : vregs_den ρA mycpu_pro_regs1 = m2).
    { unfold mycpu_pro_regs1.
      rewrite -vregs_den_insert -vregs_den_insert HdenA.
      rewrite Hspv Hs0v.
      unfold m2, m1, regval_into_reg. reflexivity. }
    iEval (rewrite Hm2den) in "Hfile".
    (* the stored words: den (SX 1 0) = ra0, den (SX 8 0) = s00 *)
    assert (Hvra0 : sval_den ρA (SX 1 0) = ra0).
    { cbn [sval_den].
      replace (ρA 1%nat) with (m0 !!! Regidx (mword_of_int 1 : mword 5))
        by (unfold ρA; reflexivity).
      change (add_vec (m0 !!! Regidx (mword_of_int 1 : mword 5)) (mword_of_int 0))
        with (add_vec_int (m0 !!! Regidx (mword_of_int 1 : mword 5)) 0).
      rewrite avi0. reflexivity. }
    assert (Hvs00 : sval_den ρA (SX 8 0) = s00).
    { cbn [sval_den].
      replace (ρA 8%nat) with (m0 !!! Regidx (mword_of_int 8 : mword 5))
        by (unfold ρA; reflexivity).
      change (add_vec (m0 !!! Regidx (mword_of_int 8 : mword 5)) (mword_of_int 0))
        with (add_vec_int (m0 !!! Regidx (mword_of_int 8 : mword 5)) 0).
      rewrite avi0. reflexivity. }
    iEval (rewrite /vheap_own; cbn [vheap]; rewrite /mycpu_pro_heap1;
           cbn [big_opL fst snd];
           rewrite Hara Has0 Hvra0 Hvs00) in "Hheap".
    iDestruct "Hheap" as "(Hbra & Hbs0 & _)".
    (* pc: mword_of_int (mycpu+8) -> the hand-proof's add_vec_int spelling *)
    assert (Hpc8 : (mword_of_int (KernelSyms.mycpu + 8) : mword 64)
                   = add_vec_int pcE 8)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (cbn [vpc]; rewrite Hpc8) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* middle: the six value-computing instructions (as in wp_mycpu).       *)
    (* ------------------------------------------------------------------ *)
    iPoseProof (myi_08 with "Htext") as "Hi08".
    iPoseProof (myi_0a with "Htext") as "Hi0a".
    iPoseProof (myi_0c with "Htext") as "Hi0c".
    iPoseProof (myi_0e with "Htext") as "Hi0e".
    iPoseProof (myi_12 with "Htext") as "Hi12".
    iPoseProof (myi_16 with "Htext") as "Hi16".
    iPoseProof (myi_1e with "Htext") as "Hi1e".
    (* +0x08 c.mv a5,tp : a5 := tp *)
    iApply (wp_cmv_gpr_s_config root_ppn E Φ (add_vec_int pcE 8) a5_idx tp_idx m2
              mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi08 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    change (<[Regidx a5_idx := regval_into_reg (add_vec zero_reg (m2 !!! Regidx tp_idx))]> m2) with m3.
    (* +0x0a c.addiw a5,0 : a5 := sext32(a5) *)
    iApply (wp_caddiw_s root_ppn E Φ (add_vec_int pcE 10) a5_idx imm_addiw m3
              mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi0a [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    change (<[Regidx a5_idx := regval_into_reg (sign_extend' 64 (subrange_vec_dec (add_vec (m3 !!! Regidx a5_idx) (sign_extend' 64 (sign_extend' 12 imm_addiw))) 31 0))]> m3) with m4.
    (* +0x0c c.slli a5,7 : a5 := a5 << 7 *)
    iApply (wp_cslli_gpr_s_config root_ppn E Φ (add_vec_int pcE 12) (Regidx a5_idx) a5_idx shamt_slli m4
              mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 ltac:(reflexivity) ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi0c [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    change (<[Regidx a5_idx := regval_into_reg (shift_bits_left (m4 !!! Regidx a5_idx) (subrange_vec_dec shamt_slli (Z.sub log2_xlen 1) 0))]> m4) with m5.
    (* +0x0e auipc a0,0x11 : a0 := pc + off *)
    iApply (wp_auipc_s root_ppn E Φ (add_vec_int pcE 14) a0_idx imm_auipc m5
              mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi0e [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    change (<[Regidx a0_idx := regval_into_reg (add_vec (add_vec_int pcE 14) (auipc_off imm_auipc))]> m5) with m6.
    replace (add_vec_int (add_vec_int pcE 14) 4) with (add_vec_int pcE 18) by (vm_compute; reflexivity).
    (* +0x12 addi a0,a0,-1388 : a0 := &cpus *)
    iApply (wp_addi4_s root_ppn E Φ (add_vec_int pcE 18) a0_idx a0_idx imm_addi m6
              mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi12 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    change (<[Regidx a0_idx := regval_into_reg (add_vec (m6 !!! Regidx a0_idx) (sign_extend' 64 imm_addi))]> m6) with m7.
    replace (add_vec_int (add_vec_int pcE 18) 4) with (add_vec_int pcE 22) by (vm_compute; reflexivity).
    (* +0x16 c.add a0,a0,a5 : a0 := &cpus[cpuid] *)
    iApply (wp_cadd_s root_ppn E Φ (add_vec_int pcE 22) a0_idx a5_idx m7
              mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi16 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    change (<[Regidx a0_idx := regval_into_reg (add_vec (m7 !!! Regidx a0_idx) (m7 !!! Regidx a5_idx))]> m7) with m8.
    (* ------------------------------------------------------------------ *)
    (* SEAM 2: enter the epilogue block from the abstract file m8.          *)
    (* ------------------------------------------------------------------ *)
    assert (Hsp8 : m8 !!! Regidx csp_rs1 = sp').
    { unfold m8, m7, m6, m5, m4, m3, m2, m1.
      do 7 (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      rewrite lookup_total_insert. reflexivity. }
    iDestruct (gpr_file_dom with "Hfile") as "[%Hdom8 Hfile]".
    iDestruct (gpr_file_x0 m8 (mword_of_int 0) ltac:(vm_compute; reflexivity)
                 with "Hfile") as "[%Hx08 Hfile]".
    set (ρB := fun k : nat =>
           if (k <? 32)%nat
           then m8 !!! Regidx (mword_of_int (Z.of_nat k) : mword 5)
           else if Nat.eqb k 33 then ra0 else s00).
    assert (HdenB : vregs_den ρB vregs_init = m8).
    { apply (vregs_den_init_agree _ _ Hdom8 Hx08). intros k Hk.
      unfold ρB. rewrite (proj2 (Nat.ltb_lt k 32) Hk). reflexivity. }
    assert (HspB : ρB 2%nat = sp').
    { replace (ρB 2%nat) with (m8 !!! Regidx (mword_of_int 2 : mword 5))
        by (unfold ρB; reflexivity).
      rewrite Hcsp2. exact Hsp8. }
    assert (HaraB : sval_den ρB (SX 2 8) = pa_ra).
    { cbn [sval_den]. rewrite HspB.
      unfold pa_ra, a8_ra, ea_ra. f_equal;
      apply bv_eq; vm_compute; reflexivity. }
    assert (Has0B : sval_den ρB (SX 2 0) = pa_s0).
    { cbn [sval_den]. rewrite HspB.
      unfold pa_s0, a8_s0, ea_s0. f_equal;
      apply bv_eq; vm_compute; reflexivity. }
    assert (HvraB : sval_den ρB (SX 33 0) = ra0).
    { cbn [sval_den].
      replace (ρB 33%nat) with ra0 by (unfold ρB; reflexivity).
      change (add_vec ra0 (mword_of_int 0)) with (add_vec_int ra0 0).
      apply avi0. }
    assert (Hvs0B : sval_den ρB (SX 34 0) = s00).
    { cbn [sval_den].
      replace (ρB 34%nat) with s00 by (unfold ρB; reflexivity).
      change (add_vec s00 (mword_of_int 0)) with (add_vec_int s00 0).
      apply avi0. }
    assert (Hpc24 : add_vec_int (add_vec_int pcE 22) 2
                    = (mword_of_int (KernelSyms.mycpu + 24) : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc24) in "Hpc".
    iEval (rewrite -HdenB) in "Hfile".
    iDestruct (mycpu_epilogue_instrs with "Htext") as "Hbi2".
    iApply (wp_vc_block_s_den root_ppn mycpu_epilogue E Φ
              (VSt (KernelSyms.mycpu + 24) vregs_init mycpu_epi_heap [])
              (VSt (KernelSyms.mycpu + 30) mycpu_epi_regs1 mycpu_epi_heap [])
              ρB mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 mycpu_epilogue_run
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                    Hpc Hfile Hbi2 [Hbra Hbs0] []").
    { rewrite /vheap_own. cbn [vheap]. rewrite /mycpu_epi_heap.
      cbn [big_opL fst snd]. rewrite HaraB Has0B HvraB Hvs0B.
      iFrame "Hbra Hbs0". }
    { rewrite /vheap4_own. cbn [vheap4]. done. }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hheap _".
    (* SEAM 2 exit: the symbolic post-state denotes to m11 *)
    assert (Hsp16B : sval_den ρB (SX 2 16)
                     = add_vec (m10 !!! Regidx csp_rs1)
                               (sign_extend' 64 (sign_extend' 12 imm_dealloc))).
    { cbn [sval_den]. rewrite HspB.
      assert (Hsp10 : m10 !!! Regidx csp_rs1 = sp').
      { unfold m10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        unfold m9. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        exact Hsp8. }
      rewrite Hsp10. f_equal;
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hm11den : vregs_den ρB mycpu_epi_regs1 = m11).
    { unfold mycpu_epi_regs1.
      rewrite -vregs_den_insert -vregs_den_insert -vregs_den_insert HdenB.
      rewrite HvraB Hvs0B Hsp16B.
      unfold m11, m10, m9, regval_into_reg. reflexivity. }
    iEval (rewrite Hm11den) in "Hfile".
    iEval (rewrite /vheap_own; cbn [vheap]; rewrite /mycpu_epi_heap;
           cbn [big_opL fst snd];
           rewrite HaraB Has0B HvraB Hvs0B) in "Hheap".
    iDestruct "Hheap" as "(Hbra & Hbs0 & _)".
    (* +0x1e c.ret : PC := ra0 (low bit cleared) *)
    assert (Hra_final : m11 !!! Regidx ra_idx = ra0).
    { unfold m11. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      unfold m10. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      unfold m9. rewrite lookup_total_insert. reflexivity. }
    iApply (wp_cret_s_zca root_ppn E Φ (mword_of_int (KernelSyms.mycpu + 30)) ra_idx m11
              mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 ltac:(vm_compute; discriminate) Hlpe
              ltac:(rewrite Hra_final; exact Hal0)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi1e [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iEval (rewrite Hra_final) in "Hpc".
    (* the inlined body leaves the two cells at the let-folded [pa_ra]/[pa_s0]
       spellings; restate the [pa_stk] bridges in that form (convertible). *)
    assert (Hpra' : pa_ra = pa_stk sp0 1) by exact Hpra.
    assert (Hps0' : pa_s0 = pa_stk sp0 2) by exact Hps0.
    iEval (rewrite Hpra') in "Hbra".
    iEval (rewrite Hps0') in "Hbs0".
    iDestruct (stack_own_2_intro with "Hbra Hbs0") as "Htop".
    iDestruct (stack_own_split_2 sp0 2 n ltac:(lia) with "[$Htop $Hdeep]") as "Hstk".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hstk").
  Qed.

End WpMycpu.
