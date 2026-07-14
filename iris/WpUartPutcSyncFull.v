(* WpUartPutcSyncFull.v -- the prologue/epilogue frame handling for
   uartputc_sync, on top of the body [wp_uartputc_body] (WpUartPutcSync.v),
   assembled into the whole-function WP [wp_uartputc].

   The prologue's three stack STORES (c.sdsp) and the epilogue's three stack
   LOADS (c.ldsp) have only [_scfg] (smode_config) leaves, so they are run
   through the VCgen (VcGenS.v) as [vop_s] blocks -- exactly as WpMycpu.v runs
   its prologue/epilogue.  The three instructions that are neither ordinary
   value-ALU ops nor stack-slot VCgen ops are handled by dedicated leaves:
     - c.mv  s1,a0     (0x96c) : [wp_cmv_gpr_s_config]  (WpSmodeRtype)
     - c.addi16sp sp,32 (0x9ae): [wp_caddi16sp_gpr_s_raw] (built below -- the
       library only ships the [_scfg] variant; +32 is out of c.addi's range so
       it cannot be folded into the VCgen block)
     - c.ret           (0x9b0) : [wp_cret_s_zca]        (WpSmodeJalr) *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes DevModel.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import WpDecode WpDecodeBridge WpRvcBridge KernelText StackOwn.
Require Import WpGpr WpGprRvc.
Require Import SmodePte Pt4kWalk KptPt SmodeCore CommonWalk.
Require Import WpMmodeLeafBase WpSmodeLeafBase.
Require Import WpSmodeItype WpSmodeRtype WpSmodeJalr.
Require Import WpMemsetInstr KernelRvcDecode.
Require Import VcGen VcGenS.
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
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* [instr]-builder templates, copied verbatim from WpUartPutcSync.v. *)
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

  (* --- [instr] facts for the three structural RVC instructions --- *)
  Lemma upi_0a : kernel_text -∗ instr (mword_of_int (UPS + 0x0a) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc4 (UPS + 0x0a)%Z (mword_of_int 0x84aa : mword 16) (mword_of_int 0xa79784aa : mword 32)
    (mword_of_int (UPS + 0x0a) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) uprvc_84aa exec_execute_C_MV. Qed.

  Lemma upi_4c : kernel_text -∗ instr (mword_of_int (UPS + 0x4c) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2), sp, sp, ADDI)).
  Proof. mk_rvc2 (UPS + 0x4c)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (UPS + 0x4c) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2), sp, sp, ADDI)) uprvc_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma upi_4e : kernel_text -∗ instr (mword_of_int (UPS + 0x4e) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc4 (UPS + 0x4e)%Z (mword_of_int 0x8082 : mword 16) (mword_of_int 0x00ef8082 : mword 32)
    (mword_of_int (UPS + 0x4e) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) mdec_cf0 exec_execute_C_JR. Qed.

  (* --- prologue frame [instr] facts (0x00 c.addi · 0x02/04/06 sd · 0x08 addi4spn) --- *)
  Lemma upi_00 : kernel_text -∗ instr (mword_of_int (UPS + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc2 (UPS + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (UPS + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) podec_00 exec_execute_C_ADDI. Qed.

  Lemma upi_02 : kernel_text -∗ instr (mword_of_int (UPS + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc4 (UPS + 0x02)%Z (mword_of_int 0xec06 : mword 16) (mword_of_int 0xe822ec06 : mword 32)
    (mword_of_int (UPS + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) podec_02 exec_execute_C_SDSP. Qed.

  Lemma upi_04 : kernel_text -∗ instr (mword_of_int (UPS + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc2 (UPS + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (UPS + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) podec_04 exec_execute_C_SDSP. Qed.

  Lemma upi_06 : kernel_text -∗ instr (mword_of_int (UPS + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc4 (UPS + 0x06)%Z (mword_of_int 0xe426 : mword 16) (mword_of_int 0x1000e426 : mword 32)
    (mword_of_int (UPS + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) podec_06 exec_execute_C_SDSP. Qed.

  Lemma upi_08 : kernel_text -∗ instr (mword_of_int (UPS + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc2 (UPS + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (UPS + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) podec_08 exec_execute_C_ADDI4SPN. Qed.

  (* --- epilogue frame [instr] facts (0x46/48/4a ld) --- *)
  Lemma upi_46 : kernel_text -∗ instr (mword_of_int (UPS + 0x46) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc4 (UPS + 0x46)%Z (mword_of_int 0x60e2 : mword 16) (mword_of_int 0x644260e2 : mword 32)
    (mword_of_int (UPS + 0x46) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) podec_22 exec_execute_C_LDSP. Qed.

  Lemma upi_48 : kernel_text -∗ instr (mword_of_int (UPS + 0x48) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc2 (UPS + 0x48)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (UPS + 0x48) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) podec_24 exec_execute_C_LDSP. Qed.

  Lemma upi_4a : kernel_text -∗ instr (mword_of_int (UPS + 0x4a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc4 (UPS + 0x4a)%Z (mword_of_int 0x64a2 : mword 16) (mword_of_int 0x610564a2 : mword 32)
    (mword_of_int (UPS + 0x4a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) podec_26 exec_execute_C_LDSP. Qed.

  (* ===================================================================== *)
  (*  Raw c.addi16sp leaf (the library ships only the [_scfg] variant).     *)
  (*  Mirrors [wp_caddi16sp_gpr_s] onto the raw [wp_gpr_write_s_config]      *)
  (*  engine, exactly as [wp_caddi_gpr_s_config] mirrors it for c.addi.      *)
  (* ===================================================================== *)
  Lemma wp_caddi16sp_gpr_s_raw (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm6 : mword 6)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm imm6)))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont".
    assert (Hsp : uint csp_rs1 <> 0) by (vm_compute; discriminate).
    unshelve iApply (wp_gpr_write_s_config root_ppn E Φ pc csp_rs1 csp_rs1 csp_rs1
              (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI))
              (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm imm6)))
              m mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hsp
              _
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    change sp with (Regidx csp_rs1).
    rewrite (exec_execute_ITYPE_ADDI_gpr csp_rs1 csp_rs1 (caddi16sp_imm imm6) s_pc).
    replace (Z.eqb (uint csp_rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hsp).
    unfold gpr_addi_val. rewrite Hva. reflexivity.
  Qed.

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
  (*  the low byte of the char [a0] is written to THR.  On exit ra/sp/s0/s1  *)
  (*  are restored (saved/restored via the 32-byte stack frame).            *)
  (* =================================================================== *)
  Lemma wp_uartputc (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (m0 : gmap regidx (mword 64)) (n : nat)
      (u u' : uart_state) (pv pkv : mword 32)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq dqm dqm2 : dfrac} :
    let ra_idx : mword 5 := mword_of_int 1 in
    let s0_idx : mword 5 := mword_of_int 8 in
    let s1_idx : mword 5 := mword_of_int 9 in
    let a0_idx : mword 5 := mword_of_int 10 in
    let pcE := mword_of_int UPS in
    let sp0 := m0 !!! Regidx csp_rs1 in
    let sp' := add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    let ra0 := m0 !!! Regidx ra_idx in
    let s00 := m0 !!! Regidx s0_idx in
    let s10 := m0 !!! Regidx s1_idx in
    let a00 := m0 !!! Regidx a0_idx in
    let ret_tgt := update_vec_dec (add_vec ra0 (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    (3 ≤ n)%nat ->
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
    eq_vec (sign_extend' 64 pv) zero_reg = false ->
    neq_vec (sign_extend' 64 pkv) zero_reg = false ->
    uart_thre u = true ->
    uart_write u 0 (autocast (T := mword)
       (subrange_vec_dec (and_vec (add_vec zero_reg a00)
          (sign_extend' 64 (mword_of_int 255 : mword 12))) 7 0) : mword 8) = Some u' ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗ cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗ mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗ kernel_text -∗
    pc_is pcE -∗ gpr_file m0 -∗
    stack_own sp0 n -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    uart_frag u -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗ cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗ mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is ret_tgt -∗
      (∃ mf, gpr_file mf ∗ ⌜ mf !!! Regidx ra_idx = ra0
                          /\ mf !!! Regidx s0_idx = s00
                          /\ mf !!! Regidx s1_idx = s10
                          /\ mf !!! Regidx csp_rs1 = sp0 ⌝) -∗
      stack_own sp0 n -∗
      (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
      (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
      uart_frag u' -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ra_idx s0_idx s1_idx a0_idx pcE sp0 sp' ra0 s00 s10 a00 ret_tgt.
    intros Hn3 HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 Hlpe Hal0 Hpv Hpkv Hthre Hwrite.
    set (ea_ra := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    set (ea_s0 := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    set (ea_s1 := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             #Htext Hpc Hfile Hstk Hpk Hpkd Huf Hcont".
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
    (* SEAM 1: run the prologue block.                                     *)
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
    { cbn [sval_den].
      replace (ρA 33%nat) with (raold : mword 64) by (unfold ρA; reflexivity).
      change (add_vec (raold : mword 64) (mword_of_int 0))
        with (add_vec_int (raold : mword 64) 0). apply avi0. }
    assert (Hvs0 : sval_den ρA (SX 34 0) = (s0old : mword 64)).
    { cbn [sval_den].
      replace (ρA 34%nat) with (s0old : mword 64) by (unfold ρA; reflexivity).
      change (add_vec (s0old : mword 64) (mword_of_int 0))
        with (add_vec_int (s0old : mword 64) 0). apply avi0. }
    assert (Hvs1 : sval_den ρA (SX 35 0) = (s1old : mword 64)).
    { cbn [sval_den].
      replace (ρA 35%nat) with (s1old : mword 64) by (unfold ρA; reflexivity).
      change (add_vec (s1old : mword 64) (mword_of_int 0))
        with (add_vec_int (s1old : mword 64) 0). apply avi0. }
    iDestruct (ups_prologue_instrs with "Htext") as "Hbi".
    iEval (rewrite -HdenA) in "Hfile".
    iApply (wp_vc_block_s_den root_ppn ups_prologue E Φ
              (VSt UPS vregs_init ups_pro_heap0 [])
              (VSt (UPS + 10) ups_pro_regs1 ups_pro_heap1 [])
              ρA mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 ups_prologue_run
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                    Hpc Hfile Hbi [Hbra Hbs0 Hbs1] []").
    { rewrite /vheap_own. cbn [vheap]. rewrite /ups_pro_heap0.
      cbn [big_opL fst snd]. rewrite Hara Has0 Has1 Hvra Hvs0 Hvs1.
      iFrame "Hbra Hbs0 Hbs1". }
    { rewrite /vheap4_own. cbn [vheap4]. done. }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hheap _".
    (* SEAM 1 exit: the post register file denotes to m2, the stored words to
       ra0/s00/s10. *)
    set (m1 := <[Regidx csp_rs1 := regval_into_reg sp']> m0).
    set (m2 := <[Regidx s0_idx := regval_into_reg
                  (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> m1).
    assert (Hspv : sval_den ρA (SX 2 (wrap64 (-32))) = sp').
    { cbn [sval_den].
      replace (ρA 2%nat) with (m0 !!! Regidx (mword_of_int 2 : mword 5))
        by (unfold ρA; reflexivity).
      rewrite Hcsp2. unfold sp'. f_equal; apply bv_eq; vm_compute; reflexivity. }
    assert (Hs0v : sval_den ρA (SX 2 0)
                   = add_vec (m1 !!! Regidx csp_rs1)
                             (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8)))).
    { cbn [sval_den].
      replace (ρA 2%nat) with (m0 !!! Regidx (mword_of_int 2 : mword 5))
        by (unfold ρA; reflexivity).
      rewrite Hcsp2. unfold m1. rewrite lookup_total_insert.
      unfold regval_into_reg, sp'. rewrite add_vec_off2.
      f_equal; f_equal; vm_compute; reflexivity. }
    assert (Hm2den : vregs_den ρA ups_pro_regs1 = m2).
    { unfold ups_pro_regs1.
      rewrite -vregs_den_insert -vregs_den_insert HdenA Hspv Hs0v.
      unfold m2, m1, regval_into_reg. reflexivity. }
    iEval (rewrite Hm2den) in "Hfile".
    (* the stored words: den (SX 1 0) = ra0, (SX 8 0) = s00, (SX 9 0) = s10 *)
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
    assert (Hvs10 : sval_den ρA (SX 9 0) = s10).
    { cbn [sval_den].
      replace (ρA 9%nat) with (m0 !!! Regidx (mword_of_int 9 : mword 5))
        by (unfold ρA; reflexivity).
      change (add_vec (m0 !!! Regidx (mword_of_int 9 : mword 5)) (mword_of_int 0))
        with (add_vec_int (m0 !!! Regidx (mword_of_int 9 : mword 5)) 0).
      rewrite avi0. reflexivity. }
    iEval (rewrite /vheap_own; cbn [vheap]; rewrite /ups_pro_heap1;
           cbn [big_opL fst snd];
           rewrite Hara Has0 Has1 Hvra0 Hvs00 Hvs10) in "Hheap".
    iDestruct "Hheap" as "(Hbra & Hbs0 & Hbs1 & _)".
    (* pc: mword_of_int (UPS+10) -> add_vec_int pcE 10 *)
    assert (Hpc10 : (mword_of_int (UPS + 10) : mword 64) = add_vec_int pcE 10)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (cbn [vpc]; rewrite Hpc10) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* c.mv s1,a0 at 0x96c: s1 := a0.                                       *)
    (* ------------------------------------------------------------------ *)
    iPoseProof (upi_0a with "Htext") as "Hi0a".
    iApply (wp_cmv_gpr_s_config root_ppn E Φ (add_vec_int pcE 10) s1_idx a0_idx m2
              mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi0a [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    set (m3 := <[Regidx s1_idx := regval_into_reg (add_vec zero_reg (m2 !!! Regidx a0_idx))]> m2).
    change (<[Regidx s1_idx := regval_into_reg (add_vec zero_reg (m2 !!! Regidx a0_idx))]> m2) with m3.
    (* ------------------------------------------------------------------ *)
    (* the body (0x96e -> 0x9a8) via [wp_uartputc_body].                    *)
    (* ------------------------------------------------------------------ *)
    assert (Ha0_23 : m2 !!! Regidx a0_idx = a00).
    { unfold m2, m1. do 2 (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      reflexivity. }
    assert (HR9m3 : m3 !!! Regidx (mword_of_int 9) = add_vec zero_reg a00).
    { unfold m3. change (Regidx s1_idx) with (Regidx (mword_of_int 9)).
      rewrite lookup_total_insert. unfold regval_into_reg. rewrite Ha0_23. reflexivity. }
    assert (Hpc0c : add_vec_int (add_vec_int pcE 10) 2
                    = (mword_of_int (UPS + 0x0c) : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    iApply (wp_uartputc_body root_ppn E Φ m3 u u' pv pkv mstatus0 mie_v mdv0 menvcfg0
              (dq:=dq) (dqm:=dqm) (dqm2:=dqm2)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 Hpv Hpkv Hthre
              ltac:(rewrite HR9m3; exact Hwrite)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Htext Hpc Hfile Hpk Hpkd Huf").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hbody Hpk Hpkd Huf".
    iDestruct "Hbody" as (mf) "[Hfile %Hbagr]".
    destruct Hbagr as (Hbra_ag & Hbs0_ag & Hbsp_ag).
    (* ra/s0/sp of [mf] agree with m3 (== ra0/s00/sp'). *)
    assert (Hmf_ra : mf !!! Regidx (mword_of_int 1) = ra0).
    { rewrite Hbra_ag. unfold m3.
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      unfold m2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      unfold m1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      reflexivity. }
    assert (Hmf_sp : mf !!! Regidx (mword_of_int 2) = sp').
    { rewrite Hbsp_ag. unfold m3.
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      unfold m2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      unfold m1. change (Regidx (mword_of_int 2)) with (Regidx csp_rs1).
      rewrite lookup_total_insert. reflexivity. }
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
    { cbn [sval_den].
      replace (ρB 33%nat) with ra0 by (unfold ρB; reflexivity).
      change (add_vec ra0 (mword_of_int 0)) with (add_vec_int ra0 0). apply avi0. }
    assert (Hvs0B : sval_den ρB (SX 34 0) = s00).
    { cbn [sval_den].
      replace (ρB 34%nat) with s00 by (unfold ρB; reflexivity).
      change (add_vec s00 (mword_of_int 0)) with (add_vec_int s00 0). apply avi0. }
    assert (Hvs1B : sval_den ρB (SX 35 0) = s10).
    { cbn [sval_den].
      replace (ρB 35%nat) with s10 by (unfold ρB; reflexivity).
      change (add_vec s10 (mword_of_int 0)) with (add_vec_int s10 0). apply avi0. }
    assert (Hpc46 : (mword_of_int (UPS + 0x46) : mword 64)
                    = (mword_of_int (UPS + 0x46) : mword 64)) by reflexivity.
    iEval (rewrite -HdenB) in "Hfile".
    iDestruct (ups_epilogue_instrs with "Htext") as "Hbi2".
    iApply (wp_vc_block_s_den root_ppn ups_epilogue E Φ
              (VSt (UPS + 0x46) vregs_init ups_epi_heap [])
              (VSt (UPS + 0x46 + 6) ups_epi_regs1 ups_epi_heap [])
              ρB mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 ups_epilogue_run
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                    Hpc Hfile Hbi2 [Hbra Hbs0 Hbs1] []").
    { rewrite /vheap_own. cbn [vheap]. rewrite /ups_epi_heap.
      cbn [big_opL fst snd]. rewrite HaraB Has0B Has1B HvraB Hvs0B Hvs1B.
      rewrite Hpra Hps0 Hps1. iFrame "Hbra Hbs0 Hbs1". }
    { rewrite /vheap4_own. cbn [vheap4]. done. }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hheap _".
    (* SEAM 2 exit: the post register file denotes to [m_epi], and the cells
       still hold ra0/s00/s10. *)
    set (m_epi := <[Regidx (mword_of_int 9 : mword 5) := s10]>
                   (<[Regidx (mword_of_int 8 : mword 5) := s00]>
                     (<[Regidx (mword_of_int 1 : mword 5) := ra0]> mf))).
    assert (Hmepiden : vregs_den ρB ups_epi_regs1 = m_epi).
    { unfold ups_epi_regs1.
      rewrite -vregs_den_insert -vregs_den_insert -vregs_den_insert HdenB
              HvraB Hvs0B Hvs1B. reflexivity. }
    iEval (rewrite Hmepiden) in "Hfile".
    iEval (rewrite /vheap_own; cbn [vheap]; rewrite /ups_epi_heap;
           cbn [big_opL fst snd];
           rewrite HaraB Has0B Has1B HvraB Hvs0B Hvs1B) in "Hheap".
    iDestruct "Hheap" as "(Hbra & Hbs0 & Hbs1 & _)".
    (* ------------------------------------------------------------------ *)
    (* c.addi16sp sp,32 at 0x9ae: sp := sp + 32 = sp0.                      *)
    (* ------------------------------------------------------------------ *)
    iPoseProof (upi_4c with "Htext") as "Hi4c".
    assert (Hpc4c : (mword_of_int (UPS + 0x46 + 6) : mword 64)
                    = (mword_of_int (UPS + 0x4c) : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (cbn [vpc]; rewrite Hpc4c) in "Hpc".
    iApply (wp_caddi16sp_gpr_s_raw root_ppn E Φ (mword_of_int (UPS + 0x4c)) (mword_of_int 2) m_epi
              mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi4c [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    set (m_epi2 := <[Regidx csp_rs1 := regval_into_reg
                      (add_vec (m_epi !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2))))]> m_epi).
    change (<[Regidx csp_rs1 := regval_into_reg
              (add_vec (m_epi !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2))))]> m_epi) with m_epi2.
    (* ------------------------------------------------------------------ *)
    (* c.ret at 0x9b0: PC := ra (= ra0).                                    *)
    (* ------------------------------------------------------------------ *)
    iPoseProof (upi_4e with "Htext") as "Hi4e".
    assert (Hra_final : m_epi2 !!! Regidx (mword_of_int 1) = ra0).
    { unfold m_epi2.
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      unfold m_epi.
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite lookup_total_insert. reflexivity. }
    assert (Hpc4e : add_vec_int (mword_of_int (UPS + 0x4c)) 2
                    = (mword_of_int (UPS + 0x4e) : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc4e) in "Hpc".
    iApply (wp_cret_s_zca root_ppn E Φ (mword_of_int (UPS + 0x4e)) (mword_of_int 1) m_epi2
              mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 ltac:(vm_compute; discriminate) Hlpe
              ltac:(rewrite Hra_final; exact Hal0)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi4e [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iEval (rewrite Hra_final) in "Hpc".
    (* rebundle the frame: the cells hold ra0/s00/s10 at pa_stk 1/2/3. *)
    iEval (rewrite Hpra) in "Hbra".
    iEval (rewrite Hps0) in "Hbs0".
    iEval (rewrite Hps1) in "Hbs1".
    iDestruct (stack_own_3_intro with "Hbra Hbs0 Hbs1") as "Htop".
    iDestruct (stack_own_split_2 sp0 3 n ltac:(lia) with "[$Htop $Hdeep]") as "Hstk".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc [Hfile] Hstk Hpk Hpkd Huf").
    iExists m_epi2. iFrame "Hfile". iPureIntro.
    (* ra/s0/s1/sp restored to their entry values. *)
    split; [| split; [| split]].
    - exact Hra_final.
    - unfold m_epi2.
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      unfold m_epi.
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite lookup_total_insert. reflexivity.
    - unfold m_epi2.
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      unfold m_epi. rewrite lookup_total_insert. reflexivity.
    - unfold m_epi2. rewrite lookup_total_insert.
      unfold regval_into_reg. unfold m_epi.
      do 3 (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      rewrite Hmf_sp. unfold sp', sp0.
      change (caddi16sp_imm (mword_of_int 2)) with (caddi16sp_imm (mword_of_int 2 : mword 6)).
      apply ups_frame_cancel.
  Qed.

End WpUartPutcSyncFull.
