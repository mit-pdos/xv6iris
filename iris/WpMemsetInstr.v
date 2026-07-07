(* WpMemsetInstr.v -- discharge the instruction DECODINGS for all 16 memset
   instructions (0x80000ccc .. 0x80000cf0) from [kernel_text], then a corollary
   [wp_memset_s_full_kt] of [wp_memset_s_full] that assumes only [kernel_text]
   instead of the 16 [instr]/decode premises.

   The eight standard prologue/epilogue instructions (c.addi16sp / c.sdsp /
   c.ldsp / c.jr) share their byte patterns with WpTimerinit's, so their decode
   lemmas are reused verbatim; the other eight (c.mv / c.slli / c.srli / c.beqz /
   c.addi a5,1 and the three base add/sb/bne) get fresh decode lemmas here. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry.
Require Import WpGpr WpGprRvc.
Require Import SmodeCore WpSmodeGpr WpSmodeSret WpEntryNew WpMemsetS WpTimerinit.
Require Import WpRvcBridge.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Decode templates.                                                      *)
(* ===================================================================== *)
Local Ltac m_ast :=
  first [ reflexivity
        | repeat f_equal;
          first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] ].

Local Ltac m_close1 s HmisaC :=
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; m_ast
  | apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |];
    apply exec_currentlyEnabled_Zca; exact HmisaC ].

Local Ltac m_close0 s HmisaC :=
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (currentlyEnabled Ext_Zca) s = Some (true, s)));
  [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; m_ast
  | apply (exec_currentlyEnabled_Zca s HmisaC) ].

(* ---- the eight reused prologue/epilogue decodes (bytes match WpTimerinit) ---- *)
Lemma mdec_ccc s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x1141 : mword 16)) s = Some (C_ADDI (mword_of_int 48, Regidx csp_rs1), s).
Proof. intro H. exact (ti_decode9 s H). Qed.

Lemma mdec_cce s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe406 : mword 16)) s = Some (C_SDSP (mword_of_int 1, Regidx (mword_of_int 1)), s).
Proof. intro H. exact (ti_decode10 s H). Qed.

Lemma mdec_cd0 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe022 : mword 16)) s = Some (C_SDSP (mword_of_int 0, Regidx (mword_of_int 8)), s).
Proof. intro H. exact (ti_decode11 s H). Qed.

Lemma mdec_cd2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0800 : mword 16)) s = Some (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 4), s).
Proof. intro H. exact (ti_decode12 s H). Qed.

Lemma mdec_cea s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x60a2 : mword 16)) s = Some (C_LDSP (mword_of_int 1, Regidx (mword_of_int 1)), s).
Proof. intro H. exact (ti_decode26 s H). Qed.

Lemma mdec_cec s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6402 : mword 16)) s = Some (C_LDSP (mword_of_int 0, Regidx (mword_of_int 8)), s).
Proof. intro H. exact (ti_decode27 s H). Qed.

Lemma mdec_cee s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0141 : mword 16)) s = Some (C_ADDI (mword_of_int 16, Regidx csp_rs1), s).
Proof. intro H. exact (ti_decode28 s H). Qed.

Lemma mdec_cf0 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8082 : mword 16)) s = Some (C_JR (Regidx (mword_of_int 1)), s).
Proof. intro H. exact (ti_decode29 s H). Qed.

(* ---- the five fresh RVC decodes ---- *)
(* cd6: 0x87aa -> c.mv a5,a0 *)
Lemma mdec_cd6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x87aa : mword 16)) s = Some (C_MV (Regidx (mword_of_int 15), Regidx (mword_of_int 10)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* cd8: 0x1602 -> c.slli a2,32 *)
Lemma mdec_cd8 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x1602 : mword 16)) s = Some (C_SLLI (mword_of_int 32, Regidx (mword_of_int 12)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* cda: 0x9201 -> c.srli a2,32 *)
Lemma mdec_cda s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x9201 : mword 16)) s = Some (C_SRLI (mword_of_int 32, Cregidx (mword_of_int 4)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* cd4: 0xca19 -> c.beqz a2,cea *)
Lemma mdec_cd4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xca19 : mword 16)) s = Some (C_BEQZ (mword_of_int 11, Cregidx (mword_of_int 4)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* ce4: 0x0785 -> c.addi a5,1 *)
Lemma mdec_ce4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0785 : mword 16)) s = Some (C_ADDI (mword_of_int 1, Regidx (mword_of_int 15)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* ---- the three base decodes (one-shot decode_any) ---- *)
(* cdc: 0x00a60733 -> add a4,a2,a0 *)
Lemma mdec_cdc s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0x00a60733 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 12), Regidx (mword_of_int 14), ADD), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.

(* ce0: 0x00b78023 -> sb a1,0(a5) *)
Lemma mdec_ce0 s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0x00b78023 : mword 32)) s
  = Some (STORE (mword_of_int 0, Regidx (mword_of_int 11), Regidx (mword_of_int 15), 1), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.

(* ce6: 0xfee79de3 -> bne a5,a4,ce0 *)
Lemma mdec_ce6 s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0xfee79de3 : mword 32)) s
  = Some (BTYPE (mword_of_int 0x1ffa, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BNE), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.

(* ===================================================================== *)
(* [instr] constructors from [kernel_text].                              *)
(* ===================================================================== *)
Section WpMemsetInstr.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* rvc constructors now target the ExecuteAs-EXPANDED base instruction:
     [instr pc true base], where [decname] decodes the compressed form i0 and
     [expname] is i0's [exec_execute_C_*] ExecuteAs-expansion into [base].
     (Mirrors WpKvInstr.kv_mk_rvc4 / kv_mk_rvc2.) *)
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

  (* Addresses are given as [KernelSyms.memset + offset]; the constructor names
     carry the concrete low-byte address in the relocated image (memset = 0xcba).
     The mod-4 alignment of the base changed from 0 (old 0xccc) to 2 (0xcba), so
     the rvc2 (2-byte window) / rvc4 (4-byte cross-boundary window) choice, and
     the 4-byte window values, differ from an unrelocated version.  The [mdec_*]
     decode lemmas are keyed by instruction BITS (address-independent), so they
     are reused as-is under their original names. *)

  (* +0x00  c.addi16sp sp,-16  ->  addi sp,sp,-16   (2-aligned -> rvc2) *)
  Lemma minstr_cba : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc2 (KernelSyms.memset + 0x00)%Z (mword_of_int 0x1141 : mword 16)
           (mword_of_int (KernelSyms.memset + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_ccc exec_execute_C_ADDI. Qed.

  (* +0x02  c.sdsp ra,8(sp)  ->  sd ra,8(sp)   (4-aligned -> rvc4) *)
  Lemma minstr_cbc : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc4 (KernelSyms.memset + 0x02)%Z (mword_of_int 0xe406 : mword 16) (mword_of_int 0xe022e406 : mword 32)
           (mword_of_int (KernelSyms.memset + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) mdec_cce exec_execute_C_SDSP. Qed.

  (* +0x04  c.sdsp s0,0(sp)  ->  sd s0,0(sp)   (2-aligned -> rvc2) *)
  Lemma minstr_cbe : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc2 (KernelSyms.memset + 0x04)%Z (mword_of_int 0xe022 : mword 16)
           (mword_of_int (KernelSyms.memset + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) mdec_cd0 exec_execute_C_SDSP. Qed.

  (* +0x06  c.addi4spn s0,sp,16  ->  addi s0,sp,16   (4-aligned -> rvc4) *)
  Lemma minstr_cc0 : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc4 (KernelSyms.memset + 0x06)%Z (mword_of_int 0x0800 : mword 16) (mword_of_int 0xca190800 : mword 32)
           (mword_of_int (KernelSyms.memset + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) mdec_cd2 exec_execute_C_ADDI4SPN. Qed.

  (* +0x08  c.beqz a2,+0x1e  ->  beq a2,x0,+0x1e   (2-aligned -> rvc2) *)
  Lemma minstr_cc2 : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x08) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 11 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 4)), BEQ)).
  Proof. mk_rvc2 (KernelSyms.memset + 0x08)%Z (mword_of_int 0xca19 : mword 16)
           (mword_of_int (KernelSyms.memset + 0x08) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 11 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 4)), BEQ)) mdec_cd4 exec_execute_C_BEQZ. Qed.

  (* +0x0a  c.mv a5,a0  ->  add a5,x0,a0   (4-aligned -> rvc4) *)
  Lemma minstr_cc4 : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x0a) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc4 (KernelSyms.memset + 0x0a)%Z (mword_of_int 0x87aa : mword 16) (mword_of_int 0x160287aa : mword 32)
           (mword_of_int (KernelSyms.memset + 0x0a) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 15), ADD)) mdec_cd6 exec_execute_C_MV. Qed.

  (* +0x0c  c.slli a2,32  ->  slli a2,a2,32   (2-aligned -> rvc2) *)
  Lemma minstr_cc6 : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x0c) : mword 64) true (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 12), Regidx (mword_of_int 12), SLLI)).
  Proof. mk_rvc2 (KernelSyms.memset + 0x0c)%Z (mword_of_int 0x1602 : mword 16)
           (mword_of_int (KernelSyms.memset + 0x0c) : mword 64) (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 12), Regidx (mword_of_int 12), SLLI)) mdec_cd8 exec_execute_C_SLLI. Qed.

  (* +0x0e  c.srli a2,32  ->  srli a2,a2,32   (4-aligned -> rvc4) *)
  Lemma minstr_cc8 : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x0e) : mword 64) true (SHIFTIOP (mword_of_int 32 : mword 6, creg2reg_idx (Cregidx (mword_of_int 4)), creg2reg_idx (Cregidx (mword_of_int 4)), SRLI)).
  Proof. mk_rvc4 (KernelSyms.memset + 0x0e)%Z (mword_of_int 0x9201 : mword 16) (mword_of_int 0x07339201 : mword 32)
           (mword_of_int (KernelSyms.memset + 0x0e) : mword 64) (SHIFTIOP (mword_of_int 32 : mword 6, creg2reg_idx (Cregidx (mword_of_int 4)), creg2reg_idx (Cregidx (mword_of_int 4)), SRLI)) mdec_cda exec_execute_C_SRLI. Qed.

  (* +0x10  add a4,a2,a0        (base, 2-aligned) *)
  Lemma minstr_cca : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x10) : mword 64) false (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 12), Regidx (mword_of_int 14), ADD)).
  Proof. mk_base (KernelSyms.memset + 0x10)%Z (mword_of_int 0x00a60733 : mword 32)
           (mword_of_int (KernelSyms.memset + 0x10) : mword 64) (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 12), Regidx (mword_of_int 14), ADD)) mdec_cdc. Qed.

  (* +0x14  sb a1,0(a5)  [LOOP head]  (base, 2-aligned) *)
  Lemma minstr_cce : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x14) : mword 64) false (STORE (mword_of_int 0, Regidx (mword_of_int 11), Regidx (mword_of_int 15), 1)).
  Proof. mk_base (KernelSyms.memset + 0x14)%Z (mword_of_int 0x00b78023 : mword 32)
           (mword_of_int (KernelSyms.memset + 0x14) : mword 64) (STORE (mword_of_int 0, Regidx (mword_of_int 11), Regidx (mword_of_int 15), 1)) mdec_ce0. Qed.

  (* +0x18  c.addi a5,1  ->  addi a5,a5,1   (2-aligned -> rvc2) *)
  Lemma minstr_cd2 : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x18) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc2 (KernelSyms.memset + 0x18)%Z (mword_of_int 0x0785 : mword 16)
           (mword_of_int (KernelSyms.memset + 0x18) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) mdec_ce4 exec_execute_C_ADDI. Qed.

  (* +0x1a  bne a5,a4,+0x14     (base, 4-aligned) *)
  Lemma minstr_cd4 : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x1a) : mword 64) false (BTYPE (mword_of_int 0x1ffa, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BNE)).
  Proof. mk_base (KernelSyms.memset + 0x1a)%Z (mword_of_int 0xfee79de3 : mword 32)
           (mword_of_int (KernelSyms.memset + 0x1a) : mword 64) (BTYPE (mword_of_int 0x1ffa, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BNE)) mdec_ce6. Qed.

  (* +0x1e  c.ldsp ra,8(sp)  ->  ld ra,8(sp)   (4-aligned -> rvc4) *)
  Lemma minstr_cd8 : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x1e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc4 (KernelSyms.memset + 0x1e)%Z (mword_of_int 0x60a2 : mword 16) (mword_of_int 0x640260a2 : mword 32)
           (mword_of_int (KernelSyms.memset + 0x1e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) mdec_cea exec_execute_C_LDSP. Qed.

  (* +0x20  c.ldsp s0,0(sp)  ->  ld s0,0(sp)   (2-aligned -> rvc2) *)
  Lemma minstr_cda : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x20) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc2 (KernelSyms.memset + 0x20)%Z (mword_of_int 0x6402 : mword 16)
           (mword_of_int (KernelSyms.memset + 0x20) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) mdec_cec exec_execute_C_LDSP. Qed.

  (* +0x22  c.addi16sp sp,16  ->  addi sp,sp,16   (4-aligned -> rvc4) *)
  Lemma minstr_cdc : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x22) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc4 (KernelSyms.memset + 0x22)%Z (mword_of_int 0x0141 : mword 16) (mword_of_int 0x80820141 : mword 32)
           (mword_of_int (KernelSyms.memset + 0x22) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_cee exec_execute_C_ADDI. Qed.

  (* +0x24  c.jr ra  (ret)  ->  jalr x0,0(ra)   (2-aligned -> rvc2) *)
  Lemma minstr_cde : kernel_text -∗ instr (mword_of_int (KernelSyms.memset + 0x24) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc2 (KernelSyms.memset + 0x24)%Z (mword_of_int 0x8082 : mword 16)
           (mword_of_int (KernelSyms.memset + 0x24) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) mdec_cf0 exec_execute_C_JR. Qed.

  (* =================================================================== *)
  (*  THE CAPSTONE: [wp_memset_s_full] with the sixteen instruction        *)
  (*  decodings discharged from [kernel_text].  Every [instr] premise is    *)
  (*  gone; the operand fields are the concrete decoded values.             *)
  (* =================================================================== *)

  Lemma wp_memset_s_full_kt (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (m0 : gmap regidx (mword 64)) (N : nat) (wval_add : mword 64)
      (svpn : mword 27) (olds : nat -> bv 8)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq : dfrac} :
    let ra_idx : mword 5 := mword_of_int 1 in
    let s0_idx : mword 5 := mword_of_int 8 in
    let a0_idx : mword 5 := mword_of_int 10 in
    let a1_idx : mword 5 := mword_of_int 11 in
    let a2_idx : mword 5 := mword_of_int 12 in
    let a4_idx : mword 5 := mword_of_int 14 in
    let a5_idx : mword 5 := mword_of_int 15 in
    let pcE := mword_of_int KernelSyms.memset in
    let pc0L : mword 64 := mword_of_int (KernelSyms.memset + 0x14) in
    let pcLS : mword 64 := mword_of_int (KernelSyms.memset + 0x1e) in
    let imm_entry : mword 6 := mword_of_int 48 in
    let shamt_l : mword 6 := mword_of_int 32 in
    let shamt_r : mword 6 := mword_of_int 32 in
    let imm_dealloc : mword 6 := mword_of_int 16 in
    let nzimm_s0 : mword 8 := mword_of_int 4 in
    let imm8_beqz : mword 8 := mword_of_int 11 in
    let i_add : instruction := RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 12), Regidx (mword_of_int 14), ADD) in
    let imm_bne : mword 13 := mword_of_int 0x1ffa in
    let sp' := add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry)) in
    let ra0 := m0 !!! Regidx ra_idx in
    let s00 := m0 !!! Regidx s0_idx in
    let p := m0 !!! Regidx a0_idx in
    let e := wval_add in
    let cval := m0 !!! Regidx a1_idx in
    let ea_ra := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let a8_ra := ea_ra in
    let pa_ra := a8_ra in
    let ea_s0 := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let a8_s0 := ea_s0 in
    let pa_s0 := a8_s0 in
    let m1 := <[Regidx csp_rs1 := regval_into_reg sp']> m0 in
    let m2 := <[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1 in
    let m3 := <[Regidx a5_idx := regval_into_reg (add_vec zero_reg (m2 !!! Regidx a0_idx))]> m2 in
    let m4 := <[Regidx a2_idx := regval_into_reg (shift_bits_left (m3 !!! Regidx a2_idx) (subrange_vec_dec shamt_l (Z.sub log2_xlen 1) 0))]> m3 in
    let m5 := <[Regidx a2_idx := regval_into_reg (shift_bits_right (m4 !!! Regidx a2_idx) (subrange_vec_dec shamt_r (Z.sub log2_xlen 1) 0))]> m4 in
    let m6 := <[Regidx a4_idx := regval_into_reg wval_add]> m5 in
    let ret_tgt := update_vec_dec (add_vec ra0 (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    let cbyte := nth_byte (autocast (T := mword) (subrange_vec_dec cval (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0 in
    ↑minstretN ⊆ E ->
    (1 <= N)%nat ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (forall s_pc : mstate,
       register_lookup nextPC s_pc.(sregs) = add_vec_int (add_vec_int pcE 16) 4 ->
       (if Z.eqb (uint a2_idx) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint a2_idx))) s_pc.(sregs)) = m5 !!! Regidx a2_idx ->
       (if Z.eqb (uint a0_idx) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint a0_idx))) s_pc.(sregs)) = m5 !!! Regidx a0_idx ->
       exec (execute i_add) s_pc
       = Some (RETIRE_SUCCESS, set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint a4_idx))) (regval_into_reg wval_add))) ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (m0 !!! Regidx a2_idx) zero_reg = false ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec ret_tgt 1) = false ->
    add_vec (add_vec_int pc0L 6) (sign_extend' 64 imm_bne) = pc0L ->
    eq_vec (access_vec_dec pc0L 0) ('b"0") = true ->
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    subrange_vec_dec svpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec svpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out svpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    (forall j : nat, (j < N)%nat ->
       neq_vec (bits_of_virtaddr (Virtaddr (ms_a8 (ms_addr p j))))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (ms_a8 (ms_addr p j)))) (Z.sub 39 1) 0)) = false) ->
    (forall j : nat, (j < N)%nat ->
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr (ms_a8 (ms_addr p j)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn) ->
    (forall j : nat, (j < N)%nat ->
       zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr (ms_a8 (ms_addr p j)))) (Z.sub pagesize_bits 1) 0)) = ms_a8 (ms_addr p j)) ->
    (forall j : nat, (j < N)%nat ->
       pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
         (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
         (uint (ms_pa (ms_addr p j))) (uint (to_bits 64 1)) = PMP_Match) ->
    (forall j : nat, add_vec (ms_addr p j) ms_incr1 = ms_addr p (S j)) ->
    (forall j : nat, (j < N)%nat -> neq_vec (ms_addr p (S j)) e = negb (Nat.eqb (S j) N)) ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m0 -∗
    pa_ra ↦₈ (bv_0 64) -∗
    pa_s0 ↦₈ (bv_0 64) -∗
    ([∗ list] j ∈ seq 0 N, (ms_pa (ms_addr p j)) ↦ₘ olds j) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is ret_tgt -∗
      pa_ra ↦₈ ra0 -∗
      pa_s0 ↦₈ s00 -∗
      ([∗ list] j ∈ seq 0 N, (ms_pa (ms_addr p j)) ↦ₘ cbyte) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ra_idx s0_idx a0_idx a1_idx a2_idx a4_idx a5_idx pcE pc0L pcLS
      imm_entry shamt_l shamt_r imm_dealloc nzimm_s0 imm8_beqz i_add imm_bne
      sp' ra0 s00 p e cval ea_ra a8_ra pa_ra ea_s0 a8_s0 pa_s0
      m1 m2 m3 m4 m5 m6 ret_tgt cbyte
      HN HNge1 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe
      HX Hcov Hpmpp Hpteregion Halignp
      Hbexec_add
      Hpmpcov HW_R HR_R
      Hn0 Hret0 Hret1 Hbne HpcL0 Hmask_b Hvpn2b Hmvpnb Hmppnb
      Hpb_canon Hpb_vpn Hpb_ident Hpb_range Hincr Hcmp.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
             #Htext Hpc Hfile Hbra Hbs0 Hbuf Hcont".
    (* derive the thirteen prefix/suffix instr resources from the text image *)
    iPoseProof (minstr_cba with "Htext") as "Hi0".
    iPoseProof (minstr_cbc with "Htext") as "Hi2".
    iPoseProof (minstr_cbe with "Htext") as "Hi4".
    iPoseProof (minstr_cc0 with "Htext") as "Hi6".
    iPoseProof (minstr_cc2 with "Htext") as "Hi8".
    iPoseProof (minstr_cc4 with "Htext") as "Hi10".
    iPoseProof (minstr_cc6 with "Htext") as "Hi12".
    iPoseProof (minstr_cc8 with "Htext") as "Hi14".
    iPoseProof (minstr_cca with "Htext") as "Hi16".
    iPoseProof (minstr_cd8 with "Htext") as "HiL0".
    iPoseProof (minstr_cda with "Htext") as "HiL2".
    iPoseProof (minstr_cdc with "Htext") as "HiL4".
    iPoseProof (minstr_cde with "Htext") as "HiL6".
    iApply (wp_memset_s_full root_ppn E Φ m0 N imm_entry shamt_l shamt_r imm_dealloc nzimm_s0 imm8_beqz
              i_add wval_add imm_bne svpn olds
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HNge1 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe
              HX Hcov Hpmpp Hpteregion Halignp
              Hbexec_add
              Hpmpcov HW_R HR_R
              Hn0 Hret0 Hret1 Hbne HpcL0 Hmask_b Hvpn2b Hmvpnb Hmppnb
              Hpb_canon Hpb_vpn Hpb_ident Hpb_range Hincr Hcmp
              minstr_cce minstr_cd2 minstr_cd4
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
                    Htext Hpc Hfile Hi0 Hi2 Hi4 Hi6 Hi8 Hi10 Hi12 Hi14 Hi16
                    HiL0 HiL2 HiL4 HiL6 Hbra Hbs0 Hbuf Hcont").
  Qed.

End WpMemsetInstr.
