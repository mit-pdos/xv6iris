(* WpMemsetInstr.v -- discharge the instruction DECODINGS for all 16 memset
   instructions (0x80000ccc .. 0x80000cf0) from [kernel_text], then a corollary
   [wp_memset_s_full_kt] of [wp_memset_s_full] that assumes only [kernel_text]
   instead of the 16 [instr]/decode premises.

   The eight standard prologue/epilogue instructions (c.addi16sp / c.sdsp /
   c.ldsp / c.jr) share their byte patterns with WpTimerinit's, so their decode
   lemmas are reused verbatim; the other eight (c.mv / c.slli / c.srli / c.beqz /
   c.addi a5,1 and the three base add/sb/bne) get fresh decode lemmas here. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry.
Require Import WpGpr WpGprRvc.
Require Import SmodeCore WpSmodeGpr WpSmodeSret WpEntryNew WpMemsetS WpTimerinit.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Decode templates (mirrors of WpTimerinit's / WpStartNew's).           *)
(* ===================================================================== *)
Local Ltac m_reg_step name w hi lo s :=
  assert (name : exec (encdec_reg_backwards (subrange_vec_dec w hi lo)) s
              = Some (Regidx (autocast (T := mword)
                        (subrange_vec_dec (subrange_vec_dec w hi lo)
                           (Z.sub regidx_bit_width 1) 0)), s));
  [ unfold encdec_reg_backwards;
    match goal with |- context[if ?g then returnM (Regidx _) else _] =>
      replace g with true by (vm_compute; reflexivity) end; cbn match; apply exec_returnM
  | idtac ].

Local Ltac m_open_rvc s HmisaC :=
  unfold ext_decode_compressed, encdec_compressed_backwards; cbv beta; cbn zeta;
  skip_pure_clause; repeat (dstep s HmisaC);
  match goal with |- context[if ?g then _ else returnM None] =>
    replace g with true by (vm_compute; reflexivity) end;
  cbn match; rewrite exec_bind.

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
  intro H. m_reg_step Hr1 (mword_of_int 0x87aa : mword 16) 11 7 s.
  m_reg_step Hr2 (mword_of_int 0x87aa : mword 16) 6 2 s.
  m_open_rvc s H.
  rewrite (exec_bind_Some _ _ _ _ _ Hr1). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ Hr2). cbn beta.
  m_close1 s H.
Qed.

(* cd8: 0x1602 -> c.slli a2,32 *)
Lemma mdec_cd8 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x1602 : mword 16)) s = Some (C_SLLI (mword_of_int 32, Regidx (mword_of_int 12)), s).
Proof.
  intro H. m_reg_step Hr (mword_of_int 0x1602 : mword 16) 11 7 s.
  m_open_rvc s H.
  rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
  m_close1 s H.
Qed.

(* cda: 0x9201 -> c.srli a2,32 *)
Lemma mdec_cda s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x9201 : mword 16)) s = Some (C_SRLI (mword_of_int 32, Cregidx (mword_of_int 4)), s).
Proof.
  intro H. m_open_rvc s H. m_close1 s H.
Qed.

(* cd4: 0xca19 -> c.beqz a2,cea *)
Lemma mdec_cd4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xca19 : mword 16)) s = Some (C_BEQZ (mword_of_int 11, Cregidx (mword_of_int 4)), s).
Proof.
  intro H. m_open_rvc s H. m_close1 s H.
Qed.

(* ce4: 0x0785 -> c.addi a5,1 *)
Lemma mdec_ce4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0785 : mword 16)) s = Some (C_ADDI (mword_of_int 1, Regidx (mword_of_int 15)), s).
Proof.
  intro H. m_reg_step Hr (mword_of_int 0x0785 : mword 16) 11 7 s.
  m_open_rvc s H.
  rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
  m_close1 s H.
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

  Local Ltac mk_rvc4 A h w pc ast decname :=
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
    | iIntros (? ? ? ?) "_"; iPureIntro; intros; apply decname; assumption ].

  Local Ltac mk_rvc2 A h pc ast decname :=
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
    | iIntros (? ? ? ?) "_"; iPureIntro; intros; apply decname; assumption ].

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
    | iIntros (? ? ? ?) "_"; iPureIntro; intros; apply decname; assumption ].

  Lemma minstr_ccc : kernel_text -∗ instr (mword_of_int 0x80000ccc : mword 64) true (C_ADDI (mword_of_int 48, Regidx csp_rs1)).
  Proof. mk_rvc4 (0x80000ccc)%Z (mword_of_int 0x1141 : mword 16) (mword_of_int 0xe4061141 : mword 32)
           (mword_of_int 0x80000ccc : mword 64) (C_ADDI (mword_of_int 48, Regidx csp_rs1)) mdec_ccc. Qed.

  Lemma minstr_cce : kernel_text -∗ instr (mword_of_int 0x80000cce : mword 64) true (C_SDSP (mword_of_int 1, Regidx (mword_of_int 1))).
  Proof. mk_rvc2 (0x80000cce)%Z (mword_of_int 0xe406 : mword 16)
           (mword_of_int 0x80000cce : mword 64) (C_SDSP (mword_of_int 1, Regidx (mword_of_int 1))) mdec_cce. Qed.

  Lemma minstr_cd0 : kernel_text -∗ instr (mword_of_int 0x80000cd0 : mword 64) true (C_SDSP (mword_of_int 0, Regidx (mword_of_int 8))).
  Proof. mk_rvc4 (0x80000cd0)%Z (mword_of_int 0xe022 : mword 16) (mword_of_int 0x0800e022 : mword 32)
           (mword_of_int 0x80000cd0 : mword 64) (C_SDSP (mword_of_int 0, Regidx (mword_of_int 8))) mdec_cd0. Qed.

  Lemma minstr_cd2 : kernel_text -∗ instr (mword_of_int 0x80000cd2 : mword 64) true (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 4)).
  Proof. mk_rvc2 (0x80000cd2)%Z (mword_of_int 0x0800 : mword 16)
           (mword_of_int 0x80000cd2 : mword 64) (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 4)) mdec_cd2. Qed.

  Lemma minstr_cd4 : kernel_text -∗ instr (mword_of_int 0x80000cd4 : mword 64) true (C_BEQZ (mword_of_int 11, Cregidx (mword_of_int 4))).
  Proof. mk_rvc4 (0x80000cd4)%Z (mword_of_int 0xca19 : mword 16) (mword_of_int 0x87aaca19 : mword 32)
           (mword_of_int 0x80000cd4 : mword 64) (C_BEQZ (mword_of_int 11, Cregidx (mword_of_int 4))) mdec_cd4. Qed.

  Lemma minstr_cd6 : kernel_text -∗ instr (mword_of_int 0x80000cd6 : mword 64) true (C_MV (Regidx (mword_of_int 15), Regidx (mword_of_int 10))).
  Proof. mk_rvc2 (0x80000cd6)%Z (mword_of_int 0x87aa : mword 16)
           (mword_of_int 0x80000cd6 : mword 64) (C_MV (Regidx (mword_of_int 15), Regidx (mword_of_int 10))) mdec_cd6. Qed.

  Lemma minstr_cd8 : kernel_text -∗ instr (mword_of_int 0x80000cd8 : mword 64) true (C_SLLI (mword_of_int 32, Regidx (mword_of_int 12))).
  Proof. mk_rvc4 (0x80000cd8)%Z (mword_of_int 0x1602 : mword 16) (mword_of_int 0x92011602 : mword 32)
           (mword_of_int 0x80000cd8 : mword 64) (C_SLLI (mword_of_int 32, Regidx (mword_of_int 12))) mdec_cd8. Qed.

  Lemma minstr_cda : kernel_text -∗ instr (mword_of_int 0x80000cda : mword 64) true (C_SRLI (mword_of_int 32, Cregidx (mword_of_int 4))).
  Proof. mk_rvc2 (0x80000cda)%Z (mword_of_int 0x9201 : mword 16)
           (mword_of_int 0x80000cda : mword 64) (C_SRLI (mword_of_int 32, Cregidx (mword_of_int 4))) mdec_cda. Qed.

  Lemma minstr_cdc : kernel_text -∗ instr (mword_of_int 0x80000cdc : mword 64) false (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 12), Regidx (mword_of_int 14), ADD)).
  Proof. mk_base (0x80000cdc)%Z (mword_of_int 0x00a60733 : mword 32)
           (mword_of_int 0x80000cdc : mword 64) (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 12), Regidx (mword_of_int 14), ADD)) mdec_cdc. Qed.

  Lemma minstr_ce0 : kernel_text -∗ instr (mword_of_int 0x80000ce0 : mword 64) false (STORE (mword_of_int 0, Regidx (mword_of_int 11), Regidx (mword_of_int 15), 1)).
  Proof. mk_base (0x80000ce0)%Z (mword_of_int 0x00b78023 : mword 32)
           (mword_of_int 0x80000ce0 : mword 64) (STORE (mword_of_int 0, Regidx (mword_of_int 11), Regidx (mword_of_int 15), 1)) mdec_ce0. Qed.

  Lemma minstr_ce4 : kernel_text -∗ instr (mword_of_int 0x80000ce4 : mword 64) true (C_ADDI (mword_of_int 1, Regidx (mword_of_int 15))).
  Proof. mk_rvc4 (0x80000ce4)%Z (mword_of_int 0x0785 : mword 16) (mword_of_int 0x9de30785 : mword 32)
           (mword_of_int 0x80000ce4 : mword 64) (C_ADDI (mword_of_int 1, Regidx (mword_of_int 15))) mdec_ce4. Qed.

  Lemma minstr_ce6 : kernel_text -∗ instr (mword_of_int 0x80000ce6 : mword 64) false (BTYPE (mword_of_int 0x1ffa, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BNE)).
  Proof. mk_base (0x80000ce6)%Z (mword_of_int 0xfee79de3 : mword 32)
           (mword_of_int 0x80000ce6 : mword 64) (BTYPE (mword_of_int 0x1ffa, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BNE)) mdec_ce6. Qed.

  Lemma minstr_cea : kernel_text -∗ instr (mword_of_int 0x80000cea : mword 64) true (C_LDSP (mword_of_int 1, Regidx (mword_of_int 1))).
  Proof. mk_rvc2 (0x80000cea)%Z (mword_of_int 0x60a2 : mword 16)
           (mword_of_int 0x80000cea : mword 64) (C_LDSP (mword_of_int 1, Regidx (mword_of_int 1))) mdec_cea. Qed.

  Lemma minstr_cec : kernel_text -∗ instr (mword_of_int 0x80000cec : mword 64) true (C_LDSP (mword_of_int 0, Regidx (mword_of_int 8))).
  Proof. mk_rvc4 (0x80000cec)%Z (mword_of_int 0x6402 : mword 16) (mword_of_int 0x01416402 : mword 32)
           (mword_of_int 0x80000cec : mword 64) (C_LDSP (mword_of_int 0, Regidx (mword_of_int 8))) mdec_cec. Qed.

  Lemma minstr_cee : kernel_text -∗ instr (mword_of_int 0x80000cee : mword 64) true (C_ADDI (mword_of_int 16, Regidx csp_rs1)).
  Proof. mk_rvc2 (0x80000cee)%Z (mword_of_int 0x0141 : mword 16)
           (mword_of_int 0x80000cee : mword 64) (C_ADDI (mword_of_int 16, Regidx csp_rs1)) mdec_cee. Qed.

  Lemma minstr_cf0 : kernel_text -∗ instr (mword_of_int 0x80000cf0 : mword 64) true (C_JR (Regidx (mword_of_int 1))).
  Proof. mk_rvc4 (0x80000cf0)%Z (mword_of_int 0x8082 : mword 16) (mword_of_int 0x11418082 : mword 32)
           (mword_of_int 0x80000cf0 : mword 64) (C_JR (Regidx (mword_of_int 1))) mdec_cf0. Qed.

End WpMemsetInstr.
