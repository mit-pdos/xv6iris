(* WpKvInstr.v -- K3: the 38 kernelvec instructions (kernel-rocq dump,
   0x800053e0 .. 0x8000542c) as decode lemmas + [instr] constructors from
   [kernel_text].  Instr #1 (the c.addi16sp sp,-256 at 0x800053e0) is
   SmodeCore's [kv_decode1] / [kv_instr1]; this file provides #2..#38:
   17 c.sdsp saves, the jal into kerneltrap, 17 c.ldsp restores, the
   c.addi16sp sp,+256, and the closing sret.  Decode templates are
   WpTimerinit's; constructor templates are WpTimerinit's ti_mk_*. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry.
Require Import WpGpr WpGprRvc.
Require Import WpRvcBridge.
Require Import SmodeCore WpSmodeGpr WpSmodeSret WpEntryNew.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
Local Open Scope Z_scope.
Import Defs.

(* One-shot decode via the symbolic bridge (WpRvcBridge): rewrite the decoder
   to its read-free form and vm_compute it (~0.01s), instead of walking the
   ~55-clause compressed-decode match by hand.  [h] is now implicit in the goal. *)
Local Ltac kv_dec_sd h s HmisaC := rvc_oneshot s HmisaC.
Local Ltac kv_dec_ld h s HmisaC := rvc_oneshot s HmisaC.

Lemma kv_dec2 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe006 : mword 16)) s
  = Some (C_SDSP (mword_of_int 0 : mword 6, Regidx (mword_of_int 1 : mword 5)), s).
Proof. intro HmisaC. kv_dec_sd (mword_of_int 0xe006 : mword 16) s HmisaC. Qed.

Lemma kv_dec3 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe80e : mword 16)) s
  = Some (C_SDSP (mword_of_int 2 : mword 6, Regidx (mword_of_int 3 : mword 5)), s).
Proof. intro HmisaC. kv_dec_sd (mword_of_int 0xe80e : mword 16) s HmisaC. Qed.

Lemma kv_dec4 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf016 : mword 16)) s
  = Some (C_SDSP (mword_of_int 4 : mword 6, Regidx (mword_of_int 5 : mword 5)), s).
Proof. intro HmisaC. kv_dec_sd (mword_of_int 0xf016 : mword 16) s HmisaC. Qed.

Lemma kv_dec5 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf41a : mword 16)) s
  = Some (C_SDSP (mword_of_int 5 : mword 6, Regidx (mword_of_int 6 : mword 5)), s).
Proof. intro HmisaC. kv_dec_sd (mword_of_int 0xf41a : mword 16) s HmisaC. Qed.

Lemma kv_dec6 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf81e : mword 16)) s
  = Some (C_SDSP (mword_of_int 6 : mword 6, Regidx (mword_of_int 7 : mword 5)), s).
Proof. intro HmisaC. kv_dec_sd (mword_of_int 0xf81e : mword 16) s HmisaC. Qed.

Lemma kv_dec7 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe4aa : mword 16)) s
  = Some (C_SDSP (mword_of_int 9 : mword 6, Regidx (mword_of_int 10 : mword 5)), s).
Proof. intro HmisaC. kv_dec_sd (mword_of_int 0xe4aa : mword 16) s HmisaC. Qed.

Lemma kv_dec8 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe8ae : mword 16)) s
  = Some (C_SDSP (mword_of_int 10 : mword 6, Regidx (mword_of_int 11 : mword 5)), s).
Proof. intro HmisaC. kv_dec_sd (mword_of_int 0xe8ae : mword 16) s HmisaC. Qed.

Lemma kv_dec9 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xecb2 : mword 16)) s
  = Some (C_SDSP (mword_of_int 11 : mword 6, Regidx (mword_of_int 12 : mword 5)), s).
Proof. intro HmisaC. kv_dec_sd (mword_of_int 0xecb2 : mword 16) s HmisaC. Qed.

Lemma kv_dec10 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf0b6 : mword 16)) s
  = Some (C_SDSP (mword_of_int 12 : mword 6, Regidx (mword_of_int 13 : mword 5)), s).
Proof. intro HmisaC. kv_dec_sd (mword_of_int 0xf0b6 : mword 16) s HmisaC. Qed.

Lemma kv_dec11 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf4ba : mword 16)) s
  = Some (C_SDSP (mword_of_int 13 : mword 6, Regidx (mword_of_int 14 : mword 5)), s).
Proof. intro HmisaC. kv_dec_sd (mword_of_int 0xf4ba : mword 16) s HmisaC. Qed.

Lemma kv_dec12 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf8be : mword 16)) s
  = Some (C_SDSP (mword_of_int 14 : mword 6, Regidx (mword_of_int 15 : mword 5)), s).
Proof. intro HmisaC. kv_dec_sd (mword_of_int 0xf8be : mword 16) s HmisaC. Qed.

Lemma kv_dec13 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xfcc2 : mword 16)) s
  = Some (C_SDSP (mword_of_int 15 : mword 6, Regidx (mword_of_int 16 : mword 5)), s).
Proof. intro HmisaC. kv_dec_sd (mword_of_int 0xfcc2 : mword 16) s HmisaC. Qed.

Lemma kv_dec14 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe146 : mword 16)) s
  = Some (C_SDSP (mword_of_int 16 : mword 6, Regidx (mword_of_int 17 : mword 5)), s).
Proof. intro HmisaC. kv_dec_sd (mword_of_int 0xe146 : mword 16) s HmisaC. Qed.

Lemma kv_dec15 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xedf2 : mword 16)) s
  = Some (C_SDSP (mword_of_int 27 : mword 6, Regidx (mword_of_int 28 : mword 5)), s).
Proof. intro HmisaC. kv_dec_sd (mword_of_int 0xedf2 : mword 16) s HmisaC. Qed.

Lemma kv_dec16 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf1f6 : mword 16)) s
  = Some (C_SDSP (mword_of_int 28 : mword 6, Regidx (mword_of_int 29 : mword 5)), s).
Proof. intro HmisaC. kv_dec_sd (mword_of_int 0xf1f6 : mword 16) s HmisaC. Qed.

Lemma kv_dec17 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf5fa : mword 16)) s
  = Some (C_SDSP (mword_of_int 29 : mword 6, Regidx (mword_of_int 30 : mword 5)), s).
Proof. intro HmisaC. kv_dec_sd (mword_of_int 0xf5fa : mword 16) s HmisaC. Qed.

Lemma kv_dec18 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf9fe : mword 16)) s
  = Some (C_SDSP (mword_of_int 30 : mword 6, Regidx (mword_of_int 31 : mword 5)), s).
Proof. intro HmisaC. kv_dec_sd (mword_of_int 0xf9fe : mword 16) s HmisaC. Qed.

Lemma kv_dec19 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa46fd0ef : mword 32)) s
  = Some (JAL (mword_of_int 0x1fd246 : mword 21, Regidx (mword_of_int 1 : mword 5)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Lemma kv_dec20 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6082 : mword 16)) s
  = Some (C_LDSP (mword_of_int 0 : mword 6, Regidx (mword_of_int 1 : mword 5)), s).
Proof. intro HmisaC. kv_dec_ld (mword_of_int 0x6082 : mword 16) s HmisaC. Qed.

Lemma kv_dec21 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x61c2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 2 : mword 6, Regidx (mword_of_int 3 : mword 5)), s).
Proof. intro HmisaC. kv_dec_ld (mword_of_int 0x61c2 : mword 16) s HmisaC. Qed.

Lemma kv_dec22 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7282 : mword 16)) s
  = Some (C_LDSP (mword_of_int 4 : mword 6, Regidx (mword_of_int 5 : mword 5)), s).
Proof. intro HmisaC. kv_dec_ld (mword_of_int 0x7282 : mword 16) s HmisaC. Qed.

Lemma kv_dec23 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7322 : mword 16)) s
  = Some (C_LDSP (mword_of_int 5 : mword 6, Regidx (mword_of_int 6 : mword 5)), s).
Proof. intro HmisaC. kv_dec_ld (mword_of_int 0x7322 : mword 16) s HmisaC. Qed.

Lemma kv_dec24 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x73c2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 6 : mword 6, Regidx (mword_of_int 7 : mword 5)), s).
Proof. intro HmisaC. kv_dec_ld (mword_of_int 0x73c2 : mword 16) s HmisaC. Qed.

Lemma kv_dec25 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6526 : mword 16)) s
  = Some (C_LDSP (mword_of_int 9 : mword 6, Regidx (mword_of_int 10 : mword 5)), s).
Proof. intro HmisaC. kv_dec_ld (mword_of_int 0x6526 : mword 16) s HmisaC. Qed.

Lemma kv_dec26 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x65c6 : mword 16)) s
  = Some (C_LDSP (mword_of_int 10 : mword 6, Regidx (mword_of_int 11 : mword 5)), s).
Proof. intro HmisaC. kv_dec_ld (mword_of_int 0x65c6 : mword 16) s HmisaC. Qed.

Lemma kv_dec27 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6666 : mword 16)) s
  = Some (C_LDSP (mword_of_int 11 : mword 6, Regidx (mword_of_int 12 : mword 5)), s).
Proof. intro HmisaC. kv_dec_ld (mword_of_int 0x6666 : mword 16) s HmisaC. Qed.

Lemma kv_dec28 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7686 : mword 16)) s
  = Some (C_LDSP (mword_of_int 12 : mword 6, Regidx (mword_of_int 13 : mword 5)), s).
Proof. intro HmisaC. kv_dec_ld (mword_of_int 0x7686 : mword 16) s HmisaC. Qed.

Lemma kv_dec29 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7726 : mword 16)) s
  = Some (C_LDSP (mword_of_int 13 : mword 6, Regidx (mword_of_int 14 : mword 5)), s).
Proof. intro HmisaC. kv_dec_ld (mword_of_int 0x7726 : mword 16) s HmisaC. Qed.

Lemma kv_dec30 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x77c6 : mword 16)) s
  = Some (C_LDSP (mword_of_int 14 : mword 6, Regidx (mword_of_int 15 : mword 5)), s).
Proof. intro HmisaC. kv_dec_ld (mword_of_int 0x77c6 : mword 16) s HmisaC. Qed.

Lemma kv_dec31 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7866 : mword 16)) s
  = Some (C_LDSP (mword_of_int 15 : mword 6, Regidx (mword_of_int 16 : mword 5)), s).
Proof. intro HmisaC. kv_dec_ld (mword_of_int 0x7866 : mword 16) s HmisaC. Qed.

Lemma kv_dec32 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x688a : mword 16)) s
  = Some (C_LDSP (mword_of_int 16 : mword 6, Regidx (mword_of_int 17 : mword 5)), s).
Proof. intro HmisaC. kv_dec_ld (mword_of_int 0x688a : mword 16) s HmisaC. Qed.

Lemma kv_dec33 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6e6e : mword 16)) s
  = Some (C_LDSP (mword_of_int 27 : mword 6, Regidx (mword_of_int 28 : mword 5)), s).
Proof. intro HmisaC. kv_dec_ld (mword_of_int 0x6e6e : mword 16) s HmisaC. Qed.

Lemma kv_dec34 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7e8e : mword 16)) s
  = Some (C_LDSP (mword_of_int 28 : mword 6, Regidx (mword_of_int 29 : mword 5)), s).
Proof. intro HmisaC. kv_dec_ld (mword_of_int 0x7e8e : mword 16) s HmisaC. Qed.

Lemma kv_dec35 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7f2e : mword 16)) s
  = Some (C_LDSP (mword_of_int 29 : mword 6, Regidx (mword_of_int 30 : mword 5)), s).
Proof. intro HmisaC. kv_dec_ld (mword_of_int 0x7f2e : mword 16) s HmisaC. Qed.

Lemma kv_dec36 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7fce : mword 16)) s
  = Some (C_LDSP (mword_of_int 30 : mword 6, Regidx (mword_of_int 31 : mword 5)), s).
Proof. intro HmisaC. kv_dec_ld (mword_of_int 0x7fce : mword 16) s HmisaC. Qed.

Lemma kv_dec37 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6111 : mword 16)) s
  = Some (C_ADDI16SP (mword_of_int 16 : mword 6), s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

(* SRET decode: mirror of WpGprMretWp's [decode_mret] with the SRET clause
   (the ECALL/MRET/SRET flat clause has PURE vec-eq guards; no Ext_S gate). *)
Lemma kv_dec38 s :
  priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0x10200073 : mword 32)) s = Some (SRET tt, s).
Proof.
  intro Hpriv.
  unfold ext_decode, encdec_backwards. cbv beta. cbn zeta.
  skip_pure_clause.
  skip_pure_clause.
  match goal with |- context[eq_vec ?w0 ?c] =>
    replace (eq_vec w0 c) with false by (vm_compute; reflexivity) end.
  match goal with |- context[eq_vec (subrange_vec_dec ?w0 11 0) ?c] =>
    replace (eq_vec (subrange_vec_dec w0 11 0) c) with false by (vm_compute; reflexivity) end.
  assert (HA1 : exec (Defs.and_boolM (currentlyEnabled Ext_Zihintpause) (returnM false)) s
                = Some (false, s)).
  { destruct (exec_cE_pause s) as [bp Hbp].
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hbp). destruct bp; [apply exec_returnm | reflexivity]. }
  rewrite (exec_bind_Some _ _ _ _ _ HA1). cbn match.
  rewrite exec_bind.
  assert (HA2 : exec (Defs.and_boolM (currentlyEnabled Ext_Zicfilp) (returnM false)) s
                = Some (false, s)).
  { destruct (exec_cE_zicfilp_mSU s Hpriv) as [bz Hbz].
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hbz). destruct bz; [apply exec_returnm | reflexivity]. }
  rewrite (exec_bind_Some _ _ _ _ _ HA2). cbn match.
  match goal with |- context[if ?g then _ else returnM None] =>
    replace g with false by (vm_compute; reflexivity) end.
  cbn match.
  rewrite (exec_returnM (@None instruction) s). cbn match.
  skip_pure_clauses.
  match goal with |- context[if ?g then returnM (Some (ECALL tt)) else _] =>
    replace g with false by (vm_compute; reflexivity) end.
  match goal with |- context[if ?g then returnM (Some (MRET tt)) else _] =>
    replace g with false by (vm_compute; reflexivity) end.
  match goal with |- context[if ?g then returnM (Some (SRET tt)) else _] =>
    replace g with true by (vm_compute; reflexivity) end.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (Some (SRET tt)) s)). cbn match.
  apply exec_returnM.
Qed.


(* ===================================================================== *)
(* [instr] constructors from [kernel_text] (WpTimerinit ti_mk templates).  *)
(* ===================================================================== *)
Section WpKvInstr.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Local Ltac kv_mk_rvc4 A h w pc ast decname expname :=
    let Hlpad := fresh "Hlpad" in
    let H2al := fresh "H2al" in
    let H4al := fresh "H4al" in
    let Hrvc := fresh "Hrvc" in
    let Hsub := fresh "Hsub" in
    let Hbytes := fresh "Hbytes" in
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

  Local Ltac kv_mk_rvc2 A h pc ast decname expname :=
    let Hlpad := fresh "Hlpad" in
    let H2al := fresh "H2al" in
    let H4al := fresh "H4al" in
    let Hrvc := fresh "Hrvc" in
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

  Local Ltac kv_mk_base A w pc ast decname :=
    let Hlpad := fresh "Hlpad" in
    let H2al := fresh "H2al" in
    let Hnrvc := fresh "Hnrvc" in
    let Hbytes := fresh "Hbytes" in
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

  Lemma kv_i2 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x2) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 1 : mword 5), sp, 8)).
  Proof.
    kv_mk_rvc2 (KernelSyms.kernelvec + 0x2) (mword_of_int 0xe006 : mword 16)
      (mword_of_int (KernelSyms.kernelvec + 0x2) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 1 : mword 5), sp, 8)) kv_dec2 exec_execute_C_SDSP.
  Qed.

  Lemma kv_i3 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x4) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 3 : mword 5), sp, 8)).
  Proof.
    kv_mk_rvc4 (KernelSyms.kernelvec + 0x4) (mword_of_int 0xe80e : mword 16) (mword_of_int 0xf016e80e : mword 32)
      (mword_of_int (KernelSyms.kernelvec + 0x4) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 3 : mword 5), sp, 8)) kv_dec3 exec_execute_C_SDSP.
  Qed.

  Lemma kv_i4 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x6) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 5 : mword 5), sp, 8)).
  Proof.
    kv_mk_rvc2 (KernelSyms.kernelvec + 0x6) (mword_of_int 0xf016 : mword 16)
      (mword_of_int (KernelSyms.kernelvec + 0x6) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 5 : mword 5), sp, 8)) kv_dec4 exec_execute_C_SDSP.
  Qed.

  Lemma kv_i5 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x8) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 6 : mword 5), sp, 8)).
  Proof.
    kv_mk_rvc4 (KernelSyms.kernelvec + 0x8) (mword_of_int 0xf41a : mword 16) (mword_of_int 0xf81ef41a : mword 32)
      (mword_of_int (KernelSyms.kernelvec + 0x8) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 6 : mword 5), sp, 8)) kv_dec5 exec_execute_C_SDSP.
  Qed.

  Lemma kv_i6 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0xa) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 7 : mword 5), sp, 8)).
  Proof.
    kv_mk_rvc2 (KernelSyms.kernelvec + 0xa) (mword_of_int 0xf81e : mword 16)
      (mword_of_int (KernelSyms.kernelvec + 0xa) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 7 : mword 5), sp, 8)) kv_dec6 exec_execute_C_SDSP.
  Qed.

  Lemma kv_i7 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0xc) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 10 : mword 5), sp, 8)).
  Proof.
    kv_mk_rvc4 (KernelSyms.kernelvec + 0xc) (mword_of_int 0xe4aa : mword 16) (mword_of_int 0xe8aee4aa : mword 32)
      (mword_of_int (KernelSyms.kernelvec + 0xc) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 10 : mword 5), sp, 8)) kv_dec7 exec_execute_C_SDSP.
  Qed.

  Lemma kv_i8 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0xe) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), Regidx (mword_of_int 11 : mword 5), sp, 8)).
  Proof.
    kv_mk_rvc2 (KernelSyms.kernelvec + 0xe) (mword_of_int 0xe8ae : mword 16)
      (mword_of_int (KernelSyms.kernelvec + 0xe) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), Regidx (mword_of_int 11 : mword 5), sp, 8)) kv_dec8 exec_execute_C_SDSP.
  Qed.

  Lemma kv_i9 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x10) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), Regidx (mword_of_int 12 : mword 5), sp, 8)).
  Proof.
    kv_mk_rvc4 (KernelSyms.kernelvec + 0x10) (mword_of_int 0xecb2 : mword 16) (mword_of_int 0xf0b6ecb2 : mword 32)
      (mword_of_int (KernelSyms.kernelvec + 0x10) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), Regidx (mword_of_int 12 : mword 5), sp, 8)) kv_dec9 exec_execute_C_SDSP.
  Qed.

  Lemma kv_i10 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x12) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 6) ('b"000")), Regidx (mword_of_int 13 : mword 5), sp, 8)).
  Proof.
    kv_mk_rvc2 (KernelSyms.kernelvec + 0x12) (mword_of_int 0xf0b6 : mword 16)
      (mword_of_int (KernelSyms.kernelvec + 0x12) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 6) ('b"000")), Regidx (mword_of_int 13 : mword 5), sp, 8)) kv_dec10 exec_execute_C_SDSP.
  Qed.

  Lemma kv_i11 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x14) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 13 : mword 6) ('b"000")), Regidx (mword_of_int 14 : mword 5), sp, 8)).
  Proof.
    kv_mk_rvc4 (KernelSyms.kernelvec + 0x14) (mword_of_int 0xf4ba : mword 16) (mword_of_int 0xf8bef4ba : mword 32)
      (mword_of_int (KernelSyms.kernelvec + 0x14) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 13 : mword 6) ('b"000")), Regidx (mword_of_int 14 : mword 5), sp, 8)) kv_dec11 exec_execute_C_SDSP.
  Qed.

  Lemma kv_i12 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x16) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 14 : mword 6) ('b"000")), Regidx (mword_of_int 15 : mword 5), sp, 8)).
  Proof.
    kv_mk_rvc2 (KernelSyms.kernelvec + 0x16) (mword_of_int 0xf8be : mword 16)
      (mword_of_int (KernelSyms.kernelvec + 0x16) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 14 : mword 6) ('b"000")), Regidx (mword_of_int 15 : mword 5), sp, 8)) kv_dec12 exec_execute_C_SDSP.
  Qed.

  Lemma kv_i13 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x18) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 15 : mword 6) ('b"000")), Regidx (mword_of_int 16 : mword 5), sp, 8)).
  Proof.
    kv_mk_rvc4 (KernelSyms.kernelvec + 0x18) (mword_of_int 0xfcc2 : mword 16) (mword_of_int 0xe146fcc2 : mword 32)
      (mword_of_int (KernelSyms.kernelvec + 0x18) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 15 : mword 6) ('b"000")), Regidx (mword_of_int 16 : mword 5), sp, 8)) kv_dec13 exec_execute_C_SDSP.
  Qed.

  Lemma kv_i14 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x1a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 16 : mword 6) ('b"000")), Regidx (mword_of_int 17 : mword 5), sp, 8)).
  Proof.
    kv_mk_rvc2 (KernelSyms.kernelvec + 0x1a) (mword_of_int 0xe146 : mword 16)
      (mword_of_int (KernelSyms.kernelvec + 0x1a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 16 : mword 6) ('b"000")), Regidx (mword_of_int 17 : mword 5), sp, 8)) kv_dec14 exec_execute_C_SDSP.
  Qed.

  Lemma kv_i15 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x1c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 27 : mword 6) ('b"000")), Regidx (mword_of_int 28 : mword 5), sp, 8)).
  Proof.
    kv_mk_rvc4 (KernelSyms.kernelvec + 0x1c) (mword_of_int 0xedf2 : mword 16) (mword_of_int 0xf1f6edf2 : mword 32)
      (mword_of_int (KernelSyms.kernelvec + 0x1c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 27 : mword 6) ('b"000")), Regidx (mword_of_int 28 : mword 5), sp, 8)) kv_dec15 exec_execute_C_SDSP.
  Qed.

  Lemma kv_i16 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x1e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 28 : mword 6) ('b"000")), Regidx (mword_of_int 29 : mword 5), sp, 8)).
  Proof.
    kv_mk_rvc2 (KernelSyms.kernelvec + 0x1e) (mword_of_int 0xf1f6 : mword 16)
      (mword_of_int (KernelSyms.kernelvec + 0x1e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 28 : mword 6) ('b"000")), Regidx (mword_of_int 29 : mword 5), sp, 8)) kv_dec16 exec_execute_C_SDSP.
  Qed.

  Lemma kv_i17 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x20) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 29 : mword 6) ('b"000")), Regidx (mword_of_int 30 : mword 5), sp, 8)).
  Proof.
    kv_mk_rvc4 (KernelSyms.kernelvec + 0x20) (mword_of_int 0xf5fa : mword 16) (mword_of_int 0xf9fef5fa : mword 32)
      (mword_of_int (KernelSyms.kernelvec + 0x20) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 29 : mword 6) ('b"000")), Regidx (mword_of_int 30 : mword 5), sp, 8)) kv_dec17 exec_execute_C_SDSP.
  Qed.

  Lemma kv_i18 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x22) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 30 : mword 6) ('b"000")), Regidx (mword_of_int 31 : mword 5), sp, 8)).
  Proof.
    kv_mk_rvc2 (KernelSyms.kernelvec + 0x22) (mword_of_int 0xf9fe : mword 16)
      (mword_of_int (KernelSyms.kernelvec + 0x22) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 30 : mword 6) ('b"000")), Regidx (mword_of_int 31 : mword 5), sp, 8)) kv_dec18 exec_execute_C_SDSP.
  Qed.

  Lemma kv_i19 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x24) : mword 64) false (JAL (mword_of_int 0x1fd246 : mword 21, Regidx (mword_of_int 1 : mword 5))).
  Proof.
    kv_mk_base (KernelSyms.kernelvec + 0x24) (mword_of_int 0xa46fd0ef : mword 32)
      (mword_of_int (KernelSyms.kernelvec + 0x24) : mword 64) (JAL (mword_of_int 0x1fd246 : mword 21, Regidx (mword_of_int 1 : mword 5))) kv_dec19.
  Qed.

  Lemma kv_i20 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x28) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1 : mword 5), false, 8)).
  Proof.
    kv_mk_rvc4 (KernelSyms.kernelvec + 0x28) (mword_of_int 0x6082 : mword 16) (mword_of_int 0x61c26082 : mword 32)
      (mword_of_int (KernelSyms.kernelvec + 0x28) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1 : mword 5), false, 8)) kv_dec20 exec_execute_C_LDSP.
  Qed.

  Lemma kv_i21 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x2a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 3 : mword 5), false, 8)).
  Proof.
    kv_mk_rvc2 (KernelSyms.kernelvec + 0x2a) (mword_of_int 0x61c2 : mword 16)
      (mword_of_int (KernelSyms.kernelvec + 0x2a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 3 : mword 5), false, 8)) kv_dec21 exec_execute_C_LDSP.
  Qed.

  Lemma kv_i22 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x2c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 5 : mword 5), false, 8)).
  Proof.
    kv_mk_rvc4 (KernelSyms.kernelvec + 0x2c) (mword_of_int 0x7282 : mword 16) (mword_of_int 0x73227282 : mword 32)
      (mword_of_int (KernelSyms.kernelvec + 0x2c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 5 : mword 5), false, 8)) kv_dec22 exec_execute_C_LDSP.
  Qed.

  Lemma kv_i23 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x2e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 6 : mword 5), false, 8)).
  Proof.
    kv_mk_rvc2 (KernelSyms.kernelvec + 0x2e) (mword_of_int 0x7322 : mword 16)
      (mword_of_int (KernelSyms.kernelvec + 0x2e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 6 : mword 5), false, 8)) kv_dec23 exec_execute_C_LDSP.
  Qed.

  Lemma kv_i24 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x30) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 7 : mword 5), false, 8)).
  Proof.
    kv_mk_rvc4 (KernelSyms.kernelvec + 0x30) (mword_of_int 0x73c2 : mword 16) (mword_of_int 0x652673c2 : mword 32)
      (mword_of_int (KernelSyms.kernelvec + 0x30) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 7 : mword 5), false, 8)) kv_dec24 exec_execute_C_LDSP.
  Qed.

  Lemma kv_i25 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x32) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 10 : mword 5), false, 8)).
  Proof.
    kv_mk_rvc2 (KernelSyms.kernelvec + 0x32) (mword_of_int 0x6526 : mword 16)
      (mword_of_int (KernelSyms.kernelvec + 0x32) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 10 : mword 5), false, 8)) kv_dec25 exec_execute_C_LDSP.
  Qed.

  Lemma kv_i26 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x34) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), sp, Regidx (mword_of_int 11 : mword 5), false, 8)).
  Proof.
    kv_mk_rvc4 (KernelSyms.kernelvec + 0x34) (mword_of_int 0x65c6 : mword 16) (mword_of_int 0x666665c6 : mword 32)
      (mword_of_int (KernelSyms.kernelvec + 0x34) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), sp, Regidx (mword_of_int 11 : mword 5), false, 8)) kv_dec26 exec_execute_C_LDSP.
  Qed.

  Lemma kv_i27 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x36) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), sp, Regidx (mword_of_int 12 : mword 5), false, 8)).
  Proof.
    kv_mk_rvc2 (KernelSyms.kernelvec + 0x36) (mword_of_int 0x6666 : mword 16)
      (mword_of_int (KernelSyms.kernelvec + 0x36) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), sp, Regidx (mword_of_int 12 : mword 5), false, 8)) kv_dec27 exec_execute_C_LDSP.
  Qed.

  Lemma kv_i28 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x38) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 6) ('b"000")), sp, Regidx (mword_of_int 13 : mword 5), false, 8)).
  Proof.
    kv_mk_rvc4 (KernelSyms.kernelvec + 0x38) (mword_of_int 0x7686 : mword 16) (mword_of_int 0x77267686 : mword 32)
      (mword_of_int (KernelSyms.kernelvec + 0x38) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 6) ('b"000")), sp, Regidx (mword_of_int 13 : mword 5), false, 8)) kv_dec28 exec_execute_C_LDSP.
  Qed.

  Lemma kv_i29 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x3a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 13 : mword 6) ('b"000")), sp, Regidx (mword_of_int 14 : mword 5), false, 8)).
  Proof.
    kv_mk_rvc2 (KernelSyms.kernelvec + 0x3a) (mword_of_int 0x7726 : mword 16)
      (mword_of_int (KernelSyms.kernelvec + 0x3a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 13 : mword 6) ('b"000")), sp, Regidx (mword_of_int 14 : mword 5), false, 8)) kv_dec29 exec_execute_C_LDSP.
  Qed.

  Lemma kv_i30 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x3c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 14 : mword 6) ('b"000")), sp, Regidx (mword_of_int 15 : mword 5), false, 8)).
  Proof.
    kv_mk_rvc4 (KernelSyms.kernelvec + 0x3c) (mword_of_int 0x77c6 : mword 16) (mword_of_int 0x786677c6 : mword 32)
      (mword_of_int (KernelSyms.kernelvec + 0x3c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 14 : mword 6) ('b"000")), sp, Regidx (mword_of_int 15 : mword 5), false, 8)) kv_dec30 exec_execute_C_LDSP.
  Qed.

  Lemma kv_i31 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x3e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 15 : mword 6) ('b"000")), sp, Regidx (mword_of_int 16 : mword 5), false, 8)).
  Proof.
    kv_mk_rvc2 (KernelSyms.kernelvec + 0x3e) (mword_of_int 0x7866 : mword 16)
      (mword_of_int (KernelSyms.kernelvec + 0x3e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 15 : mword 6) ('b"000")), sp, Regidx (mword_of_int 16 : mword 5), false, 8)) kv_dec31 exec_execute_C_LDSP.
  Qed.

  Lemma kv_i32 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x40) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 16 : mword 6) ('b"000")), sp, Regidx (mword_of_int 17 : mword 5), false, 8)).
  Proof.
    kv_mk_rvc4 (KernelSyms.kernelvec + 0x40) (mword_of_int 0x688a : mword 16) (mword_of_int 0x6e6e688a : mword 32)
      (mword_of_int (KernelSyms.kernelvec + 0x40) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 16 : mword 6) ('b"000")), sp, Regidx (mword_of_int 17 : mword 5), false, 8)) kv_dec32 exec_execute_C_LDSP.
  Qed.

  Lemma kv_i33 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x42) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 27 : mword 6) ('b"000")), sp, Regidx (mword_of_int 28 : mword 5), false, 8)).
  Proof.
    kv_mk_rvc2 (KernelSyms.kernelvec + 0x42) (mword_of_int 0x6e6e : mword 16)
      (mword_of_int (KernelSyms.kernelvec + 0x42) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 27 : mword 6) ('b"000")), sp, Regidx (mword_of_int 28 : mword 5), false, 8)) kv_dec33 exec_execute_C_LDSP.
  Qed.

  Lemma kv_i34 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x44) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 28 : mword 6) ('b"000")), sp, Regidx (mword_of_int 29 : mword 5), false, 8)).
  Proof.
    kv_mk_rvc4 (KernelSyms.kernelvec + 0x44) (mword_of_int 0x7e8e : mword 16) (mword_of_int 0x7f2e7e8e : mword 32)
      (mword_of_int (KernelSyms.kernelvec + 0x44) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 28 : mword 6) ('b"000")), sp, Regidx (mword_of_int 29 : mword 5), false, 8)) kv_dec34 exec_execute_C_LDSP.
  Qed.

  Lemma kv_i35 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x46) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 29 : mword 6) ('b"000")), sp, Regidx (mword_of_int 30 : mword 5), false, 8)).
  Proof.
    kv_mk_rvc2 (KernelSyms.kernelvec + 0x46) (mword_of_int 0x7f2e : mword 16)
      (mword_of_int (KernelSyms.kernelvec + 0x46) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 29 : mword 6) ('b"000")), sp, Regidx (mword_of_int 30 : mword 5), false, 8)) kv_dec35 exec_execute_C_LDSP.
  Qed.

  Lemma kv_i36 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x48) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 30 : mword 6) ('b"000")), sp, Regidx (mword_of_int 31 : mword 5), false, 8)).
  Proof.
    kv_mk_rvc4 (KernelSyms.kernelvec + 0x48) (mword_of_int 0x7fce : mword 16) (mword_of_int 0x61117fce : mword 32)
      (mword_of_int (KernelSyms.kernelvec + 0x48) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 30 : mword 6) ('b"000")), sp, Regidx (mword_of_int 31 : mword 5), false, 8)) kv_dec36 exec_execute_C_LDSP.
  Qed.

  Lemma kv_i37 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x4a) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 16 : mword 6), sp, sp, ADDI)).
  Proof.
    kv_mk_rvc2 (KernelSyms.kernelvec + 0x4a) (mword_of_int 0x6111 : mword 16)
      (mword_of_int (KernelSyms.kernelvec + 0x4a) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 16 : mword 6), sp, sp, ADDI)) kv_dec37 exec_execute_C_ADDI16SP.
  Qed.

  Lemma kv_i38 :
    kernel_text -∗ instr (mword_of_int (KernelSyms.kernelvec + 0x4c) : mword 64) false (SRET tt).
  Proof.
    kv_mk_base (KernelSyms.kernelvec + 0x4c) (mword_of_int 0x10200073 : mword 32)
      (mword_of_int (KernelSyms.kernelvec + 0x4c) : mword 64) (SRET tt) kv_dec38.
  Qed.

End WpKvInstr.
