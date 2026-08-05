(* UserretDefs.v -- shared userret definitions: the va/pa windows, the
   38-instruction catalog (words, ASTs, decode facts, [kernel_text]-backed
   [instr] constructors), and the pure execute reductions for the
   page-table-switch instructions (the SFENCE.VMA flush and the S-mode csrw
   satp chain).  The owned trapframe word is the canonical physical word form
   [_ ↦ₚ₈ _] ([phys_word_pointsto], RiscvPtsto). *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import InstrBytes.
Require Import WpDecodeBridge WpRvcBridge.
Require Import WpGprCsrwCommon WpGprCsrwB.
Require Import ExecCommon WpGpr.
Require Import WpMmodeLeafBase.
Require Import KernelText.
Require Import SmodePte.
Require Import TrampPt.
From Kernel Require Import KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 1. userret's va/pa windows.                                            *)
(* ===================================================================== *)

Definition uva (off : Z) : mword 64 := mword_of_int (TRAMPOLINE + off).
Definition upa (off : Z) : mword 64 := mword_of_int (KernelSyms.trampoline + off).

(* ===================================================================== *)
(* 8. flush_TLB None None clears every slot; the SFENCE.VMA x0,x0         *)
(*    execute reduction (S-mode, TVM=0).                                  *)
(* ===================================================================== *)

Lemma exec_flush_TLB_all (s : mstate) :
  exists tlbvec' : vec (option TLB_Entry) (2 ^ 6),
    exec (flush_TLB None None) s = Some (tt, set_reg s tlb tlbvec') /\
    (forall i, 0 <= i < 64 -> vec_access_dec tlbvec' i = None).
Proof.
  unfold flush_TLB.
  cbv zeta iota.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
  match goal with |- context[Defs.foreach_ZM_up ?f ?t ?st ?v ?b] =>
    change t with 63; set (B := b) end.
  unfold Defs.foreach_ZM_up.
  (* the loop invariant: after running from [from] with enough fuel, slots
     [from..63] are cleared and lower slots keep the START state's values. *)
  assert (Hloop : forall (n : nat) (from : Z) (s0 : mstate),
    0 <= from -> from + Z.of_nat n = 64 ->
    exists tv : vec (option TLB_Entry) (2 ^ 6),
      exec (Defs.foreach_ZM_up' from 63 1 n tt B) s0 = Some (tt, set_reg s0 tlb tv) /\
      (forall i, 0 <= i < 64 ->
         vec_access_dec tv i = (if from <=? i then None
                                else vec_access_dec (register_lookup tlb s0.(sregs)) i))).
  { induction n as [| n IHn]; intros from s0 Hfrom Hcover.
    - (* fuel exhausted exactly at from = 64 *)
      exists (register_lookup tlb s0.(sregs)).
      split.
      + cbn [Defs.foreach_ZM_up'].
        destruct (from <=? 63); rewrite set_reg_tlb_id; apply exec_returnm.
      + intros i Hi.
        replace (from <=? i) with false by (symmetry; apply Z.leb_gt; lia).
        reflexivity.
    - assert (Hle : from <= 63) by lia.
      rewrite (Defs.unroll_foreach_ZM_up' _ _ from 63 1 n tt B Hle).
      destruct (vec_access_dec (register_lookup tlb s0.(sregs)) from) as [e |] eqn:Hslot.
      + (* resident: cleared *)
        assert (HB : exec (B from tt) s0
                     = Some (tt, set_reg s0 tlb
                                   (vec_update_dec (register_lookup tlb s0.(sregs)) from None))).
        { unfold B. cbv beta.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s0)).
          rewrite Hslot.
          change (flush_TLB_Entry e None None) with true.
          cbv iota.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s0)).
          rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg tlb _ s0)).
          apply exec_returnM. }
        rewrite (exec_bind_Some _ _ _ _ _ HB).
        destruct (IHn (from + 1) (set_reg s0 tlb
                    (vec_update_dec (register_lookup tlb s0.(sregs)) from None))
                    ltac:(lia) ltac:(lia)) as (tv & Hex & Hprop).
        exists tv. split.
        * rewrite Hex. rewrite set_reg_tlb_overwrite. reflexivity.
        * intros i Hi.
          rewrite (Hprop i Hi).
          rewrite ?sregs_set_reg. rewrite register_lookup_set.
          rewrite (vec64_access_update _ from i None ltac:(lia)).
          destruct (Z.leb_spec from i) as [Hfi | Hfi];
            destruct (Z.leb_spec (from + 1) i) as [Hf1i | Hf1i];
            destruct (Z.eqb_spec i from) as [-> | Hne];
            try reflexivity; try lia.
      + (* empty: skip *)
        assert (HB : exec (B from tt) s0 = Some (tt, s0)).
        { unfold B. cbv beta.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s0)).
          rewrite Hslot. apply exec_returnM. }
        rewrite (exec_bind_Some _ _ _ _ _ HB).
        destruct (IHn (from + 1) s0 ltac:(lia) ltac:(lia)) as (tv & Hex & Hprop).
        exists tv. split; [exact Hex |].
        intros i Hi.
        rewrite (Hprop i Hi).
        destruct (Z.leb_spec from i) as [Hfi | Hfi];
          destruct (Z.leb_spec (from + 1) i) as [Hf1i | Hf1i];
          try reflexivity; try lia.
        (* i = from: the slot is already None *)
        assert (i = from) by lia. subst i. rewrite Hslot. reflexivity. }
  destruct (Hloop (S (Z.abs_nat (0 - 63))) 0 s ltac:(lia)
              ltac:(vm_compute (Z.of_nat _); reflexivity)) as (tv & Hex & Hprop).
  exists tv.
  split.
  - match goal with |- context[Defs.bind (Defs.bind0 ?L ?r) ?k] =>
      assert (HLr : exec (Defs.bind0 L r) s = Some (tv, set_reg s tlb tv)) end.
    { rewrite (exec_bind0_Some _ _ _ _ _ Hex).
      rewrite (exec_read_reg tlb _).
      rewrite ?sregs_set_reg; rewrite register_lookup_set; reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ HLr).
    cbv beta. apply exec_returnM.
  - intros i Hi. rewrite (Hprop i Hi).
    replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia).
    reflexivity.
Qed.

(* the SFENCE.VMA x0,x0 execute reduction: S-mode, TVM=0 => full flush. *)
Lemma exec_execute_SFENCE_VMA_S (s : mstate) :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  eq_vec (_get_Mstatus_TVM (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  exists tlbvec' : vec (option TLB_Entry) (2 ^ 6),
    exec (execute (SFENCE_VMA (zreg, zreg))) s
      = Some (RETIRE_SUCCESS, set_reg s tlb tlbvec') /\
    (forall i, 0 <= i < 64 -> vec_access_dec tlbvec' i = None).
Proof.
  intros Hpriv HTVM.
  destruct (exec_flush_TLB_all s) as (tv & Hfl & Hprop).
  exists tv. split; [| exact Hprop].
  change (execute (SFENCE_VMA (zreg, zreg))) with (execute_SFENCE_VMA zreg zreg).
  unfold execute_SFENCE_VMA.
  replace (generic_neq zreg zreg) with false by (vm_compute; reflexivity).
  cbv iota.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv. cbv iota beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  cbv zeta.
  rewrite HTVM. cbv iota.
  match goal with |- context[flush_TLB ?a ?b] =>
    change a with (@None (mword 16)) end.
  rewrite (exec_bind0_Some _ _ _ _ _ Hfl).
  apply exec_returnM.
Qed.

(* ===================================================================== *)
(* 9. csrw satp,rs1 in S-MODE (mstatus.TVM = 0).                          *)
(* ===================================================================== *)

Lemma exec_check_CSR_priv_satp_S s :
  exec (check_CSR_priv csr_satp Supervisor) s = Some (true, s).
Proof. vm_compute. reflexivity. Qed.

Lemma exec_is_CSR_accessible_satp_S s :
  eq_vec (_get_Mstatus_TVM (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  exec (is_CSR_accessible csr_satp Supervisor CSRWrite) s = Some (true, s).
Proof.
  intro HTVM.
  unfold is_CSR_accessible.
  skip_csr_false_clauses.
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  unfold satp_accessible. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  pose proof (mword1_zero_of_ne_one _ HTVM) as H0.
  rewrite H0.
  replace (eq_vec ('b"0" : mword 1) ('b"0")) with true by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

Lemma exec_check_CSR_result_csrw_satp_S s :
  eq_vec (_get_Mstatus_TVM (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  exec (check_CSR_result csr_satp Supervisor CSRWrite) s = Some (CSR_Check_OK tt, s).
Proof.
  intro HTVM.
  unfold check_CSR_result.
  match goal with |- context[Defs.bind ?m ?f] =>
    assert (Hcc : exec m s = Some (true, s)) end.
  { unfold check_CSR.
    rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_check_CSR_priv_satp_S s)). cbn match.
    match goal with |- context[and_boolM ?A ?B] =>
      assert (HB : exec A s = Some (true, s)) end.
    { vm_compute (check_CSR_access _ _). apply exec_returnM. }
    rewrite (exec_and_boolM_Some _ _ _ _ _ HB). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_is_CSR_accessible_satp_S s HTVM)). cbn match.
    vm_compute (stateen_allows_CSR_access csr_satp Supervisor CSRWrite).
    apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hcc). cbn match. apply exec_returnm.
Qed.

(* The S-mode doCSR / execute_CSRReg for a csrw are WpGprCsrwCommon.v's
   privilege-generic [exec_doCSR_csrw_p] / [exec_execute_csrw_gpr_p] at
   Supervisor -- see the note there. *)

(* csrw satp,rs1 in S-mode: writes satp := legalized(rs1 value). *)
Lemma exec_execute_csrw_satp_S (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  eq_vec (_get_Mstatus_TVM (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  exec (execute (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW))) s
    = Some (RETIRE_SUCCESS,
            set_reg s satp
              (satp_legalized (register_lookup satp s.(sregs))
                 (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hrs1 Hpriv HTVM HS HSXL.
  change (execute (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW)))
    with (execute_CSRReg csr_satp (Regidx rs1) zreg CSRRW).
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_execute_csrw_gpr_p Supervisor csr_satp rs1 s _
           (satp_legalized (register_lookup satp s.(sregs))
              (if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
  - exact Hpriv.
  - apply exec_check_CSR_result_csrw_satp_S. exact HTVM.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_satp; assumption.
  - apply exec_csr_id_write_callback_satp.
Qed.

(* a Sv39-mode value legalizes to itself. *)
Lemma satp_legalized_sv39 (prev v : mword 64) :
  _get_Satp64_Mode (Mk_Satp64 v) = ('b"1000" : mword 4) ->
  satp_legalized prev v = v.
Proof.
  intro Hmode. unfold satp_legalized.
  rewrite Hmode.
  vm_compute (satpMode_of_bits RV64 ('b"1000" : mword 4)).
  reflexivity.
Qed.


(* ===================================================================== *)
(* 4. The 38-instruction catalog.                                         *)
(* ===================================================================== *)

Definition uw_sfence : mword 32 := mword_of_int 0x12000073.
Definition uw_csrw   : mword 32 := mword_of_int 0x18051073.
Definition uw_lui    : mword 32 := mword_of_int 0x02000537.
Definition uw_sret   : mword 32 := mword_of_int 0x10200073.

Definition uw_ld_ra : mword 32 := mword_of_int 0x02853083.
Definition uw_ld_sp : mword 32 := mword_of_int 0x03053103.
Definition uw_ld_gp : mword 32 := mword_of_int 0x03853183.
Definition uw_ld_tp : mword 32 := mword_of_int 0x04053203.
Definition uw_ld_t0 : mword 32 := mword_of_int 0x04853283.
Definition uw_ld_t1 : mword 32 := mword_of_int 0x05053303.
Definition uw_ld_t2 : mword 32 := mword_of_int 0x05853383.
Definition uw_ld_a6 : mword 32 := mword_of_int 0x0a053803.
Definition uw_ld_a7 : mword 32 := mword_of_int 0x0a853883.
Definition uw_ld_s2 : mword 32 := mword_of_int 0x0b053903.
Definition uw_ld_s3 : mword 32 := mword_of_int 0x0b853983.
Definition uw_ld_s4 : mword 32 := mword_of_int 0x0c053a03.
Definition uw_ld_s5 : mword 32 := mword_of_int 0x0c853a83.
Definition uw_ld_s6 : mword 32 := mword_of_int 0x0d053b03.
Definition uw_ld_s7 : mword 32 := mword_of_int 0x0d853b83.
Definition uw_ld_s8 : mword 32 := mword_of_int 0x0e053c03.
Definition uw_ld_s9 : mword 32 := mword_of_int 0x0e853c83.
Definition uw_ld_s10 : mword 32 := mword_of_int 0x0f053d03.
Definition uw_ld_s11 : mword 32 := mword_of_int 0x0f853d83.
Definition uw_ld_t3 : mword 32 := mword_of_int 0x10053e03.
Definition uw_ld_t4 : mword 32 := mword_of_int 0x10853e83.
Definition uw_ld_t5 : mword 32 := mword_of_int 0x11053f03.
Definition uw_ld_t6 : mword 32 := mword_of_int 0x11853f83.

(* --- compressed halves and their 4-aligned windows --- *)
Definition uh_addiw : mword 16 := mword_of_int 0x357d.
Definition uh_slli  : mword 16 := mword_of_int 0x0536.
Definition uh_cld_s0 : mword 16 := mword_of_int 0x7120.
Definition uh_cld_s1 : mword 16 := mword_of_int 0x7524.
Definition uh_cld_a1 : mword 16 := mword_of_int 0x7d2c.
Definition uh_cld_a2 : mword 16 := mword_of_int 0x6150.
Definition uh_cld_a3 : mword 16 := mword_of_int 0x6554.
Definition uh_cld_a4 : mword 16 := mword_of_int 0x6958.
Definition uh_cld_a5 : mword 16 := mword_of_int 0x6d5c.
Definition uh_cld_a0 : mword 16 := mword_of_int 0x7928.

(* --- ASTs --- *)
Definition ureg (n : Z) : regidx := Regidx (mword_of_int n).
Definition ucreg (n : Z) : cregidx := Cregidx (mword_of_int n).
Definition ai_sfence : instruction := SFENCE_VMA (zreg, zreg).
Definition ai_csrw : instruction := CSRReg (csr_satp, ureg 10, zreg, CSRRW).
Definition ai_lui : instruction := UTYPE (mword_of_int 0x2000, ureg 10, LUI).
Definition ai_addiw : instruction :=
  ADDIW (sign_extend' 12 (mword_of_int 63 : mword 6), ureg 10, ureg 10).
Definition ai_slli : instruction :=
  SHIFTIOP (mword_of_int 13, ureg 10, ureg 10, SLLI).
Definition ai_sret : instruction := SRET tt.
Definition ai_ld (rd : Z) (imm : Z) : instruction :=
  LOAD (mword_of_int imm, ureg 10, ureg rd, false, 8).
Definition ai_cld_tgt (rdc : Z) (uimm : Z) : instruction :=
  LOAD (mword_of_int (uimm * 8), ureg 10, ureg (8 + rdc), false, 8).

(* --- decode facts --- *)
Lemma udec_sfence s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_sfence) s = Some (ai_sfence, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_csrw s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_csrw) s = Some (ai_csrw, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_lui s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_lui) s = Some (ai_lui, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_sret s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_sret) s = Some (ai_sret, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_ra s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_ra) s = Some (ai_ld 1 40, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_sp s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_sp) s = Some (ai_ld 2 48, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_gp s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_gp) s = Some (ai_ld 3 56, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_tp s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_tp) s = Some (ai_ld 4 64, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_t0 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_t0) s = Some (ai_ld 5 72, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_t1 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_t1) s = Some (ai_ld 6 80, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_t2 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_t2) s = Some (ai_ld 7 88, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_a6 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_a6) s = Some (ai_ld 16 160, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_a7 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_a7) s = Some (ai_ld 17 168, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_s2 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_s2) s = Some (ai_ld 18 176, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_s3 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_s3) s = Some (ai_ld 19 184, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_s4 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_s4) s = Some (ai_ld 20 192, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_s5 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_s5) s = Some (ai_ld 21 200, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_s6 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_s6) s = Some (ai_ld 22 208, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_s7 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_s7) s = Some (ai_ld 23 216, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_s8 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_s8) s = Some (ai_ld 24 224, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_s9 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_s9) s = Some (ai_ld 25 232, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_s10 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_s10) s = Some (ai_ld 26 240, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_s11 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_s11) s = Some (ai_ld 27 248, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_t3 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_t3) s = Some (ai_ld 28 256, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_t4 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_t4) s = Some (ai_ld 29 264, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_t5 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_t5) s = Some (ai_ld 30 272, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_ld_t6 s :
  register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode uw_ld_t6) s = Some (ai_ld 31 280, s).
Proof. decode_bridge_ms. Qed.

Lemma udec_addiw s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uh_addiw) s
  = Some (C_ADDIW (mword_of_int 63, ureg 10), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma udec_slli s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uh_slli) s
  = Some (C_SLLI (mword_of_int 13, ureg 10), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma udec_cld_s0 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uh_cld_s0) s
  = Some (C_LD (mword_of_int 12, ucreg 2, ucreg 0), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma udec_cld_s1 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uh_cld_s1) s
  = Some (C_LD (mword_of_int 13, ucreg 2, ucreg 1), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma udec_cld_a1 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uh_cld_a1) s
  = Some (C_LD (mword_of_int 15, ucreg 2, ucreg 3), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma udec_cld_a2 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uh_cld_a2) s
  = Some (C_LD (mword_of_int 16, ucreg 2, ucreg 4), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma udec_cld_a3 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uh_cld_a3) s
  = Some (C_LD (mword_of_int 17, ucreg 2, ucreg 5), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma udec_cld_a4 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uh_cld_a4) s
  = Some (C_LD (mword_of_int 18, ucreg 2, ucreg 6), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma udec_cld_a5 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uh_cld_a5) s
  = Some (C_LD (mword_of_int 19, ucreg 2, ucreg 7), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.

Lemma udec_cld_a0 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed uh_cld_a0) s
  = Some (C_LD (mword_of_int 14, ucreg 2, ucreg 2), s).
Proof. intro HmisaC. rvc_oneshot s HmisaC. Qed.


Section UserretInstrs.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma ui_sfence1 :
    kernel_text -∗ instr (upa 0x9c) false ai_sfence.
  Proof. mk_base (KernelSyms.trampoline + 0x9c) uw_sfence (upa 0x9c) ai_sfence udec_sfence. Qed.

  Lemma ui_csrw :
    kernel_text -∗ instr (upa 0xa0) false ai_csrw.
  Proof. mk_base (KernelSyms.trampoline + 0xa0) uw_csrw (upa 0xa0) ai_csrw udec_csrw. Qed.

  Lemma ui_sfence2 :
    kernel_text -∗ instr (upa 0xa4) false ai_sfence.
  Proof. mk_base (KernelSyms.trampoline + 0xa4) uw_sfence (upa 0xa4) ai_sfence udec_sfence. Qed.

  Lemma ui_lui :
    kernel_text -∗ instr (upa 0xa8) false ai_lui.
  Proof. mk_base (KernelSyms.trampoline + 0xa8) uw_lui (upa 0xa8) ai_lui udec_lui. Qed.

  Lemma ui_addiw :
    kernel_text -∗ instr (upa 0xac) true ai_addiw.
  Proof. mk_rvc (KernelSyms.trampoline + 0xac) uh_addiw (upa 0xac) ai_addiw udec_addiw exec_execute_C_ADDIW. Qed.

  Lemma ui_slli :
    kernel_text -∗ instr (upa 0xae) true ai_slli.
  Proof. mk_rvc (KernelSyms.trampoline + 0xae) uh_slli (upa 0xae) ai_slli udec_slli exec_execute_C_SLLI. Qed.

  Lemma ui_ld_ra :
    kernel_text -∗ instr (upa 0xb0) false (ai_ld 1 40).
  Proof. mk_base (KernelSyms.trampoline + 0xb0) uw_ld_ra (upa 0xb0) (ai_ld 1 40) udec_ld_ra. Qed.

  Lemma ui_ld_sp :
    kernel_text -∗ instr (upa 0xb4) false (ai_ld 2 48).
  Proof. mk_base (KernelSyms.trampoline + 0xb4) uw_ld_sp (upa 0xb4) (ai_ld 2 48) udec_ld_sp. Qed.

  Lemma ui_ld_gp :
    kernel_text -∗ instr (upa 0xb8) false (ai_ld 3 56).
  Proof. mk_base (KernelSyms.trampoline + 0xb8) uw_ld_gp (upa 0xb8) (ai_ld 3 56) udec_ld_gp. Qed.

  Lemma ui_ld_tp :
    kernel_text -∗ instr (upa 0xbc) false (ai_ld 4 64).
  Proof. mk_base (KernelSyms.trampoline + 0xbc) uw_ld_tp (upa 0xbc) (ai_ld 4 64) udec_ld_tp. Qed.

  Lemma ui_ld_t0 :
    kernel_text -∗ instr (upa 0xc0) false (ai_ld 5 72).
  Proof. mk_base (KernelSyms.trampoline + 0xc0) uw_ld_t0 (upa 0xc0) (ai_ld 5 72) udec_ld_t0. Qed.

  Lemma ui_ld_t1 :
    kernel_text -∗ instr (upa 0xc4) false (ai_ld 6 80).
  Proof. mk_base (KernelSyms.trampoline + 0xc4) uw_ld_t1 (upa 0xc4) (ai_ld 6 80) udec_ld_t1. Qed.

  Lemma ui_ld_t2 :
    kernel_text -∗ instr (upa 0xc8) false (ai_ld 7 88).
  Proof. mk_base (KernelSyms.trampoline + 0xc8) uw_ld_t2 (upa 0xc8) (ai_ld 7 88) udec_ld_t2. Qed.

  Lemma ui_ld_a6 :
    kernel_text -∗ instr (upa 0xda) false (ai_ld 16 160).
  Proof. mk_base (KernelSyms.trampoline + 0xda) uw_ld_a6 (upa 0xda) (ai_ld 16 160) udec_ld_a6. Qed.

  Lemma ui_ld_a7 :
    kernel_text -∗ instr (upa 0xde) false (ai_ld 17 168).
  Proof. mk_base (KernelSyms.trampoline + 0xde) uw_ld_a7 (upa 0xde) (ai_ld 17 168) udec_ld_a7. Qed.

  Lemma ui_ld_s2 :
    kernel_text -∗ instr (upa 0xe2) false (ai_ld 18 176).
  Proof. mk_base (KernelSyms.trampoline + 0xe2) uw_ld_s2 (upa 0xe2) (ai_ld 18 176) udec_ld_s2. Qed.

  Lemma ui_ld_s3 :
    kernel_text -∗ instr (upa 0xe6) false (ai_ld 19 184).
  Proof. mk_base (KernelSyms.trampoline + 0xe6) uw_ld_s3 (upa 0xe6) (ai_ld 19 184) udec_ld_s3. Qed.

  Lemma ui_ld_s4 :
    kernel_text -∗ instr (upa 0xea) false (ai_ld 20 192).
  Proof. mk_base (KernelSyms.trampoline + 0xea) uw_ld_s4 (upa 0xea) (ai_ld 20 192) udec_ld_s4. Qed.

  Lemma ui_ld_s5 :
    kernel_text -∗ instr (upa 0xee) false (ai_ld 21 200).
  Proof. mk_base (KernelSyms.trampoline + 0xee) uw_ld_s5 (upa 0xee) (ai_ld 21 200) udec_ld_s5. Qed.

  Lemma ui_ld_s6 :
    kernel_text -∗ instr (upa 0xf2) false (ai_ld 22 208).
  Proof. mk_base (KernelSyms.trampoline + 0xf2) uw_ld_s6 (upa 0xf2) (ai_ld 22 208) udec_ld_s6. Qed.

  Lemma ui_ld_s7 :
    kernel_text -∗ instr (upa 0xf6) false (ai_ld 23 216).
  Proof. mk_base (KernelSyms.trampoline + 0xf6) uw_ld_s7 (upa 0xf6) (ai_ld 23 216) udec_ld_s7. Qed.

  Lemma ui_ld_s8 :
    kernel_text -∗ instr (upa 0xfa) false (ai_ld 24 224).
  Proof. mk_base (KernelSyms.trampoline + 0xfa) uw_ld_s8 (upa 0xfa) (ai_ld 24 224) udec_ld_s8. Qed.

  Lemma ui_ld_s9 :
    kernel_text -∗ instr (upa 0xfe) false (ai_ld 25 232).
  Proof. mk_base (KernelSyms.trampoline + 0xfe) uw_ld_s9 (upa 0xfe) (ai_ld 25 232) udec_ld_s9. Qed.

  Lemma ui_ld_s10 :
    kernel_text -∗ instr (upa 0x102) false (ai_ld 26 240).
  Proof. mk_base (KernelSyms.trampoline + 0x102) uw_ld_s10 (upa 0x102) (ai_ld 26 240) udec_ld_s10. Qed.

  Lemma ui_ld_s11 :
    kernel_text -∗ instr (upa 0x106) false (ai_ld 27 248).
  Proof. mk_base (KernelSyms.trampoline + 0x106) uw_ld_s11 (upa 0x106) (ai_ld 27 248) udec_ld_s11. Qed.

  Lemma ui_ld_t3 :
    kernel_text -∗ instr (upa 0x10a) false (ai_ld 28 256).
  Proof. mk_base (KernelSyms.trampoline + 0x10a) uw_ld_t3 (upa 0x10a) (ai_ld 28 256) udec_ld_t3. Qed.

  Lemma ui_ld_t4 :
    kernel_text -∗ instr (upa 0x10e) false (ai_ld 29 264).
  Proof. mk_base (KernelSyms.trampoline + 0x10e) uw_ld_t4 (upa 0x10e) (ai_ld 29 264) udec_ld_t4. Qed.

  Lemma ui_ld_t5 :
    kernel_text -∗ instr (upa 0x112) false (ai_ld 30 272).
  Proof. mk_base (KernelSyms.trampoline + 0x112) uw_ld_t5 (upa 0x112) (ai_ld 30 272) udec_ld_t5. Qed.

  Lemma ui_ld_t6 :
    kernel_text -∗ instr (upa 0x116) false (ai_ld 31 280).
  Proof. mk_base (KernelSyms.trampoline + 0x116) uw_ld_t6 (upa 0x116) (ai_ld 31 280) udec_ld_t6. Qed.

  Lemma ui_cld_s0 :
    kernel_text -∗ instr (upa 0xcc) true (ai_cld_tgt 0 12).
  Proof. mk_rvc (KernelSyms.trampoline + 0xcc) uh_cld_s0 (upa 0xcc) (ai_cld_tgt 0 12) udec_cld_s0 exec_execute_C_LD. Qed.

  Lemma ui_cld_s1 :
    kernel_text -∗ instr (upa 0xce) true (ai_cld_tgt 1 13).
  Proof. mk_rvc (KernelSyms.trampoline + 0xce) uh_cld_s1 (upa 0xce) (ai_cld_tgt 1 13) udec_cld_s1 exec_execute_C_LD. Qed.

  Lemma ui_cld_a1 :
    kernel_text -∗ instr (upa 0xd0) true (ai_cld_tgt 3 15).
  Proof. mk_rvc (KernelSyms.trampoline + 0xd0) uh_cld_a1 (upa 0xd0) (ai_cld_tgt 3 15) udec_cld_a1 exec_execute_C_LD. Qed.

  Lemma ui_cld_a2 :
    kernel_text -∗ instr (upa 0xd2) true (ai_cld_tgt 4 16).
  Proof. mk_rvc (KernelSyms.trampoline + 0xd2) uh_cld_a2 (upa 0xd2) (ai_cld_tgt 4 16) udec_cld_a2 exec_execute_C_LD. Qed.

  Lemma ui_cld_a3 :
    kernel_text -∗ instr (upa 0xd4) true (ai_cld_tgt 5 17).
  Proof. mk_rvc (KernelSyms.trampoline + 0xd4) uh_cld_a3 (upa 0xd4) (ai_cld_tgt 5 17) udec_cld_a3 exec_execute_C_LD. Qed.

  Lemma ui_cld_a4 :
    kernel_text -∗ instr (upa 0xd6) true (ai_cld_tgt 6 18).
  Proof. mk_rvc (KernelSyms.trampoline + 0xd6) uh_cld_a4 (upa 0xd6) (ai_cld_tgt 6 18) udec_cld_a4 exec_execute_C_LD. Qed.

  Lemma ui_cld_a5 :
    kernel_text -∗ instr (upa 0xd8) true (ai_cld_tgt 7 19).
  Proof. mk_rvc (KernelSyms.trampoline + 0xd8) uh_cld_a5 (upa 0xd8) (ai_cld_tgt 7 19) udec_cld_a5 exec_execute_C_LD. Qed.

  Lemma ui_cld_a0 :
    kernel_text -∗ instr (upa 0x11a) true (ai_cld_tgt 2 14).
  Proof. mk_rvc (KernelSyms.trampoline + 0x11a) uh_cld_a0 (upa 0x11a) (ai_cld_tgt 2 14) udec_cld_a0 exec_execute_C_LD. Qed.

  Lemma ui_sret :
    kernel_text -∗ instr (upa 0x11c) false ai_sret.
  Proof. mk_base (KernelSyms.trampoline + 0x11c) uw_sret (upa 0x11c) ai_sret udec_sret. Qed.


End UserretInstrs.

