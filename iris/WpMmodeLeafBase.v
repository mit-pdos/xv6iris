(* Shared base for the M-mode per-decode-family leaf files (WpMmode<Family>.v).
   Holds exec-result helpers, value-defs, and utility lemmas shared by the
   M-mode (mmode_config) instruction leaves. Relocated from the WpGpr*.v files. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras SailStdpp.Base RiscvLang RiscvPtsto RiscvExec RiscvFetchExec ExecCommon WpGpr RegFile RiscvModelBytes RiscvTryStep RiscvExtras WpLoad SailStdpp.TypeCasts SailStdpp.MachineWord SailStdpp.Values WpAuipc WpDecode.
Import Defs.
Local Open Scope Z_scope.


(* WpGprAddi.v : gpr_addi_val *)
Definition gpr_addi_val (rs1 : mword 5) (imm : mword 12) (s : mstate) : mword 64 :=
  add_vec (if Z.eqb (uint rs1) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
          (sign_extend' 64 imm).

(* WpGprAddi.v : exec_execute_ITYPE_ADDI_gpr *)
Lemma exec_execute_ITYPE_ADDI_gpr (rs1 rd : mword 5) (imm : mword 12) s :
  exec (execute (ITYPE (imm, Regidx rs1, Regidx rd, ADDI))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_addi_val rs1 imm s))).
Proof.
  unfold gpr_addi_val.
  eapply exec_execute_ITYPE_ADDI.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_wX_bits_gpr rd _ s).
Qed.


(* ADDIW: sign-extend the low 32 bits of (rs1 + imm).  An add-immediate variant,
   so it lives here rather than in WpMmodeShiftiop.  Value inlined (like gpr_addi_val),
   so no dependency on WpMmodeShiftiop's gpr_src. *)

(* WpGprAddi.v : exec_execute_ADDIW_base *)
Lemma exec_execute_ADDIW_base (imm : mword 12) (rs1 rd : regidx) (a : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) ->
  exec (wX_bits rd (sign_extend' 64 (subrange_vec_dec (add_vec a (sign_extend' 64 imm)) 31 0))) s
    = Some (tt, s') ->
  exec (execute (ADDIW (imm, rs1, rd))) s = Some (RETIRE_SUCCESS, s').
Proof.
  intros Ha Hw.
  change (execute (ADDIW (imm, rs1, rd))) with (execute_ADDIW imm rs1 rd).
  unfold execute_ADDIW. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ Ha).
  rewrite (exec_bind0_Some _ _ _ _ _ Hw). apply exec_returnm.
Qed.

(* WpGprAddi.v : gpr_addiw_val *)
Definition gpr_addiw_val (rs1 : mword 5) (imm : mword 12) (s : mstate) : mword 64 :=
  sign_extend' 64 (subrange_vec_dec
    (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
             (sign_extend' 64 imm)) 31 0).

(* WpGprAddi.v : exec_execute_ADDIW_gpr *)
Lemma exec_execute_ADDIW_gpr (rs1 rd : mword 5) (imm : mword 12) s :
  exec (execute (ADDIW (imm, Regidx rs1, Regidx rd))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_addiw_val rs1 imm s))).
Proof.
  unfold gpr_addiw_val.
  eapply exec_execute_ADDIW_base.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_wX_bits_gpr rd _ s).
Qed.

(* exec-level register-generic ADDI step (32-bit, F_Base): one lemma, ANY rd/rs1. *)

(* WpGprAddi.v : ForwardAddiGpr *)
Section ForwardAddiGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs1 rd : mword 5) (imm : mword 12).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrd0 : uint rd <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (ITYPE (imm, Regidx rs1, Regidx rd, ADDI), s0).


End ForwardAddiGpr.

(* WpGprAddi.v : CleanAddiGpr *)
Section CleanAddiGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (rs1 rd : mword 5) (imm : mword 12) (mst0 : mword 64).

End CleanAddiGpr.

(* WpGprLogic.v : exec_execute_RTYPE_OR *)
Lemma exec_execute_RTYPE_OR (rs2 rs1 rd : regidx) (a b : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) -> exec (rX_bits rs2) s = Some (b, s) ->
  exec (wX_bits rd (or_vec a b)) s = Some (tt, s') ->
  exec (execute_RTYPE rs2 rs1 rd OR) s = Some (RETIRE_SUCCESS, s').
Proof. intros Ha Hb Hw. unfold execute_RTYPE. cbn match.
  rewrite (exec_bind_Some _ _ _ (or_vec a b) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ Ha). rewrite (exec_bind_Some _ _ _ _ _ Hb). apply exec_returnm. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw). apply exec_returnm. Qed.

(* WpGprLogic.v : exec_execute_RTYPE_AND *)
Lemma exec_execute_RTYPE_AND (rs2 rs1 rd : regidx) (a b : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) -> exec (rX_bits rs2) s = Some (b, s) ->
  exec (wX_bits rd (and_vec a b)) s = Some (tt, s') ->
  exec (execute_RTYPE rs2 rs1 rd AND) s = Some (RETIRE_SUCCESS, s').
Proof. intros Ha Hb Hw. unfold execute_RTYPE. cbn match.
  rewrite (exec_bind_Some _ _ _ (and_vec a b) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ Ha). rewrite (exec_bind_Some _ _ _ _ _ Hb). apply exec_returnm. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw). apply exec_returnm. Qed.

(* WpGprLogic.v : exec_execute_RTYPE_XOR *)

(* WpGprLogic.v : exec_execute_ITYPE_ORI *)
Lemma exec_execute_ITYPE_ORI (imm : mword 12) (rs1 rd : regidx) (a : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) ->
  exec (wX_bits rd (or_vec a (sign_extend' 64 imm))) s = Some (tt, s') ->
  exec (execute (ITYPE (imm, rs1, rd, ORI))) s = Some (RETIRE_SUCCESS, s').
Proof. intros Ha Hw.
  change (execute (ITYPE (imm, rs1, rd, ORI))) with (execute_ITYPE imm rs1 rd ORI).
  unfold execute_ITYPE. cbn match.
  rewrite (exec_bind_Some _ _ _ (or_vec a (sign_extend' 64 imm)) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ Ha). apply exec_returnm. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw). apply exec_returnm. Qed.

(* WpGprLogic.v : exec_execute_ITYPE_ANDI *)
Lemma exec_execute_ITYPE_ANDI (imm : mword 12) (rs1 rd : regidx) (a : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) ->
  exec (wX_bits rd (and_vec a (sign_extend' 64 imm))) s = Some (tt, s') ->
  exec (execute (ITYPE (imm, rs1, rd, ANDI))) s = Some (RETIRE_SUCCESS, s').
Proof. intros Ha Hw.
  change (execute (ITYPE (imm, rs1, rd, ANDI))) with (execute_ITYPE imm rs1 rd ANDI).
  unfold execute_ITYPE. cbn match.
  rewrite (exec_bind_Some _ _ _ (and_vec a (sign_extend' 64 imm)) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ Ha). apply exec_returnm. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw). apply exec_returnm. Qed.

(* WpGprLogic.v : exec_execute_ITYPE_XORI *)

(* ---------------------------------------------------------------------- *)
(* File-generic value + execute for each op (mirror [gpr_addi_val] /       *)
(* [gpr_mul_val] and [exec_execute_ITYPE_ADDI_gpr] / [exec_execute_MUL_gpr]). *)
(* ---------------------------------------------------------------------- *)

(* ===== register/register: OR / AND / XOR (two sources, like MUL) ===== *)

(* WpGprLogic.v : gpr_or_val *)
Definition gpr_or_val (rs2 rs1 : mword 5) (s : mstate) : mword 64 :=
  or_vec (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
         (if Z.eqb (uint rs2) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs)).

(* WpGprLogic.v : gpr_and_val *)
Definition gpr_and_val (rs2 rs1 : mword 5) (s : mstate) : mword 64 :=
  and_vec (if Z.eqb (uint rs1) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
          (if Z.eqb (uint rs2) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs)).

(* WpGprLogic.v : gpr_xor_val *)

(* WpGprLogic.v : exec_execute_RTYPE_OR_gpr *)
Lemma exec_execute_RTYPE_OR_gpr (rs2 rs1 rd : mword 5) s :
  uint rd <> 0 ->
  exec (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR))) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
            (regval_into_reg (gpr_or_val rs2 rs1 s))).
Proof.
  intro Hrd. unfold gpr_or_val.
  change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)))
    with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) OR).
  eapply exec_execute_RTYPE_OR.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_rX_bits_gpr rs2 s).
  - rewrite exec_wX_bits_gpr.
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(* WpGprLogic.v : exec_execute_RTYPE_AND_gpr *)
Lemma exec_execute_RTYPE_AND_gpr (rs2 rs1 rd : mword 5) s :
  uint rd <> 0 ->
  exec (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND))) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
            (regval_into_reg (gpr_and_val rs2 rs1 s))).
Proof.
  intro Hrd. unfold gpr_and_val.
  change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND)))
    with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) AND).
  eapply exec_execute_RTYPE_AND.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_rX_bits_gpr rs2 s).
  - rewrite exec_wX_bits_gpr.
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(* WpGprLogic.v : exec_execute_RTYPE_XOR_gpr *)

(* WpGprLogic.v-style : RTYPE SRL (register shift -- walk's loop-variable
   shift amount) *)
Definition gpr_srl_val (rs2 rs1 : mword 5) (s : mstate) : mword 64 :=
  shift_bits_right
    (if Z.eqb (uint rs1) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    (subrange_vec_dec
       (if Z.eqb (uint rs2) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))
       (Z.sub log2_xlen 1) 0).

Lemma exec_execute_RTYPE_SRL (rs2 rs1 rd : regidx) (a b : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) ->
  exec (rX_bits rs2) s = Some (b, s) ->
  exec (wX_bits rd (shift_bits_right a (subrange_vec_dec b (Z.sub log2_xlen 1) 0))) s
  = Some (tt, s') ->
  exec (execute_RTYPE rs2 rs1 rd SRL) s = Some (RETIRE_SUCCESS, s').
Proof.
  intros Ha Hb Hw. unfold execute_RTYPE. cbn match.
  rewrite (exec_bind_Some _ _ _
             (shift_bits_right a (subrange_vec_dec b (Z.sub log2_xlen 1) 0)) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ Ha).
      rewrite (exec_bind_Some _ _ _ _ _ Hb). apply exec_returnm. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw). apply exec_returnm.
Qed.

Lemma exec_execute_RTYPE_SRL_gpr (rs2 rs1 rd : mword 5) s :
  uint rd <> 0 ->
  exec (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SRL))) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
            (regval_into_reg (gpr_srl_val rs2 rs1 s))).
Proof.
  intro Hrd. unfold gpr_srl_val.
  change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SRL)))
    with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) SRL).
  eapply exec_execute_RTYPE_SRL.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_rX_bits_gpr rs2 s).
  - rewrite exec_wX_bits_gpr.
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(* ===== register/immediate: ORI / ANDI / XORI (one source, like ADDI) ===== *)

(* WpGprLogic.v : gpr_ori_val *)
Definition gpr_ori_val (rs1 : mword 5) (imm : mword 12) (s : mstate) : mword 64 :=
  or_vec (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
         (sign_extend' 64 imm).

(* WpGprLogic.v : gpr_andi_val *)
Definition gpr_andi_val (rs1 : mword 5) (imm : mword 12) (s : mstate) : mword 64 :=
  and_vec (if Z.eqb (uint rs1) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
          (sign_extend' 64 imm).

(* WpGprLogic.v : gpr_xori_val *)

(* WpGprLogic.v : exec_execute_ITYPE_ORI_gpr *)
Lemma exec_execute_ITYPE_ORI_gpr (rs1 rd : mword 5) (imm : mword 12) s :
  exec (execute (ITYPE (imm, Regidx rs1, Regidx rd, ORI))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_ori_val rs1 imm s))).
Proof.
  unfold gpr_ori_val.
  eapply exec_execute_ITYPE_ORI.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_wX_bits_gpr rd _ s).
Qed.

(* WpGprLogic.v : exec_execute_ITYPE_ANDI_gpr *)
Lemma exec_execute_ITYPE_ANDI_gpr (rs1 rd : mword 5) (imm : mword 12) s :
  exec (execute (ITYPE (imm, Regidx rs1, Regidx rd, ANDI))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_andi_val rs1 imm s))).
Proof.
  unfold gpr_andi_val.
  eapply exec_execute_ITYPE_ANDI.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_wX_bits_gpr rd _ s).
Qed.

(* WpGprLogic.v : exec_execute_ITYPE_XORI_gpr *)

(* ====================================================================== *)
(* The register-GENERIC RTYPE logic WPs: `<op> rd,rs1,rs2`, ANY triple     *)
(* (rs1 may equal rs2), all GPRs held as the single [gpr_file] resource.   *)
(* Structurally identical to [wp_mul_gpr]; only the written value differs   *)
(* (or_vec / and_vec / xor_vec).                                            *)
(* ====================================================================== *)

(* WpGprLoad.v : sign_extend *)
Lemma sign_extend'_id (a : mword 64) : sign_extend' 64 a = a.
Proof.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec to_word get_word
       MachineWord.MachineWord.sign_extend].
  apply bv_eq_signed. rewrite bv_sign_extend_signed; [ reflexivity | lia ].
Qed.

(* [subrange_id] / [exec_ext_data_get_addr_gpr] moved to WpGpr.v so that
   WpGprStore.v (which shares them) need not wait for this file. *)

(* writing all 64 bits of [v] into a zero word yields [v] -- a noop. *)

(* WpGprLoad.v : data2_id *)
Lemma data2_id (v : mword 64) :
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v = v.
Proof.
  apply bv_eq. unfold update_subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.update_slice, MachineWord.MachineWord.slice.
  erewrite bv_concat_unsigned by (cbn; lia).
  erewrite bv_concat_unsigned by (cbn; lia).
  rewrite !bv_unsigned_N_0.
  rewrite Z.shiftl_0_l. rewrite Z.shiftl_0_r. rewrite Z.lor_0_r. rewrite Z.lor_0_l.
  reflexivity.
Qed.


(* register-generic 8-byte vmem_read: base address from ANY rs1. *)

(* WpGprLoad.v : VRg *)
Section VRg.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable v : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Let data2 : mword (8*1*8) :=
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Hpmp : forall j, pmpAddrMatchType_encdec_backwards
   (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) j)) = OFF.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_vmem_read_8_gpr :
  exec (vmem_read (Regidx rs1) offset 8 (Load Data) false false false) s = Some (Ok data2, s).
Proof.
  unfold vmem_read. rewrite exec_catch_early_return.
  assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Load Data) 8) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Load Data) 8 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_load ea s Hcp Hmprv Hpmm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
  rewrite execR_liftR.
  rewrite (exec_vmem_read_addr_8 a8 v region s Halign Hcp Hmprv Hpmp Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes).
  reflexivity.
Qed.
End VRg.

(* WpGprLoad.v : ExecLoadG *)
Section ExecLoadG.
Variable rs1 rd : mword 5.
Variable imm : mword 12.
Variable v : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let offset := sign_extend' 64 imm.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Let data2 : mword (8*1*8) :=
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.
Hypothesis Hrd : uint rd <> 0.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Hpmp : forall j, pmpAddrMatchType_encdec_backwards
   (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) j)) = OFF.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_execute_LOAD_8_gpr :
  exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (extend_value false data2))).
Proof.
  change (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8)))
    with (execute_LOAD imm (Regidx rs1) (Regidx rd) false 8).
  unfold execute_LOAD.
  replace (8 <=? xlen_bytes) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _
    (exec_vmem_read_8_gpr rs1 offset v region s Hcp Hmprv Hpmm Halign Hpmp Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes)).
  cbn match.
  assert (Hw : exec (wX_bits (Regidx rd) (extend_value false data2)) s
               = Some (tt, set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (extend_value false data2)))).
  { rewrite (exec_wX_bits_gpr rd (extend_value false data2) s).
    rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw).
  apply exec_returnM.
Qed.
End ExecLoadG.

(* WpGprLoad.v : ForwardLDg *)
Section ForwardLDg.
  Context (s : mstate) (w : mword 32) (pc : mword 64) (imm : mword 12)
          (rs1 rd : mword 5) (data : mword 64) (b : bool).
  Hypothesis Hrd : uint rd <> 0.
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hdec_gen : forall s0 : mstate,
    register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, false, 8), s0).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hexec_spc :
    exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8)))
         (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
    = Some (RETIRE_SUCCESS,
            set_reg (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
                    (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (extend_value false data))).


  Variable mst0 : mword 64.
  Hypothesis Lmst_l : register_lookup minstret s.(sregs) = mst0.


End ForwardLDg.

(* WpGprStore.v : exec_write_ram_plain_8 *)
Lemma exec_write_ram_plain_8 (addr : mword 64) (data : bv 64) s :
  dev_addr addr = false ->
  exec (write_ram rv64d_types.Write_plain (Physaddr addr) 8 data tt) s
  = Some (true, MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev)).
Proof.
  intros Hdev.
  unfold write_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_write. cbn beta zeta iota match.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  cbn match.
  rewrite exec_MemWrite; last exact Hdev.
  reflexivity.
Qed.

(* WpGprStore.v : within_htif_writable_false *)
Lemma within_htif_writable_false (a : Arch.pa) (w : Z) s :
  register_lookup htif_tohost_base s.(sregs) = None ->
  exec (within_htif_writable (Physaddr a) w) s = Some (false, s).
Proof.
  intro Hn. unfold within_htif_writable.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg htif_tohost_base s)).
  rewrite Hn. cbn match. apply exec_returnm.
Qed.

(* WpGprStore.v : exec_pmaCheck_ram_store *)
Lemma exec_pmaCheck_ram_store (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (pmaCheck (Physaddr addr) 8 (Store Data) pbmt false) s = Some (None, s).
Proof.
  intros Hmatch Halign Hwrite.
  unfold pmaCheck.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hwrite |- *.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
  cbn match beta.
  change (assert_exp' true "sys/mem.sail:106.61-106.62" >>=
          (fun _ : true = true => returnM (PMA_writable (override_PMA rattr pbmt))))
    with (returnM (PMA_writable (override_PMA rattr pbmt)) : M bool).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite Hwrite. cbn match.
  apply exec_returnM.
Qed.

(* WpGprStore.v : exec_checked_mem_write_ram_store *)
Lemma exec_checked_mem_write_ram_store (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 64) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i)) = OFF) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 8) s = Some (false, s) ->
  dev_addr addr = false ->
  exec (checked_mem_write (Physaddr addr) 8 data (Store Data) pbmt Machine tt false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev)).
Proof.
  intros Hpmp Hmatch Halign Hwrite Hc Hsig Hh Hdev.
  unfold checked_mem_write.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_machine_none _ _ _ s Hpmp)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_store addr pbmt region s Hmatch Halign Hwrite)).
      cbn match. apply exec_returnM. }
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_writable (Physaddr addr) 8) s = Some (false, s))).
  2:{ unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (write_kind_of_flags false false false) s = Some (rv64d_types.Write_plain, s))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_write_ram_plain_8 addr data s Hdev)).
  apply exec_returnM.
Qed.

(* WpGprStore.v : exec_effectivePrivilege_store *)
Lemma exec_effectivePrivilege_store (m : mword 64) s :
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  exec (effectivePrivilege (Store Data) m Machine) s = Some (Machine, s).
Proof.
  intro H. unfold effectivePrivilege. cbn [generic_neq generic_eq].
  rewrite H. cbn [andb]. apply exec_returnm.
Qed.

(* WpGprStore.v : exec_is_shadow_stack_store *)
Lemma exec_is_shadow_stack_store s :
  exec (is_shadow_stack_access (Store Data)) s = Some (false, s).
Proof. unfold is_shadow_stack_access. cbn match. apply exec_returnM. Qed.

(* WpGprStore.v : exec_translateAddr_identity_store *)
Lemma exec_translateAddr_identity_store (a : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false ->
  exec (translateAddr (Virtaddr a) (Store Data)) s
    = Some (Ok (Physaddr (zero_extend' 64 (bits_of_virtaddr (Virtaddr a))), PBMT_PMA, init_ext_ptw), s).
Proof.
  intros Hcp Hmprv.
  unfold translateAddr.
  rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_store _ s Hmprv)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_M s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_store s)).
  unfold Defs.bind0.
  replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity).
  rewrite execR_bind. cbn match. reflexivity.
Qed.

(* WpGprStore.v : exec_mem_write_ea *)
Lemma exec_mem_write_ea (addr : mword 64) s :
  exec (mem_write_ea (Physaddr addr) 8 false false false) s = Some (Ok tt, s).
Proof.
  unfold mem_write_ea. cbn [orb andb].
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (write_kind_of_flags false false false) s = Some (rv64d_types.Write_plain, s))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
  apply exec_returnM.
Qed.

(* WpGprStore.v : exec_mem_write_value_8 *)
Lemma exec_mem_write_value_8 (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 64) (m : mword 64) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i)) = OFF) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 8) s = Some (false, s) ->
  dev_addr addr = false ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (mem_write_value (Physaddr addr) 8 data (Store Data) pbmt false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev)).
Proof.
  intros Hpmp Hmatch Halign Hwrite Hc Hsig Hh Hdev Hms Hmprv Hpriv.
  unfold mem_write_value, mem_write_value_meta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv. rewrite Hms.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_store m s Hmprv)).
  unfold mem_write_value_priv_meta. cbn [orb andb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_checked_mem_write_ram_store pbmt addr region data s Hpmp Hmatch Halign Hwrite Hc Hsig Hh Hdev)).
  cbn match. unfold mem_write_callback. apply exec_returnm.
Qed.

(* WpGprStore.v : SW *)
Section SW.
Variable a : mword 64.
Variable data : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let pa := zero_extend' 64 (add_vec_int a (0 * 8)).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 8 = true.
Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmp : forall i, pmpAddrMatchType_encdec_backwards
   (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i)) = OFF.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_vmem_write_addr_8 :
  exec (vmem_write_addr (Virtaddr a) 8 data (Store Data) false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) pa 8 data) s.(mdev)).
Proof.
  unfold vmem_write_addr.
  rewrite exec_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR (returnR (result bool ExecutionResult) tt >>
                          liftR (split_misaligned (Virtaddr a) 8)) s = Some (inr (1, 8), s)).
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
    rewrite execR_liftR. rewrite (exec_split_misaligned_aligned (Virtaddr a) s Halign). reflexivity. }
  rewrite (execR_bind_Some _ _ _ _ _ Hinner).
  rewrite misaligned_order_1.
  match goal with
  | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s
                 = Some (inr (true, 0%Z, true), MState s.(sregs) (write_bytes s.(mem) pa 8 data) s.(mdev)))
  end.
  { eapply execR_untilMT_1.
    - reflexivity.
    - (* body, vars = (false, 0, true) *)
      cbn match.
      assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
      rewrite (execR_liftR_seq _ _ _ _ _ Hass).
      rewrite (execR_liftR_seq _ _ _ _ _
        (exec_translateAddr_identity_store (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0*8)) s Hpriv Hmprv)).
      cbn [bits_of_virtaddr]. cbn match.
      (* SC dummy assert (Bool.eqb false (is_store_conditional (Store Data)) = true) *)
      assert (Hsc : exec (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51") s
                    = Some (tt, s)) by reflexivity.
      assert (Hscm : execR (Defs.liftR (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51")
                            : Defs.monadR (result bool ExecutionResult) exception unit) s = Some (inr tt, s))
        by (rewrite execR_liftR; rewrite Hsc; reflexivity).
      (* Isolate the SC-assert >> if-expression as Hinner; proving it in a
         nested goal keeps the outer goal from definitionally reducing the
         if's else branch through mem_write_value (the over-reduction trap). *)
      match goal with
      | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
          assert (Hwrloop : execR (Defs.bind0 (Defs.liftR asrt) Nbody) s
                           = Some (inr true, MState s.(sregs) (write_bytes s.(mem) pa 8 data) s.(mdev)))
      end.
      { (* peel the SC assert, keeping the if-expression opaque via [set] so
           the bind0 rewrite cannot reduce its else branch *)
        match goal with
        | |- execR (Defs.bind0 _ ?Nbody) s = _ => set (NN := Nbody)
        end.
        rewrite (execR_bind0_Some _ _ _ _ Hscm).
        unfold NN; clear NN.
        (* strip [if (andb false _) then THEN else ELSE] -> ELSE by conversion *)
        match goal with
        | |- execR (match _ as x in bool return @?P x with | true => _ | false => ?B end) ?ss = ?R =>
            change (execR B ss = R)
        end.
        (* ELSE: mem_write_ea -> Ok tt *)
        rewrite (execR_liftR_seq _ _ _ _ _ (exec_mem_write_ea (zero_extend' 64 (add_vec_int a (0*8))) s)).
        cbn match.
        (* autocast (subrange data 63 0) = data : capture the value arg from the
           goal (so it carries the mword (8*8) type) and rewrite it to data *)
        match goal with
        | |- context [ mem_write_value ?pp 8 ?D (Store Data) ?pb false false false ] =>
            replace D with data
        end.
        2: { symmetry.
             change (8*(0+1)*8-1) with 63. change (8*0*8) with 0. change (8*8) with 64.
             change (63 - 0 + 1) with 64. rewrite autocast_id.
             unfold subrange_vec_dec. change (63 - 0 + 1) with 64. rewrite autocast_id.
             unfold to_word_idx, to_word, get_word, MachineWord.slice.
             rewrite MachineWord.cast_idx_refl.
             apply bv_eq. rewrite bv_extract_unsigned.
             change (Z.of_N (MachineWord.Z_idx 0)) with 0. rewrite Z.shiftr_0_r.
             apply bv_wrap_bv_unsigned. }
        (* mem_write_value -> Ok true, write_bytes state *)
        rewrite (execR_liftR_seq _ _ _ _ _
          (exec_mem_write_value_8 PBMT_PMA (zero_extend' 64 (add_vec_int a (0*8))) region data
             (register_lookup mstatus s.(sregs)) s Hpmp Hmatch Hpalign Hwrite Hc Hsig Hh Hdev eq_refl Hmprv Hpriv)).
        cbn match.
        apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hwrloop).
      cbn.
      apply execR_returnR_fwd.
    - apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu).
  cbn. reflexivity.
Qed.
End SW.

(* WpGprStore.v : exec_is_pmm_applicable_store *)
Lemma exec_is_pmm_applicable_store s :
  exec (is_pmm_applicable (Store Data) Machine) s = Some (true, s).
Proof.
  unfold is_pmm_applicable.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Store Data) (InstructionFetch tt)) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Store Data) (Load PageTableEntry)) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Store Data) (Store PageTableEntry)) with true by (vm_compute; reflexivity). cbn match.
  match goal with
  | |- context [ and_boolM ?orb _ ] => assert (Hor : exec orb s = Some (true, s))
  end.
  { rewrite (exec_or_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
    replace (generic_eq Machine Machine) with true by (vm_compute; reflexivity). reflexivity. }
  rewrite (exec_and_boolM_Some _ _ _ _ _ Hor).
  cbn match.
  rewrite (exec_returnM _ s).
  replace (xlen =? 64) with true by (vm_compute; reflexivity). reflexivity.
Qed.

(* WpGprStore.v : exec_get_pmlen_store *)
Lemma exec_get_pmlen_store s :
  pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled ->
  exec (get_pmlen (Store Data) Machine) s = Some (0, s).
Proof.
  intro Hpmm. unfold get_pmlen.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_is_pmm_applicable_store s)).
  cbn match.
  assert (Hgp : exec (get_pmm Machine) s
          = Some (pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))), s)).
  { unfold get_pmm. rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mseccfg s)). apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hgp).
  rewrite Hpmm.
  apply exec_returnM.
Qed.

(* WpGprStore.v : exec_transform_effective_address_store *)
Lemma exec_transform_effective_address_store (ea : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled ->
  exec (transform_effective_address (Virtaddr ea) (Store Data)) s
    = Some (pm_transform_PA (Virtaddr ea) 0, s).
Proof.
  intros Hcp Hmprv Hpmm. unfold transform_effective_address.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_store _ s Hmprv)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_get_pmlen_store s Hpmm)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_translationMode_M s)).
  replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity). cbn match.
  apply exec_returnM.
Qed.

(* register-generic 8-byte vmem_write: base address from ANY rs1 (incl. x0 ->
   zero_reg), value [data]. *)

(* WpGprStore.v : VWg *)
Section VWg.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable data : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Hpmp : forall j, pmpAddrMatchType_encdec_backwards
   (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) j)) = OFF.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_vmem_write_8_gpr :
  exec (vmem_write (Regidx rs1) offset 8 data (Store Data) false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) pa 8 data) s.(mdev)).
Proof.
  unfold vmem_write. rewrite exec_catch_early_return.
  assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Store Data) 8) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) 8 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_store ea s Hcp Hmprv Hpmm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
  rewrite execR_liftR.
  rewrite (exec_vmem_write_addr_8 a8 data region s Halign Hcp Hmprv Hpmp Hmatch Hpalign Hwrite Hc Hsig Hh Hdev).
  reflexivity.
Qed.
End VWg.

(* WpGprStore.v : autocast_subrange_id *)
Lemma autocast_subrange_id (d : bv 64) :
  @autocast mword ((8*8-1) - 0 + 1) (8*8) _ (@subrange_vec_dec 64 d (8*8-1) 0) = d.
Proof.
  change (8*8-1) with 63. change (8*8) with 64. change (63 - 0 + 1) with 64.
  rewrite autocast_id.
  unfold subrange_vec_dec. change (63 - 0 + 1) with 64. rewrite autocast_id.
  unfold to_word_idx, to_word, get_word, MachineWord.slice.
  rewrite MachineWord.cast_idx_refl.
  apply bv_eq. rewrite bv_extract_unsigned.
  change (Z.of_N (MachineWord.Z_idx 0)) with 0. rewrite Z.shiftr_0_r.
  apply bv_wrap_bv_unsigned.
Qed.

(* register-generic 8-byte STORE execute: base from rs1, value from rs2 (ANY
   rs1/rs2, incl. x0 -> zero_reg for both the base and the stored value). *)

(* WpGprStore.v : ExecStoreG *)
Section ExecStoreG.
Variable rs2 rs1 : mword 5.
Variable imm : mword 12.
Variable region : PMA_Region.
Variable s : mstate.
Let offset := sign_extend' 64 imm.
Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Hpmp : forall j, pmpAddrMatchType_encdec_backwards
   (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) j)) = OFF.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_execute_STORE_8_gpr :
  exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s
    = Some (RETIRE_SUCCESS, MState s.(sregs) (write_bytes s.(mem) pa 8 vrs2) s.(mdev)).
Proof.
  change (execute (STORE (imm, Regidx rs2, Regidx rs1, 8)))
    with (execute_STORE imm (Regidx rs2) (Regidx rs1) 8).
  unfold execute_STORE.
  replace (8 <=? xlen_bytes) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:320.28-320.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
    (exec_vmem_write_8_gpr rs1 offset _ region s Hcp Hmprv Hpmm Halign Hpmp Hmatch Hpalign Hwrite Hc Hsig Hh Hdev)).
  cbn match.
  rewrite (exec_returnM _ _).
  rewrite autocast_subrange_id.
  reflexivity.
Qed.
End ExecStoreG.

(* WpGprStore.v : MemUpdate *)
Section MemUpdate.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context {dqc : dfrac}.

  (* single-byte update (no [mem_update] exists in RiscvPtsto). *)
  Lemma mem_update (mm : _) (a : Arch.pa) (v v' : bv 8) :
    gen_heap_interp (hG:=riscv_memGS) mm -∗ a ↦ₘ v ==∗ gen_heap_interp (hG:=riscv_memGS) (<[a := v']> mm) ∗ a ↦ₘ v'.
  Proof.
    (* [mem_pointsto] is [Typeclasses Opaque] (sealed in RiscvPtsto); unfold it
       here so the raw [pointsto ∗ ⌜addr_is_ram⌝] conjunction can be destructed. *)
    rewrite /mem_pointsto. iIntros "Hm [Ha %Hram]".
    iMod (gen_heap_update with "Hm Ha") as "[Hm Ha]".
    iModIntro. iFrame "Hm Ha". iPureIntro. exact Hram.
  Qed.

  (* window update over an arbitrary index list (write_bytes is a foldr). *)
  Lemma upd_window (mm : _) (pa : Arch.pa) (vnew vold : bv 64)
      (l : list nat) :
    gen_heap_interp (hG:=riscv_memGS) mm -∗ ([∗ list] j ∈ l, (pa_add pa j) ↦ₘ nth_byte vold j) ==∗
    gen_heap_interp (hG:=riscv_memGS) (foldr (fun j acc => <[pa_add pa j := nth_byte vnew j]> acc) mm l)
      ∗ ([∗ list] j ∈ l, (pa_add pa j) ↦ₘ nth_byte vnew j).
  Proof.
    iInduction l as [|x xs IH] "IH"; simpl.
    - iIntros "Hm _". iModIntro. iFrame.
    - iIntros "Hm [Ha Hrest]".
      iMod ("IH" with "Hm Hrest") as "[Hm Hrest]".
      iMod (mem_update _ (pa_add pa x) (nth_byte vold x) (nth_byte vnew x) with "Hm Ha") as "[Hm Ha]".
      iModIntro. iFrame "Ha Hrest Hm".
  Qed.

  Lemma upd_window_8 (mm : _) (pa : Arch.pa) (vnew vold : bv 64) :
    gen_heap_interp (hG:=riscv_memGS) mm -∗ ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte vold j) ==∗
    gen_heap_interp (hG:=riscv_memGS) (write_bytes mm pa 8 vnew)
      ∗ ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte vnew j).
  Proof. unfold write_bytes. change (N.to_nat 8) with 8%nat. apply upd_window. Qed.
End MemUpdate.

(* WpGprAuipc.v : exec_execute_UTYPE_AUIPC_gpr *)
Lemma exec_execute_UTYPE_AUIPC_gpr (rd : mword 5) (imm : mword 20) s :
  exec (execute (UTYPE (imm, Regidx rd, AUIPC))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg
                    (add_vec (register_lookup PC s.(sregs)) (auipc_off imm)))).
Proof.
  change (execute (UTYPE (imm, Regidx rd, AUIPC)))
    with (execute_UTYPE imm (Regidx rd) AUIPC).
  unfold execute_UTYPE, auipc_off. cbn match.
  rewrite (exec_bind_Some _ _ _
             (add_vec (register_lookup PC s.(sregs))
                      (sign_extend' 64 (concat_vec imm (Ox"000")))) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_get_arch_pc s)). apply exec_returnm. }
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)). apply exec_returnm.
Qed.

(* WpGprLui.v : luival *)
Definition luival (imm : mword 20) : mword 64 :=
  sign_extend' 64 (concat_vec imm ((Ox"000") : mword 12)).

(* register-GENERIC LUI execute: writes rd := luival imm (no source register),
   via the file-generic wX lemma ([exec_wX_bits_gpr]).  Independent of the
   gpr_file representation, so reused unchanged from the old development. *)

(* WpGprLui.v : exec_execute_UTYPE_LUI_gpr *)
Lemma exec_execute_UTYPE_LUI_gpr (rd : mword 5) (imm : mword 20) s :
  exec (execute (UTYPE (imm, Regidx rd, LUI))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (luival imm))).
Proof.
  change (execute (UTYPE (imm, Regidx rd, LUI)))
    with (execute_UTYPE imm (Regidx rd) LUI).
  unfold execute_UTYPE. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  apply exec_returnm.
Qed.

(* --- relocated from WpKfree.v / WpHolding.v: pure register-generic execute
   facts for SLTU / SUB / SLTIU, needed by the S-mode per-instruction leaf
   lemmas (kept here in the shared exec base to avoid import cycles). --- *)
Definition gpr_sltu_val (rs2 rs1 : mword 5) (s : mstate) : mword 64 :=
  zero_extend' 64 (bool_to_bit (zopz0zI_u
    (if Z.eqb (uint rs1) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    (if Z.eqb (uint rs2) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs)))).

Lemma exec_execute_RTYPE_SLTU (rs2 rs1 rd : regidx) (a b : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) -> exec (rX_bits rs2) s = Some (b, s) ->
  exec (wX_bits rd (zero_extend' 64 (bool_to_bit (zopz0zI_u a b)))) s = Some (tt, s') ->
  exec (execute_RTYPE rs2 rs1 rd SLTU) s = Some (RETIRE_SUCCESS, s').
Proof. intros Ha Hb Hw. unfold execute_RTYPE. cbn match.
  rewrite (exec_bind_Some _ _ _ (zero_extend' 64 (bool_to_bit (zopz0zI_u a b))) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ Ha). rewrite (exec_bind_Some _ _ _ _ _ Hb). apply exec_returnm. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw). apply exec_returnm. Qed.

Lemma exec_execute_RTYPE_SLTU_gpr (rs2 rs1 rd : mword 5) s :
  uint rd <> 0 ->
  exec (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SLTU))) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
            (regval_into_reg (gpr_sltu_val rs2 rs1 s))).
Proof.
  intro Hrd. unfold gpr_sltu_val.
  change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SLTU)))
    with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) SLTU).
  eapply exec_execute_RTYPE_SLTU.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_rX_bits_gpr rs2 s).
  - rewrite exec_wX_bits_gpr.
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

Definition gpr_sub_val (rs2 rs1 : mword 5) (s : mstate) : mword 64 :=
  sub_vec (if Z.eqb (uint rs1) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
          (if Z.eqb (uint rs2) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs)).

Lemma exec_execute_RTYPE_SUB_gpr (rs2 rs1 rd : mword 5) s :
  exec (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) SUB) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_sub_val rs2 rs1 s))).
Proof.
  unfold gpr_sub_val.
  unfold execute_RTYPE. cbn match.
  rewrite (exec_bind_Some _ _ _ (gpr_sub_val rs2 rs1 s) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
      apply exec_returnm. }
  unfold gpr_sub_val.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  destruct (Z.eqb (uint rd) 0); apply exec_returnm.
Qed.

Definition gpr_sltiu_val (rs1 : mword 5) (imm : mword 12) (s : mstate) : mword 64 :=
  zero_extend' 64 (bool_to_bit (zopz0zI_u
    (if Z.eqb (uint rs1) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    (sign_extend' 64 imm))).

Lemma exec_execute_ITYPE_SLTIU_gpr (rs1 rd : mword 5) (imm : mword 12) s :
  exec (execute (ITYPE (imm, Regidx rs1, Regidx rd, SLTIU))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_sltiu_val rs1 imm s))).
Proof.
  change (execute (ITYPE (imm, Regidx rs1, Regidx rd, SLTIU)))
    with (execute_ITYPE imm (Regidx rs1) (Regidx rd) SLTIU).
  unfold execute_ITYPE. cbn zeta match.
  rewrite (exec_bind_Some _ _ _ (gpr_sltiu_val rs1 imm s) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
      apply exec_returnm. }
  unfold gpr_sltiu_val.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  destruct (Z.eqb (uint rd) 0); apply exec_returnm.
Qed.


(* WpGprJalr.v : exec_cE_zicfilp_false *)
Lemma exec_cE_zicfilp_false s :
  register_lookup cur_privilege (sregs s) = Machine ->
  bool_bit_backwards (_get_Seccfg_MLPE (register_lookup mseccfg s.(sregs))) = false ->
  exec (currentlyEnabled Ext_Zicfilp) s = Some (false, s).
Proof.
  intros Hpriv Hmlpe.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zicfilp) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _
            (exec_rec_cE_Zicsr_any (currentlyEnabled_measure Ext_Zicfilp - 1) _ s
               ltac:(vm_compute; reflexivity))).
  cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Zicfilp s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). rewrite Hpriv.
  match goal with |- context[_rec_get_xLPE Machine _ ?acc] => destruct acc end.
  cbn [_rec_get_xLPE]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zicfilp - 1) 0) with true by (vm_compute; reflexivity).
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mseccfg s)). cbn match.
  rewrite Hmlpe. apply exec_returnM.
Qed.

(* base register value read by JALR, uniform over rs1 (x0 -> zero_reg). *)

(* WpGprJalr.v : jbase *)

(* Target of the JALR jump: (rs1 + sign_extend imm) with the low bit forced 0. *)

(* WpGprJalr.v : jalr_target *)

(* register-generic JALR execute: target = (rX rs1 + imm) with bit0 cleared;
   writes rd := link (nextPC), sets nextPC := target.  ANY rs1 (x0->zero_reg), rd<>0. *)

(* WpGprJalr.v : exec_execute_JALR_gpr *)

(* ret = jalr x0, 0(ra): rd = x0 (uint 0) => NO link write; just PC := target.
   Kept as an exec-level fact (representation-independent). *)

(* WpGprJalr.v : exec_execute_JALR_ret *)

(* [exec_execute_JALR_ret] for a merely 2-aligned return target under the C
   extension: the model's misalignment check reduces via [exec_jump_to_zca],
   so only bit 0 = 0 (automatic for [cret_target]) is needed, not bit 1. *)
Lemma exec_execute_JALR_ret_zca (imm : mword 12) (rs1 rdz : mword 5) s :
  uint rs1 <> 0 -> uint rdz = 0 ->
  exec (currentlyEnabled Ext_Zicfilp) s = Some (false, s) ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  eq_vec (access_vec_dec (update_vec_dec (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (sign_extend' 64 imm)) 0 ('b"0")) 0) ('b"0") = true ->
  exec (execute_JALR imm (Regidx rs1) (Regidx rdz)) s
  = Some (RETIRE_SUCCESS,
          set_reg s nextPC (update_vec_dec (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (sign_extend' 64 imm)) 0 ('b"0"))).
Proof.
  intros Hrs1 Hrdz Hzic Hzca Halign.
  unfold execute_JALR.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.bind0 (update_elp_state (Regidx rs1)) (get_next_pc tt)) s
                 = Some (register_lookup nextPC s.(sregs), s))).
  2:{ rewrite (exec_bind0_Some _ _ _ _ _
                (_ : exec (update_elp_state (Regidx rs1)) s = Some (tt, s))).
      2:{ unfold update_elp_state. rewrite (exec_bind_Some _ _ _ _ _ Hzic). cbn match. apply exec_returnm. }
      unfold get_next_pc. exact (exec_read_reg nextPC s). }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_jump_to_zca _ s Halign Hzca)).
  cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _
            (exec_wX_bits_gpr rdz (register_lookup nextPC s.(sregs))
                (set_reg s nextPC (update_vec_dec (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (sign_extend' 64 imm)) 0 ('b"0"))))).
  rewrite Hrdz. cbn match. apply exec_returnm.
Qed.

(* ====================================================================== *)
(* The register-GENERIC JALR WP: ONE lemma for `jalr rd, imm(rs1)`, ANY    *)
(* rd/rs1 (both nonzero), with all GPRs held as the single [gpr_file].      *)
(* CONTROL FLOW: writes rd := pc+4 (return addr) and jumps to the target.   *)
(* ====================================================================== *)

(* WpGprRvc.v : cli_rs1 *)
Definition cli_rs1 : mword 5 := zero_extend' 5 ('b"00").

(* WpGprRvc.v : csp_rs1 *)
Definition csp_rs1 : mword 5 := zero_extend' 5 ('b"10").

(* WpGprRvc.v : caddi16sp_imm *)
Definition caddi16sp_imm (imm : mword 6) : mword 12 := sign_extend' 12 (concat_vec imm (Ox"0")).

(* WpGprRvc.v : caddi4spn_imm *)
Definition caddi4spn_imm (nzimm : mword 8) : mword 12 := concat_vec ('b"00") (concat_vec nzimm ('b"00")).

(* ===================================================================== *)
(* ExecuteAs-expansion facts: exec (execute (C_..)) = ExecuteAs base.       *)
(* Representation-independent; reused verbatim.                            *)
(* ===================================================================== *)

(* WpGprRvc.v : exec_execute_C_LI *)
Lemma exec_execute_C_LI (imm : mword 6) (rd : regidx) s :
  exec (execute (C_LI (imm, rd))) s
    = Some (ExecuteAs (ITYPE (sign_extend' 12 imm, zreg, rd, ADDI)), s).
Proof. unfold execute. cbn match. unfold execute_C_LI. apply exec_returnM. Qed.

(* WpGprRvc.v : exec_execute_C_LUI *)
Lemma exec_execute_C_LUI (imm : mword 6) (rd : regidx) s :
  exec (execute (C_LUI (imm, rd))) s
    = Some (ExecuteAs (UTYPE (sign_extend' 20 imm, rd, LUI)), s).
Proof. unfold execute. cbn match. unfold execute_C_LUI. apply exec_returnM. Qed.

(* WpGprRvc.v : exec_execute_C_SRLI *)
Lemma exec_execute_C_SRLI (shamt : mword 6) (crsd : cregidx) s :
  exec (execute (C_SRLI (shamt, crsd))) s
    = Some (ExecuteAs (SHIFTIOP (shamt, creg2reg_idx crsd, creg2reg_idx crsd, SRLI)), s).
Proof. unfold execute. cbn match. unfold execute_C_SRLI. cbn zeta. apply exec_returnM. Qed.

(* WpGprRvc.v : exec_execute_C_SLLI *)
Lemma exec_execute_C_SLLI (shamt : mword 6) (rsd : regidx) s :
  exec (execute (C_SLLI (shamt, rsd))) s
    = Some (ExecuteAs (SHIFTIOP (shamt, rsd, rsd, SLLI)), s).
Proof. unfold execute. cbn match. unfold execute_C_SLLI. cbn zeta. apply exec_returnM. Qed.

(* WpGprRvc.v : exec_execute_C_MV *)
Lemma exec_execute_C_MV (rd rs2 : regidx) s :
  exec (execute (C_MV (rd, rs2))) s = Some (ExecuteAs (RTYPE (rs2, zreg, rd, ADD)), s).
Proof. unfold execute. cbn match. unfold execute_C_MV. apply exec_returnM. Qed.

(* WpGprRvc.v : exec_execute_C_ADD *)
Lemma exec_execute_C_ADD (rsd rs2 : regidx) s :
  exec (execute (C_ADD (rsd, rs2))) s = Some (ExecuteAs (RTYPE (rs2, rsd, rsd, ADD)), s).
Proof. unfold execute. cbn match. unfold execute_C_ADD. apply exec_returnM. Qed.

(* the compressed word load/store: register-generic, so a function proof only
   has to bridge its own concrete creg indices and offset. *)
Lemma exec_execute_C_SW (uimm : mword 5) (rsc1 rsc2 : cregidx) s :
  exec (execute (C_SW (uimm, rsc1, rsc2))) s
  = Some (ExecuteAs (STORE (zero_extend' 12 (concat_vec uimm ('b"00")),
                            creg2reg_idx rsc2, creg2reg_idx rsc1, 4)), s).
Proof. unfold execute. cbn match. unfold execute_C_SW. cbn zeta. apply exec_returnM. Qed.

Lemma exec_execute_C_LW (uimm : mword 5) (rsc1 rdc : cregidx) s :
  exec (execute (C_LW (uimm, rsc1, rdc))) s
  = Some (ExecuteAs (LOAD (zero_extend' 12 (concat_vec uimm ('b"00")),
                           creg2reg_idx rsc1, creg2reg_idx rdc, false, 4)), s).
Proof. unfold execute. cbn match. unfold execute_C_LW. cbn zeta. apply exec_returnM. Qed.

(* WpGprRvc.v : exec_execute_C_ADDI *)
Lemma exec_execute_C_ADDI (imm : mword 6) (rsd : regidx) s :
  exec (execute (C_ADDI (imm, rsd))) s
    = Some (ExecuteAs (ITYPE (sign_extend' 12 imm, rsd, rsd, ADDI)), s).
Proof. unfold execute. cbn match. unfold execute_C_ADDI. apply exec_returnM. Qed.

(* WpGprRvc.v : exec_execute_C_ADDI16SP *)
Lemma exec_execute_C_ADDI16SP (imm : mword 6) s :
  exec (execute (C_ADDI16SP imm)) s
    = Some (ExecuteAs (ITYPE (caddi16sp_imm imm, sp, sp, ADDI)), s).
Proof. unfold execute. cbn match. unfold execute_C_ADDI16SP, caddi16sp_imm. cbn zeta. apply exec_returnM. Qed.

(* WpGprRvc.v : exec_execute_C_ADDI4SPN *)
Lemma exec_execute_C_ADDI4SPN (rdc : cregidx) (nzimm : mword 8) s :
  exec (execute (C_ADDI4SPN (rdc, nzimm))) s
    = Some (ExecuteAs (ITYPE (caddi4spn_imm nzimm, sp, creg2reg_idx rdc, ADDI)), s).
Proof. unfold execute. cbn match. unfold execute_C_ADDI4SPN, caddi4spn_imm. cbn zeta. apply exec_returnM. Qed.

(* WpGprRvc.v : exec_execute_C_OR *)
Lemma exec_execute_C_OR (rsd rs2 : cregidx) s :
  exec (execute (C_OR (rsd, rs2))) s
    = Some (ExecuteAs (RTYPE (creg2reg_idx rs2, creg2reg_idx rsd, creg2reg_idx rsd, OR)), s).
Proof. unfold execute. cbn match. unfold execute_C_OR. cbn zeta. apply exec_returnM. Qed.

(* WpGprRvc.v : exec_execute_C_AND *)
Lemma exec_execute_C_AND (rsd rs2 : cregidx) s :
  exec (execute (C_AND (rsd, rs2))) s
    = Some (ExecuteAs (RTYPE (creg2reg_idx rs2, creg2reg_idx rsd, creg2reg_idx rsd, AND)), s).
Proof. unfold execute. cbn match. unfold execute_C_AND. cbn zeta. apply exec_returnM. Qed.

(* WpGprRvc.v : exec_execute_C_ADDIW *)
Lemma exec_execute_C_ADDIW (imm : mword 6) (rsd : regidx) s :
  exec (execute (C_ADDIW (imm, rsd))) s
  = Some (ExecuteAs (ADDIW (sign_extend' 12 imm, rsd, rsd)), s).
Proof. unfold execute. cbn match. unfold execute_C_ADDIW. apply exec_returnM. Qed.

(* WpGprRvc.v : exec_execute_C_LDSP *)
Lemma exec_execute_C_LDSP (uimm : mword 6) (rd : regidx) s :
  exec (execute (C_LDSP (uimm, rd))) s
  = Some (ExecuteAs (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")), sp, rd, false, 8)), s).
Proof. unfold execute. cbn match. unfold execute_C_LDSP. cbn zeta. apply exec_returnM. Qed.

(* WpGprRvc.v : exec_execute_C_SDSP *)
Lemma exec_execute_C_SDSP (uimm : mword 6) (rs2 : regidx) s :
  exec (execute (C_SDSP (uimm, rs2))) s
  = Some (ExecuteAs (STORE (zero_extend' 12 (concat_vec uimm ('b"000")), rs2, sp, 8)), s).
Proof. unfold execute. cbn match. unfold execute_C_SDSP. cbn zeta. apply exec_returnM. Qed.

(* WpGprRvc.v : exec_execute_C_JR *)
Lemma exec_execute_C_JR (rs1 : regidx) s :
  exec (execute (C_JR rs1)) s = Some (ExecuteAs (JALR (zeros' 12, rs1, zreg)), s).
Proof. unfold execute. cbn match. unfold execute_C_JR. apply exec_returnM. Qed.

(* c.ld / c.sd : the register-relative width-8 compressed memory ops (the
   creg-indexed counterparts of C_LDSP/C_SDSP above). Shared exec facts --
   used by kalloc/kfree decode, swtch, wakeup, and the userret trampoline. *)
Lemma exec_execute_C_LD (uimm : mword 5) (rsc rdc : cregidx) s :
  exec (execute (C_LD (uimm, rsc, rdc))) s
  = Some (ExecuteAs (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")),
                           creg2reg_idx rsc, creg2reg_idx rdc, false, 8)), s).
Proof. unfold execute. cbn match. unfold execute_C_LD. cbn zeta. apply exec_returnM. Qed.

Lemma exec_execute_C_SD (uimm : mword 5) (rsc1 rsc2 : cregidx) s :
  exec (execute (C_SD (uimm, rsc1, rsc2))) s
  = Some (ExecuteAs (STORE (zero_extend' 12 (concat_vec uimm ('b"000")),
                            creg2reg_idx rsc2, creg2reg_idx rsc1, 8)), s).
Proof. unfold execute. cbn match. unfold execute_C_SD. cbn zeta. apply exec_returnM. Qed.

(* c.bnez : the compressed branch-if-nonzero expands to a base BTYPE/BNE
   against x0.  Shared exec fact -- used by holding(), pop_off()'s and
   acquire()'s compressed retry loops. *)
Lemma exec_execute_C_BNEZ (imm : mword 8) (rs : cregidx) s :
  exec (execute (C_BNEZ (imm, rs))) s
    = Some (ExecuteAs (BTYPE (sign_extend' 13 (concat_vec imm ('b"0")), zreg, creg2reg_idx rs, BNE)), s).
Proof. unfold execute. cbn match. unfold execute_C_BNEZ. apply exec_returnM. Qed.

(* c.beqz : the compressed branch-if-zero expands to a base BTYPE/BEQ
   against x0.  Shared exec fact -- companion to [exec_execute_C_BNEZ],
   used by spin loops that poll via a compressed branch. *)
Lemma exec_execute_C_BEQZ (imm : mword 8) (rs : cregidx) s :
  exec (execute (C_BEQZ (imm, rs))) s
  = Some (ExecuteAs (BTYPE (sign_extend' 13 (concat_vec imm ('b"0")), zreg, creg2reg_idx rs, BEQ)), s).
Proof. unfold execute. cbn match. unfold execute_C_BEQZ. apply exec_returnM. Qed.

(* ===================================================================== *)
(* Helper facts shared by chains that step compressed instructions via     *)
(* the (is_rvc-generalized) BASE-instruction WPs.                           *)
(* ===================================================================== *)
(* sign-extending imm6 to 12 bits then to 64 is the same as extending it to 64
   directly (nested sign extension collapses); lets chains state the write
   value of a compressed addi/addiw with a single [sign_extend' 64 imm6]. *)

(* WpGprRvc.v : sext6_12_64 *)
Lemma sext6_12_64 (x : mword 6) : sign_extend' 64 (sign_extend' 12 x) = sign_extend' 64 x.
Proof.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec to_word get_word
       MachineWord.MachineWord.sign_extend].
  apply bv_eq_signed.
  rewrite bv_sign_extend_signed; [| done].
  rewrite bv_sign_extend_signed; [| done].
  rewrite bv_sign_extend_signed; [| done].
  reflexivity.
Qed.

(* adding the zero register is a noop (used by c.li = addi rd,x0 and c.mv = add rd,x0). *)

(* WpGprRvc.v : add_vec_zero_l *)
Lemma add_vec_zero_l (x : mword 64) : add_vec zero_reg x = x.
Proof. apply bv_add_0_l. vm_compute. reflexivity. Qed.

(* the value a c.li rd, imm6 (= addi rd, x0, sext imm6) writes. *)

(* WpGprRvc.v : cli_wval *)
Definition cli_wval (imm6 : mword 6) : mword 64 :=
  sign_extend' 64 imm6.


(* the file's x0 entry is hardwired zero.  Chains stepping c.li / c.mv
   through the (is_rvc-generalized) base ADDI / ADD WPs read the x0 source
   OFF THE FILE (the base WPs' written value is phrased over [m !!! rs1]),
   so they need its value pinned; formerly the per-RVC WPs baked the zero in. *)

(* WpGprRvc.v : GprFileX0 *)
Section GprFileX0.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Lemma gpr_file_x0 (m : regfile) (i : mword 5) :
    uint i = 0 ->
    gpr_file m -∗ ⌜ m !!! Regidx i = zero_reg ⌝ ∗ gpr_file m.
  Proof.
    iIntros (Hi) "[%Hdom Hmap]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ (rf_to_gmap_lookup m (Regidx i)) with "Hmap")
      as "[Hpt Hcl]".
    iEval (unfold gpr_pt; rewrite Hi; simpl) in "Hpt".
    iDestruct "Hpt" as %Hz.
    iSplitR; [iPureIntro; exact Hz|].
    iSplitR; [iPureIntro; exact Hdom|].
    iApply "Hcl". iEval (unfold gpr_pt; rewrite Hi; simpl). iPureIntro. exact Hz.
  Qed.
End GprFileX0.

(* WpGprMretNew.v : mword1_not_lp *)
Lemma mword1_not_lp (x : mword 1) :
  eq_vec x (landing_pad_bits_backwards LP_EXPECTED) = false ->
  x = landing_pad_bits_backwards NO_LP_EXPECTED.
Proof.
  intro H.
  change (landing_pad_bits_backwards LP_EXPECTED) with ('b"1" : mword 1) in H.
  change (landing_pad_bits_backwards NO_LP_EXPECTED) with ('b"0" : mword 1).
  apply bv_eq.
  replace (bv_unsigned ('b"0" : mword 1)) with 0 by (vm_compute; reflexivity).
  pose proof (bv_unsigned_in_range _ x) as Hr.
  replace (bv_modulus (MachineWord.MachineWord.Z_idx 1)) with 2 in Hr
    by (vm_compute; reflexivity).
  destruct (decide (bv_unsigned x = 1)) as [He|Hne]; [| lia].
  exfalso.
  assert (Hx1 : x = ('b"1" : mword 1)).
  { apply bv_eq. rewrite He. vm_compute. reflexivity. }
  rewrite Hx1 in H. vm_compute in H. discriminate H.
Qed.

(* Same-value physical register write: if the register already holds [v], the
   ghost register bridge is preserved by [register_set r v] with NO ghost
   update -- the agreement map is untouched.  This absorbs MRET's elp write
   (elp is persistently pinned, so no full-ownership cell exists to update). *)

(* WpGprMretNew.v : reg_interp_set_same *)
Lemma reg_interp_set_same `{!riscvGS Σ} `{CpuId} (rs : regstate) (r : register)
    (v : type_of_register r) :
  register_lookup r rs = v ->
  reg_interp rs -∗ reg_interp (register_set r v rs).
Proof.
  iIntros (Hlk) "Hi". iDestruct "Hi" as (mp) "[Hm %Hag]".
  iExists mp. iFrame "Hm". iPureIntro.
  intros k dv Hk.
  destruct (decide (k = r)) as [->|Hne].
  - rewrite (Hag r dv Hk) register_lookup_set Hlk. reflexivity.
  - rewrite (Hag k dv Hk)
      (irrelevant_register_set k r rs v (register_beq_false k r Hne)).
    reflexivity.
Qed.

(* get_xLPE at Supervisor reads the menvcfg REGISTER; with menvcfg's value
   pinned by a points-to (and its LPE bit clear) the read reduces per-state.
   This replaces the old un-dischargeable [forall sz, exec (get_xLPE ..) ..]
   premise: the WP below derives the fact at the exact intermediate state the
   MRET reduction reads it (menvcfg is untouched by the preceding set_regs). *)

(* WpGprMretNew.v : exec_get_xLPE_S *)
Lemma exec_get_xLPE_S (sz : mstate) :
  _get_MEnvcfg_LPE (register_lookup menvcfg sz.(sregs)) = ('b"0") ->
  exec (get_xLPE Supervisor) sz = Some (false, sz).
Proof.
  intro HL.
  unfold get_xLPE. destruct (Defs.Zwf_guarded _).
  cbn [_rec_get_xLPE]. unfold Defs.assert_exp'.
  replace (Z.geb 2 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl sz)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg sz)).
  rewrite HL.
  replace (bool_bit_backwards ('b"0")) with false by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

(* ---- from WpGprRvcTor.v ---- *)
Lemma exec_pmpReadAddrReg (n : Z) s :
  exec (pmpReadAddrReg n) s
  = Some (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) n, s).
Proof.
  unfold pmpReadAddrReg. cbn zeta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpaddr_n s)). cbn beta.
  replace (Z.geb sys_pmp_grain 2) with false by (vm_compute; reflexivity).
  replace (Z.geb sys_pmp_grain 1) with false by (vm_compute; reflexivity).
  cbn [andb]. apply exec_returnM.
Qed.

(* pmpRangeMatch full-match arm: an access fully inside [b, e) matches. *)

Lemma pmpRangeMatch_full (b e a w : Z) :
  b <= a -> 0 < w -> a + w <= e ->
  pmpRangeMatch b e a w = PMP_Match.
Proof.
  intros Hb Hw He. unfold pmpRangeMatch.
  replace (Z.leb (Z.add a w) b) with false by (symmetry; apply Z.leb_gt; lia).
  replace (Z.leb e a) with false by (symmetry; apply Z.leb_gt; lia).
  cbn [orb].
  replace (Z.leb b a) with true by (symmetry; apply Z.leb_le; lia).
  replace (Z.leb (Z.add a w) e) with true by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.

(* PMP TOR entry 0 (base 0) grants an 8-byte RAM access, provided the entry's
   top bound [pmpaddr0 * 4] covers all of RAM.  This discharges the
   [pmpRangeMatch ... = PMP_Match] obligation of the S-mode load/store WPs
   from the owned points-to ([ram_base <= uint a], [uint a + 8 <= ram top]
   from owning all 8 bytes) plus the single "PMP covers RAM" config fact. *)


(* pmpMatchAddr, entry-0 TOR shape (prev = zeros): the access [a, a+w) fully
   inside [0, uint paddr * 4) is a (full) PMP_Match, with no state change. *)

Lemma exec_pmpMatchAddr_tor0_match (a : mword 64) (wbv : mword 64) (ent : mword 8)
    (paddr : mword 64) s :
  pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent) = TOR ->
  0 < uint wbv ->
  uint a + uint wbv <= uint paddr * 4 ->
  exec (pmpMatchAddr (Physaddr a) wbv ent paddr (zeros' 64)) s = Some (PMP_Match, s).
Proof.
  intros HA Hw Hin.
  pose proof (bv_unsigned_in_range _ a) as [Ha0 _].
  rewrite <- uint_unsigned in Ha0.
  assert (Hp0 : 0 < uint paddr) by lia.
  unfold pmpMatchAddr. cbn zeta. rewrite HA.
  assert (Hz0 : uint (zeros' 64 : mword 64) = 0) by (vm_compute; reflexivity).
  replace (zopz0zKzJ_u (zeros' 64) paddr) with false.
  2:{ symmetry. unfold zopz0zKzJ_u. rewrite Hz0. rewrite Z.geb_leb. apply Z.leb_gt. lia. }
  rewrite Hz0.
  rewrite (pmpRangeMatch_full (Z.mul 0 4) (Z.mul (uint paddr) 4) (uint a) (uint wbv)
             ltac:(lia) Hw ltac:(lia)).
  apply exec_returnM.
Qed.

(* The pure predicate: PMP entry 0 is TOR + unlocked and the [width]-byte
   access at [ea] lies FULLY inside its region [0, pmpaddr0*4).  (Nothing is
   assumed of entries 1..: in M-mode the full match on the unlocked entry 0
   early-returns "allow" before any later entry is consulted.) *)

Definition pmp_tor0_grants (cfg : type_of_register pmpcfg_n)
    (pmpaddrs : type_of_register pmpaddr_n) (ea : mword 64) (width : Z) : Prop :=
  pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec cfg 0)) = TOR
  /\ pmpLocked (vec_access_dec cfg 0) = false
  /\ 0 < width
  /\ uint ea + width <= uint (vec_access_dec pmpaddrs 0) * 4.

(* THE reduction: in Machine mode, [pmp_tor0_grants] of the CURRENT pmpcfg_n /
   pmpaddr_n register values makes pmpCheck grant the access -- the loop's
   FIRST iteration full-matches entry 0, which (M-mode, unlocked) early-returns
   [None] (allow). *)

Lemma exec_pmpCheck_machine_tor0
    (addr : mword 64) (width : Z) (access : MemoryAccessType mem_payload) s :
  pmp_tor0_grants (register_lookup pmpcfg_n s.(sregs))
                  (register_lookup pmpaddr_n s.(sregs)) addr width ->
  (forall ent, exists b, exec (pmpCheckRWX ent access) s = Some (b, s)) ->
  uint (to_bits 64 width : mword 64) = width ->
  exec (pmpCheck (Physaddr addr) width access Machine) s = Some (None, s).
Proof.
  intros (HA & HL & Hw & Hin) Hrwx Hwidth.
  unfold pmpCheck.
  rewrite exec_catch_early_return.
  replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity).
  cbn zeta.
  rewrite execR_bind0.
  match goal with
  | |- context[Defs.foreach_ZM_up ?F ?T ?S ?vars ?body] =>
      assert (Hbody0 : execR (body 0 tt) s
                       = Some (inl (None : option ExceptionType), s))
  end.
  { assert (HW1 : 0 < uint (to_bits 64 width : mword 64))
      by (rewrite Hwidth; exact Hw).
    assert (HW2 : uint addr + uint (to_bits 64 width : mword 64)
                  <= uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) * 4)
      by (rewrite Hwidth; exact Hin).
    cbn beta.
    change (Z.gtb 0 0) with false. cbn match.
    rewrite execR_bind. rewrite execR_returnR. cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_pmpReadAddrReg 0 s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_pmpMatchAddr_tor0_match addr (to_bits 64 width)
                  (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                  (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) s
                  HA HW1 HW2)).
    cbn beta. cbn match.
    rewrite execR_bind. unfold or_boolM. rewrite execR_bind. rewrite execR_liftR.
    destruct (Hrwx (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) as [b Hb].
    rewrite Hb. cbn match.
    destruct b; [reflexivity | rewrite HL; reflexivity]. }
  match goal with
  | |- context[Defs.foreach_ZM_up ?F ?T ?S ?vars ?body] =>
      assert (Hloop : execR (Defs.foreach_ZM_up F T S vars body) s
                      = Some (inl (None : option ExceptionType), s))
  end.
  { unfold Defs.foreach_ZM_up.
    assert (Hle : 0 <= sys_pmp_count - 1) by (unfold sys_pmp_count; lia).
    rewrite (Defs.unroll_foreach_ZM_up' _ _ 0 (sys_pmp_count - 1) 1 _ tt _ Hle).
    rewrite execR_bind. rewrite Hbody0. reflexivity. }
  rewrite Hloop. cbn match. reflexivity.
Qed.

(* ===================================================================== *)
(* 2a. STORE chain [_chk] clones (WpGprStore.v), with the per-entry        *)
(* all-OFF hypothesis replaced by the abstract pmpCheck fact.  Everything  *)
(* else (PMA / mmio gates / write_ram leaf / translation) is reused.       *)
(* ===================================================================== *)

Lemma exec_checked_mem_write_ram_store_chk (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 64) s :
  exec (pmpCheck (Physaddr addr) 8 (Store Data) Machine) s = Some (None, s) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 8) s = Some (false, s) ->
  dev_addr addr = false ->
  exec (checked_mem_write (Physaddr addr) 8 data (Store Data) pbmt Machine tt false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev)).
Proof.
  intros Hpmpchk Hmatch Halign Hwrite Hc Hsig Hh Hdev.
  unfold checked_mem_write.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ Hpmpchk).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_store addr pbmt region s Hmatch Halign Hwrite)).
      cbn match. apply exec_returnM. }
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_writable (Physaddr addr) 8) s = Some (false, s))).
  2:{ unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (write_kind_of_flags false false false) s = Some (rv64d_types.Write_plain, s))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_write_ram_plain_8 addr data s Hdev)).
  apply exec_returnM.
Qed.

Lemma exec_mem_write_value_8_chk (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 64) (m : mword 64) s :
  exec (pmpCheck (Physaddr addr) 8 (Store Data) Machine) s = Some (None, s) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 8) s = Some (false, s) ->
  dev_addr addr = false ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (mem_write_value (Physaddr addr) 8 data (Store Data) pbmt false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev)).
Proof.
  intros Hpmpchk Hmatch Halign Hwrite Hc Hsig Hh Hdev Hms Hmprv Hpriv.
  unfold mem_write_value, mem_write_value_meta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv. rewrite Hms.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_store m s Hmprv)).
  unfold mem_write_value_priv_meta. cbn [orb andb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_checked_mem_write_ram_store_chk pbmt addr region data s Hpmpchk Hmatch Halign Hwrite Hc Hsig Hh Hdev)).
  cbn match. unfold mem_write_callback. apply exec_returnm.
Qed.

Section SWchk.
Variable a : mword 64.
Variable data : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let pa := zero_extend' 64 (add_vec_int a (0 * 8)).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 8 = true.
Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmpchk : exec (pmpCheck (Physaddr pa) 8 (Store Data) Machine) s = Some (None, s).
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_vmem_write_addr_8_chk :
  exec (vmem_write_addr (Virtaddr a) 8 data (Store Data) false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) pa 8 data) s.(mdev)).
Proof.
  unfold vmem_write_addr.
  rewrite exec_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR (returnR (result bool ExecutionResult) tt >>
                          liftR (split_misaligned (Virtaddr a) 8)) s = Some (inr (1, 8), s)).
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
    rewrite execR_liftR. rewrite (exec_split_misaligned_aligned (Virtaddr a) s Halign). reflexivity. }
  rewrite (execR_bind_Some _ _ _ _ _ Hinner).
  rewrite misaligned_order_1.
  match goal with
  | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s
                 = Some (inr (true, 0%Z, true), MState s.(sregs) (write_bytes s.(mem) pa 8 data) s.(mdev)))
  end.
  { eapply execR_untilMT_1.
    - reflexivity.
    - (* body, vars = (false, 0, true) *)
      cbn match.
      assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
      rewrite (execR_liftR_seq _ _ _ _ _ Hass).
      rewrite (execR_liftR_seq _ _ _ _ _
        (exec_translateAddr_identity_store (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0*8)) s Hpriv Hmprv)).
      cbn [bits_of_virtaddr]. cbn match.
      (* SC dummy assert (Bool.eqb false (is_store_conditional (Store Data)) = true) *)
      assert (Hsc : exec (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51") s
                    = Some (tt, s)) by reflexivity.
      assert (Hscm : execR (Defs.liftR (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51")
                            : Defs.monadR (result bool ExecutionResult) exception unit) s = Some (inr tt, s))
        by (rewrite execR_liftR; rewrite Hsc; reflexivity).
      match goal with
      | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
          assert (Hwrloop : execR (Defs.bind0 (Defs.liftR asrt) Nbody) s
                           = Some (inr true, MState s.(sregs) (write_bytes s.(mem) pa 8 data) s.(mdev)))
      end.
      { match goal with
        | |- execR (Defs.bind0 _ ?Nbody) s = _ => set (NN := Nbody)
        end.
        rewrite (execR_bind0_Some _ _ _ _ Hscm).
        unfold NN; clear NN.
        match goal with
        | |- execR (match _ as x in bool return @?P x with | true => _ | false => ?B end) ?ss = ?R =>
            change (execR B ss = R)
        end.
        rewrite (execR_liftR_seq _ _ _ _ _ (exec_mem_write_ea (zero_extend' 64 (add_vec_int a (0*8))) s)).
        cbn match.
        match goal with
        | |- context [ mem_write_value ?pp 8 ?D (Store Data) ?pb false false false ] =>
            replace D with data
        end.
        2: { symmetry.
             change (8*(0+1)*8-1) with 63. change (8*0*8) with 0. change (8*8) with 64.
             change (63 - 0 + 1) with 64. rewrite autocast_id.
             unfold subrange_vec_dec. change (63 - 0 + 1) with 64. rewrite autocast_id.
             unfold to_word_idx, to_word, get_word, MachineWord.slice.
             rewrite MachineWord.cast_idx_refl.
             apply bv_eq. rewrite bv_extract_unsigned.
             change (Z.of_N (MachineWord.Z_idx 0)) with 0. rewrite Z.shiftr_0_r.
             apply bv_wrap_bv_unsigned. }
        rewrite (execR_liftR_seq _ _ _ _ _
          (exec_mem_write_value_8_chk PBMT_PMA (zero_extend' 64 (add_vec_int a (0*8))) region data
             (register_lookup mstatus s.(sregs)) s Hpmpchk Hmatch Hpalign Hwrite Hc Hsig Hh Hdev eq_refl Hmprv Hpriv)).
        cbn match.
        apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hwrloop).
      cbn.
      apply execR_returnR_fwd.
    - apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu).
  cbn. reflexivity.
Qed.
End SWchk.

Section VWgchk.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable data : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Hpmpchk : exec (pmpCheck (Physaddr pa) 8 (Store Data) Machine) s = Some (None, s).
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_vmem_write_8_gpr_chk :
  exec (vmem_write (Regidx rs1) offset 8 data (Store Data) false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) pa 8 data) s.(mdev)).
Proof.
  unfold vmem_write. rewrite exec_catch_early_return.
  assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Store Data) 8) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) 8 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_store ea s Hcp Hmprv Hpmm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
  rewrite execR_liftR.
  rewrite (exec_vmem_write_addr_8_chk a8 data region s Halign Hcp Hmprv Hpmpchk Hmatch Hpalign Hwrite Hc Hsig Hh Hdev).
  reflexivity.
Qed.
End VWgchk.

Section ExecStoreGchk.
Variable rs2 rs1 : mword 5.
Variable imm : mword 12.
Variable region : PMA_Region.
Variable s : mstate.
Let offset := sign_extend' 64 imm.
Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Hpmpchk : exec (pmpCheck (Physaddr pa) 8 (Store Data) Machine) s = Some (None, s).
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_execute_STORE_8_gpr_chk :
  exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s
    = Some (RETIRE_SUCCESS, MState s.(sregs) (write_bytes s.(mem) pa 8 vrs2) s.(mdev)).
Proof.
  change (execute (STORE (imm, Regidx rs2, Regidx rs1, 8)))
    with (execute_STORE imm (Regidx rs2) (Regidx rs1) 8).
  unfold execute_STORE.
  replace (8 <=? xlen_bytes) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:320.28-320.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
    (exec_vmem_write_8_gpr_chk rs1 offset _ region s Hcp Hmprv Hpmm Halign Hpmpchk Hmatch Hpalign Hwrite Hc Hsig Hh Hdev)).
  cbn match.
  rewrite (exec_returnM _ _).
  rewrite autocast_subrange_id.
  reflexivity.
Qed.
End ExecStoreGchk.

Lemma exec_checked_mem_read_ram_load_chk (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 64) s :
  exec (pmpCheck (Physaddr addr) 8 (Load Data) Machine) s = Some (None, s) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8
    = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 8) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 8)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (Load Data) pbmt Machine (Physaddr addr) 8 false false false false)
       s = Some (Ok (w, default_meta), s).
Proof.
  intros Hpmpchk Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes.
  unfold checked_mem_read.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ Hpmpchk).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_load addr pbmt region s Hmatch Halign Hread)).
      cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_readable (Physaddr addr) 8) s = Some (false, s))).
  2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (read_kind_of_flags _ _ _) s = Some (rv64d_types.Read_plain, s))).
  2:{ unfold read_kind_of_flags. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_plain_8 addr w s Hdev Hbytes)).
  apply exec_returnM.
Qed.

Lemma exec_mem_read_load_chk (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 64) (m : mword 64) s :
  exec (pmpCheck (Physaddr addr) 8 (Load Data) Machine) s = Some (None, s) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8
    = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 8) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 8)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (mem_read (Load Data) pbmt (Physaddr addr) 8 false false false)
       s = Some (Ok w, s).
Proof.
  intros Hpmpchk Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes Hms Hmprv Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite Hms.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_load m s Hmprv)).
  unfold mem_read_priv.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (mem_read_priv_meta _ _ _ _ 8 _ _ _ _) s = Some (Ok (w, default_meta), s))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (checked_mem_read _ _ _ _ 8 _ _ _ _) s = Some (Ok (w, default_meta), s))).
      2:{ cbn match. apply exec_checked_mem_read_ram_load_chk with (region := region); assumption. }
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

Section Schk.
Variable a : mword 64.
Variable v : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let pa := zero_extend' 64 (add_vec_int a (0 * 8)).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 8 = true.
Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmpchk : exec (pmpCheck (Physaddr pa) 8 (Load Data) Machine) s = Some (None, s).
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Let data2 : mword (8*1*8) :=
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.

Lemma exec_vmem_read_addr_8_chk :
  exec (vmem_read_addr (Virtaddr a) 8 (Load Data) false false false) s
    = Some (Ok data2, s).
Proof.
  unfold vmem_read_addr.
  rewrite exec_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR (returnR (result (mword (8 * 8)) ExecutionResult) tt >>
                          liftR (split_misaligned (Virtaddr a) 8)) s = Some (inr (1, 8), s)).
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
    rewrite execR_liftR. rewrite (exec_split_misaligned_aligned (Virtaddr a) s Halign). reflexivity. }
  rewrite (execR_bind_Some _ _ _ _ _ Hinner).
  rewrite misaligned_order_1.
  match goal with
  | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (data2, true, 0), s))
  end.
  { eapply execR_untilMT_1.
    - reflexivity.
    - cbn match.
      assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
      rewrite (execR_liftR_seq _ _ _ _ _ Hass).
      rewrite (execR_liftR_seq _ _ _ _ _
        (exec_translateAddr_identity_load (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0*8)) s Hpriv Hmprv)).
      cbn [bits_of_virtaddr]. cbn match.
      match goal with
      | |- execR (Defs.bind ?mrm ?post) s = _ =>
        assert (Hmrm : execR mrm s = Some (inr data2, s))
      end.
      { rewrite (execR_liftR_seq _ _ _ _ _
          (exec_mem_read_load_chk PBMT_PMA pa region v (register_lookup mstatus s.(sregs)) s
             Hpmpchk Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes eq_refl Hmprv Hpriv)).
        cbn match.
        rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite autocast_id. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hmrm).
      cbn. apply execR_returnR_fwd.
    - apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu).
  cbn. rewrite autocast_id. reflexivity.
Qed.
End Schk.

Section VRgchk.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable v : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Let data2 : mword (8*1*8) :=
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Hpmpchk : exec (pmpCheck (Physaddr pa) 8 (Load Data) Machine) s = Some (None, s).
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_vmem_read_8_gpr_chk :
  exec (vmem_read (Regidx rs1) offset 8 (Load Data) false false false) s = Some (Ok data2, s).
Proof.
  unfold vmem_read. rewrite exec_catch_early_return.
  assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Load Data) 8) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Load Data) 8 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_load ea s Hcp Hmprv Hpmm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
  rewrite execR_liftR.
  rewrite (exec_vmem_read_addr_8_chk a8 v region s Halign Hcp Hmprv Hpmpchk Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes).
  reflexivity.
Qed.
End VRgchk.

Section ExecLoadGchk.
Variable rs1 rd : mword 5.
Variable imm : mword 12.
Variable v : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let offset := sign_extend' 64 imm.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Let data2 : mword (8*1*8) :=
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.
Hypothesis Hrd : uint rd <> 0.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Hpmpchk : exec (pmpCheck (Physaddr pa) 8 (Load Data) Machine) s = Some (None, s).
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_execute_LOAD_8_gpr_chk :
  exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (extend_value false data2))).
Proof.
  change (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8)))
    with (execute_LOAD imm (Regidx rs1) (Regidx rd) false 8).
  unfold execute_LOAD.
  replace (8 <=? xlen_bytes) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _
    (exec_vmem_read_8_gpr_chk rs1 offset v region s Hcp Hmprv Hpmm Halign Hpmpchk Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes)).
  cbn match.
  assert (Hw : exec (wX_bits (Regidx rd) (extend_value false data2)) s
               = Some (tt, set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (extend_value false data2)))).
  { rewrite (exec_wX_bits_gpr rd (extend_value false data2) s).
    rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw).
  apply exec_returnM.
Qed.
End ExecLoadGchk.

(* ====================================================================== *)
(* rd=x0 (no-op) execute facts for the two-source register families.       *)
(* When rd = x0 the wX write is discarded, so the op retires state-         *)
(* preserving for every op.  The ITYPE/SHIFTIOP/UTYPE analogs live in       *)
(* WpUserClassify.v; RTYPE/RTYPEW/MUL are proved here (the shared base), so *)
(* the orchestrator can wire them into the rd=0 RVC HINT arm.               *)
(* ====================================================================== *)


