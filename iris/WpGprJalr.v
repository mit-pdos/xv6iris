(* WpGprJalr.v -- the JALR family, stated on the new [instr] / [mmode_config]
   / [gpr_file] layer (cf. wp_addi_gpr), but CONTROL-FLOW: JALR reads rs1,
   writes rd := pc+4 (the return address / link) and JUMPS to
   [target = (rs1 + sign_extend imm)] with bit 0 cleared.  Built on [wp_instr].
   The continuation's [pc_is] is the jump TARGET, not pc+4.

   JALR's execute additionally consults [currentlyEnabled Ext_Zicfilp] (false in
   the boot config: mseccfg.MLPE = 0 at Machine privilege) and the model's
   [jump_to] checks the target's low-bit alignment; those are supplied as
   hypotheses (and the mseccfg / cur_privilege cells are owned separately from
   [mmode_config], which [wp_instr] consumes). *)
From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpGpr.
Require Import MinstretInv InstrBytes.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.

(* currentlyEnabled Ext_Zicfilp = the mseccfg MLPE bit; false in the boot config.
   Pinning the value. *)
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
Definition jbase (rs1 : mword 5) (s : mstate) : mword 64 :=
  if Z.eqb (uint rs1) 0 then zero_reg
  else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs).

(* Target of the JALR jump: (rs1 + sign_extend imm) with the low bit forced 0. *)
Definition jalr_target (vrs1 : mword 64) (imm : mword 12) : mword 64 :=
  update_vec_dec (add_vec vrs1 (sign_extend' 64 imm)) 0 ('b"0").

(* register-generic JALR execute: target = (rX rs1 + imm) with bit0 cleared;
   writes rd := link (nextPC), sets nextPC := target.  ANY rs1 (x0->zero_reg), rd<>0. *)
Lemma exec_execute_JALR_gpr (imm : mword 12) (rs1 rd : mword 5) s :
  uint rd <> 0 ->
  exec (currentlyEnabled Ext_Zicfilp) s = Some (false, s) ->
  eq_vec (access_vec_dec (jalr_target (jbase rs1 s) imm) 0) ('b"0") = true ->
  bit_to_bool (access_vec_dec (jalr_target (jbase rs1 s) imm) 1) = false ->
  exec (execute_JALR imm (Regidx rs1) (Regidx rd)) s
  = Some (RETIRE_SUCCESS,
          set_reg (set_reg s nextPC (jalr_target (jbase rs1 s) imm))
                  (R_bitvector_64 (gpr_of_Z (uint rd)))
                  (regval_into_reg (register_lookup nextPC s.(sregs)))).
Proof.
  intros Hrd Hzic Halign Hbit1. unfold jalr_target, jbase in *.
  unfold execute_JALR.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.bind0 (update_elp_state (Regidx rs1)) (get_next_pc tt)) s
                 = Some (register_lookup nextPC s.(sregs), s))).
  2:{ rewrite (exec_bind0_Some _ _ _ _ _
                (_ : exec (update_elp_state (Regidx rs1)) s = Some (tt, s))).
      2:{ unfold update_elp_state. rewrite (exec_bind_Some _ _ _ _ _ Hzic). cbn match. apply exec_returnm. }
      unfold get_next_pc. exact (exec_read_reg nextPC s). }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_jump_to _ s Halign Hbit1)).
  cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _
            (exec_wX_bits_gpr rd (register_lookup nextPC s.(sregs))
                (set_reg s nextPC (update_vec_dec (add_vec
                   (if Z.eqb (uint rs1) 0 then zero_reg
                    else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                   (sign_extend' 64 imm)) 0 ('b"0"))))).
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  apply exec_returnm.
Qed.

(* ret = jalr x0, 0(ra): rd = x0 (uint 0) => NO link write; just PC := target.
   Kept as an exec-level fact (representation-independent). *)
Lemma exec_execute_JALR_ret (imm : mword 12) (rs1 rdz : mword 5) s :
  uint rs1 <> 0 -> uint rdz = 0 ->
  exec (currentlyEnabled Ext_Zicfilp) s = Some (false, s) ->
  eq_vec (access_vec_dec (update_vec_dec (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (sign_extend' 64 imm)) 0 ('b"0")) 0) ('b"0") = true ->
  bit_to_bool (access_vec_dec (update_vec_dec (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (sign_extend' 64 imm)) 0 ('b"0")) 1) = false ->
  exec (execute_JALR imm (Regidx rs1) (Regidx rdz)) s
  = Some (RETIRE_SUCCESS,
          set_reg s nextPC (update_vec_dec (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (sign_extend' 64 imm)) 0 ('b"0"))).
Proof.
  intros Hrs1 Hrdz Hzic Halign Hbit1.
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
  rewrite (exec_bind_Some _ _ _ _ _ (exec_jump_to _ s Halign Hbit1)).
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
Section WpJalrGpr.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* [instr]/[mmode_config]-formulated register-generic JALR WP, built on
     [wp_instr].  Like [wp_addi_gpr] it reads rs1 off the [gpr_file] and writes
     rd, but the write is the return address [pc+4] and the continuation's
     [pc_is] is the JUMP TARGET.  JALR's execute reads mseccfg.MLPE (for the
     Zicfilp check) and cur_privilege; these cells are held separately from
     [mmode_config] (which [wp_instr] takes) and handed back to the caller. *)
  Lemma wp_jalr_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc : bool) (rs1 rd : mword 5)
      (imm : mword 12) (m : gmap regidx (mword 64))
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    is_aligned_paddr (Physaddr (jalr_target (m !!! Regidx rs1) imm)) 4 = true ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (JALR (imm, Regidx rs1, Regidx rd)) -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (jalr_target (m !!! Regidx rs1) imm) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec_int pc (if is_rvc then 2 else 4))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd Halign) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    destruct (aligned4_jump_bits _ Halign) as [Hal0 Hal1].
    (* keep half of mmode_config to reason about cur_privilege / mseccfg.MLPE for
       the Zicfilp check (both come from mmode_config / its hw_config). *)
    iDestruct (mmode_config_split_half with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hmlpe & %Help_np & %HmisaA)".
    (* wp_instr ties pmpcfg's fraction to mmode_config's, so split it too *)
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iApply (wp_instr E Φ pc is_rvc (JALR (imm, Regidx rs1, Regidx rd)) pmpcfg0
              HN Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    (* cur_privilege / mseccfg from the kept mmode_config half + hw_config *)
    iDestruct (reg_valid_dq with "Hreg Hpriv_k")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmseccfg") as %Lsec.
    iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (σ' := set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) σ' with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    (* jbase at σ' = m!!!rs1, so the model's target = jalr_target (m!!!) imm *)
    assert (Htgt : jalr_target (jbase rs1 σ') imm = jalr_target (m !!! Regidx rs1) imm).
    { unfold jbase. rewrite Hrv. reflexivity. }
    (* Zicfilp disabled at σ' (Machine + MLPE off, both lifted from σ) *)
    assert (Hzic : exec (currentlyEnabled Ext_Zicfilp) σ' = Some (false, σ')).
    { apply exec_cE_zicfilp_false.
      - subst σ'. unfold set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ].
      - subst σ'. unfold set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [ rewrite Lsec; exact Hmlpe | vm_compute; reflexivity ]. }
    assert (Hlink : register_lookup nextPC σ'.(sregs) = add_vec_int pc (if is_rvc then 2 else 4)).
    { subst σ'. unfold set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ nextPC _ (jalr_target (m !!! Regidx rs1) imm)
            with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec_int pc (if is_rvc then 2 else 4)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec_int pc (if is_rvc then 2 else 4)))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg σ' nextPC (jalr_target (m !!! Regidx rs1) imm))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (add_vec_int pc (if is_rvc then 2 else 4)))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (JALR (imm, Regidx rs1, Regidx rd)))
        with (execute_JALR imm (Regidx rs1) (Regidx rd)).
      fold σ'.
      rewrite (exec_execute_JALR_gpr imm rs1 rd σ' Hrd Hzic
                 ltac:(rewrite Htgt; exact Hal0) ltac:(rewrite Htgt; exact Hal1)).
      rewrite Htgt Hlink. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    (* continuation: PC and nextPC are both the jump TARGET. *)
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg σ' nextPC (jalr_target (m !!! Regidx rs1) imm))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (add_vec_int pc (if is_rvc then 2 else 4)))).(sregs)
             = jalr_target (m !!! Regidx rs1) imm).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    (* recombine mmode_config from the kept half + the half wp_instr returned *)
    iAssert (mmode_config (DfracOwn (1/2)))%I
      with "[Hhs_k Hpriv_k Hmst_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k Hmst_k". }
    iDestruct (mmode_config_combine_half with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.
End WpJalrGpr.

(* Demonstration: ONE lemma [wp_jalr_gpr] serves many (rs1,rd) pairs; and the
   exec-level [exec_execute_JALR_ret] covers the ret = jalr x0,0(ra) shape. *)
Section WpJalrGprDemo.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Definition wp_jalr_x1_x5 (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) (imm : mword 12) :=
    wp_jalr_gpr E Φ pc false (mword_of_int 1) (mword_of_int 5) imm.   (* jalr x5, imm(x1) *)
  Definition wp_jalr_x6_x28 (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) (imm : mword 12) :=
    wp_jalr_gpr E Φ pc false (mword_of_int 6) (mword_of_int 28) imm.  (* jalr x28, imm(x6) *)
  Goal gpr_of_Z (uint (mword_of_int 1 : mword 5)) = x1
    /\ gpr_of_Z (uint (mword_of_int 5 : mword 5)) = x5
    /\ gpr_of_Z (uint (mword_of_int 6 : mword 5)) = x6
    /\ gpr_of_Z (uint (mword_of_int 28 : mword 5)) = x28
    /\ uint (mword_of_int 1 : mword 5) <> 0
    /\ uint (mword_of_int 0 : mword 5) = 0.   (* x0 (ret dest) *)
  Proof. repeat split; vm_compute; first [ reflexivity | discriminate ]. Qed.
End WpJalrGprDemo.
