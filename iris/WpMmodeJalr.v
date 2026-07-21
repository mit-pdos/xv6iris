(* M-mode Jalr leaf lemmas (mmode_config, decode family).
   Relocated from WpGpr*.v; helpers in WpMmodeLeafBase. *)
Require Import WpMmodeLeafBase.
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d SailStdpp.Base RiscvLang RiscvPtsto RiscvExec RiscvFetchExec WpGpr RegFile InstrBytes RiscvExtras SailStdpp.TypeCasts SailStdpp.MachineWord SailStdpp.Values.
Import Defs.
Import Defs.

(* from WpGprJalr.v *)
Section WpJalrGpr.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* [instr]/[mmode_config]-formulated register-generic JALR WP, built on
     [wp_instr].  Like [wp_addi_gpr] it reads rs1 off the [gpr_file] and writes
     rd, but the write is the return address [pc+4] and the continuation's
     [pc_is] is the JUMP TARGET.  JALR's execute reads mseccfg.MLPE (for the
     Zicfilp check) and cur_privilege; these cells are held separately from
     [mmode_config] (which [wp_instr] takes) and handed back to the caller. *)
End WpJalrGpr.

(* from WpGprRvc.v *)
Section RvcRet.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Definition cret_target (vra : mword 64) : mword 64 :=
    update_vec_dec (add_vec vra (sign_extend' 64 (zeros' 12 : mword 12))) 0 ('b"0").


  (* [wp_cret_gpr] for a merely 2-aligned return target.  Under the C extension
     (misa.C, held by [mmode_config]'s [hw_config]) the model's jalr accepts a
     2-aligned target, so this needs only [is_aligned_paddr .. 2] where the
     4-aligned leaf needs [.. 4].  Needed after an odd-halfword layout shift
     flips a callee's return-address parity (e.g. start()'s ADUE write pushing
     the timerinit call to a 2-aligned return). *)
  Lemma wp_cret_gpr_zca (Φ : mval -> iProp Σ) (pc : mword 64) (ra : mword 5)
      (m : regfile) (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    uint ra <> 0 ->
    is_aligned_paddr (Physaddr (cret_target (m !!! Regidx ra))) 2 = true ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (JALR (zeros' 12, Regidx ra, zreg)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (cret_target (m !!! Regidx ra)) -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpmp Hra Halign) "Hmm Hpmpc [Hpc Hnpc] Hfmap Hinstr Hcont".
    pose proof (aligned2_jump_bit _ Halign) as Hal0.
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hmlpe & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iApply (wp_instr Φ pc true (JALR (zeros' 12, Regidx ra, zreg)) pmpcfg0
              Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmseccfg") as %Lsec.
    iDestruct (reg_valid_dq with "Hreg Hmisa")    as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (gpr_file_lookup_acc m (Regidx ra) with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value ra (m (Regidx ra)) s_pc with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    assert (Lrav : register_lookup (R_bitvector_64 (gpr_of_Z (uint ra))) s_pc.(sregs)
                   = m !!! Regidx ra).
    { rewrite rf_lookup -Hrv. replace (Z.eqb (uint ra) 0) with false
        by (symmetry; apply Z.eqb_neq; exact Hra). reflexivity. }
    assert (Hzic : exec (currentlyEnabled Ext_Zicfilp) s_pc = Some (false, s_pc)).
    { apply exec_cE_zicfilp_false.
      - unfold s_pc; tmig; exact Lpriv.
      - unfold s_pc; tmig; rewrite Lsec; exact Hmlpe. }
    assert (Hzca : exec (currentlyEnabled Ext_Zca) s_pc = Some (true, s_pc)).
    { apply exec_currentlyEnabled_Zca. unfold s_pc; tmig; rewrite Lmisa; exact HmisaC. }
    assert (Htgt : update_vec_dec (add_vec
                     (register_lookup (R_bitvector_64 (gpr_of_Z (uint ra))) s_pc.(sregs))
                     (sign_extend' 64 (zeros' 12 : mword 12))) 0 ('b"0")
                   = cret_target (m !!! Regidx ra)).
    { unfold cret_target. rewrite Lrav. reflexivity. }
    assert (Hexec_spc :
      exec (execute (JALR (zeros' 12, Regidx ra, zreg))) s_pc
      = Some (RETIRE_SUCCESS, set_reg s_pc nextPC (cret_target (m !!! Regidx ra)))).
    { change (execute (JALR (zeros' 12, Regidx ra, zreg)))
        with (execute_JALR (zeros' 12) (Regidx ra) zreg).
      change zreg with (Regidx cli_rs1).
      rewrite (exec_execute_JALR_ret_zca (zeros' 12) ra cli_rs1 s_pc Hra
                 ltac:(vm_compute; reflexivity) Hzic Hzca
                 ltac:(rewrite Htgt; exact Hal0)).
      rewrite Htgt. reflexivity. }
    iMod (reg_update _ nextPC _ (cret_target (m !!! Regidx ra)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (cret_target (m !!! Regidx ra))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hexec_spc. }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc nextPC (cret_target (m !!! Regidx ra))).(sregs)
             = cret_target (m !!! Regidx ra)).
    { rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hmst_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k Hmst_k". }
    iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] Hfmap").
  Qed.

End RvcRet.
