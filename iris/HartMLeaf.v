(* HartMLeaf.v -- THE LEAF: [WP Loop] from [WP Loop] through one real
   instruction, composed from the per-model-function [swp] facts.

   There is no new machinery here at all -- that is the point.  The file is
   [try_step]'s own spine, walked with [swp_bind_use] / [swp_use_cerN],
   with each call discharged by the fact that already exists for it, the
   register file threaded by [t_peel], and the leaf-local data (the word,
   the text bytes, the flag cell, the page-boundary and GPR equations)
   supplied as premises. *)
From Stdlib Require Import ZArith Zquot Lia.
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartRegNode
        HartSpan HartSpanChar HartEvents HartMCycle HartMDispatch HartMPmp
        HartMFetch HartMDecode HartMStore HartPilot.
Require Import RiscvTryStep RiscvExtras RiscvFetchExec.
Local Open Scope Z_scope.

Local Notation zerobit :=
  (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 1)
     (BinaryString.Raw.to_N "0" 0%N)).

Local Ltac l_glue :=
  cbn beta iota zeta delta
    [Defs.returnm returnM returnR Defs.returnR andb orb negb not
     Instances.generic_eq Instances.generic_neq].

Local Lemma hfrun_cE_Zca (D Drw : gset register) (rs : regstate) :
  (misa : register) ∈ D ->
  eq_vec (_get_Misa_C (register_lookup misa rs))
    (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
  hfrun 4 D Drw rs (currentlyEnabled Ext_Zca) = Some (true, rs).
Proof.
  intros HD HC. rewrite cE_Zca_eq. d_cbn.
  rewrite hfrun_read (bool_decide_eq_true_2 _ HD). d_cbn.
  rewrite HC. d_cbn. apply hfrun_ret.
Qed.

Section leaf.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [run_hart_active] at the pilot's word: dispatch, fetch, decode,
     execute.  Everything below the [swp_use_cer] peels is a fact that
     already exists. *)
  Lemma swp_run_hart_active_hp (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pmar0 : list PMA_Region)
      (pcfg : type_of_register pmpcfg_n)
      (pa : SailStdpp.Values.mword 64) (d : SailStdpp.Values.mword 64) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup (R_bitvector_64 PC) rs = hp_pc ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Misa_S (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup mstatus rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    eq_vec (_get_Misa_C (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    hfrun 8 (Drw ∪ Dro) Drw rs (is_landing_pad_expected tt)
      = Some (false, rs) ->
    (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
    pma_allows_ram pmar0 ->
    addr_is_ram hp_pc ->
    neq_vec (access_vec_dec hp_pc 0) zerobit = false ->
    neq_vec (access_vec_dec hp_pc 1) zerobit = false ->
    is_aligned_vaddr (Virtaddr hp_pc) 4 = true ->
    is_aligned_paddr (Physaddr hp_pc) 4 = true ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    addr_is_ram pa ->
    is_aligned_vaddr (Virtaddr pa) 4 = true ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    split_on_page_boundary (bits_of_virtaddr (Virtaddr pa)) 4
      = returnM (4, 0) ->
    hfrun 4 (Drw ∪ Dro) Drw
      (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2) rs)
      (rX_bits (creg2reg_idx
                  (encdec_creg_backwards (subrange_vec_dec hp_half 4 2))))
      = Some (d, register_set (R_bitvector_64 nextPC)
                    (add_vec_int hp_pc 2) rs) ->
    hfrun 8 (Drw ∪ Dro) Drw
      (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2) rs)
      (get_transformed_data_addr
         (creg2reg_idx (encdec_creg_backwards (subrange_vec_dec hp_half 9 7)))
         (sign_extend' 64
            (zero_extend' 12
               (concat_vec
                  (concat_vec
                     (concat_vec (subrange_vec_dec hp_half 5 5)
                        (subrange_vec_dec hp_half 12 10))
                     (subrange_vec_dec hp_half 6 6))
                  (MachineWord.MachineWord.N_to_word
                     (MachineWord.MachineWord.Z_idx 2)
                     (BinaryString.Raw.to_N "00" 0))))) (Store Data) 4)
      = Some (Ext_DataAddr_OK (Virtaddr pa),
              register_set (R_bitvector_64 nextPC)
                (add_vec_int hp_pc 2) rs) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) hp_pc 4 = Some hp_wf⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)) -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs)
                (write_bytes σ.(mem) pa 4
                   (Interface.WriteReq.value
                      (mwrite_req pa
                         (TypeCasts.autocast (subrange_vec_dec d 31 0)))))
                σ.(mdev)))) -∗
    swp (run_hart_active 0)
      (fun st => ⌜st = Step_Execute (RETIRE_SUCCESS,
                        zero_extend' 32 hp_half)⌝ ∗
                 hreg_frame (register_set (R_bitvector_64 nextPC)
                               (add_vec_int hp_pc 2) rs) Drw ∗
                 hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
                                     (add_vec_int hp_pc 2) rs) Dro).
  Proof.
    intros Hdisj HDpriv HDmisa HDmst HDpc HDnpc HDpma HDcfg HDhtif
      Hpriv Hpc Hpma Hpcfg Hhtif HmisaS HmIE HmisaC Hlpad Hunlock Hpallow
      Hram
      Hb0 Hb1 Hva Hpa Hmprv Hsram Hsva Hspa Hsplit Hrx Hgta.
    iIntros "#Hcert Hrw Hro Hmem Hwmem".
    unfold run_hart_active.
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (swp_use_cer (Defs.read_reg cur_privilege) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpriv.
    iApply (swp_use_cer (dispatchInterrupt Machine) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_dispatchInterrupt_M Drw Dro Df rs _ _ Hdisj HDmisa HDmst
                HmisaS HmIE eq_refl eq_refl with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mbind0_ret.
    iApply (swp_use_cer (fetch tt) _ _ C HC with "[Hrw Hro Hmem] [-]").
    { iApply (swp_fetch_ram Drw Dro Df rs hp_pc pmar0 pcfg hp_wf Hdisj HDpc
                HDmst HDpriv HDpma HDcfg HDhtif Hpc Hpriv Hpma Hpcfg
                Hhtif Hunlock Hpallow Hram Hb0 Hb1 Hva Hpa
                with "Hcert Hrw Hro Hmem"). }
    iIntros (v) "(-> & Hrw & Hro)".
    rewrite hp_isRVC. cbn beta iota.
    cbn beta iota zeta delta [ext_fetch_hook sail_instr_announce
      fetch_callback get_config_print_instr].
    iApply (swp_use_cer (ext_decode_compressed hp_half) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_decode_hp Drw Dro Df rs Hdisj HDmisa HmisaC
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". l_glue.
    rewrite mbind0_ret.
    iApply (swp_use_cer2 (is_landing_pad_expected tt) _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 8 Drw Dro Df rs rs _ _ Hdisj Hlpad
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". l_glue.
    rewrite mbind_ret. l_glue.
    iApply (swp_use_cer (currentlyEnabled Ext_Zca) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 4 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_cE_Zca (Drw ∪ Dro) Drw rs HDmisa HmisaC)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". l_glue.
    iApply (swp_use_cer (Defs.read_reg (R_bitvector_64 PC)) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpc
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpc.
    iApply (swp_use_cer2
              (Defs.write_reg (R_bitvector_64 nextPC)
                 (add_vec_int hp_pc 2)) _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_write_reg_owned Drw Dro Df rs _ _ Hdisj HDnpc
                with "Hcert Hrw Hro"). }
    iIntros (u) "[Hrw Hro]".
    iApply (swp_use_cer _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_execute_C_SW Drw Dro Df _ _ _ _ Hdisj
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". l_glue.
    cbn beta iota zeta delta [execute].
    iApply (swp_use_cer _ _ _ C HC with "[Hrw Hro Hwmem] [-]").
    { iApply (swp_execute_STORE Drw Dro Df
                (register_set (R_bitvector_64 nextPC)
                   (add_vec_int hp_pc 2) rs) _ _ _ d pa pmar0 pcfg Hdisj
                HDmst HDpriv HDpma HDcfg HDhtif
                ltac:(t_peel; exact Hpriv) ltac:(t_peel; exact Hpma)
                ltac:(t_peel; exact Hpcfg) ltac:(t_peel; exact Hhtif)
                ltac:(t_peel; exact Hmprv) Hunlock Hpallow Hsram Hsva Hspa
                Hsplit Hrx Hgta with "Hcert Hrw Hro Hwmem"). }
    iIntros (v) "(-> & Hrw & Hro)". l_glue.
    rewrite mcer_ret.
    iApply ("Hcont" $! (Step_Execute (RETIRE_SUCCESS,
                                      zero_extend' 32 hp_half))).
    by iFrame.
  Qed.

  (* the walk down to the dispatch: read cur_privilege, should_inc_minstret,
     write minstret_increment, read hart_state, then run_hart_active *)
  Lemma probe_prelude (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (R_bitvector_32 mcountinhibit : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 minstretcfg : register) ∈ Drw ∪ Dro ->
    (R_bool minstret_increment : register) ∈ Drw ->
    (hart_state : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    register_lookup hart_state rs = HART_ACTIVE tt ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (try_step 0 false) (fun _ => True%I).
  Proof.
    intros Hdisj HDpriv HDmc HDcfg HDmi HDhart Hpriv Hhart.
    iIntros "#Hcert Hrw Hro".
    unfold try_step. cbn beta iota zeta delta [ext_pre_step_hook].
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hpriv.
    iApply (swp_bind_use (should_inc_minstret Machine) _ _ _
              with "[Hrw Hro] [-]").
    { iApply (swp_should_inc_minstret Drw Dro Df rs Hdisj HDmc HDcfg
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use
                (Defs.write_reg (R_bool minstret_increment)
                   (minstret_inc_flag
                      (register_lookup (R_bitvector_32 mcountinhibit) rs)
                      (register_lookup (R_bitvector_64 minstretcfg) rs)))
                _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned Drw Dro Df rs _ _ Hdisj HDmi
                  with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iApply (swp_read_reg_pinned Drw Dro Df _ _ Hdisj HDhart
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    t_peel. rewrite Hhart.
    Show.
  Admitted.

End leaf.
