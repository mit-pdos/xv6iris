From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpEntry WpGpr WpLeafCommon.
Require Import MinstretInv InstrBytes WpEntryNew.
From iris.base_logic.lib Require Import invariants.
From Kernel Require KernelInstrs.
Local Open Scope Z_scope.

Section WpSpin.
  Context `{!riscvGS Σ}.

  (* The [spin] symbol at 0x8000001a (just past _entry's [jal start]): a single
     compressed self-jump [c.j spin] = [0xa001], the halt loop each hart runs
     forever once start() returns.  It decodes to [C_J imm_spin] whose 11-bit
     immediate is all-zero (jump offset 0), so it targets its own PC. *)
  Definition pc_spin : mword 64 := mword_of_int 0x8000001a.
  Definition h_spin : mword 16 := mword_of_int 0xa001.
  Definition imm_spin : mword 11 :=
    concat_vec (concat_vec (concat_vec (concat_vec (concat_vec (concat_vec
      (concat_vec (subrange_vec_dec h_spin 12 12) (subrange_vec_dec h_spin 8 8))
      (subrange_vec_dec h_spin 10 9)) (subrange_vec_dec h_spin 6 6))
      (subrange_vec_dec h_spin 7 7)) (subrange_vec_dec h_spin 2 2))
      (subrange_vec_dec h_spin 11 11)) (subrange_vec_dec h_spin 5 3).
  (* C_J expands (ExecuteAs) to [JAL (jimm_spin, x0)]; jimm_spin = 0. *)
  Definition jimm_spin : mword 21 := sign_extend' 21 (concat_vec imm_spin ('b"0")).

  (* ---- decode: the compressed self-jump decodes to [C_J imm_spin] ---- *)
  Lemma decode_C_J s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed h_spin) s = Some (C_J imm_spin, s).
  Proof.
    intro HmisaC. unfold imm_spin.
    unfold ext_decode_compressed, encdec_compressed_backwards. cbv beta. cbn zeta.
    skip_pure_clause.
    repeat (dstep s HmisaC).
    rewrite (exec_bind_Some _ _ _ _ _
      (exec_andM_true _ _ s (exec_currentlyEnabled_Zca s HmisaC)
         (exec_returnM_true _ s ltac:(vm_compute; reflexivity)))).
    cbv iota beta.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
    cbv iota beta. apply exec_returnM.
  Qed.

  (* ---- the two execute steps (C_J -> JAL x0 -> nextPC := PC) ---- *)
  Lemma exec_execute_C_J (imm : mword 11) s :
    exec (execute (C_J imm)) s
      = Some (ExecuteAs (JAL (sign_extend' 21 (concat_vec imm ('b"0")), zreg)), s).
  Proof. unfold execute. cbn match. unfold execute_C_J. apply exec_returnM. Qed.

  (* JAL to a 2-byte-aligned target with the C extension enabled: the
     misalignment check ([bit1] && not Zca) is false (port of
     WpKernelvecNew.kv_exec_jump_to_zca). *)
  Lemma sp_exec_jump_to_zca (target : mword 64) s :
    eq_vec (access_vec_dec target 0) ('b"0") = true ->
    exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
    exec (jump_to target) s = Some (RETIRE_SUCCESS, set_reg s nextPC target).
  Proof.
    intros Halign Hzca.
    unfold jump_to. rewrite exec_catch_early_return.
    change (ext_control_check_pc target) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ unfold Defs.bind0.
        erewrite execR_bind_Some.
        2:{ erewrite execR_bind_Some.
            2:{ apply execR_returnR_fwd. }
            rewrite execR_liftR. unfold assert_exp. rewrite Halign. cbn match.
            rewrite exec_returnm. reflexivity. }
        unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ (bit_to_bool (access_vec_dec target 1)) s).
        2:{ apply execR_returnR_fwd. }
        destruct (bit_to_bool (access_vec_dec target 1)).
        - cbv iota beta.
          rewrite (execR_bind_Some _ _ _ true s).
          2:{ rewrite execR_liftR. rewrite Hzca. reflexivity. }
          cbv iota beta. apply execR_returnR_fwd.
        - cbv iota beta. apply execR_returnR_fwd. }
    cbv iota beta.
    unfold Defs.bind0.
    rewrite (execR_bind_Some _ _ _ tt (set_reg s nextPC target)).
    2:{ rewrite execR_liftR. rewrite exec_set_next_pc. reflexivity. }
    rewrite (execR_returnR_fwd RETIRE_SUCCESS (set_reg s nextPC target)).
    reflexivity.
  Qed.

  (* JAL with rd = x0 (as C_J expands to): no link write, so the resulting
     state is just [nextPC := target]. *)
  Lemma exec_execute_JAL_zreg_zca (imm : mword 21) s :
    eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
    exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
    exec (execute_JAL imm zreg) s
      = Some (RETIRE_SUCCESS,
              set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
  Proof.
    intros Halign Hzca.
    unfold execute_JAL, get_next_pc.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg nextPC s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    rewrite (exec_bind_Some _ _ _ _ _ (sp_exec_jump_to_zca _ s Halign Hzca)).
    cbn match.
    unfold zreg.
    rewrite (exec_bind0_Some _ _ _ _ _
      (exec_wX_bits_gpr (zero_extend' 5 ('b"00")) (register_lookup nextPC s.(sregs))
         (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))))).
    apply exec_returnm.
  Qed.

  (* ---- the [instr] fact for the spin instruction, off the kernel text ---- *)
  Lemma spin_instr :
    kernel_text -∗ instr pc_spin true (C_J imm_spin).
  Proof.
    assert (Hlpad : is_lpad_instruction (C_J imm_spin) = false)
      by (vm_compute; reflexivity).
    assert (H2al : is_aligned_vaddr (Virtaddr pc_spin) 2 = true) by (vm_compute; reflexivity).
    assert (H4al : is_aligned_vaddr (Virtaddr pc_spin) 4 = false) by (vm_compute; reflexivity).
    assert (Hrvc : isRVC h_spin = true) by (vm_compute; reflexivity).
    assert (Hbytes : forall j, (j < 2)%nat ->
        KernelInstrs.kernel_bytes !! (0x8000001a + Z.of_nat j)%Z = Some (nth_byte h_spin j)).
    { intros j Hj;
        do 2 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia. }
    iIntros "#Ht". rewrite /instr.
    iSplitR; [iPureIntro; exact Hlpad|].
    iExists (F_RVC h_spin).
    iSplitR; [iPureIntro; reflexivity|].
    iSplitL "".
    - iApply (instr_bytes_rvc2 pc_spin h_spin H2al H4al Hrvc).
      iApply (kernel_window_pc 0x8000001a h_spin 2 pc_spin eq_refl Hbytes with "Ht").
    - iIntros (σ ns κs nt) "_". iPureIntro. intros _ HmisaC.
      exact (decode_C_J σ HmisaC).
  Qed.

  (* ================================================================= *)
  (*  THE THEOREM: the spin loop runs forever (proved by iLöb).        *)
  (*                                                                   *)
  (*  There is NO postcondition continuation: [spin] never leaves the  *)
  (*  self-jump, so the only way to discharge [WP Loop] is coinductive *)
  (*  -- a Löb-induction hypothesis [IH : ▷ (resources -∗ WP Loop)].   *)
  (*  We take ONE fetch/decode/execute step of [c.j spin] (which lands *)
  (*  back on [pc_spin] with every resource unchanged) and close the   *)
  (*  loop with [IH].  Built on [wp_exec_step_minstret] rather than the *)
  (*  [wp_instr] leaf layer, because only there is the step's [▷]       *)
  (*  exposed to the caller (the higher layers strip it internally,     *)
  (*  leaving no later to feed [IH]).                                   *)
  (* ================================================================= *)
  Lemma wp_spin E (Φ : mval -> iProp Σ) (m : gmap regidx (mword 64))
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc_spin -∗
    gpr_file m -∗
    kernel_text -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    assert (Hbit0 : eq_vec (access_vec_dec pc_spin 0) ('b"0") = true)
      by (vm_compute; reflexivity).
    assert (Htgt : add_vec pc_spin (sign_extend' 64 jimm_spin) = pc_spin)
      by (apply bv_eq; vm_compute; reflexivity).
    iIntros (HN Hpmp) "Hmm Hpmpc Hpc Hfile #Htext".
    (* pull the (persistent, constant) hardware config out once, so its facts
       survive the Löb induction. *)
    iDestruct "Hmm" as "(#Hhw & Hmmrest)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC & %HmisaU &
        %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    iAssert (mmode_config (DfracOwn q)) with "[Hmmrest]" as "Hmm".
    { rewrite /mmode_config. iFrame "Hhw". iExact "Hmmrest". }
    (* Löb: assume the loop already runs from any resource snapshot at pc_spin. *)
    iRevert "Hmm Hpmpc Hpc Hfile".
    iLöb as "IH".
    iIntros "Hmm Hpmpc Hpc Hfile".
    iDestruct "Hmm" as "(_ & #Hinv & Hhs & Hpriv & Hmst)".
    iDestruct "Hmst" as (mstatus0) "(Hmstatus & %HmIE & %HMPRV & %HSXL)".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    iPoseProof (spin_instr with "Htext") as "Hinstr".
    (* ---- take ONE real step, at the layer that exposes the step's later ---- *)
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) Φ HN with "Hinv").
    iIntros (σ ns κs nt) "Hsi Hbody".
    iDestruct "Hbody" as (mst mi_old) "[Hmst_c Hmi]".
    (* cur_privilege at σ (feeds should_inc_minstret) *)
    iDestruct (state_interp_reg_dq σ ns κs nt cur_privilege (DfracOwn q) Machine
                 with "Hsi Hpriv") as %Lpriv_σ.
    destruct (exec_should_inc_minstret_Some (register_lookup cur_privilege σ.(sregs)) σ)
      as [b Hsi_b].
    (* PRE: minstret_increment := b (borrowed from the invariant body) *)
    iDestruct "Hsi" as "[Hreg Hmem]".
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    set (s_a := set_reg σ (R_bool minstret_increment) b).
    iAssert (reg_interp s_a.(sregs) ∗ gen_heap_interp s_a.(mem))%I
      with "[Hreg Hmem]" as "Hsi".
    { unfold s_a, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    (* fetch/decode + dispatchInterrupt + register reads, all at s_a *)
    iDestruct (instr_lift s_a ns κs nt pc_spin true (C_J imm_spin) pmpcfg0 pmar0 misa0
                 Hpmp Hpma_all HmisaC
                 with "Hsi Hpc Hpriv Hpmpc Hpma Hhtif Hmisa Hinstr") as %Hlift.
    iDestruct (dispatchInterrupt_none_from_regs s_a ns κs nt misa0 mstatus0 HmisaS HmIE
                 with "Hsi Hmisa Hmstatus") as %Hdisp.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv_sa.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Lelp_sa.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa_sa.
    iDestruct (reg_valid_dq with "Hreg Hhs")   as %Lhs_sa.
    iDestruct (reg_valid    with "Hreg Hpc")   as %Lpc_sa.
    destruct Hlift as (h & Hfetch & Hdec & Hnlpad).
    (* the [run_hart_active] result via exec_hart_active_progress_RVC *)
    set (s_pc := set_reg s_a nextPC (add_vec_int pc_spin 2)).
    set (s_exec := set_reg s_pc nextPC pc_spin).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc_spin).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Lpc_sa | vm_compute; reflexivity]. }
    assert (HzcaC : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [rewrite Lmisa_sa; exact HmisaC | vm_compute; reflexivity]. }
    assert (Hzca_sa : exec (currentlyEnabled Ext_Zca) s_a = Some (true, s_a)).
    { apply exec_currentlyEnabled_Zca. rewrite Lmisa_sa. exact HmisaC. }
    assert (Halign_spc : eq_vec (access_vec_dec
              (add_vec (register_lookup PC s_pc.(sregs)) (sign_extend' 64 jimm_spin)) 0)
              ('b"0") = true).
    { rewrite Hpcv. rewrite Htgt. exact Hbit0. }
    assert (Hexec1 : exec (execute (C_J imm_spin)) s_pc
                       = Some (ExecuteAs (JAL (jimm_spin, zreg)), s_pc)).
    { apply exec_execute_C_J. }
    assert (Hexec2 : exec (execute (JAL (jimm_spin, zreg))) s_pc
                       = Some (RETIRE_SUCCESS, s_exec)).
    { change (execute (JAL (jimm_spin, zreg))) with (execute_JAL jimm_spin zreg).
      rewrite (exec_execute_JAL_zreg_zca jimm_spin s_pc Halign_spc
                 (exec_currentlyEnabled_Zca s_pc HzcaC)).
      unfold s_exec. rewrite Hpcv. rewrite Htgt. reflexivity. }
    assert (Hlpad_sa : eq_vec (register_lookup elp s_a.(sregs))
                              (landing_pad_bits_backwards LP_EXPECTED) = false).
    { rewrite Lelp_sa. exact Help_np. }
    assert (Hha : exec (run_hart_active 0) s_a
                  = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 h), s_exec)).
    { exact (exec_hart_active_progress_RVC s_a s_exec h (C_J imm_spin) (JAL (jimm_spin, zreg))
               pc_spin RETIRE_SUCCESS
               Lpriv_sa Hdisp Hfetch Hdec Hlpad_sa Lpc_sa Hzca_sa Hexec1 Hexec2). }
    (* hart_state / minstret_increment at s_exec (unchanged by the nextPC ticks) *)
    assert (Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt) by exact Lhs_sa.
    assert (Hhart_exec : register_lookup hart_state s_exec.(sregs) = HART_ACTIVE tt).
    { unfold s_exec, s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [| vm_compute; reflexivity].
      rewrite irrelevant_register_set; [exact Lhs_sa | vm_compute; reflexivity]. }
    assert (Hmi_exec : register_lookup (R_bool minstret_increment) s_exec.(sregs) = b).
    { unfold s_exec, s_pc, s_a, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [| vm_compute; reflexivity].
      rewrite irrelevant_register_set; [| vm_compute; reflexivity].
      rewrite register_lookup_set. reflexivity. }
    (* the whole [riscv_step] wrapper reduces to [s_final] *)
    assert (Lnpc_exec : register_lookup nextPC s_exec.(sregs) = pc_spin).
    { unfold s_exec, set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iModIntro.
    iExists (if b then set_reg (set_reg s_exec PC (register_lookup nextPC s_exec.(sregs)))
                         minstret (add_vec_int (register_lookup minstret
                           (set_reg s_exec PC (register_lookup nextPC s_exec.(sregs))).(sregs)) 1)
                  else set_reg s_exec PC (register_lookup nextPC s_exec.(sregs))).
    iSplitR.
    { iPureIntro.
      exact (exec_riscv_step_hart_active σ s_exec (zero_extend' 32 h) b
               Hsi_b Hhart_a Hha Hhart_exec Hmi_exec). }
    (* ---- the step's later: HERE [iNext] makes [IH] usable ---- *)
    iNext.
    (* POST: tick nextPC (pc+2 then pc_spin), tick PC := nextPC, bump minstret. *)
    iMod (reg_update _ nextPC _ (add_vec_int pc_spin 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ nextPC _ pc_spin with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ PC _ (register_lookup nextPC s_exec.(sregs)) with "Hreg Hpc")
      as "[Hreg Hpc]".
    iEval (rewrite Lnpc_exec) in "Hpc".
    destruct b.
    - iMod (reg_update _ minstret _
              (add_vec_int (register_lookup minstret
                 (set_reg s_exec PC (register_lookup nextPC s_exec.(sregs))).(sregs)) 1)
              with "Hreg Hmst_c") as "[Hreg Hmst_c]".
      iModIntro.
      iSplitL "Hreg Hmem".
      { unfold s_exec, s_pc, s_a, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
      iSplitL "Hmst_c Hmi".
      { iExists _, true. iFrame "Hmst_c Hmi". }
      iApply ("IH" with "[Hhs Hpriv Hmstatus] Hpmpc [$Hpc $Hnpc] Hfile").
      rewrite /mmode_config. iFrame "Hhw Hinv Hhs Hpriv".
      iExists mstatus0. iFrame "Hmstatus".
      iSplitR; [iPureIntro; exact HmIE|]. iSplitR; iPureIntro; [exact HMPRV | exact HSXL].
    - iModIntro.
      iSplitL "Hreg Hmem".
      { unfold s_exec, s_pc, s_a, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
      iSplitL "Hmst_c Hmi".
      { iExists mst, false. iFrame "Hmst_c Hmi". }
      iApply ("IH" with "[Hhs Hpriv Hmstatus] Hpmpc [$Hpc $Hnpc] Hfile").
      rewrite /mmode_config. iFrame "Hhw Hinv Hhs Hpriv".
      iExists mstatus0. iFrame "Hmstatus".
      iSplitR; [iPureIntro; exact HmIE|]. iSplitR; iPureIntro; [exact HMPRV | exact HSXL].
  Qed.

End WpSpin.
