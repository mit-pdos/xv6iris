(* WpStartChain.v -- the threaded WP for the kernel's timerinit() function
   (21 instructions, kernel_instrs idx 9..29, addresses 0x8000001c..0x80000056,
   ending in c.ret).  Leaf file: imports WpStartText/KernelBoot, imported by
   nothing.  COMPILE: coqc -R . xv6iris -R /shared/xv6rocq/model-xv6iris Riscv
   -R /shared/xv6rocq/kernel-rocq Kernel WpStartChain.v *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpFetch WpDecode WpEntry WpGpr WpRvc WpAlu2 WpGprCsrrAny WpGprCsrw KernelBoot WpStartText.
Require Import WpAdd WpAuipc WpGprLui WpGprAddi WpGprLogic WpGprJal WpGprCsrr WpGprMretWp.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* Generic AUIPC WP (any rd, gpr_file).  Mirrors WpGprLui's LUI machinery  *)
(* but the written value is [add_vec pc (auipc_off imm)] (PC-relative).    *)
(* ====================================================================== *)

(* register-GENERIC AUIPC execute: writes rd := PC + (imm<<12). *)
Lemma exec_execute_UTYPE_AUIPC_gpr (rd : mword 5) (imm : mword 20) s :
  exec (execute_UTYPE imm (Regidx rd) AUIPC) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (add_vec (register_lookup PC s.(sregs)) (auipc_off imm)))).
Proof.
  unfold execute_UTYPE, auipc_off. cbn match.
  rewrite (exec_bind_Some _ _ _
             (add_vec (register_lookup PC s.(sregs))
                      (sign_extend' 64 (concat_vec imm (Ox"000")))) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_get_arch_pc s)). apply exec_returnm. }
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)). apply exec_returnm.
Qed.

Section ForwardAuipcGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rd : mword 5) (imm : mword 20).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrd0 : uint rd <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (UTYPE (imm, Regidx rd, AUIPC), s0).

  Definition sAg : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pcg' : mstate := set_reg sAg nextPC (add_vec_int pc 4).
  Definition sXg : mstate :=
    set_reg s_pcg' (R_bitvector_64 (gpr_of_Z (uint rd)))
      (regval_into_reg (add_vec (register_lookup PC s_pcg'.(sregs)) (auipc_off imm))).
  Definition sTg : mstate := set_reg sXg PC (register_lookup nextPC sXg.(sregs)).
  Definition sFg : mstate :=
    if b then set_reg sTg minstret (add_vec_int (register_lookup minstret sTg.(sregs)) 1)
         else sTg.

  Lemma forward_exec_auipc_gpr :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    register_lookup (R_bitvector_64 mideleg) s.(sregs) = zeros' 64 ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFg).
  Proof using All.
    intros Lpc Lpriv Lhs Lmideleg LmIE Lelp.
    assert (LpcA  : register_lookup PC sAg.(sregs) = pc).
    { unfold sAg, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sAg.(sregs) = Machine).
    { unfold sAg, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sAg.(sregs) = HART_ACTIVE tt).
    { unfold sAg, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LmidA : register_lookup (R_bitvector_64 mideleg) sAg.(sregs) = zeros' 64).
    { unfold sAg, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lmideleg | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) sAg.(sregs))) ('b"1") = false).
    { unfold sAg, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAg.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAg, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lelp | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAg = Some (None, sAg)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAg _ (exec_currentlyEnabled_S sAg) LmidA LmIEA). }
    assert (HfetchA : exec (fetch tt) sAg = Some (F_Base w, sAg)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sAg = Some (UTYPE (imm, Regidx rd, AUIPC), sAg)) by (apply Hdec; exact LprivA).
    assert (HexecG : exec (execute (UTYPE (imm, Regidx rd, AUIPC))) s_pcg' = Some (RETIRE_SUCCESS, sXg)).
    { change (execute (UTYPE (imm, Regidx rd, AUIPC))) with (execute_UTYPE imm (Regidx rd) AUIPC).
      rewrite (exec_execute_UTYPE_AUIPC_gpr rd imm s_pcg').
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd0).
      unfold sXg. reflexivity. }
    assert (Hha : exec (run_hart_active 0) sAg = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXg)).
    { exact (exec_hart_active_progress sAg sAg sXg sAg w
               (UTYPE (imm, Regidx rd, AUIPC)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecG I). }
    apply (exec_riscv_step_ADD s sXg w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXg, s_pcg', sAg; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXg, s_pcg', sAg; cbn zeta. trans_mi. trans_mi. rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardAuipcGpr.

Section CleanAuipcGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (rd : mword 5) (imm : mword 20) (mst0 : mword 64).
  Ltac reg_ne_g := solve [ vm_compute; reflexivity | (unfold gpr_of_Z; repeat case_match; reflexivity) ].
  Ltac tmig := rewrite irrelevant_register_set; [ | reg_ne_g ].
  Definition base_upd_g : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b)
                  nextPC (add_vec_int pc 4))
         (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (add_vec pc (auipc_off imm))))
      PC (add_vec_int pc 4).
  Definition sFcg' : mstate :=
    if b then set_reg base_upd_g minstret (add_vec_int mst0 1) else base_upd_g.

  Lemma sFg_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFg s pc b rd imm = sFcg'.
  Proof.
    intros LpcS LmstS.
    assert (HpcX : register_lookup PC (s_pcg' s pc b).(sregs) = pc).
    { unfold s_pcg', sAg, set_reg; cbn [sregs]. tmig. tmig. exact LpcS. }
    assert (Enpc : register_lookup nextPC (sXg s pc b rd imm).(sregs) = add_vec_int pc 4).
    { unfold sXg; cbv zeta. unfold set_reg; cbn [sregs]. tmig.
      unfold s_pcg', sAg, set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTg s pc b rd imm = base_upd_g).
    { unfold sTg. rewrite Enpc. unfold sXg; cbv zeta. rewrite HpcX.
      unfold base_upd_g, s_pcg', sAg. reflexivity. }
    unfold sFg, sFcg'. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_g.(sregs) = register_lookup minstret s.(sregs)).
    { unfold base_upd_g, set_reg; cbn [sregs]. do 4 tmig. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanAuipcGpr.

Section WpStartChain.
  Context `{!riscvGS Σ}.

  (* register-GENERIC AUIPC WP (any rd, gpr_file).  4-aligned 32-bit. *)
  Lemma wp_auipc_gpr (pc : mword 64) (w : mword 32) (rd : mword 5) (imm : mword 20)
      (m : gmap register_bitvector_64 (mword 64)) (vd : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E (Phi : mval -> iProp Σ) :
    uint rd <> 0 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (UTYPE (imm, Regidx rd, AUIPC), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (add_vec pc (auipc_off imm))]> m) -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrd Hmd Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "Hpc Hfile Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFcg' s pc b1 rd imm mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 rd imm mst0 Lpc Lmst).
      apply (forward_exec_auipc_gpr s pc b1 w rd imm Hfetch_at Hsi_s Hrd Hdec
               Lpc Lpriv Lhs Lmdl).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec pc (auipc_off imm))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec pc (auipc_off imm))) with "Hrdc") as "Hfile".
    unfold sFcg', base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.

  (* ---- per-instruction program counters (kentry + offset) ---- *)
  Definition tpc9  : mword 64 := mword_of_int (kentry + 0x1c). (* c.addi16sp sp,-16 *)
  Definition tpc10 : mword 64 := mword_of_int (kentry + 0x1e). (* c.sdsp ra,8(sp) *)
  Definition tpc11 : mword 64 := mword_of_int (kentry + 0x20). (* c.sdsp s0,0(sp) *)
  Definition tpc12 : mword 64 := mword_of_int (kentry + 0x22). (* c.addi4spn s0,sp,16 *)
  Definition tpc13 : mword 64 := mword_of_int (kentry + 0x24). (* csrr a5,menvcfg *)
  Definition tpc14 : mword 64 := mword_of_int (kentry + 0x28). (* c.li a4,-1 *)
  Definition tpc15 : mword 64 := mword_of_int (kentry + 0x2a). (* c.slli a4,a4,63 *)
  Definition tpc16 : mword 64 := mword_of_int (kentry + 0x2c). (* c.or a5,a5,a4 *)
  Definition tpc17 : mword 64 := mword_of_int (kentry + 0x2e). (* csrw menvcfg,a5 *)
  Definition tpc18 : mword 64 := mword_of_int (kentry + 0x32). (* csrr a5,mcounteren *)
  Definition tpc19 : mword 64 := mword_of_int (kentry + 0x36). (* ori a5,a5,2 *)
  Definition tpc20 : mword 64 := mword_of_int (kentry + 0x3a). (* csrw mcounteren,a5 *)
  Definition tpc21 : mword 64 := mword_of_int (kentry + 0x3e). (* csrr a5,time *)
  Definition tpc22 : mword 64 := mword_of_int (kentry + 0x42). (* lui a4,0xf4 *)
  Definition tpc23 : mword 64 := mword_of_int (kentry + 0x46). (* addi a4,a4,576 *)
  Definition tpc24 : mword 64 := mword_of_int (kentry + 0x4a). (* c.add a5,a5,a4 *)
  Definition tpc25 : mword 64 := mword_of_int (kentry + 0x4c). (* csrw stimecmp,a5 *)
  Definition tpc26 : mword 64 := mword_of_int (kentry + 0x50). (* c.ldsp ra,8(sp) *)
  Definition tpc27 : mword 64 := mword_of_int (kentry + 0x52). (* c.ldsp s0,0(sp) *)
  Definition tpc28 : mword 64 := mword_of_int (kentry + 0x54). (* c.addi16sp sp,16 *)
  Definition tpc29 : mword 64 := mword_of_int (kentry + 0x56). (* c.ret *)

  (* register indices as mword 5 *)
  Definition r_ra : mword 5 := mword_of_int 1.
  Definition r_sp : mword 5 := mword_of_int 2.
  Definition r_s0 : mword 5 := mword_of_int 8.
  Definition r_a4 : mword 5 := mword_of_int 14.
  Definition r_a5 : mword 5 := mword_of_int 15.
  Definition r_z  : mword 5 := mword_of_int 0.

  (* ===================================================================== *)
  (* Decode lemmas, one per timerinit instruction, built with the          *)
  (* skip_pure_clause / cstep framework (see WpEntry.decode_C_lui).         *)
  (* ===================================================================== *)

  (* idx 9: enc 0x1141.  NB: the Sail model decodes this as C_ADDI sp,sp,imm
     (objdump shows "addi16sp", but the model uses the plain C_ADDI clause). *)
  Definition w9 : mword 16 := mword_of_int 0x1141.
  Definition imm9 : mword 6 :=
    concat_vec (subrange_vec_dec w9 12 12) (subrange_vec_dec w9 6 2).
  Definition rd9 : mword 5 :=
    autocast (subrange_vec_dec (subrange_vec_dec w9 11 7) (regidx_bit_width - 1) 0).

  Lemma decode9 s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed w9) s = Some (C_ADDI (imm9, Regidx rd9), s).
  Proof.
    intro HmisaC. unfold imm9, rd9.
    assert (Hrsd : exec (encdec_reg_backwards (subrange_vec_dec w9 11 7)) s
                = Some (Regidx (autocast (T := mword)
                          (subrange_vec_dec (subrange_vec_dec w9 11 7)
                             (Z.sub regidx_bit_width 1) 0)), s)).
    { unfold encdec_reg_backwards.
      match goal with |- context[if ?g then returnM (Regidx _) else _] =>
        replace g with true by (vm_compute; reflexivity) end. cbn match. apply exec_returnM. }
    unfold ext_decode_compressed, encdec_compressed_backwards. cbv beta. cbn zeta.
    skip_pure_clause.
    repeat (dstep s HmisaC).
    match goal with |- context[if ?g then _ else returnM None] =>
      replace g with true by (vm_compute; reflexivity) end.
    cbn match. rewrite exec_bind.
    rewrite (exec_bind_Some _ _ _ _ _ Hrsd). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
    2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
        apply exec_currentlyEnabled_Zca; exact HmisaC. }
    cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
  Qed.

  (* helper: discharge encdec_reg_backwards (subrange w hi lo) -> Regidx ... *)
  Ltac reg_step name w hi lo s :=
    assert (name : exec (encdec_reg_backwards (subrange_vec_dec w hi lo)) s
                = Some (Regidx (autocast (T := mword)
                          (subrange_vec_dec (subrange_vec_dec w hi lo)
                             (Z.sub regidx_bit_width 1) 0)), s));
    [ unfold encdec_reg_backwards;
      match goal with |- context[if ?g then returnM (Regidx _) else _] =>
        replace g with true by (vm_compute; reflexivity) end; cbn match; apply exec_returnM
    | idtac ].

  Ltac open_rvc s HmisaC :=
    unfold ext_decode_compressed, encdec_compressed_backwards; cbv beta; cbn zeta;
    skip_pure_clause; repeat (dstep s HmisaC);
    match goal with |- context[if ?g then _ else returnM None] =>
      replace g with true by (vm_compute; reflexivity) end;
    cbn match; rewrite exec_bind.

  (* close a clause whose body, after peeling encdec_reg via Hr, is
     [and_boolM (returnM b) (currentlyEnabled Zca)] reducing to true. *)
  Ltac close_zca HmisaC :=
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) _ = Some (true, _)));
    [ cbn beta iota; rewrite exec_returnM; cbn beta iota; rewrite exec_returnM; reflexivity
    | apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |];
      apply exec_currentlyEnabled_Zca; exact HmisaC ].

  (* idx 10: c.sdsp ra,8(sp)  enc 0xe406 -> C_SDSP (uimm, rs2). *)
  Definition w10 : mword 16 := mword_of_int 0xe406.
  Definition uimm10 : mword 6 :=
    concat_vec (subrange_vec_dec w10 9 7) (subrange_vec_dec w10 12 10).
  Definition rs2_10 : mword 5 :=
    autocast (subrange_vec_dec (subrange_vec_dec w10 6 2) (regidx_bit_width - 1) 0).
  Lemma decode10 s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed w10) s = Some (C_SDSP (uimm10, Regidx rs2_10), s).
  Proof.
    intro HmisaC. unfold uimm10, rs2_10.
    reg_step Hr w10 6 2 s.
    open_rvc s HmisaC.
    rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
    2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
        apply exec_currentlyEnabled_Zca; exact HmisaC. }
    cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
  Qed.

  (* idx 11: c.sdsp s0,0(sp)  enc 0xe022 -> C_SDSP. *)
  Definition w11 : mword 16 := mword_of_int 0xe022.
  Definition uimm11 : mword 6 :=
    concat_vec (subrange_vec_dec w11 9 7) (subrange_vec_dec w11 12 10).
  Definition rs2_11 : mword 5 :=
    autocast (subrange_vec_dec (subrange_vec_dec w11 6 2) (regidx_bit_width - 1) 0).
  Lemma decode11 s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed w11) s = Some (C_SDSP (uimm11, Regidx rs2_11), s).
  Proof.
    intro HmisaC. unfold uimm11, rs2_11.
    reg_step Hr w11 6 2 s.
    open_rvc s HmisaC.
    rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
    2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
        apply exec_currentlyEnabled_Zca; exact HmisaC. }
    cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
  Qed.

  (* idx 12: c.addi4spn s0,sp,16  enc 0x0800 -> C_ADDI4SPN (crdc, nzimm). *)
  Definition w12 : mword 16 := mword_of_int 0x0800.
  Definition crdc12 : cregidx := Cregidx (subrange_vec_dec w12 4 2).
  Definition nzimm12 : mword 8 :=
    concat_vec (concat_vec (concat_vec (subrange_vec_dec w12 10 7) (subrange_vec_dec w12 12 11))
                           (subrange_vec_dec w12 5 5))
               (subrange_vec_dec w12 6 6).
  Lemma decode12 s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed w12) s = Some (C_ADDI4SPN (crdc12, nzimm12), s).
  Proof.
    intro HmisaC. unfold crdc12, nzimm12.
    open_rvc s HmisaC.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
    2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
        apply exec_currentlyEnabled_Zca; exact HmisaC. }
    cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
  Qed.

  (* idx 14: c.li a4,-1  enc 0x577d -> C_LI (imm6, rd). *)
  Definition w14 : mword 16 := mword_of_int 0x577d.
  Definition imm14 : mword 6 :=
    concat_vec (subrange_vec_dec w14 12 12) (subrange_vec_dec w14 6 2).
  Definition rd14 : mword 5 :=
    autocast (subrange_vec_dec (subrange_vec_dec w14 11 7) (regidx_bit_width - 1) 0).
  Lemma decode14 s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed w14) s = Some (C_LI (imm14, Regidx rd14), s).
  Proof.
    intro HmisaC. unfold imm14, rd14.
    reg_step Hr w14 11 7 s.
    open_rvc s HmisaC.
    rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (currentlyEnabled Ext_Zca) s = Some (true, s))).
    2:{ apply (exec_currentlyEnabled_Zca s HmisaC). }
    cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
  Qed.

  (* idx 15: c.slli a4,a4,63  enc 0x177e -> C_SLLI (shamt, rsd). *)
  Definition w15 : mword 16 := mword_of_int 0x177e.
  Definition shamt15 : mword 6 :=
    concat_vec (subrange_vec_dec w15 12 12) (subrange_vec_dec w15 6 2).
  Definition rsd15 : mword 5 :=
    autocast (subrange_vec_dec (subrange_vec_dec w15 11 7) (regidx_bit_width - 1) 0).
  Lemma decode15 s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed w15) s = Some (C_SLLI (shamt15, Regidx rsd15), s).
  Proof.
    intro HmisaC. unfold shamt15, rsd15.
    reg_step Hr w15 11 7 s.
    open_rvc s HmisaC.
    rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
    2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
        apply exec_currentlyEnabled_Zca; exact HmisaC. }
    cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
  Qed.

  (* idx 16: c.or a5,a5,a4  enc 0x8fd9 -> C_OR (crsd, crs2) (cregidx). *)
  Definition w16e : mword 16 := mword_of_int 0x8fd9.
  Definition crsd16 : cregidx := Cregidx (subrange_vec_dec w16e 9 7).
  Definition crs2_16 : cregidx := Cregidx (subrange_vec_dec w16e 4 2).
  Lemma decode16 s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed w16e) s = Some (C_OR (crsd16, crs2_16), s).
  Proof.
    intro HmisaC. unfold crsd16, crs2_16.
    open_rvc s HmisaC.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (currentlyEnabled Ext_Zca) s = Some (true, s))).
    2:{ apply (exec_currentlyEnabled_Zca s HmisaC). }
    cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
  Qed.

  (* idx 24: c.add a5,a5,a4  enc 0x97ba -> C_ADD (rsd, rs2). *)
  Definition w24 : mword 16 := mword_of_int 0x97ba.
  Definition rsd24 : mword 5 :=
    autocast (subrange_vec_dec (subrange_vec_dec w24 11 7) (regidx_bit_width - 1) 0).
  Definition rs2_24 : mword 5 :=
    autocast (subrange_vec_dec (subrange_vec_dec w24 6 2) (regidx_bit_width - 1) 0).
  Lemma decode24 s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed w24) s = Some (C_ADD (Regidx rsd24, Regidx rs2_24), s).
  Proof.
    intro HmisaC. unfold rsd24, rs2_24.
    reg_step Hr1 w24 11 7 s.
    reg_step Hr2 w24 6 2 s.
    open_rvc s HmisaC.
    rewrite (exec_bind_Some _ _ _ _ _ Hr1). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hr2). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
    2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
        apply exec_currentlyEnabled_Zca; exact HmisaC. }
    cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
  Qed.

  (* idx 26: c.ldsp ra,8(sp)  enc 0x60a2 -> C_LDSP (uimm, rd). *)
  Definition w26 : mword 16 := mword_of_int 0x60a2.
  Definition uimm26 : mword 6 :=
    concat_vec (concat_vec (subrange_vec_dec w26 4 2) (subrange_vec_dec w26 12 12))
               (subrange_vec_dec w26 6 5).
  Definition rd26 : mword 5 :=
    autocast (subrange_vec_dec (subrange_vec_dec w26 11 7) (regidx_bit_width - 1) 0).
  Lemma decode26 s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed w26) s = Some (C_LDSP (uimm26, Regidx rd26), s).
  Proof.
    intro HmisaC. unfold uimm26, rd26.
    reg_step Hr w26 11 7 s.
    open_rvc s HmisaC.
    rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.and_boolM (returnM _) (Defs.and_boolM (returnM _)
                            (currentlyEnabled Ext_Zca))) s = Some (true, s))).
    2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
        apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
        apply exec_currentlyEnabled_Zca; exact HmisaC. }
    cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
  Qed.

  (* idx 27: c.ldsp s0,0(sp)  enc 0x6402 -> C_LDSP. *)
  Definition w27 : mword 16 := mword_of_int 0x6402.
  Definition uimm27 : mword 6 :=
    concat_vec (concat_vec (subrange_vec_dec w27 4 2) (subrange_vec_dec w27 12 12))
               (subrange_vec_dec w27 6 5).
  Definition rd27 : mword 5 :=
    autocast (subrange_vec_dec (subrange_vec_dec w27 11 7) (regidx_bit_width - 1) 0).
  Lemma decode27 s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed w27) s = Some (C_LDSP (uimm27, Regidx rd27), s).
  Proof.
    intro HmisaC. unfold uimm27, rd27.
    reg_step Hr w27 11 7 s.
    open_rvc s HmisaC.
    rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.and_boolM (returnM _) (Defs.and_boolM (returnM _)
                            (currentlyEnabled Ext_Zca))) s = Some (true, s))).
    2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
        apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
        apply exec_currentlyEnabled_Zca; exact HmisaC. }
    cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
  Qed.

  (* idx 28: enc 0x0141 -> C_ADDI sp,sp,16 (plain C_ADDI, like idx 9). *)
  Definition w28 : mword 16 := mword_of_int 0x0141.
  Definition imm28 : mword 6 :=
    concat_vec (subrange_vec_dec w28 12 12) (subrange_vec_dec w28 6 2).
  Definition rd28 : mword 5 :=
    autocast (subrange_vec_dec (subrange_vec_dec w28 11 7) (regidx_bit_width - 1) 0).
  Lemma decode28 s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed w28) s = Some (C_ADDI (imm28, Regidx rd28), s).
  Proof.
    intro HmisaC. unfold imm28, rd28.
    reg_step Hr w28 11 7 s.
    open_rvc s HmisaC.
    rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
    2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
        apply exec_currentlyEnabled_Zca; exact HmisaC. }
    cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
  Qed.

  (* idx 29: c.ret  enc 0x8082 -> C_JR ra. *)
  Definition w29 : mword 16 := mword_of_int 0x8082.
  Definition ra29 : mword 5 :=
    autocast (subrange_vec_dec (subrange_vec_dec w29 11 7) (regidx_bit_width - 1) 0).
  Lemma decode29 s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed w29) s = Some (C_JR (Regidx ra29), s).
  Proof.
    intro HmisaC. unfold ra29.
    reg_step Hr w29 11 7 s.
    open_rvc s HmisaC.
    rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
    2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
        apply exec_currentlyEnabled_Zca; exact HmisaC. }
    cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
  Qed.

  (* ===================================================================== *)
  (* 32-bit decode lemmas (CSRReg / ITYPE / UTYPE), following              *)
  (* WpEntry.decode_csrr.  The CSR field is [subrange w 31 20], rs1/rd are  *)
  (* [encdec_reg_backwards (subrange w 19 15)/(subrange w 11 7)].           *)
  (* ===================================================================== *)

  (* common prefix: walk encdec_backwards past ZICBOP/NTL/EBREAK/pause/
     zicfilp/UTYPE(false)/JAL.. to reach the CSRReg clause (clause 92). *)
  Ltac csr_prefix w s Hpriv :=
    unfold ext_decode, encdec_backwards; cbv beta; cbn zeta;
    skip_pure_clause; skip_pure_clause;
    match goal with |- context[eq_vec w ?c] =>
      replace (eq_vec w c) with false by (vm_compute; reflexivity) end;
    match goal with |- context[eq_vec (subrange_vec_dec w 11 0) ?c] =>
      replace (eq_vec (subrange_vec_dec w 11 0) c) with false by (vm_compute; reflexivity) end;
    let HA1 := fresh "HA1" in
    assert (HA1 : exec (Defs.and_boolM (currentlyEnabled Ext_Zihintpause) (returnM false)) s = Some (false, s))
      by (destruct (exec_cE_pause s) as [bp Hbp]; rewrite (exec_and_boolM_Some _ _ _ _ _ Hbp); destruct bp; [apply exec_returnm | reflexivity]);
    rewrite (exec_bind_Some _ _ _ _ _ HA1); cbn match; rewrite exec_bind;
    let HA2 := fresh "HA2" in
    assert (HA2 : exec (Defs.and_boolM (currentlyEnabled Ext_Zicfilp) (returnM false)) s = Some (false, s))
      by (destruct (exec_cE_zicfilp_M s Hpriv) as [bz Hbz]; rewrite (exec_and_boolM_Some _ _ _ _ _ Hbz); destruct bz; [apply exec_returnm | reflexivity]);
    rewrite (exec_bind_Some _ _ _ _ _ HA2); cbn match;
    match goal with |- context[if ?g then _ else returnM None] =>
      replace g with false by (vm_compute; reflexivity) end;
    cbn match; rewrite (exec_returnM (@None instruction) s); cbn match;
    repeat skip_pure_clause.

  (* close a CSRReg clause: guard true, then peel encdec_reg(19 15),
     encdec_csrop(13 12)->op, encdec_reg(11 7), currentlyEnabled Zicsr. *)
  Ltac csr_body w s op_eq :=
    match goal with |- context[if ?g then _ else returnM None] =>
      replace g with true by (vm_compute; reflexivity) end;
    cbn match; rewrite exec_bind;
    let Hr1 := fresh "Hr1" in
    assert (Hr1 : exec (encdec_reg_backwards (subrange_vec_dec w 19 15)) s
        = Some (Regidx (autocast (subrange_vec_dec (subrange_vec_dec w 19 15) (regidx_bit_width - 1) 0)), s))
      by (unfold encdec_reg_backwards;
          match goal with |- context[if ?g then returnM (Regidx ?x) else _] =>
            replace g with true by (vm_compute; reflexivity) end; cbn match; apply exec_returnM);
    let Hco := fresh "Hco" in
    assert (Hco : exec (encdec_csrop_backwards (subrange_vec_dec w 13 12)) s = Some (op_eq, s))
      by (unfold encdec_csrop_backwards;
          first [ replace (eq_vec (subrange_vec_dec w 13 12) ('b"01")) with true by (vm_compute; reflexivity)
                | replace (eq_vec (subrange_vec_dec w 13 12) ('b"01")) with false by (vm_compute; reflexivity);
                  replace (eq_vec (subrange_vec_dec w 13 12) ('b"10")) with true by (vm_compute; reflexivity) ];
          cbn match; apply exec_returnM);
    let Hr2 := fresh "Hr2" in
    assert (Hr2 : exec (encdec_reg_backwards (subrange_vec_dec w 11 7)) s
        = Some (Regidx (autocast (subrange_vec_dec (subrange_vec_dec w 11 7) (regidx_bit_width - 1) 0)), s))
      by (unfold encdec_reg_backwards;
          match goal with |- context[if ?g then returnM (Regidx ?x) else _] =>
            replace g with true by (vm_compute; reflexivity) end; cbn match; apply exec_returnM);
    rewrite (exec_bind_Some _ _ _ _ _ Hr1);
    rewrite (exec_bind_Some _ _ _ _ _ Hco);
    rewrite (exec_bind_Some _ _ _ _ _ Hr2); cbn match;
    rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Zicsr s));
    rewrite (exec_returnM _ s); cbn match; apply exec_returnM.

  (* idx 13: csrr a5,menvcfg  enc 0x30a027f3 -> CSRReg (csr, rs1z, rd, CSRRS). *)
  Definition w13 : mword 32 := mword_of_int 0x30a027f3.
  Definition rs1z13 : mword 5 := autocast (subrange_vec_dec (subrange_vec_dec w13 19 15) (regidx_bit_width - 1) 0).
  Definition rd13   : mword 5 := autocast (subrange_vec_dec (subrange_vec_dec w13 11 7) (regidx_bit_width - 1) 0).
  Lemma decode13 s :
    register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode w13) s
      = Some (CSRReg (subrange_vec_dec w13 31 20, Regidx rs1z13, Regidx rd13, CSRRS), s).
  Proof. intro Hpriv. unfold rs1z13, rd13. csr_prefix w13 s Hpriv. csr_body w13 s CSRRS. Qed.

  (* idx 17: csrw menvcfg,a5  enc 0x30a79073 -> CSRReg (csr, rs1, zreg, CSRRW). *)
  Definition w17 : mword 32 := mword_of_int 0x30a79073.
  Definition rs1_17 : mword 5 := autocast (subrange_vec_dec (subrange_vec_dec w17 19 15) (regidx_bit_width - 1) 0).
  Lemma decode17 s :
    register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode w17) s
      = Some (CSRReg (subrange_vec_dec w17 31 20, Regidx rs1_17,
                       Regidx (autocast (subrange_vec_dec (subrange_vec_dec w17 11 7) (regidx_bit_width - 1) 0)), CSRRW), s).
  Proof. intro Hpriv. unfold rs1_17. csr_prefix w17 s Hpriv. csr_body w17 s CSRRW. Qed.

  (* idx 18: csrr a5,mcounteren  enc 0x306027f3 -> CSRRS. *)
  Definition w18 : mword 32 := mword_of_int 0x306027f3.
  Definition rs1z18 : mword 5 := autocast (subrange_vec_dec (subrange_vec_dec w18 19 15) (regidx_bit_width - 1) 0).
  Definition rd18   : mword 5 := autocast (subrange_vec_dec (subrange_vec_dec w18 11 7) (regidx_bit_width - 1) 0).
  Lemma decode18 s :
    register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode w18) s
      = Some (CSRReg (subrange_vec_dec w18 31 20, Regidx rs1z18, Regidx rd18, CSRRS), s).
  Proof. intro Hpriv. unfold rs1z18, rd18. csr_prefix w18 s Hpriv. csr_body w18 s CSRRS. Qed.

  (* idx 20: csrw mcounteren,a5  enc 0x30679073 -> CSRRW. *)
  Definition w20 : mword 32 := mword_of_int 0x30679073.
  Definition rs1_20 : mword 5 := autocast (subrange_vec_dec (subrange_vec_dec w20 19 15) (regidx_bit_width - 1) 0).
  Lemma decode20 s :
    register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode w20) s
      = Some (CSRReg (subrange_vec_dec w20 31 20, Regidx rs1_20,
                       Regidx (autocast (subrange_vec_dec (subrange_vec_dec w20 11 7) (regidx_bit_width - 1) 0)), CSRRW), s).
  Proof. intro Hpriv. unfold rs1_20. csr_prefix w20 s Hpriv. csr_body w20 s CSRRW. Qed.

  (* idx 21: csrr a5,time  enc 0xc01027f3 -> CSRRS. *)
  Definition w21 : mword 32 := mword_of_int 0xc01027f3.
  Definition rs1z21 : mword 5 := autocast (subrange_vec_dec (subrange_vec_dec w21 19 15) (regidx_bit_width - 1) 0).
  Definition rd21   : mword 5 := autocast (subrange_vec_dec (subrange_vec_dec w21 11 7) (regidx_bit_width - 1) 0).
  Lemma decode21 s :
    register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode w21) s
      = Some (CSRReg (subrange_vec_dec w21 31 20, Regidx rs1z21, Regidx rd21, CSRRS), s).
  Proof. intro Hpriv. unfold rs1z21, rd21. csr_prefix w21 s Hpriv. csr_body w21 s CSRRS. Qed.

  (* idx 25: csrw stimecmp,a5  enc 0x14d79073 -> CSRRW. *)
  Definition w25 : mword 32 := mword_of_int 0x14d79073.
  Definition rs1_25 : mword 5 := autocast (subrange_vec_dec (subrange_vec_dec w25 19 15) (regidx_bit_width - 1) 0).
  Lemma decode25 s :
    register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode w25) s
      = Some (CSRReg (subrange_vec_dec w25 31 20, Regidx rs1_25,
                       Regidx (autocast (subrange_vec_dec (subrange_vec_dec w25 11 7) (regidx_bit_width - 1) 0)), CSRRW), s).
  Proof. intro Hpriv. unfold rs1_25. csr_prefix w25 s Hpriv. csr_body w25 s CSRRW. Qed.

  (* close an ITYPE clause: guard true, peel encdec_reg(19 15), encdec_iop(14 12)->op,
     encdec_reg(11 7), then returnM. *)
  Ltac itype_body w s op_eq :=
    match goal with |- context[if ?g then _ else returnM None] =>
      replace g with true by (vm_compute; reflexivity) end;
    cbn match;
    let Hr1 := fresh "Hr1" in
    assert (Hr1 : exec (encdec_reg_backwards (subrange_vec_dec w 19 15)) s
        = Some (Regidx (autocast (subrange_vec_dec (subrange_vec_dec w 19 15) (regidx_bit_width - 1) 0)), s))
      by (unfold encdec_reg_backwards;
          match goal with |- context[if ?g then returnM (Regidx ?x) else _] =>
            replace g with true by (vm_compute; reflexivity) end; cbn match; apply exec_returnM);
    let Hio := fresh "Hio" in
    assert (Hio : exec (encdec_iop_backwards (subrange_vec_dec w 14 12)) s = Some (op_eq, s))
      by (unfold encdec_iop_backwards;
          repeat (match goal with |- context[if ?g then returnM _ else _] =>
            first [ replace g with true by (vm_compute; reflexivity)
                  | replace g with false by (vm_compute; reflexivity) ] end; cbn match);
          apply exec_returnM);
    let Hr2 := fresh "Hr2" in
    assert (Hr2 : exec (encdec_reg_backwards (subrange_vec_dec w 11 7)) s
        = Some (Regidx (autocast (subrange_vec_dec (subrange_vec_dec w 11 7) (regidx_bit_width - 1) 0)), s))
      by (unfold encdec_reg_backwards;
          match goal with |- context[if ?g then returnM (Regidx ?x) else _] =>
            replace g with true by (vm_compute; reflexivity) end; cbn match; apply exec_returnM);
    rewrite exec_bind;
    rewrite (exec_bind_Some _ _ _ _ _ Hr1);
    rewrite (exec_bind_Some _ _ _ _ _ Hio);
    rewrite (exec_bind_Some _ _ _ _ _ Hr2); cbn match; apply exec_returnM.

  (* idx 19: ori a5,a5,2  enc 0x0027e793 -> ITYPE (imm, rs1, rd, ORI). *)
  Definition w19 : mword 32 := mword_of_int 0x0027e793.
  Definition rs1_19 : mword 5 := autocast (subrange_vec_dec (subrange_vec_dec w19 19 15) (regidx_bit_width - 1) 0).
  Definition rd19   : mword 5 := autocast (subrange_vec_dec (subrange_vec_dec w19 11 7) (regidx_bit_width - 1) 0).
  Lemma decode19 s :
    register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode w19) s
      = Some (ITYPE (subrange_vec_dec w19 31 20, Regidx rs1_19, Regidx rd19, ORI), s).
  Proof. intro Hpriv. unfold rs1_19, rd19. csr_prefix w19 s Hpriv. itype_body w19 s ORI. Qed.

  (* idx 23: addi a4,a4,576  enc 0x24070713 -> ITYPE (imm, rs1, rd, ADDI). *)
  Definition w23 : mword 32 := mword_of_int 0x24070713.
  Definition rs1_23 : mword 5 := autocast (subrange_vec_dec (subrange_vec_dec w23 19 15) (regidx_bit_width - 1) 0).
  Definition rd23   : mword 5 := autocast (subrange_vec_dec (subrange_vec_dec w23 11 7) (regidx_bit_width - 1) 0).
  Lemma decode23 s :
    register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode w23) s
      = Some (ITYPE (subrange_vec_dec w23 31 20, Regidx rs1_23, Regidx rd23, ADDI), s).
  Proof. intro Hpriv. unfold rs1_23, rd23. csr_prefix w23 s Hpriv. itype_body w23 s ADDI. Qed.

  (* idx 22: lui a4,0xf4  enc 0x000f4737 -> UTYPE (imm, rd, LUI). *)
  Definition w22 : mword 32 := mword_of_int 0x000f4737.
  Definition rd22 : mword 5 := autocast (subrange_vec_dec (subrange_vec_dec w22 11 7) (regidx_bit_width - 1) 0).
  Lemma decode22 s :
    register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode w22) s
      = Some (UTYPE (subrange_vec_dec w22 31 12, Regidx rd22, LUI), s).
  Proof.
    intro Hpriv. unfold rd22.
    unfold ext_decode, encdec_backwards. cbv beta. cbn zeta.
    skip_pure_clause. skip_pure_clause.
    match goal with |- context[eq_vec w22 ?c] =>
      replace (eq_vec w22 c) with false by (vm_compute; reflexivity) end.
    match goal with |- context[eq_vec (subrange_vec_dec w22 11 0) ?c] =>
      replace (eq_vec (subrange_vec_dec w22 11 0) c) with false by (vm_compute; reflexivity) end.
    assert (HA1 : exec (Defs.and_boolM (currentlyEnabled Ext_Zihintpause) (returnM false)) s = Some (false, s))
      by (destruct (exec_cE_pause s) as [bp Hbp]; rewrite (exec_and_boolM_Some _ _ _ _ _ Hbp); destruct bp; [apply exec_returnm | reflexivity]).
    rewrite (exec_bind_Some _ _ _ _ _ HA1). cbn match. rewrite exec_bind.
    assert (HA2 : exec (Defs.and_boolM (currentlyEnabled Ext_Zicfilp) (returnM false)) s = Some (false, s))
      by (destruct (exec_cE_zicfilp_M s Hpriv) as [bz Hbz]; rewrite (exec_and_boolM_Some _ _ _ _ _ Hbz); destruct bz; [apply exec_returnm | reflexivity]).
    rewrite (exec_bind_Some _ _ _ _ _ HA2). cbn match.
    (* UTYPE clause: guard true *)
    match goal with |- context[if ?g then _ else returnM None] =>
      replace g with true by (vm_compute; reflexivity) end.
    cbn match.
    assert (Hrd : exec (encdec_reg_backwards (subrange_vec_dec w22 11 7)) s
        = Some (Regidx (autocast (subrange_vec_dec (subrange_vec_dec w22 11 7) (regidx_bit_width - 1) 0)), s))
      by (unfold encdec_reg_backwards;
          match goal with |- context[if ?g then returnM (Regidx ?x) else _] =>
            replace g with true by (vm_compute; reflexivity) end; cbn match; apply exec_returnM).
    rewrite exec_bind.
    rewrite (exec_bind_Some _ _ _ _ _ Hrd). cbn beta. apply exec_returnM.
  Qed.

  (* ===================================================================== *)
  (* Window regrouping for the 4-aligned RVC instructions (idx 9,11,14,16, *)
  (* 26,28): the 4-byte fetch reads the RVC instr's 2 bytes + the next     *)
  (* instr's first 2 bytes.  Mirror KernelBoot.lui_regroup exactly.        *)
  (* ===================================================================== *)
  Definition w4_9  : mword 32 := mword_of_int 0xe4061141.
  Definition w4_11 : mword 32 := mword_of_int 0x0800e022.
  Definition w4_14 : mword 32 := mword_of_int 0x177e577d.
  Definition w4_16 : mword 32 := mword_of_int 0x90738fd9.
  Definition w4_26 : mword 32 := mword_of_int 0x640260a2.
  Definition w4_28 : mword 32 := mword_of_int 0x80820141.

  (* generic 4-byte window at fetch_pa pc and the "remaining high 2 bytes" of
     the next instruction at fetch_pa npc. *)
  Definition twin4 (pc : mword 64) (w : mword 32) : iProp Σ :=
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w j)%I.
  Definition trem (npc : mword 64) (enc : Z) : iProp Σ :=
    ([∗ list] ab ∈ map (fun j => (pa_add (fetch_pa npc) j, nth_byte (mword_of_int enc : mword 32) j)) (seq 2 2),
       ab.1 ↦ₘ ab.2)%I.

  (* For idx 9,11,14,26,28 the next instruction is RVC (2 bytes) so the 4-byte
     window covers BOTH instructions exactly (no remainder). *)
  Lemma regroup9 :
    (kinstr_bytes (skinstr 9) ∗ kinstr_bytes (skinstr 10)) ⊣⊢ twin4 tpc9 w4_9.
  Proof.
    rewrite (kinstr_bytes_pairs (skinstr 9)) (kinstr_bytes_pairs (skinstr 10)).
    rewrite /twin4 (win_pairs tpc9 w4_9 4) -!big_sepL_app.
    replace (app (instr_byte_pairs (skinstr 9)) (instr_byte_pairs (skinstr 10)))
      with (map (fun j => (pa_add (fetch_pa tpc9) j, nth_byte w4_9 j)) (seq 0 4))
      by (vm_compute; repeat (f_equal; try (apply bv_eq; vm_compute; reflexivity))).
    reflexivity.
  Qed.

  Lemma regroup11 :
    (kinstr_bytes (skinstr 11) ∗ kinstr_bytes (skinstr 12)) ⊣⊢ twin4 tpc11 w4_11.
  Proof.
    rewrite (kinstr_bytes_pairs (skinstr 11)) (kinstr_bytes_pairs (skinstr 12)).
    rewrite /twin4 (win_pairs tpc11 w4_11 4) -!big_sepL_app.
    replace (app (instr_byte_pairs (skinstr 11)) (instr_byte_pairs (skinstr 12)))
      with (map (fun j => (pa_add (fetch_pa tpc11) j, nth_byte w4_11 j)) (seq 0 4))
      by (vm_compute; repeat (f_equal; try (apply bv_eq; vm_compute; reflexivity))).
    reflexivity.
  Qed.

  Lemma regroup14 :
    (kinstr_bytes (skinstr 14) ∗ kinstr_bytes (skinstr 15)) ⊣⊢ twin4 tpc14 w4_14.
  Proof.
    rewrite (kinstr_bytes_pairs (skinstr 14)) (kinstr_bytes_pairs (skinstr 15)).
    rewrite /twin4 (win_pairs tpc14 w4_14 4) -!big_sepL_app.
    replace (app (instr_byte_pairs (skinstr 14)) (instr_byte_pairs (skinstr 15)))
      with (map (fun j => (pa_add (fetch_pa tpc14) j, nth_byte w4_14 j)) (seq 0 4))
      by (vm_compute; repeat (f_equal; try (apply bv_eq; vm_compute; reflexivity))).
    reflexivity.
  Qed.

  (* idx 16's next (idx 17) is 32-bit, so 2 bytes remain. *)
  Lemma regroup16 :
    (kinstr_bytes (skinstr 16) ∗ kinstr_bytes (skinstr 17)) ⊣⊢ (twin4 tpc16 w4_16 ∗ trem tpc17 0x30a79073).
  Proof.
    rewrite (kinstr_bytes_pairs (skinstr 16)) (kinstr_bytes_pairs (skinstr 17)).
    rewrite /twin4 (win_pairs tpc16 w4_16 4) /trem -!big_sepL_app.
    replace (app (instr_byte_pairs (skinstr 16)) (instr_byte_pairs (skinstr 17)))
      with (app (map (fun j => (pa_add (fetch_pa tpc16) j, nth_byte w4_16 j)) (seq 0 4))
                (map (fun j => (pa_add (fetch_pa tpc17) j, nth_byte (mword_of_int 0x30a79073 : mword 32) j)) (seq 2 2)))
      by (vm_compute; repeat (f_equal; try (apply bv_eq; vm_compute; reflexivity))).
    reflexivity.
  Qed.

  Lemma regroup26 :
    (kinstr_bytes (skinstr 26) ∗ kinstr_bytes (skinstr 27)) ⊣⊢ twin4 tpc26 w4_26.
  Proof.
    rewrite (kinstr_bytes_pairs (skinstr 26)) (kinstr_bytes_pairs (skinstr 27)).
    rewrite /twin4 (win_pairs tpc26 w4_26 4) -!big_sepL_app.
    replace (app (instr_byte_pairs (skinstr 26)) (instr_byte_pairs (skinstr 27)))
      with (map (fun j => (pa_add (fetch_pa tpc26) j, nth_byte w4_26 j)) (seq 0 4))
      by (vm_compute; repeat (f_equal; try (apply bv_eq; vm_compute; reflexivity))).
    reflexivity.
  Qed.

  Lemma regroup28 :
    (kinstr_bytes (skinstr 28) ∗ kinstr_bytes (skinstr 29)) ⊣⊢ twin4 tpc28 w4_28.
  Proof.
    rewrite (kinstr_bytes_pairs (skinstr 28)) (kinstr_bytes_pairs (skinstr 29)).
    rewrite /twin4 (win_pairs tpc28 w4_28 4) -!big_sepL_app.
    replace (app (instr_byte_pairs (skinstr 28)) (instr_byte_pairs (skinstr 29)))
      with (map (fun j => (pa_add (fetch_pa tpc28) j, nth_byte w4_28 j)) (seq 0 4))
      by (vm_compute; repeat (f_equal; try (apply bv_eq; vm_compute; reflexivity))).
    reflexivity.
  Qed.

  (* decode lemmas for the combined 4-byte words: the decoder sees only the low
     16 bits (= the RVC instr), so reduce to the 2-byte decode lemmas. *)
  Lemma decode4_9 s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (subrange_vec_dec w4_9 15 0)) s = Some (C_ADDI (imm9, Regidx rd9), s).
  Proof. assert (Hw : subrange_vec_dec w4_9 15 0 = w9) by (apply bv_eq; vm_compute; reflexivity). rewrite Hw. apply decode9. Qed.
  Lemma decode4_11 s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (subrange_vec_dec w4_11 15 0)) s = Some (C_SDSP (uimm11, Regidx rs2_11), s).
  Proof. assert (Hw : subrange_vec_dec w4_11 15 0 = w11) by (apply bv_eq; vm_compute; reflexivity). rewrite Hw. apply decode11. Qed.
  Lemma decode4_14 s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (subrange_vec_dec w4_14 15 0)) s = Some (C_LI (imm14, Regidx rd14), s).
  Proof. assert (Hw : subrange_vec_dec w4_14 15 0 = w14) by (apply bv_eq; vm_compute; reflexivity). rewrite Hw. apply decode14. Qed.
  Lemma decode4_16 s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (subrange_vec_dec w4_16 15 0)) s = Some (C_OR (crsd16, crs2_16), s).
  Proof. assert (Hw : subrange_vec_dec w4_16 15 0 = w16e) by (apply bv_eq; vm_compute; reflexivity). rewrite Hw. apply decode16. Qed.
  Lemma decode4_26 s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (subrange_vec_dec w4_26 15 0)) s = Some (C_LDSP (uimm26, Regidx rd26), s).
  Proof. assert (Hw : subrange_vec_dec w4_26 15 0 = w26) by (apply bv_eq; vm_compute; reflexivity). rewrite Hw. apply decode26. Qed.
  Lemma decode4_28 s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (subrange_vec_dec w4_28 15 0)) s = Some (C_ADDI (imm28, Regidx rd28), s).
  Proof. assert (Hw : subrange_vec_dec w4_28 15 0 = w28) by (apply bv_eq; vm_compute; reflexivity). rewrite Hw. apply decode28. Qed.

  (* ===================================================================== *)
  (* wp_timerinit : the threaded WP for timerinit() (idx 9..29).            *)
  (* ===================================================================== *)

  Local Ltac vmc := vm_compute; reflexivity.

  (* gpr-file map lookup helper (cf. KernelBoot.gpr_map). *)
  Ltac gpr_ne := by first [ discriminate | assumption | (symmetry; assumption) ].
  Ltac gpr_map :=
    repeat first
      [ reflexivity
      | rewrite lookup_delete_ne; [| gpr_ne]
      | rewrite lookup_insert_ne; [| gpr_ne]
      | rewrite lookup_delete
      | rewrite lookup_insert ].

  (* reduce every [uint <field>] occurring in the goal to its concrete number
     (each at most once -> no quadratic retry), so the gpr-file insert keys
     become concrete [gpr_of_Z N]. *)
  Ltac red1 t n := try (change (uint t) with n).
  Ltac red_uints :=
    red1 rd9 2; red1 rd28 2; red1 csp_rs1 2; red1 ra29 1;
    red1 rd13 15; red1 rd18 15; red1 rd19 15; red1 rd21 15; red1 rsd24 15; red1 r_a5 15;
    red1 rd26 1; red1 rd27 8; red1 r_s0 8;
    red1 rd14 14; red1 rd22 14; red1 rd23 14; red1 rsd15 14.

  (* drive a gpr-file lookup over a concrete insert-chain to [Some _]. *)
  Ltac mlk :=
    red_uints;
    repeat first
      [ rewrite lookup_insert
      | rewrite lookup_insert_ne; [| discriminate] ].

  (* Bridge: the WP-returned window form (seq 0 (W/8), tpc, nth_byte wN:mword W)
     equals kinstr_bytes (skinstr N).  Same idea as E_skinstr but with the WP's
     own width-W word; the field equalities hold by vm_compute on concrete enc. *)
  Lemma EW (i : nat) (W n : nat) (addr enc : Z) (pc : mword 64) (wW : mword W) :
    KernelInstrs.ki_addr (skinstr i) = addr ->
    KernelInstrs.ki_enc (skinstr i) = enc ->
    KernelInstrs.ki_width (skinstr i) = W ->
    (W / 8)%nat = n ->
    pc = mword_of_int addr ->
    (forall j : nat, (j < n)%nat -> nth_byte wW j = nth_byte (mword_of_int enc : mword 32) j) ->
    ([∗ list] j ∈ seq 0 n, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte wW j)%I
      ⊣⊢ kinstr_bytes (skinstr i).
  Proof.
    intros Ha He Hw Hn Hpc Hnb.
    rewrite (E_skinstr i addr enc W Ha He Hw). rewrite Hn. subst pc.
    apply big_sepL_proper. intros k x Hk.
    apply lookup_seq in Hk. destruct Hk as [-> Hlt]. rewrite Hnb; [done | exact Hlt].
  Qed.

  (* ===================================================================== *)
  (* START()  decode lemmas (idx 30..63).  Shared encodings (0x1141, 0xe406,*)
  (* 0xe022, 0x0800, 0x577d-ish c.li, 0x8fd9) reuse the timerinit decodeNs. *)
  (* New RVC encodings get fresh decode lemmas; the 32-bit ones use the     *)
  (* csr_prefix/csr_body/itype_body framework.  NB corrections from probes: *)
  (* idx 30/48 -> C_ADDI (not addi16sp); idx 38 (0x6705) -> C_LUI (not LI). *)
  (* ===================================================================== *)

  (* --- new RVC encoding words --- *)
  Definition sw35 : mword 16 := mword_of_int 0x7779.  (* c.lui a4 *)
  Definition sw37 : mword 16 := mword_of_int 0x8ff9.  (* c.and *)
  Definition sw38 : mword 16 := mword_of_int 0x6705.  (* c.lui a4 *)
  Definition sw45 : mword 16 := mword_of_int 0x4781.  (* c.li a5 *)
  Definition sw47 : mword 16 := mword_of_int 0x67c1.  (* c.lui a5 *)
  Definition sw48 : mword 16 := mword_of_int 0x17fd.  (* C_ADDI a5 *)
  Definition sw54 : mword 16 := mword_of_int 0x57fd.  (* c.li a5 *)
  Definition sw55 : mword 16 := mword_of_int 0x83a9.  (* c.srli a5 *)
  Definition sw57 : mword 16 := mword_of_int 0x47bd.  (* c.li a5 *)
  Definition sw61 : mword 16 := mword_of_int 0x2781.  (* c.addiw a5 *)
  Definition sw62 : mword 16 := mword_of_int 0x823e.  (* c.mv tp,a5 *)

  (* field accessors (concrete encodings -> all guards vm_compute). *)
  Definition sclui_imm (w : mword 16) : mword 6 :=
    concat_vec (subrange_vec_dec w 12 12) (subrange_vec_dec w 6 2).
  Definition sreg117 (w : mword 16) : mword 5 :=
    autocast (subrange_vec_dec (subrange_vec_dec w 11 7) (regidx_bit_width - 1) 0).
  Definition sreg62 (w : mword 16) : mword 5 :=
    autocast (subrange_vec_dec (subrange_vec_dec w 6 2) (regidx_bit_width - 1) 0).
  Definition scli_imm (w : mword 16) : mword 6 :=
    concat_vec (subrange_vec_dec w 12 12) (subrange_vec_dec w 6 2).
  Definition scsrli_sh (w : mword 16) : mword 6 :=
    concat_vec (subrange_vec_dec w 12 12) (subrange_vec_dec w 6 2).
  Definition scaddiw_imm (w : mword 16) : mword 6 :=
    concat_vec (subrange_vec_dec w 12 12) (subrange_vec_dec w 6 2).

  (* C_LUI concrete decode: body = and_boolM(neq rd sp)(and_boolM(neq imm 0)(cE Zca)). *)
  Lemma decode_clui_c (w : mword 16) s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed w) s = Some (C_LUI (sclui_imm w, Regidx (sreg117 w)), s).
  Proof.
    intro HmisaC. unfold sclui_imm, sreg117.
    reg_step Hr w 11 7 s.
    open_rvc s HmisaC.
    rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.and_boolM (returnM _) (Defs.and_boolM (returnM _)
                            (currentlyEnabled Ext_Zca))) s = Some (true, s))).
    2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
        apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
        apply exec_currentlyEnabled_Zca; exact HmisaC. }
    cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
  Qed.

  Lemma decode_s35 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed sw35) s = Some (C_LUI (sclui_imm sw35, Regidx (sreg117 sw35)), s).
  Proof. apply decode_clui_c. Qed.
  Lemma decode_s38 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed sw38) s = Some (C_LUI (sclui_imm sw38, Regidx (sreg117 sw38)), s).
  Proof. apply decode_clui_c. Qed.
  Lemma decode_s47 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed sw47) s = Some (C_LUI (sclui_imm sw47, Regidx (sreg117 sw47)), s).
  Proof. apply decode_clui_c. Qed.

  (* C_LI concrete: body = currentlyEnabled Zca (after encdec_reg). *)
  Lemma decode_cli_c (w : mword 16) s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed w) s = Some (C_LI (scli_imm w, Regidx (sreg117 w)), s).
  Proof.
    intro HmisaC. unfold scli_imm, sreg117.
    reg_step Hr w 11 7 s.
    open_rvc s HmisaC.
    rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (currentlyEnabled Ext_Zca) s = Some (true, s))).
    2:{ apply (exec_currentlyEnabled_Zca s HmisaC). }
    cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
  Qed.
  Lemma decode_s45 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed sw45) s = Some (C_LI (scli_imm sw45, Regidx (sreg117 sw45)), s).
  Proof. apply decode_cli_c. Qed.
  Lemma decode_s54 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed sw54) s = Some (C_LI (scli_imm sw54, Regidx (sreg117 sw54)), s).
  Proof. apply decode_cli_c. Qed.
  Lemma decode_s57 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed sw57) s = Some (C_LI (scli_imm sw57, Regidx (sreg117 sw57)), s).
  Proof. apply decode_cli_c. Qed.

  (* C_ADDI concrete (idx 48, 0x17fd): like decode9. *)
  Lemma decode_s48 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed sw48) s = Some (C_ADDI (scli_imm sw48, Regidx (sreg117 sw48)), s).
  Proof.
    intro HmisaC. unfold scli_imm, sreg117.
    reg_step Hr sw48 11 7 s.
    open_rvc s HmisaC.
    rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
    2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
        apply exec_currentlyEnabled_Zca; exact HmisaC. }
    cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
  Qed.

  (* C_AND (idx 37, 0x8ff9): cregidx fields, body = currentlyEnabled Zca. *)
  Definition scand_rsd : cregidx := Cregidx (subrange_vec_dec sw37 9 7).
  Definition scand_rs2 : cregidx := Cregidx (subrange_vec_dec sw37 4 2).
  Lemma decode_s37 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed sw37) s = Some (C_AND (scand_rsd, scand_rs2), s).
  Proof.
    intro HmisaC. unfold scand_rsd, scand_rs2.
    open_rvc s HmisaC.
    rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (currentlyEnabled Ext_Zca) s = Some (true, s))).
    2:{ apply (exec_currentlyEnabled_Zca s HmisaC). }
    cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
  Qed.

  (* C_SRLI (idx 55, 0x83a9): shamt + cregidx crsd, body = and_boolM(xlen-guard)(cE Zca). *)
  Definition scsrli_crsd : cregidx := Cregidx (subrange_vec_dec sw55 9 7).
  Lemma decode_s55 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed sw55) s = Some (C_SRLI (scsrli_sh sw55, scsrli_crsd), s).
  Proof.
    intro HmisaC. unfold scsrli_sh, scsrli_crsd.
    open_rvc s HmisaC.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
    2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
        apply exec_currentlyEnabled_Zca; exact HmisaC. }
    cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
  Qed.

  (* C_MV (idx 62, 0x823e): rd=encdec_reg(11:7), rs2=encdec_reg(6:2), body = and_boolM(neq rs2 0)(cE Zca). *)
  Lemma decode_s62 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed sw62) s = Some (C_MV (Regidx (sreg117 sw62), Regidx (sreg62 sw62)), s).
  Proof.
    intro HmisaC. unfold sreg117, sreg62.
    reg_step Hr1 sw62 11 7 s.
    reg_step Hr2 sw62 6 2 s.
    open_rvc s HmisaC.
    rewrite (exec_bind_Some _ _ _ _ _ Hr1). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hr2). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
    2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
        apply exec_currentlyEnabled_Zca; exact HmisaC. }
    cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
  Qed.

  (* C_ADDIW (idx 61, 0x2781): rsd=encdec_reg(11:7), imm6.  Must skip the C_JAL
     clause (guard and_boolM(returnM(xlen=?32))(cE Zca) -> false), then C_ADDIW
     body = and_boolM(returnM(xlen=?64))(cE Zca). *)
  Lemma decode_s61 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed sw61) s = Some (C_ADDIW (scaddiw_imm sw61, Regidx (sreg117 sw61)), s).
  Proof.
    intro HmisaC. unfold scaddiw_imm, sreg117.
    reg_step Hr sw61 11 7 s.
    open_rvc s HmisaC.
    rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
    2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
        apply exec_currentlyEnabled_Zca; exact HmisaC. }
    cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
  Qed.

  (* per-chunk instruction-window bundles (kernel text is never modified). *)
  Definition Kc1 : iProp Σ :=
    (kinstr_bytes (skinstr 9) ∗ kinstr_bytes (skinstr 10) ∗ kinstr_bytes (skinstr 11) ∗
     kinstr_bytes (skinstr 12) ∗ kinstr_bytes (skinstr 13))%I.
  Definition Kc2 : iProp Σ :=
    (kinstr_bytes (skinstr 14) ∗ kinstr_bytes (skinstr 15) ∗ kinstr_bytes (skinstr 16) ∗
     kinstr_bytes (skinstr 17) ∗ kinstr_bytes (skinstr 18))%I.
  Definition Kc3 : iProp Σ :=
    (kinstr_bytes (skinstr 19) ∗ kinstr_bytes (skinstr 20) ∗ kinstr_bytes (skinstr 21) ∗
     kinstr_bytes (skinstr 22) ∗ kinstr_bytes (skinstr 23))%I.
  Definition Kc4 : iProp Σ :=
    (kinstr_bytes (skinstr 24) ∗ kinstr_bytes (skinstr 25) ∗ kinstr_bytes (skinstr 26) ∗
     kinstr_bytes (skinstr 27) ∗ kinstr_bytes (skinstr 28) ∗ kinstr_bytes (skinstr 29))%I.

  (* The resources whose VALUES are invariant across all of timerinit. *)
  Definition ti_ctx (misa0 mstatus0 mseccfg0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) : iProp Σ :=
    (misa ↦ᵣ misa0 ∗ cur_privilege ↦ᵣ Machine ∗ hart_state ↦ᵣ HART_ACTIVE tt ∗
     (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 ∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 ∗
     elp ↦ᵣ elp0 ∗ mseccfg ↦ᵣ mseccfg0 ∗ mcountinhibit ↦ᵣ mc ∗ minstretcfg ↦ᵣ mcfg ∗
     pmpcfg_n ↦ᵣ pmpcfg0 ∗ pma_regions ↦ᵣ pmar0 ∗ htif_tohost_base ↦ᵣ None)%I.

  (* ===================================================================== *)
  (* CHUNK c1 : idx 9-13.  C_ADDI sp,-16 ; c.sdsp ra ; c.sdsp s0 ;          *)
  (* c.addi4spn s0 ; csrr a5,menvcfg.  Updates sp,s0,a5; stores ra,s0.      *)
  (* ===================================================================== *)
  Lemma wp_ti_c1
      (sp0 vra vs0 va5 : mword 64)
      (m : gmap register_bitvector_64 (mword 64))
      (mst0 npc0 : mword 64) (mi0 : bool)
      (misa0 mstatus0 mseccfg0 menvcfg0 mtime0 stimecmp0 : mword 64)
      (mcounteren0 : mword 32)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) (vold_ra vold_s0 : bv 64)
      E (Φ : mval -> iProp Σ) :
    let b1   := andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                     (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) in
    let bump := fun (x : mword 64) => if b1 then add_vec_int x 1 else x in
    let sp1  := add_vec sp0 (sign_extend' 64 (sign_extend' 12 imm9)) in
    let imm_ra := zero_extend' 12 (concat_vec uimm10 ('b"000")) in
    let pa_ra  := zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_ra)) (xlen - 0 - 1) 0)) (0 * 8)) in
    let imm_s0 := zero_extend' 12 (concat_vec uimm11 ('b"000")) in
    let pa_s0  := zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_s0)) (xlen - 0 - 1) 0)) (0 * 8)) in
    let a8_ra  := zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_ra)) (xlen - 0 - 1) 0) in
    let a8_s0  := zero_extend' 64 (subrange_vec_dec (add_vec sp1 (sign_extend' 64 imm_s0)) (xlen - 0 - 1) 0) in
    let mout := <[gpr_of_Z (uint rd13) := regval_into_reg (subrange_vec_dec menvcfg0 (Z.sub xlen 1) 0)]>
                (<[gpr_of_Z (uint r_s0) := regval_into_reg (add_vec sp1 (sign_extend' 64 (caddi4spn_imm nzimm12)))]>
                (<[gpr_of_Z (uint rd9) := regval_into_reg sp1]> m)) in
    m !! gpr_of_Z 1 = Some vra -> m !! gpr_of_Z 2 = Some sp0 ->
    m !! gpr_of_Z 8 = Some vs0 -> m !! gpr_of_Z 15 = Some va5 ->
    pma_allows_all pmar0 -> pmp_allows_all pmpcfg0 ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    pmm_mode_backwards (_get_Seccfg_PMM mseccfg0) = PMM_Disabled ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_U misa0) ('b"1") = true ->
    is_aligned_vaddr (Virtaddr a8_ra) 8 = true -> is_aligned_paddr (Physaddr pa_ra) 8 = true ->
    is_aligned_vaddr (Virtaddr a8_s0) 8 = true -> is_aligned_paddr (Physaddr pa_s0) 8 = true ->
    PC ↦ᵣ tpc9 -∗ gpr_file m -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗ mcounteren ↦ᵣ mcounteren0 -∗ mtime ↦ᵣ mtime0 -∗ stimecmp ↦ᵣ stimecmp0 -∗
    ti_ctx misa0 mstatus0 mseccfg0 mc mcfg pmpcfg0 pmar0 elp0 -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa_ra j) ↦ₘ nth_byte vold_ra j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa_s0 j) ↦ₘ nth_byte vold_s0 j) -∗
    Kc1 -∗
    ▷ ( PC ↦ᵣ tpc14 -∗ gpr_file mout -∗ nextPC ↦ᵣ tpc14 -∗
        (R_bool minstret_increment) ↦ᵣ b1 -∗ minstret ↦ᵣ bump (bump (bump (bump (bump mst0)))) -∗
        menvcfg ↦ᵣ menvcfg0 -∗ mcounteren ↦ᵣ mcounteren0 -∗ mtime ↦ᵣ mtime0 -∗ stimecmp ↦ᵣ stimecmp0 -∗
        ti_ctx misa0 mstatus0 mseccfg0 mc mcfg pmpcfg0 pmar0 elp0 -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa_ra j) ↦ₘ nth_byte vra j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa_s0 j) ↦ₘ nth_byte vs0 j) -∗
        Kc1 -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros b1 bump sp1 imm_ra pa_ra imm_s0 pa_s0 a8_ra a8_s0 mout.
    intros Hm1 Hm2 Hm8 Hm15 Hpmaall Hpmpf HmIE Hlp HMPRV Hpmm HmisaC HmisaU Ha8ra Hpara Ha8s0 Hpas0.
    iIntros "Hpc Hfile Hnpc Hmi Hmst Hmenv Hmcen Hmtime Hstc Hctx Hstkra Hstks0 HK".
    iDestruct "Hctx" as "(Hmisa & Hpriv & Hhs & Hmdl & Hms & Help & Hsec & Hmcinh & Hmcfg & Hpmpc & Hpma & Hhtif)".
    iDestruct "HK" as "(K9 & K10 & K11 & K12 & K13)".
    iIntros "Hcont".
    (* idx 9 *)
    iDestruct (bi.equiv_entails_1_1 _ _ regroup9 with "[$K9 $K10]") as "W9".
    assert (Hrd9 : m !! gpr_of_Z (uint rd9) = Some sp0)
      by (replace (uint rd9) with 2 by (vm_compute; reflexivity); exact Hm2).
    iApply (wp_caddi_gpr_4 tpc9 w4_9 rd9 imm9 m sp0 misa0 b1
              npc0 mst0 mstatus0 mc mcfg pmpcfg0 pmar0 mi0 elp0 E Φ
              ltac:(vm_compute; discriminate) Hrd9 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              HmisaC decode4_9 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W9").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W9".
    replace (add_vec_int tpc9 2) with tpc10 by (vm_compute; reflexivity).
    iDestruct (bi.equiv_entails_1_2 _ _ regroup9 with "W9") as "(K9 & K10)".
    iEval (rewrite (E_skinstr 10 (kentry + 0x1e) 0xe406 16%nat ltac:(vmc) ltac:(vmc) ltac:(vmc))) in "K10".
    (* idx 10 *)
    set (m10 := <[gpr_of_Z (uint rd9) := regval_into_reg sp1]> m).
    assert (Hsp10 : m10 !! gpr_of_Z (uint csp_rs1) = Some sp1).
    { unfold m10. replace (uint csp_rs1) with 2 by (vm_compute; reflexivity).
      replace (uint rd9) with 2 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    assert (Hra10 : m10 !! gpr_of_Z (uint rs2_10) = Some vra).
    { unfold m10. replace (uint rs2_10) with 1 by (vm_compute; reflexivity).
      replace (uint rd9) with 2 by (vm_compute; reflexivity).
      rewrite lookup_insert_ne; [exact Hm1 | discriminate]. }
    iApply (wp_csdsp tpc10 w10 uimm10 rs2_10 m10 sp1 vra misa0 b1 vold_ra
              tpc10 (bump mst0) mstatus0 mseccfg0
              mc mcfg pmpcfg0 pmar0 b1 elp0 E Φ
              ltac:(vm_compute; discriminate) Hsp10 Hra10 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              HmisaC decode10 eq_refl HmIE Hlp HMPRV Hpmm Ha8ra Hpara
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hstkra K10").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hstkra K10".
    replace (add_vec_int tpc10 2) with tpc11 by (vm_compute; reflexivity).
    (* idx 11 *)
    iDestruct (bi.equiv_entails_1_1 _ _ regroup11 with "[$K11 $K12]") as "W11".
    assert (Hsp11 : m10 !! gpr_of_Z (uint csp_rs1) = Some sp1).
    { unfold m10. replace (uint csp_rs1) with 2 by (vm_compute; reflexivity).
      replace (uint rd9) with 2 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    assert (Hs011 : m10 !! gpr_of_Z (uint rs2_11) = Some vs0).
    { unfold m10. replace (uint rs2_11) with 8 by (vm_compute; reflexivity).
      replace (uint rd9) with 2 by (vm_compute; reflexivity).
      rewrite lookup_insert_ne; [exact Hm8 | discriminate]. }
    iApply (wp_csdsp_4 tpc11 w4_11 uimm11 rs2_11 m10 sp1 vs0 misa0 b1 vold_s0
              _ _ mstatus0 mseccfg0
              mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Hsp11 Hs011 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              HmisaC decode4_11 eq_refl HmIE Hlp HMPRV Hpmm Ha8s0 Hpas0
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hstks0 W11").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hstks0 W11".
    replace (add_vec_int tpc11 2) with tpc12 by (vm_compute; reflexivity).
    iDestruct (bi.equiv_entails_1_2 _ _ regroup11 with "W11") as "(K11 & K12)".
    iEval (rewrite (E_skinstr 12 (kentry + 0x22) 0x0800 16%nat ltac:(vmc) ltac:(vmc) ltac:(vmc))) in "K12".
    (* idx 12 *)
    assert (Hsp12 : m10 !! gpr_of_Z (uint csp_rs1) = Some sp1).
    { unfold m10. replace (uint csp_rs1) with 2 by (vm_compute; reflexivity).
      replace (uint rd9) with 2 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    assert (Hs012 : m10 !! gpr_of_Z (uint r_s0) = Some vs0).
    { unfold m10. replace (uint r_s0) with 8 by (vm_compute; reflexivity).
      replace (uint rd9) with 2 by (vm_compute; reflexivity).
      rewrite lookup_insert_ne; [exact Hm8 | discriminate]. }
    iApply (wp_caddi4spn_gpr tpc12 w12 nzimm12 crdc12 r_s0 m10 sp1 vs0 misa0 b1
              _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vmc) ltac:(vm_compute; discriminate) Hsp12 Hs012 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              HmisaC decode12 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K12").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K12".
    replace (add_vec_int tpc12 2) with tpc13 by (vm_compute; reflexivity).
    set (m12 := <[gpr_of_Z (uint r_s0) := regval_into_reg (add_vec sp1 (sign_extend' 64 (caddi4spn_imm nzimm12)))]> m10).
    iEval (rewrite (E_skinstr 13 (kentry + 0x24) 0x30a027f3 32%nat ltac:(vmc) ltac:(vmc) ltac:(vmc))) in "K13".
    (* idx 13 *)
    assert (Ha513 : m12 !! gpr_of_Z (uint rd13) = Some va5).
    { unfold m12, m10. replace (uint rd13) with 15 by (vm_compute; reflexivity).
      replace (uint r_s0) with 8 by (vm_compute; reflexivity).
      replace (uint rd9) with 2 by (vm_compute; reflexivity).
      rewrite lookup_insert_ne; [| discriminate].
      rewrite lookup_insert_ne; [| discriminate]. exact Hm15. }
    iApply (wp_csrr_menvcfg_gpr tpc13 w13 rs1z13 rd13 m12 va5 b1
              _ _ mstatus0 misa0 menvcfg0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vmc) ltac:(vmc) ltac:(vm_compute; discriminate) Ha513 HmisaU Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              decode13 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hmenv Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K13").
    iNext.
    iIntros "Hpc Hfile Hmisa Hmenv Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K13".
    replace (add_vec_int tpc13 4) with tpc14 by (vm_compute; reflexivity).
    (* convert window-form bytes back to kinstr_bytes for the Kc1 bundle *)
    iEval (rewrite (EW 10 16%nat 2%nat (kentry + 0x1e) 0xe406 tpc10 w10 ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(reflexivity)
                      ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|exfalso;lia]))) in "K10".
    iEval (rewrite (EW 12 16%nat 2%nat (kentry + 0x22) 0x0800 tpc12 w12 ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(reflexivity)
                      ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|exfalso;lia]))) in "K12".
    iEval (rewrite (EW 13 32%nat 4%nat (kentry + 0x24) 0x30a027f3 tpc13 w13 ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(reflexivity)
                      ltac:(intros j Hj; destruct j as [|[|[|[|j]]]]; [apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|exfalso;lia]))) in "K13".
    (* repackage and hand to continuation *)
    iApply ("Hcont" with "Hpc [Hfile] Hnpc Hmi Hmst Hmenv Hmcen Hmtime Hstc
              [Hmisa Hpriv Hhs Hmdl Hms Help Hsec Hmcinh Hmcfg Hpmpc Hpma Hhtif]
              Hstkra Hstks0 [$K9 $K10 $K11 $K12 $K13]").
    { unfold mout, m12, m10. iExact "Hfile". }
    { iFrame. }
  Qed.

  (* ===================================================================== *)
  (* CHUNK c2 : idx 14-18.  c.li a4,-1 ; c.slli a4 ; c.or a5 ; csrw menvcfg ;*)
  (* csrr a5,mcounteren.  Reads a4,a5; writes a4,a5,menvcfg.                 *)
  (* ===================================================================== *)
  Lemma wp_ti_c2
      (va4 va5 : mword 64)
      (m : gmap register_bitvector_64 (mword 64))
      (mst0 npc0 : mword 64) (mi0 : bool)
      (misa0 mstatus0 mseccfg0 menvcfg0 mtime0 stimecmp0 : mword 64)
      (mcounteren0 : mword 32)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1)
      E (Φ : mval -> iProp Σ) :
    let b1   := andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                     (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) in
    let bump := fun (x : mword 64) => if b1 then add_vec_int x 1 else x in
    let va4' := regval_into_reg (cslli_wval shamt15 (cli_wval imm14)) in
    let va5' := regval_into_reg (or_vec va5 va4') in
    let mout := <[gpr_of_Z (uint rd18) := regval_into_reg (zero_extend' 64 mcounteren0)]>
                (<[gpr_of_Z (uint r_a5) := va5']>
                (<[gpr_of_Z (uint rsd15) := va4']>
                (<[gpr_of_Z (uint rd14) := regval_into_reg (cli_wval imm14)]> m))) in
    m !! gpr_of_Z 14 = Some va4 -> m !! gpr_of_Z 15 = Some va5 ->
    pma_allows_all pmar0 -> pmp_allows_all pmpcfg0 ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Misa_U misa0) ('b"1") = true ->
    PC ↦ᵣ tpc14 -∗ gpr_file m -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗ mcounteren ↦ᵣ mcounteren0 -∗ mtime ↦ᵣ mtime0 -∗ stimecmp ↦ᵣ stimecmp0 -∗
    ti_ctx misa0 mstatus0 mseccfg0 mc mcfg pmpcfg0 pmar0 elp0 -∗
    Kc2 -∗
    ▷ ( PC ↦ᵣ tpc19 -∗ gpr_file mout -∗ nextPC ↦ᵣ tpc19 -∗
        (R_bool minstret_increment) ↦ᵣ b1 -∗ minstret ↦ᵣ bump (bump (bump (bump (bump mst0)))) -∗
        menvcfg ↦ᵣ menvcfg_legalized menvcfg0 va5' -∗ mcounteren ↦ᵣ mcounteren0 -∗ mtime ↦ᵣ mtime0 -∗ stimecmp ↦ᵣ stimecmp0 -∗
        ti_ctx misa0 mstatus0 mseccfg0 mc mcfg pmpcfg0 pmar0 elp0 -∗
        Kc2 -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros b1 bump va4' va5' mout.
    intros Hm14 Hm15 Hpmaall Hpmpf HmIE Hlp HmisaC HmisaS HmisaU.
    iIntros "Hpc Hfile Hnpc Hmi Hmst Hmenv Hmcen Hmtime Hstc Hctx HK".
    iDestruct "Hctx" as "(Hmisa & Hpriv & Hhs & Hmdl & Hms & Help & Hsec & Hmcinh & Hmcfg & Hpmpc & Hpma & Hhtif)".
    iDestruct "HK" as "(K14 & K15 & K16 & K17 & K18)".
    iIntros "Hcont".
    (* idx 14 *)
    iDestruct (bi.equiv_entails_1_1 _ _ regroup14 with "[$K14 $K15]") as "W14".
    assert (Ha414 : m !! gpr_of_Z (uint rd14) = Some va4)
      by (replace (uint rd14) with 14 by (vm_compute; reflexivity); exact Hm14).
    iApply (wp_cli_gpr_4 tpc14 w4_14 rd14 imm14 m va4 misa0 b1
              npc0 mst0 mstatus0 mc mcfg pmpcfg0 pmar0 mi0 elp0 E Φ
              ltac:(vm_compute; discriminate) Ha414 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              HmisaC decode4_14 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W14").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W14".
    replace (add_vec_int tpc14 2) with tpc15 by (vm_compute; reflexivity).
    set (m14 := <[gpr_of_Z (uint rd14) := regval_into_reg (cli_wval imm14)]> m).
    iDestruct (bi.equiv_entails_1_2 _ _ regroup14 with "W14") as "(K14 & K15)".
    iEval (rewrite (E_skinstr 15 (kentry + 0x2a) 0x177e 16%nat ltac:(vmc) ltac:(vmc) ltac:(vmc))) in "K15".
    (* idx 15 *)
    assert (Ha415 : m14 !! gpr_of_Z (uint rsd15) = Some (cli_wval imm14)).
    { unfold m14. replace (uint rsd15) with 14 by (vm_compute; reflexivity).
      replace (uint rd14) with 14 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_cslli_gpr tpc15 w15 shamt15 rsd15 m14 (cli_wval imm14) misa0 b1
              _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Ha415 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              HmisaC decode15 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K15").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K15".
    replace (add_vec_int tpc15 2) with tpc16 by (vm_compute; reflexivity).
    set (m15 := <[gpr_of_Z (uint rsd15) := regval_into_reg (cslli_wval shamt15 (cli_wval imm14))]> m14).
    (* idx 16 *)
    iDestruct (bi.equiv_entails_1_1 _ _ regroup16 with "[$K16 $K17]") as "(W16 & R16)".
    assert (Ha516 : m15 !! gpr_of_Z (uint r_a5) = Some va5).
    { unfold m15, m14. replace (uint r_a5) with 15 by (vm_compute; reflexivity).
      replace (uint rsd15) with 14 by (vm_compute; reflexivity).
      replace (uint rd14) with 14 by (vm_compute; reflexivity).
      rewrite lookup_insert_ne; [| discriminate].
      rewrite lookup_insert_ne; [exact Hm15 | discriminate]. }
    assert (Ha416 : m15 !! gpr_of_Z (uint r_a4) = Some va4').
    { unfold m15, va4'. replace (uint r_a4) with 14 by (vm_compute; reflexivity).
      replace (uint rsd15) with 14 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_cor_gpr_4 tpc16 w4_16 crsd16 crs2_16 r_a5 r_a4 m15 va5 va4' misa0 b1
              _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vmc) ltac:(vmc) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              Ha516 Ha416 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              HmisaC decode4_16 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W16").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W16".
    replace (add_vec_int tpc16 2) with tpc17 by (vm_compute; reflexivity).
    set (m16 := <[gpr_of_Z (uint r_a5) := regval_into_reg (or_vec va5 va4')]> m15).
    iDestruct (bi.equiv_entails_1_2 _ _ regroup16 with "[$W16 $R16]") as "(K16 & K17)".
    iEval (rewrite (E_skinstr 17 (kentry + 0x2e) 0x30a79073 32%nat ltac:(vmc) ltac:(vmc) ltac:(vmc))) in "K17".
    (* idx 17 *)
    assert (Ha517 : m16 !! gpr_of_Z (uint rs1_17) = Some (or_vec va5 va4')).
    { unfold m16. replace (uint rs1_17) with 15 by (vm_compute; reflexivity).
      replace (uint r_a5) with 15 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_csrw_menvcfg_gpr_2 tpc17 w17 rs1_17 m16 (or_vec va5 va4') misa0 mstatus0 menvcfg0 b1
              _ _ mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Ha517 HmisaS HmisaU Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              ltac:(vmc)
              ltac:(intros j Hj; destruct j as [|[|j]]; [vm_compute; reflexivity | vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              HmisaC decode17 eq_refl HmIE Hlp
              with "Hpc Hfile Hmenv Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K17").
    iNext.
    iIntros "Hpc Hfile Hmenv Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K17".
    replace (add_vec_int tpc17 4) with tpc18 by (vm_compute; reflexivity).
    iEval (rewrite (E_skinstr 18 (kentry + 0x32) 0x306027f3 32%nat ltac:(vmc) ltac:(vmc) ltac:(vmc))) in "K18".
    (* idx 18 *)
    assert (Ha518 : m16 !! gpr_of_Z (uint rd18) = Some (or_vec va5 va4')).
    { unfold m16. replace (uint rd18) with 15 by (vm_compute; reflexivity).
      replace (uint r_a5) with 15 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_csrr_mcounteren_gpr_2 tpc18 w18 rs1z18 rd18 m16 (or_vec va5 va4') b1
              _ _ mstatus0 misa0 mcounteren0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vmc) ltac:(vmc) ltac:(vm_compute; discriminate) Ha518 HmisaU Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              ltac:(intros j Hj; destruct j as [|[|j]]; [vm_compute; reflexivity | vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              HmisaC decode18 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hmcen Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K18").
    iNext.
    iIntros "Hpc Hfile Hmisa Hmcen Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K18".
    replace (add_vec_int tpc18 4) with tpc19 by (vm_compute; reflexivity).
    (* convert windows back to kinstr_bytes *)
    iEval (rewrite (EW 15 16%nat 2%nat (kentry + 0x2a) 0x177e tpc15 w15 ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(reflexivity)
                      ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|exfalso;lia]))) in "K15".
    iEval (rewrite (EW 17 32%nat 4%nat (kentry + 0x2e) 0x30a79073 tpc17 w17 ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(reflexivity)
                      ltac:(intros j Hj; destruct j as [|[|[|[|j]]]]; [apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|exfalso;lia]))) in "K17".
    iEval (rewrite (EW 18 32%nat 4%nat (kentry + 0x32) 0x306027f3 tpc18 w18 ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(reflexivity)
                      ltac:(intros j Hj; destruct j as [|[|[|[|j]]]]; [apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|exfalso;lia]))) in "K18".
    iApply ("Hcont" with "Hpc [Hfile] Hnpc Hmi Hmst Hmenv Hmcen Hmtime Hstc
              [Hmisa Hpriv Hhs Hmdl Hms Help Hsec Hmcinh Hmcfg Hpmpc Hpma Hhtif]
              [$K14 $K15 $K16 $K17 $K18]").
    { unfold mout, m16, m15, m14, va4', va5'. iExact "Hfile". }
    { iFrame. }
  Qed.

  (* ===================================================================== *)
  (* CHUNK c3 : idx 19-23.  ori a5 ; csrw mcounteren ; csrr a5,time ;        *)
  (* lui a4 ; addi a4.  Reads a5,a4; writes a5,a4,mcounteren.                *)
  (* ===================================================================== *)
  Lemma wp_ti_c3
      (va4 va5 : mword 64)
      (m : gmap register_bitvector_64 (mword 64))
      (mst0 npc0 : mword 64) (mi0 : bool)
      (misa0 mstatus0 mseccfg0 menvcfg0 mtime0 stimecmp0 : mword 64)
      (mcounteren0 : mword 32)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1)
      E (Φ : mval -> iProp Σ) :
    let b1   := andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                     (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) in
    let bump := fun (x : mword 64) => if b1 then add_vec_int x 1 else x in
    let va4lui := WpGprLui.luival (subrange_vec_dec w22 31 12) in
    let mout := <[gpr_of_Z (uint rd23) := regval_into_reg (add_vec va4lui (sign_extend' 64 (subrange_vec_dec w23 31 20)))]>
                (<[gpr_of_Z (uint rd22) := regval_into_reg va4lui]>
                (<[gpr_of_Z (uint rd21) := regval_into_reg (subrange_vec_dec mtime0 (Z.sub xlen 1) 0)]>
                (<[gpr_of_Z (uint rd19) := regval_into_reg (or_vec va5 (sign_extend' 64 (subrange_vec_dec w19 31 20)))]> m))) in
    m !! gpr_of_Z 14 = Some va4 -> m !! gpr_of_Z 15 = Some va5 ->
    pma_allows_all pmar0 -> pmp_allows_all pmpcfg0 ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_U misa0) ('b"1") = true ->
    PC ↦ᵣ tpc19 -∗ gpr_file m -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗ mcounteren ↦ᵣ mcounteren0 -∗ mtime ↦ᵣ mtime0 -∗ stimecmp ↦ᵣ stimecmp0 -∗
    ti_ctx misa0 mstatus0 mseccfg0 mc mcfg pmpcfg0 pmar0 elp0 -∗
    Kc3 -∗
    ▷ ( PC ↦ᵣ tpc24 -∗ gpr_file mout -∗ nextPC ↦ᵣ tpc24 -∗
        (R_bool minstret_increment) ↦ᵣ b1 -∗ minstret ↦ᵣ bump (bump (bump (bump (bump mst0)))) -∗
        menvcfg ↦ᵣ menvcfg0 -∗
        mcounteren ↦ᵣ legalize_mcounteren mcounteren0 (or_vec va5 (sign_extend' 64 (subrange_vec_dec w19 31 20))) -∗
        mtime ↦ᵣ mtime0 -∗ stimecmp ↦ᵣ stimecmp0 -∗
        ti_ctx misa0 mstatus0 mseccfg0 mc mcfg pmpcfg0 pmar0 elp0 -∗
        Kc3 -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros b1 bump va4lui mout.
    intros Hm14 Hm15 Hpmaall Hpmpf HmIE Hlp HmisaC HmisaU.
    iIntros "Hpc Hfile Hnpc Hmi Hmst Hmenv Hmcen Hmtime Hstc Hctx HK".
    iDestruct "Hctx" as "(Hmisa & Hpriv & Hhs & Hmdl & Hms & Help & Hsec & Hmcinh & Hmcfg & Hpmpc & Hpma & Hhtif)".
    iDestruct "HK" as "(K19 & K20 & K21 & K22 & K23)".
    iIntros "Hcont".
    iEval (rewrite (E_skinstr 19 (kentry + 0x36) 0x0027e793 32%nat ltac:(vmc) ltac:(vmc) ltac:(vmc))) in "K19".
    (* idx 19 *)
    assert (Ha519 : m !! gpr_of_Z (uint rs1_19) = Some va5)
      by (replace (uint rs1_19) with 15 by (vm_compute; reflexivity); exact Hm15).
    assert (Hard19 : m !! gpr_of_Z (uint rd19) = Some va5)
      by (replace (uint rd19) with 15 by (vm_compute; reflexivity); exact Hm15).
    iApply (wp_ori_gpr_2 tpc19 w19 rs1_19 rd19 (subrange_vec_dec w19 31 20) m va5 va5 misa0 b1
              npc0 mst0 mstatus0 mc mcfg pmpcfg0 pmar0 mi0 elp0 E Φ
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Ha519 Hard19 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              ltac:(intros j Hj; destruct j as [|[|j]]; [vm_compute; reflexivity | vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              HmisaC decode19 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K19").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K19".
    replace (add_vec_int tpc19 4) with tpc20 by (vm_compute; reflexivity).
    set (m19 := <[gpr_of_Z (uint rd19) := regval_into_reg (or_vec va5 (sign_extend' 64 (subrange_vec_dec w19 31 20)))]> m).
    set (va5_2 := or_vec va5 (sign_extend' 64 (subrange_vec_dec w19 31 20))).
    iEval (rewrite (E_skinstr 20 (kentry + 0x3a) 0x30679073 32%nat ltac:(vmc) ltac:(vmc) ltac:(vmc))) in "K20".
    (* idx 20 *)
    assert (Ha520 : m19 !! gpr_of_Z (uint rs1_20) = Some va5_2).
    { unfold m19, va5_2. replace (uint rs1_20) with 15 by (vm_compute; reflexivity).
      replace (uint rd19) with 15 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_csrw_mcounteren_gpr_2 tpc20 w20 rs1_20 m19 va5_2 misa0 mcounteren0 b1
              _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Ha520 HmisaU Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              ltac:(intros j Hj; destruct j as [|[|j]]; [vm_compute; reflexivity | vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              HmisaC decode20 eq_refl HmIE Hlp
              with "Hpc Hfile Hmcen Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K20").
    iNext.
    iIntros "Hpc Hfile Hmcen Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K20".
    replace (add_vec_int tpc20 4) with tpc21 by (vm_compute; reflexivity).
    iEval (rewrite (E_skinstr 21 (kentry + 0x3e) 0xc01027f3 32%nat ltac:(vmc) ltac:(vmc) ltac:(vmc))) in "K21".
    (* idx 21 *)
    assert (Ha521 : m19 !! gpr_of_Z (uint rd21) = Some va5_2).
    { unfold m19, va5_2. replace (uint rd21) with 15 by (vm_compute; reflexivity).
      replace (uint rd19) with 15 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_csrr_time_gpr_2 tpc21 w21 rs1z21 rd21 m19 va5_2 b1
              _ _ mstatus0 misa0 mtime0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vmc) ltac:(vmc) ltac:(vm_compute; discriminate) Ha521 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              ltac:(intros j Hj; destruct j as [|[|j]]; [vm_compute; reflexivity | vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              HmisaC decode21 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hmtime Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K21").
    iNext.
    iIntros "Hpc Hfile Hmisa Hmtime Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K21".
    replace (add_vec_int tpc21 4) with tpc22 by (vm_compute; reflexivity).
    set (m21 := <[gpr_of_Z (uint rd21) := regval_into_reg (subrange_vec_dec mtime0 (Z.sub xlen 1) 0)]> m19).
    iEval (rewrite (E_skinstr 22 (kentry + 0x42) 0x000f4737 32%nat ltac:(vmc) ltac:(vmc) ltac:(vmc))) in "K22".
    (* idx 22 *)
    assert (Ha422 : m21 !! gpr_of_Z (uint rd22) = Some va4).
    { unfold m21, m19. replace (uint rd22) with 14 by (vm_compute; reflexivity).
      replace (uint rd21) with 15 by (vm_compute; reflexivity).
      replace (uint rd19) with 15 by (vm_compute; reflexivity).
      rewrite lookup_insert_ne; [| discriminate].
      rewrite lookup_insert_ne; [exact Hm14 | discriminate]. }
    iApply (wp_lui_gpr_2 tpc22 w22 rd22 (subrange_vec_dec w22 31 12) m21 va4 misa0 b1
              _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Ha422 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              ltac:(intros j Hj; destruct j as [|[|j]]; [vm_compute; reflexivity | vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              HmisaC decode22 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K22").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K22".
    replace (add_vec_int tpc22 4) with tpc23 by (vm_compute; reflexivity).
    set (m22 := <[gpr_of_Z (uint rd22) := regval_into_reg va4lui]> m21).
    iEval (rewrite (E_skinstr 23 (kentry + 0x46) 0x24070713 32%nat ltac:(vmc) ltac:(vmc) ltac:(vmc))) in "K23".
    (* idx 23 *)
    assert (Ha523 : m22 !! gpr_of_Z (uint rs1_23) = Some va4lui).
    { unfold m22, va4lui. replace (uint rs1_23) with 14 by (vm_compute; reflexivity).
      replace (uint rd22) with 14 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    assert (Hard23 : m22 !! gpr_of_Z (uint rd23) = Some va4lui).
    { unfold m22, va4lui. replace (uint rd23) with 14 by (vm_compute; reflexivity).
      replace (uint rd22) with 14 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_addi_gpr_2 tpc23 w23 rs1_23 rd23 (subrange_vec_dec w23 31 20) m22 va4lui va4lui misa0 b1
              _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Ha523 Hard23 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              ltac:(intros j Hj; destruct j as [|[|j]]; [vm_compute; reflexivity | vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              ltac:(intros j Hj; destruct j as [|[|j]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | exfalso; lia])
              HmisaC decode23 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K23").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K23".
    replace (add_vec_int tpc23 4) with tpc24 by (vm_compute; reflexivity).
    iEval (rewrite (EW 19 32%nat 4%nat (kentry + 0x36) 0x0027e793 tpc19 w19 ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(reflexivity)
                      ltac:(intros j Hj; destruct j as [|[|[|[|j]]]]; [apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|exfalso;lia]))) in "K19".
    iEval (rewrite (EW 20 32%nat 4%nat (kentry + 0x3a) 0x30679073 tpc20 w20 ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(reflexivity)
                      ltac:(intros j Hj; destruct j as [|[|[|[|j]]]]; [apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|exfalso;lia]))) in "K20".
    iEval (rewrite (EW 21 32%nat 4%nat (kentry + 0x3e) 0xc01027f3 tpc21 w21 ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(reflexivity)
                      ltac:(intros j Hj; destruct j as [|[|[|[|j]]]]; [apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|exfalso;lia]))) in "K21".
    iEval (rewrite (EW 22 32%nat 4%nat (kentry + 0x42) 0x000f4737 tpc22 w22 ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(reflexivity)
                      ltac:(intros j Hj; destruct j as [|[|[|[|j]]]]; [apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|exfalso;lia]))) in "K22".
    iEval (rewrite (EW 23 32%nat 4%nat (kentry + 0x46) 0x24070713 tpc23 w23 ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(reflexivity)
                      ltac:(intros j Hj; destruct j as [|[|[|[|j]]]]; [apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|apply bv_eq;vm_compute;reflexivity|exfalso;lia]))) in "K23".
    iApply ("Hcont" with "Hpc [Hfile] Hnpc Hmi Hmst Hmenv Hmcen Hmtime Hstc
              [Hmisa Hpriv Hhs Hmdl Hms Help Hsec Hmcinh Hmcfg Hpmpc Hpma Hhtif]
              [$K19 $K20 $K21 $K22 $K23]").
    { unfold mout, m22, m21, m19, va4lui. iExact "Hfile". }
    { iFrame. }
  Qed.

  (* ===================================================================== *)
  (* CHUNK c4 : idx 24-29.  c.add a5 ; csrw stimecmp ; c.ldsp ra ;          *)
  (* c.ldsp s0 ; c.addi sp,+16 ; c.ret (PC:=ra).                            *)
  (* Reads a5,a4,sp,ra,s0; reads back the two stack slots.                  *)
  (* ===================================================================== *)
  Lemma wp_ti_c4
      (vsp vra0 vs00 va4 va5 : mword 64)
      (m : gmap register_bitvector_64 (mword 64))
      (mst0 npc0 : mword 64) (mi0 : bool)
      (misa0 mstatus0 mseccfg0 menvcfg0 mtime0 stimecmp0 : mword 64)
      (mcounteren0 : mword 32)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) (vstk_ra vstk_s0 : bv 64)
      E (Φ : mval -> iProp Σ) :
    let b1   := andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                     (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) in
    let imm_ra := zero_extend' 12 (concat_vec uimm10 ('b"000")) in
    let pa_ra  := zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec (add_vec vsp (sign_extend' 64 imm_ra)) (xlen - 0 - 1) 0)) (0 * 8)) in
    let a8_ra  := zero_extend' 64 (subrange_vec_dec (add_vec vsp (sign_extend' 64 imm_ra)) (xlen - 0 - 1) 0) in
    let imm_s0 := zero_extend' 12 (concat_vec uimm11 ('b"000")) in
    let pa_s0  := zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec (add_vec vsp (sign_extend' 64 imm_s0)) (xlen - 0 - 1) 0)) (0 * 8)) in
    let a8_s0  := zero_extend' 64 (subrange_vec_dec (add_vec vsp (sign_extend' 64 imm_s0)) (xlen - 0 - 1) 0) in
    let vra_ld := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vstk_ra)) in
    let tgt := update_vec_dec (add_vec vra_ld (sign_extend' 64 (zeros' 12 : mword 12))) 0 ('b"0") in
    m !! gpr_of_Z 1 = Some vra0 -> m !! gpr_of_Z 2 = Some vsp ->
    m !! gpr_of_Z 8 = Some vs00 -> m !! gpr_of_Z 14 = Some va4 -> m !! gpr_of_Z 15 = Some va5 ->
    pma_allows_all pmar0 -> pmp_allows_all pmpcfg0 ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    pmm_mode_backwards (_get_Seccfg_PMM mseccfg0) = PMM_Disabled ->
    bool_bit_backwards (_get_Seccfg_MLPE mseccfg0) = false ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true -> eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    is_aligned_vaddr (Virtaddr a8_ra) 8 = true -> is_aligned_paddr (Physaddr pa_ra) 8 = true ->
    is_aligned_vaddr (Virtaddr a8_s0) 8 = true -> is_aligned_paddr (Physaddr pa_s0) 8 = true ->
    (* the loaded return address must be 2-byte aligned (RVC c.ret target). *)
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec tgt 1) = false ->
    PC ↦ᵣ tpc24 -∗ gpr_file m -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗ mcounteren ↦ᵣ mcounteren0 -∗ mtime ↦ᵣ mtime0 -∗ stimecmp ↦ᵣ stimecmp0 -∗
    ti_ctx misa0 mstatus0 mseccfg0 mc mcfg pmpcfg0 pmar0 elp0 -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa_ra j) ↦ₘ nth_byte vstk_ra j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa_s0 j) ↦ₘ nth_byte vstk_s0 j) -∗
    Kc4 -∗
    ▷ ( PC ↦ᵣ tgt -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros b1 imm_ra pa_ra a8_ra imm_s0 pa_s0 a8_s0 vra_ld tgt.
    intros Hm1 Hm2 Hm8 Hm14 Hm15 Hpmaall Hpmpf HmIE Hlp HMPRV Hpmm Hmlpe HmisaC HmisaS Ha8ra Hpara Ha8s0 Hpas0 Hcal0 Hcal1.
    iIntros "Hpc Hfile Hnpc Hmi Hmst Hmenv Hmcen Hmtime Hstc Hctx Hstkra Hstks0 HK".
    iDestruct "Hctx" as "(Hmisa & Hpriv & Hhs & Hmdl & Hms & Help & Hsec & Hmcinh & Hmcfg & Hpmpc & Hpma & Hhtif)".
    iDestruct "HK" as "(K24 & K25 & K26 & K27 & K28 & K29)".
    iIntros "Hcont".
    iEval (rewrite (E_skinstr 24 (kentry + 0x4a) 0x97ba 16%nat ltac:(vmc) ltac:(vmc) ltac:(vmc))) in "K24".
    (* idx 24: c.add a5,a5,a4 *)
    assert (Ha524 : m !! gpr_of_Z (uint rsd24) = Some va5)
      by (replace (uint rsd24) with 15 by (vm_compute; reflexivity); exact Hm15).
    assert (Ha424 : m !! gpr_of_Z (uint rs2_24) = Some va4)
      by (replace (uint rs2_24) with 14 by (vm_compute; reflexivity); exact Hm14).
    iApply (wp_cadd_gpr tpc24 w24 rsd24 rs2_24 m va5 va4 misa0 b1
              npc0 mst0 mstatus0 mc mcfg pmpcfg0 pmar0 mi0 elp0 E Φ
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Ha524 Ha424 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              HmisaC decode24 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K24").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K24".
    replace (add_vec_int tpc24 2) with tpc25 by (vm_compute; reflexivity).
    set (m24 := <[gpr_of_Z (uint rsd24) := regval_into_reg (add_vec va5 va4)]> m).
    iEval (rewrite (E_skinstr 25 (kentry + 0x4c) 0x14d79073 32%nat ltac:(vmc) ltac:(vmc) ltac:(vmc))) in "K25".
    (* idx 25: csrw stimecmp,a5 *)
    assert (Ha525 : m24 !! gpr_of_Z (uint rs1_25) = Some (add_vec va5 va4)).
    { unfold m24. replace (uint rs1_25) with 15 by (vm_compute; reflexivity).
      replace (uint rsd24) with 15 by (vm_compute; reflexivity). rewrite lookup_insert. reflexivity. }
    iApply (wp_csrw_stimecmp_gpr tpc25 w25 rs1_25 m24 (add_vec va5 va4) misa0 mstatus0 stimecmp0 b1
              _ _ mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Ha525 HmisaS Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              decode25 eq_refl HmIE Hlp
              with "Hpc Hfile Hstc Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K25").
    iNext.
    iIntros "Hpc Hfile Hstc Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K25".
    replace (add_vec_int tpc25 4) with tpc26 by (vm_compute; reflexivity).
    (* idx 26: c.ldsp ra,8(sp)  (4-aligned, regroup with idx 27) *)
    assert (Huimm26 : uimm26 = uimm10) by (apply bv_eq; vm_compute; reflexivity).
    iDestruct (bi.equiv_entails_1_1 _ _ regroup26 with "[$K26 $K27]") as "W26".
    assert (Hsp26 : m24 !! gpr_of_Z (uint csp_rs1) = Some vsp).
    { unfold m24. replace (uint csp_rs1) with 2 by (vm_compute; reflexivity).
      replace (uint rsd24) with 15 by (vm_compute; reflexivity).
      rewrite lookup_insert_ne; [exact Hm2 | discriminate]. }
    assert (Hra26 : m24 !! gpr_of_Z (uint rd26) = Some vra0).
    { unfold m24. replace (uint rd26) with 1 by (vm_compute; reflexivity).
      replace (uint rsd24) with 15 by (vm_compute; reflexivity).
      rewrite lookup_insert_ne; [exact Hm1 | discriminate]. }
    iApply (wp_cldsp_gpr_4 tpc26 w4_26 uimm10 rd26 m24 vsp vra0 misa0 b1 vstk_ra
              _ _ mstatus0 mc mcfg mseccfg0 pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hsp26 Hra26 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              HmisaC ltac:(rewrite <- Huimm26; exact decode4_26) eq_refl HmIE Hlp HMPRV Hpmm Ha8ra Hpara
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hstkra W26").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hstkra W26".
    replace (add_vec_int tpc26 2) with tpc27 by (vm_compute; reflexivity).
    set (m26 := <[gpr_of_Z (uint rd26) := vra_ld]> m24).
    iDestruct (bi.equiv_entails_1_2 _ _ regroup26 with "W26") as "(K26 & K27)".
    iEval (rewrite (E_skinstr 27 (kentry + 0x52) 0x6402 16%nat ltac:(vmc) ltac:(vmc) ltac:(vmc))) in "K27".
    (* idx 27: c.ldsp s0,0(sp) *)
    assert (Huimm27 : uimm27 = uimm11) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hsp27 : m26 !! gpr_of_Z (uint csp_rs1) = Some vsp).
    { unfold m26, m24. replace (uint csp_rs1) with 2 by (vm_compute; reflexivity).
      replace (uint rd26) with 1 by (vm_compute; reflexivity).
      replace (uint rsd24) with 15 by (vm_compute; reflexivity).
      rewrite lookup_insert_ne; [| discriminate].
      rewrite lookup_insert_ne; [exact Hm2 | discriminate]. }
    assert (Hs027 : m26 !! gpr_of_Z (uint rd27) = Some vs00).
    { unfold m26, m24. replace (uint rd27) with 8 by (vm_compute; reflexivity).
      replace (uint rd26) with 1 by (vm_compute; reflexivity).
      replace (uint rsd24) with 15 by (vm_compute; reflexivity).
      rewrite lookup_insert_ne; [| discriminate].
      rewrite lookup_insert_ne; [exact Hm8 | discriminate]. }
    iApply (wp_cldsp_gpr tpc27 w27 uimm11 rd27 m26 vsp vs00 misa0 b1 vstk_s0
              _ _ mstatus0 mc mcfg mseccfg0 pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hsp27 Hs027 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              HmisaC ltac:(rewrite <- Huimm27; exact decode27) eq_refl HmIE Hlp HMPRV Hpmm Ha8s0 Hpas0
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hstks0 K27").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hstks0 K27".
    replace (add_vec_int tpc27 2) with tpc28 by (vm_compute; reflexivity).
    set (m27 := <[gpr_of_Z (uint rd27) := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vstk_s0))]> m26).
    (* idx 28: c.addi sp,sp,16  (4-aligned, regroup with idx 29) *)
    iDestruct (bi.equiv_entails_1_1 _ _ regroup28 with "[$K28 $K29]") as "W28".
    assert (Hsp28 : m27 !! gpr_of_Z (uint rd28) = Some vsp).
    { unfold m27, m26, m24. replace (uint rd28) with 2 by (vm_compute; reflexivity).
      replace (uint rd27) with 8 by (vm_compute; reflexivity).
      replace (uint rd26) with 1 by (vm_compute; reflexivity).
      replace (uint rsd24) with 15 by (vm_compute; reflexivity).
      rewrite lookup_insert_ne; [| discriminate].
      rewrite lookup_insert_ne; [| discriminate].
      rewrite lookup_insert_ne; [exact Hm2 | discriminate]. }
    iApply (wp_caddi_gpr_4 tpc28 w4_28 rd28 imm28 m27 vsp misa0 b1
              _ _ mstatus0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Hsp28 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              HmisaC decode4_28 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W28").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W28".
    replace (add_vec_int tpc28 2) with tpc29 by (vm_compute; reflexivity).
    set (m28 := <[gpr_of_Z (uint rd28) := regval_into_reg (add_vec vsp (sign_extend' 64 (sign_extend' 12 imm28)))]> m27).
    iDestruct (bi.equiv_entails_1_2 _ _ regroup28 with "W28") as "(K28 & K29)".
    iEval (rewrite (E_skinstr 29 (kentry + 0x56) 0x8082 16%nat ltac:(vmc) ltac:(vmc) ltac:(vmc))) in "K29".
    (* idx 29: c.ret *)
    assert (Hra29 : m28 !! gpr_of_Z (uint ra29) = Some vra_ld).
    { unfold m28, m27, m26, vra_ld. replace (uint ra29) with 1 by (vm_compute; reflexivity).
      replace (uint rd28) with 2 by (vm_compute; reflexivity).
      replace (uint rd27) with 8 by (vm_compute; reflexivity).
      replace (uint rd26) with 1 by (vm_compute; reflexivity).
      rewrite lookup_insert_ne; [| discriminate].
      rewrite lookup_insert_ne; [| discriminate].
      rewrite lookup_insert. reflexivity. }
    iApply (wp_cret tpc29 w29 ra29 m28 vra_ld misa0 b1
              _ _ mstatus0 mseccfg0 mc mcfg pmpcfg0 pmar0 _ elp0 E Φ
              ltac:(vm_compute; discriminate) Hra29 Hmlpe Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              HmisaC decode29 Hcal0 Hcal1 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsec Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K29").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsec Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K29".
    iApply ("Hcont" with "Hpc").
  Qed.

  Lemma wp_timerinit
      (sp0 vra vs0 va4 va5 : mword 64)
      (m : gmap register_bitvector_64 (mword 64))
      (mst0 : mword 64)
      (misa0 mstatus0 mseccfg0 menvcfg0 mtime0 stimecmp0 : mword 64)
      (mcounteren0 : mword 32)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1)
      (vold_ra vold_s0 : bv 64)
      E (Φ : mval -> iProp Σ) :
    (* sp after idx 9 (C_ADDI sp,sp,imm9) *)
    let sp1   := add_vec sp0 (sign_extend' 64 (sign_extend' 12 imm9)) in
    let bump  := fun (x : mword 64) => if andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                                                (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0"))
                                       then add_vec_int x 1 else x in
    (* stack slot for ra: c.sdsp ra,8(sp1) *)
    let imm_ra := zero_extend' 12 (concat_vec uimm10 ('b"000")) in
    let ea_ra  := add_vec sp1 (sign_extend' 64 imm_ra) in
    let a8_ra  := zero_extend' 64 (subrange_vec_dec ea_ra (xlen - 0 - 1) 0) in
    let pa_ra  := zero_extend' 64 (add_vec_int a8_ra (0 * 8)) in
    (* stack slot for s0: c.sdsp s0,0(sp1) *)
    let imm_s0 := zero_extend' 12 (concat_vec uimm11 ('b"000")) in
    let ea_s0  := add_vec sp1 (sign_extend' 64 imm_s0) in
    let a8_s0  := zero_extend' 64 (subrange_vec_dec ea_s0 (xlen - 0 - 1) 0) in
    let pa_s0  := zero_extend' 64 (add_vec_int a8_s0 (0 * 8)) in
    (* lookups for the 5 registers timerinit touches *)
    m !! gpr_of_Z 1 = Some vra ->
    m !! gpr_of_Z 2 = Some sp0 ->
    m !! gpr_of_Z 8 = Some vs0 ->
    m !! gpr_of_Z 14 = Some va4 ->
    m !! gpr_of_Z 15 = Some va5 ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    pmm_mode_backwards (_get_Seccfg_PMM mseccfg0) = PMM_Disabled ->
    bool_bit_backwards (_get_Seccfg_MLPE mseccfg0) = false ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Misa_U misa0) ('b"1") = true ->
    (* stack alignment for both slots (sp1+8, sp1+0) *)
    is_aligned_vaddr (Virtaddr a8_ra) 8 = true ->
    is_aligned_paddr (Physaddr pa_ra) 8 = true ->
    is_aligned_vaddr (Virtaddr a8_s0) 8 = true ->
    is_aligned_paddr (Physaddr pa_s0) 8 = true ->
    (* the saved/restored return address must be 2-byte aligned (RVC c.ret). *)
    let vra_ld := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vra)) in
    let tgt := update_vec_dec (add_vec vra_ld (sign_extend' 64 (zeros' 12 : mword 12))) 0 ('b"0") in
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec tgt 1) = false ->
    PC ↦ᵣ tpc9 -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ tpc9 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mseccfg ↦ᵣ mseccfg0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗ mcounteren ↦ᵣ mcounteren0 -∗ mtime ↦ᵣ mtime0 -∗ stimecmp ↦ᵣ stimecmp0 -∗
    mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa_ra j) ↦ₘ nth_byte vold_ra j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa_s0 j) ↦ₘ nth_byte vold_s0 j) -∗
    kernel_text -∗
    (* continuation receives PC = the c.ret target (the loaded return address). *)
    ▷ ( PC ↦ᵣ update_vec_dec
                 (add_vec
                    (regval_into_reg (extend_value false
                       (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vra)))
                    (sign_extend' 64 (zeros' 12 : mword 12))) 0 ('b"0")
        -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros sp1 bump imm_ra ea_ra a8_ra pa_ra imm_s0 ea_s0 a8_s0 pa_s0.
    intros Hm1 Hm2 Hm8 Hm14 Hm15 Hpmaall Hpmpf HmIE Hlp HMPRV Hpmm Hmlpe HmisaC HmisaS HmisaU
      Ha8ra Hpara Ha8s0 Hpas0.
    intros vra_ld tgt Hcal0 Hcal1.
    set (b1 := andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                    (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0"))).
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hmenv Hmcen Hmtime Hstc
             Hmcinh Hmcfg Hpmpc Hpma Hhtif Hstkra Hstks0 Htext Hcont".
    iAssert (ti_ctx misa0 mstatus0 mseccfg0 mc mcfg pmpcfg0 pmar0 elp0)
      with "[Hmisa Hpriv Hhs Hmdl Hms Help Hsec Hmcinh Hmcfg Hpmpc Hpma Hhtif]" as "Hctx".
    { iFrame. }
    iDestruct (chain_text_split with "Htext") as
      "(Hpre & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & Krest)".
    (* ---- chunk c1 (idx 9-13) ---- *)
    iApply (wp_ti_c1 sp0 vra vs0 va5 m mst0 tpc9 mi0 misa0 mstatus0 mseccfg0 menvcfg0 mtime0 stimecmp0
              mcounteren0 mc mcfg pmpcfg0 pmar0 elp0 vold_ra vold_s0 E Φ
              Hm1 Hm2 Hm8 Hm15 Hpmaall Hpmpf HmIE Hlp HMPRV Hpmm HmisaC HmisaU Ha8ra Hpara Ha8s0 Hpas0
              with "Hpc Hfile Hnpc Hmi Hmst Hmenv Hmcen Hmtime Hstc Hctx Hstkra Hstks0 [$K9 $K10 $K11 $K12 $K13]").
    iNext.
    iIntros "Hpc Hfile Hnpc Hmi Hmst Hmenv Hmcen Hmtime Hstc Hctx Hstkra Hstks0 HK1".
    (* c1's output map: a5:=menvcfg, s0:=addi4spn, sp:=sp1.  c2 reads a4(orig) & a5(menvcfg). *)
    set (m1 := <[gpr_of_Z (uint rd13) := regval_into_reg (subrange_vec_dec menvcfg0 (Z.sub xlen 1) 0)]>
              (<[gpr_of_Z (uint r_s0) := regval_into_reg (add_vec sp1 (sign_extend' 64 (caddi4spn_imm nzimm12)))]>
              (<[gpr_of_Z (uint rd9) := regval_into_reg sp1]> m))).
    assert (Hc2_a4 : m1 !! gpr_of_Z 14 = Some va4).
    { unfold m1. change (uint rd13) with 15. change (uint r_s0) with 8. change (uint rd9) with 2.
      rewrite lookup_insert_ne; [| discriminate]. rewrite lookup_insert_ne; [| discriminate].
      rewrite lookup_insert_ne; [exact Hm14 | discriminate]. }
    assert (Hc2_a5 : m1 !! gpr_of_Z 15 = Some (regval_into_reg (subrange_vec_dec menvcfg0 (Z.sub xlen 1) 0))).
    { unfold m1. change (uint rd13) with 15. rewrite lookup_insert. reflexivity. }
    iDestruct "HK1" as "(K9 & K10 & K11 & K12 & K13)".
    (* ---- chunk c2 (idx 14-18) ---- *)
    iApply (wp_ti_c2 va4 (regval_into_reg (subrange_vec_dec menvcfg0 (Z.sub xlen 1) 0)) m1
              _ tpc14 b1 misa0 mstatus0 mseccfg0 menvcfg0 mtime0 stimecmp0
              mcounteren0 mc mcfg pmpcfg0 pmar0 elp0 E Φ
              Hc2_a4 Hc2_a5 Hpmaall Hpmpf HmIE Hlp HmisaC HmisaS HmisaU
              with "Hpc Hfile Hnpc Hmi Hmst Hmenv Hmcen Hmtime Hstc Hctx [$K14 $K15 $K16 $K17 $K18]").
    iNext.
    iIntros "Hpc Hfile Hnpc Hmi Hmst Hmenv Hmcen Hmtime Hstc Hctx HK2".
    iDestruct "HK2" as "(K14 & K15 & K16 & K17 & K18)".
    (* c2's output map.  c3 reads a4(cslli) & a5(mcounteren). *)
    set (va4_c2 := regval_into_reg (cslli_wval shamt15 (cli_wval imm14))).
    set (va5_c2_in := regval_into_reg (subrange_vec_dec menvcfg0 (Z.sub xlen 1) 0)).
    set (m2 := <[gpr_of_Z (uint rd18) := regval_into_reg (zero_extend' 64 mcounteren0)]>
              (<[gpr_of_Z (uint r_a5) := regval_into_reg (or_vec va5_c2_in va4_c2)]>
              (<[gpr_of_Z (uint rsd15) := va4_c2]>
              (<[gpr_of_Z (uint rd14) := regval_into_reg (cli_wval imm14)]> m1)))).
    assert (Hc3_a4 : m2 !! gpr_of_Z 14 = Some va4_c2).
    { unfold m2. change (uint rd18) with 15. change (uint r_a5) with 15. change (uint rsd15) with 14.
      change (uint rd14) with 14.
      rewrite lookup_insert_ne; [| discriminate]. rewrite lookup_insert_ne; [| discriminate].
      rewrite lookup_insert. reflexivity. }
    assert (Hc3_a5 : m2 !! gpr_of_Z 15 = Some (regval_into_reg (zero_extend' 64 mcounteren0))).
    { unfold m2. change (uint rd18) with 15. rewrite lookup_insert. reflexivity. }
    (* ---- chunk c3 (idx 19-23) ---- *)
    iApply (wp_ti_c3 va4_c2 (regval_into_reg (zero_extend' 64 mcounteren0)) m2
              _ tpc19 b1 misa0 mstatus0 mseccfg0
              (menvcfg_legalized menvcfg0 (regval_into_reg (or_vec va5_c2_in va4_c2)))
              mtime0 stimecmp0
              mcounteren0 mc mcfg pmpcfg0 pmar0 elp0 E Φ
              Hc3_a4 Hc3_a5 Hpmaall Hpmpf HmIE Hlp HmisaC HmisaU
              with "Hpc Hfile Hnpc Hmi Hmst Hmenv Hmcen Hmtime Hstc Hctx [$K19 $K20 $K21 $K22 $K23]").
    iNext.
    iIntros "Hpc Hfile Hnpc Hmi Hmst Hmenv Hmcen Hmtime Hstc Hctx HK3".
    iDestruct "HK3" as "(K19 & K20 & K21 & K22 & K23)".
    (* c3's output map m3.  c4 reads a5(time), a4(addi), sp, ra, s0 + the stack. *)
    set (va4lui := WpGprLui.luival (subrange_vec_dec w22 31 12)).
    set (va5_c2_in' := regval_into_reg (zero_extend' 64 mcounteren0)).
    set (m3 := <[gpr_of_Z (uint rd23) := regval_into_reg (add_vec va4lui (sign_extend' 64 (subrange_vec_dec w23 31 20)))]>
              (<[gpr_of_Z (uint rd22) := regval_into_reg va4lui]>
              (<[gpr_of_Z (uint rd21) := regval_into_reg (subrange_vec_dec mtime0 (Z.sub xlen 1) 0)]>
              (<[gpr_of_Z (uint rd19) := regval_into_reg (or_vec va5_c2_in' (sign_extend' 64 (subrange_vec_dec w19 31 20)))]> m2)))).
    assert (Hc4_a5 : m3 !! gpr_of_Z 15 = Some (regval_into_reg (subrange_vec_dec mtime0 (Z.sub xlen 1) 0))).
    { unfold m3. change (uint rd23) with 14. change (uint rd22) with 14. change (uint rd21) with 15.
      rewrite lookup_insert_ne; [| discriminate]. rewrite lookup_insert_ne; [| discriminate].
      rewrite lookup_insert. reflexivity. }
    assert (Hc4_a4 : m3 !! gpr_of_Z 14 = Some (regval_into_reg (add_vec va4lui (sign_extend' 64 (subrange_vec_dec w23 31 20))))).
    { unfold m3. change (uint rd23) with 14. rewrite lookup_insert. reflexivity. }
    assert (Hc4_sp : m3 !! gpr_of_Z 2 = Some (regval_into_reg sp1)).
    { unfold m3, m2, m1. change (uint rd23) with 14. change (uint rd22) with 14. change (uint rd21) with 15.
      change (uint rd19) with 15. change (uint rd18) with 15. change (uint r_a5) with 15.
      change (uint rsd15) with 14. change (uint rd14) with 14. change (uint rd13) with 15.
      change (uint r_s0) with 8. change (uint rd9) with 2.
      do 10 (rewrite lookup_insert_ne; [| discriminate]). rewrite lookup_insert. reflexivity. }
    assert (Hc4_ra : m3 !! gpr_of_Z 1 = Some vra).
    { unfold m3, m2, m1. change (uint rd23) with 14. change (uint rd22) with 14. change (uint rd21) with 15.
      change (uint rd19) with 15. change (uint rd18) with 15. change (uint r_a5) with 15.
      change (uint rsd15) with 14. change (uint rd14) with 14. change (uint rd13) with 15.
      change (uint r_s0) with 8. change (uint rd9) with 2.
      do 11 (rewrite lookup_insert_ne; [| discriminate]). exact Hm1. }
    assert (Hc4_s0 : m3 !! gpr_of_Z 8 = Some (regval_into_reg (add_vec sp1 (sign_extend' 64 (caddi4spn_imm nzimm12))))).
    { unfold m3, m2, m1. change (uint rd23) with 14. change (uint rd22) with 14. change (uint rd21) with 15.
      change (uint rd19) with 15. change (uint rd18) with 15. change (uint r_a5) with 15.
      change (uint rsd15) with 14. change (uint rd14) with 14. change (uint rd13) with 15.
      change (uint r_s0) with 8. change (uint rd9) with 2.
      do 9 (rewrite lookup_insert_ne; [| discriminate]). rewrite lookup_insert. reflexivity. }
    (* ---- chunk c4 (idx 24-29) ---- *)
    iApply (wp_ti_c4 (regval_into_reg sp1) vra
              (regval_into_reg (add_vec sp1 (sign_extend' 64 (caddi4spn_imm nzimm12))))
              (regval_into_reg (add_vec va4lui (sign_extend' 64 (subrange_vec_dec w23 31 20))))
              (regval_into_reg (subrange_vec_dec mtime0 (Z.sub xlen 1) 0)) m3
              _ tpc24 b1 misa0 mstatus0 mseccfg0
              (menvcfg_legalized menvcfg0 (regval_into_reg (or_vec va5_c2_in va4_c2)))
              mtime0 stimecmp0
              (legalize_mcounteren mcounteren0 (or_vec va5_c2_in' (sign_extend' 64 (subrange_vec_dec w19 31 20))))
              mc mcfg pmpcfg0 pmar0 elp0 vra vs0 E Φ
              Hc4_ra Hc4_sp Hc4_s0 Hc4_a4 Hc4_a5 Hpmaall Hpmpf HmIE Hlp HMPRV Hpmm Hmlpe HmisaC HmisaS
              ltac:(exact Ha8ra) ltac:(exact Hpara) ltac:(exact Ha8s0) ltac:(exact Hpas0)
              ltac:(exact Hcal0) ltac:(exact Hcal1)
              with "Hpc Hfile Hnpc Hmi Hmst Hmenv Hmcen Hmtime Hstc Hctx Hstkra Hstks0 [$K24 $K25 $K26 $K27 $K28 $K29]").
    iApply "Hcont".
  Qed.

End WpStartChain.
