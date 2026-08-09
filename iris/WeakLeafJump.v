(** * WeakLeafJump.v — the WEAK JUMP LEAVES (M4, start()/timerinit() port)

    The two control-flow shapes the [start()] / [timerinit()] port needs:

      §1  the [exec_eff] cone of the COMPRESSED return jump ([c.jr rs1] /
          [c.ret], i.e. the expanded [jalr x0, 0(rs1)]) — the mirrors of
          [WpMmodeLeafBase.exec_cE_zicfilp_false], [ExecCommon.exec_jump_to_zca]
          and [WpMmodeLeafBase.exec_execute_JALR_ret_zca], plus the successor
          register frame [cjr_sexec_facts] (a jump writes [nextPC] TWICE and,
          for [rd = x0], writes no GPR at all — so neither
          [WeakLeafWin.load_sexec_facts] nor [WkEntryNew.jal_sexec_facts]
          fits);
      §2  [wwp_jal_leaf] — the [F_Base] JAL leaf.  Statement =
          [WpMmodeJal.wp_jal_gpr] under the porting-table swaps, with the GPRs
          held as ONE destination CELL (every call site of this leaf has a
          link register that aliases nothing).  The proof is
          [WkEntryNew]'s inline [jal] funnel block, hoisted and made generic
          in the pc / immediate / link register / fetch alignment.
      §3  [wwp_cjr_rvc_leaf] — the [F_RVC] [c.jr]/[c.ret] leaf.  Statement =
          [WpMmodeJalr.wp_cret_gpr_zca] under the same swaps, cell-based.

    Both leaves ride the PLAIN funnel ([WeakFunnel.wwp_instr]) with a
    fetch-only, no-write certificate, and both are ALIGNMENT-GENERIC (the
    [al4 : bool] parameter of [WeakLeafRegOnly] / [WeakLeafTor]) because
    [start()] and [timerinit()] use both fetch alignments.

    THE ALIGNMENT SIDE CONDITION IS ABOUT THE *TARGET*, NOT THE pc.  JAL's
    execute checks bit 0 AND bit 1 of [pc + sign_extend imm], and neither is
    computable here (both [pc] and [imm] are variables — the recorded
    branch/jump gotcha), so the leaf takes the 4-alignment of the target as a
    PREMISE, exactly as [wp_jal_gpr] does, and splits it with
    [RiscvExtras.aligned4_jump_bits].  The compressed return jump needs NO
    such premise: under [misa.C] (which [WeakFunnel.wcfg_regs] hands the leaf)
    the model's [jump_to] accepts a merely 2-aligned target, and [ret_pc]
    clears bit 0 by construction ([RiscvExtras.ret_pc_aligned]). *)
From Stdlib Require Import ZArith Zquot Zwf.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterface.
Require Import SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem WeakInterp WeakLang WeakGhost WeakBridge.
Require Import WeakView WeakVProp WeakFence.
Require Import WeakInstr WeakStore WeakCert WeakEff.
Require Import WeakEffSkel WeakPmpEff WeakTickEff WeakLeafEffCommon.
Require Import WeakFetchEff WeakFetch2 WeakFetchRvc.
Require Import WeakFunnel WpDecodeBridge.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import RegFile WpGpr WpMmodeLeafBase.
Require Import WeakLeafWin.
Require Import ExecCommon WpDecode.
Require Import WeakLeafRegOnly WeakLeafTor.
Require Import WkEntryEff WkEntryNew.

Import SailStdpp.Values.
Import Defs.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. THE [exec_eff] CONE OF THE COMPRESSED RETURN JUMP (trace [])

    Every lemma is its SC twin with the trace component added; the proofs are
    the SC proofs under the substitutions [exec_bind_Some] →
    [exec_eff_bind_nil], [exec_bind0_Some] → [exec_eff_bind0_nil],
    [exec_and_boolM_Some] → [exec_eff_and_boolM_nil], [exec_returnM] →
    [exec_eff_returnM], [execR_bind_Some] → [execR_eff_bind_nil],
    [execR_returnR_fwd] → [execR_eff_returnR], [execR_liftR] →
    [execR_eff_liftR]. *)

(** *** 1a. [currentlyEnabled Ext_Zicfilp] = false in M-mode with
    [mseccfg.MLPE] clear — [WpMmodeLeafBase.exec_cE_zicfilp_false]. *)

Lemma exec_eff_cE_zicfilp_false s :
  register_lookup cur_privilege (sregs s) = Machine ->
  bool_bit_backwards (_get_Seccfg_MLPE (register_lookup mseccfg s.(sregs)))
    = false ->
  exec_eff (currentlyEnabled Ext_Zicfilp) s = Some (false, s, []).
Proof.
  intros Hpriv Hmlpe.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zicfilp) 0) with true
    by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _
            (exec_eff_rec_cE_Zicsr_any
               (currentlyEnabled_measure Ext_Zicfilp - 1) _ s
               ltac:(vm_compute; reflexivity))).
  cbn match.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_hartSupports_Zicfilp s)).
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
  rewrite Hpriv.
  match goal with |- context[_rec_get_xLPE Machine _ ?acc] => destruct acc end.
  cbn [_rec_get_xLPE]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zicfilp - 1) 0) with true
    by (vm_compute; reflexivity).
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mseccfg s)). cbn match.
  rewrite Hmlpe. apply exec_eff_returnM.
Qed.

(** *** 1b. [jump_to] under the C extension — [ExecCommon.exec_jump_to_zca].
    [WkEntryEff.exec_eff_jump_to]'s script with the bit-1 arm resolved by the
    [Ext_Zca] probe instead of by a bit-1 hypothesis. *)

Lemma exec_eff_jump_to_zca (target : SailStdpp.Values.mword 64) s :
  eq_vec (access_vec_dec target 0) ('b"0") = true ->
  exec_eff (currentlyEnabled Ext_Zca) s = Some (true, s, []) ->
  exec_eff (jump_to target) s
  = Some (RETIRE_SUCCESS, set_reg s nextPC target, []).
Proof.
  intros Halign Hzca.
  unfold jump_to. rewrite exec_eff_catch_early_return.
  change (ext_control_check_pc target) with (@None unit). cbv iota beta.
  rewrite (execR_eff_bind_nil _ _ _ false s).
  2:{ unfold Defs.bind0.
      erewrite execR_eff_bind_nil.
      2:{ erewrite execR_eff_bind_nil.
          2:{ apply execR_eff_returnR. }
          rewrite execR_eff_liftR. unfold assert_exp. rewrite Halign.
          cbn match. rewrite exec_eff_returnm. reflexivity. }
      unfold and_boolM.
      rewrite (execR_eff_bind_nil _ _ _
                 (bit_to_bool (access_vec_dec target 1)) s).
      2:{ apply execR_eff_returnR. }
      destruct (bit_to_bool (access_vec_dec target 1)).
      - cbv iota beta.
        rewrite (execR_eff_bind_nil _ _ _ true s).
        2:{ rewrite execR_eff_liftR. rewrite Hzca. reflexivity. }
        cbv iota beta. first [ apply execR_eff_returnR | reflexivity ].
      - cbv iota beta. first [ apply execR_eff_returnR | reflexivity ]. }
  cbv iota beta.
  unfold Defs.bind0.
  rewrite (execR_eff_bind_nil _ _ _ tt (set_reg s nextPC target)).
  2:{ rewrite execR_eff_liftR. rewrite exec_eff_set_next_pc. reflexivity. }
  rewrite (execR_eff_returnR RETIRE_SUCCESS (set_reg s nextPC target)).
  reflexivity.
Qed.

(** *** 1c. The return-shaped JALR ([rd = x0]: no link write) —
    [WpMmodeLeafBase.exec_execute_JALR_ret_zca]. *)

Lemma exec_eff_execute_JALR_ret_zca (imm : mword 12) (rs1 rdz : mword 5) s :
  uint rs1 <> 0 -> uint rdz = 0 ->
  exec_eff (currentlyEnabled Ext_Zicfilp) s = Some (false, s, []) ->
  exec_eff (currentlyEnabled Ext_Zca) s = Some (true, s, []) ->
  eq_vec (access_vec_dec
            (update_vec_dec
               (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                           s.(sregs)) (sign_extend' 64 imm)) 0 ('b"0")) 0)
    ('b"0") = true ->
  exec_eff (execute_JALR imm (Regidx rs1) (Regidx rdz)) s
  = Some (RETIRE_SUCCESS,
          set_reg s nextPC
            (update_vec_dec
               (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                           s.(sregs)) (sign_extend' 64 imm)) 0 ('b"0")),
          []).
Proof.
  intros Hrs1 Hrdz Hzic Hzca Halign.
  unfold execute_JALR.
  rewrite (exec_eff_bind_nil _ _ _ _ _
            (_ : exec_eff (Defs.bind0 (update_elp_state (Regidx rs1))
                             (get_next_pc tt)) s
                 = Some (register_lookup nextPC s.(sregs), s, []))).
  2:{ rewrite (exec_eff_bind0_nil _ _ _ _ _
                (_ : exec_eff (update_elp_state (Regidx rs1)) s
                     = Some (tt, s, []))).
      2:{ unfold update_elp_state.
          rewrite (exec_eff_bind_nil _ _ _ _ _ Hzic). cbn match.
          apply exec_eff_returnm. }
      unfold get_next_pc. exact (exec_eff_read_reg nextPC s). }
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_rX_bits_gpr rs1 s)).
  replace (Z.eqb (uint rs1) 0) with false
    by (symmetry; apply Z.eqb_neq; exact Hrs1).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_jump_to_zca _ s Halign Hzca)).
  cbn match.
  rewrite (exec_eff_bind0_nil _ _ _ _ _
            (exec_eff_wX_bits_gpr rdz (register_lookup nextPC s.(sregs))
               (set_reg s nextPC
                  (update_vec_dec
                     (add_vec (register_lookup
                                 (R_bitvector_64 (gpr_of_Z (uint rs1)))
                                 s.(sregs)) (sign_extend' 64 imm))
                     0 ('b"0"))))).
  rewrite Hrdz. cbn match. apply exec_eff_returnm.
Qed.

(** *** 1d. The end-to-end [c.jr rs1] / [c.ret] execute mirror, stated at the
    canonical [RiscvExtras.ret_pc] target (the [add_vec .. zeros] the model
    emits collapses — [ret_pc_jalr]) and at exactly the config facts
    [WeakFunnel.wcfg_regs] hands a leaf. *)

Lemma exec_eff_execute_cret_zca (ra : mword 5) s :
  uint ra <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  register_lookup mseccfg s.(sregs) = mword_of_int 0 ->
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (execute (JALR (zeros' 12, Regidx ra, zreg))) s
  = Some (RETIRE_SUCCESS,
          set_reg s nextPC
            (ret_pc (register_lookup (R_bitvector_64 (gpr_of_Z (uint ra)))
                       s.(sregs))),
          []).
Proof.
  intros Hra Hpriv Hsec HC.
  assert (Hzic : exec_eff (currentlyEnabled Ext_Zicfilp) s = Some (false, s, [])).
  { apply exec_eff_cE_zicfilp_false; [exact Hpriv|].
    rewrite Hsec. vm_compute. reflexivity. }
  assert (Hzca : exec_eff (currentlyEnabled Ext_Zca) s = Some (true, s, []))
    by (apply exec_eff_currentlyEnabled_Zca; exact HC).
  assert (Htgt : update_vec_dec
                   (add_vec (register_lookup
                               (R_bitvector_64 (gpr_of_Z (uint ra))) s.(sregs))
                      (sign_extend' 64 (zeros' 12 : mword 12))) 0 ('b"0")
                 = ret_pc (register_lookup (R_bitvector_64 (gpr_of_Z (uint ra)))
                             s.(sregs)))
    by apply ret_pc_jalr.
  change (execute (JALR (zeros' 12, Regidx ra, zreg)))
    with (execute_JALR (zeros' 12) (Regidx ra) zreg).
  change zreg with (Regidx cli_rs1).
  rewrite (exec_eff_execute_JALR_ret_zca (zeros' 12) ra cli_rs1 s Hra
             ltac:(vm_compute; reflexivity) Hzic Hzca
             ltac:(rewrite Htgt; apply ret_pc_aligned)).
  rewrite Htgt. reflexivity.
Qed.

(* ====================================================================== *)
(** ** 1e. THE SUCCESSOR REGISTER FRAME FOR A NO-LINK JUMP

    [WkEntryNew.jal_sexec_facts] without the link write: the successor tower
    is the funnel's [minstret_increment] pre-write, the funnel's [nextPC]
    tick, and then the jump's OWN [nextPC] write — and nothing else, because
    [c.ret]'s [rd] is [x0]. *)

Lemma cjr_sexec_facts (s0 : mstate) (b : bool)
    (npc target : SailStdpp.Values.mword 64) :
  let s_exec :=
    set_reg (set_reg (set_reg s0 (R_bool minstret_increment) b) nextPC npc)
      nextPC target in
  register_lookup hart_state (sregs s_exec)
    = register_lookup hart_state s0.(sregs)
  /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b
  /\ mem s_exec = s0.(mem)
  /\ mdev s_exec = s0.(mdev)
  /\ register_lookup nextPC (sregs s_exec) = target.
Proof.
  cbn zeta. split_and!.
  - rewrite (set_lookup_ne hart_state nextPC _ _ ltac:(reg_ne)).
    rewrite (set_lookup_ne hart_state nextPC _ _ ltac:(reg_ne)).
    by rewrite (set_lookup_ne hart_state (R_bool minstret_increment)
                  _ _ ltac:(reg_ne)).
  - rewrite (set_lookup_ne (R_bool minstret_increment) nextPC
               _ _ ltac:(reg_ne)).
    rewrite (set_lookup_ne (R_bool minstret_increment) nextPC
               _ _ ltac:(reg_ne)).
    rewrite sregs_set_reg. apply register_lookup_set.
  - by rewrite !mem_set_reg.
  - by rewrite !mdev_set_reg.
  - rewrite sregs_set_reg. apply register_lookup_set.
Qed.

(* ====================================================================== *)
(** ** 2. THE JAL LEAF ([F_Base], alignment-generic)

    [WpMmodeJal.wp_jal_gpr] under the porting-table swaps, cell-based.  The
    proof is [WkEntryNew]'s inline [jal] funnel block with the concrete
    [pc_e7] / [imm_jal] / [i_jal] / [w_jal] replaced by variables and the
    2-not-4-aligned fetch generalized to [al4] via [WeakLeafRegOnly]. *)

Section leaf_jal.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wwp_jal_leaf (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rd : mword 5) (imm : mword 21)
      (rdv0 npc0 : SailStdpp.Values.mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    uint rd <> 0 ->
    is_aligned_paddr (Physaddr (add_vec pc (sign_extend' 64 imm))) 4 = true ->
    (* the decode, in the two shapes its two consumers ask for *)
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t = Some (JAL (imm, Regidx rd), t)) ->
    (forall rs : Riscv.rv64d_types.regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst = Some (JAL (imm, Regidx rd), dst) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rdv0 -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pc_is (add_vec pc (sign_extend' 64 imm)) -∗
       R_bitvector_64 (gpr_of_Z (uint rd))
         ↦ᵣ (regval_into_reg (add_vec_int pc 4)) -∗
       hart_ws cpu_id ws' -∗
       WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrdnz Halign Hdecf Hagree HDmi Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hrdc #Hbs Hhws Hcont".
    destruct (aligned4_jump_bits _ Halign) as [Hjal0 Hjal1].
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    iAssert (⌜forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)⌝)%I
      as %Hram.
    { iDestruct "Hbs" as "(_ & _ & %Hr & _)". by iPureIntro. }
    iAssert (⌜isRVC (subrange_vec_dec w 15 0) = false⌝)%I as %HnotRVC.
    { iDestruct "Hbs" as "(_ & _ & _ & Hbw)".
      iDestruct "Hbw" as (w0) "[%Hw0 _]". destruct Hw0 as [<- H].
      by iPureIntro. }
    (* the funnel: certificate = nowrite at the fetch-only trace *)
    iApply (wwp_instr pc false (JAL (imm, Regidx rd))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc))
              wQ_pure Hgid Haccpc Hpmp
              (wcert_regonly al4 (fin_to_nat cpu_id) pc)
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false (JAL (imm, Regidx rd))
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %Hws.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    iDestruct (winstr_flat σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hfok.
    iDestruct (winstr_pinned σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hpin.
    destruct Hfok as (_ & _ & w' & [Hww _] & Htext0). subst w'.
    assert (LmisaC : eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ)))
                       ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    (* ---- premise (c): the execute mirror, at the CONFINED state ---- *)
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (JAL (imm, Regidx rd)))
         (set_reg (set_reg (MState (wm_regs σ)
                     (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ))
                     (R_bool minstret_increment) b')
                  nextPC (add_vec_int pc 4))
         = Some (RETIRE_SUCCESS, s_exec, [])
       /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
       /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b'
       /\ dom (mem s_exec) ⊆ wwin pc pc 0).
    { intro b'.
      set (s0c := MState (wm_regs σ)
                    (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ)).
      set (sic := set_reg (set_reg s0c (R_bool minstret_increment) b')
                    nextPC (add_vec_int pc 4)).
      assert (HPCc : register_lookup PC (sregs sic) = pc).
      { unfold sic.
        rewrite (set_lookup_ne PC nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup PC _ b' eq_refl). exact Lpc0. }
      pose proof (exec_eff_execute_JAL_gpr imm rd sic Hrdnz
                    ltac:(rewrite HPCc; exact Hjal0)
                    ltac:(rewrite HPCc; exact Hjal1)) as He.
      destruct (jal_sexec_facts s0c b' (add_vec_int pc 4)
                  (add_vec (register_lookup PC (sregs sic))
                     (sign_extend' 64 imm)) rd
                  (register_lookup nextPC (sregs sic)))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    (* ---- the certificate's precondition ---- *)
    assert (HP : wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc) σ).
    { apply (wP_eff_of_leaf_regonly al4 (fin_to_nat cpu_id) σ (wwin pc pc 0)
               pc w (JAL (imm, Regidx rd)) D dst).
      - exact Hwf.
      - exact (wwin_nonzero pc pc 0 Hram (win0_absurd _)).
      - exact (wwin_pinned σ pc pc 0 Haccpc Hacc0 Hpin (win0_absurd _)).
      - exact Lpc0.
      - exact Lpriv.
      - rewrite Lpmpc. exact Hpmp.
      - exact Lpma.
      - exact Lhtif.
      - exact Lhart.
      - exact LmisaS.
      - exact LmisaC.
      - exact LmIE.
      - exact Lelp.
      - exact Hal2.
      - exact Hal4.
      - exact Hram.
      - exact (wwin_conf_text σ pc pc 0 w Htext0).
      - exact HnotRVC.
      - exact (Hagree (wm_regs σ) Lpriv Lmisa Lsec).
      - exact HDmi.
      - exact Hgood.
      - exact Hdec.
      - reflexivity.
      - exact Hc. }
    (* ---- the run at the FLAT state ---- *)
    set (sif := set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                  nextPC (add_vec_int pc 4)).
    assert (HPCf : register_lookup PC (sregs sif) = pc).
    { unfold sif.
      rewrite (set_lookup_ne PC nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat PC σ b eq_refl). exact Lpc0. }
    assert (Hnpcf : register_lookup nextPC (sregs sif) = add_vec_int pc 4).
    { unfold sif. rewrite sregs_set_reg. apply register_lookup_set. }
    pose proof (exec_eff_execute_JAL_gpr imm rd sif Hrdnz
                  ltac:(rewrite HPCf; exact Hjal0)
                  ltac:(rewrite HPCf; exact Hjal1)) as Hef.
    rewrite HPCf Hnpcf in Hef.
    (* ---- the three register writes the [execute] performs ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm))
            with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec_int pc 4)) with "Hreg Hrdc")
      as "[Hreg Hrdc]".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg sif nextPC (add_vec pc (sign_extend' 64 imm)))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (add_vec_int pc 4))).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (jal_sexec_facts (wflat_st σ) b (add_vec_int pc 4)
                (add_vec pc (sign_extend' 64 imm)) rd (add_vec_int pc 4))
      as (G1 & G2 & G3 & G4 & G5).
    assert (Hdevflat : mdev t = wm_dev σ).
    { rewrite Hdevt0 -(wflat_st_dev σ). exact G4. }
    iMod (hart_ws_update cpu_id (wm_ws σ) ws (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    iEval (rewrite G5) in "Hpc'".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevflat HQl. iFrame. }
    iApply ("Hcont" $! (wm_ws σ') with
              "[%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hrdc Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

End leaf_jal.

(* ====================================================================== *)
(** ** 3. THE c.jr / c.ret LEAF ([F_RVC], alignment-generic)

    [WpMmodeJalr.wp_cret_gpr_zca] under the porting-table swaps, cell-based.
    The compressed decode pack is [WeakLeafTor.wwp_ld8_tor_rvc_leaf]'s (the
    [i0] / [ExecuteAs] pair), the recipe is [WeakLeafTor.wP_eff_of_leaf_rvc]
    at [es_x := []] and the certificate is the ONE-element fetch trace.

    Unlike the SC leaf this needs NO second [mmode_config] split: the two
    facts [exec_execute_JALR_ret_zca] wants beyond M-mode privilege —
    [mseccfg = 0] (for the Zicfilp probe) and [misa.C] (for the Zca probe) —
    are both conjuncts of [WeakFunnel.wcfg_regs], which the funnel hands the
    leaf's callback for free. *)

Section leaf_cjr.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wwp_cjr_rvc_leaf (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (h : SailStdpp.Values.mword 16)
      (ra : mword 5) (i0 : instruction)
      (rav npc0 : SailStdpp.Values.mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp)
      (D D0 : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    uint ra <> 0 ->
    (* the decode, in the two shapes its two consumers ask for *)
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exists i0' : instruction,
         exec (decode_fetch (F_RVC h)) t = Some (i0', t) /\
         is_lpad_instruction i0' = false /\
         (forall s : mstate, exec (execute i0') s
            = Some (ExecuteAs (JALR (zeros' 12, Regidx ra, zreg)), s))) ->
    (forall rs : Riscv.rv64d_types.regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode_compressed h) dst = true ->
    exec (ext_decode_compressed h) dst = Some (i0, dst) ->
    (forall s : mstate, goodb0 D0 (execute i0) s = true) ->
    (forall s : mstate, exec (execute i0) s
       = Some (ExecuteAs (JALR (zeros' 12, Regidx ra, zreg)), s)) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    R_bitvector_64 (gpr_of_Z (uint ra)) ↦ᵣ rav -∗
    winstr_bytes pc (F_RVC h) -∗
    hart_ws cpu_id ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pc_is (ret_pc rav) -∗
       R_bitvector_64 (gpr_of_Z (uint ra)) ↦ᵣ rav -∗
       hart_ws cpu_id ws' -∗
       WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hranz Hdecf Hagree HDmi Hgood Hdec Hgood0 Hexp.
    iIntros "Hmm Hpmpc Hpc Hnpc Hrac #Hbs Hhws Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    iAssert (⌜forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)⌝)%I
      as %Hram.
    { iDestruct "Hbs" as "(_ & _ & %Hr & _)". by iPureIntro. }
    iApply (wwp_instr pc true (JALR (zeros' 12, Regidx ra, zreg))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id))
                 [WEread wak_plain pc (if al4 then 4%N else 2%N)])
              wQ_pure Hgid Haccpc Hpmp
              (wcert_nowrite (fin_to_nat cpu_id) pc
                 [WEread wak_plain pc (if al4 then 4%N else 2%N)]
                 (nowrite_read1 wak_plain pc (if al4 then 4%N else 2%N)))
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc true (JALR (zeros' 12, Regidx ra, zreg))
                (F_RVC h) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %Hws.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    iDestruct (winstr_flat σ pc (F_RVC h) Hwf with "Hlat Hbs") as %Hfok.
    iDestruct (winstr_pinned σ pc (F_RVC h) Hwf with "Hlat Hbs") as %Hpin.
    destruct Hfok as (_ & _ & w & [Hsub HisRVC] & Htext0).
    assert (LmisaC : eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ)))
                       ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    (* the ONE register the funnel does not read: this instruction's source *)
    iDestruct (reg_valid with "Hreg Hrac") as %Lra_a.
    pose proof (eq_trans (eq_sym (reg_at_flat
                  (R_bitvector_64 (gpr_of_Z (uint ra))) σ b eq_refl))
                  Lra_a) as Lra.
    (* ---- premise (c): the execute mirror, at the CONFINED state ---- *)
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (JALR (zeros' 12, Regidx ra, zreg)))
         (set_reg (set_reg (MState (wm_regs σ)
                     (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ))
                     (R_bool minstret_increment) b')
                  nextPC (add_vec_int pc 2))
         = Some (RETIRE_SUCCESS, s_exec, [])
       /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
       /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b'
       /\ dom (mem s_exec) ⊆ wwin pc pc 0).
    { intro b'.
      set (s0c := MState (wm_regs σ)
                    (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ)).
      set (sic := set_reg (set_reg s0c (R_bool minstret_increment) b')
                    nextPC (add_vec_int pc 2)).
      assert (Hprivc : register_lookup cur_privilege (sregs sic) = Machine).
      { unfold sic.
        rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup cur_privilege _ b' eq_refl). exact Lpriv. }
      assert (Hsecc : register_lookup mseccfg (sregs sic) = mword_of_int 0).
      { unfold sic.
        rewrite (set_lookup_ne mseccfg nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup mseccfg _ b' eq_refl). exact Lsec. }
      assert (Hmisac : register_lookup misa (sregs sic) = MISA_C).
      { unfold sic.
        rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup misa _ b' eq_refl). exact Lmisa. }
      assert (HCc : eq_vec (_get_Misa_C (register_lookup misa (sregs sic)))
                      ('b"1") = true)
        by (rewrite Hmisac; vm_compute; reflexivity).
      pose proof (exec_eff_execute_cret_zca ra sic Hranz Hprivc Hsecc HCc)
        as He.
      destruct (cjr_sexec_facts s0c b' (add_vec_int pc 2)
                  (ret_pc (register_lookup (R_bitvector_64 (gpr_of_Z (uint ra)))
                             (sregs sic))))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    (* ---- the certificate's precondition ---- *)
    assert (HP : wP_eff (Some (fin_to_nat cpu_id))
                   [WEread wak_plain pc (if al4 then 4%N else 2%N)] σ).
    { change ([WEread wak_plain pc (if al4 then 4%N else 2%N)])
        with ([WEread wak_plain pc (if al4 then 4%N else 2%N)] ++ (@nil weff)).
      apply (wP_eff_of_leaf_rvc al4 (fin_to_nat cpu_id) σ (wwin pc pc 0)
               pc h w i0 (JALR (zeros' 12, Regidx ra, zreg)) []
               D D0 dst).
      - exact Hwf.
      - exact (wwin_nonzero pc pc 0 Hram (win0_absurd _)).
      - exact (wwin_pinned σ pc pc 0 Haccpc Hacc0 Hpin (win0_absurd _)).
      - exact Lpc0.
      - exact Lpriv.
      - rewrite Lpmpc. exact Hpmp.
      - exact Lpma.
      - exact Lhtif.
      - exact Lhart.
      - exact LmisaS.
      - exact LmisaC.
      - exact LmIE.
      - exact Lelp.
      - exact Hal2.
      - exact Hal4.
      - exact Hram.
      - exact (wwin_conf_text σ pc pc 0 w Htext0).
      - exact Hsub.
      - exact HisRVC.
      - exact (Hagree (wm_regs σ) Lpriv Lmisa Lsec).
      - exact HDmi.
      - exact Hgood.
      - exact Hdec.
      - exact Hgood0.
      - exact Hexp.
      - exact Hc. }
    (* ---- the run at the FLAT state ---- *)
    set (sif := set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                  nextPC (add_vec_int pc 2)).
    assert (Hprivf : register_lookup cur_privilege (sregs sif) = Machine).
    { unfold sif.
      rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat cur_privilege σ b eq_refl). exact Lpriv. }
    assert (Hsecf : register_lookup mseccfg (sregs sif) = mword_of_int 0).
    { unfold sif.
      rewrite (set_lookup_ne mseccfg nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat mseccfg σ b eq_refl). exact Lsec. }
    assert (Hmisaf : register_lookup misa (sregs sif) = MISA_C).
    { unfold sif.
      rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat misa σ b eq_refl). exact Lmisa. }
    assert (HCf : eq_vec (_get_Misa_C (register_lookup misa (sregs sif)))
                    ('b"1") = true)
      by (rewrite Hmisaf; vm_compute; reflexivity).
    assert (Hraf : register_lookup (R_bitvector_64 (gpr_of_Z (uint ra)))
              (sregs sif) = rav).
    { unfold sif.
      rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint ra))) nextPC
                 _ _ ltac:(reg_ne)).
      exact Lra_a. }
    pose proof (exec_eff_execute_cret_zca ra sif Hranz Hprivf Hsecf HCf) as Hef.
    rewrite Hraf in Hef.
    (* ---- the two [nextPC] writes ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ nextPC _ (ret_pc rav) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg sif nextPC (ret_pc rav)).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (cjr_sexec_facts (wflat_st σ) b (add_vec_int pc 2) (ret_pc rav))
      as (G1 & G2 & G3 & G4 & G5).
    assert (Hdevflat : mdev t = wm_dev σ).
    { rewrite Hdevt0 -(wflat_st_dev σ). exact G4. }
    iMod (hart_ws_update cpu_id (wm_ws σ) ws (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    iEval (rewrite G5) in "Hpc'".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevflat HQl. iFrame. }
    iApply ("Hcont" $! (wm_ws σ') with
              "[%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hrac Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

End leaf_cjr.

(* ====================================================================== *)
(** ** 4. Soundness check *)

Print Assumptions exec_eff_cE_zicfilp_false.
Print Assumptions exec_eff_jump_to_zca.
Print Assumptions exec_eff_execute_JALR_ret_zca.
Print Assumptions exec_eff_execute_cret_zca.
Print Assumptions cjr_sexec_facts.
Print Assumptions wwp_jal_leaf.
Print Assumptions wwp_cjr_rvc_leaf.
