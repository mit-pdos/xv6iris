(** * WkEntryNew.v — the weak-tier [_entry] boot chain (M4 batch 4: the
      vertical-slice validation on the M-mode tier)

    The weak twin of [WpEntryNew.wp_entry]: the xv6 kernel's [_entry]
    sequence — 8 instructions at 0x80000000 up to and including the [jal]
    into [start()] — as ONE WP theorem over the WEAK machine, with the SC
    statement's spellings swapped per the porting guide:

      - [kernel_text]                  → [WeakInstr.wkernel_text kbs]
        (+ the pure coverage premise [WkEntryEff.wkb_covers kbs]);
      - [entry_ld_ea ↦ₚ₈{dq} v_stack0] → [vwp_hold (wpt8 entry_ld_ea dq
        v_stack0) ws] paired with this hart's [WeakGhost.hart_ws] cell — the
        view-explicit [↦w₈] spelling — and the continuation binds the
        post-boot view [ws'] with [⌜ws_le ws ws'⌝];
      - everything else — [mmode_config], [pmpcfg_n], [pc_is], [gpr_file],
        [mhartid], the [m_jal] output file — is UNCHANGED (the register/config
        tower transfers verbatim; the [m_*] map definitions are REUSED from
        [WpEntryNew]).

    Composition: the seven register-only instructions go through
    [WeakFunnel.wwp_instr] at [P := wP_eff (fetch trace)] / [Q := wQ_pure]
    with [WeakEff.wcert_nowrite] as the certificate and [WkEntryEff]'s
    [exec_eff] mirrors (trace []) feeding both the funnel's [exec] fact and
    the fetch-arm lemmas' premise (c); the one memory instruction
    ([ld sp, 0x208(sp)]) goes through §1's [wwp_ld8_leaf_same] — the
    [WeakLeafLd8] leaf restated for the rd = rs1 register shape (one GPR
    cell), reusing that file's certificate ([wcert_load8_base4]), execute
    lemma ([exec_eff_ld8_at]) and [wP_eff] half ([wP_eff_ld8]) unchanged.

    All four fetch-alignment arms occur in this one function:
    F_Base@4 (auipc, ld, mul), F_RVC@4 (c.lui, c.add), F_Base@2 (csrr, jal),
    F_RVC@2 (c.addi). *)
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
Require Import WeakWord8.
Require Import WeakEffSkel WeakPmpEff WeakTickEff WeakLeafEffCommon.
Require Import WeakFetchEff WeakFetchRvc WeakFetch2.
Require Import WeakFunnel WpDecodeBridge.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import RegFile WpGpr WpMmodeLeafBase.
Require Import WeakLeafWin.
Require Import WeakLeafEff8 WeakLeafLd8.
Require Import ExecCommon WpDecode WpAuipc WpMmodeJal WpMmodeMul.
Require Import WpGprCsrrCommon WpGprCsrrA.
Require Import CodeEntry CodeEntryAux WpEntryNew KernelText.
Require Import KernelDecode04 KernelDecode07 KernelDecode10 KernelDecode11 KernelDecode12 KernelDecode26 KernelDecode27.
Require Import WkEntryEff.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.

Import SailStdpp.Values.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 0. The JAL successor register frame

    [WeakLeafWin.load_sexec_facts]'s twin for the JAL successor, whose tower
    carries a SECOND [nextPC] write (the jump target) before the link-register
    write. *)

Lemma jal_sexec_facts (s0 : mstate) (b : bool)
    (npc target : SailStdpp.Values.mword 64) (rd : mword 5)
    (link : SailStdpp.Values.mword 64) :
  let s_exec :=
    set_reg (set_reg (set_reg (set_reg s0 (R_bool minstret_increment) b)
                        nextPC npc)
                     nextPC target)
      (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg link) in
  register_lookup hart_state (sregs s_exec)
    = register_lookup hart_state s0.(sregs)
  /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b
  /\ mem s_exec = s0.(mem)
  /\ mdev s_exec = s0.(mdev)
  /\ register_lookup nextPC (sregs s_exec) = target.
Proof.
  cbn zeta. split_and!.
  - rewrite (set_lookup_ne hart_state (R_bitvector_64 (gpr_of_Z (uint rd)))
               _ _ ltac:(reg_ne)).
    rewrite (set_lookup_ne hart_state nextPC _ _ ltac:(reg_ne)).
    rewrite (set_lookup_ne hart_state nextPC _ _ ltac:(reg_ne)).
    by rewrite (set_lookup_ne hart_state (R_bool minstret_increment)
                  _ _ ltac:(reg_ne)).
  - rewrite (set_lookup_ne (R_bool minstret_increment)
               (R_bitvector_64 (gpr_of_Z (uint rd))) _ _ ltac:(reg_ne)).
    rewrite (set_lookup_ne (R_bool minstret_increment) nextPC
               _ _ ltac:(reg_ne)).
    rewrite (set_lookup_ne (R_bool minstret_increment) nextPC
               _ _ ltac:(reg_ne)).
    rewrite sregs_set_reg. apply register_lookup_set.
  - by rewrite !mem_set_reg.
  - by rewrite !mdev_set_reg.
  - rewrite (set_lookup_ne nextPC (R_bitvector_64 (gpr_of_Z (uint rd)))
               _ _ ltac:(reg_ne)).
    rewrite sregs_set_reg. apply register_lookup_set.
Qed.

(* ====================================================================== *)
(** ** 1. THE rd = rs1 LOAD LEAF

    [WeakLeafLd8.wwp_ld8_leaf] takes SEPARATE [rs1]/[rd] register cells, so
    it cannot run [_entry]'s [ld sp, 0x208(sp)] (base = destination = sp).
    This is the SAME leaf — same certificate [wcert_load8_base4], same
    execute lemma [exec_eff_ld8_at], same [wP_eff] half [wP_eff_ld8], same
    window — with the register-cell plumbing collapsed to ONE cell that is
    read as the base and then overwritten with the loaded value. *)

Section leaf_same.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Lemma wwp_ld8_leaf_same
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rsd : mword 5) (imm : mword 12)
      (ea : Arch.pa) (v : bv 64) (dqv : dfrac) (q : Qp)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (rs1v npc0 : SailStdpp.Values.mword 64)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_all_off pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    uint rsd <> 0 ->
    add_vec rs1v (sign_extend' 64 imm) = ea ->
    (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add ea j)) ->
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t
         = Some (LOAD (imm, Regidx rsd, Regidx rsd, false, 8), t)) ->
    (forall rs : Riscv.rv64d_types.regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (LOAD (imm, Regidx rsd, Regidx rsd, false, 8), dst) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    R_bitvector_64 (gpr_of_Z (uint rsd)) ↦ᵣ rs1v -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    vwp_hold (wpt8 ea dqv v) ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pc_is (add_vec_int pc 4) -∗
       R_bitvector_64 (gpr_of_Z (uint rsd)) ↦ᵣ (regval_into_reg v) -∗
       hart_ws cpu_id ws' -∗
       vwp_hold (wpt8 ea dqv v) ws' -∗
       WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hal4 Hrsdnz Hea Hram8 Hdecf Hagree HDmi Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hrsdc #Hbs Hhws Hpt Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    iAssert (⌜isRVC (subrange_vec_dec w 15 0) = false⌝)%I as %HnotRVC.
    { iDestruct "Hbs" as "(_ & _ & _ & Hbw)".
      iDestruct "Hbw" as (w0) "[%Hw0 _]". destruct Hw0 as [<- H].
      by iPureIntro. }
    iApply (wwp_instr pc false (LOAD (imm, Regidx rsd, Regidx rsd, false, 8))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id))
                 ([WEread wak_plain pc 4] ++ [WEread wak_plain ea 8]))
              (wQ_load_w 8 ea) Hgid Haccpc (pmp_all_off_allows_all _ Hpmp)
              (wcert_load8_base4 (fin_to_nat cpu_id) pc wak_plain ea eq_refl)
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false
                (LOAD (imm, Regidx rsd, Regidx rsd, false, 8))
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %->.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    (* the ONE register the funnel does not read: this instruction's base *)
    iDestruct (reg_valid with "Hreg Hrsdc") as %Lrsd_a.
    pose proof (eq_trans (eq_sym (reg_at_flat
                  (R_bitvector_64 (gpr_of_Z (uint rsd))) σ b eq_refl))
                  Lrsd_a)   as Lrsd.
    assert (Hea_σ : add_vec (if Z.eqb (uint rsd) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsd)))
                            (wm_regs σ)) (sign_extend' 64 imm) = ea).
    { rewrite (proj2 (Z.eqb_neq (uint rsd) 0) Hrsdnz) Lrsd. exact Hea. }
    assert (Hag_σ : forall r, D r = true ->
              register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)).
    { apply Hagree; [exact Lpriv | exact Lmisa | exact Lsec]. }
    (* ---- the certificate's precondition ---- *)
    iDestruct (wP_eff_ld8 (fin_to_nat cpu_id) σ pc w rsd rsd imm ea v dqv D dst
                 Hwf Lpc0 Lpriv ltac:(rewrite Lpmpc; exact Hpmp) Lpma
                 Lhtif Lhart LmisaS LmIE Lmprv Lpmm Lelp Hal4 HnotRVC Hrsdnz
                 Hea_σ Hram8 Hag_σ HDmi Hgood Hdec with "Hlat Hbs Hpt") as %HP.
    (* ---- the flat facts: the data doubleword ---- *)
    iDestruct (wwp_ld8 σ ea dqv v Hwf with "Hlat Hpt") as %[_ Hflat8].
    iDestruct (wpt8_align with "Hpt") as %Halea.
    (* ---- the run, at the FLAT state: the SC [execute] fact ---- *)
    pose proof (exec_eff_ld8_at (wflat_st σ) b pc rsd rsd imm ea v Hrsdnz Lpriv
                  Lmprv Lpmm ltac:(rewrite Lpmpc; exact Hpmp) Lpma Lhtif Hea_σ
                  Halea Hram8 Hflat8) as Hexf.
    (* ---- the two register writes the [execute] performs ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rsd))) _
            (regval_into_reg v) with "Hreg Hrsdc") as "[Hreg Hrsdc]".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4))
                     (R_bitvector_64 (gpr_of_Z (uint rsd)))
                     (regval_into_reg v)).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hexf)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    assert (Hdevt : mdev t = wm_dev σ).
    { rewrite Hdevt0 -(wflat_st_dev σ).
      exact (proj1 (proj2 (proj2 (proj2 (load_sexec_facts (wflat_st σ) b
                (add_vec_int pc 4) rsd (regval_into_reg v)))))). }
    pose proof Hpost as Hpost0.
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' & Hbnd').
    destruct HQ as (HQi & HQl & HQv).
    iMod (hart_ws_update cpu_id (wm_ws σ) (wm_ws σ) (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    pose proof (proj2 (proj2 (proj2 (proj2 (load_sexec_facts (wflat_st σ) b
             (add_vec_int pc 4) rsd (regval_into_reg v)))))) as HnpcR1.
    iEval (rewrite HnpcR1) in "Hpc'". clear HnpcR1.
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevt HQl. iFrame. }
    iApply ("Hcont" $! (wm_ws σ') with
              "[%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hrsdc Hhws [Hpt]").
    - exact Hwsle.
    - iApply (wwp_ld8_carry σ σ' t ea dqv v with "Hpt"). exact Hpost0.
  Qed.

End leaf_same.

(* ====================================================================== *)
(** ** 2. Small helpers for the chain *)

(** The data half of a text-only window is empty:
    [WeakLeafEffCommon.win0_absurd] (hoisted). *)

(** RAM facts for an 8-byte window at a concrete address. *)
Ltac ram_win8 :=
  let j := fresh "j" in let Hj := fresh "Hj" in
  intros j Hj;
  destruct j as [|[|[|[|[|[|[|[|]]]]]]]];
  [ram_lit|ram_lit|ram_lit|ram_lit|ram_lit|ram_lit|ram_lit|ram_lit
  |exfalso; lia].

(* ====================================================================== *)
(** ** 3. THE THEOREM: the whole weak [_entry] chain, one Qed.

    Statement = [WpEntryNew.wp_entry] with the porting guide's spellings
    swapped (see the file header); the output register file [m_jal] and every
    register-side resource are IDENTICAL. *)

Section entry.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wwp_entry
      (m : regfile) (v_stack0 : bv 64)
      (mhartid_in : SailStdpp.Values.mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (kbs : _)
      (ws : wstate) (dq : dfrac) :
    gen_id = 0%nat ->
    pmp_all_off pmpcfg0 ->
    wkb_covers kbs ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc_e0 -∗
    gpr_file m -∗
    mhartid ↦ᵣ mhartid_in -∗
    hart_ws cpu_id ws -∗
    vwp_hold (wpt8 entry_ld_ea dq v_stack0) ws -∗
    wkernel_text kbs -∗
    ( ∀ ws' : wstate,
      ⌜ws_le ws ws'⌝ -∗
      mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is pc_start -∗
      gpr_file (m_jal m v_stack0 mhartid_in) -∗
      mhartid ↦ᵣ mhartid_in -∗
      hart_ws cpu_id ws' -∗
      vwp_hold (wpt8 entry_ld_ea dq v_stack0) ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hcov.
    iIntros "Hmm Hpmpc [Hpc Hnpc] Hfile Hmh Hhws Hpt #Htext Hcont".

    (* ================= 1. AUIPC @ pc_e0 (F_Base, 4-aligned) ============ *)
    assert (Hal2_0 : is_aligned_vaddr (Virtaddr pc_e0) 2 = true)
      by (vm_compute; reflexivity).
    assert (Hal4_0 : is_aligned_vaddr (Virtaddr pc_e0) 4 = true)
      by (vm_compute; reflexivity).
    assert (Hacc_0 : acc_wf pc_e0 4)
      by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hacc0_0 : acc_wf pc_e0 0)
      by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_0 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc_e0 j))
      by ram_win.
    assert (Hrd_0 : uint i_auipc <> 0) by (vm_compute; discriminate).
    iAssert (winstr_bytes pc_e0 (F_Base w_auipc)) as "#Hbs0".
    { iApply (winstr_bytes_of_text kbs pc_e0 (F_Base w_auipc) w_auipc Hal2_0
                Hacc_0 Hram_0 (conj eq_refl nrvc_e0) with "Htext").
      iPureIntro.
      exact (wkb_window kbs (KernelSyms._entry + 0x0) w_auipc Hcov kb_e0). }
    iAssert (winstr pc_e0 false (UTYPE (imm_auipc, Regidx i_auipc, AUIPC)))
      as "#Hin0".
    { iApply (winstr_intro pc_e0 false (UTYPE (imm_auipc, Regidx i_auipc, AUIPC))
                (F_Base w_auipc) lpad_e0 eq_refl
                (fun t _ _ _ Hm Hc => kd_0000a117 t Hm Hc) with "Hbs0"). }
    iApply (wwp_instr pc_e0 false (UTYPE (imm_auipc, Regidx i_auipc, AUIPC))
              pmpcfg0 (dq := DfracOwn 1)
              (wP_eff (Some (fin_to_nat cpu_id)) [WEread wak_plain pc_e0 4])
              wQ_pure Hgid Hacc_0 (pmp_all_off_allows_all _ Hpmp)
              (wcert_nowrite (fin_to_nat cpu_id) pc_e0
                 [WEread wak_plain pc_e0 4] (nowrite_read1 wak_plain pc_e0 4))
              with "Hmm Hpmpc Hpc Hin0").
    rewrite /wwp_cb. iIntros (σ1 b1) "%Lpc1 %Hcfg1 Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd1 & %Hwf1 & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ1) ws with "Hwsauth Hhws") as %Hws1.
    destruct Hcfg1 as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                       LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    iDestruct (winstr_flat σ1 pc_e0 (F_Base w_auipc) Hwf1 with "Hlat Hbs0")
      as %Hfok.
    iDestruct (winstr_pinned σ1 pc_e0 (F_Base w_auipc) Hwf1 with "Hlat Hbs0")
      as %Hpin.
    destruct Hfok as (_ & _ & w' & [Hww _] & Htext0). subst w'.
    (* premise (c) of the fetch-arm lemma, off the mirror *)
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (UTYPE (imm_auipc, Regidx i_auipc, AUIPC)))
         (set_reg (set_reg (MState (wm_regs σ1)
                     (wmem_restrict σ1 (wwin pc_e0 pc_e0 0)) (wm_dev σ1))
                     (R_bool minstret_increment) b')
                  nextPC (add_vec_int pc_e0 4))
         = Some (RETIRE_SUCCESS, s_exec, [])
       /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
       /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b'
       /\ dom (mem s_exec) ⊆ wwin pc_e0 pc_e0 0).
    { intro b'.
      set (s0c := MState (wm_regs σ1)
                    (wmem_restrict σ1 (wwin pc_e0 pc_e0 0)) (wm_dev σ1)).
      pose proof (exec_eff_execute_UTYPE_AUIPC_gpr i_auipc imm_auipc
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc_e0 4))) as He.
      replace (Z.eqb (uint i_auipc) 0) with false in He
        by (vm_compute; reflexivity).
      destruct (load_sexec_facts s0c b' (add_vec_int pc_e0 4) i_auipc
                  (regval_into_reg
                     (add_vec (register_lookup PC (sregs
                        (set_reg (set_reg s0c (R_bool minstret_increment) b')
                           nextPC (add_vec_int pc_e0 4))))
                        (auipc_off imm_auipc))))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    assert (HP : wP_eff (Some (fin_to_nat cpu_id)) [WEread wak_plain pc_e0 4] σ1).
    { change ([WEread wak_plain pc_e0 4])
        with ([WEread wak_plain pc_e0 4] ++ []).
      apply (wP_eff_of_leaf_base (fin_to_nat cpu_id) σ1 (wwin pc_e0 pc_e0 0)
               pc_e0 w_auipc (UTYPE (imm_auipc, Regidx i_auipc, AUIPC)) []
               D_m dstateM).
      - exact Hwf1.
      - exact (wwin_nonzero pc_e0 pc_e0 0 Hram_0 (win0_absurd _)).
      - exact (wwin_pinned σ1 pc_e0 pc_e0 0 Hacc_0 Hacc0_0 Hpin (win0_absurd _)).
      - exact Lpc1.
      - exact Lpriv.
      - rewrite Lpmpc. exact (pmp_all_off_allows_all _ Hpmp).
      - exact Lpma.
      - exact Lhtif.
      - exact Lhart.
      - exact LmisaS.
      - exact LmIE.
      - exact Lelp.
      - exact Hal4_0.
      - exact Hram_0.
      - exact (wwin_conf_text σ1 pc_e0 pc_e0 0 w_auipc Htext0).
      - exact nrvc_e0.
      - exact (agree_m_regs (wm_regs σ1) Lpriv Lsec Lmisa).
      - exact D_m_mi.
      - exact good_e0.
      - exact dec_e0.
      - exact lpad_e0.
      - exact Hc. }
    (* the flat execute fact for the funnel *)
    assert (HPCin1 : register_lookup PC (sregs
              (set_reg (set_reg (wflat_st σ1) (R_bool minstret_increment) b1)
                 nextPC (add_vec_int pc_e0 4))) = pc_e0).
    { rewrite (set_lookup_ne PC nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat PC σ1 b1 eq_refl). exact Lpc1. }
    pose proof (exec_eff_execute_UTYPE_AUIPC_gpr i_auipc imm_auipc
                  (set_reg (set_reg (wflat_st σ1) (R_bool minstret_increment) b1)
                     nextPC (add_vec_int pc_e0 4))) as Hef.
    replace (Z.eqb (uint i_auipc) 0) with false in Hef
      by (vm_compute; reflexivity).
    rewrite HPCin1 in Hef.
    change (add_vec pc_e0 (auipc_off imm_auipc)) with entry_sp1 in Hef.
    iMod (reg_update _ nextPC _ (add_vec_int pc_e0 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iDestruct (gpr_file_insert_acc m (Regidx i_auipc)
                 (regval_into_reg entry_sp1) with "Hfile") as "[Hrdc Hfins]".
    iEval (rewrite (gpr_pt_nz i_auipc _ Hrd_0)) in "Hrdc".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint i_auipc))) _
            (regval_into_reg entry_sp1) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
    { iEval (rewrite (gpr_pt_nz i_auipc _ Hrd_0)). iExact "Hrdc". }
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ1)
                        (R_bool minstret_increment) b1)
                      nextPC (add_vec_int pc_e0 4))
                     (R_bitvector_64 (gpr_of_Z (uint i_auipc)))
                     (regval_into_reg entry_sp1)).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick1 σ1' t1) "%Hstep1 %Hdevt1 %Hpost1 %HQ1 Hmm Hpmpc Hpc".
    destruct Hpost1 as (Hregs1 & Hdevs1 & Hmems1 & Himgs1 & Hlogs1 & Hwsle1 &
                        Hwf1' & Hbnd1').
    destruct HQ1 as (HQi1 & HQl1 & HQw1).
    assert (Hdevflat1 : mdev t1 = wm_dev σ1).
    { rewrite Hdevt1 -(wflat_st_dev σ1).
      exact (proj1 (proj2 (proj2 (proj2 (load_sexec_facts (wflat_st σ1) b1
               (add_vec_int pc_e0 4) i_auipc (regval_into_reg entry_sp1)))))). }
    iMod (hart_ws_update cpu_id (wm_ws σ1) ws (wm_ws σ1')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    pose proof (proj2 (proj2 (proj2 (proj2 (load_sexec_facts (wflat_st σ1)
             b1 (add_vec_int pc_e0 4) i_auipc (regval_into_reg entry_sp1)))))) as HnpcR2.
    iEval (rewrite HnpcR2) in "Hpc". clear HnpcR2.
    iSplitL "Hlat"; [by rewrite HQi1 HQl1|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs1 Hdevflat1 HQl1. iFrame. }
    iEval (rewrite Hws1) in "Hpt".
    iDestruct (wpt8_mono entry_ld_ea dq v_stack0 (wm_ws σ1) (wm_ws σ1') Hwsle1
                 with "Hpt") as "Hpt".
    assert (Hle1 : ws_le ws (wm_ws σ1')) by (rewrite Hws1; exact Hwsle1).
    iEval (change (<[Regidx i_auipc := regval_into_reg entry_sp1]> m)
             with (m_auipc m)) in "Hfile".
    iEval (rewrite pc_e0_e1) in "Hpc". iEval (rewrite pc_e0_e1) in "Hnpc".

    (* ================= 2. LOAD @ pc_e1: ld sp, 0x208(sp) =============== *)
    assert (Hal2_1 : is_aligned_vaddr (Virtaddr pc_e1) 2 = true)
      by (vm_compute; reflexivity).
    assert (Hal4_1 : is_aligned_vaddr (Virtaddr pc_e1) 4 = true)
      by (vm_compute; reflexivity).
    assert (Hacc_1 : acc_wf pc_e1 4)
      by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_1 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc_e1 j))
      by ram_win.
    assert (Hram8_1 : forall j : nat, (j < 8)%nat ->
              addr_is_ram (pa_add entry_ld_ea j))
      by ram_win8.
    assert (Hrd_1 : uint i_ld <> 0) by (vm_compute; discriminate).
    iAssert (winstr_bytes pc_e1 (F_Base w_ld)) as "#Hbs1".
    { iApply (winstr_bytes_of_text kbs pc_e1 (F_Base w_ld) w_ld Hal2_1
                Hacc_1 Hram_1 (conj eq_refl nrvc_e1) with "Htext").
      iPureIntro.
      exact (wkb_window kbs (KernelSyms._entry + 0x4) w_ld Hcov kb_e1). }
    assert (HEsp : m_auipc m !!! Regidx i_ld = entry_sp1).
    { unfold m_auipc. rewrite reg_ld_auipc. rewrite upd_eq. reflexivity. }
    assert (Hea1 : add_vec (m_auipc m !!! Regidx i_ld) (sign_extend' 64 imm_ld)
                   = entry_ld_ea).
    { rewrite HEsp. reflexivity. }
    iDestruct (gpr_file_insert_acc (m_auipc m) (Regidx i_ld)
                 (regval_into_reg v_stack0) with "Hfile") as "[Hspc Hfins]".
    iEval (rewrite (gpr_pt_nz i_ld _ Hrd_1)) in "Hspc".
    iApply (wwp_ld8_leaf_same pc_e1 w_ld i_ld imm_ld entry_ld_ea v_stack0 dq
              1%Qp pmpcfg0 (m_auipc m !!! Regidx i_ld) pc_e1 D_m dstateM
              (wm_ws σ1')
              Hgid Hpmp Hal4_1 Hrd_1 Hea1 Hram8_1
              (fun t _ _ _ Hm Hc => kd_20813103 t Hm Hc)
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi good_e1 dec_e1
              with "Hmm Hpmpc Hpc Hnpc Hspc Hbs1 Hhws Hpt").
    iIntros (ws2) "%Hwsle2 Hmm Hpmpc [Hpc Hnpc] Hspc Hhws Hpt".
    iDestruct ("Hfins" with "[Hspc]") as "Hfile".
    { iEval (rewrite (gpr_pt_nz i_ld _ Hrd_1)). iExact "Hspc". }
    iEval (change (<[Regidx i_ld := regval_into_reg v_stack0]> (m_auipc m))
             with (m_ld m v_stack0)) in "Hfile".
    assert (Hle2 : ws_le ws ws2) by (etransitivity; [exact Hle1|exact Hwsle2]).
    iEval (rewrite pc_e1_e2) in "Hpc". iEval (rewrite pc_e1_e2) in "Hnpc".

    (* ================= 3. C.LUI @ pc_e2 (F_RVC, 4-aligned) ============= *)
    assert (Hal2_2 : is_aligned_vaddr (Virtaddr pc_e2) 2 = true)
      by (vm_compute; reflexivity).
    assert (Hal4_2 : is_aligned_vaddr (Virtaddr pc_e2) 4 = true)
      by (vm_compute; reflexivity).
    assert (Hacc_2 : acc_wf pc_e2 4)
      by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hacc0_2 : acc_wf pc_e2 0)
      by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_2 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc_e2 j))
      by ram_win.
    assert (Hrd_2 : uint (regidx_bits rd_clui) <> 0) by (vm_compute; discriminate).
    iAssert (winstr_bytes pc_e2 (F_RVC h_lui)) as "#Hbs2".
    { iApply (winstr_bytes_of_text kbs pc_e2 (F_RVC h_lui) w_e2 Hal2_2 Hacc_2
                Hram_2 (conj sub_e2 rvc_e2) with "Htext").
      iPureIntro.
      exact (wkb_window kbs (KernelSyms._entry + 0x8) w_e2 Hcov kb_e2). }
    iAssert (winstr pc_e2 true (UTYPE (sign_extend' 20 imm_clui, rd_clui, LUI)))
      as "#Hin2".
    { iApply (winstr_intro pc_e2 true
                (UTYPE (sign_extend' 20 imm_clui, rd_clui, LUI))
                (F_RVC h_lui) lpad_e2 eq_refl
                (fun t _ HC _ _ _ =>
                   ex_intro _ (C_LUI (imm_clui, rd_clui))
                     (conj (kd_6505 t HC)
                        (conj lpad_i0_e2 (exec_execute_C_LUI imm_clui rd_clui))))
                with "Hbs2"). }
    iApply (wwp_instr pc_e2 true (UTYPE (sign_extend' 20 imm_clui, rd_clui, LUI))
              pmpcfg0 (dq := DfracOwn 1)
              (wP_eff (Some (fin_to_nat cpu_id)) [WEread wak_plain pc_e2 4])
              wQ_pure Hgid Hacc_2 (pmp_all_off_allows_all _ Hpmp)
              (wcert_nowrite (fin_to_nat cpu_id) pc_e2
                 [WEread wak_plain pc_e2 4] (nowrite_read1 wak_plain pc_e2 4))
              with "Hmm Hpmpc Hpc Hin2").
    rewrite /wwp_cb. iIntros (s3 b3) "%Lpc3 %Hcfg3 Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd3 & %Hwf3 & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws s3) ws2 with "Hwsauth Hhws") as %Hws3.
    destruct Hcfg3 as (Lpriv3 & Lhart3 & Lmisa3 & Lsec3 & Lpmpc3 & Lpma3 &
                       Lhtif3 & LmisaS3 & LmIE3 & Lmprv3 & Lpmm3 & Lelp3).
    iDestruct (winstr_flat s3 pc_e2 (F_RVC h_lui) Hwf3 with "Hlat Hbs2")
      as %Hfok3.
    iDestruct (winstr_pinned s3 pc_e2 (F_RVC h_lui) Hwf3 with "Hlat Hbs2")
      as %Hpin3.
    destruct Hfok3 as (_ & _ & w3 & [Hsub3 Hrvc3] & Htext3).
    assert (Hc3 : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (UTYPE (sign_extend' 20 imm_clui, rd_clui, LUI)))
         (set_reg (set_reg (MState (wm_regs s3)
                     (wmem_restrict s3 (wwin pc_e2 pc_e2 0)) (wm_dev s3))
                     (R_bool minstret_increment) b')
                  nextPC (add_vec_int pc_e2 2))
         = Some (RETIRE_SUCCESS, s_exec, [])
       /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
       /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b'
       /\ dom (mem s_exec) ⊆ wwin pc_e2 pc_e2 0).
    { intro b'.
      set (s0c := MState (wm_regs s3)
                    (wmem_restrict s3 (wwin pc_e2 pc_e2 0)) (wm_dev s3)).
      pose proof (exec_eff_execute_UTYPE_LUI_gpr (regidx_bits rd_clui)
                    (sign_extend' 20 imm_clui)
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc_e2 2))) as He.
      replace (Z.eqb (uint (regidx_bits rd_clui)) 0) with false in He
        by (vm_compute; reflexivity).
      destruct (load_sexec_facts s0c b' (add_vec_int pc_e2 2)
                  (regidx_bits rd_clui)
                  (regval_into_reg (luival (sign_extend' 20 imm_clui))))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart3.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    assert (HP3 : wP_eff (Some (fin_to_nat cpu_id)) [WEread wak_plain pc_e2 4] s3).
    { change ([WEread wak_plain pc_e2 4])
        with ([WEread wak_plain pc_e2 4] ++ []).
      apply (wP_eff_of_leaf_rvc4 (fin_to_nat cpu_id) s3 (wwin pc_e2 pc_e2 0)
               pc_e2 h_lui w3 (C_LUI (imm_clui, rd_clui))
               (UTYPE (sign_extend' 20 imm_clui, rd_clui, LUI)) []
               D_m D_none dstateM).
      - exact Hwf3.
      - exact (wwin_nonzero pc_e2 pc_e2 0 Hram_2 (win0_absurd _)).
      - exact (wwin_pinned s3 pc_e2 pc_e2 0 Hacc_2 Hacc0_2 Hpin3 (win0_absurd _)).
      - exact Lpc3.
      - exact Lpriv3.
      - rewrite Lpmpc3. exact (pmp_all_off_allows_all _ Hpmp).
      - exact Lpma3.
      - exact Lhtif3.
      - exact Lhart3.
      - exact LmisaS3.
      - exact (misaC_of_val _ Lmisa3).
      - exact LmIE3.
      - exact Lelp3.
      - exact Hal4_2.
      - exact Hram_2.
      - exact (wwin_conf_text s3 pc_e2 pc_e2 0 w3 Htext3).
      - exact Hsub3.
      - exact Hrvc3.
      - exact (agree_m_regs (wm_regs s3) Lpriv3 Lsec3 Lmisa3).
      - exact D_m_mi.
      - exact good_e2.
      - exact dec_e2.
      - exact good_exp_e2.
      - exact (exec_execute_C_LUI imm_clui rd_clui).
      - exact Hc3. }
    pose proof (exec_eff_execute_UTYPE_LUI_gpr (regidx_bits rd_clui)
                  (sign_extend' 20 imm_clui)
                  (set_reg (set_reg (wflat_st s3) (R_bool minstret_increment) b3)
                     nextPC (add_vec_int pc_e2 2))) as Hef3.
    replace (Z.eqb (uint (regidx_bits rd_clui)) 0) with false in Hef3
      by (vm_compute; reflexivity).
    iMod (reg_update _ nextPC _ (add_vec_int pc_e2 2) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iDestruct (gpr_file_insert_acc (m_ld m v_stack0) (Regidx (regidx_bits rd_clui))
                 (regval_into_reg (luival (sign_extend' 20 imm_clui)))
                 with "Hfile") as "[Hrdc3 Hfins3]".
    iEval (rewrite (gpr_pt_nz (regidx_bits rd_clui) _ Hrd_2)) in "Hrdc3".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint (regidx_bits rd_clui)))) _
            (regval_into_reg (luival (sign_extend' 20 imm_clui)))
            with "Hreg Hrdc3") as "[Hreg Hrdc3]".
    iDestruct ("Hfins3" with "[Hrdc3]") as "Hfile".
    { iEval (rewrite (gpr_pt_nz (regidx_bits rd_clui) _ Hrd_2)).
      iExact "Hrdc3". }
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP3|].
    iExists (set_reg (set_reg (set_reg (wflat_st s3)
                        (R_bool minstret_increment) b3)
                      nextPC (add_vec_int pc_e2 2))
                     (R_bitvector_64 (gpr_of_Z (uint (regidx_bits rd_clui))))
                     (regval_into_reg (luival (sign_extend' 20 imm_clui)))).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef3)|].
    iFrame "Hreg".
    iNext. iIntros (tick3 s3' t3) "%Hstep3 %Hdevt3 %Hpost3 %HQ3 Hmm Hpmpc Hpc".
    destruct Hpost3 as (Hregs3 & Hdevs3 & Hmems3 & Himgs3 & Hlogs3 & Hwsle3 &
                        Hwf3' & Hbnd3').
    destruct HQ3 as (HQi3 & HQl3 & HQw3).
    assert (Hdevflat3 : mdev t3 = wm_dev s3).
    { rewrite Hdevt3 -(wflat_st_dev s3).
      exact (proj1 (proj2 (proj2 (proj2 (load_sexec_facts (wflat_st s3) b3
               (add_vec_int pc_e2 2) (regidx_bits rd_clui)
               (regval_into_reg (luival (sign_extend' 20 imm_clui)))))))). }
    iMod (hart_ws_update cpu_id (wm_ws s3) ws2 (wm_ws s3')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    pose proof (proj2 (proj2 (proj2 (proj2 (load_sexec_facts (wflat_st s3)
             b3 (add_vec_int pc_e2 2) (regidx_bits rd_clui)
             (regval_into_reg (luival (sign_extend' 20 imm_clui)))))))) as HnpcR3.
    iEval (rewrite HnpcR3) in "Hpc". clear HnpcR3.
    iSplitL "Hlat"; [by rewrite HQi3 HQl3|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs3 Hdevflat3 HQl3. iFrame. }
    iEval (rewrite Hws3) in "Hpt".
    iDestruct (wpt8_mono entry_ld_ea dq v_stack0 (wm_ws s3) (wm_ws s3') Hwsle3
                 with "Hpt") as "Hpt".
    assert (Hle3 : ws_le ws (wm_ws s3')).
    { etransitivity; [exact Hle2|]. rewrite Hws3. exact Hwsle3. }
    iEval (change (<[Regidx (regidx_bits rd_clui) :=
                      regval_into_reg (luival (sign_extend' 20 imm_clui))]>
                     (m_ld m v_stack0))
             with (m_clui m v_stack0)) in "Hfile".
    iEval (rewrite pc_e2_e3) in "Hpc". iEval (rewrite pc_e2_e3) in "Hnpc".

    (* ================= 4. CSRRS @ pc_e3 (F_Base, 2-aligned) ============ *)
    assert (Hal2_3 : is_aligned_vaddr (Virtaddr pc_e3) 2 = true)
      by (vm_compute; reflexivity).
    assert (Hal4_3 : is_aligned_vaddr (Virtaddr pc_e3) 4 = false)
      by (vm_compute; reflexivity).
    assert (Hacc_3 : acc_wf pc_e3 4)
      by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hacc0_3 : acc_wf pc_e3 0)
      by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_3 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc_e3 j))
      by ram_win.
    assert (Hrd_3 : uint i_rd_csrr <> 0) by (vm_compute; discriminate).
    iAssert (winstr_bytes pc_e3 (F_Base w_csrr)) as "#Hbs3".
    { iApply (winstr_bytes_of_text kbs pc_e3 (F_Base w_csrr) w_csrr Hal2_3
                Hacc_3 Hram_3 (conj eq_refl nrvc_e3) with "Htext").
      iPureIntro.
      exact (wkb_window kbs (KernelSyms._entry + 0xa) w_csrr Hcov kb_e3). }
    iAssert (winstr pc_e3 false
               (CSRReg (csr_csrr, zreg, Regidx i_rd_csrr, CSRRS))) as "#Hin3".
    { iApply (winstr_intro pc_e3 false
                (CSRReg (csr_csrr, zreg, Regidx i_rd_csrr, CSRRS))
                (F_Base w_csrr) lpad_e3 eq_refl
                (fun t _ _ _ Hm Hc => kd_f14025f3 t Hm Hc) with "Hbs3"). }
    iApply (wwp_instr pc_e3 false
              (CSRReg (csr_csrr, zreg, Regidx i_rd_csrr, CSRRS))
              pmpcfg0 (dq := DfracOwn 1)
              (wP_eff (Some (fin_to_nat cpu_id))
                 [WEread wak_plain pc_e3 2;
                  WEread wak_plain (add_vec_int pc_e3 2) 2])
              wQ_pure Hgid Hacc_3 (pmp_all_off_allows_all _ Hpmp)
              (wcert_nowrite (fin_to_nat cpu_id) pc_e3
                 [WEread wak_plain pc_e3 2;
                  WEread wak_plain (add_vec_int pc_e3 2) 2]
                 (nowrite_fetch2 pc_e3))
              with "Hmm Hpmpc Hpc Hin3").
    rewrite /wwp_cb. iIntros (s4 b4) "%Lpc4 %Hcfg4 Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd4 & %Hwf4 & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws s4) (wm_ws s3') with "Hwsauth Hhws")
      as %Hws4.
    destruct Hcfg4 as (Lpriv4 & Lhart4 & Lmisa4 & Lsec4 & Lpmpc4 & Lpma4 &
                       Lhtif4 & LmisaS4 & LmIE4 & Lmprv4 & Lpmm4 & Lelp4).
    iDestruct (winstr_flat s4 pc_e3 (F_Base w_csrr) Hwf4 with "Hlat Hbs3")
      as %Hfok4.
    iDestruct (winstr_pinned s4 pc_e3 (F_Base w_csrr) Hwf4 with "Hlat Hbs3")
      as %Hpin4.
    destruct Hfok4 as (_ & _ & w4 & [Hww4 _] & Htext4). subst w4.
    (* the operand register the funnel does not read: mhartid *)
    iDestruct (reg_valid with "Hreg Hmh") as %Lmh4.
    assert (Hc4 : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (CSRReg (csr_csrr, zreg, Regidx i_rd_csrr, CSRRS)))
         (set_reg (set_reg (MState (wm_regs s4)
                     (wmem_restrict s4 (wwin pc_e3 pc_e3 0)) (wm_dev s4))
                     (R_bool minstret_increment) b')
                  nextPC (add_vec_int pc_e3 4))
         = Some (RETIRE_SUCCESS, s_exec, [])
       /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
       /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b'
       /\ dom (mem s_exec) ⊆ wwin pc_e3 pc_e3 0).
    { intro b'.
      set (s0c := MState (wm_regs s4)
                    (wmem_restrict s4 (wwin pc_e3 pc_e3 0)) (wm_dev s4)).
      assert (Hprivc : register_lookup cur_privilege
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc_e3 4))) = Machine).
      { rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup cur_privilege _ b' eq_refl). exact Lpriv4. }
      pose proof (exec_eff_execute_CSRReg_gpr i_rd_csrr
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc_e3 4)) Hrd_3 Hprivc) as He.
      destruct (load_sexec_facts s0c b' (add_vec_int pc_e3 4) i_rd_csrr
                  (regval_into_reg (register_lookup mhartid
                     (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                               nextPC (add_vec_int pc_e3 4))))))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart4.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    assert (HP4 : wP_eff (Some (fin_to_nat cpu_id))
                    [WEread wak_plain pc_e3 2;
                     WEread wak_plain (add_vec_int pc_e3 2) 2] s4).
    { change ([WEread wak_plain pc_e3 2;
               WEread wak_plain (add_vec_int pc_e3 2) 2])
        with ([WEread wak_plain pc_e3 2;
               WEread wak_plain (add_vec_int pc_e3 2) 2] ++ []).
      apply (wP_eff_of_leaf_base2 (fin_to_nat cpu_id) s4 (wwin pc_e3 pc_e3 0)
               pc_e3 w_csrr (CSRReg (csr_csrr, zreg, Regidx i_rd_csrr, CSRRS))
               [] D_m dstateM).
      - exact Hwf4.
      - exact (wwin_nonzero pc_e3 pc_e3 0 Hram_3 (win0_absurd _)).
      - exact (wwin_pinned s4 pc_e3 pc_e3 0 Hacc_3 Hacc0_3 Hpin4 (win0_absurd _)).
      - exact Lpc4.
      - exact Lpriv4.
      - rewrite Lpmpc4. exact (pmp_all_off_allows_all _ Hpmp).
      - exact Lpma4.
      - exact Lhtif4.
      - exact Lhart4.
      - exact LmisaS4.
      - exact (misaC_of_val _ Lmisa4).
      - exact LmIE4.
      - exact Lelp4.
      - exact Hal2_3.
      - exact Hal4_3.
      - exact Hram_3.
      - exact (wwin_conf_text s4 pc_e3 pc_e3 0 w_csrr Htext4).
      - exact nrvc_e3.
      - exact (agree_m_regs (wm_regs s4) Lpriv4 Lsec4 Lmisa4).
      - exact D_m_mi.
      - exact good_e3.
      - exact dec_e3.
      - exact lpad_e3.
      - exact Hc4. }
    assert (Hprivf4 : register_lookup cur_privilege
              (sregs (set_reg (set_reg (wflat_st s4) (R_bool minstret_increment) b4)
                        nextPC (add_vec_int pc_e3 4))) = Machine).
    { rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat cur_privilege s4 b4 eq_refl). exact Lpriv4. }
    assert (Lmh4in : register_lookup mhartid
              (sregs (set_reg (set_reg (wflat_st s4) (R_bool minstret_increment) b4)
                        nextPC (add_vec_int pc_e3 4))) = mhartid_in).
    { rewrite (set_lookup_ne mhartid nextPC _ _ ltac:(reg_ne)). exact Lmh4. }
    pose proof (exec_eff_execute_CSRReg_gpr i_rd_csrr
                  (set_reg (set_reg (wflat_st s4) (R_bool minstret_increment) b4)
                     nextPC (add_vec_int pc_e3 4)) Hrd_3 Hprivf4) as Hef4.
    rewrite Lmh4in in Hef4.
    iMod (reg_update _ nextPC _ (add_vec_int pc_e3 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iDestruct (gpr_file_insert_acc (m_clui m v_stack0) (Regidx i_rd_csrr)
                 (regval_into_reg mhartid_in) with "Hfile") as "[Hrdc4 Hfins4]".
    iEval (rewrite (gpr_pt_nz i_rd_csrr _ Hrd_3)) in "Hrdc4".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint i_rd_csrr))) _
            (regval_into_reg mhartid_in) with "Hreg Hrdc4") as "[Hreg Hrdc4]".
    iDestruct ("Hfins4" with "[Hrdc4]") as "Hfile".
    { iEval (rewrite (gpr_pt_nz i_rd_csrr _ Hrd_3)). iExact "Hrdc4". }
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP4|].
    iExists (set_reg (set_reg (set_reg (wflat_st s4)
                        (R_bool minstret_increment) b4)
                      nextPC (add_vec_int pc_e3 4))
                     (R_bitvector_64 (gpr_of_Z (uint i_rd_csrr)))
                     (regval_into_reg mhartid_in)).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef4)|].
    iFrame "Hreg".
    iNext. iIntros (tick4 s4' t4) "%Hstep4 %Hdevt4 %Hpost4 %HQ4 Hmm Hpmpc Hpc".
    destruct Hpost4 as (Hregs4 & Hdevs4 & Hmems4 & Himgs4 & Hlogs4 & Hwsle4 &
                        Hwf4' & Hbnd4').
    destruct HQ4 as (HQi4 & HQl4 & HQw4).
    assert (Hdevflat4 : mdev t4 = wm_dev s4).
    { rewrite Hdevt4 -(wflat_st_dev s4).
      exact (proj1 (proj2 (proj2 (proj2 (load_sexec_facts (wflat_st s4) b4
               (add_vec_int pc_e3 4) i_rd_csrr (regval_into_reg mhartid_in)))))). }
    iMod (hart_ws_update cpu_id (wm_ws s4) (wm_ws s3') (wm_ws s4')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    pose proof (proj2 (proj2 (proj2 (proj2 (load_sexec_facts (wflat_st s4)
             b4 (add_vec_int pc_e3 4) i_rd_csrr (regval_into_reg mhartid_in)))))) as HnpcR4.
    iEval (rewrite HnpcR4) in "Hpc". clear HnpcR4.
    iSplitL "Hlat"; [by rewrite HQi4 HQl4|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs4 Hdevflat4 HQl4. iFrame. }
    iEval (rewrite Hws4) in "Hpt".
    iDestruct (wpt8_mono entry_ld_ea dq v_stack0 (wm_ws s4) (wm_ws s4') Hwsle4
                 with "Hpt") as "Hpt".
    assert (Hle4 : ws_le ws (wm_ws s4')).
    { etransitivity; [exact Hle3|]. rewrite Hws4. exact Hwsle4. }
    iEval (change (<[Regidx i_rd_csrr := regval_into_reg mhartid_in]>
                     (m_clui m v_stack0))
             with (m_csrr m v_stack0 mhartid_in)) in "Hfile".
    iEval (rewrite pc_e3_e4) in "Hpc". iEval (rewrite pc_e3_e4) in "Hnpc".

    (* ================= 5. C.ADDI @ pc_e4 (F_RVC, 2-aligned) ============ *)
    assert (Hal2_4 : is_aligned_vaddr (Virtaddr pc_e4) 2 = true)
      by (vm_compute; reflexivity).
    assert (Hal4_4 : is_aligned_vaddr (Virtaddr pc_e4) 4 = false)
      by (vm_compute; reflexivity).
    assert (Hacc_4 : acc_wf pc_e4 4)
      by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hacc0_4 : acc_wf pc_e4 0)
      by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_4 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc_e4 j))
      by ram_win.
    assert (Hrd_4 : uint (regidx_bits rsd_caddi) <> 0)
      by (vm_compute; discriminate).
    iAssert (winstr_bytes pc_e4 (F_RVC h_addi)) as "#Hbs4".
    { iApply (winstr_bytes_of_text kbs pc_e4 (F_RVC h_addi) w_e4 Hal2_4 Hacc_4
                Hram_4 (conj sub_e4 rvc_e4) with "Htext").
      iPureIntro.
      exact (wkb_window kbs (KernelSyms._entry + 0xe) w_e4 Hcov kb_e4). }
    iAssert (winstr pc_e4 true
               (ITYPE (sign_extend' 12 imm_caddi, rsd_caddi, rsd_caddi, ADDI)))
      as "#Hin4".
    { iApply (winstr_intro pc_e4 true
                (ITYPE (sign_extend' 12 imm_caddi, rsd_caddi, rsd_caddi, ADDI))
                (F_RVC h_addi) lpad_e4 eq_refl
                (fun t _ HC _ _ _ =>
                   ex_intro _ (C_ADDI (imm_caddi, rsd_caddi))
                     (conj (kd_0585 t HC)
                        (conj lpad_i0_e4
                           (exec_execute_C_ADDI imm_caddi rsd_caddi))))
                with "Hbs4"). }
    iApply (wwp_instr pc_e4 true
              (ITYPE (sign_extend' 12 imm_caddi, rsd_caddi, rsd_caddi, ADDI))
              pmpcfg0 (dq := DfracOwn 1)
              (wP_eff (Some (fin_to_nat cpu_id)) [WEread wak_plain pc_e4 2])
              wQ_pure Hgid Hacc_4 (pmp_all_off_allows_all _ Hpmp)
              (wcert_nowrite (fin_to_nat cpu_id) pc_e4
                 [WEread wak_plain pc_e4 2] (nowrite_read1 wak_plain pc_e4 2))
              with "Hmm Hpmpc Hpc Hin4").
    rewrite /wwp_cb. iIntros (s5 b5) "%Lpc5 %Hcfg5 Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd5 & %Hwf5 & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws s5) (wm_ws s4') with "Hwsauth Hhws")
      as %Hws5.
    destruct Hcfg5 as (Lpriv5 & Lhart5 & Lmisa5 & Lsec5 & Lpmpc5 & Lpma5 &
                       Lhtif5 & LmisaS5 & LmIE5 & Lmprv5 & Lpmm5 & Lelp5).
    iDestruct (winstr_flat s5 pc_e4 (F_RVC h_addi) Hwf5 with "Hlat Hbs4")
      as %Hfok5.
    iDestruct (winstr_pinned s5 pc_e4 (F_RVC h_addi) Hwf5 with "Hlat Hbs4")
      as %Hpin5.
    destruct Hfok5 as (_ & _ & w5 & [Hsub5 Hrvc5] & Htext5).
    assert (Hc5 : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute
                   (ITYPE (sign_extend' 12 imm_caddi, rsd_caddi, rsd_caddi, ADDI)))
         (set_reg (set_reg (MState (wm_regs s5)
                     (wmem_restrict s5 (wwin pc_e4 pc_e4 0)) (wm_dev s5))
                     (R_bool minstret_increment) b')
                  nextPC (add_vec_int pc_e4 2))
         = Some (RETIRE_SUCCESS, s_exec, [])
       /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
       /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b'
       /\ dom (mem s_exec) ⊆ wwin pc_e4 pc_e4 0).
    { intro b'.
      set (s0c := MState (wm_regs s5)
                    (wmem_restrict s5 (wwin pc_e4 pc_e4 0)) (wm_dev s5)).
      pose proof (exec_eff_execute_ITYPE_ADDI_gpr (regidx_bits rsd_caddi)
                    (regidx_bits rsd_caddi) (sign_extend' 12 imm_caddi)
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc_e4 2))) as He.
      replace (Z.eqb (uint (regidx_bits rsd_caddi)) 0) with false in He
        by (vm_compute; reflexivity).
      destruct (load_sexec_facts s0c b' (add_vec_int pc_e4 2)
                  (regidx_bits rsd_caddi)
                  (regval_into_reg (gpr_addi_val (regidx_bits rsd_caddi)
                     (sign_extend' 12 imm_caddi)
                     (set_reg (set_reg s0c (R_bool minstret_increment) b')
                        nextPC (add_vec_int pc_e4 2)))))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart5.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    assert (HP5 : wP_eff (Some (fin_to_nat cpu_id)) [WEread wak_plain pc_e4 2] s5).
    { change ([WEread wak_plain pc_e4 2])
        with ([WEread wak_plain pc_e4 2] ++ []).
      apply (wP_eff_of_leaf_rvc2 (fin_to_nat cpu_id) s5 (wwin pc_e4 pc_e4 0)
               pc_e4 h_addi w5 (C_ADDI (imm_caddi, rsd_caddi))
               (ITYPE (sign_extend' 12 imm_caddi, rsd_caddi, rsd_caddi, ADDI))
               [] D_m D_none dstateM).
      - exact Hwf5.
      - exact (wwin_nonzero pc_e4 pc_e4 0 Hram_4 (win0_absurd _)).
      - exact (wwin_pinned s5 pc_e4 pc_e4 0 Hacc_4 Hacc0_4 Hpin5 (win0_absurd _)).
      - exact Lpc5.
      - exact Lpriv5.
      - rewrite Lpmpc5. exact (pmp_all_off_allows_all _ Hpmp).
      - exact Lpma5.
      - exact Lhtif5.
      - exact Lhart5.
      - exact LmisaS5.
      - exact (misaC_of_val _ Lmisa5).
      - exact LmIE5.
      - exact Lelp5.
      - exact Hal2_4.
      - exact Hal4_4.
      - exact Hram_4.
      - exact (wwin_conf_text s5 pc_e4 pc_e4 0 w5 Htext5).
      - exact Hsub5.
      - exact Hrvc5.
      - exact (agree_m_regs (wm_regs s5) Lpriv5 Lsec5 Lmisa5).
      - exact D_m_mi.
      - exact good_e4.
      - exact dec_e4.
      - exact good_exp_e4.
      - exact (exec_execute_C_ADDI imm_caddi rsd_caddi).
      - exact Hc5. }
    (* the operand cell: a1, read then overwritten *)
    iDestruct (gpr_file_insert_acc (m_csrr m v_stack0 mhartid_in)
                 (Regidx (regidx_bits rsd_caddi))
                 (regval_into_reg
                    (add_vec (m_csrr m v_stack0 mhartid_in
                                !!! Regidx (regidx_bits rsd_caddi))
                       (sign_extend' 64 imm_caddi)))
                 with "Hfile") as "[Hc5c Hfins5]".
    iEval (rewrite (gpr_pt_nz (regidx_bits rsd_caddi) _ Hrd_4)) in "Hc5c".
    iDestruct (reg_valid with "Hreg Hc5c") as %La1_5.
    assert (Hval5 : gpr_addi_val (regidx_bits rsd_caddi)
              (sign_extend' 12 imm_caddi)
              (set_reg (set_reg (wflat_st s5) (R_bool minstret_increment) b5)
                 nextPC (add_vec_int pc_e4 2))
            = add_vec (m_csrr m v_stack0 mhartid_in
                         !!! Regidx (regidx_bits rsd_caddi))
                (sign_extend' 64 imm_caddi)).
    { unfold gpr_addi_val.
      replace (Z.eqb (uint (regidx_bits rsd_caddi)) 0) with false
        by (vm_compute; reflexivity).
      rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint (regidx_bits rsd_caddi))))
                 nextPC _ _ ltac:(reg_ne)).
      rewrite La1_5. rewrite sext6_12_64. reflexivity. }
    pose proof (exec_eff_execute_ITYPE_ADDI_gpr (regidx_bits rsd_caddi)
                  (regidx_bits rsd_caddi) (sign_extend' 12 imm_caddi)
                  (set_reg (set_reg (wflat_st s5) (R_bool minstret_increment) b5)
                     nextPC (add_vec_int pc_e4 2))) as Hef5.
    replace (Z.eqb (uint (regidx_bits rsd_caddi)) 0) with false in Hef5
      by (vm_compute; reflexivity).
    rewrite Hval5 in Hef5.
    iMod (reg_update _ nextPC _ (add_vec_int pc_e4 2) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _
            (R_bitvector_64 (gpr_of_Z (uint (regidx_bits rsd_caddi)))) _
            (regval_into_reg
               (add_vec (m_csrr m v_stack0 mhartid_in
                           !!! Regidx (regidx_bits rsd_caddi))
                  (sign_extend' 64 imm_caddi)))
            with "Hreg Hc5c") as "[Hreg Hc5c]".
    iDestruct ("Hfins5" with "[Hc5c]") as "Hfile".
    { iEval (rewrite (gpr_pt_nz (regidx_bits rsd_caddi) _ Hrd_4)).
      iExact "Hc5c". }
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP5|].
    iExists (set_reg (set_reg (set_reg (wflat_st s5)
                        (R_bool minstret_increment) b5)
                      nextPC (add_vec_int pc_e4 2))
                     (R_bitvector_64 (gpr_of_Z (uint (regidx_bits rsd_caddi))))
                     (regval_into_reg
                        (add_vec (m_csrr m v_stack0 mhartid_in
                                    !!! Regidx (regidx_bits rsd_caddi))
                           (sign_extend' 64 imm_caddi)))).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef5)|].
    iFrame "Hreg".
    iNext. iIntros (tick5 s5' t5) "%Hstep5 %Hdevt5 %Hpost5 %HQ5 Hmm Hpmpc Hpc".
    destruct Hpost5 as (Hregs5 & Hdevs5 & Hmems5 & Himgs5 & Hlogs5 & Hwsle5 &
                        Hwf5' & Hbnd5').
    destruct HQ5 as (HQi5 & HQl5 & HQw5).
    assert (Hdevflat5 : mdev t5 = wm_dev s5).
    { rewrite Hdevt5 -(wflat_st_dev s5).
      exact (proj1 (proj2 (proj2 (proj2 (load_sexec_facts (wflat_st s5) b5
               (add_vec_int pc_e4 2) (regidx_bits rsd_caddi)
               (regval_into_reg
                  (add_vec (m_csrr m v_stack0 mhartid_in
                              !!! Regidx (regidx_bits rsd_caddi))
                     (sign_extend' 64 imm_caddi)))))))). }
    iMod (hart_ws_update cpu_id (wm_ws s5) (wm_ws s4') (wm_ws s5')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    pose proof (proj2 (proj2 (proj2 (proj2 (load_sexec_facts (wflat_st s5)
             b5 (add_vec_int pc_e4 2) (regidx_bits rsd_caddi)
             (regval_into_reg
                (add_vec (m_csrr m v_stack0 mhartid_in
                            !!! Regidx (regidx_bits rsd_caddi))
                   (sign_extend' 64 imm_caddi)))))))) as HnpcR5.
    iEval (rewrite HnpcR5) in "Hpc". clear HnpcR5.
    iSplitL "Hlat"; [by rewrite HQi5 HQl5|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs5 Hdevflat5 HQl5. iFrame. }
    iEval (rewrite Hws5) in "Hpt".
    iDestruct (wpt8_mono entry_ld_ea dq v_stack0 (wm_ws s5) (wm_ws s5') Hwsle5
                 with "Hpt") as "Hpt".
    assert (Hle5 : ws_le ws (wm_ws s5')).
    { etransitivity; [exact Hle4|]. rewrite Hws5. exact Hwsle5. }
    iEval (change (<[Regidx (regidx_bits rsd_caddi) :=
                      regval_into_reg
                        (add_vec (m_csrr m v_stack0 mhartid_in
                                    !!! Regidx (regidx_bits rsd_caddi))
                           (sign_extend' 64 imm_caddi))]>
                     (m_csrr m v_stack0 mhartid_in))
             with (m_caddi m v_stack0 mhartid_in)) in "Hfile".
    iEval (rewrite pc_e4_e5) in "Hpc". iEval (rewrite pc_e4_e5) in "Hnpc".

    (* ================= 6. MUL @ pc_e5 (F_Base, 4-aligned) ============== *)
    assert (Hal2_5 : is_aligned_vaddr (Virtaddr pc_e5) 2 = true)
      by (vm_compute; reflexivity).
    assert (Hal4_5 : is_aligned_vaddr (Virtaddr pc_e5) 4 = true)
      by (vm_compute; reflexivity).
    assert (Hacc_5 : acc_wf pc_e5 4)
      by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hacc0_5 : acc_wf pc_e5 0)
      by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_5 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc_e5 j))
      by ram_win.
    assert (Hrd_5 : uint i_mul_rd <> 0) by (vm_compute; discriminate).
    assert (Hrs2_5 : uint i_mul_rs2 <> 0) by (vm_compute; discriminate).
    iAssert (winstr_bytes pc_e5 (F_Base w_mul)) as "#Hbs5".
    { iApply (winstr_bytes_of_text kbs pc_e5 (F_Base w_mul) w_mul Hal2_5
                Hacc_5 Hram_5 (conj eq_refl nrvc_e5) with "Htext").
      iPureIntro.
      exact (wkb_window kbs (KernelSyms._entry + 0x10) w_mul Hcov kb_e5). }
    iAssert (winstr pc_e5 false
               (MUL (Regidx i_mul_rs2, Regidx i_mul_rs1, Regidx i_mul_rd,
                     mulop_mul))) as "#Hin5".
    { iApply (winstr_intro pc_e5 false
                (MUL (Regidx i_mul_rs2, Regidx i_mul_rs1, Regidx i_mul_rd,
                      mulop_mul))
                (F_Base w_mul) lpad_e5 eq_refl
                (fun t _ _ _ Hm Hc => kd_02b50533 t Hm Hc)
                with "Hbs5"). }
    iApply (wwp_instr pc_e5 false
              (MUL (Regidx i_mul_rs2, Regidx i_mul_rs1, Regidx i_mul_rd,
                    mulop_mul))
              pmpcfg0 (dq := DfracOwn 1)
              (wP_eff (Some (fin_to_nat cpu_id)) [WEread wak_plain pc_e5 4])
              wQ_pure Hgid Hacc_5 (pmp_all_off_allows_all _ Hpmp)
              (wcert_nowrite (fin_to_nat cpu_id) pc_e5
                 [WEread wak_plain pc_e5 4] (nowrite_read1 wak_plain pc_e5 4))
              with "Hmm Hpmpc Hpc Hin5").
    rewrite /wwp_cb. iIntros (s6 b6) "%Lpc6 %Hcfg6 Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd6 & %Hwf6 & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws s6) (wm_ws s5') with "Hwsauth Hhws")
      as %Hws6.
    destruct Hcfg6 as (Lpriv6 & Lhart6 & Lmisa6 & Lsec6 & Lpmpc6 & Lpma6 &
                       Lhtif6 & LmisaS6 & LmIE6 & Lmprv6 & Lpmm6 & Lelp6).
    iDestruct (winstr_flat s6 pc_e5 (F_Base w_mul) Hwf6 with "Hlat Hbs5")
      as %Hfok6.
    iDestruct (winstr_pinned s6 pc_e5 (F_Base w_mul) Hwf6 with "Hlat Hbs5")
      as %Hpin6.
    destruct Hfok6 as (_ & _ & w6 & [Hww6 _] & Htext6). subst w6.
    assert (Hc6 : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (MUL (Regidx i_mul_rs2, Regidx i_mul_rs1,
                               Regidx i_mul_rd, mulop_mul)))
         (set_reg (set_reg (MState (wm_regs s6)
                     (wmem_restrict s6 (wwin pc_e5 pc_e5 0)) (wm_dev s6))
                     (R_bool minstret_increment) b')
                  nextPC (add_vec_int pc_e5 4))
         = Some (RETIRE_SUCCESS, s_exec, [])
       /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
       /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b'
       /\ dom (mem s_exec) ⊆ wwin pc_e5 pc_e5 0).
    { intro b'.
      set (s0c := MState (wm_regs s6)
                    (wmem_restrict s6 (wwin pc_e5 pc_e5 0)) (wm_dev s6)).
      pose proof (exec_eff_execute_MUL_gpr i_mul_rs2 i_mul_rs1 i_mul_rd
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc_e5 4)) Hrd_5) as He.
      destruct (load_sexec_facts s0c b' (add_vec_int pc_e5 4) i_mul_rd
                  (regval_into_reg (gpr_mul_val i_mul_rs2 i_mul_rs1
                     (set_reg (set_reg s0c (R_bool minstret_increment) b')
                        nextPC (add_vec_int pc_e5 4)))))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart6.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    assert (HP6 : wP_eff (Some (fin_to_nat cpu_id)) [WEread wak_plain pc_e5 4] s6).
    { change ([WEread wak_plain pc_e5 4])
        with ([WEread wak_plain pc_e5 4] ++ []).
      apply (wP_eff_of_leaf_base (fin_to_nat cpu_id) s6 (wwin pc_e5 pc_e5 0)
               pc_e5 w_mul
               (MUL (Regidx i_mul_rs2, Regidx i_mul_rs1, Regidx i_mul_rd,
                     mulop_mul)) [] D_m dstateM).
      - exact Hwf6.
      - exact (wwin_nonzero pc_e5 pc_e5 0 Hram_5 (win0_absurd _)).
      - exact (wwin_pinned s6 pc_e5 pc_e5 0 Hacc_5 Hacc0_5 Hpin6 (win0_absurd _)).
      - exact Lpc6.
      - exact Lpriv6.
      - rewrite Lpmpc6. exact (pmp_all_off_allows_all _ Hpmp).
      - exact Lpma6.
      - exact Lhtif6.
      - exact Lhart6.
      - exact LmisaS6.
      - exact LmIE6.
      - exact Lelp6.
      - exact Hal4_5.
      - exact Hram_5.
      - exact (wwin_conf_text s6 pc_e5 pc_e5 0 w_mul Htext6).
      - exact nrvc_e5.
      - exact (agree_m_regs (wm_regs s6) Lpriv6 Lsec6 Lmisa6).
      - exact D_m_mi.
      - exact good_e5.
      - exact dec_e5.
      - exact lpad_e5.
      - exact Hc6. }
    (* the two operand reads: a0 (rs1 = rd) and a1 (rs2) *)
    iDestruct (gpr_file_lookup_acc (m_caddi m v_stack0 mhartid_in)
                 (Regidx i_mul_rs2) with "Hfile") as "[Hc6b Hf6b]".
    iEval (rewrite (gpr_pt_nz i_mul_rs2 _ Hrs2_5)) in "Hc6b".
    iDestruct (reg_valid with "Hreg Hc6b") as %La1_6.
    iEval (rewrite <- (gpr_pt_nz i_mul_rs2 _ Hrs2_5)) in "Hc6b".
    iDestruct ("Hf6b" with "Hc6b") as "Hfile".
    iDestruct (gpr_file_insert_acc (m_caddi m v_stack0 mhartid_in)
                 (Regidx i_mul_rd)
                 (regval_into_reg
                    (mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
                       (mulop_mul.(mul_op_signed_rs2))
                       (m_caddi m v_stack0 mhartid_in !!! Regidx i_mul_rs1)
                       (m_caddi m v_stack0 mhartid_in !!! Regidx i_mul_rs2)
                       (mulop_mul.(mul_op_result_part))))
                 with "Hfile") as "[Hc6a Hfins6]".
    iEval (rewrite (gpr_pt_nz i_mul_rd _ Hrd_5)) in "Hc6a".
    iDestruct (reg_valid with "Hreg Hc6a") as %La0_6.
    assert (Hval6 : gpr_mul_val i_mul_rs2 i_mul_rs1
              (set_reg (set_reg (wflat_st s6) (R_bool minstret_increment) b6)
                 nextPC (add_vec_int pc_e5 4))
            = mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
                (mulop_mul.(mul_op_signed_rs2))
                (m_caddi m v_stack0 mhartid_in !!! Regidx i_mul_rs1)
                (m_caddi m v_stack0 mhartid_in !!! Regidx i_mul_rs2)
                (mulop_mul.(mul_op_result_part))).
    { unfold gpr_mul_val.
      replace (Z.eqb (uint i_mul_rs1) 0) with false
        by (vm_compute; reflexivity).
      replace (Z.eqb (uint i_mul_rs2) 0) with false
        by (vm_compute; reflexivity).
      rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint i_mul_rs1)))
                 nextPC _ _ ltac:(reg_ne)).
      rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint i_mul_rs2)))
                 nextPC _ _ ltac:(reg_ne)).
      change (gpr_of_Z (uint i_mul_rs1)) with (gpr_of_Z (uint i_mul_rd)).
      rewrite La0_6 La1_6. reflexivity. }
    pose proof (exec_eff_execute_MUL_gpr i_mul_rs2 i_mul_rs1 i_mul_rd
                  (set_reg (set_reg (wflat_st s6) (R_bool minstret_increment) b6)
                     nextPC (add_vec_int pc_e5 4)) Hrd_5) as Hef6.
    rewrite Hval6 in Hef6.
    iMod (reg_update _ nextPC _ (add_vec_int pc_e5 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint i_mul_rd))) _
            (regval_into_reg
               (mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
                  (mulop_mul.(mul_op_signed_rs2))
                  (m_caddi m v_stack0 mhartid_in !!! Regidx i_mul_rs1)
                  (m_caddi m v_stack0 mhartid_in !!! Regidx i_mul_rs2)
                  (mulop_mul.(mul_op_result_part))))
            with "Hreg Hc6a") as "[Hreg Hc6a]".
    iDestruct ("Hfins6" with "[Hc6a]") as "Hfile".
    { iEval (rewrite (gpr_pt_nz i_mul_rd _ Hrd_5)). iExact "Hc6a". }
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP6|].
    iExists (set_reg (set_reg (set_reg (wflat_st s6)
                        (R_bool minstret_increment) b6)
                      nextPC (add_vec_int pc_e5 4))
                     (R_bitvector_64 (gpr_of_Z (uint i_mul_rd)))
                     (regval_into_reg
                        (mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
                           (mulop_mul.(mul_op_signed_rs2))
                           (m_caddi m v_stack0 mhartid_in !!! Regidx i_mul_rs1)
                           (m_caddi m v_stack0 mhartid_in !!! Regidx i_mul_rs2)
                           (mulop_mul.(mul_op_result_part))))).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef6)|].
    iFrame "Hreg".
    iNext. iIntros (tick6 s6' t6) "%Hstep6 %Hdevt6 %Hpost6 %HQ6 Hmm Hpmpc Hpc".
    destruct Hpost6 as (Hregs6 & Hdevs6 & Hmems6 & Himgs6 & Hlogs6 & Hwsle6 &
                        Hwf6' & Hbnd6').
    destruct HQ6 as (HQi6 & HQl6 & HQw6).
    assert (Hdevflat6 : mdev t6 = wm_dev s6).
    { rewrite Hdevt6 -(wflat_st_dev s6).
      exact (proj1 (proj2 (proj2 (proj2 (load_sexec_facts (wflat_st s6) b6
               (add_vec_int pc_e5 4) i_mul_rd
               (regval_into_reg
                  (mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
                     (mulop_mul.(mul_op_signed_rs2))
                     (m_caddi m v_stack0 mhartid_in !!! Regidx i_mul_rs1)
                     (m_caddi m v_stack0 mhartid_in !!! Regidx i_mul_rs2)
                     (mulop_mul.(mul_op_result_part))))))))). }
    iMod (hart_ws_update cpu_id (wm_ws s6) (wm_ws s5') (wm_ws s6')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    pose proof (proj2 (proj2 (proj2 (proj2 (load_sexec_facts (wflat_st s6)
             b6 (add_vec_int pc_e5 4) i_mul_rd
             (regval_into_reg
                (mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
                   (mulop_mul.(mul_op_signed_rs2))
                   (m_caddi m v_stack0 mhartid_in !!! Regidx i_mul_rs1)
                   (m_caddi m v_stack0 mhartid_in !!! Regidx i_mul_rs2)
                   (mulop_mul.(mul_op_result_part))))))))) as HnpcR6.
    iEval (rewrite HnpcR6) in "Hpc". clear HnpcR6.
    iSplitL "Hlat"; [by rewrite HQi6 HQl6|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs6 Hdevflat6 HQl6. iFrame. }
    iEval (rewrite Hws6) in "Hpt".
    iDestruct (wpt8_mono entry_ld_ea dq v_stack0 (wm_ws s6) (wm_ws s6') Hwsle6
                 with "Hpt") as "Hpt".
    assert (Hle6 : ws_le ws (wm_ws s6')).
    { etransitivity; [exact Hle5|]. rewrite Hws6. exact Hwsle6. }
    iEval (change (<[Regidx i_mul_rd :=
                      regval_into_reg
                        (mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
                           (mulop_mul.(mul_op_signed_rs2))
                           (m_caddi m v_stack0 mhartid_in !!! Regidx i_mul_rs1)
                           (m_caddi m v_stack0 mhartid_in !!! Regidx i_mul_rs2)
                           (mulop_mul.(mul_op_result_part)))]>
                     (m_caddi m v_stack0 mhartid_in))
             with (m_mul m v_stack0 mhartid_in)) in "Hfile".
    iEval (rewrite pc_e5_e6) in "Hpc". iEval (rewrite pc_e5_e6) in "Hnpc".

    (* ================= 7. C.ADD @ pc_e6 (F_RVC, 4-aligned) ============= *)
    assert (Hal2_6 : is_aligned_vaddr (Virtaddr pc_e6) 2 = true)
      by (vm_compute; reflexivity).
    assert (Hal4_6 : is_aligned_vaddr (Virtaddr pc_e6) 4 = true)
      by (vm_compute; reflexivity).
    assert (Hacc_6 : acc_wf pc_e6 4)
      by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hacc0_6 : acc_wf pc_e6 0)
      by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_6 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc_e6 j))
      by ram_win.
    assert (Hrd_6 : uint (regidx_bits rsd_cadd) <> 0)
      by (vm_compute; discriminate).
    assert (Hrs2_6 : uint (regidx_bits rs2_cadd) <> 0)
      by (vm_compute; discriminate).
    iAssert (winstr_bytes pc_e6 (F_RVC h_add)) as "#Hbs6".
    { iApply (winstr_bytes_of_text kbs pc_e6 (F_RVC h_add) w_e6 Hal2_6 Hacc_6
                Hram_6 (conj sub_e6 rvc_e6) with "Htext").
      iPureIntro.
      exact (wkb_window kbs (KernelSyms._entry + 0x14) w_e6 Hcov kb_e6). }
    iAssert (winstr pc_e6 true (RTYPE (rs2_cadd, rsd_cadd, rsd_cadd, ADD)))
      as "#Hin6".
    { iApply (winstr_intro pc_e6 true
                (RTYPE (rs2_cadd, rsd_cadd, rsd_cadd, ADD))
                (F_RVC h_add) lpad_e6 eq_refl
                (fun t _ HC _ _ _ =>
                   ex_intro _ (C_ADD (rsd_cadd, rs2_cadd))
                     (conj (kd_912a t HC)
                        (conj lpad_i0_e6 (exec_execute_C_ADD rsd_cadd rs2_cadd))))
                with "Hbs6"). }
    iApply (wwp_instr pc_e6 true (RTYPE (rs2_cadd, rsd_cadd, rsd_cadd, ADD))
              pmpcfg0 (dq := DfracOwn 1)
              (wP_eff (Some (fin_to_nat cpu_id)) [WEread wak_plain pc_e6 4])
              wQ_pure Hgid Hacc_6 (pmp_all_off_allows_all _ Hpmp)
              (wcert_nowrite (fin_to_nat cpu_id) pc_e6
                 [WEread wak_plain pc_e6 4] (nowrite_read1 wak_plain pc_e6 4))
              with "Hmm Hpmpc Hpc Hin6").
    rewrite /wwp_cb. iIntros (s7 b7) "%Lpc7 %Hcfg7 Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd7 & %Hwf7 & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws s7) (wm_ws s6') with "Hwsauth Hhws")
      as %Hws7.
    destruct Hcfg7 as (Lpriv7 & Lhart7 & Lmisa7 & Lsec7 & Lpmpc7 & Lpma7 &
                       Lhtif7 & LmisaS7 & LmIE7 & Lmprv7 & Lpmm7 & Lelp7).
    iDestruct (winstr_flat s7 pc_e6 (F_RVC h_add) Hwf7 with "Hlat Hbs6")
      as %Hfok7.
    iDestruct (winstr_pinned s7 pc_e6 (F_RVC h_add) Hwf7 with "Hlat Hbs6")
      as %Hpin7.
    destruct Hfok7 as (_ & _ & w7 & [Hsub7 Hrvc7] & Htext7).
    assert (Hc7 : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (RTYPE (rs2_cadd, rsd_cadd, rsd_cadd, ADD)))
         (set_reg (set_reg (MState (wm_regs s7)
                     (wmem_restrict s7 (wwin pc_e6 pc_e6 0)) (wm_dev s7))
                     (R_bool minstret_increment) b')
                  nextPC (add_vec_int pc_e6 2))
         = Some (RETIRE_SUCCESS, s_exec, [])
       /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
       /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b'
       /\ dom (mem s_exec) ⊆ wwin pc_e6 pc_e6 0).
    { intro b'.
      set (s0c := MState (wm_regs s7)
                    (wmem_restrict s7 (wwin pc_e6 pc_e6 0)) (wm_dev s7)).
      pose proof (exec_eff_execute_RTYPE_ADD_gpr (regidx_bits rs2_cadd)
                    (regidx_bits rsd_cadd) (regidx_bits rsd_cadd)
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc_e6 2))) as He.
      replace (Z.eqb (uint (regidx_bits rsd_cadd)) 0) with false in He
        by (vm_compute; reflexivity).
      destruct (load_sexec_facts s0c b' (add_vec_int pc_e6 2)
                  (regidx_bits rsd_cadd)
                  (regval_into_reg (gpr_rd_val (regidx_bits rs2_cadd)
                     (regidx_bits rsd_cadd)
                     (set_reg (set_reg s0c (R_bool minstret_increment) b')
                        nextPC (add_vec_int pc_e6 2)))))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart7.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    assert (HP7 : wP_eff (Some (fin_to_nat cpu_id)) [WEread wak_plain pc_e6 4] s7).
    { change ([WEread wak_plain pc_e6 4])
        with ([WEread wak_plain pc_e6 4] ++ []).
      apply (wP_eff_of_leaf_rvc4 (fin_to_nat cpu_id) s7 (wwin pc_e6 pc_e6 0)
               pc_e6 h_add w7 (C_ADD (rsd_cadd, rs2_cadd))
               (RTYPE (rs2_cadd, rsd_cadd, rsd_cadd, ADD)) []
               D_m D_none dstateM).
      - exact Hwf7.
      - exact (wwin_nonzero pc_e6 pc_e6 0 Hram_6 (win0_absurd _)).
      - exact (wwin_pinned s7 pc_e6 pc_e6 0 Hacc_6 Hacc0_6 Hpin7 (win0_absurd _)).
      - exact Lpc7.
      - exact Lpriv7.
      - rewrite Lpmpc7. exact (pmp_all_off_allows_all _ Hpmp).
      - exact Lpma7.
      - exact Lhtif7.
      - exact Lhart7.
      - exact LmisaS7.
      - exact (misaC_of_val _ Lmisa7).
      - exact LmIE7.
      - exact Lelp7.
      - exact Hal4_6.
      - exact Hram_6.
      - exact (wwin_conf_text s7 pc_e6 pc_e6 0 w7 Htext7).
      - exact Hsub7.
      - exact Hrvc7.
      - exact (agree_m_regs (wm_regs s7) Lpriv7 Lsec7 Lmisa7).
      - exact D_m_mi.
      - exact good_e6.
      - exact dec_e6.
      - exact good_exp_e6.
      - exact (exec_execute_C_ADD rsd_cadd rs2_cadd).
      - exact Hc7. }
    (* the two operand reads: sp (rsd) and a0 (rs2) *)
    iDestruct (gpr_file_lookup_acc (m_mul m v_stack0 mhartid_in)
                 (Regidx (regidx_bits rs2_cadd)) with "Hfile") as "[Hc7b Hf7b]".
    iEval (rewrite (gpr_pt_nz (regidx_bits rs2_cadd) _ Hrs2_6)) in "Hc7b".
    iDestruct (reg_valid with "Hreg Hc7b") as %La0_7.
    iEval (rewrite <- (gpr_pt_nz (regidx_bits rs2_cadd) _ Hrs2_6)) in "Hc7b".
    iDestruct ("Hf7b" with "Hc7b") as "Hfile".
    iDestruct (gpr_file_insert_acc (m_mul m v_stack0 mhartid_in)
                 (Regidx (regidx_bits rsd_cadd))
                 (regval_into_reg
                    (add_vec (m_mul m v_stack0 mhartid_in
                                !!! Regidx (regidx_bits rsd_cadd))
                       (m_mul m v_stack0 mhartid_in
                          !!! Regidx (regidx_bits rs2_cadd))))
                 with "Hfile") as "[Hc7a Hfins7]".
    iEval (rewrite (gpr_pt_nz (regidx_bits rsd_cadd) _ Hrd_6)) in "Hc7a".
    iDestruct (reg_valid with "Hreg Hc7a") as %Lsp_7.
    assert (Hval7 : gpr_rd_val (regidx_bits rs2_cadd) (regidx_bits rsd_cadd)
              (set_reg (set_reg (wflat_st s7) (R_bool minstret_increment) b7)
                 nextPC (add_vec_int pc_e6 2))
            = add_vec (m_mul m v_stack0 mhartid_in
                         !!! Regidx (regidx_bits rsd_cadd))
                (m_mul m v_stack0 mhartid_in
                   !!! Regidx (regidx_bits rs2_cadd))).
    { unfold gpr_rd_val.
      replace (Z.eqb (uint (regidx_bits rsd_cadd)) 0) with false
        by (vm_compute; reflexivity).
      replace (Z.eqb (uint (regidx_bits rs2_cadd)) 0) with false
        by (vm_compute; reflexivity).
      rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint (regidx_bits rsd_cadd))))
                 nextPC _ _ ltac:(reg_ne)).
      rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint (regidx_bits rs2_cadd))))
                 nextPC _ _ ltac:(reg_ne)).
      rewrite Lsp_7 La0_7. reflexivity. }
    pose proof (exec_eff_execute_RTYPE_ADD_gpr (regidx_bits rs2_cadd)
                  (regidx_bits rsd_cadd) (regidx_bits rsd_cadd)
                  (set_reg (set_reg (wflat_st s7) (R_bool minstret_increment) b7)
                     nextPC (add_vec_int pc_e6 2))) as Hef7.
    replace (Z.eqb (uint (regidx_bits rsd_cadd)) 0) with false in Hef7
      by (vm_compute; reflexivity).
    rewrite Hval7 in Hef7.
    iMod (reg_update _ nextPC _ (add_vec_int pc_e6 2) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _
            (R_bitvector_64 (gpr_of_Z (uint (regidx_bits rsd_cadd)))) _
            (regval_into_reg
               (add_vec (m_mul m v_stack0 mhartid_in
                           !!! Regidx (regidx_bits rsd_cadd))
                  (m_mul m v_stack0 mhartid_in
                     !!! Regidx (regidx_bits rs2_cadd))))
            with "Hreg Hc7a") as "[Hreg Hc7a]".
    iDestruct ("Hfins7" with "[Hc7a]") as "Hfile".
    { iEval (rewrite (gpr_pt_nz (regidx_bits rsd_cadd) _ Hrd_6)).
      iExact "Hc7a". }
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP7|].
    iExists (set_reg (set_reg (set_reg (wflat_st s7)
                        (R_bool minstret_increment) b7)
                      nextPC (add_vec_int pc_e6 2))
                     (R_bitvector_64 (gpr_of_Z (uint (regidx_bits rsd_cadd))))
                     (regval_into_reg
                        (add_vec (m_mul m v_stack0 mhartid_in
                                    !!! Regidx (regidx_bits rsd_cadd))
                           (m_mul m v_stack0 mhartid_in
                              !!! Regidx (regidx_bits rs2_cadd))))).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef7)|].
    iFrame "Hreg".
    iNext. iIntros (tick7 s7' t7) "%Hstep7 %Hdevt7 %Hpost7 %HQ7 Hmm Hpmpc Hpc".
    destruct Hpost7 as (Hregs7 & Hdevs7 & Hmems7 & Himgs7 & Hlogs7 & Hwsle7 &
                        Hwf7' & Hbnd7').
    destruct HQ7 as (HQi7 & HQl7 & HQw7).
    assert (Hdevflat7 : mdev t7 = wm_dev s7).
    { rewrite Hdevt7 -(wflat_st_dev s7).
      exact (proj1 (proj2 (proj2 (proj2 (load_sexec_facts (wflat_st s7) b7
               (add_vec_int pc_e6 2) (regidx_bits rsd_cadd)
               (regval_into_reg
                  (add_vec (m_mul m v_stack0 mhartid_in
                              !!! Regidx (regidx_bits rsd_cadd))
                     (m_mul m v_stack0 mhartid_in
                        !!! Regidx (regidx_bits rs2_cadd))))))))). }
    iMod (hart_ws_update cpu_id (wm_ws s7) (wm_ws s6') (wm_ws s7')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    pose proof (proj2 (proj2 (proj2 (proj2 (load_sexec_facts (wflat_st s7)
             b7 (add_vec_int pc_e6 2) (regidx_bits rsd_cadd)
             (regval_into_reg
                (add_vec (m_mul m v_stack0 mhartid_in
                            !!! Regidx (regidx_bits rsd_cadd))
                   (m_mul m v_stack0 mhartid_in
                      !!! Regidx (regidx_bits rs2_cadd))))))))) as HnpcR7.
    iEval (rewrite HnpcR7) in "Hpc". clear HnpcR7.
    iSplitL "Hlat"; [by rewrite HQi7 HQl7|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs7 Hdevflat7 HQl7. iFrame. }
    iEval (rewrite Hws7) in "Hpt".
    iDestruct (wpt8_mono entry_ld_ea dq v_stack0 (wm_ws s7) (wm_ws s7') Hwsle7
                 with "Hpt") as "Hpt".
    assert (Hle7 : ws_le ws (wm_ws s7')).
    { etransitivity; [exact Hle6|]. rewrite Hws7. exact Hwsle7. }
    iEval (change (<[Regidx (regidx_bits rsd_cadd) :=
                      regval_into_reg
                        (add_vec (m_mul m v_stack0 mhartid_in
                                    !!! Regidx (regidx_bits rsd_cadd))
                           (m_mul m v_stack0 mhartid_in
                              !!! Regidx (regidx_bits rs2_cadd)))]>
                     (m_mul m v_stack0 mhartid_in))
             with (m_cadd m v_stack0 mhartid_in)) in "Hfile".
    iEval (rewrite pc_e6_e7) in "Hpc". iEval (rewrite pc_e6_e7) in "Hnpc".

    (* ================= 8. JAL @ pc_e7 (F_Base, 2-aligned) ============== *)
    assert (Hal2_7 : is_aligned_vaddr (Virtaddr pc_e7) 2 = true)
      by (vm_compute; reflexivity).
    assert (Hal4_7 : is_aligned_vaddr (Virtaddr pc_e7) 4 = false)
      by (vm_compute; reflexivity).
    assert (Hacc_7 : acc_wf pc_e7 4)
      by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hacc0_7 : acc_wf pc_e7 0)
      by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_7 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc_e7 j))
      by ram_win.
    assert (Hrd_7 : uint i_jal <> 0) by (vm_compute; discriminate).
    assert (Hjal0 : eq_vec (access_vec_dec
                      (add_vec pc_e7 (sign_extend' 64 imm_jal)) 0) ('b"0") = true)
      by (vm_compute; reflexivity).
    assert (Hjal1 : bit_to_bool (access_vec_dec
                      (add_vec pc_e7 (sign_extend' 64 imm_jal)) 1) = false)
      by (vm_compute; reflexivity).
    iAssert (winstr_bytes pc_e7 (F_Base w_jal)) as "#Hbs7".
    { iApply (winstr_bytes_of_text kbs pc_e7 (F_Base w_jal) w_jal Hal2_7
                Hacc_7 Hram_7 (conj eq_refl nrvc_e7) with "Htext").
      iPureIntro.
      exact (wkb_window kbs (KernelSyms._entry + 0x16) w_jal Hcov kb_e7). }
    iAssert (winstr pc_e7 false (JAL (imm_jal, Regidx i_jal))) as "#Hin7".
    { iApply (winstr_intro pc_e7 false (JAL (imm_jal, Regidx i_jal))
                (F_Base w_jal) lpad_e7 eq_refl
                (fun t _ _ _ Hm Hc => kd_042000ef t Hm Hc) with "Hbs7"). }
    iApply (wwp_instr pc_e7 false (JAL (imm_jal, Regidx i_jal))
              pmpcfg0 (dq := DfracOwn 1)
              (wP_eff (Some (fin_to_nat cpu_id))
                 [WEread wak_plain pc_e7 2;
                  WEread wak_plain (add_vec_int pc_e7 2) 2])
              wQ_pure Hgid Hacc_7 (pmp_all_off_allows_all _ Hpmp)
              (wcert_nowrite (fin_to_nat cpu_id) pc_e7
                 [WEread wak_plain pc_e7 2;
                  WEread wak_plain (add_vec_int pc_e7 2) 2]
                 (nowrite_fetch2 pc_e7))
              with "Hmm Hpmpc Hpc Hin7").
    rewrite /wwp_cb. iIntros (s8 b8) "%Lpc8 %Hcfg8 Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd8 & %Hwf8 & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws s8) (wm_ws s7') with "Hwsauth Hhws")
      as %Hws8.
    destruct Hcfg8 as (Lpriv8 & Lhart8 & Lmisa8 & Lsec8 & Lpmpc8 & Lpma8 &
                       Lhtif8 & LmisaS8 & LmIE8 & Lmprv8 & Lpmm8 & Lelp8).
    iDestruct (winstr_flat s8 pc_e7 (F_Base w_jal) Hwf8 with "Hlat Hbs7")
      as %Hfok8.
    iDestruct (winstr_pinned s8 pc_e7 (F_Base w_jal) Hwf8 with "Hlat Hbs7")
      as %Hpin8.
    destruct Hfok8 as (_ & _ & w8 & [Hww8 _] & Htext8). subst w8.
    assert (Hc8 : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (JAL (imm_jal, Regidx i_jal)))
         (set_reg (set_reg (MState (wm_regs s8)
                     (wmem_restrict s8 (wwin pc_e7 pc_e7 0)) (wm_dev s8))
                     (R_bool minstret_increment) b')
                  nextPC (add_vec_int pc_e7 4))
         = Some (RETIRE_SUCCESS, s_exec, [])
       /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
       /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b'
       /\ dom (mem s_exec) ⊆ wwin pc_e7 pc_e7 0).
    { intro b'.
      set (s0c := MState (wm_regs s8)
                    (wmem_restrict s8 (wwin pc_e7 pc_e7 0)) (wm_dev s8)).
      set (sic := set_reg (set_reg s0c (R_bool minstret_increment) b')
                    nextPC (add_vec_int pc_e7 4)).
      assert (HPCc : register_lookup PC (sregs sic) = pc_e7).
      { unfold sic.
        rewrite (set_lookup_ne PC nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup PC _ b' eq_refl). exact Lpc8. }
      pose proof (exec_eff_execute_JAL_gpr imm_jal i_jal sic Hrd_7
                    ltac:(rewrite HPCc; exact Hjal0)
                    ltac:(rewrite HPCc; exact Hjal1)) as He.
      destruct (jal_sexec_facts s0c b' (add_vec_int pc_e7 4)
                  (add_vec (register_lookup PC (sregs sic))
                     (sign_extend' 64 imm_jal)) i_jal
                  (register_lookup nextPC (sregs sic)))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart8.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    assert (HP8 : wP_eff (Some (fin_to_nat cpu_id))
                    [WEread wak_plain pc_e7 2;
                     WEread wak_plain (add_vec_int pc_e7 2) 2] s8).
    { change ([WEread wak_plain pc_e7 2;
               WEread wak_plain (add_vec_int pc_e7 2) 2])
        with ([WEread wak_plain pc_e7 2;
               WEread wak_plain (add_vec_int pc_e7 2) 2] ++ []).
      apply (wP_eff_of_leaf_base2 (fin_to_nat cpu_id) s8 (wwin pc_e7 pc_e7 0)
               pc_e7 w_jal (JAL (imm_jal, Regidx i_jal)) [] D_m dstateM).
      - exact Hwf8.
      - exact (wwin_nonzero pc_e7 pc_e7 0 Hram_7 (win0_absurd _)).
      - exact (wwin_pinned s8 pc_e7 pc_e7 0 Hacc_7 Hacc0_7 Hpin8 (win0_absurd _)).
      - exact Lpc8.
      - exact Lpriv8.
      - rewrite Lpmpc8. exact (pmp_all_off_allows_all _ Hpmp).
      - exact Lpma8.
      - exact Lhtif8.
      - exact Lhart8.
      - exact LmisaS8.
      - exact (misaC_of_val _ Lmisa8).
      - exact LmIE8.
      - exact Lelp8.
      - exact Hal2_7.
      - exact Hal4_7.
      - exact Hram_7.
      - exact (wwin_conf_text s8 pc_e7 pc_e7 0 w_jal Htext8).
      - exact nrvc_e7.
      - exact (agree_m_regs (wm_regs s8) Lpriv8 Lsec8 Lmisa8).
      - exact D_m_mi.
      - exact good_e7.
      - exact dec_e7.
      - exact lpad_e7.
      - exact Hc8. }
    (* the flat execute fact *)
    set (sif := set_reg (set_reg (wflat_st s8) (R_bool minstret_increment) b8)
                  nextPC (add_vec_int pc_e7 4)).
    assert (HPCin8 : register_lookup PC (sregs sif) = pc_e7).
    { unfold sif.
      rewrite (set_lookup_ne PC nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat PC s8 b8 eq_refl). exact Lpc8. }
    assert (Hnpc8 : register_lookup nextPC (sregs sif) = add_vec_int pc_e7 4).
    { unfold sif. rewrite sregs_set_reg. apply register_lookup_set. }
    pose proof (exec_eff_execute_JAL_gpr imm_jal i_jal sif Hrd_7
                  ltac:(rewrite HPCin8; exact Hjal0)
                  ltac:(rewrite HPCin8; exact Hjal1)) as Hef8.
    rewrite HPCin8 Hnpc8 in Hef8.
    rewrite pc_e7_start in Hef8.
    iMod (reg_update _ nextPC _ (add_vec_int pc_e7 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ nextPC _ pc_start with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (gpr_file_insert_acc (m_cadd m v_stack0 mhartid_in)
                 (Regidx i_jal) (regval_into_reg (add_vec_int pc_e7 4))
                 with "Hfile") as "[Hrac Hfins8]".
    iEval (rewrite (gpr_pt_nz i_jal _ Hrd_7)) in "Hrac".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint i_jal))) _
            (regval_into_reg (add_vec_int pc_e7 4)) with "Hreg Hrac")
      as "[Hreg Hrac]".
    iDestruct ("Hfins8" with "[Hrac]") as "Hfile".
    { iEval (rewrite (gpr_pt_nz i_jal _ Hrd_7)). iExact "Hrac". }
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP8|].
    iExists (set_reg (set_reg sif nextPC pc_start)
               (R_bitvector_64 (gpr_of_Z (uint i_jal)))
               (regval_into_reg (add_vec_int pc_e7 4))).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef8)|].
    iFrame "Hreg".
    iNext. iIntros (tick8 s8' t8) "%Hstep8 %Hdevt8 %Hpost8 %HQ8 Hmm Hpmpc Hpc".
    destruct Hpost8 as (Hregs8 & Hdevs8 & Hmems8 & Himgs8 & Hlogs8 & Hwsle8 &
                        Hwf8' & Hbnd8').
    destruct HQ8 as (HQi8 & HQl8 & HQw8).
    destruct (jal_sexec_facts (wflat_st s8) b8 (add_vec_int pc_e7 4) pc_start
                i_jal (add_vec_int pc_e7 4)) as (G1 & G2 & G3 & G4 & G5).
    assert (Hdevflat8 : mdev t8 = wm_dev s8).
    { rewrite Hdevt8 -(wflat_st_dev s8). exact G4. }
    iMod (hart_ws_update cpu_id (wm_ws s8) (wm_ws s7') (wm_ws s8')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    iEval (rewrite G5) in "Hpc".
    iSplitL "Hlat"; [by rewrite HQi8 HQl8|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs8 Hdevflat8 HQl8. iFrame. }
    iEval (rewrite Hws8) in "Hpt".
    iDestruct (wpt8_mono entry_ld_ea dq v_stack0 (wm_ws s8) (wm_ws s8') Hwsle8
                 with "Hpt") as "Hpt".
    assert (Hle8 : ws_le ws (wm_ws s8')).
    { etransitivity; [exact Hle7|]. rewrite Hws8. exact Hwsle8. }
    iEval (change (<[Regidx i_jal := regval_into_reg (add_vec_int pc_e7 4)]>
                     (m_cadd m v_stack0 mhartid_in))
             with (m_jal m v_stack0 mhartid_in)) in "Hfile".
    iApply ("Hcont" $! (wm_ws s8') with
              "[%] Hmm Hpmpc [$Hpc $Hnpc] Hfile Hmh Hhws Hpt").
    exact Hle8.
  Qed.

End entry.
