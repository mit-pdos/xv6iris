(** * WeakLeafItype.v — the weak REGISTER-ONLY ITYPE leaves (M4, start/timerinit)

    The weak twins of [WpMmodeItype]'s two register-generic I-type leaves
    ([wp_addi_gpr] / [wp_ori_gpr]), stated over the WHOLE [gpr_file] — the
    [start()] / [timerinit()] call sites have [rd = rs1] and [rs1 = x0] all
    over, and separate per-register cells cannot express either (the
    [wwp_entry] finding).  Three leaves:

      §2  [wwp_addi_leaf]      — [addi rd, rs1, imm] at an [F_Base] fetch;
      §3  [wwp_addi_rvc_leaf]  — the SAME [ITYPE … ADDI] ast reached through a
          COMPRESSED decode (this is what [c.addi] / [c.li] / [c.addi4spn]
          expand to), at an [F_RVC] fetch;
      §4  [wwp_ori_leaf]       — [ori rd, rs1, imm] at an [F_Base] fetch.

    Every leaf takes the fetch alignment [al4] as a PARAMETER and so covers
    both the 4-aligned and the 2-not-4-aligned call sites with one statement:
    the [F_Base] pair goes through [WeakLeafRegOnly.wP_eff_of_leaf_regonly] +
    [wcert_regonly], the compressed one through
    [WeakLeafTor.wP_eff_of_leaf_rvc] at [es_x := []] (whose conclusion is then
    the single fetch element, certified by [WeakEff.wcert_nowrite]).

    Nothing here touches memory, so the window is the text-only
    [WeakLeafWin.wwin pc pc 0] and the certificate's [Q] is [wQ_pure].  The
    only per-instruction facts are the two [execute] mirrors: ADDI's is
    [WkEntryEff.exec_eff_execute_ITYPE_ADDI_gpr], reused; ORI's (§1) is that
    script with [add_vec] → [or_vec], mirroring
    [WpMmodeLeafBase.exec_execute_ITYPE_ORI_gpr].

    Proof template: [WeakLeafCsrw2.wwp_csrw_medeleg_leaf] with the CSR
    plumbing replaced by the gpr-file read/write moves of [WkEntryNew]'s
    AUIPC block ([gpr_file_lookup_acc] + [gpr_pt_value] for the x0-safe
    source read, [gpr_file_insert_acc] + [gpr_pt_nz] + [reg_update] for the
    destination write). *)
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
Require Import WeakFetchEff WeakFetchRvc WeakFetch2.
Require Import WeakFunnel WpDecodeBridge.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import RegFile WpGpr WpMmodeLeafBase.
Require Import ExecCommon WpDecode.
(* the shared window / register-peel kit, the alignment-generic register-only
   recipe, and the compressed one. *)
Require Import WeakLeafWin WeakLeafRegOnly WeakLeafTor.
(* the ADDI [execute] mirror (§2d there). *)
Require Import WkEntryEff.

Import SailStdpp.Values.
Import Defs.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The ORI [execute] mirror, and the source-register peel *)

(** [WkEntryEff.exec_eff_execute_ITYPE_ADDI_gpr]'s script at the [ORI] arm of
    [execute_ITYPE] (the model's two arms are the same bind spine with
    [add_vec] resp. [or_vec] between them), i.e. the [exec_eff] twin of
    [WpMmodeLeafBase.exec_execute_ITYPE_ORI_gpr]. *)
Lemma exec_eff_execute_ITYPE_ORI_gpr (rs1 rd : mword 5) (imm : mword 12) s :
  exec_eff (execute (ITYPE (imm, Regidx rs1, Regidx rd, ORI))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_ori_val rs1 imm s)),
          []).
Proof.
  change (execute (ITYPE (imm, Regidx rs1, Regidx rd, ORI)))
    with (execute_ITYPE imm (Regidx rs1) (Regidx rd) ORI).
  unfold execute_ITYPE, gpr_ori_val. cbn match.
  rewrite (exec_eff_bind_nil _ _ _
             (or_vec (if Z.eqb (uint rs1) 0 then zero_reg
                      else register_lookup
                             (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                (sign_extend' 64 imm)) s).
  2:{ rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_rX_bits_gpr rs1 s)).
      apply exec_eff_returnm. }
  rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_wX_bits_gpr rd _ s)).
  apply exec_eff_returnm.
Qed.

(** The x0-SAFE source read, moved past the funnel's [nextPC] pre-write.
    ([WeakLeafWin.leaf_peel] peels BOTH pre-writes; the [minstret_increment]
    one is already peeled here, because the funnel hands the leaf
    [reg_interp] AT that state.) *)
Lemma gpr_src_peel_npc (rs1 : mword 5) (s : mstate)
    (npc : SailStdpp.Values.mword 64) :
  (if Z.eqb (uint rs1) 0 then zero_reg
   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
          (sregs (set_reg s nextPC npc)))
  = (if Z.eqb (uint rs1) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)).
Proof.
  destruct (Z.eqb (uint rs1) 0); [reflexivity|].
  exact (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC s npc
           ltac:(reg_ne)).
Qed.

(** ... and the same read moved from the funnel's flat state to [σ]'s own
    register file ([WeakLeafWin.reg_at_flat] under the [x0] guard). *)
Lemma gpr_src_at_flat (rs1 : mword 5) (σ : wmstate) (b : bool) :
  (if Z.eqb (uint rs1) 0 then zero_reg
   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
          (sregs (set_reg (wflat_st σ) (R_bool minstret_increment) b)))
  = (if Z.eqb (uint rs1) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) (wm_regs σ)).
Proof.
  destruct (Z.eqb (uint rs1) 0); [reflexivity|].
  exact (reg_at_flat (R_bitvector_64 (gpr_of_Z (uint rs1))) σ b eq_refl).
Qed.

(* ====================================================================== *)
(** ** 2. [addi rd, rs1, imm] — the [F_Base] leaf (THE TEMPLATE) *)

Section leaf_addi.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Implicit Types Φ : mval -> iProp Σ.

  Lemma wwp_addi_leaf Φ (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rs1 rd : mword 5) (imm : mword 12) (m : regfile)
      (npc0 : SailStdpp.Values.mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    uint rd <> 0 ->
    (* the decode, in the two shapes its two consumers ask for *)
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t
         = Some (ITYPE (imm, Regidx rs1, Regidx rd, ADDI), t)) ->
    (forall rs : Riscv.rv64d_types.regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (ITYPE (imm, Regidx rs1, Regidx rd, ADDI), dst) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    gpr_file m -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pc_is (add_vec_int pc 4) -∗
       gpr_file (<[Regidx rd :=
                   regval_into_reg (add_vec (m !!! Regidx rs1)
                                      (sign_extend' 64 imm))]> m) -∗
       hart_ws cpu_id ws' -∗
       WP (Loop : expr weak_riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrd Hdecf Hagree HDmi Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hgf #Hbs Hhws Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    (* the funnel: certificate = nowrite at the fetch-only trace *)
    iApply (wwp_instr Φ pc false (ITYPE (imm, Regidx rs1, Regidx rd, ADDI))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc))
              wQ_pure Hgid Haccpc Hpmp
              (wcert_regonly al4 (fin_to_nat cpu_id) pc)
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false (ITYPE (imm, Regidx rs1, Regidx rd, ADDI))
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %Hws.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    iDestruct (winstr_flat σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hfok.
    iDestruct (winstr_pinned σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hpin.
    destruct Hfok as (_ & Hram & w' & [Hww HnotRVC] & Htext0). subst w'.
    assert (LmisaC : eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ)))
                       ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    (* ---- the SOURCE register, read off the file (x0-safe) ---- *)
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hgf") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 _
                 (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                 with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hgf".
    (* ---- premise (c): the execute mirror, at the CONFINED state ---- *)
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)))
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
      pose proof (exec_eff_execute_ITYPE_ADDI_gpr rs1 rd imm
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 4))) as He.
      replace (Z.eqb (uint rd) 0) with false in He
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      destruct (load_sexec_facts s0c b' (add_vec_int pc 4) rd
                  (regval_into_reg (gpr_addi_val rs1 imm
                     (set_reg (set_reg s0c (R_bool minstret_increment) b')
                        nextPC (add_vec_int pc 4)))))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    (* ---- the certificate's precondition ---- *)
    assert (HP : wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc) σ).
    { apply (wP_eff_of_leaf_regonly al4 (fin_to_nat cpu_id) σ (wwin pc pc 0)
               pc w (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) D dst).
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
    assert (Hav : gpr_addi_val rs1 imm
                    (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                       nextPC (add_vec_int pc 4))
                  = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
    { unfold gpr_addi_val.
      rewrite (gpr_src_peel_npc rs1
                 (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                 (add_vec_int pc 4)).
      rewrite Hrv. reflexivity. }
    pose proof (exec_eff_execute_ITYPE_ADDI_gpr rs1 rd imm
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 4))) as Hef.
    replace (Z.eqb (uint rd) 0) with false in Hef
      by (symmetry; apply Z.eqb_neq; exact Hrd).
    rewrite Hav in Hef.
    (* ---- the two register writes the [execute] performs ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iDestruct (gpr_file_insert_acc m (Regidx rd)
                 (regval_into_reg (add_vec (m !!! Regidx rs1)
                    (sign_extend' 64 imm))) with "Hgf") as "[Hrdc Hfins]".
    iEval (rewrite (gpr_pt_nz rd _ Hrd)) in "Hrdc".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hgf".
    { iEval (rewrite (gpr_pt_nz rd _ Hrd)). iExact "Hrdc". }
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4))
                     (R_bitvector_64 (gpr_of_Z (uint rd)))
                     (regval_into_reg (add_vec (m !!! Regidx rs1)
                        (sign_extend' 64 imm)))).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (load_sexec_facts (wflat_st σ) b (add_vec_int pc 4) rd
                (regval_into_reg (add_vec (m !!! Regidx rs1)
                   (sign_extend' 64 imm))))
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
              "[%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hgf Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

End leaf_addi.

(* ====================================================================== *)
(** ** 3. The SAME [ITYPE … ADDI], through a COMPRESSED decode

    [c.addi] / [c.li] / [c.addi4spn] all expand to [ITYPE (imm, rs1, rd,
    ADDI)], so ONE compressed leaf covers all three call-site shapes: the
    decode premises name the compressed intermediate [i0] and its
    state-generic [ExecuteAs] expansion, and the [execute] mirror is §2's,
    unchanged.  Two deltas against §2: the fetch reads ONE element at either
    alignment (so the certificate is [wcert_nowrite] at the single
    alignment-dependent read, not [WeakLeafRegOnly]'s two-arm trace) and the
    pc bump is 2. *)

Section leaf_addi_rvc.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Implicit Types Φ : mval -> iProp Σ.

  Lemma wwp_addi_rvc_leaf Φ (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (h : SailStdpp.Values.mword 16)
      (rs1 rd : mword 5) (imm : mword 12) (i0 : instruction) (m : regfile)
      (npc0 : SailStdpp.Values.mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp)
      (D D0 : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    uint rd <> 0 ->
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
            = Some (ExecuteAs (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)), s))) ->
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
       = Some (ExecuteAs (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)), s)) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    gpr_file m -∗
    winstr_bytes pc (F_RVC h) -∗
    hart_ws cpu_id ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pc_is (add_vec_int pc 2) -∗
       gpr_file (<[Regidx rd :=
                   regval_into_reg (add_vec (m !!! Regidx rs1)
                                      (sign_extend' 64 imm))]> m) -∗
       hart_ws cpu_id ws' -∗
       WP (Loop : expr weak_riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrd Hdecf Hagree HDmi Hgood Hdec Hgood0 Hexp.
    iIntros "Hmm Hpmpc Hpc Hnpc Hgf #Hbs Hhws Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    iApply (wwp_instr Φ pc true (ITYPE (imm, Regidx rs1, Regidx rd, ADDI))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id))
                 [WEread wak_plain pc (if al4 then 4%N else 2%N)])
              wQ_pure Hgid Haccpc Hpmp
              (wcert_nowrite (fin_to_nat cpu_id) pc
                 [WEread wak_plain pc (if al4 then 4%N else 2%N)]
                 (nowrite_read1 wak_plain pc (if al4 then 4%N else 2%N)))
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc true (ITYPE (imm, Regidx rs1, Regidx rd, ADDI))
                (F_RVC h) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %Hws.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    iDestruct (winstr_flat σ pc (F_RVC h) Hwf with "Hlat Hbs") as %Hfok.
    iDestruct (winstr_pinned σ pc (F_RVC h) Hwf with "Hlat Hbs") as %Hpin.
    destruct Hfok as (_ & Hram & w & [Hsub HisRVC] & Htext0).
    assert (LmisaC : eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ)))
                       ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    (* ---- the SOURCE register, read off the file (x0-safe) ---- *)
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hgf") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 _
                 (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                 with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hgf".
    (* ---- premise (c): the execute mirror, at the CONFINED state ---- *)
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)))
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
      pose proof (exec_eff_execute_ITYPE_ADDI_gpr rs1 rd imm
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 2))) as He.
      replace (Z.eqb (uint rd) 0) with false in He
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      destruct (load_sexec_facts s0c b' (add_vec_int pc 2) rd
                  (regval_into_reg (gpr_addi_val rs1 imm
                     (set_reg (set_reg s0c (R_bool minstret_increment) b')
                        nextPC (add_vec_int pc 2)))))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    (* ---- the certificate's precondition ---- *)
    assert (HP : wP_eff (Some (fin_to_nat cpu_id))
                   ([WEread wak_plain pc (if al4 then 4%N else 2%N)] ++ []) σ).
    { apply (wP_eff_of_leaf_rvc al4 (fin_to_nat cpu_id) σ (wwin pc pc 0)
               pc h w i0 (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) []
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
    assert (Hav : gpr_addi_val rs1 imm
                    (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                       nextPC (add_vec_int pc 2))
                  = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
    { unfold gpr_addi_val.
      rewrite (gpr_src_peel_npc rs1
                 (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                 (add_vec_int pc 2)).
      rewrite Hrv. reflexivity. }
    pose proof (exec_eff_execute_ITYPE_ADDI_gpr rs1 rd imm
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 2))) as Hef.
    replace (Z.eqb (uint rd) 0) with false in Hef
      by (symmetry; apply Z.eqb_neq; exact Hrd).
    rewrite Hav in Hef.
    (* ---- the two register writes the [execute] performs ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iDestruct (gpr_file_insert_acc m (Regidx rd)
                 (regval_into_reg (add_vec (m !!! Regidx rs1)
                    (sign_extend' 64 imm))) with "Hgf") as "[Hrdc Hfins]".
    iEval (rewrite (gpr_pt_nz rd _ Hrd)) in "Hrdc".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hgf".
    { iEval (rewrite (gpr_pt_nz rd _ Hrd)). iExact "Hrdc". }
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 2))
                     (R_bitvector_64 (gpr_of_Z (uint rd)))
                     (regval_into_reg (add_vec (m !!! Regidx rs1)
                        (sign_extend' 64 imm)))).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (load_sexec_facts (wflat_st σ) b (add_vec_int pc 2) rd
                (regval_into_reg (add_vec (m !!! Regidx rs1)
                   (sign_extend' 64 imm))))
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
              "[%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hgf Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

End leaf_addi_rvc.

(* ====================================================================== *)
(** ** 4. [ori rd, rs1, imm] — §2 with §1's mirror and [or_vec] *)

Section leaf_ori.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Implicit Types Φ : mval -> iProp Σ.

  Lemma wwp_ori_leaf Φ (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rs1 rd : mword 5) (imm : mword 12) (m : regfile)
      (npc0 : SailStdpp.Values.mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    uint rd <> 0 ->
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t
         = Some (ITYPE (imm, Regidx rs1, Regidx rd, ORI), t)) ->
    (forall rs : Riscv.rv64d_types.regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (ITYPE (imm, Regidx rs1, Regidx rd, ORI), dst) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    gpr_file m -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pc_is (add_vec_int pc 4) -∗
       gpr_file (<[Regidx rd :=
                   regval_into_reg (or_vec (m !!! Regidx rs1)
                                      (sign_extend' 64 imm))]> m) -∗
       hart_ws cpu_id ws' -∗
       WP (Loop : expr weak_riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrd Hdecf Hagree HDmi Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hgf #Hbs Hhws Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    iApply (wwp_instr Φ pc false (ITYPE (imm, Regidx rs1, Regidx rd, ORI))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc))
              wQ_pure Hgid Haccpc Hpmp
              (wcert_regonly al4 (fin_to_nat cpu_id) pc)
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false (ITYPE (imm, Regidx rs1, Regidx rd, ORI))
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %Hws.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    iDestruct (winstr_flat σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hfok.
    iDestruct (winstr_pinned σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hpin.
    destruct Hfok as (_ & Hram & w' & [Hww HnotRVC] & Htext0). subst w'.
    assert (LmisaC : eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ)))
                       ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hgf") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 _
                 (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                 with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hgf".
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (ITYPE (imm, Regidx rs1, Regidx rd, ORI)))
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
      pose proof (exec_eff_execute_ITYPE_ORI_gpr rs1 rd imm
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 4))) as He.
      replace (Z.eqb (uint rd) 0) with false in He
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      destruct (load_sexec_facts s0c b' (add_vec_int pc 4) rd
                  (regval_into_reg (gpr_ori_val rs1 imm
                     (set_reg (set_reg s0c (R_bool minstret_increment) b')
                        nextPC (add_vec_int pc 4)))))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    assert (HP : wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc) σ).
    { apply (wP_eff_of_leaf_regonly al4 (fin_to_nat cpu_id) σ (wwin pc pc 0)
               pc w (ITYPE (imm, Regidx rs1, Regidx rd, ORI)) D dst).
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
    assert (Hav : gpr_ori_val rs1 imm
                    (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                       nextPC (add_vec_int pc 4))
                  = or_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
    { unfold gpr_ori_val.
      rewrite (gpr_src_peel_npc rs1
                 (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                 (add_vec_int pc 4)).
      rewrite Hrv. reflexivity. }
    pose proof (exec_eff_execute_ITYPE_ORI_gpr rs1 rd imm
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 4))) as Hef.
    replace (Z.eqb (uint rd) 0) with false in Hef
      by (symmetry; apply Z.eqb_neq; exact Hrd).
    rewrite Hav in Hef.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iDestruct (gpr_file_insert_acc m (Regidx rd)
                 (regval_into_reg (or_vec (m !!! Regidx rs1)
                    (sign_extend' 64 imm))) with "Hgf") as "[Hrdc Hfins]".
    iEval (rewrite (gpr_pt_nz rd _ Hrd)) in "Hrdc".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (or_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hgf".
    { iEval (rewrite (gpr_pt_nz rd _ Hrd)). iExact "Hrdc". }
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4))
                     (R_bitvector_64 (gpr_of_Z (uint rd)))
                     (regval_into_reg (or_vec (m !!! Regidx rs1)
                        (sign_extend' 64 imm)))).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (load_sexec_facts (wflat_st σ) b (add_vec_int pc 4) rd
                (regval_into_reg (or_vec (m !!! Regidx rs1)
                   (sign_extend' 64 imm))))
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
              "[%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hgf Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

End leaf_ori.

(* ====================================================================== *)
(** ** 5. Soundness checks *)

Print Assumptions exec_eff_execute_ITYPE_ORI_gpr.
Print Assumptions gpr_src_peel_npc.
Print Assumptions gpr_src_at_flat.
Print Assumptions wwp_addi_leaf.
Print Assumptions wwp_addi_rvc_leaf.
Print Assumptions wwp_ori_leaf.
