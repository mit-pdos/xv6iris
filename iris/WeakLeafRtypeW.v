(** * WeakLeafRtypeW.v — the COMPRESSED register-only ALU leaves (M4,
      start()/timerinit() port)

    Four weak-tier leaves, all RVC-fetch and all GPR-FILE-based:

      [wwp_add_rvc_leaf]    — the RTYPE ADD reached through a compressed
                              decode.  ONE lemma covers BOTH [c.add rd,rs2]
                              (rd = rs1) and [c.mv rd,rs2] (rs1 = x0): the
                              leaf takes the whole [gpr_file m] (so rd = rs1
                              is expressible, which separate cells cannot do)
                              and reads its two sources with the x0-safe
                              [WpGpr.gpr_pt_value], which is exactly the
                              [rs1 = x0] arm.
      [wwp_or_rvc_leaf]     — the same for [c.or].
      [wwp_and_rvc_leaf]    — the same for [c.and].
      [wwp_addiw_rvc_leaf]  — [c.addiw] (rd = rs1 at the call site; the leaf
                              is generic, like its SC twin).

    Each statement is its SC twin ([WpMmodeRtype.wp_add_gpr] / [wp_or_gpr] /
    [wp_and_gpr], [WpMmodeAddiw.wp_addiw_gpr]) under the porting table's
    swaps — [instr] → [winstr_bytes pc (F_RVC h)] plus the compressed decode
    premise pack, [kmap_static] dropped, [gen_id]/alignment/[hart_ws] added,
    [riscv_lang] → [weak_riscv_lang], pc bump 2 — and each proof is the plain
    funnel recipe of [WeakLeafCsrw2.wwp_csrw_medeleg_leaf] with
    [WeakLeafTor.wwp_ld8_tor_rvc_leaf]'s F_RVC fetch machinery
    ([WeakLeafTor.wP_eff_of_leaf_rvc] at [es_x := []]) and the gpr-file moves
    of [WkEntryNew.v]'s AUIPC / c.add blocks.

    §1 is the three missing [execute] mirrors (RTYPE OR, RTYPE AND, ADDIW),
    each a name-swap of [WkEntryEff.exec_eff_execute_RTYPE_ADD_gpr] against
    the SC lemma the corresponding [Wp*] leaf uses
    ([WpMmodeLeafBase.exec_execute_RTYPE_OR_gpr] / [_AND_gpr] /
    [exec_execute_ADDIW_gpr]); every trace is [[]].  The ADD mirror already
    exists and is reused.

    Import discipline: NO [SailStdpp.Base] (the [Countable Arch.pa]
    binder-position trap) and no new [gset Arch.pa] — every window here is
    [WeakLeafWin.wwin pc pc 0], the text-only window. *)
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
(* the shared window kit ([wwin], [leaf_peel], [reg_at_flat],
   [load_sexec_facts]) *)
Require Import WeakLeafWin.
(* the alignment-union COMPRESSED recipe [wP_eff_of_leaf_rvc] *)
Require Import WeakLeafTor.
(* [exec_eff_execute_RTYPE_ADD_gpr] — the ADD mirror, already landed *)
Require Import WkEntryEff.

Import SailStdpp.Values.
Import Defs.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. THE THREE MISSING [execute] MIRRORS

    Clones of [WkEntryEff.exec_eff_execute_RTYPE_ADD_gpr]'s script against
    the SC lemmas [WpMmodeRtype]/[WpMmodeAddiw] use.  State-generic, trace
    [[]] — so ONE lemma serves the funnel's flat instantiation and the
    certificate's confined one (at every [b]). *)

Lemma exec_eff_execute_RTYPE_OR_gpr (rs2 rs1 rd : mword 5) s :
  exec_eff (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_or_val rs2 rs1 s)),
          []).
Proof.
  change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)))
    with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) OR).
  unfold execute_RTYPE, gpr_or_val. cbn match.
  rewrite (exec_eff_bind_nil _ _ _
             (or_vec
                (if Z.eqb (uint rs1) 0 then zero_reg
                 else register_lookup
                        (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                (if Z.eqb (uint rs2) 0 then zero_reg
                 else register_lookup
                        (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))) s).
  2:{ rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_rX_bits_gpr rs1 s)).
      rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_rX_bits_gpr rs2 s)).
      apply exec_eff_returnm. }
  rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_wX_bits_gpr rd _ s)).
  apply exec_eff_returnm.
Qed.

Lemma exec_eff_execute_RTYPE_AND_gpr (rs2 rs1 rd : mword 5) s :
  exec_eff (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_and_val rs2 rs1 s)),
          []).
Proof.
  change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND)))
    with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) AND).
  unfold execute_RTYPE, gpr_and_val. cbn match.
  rewrite (exec_eff_bind_nil _ _ _
             (and_vec
                (if Z.eqb (uint rs1) 0 then zero_reg
                 else register_lookup
                        (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                (if Z.eqb (uint rs2) 0 then zero_reg
                 else register_lookup
                        (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))) s).
  2:{ rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_rX_bits_gpr rs1 s)).
      rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_rX_bits_gpr rs2 s)).
      apply exec_eff_returnm. }
  rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_wX_bits_gpr rd _ s)).
  apply exec_eff_returnm.
Qed.

(** [execute_ADDIW] is a standalone definition (no [rop] match), so the
    spine is the ADDI mirror's minus the outer match: one [rX_bits], the
    32-bit truncate-and-sign-extend, one [wX_bits]. *)
Lemma exec_eff_execute_ADDIW_gpr (rs1 rd : mword 5) (imm : mword 12) s :
  exec_eff (execute (ADDIW (imm, Regidx rs1, Regidx rd))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_addiw_val rs1 imm s)),
          []).
Proof.
  change (execute (ADDIW (imm, Regidx rs1, Regidx rd)))
    with (execute_ADDIW imm (Regidx rs1) (Regidx rd)).
  unfold execute_ADDIW, gpr_addiw_val. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_rX_bits_gpr rs1 s)).
  rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_wX_bits_gpr rd _ s)).
  apply exec_eff_returnm.
Qed.

(* ====================================================================== *)
(** ** 2. THE FOUR LEAVES *)

Section leaves.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (** *** 2a. [c.add] / [c.mv] — the RTYPE ADD leaf. *)

  Lemma wwp_add_rvc_leaf (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (h : SailStdpp.Values.mword 16)
      (rs2 rs1 rd : mword 5) (i0 : instruction) (m : regfile)
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
            = Some (ExecuteAs
                      (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)), s))) ->
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
       = Some (ExecuteAs (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)), s)) ->
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
          regval_into_reg (add_vec (m !!! Regidx rs1) (m !!! Regidx rs2))]> m) -∗
       hart_ws cpu_id ws' -∗
       WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrd Hdecf Hagree HDmi Hgood Hdec Hgood0 Hexp.
    iIntros "Hmm Hpmpc Hpc Hnpc Hfile #Hbs Hhws Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    iApply (wwp_instr pc true (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id))
                 [WEread wak_plain pc (if al4 then 4%N else 2%N)])
              wQ_pure Hgid Haccpc Hpmp
              (wcert_nowrite (fin_to_nat cpu_id) pc
                 [WEread wak_plain pc (if al4 then 4%N else 2%N)]
                 (nowrite_read1 wak_plain pc (if al4 then 4%N else 2%N)))
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc true
                (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD))
                (F_RVC h) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %Hws.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    assert (LmisaC : eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ)))
                       ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    iDestruct (winstr_flat σ pc (F_RVC h) Hwf with "Hlat Hbs") as %Hfok.
    iDestruct (winstr_pinned σ pc (F_RVC h) Hwf with "Hlat Hbs") as %Hpin.
    destruct Hfok as (_ & Hram & w & [Hsub HisRVC] & Htext0).
    assert (Hag : forall r, D r = true ->
              register_lookup r (wm_regs σ) = register_lookup r dst.(sregs))
      by (apply Hagree; [exact Lpriv | exact Lmisa | exact Lsec]).
    (* ---- premise (c): the execute mirror, at the CONFINED state ---- *)
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)))
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
      pose proof (exec_eff_execute_RTYPE_ADD_gpr rs2 rs1 rd
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 2))) as He.
      replace (Z.eqb (uint rd) 0) with false in He
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      destruct (load_sexec_facts s0c b' (add_vec_int pc 2) rd
                  (regval_into_reg (gpr_rd_val rs2 rs1
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
                   [WEread wak_plain pc (if al4 then 4%N else 2%N)] σ).
    { change ([WEread wak_plain pc (if al4 then 4%N else 2%N)])
        with ([WEread wak_plain pc (if al4 then 4%N else 2%N)]
                ++ (@nil weff)).
      apply (wP_eff_of_leaf_rvc al4 (fin_to_nat cpu_id) σ (wwin pc pc 0)
               pc h w i0 (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD))
               [] D D0 dst).
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
      - exact Hag.
      - exact HDmi.
      - exact Hgood.
      - exact Hdec.
      - exact Hgood0.
      - exact Hexp.
      - exact Hc. }
    (* ---- the nextPC pre-write, then the TWO source reads ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1))
                 (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                    nextPC (add_vec_int pc 2)) with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    iDestruct (gpr_file_lookup_acc m (Regidx rs2) with "Hfile") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m (Regidx rs2))
                 (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                    nextPC (add_vec_int pc 2)) with "Hreg Hr2c") as %Hrv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfile".
    assert (Hval : gpr_rd_val rs2 rs1
                     (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 2))
                   = add_vec (m !!! Regidx rs1) (m !!! Regidx rs2)).
    { unfold gpr_rd_val. rewrite Hrv1. rewrite Hrv2. reflexivity. }
    (* ---- the run at the FLAT state ---- *)
    pose proof (exec_eff_execute_RTYPE_ADD_gpr rs2 rs1 rd
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 2))) as Hef.
    replace (Z.eqb (uint rd) 0) with false in Hef
      by (symmetry; apply Z.eqb_neq; exact Hrd).
    rewrite Hval in Hef.
    (* ---- the rd write ---- *)
    iDestruct (gpr_file_insert_acc m (Regidx rd)
                 (regval_into_reg
                    (add_vec (m !!! Regidx rs1) (m !!! Regidx rs2)))
                 with "Hfile") as "[Hrdc Hfins]".
    iEval (rewrite (gpr_pt_nz rd _ Hrd)) in "Hrdc".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg
               (add_vec (m !!! Regidx rs1) (m !!! Regidx rs2)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
    { iEval (rewrite (gpr_pt_nz rd _ Hrd)). iExact "Hrdc". }
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 2))
                     (R_bitvector_64 (gpr_of_Z (uint rd)))
                     (regval_into_reg
                        (add_vec (m !!! Regidx rs1) (m !!! Regidx rs2)))).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (load_sexec_facts (wflat_st σ) b (add_vec_int pc 2) rd
                (regval_into_reg
                   (add_vec (m !!! Regidx rs1) (m !!! Regidx rs2))))
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
              "[%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hfile Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

  (** *** 2b. [c.or] — the RTYPE OR leaf (2a with [or_vec]). *)

  Lemma wwp_or_rvc_leaf (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (h : SailStdpp.Values.mword 16)
      (rs2 rs1 rd : mword 5) (i0 : instruction) (m : regfile)
      (npc0 : SailStdpp.Values.mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp)
      (D D0 : register -> bool) (dst : mstate) (ws : wstate) :
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
       exists i0' : instruction,
         exec (decode_fetch (F_RVC h)) t = Some (i0', t) /\
         is_lpad_instruction i0' = false /\
         (forall s : mstate, exec (execute i0') s
            = Some (ExecuteAs
                      (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)), s))) ->
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
       = Some (ExecuteAs (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)), s)) ->
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
          regval_into_reg (or_vec (m !!! Regidx rs1) (m !!! Regidx rs2))]> m) -∗
       hart_ws cpu_id ws' -∗
       WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrd Hdecf Hagree HDmi Hgood Hdec Hgood0 Hexp.
    iIntros "Hmm Hpmpc Hpc Hnpc Hfile #Hbs Hhws Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    iApply (wwp_instr pc true (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id))
                 [WEread wak_plain pc (if al4 then 4%N else 2%N)])
              wQ_pure Hgid Haccpc Hpmp
              (wcert_nowrite (fin_to_nat cpu_id) pc
                 [WEread wak_plain pc (if al4 then 4%N else 2%N)]
                 (nowrite_read1 wak_plain pc (if al4 then 4%N else 2%N)))
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc true
                (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR))
                (F_RVC h) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %Hws.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    assert (LmisaC : eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ)))
                       ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    iDestruct (winstr_flat σ pc (F_RVC h) Hwf with "Hlat Hbs") as %Hfok.
    iDestruct (winstr_pinned σ pc (F_RVC h) Hwf with "Hlat Hbs") as %Hpin.
    destruct Hfok as (_ & Hram & w & [Hsub HisRVC] & Htext0).
    assert (Hag : forall r, D r = true ->
              register_lookup r (wm_regs σ) = register_lookup r dst.(sregs))
      by (apply Hagree; [exact Lpriv | exact Lmisa | exact Lsec]).
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)))
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
      pose proof (exec_eff_execute_RTYPE_OR_gpr rs2 rs1 rd
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 2))) as He.
      replace (Z.eqb (uint rd) 0) with false in He
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      destruct (load_sexec_facts s0c b' (add_vec_int pc 2) rd
                  (regval_into_reg (gpr_or_val rs2 rs1
                     (set_reg (set_reg s0c (R_bool minstret_increment) b')
                        nextPC (add_vec_int pc 2)))))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    assert (HP : wP_eff (Some (fin_to_nat cpu_id))
                   [WEread wak_plain pc (if al4 then 4%N else 2%N)] σ).
    { change ([WEread wak_plain pc (if al4 then 4%N else 2%N)])
        with ([WEread wak_plain pc (if al4 then 4%N else 2%N)]
                ++ (@nil weff)).
      apply (wP_eff_of_leaf_rvc al4 (fin_to_nat cpu_id) σ (wwin pc pc 0)
               pc h w i0 (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR))
               [] D D0 dst).
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
      - exact Hag.
      - exact HDmi.
      - exact Hgood.
      - exact Hdec.
      - exact Hgood0.
      - exact Hexp.
      - exact Hc. }
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1))
                 (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                    nextPC (add_vec_int pc 2)) with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    iDestruct (gpr_file_lookup_acc m (Regidx rs2) with "Hfile") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m (Regidx rs2))
                 (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                    nextPC (add_vec_int pc 2)) with "Hreg Hr2c") as %Hrv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfile".
    assert (Hval : gpr_or_val rs2 rs1
                     (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 2))
                   = or_vec (m !!! Regidx rs1) (m !!! Regidx rs2)).
    { unfold gpr_or_val. rewrite Hrv1. rewrite Hrv2. reflexivity. }
    pose proof (exec_eff_execute_RTYPE_OR_gpr rs2 rs1 rd
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 2))) as Hef.
    replace (Z.eqb (uint rd) 0) with false in Hef
      by (symmetry; apply Z.eqb_neq; exact Hrd).
    rewrite Hval in Hef.
    iDestruct (gpr_file_insert_acc m (Regidx rd)
                 (regval_into_reg
                    (or_vec (m !!! Regidx rs1) (m !!! Regidx rs2)))
                 with "Hfile") as "[Hrdc Hfins]".
    iEval (rewrite (gpr_pt_nz rd _ Hrd)) in "Hrdc".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg
               (or_vec (m !!! Regidx rs1) (m !!! Regidx rs2)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
    { iEval (rewrite (gpr_pt_nz rd _ Hrd)). iExact "Hrdc". }
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 2))
                     (R_bitvector_64 (gpr_of_Z (uint rd)))
                     (regval_into_reg
                        (or_vec (m !!! Regidx rs1) (m !!! Regidx rs2)))).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (load_sexec_facts (wflat_st σ) b (add_vec_int pc 2) rd
                (regval_into_reg
                   (or_vec (m !!! Regidx rs1) (m !!! Regidx rs2))))
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
              "[%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hfile Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

  (** *** 2c. [c.and] — the RTYPE AND leaf (2a with [and_vec]). *)

  Lemma wwp_and_rvc_leaf (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (h : SailStdpp.Values.mword 16)
      (rs2 rs1 rd : mword 5) (i0 : instruction) (m : regfile)
      (npc0 : SailStdpp.Values.mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp)
      (D D0 : register -> bool) (dst : mstate) (ws : wstate) :
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
       exists i0' : instruction,
         exec (decode_fetch (F_RVC h)) t = Some (i0', t) /\
         is_lpad_instruction i0' = false /\
         (forall s : mstate, exec (execute i0') s
            = Some (ExecuteAs
                      (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND)), s))) ->
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
       = Some (ExecuteAs (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND)), s)) ->
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
          regval_into_reg (and_vec (m !!! Regidx rs1) (m !!! Regidx rs2))]> m) -∗
       hart_ws cpu_id ws' -∗
       WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrd Hdecf Hagree HDmi Hgood Hdec Hgood0 Hexp.
    iIntros "Hmm Hpmpc Hpc Hnpc Hfile #Hbs Hhws Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    iApply (wwp_instr pc true (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id))
                 [WEread wak_plain pc (if al4 then 4%N else 2%N)])
              wQ_pure Hgid Haccpc Hpmp
              (wcert_nowrite (fin_to_nat cpu_id) pc
                 [WEread wak_plain pc (if al4 then 4%N else 2%N)]
                 (nowrite_read1 wak_plain pc (if al4 then 4%N else 2%N)))
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc true
                (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND))
                (F_RVC h) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %Hws.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    assert (LmisaC : eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ)))
                       ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    iDestruct (winstr_flat σ pc (F_RVC h) Hwf with "Hlat Hbs") as %Hfok.
    iDestruct (winstr_pinned σ pc (F_RVC h) Hwf with "Hlat Hbs") as %Hpin.
    destruct Hfok as (_ & Hram & w & [Hsub HisRVC] & Htext0).
    assert (Hag : forall r, D r = true ->
              register_lookup r (wm_regs σ) = register_lookup r dst.(sregs))
      by (apply Hagree; [exact Lpriv | exact Lmisa | exact Lsec]).
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND)))
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
      pose proof (exec_eff_execute_RTYPE_AND_gpr rs2 rs1 rd
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 2))) as He.
      replace (Z.eqb (uint rd) 0) with false in He
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      destruct (load_sexec_facts s0c b' (add_vec_int pc 2) rd
                  (regval_into_reg (gpr_and_val rs2 rs1
                     (set_reg (set_reg s0c (R_bool minstret_increment) b')
                        nextPC (add_vec_int pc 2)))))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    assert (HP : wP_eff (Some (fin_to_nat cpu_id))
                   [WEread wak_plain pc (if al4 then 4%N else 2%N)] σ).
    { change ([WEread wak_plain pc (if al4 then 4%N else 2%N)])
        with ([WEread wak_plain pc (if al4 then 4%N else 2%N)]
                ++ (@nil weff)).
      apply (wP_eff_of_leaf_rvc al4 (fin_to_nat cpu_id) σ (wwin pc pc 0)
               pc h w i0 (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND))
               [] D D0 dst).
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
      - exact Hag.
      - exact HDmi.
      - exact Hgood.
      - exact Hdec.
      - exact Hgood0.
      - exact Hexp.
      - exact Hc. }
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1))
                 (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                    nextPC (add_vec_int pc 2)) with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    iDestruct (gpr_file_lookup_acc m (Regidx rs2) with "Hfile") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m (Regidx rs2))
                 (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                    nextPC (add_vec_int pc 2)) with "Hreg Hr2c") as %Hrv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfile".
    assert (Hval : gpr_and_val rs2 rs1
                     (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 2))
                   = and_vec (m !!! Regidx rs1) (m !!! Regidx rs2)).
    { unfold gpr_and_val. rewrite Hrv1. rewrite Hrv2. reflexivity. }
    pose proof (exec_eff_execute_RTYPE_AND_gpr rs2 rs1 rd
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 2))) as Hef.
    replace (Z.eqb (uint rd) 0) with false in Hef
      by (symmetry; apply Z.eqb_neq; exact Hrd).
    rewrite Hval in Hef.
    iDestruct (gpr_file_insert_acc m (Regidx rd)
                 (regval_into_reg
                    (and_vec (m !!! Regidx rs1) (m !!! Regidx rs2)))
                 with "Hfile") as "[Hrdc Hfins]".
    iEval (rewrite (gpr_pt_nz rd _ Hrd)) in "Hrdc".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg
               (and_vec (m !!! Regidx rs1) (m !!! Regidx rs2)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
    { iEval (rewrite (gpr_pt_nz rd _ Hrd)). iExact "Hrdc". }
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 2))
                     (R_bitvector_64 (gpr_of_Z (uint rd)))
                     (regval_into_reg
                        (and_vec (m !!! Regidx rs1) (m !!! Regidx rs2)))).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (load_sexec_facts (wflat_st σ) b (add_vec_int pc 2) rd
                (regval_into_reg
                   (and_vec (m !!! Regidx rs1) (m !!! Regidx rs2))))
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
              "[%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hfile Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

  (** *** 2d. [c.addiw] — the ADDIW leaf (ONE source, the 32-bit
      truncate-and-sign-extend result). *)

  Lemma wwp_addiw_rvc_leaf (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (h : SailStdpp.Values.mword 16)
      (rs1 rd : mword 5) (immv : mword 12) (i0 : instruction) (m : regfile)
      (npc0 : SailStdpp.Values.mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp)
      (D D0 : register -> bool) (dst : mstate) (ws : wstate) :
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
       exists i0' : instruction,
         exec (decode_fetch (F_RVC h)) t = Some (i0', t) /\
         is_lpad_instruction i0' = false /\
         (forall s : mstate, exec (execute i0') s
            = Some (ExecuteAs (ADDIW (immv, Regidx rs1, Regidx rd)), s))) ->
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
       = Some (ExecuteAs (ADDIW (immv, Regidx rs1, Regidx rd)), s)) ->
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
          regval_into_reg (sign_extend' 64
            (subrange_vec_dec
               (add_vec (m !!! Regidx rs1) (sign_extend' 64 immv)) 31 0))]> m) -∗
       hart_ws cpu_id ws' -∗
       WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrd Hdecf Hagree HDmi Hgood Hdec Hgood0 Hexp.
    iIntros "Hmm Hpmpc Hpc Hnpc Hfile #Hbs Hhws Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    iApply (wwp_instr pc true (ADDIW (immv, Regidx rs1, Regidx rd))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id))
                 [WEread wak_plain pc (if al4 then 4%N else 2%N)])
              wQ_pure Hgid Haccpc Hpmp
              (wcert_nowrite (fin_to_nat cpu_id) pc
                 [WEread wak_plain pc (if al4 then 4%N else 2%N)]
                 (nowrite_read1 wak_plain pc (if al4 then 4%N else 2%N)))
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc true (ADDIW (immv, Regidx rs1, Regidx rd))
                (F_RVC h) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %Hws.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    assert (LmisaC : eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ)))
                       ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    iDestruct (winstr_flat σ pc (F_RVC h) Hwf with "Hlat Hbs") as %Hfok.
    iDestruct (winstr_pinned σ pc (F_RVC h) Hwf with "Hlat Hbs") as %Hpin.
    destruct Hfok as (_ & Hram & w & [Hsub HisRVC] & Htext0).
    assert (Hag : forall r, D r = true ->
              register_lookup r (wm_regs σ) = register_lookup r dst.(sregs))
      by (apply Hagree; [exact Lpriv | exact Lmisa | exact Lsec]).
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (ADDIW (immv, Regidx rs1, Regidx rd)))
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
      pose proof (exec_eff_execute_ADDIW_gpr rs1 rd immv
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 2))) as He.
      replace (Z.eqb (uint rd) 0) with false in He
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      destruct (load_sexec_facts s0c b' (add_vec_int pc 2) rd
                  (regval_into_reg (gpr_addiw_val rs1 immv
                     (set_reg (set_reg s0c (R_bool minstret_increment) b')
                        nextPC (add_vec_int pc 2)))))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    assert (HP : wP_eff (Some (fin_to_nat cpu_id))
                   [WEread wak_plain pc (if al4 then 4%N else 2%N)] σ).
    { change ([WEread wak_plain pc (if al4 then 4%N else 2%N)])
        with ([WEread wak_plain pc (if al4 then 4%N else 2%N)]
                ++ (@nil weff)).
      apply (wP_eff_of_leaf_rvc al4 (fin_to_nat cpu_id) σ (wwin pc pc 0)
               pc h w i0 (ADDIW (immv, Regidx rs1, Regidx rd))
               [] D D0 dst).
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
      - exact Hag.
      - exact HDmi.
      - exact Hgood.
      - exact Hdec.
      - exact Hgood0.
      - exact Hexp.
      - exact Hc. }
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1))
                 (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                    nextPC (add_vec_int pc 2)) with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    assert (Hval : gpr_addiw_val rs1 immv
                     (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 2))
                   = sign_extend' 64
                       (subrange_vec_dec
                          (add_vec (m !!! Regidx rs1)
                             (sign_extend' 64 immv)) 31 0)).
    { unfold gpr_addiw_val. rewrite Hrv1. reflexivity. }
    pose proof (exec_eff_execute_ADDIW_gpr rs1 rd immv
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 2))) as Hef.
    replace (Z.eqb (uint rd) 0) with false in Hef
      by (symmetry; apply Z.eqb_neq; exact Hrd).
    rewrite Hval in Hef.
    iDestruct (gpr_file_insert_acc m (Regidx rd)
                 (regval_into_reg (sign_extend' 64
                    (subrange_vec_dec
                       (add_vec (m !!! Regidx rs1)
                          (sign_extend' 64 immv)) 31 0)))
                 with "Hfile") as "[Hrdc Hfins]".
    iEval (rewrite (gpr_pt_nz rd _ Hrd)) in "Hrdc".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (sign_extend' 64
               (subrange_vec_dec
                  (add_vec (m !!! Regidx rs1) (sign_extend' 64 immv)) 31 0)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
    { iEval (rewrite (gpr_pt_nz rd _ Hrd)). iExact "Hrdc". }
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 2))
                     (R_bitvector_64 (gpr_of_Z (uint rd)))
                     (regval_into_reg (sign_extend' 64
                        (subrange_vec_dec
                           (add_vec (m !!! Regidx rs1)
                              (sign_extend' 64 immv)) 31 0)))).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (load_sexec_facts (wflat_st σ) b (add_vec_int pc 2) rd
                (regval_into_reg (sign_extend' 64
                   (subrange_vec_dec
                      (add_vec (m !!! Regidx rs1) (sign_extend' 64 immv))
                      31 0))))
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
              "[%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hfile Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

End leaves.

(* ====================================================================== *)
(** ** 3. Soundness check *)

Print Assumptions exec_eff_execute_RTYPE_OR_gpr.
Print Assumptions exec_eff_execute_RTYPE_AND_gpr.
Print Assumptions exec_eff_execute_ADDIW_gpr.
Print Assumptions wwp_add_rvc_leaf.
Print Assumptions wwp_or_rvc_leaf.
Print Assumptions wwp_and_rvc_leaf.
Print Assumptions wwp_addiw_rvc_leaf.
