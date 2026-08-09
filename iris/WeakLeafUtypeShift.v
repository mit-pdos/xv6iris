(** * WeakLeafUtypeShift.v — the weak UTYPE and shift-immediate GPR-FILE
      leaves (M4, the [start()]/[timerinit()] port)

    Five register-only leaves on the PLAIN funnel ([WeakFunnel.wwp_instr]),
    all stated over the WHOLE [WpGpr.gpr_file] rather than per-register
    cells, because nearly every call site in [start()]/[timerinit()] has
    [rd = rs1] (the shift-immediates always do — they come from [c.slli] /
    [c.srli]) or [rs1 = x0], and separate cells cannot express that:

      §2  [wwp_lui_leaf]       — [F_Base] LUI  (mirror of
                                 [WpMmodeUtype.wp_lui_gpr]);
      §3  [wwp_lui_rvc_leaf]   — the SAME AST reached by a COMPRESSED decode
                                 (covers [c.lui]);
      §4  [wwp_auipc_leaf]     — [F_Base] AUIPC (mirror of
                                 [WpMmodeUtype.wp_auipc_gpr]); this is
                                 [WkEntryNew]'s inline [_entry] AUIPC block,
                                 hoisted to a reusable leaf;
      §5  [wwp_slli_rvc_leaf]  — [c.slli] (mirror of
                                 [WpMmodeShiftiop.wp_slli_gpr]);
      §6  [wwp_srli_rvc_leaf]  — [c.srli] (mirror of
                                 [WpMmodeShiftiop.wp_srli_gpr]).

    Every leaf takes the fetch alignment [al4 : bool] as a parameter and so
    covers both the 4-aligned and the 2-not-4-aligned call sites with ONE
    statement: the [F_Base] pair goes through
    [WeakLeafRegOnly.wP_eff_of_leaf_regonly] (+ [wcert_regonly]), the
    compressed three through [WeakLeafTor.wP_eff_of_leaf_rvc] at [es_x := []]
    (+ [WeakEff.wcert_nowrite] at the one-element fetch trace, whose width is
    the only thing [al4] decides).

    The per-leaf price is the porting guide §2g recipe with the CSR plumbing
    of [WeakLeafCsrw2.wwp_csrw_medeleg_leaf] (the plain-funnel template)
    replaced by the gpr-file moves demonstrated in [WkEntryNew.v]:
    [gpr_file_lookup_acc] + [gpr_pt_value] to read a source register
    (x0-safe), [gpr_file_insert_acc] + [gpr_pt_nz] + [reg_update] to write
    [rd].  The [execute] mirrors of LUI / AUIPC are [WkEntryEff]'s; the two
    SHIFTIOP mirrors are §1 below (name-swaps of
    [WpMmodeShiftiop.exec_execute_SHIFTIOP_{SLLI,SRLI}_gpr] against the
    [exec_eff] kit, trace [[]]). *)
From Stdlib Require Import ZArith Zquot Zwf.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterface.
(* DELIBERATELY NOT [Require Import SailStdpp.Base] / no [gset Arch.pa]
   binder: the Countable-instance trap (porting guide §4.11a).  Every window
   here is [WeakLeafWin.wwin] and every recipe's window binder is [W : _]. *)
Require Import SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
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
Require Import WeakLeafWin.
Require Import ExecCommon WpDecode.
(* the SC leaves these five mirror, and the SC [execute] value functions
   ([luival], [auipc_off], [gpr_slli_val], [gpr_srli_val]) *)
Require Import WpMmodeUtype WpMmodeShiftiop.
(* the two alignment-union recipes + the register-only certificate *)
Require Import WeakLeafRegOnly WeakLeafTor.
(* the LUI / AUIPC [exec_eff] mirrors *)
Require Import WkEntryEff.

Import SailStdpp.Values.
Import Defs.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. THE TWO MISSING [execute] MIRRORS: SHIFTIOP SLLI / SRLI

    [WkEntryEff.exec_eff_execute_ITYPE_ADDI_gpr]'s script against
    [WpMmodeShiftiop]'s SC exec lemmas: one bind for the source read + the
    shift, one [bind0] for the [rd] write.  Both are STATE-GENERIC and their
    trace is [[]] — a shift-immediate touches no memory — so one lemma
    serves the funnel's flat instantiation and the certificate's confined
    one. *)

Lemma exec_eff_execute_SHIFTIOP_SLLI_gpr (rs1 rd : mword 5) (shamt : mword 6)
    s :
  exec_eff (execute (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_slli_val rs1 shamt s)),
          []).
Proof.
  change (execute (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI)))
    with (execute_SHIFTIOP shamt (Regidx rs1) (Regidx rd) SLLI).
  unfold execute_SHIFTIOP, gpr_slli_val, gpr_src. cbn match.
  rewrite (exec_eff_bind_nil _ _ _
             (shift_bits_left
                (if Z.eqb (uint rs1) 0 then zero_reg
                 else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                        s.(sregs))
                (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)) s).
  2:{ rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_rX_bits_gpr rs1 s)).
      apply exec_eff_returnm. }
  rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_wX_bits_gpr rd _ s)).
  apply exec_eff_returnm.
Qed.

Lemma exec_eff_execute_SHIFTIOP_SRLI_gpr (rs1 rd : mword 5) (shamt : mword 6)
    s :
  exec_eff (execute (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_srli_val rs1 shamt s)),
          []).
Proof.
  change (execute (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI)))
    with (execute_SHIFTIOP shamt (Regidx rs1) (Regidx rd) SRLI).
  unfold execute_SHIFTIOP, gpr_srli_val, gpr_src. cbn match.
  rewrite (exec_eff_bind_nil _ _ _
             (shift_bits_right
                (if Z.eqb (uint rs1) 0 then zero_reg
                 else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                        s.(sregs))
                (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)) s).
  2:{ rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_rX_bits_gpr rs1 s)).
      apply exec_eff_returnm. }
  rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_wX_bits_gpr rd _ s)).
  apply exec_eff_returnm.
Qed.

(* ====================================================================== *)
(** ** 2. [lui] — [F_Base] fetch, alignment-generic

    Statement = [WpMmodeUtype.wp_lui_gpr] at [is_rvc := false] under the
    porting-table swaps ([instr] → [winstr_bytes] + the decode premise pack;
    [boot_static] DROPPED; [gen_id]/alignment/[hart_ws] added). *)

Section leaf_lui.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Implicit Types Φ : mval -> iProp Σ.

  Lemma wwp_lui_leaf Φ (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rd : mword 5) (imm : mword 20) (m : regfile)
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
         = Some (UTYPE (imm, Regidx rd, LUI), t)) ->
    (forall rs : Riscv.rv64d_types.regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst = Some (UTYPE (imm, Regidx rd, LUI), dst) ->
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
       gpr_file (<[Regidx rd := regval_into_reg (luival imm)]> m) -∗
       hart_ws cpu_id ws' -∗
       WP (Loop : expr weak_riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrdnz Hdecf Hagree HDmi Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hfile #Hbs Hhws Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    iApply (wwp_instr Φ pc false (UTYPE (imm, Regidx rd, LUI))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc))
              wQ_pure Hgid Haccpc Hpmp
              (wcert_regonly al4 (fin_to_nat cpu_id) pc)
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false (UTYPE (imm, Regidx rd, LUI))
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
    (* ---- premise (c): the execute mirror, at the CONFINED state ---- *)
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (UTYPE (imm, Regidx rd, LUI)))
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
      pose proof (exec_eff_execute_UTYPE_LUI_gpr rd imm
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 4))) as He.
      replace (Z.eqb (uint rd) 0) with false in He
        by (symmetry; apply Z.eqb_neq; exact Hrdnz).
      destruct (load_sexec_facts s0c b' (add_vec_int pc 4) rd
                  (regval_into_reg (luival imm)))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    (* ---- the certificate's precondition ---- *)
    assert (HP : wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc) σ).
    { apply (wP_eff_of_leaf_regonly al4 (fin_to_nat cpu_id) σ (wwin pc pc 0)
               pc w (UTYPE (imm, Regidx rd, LUI)) D dst).
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
    pose proof (exec_eff_execute_UTYPE_LUI_gpr rd imm
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 4))) as Hef.
    replace (Z.eqb (uint rd) 0) with false in Hef
      by (symmetry; apply Z.eqb_neq; exact Hrdnz).
    (* ---- the two register writes the [execute] performs ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iDestruct (gpr_file_insert_acc m (Regidx rd)
                 (regval_into_reg (luival imm)) with "Hfile") as "[Hrdc Hfins]".
    iEval (rewrite (gpr_pt_nz rd _ Hrdnz)) in "Hrdc".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (luival imm)) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
    { iEval (rewrite (gpr_pt_nz rd _ Hrdnz)). iExact "Hrdc". }
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4))
                     (R_bitvector_64 (gpr_of_Z (uint rd)))
                     (regval_into_reg (luival imm))).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (load_sexec_facts (wflat_st σ) b (add_vec_int pc 4) rd
                (regval_into_reg (luival imm))) as (G1 & G2 & G3 & G4 & G5).
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

End leaf_lui.

(* ====================================================================== *)
(** ** 3. [c.lui] — the SAME UTYPE LUI ast through a COMPRESSED decode

    §2's leaf on [WeakLeafTor.wP_eff_of_leaf_rvc] at [es_x := []]: the decode
    premise pack gains the intermediate compressed instruction [i0] with its
    [goodb0] witness ([D0]) and its state-generic [ExecuteAs] expansion, the
    certificate is [wcert_nowrite] at the ONE-element fetch trace (whose
    width [al4] decides), and the pc bump is 2. *)

Section leaf_lui_rvc.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Implicit Types Φ : mval -> iProp Σ.

  Lemma wwp_lui_rvc_leaf Φ (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (h : SailStdpp.Values.mword 16)
      (rd : mword 5) (imm : mword 20) (i0 : instruction) (m : regfile)
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
            = Some (ExecuteAs (UTYPE (imm, Regidx rd, LUI)), s))) ->
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
       = Some (ExecuteAs (UTYPE (imm, Regidx rd, LUI)), s)) ->
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
       gpr_file (<[Regidx rd := regval_into_reg (luival imm)]> m) -∗
       hart_ws cpu_id ws' -∗
       WP (Loop : expr weak_riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrdnz Hdecf Hagree HDmi Hgood Hdec Hgood0 Hexp.
    iIntros "Hmm Hpmpc Hpc Hnpc Hfile #Hbs Hhws Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    iApply (wwp_instr Φ pc true (UTYPE (imm, Regidx rd, LUI))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id))
                 [WEread wak_plain pc (if al4 then 4%N else 2%N)])
              wQ_pure Hgid Haccpc Hpmp
              (wcert_nowrite (fin_to_nat cpu_id) pc
                 [WEread wak_plain pc (if al4 then 4%N else 2%N)]
                 (nowrite_read1 wak_plain pc (if al4 then 4%N else 2%N)))
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc true (UTYPE (imm, Regidx rd, LUI))
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
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (UTYPE (imm, Regidx rd, LUI)))
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
      pose proof (exec_eff_execute_UTYPE_LUI_gpr rd imm
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 2))) as He.
      replace (Z.eqb (uint rd) 0) with false in He
        by (symmetry; apply Z.eqb_neq; exact Hrdnz).
      destruct (load_sexec_facts s0c b' (add_vec_int pc 2) rd
                  (regval_into_reg (luival imm)))
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
               pc h w i0 (UTYPE (imm, Regidx rd, LUI)) [] D D0 dst).
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
    pose proof (exec_eff_execute_UTYPE_LUI_gpr rd imm
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 2))) as Hef.
    replace (Z.eqb (uint rd) 0) with false in Hef
      by (symmetry; apply Z.eqb_neq; exact Hrdnz).
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iDestruct (gpr_file_insert_acc m (Regidx rd)
                 (regval_into_reg (luival imm)) with "Hfile") as "[Hrdc Hfins]".
    iEval (rewrite (gpr_pt_nz rd _ Hrdnz)) in "Hrdc".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (luival imm)) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
    { iEval (rewrite (gpr_pt_nz rd _ Hrdnz)). iExact "Hrdc". }
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 2))
                     (R_bitvector_64 (gpr_of_Z (uint rd)))
                     (regval_into_reg (luival imm))).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (load_sexec_facts (wflat_st σ) b (add_vec_int pc 2) rd
                (regval_into_reg (luival imm))) as (G1 & G2 & G3 & G4 & G5).
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

End leaf_lui_rvc.

(* ====================================================================== *)
(** ** 4. [auipc] — [F_Base] fetch, alignment-generic

    Mirror of [WpMmodeUtype.wp_auipc_gpr]: identical to §2 but for the
    written VALUE, which is PC-relative — so the flat run needs the ONE extra
    step [HPCin] (the [PC] read, moved past the funnel's two pre-writes)
    before the mirror's [register_lookup PC …] is [pc]. *)

Section leaf_auipc.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Implicit Types Φ : mval -> iProp Σ.

  Lemma wwp_auipc_leaf Φ (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rd : mword 5) (imm : mword 20) (m : regfile)
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
         = Some (UTYPE (imm, Regidx rd, AUIPC), t)) ->
    (forall rs : Riscv.rv64d_types.regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst = Some (UTYPE (imm, Regidx rd, AUIPC), dst) ->
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
                     regval_into_reg (add_vec pc (auipc_off imm))]> m) -∗
       hart_ws cpu_id ws' -∗
       WP (Loop : expr weak_riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrdnz Hdecf Hagree HDmi Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hfile #Hbs Hhws Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    iApply (wwp_instr Φ pc false (UTYPE (imm, Regidx rd, AUIPC))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc))
              wQ_pure Hgid Haccpc Hpmp
              (wcert_regonly al4 (fin_to_nat cpu_id) pc)
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false (UTYPE (imm, Regidx rd, AUIPC))
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
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (UTYPE (imm, Regidx rd, AUIPC)))
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
      pose proof (exec_eff_execute_UTYPE_AUIPC_gpr rd imm
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 4))) as He.
      replace (Z.eqb (uint rd) 0) with false in He
        by (symmetry; apply Z.eqb_neq; exact Hrdnz).
      destruct (load_sexec_facts s0c b' (add_vec_int pc 4) rd
                  (regval_into_reg
                     (add_vec (register_lookup PC (sregs
                        (set_reg (set_reg s0c (R_bool minstret_increment) b')
                           nextPC (add_vec_int pc 4))))
                        (auipc_off imm))))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    assert (HP : wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc) σ).
    { apply (wP_eff_of_leaf_regonly al4 (fin_to_nat cpu_id) σ (wwin pc pc 0)
               pc w (UTYPE (imm, Regidx rd, AUIPC)) D dst).
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
    (* ---- the run at the FLAT state: the PC read is the one extra step ---- *)
    assert (HPCin : register_lookup PC (sregs
              (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                 nextPC (add_vec_int pc 4))) = pc).
    { rewrite (set_lookup_ne PC nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat PC σ b eq_refl). exact Lpc0. }
    pose proof (exec_eff_execute_UTYPE_AUIPC_gpr rd imm
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 4))) as Hef.
    replace (Z.eqb (uint rd) 0) with false in Hef
      by (symmetry; apply Z.eqb_neq; exact Hrdnz).
    rewrite HPCin in Hef.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iDestruct (gpr_file_insert_acc m (Regidx rd)
                 (regval_into_reg (add_vec pc (auipc_off imm)))
                 with "Hfile") as "[Hrdc Hfins]".
    iEval (rewrite (gpr_pt_nz rd _ Hrdnz)) in "Hrdc".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec pc (auipc_off imm)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
    { iEval (rewrite (gpr_pt_nz rd _ Hrdnz)). iExact "Hrdc". }
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4))
                     (R_bitvector_64 (gpr_of_Z (uint rd)))
                     (regval_into_reg (add_vec pc (auipc_off imm)))).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (load_sexec_facts (wflat_st σ) b (add_vec_int pc 4) rd
                (regval_into_reg (add_vec pc (auipc_off imm))))
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

End leaf_auipc.

(* ====================================================================== *)
(** ** 5. [c.slli] — SHIFTIOP SLLI through a COMPRESSED decode

    §3's compressed shape with §1's mirror.  THE ONE NEW MOVE is the SOURCE
    READ: the shift's value depends on [rs1], and [rd = rs1] at every
    [c.slli] call site — which is exactly why this leaf takes the whole
    [gpr_file].  It is read x0-safely with
    [WpGpr.gpr_file_lookup_acc] + [gpr_pt_value] (the accessor is closed
    again immediately, so the later [gpr_file_insert_acc] on the SAME index
    is legal), and the resulting value equation is moved past the funnel's
    [nextPC] pre-write by [WeakLeafWin.set_lookup_ne]. *)

Section leaf_slli_rvc.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Implicit Types Φ : mval -> iProp Σ.

  Lemma wwp_slli_rvc_leaf Φ (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (h : SailStdpp.Values.mword 16)
      (rs1 rd : mword 5) (shamt : mword 6) (i0 : instruction) (m : regfile)
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
                      (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI)), s))) ->
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
       = Some (ExecuteAs (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI)), s)) ->
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
                     regval_into_reg (shift_bits_left (m !!! Regidx rs1)
                       (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
       hart_ws cpu_id ws' -∗
       WP (Loop : expr weak_riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrdnz Hdecf Hagree HDmi Hgood Hdec Hgood0 Hexp.
    iIntros "Hmm Hpmpc Hpc Hnpc Hfile #Hbs Hhws Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    iApply (wwp_instr Φ pc true (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id))
                 [WEread wak_plain pc (if al4 then 4%N else 2%N)])
              wQ_pure Hgid Haccpc Hpmp
              (wcert_nowrite (fin_to_nat cpu_id) pc
                 [WEread wak_plain pc (if al4 then 4%N else 2%N)]
                 (nowrite_read1 wak_plain pc (if al4 then 4%N else 2%N)))
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc true
                (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI))
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
    (* ---- THE SOURCE READ (x0-safe; the accessor is closed again) ---- *)
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfile")
      as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1))
                 (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                 with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    assert (Hsrcf : (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                            (sregs (set_reg (set_reg (wflat_st σ)
                                      (R_bool minstret_increment) b)
                                    nextPC (add_vec_int pc 2))))
                    = m !!! Regidx rs1).
    { destruct (Z.eqb (uint rs1) 0); [exact Hrv|].
      rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC
                 _ _ ltac:(reg_ne)).
      exact Hrv. }
    assert (Hav : gpr_slli_val rs1 shamt
                    (set_reg (set_reg (wflat_st σ)
                                (R_bool minstret_increment) b)
                             nextPC (add_vec_int pc 2))
                  = shift_bits_left (m !!! Regidx rs1)
                      (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)).
    { unfold gpr_slli_val, gpr_src. rewrite Hsrcf. reflexivity. }
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI)))
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
      pose proof (exec_eff_execute_SHIFTIOP_SLLI_gpr rs1 rd shamt
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 2))) as He.
      replace (Z.eqb (uint rd) 0) with false in He
        by (symmetry; apply Z.eqb_neq; exact Hrdnz).
      destruct (load_sexec_facts s0c b' (add_vec_int pc 2) rd
                  (regval_into_reg (gpr_slli_val rs1 shamt
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
               pc h w i0 (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI))
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
      - exact (Hagree (wm_regs σ) Lpriv Lmisa Lsec).
      - exact HDmi.
      - exact Hgood.
      - exact Hdec.
      - exact Hgood0.
      - exact Hexp.
      - exact Hc. }
    pose proof (exec_eff_execute_SHIFTIOP_SLLI_gpr rs1 rd shamt
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 2))) as Hef.
    replace (Z.eqb (uint rd) 0) with false in Hef
      by (symmetry; apply Z.eqb_neq; exact Hrdnz).
    rewrite Hav in Hef.
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iDestruct (gpr_file_insert_acc m (Regidx rd)
                 (regval_into_reg (shift_bits_left (m !!! Regidx rs1)
                    (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)))
                 with "Hfile") as "[Hrdc Hfins]".
    iEval (rewrite (gpr_pt_nz rd _ Hrdnz)) in "Hrdc".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (shift_bits_left (m !!! Regidx rs1)
               (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
    { iEval (rewrite (gpr_pt_nz rd _ Hrdnz)). iExact "Hrdc". }
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 2))
                     (R_bitvector_64 (gpr_of_Z (uint rd)))
                     (regval_into_reg (shift_bits_left (m !!! Regidx rs1)
                        (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)))).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (load_sexec_facts (wflat_st σ) b (add_vec_int pc 2) rd
                (regval_into_reg (shift_bits_left (m !!! Regidx rs1)
                   (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))))
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

End leaf_slli_rvc.

(* ====================================================================== *)
(** ** 6. [c.srli] — SHIFTIOP SRLI through a COMPRESSED decode

    §5 with [shift_bits_left] / [gpr_slli_val] replaced by
    [shift_bits_right] / [gpr_srli_val]; nothing else moves. *)

Section leaf_srli_rvc.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Implicit Types Φ : mval -> iProp Σ.

  Lemma wwp_srli_rvc_leaf Φ (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (h : SailStdpp.Values.mword 16)
      (rs1 rd : mword 5) (shamt : mword 6) (i0 : instruction) (m : regfile)
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
                      (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI)), s))) ->
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
       = Some (ExecuteAs (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI)), s)) ->
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
                     regval_into_reg (shift_bits_right (m !!! Regidx rs1)
                       (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
       hart_ws cpu_id ws' -∗
       WP (Loop : expr weak_riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrdnz Hdecf Hagree HDmi Hgood Hdec Hgood0 Hexp.
    iIntros "Hmm Hpmpc Hpc Hnpc Hfile #Hbs Hhws Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    iApply (wwp_instr Φ pc true (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id))
                 [WEread wak_plain pc (if al4 then 4%N else 2%N)])
              wQ_pure Hgid Haccpc Hpmp
              (wcert_nowrite (fin_to_nat cpu_id) pc
                 [WEread wak_plain pc (if al4 then 4%N else 2%N)]
                 (nowrite_read1 wak_plain pc (if al4 then 4%N else 2%N)))
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc true
                (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI))
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
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfile")
      as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1))
                 (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                 with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    assert (Hsrcf : (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                            (sregs (set_reg (set_reg (wflat_st σ)
                                      (R_bool minstret_increment) b)
                                    nextPC (add_vec_int pc 2))))
                    = m !!! Regidx rs1).
    { destruct (Z.eqb (uint rs1) 0); [exact Hrv|].
      rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC
                 _ _ ltac:(reg_ne)).
      exact Hrv. }
    assert (Hav : gpr_srli_val rs1 shamt
                    (set_reg (set_reg (wflat_st σ)
                                (R_bool minstret_increment) b)
                             nextPC (add_vec_int pc 2))
                  = shift_bits_right (m !!! Regidx rs1)
                      (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)).
    { unfold gpr_srli_val, gpr_src. rewrite Hsrcf. reflexivity. }
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI)))
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
      pose proof (exec_eff_execute_SHIFTIOP_SRLI_gpr rs1 rd shamt
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 2))) as He.
      replace (Z.eqb (uint rd) 0) with false in He
        by (symmetry; apply Z.eqb_neq; exact Hrdnz).
      destruct (load_sexec_facts s0c b' (add_vec_int pc 2) rd
                  (regval_into_reg (gpr_srli_val rs1 shamt
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
               pc h w i0 (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI))
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
      - exact (Hagree (wm_regs σ) Lpriv Lmisa Lsec).
      - exact HDmi.
      - exact Hgood.
      - exact Hdec.
      - exact Hgood0.
      - exact Hexp.
      - exact Hc. }
    pose proof (exec_eff_execute_SHIFTIOP_SRLI_gpr rs1 rd shamt
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 2))) as Hef.
    replace (Z.eqb (uint rd) 0) with false in Hef
      by (symmetry; apply Z.eqb_neq; exact Hrdnz).
    rewrite Hav in Hef.
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iDestruct (gpr_file_insert_acc m (Regidx rd)
                 (regval_into_reg (shift_bits_right (m !!! Regidx rs1)
                    (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)))
                 with "Hfile") as "[Hrdc Hfins]".
    iEval (rewrite (gpr_pt_nz rd _ Hrdnz)) in "Hrdc".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (shift_bits_right (m !!! Regidx rs1)
               (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
    { iEval (rewrite (gpr_pt_nz rd _ Hrdnz)). iExact "Hrdc". }
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 2))
                     (R_bitvector_64 (gpr_of_Z (uint rd)))
                     (regval_into_reg (shift_bits_right (m !!! Regidx rs1)
                        (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)))).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (load_sexec_facts (wflat_st σ) b (add_vec_int pc 2) rd
                (regval_into_reg (shift_bits_right (m !!! Regidx rs1)
                   (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))))
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

End leaf_srli_rvc.

(* ====================================================================== *)
(** ** 7. Soundness check *)

Print Assumptions exec_eff_execute_SHIFTIOP_SLLI_gpr.
Print Assumptions exec_eff_execute_SHIFTIOP_SRLI_gpr.
Print Assumptions wwp_lui_leaf.
Print Assumptions wwp_lui_rvc_leaf.
Print Assumptions wwp_auipc_leaf.
Print Assumptions wwp_slli_rvc_leaf.
Print Assumptions wwp_srli_rvc_leaf.
