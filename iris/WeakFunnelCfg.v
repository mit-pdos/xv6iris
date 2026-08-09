(** * WeakFunnelCfg.v — the weak funnel for CONFIG-WRITING instructions

    [WeakFunnel.wwp_instr] holds the M-mode config cells (cur_privilege /
    mstatus / pmpcfg_n / hart_state) inside [mmode_config] across the step and
    hands the SAME bundle back — the right contract for every instruction that
    only READS the config, and a wrong one for the three that WRITE it
    (csrw mstatus / csrw pmpcfg0 / MRET): their [execute] must [reg_update]
    the very cells the funnel is holding.  On the SC side the same fork exists
    as [InstrBytes.wp_instr] vs [InstrBytes.wp_instr_config]; THIS FILE is
    the weak twin of the latter, and the interface delta from [wwp_instr]
    mirrors the SC delta exactly:

      - the funnel takes the UNBUNDLED config cells at FULL ownership, with
        the mstatus VALUE [ms0] an explicit parameter (a caller holding
        [mmode_config (DfracOwn 1)] first applies [mmode_config_unbundle],
        pinning [ms0] in ITS proof context);
      - only the MIE fact on [ms0] is needed to run the engine (it discharges
        [dispatchInterrupt]); the MPRV fact is additionally required because —
        unlike SC — the weak funnel SURFACES its config reads as
        [⌜wcfg_regs σ pmpcfg0⌝] (the batch-2 seam-2 fix), and that record
        carries the MPRV bit.  Every M-mode caller has it for free:
        [mmode_config] itself pins MPRV = 0, so unbundling yields the fact;
      - the engine reads cur_privilege / mstatus / pmpcfg_n (for the fetch,
        the interrupt gate and the decode) and then passes the three
        points-to INTO the callback, so the LEAF can [reg_update] them
        alongside its other writes when exhibiting [s_exec];
      - the callback additionally receives
        [⌜register_lookup mstatus (wm_regs σ) = ms0⌝] — the whole-value pin
        the leaf's [execute] fact is stated against (the config-variant
        analogue of [wcfg_regs] pinning misa/mseccfg to their whole values);
      - the continuation receives only the RAW [hart_state] cell back (plus
        the stepped PC); the written cells live in the leaf's closure.  A
        leaf that re-establishes the invariant facts on its final mstatus
        value can rebuild [mmode_config (DfracOwn 1)] via
        [InstrBytes.mmode_config_rebuild].

    EVERYTHING ELSE — the certificate interface ([wstep_cert]), the fetch
    obligations ([winstr] / [winstr_pinned] / [exec_fetch_flat]), the device
    frame seam [⌜mdev t = mdev s_exec⌝] (stated against [mdev s_exec], per
    the batch-2 seam-1 fix), [wstep_post], and the [wmstate_norg] hand-off —
    is IDENTICAL to [wwp_instr]; the proof below is that proof with the cell
    plumbing swapped.  This is seam 1 of the three [start()]/[timerinit()]
    blockers recorded in claude-notes/projects/weak-memory.md ("THE FIRST
    FUNCTION PORT"); the smoke-test consumer is
    [WeakLeafCsrw.wwp_csrw_mstatus_leaf]. *)
From Stdlib Require Import ZArith Zquot.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes SmodeCore.
Require Import WeakMem WeakInterp WeakLang WeakGhost WeakExec.
Require Import WeakView WeakVProp WeakFence WeakBridge WeakInstr.
Require Import WeakCert WeakAcquire.
Require Import WeakFunnel.

Local Open Scope Z_scope.

Section funnelcfg.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (** THE LEAF'S OBLIGATION, named — [wwp_instr_config]'s last premise.  Read
      it as [WeakFunnel.wwp_cb] with the SC config-variant delta applied and
      nothing else: the three written cells arrive at FULL ownership INSIDE
      the callback (so the leaf [reg_update]s them when exhibiting [s_exec]),
      the mstatus whole-value pin [⌜… = ms0⌝] is handed alongside
      [⌜wcfg_regs σ pmpcfg0⌝], and the post-step continuation gives back only
      the raw [hart_state] cell and the stepped PC.  The device-frame seam
      [⌜mdev t = mdev s_exec⌝] and the [wstep_post]/[wmstate_norg] plumbing
      are [wwp_cb]'s, verbatim. *)
  Definition wwp_cb_config (pc : SailStdpp.Values.mword 64) (is_rvc : bool)
      (i : instruction) (pmpcfg0 : type_of_register pmpcfg_n)
      (ms0 : SailStdpp.Values.mword 64)
      (P : wmstate -> Prop) (Q : wmstate -> wmstate -> Prop) : iProp Σ :=
    (∀ (σ : wmstate) (b : bool),
       ⌜register_lookup PC (wm_regs σ) = pc⌝ -∗
       ⌜wcfg_regs σ pmpcfg0⌝ -∗
       ⌜register_lookup mstatus (wm_regs σ) = ms0⌝ -∗
       cur_privilege ↦ᵣ Machine -∗
       mstatus ↦ᵣ ms0 -∗
       pmpcfg_n ↦ᵣ pmpcfg0 -∗
       wlat_interp (wm_img σ) (wm_log σ) -∗
       reg_interp (sregs (set_reg (wflat_st σ) (R_bool minstret_increment) b)) -∗
       wmstate_norg σ
       ={⊤ ∖ ↑minstretN, ∅}=∗
         (⌜P σ⌝ ∗
          ∃ s_exec : mstate,
            ⌜exec (execute i)
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc (if is_rvc then 2 else 4)))
               = Some (RETIRE_SUCCESS, s_exec)⌝ ∗
            reg_interp (sregs s_exec) ∗
            ▷ (∀ (tick : bool) (σ' : wmstate) (t : mstate),
                 ⌜exec (riscv_step tick) (wflat_st σ) = Some (tt, t)⌝ -∗
                 ⌜mdev t = mdev s_exec⌝ -∗
                 ⌜wstep_post σ σ' t⌝ -∗
                 ⌜Q σ σ'⌝ -∗
                 hart_state ↦ᵣ HART_ACTIVE tt -∗
                 PC ↦ᵣ (register_lookup nextPC (sregs s_exec)) -∗
                 (|={∅, ⊤ ∖ ↑minstretN}=>
                    (wlat_interp (wm_img σ') (wm_log σ') ∗
                     wmstate_norg σ' ∗
                     WWP Loop)))))%I.

  Lemma wwp_instr_config (pc : SailStdpp.Values.mword 64) (is_rvc : bool)
      (i : instruction) (pmpcfg0 : type_of_register pmpcfg_n)
      (ms0 : SailStdpp.Values.mword 64)
      (P : wmstate -> Prop) (Q : wmstate -> wmstate -> Prop) :
    gen_id = 0%nat ->
    acc_wf pc 4 ->
    pmp_allows_all pmpcfg0 ->
    eq_vec (_get_Mstatus_MIE ms0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV ms0) ('b"1") = false ->
    wstep_cert (fin_to_nat cpu_id) pc P Q ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Machine -∗
    mstatus ↦ᵣ ms0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    winstr pc is_rvc i -∗
    wwp_cb_config pc is_rvc i pmpcfg0 ms0 P Q -∗
    WWP Loop.
  Proof.
    rewrite /wwp_cb_config.
    iIntros (Hgid Haccpc Hpmp HmIE HMPRV Hcert)
      "#Hhw #Hmiv0 Hhs Hpriv Hmstatus Hpmpc Hpc Hinstr H".
    iDestruct "Hmiv0" as "#(Hinv & Hcinv & Hgc)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct "Hinstr" as "[%Hnlpad Hinstr]".
    iDestruct "Hinstr" as (r) "(%Hrvc & #Hb & %Hdec)".
    iApply (wp_winstr pc P Q Hgid Haccpc Hcert).
    iIntros (σ) "Hσ".
    iDestruct (wmstate_interp_split_regs σ with "Hσ") as "(Hreg & Hlat & Hnorg)".
    iDestruct (wmstate_norg_facts with "Hnorg") as %[Hbnd Hwf].
    (* open the minstret invariant: ⊤ -> ⊤ ∖ ↑minstretN, held across the ▷ *)
    iInv "Hinv" as ">Hbody" "Hclose".
    iDestruct "Hbody" as (mst0 mi0) "[Hmst Hmi]".
    (* every register the wrapper / fetch / decode reads, at [wm_regs σ] *)
    iDestruct (reg_valid    with "Hreg Hpc")       as %Lpc.
    iDestruct (reg_valid    with "Hreg Hpriv")     as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hpmpc")     as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpma")      as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif")     as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa")     as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hmseccfg")  as %Lmseccfg.
    iDestruct (reg_valid    with "Hreg Hmstatus")  as %Lmstatus.
    iDestruct (reg_valid_dq with "Hreg Help")      as %Lelp.
    iDestruct (reg_valid    with "Hreg Hhs")       as %Lhs.
    (* the same reads, packaged for the leaf — the MIE/MPRV bits come off the
       lemma's own [ms0] premises instead of [mmode_config]'s stored facts *)
    assert (Hcfg : wcfg_regs σ pmpcfg0).
    { rewrite /wcfg_regs Lpriv Lhs Lmisa Lmseccfg Lpmpc Lpma Lhtif Lmstatus
              Lelp.
      split_and!;
        [ reflexivity | reflexivity | exact Hmisa_val0 | exact Hmseccfg_val0
        | reflexivity | exact Hpma_all | reflexivity | exact HmisaS
        | exact HmIE | exact HMPRV | exact Hseccfg1 | exact Help_np ]. }
    (* the two facts the weak fetch needs, off the text elements *)
    iDestruct (winstr_flat σ pc r Hwf with "Hlat Hb") as %Hfok.
    iDestruct (winstr_pinned σ pc r Hwf with "Hlat Hb") as %Hpin.
    (* the funnel's own choice of the increment flag *)
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege (wflat_st σ).(sregs)) (wflat_st σ))
      as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi")
      as "[Hreg Hmi]".
    (* ---- the state the run really starts from ---- *)
    assert (Lpriv_a : register_lookup cur_privilege
              (set_reg (wflat_st σ) (R_bool minstret_increment) b).(sregs) = Machine).
    { rewrite (set_mi_lookup cur_privilege _ b eq_refl) wflat_st_regs. exact Lpriv. }
    assert (Lpc_a : register_lookup PC
              (set_reg (wflat_st σ) (R_bool minstret_increment) b).(sregs) = pc).
    { rewrite (set_mi_lookup PC _ b eq_refl) wflat_st_regs. exact Lpc. }
    assert (Lmisa_a : register_lookup misa
              (set_reg (wflat_st σ) (R_bool minstret_increment) b).(sregs) = misa0).
    { rewrite (set_mi_lookup misa _ b eq_refl) wflat_st_regs. exact Lmisa. }
    assert (Lmstatus_a : register_lookup mstatus
              (set_reg (wflat_st σ) (R_bool minstret_increment) b).(sregs) = ms0).
    { rewrite (set_mi_lookup mstatus _ b eq_refl) wflat_st_regs. exact Lmstatus. }
    assert (Lelp_a : register_lookup elp
              (set_reg (wflat_st σ) (R_bool minstret_increment) b).(sregs) = elp0).
    { rewrite (set_mi_lookup elp _ b eq_refl) wflat_st_regs. exact Lelp. }
    assert (Lmseccfg_a : register_lookup mseccfg
              (set_reg (wflat_st σ) (R_bool minstret_increment) b).(sregs) = mseccfg0).
    { rewrite (set_mi_lookup mseccfg _ b eq_refl) wflat_st_regs. exact Lmseccfg. }
    assert (Lhs_a : register_lookup hart_state
              (set_reg (wflat_st σ) (R_bool minstret_increment) b).(sregs)
              = HART_ACTIVE tt).
    { rewrite (set_mi_lookup hart_state _ b eq_refl) wflat_st_regs. exact Lhs. }
    (* fetch, at the post-write state (only the MEMORY matters, and it moved not) *)
    assert (Hfetch : exec (fetch tt)
              (set_reg (wflat_st σ) (R_bool minstret_increment) b)
              = Some (r, set_reg (wflat_st σ) (R_bool minstret_increment) b)).
    { apply (exec_fetch_flat _ pc r).
      - rewrite (set_mi_lookup pmpcfg_n _ b eq_refl) wflat_st_regs Lpmpc. exact Hpmp.
      - rewrite (set_mi_lookup pma_regions _ b eq_refl) wflat_st_regs Lpma.
        exact Hpma_all.
      - rewrite Lmisa_a. exact HmisaC.
      - exact Lpc_a.
      - exact Lpriv_a.
      - rewrite (set_mi_lookup htif_tohost_base _ b eq_refl) wflat_st_regs.
        exact Lhtif.
      - apply (fetch_flat_ok_mem (wflat_st σ)); [apply mem_set_reg | exact Hfok]. }
    (* the interrupt dispatch is a no-op: misa.S set, mstatus.MIE clear *)
    assert (Hdisp : exec (dispatchInterrupt Machine)
              (set_reg (wflat_st σ) (R_bool minstret_increment) b)
              = Some (None, set_reg (wflat_st σ) (R_bool minstret_increment) b)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none _ _
               (exec_currentlyEnabled_S
                  (set_reg (wflat_st σ) (R_bool minstret_increment) b))).
      - rewrite Lmisa_a. exact HmisaS.
      - rewrite Lmstatus_a. exact HmIE. }
    assert (Help_a : eq_vec (register_lookup elp
              (set_reg (wflat_st σ) (R_bool minstret_increment) b).(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false).
    { rewrite Lelp_a. exact Help_np. }
    assert (HZca_a : exec (currentlyEnabled Ext_Zca)
              (set_reg (wflat_st σ) (R_bool minstret_increment) b)
              = Some (true, set_reg (wflat_st σ) (R_bool minstret_increment) b)).
    { apply exec_currentlyEnabled_Zca. rewrite Lmisa_a. exact HmisaC. }
    (* the decode obligation, discharged from the PURE field of [winstr] *)
    specialize (Hdec (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                  ltac:(rewrite Lpriv_a; reflexivity)
                  ltac:(rewrite Lmisa_a; exact HmisaC)
                  ltac:(rewrite Lmisa_a; exact HmisaA)
                  ltac:(rewrite Lmisa_a; exact Hmisa_val0)
                  ltac:(unfold cfg_ok; left; split;
                        [ exact Lpriv_a
                        | rewrite Lmseccfg_a; exact Hmseccfg_val0 ])).
    (* ---- the leaf's obligation: the written cells go IN ---- *)
    iMod ("H" $! σ b with "[%] [%] [%] Hpriv Hmstatus Hpmpc Hlat Hreg Hnorg")
      as "(%HP & Hcb)"; [exact Lpc | exact Hcfg | exact Lmstatus |].
    iDestruct "Hcb" as (s_exec) "(%Hexec & Hreg & Hcont)".
    iDestruct (reg_valid with "Hreg Hhs") as %Lhs_e.
    iDestruct (reg_valid with "Hreg Hmi") as %Lmi_e.
    (* ---- the [run_hart_active] progress fact, by width ---- *)
    pose proof Hfok as Hfok'.
    destruct Hfok' as (_ & _ & wfw & Hrm & _).
    assert (Hha : exec (run_hart_active 0)
              (set_reg (wflat_st σ) (R_bool minstret_increment) b)
              = Some (Step_Execute (RETIRE_SUCCESS,
                        (match r with
                         | F_Base w => zero_extend' 32 w
                         | F_RVC h  => zero_extend' 32 h
                         | _ => mword_of_int 0
                         end : SailStdpp.Values.mword 32)), s_exec)).
    { destruct r as [e | w | h | erx]; [destruct Hrm | | | destruct Hrm].
      - (* F_Base: direct decode, one execute *)
        cbn [fetch_is_rvc] in Hrvc, Hdec. subst is_rvc.
        exact (exec_hart_active_progress_base_gen Machine
                 (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                 (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                 s_exec w i pc RETIRE_SUCCESS
                 Lpriv_a Hdisp Hfetch Hdec
                 Help_a Hnlpad Lpc_a Hexec I).
      - (* F_RVC: indirect decode through the state-generic [ExecuteAs] *)
        cbn [fetch_is_rvc] in Hrvc, Hdec. subst is_rvc.
        destruct Hdec as (i0 & Hdec0 & Hnlpad0 & Hexp).
        exact (exec_hart_active_progress_RVC_gen Machine
                 (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                 (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                 s_exec h i0 i pc RETIRE_SUCCESS
                 Lpriv_a Hdisp Hfetch Hdec0
                 Help_a Lpc_a HZca_a (Hexp _) Hexec). }
    pose proof (exec_riscv_step_hart_active (wflat_st σ) s_exec _ b
                  Hsi Lhs_a Hha Lhs_e Lmi_e) as Hstep0.
    (* ---- the wrapper's own register writes: tick PC, maybe bump minstret ---- *)
    iAssert (|==> ∃ t0 : mstate,
                ⌜exec (riscv_step false) (wflat_st σ) = Some (tt, t0)⌝ ∗
                ⌜mdev t0 = mdev s_exec⌝ ∗
                reg_interp (sregs t0) ∗ minstret_inv_body ∗
                PC ↦ᵣ (register_lookup nextPC (sregs s_exec)))%I
      with "[Hreg Hmst Hmi Hpc]" as ">Hw".
    { iMod (reg_update _ PC _ (register_lookup nextPC (sregs s_exec))
              with "Hreg Hpc") as "[Hreg Hpc]".
      destruct b.
      - iMod (reg_update _ minstret _
                (add_vec_int (register_lookup minstret
                   (sregs (set_reg s_exec PC
                             (register_lookup nextPC (sregs s_exec))))) 1)
                with "Hreg Hmst") as "[Hreg Hmst]".
        iModIntro. iExists _. iSplitR; [iPureIntro; exact Hstep0|].
        iSplitR; [iPureIntro; by rewrite !mdev_set_reg|].
        iFrame "Hreg Hpc". iExists _, true. iFrame.
      - iModIntro. iExists _. iSplitR; [iPureIntro; exact Hstep0|].
        iSplitR; [iPureIntro; by rewrite !mdev_set_reg|].
        iFrame "Hreg Hpc". iExists _, false. iFrame. }
    iDestruct "Hw" as (t0) "(%Hst0 & %Hdev0 & Hreg & Hbody & Hpc)".
    destruct (exec_tick_clock t0) as (c' & ti' & p' & Htick).
    pose proof (exec_riscv_step_tick _ _ _ Hst0 Htick) as Hst1.
    (* ---- hand the two successors to [wp_winstr] ---- *)
    iModIntro.
    iSplitR; [iPureIntro; exact Lpc|].
    iSplitR; [iPureIntro; exact Hpin|].
    iSplitR; [iPureIntro; exact HP|].
    iExists t0, (set_reg (set_reg (set_reg t0 mcycle c') mtime ti') mip p').
    iSplitR; [iPureIntro; exact Hst0|].
    iSplitR; [iPureIntro; exact Hst1|].
    iNext. iIntros (tick σ') "%Hpost %HQ".
    iSpecialize ("Hcont" $! tick σ' (if tick then
        set_reg (set_reg (set_reg t0 mcycle c') mtime ti') mip p' else t0)).
    iSpecialize ("Hcont" with "[%]");
      [destruct tick; [exact Hst1 | exact Hst0]|].
    iSpecialize ("Hcont" with "[%]");
      [destruct tick; [rewrite !mdev_set_reg; exact Hdev0 | exact Hdev0]|].
    iSpecialize ("Hcont" with "[%]"); [exact Hpost|].
    iSpecialize ("Hcont" with "[%]"); [exact HQ|].
    iSpecialize ("Hcont" with "Hhs").
    iSpecialize ("Hcont" with "Hpc").
    iMod "Hcont" as "(Hlat' & Hnorg' & HWP)".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' & Hbnd').
    destruct tick.
    - (* TICK: [tick_clock] wrote mcycle / mtime / mip, all owned by clock_inv *)
      iInv "Hcinv" as ">Hcb" "Hclosec".
      iDestruct "Hcb" as (c0 t0c p0) "(Hc & Ht & Hp)".
      iMod (reg_update _ mcycle _ c' with "Hreg Hc") as "[Hreg Hc]".
      iMod (reg_update _ mtime _ ti' with "Hreg Ht") as "[Hreg Ht]".
      iMod (reg_update _ mip _ p' with "Hreg Hp") as "[Hreg Hp]".
      iMod ("Hclosec" with "[Hc Ht Hp]") as "_".
      { iNext. iExists c', ti', p'. iFrame. }
      iMod ("Hclose" with "[Hbody]") as "_"; [by iNext|].
      iModIntro. rewrite (wmstate_interp_split_regs σ'). iFrame "HWP Hlat' Hnorg'".
      rewrite Hregs. iExact "Hreg".
    - (* NO TICK: the registers are already those of [t0] *)
      iMod ("Hclose" with "[Hbody]") as "_"; [by iNext|].
      iModIntro. rewrite (wmstate_interp_split_regs σ'). iFrame "HWP Hlat' Hnorg'".
      rewrite Hregs. iExact "Hreg".
  Qed.

End funnelcfg.

(* ====================================================================== *)
(** ** Soundness check *)

Print Assumptions wwp_instr_config.
