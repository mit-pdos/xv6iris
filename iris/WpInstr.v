(* WpInstr.v -- THE M-MODE INSTRUCTION WRAPPER.

   [wp_instr] is the rule the 135 leaf call sites see, and [mm_cycle] is the
   M-mode instance of [HartMCycle.swp_exec_step_decode_execute] it is built
   on.  Split out of [InstrBytes] purely so that iterating on the wrapper
   does not re-elaborate the [instr] / [instr_bytes] / [decode_hval]
   definitions and the frame bridges, which are stable. *)
From Stdlib Require Import ZArith Zquot.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
From iris.program_logic Require Import language.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords.
Require Import HartSwp HartLift HartLift2 HartSpan HartSpanChar
        HartRegNode HartMCycle HartMRun HartMFrame RegFile WpGpr.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec MinstretInv.
Require Import MstatusFacts.
Require Import KptPt KMap.
Local Open Scope Z_scope.

Require Import InstrBytes.

Section WpInstr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* every tower lookup, in one tactic: the [mm_rs_*] equations are complete,
     so any premise of the form [register_lookup r (mm_rs ..) = v] closes. *)
  Local Ltac mmrs :=
    by rewrite ?mm_rs_PC ?mm_rs_nPC ?mm_rs_ms ?mm_rs_mi ?mm_rs_cy ?mm_rs_ti
       ?mm_rs_ip ?mm_rs_priv ?mm_rs_mst ?mm_rs_hart ?mm_rs_pcfg ?mm_rs_mc
       ?mm_rs_micfg ?mm_rs_misa ?mm_rs_sec ?mm_rs_pma ?mm_rs_htif ?mm_rs_elp
       ?mm_rs_senv.

  (* [decode_ok] survives a nextPC write: the compressed expansion runs AFTER
     the fetch has committed nextPC, so it needs the same regime pins at the
     updated file. *)
  Lemma decode_ok_set_nPC (D : gset register) (rs : regstate) (v : mword 64) :
    decode_ok D rs -> decode_ok D (register_set (R_bitvector_64 nextPC) v rs).
  Proof.
    rewrite /decode_ok.
    rewrite (irrelevant_register_set cur_privilege (R_bitvector_64 nextPC)
               _ _ eq_refl).
    rewrite (irrelevant_register_set misa (R_bitvector_64 nextPC)
               _ _ eq_refl).
    rewrite (irrelevant_register_set mseccfg (R_bitvector_64 nextPC)
               _ _ eq_refl).
    rewrite (irrelevant_register_set menvcfg (R_bitvector_64 nextPC)
               _ _ eq_refl).
    exact (fun H => H).
  Qed.

  (* the 4-byte text window, resplit as the two halfwords the 2-mod-4 base
     fetch reads.  The bytes are persistent, so this is a duplication, not a
     transfer. *)
  Lemma text_split_halves (pc : mword 64) (w : mword 32) :
    ([∗ list] j ∈ seq 0 4, (pa_add pc j) ↦ₓ□ nth_byte w j) -∗
    ([∗ list] j ∈ seq 0 2,
       (pa_add pc j) ↦ₓ□ nth_byte (subrange_vec_dec w 15 0 : mword 16) j) ∗
    ([∗ list] j ∈ seq 0 2,
       (pa_add (add_vec_int pc 2) j) ↦ₓ□
         nth_byte (subrange_vec_dec w 31 16 : mword 16) j).
  Proof.
    assert (Hoff : forall j : nat,
              pa_add (add_vec_int pc 2) j = pa_add pc (2 + j)).
    { intros j. unfold pa_add. rewrite avi_assoc. f_equal. lia. }
    iIntros "#Hb".
    iAssert (∀ k : nat, ⌜(k < 4)%nat⌝ -∗
               (pa_add pc k) ↦ₓ□ nth_byte w k)%I as "#Hbk".
    { iIntros (k) "%Hk". iApply (big_sepL_lookup _ _ k k with "Hb").
      rewrite lookup_seq_lt; [reflexivity | lia]. }
    iSplit; iApply big_sepL_intro; iIntros "!>" (k j) "%Hk";
      apply lookup_seq in Hk as [-> Hj].
    - rewrite (nth_byte_subrange_lo w (0 + k)%nat ltac:(lia)).
      iApply "Hbk". iPureIntro. lia.
    - rewrite (nth_byte_subrange_hi w (0 + k)%nat ltac:(lia))
              (Hoff (0 + k)%nat).
      iApply "Hbk". iPureIntro. lia.
  Qed.

  (* ==================================================================== *)
  (* mm_cycle -- the M-MODE INSTANCE of [swp_exec_step_decode_execute].     *)
  (*                                                                      *)
  (* All it adds is the two bundle<->frame bridges.  Everything about the   *)
  (* cycle itself (boundary, interrupt check, minstret, tick, PC commit)    *)
  (* is in the generic rule, which knows nothing about privilege regimes;   *)
  (* the S-mode wrapper writes its own thirty-line twin of THIS and reuses  *)
  (* that rule unchanged.                                                  *)
  (* ==================================================================== *)
  Lemma mm_cycle (pc npc : mword 64) (pmpcfg0 : type_of_register pmpcfg_n)
      {dq : dfrac} (Psi : iProp Σ)
      (ms : mword 64) (bmi : bool) (cy ti ip mst0 : mword 64)
      (mc : mword 32) (micfg misa0 mseccfg0 senv0 : mword 64)
      (pmar0 : list PMA_Region) (elp0 : type_of_register elp) :
    eq_vec (_get_Mstatus_MIE mst0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mst0) ('b"1") = false ->
    _get_Mstatus_SXL mst0 = 'b"10" ->
    mstatus_kernel_facts mst0 ->
    hw_config -∗
    hreg_frame (mm_rs pc pc ms bmi cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) mm_Drw -∗
    hreg_frame_ro (mm_Df dq) (mm_rs pc pc ms bmi cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) mm_Dro -∗
    (hreg_frame (mm_rs pc pc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) mm_Drw -∗ hreg_frame_ro (mm_Df dq) (mm_rs pc pc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) mm_Dro -∗
       swp (run_hart_active 0)
         (fun st => ∃ w : mword 32,
                    ⌜st = Step_Execute (RETIRE_SUCCESS, w)⌝ ∗
                    hreg_frame (mm_rs pc npc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) mm_Drw ∗
                    hreg_frame_ro (mm_Df dq) (mm_rs pc npc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) mm_Dro ∗ Psi)) -∗
    ▷ (mmode_config dq -∗ pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pc_is npc -∗ Psi -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HmIE HMPRV HSXL HKF.
    iIntros "#Hhw Hrw Hro Hbody Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iApply (swp_exec_step_decode_execute mm_Drw mm_Dro (mm_Df dq)
              (mm_rs pc pc ms bmi cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) (mm_rs pc pc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) (mm_rs pc npc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) Psi
              mm_disj mm_w_cy mm_w_ti mm_w_ip mm_in_priv mm_in_hart mm_in_mc
              mm_in_micfg mm_w_mi mm_in_mi mm_w_ms mm_in_ms mm_w_PC mm_in_PC
              mm_in_nPC ltac:(mmrs) ltac:(mmrs) ltac:(mmrs) ltac:(mmrs)
              (mm_pre_agree pc ms bmi cy ti ip mst0 pmpcfg0 mc micfg misa0
                 mseccfg0 senv0 pmar0 elp0)
              with "Hcert Hrw Hro Hbody [Hcont]").
    iNext. iIntros (rs3) "%Hag Hrw Hro HPsi".
    destruct Hag as (mi & Hag).
    pose proof (mm_tick_agree pc npc ms (minstret_inc_flag mc micfg)
                  cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 senv0
                  pmar0 elp0 mi rs3 Hag) as Hag'.
    iDestruct (mm_rw_ext _ _ Hag' with "Hrw") as "Hrw".
    iDestruct (mm_ro_ext dq _ _ Hag' with "Hro") as "Hro".
    iDestruct (mm_frames_elim dq npc pmpcfg0 mi (minstret_inc_flag mc micfg)
                 _ _ _ mst0 mc micfg misa0 mseccfg0 senv0 pmar0 elp0
                 HmIE HMPRV HSXL HKF with "Hhw Hrw Hro")
      as "(Hmm & Hpmpc & Hpc)".
    iApply ("Hcont" with "Hmm Hpmpc Hpc HPsi").
  Qed.

  (* ==================================================================== *)
  (* wp_instr -- THE WRAPPER THE 135 LEAF CALL SITES SEE.                  *)
  (*                                                                      *)
  (* Same surface as before: [mmode_config] / [pmpcfg_n] / [pc_is] /       *)
  (* [gpr_file] / [instr] in, the same four back in the continuation.      *)
  (* What changed is the OBLIGATION -- one [swp] over [execute i] at the   *)
  (* caller's own resources, instead of handing the caller ALL of sigma    *)
  (* and asking for a successor state in one fupd, which per-node          *)
  (* stepping invalidates.                                                *)
  (*                                                                      *)
  (* Structurally this is the old [wp_instr]: ONE call to the cycle rule,  *)
  (* with the fetch-shape dispatch underneath it, where [instr_lift] used  *)
  (* to sit.  The obligation the caller sees is UNIFORM across the four    *)
  (* shapes because [decode_hval]'s RVC arm carries the [ExecuteAs]        *)
  (* expansion: the caller supplies [execute i] and never sees             *)
  (* [execute i0].                                                        *)
  (* ==================================================================== *)
  Lemma wp_instr (pc npc : mword 64) (is_rvc : bool) (i : instruction)
      (m m' : regfile) (pmpcfg0 : type_of_register pmpcfg_n)
      {dq : dfrac} (R : iProp Σ) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> kmap_static (svpn_of (pa_add pc j)) KP_rx) ->
    mmode_config dq -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc i -∗
    (* PC rides along read-only: AUIPC and JAL compute from it, and the
       instruction never writes it (tick_pc does, after the instruction). *)
    (gpr_file m -∗
     (R_bitvector_64 PC) ↦ᵣ pc -∗
     (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc (if is_rvc then 2 else 4)) -∗
       swp (execute i)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗ gpr_file m' ∗
                   (R_bitvector_64 PC) ↦ᵣ pc ∗
                   (R_bitvector_64 nextPC) ↦ᵣ npc ∗ R)) -∗
    ▷ (mmode_config dq -∗ pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
       pc_is npc -∗ gpr_file m' -∗ R -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hpmp Hstat.
    iIntros "Hmm Hpmpc Hpc Hgpr Hinstr Hex Hcont".
    iDestruct "Hinstr" as "(%Hlpi & Hib)".
    iDestruct "Hib" as (r) "(%Hrvc & Hbytes & %Hdec)".
    iDestruct (mm_frames_intro dq pc pmpcfg0 with "Hmm Hpmpc Hpc")
      as "[#Hhw Hfr]".
    iDestruct "Hfr" as (ms bmi cy ti ip mst0 mc micfg misa0 mseccfg0 senv0
        pmar0 elp0)
      "(%HmIE & %HMPRV & %HSXL & %HKF & %HmS & %HmC & %HmA & %Hmisaval &
        %Hsecval & %Hpmaall & %Helpnp & Hrw & Hro)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iDestruct (hw_config_kmap with "Hhw") as "#Hkm".
    (* ONE cycle step.  The fetch-shape dispatch is below it, not above. *)
    iApply (mm_cycle pc npc pmpcfg0 (gpr_file m' ∗ R)%I ms bmi cy ti ip mst0
              mc micfg misa0 mseccfg0 senv0 pmar0 elp0 HmIE HMPRV HSXL HKF
              with "Hhw Hrw Hro [Hgpr Hbytes Hex] [Hcont]").
    2:{ iNext. iIntros "Hmm Hpmpc Hpc [Hgpr HR]".
        iApply ("Hcont" with "Hmm Hpmpc Hpc Hgpr HR"). }
    (* the two pure facts every arm's run rule wants, at the [wrap_pre] file *)
    assert (Hdok : decode_ok (mm_Drw ∪ mm_Dro) (mm_rs pc pc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0)).
    { rewrite /decode_ok. split_and!.
      - exact mm_in_priv.
      - exact mm_in_misa.
      - rewrite mm_rs_priv. vm_compute. reflexivity.
      - rewrite mm_rs_misa. exact HmC.
      - rewrite mm_rs_misa. exact HmA.
      - rewrite mm_rs_misa. exact Hmisaval.
      - left. split_and!.
        + exact mm_in_sec.
        + mmrs.
        + rewrite mm_rs_sec. exact Hsecval. }
    pose proof (hfrun_lpad (mm_Drw ∪ mm_Dro) mm_Drw (mm_rs pc pc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0)
                  mm_in_elp ltac:(rewrite mm_rs_elp; exact Helpnp)) as Hlp.
    iIntros "Hrw Hro".
    iEval (rewrite /instr_bytes) in "Hbytes".
    iDestruct "Hbytes" as "[%H2al Hbytes]".
    destruct r as [e | w | h | erx]; [ done | | | done ];
      cbn [fetch_is_rvc decode_fetch] in Hrvc, Hdec; subst is_rvc.

    - (* ============================ F_Base w ======================== *)
      iDestruct "Hbytes" as "[%HnotRVC #Hb]".
      iAssert (⌜addr_is_ram pc⌝)%I as %Hram.
      { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hb") as "Hb0".
        { rewrite lookup_seq_lt; [reflexivity | lia]. }
        iDestruct (text_ident_phys _ _ _ (Hstat 0%nat ltac:(lia))
                     with "Hkm Hb0") as "Hb0'".
        iDestruct (phys_ram with "Hb0'") as %Hr0. rewrite pa_add_0 in Hr0.
        iPureIntro. exact Hr0. }
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal.
      + (* ---- 4-aligned: one 4-byte read ---- *)
        destruct (align4_low_bits pc Hal) as [Hbit0 Hbit1].
        (* the fetched word is existential in the cycle rule; introduce it
           HERE, per arm -- one [swp_step_ex] above the alignment split would
           make the two branches share a single evar. *)
        iApply swp_step_ex.
        iApply (swp_run_hart_active_base mm_Drw mm_Dro (mm_Df dq)
                  (mm_rs pc pc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) (mm_rs pc npc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) pc w i pmar0 pmpcfg0 8 (gpr_file m' ∗ R)%I
                  mm_disj mm_in_priv mm_in_misa mm_in_mst mm_in_PC mm_w_nPC
                  mm_in_pma mm_in_pcfg mm_in_htif
                  ltac:(mmrs) ltac:(mmrs) ltac:(mmrs) ltac:(mmrs) ltac:(mmrs)
                  ltac:(rewrite mm_rs_misa; exact HmS)
                  ltac:(rewrite mm_rs_mst; exact HmIE)
                  Hpmp (pma_all_ram Hpmaall) Hram Hbit0 Hbit1 Hal Hal
                  HnotRVC (Hdec _ _ _ Hdok) Hlp
                  with "Hcert Hrw Hro [] [Hgpr Hex]").
        { iApply (text_fetch_obl pc 4 w with "Hb"). }
        iIntros "Hrw Hro".
        pose proof (mm_npc_agree pc pc ms (minstret_inc_flag mc micfg) cy ti ip mst0
                       pmpcfg0 mc micfg misa0 mseccfg0 senv0 pmar0 elp0
                       (add_vec_int pc 4)) as Hnp.
        iDestruct (mm_rw_ext _ _ Hnp with "Hrw") as "Hrw".
        iDestruct (mm_ro_ext dq _ _ Hnp with "Hro") as "Hro".
        iDestruct (mm_rw_open with "Hrw")
          as "(HPC & HnPC & Hms & Hmi & Hcy & Hti & Hip)".
        iApply (swp_mono with "[Hms Hmi Hcy Hti Hip Hro] [-]");
          [| iApply ("Hex" with "Hgpr HPC HnPC") ].
        iIntros (u) "(-> & Hgpr & HPC & HnPC & HR)".
        iSplitR; [done|].
        iSplitL "HPC HnPC Hms Hmi Hcy Hti Hip".
        { iApply mm_rw_close. iFrame "HPC HnPC Hms Hmi Hcy Hti Hip". }
        iSplitL "Hro".
        { iApply (mm_ro_ext' dq _ _
                    (mm_ro_nPC pc (add_vec_int pc 4) npc ms
                       (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc
                       micfg misa0 mseccfg0 senv0 pmar0 elp0) with "Hro"). }
        iFrame "Hgpr HR".
      + (* ---- 2 mod 4: two halfword reads ---- *)
        destruct (align2_not4_facts pc H2al Hal) as (Halignl & Hbit0 & Hbit1).
        pose proof (align2_plus2 pc H2al) as Halignh.
        rewrite fetch_pa_id in Halignl. rewrite fetch_pa_id in Halignh.
        iAssert (⌜addr_is_ram (add_vec_int pc 2)⌝)%I as %Hramh.
        { iDestruct (big_sepL_lookup _ _ 2%nat 2%nat with "Hb") as "Hb2".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (text_ident_phys _ _ _ (Hstat 2%nat ltac:(lia))
                       with "Hkm Hb2") as "Hb2'".
          iDestruct (phys_ram with "Hb2'") as %Hr2. iPureIntro.
          unfold pa_add in Hr2. exact Hr2. }
        iDestruct (text_split_halves pc w with "Hb") as "[#Hbl #Hbh]".
        (* the fetched word is existential in the cycle rule; introduce it
           HERE, per arm -- one [swp_step_ex] above the alignment split would
           make the two branches share a single evar. *)
        iApply swp_step_ex.
        iApply (swp_run_hart_active_base2 mm_Drw mm_Dro (mm_Df dq)
                  (mm_rs pc pc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) (mm_rs pc npc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) pc
                  (subrange_vec_dec w 15 0) (subrange_vec_dec w 31 16) i
                  pmar0 pmpcfg0 8 (gpr_file m' ∗ R)%I
                  mm_disj mm_in_priv mm_in_misa mm_in_mst mm_in_PC mm_w_nPC
                  mm_in_pma mm_in_pcfg mm_in_htif
                  ltac:(mmrs) ltac:(mmrs) ltac:(mmrs) ltac:(mmrs) ltac:(mmrs)
                  ltac:(rewrite mm_rs_misa; exact HmS)
                  ltac:(rewrite mm_rs_mst; exact HmIE)
                  Hpmp (pma_all_ram Hpmaall) Hram Hbit0 Hbit1 Hal Halignl
                  Hramh Halignh
                  ltac:(rewrite mm_rs_misa; exact HmC)
                  HnotRVC
                  ltac:(rewrite concat_subranges_id; exact (Hdec _ _ _ Hdok))
                  Hlp
                  with "Hcert Hrw Hro [] [] [Hgpr Hex]").
        { iApply (text_fetch_obl pc 2 (subrange_vec_dec w 15 0) with "Hbl"). }
        { iApply (text_fetch_obl (add_vec_int pc 2) 2
                    (subrange_vec_dec w 31 16) with "Hbh"). }
        iIntros "Hrw Hro".
        pose proof (mm_npc_agree pc pc ms (minstret_inc_flag mc micfg) cy ti ip mst0
                       pmpcfg0 mc micfg misa0 mseccfg0 senv0 pmar0 elp0
                       (add_vec_int pc 4)) as Hnp.
        iDestruct (mm_rw_ext _ _ Hnp with "Hrw") as "Hrw".
        iDestruct (mm_ro_ext dq _ _ Hnp with "Hro") as "Hro".
        iDestruct (mm_rw_open with "Hrw")
          as "(HPC & HnPC & Hms & Hmi & Hcy & Hti & Hip)".
        iApply (swp_mono with "[Hms Hmi Hcy Hti Hip Hro] [-]");
          [| iApply ("Hex" with "Hgpr HPC HnPC") ].
        iIntros (u) "(-> & Hgpr & HPC & HnPC & HR)".
        iSplitR; [done|].
        iSplitL "HPC HnPC Hms Hmi Hcy Hti Hip".
        { iApply mm_rw_close. iFrame "HPC HnPC Hms Hmi Hcy Hti Hip". }
        iSplitL "Hro".
        { iApply (mm_ro_ext' dq _ _
                    (mm_ro_nPC pc (add_vec_int pc 4) npc ms
                       (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc
                       micfg misa0 mseccfg0 senv0 pmar0 elp0) with "Hro"). }
        iFrame "Hgpr HR".

    - (* ============================ F_RVC h ========================= *)
      iDestruct "Hbytes" as "[%HisRVC Hbytes]".
      destruct Hdec as (i0 & Hlp0 & Hdec2).
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal.
      + (* ---- 4-aligned: the compressed halfword sits in a 4-byte word -- *)
        iDestruct "Hbytes" as (w) "[%Hsub #Hb]".
        iAssert (⌜addr_is_ram pc⌝)%I as %Hram.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hb") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (text_ident_phys _ _ _ (Hstat 0%nat ltac:(lia))
                       with "Hkm Hb0") as "Hb0'".
          iDestruct (phys_ram with "Hb0'") as %Hr0. rewrite pa_add_0 in Hr0.
          iPureIntro. exact Hr0. }
        destruct (align4_low_bits pc Hal) as [Hbit0 Hbit1].
        (* the fetched word is existential in the cycle rule; introduce it
           HERE, per arm -- one [swp_step_ex] above the alignment split would
           make the two branches share a single evar. *)
        iApply swp_step_ex.
        iApply (swp_run_hart_active_rvc mm_Drw mm_Dro (mm_Df dq)
                  (mm_rs pc pc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) (mm_rs pc npc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) pc w i0 i pmar0 pmpcfg0 8 (gpr_file m' ∗ R)%I
                  mm_disj mm_in_priv mm_in_misa mm_in_mst mm_in_PC mm_w_nPC
                  mm_in_pma mm_in_pcfg mm_in_htif
                  ltac:(mmrs) ltac:(mmrs) ltac:(mmrs) ltac:(mmrs) ltac:(mmrs)
                  ltac:(rewrite mm_rs_misa; exact HmS)
                  ltac:(rewrite mm_rs_mst; exact HmIE)
                  ltac:(rewrite mm_rs_misa; exact HmC)
                  Hpmp (pma_all_ram Hpmaall) Hram Hbit0 Hbit1 Hal Hal
                  ltac:(rewrite Hsub; exact HisRVC)
                  ltac:(rewrite Hsub; exact (proj1 (Hdec2 _ _ _ Hdok)))
                  Hlp
                  with "Hcert Hrw Hro [] [] [Hgpr Hex]").
        { iApply (text_fetch_obl pc 4 w with "Hb"). }
        { iIntros "Hrw Hro".
          iApply (swp_span mm_Drw mm_Dro (mm_Df dq) _ _ _ _ mm_disj
                    (proj2 (Hdec2 _ _ _ (decode_ok_set_nPC _ _ _ Hdok)))
                    with "Hcert Hrw Hro"). }
        iIntros "Hrw Hro".
        pose proof (mm_npc_agree pc pc ms (minstret_inc_flag mc micfg) cy ti ip mst0
                       pmpcfg0 mc micfg misa0 mseccfg0 senv0 pmar0 elp0
                       (add_vec_int pc 2)) as Hnp.
        iDestruct (mm_rw_ext _ _ Hnp with "Hrw") as "Hrw".
        iDestruct (mm_ro_ext dq _ _ Hnp with "Hro") as "Hro".
        iDestruct (mm_rw_open with "Hrw")
          as "(HPC & HnPC & Hms & Hmi & Hcy & Hti & Hip)".
        iApply (swp_mono with "[Hms Hmi Hcy Hti Hip Hro] [-]");
          [| iApply ("Hex" with "Hgpr HPC HnPC") ].
        iIntros (u) "(-> & Hgpr & HPC & HnPC & HR)".
        iSplitR; [done|].
        iSplitL "HPC HnPC Hms Hmi Hcy Hti Hip".
        { iApply mm_rw_close. iFrame "HPC HnPC Hms Hmi Hcy Hti Hip". }
        iSplitL "Hro".
        { iApply (mm_ro_ext' dq _ _
                    (mm_ro_nPC pc (add_vec_int pc 2) npc ms
                       (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc
                       micfg misa0 mseccfg0 senv0 pmar0 elp0) with "Hro"). }
        iFrame "Hgpr HR".
      + (* ---- 2 mod 4: a bare halfword read ---- *)
        iDestruct "Hbytes" as "#Hb".
        iAssert (⌜addr_is_ram pc⌝)%I as %Hram.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hb") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (text_ident_phys _ _ _ (Hstat 0%nat ltac:(lia))
                       with "Hkm Hb0") as "Hb0'".
          iDestruct (phys_ram with "Hb0'") as %Hr0. rewrite pa_add_0 in Hr0.
          iPureIntro. exact Hr0. }
        destruct (align2_not4_facts pc H2al Hal) as (Halignl & Hbit0 & Hbit1).
        rewrite fetch_pa_id in Halignl.
        (* the fetched word is existential in the cycle rule; introduce it
           HERE, per arm -- one [swp_step_ex] above the alignment split would
           make the two branches share a single evar. *)
        iApply swp_step_ex.
        iApply (swp_run_hart_active_rvc2 mm_Drw mm_Dro (mm_Df dq)
                  (mm_rs pc pc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) (mm_rs pc npc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) pc h i0 i pmar0 pmpcfg0 8 (gpr_file m' ∗ R)%I
                  mm_disj mm_in_priv mm_in_misa mm_in_mst mm_in_PC mm_w_nPC
                  mm_in_pma mm_in_pcfg mm_in_htif
                  ltac:(mmrs) ltac:(mmrs) ltac:(mmrs) ltac:(mmrs) ltac:(mmrs)
                  ltac:(rewrite mm_rs_misa; exact HmS)
                  ltac:(rewrite mm_rs_mst; exact HmIE)
                  ltac:(rewrite mm_rs_misa; exact HmC)
                  Hpmp (pma_all_ram Hpmaall) Hram Hbit0 Hbit1 Hal Halignl
                  HisRVC (proj1 (Hdec2 _ _ _ Hdok)) Hlp
                  with "Hcert Hrw Hro [] [] [Hgpr Hex]").
        { iApply (text_fetch_obl pc 2 h with "Hb"). }
        { iIntros "Hrw Hro".
          iApply (swp_span mm_Drw mm_Dro (mm_Df dq) _ _ _ _ mm_disj
                    (proj2 (Hdec2 _ _ _ (decode_ok_set_nPC _ _ _ Hdok)))
                    with "Hcert Hrw Hro"). }
        iIntros "Hrw Hro".
        pose proof (mm_npc_agree pc pc ms (minstret_inc_flag mc micfg) cy ti ip mst0
                       pmpcfg0 mc micfg misa0 mseccfg0 senv0 pmar0 elp0
                       (add_vec_int pc 2)) as Hnp.
        iDestruct (mm_rw_ext _ _ Hnp with "Hrw") as "Hrw".
        iDestruct (mm_ro_ext dq _ _ Hnp with "Hro") as "Hro".
        iDestruct (mm_rw_open with "Hrw")
          as "(HPC & HnPC & Hms & Hmi & Hcy & Hti & Hip)".
        iApply (swp_mono with "[Hms Hmi Hcy Hti Hip Hro] [-]");
          [| iApply ("Hex" with "Hgpr HPC HnPC") ].
        iIntros (u) "(-> & Hgpr & HPC & HnPC & HR)".
        iSplitR; [done|].
        iSplitL "HPC HnPC Hms Hmi Hcy Hti Hip".
        { iApply mm_rw_close. iFrame "HPC HnPC Hms Hmi Hcy Hti Hip". }
        iSplitL "Hro".
        { iApply (mm_ro_ext' dq _ _
                    (mm_ro_nPC pc (add_vec_int pc 2) npc ms
                       (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc
                       micfg misa0 mseccfg0 senv0 pmar0 elp0) with "Hro"). }
        iFrame "Hgpr HR".
  Qed.

End WpInstr.
