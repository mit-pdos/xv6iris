(* M-mode Load leaf lemmas (mmode_config, decode family).
   Relocated from WpGpr*.v; helpers in WpMmodeLeafBase.

   The 8-byte load engine is [HartMLoad] and the leaves below are thin: each
   splits [mmode_config] in half, builds the read-only frame the engine wants
   out of the KEPT half's cells ([ld_frames]), calls [swp_execute_LOAD8] at
   that frame with an EMPTY writable frame (a load writes no config register),
   and rebuilds the bundle for the continuation.  The only obligation the leaf
   pays that the engine cannot is the memory one: it owns the eight target
   bytes and turns them into the [read_bytes] the read node asks for
   ([phys_word_read_bytes]).

   NOT YET CONVERTED: the two TOR leaves ([wp_ld_gpr_tor],
   [wp_cldsp_gpr_tor]).  They differ from [wp_ld_gpr] in exactly ONE step --
   the PMP check runs at a TOR-configured entry 0 rather than at an all-OFF
   configuration, so [HartMPmp.swp_pmpCheck_load8_off] does not apply.  What
   they need is its TOR twin at Machine, which belongs beside [mpmp_hval_off]
   in [HartMPmp] (it needs that file's [mpmp_red] / [mpmp_peel_D] /
   [mpmp_peel_any], which are [Local]):

     Lemma mpmp_hval_tor0 (D Drw : gset register) (pcfg paddr) rs addr wd acc :
       pmpcfg_n ∈ D -> pmpaddr_n ∈ D ->
       register_lookup pmpcfg_n rs = pcfg ->
       register_lookup pmpaddr_n rs = paddr ->
       pmp_tor0_grants pcfg paddr addr wd ->
       uint (to_bits 64 wd : mword 64) = wd ->
       hval D Drw rs (pmpCheck (Physaddr addr) wd acc Machine) None rs.

   Its proof is [PtTreeAdue.spmp_hval_grant] verbatim with the Supervisor
   [pmpCheckRWX] premise replaced by the Machine + unlocked early return that
   [mpmp_hval]'s "Match: Machine + unlocked allows" branch already performs:
   one loop iteration, entry 0 full-matches, allow.  Everything else in the
   two leaves is [wp_ld_gpr]'s script with [pmpaddr_n] added to [ld_Dro]. *)
Require Import WpMmodeLeafBase.
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d SailStdpp.Base RiscvLang RiscvPtsto RiscvExec RiscvFetchExec WpGpr RegFile InstrBytes RiscvModelBytes RiscvTryStep RiscvExtras SailStdpp.TypeCasts SailStdpp.MachineWord SailStdpp.Values.
Require Import WpInstr.   (* wp_instr / mm_cycle, split out of InstrBytes *)
Require Import HartSwp HartLift HartSpan HartSpanChar HartMFrame HartMLoad.
Import Defs.
Import Defs.

(* ====================================================================== *)
(* THE LOAD LEAF'S FOOTPRINT.                                              *)
(*                                                                        *)
(* A load WRITES no register the wrapper does not already own (its only    *)
(* write is the destination GPR, and the GPRs ride in [gpr_file], outside  *)
(* every frame), so the writable half is EMPTY.  The read-only half is     *)
(* exactly the six cells [HartMLoad]'s chain reads: mstatus (MPRV),        *)
(* cur_privilege, mseccfg (the pointer-masking mode), pma_regions,         *)
(* pmpcfg_n and htif_tohost_base.                                          *)
(* ====================================================================== *)
Definition ld_Dro : gset register :=
  {[ (mstatus : register); (cur_privilege : register); (mseccfg : register);
     (pma_regions : register); (pmpcfg_n : register);
     (htif_tohost_base : register) ]}.

(* three of the six are [hw_config]'s persistent cells; the other three are
   the fraction the leaf kept back *)
Definition ld_Df (dq : dfrac) : register -> dfrac := fun r =>
  if decide (r = (mseccfg : register)) then DfracDiscarded
  else if decide (r = (pma_regions : register)) then DfracDiscarded
  else if decide (r = (htif_tohost_base : register)) then DfracDiscarded
  else dq.

Definition ld_rs (ms0 sec0 : mword 64) (pmar0 : list PMA_Region)
    (pcfg : type_of_register pmpcfg_n) : regstate :=
  register_set mstatus ms0
    (register_set mseccfg sec0
      (register_set pma_regions pmar0
        (register_set pmpcfg_n pcfg
          (register_set htif_tohost_base None
            (register_set cur_privilege Machine init_regstate))))).

Ltac ld_lookup :=
  rewrite /ld_rs;
  repeat first [ apply register_lookup_set
               | rewrite irrelevant_register_set; [|vm_compute; reflexivity] ];
  reflexivity.

Lemma ld_rs_mst ms0 sec0 pmar0 pcfg :
  register_lookup mstatus (ld_rs ms0 sec0 pmar0 pcfg) = ms0.
Proof. ld_lookup. Qed.
Lemma ld_rs_sec ms0 sec0 pmar0 pcfg :
  register_lookup mseccfg (ld_rs ms0 sec0 pmar0 pcfg) = sec0.
Proof. ld_lookup. Qed.
Lemma ld_rs_pma ms0 sec0 pmar0 pcfg :
  register_lookup pma_regions (ld_rs ms0 sec0 pmar0 pcfg) = pmar0.
Proof. ld_lookup. Qed.
Lemma ld_rs_pcfg ms0 sec0 pmar0 pcfg :
  register_lookup pmpcfg_n (ld_rs ms0 sec0 pmar0 pcfg) = pcfg.
Proof. ld_lookup. Qed.
Lemma ld_rs_htif ms0 sec0 pmar0 pcfg :
  register_lookup htif_tohost_base (ld_rs ms0 sec0 pmar0 pcfg) = None.
Proof. ld_lookup. Qed.
Lemma ld_rs_priv ms0 sec0 pmar0 pcfg :
  register_lookup cur_privilege (ld_rs ms0 sec0 pmar0 pcfg) = Machine.
Proof. ld_lookup. Qed.

Lemma ld_disj : (∅ : gset register) ## ld_Dro.
Proof. set_solver. Qed.
Lemma ld_in_mst : (mstatus : register) ∈ (∅ : gset register) ∪ ld_Dro.
Proof. rewrite /ld_Dro. set_solver. Qed.
Lemma ld_in_priv : (cur_privilege : register) ∈ (∅ : gset register) ∪ ld_Dro.
Proof. rewrite /ld_Dro. set_solver. Qed.
Lemma ld_in_sec : (mseccfg : register) ∈ (∅ : gset register) ∪ ld_Dro.
Proof. rewrite /ld_Dro. set_solver. Qed.
Lemma ld_in_pma : (pma_regions : register) ∈ (∅ : gset register) ∪ ld_Dro.
Proof. rewrite /ld_Dro. set_solver. Qed.
Lemma ld_in_pcfg : (pmpcfg_n : register) ∈ (∅ : gset register) ∪ ld_Dro.
Proof. rewrite /ld_Dro. set_solver. Qed.
Lemma ld_in_htif :
  (htif_tohost_base : register) ∈ (∅ : gset register) ∪ ld_Dro.
Proof. rewrite /ld_Dro. set_solver. Qed.

Ltac ld_df :=
  rewrite /ld_Df; repeat case_decide; congruence.

Section LdFrames.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Lemma hreg_frame_empty (rs : regstate) : ⊢ (hreg_frame rs ∅ : iProp Σ).
  Proof. rewrite /hreg_frame big_sepS_empty. auto. Qed.

  (* the frame the engine wants, spelled as the six cells the leaf holds *)
  Lemma ld_frames (dq : dfrac) (ms0 sec0 : mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n) :
    (hreg_frame_ro (ld_Df dq) (ld_rs ms0 sec0 pmar0 pcfg) ld_Dro : iProp Σ)
    ⊣⊢ (reg_pointsto mstatus dq ms0 ∗
        reg_pointsto cur_privilege dq Machine ∗
        reg_pointsto mseccfg DfracDiscarded sec0 ∗
        reg_pointsto pma_regions DfracDiscarded pmar0 ∗
        reg_pointsto pmpcfg_n dq pcfg ∗
        reg_pointsto htif_tohost_base DfracDiscarded None).
  Proof.
    rewrite /hreg_frame_ro /ld_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite ld_rs_mst ld_rs_priv ld_rs_sec ld_rs_pma ld_rs_pcfg ld_rs_htif.
    rewrite (_ : ld_Df dq mstatus = dq); [|ld_df].
    rewrite (_ : ld_Df dq cur_privilege = dq); [|ld_df].
    rewrite (_ : ld_Df dq mseccfg = DfracDiscarded); [|ld_df].
    rewrite (_ : ld_Df dq pma_regions = DfracDiscarded); [|ld_df].
    rewrite (_ : ld_Df dq pmpcfg_n = dq); [|ld_df].
    rewrite (_ : ld_Df dq htif_tohost_base = DfracDiscarded); [|ld_df].
    by rewrite !bi.sep_assoc.
  Qed.

  (* the eight owned bytes, as the read node's [read_bytes] obligation.
     ([HartPilot.phys_read_bytes] is the width-generic form; it is not
     reachable from here without dragging in the pilot's cone.) *)
  Lemma phys_word_read_bytes (σ : mstate) (pa : Arch.pa)
      (w : bv 64) (dq : dfrac) :
    gen_heap_interp (hG:=riscv_memGS) σ.(mem) -∗
    phys_word_pointsto pa dq w -∗
    ⌜read_bytes σ.(mem) pa 8 = Some w⌝.
  Proof.
    iIntros "Hm [_ Hb]".
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
              σ.(mem) !! pa_add pa j = Some (nth_byte w j)⌝)%I as %Hbytes.
    { iIntros (j Hj). assert (Hj' : (j < 8)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hb") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (phys_valid with "Hm Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iPureIntro.
    destruct (read_bytes σ.(mem) pa 8) as [w'|] eqn:Hrb.
    - f_equal. apply bv_eq_of_bytes. intros j Hj.
      pose proof (read_bytes_spec _ _ _ _ Hrb j Hj) as H0.
      pose proof (Hbytes j Hj) as H1.
      rewrite H0 in H1. apply Some_inj in H1. exact H1.
    - exfalso. exact (read_bytes_ne σ.(mem) pa 8 w Hbytes Hrb).
  Qed.
End LdFrames.

(* from WpGprLoad.v *)
Section WpLdGpr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* reg_pointsto Fractional/AsFractional, reg_pointsto_agree, and
     mmode_config_split_half / mmode_config_combine_half now live in InstrBytes.v
     (next to mmode_config) -- shared by every memory / control-flow WP. *)

  (* [instr]/[mmode_config]-formulated register-generic 8-byte LOAD WP.  The
     caller supplies the loaded bytes ([pa..pa+7] ↦ₘ) and alignment facts; the
     config the load's translation / PMP checks read is recovered from the KEPT
     half of [mmode_config] + [hw_config].  [rs1<>0] (base) / [rd<>0] (dest). *)
  Lemma wp_ld_gpr (pc : mword 64) (is_rvc : bool) (rs1 rd : mword 5)
      (imm : mword 12) (m : regfile) (v : bv 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) {dq : dfrac} :
    let offset := sign_extend' 64 imm in
    let ea := add_vec (m !!! Regidx rs1) offset in
    (* the 8-byte DATA access needs the stronger all-OFF form: an 8-byte
       window can partially overlap a TOR/NA4 boundary (partial match faults
       even in M-mode), so unlocked-ness alone does not suffice.  The fetch
       side uses [pmp_all_off_allows_all]. *)
    pmp_all_off pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    phys_word_pointsto ea dq v -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      phys_word_pointsto ea dq v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros offset ea Hpmp Hstat Hrd.
    iIntros "Hmm Hpmpc Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (phys_word_pointsto_aligned_p with "Hbw") as %Halign.
    iDestruct (phys_word_pointsto_ram with "Hbw") as %Hram_ea.
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL & %HKF)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS &
        %HmisaC & %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 &
        %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iApply (wp_instr pc (add_vec_int pc (if is_rvc then 2 else 4)) is_rvc
              (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) m
              (<[Regidx rd := regval_into_reg v]> m) pmpcfg0
              (mmode_config (DfracOwn (q/2)) ∗
               pmpcfg_n ↦ᵣ{DfracOwn (q/2)} pmpcfg0 ∗
               phys_word_pointsto ea dq v)%I
              (pmp_all_off_allows_all _ Hpmp) Hstat
              with "Hmm_wp Hpmpc_wp Hpc Hfile Hinstr
                    [Hhs_k Hpriv_k Hms_k Hpmpc_k Hbw] [Hcont]").
    - iIntros "Hf HPC HnPC".
      iAssert (hreg_frame_ro (ld_Df (DfracOwn (q/2)))
                 (ld_rs ms0 mseccfg0 pmar0 pmpcfg0) ld_Dro)%I
        with "[Hms_k Hpriv_k Hpmpc_k]" as "Hro".
      { iApply ld_frames. iFrame "Hms_k Hpriv_k Hpmpc_k".
        iFrame "Hmseccfg Hpma Hhtif". }
      iApply (swp_mono with "[HPC HnPC Hhs_k] [Hf Hro Hbw]");
        [| iApply (swp_execute_LOAD8 ∅ ld_Dro (ld_Df (DfracOwn (q/2)))
                     (ld_rs ms0 mseccfg0 pmar0 pmpcfg0) imm rs1 rd false m v
                     pmar0 pmpcfg0 (phys_word_pointsto ea dq v)
                     ld_disj ld_in_mst ld_in_priv ld_in_sec ld_in_pma
                     ld_in_pcfg ld_in_htif
                     (ld_rs_priv ms0 mseccfg0 pmar0 pmpcfg0)
                     (ld_rs_pma ms0 mseccfg0 pmar0 pmpcfg0)
                     (ld_rs_pcfg ms0 mseccfg0 pmar0 pmpcfg0)
                     (ld_rs_htif ms0 mseccfg0 pmar0 pmpcfg0)
                     ltac:(rewrite ld_rs_mst; exact HMPRV)
                     ltac:(rewrite ld_rs_sec; exact Hseccfg1)
                     Hpmp (pma_all_ram Hpma_all) Hram_ea Halign Hrd
                     with "Hcert Hf [] Hro [Hbw]") ].
      + iIntros (e) "(-> & Hf & _ & Hro & Hbw)".
        iDestruct (ld_frames with "Hro")
          as "(Hms_k & Hpriv_k & _ & _ & Hpmpc_k & _)".
        iSplitR; [done|]. iFrame "Hf HPC HnPC".
        iSplitL "Hhs_k Hpriv_k Hms_k".
        { iFrame "Hhw Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k".
          iPureIntro. exact (conj HmIE (conj HMPRV (conj HSXL HKF))). }
        iFrame "Hpmpc_k Hbw".
      + iApply hreg_frame_empty.
      + (* the read node's obligation: the eight owned bytes ARE the value *)
        iIntros (sg) "Hsi". rewrite /mstate_interp.
        iDestruct "Hsi" as "(Hreg & Hmem & Hdev)".
        iDestruct (phys_word_read_bytes sg ea v dq with "Hmem Hbw") as %Hrb.
        iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hcl".
        iSplitR; [iPureIntro; exact Hrb|].
        iNext. iMod "Hcl" as "_". iModIntro. iFrame "Hreg Hmem Hdev Hbw".
    - iNext. iIntros "Hmm' Hpmpc' Hpc' Hf' (Hmm_k' & Hpmpc_k' & Hbw')".
      iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
      iCombine "Hpmpc' Hpmpc_k'" as "Hpmpc''".
      iApply ("Hcont" with "Hmm'' Hpmpc'' Hpc' Hf' Hbw'").
  Qed.

End WpLdGpr.

(* from WpGprRvcTor.v (RvcTorEngines, load leaves) *)
Section MmodeLoadTor.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_ld_gpr_tor (pc : mword 64) (is_rvc : bool) (rs1 rd : mword 5)
      (imm : mword 12) (m : regfile) (v : bv 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddrs : type_of_register pmpaddr_n)
      (q : Qp) {dq : dfrac} :
    let offset := sign_extend' 64 imm in
    let ea := add_vec (m !!! Regidx rs1) offset in
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    pmp_tor0_grants pmpcfg0 pmpaddrs ea 8 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    ea ↦ₚ₈{ dq } v -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      ea ↦ₚ₈{ dq } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros offset ea Hpmp Hstat Htor Hrd.
    iIntros "Hmm Hpmpc Hpaddr [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iDestruct (phys_word_pointsto_ram with "Hbytes") as %Hram_ea.
    iDestruct (phys_word_pointsto_ram7 with "Hbytes") as %Hram_ea7.
    iDestruct "Hbytes" as "(%Halign & Hbytes)".
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL & %HKF)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    destruct (pma_all_ram Hpma_all ea 8
               (pma_access_ram _ _ _ Hram_ea Hram_ea7 (pma_width_ok 8 eq_refl eq_refl) eq_refl eq_refl)) as (region & Hmatch & _ & Hread & _).
    iApply (wp_instr pc is_rvc (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) pmpcfg0
              Hpmp Hstat with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k")   as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms_k")     as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hpmpc_k")   as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpaddr")    as %Lpaddr.
    iDestruct (reg_valid_dq with "Hreg Hmseccfg")  as %Lsec.
    iDestruct (reg_valid_dq with "Hreg Hpma")      as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif")     as %Lhtif.
    iDestruct (big_sepM_lookup_acc _ _ _ _ (rf_to_gmap_lookup m (Regidx rs1)) with "Hfmap") as "[Hr1c Hfb1]".
    iEval (rewrite -(rf_lookup m (Regidx rs1))) in "Hr1c".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) σ with "Hreg Hr1c") as %Lrs1v.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
              σ.(mem) !! (pa_add ea j) = Some (nth_byte v j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 8)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (phys_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram ea⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (phys_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))).
    assert (Hbase : (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                    = m !!! Regidx rs1).
    { rewrite -Lrs1v. destruct (Z.eqb (uint rs1) 0) eqn:Ez; [reflexivity |].
      unfold s_pc; gpr_trans; reflexivity. }
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmsp : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsecp : register_lookup mseccfg s_pc.(sregs) = mseccfg0)
      by (unfold s_pc; tmig; exact Lsec).
    assert (Lpmpcp : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpaddrp : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddrs)
      by (unfold s_pc; tmig; exact Lpaddr).
    assert (Lpmap : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtifp : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    pose proof (within_clint_false ea 8 s_pc (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false ea 8 s_pc (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_false ea 8 s_pc Lhtifp) as Hwh.
    (* THE pmpCheck fact at the ticked state, from the TOR-entry-0 predicate. *)
    assert (Hpmpchk_ea : exec (pmpCheck (Physaddr ea) 8 (Load Data) Machine) s_pc
                         = Some (None, s_pc)).
    { apply (exec_pmpCheck_machine_tor0 ea 8 (Load Data) s_pc).
      - rewrite Lpmpcp Lpaddrp. exact Htor.
      - intros ent. eexists. apply exec_returnM.
      - vm_compute; reflexivity. }
    assert (Hev : extend_value false
              (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v) = v).
    { unfold extend_value. rewrite sign_extend'_id. apply data2_id. }
    assert (Ha8 : zero_extend' 64 (subrange_vec_dec
              (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                       offset) (xlen - 0 - 1) 0) = ea).
    { rewrite Hbase. rewrite zero_extend'_id. rewrite subrange_id. reflexivity. }
    assert (Hpa : zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec
              (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                       offset) (xlen - 0 - 1) 0)) (0 * 8)) = ea).
    { rewrite Hbase. rewrite !zero_extend'_id. rewrite subrange_id.
      change (0 * 8) with 0. rewrite avi0. reflexivity. }
    assert (Hexec_spc :
      exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s_pc
      = Some (RETIRE_SUCCESS,
              set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg v))).
    { rewrite -Hev.
      apply (exec_execute_LOAD_8_gpr_chk rs1 rd imm v region s_pc Hrd Lprivp).
      - rewrite Lmsp. exact HMPRV.
      - rewrite Lsecp. exact Hseccfg1.
      - rewrite Ha8. unfold is_aligned_vaddr. unfold is_aligned_paddr in Halign. exact Halign.
      - rewrite Hpa. exact Hpmpchk_ea.
      - rewrite Lpmap Hpa. exact Hmatch.
      - rewrite Hpa. exact Halign.
      - exact Hread.
      - rewrite Hpa. apply Hwc.
      - rewrite Hpa. apply Hws.
      - rewrite Hpa. apply Hwh.
      - rewrite Hpa. exact (addr_is_ram_not_dev _ Hrampa).
      - intros j Hj. rewrite Hpa. exact (Hbytesf j Hj). }
    iDestruct (big_sepM_insert_acc _ _ _ _ (rf_to_gmap_lookup m (Regidx rd)) with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg v) with "Hreg Hrdc")
      as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg v) with "[Hrdc]")
      as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iEval (rewrite -rf_to_gmap_upd) in "Hfmap".
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg v)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. exact Hexec_spc. }
    iSplitL "Hreg Hmem Hdev".
    { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hmem Hdev". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg v)).(sregs)
             = add_vec_int pc (if is_rvc then 2 else 4)).
    { unfold s_pc. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k". iPureIntro. exact (conj HmIE (conj HMPRV (conj HSXL HKF))). }
    iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iAssert (ea ↦ₚ₈{ dq } v)%I with "[Hbytes]" as "Hbw".
    { rewrite /phys_word_pointsto. iFrame "Hbytes". iPureIntro. exact Halign. }
    iApply ("Hcont" with "Hmm'' Hpmpc'' Hpaddr [$Hpc' $Hnpc] [Hfmap] Hbw").
    iSplitR.
    { iPureIntro. intro r. rewrite rf_to_gmap_upd dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  Lemma wp_cldsp_gpr_tor (pc : mword 64) (uimm : mword 6)
      (rd : mword 5) (m : regfile) (v : bv 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddrs : type_of_register pmpaddr_n)
      (q : Qp) {dq : dfrac} :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let ea := add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 imm) in
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    pmp_tor0_grants pmpcfg0 pmpaddrs ea 8 ->
    uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (LOAD (imm, Regidx csp_rs1, Regidx rd, false, 8)) -∗
    ea ↦ₚ₈{ dq } v -∗
    ( mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      ea ↦ₚ₈{ dq } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros imm ea Hpmp Hstat Htor Hrd.
    iIntros "Hmm Hpmpc Hpaddr Hpc Hfile Hinstr Hbytes Hcont".
    iApply (wp_ld_gpr_tor pc true csp_rs1 rd imm m v
              pmpcfg0 pmpaddrs q Hpmp Hstat Htor Hrd
              with "Hmm Hpmpc Hpaddr Hpc Hfile Hinstr Hbytes Hcont").
  Qed.

  (* ---- c.sdsp rs2, uimm(sp), TOR-aware ---- *)
End MmodeLoadTor.
