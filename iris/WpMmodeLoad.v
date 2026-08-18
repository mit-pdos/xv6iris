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

   THE PMP STEP IS THE ONLY THING THAT VARIES between the three leaves'
   configurations, and [HartMLoad] takes it as an obligation rather than
   pinning it -- so [wp_ld_gpr] hands the chain
   [HartMPmp.swp_pmpCheck_load8_off] (every entry OFF) and the two TOR leaves
   hand it [swp_pmpCheck_load8_tor0] (entry 0 is TOR, unlocked, and its top
   bound covers the eight bytes -- [ld_tor0_range] turns the leaves'
   [pmp_tor0_grants] into the two address-comparison facts that rule wants).
   The TOR footprint is [ldt_Dro] = [ld_Dro] plus the pmpaddr file, and
   [ld_rs] carries a pmpaddr value in both cases: [hreg_frame_ro] only reads
   the registers in [Dro], so one reference file serves both. *)
Require Import WpMmodeLeafBase.
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d SailStdpp.Base RiscvLang RiscvPtsto RiscvExec RiscvFetchExec WpGpr RegFile InstrBytes RiscvModelBytes RiscvTryStep RiscvExtras SailStdpp.TypeCasts SailStdpp.MachineWord SailStdpp.Values.
Require Import WpInstr.   (* wp_instr / mm_cycle, split out of InstrBytes *)
Require Import HartSwp HartLift HartSpan HartSpanChar HartMFrame HartMPmp
        HartMLoad.
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

(* [pmpaddr_n] is ALWAYS set, even for the all-OFF leaves whose frame does
   not include it: [hreg_frame_ro] only looks at the registers in [Dro], so
   one reference file serves both footprints. *)
Definition ld_rs (ms0 sec0 : mword 64) (pmar0 : list PMA_Region)
    (pcfg : type_of_register pmpcfg_n)
    (paddr0 : type_of_register pmpaddr_n) : regstate :=
  register_set mstatus ms0
    (register_set mseccfg sec0
      (register_set pma_regions pmar0
        (register_set pmpcfg_n pcfg
          (register_set pmpaddr_n paddr0
            (register_set htif_tohost_base None
              (register_set cur_privilege Machine init_regstate)))))).

Ltac ld_lookup :=
  rewrite /ld_rs;
  repeat first [ apply register_lookup_set
               | rewrite irrelevant_register_set; [|vm_compute; reflexivity] ];
  reflexivity.

Lemma ld_rs_mst ms0 sec0 pmar0 pcfg paddr0 :
  register_lookup mstatus (ld_rs ms0 sec0 pmar0 pcfg paddr0) = ms0.
Proof. ld_lookup. Qed.
Lemma ld_rs_sec ms0 sec0 pmar0 pcfg paddr0 :
  register_lookup mseccfg (ld_rs ms0 sec0 pmar0 pcfg paddr0) = sec0.
Proof. ld_lookup. Qed.
Lemma ld_rs_pma ms0 sec0 pmar0 pcfg paddr0 :
  register_lookup pma_regions (ld_rs ms0 sec0 pmar0 pcfg paddr0) = pmar0.
Proof. ld_lookup. Qed.
Lemma ld_rs_pcfg ms0 sec0 pmar0 pcfg paddr0 :
  register_lookup pmpcfg_n (ld_rs ms0 sec0 pmar0 pcfg paddr0) = pcfg.
Proof. ld_lookup. Qed.
Lemma ld_rs_htif ms0 sec0 pmar0 pcfg paddr0 :
  register_lookup htif_tohost_base (ld_rs ms0 sec0 pmar0 pcfg paddr0) = None.
Proof. ld_lookup. Qed.
Lemma ld_rs_priv ms0 sec0 pmar0 pcfg paddr0 :
  register_lookup cur_privilege (ld_rs ms0 sec0 pmar0 pcfg paddr0) = Machine.
Proof. ld_lookup. Qed.
Lemma ld_rs_paddr ms0 sec0 pmar0 pcfg paddr0 :
  register_lookup pmpaddr_n (ld_rs ms0 sec0 pmar0 pcfg paddr0) = paddr0.
Proof. ld_lookup. Qed.

(* the TOR leaves' footprint: [ld_Dro] plus the pmpaddr file, which the
   TOR-entry-0 PMP walk reads. *)
Definition ldt_Dro : gset register := {[ (pmpaddr_n : register) ]} ∪ ld_Dro.

Lemma ldt_disj : (∅ : gset register) ## ldt_Dro.
Proof. set_solver. Qed.
Lemma ldt_in_mst : (mstatus : register) ∈ (∅ : gset register) ∪ ldt_Dro.
Proof. rewrite /ldt_Dro /ld_Dro. set_solver. Qed.
Lemma ldt_in_priv : (cur_privilege : register) ∈ (∅ : gset register) ∪ ldt_Dro.
Proof. rewrite /ldt_Dro /ld_Dro. set_solver. Qed.
Lemma ldt_in_sec : (mseccfg : register) ∈ (∅ : gset register) ∪ ldt_Dro.
Proof. rewrite /ldt_Dro /ld_Dro. set_solver. Qed.
Lemma ldt_in_pma : (pma_regions : register) ∈ (∅ : gset register) ∪ ldt_Dro.
Proof. rewrite /ldt_Dro /ld_Dro. set_solver. Qed.
Lemma ldt_in_pcfg : (pmpcfg_n : register) ∈ (∅ : gset register) ∪ ldt_Dro.
Proof. rewrite /ldt_Dro /ld_Dro. set_solver. Qed.
Lemma ldt_in_paddr : (pmpaddr_n : register) ∈ (∅ : gset register) ∪ ldt_Dro.
Proof. rewrite /ldt_Dro. set_solver. Qed.
Lemma ldt_in_htif :
  (htif_tohost_base : register) ∈ (∅ : gset register) ∪ ldt_Dro.
Proof. rewrite /ldt_Dro /ld_Dro. set_solver. Qed.

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

(* the two address-comparison facts [HartMPmp.swp_pmpCheck_load8_tor0] asks
   for, from the leaves' own [pmp_tor0_grants] -- the same two steps
   [WpMmodeLeafBase.exec_pmpMatchAddr_tor0_match] takes at the exec layer. *)
Lemma ld_tor0_range (pcfg : type_of_register pmpcfg_n)
    (paddr : type_of_register pmpaddr_n) (ea : mword 64) :
  pmp_tor0_grants pcfg paddr ea 8 ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false /\
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec paddr 0)) 4)
    (uint ea) (uint (to_bits 64 8)) = PMP_Match.
Proof.
  intros (_ & _ & _ & Hin).
  pose proof (bv_unsigned_in_range _ ea) as [Ha0 _].
  rewrite <- uint_unsigned in Ha0.
  assert (Hz0 : uint (zeros' 64 : mword 64) = 0) by (vm_compute; reflexivity).
  assert (Hw8 : uint (to_bits 64 8 : mword 64) = 8)
    by (vm_compute; reflexivity).
  split.
  - unfold zopz0zKzJ_u. rewrite Hz0. rewrite Z.geb_leb. apply Z.leb_gt. lia.
  - rewrite Hz0 Hw8. apply pmpRangeMatch_full; lia.
Qed.

Section LdFrames.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Lemma hreg_frame_empty (rs : regstate) : ⊢ (hreg_frame rs ∅ : iProp Σ).
  Proof. rewrite /hreg_frame big_sepS_empty. auto. Qed.

  (* the frame the engine wants, spelled as the six cells the leaf holds *)
  Lemma ld_frames (dq : dfrac) (ms0 sec0 : mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr0 : type_of_register pmpaddr_n) :
    (hreg_frame_ro (ld_Df dq) (ld_rs ms0 sec0 pmar0 pcfg paddr0) ld_Dro : iProp Σ)
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

  (* ...and the TOR footprint: the same six plus the pmpaddr file *)
  Lemma ldt_frames (dq : dfrac) (ms0 sec0 : mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr0 : type_of_register pmpaddr_n) :
    (hreg_frame_ro (ld_Df dq) (ld_rs ms0 sec0 pmar0 pcfg paddr0) ldt_Dro
      : iProp Σ)
    ⊣⊢ (reg_pointsto pmpaddr_n dq paddr0 ∗
        hreg_frame_ro (ld_Df dq) (ld_rs ms0 sec0 pmar0 pcfg paddr0) ld_Dro).
  Proof.
    rewrite /hreg_frame_ro /ldt_Dro.
    rewrite big_sepS_union; last (rewrite /ld_Dro; set_solver).
    rewrite big_sepS_singleton ld_rs_paddr.
    by rewrite (_ : ld_Df dq pmpaddr_n = dq); [|ld_df].
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
      set (pa0 := register_lookup pmpaddr_n init_regstate).
      iAssert (hreg_frame_ro (ld_Df (DfracOwn (q/2)))
                 (ld_rs ms0 mseccfg0 pmar0 pmpcfg0 pa0) ld_Dro)%I
        with "[Hms_k Hpriv_k Hpmpc_k]" as "Hro".
      { iApply ld_frames. iFrame "Hms_k Hpriv_k Hpmpc_k".
        iFrame "Hmseccfg Hpma Hhtif". }
      iApply (swp_mono with "[HPC HnPC Hhs_k] [Hf Hro Hbw]");
        [| iApply (swp_execute_LOAD8 ∅ ld_Dro (ld_Df (DfracOwn (q/2)))
                     (ld_rs ms0 mseccfg0 pmar0 pmpcfg0 pa0) imm rs1 rd false
                     m v pmar0 (phys_word_pointsto ea dq v)
                     ld_disj ld_in_mst ld_in_priv ld_in_sec ld_in_pma
                     ld_in_htif
                     (ld_rs_priv ms0 mseccfg0 pmar0 pmpcfg0 pa0)
                     (ld_rs_pma ms0 mseccfg0 pmar0 pmpcfg0 pa0)
                     (ld_rs_htif ms0 mseccfg0 pmar0 pmpcfg0 pa0)
                     ltac:(rewrite ld_rs_mst; exact HMPRV)
                     ltac:(rewrite ld_rs_sec; exact Hseccfg1)
                     (pma_all_ram Hpma_all) Hram_ea Halign Hrd
                     with "Hcert Hf [] Hro [] [Hbw]") ].
      + iIntros (e) "(-> & Hf & _ & Hro & Hbw)".
        iDestruct (ld_frames with "Hro")
          as "(Hms_k & Hpriv_k & _ & _ & Hpmpc_k & _)".
        iSplitR; [done|]. iFrame "Hf HPC HnPC".
        iSplitL "Hhs_k Hpriv_k Hms_k".
        { iFrame "Hhw Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k".
          iPureIntro. exact (conj HmIE (conj HMPRV (conj HSXL HKF))). }
        iFrame "Hpmpc_k Hbw".
      + iApply hreg_frame_empty.
      + (* the PMP check, at the all-OFF configuration *)
        iIntros "Hrw Hro".
        iApply (swp_pmpCheck_load8_off ∅ ld_Dro (ld_Df (DfracOwn (q/2)))
                  (ld_rs ms0 mseccfg0 pmar0 pmpcfg0 pa0) pmpcfg0 ea
                  ld_disj ld_in_pcfg Hpmp
                  (ld_rs_pcfg ms0 mseccfg0 pmar0 pmpcfg0 pa0)
                  with "Hcert Hrw Hro").
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
    iIntros "Hmm Hpmpc Hpaddr Hpc Hfile Hinstr Hbytes Hcont".
    iDestruct (phys_word_pointsto_aligned_p with "Hbytes") as %Halign.
    iDestruct (phys_word_pointsto_ram with "Hbytes") as %Hram_ea.
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hpaddr" as "[Hpaddr_a Hpaddr_b]".
    iDestruct "Hmm_k" as "(#Hhw & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL & %HKF)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS &
        %HmisaC & %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 &
        %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    destruct (ld_tor0_range pmpcfg0 pmpaddrs ea Htor) as [Hord Hrange].
    iApply (wp_instr pc (add_vec_int pc (if is_rvc then 2 else 4)) is_rvc
              (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) m
              (<[Regidx rd := regval_into_reg v]> m) pmpcfg0
              (mmode_config (DfracOwn (q/2)) ∗
               pmpcfg_n ↦ᵣ{DfracOwn (q/2)} pmpcfg0 ∗
               pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs ∗
               phys_word_pointsto ea dq v)%I
              Hpmp Hstat
              with "Hmm_wp Hpmpc_wp Hpc Hfile Hinstr
                    [Hhs_k Hpriv_k Hms_k Hpmpc_k Hpaddr_a Hpaddr_b Hbytes]
                    [Hcont]").
    - iIntros "Hf HPC HnPC".
      iAssert (hreg_frame_ro (ld_Df (DfracOwn (q/2)))
                 (ld_rs ms0 mseccfg0 pmar0 pmpcfg0 pmpaddrs) ldt_Dro)%I
        with "[Hms_k Hpriv_k Hpmpc_k Hpaddr_a]" as "Hro".
      { iApply ldt_frames. iFrame "Hpaddr_a". iApply ld_frames.
        iFrame "Hms_k Hpriv_k Hpmpc_k". iFrame "Hmseccfg Hpma Hhtif". }
      iApply (swp_mono with "[HPC HnPC Hhs_k Hpaddr_b] [Hf Hro Hbytes]");
        [| iApply (swp_execute_LOAD8 ∅ ldt_Dro (ld_Df (DfracOwn (q/2)))
                     (ld_rs ms0 mseccfg0 pmar0 pmpcfg0 pmpaddrs) imm rs1 rd
                     false m v pmar0 (phys_word_pointsto ea dq v)
                     ldt_disj ldt_in_mst ldt_in_priv ldt_in_sec ldt_in_pma
                     ldt_in_htif
                     (ld_rs_priv ms0 mseccfg0 pmar0 pmpcfg0 pmpaddrs)
                     (ld_rs_pma ms0 mseccfg0 pmar0 pmpcfg0 pmpaddrs)
                     (ld_rs_htif ms0 mseccfg0 pmar0 pmpcfg0 pmpaddrs)
                     ltac:(rewrite ld_rs_mst; exact HMPRV)
                     ltac:(rewrite ld_rs_sec; exact Hseccfg1)
                     (pma_all_ram Hpma_all) Hram_ea Halign Hrd
                     with "Hcert Hf [] Hro [] [Hbytes]") ].
      + iIntros (e) "(-> & Hf & _ & Hro & Hbytes)".
        iDestruct (ldt_frames with "Hro") as "[Hpaddr_a Hro]".
        iDestruct (ld_frames with "Hro")
          as "(Hms_k & Hpriv_k & _ & _ & Hpmpc_k & _)".
        iCombine "Hpaddr_a Hpaddr_b" as "Hpaddr".
        iSplitR; [done|]. iFrame "Hf HPC HnPC".
        iSplitL "Hhs_k Hpriv_k Hms_k".
        { iFrame "Hhw Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k".
          iPureIntro. exact (conj HmIE (conj HMPRV (conj HSXL HKF))). }
        iFrame "Hpmpc_k Hpaddr Hbytes".
      + iApply hreg_frame_empty.
      + (* the PMP check, at the TOR entry 0 that covers the access *)
        iIntros "Hrw Hro".
        iApply (swp_pmpCheck_load8_tor0 ∅ ldt_Dro (ld_Df (DfracOwn (q/2)))
                  (ld_rs ms0 mseccfg0 pmar0 pmpcfg0 pmpaddrs) pmpcfg0 pmpaddrs
                  ea ldt_disj ldt_in_pcfg ldt_in_paddr
                  (ld_rs_pcfg ms0 mseccfg0 pmar0 pmpcfg0 pmpaddrs)
                  (ld_rs_paddr ms0 mseccfg0 pmar0 pmpcfg0 pmpaddrs)
                  (proj1 Htor) (proj1 (proj2 Htor)) Hord Hrange
                  with "Hcert Hrw Hro").
      + (* the read node's obligation: the eight owned bytes ARE the value *)
        iIntros (sg) "Hsi". rewrite /mstate_interp.
        iDestruct "Hsi" as "(Hreg & Hmem & Hdev)".
        iDestruct (phys_word_read_bytes sg ea v dq with "Hmem Hbytes") as %Hrb.
        iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hcl".
        iSplitR; [iPureIntro; exact Hrb|].
        iNext. iMod "Hcl" as "_". iModIntro. iFrame "Hreg Hmem Hdev Hbytes".
    - iNext.
      iIntros "Hmm' Hpmpc' Hpc' Hf' (Hmm_k' & Hpmpc_k' & Hpaddr' & Hbw')".
      iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
      iCombine "Hpmpc' Hpmpc_k'" as "Hpmpc''".
      iApply ("Hcont" with "Hmm'' Hpmpc'' Hpaddr' Hpc' Hf' Hbw'").

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
