(* WpInstrConfig.v -- THE M-MODE WRAPPER FOR CONFIG-WRITING INSTRUCTIONS.

   [wp_instr_config] is [WpInstr.wp_instr]'s twin for the three instructions
   that write the very cells [mmode_config] bundles: [csrw mstatus],
   [csrw pmpcfg0] and [MRET].  [wp_instr]'s contract is "hand the bundle in,
   get the SAME bundle back", which is exactly wrong for them, so this
   wrapper takes the config cells RAW and at FULL ownership and returns them
   at the caller's new values.

   Everything else is shared: the cycle rule is
   [HartMCycle.swp_exec_step_decode_execute] (which knows nothing about
   privilege regimes) and the fetch is
   [WpInstrRun.swp_run_hart_active_instr] (which knows nothing about
   bundles).  What lives here is the bookkeeping in between:

   - [mc_rs], the anchor tower with cur_privilege a PARAMETER.  [mm_rs] pins
     it to Machine, which is right for every file the FETCH runs against
     (this is the M-mode wrapper) but not for MRET's post-file.  mstatus and
     pmpcfg are already [mm_rs] parameters, so csrw needs no new tower at
     all -- only MRET does.

   - THE FOOTPRINT IS UNCHANGED: [mm_Drw] / [mm_Dro], with [mm_Df
     (DfracOwn 1)].  cur_privilege / mstatus / pmpcfg_n do NOT move into the
     writable frame even though this wrapper's instructions write them.  A
     cell is in [Drw] so that the WALKER may write it; these three are
     written by the LEAF, which holds them as ordinary points-to during the
     instruction ([mc_ro_acc] hands them out and takes them back).  "Read-
     only frame" is about what the walker may do, not about the fraction:
     [mm_Df (DfracOwn 1)] is full ownership, used read-only. *)
From Stdlib Require Import ZArith Zquot.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
From iris.program_logic Require Import language.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords.
Require Import HartSwp HartLift HartLift2 HartSpan HartSpanChar HartRunGen
        HartRegNode HartMCycle HartMRun HartMFrame RegFile WpGpr.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep
        RiscvFetchExec MinstretInv.
Require Import MstatusFacts.
Require Import KptPt KMap.
Local Open Scope Z_scope.

Require Import InstrBytes WpInstrRun.

(* ====================================================================== *)
(* THE PRIVILEGE-PARAMETRIC ANCHOR TOWER.                                  *)
(*                                                                        *)
(* One [register_set] over [mm_rs], not a nineteenth copy of the tower:    *)
(* [mm_rs] is opaque, so a lookup here is one peel and then one [mm_rs_*]. *)
(* ====================================================================== *)
Section ctower.
  Context (priv : Privilege).
  Context (pc npc ms : SailStdpp.Values.mword 64) (bmi : bool)
          (cy ti ip : SailStdpp.Values.mword 64)
          (mst0 : SailStdpp.Values.mword 64)
          (pcfg : type_of_register pmpcfg_n)
          (mc : SailStdpp.Values.mword 32)
          (micfg misa0 mseccfg0 : SailStdpp.Values.mword 64)
          (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
          (senv0 : SailStdpp.Values.mword 64).

  Definition mc_rs : regstate :=
    register_set cur_privilege priv
      (mm_rs pc npc ms bmi cy ti ip mst0 pcfg mc micfg misa0 mseccfg0
         pmar0 elp0 senv0).

  (* every cell but cur_privilege: peel the set, then [mm_rs]'s own equation *)
  Local Ltac ck L :=
    etransitivity;
      [ apply irrelevant_register_set; vm_compute; reflexivity | apply L ].

  Lemma mc_rs_priv : register_lookup cur_privilege mc_rs = priv.
  Proof. apply register_lookup_set. Qed.
  Lemma mc_rs_PC : register_lookup (R_bitvector_64 PC) mc_rs = pc.
  Proof. ck mm_rs_PC. Qed.
  Lemma mc_rs_nPC : register_lookup (R_bitvector_64 nextPC) mc_rs = npc.
  Proof. ck mm_rs_nPC. Qed.
  Lemma mc_rs_ms : register_lookup (R_bitvector_64 minstret) mc_rs = ms.
  Proof. ck mm_rs_ms. Qed.
  Lemma mc_rs_mi : register_lookup (R_bool minstret_increment) mc_rs = bmi.
  Proof. ck mm_rs_mi. Qed.
  Lemma mc_rs_cy : register_lookup (R_bitvector_64 mcycle) mc_rs = cy.
  Proof. ck mm_rs_cy. Qed.
  Lemma mc_rs_ti : register_lookup (R_bitvector_64 mtime) mc_rs = ti.
  Proof. ck mm_rs_ti. Qed.
  Lemma mc_rs_ip : register_lookup (R_bitvector_64 mip) mc_rs = ip.
  Proof. ck mm_rs_ip. Qed.
  Lemma mc_rs_mst : register_lookup mstatus mc_rs = mst0.
  Proof. ck mm_rs_mst. Qed.
  Lemma mc_rs_hart : register_lookup hart_state mc_rs = HART_ACTIVE tt.
  Proof. ck mm_rs_hart. Qed.
  Lemma mc_rs_pcfg : register_lookup pmpcfg_n mc_rs = pcfg.
  Proof. ck mm_rs_pcfg. Qed.
  Lemma mc_rs_mc :
    register_lookup (R_bitvector_32 mcountinhibit) mc_rs = mc.
  Proof. ck mm_rs_mc. Qed.
  Lemma mc_rs_micfg :
    register_lookup (R_bitvector_64 minstretcfg) mc_rs = micfg.
  Proof. ck mm_rs_micfg. Qed.
  Lemma mc_rs_misa : register_lookup misa mc_rs = misa0.
  Proof. ck mm_rs_misa. Qed.
  Lemma mc_rs_sec : register_lookup mseccfg mc_rs = mseccfg0.
  Proof. ck mm_rs_sec. Qed.
  Lemma mc_rs_pma : register_lookup pma_regions mc_rs = pmar0.
  Proof. ck mm_rs_pma. Qed.
  Lemma mc_rs_htif : register_lookup htif_tohost_base mc_rs = None.
  Proof. ck mm_rs_htif. Qed.
  Lemma mc_rs_elp : register_lookup elp mc_rs = elp0.
  Proof. ck mm_rs_elp. Qed.
  Lemma mc_rs_senv : register_lookup senvcfg mc_rs = senv0.
  Proof. ck mm_rs_senv. Qed.

End ctower.

(* same reason as [mm_rs]: nothing downstream may see the tower's body *)
Global Opaque mc_rs.

Ltac mc_rs_lk :=
  first [ apply mc_rs_PC | apply mc_rs_nPC | apply mc_rs_ms | apply mc_rs_mi
        | apply mc_rs_cy | apply mc_rs_ti | apply mc_rs_ip | apply mc_rs_priv
        | apply mc_rs_mst | apply mc_rs_hart | apply mc_rs_pcfg
        | apply mc_rs_mc | apply mc_rs_micfg | apply mc_rs_misa
        | apply mc_rs_sec | apply mc_rs_pma | apply mc_rs_htif
        | apply mc_rs_elp | apply mc_rs_senv ].

Section cagree.
  Context (priv : Privilege).
  Context (pc npc ms : SailStdpp.Values.mword 64) (bmi : bool).
  Context (cy ti ip mst0 : SailStdpp.Values.mword 64).
  Context (pcfg : type_of_register pmpcfg_n).
  Context (mc : SailStdpp.Values.mword 32).
  Context (micfg misa0 mseccfg0 : SailStdpp.Values.mword 64).
  Context (pmar0 : type_of_register pma_regions).
  Context (elp0 : type_of_register elp).
  Context (senv0 : SailStdpp.Values.mword 64).

  (* the 19-way decomposition, once, with ONE side a variable (see
     HartMFrame's note: a lemma with a tower on each side is the two-tower
     conversion trap) *)
  Lemma mc_rs_agree (rs : regstate) :
    register_lookup (R_bitvector_64 PC) rs = pc ->
    register_lookup (R_bitvector_64 nextPC) rs = npc ->
    register_lookup (R_bitvector_64 minstret) rs = ms ->
    register_lookup (R_bool minstret_increment) rs = bmi ->
    register_lookup (R_bitvector_64 mcycle) rs = cy ->
    register_lookup (R_bitvector_64 mtime) rs = ti ->
    register_lookup (R_bitvector_64 mip) rs = ip ->
    register_lookup cur_privilege rs = priv ->
    register_lookup mstatus rs = mst0 ->
    register_lookup hart_state rs = HART_ACTIVE tt ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup (R_bitvector_32 mcountinhibit) rs = mc ->
    register_lookup (R_bitvector_64 minstretcfg) rs = micfg ->
    register_lookup misa rs = misa0 ->
    register_lookup mseccfg rs = mseccfg0 ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup elp rs = elp0 ->
    register_lookup senvcfg rs = senv0 ->
    reg_agree_on (mm_Drw ∪ mm_Dro) rs
      (mc_rs priv pc npc ms bmi cy ti ip mst0 pcfg mc micfg misa0 mseccfg0
         pmar0 elp0 senv0).
  Proof.
    intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17
      H18 H19.
    intros r Hr. rewrite /mm_Drw /mm_Dro in Hr.
    repeat (apply elem_of_union in Hr as [Hr|Hr]);
      apply elem_of_singleton in Hr; subst r.
    all: first
      [ by rewrite H1 mc_rs_PC | by rewrite H2 mc_rs_nPC
      | by rewrite H3 mc_rs_ms | by rewrite H4 mc_rs_mi
      | by rewrite H5 mc_rs_cy | by rewrite H6 mc_rs_ti
      | by rewrite H7 mc_rs_ip | by rewrite H8 mc_rs_priv
      | by rewrite H9 mc_rs_mst | by rewrite H10 mc_rs_hart
      | by rewrite H11 mc_rs_pcfg | by rewrite H12 mc_rs_mc
      | by rewrite H13 mc_rs_micfg | by rewrite H14 mc_rs_misa
      | by rewrite H15 mc_rs_sec | by rewrite H16 mc_rs_pma
      | by rewrite H17 mc_rs_htif | by rewrite H18 mc_rs_elp
      | by rewrite H19 mc_rs_senv ].
  Qed.
End cagree.

(* the tail transport, [mm_tick_agree]'s twin at the parametric tower: the
   cycle commits nextPC into PC and sets minstret, then the tick moves
   mcycle/mtime/mip -- which the [∖ tk_clock3] leaves unpinned, so those
   three are read straight off the successor file. *)
Lemma mc_tick_agree (priv : Privilege) (pc npc ms : SailStdpp.Values.mword 64)
    (bmi : bool) (cy ti ip mst0 : SailStdpp.Values.mword 64)
    (pcfg : type_of_register pmpcfg_n) (mc : SailStdpp.Values.mword 32)
    (micfg misa0 mseccfg0 senv0 : SailStdpp.Values.mword 64)
    (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
    (mi : SailStdpp.Values.mword 64) (rs : regstate) :
  reg_agree_on ((mm_Drw ∪ mm_Dro) ∖ tk_clock3) rs
    (wrap_post (mc_rs priv pc npc ms bmi cy ti ip mst0 pcfg mc micfg misa0
                  mseccfg0 pmar0 elp0 senv0) mi) ->
  reg_agree_on (mm_Drw ∪ mm_Dro) rs
    (mc_rs priv npc npc mi bmi
       (register_lookup (R_bitvector_64 mcycle) rs)
       (register_lookup (R_bitvector_64 mtime) rs)
       (register_lookup (R_bitvector_64 mip) rs)
       mst0 pcfg mc micfg misa0 mseccfg0 pmar0 elp0 senv0).
Proof.
  intros Hag. apply mc_rs_agree.
  all: try reflexivity.
  all: (etransitivity;
        [ apply Hag; rewrite /mm_Drw /mm_Dro /tk_clock3; set_solver | ]).
  all: try (by rewrite wrap_post_PC mc_rs_nPC).
  all: try (by rewrite wrap_post_ms).
  all: rewrite wrap_post_other;
    [| vm_compute; reflexivity | vm_compute; reflexivity ].
  all: mc_rs_lk.
Qed.

(* nextPC is in [mm_Drw], so the READ-ONLY frame does not see the fetch's
   nextPC write -- which is what lets the accessor below hand its frame back
   at the tower the cycle rule names.  [mm_ro_nPC]'s twin; discharged
   POSITIONALLY for the reason recorded there (a [first [...]] over failing
   [apply]s must not be let near a tower). *)
Lemma mc_ro_nPC (priv : Privilege) (pc x y ms : SailStdpp.Values.mword 64)
    (bmi : bool) (cy ti ip mst0 : SailStdpp.Values.mword 64)
    (pcfg : type_of_register pmpcfg_n) (mc : SailStdpp.Values.mword 32)
    (micfg misa0 mseccfg0 senv0 : SailStdpp.Values.mword 64)
    (pmar0 : type_of_register pma_regions) (elp0 : type_of_register elp) :
  reg_agree_on mm_Dro
    (mc_rs priv pc x ms bmi cy ti ip mst0 pcfg mc micfg misa0 mseccfg0
       pmar0 elp0 senv0)
    (mc_rs priv pc y ms bmi cy ti ip mst0 pcfg mc micfg misa0 mseccfg0
       pmar0 elp0 senv0).
Proof.
  intros r Hr. rewrite /mm_Dro in Hr.
  repeat (apply elem_of_union in Hr as [Hr|Hr]);
    apply elem_of_singleton in Hr; subst r.
  all: (etransitivity;
        [ first [ apply mc_rs_priv | apply mc_rs_mst | apply mc_rs_hart
                | apply mc_rs_pcfg | apply mc_rs_mc | apply mc_rs_micfg
                | apply mc_rs_misa | apply mc_rs_sec | apply mc_rs_pma
                | apply mc_rs_htif | apply mc_rs_elp | apply mc_rs_senv ]
        | symmetry;
          first [ apply mc_rs_priv | apply mc_rs_mst | apply mc_rs_hart
                | apply mc_rs_pcfg | apply mc_rs_mc | apply mc_rs_micfg
                | apply mc_rs_misa | apply mc_rs_sec | apply mc_rs_pma
                | apply mc_rs_htif | apply mc_rs_elp | apply mc_rs_senv ] ]).
Qed.

Section WpInstrConfig.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac mmrs :=
    by rewrite ?mm_rs_PC ?mm_rs_nPC ?mm_rs_ms ?mm_rs_mi ?mm_rs_cy ?mm_rs_ti
       ?mm_rs_ip ?mm_rs_priv ?mm_rs_mst ?mm_rs_hart ?mm_rs_pcfg ?mm_rs_mc
       ?mm_rs_micfg ?mm_rs_misa ?mm_rs_sec ?mm_rs_pma ?mm_rs_htif ?mm_rs_elp
       ?mm_rs_senv.

  (* ------------------------------------------------------------------ *)
  (* THE RAW-CELL <-> FRAME BRIDGE.  [mm_frames_intro]'s twin: same       *)
  (* frames out, but the config arrives as cells, so no [mmode_config]    *)
  (* is built and its MPRV / SXL / kernel-facts conjuncts are not         *)
  (* required.  That is what keeps this wrapper's premise list down to    *)
  (* the MIE fact alone.                                                 *)
  (* ------------------------------------------------------------------ *)
  Lemma mc_frames_intro (pc ms0 : mword 64)
      (pcfg0 : type_of_register pmpcfg_n) :
    hw_config -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Machine -∗
    mstatus ↦ᵣ ms0 -∗
    pmpcfg_n ↦ᵣ pcfg0 -∗
    pc_is pc -∗
    resv_any cpu_id ∗
    ∃ (ms : mword 64) (bmi : bool) (cy ti ip : mword 64) (mc : mword 32)
      (micfg misa0 mseccfg0 senv0 : mword 64) (pmar0 : list PMA_Region)
      (elp0 : type_of_register elp),
      ⌜ eq_vec (_get_Misa_S misa0) ('b"1") = true ⌝ ∗
      ⌜ eq_vec (_get_Misa_C misa0) ('b"1") = true ⌝ ∗
      ⌜ eq_vec (_get_Misa_A misa0) ('b"1") = true ⌝ ∗
      ⌜ misa0 = MISA_C ⌝ ∗
      ⌜ mseccfg0 = mword_of_int 0 ⌝ ∗
      ⌜ pma_allows_all pmar0 ⌝ ∗
      ⌜ eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ⌝ ∗
      hreg_frame (mm_rs pc pc ms bmi cy ti ip ms0 pcfg0 mc micfg misa0
                    mseccfg0 pmar0 elp0 senv0) mm_Drw ∗
      hreg_frame_ro (mm_Df (DfracOwn 1))
        (mm_rs pc pc ms bmi cy ti ip ms0 pcfg0 mc micfg misa0
           mseccfg0 pmar0 elp0 senv0) mm_Dro.
  Proof.
    iIntros "#Hhw Hhs Hpriv Hmstatus Hpmpc Hpc".
    iDestruct "Hpc" as "(HPC & HnPC & Hmr & Hcr & Hresv)". iFrame "Hresv".
    iDestruct "Hmr" as (ms bmi mc micfg) "(Hms & Hmi & #Hmc & #Hmicfg)".
    iDestruct "Hcr" as (cy ti ip) "(Hcy & Hti & Hip)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmS & %HmC &
        %HmU & %HmM & %Hpmaall & %Hsec1 & %Hsec2 & %Helpnp & %HmA &
        %Hmisaval & %Hsecval & _)".
    iExists ms, bmi, cy, ti, ip, mc, micfg, misa0, mseccfg0,
            (mword_of_int 0 : mword 64), pmar0, elp0.
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iSplitL "HPC HnPC Hms Hmi Hcy Hti Hip".
    - rewrite mm_rw_split.
      rewrite mm_rs_PC mm_rs_nPC mm_rs_ms mm_rs_mi mm_rs_cy mm_rs_ti
        mm_rs_ip. iFrame.
    - rewrite mm_ro_split.
      rewrite mm_rs_priv mm_rs_mst mm_rs_hart mm_rs_pcfg mm_rs_mc
        mm_rs_micfg mm_rs_misa mm_rs_sec mm_rs_pma mm_rs_htif mm_rs_elp
        mm_rs_senv.
      iFrame "Hpriv Hmstatus Hhs Hpmpc".
      by iFrame "Hmc Hmicfg Hmisa Hmseccfg Hpma Hhtif Help Hsenv".
  Qed.

  (* ... and back, at the parametric tower: the continuation of a
     config-writing instruction gets CELLS, never a bundle -- rebuilding
     [mmode_config] needs invariant facts about the WRITTEN mstatus, which
     only the leaf knows. *)
  Lemma mc_frames_elim (priv1 : Privilege) (npc : mword 64)
      (pcfg1 : type_of_register pmpcfg_n)
      (ms : mword 64) (bmi : bool) (cy ti ip mst1 : mword 64)
      (mc : mword 32) (micfg misa0 mseccfg0 senv0 : mword 64)
      (pmar0 : list PMA_Region) (elp0 : type_of_register elp) :
    resv_any cpu_id -∗
    hreg_frame (mc_rs priv1 npc npc ms bmi cy ti ip mst1 pcfg1 mc micfg
                  misa0 mseccfg0 pmar0 elp0 senv0) mm_Drw -∗
    hreg_frame_ro (mm_Df (DfracOwn 1))
      (mc_rs priv1 npc npc ms bmi cy ti ip mst1 pcfg1 mc micfg misa0
         mseccfg0 pmar0 elp0 senv0) mm_Dro -∗
    hart_state ↦ᵣ HART_ACTIVE tt ∗ cur_privilege ↦ᵣ priv1 ∗
    mstatus ↦ᵣ mst1 ∗ pmpcfg_n ↦ᵣ pcfg1 ∗ pc_is npc.
  Proof.
    iIntros "Hresv Hrw Hro".
    rewrite mm_rw_split mm_ro_split.
    rewrite mc_rs_PC mc_rs_nPC mc_rs_ms mc_rs_mi mc_rs_cy mc_rs_ti mc_rs_ip.
    rewrite mc_rs_priv mc_rs_mst mc_rs_hart mc_rs_pcfg mc_rs_mc
      mc_rs_micfg mc_rs_misa mc_rs_sec mc_rs_pma mc_rs_htif mc_rs_elp
      mc_rs_senv.
    iDestruct "Hrw" as "(HPC & HnPC & Hms & Hmi & Hcy & Hti & Hip)".
    iDestruct "Hro" as "(Hpriv & Hmst & Hhs & Hpcfg & #Hmc & #Hmicfg & _)".
    iFrame "Hhs Hpriv Hmst Hpcfg".
    rewrite /pc_is /minstret_res /clock_res.
    iFrame "HPC HnPC Hresv".
    iSplitL "Hms Hmi".
    - iExists ms, bmi, mc, micfg. by iFrame "Hms Hmi Hmc Hmicfg".
    - iExists cy, ti, ip. by iFrame.
  Qed.

  (* the READ-ONLY frame at the parametric tower: [mm_ro_open]'s mirror, and
     what [mc_ro_acc]'s closure rebuilds.  Directed, so no caller rewrites
     [mm_ro_split] against a goal that carries the tower (optimization.md,
     "Directed entailments, not ⊣⊢ rewrites, for frame bridges"). *)
  Lemma mc_ro_close (dq : dfrac) (priv1 : Privilege) (pc npc ms : mword 64)
      (bmi : bool) (cy ti ip mst1 : mword 64)
      (pcfg1 : type_of_register pmpcfg_n) (mc : mword 32)
      (micfg misa0 mseccfg0 senv0 : mword 64)
      (pmar0 : list PMA_Region) (elp0 : type_of_register elp) :
    (reg_pointsto cur_privilege dq priv1 ∗
     reg_pointsto mstatus dq mst1 ∗
     reg_pointsto hart_state dq (HART_ACTIVE tt) ∗
     reg_pointsto pmpcfg_n dq pcfg1 ∗
     reg_pointsto (R_bitvector_32 mcountinhibit) DfracDiscarded mc ∗
     reg_pointsto (R_bitvector_64 minstretcfg) DfracDiscarded micfg ∗
     reg_pointsto misa DfracDiscarded misa0 ∗
     reg_pointsto mseccfg DfracDiscarded mseccfg0 ∗
     reg_pointsto pma_regions DfracDiscarded pmar0 ∗
     reg_pointsto htif_tohost_base DfracDiscarded None ∗
     reg_pointsto elp DfracDiscarded elp0 ∗
     reg_pointsto senvcfg DfracDiscarded senv0 : iProp Σ) -∗
    hreg_frame_ro (mm_Df dq)
      (mc_rs priv1 pc npc ms bmi cy ti ip mst1 pcfg1 mc micfg misa0
         mseccfg0 pmar0 elp0 senv0) mm_Dro.
  Proof.
    rewrite mm_ro_split mc_rs_priv mc_rs_mst mc_rs_hart mc_rs_pcfg mc_rs_mc
      mc_rs_micfg mc_rs_misa mc_rs_sec mc_rs_pma mc_rs_htif mc_rs_elp
      mc_rs_senv. iIntros "H". iExact "H".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE THREE WRITTEN CELLS, LENT AND TAKEN BACK.  One accessor rather   *)
  (* than an open/close pair, so the nine cells the leaf never sees       *)
  (* (hart_state and the eight persistent ones) stay in the closure       *)
  (* instead of being threaded through every leaf statement.              *)
  (* ------------------------------------------------------------------ *)
  Lemma mc_ro_acc (pc npc ms : mword 64) (bmi : bool)
      (cy ti ip mst0 : mword 64) (pcfg : type_of_register pmpcfg_n)
      (mc : mword 32) (micfg misa0 mseccfg0 senv0 : mword 64)
      (pmar0 : list PMA_Region) (elp0 : type_of_register elp) :
    hreg_frame_ro (mm_Df (DfracOwn 1))
      (mm_rs pc npc ms bmi cy ti ip mst0 pcfg mc micfg misa0 mseccfg0
         pmar0 elp0 senv0) mm_Dro -∗
    cur_privilege ↦ᵣ Machine ∗ mstatus ↦ᵣ mst0 ∗ pmpcfg_n ↦ᵣ pcfg ∗
    (∀ (priv1 : Privilege) (mst1 : mword 64)
       (pcfg1 : type_of_register pmpcfg_n),
       cur_privilege ↦ᵣ priv1 -∗ mstatus ↦ᵣ mst1 -∗ pmpcfg_n ↦ᵣ pcfg1 -∗
       hreg_frame_ro (mm_Df (DfracOwn 1))
         (mc_rs priv1 pc npc ms bmi cy ti ip mst1 pcfg1 mc micfg misa0
            mseccfg0 pmar0 elp0 senv0) mm_Dro).
  Proof.
    (* BOTH BRIDGES ARE APPLIED, NOT REWRITTEN.  This goal carries the whole
       [mc_rs] tower inside the ∀-closure, and a [rewrite mm_ro_split] fires
       on the entire [envs_entails Δ Q] -- 24.9 s for the first of the two,
       the most expensive statement in this file.  [mm_ro_open] /
       [mc_ro_close] do the same twelve-cell split and its twelve lookups
       where the goal is two lines long. *)
    iIntros "Hro".
    iDestruct (mm_ro_open with "Hro") as
      "(Hpriv & Hmst & Hhs & Hpcfg & #Hmc & #Hmicfg &
        #Hmisa & #Hsec & #Hpma & #Hhtif & #Help & #Hsenv)".
    iFrame "Hpriv Hmst Hpcfg".
    iIntros (priv1 mst1 pcfg1) "Hpriv Hmst Hpcfg".
    iApply mc_ro_close.
    iFrame "Hpriv Hmst Hhs Hpcfg".
    by iFrame "Hmc Hmicfg Hmisa Hsec Hpma Hhtif Help Hsenv".
  Qed.

  (* the writable frame at the parametric tower: [mm_Drw] holds none of the
     three written cells, so this is [mm_rw_close] with the tower's own
     seven lookups. *)
  Lemma mc_rw_close (priv1 : Privilege) (pc npc ms : mword 64) (bmi : bool)
      (cy ti ip mst1 : mword 64) (pcfg1 : type_of_register pmpcfg_n)
      (mc : mword 32) (micfg misa0 mseccfg0 senv0 : mword 64)
      (pmar0 : list PMA_Region) (elp0 : type_of_register elp) :
    ((R_bitvector_64 PC) ↦ᵣ pc ∗ (R_bitvector_64 nextPC) ↦ᵣ npc ∗
     (R_bitvector_64 minstret) ↦ᵣ ms ∗ (R_bool minstret_increment) ↦ᵣ bmi ∗
     (R_bitvector_64 mcycle) ↦ᵣ cy ∗ (R_bitvector_64 mtime) ↦ᵣ ti ∗
     (R_bitvector_64 mip) ↦ᵣ ip : iProp Σ) -∗
    hreg_frame (mc_rs priv1 pc npc ms bmi cy ti ip mst1 pcfg1 mc micfg
                  misa0 mseccfg0 pmar0 elp0 senv0) mm_Drw.
  Proof.
    rewrite mm_rw_split mc_rs_PC mc_rs_nPC mc_rs_ms mc_rs_mi mc_rs_cy
      mc_rs_ti mc_rs_ip. iIntros "H". iExact "H".
  Qed.

  (* ==================================================================== *)
  (* mc_cycle -- the cycle rule at the parametric post-file.               *)
  (*                                                                      *)
  (* [mm_cycle]'s twin.  The generic rule already allows an arbitrary      *)
  (* post-file [rsB], so the only difference is which tower is named and   *)
  (* which bridge closes the continuation: raw cells, not a bundle -- and  *)
  (* therefore NO mstatus invariant facts (they exist to rebuild           *)
  (* [mmode_config], and this wrapper's caller is the one that knows what  *)
  (* it wrote).                                                           *)
  (* ==================================================================== *)
  Lemma mc_cycle (pc npc : mword 64) (priv1 : Privilege)
      (pcfg0 pcfg1 : type_of_register pmpcfg_n) (Psi : iProp Σ)
      (ms : mword 64) (bmi : bool) (cy ti ip mst0 mst1 : mword 64)
      (mc : mword 32) (micfg misa0 mseccfg0 senv0 : mword 64)
      (pmar0 : list PMA_Region) (elp0 : type_of_register elp) :
    hw_config -∗
    resv_any cpu_id -∗
    hreg_frame (mm_rs pc pc ms bmi cy ti ip mst0 pcfg0 mc micfg misa0
                  mseccfg0 pmar0 elp0 senv0) mm_Drw -∗
    hreg_frame_ro (mm_Df (DfracOwn 1))
      (mm_rs pc pc ms bmi cy ti ip mst0 pcfg0 mc micfg misa0 mseccfg0
         pmar0 elp0 senv0) mm_Dro -∗
    (hreg_frame (mm_rs pc pc ms (minstret_inc_flag mc micfg Machine) cy ti ip mst0
                   pcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) mm_Drw -∗
     hreg_frame_ro (mm_Df (DfracOwn 1))
       (mm_rs pc pc ms (minstret_inc_flag mc micfg Machine) cy ti ip mst0 pcfg0 mc
          micfg misa0 mseccfg0 pmar0 elp0 senv0) mm_Dro -∗
       swp (run_hart_active 0)
         (fun st => ∃ w : mword 32,
                    ⌜st = Step_Execute (RETIRE_SUCCESS, w)⌝ ∗
                    hreg_frame (mc_rs priv1 pc npc ms
                                  (minstret_inc_flag mc micfg Machine) cy ti ip mst1
                                  pcfg1 mc micfg misa0 mseccfg0 pmar0 elp0
                                  senv0) mm_Drw ∗
                    hreg_frame_ro (mm_Df (DfracOwn 1))
                      (mc_rs priv1 pc npc ms (minstret_inc_flag mc micfg Machine)
                         cy ti ip mst1 pcfg1 mc micfg misa0 mseccfg0 pmar0
                         elp0 senv0) mm_Dro ∗ Psi)) -∗
    ▷ (hart_state ↦ᵣ HART_ACTIVE tt -∗ cur_privilege ↦ᵣ priv1 -∗
       mstatus ↦ᵣ mst1 -∗ pmpcfg_n ↦ᵣ pcfg1 -∗ pc_is npc -∗ Psi -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hhw Hfrag Hrw Hro Hbody Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iApply (swp_exec_step_decode_execute mm_Drw mm_Dro (mm_Df (DfracOwn 1))
              (mm_rs pc pc ms bmi cy ti ip mst0 pcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) (mm_rs pc pc ms (minstret_inc_flag mc micfg Machine) cy ti ip mst0 pcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) (mc_rs priv1 pc npc ms (minstret_inc_flag mc micfg Machine) cy ti ip mst1 pcfg1 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) (Psi ∗ resv_any cpu_id)%I
              mm_disj mm_w_cy mm_w_ti mm_w_ip mm_in_priv mm_in_hart mm_in_mc
              mm_in_micfg mm_w_mi mm_in_mi mm_w_ms mm_in_ms mm_w_PC mm_in_PC
              mm_in_nPC ltac:(mmrs)
              (mc_rs_hart priv1 pc npc ms (minstret_inc_flag mc micfg Machine) cy ti
                 ip mst1 pcfg1 mc micfg misa0 mseccfg0 pmar0 elp0 senv0)
              ltac:(etransitivity;
                    [ apply mc_rs_mi
                    | by rewrite mm_rs_mc mm_rs_micfg mm_rs_priv ])
              (mm_pre_agree pc ms bmi cy ti ip mst0 pcfg0 mc micfg misa0
                 mseccfg0 senv0 pmar0 elp0)
              with "Hcert Hfrag Hrw Hro [Hbody] [Hcont]").
    2:{ iNext. iIntros (rs3) "%Hag Hrw Hro [HPsi Hfrag]".
        destruct Hag as (mi & Hag).
        pose proof (mc_tick_agree priv1 pc npc ms (minstret_inc_flag mc micfg Machine)
                      cy ti ip mst1 pcfg1 mc micfg misa0 mseccfg0 senv0
                      pmar0 elp0 mi rs3 Hag) as Hag'.
        iDestruct (mm_rw_ext _ _ Hag' with "Hrw") as "Hrw".
        iDestruct (mm_ro_ext (DfracOwn 1) _ _ Hag' with "Hro") as "Hro".
        iDestruct (mc_frames_elim priv1 npc pcfg1 mi
                     (minstret_inc_flag mc micfg Machine) _ _ _ mst1 mc micfg misa0
                     mseccfg0 senv0 pmar0 elp0 with "Hfrag Hrw Hro")
          as "(Hhs & Hpriv & Hmst & Hpcfg & Hpc)".
        iApply ("Hcont" with "Hhs Hpriv Hmst Hpcfg Hpc HPsi"). }
    iIntros "Hfrag Hrw Hro".
    iApply (swp_mono with "[Hfrag] [-]"); [|iApply ("Hbody" with "Hrw Hro")].
    iIntros (st). iDestruct 1 as (w) "(-> & Hrw & Hro & HPsi)".
    iExists w. iFrame "Hrw Hro HPsi". iSplitR; [done|].
    iApply (resv_any_intro with "Hfrag").
  Qed.

  (* ==================================================================== *)
  (* wp_instr_config.                                                      *)
  (*                                                                      *)
  (* Same surface as the exec-based rule it replaces: the unbundled config *)
  (* cells at FULL ownership with the mstatus VALUE explicit, only the MIE *)
  (* fact required (it discharges [dispatchInterrupt]), and the engine     *)
  (* passing those cells INTO the caller's obligation so the caller can    *)
  (* write them alongside its own.  The obligation is a [swp] over         *)
  (* [execute i] instead of a fupd handing back a whole successor sigma --  *)
  (* the one difference per-node stepping forces, exactly as in            *)
  (* [wp_instr].                                                          *)
  (*                                                                      *)
  (* The continuation takes the cells back at the caller's new values.     *)
  (* [minstret_inv] is kept as a premise so upstream callers do not have   *)
  (* to notice that the invariant is gone.                                *)
  (* ==================================================================== *)
  Lemma wp_instr_config (pc npc : mword 64) (is_rvc : bool) (i : instruction)
      (m m' : regfile) (priv1 : Privilege) (ms0 ms1 : mword 64)
      (pmpcfg0 pmpcfg1 : type_of_register pmpcfg_n) (R : iProp Σ) :
    pmp_allows_all pmpcfg0 ->
    eq_vec (_get_Mstatus_MIE ms0) ('b"1") = false ->
    (forall j, (j < 4)%nat -> kmap_static (svpn_of (pa_add pc j)) KP_rx) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Machine -∗
    mstatus ↦ᵣ ms0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc i -∗
    (cur_privilege ↦ᵣ Machine -∗
     mstatus ↦ᵣ ms0 -∗
     pmpcfg_n ↦ᵣ pmpcfg0 -∗
     gpr_file m -∗
     (R_bitvector_64 PC) ↦ᵣ pc -∗
     (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc (if is_rvc then 2 else 4)) -∗
       swp (execute i)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                   cur_privilege ↦ᵣ priv1 ∗ mstatus ↦ᵣ ms1 ∗
                   pmpcfg_n ↦ᵣ pmpcfg1 ∗ gpr_file m' ∗
                   (R_bitvector_64 PC) ↦ᵣ pc ∗
                   (R_bitvector_64 nextPC) ↦ᵣ npc ∗ R)) -∗
    ▷ (hart_state ↦ᵣ HART_ACTIVE tt -∗ cur_privilege ↦ᵣ priv1 -∗
       mstatus ↦ᵣ ms1 -∗ pmpcfg_n ↦ᵣ pmpcfg1 -∗ pc_is npc -∗
       gpr_file m' -∗ R -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hpmp HmIE Hstat.
    iIntros "#Hhw _ Hhs Hpriv Hms Hpmpc Hpc Hgpr Hinstr Hex Hcont".
    iDestruct (mc_frames_intro pc ms0 pmpcfg0
                 with "Hhw Hhs Hpriv Hms Hpmpc Hpc") as "[Hfrag Hfr]".
    iDestruct "Hfr" as (ms bmi cy ti ip mc micfg misa0 mseccfg0 senv0
        pmar0 elp0)
      "(%HmS & %HmC & %HmA & %Hmisaval & %Hsecval & %Hpmaall & %Helpnp &
        Hrw & Hro)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iDestruct (hw_config_kmap with "Hhw") as "#Hkm".
    iApply (mc_cycle pc npc priv1 pmpcfg0 pmpcfg1 (gpr_file m' ∗ R)%I
              ms bmi cy ti ip ms0 ms1 mc micfg misa0 mseccfg0 senv0 pmar0
              elp0 with "Hhw Hfrag Hrw Hro [Hgpr Hinstr Hex] [Hcont]").
    2:{ iNext. iIntros "Hhs Hpriv Hms Hpmpc Hpc [Hgpr HR]".
        iApply ("Hcont" with "Hhs Hpriv Hms Hpmpc Hpc Hgpr HR"). }
    assert (Hdok : decode_ok (mm_Drw ∪ mm_Dro) (mm_rs pc pc ms (minstret_inc_flag mc micfg Machine) cy ti ip ms0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0)).
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
    pose proof (hfrun_lpad (mm_Drw ∪ mm_Dro) mm_Drw (mm_rs pc pc ms (minstret_inc_flag mc micfg Machine) cy ti ip ms0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0)
                  mm_in_elp ltac:(rewrite mm_rs_elp; exact Helpnp)) as Hlp.
    iIntros "Hrw Hro".
    iApply (swp_run_hart_active_instr mm_Drw mm_Dro (mm_Df (DfracOwn 1))
              (mm_rs pc pc ms (minstret_inc_flag mc micfg Machine) cy ti ip ms0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) (mc_rs priv1 pc npc ms (minstret_inc_flag mc micfg Machine) cy ti ip ms1 pmpcfg1 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) pc is_rvc i pmar0 pmpcfg0 (gpr_file m' ∗ R)%I
              mm_disj mm_in_priv mm_in_misa mm_in_mst mm_in_PC mm_w_nPC
              mm_in_pma mm_in_pcfg mm_in_htif
              ltac:(mmrs) ltac:(mmrs) ltac:(mmrs) ltac:(mmrs) ltac:(mmrs)
              ltac:(rewrite mm_rs_misa; exact HmS)
              ltac:(rewrite mm_rs_misa; exact HmC)
              ltac:(rewrite mm_rs_mst; exact HmIE)
              Hpmp Hpmaall Hstat Hdok Hlp
              with "Hcert Hkm Hinstr Hrw Hro [Hgpr Hex]").
    iIntros "Hrw Hro".
    pose proof (mm_npc_agree pc pc ms (minstret_inc_flag mc micfg Machine) cy ti ip
                   ms0 pmpcfg0 mc micfg misa0 mseccfg0 senv0 pmar0 elp0
                   (add_vec_int pc (if is_rvc then 2 else 4))) as Hnp.
    iDestruct (mm_rw_ext _ _ Hnp with "Hrw") as "Hrw".
    iDestruct (mm_ro_ext (DfracOwn 1) _ _ Hnp with "Hro") as "Hro".
    iDestruct (mm_rw_open with "Hrw")
      as "(HPC & HnPC & Hms & Hmi & Hcy & Hti & Hip)".
    iDestruct (mc_ro_acc with "Hro") as "(Hpriv & Hmst & Hpcfg & Hcl)".
    iApply (swp_mono with "[Hms Hmi Hcy Hti Hip Hcl] [-]");
      [| iApply ("Hex" with "Hpriv Hmst Hpcfg Hgpr HPC HnPC") ].
    iIntros (u) "(-> & Hpriv & Hmst & Hpcfg & Hgpr & HPC & HnPC & HR)".
    iSplitR; [done|].
    iSplitL "HPC HnPC Hms Hmi Hcy Hti Hip".
    { iApply mc_rw_close. iFrame "HPC HnPC Hms Hmi Hcy Hti Hip". }
    iSplitL "Hcl Hpriv Hmst Hpcfg".
    { iApply (mm_ro_ext' (DfracOwn 1) _ _
                (mc_ro_nPC priv1 pc
                   (add_vec_int pc (if is_rvc then 2 else 4)) npc ms
                   (minstret_inc_flag mc micfg Machine) cy ti ip ms1 pmpcfg1 mc
                   micfg misa0 mseccfg0 senv0 pmar0 elp0)).
      iApply ("Hcl" with "Hpriv Hmst Hpcfg"). }
    iFrame "Hgpr HR".
  Qed.

End WpInstrConfig.
