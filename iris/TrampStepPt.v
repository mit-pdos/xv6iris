(* TrampStepPt.v -- the S-mode TRAMPOLINE-page fetch and step engine, PER
   NODE.  One S-mode instruction whose VA is a trampoline va [pc] and whose
   BYTES live at the physical [pa] on the trampoline page: the two are tied
   by the geometry premises below and by the BYTES' OWN CLAIM -- [instr pa]
   is [↦ₓ□] data, so [code_text] hands over the [kmap_at] for the window,
   [text_canonical] its canonicality and the datum's tier pin its identity
   ([ktier_pin_id]).  NOTHING comes from a static bundle: the whole
   side-condition of the fetch's memory side is a projection of the
   points-to of the bytes being fetched (the user rule, recorded in
   claude-notes/projects/main-cycle-port.md).

   [wp_instr_tramp_pt] is [SmodeCorePt.wp_instr_s_config_regime] with that
   va/pa split, and the whole-cycle [Habs] (a [translateAddr] fupd over a
   whole sigma, which per-node stepping makes unsound -- other harts run
   between the walk's nodes) is replaced by the per-node obligation
   [tramp_tr_obl] / [tramp_fetch_tr], which is [SRegime.sr_swp_translate]'s
   shape at [InstructionFetch tt].

   THE PRODUCER IS THE WITNESSED ONE.  A trampoline va's claim is
   [kmap_at tramp_vpn tramp_ppn KP_rx], whose ppn is NOT [svpn_of va], so
   there is no [ktier_pin] to feed [sr_adm] and [spt_tr_obl_of_regime] does
   not apply.  [tramp_tr_obl_of_regime] takes [sr_swp_translate_wit]
   instead -- admissibility dropped in favour of the regime's all-claims
   witness [sr_kwit], which is [emp] at [kpt_share_regime] and [False] at
   Bare (which is what keeps the route sound).

   THE THREE TABLES.  The engine is regime-generic in [Res] and each table
   supplies its own [tramp_fetch_tr] producer plus a wrapper that opens its
   bundle into the engine's cells:
     - the SHARED KERNEL table: [ktramp_fetch_tr_share] and
       [wp_instr_ktramp_pt_share] below, off [SRegime.kpt_share_regime] /
       [HartSKpt.swp_translate_kpt];
     - the USER table [UptTree.utlb_inv_pt]: [UptWalkPt.utramp_fetch_tr] and
       [UptWalkPt.wp_instr_u_pt], off [UptWalkPt.swp_translate_upt];
     - the switch-window two-table invariants [TransPt.tlb_inv_pt2_kcur] /
       [_kprev] have NO per-node walk yet.  They are exec-level today
       ([tlb_inv_pt2_translateAddr]) and differ from [utlb_inv_pt] in the
       TLB agreement ([tlb_ok_pt2] over two trees) and in taking an abstract
       tree spec, so [swp_translate_upt] does not instantiate: the exec side
       is [TransPt.ptree2_translateAddr_cases] and the certificate has to be
       its [goodmb] twin.  Until that exists, TransPt.v, [UserretEntryPt]
       and [UservecExitPt] stay red. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import KMap.
Require Import KptExecMap.
Require Import SmodeCore SmodeCorePt KptTree UptTree PtFetchGen.
Require Import PtTree PtAdBits PtTreeAdue KptGhost KptShare.
Require Import KptPt UserBits SRegime KptGoodb.
Require Import HartSwp HartLift HartSpan HartSpanChar HartSFrame.
Require Import HartEvents HartRegNode HartMCycle HartStepAny HartRunGen.
Require Import HartMFetch HartSTrans.
Require Import WpDecodeBridge WpIntrCore CommonWalk HartGoodb.
Require Import WpInstrRun WpSFrames.
Require Import SmodePte WpSmodePtFetch.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

Local Ltac srs_lk_g :=
  by rewrite ?s_rs_PC ?s_rs_nPC ?s_rs_ms ?s_rs_mi ?s_rs_cy ?s_rs_ti
     ?s_rs_ip ?s_rs_tlb ?s_rs_priv ?s_rs_mst ?s_rs_hart ?s_rs_pcfg
     ?s_rs_paddr ?s_rs_mc ?s_rs_micfg ?s_rs_misa ?s_rs_sec ?s_rs_pma
     ?s_rs_htif ?s_rs_elp ?s_rs_senv ?s_rs_satp ?s_rs_mie ?s_rs_mdl
     ?s_rs_menv.


(* ===================================================================== *)
(* THE POST FILE AT AN ARBITRARY PRIVILEGE.                               *)
(*                                                                       *)
(* [HartSFrame.s_rs] pins [cur_privilege := Supervisor], which is right   *)
(* for every S-mode instruction except the one that LEAVES S-mode -- the  *)
(* trampoline's [sret] to user.  [SmodeCorePt.spt_cycle] is already       *)
(* post-generic (its landing file is constrained only by the caller's     *)
(* [Q]), so the ONLY Supervisor-pinned pieces of the step engine are the  *)
(* three tower transports below: the cells->frame bridge, its inverse,    *)
(* and the tick's agreement.  Each is its [s_rs] twin with the privilege  *)
(* cell peeled off the front, so an S-mode caller pays nothing for the    *)
(* generality.                                                           *)
(* ===================================================================== *)

Definition s_rs_p (p : Privilege) (pc npc ms : SailStdpp.Values.mword 64)
    (bmi : bool) (cy ti ip mst0 : SailStdpp.Values.mword 64)
    (pcfg : type_of_register pmpcfg_n)
    (paddr : type_of_register pmpaddr_n)
    (mc : SailStdpp.Values.mword 32)
    (micfg misa0 mseccfg0 senv0 : SailStdpp.Values.mword 64)
    (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
    (satp0 mie0 mdv0 menv0 : SailStdpp.Values.mword 64)
    (tlbv : type_of_register tlb) : regstate :=
  register_set cur_privilege p
    (s_rs pc npc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv).

Section SRsP.
  Context (p : Privilege) (pc npc ms : SailStdpp.Values.mword 64) (bmi : bool)
          (cy ti ip mst0 : SailStdpp.Values.mword 64)
          (pcfg : type_of_register pmpcfg_n)
          (paddr : type_of_register pmpaddr_n)
          (mc : SailStdpp.Values.mword 32)
          (micfg misa0 mseccfg0 senv0 : SailStdpp.Values.mword 64)
          (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
          (satp0 mie0 mdv0 menv0 : SailStdpp.Values.mword 64)
          (tlbv : type_of_register tlb).

  Local Notation RSP := (s_rs_p p pc npc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv).

  Lemma s_rs_p_priv : register_lookup cur_privilege RSP = p.
  Proof. apply register_lookup_set. Qed.

  Lemma s_rs_p_peel (r : register) :
    register_beq r cur_privilege = false ->
    register_lookup r RSP = register_lookup r (s_rs pc npc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv).
  Proof.
    (* [exact], NOT [rewrite]: [s_rs]'s body IS a 25-deep [register_set]
       tower, so an ssreflect rewrite with [irrelevant_register_set]'s
       pattern searches inside it and detonates the record-update conversion
       bomb ([SmodeCorePt.s_npc_agree]'s note).  Here the lemma IS the goal. *)
    intro H.
    exact (irrelevant_register_set r cur_privilege
             (s_rs pc npc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv) p H).
  Qed.

  Local Ltac lkp := rewrite s_rs_p_peel; [ | vm_compute; reflexivity ].

  Lemma s_rs_p_PC : register_lookup (R_bitvector_64 PC) RSP = pc.
  Proof. lkp. apply s_rs_PC. Qed.
  Lemma s_rs_p_nPC : register_lookup (R_bitvector_64 nextPC) RSP = npc.
  Proof. lkp. apply s_rs_nPC. Qed.
  Lemma s_rs_p_ms : register_lookup (R_bitvector_64 minstret) RSP = ms.
  Proof. lkp. apply s_rs_ms. Qed.
  Lemma s_rs_p_mi : register_lookup (R_bool minstret_increment) RSP = bmi.
  Proof. lkp. apply s_rs_mi. Qed.
  Lemma s_rs_p_cy : register_lookup (R_bitvector_64 mcycle) RSP = cy.
  Proof. lkp. apply s_rs_cy. Qed.
  Lemma s_rs_p_ti : register_lookup (R_bitvector_64 mtime) RSP = ti.
  Proof. lkp. apply s_rs_ti. Qed.
  Lemma s_rs_p_ip : register_lookup (R_bitvector_64 mip) RSP = ip.
  Proof. lkp. apply s_rs_ip. Qed.
  Lemma s_rs_p_tlb : register_lookup tlb RSP = tlbv.
  Proof. lkp. apply s_rs_tlb. Qed.
  Lemma s_rs_p_mst : register_lookup mstatus RSP = mst0.
  Proof. lkp. apply s_rs_mst. Qed.
  Lemma s_rs_p_hart : register_lookup hart_state RSP = (HART_ACTIVE tt).
  Proof. lkp. apply s_rs_hart. Qed.
  Lemma s_rs_p_pcfg : register_lookup pmpcfg_n RSP = pcfg.
  Proof. lkp. apply s_rs_pcfg. Qed.
  Lemma s_rs_p_paddr : register_lookup pmpaddr_n RSP = paddr.
  Proof. lkp. apply s_rs_paddr. Qed.
  Lemma s_rs_p_mc : register_lookup (R_bitvector_32 mcountinhibit) RSP = mc.
  Proof. lkp. apply s_rs_mc. Qed.
  Lemma s_rs_p_micfg : register_lookup (R_bitvector_64 minstretcfg) RSP = micfg.
  Proof. lkp. apply s_rs_micfg. Qed.
  Lemma s_rs_p_misa : register_lookup misa RSP = misa0.
  Proof. lkp. apply s_rs_misa. Qed.
  Lemma s_rs_p_sec : register_lookup mseccfg RSP = mseccfg0.
  Proof. lkp. apply s_rs_sec. Qed.
  Lemma s_rs_p_pma : register_lookup pma_regions RSP = pmar0.
  Proof. lkp. apply s_rs_pma. Qed.
  Lemma s_rs_p_htif : register_lookup htif_tohost_base RSP = None.
  Proof. lkp. apply s_rs_htif. Qed.
  Lemma s_rs_p_elp : register_lookup elp RSP = elp0.
  Proof. lkp. apply s_rs_elp. Qed.
  Lemma s_rs_p_senv : register_lookup senvcfg RSP = senv0.
  Proof. lkp. apply s_rs_senv. Qed.
  Lemma s_rs_p_satp : register_lookup satp RSP = satp0.
  Proof. lkp. apply s_rs_satp. Qed.
  Lemma s_rs_p_mie : register_lookup mie RSP = mie0.
  Proof. lkp. apply s_rs_mie. Qed.
  Lemma s_rs_p_mdl : register_lookup mideleg RSP = mdv0.
  Proof. lkp. apply s_rs_mdl. Qed.
  Lemma s_rs_p_menv : register_lookup menvcfg RSP = menv0.
  Proof. lkp. apply s_rs_menv. Qed.

End SRsP.

(* the tower transport, [HartSFrame.s_rs_agree] with the privilege free *)
Lemma s_rs_p_agree (p : Privilege) (pc npc ms : SailStdpp.Values.mword 64)
    (bmi : bool) (cy ti ip mst0 : SailStdpp.Values.mword 64)
    (pcfg : type_of_register pmpcfg_n)
    (paddr : type_of_register pmpaddr_n)
    (mc : SailStdpp.Values.mword 32)
    (micfg misa0 mseccfg0 senv0 : SailStdpp.Values.mword 64)
    (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
    (satp0 mie0 mdv0 menv0 : SailStdpp.Values.mword 64)
    (tlbv : type_of_register tlb) (rs : regstate) :
    register_lookup (R_bitvector_64 PC) rs = pc ->
    register_lookup (R_bitvector_64 nextPC) rs = npc ->
    register_lookup (R_bitvector_64 minstret) rs = ms ->
    register_lookup (R_bool minstret_increment) rs = bmi ->
    register_lookup (R_bitvector_64 mcycle) rs = cy ->
    register_lookup (R_bitvector_64 mtime) rs = ti ->
    register_lookup (R_bitvector_64 mip) rs = ip ->
    register_lookup tlb rs = tlbv ->
    register_lookup mstatus rs = mst0 ->
    register_lookup hart_state rs = (HART_ACTIVE tt) ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    register_lookup (R_bitvector_32 mcountinhibit) rs = mc ->
    register_lookup (R_bitvector_64 minstretcfg) rs = micfg ->
    register_lookup misa rs = misa0 ->
    register_lookup mseccfg rs = mseccfg0 ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup elp rs = elp0 ->
    register_lookup senvcfg rs = senv0 ->
    register_lookup satp rs = satp0 ->
    register_lookup mie rs = mie0 ->
    register_lookup mideleg rs = mdv0 ->
    register_lookup menvcfg rs = menv0 ->
    register_lookup cur_privilege rs = p ->
    reg_agree_on (s_Drw ∪ s_Dro) rs (s_rs_p p pc npc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv).
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 Hp.
  intros r Hr. rewrite /s_Drw /s_Dro in Hr.
  repeat (apply elem_of_union in Hr as [Hr|Hr]);
    apply elem_of_singleton in Hr; subst r.
  (* peel the privilege cell FIRST: on the [cur_privilege] goal the peel's
     side condition is refutable, so that branch backtracks -- which is
     cheaper than trying an [exact] whose unification would compare two
     [register_lookup]s at different (dependently typed) registers. *)
  all: first
    [ rewrite s_rs_p_peel; [ | vm_compute; reflexivity ]
    | (etransitivity; [ exact Hp | symmetry; apply s_rs_p_priv ]) ].
  all: first
    [ by []
      | by rewrite H1 s_rs_PC
      | by rewrite H2 s_rs_nPC
      | by rewrite H3 s_rs_ms
      | by rewrite H4 s_rs_mi
      | by rewrite H5 s_rs_cy
      | by rewrite H6 s_rs_ti
      | by rewrite H7 s_rs_ip
      | by rewrite H8 s_rs_tlb
      | by rewrite H9 s_rs_mst
      | by rewrite H10 s_rs_hart
      | by rewrite H11 s_rs_pcfg
      | by rewrite H12 s_rs_paddr
      | by rewrite H13 s_rs_mc
      | by rewrite H14 s_rs_micfg
      | by rewrite H15 s_rs_misa
      | by rewrite H16 s_rs_sec
      | by rewrite H17 s_rs_pma
      | by rewrite H18 s_rs_htif
      | by rewrite H19 s_rs_elp
      | by rewrite H20 s_rs_senv
      | by rewrite H21 s_rs_satp
      | by rewrite H22 s_rs_mie
      | by rewrite H23 s_rs_mdl
      | by rewrite H24 s_rs_menv ].
Qed.

Section SRsPFrames.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [SmodeCorePt.spt_frames_close] at [cur_privilege := p] *)
  Lemma spt_frames_close_p (dq : dfrac) (p : Privilege)
      (pc npc ms : SailStdpp.Values.mword 64) (bmi : bool)
      (cy ti ip mst0 : SailStdpp.Values.mword 64)
      (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (mc : SailStdpp.Values.mword 32)
      (micfg misa0 mseccfg0 senv0 : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
      (satp0 mie0 mdv0 menv0 : SailStdpp.Values.mword 64)
      (tlbv : type_of_register tlb) :
    ((R_bitvector_64 PC) ↦ᵣ pc ∗ (R_bitvector_64 nextPC) ↦ᵣ npc ∗
     (R_bitvector_64 minstret) ↦ᵣ ms ∗ (R_bool minstret_increment) ↦ᵣ bmi ∗
     (R_bitvector_64 mcycle) ↦ᵣ cy ∗ (R_bitvector_64 mtime) ↦ᵣ ti ∗
     (R_bitvector_64 mip) ↦ᵣ ip ∗ tlb ↦ᵣ tlbv ∗
     cur_privilege ↦ᵣ{ dq } p ∗ mstatus ↦ᵣ{ dq } mst0 ∗
     hart_state ↦ᵣ{ dq } HART_ACTIVE tt ∗
     pmpcfg_n ↦ᵣ pcfg ∗ pmpaddr_n ↦ᵣ paddr ∗
     reg_pointsto (R_bitvector_32 mcountinhibit) DfracDiscarded mc ∗
     reg_pointsto (R_bitvector_64 minstretcfg) DfracDiscarded micfg ∗
     reg_pointsto misa DfracDiscarded misa0 ∗
     reg_pointsto mseccfg DfracDiscarded mseccfg0 ∗
     reg_pointsto pma_regions DfracDiscarded pmar0 ∗
     reg_pointsto htif_tohost_base DfracDiscarded None ∗
     reg_pointsto elp DfracDiscarded elp0 ∗
     reg_pointsto senvcfg DfracDiscarded senv0 ∗
     satp ↦ᵣ satp0 ∗ mie ↦ᵣ{ dq } mie0 ∗ mideleg ↦ᵣ{ dq } mdv0 ∗
     menvcfg ↦ᵣ{ dq } menv0) -∗
    hreg_frame (s_rs_p p pc npc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv) s_Drw ∗
    hreg_frame_ro (s_Df_mix dq) (s_rs_p p pc npc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv) s_Dro.
  Proof.
    iIntros "(HPC & HnPC & Hms & Hmi & Hcy & Hti & Hip & Htlbc & Hpriv & Hmst
              & Hhs & Hpcfg & Hpaddr & Hmc & Hmicfg & Hmisa & Hsec & Hpma
              & Hhtif & Help & Hsenv & Hsatp & Hmie & Hmdl & Hmenv)".
    rewrite s_rw_split s_ro_split_mix.
    rewrite s_rs_p_PC s_rs_p_nPC s_rs_p_ms s_rs_p_mi s_rs_p_cy s_rs_p_ti
      s_rs_p_ip s_rs_p_tlb s_rs_p_priv s_rs_p_mst s_rs_p_hart s_rs_p_pcfg
      s_rs_p_paddr s_rs_p_mc s_rs_p_micfg s_rs_p_misa s_rs_p_sec s_rs_p_pma
      s_rs_p_htif s_rs_p_elp s_rs_p_senv s_rs_p_satp s_rs_p_mie s_rs_p_mdl
      s_rs_p_menv.
    iFrame.
  Qed.

  (* [SmodeCorePt.spt_frames_elim] at [cur_privilege := p] *)
  Lemma spt_frames_elim_p (dq : dfrac) (p : Privilege)
      (npc ms : SailStdpp.Values.mword 64) (bmi : bool)
      (cy ti ip : SailStdpp.Values.mword 64) (mc : SailStdpp.Values.mword 32)
      (micfg misa0 mseccfg0 senv0 : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
      (mstatus1 satp1 mie1 mdv1 menvcfg1 : SailStdpp.Values.mword 64)
      (pcfg1 : type_of_register pmpcfg_n)
      (paddr1 : type_of_register pmpaddr_n) (tv : type_of_register tlb) :
    resv_any cpu_id -∗
    hreg_frame (s_rs_p p npc npc ms bmi cy ti ip mstatus1 pcfg1 paddr1 mc micfg
                  misa0 mseccfg0 senv0 pmar0 elp0 satp1 mie1 mdv1 menvcfg1 tv)
      s_Drw -∗
    hreg_frame_ro (s_Df_mix dq)
      (s_rs_p p npc npc ms bmi cy ti ip mstatus1 pcfg1 paddr1 mc micfg misa0
         mseccfg0 senv0 pmar0 elp0 satp1 mie1 mdv1 menvcfg1 tv) s_Dro -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt ∗ cur_privilege ↦ᵣ{ dq } p ∗
    mstatus ↦ᵣ{ dq } mstatus1 ∗ mie ↦ᵣ{ dq } mie1 ∗
    mideleg ↦ᵣ{ dq } mdv1 ∗ menvcfg ↦ᵣ{ dq } menvcfg1 ∗
    satp ↦ᵣ satp1 ∗ pmpcfg_n ↦ᵣ pcfg1 ∗ pmpaddr_n ↦ᵣ paddr1 ∗
    tlb ↦ᵣ tv ∗ pc_is npc.
  Proof.
    iIntros "Hresv Hrw Hro".
    rewrite s_rw_split s_ro_split_mix.
    rewrite s_rs_p_PC s_rs_p_nPC s_rs_p_ms s_rs_p_mi s_rs_p_cy s_rs_p_ti
      s_rs_p_ip s_rs_p_tlb s_rs_p_priv s_rs_p_mst s_rs_p_hart s_rs_p_pcfg
      s_rs_p_paddr s_rs_p_mc s_rs_p_micfg s_rs_p_misa s_rs_p_sec s_rs_p_pma
      s_rs_p_htif s_rs_p_elp s_rs_p_senv s_rs_p_satp s_rs_p_mie s_rs_p_mdl
      s_rs_p_menv.
    iDestruct "Hrw" as "(HPC & HnPC & Hms & Hmi & Hcy & Hti & Hip & Htlbc)".
    iDestruct "Hro" as "(Hpriv & Hmst & Hhs & Hpcfg & Hpaddr & #Hmc & #Hmicfg &
                         #Hmisa & #Hsec & #Hpma & #Hhtif & #Help & #Hsenv &
                         Hsatp & Hmie & Hmdl & Hmenv)".
    iFrame "Hhs Hpriv Hmst Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr Htlbc".
    rewrite /pc_is /minstret_res /clock_res.
    iFrame "HPC HnPC Hresv".
    iSplitL "Hms Hmi".
    - iExists ms, bmi, mc, micfg. by iFrame "Hms Hmi Hmc Hmicfg".
    - iExists cy, ti, ip. by iFrame.
  Qed.

End SRsPFrames.

(* [WpSFrames.s_tick_agree] at [cur_privilege := p] *)
Lemma s_tick_agree_p (p : Privilege) (pc npc ms : SailStdpp.Values.mword 64)
    (bmi : bool) (cy ti ip mst0 : SailStdpp.Values.mword 64)
    (pcfg : type_of_register pmpcfg_n)
    (paddr : type_of_register pmpaddr_n) (mc : SailStdpp.Values.mword 32)
    (micfg misa0 mseccfg0 senv0 : SailStdpp.Values.mword 64)
    (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
    (satp0 mie0 mdv0 menv0 : SailStdpp.Values.mword 64)
    (tlbv : type_of_register tlb)
    (mi : SailStdpp.Values.mword 64) (rs : regstate) :
  reg_agree_on ((s_Drw ∪ s_Dro) ∖ tk_clock3) rs
    (wrap_post (s_rs_p p pc npc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tlbv) mi) ->
  reg_agree_on (s_Drw ∪ s_Dro) rs
    (s_rs_p p npc npc mi bmi
       (register_lookup (R_bitvector_64 mcycle) rs)
       (register_lookup (R_bitvector_64 mtime) rs)
       (register_lookup (R_bitvector_64 mip) rs)
       mst0 pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0
       satp0 mie0 mdv0 menv0 tlbv).
Proof.
  intros Hag. apply s_rs_p_agree.
  all: try reflexivity.
  all: (etransitivity;
        [ apply Hag; rewrite /s_Drw /s_Dro /tk_clock3; set_solver | ]).
  all: try (by rewrite wrap_post_PC s_rs_p_nPC).
  all: try (by rewrite wrap_post_ms).
  all: rewrite wrap_post_other;
    [| vm_compute; reflexivity | vm_compute; reflexivity ].
  all: by rewrite ?s_rs_p_PC ?s_rs_p_nPC ?s_rs_p_ms ?s_rs_p_mi ?s_rs_p_cy
            ?s_rs_p_ti ?s_rs_p_ip ?s_rs_p_tlb ?s_rs_p_priv ?s_rs_p_mst
            ?s_rs_p_hart ?s_rs_p_pcfg ?s_rs_p_paddr ?s_rs_p_mc ?s_rs_p_micfg
            ?s_rs_p_misa ?s_rs_p_sec ?s_rs_p_pma ?s_rs_p_htif ?s_rs_p_elp
            ?s_rs_p_senv ?s_rs_p_satp ?s_rs_p_mie ?s_rs_p_mdl ?s_rs_p_menv.
Qed.

Section TrampFetchPt.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Definition tramp_tr_obl (Df : register -> dfrac)
      (pc ms : mword 64) (bmi : bool) (cy ti ip mst0 : mword 64)
      (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (mc : mword 32) (micfg misa0 mseccfg0 senv0 : mword 64)
      (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
      (satp0 mie0 mdv0 menv0 : mword 64)
      (Res : type_of_register tlb -> iProp Σ) : iProp Σ :=
    (□ (∀ (va pax : mword 64) (tv : type_of_register tlb) (rr : option resv),
          ⌜ neq_vec (bits_of_virtaddr (Virtaddr va))
              (sign_extend' 64 (subrange_vec_dec
                 (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ⌝ -∗
          ⌜ svpn_of va = tramp_vpn ⌝ -∗
          ⌜ zero_extend' 64 (concat_vec tramp_ppn
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                 (Z.sub pagesize_bits 1) 0)) = pax ⌝ -∗
          resv_frag cpu_id rr -∗ Res tv -∗
          hreg_frame (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg
             misa0 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv) s_Drw -∗
          hreg_frame_ro Df (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg
             misa0 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv) s_Dro -∗
          swp (translateAddr (Virtaddr va) (InstructionFetch tt))
            (fun r => ⌜r = Values.Ok (Physaddr pax, PBMT_PMA, init_ext_ptw)⌝ ∗
                      ∃ tv' : type_of_register tlb,
                        Res tv' ∗ resv_any cpu_id ∗
                        hreg_frame (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr
                           mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0 mie0
                           mdv0 menv0 tv') s_Drw ∗
                        hreg_frame_ro Df (s_rs pc pc ms bmi cy ti ip mst0 pcfg
                           paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0
                           mie0 mdv0 menv0 tv') s_Dro)))%I.

  Definition tramp_fetch_tr (Df : register -> dfrac)
      (Res : type_of_register tlb -> iProp Σ) (pc : mword 64)
      (mst0 satp0 mie0 mdv0 menv0 : mword 64)
      (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) : iProp Σ :=
    (∀ (ms : mword 64) (bmi : bool) (cy ti ip : mword 64) (mc : mword 32)
       (micfg misa0 mseccfg0 senv0 : mword 64) (pmar0 : list PMA_Region)
       (elp0 : type_of_register elp),
       tramp_tr_obl Df pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
         mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 Res)%I.

  Section TrampDispatch.
    Context (Df : register -> dfrac).
    Context (pc pa ms : SailStdpp.Values.mword 64) (bmi : bool)
            (cy ti ip mst0 : SailStdpp.Values.mword 64)
            (pcfg : type_of_register pmpcfg_n)
            (paddr : type_of_register pmpaddr_n)
            (mc : SailStdpp.Values.mword 32)
            (micfg misa0 mseccfg0 senv0 : SailStdpp.Values.mword 64)
            (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
            (satp0 mie0 mdv0 menv0 : SailStdpp.Values.mword 64).
    Context (Res : type_of_register tlb -> iProp Σ).

    Local Notation srs tv :=
      (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0
         senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv).

    Local Notation Qtow :=
      (fun rsx : regstate => exists tv : type_of_register tlb, rsx = srs tv).
    Local Notation RtowW W :=
      (fun rsx : regstate =>
         (W ∗ Res (register_lookup tlb rsx) ∗ resv_any cpu_id)%I).

    (* [SmodeCorePt]'s three LOCAL helpers, re-proved here (they are
       [Local] there, and each is three lines). *)
    Local Lemma tramp_decode_ok (tv : type_of_register tlb) :
      misa0 = MISA_C -> menv0 = MENVCFG_S ->
      decode_ok (s_Drw ∪ s_Dro) (srs tv).
    Proof.
      intros Hmisa Hmenv. rewrite /decode_ok. split_and!.
      - exact s_in_priv.
      - exact s_in_misa.
      - rewrite s_rs_priv. vm_compute. reflexivity.
      - rewrite s_rs_misa Hmisa. vm_compute. reflexivity.
      - rewrite s_rs_misa Hmisa. vm_compute. reflexivity.
      - rewrite s_rs_misa. exact Hmisa.
      - right. split_and!.
        + exact s_in_menv.
        + srs_lk_g.
        + rewrite s_rs_menv. exact Hmenv.
    Qed.

    Local Lemma tramp_ex_w (Q : regstate -> Prop) (Rr : regstate -> iProp Σ)
        (Qi : InterruptType -> Privilege -> iProp Σ)
        (w : SailStdpp.Values.mword 32) :
      swp (run_hart_active 0)
        (fun st => (∃ ii pr, ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗ Qi ii pr)
                   ∨ (⌜st = Step_Execute (RETIRE_SUCCESS, w)⌝ ∗
                      ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
                      hreg_frame rs2 s_Drw ∗ hreg_frame_ro Df rs2 s_Dro ∗ Rr rs2))
      -∗ swp (run_hart_active 0) (spt_run_post Df Q Rr Qi).
    Proof.
      iIntros "H". iApply (swp_mono with "[] H").
      iIntros (st) "[Hi | (-> & Hr)]".
      - by iLeft.
      - iRight. iExists w. by iFrame.
    Qed.

    Local Lemma tramp_ex_adapt (is_rvc : bool) (i : instruction)
        (Q : regstate -> Prop) (Rr : regstate -> iProp Σ) (W : iProp Σ) :
      spt_ex_obl Df pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
        mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 Res is_rvc i Q Rr W -∗
      (∀ rsf : regstate, ⌜Qtow rsf⌝ -∗ RtowW W rsf -∗
       hreg_frame (register_set (R_bitvector_64 nextPC)
           (add_vec_int pc (if is_rvc then 2 else 4)) rsf) s_Drw -∗
       hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
           (add_vec_int pc (if is_rvc then 2 else 4)) rsf) s_Dro -∗
       swp (execute i)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                   ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
                   hreg_frame rs2 s_Drw ∗ hreg_frame_ro Df rs2 s_Dro ∗ Rr rs2)).
    Proof.
      iIntros "Hex" (rsf) "%HQ (HW & HRes & Hany) Hrw Hro".
      destruct HQ as (tv & ->). rewrite s_rs_tlb.
      iApply ("Hex" $! tv with "HW HRes Hany Hrw Hro").
    Qed.

    (* =================================================================== *)
    (* THE TRAMPOLINE DISPATCH.  [SmodeCorePt.spt_run_hart_active_instr_S]  *)
    (* with the fetch's VA and its BYTES pulled apart: the va is [pc] (a    *)
    (* trampoline va, which the identity map does not cover), the bytes     *)
    (* live at the PHYSICAL [pa] on the trampoline page, and the two are    *)
    (* tied only by the geometry premises + [KptPt.tramp_window_static].    *)
    (* Same four arms; the only per-arm difference is that the byte-window  *)
    (* lemmas ([code_text], [s_chunk_ram], [s_text_obl]) run at [pa] while  *)
    (* the fetch shape lemmas run at [pc], and that the translation         *)
    (* obligation is [tramp_tr_obl] (geometry) rather than [spt_tr_obl]     *)
    (* ([ktier_pin]).                                                       *)
    (* =================================================================== *)
    Lemma tramp_run_hart_active_instr_S (tlbv : type_of_register tlb)
        (is_rvc : bool) (i : instruction) (Q : regstate -> Prop)
        (Rr : regstate -> iProp Σ) (W : iProp Σ)
        (Qi : InterruptType -> Privilege -> iProp Σ) :
      misa0 = MISA_C ->
      menv0 = MENVCFG_S ->
      eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
      pma_allows_ram pmar0 ->
      pmpAddrMatchType_encdec_backwards
        (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
      zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
      eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pcfg 0)) ('b"1") = true ->
      (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
      neq_vec (bits_of_virtaddr (Virtaddr pc))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr pc)) (Z.sub 39 1) 0)) = false ->
      svpn_of pc = tramp_vpn ->
      zero_extend' 64 (concat_vec tramp_ppn
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr pc)) (Z.sub pagesize_bits 1) 0)) = pa ->
      neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int pc 2)))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int pc 2))) (Z.sub 39 1) 0)) = false ->
      svpn_of (add_vec_int pc 2) = tramp_vpn ->
      zero_extend' 64 (concat_vec tramp_ppn
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int pc 2))) (Z.sub pagesize_bits 1) 0)) = add_vec_int pa 2 ->
      is_aligned_vaddr (Virtaddr pc) 2 = true ->
      is_aligned_vaddr (Virtaddr pa) 4 = is_aligned_vaddr (Virtaddr pc) 4 ->
      gen_cert -∗
      instr pa is_rvc i -∗
      W -∗
      resv_frag cpu_id None -∗
      Res tlbv -∗
      hreg_frame (srs tlbv) s_Drw -∗
      hreg_frame_ro Df (srs tlbv) s_Dro -∗
      spt_disp_obl Df pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
        mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 Res tlbv W Qi -∗
      tramp_tr_obl Df pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
        mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 Res -∗
      spt_ex_obl Df pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
        mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 Res is_rvc i Q Rr W -∗
      swp (run_hart_active 0) (spt_run_post Df Q Rr Qi).
    Proof.
      intros Hmisa Hmenv Help Hpallow HA Hord HX Hcov
             Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4.
      pose proof (eq_sym Hpa4va4) as Hpv.
      iIntros "#Hcert Hinstr HW Hfrag0 HRes Hrw Hro Hdisp #Htr Hex".
      iAssert ((W ∗ Res tlbv ∗ resv_frag cpu_id None) -∗
               hreg_frame (srs tlbv) s_Drw -∗
               hreg_frame_ro Df (srs tlbv) s_Dro -∗
               swp (dispatchInterrupt Supervisor)
                 (fun o => match o with
                           | Some (ii, pr) => Qi ii pr
                           | None => (W ∗ Res tlbv ∗ resv_frag cpu_id None) ∗
                                     hreg_frame (srs tlbv) s_Drw ∗
                                     hreg_frame_ro Df (srs tlbv) s_Dro
                           end))%I with "[Hdisp]" as "Hdisp'".
      { iIntros "(HW & HRes & Hfrag) Hrw Hro".
        iApply (swp_mono with "[] [-]");
          [| iApply ("Hdisp" with "HW HRes Hfrag Hrw Hro") ].
        iIntros (o). destruct o as [[ii pr] |].
        - iIntros "H". iExact "H".
        - iIntros "(HW & HRes & Hfrag & Hrw & Hro)". iFrame. }
      iDestruct "Hinstr" as "(%Hlpi & Hib)".
      iDestruct "Hib" as (r) "(%Hrvc & Hbytes & %Hdec)".
      iEval (rewrite /instr_bytes) in "Hbytes".
      iDestruct "Hbytes" as "[%H2al Hbytes]".
      pose proof (fun tv : type_of_register tlb =>
                    hfrun_lpad (s_Drw ∪ s_Dro) s_Drw (srs tv) s_in_elp
                      ltac:(rewrite s_rs_elp; exact Help)) as Hlp.
      destruct r as [e | w | h | erx]; [ done | | | done ];
        cbn [fetch_is_rvc decode_fetch] in Hrvc, Hdec; subst is_rvc.

      - (* ======================= F_Base w ========================== *)
        iDestruct "Hbytes" as "[%HnotRVC #Hb]".
        destruct (is_aligned_vaddr (Virtaddr pa) 4) eqn:Halpa.
        + (* ---- 4-aligned: one 4-byte read ---- *)
          destruct (align4_low_bits pc Hpv) as [Hbit0 Hbit1].
          iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hb") as "#Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iEval (rewrite pa_add_0) in "Hb0".
          iDestruct (code_text with "Hb0") as (ppn) "(#Hk & _ & %Hid)".
          iDestruct (text_canonical with "Hb0") as %Hcan.
          pose proof (ktier_pin_id ppn pa Hid) as Hpaid.
          pose proof (off4_bound pa Halpa) as Hoff.
          rewrite (uint_unsigned_n _) in Hoff.
          iDestruct (s_chunk_ram pa pa 0 4 4 (nth_byte w) ppn
                       ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                       with "Hk Hb") as %[Hram0 Hram3].
          iApply (tramp_ex_w Q Rr Qi _).
          iApply (swp_run_hart_active_gen_exf s_Drw s_Dro Df (srs tlbv)
                    Qtow Q (RtowW W) (W ∗ Res tlbv ∗ resv_frag cpu_id None)%I Supervisor pc w i 8 Rr Qi
                    s_disj s_in_priv s_in_PC s_w_nPC ltac:(srs_lk_g)
                    ltac:(intros rsf (tv & ->); srs_lk_g)
                    ltac:(intros rsf (tv & ->);
                          exact (Hdec _ _ _ (tramp_decode_ok tv Hmisa Hmenv)))
                    ltac:(intros rsf (tv & ->); exact (Hlp tv))
                    with "Hcert Hrw Hro [$HW $HRes $Hfrag0] Hdisp' [] [Hex]").
          2:{ iApply (tramp_ex_adapt false i Q Rr W with "Hex"). }
          iIntros "(HW & HRes & Hany) Hrw Hro".
          iApply (swp_mono with "[] [-]");
            [| iApply (spt_fetch_S_P s_Drw s_Dro Df (srs tlbv) Qtow (RtowW W) pc
                         (pa_of ppn pa) w s_disj s_in_PC s_in_mst s_in_priv
                         ltac:(srs_lk_g) ltac:(intros rsf (tv & ->); srs_lk_g)
                         Hbit0 Hbit1 Hpv
                         with "Hcert Hrw Hro [Hany HRes HW] []") ].
          * iIntros (rr) "(%Hr & Hf)". rewrite HnotRVC in Hr. subst rr.
            by iFrame.
          * iIntros "Hrw Hro". iRename "Hany" into "Hfrag".
            iApply (swp_mono with "[HW] [-]");
              [| iApply ("Htr" $! pc (pa_of ppn pa) tlbv None with
                           "[%] [%] [%] Hfrag HRes Hrw Hro") ].
            2:{ exact Hcanon. }
            2:{ exact Hvpn. }
            2:{ rewrite Hident. exact (eq_sym Hpaid). }
            iIntros (v) "(-> & Hf)". iSplitR; [done|].
            iDestruct "Hf" as (tv') "(HRes & Hany & Hrw & Hro)".
            iExists (srs tv'). iSplitR; [iPureIntro; by exists tv' |].
            rewrite s_rs_tlb. iFrame.
          * iIntros (rsf) "%HQ Hrw Hro". destruct HQ as (tv & ->).
            iApply (swp_checked_mem_read_ifetch4_S s_Drw s_Dro Df (srs tv)
                      (pa_of ppn pa) pmar0 pcfg paddr w s_disj s_in_pma
                      s_in_pcfg s_in_paddr s_in_htif ltac:(srs_lk_g)
                      ltac:(srs_lk_g) ltac:(srs_lk_g) ltac:(srs_lk_g)
                      HA Hord HX Hcov Hpallow Hram0 Hram3
                      (pa4_aligned ppn pa Halpa) with "Hcert Hrw Hro []").
            iApply (s_text_obl pa pa 0%nat 4%nat 4%N (nth_byte w) ppn w
                      ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                      (fun j _ => eq_refl) with "Hk Hb").

        + (* ---- 2 mod 4: two halfword reads, two translations ---- *)
          destruct (align2_not4_facts pc Hva2 Hpv) as (_ & Hbit0 & Hbit1).
          assert (Hvah2 : is_aligned_vaddr (Virtaddr (add_vec_int pa 2)) 2 = true).
          { pose proof (align2_plus2 pa H2al) as Hh. rewrite fetch_pa_id in Hh.
            exact Hh. }
          assert (HbaseH : forall k : nat,
                    pa_add pa (2 + k)%nat = pa_add (add_vec_int pa 2) k).
          { intros k. unfold pa_add. rewrite avi_assoc. f_equal. lia. }
          iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hb") as "#Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iEval (rewrite pa_add_0) in "Hb0".
          iDestruct (code_text with "Hb0") as (ppnl) "(#Hkl & _ & %Hidl)".
          iDestruct (text_canonical with "Hb0") as %Hcanl.
          pose proof (ktier_pin_id ppnl pa Hidl) as Hpaidl.
          pose proof (off_bound_div pa 2 ltac:(lia) ltac:(exists 2048; lia) H2al)
            as Hoffl. rewrite (uint_unsigned_n _) in Hoffl.
          iDestruct (big_sepL_lookup _ _ 2%nat 2%nat with "Hb") as "#Hb2".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (code_text with "Hb2") as (ppnh) "(#Hkh & _ & %Hidh)".
          iDestruct (text_canonical with "Hb2") as %Hcanh.
          pose proof (ktier_pin_id ppnh (add_vec_int pa 2) Hidh) as Hpaidh.
          pose proof (off_bound_div (add_vec_int pa 2) 2 ltac:(lia)
                        ltac:(exists 2048; lia) Hvah2) as Hoffh.
          rewrite (uint_unsigned_n _) in Hoffh.
          iDestruct (s_chunk_ram pa pa 0 2 4 (nth_byte w) ppnl
                       ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoffl Hcanl
                       with "Hkl Hb") as %[Hraml0 Hraml1].
          iDestruct (s_chunk_ram pa (add_vec_int pa 2) 2 2 4 (nth_byte w) ppnh
                       ltac:(lia) ltac:(lia) HbaseH Hoffh Hcanh
                       with "Hkh Hb") as %[Hramh0 Hramh1].
          iApply (tramp_ex_w Q Rr Qi _).
          iApply (swp_run_hart_active_gen_exf s_Drw s_Dro Df (srs tlbv)
                    Qtow Q (RtowW W) (W ∗ Res tlbv ∗ resv_frag cpu_id None)%I Supervisor pc
                    (concat_vec (subrange_vec_dec w 31 16)
                       (subrange_vec_dec w 15 0)) i 8 Rr Qi
                    s_disj s_in_priv s_in_PC s_w_nPC ltac:(srs_lk_g)
                    ltac:(intros rsf (tv & ->); srs_lk_g)
                    ltac:(intros rsf (tv & ->);
                          rewrite concat_subranges_id;
                          exact (Hdec _ _ _ (tramp_decode_ok tv Hmisa Hmenv)))
                    ltac:(intros rsf (tv & ->); exact (Hlp tv))
                    with "Hcert Hrw Hro [$HW $HRes $Hfrag0] Hdisp' [] [Hex]").
          2:{ iApply (tramp_ex_adapt false i Q Rr W with "Hex"). }
          iIntros "(HW & HRes & Hany) Hrw Hro".
          iApply (spt_fetch_S_base2_P s_Drw s_Dro Df (srs tlbv) Qtow Qtow
                    (RtowW W) (RtowW W) pc (pa_of ppnl pa)
                    (pa_of ppnh (add_vec_int pa 2))
                    (subrange_vec_dec w 15 0) (subrange_vec_dec w 31 16)
                    s_disj s_in_PC s_in_misa s_in_mst s_in_priv
                    ltac:(srs_lk_g) ltac:(intros rs1 (tv & ->); srs_lk_g)
                    ltac:(intros rs1 (tv & ->); srs_lk_g)
                    ltac:(intros rs2 (tv & ->); srs_lk_g)
                    ltac:(rewrite s_rs_misa Hmisa; vm_compute; reflexivity)
                    Hbit0 Hbit1 Hpv
                    HnotRVC
                    with "Hcert Hrw Hro [Hany HRes HW] [] [] []").
          * iIntros "Hrw Hro". iRename "Hany" into "Hfrag".
            iApply (swp_mono with "[HW] [-]");
              [| iApply ("Htr" $! pc (pa_of ppnl pa) tlbv None with
                           "[%] [%] [%] Hfrag HRes Hrw Hro") ].
            2:{ exact Hcanon. }
            2:{ exact Hvpn. }
            2:{ rewrite Hident. exact (eq_sym Hpaidl). }
            iIntros (v) "(-> & Hf)". iSplitR; [done|].
            iDestruct "Hf" as (tv') "(HRes & Hany & Hrw & Hro)".
            iExists (srs tv'). iSplitR; [iPureIntro; by exists tv' |].
            rewrite s_rs_tlb. iFrame.
          * iIntros (rs1) "%HQ Hrw Hro". destruct HQ as (tv & ->).
            iApply (swp_checked_mem_read_ifetch2_S s_Drw s_Dro Df (srs tv)
                      (pa_of ppnl pa) pmar0 pcfg paddr
                      (subrange_vec_dec w 15 0) s_disj s_in_pma
                      s_in_pcfg s_in_paddr s_in_htif ltac:(srs_lk_g)
                      ltac:(srs_lk_g) ltac:(srs_lk_g) ltac:(srs_lk_g)
                      HA Hord HX Hcov Hpallow Hraml0 Hraml1
                      (pa_aligned_div ppnl pa 2 ltac:(lia)
                         ltac:(exists 2048; lia) H2al)
                      with "Hcert Hrw Hro []").
            iApply (s_text_obl pa pa 0%nat 4%nat 2%N (nth_byte w) ppnl
                      (subrange_vec_dec w 15 0)
                      ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoffl Hcanl
                      ltac:(intros j Hj;
                            exact (eq_sym (nth_byte_subrange_lo w j Hj)))
                      with "Hkl Hb").
          * iIntros (rs1) "%HQ (HW & HRes & Hany) Hrw Hro".
            destruct HQ as (tv & ->). rewrite s_rs_tlb.
            iDestruct "Hany" as (rr) "Hfrag".
            iApply (swp_mono with "[HW] [-]");
              [| iApply ("Htr" $! (add_vec_int pc 2)
                           (pa_of ppnh (add_vec_int pa 2)) tv rr with
                           "[%] [%] [%] Hfrag HRes Hrw Hro") ].
            2:{ exact Hcanon2. }
            2:{ exact Hvpn2. }
            2:{ rewrite Hident2. exact (eq_sym Hpaidh). }
            iIntros (v) "(-> & Hf)". iSplitR; [done|].
            iDestruct "Hf" as (tv') "(HRes & Hany & Hrw & Hro)".
            iExists (srs tv'). iSplitR; [iPureIntro; by exists tv' |].
            rewrite s_rs_tlb. iFrame.
          * iIntros (rs2) "%HQ Hrw Hro". destruct HQ as (tv & ->).
            iApply (swp_checked_mem_read_ifetch2_S s_Drw s_Dro Df (srs tv)
                      (pa_of ppnh (add_vec_int pa 2)) pmar0 pcfg paddr
                      (subrange_vec_dec w 31 16) s_disj s_in_pma
                      s_in_pcfg s_in_paddr s_in_htif ltac:(srs_lk_g)
                      ltac:(srs_lk_g) ltac:(srs_lk_g) ltac:(srs_lk_g)
                      HA Hord HX Hcov Hpallow Hramh0 Hramh1
                      (pa_aligned_div ppnh (add_vec_int pa 2) 2 ltac:(lia)
                         ltac:(exists 2048; lia) Hvah2)
                      with "Hcert Hrw Hro []").
            iApply (s_text_obl pa (add_vec_int pa 2) 2%nat 4%nat 2%N
                      (nth_byte w) ppnh (subrange_vec_dec w 31 16)
                      ltac:(lia) ltac:(lia) HbaseH Hoffh Hcanh
                      ltac:(intros j Hj;
                            exact (eq_sym (nth_byte_subrange_hi w j Hj)))
                      with "Hkh Hb").

      - (* ======================= F_RVC h =========================== *)
        iDestruct "Hbytes" as "[%HisRVC Hbytes]".
        destruct Hdec as (i0 & Hlp0 & Hdec2).
        destruct (is_aligned_vaddr (Virtaddr pa) 4) eqn:Halpa.
        + (* ---- 4-aligned: the halfword sits in a 4-byte word ---- *)
          iDestruct "Hbytes" as (w) "[%Hsub #Hb]".
          destruct (align4_low_bits pc Hpv) as [Hbit0 Hbit1].
          iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hb") as "#Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iEval (rewrite pa_add_0) in "Hb0".
          iDestruct (code_text with "Hb0") as (ppn) "(#Hk & _ & %Hid)".
          iDestruct (text_canonical with "Hb0") as %Hcan.
          pose proof (ktier_pin_id ppn pa Hid) as Hpaid.
          pose proof (off4_bound pa Halpa) as Hoff.
          rewrite (uint_unsigned_n _) in Hoff.
          iDestruct (s_chunk_ram pa pa 0 4 4 (nth_byte w) ppn
                       ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                       with "Hk Hb") as %[Hram0 Hram3].
          iApply (tramp_ex_w Q Rr Qi _).
          iApply (swp_run_hart_active_gen_rvc_exf s_Drw s_Dro Df (srs tlbv)
                    Qtow Q (RtowW W) (W ∗ Res tlbv ∗ resv_frag cpu_id None)%I Supervisor pc h i0 i 8 Rr Qi
                    s_disj s_in_priv s_in_misa s_in_PC s_w_nPC ltac:(srs_lk_g)
                    ltac:(intros rsf (tv & ->); srs_lk_g)
                    ltac:(intros rsf (tv & ->); rewrite s_rs_misa Hmisa;
                          vm_compute; reflexivity)
                    ltac:(intros rsf (tv & ->);
                          exact (proj1 (Hdec2 _ _ _
                                   (tramp_decode_ok tv Hmisa Hmenv))))
                    ltac:(intros rsf (tv & ->); exact (Hlp tv))
                    with "Hcert Hrw Hro [$HW $HRes $Hfrag0] Hdisp' [] [] [Hex]").
          2:{ iIntros (rsf) "%HQ Hrw Hro". destruct HQ as (tv & ->).
              iApply (swp_span s_Drw s_Dro Df _ _ _ _ s_disj
                        (proj2 (Hdec2 _ _ _ (decode_ok_set_nPC _ _ _
                                  (tramp_decode_ok tv Hmisa Hmenv))))
                        with "Hcert Hrw Hro"). }
          2:{ iApply (tramp_ex_adapt true i Q Rr W with "Hex"). }
          iIntros "(HW & HRes & Hany) Hrw Hro".
          iApply (swp_mono with "[] [-]");
            [| iApply (spt_fetch_S_P s_Drw s_Dro Df (srs tlbv) Qtow (RtowW W) pc
                         (pa_of ppn pa) w s_disj s_in_PC s_in_mst s_in_priv
                         ltac:(srs_lk_g) ltac:(intros rsf (tv & ->); srs_lk_g)
                         Hbit0 Hbit1 Hpv
                         with "Hcert Hrw Hro [Hany HRes HW] []") ].
          * iIntros (rr) "(%Hr & Hf)". rewrite Hsub HisRVC in Hr. subst rr.
            by iFrame.
          * iIntros "Hrw Hro". iRename "Hany" into "Hfrag".
            iApply (swp_mono with "[HW] [-]");
              [| iApply ("Htr" $! pc (pa_of ppn pa) tlbv None with
                           "[%] [%] [%] Hfrag HRes Hrw Hro") ].
            2:{ exact Hcanon. }
            2:{ exact Hvpn. }
            2:{ rewrite Hident. exact (eq_sym Hpaid). }
            iIntros (v) "(-> & Hf)". iSplitR; [done|].
            iDestruct "Hf" as (tv') "(HRes & Hany & Hrw & Hro)".
            iExists (srs tv'). iSplitR; [iPureIntro; by exists tv' |].
            rewrite s_rs_tlb. iFrame.
          * iIntros (rsf) "%HQ Hrw Hro". destruct HQ as (tv & ->).
            iApply (swp_checked_mem_read_ifetch4_S s_Drw s_Dro Df (srs tv)
                      (pa_of ppn pa) pmar0 pcfg paddr w s_disj s_in_pma
                      s_in_pcfg s_in_paddr s_in_htif ltac:(srs_lk_g)
                      ltac:(srs_lk_g) ltac:(srs_lk_g) ltac:(srs_lk_g)
                      HA Hord HX Hcov Hpallow Hram0 Hram3
                      (pa4_aligned ppn pa Halpa) with "Hcert Hrw Hro []").
            iApply (s_text_obl pa pa 0%nat 4%nat 4%N (nth_byte w) ppn w
                      ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                      (fun j _ => eq_refl) with "Hk Hb").

        + (* ---- 2 mod 4: a bare halfword read ---- *)
          iDestruct "Hbytes" as "#Hb".
          destruct (align2_not4_facts pc Hva2 Hpv) as (_ & Hbit0 & Hbit1).
          iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hb") as "#Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iEval (rewrite pa_add_0) in "Hb0".
          iDestruct (code_text with "Hb0") as (ppn) "(#Hk & _ & %Hid)".
          iDestruct (text_canonical with "Hb0") as %Hcan.
          pose proof (ktier_pin_id ppn pa Hid) as Hpaid.
          pose proof (off_bound_div pa 2 ltac:(lia) ltac:(exists 2048; lia) H2al)
            as Hoff. rewrite (uint_unsigned_n _) in Hoff.
          iDestruct (s_chunk_ram pa pa 0 2 2 (nth_byte h) ppn
                       ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                       with "Hk Hb") as %[Hram0 Hram1].
          iApply (tramp_ex_w Q Rr Qi _).
          iApply (swp_run_hart_active_gen_rvc_exf s_Drw s_Dro Df (srs tlbv)
                    Qtow Q (RtowW W) (W ∗ Res tlbv ∗ resv_frag cpu_id None)%I Supervisor pc h i0 i 8 Rr Qi
                    s_disj s_in_priv s_in_misa s_in_PC s_w_nPC ltac:(srs_lk_g)
                    ltac:(intros rsf (tv & ->); srs_lk_g)
                    ltac:(intros rsf (tv & ->); rewrite s_rs_misa Hmisa;
                          vm_compute; reflexivity)
                    ltac:(intros rsf (tv & ->);
                          exact (proj1 (Hdec2 _ _ _
                                   (tramp_decode_ok tv Hmisa Hmenv))))
                    ltac:(intros rsf (tv & ->); exact (Hlp tv))
                    with "Hcert Hrw Hro [$HW $HRes $Hfrag0] Hdisp' [] [] [Hex]").
          2:{ iIntros (rsf) "%HQ Hrw Hro". destruct HQ as (tv & ->).
              iApply (swp_span s_Drw s_Dro Df _ _ _ _ s_disj
                        (proj2 (Hdec2 _ _ _ (decode_ok_set_nPC _ _ _
                                  (tramp_decode_ok tv Hmisa Hmenv))))
                        with "Hcert Hrw Hro"). }
          2:{ iApply (tramp_ex_adapt true i Q Rr W with "Hex"). }
          iIntros "(HW & HRes & Hany) Hrw Hro".
          iApply (spt_fetch_S_rvc2_P s_Drw s_Dro Df (srs tlbv) Qtow (RtowW W) pc
                    (pa_of ppn pa) h s_disj s_in_PC s_in_misa s_in_mst
                    s_in_priv ltac:(srs_lk_g)
                    ltac:(intros rsf (tv & ->); srs_lk_g)
                    ltac:(rewrite s_rs_misa Hmisa; vm_compute; reflexivity)
                    Hbit0 Hbit1 Hpv HisRVC
                    with "Hcert Hrw Hro [Hany HRes HW] []").
          * iIntros "Hrw Hro". iRename "Hany" into "Hfrag".
            iApply (swp_mono with "[HW] [-]");
              [| iApply ("Htr" $! pc (pa_of ppn pa) tlbv None with
                           "[%] [%] [%] Hfrag HRes Hrw Hro") ].
            2:{ exact Hcanon. }
            2:{ exact Hvpn. }
            2:{ rewrite Hident. exact (eq_sym Hpaid). }
            iIntros (v) "(-> & Hf)". iSplitR; [done|].
            iDestruct "Hf" as (tv') "(HRes & Hany & Hrw & Hro)".
            iExists (srs tv'). iSplitR; [iPureIntro; by exists tv' |].
            rewrite s_rs_tlb. iFrame.
          * iIntros (rsf) "%HQ Hrw Hro". destruct HQ as (tv & ->).
            iApply (swp_checked_mem_read_ifetch2_S s_Drw s_Dro Df (srs tv)
                      (pa_of ppn pa) pmar0 pcfg paddr h s_disj s_in_pma
                      s_in_pcfg s_in_paddr s_in_htif ltac:(srs_lk_g)
                      ltac:(srs_lk_g) ltac:(srs_lk_g) ltac:(srs_lk_g)
                      HA Hord HX Hcov Hpallow Hram0 Hram1
                      (pa_aligned_div ppn pa 2 ltac:(lia)
                         ltac:(exists 2048; lia) H2al)
                      with "Hcert Hrw Hro []").
            iApply (s_text_obl pa pa 0%nat 2%nat 2%N (nth_byte h) ppn h
                      ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                      (fun j _ => eq_refl) with "Hk Hb").
    Qed.

  End TrampDispatch.

  (* ==================================================================== *)
  (* THE TRAMPOLINE STEP ENGINE, per node.                                 *)
  (*                                                                      *)
  (* [SmodeCorePt.wp_instr_s_config_regime] with the fetch's VA and its    *)
  (* BYTES pulled apart -- the va is the trampoline [pc], the bytes are at *)
  (* the physical [pa] -- and with the regime's [spt_fetch_tr] replaced by *)
  (* [tramp_fetch_tr], the per-node heir of the deleted whole-cycle        *)
  (* [Habs].  Everything else (the cells in, [swp (execute i)] with them   *)
  (* back, the existential landing tlb / clock / mstatus / mideleg, the    *)
  (* rider keyed on the landing pc) is the S wrapper's shape verbatim.     *)
  (*                                                                      *)
  (* THE RUNNING SIDE IS ALWAYS SUPERVISOR -- the trampoline is reached    *)
  (* by a trap, which raises privilege before the pc gets there.  Only the *)
  (* LANDING file is privilege-parametric, and only because one            *)
  (* trampoline instruction leaves S-mode: userret's [sret] to user.       *)
  (* Every wrapper below states its own [priv1] CONCRETELY.                *)
  (* ==================================================================== *)
  Lemma wp_instr_tramp_pt
      (Res : type_of_register tlb -> iProp Σ)
      (pc pa : mword 64) (is_rvc : bool) (i : instruction)
      (mstatus0 mie_v mdv0 menvcfg0 satp0 : mword 64)
      (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (tlbv : type_of_register tlb)
      (mie1 menvcfg1 satp1 : mword 64)
      (pcfg1 : type_of_register pmpcfg_n)
      (paddr1 : type_of_register pmpaddr_n) (priv1 : Privilege)
      (Rl : mword 64 -> mword 64 -> mword 64 -> iProp Σ) {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    pmp_ent0_ok pcfg paddr ->
    neq_vec (bits_of_virtaddr (Virtaddr pc))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr pc)) (Z.sub 39 1) 0)) = false ->
    svpn_of pc = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr pc)) (Z.sub pagesize_bits 1) 0)) = pa ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int pc 2)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int pc 2))) (Z.sub 39 1) 0)) = false ->
    svpn_of (add_vec_int pc 2) = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int pc 2))) (Z.sub pagesize_bits 1) 0)) = add_vec_int pa 2 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pa) 4 = is_aligned_vaddr (Virtaddr pc) 4 ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    satp ↦ᵣ satp0 -∗ pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
    tlb ↦ᵣ tlbv -∗ Res tlbv -∗
    pc_is pc -∗
    instr pa is_rvc i -∗
    tramp_fetch_tr (s_Df_mix dq) Res pc mstatus0 satp0 mie_v mdv0 menvcfg0
      pcfg paddr -∗
    (∀ tv' : type_of_register tlb,
       ⌜ pmp_ent0_ok pcfg paddr ⌝ -∗
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       satp ↦ᵣ satp0 -∗ pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
       tlb ↦ᵣ tv' -∗ Res tv' -∗
       clock_res -∗
       (R_bitvector_64 PC) ↦ᵣ pc -∗
       (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc (if is_rvc then 2 else 4)) -∗
       resv_any cpu_id -∗
       swp (execute i)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                   cur_privilege ↦ᵣ{ dq } priv1 ∗
                   mie ↦ᵣ{ dq } mie1 ∗
                   menvcfg ↦ᵣ{ dq } menvcfg1 ∗
                   satp ↦ᵣ satp1 ∗ pmpcfg_n ↦ᵣ pcfg1 ∗
                   pmpaddr_n ↦ᵣ paddr1 ∗
                   (∃ tv2 : type_of_register tlb, tlb ↦ᵣ tv2 ∗ Res tv2) ∗
                   clock_res ∗
                   (∃ ms1 mdv1 npc : mword 64,
                      mstatus ↦ᵣ{ dq } ms1 ∗ mideleg ↦ᵣ{ dq } mdv1 ∗
                      (R_bitvector_64 PC) ↦ᵣ pc ∗
                      (R_bitvector_64 nextPC) ↦ᵣ npc ∗ Rl npc ms1 mdv1) ∗
                   resv_any cpu_id)) -∗
    ▷ (∀ (npc ms1 mdv1 : mword 64) (tv1 : type_of_register tlb),
         hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
         cur_privilege ↦ᵣ{ dq } priv1 -∗
         mstatus ↦ᵣ{ dq } ms1 -∗
         mie ↦ᵣ{ dq } mie1 -∗
         mideleg ↦ᵣ{ dq } mdv1 -∗
         menvcfg ↦ᵣ{ dq } menvcfg1 -∗
         satp ↦ᵣ satp1 -∗ pmpcfg_n ↦ᵣ pcfg1 -∗ pmpaddr_n ↦ᵣ paddr1 -∗
         tlb ↦ᵣ tv1 -∗ Res tv1 -∗
         pc_is npc -∗ Rl npc ms1 mdv1 -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HSIE HMPRV HSXL Hmm HPBMTE Hmenvval Hpmp
           Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4.
    pose proof Hpmp as (HA & Hord & HX & HW & HR & Hcov).
    iIntros "#Hhw #Hminv Hhs Hpriv Hmst Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr
             Htlbc HRes Hpc Hinstr Htr Hex Hcont".
    iDestruct (spt_frames_intro dq pc mstatus0 mie_v mdv0 menvcfg0 satp0 pcfg
                 paddr tlbv
                 with "Hhw Hhs Hpriv Hmst Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr
                       Htlbc Hpc") as "[Hfrag Hfr]".
    iDestruct "Hfr" as (ms bmi cy ti ip mc micfg misa0 mseccfg0 senv0 pmar0 elp0)
      "(%Hmisaval & %Hpmaall & %Helpnp & Hrw & Hro)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iPoseProof ("Htr" $! ms (minstret_inc_flag mc micfg Supervisor) cy ti ip mc
                  micfg misa0 mseccfg0 senv0 pmar0 elp0) as "#Htr0".
    iApply (spt_cycle (s_Df_mix dq) pc
              (fun rs2 => (Res (register_lookup tlb rs2) ∗ resv_any cpu_id
                           ∗ Rl (register_lookup (R_bitvector_64 nextPC) rs2)
                                (register_lookup mstatus rs2)
                                (register_lookup mideleg rs2))%I)
              (fun rs2 => exists (npc ms1 mdv1 cy1 ti1 ip1 : mword 64)
                            (tv : type_of_register tlb),
                 rs2 = s_rs_p priv1 pc npc ms (minstret_inc_flag mc micfg Supervisor) cy1 ti1 ip1 ms1 pcfg1 paddr1 mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp1 mie1 mdv1 menvcfg1 tv)
              ms bmi cy ti ip mstatus0 mc micfg misa0 mseccfg0 senv0 pmar0 elp0
              satp0 mie_v mdv0 menvcfg0 pcfg paddr tlbv
              ltac:(intros rs2 (npc & ms1 & mdv1 & cy1 & ti1 & ip1 & tv & ->);
                    apply s_rs_p_hart)
              ltac:(intros rs2 (npc & ms1 & mdv1 & cy1 & ti1 & ip1 & tv & ->);
                    apply s_rs_p_mi)
              with "Hcert Hfrag Hrw Hro [Hex HRes Hinstr] [Hcont]").
    2:{ (* ---- the continuation ---- *)
        iNext. iIntros (rs3 rs2 mi) "[%HQ %Hag] Hrw Hro (HRes & Hfrag & HRl)".
        destruct HQ as (npc & ms1 & mdv1 & cy1 & ti1 & ip1 & tv & ->).
        iEval (rewrite s_rs_p_tlb) in "HRes".
        iEval (rewrite s_rs_p_nPC s_rs_p_mst s_rs_p_mdl) in "HRl".
        pose proof (s_tick_agree_p priv1 pc npc ms
                      (minstret_inc_flag mc micfg Supervisor) cy1 ti1 ip1 ms1
                      pcfg1 paddr1 mc micfg misa0 mseccfg0 senv0 pmar0 elp0
                      satp1 mie1 mdv1 menvcfg1 tv mi rs3 Hag) as Hag'.
        iDestruct (s_rw_ext _ _ Hag' with "Hrw") as "Hrw".
        iDestruct (s_ro_ext_gen (s_Df_mix dq) _ _ Hag' with "Hro") as "Hro".
        iDestruct (spt_frames_elim_p dq priv1 npc mi
                     (minstret_inc_flag mc micfg Supervisor) _ _ _ mc micfg
                     misa0 mseccfg0 senv0 pmar0 elp0 ms1 satp1 mie1 mdv1
                     menvcfg1 pcfg1 paddr1 tv with "Hfrag Hrw Hro")
          as "(Hhs & Hpriv & Hmst & Hmie & Hmdl & Hmenv & Hsatp & Hpcfg &
               Hpaddr & Htlbc & Hpc)".
        iApply ("Hcont" $! npc ms1 mdv1 tv with "Hhs Hpriv Hmst Hmie Hmdl Hmenv
                  Hsatp Hpcfg Hpaddr Htlbc HRes Hpc HRl"). }
    (* ---- the body ---- *)
    iIntros "Hfrag Hrw Hro".
    iApply (swp_mono with "[] [-]");
      [| iApply (tramp_run_hart_active_instr_S (s_Df_mix dq) pc pa ms
                   (minstret_inc_flag mc micfg Supervisor) cy ti ip mstatus0
                   pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0
                   mie_v mdv0 menvcfg0 Res tlbv is_rvc i
                   (fun rs2 => exists (npc ms1 mdv1 cy1 ti1 ip1 : mword 64)
                                 (tv : type_of_register tlb),
                      rs2 = s_rs_p priv1 pc npc ms (minstret_inc_flag mc micfg Supervisor) cy1 ti1 ip1 ms1 pcfg1 paddr1 mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp1 mie1 mdv1 menvcfg1 tv)
                   (fun rs2 => (Res (register_lookup tlb rs2)
                                ∗ resv_any cpu_id
                                ∗ Rl (register_lookup (R_bitvector_64 nextPC) rs2)
                                     (register_lookup mstatus rs2)
                                     (register_lookup mideleg rs2))%I)
                   emp%I (fun _ _ => False%I)
                   Hmisaval Hmenvval Helpnp (pma_all_ram Hpmaall)
                   HA Hord HX Hcov
                   Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4
                   with "Hcert Hinstr [] Hfrag HRes Hrw Hro [] Htr0
                         [Hex]") ].
    - iIntros (st) "[Hi | Hr]".
      + iDestruct "Hi" as (ii pr) "(_ & Hf)". iDestruct "Hf" as %[].
      + iDestruct "Hr" as (w) "(-> & Hr)".
        iDestruct "Hr" as (rs2) "(%HQ & Hrw & Hro & HPsi)".
        iExists rs2. iSplitR; [done|]. iFrame.
    - done.
    - iApply (spt_dispatch_none (s_Df_mix dq) pc ms
                (minstret_inc_flag mc micfg Supervisor) cy ti ip mstatus0 pcfg
                paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0 mie_v mdv0
                menvcfg0 Res tlbv emp%I (fun _ _ => False%I) Hmisaval HSIE Hmm
                with "Hcert").
    - (* THE LEAF, at the file the fetch landed on *)
      iIntros (tv') "_ HRes' Hany Hrw Hro".
      pose proof (s_npc_agree pc pc
                    (add_vec_int pc (if is_rvc then 2 else 4)) ms
                    (minstret_inc_flag mc micfg Supervisor) cy ti ip mstatus0
                    pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0
                    mie_v mdv0 menvcfg0 tv') as Hnp.
      iDestruct (s_rw_ext _ _ Hnp with "Hrw") as "Hrw".
      iDestruct (s_ro_ext_gen (s_Df_mix dq) _ _ Hnp with "Hro") as "Hro".
      iDestruct (spt_frames_open dq pc
                   (add_vec_int pc (if is_rvc then 2 else 4)) ms
                   (minstret_inc_flag mc micfg Supervisor) cy ti ip mstatus0
                   pcfg paddr mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0
                   mie_v mdv0 menvcfg0 tv' with "Hrw Hro")
        as "(HPC & HnPC & Hms & Hmi & Hcy & Hti & Hip & Htlbc & Hpriv & Hmst
             & Hhs & Hpcfg & Hpaddr & #Hmc & #Hmicfg & #Hmisa & #Hsec & #Hpma
             & #Hhtif & #Help & #Hsenv & Hsatp & Hmie & Hmdl & Hmenv)".
      iSpecialize ("Hex" $! tv' with "[%]"); [ exact Hpmp | ].
      iAssert clock_res with "[Hcy Hti Hip]" as "Hclk".
      { iExists cy, ti, ip. iFrame "Hcy Hti Hip". }
      iApply (swp_mono with "[Hms Hmi Hhs] [-]");
        [| iApply ("Hex" with "Hpriv Hmst Hmie Hmdl Hmenv Hsatp Hpcfg
                     Hpaddr Htlbc HRes' Hclk HPC HnPC Hany") ].
      iIntros (e) "(-> & Hpriv & Hmie & Hmenv & Hsatp & Hpcfg &
                    Hpaddr & Htlbr & Hclk & Hcfg & Hany)".
      iDestruct "Htlbr" as (tv2) "(Htlbc & HRes')".
      iDestruct "Hclk" as (cy1 ti1 ip1) "(Hcy & Hti & Hip)".
      iDestruct "Hcfg" as (ms1 mdv1 npc) "(Hmst & Hmdl & HPC & HnPC & HRl)".
      iSplitR; [done|].
      iExists (s_rs_p priv1 pc npc ms (minstret_inc_flag mc micfg Supervisor) cy1 ti1 ip1 ms1 pcfg1 paddr1 mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp1 mie1 mdv1 menvcfg1 tv2).
      iSplitR;
        [ iPureIntro; by exists npc, ms1, mdv1, cy1, ti1, ip1, tv2 |].
      iDestruct (spt_frames_close_p dq priv1 pc npc ms
                   (minstret_inc_flag mc micfg Supervisor) cy1 ti1 ip1 ms1
                   pcfg1 paddr1 mc micfg misa0 mseccfg0 senv0 pmar0 elp0 satp1
                   mie1 mdv1 menvcfg1 tv2
                   with "[HPC HnPC Hms Hmi Hcy Hti Hip Htlbc Hpriv Hmst Hhs
                          Hpcfg Hpaddr Hsatp Hmie Hmdl Hmenv]")
        as "[Hrw Hro]".
      { iFrame "HPC HnPC Hms Hmi Hcy Hti Hip Htlbc Hpriv Hmst Hhs Hpcfg
                Hpaddr Hsatp Hmie Hmdl Hmenv".
        by iFrame "Hmc Hmicfg Hmisa Hsec Hpma Hhtif Help Hsenv". }
      rewrite s_rs_p_tlb s_rs_p_nPC s_rs_p_mst s_rs_p_mdl.
      iFrame "Hrw Hro HRes' Hany HRl".
  Qed.

  (* ==================================================================== *)
  (* THE TRAMPOLINE FETCH-TRANSLATION PRODUCER.                            *)
  (*                                                                      *)
  (* [SmodeCorePt.spt_tr_obl_of_regime] on the WITNESSED route.  The       *)
  (* trampoline va's claim is [kmap_at tramp_vpn tramp_ppn KP_rx], whose   *)
  (* ppn is NOT [svpn_of va] -- so there is no [ktier_pin] to feed         *)
  (* [sr_adm], and admissibility is dropped in favour of the regime's      *)
  (* all-claims witness [sr_kwit] exactly as [sr_swp_translate_wit] is     *)
  (* designed to be used ([kpt_share_regime]'s witness is [emp]; Bare's is *)
  (* [False], which is what keeps the route sound).                        *)
  (* ==================================================================== *)
  Local Ltac tlbpeel :=
    rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

  Lemma tramp_tr_obl_of_regime
      (R : s_regime)
      (Df : register -> dfrac) (Db : register -> bool)
      (pc ms : mword 64) (bmi : bool) (cy ti ip mst0 : mword 64)
      (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (mc : mword 32) (micfg misa0 mseccfg0 senv0 : mword 64)
      (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
      (satp0 mie0 mdv0 menv0 : mword 64) :
    misa0 = MISA_C ->
    menv0 = MENVCFG_S ->
    _get_Mstatus_SXL mst0 = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV mst0) ('b"1") = false ->
    (forall r : register, Db r = true -> r ∈ s_Drw ∪ s_Dro) ->
    (forall r : register, D_leafchk r = true -> r ∈ s_Drw ∪ s_Dro) ->
    Db mstatus = true -> Db satp = true ->
    sr_swp_satp_ok R satp0 ->
    pmp_ent0_ok pcfg paddr ->
    pma_allows_ram pmar0 ->
    sr_ktier_wit R KT1 -∗
    kmap_at tramp_vpn tramp_ppn KP_rx -∗
    gen_cert -∗
    tramp_tr_obl Df pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0
      senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 (sr_swp_res_at R satp0).
  Proof.
    intros Hmisa Hmenv HSXL HMPRV HDb HDlc HDm HDs Hsok Hpmp Hpma.
    iIntros "#Hwit #Hclaim #Hcert". rewrite /tramp_tr_obl. iModIntro.
    iIntros (va pax tv rr) "%Hcanon %Hvpn %Hident Hfrag HRes Hrw Hro".
    iAssert (kmap_at (svpn_of va) tramp_ppn KP_rx) as "#Hat".
    { rewrite Hvpn. iApply "Hclaim". }
    assert (Lmisa : register_lookup misa
              (MState (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg
                 misa0 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv)
                 ∅ dev0_state).(sregs) = MISA_C).
    { cbn [sregs]. rewrite s_rs_misa. exact Hmisa. }
    assert (Lmenv : register_lookup menvcfg
              (MState (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg
                 misa0 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv)
                 ∅ dev0_state).(sregs) = MENVCFG_S).
    { cbn [sregs]. rewrite s_rs_menv. exact Hmenv. }
    assert (LSXL : _get_Mstatus_SXL (register_lookup mstatus
              (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv))
              = 'b"10").
    { rewrite s_rs_mst. exact HSXL. }
    iAssert (sr_swp_res R
               (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                  mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv))
      with "[HRes]" as "HRes'".
    { rewrite -(sr_swp_res_agree R
                  (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                     mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv)).
      rewrite s_rs_satp s_rs_tlb. iExact "HRes". }
    assert (Hside : sr_swp_side R (InstructionFetch tt) va tramp_ppn KP_rx Db
                      s_Drw s_Dro
                      (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg
                 misa0 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv)
                      (MState (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg
                 misa0 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv)
                         ∅ dev0_state)).
    { apply (sr_swp_side_ok R (InstructionFetch tt) va tramp_ppn KP_rx Db
               s_Drw s_Dro).
      - left. reflexivity.
      - rewrite s_rs_satp. exact Hsok.
      - rewrite s_rs_pcfg s_rs_paddr. exact Hpmp.
      - rewrite s_rs_pma. exact Hpma.
      - rewrite s_rs_mst. exact HMPRV.
      - exact HDm.
      - exact HDs.
      - cbn [sregs]. rewrite s_rs_mst. exact HSXL.
      - reflexivity.
      - rewrite /s_Drw. set_solver. }
    iApply (swp_mono with "[] [-]").
    2:{ iApply (sr_swp_translate_wit R (InstructionFetch tt) s_Drw s_Dro Df
                  (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                     mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv)
                  (MState (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg
                     misa0 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv)
                     ∅ dev0_state)
                  Db va pax tramp_ppn KP_rx rr
                  s_disj (or_introl eq_refl) eq_refl
                  s_in_mst s_in_priv s_in_satp s_in_pma s_in_pcfg
                  s_in_paddr s_in_htif
                  HDb (fun r _ => eq_refl) HDlc (fun r _ => eq_refl)
                  ltac:(by apply s_rs_priv) ltac:(by apply s_rs_htif) eq_refl
                  Lmisa Lmenv LSXL
                  (exec_effectivePrivilege_fetch _ Supervisor _)
                  (goodb_effectivePrivilege_fetch Db _ Supervisor _)
                  (exec_is_shadow_stack_fetch _)
                  (goodb_is_shadow_stack_fetch Db _)
                  Hcanon Hident Hside
                  with "Hwit Hat Hcert Hfrag HRes' Hrw Hro"). }
    iIntros (r) "(-> & %rsf & %Hshape & Hrw & Hro & HRes & Hany)".
    iSplitR; [done |].
    destruct Hshape as [-> | (tvx & ->)].
    - iExists tv. iFrame "Hany Hrw Hro".
      iEval (rewrite -(sr_swp_res_agree R
                (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                   mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv))
             s_rs_satp s_rs_tlb) in "HRes".
      iExact "HRes".
    - assert (Lsatp : register_lookup satp
                (register_set tlb tvx
                   (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                      mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv))
                = satp0).
      { tlbpeel; apply s_rs_satp. }
      assert (Ltlbv : register_lookup tlb
                (register_set tlb tvx
                   (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                      mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv))
                = tvx)
        by apply register_lookup_set.
      assert (Hag : reg_agree_on (s_Drw ∪ s_Dro)
                (register_set tlb tvx
                   (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                      mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv))
                (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                   mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tvx)).
      { apply (s_rs_agree pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tvx);
          [ tlbpeel; apply s_rs_PC
          | tlbpeel; apply s_rs_nPC
          | tlbpeel; apply s_rs_ms
          | tlbpeel; apply s_rs_mi
          | tlbpeel; apply s_rs_cy
          | tlbpeel; apply s_rs_ti
          | tlbpeel; apply s_rs_ip
          | exact Ltlbv
          | tlbpeel; apply s_rs_priv
          | tlbpeel; apply s_rs_mst
          | tlbpeel; apply s_rs_hart
          | tlbpeel; apply s_rs_pcfg
          | tlbpeel; apply s_rs_paddr
          | tlbpeel; apply s_rs_mc
          | tlbpeel; apply s_rs_micfg
          | tlbpeel; apply s_rs_misa
          | tlbpeel; apply s_rs_sec
          | tlbpeel; apply s_rs_pma
          | tlbpeel; apply s_rs_htif
          | tlbpeel; apply s_rs_elp
          | tlbpeel; apply s_rs_senv
          | exact Lsatp
          | tlbpeel; apply s_rs_mie
          | tlbpeel; apply s_rs_mdl
          | tlbpeel; apply s_rs_menv ]. }
      iDestruct (s_rw_ext _ _ Hag with "Hrw") as "Hrw".
      iDestruct (s_ro_ext_gen Df _ _ Hag with "Hro") as "Hro".
      iExists tvx. iFrame "Hany Hrw Hro".
      iEval (rewrite -(sr_swp_res_agree R
                (register_set tlb tvx
                   (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                      mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv)))
             Lsatp Ltlbv) in "HRes".
      iExact "HRes".
  Qed.

  (* the whole-tower form the wrapper takes.  [WpSmodePtFetch]'s
     [spt_fetch_tr_of_regime], one va-family over: the producer wants
     [misa0 = MISA_C] and [pma_allows_ram pmar0], which [tramp_fetch_tr]
     ∀-quantifies, so it applies only from INSIDE the box -- where the
     frame's own discarded misa / pma_regions cells and [hw_config]'s pins
     turn the two ∀-bound components into the literals. *)
  Lemma tramp_fetch_tr_of_regime (R : s_regime) (dq : dfrac)
      (pc mst0 satp0 mie0 mdv0 menv0 : SailStdpp.Values.mword 64)
      (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) :
    menv0 = MENVCFG_S ->
    _get_Mstatus_SXL mst0 = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV mst0) ('b"1") = false ->
    sr_swp_satp_ok R satp0 ->
    pmp_ent0_ok pcfg paddr ->
    sr_ktier_wit R KT1 -∗
    kmap_at tramp_vpn tramp_ppn KP_rx -∗
    hw_config -∗
    tramp_fetch_tr (s_Df_mix dq) (sr_swp_res_at R satp0) pc mst0 satp0 mie0
      mdv0 menv0 pcfg paddr.
  Proof.
    intros Hmenv HSXL HMPRV Hsatpok Hpmpok.
    iIntros "#Hwit #Hclaim #Hhw".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    rewrite /tramp_fetch_tr.
    iIntros (ms bmi cy ti ip mc micfg misa0 mseccfg0 senv0 pmar0 elp0).
    rewrite /tramp_tr_obl.
    iModIntro.
    iIntros (va pax tv rr) "%Hcanon %Hvpn %Hident Hfrag HRes Hrw Hro".
    iAssert (⌜ misa0 = MISA_C /\ pma_allows_all pmar0 ⌝)%I as %[Hmisa Hpma].
    { iEval (rewrite s_ro_split_mix) in "Hro".
      iDestruct "Hro" as "(_ & _ & _ & _ & _ & _ & _ & Hmisac & _ & Hpmac & _)".
      rewrite s_rs_misa s_rs_pma.
      iDestruct "Hhw" as (misaX secX pmaX elpX)
        "(#HmisaW & _ & #HpmaW & _ & _ & _ & _ & _ & _ & _ & %HpmaV & _ & _ &
          _ & _ & %HmisaV & _)".
      iDestruct (reg_pointsto_agree with "Hmisac HmisaW") as %->.
      iDestruct (reg_pointsto_agree with "Hpmac HpmaW") as %->.
      iPureIntro. split; [exact HmisaV | exact HpmaV]. }
    subst misa0.
    iDestruct (tramp_tr_obl_of_regime R (s_Df_mix dq) spf_Db pc ms bmi cy ti ip
                 mst0 pcfg paddr mc micfg MISA_C mseccfg0 senv0 pmar0 elp0
                 satp0 mie0 mdv0 menv0 eq_refl Hmenv HSXL HMPRV spf_Db_in
                 spf_leafchk_in spf_Db_mst spf_Db_satp Hsatpok Hpmpok
                 (pma_all_ram Hpma) with "Hwit Hclaim Hcert") as "#Hobl".
    iApply ("Hobl" $! va pax tv rr with "[%] [%] [%] Hfrag HRes Hrw Hro");
      [ exact Hcanon | exact Hvpn | exact Hident ].
  Qed.

  (* THE SHARED-KERNEL-TABLE INSTANCE.  [kpt_share_regime]'s Sv39 walk
     honors every claim, so its [sr_kwit] is [emp] ([sr_ktier_wit_kpt_share])
     and the trampoline fetch costs the caller only the persistent claim.
     This is the heir of the deleted [ktramp_fetch_habs_share]. *)
  Lemma ktramp_fetch_tr_share (root_ppn : mword 44) (dq : dfrac)
      (pc mst0 satp0 mie0 mdv0 menv0 : SailStdpp.Values.mword 64)
      (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) :
    menv0 = MENVCFG_S ->
    _get_Mstatus_SXL mst0 = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV mst0) ('b"1") = false ->
    kpt_satp_ok root_ppn satp0 ->
    pmp_ent0_ok pcfg paddr ->
    kmap_at tramp_vpn tramp_ppn KP_rx -∗
    hw_config -∗
    tramp_fetch_tr (s_Df_mix dq) (kpt_res_at root_ppn satp0) pc mst0 satp0
      mie0 mdv0 menv0 pcfg paddr.
  Proof.
    intros Hmenv HSXL HMPRV Hsatpok Hpmpok.
    iIntros "#Hclaim #Hhw".
    iApply (tramp_fetch_tr_of_regime (kpt_share_regime root_ppn) dq pc mst0
              satp0 mie0 mdv0 menv0 pcfg paddr Hmenv HSXL HMPRV Hsatpok Hpmpok
              with "[] Hclaim Hhw").
    iApply (sr_ktier_wit_kpt_share root_ppn KT1).
  Qed.

  (* ==================================================================== *)
  (* THE SHARED-KERNEL-TABLE STEP ENGINE.                                  *)
  (*                                                                      *)
  (* [wp_instr_tramp_pt] at [Res := kpt_res_at root_ppn satp0], on the     *)
  (* per-hart bundle [KptShare.tlb_res_pt] -- i.e.                         *)
  (* [SmodeCorePt.wp_instr_s_config_sr]'s open/call/close over             *)
  (* [kpt_share_regime root_ppn] (whose [sr_inv] IS [tlb_res_pt] and whose *)
  (* [sr_swp_open]/[sr_swp_close] ARE [kpt_swp_open]/[kpt_swp_close]),     *)
  (* with the trampoline fetch underneath.  The statement is CONCRETE in   *)
  (* [root_ppn] on purpose: an [s_regime] in a parameter position makes    *)
  (* the call site's [iApply] diverge (claude-notes/projects/              *)
  (* kvminithart-tlb-lane.md §3), so the regime lives only in the PROOF.   *)
  (* ==================================================================== *)
  Lemma wp_instr_ktramp_pt_share (root_ppn : mword 44)
      (pc pa : mword 64) (is_rvc : bool) (i : instruction)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (mie1 menvcfg1 : mword 64)
      (Rl : mword 64 -> mword 64 -> mword 64 -> iProp Σ) {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    neq_vec (bits_of_virtaddr (Virtaddr pc))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr pc)) (Z.sub 39 1) 0)) = false ->
    svpn_of pc = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr pc)) (Z.sub pagesize_bits 1) 0)) = pa ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int pc 2)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int pc 2))) (Z.sub 39 1) 0)) = false ->
    svpn_of (add_vec_int pc 2) = tramp_vpn ->
    zero_extend' 64 (concat_vec tramp_ppn
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int pc 2))) (Z.sub pagesize_bits 1) 0)) = add_vec_int pa 2 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pa) 4 = is_aligned_vaddr (Virtaddr pc) 4 ->
    kmap_at tramp_vpn tramp_ppn KP_rx -∗
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_res_pt root_ppn -∗
    pc_is pc -∗
    instr pa is_rvc i -∗
    (∀ (satp0 : mword 64) (pcfg : type_of_register pmpcfg_n)
       (paddr : type_of_register pmpaddr_n) (tv' : type_of_register tlb),
       ⌜ kpt_satp_ok root_ppn satp0 ⌝ -∗ ⌜ pmp_ent0_ok pcfg paddr ⌝ -∗
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       satp ↦ᵣ satp0 -∗ pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
       tlb ↦ᵣ tv' -∗ kpt_res_at root_ppn satp0 tv' -∗
       clock_res -∗
       (R_bitvector_64 PC) ↦ᵣ pc -∗
       (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc (if is_rvc then 2 else 4)) -∗
       resv_any cpu_id -∗
       swp (execute i)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                   cur_privilege ↦ᵣ{ dq } Supervisor ∗
                   mie ↦ᵣ{ dq } mie1 ∗
                   menvcfg ↦ᵣ{ dq } menvcfg1 ∗
                   satp ↦ᵣ satp0 ∗ pmpcfg_n ↦ᵣ pcfg ∗
                   pmpaddr_n ↦ᵣ paddr ∗
                   (∃ tv2 : type_of_register tlb,
                      tlb ↦ᵣ tv2 ∗ kpt_res_at root_ppn satp0 tv2) ∗
                   clock_res ∗
                   (∃ ms1 mdv1 npc : mword 64,
                      mstatus ↦ᵣ{ dq } ms1 ∗ mideleg ↦ᵣ{ dq } mdv1 ∗
                      (R_bitvector_64 PC) ↦ᵣ pc ∗
                      (R_bitvector_64 nextPC) ↦ᵣ npc ∗ Rl npc ms1 mdv1) ∗
                   resv_any cpu_id)) -∗
    ▷ (∀ npc ms1 mdv1 : mword 64,
         hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
         cur_privilege ↦ᵣ{ dq } Supervisor -∗
         mstatus ↦ᵣ{ dq } ms1 -∗
         mie ↦ᵣ{ dq } mie1 -∗
         mideleg ↦ᵣ{ dq } mdv1 -∗
         menvcfg ↦ᵣ{ dq } menvcfg1 -∗
         tlb_res_pt root_ppn -∗
         pc_is npc -∗ Rl npc ms1 mdv1 -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HSIE HMPRV HSXL Hmm HPBMTE Hmenvval
           Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4.
    iIntros "#Hclaim #Hhw #Hminv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hinv Hpc
             Hinstr Hex Hcont".
    iDestruct (kpt_swp_open root_ppn with "Hinv") as (satp0 tlbv pcfg paddr)
      "(%Hsatpok & %Hpmpok & Hsatp & Htlbc & Hpcfg & Hpaddr & HRes)".
    iApply (wp_instr_tramp_pt (kpt_res_at root_ppn satp0) pc pa is_rvc i
              mstatus0 mie_v mdv0 menvcfg0 satp0 pcfg paddr tlbv
              mie1 menvcfg1 satp0 pcfg paddr Supervisor Rl (dq := dq)
              HSIE HMPRV HSXL Hmm HPBMTE Hmenvval Hpmpok
              Hcanon Hvpn Hident Hcanon2 Hvpn2 Hident2 Hva2 Hpa4va4
              with "Hhw Hminv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp
                    Hpcfg Hpaddr Htlbc HRes Hpc Hinstr [] [Hex] [Hcont]").
    - iApply (ktramp_fetch_tr_share root_ppn dq pc mstatus0 satp0 mie_v mdv0
                menvcfg0 pcfg paddr Hmenvval HSXL HMPRV Hsatpok Hpmpok
                with "Hclaim Hhw").
    - iIntros (tv') "_".
      iApply ("Hex" $! satp0 pcfg paddr tv' with "[%] [%]");
        [ exact Hsatpok | exact Hpmpok ].
    - iNext. iIntros (npc ms1 mdv1 tv1)
        "Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Hsatp Hpcfg Hpaddr Htlbc
         HRes Hpc HRl".
      iApply ("Hcont" $! npc ms1 mdv1 with
                "Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc
                 [Hsatp Htlbc Hpcfg Hpaddr HRes] Hpc HRl").
      iApply (kpt_swp_close root_ppn satp0 tv1 pcfg paddr Hsatpok Hpmpok
                with "Hsatp Htlbc Hpcfg Hpaddr HRes").
  Qed.

End TrampFetchPt.
