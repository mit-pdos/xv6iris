(* WpMmodeMret.v -- the M-mode MRET leaf, on the [swp] engine.

   [wp_mret_gpr] rides [WpInstrConfig.wp_instr_config] (the raw-cell wrapper
   for the instructions that CHANGE cur_privilege / mstatus), whose obligation
   is a [swp] over [execute (MRET tt)] at the cells the leaf holds.

   THE FOOTPRINT IS THE LEAF'S OWN, six cells wide:
     Drw = {mstatus, cur_privilege, nextPC}   (the three the walk writes)
     Dro = {misa, menvcfg, mepc}              (misa pinned by [hw_config],
                                               menvcfg/mepc owned outright)
   [mr_rs] is the anchor tower, [mr_frames] the cells <-> frames bridge and
   [mr_set_ms]/[mr_set_priv]/[mr_set_npc] the three write-normalizations that
   keep every intermediate file in the canonical [mr_rs _ _ _ _ _] shape.

   THE WALK follows the model's own binds ([swp_bind_use]/[swp_bind0_use]) with
   [swp_read_reg_pinned] / [swp_write_reg_owned] at the raw nodes.  Four
   sub-calls get a route of their own:
   - [currentlyEnabled Ext_U], [hartSupports Ext_Zicfilp] and the mstatus
     [long_csr_write_callback] read at most misa, so they are transported from
     the concrete reference state [dstateM] by [HartGoodb.hval_of_goodb] --
     which matters, because by then cur_privilege is no longer Machine and the
     [D_m] agreement would not hold;
   - [get_xLPE Supervisor]'s ANSWER depends on menvcfg's value, so it is walked
     at the leaf's own frame ([hval_of_goodb] at [MState rs _ _], not at a
     reference state);
   - [prepare_xret_target Machine] reads mepc then [align_pc]'s misa gate, and
     goes through [hfrun] ([hfrun_cE_Zca]) rather than [goodb] -- vm-computing
     [goodb] of [currentlyEnabled Ext_Zca] at a symbolic file does not finish.

   THE ONE NODE THE SPAN CANNOT TAKE is the elp reset inside
   [zicfilp_restore_elp_on_xret mRET]: MRET writes elp with the value it
   already holds, but [hw_config] pins elp at [DfracDiscarded] so no leaf can
   own it, and [hspan_node] gates a write on [r ∈ Drw] with no value-preserving
   exception.  The walk SPLITS there and takes
   [HartRegNode.swp_write_reg_same] ([swp_zicfilp_mRET_S]). *)
Require Import WpMmodeLeafBase.
Require Import RegFile.
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d SailStdpp.Base RiscvLang RiscvPtsto RiscvExec RiscvFetchExec WpGpr MinstretInv InstrBytes SailStdpp.TypeCasts SailStdpp.MachineWord SailStdpp.Values.
Require Import RiscvExtras.
Import Defs.
Require Import WpGprMret WpGprMretWp.
Import Defs.
Require Import HartSwp HartLift HartSpan HartSpanChar HartRunGen HartRegNode
        HartMCycle HartMRun HartMFrame HartGoodb WpDecodeBridge ExecCommon.
Require Import WpInstrConfig.
Require Import TsoCtx.
Local Open Scope Z_scope.


(* ==================================================================== *)
(* The MRET leaf's own six-cell footprint.                               *)
(* ==================================================================== *)
Definition mr_Drw : gset register :=
  {[ (mstatus : register); (cur_privilege : register);
     (R_bitvector_64 nextPC : register) ]}.
Definition mr_Dro : gset register :=
  {[ (misa : register); (menvcfg : register); (mepc : register) ]}.
Definition mr_Df : register -> dfrac := fun r =>
  if decide (r = (misa : register)) then DfracDiscarded else DfracOwn 1.

Definition mr_rs (ms : mword 64) (p : Privilege) (npc menv mep : mword 64)
    : regstate :=
  register_set mstatus ms
  (register_set cur_privilege p
  (register_set (R_bitvector_64 nextPC) npc
  (register_set misa MISA_C
  (register_set menvcfg menv
  (register_set mepc mep init_regstate))))).

Local Ltac mrtm := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

Lemma mr_rs_ms ms p npc menv mep :
  register_lookup mstatus (mr_rs ms p npc menv mep) = ms.
Proof. rewrite /mr_rs. apply register_lookup_set. Qed.
Lemma mr_rs_priv ms p npc menv mep :
  register_lookup cur_privilege (mr_rs ms p npc menv mep) = p.
Proof. rewrite /mr_rs. mrtm. apply register_lookup_set. Qed.
Lemma mr_rs_npc ms p npc menv mep :
  register_lookup (R_bitvector_64 nextPC) (mr_rs ms p npc menv mep) = npc.
Proof. rewrite /mr_rs. mrtm. mrtm. apply register_lookup_set. Qed.
Lemma mr_rs_misa ms p npc menv mep :
  register_lookup misa (mr_rs ms p npc menv mep) = MISA_C.
Proof. rewrite /mr_rs. mrtm. mrtm. mrtm. apply register_lookup_set. Qed.
Lemma mr_rs_menv ms p npc menv mep :
  register_lookup menvcfg (mr_rs ms p npc menv mep) = menv.
Proof. rewrite /mr_rs. mrtm. mrtm. mrtm. mrtm. apply register_lookup_set. Qed.
Lemma mr_rs_mepc ms p npc menv mep :
  register_lookup mepc (mr_rs ms p npc menv mep) = mep.
Proof. rewrite /mr_rs. mrtm. mrtm. mrtm. mrtm. mrtm. apply register_lookup_set. Qed.

Lemma mr_disj : mr_Drw ## mr_Dro.
Proof. rewrite /mr_Drw /mr_Dro. set_solver. Qed.

Lemma mr_in_ms : (mstatus : register) ∈ mr_Drw ∪ mr_Dro.
Proof. rewrite /mr_Drw. set_solver. Qed.
Lemma mr_in_priv : (cur_privilege : register) ∈ mr_Drw ∪ mr_Dro.
Proof. rewrite /mr_Drw. set_solver. Qed.
Lemma mr_in_npc : (R_bitvector_64 nextPC : register) ∈ mr_Drw ∪ mr_Dro.
Proof. rewrite /mr_Drw. set_solver. Qed.
Lemma mr_in_misa : (misa : register) ∈ mr_Drw ∪ mr_Dro.
Proof. rewrite /mr_Dro. set_solver. Qed.
Lemma mr_in_menv : (menvcfg : register) ∈ mr_Drw ∪ mr_Dro.
Proof. rewrite /mr_Dro. set_solver. Qed.
Lemma mr_in_mepc : (mepc : register) ∈ mr_Drw ∪ mr_Dro.
Proof. rewrite /mr_Dro. set_solver. Qed.
Lemma mr_w_ms : (mstatus : register) ∈ mr_Drw.
Proof. rewrite /mr_Drw. set_solver. Qed.
Lemma mr_w_priv : (cur_privilege : register) ∈ mr_Drw.
Proof. rewrite /mr_Drw. set_solver. Qed.
Lemma mr_w_npc : (R_bitvector_64 nextPC : register) ∈ mr_Drw.
Proof. rewrite /mr_Drw. set_solver. Qed.

Local Ltac mrdf :=
  unfold mr_Df;
  repeat first [ rewrite decide_True; [reflexivity|reflexivity]
               | rewrite decide_False; [|discriminate] ];
  reflexivity.
Lemma mr_Df_misa : mr_Df misa = DfracDiscarded.
Proof. mrdf. Qed.
Lemma mr_Df_menv : mr_Df menvcfg = DfracOwn 1.
Proof. mrdf. Qed.
Lemma mr_Df_mepc : mr_Df mepc = DfracOwn 1.
Proof. mrdf. Qed.

(* the three write-normalizations *)
Local Ltac mrag :=
  intros r Hr; rewrite /mr_Drw /mr_Dro in Hr;
  repeat (apply elem_of_union in Hr as [Hr|Hr]);
  apply elem_of_singleton in Hr; subst r;
  first [ rewrite register_lookup_set | mrtm ];
  rewrite ?mr_rs_ms ?mr_rs_priv ?mr_rs_npc ?mr_rs_misa ?mr_rs_menv ?mr_rs_mepc;
  reflexivity.

Lemma mr_set_ms (ms ms' : mword 64) p npc menv mep :
  reg_agree_on (mr_Drw ∪ mr_Dro)
    (register_set mstatus ms' (mr_rs ms p npc menv mep))
    (mr_rs ms' p npc menv mep).
Proof. mrag. Qed.

Lemma mr_set_priv (ms : mword 64) p p' npc menv mep :
  reg_agree_on (mr_Drw ∪ mr_Dro)
    (register_set cur_privilege p' (mr_rs ms p npc menv mep))
    (mr_rs ms p' npc menv mep).
Proof. mrag. Qed.

Lemma mr_set_npc (ms : mword 64) p npc npc' menv mep :
  reg_agree_on (mr_Drw ∪ mr_Dro)
    (register_set (R_bitvector_64 nextPC) npc' (mr_rs ms p npc menv mep))
    (mr_rs ms p npc' menv mep).
Proof. mrag. Qed.

(* ==================================================================== *)
(* The sub-calls that read ONLY misa: transported from the concrete       *)
(* reference state by [goodb], exactly as the decode is.                  *)
(* ==================================================================== *)
Definition Db_misa (r : register) : bool := register_beq r (R_bitvector_64 misa).

Lemma hval_at_misa {X : Type} (D Drw : gset register) (rs : regstate)
    (m : M X) (x : X) :
  (misa : register) ∈ D ->
  register_lookup misa rs = MISA_C ->
  goodb Db_misa m dstateM = true ->
  exec m dstateM = Some (x, dstateM) ->
  hval D Drw rs m x rs.
Proof.
  intros HD Hmisa Hg He.
  apply (hval_of_goodb Db_misa D Drw m dstateM rs x);
    [ intros r Hr; apply register_beq_eq in Hr; subst r; exact HD
    | intros r Hr; apply register_beq_eq in Hr; subst r;
      rewrite Hmisa; vm_compute; reflexivity
    | exact Hg | exact He ].
Qed.

Lemma hval_cE_U (D Drw : gset register) (rs : regstate) :
  (misa : register) ∈ D -> register_lookup misa rs = MISA_C ->
  hval D Drw rs (currentlyEnabled Ext_U) true rs.
Proof.
  intros HD Hmisa. apply hval_at_misa; [exact HD|exact Hmisa| |].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.

Lemma hval_hS_Zicfilp (D Drw : gset register) (rs : regstate) :
  (misa : register) ∈ D -> register_lookup misa rs = MISA_C ->
  hval D Drw rs (hartSupports Ext_Zicfilp) true rs.
Proof.
  intros HD Hmisa. apply hval_at_misa; [exact HD|exact Hmisa| |].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.

Lemma hval_long_csr (D Drw : gset register) (rs : regstate) (V : mword 64) :
  (misa : register) ∈ D -> register_lookup misa rs = MISA_C ->
  hval D Drw rs (long_csr_write_callback "mstatus" "mstatush" V) tt rs.
Proof.
  intros HD Hmisa. apply hval_at_misa; [exact HD|exact Hmisa| |].
  - vm_compute; reflexivity.
  - apply exec_long_csr_write_mstatus.
Qed.

(* ==================================================================== *)
(* get_xLPE at Supervisor: reads menvcfg and its ANSWER depends on the    *)
(* value, so it cannot be transported from a reference state -- it is     *)
(* walked at the leaf's own frame.                                       *)
(* ==================================================================== *)
Definition Db_menv (r : register) : bool := register_beq r (R_bitvector_64 menvcfg).

Lemma hval_get_xLPE_S (D Drw : gset register) (rs : regstate) :
  (menvcfg : register) ∈ D ->
  _get_MEnvcfg_LPE (register_lookup menvcfg rs) = ('b"0") ->
  hval D Drw rs (get_xLPE Supervisor) false rs.
Proof.
  intros HD HL.
  apply (hval_of_goodb Db_menv D Drw _ (MState rs ∅ dev0_state) rs false);
    [ intros r Hr; apply register_beq_eq in Hr; subst r; exact HD
    | intros r Hr; reflexivity
    | vm_compute; reflexivity
    | apply exec_get_xLPE_S; exact HL ].
Qed.

(* ==================================================================== *)
(* prepare_xret_target Machine = read mepc, then align_pc (which reads    *)
(* misa for Ext_Zca).  Both cells are in the leaf's read-only frame.      *)
(* ==================================================================== *)
Lemma exec_prepare_xret_M (s : mstate) :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (prepare_xret_target Machine) s
    = Some (ret_pc (register_lookup mepc s.(sregs)), s).
Proof.
  intro Hmc. unfold prepare_xret_target, get_xepc. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mepc s)).
  unfold align_pc.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Zca s Hmc)).
  cbn match. unfold ret_pc. apply exec_returnm.
Qed.


Lemma hfrun_read_reg (D Drw : gset register) (rs : regstate) (r : register) :
  r ∈ D -> hfrun 2 D Drw rs (Defs.read_reg r) = Some (register_lookup r rs, rs).
Proof. intros Hin. cbn. by rewrite (bool_decide_eq_true_2 _ Hin). Qed.

Lemma hfrun_prepare_xret_M (D Drw : gset register) (rs : regstate) :
  (mepc : register) ∈ D -> (misa : register) ∈ D ->
  eq_vec (_get_Misa_C (register_lookup misa rs))
    (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
  hfrun 8 D Drw rs (prepare_xret_target Machine)
    = Some (ret_pc (register_lookup mepc rs), rs).
Proof.
  intros HDe HDi HC.
  unfold prepare_xret_target, get_xepc. cbn match.
  apply (hfrun_bind 2 6 D Drw rs rs rs _ _ (register_lookup mepc rs) _).
  { apply hfrun_read_reg; exact HDe. }
  cbn beta. unfold align_pc.
  apply (hfrun_bind 4 2 D Drw rs rs rs _ _ true _).
  { apply hfrun_cE_Zca; assumption. }
  cbn beta zeta match. unfold ret_pc. apply hfrun_ret.
Qed.

Lemma hregwrite_val_at_write_reg (r : register) (v : type_of_register r) :
  hregwrite_val_at r (Defs.write_reg r v) = Some v.
Proof.
  cbn [Defs.write_reg hregwrite_val_at].
  match goal with
  | |- context [ match ?d with | left _ => _ | right _ => _ end ] =>
      destruct d as [Heq|Hne]
  end; [|congruence].
  assert (Heq = eq_refl) as -> by apply proof_irrel. reflexivity.
Qed.

Lemma hregwrite_resume_write_reg (r : register) (v : type_of_register r) :
  hregwrite_resume (Defs.write_reg r v) = Interface.Ret tt.
Proof. reflexivity. Qed.

Definition mr_elp (ms : mword 64) : mword 64 :=
  update_subrange_vec_dec ms 41 41 (landing_pad_bits_backwards NO_LP_EXPECTED).

Lemma mr_elp_cms5 (ms : mword 64) : mr_elp (cms4 ms) = cms5 ms.
Proof. reflexivity. Qed.

Lemma bind_returnM {X Y : Type} (x : X) (f : X -> M Y) :
  Defs.bind (returnM x) f = f x.
Proof. reflexivity. Qed.

Section MretSwp.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma mr_frames (ms : mword 64) (p : Privilege) (npc menv mep : mword 64) :
    (hreg_frame (mr_rs ms p npc menv mep) mr_Drw ∗
     hreg_frame_ro mr_Df (mr_rs ms p npc menv mep) mr_Dro : iProp Σ)
    ⊣⊢ (reg_pointsto mstatus (DfracOwn 1) ms ∗
        reg_pointsto cur_privilege (DfracOwn 1) p ∗
        reg_pointsto (R_bitvector_64 nextPC) (DfracOwn 1) npc ∗
        reg_pointsto misa DfracDiscarded MISA_C ∗
        reg_pointsto menvcfg (DfracOwn 1) menv ∗
        reg_pointsto mepc (DfracOwn 1) mep).
  Proof.
    rewrite /hreg_frame /hreg_frame_ro /mr_Drw /mr_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite mr_rs_ms mr_rs_priv mr_rs_npc mr_rs_misa mr_rs_menv mr_rs_mepc.
    rewrite mr_Df_misa mr_Df_menv mr_Df_mepc.
    by rewrite !bi.sep_assoc.
  Qed.

  Lemma mr_frames_in (ms : mword 64) (p : Privilege) (npc menv mep : mword 64) :
    reg_pointsto mstatus (DfracOwn 1) ms -∗
    reg_pointsto cur_privilege (DfracOwn 1) p -∗
    reg_pointsto (R_bitvector_64 nextPC) (DfracOwn 1) npc -∗
    reg_pointsto misa DfracDiscarded MISA_C -∗
    reg_pointsto menvcfg (DfracOwn 1) menv -∗
    reg_pointsto mepc (DfracOwn 1) mep -∗
    (hreg_frame (mr_rs ms p npc menv mep) mr_Drw ∗
     hreg_frame_ro mr_Df (mr_rs ms p npc menv mep) mr_Dro : iProp Σ).
  Proof. iIntros "H1 H2 H3 H4 H5 H6". rewrite mr_frames. iFrame. Qed.

  Lemma mr_frames_out (ms : mword 64) (p : Privilege) (npc menv mep : mword 64) :
    (hreg_frame (mr_rs ms p npc menv mep) mr_Drw ∗
     hreg_frame_ro mr_Df (mr_rs ms p npc menv mep) mr_Dro : iProp Σ) -∗
    (reg_pointsto mstatus (DfracOwn 1) ms ∗
     reg_pointsto cur_privilege (DfracOwn 1) p ∗
     reg_pointsto (R_bitvector_64 nextPC) (DfracOwn 1) npc ∗
     reg_pointsto misa DfracDiscarded MISA_C ∗
     reg_pointsto menvcfg (DfracOwn 1) menv ∗
     reg_pointsto mepc (DfracOwn 1) mep).
  Proof. rewrite mr_frames. iIntros "H". iExact "H". Qed.

  Lemma mr_rw_ext (rs rs' : regstate) :
    reg_agree_on (mr_Drw ∪ mr_Dro) rs rs' ->
    hreg_frame rs mr_Drw -∗ (hreg_frame rs' mr_Drw : iProp Σ).
  Proof.
    intros Hag. rewrite (hreg_frame_ext _ _ mr_Drw
      (reg_agree_mono (mr_Drw ∪ mr_Dro) mr_Drw _ _ ltac:(set_solver) Hag)).
    iIntros "H". iExact "H".
  Qed.

  Lemma mr_ro_ext (rs rs' : regstate) :
    reg_agree_on (mr_Drw ∪ mr_Dro) rs rs' ->
    hreg_frame_ro mr_Df rs mr_Dro -∗ (hreg_frame_ro mr_Df rs' mr_Dro : iProp Σ).
  Proof.
    intros Hag. rewrite (hreg_frame_ro_ext mr_Df _ _ mr_Dro
      (reg_agree_mono (mr_Drw ∪ mr_Dro) mr_Dro _ _ ltac:(set_solver) Hag)).
    iIntros "H". iExact "H".
  Qed.


  (* ------------------------------------------------------------------ *)
  (* [zicfilp_restore_elp_on_xret mRET Supervisor]: three mstatus nodes,   *)
  (* the menvcfg-reading [get_xLPE] probe, and then THE WRITE THE SPAN     *)
  (* CANNOT TAKE -- elp, written with the value the [hw_config] pin        *)
  (* already fixes.  The walk splits there and takes                       *)
  (* [HartRegNode.swp_write_reg_same].                                     *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_zicfilp_mRET_S (ms : mword 64) (p : Privilege)
      (npc menv mep : mword 64) :
    _get_MEnvcfg_LPE menv = ('b"0") ->
    gen_cert -∗
    reg_pointsto elp DfracDiscarded (landing_pad_bits_backwards NO_LP_EXPECTED) -∗
    hreg_frame (mr_rs ms p npc menv mep) mr_Drw -∗
    hreg_frame_ro mr_Df (mr_rs ms p npc menv mep) mr_Dro -∗
    swp (zicfilp_restore_elp_on_xret mRET Supervisor)
      (fun _ => hreg_frame (mr_rs (mr_elp ms) p npc menv mep) mr_Drw ∗
                hreg_frame_ro mr_Df (mr_rs (mr_elp ms) p npc menv mep) mr_Dro).
  Proof.
    intros HL. iIntros "#Hcert #Help Hrw Hro".
    unfold zicfilp_restore_elp_on_xret. cbn match.
    iApply (swp_bind_use _ _
              (fun x => ⌜x = _get_Mstatus_MPELP ms⌝ ∗
                hreg_frame (mr_rs (mr_elp ms) p npc menv mep) mr_Drw ∗
                hreg_frame_ro mr_Df (mr_rs (mr_elp ms) p npc menv mep) mr_Dro)%I
              _ with "[Hrw Hro] [-]").
    { iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_read_reg_pinned mr_Drw mr_Dro mr_Df _ mstatus
                  mr_disj mr_in_ms with "Hcert Hrw Hro"). }
      iIntros (w0) "(-> & Hrw & Hro)". rewrite mr_rs_ms. cbn zeta.
      iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_read_reg_pinned mr_Drw mr_Dro mr_Df _ mstatus
                  mr_disj mr_in_ms with "Hcert Hrw Hro"). }
      iIntros (w1) "(-> & Hrw & Hro)". rewrite mr_rs_ms.
      iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned mr_Drw mr_Dro mr_Df _ mstatus (mr_elp ms)
                  mr_disj mr_w_ms with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iDestruct (mr_rw_ext _ _ (mr_set_ms ms (mr_elp ms) p npc menv mep)
                   with "Hrw") as "Hrw".
      iDestruct (mr_ro_ext _ _ (mr_set_ms ms (mr_elp ms) p npc menv mep)
                   with "Hro") as "Hro".
      iApply swp_ret. iFrame. done. }
    iIntros (pelp) "(-> & Hrw & Hro)".
    iApply (swp_bind_use (get_xLPE Supervisor) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_span mr_Drw mr_Dro mr_Df _ _ _ false mr_disj
                (hval_get_xLPE_S (mr_Drw ∪ mr_Dro) mr_Drw
                   (mr_rs (mr_elp ms) p npc menv mep) mr_in_menv
                   ltac:(rewrite mr_rs_menv; exact HL))
                with "Hcert Hrw Hro"). }
    iIntros (b) "(-> & Hrw & Hro)". cbn zeta match.
    iApply (swp_write_reg_same elp DfracDiscarded _ _ _
              (hregwrite_val_at_write_reg elp _) with "Hcert Help [-]").
    iIntros "_". rewrite hregwrite_resume_write_reg.
    iApply swp_ret. iFrame.
  Qed.


  (* ------------------------------------------------------------------ *)
  (* THE WALK.  [execute (MRET tt)] at the six-cell frame, node by node    *)
  (* along the model's own binds.                                          *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_execute_MRET (ms_cur npc menvcfg1 mepc0 : mword 64)
      (newpriv : Privilege) :
    privLevel_bits_forwards (_get_Mstatus_MPP (cms2 ms_cur), ('b"0"))
      = returnM newpriv ->
    newpriv = Supervisor ->
    _get_MEnvcfg_LPE menvcfg1 = ('b"0") ->
    gen_cert -∗
    reg_pointsto elp DfracDiscarded (landing_pad_bits_backwards NO_LP_EXPECTED) -∗
    hreg_frame (mr_rs ms_cur Machine npc menvcfg1 mepc0) mr_Drw -∗
    hreg_frame_ro mr_Df (mr_rs ms_cur Machine npc menvcfg1 mepc0) mr_Dro -∗
    swp (execute (MRET tt))
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
        hreg_frame (mr_rs (cms5 ms_cur) newpriv (ret_pc mepc0) menvcfg1 mepc0)
          mr_Drw ∗
        hreg_frame_ro mr_Df
          (mr_rs (cms5 ms_cur) newpriv (ret_pc mepc0) menvcfg1 mepc0) mr_Dro).
  Proof.
    intros Hnp Hsup HL. subst newpriv.
    assert (Hnpm : generic_neq Supervisor Machine = true)
      by (vm_compute; reflexivity).
    iIntros "#Hcert #Help Hrw Hro".
    change (execute (MRET tt)) with (execute_MRET tt).
    unfold execute_MRET.
    (* -- cur_privilege, the two guards -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned mr_Drw mr_Dro mr_Df _ cur_privilege
                mr_disj mr_in_priv with "Hcert Hrw Hro"). }
    iIntros (p0) "(-> & Hrw & Hro)". rewrite mr_rs_priv.
    replace (generic_neq Machine Machine) with false by reflexivity.
    cbn match. change (ext_check_xret_priv Machine) with true.
    cbn [not negb]. cbn match.
    (* -- prev_priv -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned mr_Drw mr_Dro mr_Df _ cur_privilege
                mr_disj mr_in_priv with "Hcert Hrw Hro"). }
    iIntros (pp) "(-> & Hrw & Hro)".
    (* -- w1, w2 -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned mr_Drw mr_Dro mr_Df _ mstatus
                mr_disj mr_in_ms with "Hcert Hrw Hro"). }
    iIntros (w1) "(-> & Hrw & Hro)". rewrite mr_rs_ms.
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned mr_Drw mr_Dro mr_Df _ mstatus
                mr_disj mr_in_ms with "Hcert Hrw Hro"). }
    iIntros (w2) "(-> & Hrw & Hro)". rewrite mr_rs_ms.
    (* -- write cms1, read back -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned mr_Drw mr_Dro mr_Df _ mstatus (cms1 ms_cur)
                  mr_disj mr_w_ms with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iDestruct (mr_rw_ext _ _ (mr_set_ms ms_cur (cms1 ms_cur) Machine npc
                   menvcfg1 mepc0) with "Hrw") as "Hrw".
      iDestruct (mr_ro_ext _ _ (mr_set_ms ms_cur (cms1 ms_cur) Machine npc
                   menvcfg1 mepc0) with "Hro") as "Hro".
      iApply (swp_read_reg_pinned mr_Drw mr_Dro mr_Df _ mstatus
                mr_disj mr_in_ms with "Hcert Hrw Hro"). }
    iIntros (w3) "(-> & Hrw & Hro)". rewrite mr_rs_ms.
    (* -- write cms2, read back -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned mr_Drw mr_Dro mr_Df _ mstatus (cms2 ms_cur)
                  mr_disj mr_w_ms with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iDestruct (mr_rw_ext _ _ (mr_set_ms (cms1 ms_cur) (cms2 ms_cur) Machine npc
                   menvcfg1 mepc0) with "Hrw") as "Hrw".
      iDestruct (mr_ro_ext _ _ (mr_set_ms (cms1 ms_cur) (cms2 ms_cur) Machine npc
                   menvcfg1 mepc0) with "Hro") as "Hro".
      iApply (swp_read_reg_pinned mr_Drw mr_Dro mr_Df _ mstatus
                mr_disj mr_in_ms with "Hcert Hrw Hro"). }
    iIntros (w4) "(-> & Hrw & Hro)". rewrite mr_rs_ms.
    (* -- the MPP decode -- *)
    rewrite Hnp bind_returnM. cbn beta.
    (* -- write cur_privilege, read mstatus -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned mr_Drw mr_Dro mr_Df _ cur_privilege Supervisor
                  mr_disj mr_w_priv with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iDestruct (mr_rw_ext _ _ (mr_set_priv (cms2 ms_cur) Machine Supervisor npc
                   menvcfg1 mepc0) with "Hrw") as "Hrw".
      iDestruct (mr_ro_ext _ _ (mr_set_priv (cms2 ms_cur) Machine Supervisor npc
                   menvcfg1 mepc0) with "Hro") as "Hro".
      iApply (swp_read_reg_pinned mr_Drw mr_Dro mr_Df _ mstatus
                mr_disj mr_in_ms with "Hcert Hrw Hro"). }
    iIntros (w6) "(-> & Hrw & Hro)". rewrite mr_rs_ms.
    (* -- currentlyEnabled Ext_U -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_span mr_Drw mr_Dro mr_Df _ _ _ true mr_disj
                (hval_cE_U (mr_Drw ∪ mr_Dro) mr_Drw
                   (mr_rs (cms2 ms_cur) Supervisor npc menvcfg1 mepc0)
                   mr_in_misa (mr_rs_misa _ _ _ _ _))
                with "Hcert Hrw Hro"). }
    iIntros (w7) "(-> & Hrw & Hro)". cbn zeta match.
    (* -- write cms3, read cur_privilege -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned mr_Drw mr_Dro mr_Df _ mstatus (cms3 ms_cur)
                  mr_disj mr_w_ms with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iDestruct (mr_rw_ext _ _ (mr_set_ms (cms2 ms_cur) (cms3 ms_cur) Supervisor
                   npc menvcfg1 mepc0) with "Hrw") as "Hrw".
      iDestruct (mr_ro_ext _ _ (mr_set_ms (cms2 ms_cur) (cms3 ms_cur) Supervisor
                   npc menvcfg1 mepc0) with "Hro") as "Hro".
      iApply (swp_read_reg_pinned mr_Drw mr_Dro mr_Df _ cur_privilege
                mr_disj mr_in_priv with "Hcert Hrw Hro"). }
    iIntros (w9) "(-> & Hrw & Hro)". rewrite mr_rs_priv. rewrite Hnpm. cbn match.
    (* -- the MPRV clear, then hartSupports Zicfilp -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
        { iApply (swp_read_reg_pinned mr_Drw mr_Dro mr_Df _ mstatus
                    mr_disj mr_in_ms with "Hcert Hrw Hro"). }
        iIntros (w10) "(-> & Hrw & Hro)". rewrite mr_rs_ms.
        iApply (swp_write_reg_owned mr_Drw mr_Dro mr_Df _ mstatus (cms4 ms_cur)
                  mr_disj mr_w_ms with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iDestruct (mr_rw_ext _ _ (mr_set_ms (cms3 ms_cur) (cms4 ms_cur) Supervisor
                   npc menvcfg1 mepc0) with "Hrw") as "Hrw".
      iDestruct (mr_ro_ext _ _ (mr_set_ms (cms3 ms_cur) (cms4 ms_cur) Supervisor
                   npc menvcfg1 mepc0) with "Hro") as "Hro".
      iApply (swp_span mr_Drw mr_Dro mr_Df _ _ _ true mr_disj
                (hval_hS_Zicfilp (mr_Drw ∪ mr_Dro) mr_Drw
                   (mr_rs (cms4 ms_cur) Supervisor npc menvcfg1 mepc0)
                   mr_in_misa (mr_rs_misa _ _ _ _ _))
                with "Hcert Hrw Hro"). }
    iIntros (w11) "(-> & Hrw & Hro)". cbn match.
    (* -- the elp reset, then read mstatus -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
        { iApply (swp_read_reg_pinned mr_Drw mr_Dro mr_Df _ cur_privilege
                    mr_disj mr_in_priv with "Hcert Hrw Hro"). }
        iIntros (w12) "(-> & Hrw & Hro)". rewrite mr_rs_priv.
        iApply (swp_zicfilp_mRET_S (cms4 ms_cur) Supervisor npc menvcfg1 mepc0
                  HL with "Hcert Help Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iApply (swp_read_reg_pinned mr_Drw mr_Dro mr_Df _ mstatus
                mr_disj mr_in_ms with "Hcert Hrw Hro"). }
    iIntros (w13) "(-> & Hrw & Hro)". rewrite mr_rs_ms.
    rewrite mr_elp_cms5.
    (* -- the callback, the print guard, prepare_xret_target -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ : unit =>
                   hreg_frame (mr_rs (cms5 ms_cur) Supervisor npc menvcfg1 mepc0)
                     mr_Drw ∗
                   hreg_frame_ro mr_Df
                     (mr_rs (cms5 ms_cur) Supervisor npc menvcfg1 mepc0) mr_Dro)%I
                _ with "[Hrw Hro] [-]").
      { iApply (swp_bind0_use _ _
                  (fun x : unit => ⌜x = tt⌝ ∗
                     hreg_frame (mr_rs (cms5 ms_cur) Supervisor npc menvcfg1 mepc0)
                       mr_Drw ∗
                     hreg_frame_ro mr_Df
                       (mr_rs (cms5 ms_cur) Supervisor npc menvcfg1 mepc0) mr_Dro)%I
                  _ with "[Hrw Hro] [-]").
        { iApply (swp_span mr_Drw mr_Dro mr_Df _ _ _ tt mr_disj
                    (hval_long_csr (mr_Drw ∪ mr_Dro) mr_Drw
                       (mr_rs (cms5 ms_cur) Supervisor npc menvcfg1 mepc0)
                       _ mr_in_misa (mr_rs_misa _ _ _ _ _))
                    with "Hcert Hrw Hro"). }
        iIntros (u) "(_ & Hrw & Hro)".
        replace (get_config_print_exception tt) with false by reflexivity.
        cbn match. iApply swp_ret. iFrame. }
      iIntros (u) "[Hrw Hro]".
      iApply (swp_hfrun 8 mr_Drw mr_Dro mr_Df _ _ _ _ mr_disj
                (hfrun_prepare_xret_M (mr_Drw ∪ mr_Dro) mr_Drw
                   (mr_rs (cms5 ms_cur) Supervisor npc menvcfg1 mepc0)
                   mr_in_mepc mr_in_misa
                   ltac:(rewrite mr_rs_misa; vm_compute; reflexivity))
                with "Hcert Hrw Hro"). }
    iIntros (w17) "(-> & Hrw & Hro)". rewrite mr_rs_mepc.
    (* -- set_next_pc -- *)
    iApply (swp_bind0_use _ _
              (fun _ : unit =>
                 hreg_frame
                   (mr_rs (cms5 ms_cur) Supervisor (ret_pc mepc0) menvcfg1 mepc0)
                   mr_Drw ∗
                 hreg_frame_ro mr_Df
                   (mr_rs (cms5 ms_cur) Supervisor (ret_pc mepc0) menvcfg1 mepc0)
                   mr_Dro)%I
              _ with "[Hrw Hro] [-]").
    { unfold set_next_pc. cbn match zeta.
      iApply (swp_bind0_use _ _ _
                (fun _ : unit =>
                   hreg_frame
                     (mr_rs (cms5 ms_cur) Supervisor (ret_pc mepc0) menvcfg1 mepc0)
                     mr_Drw ∗
                   hreg_frame_ro mr_Df
                     (mr_rs (cms5 ms_cur) Supervisor (ret_pc mepc0) menvcfg1 mepc0)
                     mr_Dro)%I
                with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned mr_Drw mr_Dro mr_Df _
                  (R_bitvector_64 nextPC) (ret_pc mepc0)
                  mr_disj mr_w_npc with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iDestruct (mr_rw_ext _ _ (mr_set_npc (cms5 ms_cur) Supervisor npc
                   (ret_pc mepc0) menvcfg1 mepc0) with "Hrw") as "Hrw".
      iDestruct (mr_ro_ext _ _ (mr_set_npc (cms5 ms_cur) Supervisor npc
                   (ret_pc mepc0) menvcfg1 mepc0) with "Hro") as "Hro".
      iApply swp_ret. iFrame. }
    iIntros (u) "[Hrw Hro]". iApply swp_ret. iSplitR; [done|]. iFrame.
  Qed.

End MretSwp.

(* from WpGprMretNew.v *)
Section WpMretGpr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* wp_mret_gpr: the new-layer MRET WP.  Unbundled config premises with the
     mstatus value [ms_cur] explicit; premises mirror [wp_mret]'s execute
     tower: the decoded MPP target [newpriv] (for xv6: Supervisor, from
     [mstatus_legalized_MPP] on the csrw'd value), newpriv ≠ Machine, and the
     xLPE-off fact (lpe = false, forced by the persistent elp pinning).
     The continuation receives the RAW post-MRET cells: privilege [newpriv],
     mstatus [cms5 ms_cur], pc at the aligned mepc target [ret_pc mepc0]; pmpcfg,
     mepc and the GPR file are unchanged. *)
  Lemma wp_mret_gpr (pc : mword 64)
      (newpriv : Privilege)
      (ms_cur mepc0 menvcfg1 : mword 64)
      (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    eq_vec (_get_Mstatus_MIE ms_cur) ('b"1") = false ->
    privLevel_bits_forwards (_get_Mstatus_MPP (cms2 ms_cur), ('b"0"))
      = returnM newpriv ->
    newpriv = Supervisor ->
    _get_MEnvcfg_LPE menvcfg1 = ('b"0") ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Machine -∗
    mstatus ↦ᵣ ms_cur -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    menvcfg ↦ᵣ menvcfg1 -∗
    pc_is pc -∗
    gpr_file m -∗
    mepc ↦ᵣ mepc0 -∗
    instr pc false (MRET tt) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ newpriv -∗
      mstatus ↦ᵣ cms5 ms_cur -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      menvcfg ↦ᵣ menvcfg1 -∗
      pc_is (ret_pc mepc0) -∗
      gpr_file m -∗
      mepc ↦ᵣ mepc0 -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat HmIE Hnp Hsup Hlpe0)
      "#Hhw #Hinv Hhs Hpriv Hms Hpmpc Hmenv Hpc Hfile Hmepc Hinstr Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    pose proof (mword1_not_lp elp0 Help_np) as Help0.
    subst misa0 elp0.
    iApply (wp_instr_config pc (ret_pc mepc0) false (MRET tt) m m newpriv
              ms_cur (cms5 ms_cur) pmpcfg0 pmpcfg0
              (menvcfg ↦ᵣ menvcfg1 ∗ mepc ↦ᵣ mepc0)%I Hpmp HmIE Hstat
              with "Hhw Hinv Hhs Hpriv Hms Hpmpc Hpc Hfile Hinstr
                    [Hmenv Hmepc] [Hcont]").
    - iIntros "Hpriv Hms Hpmpc Hfile HPC HnPC".
      iDestruct (mr_frames_in ms_cur Machine _ menvcfg1 mepc0
                   with "Hms Hpriv HnPC Hmisa Hmenv Hmepc") as "[Hrw Hro]".
      iApply (swp_mono with "[Hfile HPC Hpmpc] [Hrw Hro]");
        [| iApply (swp_execute_MRET ms_cur _ menvcfg1 mepc0 newpriv
                     Hnp Hsup Hlpe0 with "Hcert Help Hrw Hro") ].
      iIntros (e) "(-> & Hrw & Hro)".
      iDestruct (mr_frames_out with "[$Hrw $Hro]")
        as "(Hms & Hpriv & HnPC & _ & Hmenv & Hmepc)".
      iSplitR; [done|]. iFrame.
    - iNext. iIntros "Hhs Hpriv Hms Hpmpc Hpc Hfile [Hmenv Hmepc]".
      iApply ("Hcont" with "Hhs Hpriv Hms Hpmpc Hmenv Hpc Hfile Hmepc").
  Qed.

End WpMretGpr.
