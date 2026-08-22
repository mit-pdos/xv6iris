(* WpSmodePtEngine.v -- the S-mode instruction ENGINES the leaf sweep was
   missing, at the per-node ([swp]) layer.

   Every register-only S-mode instruction already has a node shape
   ([WpMmodeSwpBase]), every branch/jump/fence one has a walk
   ([WpSconfEngine]), and the data accesses have theirs ([HartSMem]).  SRET
   had only the exec-side reduction ([WpSmodeSret.exec_execute_SRET_menv]),
   so [WpSmodePtCtl.wp_sret_gpr_r] and [WpSconfSret.wp_sret_s_sconf] had
   nothing to stand on.  [swp_execute_SRET_S] below is that walk --
   [WpMmodeMret.swp_execute_MRET] one privilege over, node by node along the
   model's own binds.

   Also here: [s_va_canon_of_lo], the Sv39 canonicality premise every
   translate lemma asks for, derived from the [uint va < 2^38] bound the
   fetch obligation hands its caller.

   NOTHING HERE IS REGIME-AWARE.  The regime layer ([SRegime] /
   [SmodeCorePt]) is a sibling effort; this file deliberately does not
   depend on it, so it stays green while that interface moves. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import RegFile WpGpr.
Require Import HartLift HartSpan HartSpanChar HartRegNode HartGoodb WpDecodeBridge.
Require Import HartSwp.
Require Import MstatusBits WpGprMret WpMmodeLeafBase HartRunGen.
Require Import HartMFrame HartMCycle WpMmodeJump WpDecode.
Require Import RiscvExtras.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.


(* ===================================================================== *)
(* §1  CANONICALITY, from the [uint va < 2^38] the fetch obligation gives. *)
(* ===================================================================== *)
Lemma se39_unsigned_e (a : SailStdpp.Values.mword 64) :
  bv_unsigned
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a))
                        (Z.sub 39 1) 0))
  = bv_wrap 64 (bv_swrap 39 (bv_unsigned a mod 549755813888)).
Proof.
  cbn [bits_of_virtaddr].
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned. unfold bv_signed.
  rewrite (subrange_dec_unsigned_lo0 a (Z.sub 39 1) 549755813888
             ltac:(lia) ltac:(vm_compute; reflexivity)).
  reflexivity.
Qed.

Lemma s_va_canon_of_lo (a : SailStdpp.Values.mword 64) :
  (uint a < 274877906944)%Z ->
  neq_vec (bits_of_virtaddr (Virtaddr a))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a))
                        (Z.sub 39 1) 0)) = false.
Proof.
  rewrite uint_unsigned. intro Hlt.
  pose proof (proj1 (bv_unsigned_in_range _ a)) as Hlo.
  unfold neq_vec. rewrite negb_false_iff. rewrite eq_vec_true_iff.
  cbn [bits_of_virtaddr]. apply bv_eq. rewrite se39_unsigned_e.
  unfold bv_swrap, bv_wrap.
  assert (E39 : bv_modulus 39 = 549755813888) by (vm_compute; reflexivity).
  assert (E64 : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
  assert (Eh39 : bv_half_modulus 39 = 274877906944) by (vm_compute; reflexivity).
  rewrite E39 E64 Eh39.
  set (V := bv_unsigned a) in *.
  rewrite (Z.mod_small V 549755813888 ltac:(lia)).
  rewrite (Z.mod_small (V + 274877906944) 549755813888 ltac:(lia)).
  replace (V + 274877906944 - 274877906944) with V by lia.
  rewrite (Z.mod_small V 18446744073709551616 ltac:(lia)). reflexivity.
Qed.

(* ===================================================================== *)
(* §2  THE SRET FOOTPRINT -- [WpMmodeMret]'s six-cell frame with [sepc]    *)
(*     in place of [mepc].  SRET reads cur_privilege / mstatus / misa /    *)
(*     menvcfg / sepc and writes mstatus, cur_privilege and nextPC; elp is *)
(*     written with the value [hw_config] already pins, so it is a         *)
(*     write-that-changes-nothing and stays OUT of the frame.              *)
(* ===================================================================== *)
Definition sret_Drw : gset register :=
  {[ (mstatus : register); (cur_privilege : register);
     (R_bitvector_64 nextPC : register) ]}.
Definition sret_Dro : gset register :=
  {[ (misa : register); (menvcfg : register); (sepc : register) ]}.
Definition sret_Df : register -> dfrac := fun r =>
  if decide (r = (misa : register)) then DfracDiscarded else DfracOwn 1.

Definition sret_rs (ms : mword 64) (p : Privilege) (npc menv sep : mword 64)
    : regstate :=
  register_set mstatus ms
  (register_set cur_privilege p
  (register_set (R_bitvector_64 nextPC) npc
  (register_set misa MISA_C
  (register_set menvcfg menv
  (register_set sepc sep init_regstate))))).

Local Ltac srtm := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

Lemma sret_rs_ms ms p npc menv sep :
  register_lookup mstatus (sret_rs ms p npc menv sep) = ms.
Proof. rewrite /sret_rs. apply register_lookup_set. Qed.
Lemma sret_rs_priv ms p npc menv sep :
  register_lookup cur_privilege (sret_rs ms p npc menv sep) = p.
Proof. rewrite /sret_rs. srtm. apply register_lookup_set. Qed.
Lemma sret_rs_npc ms p npc menv sep :
  register_lookup (R_bitvector_64 nextPC) (sret_rs ms p npc menv sep) = npc.
Proof. rewrite /sret_rs. srtm. srtm. apply register_lookup_set. Qed.
Lemma sret_rs_misa ms p npc menv sep :
  register_lookup misa (sret_rs ms p npc menv sep) = MISA_C.
Proof. rewrite /sret_rs. srtm. srtm. srtm. apply register_lookup_set. Qed.
Lemma sret_rs_menv ms p npc menv sep :
  register_lookup menvcfg (sret_rs ms p npc menv sep) = menv.
Proof. rewrite /sret_rs. srtm. srtm. srtm. srtm. apply register_lookup_set. Qed.
Lemma sret_rs_sepc ms p npc menv sep :
  register_lookup sepc (sret_rs ms p npc menv sep) = sep.
Proof. rewrite /sret_rs. srtm. srtm. srtm. srtm. srtm. apply register_lookup_set. Qed.

Lemma sret_disj : sret_Drw ## sret_Dro.
Proof. rewrite /sret_Drw /sret_Dro. set_solver. Qed.

Lemma sret_in_ms : (mstatus : register) ∈ sret_Drw ∪ sret_Dro.
Proof. rewrite /sret_Drw. set_solver. Qed.
Lemma sret_in_priv : (cur_privilege : register) ∈ sret_Drw ∪ sret_Dro.
Proof. rewrite /sret_Drw. set_solver. Qed.
Lemma sret_in_npc : (R_bitvector_64 nextPC : register) ∈ sret_Drw ∪ sret_Dro.
Proof. rewrite /sret_Drw. set_solver. Qed.
Lemma sret_in_misa : (misa : register) ∈ sret_Drw ∪ sret_Dro.
Proof. rewrite /sret_Dro. set_solver. Qed.
Lemma sret_in_menv : (menvcfg : register) ∈ sret_Drw ∪ sret_Dro.
Proof. rewrite /sret_Dro. set_solver. Qed.
Lemma sret_in_sepc : (sepc : register) ∈ sret_Drw ∪ sret_Dro.
Proof. rewrite /sret_Dro. set_solver. Qed.
Lemma sret_w_ms : (mstatus : register) ∈ sret_Drw.
Proof. rewrite /sret_Drw. set_solver. Qed.
Lemma sret_w_priv : (cur_privilege : register) ∈ sret_Drw.
Proof. rewrite /sret_Drw. set_solver. Qed.
Lemma sret_w_npc : (R_bitvector_64 nextPC : register) ∈ sret_Drw.
Proof. rewrite /sret_Drw. set_solver. Qed.

Local Ltac srdf :=
  unfold sret_Df;
  repeat first [ rewrite decide_True; [reflexivity|reflexivity]
               | rewrite decide_False; [|discriminate] ];
  reflexivity.
Lemma sret_Df_misa : sret_Df misa = DfracDiscarded.
Proof. srdf. Qed.
Lemma sret_Df_menv : sret_Df menvcfg = DfracOwn 1.
Proof. srdf. Qed.
Lemma sret_Df_sepc : sret_Df sepc = DfracOwn 1.
Proof. srdf. Qed.

Local Ltac srag :=
  intros r Hr; rewrite /sret_Drw /sret_Dro in Hr;
  repeat (apply elem_of_union in Hr as [Hr|Hr]);
  apply elem_of_singleton in Hr; subst r;
  first [ rewrite register_lookup_set | srtm ];
  rewrite ?sret_rs_ms ?sret_rs_priv ?sret_rs_npc ?sret_rs_misa ?sret_rs_menv
          ?sret_rs_sepc;
  reflexivity.

Lemma sret_set_ms (ms ms' : mword 64) p npc menv sep :
  reg_agree_on (sret_Drw ∪ sret_Dro)
    (register_set mstatus ms' (sret_rs ms p npc menv sep))
    (sret_rs ms' p npc menv sep).
Proof. srag. Qed.

Lemma sret_set_priv (ms : mword 64) p p' npc menv sep :
  reg_agree_on (sret_Drw ∪ sret_Dro)
    (register_set cur_privilege p' (sret_rs ms p npc menv sep))
    (sret_rs ms p' npc menv sep).
Proof. srag. Qed.

Lemma sret_set_npc (ms : mword 64) p npc npc' menv sep :
  reg_agree_on (sret_Drw ∪ sret_Dro)
    (register_set (R_bitvector_64 nextPC) npc' (sret_rs ms p npc menv sep))
    (sret_rs ms p npc' menv sep).
Proof. srag. Qed.

(* ---- helpers cloned from WpMmodeMret.v (that file is a leaf and cannot be
   required from an engine file; each is two lines) ---- *)
Definition sD_misa (r : register) : bool := register_beq r (R_bitvector_64 misa).
Definition sD_menv (r : register) : bool := register_beq r (R_bitvector_64 menvcfg).

Lemma s_hval_at_misa {X : Type} (D Drw : gset register) (rs : regstate)
    (m : M X) (x : X) :
  (misa : register) ∈ D ->
  register_lookup misa rs = MISA_C ->
  goodb sD_misa m dstateM = true ->
  exec m dstateM = Some (x, dstateM) ->
  hval D Drw rs m x rs.
Proof.
  intros HD Hmisa Hg He.
  apply (hval_of_goodb sD_misa D Drw m dstateM rs x);
    [ intros r Hr; apply register_beq_eq in Hr; subst r; exact HD
    | intros r Hr; apply register_beq_eq in Hr; subst r;
      rewrite Hmisa; vm_compute; reflexivity
    | exact Hg | exact He ].
Qed.

Lemma s_hval_hS_Zicfilp (D Drw : gset register) (rs : regstate) :
  (misa : register) ∈ D -> register_lookup misa rs = MISA_C ->
  hval D Drw rs (hartSupports Ext_Zicfilp) true rs.
Proof.
  intros HD Hmisa. apply s_hval_at_misa; [exact HD|exact Hmisa| |].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.

Lemma s_hval_long_csr (D Drw : gset register) (rs : regstate) (V : mword 64) :
  (misa : register) ∈ D -> register_lookup misa rs = MISA_C ->
  hval D Drw rs (long_csr_write_callback "mstatus" "mstatush" V) tt rs.
Proof.
  intros HD Hmisa. apply s_hval_at_misa; [exact HD|exact Hmisa| |].
  - vm_compute; reflexivity.
  - apply exec_long_csr_write_mstatus.
Qed.

Lemma s_hval_get_xLPE_S (D Drw : gset register) (rs : regstate) :
  (menvcfg : register) ∈ D ->
  _get_MEnvcfg_LPE (register_lookup menvcfg rs) = ('b"0") ->
  hval D Drw rs (get_xLPE Supervisor) false rs.
Proof.
  intros HD HL.
  apply (hval_of_goodb sD_menv D Drw _ (MState rs ∅ dev0_state) rs false);
    [ intros r Hr; apply register_beq_eq in Hr; subst r; exact HD
    | intros r Hr; reflexivity
    | vm_compute; reflexivity
    | apply exec_get_xLPE_S; exact HL ].
Qed.

Lemma s_hfrun_read_reg (D Drw : gset register) (rs : regstate) (r : register) :
  r ∈ D -> hfrun 2 D Drw rs (Defs.read_reg r) = Some (register_lookup r rs, rs).
Proof. intros Hin. cbn. by rewrite (bool_decide_eq_true_2 _ Hin). Qed.

Lemma s_hregwrite_val_at_write_reg (r : register) (v : type_of_register r) :
  hregwrite_val_at r (Defs.write_reg r v) = Some v.
Proof.
  cbn [Defs.write_reg hregwrite_val_at].
  match goal with
  | |- context [ match ?d with | left _ => _ | right _ => _ end ] =>
      destruct d as [Heq|Hne]
  end; [|congruence].
  assert (Heq = eq_refl) as -> by apply proof_irrel. reflexivity.
Qed.

Lemma s_hregwrite_resume_write_reg (r : register) (v : type_of_register r) :
  hregwrite_resume (Defs.write_reg r v) = Interface.Ret tt.
Proof. reflexivity. Qed.

Lemma s_bind_returnM {X Y : Type} (x : X) (f : X -> M Y) :
  Defs.bind (returnM x) f = f x.
Proof. reflexivity. Qed.

(* the SPELP clear, as a function of the mstatus value (SRET's bit 23; the
   MRET twin is [WpMmodeMret.mr_elp] at bit 41) *)
Definition sret_elpclr (ms : mword 64) : mword 64 :=
  update_subrange_vec_dec ms 23 23 (landing_pad_bits_backwards NO_LP_EXPECTED).

Lemma sret_elpclr_ms5 (ms : mword 64) : sret_elpclr (sret_ms4 ms) = sret_ms5 ms.
Proof. reflexivity. Qed.

(* [currentlyEnabled Ext_S], the one extension gate MRET's file does not
   already carry (it has Ext_U and Zicfilp) *)
Lemma hval_cE_S (D Drw : gset register) (rs : regstate) :
  (misa : register) ∈ D -> register_lookup misa rs = MISA_C ->
  hval D Drw rs (currentlyEnabled Ext_S) true rs.
Proof.
  intros HD Hmisa. apply s_hval_at_misa; [exact HD|exact Hmisa| |].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.

(* [prepare_xret_target Supervisor] = read sepc, then [align_pc] (which
   reads misa for Ext_Zca) -- [WpMmodeMret.hfrun_prepare_xret_M] at the
   other privilege. *)
Lemma exec_prepare_xret_S (s : mstate) :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (prepare_xret_target Supervisor) s
    = Some (ret_pc (register_lookup sepc s.(sregs)), s).
Proof.
  intro Hmc. unfold prepare_xret_target, get_xepc. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg sepc s)).
  unfold align_pc.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Zca s Hmc)).
  cbn match. unfold ret_pc. apply exec_returnm.
Qed.

Lemma hfrun_prepare_xret_S (D Drw : gset register) (rs : regstate) :
  (sepc : register) ∈ D -> (misa : register) ∈ D ->
  eq_vec (_get_Misa_C (register_lookup misa rs))
    (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
  hfrun 8 D Drw rs (prepare_xret_target Supervisor)
    = Some (ret_pc (register_lookup sepc rs), rs).
Proof.
  intros HDe HDi HC.
  unfold prepare_xret_target, get_xepc. cbn match.
  apply (hfrun_bind 2 6 D Drw rs rs rs _ _ (register_lookup sepc rs) _).
  { apply s_hfrun_read_reg; exact HDe. }
  cbn beta. unfold align_pc.
  apply (hfrun_bind 4 2 D Drw rs rs rs _ _ true _).
  { apply hfrun_cE_Zca; assumption. }
  cbn beta zeta match. unfold ret_pc. apply hfrun_ret.
Qed.

Section SretSwp.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma sret_frames (ms : mword 64) (p : Privilege) (npc menv sep : mword 64) :
    (hreg_frame (sret_rs ms p npc menv sep) sret_Drw ∗
     hreg_frame_ro sret_Df (sret_rs ms p npc menv sep) sret_Dro : iProp Σ)
    ⊣⊢ (reg_pointsto mstatus (DfracOwn 1) ms ∗
        reg_pointsto cur_privilege (DfracOwn 1) p ∗
        reg_pointsto (R_bitvector_64 nextPC) (DfracOwn 1) npc ∗
        reg_pointsto misa DfracDiscarded MISA_C ∗
        reg_pointsto menvcfg (DfracOwn 1) menv ∗
        reg_pointsto sepc (DfracOwn 1) sep).
  Proof.
    rewrite /hreg_frame /hreg_frame_ro /sret_Drw /sret_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite sret_rs_ms sret_rs_priv sret_rs_npc sret_rs_misa sret_rs_menv
            sret_rs_sepc.
    rewrite sret_Df_misa sret_Df_menv sret_Df_sepc.
    by rewrite !bi.sep_assoc.
  Qed.

  Lemma sret_frames_in (ms : mword 64) (p : Privilege) (npc menv sep : mword 64) :
    reg_pointsto mstatus (DfracOwn 1) ms -∗
    reg_pointsto cur_privilege (DfracOwn 1) p -∗
    reg_pointsto (R_bitvector_64 nextPC) (DfracOwn 1) npc -∗
    reg_pointsto misa DfracDiscarded MISA_C -∗
    reg_pointsto menvcfg (DfracOwn 1) menv -∗
    reg_pointsto sepc (DfracOwn 1) sep -∗
    (hreg_frame (sret_rs ms p npc menv sep) sret_Drw ∗
     hreg_frame_ro sret_Df (sret_rs ms p npc menv sep) sret_Dro : iProp Σ).
  Proof. iIntros "H1 H2 H3 H4 H5 H6". rewrite sret_frames. iFrame. Qed.

  Lemma sret_frames_out (ms : mword 64) (p : Privilege) (npc menv sep : mword 64) :
    (hreg_frame (sret_rs ms p npc menv sep) sret_Drw ∗
     hreg_frame_ro sret_Df (sret_rs ms p npc menv sep) sret_Dro : iProp Σ) -∗
    (reg_pointsto mstatus (DfracOwn 1) ms ∗
     reg_pointsto cur_privilege (DfracOwn 1) p ∗
     reg_pointsto (R_bitvector_64 nextPC) (DfracOwn 1) npc ∗
     reg_pointsto misa DfracDiscarded MISA_C ∗
     reg_pointsto menvcfg (DfracOwn 1) menv ∗
     reg_pointsto sepc (DfracOwn 1) sep).
  Proof. rewrite sret_frames. iIntros "H". iExact "H". Qed.

  Lemma sret_rw_ext (rs rs' : regstate) :
    reg_agree_on (sret_Drw ∪ sret_Dro) rs rs' ->
    hreg_frame rs sret_Drw -∗ (hreg_frame rs' sret_Drw : iProp Σ).
  Proof.
    intros Hag. rewrite (hreg_frame_ext _ _ sret_Drw
      (reg_agree_mono (sret_Drw ∪ sret_Dro) sret_Drw _ _ ltac:(set_solver) Hag)).
    iIntros "H". iExact "H".
  Qed.

  Lemma sret_ro_ext (rs rs' : regstate) :
    reg_agree_on (sret_Drw ∪ sret_Dro) rs rs' ->
    hreg_frame_ro sret_Df rs sret_Dro -∗
    (hreg_frame_ro sret_Df rs' sret_Dro : iProp Σ).
  Proof.
    intros Hag. rewrite (hreg_frame_ro_ext sret_Df _ _ sret_Dro
      (reg_agree_mono (sret_Drw ∪ sret_Dro) sret_Dro _ _ ltac:(set_solver) Hag)).
    iIntros "H". iExact "H".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* [zicfilp_restore_elp_on_xret sRET Supervisor]: two mstatus reads, the *)
  (* SPELP clear, the menvcfg-reading [get_xLPE] probe, and then THE WRITE *)
  (* THE SPAN CANNOT TAKE -- elp, at the value [hw_config] already pins.   *)
  (* [WpMmodeMret.swp_zicfilp_mRET_S] at the other xRET kind.             *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_zicfilp_sRET_S (ms : mword 64) (p : Privilege)
      (npc menv sep : mword 64) :
    _get_MEnvcfg_LPE menv = ('b"0") ->
    gen_cert -∗
    reg_pointsto elp DfracDiscarded (landing_pad_bits_backwards NO_LP_EXPECTED) -∗
    hreg_frame (sret_rs ms p npc menv sep) sret_Drw -∗
    hreg_frame_ro sret_Df (sret_rs ms p npc menv sep) sret_Dro -∗
    swp (zicfilp_restore_elp_on_xret sRET Supervisor)
      (fun _ => hreg_frame (sret_rs (sret_elpclr ms) p npc menv sep) sret_Drw ∗
                hreg_frame_ro sret_Df (sret_rs (sret_elpclr ms) p npc menv sep)
                  sret_Dro).
  Proof.
    intros HL. iIntros "#Hcert #Help Hrw Hro".
    unfold zicfilp_restore_elp_on_xret. cbn match.
    iApply (swp_bind_use _ _
              (fun x => ⌜x = _get_Mstatus_SPELP ms⌝ ∗
                hreg_frame (sret_rs (sret_elpclr ms) p npc menv sep) sret_Drw ∗
                hreg_frame_ro sret_Df
                  (sret_rs (sret_elpclr ms) p npc menv sep) sret_Dro)%I
              _ with "[Hrw Hro] [-]").
    { iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_read_reg_pinned sret_Drw sret_Dro sret_Df _ mstatus
                  sret_disj sret_in_ms with "Hcert Hrw Hro"). }
      iIntros (w0) "(-> & Hrw & Hro)". rewrite sret_rs_ms. cbn zeta.
      iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_read_reg_pinned sret_Drw sret_Dro sret_Df _ mstatus
                  sret_disj sret_in_ms with "Hcert Hrw Hro"). }
      iIntros (w1) "(-> & Hrw & Hro)". rewrite sret_rs_ms.
      iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned sret_Drw sret_Dro sret_Df _ mstatus
                  (sret_elpclr ms) sret_disj sret_w_ms with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iDestruct (sret_rw_ext _ _ (sret_set_ms ms (sret_elpclr ms) p npc menv sep)
                   with "Hrw") as "Hrw".
      iDestruct (sret_ro_ext _ _ (sret_set_ms ms (sret_elpclr ms) p npc menv sep)
                   with "Hro") as "Hro".
      iApply swp_ret. iFrame. done. }
    iIntros (pelp) "(-> & Hrw & Hro)".
    iApply (swp_bind_use (get_xLPE Supervisor) _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_span sret_Drw sret_Dro sret_Df _ _ _ false sret_disj
                (s_hval_get_xLPE_S (sret_Drw ∪ sret_Dro) sret_Drw
                   (sret_rs (sret_elpclr ms) p npc menv sep) sret_in_menv
                   ltac:(rewrite sret_rs_menv; exact HL))
                with "Hcert Hrw Hro"). }
    iIntros (b) "(-> & Hrw & Hro)". cbn zeta match.
    iApply (swp_write_reg_same elp DfracDiscarded _ _ _
              (s_hregwrite_val_at_write_reg elp _) with "Hcert Help [-]").
    iIntros "_". rewrite s_hregwrite_resume_write_reg.
    iApply swp_ret. iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE WALK.  [execute (SRET tt)] at the six-cell frame, node by node    *)
  (* along the model's own binds -- [WpMmodeMret.swp_execute_MRET]'s twin. *)
  (* ------------------------------------------------------------------ *)
  Local Notation SF ms npc menv sep :=
    (hreg_frame (sret_rs ms Supervisor npc menv sep) sret_Drw ∗
     hreg_frame_ro sret_Df (sret_rs ms Supervisor npc menv sep) sret_Dro)%I.

  Lemma swp_execute_SRET_S (ms_cur npc menvcfg1 sepc0 : mword 64) :
    eq_vec (_get_Mstatus_TSR ms_cur) ('b"1") = false ->
    sret_newpriv ms_cur = Supervisor ->
    _get_MEnvcfg_LPE menvcfg1 = ('b"0") ->
    gen_cert -∗
    reg_pointsto elp DfracDiscarded (landing_pad_bits_backwards NO_LP_EXPECTED) -∗
    hreg_frame (sret_rs ms_cur Supervisor npc menvcfg1 sepc0) sret_Drw -∗
    hreg_frame_ro sret_Df (sret_rs ms_cur Supervisor npc menvcfg1 sepc0)
      sret_Dro -∗
    swp (execute (SRET tt))
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
        hreg_frame (sret_rs (sret_ms5 ms_cur) Supervisor (ret_pc sepc0)
                      menvcfg1 sepc0) sret_Drw ∗
        hreg_frame_ro sret_Df
          (sret_rs (sret_ms5 ms_cur) Supervisor (ret_pc sepc0) menvcfg1 sepc0)
          sret_Dro).
  Proof.
    intros HTSR Hsup HL.
    assert (Hnpm : generic_neq Supervisor Machine = true)
      by (vm_compute; reflexivity).
    iIntros "#Hcert #Help Hrw Hro".
    change (execute (SRET tt)) with (execute_SRET tt).
    unfold execute_SRET.
    (* -- cur_privilege, then the sret_illegal guard -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned sret_Drw sret_Dro sret_Df _ cur_privilege
                sret_disj sret_in_priv with "Hcert Hrw Hro"). }
    iIntros (p0) "(-> & Hrw & Hro)". rewrite sret_rs_priv. cbn match.
    iApply (swp_bind_use _ _
              (fun l : bool => ⌜l = false⌝ ∗ SF ms_cur npc menvcfg1 sepc0)%I
              _ with "[Hrw Hro] [-]").
    { unfold or_boolM.
      iApply (swp_bind_use _ _
                (fun a : bool => ⌜a = false⌝ ∗ SF ms_cur npc menvcfg1 sepc0)%I
                _ with "[Hrw Hro] [-]").
      { iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
        { iApply (swp_span sret_Drw sret_Dro sret_Df _ _ _ true sret_disj
                    (hval_cE_S (sret_Drw ∪ sret_Dro) sret_Drw
                       (sret_rs ms_cur Supervisor npc menvcfg1 sepc0)
                       sret_in_misa (sret_rs_misa _ _ _ _ _))
                    with "Hcert Hrw Hro"). }
        iIntros (w1) "(-> & Hrw & Hro)".
        iApply swp_ret. iSplitR; [done|]. iFrame. }
      iIntros (a) "(-> & Hrw & Hro)". cbn match.
      iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_read_reg_pinned sret_Drw sret_Dro sret_Df _ mstatus
                  sret_disj sret_in_ms with "Hcert Hrw Hro"). }
      iIntros (w2) "(-> & Hrw & Hro)". rewrite sret_rs_ms.
      iApply swp_ret. iSplitR; [iPureIntro; exact HTSR|]. iFrame. }
    iIntros (l) "(-> & Hrw & Hro)". cbn match.
    change (ext_check_xret_priv Supervisor) with true.
    cbn [Riscv.rv64d.not negb]. cbn match.
    (* -- prev_priv -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned sret_Drw sret_Dro sret_Df _ cur_privilege
                sret_disj sret_in_priv with "Hcert Hrw Hro"). }
    iIntros (pp) "(-> & Hrw & Hro)".
    (* -- w7, w8 -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned sret_Drw sret_Dro sret_Df _ mstatus
                sret_disj sret_in_ms with "Hcert Hrw Hro"). }
    iIntros (w7) "(-> & Hrw & Hro)". rewrite sret_rs_ms.
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned sret_Drw sret_Dro sret_Df _ mstatus
                sret_disj sret_in_ms with "Hcert Hrw Hro"). }
    iIntros (w8) "(-> & Hrw & Hro)". rewrite sret_rs_ms.
    (* -- write sret_ms1, read back -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned sret_Drw sret_Dro sret_Df _ mstatus
                  (sret_ms1 ms_cur) sret_disj sret_w_ms with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iDestruct (sret_rw_ext _ _ (sret_set_ms ms_cur (sret_ms1 ms_cur)
                   Supervisor npc menvcfg1 sepc0) with "Hrw") as "Hrw".
      iDestruct (sret_ro_ext _ _ (sret_set_ms ms_cur (sret_ms1 ms_cur)
                   Supervisor npc menvcfg1 sepc0) with "Hro") as "Hro".
      iApply (swp_read_reg_pinned sret_Drw sret_Dro sret_Df _ mstatus
                sret_disj sret_in_ms with "Hcert Hrw Hro"). }
    iIntros (w9) "(-> & Hrw & Hro)". rewrite sret_rs_ms.
    (* -- write sret_ms2, read back -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned sret_Drw sret_Dro sret_Df _ mstatus
                  (sret_ms2 ms_cur) sret_disj sret_w_ms with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iDestruct (sret_rw_ext _ _ (sret_set_ms (sret_ms1 ms_cur) (sret_ms2 ms_cur)
                   Supervisor npc menvcfg1 sepc0) with "Hrw") as "Hrw".
      iDestruct (sret_ro_ext _ _ (sret_set_ms (sret_ms1 ms_cur) (sret_ms2 ms_cur)
                   Supervisor npc menvcfg1 sepc0) with "Hro") as "Hro".
      iApply (swp_read_reg_pinned sret_Drw sret_Dro sret_Df _ mstatus
                sret_disj sret_in_ms with "Hcert Hrw Hro"). }
    iIntros (w10) "(-> & Hrw & Hro)". rewrite sret_rs_ms.
    (* -- the SPP decode, then write cur_privilege and read mstatus -- *)
    change (if eq_vec (_get_Mstatus_SPP (sret_ms2 ms_cur)) ('b"1")
            then Supervisor else User) with (sret_newpriv ms_cur).
    rewrite Hsup.
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned sret_Drw sret_Dro sret_Df _ cur_privilege
                  Supervisor sret_disj sret_w_priv with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iDestruct (sret_rw_ext _ _ (sret_set_priv (sret_ms2 ms_cur) Supervisor
                   Supervisor npc menvcfg1 sepc0) with "Hrw") as "Hrw".
      iDestruct (sret_ro_ext _ _ (sret_set_priv (sret_ms2 ms_cur) Supervisor
                   Supervisor npc menvcfg1 sepc0) with "Hro") as "Hro".
      iApply (swp_read_reg_pinned sret_Drw sret_Dro sret_Df _ mstatus
                sret_disj sret_in_ms with "Hcert Hrw Hro"). }
    iIntros (w12) "(-> & Hrw & Hro)". rewrite sret_rs_ms.
    (* -- write sret_ms3, read cur_privilege, the newpriv guard -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned sret_Drw sret_Dro sret_Df _ mstatus
                  (sret_ms3 ms_cur) sret_disj sret_w_ms with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iDestruct (sret_rw_ext _ _ (sret_set_ms (sret_ms2 ms_cur) (sret_ms3 ms_cur)
                   Supervisor npc menvcfg1 sepc0) with "Hrw") as "Hrw".
      iDestruct (sret_ro_ext _ _ (sret_set_ms (sret_ms2 ms_cur) (sret_ms3 ms_cur)
                   Supervisor npc menvcfg1 sepc0) with "Hro") as "Hro".
      iApply (swp_read_reg_pinned sret_Drw sret_Dro sret_Df _ cur_privilege
                sret_disj sret_in_priv with "Hcert Hrw Hro"). }
    iIntros (w13) "(-> & Hrw & Hro)". rewrite sret_rs_priv. rewrite Hnpm.
    cbn match.
    (* -- the MPRV clear, then hartSupports Zicfilp -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
        { iApply (swp_read_reg_pinned sret_Drw sret_Dro sret_Df _ mstatus
                    sret_disj sret_in_ms with "Hcert Hrw Hro"). }
        iIntros (w14) "(-> & Hrw & Hro)". rewrite sret_rs_ms.
        iApply (swp_write_reg_owned sret_Drw sret_Dro sret_Df _ mstatus
                  (sret_ms4 ms_cur) sret_disj sret_w_ms with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iDestruct (sret_rw_ext _ _ (sret_set_ms (sret_ms3 ms_cur) (sret_ms4 ms_cur)
                   Supervisor npc menvcfg1 sepc0) with "Hrw") as "Hrw".
      iDestruct (sret_ro_ext _ _ (sret_set_ms (sret_ms3 ms_cur) (sret_ms4 ms_cur)
                   Supervisor npc menvcfg1 sepc0) with "Hro") as "Hro".
      iApply (swp_span sret_Drw sret_Dro sret_Df _ _ _ true sret_disj
                (s_hval_hS_Zicfilp (sret_Drw ∪ sret_Dro) sret_Drw
                   (sret_rs (sret_ms4 ms_cur) Supervisor npc menvcfg1 sepc0)
                   sret_in_misa (sret_rs_misa _ _ _ _ _))
                with "Hcert Hrw Hro"). }
    iIntros (w15) "(-> & Hrw & Hro)". cbn match.
    (* -- the elp reset, then read mstatus -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _ _ _ with "[Hrw Hro] [-]").
      { iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
        { iApply (swp_read_reg_pinned sret_Drw sret_Dro sret_Df _ cur_privilege
                    sret_disj sret_in_priv with "Hcert Hrw Hro"). }
        iIntros (w16) "(-> & Hrw & Hro)". rewrite sret_rs_priv.
        iApply (swp_zicfilp_sRET_S (sret_ms4 ms_cur) Supervisor npc menvcfg1
                  sepc0 HL with "Hcert Help Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iApply (swp_read_reg_pinned sret_Drw sret_Dro sret_Df _ mstatus
                sret_disj sret_in_ms with "Hcert Hrw Hro"). }
    iIntros (w17) "(-> & Hrw & Hro)". rewrite sret_rs_ms.
    rewrite sret_elpclr_ms5.
    (* -- the callback, the print guard, prepare_xret_target -- *)
    iApply (swp_bind_use _ _ _ _ with "[Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ : unit => SF (sret_ms5 ms_cur) npc menvcfg1 sepc0)%I
                _ with "[Hrw Hro] [-]").
      { iApply (swp_bind0_use _ _
                  (fun x : unit => ⌜x = tt⌝ ∗
                     SF (sret_ms5 ms_cur) npc menvcfg1 sepc0)%I
                  _ with "[Hrw Hro] [-]").
        { iApply (swp_span sret_Drw sret_Dro sret_Df _ _ _ tt sret_disj
                    (s_hval_long_csr (sret_Drw ∪ sret_Dro) sret_Drw
                       (sret_rs (sret_ms5 ms_cur) Supervisor npc menvcfg1 sepc0)
                       _ sret_in_misa (sret_rs_misa _ _ _ _ _))
                    with "Hcert Hrw Hro"). }
        iIntros (u) "(_ & Hrw & Hro)".
        replace (get_config_print_exception tt) with false by reflexivity.
        cbn match. iApply swp_ret. iFrame. }
      iIntros (u) "[Hrw Hro]".
      iApply (swp_hfrun 8 sret_Drw sret_Dro sret_Df _ _ _ _ sret_disj
                (hfrun_prepare_xret_S (sret_Drw ∪ sret_Dro) sret_Drw
                   (sret_rs (sret_ms5 ms_cur) Supervisor npc menvcfg1 sepc0)
                   sret_in_sepc sret_in_misa
                   ltac:(rewrite sret_rs_misa; vm_compute; reflexivity))
                with "Hcert Hrw Hro"). }
    iIntros (w21) "(-> & Hrw & Hro)". rewrite sret_rs_sepc.
    (* -- set_next_pc -- *)
    iApply (swp_bind0_use _ _
              (fun _ : unit =>
                 SF (sret_ms5 ms_cur) (ret_pc sepc0) menvcfg1 sepc0)%I
              _ with "[Hrw Hro] [-]").
    { unfold set_next_pc. cbn match zeta.
      iApply (swp_bind0_use _ _ _
                (fun _ : unit =>
                   SF (sret_ms5 ms_cur) (ret_pc sepc0) menvcfg1 sepc0)%I
                with "[Hrw Hro] [-]").
      { iApply (swp_write_reg_owned sret_Drw sret_Dro sret_Df _
                  (R_bitvector_64 nextPC) (ret_pc sepc0)
                  sret_disj sret_w_npc with "Hcert Hrw Hro"). }
      iIntros (u) "[Hrw Hro]".
      iDestruct (sret_rw_ext _ _ (sret_set_npc (sret_ms5 ms_cur) Supervisor npc
                   (ret_pc sepc0) menvcfg1 sepc0) with "Hrw") as "Hrw".
      iDestruct (sret_ro_ext _ _ (sret_set_npc (sret_ms5 ms_cur) Supervisor npc
                   (ret_pc sepc0) menvcfg1 sepc0) with "Hro") as "Hro".
      iApply swp_ret. iFrame. }
    iIntros (u) "[Hrw Hro]". iApply swp_ret. iSplitR; [done|]. iFrame.
  Qed.

End SretSwp.



(* ===================================================================== *)
(* §3  THE S-MODE DATA-ACCESS FOOTPRINT.                                  *)
(*                                                                       *)
(* [HartSMem]'s engines are stated over a frame, and an S-mode data leaf   *)
(* holds CELLS -- the ones its wrapper lends (cur_privilege, mstatus,      *)
(* menvcfg, satp, pmpcfg_n, pmpaddr_n, tlb) plus the persistent pins       *)
(* [hw_config] carries (misa, pma_regions, htif_tohost_base).  That is     *)
(* exactly the read set of [translateAddr] + [transform_effective_address] *)
(* + the PMP/PMA checks, and nothing else; the GPRs stay out (a symbolic   *)
(* register index is the one node no walker takes) and so do PC/nextPC (a  *)
(* load or a store touches neither).                                       *)
(*                                                                       *)
(* [tlb] is the ONLY writable cell: the walk may fill it, which is what     *)
(* [SRegime.sr_swp_translate]'s landing disjunct records.                  *)
(* ===================================================================== *)
Definition sda_Drw : gset register := {[ (tlb : register) ]}.

Definition sda_Dro : gset register :=
  {[ (mstatus : register); (cur_privilege : register); (menvcfg : register);
     (satp : register); (pma_regions : register); (pmpcfg_n : register);
     (pmpaddr_n : register); (htif_tohost_base : register);
     (misa : register) ]}.

(* the fraction split: the config cells at the caller's [dq], the regime's
   three at full ownership, the [hw_config] pins discarded *)
Definition sda_Df (dq : dfrac) : register -> dfrac := fun r =>
  if decide (r = (misa : register)) then DfracDiscarded
  else if decide (r = (pma_regions : register)) then DfracDiscarded
  else if decide (r = (htif_tohost_base : register)) then DfracDiscarded
  else if decide (r = (satp : register)) then DfracOwn 1
  else if decide (r = (pmpcfg_n : register)) then DfracOwn 1
  else if decide (r = (pmpaddr_n : register)) then DfracOwn 1
  else dq.

Definition sda_rs (mst0 menv0 satp0 : SailStdpp.Values.mword 64)
    (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
    (paddr : type_of_register pmpaddr_n)
    (tlbv : type_of_register tlb) : regstate :=
  register_set tlb tlbv
  (register_set mstatus mst0
  (register_set cur_privilege Supervisor
  (register_set menvcfg menv0
  (register_set satp satp0
  (register_set pma_regions pmar0
  (register_set pmpcfg_n pcfg
  (register_set pmpaddr_n paddr
  (register_set htif_tohost_base None
  (register_set misa MISA_C init_regstate))))))))).

Local Ltac sdtm := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

Section sda_lookups.
  Context (mst0 menv0 satp0 : SailStdpp.Values.mword 64)
          (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
          (paddr : type_of_register pmpaddr_n)
          (tlbv : type_of_register tlb).
  Local Notation rs := (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv).

  Lemma sda_rs_tlb : register_lookup tlb rs = tlbv.
  Proof. rewrite /sda_rs. apply register_lookup_set. Qed.
  Lemma sda_rs_mst : register_lookup mstatus rs = mst0.
  Proof. rewrite /sda_rs. sdtm. apply register_lookup_set. Qed.
  Lemma sda_rs_priv : register_lookup cur_privilege rs = Supervisor.
  Proof. rewrite /sda_rs. sdtm. sdtm. apply register_lookup_set. Qed.
  Lemma sda_rs_menv : register_lookup menvcfg rs = menv0.
  Proof. rewrite /sda_rs. sdtm. sdtm. sdtm. apply register_lookup_set. Qed.
  Lemma sda_rs_satp : register_lookup satp rs = satp0.
  Proof. rewrite /sda_rs. sdtm. sdtm. sdtm. sdtm. apply register_lookup_set. Qed.
  Lemma sda_rs_pma : register_lookup pma_regions rs = pmar0.
  Proof. rewrite /sda_rs. sdtm. sdtm. sdtm. sdtm. sdtm.
         apply register_lookup_set. Qed.
  Lemma sda_rs_pcfg : register_lookup pmpcfg_n rs = pcfg.
  Proof. rewrite /sda_rs. sdtm. sdtm. sdtm. sdtm. sdtm. sdtm.
         apply register_lookup_set. Qed.
  Lemma sda_rs_paddr : register_lookup pmpaddr_n rs = paddr.
  Proof. rewrite /sda_rs. sdtm. sdtm. sdtm. sdtm. sdtm. sdtm. sdtm.
         apply register_lookup_set. Qed.
  Lemma sda_rs_htif : register_lookup htif_tohost_base rs = None.
  Proof. rewrite /sda_rs. sdtm. sdtm. sdtm. sdtm. sdtm. sdtm. sdtm. sdtm.
         apply register_lookup_set. Qed.
  Lemma sda_rs_misa : register_lookup misa rs = MISA_C.
  Proof. rewrite /sda_rs. sdtm. sdtm. sdtm. sdtm. sdtm. sdtm. sdtm. sdtm. sdtm.
         apply register_lookup_set. Qed.
End sda_lookups.

Lemma sda_disj : sda_Drw ## sda_Dro.
Proof. rewrite /sda_Drw /sda_Dro. set_solver. Qed.

Lemma sda_w_tlb : (tlb : register) ∈ sda_Drw.
Proof. rewrite /sda_Drw. set_solver. Qed.
Lemma sda_in_tlb : (tlb : register) ∈ sda_Drw ∪ sda_Dro.
Proof. rewrite /sda_Drw. set_solver. Qed.
Lemma sda_in_mst : (mstatus : register) ∈ sda_Drw ∪ sda_Dro.
Proof. rewrite /sda_Dro. set_solver. Qed.
Lemma sda_in_priv : (cur_privilege : register) ∈ sda_Drw ∪ sda_Dro.
Proof. rewrite /sda_Dro. set_solver. Qed.
Lemma sda_in_menv : (menvcfg : register) ∈ sda_Drw ∪ sda_Dro.
Proof. rewrite /sda_Dro. set_solver. Qed.
Lemma sda_in_satp : (satp : register) ∈ sda_Drw ∪ sda_Dro.
Proof. rewrite /sda_Dro. set_solver. Qed.
Lemma sda_in_pma : (pma_regions : register) ∈ sda_Drw ∪ sda_Dro.
Proof. rewrite /sda_Dro. set_solver. Qed.
Lemma sda_in_pcfg : (pmpcfg_n : register) ∈ sda_Drw ∪ sda_Dro.
Proof. rewrite /sda_Dro. set_solver. Qed.
Lemma sda_in_paddr : (pmpaddr_n : register) ∈ sda_Drw ∪ sda_Dro.
Proof. rewrite /sda_Dro. set_solver. Qed.
Lemma sda_in_htif : (htif_tohost_base : register) ∈ sda_Drw ∪ sda_Dro.
Proof. rewrite /sda_Dro. set_solver. Qed.
Lemma sda_in_misa : (misa : register) ∈ sda_Drw ∪ sda_Dro.
Proof. rewrite /sda_Dro. set_solver. Qed.

(* ===================================================================== *)
(* THE BARE DATA WRITE SET.                                               *)
(*                                                                       *)
(* [sda_Drw] is the tlb cell AND NOTHING ELSE -- a data access writes no  *)
(* other register -- and it is there because a Sv39 walk FILLS the TLB on *)
(* a miss.  At Bare the model's [translateAddr] returns before the TLB is *)
(* consulted at all (rv64d.v: the [Bare] arm is a bare [returnR]), so the *)
(* Bare data frame is EMPTY.                                             *)
(*                                                                       *)
(* This is what lets the Bare arm of [IntrDefs.strans_inv] hold no tlb    *)
(* cell, which is what lets kvminithart keep the flushed-TLB fact its     *)
(* pre-port proof kept -- see claude-notes/projects/main-cycle-port.md,   *)
(* "THE KVMINITHART LANE".  ONE lemma absorbs the difference              *)
(* ([WpIntrInv.sda_translate_slot]); no leaf ever sees which set it is on. *)
(* ===================================================================== *)
Definition sda_Drwb : gset register := ∅.

Lemma sda_disj_b : sda_Drwb ## sda_Dro.
Proof. rewrite /sda_Drwb. set_solver. Qed.

(* the [∈ D ∪ sda_Dro] family at an ARBITRARY write set.  Every member but
   the tlb is proved from [sda_Dro] alone above, so the generalization is
   free -- and the tlb has no twin, on purpose. *)
Lemma sda_in_mst_D (D : gset register) : (mstatus : register) ∈ D ∪ sda_Dro.
Proof. rewrite /sda_Dro. set_solver. Qed.
Lemma sda_in_priv_D (D : gset register) : (cur_privilege : register) ∈ D ∪ sda_Dro.
Proof. rewrite /sda_Dro. set_solver. Qed.
Lemma sda_in_menv_D (D : gset register) : (menvcfg : register) ∈ D ∪ sda_Dro.
Proof. rewrite /sda_Dro. set_solver. Qed.
Lemma sda_in_satp_D (D : gset register) : (satp : register) ∈ D ∪ sda_Dro.
Proof. rewrite /sda_Dro. set_solver. Qed.
Lemma sda_in_pma_D (D : gset register) : (pma_regions : register) ∈ D ∪ sda_Dro.
Proof. rewrite /sda_Dro. set_solver. Qed.
Lemma sda_in_pcfg_D (D : gset register) : (pmpcfg_n : register) ∈ D ∪ sda_Dro.
Proof. rewrite /sda_Dro. set_solver. Qed.
Lemma sda_in_paddr_D (D : gset register) : (pmpaddr_n : register) ∈ D ∪ sda_Dro.
Proof. rewrite /sda_Dro. set_solver. Qed.
Lemma sda_in_htif_D (D : gset register) : (htif_tohost_base : register) ∈ D ∪ sda_Dro.
Proof. rewrite /sda_Dro. set_solver. Qed.
Lemma sda_in_misa_D (D : gset register) : (misa : register) ∈ D ∪ sda_Dro.
Proof. rewrite /sda_Dro. set_solver. Qed.

Local Ltac sdadf :=
  unfold sda_Df;
  repeat first [ rewrite decide_True; [reflexivity|reflexivity]
               | rewrite decide_False; [|discriminate] ];
  reflexivity.
Lemma sda_Df_misa dq : sda_Df dq misa = DfracDiscarded. Proof. sdadf. Qed.
Lemma sda_Df_pma dq : sda_Df dq pma_regions = DfracDiscarded. Proof. sdadf. Qed.
Lemma sda_Df_htif dq : sda_Df dq htif_tohost_base = DfracDiscarded.
Proof. sdadf. Qed.
Lemma sda_Df_satp dq : sda_Df dq satp = DfracOwn 1. Proof. sdadf. Qed.
Lemma sda_Df_pcfg dq : sda_Df dq pmpcfg_n = DfracOwn 1. Proof. sdadf. Qed.
Lemma sda_Df_paddr dq : sda_Df dq pmpaddr_n = DfracOwn 1. Proof. sdadf. Qed.
Lemma sda_Df_mst dq : sda_Df dq mstatus = dq. Proof. sdadf. Qed.
Lemma sda_Df_priv dq : sda_Df dq cur_privilege = dq. Proof. sdadf. Qed.
Lemma sda_Df_menv dq : sda_Df dq menvcfg = dq. Proof. sdadf. Qed.

(* THE TLB WRITE-BACK, as a frame transport: the walk's landing file is
   [register_set tlb tv (sda_rs … tlbv)], which is not syntactically the
   tower at [tv] but agrees with it on all ten cells. *)
Lemma sda_set_tlb (mst0 menv0 satp0 : SailStdpp.Values.mword 64)
    (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
    (paddr : type_of_register pmpaddr_n)
    (tlbv tv : type_of_register tlb) :
  reg_agree_on (sda_Drw ∪ sda_Dro)
    (register_set tlb tv (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv))
    (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tv).
Proof.
  intros r Hr. rewrite /sda_Drw /sda_Dro in Hr.
  repeat (apply elem_of_union in Hr as [Hr|Hr]);
    apply elem_of_singleton in Hr; subst r;
    first [ rewrite register_lookup_set | sdtm ];
    rewrite ?sda_rs_tlb ?sda_rs_mst ?sda_rs_priv ?sda_rs_menv ?sda_rs_satp
            ?sda_rs_pma ?sda_rs_pcfg ?sda_rs_paddr ?sda_rs_htif ?sda_rs_misa;
    reflexivity.
Qed.

Section SdaFrames.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma sda_rw_ext (rs rs' : regstate) :
    reg_agree_on (sda_Drw ∪ sda_Dro) rs rs' ->
    hreg_frame rs sda_Drw -∗ (hreg_frame rs' sda_Drw : iProp Σ).
  Proof.
    intros Hag. rewrite (hreg_frame_ext _ _ sda_Drw
      (reg_agree_mono (sda_Drw ∪ sda_Dro) sda_Drw _ _ ltac:(set_solver) Hag)).
    iIntros "H". iExact "H".
  Qed.

  (* the write-frame extension at an ARBITRARY data write set below
     [sda_Drw] -- what a leaf handed an abstract set by
     [WpIntrInv.sda_slot_acc] normalises its landing file with.  [sda_ro_ext]
     needs no twin: it never mentions the write set. *)
  Lemma sda_rw_ext_D (D : gset register) (rs rs' : regstate) :
    D ⊆ sda_Drw ->
    reg_agree_on (sda_Drw ∪ sda_Dro) rs rs' ->
    hreg_frame rs D -∗ (hreg_frame rs' D : iProp Σ).
  Proof.
    intros Hsub Hag.
    rewrite (hreg_frame_ext _ _ D
      (reg_agree_mono (sda_Drw ∪ sda_Dro) D _ _
         (transitivity Hsub (union_subseteq_l sda_Drw sda_Dro)) Hag)).
    iIntros "H". iExact "H".
  Qed.

  Lemma sda_ro_ext (Df : register -> dfrac) (rs rs' : regstate) :
    reg_agree_on (sda_Drw ∪ sda_Dro) rs rs' ->
    hreg_frame_ro Df rs sda_Dro -∗ (hreg_frame_ro Df rs' sda_Dro : iProp Σ).
  Proof.
    intros Hag. rewrite (hreg_frame_ro_ext Df _ _ sda_Dro
      (reg_agree_mono (sda_Drw ∪ sda_Dro) sda_Dro _ _ ltac:(set_solver) Hag)).
    iIntros "H". iExact "H".
  Qed.

  (* THE CELL <-> FRAME BRIDGE.  Ten cells in, the frame out; the three
     [hw_config] pins are persistent, so the elimination hands back only the
     seven the leaf owns. *)
  Lemma sda_frames (dq : dfrac) (mst0 menv0 satp0 : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (tlbv : type_of_register tlb) :
    (hreg_frame (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) sda_Drw ∗
     hreg_frame_ro (sda_Df dq)
       (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) sda_Dro : iProp Σ)
    ⊣⊢ (reg_pointsto tlb (DfracOwn 1) tlbv ∗
        reg_pointsto mstatus dq mst0 ∗
        reg_pointsto cur_privilege dq Supervisor ∗
        reg_pointsto menvcfg dq menv0 ∗
        reg_pointsto satp (DfracOwn 1) satp0 ∗
        reg_pointsto pma_regions DfracDiscarded pmar0 ∗
        reg_pointsto pmpcfg_n (DfracOwn 1) pcfg ∗
        reg_pointsto pmpaddr_n (DfracOwn 1) paddr ∗
        reg_pointsto htif_tohost_base DfracDiscarded None ∗
        reg_pointsto misa DfracDiscarded MISA_C).
  Proof.
    rewrite /hreg_frame /hreg_frame_ro /sda_Drw /sda_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite sda_rs_tlb sda_rs_mst sda_rs_priv sda_rs_menv sda_rs_satp
            sda_rs_pma sda_rs_pcfg sda_rs_paddr sda_rs_htif sda_rs_misa.
    rewrite sda_Df_misa sda_Df_pma sda_Df_htif sda_Df_satp sda_Df_pcfg
            sda_Df_paddr sda_Df_mst sda_Df_priv sda_Df_menv.
    by rewrite !bi.sep_assoc.
  Qed.

  (* the BARE twin: [sda_Drwb] is empty, so the write frame contributes
     nothing and the tlb cell is simply absent.  Everything else is
     [sda_frames] verbatim -- which is what makes one combinator able to hand
     either frame to a body that never looks at the set
     ([WpIntrInv.sie_cap_to_frames]). *)
  Lemma sda_frames_b (dq : dfrac) (mst0 menv0 satp0 : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (tlbv : type_of_register tlb) :
    (hreg_frame (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) sda_Drwb ∗
     hreg_frame_ro (sda_Df dq)
       (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) sda_Dro : iProp Σ)
    ⊣⊢ (reg_pointsto mstatus dq mst0 ∗
        reg_pointsto cur_privilege dq Supervisor ∗
        reg_pointsto menvcfg dq menv0 ∗
        reg_pointsto satp (DfracOwn 1) satp0 ∗
        reg_pointsto pma_regions DfracDiscarded pmar0 ∗
        reg_pointsto pmpcfg_n (DfracOwn 1) pcfg ∗
        reg_pointsto pmpaddr_n (DfracOwn 1) paddr ∗
        reg_pointsto htif_tohost_base DfracDiscarded None ∗
        reg_pointsto misa DfracDiscarded MISA_C).
  Proof.
    rewrite /hreg_frame /hreg_frame_ro /sda_Drwb /sda_Dro.
    rewrite big_sepS_empty left_id.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite sda_rs_mst sda_rs_priv sda_rs_menv sda_rs_satp
            sda_rs_pma sda_rs_pcfg sda_rs_paddr sda_rs_htif sda_rs_misa.
    rewrite sda_Df_misa sda_Df_pma sda_Df_htif sda_Df_satp sda_Df_pcfg
            sda_Df_paddr sda_Df_mst sda_Df_priv sda_Df_menv.
    by rewrite !bi.sep_assoc.
  Qed.

  (* the two DIRECTED forms (a [⊣⊢] rewrite inside a proofmode goal is both
     awkward and, per optimization.md, occasionally very slow) *)
  Lemma sda_frames_in (dq : dfrac)
      (mst0 menv0 satp0 : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (tlbv : type_of_register tlb) :
    reg_pointsto tlb (DfracOwn 1) tlbv -∗
    reg_pointsto mstatus dq mst0 -∗
    reg_pointsto cur_privilege dq Supervisor -∗
    reg_pointsto menvcfg dq menv0 -∗
    reg_pointsto satp (DfracOwn 1) satp0 -∗
    reg_pointsto pma_regions DfracDiscarded pmar0 -∗
    reg_pointsto pmpcfg_n (DfracOwn 1) pcfg -∗
    reg_pointsto pmpaddr_n (DfracOwn 1) paddr -∗
    reg_pointsto htif_tohost_base DfracDiscarded None -∗
    reg_pointsto misa DfracDiscarded MISA_C -∗
    (hreg_frame (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) sda_Drw ∗
     hreg_frame_ro (sda_Df dq)
       (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) sda_Dro : iProp Σ).
  Proof.
    iIntros "H1 H2 H3 H4 H5 H6 H7 H8 H9 H10". rewrite sda_frames. iFrame.
  Qed.

  Lemma sda_frames_out (dq : dfrac)
      (mst0 menv0 satp0 : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (tlbv : type_of_register tlb) :
    (hreg_frame (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) sda_Drw ∗
     hreg_frame_ro (sda_Df dq)
       (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) sda_Dro : iProp Σ) -∗
    (reg_pointsto tlb (DfracOwn 1) tlbv ∗
     reg_pointsto mstatus dq mst0 ∗
     reg_pointsto cur_privilege dq Supervisor ∗
     reg_pointsto menvcfg dq menv0 ∗
     reg_pointsto satp (DfracOwn 1) satp0 ∗
     reg_pointsto pma_regions DfracDiscarded pmar0 ∗
     reg_pointsto pmpcfg_n (DfracOwn 1) pcfg ∗
     reg_pointsto pmpaddr_n (DfracOwn 1) paddr ∗
     reg_pointsto htif_tohost_base DfracDiscarded None ∗
     reg_pointsto misa DfracDiscarded MISA_C).
  Proof. rewrite sda_frames. iIntros "H". iExact "H". Qed.

  (* the BARE in/out pair: [sda_frames_b] as wands, and with no tlb cell. *)
  Lemma sda_frames_in_b (dq : dfrac)
      (mst0 menv0 satp0 : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (tlbv : type_of_register tlb) :
    reg_pointsto mstatus dq mst0 -∗
    reg_pointsto cur_privilege dq Supervisor -∗
    reg_pointsto menvcfg dq menv0 -∗
    reg_pointsto satp (DfracOwn 1) satp0 -∗
    reg_pointsto pma_regions DfracDiscarded pmar0 -∗
    reg_pointsto pmpcfg_n (DfracOwn 1) pcfg -∗
    reg_pointsto pmpaddr_n (DfracOwn 1) paddr -∗
    reg_pointsto htif_tohost_base DfracDiscarded None -∗
    reg_pointsto misa DfracDiscarded MISA_C -∗
    (hreg_frame (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) sda_Drwb ∗
     hreg_frame_ro (sda_Df dq)
       (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) sda_Dro : iProp Σ).
  Proof.
    iIntros "H1 H2 H3 H4 H5 H6 H7 H8 H9". rewrite sda_frames_b. iFrame.
  Qed.

  Lemma sda_frames_out_b (dq : dfrac)
      (mst0 menv0 satp0 : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (tlbv : type_of_register tlb) :
    (hreg_frame (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) sda_Drwb ∗
     hreg_frame_ro (sda_Df dq)
       (sda_rs mst0 menv0 satp0 pmar0 pcfg paddr tlbv) sda_Dro : iProp Σ) -∗
    (reg_pointsto mstatus dq mst0 ∗
     reg_pointsto cur_privilege dq Supervisor ∗
     reg_pointsto menvcfg dq menv0 ∗
     reg_pointsto satp (DfracOwn 1) satp0 ∗
     reg_pointsto pma_regions DfracDiscarded pmar0 ∗
     reg_pointsto pmpcfg_n (DfracOwn 1) pcfg ∗
     reg_pointsto pmpaddr_n (DfracOwn 1) paddr ∗
     reg_pointsto htif_tohost_base DfracDiscarded None ∗
     reg_pointsto misa DfracDiscarded MISA_C).
  Proof. rewrite sda_frames_b. iIntros "H". iExact "H". Qed.

End SdaFrames.


(* ===================================================================== *)
(* §4  THE BRANCH WALKS.                                                  *)
(*                                                                       *)
(* A branch is the one instruction family that writes NO gpr: the         *)
(* fall-through arm is two register reads and a [Ret], and the taken arm   *)
(* adds a PC read and a nextPC write.  Both are privilege- and            *)
(* bundle-free.  (The same three walks exist in [WpSconfEngine]; that file *)
(* sits on the sconf wrapper and therefore on [IntrDefs], which this tier  *)
(* must not depend on -- so they are cloned here under [sb_]/[swp_sb_]     *)
(* names.  Fold the two copies together when the sconf side settles.)     *)
(* ===================================================================== *)
Notation sb_btype_body imm rs2 rs1 cmp :=
  (Defs.bind
     (Defs.bind (rX_bits (Regidx rs1))
        (fun a => Defs.bind (rX_bits (Regidx rs2))
                    (fun c => returnM (cmp a c))))
     (fun taken : bool =>
        if taken
        then Defs.bind (Defs.read_reg (R_bitvector_64 PC))
               (fun w => jump_to (add_vec w (sign_extend' 64 imm)))
        else returnM RETIRE_SUCCESS)).

(* the target's bit 0, spelled as the MODEL spells it (design §5 item 1(g)) *)
Local Notation sb_zerobit :=
  (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 1)
     (BinaryString.Raw.to_N "0" 0%N)).

Definition sb_Drw : gset register := {[ (R_bitvector_64 nextPC : register) ]}.
Definition sb_Dro : gset register := {[ (misa : register) ]}.
Definition sb_Df : register -> dfrac := fun _ => DfracDiscarded.
Definition sb_rs (npc0 : SailStdpp.Values.mword 64) : regstate :=
  register_set (R_bitvector_64 nextPC) npc0
    (register_set misa MISA_C init_regstate).

Lemma sb_disj : sb_Drw ## sb_Dro.
Proof. rewrite /sb_Drw /sb_Dro. set_solver. Qed.
Lemma sb_w_nPC : (R_bitvector_64 nextPC : register) ∈ sb_Drw.
Proof. rewrite /sb_Drw. set_solver. Qed.
Lemma sb_in_misa : (misa : register) ∈ sb_Drw ∪ sb_Dro.
Proof. rewrite /sb_Drw /sb_Dro. set_solver. Qed.

Lemma sb_rs_nPC npc0 :
  register_lookup (R_bitvector_64 nextPC) (sb_rs npc0) = npc0.
Proof. rewrite /sb_rs. by rewrite register_lookup_set. Qed.
Lemma sb_rs_misa npc0 : register_lookup misa (sb_rs npc0) = MISA_C.
Proof.
  rewrite /sb_rs.
  etransitivity; [apply irrelevant_register_set; vm_compute; reflexivity|].
  apply register_lookup_set.
Qed.

Lemma sb_set_agree (npc0 target : SailStdpp.Values.mword 64) :
  reg_agree_on (sb_Drw ∪ sb_Dro)
    (register_set (R_bitvector_64 nextPC) target (sb_rs npc0)) (sb_rs target).
Proof.
  intros r Hr. rewrite /sb_Drw /sb_Dro in Hr.
  apply elem_of_union in Hr as [Hr|Hr]; apply elem_of_singleton in Hr; subst r.
  - etransitivity; [apply register_lookup_set|]. symmetry. apply sb_rs_nPC.
  - etransitivity;
      [apply irrelevant_register_set; vm_compute; reflexivity|].
    etransitivity; [apply sb_rs_misa|]. symmetry. apply sb_rs_misa.
Qed.

Section SbBranch.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the ONE cell a jump needs out of the persistent config bundle *)
  Lemma sb_hw_config_misa : hw_config -∗ misa ↦ᵣ□ MISA_C.
  Proof.
    iIntros "H". iDestruct "H" as (misa0 mseccfg0 pmar0 elp0)
      "(Hmisa & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hv & _)".
    rewrite Hv. iExact "Hmisa".
  Qed.

  Lemma sb_frames (npc0 : SailStdpp.Values.mword 64) :
    (hreg_frame (sb_rs npc0) sb_Drw ∗
     hreg_frame_ro sb_Df (sb_rs npc0) sb_Dro : iProp Σ)
    ⊣⊢ ((R_bitvector_64 nextPC) ↦ᵣ npc0 ∗ misa ↦ᵣ□ MISA_C).
  Proof.
    rewrite /hreg_frame /hreg_frame_ro /sb_Drw /sb_Dro.
    rewrite !big_sepS_singleton.
    by rewrite sb_rs_nPC sb_rs_misa.
  Qed.

  Lemma swp_sb_jump (target npc0 : SailStdpp.Values.mword 64) :
    eq_vec (access_vec_dec target 0) sb_zerobit = true ->
    gen_cert -∗
    (R_bitvector_64 nextPC) ↦ᵣ npc0 -∗
    misa ↦ᵣ□ MISA_C -∗
    swp (jump_to target)
      (fun r => ⌜r = RETIRE_SUCCESS⌝ ∗
                (R_bitvector_64 nextPC) ↦ᵣ target ∗ misa ↦ᵣ□ MISA_C).
  Proof.
    intros Halign. iIntros "#Hcert HnPC Hmisa".
    iAssert (hreg_frame (sb_rs npc0) sb_Drw ∗
             hreg_frame_ro sb_Df (sb_rs npc0) sb_Dro)%I with "[HnPC Hmisa]"
      as "[Hrw Hro]".
    { rewrite sb_frames. iFrame. }
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_hfrun 6 sb_Drw sb_Dro sb_Df (sb_rs npc0)
                   (register_set (R_bitvector_64 nextPC) target (sb_rs npc0))
                   (jump_to target) RETIRE_SUCCESS sb_disj
                   (hfrun_jump_to_zca (sb_Drw ∪ sb_Dro) sb_Drw (sb_rs npc0)
                      target sb_in_misa sb_w_nPC Halign
                      ltac:(rewrite sb_rs_misa; vm_compute; reflexivity))
                   with "Hcert Hrw Hro") ].
    iIntros (r) "(-> & Hrw & Hro)".
    rewrite (hreg_frame_ext _ (sb_rs target) sb_Drw
               (reg_agree_l _ _ _ _ (sb_set_agree npc0 target))).
    rewrite (hreg_frame_ro_ext sb_Df _ (sb_rs target) sb_Dro
               (reg_agree_r _ _ _ _ (sb_set_agree npc0 target))).
    iSplitR; [done|]. rewrite -sb_frames. iFrame.
  Qed.

  Lemma swp_sb_cmp (rs2 rs1 : SailStdpp.Values.mword 5) (m : regfile)
      (cmp : SailStdpp.Values.mword 64 -> SailStdpp.Values.mword 64 -> bool) :
    gen_cert -∗ gpr_file m -∗
    swp (Defs.bind (rX_bits (Regidx rs1))
           (fun a => Defs.bind (rX_bits (Regidx rs2))
                       (fun c => returnM (cmp a c))))
      (fun v => ⌜v = cmp (m !!! Regidx rs1) (m !!! Regidx rs2)⌝ ∗ gpr_file m).
  Proof.
    iIntros "#Hcert Hf".
    iApply (swp_bind_use (rX_bits (Regidx rs1)) _ _ _ with "[Hf] [-]").
    { iApply (swp_rX_file rs1 m with "Hcert Hf"). }
    iIntros (v1) "[-> Hf]".
    iApply (swp_bind_use (rX_bits (Regidx rs2)) _ _ _ with "[Hf] [-]").
    { iApply (swp_rX_file rs2 m with "Hcert Hf"). }
    iIntros (v2) "[-> Hf]".
    iApply swp_ret. by iFrame.
  Qed.

  Lemma swp_sb_BTYPE_fall (imm : SailStdpp.Values.mword 13)
      (rs2 rs1 : SailStdpp.Values.mword 5) (m : regfile)
      (mo : M ExecutionResult)
      (cmp : SailStdpp.Values.mword 64 -> SailStdpp.Values.mword 64 -> bool) :
    mo = sb_btype_body imm rs2 rs1 cmp ->
    cmp (m !!! Regidx rs1) (m !!! Regidx rs2) = false ->
    gen_cert -∗ gpr_file m -∗
    swp mo (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗ gpr_file m).
  Proof.
    intros Hred Hcmp. iIntros "#Hcert Hf". rewrite Hred.
    iApply (swp_bind_use _ _
              (fun v => ⌜v = cmp (m !!! Regidx rs1) (m !!! Regidx rs2)⌝ ∗
                        gpr_file m)%I _ with "[Hf] [-]").
    { iApply (swp_sb_cmp rs2 rs1 m cmp with "Hcert Hf"). }
    iIntros (v) "[-> Hf]". rewrite Hcmp.
    iApply swp_ret. by iFrame.
  Qed.

  Lemma swp_sb_BTYPE_taken (imm : SailStdpp.Values.mword 13)
      (rs2 rs1 : SailStdpp.Values.mword 5) (m : regfile)
      (mo : M ExecutionResult)
      (pc npc0 : SailStdpp.Values.mword 64)
      (cmp : SailStdpp.Values.mword 64 -> SailStdpp.Values.mword 64 -> bool) :
    mo = sb_btype_body imm rs2 rs1 cmp ->
    cmp (m !!! Regidx rs1) (m !!! Regidx rs2) = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) sb_zerobit
      = true ->
    gen_cert -∗ gpr_file m -∗
    (R_bitvector_64 PC) ↦ᵣ pc -∗
    (R_bitvector_64 nextPC) ↦ᵣ npc0 -∗
    misa ↦ᵣ□ MISA_C -∗
    swp mo (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗ gpr_file m ∗
              (R_bitvector_64 PC) ↦ᵣ pc ∗
              (R_bitvector_64 nextPC) ↦ᵣ (add_vec pc (sign_extend' 64 imm)) ∗
              misa ↦ᵣ□ MISA_C).
  Proof.
    intros Hred Hcmp Halign. iIntros "#Hcert Hf HPC HnPC Hmisa". rewrite Hred.
    iApply (swp_bind_use _ _
              (fun v => ⌜v = cmp (m !!! Regidx rs1) (m !!! Regidx rs2)⌝ ∗
                        gpr_file m)%I _ with "[Hf] [-]").
    { iApply (swp_sb_cmp rs2 rs1 m cmp with "Hcert Hf"). }
    iIntros (v) "[-> Hf]". rewrite Hcmp.
    iApply (swp_bind_use (Defs.read_reg (R_bitvector_64 PC)) _
              (fun w => ⌜w = pc⌝ ∗ (R_bitvector_64 PC) ↦ᵣ pc)%I _
              with "[HPC] [-]").
    { iApply (swp_read_reg_cell (R_bitvector_64 PC) pc with "Hcert HPC"). }
    iIntros (w) "[-> HPC]".
    iApply (swp_mono with "[Hf HPC] [HnPC Hmisa]");
      [| iApply (swp_sb_jump (add_vec pc (sign_extend' 64 imm)) npc0 Halign
                   with "Hcert HnPC Hmisa") ].
    iIntros (r) "(-> & HnPC & Hmisa)". iFrame. done.
  Qed.

End SbBranch.


(* ===================================================================== *)
(* §5  THE CONTROL-TRANSFER WALKS (JAL and the JALR return).              *)
(*                                                                       *)
(* Cloned from [WpSconfEngine]'s for the reason §4 records -- that file    *)
(* sits on IntrDefs and does not currently build.  [WpMmodeJump]'s twins   *)
(* pin cur_privilege to Machine in two places, so they cannot serve; the   *)
(* only real S-mode difference is [update_elp_state], which reads the      *)
(* privilege through [currentlyEnabled Ext_Zicfilp] and is bridged at      *)
(* [dstateS].  Four cells: nextPC written, cur_privilege/menvcfg/misa read.*)
(* ===================================================================== *)
Lemma cj_ds_sub (D : gset register) :
  (cur_privilege : register) ∈ D -> (menvcfg : register) ∈ D ->
  (misa : register) ∈ D ->
  forall r : register, D_s r = true -> r ∈ D.
Proof.
  intros H1 H2 H3 r Hr. unfold D_s in Hr.
  apply orb_prop in Hr as [Hr|Hr];
    [apply orb_prop in Hr as [Hr|Hr]|];
    apply register_beq_eq in Hr; subst r; assumption.
Qed.

Lemma hval_cj_update_elp (D Drw : gset register) (rs : regstate)
    (ra : SailStdpp.Values.mword 5) :
  (cur_privilege : register) ∈ D -> (menvcfg : register) ∈ D ->
  (misa : register) ∈ D ->
  register_lookup cur_privilege rs = Supervisor ->
  register_lookup menvcfg rs = MENVCFG_S ->
  register_lookup misa rs = MISA_C ->
  hval D Drw rs (update_elp_state (Regidx ra)) tt rs.
Proof.
  intros HD1 HD2 HD3 Hp Hme Hm.
  apply (hval_of_goodb D_s D Drw _ dstateS rs tt
           (cj_ds_sub D HD1 HD2 HD3)
           (agree_s (MState rs ∅ dev0_state) Hp Hme Hm)).
  - vm_compute. reflexivity.
  - unfold update_elp_state.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_cE_zicfilp_false_S dstateS
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))).
    cbn match. apply exec_returnm.
Qed.

Definition cj_Drw : gset register := {[ (R_bitvector_64 nextPC : register) ]}.
Definition cj_Dro : gset register :=
  {[ (cur_privilege : register); (menvcfg : register); (misa : register) ]}.
(* DFRAC-PARAMETRIC: the S-mode config cells arrive at whatever fraction the
   wrapper lends, and the JALR return only READS them. *)
Definition cj_Df (dq : dfrac) : register -> dfrac := fun r =>
  if decide (r = (misa : register)) then DfracDiscarded else dq.
Definition cj_rs (npc0 : SailStdpp.Values.mword 64) : regstate :=
  register_set (R_bitvector_64 nextPC) npc0
    (register_set misa MISA_C
       (register_set menvcfg MENVCFG_S
          (register_set cur_privilege Supervisor init_regstate))).

Lemma cj_disj : cj_Drw ## cj_Dro.
Proof. rewrite /cj_Drw /cj_Dro. set_solver. Qed.
Lemma cj_in_priv : (cur_privilege : register) ∈ cj_Drw ∪ cj_Dro.
Proof. rewrite /cj_Drw /cj_Dro. set_solver. Qed.
Lemma cj_in_menv : (menvcfg : register) ∈ cj_Drw ∪ cj_Dro.
Proof. rewrite /cj_Drw /cj_Dro. set_solver. Qed.
Lemma cj_in_misa : (misa : register) ∈ cj_Drw ∪ cj_Dro.
Proof. rewrite /cj_Drw /cj_Dro. set_solver. Qed.

Ltac sjeskip :=
  etransitivity; [apply irrelevant_register_set; vm_compute; reflexivity|].

Lemma cj_rs_nPC npc0 :
  register_lookup (R_bitvector_64 nextPC) (cj_rs npc0) = npc0.
Proof. rewrite /cj_rs. by rewrite register_lookup_set. Qed.
Lemma cj_rs_misa npc0 : register_lookup misa (cj_rs npc0) = MISA_C.
Proof. rewrite /cj_rs. sjeskip. apply register_lookup_set. Qed.
Lemma cj_rs_menv npc0 : register_lookup menvcfg (cj_rs npc0) = MENVCFG_S.
Proof. rewrite /cj_rs. sjeskip. sjeskip. apply register_lookup_set. Qed.
Lemma cj_rs_priv npc0 :
  register_lookup cur_privilege (cj_rs npc0) = Supervisor.
Proof. rewrite /cj_rs. sjeskip. sjeskip. sjeskip. apply register_lookup_set. Qed.

Ltac sjedf :=
  unfold cj_Df;
  repeat first [ rewrite decide_True; [reflexivity|reflexivity]
               | rewrite decide_False; [|discriminate] ];
  reflexivity.
Lemma cj_Df_misa dq : cj_Df dq misa = DfracDiscarded.
Proof. sjedf. Qed.
Lemma cj_Df_menv dq : cj_Df dq menvcfg = dq.
Proof. sjedf. Qed.
Lemma cj_Df_priv dq : cj_Df dq cur_privilege = dq.
Proof. sjedf. Qed.

Section CjCtl.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma cj_frames (dq : dfrac) (npc0 : SailStdpp.Values.mword 64) :
    (hreg_frame (cj_rs npc0) cj_Drw ∗
     hreg_frame_ro (cj_Df dq) (cj_rs npc0) cj_Dro : iProp Σ)
    ⊣⊢ ((R_bitvector_64 nextPC) ↦ᵣ npc0 ∗
        cur_privilege ↦ᵣ{ dq } Supervisor ∗ menvcfg ↦ᵣ{ dq } MENVCFG_S ∗
        misa ↦ᵣ□ MISA_C).
  Proof.
    rewrite /hreg_frame /hreg_frame_ro /cj_Drw /cj_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite cj_rs_nPC cj_rs_priv cj_rs_menv cj_rs_misa.
    rewrite cj_Df_priv cj_Df_menv cj_Df_misa.
    by rewrite !bi.sep_assoc.
  Qed.

  Lemma swp_cj_update_elp (dq : dfrac) (ra : SailStdpp.Values.mword 5)
      (npc0 : SailStdpp.Values.mword 64) :
    gen_cert -∗
    (R_bitvector_64 nextPC) ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    menvcfg ↦ᵣ{ dq } MENVCFG_S -∗
    misa ↦ᵣ□ MISA_C -∗
    swp (update_elp_state (Regidx ra))
      (fun _ => (R_bitvector_64 nextPC) ↦ᵣ npc0 ∗
                cur_privilege ↦ᵣ{ dq } Supervisor ∗
                menvcfg ↦ᵣ{ dq } MENVCFG_S ∗
                misa ↦ᵣ□ MISA_C).
  Proof.
    iIntros "#Hcert HnPC Hpriv Hmenv Hmisa".
    iAssert (hreg_frame (cj_rs npc0) cj_Drw ∗
             hreg_frame_ro (cj_Df dq) (cj_rs npc0) cj_Dro)%I
      with "[HnPC Hpriv Hmenv Hmisa]" as "[Hrw Hro]".
    { rewrite cj_frames. iFrame. }
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_span cj_Drw cj_Dro (cj_Df dq) (cj_rs npc0) (cj_rs npc0)
                   (update_elp_state (Regidx ra)) tt cj_disj
                   (hval_cj_update_elp (cj_Drw ∪ cj_Dro) cj_Drw
                      (cj_rs npc0) ra cj_in_priv cj_in_menv cj_in_misa
                      (cj_rs_priv npc0) (cj_rs_menv npc0) (cj_rs_misa npc0))
                   with "Hcert Hrw Hro") ].
    iIntros (u) "(_ & Hrw & Hro)".
    iAssert ((R_bitvector_64 nextPC) ↦ᵣ npc0 ∗
             cur_privilege ↦ᵣ{ dq } Supervisor ∗
             menvcfg ↦ᵣ{ dq } MENVCFG_S ∗ misa ↦ᵣ□ MISA_C)%I
      with "[Hrw Hro]" as "H".
    { rewrite -cj_frames. iFrame. }
    iExact "H".
  Qed.

  Lemma swp_cj_JAL (imm : SailStdpp.Values.mword 21)
      (rd : SailStdpp.Values.mword 5) (m : regfile)
      (pc npc0 : SailStdpp.Values.mword 64) :
    uint rd <> 0 ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) sb_zerobit = true ->
    gen_cert -∗ gpr_file m -∗
    (R_bitvector_64 PC) ↦ᵣ pc -∗
    (R_bitvector_64 nextPC) ↦ᵣ npc0 -∗
    misa ↦ᵣ□ MISA_C -∗
    swp (execute (JAL (imm, Regidx rd)))
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                gpr_file (<[Regidx rd := regval_into_reg npc0]> m) ∗
                (R_bitvector_64 PC) ↦ᵣ pc ∗
                (R_bitvector_64 nextPC) ↦ᵣ (add_vec pc (sign_extend' 64 imm)) ∗
                misa ↦ᵣ□ MISA_C).
  Proof.
    intros Hrd Halign. iIntros "#Hcert Hf HPC HnPC Hmisa".
    change (execute (JAL (imm, Regidx rd))) with (execute_JAL imm (Regidx rd)).
    unfold execute_JAL. cbn match.
    iApply (swp_bind_use (get_next_pc tt) _
              (fun link => ⌜link = npc0⌝ ∗
                 (R_bitvector_64 nextPC) ↦ᵣ npc0)%I _ with "[HnPC] [-]").
    { unfold get_next_pc.
      iApply (swp_read_reg_cell (R_bitvector_64 nextPC) npc0 with "Hcert HnPC"). }
    iIntros (link) "[-> HnPC]".
    iApply (swp_bind_use (Defs.read_reg (R_bitvector_64 PC)) _
              (fun w => ⌜w = pc⌝ ∗ (R_bitvector_64 PC) ↦ᵣ pc)%I _
              with "[HPC] [-]").
    { iApply (swp_read_reg_cell (R_bitvector_64 PC) pc with "Hcert HPC"). }
    iIntros (w0) "[-> HPC]".
    iApply (swp_bind_use _ _ _ _ with "[HnPC Hmisa] [-]").
    { iApply (swp_sb_jump _ npc0 Halign with "Hcert HnPC Hmisa"). }
    iIntros (r) "(-> & HnPC & Hmisa)". cbn match.
    iApply (swp_bind0_use _ _ _ _ with "[Hf] [-]").
    { iApply (swp_wX_file rd m npc0 Hrd with "Hcert Hf"). }
    iIntros (u) "Hf". iApply swp_ret. iSplitR; [done|]. iFrame.
  Qed.

  Lemma swp_cj_JALR_ret (dq : dfrac) (ra rdz : SailStdpp.Values.mword 5)
      (m : regfile) (npc0 : SailStdpp.Values.mword 64) :
    uint rdz = 0 ->
    gen_cert -∗ gpr_file m -∗
    (R_bitvector_64 nextPC) ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    menvcfg ↦ᵣ{ dq } MENVCFG_S -∗
    misa ↦ᵣ□ MISA_C -∗
    swp (execute (JALR (zeros' 12, Regidx ra, Regidx rdz)))
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗ gpr_file m ∗
                (R_bitvector_64 nextPC) ↦ᵣ (ret_pc (m !!! Regidx ra)) ∗
                cur_privilege ↦ᵣ{ dq } Supervisor ∗
                menvcfg ↦ᵣ{ dq } MENVCFG_S ∗
                misa ↦ᵣ□ MISA_C).
  Proof.
    intros Hrdz.
    (* the alignment side condition is [ret_pc]'s own construction, and it has
       to be POSED rather than passed as an [ltac:] inside the application:
       inside one, the goal still carries the application's evars. *)
    assert (Halign : eq_vec (access_vec_dec
              (update_vec_dec
                 (add_vec (m !!! Regidx ra) (sign_extend' 64 (zeros' 12))) 0
                 sb_zerobit) 0) sb_zerobit = true)
      by (rewrite ret_pc_jalr; apply ret_pc_aligned).
    iIntros "#Hcert Hf HnPC Hpriv Hmenv Hmisa".
    change (execute (JALR (zeros' 12, Regidx ra, Regidx rdz)))
      with (execute_JALR (zeros' 12) (Regidx ra) (Regidx rdz)).
    unfold execute_JALR. cbn match.
    iApply (swp_bind_use
              (Defs.bind0 (update_elp_state (Regidx ra)) (get_next_pc tt)) _
              (fun link => ⌜link = npc0⌝ ∗
                 (R_bitvector_64 nextPC) ↦ᵣ npc0 ∗
                 cur_privilege ↦ᵣ{ dq } Supervisor ∗
                 menvcfg ↦ᵣ{ dq } MENVCFG_S ∗
                 misa ↦ᵣ□ MISA_C)%I _
              with "[HnPC Hpriv Hmenv Hmisa] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ => (R_bitvector_64 nextPC) ↦ᵣ npc0 ∗
                   cur_privilege ↦ᵣ{ dq } Supervisor ∗
                   menvcfg ↦ᵣ{ dq } MENVCFG_S ∗
                   misa ↦ᵣ□ MISA_C)%I _
                with "[HnPC Hpriv Hmenv Hmisa] [-]").
      { iApply (swp_cj_update_elp dq ra npc0
                  with "Hcert HnPC Hpriv Hmenv Hmisa"). }
      iIntros (u) "(HnPC & Hpriv & Hmenv & Hmisa)".
      unfold get_next_pc.
      iApply (swp_mono with "[Hpriv Hmenv Hmisa] [-]");
        [| iApply (swp_read_reg_cell (R_bitvector_64 nextPC) npc0
                     with "Hcert HnPC") ].
      iIntros (link) "[-> HnPC]". iSplitR; [done|]. iFrame. }
    iIntros (link) "(-> & HnPC & Hpriv & Hmenv & Hmisa)".
    iApply (swp_bind_use (rX_bits (Regidx ra)) _ _ _ with "[Hf] [-]").
    { iApply (swp_rX_file ra m with "Hcert Hf"). }
    iIntros (w) "[-> Hf]".
    iApply (swp_bind_use _ _ _ _ with "[HnPC Hmisa] [-]").
    { iApply (swp_sb_jump _ npc0 Halign with "Hcert HnPC Hmisa"). }
    iIntros (r) "(-> & HnPC & Hmisa)". cbn match.
    iApply (swp_bind0_use _ _ (fun _ => gpr_file m)%I _ with "[Hf] [-]").
    { iApply (swp_wX_zero rdz _ (gpr_file m) Hrdz with "Hf"). }
    iIntros (u2) "Hf". iApply swp_ret. rewrite ret_pc_jalr.
    iSplitR; [done|]. iFrame.
  Qed.

End CjCtl.
