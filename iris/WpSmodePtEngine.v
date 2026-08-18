(* WpSmodePtEngine.v -- the REGIME-GENERIC S-mode instruction engines at the
   per-node ([swp]) layer, and the one thing the [sr_inv R] wrappers still
   owe their callers.

   WHY THIS FILE EXISTS.  [SmodeCorePt]'s wrappers
   ([wp_instr_s_config_sr] / [wp_instr_s_sr]) take the FETCH TRANSLATION
   ([SmodeCorePt.spt_fetch_tr]) as a premise and hand it straight up.  A
   regime-generic LEAF carries only [SRegime.sr_inv R], so it has nothing to
   pay that premise with -- and it cannot be produced from
   [SRegime.sr_swp_translate] alone either, because that field's last two
   premises are REGIME-SPECIFIC:

     - [sr_adm R va ppn], the regime's admissibility of the claim, and
     - [sr_swp_side R RS acc va ppn kp Db Drw Dro rs dst], the regime's own
       side condition (13 conjuncts for the shared kernel table).

   [SRegimeFetch] below is exactly those two, specialised to a FETCH
   ([acc = InstructionFetch tt], [kp = KP_rx], the S-mode frame footprints)
   and stated over the pins a wrapper's tower actually provides.  It is a
   CLASS, so a leaf takes it as an inferred implicit binder and every call
   site keeps its positional argument list.

   [s_regime_swp] is likewise made a class here (it is declared as a plain
   [Record] in SRegime.v, which this file does not edit), with the two
   instances registered, so that a leaf quantified over [R : s_regime] can
   find the swp face of its own regime. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import RegFile WpGpr InstrBytes MinstretInv.
Require Import HartLift HartSpan HartSpanChar HartRegNode HartGoodb WpDecodeBridge ExecCommon.
Require Import HartSwp.
Require Import MstatusBits WpGprMret WpMmodeLeafBase HartRunGen.
Require Import SmodeCore.
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
