(* WpMmodeJump.v -- the JUMP instructions' [swp] machinery.

   [jump_to] is the one model function in the leaf sweep that no node-shape
   template covers.  It reads misa -- but only when the target's bit 1 is set
   -- WRITES nextPC, and does both under [catch_early_return], i.e. inside the
   [monadR] exception monad rather than [M].

   The two lemmas here are proved by DIFFERENT routes, and which route fits is
   decided by one question: does the stretch write a register?

   - [hfrun_jump_to_zca] -- BY COMPUTATION.  [jump_to] writes nextPC, so the
     [goodb] bridge is unavailable (that certificate rejects writes outright).
     The walk is done by hand: reduce the [catch_early_return]/[liftR]/
     [try_catch] spine with a whitelisted [cbn], then step [hfrun] one node at
     a time by its own equations -- the discipline HartSpan's comment on
     [hfrun] insists on.  [try_catch] is a Fixpoint over the monad term, not a
     node, so it pushes THROUGH the read and the write and disappears; nothing
     about the exception monad survives into the walk.

   - [hval_update_elp_state] -- BY THE [goodb] BRIDGE.  Its
     [currentlyEnabled Ext_Zicfilp] is four levels of guarded recursion
     ([_rec_currentlyEnabled] -> [and_boolM] -> [hartSupports] ->
     [_rec_get_xLPE]) and reducing that by hand is a bad trade.  But it only
     READS (cur_privilege and mseccfg), so [HartGoodb.hval_of_goodb] applies:
     the [goodb] certificate is [vm_compute]d at [dstateM] and the [exec] fact
     is [WpMmodeLeafBase.exec_cE_zicfilp_false], which the exec-based stack
     already proved.  Its read set is exactly [WpDecodeBridge.D_m], the
     decode bridge's -- the same three config registers, so the same
     [agree_m] transports it to the caller's file.

   The moral for the rest of the sweep: reach for [goodb] whenever a stretch
   is read-only, however deep its recursion, and hand-walk only the stretches
   that write. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartSpan
        HartSpanChar HartRunGen HartRegNode HartMCycle RegFile WpGpr.
Require Import RiscvExtras RiscvFetchExec WpMmodeLeafBase HartMFrame
        ExecCommon HartMRun HartGoodb WpDecodeBridge.
Require Import TsoCtx.
Local Open Scope Z_scope.

(* collapse the closed [Z.eqb] tests of the model's rX/wX cascades *)
Local Ltac zt :=
  repeat match goal with
  | |- context [ if ?b then _ else _ ] =>
      assert_fails (is_var b);
      let x := eval vm_compute in b in
      lazymatch x with true => change b with true
                     | false => change b with false end
  end.

Local Notation zerobit :=
  (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 1)
     (BinaryString.Raw.to_N "0" 0%N)).

Lemma jt_red (target : SailStdpp.Values.mword 64) :
  eq_vec (access_vec_dec target 0) zerobit = true ->
  bit_to_bool (access_vec_dec target 1) = false ->
  jump_to target
  = Defs.bind0 (Defs.write_reg (R_bitvector_64 nextPC) target)
      (Interface.Ret RETIRE_SUCCESS).
Proof.
  intros Halign Hbit1.
  unfold jump_to.
  change (ext_control_check_pc target) with (@None unit).
  cbn beta iota zeta delta [Defs.catch_early_return Defs.try_catch Defs.bind
    Defs.bind0 Defs.returnR Defs.liftR Defs.and_boolM Defs.assert_exp
    Interface.iMon_bind Defs.returnm returnM].
  rewrite Halign. rewrite Hbit1.
  cbn beta iota zeta delta [Defs.try_catch Defs.liftR Defs.bind Defs.bind0
    Defs.returnR Defs.returnm returnM Interface.iMon_bind set_next_pc
    Defs.write_reg].
  cbn beta iota zeta delta [Defs.assert_exp Defs.try_catch Defs.liftR
    Defs.returnm returnM Interface.iMon_bind Defs.returnR].
  reflexivity.
Qed.

Local Notation onebit := (MachineWord.MachineWord.N_to_word 1 1%N).

Lemma hfrun_jump_to_zca (D Drw : gset register) (rs : regstate)
    (target : SailStdpp.Values.mword 64) :
  (misa : register) ∈ D ->
  (R_bitvector_64 nextPC : register) ∈ Drw ->
  eq_vec (access_vec_dec target 0) zerobit = true ->
  eq_vec (_get_Misa_C (register_lookup misa rs)) onebit = true ->
  hfrun 6 D Drw rs (jump_to target)
  = Some (RETIRE_SUCCESS, register_set (R_bitvector_64 nextPC) target rs).
Proof.
  intros HDmisa HWnpc Halign HmisaC.
  destruct (bit_to_bool (access_vec_dec target 1)) eqn:Hb1.
  - unfold jump_to.
    change (ext_control_check_pc target) with (@None unit).
    cbn beta iota zeta delta [Defs.catch_early_return Defs.try_catch Defs.bind
      Defs.bind0 Defs.returnR Defs.liftR Defs.and_boolM Defs.assert_exp
      Interface.iMon_bind Defs.returnm returnM].
    rewrite Halign. rewrite Hb1.
    cbn beta iota zeta delta [Defs.assert_exp Defs.try_catch Defs.liftR
      Defs.returnm returnM Interface.iMon_bind Defs.returnR Defs.bind].
    rewrite cE_Zca_read.
    cbn beta iota zeta delta [Defs.read_reg Defs.liftR Defs.try_catch Defs.bind
      Defs.bind0 Interface.iMon_bind Defs.returnm returnM Defs.returnR].
    rewrite hfrun_read (bool_decide_eq_true_2 _ HDmisa).
    rewrite HmisaC.
    cbn beta iota zeta delta [Defs.try_catch Defs.liftR Defs.bind Defs.bind0
      Interface.iMon_bind Defs.returnm returnM Defs.returnR set_next_pc
      Defs.write_reg].
    cbn beta iota zeta delta [not Defs.try_catch Defs.returnR Defs.returnm
      returnM].
    rewrite hfrun_write (bool_decide_eq_true_2 _ HWnpc). apply hfrun_ret.
  - rewrite (jt_red target Halign Hb1).
    cbn beta iota zeta delta [Defs.bind0 Defs.bind Defs.write_reg
      Interface.iMon_bind].
    rewrite hfrun_write (bool_decide_eq_true_2 _ HWnpc). apply hfrun_ret.
Qed.

Lemma dm_sub (D : gset register) :
  (cur_privilege : register) ∈ D -> (mseccfg : register) ∈ D ->
  (misa : register) ∈ D ->
  forall r : register, D_m r = true -> r ∈ D.
Proof.
  intros H1 H2 H3 r Hr. unfold D_m in Hr.
  apply orb_prop in Hr as [Hr|Hr];
    [apply orb_prop in Hr as [Hr|Hr]|];
    apply register_beq_eq in Hr; subst r; assumption.
Qed.

Lemma hval_update_elp_state (D Drw : gset register) (rs : regstate)
    (ra : SailStdpp.Values.mword 5) :
  (cur_privilege : register) ∈ D -> (mseccfg : register) ∈ D ->
  (misa : register) ∈ D ->
  register_lookup cur_privilege rs = Machine ->
  register_lookup mseccfg rs = Values.mword_of_int 0 ->
  register_lookup misa rs = MISA_C ->
  hval D Drw rs (update_elp_state (Regidx ra)) tt rs.
Proof.
  intros HD1 HD2 HD3 Hp Hs Hm.
  apply (hval_of_goodb D_m D Drw _ dstateM rs tt
           (dm_sub D HD1 HD2 HD3)
           (agree_m (MState rs ∅ dev0_state) Hp Hs Hm)).
  - vm_compute. reflexivity.
  - unfold update_elp_state.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_cE_zicfilp_false dstateM
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))).
    cbn match. apply exec_returnm.
Qed.


(* ====================================================================== *)
(* A FOUR-CELL FOOTPRINT, OWNED BY THE LEAF ITSELF.                        *)
(*                                                                        *)
(* [hfrun_jump_to_zca] and [hval_update_elp_state] are stated over an       *)
(* ARBITRARY (D, Drw, rs), and [swp_hfrun]/[swp_span] consume them at       *)
(* frames.  A jump leaf holds CELLS, not a frame -- but it does not need    *)
(* the wrapper's footprint to build one: the four registers these two       *)
(* stretches touch are nextPC (written) and cur_privilege / mseccfg / misa  *)
(* (read), and the leaf already owns all four -- nextPC from the            *)
(* obligation, cur_privilege from its own half of [mmode_config_split],     *)
(* and misa / mseccfg as PERSISTENT pins out of [hw_config].                *)
(*                                                                        *)
(* So the frame is built here, over [ColdBoot.init_regstate] as the         *)
(* inhabitant, with the three config values PINNED to what [hw_config]      *)
(* guarantees.  Nothing about [wp_instr]'s obligation has to change to let  *)
(* a jump leaf reason -- which is the answer to "what does JALR need": not  *)
(* a wider obligation, just its own footprint.                              *)
(* ====================================================================== *)
(* THE FOOTPRINT, over the ONE register the stretch writes.
   [cw_Dro] is the read-only half every M-mode config-reading stretch needs:
   cur_privilege / mseccfg / misa is exactly [WpDecodeBridge.D_m], so a
   [goodb]-transported fact lands in it without widening.  [cw_Drw] is
   whatever the stretch writes -- nextPC for a jump, the CSR for a CSR write
   -- which is why it is a parameter. *)
Definition cw_Drw (r : register) : gset register := {[ r ]}.
Definition cw_Dro : gset register :=
  {[ (cur_privilege : register); (mseccfg : register); (misa : register) ]}.

Definition jr_Drw : gset register := cw_Drw (R_bitvector_64 nextPC).
Definition jr_Dro : gset register := cw_Dro.
Definition jr_Df (dq : dfrac) : register -> dfrac := fun r =>
  if decide (r = (misa : register)) then DfracDiscarded
  else if decide (r = (mseccfg : register)) then DfracDiscarded
  else dq.

Definition jr_rs (npc0 : SailStdpp.Values.mword 64) : regstate :=
  register_set (R_bitvector_64 nextPC) npc0
    (register_set misa MISA_C
       (register_set mseccfg (Values.mword_of_int 0)
          (register_set cur_privilege Machine init_regstate))).

Lemma jr_disj : jr_Drw ## jr_Dro.
Proof. rewrite /jr_Drw /jr_Dro /cw_Drw /cw_Dro. set_solver. Qed.
Lemma jr_w_nPC : (R_bitvector_64 nextPC : register) ∈ jr_Drw.
Proof. rewrite /jr_Drw /cw_Drw. set_solver. Qed.
Lemma jr_in_nPC : (R_bitvector_64 nextPC : register) ∈ jr_Drw ∪ jr_Dro.
Proof. rewrite /jr_Drw /jr_Dro /cw_Drw /cw_Dro. set_solver. Qed.
Lemma jr_in_priv : (cur_privilege : register) ∈ jr_Drw ∪ jr_Dro.
Proof. rewrite /jr_Drw /jr_Dro /cw_Drw /cw_Dro. set_solver. Qed.
Lemma jr_in_sec : (mseccfg : register) ∈ jr_Drw ∪ jr_Dro.
Proof. rewrite /jr_Drw /jr_Dro /cw_Drw /cw_Dro. set_solver. Qed.
Lemma jr_in_misa : (misa : register) ∈ jr_Drw ∪ jr_Dro.
Proof. rewrite /jr_Drw /jr_Dro /cw_Drw /cw_Dro. set_solver. Qed.

(* NOT [rewrite (irrelevant_register_set _ _ _ _ ltac:(vm_compute; …))]: the
   [ltac:] runs before the register evar is solved.  [apply] fixes it from the
   goal first.  The count is the cell's depth in [jr_rs]. *)
Ltac jrskip :=
  etransitivity; [apply irrelevant_register_set; vm_compute; reflexivity|].

Lemma jr_rs_nPC npc0 :
  register_lookup (R_bitvector_64 nextPC) (jr_rs npc0) = npc0.
Proof. rewrite /jr_rs. by rewrite register_lookup_set. Qed.
Lemma jr_rs_misa npc0 :
  register_lookup misa (jr_rs npc0) = MISA_C.
Proof. rewrite /jr_rs. jrskip. apply register_lookup_set. Qed.
Lemma jr_rs_sec npc0 :
  register_lookup mseccfg (jr_rs npc0) = Values.mword_of_int 0.
Proof. rewrite /jr_rs. jrskip. jrskip. apply register_lookup_set. Qed.
Lemma jr_rs_priv npc0 :
  register_lookup cur_privilege (jr_rs npc0) = Machine.
Proof. rewrite /jr_rs. jrskip. jrskip. jrskip. apply register_lookup_set. Qed.

Ltac jrdf :=
  unfold jr_Df;
  repeat first [ rewrite decide_True; [reflexivity|reflexivity]
               | rewrite decide_False; [|discriminate] ];
  reflexivity.

Lemma jr_Df_misa dq : jr_Df dq misa = DfracDiscarded.
Proof. jrdf. Qed.
Lemma jr_Df_sec dq : jr_Df dq mseccfg = DfracDiscarded.
Proof. jrdf. Qed.
Lemma jr_Df_priv dq : jr_Df dq cur_privilege = dq.
Proof. jrdf. Qed.

(* the post-file of the jump: [jump_to] writes nextPC, and the resulting
   [register_set] agrees with the tower that simply NAMES the new value *)
Lemma jr_set_agree (npc0 target : SailStdpp.Values.mword 64) :
  reg_agree_on (jr_Drw ∪ jr_Dro)
    (register_set (R_bitvector_64 nextPC) target (jr_rs npc0)) (jr_rs target).
Proof.
  intros r Hr. rewrite /jr_Drw /jr_Dro /cw_Drw /cw_Dro in Hr.
  repeat (apply elem_of_union in Hr as [Hr|Hr]);
    apply elem_of_singleton in Hr; subst r.
  - etransitivity; [apply register_lookup_set|]. symmetry. apply jr_rs_nPC.
  - etransitivity;
      [apply irrelevant_register_set; vm_compute; reflexivity|].
    etransitivity; [apply jr_rs_priv|]. symmetry. apply jr_rs_priv.
  - etransitivity;
      [apply irrelevant_register_set; vm_compute; reflexivity|].
    etransitivity; [apply jr_rs_sec|]. symmetry. apply jr_rs_sec.
  - etransitivity;
      [apply irrelevant_register_set; vm_compute; reflexivity|].
    etransitivity; [apply jr_rs_misa|]. symmetry. apply jr_rs_misa.
Qed.

Section jump.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* ---- cells <-> the four-cell frame ---- *)
  Lemma jr_frames (dq : dfrac) (npc0 : SailStdpp.Values.mword 64) :
    (hreg_frame (jr_rs npc0) jr_Drw ∗
     hreg_frame_ro (jr_Df dq) (jr_rs npc0) jr_Dro : iProp Σ)
    ⊣⊢ ((R_bitvector_64 nextPC) ↦ᵣ npc0 ∗
        reg_pointsto cur_privilege dq Machine ∗
        reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) ∗
        reg_pointsto misa DfracDiscarded MISA_C).
  Proof.
    rewrite /hreg_frame /hreg_frame_ro /jr_Drw /jr_Dro /cw_Drw /cw_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite jr_rs_nPC jr_rs_priv jr_rs_sec jr_rs_misa.
    rewrite (jr_Df_priv dq) (jr_Df_sec dq) (jr_Df_misa dq).
    by rewrite !bi.sep_assoc.
  Qed.

  Lemma jr_frames_in (dq : dfrac) (npc0 : SailStdpp.Values.mword 64) :
    (R_bitvector_64 nextPC) ↦ᵣ npc0 -∗
    reg_pointsto cur_privilege dq Machine -∗
    reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) -∗
    reg_pointsto misa DfracDiscarded MISA_C -∗
    (hreg_frame (jr_rs npc0) jr_Drw ∗
     hreg_frame_ro (jr_Df dq) (jr_rs npc0) jr_Dro : iProp Σ).
  Proof.
    iIntros "H1 H2 H3 H4". rewrite jr_frames. iFrame.
  Qed.

  Lemma jr_frames_out (dq : dfrac) (npc0 : SailStdpp.Values.mword 64) :
    (hreg_frame (jr_rs npc0) jr_Drw ∗
     hreg_frame_ro (jr_Df dq) (jr_rs npc0) jr_Dro : iProp Σ) -∗
    ((R_bitvector_64 nextPC) ↦ᵣ npc0 ∗
     reg_pointsto cur_privilege dq Machine ∗
     reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) ∗
     reg_pointsto misa DfracDiscarded MISA_C).
  Proof. rewrite jr_frames. iIntros "H". iExact "H". Qed.

  Lemma jr_rw_ext (rs rs' : regstate) :
    reg_agree_on jr_Drw rs rs' ->
    hreg_frame rs jr_Drw -∗ (hreg_frame rs' jr_Drw : iProp Σ).
  Proof.
    intros Hag. rewrite (hreg_frame_ext _ _ jr_Drw Hag).
    iIntros "H". iExact "H".
  Qed.

  Lemma jr_ro_ext (dq : dfrac) (rs rs' : regstate) :
    reg_agree_on jr_Dro rs rs' ->
    hreg_frame_ro (jr_Df dq) rs jr_Dro -∗
    (hreg_frame_ro (jr_Df dq) rs' jr_Dro : iProp Σ).
  Proof.
    intros Hag. rewrite (hreg_frame_ro_ext (jr_Df dq) _ _ jr_Dro Hag).
    iIntros "H". iExact "H".
  Qed.

  (* ---- THE TWO LEAF-FACING RULES, at cells ---- *)

  Lemma swp_jump_to_zca (dq : dfrac)
      (target npc0 : SailStdpp.Values.mword 64) :
    eq_vec (access_vec_dec target 0) zerobit = true ->
    gen_cert -∗
    (R_bitvector_64 nextPC) ↦ᵣ npc0 -∗
    reg_pointsto cur_privilege dq Machine -∗
    reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) -∗
    reg_pointsto misa DfracDiscarded MISA_C -∗
    swp (jump_to target)
      (fun r => ⌜r = RETIRE_SUCCESS⌝ ∗
                (R_bitvector_64 nextPC) ↦ᵣ target ∗
                reg_pointsto cur_privilege dq Machine ∗
                reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) ∗
                reg_pointsto misa DfracDiscarded MISA_C).
  Proof.
    intros Halign. iIntros "#Hcert HnPC Hpriv Hsec Hmisa".
    iDestruct (jr_frames_in dq npc0 with "HnPC Hpriv Hsec Hmisa")
      as "[Hrw Hro]".
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_hfrun 6 jr_Drw jr_Dro (jr_Df dq) (jr_rs npc0)
                   (register_set (R_bitvector_64 nextPC) target (jr_rs npc0))
                   (jump_to target) RETIRE_SUCCESS jr_disj
                   (hfrun_jump_to_zca (jr_Drw ∪ jr_Dro) jr_Drw (jr_rs npc0)
                      target jr_in_misa jr_w_nPC Halign
                      ltac:(rewrite jr_rs_misa; vm_compute; reflexivity))
                   with "Hcert Hrw Hro") ].
    iIntros (r) "(-> & Hrw & Hro)".
    iDestruct (jr_rw_ext _ _
                 (reg_agree_l _ _ _ _ (jr_set_agree npc0 target))
                 with "Hrw") as "Hrw".
    iDestruct (jr_ro_ext dq _ _
                 (reg_agree_r _ _ _ _ (jr_set_agree npc0 target))
                 with "Hro") as "Hro".
    iDestruct (jr_frames_out dq target with "[$Hrw $Hro]")
      as "(HnPC & Hpriv & Hsec & Hmisa)".
    iSplitR; [done|]. iFrame.
  Qed.

  Lemma swp_update_elp_state (dq : dfrac) (ra : SailStdpp.Values.mword 5)
      (npc0 : SailStdpp.Values.mword 64) :
    gen_cert -∗
    (R_bitvector_64 nextPC) ↦ᵣ npc0 -∗
    reg_pointsto cur_privilege dq Machine -∗
    reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) -∗
    reg_pointsto misa DfracDiscarded MISA_C -∗
    swp (update_elp_state (Regidx ra))
      (fun _ => (R_bitvector_64 nextPC) ↦ᵣ npc0 ∗
                reg_pointsto cur_privilege dq Machine ∗
                reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) ∗
                reg_pointsto misa DfracDiscarded MISA_C).
  Proof.
    iIntros "#Hcert HnPC Hpriv Hsec Hmisa".
    iDestruct (jr_frames_in dq npc0 with "HnPC Hpriv Hsec Hmisa")
      as "[Hrw Hro]".
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_span jr_Drw jr_Dro (jr_Df dq) (jr_rs npc0) (jr_rs npc0)
                   (update_elp_state (Regidx ra)) tt jr_disj
                   (hval_update_elp_state (jr_Drw ∪ jr_Dro) jr_Drw
                      (jr_rs npc0) ra jr_in_priv jr_in_sec jr_in_misa
                      (jr_rs_priv npc0) (jr_rs_sec npc0) (jr_rs_misa npc0))
                   with "Hcert Hrw Hro") ].
    iIntros (u) "(_ & Hrw & Hro)".
    iDestruct (jr_frames_out dq npc0 with "[$Hrw $Hro]")
      as "(HnPC & Hpriv & Hsec & Hmisa)".
    iFrame.
  Qed.

  (* a write to x0 is discarded: the model's [wX_bits] cascade returns at
     index 0 without a node *)
  Lemma swp_wX_zero (i : SailStdpp.Values.mword 5)
      (v : SailStdpp.Values.mword 64) (P : iProp Σ) :
    uint i = 0 -> P -∗ swp (wX_bits (Regidx i) v) (fun _ => P).
  Proof.
    intros Hz. iIntros "HP". unfold wX_bits, wX. rewrite Hz. cbn match.
    iApply swp_ret. iExact "HP".
  Qed.

  (* ==================================================================== *)
  (* execute_JALR at rd = x0 -- the compressed RET.  The swp twin of        *)
  (* [WpMmodeLeafBase.exec_execute_JALR_ret_zca], peeled at the ONE node    *)
  (* the walkers cannot take: [rX_bits] at a symbolic index.                *)
  (* ==================================================================== *)
  Lemma swp_execute_JALR_ret_zca (dq : dfrac)
      (imm : SailStdpp.Values.mword 12)
      (ra rdz : SailStdpp.Values.mword 5)
      (m : regfile) (npc0 : SailStdpp.Values.mword 64) :
    uint rdz = 0 ->
    eq_vec (access_vec_dec
              (update_vec_dec
                 (add_vec (m !!! Regidx ra) (sign_extend' 64 imm)) 0 zerobit)
              0) zerobit = true ->
    gen_cert -∗
    gpr_file m -∗
    (R_bitvector_64 nextPC) ↦ᵣ npc0 -∗
    reg_pointsto cur_privilege dq Machine -∗
    reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) -∗
    reg_pointsto misa DfracDiscarded MISA_C -∗
    swp (execute_JALR imm (Regidx ra) (Regidx rdz))
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗ gpr_file m ∗
                (R_bitvector_64 nextPC) ↦ᵣ
                  (update_vec_dec
                     (add_vec (m !!! Regidx ra) (sign_extend' 64 imm)) 0
                     zerobit) ∗
                reg_pointsto cur_privilege dq Machine ∗
                reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) ∗
                reg_pointsto misa DfracDiscarded MISA_C).
  Proof.
    intros Hrdz Halign. iIntros "#Hcert Hf HnPC Hpriv Hsec Hmisa".
    unfold execute_JALR. cbn match.
    (* [m >> n >>= f] parses as [(m >> n) >>= f], so the elp gate and the link
       read are ONE first component of the outer bind. *)
    iApply (swp_bind_use
              (Defs.bind0 (update_elp_state (Regidx ra)) (get_next_pc tt)) _
              (fun link => ⌜link = npc0⌝ ∗
                 (R_bitvector_64 nextPC) ↦ᵣ npc0 ∗
                 reg_pointsto cur_privilege dq Machine ∗
                 reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) ∗
                 reg_pointsto misa DfracDiscarded MISA_C)%I _
              with "[HnPC Hpriv Hsec Hmisa] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ => (R_bitvector_64 nextPC) ↦ᵣ npc0 ∗
                   reg_pointsto cur_privilege dq Machine ∗
                   reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) ∗
                   reg_pointsto misa DfracDiscarded MISA_C)%I _
                with "[HnPC Hpriv Hsec Hmisa] [-]").
      { iApply (swp_update_elp_state dq ra npc0
                  with "Hcert HnPC Hpriv Hsec Hmisa"). }
      iIntros (u) "(HnPC & Hpriv & Hsec & Hmisa)".
      unfold get_next_pc.
      iApply (swp_mono with "[Hpriv Hsec Hmisa] [-]");
        [| iApply (swp_read_reg_cell (R_bitvector_64 nextPC) npc0
                     with "Hcert HnPC") ].
      iIntros (link) "[-> HnPC]". iSplitR; [done|]. iFrame. }
    iIntros (link) "(-> & HnPC & Hpriv & Hsec & Hmisa)".
    (* 3. the ONE symbolic-index node *)
    iApply (swp_bind_use (rX_bits (Regidx ra)) _ _ _ with "[Hf] [-]").
    { iApply (swp_rX_file ra m with "Hcert Hf"). }
    iIntros (w) "[-> Hf]".
    (* 4. the jump *)
    iApply (swp_bind_use _ _ _ _ with "[HnPC Hpriv Hsec Hmisa] [-]").
    { iApply (swp_jump_to_zca dq _ npc0 Halign
                with "Hcert HnPC Hpriv Hsec Hmisa"). }
    iIntros (r) "(-> & HnPC & Hpriv & Hsec & Hmisa)". cbn match.
    (* 5. the discarded write to x0 *)
    iApply (swp_bind0_use _ _ (fun _ => gpr_file m)%I _ with "[Hf] [-]").
    { iApply (swp_wX_zero rdz _ (gpr_file m) Hrdz with "Hf"). }
    iIntros (u2) "Hf". iApply swp_ret. iSplitR; [done|]. iFrame.
  Qed.

  (* the form a leaf states: the target spelled as [ret_pc], and the alignment
     side condition discharged from [ret_pc]'s own construction *)
  Lemma swp_execute_JALR_ret (dq : dfrac)
      (ra rdz : SailStdpp.Values.mword 5) (m : regfile)
      (npc0 : SailStdpp.Values.mword 64) :
    uint rdz = 0 ->
    gen_cert -∗
    gpr_file m -∗
    (R_bitvector_64 nextPC) ↦ᵣ npc0 -∗
    reg_pointsto cur_privilege dq Machine -∗
    reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) -∗
    reg_pointsto misa DfracDiscarded MISA_C -∗
    swp (execute_JALR (zeros' 12) (Regidx ra) (Regidx rdz))
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗ gpr_file m ∗
                (R_bitvector_64 nextPC) ↦ᵣ (ret_pc (m !!! Regidx ra)) ∗
                reg_pointsto cur_privilege dq Machine ∗
                reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) ∗
                reg_pointsto misa DfracDiscarded MISA_C).
  Proof.
    intros Hrdz. iIntros "#Hcert Hf HnPC Hpriv Hsec Hmisa".
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_execute_JALR_ret_zca dq (zeros' 12) ra rdz m npc0 Hrdz
                   ltac:(rewrite ret_pc_jalr; apply ret_pc_aligned)
                   with "Hcert Hf HnPC Hpriv Hsec Hmisa") ].
    iIntros (e) "(-> & Hf & HnPC & Hpriv & Hsec & Hmisa)".
    rewrite ret_pc_jalr. iSplitR; [done|]. iFrame.
  Qed.

  (* ==================================================================== *)
  (* execute_JAL -- reads nextPC (the link) and PC (the base), jumps, and    *)
  (* links into rd.  PC is read-only here, which is why [wp_instr]'s          *)
  (* obligation lends it rather than keeping it in the frame.                *)
  (* ==================================================================== *)
  Lemma swp_execute_JAL (dq : dfrac) (imm : SailStdpp.Values.mword 21)
      (rd : SailStdpp.Values.mword 5) (m : regfile)
      (pc npc0 : SailStdpp.Values.mword 64) :
    uint rd <> 0 ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) zerobit
      = true ->
    gen_cert -∗
    gpr_file m -∗
    (R_bitvector_64 PC) ↦ᵣ pc -∗
    (R_bitvector_64 nextPC) ↦ᵣ npc0 -∗
    reg_pointsto cur_privilege dq Machine -∗
    reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) -∗
    reg_pointsto misa DfracDiscarded MISA_C -∗
    swp (execute_JAL imm (Regidx rd))
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                gpr_file (<[Regidx rd := regval_into_reg npc0]> m) ∗
                (R_bitvector_64 PC) ↦ᵣ pc ∗
                (R_bitvector_64 nextPC) ↦ᵣ (add_vec pc (sign_extend' 64 imm)) ∗
                reg_pointsto cur_privilege dq Machine ∗
                reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) ∗
                reg_pointsto misa DfracDiscarded MISA_C).
  Proof.
    intros Hrd Halign. iIntros "#Hcert Hf HPC HnPC Hpriv Hsec Hmisa".
    unfold execute_JAL. cbn match.
    (* 1. the link address *)
    iApply (swp_bind_use (get_next_pc tt) _
              (fun link => ⌜link = npc0⌝ ∗
                 (R_bitvector_64 nextPC) ↦ᵣ npc0)%I _
              with "[HnPC] [-]").
    { unfold get_next_pc.
      iApply (swp_read_reg_cell (R_bitvector_64 nextPC) npc0
                with "Hcert HnPC"). }
    iIntros (link) "[-> HnPC]".
    (* 2. the base *)
    iApply (swp_bind_use (Defs.read_reg (R_bitvector_64 PC)) _
              (fun w => ⌜w = pc⌝ ∗ (R_bitvector_64 PC) ↦ᵣ pc)%I _
              with "[HPC] [-]").
    { iApply (swp_read_reg_cell (R_bitvector_64 PC) pc with "Hcert HPC"). }
    iIntros (w0) "[-> HPC]".
    (* 3. the jump *)
    iApply (swp_bind_use _ _ _ _ with "[HnPC Hpriv Hsec Hmisa] [-]").
    { iApply (swp_jump_to_zca dq _ npc0 Halign
                with "Hcert HnPC Hpriv Hsec Hmisa"). }
    iIntros (r) "(-> & HnPC & Hpriv & Hsec & Hmisa)". cbn match.
    (* 4. the link write *)
    iApply (swp_bind0_use _ _ _ _ with "[Hf] [-]").
    { iApply (swp_wX_file rd m npc0 Hrd with "Hcert Hf"). }
    iIntros (u) "Hf". iApply swp_ret. iSplitR; [done|]. iFrame.
  Qed.

  (* [c.j] and [jal x0, off]: rd = x0, so the link write is discarded and the
     whole instruction is a pure redirect of nextPC. *)
  Lemma swp_execute_JAL_zreg (dq : dfrac) (imm : SailStdpp.Values.mword 21)
      (rdz : SailStdpp.Values.mword 5) (m : regfile)
      (pc npc0 : SailStdpp.Values.mword 64) :
    uint rdz = 0 ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) zerobit
      = true ->
    gen_cert -∗
    gpr_file m -∗
    (R_bitvector_64 PC) ↦ᵣ pc -∗
    (R_bitvector_64 nextPC) ↦ᵣ npc0 -∗
    reg_pointsto cur_privilege dq Machine -∗
    reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) -∗
    reg_pointsto misa DfracDiscarded MISA_C -∗
    swp (execute_JAL imm (Regidx rdz))
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗ gpr_file m ∗
                (R_bitvector_64 PC) ↦ᵣ pc ∗
                (R_bitvector_64 nextPC) ↦ᵣ (add_vec pc (sign_extend' 64 imm)) ∗
                reg_pointsto cur_privilege dq Machine ∗
                reg_pointsto mseccfg DfracDiscarded (Values.mword_of_int 0) ∗
                reg_pointsto misa DfracDiscarded MISA_C).
  Proof.
    intros Hrdz Halign. iIntros "#Hcert Hf HPC HnPC Hpriv Hsec Hmisa".
    unfold execute_JAL. cbn match.
    iApply (swp_bind_use (get_next_pc tt) _
              (fun link => ⌜link = npc0⌝ ∗
                 (R_bitvector_64 nextPC) ↦ᵣ npc0)%I _
              with "[HnPC] [-]").
    { unfold get_next_pc.
      iApply (swp_read_reg_cell (R_bitvector_64 nextPC) npc0
                with "Hcert HnPC"). }
    iIntros (link) "[-> HnPC]".
    iApply (swp_bind_use (Defs.read_reg (R_bitvector_64 PC)) _
              (fun w => ⌜w = pc⌝ ∗ (R_bitvector_64 PC) ↦ᵣ pc)%I _
              with "[HPC] [-]").
    { iApply (swp_read_reg_cell (R_bitvector_64 PC) pc with "Hcert HPC"). }
    iIntros (w0) "[-> HPC]".
    iApply (swp_bind_use _ _ _ _ with "[HnPC Hpriv Hsec Hmisa] [-]").
    { iApply (swp_jump_to_zca dq _ npc0 Halign
                with "Hcert HnPC Hpriv Hsec Hmisa"). }
    iIntros (r) "(-> & HnPC & Hpriv & Hsec & Hmisa)". cbn match.
    iApply (swp_bind0_use _ _ (fun _ => gpr_file m)%I _ with "[Hf] [-]").
    { iApply (swp_wX_zero rdz _ (gpr_file m) Hrdz with "Hf"). }
    iIntros (u) "Hf". iApply swp_ret. iSplitR; [done|]. iFrame.
  Qed.

End jump.
