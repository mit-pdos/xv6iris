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
        HartRegNode RegFile WpGpr.
Require Import ColdBoot.
Require Import RiscvFetchExec WpMmodeLeafBase HartMFrame ExecCommon
        HartMRun HartGoodb WpDecodeBridge.
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
Definition jr_Drw : gset register := {[ (R_bitvector_64 nextPC : register) ]}.
Definition jr_Dro : gset register :=
  {[ (cur_privilege : register); (mseccfg : register); (misa : register) ]}.
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
Proof. rewrite /jr_Drw /jr_Dro. set_solver. Qed.
Lemma jr_w_nPC : (R_bitvector_64 nextPC : register) ∈ jr_Drw.
Proof. rewrite /jr_Drw. set_solver. Qed.
Lemma jr_in_nPC : (R_bitvector_64 nextPC : register) ∈ jr_Drw ∪ jr_Dro.
Proof. rewrite /jr_Drw /jr_Dro. set_solver. Qed.
Lemma jr_in_priv : (cur_privilege : register) ∈ jr_Drw ∪ jr_Dro.
Proof. rewrite /jr_Drw /jr_Dro. set_solver. Qed.
Lemma jr_in_sec : (mseccfg : register) ∈ jr_Drw ∪ jr_Dro.
Proof. rewrite /jr_Drw /jr_Dro. set_solver. Qed.
Lemma jr_in_misa : (misa : register) ∈ jr_Drw ∪ jr_Dro.
Proof. rewrite /jr_Drw /jr_Dro. set_solver. Qed.

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
