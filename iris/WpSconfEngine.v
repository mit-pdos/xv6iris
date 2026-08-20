(* WpSconfEngine.v -- the S-MODE gpr-write ENGINES at the per-node layer,
   for the leaves whose written value is a FUNCTION OF THE SOURCE READS.

   WHY THIS FILE EXISTS.  [WpSmodeIntr.wp_gpr_write_s_sconf{,_base}]'s
   instruction obligation is HART-GENERIC -- it is [∀ CID, gen_cert -∗
   gpr_file (tp_pin m) -∗ swp (execute base) (... <[rd := wval]> (tp_pin m))]
   with [wval] fixed by the CALLER, at the caller's hart.  That is exactly
   right for a leaf whose value reads no caller-chosen register ([c.li],
   [lui]), and it is UNPROVABLE for one that does: the walk answers the read
   at the hart the σ-callback was instantiated at, while [wval] names the
   value at the entry hart, and the two differ at tp.  A leaf holding only
   [ops_ok b rd rsa rsb] cannot close that gap by itself -- [src_ok] is
   guarded on [b = true], and the guard that saves the [b = false] case is
   [WpNext.wp_next]'s, which the obligation does not carry.  (This is the
   "guarded route" IntrDefs' [SrcOk] note points at: a leaf whose caller has
   only [ops_ok] at a variable [b] belongs here and not on the class.)

   THE SHAPE THAT DISSOLVES IT.  Do not hand the obligation a value; hand it
   the FUNCTION.  The engines below take [f : mword 64 -> mword 64 -> mword 64]
   and a caller premise [f (rget m rsa) (rget m rsb) = wval], and their
   obligation is

     ∀ CID, gen_cert -∗ gpr_file (tp_pin m) -∗
       swp (execute base) (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
         gpr_file (<[Regidx rd := regval_into_reg
                       (f (tp_pin m !!! Regidx rsa)
                          (tp_pin m !!! Regidx rsb))]> (tp_pin m)))

   -- which mentions no hart-specific value at all and is, verbatim, what
   [WpMmodeSwpBase]'s node shapes ([swp_execute_rrw] / [_rw] / [_rw2] /
   [_rrw2] / [_pure_w]) conclude.  A converted leaf is therefore ONE [iApply]
   with no [swp_mono] and no rewriting.  The reconciliation between the two
   harts happens ONCE, here, out of [ops_ok] and the [wp_next] guard, by
   [IntrDefs.rget_next_ops_indep].

   A leaf reading NO caller-chosen register may still use these ([f] ignores
   its arguments) or stay on [WpSmodeIntr]'s value-shaped engines; both are
   proved from the same funnel.

   ADDITIVE: nothing here changes an existing statement.  The three engines
   that live in WpSconfAlu.v ([wp_gpr_write_s_sconf_base_pc], the two cap
   engines) are converted in place beside their leaves. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import RegFile HartTp WpNext WpGpr InstrBytes WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import HartSwp HartMFrame.
Require Import HartLift HartSpan HartSpanChar HartMCycle WpMmodeJump.
Require Import HartGoodb WpDecodeBridge WpDecode RiscvExtras.
Require Import IntrDefs WpIntrInv WpSmodeIntr.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.
Import Defs.

(* ====================================================================== *)
(* §2 BRANCHES.  A branch writes no GPR, so none of the engines above      *)
(* fits: what it does is read two registers, and -- if the comparison      *)
(* holds -- read PC and WRITE nextPC.  The model's own shape, printed      *)
(* rather than guessed (durable-notes' rule), is the notation below; the   *)
(* condition code is a parameter, so each of the six [bop]s is [eq_refl].  *)
(* ====================================================================== *)

Notation btype_body imm rs2 rs1 cmp :=
  (Defs.bind
     (Defs.bind (rX_bits (Regidx rs1))
        (fun a => Defs.bind (rX_bits (Regidx rs2))
                    (fun c => returnM (cmp a c))))
     (fun taken : bool =>
        if taken
        then Defs.bind (Defs.read_reg (R_bitvector_64 PC))
               (fun w => jump_to (add_vec w (sign_extend' 64 imm)))
        else returnM RETIRE_SUCCESS)).

(* the target's bit 0, spelled as the MODEL spells it (design §5 item 1(g):
   a hand-written [N_to_word 1 0] is convertible but not syntactically equal,
   and [rewrite]/[destruct .. eqn:] match syntactically) *)
Local Notation zerobit :=
  (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 1)
     (BinaryString.Raw.to_N "0" 0%N)).

(* ---- THE TWO-CELL FRAME the S-mode jump needs.  [WpMmodeJump]'s is FOUR
   cells and pins cur_privilege to Machine, which no S-mode leaf can supply;
   but [hfrun_jump_to_zca] itself only ever reads misa and only ever writes
   nextPC, so the privilege was never the jump's business.  This is that
   fact, framed. ---- *)
Definition sj_Drw : gset register := {[ (R_bitvector_64 nextPC : register) ]}.
Definition sj_Dro : gset register := {[ (misa : register) ]}.
Definition sj_Df : register -> dfrac := fun _ => DfracDiscarded.
Definition sj_rs (npc0 : SailStdpp.Values.mword 64) : regstate :=
  register_set (R_bitvector_64 nextPC) npc0 (register_set misa MISA_C init_regstate).

Lemma sj_disj : sj_Drw ## sj_Dro.
Proof. rewrite /sj_Drw /sj_Dro. set_solver. Qed.
Lemma sj_w_nPC : (R_bitvector_64 nextPC : register) ∈ sj_Drw.
Proof. rewrite /sj_Drw. set_solver. Qed.
Lemma sj_in_misa : (misa : register) ∈ sj_Drw ∪ sj_Dro.
Proof. rewrite /sj_Drw /sj_Dro. set_solver. Qed.

Lemma sj_rs_nPC npc0 :
  register_lookup (R_bitvector_64 nextPC) (sj_rs npc0) = npc0.
Proof. rewrite /sj_rs. by rewrite register_lookup_set. Qed.
Lemma sj_rs_misa npc0 : register_lookup misa (sj_rs npc0) = MISA_C.
Proof.
  rewrite /sj_rs.
  etransitivity; [apply irrelevant_register_set; vm_compute; reflexivity|].
  apply register_lookup_set.
Qed.

Lemma sj_set_agree (npc0 target : SailStdpp.Values.mword 64) :
  reg_agree_on (sj_Drw ∪ sj_Dro)
    (register_set (R_bitvector_64 nextPC) target (sj_rs npc0)) (sj_rs target).
Proof.
  intros r Hr. rewrite /sj_Drw /sj_Dro in Hr.
  apply elem_of_union in Hr as [Hr|Hr]; apply elem_of_singleton in Hr; subst r.
  - etransitivity; [apply register_lookup_set|]. symmetry. apply sj_rs_nPC.
  - etransitivity;
      [apply irrelevant_register_set; vm_compute; reflexivity|].
    etransitivity; [apply sj_rs_misa|]. symmetry. apply sj_rs_misa.
Qed.

Section HwMisa.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the ONE cell a jump needs out of the persistent config bundle *)
  Lemma hw_config_misa : hw_config -∗ misa ↦ᵣ□ MISA_C.
  Proof.
    iIntros "H". iDestruct "H" as (misa0 mseccfg0 pmar0 elp0)
      "(Hmisa & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hv & _)".
    rewrite Hv. iExact "Hmisa".
  Qed.
End HwMisa.

Section WpSconfBranch.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma sj_frames (npc0 : SailStdpp.Values.mword 64) :
    (hreg_frame (sj_rs npc0) sj_Drw ∗
     hreg_frame_ro sj_Df (sj_rs npc0) sj_Dro : iProp Σ)
    ⊣⊢ ((R_bitvector_64 nextPC) ↦ᵣ npc0 ∗ misa ↦ᵣ□ MISA_C).
  Proof.
    rewrite /hreg_frame /hreg_frame_ro /sj_Drw /sj_Dro.
    rewrite !big_sepS_singleton.
    by rewrite sj_rs_nPC sj_rs_misa.
  Qed.

  (* THE S-MODE JUMP, at cells: nextPC written, misa read.  Privilege-free. *)
  Lemma swp_jump_to_s (target npc0 : SailStdpp.Values.mword 64) :
    eq_vec (access_vec_dec target 0) zerobit = true ->
    gen_cert -∗
    (R_bitvector_64 nextPC) ↦ᵣ npc0 -∗
    misa ↦ᵣ□ MISA_C -∗
    swp (jump_to target)
      (fun r => ⌜r = RETIRE_SUCCESS⌝ ∗
                (R_bitvector_64 nextPC) ↦ᵣ target ∗ misa ↦ᵣ□ MISA_C).
  Proof.
    intros Halign. iIntros "#Hcert HnPC Hmisa".
    iAssert (hreg_frame (sj_rs npc0) sj_Drw ∗
             hreg_frame_ro sj_Df (sj_rs npc0) sj_Dro)%I with "[HnPC Hmisa]"
      as "[Hrw Hro]".
    { rewrite sj_frames. iFrame. }
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_hfrun 6 sj_Drw sj_Dro sj_Df (sj_rs npc0)
                   (register_set (R_bitvector_64 nextPC) target (sj_rs npc0))
                   (jump_to target) RETIRE_SUCCESS sj_disj
                   (hfrun_jump_to_zca (sj_Drw ∪ sj_Dro) sj_Drw (sj_rs npc0)
                      target sj_in_misa sj_w_nPC Halign
                      ltac:(rewrite sj_rs_misa; vm_compute; reflexivity))
                   with "Hcert Hrw Hro") ].
    iIntros (r) "(-> & Hrw & Hro)".
    rewrite (hreg_frame_ext _ (sj_rs target) sj_Drw
               (reg_agree_l _ _ _ _ (sj_set_agree npc0 target))).
    rewrite (hreg_frame_ro_ext sj_Df _ (sj_rs target) sj_Dro
               (reg_agree_r _ _ _ _ (sj_set_agree npc0 target))).
    iSplitR; [done|]. rewrite -sj_frames. iFrame.
  Qed.

  (* the comparison half: two GPR reads at a symbolic index, so it peels at
     [swp_rX_file] like every other operand read in the sweep *)
  Lemma swp_btype_cmp (rs2 rs1 : SailStdpp.Values.mword 5) (m : regfile)
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

  (* THE FALL-THROUGH ARM: the comparison is false, so the branch is two
     register reads and a [Ret] -- no cell of any kind is touched. *)
  Lemma swp_execute_BTYPE_fall (imm : SailStdpp.Values.mword 13)
      (rs2 rs1 : SailStdpp.Values.mword 5) (m : regfile)
      (mo : M ExecutionResult)
      (cmp : SailStdpp.Values.mword 64 -> SailStdpp.Values.mword 64 -> bool) :
    mo = btype_body imm rs2 rs1 cmp ->
    cmp (m !!! Regidx rs1) (m !!! Regidx rs2) = false ->
    gen_cert -∗ gpr_file m -∗
    swp mo (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗ gpr_file m).
  Proof.
    intros Hred Hcmp. iIntros "#Hcert Hf". rewrite Hred.
    iApply (swp_bind_use _ _
              (fun v => ⌜v = cmp (m !!! Regidx rs1) (m !!! Regidx rs2)⌝ ∗
                        gpr_file m)%I _ with "[Hf] [-]").
    { iApply (swp_btype_cmp rs2 rs1 m cmp with "Hcert Hf"). }
    iIntros (v) "[-> Hf]". rewrite Hcmp.
    iApply swp_ret. by iFrame.
  Qed.

  (* THE TAKEN ARM: the comparison holds, PC is read and nextPC written. *)
  Lemma swp_execute_BTYPE_taken (imm : SailStdpp.Values.mword 13)
      (rs2 rs1 : SailStdpp.Values.mword 5) (m : regfile)
      (mo : M ExecutionResult) (pc npc0 : SailStdpp.Values.mword 64)
      (cmp : SailStdpp.Values.mword 64 -> SailStdpp.Values.mword 64 -> bool) :
    mo = btype_body imm rs2 rs1 cmp ->
    cmp (m !!! Regidx rs1) (m !!! Regidx rs2) = true ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) zerobit = true ->
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
    { iApply (swp_btype_cmp rs2 rs1 m cmp with "Hcert Hf"). }
    iIntros (v) "[-> Hf]". rewrite Hcmp.
    iApply (swp_bind_use (Defs.read_reg (R_bitvector_64 PC)) _
              (fun w => ⌜w = pc⌝ ∗ (R_bitvector_64 PC) ↦ᵣ pc)%I _
              with "[HPC] [-]").
    { iApply (swp_read_reg_cell (R_bitvector_64 PC) pc with "Hcert HPC"). }
    iIntros (w) "[-> HPC]".
    iApply (swp_mono with "[Hf HPC] [HnPC Hmisa]");
      [| iApply (swp_jump_to_s (add_vec pc (sign_extend' 64 imm)) npc0 Halign
                   with "Hcert HnPC Hmisa") ].
    iIntros (r) "(-> & HnPC & Hmisa)". iFrame. done.
  Qed.

End WpSconfBranch.

(* ====================================================================== *)
(* §4 CONTROL TRANSFER AND FENCES AT SUPERVISOR.                           *)
(*                                                                        *)
(* [WpMmodeJump]'s JAL/JALR engines pin cur_privilege to Machine in TWO    *)
(* places: [swp_jump_to_zca]'s frame (which does not need it at all -- §2) *)
(* and [hval_update_elp_state], which really does read the privilege, via  *)
(* [currentlyEnabled Ext_Zicfilp].  The second is the S-mode twin below:   *)
(* the same [goodb] bridge at [dstateS] instead of [dstateM], with         *)
(* [WpDecode.exec_cE_zicfilp_false_S] as the exec fact.  So the S-mode     *)
(* jump footprint is FOUR cells -- nextPC written, cur_privilege/menvcfg/  *)
(* misa read -- and every one of them is in [sconf].                       *)
(* ====================================================================== *)

Lemma ds_sub (D : gset register) :
  (cur_privilege : register) ∈ D -> (menvcfg : register) ∈ D ->
  (misa : register) ∈ D ->
  forall r : register, D_s r = true -> r ∈ D.
Proof.
  intros H1 H2 H3 r Hr. unfold D_s in Hr.
  apply orb_prop in Hr as [Hr|Hr];
    [apply orb_prop in Hr as [Hr|Hr]|];
    apply register_beq_eq in Hr; subst r; assumption.
Qed.

Lemma hval_update_elp_state_S (D Drw : gset register) (rs : regstate)
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
           (ds_sub D HD1 HD2 HD3)
           (agree_s (MState rs ∅ dev0_state) Hp Hme Hm)).
  - vm_compute. reflexivity.
  - unfold update_elp_state.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_cE_zicfilp_false_S dstateS
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))).
    cbn match. apply exec_returnm.
Qed.

(* the FOUR-cell S-mode jump frame *)
Definition sje_Drw : gset register := {[ (R_bitvector_64 nextPC : register) ]}.
Definition sje_Dro : gset register :=
  {[ (cur_privilege : register); (menvcfg : register); (misa : register) ]}.
Definition sje_Df : register -> dfrac := fun r =>
  if decide (r = (misa : register)) then DfracDiscarded else DfracOwn 1.
Definition sje_rs (npc0 : SailStdpp.Values.mword 64) : regstate :=
  register_set (R_bitvector_64 nextPC) npc0
    (register_set misa MISA_C
       (register_set menvcfg MENVCFG_S
          (register_set cur_privilege Supervisor init_regstate))).

Lemma sje_disj : sje_Drw ## sje_Dro.
Proof. rewrite /sje_Drw /sje_Dro. set_solver. Qed.
Lemma sje_in_priv : (cur_privilege : register) ∈ sje_Drw ∪ sje_Dro.
Proof. rewrite /sje_Drw /sje_Dro. set_solver. Qed.
Lemma sje_in_menv : (menvcfg : register) ∈ sje_Drw ∪ sje_Dro.
Proof. rewrite /sje_Drw /sje_Dro. set_solver. Qed.
Lemma sje_in_misa : (misa : register) ∈ sje_Drw ∪ sje_Dro.
Proof. rewrite /sje_Drw /sje_Dro. set_solver. Qed.

Ltac sjeskip :=
  etransitivity; [apply irrelevant_register_set; vm_compute; reflexivity|].

Lemma sje_rs_nPC npc0 :
  register_lookup (R_bitvector_64 nextPC) (sje_rs npc0) = npc0.
Proof. rewrite /sje_rs. by rewrite register_lookup_set. Qed.
Lemma sje_rs_misa npc0 : register_lookup misa (sje_rs npc0) = MISA_C.
Proof. rewrite /sje_rs. sjeskip. apply register_lookup_set. Qed.
Lemma sje_rs_menv npc0 : register_lookup menvcfg (sje_rs npc0) = MENVCFG_S.
Proof. rewrite /sje_rs. sjeskip. sjeskip. apply register_lookup_set. Qed.
Lemma sje_rs_priv npc0 :
  register_lookup cur_privilege (sje_rs npc0) = Supervisor.
Proof. rewrite /sje_rs. sjeskip. sjeskip. sjeskip. apply register_lookup_set. Qed.

Ltac sjedf :=
  unfold sje_Df;
  repeat first [ rewrite decide_True; [reflexivity|reflexivity]
               | rewrite decide_False; [|discriminate] ];
  reflexivity.
Lemma sje_Df_misa : sje_Df misa = DfracDiscarded.
Proof. sjedf. Qed.
Lemma sje_Df_menv : sje_Df menvcfg = DfracOwn 1.
Proof. sjedf. Qed.
Lemma sje_Df_priv : sje_Df cur_privilege = DfracOwn 1.
Proof. sjedf. Qed.

Section WpSconfCtlEng.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma sje_frames (npc0 : SailStdpp.Values.mword 64) :
    (hreg_frame (sje_rs npc0) sje_Drw ∗
     hreg_frame_ro sje_Df (sje_rs npc0) sje_Dro : iProp Σ)
    ⊣⊢ ((R_bitvector_64 nextPC) ↦ᵣ npc0 ∗
        cur_privilege ↦ᵣ Supervisor ∗ menvcfg ↦ᵣ MENVCFG_S ∗
        misa ↦ᵣ□ MISA_C).
  Proof.
    rewrite /hreg_frame /hreg_frame_ro /sje_Drw /sje_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite sje_rs_nPC sje_rs_priv sje_rs_menv sje_rs_misa.
    rewrite sje_Df_priv sje_Df_menv sje_Df_misa.
    by rewrite !bi.sep_assoc.
  Qed.

  Lemma swp_update_elp_state_S (ra : SailStdpp.Values.mword 5)
      (npc0 : SailStdpp.Values.mword 64) :
    gen_cert -∗
    (R_bitvector_64 nextPC) ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Supervisor -∗
    menvcfg ↦ᵣ MENVCFG_S -∗
    misa ↦ᵣ□ MISA_C -∗
    swp (update_elp_state (Regidx ra))
      (fun _ => (R_bitvector_64 nextPC) ↦ᵣ npc0 ∗
                cur_privilege ↦ᵣ Supervisor ∗ menvcfg ↦ᵣ MENVCFG_S ∗
                misa ↦ᵣ□ MISA_C).
  Proof.
    iIntros "#Hcert HnPC Hpriv Hmenv Hmisa".
    iAssert (hreg_frame (sje_rs npc0) sje_Drw ∗
             hreg_frame_ro sje_Df (sje_rs npc0) sje_Dro)%I
      with "[HnPC Hpriv Hmenv Hmisa]" as "[Hrw Hro]".
    { rewrite sje_frames. iFrame. }
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_span sje_Drw sje_Dro sje_Df (sje_rs npc0) (sje_rs npc0)
                   (update_elp_state (Regidx ra)) tt sje_disj
                   (hval_update_elp_state_S (sje_Drw ∪ sje_Dro) sje_Drw
                      (sje_rs npc0) ra sje_in_priv sje_in_menv sje_in_misa
                      (sje_rs_priv npc0) (sje_rs_menv npc0) (sje_rs_misa npc0))
                   with "Hcert Hrw Hro") ].
    iIntros (u) "(_ & Hrw & Hro)".
    iAssert ((R_bitvector_64 nextPC) ↦ᵣ npc0 ∗ cur_privilege ↦ᵣ Supervisor ∗
             menvcfg ↦ᵣ MENVCFG_S ∗ misa ↦ᵣ□ MISA_C)%I
      with "[Hrw Hro]" as "H".
    { rewrite -sje_frames. iFrame. }
    iExact "H".
  Qed.

  (* ---- fences: a barrier is a SILENT node, so the walker passes it ---- *)
  Lemma swp_barrier_ret (bk : barrier_kind) :
    gen_cert -∗
    swp (Defs.bind0 (sail_barrier bk) (returnM RETIRE_SUCCESS))
      (fun e => ⌜e = RETIRE_SUCCESS⌝).
  Proof.
    iIntros "#Hcert".
    iAssert (hreg_frame init_regstate ∅) as "Hrw".
    { rewrite /hreg_frame. by rewrite big_sepS_empty. }
    iAssert (hreg_frame_ro (fun _ => DfracDiscarded) init_regstate ∅) as "Hro".
    { rewrite /hreg_frame_ro. by rewrite big_sepS_empty. }
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_hfrun 2 ∅ ∅ (fun _ => DfracDiscarded)
                   init_regstate init_regstate
                   (Defs.bind0 (sail_barrier bk) (returnM RETIRE_SUCCESS))
                   RETIRE_SUCCESS ltac:(set_solver) ltac:(reflexivity)
                   with "Hcert Hrw Hro") ].
    iIntros (e) "(-> & _ & _)". done.
  Qed.

  Lemma swp_execute_FENCEI_s (imm : SailStdpp.Values.mword 12) (rs rd : regidx) :
    gen_cert -∗
    swp (execute (FENCEI (imm, rs, rd))) (fun e => ⌜e = RETIRE_SUCCESS⌝).
  Proof. exact (swp_barrier_ret Barrier_RISCV_i). Qed.

  Lemma swp_is_fiom_active_S (menv : SailStdpp.Values.mword 64) :
    gen_cert -∗ cur_privilege ↦ᵣ Supervisor -∗ menvcfg ↦ᵣ menv -∗
    swp (is_fiom_active tt)
      (fun v => ⌜v = eq_vec (_get_MEnvcfg_FIOM menv) ('b"1")⌝ ∗
                cur_privilege ↦ᵣ Supervisor ∗ menvcfg ↦ᵣ menv).
  Proof.
    iIntros "#Hcert Hpriv Hmenv". unfold is_fiom_active.
    iApply (swp_bind_use (Defs.read_reg cur_privilege) _
              (fun w => ⌜w = Supervisor⌝ ∗ cur_privilege ↦ᵣ Supervisor)%I _
              with "[Hpriv] [-]").
    { iApply (swp_read_reg_cell cur_privilege Supervisor with "Hcert Hpriv"). }
    iIntros (w) "[-> Hpriv]". cbn match.
    iApply (swp_bind_use (Defs.read_reg menvcfg) _
              (fun w2 => ⌜w2 = menv⌝ ∗ menvcfg ↦ᵣ menv)%I _
              with "[Hmenv] [-]").
    { iApply (swp_read_reg_cell menvcfg menv with "Hcert Hmenv"). }
    iIntros (w2) "[-> Hmenv]". iApply swp_ret. by iFrame.
  Qed.

  (* THE FENCE.  Its barrier DISPATCH is a nine-way [if] chain on the
     effective pred/succ pairs, which are symbolic at a leaf -- so no walker
     takes it: the chain is [destruct]ed, and every arm is one barrier node. *)
  Lemma swp_execute_FENCE_S (fm pred succ : SailStdpp.Values.mword 4)
      (rs rd : regidx) (menv : SailStdpp.Values.mword 64) :
    gen_cert -∗ cur_privilege ↦ᵣ Supervisor -∗ menvcfg ↦ᵣ menv -∗
    swp (execute (FENCE (fm, pred, succ, rs, rd)))
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                cur_privilege ↦ᵣ Supervisor ∗ menvcfg ↦ᵣ menv).
  Proof.
    iIntros "#Hcert Hpriv Hmenv".
    change (execute (FENCE (fm, pred, succ, rs, rd)))
      with (execute_FENCE fm pred succ rs rd).
    unfold execute_FENCE.
    iApply (swp_bind_use (is_fiom_active tt) _
              (fun v => ⌜v = eq_vec (_get_MEnvcfg_FIOM menv) ('b"1")⌝ ∗
                        cur_privilege ↦ᵣ Supervisor ∗ menvcfg ↦ᵣ menv)%I _
              with "[Hpriv Hmenv] [-]").
    { iApply (swp_is_fiom_active_S menv with "Hcert Hpriv Hmenv"). }
    iIntros (v) "(-> & Hpriv & Hmenv)".
    iApply (swp_mono _ (fun e : ExecutionResult => ⌜e = RETIRE_SUCCESS⌝%I) _
              with "[Hpriv Hmenv] []");
      [ iIntros (e) "->"; iSplitR; [done|]; iFrame |].
    repeat (match goal with
            | |- context [ if ?g then _ else _ ] =>
                lazymatch g with
                | true => fail
                | false => fail
                | _ => destruct g; cbn match
                end
            end);
      first [ iApply (swp_barrier_ret _ with "Hcert")
            | (* the model's fallback arm is [returnM tt], not a barrier *)
              iApply swp_ret; done ].
  Qed.

  (* ---- JAL / JALR at Supervisor: WpMmodeJump's four engines, over the
     S-mode cells ---- *)
  Lemma swp_execute_JAL_s (imm : SailStdpp.Values.mword 21)
      (rd : SailStdpp.Values.mword 5) (m : regfile)
      (pc npc0 : SailStdpp.Values.mword 64) :
    uint rd <> 0 ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) zerobit = true ->
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
    { iApply (swp_jump_to_s _ npc0 Halign with "Hcert HnPC Hmisa"). }
    iIntros (r) "(-> & HnPC & Hmisa)". cbn match.
    iApply (swp_bind0_use _ _ _ _ with "[Hf] [-]").
    { iApply (swp_wX_file rd m npc0 Hrd with "Hcert Hf"). }
    iIntros (u) "Hf". iApply swp_ret. iSplitR; [done|]. iFrame.
  Qed.

  Lemma swp_execute_JAL_zreg_s (imm : SailStdpp.Values.mword 21)
      (rdz : SailStdpp.Values.mword 5) (m : regfile)
      (pc npc0 : SailStdpp.Values.mword 64) :
    uint rdz = 0 ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) zerobit = true ->
    gen_cert -∗ gpr_file m -∗
    (R_bitvector_64 PC) ↦ᵣ pc -∗
    (R_bitvector_64 nextPC) ↦ᵣ npc0 -∗
    misa ↦ᵣ□ MISA_C -∗
    swp (execute (JAL (imm, Regidx rdz)))
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗ gpr_file m ∗
                (R_bitvector_64 PC) ↦ᵣ pc ∗
                (R_bitvector_64 nextPC) ↦ᵣ (add_vec pc (sign_extend' 64 imm)) ∗
                misa ↦ᵣ□ MISA_C).
  Proof.
    intros Hrdz Halign. iIntros "#Hcert Hf HPC HnPC Hmisa".
    change (execute (JAL (imm, Regidx rdz))) with (execute_JAL imm (Regidx rdz)).
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
    { iApply (swp_jump_to_s _ npc0 Halign with "Hcert HnPC Hmisa"). }
    iIntros (r) "(-> & HnPC & Hmisa)". cbn match.
    iApply (swp_bind0_use _ _ (fun _ => gpr_file m)%I _ with "[Hf] [-]").
    { iApply (swp_wX_zero rdz _ (gpr_file m) Hrdz with "Hf"). }
    iIntros (u) "Hf". iApply swp_ret. iSplitR; [done|]. iFrame.
  Qed.

  (* JALR, the general form: the elp gate + the link read are ONE first
     component of the outer bind ([m >> n >>= f] parses left-nested). *)
  Lemma swp_execute_JALR_s (imm : SailStdpp.Values.mword 12)
      (rs1 rd : SailStdpp.Values.mword 5) (m : regfile)
      (npc0 : SailStdpp.Values.mword 64) :
    uint rd <> 0 ->
    eq_vec (access_vec_dec
              (update_vec_dec
                 (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) 0 zerobit)
              0) zerobit = true ->
    gen_cert -∗ gpr_file m -∗
    (R_bitvector_64 nextPC) ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Supervisor -∗
    menvcfg ↦ᵣ MENVCFG_S -∗
    misa ↦ᵣ□ MISA_C -∗
    swp (execute (JALR (imm, Regidx rs1, Regidx rd)))
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                gpr_file (<[Regidx rd := regval_into_reg npc0]> m) ∗
                (R_bitvector_64 nextPC) ↦ᵣ
                  (update_vec_dec
                     (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) 0 zerobit) ∗
                cur_privilege ↦ᵣ Supervisor ∗ menvcfg ↦ᵣ MENVCFG_S ∗
                misa ↦ᵣ□ MISA_C).
  Proof.
    intros Hrd Halign. iIntros "#Hcert Hf HnPC Hpriv Hmenv Hmisa".
    change (execute (JALR (imm, Regidx rs1, Regidx rd)))
      with (execute_JALR imm (Regidx rs1) (Regidx rd)).
    unfold execute_JALR. cbn match.
    iApply (swp_bind_use
              (Defs.bind0 (update_elp_state (Regidx rs1)) (get_next_pc tt)) _
              (fun link => ⌜link = npc0⌝ ∗
                 (R_bitvector_64 nextPC) ↦ᵣ npc0 ∗
                 cur_privilege ↦ᵣ Supervisor ∗ menvcfg ↦ᵣ MENVCFG_S ∗
                 misa ↦ᵣ□ MISA_C)%I _
              with "[HnPC Hpriv Hmenv Hmisa] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ => (R_bitvector_64 nextPC) ↦ᵣ npc0 ∗
                   cur_privilege ↦ᵣ Supervisor ∗ menvcfg ↦ᵣ MENVCFG_S ∗
                   misa ↦ᵣ□ MISA_C)%I _
                with "[HnPC Hpriv Hmenv Hmisa] [-]").
      { iApply (swp_update_elp_state_S rs1 npc0
                  with "Hcert HnPC Hpriv Hmenv Hmisa"). }
      iIntros (u) "(HnPC & Hpriv & Hmenv & Hmisa)".
      unfold get_next_pc.
      iApply (swp_mono with "[Hpriv Hmenv Hmisa] [-]");
        [| iApply (swp_read_reg_cell (R_bitvector_64 nextPC) npc0
                     with "Hcert HnPC") ].
      iIntros (link) "[-> HnPC]". iSplitR; [done|]. iFrame. }
    iIntros (link) "(-> & HnPC & Hpriv & Hmenv & Hmisa)".
    iApply (swp_bind_use (rX_bits (Regidx rs1)) _ _ _ with "[Hf] [-]").
    { iApply (swp_rX_file rs1 m with "Hcert Hf"). }
    iIntros (w) "[-> Hf]".
    iApply (swp_bind_use _ _ _ _ with "[HnPC Hmisa] [-]").
    { iApply (swp_jump_to_s _ npc0 Halign with "Hcert HnPC Hmisa"). }
    iIntros (r) "(-> & HnPC & Hmisa)". cbn match.
    iApply (swp_bind0_use _ _ _ _ with "[Hf] [-]").
    { iApply (swp_wX_file rd m npc0 Hrd with "Hcert Hf"). }
    iIntros (u2) "Hf". iApply swp_ret. iSplitR; [done|]. iFrame.
  Qed.

  (* the c.ret form: rd = x0, imm = 0, target spelled [ret_pc] *)
  Lemma swp_execute_JALR_ret_s (ra rdz : SailStdpp.Values.mword 5)
      (m : regfile) (npc0 : SailStdpp.Values.mword 64) :
    uint rdz = 0 ->
    gen_cert -∗ gpr_file m -∗
    (R_bitvector_64 nextPC) ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Supervisor -∗
    menvcfg ↦ᵣ MENVCFG_S -∗
    misa ↦ᵣ□ MISA_C -∗
    swp (execute (JALR (zeros' 12, Regidx ra, Regidx rdz)))
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗ gpr_file m ∗
                (R_bitvector_64 nextPC) ↦ᵣ (ret_pc (m !!! Regidx ra)) ∗
                cur_privilege ↦ᵣ Supervisor ∗ menvcfg ↦ᵣ MENVCFG_S ∗
                misa ↦ᵣ□ MISA_C).
  Proof.
    intros Hrdz.
    (* the alignment side condition is [ret_pc]'s own construction, and it has
       to be POSED rather than passed as an [ltac:] inside the application:
       inside one, the goal still carries the application's evars. *)
    assert (Halign : eq_vec (access_vec_dec
              (update_vec_dec
                 (add_vec (m !!! Regidx ra) (sign_extend' 64 (zeros' 12))) 0
                 zerobit) 0) zerobit = true)
      by (rewrite ret_pc_jalr; apply ret_pc_aligned).
    iIntros "#Hcert Hf HnPC Hpriv Hmenv Hmisa".
    change (execute (JALR (zeros' 12, Regidx ra, Regidx rdz)))
      with (execute_JALR (zeros' 12) (Regidx ra) (Regidx rdz)).
    unfold execute_JALR. cbn match.
    iApply (swp_bind_use
              (Defs.bind0 (update_elp_state (Regidx ra)) (get_next_pc tt)) _
              (fun link => ⌜link = npc0⌝ ∗
                 (R_bitvector_64 nextPC) ↦ᵣ npc0 ∗
                 cur_privilege ↦ᵣ Supervisor ∗ menvcfg ↦ᵣ MENVCFG_S ∗
                 misa ↦ᵣ□ MISA_C)%I _
              with "[HnPC Hpriv Hmenv Hmisa] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ => (R_bitvector_64 nextPC) ↦ᵣ npc0 ∗
                   cur_privilege ↦ᵣ Supervisor ∗ menvcfg ↦ᵣ MENVCFG_S ∗
                   misa ↦ᵣ□ MISA_C)%I _
                with "[HnPC Hpriv Hmenv Hmisa] [-]").
      { iApply (swp_update_elp_state_S ra npc0
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
    { iApply (swp_jump_to_s _ npc0 Halign with "Hcert HnPC Hmisa"). }
    iIntros (r) "(-> & HnPC & Hmisa)". cbn match.
    iApply (swp_bind0_use _ _ (fun _ => gpr_file m)%I _ with "[Hf] [-]").
    { iApply (swp_wX_zero rdz _ (gpr_file m) Hrdz with "Hf"). }
    iIntros (u2) "Hf". iApply swp_ret. rewrite ret_pc_jalr.
    iSplitR; [done|]. iFrame.
  Qed.

End WpSconfCtlEng.

Section WpSconfEngine.
  Context `{!riscvGS Σ}.
  Context `{!xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {kt : ktier}.
  Context {p : mword 64}.

  (* [IntrDefs.tp_pin_sp] with the [rget] FOLDED, so a leaf reading sp can
     [rewrite] it: the engines' value premise is spelled [rget m rsa], and a
     leaf whose source is the concrete sp states its value at the plain map
     lookup.  The two are convertible; [rewrite] is syntactic. *)
  Lemma rget_sp (m : regfile) : rget m csp_rs1 = m !!! Regidx csp_rs1.
  Proof. exact (tp_pin_sp m). Qed.

  (* =================================================================== *)
  (* THE MASTER.  Encoding width [c] is a parameter; the capability moves  *)
  (* by a caller-supplied TRANSFORMER (so an sp-write is the same engine); *)
  (* and the PC cell the funnel lends is passed straight through to the    *)
  (* obligation (so AUIPC is the same engine too).  [ops_ok_sp] rather     *)
  (* than [ops_ok] -- rd MAY be sp here; the tp half and the whole read    *)
  (* side are identical.  Everything else in this file is an instance.     *)
  (* =================================================================== *)
  Lemma wp_gpr_write_s_sconf_gen
      (pc : mword 64) (c : bool) (rd rsa rsb : mword 5) (base : instruction)
      (f : mword 64 -> mword 64 -> mword 64) (wval : mword 64)
      (m : regfile) (n n' : nat) (P : iProp Σ) (b : bool) :
    uint rd <> 0 ->
    ops_ok_sp b rd rsa rsb ->
    f (rget m rsa) (rget m rsb) = wval ->
    (* THE INSTRUCTION'S OWN OBLIGATION, hart-generic and value-free: the walk
       reads whatever this hart's pin holds and writes [f] of it.  This is
       exactly what [WpMmodeSwpBase]'s node shapes conclude. *)
    (∀ CID : CpuId,
       gen_cert -∗ gpr_file (tp_pin m) -∗ (R_bitvector_64 PC) ↦ᵣ pc -∗
       swp (execute base)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
            gpr_file (<[Regidx rd := regval_into_reg
                          (f (tp_pin m !!! Regidx rsa)
                             (tp_pin m !!! Regidx rsb))]> (tp_pin m)) ∗
            (R_bitvector_64 PC) ↦ᵣ pc)) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc c base -∗
    ( ∀ CIDx : CpuId,
      sie_cap kt (CID := CIDx) m n b p -∗
      sie_cap kt (CID := CIDx) (<[Regidx rd := regval_into_reg wval]> m) n' b p ∗ P ) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n' b p -∗
      P -∗
      pc_is (add_vec_int pc (if c then 2 else 4)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hex Hcg Hpc Hinstr Hrecap Hcont".
    pose proof (ops_ok_sp_rd _ _ _ _ Hops) as Hrdtp.
    iApply (wp_instr_s_sconf m n b b pc c base
              (fun _ npc ms' m2 n2 =>
                 ⌜npc = add_vec_int pc (if c then 2 else 4)⌝ ∗
                 ⌜m2 = <[Regidx rd := regval_into_reg wval]> m⌝ ∗
                 ⌜n2 = n'⌝ ∗ P)%I
              with "Hcg Hpc Hinstr [Hex Hrecap Hcont]").
    iNext.
    (* FREE THE NAME [CID] FOR THE REBOUND HART -- the statement never sees
       the rename, so callers naming this engine's hart keep working. *)
    rename CID into CID0.
    iIntros (CID Hs). rewrite /sconf_step_obl. iSplitL "Hex Hrecap".
    - (* the instruction *)
      iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      iDestruct "Hsc" as "(#Hhw & #Hminv & Hsc)".
      iDestruct (hw_config_cert with "Hhw") as "#Hcert".
      (* THE ONE RECONCILIATION, and the reason this engine exists: the walk
         answers the two source reads at the REBOUND hart, while [Hwval] names
         them at the entry hart.  At [b = true] [ops_ok] says neither source is
         tp; at [b = false] the guard [Hs] pins the hart outright. *)
      pose proof (rget_next_indep (CID := CID0) b p CID m rsa Hs
                    (ops_ok_sp_s1 _ _ _ _ Hops)) as Hra.
      pose proof (rget_next_indep (CID := CID0) b p CID m rsb Hs
                    (ops_ok_sp_s2 _ _ _ _ Hops)) as Hrb.
      assert (Hval : f (tp_pin (CID := CID) m !!! Regidx rsa)
                       (tp_pin (CID := CID) m !!! Regidx rsb) = wval)
        by (unfold rget in Hra, Hrb; rewrite Hra Hrb; exact Hwval).
      iDestruct ("Hrecap" $! CID with "Hcap") as "[Hcap HP]".
      iDestruct ("Hex" $! CID with "Hcert Hfile HPC") as "Hexx".
      iApply (swp_mono (CID := CID) with "[Hsc Hcap HnPC Hresv HP] [Hexx]");
        [| iExact "Hexx" ].
      iIntros (e) "(-> & Hfile & HPC)".
      iSplitR; [done|].
      (* the funnel's post names the mstatus the instruction LEFT; this leaf
         family does not move it, so the witness comes straight back out of
         the bundle ([WpIntrInv.sconf_at_priv_open]). *)
      iAssert (sconf (CID := CID)) with "[Hsc]" as "Hsc2".
      { rewrite /sconf. iFrame "Hhw Hminv Hsc". }
      iDestruct (sconf_at_priv_open (CID := CID) with "Hsc2") as (ms') "Hscp".
      iExists (add_vec_int pc (if c then 2 else 4)), ms',
              (<[Regidx rd := regval_into_reg wval]> m), n'.
      iFrame "HPC HnPC Hresv Hscp".
      iSplitL "Hcap"; [ iExact "Hcap" |].
      iSplitL "Hfile".
      { iEval (rewrite Hval) in "Hfile".
        iEval (rewrite (tp_pin_upd m rd (regval_into_reg wval) Hrdtp))
          in "Hfile". iExact "Hfile". }
      iFrame "HP". done.
    - (* the continuation: the engine resumes on the hart [Hs] names *)
      iIntros (npc ms' m2 n2) "Hcg' Hpc' (-> & -> & -> & HP)".
      iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
      iApply ("Hcont" $! CID with "[%] Hcg' HP Hpc'"). exact Hs.
  Qed.

  (* THE PC-FREE OBLIGATION, the shape 99 % of the leaves want: the cell is
     framed across the walk here instead of at every call site. *)
  Lemma wp_gpr_write_s_sconf_cap_val_w
      (pc : mword 64) (c : bool) (rd rsa rsb : mword 5) (base : instruction)
      (f : mword 64 -> mword 64 -> mword 64) (wval : mword 64)
      (m : regfile) (n n' : nat) (P : iProp Σ) (b : bool) :
    uint rd <> 0 ->
    ops_ok_sp b rd rsa rsb ->
    f (rget m rsa) (rget m rsb) = wval ->
    (∀ CID : CpuId,
       gen_cert -∗ gpr_file (tp_pin m) -∗
       swp (execute base)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
            gpr_file (<[Regidx rd := regval_into_reg
                          (f (tp_pin m !!! Regidx rsa)
                             (tp_pin m !!! Regidx rsb))]> (tp_pin m)))) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc c base -∗
    ( ∀ CIDx : CpuId,
      sie_cap kt (CID := CIDx) m n b p -∗
      sie_cap kt (CID := CIDx) (<[Regidx rd := regval_into_reg wval]> m) n' b p ∗ P ) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n' b p -∗
      P -∗
      pc_is (add_vec_int pc (if c then 2 else 4)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hex Hcg Hpc Hinstr Hrecap Hcont".
    iApply (wp_gpr_write_s_sconf_gen pc c rd rsa rsb base f wval m n n' P b
              Hrd Hops Hwval with "[Hex] Hcg Hpc Hinstr Hrecap Hcont").
    iIntros (CIDn) "Hcert Hf HPC".
    iApply (swp_mono (CID := CIDn) with "[HPC] [-]");
      [| iApply ("Hex" $! CIDn with "Hcert Hf") ].
    iIntros (e) "[-> Hf]". iSplitR; [done|]. iFrame "Hf HPC".
  Qed.

  (* =================================================================== *)
  (* The ordinary (non-sp) engine: the capability is merely RETARGETED    *)
  (* across the write, which is what [rd_ok]'s sp conjunct buys.          *)
  (* =================================================================== *)
  Lemma wp_gpr_write_s_sconf_val_w
      (pc : mword 64) (c : bool) (rd rsa rsb : mword 5) (base : instruction)
      (f : mword 64 -> mword 64 -> mword 64) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rsa rsb ->
    f (rget m rsa) (rget m rsb) = wval ->
    (∀ CID : CpuId,
       gen_cert -∗ gpr_file (tp_pin m) -∗
       swp (execute base)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
            gpr_file (<[Regidx rd := regval_into_reg
                          (f (tp_pin m !!! Regidx rsa)
                             (tp_pin m !!! Regidx rsb))]> (tp_pin m)))) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc c base -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc (if c then 2 else 4)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hex Hcg Hpc Hinstr Hcont".
    pose proof (rd_ok_sp _ (ops_ok_rd _ _ _ _ Hops)) as Hrdsp.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg wval]> m !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
    iApply (wp_gpr_write_s_sconf_cap_val_w pc c rd rsa rsb base f wval m n n
              emp%I b Hrd (ops_ok_to_sp _ _ _ _ Hops) Hwval
              with "Hex Hcg Hpc Hinstr [] [Hcont]").
    - iIntros (CIDx) "Hcap". iSplitL; [| done].
      iApply (sie_cap_retarget (CID := CIDx) m
                (<[Regidx rd := regval_into_reg wval]> m) n b Hsp with "Hcap").
    - iIntros (CIDx Hs) "Hcg' _ Hpc'".
      iApply ("Hcont" $! CIDx with "[%] Hcg' Hpc'"). exact Hs.
  Qed.

  (* the two width instances every leaf actually names *)
  Lemma wp_gpr_write_s_sconf_val
      (pc : mword 64) (rd rsa rsb : mword 5) (base : instruction)
      (f : mword 64 -> mword 64 -> mword 64) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rsa rsb ->
    f (rget m rsa) (rget m rsb) = wval ->
    (∀ CID : CpuId,
       gen_cert -∗ gpr_file (tp_pin m) -∗
       swp (execute base)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
            gpr_file (<[Regidx rd := regval_into_reg
                          (f (tp_pin m !!! Regidx rsa)
                             (tp_pin m !!! Regidx rsb))]> (tp_pin m)))) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true base -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof. exact (wp_gpr_write_s_sconf_val_w pc true rd rsa rsb base f wval m n b). Qed.

  Lemma wp_gpr_write_s_sconf_val_base
      (pc : mword 64) (rd rsa rsb : mword 5) (base : instruction)
      (f : mword 64 -> mword 64 -> mword 64) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rsa rsb ->
    f (rget m rsa) (rget m rsb) = wval ->
    (∀ CID : CpuId,
       gen_cert -∗ gpr_file (tp_pin m) -∗
       swp (execute base)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
            gpr_file (<[Regidx rd := regval_into_reg
                          (f (tp_pin m !!! Regidx rsa)
                             (tp_pin m !!! Regidx rsb))]> (tp_pin m)))) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc false base -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof. exact (wp_gpr_write_s_sconf_val_w pc false rd rsa rsb base f wval m n b). Qed.

  (* the COMPRESSED cap engine -- the shape every sp-mover is built over *)
  Lemma wp_gpr_write_s_sconf_cap_val
      (pc : mword 64) (rd rsa rsb : mword 5) (base : instruction)
      (f : mword 64 -> mword 64 -> mword 64) (wval : mword 64)
      (m : regfile) (n n' : nat) (P : iProp Σ) (b : bool) :
    uint rd <> 0 ->
    ops_ok_sp b rd rsa rsb ->
    f (rget m rsa) (rget m rsb) = wval ->
    (∀ CID : CpuId,
       gen_cert -∗ gpr_file (tp_pin m) -∗
       swp (execute base)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
            gpr_file (<[Regidx rd := regval_into_reg
                          (f (tp_pin m !!! Regidx rsa)
                             (tp_pin m !!! Regidx rsb))]> (tp_pin m)))) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true base -∗
    ( ∀ CIDx : CpuId,
      sie_cap kt (CID := CIDx) m n b p -∗
      sie_cap kt (CID := CIDx) (<[Regidx rd := regval_into_reg wval]> m) n' b p ∗ P ) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n' b p -∗
      P -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    exact (wp_gpr_write_s_sconf_cap_val_w pc true rd rsa rsb base f wval m n n' P b).
  Qed.

  (* THE PC-READING ENGINE (auipc): the funnel's own PC cell, lent to the
     obligation and taken back.  [f] ignores its arguments at every current
     call site -- the value is a function of [pc] -- but it is kept for
     uniformity with the rest of the family. *)
  Lemma wp_gpr_write_s_sconf_pc_val_base
      (pc : mword 64) (rd rsa rsb : mword 5) (base : instruction)
      (f : mword 64 -> mword 64 -> mword 64) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rsa rsb ->
    f (rget m rsa) (rget m rsb) = wval ->
    (∀ CID : CpuId,
       gen_cert -∗ gpr_file (tp_pin m) -∗ (R_bitvector_64 PC) ↦ᵣ pc -∗
       swp (execute base)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
            gpr_file (<[Regidx rd := regval_into_reg
                          (f (tp_pin m !!! Regidx rsa)
                             (tp_pin m !!! Regidx rsb))]> (tp_pin m)) ∗
            (R_bitvector_64 PC) ↦ᵣ pc)) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc false base -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hex Hcg Hpc Hinstr Hcont".
    pose proof (rd_ok_sp _ (ops_ok_rd _ _ _ _ Hops)) as Hrdsp.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg wval]> m !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
    iApply (wp_gpr_write_s_sconf_gen pc false rd rsa rsb base f wval m n n
              emp%I b Hrd (ops_ok_to_sp _ _ _ _ Hops) Hwval
              with "Hex Hcg Hpc Hinstr [] [Hcont]").
    - iIntros (CIDx) "Hcap". iSplitL; [| done].
      iApply (sie_cap_retarget (CID := CIDx) m
                (<[Regidx rd := regval_into_reg wval]> m) n b Hsp with "Hcap").
    - iIntros (CIDx Hs) "Hcg' _ Hpc'".
      iApply ("Hcont" $! CIDx with "[%] Hcg' Hpc'"). exact Hs.
  Qed.

  (* ================================================================== *)
  (* §3 THE TWO BRANCH FUNNELS.  A branch writes no GPR, so [sie_cap]    *)
  (* and the file pass through untouched and the only thing that moves   *)
  (* is nextPC (the taken arm).  The comparison premise is the ALL-HARTS *)
  (* form -- that is what a leaf's [SrcOk] classes buy it, and the       *)
  (* reason it is a premise here rather than a class is that the engine  *)
  (* has no register argument for a class to attach to.                  *)
  (* ================================================================== *)
  Lemma wp_btype_fall_s_sconf
      (pc : mword 64) (c : bool) (imm : mword 13) (rs2 rs1 : mword 5)
      (i : instruction)
      (cmp : mword 64 -> mword 64 -> bool)
      (m : regfile) (n : nat) (b : bool) :
    execute i = btype_body imm rs2 rs1 cmp ->
    (* THE COMPARISON, at whatever hart the funnel resumes on, and stated
       AGAINST THE FILE rather than purely: a branch on x0 reads index 0,
       whose value is [zero_reg] only because [gpr_file] says so
       ([WpGpr.gpr_file_x0]).  A leaf whose operands are ordinary registers
       supplies this from its own premise and its [SrcOk] classes and gives
       the file straight back. *)
    (∀ hh : CpuId, gpr_file (CID := hh) (tp_pin (CID := hh) m) -∗
       ⌜cmp (rget (CID := hh) m rs1) (rget (CID := hh) m rs2) = false⌝ ∗
       gpr_file (CID := hh) (tp_pin (CID := hh) m)) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc c i -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec_int pc (if c then 2 else 4)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hred) "Hcmp Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b b pc c i
              (fun _ npc ms' m2 n2 =>
                 ⌜npc = add_vec_int pc (if c then 2 else 4)⌝ ∗
                 ⌜m2 = m⌝ ∗ ⌜n2 = n⌝)%I
              with "Hcg Hpc Hinstr [Hcmp Hcont]").
    iNext. rename CID into CID0.
    iIntros (CID Hs). rewrite /sconf_step_obl. iSplitR "Hcont".
    - iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      iDestruct "Hsc" as "(#Hhw & #Hminv & Hsc)".
      iDestruct (hw_config_cert with "Hhw") as "#Hcert".
      iDestruct ("Hcmp" $! CID with "Hfile") as "[%Hc0 Hfile]".
      iApply (swp_mono (CID := CID) with "[Hsc Hcap HPC HnPC Hresv] [Hfile]");
        [| iApply (swp_execute_BTYPE_fall (CID := CID) imm rs2 rs1
                     (tp_pin (CID := CID) m) (execute i) cmp Hred
                     Hc0 with "Hcert Hfile") ].
      iIntros (e) "[-> Hfile]". iSplitR; [done|].
      iAssert (sconf (CID := CID)) with "[Hsc]" as "Hsc2".
      { rewrite /sconf. iFrame "Hhw Hminv Hsc". }
      iDestruct (sconf_at_priv_open (CID := CID) with "Hsc2") as (ms') "Hscp".
      iExists (add_vec_int pc (if c then 2 else 4)), ms', m, n.
      iFrame "HPC HnPC Hresv Hscp Hcap Hfile". done.
    - iIntros (npc ms' m2 n2) "Hcg' Hpc' (-> & -> & ->)".
      iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
      iApply ("Hcont" $! CID with "[%] Hcg' Hpc'"). exact Hs.
  Qed.

  Lemma wp_btype_taken_s_sconf
      (pc : mword 64) (c : bool) (imm : mword 13) (rs2 rs1 : mword 5)
      (i : instruction)
      (cmp : mword 64 -> mword 64 -> bool)
      (m : regfile) (n : nat) (b : bool) :
    execute i = btype_body imm rs2 rs1 cmp ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) zerobit = true ->
    (* the comparison, against the file -- see the fall-through engine *)
    (∀ hh : CpuId, gpr_file (CID := hh) (tp_pin (CID := hh) m) -∗
       ⌜cmp (rget (CID := hh) m rs1) (rget (CID := hh) m rs2) = true⌝ ∗
       gpr_file (CID := hh) (tp_pin (CID := hh) m)) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc c i -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n b p -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hred Hal0) "Hcmp Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b b pc c i
              (fun _ npc ms' m2 n2 => ⌜npc = add_vec pc (sign_extend' 64 imm)⌝ ∗
                                      ⌜m2 = m⌝ ∗ ⌜n2 = n⌝)%I
              with "Hcg Hpc Hinstr [Hcmp Hcont]").
    iNext. rename CID into CID0.
    iIntros (CID Hs). rewrite /sconf_step_obl. iSplitR "Hcont".
    - iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      iDestruct "Hsc" as "(#Hhw & #Hminv & Hsc)".
      iDestruct (hw_config_cert with "Hhw") as "#Hcert".
      iDestruct (hw_config_misa with "Hhw") as "#Hmisa".
      iDestruct ("Hcmp" $! CID with "Hfile") as "[%Hc0 Hfile]".
      iApply (swp_mono (CID := CID) with "[Hsc Hcap Hresv] [Hfile HPC HnPC]");
        [| iApply (swp_execute_BTYPE_taken (CID := CID) imm rs2 rs1
                     (tp_pin (CID := CID) m) (execute i) pc
                     (add_vec_int pc (if c then 2 else 4)) cmp Hred
                     Hc0 Hal0 with "Hcert Hfile HPC HnPC Hmisa") ].
      iIntros (e) "(-> & Hfile & HPC & HnPC & _)". iSplitR; [done|].
      iAssert (sconf (CID := CID)) with "[Hsc]" as "Hsc2".
      { rewrite /sconf. iFrame "Hhw Hminv Hsc". }
      iDestruct (sconf_at_priv_open (CID := CID) with "Hsc2") as (ms') "Hscp".
      iExists (add_vec pc (sign_extend' 64 imm)), ms', m, n.
      iFrame "HPC HnPC Hresv Hscp Hcap Hfile". done.
    - iIntros (npc ms' m2 n2) "Hcg' Hpc' (-> & -> & ->)".
      iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
      iApply ("Hcont" $! CID with "[%] Hcg' Hpc'"). exact Hs.
  Qed.

  (* ================================================================== *)
  (* §5 THE GENERAL S-MODE STEP ENGINE, for the leaves that are not a    *)
  (* gpr write and not a branch: fences and the jumps.  It hands the     *)
  (* obligation [sconf] WHOLE (a fence reads cur_privilege + menvcfg, a  *)
  (* jump reads misa, and all three live there) plus the file and the    *)
  (* two pc cells, and takes back a post-file, a post-nextPC and the     *)
  (* capability moved by the caller's transformer.                      *)
  (* ================================================================== *)
  Lemma wp_instr_s_gen
      (pc npc : mword 64) (c : bool) (i : instruction)
      (m m' : regfile) (n n' : nat) (b : bool) (P : iProp Σ) :
    (∀ CID : CpuId,
       sconf -∗ gpr_file (tp_pin m) -∗
       (R_bitvector_64 PC) ↦ᵣ pc -∗
       (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc (if c then 2 else 4)) -∗
       swp (execute i)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗ sconf ∗ gpr_file (tp_pin m') ∗
            (R_bitvector_64 PC) ↦ᵣ pc ∗ (R_bitvector_64 nextPC) ↦ᵣ npc)) -∗
    ( ∀ CIDx : CpuId,
      sie_cap kt (CID := CIDx) m n b p -∗
      sie_cap kt (CID := CIDx) m' n' b p ∗ P ) -∗
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc c i -∗
    ▷ wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m' n' b p -∗ P -∗ pc_is npc -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "Hex Hrecap Hcg Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b b pc c i
              (fun _ npc2 ms' m2 n2 =>
                 ⌜npc2 = npc⌝ ∗ ⌜m2 = m'⌝ ∗ ⌜n2 = n'⌝ ∗ P)%I
              with "Hcg Hpc Hinstr [Hex Hrecap Hcont]").
    iNext. rename CID into CID0.
    iIntros (CID Hs). rewrite /sconf_step_obl. iSplitL "Hex Hrecap".
    - iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      iDestruct ("Hrecap" $! CID with "Hcap") as "[Hcap HP]".
      iDestruct ("Hex" $! CID with "Hsc Hfile HPC HnPC") as "Hexx".
      iApply (swp_mono (CID := CID) with "[Hcap Hresv HP] [Hexx]");
        [| iExact "Hexx" ].
      iIntros (e) "(-> & Hsc & Hfile & HPC & HnPC)".
      iSplitR; [done|].
      iDestruct (sconf_at_priv_open (CID := CID) with "Hsc") as (ms') "Hscp".
      iExists npc, ms', m', n'.
      iFrame "HPC HnPC Hresv Hscp Hcap Hfile HP". done.
    - iIntros (npc2 ms' m2 n2) "Hcg' Hpc' (-> & -> & -> & HP)".
      iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
      iApply ("Hcont" $! CID with "[%] Hcg' HP Hpc'"). exact Hs.
  Qed.

  (* everything a fence or a jump needs out of [sconf], with the two
     EXCLUSIVE cells borrowed and a wand that puts them back *)
  Lemma sconf_ctl_acc :
    sconf -∗ gen_cert ∗ misa ↦ᵣ□ MISA_C ∗
      cur_privilege ↦ᵣ Supervisor ∗ menvcfg ↦ᵣ MENVCFG_S ∗
      (cur_privilege ↦ᵣ Supervisor -∗ menvcfg ↦ᵣ MENVCFG_S -∗ sconf).
  Proof.
    iIntros "(#Hhw & #Hminv & Hpriv & Hms & Hmie & Hmenvx)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iDestruct (hw_config_misa with "Hhw") as "#Hmisa".
    iDestruct "Hmenvx" as (menvcfg0)
      "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hval)".
    subst menvcfg0.
    iSplitR; [ iExact "Hcert" |].
    iSplitR; [ iExact "Hmisa" |].
    iSplitL "Hpriv"; [ iExact "Hpriv" |].
    iSplitL "Hmenv"; [ iExact "Hmenv" |].
    iIntros "Hpriv Hmenv".
    iFrame "Hhw Hminv Hpriv Hms Hmie".
    iExists MENVCFG_S. iFrame "Hmenv". iPureIntro.
    repeat split; try assumption; reflexivity.
  Qed.

  (* A LEAF THAT HANDS ITS CALLER THE STEP'S LATER states it INSIDE the
     [wp_next] binder; the funnel wants it outermost.  The two are the same
     proposition: [▷] commutes with [∀], and the guard is PURE, so it
     commutes with that wand too. *)
  Lemma wp_next_later (b : bool) (pv : mword 64) (K : CpuId -> iProp Σ) :
    wp_next b pv (fun CIDx => ▷ K CIDx) -∗ ▷ wp_next b pv K.
  Proof.
    rewrite /wp_next. iIntros "H".
    rewrite bi.later_forall. iIntros (CIDx). iSpecialize ("H" $! CIDx).
    rewrite !bi.pure_wand_forall bi.later_forall. iExact "H".
  Qed.

End WpSconfEngine.
