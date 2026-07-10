(* WpAuipc.v -- the AUIPC opcode: execute reduction, forward_exec_auipc, wp_step_auipc. *)
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch.
Require Import MinstretInv.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.
Import Defs.


Lemma exec_get_arch_pc s :
  exec (get_arch_pc tt) s = Some (register_lookup PC s.(sregs), s).
Proof. unfold get_arch_pc. exact (exec_read_reg PC s). Qed.

(* --- execute (UTYPE imm rd AUIPC): read PC, add imm<<12, write rd, retire. --- *)
Definition auipc_off (imm : mword 20) : mword 64 :=
  sign_extend' 64 (concat_vec imm (Ox"000")).

Lemma exec_execute_UTYPE_AUIPC (i : mword 5) (imm : mword 20) s :
  uint i = 2 ->
  exec (execute_UTYPE imm (Regidx i) AUIPC) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 x2)
            (regval_into_reg
               (add_vec (register_lookup PC s.(sregs)) (auipc_off imm)))).
Proof.
  intro Hi.
  unfold execute_UTYPE, auipc_off. cbn match.
  rewrite (exec_bind_Some _ _ _
             (add_vec (register_lookup PC s.(sregs))
                      (sign_extend' 64 (concat_vec imm (Ox"000")))) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_get_arch_pc s)). apply exec_returnm. }
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_x2 i s _ Hi)). apply exec_returnm.
Qed.

(* ---------------------------------------------------------------------- *)
(* forward_exec_auipc: thread the generic try_step wrapper + the generic    *)
(* run_hart_active progress engine around the AUIPC execute leaf.           *)
(* Hypotheses mirror forward_exec_final's: universally-quantified fetch /    *)
(* decode / should_inc facts + booting-Machine register conditions.         *)
(* ---------------------------------------------------------------------- *)

Section ForwardAUIPC.
  Context (s : mstate) (w : mword 32) (pc : mword 64) (imm : mword 20)
          (i : mword 5) (b : bool).

  Hypothesis Hi : uint i = 2.
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hdec_gen : forall s0 : mstate,
    register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (UTYPE (imm, Regidx i, AUIPC), s0).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).

  Definition sAa : mstate := set_reg s (R_bool minstret_increment) b.
  Definition sXa : mstate :=
    let s1 := set_reg sAa nextPC (add_vec_int pc 4) in
    set_reg s1 (R_bitvector_64 x2)
      (regval_into_reg (add_vec (register_lookup PC s1.(sregs)) (auipc_off imm))).
  Definition sTa : mstate := set_reg sXa PC (register_lookup nextPC sXa.(sregs)).
  Definition sFa : mstate :=
    if b then set_reg sTa minstret
                  (add_vec_int (register_lookup minstret sTa.(sregs)) 1)
         else sTa.

  Lemma forward_exec_auipc :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFa).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp.
    (* booting-config reads transfer through the minstret_increment write. *)
    assert (LpcA  : register_lookup PC sAa.(sregs) = pc).
    { unfold sAa, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sAa.(sregs) = Machine).
    { unfold sAa, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sAa.(sregs) = HART_ACTIVE tt).
    { unfold sAa, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa sAa.(sregs))) ('b"1") = true).
    { unfold sAa, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LS | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE
              (register_lookup (R_bitvector_64 mstatus) sAa.(sregs))) ('b"1") = false).
    { unfold sAa, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAa.(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAa, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lelp | vm_compute; reflexivity ]. }
    (* dispatchInterrupt = None at sAa via the getPendingSet keystone;
       currentlyEnabled Ext_S reduces for any state (exec_currentlyEnabled_S). *)
    assert (HdispA : exec (dispatchInterrupt Machine) sAa = Some (None, sAa)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAa _ (exec_currentlyEnabled_S sAa) LSA LmIEA). }
    (* fetch / decode at sAa (state-preserving). *)
    assert (HfetchA : exec (fetch tt) sAa = Some (F_Base w, sAa))
      by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sAa = Some (UTYPE (imm, Regidx i, AUIPC), sAa))
      by (apply Hdec_gen; exact LprivA).
    (* execute leaf at s_pc = set_reg sAa nextPC (pc+4). *)
    pose (s_pc := set_reg sAa nextPC (add_vec_int pc 4)).
    assert (HpcPCpc : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LpcA | vm_compute; reflexivity ]. }
    assert (HexecA : exec (execute (UTYPE (imm, Regidx i, AUIPC))) s_pc
              = Some (RETIRE_SUCCESS, sXa)).
    { change (execute (UTYPE (imm, Regidx i, AUIPC)))
        with (execute_UTYPE imm (Regidx i) AUIPC).
      unfold sXa. fold s_pc.
      exact (exec_execute_UTYPE_AUIPC i imm s_pc Hi). }
    (* the run_hart_active reduction (exact value) via the generic engine. *)
    assert (Hha : exec (run_hart_active 0) sAa
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXa)).
    { exact (exec_hart_active_progress sAa sAa sXa sAa w
               (UTYPE (imm, Regidx i, AUIPC)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecA I). }
    (* the generic try_step wrapper. *)
    apply (exec_riscv_step_ADD s sXa w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - (* hart_state at sXa = HART_ACTIVE tt *)
      unfold sXa, sAa; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - (* minstret_increment at sXa = b *)
      unfold sXa, sAa; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity. (* Hrvfi : get_config_rvfi tt = false -- definitional *)
  Qed.

  (* clean-form post-state (concrete values). *)
  Variable mst0 : mword 64.
  Hypothesis Lmst_a : register_lookup minstret s.(sregs) = mst0.

  Definition base_upd_a : mstate :=
    set_reg (set_reg (set_reg (set_reg s (R_bool minstret_increment) b)
                              nextPC (add_vec_int pc 4))
                     (R_bitvector_64 x2) (regval_into_reg (add_vec pc (auipc_off imm))))
            PC (add_vec_int pc 4).
  Definition sFca : mstate :=
    if b then set_reg base_upd_a minstret (add_vec_int mst0 1)
         else base_upd_a.

  Ltac tmiss := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

  Lemma sFa_eq : register_lookup PC s.(sregs) = pc -> sFa = sFca.
  Proof.
    intro LpcS.
    assert (Enpc : register_lookup nextPC sXa.(sregs) = add_vec_int pc 4).
    { unfold sXa; cbv zeta. unfold set_reg; cbn [sregs]. tmiss.
      rewrite register_lookup_set. reflexivity. }
    assert (Epc1 : register_lookup PC (set_reg sAa nextPC (add_vec_int pc 4)).(sregs) = pc).
    { unfold sAa, set_reg; cbn [sregs]. tmiss. tmiss. exact LpcS. }
    assert (HsT : sTa = base_upd_a).
    { unfold sTa. rewrite Enpc. unfold sXa; cbv zeta. rewrite Epc1.
      unfold regval_into_reg, base_upd_a, sAa. reflexivity. }
    unfold sFa, sFca. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_a.(sregs) = register_lookup minstret s.(sregs)).
    { unfold base_upd_a, set_reg; cbn [sregs]. tmiss. tmiss. tmiss. tmiss. reflexivity. }
    rewrite Emst Lmst_a. reflexivity.
  Qed.

End ForwardAUIPC.

Section StepAUIPC.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context {dqc : dfrac}.

  (* ---------------------------------------------------------------------- *)
  (* Single-step WP for `ld rd,imm(rs1)` (rs1=rd=x2), via wp_exec_step +     *)
  (* forward_exec_ld + sFl_eq, discharging Hexec_spc via exec_execute_LOAD_8.*)
  (* ---------------------------------------------------------------------- *)
End StepAUIPC.
