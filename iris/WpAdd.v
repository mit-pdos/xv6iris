(* WpAdd.v -- the ADD opcode: forward_exec_final + wp_add_real_final. *)
From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Local Open Scope Z_scope.

(* ===== RiscvModelFinalWP ===== *)
(* ====================================================================== *)
(* RiscvModelFinalWP.v                                                     *)
(*                                                                         *)
(* THE capstone: wp_add_real_final -- an Iris WP for `add a2,a0,a1` through *)
(* the real Sail try_step, with Hne DISCHARGED at the quantified state via *)
(* exec_hart_active_done (NOT the over-strong unconditional Hne_gen).       *)
(* Remaining genuine assumptions: Hdec (decode wall) + reducible geometric. *)
(* ====================================================================== *)



Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Step 1: exec_currentlyEnabled_S -- exec twin of run_currentlyEnabled_S. *)
(* Supplies HecES for exec_hart_active_done.                               *)
(* ---------------------------------------------------------------------- *)

Lemma exec_hartSupports_S s : exec (hartSupports Ext_S) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_S) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  apply exec_returnM.
Qed.

Lemma exec_hartSupports_Zicsr s : exec (hartSupports Ext_Zicsr) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zicsr) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  apply exec_returnM.
Qed.

Lemma exec_rec_cE_Zicsr s (acc : Acc (Zwf 0) 0) :
  exec (_rec_currentlyEnabled Ext_Zicsr 0 acc) s = Some (true, s).
Proof.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb 0 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  apply exec_hartSupports_Zicsr.
Qed.

Lemma exec_currentlyEnabled_S s :
  exec (currentlyEnabled Ext_S) s
    = Some (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1"), s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_S) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  (* outer and_boolM (hartSupports Ext_S = true) INNER *)
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_S s)).
  (* INNER = and_boolM (read misa; misa.S check) (cE Ext_Zicsr) *)
  rewrite (exec_and_boolM_Some _ _ s
             (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa s)). apply exec_returnM. }
  destruct (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) eqn:Hb.
  - apply exec_rec_cE_Zicsr.
  - reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* Step 2: the capstone WP, with Hne DERIVED via exec_hart_active_done.    *)
(* ---------------------------------------------------------------------- *)

Ltac trans_mi := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

Section FinalWP.
  Context `{!riscvGS Σ}.
  Context (b : bool) (pc a0 a1 mst0 npc v2old : mword 64) (mi0 : bool)
          (w : mword 32) (rs2 rs1 rd : mword 5).

  Definition sA (s : mstate) : mstate := set_reg s (R_bool minstret_increment) b.
  Definition sX (s : mstate) : mstate :=
    let s1 := set_reg (sA s) nextPC (add_vec_int pc 4) in
    set_reg s1 (R_bitvector_64 x12)
       (regval_into_reg
          (add_vec (register_lookup (R_bitvector_64 x10) s1.(sregs))
                   (register_lookup (R_bitvector_64 x11) s1.(sregs)))).
  Definition sT (s : mstate) : mstate :=
    set_reg (sX s) PC (register_lookup nextPC (sX s).(sregs)).
  Definition sF (s : mstate) : mstate :=
    if b then set_reg (sT s) minstret
                      (add_vec_int (register_lookup minstret (sT s).(sregs)) 1)
         else sT s.

  (* fetch/decode facts, stated once at the EXEC level; the relational [run]
     twins needed by run_hart_active_ADD are derived on the spot via
     [exec_run_det] (exec = Some -> run), so no separate run hypotheses. *)
  Hypothesis Hfetch_exec_gen : forall s : mstate,
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    exec (fetch tt) s = Some (F_Base w, s).
  Hypothesis Hdec_exec_gen : forall s : mstate,
    exec (ext_decode w) s = Some (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD), s).
  Hypothesis Hsi_gen : forall s : mstate,
    register_lookup cur_privilege s.(sregs) = Machine ->
    exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrs1 : uint rs1 = 10.
  Hypothesis Hrs2 : uint rs2 = 11.
  Hypothesis Hrd  : uint rd  = 12.
  Hypothesis Hrvfi : get_config_rvfi tt = false.

  Lemma forward_exec_final (s : mstate) :
    register_lookup (R_bitvector_64 x10) s.(sregs) = a0 ->
    register_lookup (R_bitvector_64 x11) s.(sregs) = a1 ->
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    register_lookup (R_bitvector_64 mideleg) s.(sregs) = zeros' 64 ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sF s).
  Proof using All.
    intros Lx10 Lx11 Lpc Lmst Lpriv Lhs Lmideleg LmIE Lelp.
    (* Hne at sA s via exec_hart_active_done. *)
    assert (Hne_at : exec (run_hart_active 0) (sA s) <> None).
    { apply (exec_hart_active_done (sA s) pc w rs1 rs2 rd
               (eq_vec (_get_Misa_S (register_lookup misa (sA s).(sregs))) ('b"1"))).
      - exact Hrs1.
      - exact Hrs2.
      - exact Hrd.
      - unfold sA; trans_mi; exact Lpriv.
      - unfold sA; trans_mi; exact Lpc.
      - apply exec_currentlyEnabled_S.
      - unfold sA; trans_mi; exact Lmideleg.
      - unfold sA; trans_mi; exact LmIE.
      - apply Hfetch_exec_gen; [ unfold sA; trans_mi; exact Lpc | unfold sA; trans_mi; exact Lpriv ].
      - apply Hdec_exec_gen.
      - unfold sA; trans_mi; exact Lelp. }
    (* Hpend at sA s via the keystone. *)
    assert (HpendA : run (getPendingSet Machine) (sA s) None (sA s)).
    { apply (run_getPendingSet_machine_none (sA s) _ (run_currentlyEnabled_S (sA s))).
      - unfold sA. trans_mi. exact Lmideleg.
      - unfold sA. trans_mi. exact LmIE. }
    (* Hha at sA s via exec_hart_active_ADD, with Hne supplied by exec_hart_active_done. *)
    assert (Hha : exec (run_hart_active 0) (sA s)
                  = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sX s)).
    { unfold sX.
      apply (exec_hart_active_ADD (sA s) w pc rs2 rs1 rd); try assumption.
      - unfold sA; trans_mi; exact Lpriv.
      - unfold sA; trans_mi; exact Lpc.
      - unfold sA; trans_mi; exact Lelp.
      - apply (proj1 (exec_run_det _ _ _ _
                 (Hfetch_exec_gen (sA s)
                    ltac:(unfold sA; trans_mi; exact Lpc)
                    ltac:(unfold sA; trans_mi; exact Lpriv)))).
      - apply (proj1 (exec_run_det _ _ _ _ (Hdec_exec_gen (sA s)))). }
    apply (exec_riscv_step_ADD s (sX s) w b pc).
    - exact Lpriv.
    - apply Hsi_gen; exact Lpriv.
    - unfold sA; trans_mi; exact Lhs.
    - exact Hha.
    - unfold sX, sA. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sX, sA. trans_mi. trans_mi. rewrite register_lookup_set. reflexivity.
    - exact Hrvfi.
  Qed.

  Definition mst_final : mword 64 := if b then add_vec_int mst0 1 else mst0.

  Definition base_upd (s : mstate) : mstate :=
    set_reg
      (set_reg
        (set_reg
          (set_reg s (R_bool minstret_increment) b)
          nextPC (add_vec_int pc 4))
        (R_bitvector_64 x12) (add_vec a0 a1))
      PC (add_vec_int pc 4).

  Definition sFc (s : mstate) : mstate :=
    if b then set_reg (base_upd s) minstret (add_vec_int mst0 1) else base_upd s.

  Ltac tmiss := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

  Lemma sF_eq (s : mstate) :
    register_lookup (R_bitvector_64 x10) s.(sregs) = a0 ->
    register_lookup (R_bitvector_64 x11) s.(sregs) = a1 ->
    register_lookup minstret s.(sregs) = mst0 ->
    sF s = sFc s.
  Proof using All.
    intros Lx10 Lx11 Lmst.
    assert (E10 : register_lookup (R_bitvector_64 x10)
                    (set_reg (sA s) nextPC (add_vec_int pc 4)).(sregs) = a0).
    { unfold sA, set_reg; cbn [sregs]. tmiss. tmiss. exact Lx10. }
    assert (E11 : register_lookup (R_bitvector_64 x11)
                    (set_reg (sA s) nextPC (add_vec_int pc 4)).(sregs) = a1).
    { unfold sA, set_reg; cbn [sregs]. tmiss. tmiss. exact Lx11. }
    assert (Enpc : register_lookup nextPC (sX s).(sregs) = add_vec_int pc 4).
    { unfold sX; cbv zeta. unfold sA, set_reg; cbn [sregs]. tmiss.
      rewrite register_lookup_set. reflexivity. }
    assert (HsT : sT s = base_upd s).
    { unfold sT. rewrite Enpc. unfold sX; cbv zeta. rewrite E10 E11.
      unfold regval_into_reg, base_upd, sA. reflexivity. }
    unfold sF, sFc. rewrite HsT. destruct b; [ | reflexivity ].
    assert (Emst : register_lookup minstret (base_upd s).(sregs) = mst0).
    { unfold base_upd, sA, set_reg; cbn [sregs]. tmiss. tmiss. tmiss. tmiss. exact Lmst. }
    rewrite Emst. reflexivity.
  Qed.

  Lemma wp_add_real_final
      (mstatus0 : mword 64) (elp0 : mword 1) E (Φ : mval -> iProp Σ) :
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    (R_bitvector_64 x10) ↦ᵣ a0 -∗
    (R_bitvector_64 x11) ↦ᵣ a1 -∗
    (R_bitvector_64 x12) ↦ᵣ v2old -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗
    minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗
    (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗
    ▷ ( (R_bitvector_64 x10) ↦ᵣ a0 -∗
        (R_bitvector_64 x11) ↦ᵣ a1 -∗
        (R_bitvector_64 x12) ↦ᵣ (add_vec a0 a1) -∗
        PC ↦ᵣ (add_vec_int pc 4) -∗
        nextPC ↦ᵣ (add_vec_int pc 4) -∗
        (R_bool minstret_increment) ↦ᵣ b -∗
        minstret ↦ᵣ mst_final -∗
        cur_privilege ↦ᵣ Machine -∗
        hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗
        (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof using All.
    iIntros (HmIE0 Help0)
      "Hx10 Hx11 Hx12 Hpc Hnpc Hmi Hmst Hpriv Hhs Hmdl Hmst' Help Hcont".
    iApply wp_exec_step.
    iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hx10")  as %Lx10.
    iDestruct (reg_valid with "Hreg Hx11")  as %Lx11.
    iDestruct (reg_valid with "Hreg Hpc")   as %Lpc.
    iDestruct (reg_valid with "Hreg Hmst")  as %Lmst.
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")   as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")  as %Lmdl.
    iDestruct (reg_valid with "Hreg Hmst'") as %Lmst2.
    iDestruct (reg_valid with "Hreg Help")  as %Lelp.
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iExists (sFc s). iSplitR.
    { iPureIntro. rewrite <- (sF_eq s Lx10 Lx11 Lmst).
      apply forward_exec_final; try assumption.
      - rewrite Lmst2. exact HmIE0.
      - rewrite Lelp. exact Help0. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi")  as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 x12) _ (add_vec a0 a1) with "Hreg Hx12") as "[Hreg Hx12]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    unfold sFc, base_upd, mst_final.
    destruct b.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro.
      unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hx10 Hx11 Hx12 Hpc Hnpc Hmi Hmst Hpriv Hhs Hmdl Hmst' Help").
    - iMod "Hclose" as "_". iModIntro.
      unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hx10 Hx11 Hx12 Hpc Hnpc Hmi Hmst Hpriv Hhs Hmdl Hmst' Help").
  Qed.

End FinalWP.

