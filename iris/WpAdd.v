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
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec WpFetch.
Require Import MinstretInv.
From iris.base_logic.lib Require Import invariants.
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
  Context {dqc : dfrac}.
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
    exec (fetch tt) (sA s) = Some (F_Base w, sA s) ->
    register_lookup (R_bitvector_64 x10) s.(sregs) = a0 ->
    register_lookup (R_bitvector_64 x11) s.(sregs) = a1 ->
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sF s).
  Proof using All.
    intros Hfetch_at Lx10 Lx11 Lpc Lpriv Lhs LS LmIE Lelp.
    (* dispatchInterrupt -> None at sA s via the misa.S keystone (mideleg-agnostic). *)
    assert (HdispA : exec (dispatchInterrupt Machine) (sA s) = Some (None, sA s)).
    { apply exec_dispatchInterrupt_none.
      assert (LSA : eq_vec (_get_Misa_S (register_lookup misa (sA s).(sregs))) ('b"1") = true)
        by (unfold sA; trans_mi; exact LS).
      assert (LmIEA : eq_vec (_get_Mstatus_MIE
                (register_lookup (R_bitvector_64 mstatus) (sA s).(sregs))) ('b"1") = false)
        by (unfold sA; trans_mi; exact LmIE).
      apply (exec_getPendingSet_machine_none (sA s) _ (exec_currentlyEnabled_S (sA s)) LSA LmIEA). }
    (* Hha at sA s via exec_hart_active_progress (no Hne precondition, mideleg-free). *)
    assert (Hha : exec (run_hart_active 0) (sA s)
                  = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sX s)).
    { unfold sX.
      assert (HdecA : exec (ext_decode w) (sA s)
                = Some (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD), sA s))
        by exact (Hdec_exec_gen (sA s)).
      assert (HexecA : exec (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)))
                (set_reg (sA s) nextPC (add_vec_int pc 4))
              = Some (RETIRE_SUCCESS,
                      set_reg (set_reg (sA s) nextPC (add_vec_int pc 4)) (R_bitvector_64 x12)
                        (regval_into_reg
                           (add_vec (register_lookup (R_bitvector_64 x10)
                                       (set_reg (sA s) nextPC (add_vec_int pc 4)).(sregs))
                                    (register_lookup (R_bitvector_64 x11)
                                       (set_reg (sA s) nextPC (add_vec_int pc 4)).(sregs)))))).
      { change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)))
          with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) ADD).
        exact (exec_execute_ADD rd rs1 rs2 _ Hrs1 Hrs2 Hrd). }
      exact (exec_hart_active_progress (sA s) (sA s) _ (sA s) w
               (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) pc RETIRE_SUCCESS
               ltac:(unfold sA; trans_mi; exact Lpriv) HdispA Hfetch_at HdecA
               ltac:(unfold sA; trans_mi; exact Lelp) ltac:(reflexivity)
               ltac:(unfold sA; trans_mi; exact Lpc) HexecA I). }
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

  (* Like [sF_eq], but expresses the post-step state through the *runtime* minstret
     value [register_lookup minstret s.(sregs)] rather than the section parameter
     [mst0].  This is what a leaf needs when it does NOT own (and never learns) the
     minstret value up front -- it only obtains it transiently from the invariant
     after the step. *)
  Lemma sF_eq_rt (s : mstate) :
    register_lookup (R_bitvector_64 x10) s.(sregs) = a0 ->
    register_lookup (R_bitvector_64 x11) s.(sregs) = a1 ->
    sF s = if b then set_reg (base_upd s) minstret
                      (add_vec_int (register_lookup minstret s.(sregs)) 1)
           else base_upd s.
  Proof using All.
    intros Lx10 Lx11.
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
    unfold sF. rewrite HsT. destruct b; [ | reflexivity ].
    assert (Emst : register_lookup minstret (base_upd s).(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd, sA, set_reg; cbn [sregs]. tmiss. tmiss. tmiss. tmiss. reflexivity. }
    rewrite Emst. reflexivity.
  Qed.

  (* ====================================================================== *)
  (* PROTOTYPE: the same ADD leaf, but with [minstret] / [minstret_increment]
     taken from the persistent [minstret_inv] (opened across the step) instead
     of threaded as two owned cells.  Note the precondition/continuation no
     longer mention either cell -- only the (duplicable) [minstret_inv].
     The exec witness is [sF s], built WITHOUT the minstret value; the cells are
     obtained from the invariant body only AFTER the step, to fold the bump into
     [state_interp] and hand a fresh body back to close the invariant.        *)
  (* ====================================================================== *)
  Lemma wp_add_real_final_minstret
      (mstatus0 misa0 mdv0 : mword 64) (elp0 : mword 1)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      E {dq : dfrac} (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
        is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    minstret_inv -∗
    (R_bitvector_64 x10) ↦ᵣ a0 -∗
    (R_bitvector_64 x11) ↦ᵣ a1 -∗
    (R_bitvector_64 x12) ↦ᵣ v2old -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc -∗
    cur_privilege ↦ᵣ Machine -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗
    (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    reg_pointsto misa dqc misa0 -∗
    elp ↦ᵣ elp0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( (R_bitvector_64 x10) ↦ᵣ a0 -∗
        (R_bitvector_64 x11) ↦ᵣ a1 -∗
        (R_bitvector_64 x12) ↦ᵣ (add_vec a0 a1) -∗
        PC ↦ᵣ (add_vec_int pc 4) -∗
        nextPC ↦ᵣ (add_vec_int pc 4) -∗
        cur_privilege ↦ᵣ Machine -∗
        hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗
        (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        reg_pointsto misa dqc misa0 -∗
        elp ↦ᵣ elp0 -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof using All.
    iIntros (HN HS0 HmIE0 Help0 Hpmaall Hpmpf Hvalignf HnotRVCf)
      "#Hinv Hx10 Hx11 Hx12 Hpc Hnpc Hpriv Hhs Hmdl Hmst' Hmisa Help Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    (* this leaf opens no further invariant, so take the inner mask = E∖↑minstretN
       (both fupds then reflexive, discharged by iModIntro) *)
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hx10")  as %Lx10.
    iDestruct (reg_valid_dq with "Hreg Hx11")  as %Lx11.
    iDestruct (reg_valid_dq with "Hreg Hpc")   as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")   as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")  as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hmst'") as %Lmst2.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Lelp.
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b s
                 Hmatchf Hexecf Hpmpf Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sF s). iSplitR.
    { iPureIntro. apply forward_exec_final; try assumption.
      - rewrite Lmisa. exact HS0.
      - rewrite Lmst2. exact HmIE0.
      - rewrite Lelp. exact Help0. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi")  as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 x12) _ (add_vec a0 a1) with "Hreg Hx12") as "[Hreg Hx12]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    rewrite (sF_eq_rt s Lx10 Lx11). unfold base_upd.
    destruct b.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1)
              with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro.
      unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi".
      { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hx10 Hx11 Hx12 Hpc Hnpc Hpriv Hhs Hmdl Hmst' Hmisa Help Hpmpc Hpma Hhtif Hibytes").
    - iModIntro.
      unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi".
      { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hx10 Hx11 Hx12 Hpc Hnpc Hpriv Hhs Hmdl Hmst' Hmisa Help Hpmpc Hpma Hhtif Hibytes").
  Qed.

End FinalWP.

