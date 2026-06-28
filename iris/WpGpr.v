From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpEntry.
Require Import MinstretInv.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.

Definition gpr_of_Z (n : Z) : register_bitvector_64 :=
  if Z.eqb n 1 then x1 else if Z.eqb n 2 then x2
  else if Z.eqb n 3 then x3 else if Z.eqb n 4 then x4 else if Z.eqb n 5 then x5
  else if Z.eqb n 6 then x6 else if Z.eqb n 7 then x7 else if Z.eqb n 8 then x8
  else if Z.eqb n 9 then x9 else if Z.eqb n 10 then x10 else if Z.eqb n 11 then x11
  else if Z.eqb n 12 then x12 else if Z.eqb n 13 then x13 else if Z.eqb n 14 then x14
  else if Z.eqb n 15 then x15 else if Z.eqb n 16 then x16 else if Z.eqb n 17 then x17
  else if Z.eqb n 18 then x18 else if Z.eqb n 19 then x19 else if Z.eqb n 20 then x20
  else if Z.eqb n 21 then x21 else if Z.eqb n 22 then x22 else if Z.eqb n 23 then x23
  else if Z.eqb n 24 then x24 else if Z.eqb n 25 then x25 else if Z.eqb n 26 then x26
  else if Z.eqb n 27 then x27 else if Z.eqb n 28 then x28 else if Z.eqb n 29 then x29
  else if Z.eqb n 30 then x30 else x31.

Lemma uint5_lt (i : mword 5) : 0 <= uint i < 32.
Proof. pose proof (uint_range i ltac:(lia)) as H. change (2^5-1) with 31 in H. lia. Qed.

Lemma exec_wX_bits_gpr (i : mword 5) (v : mword 64) s :
  exec (wX_bits (Regidx i) v) s
  = Some (tt, if Z.eqb (uint i) 0 then s
              else set_reg s (R_bitvector_64 (gpr_of_Z (uint i))) (regval_into_reg v)).
Proof.
  pose proof (uint5_lt i) as Hb.
  assert (Hc : uint i = 0 \/ uint i = 1 \/ uint i = 2 \/ uint i = 3 \/ uint i = 4 \/
    uint i = 5 \/ uint i = 6 \/ uint i = 7 \/ uint i = 8 \/ uint i = 9 \/ uint i = 10 \/
    uint i = 11 \/ uint i = 12 \/ uint i = 13 \/ uint i = 14 \/ uint i = 15 \/ uint i = 16 \/
    uint i = 17 \/ uint i = 18 \/ uint i = 19 \/ uint i = 20 \/ uint i = 21 \/ uint i = 22 \/
    uint i = 23 \/ uint i = 24 \/ uint i = 25 \/ uint i = 26 \/ uint i = 27 \/ uint i = 28 \/
    uint i = 29 \/ uint i = 30 \/ uint i = 31) by lia.
  destruct Hc as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  1:{ unfold wX_bits, wX. rewrite H. cbn match.
      rewrite (exec_bind0_Some _ _ _ _ _ (exec_returnm tt s)). reflexivity. }
  all: rewrite (exec_wX_bits_at i (gpr_of_Z (uint i)) s v ltac:(rewrite H; vm_compute; reflexivity));
       rewrite H; reflexivity.
Qed.

Lemma exec_rX_bits_gpr (i : mword 5) s :
  exec (rX_bits (Regidx i)) s
  = Some (if Z.eqb (uint i) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint i))) s.(sregs), s).
Proof.
  pose proof (uint5_lt i) as Hb.
  assert (Hc : uint i = 0 \/ uint i = 1 \/ uint i = 2 \/ uint i = 3 \/ uint i = 4 \/
    uint i = 5 \/ uint i = 6 \/ uint i = 7 \/ uint i = 8 \/ uint i = 9 \/ uint i = 10 \/
    uint i = 11 \/ uint i = 12 \/ uint i = 13 \/ uint i = 14 \/ uint i = 15 \/ uint i = 16 \/
    uint i = 17 \/ uint i = 18 \/ uint i = 19 \/ uint i = 20 \/ uint i = 21 \/ uint i = 22 \/
    uint i = 23 \/ uint i = 24 \/ uint i = 25 \/ uint i = 26 \/ uint i = 27 \/ uint i = 28 \/
    uint i = 29 \/ uint i = 30 \/ uint i = 31) by lia.
  destruct Hc as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  1:{ unfold rX_bits, rX. rewrite H. cbn match. apply exec_returnm. }
  all: unfold rX_bits, rX; rewrite H; cbn match; reflexivity.
Qed.

(* register-generic ADD execute: reads rs1/rs2, writes rd, all via the file-generic
   rX/wX lemmas — works for ANY register triple. *)
Definition gpr_rd_val (rs2 rs1 : mword 5) (s : mstate) : mword 64 :=
  add_vec (if Z.eqb (uint rs1) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
          (if Z.eqb (uint rs2) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs)).

Lemma exec_execute_RTYPE_ADD_gpr (rs2 rs1 rd : mword 5) s :
  exec (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) ADD) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_rd_val rs2 rs1 s))).
Proof.
  unfold gpr_rd_val.
  eapply exec_execute_RTYPE_ADD.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_rX_bits_gpr rs2 s).
  - apply (exec_wX_bits_gpr rd _ s).
Qed.

(* ====================================================================== *)
(* The general-purpose register file as a SINGLE resource: all of x1..x31  *)
(* in one separating conjunction (special/CSR registers stay separate).    *)
(* ====================================================================== *)
Definition gpr_list : list register_bitvector_64 :=
  [x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15;x16;
   x17;x18;x19;x20;x21;x22;x23;x24;x25;x26;x27;x28;x29;x30;x31].
Definition gpr_set : gset register_bitvector_64 := list_to_set gpr_list.

Section GprFile.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Definition gpr_file (m : gmap register_bitvector_64 (mword 64)) : iProp Σ :=
    ([∗ map] r ↦ v ∈ m, (R_bitvector_64 r) ↦ᵣ v)%I.
End GprFile.

(* exec-level register-generic ADD step (32-bit, F_Base): one lemma, ANY rd/rs1/rs2. *)
Section ForwardAddGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs2 rs1 rd : mword 5).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrd0 : uint rd <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD), s0).

  Definition sAg : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pcg : mstate := set_reg sAg nextPC (add_vec_int pc 4).
  Definition sXg : mstate :=
    set_reg s_pcg (R_bitvector_64 (gpr_of_Z (uint rd)))
      (regval_into_reg (gpr_rd_val rs2 rs1 s_pcg)).
  Definition sTg : mstate := set_reg sXg PC (register_lookup nextPC sXg.(sregs)).
  Definition sFg : mstate :=
    if b then set_reg sTg minstret (add_vec_int (register_lookup minstret sTg.(sregs)) 1)
         else sTg.

  Lemma forward_exec_add_gpr :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFg).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp.
    assert (LpcA  : register_lookup PC sAg.(sregs) = pc).
    { unfold sAg, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sAg.(sregs) = Machine).
    { unfold sAg, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sAg.(sregs) = HART_ACTIVE tt).
    { unfold sAg, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa sAg.(sregs))) ('b"1") = true).
    { unfold sAg, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LS | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE
              (register_lookup (R_bitvector_64 mstatus) sAg.(sregs))) ('b"1") = false).
    { unfold sAg, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAg.(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAg, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lelp | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAg = Some (None, sAg)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAg _ (exec_currentlyEnabled_S sAg) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) sAg = Some (F_Base w, sAg)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sAg
              = Some (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD), sAg))
      by (apply Hdec; exact LprivA).
    assert (HexecG : exec (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD))) s_pcg
              = Some (RETIRE_SUCCESS, sXg)).
    { change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)))
        with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) ADD).
      rewrite (exec_execute_RTYPE_ADD_gpr rs2 rs1 rd s_pcg).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd0).
      reflexivity. }
    assert (Hha : exec (run_hart_active 0) sAg
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXg)).
    { exact (exec_hart_active_progress sAg sAg sXg sAg w
               (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecG I). }
    apply (exec_riscv_step_ADD s sXg w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXg, s_pcg, sAg; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXg, s_pcg, sAg; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardAddGpr.

(* gpr_of_Z always lands in x1..x31, hence differs from any non-GPR register. *)
Lemma gpr_of_Z_ne_nextPC (n : Z) : register_beq (R_bitvector_64 (gpr_of_Z n)) (R_bitvector_64 nextPC) = false.
Proof. unfold gpr_of_Z; repeat case_match; reflexivity. Qed.
Lemma gpr_of_Z_ne_PC (n : Z) : register_beq (R_bitvector_64 (gpr_of_Z n)) (R_bitvector_64 PC) = false.
Proof. unfold gpr_of_Z; repeat case_match; reflexivity. Qed.
Lemma gpr_of_Z_ne_minstret (n : Z) : register_beq (R_bitvector_64 (gpr_of_Z n)) minstret = false.
Proof. unfold gpr_of_Z; repeat case_match; reflexivity. Qed.

Ltac gpr_trans := first
  [ rewrite (irrelevant_register_set _ _ _ _ (gpr_of_Z_ne_nextPC _))
  | rewrite (irrelevant_register_set _ _ _ _ (gpr_of_Z_ne_PC _))
  | rewrite (irrelevant_register_set _ _ _ _ (gpr_of_Z_ne_minstret _))
  | rewrite irrelevant_register_set; [|vm_compute; reflexivity] ].

Lemma gpr_rd_val_lookup (rs2 rs1 : mword 5) (t : mstate) :
  uint rs1 <> 0 -> uint rs2 <> 0 ->
  gpr_rd_val rs2 rs1 t
  = add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) t.(sregs))
            (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) t.(sregs)).
Proof.
  intros H1 H2. unfold gpr_rd_val.
  replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact H1).
  replace (Z.eqb (uint rs2) 0) with false by (symmetry; apply Z.eqb_neq; exact H2).
  reflexivity.
Qed.

Lemma gpr_rd_val_file (s : mstate) (pc : mword 64) (b : bool) (rs2 rs1 : mword 5) (va vb : mword 64) :
  uint rs1 <> 0 -> uint rs2 <> 0 ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs) = va ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs) = vb ->
  gpr_rd_val rs2 rs1 (s_pcg s pc b) = add_vec va vb.
Proof.
  intros H1 H2 Lva Lvb.
  rewrite (gpr_rd_val_lookup rs2 rs1 (s_pcg s pc b) H1 H2).
  unfold s_pcg, sAg. unfold set_reg; cbn [sregs].
  do 4 (gpr_trans). rewrite Lva. rewrite Lvb. reflexivity.
Qed.

Ltac reg_ne := solve [ vm_compute; reflexivity
                     | (unfold gpr_of_Z; repeat case_match; reflexivity) ].
Ltac tmig := rewrite irrelevant_register_set; [ | reg_ne ].

Section CleanGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (rs2 rs1 rd : mword 5) (mst0 : mword 64).
  Definition base_upd_g : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b)
                  nextPC (add_vec_int pc 4))
         (R_bitvector_64 (gpr_of_Z (uint rd)))
         (regval_into_reg (gpr_rd_val rs2 rs1 (s_pcg s pc b))))
      PC (add_vec_int pc 4).
  Definition sFcg : mstate :=
    if b then set_reg base_upd_g minstret (add_vec_int mst0 1) else base_upd_g.

  Lemma sFg_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFg s pc b rs2 rs1 rd = sFcg.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXg s pc b rs2 rs1 rd).(sregs) = add_vec_int pc 4).
    { unfold sXg; cbv zeta. unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTg s pc b rs2 rs1 rd = base_upd_g).
    { unfold sTg. rewrite Enpc. unfold sXg, s_pcg, sAg; cbv zeta.
      unfold base_upd_g, s_pcg, sAg. reflexivity. }
    unfold sFg, sFcg. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_g.(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd_g, set_reg; cbn [sregs].
      do 4 tmig. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanGpr.

(* ====================================================================== *)
(* The register-GENERIC add WP: ONE lemma covering `add rd,rs1,rs2` for    *)
(* ANY register triple, with all GPRs held as the single [gpr_file]        *)
(* resource (special/CSR registers stay as individual points-tos).         *)
(* ====================================================================== *)
Section WpAddGpr.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.

  Lemma wp_add_gpr (pc : mword 64) (w : mword 32) (rs2 rs1 rd : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (va vb vd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    uint rs1 <> 0 -> uint rs2 <> 0 -> uint rd <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some va ->
    m !! gpr_of_Z (uint rs2) = Some vb ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    minstret_inv -∗
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (add_vec va vb)]> m) -∗
        reg_pointsto misa dqc misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hr1 Hr2 Hrd Hm1 Hm2 Hmd HS Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "#Hinv Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    (* read rs1, rs2 values out of the register file (non-destructively) *)
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (reg_valid_dq with "Hreg Hr1c") as %Lrs1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfile") as "[Hr2c Hfb2]".
    iDestruct (reg_valid_dq with "Hreg Hr2c") as %Lrs2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hrdv : gpr_rd_val rs2 rs1 (s_pcg s pc b1) = add_vec va vb)
      by (apply (gpr_rd_val_file s pc b1 rs2 rs1 va vb Hr1 Hr2 Lrs1 Lrs2)).
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcg s pc b1 rs2 rs1 rd (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFg_eq s pc b1 rs2 rs1 rd (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_add_gpr s pc b1 w rs2 rs1 rd Hfetch_at Hsi_s Hrd Hdec
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (gpr_rd_val rs2 rs1 (s_pcg s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hrdv) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec va vb)) with "Hrdc") as "Hfile".
    unfold sFcg, base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpAddGpr.

(* ====================================================================== *)
(* Demonstration: ONE lemma [wp_add_gpr] serves many register triples.     *)
(* The register operands are ordinary arguments; only they differ between  *)
(* `add x5,x6,x7` and `add x28,x1,x2`.  (Concrete reg numbers reduce:       *)
(* uint (mword_of_int 6) = 6 and gpr_of_Z 6 = x6, etc.)                     *)
(* ====================================================================== *)
Section WpAddGprDemo.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.

  (* `add x5, x6, x7` : rd=x5, rs1=x6, rs2=x7.  Same lemma, instantiated. *)
  Definition wp_add_x5_x6_x7 (pc : mword 64) (w : mword 32) :=
    wp_add_gpr (dqc:=DfracOwn 1) pc w (mword_of_int 7) (mword_of_int 6) (mword_of_int 5).
  (* `add x28, x1, x2` : rd=x28, rs1=x1, rs2=x2.  SAME lemma, different regs. *)
  Definition wp_add_x28_x1_x2 (pc : mword 64) (w : mword 32) :=
    wp_add_gpr (dqc:=DfracOwn 1) pc w (mword_of_int 2) (mword_of_int 1) (mword_of_int 28).

  (* The concrete register operands resolve to the intended file entries. *)
  Goal gpr_of_Z (uint (mword_of_int 6 : mword 5)) = x6
    /\ gpr_of_Z (uint (mword_of_int 28 : mword 5)) = x28
    /\ uint (mword_of_int 7 : mword 5) <> 0.
  Proof. repeat split; vm_compute; first [ reflexivity | discriminate ]. Qed.
End WpAddGprDemo.
