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
Local Open Scope Z_scope.

Require Import WpGpr.
Require Import WpGprMret.

(* ====================================================================== *)
(* decode_mret : ext_decode of 0x30200073 = MRET tt.                       *)
(* ====================================================================== *)
Definition w_mret : mword 32 := mword_of_int 0x30200073.

Lemma decode_mret s :
  register_lookup cur_privilege (sregs s) = Machine ->
  exec (ext_decode w_mret) s = Some (MRET tt, s).
Proof.
  intro Hpriv.
  unfold ext_decode, encdec_backwards. cbv beta. cbn zeta.
  skip_pure_clause.                       (* ZICBOP *)
  skip_pure_clause.                       (* NTL    *)
  match goal with |- context[eq_vec w_mret ?c] =>
    replace (eq_vec w_mret c) with false by (vm_compute; reflexivity) end.
  match goal with |- context[eq_vec (subrange_vec_dec w_mret 11 0) ?c] =>
    replace (eq_vec (subrange_vec_dec w_mret 11 0) c) with false by (vm_compute; reflexivity) end.
  assert (HA1 : exec (Defs.and_boolM (currentlyEnabled Ext_Zihintpause) (returnM false)) s
                = Some (false, s)).
  { destruct (exec_cE_pause s) as [bp Hbp].
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hbp). destruct bp; [apply exec_returnm | reflexivity]. }
  rewrite (exec_bind_Some _ _ _ _ _ HA1). cbn match.
  rewrite exec_bind.
  assert (HA2 : exec (Defs.and_boolM (currentlyEnabled Ext_Zicfilp) (returnM false)) s
                = Some (false, s)).
  { destruct (exec_cE_zicfilp_M s Hpriv) as [bz Hbz].
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hbz). destruct bz; [apply exec_returnm | reflexivity]. }
  rewrite (exec_bind_Some _ _ _ _ _ HA2). cbn match.
  (* UTYPE guard false -> returnM None -> reach JAL clause *)
  match goal with |- context[if ?g then _ else returnM None] =>
    replace g with false by (vm_compute; reflexivity) end.
  cbn match.
  rewrite (exec_returnM (@None instruction) s). cbn match.
  (* skip clauses until the ECALL/MRET/SRET flat clause *)
  repeat skip_pure_clause.
  (* MRET clause: ECALL guard false, MRET guard true *)
  match goal with |- context[if ?g then returnM (Some (ECALL tt)) else _] =>
    replace g with false by (vm_compute; reflexivity) end.
  match goal with |- context[if ?g then returnM (Some (MRET tt)) else _] =>
    replace g with true by (vm_compute; reflexivity) end.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (Some (MRET tt)) s)). cbn match.
  apply exec_returnM.
Qed.

(* ====================================================================== *)
(* forward_exec_mret : thread fetch+decode+execute(MRET) through riscv_step *)
(* ====================================================================== *)
Section ForwardMRET.
  Context (s : mstate) (pc : mword 64) (b : bool)
          (newpriv : Privilege) (lpe : bool).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w_mret, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).

  Definition sAm : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pcm : mstate := set_reg sAm nextPC (add_vec_int pc 4).

  (* MRET execute post-state, mirroring exec_execute_MRET's [sF] at [s_pcm]. *)
  Let ms0 := register_lookup mstatus s_pcm.(sregs).
  Let ms1 := update_subrange_vec_dec ms0 3 3 (_get_Mstatus_MPIE ms0).
  Let ms2 := update_subrange_vec_dec ms1 7 7 ('b"1").
  Let ms3 := update_subrange_vec_dec ms2 12 11 (privLevel_to_bits User).
  Let ms4 := update_subrange_vec_dec ms3 17 17 ('b"0").
  Let ms5 := update_subrange_vec_dec ms4 41 41 (landing_pad_bits_backwards NO_LP_EXPECTED).
  Let elpv := if lpe then _get_Mstatus_MPELP ms4 else landing_pad_bits_backwards NO_LP_EXPECTED.
  Let tgt := update_vec_dec (register_lookup mepc s_pcm.(sregs)) 0 ('b"0").
  Definition sXm : mstate :=
    set_reg (set_reg (set_reg (set_reg (set_reg
              (set_reg (set_reg (set_reg s_pcm mstatus ms1) mstatus ms2)
                       cur_privilege newpriv) mstatus ms3) mstatus ms4)
              mstatus ms5) elp elpv) nextPC tgt.
  Definition sTm : mstate := set_reg sXm PC (register_lookup nextPC sXm.(sregs)).
  Definition sFm : mstate :=
    if b then set_reg sTm minstret (add_vec_int (register_lookup minstret sTm.(sregs)) 1)
         else sTm.

  (* The 6 MRET execute side-conditions, stated at [s] (transferred to [s_pcm]). *)
  Hypothesis Hmu : eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis Hmc : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis Hnp : privLevel_bits_forwards (_get_Mstatus_MPP ms2, ('b"0")) = returnM newpriv.
  Hypothesis Hnpm : generic_neq newpriv Machine = true.
  Hypothesis Hlpe : forall sz, exec (get_xLPE newpriv) sz = Some (lpe, sz).

  Lemma forward_exec_mret :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFm).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp.
    assert (LpcA  : register_lookup PC sAm.(sregs) = pc).
    { unfold sAm, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sAm.(sregs) = Machine).
    { unfold sAm, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sAm.(sregs) = HART_ACTIVE tt).
    { unfold sAm, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa sAm.(sregs))) ('b"1") = true).
    { unfold sAm, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LS | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE
              (register_lookup (R_bitvector_64 mstatus) sAm.(sregs))) ('b"1") = false).
    { unfold sAm, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAm.(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAm, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lelp | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAm = Some (None, sAm)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAm _ (exec_currentlyEnabled_S sAm) (or_introl LSA) LmIEA). }
    assert (HfetchA : exec (fetch tt) sAm = Some (F_Base w_mret, sAm))
      by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w_mret) sAm = Some (MRET tt, sAm))
      by (apply decode_mret; exact LprivA).
    (* The MRET execute side-conditions transfer from [s] to [s_pcm]. *)
    assert (LprivP : register_lookup cur_privilege s_pcm.(sregs) = Machine).
    { unfold s_pcm, sAm, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [|vm_compute; reflexivity].
      rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (HmuP : eq_vec (_get_Misa_U (register_lookup misa s_pcm.(sregs))) ('b"1") = true).
    { unfold s_pcm, sAm, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [|vm_compute; reflexivity].
      rewrite irrelevant_register_set; [exact Hmu | vm_compute; reflexivity]. }
    assert (HmcP : eq_vec (_get_Misa_C (register_lookup misa s_pcm.(sregs))) ('b"1") = true).
    { unfold s_pcm, sAm, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [|vm_compute; reflexivity].
      rewrite irrelevant_register_set; [exact Hmc | vm_compute; reflexivity]. }
    assert (HnpP : privLevel_bits_forwards
              (_get_Mstatus_MPP (update_subrange_vec_dec
                 (update_subrange_vec_dec (register_lookup mstatus s_pcm.(sregs)) 3 3
                    (_get_Mstatus_MPIE (register_lookup mstatus s_pcm.(sregs)))) 7 7 ('b"1")),
               ('b"0")) = returnM newpriv).
    { exact Hnp. }
    assert (HexecM : exec (execute (MRET tt)) s_pcm = Some (RETIRE_SUCCESS, sXm)).
    { exact (exec_execute_MRET s_pcm newpriv lpe LprivP HmuP HmcP HnpP Hnpm Hlpe). }
    assert (Hha : exec (run_hart_active 0) sAm
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w_mret), sXm)).
    { exact (exec_hart_active_progress sAm sAm sXm sAm w_mret
               (MRET tt) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecM I). }
    apply (exec_riscv_step_ADD s sXm w_mret b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXm, s_pcm, sAm; cbn zeta.
      repeat (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). exact Lhs.
    - unfold sXm, s_pcm, sAm; cbn zeta.
      repeat (rewrite irrelevant_register_set; [|vm_compute; reflexivity]).
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardMRET.

(* ====================================================================== *)
(* wp_mret : Iris WP layer for MRET.                                        *)
(* ====================================================================== *)
Section StepMRET.
  Context `{!riscvGS Σ}.

  (* Clean MRET post-state in terms of the OWNED register values             *)
  (* (mstatus0, mepc0, elp0), parameterised so the WP can hand them back.     *)
  Section CleanMRET.
    Context (s : mstate) (pc : mword 64) (b : bool)
            (newpriv : Privilege) (lpe : bool)
            (mstatus0 mepc0 : mword 64) (mst0 : mword 64).
    Definition cms1 := update_subrange_vec_dec mstatus0 3 3 (_get_Mstatus_MPIE mstatus0).
    Definition cms2 := update_subrange_vec_dec cms1 7 7 ('b"1").
    Definition cms3 := update_subrange_vec_dec cms2 12 11 (privLevel_to_bits User).
    Definition cms4 := update_subrange_vec_dec cms3 17 17 ('b"0").
    Definition cms5 := update_subrange_vec_dec cms4 41 41 (landing_pad_bits_backwards NO_LP_EXPECTED).
    Definition celpv := if lpe then _get_Mstatus_MPELP cms4 else landing_pad_bits_backwards NO_LP_EXPECTED.
    Definition ctgt := update_vec_dec mepc0 0 ('b"0").

    Definition base_upd_m : mstate :=
      set_reg
        (set_reg (set_reg (set_reg (set_reg (set_reg (set_reg (set_reg (set_reg
          (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
            mstatus cms1) mstatus cms2) cur_privilege newpriv) mstatus cms3)
            mstatus cms4) mstatus cms5) elp celpv) nextPC ctgt)
        PC ctgt.
    Definition sFcm : mstate :=
      if b then set_reg base_upd_m minstret (add_vec_int mst0 1) else base_upd_m.

    Ltac tmim := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

    Lemma sFm_eq :
      register_lookup PC s.(sregs) = pc ->
      register_lookup mstatus s.(sregs) = mstatus0 ->
      register_lookup mepc s.(sregs) = mepc0 ->
      register_lookup minstret s.(sregs) = mst0 ->
      sFm s pc b newpriv lpe = sFcm.
    Proof.
      intros LpcS LmsS LmepcS LmstS.
      (* the inner lookups at s_pcm reduce to the owned values *)
      assert (Lms : register_lookup mstatus (s_pcm s pc b).(sregs) = mstatus0).
      { unfold s_pcm, sAm, set_reg; cbn [sregs]. tmim. tmim. exact LmsS. }
      assert (Lmepc : register_lookup mepc (s_pcm s pc b).(sregs) = mepc0).
      { unfold s_pcm, sAm, set_reg; cbn [sregs]. tmim. tmim. exact LmepcS. }
      (* sXm: rewrite ms_i and tgt to clean versions *)
      assert (HsX : sXm s pc b newpriv lpe =
        set_reg (set_reg (set_reg (set_reg (set_reg
          (set_reg (set_reg (set_reg (s_pcm s pc b) mstatus cms1) mstatus cms2)
                   cur_privilege newpriv) mstatus cms3) mstatus cms4)
          mstatus cms5) elp celpv) nextPC ctgt).
      { unfold sXm. unfold cms1, cms2, cms3, cms4, cms5, celpv, ctgt.
        rewrite Lms Lmepc. reflexivity. }
      assert (Enpc : register_lookup nextPC (sXm s pc b newpriv lpe).(sregs) = ctgt).
      { rewrite HsX. unfold set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
      assert (HsT : sTm s pc b newpriv lpe = base_upd_m).
      { unfold sTm. rewrite Enpc. rewrite HsX. unfold base_upd_m, s_pcm, sAm. reflexivity. }
      unfold sFm, sFcm. rewrite HsT. destruct b; [|reflexivity].
      assert (Emst : register_lookup minstret base_upd_m.(sregs)
                     = register_lookup minstret s.(sregs)).
      { unfold base_upd_m, set_reg; cbn [sregs].
        tmim. tmim. tmim. tmim. tmim. tmim. tmim. tmim. tmim. tmim. tmim. reflexivity. }
      rewrite Emst LmstS. reflexivity.
    Qed.
  End CleanMRET.

  Lemma wp_mret (pc : mword 64) (newpriv : Privilege) (lpe : bool)
      (b1 : bool) (npc0 mst0 mstatus0 misa0 mepc0 mdv0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E (Phi : mval -> iProp Σ) :
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Misa_U misa0) ('b"1") = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    privLevel_bits_forwards
      (_get_Mstatus_MPP (cms2 mstatus0), ('b"0")) = returnM newpriv ->
    generic_neq newpriv Machine = true ->
    (forall sz, exec (get_xLPE newpriv) sz = Some (lpe, sz)) ->
    PC ↦ᵣ pc -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    misa ↦ᵣ misa0 -∗ mepc ↦ᵣ mepc0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w_mret j) -∗
    ▷ ( PC ↦ᵣ ctgt mepc0 -∗ nextPC ↦ᵣ ctgt mepc0 -∗
        (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ newpriv -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗
        (R_bitvector_64 mstatus) ↦ᵣ cms5 mstatus0 -∗
        misa ↦ᵣ misa0 -∗ mepc ↦ᵣ mepc0 -∗
        elp ↦ᵣ celpv lpe mstatus0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w_mret j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf Hb1 HmIE Help HS Hmu Hmc Hnp Hnpm Hlpe)
      "Hpc Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hmisa Hmepc Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (reg_valid with "Hreg Hmepc")  as %Lmepc.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    iDestruct (fetch_from_pts_minstret pc w_mret region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf
                 ltac:(vm_compute; reflexivity)
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFcm s pc b1 newpriv lpe mstatus0 mepc0 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFm_eq s pc b1 newpriv lpe mstatus0 mepc0 mst0 Lpc Lms Lmepc Lmst).
      apply (forward_exec_mret s pc b1 newpriv lpe Hfetch_at Hsi_s).
      - rewrite Lmisa. exact Hmu.
      - rewrite Lmisa. exact Hmc.
      - (* Hnp: privLevel_bits_forwards over ms2 at s_pcm = over cms2 mstatus0 *)
        replace (update_subrange_vec_dec
                   (update_subrange_vec_dec (register_lookup mstatus (s_pcm s pc b1).(sregs)) 3 3
                      (_get_Mstatus_MPIE (register_lookup mstatus (s_pcm s pc b1).(sregs)))) 7 7
                   ('b"1"))
          with (cms2 mstatus0).
        2:{ unfold cms2, cms1.
            replace (register_lookup mstatus (s_pcm s pc b1).(sregs)) with mstatus0
              by (unfold s_pcm, sAm, set_reg; cbn [sregs];
                  rewrite irrelevant_register_set; [|vm_compute; reflexivity];
                  rewrite irrelevant_register_set; [symmetry; exact Lms | vm_compute; reflexivity]).
            reflexivity. }
        exact Hnp.
      - exact Hnpm.
      - exact Hlpe.
      - exact Lpc.
      - exact Lpriv.
      - exact Lhs.
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iIntros "!>".
    unfold sFcm, base_upd_m.
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ mstatus _ (cms1 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (cms2 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ cur_privilege _ newpriv with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ mstatus _ (cms3 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (cms4 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (cms5 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ elp _ (celpv lpe mstatus0) with "Hreg Help") as "[Hreg Help]".
    iMod (reg_update _ nextPC _ (ctgt mepc0) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ PC _ (ctgt mepc0) with "Hreg Hpc") as "[Hreg Hpc]".
    destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hmisa Hmepc Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hmisa Hmepc Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End StepMRET.
