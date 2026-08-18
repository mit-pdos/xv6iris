(* UserActiveClass.v -- worklist item (A): the [active_class] assembly.

   Builds [active_class] (the no-pending-interrupt fetch/decode/execute
   classification) as a [va] CASE TREE routing every geometry to one of the
   six producers/adapters in UserClassifyAsm.v, then [active_step_branch].
   The two execute totalities are taken as Coq-level hypotheses [Hbase]/[Hrvc]
   (the sibling UserTotalU.v supplies [base_exec_total_u_holds] /
   [rvc_exec_total_u_holds] of exactly this shape).

   Closes the capstone: [active_class_intro] -> [wp_user_step_active]
   (UserStepFull) -> [wp_user_exec_active] (UserStep). *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec RiscvExtras.
Require Import MinstretInv RegFile UserBits AlignBits WpGpr.
Require Import TrampPt KptTree UptTree.
Require Import SmodeCore WpIntrCore.
Require Import HartSwp HartLift HartSpan HartMCycle HartStepFull HartRunFull.
Require Import HartMemRun PtreeType PtTree SmodePte PtBytes UserBytes InstrBytes.
Require Import UserFrame UserClassifyAsm.
Require Import UserPtTree UserExec UserStep UserStepFull.
Require Import UserFetchPt UserClassify.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1  Pure alignment bridges (bit0 <-> 2-alignment; +2 preserves it).    *)
(* ===================================================================== *)

(* bit 0 of [va] is 0  =>  [va] is even *)
Lemma access0_even (va : mword 64) :
  neq_vec (access_vec_dec va 0) ('b"0") = false ->
  bv_unsigned va mod 2 = 0.
Proof.
  intro H0.
  unfold neq_vec in H0. rewrite negb_false_iff in H0.
  unfold eq_vec, access_vec_dec, access_mword_dec, slice, get_word in H0.
  rewrite MachineWord.MachineWord.eqb_true_iff in H0.
  apply bv_eq in H0.
  unfold MachineWord.slice in H0.
  rewrite bv_extract_unsigned in H0.
  replace (bv_unsigned ('b"0")) with 0%Z in H0 by (vm_compute; reflexivity).
  revert H0.
  match goal with
  | |- bv_wrap ?n (Z.shiftr (bv_unsigned va) ?s) = 0%Z -> _ =>
      replace s with 0%Z by (vm_compute; reflexivity);
      rewrite Z.shiftr_0_r;
      replace (bv_wrap n (bv_unsigned va)) with (bv_unsigned va mod 2)
        by (unfold bv_wrap; replace (bv_modulus n) with 2%Z by (vm_compute; reflexivity);
            reflexivity)
  end.
  intro H; exact H.
Qed.

(* CONVERSE of [align2_low_bit]: bit0 = 0  =>  2-aligned. *)
Lemma align2_of_bit0 (va : mword 64) :
  neq_vec (access_vec_dec va 0) ('b"0") = false ->
  is_aligned_vaddr (Virtaddr va) 2 = true.
Proof.
  intro H0. pose proof (access0_even va H0) as He.
  unfold is_aligned_vaddr. apply Z.eqb_eq.
  rewrite uint_unsigned.
  pose proof (bv_unsigned_in_range _ va) as Hr.
  rewrite Z.rem_mod_nonneg; [ | lia | lia ].
  exact He.
Qed.

(* 2-alignment is preserved by adding 2. *)
Lemma align2_add2 (va : mword 64) :
  is_aligned_vaddr (Virtaddr va) 2 = true ->
  is_aligned_vaddr (Virtaddr (add_vec_int va 2)) 2 = true.
Proof.
  unfold is_aligned_vaddr. intro H. apply Z.eqb_eq in H. apply Z.eqb_eq.
  rewrite uint_unsigned in H. rewrite uint_unsigned.
  pose proof (bv_unsigned_in_range _ va) as Hv.
  pose proof (bv_unsigned_in_range _ (add_vec_int va 2)) as Hs.
  rewrite Z.rem_mod_nonneg in H; [ | lia | lia ].
  rewrite Z.rem_mod_nonneg; [ | lia | lia ].
  unfold add_vec_int, add_vec, Operators_mwords.word_binop,
    Operators_mwords.with_word', to_word, get_word, SailStdpp.Values.with_word.
  unfold MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  assert (Hjv : bv_unsigned (mword_of_int 2 : mword 64) = 2) by (vm_compute; reflexivity).
  rewrite Hjv.
  rewrite mod2_wrap.
  2:{ apply Z.leb_le; vm_compute; reflexivity. }
  rewrite Zplus_mod. rewrite H. reflexivity.
Qed.

(* ===================================================================== *)
(* §2  The fetch classification of a va: fetchable OR fault-flavor.       *)
(* ===================================================================== *)

(* a va whose instruction fetch will succeed: canonical, mapped, and the
   leaf passes the U-mode fetch check on every A/D variant. *)
Definition u_fetchable (um : gmap (mword 27) (mword 64)) (va : mword 64) : Prop :=
  exists w, um !! svpn_of va = Some w
            /\ uleaf_ok (InstructionFetch tt) w
            /\ neq_vec (bits_of_virtaddr (Virtaddr va))
                 (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                    (Z.sub 39 1) 0)) = false.

Local Ltac u_notin_clock := apply (bool_decide_unpack _); vm_compute; reflexivity.

Section UserActiveClass.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).
  Context (Rut : uptd -> iProp Σ).

  (* every canonical/non-canonical va either fetches or faults; the
     tramp/tf pages are denied leaves (U=0), a genuinely unmapped canonical
     va is a page fault, non-canonical faults outright. *)
  Lemma fetch_classify (va : mword 64) :
    upt_acc_wf pt.(ud_um) ->
    u_fetchable pt.(ud_um) va \/ u_fetch_fault_flavor pt.(ud_tfp) pt.(ud_um) va.
  Proof.
    intro Hwf.
    unfold u_fetch_fault_flavor, u_fault_flavor.
    destruct (neq_vec (bits_of_virtaddr (Virtaddr va))
                (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                   (Z.sub 39 1) 0))) eqn:Hcn.
    - (* non-canonical *)
      right. left. reflexivity.
    - (* canonical *)
      destruct (decide (svpn_of va = tramp_vpn)) as [Het | Hnt].
      + (* trampoline page: denied leaf *)
        right. right. right. split; [reflexivity|].
        exists pte_tramp. split.
        * unfold upt_leaf_at. left. split; [exact Het | reflexivity].
        * exact (uleaf_denied_tramp (InstructionFetch tt)).
      + destruct (decide (svpn_of va = tf_vpn)) as [Hetf | Hntf].
        * (* trapframe page: denied leaf *)
          right. right. right. split; [reflexivity|].
          exists (pte_tf pt.(ud_tfp)). split.
          -- unfold upt_leaf_at. right. left. split; [exact Hetf | reflexivity].
          -- exact (uleaf_denied_tf pt.(ud_tfp) (InstructionFetch tt)).
        * destruct (pt.(ud_um) !! svpn_of va) as [w|] eqn:Hm.
          -- (* mapped user leaf: classified by upt_acc_wf *)
             destruct (Hwf (svpn_of va) w Hm (InstructionFetch tt) (or_introl eq_refl))
               as [Hok | Hden].
             ++ left. exists w. split; [exact Hm | split; [exact Hok | exact Hcn]].
             ++ right. right. right. split; [reflexivity|].
                exists w. split.
                ** unfold upt_leaf_at. right. right. exact Hm.
                ** exact Hden.
          -- (* unmapped, and not tramp/tf: page fault *)
             right. right. left. split; [reflexivity|]. split; [reflexivity|].
             split; [exact Hnt | exact Hntf].
  Qed.

  (* ===================================================================== *)
  (* §3  THE TWO CLOSERS.                                                   *)
  (*                                                                        *)
  (* Every one of the six arms ends the same way: the cycle's tail has run,  *)
  (* the frame is at some [rs3], and what is owed is either [user_inv] (the  *)
  (* hart retired, still at User) or [user_trap_frame] (it trapped, and is   *)
  (* now at Supervisor with the pc at [stvec]).  Both closers take the pins  *)
  (* at [rs3] as PURE premises so that an arm only has to say what its       *)
  (* landing file looks like -- which is exactly what the arm's [exec] fact  *)
  (* and the tower's agreement give it.                                      *)
  (* ===================================================================== *)

  (* THE TRAPPED FILE.  [UserStep.u_close_inv] is the retiring twin; this
     one cannot reuse it, because [u_pins_regs] pins [cur_privilege] to
     [User] (that is what makes it the USER machine's bundle) and a trapped
     file is at [Supervisor] -- hence [UserFrame.u_frames_elim_at]. *)
  Lemma u_close_trap (t : ptree) (mm : PtBytes.pamap) (usatp : mword 64)
      (tlbvec : type_of_register tlb)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (mcenv scenv : mword 32) (hpm : type_of_register mhpmcounter)
      (rs3 : regstate) :
    trap_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rs3) ->
    register_lookup hart_state rs3 = HART_ACTIVE tt ->
    register_lookup cur_privilege rs3 = Supervisor ->
    register_lookup (R_bitvector_64 PC) rs3 = stvec_base (uc_stvec C) ->
    register_lookup (R_bitvector_64 nextPC) rs3 = stvec_base (uc_stvec C) ->
    register_lookup (R_bitvector_64 stvec) rs3 = uc_stvec C ->
    register_lookup (R_bitvector_64 mie) rs3 = uc_mie C ->
    register_lookup (R_bitvector_64 mideleg) rs3 = uc_mideleg C ->
    register_lookup (R_bitvector_64 menvcfg) rs3 = MENVCFG_S ->
    register_lookup (R_bitvector_64 satp) rs3 = usatp ->
    register_lookup pmpcfg_n rs3 = pcfg ->
    register_lookup pmpaddr_n rs3 = paddr ->
    register_lookup tlb rs3 = tlbvec ->
    tlb_ok_pt (mword_of_int 0) t tlbvec ->
    u_mem_wf pt t mm ->
    u_open C pt t mm usatp pcfg paddr mcenv scenv hpm -∗
    hreg_frame rs3 u_Drw -∗ hreg_frame_ro (u_Df (uc_dqc C)) rs3 u_Dro -∗
    resv_any cpu_id -∗ Rut pt -∗
    user_trap_frame C pt Rut.
  Proof.
    intros Hmsok Lhs Lpriv Lpc Lnpc Lstvec Lmie Lmdl Lmenv Lsatp Lpcfg Lpaddr
      Ltlb Htlbok Hwf.
    iIntros "Hopen Hrw Hro Hresv Hrut".
    rewrite /u_open.
    iDestruct "Hopen" as "(Hpmp & #Hmedl & #Hsenv & #Hmste & #Hsste &
                           #Hmcen & #Hscen & #Hhpm & #Hclaims & Hbytes & Hclose)".
    iDestruct (u_frames_elim_at Supervisor rs3 (uc_dqc C) (HART_ACTIVE tt)
                 (register_lookup (R_bitvector_64 mstatus) rs3)
                 (register_lookup (R_bitvector_64 scause) rs3)
                 (register_lookup (R_bitvector_64 stval) rs3)
                 (register_lookup (R_bitvector_64 sepc) rs3)
                 (stvec_base (uc_stvec C)) (stvec_base (uc_stvec C))
                 (register_lookup (R_bitvector_64 minstret) rs3)
                 (register_lookup (R_bool minstret_increment) rs3)
                 (register_lookup (R_bitvector_32 mcountinhibit) rs3)
                 (register_lookup (R_bitvector_64 minstretcfg) rs3)
                 (register_lookup (R_bitvector_64 mcycle) rs3)
                 (register_lookup (R_bitvector_64 mtime) rs3)
                 (register_lookup (R_bitvector_64 mip) rs3)
                 (uc_stvec C) (uc_mie C) (uc_mideleg C)
                 (register_lookup (R_bitvector_64 medeleg) rs3) MENVCFG_S
                 (register_lookup (R_bitvector_64 mstateen0) rs3)
                 (register_lookup (R_bitvector_32 sstateen0) rs3)
                 (register_lookup (R_bitvector_32 mcounteren) rs3)
                 (register_lookup (R_bitvector_32 scounteren) rs3)
                 (register_lookup mhpmcounter rs3)
                 (register_lookup (R_bitvector_64 misa) rs3)
                 (register_lookup (R_bitvector_64 mseccfg) rs3)
                 (register_lookup (R_bitvector_64 senvcfg) rs3)
                 (register_lookup pma_regions rs3)
                 (register_lookup htif_tohost_base rs3)
                 (register_lookup (R_bitvector_1 elp) rs3)
                 usatp pcfg paddr tlbvec
                 ltac:(rewrite /u_pins_regs_at; split_and!;
                       [ exact Lhs | exact Lpriv | reflexivity
                       | reflexivity | reflexivity | reflexivity
                       | exact Lpc | exact Lnpc | exact (u_regfile_agree rs3) ])
                 ltac:(rewrite /u_pins_tick; split_and!; reflexivity)
                 ltac:(rewrite /u_pins_cfg; split_and!;
                       [ exact Lstvec | exact Lmie | exact Lmdl
                       | reflexivity | exact Lmenv | reflexivity | reflexivity
                       | reflexivity | reflexivity | reflexivity ])
                 ltac:(rewrite /u_pins_hw; split_and!; reflexivity)
                 ltac:(rewrite /u_pins_pt; split_and!;
                       [ exact Lsatp | exact Lpcfg | exact Lpaddr | exact Ltlb ])
                 with "Hrw Hro")
      as "(Hhs & Hpriv & Hms & Hsc & Hstval & Hsepc & HPC & HnPC & Hgpr &
           Hminstret & Hmincr & #Hmcnt & #Hmicfg & Hmcycle & Hmtime & Hmip &
           Hstvec & Hmie & Hmdl & _ & Hmenv & _ & _ & _ & _ & _ &
           _ & _ & _ & _ & _ & _ &
           Hsatp & Htlb & Hpcfg & Hpaddr)".
    iApply (user_trap_frame_intro C pt Rut _ _ _ _ (u_regfile rs3) Hmsok
              with "Hhs Hpriv Hms Hsc Hstval Hsepc
                    [HPC HnPC Hresv Hminstret Hmincr Hmcycle Hmtime Hmip]
                    Hgpr [Hpmp Hbytes Hclose Hsatp Htlb Hpcfg Hpaddr]
                    [Hstvec Hmie Hmdl Hmenv] Hrut").
    - (* pc_is at the handler base *)
      rewrite /pc_is /minstret_res /clock_res.
      iFrame "HPC HnPC Hresv".
      iSplitL "Hminstret Hmincr".
      + iExists _, _, _, _. iFrame "Hminstret Hmincr Hmcnt Hmicfg".
      + iExists _, _, _. iFrame "Hmcycle Hmtime Hmip".
    - (* user_pt_inv, re-closed at the SAME tree and map *)
      iApply ("Hclose" $! t mm tlbvec
                (u_mem_step_refl pt t mm Hwf) Htlbok with "[-Hbytes] Hbytes").
      rewrite /upt_regs. iFrame "Hsatp Htlb".
      iApply ("Hpmp" with "Hpcfg Hpaddr").
    - (* user_cfg *)
      rewrite /user_cfg. iFrame "Hstvec Hmie Hmdl Hmenv".
      iFrame "Hmedl Hsenv Hmste Hsste".
      iSplitR; [ iExists mcenv, scenv; iFrame "Hmcen Hscen"
               | iExists hpm; iFrame "Hhpm" ].
  Qed.


  (* ===================================================================== *)
  (* §4  THE CYCLE TAIL, AND THE TWO PAYLOAD BUILDERS.                      *)
  (*                                                                        *)
  (* [swp_exec_step_full]'s continuation relates the file it hands back to   *)
  (* the file the ARM landed on only through [tsf_post] -- an existential    *)
  (* over the step -- and agreement off the three clock cells.  [u_tail]     *)
  (* is that relation with the existential discharged: either the tick ran   *)
  (* ([wrap_post]) or the hart entered wait (one [hart_state] write, no      *)
  (* tick).  Everything downstream reads the landing file through it.        *)
  (* ===================================================================== *)
  Definition u_tail (rs2 rs3 : regstate) : Prop :=
    (exists mi : mword 64,
       forall r : register, r ∈ u_Drw ∪ u_Dro -> r ∉ tk_clock3 ->
         register_lookup r rs3 = register_lookup r (wrap_post rs2 mi))
    \/ (exists (wr : WaitReason) (ib : mword 32),
          (wr = WAIT_WRS_STO \/ wr = WAIT_WRS_NTO) /\
          register_lookup cur_privilege rs2 = User /\
          forall r : register, r ∈ u_Drw ∪ u_Dro -> r ∉ tk_clock3 ->
            register_lookup r rs3
              = register_lookup r
                  (register_set hart_state (HART_WAITING (wr, ib)) rs2)).

  Lemma u_tail_of (rs1 rs2 rs3 : regstate) :
    (exists rsP : regstate, tsf_post (u_land rs1) rs2 rsP /\
       reg_agree_on ((u_Drw ∪ u_Dro) ∖ tk_clock3) rs3 rsP) ->
    u_tail rs2 rs3.
  Proof.
    intros (rsP & (st & Hq & Hsh) & Hag).
    assert (T : forall r : register, r ∈ u_Drw ∪ u_Dro -> r ∉ tk_clock3 ->
              register_lookup r rs3 = register_lookup r rsP).
    { intros r H1 H2. apply Hag, elem_of_difference. split; assumption. }
    destruct st as [ [ii pr] | x | [xv e] | [r ib] | wq ];
      try (destruct Hsh as (mi & ->); left; exists mi; exact T).
    destruct r as [u | i0 | wr0 | u | u | trp | u | ec | ed | u];
      try (destruct Hsh as (mi & ->); left; exists mi; exact T).
    (* Enter_Wait: the [u_land] tag names the reason *)
    destruct Hsh as (_ & ->).
    destruct Hq as (_ & _ & Hwr & Hcp).
    right. exists wr0, ib. split_and!; [ exact Hwr | exact Hcp | exact T ].
  Qed.

  (* what a register that the tail does NOT move reads, at either shape *)
  Lemma u_tail_reg (rs2 rs3 : regstate) (r : register) :
    u_tail rs2 rs3 ->
    r ∈ u_Drw ∪ u_Dro -> r ∉ tk_clock3 ->
    register_beq r (R_bitvector_64 minstret) = false ->
    register_beq r (R_bitvector_64 PC) = false ->
    register_beq r hart_state = false ->
    register_lookup r rs3 = register_lookup r rs2.
  Proof.
    intros [(mi & T) | (wr & ib & _ & _ & T)] Hin Hnc Hms Hpc Hhs.
    - rewrite (T r Hin Hnc). exact (wrap_post_other r rs2 mi Hms Hpc).
    - rewrite (T r Hin Hnc). exact (irrelevant_register_set r hart_state _ _ Hhs).
  Qed.

  (* ...and the three cells it DOES move *)
  Lemma u_tail_hart (rs2 rs3 : regstate) :
    register_lookup hart_state rs2 = HART_ACTIVE tt ->
    u_tail rs2 rs3 ->
    (register_lookup hart_state rs3 = HART_ACTIVE tt /\
     register_lookup (R_bitvector_64 PC) rs3
       = register_lookup (R_bitvector_64 nextPC) rs2 /\
     register_lookup (R_bitvector_64 nextPC) rs3
       = register_lookup (R_bitvector_64 nextPC) rs2)
    \/ (exists (wr : WaitReason) (ib : mword 32),
          user_hart_ok (HART_WAITING (wr, ib)) /\
          register_lookup cur_privilege rs2 = User /\
          register_lookup hart_state rs3 = HART_WAITING (wr, ib) /\
          register_lookup (R_bitvector_64 PC) rs3
            = register_lookup (R_bitvector_64 PC) rs2 /\
          register_lookup (R_bitvector_64 nextPC) rs3
            = register_lookup (R_bitvector_64 nextPC) rs2).
  Proof.
    intros Lhs [(mi & T) | (wr & ib & Hwr & Hcp & T)].
    - left. split_and!.
      + rewrite (T _ u_in_hart ltac:(u_notin_clock))
                (wrap_post_other hart_state rs2 mi eq_refl eq_refl). exact Lhs.
      + rewrite (T _ u_in_PC ltac:(u_notin_clock)). apply wrap_post_PC.
      + rewrite (T _ u_in_nPC ltac:(u_notin_clock))
                (wrap_post_other (R_bitvector_64 nextPC) rs2 mi eq_refl eq_refl).
        reflexivity.
    - right. exists wr, ib. split_and!.
      + exact Hwr.
      + exact Hcp.
      + rewrite (T _ u_in_hart ltac:(u_notin_clock)). apply register_lookup_set.
      + rewrite (T _ u_in_PC ltac:(u_notin_clock)).
        exact (irrelevant_register_set (R_bitvector_64 PC) hart_state _ _ eq_refl).
      + rewrite (T _ u_in_nPC ltac:(u_notin_clock)).
        exact (irrelevant_register_set (R_bitvector_64 nextPC) hart_state _ _ eq_refl).
  Qed.


  (* ------------------------------------------------------------------- *)
  (* The ACTIVE-at-User payload: the hart retired (or entered wait).       *)
  (* One builder covers both, because [u_tail] leaves exactly those two    *)
  (* shapes and [user_inv] accepts either hart state.                      *)
  (* ------------------------------------------------------------------- *)
  Lemma u_psi_active (t : ptree) (mm : PtBytes.pamap) (usatp : mword 64)
      (tlbvec : type_of_register tlb)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (mcenv scenv : mword 32) (hpm : type_of_register mhpmcounter)
      (rs1 rs2 : regstate) :
    register_lookup hart_state rs2 = HART_ACTIVE tt ->
    register_lookup cur_privilege rs2 = User ->
    user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rs2) ->
    register_lookup (R_bitvector_64 stvec) rs2 = uc_stvec C ->
    register_lookup (R_bitvector_64 mie) rs2 = uc_mie C ->
    register_lookup (R_bitvector_64 mideleg) rs2 = uc_mideleg C ->
    register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S ->
    register_lookup (R_bitvector_64 satp) rs2 = usatp ->
    register_lookup pmpcfg_n rs2 = pcfg ->
    register_lookup pmpaddr_n rs2 = paddr ->
    register_lookup tlb rs2 = tlbvec ->
    tlb_ok_pt (mword_of_int 0) t tlbvec ->
    u_mem_wf pt t mm ->
    resv_any cpu_id -∗
    u_open C pt t mm usatp pcfg paddr mcenv scenv hpm -∗
    Rut pt -∗
    u_step_psi C pt Rut rs1 rs2.
  Proof.
    intros Lhs Lpriv Hmsok Lstvec Lmie Lmdl Lmenv Lsatp Lpcfg Lpaddr Ltlb
      Htlbok Hwf.
    iIntros "Hresv Hopen Hrut".
    rewrite /u_step_psi. iFrame "Hresv".
    iIntros (rs3) "%Htp Hrw Hro Hresv Hk".
    pose proof (u_tail_of rs1 rs2 rs3 Htp) as Htail.
    assert (T : forall r : register, r ∈ u_Drw ∪ u_Dro -> r ∉ tk_clock3 ->
              register_beq r (R_bitvector_64 minstret) = false ->
              register_beq r (R_bitvector_64 PC) = false ->
              register_beq r hart_state = false ->
              register_lookup r rs3 = register_lookup r rs2)
      by (intros r H1 H2 H3 H4 H5; exact (u_tail_reg rs2 rs3 r Htail H1 H2 H3 H4 H5)).
    rewrite /u_open.
    iDestruct "Hopen" as "(Hpmp & #Hmedl & #Hsenv & #Hmste & #Hsste &
                           #Hmcen & #Hscen & #Hhpm & #Hclaims & Hbytes & Hclose)".
    iDestruct "Hk" as "[Hretire _]".
    iApply "Hretire".
    destruct (u_tail_hart rs2 rs3 Lhs Htail)
      as [(Lhs3 & Lpc3 & Lnpc3) | (wr & ib & Hhok & _ & Lhs3 & Lpc3 & Lnpc3)].
    - iApply (u_close_inv C pt Rut t mm usatp tlbvec pcfg paddr
                mcenv scenv hpm rs3 (HART_ACTIVE tt)
                (register_lookup (R_bitvector_64 mstatus) rs2)
                (register_lookup (R_bitvector_64 nextPC) rs2)
                (register_lookup (R_bitvector_64 nextPC) rs2)
                I Hmsok ltac:(intros u _; reflexivity)
                Lhs3
                ltac:(rewrite (T _ u_in_priv ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Lpriv)
                ltac:(exact (T _ u_in_mst ltac:(u_notin_clock) eq_refl eq_refl eq_refl))
                Lpc3 Lnpc3
                ltac:(rewrite (T _ u_in_stvec ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Lstvec)
                ltac:(rewrite (T _ u_in_mie ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Lmie)
                ltac:(rewrite (T _ u_in_mdl ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Lmdl)
                ltac:(rewrite (T _ u_in_menv ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Lmenv)
                ltac:(rewrite (T _ u_in_satp ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Lsatp)
                ltac:(rewrite (T _ u_in_pcfg ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Lpcfg)
                ltac:(rewrite (T _ u_in_paddr ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Lpaddr)
                ltac:(rewrite (T _ u_in_tlb ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Ltlb)
                Htlbok Hwf
                with "Hpmp Hmedl Hsenv Hmste Hsste Hmcen Hscen Hhpm
                      Hrw Hro Hresv Hclaims Hbytes Hclose Hrut").
    - iApply (u_close_inv C pt Rut t mm usatp tlbvec pcfg paddr
                mcenv scenv hpm rs3 (HART_WAITING (wr, ib))
                (register_lookup (R_bitvector_64 mstatus) rs2)
                (register_lookup (R_bitvector_64 PC) rs2)
                (register_lookup (R_bitvector_64 nextPC) rs2)
                Hhok Hmsok ltac:(intros u Hu; discriminate Hu)
                Lhs3
                ltac:(rewrite (T _ u_in_priv ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Lpriv)
                ltac:(exact (T _ u_in_mst ltac:(u_notin_clock) eq_refl eq_refl eq_refl))
                Lpc3 Lnpc3
                ltac:(rewrite (T _ u_in_stvec ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Lstvec)
                ltac:(rewrite (T _ u_in_mie ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Lmie)
                ltac:(rewrite (T _ u_in_mdl ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Lmdl)
                ltac:(rewrite (T _ u_in_menv ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Lmenv)
                ltac:(rewrite (T _ u_in_satp ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Lsatp)
                ltac:(rewrite (T _ u_in_pcfg ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Lpcfg)
                ltac:(rewrite (T _ u_in_paddr ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Lpaddr)
                ltac:(rewrite (T _ u_in_tlb ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Ltlb)
                Htlbok Hwf
                with "Hpmp Hmedl Hsenv Hmste Hsste Hmcen Hscen Hhpm
                      Hrw Hro Hresv Hclaims Hbytes Hclose Hrut").
  Qed.


  (* ------------------------------------------------------------------- *)
  (* The TRAPPED payload.  The wait shape is IMPOSSIBLE here and that is    *)
  (* what [u_land]'s privilege tag buys: a trapped file is at Supervisor,   *)
  (* and the tag pins the enter-wait arm's file at User.                    *)
  (* ------------------------------------------------------------------- *)
  Lemma u_psi_trap (t : ptree) (mm : PtBytes.pamap) (usatp : mword 64)
      (tlbvec : type_of_register tlb)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (mcenv scenv : mword 32) (hpm : type_of_register mhpmcounter)
      (rs1 rs2 : regstate) :
    register_lookup hart_state rs2 = HART_ACTIVE tt ->
    register_lookup cur_privilege rs2 = Supervisor ->
    trap_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rs2) ->
    register_lookup (R_bitvector_64 nextPC) rs2 = stvec_base (uc_stvec C) ->
    register_lookup (R_bitvector_64 stvec) rs2 = uc_stvec C ->
    register_lookup (R_bitvector_64 mie) rs2 = uc_mie C ->
    register_lookup (R_bitvector_64 mideleg) rs2 = uc_mideleg C ->
    register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S ->
    register_lookup (R_bitvector_64 satp) rs2 = usatp ->
    register_lookup pmpcfg_n rs2 = pcfg ->
    register_lookup pmpaddr_n rs2 = paddr ->
    register_lookup tlb rs2 = tlbvec ->
    tlb_ok_pt (mword_of_int 0) t tlbvec ->
    u_mem_wf pt t mm ->
    resv_any cpu_id -∗
    u_open C pt t mm usatp pcfg paddr mcenv scenv hpm -∗
    Rut pt -∗
    u_step_psi C pt Rut rs1 rs2.
  Proof.
    intros Lhs Lpriv Hmsok Lnpc Lstvec Lmie Lmdl Lmenv Lsatp Lpcfg Lpaddr Ltlb
      Htlbok Hwf.
    iIntros "Hresv Hopen Hrut".
    rewrite /u_step_psi. iFrame "Hresv".
    iIntros (rs3) "%Htp Hrw Hro Hresv Hk".
    pose proof (u_tail_of rs1 rs2 rs3 Htp) as Htail.
    assert (T : forall r : register, r ∈ u_Drw ∪ u_Dro -> r ∉ tk_clock3 ->
              register_beq r (R_bitvector_64 minstret) = false ->
              register_beq r (R_bitvector_64 PC) = false ->
              register_beq r hart_state = false ->
              register_lookup r rs3 = register_lookup r rs2)
      by (intros r H1 H2 H3 H4 H5; exact (u_tail_reg rs2 rs3 r Htail H1 H2 H3 H4 H5)).
    iDestruct "Hk" as "[_ Htrap]".
    iApply "Htrap".
    destruct (u_tail_hart rs2 rs3 Lhs Htail)
      as [(Lhs3 & Lpc3 & Lnpc3) | (wr & ib & _ & Hcp & _)];
      [| rewrite Lpriv in Hcp; discriminate Hcp ].
    rewrite Lnpc in Lpc3. rewrite Lnpc in Lnpc3.
    iApply (u_close_trap t mm usatp tlbvec pcfg paddr mcenv scenv hpm rs3
              ltac:(rewrite (T _ u_in_mst ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Hmsok)
              Lhs3
              ltac:(rewrite (T _ u_in_priv ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Lpriv)
              Lpc3 Lnpc3
              ltac:(rewrite (T _ u_in_stvec ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Lstvec)
              ltac:(rewrite (T _ u_in_mie ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Lmie)
              ltac:(rewrite (T _ u_in_mdl ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Lmdl)
              ltac:(rewrite (T _ u_in_menv ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Lmenv)
              ltac:(rewrite (T _ u_in_satp ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Lsatp)
              ltac:(rewrite (T _ u_in_pcfg ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Lpcfg)
              ltac:(rewrite (T _ u_in_paddr ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Lpaddr)
              ltac:(rewrite (T _ u_in_tlb ltac:(u_notin_clock) eq_refl eq_refl eq_refl); exact Ltlb)
              Htlbok Hwf
              with "Hopen Hrw Hro Hresv Hrut").
  Qed.

End UserActiveClass.
