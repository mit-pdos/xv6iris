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
Require Import MinstretInv WireInv RegFile UserBits AlignBits WpGpr.
Require Import TrampPt KptTree UptTree.
Require Import SmodeCore WpIntrCore.
Require Import HartSwp HartLift HartSpan HartMCycle HartStepFull HartRunFull.
Require Import HartMemRun PtreeType PtTree SmodePte PtBytes UserBytes InstrBytes.
Require Import UserFrame UserClassifyAsm.
Require Import UserPtTree UserExec UserStep UserStepFull.
Require Import UserFetchPt UserClassify.
Require Import UserTrap.
(* the swp bridge needs [exec] itself, and the five PURE fetch producers *)
Require Import RiscvExec.
Require Import UserFetchCert UserFaultCert.
(* the cycle rule's monadic plumbing (§7), the align-fault certificate (§2b)
   and the decode reference the totalities are stated against *)
Require Import RiscvTryStep RiscvFetchExec.
Require Import HartSpanChar HartRunGen HartMemAsm PtWalkCert.
Require Import UserFetch WpDecodeBridge DecodeTotalU UserTotalU.
From iris.base_logic.lib Require Import ghost_map.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

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

(* ===================================================================== *)
(* §2b  THE SIXTH FETCH PRODUCER: an ODD pc.                              *)
(*                                                                        *)
(* [active_class] classifies EVERY [va] -- neither [user_inv] nor the      *)
(* cycle rule constrains the pc's alignment -- so the case tree has a      *)
(* branch that the §14.4 package does not cover: both the 4-aligned and    *)
(* the 2-aligned families start from bit0 = 0.  An ODD pc raises           *)
(* [E_Fetch_Addr_Align] before anything translates or reads, so this is    *)
(* the CHEAPEST of the six: three [PC] reads and the misalignment test.    *)
(* [UserFetch.exec_fetch_align_fault] is the exec side; only the [goodmb]  *)
(* certificate was missing.                                                *)
(* ===================================================================== *)
Section FetchAlignCert.
  Context (Dr Dw : register -> bool).
  Context (s : mstate) (mm : PtBytes.pamap) (pc : mword 64).
  Hypothesis HDpc : Dr PC = true.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Hbit0 : neq_vec (access_vec_dec pc 0) ('b"0") = true.

  Let HrdPC : exec (Defs.read_reg PC) s = Some (pc, s).
  Proof. rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. Qed.

  Let HrdPCg : goodmb Dr Dw (Defs.read_reg PC : M _) s mm = true.
  Proof. rewrite goodmb_read_reg. exact HDpc. Qed.

  Lemma goodmb_fetch_align_fault : goodmb Dr Dw (fetch tt) s mm = true.
  Proof using Dr Dw s mm pc HDpc HpcPC Hbit0.
    unfold fetch. apply goodmb_cer.
    change (get_config_rvfi tt) with false. cbv iota beta.
    gmm_lift HrdPCg HrdPC.
    gmm_lift HrdPCg HrdPC.
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    match goal with |- context[Defs.bind ?A ?K] =>
      assert (Halg : goodmb Dr Dw A s mm = true);
      [ | assert (Hale : execR A s = Some (inr true, s)) ] end.
    { erewrite gm_bind0R; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
      unfold Defs.or_boolM.
      erewrite gm_liftR_nest; [ | exact HrdPCg | exact HrdPC ].
      rewrite Hbit0. rewrite bindR_ret. cbv iota beta. reflexivity. }
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      unfold Defs.or_boolM.
      rewrite (execR_bind_Some _ _ _ true s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0.
          apply execR_returnR_fwd. }
      cbv iota beta. apply execR_returnR_fwd. }
    erewrite (gm_bindR Dr Dw _ _ s s mm true Halg Hale). cbv iota beta.
    gmm_lift HrdPCg HrdPC.
    apply goodmb_returnm.
  Qed.

End FetchAlignCert.

(* the producer, in the shape the other five have *)
Lemma u_fetch_align_fault_pure (P : uptd) (t : ptree) (mm : PtBytes.pamap)
    (rsf : regstate) (va : mword 64) :
  register_lookup PC rsf = va ->
  neq_vec (access_vec_dec va 0) ('b"0") = true ->
  u_exec_pins P t rsf ->
  u_mem_wf P t mm ->
  exec (fetch tt) (u_state rsf mm)
    = Some (F_Error (E_Fetch_Addr_Align tt, va), u_state rsf mm)
  /\ goodmb Du_r Du_w (fetch tt) (u_state rsf mm) mm = true
  /\ tlb_ok_pt (mword_of_int 0) t (register_lookup tlb rsf)
  /\ u_mem_step P t t mm mm.
Proof.
  intros Lpc Hbit0 Hpins Hwf.
  pose proof Hpins as (_ & _ & _ & Htlbok).
  split_and!.
  - exact (exec_fetch_align_fault (u_state rsf mm) va Lpc Hbit0).
  - exact (goodmb_fetch_align_fault Du_r Du_w (u_state rsf mm) mm va
             ltac:(vm_compute; reflexivity) Lpc Hbit0).
  - exact Htlbok.
  - exact (u_mem_step_refl P t mm Hwf).
Qed.

(* ===================================================================== *)
(* §5a  THE FILE THE U TRAP TOWER LANDS ON.                               *)
(*                                                                       *)
(* [UserTrap]'s [UTrapReduce] hands its landing file back only up to      *)
(* agreement on the footprint -- the file itself is a [Let] chain that    *)
(* section discharge INLINES, so no name for it escapes the section.      *)
(* [u_step_post] however binds [rs2] OUTSIDE the [swp] (the [u_land] tag  *)
(* is a pure conjunct of the arm, not of its postcondition), so a trap    *)
(* arm has to name the landing file before it runs the tower.  This is    *)
(* that name: [UTrapReduce]'s [s9] plus [set_next_pc], at the REGISTER    *)
(* level (the tower's memory is untouched, so the [mstate] wrapper adds   *)
(* nothing), written so that it is CONVERTIBLE to what the producers      *)
(* spell -- the [let]s keep the conversion linear instead of unfolding    *)
(* [set_reg]'s three-fold body into a 3^12 tree (RiscvLang.v:92).         *)
(* ===================================================================== *)
Definition u_trap_rs (rsf : regstate) (c : TrapCause) (info : option (mword 64))
    (pcx stvec_v : mword 64) : regstate :=
  let ms_v := register_lookup (R_bitvector_64 mstatus) rsf in
  let sc_v := register_lookup (R_bitvector_64 scause) rsf in
  let ms_e := update_subrange_vec_dec ms_v 23 23
                (landing_pad_bits_backwards NO_LP_EXPECTED) in
  let c1   := update_subrange_vec_dec sc_v (64 - 1) (64 - 1)
                (bool_to_bit (trapCause_is_interrupt c)) in
  let c2   := update_subrange_vec_dec c1 (64 - 2) 0
                (zero_extend' (64 - 1) (trapCause_bits_forwards c)) in
  let ms_a := update_subrange_vec_dec ms_e 5 5 (_get_Mstatus_SIE ms_e) in
  let ms_b := update_subrange_vec_dec ms_a 1 1 ('b"0") in
  let ms_c := update_subrange_vec_dec ms_b 8 8 ('b"0") in
  register_set nextPC (stvec_base stvec_v)
   (register_set cur_privilege Supervisor
    (register_set sepc pcx
     (register_set stval (tval info)
      (register_set mstatus ms_c
       (register_set mstatus ms_b
        (register_set mstatus ms_a
         (register_set scause c2
          (register_set scause c1
           (register_set elp (landing_pad_bits_backwards NO_LP_EXPECTED)
            (register_set mstatus ms_e rsf)))))))))).

(* peel the landing file down to [rsf]; stops on its own at the first
   cell the tower DOES write. *)
Local Ltac u_trap_peel :=
  unfold u_trap_rs; cbv zeta;
  repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).

Local Ltac u_in_ro := apply (bool_decide_unpack _); vm_compute; reflexivity.

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


  (* ===================================================================== *)
  (* §5  THE FOUR TRAP ARMS.                                                *)
  (*                                                                        *)
  (* Each is ONE instantiation of [UserTrap]'s [UTrapReduce] section at the  *)
  (* tier's concrete state [s := UserClassifyAsm.u_state rsf mm] -- [rsf]    *)
  (* being the file the fetch (or fetch+execute) landed on -- wrapped so     *)
  (* that the postcondition is [u_arm_res rs1 rs2] at [rs2 := u_trap_rs …].  *)
  (* [UTrapReduce]'s eight hypotheses come out of [active_class]' pins:      *)
  (*   Hpriv/Hpc     the cur_privilege and PC pins,                          *)
  (*   Hms/Hsc/Help  DEFINITIONAL (the section variables are instantiated at *)
  (*                 [rsf]'s own lookups -- [Help] at the value              *)
  (*                 [u_hw_pins]' elp conjunct forces, via [elp_no_lp]),     *)
  (*   Hstvec        the [uc_stvec] pin,                                     *)
  (*   HmisaS        [u_hw_pins]' [misa = MISA_C],                           *)
  (*   Htvd          the record field [uc_tvd].                              *)
  (* The ONE thing [active_class] does not pin is [medeleg]; it is recovered *)
  (* in Iris from [u_open]'s persistent cell against the read-only frame's   *)
  (* own discarded one ([u_medeleg_pin] below).                              *)
  (* ===================================================================== *)

  (* two persistent cells the tower needs, read off the read-only frame *)
  Lemma u_ro_elp_acc (dq : dfrac) (rs : regstate) :
    hreg_frame_ro (u_Df dq) rs u_Dro -∗
    (R_bitvector_1 elp) ↦ᵣ□ (register_lookup (R_bitvector_1 elp) rs) ∗
    hreg_frame_ro (u_Df dq) rs u_Dro.
  Proof.
    iIntros "H". rewrite /hreg_frame_ro.
    iDestruct (big_sepS_elem_of_acc _ u_Dro (R_bitvector_1 elp : register)
                 with "H") as "[Hc Hback]"; [ u_in_ro | ].
    iAssert ((R_bitvector_1 elp) ↦ᵣ□ (register_lookup (R_bitvector_1 elp) rs))%I
      with "[Hc]" as "#Hc'"; [ iExact "Hc" | ].
    iFrame "Hc'". iApply "Hback". iExact "Hc'".
  Qed.

  Lemma u_ro_medl_acc (dq : dfrac) (rs : regstate) :
    hreg_frame_ro (u_Df dq) rs u_Dro -∗
    (R_bitvector_64 medeleg) ↦ᵣ□ (register_lookup (R_bitvector_64 medeleg) rs) ∗
    hreg_frame_ro (u_Df dq) rs u_Dro.
  Proof.
    iIntros "H". rewrite /hreg_frame_ro.
    iDestruct (big_sepS_elem_of_acc _ u_Dro (R_bitvector_64 medeleg : register)
                 with "H") as "[Hc Hback]"; [ u_in_ro | ].
    iAssert ((R_bitvector_64 medeleg) ↦ᵣ□
               (register_lookup (R_bitvector_64 medeleg) rs))%I
      with "[Hc]" as "#Hc'"; [ iExact "Hc" | ].
    iFrame "Hc'". iApply "Hback". iExact "Hc'".
  Qed.

  Lemma u_open_medl (t : ptree) (mm : PtBytes.pamap) (usatp : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (mcenv scenv : mword 32) (hpm : type_of_register mhpmcounter) :
    u_open C pt t mm usatp pcfg paddr mcenv scenv hpm -∗
    (R_bitvector_64 medeleg) ↦ᵣ□ uc_medeleg C ∗
    u_open C pt t mm usatp pcfg paddr mcenv scenv hpm.
  Proof.
    iIntros "H". rewrite /u_open.
    iDestruct "H" as "(H1 & #H2 & H3)". iFrame "H2 H1 H3".
  Qed.

  Lemma u_reg_pointsto_agree (r : register) (dq1 dq2 : dfrac)
      (v1 v2 : type_of_register r) :
    reg_pointsto r dq1 v1 -∗ reg_pointsto r dq2 v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "H1 H2". rewrite /reg_pointsto.
    iDestruct (ghost_map_elem_agree with "H1 H2") as %He.
    iPureIntro. exact (reg_existT_inj r v1 v2 He).
  Qed.

  (* [medeleg]'s VALUE, which [active_class] does not pin: [u_open] holds
     the cell at [uc_medeleg C] and the read-only frame holds it at the
     entry file's own lookup, and both are discarded, so they agree. *)
  Lemma u_medeleg_pin (t : ptree) (mm : PtBytes.pamap) (usatp : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (mcenv scenv : mword 32) (hpm : type_of_register mhpmcounter)
      (rs : regstate) :
    u_open C pt t mm usatp pcfg paddr mcenv scenv hpm -∗
    hreg_frame_ro (u_Df (uc_dqc C)) rs u_Dro -∗
    ⌜register_lookup (R_bitvector_64 medeleg) rs = uc_medeleg C⌝ ∗
    u_open C pt t mm usatp pcfg paddr mcenv scenv hpm ∗
    hreg_frame_ro (u_Df (uc_dqc C)) rs u_Dro.
  Proof.
    iIntros "Hopen Hro".
    iDestruct (u_open_medl with "Hopen") as "[#Hm1 Hopen]".
    iDestruct (u_ro_medl_acc with "Hro") as "[#Hm2 Hro]".
    iDestruct (u_reg_pointsto_agree with "Hm2 Hm1") as %Heq.
    iFrame "Hopen Hro". iPureIntro. exact Heq.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE SHARED CLOSER: one producer's postcondition -> [u_arm_res].       *)
  (* ------------------------------------------------------------------- *)
  Lemma u_arm_close (t : ptree) (mm : PtBytes.pamap) (usatp : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (mcenv scenv : mword 32) (hpm : type_of_register mhpmcounter)
      (rs1 rsf rs' : regstate) (c : TrapCause) (info : option (mword 64))
      (pcx : mword 64) :
    register_lookup hart_state rsf = HART_ACTIVE tt ->
    user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rsf) ->
    register_lookup (R_bitvector_64 stvec) rsf = uc_stvec C ->
    register_lookup (R_bitvector_64 mie) rsf = uc_mie C ->
    register_lookup (R_bitvector_64 mideleg) rsf = uc_mideleg C ->
    register_lookup (R_bitvector_64 menvcfg) rsf = MENVCFG_S ->
    register_lookup (R_bitvector_64 satp) rsf = usatp ->
    register_lookup pmpcfg_n rsf = pcfg ->
    register_lookup pmpaddr_n rsf = paddr ->
    tlb_ok_pt (mword_of_int 0) t (register_lookup tlb rsf) ->
    u_mem_wf pt t mm ->
    reg_agree_on (u_Drw ∪ u_Dro) rs' (u_trap_rs rsf c info pcx (uc_stvec C)) ->
    hreg_frame rs' u_Drw -∗
    hreg_frame_ro (u_Df (uc_dqc C)) rs' u_Dro -∗
    resv_any cpu_id -∗
    u_open C pt t mm usatp pcfg paddr mcenv scenv hpm -∗
    Rut pt -∗
    u_arm_res C pt Rut rs1 (u_trap_rs rsf c info pcx (uc_stvec C)).
  Proof.
    intros Lhs Hmsok Lstvec Lmie Lmdl Lmenv Lsatp Lpcfg Lpaddr Htlbok Hwf Hag.
    iIntros "Hrw Hro Hany Hopen Hrut".
    rewrite /u_arm_res.
    rewrite <- (hreg_frame_ext rs' (u_trap_rs rsf c info pcx (uc_stvec C)) u_Drw
                 ltac:(intros r Hr; apply Hag, elem_of_union_l, Hr)).
    rewrite <- (hreg_frame_ro_ext (u_Df (uc_dqc C)) rs'
                 (u_trap_rs rsf c info pcx (uc_stvec C)) u_Dro
                 ltac:(intros r Hr; apply Hag, elem_of_union_r, Hr)).
    iFrame "Hrw Hro".
    iApply (u_psi_trap t mm usatp (register_lookup tlb rsf) pcfg paddr
              mcenv scenv hpm rs1 (u_trap_rs rsf c info pcx (uc_stvec C))
              ltac:(u_trap_peel; exact Lhs)
              ltac:(u_trap_peel; apply register_lookup_set)
              ltac:(u_trap_peel; rewrite register_lookup_set;
                    exact (utrap_ms_ok _ _ Hmsok))
              ltac:(u_trap_peel; apply register_lookup_set)
              ltac:(u_trap_peel; exact Lstvec)
              ltac:(u_trap_peel; exact Lmie)
              ltac:(u_trap_peel; exact Lmdl)
              ltac:(u_trap_peel; exact Lmenv)
              ltac:(u_trap_peel; exact Lsatp)
              ltac:(u_trap_peel; exact Lpcfg)
              ltac:(u_trap_peel; exact Lpaddr)
              ltac:(u_trap_peel; reflexivity)
              Htlbok Hwf
              with "Hany Hopen Hrut").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ARM 1 -- [Step_Pending_Interrupt].                                    *)
  (* ------------------------------------------------------------------- *)
  Lemma u_arm_pending_interrupt
      (t : ptree) (mm : PtBytes.pamap) (usatp : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (mcenv scenv : mword 32) (hpm : type_of_register mhpmcounter)
      (rs1 rsf : regstate) (i : InterruptType) :
    register_lookup hart_state rsf = HART_ACTIVE tt ->
    register_lookup cur_privilege rsf = User ->
    user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rsf) ->
    register_lookup (R_bool minstret_increment) rsf
      = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs1)
          (register_lookup (R_bitvector_64 minstretcfg) rs1)
          (register_lookup cur_privilege rs1) ->
    register_lookup (R_bitvector_64 stvec) rsf = uc_stvec C ->
    register_lookup (R_bitvector_64 mie) rsf = uc_mie C ->
    register_lookup (R_bitvector_64 mideleg) rsf = uc_mideleg C ->
    register_lookup (R_bitvector_64 menvcfg) rsf = MENVCFG_S ->
    register_lookup (R_bitvector_64 satp) rsf = usatp ->
    register_lookup pmpcfg_n rsf = pcfg ->
    register_lookup pmpaddr_n rsf = paddr ->
    u_exec_pins pt t rsf ->
    u_mem_wf pt t mm ->
    gen_cert -∗
    resv_frag cpu_id None -∗
    hreg_frame rsf u_Drw -∗
    hreg_frame_ro (u_Df (uc_dqc C)) rsf u_Dro -∗
    u_open C pt t mm usatp pcfg paddr mcenv scenv hpm -∗
    Rut pt -∗
    u_step_post C pt Rut rs1 (Step_Pending_Interrupt (i, Supervisor)).
  Proof.
    intros Lhs Lpriv Hmsok Lmi Lstvec Lmie Lmdl Lmenv Lsatp Lpcfg Lpaddr
      Hpins Hwf.
    destruct Hpins as ((Hmisa & _ & _ & _ & _ & Helpne) & _ & _ & Htlbok).
    pose proof (elp_no_lp _ Helpne) as Lelp.
    assert (HmisaS : eq_vec (_get_Misa_S (register_lookup (R_bitvector_64 misa) rsf))
                       ('b"1") = true)
      by (rewrite Hmisa; vm_compute; reflexivity).
    iIntros "#Hcert Hfrag Hrw Hro Hopen Hrut".
    iDestruct (u_ro_elp_acc with "Hro") as "[#Help Hro]".
    rewrite Lelp.
    iDestruct (resv_any_intro cpu_id None with "Hfrag") as "Hany".
    rewrite /u_step_post.
    iExists (u_trap_rs rsf (Interrupt i) None
               (register_lookup (R_bitvector_64 PC) rsf) (uc_stvec C)).
    iSplitR "Hany Hrw Hro Hopen Hrut".
    { iPureIntro. rewrite /u_land. split_and!;
        [ u_trap_peel; exact Lhs | u_trap_peel; exact Lmi | exact I ]. }
    iApply (swp_mono with "[Hopen Hrut] [Hany Hrw Hro]").
    2:{ iApply (swp_handle_interrupt_u (u_state rsf mm) (Interrupt i) None
                  (register_lookup (R_bitvector_64 PC) rsf)
                  (register_lookup (R_bitvector_64 mstatus) rsf)
                  (register_lookup (R_bitvector_64 scause) rsf)
                  (uc_stvec C) (landing_pad_bits_backwards NO_LP_EXPECTED)
                  Lpriv eq_refl eq_refl Lstvec Lelp HmisaS (uc_tvd C) eq_refl
                  Du_r Du_w u_Drw u_Dro (u_Df (uc_dqc C)) rsf i eq_refl eq_refl
                  u_disj Du_r_sub Du_w_sub
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(intros r _; reflexivity) eq_refl
                  with "Hcert Hany Help Hrw Hro"). }
    iIntros (v) "Hpost".
    iDestruct "Hpost" as (rs') "(%Hag & Hrw & Hro & Hany)".
    iApply (u_arm_close t mm usatp pcfg paddr mcenv scenv hpm rs1 rsf rs'
              (Interrupt i) None (register_lookup (R_bitvector_64 PC) rsf)
              Lhs Hmsok Lstvec Lmie Lmdl Lmenv Lsatp Lpcfg Lpaddr Htlbok Hwf
              Hag with "Hrw Hro Hany Hopen Hrut").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ARM 2 -- [Step_Fetch_Failure]: the generic delegated-exception tower.  *)
  (* ------------------------------------------------------------------- *)
  Lemma u_arm_fetch_failure
      (t : ptree) (mm : PtBytes.pamap) (usatp : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (mcenv scenv : mword 32) (hpm : type_of_register mhpmcounter)
      (rs1 rsf : regstate) (e : ExceptionType) (xv : mword 64) :
    user_exc e = true ->
    register_lookup hart_state rsf = HART_ACTIVE tt ->
    register_lookup cur_privilege rsf = User ->
    user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rsf) ->
    register_lookup (R_bool minstret_increment) rsf
      = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs1)
          (register_lookup (R_bitvector_64 minstretcfg) rs1)
          (register_lookup cur_privilege rs1) ->
    register_lookup (R_bitvector_64 stvec) rsf = uc_stvec C ->
    register_lookup (R_bitvector_64 mie) rsf = uc_mie C ->
    register_lookup (R_bitvector_64 mideleg) rsf = uc_mideleg C ->
    register_lookup (R_bitvector_64 menvcfg) rsf = MENVCFG_S ->
    register_lookup (R_bitvector_64 satp) rsf = usatp ->
    register_lookup pmpcfg_n rsf = pcfg ->
    register_lookup pmpaddr_n rsf = paddr ->
    u_exec_pins pt t rsf ->
    u_mem_wf pt t mm ->
    gen_cert -∗
    resv_any cpu_id -∗
    hreg_frame rsf u_Drw -∗
    hreg_frame_ro (u_Df (uc_dqc C)) rsf u_Dro -∗
    u_open C pt t mm usatp pcfg paddr mcenv scenv hpm -∗
    Rut pt -∗
    u_step_post C pt Rut rs1 (Step_Fetch_Failure (Virtaddr xv, e)).
  Proof.
    intros Hue Lhs Lpriv Hmsok Lmi Lstvec Lmie Lmdl Lmenv Lsatp Lpcfg Lpaddr
      Hpins Hwf.
    destruct Hpins as ((Hmisa & _ & _ & _ & _ & Helpne) & _ & _ & Htlbok).
    pose proof (elp_no_lp _ Helpne) as Lelp.
    assert (HmisaS : eq_vec (_get_Misa_S (register_lookup (R_bitvector_64 misa) rsf))
                       ('b"1") = true)
      by (rewrite Hmisa; vm_compute; reflexivity).
    iIntros "#Hcert Hany Hrw Hro Hopen Hrut".
    iDestruct (u_ro_elp_acc with "Hro") as "[#Help Hro]".
    rewrite Lelp.
    iDestruct (u_medeleg_pin with "Hopen Hro") as "(%Lmedl & Hopen & Hro)".
    assert (Hdel : bit_to_bool
                     (access_vec_dec (register_lookup (R_bitvector_64 medeleg) rsf)
                        (uint (exceptionType_bits_forwards e))) = true)
      by (rewrite Lmedl; exact (uc_del C e Hue)).
    rewrite /u_step_post.
    iExists (u_trap_rs rsf (rv64d_types.Exception e)
               (xtval_exception_value e xv)
               (register_lookup (R_bitvector_64 PC) rsf) (uc_stvec C)).
    iSplitR "Hany Hrw Hro Hopen Hrut".
    { iPureIntro. rewrite /u_land. split_and!;
        [ u_trap_peel; exact Lhs | u_trap_peel; exact Lmi | exact I ]. }
    iApply (swp_mono with "[Hopen Hrut] [Hany Hrw Hro]").
    2:{ iApply (swp_handle_exception_u (u_state rsf mm)
                  (rv64d_types.Exception e) (xtval_exception_value e xv)
                  (register_lookup (R_bitvector_64 PC) rsf)
                  (register_lookup (R_bitvector_64 mstatus) rsf)
                  (register_lookup (R_bitvector_64 scause) rsf)
                  (uc_stvec C) (landing_pad_bits_backwards NO_LP_EXPECTED)
                  Lpriv eq_refl eq_refl Lstvec Lelp HmisaS (uc_tvd C) eq_refl
                  Du_r Du_w u_Drw u_Dro (u_Df (uc_dqc C)) rsf e xv
                  eq_refl eq_refl Hdel
                  u_disj Du_r_sub Du_w_sub
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(intros r _; reflexivity) eq_refl
                  with "Hcert Hany Help Hrw Hro"). }
    iIntros (v) "Hpost".
    iDestruct "Hpost" as (rs') "(%Hag & Hrw & Hro & Hany)".
    iApply (u_arm_close t mm usatp pcfg paddr mcenv scenv hpm rs1 rsf rs'
              (rv64d_types.Exception e) (xtval_exception_value e xv)
              (register_lookup (R_bitvector_64 PC) rsf)
              Lhs Hmsok Lstvec Lmie Lmdl Lmenv Lsatp Lpcfg Lpaddr Htlbok Hwf
              Hag with "Hrw Hro Hany Hopen Hrut").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ARM 3 -- [Step_Execute (Illegal_Instruction tt, ib)]: the same tower   *)
  (* at [E_Illegal_Instr], whose tval is the instruction bits.             *)
  (* ------------------------------------------------------------------- *)
  Lemma u_arm_illegal
      (t : ptree) (mm : PtBytes.pamap) (usatp : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (mcenv scenv : mword 32) (hpm : type_of_register mhpmcounter)
      (rs1 rsf : regstate) (ib : mword 32) :
    register_lookup hart_state rsf = HART_ACTIVE tt ->
    register_lookup cur_privilege rsf = User ->
    user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rsf) ->
    register_lookup (R_bool minstret_increment) rsf
      = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs1)
          (register_lookup (R_bitvector_64 minstretcfg) rs1)
          (register_lookup cur_privilege rs1) ->
    register_lookup (R_bitvector_64 stvec) rsf = uc_stvec C ->
    register_lookup (R_bitvector_64 mie) rsf = uc_mie C ->
    register_lookup (R_bitvector_64 mideleg) rsf = uc_mideleg C ->
    register_lookup (R_bitvector_64 menvcfg) rsf = MENVCFG_S ->
    register_lookup (R_bitvector_64 satp) rsf = usatp ->
    register_lookup pmpcfg_n rsf = pcfg ->
    register_lookup pmpaddr_n rsf = paddr ->
    u_exec_pins pt t rsf ->
    u_mem_wf pt t mm ->
    gen_cert -∗
    resv_any cpu_id -∗
    hreg_frame rsf u_Drw -∗
    hreg_frame_ro (u_Df (uc_dqc C)) rsf u_Dro -∗
    u_open C pt t mm usatp pcfg paddr mcenv scenv hpm -∗
    Rut pt -∗
    u_step_post C pt Rut rs1 (Step_Execute (Illegal_Instruction tt, ib)).
  Proof.
    intros Lhs Lpriv Hmsok Lmi Lstvec Lmie Lmdl Lmenv Lsatp Lpcfg Lpaddr
      Hpins Hwf.
    iIntros "Hcert Hany Hrw Hro Hopen Hrut".
    iApply (u_arm_fetch_failure t mm usatp pcfg paddr mcenv scenv hpm rs1 rsf
              (E_Illegal_Instr tt) (zero_extend' 64 ib) eq_refl
              Lhs Lpriv Hmsok Lmi Lstvec Lmie Lmdl Lmenv Lsatp Lpcfg Lpaddr
              Hpins Hwf with "Hcert Hany Hrw Hro Hopen Hrut").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ARM 4 -- [Step_Execute (Trap …)]: the tower entered ONE node lower,    *)
  (* at [exception_handler] itself (the step has already made               *)
  (* [handle_exception]'s two reads), so its sepc is the STEP's [pcx].      *)
  (* ------------------------------------------------------------------- *)
  Lemma u_arm_exec_trap
      (t : ptree) (mm : PtBytes.pamap) (usatp : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (mcenv scenv : mword 32) (hpm : type_of_register mhpmcounter)
      (rs1 rsf : regstate) (e : ExceptionType) (xv pcx : mword 64)
      (ib : mword 32) :
    user_exc e = true ->
    register_lookup hart_state rsf = HART_ACTIVE tt ->
    register_lookup cur_privilege rsf = User ->
    user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rsf) ->
    register_lookup (R_bool minstret_increment) rsf
      = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs1)
          (register_lookup (R_bitvector_64 minstretcfg) rs1)
          (register_lookup cur_privilege rs1) ->
    register_lookup (R_bitvector_64 stvec) rsf = uc_stvec C ->
    register_lookup (R_bitvector_64 mie) rsf = uc_mie C ->
    register_lookup (R_bitvector_64 mideleg) rsf = uc_mideleg C ->
    register_lookup (R_bitvector_64 menvcfg) rsf = MENVCFG_S ->
    register_lookup (R_bitvector_64 satp) rsf = usatp ->
    register_lookup pmpcfg_n rsf = pcfg ->
    register_lookup pmpaddr_n rsf = paddr ->
    u_exec_pins pt t rsf ->
    u_mem_wf pt t mm ->
    gen_cert -∗
    resv_any cpu_id -∗
    hreg_frame rsf u_Drw -∗
    hreg_frame_ro (u_Df (uc_dqc C)) rsf u_Dro -∗
    u_open C pt t mm usatp pcfg paddr mcenv scenv hpm -∗
    Rut pt -∗
    u_step_post C pt Rut rs1
      (Step_Execute (rv64d_types.Trap (User, make_sync_exception e xv, pcx), ib)).
  Proof.
    intros Hue Lhs Lpriv Hmsok Lmi Lstvec Lmie Lmdl Lmenv Lsatp Lpcfg Lpaddr
      Hpins Hwf.
    destruct Hpins as ((Hmisa & _ & _ & _ & _ & Helpne) & _ & _ & Htlbok).
    pose proof (elp_no_lp _ Helpne) as Lelp.
    assert (HmisaS : eq_vec (_get_Misa_S (register_lookup (R_bitvector_64 misa) rsf))
                       ('b"1") = true)
      by (rewrite Hmisa; vm_compute; reflexivity).
    iIntros "#Hcert Hany Hrw Hro Hopen Hrut".
    iDestruct (u_ro_elp_acc with "Hro") as "[#Help Hro]".
    rewrite Lelp.
    iDestruct (u_medeleg_pin with "Hopen Hro") as "(%Lmedl & Hopen & Hro)".
    assert (Hdel : bit_to_bool
                     (access_vec_dec (register_lookup (R_bitvector_64 medeleg) rsf)
                        (uint (exceptionType_bits_forwards e))) = true)
      by (rewrite Lmedl; exact (uc_del C e Hue)).
    rewrite /u_step_post.
    iExists (u_trap_rs rsf (rv64d_types.Exception e)
               (xtval_exception_value e xv) pcx (uc_stvec C)).
    iSplitR "Hany Hrw Hro Hopen Hrut".
    { iPureIntro. rewrite /u_land. split_and!;
        [ u_trap_peel; exact Lhs | u_trap_peel; exact Lmi | exact I ]. }
    iApply (swp_mono with "[Hopen Hrut] [Hany Hrw Hro]").
    2:{ iApply (swp_exec_trap_u (u_state rsf mm)
                  (rv64d_types.Exception e) (xtval_exception_value e xv) pcx
                  (register_lookup (R_bitvector_64 mstatus) rsf)
                  (register_lookup (R_bitvector_64 scause) rsf)
                  (uc_stvec C) (landing_pad_bits_backwards NO_LP_EXPECTED)
                  Lpriv eq_refl eq_refl Lstvec Lelp HmisaS (uc_tvd C)
                  Du_r Du_w u_Drw u_Dro (u_Df (uc_dqc C)) rsf e xv
                  eq_refl eq_refl Hdel
                  u_disj Du_r_sub Du_w_sub
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(intros r _; reflexivity) eq_refl
                  with "Hcert Hany Help Hrw Hro"). }
    iIntros (v) "Hpost".
    iDestruct "Hpost" as (rs') "(%Hag & Hrw & Hro & Hany)".
    iApply (u_arm_close t mm usatp pcfg paddr mcenv scenv hpm rs1 rsf rs'
              (rv64d_types.Exception e) (xtval_exception_value e xv) pcx
              Lhs Hmsok Lstvec Lmie Lmdl Lmenv Lsatp Lpcfg Lpaddr Htlbok Hwf
              Hag with "Hrw Hro Hany Hopen Hrut").
  Qed.

  (* ===================================================================== *)
  (* §6a  THE [swp] BRIDGE OVER THE PURE FETCH LAYER.                       *)
  (*                                                                        *)
  (* ONE lemma serves all FIVE pure fetch producers -- [u_fetch_pure] and    *)
  (* [u_fetch_fault_pure] for the 4-aligned arm, and [u_fetch_pure_2] /      *)
  (* [u_fetch_or_fault_pure_2_second] / [u_fetch_fault_pure_2_first] for the *)
  (* 2-aligned one -- because §14.4 gave all five the SAME five conjuncts.   *)
  (* That uniformity is exactly what the shape was chosen for.               *)
  (*                                                                        *)
  (* [u_landing_map] is what turns [swp_hmrun_of_exec]'s existential post    *)
  (* map into the composer's [mm']: at the reference state a submap with the *)
  (* full domain IS the map.                                                 *)
  (* ===================================================================== *)
  Lemma swp_fetch_of_pure (dq : dfrac) (t t' : ptree) (mm mm' : PtBytes.pamap)
      (rsf rsf' : regstate) (fr : FetchResult)
      (Pe : ExecutionResult -> mword 32 -> iProp Σ)
      (Pf : mword 64 -> ExceptionType -> iProp Σ)
      (Px : ext_fetch_addr_error -> iProp Σ) :
    exec (fetch tt) (u_state rsf mm) = Some (fr, u_state rsf' mm') ->
    goodmb Du_r Du_w (fetch tt) (u_state rsf mm) mm = true ->
    u_mem_ok pt t mm ->
    u_mem_step_ok pt t t' mm mm' ->
    gen_cert -∗ resv_any cpu_id -∗
    hreg_frame rsf u_Drw -∗ hreg_frame_ro (u_Df dq) rsf u_Dro -∗
    bytes_own mm -∗
    (∀ rs2 : regstate,
       ⌜reg_agree_on (u_Drw ∪ u_Dro) rs2 rsf'⌝ -∗
       hreg_frame rs2 u_Drw -∗ hreg_frame_ro (u_Df dq) rs2 u_Dro -∗
       bytes_own mm' -∗ resv_any cpu_id -∗
       run_fetch_post u_Drw u_Dro (u_Df dq) Pe Pf Px fr) -∗
    swp (fetch tt) (run_fetch_post u_Drw u_Dro (u_Df dq) Pe Pf Px).
  Proof.
    intros He Hg Hwf Hstep.
    iIntros "#Hcert Hany Hrw Hro Hown Hk".
    iApply (swp_mono with "[Hk] [Hany Hrw Hro Hown]").
    2:{ iApply (swp_hmrun_of_exec Du_r Du_w u_Drw u_Dro (u_Df dq) (fetch tt)
                  (u_state rsf mm) (u_state rsf' mm') fr rsf mm
                  u_disj Du_r_sub Du_w_sub
                  ltac:(intros r _; reflexivity) ltac:(reflexivity) Hg He
                  with "Hcert Hany Hrw Hro Hown"). }
    iIntros (v) "(-> & Hpost)".
    iDestruct "Hpost"
      as (rs2 mm2) "(%Hag & %Hsub & %Hdom & Hrw & Hro & Hown & Hany)".
    assert (Hmm2 : mm2 = mm')
      by exact (u_landing_map pt t t' mm mm2 (u_state rsf' mm') Hstep
                  Hsub Hdom).
    subst mm2.
    iApply ("Hk" $! rs2 with "[%] Hrw Hro Hown Hany"). exact Hag.
  Qed.

  (* ===================================================================== *)
  (* §6b  THE [swp] BRIDGE OVER THE EXECUTE HALF of [base_post]/[rvc_post]. *)
  (*                                                                        *)
  (* The [ExecuteAs] fork is a SECOND [swp] inside the FIRST execute's post  *)
  (* ([HartRunFull.run_exec_post]), not a side condition, so the redirect    *)
  (* arm runs [swp_hmrun_of_exec] twice -- and the redirect lands on the     *)
  (* state it started from, which is what lets the second run start from the *)
  (* frame the first handed back.                                            *)
  (* ===================================================================== *)
  Lemma swp_execute_of_pure (dq : dfrac) (t t' : ptree) (mm : PtBytes.pamap)
      (rsx : regstate) (instr : instruction) (r : ExecutionResult)
      (s_x : mstate) (ib : mword 32)
      (Pe : ExecutionResult -> mword 32 -> iProp Σ) :
    (exec (execute instr) (u_state rsx mm) = Some (r, s_x)
       /\ goodmb Du_r Du_w (execute instr) (u_state rsx mm) mm = true
     \/ (exists other : instruction,
           exec (execute instr) (u_state rsx mm)
             = Some (ExecuteAs other, u_state rsx mm)
           /\ goodmb Du_r Du_w (execute instr) (u_state rsx mm) mm = true
           /\ exec (execute other) (u_state rsx mm) = Some (r, s_x)
           /\ goodmb Du_r Du_w (execute other) (u_state rsx mm) mm = true)) ->
    (match r with ExecuteAs _ => False | _ => True end) ->
    u_mem_ok pt t mm ->
    u_mem_step_ok pt t t' mm s_x.(mem) ->
    gen_cert -∗ resv_any cpu_id -∗
    hreg_frame rsx u_Drw -∗ hreg_frame_ro (u_Df dq) rsx u_Dro -∗
    bytes_own mm -∗
    (∀ rs2 : regstate,
       ⌜reg_agree_on (u_Drw ∪ u_Dro) rs2 s_x.(sregs)⌝ -∗
       hreg_frame rs2 u_Drw -∗ hreg_frame_ro (u_Df dq) rs2 u_Dro -∗
       bytes_own s_x.(mem) -∗ resv_any cpu_id -∗
       Pe r ib) -∗
    swp (execute instr) (run_exec_post Pe ib).
  Proof.
    intros Hexe Hnr Hwf Hstep.
    iIntros "#Hcert Hany Hrw Hro Hown Hk".
    destruct Hexe as [(He & Hg) | (other & He1 & Hg1 & He2 & Hg2)].
    - (* DIRECT: one execute, and the result is not a redirect *)
      iApply (swp_mono with "[Hk] [Hany Hrw Hro Hown]").
      2:{ iApply (swp_hmrun_of_exec Du_r Du_w u_Drw u_Dro (u_Df dq)
                    (execute instr) (u_state rsx mm) s_x r rsx mm
                    u_disj Du_r_sub Du_w_sub
                    ltac:(intros q _; reflexivity) ltac:(reflexivity) Hg He
                    with "Hcert Hany Hrw Hro Hown"). }
      iIntros (v) "(-> & Hpost)".
      iDestruct "Hpost"
        as (rs2 mm2) "(%Hag & %Hsub & %Hdom & Hrw & Hro & Hown & Hany)".
      assert (Hmm2 : mm2 = s_x.(mem))
        by exact (u_landing_map pt t t' mm mm2 s_x Hstep Hsub Hdom).
      subst mm2.
      iApply (run_exec_post_direct Pe ib r Hnr).
      iApply ("Hk" $! rs2 with "[%] Hrw Hro Hown Hany"). exact Hag.
    - (* REDIRECT: the first execute answers [ExecuteAs other] AT THE SAME
         STATE, so the second starts from the frame the first handed back *)
      iApply (swp_mono with "[Hk] [Hany Hrw Hro Hown]").
      2:{ iApply (swp_hmrun_of_exec Du_r Du_w u_Drw u_Dro (u_Df dq)
                    (execute instr) (u_state rsx mm) (u_state rsx mm)
                    (ExecuteAs other) rsx mm
                    u_disj Du_r_sub Du_w_sub
                    ltac:(intros q _; reflexivity) ltac:(reflexivity)
                    Hg1 He1 with "Hcert Hany Hrw Hro Hown"). }
      iIntros (v) "(-> & Hpost)".
      iDestruct "Hpost"
        as (rs1 mm1) "(%Hag1 & %Hsub1 & %Hdom1 & Hrw & Hro & Hown & Hany)".
      assert (Hmm1 : mm1 = mm)
        by exact (u_landing_map pt t t mm mm1 (u_state rsx mm)
                    (u_mem_step_ok_refl pt t mm Hwf) Hsub1 Hdom1).
      subst mm1.
      iApply run_exec_post_redirect.
      iApply (swp_mono with "[Hk] [Hany Hrw Hro Hown]").
      2:{ iApply (swp_hmrun_of_exec Du_r Du_w u_Drw u_Dro (u_Df dq)
                    (execute other) (u_state rsx mm) s_x r rs1 mm
                    u_disj Du_r_sub Du_w_sub Hag1 ltac:(reflexivity)
                    Hg2 He2 with "Hcert Hany Hrw Hro Hown"). }
      iIntros (v) "(-> & Hpost)".
      iDestruct "Hpost"
        as (rs2 mm2) "(%Hag & %Hsub & %Hdom & Hrw & Hro & Hown & Hany)".
      assert (Hmm2 : mm2 = s_x.(mem))
        by exact (u_landing_map pt t t' mm mm2 s_x Hstep Hsub Hdom).
      subst mm2.
      (* NO [run_exec_post_direct] here: [run_exec_post_redirect] already
         stripped the wrapper, so the second execute's continuation is
         [fun e' => Pe e' ib] and the goal IS [Pe r ib]. *)
      iApply ("Hk" $! rs2 with "[%] Hrw Hro Hown Hany"). exact Hag.
  Qed.

  (* ===================================================================== *)
  (* §6c  TWO BOOKKEEPING MOVES the assembly needs.                          *)
  (* ===================================================================== *)

  (* [u_open] holds the bytes, but so does every memory-touching producer.   *)
  (* Take them out once and hand back a re-former at whatever tree/map the   *)
  (* step landed on: the node claims travel by [pt_claims_shape] (a step     *)
  (* preserves the SHAPE) and the [user_pt_inv] closer by                    *)
  (* [u_mem_step_trans].                                                     *)
  Lemma u_open_bytes (t : ptree) (mm : PtBytes.pamap) (usatp : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (mcenv scenv : mword 32) (hpm : type_of_register mhpmcounter) :
    u_open C pt t mm usatp pcfg paddr mcenv scenv hpm -∗
    bytes_own mm ∗
    (∀ (t' : ptree) (mm' : PtBytes.pamap),
       ⌜u_mem_step pt t t' mm mm'⌝ -∗ bytes_own mm' -∗
       u_open C pt t' mm' usatp pcfg paddr mcenv scenv hpm).
  Proof.
    rewrite /u_open.
    iIntros "(Hpmp & #Hmedl & #Hsenv & #Hmste & #Hsste & #Hmcen & #Hscen &
              #Hhpm & #Hclaims & Hbytes & Hclose)".
    iFrame "Hbytes".
    iIntros (t' mm') "%Hstep Hbytes".
    iDestruct (bi.equiv_entails_1_1 _ _ (pt_claims_shape 2 t t' (proj1 Hstep))
                 with "Hclaims") as "#Hclaims'".
    iFrame "Hpmp Hmedl Hsenv Hmste Hsste Hmcen Hscen Hhpm Hclaims' Hbytes".
    iIntros (t'' mm'' tlbvec'') "%Hstep' %Htlbok Hregs Hbytes'".
    iApply ("Hclose" $! t'' mm'' tlbvec'' with "[%] [%] Hregs Hbytes'");
      [ exact (u_mem_step_trans pt t t' t'' mm mm' mm'' Hstep Hstep')
      | exact Htlbok ].
  Qed.

  (* the ambient pin bundle, moved along a footprint agreement that may       *)
  (* disturb the TLB and the minstret flag.  [UserClassifyAsm.u_exec_pins_    *)
  (* only] wants a WHOLE-file [u_tlb_only]; what a landing hands back is      *)
  (* agreement on the FOOTPRINT only, which is all the bundle reads.          *)
  (* the two cells [u_Dfix] deliberately leaves out, as [register_beq]        *)
  (* equations -- what a per-register transport needs to peel a [nextPC]      *)
  (* write or to skip a TLB fill.                                             *)
  Lemma u_fix_ne_nPC (r : register) :
    r ∈ u_Dfix -> register_beq r (R_bitvector_64 nextPC) = false.
  Proof.
    intros Hr. destruct (register_beq r (R_bitvector_64 nextPC)) eqn:Hb;
      [| reflexivity].
    apply register_beq_true in Hb. subst r. exfalso. exact (u_fix_nPC Hr).
  Qed.

  Lemma u_fix_ne_tlb (r : register) :
    r ∈ u_Dfix -> register_beq r (tlb : register) = false.
  Proof.
    intros Hr. destruct (register_beq r (tlb : register)) eqn:Hb;
      [| reflexivity].
    apply register_beq_true in Hb. subst r. exfalso. exact (u_fix_tlb Hr).
  Qed.

  Lemma u_pins_move (t t' : ptree) (rs rs' : regstate) :
    (forall r : register, r ∈ u_Dfix ->
       register_beq r (R_bool minstret_increment) = false ->
       register_lookup r rs' = register_lookup r rs) ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') ->
    u_exec_pins pt t rs -> u_exec_pins pt t' rs'.
  Proof.
    intros T Htlbok' (Hhw & Hcfgp & Hpt & _).
    destruct Hhw as (Hmisa & Hsec & Hsenv & Hhtif & Hall & Help).
    destruct Hcfgp as (Hmst0 & Hsst0).
    destruct Hpt as ((usatp & Hsatpok & Hsatp) & HA & Hord & HX & HW & HR & Hcov).
    split_and!; [ | | | exact Htlbok' ].
    - split_and!;
        [ rewrite (T _ u_fix_misa eq_refl); exact Hmisa
        | rewrite (T _ u_fix_sec eq_refl); exact Hsec
        | rewrite (T _ u_fix_senv eq_refl); exact Hsenv
        | rewrite (T _ u_fix_htif eq_refl); exact Hhtif
        | rewrite (T _ u_fix_pma eq_refl); exact Hall
        | rewrite (T _ u_fix_elp eq_refl); exact Help ].
    - split_and!;
        [ rewrite (T _ u_fix_mste eq_refl); exact Hmst0
        | rewrite (T _ u_fix_sste eq_refl); exact Hsst0 ].
    - split_and!;
        [ exists usatp; split;
            [ exact Hsatpok
            | rewrite (T _ u_fix_satp eq_refl); exact Hsatp ]
        | rewrite (T _ u_fix_pcfg eq_refl); exact HA
        | rewrite (T _ u_fix_paddr eq_refl); exact Hord
        | rewrite (T _ u_fix_pcfg eq_refl); exact HX
        | rewrite (T _ u_fix_pcfg eq_refl); exact HW
        | rewrite (T _ u_fix_pcfg eq_refl); exact HR
        | rewrite (T _ u_fix_paddr eq_refl); exact Hcov ].
  Qed.

  (* [swp_run_hart_active_res] moved to [HartRunFull], beside
     [swp_run_hart_active_full]: the verified Umode engine is its third
     consumer, so it is generic machinery rather than tier glue. *)


  (* ===================================================================== *)
  (* §8  THE EXECUTE RESULT -> [u_step_post], once for all four shapes.      *)
  (* [UserClassify.u_result_ok] is what the totalities deliver, and it is    *)
  (* exactly a four-way case: the two RETIRING shapes go to [u_psi_active]   *)
  (* (one builder, per §14.2's tag), the two TRAPPING ones to the arms.      *)
  (* ===================================================================== *)
  Lemma u_arm_of_result (t : ptree) (mm : PtBytes.pamap) (usatp : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (mcenv scenv : mword 32) (hpm : type_of_register mhpmcounter)
      (rs1 rsX : regstate) (r : ExecutionResult) (ib : mword 32) :
    u_result_ok r ->
    register_lookup hart_state rsX = HART_ACTIVE tt ->
    register_lookup cur_privilege rsX = User ->
    user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rsX) ->
    register_lookup (R_bool minstret_increment) rsX
      = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs1)
          (register_lookup (R_bitvector_64 minstretcfg) rs1)
          (register_lookup cur_privilege rs1) ->
    register_lookup (R_bitvector_64 stvec) rsX = uc_stvec C ->
    register_lookup (R_bitvector_64 mie) rsX = uc_mie C ->
    register_lookup (R_bitvector_64 mideleg) rsX = uc_mideleg C ->
    register_lookup (R_bitvector_64 menvcfg) rsX = MENVCFG_S ->
    register_lookup (R_bitvector_64 satp) rsX = usatp ->
    register_lookup pmpcfg_n rsX = pcfg ->
    register_lookup pmpaddr_n rsX = paddr ->
    u_exec_pins pt t rsX ->
    u_mem_wf pt t mm ->
    gen_cert -∗ resv_any cpu_id -∗
    hreg_frame rsX u_Drw -∗ hreg_frame_ro (u_Df (uc_dqc C)) rsX u_Dro -∗
    u_open C pt t mm usatp pcfg paddr mcenv scenv hpm -∗
    Rut pt -∗
    u_step_post C pt Rut rs1 (Step_Execute (r, ib)).
  Proof.
    intros Hrok Lhs Lcp Hmsok Lmi Lstvec Lmie Lmdl Lmenv Lsatp Lpcfg Lpaddr
      Hpins Hwf.
    pose proof Hpins as (_ & _ & _ & Htlbok).
    iIntros "#Hcert Hany Hrw Hro Hopen Hrut".
    destruct Hrok as [-> | [(e & xv & pcx & -> & Hue) | [-> | (wr & -> & Hwr)]]].
    - (* RETIRE *)
      rewrite /u_step_post. iExists rsX.
      iSplitR "Hany Hrw Hro Hopen Hrut".
      { iPureIntro. rewrite /u_land.
        split_and!; [ exact Lhs | exact Lmi | exact I ]. }
      rewrite /u_arm_res. iFrame "Hrw Hro".
      iApply (u_psi_active t mm usatp (register_lookup tlb rsX) pcfg paddr
                mcenv scenv hpm rs1 rsX Lhs Lcp Hmsok Lstvec Lmie Lmdl Lmenv
                Lsatp Lpcfg Lpaddr eq_refl Htlbok Hwf with "Hany Hopen Hrut").
    - (* DELEGATED USER TRAP *)
      iApply (u_arm_exec_trap t mm usatp pcfg paddr mcenv scenv hpm rs1 rsX
                e xv pcx ib Hue Lhs Lcp Hmsok Lmi Lstvec Lmie Lmdl Lmenv
                Lsatp Lpcfg Lpaddr Hpins Hwf
                with "Hcert Hany Hrw Hro Hopen Hrut").
    - (* ILLEGAL *)
      iApply (u_arm_illegal t mm usatp pcfg paddr mcenv scenv hpm rs1 rsX ib
                Lhs Lcp Hmsok Lmi Lstvec Lmie Lmdl Lmenv Lsatp Lpcfg Lpaddr
                Hpins Hwf with "Hcert Hany Hrw Hro Hopen Hrut").
    - (* ENTER WAIT (WRS.STO / WRS.NTO) *)
      rewrite /u_step_post. iExists rsX.
      iSplitR "Hany Hrw Hro Hopen Hrut".
      { iPureIntro. rewrite /u_land.
        split_and!; [ exact Lhs | exact Lmi | exact Hwr | exact Lcp ]. }
      iSplitR.
      { iPureIntro. destruct Hwr as [-> | ->]; vm_compute; reflexivity. }
      rewrite /u_arm_res. iFrame "Hrw Hro".
      iApply (u_psi_active t mm usatp (register_lookup tlb rsX) pcfg paddr
                mcenv scenv hpm rs1 rsX Lhs Lcp Hmsok Lstvec Lmie Lmdl Lmenv
                Lsatp Lpcfg Lpaddr eq_refl Htlbok Hwf with "Hany Hopen Hrut").
  Qed.

  (* ===================================================================== *)
  (* §9  THE FETCH OBLIGATION, once for all six producers.                  *)
  (*                                                                        *)
  (* Every one of the six delivers the SAME five conjuncts (§14.6) plus a    *)
  (* classification of the [FetchResult]; [u_fr_ok] is that classification,  *)
  (* carrying the 2-alignment on the two RETIRING shapes because that is     *)
  (* where [post_fetch_cfg] needs it (an ODD pc has no such fact and needs   *)
  (* none -- it always lands on [F_Error]).                                  *)
  (* ===================================================================== *)
  Definition u_fr_ok (va : mword 64) (fr : FetchResult) : Prop :=
    (((exists h : mword 16, fr = F_RVC h) \/ (exists w : mword 32, fr = F_Base w))
       /\ is_aligned_vaddr (Virtaddr va) 2 = true)
    \/ (exists (ex : ExceptionType) (xv : mword 64),
          fr = F_Error (ex, xv) /\ user_exc ex = true).

  Lemma u_swp_fetch (t t' : ptree) (mm mm' : PtBytes.pamap) (usatp : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (mcenv scenv : mword 32) (hpm : type_of_register mhpmcounter)
      (rs1 rsA rsf' : regstate) (fr : FetchResult) (va : mword 64) :
    (forall (v : mword 64) (b : bool), base_exec_total_u pt v b) ->
    (forall (v : mword 64) (b : bool), rvc_exec_total_u pt v b) ->
    register_lookup hart_state rsA = HART_ACTIVE tt ->
    register_lookup cur_privilege rsA = User ->
    user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rsA) ->
    register_lookup (R_bool minstret_increment) rsA
      = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs1)
          (register_lookup (R_bitvector_64 minstretcfg) rs1)
          (register_lookup cur_privilege rs1) ->
    register_lookup (R_bitvector_64 PC) rsA = va ->
    register_lookup (R_bitvector_64 stvec) rsA = uc_stvec C ->
    register_lookup (R_bitvector_64 mie) rsA = uc_mie C ->
    register_lookup (R_bitvector_64 mideleg) rsA = uc_mideleg C ->
    register_lookup (R_bitvector_64 menvcfg) rsA = MENVCFG_S ->
    register_lookup (R_bitvector_64 satp) rsA = usatp ->
    register_lookup pmpcfg_n rsA = pcfg ->
    register_lookup pmpaddr_n rsA = paddr ->
    u_exec_pins pt t rsA ->
    u_mem_wf pt t mm ->
    exec (fetch tt) (u_state rsA mm) = Some (fr, u_state rsf' mm') ->
    goodmb Du_r Du_w (fetch tt) (u_state rsA mm) mm = true ->
    u_fr_ok va fr ->
    u_tlb_only rsA rsf' ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf') ->
    u_mem_step pt t t' mm mm' ->
    gen_cert -∗ resv_any cpu_id -∗
    hreg_frame rsA u_Drw -∗ hreg_frame_ro (u_Df (uc_dqc C)) rsA u_Dro -∗
    bytes_own mm -∗
    (∀ (t'' : ptree) (mm'' : PtBytes.pamap),
       ⌜u_mem_step pt t t'' mm mm''⌝ -∗ bytes_own mm'' -∗
       u_open C pt t'' mm'' usatp pcfg paddr mcenv scenv hpm) -∗
    Rut pt -∗
    swp (fetch tt)
      (run_fetch_post u_Drw u_Dro (u_Df (uc_dqc C))
         (fun (r : ExecutionResult) (ib : mword 32) =>
            u_step_post C pt Rut rs1 (Step_Execute (r, ib)))
         (fun (xv : mword 64) (e : ExceptionType) =>
            u_step_post C pt Rut rs1 (Step_Fetch_Failure (Virtaddr xv, e)))
         (fun _ : ext_fetch_addr_error => False)).
  Proof.
    intros Hbase Hrvc Lhs Lcp Hmsok Lmi Lpc Lstvec Lmie Lmdl Lmenv Lsatp
      Lpcfg Lpaddr Hpins Hwf Hex Hg Hfrok Htr Htlbok' Hstep.
    iIntros "#Hcert Hany Hrw Hro Hbytes Hoback Hrut".
    iApply (swp_fetch_of_pure (uc_dqc C) t t' mm mm' rsA rsf' fr _ _ _
              Hex Hg (u_mem_wf_ok pt t mm Hwf)
              (u_mem_step_ok_of pt t t' mm mm' Hwf Hstep)
              with "Hcert Hany Hrw Hro Hbytes").
    iIntros (rsF) "%Hag Hrw Hro Hbytes Hany".
    (* the landing file agrees with [rsA] off the TLB, so every pin moves *)
    assert (TF : forall q : register, q ∈ u_Dfix ->
              register_lookup q rsF = register_lookup q rsA).
    { intros q Hq.
      rewrite (Hag q (u_Dfix_sub q Hq)). exact (Htr q (u_fix_ne_tlb q Hq)). }
    assert (LtlbF : register_lookup tlb rsF = register_lookup tlb rsf')
      by exact (Hag _ u_in_tlb).
    assert (HpinsF : u_exec_pins pt t' rsF).
    { apply (u_pins_move t t' rsA rsF);
        [ intros q Hq _; exact (TF q Hq)
        | rewrite LtlbF; exact Htlbok'
        | exact Hpins ]. }
    assert (HwfF : u_mem_wf pt t' mm')
      by exact (u_mem_step_wf pt t t' mm mm' Hwf Hstep).
    assert (LhsF : register_lookup hart_state rsF = HART_ACTIVE tt)
      by (rewrite (TF _ u_fix_hart); exact Lhs).
    assert (LcpF : register_lookup cur_privilege rsF = User)
      by (rewrite (TF _ u_fix_priv); exact Lcp).
    assert (HmsokF : user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rsF))
      by (rewrite (TF _ u_fix_mst); exact Hmsok).
    assert (LmiF : register_lookup (R_bool minstret_increment) rsF
                   = minstret_inc_flag
                       (register_lookup (R_bitvector_32 mcountinhibit) rs1)
                       (register_lookup (R_bitvector_64 minstretcfg) rs1)
                       (register_lookup cur_privilege rs1))
      by (rewrite (TF _ u_fix_mi); exact Lmi).
    assert (LpcF : register_lookup (R_bitvector_64 PC) rsF = va)
      by (rewrite (TF _ u_fix_PC); exact Lpc).
    assert (LstvecF : register_lookup (R_bitvector_64 stvec) rsF = uc_stvec C)
      by (rewrite (TF _ u_fix_stvec); exact Lstvec).
    assert (LmieF : register_lookup (R_bitvector_64 mie) rsF = uc_mie C)
      by (rewrite (TF _ u_fix_mie); exact Lmie).
    assert (LmdlF : register_lookup (R_bitvector_64 mideleg) rsF = uc_mideleg C)
      by (rewrite (TF _ u_fix_mdl); exact Lmdl).
    assert (LmenvF : register_lookup (R_bitvector_64 menvcfg) rsF = MENVCFG_S)
      by (rewrite (TF _ u_fix_menv); exact Lmenv).
    assert (LsatpF : register_lookup (R_bitvector_64 satp) rsF = usatp)
      by (rewrite (TF _ u_fix_satp); exact Lsatp).
    assert (LpcfgF : register_lookup pmpcfg_n rsF = pcfg)
      by (rewrite (TF _ u_fix_pcfg); exact Lpcfg).
    assert (LpaddrF : register_lookup pmpaddr_n rsF = paddr)
      by (rewrite (TF _ u_fix_paddr); exact Lpaddr).
    pose proof HpinsF as (HhwF & _ & _ & _).
    destruct HhwF as (HmisaF & _ & _ & _ & _ & HelpF).
    destruct Hfrok as [ (Hshape & Hal2) | (ex & xv & -> & Hue) ].
    2:{ (* ---- THE FETCH FAULTED ---- *)
      rewrite /run_fetch_post.
      iDestruct ("Hoback" $! t' mm' with "[%] Hbytes") as "Hopen";
        [ exact Hstep |].
      iApply (u_arm_fetch_failure t' mm' usatp pcfg paddr mcenv scenv hpm
                rs1 rsF ex xv Hue LhsF LcpF HmsokF LmiF LstvecF LmieF LmdlF
                LmenvF LsatpF LpcfgF LpaddrF HpinsF HwfF
                with "Hcert Hany Hrw Hro Hopen Hrut"). }
    (* ---- THE FETCH RETIRED: the config the totalities assume ---- *)
    assert (HcfgF : post_fetch_cfg (u_state rsF mm') va
                      (register_lookup (R_bool minstret_increment) rsF)).
    { rewrite /post_fetch_cfg. split_and!;
        [ exact LpcF | exact LcpF | exact HmsokF | exact LmenvF | exact Hal2
        | reflexivity ]. }
    destruct Hshape as [(h & ->) | (w & ->)].
    - (* ---- F_RVC ---- *)
      rewrite /run_fetch_post /run_fetch_rvc.
      destruct (Hrvc va (register_lookup (R_bool minstret_increment) rsF)
                  h rsF t' mm' HcfgF HpinsF HwfF)
        as (instr & r & s_x & t'' & Hdec & Hhv & Hzca & Hexe & Hrok & Hnr &
            Hfix & Htlbok'' & Hstep'').
      iExists rsF, instr, va, 8%nat, 4%nat.
      iSplitR; [ by iPureIntro |].
      iSplitR; [ by iPureIntro |].
      iSplitR.
      { iPureIntro.
        exact (hfrun_lpad (u_Drw ∪ u_Dro) u_Drw rsF u_in_elp HelpF). }
      iSplitR.
      { iPureIntro.
        apply (hfrun_cE_Zca (u_Drw ∪ u_Dro) u_Drw rsF u_in_misa).
        rewrite HmisaF. vm_compute; reflexivity. }
      iFrame "Hrw Hro".
      iIntros "Hrw Hro".
      iApply (swp_execute_of_pure (uc_dqc C) t' t'' mm'
                (register_set nextPC (add_vec_int va 2) rsF) instr r s_x
                (zero_extend' 32 h) _ Hexe Hnr (u_mem_wf_ok pt t' mm' HwfF)
                (u_mem_step_ok_of pt t' t'' mm' s_x.(mem) HwfF Hstep'')
                with "Hcert Hany Hrw Hro Hbytes").
      iIntros (rsX) "%Hag2 Hrw Hro Hbytes Hany".
      assert (TX : forall q : register, q ∈ u_Dfix ->
                register_lookup q rsX = register_lookup q rsF).
      { intros q Hq. rewrite (Hag2 q (u_Dfix_sub q Hq)) (Hfix q Hq).
        exact (irrelevant_register_set q (R_bitvector_64 nextPC) _ _
                 (u_fix_ne_nPC q Hq)). }
      assert (HpinsX : u_exec_pins pt t'' rsX).
      { apply (u_pins_move t' t'' rsF rsX);
          [ intros q Hq _; exact (TX q Hq)
          | rewrite (Hag2 _ u_in_tlb); exact Htlbok''
          | exact HpinsF ]. }
      iDestruct ("Hoback" $! t'' s_x.(mem) with "[%] Hbytes") as "Hopen".
      { exact (u_mem_step_trans pt t t' t'' mm mm' s_x.(mem) Hstep Hstep''). }
      iApply (u_arm_of_result t'' s_x.(mem) usatp pcfg paddr mcenv scenv hpm
                rs1 rsX r (zero_extend' 32 h) Hrok
                ltac:(rewrite (TX _ u_fix_hart); exact LhsF)
                ltac:(rewrite (TX _ u_fix_priv); exact LcpF)
                ltac:(rewrite (TX _ u_fix_mst); exact HmsokF)
                ltac:(rewrite (TX _ u_fix_mi); exact LmiF)
                ltac:(rewrite (TX _ u_fix_stvec); exact LstvecF)
                ltac:(rewrite (TX _ u_fix_mie); exact LmieF)
                ltac:(rewrite (TX _ u_fix_mdl); exact LmdlF)
                ltac:(rewrite (TX _ u_fix_menv); exact LmenvF)
                ltac:(rewrite (TX _ u_fix_satp); exact LsatpF)
                ltac:(rewrite (TX _ u_fix_pcfg); exact LpcfgF)
                ltac:(rewrite (TX _ u_fix_paddr); exact LpaddrF)
                HpinsX
                (u_mem_step_wf pt t' t'' mm' s_x.(mem) HwfF Hstep'')
                with "Hcert Hany Hrw Hro Hopen Hrut").
    - (* ---- F_Base ---- *)
      rewrite /run_fetch_post /run_fetch_base.
      destruct (Hbase va (register_lookup (R_bool minstret_increment) rsF)
                  w rsF t' mm' HcfgF HpinsF HwfF)
        as (instr & r & s_x & t'' & Hdec & Hhv & Hlpi & Hexe & Hrok & Hnr &
            Hfix & Htlbok'' & Hstep'').
      iExists rsF, instr, va, 8%nat.
      iSplitR; [ by iPureIntro |].
      iSplitR; [ by iPureIntro |].
      iSplitR.
      { iPureIntro.
        exact (hfrun_lpad (u_Drw ∪ u_Dro) u_Drw rsF u_in_elp HelpF). }
      iFrame "Hrw Hro".
      iIntros "Hrw Hro".
      iApply (swp_execute_of_pure (uc_dqc C) t' t'' mm'
                (register_set nextPC (add_vec_int va 4) rsF) instr r s_x
                (zero_extend' 32 w) _ Hexe Hnr (u_mem_wf_ok pt t' mm' HwfF)
                (u_mem_step_ok_of pt t' t'' mm' s_x.(mem) HwfF Hstep'')
                with "Hcert Hany Hrw Hro Hbytes").
      iIntros (rsX) "%Hag2 Hrw Hro Hbytes Hany".
      assert (TX : forall q : register, q ∈ u_Dfix ->
                register_lookup q rsX = register_lookup q rsF).
      { intros q Hq. rewrite (Hag2 q (u_Dfix_sub q Hq)) (Hfix q Hq).
        exact (irrelevant_register_set q (R_bitvector_64 nextPC) _ _
                 (u_fix_ne_nPC q Hq)). }
      assert (HpinsX : u_exec_pins pt t'' rsX).
      { apply (u_pins_move t' t'' rsF rsX);
          [ intros q Hq _; exact (TX q Hq)
          | rewrite (Hag2 _ u_in_tlb); exact Htlbok''
          | exact HpinsF ]. }
      iDestruct ("Hoback" $! t'' s_x.(mem) with "[%] Hbytes") as "Hopen".
      { exact (u_mem_step_trans pt t t' t'' mm mm' s_x.(mem) Hstep Hstep''). }
      iApply (u_arm_of_result t'' s_x.(mem) usatp pcfg paddr mcenv scenv hpm
                rs1 rsX r (zero_extend' 32 w) Hrok
                ltac:(rewrite (TX _ u_fix_hart); exact LhsF)
                ltac:(rewrite (TX _ u_fix_priv); exact LcpF)
                ltac:(rewrite (TX _ u_fix_mst); exact HmsokF)
                ltac:(rewrite (TX _ u_fix_mi); exact LmiF)
                ltac:(rewrite (TX _ u_fix_stvec); exact LstvecF)
                ltac:(rewrite (TX _ u_fix_mie); exact LmieF)
                ltac:(rewrite (TX _ u_fix_mdl); exact LmdlF)
                ltac:(rewrite (TX _ u_fix_menv); exact LmenvF)
                ltac:(rewrite (TX _ u_fix_satp); exact LsatpF)
                ltac:(rewrite (TX _ u_fix_pcfg); exact LpcfgF)
                ltac:(rewrite (TX _ u_fix_paddr); exact LpaddrF)
                HpinsX
                (u_mem_step_wf pt t' t'' mm' s_x.(mem) HwfF Hstep'')
                with "Hcert Hany Hrw Hro Hopen Hrut").
  Qed.

  (* ===================================================================== *)
  (* §10  [active_class], from [hw_config] and the two PURE totalities.      *)
  (*                                                                        *)
  (* The [va] CASE TREE is the pre-port [active_obligations]' -- split on    *)
  (* bit 0, then on 4-alignment, then classify with [fetch_classify] -- with *)
  (* the six PURE producers where the six Iris ones used to be, and ONE      *)
  (* [u_swp_fetch] behind all of them.                                       *)
  (* ===================================================================== *)
  Lemma active_class_intro (Ei : coPset) :
    (forall (va : mword 64) (mi : bool), base_exec_total_u pt va mi) ->
    (forall (va : mword 64) (mi : bool), rvc_exec_total_u pt va mi) ->
    hw_config -∗ active_class C pt Rut Ei.
  Proof.
    intros Hbase Hrvc.
    iIntros "#Hhw". rewrite /active_class. iModIntro.
    iIntros (rs1 rsA t mm usatp pcfg paddr mcenv scenv hpm).
    iIntros "%Lhs1 %Lcp1 %Hmsok1 %Lpcnpc %Lstvec1 %Lmie1 %Lmdl1 %Lmenv1
             %Lsatp1 %Lpcfg1 %Lpaddr1 %Hpins1 %Hwf %Hag Hfrag Hrw Hro Hopen Hrut".
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & _ & _ & #Hcert & _)".
    pose proof Hpins1 as (_ & _ & _ & Htlbok1).
    pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & Hacc & _ & _).
    (* ---- every pin moves from [rs1] to [rsA]: the prelude writes ONE cell *)
    assert (TA : forall q : register, q ∈ u_Dfix ->
              register_beq q (R_bool minstret_increment) = false ->
              register_lookup q rsA = register_lookup q rs1).
    { intros q Hq Hne. rewrite <- (Hag q (u_Dfix_sub q Hq)).
      exact (wrap_pre_other q rs1 Hne). }
    assert (LmiA : register_lookup (R_bool minstret_increment) rsA
                   = minstret_inc_flag
                       (register_lookup (R_bitvector_32 mcountinhibit) rs1)
                       (register_lookup (R_bitvector_64 minstretcfg) rs1)
                       (register_lookup cur_privilege rs1)).
    { rewrite <- (Hag _ u_in_mi). apply wrap_pre_mi. }
    assert (LtlbA : register_lookup tlb rsA = register_lookup tlb rs1).
    { rewrite <- (Hag _ u_in_tlb). exact (wrap_pre_other tlb rs1 eq_refl). }
    assert (LhsA : register_lookup hart_state rsA = HART_ACTIVE tt)
      by (rewrite (TA _ u_fix_hart eq_refl); exact Lhs1).
    assert (LcpA : register_lookup cur_privilege rsA = User)
      by (rewrite (TA _ u_fix_priv eq_refl); exact Lcp1).
    assert (HmsokA : user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rsA))
      by (rewrite (TA _ u_fix_mst eq_refl); exact Hmsok1).
    assert (LstvecA : register_lookup (R_bitvector_64 stvec) rsA = uc_stvec C)
      by (rewrite (TA _ u_fix_stvec eq_refl); exact Lstvec1).
    assert (LmieA : register_lookup (R_bitvector_64 mie) rsA = uc_mie C)
      by (rewrite (TA _ u_fix_mie eq_refl); exact Lmie1).
    assert (LmdlA : register_lookup (R_bitvector_64 mideleg) rsA = uc_mideleg C)
      by (rewrite (TA _ u_fix_mdl eq_refl); exact Lmdl1).
    assert (LmenvA : register_lookup (R_bitvector_64 menvcfg) rsA = MENVCFG_S)
      by (rewrite (TA _ u_fix_menv eq_refl); exact Lmenv1).
    assert (LsatpA : register_lookup (R_bitvector_64 satp) rsA = usatp)
      by (rewrite (TA _ u_fix_satp eq_refl); exact Lsatp1).
    assert (LpcfgA : register_lookup pmpcfg_n rsA = pcfg)
      by (rewrite (TA _ u_fix_pcfg eq_refl); exact Lpcfg1).
    assert (LpaddrA : register_lookup pmpaddr_n rsA = paddr)
      by (rewrite (TA _ u_fix_paddr eq_refl); exact Lpaddr1).
    assert (HpinsA : u_exec_pins pt t rsA).
    { apply (u_pins_move t t rs1 rsA);
        [ intros q Hq Hne; exact (TA q Hq Hne)
        | rewrite LtlbA; exact Htlbok1
        | exact Hpins1 ]. }
    pose proof HpinsA as (HhwA & HcfgpA & _ & _).
    assert (HagdA : agree_on D_u (u_state rsA mm) dstateU)
      by exact (u_agree_decode rsA mm LcpA LmenvA HhwA HcfgpA).
    set (va := register_lookup (R_bitvector_64 PC) rsA).
    assert (LpcA : register_lookup (R_bitvector_64 PC) rsA = va) by reflexivity.
    (* ---- ONE cycle, with the tier's own resources threaded past the       *)
    (* dispatch; [Pe] / [Pf] / [Qi] ARE [u_step_post]'s arms, so the         *)
    (* [swp_mono] wand carries nothing.                                      *)
    iApply (swp_mono with "[] [-]").
    2: iApply (swp_run_hart_active_res u_Drw u_Dro (u_Df (uc_dqc C)) rsA User
              (resv_frag cpu_id None ∗
               u_open C pt t mm usatp pcfg paddr mcenv scenv hpm ∗ Rut pt)%I
              (fun (ii : InterruptType) (pr : Privilege) =>
                 u_step_post C pt Rut rs1 (Step_Pending_Interrupt (ii, pr)))
              (fun (r : ExecutionResult) (ib : mword 32) =>
                 u_step_post C pt Rut rs1 (Step_Execute (r, ib)))
              (fun (xv : mword 64) (e : ExceptionType) =>
                 u_step_post C pt Rut rs1 (Step_Fetch_Failure (Virtaddr xv, e)))
              (fun _ : ext_fetch_addr_error => False%I)
              u_disj u_in_priv u_in_PC u_w_nPC LcpA
              with "Hcert Hrw Hro [Hfrag Hopen Hrut] [] []").
    - (* the outcome map: [Qi] / [Pe] / [Pf] ARE [u_step_post]'s arms, and
         the two shapes the tier rules out are [False] on both sides *)
      iIntros (st) "H". destruct st as [ p | x | p | p | wq ];
        [ destruct p as [ii pr] | | destruct p as [[xv] e]
        | destruct p as [r ib] | ];
        [ iApply "H" | iExFalso; iExact "H" | iApply "H" | iApply "H"
        | iExFalso; iExact "H" ].
    - (* the threaded bundle *)
      iFrame "Hfrag Hopen Hrut".
    - (* ---- THE DISPATCH ---- *)
      iIntros "HWd Hrw Hro".
      iApply (swp_mono with "[HWd] [Hrw Hro]").
      2:{ iApply (swp_dispatchInterrupt_U u_Drw u_Dro (u_Df (uc_dqc C)) rsA
                    dstateU D_u (register_lookup mip rsA) (uc_mie C)
                    (uc_mideleg C) u_disj u_in_ip u_in_mie u_in_mdl
                    eq_refl LmieA LmdlA (uc_mm C) u_D_u_sub HagdA
                    (s0_ext_S dstateU ltac:(vm_compute; reflexivity))
                    ltac:(reflexivity)
                    with "Hcert Hrw Hro"). }
      iIntros (o). iDestruct 1 as (meip seip) "(%Hd & Hrw & Hro)".
      destruct o as [[ii pr] |].
      + assert (Hsup : pr = Supervisor).
        { rewrite <- u_dispatch_of_pending in Hd. unfold u_dispatch in Hd.
          destruct (neq_vec (s_pending (register_lookup mip rsA) meip seip
                               (uc_mie C) (uc_mideleg C)) (zeros' 64));
            [| discriminate Hd].
          destruct (findPendingInterrupt
                      (s_pending (register_lookup mip rsA) meip seip
                         (uc_mie C) (uc_mideleg C)));
            [| discriminate Hd].
          congruence. }
        subst pr.
        iDestruct "HWd" as "(Hfrag & Hopen & Hrut)".
        iApply (u_arm_pending_interrupt t mm usatp pcfg paddr mcenv scenv hpm
                  rs1 rsA ii LhsA LcpA HmsokA LmiA LstvecA LmieA LmdlA LmenvA
                  LsatpA LpcfgA LpaddrA HpinsA Hwf
                  with "Hcert Hfrag Hrw Hro Hopen Hrut").
      + iFrame.
    - (* ---- THE FETCH: the [va] case tree ---- *)
      iIntros "HWd Hrw Hro".
      iDestruct "HWd" as "(Hfrag & Hopen & Hrut)".
      iDestruct (u_open_bytes with "Hopen") as "[Hbytes Hoback]".
      iDestruct (resv_any_intro cpu_id None with "Hfrag") as "Hany".
      destruct (neq_vec (access_vec_dec va 0) ('b"0")) eqn:Hb0.
      + (* ---- ODD pc: address-align fault, nothing translates ---- *)
        destruct (u_fetch_align_fault_pure pt t mm rsA va LpcA Hb0 HpinsA Hwf)
          as (Hex & Hg & Htlbok' & Hstep).
        assert (Hfrok : u_fr_ok va (F_Error (E_Fetch_Addr_Align tt, va))).
        { right. exists (E_Fetch_Addr_Align tt), va.
          split; [ reflexivity | vm_compute; reflexivity ]. }
        iApply (u_swp_fetch t t mm mm usatp pcfg paddr mcenv scenv hpm
                  rs1 rsA rsA (F_Error (E_Fetch_Addr_Align tt, va)) va
                  Hbase Hrvc LhsA LcpA HmsokA LmiA LpcA LstvecA LmieA LmdlA
                  LmenvA LsatpA LpcfgA LpaddrA HpinsA Hwf Hex Hg Hfrok
                  (u_tlb_only_refl rsA) Htlbok' Hstep
                  with "Hcert Hany Hrw Hro Hbytes Hoback Hrut").
      + (* ---- EVEN pc ---- *)
        assert (Hal2 : is_aligned_vaddr (Virtaddr va) 2 = true)
          by (apply align2_of_bit0; exact Hb0).
        assert (HcfgA : post_fetch_cfg (u_state rsA mm) va
                          (register_lookup (R_bool minstret_increment) rsA)).
        { rewrite /post_fetch_cfg. split_and!;
            [ exact LpcA | exact LcpA | exact HmsokA | exact LmenvA
            | exact Hal2 | reflexivity ]. }
        destruct (is_aligned_vaddr (Virtaddr va) 4) eqn:Hal4.
        * (* ---- 4-ALIGNED ---- *)
          destruct (fetch_classify va Hacc)
            as [(w & Hum & Hok & Hcanon) | Hfault].
          -- (* fetchable *)
             assert (Hwin4 : forall j : nat, (j < 4)%nat ->
                       is_Some (mm !! RiscvModelBytes.pa_add (CommonWalk.u_walk_pa w va) j))
               by (intros j Hj;
                   exact (u_fetch_win_in pt t mm 4 w va ltac:(lia)
                            (Z.divide_factor_l 4 1024) Hwf Hum Hal4 j
                            ltac:(lia))).
             destruct (u_fetch_pure pt t mm rsA w va
                         (register_lookup (R_bool minstret_increment) rsA)
                         Hum Hok Hal4 Hcanon HcfgA HpinsA
                         (u_mem_wf_ok pt t mm Hwf) Hwin4)
               as (iw & rsf' & mm' & t' & Hex & Hg & Hfile & Htlbok' & Hstepk).
             assert (Hstep : u_mem_step pt t t' mm mm')
               by exact (u_mem_step_of_ok pt t t' mm mm' Hwf Hstepk).
             lazymatch type of Hex with
             | exec _ _ = Some (?fr, _) =>
                 assert (Hfrok : u_fr_ok va fr);
                 [ left; split;
                   [ lazymatch goal with
                     | |- context[if ?b then _ else _] => destruct b
                     end; [ left | right ]; eexists; reflexivity
                   | exact Hal2 ]
                 | ]
             end.
             iApply (u_swp_fetch t t' mm mm' usatp pcfg paddr mcenv scenv hpm
                       rs1 rsA rsf' _ va
                       Hbase Hrvc LhsA LcpA HmsokA LmiA LpcA LstvecA LmieA
                       LmdlA LmenvA LsatpA LpcfgA LpaddrA HpinsA Hwf Hex Hg
                       Hfrok (u_tlb_only_land rsA rsf' Hfile) Htlbok' Hstep
                       with "Hcert Hany Hrw Hro Hbytes Hoback Hrut").
          -- (* faults *)
             destruct (u_fetch_fault_pure pt t mm rsA va
                         (register_lookup (R_bool minstret_increment) rsA)
                         Hfault Hal4 HcfgA HpinsA (u_mem_wf_ok pt t mm Hwf))
               as (Hex & Hg & Htlbok' & Hstepk).
             assert (Hstep : u_mem_step pt t t mm mm)
               by exact (u_mem_step_of_ok pt t t mm mm Hwf Hstepk).
             assert (Hfrok : u_fr_ok va (F_Error (E_Fetch_Page_Fault tt, va))).
             { right. exists (E_Fetch_Page_Fault tt), va.
               split; [ reflexivity | vm_compute; reflexivity ]. }
             iApply (u_swp_fetch t t mm mm usatp pcfg paddr mcenv scenv hpm
                       rs1 rsA rsA (F_Error (E_Fetch_Page_Fault tt, va)) va
                       Hbase Hrvc LhsA LcpA HmsokA LmiA LpcA LstvecA LmieA
                       LmdlA LmenvA LsatpA LpcfgA LpaddrA HpinsA Hwf Hex Hg
                       Hfrok (u_tlb_only_refl rsA) Htlbok' Hstep
                       with "Hcert Hany Hrw Hro Hbytes Hoback Hrut").
        * (* ---- 2-ALIGNED, NOT 4-ALIGNED: bit 1 is set ---- *)
          assert (Hb1 : neq_vec (access_vec_dec va 1) ('b"0") = true).
          { destruct (neq_vec (access_vec_dec va 1) ('b"0")) eqn:Hb1';
              [reflexivity|].
            exfalso. rewrite (align4_of_low_bits va Hb0 Hb1') in Hal4.
            discriminate. }
          destruct (fetch_classify va Hacc)
            as [(w & Hum & Hok & Hcanon) | Hfault].
          -- (* low half fetchable: classify [va+2] *)
             destruct (fetch_classify (add_vec_int va 2) Hacc)
               as [(wh & Humh & Hokh & Hcanonh) | Hfaulth].
             ++ (* both halves ok *)
                assert (Hwin2 : forall j : nat, (j < 2)%nat ->
                          is_Some (mm !! RiscvModelBytes.pa_add (CommonWalk.u_walk_pa w va) j))
                  by (intros j Hj;
                      exact (u_fetch_win_in pt t mm 2 w va ltac:(lia)
                               (Z.divide_factor_l 2 2048) Hwf Hum Hal2 j
                               ltac:(lia))).
                assert (Hwin2h : forall j : nat, (j < 2)%nat ->
                          is_Some (mm !! RiscvModelBytes.pa_add
                                     (CommonWalk.u_walk_pa wh (add_vec_int va 2)) j))
                  by (intros j Hj;
                      exact (u_fetch_win_in pt t mm 2 wh (add_vec_int va 2)
                               ltac:(lia) (Z.divide_factor_l 2 2048) Hwf Humh
                               (u_align2_plus2 va Hal2) j ltac:(lia))).
                destruct (u_fetch_pure_2 pt t mm rsA w wh va
                            (register_lookup (R_bool minstret_increment) rsA)
                            Hum Hok Hcanon Humh Hokh Hcanonh Hb0 Hb1 Hal4
                            HcfgA HpinsA (u_mem_wf_ok pt t mm Hwf)
                            Hwin2 Hwin2h)
                  as (rsf' & mm' & t' & fr & Hex & Hg & Hshape & Htr &
                      Htlbok' & Hstepk).
                assert (Hstep : u_mem_step pt t t' mm mm')
                  by exact (u_mem_step_of_ok pt t t' mm mm' Hwf Hstepk).
                assert (Hfrok : u_fr_ok va fr)
                  by (left; split; [ exact Hshape | exact Hal2 ]).
                iApply (u_swp_fetch t t' mm mm' usatp pcfg paddr mcenv scenv
                          hpm rs1 rsA rsf' fr va
                          Hbase Hrvc LhsA LcpA HmsokA LmiA LpcA LstvecA LmieA
                          LmdlA LmenvA LsatpA LpcfgA LpaddrA HpinsA Hwf Hex Hg
                          Hfrok Htr Htlbok' Hstep
                          with "Hcert Hany Hrw Hro Hbytes Hoback Hrut").
             ++ (* low half ok, the straddle faults at [va+2] *)
                assert (Hwin2 : forall j : nat, (j < 2)%nat ->
                          is_Some (mm !! RiscvModelBytes.pa_add (CommonWalk.u_walk_pa w va) j))
                  by (intros j Hj;
                      exact (u_fetch_win_in pt t mm 2 w va ltac:(lia)
                               (Z.divide_factor_l 2 2048) Hwf Hum Hal2 j
                               ltac:(lia))).
                destruct (u_fetch_or_fault_pure_2_second pt t mm rsA w va
                            (register_lookup (R_bool minstret_increment) rsA)
                            Hum Hok Hcanon Hfaulth Hb0 Hb1 Hal4
                            HcfgA HpinsA (u_mem_wf_ok pt t mm Hwf) Hwin2)
                  as (rsf' & mm' & t' & fr & Hex & Hg & Hshape & Htr &
                      Htlbok' & Hstepk).
                assert (Hstep : u_mem_step pt t t' mm mm')
                  by exact (u_mem_step_of_ok pt t t' mm mm' Hwf Hstepk).
                assert (Hfrok : u_fr_ok va fr).
                { destruct Hshape as [(h & ->) | (ex & -> & Hue)].
                  - left. split; [ left; by exists h | exact Hal2 ].
                  - right. exists ex, (add_vec_int va 2).
                    split; [ reflexivity | exact Hue ]. }
                iApply (u_swp_fetch t t' mm mm' usatp pcfg paddr mcenv scenv
                          hpm rs1 rsA rsf' fr va
                          Hbase Hrvc LhsA LcpA HmsokA LmiA LpcA LstvecA LmieA
                          LmdlA LmenvA LsatpA LpcfgA LpaddrA HpinsA Hwf Hex Hg
                          Hfrok Htr Htlbok' Hstep
                          with "Hcert Hany Hrw Hro Hbytes Hoback Hrut").
          -- (* low half faults *)
             destruct (u_fetch_fault_pure_2_first pt t mm rsA va
                         (register_lookup (R_bool minstret_increment) rsA)
                         Hfault Hb0 Hb1 Hal4 HcfgA HpinsA
                         (u_mem_wf_ok pt t mm Hwf))
               as (rsf' & mm' & t' & fr & Hex & Hg & Hshape & Htr &
                   Htlbok' & Hstepk).
             assert (Hstep : u_mem_step pt t t' mm mm')
               by exact (u_mem_step_of_ok pt t t' mm mm' Hwf Hstepk).
             assert (Hfrok : u_fr_ok va fr).
             { destruct Hshape as (ex & -> & Hue).
               right. exists ex, va. split; [ reflexivity | exact Hue ]. }
             iApply (u_swp_fetch t t' mm mm' usatp pcfg paddr mcenv scenv hpm
                       rs1 rsA rsf' fr va
                       Hbase Hrvc LhsA LcpA HmsokA LmiA LpcA LstvecA LmieA
                       LmdlA LmenvA LsatpA LpcfgA LpaddrA HpinsA Hwf Hex Hg
                       Hfrok Htr Htlbok' Hstep
                       with "Hcert Hany Hrw Hro Hbytes Hoback Hrut").
  Qed.

  (* ===================================================================== *)
  (* §11  WIRE TOWARD THE CAPSTONE.                                         *)
  (* ===================================================================== *)

  (* the ACTIVE-residue step obligation, from the two totalities *)
  Lemma user_step_obligation_active_holds :
    (forall (va : mword 64) (mi : bool), base_exec_total_u pt va mi) ->
    (forall (va : mword 64) (mi : bool), rvc_exec_total_u pt va mi) ->
    hw_config -∗ minstret_inv -∗ wire_inv -∗ user_step_obligation_active C pt Rut.
  Proof.
    intros Hbase Hrvc. iIntros "#Hhw #Hmin #Hwinv".
    iApply (wp_user_step_active C pt Rut with "Hhw Hmin Hwinv").
    iApply (active_class_intro (⊤ ∖ ↑minstretN ∖ ↑wireN ∖ ↑clockN) Hbase Hrvc
              with "Hhw").
  Qed.

  (* THE CAPSTONE: safety of arbitrary user-mode execution, parametrized on
     the two execute totalities. *)
  Theorem wp_user_exec_full :
    (forall (va : mword 64) (mi : bool), base_exec_total_u pt va mi) ->
    (forall (va : mword 64) (mi : bool), rvc_exec_total_u pt va mi) ->
    hw_config -∗ minstret_inv -∗ wire_inv -∗
    user_inv C pt Rut -∗ ▷ stvec_handler_wp C pt Rut -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hbase Hrvc. iIntros "#Hhw #Hmin #Hwinv Hinv Htrap".
    iApply (wp_user_exec_active C pt Rut with "Hhw [] Hinv Htrap").
    iApply (user_step_obligation_active_holds Hbase Hrvc with "Hhw Hmin Hwinv").
  Qed.

End UserActiveClass.
