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
Require Import MinstretInv RegFile UserBits AlignBits.
Require Import TrampPt KptTree UptTree.
Require Import UserPtTree UserExec UserStep.
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

  (* ------------------------------------------------------------------- *)
  (* §3 .. §5 -- THE ASSEMBLY -- WAITING ON THE FETCH.                      *)
  (*                                                                       *)
  (* [active_obligations] routed each [va] geometry to one of the six       *)
  (* whole-[run_hart_active] producers of the old [UserClassifyAsm], and    *)
  (* [active_class_intro] then ran [active_step_branch].  Under per-node    *)
  (* semantics the SAME case tree routes to the SAME six geometries, but    *)
  (* what each of them owes is now a [swp (fetch tt) (run_fetch_post ...)]  *)
  (* -- HartRunFull's match-shaped fetch obligation -- rather than an       *)
  (* [exec (run_hart_active 0)] fact plus a move of [mstate_interp].  The   *)
  (* producers are P3's (the pure fetch composer, section 4.2 of the port   *)
  (* plan) and have not landed; the routing above it is [fetch_classify] +  *)
  (* the four alignment bridges of sections 1-2, which do not move.          *)
  (*                                                                       *)
  (* Sections 1-2 above are UNTOUCHED by the port, and that is checkable:   *)
  (* a [git diff] of them against the pre-port commit is empty.             *)
  (* ------------------------------------------------------------------- *)

End UserActiveClass.
