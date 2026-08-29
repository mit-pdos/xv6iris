(* ===================================================================== *)
(* UexecApply.v -- THE VOCABULARY THE TRAP LOOP NEEDS TO APPLY A SLOT.     *)
(*                                                                        *)
(* Milestone J (claude-notes/projects/user-wp-slot.md SS4c) has the loop   *)
(* hold [UexecRet.uexec_ret sc W] across a round and re-key it at the      *)
(* state the round resumed.  Everything here is what that re-keying needs  *)
(* and nothing in the tree had:                                           *)
(*                                                                        *)
(*   SS1  [ret_pc] ON [Z], and the one bv fact the bump wants (K4):        *)
(*        [ret_pc_add4] -- adding four does not touch bit 0, so clearing   *)
(*        it before or after the [epc += 4] gives the same resume pc.      *)
(*   SS2  FOUR REGISTER PEELS out of [tf_resume_gpr0] (K5): x0, a0, a1     *)
(*        and a7.  [UexecSlot.tf_resume_gpr_sp] is the discipline -- never *)
(*        [rewrite upd_eq], never a [reflexivity] across the 31-insert     *)
(*        [userret_gpr] tower; go through [apply]/[exact] at explicit      *)
(*        arguments and let the kernel do the conversion.                  *)
(*   SS3  [usys_mem_ok] is blind to everything but the number and the two  *)
(*        window bases, so two keys agreeing there carry the same row.     *)
(*   SS4  THE KEY CONGRUENCES: [uslot] depends on its key only through     *)
(*        [(tf_resume_gpr0 tf, tf_resume_pc tf, uvis_M, uvis_perm)], and   *)
(*        [uexec_ret] only through those plus the number and the two       *)
(*        window bases.  [uexec_ret_run] is the instance the loop uses:    *)
(*        the trapped key and the RUN key it projects to are the same key. *)
(*   SS5  [UserPerm.usz_ok] from the trapframe bound, so the loop can      *)
(*        discharge [uvb]'s size guard from [ProcInv]'s own conjunct       *)
(*        ([proc_priv_nopt_sz_maxsz], added there for this).               *)
(*                                                                        *)
(* NOT HERE: a mover between [UexecRet.trapped_machine] and a              *)
(* [UserExec.user_trap_frame_at] whose image is NAMED.  The two differ in  *)
(* exactly one conjunct -- [user_ptm_inv pt sz M] against [user_pt_any     *)
(* pt] -- so the direction that FORGETS the image is a one-liner and is    *)
(* below ([trapped_machine_frame]); the direction that names it is         *)
(* S3's [user_trap_frame_atm] (SS4c's "lazy seam", which needs the twin in *)
(* BOTH directions and a new USERTRAP_RES entry), and stating half of it   *)
(* here would only have to be restated there.                              *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec RiscvExtras.
Require Import RegFile WpGpr.
Require Import MinstretInv WireInv.
Require Import ProcDefs.     (* [ustate] / [pv_tf] / [pv_sz] / [pv_upt] *)
Require Import UserFrame.    (* [u_regs] -- the loop's own cell bundle *)
Require Import UmodeRegs.    (* [uv_regs] / [uv_amb] and the two movers *)
Require Import UexecWp.      (* [loop_ok] -- [uslot]'s own guard *)
Require Import ProcGeom.     (* [tf_arg_idx] / [tf_epc_idx] / [TFWORDS] *)
Require Import UserPtTree.   (* [uptd] / [user_ptm_inv] / [pgroundup] on Z *)
Require Import ProcPtOwn.    (* [uvm_maxsz] *)
Require Import UserPerm.     (* [uperm] / [usz_ok] *)
Require Import UserExec.     (* [user_trap_frame_at] *)
Require Import UsysMemOk.    (* [usys_num] / [usys_mem_ok] / [bump_tf] *)
Require Import SpecUserret.  (* [userret_gpr] -- the 31-insert register file *)
Require Import UexecSlot.    (* [uvis] / [tf_w] / [tf_resume_gpr] / [ret_pc_idem] *)
Require Import UexecRet.     (* [tf_resume_gpr0] / [tf_of] / [uslot] / [uexec_ret] *)
Require Import UexecRound.   (* the round this vocabulary is applied under *)
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* SS1 [ret_pc] ON [Z], AND THE +4 CONGRUENCE (K4).                        *)
(*                                                                         *)
(* [ret_pc] clears bit 0, i.e. rounds DOWN to an even number, and the      *)
(* [epc += 4] the trap round performs cannot carry into bit 0.  So the     *)
(* resume pc after a bump is the same whether the trapped key carried the  *)
(* raw epc word or the already-cleared one -- which is exactly the         *)
(* difference between the key the kernel holds and the key                 *)
(* [UexecRet.uvis_of_run] projects to.                                     *)
(*                                                                         *)
(* The rewrite chain below is [AlignBits.update_bit0_zero_of_aligned2]'s,  *)
(* stopped one step earlier: that lemma is this one plus evenness.  Kept   *)
(* in this file rather than beside it because [AlignBits] is a leaf with a *)
(* deliberately minimal import set.                                        *)
(* ===================================================================== *)
Lemma ret_pc_unsigned (v : mword 64) :
  bv_unsigned (ret_pc v) = bv_unsigned v / 2 * 2.
Proof.
  pose proof (bv_unsigned_in_range _ v) as [Hlo Hhi].
  unfold ret_pc, update_vec_dec, update_mword_dec, MachineWord.update_slice.
  rewrite bv_concat_unsigned'.
  rewrite bv_concat_unsigned'.
  unfold MachineWord.slice.
  rewrite !bv_extract_unsigned.
  change (Z.of_N 0) with 0%Z.
  rewrite Z.shiftr_0_r.
  match goal with |- context [bv_wrap (MachineWord.Z_idx 0) ?z] =>
    replace (bv_wrap (MachineWord.Z_idx 0) z) with 0%Z
      by (unfold bv_wrap, bv_modulus;
          change (2 ^ Z.of_N (MachineWord.Z_idx 0))%Z with 1%Z;
          rewrite Z.mod_1_r; reflexivity) end.
  match goal with |- context [Z.lor ?hi (bv_wrap ?w ?z)] =>
    replace (bv_wrap w z) with 0%Z by (vm_compute; reflexivity) end.
  rewrite Z.lor_0_r.
  change (Z.of_N (MachineWord.Z_idx 0 + MachineWord.Z_idx 1)) with 1%Z.
  change (MachineWord.Z_idx 64 - MachineWord.Z_idx 1 - MachineWord.Z_idx 0)%N with 63%N.
  (* the three conditional rewrites are FULLY APPLIED / asserted: [rewrite]
     here is ssreflect's (the proofmode pulls it in) and does not take a
     [by] suffix the way the same script does in AlignBits. *)
  rewrite (Z.shiftr_div_pow2 _ 1 ltac:(lia)).
  change (2 ^ 1)%Z with 2%Z.
  assert (Hm64 : bv_modulus (MachineWord.Z_idx 64) = (2 ^ 64)%Z)
    by (vm_compute; reflexivity).
  assert (Hpow : (2 ^ 64)%Z = (2 * 2 ^ 63)%Z) by (vm_compute; reflexivity).
  rewrite Hm64 in Hhi.
  assert (Hdiv : (0 <= bv_unsigned v / 2 < 2 ^ 63)%Z).
  { split; [ apply Z.div_pos; lia | ].
    apply Z.div_lt_upper_bound; [ lia | ]. lia. }
  assert (Hw63 : bv_wrap 63 (bv_unsigned v / 2) = bv_unsigned v / 2).
  { apply bv_wrap_small.
    replace (bv_modulus 63) with (2 ^ 63)%Z by (vm_compute; reflexivity).
    lia. }
  rewrite Hw63.
  rewrite (Z.shiftl_mul_pow2 _ 1 ltac:(lia)).
  change (2 ^ 1)%Z with 2%Z.
  apply bv_wrap_small. rewrite Hm64. lia.
Qed.

Lemma addv4_unsigned (x : mword 64) :
  bv_unsigned (add_vec_int x 4) = bv_wrap 64 (bv_unsigned x + 4).
Proof.
  unfold add_vec_int. rewrite add_vec64_unsigned.
  assert (H4 : bv_unsigned (mword_of_int 4 : mword 64) = 4%Z)
    by (vm_compute; reflexivity).
  rewrite H4. reflexivity.
Qed.

(* the pure arithmetic: [2^64] is even, so a carry out of the low bit is
   impossible and clearing it commutes with adding an even number. *)
Local Lemma z_wrap_even2 (t : Z) :
  exists j : Z, (Z.modulo (2 * t) 18446744073709551616 = 2 * j)%Z
                /\ (0 <= 2 * j < 18446744073709551616)%Z.
Proof.
  pose proof (Z.div_mod (2 * t) 18446744073709551616 ltac:(lia)) as H1.
  pose proof (Z.mod_pos_bound (2 * t) 18446744073709551616 ltac:(lia)) as H2.
  exists (t - 9223372036854775808 * (Z.div (2 * t) 18446744073709551616))%Z.
  split; lia.
Qed.

Local Lemma z_bit0_add4 (u : Z) :
  (0 <= u)%Z ->
  (Z.modulo (u / 2 * 2 + 4) 18446744073709551616 / 2 * 2)%Z
  = (Z.modulo (u + 4) 18446744073709551616 / 2 * 2)%Z.
Proof.
  intros Hu.
  pose proof (Z.div_mod u 2 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound u 2 ltac:(lia)) as Hr.
  assert (Ht : (u / 2 * 2 + 4 = 2 * (u / 2 + 2))%Z) by lia.
  assert (Hu2 : (u + 4 = 2 * (u / 2 + 2) + Z.modulo u 2)%Z) by lia.
  rewrite Ht Hu2.
  destruct (z_wrap_even2 (u / 2 + 2)%Z) as [j [Hj Hjb]].
  assert (Hadd : (Z.modulo (2 * (u / 2 + 2) + Z.modulo u 2) 18446744073709551616
                  = 2 * j + Z.modulo u 2)%Z).
  { rewrite <- (Z.add_mod_idemp_l (2 * (u / 2 + 2)) (Z.modulo u 2)
                  18446744073709551616 ltac:(lia)).
    rewrite Hj. apply Z.mod_small. lia. }
  rewrite Hj Hadd.
  (* the two divisions, by hand: [lia] alone will not find the witness that
     [2j] and [2j + r] round down to the same [j]. *)
  assert (Hd1 : (2 * j / 2 = j)%Z).
  { replace (2 * j)%Z with (j * 2)%Z by lia.
    exact (Z.div_mul j 2 ltac:(lia)). }
  assert (Hr0 : (Z.modulo u 2 / 2 = 0)%Z) by (apply Z.div_small; lia).
  assert (Hd2 : ((2 * j + Z.modulo u 2) / 2 = j)%Z).
  { replace (2 * j + Z.modulo u 2)%Z with (j * 2 + Z.modulo u 2)%Z by lia.
    rewrite (Z.div_add_l j 2 (Z.modulo u 2) ltac:(lia)). rewrite Hr0. lia. }
  rewrite Hd1 Hd2. reflexivity.
Qed.

(* K4 -- true UNCONDITIONALLY. *)
Lemma ret_pc_add4 (v : mword 64) :
  ret_pc (add_vec_int (ret_pc v) 4) = ret_pc (add_vec_int v 4).
Proof.
  apply bv_eq.
  rewrite (ret_pc_unsigned (add_vec_int (ret_pc v) 4)).
  rewrite (ret_pc_unsigned (add_vec_int v 4)).
  rewrite !addv4_unsigned.
  rewrite (ret_pc_unsigned v).
  unfold bv_wrap. rewrite bv_modulus64.
  exact (z_bit0_add4 (bv_unsigned v) (proj1 (bv_unsigned_in_range _ v))).
Qed.

(* ...and the congruence the round's bump actually applies: two epc words
   with the same resume pc bump to the same resume pc. *)
Lemma ret_pc_add4_cong (x y : mword 64) :
  ret_pc x = ret_pc y ->
  ret_pc (add_vec_int x 4) = ret_pc (add_vec_int y 4).
Proof.
  intros H.
  rewrite <- (ret_pc_add4 x). rewrite <- (ret_pc_add4 y). rewrite H.
  reflexivity.
Qed.

(* ===================================================================== *)
(* SS2 FOUR REGISTER PEELS OUT OF [tf_resume_gpr0] (K5).                   *)
(*                                                                         *)
(* Same discipline as [UexecSlot.tf_resume_gpr_sp]: peel the insert chain  *)
(* by [apply], discharge each key disequality by [vm_compute;              *)
(* discriminate] (both keys are closed literals, so there is no symbolic   *)
(* value for the reduction to meet), and finish at [upd_eq] -- NEVER a     *)
(* [rewrite]/[reflexivity] that could see the whole [userret_gpr] tower.   *)
(* ===================================================================== *)
Local Lemma tf_upd_ne (f : regfile) (k j : regidx) (v w : mword 64) :
  j <> k -> f !!! j = w -> (<[k := v]> f) !!! j = w.
Proof. intros Hne <-. exact (upd_ne f k j v Hne). Qed.

Local Ltac gpr_peel :=
  repeat (apply tf_upd_ne; [ vm_compute; discriminate | ]).

(* x0 is the ONE index the dead base survives at, and [tf_resume_gpr0]
   pins it to zero -- which is what [UexecRet.tf_of_resume_gpr]'s premise
   asks for at the projected key. *)
Lemma tf_resume_gpr0_x0 (tf : list (mword 64)) :
  tf_resume_gpr0 tf !!! Regidx (mword_of_int 0) = zero_reg.
Proof.
  unfold tf_resume_gpr0, tf_resume_gpr, userret_gpr.
  gpr_peel. unfold zero_rf. reflexivity.
Qed.

(* a0 = x10, trapframe word [tf_arg_idx 0] = 14 (the return-value slot) *)
Lemma tf_resume_gpr0_a0 (tf : list (mword 64)) :
  tf_resume_gpr0 tf !!! Regidx (mword_of_int 10) = tf_w tf (tf_arg_idx 0).
Proof.
  unfold tf_resume_gpr0, tf_resume_gpr, userret_gpr.
  gpr_peel. exact (upd_eq _ (Regidx (mword_of_int 10)) _).
Qed.

(* a1 = x11, trapframe word [tf_arg_idx 1] = 15 (read/fstat's buffer) *)
Lemma tf_resume_gpr0_a1 (tf : list (mword 64)) :
  tf_resume_gpr0 tf !!! Regidx (mword_of_int 11) = tf_w tf (tf_arg_idx 1).
Proof.
  unfold tf_resume_gpr0, tf_resume_gpr, userret_gpr.
  gpr_peel. exact (upd_eq _ (Regidx (mword_of_int 11)) _).
Qed.

(* a7 = x17, trapframe word [tf_arg_idx 7] = 21 -- THE SYSCALL NUMBER *)
Lemma tf_resume_gpr0_a7 (tf : list (mword 64)) :
  tf_resume_gpr0 tf !!! Regidx (mword_of_int 17) = tf_w tf (tf_arg_idx 7).
Proof.
  unfold tf_resume_gpr0, tf_resume_gpr, userret_gpr.
  gpr_peel. exact (upd_eq _ (Regidx (mword_of_int 17)) _).
Qed.

(* ===================================================================== *)
(* SS3 THE TABLE READS THREE WORDS.                                        *)
(*                                                                         *)
(* [UsysMemOk.usys_mem_ok_ueq] transports a row across [tf_ueq], which     *)
(* pins the EPC word too -- and the epc is exactly where the trapped key   *)
(* and its run projection differ ([ret_pc] of it against it).  What is     *)
(* actually read is the number (word 21) and the two window bases (14 and  *)
(* 15), so state the congruence at those.                                  *)
(* ===================================================================== *)
Lemma usys_mem_ok_args (n : Z) (tf tf' : list (mword 64)) (r : mword 64)
    (M M' : gmap Z (bv 8)) (pi pi' : gmap (mword 27) uperm) :
  tf !!! tf_arg_idx 0 = tf' !!! tf_arg_idx 0 ->
  tf !!! tf_arg_idx 1 = tf' !!! tf_arg_idx 1 ->
  usys_mem_ok n tf r M pi M' pi' -> usys_mem_ok n tf' r M pi M' pi'.
Proof.
  intros H0 H1 H. unfold usys_mem_ok in H |- *.
  destruct (decide (n = USYS_exec)); [ exact H | ].
  destruct (decide (n = USYS_sbrk)); [ exact H | ].
  destruct (usys_window n) as [i | ] eqn:Hw; [ | exact H ].
  destruct (usys_window_idx n i Hw) as [-> | ->];
    [ rewrite <- H0 | rewrite <- H1 ]; exact H.
Qed.

(* ===================================================================== *)
(* SS4 THE RUN KEY, AND THE TWO CONGRUENCES.                               *)
(* ===================================================================== *)

(* THE RUN PROJECTION of a key: the machine the key describes, written
   back out as a trapframe.  [UexecRet.uvis_of_run] at the key's own
   resume register file and resume pc.  It is NOT the same list -- the
   four kernel words are dropped and the epc word is [ret_pc]'d -- but it
   is the same KEY, which is what SS4 proves. *)
Definition uvis_run (W : uvis) : uvis :=
  uvis_of_run (tf_resume_gpr0 (uvis_tf W))
              (ret_pc (tf_w (uvis_tf W) tf_epc_idx))
              (uvis_M W) (uvis_perm W).

Lemma uvis_run_length (W : uvis) : length (uvis_tf (uvis_run W)) = TFWORDS.
Proof. exact (tf_of_length _ _). Qed.

Lemma uvis_run_gpr (W : uvis) :
  tf_resume_gpr0 (uvis_tf (uvis_run W)) = tf_resume_gpr0 (uvis_tf W).
Proof.
  unfold uvis_run. cbn [uvis_tf uvis_of_run].
  exact (tf_of_resume_gpr _ _ (tf_resume_gpr0_x0 (uvis_tf W))).
Qed.

Lemma uvis_run_pc (W : uvis) :
  tf_resume_pc (uvis_tf (uvis_run W)) = tf_resume_pc (uvis_tf W).
Proof.
  unfold uvis_run, tf_resume_pc. cbn [uvis_tf uvis_of_run].
  rewrite (tf_of_epc (tf_resume_gpr0 (uvis_tf W))
             (ret_pc (tf_w (uvis_tf W) tf_epc_idx))).
  exact (ret_pc_idem (tf_w (uvis_tf W) tf_epc_idx)).
Qed.

Lemma uvis_run_num (W : uvis) :
  usys_num (uvis_tf (uvis_run W)) = usys_num (uvis_tf W).
Proof.
  unfold uvis_run. cbn [uvis_tf uvis_of_run].
  rewrite (tf_of_num (tf_resume_gpr0 (uvis_tf W))
             (ret_pc (tf_w (uvis_tf W) tf_epc_idx))).
  rewrite (tf_resume_gpr0_a7 (uvis_tf W)).
  unfold usys_num, tf_w. reflexivity.
Qed.

Lemma uvis_run_arg0 (W : uvis) :
  uvis_tf (uvis_run W) !!! tf_arg_idx 0 = uvis_tf W !!! tf_arg_idx 0.
Proof. exact (tf_resume_gpr0_a0 (uvis_tf W)). Qed.

Lemma uvis_run_arg1 (W : uvis) :
  uvis_tf (uvis_run W) !!! tf_arg_idx 1 = uvis_tf W !!! tf_arg_idx 1.
Proof. exact (tf_resume_gpr0_a1 (uvis_tf W)). Qed.

Section Apply.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  (* THE SLOT SEES FOUR PROJECTIONS OF ITS KEY AND NOTHING ELSE.
     [uslot_ukc] is the whole content: the slot IS [ukc] at
     [(perm, M, resume gpr, resume pc)]. *)
  Lemma uslot_key_cong (W W' : uvis) :
    tf_resume_gpr0 (uvis_tf W) = tf_resume_gpr0 (uvis_tf W') ->
    tf_resume_pc (uvis_tf W) = tf_resume_pc (uvis_tf W') ->
    uvis_M W = uvis_M W' ->
    uvis_perm W = uvis_perm W' ->
    (* the type ascription pins [Σ]: [uvis] is Σ-free, so without it the
       [⊣⊢] notation cannot elaborate [uslot]'s implicit [Σ] before it
       has to unify against [bi_car]. *)
    (uslot W : iProp Σ) ⊣⊢ uslot W'.
  Proof.
    intros Hg Hp HM Hpi.
    rewrite (uslot_ukc W) (uslot_ukc W').
    rewrite Hg Hp HM Hpi. reflexivity.
  Qed.

  (* ...AND THE RETURN CHANNEL SEES THOSE FOUR PLUS THE NUMBER AND THE TWO
     WINDOW BASES.  The length premises are [trapped_machine]'s own K3
     conjunct: the bump's two readers ([tf_resume_gpr_bump],
     [tf_resume_pc_bump]) are guarded on the list being long enough. *)
  Lemma uexec_ret_key_cong (sc : mword 64) (W W' : uvis) :
    length (uvis_tf W) = TFWORDS ->
    length (uvis_tf W') = TFWORDS ->
    usys_num (uvis_tf W) = usys_num (uvis_tf W') ->
    uvis_tf W !!! tf_arg_idx 0 = uvis_tf W' !!! tf_arg_idx 0 ->
    uvis_tf W !!! tf_arg_idx 1 = uvis_tf W' !!! tf_arg_idx 1 ->
    tf_resume_gpr0 (uvis_tf W) = tf_resume_gpr0 (uvis_tf W') ->
    tf_resume_pc (uvis_tf W) = tf_resume_pc (uvis_tf W') ->
    uvis_M W = uvis_M W' ->
    uvis_perm W = uvis_perm W' ->
    (uexec_ret sc W : iProp Σ) ⊣⊢ uexec_ret sc W'.
  Proof.
    intros HlW HlW' Hn Ha0 Ha1 Hg Hp HM Hpi.
    (* the BUMPED keys agree too, at every return value and every
       image/permission pair the row allows *)
    assert (Hb : forall (r : mword 64) (M' : gmap Z (bv 8))
                        (pi' : gmap (mword 27) uperm),
                   (uslot (bump W r M' pi') : iProp Σ)
                     ⊣⊢ uslot (bump W' r M' pi')).
    { intros r M' pi'.
      apply uslot_key_cong; cbn [bump uvis_tf uvis_M uvis_perm].
      - unfold tf_resume_gpr0 in Hg |- *.
        rewrite (tf_resume_gpr_bump zero_rf (uvis_tf W) r
                   ltac:(rewrite HlW; unfold tf_arg_idx, TFWORDS; lia)).
        rewrite (tf_resume_gpr_bump zero_rf (uvis_tf W') r
                   ltac:(rewrite HlW'; unfold tf_arg_idx, TFWORDS; lia)).
        rewrite Hg. reflexivity.
      - rewrite (tf_resume_pc_bump (uvis_tf W) r
                   ltac:(rewrite HlW; unfold tf_epc_idx, TFWORDS; lia)).
        rewrite (tf_resume_pc_bump (uvis_tf W') r
                   ltac:(rewrite HlW'; unfold tf_epc_idx, TFWORDS; lia)).
        exact (ret_pc_add4_cong _ _ Hp).
      - reflexivity.
      - reflexivity. }
    rewrite /uexec_ret /uexec_ret_F. cbv zeta.
    destruct (decide (sc = uecall_scause)) as [_ | _];
      [ | exact (uslot_key_cong W W' Hg Hp HM Hpi) ].
    rewrite Hn HM Hpi.
    destruct (decide (usys_num (uvis_tf W') = USYS_exit)) as [_ | _];
      [ reflexivity | ].
    destruct (decide (usys_num (uvis_tf W') = USYS_fork)) as [_ | _].
    - (* fork: two arms, both at the [(M, pi)] the key already carries *)
      iSplit.
      + iIntros "[H1 H2]". iSplitL "H1".
        * iIntros (r Hr). rewrite -(Hb r (uvis_M W') (uvis_perm W')).
          iApply ("H1" $! r). iPureIntro. exact Hr.
        * rewrite -(Hb (mword_of_int 0) (uvis_M W') (uvis_perm W')). iExact "H2".
      + iIntros "[H1 H2]". iSplitL "H1".
        * iIntros (r Hr). rewrite (Hb r (uvis_M W') (uvis_perm W')).
          iApply ("H1" $! r). iPureIntro. exact Hr.
        * rewrite (Hb (mword_of_int 0) (uvis_M W') (uvis_perm W')). iExact "H2".
    - (* the returning arms: the row transports by SS3 *)
      iSplit.
      + iIntros "H" (r M' pi' Hmo).
        rewrite -(Hb r M' pi'). iApply ("H" $! r M' pi'). iPureIntro.
        exact (usys_mem_ok_args _ (uvis_tf W') (uvis_tf W) r _ _ _ _
                 (eq_sym Ha0) (eq_sym Ha1) Hmo).
      + iIntros "H" (r M' pi' Hmo).
        rewrite (Hb r M' pi'). iApply ("H" $! r M' pi'). iPureIntro.
        exact (usys_mem_ok_args _ (uvis_tf W) (uvis_tf W') r _ _ _ _
                 Ha0 Ha1 Hmo).
  Qed.

  (* THE INSTANCE THE LOOP USES: the key the kernel trapped with and the
     key its own resume projection describes are the same key, so a
     [uexec_ret] handed back at one is a [uexec_ret] at the other.  The
     length premise is [trapped_machine]'s K3 conjunct. *)
  Lemma uexec_ret_run (sc : mword 64) (W : uvis) :
    length (uvis_tf W) = TFWORDS ->
    (uexec_ret sc W : iProp Σ) ⊣⊢ uexec_ret sc (uvis_run W).
  Proof.
    intros Hl.
    apply (uexec_ret_key_cong sc W (uvis_run W) Hl (uvis_run_length W)
             (eq_sym (uvis_run_num W)) (eq_sym (uvis_run_arg0 W))
             (eq_sym (uvis_run_arg1 W)) (eq_sym (uvis_run_gpr W))
             (eq_sym (uvis_run_pc W)) eq_refl eq_refl).
  Qed.

End Apply.

(* ===================================================================== *)
(* SS4b THE ONE FRAME MOVER THAT IS FREE.                                  *)
(*                                                                         *)
(* [trapped_machine] and [UserExec.user_trap_frame_at] are the SAME rows   *)
(* but for the image conjunct: the former names it at the lazy tier        *)
(* ([user_ptm_inv pt sz M]), the latter existentially                      *)
(* ([UserPtTree.user_pt_any pt]).  Forgetting the image is                 *)
(* [user_ptm_inv_any]; naming it is S3's business (see the header).        *)
(* ===================================================================== *)
Section Frame.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma trapped_machine_frame (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ)
      (sz : Z) (sc stv : mword 64) (W : uvis) :
    trapped_machine C pt Rut sz sc stv W -∗
    ∃ ms_v : mword 64,
      ⌜trap_mstatus_ok ms_v⌝ ∗
      user_trap_frame_at C pt Rut ms_v sc stv
        (tf_w (uvis_tf W) tf_epc_idx) (tf_resume_gpr0 (uvis_tf W)).
  Proof.
    (* post-S3 [trapped_machine] IS [user_trap_frame_atm] plus the K3 length
       conjunct, so the only row that moves is the image. *)
    rewrite /trapped_machine /user_trap_frame_atm /user_trap_frame_at.
    iIntros "H".
    iDestruct "H" as (ms_v) "(%Hlen & %Hto & Hhs & Hpriv & Hms & Hsc & Hstv &
                              Hsep & Hpc & Hg & Hpt & Hcfg & Hrut)".
    iDestruct (user_ptm_inv_any with "Hpt") as "Hany".
    iExists ms_v.
    iSplitR; [ iPureIntro; exact Hto | ].
    iSplitR; [ iPureIntro; exact Hto | ].
    iSplitL "Hhs"; [ iExact "Hhs" | ].
    iSplitL "Hpriv"; [ iExact "Hpriv" | ].
    iSplitL "Hms"; [ iExact "Hms" | ].
    iSplitL "Hsc"; [ iExact "Hsc" | ].
    iSplitL "Hstv"; [ iExact "Hstv" | ].
    iSplitL "Hsep"; [ iExact "Hsep" | ].
    iSplitL "Hpc"; [ iExact "Hpc" | ].
    iSplitL "Hg"; [ iExact "Hg" | ].
    iSplitL "Hany"; [ iExact "Hany" | ].
    iSplitL "Hcfg"; [ iExact "Hcfg" | ].
    iExact "Hrut".
  Qed.

End Frame.

(* ===================================================================== *)
(* SS5 THE RESUME SIZE GUARD.                                              *)
(*                                                                         *)
(* [UexecRet.uvb] carries [⌜usz_ok sz⌝], and the loop's [sz] is the        *)
(* process's own [p->sz].  [ProcInv.proc_priv_nopt_sz_maxsz] gives         *)
(* [uint (pv_sz V) <= uvm_maxsz]; [uvm_maxsz = 2^38 - 8192] is             *)
(* page-aligned and IS [usz_ok]'s bound, so [pgroundup]'s monotonicity     *)
(* closes the gap.                                                         *)
(* ===================================================================== *)
Lemma usz_ok_of_maxsz (sz : Z) : (sz <= uvm_maxsz)%Z -> usz_ok sz.
Proof.
  intros H. rewrite uvm_maxsz_val in H. unfold usz_ok.
  refine (Z.le_trans _ _ _
            (UserPtTree.pgroundup_mono sz 274877898752 H) _).
  vm_compute. discriminate.
Qed.

(* ===================================================================== *)
(* SS6 THE ROUND'S TAIL, AS NAMED LEMMAS (milestone J, stage S5).          *)
(*                                                                         *)
(* [ProofUserretClosed.stvec_handler_loop] is a whole-function continuation *)
(* -- every proofmode step in it pays for the whole Iris context           *)
(* (claude-notes/optimization.md, RULE ONE) -- so the round's END, which is *)
(* pure re-keying and one bundle construction, is discharged HERE, where    *)
(* the context is the lemma's own premises and nothing else.               *)
(*                                                                         *)
(*   [uexec_ret_round_slot] / [_of]  steps A and B: the returned            *)
(*        [uexec_ret] is re-keyed onto the RUN projection of the trapped    *)
(*        key ([uexec_ret_run]) -- which is the key the round's relation is *)
(*        stated at -- and then the round's own arm picks which of          *)
(*        [uexec_ret]'s arms pays: transparent, ecall/exec (MINT),          *)
(*        ecall/fork (MINT), ecall/other (the bumped slot).  The mint       *)
(*        arrives as the premise [∀ W, uslot W]: the loop holds a           *)
(*        [UEXEC_GEN] and [UexecCond.cond_entry_slot] turns its [box] into  *)
(*        exactly that family, so this file needs no functor argument.      *)
(*   [ukc_apply]                     step D: [uvb] built ROW BY ROW (never  *)
(*        [iFrame]: the bundle carries [gpr_file]) and the continuation     *)
(*        applied at the table/size the round landed on -- which is step C, *)
(*        the guard, met by [reflexivity] because the bundle is asked for   *)
(*        at [perm_of (ud_um pt) sz] itself.                                *)
(*   [uslot_apply_loop]              the two composed at a KEY: the slot's  *)
(*        four projections are supplied as equations, so the caller states  *)
(*        what its post gave it and never unfolds the seal.                 *)
(* ===================================================================== *)
(* [tf_resume_gpr_bump] at the canonical dead base -- the spelling the
   round's [uround_bump_ok] is stated in. *)
Lemma tf_resume_gpr0_bump (tf : list (mword 64)) (r : mword 64) :
  (tf_arg_idx 0 < length tf)%nat ->
  tf_resume_gpr0 (bump_tf tf r)
  = <[Regidx (mword_of_int 10) := r]> (tf_resume_gpr0 tf).
Proof.
  intros Hl. unfold tf_resume_gpr0. exact (tf_resume_gpr_bump zero_rf tf r Hl).
Qed.

Section LoopApply.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ------------------------------------------------------------------ *)
  (* STEPS A + B: the returned [uexec_ret], re-keyed at the resume state. *)
  (* ------------------------------------------------------------------ *)
  Lemma uexec_ret_round_slot (sc : mword 64) (W W' : uvis) :
    length (uvis_tf W) = TFWORDS ->
    uround_ok sc (uvis_tf (uvis_run W)) (uvis_M W) (uvis_perm W)
      (uvis_tf W') (uvis_M W') (uvis_perm W') ->
    (∀ W'' : uvis, uslot W'') -∗ uexec_ret sc W -∗ uslot W'.
  Proof.
    intros Hl Hr.
    iIntros "Hmk Hret".
    (* STEP A: the trapped key and its run projection are the same key *)
    iEval (rewrite (uexec_ret_run sc W Hl)) in "Hret".
    (* the two length side conditions the bump's readers take *)
    assert (Hla : (tf_arg_idx 0 < length (uvis_tf (uvis_run W)))%nat)
      by (rewrite (uvis_run_length W); unfold tf_arg_idx, TFWORDS; lia).
    assert (Hle : (tf_epc_idx < length (uvis_tf (uvis_run W)))%nat)
      by (rewrite (uvis_run_length W); unfold tf_epc_idx, TFWORDS; lia).
    destruct (decide (sc = uecall_scause)) as [Hec | Hne].
    - (* ---- ECALL ---- *)
      rewrite (uexec_ret_ecall sc (uvis_run W) Hec).
      rewrite Hec in Hr.
      destruct (uround_ok_ecall (uvis_tf (uvis_run W)) (uvis_M W) (uvis_M W')
                  (uvis_perm W) (uvis_perm W') (uvis_tf W') Hr)
        as [Hexec | [Hnex [r [[Hb1 Hb2] Hm]]]].
      + (* exec: the round says NOTHING by design -- the kernel MINTS *)
        iApply "Hmk".
      + cbv zeta.
        destruct (decide (usys_num (uvis_tf (uvis_run W)) = USYS_exit))
          as [Hx | _]; [ contradiction (Hnex Hx) | ].
        destruct (decide (usys_num (uvis_tf (uvis_run W)) = USYS_fork))
          as [_ | _].
        * (* fork: nothing says [r <> 0] (K2) -- MINT *)
          iApply "Hmk".
        * (* the returning arms: the row is the round's own conjunct *)
          iDestruct ("Hret" $! r (uvis_M W') (uvis_perm W') with "[%]") as "Hs";
            [ exact Hm | ].
          (* the bump's two readers, hoisted out of argument position
             (claude-notes/optimization.md, "Inline [ltac:]") *)
          assert (Hg1 : tf_resume_gpr0 (bump_tf (uvis_tf (uvis_run W)) r)
                        = tf_resume_gpr0 (uvis_tf W')).
          { rewrite (tf_resume_gpr0_bump (uvis_tf (uvis_run W)) r Hla).
            exact (eq_sym Hb1). }
          assert (Hp1 : tf_resume_pc (bump_tf (uvis_tf (uvis_run W)) r)
                        = tf_resume_pc (uvis_tf W')).
          { rewrite (tf_resume_pc_bump (uvis_tf (uvis_run W)) r Hle).
            exact (eq_sym Hb2). }
          iEval (rewrite (uslot_key_cong
                            (bump (uvis_run W) r (uvis_M W') (uvis_perm W')) W'
                            Hg1 Hp1 eq_refl eq_refl)) in "Hs".
          iExact "Hs".
    - (* ---- TRANSPARENT: interrupt, page fault, anything else ---- *)
      rewrite (uexec_ret_transparent sc (uvis_run W) Hne).
      destruct (uround_ok_transparent sc (uvis_tf (uvis_run W))
                  (uvis_M W) (uvis_M W') (uvis_perm W) (uvis_perm W')
                  (uvis_tf W') Hne Hr) as [[Hi1 Hi2] [HM Hpi]].
      iEval (rewrite (uslot_key_cong (uvis_run W) W'
                        (eq_sym Hi1) (eq_sym Hi2)
                        (eq_sym HM) (eq_sym Hpi))) in "Hret".
      iExact "Hret".
  Qed.

  (* ...at the key the loop actually holds: the round's post is stated at
     the trapped machine's own register file and epc word, and the resume
     key is [UexecSlot.uvis_of] of the record the round left. *)
  Lemma uexec_ret_round_slot_of (sc : mword 64) (W : uvis) (g : regfile)
      (sepc_v : mword 64) (U' : ustate) :
    length (uvis_tf W) = TFWORDS ->
    g = tf_resume_gpr0 (uvis_tf W) ->
    sepc_v = tf_w (uvis_tf W) tf_epc_idx ->
    uround_ok sc (tf_of g (ret_pc sepc_v)) (uvis_M W) (uvis_perm W)
      (pv_tf (us_V U')) (us_M U')
      (perm_of (ud_um (pv_upt (us_V U'))) (uint (pv_sz (us_V U')))) ->
    (∀ W'' : uvis, uslot W'') -∗ uexec_ret sc W -∗ uslot (uvis_of U').
  Proof.
    intros Hl -> -> Hr.
    exact (uexec_ret_round_slot sc W (uvis_of U') Hl Hr).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* STEP D (and C): [uvb], row by row, and the continuation applied.     *)
  (* ------------------------------------------------------------------ *)
  Lemma ukc_apply (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ)
      (sz : Z) (M : gmap Z (bv 8)) (m : regfile)
      (ms_v sc_v stv_v sepc_v pc : mword 64) :
    loop_ok C pt ->
    usz_ok sz ->
    user_mstatus_ok ms_v ->
    ukc (perm_of (ud_um pt) sz) M m pc -∗
    hw_config -∗ minstret_inv -∗ wire_inv -∗
    u_regs (HART_ACTIVE tt) ms_v sc_v stv_v sepc_v pc pc m -∗
    user_ptm_inv pt sz M -∗
    user_cfg C -∗
    Rut pt -∗
    ▷ ukb C pt Rut sz (perm_of (ud_um pt) sz) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hlo Hsz Hms.
    iIntros "Hkc Hhw Hmi Hwi Hregs Hupt Hcfg Hrut Hk".
    (* the cell bundle splits into the U-mode residue, the file and the pc *)
    iDestruct (u_regs_uv_regs ms_v sc_v stv_v sepc_v pc m Hms with "Hregs")
      as "(Hur & Hg & Hpc)".
    iApply ("Hkc" $! CID C pt Rut sz
              with "[%] [%] [Hhw Hmi Hwi Hur Hg Hpc Hupt Hcfg Hrut Hk]").
    - exact Hlo.
    - reflexivity.
    - (* THE BUNDLE, ROW BY ROW -- it carries [gpr_file], so never [iFrame]
         (claude-notes/optimization.md, "Framing"). *)
      rewrite /uvb /uvb_F.
      iSplitL "Hhw Hmi Hwi"; [ iApply (uv_amb_intro with "Hhw Hmi Hwi") | ].
      iSplitL "Hur"; [ iExact "Hur" | ].
      iSplitR; [ iPureIntro; exact Hsz | ].
      iSplitL "Hupt"; [ iExact "Hupt" | ].
      iSplitL "Hcfg"; [ iExact "Hcfg" | ].
      iSplitL "Hg"; [ iExact "Hg" | ].
      iSplitL "Hpc"; [ iExact "Hpc" | ].
      iSplitL "Hrut"; [ iExact "Hrut" | ].
      rewrite /ukont_F. iExact "Hk".
  Qed.

  (* ...and the slot at a KEY, which is what the loop holds: the four
     projections the slot reads, supplied as equations. *)
  Lemma uslot_apply_loop (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ)
      (sz : Z) (W : uvis) (M : gmap Z (bv 8)) (m : regfile)
      (ms_v sc_v stv_v sepc_v pc : mword 64) :
    loop_ok C pt ->
    usz_ok sz ->
    user_mstatus_ok ms_v ->
    uvis_perm W = perm_of (ud_um pt) sz ->
    uvis_M W = M ->
    tf_resume_gpr0 (uvis_tf W) = m ->
    tf_resume_pc (uvis_tf W) = pc ->
    uslot W -∗
    hw_config -∗ minstret_inv -∗ wire_inv -∗
    u_regs (HART_ACTIVE tt) ms_v sc_v stv_v sepc_v pc pc m -∗
    user_ptm_inv pt sz M -∗
    user_cfg C -∗
    Rut pt -∗
    ▷ ukb C pt Rut sz (perm_of (ud_um pt) sz) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hlo Hsz Hms Hpi HM Hg Hpc.
    iIntros "Hs".
    (* the seal comes off the HYPOTHESIS only *)
    iEval (rewrite uslot_ukc) in "Hs".
    iEval (rewrite Hpi HM Hg Hpc) in "Hs".
    iApply (ukc_apply C pt Rut sz M m ms_v sc_v stv_v sepc_v pc Hlo Hsz Hms
              with "Hs").
  Qed.

End LoopApply.
