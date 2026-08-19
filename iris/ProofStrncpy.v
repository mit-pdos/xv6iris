(* ProofStrncpy.v -- reusable functional invariants for the whole-machine
   proof of kernel/string.c's [strncpy].  The instruction proof below builds
   its destination naming function one [bb_upd] at a time; keeping these
   facts outside the Iris context makes the loop obligations purely
   arithmetic. *)
From Stdlib Require Import Lia.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvPtsto RiscvLang RiscvExtras.
Require Import RegFile InstrBytes WpMmodeLeafBase.
Require Import SmodeCore StackOwn CalleeSaved KernelText KernelRvcDecode.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import HartTp WpNext IntrDefs ByteCursor ByteBuf KstackArith.
Require Import VcGen.
Require Import CodeStrncpy SpecStrncpy.
From Kernel Require KernelInstrs KernelSyms.
Import Defs.
Local Open Scope Z_scope.

(* A copied prefix is extended by the byte just copied. *)
Lemma snc_copy_prefix_step (f h : nat -> bv 8) (d : nat) :
  (forall j, (j < d)%nat -> h j = f j) ->
  forall j, (j < S d)%nat -> bb_upd h d (f d) j = f j.
Proof.
  intros H j Hj. destruct (Nat.eq_dec j d) as [-> | Hne].
  - apply bb_upd_eq.
  - rewrite (bb_upd_ne h d _ j Hne). apply H. lia.
Qed.

Module StrncpyProof : STRNCPY.

Section MachineProof.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Ra6 := (mword_of_int 16 : mword 5).
  Notation Rz  := (mword_of_int 0 : mword 5).

  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.

  Local Ltac rgne :=
    rewrite rget_ne;
    [ | let H1 := fresh in let H2 := fresh in
        intro H1; injection H1 as H2; vm_compute in H2; congruence ].

  Local Lemma snc_cs_ne (k r : mword 5) :
    is_cs_idx k = false -> is_cs_idx r = true -> Regidx r <> Regidx k.
  Proof. intros Hk Hr He. symmetry in He. exact (is_cs_idx_true_neq k r Hk Hr He). Qed.

  Local Lemma snc_K_restore (K : nat) : (2 <= K)%nat -> ((K - 2) + 2)%nat = K.
  Proof. lia. Qed.

  Local Lemma snc_push (X : mword 64) :
    add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk X 2.
  Proof. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. Qed.

  Local Lemma snc_bump1 (q : mword 64) (j : nat) :
    add_vec (pa_add q j) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))
    = pa_add q (S j).
  Proof. apply pa_add_step. apply bv_eq; vm_compute; reflexivity. Qed.

  Local Lemma snc_back1 (q : mword 64) (j : nat) :
    add_vec (pa_add q (S j)) (sign_extend' 64 (mword_of_int 4095 : mword 12)) = pa_add q j.
  Proof. apply pa_add_back1. apply bv_eq; vm_compute; reflexivity. Qed.

  Local Lemma snc_sb_zero (M : regfile) :
    M !!! Regidx (mword_of_int 0 : mword 5) = zero_reg ->
    forall CID' : CpuId,
      trunc8 (rget (CID := CID') M (mword_of_int 0 : mword 5)) = (mword_of_int 0 : mword 8).
  Proof.
    intros Hx0 CID'. rgne. rewrite Hx0. apply bv_eq; vm_compute; reflexivity.
  Qed.

  (* The padding loop compares only the low 32 bits of its synthetic end
     cursor.  Thus the pointer base cancels even if either cursor wrapped in
     64 bits; [bc_subw_diff] is exactly that address-independent fact. *)
  Local Lemma snc_subw_rem (s endw : mword 64) (n k rem : nat) :
    (k + rem = n)%nat ->
    (Z.of_nat n < 2 ^ 31)%Z ->
    (subrange_vec_dec endw 31 0 : mword 32)
      = subrange_vec_dec (pa_add s n) 31 0 ->
    sign_extend' 64
      (sub_vec (subrange_vec_dec endw 31 0 : mword 32)
               (subrange_vec_dec (pa_add s k) 31 0 : mword 32))
      = (mword_of_int (Z.of_nat rem) : mword 64).
  Proof.
    intros Hsum Hn31 Hend. rewrite Hend.
    apply bc_subw_diff.
    - lia.
    - rewrite !pa_add_unsigned. rewrite bv_wrap_add_idemp_l.
      f_equal. lia.
  Qed.

  Local Lemma snc_bgtz_nat (r : nat) :
    (Z.of_nat r < 2 ^ 31)%Z ->
    zopz0zI_s zero_reg (mword_of_int (Z.of_nat r) : mword 64) = Nat.ltb 0 r.
  Proof.
    intro Hr. unfold zopz0zI_s.
    assert (Hz : sint (zero_reg : mword 64) = 0%Z) by (vm_compute; reflexivity).
    rewrite Hz (sint_moi_small (Z.of_nat r) ltac:(lia)).
    destruct r; reflexivity.
  Qed.

  Local Lemma snc_addiw_m1 (r : nat) : (0 < r)%nat -> (Z.of_nat r < 2 ^ 31)%Z ->
    sign_extend' 64 (subrange_vec_dec
      (add_vec (mword_of_int (Z.of_nat r) : mword 64)
               (sign_extend' 64 (mword_of_int 4095 : mword 12))) 31 0)
    = (mword_of_int (Z.of_nat (r - 1)) : mword 64).
  Proof.
    intros Hr H31.
    assert (Hsub : Z.of_nat (r - 1) = (Z.of_nat r - 1)%Z) by lia.
    apply bv_eq.
    cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
         to_word get_word MachineWord.MachineWord.sign_extend].
    rewrite bv_sign_extend_unsigned. change (MachineWord.MachineWord.Z_idx 64) with 64%N.
    unfold bv_signed. rewrite subrange_31_0_unsigned add_vec64_unsigned moi64_unsigned.
    assert (Hm1 : bv_unsigned (sign_extend' 64 (mword_of_int 4095 : mword 12) : mword 64)
                   = 18446744073709551615%Z) by (vm_compute; reflexivity).
    rewrite Hm1. unfold bv_wrap.
    change (bv_modulus 64) with 18446744073709551616%Z.
    change (bv_modulus 32) with 4294967296%Z.
    rewrite (Z.mod_small (Z.of_nat r) 18446744073709551616); [|lia].
    replace (Z.of_nat r + 18446744073709551615)%Z
      with ((Z.of_nat r - 1) + 1 * 18446744073709551616)%Z by lia.
    rewrite Z_mod_plus_full.
    rewrite (Z.mod_small (Z.of_nat r - 1) 18446744073709551616); [|lia].
    rewrite (Z.mod_small (Z.of_nat r - 1) 4294967296); [|lia].
    assert (Hhm : (bv_half_modulus 32 = 2147483648)%Z) by (vm_compute; reflexivity).
    rewrite bv_swrap_small; [| rewrite Hhm; lia].
    rewrite moi64_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616%Z.
    rewrite Hsub.
    rewrite Z.mod_small; [reflexivity|lia].
  Qed.

  Local Lemma snc_bgez_count (r : nat) :
    (Z.of_nat r < 2 ^ 31)%Z ->
    zopz0zKzJ_s (zero_reg : mword 64) (mword_of_int (Z.of_nat r) : mword 64)
      = Nat.eqb r 0.
  Proof.
    intro Hr. unfold zopz0zKzJ_s.
    assert (Hz : sint (zero_reg : mword 64) = 0%Z) by (vm_compute; reflexivity).
    rewrite Hz (sint_moi_small (Z.of_nat r) ltac:(lia)).
    destruct r; reflexivity.
  Qed.

  (* [+0x2c c.addw; +0x2e c.addiw -1] computes an end marker whose
     low word is the low word of [s+n].  Only that low word is subsequently
     consumed by [subw], so no representation condition on [s] is needed. *)
  Local Lemma snc_padding_end_low (s : mword 64) (n d rem : nat) :
    (d + S rem = n)%nat ->
    let w1 := sign_extend' 64
      (add_vec (subrange_vec_dec (pa_add s (S d)) 31 0 : mword 32)
               (subrange_vec_dec (mword_of_int (Z.of_nat (S rem)) : mword 64) 31 0)) in
    let w2 := sign_extend' 64
      (subrange_vec_dec
        (add_vec w1
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0) in
    (subrange_vec_dec w2 31 0 : mword 32)
      = subrange_vec_dec (pa_add s n) 31 0.
  Proof.
    intros Hsum. cbn zeta.
    assert (Hm1 : trunc32
        (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))
        = trunc32 (mword_of_int (-1) : mword 64)).
    { apply bv_eq; vm_compute; reflexivity. }
    assert (Haddr :
      add_vec
        (add_vec (pa_add s (S d))
                 (mword_of_int (Z.of_nat (S rem)) : mword 64))
        (mword_of_int (-1) : mword 64)
      = pa_add s n).
    { rewrite pa_add_bump.
      replace (S d + S rem)%nat with (S n) by lia.
      apply pa_add_back1. apply bv_eq; vm_compute; reflexivity. }
    rewrite <- !trunc32_subrange.
    rewrite !trunc32_sext !trunc32_add Hm1.
    rewrite trunc32_sext.
    rewrite -!trunc32_add Haddr. reflexivity.
  Qed.

  (* The common 2-slot leaf epilogue, reached after either loop terminates. *)
  Local Lemma snc_tail `{CID0 : CpuId}
      (mm Mt : regfile) (K : nat) (rv sp0 ra0 s00 : mword 64) (b : bool) (p : mword 64) :
    (2 <= K)%nat ->
    mm !!! Regidx csp_rs1 = sp0 ->
    mm !!! Regidx Rra = ra0 ->
    mm !!! Regidx Rs0 = s00 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 2 ->
    Mt !!! Regidx Ra0 = rv ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
        Mt !!! Regidx r = mm !!! Regidx r) ->
    sie_cap_gpr KT1 (CID := CID0) Mt (K - 2)%nat b p -∗
    kernel_text -∗
    pc_is (CID := CID0) (mword_of_int (KernelSyms.strncpy + 0x3e) : mword 64) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    wp_next (CID0 := CID0) b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved mm mf /\ mf !!! Regidx Ra0 = rv⌝ -∗
        sie_cap_gpr KT1 mf K b p -∗ pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp0 Hra0 Hs00 Hmtsp Hmta0 Hthr.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hcont".
    iPoseProof (sncp_3e with "Htext") as "Hi3e".
    iPoseProof (sncp_40 with "Htext") as "Hi40".
    iPoseProof (sncp_42 with "Htext") as "Hi42".
    iPoseProof (sncp_44 with "Htext") as "Hi44".
    assert (Hpa1 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                   = pa_stk sp0 1).
    { rewrite Hmtsp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (KernelSyms.strncpy + 0x3e))
              (mword_of_int 1 : mword 6) Rra Mt (K - 2)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3e Hb1").
    iIntros (CID1 Hs1) "Hcg Hpc Hb1". iEval (rewrite Hpa1) in "Hb1".
    set (T1 := <[Regidx Rra := regval_into_reg ra0]> Mt).
    assert (Hp40 : add_vec_int (mword_of_int (KernelSyms.strncpy + 0x3e) : mword 64) 2
                   = mword_of_int (KernelSyms.strncpy + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp40) in "Hpc".
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /T1 upd_ne; [exact Hmtsp | reg_neq]).
    assert (Hpa2 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                   = pa_stk sp0 2).
    { rewrite HT1sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_cldsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (KernelSyms.strncpy + 0x40))
              (mword_of_int 0 : mword 6) Rs0 T1 (K - 2)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi40 Hb2").
    iIntros (CID2 Hs2) "Hcg Hpc Hb2". iEval (rewrite Hpa2) in "Hb2".
    set (T2 := <[Regidx Rs0 := regval_into_reg s00]> T1).
    assert (Hp42 : add_vec_int (mword_of_int (KernelSyms.strncpy + 0x40) : mword 64) 2
                   = mword_of_int (KernelSyms.strncpy + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp42) in "Hpc".
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /T2 upd_ne; [exact HT1sp | reg_neq]).
    assert (Hwv : add_vec (T2 !!! Regidx csp_rs1)
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0)
      by (rewrite HT2sp; apply stk_pop_16).
    assert (Hpop : T2 !!! Regidx csp_rs1 = pa_stk (add_vec (T2 !!! Regidx csp_rs1)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2)
      by (rewrite Hwv; exact HT2sp).
    iDestruct (stack_own_2_intro sp0 ra0 s00 with "Hb1 Hb2") as "Hframe".
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.strncpy + 0x42))
              (mword_of_int 16 : mword 6) T2 (K - 2)%nat 2 b Hpop
              with "Hcg Hpc Hi42 Hframe").
    iIntros (CID3 Hs3) "Hcg Hpc".
    pose proof (snc_K_restore K HK) as Hnk. iEval (rewrite Hnk) in "Hcg".
    set (T3 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (T2 !!! Regidx csp_rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> T2).
    assert (Hp44 : add_vec_int (mword_of_int (KernelSyms.strncpy + 0x42) : mword 64) 2
                   = mword_of_int (KernelSyms.strncpy + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp44) in "Hpc".
    assert (HT3ra : T3 !!! Regidx Rra = ra0).
    { rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_eq. reflexivity. }
    assert (HT3ra' : forall CID' : CpuId, rget (CID := CID') T3 Rra = ra0)
      by (intros CID'; rgne; exact HT3ra).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.strncpy + 0x44)) Rra T3 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi44").
    iIntros (CID4 Hs4) "Hcg Hpc". iEval (rewrite HT3ra') in "Hpc".
    assert (HT3a0 : T3 !!! Regidx Ra0 = rv).
    { rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_ne; [| reg_neq]. exact Hmta0. }
    assert (Hgen : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                     T3 !!! Regidx r = mm !!! Regidx r).
    { intros r Hr Ncsp Ns0.
      rewrite /T3 upd_ne; [| intro He; injection He as He'; congruence].
      rewrite /T2 upd_ne; [| intro He; injection He as He'; congruence].
      rewrite /T1 upd_ne; [| apply snc_cs_ne; [vm_compute; reflexivity | exact Hr]].
      apply Hthr; assumption. }
    iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! T3 with "[%] Hcg Hpc"). split; [| exact HT3a0].
    unfold callee_saved. split_and!.
    - rewrite /T3 upd_eq Hwv. symmetry. exact Hsp0.
    - rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_eq. symmetry. exact Hs00.
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
  Qed.

(* Updating the current byte cannot disturb either part of the copy-loop
   invariant: the completed prefix or the still-untouched suffix. *)
Lemma snc_copy_suffix_step (g h : nat -> bv 8) (d : nat) (v : bv 8) :
  (forall j, (d <= j)%nat -> h j = g j) ->
  forall j, (S d <= j)%nat -> bb_upd h d v j = g j.
Proof.
  intros H j Hj. rewrite (bb_upd_ne h d v j ltac:(lia)). apply H. lia.
Qed.

(* One padding store extends a zero-filled suffix by precisely its current
   cursor index. *)
Lemma snc_pad_suffix_step (h : nat -> bv 8) (n k : nat) :
  (forall j, (S k <= j)%nat -> (j < n)%nat -> h j = (mword_of_int 0 : mword 8)) ->
  forall j, (k <= j)%nat -> (j < n)%nat ->
    bb_upd h k (mword_of_int 0 : mword 8) j = (mword_of_int 0 : mword 8).
Proof.
  intros H j Hkj Hjn. destruct (Nat.eq_dec j k) as [-> | Hne].
  - apply bb_upd_eq.
  - rewrite (bb_upd_ne h k _ j Hne). apply H; lia.
Qed.

(* The copied prefix remains intact while the padding loop changes only the
   suffix. *)
Lemma snc_pad_prefix_preserved (f h : nat -> bv 8) (k d : nat) :
  (d <= k)%nat ->
  (forall j, (j < d)%nat -> h j = f j) ->
  forall j, (j < d)%nat ->
    bb_upd h k (mword_of_int 0 : mword 8) j = f j.
Proof.
  intros Hdk Hcopy j Hj. rewrite (bb_upd_ne h k _ j ltac:(lia)). apply Hcopy; exact Hj.
Qed.

Lemma snc_pad_extend (h : nat -> bv 8) (k0 k : nat) :
  (forall j, (k0 <= j)%nat -> (j < k)%nat -> h j = (mword_of_int 0 : mword 8)) ->
  forall j, (k0 <= j)%nat -> (j < S k)%nat ->
    bb_upd h k (mword_of_int 0 : mword 8) j = (mword_of_int 0 : mword 8).
Proof.
  intros H j Hj0 Hjk. destruct (Nat.eq_dec j k) as [-> | Hne].
  - apply bb_upd_eq.
  - rewrite (bb_upd_ne h k _ j Hne). apply H; lia.
Qed.

(* The no-NUL exit has copied the entire range. *)
Lemma snc_post_full (f h : nat -> bv 8) (n : nat) :
  bb_nonul f n ->
  (forall j, (j < n)%nat -> h j = f j) ->
  snc_post f h n.
Proof. intros Hnz Hcopy. left. split; assumption. Qed.

(* Once the first NUL at [k] has been copied, the padding loop writes zero
   throughout its suffix.  This is the exact pure fact consumed by the final
   continuation of the machine proof. *)
Lemma snc_post_padded (f h : nat -> bv 8) (n k : nat) :
  (k < n)%nat -> bb_cstr f k ->
  (forall j, (j < k)%nat -> h j = f j) ->
  (forall j, (k <= j)%nat -> (j < n)%nat -> h j = (mword_of_int 0 : mword 8)) ->
  snc_post f h n.
Proof.
  intros Hkn Hstr Hcopy Hzero. right. exists k.
  split; [exact Hkn |]. split; [exact Hstr |]. split; assumption.
Qed.

  (* The second loop writes one NUL per iteration.  [k] is the next index
     to fill and [rem] its fuel; [endw] is gcc's 32-bit synthetic end cursor,
     whose low word is all the signed [subw] comparison observes. *)
  Local Lemma snc_pad_loop
      (mm : regfile) (n k0 : nat) (f : nat -> bv 8) (K : nat) (dq : dfrac)
      (t s sp0 endw : mword 64) (b : bool) (p : mword 64) (CIDh : CpuId) :
    (k0 < n)%nat -> bb_cstr f k0 -> (Z.of_nat n < 2 ^ 31)%Z ->
    (subrange_vec_dec endw 31 0 : mword 32)
      = subrange_vec_dec (pa_add s n) 31 0 ->
    forall (rem k : nat) (h : nat -> bv 8) (M : regfile) (CID0 : CpuId),
    (b = false \/ p = zero_reg -> (CID0 : CPU) = (CIDh : CPU)) ->
    (0 < rem)%nat -> (k + rem = n)%nat -> (k0 <= k)%nat ->
    (forall j, (j < k0)%nat -> h j = f j) ->
    (forall j, (k0 <= j)%nat -> (j < k)%nat -> h j = (mword_of_int 0 : mword 8)) ->
    M !!! Regidx csp_rs1 = pa_stk sp0 2 ->
    M !!! Regidx Ra0 = s -> M !!! Regidx Ra4 = pa_add s k -> M !!! Regidx Ra5 = endw ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
        M !!! Regidx r = mm !!! Regidx r) ->
    sie_cap_gpr KT1 (CID := CID0) M (K - 2)%nat b p -∗ kernel_text -∗
    pc_is (CID := CID0) (mword_of_int (KernelSyms.strncpy + 0x30) : mword 64) -∗
    ([∗ list] j ∈ seq 0 n, (pa_add t j) ↦ₘ[KT1]{dq} f j) -∗
    ([∗ list] j ∈ seq 0 n, (pa_add s j) ↦ₘ[KT1] h j) -∗
    wp_next (CID0 := CIDh) b p (fun (CID : CpuId) =>
      ∀ (Mt : regfile) (hf : nat -> bv 8),
        ⌜snc_post f hf n⌝ -∗
        ⌜Mt !!! Regidx csp_rs1 = pa_stk sp0 2⌝ -∗
        ⌜Mt !!! Regidx Ra0 = s⌝ -∗
        ⌜forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
            Mt !!! Regidx r = mm !!! Regidx r⌝ -∗
        sie_cap_gpr KT1 Mt (K - 2)%nat b p -∗
        pc_is (mword_of_int (KernelSyms.strncpy + 0x3e) : mword 64) -∗
        ([∗ list] j ∈ seq 0 n, (pa_add t j) ↦ₘ[KT1]{dq} f j) -∗
        ([∗ list] j ∈ seq 0 n, (pa_add s j) ↦ₘ[KT1] hf j) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hk0n Hcstr Hn31 Hend rem.
    induction rem as [|rem IH]; intros k h M CID0 Hchain Hpos Hsum Hk0k Hcopy Hzero
      Hsp Ha0 Ha4 Ha5 Hthr; [lia|].
    iIntros "Hcg #Htext Hpc Hsrc Hdst Hcont".
    iPoseProof (sncp_30 with "Htext") as "Hi30".
    assert (Ha4' : forall CID' : CpuId, rget (CID := CID') M Ra4 = pa_add s k)
      by (intros CID'; rgne; exact Ha4).
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.strncpy + 0x30)) Ra4
              (mword_of_int 1 : mword 6) M (K - 2)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi30").
    iIntros (CID1 Hs1) "Hcg Hpc".
    iEval (rewrite (Ha4' _) (snc_bump1 s k)) in "Hcg".
    set (P1 := <[Regidx Ra4 := regval_into_reg (pa_add s (S k))]> M).
    assert (HP1a4 : P1 !!! Regidx Ra4 = pa_add s (S k)) by (rewrite /P1 upd_eq; reflexivity).
    assert (HP1a4' : forall CID' : CpuId, rget (CID := CID') P1 Ra4 = pa_add s (S k))
      by (intros CID'; rgne; exact HP1a4).
    assert (HP1a5 : P1 !!! Regidx Ra5 = endw) by (rewrite /P1 upd_ne; [exact Ha5 | reg_neq]).
    assert (HP1a5' : forall CID' : CpuId, rget (CID := CID') P1 Ra5 = endw)
      by (intros CID'; rgne; exact HP1a5).
    assert (HP1sp : P1 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /P1 upd_ne; [exact Hsp | reg_neq]).
    assert (HP1a0 : P1 !!! Regidx Ra0 = s) by (rewrite /P1 upd_ne; [exact Ha0 | reg_neq]).
    assert (HP1thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                         P1 !!! Regidx r = mm !!! Regidx r).
    { intros r Hr Ncsp Ns0. rewrite /P1 upd_ne;
        [apply Hthr; assumption|apply snc_cs_ne; [vm_compute; reflexivity|exact Hr]]. }
    assert (Hklt : (k < n)%nat) by lia.
    assert (Hp32 : add_vec_int (mword_of_int (KernelSyms.strncpy + 0x30) : mword 64) 2
                   = mword_of_int (KernelSyms.strncpy + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp32) in "Hpc".
    iPoseProof (sncp_32 with "Htext") as "Hi32".
    iDestruct (bb_byte_acc s n k h (DfracOwn 1) Hklt with "Hdst") as "[Hdb Hdback]".
    iDestruct (sie_cap_gpr_x0 P1 (K - 2)%nat b p Rz
                 ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx0 Hcg]".
    iApply (wp_sb_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (KernelSyms.strncpy + 0x32)) Rz Ra4
              (mword_of_int 4095 : mword 12) P1 (K - 2)%nat (h k) b
              with "Hcg Hpc Hi32 [Hdb]").
    { iEval (rewrite (HP1a4' _) (snc_back1 s k)). iExact "Hdb". }
    iIntros (CID2 Hs2) "Hcg Hpc Hdb".
    iEval (rewrite (HP1a4' _) (snc_back1 s k)) in "Hdb".
    iEval (rewrite (snc_sb_zero P1 Hx0 _)) in "Hdb".
    iDestruct ("Hdback" $! (bb_upd h k (mword_of_int 0 : mword 8)) with "[%] [Hdb]") as "Hdst".
    { intros j Hj Hne. apply bb_upd_ne; exact Hne. }
    { iEval (rewrite bb_upd_eq). iExact "Hdb". }
    set (h' := bb_upd h k (mword_of_int 0 : mword 8)).
    assert (Hcopy' : forall j, (j < k0)%nat -> h' j = f j).
    { apply snc_pad_prefix_preserved; assumption. }
    assert (Hzero' : forall j, (k0 <= j)%nat -> (j < S k)%nat ->
                       h' j = (mword_of_int 0 : mword 8)).
    { apply snc_pad_extend; exact Hzero. }
    assert (Hp36 : add_vec_int (mword_of_int (KernelSyms.strncpy + 0x32) : mword 64) 4
                   = mword_of_int (KernelSyms.strncpy + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp36) in "Hpc".
    iPoseProof (sncp_36 with "Htext") as "Hi36".
    destruct rem as [|rem'].
    - (* one byte remained; the subtraction produces zero and the branch falls through *)
      assert (Hsub0 : sign_extend' 64
          (sub_vec (subrange_vec_dec endw 31 0 : mword 32)
                   (subrange_vec_dec (pa_add s (S k)) 31 0 : mword 32))
          = (mword_of_int 0 : mword 64)).
      { apply (snc_subw_rem s endw n (S k) 0); [lia|exact Hn31|exact Hend]. }
      iApply (wp_subw_s_sconf (mword_of_int (KernelSyms.strncpy + 0x36)) Ra3 Ra5 Ra4
                P1 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi36").
      iIntros (CID3 Hs3) "Hcg Hpc".
      iEval (rewrite (HP1a5' _) (HP1a4' _) Hsub0) in "Hcg".
      set (P2 := <[Regidx Ra3 := regval_into_reg (mword_of_int 0 : mword 64)]> P1).
      assert (Hp3a : add_vec_int (mword_of_int (KernelSyms.strncpy + 0x36) : mword 64) 4
                     = mword_of_int (KernelSyms.strncpy + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp3a) in "Hpc". iPoseProof (sncp_3a with "Htext") as "Hi3a".
      iApply (wp_bgtz_fall_s_sconf (mword_of_int (KernelSyms.strncpy + 0x3a))
                (mword_of_int 8182 : mword 13) Ra3 P2 (K - 2)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite /P2 upd_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi3a").
      iIntros (CID4 Hs4) "Hcg Hpc".
      assert (Hp3e : add_vec_int (mword_of_int (KernelSyms.strncpy + 0x3a) : mword 64) 4
                     = mword_of_int (KernelSyms.strncpy + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp3e) in "Hpc".
      assert (HP2sp : P2 !!! Regidx csp_rs1 = pa_stk sp0 2)
        by (rewrite /P2 upd_ne; [exact HP1sp|reg_neq]).
      assert (HP2a0 : P2 !!! Regidx Ra0 = s) by (rewrite /P2 upd_ne; [exact HP1a0|reg_neq]).
      assert (HP2thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                           P2 !!! Regidx r = mm !!! Regidx r).
      { intros r Hr Ncsp Ns0. rewrite /P2 upd_ne;
          [apply HP1thr; assumption|apply snc_cs_ne; [vm_compute; reflexivity|exact Hr]]. }
      assert (Hpost : snc_post f h' n).
      { apply snc_post_padded with (k:=k0); [exact Hk0n|exact Hcstr|exact Hcopy'|].
        intros j Hj0 Hjn. apply Hzero'; [exact Hj0|lia]. }
      iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! P2 h' with "[%] [%] [%] [%] Hcg Hpc Hsrc Hdst"); assumption.
    - (* at least two remained; the positive difference takes the back edge *)
      assert (HsubS : sign_extend' 64
          (sub_vec (subrange_vec_dec endw 31 0 : mword 32)
                   (subrange_vec_dec (pa_add s (S k)) 31 0 : mword 32))
          = (mword_of_int (Z.of_nat (S rem')) : mword 64)).
      { apply (snc_subw_rem s endw n (S k) (S rem')); [lia|exact Hn31|exact Hend]. }
      iApply (wp_subw_s_sconf (mword_of_int (KernelSyms.strncpy + 0x36)) Ra3 Ra5 Ra4
                P1 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi36").
      iIntros (CID3 Hs3) "Hcg Hpc".
      iEval (rewrite (HP1a5' _) (HP1a4' _) HsubS) in "Hcg".
      set (P2 := <[Regidx Ra3 := regval_into_reg
                    (mword_of_int (Z.of_nat (S rem')) : mword 64)]> P1).
      assert (Hp3a : add_vec_int (mword_of_int (KernelSyms.strncpy + 0x36) : mword 64) 4
                     = mword_of_int (KernelSyms.strncpy + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp3a) in "Hpc". iPoseProof (sncp_3a with "Htext") as "Hi3a".
      iApply (wp_bgtz_taken_s_sconf (mword_of_int (KernelSyms.strncpy + 0x3a))
                (mword_of_int 8182 : mword 13) Ra3 P2 (K - 2)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite /P2 upd_eq (snc_bgtz_nat (S rem') ltac:(lia)); reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi3a").
      iNext. iIntros (CID4 Hs4) "Hcg Hpc".
      assert (Hback : add_vec (mword_of_int (KernelSyms.strncpy + 0x3a) : mword 64)
                       (sign_extend' 64 (mword_of_int 8182 : mword 13))
                     = mword_of_int (KernelSyms.strncpy + 0x30))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hback) in "Hpc".
      assert (HP2sp : P2 !!! Regidx csp_rs1 = pa_stk sp0 2)
        by (rewrite /P2 upd_ne; [exact HP1sp|reg_neq]).
      assert (HP2a0 : P2 !!! Regidx Ra0 = s) by (rewrite /P2 upd_ne; [exact HP1a0|reg_neq]).
      assert (HP2a4 : P2 !!! Regidx Ra4 = pa_add s (S k))
        by (rewrite /P2 upd_ne; [exact HP1a4|reg_neq]).
      assert (HP2a5 : P2 !!! Regidx Ra5 = endw)
        by (rewrite /P2 upd_ne; [exact HP1a5|reg_neq]).
      assert (HP2thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                           P2 !!! Regidx r = mm !!! Regidx r).
      { intros r Hr Ncsp Ns0. rewrite /P2 upd_ne;
          [apply HP1thr; assumption|apply snc_cs_ne; [vm_compute; reflexivity|exact Hr]]. }
      assert (Hchain' : b = false \/ p = zero_reg -> (CID4 : CPU) = (CIDh : CPU)) by wp_next_chain.
      iApply (IH (S k) h' P2 CID4 Hchain' ltac:(lia) ltac:(lia) ltac:(lia)
                Hcopy' Hzero' HP2sp HP2a0 HP2a4 HP2a5 HP2thr
                with "Hcg Htext Hpc Hsrc Hdst Hcont").
  Qed.

  (* The first loop copies bytes until either [rem] is exhausted or the
     first NUL is observed.  The latter arm either exits immediately (NUL was
     the last byte) or enters [snc_pad_loop] for the remaining suffix. *)
  Local Lemma snc_copy_loop
      (mm : regfile) (n : nat) (f g : nat -> bv 8) (K : nat) (dq : dfrac)
      (t s sp0 : mword 64) (b : bool) (p : mword 64) (CIDh : CpuId) :
    (Z.of_nat n < 2 ^ 31)%Z ->
    forall (rem d : nat) (h : nat -> bv 8) (M : regfile) (CID0 : CpuId),
    (b = false \/ p = zero_reg -> (CID0 : CPU) = (CIDh : CPU)) ->
    (d + rem = n)%nat ->
    (forall j, (j < d)%nat -> h j = f j) ->
    (forall j, (d <= j)%nat -> h j = g j) ->
    bb_nonul f d ->
    M !!! Regidx csp_rs1 = pa_stk sp0 2 -> M !!! Regidx Ra0 = s ->
    M !!! Regidx Ra1 = pa_add t d ->
    M !!! Regidx Ra2 = (mword_of_int (Z.of_nat rem) : mword 64) ->
    M !!! Regidx Ra5 = pa_add s d ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
        M !!! Regidx r = mm !!! Regidx r) ->
    sie_cap_gpr KT1 (CID := CID0) M (K - 2)%nat b p -∗ kernel_text -∗
    pc_is (CID := CID0) (mword_of_int (KernelSyms.strncpy + 0x0e) : mword 64) -∗
    ([∗ list] j ∈ seq 0 n, (pa_add t j) ↦ₘ[KT1]{dq} f j) -∗
    ([∗ list] j ∈ seq 0 n, (pa_add s j) ↦ₘ[KT1] h j) -∗
    wp_next (CID0 := CIDh) b p (fun (CID : CpuId) =>
      ∀ (Mt : regfile) (hf : nat -> bv 8),
        ⌜snc_post f hf n⌝ -∗
        ⌜Mt !!! Regidx csp_rs1 = pa_stk sp0 2⌝ -∗
        ⌜Mt !!! Regidx Ra0 = s⌝ -∗
        ⌜forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
            Mt !!! Regidx r = mm !!! Regidx r⌝ -∗
        sie_cap_gpr KT1 Mt (K - 2)%nat b p -∗
        pc_is (mword_of_int (KernelSyms.strncpy + 0x3e) : mword 64) -∗
        ([∗ list] j ∈ seq 0 n, (pa_add t j) ↦ₘ[KT1]{dq} f j) -∗
        ([∗ list] j ∈ seq 0 n, (pa_add s j) ↦ₘ[KT1] hf j) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn31 rem. induction rem as [|rem IH];
      intros d h M CID0 Hchain Hsum Hcopy Hunt Hnn Hsp Ha0 Ha1 Ha2 Ha5 Hthr;
      iIntros "Hcg #Htext Hpc Hsrc Hdst Hcont".
    - (* count exhausted: the whole range was copied without a NUL *)
      iPoseProof (sncp_0e with "Htext") as "Hi0e".
      assert (Ha2' : forall CID' : CpuId, rget (CID := CID') M Ra2 = (mword_of_int 0 : mword 64))
        by (intros CID'; rgne; exact Ha2).
      iApply (wp_bge_x0_taken_s_sconf (mword_of_int (KernelSyms.strncpy + 0x0e))
                (mword_of_int 48 : mword 13) Ra2 M (K - 2)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Ha2' _); vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi0e").
      iNext. iIntros (CID1 Hs1) "Hcg Hpc".
      assert (Hpc3e : add_vec (mword_of_int (KernelSyms.strncpy + 0x0e) : mword 64)
                       (sign_extend' 64 (mword_of_int 48 : mword 13))
                     = mword_of_int (KernelSyms.strncpy + 0x3e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc3e) in "Hpc".
      assert (Hd : d = n) by lia.
      assert (Hpost : snc_post f h n).
      { apply snc_post_full; [rewrite -Hd; exact Hnn|]. intros j Hj. apply Hcopy; lia. }
      iSpecialize ("Hcont" $! CID1 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! M h with "[%] [%] [%] [%] Hcg Hpc Hsrc Hdst"); assumption.
    - (* a byte remains: decrement the int count, copy it, then inspect it *)
      iPoseProof (sncp_0e with "Htext") as "Hi0e".
      assert (Hrem31 : (Z.of_nat (S rem) < 2 ^ 31)%Z) by lia.
      assert (Ha2' : forall CID' : CpuId,
                 rget (CID := CID') M Ra2 = (mword_of_int (Z.of_nat (S rem)) : mword 64))
        by (intros CID'; rgne; exact Ha2).
      iApply (wp_bge_x0_fall_s_sconf (mword_of_int (KernelSyms.strncpy + 0x0e))
                (mword_of_int 48 : mword 13) Ra2 M (K - 2)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (Ha2' _) (snc_bgez_count (S rem) Hrem31); reflexivity)
                with "Hcg Hpc Hi0e").
      iIntros (CID1 Hs1) "Hcg Hpc".
      assert (Hp12 : add_vec_int (mword_of_int (KernelSyms.strncpy + 0x0e) : mword 64) 4
                     = mword_of_int (KernelSyms.strncpy + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp12) in "Hpc". iPoseProof (sncp_12 with "Htext") as "Hi12".
      iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.strncpy + 0x12)) Ra3 Ra2
                (mword_of_int 4095 : mword 12) M (K - 2)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi12").
      iIntros (CID2 Hs2) "Hcg Hpc".
      iEval (rewrite (Ha2' _)) in "Hcg".
      pose proof (snc_addiw_m1 (S rem) ltac:(lia) Hrem31) as Hdec.
      replace (S rem - 1)%nat with rem in Hdec by lia.
      iEval (rewrite Hdec) in "Hcg".
      set (C1 := <[Regidx Ra3 := regval_into_reg
                    (mword_of_int (Z.of_nat rem) : mword 64)]> M).
      assert (HC1a3 : C1 !!! Regidx Ra3 = (mword_of_int (Z.of_nat rem) : mword 64))
        by (rewrite /C1 upd_eq; reflexivity).
      assert (HC1a3' : forall CID' : CpuId, rget (CID := CID') C1 Ra3 =
                    (mword_of_int (Z.of_nat rem) : mword 64))
        by (intros CID'; rgne; exact HC1a3).
      assert (Hp16 : add_vec_int (mword_of_int (KernelSyms.strncpy + 0x12) : mword 64) 4
                     = mword_of_int (KernelSyms.strncpy + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp16) in "Hpc". iPoseProof (sncp_16 with "Htext") as "Hi16".
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.strncpy + 0x16)) Ra6 Ra3 C1
                (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi16").
      iIntros (CID3 Hs3) "Hcg Hpc".
      iEval (rewrite (HC1a3' _) add_vec_zero_l) in "Hcg".
      set (C2 := <[Regidx Ra6 := regval_into_reg
                    (mword_of_int (Z.of_nat rem) : mword 64)]> C1).
      assert (Hp18 : add_vec_int (mword_of_int (KernelSyms.strncpy + 0x16) : mword 64) 2
                     = mword_of_int (KernelSyms.strncpy + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp18) in "Hpc". iPoseProof (sncp_18 with "Htext") as "Hi18".
      assert (HC2a5 : C2 !!! Regidx Ra5 = pa_add s d).
      { rewrite /C2 upd_ne; [rewrite /C1 upd_ne; [exact Ha5|reg_neq]|reg_neq]. }
      assert (HC2a5' : forall CID' : CpuId, rget (CID := CID') C2 Ra5 = pa_add s d)
        by (intros CID'; rgne; exact HC2a5).
      iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.strncpy + 0x18)) Ra5
                (mword_of_int 1 : mword 6) C2 (K - 2)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi18").
      iIntros (CID4 Hs4) "Hcg Hpc".
      iEval (rewrite (HC2a5' _) (snc_bump1 s d)) in "Hcg".
      set (C3 := <[Regidx Ra5 := regval_into_reg (pa_add s (S d))]> C2).
      assert (HC3a5 : C3 !!! Regidx Ra5 = pa_add s (S d)) by (rewrite /C3 upd_eq; reflexivity).
      assert (HC3a5' : forall CID' : CpuId, rget (CID := CID') C3 Ra5 = pa_add s (S d))
        by (intros CID'; rgne; exact HC3a5).
      assert (HC3a1 : C3 !!! Regidx Ra1 = pa_add t d).
      { rewrite /C3 upd_ne; [rewrite /C2 upd_ne; [rewrite /C1 upd_ne; [exact Ha1|reg_neq]|reg_neq]|reg_neq]. }
      assert (HC3a1' : forall CID' : CpuId, rget (CID := CID') C3 Ra1 = pa_add t d)
        by (intros CID'; rgne; exact HC3a1).
      assert (Hdlt : (d < n)%nat) by lia.
      assert (Hp1a : add_vec_int (mword_of_int (KernelSyms.strncpy + 0x18) : mword 64) 2
                     = mword_of_int (KernelSyms.strncpy + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp1a) in "Hpc". iPoseProof (sncp_1a with "Htext") as "Hi1a".
      iDestruct (bb_byte_acc t n d f dq Hdlt with "Hsrc") as "[Hsb Hsback]".
      iApply (wp_lbu_s_sconf (mword_of_int (KernelSyms.strncpy + 0x1a)) Ra4 Ra1
                (mword_of_int 0 : mword 12) C3 (K - 2)%nat (f d : mword 8) b (dqm:=dq)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi1a [Hsb]").
      { iEval (rewrite (HC3a1' _) addv_sext0). iExact "Hsb". }
      iIntros (CID5 Hs5) "Hcg Hpc Hsb".
      iEval (rewrite (HC3a1' _) addv_sext0) in "Hsb".
      iDestruct ("Hsback" $! f with "[%] Hsb") as "Hsrc"; [done|].
      set (C4 := <[Regidx Ra4 := regval_into_reg (zero_extend' 64 (f d : mword 8))]> C3).
      assert (HC4a4 : C4 !!! Regidx Ra4 = zero_extend' 64 (f d : mword 8))
        by (rewrite /C4 upd_eq; reflexivity).
      assert (HC4a4' : forall CID' : CpuId, rget (CID := CID') C4 Ra4 =
                    zero_extend' 64 (f d : mword 8))
        by (intros CID'; rgne; exact HC4a4).
      assert (HC4a5 : C4 !!! Regidx Ra5 = pa_add s (S d))
        by (rewrite /C4 upd_ne; [exact HC3a5|reg_neq]).
      assert (HC4a5' : forall CID' : CpuId, rget (CID := CID') C4 Ra5 = pa_add s (S d))
        by (intros CID'; rgne; exact HC4a5).
      assert (Hp1e : add_vec_int (mword_of_int (KernelSyms.strncpy + 0x1a) : mword 64) 4
                     = mword_of_int (KernelSyms.strncpy + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp1e) in "Hpc". iPoseProof (sncp_1e with "Htext") as "Hi1e".
      iDestruct (bb_byte_acc s n d h (DfracOwn 1) Hdlt with "Hdst") as "[Hdb Hdback]".
      iApply (wp_sb_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (KernelSyms.strncpy + 0x1e)) Ra4 Ra5
                (mword_of_int 4095 : mword 12) C4 (K - 2)%nat (h d) b
                with "Hcg Hpc Hi1e [Hdb]").
      { iEval (rewrite (HC4a5' _) (snc_back1 s d)). iExact "Hdb". }
      iIntros (CID6 Hs6) "Hcg Hpc Hdb".
      iEval (rewrite (HC4a5' _) (snc_back1 s d)) in "Hdb".
      iEval (rewrite (HC4a4' _) trunc8_zext8) in "Hdb".
      iDestruct ("Hdback" $! (bb_upd h d (f d)) with "[%] [Hdb]") as "Hdst".
      { intros j Hj Hne. apply bb_upd_ne; exact Hne. }
      { iEval (rewrite bb_upd_eq). iExact "Hdb". }
      set (h' := bb_upd h d (f d)).
      assert (Hcopy' : forall j, (j < S d)%nat -> h' j = f j)
        by (apply snc_copy_prefix_step; exact Hcopy).
      assert (Hunt' : forall j, (S d <= j)%nat -> h' j = g j)
        by (apply snc_copy_suffix_step; exact Hunt).
      assert (Hp22 : add_vec_int (mword_of_int (KernelSyms.strncpy + 0x1e) : mword 64) 4
                     = mword_of_int (KernelSyms.strncpy + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp22) in "Hpc". iPoseProof (sncp_22 with "Htext") as "Hi22".
      assert (HC4a1 : C4 !!! Regidx Ra1 = pa_add t d) by (rewrite /C4 upd_ne; [exact HC3a1|reg_neq]).
      assert (HC4a1' : forall CID' : CpuId, rget (CID := CID') C4 Ra1 = pa_add t d)
        by (intros CID'; rgne; exact HC4a1).
      iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.strncpy + 0x22)) Ra1
                (mword_of_int 1 : mword 6) C4 (K - 2)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi22").
      iIntros (CID7 Hs7) "Hcg Hpc".
      iEval (rewrite (HC4a1' _) (snc_bump1 t d)) in "Hcg".
      set (C5 := <[Regidx Ra1 := regval_into_reg (pa_add t (S d))]> C4).
      assert (HC5a1 : C5 !!! Regidx Ra1 = pa_add t (S d))
        by (rewrite /C5 upd_eq; reflexivity).
      assert (HC5a3 : C5 !!! Regidx Ra3 = (mword_of_int (Z.of_nat rem) : mword 64)).
      { rewrite /C5 upd_ne; [|reg_neq]. rewrite /C4 upd_ne; [|reg_neq].
        rewrite /C3 upd_ne; [|reg_neq]. rewrite /C2 upd_ne; [exact HC1a3|reg_neq]. }
      assert (HC5a4 : C5 !!! Regidx Ra4 = zero_extend' 64 (f d : mword 8))
        by (rewrite /C5 upd_ne; [exact HC4a4|reg_neq]).
      assert (HC5a5 : C5 !!! Regidx Ra5 = pa_add s (S d))
        by (rewrite /C5 upd_ne; [exact HC4a5|reg_neq]).
      assert (HC5a6 : C5 !!! Regidx Ra6 = (mword_of_int (Z.of_nat rem) : mword 64)).
      { rewrite /C5 upd_ne; [|reg_neq]. rewrite /C4 upd_ne; [|reg_neq].
        rewrite /C3 upd_ne; [|reg_neq]. rewrite /C2 upd_eq; reflexivity. }
      assert (HC5a2 : C5 !!! Regidx Ra2 =
                        (mword_of_int (Z.of_nat (S rem)) : mword 64)).
      { rewrite /C5 upd_ne; [|reg_neq]. rewrite /C4 upd_ne; [|reg_neq].
        rewrite /C3 upd_ne; [|reg_neq]. rewrite /C2 upd_ne; [|reg_neq].
        rewrite /C1 upd_ne; [exact Ha2|reg_neq]. }
      assert (HC5sp : C5 !!! Regidx csp_rs1 = pa_stk sp0 2).
      { rewrite /C5 upd_ne; [|reg_neq]. rewrite /C4 upd_ne; [|reg_neq].
        rewrite /C3 upd_ne; [|reg_neq]. rewrite /C2 upd_ne; [|reg_neq].
        rewrite /C1 upd_ne; [exact Hsp|reg_neq]. }
      assert (HC5a0 : C5 !!! Regidx Ra0 = s).
      { rewrite /C5 upd_ne; [|reg_neq]. rewrite /C4 upd_ne; [|reg_neq].
        rewrite /C3 upd_ne; [|reg_neq]. rewrite /C2 upd_ne; [|reg_neq].
        rewrite /C1 upd_ne; [exact Ha0|reg_neq]. }
      assert (HC5thr : forall r : mword 5, is_cs_idx r = true ->
                    r <> csp_rs1 -> r <> Rs0 -> C5 !!! Regidx r = mm !!! Regidx r).
      { intros r Hr Ncsp Ns0.
        rewrite /C5 upd_ne;
          [|apply snc_cs_ne; [vm_compute; reflexivity|exact Hr]].
        rewrite /C4 upd_ne;
          [|apply snc_cs_ne; [vm_compute; reflexivity|exact Hr]].
        rewrite /C3 upd_ne;
          [|apply snc_cs_ne; [vm_compute; reflexivity|exact Hr]].
        rewrite /C2 upd_ne;
          [|apply snc_cs_ne; [vm_compute; reflexivity|exact Hr]].
        rewrite /C1 upd_ne;
          [apply Hthr; assumption|apply snc_cs_ne; [vm_compute; reflexivity|exact Hr]]. }
      assert (HC5a3' : forall CID' : CpuId, rget (CID := CID') C5 Ra3 =
                         (mword_of_int (Z.of_nat rem) : mword 64))
        by (intros CID'; rgne; exact HC5a3).
      assert (HC5a4' : forall CID' : CpuId, rget (CID := CID') C5 Ra4 =
                         zero_extend' 64 (f d : mword 8))
        by (intros CID'; rgne; exact HC5a4).
      assert (HC5a5' : forall CID' : CpuId, rget (CID := CID') C5 Ra5 = pa_add s (S d))
        by (intros CID'; rgne; exact HC5a5).
      assert (Hp24 : add_vec_int (mword_of_int (KernelSyms.strncpy + 0x22) : mword 64) 2
                     = mword_of_int (KernelSyms.strncpy + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp24) in "Hpc". iPoseProof (sncp_24 with "Htext") as "Hi24".
      destruct (decide (f d = (mword_of_int 0 : mword 8))) as [Hz|Hnz].
      + (* the copied byte was NUL: either finish or pad the suffix *)
        iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.strncpy + 0x24))
                  (mword_of_int 244 : mword 8) (Cregidx (mword_of_int 6)) Ra4
                  C5 (K - 2)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(unfold neq_vec; rgne; rewrite HC5a4 Hz bc_zext8_iszero; reflexivity)
                  with "Hcg Hpc Hi24").
        iIntros (CID8 Hs8) "Hcg Hpc".
        assert (Hp26 : add_vec_int (mword_of_int (KernelSyms.strncpy + 0x24) : mword 64) 2
                       = mword_of_int (KernelSyms.strncpy + 0x26))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp26) in "Hpc". iPoseProof (sncp_26 with "Htext") as "Hi26".
        iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.strncpy + 0x26))
                  Ra4 Ra5 C5 (K - 2)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi26").
        iIntros (CID9 Hs9) "Hcg Hpc".
        iEval (rewrite (HC5a5' _) add_vec_zero_l) in "Hcg".
        set (C6 := <[Regidx Ra4 := regval_into_reg (pa_add s (S d))]> C5).
        assert (HC6a4 : C6 !!! Regidx Ra4 = pa_add s (S d))
          by (rewrite /C6 upd_eq; reflexivity).
        assert (HC6a6 : C6 !!! Regidx Ra6 =
                          (mword_of_int (Z.of_nat rem) : mword 64))
          by (rewrite /C6 upd_ne; [exact HC5a6|reg_neq]).
        assert (HC6a2 : C6 !!! Regidx Ra2 =
                          (mword_of_int (Z.of_nat (S rem)) : mword 64))
          by (rewrite /C6 upd_ne; [exact HC5a2|reg_neq]).
        assert (HC6a5 : C6 !!! Regidx Ra5 = pa_add s (S d))
          by (rewrite /C6 upd_ne; [exact HC5a5|reg_neq]).
        assert (HC6sp : C6 !!! Regidx csp_rs1 = pa_stk sp0 2)
          by (rewrite /C6 upd_ne; [exact HC5sp|reg_neq]).
        assert (HC6a0 : C6 !!! Regidx Ra0 = s)
          by (rewrite /C6 upd_ne; [exact HC5a0|reg_neq]).
        assert (HC6thr : forall r : mword 5, is_cs_idx r = true ->
                      r <> csp_rs1 -> r <> Rs0 -> C6 !!! Regidx r = mm !!! Regidx r).
        { intros r Hr Ncsp Ns0. rewrite /C6 upd_ne;
            [apply HC5thr; assumption|apply snc_cs_ne; [vm_compute; reflexivity|exact Hr]]. }
        assert (HC6a6' : forall CID' : CpuId, rget (CID := CID') C6 Ra6 =
                           (mword_of_int (Z.of_nat rem) : mword 64))
          by (intros CID'; rgne; exact HC6a6).
        assert (HC6a2' : forall CID' : CpuId, rget (CID := CID') C6 Ra2 =
                           (mword_of_int (Z.of_nat (S rem)) : mword 64))
          by (intros CID'; rgne; exact HC6a2).
        assert (HC6a5' : forall CID' : CpuId, rget (CID := CID') C6 Ra5 = pa_add s (S d))
          by (intros CID'; rgne; exact HC6a5).
        assert (Hp28 : add_vec_int (mword_of_int (KernelSyms.strncpy + 0x26) : mword 64) 2
                       = mword_of_int (KernelSyms.strncpy + 0x28))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp28) in "Hpc". iPoseProof (sncp_28 with "Htext") as "Hi28".
        destruct rem as [|q].
        * (* the NUL was the last byte allowed by [n] *)
          iApply (wp_bge_x0_taken_s_sconf (mword_of_int (KernelSyms.strncpy + 0x28))
                    (mword_of_int 22 : mword 13) Ra6 C6 (K - 2)%nat b
                    ltac:(vm_compute; discriminate)
                    ltac:(rewrite (HC6a6' _) (snc_bgez_count 0 ltac:(lia)); reflexivity)
                    ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi28").
          iNext. iIntros (CID10 Hs10) "Hcg Hpc".
          assert (Hto3e : add_vec (mword_of_int (KernelSyms.strncpy + 0x28) : mword 64)
                            (sign_extend' 64 (mword_of_int 22 : mword 13))
                          = mword_of_int (KernelSyms.strncpy + 0x3e))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hto3e) in "Hpc".
          assert (Hpost : snc_post f h' n).
          { apply snc_post_padded with (k:=d); [lia|split; assumption| |].
            - intros j Hj. apply Hcopy'; lia.
            - intros j Hjd Hjn. assert (j = d) by lia. subst j.
              rewrite /h' bb_upd_eq Hz. reflexivity. }
          iSpecialize ("Hcont" $! CID10 with "[%]"); [wp_next_chain|].
          iApply ("Hcont" $! C6 h' with "[%] [%] [%] [%] Hcg Hpc Hsrc Hdst"); assumption.
        * (* at least one padding byte remains *)
          iApply (wp_bge_x0_fall_s_sconf (mword_of_int (KernelSyms.strncpy + 0x28))
                    (mword_of_int 22 : mword 13) Ra6 C6 (K - 2)%nat b
                    ltac:(vm_compute; discriminate)
                    ltac:(rewrite (HC6a6' _) (snc_bgez_count (S q) ltac:(lia)); reflexivity)
                    with "Hcg Hpc Hi28").
          iIntros (CID10 Hs10) "Hcg Hpc".
          assert (Hp2c : add_vec_int (mword_of_int (KernelSyms.strncpy + 0x28) : mword 64) 4
                         = mword_of_int (KernelSyms.strncpy + 0x2c))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp2c) in "Hpc". iPoseProof (sncp_2c with "Htext") as "Hi2c".
          set (w1 := sign_extend' 64
            (add_vec (subrange_vec_dec (pa_add s (S d)) 31 0 : mword 32)
                     (subrange_vec_dec
                       (mword_of_int (Z.of_nat (S (S q))) : mword 64) 31 0))).
          iApply (wp_addw_s_sconf (mword_of_int (KernelSyms.strncpy + 0x2c))
                    Ra5 Ra2 C6 (K - 2)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc Hi2c").
          iIntros (CID11 Hs11) "Hcg Hpc".
          iEval (rewrite (HC6a5' _) (HC6a2' _)) in "Hcg".
          set (D1 := <[Regidx Ra5 := regval_into_reg w1]> C6).
          assert (HD1a5 : D1 !!! Regidx Ra5 = w1) by (rewrite /D1 upd_eq; reflexivity).
          assert (HD1a5' : forall CID' : CpuId, rget (CID := CID') D1 Ra5 = w1)
            by (intros CID'; rgne; exact HD1a5).
          assert (Hp2e : add_vec_int (mword_of_int (KernelSyms.strncpy + 0x2c) : mword 64) 2
                         = mword_of_int (KernelSyms.strncpy + 0x2e))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp2e) in "Hpc". iPoseProof (sncp_2e with "Htext") as "Hi2e".
          set (w2 := sign_extend' 64
            (subrange_vec_dec
              (add_vec w1
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0)).
          iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.strncpy + 0x2e))
                    Ra5 (mword_of_int 63 : mword 6) D1 (K - 2)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc Hi2e").
          iIntros (CID12 Hs12) "Hcg Hpc".
          iEval (rewrite (HD1a5' _)) in "Hcg".
          set (D2 := <[Regidx Ra5 := regval_into_reg w2]> D1).
          assert (HD2sp : D2 !!! Regidx csp_rs1 = pa_stk sp0 2)
            by (rewrite /D2 upd_ne; [rewrite /D1 upd_ne; [exact HC6sp|reg_neq]|reg_neq]).
          assert (HD2a0 : D2 !!! Regidx Ra0 = s)
            by (rewrite /D2 upd_ne; [rewrite /D1 upd_ne; [exact HC6a0|reg_neq]|reg_neq]).
          assert (HD2a4 : D2 !!! Regidx Ra4 = pa_add s (S d))
            by (rewrite /D2 upd_ne; [rewrite /D1 upd_ne; [exact HC6a4|reg_neq]|reg_neq]).
          assert (HD2a5 : D2 !!! Regidx Ra5 = w2) by (rewrite /D2 upd_eq; reflexivity).
          assert (HD2thr : forall r : mword 5, is_cs_idx r = true ->
                        r <> csp_rs1 -> r <> Rs0 -> D2 !!! Regidx r = mm !!! Regidx r).
          { intros r Hr Ncsp Ns0. rewrite /D2 upd_ne;
              [|apply snc_cs_ne; [vm_compute; reflexivity|exact Hr]].
            rewrite /D1 upd_ne;
              [apply HC6thr; assumption|apply snc_cs_ne; [vm_compute; reflexivity|exact Hr]]. }
          assert (Hendlow : (subrange_vec_dec w2 31 0 : mword 32) =
                    subrange_vec_dec (pa_add s n) 31 0).
          { apply (snc_padding_end_low s n d (S q)); exact Hsum. }
          assert (Hzero1 : forall j, (d <= j)%nat -> (j < S d)%nat ->
                         h' j = (mword_of_int 0 : mword 8)).
          { intros j Hj1 Hj2. assert (j = d) by lia. subst j.
            rewrite /h' bb_upd_eq Hz. reflexivity. }
          assert (Hchain' : b = false \/ p = zero_reg ->
                              (CID12 : CPU) = (CIDh : CPU)) by wp_next_chain.
          iApply (snc_pad_loop mm n d f K dq t s sp0 w2 b p CIDh
                    ltac:(lia) ltac:(split; assumption) Hn31 Hendlow
                    (S q) (S d) h' D2 CID12 Hchain'
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros j Hj; apply Hcopy'; lia) Hzero1
                    HD2sp HD2a0 HD2a4 HD2a5 HD2thr
                    with "Hcg Htext Hpc Hsrc Hdst Hcont").
      + (* non-NUL: take the back edge and continue with one fewer byte *)
        iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.strncpy + 0x24))
                  (mword_of_int 244 : mword 8) (Cregidx (mword_of_int 6)) Ra4
                  C5 (K - 2)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(unfold neq_vec; rgne; rewrite HC5a4 (bc_zext8_nonzero _ Hnz); reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi24").
        iNext. iIntros (CID8 Hs8) "Hcg Hpc".
        assert (Hback0c : add_vec (mword_of_int (KernelSyms.strncpy + 0x24) : mword 64)
                           (sign_extend' 64
                             (sign_extend' 13
                               (concat_vec (mword_of_int 244 : mword 8) ('b"0"))))
                         = mword_of_int (KernelSyms.strncpy + 0x0c))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hback0c) in "Hpc". iPoseProof (sncp_0c with "Htext") as "Hi0c".
        iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.strncpy + 0x0c))
                  Ra2 Ra3 C5 (K - 2)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi0c").
        iIntros (CID9 Hs9) "Hcg Hpc".
        iEval (rewrite (HC5a3' _) add_vec_zero_l) in "Hcg".
        set (C6 := <[Regidx Ra2 := regval_into_reg
                      (mword_of_int (Z.of_nat rem) : mword 64)]> C5).
        assert (HC6sp : C6 !!! Regidx csp_rs1 = pa_stk sp0 2)
          by (rewrite /C6 upd_ne; [exact HC5sp|reg_neq]).
        assert (HC6a0 : C6 !!! Regidx Ra0 = s)
          by (rewrite /C6 upd_ne; [exact HC5a0|reg_neq]).
        assert (HC6a1 : C6 !!! Regidx Ra1 = pa_add t (S d))
          by (rewrite /C6 upd_ne; [exact HC5a1|reg_neq]).
        assert (HC6a2 : C6 !!! Regidx Ra2 =
                          (mword_of_int (Z.of_nat rem) : mword 64))
          by (rewrite /C6 upd_eq; reflexivity).
        assert (HC6a5 : C6 !!! Regidx Ra5 = pa_add s (S d))
          by (rewrite /C6 upd_ne; [exact HC5a5|reg_neq]).
        assert (HC6thr : forall r : mword 5, is_cs_idx r = true ->
                      r <> csp_rs1 -> r <> Rs0 -> C6 !!! Regidx r = mm !!! Regidx r).
        { intros r Hr Ncsp Ns0. rewrite /C6 upd_ne;
            [apply HC5thr; assumption|apply snc_cs_ne; [vm_compute; reflexivity|exact Hr]]. }
        assert (Hchain' : b = false \/ p = zero_reg ->
                            (CID9 : CPU) = (CIDh : CPU)) by wp_next_chain.
        iApply (IH (S d) h' C6 CID9 Hchain' ltac:(lia)
                  Hcopy' Hunt' (bb_nonul_step f d Hnn Hnz)
                  HC6sp HC6a0 HC6a1 HC6a2 HC6a5 HC6thr
                  with "Hcg Htext Hpc Hsrc Hdst Hcont").
  Qed.

  (* The public theorem.  Its only buffer assumptions are the two byte-wise
     points-to ranges in [wp_strncpy_sconf_body]; the numeric bound is needed
     because gcc implements the loop counter and padding comparison with
     signed 32-bit word instructions. *)
  Lemma wp_strncpy_sconf (mm : regfile)
      (n : nat) (f g : nat -> bv 8) (K : nat) (dq : dfrac) (b : bool) (p : mword 64)
    : wp_strncpy_sconf_body mm n f g K dq b p.
  Proof.
    cbv beta delta [wp_strncpy_sconf_body].
    intros pcE s t ret_tgt HK Hn2 Hn31.
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg #Htext Hpc Hsrc Hdst Hcont".
    iPoseProof (sncp_00 with "Htext") as "Hi00".
    iPoseProof (sncp_02 with "Htext") as "Hi02".
    iPoseProof (sncp_04 with "Htext") as "Hi04".
    iPoseProof (sncp_06 with "Htext") as "Hi06".
    iPoseProof (sncp_08 with "Htext") as "Hi08".
    iPoseProof (sncp_0a with "Htext") as "Hi0a".
    (* +0x00: allocate the two-word stack frame. *)
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 48 : mword 6) mm K 2 b
              HK (snc_push (mm !!! Regidx csp_rs1))
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (mm !!! Regidx csp_rs1)
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> mm).
    change (<[Regidx csp_rs1 := regval_into_reg
               (add_vec (mm !!! Regidx csp_rs1)
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> mm)
      with R1.
    assert (HR1sp : R1 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /R1 upd_eq; apply snc_push).
    assert (Hp02 : add_vec_int (pcE : mword 64) 2 =
                     mword_of_int (KernelSyms.strncpy + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    iDestruct (stack_own_2_elim with "Hframe") as (u1 u2) "[Hb1 Hb2]".
    assert (Hpa1 : add_vec (R1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                   = pa_stk sp0 1).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpa2 : add_vec (R1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                   = pa_stk sp0 2).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* +0x02,+0x04: save ra and s0. *)
    iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (KernelSyms.strncpy + 0x02))
              (mword_of_int 1 : mword 6) Rra R1 (K - 2)%nat u1 b
              with "Hcg Hpc Hi02 [Hb1]").
    { iEval (rewrite Hpa1). iExact "Hb1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hb1". iEval (rewrite Hpa1) in "Hb1".
    assert (HR1ra : R1 !!! Regidx Rra = mm !!! Regidx Rra)
      by (rewrite /R1 upd_ne; [reflexivity|reg_neq]).
    assert (HR1ra' : forall CID' : CpuId, rget (CID := CID') R1 Rra = mm !!! Regidx Rra)
      by (intros CID'; rgne; exact HR1ra).
    iEval (rewrite HR1ra') in "Hb1".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.strncpy + 0x02) : mword 64) 2
                   = mword_of_int (KernelSyms.strncpy + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (kt := KT1) (ktd := KT1) (mword_of_int (KernelSyms.strncpy + 0x04))
              (mword_of_int 0 : mword 6) Rs0 R1 (K - 2)%nat u2 b
              with "Hcg Hpc Hi04 [Hb2]").
    { iEval (rewrite Hpa2). iExact "Hb2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hb2". iEval (rewrite Hpa2) in "Hb2".
    assert (HR1s0 : R1 !!! Regidx Rs0 = mm !!! Regidx Rs0)
      by (rewrite /R1 upd_ne; [reflexivity|reg_neq]).
    assert (HR1s0' : forall CID' : CpuId, rget (CID := CID') R1 Rs0 = mm !!! Regidx Rs0)
      by (intros CID'; rgne; exact HR1s0).
    iEval (rewrite HR1s0') in "Hb2".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.strncpy + 0x04) : mword 64) 2
                   = mword_of_int (KernelSyms.strncpy + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    (* +0x06: establish the frame pointer. *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.strncpy + 0x06))
              (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) Rs0 R1
              (K - 2)%nat b ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06").
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1).
    change (<[Regidx Rs0 := regval_into_reg
               (add_vec (R1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1)
      with R2.
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.strncpy + 0x06) : mword 64) 2
                   = mword_of_int (KernelSyms.strncpy + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    assert (HR2sp : R2 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /R2 upd_ne; [exact HR1sp|reg_neq]).
    assert (HR2a0 : R2 !!! Regidx Ra0 = s)
      by (rewrite /R2 upd_ne; [rewrite /R1 upd_ne; [reflexivity|reg_neq]|reg_neq]).
    assert (HR2a1 : R2 !!! Regidx Ra1 = t)
      by (rewrite /R2 upd_ne; [rewrite /R1 upd_ne; [reflexivity|reg_neq]|reg_neq]).
    assert (HR2a2 : R2 !!! Regidx Ra2 = (mword_of_int (Z.of_nat n) : mword 64))
      by (rewrite /R2 upd_ne; [rewrite /R1 upd_ne; [exact Hn2|reg_neq]|reg_neq]).
    assert (HR2a0' : forall CID' : CpuId, rget (CID := CID') R2 Ra0 = s)
      by (intros CID'; rgne; exact HR2a0).
    assert (HR2thr : forall r : mword 5, is_cs_idx r = true ->
                  r <> csp_rs1 -> r <> Rs0 -> R2 !!! Regidx r = mm !!! Regidx r).
    { intros r Hr Ncsp Ns0. rewrite /R2 upd_ne;
        [|intro He; injection He as He'; congruence].
      rewrite /R1 upd_ne; [reflexivity|intro He; injection He as He'; congruence]. }
    (* +0x08: preserve the return value in a5. *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.strncpy + 0x08))
              Ra5 Ra0 R2 (K - 2)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hs5) "Hcg Hpc".
    iEval (rewrite (HR2a0' _) add_vec_zero_l) in "Hcg".
    set (R3 := <[Regidx Ra5 := regval_into_reg s]> R2).
    assert (HR3sp : R3 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /R3 upd_ne; [exact HR2sp|reg_neq]).
    assert (HR3a0 : R3 !!! Regidx Ra0 = s)
      by (rewrite /R3 upd_ne; [exact HR2a0|reg_neq]).
    assert (HR3a1 : R3 !!! Regidx Ra1 = t)
      by (rewrite /R3 upd_ne; [exact HR2a1|reg_neq]).
    assert (HR3a2 : R3 !!! Regidx Ra2 = (mword_of_int (Z.of_nat n) : mword 64))
      by (rewrite /R3 upd_ne; [exact HR2a2|reg_neq]).
    assert (HR3a5 : R3 !!! Regidx Ra5 = s) by (rewrite /R3 upd_eq; reflexivity).
    assert (HR3a2' : forall CID' : CpuId,
               rget (CID := CID') R3 Ra2 = (mword_of_int (Z.of_nat n) : mword 64))
      by (intros CID'; rgne; exact HR3a2).
    assert (HR3thr : forall r : mword 5, is_cs_idx r = true ->
                  r <> csp_rs1 -> r <> Rs0 -> R3 !!! Regidx r = mm !!! Regidx r).
    { intros r Hr Ncsp Ns0. rewrite /R3 upd_ne;
        [apply HR2thr; assumption|apply snc_cs_ne; [vm_compute; reflexivity|exact Hr]]. }
    assert (Hp0a : add_vec_int (mword_of_int (KernelSyms.strncpy + 0x08) : mword 64) 2
                   = mword_of_int (KernelSyms.strncpy + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0a) in "Hpc".
    (* +0x0a: jump over the loop's back-edge assignment to its guard. *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.strncpy + 0x0a))
              (sign_extend' 21 (concat_vec (mword_of_int 2 : mword 11) ('b"0")))
              R3 (K - 2)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0a").
    iIntros (CID6 Hs6). iNext. iIntros "Hcg Hpc".
    assert (Ht0e : add_vec (mword_of_int (KernelSyms.strncpy + 0x0a) : mword 64)
                     (sign_extend' 64
                       (sign_extend' 21
                         (concat_vec (mword_of_int 2 : mword 11) ('b"0"))))
                   = mword_of_int (KernelSyms.strncpy + 0x0e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ht0e) in "Hpc".
    destruct (Nat.eq_dec n 0) as [Hn0|Hnpos].
    - (* n=0: no buffer cell is touched, and its name remains exactly [g]. *)
      iPoseProof (sncp_0e with "Htext") as "Hi0e".
      iApply (wp_bge_x0_taken_s_sconf (mword_of_int (KernelSyms.strncpy + 0x0e))
                (mword_of_int 48 : mword 13) Ra2 R3 (K - 2)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (HR3a2' _) (snc_bgez_count n Hn31);
                       apply Nat.eqb_eq; exact Hn0)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi0e").
      iNext. iIntros (CID7 Hs7) "Hcg Hpc".
      assert (Ht3e : add_vec (mword_of_int (KernelSyms.strncpy + 0x0e) : mword 64)
                       (sign_extend' 64 (mword_of_int 48 : mword 13))
                     = mword_of_int (KernelSyms.strncpy + 0x3e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ht3e) in "Hpc".
      iApply (snc_tail mm R3 K s sp0 (mm !!! Regidx Rra) (mm !!! Regidx Rs0) b p
                HK ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                HR3sp HR3a0 HR3thr
                with "Hcg Htext Hpc Hb1 Hb2").
      iIntros (CID8 Hs8 mf) "[%Hcs %Hfa0] Hcg Hpc".
      iSpecialize ("Hcont" $! CID8 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf g with "Hcg Hpc Hsrc Hdst [%] [%] [%]").
      + exact Hcs.
      + exact Hfa0.
      + left. split; [exact Hn0|reflexivity].
    - (* n>0: run the verified copy/pad loops from index zero. *)
      assert (Hpos : (0 < n)%nat) by lia.
      assert (HR3a1' : R3 !!! Regidx Ra1 = pa_add t 0)
        by (rewrite HR3a1 pa_add_0; reflexivity).
      assert (HR3a5' : R3 !!! Regidx Ra5 = pa_add s 0)
        by (rewrite HR3a5 pa_add_0; reflexivity).
      iApply (snc_copy_loop mm n f g K dq t s sp0 b p CID6 Hn31
                n 0%nat g R3 CID6 ltac:(intros _; reflexivity)
                ltac:(lia) ltac:(intros j Hj; lia) ltac:(intros j Hj; reflexivity)
                (bb_nonul_0 f) HR3sp HR3a0 HR3a1' HR3a2 HR3a5' HR3thr
                with "Hcg Htext Hpc Hsrc Hdst").
      iIntros (CID7 Hs7 Mt hf) "%Hpost %Htsp %Hta0 %Htthr Hcg Hpc Hsrc Hdst".
      iApply (snc_tail mm Mt K s sp0 (mm !!! Regidx Rra) (mm !!! Regidx Rs0) b p
                HK ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                Htsp Hta0 Htthr
                with "Hcg Htext Hpc Hb1 Hb2").
      iIntros (CID8 Hs8 mf) "[%Hcs %Hfa0] Hcg Hpc".
      iSpecialize ("Hcont" $! CID8 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf hf with "Hcg Hpc Hsrc Hdst [%] [%] [%]").
      + exact Hcs.
      + exact Hfa0.
      + right. split; assumption.
  Qed.

End MachineProof.
End StrncpyProof.
