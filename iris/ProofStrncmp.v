(* ProofStrncmp.v -- the whole-function WP for xv6's strncmp(), over the
   SIE-agnostic sconf world.

     int strncmp(const char *p, const char *q, uint n)

   Contract: SpecStrncmp.v.  29 instructions, a 2-slot ra/s0 frame, no callees. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvPtsto RiscvLang.
Require Import RegFile InstrBytes WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn CalleeSaved KernelText.
Require Import KernelRvcDecode.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl WpSmodeIntr.
Require Import HartTp WpNext IntrDefs.
Require Import ByteCursor ByteBuf.
Require Import CodeStrncmp.
Require Import SpecStrncmp.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Local Open Scope Z_scope.

Local Ltac rgne :=
  rewrite rget_ne;
  [ | let H1 := fresh in let H2 := fresh in
      intro H1; injection H1 as H2; vm_compute in H2; congruence ].

Module StrncmpProof : STRNCMP.

Section ProofStrncmp.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {ktf ktg : ktier}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.

  Local Lemma cs_ne (k r : mword 5) :
    is_cs_idx k = false -> is_cs_idx r = true -> Regidx r <> Regidx k.
  Proof. intros Hk Hr He. symmetry in He. exact (is_cs_idx_true_neq k r Hk Hr He). Qed.

  Local Ltac peel_sym :=
    rewrite upd_ne;
    [| let H := fresh "Hpe" in
       let H' := fresh "Hpe" in
       intro H; injection H as H'; congruence ].

  Local Lemma snc_push (X : mword 64) :
    add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk X 2.
  Proof. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. Qed.

  Local Lemma snc_step (s : mword 64) (j : nat) :
    add_vec (pa_add s j) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))) = pa_add s (S j).
  Proof. apply pa_add_step. apply bv_eq; vm_compute; reflexivity. Qed.

  Lemma snc_subw_diff (b1 b2 : bv 8) :
    sign_extend' 64
      (sub_vec (subrange_vec_dec (zero_extend' 64 (b1 : mword 8) : mword 64) 31 0 : mword 32)
               (subrange_vec_dec (zero_extend' 64 (b2 : mword 8) : mword 64) 31 0 : mword 32))
    = (mword_of_int (bv_unsigned b1 - bv_unsigned b2) : mword 64).
  Proof.
    apply bv_eq.
    rewrite moi64_unsigned.
    assert (Hze1 : (8 <= 64)%N) by (vm_compute; intro Hc; discriminate Hc).
    assert (Hze2 : (8 <= 64)%N) by (vm_compute; intro Hc; discriminate Hc).
    unfold sign_extend', zero_extend', Operators_mwords.sign_extend, Operators_mwords.zero_extend,
      Operators_mwords.exts_vec, Operators_mwords.extz_vec, to_word, get_word.
    rewrite bv_sign_extend_unsigned.
    unfold bv_signed.
    rewrite sub_vec32_unsigned.
    rewrite !subrange_31_0_unsigned.
    rewrite (bv_zero_extend_unsigned 64 (b1 : mword 8) Hze1).
    rewrite (bv_zero_extend_unsigned 64 (b2 : mword 8) Hze2).
    pose proof (bv_unsigned_in_range 8 b1) as Hb1.
    pose proof (bv_unsigned_in_range 8 b2) as Hb2.
    unfold bv_modulus in Hb1, Hb2.
    unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (MachineWord.MachineWord.Z_idx 32) with 32%N.
    change (MachineWord.MachineWord.Z_idx 64) with 64%N.
    change (2 ^ Z.of_N 32 / 2)%Z with 2147483648%Z.
    change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
    change (2^(32-1))%Z with 2147483648%Z.
    change (2^32)%Z with 4294967296%Z.
    change (2^(64-1))%Z with 9223372036854775808%Z.
    change (2^64)%Z with 18446744073709551616%Z.
    assert (Hb1m : (bv_unsigned b1) mod 4294967296 = bv_unsigned b1) by (apply Z.mod_small; lia).
    assert (Hb2m : (bv_unsigned b2) mod 4294967296 = bv_unsigned b2) by (apply Z.mod_small; lia).
    rewrite Hb1m Hb2m.
    destruct (Z.le_gt_cases 0 (bv_unsigned b1 - bv_unsigned b2)) as [Hpos | Hneg].
    - rewrite (Z.mod_small (bv_unsigned b1 - bv_unsigned b2) 4294967296); [| lia].
      rewrite (Z.mod_small (bv_unsigned b1 - bv_unsigned b2 + 2147483648) 4294967296); [| lia].
      replace (bv_unsigned b1 - bv_unsigned b2 + 2147483648 - 2147483648) with (bv_unsigned b1 - bv_unsigned b2) by lia.
      rewrite (Z.mod_small (bv_unsigned b1 - bv_unsigned b2) 18446744073709551616); [| lia].
      reflexivity.
    - assert (Hm32 : (bv_unsigned b1 - bv_unsigned b2) mod 4294967296 = 4294967296 + (bv_unsigned b1 - bv_unsigned b2)).
      { rewrite <- Z.mod_add with (b := 1) by lia.
        replace (bv_unsigned b1 - bv_unsigned b2 + 1 * 4294967296) with (4294967296 + (bv_unsigned b1 - bv_unsigned b2)) by lia.
        apply Z.mod_small. lia. }
      assert (Hsw32 : (4294967296 + (bv_unsigned b1 - bv_unsigned b2) + 2147483648) mod 4294967296 = bv_unsigned b1 - bv_unsigned b2 + 2147483648).
      { replace (4294967296 + (bv_unsigned b1 - bv_unsigned b2) + 2147483648) with ((bv_unsigned b1 - bv_unsigned b2 + 2147483648) + 1 * 4294967296) by lia.
        rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
      assert (Hm64 : (bv_unsigned b1 - bv_unsigned b2) mod 18446744073709551616 = 18446744073709551616 + (bv_unsigned b1 - bv_unsigned b2)).
      { rewrite <- Z.mod_add with (b := 1) by lia.
        replace (bv_unsigned b1 - bv_unsigned b2 + 1 * 18446744073709551616) with (18446744073709551616 + (bv_unsigned b1 - bv_unsigned b2)) by lia.
        apply Z.mod_small. lia. }
      rewrite Hm32 Hsw32.
      replace (bv_unsigned b1 - bv_unsigned b2 + 2147483648 - 2147483648) with (bv_unsigned b1 - bv_unsigned b2) by lia.
      rewrite Hm64. reflexivity.
  Qed.

  Local Lemma snc_dec_a2 (n t : nat) :
    (t < n)%nat -> (Z.of_nat n < 2147483648)%Z ->
    add_vec (mword_of_int (Z.of_nat (n - t)) : mword 64)
      (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))
    = (mword_of_int (Z.of_nat (n - S t)) : mword 64).
  Proof.
    intros Htn Hn. apply bv_eq.
    rewrite add_vec64_unsigned !moi64_unsigned.
    unfold bv_wrap.
    change (bv_modulus 64) with 18446744073709551616%Z.
    change (bv_signed (get_word (sign_extend' 12 (mword_of_int 63)))) with (-1)%Z.
    rewrite <- Z.add_mod; [| intro Hc; discriminate Hc].
    replace (Z.of_nat (n - t) + -1)%Z with (Z.of_nat (n - S t))%Z by lia.
    reflexivity.
  Qed.

  (* Epilogue helper (+0x32 .. +0x38) *)
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
    pc_is (CID := CID0) (mword_of_int (KernelSyms.strncmp + 0x32) : mword 64) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    wp_next (CID0 := CID0) b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved mm mf /\ mf !!! Regidx Ra0 = rv⌝ -∗
        sie_cap_gpr KT1 mf K b p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp0 Hra0 Hs00 Hmtsp Hmta0 Hthr.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hcont".
    iPoseProof (snci_32 with "Htext") as "Hi32".
    iPoseProof (snci_34 with "Htext") as "Hi34".
    iPoseProof (snci_36 with "Htext") as "Hi36".
    iPoseProof (snci_38 with "Htext") as "Hi38".
    (* ---- +0x32: c.ldsp ra,8(sp) ---- *)
    assert (Hpa1 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                   = pa_stk sp0 1).
    { rewrite Hmtsp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.strncmp + 0x32))
              (mword_of_int 1 : mword 6) Rra Mt (K - 2)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi32 Hb1").
    iIntros (CID1 Hs1) "Hcg Hpc Hb1".
    iEval (rewrite Hpa1) in "Hb1".
    set (T1 := <[Regidx Rra := regval_into_reg ra0]> Mt).
    change (<[Regidx Rra := regval_into_reg ra0]> Mt) with T1.
    assert (Hp34 : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x32) : mword 64) 2
                   = mword_of_int (KernelSyms.strncmp + 0x34))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp34) in "Hpc".
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /T1 upd_ne; [exact Hmtsp | reg_neq]).
    (* ---- +0x34: c.ldsp s0,0(sp) ---- *)
    assert (Hpa2 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                   = pa_stk sp0 2).
    { rewrite HT1sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.strncmp + 0x34))
              (mword_of_int 0 : mword 6) Rs0 T1 (K - 2)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi34 Hb2").
    iIntros (CID2 Hs2) "Hcg Hpc Hb2".
    iEval (rewrite Hpa2) in "Hb2".
    set (T2 := <[Regidx Rs0 := regval_into_reg s00]> T1).
    change (<[Regidx Rs0 := regval_into_reg s00]> T1) with T2.
    assert (Hp36 : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x34) : mword 64) 2
                   = mword_of_int (KernelSyms.strncmp + 0x36))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp36) in "Hpc".
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /T2 upd_ne; [exact HT1sp | reg_neq]).
    (* ---- +0x36: c.addi sp,16 ---- *)
    assert (Hwv : add_vec (T2 !!! Regidx csp_rs1)
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0)
      by (rewrite HT2sp; apply stk_pop_16).
    assert (Hpop : T2 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T2 !!! Regidx csp_rs1)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2)
      by (rewrite Hwv; exact HT2sp).
    iDestruct (stack_own_2_intro sp0 ra0 s00 with "Hb1 Hb2") as "Hframe".
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.strncmp + 0x36))
              (mword_of_int 16 : mword 6) T2 (K - 2)%nat 2 b Hpop
              with "Hcg Hpc Hi36 Hframe").
    iIntros (CID3 Hs3) "Hcg Hpc".
    assert (Hnk : ((K - 2) + 2)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    set (T3 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (T2 !!! Regidx csp_rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> T2).
    change (<[Regidx csp_rs1 := regval_into_reg
               (add_vec (T2 !!! Regidx csp_rs1)
                  (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> T2) with T3.
    assert (Hp38 : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x36) : mword 64) 2
                   = mword_of_int (KernelSyms.strncmp + 0x38))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp38) in "Hpc".
    (* ---- +0x38: c.ret ---- *)
    assert (HT3ra : T3 !!! Regidx Rra = ra0).
    { rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_eq. reflexivity. }
    assert (HT3ra' : forall CID' : CpuId, rget (CID := CID') T3 Rra = ra0)
      by (intros CID'; rgne; exact HT3ra).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.strncmp + 0x38)) Rra T3 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi38").
    iIntros (CID4 Hs4) "Hcg Hpc".
    iEval (rewrite HT3ra') in "Hpc".
    (* ---- postcondition ---- *)
    assert (HT3a0 : T3 !!! Regidx Ra0 = rv).
    { rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_ne; [| reg_neq]. exact Hmta0. }
    assert (Hgen : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                     T3 !!! Regidx r = mm !!! Regidx r).
    { intros r Hr Ncsp Ns0.
      rewrite /T3 upd_ne; [| intro He; injection He as He'; congruence].
      rewrite /T2 upd_ne; [| intro He; injection He as He'; congruence].
      rewrite /T1 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
      apply Hthr; assumption. }
    iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! T3 with "[%] Hcg Hpc").
    split; [| exact HT3a0].
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

  (* Loop induction lemma *)
  Local Lemma snc_loop
      (mm : regfile) (n : nat) (f g : nat -> bv 8) (K : nat) (dq1 dq2 : dfrac)
      (s1 s2 sp0 : mword 64) (b : bool) (p : mword 64) (CIDh : CpuId) :
    (0 < n)%nat -> (Z.of_nat n < 2147483648)%Z ->
    forall (rem t : nat) (M : regfile) (CID0 : CpuId),
    (b = false \/ p = zero_reg -> (CID0 : CPU) = (CIDh : CPU)) ->
    (t + rem = n - 1)%nat -> bb_nonul f t ->
    (forall j, (j < t)%nat -> f j = g j) ->
    M !!! Regidx csp_rs1 = pa_stk sp0 2 ->
    M !!! Regidx Ra0 = pa_add s1 t ->
    M !!! Regidx Ra1 = pa_add s2 t ->
    M !!! Regidx Ra2 = (mword_of_int (Z.of_nat (n - t)) : mword 64) ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
        M !!! Regidx r = mm !!! Regidx r) ->
    sie_cap_gpr KT1 (CID := CID0) M (K - 2)%nat b p -∗
    kernel_text -∗
    pc_is (CID := CID0) (mword_of_int (KernelSyms.strncmp + 0x0a) : mword 64) -∗
    ([∗ list] j ∈ seq 0 n, (pa_add s1 j) ↦ₘ[ktf]{dq1} f j) -∗
    ([∗ list] j ∈ seq 0 n, (pa_add s2 j) ↦ₘ[ktg]{dq2} g j) -∗
    wp_next (CID0 := CIDh) b p (fun (CID : CpuId) =>
      ∀ Mt : regfile,
        ⌜Mt !!! Regidx csp_rs1 = pa_stk sp0 2⌝ -∗
        ⌜strncmp_res f g n (Mt !!! Regidx Ra0)⌝ -∗
        ⌜forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
            Mt !!! Regidx r = mm !!! Regidx r⌝ -∗
        sie_cap_gpr KT1 Mt (K - 2)%nat b p -∗
        pc_is (mword_of_int (KernelSyms.strncmp + 0x32) : mword 64) -∗
        ([∗ list] j ∈ seq 0 n, (pa_add s1 j) ↦ₘ[ktf]{dq1} f j) -∗
        ([∗ list] j ∈ seq 0 n, (pa_add s2 j) ↦ₘ[ktg]{dq2} g j) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hnpos Hn31 rem.
    induction rem as [| rem IH]; intros t M CID0 Hchain Hsum Hnn Heq Hsp Ha0 Ha1 Ha2 Hthr;
      iIntros "Hcg #Htext Hpc Hbuf1 Hbuf2 Hcont".
    - (* rem = 0: t = n - 1 *)
      assert (Htn1 : t = (n - 1)%nat) by lia.
      assert (Htn : (t < n)%nat) by lia.
      iPoseProof (snci_0a with "Htext") as "Hi0a".
      iPoseProof (snci_0e with "Htext") as "Hi0e".
      iDestruct (bb_byte_acc s1 n t f dq1 Htn with "Hbuf1") as "[Hb1 Hback1]".
      assert (HMa0 : rget M Ra0 = pa_add s1 t) by (rgne; exact Ha0).
      (* +0x0a: lbu a5, 0(a0) *)
      iApply (wp_lbu_s_sconf (kt := KT1) (ktd := ktf) (mword_of_int (KernelSyms.strncmp + 0x0a)) Ra5 Ra0
                (mword_of_int 0 : mword 12) M (K - 2)%nat (f t : mword 8) b (dqm:=dq1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi0a [Hb1]").
      { iEval (rewrite HMa0 addv_sext0). iExact "Hb1". }
      iIntros (CID1 Hs1) "Hcg Hpc Hb1".
      iEval (rewrite HMa0 addv_sext0) in "Hb1".
      iDestruct ("Hback1" $! f with "[%] Hb1") as "Hbuf1"; [done |].
      set (M1 := <[Regidx Ra5 := regval_into_reg (zero_extend' 64 (f t : mword 8))]> M).
      change (<[Regidx Ra5 := regval_into_reg (zero_extend' 64 (f t : mword 8))]> M) with M1.
      assert (Hp0e : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x0a) : mword 64) 4
                     = mword_of_int (KernelSyms.strncmp + 0x0e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp0e) in "Hpc".
      assert (HM1a5 : M1 !!! Regidx Ra5 = zero_extend' 64 (f t : mword 8))
        by (rewrite /M1 upd_eq; reflexivity).
      assert (HM1a5' : rget M1 Ra5 = zero_extend' 64 (f t : mword 8)) by (rgne; exact HM1a5).
      (* +0x0e: c.beqz a5, +0x1a -> +0x28 *)
      destruct (eq_vec (zero_extend' 64 (f t : mword 8) : mword 64) (zero_reg : mword 64)) eqn:Ez.
      + (* f t = 0: early exit at +0x28 *)
        assert (Hzt : f t = (mword_of_int 0 : mword 8)) by (apply bc_zext8_zero; exact Ez).
        iPoseProof (snci_28 with "Htext") as "Hi28".
        iPoseProof (snci_2c with "Htext") as "Hi2c".
        iPoseProof (snci_30 with "Htext") as "Hi30".
        iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.strncmp + 0x0e))
                  (mword_of_int 13 : mword 8) (Cregidx (mword_of_int 7)) Ra5 M1 (K - 2)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rewrite HM1a5'; exact Ez) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi0e").
        iNext. iIntros (CID2 Hs2) "Hcg Hpc".
        assert (Ht28 : add_vec (mword_of_int (KernelSyms.strncmp + 0x0e) : mword 64)
                  (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 13 : mword 8) ('b"0"))))
                = mword_of_int (KernelSyms.strncmp + 0x28))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Ht28) in "Hpc".
        iDestruct (bb_byte_acc s1 n t f dq1 Htn with "Hbuf1") as "[Hb1 Hback1]".
        iDestruct (bb_byte_acc s2 n t g dq2 Htn with "Hbuf2") as "[Hb2 Hback2]".
        assert (HM1a0 : M1 !!! Regidx Ra0 = pa_add s1 t)
          by (rewrite /M1 upd_ne; [exact Ha0 | reg_neq]).
        assert (HM1a0' : rget M1 Ra0 = pa_add s1 t) by (rgne; exact HM1a0).
        assert (HM1a1 : M1 !!! Regidx Ra1 = pa_add s2 t)
          by (rewrite /M1 upd_ne; [exact Ha1 | reg_neq]).
        assert (HM1a1' : rget M1 Ra1 = pa_add s2 t) by (rgne; exact HM1a1).
        (* +0x28: lbu a0, 0(a0) *)
        iApply (wp_lbu_s_sconf (kt := KT1) (ktd := ktf) (mword_of_int (KernelSyms.strncmp + 0x28)) Ra0 Ra0
                  (mword_of_int 0 : mword 12) M1 (K - 2)%nat (f t : mword 8) b (dqm:=dq1)
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi28 [Hb1]").
        { iEval (rewrite HM1a0' addv_sext0). iExact "Hb1". }
        iIntros (CID3 Hs3) "Hcg Hpc Hb1".
        iEval (rewrite HM1a0' addv_sext0) in "Hb1".
        iDestruct ("Hback1" $! f with "[%] Hb1") as "Hbuf1"; [done |].
        set (M2 := <[Regidx Ra0 := regval_into_reg (zero_extend' 64 (f t : mword 8))]> M1).
        change (<[Regidx Ra0 := regval_into_reg (zero_extend' 64 (f t : mword 8))]> M1) with M2.
        assert (Hp2c : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x28) : mword 64) 4
                       = mword_of_int (KernelSyms.strncmp + 0x2c))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp2c) in "Hpc".
        assert (HM2a1 : M2 !!! Regidx Ra1 = pa_add s2 t)
          by (rewrite /M2 upd_ne; [exact HM1a1 | reg_neq]).
        assert (HM2a1' : rget M2 Ra1 = pa_add s2 t) by (rgne; exact HM2a1).
        (* +0x2c: lbu a5, 0(a1) *)
        iApply (wp_lbu_s_sconf (kt := KT1) (ktd := ktg) (mword_of_int (KernelSyms.strncmp + 0x2c)) Ra5 Ra1
                  (mword_of_int 0 : mword 12) M2 (K - 2)%nat (g t : mword 8) b (dqm:=dq2)
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi2c [Hb2]").
        { iEval (rewrite HM2a1' addv_sext0). iExact "Hb2". }
        iIntros (CID4 Hs4) "Hcg Hpc Hb2".
        iEval (rewrite HM2a1' addv_sext0) in "Hb2".
        iDestruct ("Hback2" $! g with "[%] Hb2") as "Hbuf2"; [done |].
        set (M3 := <[Regidx Ra5 := regval_into_reg (zero_extend' 64 (g t : mword 8))]> M2).
        change (<[Regidx Ra5 := regval_into_reg (zero_extend' 64 (g t : mword 8))]> M2) with M3.
        assert (Hp30 : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x2c) : mword 64) 4
                       = mword_of_int (KernelSyms.strncmp + 0x30))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp30) in "Hpc".
        assert (HM3a0 : M3 !!! Regidx Ra0 = zero_extend' 64 (f t : mword 8)).
        { rewrite /M3 upd_ne; [| reg_neq]. rewrite /M2 upd_eq. reflexivity. }
        assert (HM3a0' : rget M3 Ra0 = zero_extend' 64 (f t : mword 8)) by (rgne; exact HM3a0).
        assert (HM3a5 : M3 !!! Regidx Ra5 = zero_extend' 64 (g t : mword 8))
          by (rewrite /M3 upd_eq; reflexivity).
        assert (HM3a5' : rget M3 Ra5 = zero_extend' 64 (g t : mword 8)) by (rgne; exact HM3a5).
        (* +0x30: c.subw a0, a5 *)
        iApply (wp_csubw_s_sconf (mword_of_int (KernelSyms.strncmp + 0x30))
                  Ra0 Ra0 Ra5 M3 (K - 2)%nat b
                  ltac:(vm_compute; discriminate)
                  ltac:(rdok)
                  with "Hcg Hpc Hi30").
        iIntros (CID5 Hs5) "Hcg Hpc".
        set (M4 := <[Regidx Ra0 := regval_into_reg
                      (sign_extend' 64
                         (sub_vec (subrange_vec_dec (rget M3 Ra0) 31 0 : mword 32)
                                  (subrange_vec_dec (rget M3 Ra5) 31 0 : mword 32)))]> M3).
        change (<[Regidx Ra0 := regval_into_reg
                   (sign_extend' 64
                      (sub_vec (subrange_vec_dec (rget M3 Ra0) 31 0 : mword 32)
                               (subrange_vec_dec (rget M3 Ra5) 31 0 : mword 32)))]> M3) with M4.
        assert (HM4a0 : M4 !!! Regidx Ra0 = (mword_of_int (bv_unsigned (f t) - bv_unsigned (g t)) : mword 64)).
        { rewrite /M4 upd_eq HM3a0' HM3a5'. apply snc_subw_diff. }
        assert (Hp32 : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x30) : mword 64) 2
                       = mword_of_int (KernelSyms.strncmp + 0x32))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp32) in "Hpc".
        assert (HM4sp : M4 !!! Regidx csp_rs1 = pa_stk sp0 2).
        { rewrite /M4 upd_ne; [| reg_neq]. rewrite /M3 upd_ne; [| reg_neq].
          rewrite /M2 upd_ne; [| reg_neq]. rewrite /M1 upd_ne; [exact Hsp | reg_neq]. }
        assert (HM4thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                           M4 !!! Regidx r = mm !!! Regidx r).
        { intros r Hr Ncsp Ns0.
          rewrite /M4 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
          rewrite /M3 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
          rewrite /M2 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
          rewrite /M1 upd_ne; [apply Hthr; assumption | apply cs_ne; [vm_compute; reflexivity | exact Hr]]. }
        iSpecialize ("Hcont" $! CID5 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! M4 with "[%] [%] [%] Hcg Hpc Hbuf1 Hbuf2").
        * exact HM4sp.
        * rewrite HM4a0. right. split; [exact Hnpos |]. left.
          exists t. split.
          -- unfold strncmp_stop. split_and!; [exact Htn | exact Hnn | exact Heq | left; exact Hzt].
          -- reflexivity.
        * exact HM4thr.
      + (* f t != 0: fall through to +0x10 *)
        assert (Hnz1 : f t <> (mword_of_int 0 : mword 8)).
        { intro He. rewrite He bc_zext8_iszero in Ez. discriminate. }
        iPoseProof (snci_10 with "Htext") as "Hi10".
        iPoseProof (snci_14 with "Htext") as "Hi14".
        iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.strncmp + 0x0e))
                  (mword_of_int 13 : mword 8) (Cregidx (mword_of_int 7)) Ra5 M1 (K - 2)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rewrite HM1a5'; exact Ez)
                  with "Hcg Hpc Hi0e").
        iIntros (CID2 Hs2) "Hcg Hpc".
        assert (Hp10 : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x0e) : mword 64) 2
                       = mword_of_int (KernelSyms.strncmp + 0x10))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp10) in "Hpc".
        iDestruct (bb_byte_acc s2 n t g dq2 Htn with "Hbuf2") as "[Hb2 Hback2]".
        assert (HM1a1 : M1 !!! Regidx Ra1 = pa_add s2 t)
          by (rewrite /M1 upd_ne; [exact Ha1 | reg_neq]).
        assert (HM1a1' : rget M1 Ra1 = pa_add s2 t) by (rgne; exact HM1a1).
        (* +0x10: lbu a4, 0(a1) *)
        iApply (wp_lbu_s_sconf (kt := KT1) (ktd := ktg) (mword_of_int (KernelSyms.strncmp + 0x10)) Ra4 Ra1
                  (mword_of_int 0 : mword 12) M1 (K - 2)%nat (g t : mword 8) b (dqm:=dq2)
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi10 [Hb2]").
        { iEval (rewrite HM1a1' addv_sext0). iExact "Hb2". }
        iIntros (CID3 Hs3) "Hcg Hpc Hb2".
        iEval (rewrite HM1a1' addv_sext0) in "Hb2".
        iDestruct ("Hback2" $! g with "[%] Hb2") as "Hbuf2"; [done |].
        set (M2 := <[Regidx Ra4 := regval_into_reg (zero_extend' 64 (g t : mword 8))]> M1).
        change (<[Regidx Ra4 := regval_into_reg (zero_extend' 64 (g t : mword 8))]> M1) with M2.
        assert (Hp14 : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x10) : mword 64) 4
                       = mword_of_int (KernelSyms.strncmp + 0x14))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp14) in "Hpc".
        assert (HM2a4 : M2 !!! Regidx Ra4 = zero_extend' 64 (g t : mword 8))
          by (rewrite /M2 upd_eq; reflexivity).
        assert (HM2a4' : rget M2 Ra4 = zero_extend' 64 (g t : mword 8)) by (rgne; exact HM2a4).
        assert (HM2a5 : M2 !!! Regidx Ra5 = zero_extend' 64 (f t : mword 8))
          by (rewrite /M2 upd_ne; [exact HM1a5 | reg_neq]).
        assert (HM2a5' : rget M2 Ra5 = zero_extend' 64 (f t : mword 8)) by (rgne; exact HM2a5).
        (* +0x14: bne a4, a5, +0x14 -> +0x28 *)
        destruct (eq_vec (zero_extend' 64 (g t : mword 8) : mword 64) (zero_extend' 64 (f t : mword 8) : mword 64)) eqn:Eeq.
        * (* g t = f t: bne falls through to +0x18 *)
          assert (Hgtft : g t = f t).
          { apply eq_vec_true_iff in Eeq. apply (f_equal bv_unsigned) in Eeq.
            unfold zero_extend', Operators_mwords.zero_extend, Operators_mwords.extz_vec,
              to_word, get_word, MachineWord.MachineWord.zero_extend in Eeq.
            rewrite !bv_zero_extend_unsigned in Eeq; try (vm_compute; intro Hc; discriminate Hc).
            apply bv_eq. exact Eeq. }
          assert (Hneq : neq_vec (rget M2 Ra4) (rget M2 Ra5) = false).
          { unfold neq_vec. rewrite HM2a4' HM2a5' Hgtft eq_vec_refl. reflexivity. }
          iPoseProof (snci_18 with "Htext") as "Hi18".
          iPoseProof (snci_1a with "Htext") as "Hi1a".
          iPoseProof (snci_1c with "Htext") as "Hi1c".
          iPoseProof (snci_1e with "Htext") as "Hi1e".
          iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.strncmp + 0x14))
                    (mword_of_int 20 : mword 13) Ra5 Ra4 M2 (K - 2)%nat b
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hneq
                    with "Hcg Hpc Hi14").
          iIntros (CID4 Hs4) "Hcg Hpc".
          assert (Hp18 : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x14) : mword 64) 4
                         = mword_of_int (KernelSyms.strncmp + 0x18))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp18) in "Hpc".
          assert (HM2a2 : M2 !!! Regidx Ra2 = (mword_of_int (Z.of_nat (n - t)) : mword 64)).
          { rewrite /M2 upd_ne; [| reg_neq]. rewrite /M1 upd_ne; [exact Ha2 | reg_neq]. }
          assert (HM2a2' : rget M2 Ra2 = (mword_of_int (Z.of_nat (n - t)) : mword 64)) by (rgne; exact HM2a2).
          (* +0x18: c.addiw a2, -1 *)
          iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.strncmp + 0x18)) Ra2
                    (mword_of_int 63 : mword 6) M2 (K - 2)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc Hi18").
          iIntros (CID5 Hs5) "Hcg Hpc".
          set (M3 := <[Regidx Ra2 := regval_into_reg
                        (sign_extend' 64 (subrange_vec_dec
                           (add_vec (M2 !!! Regidx Ra2)
                              (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))]> M2).
          change (<[Regidx Ra2 := regval_into_reg
                     (sign_extend' 64 (subrange_vec_dec
                        (add_vec (M2 !!! Regidx Ra2)
                           (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))]> M2) with M3.
          assert (HM3a2 : M3 !!! Regidx Ra2 = (mword_of_int (Z.of_nat (n - S t)) : mword 64)).
          { rewrite /M3 upd_eq /regval_into_reg HM2a2.
            rewrite (snc_dec_a2 n t Htn Hn31).
            apply bv_eq.
            unfold sign_extend', Operators_mwords.sign_extend, Operators_mwords.exts_vec, to_word, get_word.
            rewrite bv_sign_extend_unsigned. unfold bv_signed. rewrite !subrange_31_0_unsigned !moi64_unsigned.
            unfold MachineWord.Z_idx, bv_half_modulus, bv_modulus, bv_swrap, bv_wrap.
            change (Z.to_N (31 - 0 + 1)) with 32%N.
            change (Z.to_N 64) with 64%N.
            change (bv_half_modulus 32%N) with 2147483648%Z.
            change (bv_modulus 32%N) with 4294967296%Z.
            change (bv_modulus 64%N) with 18446744073709551616%Z.
            change (bv_modulus 64) with 18446744073709551616%Z.
            replace ((Z.of_nat (n - S t)) mod 18446744073709551616) with (Z.of_nat (n - S t)) by (symmetry; apply Z.mod_small; lia).
            replace ((Z.of_nat (n - S t)) mod 4294967296) with (Z.of_nat (n - S t)) by (symmetry; apply Z.mod_small; lia).
            replace ((Z.of_nat (n - S t) + 2147483648) mod 4294967296) with (Z.of_nat (n - S t) + 2147483648) by (symmetry; apply Z.mod_small; lia).
            replace (Z.of_nat (n - S t) + 2147483648 - 2147483648) with (Z.of_nat (n - S t)) by lia.
            replace ((Z.of_nat (n - S t)) mod 18446744073709551616) with (Z.of_nat (n - S t)) by (symmetry; apply Z.mod_small; lia).
            reflexivity. }
          assert (HM3a2' : rget M3 Ra2 = (mword_of_int (Z.of_nat (n - S t)) : mword 64)) by (rgne; exact HM3a2).
          assert (Hp1a : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x18) : mword 64) 2
                         = mword_of_int (KernelSyms.strncmp + 0x1a))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp1a) in "Hpc".
          assert (HM3a0 : M3 !!! Regidx Ra0 = pa_add s1 t).
          { rewrite /M3 upd_ne; [| reg_neq]. rewrite /M2 upd_ne; [| reg_neq].
            rewrite /M1 upd_ne; [exact Ha0 | reg_neq]. }
          assert (HM3a0' : rget M3 Ra0 = pa_add s1 t) by (rgne; exact HM3a0).
          (* +0x1a: c.addi a0, 1 *)
          iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.strncmp + 0x1a)) Ra0
                    (mword_of_int 1 : mword 6) M3 (K - 2)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc Hi1a").
          iIntros (CID6 Hs6) "Hcg Hpc".
          set (M4 := <[Regidx Ra0 := regval_into_reg
                        (add_vec (rget M3 Ra0)
                           (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> M3).
          change (<[Regidx Ra0 := regval_into_reg
                     (add_vec (rget M3 Ra0)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> M3) with M4.
          assert (HM4a0 : M4 !!! Regidx Ra0 = pa_add s1 (S t)).
          { rewrite /M4 upd_eq HM3a0'. apply snc_step. }
          assert (Hp1c : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x1a) : mword 64) 2
                         = mword_of_int (KernelSyms.strncmp + 0x1c))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp1c) in "Hpc".
          assert (HM4a1 : M4 !!! Regidx Ra1 = pa_add s2 t).
          { rewrite /M4 upd_ne; [| reg_neq]. rewrite /M3 upd_ne; [| reg_neq].
            rewrite /M2 upd_ne; [| reg_neq]. rewrite /M1 upd_ne; [exact Ha1 | reg_neq]. }
          assert (HM4a1' : rget M4 Ra1 = pa_add s2 t) by (rgne; exact HM4a1).
          (* +0x1c: c.addi a1, 1 *)
          iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.strncmp + 0x1c)) Ra1
                    (mword_of_int 1 : mword 6) M4 (K - 2)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc Hi1c").
          iIntros (CID7 Hs7) "Hcg Hpc".
          set (M5 := <[Regidx Ra1 := regval_into_reg
                        (add_vec (rget M4 Ra1)
                           (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> M4).
          change (<[Regidx Ra1 := regval_into_reg
                     (add_vec (rget M4 Ra1)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> M4) with M5.
          assert (HM5a1 : M5 !!! Regidx Ra1 = pa_add s2 (S t)).
          { rewrite /M5 upd_eq HM4a1'. apply snc_step. }
          assert (Hp1e : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x1c) : mword 64) 2
                         = mword_of_int (KernelSyms.strncmp + 0x1e))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp1e) in "Hpc".
          assert (HM5a2 : M5 !!! Regidx Ra2 = (mword_of_int (Z.of_nat (n - S t)) : mword 64)).
          { rewrite /M5 upd_ne; [| reg_neq]. rewrite /M4 upd_ne; [| reg_neq].
            rewrite /M3 upd_eq. exact HM3a2. }
          assert (HM5a2' : rget M5 Ra2 = (mword_of_int (Z.of_nat (n - S t)) : mword 64)) by (rgne; exact HM5a2).
          (* +0x1e: c.bnez a2, -0x14 *)
          assert (HEz2 : eq_vec (rget M5 Ra2) (zero_reg : mword 64) = true).
          { rewrite HM5a2'. assert (Hnst0 : (n - S t = 0)%nat) by lia. rewrite Hnst0. reflexivity. }
          assert (Hneq2 : neq_vec (rget M5 Ra2) (zero_reg : mword 64) = false).
          { unfold neq_vec. rewrite HEz2. reflexivity. }
          iPoseProof (snci_20 with "Htext") as "Hi20".
          iPoseProof (snci_22 with "Htext") as "Hi22".
          iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.strncmp + 0x1e))
                    (mword_of_int 246 : mword 8) (Cregidx (mword_of_int 4)) Ra2 M5 (K - 2)%nat b
                    ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hneq2
                    with "Hcg Hpc Hi1e").
          iIntros (CID8 Hs8) "Hcg Hpc".
          assert (Hp20 : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x1e) : mword 64) 2
                         = mword_of_int (KernelSyms.strncmp + 0x20))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp20) in "Hpc".
          (* +0x20: c.li a0, 0 *)
          iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.strncmp + 0x20)) Ra0
                    (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                    M5 (K - 2)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity)
                    with "Hcg Hpc Hi20").
          iIntros (CID9 Hs9) "Hcg Hpc".
          set (M6 := <[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> M5).
          change (<[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> M5) with M6.
          assert (Hp22 : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x20) : mword 64) 2
                         = mword_of_int (KernelSyms.strncmp + 0x22))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp22) in "Hpc".
          (* +0x22: c.j +0x10 -> +0x32 *)
          iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.strncmp + 0x22))
                    (sign_extend' 21 (concat_vec (mword_of_int 8 : mword 11) ('b"0")))
                    M6 (K - 2)%nat b ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi22").
          iIntros (CID10 Hs10). iNext. iIntros "Hcg Hpc".
          assert (Ht32 : add_vec (mword_of_int (KernelSyms.strncmp + 0x22) : mword 64)
                    (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 8 : mword 11) ('b"0"))))
                  = mword_of_int (KernelSyms.strncmp + 0x32))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Ht32) in "Hpc".
          assert (HM6sp : M6 !!! Regidx csp_rs1 = pa_stk sp0 2).
          { rewrite /M6 upd_ne; [| reg_neq]. rewrite /M5 upd_ne; [| reg_neq].
            rewrite /M4 upd_ne; [| reg_neq]. rewrite /M3 upd_ne; [| reg_neq].
            rewrite /M2 upd_ne; [| reg_neq]. rewrite /M1 upd_ne; [exact Hsp | reg_neq]. }
          assert (HM6a0 : M6 !!! Regidx Ra0 = (mword_of_int 0 : mword 64))
            by (rewrite /M6 upd_eq; reflexivity).
          assert (HM6thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                             M6 !!! Regidx r = mm !!! Regidx r).
          { intros r Hr Ncsp Ns0.
            rewrite /M6 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
            rewrite /M5 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
            rewrite /M4 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
            rewrite /M3 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
            rewrite /M2 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
            rewrite /M1 upd_ne; [apply Hthr; assumption | apply cs_ne; [vm_compute; reflexivity | exact Hr]]. }
          iSpecialize ("Hcont" $! CID10 with "[%]"); [wp_next_chain|].
          iApply ("Hcont" $! M6 with "[%] [%] [%] Hcg Hpc Hbuf1 Hbuf2").
          -- exact HM6sp.
          -- rewrite HM6a0. right. split; [exact Hnpos |]. right.
             split; [| reflexivity].
             intros j Hj. assert (Hjt : j = t \/ (j < t)%nat) by lia.
             destruct Hjt as [-> | Hjt].
             ++ split; [symmetry; exact Hgtft | exact Hnz1].
             ++ split; [apply Heq; exact Hjt |].
                intro Hzj. apply (Hnn j Hjt Hzj).
          -- exact HM6thr.
        * (* g t != f t: bne takes branch to +0x28 *)
          assert (Hneq : neq_vec (rget M2 Ra4) (rget M2 Ra5) = true).
          { unfold neq_vec. rewrite HM2a4' HM2a5' Eeq. reflexivity. }
          assert (Hgneq : f t <> g t).
          { intro Heq'. rewrite Heq' eq_vec_refl in Eeq. discriminate. }
          iPoseProof (snci_28 with "Htext") as "Hi28".
          iPoseProof (snci_2c with "Htext") as "Hi2c".
          iPoseProof (snci_30 with "Htext") as "Hi30".
          iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.strncmp + 0x14))
                    (mword_of_int 20 : mword 13) Ra5 Ra4 M2 (K - 2)%nat b
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hneq
                    ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi14").
          iNext. iIntros (CID4 Hs4) "Hcg Hpc".
          assert (Ht28 : add_vec (mword_of_int (KernelSyms.strncmp + 0x14) : mword 64)
                    (sign_extend' 64 (sign_extend' 13 (mword_of_int 20 : mword 13)))
                  = mword_of_int (KernelSyms.strncmp + 0x28))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Ht28) in "Hpc".
          iDestruct (bb_byte_acc s1 n t f dq1 Htn with "Hbuf1") as "[Hb1 Hback1]".
          iDestruct (bb_byte_acc s2 n t g dq2 Htn with "Hbuf2") as "[Hb2 Hback2]".
          assert (HM2a0 : M2 !!! Regidx Ra0 = pa_add s1 t).
          { rewrite /M2 upd_ne; [| reg_neq]. rewrite /M1 upd_ne; [exact Ha0 | reg_neq]. }
          assert (HM2a0' : rget M2 Ra0 = pa_add s1 t) by (rgne; exact HM2a0).
          assert (HM2a1 : M2 !!! Regidx Ra1 = pa_add s2 t).
          { rewrite /M2 upd_ne; [| reg_neq]. rewrite /M1 upd_ne; [exact Ha1 | reg_neq]. }
          assert (HM2a1' : rget M2 Ra1 = pa_add s2 t) by (rgne; exact HM2a1).
          (* +0x28: lbu a0, 0(a0) *)
          iApply (wp_lbu_s_sconf (kt := KT1) (ktd := ktf) (mword_of_int (KernelSyms.strncmp + 0x28)) Ra0 Ra0
                    (mword_of_int 0 : mword 12) M2 (K - 2)%nat (f t : mword 8) b (dqm:=dq1)
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc Hi28 [Hb1]").
          { iEval (rewrite HM2a0' addv_sext0). iExact "Hb1". }
          iIntros (CID5 Hs5) "Hcg Hpc Hb1".
          iEval (rewrite HM2a0' addv_sext0) in "Hb1".
          iDestruct ("Hback1" $! f with "[%] Hb1") as "Hbuf1"; [done |].
          set (M3 := <[Regidx Ra0 := regval_into_reg (zero_extend' 64 (f t : mword 8))]> M2).
          change (<[Regidx Ra0 := regval_into_reg (zero_extend' 64 (f t : mword 8))]> M2) with M3.
          assert (Hp2c : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x28) : mword 64) 4
                         = mword_of_int (KernelSyms.strncmp + 0x2c))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp2c) in "Hpc".
          assert (HM3a1 : M3 !!! Regidx Ra1 = pa_add s2 t).
          { rewrite /M3 upd_ne; [| reg_neq]. rewrite /M2 upd_ne; [| reg_neq].
            rewrite /M1 upd_ne; [exact Ha1 | reg_neq]. }
          assert (HM3a1' : rget M3 Ra1 = pa_add s2 t) by (rgne; exact HM3a1).
          (* +0x2c: lbu a5, 0(a1) *)
          iApply (wp_lbu_s_sconf (kt := KT1) (ktd := ktg) (mword_of_int (KernelSyms.strncmp + 0x2c)) Ra5 Ra1
                    (mword_of_int 0 : mword 12) M3 (K - 2)%nat (g t : mword 8) b (dqm:=dq2)
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc Hi2c [Hb2]").
          { iEval (rewrite HM3a1' addv_sext0). iExact "Hb2". }
          iIntros (CID6 Hs6) "Hcg Hpc Hb2".
          iEval (rewrite HM3a1' addv_sext0) in "Hb2".
          iDestruct ("Hback2" $! g with "[%] Hb2") as "Hbuf2"; [done |].
          set (M4 := <[Regidx Ra5 := regval_into_reg (zero_extend' 64 (g t : mword 8))]> M3).
          change (<[Regidx Ra5 := regval_into_reg (zero_extend' 64 (g t : mword 8))]> M3) with M4.
          assert (Hp30 : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x2c) : mword 64) 4
                         = mword_of_int (KernelSyms.strncmp + 0x30))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp30) in "Hpc".
          assert (HM4a0 : M4 !!! Regidx Ra0 = zero_extend' 64 (f t : mword 8)).
          { rewrite /M4 upd_ne; [| reg_neq]. rewrite /M3 upd_eq. reflexivity. }
          assert (HM4a0' : rget M4 Ra0 = zero_extend' 64 (f t : mword 8)) by (rgne; exact HM4a0).
          assert (HM4a5 : M4 !!! Regidx Ra5 = zero_extend' 64 (g t : mword 8))
            by (rewrite /M4 upd_eq; reflexivity).
          assert (HM4a5' : rget M4 Ra5 = zero_extend' 64 (g t : mword 8)) by (rgne; exact HM4a5).
          (* +0x30: c.subw a0, a5 *)
          iApply (wp_csubw_s_sconf (mword_of_int (KernelSyms.strncmp + 0x30))
                    Ra0 Ra0 Ra5 M4 (K - 2)%nat b
                    ltac:(vm_compute; discriminate)
                    ltac:(rdok)
                    with "Hcg Hpc Hi30").
          iIntros (CID7 Hs7) "Hcg Hpc".
          set (M5 := <[Regidx Ra0 := regval_into_reg
                        (sign_extend' 64
                           (sub_vec (subrange_vec_dec (rget M4 Ra0) 31 0 : mword 32)
                                    (subrange_vec_dec (rget M4 Ra5) 31 0 : mword 32)))]> M4).
          change (<[Regidx Ra0 := regval_into_reg
                     (sign_extend' 64
                        (sub_vec (subrange_vec_dec (rget M4 Ra0) 31 0 : mword 32)
                                 (subrange_vec_dec (rget M4 Ra5) 31 0 : mword 32)))]> M4) with M5.
          assert (HM5a0 : M5 !!! Regidx Ra0 = (mword_of_int (bv_unsigned (f t) - bv_unsigned (g t)) : mword 64)).
          { rewrite /M5 upd_eq HM4a0' HM4a5'. apply snc_subw_diff. }
          assert (Hp32 : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x30) : mword 64) 2
                         = mword_of_int (KernelSyms.strncmp + 0x32))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp32) in "Hpc".
          assert (HM5sp : M5 !!! Regidx csp_rs1 = pa_stk sp0 2).
          { rewrite /M5 upd_ne; [| reg_neq]. rewrite /M4 upd_ne; [| reg_neq].
            rewrite /M3 upd_ne; [| reg_neq]. rewrite /M2 upd_ne; [| reg_neq].
            rewrite /M1 upd_ne; [exact Hsp | reg_neq]. }
          assert (HM5thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                             M5 !!! Regidx r = mm !!! Regidx r).
          { intros r Hr Ncsp Ns0.
            rewrite /M5 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
            rewrite /M4 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
            rewrite /M3 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
            rewrite /M2 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
            rewrite /M1 upd_ne; [apply Hthr; assumption | apply cs_ne; [vm_compute; reflexivity | exact Hr]]. }
          iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
          iApply ("Hcont" $! M5 with "[%] [%] [%] Hcg Hpc Hbuf1 Hbuf2").
          -- exact HM5sp.
          -- rewrite HM5a0. right. split; [exact Hnpos |]. left.
             exists t. split.
             ++ unfold strncmp_stop. split_and!; [exact Htn | exact Hnn | exact Heq | right; exact Hgneq].
             ++ reflexivity.
          -- exact HM5thr.
    - (* rem = S rem': t < n - 1 *)
      assert (Htn : (t < n)%nat) by lia.
      assert (Hstn : (S t < n)%nat) by lia.
      assert (Hnstpos : (0 < n - S t)%nat) by lia.
      iPoseProof (snci_0a with "Htext") as "Hi0a".
      iPoseProof (snci_0e with "Htext") as "Hi0e".
      iDestruct (bb_byte_acc s1 n t f dq1 Htn with "Hbuf1") as "[Hb1 Hback1]".
      assert (HMa0 : rget M Ra0 = pa_add s1 t) by (rgne; exact Ha0).
      (* +0x0a: lbu a5, 0(a0) *)
      iApply (wp_lbu_s_sconf (kt := KT1) (ktd := ktf) (mword_of_int (KernelSyms.strncmp + 0x0a)) Ra5 Ra0
                (mword_of_int 0 : mword 12) M (K - 2)%nat (f t : mword 8) b (dqm:=dq1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi0a [Hb1]").
      { iEval (rewrite HMa0 addv_sext0). iExact "Hb1". }
      iIntros (CID1 Hs1) "Hcg Hpc Hb1".
      iEval (rewrite HMa0 addv_sext0) in "Hb1".
      iDestruct ("Hback1" $! f with "[%] Hb1") as "Hbuf1"; [done |].
      set (M1 := <[Regidx Ra5 := regval_into_reg (zero_extend' 64 (f t : mword 8))]> M).
      change (<[Regidx Ra5 := regval_into_reg (zero_extend' 64 (f t : mword 8))]> M) with M1.
      assert (Hp0e : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x0a) : mword 64) 4
                     = mword_of_int (KernelSyms.strncmp + 0x0e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp0e) in "Hpc".
      assert (HM1a5 : M1 !!! Regidx Ra5 = zero_extend' 64 (f t : mword 8))
        by (rewrite /M1 upd_eq; reflexivity).
      assert (HM1a5' : rget M1 Ra5 = zero_extend' 64 (f t : mword 8)) by (rgne; exact HM1a5).
      (* +0x0e: c.beqz a5, +0x1a -> +0x28 *)
      destruct (eq_vec (zero_extend' 64 (f t : mword 8) : mword 64) (zero_reg : mword 64)) eqn:Ez.
      + (* f t = 0: early exit at +0x28 *)
        assert (Hzt : f t = (mword_of_int 0 : mword 8)) by (apply bc_zext8_zero; exact Ez).
        iPoseProof (snci_28 with "Htext") as "Hi28".
        iPoseProof (snci_2c with "Htext") as "Hi2c".
        iPoseProof (snci_30 with "Htext") as "Hi30".
        iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.strncmp + 0x0e))
                  (mword_of_int 13 : mword 8) (Cregidx (mword_of_int 7)) Ra5 M1 (K - 2)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rewrite HM1a5'; exact Ez) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi0e").
        iNext. iIntros (CID2 Hs2) "Hcg Hpc".
        assert (Ht28 : add_vec (mword_of_int (KernelSyms.strncmp + 0x0e) : mword 64)
                  (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 13 : mword 8) ('b"0"))))
                = mword_of_int (KernelSyms.strncmp + 0x28))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Ht28) in "Hpc".
        iDestruct (bb_byte_acc s1 n t f dq1 Htn with "Hbuf1") as "[Hb1 Hback1]".
        iDestruct (bb_byte_acc s2 n t g dq2 Htn with "Hbuf2") as "[Hb2 Hback2]".
        assert (HM1a0 : M1 !!! Regidx Ra0 = pa_add s1 t) by (rewrite /M1 upd_ne; [exact Ha0 | reg_neq]).
        assert (HM1a0' : rget M1 Ra0 = pa_add s1 t) by (rgne; exact HM1a0).
        assert (HM1a1 : M1 !!! Regidx Ra1 = pa_add s2 t) by (rewrite /M1 upd_ne; [exact Ha1 | reg_neq]).
        assert (HM1a1' : rget M1 Ra1 = pa_add s2 t) by (rgne; exact HM1a1).
        iApply (wp_lbu_s_sconf (kt := KT1) (ktd := ktf) (mword_of_int (KernelSyms.strncmp + 0x28)) Ra0 Ra0
                  (mword_of_int 0 : mword 12) M1 (K - 2)%nat (f t : mword 8) b (dqm:=dq1)
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi28 [Hb1]").
        { iEval (rewrite HM1a0' addv_sext0). iExact "Hb1". }
        iIntros (CID3 Hs3) "Hcg Hpc Hb1".
        iEval (rewrite HM1a0' addv_sext0) in "Hb1".
        iDestruct ("Hback1" $! f with "[%] Hb1") as "Hbuf1"; [done |].
        set (M2 := <[Regidx Ra0 := regval_into_reg (zero_extend' 64 (f t : mword 8))]> M1).
        change (<[Regidx Ra0 := regval_into_reg (zero_extend' 64 (f t : mword 8))]> M1) with M2.
        assert (Hp2c : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x28) : mword 64) 4
                       = mword_of_int (KernelSyms.strncmp + 0x2c))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp2c) in "Hpc".
        assert (HM2a1 : M2 !!! Regidx Ra1 = pa_add s2 t) by (rewrite /M2 upd_ne; [exact HM1a1 | reg_neq]).
        assert (HM2a1' : rget M2 Ra1 = pa_add s2 t) by (rgne; exact HM2a1).
        iApply (wp_lbu_s_sconf (kt := KT1) (ktd := ktg) (mword_of_int (KernelSyms.strncmp + 0x2c)) Ra5 Ra1
                  (mword_of_int 0 : mword 12) M2 (K - 2)%nat (g t : mword 8) b (dqm:=dq2)
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi2c [Hb2]").
        { iEval (rewrite HM2a1' addv_sext0). iExact "Hb2". }
        iIntros (CID4 Hs4) "Hcg Hpc Hb2".
        iEval (rewrite HM2a1' addv_sext0) in "Hb2".
        iDestruct ("Hback2" $! g with "[%] Hb2") as "Hbuf2"; [done |].
        set (M3 := <[Regidx Ra5 := regval_into_reg (zero_extend' 64 (g t : mword 8))]> M2).
        change (<[Regidx Ra5 := regval_into_reg (zero_extend' 64 (g t : mword 8))]> M2) with M3.
        assert (Hp30 : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x2c) : mword 64) 4
                       = mword_of_int (KernelSyms.strncmp + 0x30))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp30) in "Hpc".
        assert (HM3a0 : M3 !!! Regidx Ra0 = zero_extend' 64 (f t : mword 8)).
        { rewrite /M3 upd_ne; [| reg_neq]. rewrite /M2 upd_eq. reflexivity. }
        assert (HM3a0' : rget M3 Ra0 = zero_extend' 64 (f t : mword 8)) by (rgne; exact HM3a0).
        assert (HM3a5 : M3 !!! Regidx Ra5 = zero_extend' 64 (g t : mword 8)) by (rewrite /M3 upd_eq; reflexivity).
        assert (HM3a5' : rget M3 Ra5 = zero_extend' 64 (g t : mword 8)) by (rgne; exact HM3a5).
        iApply (wp_csubw_s_sconf (mword_of_int (KernelSyms.strncmp + 0x30))
                  Ra0 Ra0 Ra5 M3 (K - 2)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi30").
        iIntros (CID5 Hs5) "Hcg Hpc".
        set (M4 := <[Regidx Ra0 := regval_into_reg
                      (sign_extend' 64
                         (sub_vec (subrange_vec_dec (rget M3 Ra0) 31 0 : mword 32)
                                  (subrange_vec_dec (rget M3 Ra5) 31 0 : mword 32)))]> M3).
        change (<[Regidx Ra0 := regval_into_reg
                   (sign_extend' 64
                      (sub_vec (subrange_vec_dec (rget M3 Ra0) 31 0 : mword 32)
                               (subrange_vec_dec (rget M3 Ra5) 31 0 : mword 32)))]> M3) with M4.
        assert (HM4a0 : M4 !!! Regidx Ra0 = (mword_of_int (bv_unsigned (f t) - bv_unsigned (g t)) : mword 64)).
        { rewrite /M4 upd_eq /regval_into_reg HM3a0' HM3a5'. apply snc_subw_diff. }
        assert (HM4a0' : rget M4 Ra0 = (mword_of_int (bv_unsigned (f t) - bv_unsigned (g t)) : mword 64)) by (rgne; exact HM4a0).
        assert (HM4sp : M4 !!! Regidx csp_rs1 = pa_stk sp0 2).
        { rewrite /M4 upd_ne; [| reg_neq]. rewrite /M3 upd_ne; [| reg_neq].
          rewrite /M2 upd_ne; [| reg_neq]. rewrite /M1 upd_ne; [exact Hsp | reg_neq]. }
        assert (HM4thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                           M4 !!! Regidx r = mm !!! Regidx r).
        { intros r Hr Ncsp Ns0.
          rewrite /M4 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
          rewrite /M3 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
          rewrite /M2 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
          rewrite /M1 upd_ne; [apply Hthr; assumption | apply cs_ne; [vm_compute; reflexivity | exact Hr]]. }
        iSpecialize ("Hcont" $! CID5 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! M4 with "[%] [%] [%] Hcg Hpc Hbuf1 Hbuf2").
        -- exact HM4sp.
        -- rewrite HM4a0. right. split; [exact Hnpos |]. left.
           exists t. split.
           ++ unfold strncmp_stop. split_and!; [exact Htn | exact Hnn | exact Heq | left; exact Hzt].
           ++ reflexivity.
        -- exact HM4thr.
      + (* f t != 0: continue to +0x10 *)
        assert (Hnz1 : f t <> (mword_of_int 0 : mword 8)).
        { intro He. rewrite He bc_zext8_iszero in Ez. discriminate. }
        iPoseProof (snci_10 with "Htext") as "Hi10".
        iPoseProof (snci_14 with "Htext") as "Hi14".
        iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.strncmp + 0x0e))
                  (mword_of_int 13 : mword 8) (Cregidx (mword_of_int 7)) Ra5 M1 (K - 2)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rewrite HM1a5'; exact Ez)
                  with "Hcg Hpc Hi0e").
        iIntros (CID2 Hs2) "Hcg Hpc".
        assert (Hp10 : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x0e) : mword 64) 2
                       = mword_of_int (KernelSyms.strncmp + 0x10))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp10) in "Hpc".
        iDestruct (bb_byte_acc s2 n t g dq2 Htn with "Hbuf2") as "[Hb2 Hback2]".
        assert (HM1a1 : M1 !!! Regidx Ra1 = pa_add s2 t) by (rewrite /M1 upd_ne; [exact Ha1 | reg_neq]).
        assert (HM1a1' : rget M1 Ra1 = pa_add s2 t) by (rgne; exact HM1a1).
        (* +0x10: lbu a4, 0(a1) *)
        iApply (wp_lbu_s_sconf (kt := KT1) (ktd := ktg) (mword_of_int (KernelSyms.strncmp + 0x10)) Ra4 Ra1
                  (mword_of_int 0 : mword 12) M1 (K - 2)%nat (g t : mword 8) b (dqm:=dq2)
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi10 [Hb2]").
        { iEval (rewrite HM1a1' addv_sext0). iExact "Hb2". }
        iIntros (CID3 Hs3) "Hcg Hpc Hb2".
        iEval (rewrite HM1a1' addv_sext0) in "Hb2".
        iDestruct ("Hback2" $! g with "[%] Hb2") as "Hbuf2"; [done |].
        set (M2 := <[Regidx Ra4 := regval_into_reg (zero_extend' 64 (g t : mword 8))]> M1).
        change (<[Regidx Ra4 := regval_into_reg (zero_extend' 64 (g t : mword 8))]> M1) with M2.
        assert (Hp14 : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x10) : mword 64) 4
                       = mword_of_int (KernelSyms.strncmp + 0x14))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp14) in "Hpc".
        assert (HM2a4 : M2 !!! Regidx Ra4 = zero_extend' 64 (g t : mword 8))
          by (rewrite /M2 upd_eq; reflexivity).
        assert (HM2a4' : rget M2 Ra4 = zero_extend' 64 (g t : mword 8)) by (rgne; exact HM2a4).
        assert (HM2a5 : M2 !!! Regidx Ra5 = zero_extend' 64 (f t : mword 8))
          by (rewrite /M2 upd_ne; [exact HM1a5 | reg_neq]).
        assert (HM2a5' : rget M2 Ra5 = zero_extend' 64 (f t : mword 8)) by (rgne; exact HM2a5).
        (* +0x14: bne a4, a5, +0x14 -> +0x28 *)
        destruct (eq_vec (zero_extend' 64 (g t : mword 8) : mword 64) (zero_extend' 64 (f t : mword 8) : mword 64)) eqn:Eeq.
        * (* g t = f t: bne falls through to +0x18 *)
          assert (Hgtft : g t = f t).
          { apply eq_vec_true_iff in Eeq. apply (f_equal bv_unsigned) in Eeq.
            unfold zero_extend', Operators_mwords.zero_extend, Operators_mwords.extz_vec,
              to_word, get_word, MachineWord.MachineWord.zero_extend in Eeq.
            rewrite !bv_zero_extend_unsigned in Eeq; try (vm_compute; intro Hc; discriminate Hc).
            apply bv_eq. exact Eeq. }
          assert (Hneq : neq_vec (rget M2 Ra4) (rget M2 Ra5) = false).
          { unfold neq_vec. rewrite HM2a4' HM2a5' Hgtft eq_vec_refl. reflexivity. }
          iPoseProof (snci_18 with "Htext") as "Hi18".
          iPoseProof (snci_1a with "Htext") as "Hi1a".
          iPoseProof (snci_1c with "Htext") as "Hi1c".
          iPoseProof (snci_1e with "Htext") as "Hi1e".
          iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.strncmp + 0x14))
                    (mword_of_int 20 : mword 13) Ra5 Ra4 M2 (K - 2)%nat b
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hneq
                    with "Hcg Hpc Hi14").
          iIntros (CID4 Hs4) "Hcg Hpc".
          assert (Hp18 : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x14) : mword 64) 4
                         = mword_of_int (KernelSyms.strncmp + 0x18))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp18) in "Hpc".
          assert (HM2a2 : M2 !!! Regidx Ra2 = (mword_of_int (Z.of_nat (n - t)) : mword 64)).
          { rewrite /M2 upd_ne; [| reg_neq]. rewrite /M1 upd_ne; [exact Ha2 | reg_neq]. }
          assert (HM2a2' : rget M2 Ra2 = (mword_of_int (Z.of_nat (n - t)) : mword 64)) by (rgne; exact HM2a2).
          (* +0x18: c.addiw a2, -1 *)
          iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.strncmp + 0x18)) Ra2
                    (mword_of_int 63 : mword 6) M2 (K - 2)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc Hi18").
          iIntros (CID5 Hs5) "Hcg Hpc".
          set (M3 := <[Regidx Ra2 := regval_into_reg
                        (sign_extend' 64 (subrange_vec_dec
                           (add_vec (M2 !!! Regidx Ra2)
                              (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))]> M2).
          change (<[Regidx Ra2 := regval_into_reg
                     (sign_extend' 64 (subrange_vec_dec
                        (add_vec (M2 !!! Regidx Ra2)
                           (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))]> M2) with M3.
          assert (HM3a2 : M3 !!! Regidx Ra2 = (mword_of_int (Z.of_nat (n - S t)) : mword 64)).
          { rewrite /M3 upd_eq /regval_into_reg HM2a2.
            rewrite (snc_dec_a2 n t Htn Hn31).
            apply bv_eq.
            unfold sign_extend', Operators_mwords.sign_extend, Operators_mwords.exts_vec, to_word, get_word.
            rewrite bv_sign_extend_unsigned. unfold bv_signed. rewrite !subrange_31_0_unsigned !moi64_unsigned.
            unfold MachineWord.Z_idx, bv_half_modulus, bv_modulus, bv_swrap, bv_wrap.
            change (Z.to_N (31 - 0 + 1)) with 32%N.
            change (Z.to_N 64) with 64%N.
            change (bv_half_modulus 32%N) with 2147483648%Z.
            change (bv_modulus 32%N) with 4294967296%Z.
            change (bv_modulus 64%N) with 18446744073709551616%Z.
            change (bv_modulus 64) with 18446744073709551616%Z.
            replace ((Z.of_nat (n - S t)) mod 18446744073709551616) with (Z.of_nat (n - S t)) by (symmetry; apply Z.mod_small; lia).
            replace ((Z.of_nat (n - S t)) mod 4294967296) with (Z.of_nat (n - S t)) by (symmetry; apply Z.mod_small; lia).
            replace ((Z.of_nat (n - S t) + 2147483648) mod 4294967296) with (Z.of_nat (n - S t) + 2147483648) by (symmetry; apply Z.mod_small; lia).
            replace (Z.of_nat (n - S t) + 2147483648 - 2147483648) with (Z.of_nat (n - S t)) by lia.
            apply Z.mod_small. lia. }
          assert (HM3a2' : rget M3 Ra2 = (mword_of_int (Z.of_nat (n - S t)) : mword 64)) by (rgne; exact HM3a2).
          assert (Hp1a : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x18) : mword 64) 2
                         = mword_of_int (KernelSyms.strncmp + 0x1a))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp1a) in "Hpc".
          assert (HM3a0 : M3 !!! Regidx Ra0 = pa_add s1 t).
          { rewrite /M3 upd_ne; [| reg_neq]. rewrite /M2 upd_ne; [| reg_neq].
            rewrite /M1 upd_ne; [exact Ha0 | reg_neq]. }
          assert (HM3a0' : rget M3 Ra0 = pa_add s1 t) by (rgne; exact HM3a0).
          (* +0x1a: c.addi a0, 1 *)
          iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.strncmp + 0x1a)) Ra0
                    (mword_of_int 1 : mword 6) M3 (K - 2)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc Hi1a").
          iIntros (CID6 Hs6) "Hcg Hpc".
          set (M4 := <[Regidx Ra0 := regval_into_reg
                        (add_vec (rget M3 Ra0)
                           (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> M3).
          change (<[Regidx Ra0 := regval_into_reg
                     (add_vec (rget M3 Ra0)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> M3) with M4.
          assert (HM4a0 : M4 !!! Regidx Ra0 = pa_add s1 (S t)).
          { rewrite /M4 upd_eq HM3a0'. apply snc_step. }
          assert (HM4a0' : rget M4 Ra0 = pa_add s1 (S t)) by (rgne; exact HM4a0).
          assert (Hp1c : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x1a) : mword 64) 2
                         = mword_of_int (KernelSyms.strncmp + 0x1c))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp1c) in "Hpc".
          assert (HM4a1 : M4 !!! Regidx Ra1 = pa_add s2 t).
          { rewrite /M4 upd_ne; [| reg_neq]. rewrite /M3 upd_ne; [| reg_neq].
            rewrite /M2 upd_ne; [| reg_neq]. rewrite /M1 upd_ne; [exact Ha1 | reg_neq]. }
          assert (HM4a1' : rget M4 Ra1 = pa_add s2 t) by (rgne; exact HM4a1).
          (* +0x1c: c.addi a1, 1 *)
          iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.strncmp + 0x1c)) Ra1
                    (mword_of_int 1 : mword 6) M4 (K - 2)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc Hi1c").
          iIntros (CID7 Hs7) "Hcg Hpc".
          set (M5 := <[Regidx Ra1 := regval_into_reg
                        (add_vec (rget M4 Ra1)
                           (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> M4).
          change (<[Regidx Ra1 := regval_into_reg
                     (add_vec (rget M4 Ra1)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> M4) with M5.
          assert (HM5a1 : M5 !!! Regidx Ra1 = pa_add s2 (S t)).
          { rewrite /M5 upd_eq HM4a1'. apply snc_step. }
          assert (HM5a1' : rget M5 Ra1 = pa_add s2 (S t)) by (rgne; exact HM5a1).
          assert (Hp1e : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x1c) : mword 64) 2
                         = mword_of_int (KernelSyms.strncmp + 0x1e))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp1e) in "Hpc".
          assert (HM5a2 : M5 !!! Regidx Ra2 = (mword_of_int (Z.of_nat (n - S t)) : mword 64)).
          { rewrite /M5 upd_ne; [| reg_neq]. rewrite /M4 upd_ne; [| reg_neq].
            rewrite /M3 upd_eq. exact HM3a2. }
          assert (HM5a2' : rget M5 Ra2 = (mword_of_int (Z.of_nat (n - S t)) : mword 64)) by (rgne; exact HM5a2).
          (* +0x1e: c.bnez a2, -0x14 *)
          assert (HEz2 : eq_vec (rget M5 Ra2) (zero_reg : mword 64) = false).
          { rewrite HM5a2'. destruct (eq_vec (mword_of_int (Z.of_nat (n - S t)) : mword 64) zero_reg) eqn:E2; [| reflexivity]. exfalso.
            apply eq_vec_true_iff in E2. apply (f_equal bv_unsigned) in E2.
            change (bv_unsigned (mword_of_int (Z.of_nat (n - S t)) : mword 64)) with (Z.of_nat (n - S t) mod 18446744073709551616)%Z in E2.
            change (bv_unsigned (zero_reg : mword 64)) with 0%Z in E2.
            rewrite Z.mod_small in E2; [lia | split; [apply Nat2Z.is_nonneg | lia]]. }
          assert (Hneq2 : neq_vec (rget M5 Ra2) (zero_reg : mword 64) = true).
          { unfold neq_vec. rewrite HEz2. reflexivity. }
          iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.strncmp + 0x1e))
                    (mword_of_int 246 : mword 8) (Cregidx (mword_of_int 4)) Ra2 M5 (K - 2)%nat b
                    ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hneq2
                    ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi1e").
          iNext. iIntros (CID8 Hs8) "Hcg Hpc".
          assert (Ht0a : add_vec (mword_of_int (KernelSyms.strncmp + 0x1e) : mword 64)
                    (sign_extend' 64 (sign_extend' 9 (concat_vec (mword_of_int 246 : mword 8) ('b"0"))))
                  = mword_of_int (KernelSyms.strncmp + 0x0a))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Ht0a) in "Hpc".
          assert (HM5sp : M5 !!! Regidx csp_rs1 = pa_stk sp0 2).
          { rewrite /M5 upd_ne; [| reg_neq]. rewrite /M4 upd_ne; [| reg_neq].
            rewrite /M3 upd_ne; [| reg_neq]. rewrite /M2 upd_ne; [| reg_neq].
            rewrite /M1 upd_ne; [exact Hsp | reg_neq]. }
          assert (HM5a0 : M5 !!! Regidx Ra0 = pa_add s1 (S t)).
          { rewrite /M5 upd_ne; [| reg_neq]. rewrite /M4 upd_eq. exact HM4a0. }
          assert (HM5thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                             M5 !!! Regidx r = mm !!! Regidx r).
          { intros r Hr Ncsp Ns0.
            rewrite /M5 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
            rewrite /M4 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
            rewrite /M3 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
            rewrite /M2 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
            rewrite /M1 upd_ne; [apply Hthr; assumption | apply cs_ne; [vm_compute; reflexivity | exact Hr]]. }
          assert (Hsum' : (S t + rem)%nat = (n - 1)%nat) by lia.
          assert (Hnn' : bb_nonul f (S t)) by (apply bb_nonul_step; [exact Hnn | exact Hnz1]).
          assert (Heq' : forall j : nat, (j < S t)%nat -> f j = g j).
          { intros j Hj. assert (Hjt : j = t \/ (j < t)%nat) by lia.
            destruct Hjt as [-> | Hjt].
            - symmetry; exact Hgtft.
            - apply Heq; exact Hjt. }
          iApply (IH (S t) M5 CID8 ltac:(intro Hb; rewrite Hs8; [| exact Hb]; rewrite Hs7; [| exact Hb]; rewrite Hs6; [| exact Hb]; rewrite Hs5; [| exact Hb]; rewrite Hs4; [| exact Hb]; rewrite Hs3; [| exact Hb]; rewrite Hs2; [| exact Hb]; rewrite Hs1; [| exact Hb]; exact (Hchain Hb)) Hsum' Hnn' Heq' HM5sp HM5a0 HM5a1 HM5a2 HM5thr with "Hcg Htext Hpc Hbuf1 Hbuf2 Hcont").
        * (* g t != f t: bne takes branch to +0x28 *)
          assert (Hneq : neq_vec (rget M2 Ra4) (rget M2 Ra5) = true).
          { unfold neq_vec. rewrite HM2a4' HM2a5' Eeq. reflexivity. }
          assert (Hgneq : f t <> g t).
          { intro Heq'. rewrite Heq' eq_vec_refl in Eeq. discriminate. }
          iPoseProof (snci_28 with "Htext") as "Hi28".
          iPoseProof (snci_2c with "Htext") as "Hi2c".
          iPoseProof (snci_30 with "Htext") as "Hi30".
          iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.strncmp + 0x14))
                    (mword_of_int 20 : mword 13) Ra5 Ra4 M2 (K - 2)%nat b
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hneq
                    ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi14").
          iNext. iIntros (CID4 Hs4) "Hcg Hpc".
          assert (Ht28 : add_vec (mword_of_int (KernelSyms.strncmp + 0x14) : mword 64)
                    (sign_extend' 64 (sign_extend' 13 (mword_of_int 20 : mword 13)))
                  = mword_of_int (KernelSyms.strncmp + 0x28))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Ht28) in "Hpc".
          iDestruct (bb_byte_acc s1 n t f dq1 Htn with "Hbuf1") as "[Hb1 Hback1]".
          iDestruct (bb_byte_acc s2 n t g dq2 Htn with "Hbuf2") as "[Hb2 Hback2]".
          assert (HM2a0 : M2 !!! Regidx Ra0 = pa_add s1 t).
          { rewrite /M2 upd_ne; [| reg_neq]. rewrite /M1 upd_ne; [exact Ha0 | reg_neq]. }
          assert (HM2a0' : rget M2 Ra0 = pa_add s1 t) by (rgne; exact HM2a0).
          assert (HM2a1 : M2 !!! Regidx Ra1 = pa_add s2 t).
          { rewrite /M2 upd_ne; [| reg_neq]. rewrite /M1 upd_ne; [exact Ha1 | reg_neq]. }
          assert (HM2a1' : rget M2 Ra1 = pa_add s2 t) by (rgne; exact HM2a1).
          (* +0x28: lbu a0, 0(a0) *)
          iApply (wp_lbu_s_sconf (kt := KT1) (ktd := ktf) (mword_of_int (KernelSyms.strncmp + 0x28)) Ra0 Ra0
                    (mword_of_int 0 : mword 12) M2 (K - 2)%nat (f t : mword 8) b (dqm:=dq1)
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc Hi28 [Hb1]").
          { iEval (rewrite HM2a0' addv_sext0). iExact "Hb1". }
          iIntros (CID5 Hs5) "Hcg Hpc Hb1".
          iEval (rewrite HM2a0' addv_sext0) in "Hb1".
          iDestruct ("Hback1" $! f with "[%] Hb1") as "Hbuf1"; [done |].
          set (M3 := <[Regidx Ra0 := regval_into_reg (zero_extend' 64 (f t : mword 8))]> M2).
          change (<[Regidx Ra0 := regval_into_reg (zero_extend' 64 (f t : mword 8))]> M2) with M3.
          assert (Hp2c : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x28) : mword 64) 4
                         = mword_of_int (KernelSyms.strncmp + 0x2c))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp2c) in "Hpc".
          assert (HM3a1 : M3 !!! Regidx Ra1 = pa_add s2 t).
          { rewrite /M3 upd_ne; [| reg_neq]. rewrite /M2 upd_ne; [| reg_neq].
            rewrite /M1 upd_ne; [exact Ha1 | reg_neq]. }
          assert (HM3a1' : rget M3 Ra1 = pa_add s2 t) by (rgne; exact HM3a1).
          (* +0x2c: lbu a5, 0(a1) *)
          iApply (wp_lbu_s_sconf (kt := KT1) (ktd := ktg) (mword_of_int (KernelSyms.strncmp + 0x2c)) Ra5 Ra1
                    (mword_of_int 0 : mword 12) M3 (K - 2)%nat (g t : mword 8) b (dqm:=dq2)
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc Hi2c [Hb2]").
          { iEval (rewrite HM3a1' addv_sext0). iExact "Hb2". }
          iIntros (CID6 Hs6) "Hcg Hpc Hb2".
          iEval (rewrite HM3a1' addv_sext0) in "Hb2".
          iDestruct ("Hback2" $! g with "[%] Hb2") as "Hbuf2"; [done |].
          set (M4 := <[Regidx Ra5 := regval_into_reg (zero_extend' 64 (g t : mword 8))]> M3).
          change (<[Regidx Ra5 := regval_into_reg (zero_extend' 64 (g t : mword 8))]> M3) with M4.
          assert (Hp30 : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x2c) : mword 64) 4
                         = mword_of_int (KernelSyms.strncmp + 0x30))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp30) in "Hpc".
          assert (HM4a0 : M4 !!! Regidx Ra0 = zero_extend' 64 (f t : mword 8)).
          { rewrite /M4 upd_ne; [| reg_neq]. rewrite /M3 upd_eq. reflexivity. }
          assert (HM4a0' : rget M4 Ra0 = zero_extend' 64 (f t : mword 8)) by (rgne; exact HM4a0).
          assert (HM4a5 : M4 !!! Regidx Ra5 = zero_extend' 64 (g t : mword 8))
            by (rewrite /M4 upd_eq; reflexivity).
          assert (HM4a5' : rget M4 Ra5 = zero_extend' 64 (g t : mword 8)) by (rgne; exact HM4a5).
          (* +0x30: c.subw a0, a5 *)
          iApply (wp_csubw_s_sconf (mword_of_int (KernelSyms.strncmp + 0x30))
                    Ra0 Ra0 Ra5 M4 (K - 2)%nat b
                    ltac:(vm_compute; discriminate)
                    ltac:(rdok)
                    with "Hcg Hpc Hi30").
          iIntros (CID7 Hs7) "Hcg Hpc".
          set (M5 := <[Regidx Ra0 := regval_into_reg
                        (sign_extend' 64
                           (sub_vec (subrange_vec_dec (rget M4 Ra0) 31 0 : mword 32)
                                    (subrange_vec_dec (rget M4 Ra5) 31 0 : mword 32)))]> M4).
          change (<[Regidx Ra0 := regval_into_reg
                     (sign_extend' 64
                        (sub_vec (subrange_vec_dec (rget M4 Ra0) 31 0 : mword 32)
                                 (subrange_vec_dec (rget M4 Ra5) 31 0 : mword 32)))]> M4) with M5.
          assert (HM5a0 : M5 !!! Regidx Ra0 = (mword_of_int (bv_unsigned (f t) - bv_unsigned (g t)) : mword 64)).
          { rewrite /M5 upd_eq /regval_into_reg HM4a0' HM4a5'. apply snc_subw_diff. }
          assert (HM5sp : M5 !!! Regidx csp_rs1 = pa_stk sp0 2).
          { rewrite /M5 upd_ne; [| reg_neq]. rewrite /M4 upd_ne; [| reg_neq].
            rewrite /M3 upd_ne; [| reg_neq]. rewrite /M2 upd_ne; [| reg_neq].
            rewrite /M1 upd_ne; [exact Hsp | reg_neq]. }
          assert (HM5thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                             M5 !!! Regidx r = mm !!! Regidx r).
          { intros r Hr Ncsp Ns0.
            rewrite /M5 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
            rewrite /M4 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
            rewrite /M3 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
            rewrite /M2 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
            rewrite /M1 upd_ne; [apply Hthr; assumption | apply cs_ne; [vm_compute; reflexivity | exact Hr]]. }
          iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
          iApply ("Hcont" $! M5 with "[%] [%] [%] Hcg Hpc Hbuf1 Hbuf2").
          -- exact HM5sp.
          -- rewrite HM5a0. right. split; [exact Hnpos |]. left.
             exists t. split.
             ++ unfold strncmp_stop. split_and!; [exact Htn | exact Hnn | exact Heq | right; exact Hgneq].
             ++ reflexivity.
          -- exact HM5thr.
  Qed.

  Lemma wp_strncmp_sconf (mm : regfile)
      (n : nat) (f g : nat -> bv 8) (K : nat) (dq1 dq2 : dfrac) (b : bool) (p : mword 64)
    : wp_strncmp_sconf_body ktf ktg mm n f g K dq1 dq2 b p.
  Proof.
    cbv beta delta [wp_strncmp_sconf_body].
    intros pcE s1 s2 ret_tgt HK Ha2 Hn31.
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg #Htext Hpc Hbuf1 Hbuf2 Hcont".
    iPoseProof (snci_00 with "Htext") as "Hi00".
    iPoseProof (snci_02 with "Htext") as "Hi02".
    iPoseProof (snci_04 with "Htext") as "Hi04".
    iPoseProof (snci_06 with "Htext") as "Hi06".
    iPoseProof (snci_08 with "Htext") as "Hi08".
    (* +0x00: c.addi sp, -16 *)
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 48 : mword 6) mm K 2 b
              ltac:(lia) (snc_push (mm !!! Regidx csp_rs1))
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (mm !!! Regidx csp_rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> mm).
    change (<[Regidx csp_rs1 := regval_into_reg
               (add_vec (mm !!! Regidx csp_rs1)
                  (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> mm) with R1.
    assert (HR1sp : R1 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /R1 upd_eq; apply snc_push).
    assert (Hp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.strncmp + 0x02))
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
    (* +0x02: c.sdsp ra, 8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.strncmp + 0x02))
              (mword_of_int 1 : mword 6) Rra R1 (K - 2)%nat u1 b
              with "Hcg Hpc Hi02 [Hb1]").
    { iEval (rewrite Hpa1). iExact "Hb1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hb1". iEval (rewrite Hpa1) in "Hb1".
    assert (HR1ra : R1 !!! Regidx Rra = mm !!! Regidx Rra)
      by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (HR1ra' : forall CID' : CpuId, rget (CID := CID') R1 Rra = mm !!! Regidx Rra)
      by (intros CID'; rgne; exact HR1ra).
    iEval (rewrite HR1ra') in "Hb1".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x02) : mword 64) 2
                   = mword_of_int (KernelSyms.strncmp + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    (* +0x04: c.sdsp s0, 0(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.strncmp + 0x04))
              (mword_of_int 0 : mword 6) Rs0 R1 (K - 2)%nat u2 b
              with "Hcg Hpc Hi04 [Hb2]").
    { iEval (rewrite Hpa2). iExact "Hb2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hb2". iEval (rewrite Hpa2) in "Hb2".
    assert (HR1s0 : R1 !!! Regidx Rs0 = mm !!! Regidx Rs0)
      by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (HR1s0' : forall CID' : CpuId, rget (CID := CID') R1 Rs0 = mm !!! Regidx Rs0)
      by (intros CID'; rgne; exact HR1s0).
    iEval (rewrite HR1s0') in "Hb2".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x04) : mword 64) 2
                   = mword_of_int (KernelSyms.strncmp + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    (* +0x06: c.addi4spn s0, sp, 16 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.strncmp + 0x06))
              (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) Rs0 R1 (K - 2)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok)
              with "Hcg Hpc Hi06").
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1).
    change (<[Regidx Rs0 := regval_into_reg
               (add_vec (R1 !!! Regidx csp_rs1)
                  (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1) with R2.
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x06) : mword 64) 2
                   = mword_of_int (KernelSyms.strncmp + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    assert (HR2a2 : R2 !!! Regidx Ra2 = (mword_of_int (Z.of_nat n) : mword 64)).
    { rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [exact Ha2 | reg_neq]. }
    assert (HR2a2' : rget R2 Ra2 = (mword_of_int (Z.of_nat n) : mword 64)) by (rgne; exact HR2a2).
    assert (HR2sp : R2 !!! Regidx csp_rs1 = pa_stk sp0 2).
    { rewrite /R2 upd_ne; [| reg_neq]. exact HR1sp. }
    assert (HR2a0 : R2 !!! Regidx Ra0 = s1).
    { rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [reflexivity | reg_neq]. }
    assert (HR2a1 : R2 !!! Regidx Ra1 = s2).
    { rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [reflexivity | reg_neq]. }
    assert (HR2thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                       R2 !!! Regidx r = mm !!! Regidx r).
    { intros r Hr Ncsp Ns0.
      rewrite /R2 upd_ne; [| intro He; injection He as He'; congruence].
      rewrite /R1 upd_ne; [reflexivity | intro He; injection He as He'; congruence]. }
    (* +0x08: c.beqz a2, +0x24 *)
    destruct (eq_vec (mword_of_int (Z.of_nat n) : mword 64) (zero_reg : mword 64)) eqn:Ea2.
    - (* n = 0 *)
      assert (Hn0 : n = 0%nat).
      { apply eq_vec_true_iff in Ea2. apply (f_equal bv_unsigned) in Ea2.
        change (bv_unsigned (mword_of_int (Z.of_nat n) : mword 64)) with (Z.of_nat n mod 18446744073709551616)%Z in Ea2.
        change (bv_unsigned (zero_reg : mword 64)) with 0%Z in Ea2.
        rewrite Z.mod_small in Ea2; [lia | split; [apply Nat2Z.is_nonneg | lia]]. }
      iPoseProof (snci_24 with "Htext") as "Hi24".
      iPoseProof (snci_26 with "Htext") as "Hi26".
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.strncmp + 0x08))
                (mword_of_int 14 : mword 8) (Cregidx (mword_of_int 4)) Ra2 R2 (K - 2)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite HR2a2'; exact Ea2) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi08").
      iNext. iIntros (CID5 Hs5) "Hcg Hpc".
      assert (Ht24 : add_vec (mword_of_int (KernelSyms.strncmp + 0x08) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 14 : mword 8) ('b"0"))))
              = mword_of_int (KernelSyms.strncmp + 0x24))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ht24) in "Hpc".
      (* +0x24: c.li a0, 0 *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.strncmp + 0x24)) Ra0
                (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                R2 (K - 2)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity)
                with "Hcg Hpc Hi24").
      iIntros (CID6 Hs6) "Hcg Hpc".
      set (Z1 := <[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> R2).
      change (<[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> R2) with Z1.
      assert (Hp26 : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x24) : mword 64) 2
                     = mword_of_int (KernelSyms.strncmp + 0x26))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp26) in "Hpc".
      (* +0x26: c.j +0x0c -> +0x32 *)
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.strncmp + 0x26))
                (sign_extend' 21 (concat_vec (mword_of_int 6 : mword 11) ('b"0")))
                Z1 (K - 2)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi26").
      iIntros (CID7 Hs7). iNext. iIntros "Hcg Hpc".
      assert (Ht32 : add_vec (mword_of_int (KernelSyms.strncmp + 0x26) : mword 64)
                (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 6 : mword 11) ('b"0"))))
              = mword_of_int (KernelSyms.strncmp + 0x32))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ht32) in "Hpc".
      assert (HZ1sp : Z1 !!! Regidx csp_rs1 = pa_stk sp0 2).
      { rewrite /Z1 upd_ne; [exact HR2sp | reg_neq]. }
      assert (HZ1a0 : Z1 !!! Regidx Ra0 = (mword_of_int 0 : mword 64))
        by (rewrite /Z1 upd_eq; reflexivity).
      assert (HZ1thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                         Z1 !!! Regidx r = mm !!! Regidx r).
      { intros r Hr Ncsp Ns0.
        rewrite /Z1 upd_ne; [apply HR2thr; assumption | apply cs_ne; [vm_compute; reflexivity | exact Hr]]. }
      iApply (snc_tail mm Z1 K (mword_of_int 0 : mword 64) sp0
                (mm !!! Regidx Rra) (mm !!! Regidx Rs0) b p
                HK ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                HZ1sp HZ1a0 HZ1thr
                with "Hcg Htext Hpc Hb1 Hb2").
      iIntros (CID8 Hs8 mf) "[%Hcs %Hfa0] Hcg Hpc".
      iSpecialize ("Hcont" $! CID8 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "Hcg Hpc Hbuf1 Hbuf2 [%] [%]").
      + exact Hcs.
      + rewrite Hfa0. left. split; [exact Hn0 | reflexivity].
    - (* n > 0 *)
      assert (Hnpos : (0 < n)%nat).
      { destruct n as [| n']; [| lia].
        exfalso. rewrite bc_zext8_iszero in Ea2. discriminate. }
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.strncmp + 0x08))
                (mword_of_int 14 : mword 8) (Cregidx (mword_of_int 4)) Ra2 R2 (K - 2)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite HR2a2'; exact Ea2)
                with "Hcg Hpc Hi08").
      iIntros (CID5 Hs5) "Hcg Hpc".
      assert (Hp0a : add_vec_int (mword_of_int (KernelSyms.strncmp + 0x08) : mword 64) 2
                     = mword_of_int (KernelSyms.strncmp + 0x0a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp0a) in "Hpc".
      assert (Hrem : (0 + (n - 1) = n - 1)%nat) by lia.
      assert (HR2a0_0 : R2 !!! Regidx Ra0 = pa_add s1 0%nat).
      { rewrite HR2a0. symmetry. apply pa_add_0. }
      assert (HR2a1_0 : R2 !!! Regidx Ra1 = pa_add s2 0%nat).
      { rewrite HR2a1. symmetry. apply pa_add_0. }
      assert (HR2a2_n : R2 !!! Regidx Ra2 = (mword_of_int (Z.of_nat (n - 0)) : mword 64)).
      { replace (n - 0)%nat with n by lia. exact HR2a2. }
      iApply (snc_loop mm n f g K dq1 dq2 s1 s2 sp0 b p CID5 Hnpos Hn31
                (n - 1)%nat 0%nat R2 CID5 ltac:(intros _; reflexivity) Hrem (bb_nonul_0 f)
                ltac:(intros j Hj; exfalso; lia)
                HR2sp HR2a0_0 HR2a1_0 HR2a2_n HR2thr
                with "Hcg Htext Hpc Hbuf1 Hbuf2").
      iIntros (CID6 Hs6 Mt) "%HMtsp %HMta0 %HMtthr Hcg Hpc Hbuf1 Hbuf2".
      iApply (snc_tail mm Mt K (Mt !!! Regidx Ra0) sp0
                (mm !!! Regidx Rra) (mm !!! Regidx Rs0) b p
                HK ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                HMtsp ltac:(reflexivity) HMtthr
                with "Hcg Htext Hpc Hb1 Hb2").
      iIntros (CID7 Hs7 mf) "[%Hcs %Hfa0] Hcg Hpc".
      iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "Hcg Hpc Hbuf1 Hbuf2 [%] [%]").
      + exact Hcs.
      + rewrite Hfa0. exact HMta0.
  Qed.

End ProofStrncmp.

End StrncmpProof.
