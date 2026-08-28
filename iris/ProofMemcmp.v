(* ProofMemcmp.v -- the whole-function WP for xv6's memcmp(), over the
   SIE-agnostic sconf world.

     int memcmp(const void *v1, const void *v2, uint n)

   Contract: SpecMemcmp.v.  22 instructions, a 2-slot ra/s0 frame, no callees.

   Control flow, as the decode in CodeMemcmp.v gives it:

     +0x00..+0x06  prologue: the 2-slot frame push, the ra/s0 spills, addi4spn
     +0x08         c.beqz a2 -- n = 0 jumps to +0x36 (return 0)
     +0x0a..+0x0c  c.slli/c.srli a2,32: the (unsigned int)n truncation
     +0x0e         add a3,a0,a2 -- the END POINTER, v1 + n
     +0x12..+0x22  the compare loop                                 [mc_loop]
       +0x12  lbu a5,0(a0)      +0x16  lbu a4,0(a1)
       +0x1a  bne a5,a4  -> +0x2a  (the bytes differ: stop here)
       +0x1e  c.addi a0,1       +0x20  c.addi a1,1
       +0x22  bne a0,a3  -> +0x12  (cursor has not reached v1 + n: go round)
     +0x26..+0x28  c.li a0,0 ; c.j +0x2e -- ran off the end, equal
     +0x2a         subw a0,a5,a4 -- the unsigned-byte difference
     +0x2e..+0x34  epilogue: reload ra/s0, frame trade back, ret     [mc_tail]
     +0x36..+0x38  c.li a0,0 ; c.j +0x2e -- the n = 0 arm

   Unlike strncmp, the loop does NOT count a2 down: it compares the source
   cursor against the precomputed end pointer, so the induction's index fact
   is [pa_add_cmp_bound] over [a3 = v1 + n] (ByteCursor.v) rather than an
   [addiw]-decrement lemma.  That is also why the count bound here is the
   [< 2^32] of the truncation (as in memmove) and not strncmp's [< 2^31].

   The two buffers are read at INDEPENDENT dfracs, so nothing in this file
   needs -- or gets -- a disjointness fact between them; see SpecMemcmp.v.

   EXPLICIT-CPUID: the whole function threads a generic [b : bool].
   [mc_tail] is a non-recursive fragment, so it takes its own leading
   (shadowing) hart [`{CID0 : CpuId}`].  [mc_loop] recurses via
   [induction rem], so it needs TWO harts kept separate: [CIDh] (its
   [Hcont]'s fixed anchor, forwarded unchanged across every recursive call)
   and [CID0] (this iteration's own entry hart). *)
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
Require Import CodeMemcmp.
Require Import SpecMemcmp.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Local Open Scope Z_scope.

Local Ltac rgne :=
  rewrite rget_ne;
  [ | let H1 := fresh in let H2 := fresh in
      intro H1; injection H1 as H2; vm_compute in H2; congruence ].

Module MemcmpProof : MEMCMP.

Section ProofMemcmp.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.

  Local Lemma cs_ne (k r : mword 5) :
    is_cs_idx k = false -> is_cs_idx r = true -> Regidx r <> Regidx k.
  Proof. intros Hk Hr He. symmetry in He. exact (is_cs_idx_true_neq k r Hk Hr He). Qed.

  Local Lemma mc_push (X : mword 64) :
    add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk X 2.
  Proof. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. Qed.

  Local Lemma mc_step (s : mword 64) (j : nat) :
    add_vec (pa_add s j) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))) = pa_add s (S j).
  Proof. apply pa_add_step. apply bv_eq; vm_compute; reflexivity. Qed.

  (* [subw a0,a5,a4] on two ZERO-EXTENDED bytes: the 32-bit difference,
     sign-extended to 64, is exactly the difference of the two unsigned byte
     values.  (Same fact as ProofStrncmp's [snc_subw_diff]; both are local to
     their file because each is stated against its own operand order.) *)
  Lemma mc_subw_diff (b1 b2 : bv 8) :
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

  (* two zero-extended bytes are equal as 64-bit words only if they are equal *)
  Local Lemma mc_zext8_inj (b1 b2 : bv 8) :
    eq_vec (zero_extend' 64 (b1 : mword 8) : mword 64) (zero_extend' 64 (b2 : mword 8) : mword 64) = true ->
    b1 = b2.
  Proof.
    intro Heq. apply eq_vec_true_iff in Heq. apply (f_equal bv_unsigned) in Heq.
    unfold zero_extend', Operators_mwords.zero_extend, Operators_mwords.extz_vec,
      to_word, get_word, MachineWord.MachineWord.zero_extend in Heq.
    rewrite !bv_zero_extend_unsigned in Heq; try (vm_compute; intro Hc; discriminate Hc).
    apply bv_eq. exact Heq.
  Qed.

  (* =================================================================== *)
  (*  THE EPILOGUE, +0x2e .. +0x34.                                        *)
  (* =================================================================== *)
  Local Lemma mc_tail `{CID0 : CpuId}
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
    pc_is (CID := CID0) (mword_of_int (KernelSyms.memcmp + 0x2e) : mword 64) -∗
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
    (* ---- +0x2e: c.ldsp ra,8(sp) ---- *)
    assert (Hpa1 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                   = pa_stk sp0 1).
    { rewrite Hmtsp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.memcmp + 0x2e))
              (mword_of_int 1 : mword 6) Rra Mt (K - 2)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hb1").
    { iApply (mci_2e with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hpc Hb1".
    iEval (rewrite Hpa1) in "Hb1".
    set (T1 := <[Regidx Rra := regval_into_reg ra0]> Mt).
    change (<[Regidx Rra := regval_into_reg ra0]> Mt) with T1.
    assert (Hp30 : add_vec_int (mword_of_int (KernelSyms.memcmp + 0x2e) : mword 64) 2
                   = mword_of_int (KernelSyms.memcmp + 0x30))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp30) in "Hpc".
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /T1 upd_ne; [exact Hmtsp | reg_neq]).
    (* ---- +0x30: c.ldsp s0,0(sp) ---- *)
    assert (Hpa2 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                   = pa_stk sp0 2).
    { rewrite HT1sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.memcmp + 0x30))
              (mword_of_int 0 : mword 6) Rs0 T1 (K - 2)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hb2").
    { iApply (mci_30 with "Htext"). }
    iIntros (CID2 Hs2) "Hcg Hpc Hb2".
    iEval (rewrite Hpa2) in "Hb2".
    set (T2 := <[Regidx Rs0 := regval_into_reg s00]> T1).
    change (<[Regidx Rs0 := regval_into_reg s00]> T1) with T2.
    assert (Hp32 : add_vec_int (mword_of_int (KernelSyms.memcmp + 0x30) : mword 64) 2
                   = mword_of_int (KernelSyms.memcmp + 0x32))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp32) in "Hpc".
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /T2 upd_ne; [exact HT1sp | reg_neq]).
    (* ---- +0x32: c.addi sp,16 ---- *)
    assert (Hwv : add_vec (T2 !!! Regidx csp_rs1)
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0)
      by (rewrite HT2sp; apply stk_pop_16).
    assert (Hpop : T2 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T2 !!! Regidx csp_rs1)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2)
      by (rewrite Hwv; exact HT2sp).
    iDestruct (stack_own_2_intro sp0 ra0 s00 with "Hb1 Hb2") as "Hframe".
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.memcmp + 0x32))
              (mword_of_int 16 : mword 6) T2 (K - 2)%nat 2 b Hpop
              with "Hcg Hpc [] Hframe").
    { iApply (mci_32 with "Htext"). }
    iIntros (CID3 Hs3) "Hcg Hpc".
    assert (Hnk : ((K - 2) + 2)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    set (T3 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (T2 !!! Regidx csp_rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> T2).
    change (<[Regidx csp_rs1 := regval_into_reg
               (add_vec (T2 !!! Regidx csp_rs1)
                  (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> T2) with T3.
    assert (Hp34 : add_vec_int (mword_of_int (KernelSyms.memcmp + 0x32) : mword 64) 2
                   = mword_of_int (KernelSyms.memcmp + 0x34))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp34) in "Hpc".
    (* ---- +0x34: c.ret ---- *)
    assert (HT3ra : T3 !!! Regidx Rra = ra0).
    { rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_eq. reflexivity. }
    assert (HT3ra' : forall CID' : CpuId, rget (CID := CID') T3 Rra = ra0)
      by (intros CID'; rgne; exact HT3ra).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.memcmp + 0x34)) Rra T3 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc []").
    { iApply (mci_34 with "Htext"). }
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

  (* =================================================================== *)
  (*  THE COMPARE LOOP, +0x12 .. +0x22.                                    *)
  (*                                                                       *)
  (*  Fuel induction on [rem], the number of index positions still to be    *)
  (*  visited: entering at index [t] with [t + rem = n] and [1 <= rem].     *)
  (*  The [rem = 0] case is vacuous, so the loop body is written ONCE and   *)
  (*  the two outcomes of the +0x22 back-branch are a [destruct rem'] at    *)
  (*  the branch itself (as in ProofMemmove's [mm_loop]).                   *)
  (* =================================================================== *)
  Local Lemma mc_loop
      (mm : regfile) (n : nat) (f g : nat -> bv 8) (K : nat) (dq1 dq2 : dfrac)
      (s1 s2 sp0 : mword 64) (b : bool) (p : mword 64) (CIDh : CpuId) :
    (Z.of_nat n < 2 ^ 64)%Z ->
    forall (rem t : nat) (M : regfile) (CID0 : CpuId),
    (b = false \/ p = zero_reg -> (CID0 : CPU) = (CIDh : CPU)) ->
    (t + rem = n)%nat -> (1 <= rem)%nat ->
    (forall j, (j < t)%nat -> f j = g j) ->
    M !!! Regidx csp_rs1 = pa_stk sp0 2 ->
    M !!! Regidx Ra0 = pa_add s1 t ->
    M !!! Regidx Ra1 = pa_add s2 t ->
    M !!! Regidx Ra3 = add_vec (mword_of_int (Z.of_nat n) : mword 64) s1 ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
        M !!! Regidx r = mm !!! Regidx r) ->
    sie_cap_gpr KT1 (CID := CID0) M (K - 2)%nat b p -∗
    kernel_text -∗
    pc_is (CID := CID0) (mword_of_int (KernelSyms.memcmp + 0x12) : mword 64) -∗
    ([∗ list] j ∈ seq 0 n, (pa_add s1 j) ↦ₘ{dq1} f j) -∗
    ([∗ list] j ∈ seq 0 n, (pa_add s2 j) ↦ₘ{dq2} g j) -∗
    wp_next (CID0 := CIDh) b p (fun (CID : CpuId) =>
      ∀ Mt : regfile,
        ⌜Mt !!! Regidx csp_rs1 = pa_stk sp0 2⌝ -∗
        ⌜memcmp_res f g n (Mt !!! Regidx Ra0)⌝ -∗
        ⌜forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
            Mt !!! Regidx r = mm !!! Regidx r⌝ -∗
        sie_cap_gpr KT1 Mt (K - 2)%nat b p -∗
        pc_is (mword_of_int (KernelSyms.memcmp + 0x2e) : mword 64) -∗
        ([∗ list] j ∈ seq 0 n, (pa_add s1 j) ↦ₘ{dq1} f j) -∗
        ([∗ list] j ∈ seq 0 n, (pa_add s2 j) ↦ₘ{dq2} g j) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn64 rem.
    induction rem as [| rem' IH]; intros t M CID0 Hchain Hsum Hrem Heq Hsp Ha0 Ha1 Ha3 Hthr;
      [ exfalso; lia |].
    iIntros "Hcg #Htext Hpc Hbuf1 Hbuf2 Hcont".
    assert (Htn : (t < n)%nat) by lia.
    (* ---- +0x12: lbu a5,0(a0) ---- *)
    iDestruct (bb_byte_acc s1 n t f dq1 Htn with "Hbuf1") as "[Hb1 Hback1]".
    assert (HMa0 : rget M Ra0 = pa_add s1 t) by (rgne; exact Ha0).
    iApply (wp_lbu_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.memcmp + 0x12)) Ra5 Ra0
              (mword_of_int 0 : mword 12) M (K - 2)%nat (f t : mword 8) b (dqm:=dq1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hb1]").
    { iApply (mci_12 with "Htext"). }
    { iEval (rewrite HMa0 addv_sext0). iExact "Hb1". }
    iIntros (CID1 Hs1) "Hcg Hpc Hb1".
    iEval (rewrite HMa0 addv_sext0) in "Hb1".
    iDestruct ("Hback1" $! f with "[%] Hb1") as "Hbuf1"; [done |].
    set (M1 := <[Regidx Ra5 := regval_into_reg (zero_extend' 64 (f t : mword 8))]> M).
    change (<[Regidx Ra5 := regval_into_reg (zero_extend' 64 (f t : mword 8))]> M) with M1.
    assert (Hp16 : add_vec_int (mword_of_int (KernelSyms.memcmp + 0x12) : mword 64) 4
                   = mword_of_int (KernelSyms.memcmp + 0x16))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp16) in "Hpc".
    (* ---- +0x16: lbu a4,0(a1) ---- *)
    iDestruct (bb_byte_acc s2 n t g dq2 Htn with "Hbuf2") as "[Hb2 Hback2]".
    assert (HM1a1 : M1 !!! Regidx Ra1 = pa_add s2 t)
      by (rewrite /M1 upd_ne; [exact Ha1 | reg_neq]).
    assert (HM1a1' : rget M1 Ra1 = pa_add s2 t) by (rgne; exact HM1a1).
    iApply (wp_lbu_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.memcmp + 0x16)) Ra4 Ra1
              (mword_of_int 0 : mword 12) M1 (K - 2)%nat (g t : mword 8) b (dqm:=dq2)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hb2]").
    { iApply (mci_16 with "Htext"). }
    { iEval (rewrite HM1a1' addv_sext0). iExact "Hb2". }
    iIntros (CID2 Hs2) "Hcg Hpc Hb2".
    iEval (rewrite HM1a1' addv_sext0) in "Hb2".
    iDestruct ("Hback2" $! g with "[%] Hb2") as "Hbuf2"; [done |].
    set (M2 := <[Regidx Ra4 := regval_into_reg (zero_extend' 64 (g t : mword 8))]> M1).
    change (<[Regidx Ra4 := regval_into_reg (zero_extend' 64 (g t : mword 8))]> M1) with M2.
    assert (Hp1a : add_vec_int (mword_of_int (KernelSyms.memcmp + 0x16) : mword 64) 4
                   = mword_of_int (KernelSyms.memcmp + 0x1a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1a) in "Hpc".
    assert (HM2a5 : M2 !!! Regidx Ra5 = zero_extend' 64 (f t : mword 8)).
    { rewrite /M2 upd_ne; [| reg_neq]. rewrite /M1 upd_eq. reflexivity. }
    assert (HM2a5' : rget M2 Ra5 = zero_extend' 64 (f t : mword 8)) by (rgne; exact HM2a5).
    assert (HM2a4 : M2 !!! Regidx Ra4 = zero_extend' 64 (g t : mword 8))
      by (rewrite /M2 upd_eq; reflexivity).
    assert (HM2a4' : rget M2 Ra4 = zero_extend' 64 (g t : mword 8)) by (rgne; exact HM2a4).
    (* the CID-generic twins: [set] binds the register-map update to the goal's
       OWN [rget] instance, whose hart is the one the branch peeled off, so a
       rewrite into that update needs the fact at an arbitrary hart *)
    assert (HM2a5g : forall CID' : CpuId, rget (CID := CID') M2 Ra5 = zero_extend' 64 (f t : mword 8))
      by (intros CID'; rgne; exact HM2a5).
    assert (HM2a4g : forall CID' : CpuId, rget (CID := CID') M2 Ra4 = zero_extend' 64 (g t : mword 8))
      by (intros CID'; rgne; exact HM2a4).
    assert (HM2sp : M2 !!! Regidx csp_rs1 = pa_stk sp0 2).
    { rewrite /M2 upd_ne; [| reg_neq]. rewrite /M1 upd_ne; [exact Hsp | reg_neq]. }
    assert (HM2thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                       M2 !!! Regidx r = mm !!! Regidx r).
    { intros r Hr Ncsp Ns0.
      rewrite /M2 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
      rewrite /M1 upd_ne; [apply Hthr; assumption | apply cs_ne; [vm_compute; reflexivity | exact Hr]]. }
    (* ---- +0x1a: bne a5,a4 -> +0x2a ---- *)
    destruct (eq_vec (zero_extend' 64 (f t : mword 8) : mword 64)
                     (zero_extend' 64 (g t : mword 8) : mword 64)) eqn:Eeq.
    - (* the bytes agree: fall through to +0x1e *)
      assert (Hfg : f t = g t) by (apply mc_zext8_inj; exact Eeq).
      assert (Hfall : neq_vec (rget M2 Ra5) (rget M2 Ra4) = false).
      { unfold neq_vec. rewrite HM2a5' HM2a4' Eeq. reflexivity. }
      iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.memcmp + 0x1a))
                (mword_of_int 16 : mword 13) Ra4 Ra5 M2 (K - 2)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hfall
                with "Hcg Hpc []").
      { iApply (mci_1a with "Htext"). }
      iIntros (CID3 Hs3) "Hcg Hpc".
      assert (Hp1e : add_vec_int (mword_of_int (KernelSyms.memcmp + 0x1a) : mword 64) 4
                     = mword_of_int (KernelSyms.memcmp + 0x1e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp1e) in "Hpc".
      (* ---- +0x1e: c.addi a0,1 ---- *)
      assert (HM2a0 : M2 !!! Regidx Ra0 = pa_add s1 t).
      { rewrite /M2 upd_ne; [| reg_neq]. rewrite /M1 upd_ne; [exact Ha0 | reg_neq]. }
      assert (HM2a0' : rget M2 Ra0 = pa_add s1 t) by (rgne; exact HM2a0).
      iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.memcmp + 0x1e)) Ra0
                (mword_of_int 1 : mword 6) M2 (K - 2)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (mci_1e with "Htext"). }
      iIntros (CID4 Hs4) "Hcg Hpc".
      set (M3 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (rget M2 Ra0)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> M2).
      change (<[Regidx Ra0 := regval_into_reg
                 (add_vec (rget M2 Ra0)
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> M2) with M3.
      assert (HM3a0 : M3 !!! Regidx Ra0 = pa_add s1 (S t)).
      { rewrite /M3 upd_eq HM2a0'. apply mc_step. }
      assert (Hp20 : add_vec_int (mword_of_int (KernelSyms.memcmp + 0x1e) : mword 64) 2
                     = mword_of_int (KernelSyms.memcmp + 0x20))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp20) in "Hpc".
      (* ---- +0x20: c.addi a1,1 ---- *)
      assert (HM3a1 : M3 !!! Regidx Ra1 = pa_add s2 t)
        by (rewrite /M3 upd_ne; [exact HM1a1 | reg_neq]).
      assert (HM3a1' : rget M3 Ra1 = pa_add s2 t) by (rgne; exact HM3a1).
      iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.memcmp + 0x20)) Ra1
                (mword_of_int 1 : mword 6) M3 (K - 2)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (mci_20 with "Htext"). }
      iIntros (CID5 Hs5) "Hcg Hpc".
      set (M4 := <[Regidx Ra1 := regval_into_reg
                    (add_vec (rget M3 Ra1)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> M3).
      change (<[Regidx Ra1 := regval_into_reg
                 (add_vec (rget M3 Ra1)
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> M3) with M4.
      assert (HM4a1 : M4 !!! Regidx Ra1 = pa_add s2 (S t)).
      { rewrite /M4 upd_eq HM3a1'. apply mc_step. }
      assert (Hp22 : add_vec_int (mword_of_int (KernelSyms.memcmp + 0x20) : mword 64) 2
                     = mword_of_int (KernelSyms.memcmp + 0x22))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp22) in "Hpc".
      (* ---- +0x22: bne a0,a3 -- back to +0x12 unless the cursor is done ---- *)
      assert (HM4a0 : M4 !!! Regidx Ra0 = pa_add s1 (S t))
        by (rewrite /M4 upd_ne; [exact HM3a0 | reg_neq]).
      assert (HM4a0' : rget M4 Ra0 = pa_add s1 (S t)) by (rgne; exact HM4a0).
      assert (HM4a3 : M4 !!! Regidx Ra3 = add_vec (mword_of_int (Z.of_nat n) : mword 64) s1).
      { rewrite /M4 upd_ne; [| reg_neq]. rewrite /M3 upd_ne; [| reg_neq].
        rewrite /M2 upd_ne; [| reg_neq]. rewrite /M1 upd_ne; [exact Ha3 | reg_neq]. }
      assert (HM4a3' : rget M4 Ra3 = add_vec (mword_of_int (Z.of_nat n) : mword 64) s1)
        by (rgne; exact HM4a3).
      assert (Hcmp : neq_vec (rget M4 Ra0) (rget M4 Ra3) = negb (Nat.eqb (S t) n)).
      { rewrite HM4a0' HM4a3'. apply pa_add_cmp_bound; [exact Hn64 | exact Htn]. }
      assert (HM4sp : M4 !!! Regidx csp_rs1 = pa_stk sp0 2).
      { rewrite /M4 upd_ne; [| reg_neq]. rewrite /M3 upd_ne; [exact HM2sp | reg_neq]. }
      assert (HM4thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                         M4 !!! Regidx r = mm !!! Regidx r).
      { intros r Hr Ncsp Ns0.
        rewrite /M4 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
        rewrite /M3 upd_ne; [apply HM2thr; assumption
                            | apply cs_ne; [vm_compute; reflexivity | exact Hr]]. }
      assert (Heq' : forall j, (j < S t)%nat -> f j = g j).
      { intros j Hj. assert (Hjt : j = t \/ (j < t)%nat) by lia.
        destruct Hjt as [-> | Hjt]; [exact Hfg | apply Heq; exact Hjt]. }
      destruct rem' as [| rem''].
      + (* the cursor reached v1 + n: fall through to +0x26 *)
        assert (Hlast : (S t = n)%nat) by lia.
        assert (Hfall2 : neq_vec (rget M4 Ra0) (rget M4 Ra3) = false).
        { rewrite Hcmp Hlast Nat.eqb_refl. reflexivity. }
        iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.memcmp + 0x22))
                  (mword_of_int 8176 : mword 13) Ra3 Ra0 M4 (K - 2)%nat b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hfall2
                  with "Hcg Hpc []").
        { iApply (mci_22 with "Htext"). }
        iIntros (CID6 Hs6) "Hcg Hpc".
        assert (Hp26 : add_vec_int (mword_of_int (KernelSyms.memcmp + 0x22) : mword 64) 4
                       = mword_of_int (KernelSyms.memcmp + 0x26))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp26) in "Hpc".
        (* ---- +0x26: c.li a0,0 ---- *)
        iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.memcmp + 0x26)) Ra0
                  (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                  M4 (K - 2)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity)
                  with "Hcg Hpc []").
        { iApply (mci_26 with "Htext"). }
        iIntros (CID7 Hs7) "Hcg Hpc".
        set (M5 := <[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> M4).
        change (<[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> M4) with M5.
        assert (Hp28 : add_vec_int (mword_of_int (KernelSyms.memcmp + 0x26) : mword 64) 2
                       = mword_of_int (KernelSyms.memcmp + 0x28))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp28) in "Hpc".
        (* ---- +0x28: c.j -> +0x2e ---- *)
        iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.memcmp + 0x28))
                  (sign_extend' 21 (concat_vec (mword_of_int 3 : mword 11) ('b"0")))
                  M5 (K - 2)%nat b ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (mci_28 with "Htext"). }
        iIntros (CID8 Hs8). iApply bi.later_intro. iIntros "Hcg Hpc".
        assert (Ht2e : add_vec (mword_of_int (KernelSyms.memcmp + 0x28) : mword 64)
                  (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 3 : mword 11) ('b"0"))))
                = mword_of_int (KernelSyms.memcmp + 0x2e))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Ht2e) in "Hpc".
        assert (HM5sp : M5 !!! Regidx csp_rs1 = pa_stk sp0 2)
          by (rewrite /M5 upd_ne; [exact HM4sp | reg_neq]).
        assert (HM5a0 : M5 !!! Regidx Ra0 = (mword_of_int 0 : mword 64))
          by (rewrite /M5 upd_eq; reflexivity).
        assert (HM5thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                           M5 !!! Regidx r = mm !!! Regidx r).
        { intros r Hr Ncsp Ns0.
          rewrite /M5 upd_ne; [apply HM4thr; assumption
                              | apply cs_ne; [vm_compute; reflexivity | exact Hr]]. }
        iSpecialize ("Hcont" $! CID8 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! M5 with "[%] [%] [%] Hcg Hpc Hbuf1 Hbuf2").
        * exact HM5sp.
        * rewrite HM5a0. right. split; [| reflexivity].
          intros j Hj. apply Heq'. lia.
        * exact HM5thr.
      + (* more bytes: the bne is taken back to +0x12 *)
        assert (Htaken : neq_vec (rget M4 Ra0) (rget M4 Ra3) = true).
        { rewrite Hcmp. destruct (Nat.eqb_spec (S t) n) as [He | Hne];
            [exfalso; lia | reflexivity]. }
        iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.memcmp + 0x22))
                  (mword_of_int 8176 : mword 13) Ra3 Ra0 M4 (K - 2)%nat b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Htaken
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (mci_22 with "Htext"). }
        iApply bi.later_intro. iIntros (CID6 Hs6) "Hcg Hpc".
        assert (Hback12 : add_vec (mword_of_int (KernelSyms.memcmp + 0x22) : mword 64)
                            (sign_extend' 64 (mword_of_int 8176 : mword 13))
                          = mword_of_int (KernelSyms.memcmp + 0x12))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hback12) in "Hpc".
        assert (Hchain' : b = false \/ p = zero_reg -> (CID6 : CPU) = (CIDh : CPU))
          by wp_next_chain.
        iApply (IH (S t) M4 CID6 Hchain' ltac:(lia) ltac:(lia) Heq'
                  HM4sp HM4a0 HM4a1 HM4a3 HM4thr
                  with "Hcg Htext Hpc Hbuf1 Hbuf2 Hcont").
    - (* the bytes differ: the bne is taken to +0x2a *)
      assert (Hne : f t <> g t).
      { intro He. rewrite He eq_vec_refl in Eeq. discriminate. }
      assert (Htaken : neq_vec (rget M2 Ra5) (rget M2 Ra4) = true).
      { unfold neq_vec. rewrite HM2a5' HM2a4' Eeq. reflexivity. }
      iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.memcmp + 0x1a))
                (mword_of_int 16 : mword 13) Ra4 Ra5 M2 (K - 2)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Htaken
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (mci_1a with "Htext"). }
      iApply bi.later_intro. iIntros (CID3 Hs3) "Hcg Hpc".
      assert (Ht2a : add_vec (mword_of_int (KernelSyms.memcmp + 0x1a) : mword 64)
                       (sign_extend' 64 (mword_of_int 16 : mword 13))
                     = mword_of_int (KernelSyms.memcmp + 0x2a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ht2a) in "Hpc".
      (* ---- +0x2a: subw a0,a5,a4 ---- *)
      iApply (wp_subw_s_sconf (mword_of_int (KernelSyms.memcmp + 0x2a)) Ra0 Ra5 Ra4
                M2 (K - 2)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (mci_2a with "Htext"). }
      iIntros (CID4 Hs4) "Hcg Hpc".
      set (M3 := <[Regidx Ra0 := regval_into_reg
                    (sign_extend' 64
                       (sub_vec (subrange_vec_dec (rget M2 Ra5) 31 0 : mword 32)
                                (subrange_vec_dec (rget M2 Ra4) 31 0 : mword 32)))]> M2).
      change (<[Regidx Ra0 := regval_into_reg
                 (sign_extend' 64
                    (sub_vec (subrange_vec_dec (rget M2 Ra5) 31 0 : mword 32)
                             (subrange_vec_dec (rget M2 Ra4) 31 0 : mword 32)))]> M2) with M3.
      assert (HM3a0 : M3 !!! Regidx Ra0
                      = (mword_of_int (bv_unsigned (f t) - bv_unsigned (g t)) : mword 64)).
      { rewrite /M3 upd_eq /regval_into_reg HM2a5g HM2a4g. apply mc_subw_diff. }
      assert (Hp2e : add_vec_int (mword_of_int (KernelSyms.memcmp + 0x2a) : mword 64) 4
                     = mword_of_int (KernelSyms.memcmp + 0x2e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp2e) in "Hpc".
      assert (HM3sp : M3 !!! Regidx csp_rs1 = pa_stk sp0 2)
        by (rewrite /M3 upd_ne; [exact HM2sp | reg_neq]).
      assert (HM3thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                         M3 !!! Regidx r = mm !!! Regidx r).
      { intros r Hr Ncsp Ns0.
        rewrite /M3 upd_ne; [apply HM2thr; assumption
                            | apply cs_ne; [vm_compute; reflexivity | exact Hr]]. }
      iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! M3 with "[%] [%] [%] Hcg Hpc Hbuf1 Hbuf2").
      + exact HM3sp.
      + rewrite HM3a0. left. exists t.
        split_and!; [exact Htn | exact Heq | exact Hne | reflexivity].
      + exact HM3thr.
  Qed.

  (* =================================================================== *)
  (*  THE WHOLE FUNCTION.                                                  *)
  (* =================================================================== *)
  Lemma wp_memcmp_sconf (mm : regfile)
      (n : nat) (f g : nat -> bv 8) (K : nat) (dq1 dq2 : dfrac) (b : bool) (p : mword 64)
    : wp_memcmp_sconf_body mm n f g K dq1 dq2 b p.
  Proof.
    cbv beta delta [wp_memcmp_sconf_body].
    intros pcE s1 s2 ret_tgt HK Ha2 Hn32.
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    assert (Hn64 : (Z.of_nat n < 2 ^ 64)%Z)
      by (apply (Z.lt_trans _ (2 ^ 32)); [exact Hn32 | vm_compute; reflexivity]).
    assert (Hnu : bv_unsigned (mword_of_int (Z.of_nat n) : mword 64) = Z.of_nat n).
    { rewrite moi64_unsigned. apply bv_wrap_small.
      split; [apply Nat2Z.is_nonneg |].
      apply (Z.lt_trans _ (2 ^ 32)); [exact Hn32 |].
      unfold bv_modulus. vm_compute. reflexivity. }
    iIntros "Hcg #Htext Hpc Hbuf1 Hbuf2 Hcont".
    (* ---- +0x00: c.addi sp,-16 ---- *)
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 48 : mword 6) mm K 2 b
              ltac:(lia) (mc_push (mm !!! Regidx csp_rs1))
              with "Hcg Hpc []").
    { iApply (mci_00 with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (mm !!! Regidx csp_rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> mm).
    change (<[Regidx csp_rs1 := regval_into_reg
               (add_vec (mm !!! Regidx csp_rs1)
                  (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> mm) with R1.
    assert (HR1sp : R1 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /R1 upd_eq; apply mc_push).
    assert (Hp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.memcmp + 0x02))
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
    (* ---- +0x02: c.sdsp ra,8(sp) ---- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.memcmp + 0x02))
              (mword_of_int 1 : mword 6) Rra R1 (K - 2)%nat u1 b
              with "Hcg Hpc [] [Hb1]").
    { iApply (mci_02 with "Htext"). }
    { iEval (rewrite Hpa1). iExact "Hb1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hb1". iEval (rewrite Hpa1) in "Hb1".
    assert (HR1ra : R1 !!! Regidx Rra = mm !!! Regidx Rra)
      by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (HR1ra' : forall CID' : CpuId, rget (CID := CID') R1 Rra = mm !!! Regidx Rra)
      by (intros CID'; rgne; exact HR1ra).
    iEval (rewrite HR1ra') in "Hb1".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.memcmp + 0x02) : mword 64) 2
                   = mword_of_int (KernelSyms.memcmp + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    (* ---- +0x04: c.sdsp s0,0(sp) ---- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.memcmp + 0x04))
              (mword_of_int 0 : mword 6) Rs0 R1 (K - 2)%nat u2 b
              with "Hcg Hpc [] [Hb2]").
    { iApply (mci_04 with "Htext"). }
    { iEval (rewrite Hpa2). iExact "Hb2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hb2". iEval (rewrite Hpa2) in "Hb2".
    assert (HR1s0 : R1 !!! Regidx Rs0 = mm !!! Regidx Rs0)
      by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (HR1s0' : forall CID' : CpuId, rget (CID := CID') R1 Rs0 = mm !!! Regidx Rs0)
      by (intros CID'; rgne; exact HR1s0).
    iEval (rewrite HR1s0') in "Hb2".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.memcmp + 0x04) : mword 64) 2
                   = mword_of_int (KernelSyms.memcmp + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    (* ---- +0x06: c.addi4spn s0,sp,16 ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.memcmp + 0x06))
              (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) Rs0 R1 (K - 2)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (mci_06 with "Htext"). }
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1).
    change (<[Regidx Rs0 := regval_into_reg
               (add_vec (R1 !!! Regidx csp_rs1)
                  (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1) with R2.
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.memcmp + 0x06) : mword 64) 2
                   = mword_of_int (KernelSyms.memcmp + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    assert (HR2a2 : R2 !!! Regidx Ra2 = (mword_of_int (Z.of_nat n) : mword 64)).
    { rewrite /R2 upd_ne; [| reg_neq]. rewrite /R1 upd_ne; [exact Ha2 | reg_neq]. }
    assert (HR2a2' : forall CID' : CpuId, rget (CID := CID') R2 Ra2 = (mword_of_int (Z.of_nat n) : mword 64))
      by (intros CID'; rgne; exact HR2a2).
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
    (* ---- +0x08: c.beqz a2, +0x2e -> +0x36 ---- *)
    destruct (eq_vec (mword_of_int (Z.of_nat n) : mword 64) (zero_reg : mword 64)) eqn:Ea2.
    - (* n = 0: the compare loop never runs *)
      assert (Hn0 : n = 0%nat).
      { apply eq_vec_true_iff in Ea2. apply (f_equal bv_unsigned) in Ea2.
        rewrite Hnu in Ea2.
        change (bv_unsigned (zero_reg : mword 64)) with 0%Z in Ea2. lia. }
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.memcmp + 0x08))
                (mword_of_int 23 : mword 8) (Cregidx (mword_of_int 4)) Ra2 R2 (K - 2)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite HR2a2'; exact Ea2) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (mci_08 with "Htext"). }
      iApply bi.later_intro. iIntros (CID5 Hs5) "Hcg Hpc".
      assert (Ht36 : add_vec (mword_of_int (KernelSyms.memcmp + 0x08) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 23 : mword 8) ('b"0"))))
              = mword_of_int (KernelSyms.memcmp + 0x36))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ht36) in "Hpc".
      (* ---- +0x36: c.li a0,0 ---- *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.memcmp + 0x36)) Ra0
                (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                R2 (K - 2)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity)
                with "Hcg Hpc []").
      { iApply (mci_36 with "Htext"). }
      iIntros (CID6 Hs6) "Hcg Hpc".
      set (Z1 := <[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> R2).
      change (<[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> R2) with Z1.
      assert (Hp38 : add_vec_int (mword_of_int (KernelSyms.memcmp + 0x36) : mword 64) 2
                     = mword_of_int (KernelSyms.memcmp + 0x38))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp38) in "Hpc".
      (* ---- +0x38: c.j -> +0x2e ---- *)
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.memcmp + 0x38))
                (sign_extend' 21 (concat_vec (mword_of_int 2043 : mword 11) ('b"0")))
                Z1 (K - 2)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (mci_38 with "Htext"). }
      iIntros (CID7 Hs7). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Ht2e : add_vec (mword_of_int (KernelSyms.memcmp + 0x38) : mword 64)
                (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2043 : mword 11) ('b"0"))))
              = mword_of_int (KernelSyms.memcmp + 0x2e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ht2e) in "Hpc".
      assert (HZ1sp : Z1 !!! Regidx csp_rs1 = pa_stk sp0 2)
        by (rewrite /Z1 upd_ne; [exact HR2sp | reg_neq]).
      assert (HZ1a0 : Z1 !!! Regidx Ra0 = (mword_of_int 0 : mword 64))
        by (rewrite /Z1 upd_eq; reflexivity).
      assert (HZ1thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                         Z1 !!! Regidx r = mm !!! Regidx r).
      { intros r Hr Ncsp Ns0.
        rewrite /Z1 upd_ne; [apply HR2thr; assumption
                            | apply cs_ne; [vm_compute; reflexivity | exact Hr]]. }
      iApply (mc_tail mm Z1 K (mword_of_int 0 : mword 64) sp0
                (mm !!! Regidx Rra) (mm !!! Regidx Rs0) b p
                HK ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                HZ1sp HZ1a0 HZ1thr
                with "Hcg Htext Hpc Hb1 Hb2").
      iIntros (CID8 Hs8 mf) "[%Hcs %Hfa0] Hcg Hpc".
      iSpecialize ("Hcont" $! CID8 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "Hcg Hpc Hbuf1 Hbuf2 [%] [%]").
      + exact Hcs.
      + rewrite Hfa0. right. split; [| reflexivity].
        intros j Hj. exfalso. rewrite Hn0 in Hj. lia.
    - (* n > 0: the truncation, the end pointer, and the loop *)
      assert (Hnpos : (0 < n)%nat).
      { destruct n as [| n']; [| lia].
        exfalso. rewrite bc_zext8_iszero in Ea2. discriminate. }
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.memcmp + 0x08))
                (mword_of_int 23 : mword 8) (Cregidx (mword_of_int 4)) Ra2 R2 (K - 2)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite HR2a2'; exact Ea2)
                with "Hcg Hpc []").
      { iApply (mci_08 with "Htext"). }
      iIntros (CID5 Hs5) "Hcg Hpc".
      assert (Hp0a : add_vec_int (mword_of_int (KernelSyms.memcmp + 0x08) : mword 64) 2
                     = mword_of_int (KernelSyms.memcmp + 0x0a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp0a) in "Hpc".
      (* ---- +0x0a: c.slli a2,32 ---- *)
      iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.memcmp + 0x0a)) (Regidx Ra2) Ra2
                (mword_of_int 32 : mword 6) R2 (K - 2)%nat b
                eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (mci_0a with "Htext"). }
      iIntros (CID6 Hs6) "Hcg Hpc".
      set (R3 := <[Regidx Ra2 := regval_into_reg
                    (shift_bits_left (rget R2 Ra2)
                       (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))]> R2).
      change (<[Regidx Ra2 := regval_into_reg
                 (shift_bits_left (rget R2 Ra2)
                    (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))]> R2) with R3.
      assert (Hp0c : add_vec_int (mword_of_int (KernelSyms.memcmp + 0x0a) : mword 64) 2
                     = mword_of_int (KernelSyms.memcmp + 0x0c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp0c) in "Hpc".
      assert (HR3a2 : R3 !!! Regidx Ra2
                      = shift_bits_left (rget R2 Ra2)
                          (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))
        by (rewrite /R3 upd_eq; reflexivity).
      assert (HR3a2' : forall CID' : CpuId, rget (CID := CID') R3 Ra2
                       = shift_bits_left (rget R2 Ra2)
                           (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))
        by (intros CID'; rgne; exact HR3a2).
      (* ---- +0x0c: c.srli a2,32 ---- *)
      iApply (wp_csrli_s_sconf (mword_of_int (KernelSyms.memcmp + 0x0c)) (Cregidx (mword_of_int 4)) Ra2
                (mword_of_int 32 : mword 6) R3 (K - 2)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (mci_0c with "Htext"). }
      iIntros (CID7 Hs7) "Hcg Hpc".
      set (R4 := <[Regidx Ra2 := regval_into_reg
                    (shift_bits_right (rget R3 Ra2)
                       (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))]> R3).
      change (<[Regidx Ra2 := regval_into_reg
                 (shift_bits_right (rget R3 Ra2)
                    (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))]> R3) with R4.
      assert (Hp0e : add_vec_int (mword_of_int (KernelSyms.memcmp + 0x0c) : mword 64) 2
                     = mword_of_int (KernelSyms.memcmp + 0x0e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp0e) in "Hpc".
      (* the round trip through 32 bits is the identity on the count *)
      assert (HR4a2 : R4 !!! Regidx Ra2 = (mword_of_int (Z.of_nat n) : mword 64)).
      { rewrite /R4 upd_eq /regval_into_reg HR3a2' HR2a2'.
        apply slli32_srli32. rewrite Hnu. exact Hn32. }
      assert (HR4a2' : forall CID' : CpuId, rget (CID := CID') R4 Ra2 = (mword_of_int (Z.of_nat n) : mword 64))
        by (intros CID'; rgne; exact HR4a2).
      assert (HR4a0 : R4 !!! Regidx Ra0 = s1).
      { rewrite /R4 upd_ne; [| reg_neq]. rewrite /R3 upd_ne; [exact HR2a0 | reg_neq]. }
      assert (HR4a0' : forall CID' : CpuId, rget (CID := CID') R4 Ra0 = s1)
        by (intros CID'; rgne; exact HR4a0).
      assert (HR4a1 : R4 !!! Regidx Ra1 = s2).
      { rewrite /R4 upd_ne; [| reg_neq]. rewrite /R3 upd_ne; [exact HR2a1 | reg_neq]. }
      assert (HR4sp : R4 !!! Regidx csp_rs1 = pa_stk sp0 2).
      { rewrite /R4 upd_ne; [| reg_neq]. rewrite /R3 upd_ne; [exact HR2sp | reg_neq]. }
      assert (HR4thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                         R4 !!! Regidx r = mm !!! Regidx r).
      { intros r Hr Ncsp Ns0.
        rewrite /R4 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
        rewrite /R3 upd_ne; [apply HR2thr; assumption
                            | apply cs_ne; [vm_compute; reflexivity | exact Hr]]. }
      (* ---- +0x0e: add a3,a0,a2 -- the end pointer ---- *)
      iApply (wp_add_s_sconf (mword_of_int (KernelSyms.memcmp + 0x0e)) Ra3 Ra0 Ra2
                (add_vec (mword_of_int (Z.of_nat n) : mword 64) s1) R4 (K - 2)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(rewrite HR4a0' HR4a2'; apply add_vec64_comm)
                with "Hcg Hpc []").
      { iApply (mci_0e with "Htext"). }
      iIntros (CID8 Hs8) "Hcg Hpc".
      set (R5 := <[Regidx Ra3 := regval_into_reg
                    (add_vec (mword_of_int (Z.of_nat n) : mword 64) s1)]> R4).
      change (<[Regidx Ra3 := regval_into_reg
                 (add_vec (mword_of_int (Z.of_nat n) : mword 64) s1)]> R4) with R5.
      assert (Hp12 : add_vec_int (mword_of_int (KernelSyms.memcmp + 0x0e) : mword 64) 4
                     = mword_of_int (KernelSyms.memcmp + 0x12))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp12) in "Hpc".
      assert (HR5a3 : R5 !!! Regidx Ra3 = add_vec (mword_of_int (Z.of_nat n) : mword 64) s1)
        by (rewrite /R5 upd_eq; reflexivity).
      assert (HR5a0 : R5 !!! Regidx Ra0 = pa_add s1 0%nat).
      { rewrite pa_add_0. rewrite /R5 upd_ne; [exact HR4a0 | reg_neq]. }
      assert (HR5a1 : R5 !!! Regidx Ra1 = pa_add s2 0%nat).
      { rewrite pa_add_0. rewrite /R5 upd_ne; [exact HR4a1 | reg_neq]. }
      assert (HR5sp : R5 !!! Regidx csp_rs1 = pa_stk sp0 2)
        by (rewrite /R5 upd_ne; [exact HR4sp | reg_neq]).
      assert (HR5thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                         R5 !!! Regidx r = mm !!! Regidx r).
      { intros r Hr Ncsp Ns0.
        rewrite /R5 upd_ne; [apply HR4thr; assumption
                            | apply cs_ne; [vm_compute; reflexivity | exact Hr]]. }
      (* ---- +0x12 .. +0x22: the compare loop ---- *)
      iApply (mc_loop mm n f g K dq1 dq2 s1 s2 sp0 b p CID8 Hn64
                n 0%nat R5 CID8 ltac:(intros _; reflexivity) ltac:(lia) ltac:(lia)
                ltac:(intros j Hj; exfalso; lia)
                HR5sp HR5a0 HR5a1 HR5a3 HR5thr
                with "Hcg Htext Hpc Hbuf1 Hbuf2").
      iIntros (CID9 Hs9 Mt) "%HMtsp %HMtres %HMtthr Hcg Hpc Hbuf1 Hbuf2".
      (* ---- +0x2e .. +0x34: the epilogue ---- *)
      iApply (mc_tail mm Mt K (Mt !!! Regidx Ra0) sp0
                (mm !!! Regidx Rra) (mm !!! Regidx Rs0) b p
                HK ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                HMtsp ltac:(reflexivity) HMtthr
                with "Hcg Htext Hpc Hb1 Hb2").
      iIntros (CID10 Hs10 mf) "[%Hcs %Hfa0] Hcg Hpc".
      iSpecialize ("Hcont" $! CID10 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf with "Hcg Hpc Hbuf1 Hbuf2 [%] [%]").
      + exact Hcs.
      + rewrite Hfa0. exact HMtres.
  Qed.

End ProofMemcmp.

End MemcmpProof.
