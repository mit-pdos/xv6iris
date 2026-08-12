(* ProofFetchaddr.v -- the whole-function WP for xv6's fetchaddr().

     int fetchaddr(uint64 addr, uint64 *ip) {
       struct proc *p = myproc();
       if (addr >= p->sz || addr + sizeof(uint64) > p->sz) return -1;
       if (copyin(p->pagetable, (char * )ip, addr, sizeof( *ip)) != 0) return -1;
       return 0;
     }

   Twenty-six instructions, a 32-byte frame with all four slots used, three
   arms joining at the epilogue (+0x36).  The contract is SpecFetchaddr.v.

   THE ONE STRUCTURAL IDEA: the whole body is a borrow out of [proc_priv].
   [ProcInv.proc_priv_copy] is taken ONCE, right after myproc returns -- both
   the [p->sz] read the range test needs and the [p->pagetable] read copyin
   needs come out of that single accessor -- and every arm closes it,
   the two early ones at [P' := pv_upt V] with [uptd_ext_refl].  Doing it
   that way is what makes the postcondition uniform across the three arms
   instead of one shape for the arms that ran copyin and another for the
   arms that did not.

   THREE THINGS WORTH REUSING.

   * [ByteBuf.bb_word_acc] is the [↦₈ ⇄ 8 named bytes] accessor a copy
     through a caller's WORD-sized out-parameter needs.  copyin's buffer is
     [[∗ list] j ∈ seq 0 8, pa_add ip j ↦ₘ f j] at an arbitrary [f], so the
     word cannot come back holding a named value -- only [∃ w].  That is
     honest (see SpecCopyin.v) and it is why [fetchaddr_post]'s second arm
     is existential.

   * [snez a0,a0; negw a0,a0] is gcc's map from copyin's 0/-1 to
     fetchaddr's 0/-1, and BOTH read x0 as a source operand.  The generic
     leaves ([wp_sltu_s_sconf] / [wp_subw_s_sconf]) state their written
     value over [m !!! Regidx rs1], so the proof must know the ambient map
     reads x0 as zero: that is [IntrDefs.sie_cap_gpr_x0], whose pure
     conclusion keeps the bundle.  With copyin's return value case-split
     first, both values are then closed literals and [vm_compute] finishes.

   * THE FRAME IS ASYMMETRIC.  [c.addi sp,-32] pushes but [c.addi16sp sp,32]
     pops, so the two ends take DIFFERENT leaves; do not assume a function's
     push and pop words are twins. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved KernelText.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl WpSmodeIntr.
Require Import IntrDefs.
Require Import HartTp WpNext CpuOwn.
Require Import WpLock.
Require Import ProcGeom.
Require Import KallocInv.
Require Import ByteBuf.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import FdSlots ProcInv.
Require Import FileInvDefs.
Require Import CodeFetchaddr.
Require Import SpecMyproc SpecCopyin.
Require Import SpecFetchaddr.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  Pure arithmetic: the 32-byte frame.                                   *)
(* ===================================================================== *)




(* ===================================================================== *)
(*  The range test, as plain [Z] arithmetic.                              *)
(* ===================================================================== *)
(* Kept mword-FREE (durable-notes' zify-hook rule: [lia] misbehaves as soon
   as a goal mentions [bv_unsigned]), and with 2^38 / 2^64 spelled as
   literals, which [lia] cannot compute for itself. *)

Lemma fa_z_ge_bad (a s : Z) : s <= a -> ~ (a + 8 <= s).
Proof. lia. Qed.

(* the two numeric premises myproc / copyin take; [lia] cannot evaluate the
   powers, so they are [vm_compute]d once here rather than inline at the
   call (the inline-[ltac:] trap, optimization.md). *)
Lemma fa_n0 : (Z.of_nat 0%nat + 1 < 2 ^ 31)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma fa_len8 : (Z.of_nat 8%nat < 2 ^ 64)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma fa_z_range (a s : Z) :
  0 <= a -> a < s -> s <= 274877906944 -> 0 <= a + 8 < 18446744073709551616.
Proof. lia. Qed.

Lemma fa_z_lt_bad (a s : Z) : s < a + 8 -> ~ (a + 8 <= s).
Proof. lia. Qed.

Lemma fa_maxva_lit : (2 ^ 38)%Z = 274877906944%Z.
Proof. vm_compute. reflexivity. Qed.

Module FetchaddrProof (Myproc : MYPROC) (Copyin : COPYIN) : FETCHADDR.

Section ProofFetchaddr.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rtp := (mword_of_int 4 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rx0 := (mword_of_int 0 : mword 5).

  (* =================================================================== *)
  (*  The shared tail at +0x36: the epilogue, entered by all three arms.  *)
  (* =================================================================== *)
  Lemma fa_tail `{CID0 : CpuId}
      (m Mt : regfile) (av : nat) (rv : mword 64)
      (sp0 ra0 s00 s10 s20 : mword 64) (p : mword 64) (b : bool) :
    (4 <= av)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs2 = s20 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 4 ->
    Mt !!! Regidx Ra0 = rv ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr Mt (av - 4)%nat b p -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.fetchaddr + 0x36) : mword 64) -∗
    word_pointsto (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (pa_stk sp0 3) (DfracOwn 1) s10 -∗
    word_pointsto (pa_stk sp0 4) (DfracOwn 1) s20 -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf /\ mf !!! Regidx Ra0 = rv⌝ -∗
        sie_cap_gpr mf av b p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hav Hsp0 Hra0 Hs00 Hs10 Hs20 Hmtsp Hmta0 Hthr.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hb3 Hb4 Hcont".
    iPoseProof (fai_36 with "Htext") as "Hi36".
    iPoseProof (fai_38 with "Htext") as "Hi38".
    iPoseProof (fai_3a with "Htext") as "Hi3a".
    iPoseProof (fai_3c with "Htext") as "Hi3c".
    iPoseProof (fai_3e with "Htext") as "Hi3e".
    iPoseProof (fai_40 with "Htext") as "Hi40".
    (* ---- +0x36: c.ldsp ra,24(sp) ---- *)
    assert (Hpa1 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hmtsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x36))
              (mword_of_int 3 : mword 6) Rra Mt (av - 4)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi36 Hb1 [-]").
    iIntros (CIDt1 Hkt1) "Hcg Hpc Hb1".
    iEval (rewrite Hpa1) in "Hb1".
    set (T1 := <[Regidx Rra := regval_into_reg ra0]> Mt).
    change (<[Regidx Rra := regval_into_reg ra0]> Mt) with T1.
    assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x36) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchaddr + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp38) in "Hpc".
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T1 upd_ne; [exact Hmtsp | reg_neq]).
    (* ---- +0x38: c.ldsp s0,16(sp) ---- *)
    assert (Hpa2 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HT1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x38))
              (mword_of_int 2 : mword 6) Rs0 T1 (av - 4)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi38 Hb2 [-]").
    iIntros (CIDt2 Hkt2) "Hcg Hpc Hb2".
    iEval (rewrite Hpa2) in "Hb2".
    set (T2 := <[Regidx Rs0 := regval_into_reg s00]> T1).
    change (<[Regidx Rs0 := regval_into_reg s00]> T1) with T2.
    assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x38) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchaddr + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3a) in "Hpc".
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T2 upd_ne; [exact HT1sp | reg_neq]).
    (* ---- +0x3a: c.ldsp s1,8(sp) ---- *)
    assert (Hpa3 : add_vec (T2 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HT2sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa3) in "Hb3".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x3a))
              (mword_of_int 1 : mword 6) Rs1 T2 (av - 4)%nat s10 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3a Hb3 [-]").
    iIntros (CIDt3 Hkt3) "Hcg Hpc Hb3".
    iEval (rewrite Hpa3) in "Hb3".
    set (T3 := <[Regidx Rs1 := regval_into_reg s10]> T2).
    change (<[Regidx Rs1 := regval_into_reg s10]> T2) with T3.
    assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x3a) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchaddr + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3c) in "Hpc".
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T3 upd_ne; [exact HT2sp | reg_neq]).
    (* ---- +0x3c: c.ldsp s2,0(sp) ---- *)
    assert (Hpa4 : add_vec (T3 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HT3sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa4) in "Hb4".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x3c))
              (mword_of_int 0 : mword 6) Rs2 T3 (av - 4)%nat s20 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3c Hb4 [-]").
    iIntros (CIDt4 Hkt4) "Hcg Hpc Hb4".
    iEval (rewrite Hpa4) in "Hb4".
    set (T4 := <[Regidx Rs2 := regval_into_reg s20]> T3).
    change (<[Regidx Rs2 := regval_into_reg s20]> T3) with T4.
    assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x3c) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchaddr + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3e) in "Hpc".
    assert (HT4sp : T4 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T4 upd_ne; [exact HT3sp | reg_neq]).
    (* ---- +0x3e: c.addi16sp sp,32 (frame pop) ---- *)
    assert (Hwv : add_vec (T4 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0)
      by (rewrite HT4sp; apply stk_pop_32).
    assert (Hpop : T4 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T4 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4)
      by (rewrite Hwv; exact HT4sp).
    iDestruct (stack_own_4_intro sp0 ra0 s00 s10 s20 with "Hb1 Hb2 Hb3 Hb4") as "Hframe".
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x3e))
              (mword_of_int 2 : mword 6) T4 (av - 4)%nat 4 b Hpop
              with "Hcg Hpc Hi3e Hframe [-]").
    iIntros (CIDt5 Hkt5) "Hcg Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x3e) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchaddr + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp40) in "Hpc".
    set (T5 := <[Regidx csp_rs1 := regval_into_reg (add_vec (T4 !!! Regidx csp_rs1)
                  (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> T4).
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (T4 !!! Regidx csp_rs1)
              (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> T4) with T5.
    (* ---- +0x40: c.ret ---- *)
    assert (HT5ra : T5 !!! Regidx Rra = ra0).
    { rewrite /T5 upd_ne; [| reg_neq].
      rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_ne; [| reg_neq].
      rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x40))
              Rra T5 av b ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi40 [-]").
    iIntros (CIDt6 Hkt6) "Hcg Hpc".
    iEval (rewrite (rget_ne (CID := CIDt5) T5 Rra ltac:(vm_compute; discriminate))) in "Hpc".
    iEval (rewrite HT5ra) in "Hpc".
    (* ---- the postcondition ---- *)
    assert (HT5sp : T5 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite /T5 upd_eq Hwv; symmetry; exact Hsp0).
    assert (HT5s0 : T5 !!! Regidx Rs0 = m !!! Regidx Rs0).
    { rewrite /T5 upd_ne; [| reg_neq].
      rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_ne; [| reg_neq].
      rewrite /T2 upd_eq. symmetry; exact Hs00. }
    assert (HT5s1 : T5 !!! Regidx Rs1 = m !!! Regidx Rs1).
    { rewrite /T5 upd_ne; [| reg_neq].
      rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_eq. symmetry; exact Hs10. }
    assert (HT5s2 : T5 !!! Regidx Rs2 = m !!! Regidx Rs2).
    { rewrite /T5 upd_ne; [| reg_neq].
      rewrite /T4 upd_eq. symmetry; exact Hs20. }
    assert (HT5a0 : T5 !!! Regidx Ra0 = rv).
    { rewrite /T5 upd_ne; [| reg_neq].
      rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_ne; [| reg_neq].
      rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_ne; [| reg_neq]. exact Hmta0. }
    assert (Hthr5 : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
              T5 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /T5 upd_ne; [| congruence].
      rewrite /T4 upd_ne; [| congruence].
      rewrite /T3 upd_ne; [| congruence].
      rewrite /T2 upd_ne; [| congruence].
      rewrite /T1 upd_ne; [| congruence].
      apply Hthr; assumption. }
    iSpecialize ("Hcont" $! CIDt6 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! T5 with "[%] Hcg Hpc").
    split; [| exact HT5a0].
    unfold callee_saved.
    split; [exact HT5sp|].
    split; [exact HT5s0|].
    split; [exact HT5s1|].
    split; [exact HT5s2|].
    split; [apply Hthr5; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr5; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr5; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr5; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr5; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr5; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr5; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr5; vm_compute; first [reflexivity | discriminate]|].
    apply Hthr5; vm_compute; first [reflexivity | discriminate].
  Qed.

  (* =================================================================== *)
  (*  THE CAPSTONE.                                                       *)
  (* =================================================================== *)
  Lemma wp_fetchaddr_sconf (γa : gname) (γf : gname)
      (m : regfile) (av : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (oldv : mword 64) (b : bool)
    : wp_fetchaddr_sconf_body γa γf m av eb p C pid V oldv b.
  Proof.
    cbv beta delta [wp_fetchaddr_sconf_body].
    intros pcE addr ip ret_tgt Hav.
    unfold fetchaddr_stack in Hav.
    set (sp0 := m !!! Regidx csp_rs1).
    set (ra0 := m !!! Regidx Rra).
    set (s00 := m !!! Regidx Rs0).
    set (s10 := m !!! Regidx Rs1).
    set (s20 := m !!! Regidx Rs2).
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    iIntros "Hcg Hcpu #Htext Hpc Hpriv #Henv Hip Hcont".
    iPoseProof (fai_00 with "Htext") as "Hi00".
    iPoseProof (fai_02 with "Htext") as "Hi02".
    iPoseProof (fai_04 with "Htext") as "Hi04".
    iPoseProof (fai_06 with "Htext") as "Hi06".
    iPoseProof (fai_08 with "Htext") as "Hi08".
    iPoseProof (fai_0a with "Htext") as "Hi0a".
    iPoseProof (fai_0c with "Htext") as "Hi0c".
    iPoseProof (fai_0e with "Htext") as "Hi0e".
    iPoseProof (fai_10 with "Htext") as "Hi10".
    iPoseProof (fai_14 with "Htext") as "Hi14".
    iPoseProof (fai_16 with "Htext") as "Hi16".
    iPoseProof (fai_1a with "Htext") as "Hi1a".
    iPoseProof (fai_1e with "Htext") as "Hi1e".
    iPoseProof (fai_22 with "Htext") as "Hi22".
    iPoseProof (fai_24 with "Htext") as "Hi24".
    iPoseProof (fai_26 with "Htext") as "Hi26".
    iPoseProof (fai_28 with "Htext") as "Hi28".
    iPoseProof (fai_2a with "Htext") as "Hi2a".
    iPoseProof (fai_2e with "Htext") as "Hi2e".
    iPoseProof (fai_32 with "Htext") as "Hi32".
    iPoseProof (fai_42 with "Htext") as "Hi42".
    iPoseProof (fai_44 with "Htext") as "Hi44".
    iPoseProof (fai_46 with "Htext") as "Hi46".
    iPoseProof (fai_48 with "Htext") as "Hi48".
    (* ---- +0x00: c.addi sp,-32 (frame push) ---- *)
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m av 4 b
              ltac:(lia) (stk_push_32 (m !!! Regidx csp_rs1))
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hk1) "Hcg Hframe Hpc".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.fetchaddr + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /M1 upd_eq; apply stk_push_32).
    iDestruct (stack_own_4_elim with "Hframe") as (u1 u2 u3 u4) "(Hs1 & Hs2 & Hs3 & Hs4)".
    (* ---- +0x02 .. +0x08: save ra / s0 / s1 / s2 ---- *)
    assert (Hpa1 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa2 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa3 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa4 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa1) in "Hs1".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x02))
              (mword_of_int 3 : mword 6) Rra M1 (av - 4)%nat u1 b
              with "Hcg Hpc Hi02 Hs1 [-]").
    iIntros (CID2 Hk2) "Hcg Hpc Hs1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchaddr + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    iEval (rewrite -Hpa2) in "Hs2".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x04))
              (mword_of_int 2 : mword 6) Rs0 M1 (av - 4)%nat u2 b
              with "Hcg Hpc Hi04 Hs2 [-]").
    iIntros (CID3 Hk3) "Hcg Hpc Hs2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchaddr + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    iEval (rewrite -Hpa3) in "Hs3".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x06))
              (mword_of_int 1 : mword 6) Rs1 M1 (av - 4)%nat u3 b
              with "Hcg Hpc Hi06 Hs3 [-]").
    iIntros (CID4 Hk4) "Hcg Hpc Hs3".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchaddr + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    iEval (rewrite -Hpa4) in "Hs4".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x08))
              (mword_of_int 0 : mword 6) Rs2 M1 (av - 4)%nat u4 b
              with "Hcg Hpc Hi08 Hs4 [-]").
    iIntros (CID5 Hk5) "Hcg Hpc Hs4".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x08) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchaddr + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* name the four saved values *)
    assert (HM1ra : M1 !!! Regidx Rra = ra0)
      by (rewrite /M1 upd_ne; [reflexivity | reg_neq]).
    assert (HM1s0 : M1 !!! Regidx Rs0 = s00)
      by (rewrite /M1 upd_ne; [reflexivity | reg_neq]).
    assert (HM1s1 : M1 !!! Regidx Rs1 = s10)
      by (rewrite /M1 upd_ne; [reflexivity | reg_neq]).
    assert (HM1s2 : M1 !!! Regidx Rs2 = s20)
      by (rewrite /M1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite (rget_ne (CID := CID1) M1 Rra ltac:(vm_compute; discriminate)) Hpa1 HM1ra) in "Hs1".
    iEval (rewrite (rget_ne (CID := CID2) M1 Rs0 ltac:(vm_compute; discriminate)) Hpa2 HM1s0) in "Hs2".
    iEval (rewrite (rget_ne (CID := CID3) M1 Rs1 ltac:(vm_compute; discriminate)) Hpa3 HM1s1) in "Hs3".
    iEval (rewrite (rget_ne (CID := CID4) M1 Rs2 ltac:(vm_compute; discriminate)) Hpa4 HM1s2) in "Hs4".
    (* ---- +0x0a: c.addi4spn s0,sp,32 (s0's VALUE is never read) ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x0a))
              (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) Rs0
              M1 (av - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a [-]").
    iIntros (CID6 Hk6) "Hcg Hpc".
    set (M2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1).
    change (<[Regidx Rs0 := regval_into_reg
              (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1) with M2.
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x0a) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchaddr + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* ---- +0x0c: c.mv s1,a0 -- s1 := addr ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x0c))
              Rs1 Ra0 M2 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c [-]").
    iIntros (CID7 Hk7) "Hcg Hpc".
    set (M3 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (M2 !!! Regidx Ra0))]> M2).
    change (<[Regidx Rs1 := regval_into_reg (add_vec zero_reg (M2 !!! Regidx Ra0))]> M2) with M3.
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x0c) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchaddr + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    assert (HM2a0 : M2 !!! Regidx Ra0 = addr).
    { rewrite /M2 upd_ne; [| reg_neq]. rewrite /M1 upd_ne; [reflexivity | reg_neq]. }
    assert (HM3s1 : M3 !!! Regidx Rs1 = addr)
      by (rewrite /M3 upd_eq HM2a0; apply add_vec_zero_l).
    (* ---- +0x0e: c.mv s2,a1 -- s2 := ip ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x0e))
              Rs2 Ra1 M3 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e [-]").
    iIntros (CID8 Hk8) "Hcg Hpc".
    set (M4 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (M3 !!! Regidx Ra1))]> M3).
    change (<[Regidx Rs2 := regval_into_reg (add_vec zero_reg (M3 !!! Regidx Ra1))]> M3) with M4.
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x0e) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchaddr + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    assert (HM3a1 : M3 !!! Regidx Ra1 = ip).
    { rewrite /M3 upd_ne; [| reg_neq]. rewrite /M2 upd_ne; [| reg_neq].
      rewrite /M1 upd_ne; [reflexivity | reg_neq]. }
    assert (HM4s2 : M4 !!! Regidx Rs2 = ip)
      by (rewrite /M4 upd_eq HM3a1; apply add_vec_zero_l).
    assert (HM4s1 : M4 !!! Regidx Rs1 = addr)
      by (rewrite /M4 upd_ne; [exact HM3s1 | reg_neq]).
    (* ---- +0x10: jal ra,myproc ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x10))
              Rra (mword_of_int 2093422 : mword 21) M4 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi10 [-]").
    iIntros (CID9 Hk9) "Hcg Hpc".
    set (M5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x10) : mword 64) 4)]> M4).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x10) : mword 64) 4)]> M4) with M5.
    assert (Hjmp : add_vec (mword_of_int (KernelSyms.fetchaddr + 0x10) : mword 64)
                     (sign_extend' 64 (mword_of_int 2093422 : mword 21)) = mword_of_int KernelSyms.myproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmp) in "Hpc".
    assert (HM5ra : M5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x10) : mword 64) 4)
      by (rewrite /M5 upd_eq; reflexivity).
    assert (HM5sp : M5 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite /M5 upd_ne; [| reg_neq]. rewrite /M4 upd_ne; [| reg_neq].
      rewrite /M3 upd_ne; [| reg_neq]. rewrite /M2 upd_ne; [| reg_neq]. exact HM1sp. }
    assert (HM5s1 : M5 !!! Regidx Rs1 = addr)
      by (rewrite /M5 upd_ne; [exact HM4s1 | reg_neq]).
    assert (HM5s2 : M5 !!! Regidx Rs2 = ip)
      by (rewrite /M5 upd_ne; [exact HM4s2 | reg_neq]).
    (* ---- myproc(): a0 = p ---- *)
    (* [Hcpu] was established at the entry hart; the nine leaf steps above may
       have moved us to another one, so re-anchor it before myproc's own
       [cpu_own] premise can take it. *)
    iDestruct (cpu_own_transport CID CID9 0%nat eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Myproc.wp_myproc_sconf M5 (av - 4)%nat 0%nat eb p C b
              fa_n0 ltac:(lia)
              with "Hcg Hcpu Htext Hpc [-]").
    iIntros (CID10 Hk10 ms A) "%Hms Hcg Hcpu Hpc %HcsA".
    destruct HcsA as [HcsA HAa0].
    assert (Hpc14 : ret_pc (M5 !!! Regidx Rra) = mword_of_int (KernelSyms.fetchaddr + 0x14))
      by (rewrite HM5ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    (* what fetchaddr parked across the call *)
    assert (HAsp : A !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite (callee_saved_lookup HcsA csp_rs1 ltac:(vm_compute; reflexivity)); exact HM5sp).
    assert (HAs1 : A !!! Regidx Rs1 = addr)
      by (rewrite (callee_saved_lookup HcsA (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HM5s1).
    assert (HAs2 : A !!! Regidx Rs2 = ip)
      by (rewrite (callee_saved_lookup HcsA (mword_of_int 18) ltac:(vm_compute; reflexivity)); exact HM5s2).
    (* the residual threading fact every arm hands to [fa_tail] *)
    assert (HthrA : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> A !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite (callee_saved_lookup HcsA r Hr).
      rewrite /M5 upd_ne; [| congruence].
      rewrite /M4 upd_ne; [| congruence].
      rewrite /M3 upd_ne; [| congruence].
      rewrite /M2 upd_ne; [| congruence].
      rewrite /M1 upd_ne; [| congruence]. reflexivity. }
    (* ---- the ONE borrow out of [proc_priv] ---- *)
    iDestruct (proc_priv_sz_bound with "Hpriv") as %Hszb.
    iDestruct (proc_priv_copy with "Hpriv") as "(Hszc & Hptc & Hpt & Hpback)".
    (* ---- +0x14: c.ld a5,72(a0) -- a5 := p->sz ---- *)
    assert (Hszaddr : add_vec (A !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 72 : mword 12)) = p_sz p)
      by (rewrite HAa0; reflexivity).
    iEval (rewrite -Hszaddr) in "Hszc".
    iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x14)) Ra5 Ra0
              (mword_of_int 72 : mword 12) A (av - 4)%nat (pv_sz V) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 Hszc [-]").
    iIntros (CID11 Hk11) "Hcg Hpc Hszc".
    iEval (rewrite Hszaddr) in "Hszc".
    set (A1 := <[Regidx Ra5 := regval_into_reg (pv_sz V)]> A).
    change (<[Regidx Ra5 := regval_into_reg (pv_sz V)]> A) with A1.
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x14) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchaddr + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    assert (HA1a5 : A1 !!! Regidx Ra5 = pv_sz V) by (rewrite /A1 upd_eq; reflexivity).
    assert (HA1s1 : A1 !!! Regidx Rs1 = addr)
      by (rewrite /A1 upd_ne; [exact HAs1 | reg_neq]).
    assert (HA1s2 : A1 !!! Regidx Rs2 = ip)
      by (rewrite /A1 upd_ne; [exact HAs2 | reg_neq]).
    assert (HA1sp : A1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /A1 upd_ne; [exact HAsp | reg_neq]).
    assert (HA1a0 : A1 !!! Regidx Ra0 = p)
      by (rewrite /A1 upd_ne; [exact HAa0 | reg_neq]).
    assert (HthrA1 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> A1 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      assert (N15 : r <> mword_of_int 15)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /A1 upd_ne; [| congruence]. apply HthrA; assumption. }
    (* the MAXVA bound, as a plain-[Z] fact *)
    rewrite fa_maxva_lit in Hszb.
    (* ---- +0x16: bgeu s1,a5 -- addr >=u p->sz ---- *)
    destruct (zopz0zKzJ_u (A1 !!! Regidx Rs1) (A1 !!! Regidx Ra5)) eqn:Hbge.
    - (* ======= addr >= sz: return -1 without touching *ip ======= *)
      assert (Hbad : ~ fetch_ok addr (pv_sz V)).
      { unfold fetch_ok. rewrite HA1s1 HA1a5 in Hbge.
        unfold zopz0zKzJ_u in Hbge. rewrite Z.geb_leb in Hbge.
        apply Z.leb_le in Hbge. apply fa_z_ge_bad. exact Hbge. }
      iApply (wp_bgeu_taken_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x16))
                (mword_of_int 44 : mword 13) Ra5 Rs1 A1 (av - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hbge ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi16 [-]").
      iNext. iIntros (CID12 Hk12) "Hcg Hpc".
      assert (Hjb : add_vec (mword_of_int (KernelSyms.fetchaddr + 0x16) : mword 64)
                      (sign_extend' 64 (mword_of_int 44 : mword 13))
                    = mword_of_int (KernelSyms.fetchaddr + 0x42))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjb) in "Hpc".
      (* ---- +0x42: c.li a0,-1 ---- *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x42))
                Ra0 (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64) A1 (av - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi42 [-]").
      iIntros (CID13 Hk13) "Hcg Hpc".
      set (E1 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> A1).
      change (<[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> A1) with E1.
      assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x42) : mword 64) 2
                      = mword_of_int (KernelSyms.fetchaddr + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp44) in "Hpc".
      (* ---- +0x44: c.j -0x0e ---- *)
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x44))
                (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0")))
                E1 (av - 4)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi44 [-]").
      iIntros (CID14 Hk14). iNext. iIntros "Hcg Hpc".
      assert (Hjc : add_vec (mword_of_int (KernelSyms.fetchaddr + 0x44) : mword 64)
                      (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0"))))
                    = mword_of_int (KernelSyms.fetchaddr + 0x36))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjc) in "Hpc".
      (* ---- the epilogue ---- *)
      assert (HE1sp : E1 !!! Regidx csp_rs1 = pa_stk sp0 4)
        by (rewrite /E1 upd_ne; [exact HA1sp | reg_neq]).
      assert (HE1a0 : E1 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64))
        by (rewrite /E1 upd_eq; reflexivity).
      assert (HthrE1 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> E1 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18.
        assert (N10 : r <> mword_of_int 10)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /E1 upd_ne; [| congruence]. apply HthrA1; assumption. }
      iApply (fa_tail m E1 av (mword_of_int (-1) : mword 64) sp0 ra0 s00 s10 s20 p b
                ltac:(lia) eq_refl eq_refl eq_refl eq_refl eq_refl
                HE1sp HE1a0 HthrE1
                with "Hcg Htext Hpc Hs1 Hs2 Hs3 Hs4 [-]").
      iIntros (CID15 Hk15 mf) "[%Hcsf %Hfa0] Hcg Hpc".
      iAssert (⌜uptd_ext_sz (pv_sz V) (pv_upt V) (pv_upt V)⌝)%I as "#Hxr";
        [iPureIntro; apply uptd_ext_sz_refl|].
      iDestruct ("Hpback" $! (pv_upt V) with "Hxr Hszc Hptc Hpt") as "Hpriv".
      iDestruct (cpu_own_transport CID10 CID15 0%nat eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iSpecialize ("Hcont" $! CID15 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf (pv_upt V) with "[%] [%] Hcg Hcpu Hpc Hpriv [Hip]").
      { exact Hcsf. }
      { apply uptd_ext_refl. }
      iLeft. iFrame "Hip". iPureIntro. split; [exact Hfa0 | exact Hbad].
    - (* ======= addr < sz: on to the second test ======= *)
      assert (Hlt : (uint addr < uint (pv_sz V))%Z).
      { rewrite HA1s1 HA1a5 in Hbge. unfold zopz0zKzJ_u in Hbge.
        rewrite Z.geb_leb in Hbge. by apply Z.leb_gt in Hbge. }
      iApply (wp_bgeu_fall_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x16))
                (mword_of_int 44 : mword 13) Ra5 Rs1 A1 (av - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hbge
                with "Hcg Hpc Hi16 [-]").
      iIntros (CID12 Hk12) "Hcg Hpc".
      assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x16) : mword 64) 4
                      = mword_of_int (KernelSyms.fetchaddr + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1a) in "Hpc".
      (* ---- +0x1a: addi a4,s1,8 ---- *)
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x1a))
                Ra4 Rs1 (mword_of_int 8 : mword 12) A1 (av - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi1a [-]").
      iIntros (CID13 Hk13) "Hcg Hpc".
      set (A2 := <[Regidx Ra4 := regval_into_reg
                    (add_vec (A1 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 8 : mword 12)))]> A1).
      change (<[Regidx Ra4 := regval_into_reg
                (add_vec (A1 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 8 : mword 12)))]> A1) with A2.
      assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x1a) : mword 64) 4
                      = mword_of_int (KernelSyms.fetchaddr + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1e) in "Hpc".
      (* [addr + 8] does not wrap: [addr < p->sz <= MAXVA] *)
      assert (Hc8 : bv_unsigned (sign_extend' 64 (mword_of_int 8 : mword 12) : mword 64) = 8)
        by (vm_compute; reflexivity).
      assert (Ha8 : (uint (A2 !!! Regidx Ra4) = uint addr + 8)%Z).
      { pose proof (bv_unsigned_in_range _ addr) as [Hlo _].
        pose proof Hlt as Hlt'. rewrite !uint_unsigned in Hlt'.
        pose proof Hszb as Hszb'. rewrite uint_unsigned in Hszb'.
        assert (Hm : bv_modulus 64 = 18446744073709551616%Z) by (vm_compute; reflexivity).
        rewrite /A2 upd_eq HA1s1. rewrite !uint_unsigned.
        rewrite add_vec64_unsigned Hc8.
        rewrite bv_wrap_small; [reflexivity|].
        rewrite Hm. exact (fa_z_range _ _ Hlo Hlt' Hszb'). }
      assert (HA2a5 : A2 !!! Regidx Ra5 = pv_sz V)
        by (rewrite /A2 upd_ne; [exact HA1a5 | reg_neq]).
      assert (HA2s1 : A2 !!! Regidx Rs1 = addr)
        by (rewrite /A2 upd_ne; [exact HA1s1 | reg_neq]).
      assert (HA2s2 : A2 !!! Regidx Rs2 = ip)
        by (rewrite /A2 upd_ne; [exact HA1s2 | reg_neq]).
      assert (HA2sp : A2 !!! Regidx csp_rs1 = pa_stk sp0 4)
        by (rewrite /A2 upd_ne; [exact HA1sp | reg_neq]).
      assert (HA2a0 : A2 !!! Regidx Ra0 = p)
        by (rewrite /A2 upd_ne; [exact HA1a0 | reg_neq]).
      assert (HthrA2 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> A2 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18.
        assert (N14 : r <> mword_of_int 14)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /A2 upd_ne; [| congruence]. apply HthrA1; assumption. }
      (* ---- +0x1e: bltu a5,a4 -- p->sz <u addr + 8 ---- *)
      destruct (zopz0zI_u (A2 !!! Regidx Ra5) (A2 !!! Regidx Ra4)) eqn:Hblt.
      + (* ------- sz < addr + 8: return -1 ------- *)
        assert (Hbad : ~ fetch_ok addr (pv_sz V)).
        { unfold fetch_ok. unfold zopz0zI_u in Hblt. apply Z.ltb_lt in Hblt.
          rewrite HA2a5 Ha8 in Hblt. apply fa_z_lt_bad. lia. }
        iApply (wp_bltu_taken_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x1e))
                  (mword_of_int 40 : mword 13) Ra4 Ra5 A2 (av - 4)%nat b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hblt ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi1e [-]").
        iNext. iIntros (CID14 Hk14) "Hcg Hpc".
        assert (Hjb : add_vec (mword_of_int (KernelSyms.fetchaddr + 0x1e) : mword 64)
                        (sign_extend' 64 (mword_of_int 40 : mword 13))
                      = mword_of_int (KernelSyms.fetchaddr + 0x46))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjb) in "Hpc".
        (* ---- +0x46: c.li a0,-1 ---- *)
        iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x46))
                  Ra0 (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64) A2 (av - 4)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc Hi46 [-]").
        iIntros (CID15 Hk15) "Hcg Hpc".
        set (E2 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> A2).
        change (<[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> A2) with E2.
        assert (Hpp48 : add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x46) : mword 64) 2
                        = mword_of_int (KernelSyms.fetchaddr + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp48) in "Hpc".
        (* ---- +0x48: c.j -0x12 ---- *)
        iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x48))
                  (sign_extend' 21 (concat_vec (mword_of_int 2039 : mword 11) ('b"0")))
                  E2 (av - 4)%nat b ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi48 [-]").
        iIntros (CID16 Hk16). iNext. iIntros "Hcg Hpc".
        assert (Hjc : add_vec (mword_of_int (KernelSyms.fetchaddr + 0x48) : mword 64)
                        (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2039 : mword 11) ('b"0"))))
                      = mword_of_int (KernelSyms.fetchaddr + 0x36))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjc) in "Hpc".
        assert (HE2sp : E2 !!! Regidx csp_rs1 = pa_stk sp0 4)
          by (rewrite /E2 upd_ne; [exact HA2sp | reg_neq]).
        assert (HE2a0 : E2 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64))
          by (rewrite /E2 upd_eq; reflexivity).
        assert (HthrE2 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                  r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> E2 !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8 N9 N18.
          assert (N10 : r <> mword_of_int 10)
            by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          rewrite /E2 upd_ne; [| congruence]. apply HthrA2; assumption. }
        iApply (fa_tail m E2 av (mword_of_int (-1) : mword 64) sp0 ra0 s00 s10 s20 p b
                  ltac:(lia) eq_refl eq_refl eq_refl eq_refl eq_refl
                  HE2sp HE2a0 HthrE2
                  with "Hcg Htext Hpc Hs1 Hs2 Hs3 Hs4 [-]").
        iIntros (CID17 Hk17 mf) "[%Hcsf %Hfa0] Hcg Hpc".
        iAssert (⌜uptd_ext_sz (pv_sz V) (pv_upt V) (pv_upt V)⌝)%I as "#Hxr";
          [iPureIntro; apply uptd_ext_sz_refl|].
        iDestruct ("Hpback" $! (pv_upt V) with "Hxr Hszc Hptc Hpt") as "Hpriv".
        iDestruct (cpu_own_transport CID10 CID17 0%nat eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
        iSpecialize ("Hcont" $! CID17 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! mf (pv_upt V) with "[%] [%] Hcg Hcpu Hpc Hpriv [Hip]").
        { exact Hcsf. }
        { apply uptd_ext_refl. }
        iLeft. iFrame "Hip". iPureIntro. split; [exact Hfa0 | exact Hbad].
      + (* ------- the whole doubleword is in range: call copyin ------- *)
        assert (Hok : fetch_ok addr (pv_sz V)).
        { unfold fetch_ok. unfold zopz0zI_u in Hblt. apply Z.ltb_ge in Hblt.
          rewrite HA2a5 Ha8 in Hblt. lia. }
        iApply (wp_bltu_fall_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x1e))
                  (mword_of_int 40 : mword 13) Ra4 Ra5 A2 (av - 4)%nat b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hblt
                  with "Hcg Hpc Hi1e [-]").
        iIntros (CID14 Hk14) "Hcg Hpc".
        assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x1e) : mword 64) 4
                        = mword_of_int (KernelSyms.fetchaddr + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp22) in "Hpc".
        (* ---- +0x22: c.li a3,8 -- len = sizeof(uint64) ---- *)
        iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x22))
                  Ra3 (mword_of_int 8 : mword 6) (mword_of_int 8 : mword 64) A2 (av - 4)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc Hi22 [-]").
        iIntros (CID15 Hk15) "Hcg Hpc".
        set (A3 := <[Regidx Ra3 := regval_into_reg (mword_of_int 8 : mword 64)]> A2).
        change (<[Regidx Ra3 := regval_into_reg (mword_of_int 8 : mword 64)]> A2) with A3.
        assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x22) : mword 64) 2
                        = mword_of_int (KernelSyms.fetchaddr + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp24) in "Hpc".
        (* ---- +0x24: c.mv a2,s1 -- srcva = addr ---- *)
        iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x24))
                  Ra2 Rs1 A3 (av - 4)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi24 [-]").
        iIntros (CID16 Hk16) "Hcg Hpc".
        set (A4 := <[Regidx Ra2 := regval_into_reg (add_vec zero_reg (A3 !!! Regidx Rs1))]> A3).
        change (<[Regidx Ra2 := regval_into_reg (add_vec zero_reg (A3 !!! Regidx Rs1))]> A3) with A4.
        assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x24) : mword 64) 2
                        = mword_of_int (KernelSyms.fetchaddr + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp26) in "Hpc".
        (* ---- +0x26: c.mv a1,s2 -- dst = ip ---- *)
        iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x26))
                  Ra1 Rs2 A4 (av - 4)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi26 [-]").
        iIntros (CID17 Hk17) "Hcg Hpc".
        set (A5 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (A4 !!! Regidx Rs2))]> A4).
        change (<[Regidx Ra1 := regval_into_reg (add_vec zero_reg (A4 !!! Regidx Rs2))]> A4) with A5.
        assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x26) : mword 64) 2
                        = mword_of_int (KernelSyms.fetchaddr + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp28) in "Hpc".
        assert (HA4s2 : A4 !!! Regidx Rs2 = ip).
        { rewrite /A4 upd_ne; [| reg_neq]. rewrite /A3 upd_ne; [exact HA2s2 | reg_neq]. }
        assert (HA5a1 : A5 !!! Regidx Ra1 = ip)
          by (rewrite /A5 upd_eq HA4s2; apply add_vec_zero_l).
        assert (HA5a0 : A5 !!! Regidx Ra0 = p).
        { rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
          rewrite /A3 upd_ne; [exact HA2a0 | reg_neq]. }
        (* ---- +0x28: c.ld a0,80(a0) -- a0 := p->pagetable ---- *)
        assert (Hptaddr : add_vec (A5 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 80 : mword 12))
                          = p_pagetable p)
          by (rewrite HA5a0; reflexivity).
        iEval (rewrite -Hptaddr) in "Hptc".
        iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x28)) Ra0 Ra0
                  (mword_of_int 80 : mword 12) A5 (av - 4)%nat (page_base (ud_root (pv_upt V))) b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi28 Hptc [-]").
        iIntros (CID18 Hk18) "Hcg Hpc Hptc".
        iEval (rewrite Hptaddr) in "Hptc".
        set (A6 := <[Regidx Ra0 := regval_into_reg (page_base (ud_root (pv_upt V)))]> A5).
        change (<[Regidx Ra0 := regval_into_reg (page_base (ud_root (pv_upt V)))]> A5) with A6.
        assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x28) : mword 64) 2
                        = mword_of_int (KernelSyms.fetchaddr + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp2a) in "Hpc".
        (* ---- +0x2a: jal ra,copyin ---- *)
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x2a))
                  Rra (mword_of_int 2092850 : mword 21) A6 (av - 4)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi2a [-]").
        iIntros (CID19 Hk19) "Hcg Hpc".
        set (A7 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x2a) : mword 64) 4)]> A6).
        change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x2a) : mword 64) 4)]> A6) with A7.
        assert (Hjci : add_vec (mword_of_int (KernelSyms.fetchaddr + 0x2a) : mword 64)
                         (sign_extend' 64 (mword_of_int 2092850 : mword 21)) = mword_of_int KernelSyms.copyin)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjci) in "Hpc".
        assert (HA7ra : A7 !!! Regidx Rra
                        = add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x2a) : mword 64) 4)
          by (rewrite /A7 upd_eq; reflexivity).
        assert (HA7a0 : A7 !!! Regidx Ra0 = page_base (ud_root (pv_upt V))).
        { rewrite /A7 upd_ne; [| reg_neq]. rewrite /A6 upd_eq. reflexivity. }
        assert (HA7a1 : A7 !!! Regidx Ra1 = ip).
        { rewrite /A7 upd_ne; [| reg_neq]. rewrite /A6 upd_ne; [| reg_neq]. exact HA5a1. }
        assert (HA7a3 : A7 !!! Regidx Ra3 = (mword_of_int 8 : mword 64)).
        { rewrite /A7 upd_ne; [| reg_neq]. rewrite /A6 upd_ne; [| reg_neq].
          rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
          rewrite /A3 upd_eq. reflexivity. }
        assert (HA7sp : A7 !!! Regidx csp_rs1 = pa_stk sp0 4).
        { rewrite /A7 upd_ne; [| reg_neq]. rewrite /A6 upd_ne; [| reg_neq].
          rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
          rewrite /A3 upd_ne; [exact HA2sp | reg_neq]. }
        assert (HthrA7 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                  r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> A7 !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8 N9 N18.
          assert (N1 : r <> mword_of_int 1)
            by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          assert (N10 : r <> mword_of_int 10)
            by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          assert (N11 : r <> mword_of_int 11)
            by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          assert (N12 : r <> mword_of_int 12)
            by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          assert (N13 : r <> mword_of_int 13)
            by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          rewrite /A7 upd_ne; [| congruence].
          rewrite /A6 upd_ne; [| congruence].
          rewrite /A5 upd_ne; [| congruence].
          rewrite /A4 upd_ne; [| congruence].
          rewrite /A3 upd_ne; [| congruence]. apply HthrA2; assumption. }
        assert (HK50 : (50 <= av - 4)%nat) by lia.
        assert (HA7len : A7 !!! Regidx Ra3 = (mword_of_int (Z.of_nat 8%nat) : mword 64)).
        { rewrite HA7a3. apply bv_eq; vm_compute; reflexivity. }
        assert (Hszb38 : (uint (pv_sz V) <= 2 ^ 38)%Z) by (rewrite fa_maxva_lit; exact Hszb).
        (* the caller's [uint64 *] AS copyin's byte buffer *)
        iDestruct (bb_word_acc with "Hip") as "[Hbuf Hipback]".
        iEval (rewrite -HA7a1) in "Hbuf".
        (* ---- copyin(p->pagetable, ip, addr, 8) ---- *)
        iDestruct (cpu_own_transport CID10 CID19 0%nat eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
        iApply (Copyin.wp_copyin_sconf γa A7 (pv_upt V) (pv_sz V) 8%nat
                  (fun j => nth_byte (oldv : mword 64) j) (av - 4)%nat 0%nat eb p C
                  (DfracOwn 1) (DfracOwn 1) b
                  HK50 HA7a0 HA7len fa_len8 Hszb38 fa_n0
                  with "Hcg Hcpu Htext Hpc Hszc Hptc Hpt Henv Hbuf [-]").
        iIntros (CID20 Hk20 mr P' dst_new) "Hcg Hcpu Hpc Hszc Hptc Hpt Hbuf %Hcsr %Hext %Hret".
        assert (Hpc2e : ret_pc (A7 !!! Regidx Rra) = mword_of_int (KernelSyms.fetchaddr + 0x2e))
          by (rewrite HA7ra; apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc2e) in "Hpc".
        iEval (rewrite HA7a1) in "Hbuf".
        iDestruct ("Hipback" $! dst_new with "Hbuf") as (wnew) "Hip".
        iAssert (⌜uptd_ext_sz (pv_sz V) (pv_upt V) P'⌝)%I as "#Hxe"; [iPureIntro; exact Hext|].
        iDestruct ("Hpback" $! P' with "Hxe Hszc Hptc Hpt") as "Hpriv".
        (* the frame and the callee-saved set survived copyin *)
        assert (Hrsp : mr !!! Regidx csp_rs1 = pa_stk sp0 4)
          by (rewrite (callee_saved_lookup Hcsr csp_rs1 ltac:(vm_compute; reflexivity)); exact HA7sp).
        assert (Hthrr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                  r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> mr !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8 N9 N18.
          rewrite (callee_saved_lookup Hcsr r Hr). apply HthrA7; assumption. }
        (* x0 reads zero -- both [snez] and [negw] use it as a source *)
        iDestruct (sie_cap_gpr_x0 mr (av - 4)%nat b p Rx0 ltac:(vm_compute; reflexivity) with "Hcg")
          as "[%Hz0 Hcg]".
        (* ---- +0x2e: snez a0,a0  (= sltu a0,x0,a0) ---- *)
        (* copyin answers 0 or -1, so BOTH written values are closed
           literals: discharge the whole two-instruction sequence up front,
           by cases, and the WP steps below never have to case-split. *)
        assert (Hpair : exists sv rv : mword 64,
                  zero_extend' 64 (bool_to_bit (zopz0zI_u zero_reg (mr !!! Regidx Ra0))) = sv /\
                  sign_extend' 64 (sub_vec (subrange_vec_dec (zero_reg : mword 64) 31 0 : mword 32)
                                           (subrange_vec_dec sv 31 0 : mword 32)) = rv /\
                  (rv = (mword_of_int 0 : mword 64) \/ rv = (mword_of_int (-1) : mword 64))).
        { destruct Hret as [H0 | H1].
          - exists (mword_of_int 0 : mword 64), (mword_of_int 0 : mword 64). rewrite H0.
            split; [apply bv_eq; vm_compute; reflexivity|].
            split; [apply bv_eq; vm_compute; reflexivity| left; reflexivity].
          - exists (mword_of_int 1 : mword 64), (mword_of_int (-1) : mword 64). rewrite H1.
            split; [apply bv_eq; vm_compute; reflexivity|].
            split; [apply bv_eq; vm_compute; reflexivity| right; reflexivity]. }
        destruct Hpair as (sv & rv & Hsv & Hrv & Hrvcase).
        assert (Hsnez : zero_extend' 64 (bool_to_bit
                          (zopz0zI_u (mr !!! Regidx Rx0) (mr !!! Regidx Ra0))) = sv)
          by (rewrite Hz0; exact Hsv).
        iApply (wp_sltu_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x2e))
                  Ra0 Rx0 Ra0 sv mr (av - 4)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok) Hsnez
                  with "Hcg Hpc Hi2e [-]").
        iIntros (CID21 Hk21) "Hcg Hpc".
        set (B1 := <[Regidx Ra0 := regval_into_reg sv]> mr).
        change (<[Regidx Ra0 := regval_into_reg sv]> mr) with B1.
        assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x2e) : mword 64) 4
                        = mword_of_int (KernelSyms.fetchaddr + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp32) in "Hpc".
        (* ---- +0x32: negw a0,a0  (= subw a0,x0,a0) ---- *)
        iApply (wp_subw_s_sconf (mword_of_int (KernelSyms.fetchaddr + 0x32))
                  Ra0 Rx0 Ra0 B1 (av - 4)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi32 [-]").
        iIntros (CID22 Hk22) "Hcg Hpc".
        set (B2 := <[Regidx Ra0 := regval_into_reg
                      (sign_extend' 64 (sub_vec (subrange_vec_dec (B1 !!! Regidx Rx0) 31 0 : mword 32)
                                                (subrange_vec_dec (B1 !!! Regidx Ra0) 31 0 : mword 32)))]> B1).
        change (<[Regidx Ra0 := regval_into_reg
                  (sign_extend' 64 (sub_vec (subrange_vec_dec (B1 !!! Regidx Rx0) 31 0 : mword 32)
                                            (subrange_vec_dec (B1 !!! Regidx Ra0) 31 0 : mword 32)))]> B1) with B2.
        assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.fetchaddr + 0x32) : mword 64) 4
                        = mword_of_int (KernelSyms.fetchaddr + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp36) in "Hpc".
        assert (HB1x0 : B1 !!! Regidx Rx0 = zero_reg)
          by (rewrite /B1 upd_ne; [exact Hz0 | reg_neq]).
        assert (HB1a0 : B1 !!! Regidx Ra0 = sv) by (rewrite /B1 upd_eq; reflexivity).
        assert (HB2a0 : B2 !!! Regidx Ra0 = rv)
          by (rewrite /B2 upd_eq HB1x0 HB1a0; exact Hrv).
        assert (HB2sp : B2 !!! Regidx csp_rs1 = pa_stk sp0 4).
        { rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [exact Hrsp | reg_neq]. }
        assert (HthrB2 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                  r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> B2 !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8 N9 N18.
          assert (N10 : r <> mword_of_int 10)
            by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          rewrite /B2 upd_ne; [| congruence].
          rewrite /B1 upd_ne; [| congruence]. apply Hthrr; assumption. }
        iApply (fa_tail m B2 av rv sp0 ra0 s00 s10 s20 p b
                  ltac:(lia) eq_refl eq_refl eq_refl eq_refl eq_refl
                  HB2sp HB2a0 HthrB2
                  with "Hcg Htext Hpc Hs1 Hs2 Hs3 Hs4 [-]").
        iIntros (CID23 Hk23 mf) "[%Hcsf %Hfa0] Hcg Hpc".
        iDestruct (cpu_own_transport CID20 CID23 0%nat eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
        iSpecialize ("Hcont" $! CID23 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! mf P' with "[%] [%] Hcg Hcpu Hpc Hpriv [Hip]").
        { exact Hcsf. }
        { exact (uptd_ext_sz_ext _ _ _ Hext). }
        iRight. iSplitR.
        { iPureIntro. split; [| exact Hok]. rewrite Hfa0. exact Hrvcase. }
        iExists wnew. iExact "Hip".
  Qed.

End ProofFetchaddr.

End FetchaddrProof.
