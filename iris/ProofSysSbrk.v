(* ProofSysSbrk.v -- the whole-function proof of sys_sbrk(), over the
   contracts of argint(), myproc() and growproc().

   Shape: a 48-byte ra/s0/s1 frame, four calls, five exits joining at ONE
   place (the [c.mv a0,s1] at +0x64).  So the proof is one shared block
   ([ss_tail]) plus a dispatch, and no loop anywhere.

   THE THREE THINGS THIS PROOF IS ABOUT:

   1. THE LAZY PATH IS WHY [um_below] IS AN INEQUALITY.  It raises [p->sz]
      and maps NOTHING; [ProcPtOwn.um_below_mono] is the whole of its
      coherence obligation.  A [p->sz]-equals-the-mapped-domain invariant
      would have made this function unprovable.

   2. BOTH [int] LOCALS SHARE ONE FRAME SLOT.  [n] is the LOWER word of slot
      5 and [t] the UPPER; the slot is split once
      ([InstrBytes.word_pointsto_split4]) and the two halves go to the two
      argint calls separately.  It is rejoined only at the epilogue, where
      both are dead.

   3. THE WRAP TEST AT +0x44 IS DEAD, and cheaply so.  [addr + n < addr]
      needs the 64-bit sum to wrap; [p->sz <= TRAPFRAME] and
      [RiscvExtras.sint64_range] put it below 2^64 with room to spare.  No
      32-bit bound on [n] is needed -- which matters, because the [lw] that
      loads it does not hand one over in any convenient form. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap sets bitvector.definitions.
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
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl WpSmodeIntr.
Require Import IntrDefs HartTp WpNext.
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import KallocInv.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import FdSlots ProcInv.
Require Import ProofKforkParts.
Require Import FileInvDefs.
Require Import CodeSysSbrk.
Require Import SpecArgint SpecMyproc SpecGrowproc SpecSysSbrk.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

Set Printing Depth 40.

(* ===================================================================== *)
(*  §1  sys_sbrk's own arithmetic, kept mword-free.                       *)
(* ===================================================================== *)

Lemma ss_n0 : (Z.of_nat 0%nat + 1 < 2 ^ 31)%Z.
Proof. vm_compute. reflexivity. Qed.

(* the sum a lazy sbrk forms cannot wrap: the size is inside the user region
   and [sint n] is below 2^63. *)
Lemma ss_z_nowrap (a b : Z) :
  0 <= a -> a <= 274877898752 -> b < 9223372036854775808 ->
  a + b < 18446744073709551616.
Proof. lia. Qed.

Lemma ss_z_le_absurd (a b : Z) : a < b -> b <= a -> False.
Proof. lia. Qed.

Module SysSbrkProof (Argint : ARGINT) (Myproc : MYPROC)
                    (Growproc : GROWPROC) : SYSSBRK.

Section ProofSysSbrk.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rtp := (mword_of_int 4 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  (* the two [int] locals, as offsets from the frame pointer [s0 = sp0] *)
  Lemma ss_addr_n (X : mword 64) :
    add_vec X (sign_extend' 64 (mword_of_int 0xfd8 : mword 12)) = pa_stk X 5.
  Proof.
    unfold pa_stk, add_vec_int. apply f_equal.
    apply bv_eq; vm_compute; reflexivity.
  Qed.


  Lemma ss_addr_t (X : mword 64) :
    add_vec X (sign_extend' 64 (mword_of_int 0xfdc : mword 12)) = pa_add (pa_stk X 5) 4.
  Proof.
    unfold pa_add, pa_stk, add_vec_int. rewrite pa_stk_off2.
    apply f_equal. apply bv_eq; vm_compute; reflexivity.
  Qed.

  (* =================================================================== *)
  (*  §2  The epilogue at +0x64, entered by all five exits.               *)
  (* =================================================================== *)
  (*   [c.mv a0,s1] then the 48-byte pop.  The return value is whatever s1
     holds -- [addr] on the three success paths, -1 on the two failures --
     which is why the two failure tails write s1 and not a0. *)
  Lemma ss_tail `{CID0 : CpuId}
      (m Mt : regfile) (av : nat) (b : bool) (p : mword 64) (rv : mword 64)
      (sp0 ra0 s00 s10 w4 w5 w6 : mword 64) :
    (6 <= av)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 6 ->
    Mt !!! Regidx Rs1 = rv ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr Mt (av - 6)%nat b p -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.sys_sbrk + 0x64) : mword 64) -∗
    word_pointsto (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (pa_stk sp0 3) (DfracOwn 1) s10 -∗
    word_pointsto (pa_stk sp0 4) (DfracOwn 1) w4 -∗
    word_pointsto (pa_stk sp0 5) (DfracOwn 1) w5 -∗
    word_pointsto (pa_stk sp0 6) (DfracOwn 1) w6 -∗
    wp_next b p (fun (CID1 : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf /\ mf !!! Regidx Ra0 = rv⌝ -∗
        sie_cap_gpr mf av b p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hav Hsp0 Hra0 Hs00 Hs10 Hmtsp Hmts1 Hthr.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hcont".
    iPoseProof (ssi_64 with "Htext") as "Hi64".
    iPoseProof (ssi_66 with "Htext") as "Hi66".
    iPoseProof (ssi_68 with "Htext") as "Hi68".
    iPoseProof (ssi_6a with "Htext") as "Hi6a".
    iPoseProof (ssi_6c with "Htext") as "Hi6c".
    iPoseProof (ssi_6e with "Htext") as "Hi6e".
    (* ---- +0x64: c.mv a0,s1 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x64))
              Ra0 Rs1 Mt (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi64").
    iIntros (CID1 Hs1) "Hcg Hpc".
    set (T0 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (Mt !!! Regidx Rs1))]> Mt).
    change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (Mt !!! Regidx Rs1))]> Mt) with T0.
    assert (Hpp66 : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x64) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_sbrk + 0x66)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp66) in "Hpc".
    assert (HT0a0 : T0 !!! Regidx Ra0 = rv)
      by (rewrite /T0 upd_eq Hmts1; apply add_vec_zero_l).
    assert (HT0sp : T0 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T0 upd_ne; [exact Hmtsp | reg_neq]).
    (* ---- +0x66: c.ldsp ra,40(sp) ---- *)
    assert (Hpa1 : add_vec (T0 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HT0sp. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x66))
              (mword_of_int 5 : mword 6) Rra T0 (av - 6)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi66 Hb1").
    iIntros (CID2 Hs2) "Hcg Hpc Hb1".
    iEval (rewrite Hpa1) in "Hb1".
    set (T1 := <[Regidx Rra := regval_into_reg ra0]> T0).
    change (<[Regidx Rra := regval_into_reg ra0]> T0) with T1.
    assert (Hpp68 : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x66) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_sbrk + 0x68)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp68) in "Hpc".
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T1 upd_ne; [exact HT0sp | reg_neq]).
    (* ---- +0x68: c.ldsp s0,32(sp) ---- *)
    assert (Hpa2 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HT1sp. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x68))
              (mword_of_int 4 : mword 6) Rs0 T1 (av - 6)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi68 Hb2").
    iIntros (CID3 Hs3) "Hcg Hpc Hb2".
    iEval (rewrite Hpa2) in "Hb2".
    set (T2 := <[Regidx Rs0 := regval_into_reg s00]> T1).
    change (<[Regidx Rs0 := regval_into_reg s00]> T1) with T2.
    assert (Hpp6a : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x68) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_sbrk + 0x6a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp6a) in "Hpc".
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T2 upd_ne; [exact HT1sp | reg_neq]).
    (* ---- +0x6a: c.ldsp s1,24(sp) ---- *)
    assert (Hpa3 : add_vec (T2 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HT2sp. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa3) in "Hb3".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x6a))
              (mword_of_int 3 : mword 6) Rs1 T2 (av - 6)%nat s10 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6a Hb3").
    iIntros (CID4 Hs4) "Hcg Hpc Hb3".
    iEval (rewrite Hpa3) in "Hb3".
    set (T3 := <[Regidx Rs1 := regval_into_reg s10]> T2).
    change (<[Regidx Rs1 := regval_into_reg s10]> T2) with T3.
    assert (Hpp6c : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x6a) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_sbrk + 0x6c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp6c) in "Hpc".
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T3 upd_ne; [exact HT2sp | reg_neq]).
    (* ---- +0x6c: c.addi16sp sp,48 (frame pop) ---- *)
    assert (Hwv : add_vec (T3 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0)
      by (rewrite HT3sp; apply stk_pop_48).
    assert (Hpop : T3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T3 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6)
      by (rewrite Hwv; exact HT3sp).
    assert (E5 : pa_stk (pa_stk sp0 4) 1 = pa_stk sp0 5) by (rewrite pa_stk_assoc; reflexivity).
    assert (E6 : pa_stk (pa_stk sp0 4) 2 = pa_stk sp0 6) by (rewrite pa_stk_assoc; reflexivity).
    iEval (rewrite -E5) in "Hb5".
    iEval (rewrite -E6) in "Hb6".
    iDestruct (stack_own_4_intro sp0 ra0 s00 s10 w4 with "Hb1 Hb2 Hb3 Hb4") as "Hf14".
    iDestruct (stack_own_2_intro (pa_stk sp0 4) w5 w6 with "Hb5 Hb6") as "Hf56".
    iAssert (stack_own sp0 6) with "[Hf14 Hf56]" as "Hframe".
    { rewrite (stack_own_split sp0 4 6 ltac:(lia)). change (6 - 4)%nat with 2%nat. iFrame. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x6c))
              (mword_of_int 3 : mword 6) T3 (av - 6)%nat 6 b Hpop
              with "Hcg Hpc Hi6c Hframe").
    iIntros (CID5 Hs5) "Hcg Hpc".
    assert (Hnk : ((av - 6) + 6)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp6e : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x6c) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_sbrk + 0x6e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp6e) in "Hpc".
    set (T4 := <[Regidx csp_rs1 := regval_into_reg (add_vec (T3 !!! Regidx csp_rs1)
                  (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> T3).
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (T3 !!! Regidx csp_rs1)
              (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> T3) with T4.
    (* ---- +0x6e: c.ret ---- *)
    assert (HT4ra : T4 !!! Regidx Rra = ra0).
    { rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_ne; [| reg_neq].
      rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x6e))
              Rra T4 av b ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi6e").
    iIntros (CID6 Hs6) "Hcg Hpc".
    iEval (rgne; rewrite HT4ra) in "Hpc".
    assert (HT4sp : T4 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite /T4 upd_eq Hwv; symmetry; exact Hsp0).
    assert (HT4s0 : T4 !!! Regidx Rs0 = m !!! Regidx Rs0).
    { rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_ne; [| reg_neq].
      rewrite /T2 upd_eq. symmetry; exact Hs00. }
    assert (HT4s1 : T4 !!! Regidx Rs1 = m !!! Regidx Rs1).
    { rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_eq. symmetry; exact Hs10. }
    assert (HT4a0 : T4 !!! Regidx Ra0 = rv).
    { rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_ne; [| reg_neq].
      rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_ne; [| reg_neq]. exact HT0a0. }
    assert (Hthr4 : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 ->
              T4 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /T4 upd_ne; [| congruence].
      rewrite /T3 upd_ne; [| congruence].
      rewrite /T2 upd_ne; [| congruence].
      rewrite /T1 upd_ne; [| congruence].
      rewrite /T0 upd_ne; [| congruence].
      apply Hthr; assumption. }
    iSpecialize ("Hcont" $! CID6 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! T4 with "[%] Hcg Hpc").
    split; [| exact HT4a0].
    unfold callee_saved.
    split; [exact HT4sp|].
    split; [exact HT4s0|].
    split; [exact HT4s1|].
    do 9 (split; [apply Hthr4; vm_compute; first [reflexivity | discriminate]|]).
    apply Hthr4; vm_compute; first [reflexivity | discriminate].
  Qed.

  (* =================================================================== *)
  (*  §3  The EAGER arm at +0x58, entered by both of the two tests.       *)
  (* =================================================================== *)
  (*   [lw a0,-40(s0); jal growproc; blt a0,x0].  Stated as a lemma rather
     than an [iAssert] because both entries need it and an [iAssert] would
     have consumed the epilogue block one of them still needs. *)
  (* A DECOMPOSED helper (porting guide): its own fresh `{CID0} binder, its
     own [(b : bool)], and its continuation wrapped in [wp_next]. *)
  Local Lemma ss_eager `{CID0 : CpuId} (γa γf : gname)
      (m Me : regfile) (av : nat) (eb : bool) (p : mword 64)
      (pid : mword 32) (V : pprivate) (sp0 : mword 64) (nw : mword 32) (b : bool) (lks : gset string) :
    (52 <= av)%nat ->
    Me !!! Regidx csp_rs1 = pa_stk sp0 6 ->
    Me !!! Regidx Rs0 = sp0 ->
    Me !!! Regidx Rs1 = pv_sz V ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> Me !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr Me (av - 6)%nat b p -∗
    cpu_own 0%nat eb p b lks -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.sys_sbrk + 0x58) : mword 64) -∗
    proc_priv γf p pid V -∗
    kalloc_env γa None -∗
    word4_pointsto (pa_stk sp0 5) (DfracOwn 1) nw -∗
    wp_next (CID0 := CID0) b p (fun (CID1 : CpuId) =>
      ∀ (Mf : regfile) (P' : uptd) (szv' rv : mword 64),
        ⌜Mf !!! Regidx csp_rs1 = pa_stk sp0 6⌝ -∗
        ⌜Mf !!! Regidx Rs1 = rv⌝ -∗
        ⌜forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
            r <> Rs0 -> r <> Rs1 -> Mf !!! Regidx r = m !!! Regidx r⌝ -∗
        ⌜ (rv = pv_sz V /\
           growproc_ok (pv_sz V) (sign_extend' 64 nw) (pv_upt V) P' szv'
                       (mword_of_int 0 : mword 64))
          \/ (rv = (mword_of_int (-1) : mword 64) /\
              P' = pv_upt V /\ szv' = pv_sz V) ⌝ -∗
        sie_cap_gpr Mf (av - 6)%nat b p -∗
        cpu_own 0%nat eb p b lks -∗
        pc_is (mword_of_int (KernelSyms.sys_sbrk + 0x64) : mword 64) -∗
        proc_priv γf p pid (upd_sz (upd_upt V P') szv') -∗
        word4_pointsto (pa_stk sp0 5) (DfracOwn 1) nw -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hav Hesp Hes0 Hes1 Hethr.
    iIntros "Hcg Hcpu #Htext Hpc Hpriv #Henv Hnw Hcont".
    iPoseProof (ssi_58 with "Htext") as "Hi58".
    iPoseProof (ssi_5c with "Htext") as "Hi5c".
    iPoseProof (ssi_60 with "Htext") as "Hi60".
    iPoseProof (ssi_70 with "Htext") as "Hi70".
    iPoseProof (ssi_72 with "Htext") as "Hi72".
    (* ---- +0x58: lw a0,-40(s0) -- a0 := n ---- *)
    assert (Hnaddr : forall CID' : CpuId,
              add_vec (rget (CID := CID') Me Rs0) (sign_extend' 64 (mword_of_int 0xfd8 : mword 12))
              = pa_stk sp0 5).
    { intros CID'; rgne. rewrite Hes0; apply ss_addr_n. }
    iEval (rewrite -(Hnaddr CID0)) in "Hnw".
    iApply (wp_lw_s_sconf (CID := CID0) (mword_of_int (KernelSyms.sys_sbrk + 0x58)) Ra0 Rs0
              (mword_of_int 0xfd8 : mword 12) Me (av - 6)%nat nw b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi58 Hnw").
    iIntros (CIDa Hsa) "Hcg Hpc Hnw".
    iEval (rewrite (Hnaddr CID0)) in "Hnw".
    set (G1 := <[Regidx Ra0 := regval_into_reg (sign_extend' 64 nw)]> Me).
    change (<[Regidx Ra0 := regval_into_reg (sign_extend' 64 nw)]> Me) with G1.
    assert (Hpp5c : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x58) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_sbrk + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5c) in "Hpc".
    (* ---- +0x5c: jal ra,growproc ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x5c))
              Rra (mword_of_int 2093628 : mword 21) G1 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi5c").
    iIntros (CIDb Hsb) "Hcg Hpc".
    set (G2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x5c) : mword 64) 4)]> G1).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x5c) : mword 64) 4)]> G1) with G2.
    assert (Hjmpgp : add_vec (mword_of_int (KernelSyms.sys_sbrk + 0x5c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2093628 : mword 21)) = mword_of_int KernelSyms.growproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmpgp) in "Hpc".
    assert (HG2a0 : G2 !!! Regidx Ra0 = sign_extend' 64 nw).
    { rewrite /G2 upd_ne; [| reg_neq]. rewrite /G1 upd_eq. reflexivity. }
    assert (HG2sp : G2 !!! Regidx csp_rs1 = pa_stk sp0 6).
    { rewrite /G2 upd_ne; [| reg_neq]. rewrite /G1 upd_ne; [| reg_neq]. exact Hesp. }
    assert (HG2s1 : G2 !!! Regidx Rs1 = pv_sz V).
    { rewrite /G2 upd_ne; [| reg_neq]. rewrite /G1 upd_ne; [| reg_neq]. exact Hes1. }
    assert (HG2ra : G2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x5c) : mword 64) 4)
      by (rewrite /G2 upd_eq; reflexivity).
    assert (HthrG2 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> G2 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /G2 upd_ne; [| congruence]. rewrite /G1 upd_ne; [| congruence].
      apply Hethr; assumption. }
    iDestruct (cpu_own_transport CID0 CIDb 0%nat eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Growproc.wp_growproc_sconf γa γf G2 (av - 6)%nat eb p pid V b lks
              ltac:(unfold growproc_stack; lia)
              with "Hcg Hcpu Htext Hpc Hpriv Henv").
    iIntros (CIDg Hsg mg P' szv') "%Hcsg %Hok Hcg Hcpu Hpc Hpriv".
    rewrite HG2a0 in Hok.
    assert (Hpc60 : ret_pc (G2 !!! Regidx Rra) = mword_of_int (KernelSyms.sys_sbrk + 0x60))
      by (rewrite HG2ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc60) in "Hpc".
    assert (Hgsp : mg !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite (callee_saved_lookup Hcsg csp_rs1 ltac:(vm_compute; reflexivity)); exact HG2sp).
    assert (Hgs1 : mg !!! Regidx Rs1 = pv_sz V)
      by (rewrite (callee_saved_lookup Hcsg (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HG2s1).
    assert (Hthrg : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> mg !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      rewrite (callee_saved_lookup Hcsg r Hr). apply HthrG2; assumption. }
    (* ---- +0x60: blt a0,x0 -- did growproc fail? ---- *)
    destruct Hok as [(Hr1 & Hp1 & Hs1') | Hok0].
    { (* growproc returned -1: [c.li s1,-1] then the epilogue *)
      assert (Hneg : zopz0zI_s (mg !!! Regidx Ra0) (zero_reg : mword 64) = true).
      { rewrite Hr1. unfold zopz0zI_s. apply Z.ltb_lt.
        assert (Hz0 : sint (zero_reg : mword 64) = 0%Z) by reflexivity. rewrite Hz0.
        vm_compute. reflexivity. }
      assert (Htgt70 : add_vec (mword_of_int (KernelSyms.sys_sbrk + 0x60) : mword 64)
                         (sign_extend' 64 (mword_of_int 16 : mword 13))
                       = mword_of_int (KernelSyms.sys_sbrk + 0x70))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_blt_x0_taken_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x60))
                (mword_of_int 16 : mword 13) Ra0 mg (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rgne; exact Hneg)
                ltac:(rewrite Htgt70; vm_compute; reflexivity)
                with "Hcg Hpc Hi60").
      iApply bi.later_intro. iIntros (CIDt Hst) "Hcg Hpc".
      iEval (rewrite Htgt70) in "Hpc".
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x70))
                Rs1 (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64) mg (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi70").
      iIntros (CIDu Hsu) "Hcg Hpc".
      set (X1 := <[Regidx Rs1 := regval_into_reg (mword_of_int (-1) : mword 64)]> mg).
      change (<[Regidx Rs1 := regval_into_reg (mword_of_int (-1) : mword 64)]> mg) with X1.
      assert (Hpp72 : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x70) : mword 64) 2
                      = mword_of_int (KernelSyms.sys_sbrk + 0x72)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp72) in "Hpc".
      assert (Htgt64 : add_vec (mword_of_int (KernelSyms.sys_sbrk + 0x72) : mword 64)
                         (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0"))))
                       = mword_of_int (KernelSyms.sys_sbrk + 0x64))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x72))
                (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0"))) X1 (av - 6)%nat b
                ltac:(rewrite Htgt64; vm_compute; reflexivity)
                with "Hcg Hpc Hi72").
      iIntros (CIDv Hsv). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt64) in "Hpc".
      iDestruct (cpu_own_transport CIDg CIDv 0%nat eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iSpecialize ("Hcont" $! CIDv with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! X1 P' szv' (mword_of_int (-1) : mword 64)
                with "[%] [%] [%] [%] Hcg Hcpu Hpc Hpriv Hnw").
      - rewrite /X1 upd_ne; [exact Hgsp | reg_neq].
      - rewrite /X1 upd_eq. reflexivity.
      - intros r Hr Ncsp N8 N9.
        rewrite /X1 upd_ne; [| congruence]. apply Hthrg; assumption.
      - right. split; [reflexivity | split; [exact Hp1 | exact Hs1']]. }
    (* growproc returned 0: fall through to the epilogue with s1 = addr *)
    assert (Hr0 : mg !!! Regidx Ra0 = (mword_of_int 0 : mword 64)).
    { destruct Hok0 as [(H & _) | [(H & _) | (H & _)]]; exact H. }
    assert (Hpos : zopz0zI_s (mg !!! Regidx Ra0) (zero_reg : mword 64) = false).
    { rewrite Hr0. unfold zopz0zI_s. apply Z.ltb_ge.
      assert (Hz0 : sint (zero_reg : mword 64) = 0%Z) by reflexivity. rewrite Hz0.
      vm_compute. discriminate. }
    iApply (wp_blt_x0_fall_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x60))
              (mword_of_int 16 : mword 13) Ra0 mg (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rgne; exact Hpos)
              with "Hcg Hpc Hi60").
    iIntros (CIDw Hsw) "Hcg Hpc".
    assert (Hpp64 : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x60) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_sbrk + 0x64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp64) in "Hpc".
    iDestruct (cpu_own_transport CIDg CIDw 0%nat eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iSpecialize ("Hcont" $! CIDw with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! mg P' szv' (pv_sz V)
              with "[%] [%] [%] [%] Hcg Hcpu Hpc Hpriv Hnw").
    - exact Hgsp.
    - exact Hgs1.
    - exact Hthrg.
    - left. split; [reflexivity |].
      rewrite <- Hr0. right. exact Hok0.
  Qed.

  (* =================================================================== *)
  (*  §4  THE CAPSTONE.                                                   *)
  (* =================================================================== *)
  Lemma wp_sys_sbrk_sconf (γa : gname) (γf : gname)
      (m : regfile) (av : nat) (eb : bool) (p : mword 64)
      (pid : mword 32) (V : pprivate) (v0 v1 : mword 64) (b : bool) (lks : gset string)
    : wp_sys_sbrk_sconf_body γa γf m av eb p pid V v0 v1 b lks.
  Proof.
    cbv beta delta [wp_sys_sbrk_sconf_body].
    intros pcE ret_tgt Harg0 Harg1 Hav.
    unfold sys_sbrk_stack in Hav.
    set (sp0 := m !!! Regidx csp_rs1).
    set (ra0 := m !!! Regidx Rra).
    set (s00 := m !!! Regidx Rs0).
    set (s10 := m !!! Regidx Rs1).
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    iIntros "Hcg Hcpu #Htext #Hdata Hpc Hpriv #Henv Hcont".
    iPoseProof (ssi_00 with "Htext") as "Hi00".
    iPoseProof (ssi_02 with "Htext") as "Hi02".
    iPoseProof (ssi_04 with "Htext") as "Hi04".
    iPoseProof (ssi_06 with "Htext") as "Hi06".
    iPoseProof (ssi_08 with "Htext") as "Hi08".
    iPoseProof (ssi_0a with "Htext") as "Hi0a".
    iPoseProof (ssi_0e with "Htext") as "Hi0e".
    iPoseProof (ssi_10 with "Htext") as "Hi10".
    iPoseProof (ssi_14 with "Htext") as "Hi14".
    iPoseProof (ssi_18 with "Htext") as "Hi18".
    iPoseProof (ssi_1a with "Htext") as "Hi1a".
    iPoseProof (ssi_1e with "Htext") as "Hi1e".
    iPoseProof (ssi_22 with "Htext") as "Hi22".
    iPoseProof (ssi_24 with "Htext") as "Hi24".
    iPoseProof (ssi_28 with "Htext") as "Hi28".
    iPoseProof (ssi_2a with "Htext") as "Hi2a".
    iPoseProof (ssi_2e with "Htext") as "Hi2e".
    iPoseProof (ssi_32 with "Htext") as "Hi32".
    iPoseProof (ssi_36 with "Htext") as "Hi36".
    iPoseProof (ssi_38 with "Htext") as "Hi38".
    iPoseProof (ssi_3c with "Htext") as "Hi3c".
    iPoseProof (ssi_3e with "Htext") as "Hi3e".
    iPoseProof (ssi_40 with "Htext") as "Hi40".
    iPoseProof (ssi_44 with "Htext") as "Hi44".
    iPoseProof (ssi_48 with "Htext") as "Hi48".
    iPoseProof (ssi_4c with "Htext") as "Hi4c".
    iPoseProof (ssi_50 with "Htext") as "Hi50".
    iPoseProof (ssi_52 with "Htext") as "Hi52".
    iPoseProof (ssi_54 with "Htext") as "Hi54".
    iPoseProof (ssi_56 with "Htext") as "Hi56".
    iPoseProof (ssi_58 with "Htext") as "Hi58".
    iPoseProof (ssi_5c with "Htext") as "Hi5c".
    iPoseProof (ssi_60 with "Htext") as "Hi60".
    iPoseProof (ssi_70 with "Htext") as "Hi70".
    iPoseProof (ssi_72 with "Htext") as "Hi72".
    iPoseProof (ssi_74 with "Htext") as "Hi74".
    iPoseProof (ssi_76 with "Htext") as "Hi76".
    (* ---- +0x00: c.addi16sp sp,-48 (frame push) ---- *)
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 61 : mword 6) m av 6 b
              ltac:(lia) (stk_push_48 (m !!! Regidx csp_rs1))
              with "Hcg Hpc Hi00").
    iIntros (CIDs1 Hq1) "Hcg Hframe Hpc".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.sys_sbrk + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /M1 upd_eq; apply stk_push_48).
    (* six slots: 1-3 take ra/s0/s1, 5 holds the two [int] locals, 4 and 6
       are never touched *)
    assert (H46 : (4 <= 6)%nat) by lia.
    iEval (rewrite (stack_own_split sp0 4 6 H46)) in "Hframe".
    iEval (change (6 - 4)%nat with 2%nat) in "Hframe".
    iDestruct "Hframe" as "[Hf14 Hf56]".
    iDestruct (stack_own_4_elim with "Hf14") as (u1 u2 u3 u4) "(Hs1 & Hs2 & Hs3 & Hs4)".
    iDestruct (stack_own_2_elim with "Hf56") as (u5 u6) "[Hs5 Hs6]".
    assert (E5 : pa_stk (pa_stk sp0 4) 1 = pa_stk sp0 5) by (rewrite pa_stk_assoc; reflexivity).
    assert (E6 : pa_stk (pa_stk sp0 4) 2 = pa_stk sp0 6) by (rewrite pa_stk_assoc; reflexivity).
    iEval (rewrite E5) in "Hs5".
    iEval (rewrite E6) in "Hs6".
    (* ---- +0x02 .. +0x06: save ra / s0 / s1 ---- *)
    assert (Hpa1 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa2 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa3 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa1) in "Hs1".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x02))
              (mword_of_int 5 : mword 6) Rra M1 (av - 6)%nat u1 b
              with "Hcg Hpc Hi02 Hs1").
    iIntros (CIDs2 Hq2) "Hcg Hpc Hs1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_sbrk + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    iEval (rewrite -Hpa2) in "Hs2".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x04))
              (mword_of_int 4 : mword 6) Rs0 M1 (av - 6)%nat u2 b
              with "Hcg Hpc Hi04 Hs2").
    iIntros (CIDs3 Hq3) "Hcg Hpc Hs2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_sbrk + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    iEval (rewrite -Hpa3) in "Hs3".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x06))
              (mword_of_int 3 : mword 6) Rs1 M1 (av - 6)%nat u3 b
              with "Hcg Hpc Hi06 Hs3").
    iIntros (CIDs4 Hq4) "Hcg Hpc Hs3".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_sbrk + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    assert (HM1ra : forall CID' : CpuId, rget (CID := CID') M1 Rra = ra0).
    { intros CID'; rgne. rewrite /M1 upd_ne; [reflexivity | reg_neq]. }
    assert (HM1s0 : forall CID' : CpuId, rget (CID := CID') M1 Rs0 = s00).
    { intros CID'; rgne. rewrite /M1 upd_ne; [reflexivity | reg_neq]. }
    assert (HM1s1 : forall CID' : CpuId, rget (CID := CID') M1 Rs1 = s10).
    { intros CID'; rgne. rewrite /M1 upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite Hpa1 HM1ra) in "Hs1".
    iEval (rewrite Hpa2 HM1s0) in "Hs2".
    iEval (rewrite Hpa3 HM1s1) in "Hs3".
    (* ---- +0x08: c.addi4spn s0,sp,48 -- the frame pointer IS sp0 ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x08))
              (Cregidx (mword_of_int 0)) (mword_of_int 12 : mword 8) Rs0
              M1 (av - 6)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CIDs5 Hq5) "Hcg Hpc".
    set (M2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> M1).
    change (<[Regidx Rs0 := regval_into_reg
              (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> M1) with M2.
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x08) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_sbrk + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    assert (HM2s0 : M2 !!! Regidx Rs0 = sp0)
      by (rewrite /M2 upd_eq HM1sp; apply stk_fp_48).
    assert (HM2sp : M2 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /M2 upd_ne; [exact HM1sp | reg_neq]).
    (* the two [int] locals: the two halves of slot 5 *)
    iDestruct (word_pointsto_aligned_p with "Hs5") as %Hal5.
    iDestruct (word_pointsto_split4 with "Hs5") as "[Hs5lo Hs5hi]".
    (* ---- +0x0a: addi a1,s0,-40 -- a1 := &n ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x0a))
              Ra1 Rs0 (mword_of_int 0xfd8 : mword 12) M2 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a").
    iIntros (CIDs6 Hq6) "Hcg Hpc".
    set (M3 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (rget M2 Rs0) (sign_extend' 64 (mword_of_int 0xfd8 : mword 12)))]> M2).
    change (<[Regidx Ra1 := regval_into_reg
              (add_vec (rget M2 Rs0) (sign_extend' 64 (mword_of_int 0xfd8 : mword 12)))]> M2) with M3.
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x0a) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_sbrk + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    assert (HM3a1 : M3 !!! Regidx Ra1 = pa_stk sp0 5).
    { rewrite /M3 upd_eq. rgne. rewrite HM2s0. apply ss_addr_n. }
    (* ---- +0x0e: c.li a0,0 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x0e))
              Ra0 (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64) M3 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi0e").
    iIntros (CIDs7 Hq7) "Hcg Hpc".
    set (M4 := <[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> M3).
    change (<[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> M3) with M4.
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x0e) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_sbrk + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* ---- +0x10: jal ra,argint ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x10))
              Rra (mword_of_int 2096828 : mword 21) M4 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi10").
    iIntros (CIDs8 Hq8) "Hcg Hpc".
    set (M5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x10) : mword 64) 4)]> M4).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x10) : mword 64) 4)]> M4) with M5.
    assert (Hjmp0 : add_vec (mword_of_int (KernelSyms.sys_sbrk + 0x10) : mword 64)
                      (sign_extend' 64 (mword_of_int 2096828 : mword 21)) = mword_of_int KernelSyms.argint)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmp0) in "Hpc".
    assert (HM5a0 : M5 !!! Regidx Ra0 = (mword_of_int 0 : mword 64)).
    { rewrite /M5 upd_ne; [| reg_neq]. rewrite /M4 upd_eq. reflexivity. }
    assert (HM5a1 : M5 !!! Regidx Ra1 = pa_stk sp0 5).
    { rewrite /M5 upd_ne; [| reg_neq]. rewrite /M4 upd_ne; [| reg_neq]. exact HM3a1. }
    assert (HM5sp : M5 !!! Regidx csp_rs1 = pa_stk sp0 6).
    { rewrite /M5 upd_ne; [| reg_neq]. rewrite /M4 upd_ne; [| reg_neq].
      rewrite /M3 upd_ne; [| reg_neq]. exact HM2sp. }
    assert (HM5s0 : M5 !!! Regidx Rs0 = sp0).
    { rewrite /M5 upd_ne; [| reg_neq]. rewrite /M4 upd_ne; [| reg_neq].
      rewrite /M3 upd_ne; [| reg_neq]. exact HM2s0. }
    assert (HM5ra : M5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x10) : mword 64) 4)
      by (rewrite /M5 upd_eq; reflexivity).
    assert (HthrM5 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> M5 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N11 : r <> mword_of_int 11)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /M5 upd_ne; [| congruence]. rewrite /M4 upd_ne; [| congruence].
      rewrite /M3 upd_ne; [| congruence]. rewrite /M2 upd_ne; [| congruence].
      rewrite /M1 upd_ne; [| congruence]. reflexivity. }
    (* argint reads the trapframe pointer AND page out of [proc_priv] *)
    iDestruct (proc_priv_tfp_valid with "Hpriv") as %Hpv.
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfp & Hpage & Hpbacktf)".
    iDestruct (cpu_own_transport CID CIDs8 0%nat eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Argint.wp_argint_sconf (CID := CIDs8) M5 (av - 6)%nat 0%nat eb p 0%nat
              (ud_tfp (pv_upt V)) (pv_tf V) v0 (word_lo u5) (DfracOwn (1/4)) b lks
              ltac:(vm_compute; lia) HM5a0 Harg0 ss_n0 ltac:(lia) Hpv
              with "Hcg Hcpu Htext Hdata Hpc Htfp Hpage [Hs5lo]").
    { iEval (rewrite HM5a1). iExact "Hs5lo". }
    iIntros (CIDA HqA A) "%HcsA Hcg Hcpu Hpc Htfp Hpage Hs5lo".
    iEval (rewrite HM5a1) in "Hs5lo".
    iDestruct ("Hpbacktf" with "Htfp Hpage") as "Hpriv".
    assert (Hpc14 : ret_pc (M5 !!! Regidx Rra) = mword_of_int (KernelSyms.sys_sbrk + 0x14))
      by (rewrite HM5ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    assert (HAsp : A !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite (callee_saved_lookup HcsA csp_rs1 ltac:(vm_compute; reflexivity)); exact HM5sp).
    assert (HAs0 : A !!! Regidx Rs0 = sp0)
      by (rewrite (callee_saved_lookup HcsA (mword_of_int 8) ltac:(vm_compute; reflexivity)); exact HM5s0).
    assert (HthrA : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> A !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      rewrite (callee_saved_lookup HcsA r Hr). apply HthrM5; assumption. }
    (* ---- +0x14: addi a1,s0,-36 -- a1 := &t ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x14))
              Ra1 Rs0 (mword_of_int 0xfdc : mword 12) A (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14").
    iIntros (CIDs9 Hq9) "Hcg Hpc".
    set (A1 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (rget A Rs0) (sign_extend' 64 (mword_of_int 0xfdc : mword 12)))]> A).
    change (<[Regidx Ra1 := regval_into_reg
              (add_vec (rget A Rs0) (sign_extend' 64 (mword_of_int 0xfdc : mword 12)))]> A) with A1.
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x14) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_sbrk + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    assert (HA1a1 : A1 !!! Regidx Ra1 = pa_add (pa_stk sp0 5) 4).
    { rewrite /A1 upd_eq. rgne. rewrite HAs0. apply ss_addr_t. }
    (* ---- +0x18: c.li a0,1 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x18))
              Ra0 (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64) A1 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi18").
    iIntros (CIDs10 Hq10) "Hcg Hpc".
    set (A2 := <[Regidx Ra0 := regval_into_reg (mword_of_int 1 : mword 64)]> A1).
    change (<[Regidx Ra0 := regval_into_reg (mword_of_int 1 : mword 64)]> A1) with A2.
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x18) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_sbrk + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* ---- +0x1a: jal ra,argint ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x1a))
              Rra (mword_of_int 2096818 : mword 21) A2 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1a").
    iIntros (CIDs11 Hq11) "Hcg Hpc".
    set (A3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x1a) : mword 64) 4)]> A2).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x1a) : mword 64) 4)]> A2) with A3.
    assert (Hjmp1 : add_vec (mword_of_int (KernelSyms.sys_sbrk + 0x1a) : mword 64)
                      (sign_extend' 64 (mword_of_int 2096818 : mword 21)) = mword_of_int KernelSyms.argint)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmp1) in "Hpc".
    assert (HA3a0 : A3 !!! Regidx Ra0 = (mword_of_int 1 : mword 64)).
    { rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_eq. reflexivity. }
    assert (HA3a1 : A3 !!! Regidx Ra1 = pa_add (pa_stk sp0 5) 4).
    { rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq]. exact HA1a1. }
    assert (HA3sp : A3 !!! Regidx csp_rs1 = pa_stk sp0 6).
    { rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
      rewrite /A1 upd_ne; [| reg_neq]. exact HAsp. }
    assert (HA3s0 : A3 !!! Regidx Rs0 = sp0).
    { rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
      rewrite /A1 upd_ne; [| reg_neq]. exact HAs0. }
    assert (HA3ra : A3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x1a) : mword 64) 4)
      by (rewrite /A3 upd_eq; reflexivity).
    assert (HthrA3 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> A3 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N11 : r <> mword_of_int 11)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /A3 upd_ne; [| congruence]. rewrite /A2 upd_ne; [| congruence].
      rewrite /A1 upd_ne; [| congruence]. apply HthrA; assumption. }
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfp & Hpage & Hpbacktf)".
    iDestruct (cpu_own_transport CIDA CIDs11 0%nat eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Argint.wp_argint_sconf (CID := CIDs11) A3 (av - 6)%nat 0%nat eb p 1%nat
              (ud_tfp (pv_upt V)) (pv_tf V) v1 (word_hi u5) (DfracOwn (1/4)) b lks
              ltac:(vm_compute; lia) HA3a0 Harg1 ss_n0 ltac:(lia) Hpv
              with "Hcg Hcpu Htext Hdata Hpc Htfp Hpage [Hs5hi]").
    { iEval (rewrite HA3a1). iExact "Hs5hi". }
    iIntros (CIDB HqB B) "%HcsB Hcg Hcpu Hpc Htfp Hpage Hs5hi".
    iEval (rewrite HA3a1) in "Hs5hi".
    iDestruct ("Hpbacktf" with "Htfp Hpage") as "Hpriv".
    assert (Hpc1e : ret_pc (A3 !!! Regidx Rra) = mword_of_int (KernelSyms.sys_sbrk + 0x1e))
      by (rewrite HA3ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1e) in "Hpc".
    assert (HBsp : B !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite (callee_saved_lookup HcsB csp_rs1 ltac:(vm_compute; reflexivity)); exact HA3sp).
    assert (HBs0 : B !!! Regidx Rs0 = sp0)
      by (rewrite (callee_saved_lookup HcsB (mword_of_int 8) ltac:(vm_compute; reflexivity)); exact HA3s0).
    assert (HthrB : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> B !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      rewrite (callee_saved_lookup HcsB r Hr). apply HthrA3; assumption. }
    (* ---- +0x1e: jal ra,myproc ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x1e))
              Rra (mword_of_int 2092908 : mword 21) B (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1e").
    iIntros (CIDs12 Hq12) "Hcg Hpc".
    set (B1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x1e) : mword 64) 4)]> B).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x1e) : mword 64) 4)]> B) with B1.
    assert (Hjmpmp : add_vec (mword_of_int (KernelSyms.sys_sbrk + 0x1e) : mword 64)
                       (sign_extend' 64 (mword_of_int 2092908 : mword 21)) = mword_of_int KernelSyms.myproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmpmp) in "Hpc".
    assert (HB1sp : B1 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /B1 upd_ne; [exact HBsp | reg_neq]).
    assert (HB1s0 : B1 !!! Regidx Rs0 = sp0)
      by (rewrite /B1 upd_ne; [exact HBs0 | reg_neq]).
    assert (HB1ra : B1 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x1e) : mword 64) 4)
      by (rewrite /B1 upd_eq; reflexivity).
    assert (HthrB1 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> B1 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /B1 upd_ne; [| congruence]. apply HthrB; assumption. }
    iDestruct (cpu_own_transport CIDB CIDs12 0%nat eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Myproc.wp_myproc_sconf (CID := CIDs12) B1 (av - 6)%nat 0%nat eb p b lks
              ss_n0 ltac:(lia)
              with "Hcg Hcpu Htext Hpc").
    iIntros (CIDD HqD ms1 D) "%Hms1 Hcg Hcpu Hpc %HcsD".
    destruct HcsD as [HcsD HDa0].
    assert (Hpc22 : ret_pc (B1 !!! Regidx Rra) = mword_of_int (KernelSyms.sys_sbrk + 0x22))
      by (rewrite HB1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc22) in "Hpc".
    assert (HDsp : D !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite (callee_saved_lookup HcsD csp_rs1 ltac:(vm_compute; reflexivity)); exact HB1sp).
    assert (HDs0 : D !!! Regidx Rs0 = sp0)
      by (rewrite (callee_saved_lookup HcsD (mword_of_int 8) ltac:(vm_compute; reflexivity)); exact HB1s0).
    assert (HthrD : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> D !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      rewrite (callee_saved_lookup HcsD r Hr). apply HthrB1; assumption. }
    (* the two invariant facts, and the size cell *)
    iDestruct (proc_priv_sz_maxsz with "Hpriv") as %Hszmax.
    iDestruct (proc_priv_um_below with "Hpriv") as %Hbel.
    assert (Hszmaxz : (bv_unsigned (pv_sz V) <= 274877898752)%Z).
    { rewrite <- uint_unsigned. rewrite <- uvm_maxsz_val. exact Hszmax. }
    iDestruct (proc_priv_addrspace with "Hpriv") as "(Hszc & Hptc & Hpt & Hpback)".
    (* ---- +0x22: c.ld s1,72(a0) -- s1 := p->sz, the value sbrk returns -- *)
    assert (Hszaddr : forall CID' : CpuId,
              add_vec (rget (CID := CID') D Ra0) (sign_extend' 64 (mword_of_int 72 : mword 12)) = p_sz p).
    { intros CID'; rgne. rewrite HDa0; reflexivity. }
    iEval (rewrite -(Hszaddr CIDD)) in "Hszc".
    iApply (wp_cld_s_sconf (CID := CIDD) (mword_of_int (KernelSyms.sys_sbrk + 0x22)) Rs1 Ra0
              (mword_of_int 72 : mword 12) D (av - 6)%nat (pv_sz V) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 Hszc").
    iIntros (CIDs13 Hq13) "Hcg Hpc Hszc".
    iEval (rewrite (Hszaddr CIDD)) in "Hszc".
    set (D1 := <[Regidx Rs1 := regval_into_reg (pv_sz V)]> D).
    change (<[Regidx Rs1 := regval_into_reg (pv_sz V)]> D) with D1.
    assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x22) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_sbrk + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    assert (HD1s1 : D1 !!! Regidx Rs1 = pv_sz V) by (rewrite /D1 upd_eq; reflexivity).
    assert (HD1s0 : D1 !!! Regidx Rs0 = sp0)
      by (rewrite /D1 upd_ne; [exact HDs0 | reg_neq]).
    assert (HD1sp : D1 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /D1 upd_ne; [exact HDsp | reg_neq]).
    assert (HD1a0 : D1 !!! Regidx Ra0 = p)
      by (rewrite /D1 upd_ne; [exact HDa0 | reg_neq]).
    assert (HthrD1 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> D1 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      rewrite /D1 upd_ne; [| congruence]. apply HthrD; assumption. }
    (* ---- +0x24: lw a4,-36(s0) -- a4 := t ---- *)
    assert (Htaddr : forall CID' : CpuId,
              add_vec (rget (CID := CID') D1 Rs0) (sign_extend' 64 (mword_of_int 0xfdc : mword 12))
              = pa_add (pa_stk sp0 5) 4).
    { intros CID'; rgne. rewrite HD1s0; apply ss_addr_t. }
    iEval (rewrite -(Htaddr CIDs13)) in "Hs5hi".
    iApply (wp_lw_s_sconf (CID := CIDs13) (mword_of_int (KernelSyms.sys_sbrk + 0x24)) Ra4 Rs0
              (mword_of_int 0xfdc : mword 12) D1 (av - 6)%nat (trunc32 v1) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24 Hs5hi").
    iIntros (CIDs14 Hq14) "Hcg Hpc Hs5hi".
    iEval (rewrite (Htaddr CIDs13)) in "Hs5hi".
    set (D2 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 (trunc32 v1))]> D1).
    change (<[Regidx Ra4 := regval_into_reg (sign_extend' 64 (trunc32 v1))]> D1) with D2.
    assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x24) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_sbrk + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    (* ---- +0x28: c.li a5,1 -- SBRK_EAGER ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x28))
              Ra5 (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64) D2 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi28").
    iIntros (CIDs15 Hq15) "Hcg Hpc".
    set (D3 := <[Regidx Ra5 := regval_into_reg (mword_of_int 1 : mword 64)]> D2).
    change (<[Regidx Ra5 := regval_into_reg (mword_of_int 1 : mword 64)]> D2) with D3.
    assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x28) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_sbrk + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2a) in "Hpc".
    assert (HD3a4 : D3 !!! Regidx Ra4 = sbrk_arg v1).
    { rewrite /D3 upd_ne; [| reg_neq]. rewrite /D2 upd_eq. reflexivity. }
    assert (HD3a5 : D3 !!! Regidx Ra5 = (mword_of_int 1 : mword 64))
      by (rewrite /D3 upd_eq; reflexivity).
    assert (HD3s1 : D3 !!! Regidx Rs1 = pv_sz V).
    { rewrite /D3 upd_ne; [| reg_neq]. rewrite /D2 upd_ne; [| reg_neq]. exact HD1s1. }
    assert (HD3s0 : D3 !!! Regidx Rs0 = sp0).
    { rewrite /D3 upd_ne; [| reg_neq]. rewrite /D2 upd_ne; [| reg_neq]. exact HD1s0. }
    assert (HD3sp : D3 !!! Regidx csp_rs1 = pa_stk sp0 6).
    { rewrite /D3 upd_ne; [| reg_neq]. rewrite /D2 upd_ne; [| reg_neq]. exact HD1sp. }
    assert (HD3a0 : D3 !!! Regidx Ra0 = p).
    { rewrite /D3 upd_ne; [| reg_neq]. rewrite /D2 upd_ne; [| reg_neq]. exact HD1a0. }
    assert (HthrD3 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> D3 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      assert (N14 : r <> mword_of_int 14)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> mword_of_int 15)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /D3 upd_ne; [| congruence]. rewrite /D2 upd_ne; [| congruence].
      apply HthrD1; assumption. }

    (* ================================================================= *)
    (*  THE EXIT, shared by all five arms.                                *)
    (* ================================================================= *)
    (* The shared exit quantifies the HART it is entered on -- each of the five
       arms reaches +0x64 at a different point in the crossing chain -- and
       carries the chain fact back to [CID] so [Hcont] can be discharged. *)
    iAssert (∀ (CIDx : CpuId) (Mf : regfile) (P' : uptd) (szv' rv : mword 64),
        ⌜b = false \/ p = zero_reg -> (CIDx : CPU) = (CID : CPU)⌝ -∗
        ⌜Mf !!! Regidx csp_rs1 = pa_stk sp0 6⌝ -∗
        ⌜Mf !!! Regidx Rs1 = rv⌝ -∗
        ⌜forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
            r <> Rs0 -> r <> Rs1 -> Mf !!! Regidx r = m !!! Regidx r⌝ -∗
        ⌜sys_sbrk_ok V v0 v1 P' szv' rv⌝ -∗
        sie_cap_gpr (CID := CIDx) Mf (av - 6)%nat b p -∗
        cpu_own (CID := CIDx) 0%nat eb p b lks -∗
        pc_is (mword_of_int (KernelSyms.sys_sbrk + 0x64) : mword 64) -∗
        proc_priv γf p pid (upd_sz (upd_upt V P') szv') -∗
        (∃ w5 : mword 64, word_pointsto (pa_stk sp0 5) (DfracOwn 1) w5) -∗
        WP (Loop : expr riscv_lang))%I
      with "[Hcont Hs1 Hs2 Hs3 Hs4 Hs6]" as "EXIT".
    { iIntros (CIDx Mf P' szv' rv) "%Hsx %Hfsp %Hfs1 %Hfthr %Hok Hcg Hcpu Hpc Hpriv Hw5".
      iDestruct "Hw5" as (w5) "Hs5".
      iApply (ss_tail (CID0 := CIDx) m Mf av b p rv sp0 ra0 s00 s10 u4 w5 u6
                ltac:(lia) eq_refl eq_refl eq_refl eq_refl Hfsp Hfs1 Hfthr
                with "Hcg Htext Hpc Hs1 Hs2 Hs3 Hs4 Hs5 Hs6").
      iIntros (CIDy Hqy mf) "[%Hcsf %Hmfa0] Hcg Hpc".
      iDestruct (cpu_own_transport CIDx CIDy 0%nat eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf P' szv' with "[%] [%] Hcg Hcpu Hpc Hpriv").
      { exact Hcsf. }
      { rewrite Hmfa0. exact Hok. } }
    (* ================================================================= *)
    (*  +0x2a  beq a4,a5 : t == SBRK_EAGER ?                              *)
    (* ================================================================= *)
    destruct (eq_vec (D3 !!! Regidx Ra4) (D3 !!! Regidx Ra5)) eqn:Hbeq.
    { (* ---- EAGER because t == SBRK_EAGER ---- *)
      assert (Heager : sbrk_eager v1).
      { unfold sbrk_eager, sbrk_arg. rewrite HD3a4 HD3a5 in Hbeq.
        by apply eq_vec_true_iff in Hbeq. }
      assert (Htgt58 : add_vec (mword_of_int (KernelSyms.sys_sbrk + 0x2a) : mword 64)
                         (sign_extend' 64 (mword_of_int 46 : mword 13))
                       = mword_of_int (KernelSyms.sys_sbrk + 0x58))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x2a))
                (mword_of_int 46 : mword 13) Ra5 Ra4 D3 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgne; rgne; exact Hbeq) ltac:(rewrite Htgt58; vm_compute; reflexivity)
                with "Hcg Hpc Hi2a").
      iIntros (CIDs16 Hq16). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt58) in "Hpc".
      iDestruct ("Hpback" $! (pv_upt V) (pv_sz V) with "[%] [%] [%] [%] Hszc Hptc Hpt")
        as "Hpriv"; [reflexivity | reflexivity | exact Hszmax | exact Hbel |].
      iDestruct (cpu_own_transport CIDD CIDs16 0%nat eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iApply (ss_eager (CID0 := CIDs16) γa γf m D3 av eb p pid V sp0 (trunc32 v0) b lks
                ltac:(lia) HD3sp HD3s0 HD3s1 HthrD3
                with "Hcg Hcpu Htext Hpc Hpriv Henv Hs5lo").
      iIntros (CIDe Hqe Mf P' szv' rv) "%Hfsp %Hfs1 %Hfthr %Hres Hcg Hcpu Hpc Hpriv Hs5lo".
      iApply ("EXIT" $! CIDe Mf P' szv' rv with "[%] [%] [%] [%] [%] Hcg Hcpu Hpc Hpriv [Hs5lo Hs5hi]").
      - wp_next_chain.
      - exact Hfsp.
      - exact Hfs1.
      - exact Hfthr.
      - destruct Hres as [(Hrv & Hgok) | (Hrv & Hp & Hs)].
        + right. split; [exact Hrv |]. left. split; [left; exact Heager | exact Hgok].
        + left. split; [exact Hrv | split; [exact Hp | exact Hs]].
      - iExists (word_of_words (trunc32 v0) (trunc32 v1)).
        iApply (word_pointsto_join4 _ _ _ _ Hal5 with "Hs5lo Hs5hi"). }
    (* ---- t <> SBRK_EAGER: look at the sign of n ---- *)
    assert (Hnoteager : ~ sbrk_eager v1).
    { unfold sbrk_eager. intro He.
      rewrite HD3a4 HD3a5 He in Hbeq.
      assert (Ht : eq_vec (mword_of_int 1 : mword 64) (mword_of_int 1 : mword 64) = true)
        by (apply eq_vec_true_iff; reflexivity).
      rewrite Ht in Hbeq. discriminate. }
    iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x2a))
              (mword_of_int 46 : mword 13) Ra5 Ra4 D3 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rgne; rgne; exact Hbeq)
              with "Hcg Hpc Hi2a").
    iIntros (CIDs17 Hq17) "Hcg Hpc".
    assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x2a) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_sbrk + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    (* ---- +0x2e: lw a5,-40(s0) -- a5 := n ---- *)
    assert (Hnaddr : forall CID' : CpuId,
              add_vec (rget (CID := CID') D3 Rs0) (sign_extend' 64 (mword_of_int 0xfd8 : mword 12))
              = pa_stk sp0 5).
    { intros CID'; rgne. rewrite HD3s0; apply ss_addr_n. }
    iEval (rewrite -(Hnaddr CIDs17)) in "Hs5lo".
    iApply (wp_lw_s_sconf (CID := CIDs17) (mword_of_int (KernelSyms.sys_sbrk + 0x2e)) Ra5 Rs0
              (mword_of_int 0xfd8 : mword 12) D3 (av - 6)%nat (trunc32 v0) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2e Hs5lo").
    iIntros (CIDs18 Hq18) "Hcg Hpc Hs5lo".
    iEval (rewrite (Hnaddr CIDs17)) in "Hs5lo".
    set (D4 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (trunc32 v0))]> D3).
    change (<[Regidx Ra5 := regval_into_reg (sign_extend' 64 (trunc32 v0))]> D3) with D4.
    assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x2e) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_sbrk + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    assert (HD4a5 : D4 !!! Regidx Ra5 = sbrk_arg v0) by (rewrite /D4 upd_eq; reflexivity).
    assert (HD4s1 : D4 !!! Regidx Rs1 = pv_sz V)
      by (rewrite /D4 upd_ne; [exact HD3s1 | reg_neq]).
    assert (HD4s0 : D4 !!! Regidx Rs0 = sp0)
      by (rewrite /D4 upd_ne; [exact HD3s0 | reg_neq]).
    assert (HD4sp : D4 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /D4 upd_ne; [exact HD3sp | reg_neq]).
    assert (HthrD4 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> D4 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      assert (N15 : r <> mword_of_int 15)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /D4 upd_ne; [| congruence]. apply HthrD3; assumption. }
    (* ---- +0x32: blt a5,x0 -- is n negative? ---- *)
    destruct (zopz0zI_s (D4 !!! Regidx Ra5) (zero_reg : mword 64)) eqn:Hbltz.
    { (* ---- EAGER because n < 0 ---- *)
      assert (Hnneg : (sint (sbrk_arg v0) < 0)%Z).
      { rewrite HD4a5 in Hbltz. unfold zopz0zI_s in Hbltz.
        assert (Hz0 : sint (zero_reg : mword 64) = 0%Z) by reflexivity.
        rewrite Hz0 in Hbltz. by apply Z.ltb_lt in Hbltz. }
      assert (Htgt58 : add_vec (mword_of_int (KernelSyms.sys_sbrk + 0x32) : mword 64)
                         (sign_extend' 64 (mword_of_int 38 : mword 13))
                       = mword_of_int (KernelSyms.sys_sbrk + 0x58))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_blt_x0_taken_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x32))
                (mword_of_int 38 : mword 13) Ra5 D4 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rgne; exact Hbltz)
                ltac:(rewrite Htgt58; vm_compute; reflexivity)
                with "Hcg Hpc Hi32").
      iIntros (CIDs19 Hq19). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt58) in "Hpc".
      iDestruct ("Hpback" $! (pv_upt V) (pv_sz V) with "[%] [%] [%] [%] Hszc Hptc Hpt")
        as "Hpriv"; [reflexivity | reflexivity | exact Hszmax | exact Hbel |].
      iDestruct (cpu_own_transport CIDD CIDs19 0%nat eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iApply (ss_eager (CID0 := CIDs19) γa γf m D4 av eb p pid V sp0 (trunc32 v0) b lks
                ltac:(lia) HD4sp HD4s0 HD4s1 HthrD4
                with "Hcg Hcpu Htext Hpc Hpriv Henv Hs5lo").
      iIntros (CIDe Hqe Mf P' szv' rv) "%Hfsp %Hfs1 %Hfthr %Hres Hcg Hcpu Hpc Hpriv Hs5lo".
      iApply ("EXIT" $! CIDe Mf P' szv' rv with "[%] [%] [%] [%] [%] Hcg Hcpu Hpc Hpriv [Hs5lo Hs5hi]").
      - wp_next_chain.
      - exact Hfsp.
      - exact Hfs1.
      - exact Hfthr.
      - destruct Hres as [(Hrv & Hgok) | (Hrv & Hp & Hs)].
        + right. split; [exact Hrv |]. left. split; [right; exact Hnneg | exact Hgok].
        + left. split; [exact Hrv | split; [exact Hp | exact Hs]].
      - iExists (word_of_words (trunc32 v0) (trunc32 v1)).
        iApply (word_pointsto_join4 _ _ _ _ Hal5 with "Hs5lo Hs5hi"). }
    (* ================================================================= *)
    (*  THE LAZY PATH: n >= 0 and t <> SBRK_EAGER.                        *)
    (* ================================================================= *)
    assert (Hnpos : (0 <= sint (sbrk_arg v0))%Z).
    { rewrite HD4a5 in Hbltz. unfold zopz0zI_s in Hbltz.
      assert (Hz0 : sint (zero_reg : mword 64) = 0%Z) by reflexivity.
      rewrite Hz0 in Hbltz. by apply Z.ltb_ge in Hbltz. }
    pose proof (sint64_range (sbrk_arg v0)) as Hnb.
    pose proof (proj1 (bv_unsigned_in_range _ (pv_sz V))) as Hsz0.
    assert (Hsum : bv_unsigned (add_vec (pv_sz V) (sbrk_arg v0))
                   = (bv_unsigned (pv_sz V) + sint (sbrk_arg v0))%Z).
    { apply add_vec_sint_unsigned; [exact Hnpos |].
      apply ss_z_nowrap; [exact Hsz0 | exact Hszmaxz | lia]. }
    iApply (wp_blt_x0_fall_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x32))
              (mword_of_int 38 : mword 13) Ra5 D4 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rgne; exact Hbltz)
              with "Hcg Hpc Hi32").
    iIntros (CIDs20 Hq20) "Hcg Hpc".
    assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x32) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_sbrk + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp36) in "Hpc".
    (* ---- +0x36: c.add a5,a5,s1 -- a5 := addr + n ---- *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x36))
              Ra5 Rs1 D4 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi36").
    iIntros (CIDs21 Hq21) "Hcg Hpc".
    set (L1 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (rget D4 Ra5) (rget D4 Rs1))]> D4).
    change (<[Regidx Ra5 := regval_into_reg
              (add_vec (rget D4 Ra5) (rget D4 Rs1))]> D4) with L1.
    assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x36) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_sbrk + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp38) in "Hpc".
    assert (HL1a5 : L1 !!! Regidx Ra5 = add_vec (pv_sz V) (sbrk_arg v0)).
    { rewrite /L1 upd_eq. rgne. rgne. rewrite HD4a5 HD4s1. apply add_vec64_comm. }
    (* ---- +0x38 .. +0x3e: a4 := TRAPFRAME ---- *)
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x38))
              Ra4 (mword_of_int 8192 : mword 20) (mword_of_int 33554432 : mword 64)
              L1 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi38").
    iIntros (CIDs22 Hq22) "Hcg Hpc".
    set (L2 := <[Regidx Ra4 := regval_into_reg (mword_of_int 33554432 : mword 64)]> L1).
    change (<[Regidx Ra4 := regval_into_reg (mword_of_int 33554432 : mword 64)]> L1) with L2.
    assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x38) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_sbrk + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3c) in "Hpc".
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x3c))
              Ra4 (mword_of_int 63 : mword 6) L2 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3c").
    iIntros (CIDs23 Hq23) "Hcg Hpc".
    set (L3 := <[Regidx Ra4 := regval_into_reg
          (add_vec (rget L2 Ra4) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> L2).
    change (<[Regidx Ra4 := regval_into_reg
          (add_vec (rget L2 Ra4) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> L2) with L3.
    assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x3c) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_sbrk + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3e) in "Hpc".
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x3e))
              (Regidx Ra4) Ra4 (mword_of_int 13 : mword 6) L3 (av - 6)%nat b
              eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3e").
    iIntros (CIDs24 Hq24) "Hcg Hpc".
    set (L4 := <[Regidx Ra4 := regval_into_reg
          (shift_bits_left (rget L3 Ra4)
             (subrange_vec_dec (mword_of_int 13 : mword 6) (Z.sub log2_xlen 1) 0))]> L3).
    change (<[Regidx Ra4 := regval_into_reg
          (shift_bits_left (rget L3 Ra4)
             (subrange_vec_dec (mword_of_int 13 : mword 6) (Z.sub log2_xlen 1) 0))]> L3) with L4.
    assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x3e) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_sbrk + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp40) in "Hpc".
    assert (HL4a4 : L4 !!! Regidx Ra4 = (mword_of_int 274877898752 : mword 64)).
    { rewrite /L4 upd_eq. rgne. rewrite /L3 upd_eq. rgne. rewrite /L2 upd_eq.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HL4a5 : L4 !!! Regidx Ra5 = add_vec (pv_sz V) (sbrk_arg v0)).
    { rewrite /L4 upd_ne; [| reg_neq]. rewrite /L3 upd_ne; [| reg_neq].
      rewrite /L2 upd_ne; [| reg_neq]. exact HL1a5. }
    assert (HL4s1 : L4 !!! Regidx Rs1 = pv_sz V).
    { rewrite /L4 upd_ne; [| reg_neq]. rewrite /L3 upd_ne; [| reg_neq].
      rewrite /L2 upd_ne; [| reg_neq]. rewrite /L1 upd_ne; [| reg_neq]. exact HD4s1. }
    assert (HL4s0 : L4 !!! Regidx Rs0 = sp0).
    { rewrite /L4 upd_ne; [| reg_neq]. rewrite /L3 upd_ne; [| reg_neq].
      rewrite /L2 upd_ne; [| reg_neq]. rewrite /L1 upd_ne; [| reg_neq]. exact HD4s0. }
    assert (HL4sp : L4 !!! Regidx csp_rs1 = pa_stk sp0 6).
    { rewrite /L4 upd_ne; [| reg_neq]. rewrite /L3 upd_ne; [| reg_neq].
      rewrite /L2 upd_ne; [| reg_neq]. rewrite /L1 upd_ne; [| reg_neq]. exact HD4sp. }
    assert (HthrL4 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> L4 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      assert (N14 : r <> mword_of_int 14)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> mword_of_int 15)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /L4 upd_ne; [| congruence]. rewrite /L3 upd_ne; [| congruence].
      rewrite /L2 upd_ne; [| congruence]. rewrite /L1 upd_ne; [| congruence].
      apply HthrD4; assumption. }
    (* ---- +0x40: bltu a4,a5 -- addr + n > TRAPFRAME ? ---- *)
    destruct (zopz0zI_u (L4 !!! Regidx Ra4) (L4 !!! Regidx Ra5)) eqn:Hbltu1.
    { (* over TRAPFRAME: [s1 := -1] and out *)
      assert (Htgt74 : add_vec (mword_of_int (KernelSyms.sys_sbrk + 0x40) : mword 64)
                         (sign_extend' 64 (mword_of_int 52 : mword 13))
                       = mword_of_int (KernelSyms.sys_sbrk + 0x74))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_bltu_taken_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x40))
                (mword_of_int 52 : mword 13) Ra5 Ra4 L4 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgne; rgne; exact Hbltu1) ltac:(rewrite Htgt74; vm_compute; reflexivity)
                with "Hcg Hpc Hi40").
      iIntros (CIDs25 Hq25). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt74) in "Hpc".
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x74))
                Rs1 (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64) L4 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi74").
      iIntros (CIDs26 Hq26) "Hcg Hpc".
      set (Y1 := <[Regidx Rs1 := regval_into_reg (mword_of_int (-1) : mword 64)]> L4).
      change (<[Regidx Rs1 := regval_into_reg (mword_of_int (-1) : mword 64)]> L4) with Y1.
      assert (Hpp76 : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x74) : mword 64) 2
                      = mword_of_int (KernelSyms.sys_sbrk + 0x76)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp76) in "Hpc".
      assert (Htgt64 : add_vec (mword_of_int (KernelSyms.sys_sbrk + 0x76) : mword 64)
                         (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2039 : mword 11) ('b"0"))))
                       = mword_of_int (KernelSyms.sys_sbrk + 0x64))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x76))
                (sign_extend' 21 (concat_vec (mword_of_int 2039 : mword 11) ('b"0"))) Y1 (av - 6)%nat b
                ltac:(rewrite Htgt64; vm_compute; reflexivity)
                with "Hcg Hpc Hi76").
      iIntros (CIDs27 Hq27). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt64) in "Hpc".
      iDestruct ("Hpback" $! (pv_upt V) (pv_sz V) with "[%] [%] [%] [%] Hszc Hptc Hpt")
        as "Hpriv"; [reflexivity | reflexivity | exact Hszmax | exact Hbel |].
      iDestruct (cpu_own_transport CIDD CIDs27 0%nat eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iApply ("EXIT" $! CIDs27 Y1 (pv_upt V) (pv_sz V) (mword_of_int (-1) : mword 64)
                with "[%] [%] [%] [%] [%] Hcg Hcpu Hpc Hpriv [Hs5lo Hs5hi]").
      - wp_next_chain.
      - rewrite /Y1 upd_ne; [exact HL4sp | reg_neq].
      - rewrite /Y1 upd_eq. reflexivity.
      - intros r Hr Ncsp N8 N9.
        rewrite /Y1 upd_ne; [| congruence]. apply HthrL4; assumption.
      - left. split; [reflexivity | split; reflexivity].
      - iExists (word_of_words (trunc32 v0) (trunc32 v1)).
        iApply (word_pointsto_join4 _ _ _ _ Hal5 with "Hs5lo Hs5hi"). }
    (* ---- it fits ---- *)
    assert (Hfits : (bv_unsigned (add_vec (pv_sz V) (sbrk_arg v0)) <= 274877898752)%Z).
    { rewrite HL4a4 HL4a5 in Hbltu1. unfold zopz0zI_u in Hbltu1.
      apply Z.ltb_ge in Hbltu1. rewrite !uint_unsigned in Hbltu1.
      assert (Hlit : bv_unsigned (mword_of_int 274877898752 : mword 64) = 274877898752%Z)
        by (vm_compute; reflexivity).
      rewrite Hlit in Hbltu1. exact Hbltu1. }
    iApply (wp_bltu_fall_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x40))
              (mword_of_int 52 : mword 13) Ra5 Ra4 L4 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rgne; rgne; exact Hbltu1)
              with "Hcg Hpc Hi40").
    iIntros (CIDs28 Hq28) "Hcg Hpc".
    assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x40) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_sbrk + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp44) in "Hpc".
    (* ---- +0x44: bltu a5,s1 -- the WRAP test, and it is DEAD ---- *)
    assert (Hnowrap : zopz0zI_u (L4 !!! Regidx Ra5) (L4 !!! Regidx Rs1) = false).
    { rewrite HL4a5 HL4s1. unfold zopz0zI_u. apply Z.ltb_ge.
      rewrite !uint_unsigned Hsum. lia. }
    iApply (wp_bltu_fall_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x44))
              (mword_of_int 48 : mword 13) Rs1 Ra5 L4 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rgne; rgne; exact Hnowrap)
              with "Hcg Hpc Hi44").
    iIntros (CIDs29 Hq29) "Hcg Hpc".
    assert (Hpp48 : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x44) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_sbrk + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp48) in "Hpc".
    (* ---- +0x48: the SECOND myproc() ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x48))
              Rra (mword_of_int 2092866 : mword 21) L4 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi48").
    iIntros (CIDs30 Hq30) "Hcg Hpc".
    set (L5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x48) : mword 64) 4)]> L4).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x48) : mword 64) 4)]> L4) with L5.
    assert (Hjmpmp2 : add_vec (mword_of_int (KernelSyms.sys_sbrk + 0x48) : mword 64)
                        (sign_extend' 64 (mword_of_int 2092866 : mword 21)) = mword_of_int KernelSyms.myproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmpmp2) in "Hpc".
    assert (HL5sp : L5 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /L5 upd_ne; [exact HL4sp | reg_neq]).
    assert (HL5s0 : L5 !!! Regidx Rs0 = sp0)
      by (rewrite /L5 upd_ne; [exact HL4s0 | reg_neq]).
    assert (HL5s1 : L5 !!! Regidx Rs1 = pv_sz V)
      by (rewrite /L5 upd_ne; [exact HL4s1 | reg_neq]).
    assert (HL5ra : L5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x48) : mword 64) 4)
      by (rewrite /L5 upd_eq; reflexivity).
    assert (HthrL5 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> L5 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /L5 upd_ne; [| congruence]. apply HthrL4; assumption. }
    iDestruct (cpu_own_transport CIDD CIDs30 0%nat eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Myproc.wp_myproc_sconf (CID := CIDs30) L5 (av - 6)%nat 0%nat eb p b lks
              ss_n0 ltac:(lia)
              with "Hcg Hcpu Htext Hpc").
    iIntros (CIDE HqE ms2 E) "%Hms2 Hcg Hcpu Hpc %HcsE".
    destruct HcsE as [HcsE HEa0].
    assert (Hpc4c : ret_pc (L5 !!! Regidx Rra) = mword_of_int (KernelSyms.sys_sbrk + 0x4c))
      by (rewrite HL5ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc4c) in "Hpc".
    assert (HEsp : E !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite (callee_saved_lookup HcsE csp_rs1 ltac:(vm_compute; reflexivity)); exact HL5sp).
    assert (HEs0 : E !!! Regidx Rs0 = sp0)
      by (rewrite (callee_saved_lookup HcsE (mword_of_int 8) ltac:(vm_compute; reflexivity)); exact HL5s0).
    assert (HEs1 : E !!! Regidx Rs1 = pv_sz V)
      by (rewrite (callee_saved_lookup HcsE (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HL5s1).
    assert (HthrE : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> E !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      rewrite (callee_saved_lookup HcsE r Hr). apply HthrL5; assumption. }
    (* ---- +0x4c: lw a4,-40(s0) -- a4 := n ---- *)
    assert (Hnaddr2 : forall CID' : CpuId,
              add_vec (rget (CID := CID') E Rs0) (sign_extend' 64 (mword_of_int 0xfd8 : mword 12))
              = pa_stk sp0 5).
    { intros CID'; rgne. rewrite HEs0; apply ss_addr_n. }
    iEval (rewrite -(Hnaddr2 CIDE)) in "Hs5lo".
    iApply (wp_lw_s_sconf (CID := CIDE) (mword_of_int (KernelSyms.sys_sbrk + 0x4c)) Ra4 Rs0
              (mword_of_int 0xfd8 : mword 12) E (av - 6)%nat (trunc32 v0) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4c Hs5lo").
    iIntros (CIDs31 Hq31) "Hcg Hpc Hs5lo".
    iEval (rewrite (Hnaddr2 CIDE)) in "Hs5lo".
    set (E1 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 (trunc32 v0))]> E).
    change (<[Regidx Ra4 := regval_into_reg (sign_extend' 64 (trunc32 v0))]> E) with E1.
    assert (Hpp50 : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x4c) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_sbrk + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp50) in "Hpc".
    assert (HE1a4 : E1 !!! Regidx Ra4 = sbrk_arg v0) by (rewrite /E1 upd_eq; reflexivity).
    assert (HE1a0 : E1 !!! Regidx Ra0 = p)
      by (rewrite /E1 upd_ne; [exact HEa0 | reg_neq]).
    assert (HE1sp : E1 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /E1 upd_ne; [exact HEsp | reg_neq]).
    assert (HE1s1 : E1 !!! Regidx Rs1 = pv_sz V)
      by (rewrite /E1 upd_ne; [exact HEs1 | reg_neq]).
    assert (HthrE1 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> E1 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      assert (N14 : r <> mword_of_int 14)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /E1 upd_ne; [| congruence]. apply HthrE; assumption. }
    (* ---- +0x50: c.ld a5,72(a0) -- re-read p->sz ---- *)
    assert (Hszaddr2 : forall CID' : CpuId,
              add_vec (rget (CID := CID') E1 Ra0) (sign_extend' 64 (mword_of_int 72 : mword 12)) = p_sz p).
    { intros CID'; rgne. rewrite HE1a0; reflexivity. }
    iEval (rewrite -(Hszaddr2 CIDs31)) in "Hszc".
    iApply (wp_cld_s_sconf (CID := CIDs31) (mword_of_int (KernelSyms.sys_sbrk + 0x50)) Ra5 Ra0
              (mword_of_int 72 : mword 12) E1 (av - 6)%nat (pv_sz V) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi50 Hszc").
    iIntros (CIDs32 Hq32) "Hcg Hpc Hszc".
    iEval (rewrite (Hszaddr2 CIDs31)) in "Hszc".
    set (E2 := <[Regidx Ra5 := regval_into_reg (pv_sz V)]> E1).
    change (<[Regidx Ra5 := regval_into_reg (pv_sz V)]> E1) with E2.
    assert (Hpp52 : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x50) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_sbrk + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp52) in "Hpc".
    (* ---- +0x52: c.add a5,a5,a4 ---- *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x52))
              Ra5 Ra4 E2 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi52").
    iIntros (CIDs33 Hq33) "Hcg Hpc".
    set (E3 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (E2 !!! Regidx Ra5) (E2 !!! Regidx Ra4))]> E2).
    change (<[Regidx Ra5 := regval_into_reg
              (add_vec (E2 !!! Regidx Ra5) (E2 !!! Regidx Ra4))]> E2) with E3.
    assert (Hpp54 : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x52) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_sbrk + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp54) in "Hpc".
    assert (HE3a5 : E3 !!! Regidx Ra5 = add_vec (pv_sz V) (sbrk_arg v0)).
    { rewrite /E3 upd_eq. rewrite /E2 upd_eq.
      rewrite /E2 upd_ne; [| reg_neq]. rewrite HE1a4. reflexivity. }
    assert (HE3a0 : E3 !!! Regidx Ra0 = p).
    { rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq]. exact HE1a0. }
    assert (HE3sp : E3 !!! Regidx csp_rs1 = pa_stk sp0 6).
    { rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq]. exact HE1sp. }
    assert (HE3s1 : E3 !!! Regidx Rs1 = pv_sz V).
    { rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq]. exact HE1s1. }
    assert (HthrE3 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> E3 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      assert (N15 : r <> mword_of_int 15)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /E3 upd_ne; [| congruence]. rewrite /E2 upd_ne; [| congruence].
      apply HthrE1; assumption. }
    (* ---- +0x54: c.sd a5,72(a0) -- THE write, and the only one ---- *)
    assert (Hstaddr : add_vec (E3 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 72 : mword 12)) = p_sz p)
      by (rewrite HE3a0; reflexivity).
    iEval (rewrite -Hstaddr) in "Hszc".
    iApply (wp_csd_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x54))
              Ra5 Ra0 (mword_of_int 72 : mword 12) E3 (av - 6)%nat (pv_sz V) b
              with "Hcg Hpc Hi54 Hszc").
    iIntros (CIDs34 Hq34) "Hcg Hpc Hszc".
    (* The store leaf spells BOTH its address and its stored VALUE with [rget]
       (porting guide: for a store the respelling lands on the value side of
       the memory hypothesis).  [iApply] matched them by conversion, but a
       [rewrite] needs them back in [!!!] form first. *)
    iEval (rgne) in "Hszc".
    iEval (rgne) in "Hszc".
    iEval (rewrite HE3a5 Hstaddr) in "Hszc".
    assert (Hpp56 : add_vec_int (mword_of_int (KernelSyms.sys_sbrk + 0x54) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_sbrk + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp56) in "Hpc".
    (* ---- +0x56: c.j +0x0e, into the epilogue ---- *)
    assert (Htgt64l : add_vec (mword_of_int (KernelSyms.sys_sbrk + 0x56) : mword 64)
                        (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 7 : mword 11) ('b"0"))))
                      = mword_of_int (KernelSyms.sys_sbrk + 0x64))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.sys_sbrk + 0x56))
              (sign_extend' 21 (concat_vec (mword_of_int 7 : mword 11) ('b"0"))) E3 (av - 6)%nat b
              ltac:(rewrite Htgt64l; vm_compute; reflexivity)
              with "Hcg Hpc Hi56").
    iIntros (CIDs35 Hq35). iApply bi.later_intro. iIntros "Hcg Hpc".
    iEval (rewrite Htgt64l) in "Hpc".
    (* the new size still bounds the map: it only went UP *)
    iDestruct ("Hpback" $! (pv_upt V) (add_vec (pv_sz V) (sbrk_arg v0))
                 with "[%] [%] [%] [%] Hszc Hptc Hpt") as "Hpriv".
    { reflexivity. }
    { reflexivity. }
    { rewrite uint_unsigned uvm_maxsz_val. exact Hfits. }
    { apply (um_below_mono (pv_sz V)); [| exact Hbel]. rewrite Hsum. lia. }
    iDestruct (cpu_own_transport CIDE CIDs35 0%nat eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply ("EXIT" $! CIDs35 E3 (pv_upt V) (add_vec (pv_sz V) (sbrk_arg v0)) (pv_sz V)
              with "[%] [%] [%] [%] [%] Hcg Hcpu Hpc Hpriv [Hs5lo Hs5hi]").
    - wp_next_chain.
    - exact HE3sp.
    - exact HE3s1.
    - exact HthrE3.
    - right. split; [reflexivity |]. right.
      split; [exact Hnoteager |].
      split; [exact Hnpos |].
      split; [reflexivity |].
      split; [| reflexivity].
      rewrite uint_unsigned uvm_maxsz_val. rewrite -Hsum. exact Hfits.
    - iExists (word_of_words (trunc32 v0) (trunc32 v1)).
      iApply (word_pointsto_join4 _ _ _ _ Hal5 with "Hs5lo Hs5hi").
  Qed.

End ProofSysSbrk.

End SysSbrkProof.
