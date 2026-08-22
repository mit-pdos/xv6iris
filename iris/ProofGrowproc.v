(* ProofGrowproc.v -- the whole-function proof of growproc(), over the
   contracts of myproc(), uvmalloc() and uvmdealloc().

   Shape: a 32-byte ra/s0/s1/s2 frame, one call on every path, FIVE exits
   joining at TWO places -- the three "return 0" paths at the store +0x36,
   and everything at the epilogue +0x3c.  So the proof is two shared blocks
   ([gp_store], [gp_tail]) plus a dispatch, and no loop anywhere.

   THE THREE THINGS THIS PROOF IS ABOUT (everything else is bookkeeping):

   1. THE FRESHNESS uvmalloc DEMANDS IS PAID OUT OF THE INVARIANT.
      [ProcInv.proc_priv]'s [um_below] conjunct says the process maps
      nothing at or above [p->sz]; uvmalloc's run starts at PGROUNDUP(p->sz),
      so [ProcPtOwn.um_below_run_fresh] discharges the premise outright.
      Without that conjunct there is no proof: no caller of growproc could
      supply it either.

   2. THE THREE SIGNS OF [n] ARE THREE DIFFERENT ARITHMETICS.  [n > 0] is a
      SIGNED test and the range check that follows it is UNSIGNED, so the
      grow arm has to bridge the two ([RiscvExtras.add_vec_sint_unsigned]).  The [n < 0] arm
      bridges nothing: [sz + n] may WRAP, uvmdealloc is called at the
      wrapped value, and its guarded [uvmd_np] is what makes that arm say
      the truth (nothing was unmapped) instead of a falsehood.

   3. THE ONE WRITE RE-ESTABLISHES THE INVARIANT.  [sd a1,72(s2)] is the
      only store, and closing [proc_priv_addrspace] over it is exactly the
      obligation "the new size still bounds the new map" -- discharged by
      [um_below_grow] on the grow arm and [um_below_shrink] on the shrink
      arm, which is why those two laws exist. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap sets bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile InstrBytes WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn CalleeSaved KernelText.
Require Import KernelRvcDecode.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl WpSmodeIntr.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import PtBuild.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import FdSlots ProcInv.
Require Import FileInvDefs.
Require Import CodeGrowproc.
Require Import SpecMyproc SpecUvmalloc SpecUvmdealloc SpecGrowproc.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Local Open Scope Z_scope.

Set Printing Depth 40.

(* ===================================================================== *)
(*  §1  growproc's own arithmetic, kept mword-free where it can be.       *)
(* ===================================================================== *)

Lemma gp_n0 : (Z.of_nat 0%nat + 1 < 2 ^ 31)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma gp_xperm_rng : (0 <= 4 < 512)%Z.
Proof. lia. Qed.

Lemma gp_perm_ok : uvm_perm_ok (Z.lor 4 18).
Proof. change (Z.lor 4 18) with 22. exact uvm_perm_ok_22. Qed.

(* The [blez] at +0x16 is signed and the [bltu] at +0x26 is not, so the grow
   arm has to cross once: [RiscvExtras.sint64_unsigned] /
   [add_vec_sint_unsigned] / [sint64_range] are that crossing, shared with
   sys_sbrk. *)



(* The two contradictions the grow arm needs, over plain [Z] -- [lia] will
   not look at a goal that mentions [bv_unsigned] (the zify-hook rule). *)
Lemma gp_z_lt_le_absurd (a b : Z) : a < b -> b <= a -> False.
Proof. lia. Qed.

Lemma gp_z_sum_pos_ne0 (a b : Z) : 0 <= a -> 0 < b -> a + b = 0 -> False.
Proof. lia. Qed.

(* AN ALIGNED VALUE THAT ALMOST FITS, FITS. *)
Lemma gp_align_le_maxsz (x : Z) :
  x mod 4096 = 0 -> x < 274877898752 + 4096 -> x <= 274877898752.
Proof.
  intros Hm Hx.
  pose proof (Z_div_mod_eq_full x 4096) as Hd.
  assert (Hq : x = 4096 * (x / 4096)) by lia.
  assert (Hlt : 4096 * (x / 4096) < 4096 * 67108863) by lia.
  assert (Hql : x / 4096 < 67108863) by nia.
  lia.
Qed.

(* THE RUN uvmalloc MAPS ENDS AT OR BELOW TRAPFRAME.  [pu] is
   PGROUNDUP(oldsz) and the run length is [uvma_np]'s quotient; the run's
   end is the least multiple of 4096 at or above [nz], which is inside the
   region because [nz] is. *)
Lemma gp_z_run_end (pu nz : Z) :
  0 <= pu -> pu mod 4096 = 0 -> pu <= 274877898752 -> nz <= 274877898752 ->
  pu + 4096 * Z.of_nat (Z.to_nat ((nz - pu + 4095) / 4096)) <= 274877898752.
Proof.
  intros H0 Hm Hpu Hnz.
  destruct (Z.le_gt_cases ((nz - pu + 4095) / 4096) 0) as [Hq | Hq].
  - assert (Hz : Z.to_nat ((nz - pu + 4095) / 4096) = 0%nat)
      by (destruct ((nz - pu + 4095) / 4096) as [| pz | pz];
          [reflexivity | exfalso; lia | reflexivity]).
    rewrite Hz. lia.
  - rewrite Z2Nat.id; [| lia].
    assert (Hstep : 4096 * ((nz - pu + 4095) / 4096 - 1) < nz - pu).
    { pose proof (Z_div_mod_eq_full (nz - pu + 4095) 4096) as Hdm.
      pose proof (Z.mod_pos_bound (nz - pu + 4095) 4096 ltac:(lia)). lia. }
    apply gp_align_le_maxsz; [| lia].
    rewrite Zplus_mod Hm.
    rewrite (Z.mul_comm 4096 ((nz - pu + 4095) / 4096)).
    rewrite Z.mod_mul; [| lia]. reflexivity.
Qed.

Module GrowprocProof (Myproc : MYPROC) (Uvmalloc : UVMALLOC)
                     (Uvmdealloc : UVMDEALLOC) : GROWPROC.

Section ProofGrowproc.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ}.
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
  Notation Ra5 := (mword_of_int 15 : mword 5).


  (* =================================================================== *)
  (*  §2  The epilogue at +0x3c, entered by all five exits.               *)
  (* =================================================================== *)
  Lemma gp_tail `{CID0 : CpuId}
      (m Mt : regfile) (av : nat) (rv : mword 64)
      (sp0 ra0 s00 s10 s20 : mword 64) (b : bool) (p : mword 64) :
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
    sie_cap_gpr KT1 Mt (av - 4)%nat b p -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.growproc + 0x3c) : mword 64) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 3) (DfracOwn 1) s10 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 4) (DfracOwn 1) s20 -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf /\ mf !!! Regidx Ra0 = rv⌝ -∗
        sie_cap_gpr KT1 mf av b p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hav Hsp0 Hra0 Hs00 Hs10 Hs20 Hmtsp Hmta0 Hthr.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hb3 Hb4 Hcont".
    iPoseProof (gpi_3c with "Htext") as "Hi3c".
    iPoseProof (gpi_3e with "Htext") as "Hi3e".
    iPoseProof (gpi_40 with "Htext") as "Hi40".
    iPoseProof (gpi_42 with "Htext") as "Hi42".
    iPoseProof (gpi_44 with "Htext") as "Hi44".
    iPoseProof (gpi_46 with "Htext") as "Hi46".
    (* ---- +0x3c: c.ldsp ra,24(sp) ---- *)
    assert (Hpa1 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hmtsp. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.growproc + 0x3c))
              (mword_of_int 3 : mword 6) Rra Mt (av - 4)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3c Hb1").
    iIntros (CIDt1 Hnt1) "Hcg Hpc Hb1".
    iEval (rewrite Hpa1) in "Hb1".
    set (T1 := <[Regidx Rra := regval_into_reg ra0]> Mt).
    change (<[Regidx Rra := regval_into_reg ra0]> Mt) with T1.
    assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.growproc + 0x3c) : mword 64) 2
                    = mword_of_int (KernelSyms.growproc + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3e) in "Hpc".
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T1 upd_ne; [exact Hmtsp | reg_neq]).
    (* ---- +0x3e: c.ldsp s0,16(sp) ---- *)
    assert (Hpa2 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HT1sp. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.growproc + 0x3e))
              (mword_of_int 2 : mword 6) Rs0 T1 (av - 4)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3e Hb2").
    iIntros (CIDt2 Hnt2) "Hcg Hpc Hb2".
    iEval (rewrite Hpa2) in "Hb2".
    set (T2 := <[Regidx Rs0 := regval_into_reg s00]> T1).
    change (<[Regidx Rs0 := regval_into_reg s00]> T1) with T2.
    assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.growproc + 0x3e) : mword 64) 2
                    = mword_of_int (KernelSyms.growproc + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp40) in "Hpc".
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T2 upd_ne; [exact HT1sp | reg_neq]).
    (* ---- +0x40: c.ldsp s1,8(sp) ---- *)
    assert (Hpa3 : add_vec (T2 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HT2sp. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa3) in "Hb3".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.growproc + 0x40))
              (mword_of_int 1 : mword 6) Rs1 T2 (av - 4)%nat s10 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi40 Hb3").
    iIntros (CIDt3 Hnt3) "Hcg Hpc Hb3".
    iEval (rewrite Hpa3) in "Hb3".
    set (T3 := <[Regidx Rs1 := regval_into_reg s10]> T2).
    change (<[Regidx Rs1 := regval_into_reg s10]> T2) with T3.
    assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.growproc + 0x40) : mword 64) 2
                    = mword_of_int (KernelSyms.growproc + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp42) in "Hpc".
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T3 upd_ne; [exact HT2sp | reg_neq]).
    (* ---- +0x42: c.ldsp s2,0(sp) ---- *)
    assert (Hpa4 : add_vec (T3 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HT3sp. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa4) in "Hb4".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.growproc + 0x42))
              (mword_of_int 0 : mword 6) Rs2 T3 (av - 4)%nat s20 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi42 Hb4").
    iIntros (CIDt4 Hnt4) "Hcg Hpc Hb4".
    iEval (rewrite Hpa4) in "Hb4".
    set (T4 := <[Regidx Rs2 := regval_into_reg s20]> T3).
    change (<[Regidx Rs2 := regval_into_reg s20]> T3) with T4.
    assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.growproc + 0x42) : mword 64) 2
                    = mword_of_int (KernelSyms.growproc + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp44) in "Hpc".
    assert (HT4sp : T4 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T4 upd_ne; [exact HT3sp | reg_neq]).
    (* ---- +0x44: c.addi16sp sp,32 (frame pop) ---- *)
    assert (Hwv : add_vec (T4 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0)
      by (rewrite HT4sp; apply stk_pop_32).
    assert (Hpop : T4 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T4 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4)
      by (rewrite Hwv; exact HT4sp).
    iDestruct (stack_own_4_intro sp0 ra0 s00 s10 s20 with "Hb1 Hb2 Hb3 Hb4") as "Hframe".
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.growproc + 0x44))
              (mword_of_int 2 : mword 6) T4 (av - 4)%nat 4 b Hpop
              with "Hcg Hpc Hi44 Hframe").
    iIntros (CIDt5 Hnt5) "Hcg Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.growproc + 0x44) : mword 64) 2
                    = mword_of_int (KernelSyms.growproc + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp46) in "Hpc".
    set (T5 := <[Regidx csp_rs1 := regval_into_reg (add_vec (T4 !!! Regidx csp_rs1)
                  (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> T4).
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (T4 !!! Regidx csp_rs1)
              (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> T4) with T5.
    (* ---- +0x46: c.ret ---- *)
    assert (HT5ra : T5 !!! Regidx Rra = ra0).
    { rewrite /T5 upd_ne; [| reg_neq].
      rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_ne; [| reg_neq].
      rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_eq. reflexivity. }
    assert (Hrt : forall CID' : CpuId, ret_pc (rget (CID := CID') T5 Rra) = ret_pc ra0)
      by (intros CID'; rgne; rewrite HT5ra; reflexivity).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.growproc + 0x46))
              Rra T5 av b ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi46").
    iIntros (CIDt6 Hnt6) "Hcg Hpc".
    iEval (rewrite Hrt) in "Hpc".
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
  (*  §3  The store at +0x36, entered by all three "return 0" paths.      *)
  (* =================================================================== *)
  (*   [sd a1,72(s2)] then [c.li a0,0], falling into the epilogue.  Stated
     over the bare CELL rather than [proc_priv]: the block sits inside the
     accessor's window, and the three callers differ only in which
     descriptor and size they are about to close it at. *)
  Lemma gp_store `{CID0 : CpuId}
      (Ms : regfile) (av : nat) (p szold szv' : mword 64) (b : bool) :
    Ms !!! Regidx Ra1 = szv' ->
    Ms !!! Regidx Rs2 = p ->
    sie_cap_gpr KT1 Ms (av - 4)%nat b p -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.growproc + 0x36) : mword 64) -∗
    p_sz p ↦₈ szold -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ Ms' : regfile,
        ⌜Ms' !!! Regidx Ra0 = (mword_of_int 0 : mword 64)⌝ -∗
        ⌜forall r : mword 5, r <> Ra0 -> Ms' !!! Regidx r = Ms !!! Regidx r⌝ -∗
        sie_cap_gpr KT1 Ms' (av - 4)%nat b p -∗
        pc_is (mword_of_int (KernelSyms.growproc + 0x3c) : mword 64) -∗
        p_sz p ↦₈ szv' -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha1 Hs2.
    iIntros "Hcg #Htext Hpc Hsz Hcont".
    iPoseProof (gpi_36 with "Htext") as "Hi36".
    iPoseProof (gpi_3a with "Htext") as "Hi3a".
    (* ---- +0x36: sd a1,72(s2) ---- *)
    assert (Haddr : add_vec (Ms !!! Regidx Rs2) (sign_extend' 64 (mword_of_int 72 : mword 12))
                    = p_sz p) by (rewrite Hs2; reflexivity).
    iApply (wp_sd_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.growproc + 0x36))
              Ra1 Rs2 (mword_of_int 72 : mword 12) Ms (av - 4)%nat szold b
              with "Hcg Hpc Hi36 [Hsz]").
    { iEval (rgne; rewrite Haddr). iExact "Hsz". }
    iIntros (CIDp1 Hnp1) "Hcg Hpc Hsz".
    iEval (rgne; rgne; rewrite Ha1 Haddr) in "Hsz".
    assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.growproc + 0x36) : mword 64) 4
                    = mword_of_int (KernelSyms.growproc + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3a) in "Hpc".
    (* ---- +0x3a: c.li a0,0 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.growproc + 0x3a))
              Ra0 (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64) Ms (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi3a").
    iIntros (CIDp2 Hnp2) "Hcg Hpc".
    assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.growproc + 0x3a) : mword 64) 2
                    = mword_of_int (KernelSyms.growproc + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3c) in "Hpc".
    iSpecialize ("Hcont" $! CIDp2 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! (<[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> Ms)
              with "[%] [%] Hcg Hpc Hsz").
    - rewrite upd_eq. reflexivity.
    - intros r Hr. rewrite upd_ne; [reflexivity | congruence].
  Qed.

  (* =================================================================== *)
  (*  §4  THE CAPSTONE.                                                   *)
  (* =================================================================== *)
  Lemma wp_growproc_sconf (γa : gname) (γf : gname)
      (m : regfile) (av : nat) (eb : bool) (p : mword 64)
      (pid : mword 32) (V : pprivate) (b : bool) (lks : gset string)
    : wp_growproc_sconf_body γa γf m av eb p pid V b lks.
  Proof.
    cbv beta delta [wp_growproc_sconf_body].
    intros pcE nv ret_tgt Hav.
    
    set (sp0 := m !!! Regidx csp_rs1).
    set (ra0 := m !!! Regidx Rra).
    set (s00 := m !!! Regidx Rs0).
    set (s10 := m !!! Regidx Rs1).
    set (s20 := m !!! Regidx Rs2).
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    iIntros "Hcg Hcpu #Htext Hpc Hpriv #Henv Hcont".
    (* depth 0 forces the held set empty, so this body needs no order
       premise of its own -- every [locks_below] its callees raise is
       [locks_below ∅ _], which [lkbelow] closes outright. *)
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlkempty Hcpu]".
    iPoseProof (gpi_00 with "Htext") as "Hi00".
    iPoseProof (gpi_02 with "Htext") as "Hi02".
    iPoseProof (gpi_04 with "Htext") as "Hi04".
    iPoseProof (gpi_06 with "Htext") as "Hi06".
    iPoseProof (gpi_08 with "Htext") as "Hi08".
    iPoseProof (gpi_0a with "Htext") as "Hi0a".
    iPoseProof (gpi_0c with "Htext") as "Hi0c".
    iPoseProof (gpi_0e with "Htext") as "Hi0e".
    iPoseProof (gpi_12 with "Htext") as "Hi12".
    iPoseProof (gpi_14 with "Htext") as "Hi14".
    iPoseProof (gpi_16 with "Htext") as "Hi16".
    (* ---- +0x00: c.addi sp,-32 (frame push) ---- *)
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m av 4 b
              ltac:(lia) (stk_push_32 (m !!! Regidx csp_rs1))
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hn1) "Hcg Hframe Hpc".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.growproc + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /M1 upd_eq; apply stk_push_32).
    iDestruct (stack_own_4_elim with "Hframe") as (u1 u2 u3 u4) "(Hs1 & Hs2 & Hs3 & Hs4)".
    (* ---- +0x02 .. +0x08: save ra / s0 / s1 / s2 ---- *)
    assert (Hpa1 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa2 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa3 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa4 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite pa_stk_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa1) in "Hs1".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.growproc + 0x02))
              (mword_of_int 3 : mword 6) Rra M1 (av - 4)%nat u1 b
              with "Hcg Hpc Hi02 Hs1").
    iIntros (CID2 Hn2) "Hcg Hpc Hs1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.growproc + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.growproc + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    iEval (rewrite -Hpa2) in "Hs2".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.growproc + 0x04))
              (mword_of_int 2 : mword 6) Rs0 M1 (av - 4)%nat u2 b
              with "Hcg Hpc Hi04 Hs2").
    iIntros (CID3 Hn3) "Hcg Hpc Hs2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.growproc + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.growproc + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    iEval (rewrite -Hpa3) in "Hs3".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.growproc + 0x06))
              (mword_of_int 1 : mword 6) Rs1 M1 (av - 4)%nat u3 b
              with "Hcg Hpc Hi06 Hs3").
    iIntros (CID4 Hn4) "Hcg Hpc Hs3".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.growproc + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.growproc + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    iEval (rewrite -Hpa4) in "Hs4".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.growproc + 0x08))
              (mword_of_int 0 : mword 6) Rs2 M1 (av - 4)%nat u4 b
              with "Hcg Hpc Hi08 Hs4").
    iIntros (CID5 Hn5) "Hcg Hpc Hs4".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.growproc + 0x08) : mword 64) 2
                    = mword_of_int (KernelSyms.growproc + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    assert (HM1ra : M1 !!! Regidx Rra = ra0)
      by (rewrite /M1 upd_ne; [reflexivity | reg_neq]).
    assert (HM1s0 : M1 !!! Regidx Rs0 = s00)
      by (rewrite /M1 upd_ne; [reflexivity | reg_neq]).
    assert (HM1s1 : M1 !!! Regidx Rs1 = s10)
      by (rewrite /M1 upd_ne; [reflexivity | reg_neq]).
    assert (HM1s2 : M1 !!! Regidx Rs2 = s20)
      by (rewrite /M1 upd_ne; [reflexivity | reg_neq]).
    iEval (rgne; rewrite Hpa1 HM1ra) in "Hs1".
    iEval (rgne; rewrite Hpa2 HM1s0) in "Hs2".
    iEval (rgne; rewrite Hpa3 HM1s1) in "Hs3".
    iEval (rgne; rewrite Hpa4 HM1s2) in "Hs4".
    (* ---- +0x0a: c.addi4spn s0,sp,32 ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.growproc + 0x0a))
              (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) Rs0
              M1 (av - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a").
    iIntros (CID6 Hn6) "Hcg Hpc".
    set (M2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1).
    change (<[Regidx Rs0 := regval_into_reg
              (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1) with M2.
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.growproc + 0x0a) : mword 64) 2
                    = mword_of_int (KernelSyms.growproc + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* ---- +0x0c: c.mv s1,a0 -- s1 := n, parked across the call ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.growproc + 0x0c))
              Rs1 Ra0 M2 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c").
    iIntros (CID7 Hn7) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (M3 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (M2 !!! Regidx Ra0))]> M2).
    change (<[Regidx Rs1 := regval_into_reg (add_vec zero_reg (M2 !!! Regidx Ra0))]> M2) with M3.
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.growproc + 0x0c) : mword 64) 2
                    = mword_of_int (KernelSyms.growproc + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    assert (HM2a0 : M2 !!! Regidx Ra0 = nv).
    { rewrite /M2 upd_ne; [| reg_neq]. rewrite /M1 upd_ne; [reflexivity | reg_neq]. }
    assert (HM3s1 : M3 !!! Regidx Rs1 = nv)
      by (rewrite /M3 upd_eq HM2a0; apply add_vec_zero_l).
    (* ---- +0x0e: jal ra,myproc ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.growproc + 0x0e))
              Rra (mword_of_int 2096356 : mword 21) M3 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0e").
    iIntros (CID8 Hn8) "Hcg Hpc".
    set (M4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.growproc + 0x0e) : mword 64) 4)]> M3).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.growproc + 0x0e) : mword 64) 4)]> M3) with M4.
    assert (Hjmp : add_vec (mword_of_int (KernelSyms.growproc + 0x0e) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096356 : mword 21)) = mword_of_int KernelSyms.myproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmp) in "Hpc".
    assert (HM4ra : M4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.growproc + 0x0e) : mword 64) 4)
      by (rewrite /M4 upd_eq; reflexivity).
    assert (HM4sp : M4 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite /M4 upd_ne; [| reg_neq]. rewrite /M3 upd_ne; [| reg_neq].
      rewrite /M2 upd_ne; [| reg_neq]. exact HM1sp. }
    assert (HM4s1 : M4 !!! Regidx Rs1 = nv)
      by (rewrite /M4 upd_ne; [exact HM3s1 | reg_neq]).
    (* ---- myproc(): a0 = p ---- *)
    iDestruct (cpu_own_transport CID CID8 0%nat eb p b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (Myproc.wp_myproc_sconf M4 (av - 4)%nat 0%nat eb p b
              _ gp_n0 ltac:(lia)
              with "Hcg Hcpu Htext Hpc").
    iIntros (CID9 Hn9 ms A) "%Hms Hcg Hcpu Hpc %HcsA".
    destruct HcsA as [HcsA HAa0].
    assert (Hpc12 : ret_pc (M4 !!! Regidx Rra) = mword_of_int (KernelSyms.growproc + 0x12))
      by (rewrite HM4ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    assert (HAsp : A !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite (callee_saved_lookup HcsA csp_rs1 ltac:(vm_compute; reflexivity)); exact HM4sp).
    assert (HAs1 : A !!! Regidx Rs1 = nv)
      by (rewrite (callee_saved_lookup HcsA (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HM4s1).
    assert (HthrA : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> A !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite (callee_saved_lookup HcsA r Hr).
      rewrite /M4 upd_ne; [| congruence].
      rewrite /M3 upd_ne; [| congruence].
      rewrite /M2 upd_ne; [| congruence].
      rewrite /M1 upd_ne; [| congruence]. reflexivity. }
    (* ---- the ONE borrow out of [proc_priv] ---- *)
    iDestruct (proc_priv_sz_maxsz with "Hpriv") as %Hszmax.
    iDestruct (proc_priv_um_below with "Hpriv") as %Hbel.
    iDestruct (proc_priv_addrspace with "Hpriv") as "(Hszc & Hptc & Hpt & Hpback)".
    assert (Hszmaxz : (bv_unsigned (pv_sz V) <= 274877898752)%Z).
    { rewrite <- uint_unsigned. rewrite <- uvm_maxsz_val. exact Hszmax. }
    (* ---- +0x12: c.mv s2,a0 -- s2 := p ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.growproc + 0x12))
              Rs2 Ra0 A (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12").
    iIntros (CID10 Hn10) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A1 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (A !!! Regidx Ra0))]> A).
    change (<[Regidx Rs2 := regval_into_reg (add_vec zero_reg (A !!! Regidx Ra0))]> A) with A1.
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.growproc + 0x12) : mword 64) 2
                    = mword_of_int (KernelSyms.growproc + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    assert (HA1s2 : A1 !!! Regidx Rs2 = p)
      by (rewrite /A1 upd_eq HAa0; apply add_vec_zero_l).
    assert (HA1a0 : A1 !!! Regidx Ra0 = p)
      by (rewrite /A1 upd_ne; [exact HAa0 | reg_neq]).
    assert (HA1s1 : A1 !!! Regidx Rs1 = nv)
      by (rewrite /A1 upd_ne; [exact HAs1 | reg_neq]).
    assert (HA1sp : A1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /A1 upd_ne; [exact HAsp | reg_neq]).
    assert (HthrA1 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> A1 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      rewrite /A1 upd_ne; [| congruence]. apply HthrA; assumption. }
    (* ---- +0x14: c.ld a1,72(a0) -- a1 := p->sz ---- *)
    assert (Hszaddr : add_vec (A1 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 72 : mword 12)) = p_sz p)
      by (rewrite HA1a0; reflexivity).
    iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.growproc + 0x14)) Ra1 Ra0
              (mword_of_int 72 : mword 12) A1 (av - 4)%nat (pv_sz V) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [Hszc]").
    { iEval (rgne; rewrite Hszaddr). iExact "Hszc". }
    iIntros (CID11 Hn11) "Hcg Hpc Hszc".
    iEval (rgne; rewrite Hszaddr) in "Hszc".
    set (A2 := <[Regidx Ra1 := regval_into_reg (pv_sz V)]> A1).
    change (<[Regidx Ra1 := regval_into_reg (pv_sz V)]> A1) with A2.
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.growproc + 0x14) : mword 64) 2
                    = mword_of_int (KernelSyms.growproc + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    assert (HA2a1 : A2 !!! Regidx Ra1 = pv_sz V) by (rewrite /A2 upd_eq; reflexivity).
    assert (HA2s2 : A2 !!! Regidx Rs2 = p)
      by (rewrite /A2 upd_ne; [exact HA1s2 | reg_neq]).
    assert (HA2a0 : A2 !!! Regidx Ra0 = p)
      by (rewrite /A2 upd_ne; [exact HA1a0 | reg_neq]).
    assert (HA2s1 : A2 !!! Regidx Rs1 = nv)
      by (rewrite /A2 upd_ne; [exact HA1s1 | reg_neq]).
    assert (HA2sp : A2 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /A2 upd_ne; [exact HA1sp | reg_neq]).
    assert (HthrA2 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> A2 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      assert (N11 : r <> mword_of_int 11)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /A2 upd_ne; [| congruence]. apply HthrA1; assumption. }
    (* ================================================================= *)
    (*  THE EXIT, shared by all five arms: close the accessor at the pair  *)
    (*  the arm ended at, run the epilogue, hand the caller its answer.    *)
    (* ================================================================= *)
    iAssert (∀ (CIDx : CpuId) (Mf : regfile) (P' : uptd) (szv' rv : mword 64),
        ⌜b = false \/ p = zero_reg -> (CIDx : CPU) = (CID : CPU)⌝ -∗
        ⌜Mf !!! Regidx csp_rs1 = pa_stk sp0 4⌝ -∗
        ⌜Mf !!! Regidx Ra0 = rv⌝ -∗
        ⌜forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
            r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> Mf !!! Regidx r = m !!! Regidx r⌝ -∗
        ⌜ud_root P' = ud_root (pv_upt V)⌝ -∗
        ⌜ud_tfp P' = ud_tfp (pv_upt V)⌝ -∗
        ⌜(uint szv' <= uvm_maxsz)%Z⌝ -∗
        ⌜um_below szv' (ud_um P')⌝ -∗
        ⌜growproc_ok (pv_sz V) nv (pv_upt V) P' szv' rv⌝ -∗
        sie_cap_gpr KT1 (CID:=CIDx) Mf (av - 4)%nat b p -∗
        cpu_own (CID:=CIDx) 0%nat eb p b lks -∗
        pc_is (CID:=CIDx) (mword_of_int (KernelSyms.growproc + 0x3c) : mword 64) -∗
        p_sz p ↦₈ szv' -∗
        p_pagetable p ↦₈ page_base (ud_root (pv_upt V)) -∗
        proc_pt P' -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 2) (DfracOwn 1) s00 -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 3) (DfracOwn 1) s10 -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 4) (DfracOwn 1) s20 -∗
        WP (Loop : expr riscv_lang))%I
      with "[Hpback Hcont]" as "EXIT".
    { iIntros (CIDx Mf P' szv' rv)
        "%Hchain %Hfsp %Hfa0 %Hfthr %Hroot %Htfp %Hszb %Hbel' %Hok Hcg Hcpu Hpc Hszc Hptc Hpt Hb1 Hb2 Hb3 Hb4".
      iDestruct ("Hpback" $! P' szv' with "[%] [%] [%] [%] Hszc Hptc Hpt") as "Hpriv";
        [exact Hroot | exact Htfp | exact Hszb | exact Hbel' |].
      iApply (gp_tail m Mf av rv sp0 ra0 s00 s10 s20 b p
                ltac:(lia) eq_refl eq_refl eq_refl eq_refl eq_refl
                Hfsp Hfa0 Hfthr
                with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4").
      iIntros (CIDf Hnf mf) "[%Hcsf %Hmfa0] Hcg Hpc".
      iDestruct (cpu_own_transport CIDx CIDf 0%nat eb p b ltac:(wp_next_chain)
                   with "Hcpu") as "Hcpu".
      iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf P' szv' with "[%] [%] Hcg Hcpu Hpc Hpriv").
      { exact Hcsf. }
      { rewrite Hmfa0. exact Hok. } }
    iClear "Hi00 Hi02 Hi04 Hi06 Hi08 Hi0a Hi0c Hi0e Hi12 Hi14".

    iPoseProof (gpi_1a with "Htext") as "Hi1a".
    iPoseProof (gpi_1e with "Htext") as "Hi1e".
    iPoseProof (gpi_22 with "Htext") as "Hi22".
    iPoseProof (gpi_24 with "Htext") as "Hi24".
    iPoseProof (gpi_26 with "Htext") as "Hi26".
    iPoseProof (gpi_2a with "Htext") as "Hi2a".
    iPoseProof (gpi_2c with "Htext") as "Hi2c".
    iPoseProof (gpi_2e with "Htext") as "Hi2e".
    iPoseProof (gpi_32 with "Htext") as "Hi32".
    iPoseProof (gpi_34 with "Htext") as "Hi34".
    iPoseProof (gpi_48 with "Htext") as "Hi48".
    iPoseProof (gpi_4c with "Htext") as "Hi4c".
    iPoseProof (gpi_50 with "Htext") as "Hi50".
    iPoseProof (gpi_52 with "Htext") as "Hi52".
    iPoseProof (gpi_56 with "Htext") as "Hi56".
    iPoseProof (gpi_58 with "Htext") as "Hi58".
    iPoseProof (gpi_5a with "Htext") as "Hi5a".
    iPoseProof (gpi_5c with "Htext") as "Hi5c".
    iPoseProof (gpi_5e with "Htext") as "Hi5e".
    iPoseProof (gpi_60 with "Htext") as "Hi60".
    (* ================================================================= *)
    (*  §4a  +0x16  bge x0,s1 : the [n > 0] test, SIGNED.                  *)
    (* ================================================================= *)
    destruct (zopz0zKzJ_s (zero_reg : mword 64) (A2 !!! Regidx Rs1)) eqn:Hblez.
    2:{ (* =============== n > 0: grow =============== *)
      assert (Hnpos : (0 < sint nv)%Z).
      { rewrite HA2s1 in Hblez. unfold zopz0zKzJ_s in Hblez.
        assert (Hz0 : sint (zero_reg : mword 64) = 0%Z) by reflexivity.
        rewrite Hz0 Z.geb_leb in Hblez. apply Z.leb_gt in Hblez. exact Hblez. }
      pose proof (sint64_range nv) as Hnb.
      pose proof (bv_unsigned_in_range _ (pv_sz V)) as [Hsz0 _].
      assert (Hnewu : bv_unsigned (add_vec (pv_sz V) nv)
                      = (bv_unsigned (pv_sz V) + sint nv)%Z)
        by (apply add_vec_sint_unsigned; lia).
      assert (Hlesz : (bv_unsigned (pv_sz V) <= bv_unsigned (add_vec (pv_sz V) nv))%Z)
        by lia.
      iApply (wp_bge_x0_fall_s_sconf (mword_of_int (KernelSyms.growproc + 0x16))
                (mword_of_int 50 : mword 13) Rs1 A2 (av - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(rgne; exact Hblez)
                with "Hcg Hpc Hi16").
      iIntros (CID12 Hn12) "Hcg Hpc".
      assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.growproc + 0x16) : mword 64) 4
                      = mword_of_int (KernelSyms.growproc + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1a) in "Hpc".
      (* ---- +0x1a: add a2,s1,a1 -- a2 := sz + n ---- *)
      iApply (wp_add_s_sconf (mword_of_int (KernelSyms.growproc + 0x1a))
                Ra2 Rs1 Ra1 (add_vec (pv_sz V) nv) A2 (av - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(rgne; rgne; rewrite HA2s1 HA2a1; apply add_vec64_comm)
                with "Hcg Hpc Hi1a").
      iIntros (CID13 Hn13) "Hcg Hpc".
      set (B1 := <[Regidx Ra2 := regval_into_reg (add_vec (pv_sz V) nv)]> A2).
      change (<[Regidx Ra2 := regval_into_reg (add_vec (pv_sz V) nv)]> A2) with B1.
      assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.growproc + 0x1a) : mword 64) 4
                      = mword_of_int (KernelSyms.growproc + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1e) in "Hpc".
      (* ---- +0x1e .. +0x24: a5 := TRAPFRAME, in three instructions ---- *)
      iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.growproc + 0x1e))
                Ra5 (mword_of_int 8192 : mword 20) (mword_of_int 33554432 : mword 64)
                B1 (av - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi1e").
      iIntros (CID14 Hn14) "Hcg Hpc".
      set (B2 := <[Regidx Ra5 := regval_into_reg (mword_of_int 33554432 : mword 64)]> B1).
      change (<[Regidx Ra5 := regval_into_reg (mword_of_int 33554432 : mword 64)]> B1) with B2.
      assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.growproc + 0x1e) : mword 64) 4
                      = mword_of_int (KernelSyms.growproc + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp22) in "Hpc".
      iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.growproc + 0x22))
                Ra5 (mword_of_int 63 : mword 6) B2 (av - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi22").
      iIntros (CID15 Hn15) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (B3 := <[Regidx Ra5 := regval_into_reg
            (add_vec (B2 !!! Regidx Ra5) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> B2).
      change (<[Regidx Ra5 := regval_into_reg
            (add_vec (B2 !!! Regidx Ra5) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> B2) with B3.
      assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.growproc + 0x22) : mword 64) 2
                      = mword_of_int (KernelSyms.growproc + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp24) in "Hpc".
      iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.growproc + 0x24))
                (Regidx Ra5) Ra5 (mword_of_int 13 : mword 6) B3 (av - 4)%nat b
                eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi24").
      iIntros (CID16 Hn16) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (B4 := <[Regidx Ra5 := regval_into_reg
            (shift_bits_left (B3 !!! Regidx Ra5)
               (subrange_vec_dec (mword_of_int 13 : mword 6) (Z.sub log2_xlen 1) 0))]> B3).
      change (<[Regidx Ra5 := regval_into_reg
            (shift_bits_left (B3 !!! Regidx Ra5)
               (subrange_vec_dec (mword_of_int 13 : mword 6) (Z.sub log2_xlen 1) 0))]> B3) with B4.
      assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.growproc + 0x24) : mword 64) 2
                      = mword_of_int (KernelSyms.growproc + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp26) in "Hpc".
      (* the three instructions above build exactly TRAPFRAME *)
      assert (HB4a5 : B4 !!! Regidx Ra5 = (mword_of_int 274877898752 : mword 64)).
      { rewrite /B4 upd_eq /B3 upd_eq /B2 upd_eq. apply bv_eq; vm_compute; reflexivity. }
      assert (HB4a2 : B4 !!! Regidx Ra2 = add_vec (pv_sz V) nv).
      { rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_ne; [| reg_neq].
        rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_eq. reflexivity. }
      assert (HB4a1 : B4 !!! Regidx Ra1 = pv_sz V).
      { rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_ne; [| reg_neq].
        rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [| reg_neq]. exact HA2a1. }
      assert (HB4a0 : B4 !!! Regidx Ra0 = p).
      { rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_ne; [| reg_neq].
        rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [| reg_neq]. exact HA2a0. }
      assert (HB4s2 : B4 !!! Regidx Rs2 = p).
      { rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_ne; [| reg_neq].
        rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [| reg_neq]. exact HA2s2. }
      assert (HB4sp : B4 !!! Regidx csp_rs1 = pa_stk sp0 4).
      { rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_ne; [| reg_neq].
        rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [| reg_neq]. exact HA2sp. }
      assert (HthrB4 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> B4 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18.
        assert (N12 : r <> mword_of_int 12)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N15 : r <> mword_of_int 15)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /B4 upd_ne; [| congruence]. rewrite /B3 upd_ne; [| congruence].
        rewrite /B2 upd_ne; [| congruence]. rewrite /B1 upd_ne; [| congruence].
        apply HthrA2; assumption. }
      (* ---- +0x26: bltu a5,a2 -- the TRAPFRAME test, UNSIGNED ---- *)
      destruct (zopz0zI_u (B4 !!! Regidx Ra5) (B4 !!! Regidx Ra2)) eqn:Hbltu.
      { (* TAKEN: sz + n > TRAPFRAME, return -1 without calling anything *)
        assert (Htgt5a : add_vec (mword_of_int (KernelSyms.growproc + 0x26) : mword 64)
                           (sign_extend' 64 (mword_of_int 52 : mword 13))
                         = mword_of_int (KernelSyms.growproc + 0x5a))
          by (apply bv_eq; vm_compute; reflexivity).
        iApply (wp_bltu_taken_s_sconf (mword_of_int (KernelSyms.growproc + 0x26))
                  (mword_of_int 52 : mword 13) Ra2 Ra5 B4 (av - 4)%nat b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rgne; rgne; exact Hbltu)
                  ltac:(rewrite Htgt5a; vm_compute; reflexivity)
                  with "Hcg Hpc Hi26").
        iApply bi.later_intro. iIntros (CID17 Hn17) "Hcg Hpc".
        iEval (rewrite Htgt5a) in "Hpc".
        (* +0x5a c.li a0,-1 *)
        iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.growproc + 0x5a))
                  Ra0 (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64) B4 (av - 4)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc Hi5a").
        iIntros (CID18 Hn18) "Hcg Hpc".
        set (X1 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> B4).
        change (<[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> B4) with X1.
        assert (Hpp5c : add_vec_int (mword_of_int (KernelSyms.growproc + 0x5a) : mword 64) 2
                        = mword_of_int (KernelSyms.growproc + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp5c) in "Hpc".
        (* +0x5c c.j -0x20 *)
        assert (Htgt3c : add_vec (mword_of_int (KernelSyms.growproc + 0x5c) : mword 64)
                           (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2032 : mword 11) ('b"0"))))
                         = mword_of_int (KernelSyms.growproc + 0x3c))
          by (apply bv_eq; vm_compute; reflexivity).
        iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.growproc + 0x5c))
                  (sign_extend' 21 (concat_vec (mword_of_int 2032 : mword 11) ('b"0"))) X1 (av - 4)%nat b
                  ltac:(rewrite Htgt3c; vm_compute; reflexivity)
                  with "Hcg Hpc Hi5c").
        iIntros (CID19 Hn19). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htgt3c) in "Hpc".
        iDestruct (cpu_own_transport CID9 CID19 0%nat eb p b ltac:(wp_next_chain)
                     with "Hcpu") as "Hcpu".
        iApply ("EXIT" $! CID19 X1 (pv_upt V) (pv_sz V) (mword_of_int (-1) : mword 64)
                  with "[%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hcpu Hpc Hszc Hptc Hpt Hs1 Hs2 Hs3 Hs4").
        - wp_next_chain.
        - rewrite /X1 upd_ne; [exact HB4sp | reg_neq].
        - rewrite /X1 upd_eq. reflexivity.
        - intros r Hr Ncsp N8 N9 N18.
          assert (N10 : r <> mword_of_int 10)
            by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          rewrite /X1 upd_ne; [| congruence]. apply HthrB4; assumption.
        - reflexivity.
        - reflexivity.
        - exact Hszmax.
        - exact Hbel.
        - left. split; [reflexivity | split; reflexivity]. }
      (* ---- FALL: sz + n fits, call uvmalloc ---- *)
      assert (Hnewle : (bv_unsigned (add_vec (pv_sz V) nv) <= 274877898752)%Z).
      { rewrite HB4a5 HB4a2 in Hbltu. unfold zopz0zI_u in Hbltu.
        apply Z.ltb_ge in Hbltu. rewrite !uint_unsigned in Hbltu.
        assert (Hlit : bv_unsigned (mword_of_int 274877898752 : mword 64) = 274877898752%Z)
          by (vm_compute; reflexivity).
        rewrite Hlit in Hbltu. exact Hbltu. }
      iApply (wp_bltu_fall_s_sconf (mword_of_int (KernelSyms.growproc + 0x26))
                (mword_of_int 52 : mword 13) Ra2 Ra5 B4 (av - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgne; rgne; exact Hbltu)
                with "Hcg Hpc Hi26").
      iIntros (CID17 Hn17) "Hcg Hpc".
      assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.growproc + 0x26) : mword 64) 4
                      = mword_of_int (KernelSyms.growproc + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2a) in "Hpc".
      (* ---- +0x2a: c.li a3,4 -- xperm = PTE_W ---- *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.growproc + 0x2a))
                Ra3 (mword_of_int 4 : mword 6) (mword_of_int 4 : mword 64) B4 (av - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi2a").
      iIntros (CID18 Hn18) "Hcg Hpc".
      set (C1 := <[Regidx Ra3 := regval_into_reg (mword_of_int 4 : mword 64)]> B4).
      change (<[Regidx Ra3 := regval_into_reg (mword_of_int 4 : mword 64)]> B4) with C1.
      assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.growproc + 0x2a) : mword 64) 2
                      = mword_of_int (KernelSyms.growproc + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2c) in "Hpc".
      (* ---- +0x2c: c.ld a0,80(a0) -- a0 := p->pagetable ---- *)
      assert (HC1a0 : C1 !!! Regidx Ra0 = p) by (rewrite /C1 upd_ne; [exact HB4a0 | reg_neq]).
      assert (Hpta : add_vec (C1 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 80 : mword 12))
                     = p_pagetable p) by (rewrite HC1a0; reflexivity).
      iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.growproc + 0x2c)) Ra0 Ra0
                (mword_of_int 80 : mword 12) C1 (av - 4)%nat (page_base (ud_root (pv_upt V))) b
                (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi2c [Hptc]").
      { iEval (rgne; rewrite Hpta). iExact "Hptc". }
      iIntros (CID19 Hn19) "Hcg Hpc Hptc".
      iEval (rgne; rewrite Hpta) in "Hptc".
      set (C2 := <[Regidx Ra0 := regval_into_reg (page_base (ud_root (pv_upt V)))]> C1).
      change (<[Regidx Ra0 := regval_into_reg (page_base (ud_root (pv_upt V)))]> C1) with C2.
      assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.growproc + 0x2c) : mword 64) 2
                      = mword_of_int (KernelSyms.growproc + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2e) in "Hpc".
      (* ---- +0x2e: jal ra,uvmalloc ---- *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.growproc + 0x2e))
                Rra (mword_of_int 2094698 : mword 21) C2 (av - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi2e").
      iIntros (CID20 Hn20) "Hcg Hpc".
      set (C3 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.growproc + 0x2e) : mword 64) 4)]> C2).
      change (<[Regidx Rra := regval_into_reg
                (add_vec_int (mword_of_int (KernelSyms.growproc + 0x2e) : mword 64) 4)]> C2) with C3.
      assert (Hjmpua : add_vec (mword_of_int (KernelSyms.growproc + 0x2e) : mword 64)
                         (sign_extend' 64 (mword_of_int 2094698 : mword 21))
                       = mword_of_int KernelSyms.uvmalloc)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjmpua) in "Hpc".
      assert (HC3a0 : C3 !!! Regidx Ra0 = page_base (ud_root (pv_upt V))).
      { rewrite /C3 upd_ne; [| reg_neq]. rewrite /C2 upd_eq. reflexivity. }
      assert (HC3a1 : C3 !!! Regidx Ra1 = pv_sz V).
      { rewrite /C3 upd_ne; [| reg_neq]. rewrite /C2 upd_ne; [| reg_neq].
        rewrite /C1 upd_ne; [| reg_neq]. exact HB4a1. }
      assert (HC3a2 : C3 !!! Regidx Ra2 = add_vec (pv_sz V) nv).
      { rewrite /C3 upd_ne; [| reg_neq]. rewrite /C2 upd_ne; [| reg_neq].
        rewrite /C1 upd_ne; [| reg_neq]. exact HB4a2. }
      assert (HC3a3 : C3 !!! Regidx Ra3 = (mword_of_int 4 : mword 64)).
      { rewrite /C3 upd_ne; [| reg_neq]. rewrite /C2 upd_ne; [| reg_neq].
        rewrite /C1 upd_eq. reflexivity. }
      assert (HC3sp : C3 !!! Regidx csp_rs1 = pa_stk sp0 4).
      { rewrite /C3 upd_ne; [| reg_neq]. rewrite /C2 upd_ne; [| reg_neq].
        rewrite /C1 upd_ne; [| reg_neq]. exact HB4sp. }
      assert (HC3s2 : C3 !!! Regidx Rs2 = p).
      { rewrite /C3 upd_ne; [| reg_neq]. rewrite /C2 upd_ne; [| reg_neq].
        rewrite /C1 upd_ne; [| reg_neq]. exact HB4s2. }
      assert (HC3ra : C3 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KernelSyms.growproc + 0x2e) : mword 64) 4)
        by (rewrite /C3 upd_eq; reflexivity).
      assert (HthrC3 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> C3 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18.
        assert (N1 : r <> mword_of_int 1)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N10 : r <> mword_of_int 10)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N13 : r <> mword_of_int 13)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /C3 upd_ne; [| congruence]. rewrite /C2 upd_ne; [| congruence].
        rewrite /C1 upd_ne; [| congruence]. apply HthrB4; assumption. }
      (* the two premises about the RUN: it stays inside the user region,
         and -- the whole point -- it is fresh in [ud_um]. *)
      destruct (pgroundup_maxsz (pv_sz V) ltac:(rewrite -uint_unsigned; exact Hszmax))
        as [[Hpuge Hpule] Hpumod].
      rewrite uvm_maxsz_val in Hpule.
      pose proof (proj1 (bv_unsigned_in_range _ (pgroundup (pv_sz V)))) as Hpu0.
      assert (Hrun : (bv_unsigned (pgroundup (pv_sz V))
                      + 4096 * Z.of_nat (uvma_np (pv_sz V) (add_vec (pv_sz V) nv))
                      <= uvm_maxsz)%Z).
      { rewrite uvm_maxsz_val. unfold uvma_np.
        apply gp_z_run_end; [exact Hpu0 | exact Hpumod | exact Hpule | exact Hnewle]. }
      (* growproc TESTS the size, so it pays the freshness premise's guard by
         ignoring it -- the run is inside TRAPFRAME whatever iteration the
         loop is at ([Hrun]).  SpecUvmalloc.v's note says why the guard is
         there; it is kexec that cannot bound the run. *)
      assert (Hfresh : forall i : nat, (i < uvma_np (pv_sz V) (add_vec (pv_sz V) nv))%nat ->
                (bv_unsigned (pgroundup (pv_sz V)) + 4096 * Z.of_nat i + 4096
                 <= uvm_maxsz)%Z ->
                ud_um (pv_upt V) !! vpn_at (svpn_of (pgroundup (pv_sz V))) i = None).
      { intros i Hi _.
        apply (um_below_run_fresh (pv_sz V) (ud_um (pv_upt V))
                 (uvma_np (pv_sz V) (add_vec (pv_sz V) nv)) i Hbel);
          [rewrite uvm_maxsz_val; exact Hszmaxz | exact Hrun | exact Hi]. }
      (* SpecUvmalloc.v still asks for the RAW entry map's tp slot
         ([mm !!! Regidx 4 = cid_word]) -- a shape this sweep left in place
         there, and one nothing can produce about a raw map any more
         ([tp_pin] hides slot 4, and [callee_saved] says nothing about tp).
         Calling at [C3p := tp_pin C3] makes the premise true BY
         CONSTRUCTION ([upd_eq]) and costs nothing: [C3p] agrees with [C3]
         on sp ([tp_pin_sp]) and on every non-tp register ([rget_ne]), so
         [sie_cap_gpr] and [callee_saved] survive the swap.  Same recipe as
         ProofProcPagetable.v's uvmcreate call. *)
      set (C3p := tp_pin C3).
      assert (Hpinid3 : tp_pin C3p = tp_pin C3)
        by (rewrite /C3p; apply (tp_pin_id (tp_pin C3) (rget_tp C3))).
      assert (Hc3psp : C3p !!! Regidx csp_rs1 = C3 !!! Regidx csp_rs1)
        by (rewrite /C3p; exact (tp_pin_sp C3)).
      assert (Hgpreq3 : sie_cap_gpr KT1 C3 (av - 4)%nat b p = sie_cap_gpr KT1 C3p (av - 4)%nat b p)
        by (unfold sie_cap_gpr, sie_cap; rewrite Hc3psp Hpinid3; reflexivity).
      iEval (rewrite Hgpreq3) in "Hcg".
      assert (HC3pne : forall r : mword 5, r <> Rtp -> C3p !!! Regidx r = C3 !!! Regidx r).
      { intros r Hr. rewrite /C3p. apply (rget_ne C3 r).
        intro He. injection He as He2. congruence. }
      assert (HC3ptp : C3p !!! Regidx Rtp = cid_word)
        by (rewrite /C3p upd_eq; reflexivity).
      assert (HC3pa0 : C3p !!! Regidx Ra0 = page_base (ud_root (pv_upt V)))
        by (rewrite (HC3pne Ra0 ltac:(reg_neq)); exact HC3a0).
      assert (HC3pa1 : C3p !!! Regidx Ra1 = pv_sz V)
        by (rewrite (HC3pne Ra1 ltac:(reg_neq)); exact HC3a1).
      assert (HC3pa2 : C3p !!! Regidx Ra2 = add_vec (pv_sz V) nv)
        by (rewrite (HC3pne Ra2 ltac:(reg_neq)); exact HC3a2).
      assert (HC3pa3 : C3p !!! Regidx Ra3 = (mword_of_int 4 : mword 64))
        by (rewrite (HC3pne Ra3 ltac:(reg_neq)); exact HC3a3).
      assert (HC3psp2 : C3p !!! Regidx csp_rs1 = pa_stk sp0 4)
        by (rewrite Hc3psp; exact HC3sp).
      assert (HC3ps2 : C3p !!! Regidx Rs2 = p)
        by (rewrite (HC3pne Rs2 ltac:(reg_neq)); exact HC3s2).
      assert (HC3pra : C3p !!! Regidx Rra
                       = add_vec_int (mword_of_int (KernelSyms.growproc + 0x2e) : mword 64) 4)
        by (rewrite (HC3pne Rra ltac:(reg_neq)); exact HC3ra).
      assert (HthrC3p : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> C3p !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18.
        assert (N4 : r <> Rtp)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite (HC3pne r N4). apply HthrC3; assumption. }
      iDestruct (cpu_own_transport CID9 CID20 0%nat eb p b ltac:(wp_next_chain)
                   with "Hcpu") as "Hcpu".
      iApply (Uvmalloc.wp_uvmalloc_sconf γa C3p (pv_upt V) 4 (av - 4)%nat eb p b lks
                ltac:(lia) HC3ptp HC3pa0 HC3pa3 gp_xperm_rng gp_perm_ok
                ltac:(rewrite HC3pa1 uint_unsigned uvm_maxsz_val; exact Hszmaxz)
                (* growproc TESTS the bound ([sz + n > TRAPFRAME] returns -1),
                   so it pays uvmalloc's left disjunct; the coverage arm is
                   for kexec, whose newsz comes out of a file. *)
                ltac:(left; rewrite HC3pa2 uint_unsigned uvm_maxsz_val;
                      exact Hnewle)
                ltac:(rewrite HC3pa1 HC3pa2; exact Hfresh)
                with "Hcg Hcpu Htext Hpc Hpt Henv").
      all: try lkbelow.
      iIntros (CID21 Hn21 mr) "Hcg Hcpu Hpc %Hcsr Hpost".
      assert (Hpc32 : ret_pc (C3p !!! Regidx Rra) = mword_of_int (KernelSyms.growproc + 0x32))
        by (rewrite HC3pra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc32) in "Hpc".
      assert (Hmrsp : mr !!! Regidx csp_rs1 = pa_stk sp0 4)
        by (rewrite (callee_saved_lookup Hcsr csp_rs1 ltac:(vm_compute; reflexivity)); exact HC3psp2).
      assert (Hmrs2 : mr !!! Regidx Rs2 = p)
        by (rewrite (callee_saved_lookup Hcsr (mword_of_int 18) ltac:(vm_compute; reflexivity)); exact HC3ps2).
      assert (Hthrmr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> mr !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18.
        rewrite (callee_saved_lookup Hcsr r Hr). apply HthrC3p; assumption. }
      (* ---- +0x32: c.mv a1,a0 ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.growproc + 0x32))
                Ra1 Ra0 mr (av - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi32").
      iIntros (CID22 Hn22) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (D1 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (mr !!! Regidx Ra0))]> mr).
      change (<[Regidx Ra1 := regval_into_reg (add_vec zero_reg (mr !!! Regidx Ra0))]> mr) with D1.
      assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.growproc + 0x32) : mword 64) 2
                      = mword_of_int (KernelSyms.growproc + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp34) in "Hpc".
      assert (HD1sp : D1 !!! Regidx csp_rs1 = pa_stk sp0 4)
        by (rewrite /D1 upd_ne; [exact Hmrsp | reg_neq]).
      assert (HD1s2 : D1 !!! Regidx Rs2 = p)
        by (rewrite /D1 upd_ne; [exact Hmrs2 | reg_neq]).
      assert (HD1a0 : D1 !!! Regidx Ra0 = mr !!! Regidx Ra0)
        by (rewrite /D1 upd_ne; [reflexivity | reg_neq]).
      assert (HD1a1 : D1 !!! Regidx Ra1 = mr !!! Regidx Ra0)
        by (rewrite /D1 upd_eq; apply add_vec_zero_l).
      assert (HthrD1 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> D1 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18.
        assert (N11 : r <> mword_of_int 11)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /D1 upd_ne; [| congruence]. apply Hthrmr; assumption. }
      (* ---- +0x34: c.beqz a0 -- did uvmalloc fail? ---- *)
      iDestruct "Hpost" as "[[%Hz Hpt] | Hpost]".
      { (* OUT OF MEMORY: a0 = 0, the table is exactly the one we passed *)
        assert (Hzz : eq_vec (D1 !!! Regidx Ra0) (zero_reg : mword 64) = true).
        { rewrite HD1a0 Hz. apply eq_vec_true_iff. apply bv_eq; vm_compute; reflexivity. }
        assert (Htgt5e : add_vec (mword_of_int (KernelSyms.growproc + 0x34) : mword 64)
                           (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 21 : mword 8) ('b"0"))))
                         = mword_of_int (KernelSyms.growproc + 0x5e))
          by (apply bv_eq; vm_compute; reflexivity).
        iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.growproc + 0x34))
                  (mword_of_int 21 : mword 8) (Cregidx (mword_of_int 2)) Ra0 D1 (av - 4)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rgne; exact Hzz) ltac:(rewrite Htgt5e; vm_compute; reflexivity)
                  with "Hcg Hpc Hi34").
        iApply bi.later_intro. iIntros (CID23 Hn23) "Hcg Hpc".
        iEval (rewrite Htgt5e) in "Hpc".
        (* +0x5e c.li a0,-1 ; +0x60 c.j -0x24 *)
        iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.growproc + 0x5e))
                  Ra0 (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64) D1 (av - 4)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc Hi5e").
        iIntros (CID24 Hn24) "Hcg Hpc".
        set (X2 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> D1).
        change (<[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> D1) with X2.
        assert (Hpp60 : add_vec_int (mword_of_int (KernelSyms.growproc + 0x5e) : mword 64) 2
                        = mword_of_int (KernelSyms.growproc + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp60) in "Hpc".
        assert (Htgt3c2 : add_vec (mword_of_int (KernelSyms.growproc + 0x60) : mword 64)
                            (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2030 : mword 11) ('b"0"))))
                          = mword_of_int (KernelSyms.growproc + 0x3c))
          by (apply bv_eq; vm_compute; reflexivity).
        iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.growproc + 0x60))
                  (sign_extend' 21 (concat_vec (mword_of_int 2030 : mword 11) ('b"0"))) X2 (av - 4)%nat b
                  ltac:(rewrite Htgt3c2; vm_compute; reflexivity)
                  with "Hcg Hpc Hi60").
        iIntros (CID25 Hn25). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htgt3c2) in "Hpc".
        iDestruct (cpu_own_transport CID21 CID25 0%nat eb p b ltac:(wp_next_chain)
                     with "Hcpu") as "Hcpu".
        iApply ("EXIT" $! CID25 X2 (pv_upt V) (pv_sz V) (mword_of_int (-1) : mword 64)
                  with "[%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hcpu Hpc Hszc Hptc Hpt Hs1 Hs2 Hs3 Hs4").
        - wp_next_chain.
        - rewrite /X2 upd_ne; [exact HD1sp | reg_neq].
        - rewrite /X2 upd_eq. reflexivity.
        - intros r Hr Ncsp N8 N9 N18.
          assert (N10 : r <> mword_of_int 10)
            by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          rewrite /X2 upd_ne; [| congruence]. apply HthrD1; assumption.
        - reflexivity.
        - reflexivity.
        - exact Hszmax.
        - exact Hbel.
        - left. split; [reflexivity | split; reflexivity]. }
      (* SUCCESS: the map gained the run, and a0 is the NEW size *)
      iDestruct "Hpost" as (P') "(%Hext & %Hdom & %Hleaf & %Hret & Hpt)".
      assert (Hret' : mr !!! Regidx Ra0 = add_vec (pv_sz V) nv).
      { destruct Hret as [[Hlt _] | [_ Hr]]; [| exact Hr].
        exfalso. rewrite !uint_unsigned in Hlt.
        exact (gp_z_lt_le_absurd _ _ Hlt Hlesz). }
      assert (Hnzero : eq_vec (D1 !!! Regidx Ra0) (zero_reg : mword 64) = false).
      { destruct (eq_vec (D1 !!! Regidx Ra0) (zero_reg : mword 64)) eqn:He;
          [exfalso | reflexivity].
        apply eq_vec_true_iff in He. rewrite HD1a0 Hret' in He.
        assert (Hzu : bv_unsigned (add_vec (pv_sz V) nv) = bv_unsigned (zero_reg : mword 64))
          by (rewrite He; reflexivity).
        assert (Hz0 : bv_unsigned (zero_reg : mword 64) = 0%Z) by (vm_compute; reflexivity).
        rewrite Hz0 Hnewu in Hzu.
        exact (gp_z_sum_pos_ne0 _ _ Hsz0 Hnpos Hzu). }
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.growproc + 0x34))
                (mword_of_int 21 : mword 8) (Cregidx (mword_of_int 2)) Ra0 D1 (av - 4)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rgne; exact Hnzero)
                with "Hcg Hpc Hi34").
      iIntros (CID23 Hn23) "Hcg Hpc".
      assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.growproc + 0x34) : mword 64) 2
                      = mword_of_int (KernelSyms.growproc + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp36) in "Hpc".
      (* ---- +0x36: the store, then the epilogue ---- *)
      iApply (gp_store D1 av p (pv_sz V) (add_vec (pv_sz V) nv) b
                ltac:(rewrite HD1a1; exact Hret') HD1s2
                with "Hcg Htext Hpc Hszc").
      iIntros (CID24 Hn24 Ms') "%Hs'a0 %Hs'thr Hcg Hpc Hszc".
      iDestruct (cpu_own_transport CID21 CID24 0%nat eb p b ltac:(wp_next_chain)
                   with "Hcpu") as "Hcpu".
      iApply ("EXIT" $! CID24 Ms' P' (add_vec (pv_sz V) nv) (mword_of_int 0 : mword 64)
                with "[%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hcpu Hpc Hszc Hptc Hpt Hs1 Hs2 Hs3 Hs4").
      - wp_next_chain.
      - rewrite (Hs'thr csp_rs1 ltac:(reg_neq)). exact HD1sp.
      - exact Hs'a0.
      - intros r Hr Ncsp N8 N9 N18.
        assert (N10 : r <> mword_of_int 10)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite (Hs'thr r ltac:(congruence)). apply HthrD1; assumption.
      - exact (proj1 Hext).
      - exact (proj1 (proj2 Hext)).
      - rewrite uint_unsigned uvm_maxsz_val. exact Hnewle.
      - apply (um_below_grow (pv_sz V) (add_vec (pv_sz V) nv) (ud_um (pv_upt V)));
          [exact Hbel | exact Hlesz | rewrite uvm_maxsz_val; exact Hnewle | exact Hdom].
      - right. left.
        split; [reflexivity |].
        split; [exact Hnpos |].
        split; [rewrite uint_unsigned uvm_maxsz_val; exact Hnewle |].
        split; [reflexivity |].
        split; [exact Hext | exact Hdom]. }
    (* =============== n <= 0 =============== *)
    assert (Htgt48 : add_vec (mword_of_int (KernelSyms.growproc + 0x16) : mword 64)
                       (sign_extend' 64 (mword_of_int 50 : mword 13))
                     = mword_of_int (KernelSyms.growproc + 0x48))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_bge_x0_taken_s_sconf (mword_of_int (KernelSyms.growproc + 0x16))
              (mword_of_int 50 : mword 13) Rs1 A2 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rgne; exact Hblez)
              ltac:(rewrite Htgt48; vm_compute; reflexivity)
              with "Hcg Hpc Hi16").
    iApply bi.later_intro. iIntros (CID12 Hn12) "Hcg Hpc".
    iEval (rewrite Htgt48) in "Hpc".
    assert (Hnle : (sint nv <= 0)%Z).
    { rewrite HA2s1 in Hblez. unfold zopz0zKzJ_s in Hblez.
      assert (Hz0 : sint (zero_reg : mword 64) = 0%Z) by reflexivity.
      rewrite Hz0 in Hblez. apply Z.geb_le in Hblez. lia. }
    (* ---- +0x48: bge s1,x0 -- is n exactly 0? ---- *)
    destruct (zopz0zKzJ_s (A2 !!! Regidx Rs1) (zero_reg : mword 64)) eqn:Hbgez.
    { (* n = 0: store [sz] back over itself and return 0 *)
      assert (Hn0 : sint nv = 0%Z).
      { rewrite HA2s1 in Hbgez. unfold zopz0zKzJ_s in Hbgez.
        assert (Hz0 : sint (zero_reg : mword 64) = 0%Z) by reflexivity.
        rewrite Hz0 in Hbgez. apply Z.geb_le in Hbgez. lia. }
      assert (Htgt36 : add_vec (mword_of_int (KernelSyms.growproc + 0x48) : mword 64)
                         (sign_extend' 64 (mword_of_int 8174 : mword 13))
                       = mword_of_int (KernelSyms.growproc + 0x36))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_bgez_taken_s_sconf (mword_of_int (KernelSyms.growproc + 0x48))
                (mword_of_int 8174 : mword 13) Rs1 A2 (av - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(rgne; exact Hbgez)
                ltac:(rewrite Htgt36; vm_compute; reflexivity)
                with "Hcg Hpc Hi48").
      iApply bi.later_intro. iIntros (CID13 Hn13) "Hcg Hpc".
      iEval (rewrite Htgt36) in "Hpc".
      iApply (gp_store A2 av p (pv_sz V) (pv_sz V) b HA2a1 HA2s2
                with "Hcg Htext Hpc Hszc").
      iIntros (CID14 Hn14 Ms') "%Hs'a0 %Hs'thr Hcg Hpc Hszc".
      iDestruct (cpu_own_transport CID9 CID14 0%nat eb p b ltac:(wp_next_chain)
                   with "Hcpu") as "Hcpu".
      iApply ("EXIT" $! CID14 Ms' (pv_upt V) (pv_sz V) (mword_of_int 0 : mword 64)
                with "[%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hcpu Hpc Hszc Hptc Hpt Hs1 Hs2 Hs3 Hs4").
      - wp_next_chain.
      - rewrite (Hs'thr csp_rs1 ltac:(reg_neq)). exact HA2sp.
      - exact Hs'a0.
      - intros r Hr Ncsp N8 N9 N18.
        assert (N10 : r <> mword_of_int 10)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite (Hs'thr r ltac:(congruence)). apply HthrA2; assumption.
      - reflexivity.
      - reflexivity.
      - exact Hszmax.
      - exact Hbel.
      - right. right. left.
        split; [reflexivity | split; [exact Hn0 | split; reflexivity]]. }
    (* ---- n < 0: shrink through uvmdealloc ---- *)
    assert (Hnneg : (sint nv < 0)%Z).
    { rewrite HA2s1 in Hbgez. unfold zopz0zKzJ_s in Hbgez.
      assert (Hz0 : sint (zero_reg : mword 64) = 0%Z) by reflexivity.
      rewrite Hz0 Z.geb_leb in Hbgez. apply Z.leb_gt in Hbgez. lia. }
    iApply (wp_bgez_fall_s_sconf (mword_of_int (KernelSyms.growproc + 0x48))
              (mword_of_int 8174 : mword 13) Rs1 A2 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rgne; exact Hbgez)
              with "Hcg Hpc Hi48").
    iIntros (CID13 Hn13) "Hcg Hpc".
    assert (Hpp4c : add_vec_int (mword_of_int (KernelSyms.growproc + 0x48) : mword 64) 4
                    = mword_of_int (KernelSyms.growproc + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4c) in "Hpc".
    (* ---- +0x4c: add a2,s1,a1 ---- *)
    iApply (wp_add_s_sconf (mword_of_int (KernelSyms.growproc + 0x4c))
              Ra2 Rs1 Ra1 (add_vec (pv_sz V) nv) A2 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rgne; rewrite HA2s1 HA2a1; apply add_vec64_comm)
              with "Hcg Hpc Hi4c").
    iIntros (CID14 Hn14) "Hcg Hpc".
    set (E1 := <[Regidx Ra2 := regval_into_reg (add_vec (pv_sz V) nv)]> A2).
    change (<[Regidx Ra2 := regval_into_reg (add_vec (pv_sz V) nv)]> A2) with E1.
    assert (Hpp50 : add_vec_int (mword_of_int (KernelSyms.growproc + 0x4c) : mword 64) 4
                    = mword_of_int (KernelSyms.growproc + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp50) in "Hpc".
    (* ---- +0x50: c.ld a0,80(a0) -- a0 STILL holds p on this path ---- *)
    assert (HE1a0 : E1 !!! Regidx Ra0 = p) by (rewrite /E1 upd_ne; [exact HA2a0 | reg_neq]).
    assert (Hpta2 : add_vec (E1 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 80 : mword 12))
                    = p_pagetable p) by (rewrite HE1a0; reflexivity).
    iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.growproc + 0x50)) Ra0 Ra0
              (mword_of_int 80 : mword 12) E1 (av - 4)%nat (page_base (ud_root (pv_upt V))) b
              (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi50 [Hptc]").
    { iEval (rgne; rewrite Hpta2). iExact "Hptc". }
    iIntros (CID15 Hn15) "Hcg Hpc Hptc".
    iEval (rgne; rewrite Hpta2) in "Hptc".
    set (E2 := <[Regidx Ra0 := regval_into_reg (page_base (ud_root (pv_upt V)))]> E1).
    change (<[Regidx Ra0 := regval_into_reg (page_base (ud_root (pv_upt V)))]> E1) with E2.
    assert (Hpp52 : add_vec_int (mword_of_int (KernelSyms.growproc + 0x50) : mword 64) 2
                    = mword_of_int (KernelSyms.growproc + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp52) in "Hpc".
    (* ---- +0x52: jal ra,uvmdealloc ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.growproc + 0x52))
              Rra (mword_of_int 2094594 : mword 21) E2 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi52").
    iIntros (CID16 Hn16) "Hcg Hpc".
    set (E3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.growproc + 0x52) : mword 64) 4)]> E2).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.growproc + 0x52) : mword 64) 4)]> E2) with E3.
    assert (Hjmpud : add_vec (mword_of_int (KernelSyms.growproc + 0x52) : mword 64)
                       (sign_extend' 64 (mword_of_int 2094594 : mword 21))
                     = mword_of_int KernelSyms.uvmdealloc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmpud) in "Hpc".
    assert (HE3a0 : E3 !!! Regidx Ra0 = page_base (ud_root (pv_upt V))).
    { rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_eq. reflexivity. }
    assert (HE3a1 : E3 !!! Regidx Ra1 = pv_sz V).
    { rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq].
      rewrite /E1 upd_ne; [| reg_neq]. exact HA2a1. }
    assert (HE3a2 : E3 !!! Regidx Ra2 = add_vec (pv_sz V) nv).
    { rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq].
      rewrite /E1 upd_eq. reflexivity. }
    assert (HE3sp : E3 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq].
      rewrite /E1 upd_ne; [| reg_neq]. exact HA2sp. }
    assert (HE3s2 : E3 !!! Regidx Rs2 = p).
    { rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq].
      rewrite /E1 upd_ne; [| reg_neq]. exact HA2s2. }
    assert (HE3ra : E3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.growproc + 0x52) : mword 64) 4)
      by (rewrite /E3 upd_eq; reflexivity).
    assert (HthrE3 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> E3 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N12 : r <> mword_of_int 12)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /E3 upd_ne; [| congruence]. rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence]. apply HthrA2; assumption. }
    iDestruct (cpu_own_transport CID9 CID16 0%nat eb p b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (Uvmdealloc.wp_uvmdealloc_sconf γa E3 (pv_upt V) (av - 4)%nat eb p b lks
              ltac:(lia) HE3a0
              ltac:(rewrite HE3a1; exact Hszmax)
              with "Hcg Hcpu Htext Hpc Hpt Henv").
    all: try lkbelow.
    iIntros (CID17 Hn17 md) "Hcg Hcpu Hpc %Hcsd %Hdret Hpt".
    rewrite HE3a1 HE3a2 in Hdret.
    iEval (rewrite HE3a1 HE3a2) in "Hpt".
    assert (Hpc56 : ret_pc (E3 !!! Regidx Rra) = mword_of_int (KernelSyms.growproc + 0x56))
      by (rewrite HE3ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc56) in "Hpc".
    assert (Hmdsp : md !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite (callee_saved_lookup Hcsd csp_rs1 ltac:(vm_compute; reflexivity)); exact HE3sp).
    assert (Hmds2 : md !!! Regidx Rs2 = p)
      by (rewrite (callee_saved_lookup Hcsd (mword_of_int 18) ltac:(vm_compute; reflexivity)); exact HE3s2).
    assert (Hthrmd : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> md !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      rewrite (callee_saved_lookup Hcsd r Hr). apply HthrE3; assumption. }
    (* ---- +0x56: c.mv a1,a0 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.growproc + 0x56))
              Ra1 Ra0 md (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi56").
    iIntros (CID18 Hn18) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (F2 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (md !!! Regidx Ra0))]> md).
    change (<[Regidx Ra1 := regval_into_reg (add_vec zero_reg (md !!! Regidx Ra0))]> md) with F2.
    assert (Hpp58 : add_vec_int (mword_of_int (KernelSyms.growproc + 0x56) : mword 64) 2
                    = mword_of_int (KernelSyms.growproc + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp58) in "Hpc".
    assert (HF2a1 : F2 !!! Regidx Ra1 = md !!! Regidx Ra0)
      by (rewrite /F2 upd_eq; apply add_vec_zero_l).
    assert (HF2s2 : F2 !!! Regidx Rs2 = p)
      by (rewrite /F2 upd_ne; [exact Hmds2 | reg_neq]).
    assert (HF2sp : F2 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /F2 upd_ne; [exact Hmdsp | reg_neq]).
    assert (HthrF2 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> F2 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      assert (N11 : r <> mword_of_int 11)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /F2 upd_ne; [| congruence]. apply Hthrmd; assumption. }
    (* ---- +0x58: c.j -0x22, into the store ---- *)
    assert (Htgt362 : add_vec (mword_of_int (KernelSyms.growproc + 0x58) : mword 64)
                        (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2031 : mword 11) ('b"0"))))
                      = mword_of_int (KernelSyms.growproc + 0x36))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.growproc + 0x58))
              (sign_extend' 21 (concat_vec (mword_of_int 2031 : mword 11) ('b"0"))) F2 (av - 4)%nat b
              ltac:(rewrite Htgt362; vm_compute; reflexivity)
              with "Hcg Hpc Hi58").
    iIntros (CID19 Hn19). iApply bi.later_intro. iIntros "Hcg Hpc".
    iEval (rewrite Htgt362) in "Hpc".
    (* what the new size is, and that it still bounds the map *)
    assert (Hszb' : (uint (md !!! Regidx Ra0) <= uvm_maxsz)%Z).
    { destruct Hdret as [[_ Hr] | [Hlt Hr]]; rewrite Hr; [exact Hszmax |].
      rewrite uint_unsigned. rewrite !uint_unsigned in Hlt.
      rewrite uvm_maxsz_val. lia. }
    assert (Hbel' : um_below (md !!! Regidx Ra0)
              (ud_um (uptd_del_run (pv_upt V) (svpn_of (pgroundup (add_vec (pv_sz V) nv)))
                        (uvmd_np (pv_sz V) (add_vec (pv_sz V) nv))))).
    { unfold uptd_del_run. cbn [ud_um].
      destruct Hdret as [[Hge Hr] | [Hlt Hr]]; rewrite Hr.
      - rewrite !uint_unsigned in Hge.
        rewrite (uvmd_np_ge (pv_sz V) (add_vec (pv_sz V) nv) ltac:(lia)).
        cbn [um_del_run]. exact Hbel.
      - rewrite !uint_unsigned in Hlt.
        apply (um_below_shrink (pv_sz V) (add_vec (pv_sz V) nv) (ud_um (pv_upt V)) Hbel Hlt).
        rewrite uvm_maxsz_val. exact Hszmaxz. }
    iApply (gp_store F2 av p (pv_sz V) (md !!! Regidx Ra0) b HF2a1 HF2s2
              with "Hcg Htext Hpc Hszc").
    iIntros (CID20 Hn20 Ms') "%Hs'a0 %Hs'thr Hcg Hpc Hszc".
    iDestruct (cpu_own_transport CID17 CID20 0%nat eb p b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply ("EXIT" $! CID20 Ms'
              (uptd_del_run (pv_upt V) (svpn_of (pgroundup (add_vec (pv_sz V) nv)))
                 (uvmd_np (pv_sz V) (add_vec (pv_sz V) nv)))
              (md !!! Regidx Ra0) (mword_of_int 0 : mword 64)
              with "[%] [%] [%] [%] [%] [%] [%] [%] [%] Hcg Hcpu Hpc Hszc Hptc Hpt Hs1 Hs2 Hs3 Hs4").
    - wp_next_chain.
    - rewrite (Hs'thr csp_rs1 ltac:(reg_neq)). exact HF2sp.
    - exact Hs'a0.
    - intros r Hr Ncsp N8 N9 N18.
      assert (N10 : r <> mword_of_int 10)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite (Hs'thr r ltac:(congruence)). apply HthrF2; assumption.
    - reflexivity.
    - reflexivity.
    - exact Hszb'.
    - exact Hbel'.
    - right. right. right.
      split; [reflexivity |].
      split; [exact Hnneg |].
      split; [reflexivity |].
      destruct Hdret as [[Hge Hr] | [Hlt Hr]]; rewrite Hr.
      + right. split; [lia | reflexivity].
      + left. split; [exact Hlt | reflexivity].
  Qed.

End ProofGrowproc.

End GrowprocProof.
