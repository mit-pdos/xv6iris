(* ProofSysDupAUTail.v -- sys_dup's shared epilogue and its stack-bound
   reading, as FREE-STANDING lemmas the atomic-update walk can call.

   WHY THIS FILE EXISTS.  The reuse rule (durable-notes: "a block lemma that
   names its syscall's postcondition cannot be reused by a parallel proof;
   one that takes an abstract continuation can") applies to sys_dup's tail
   word for word -- [ProofSysDup]'s [sd_tail] concludes with [wp_next ...
   (fun CIDx => forall mf, ... -* WP Loop)] promising registers, pc and
   nothing about [sys_dup_post], so the AU walk can use it verbatim.  The
   one obstacle is VISIBILITY, not shape: [sd_tail] and [sd_sp_bounds] sit
   inside [SysDupProof], which is sealed by [: SYSDUP], so only
   [wp_sys_dup_sconf] leaves that module.  R10 forbids moving the landed
   statement, so the two helpers are restated here, OUTSIDE any functor --
   same statements, same proofs, no module parameters (neither helper
   mentions argfd, fdalloc or filedup) -- and both walks' epilogues are
   this one lemma's two readings.

   The PURE side conditions the walk also wants ([sd_addr_f],
   [sd_addr_f_base], [sd_fd_nonneg], [sd_fd_range], [sd_m1_neg],
   [sd_zero_nonneg]) are already top-level in [ProofSysDup.v] -- outside its
   module -- so they are imported rather than restated.

   Contract of the walk that uses these: SpecSysDupAU.v.  Decode:
   CodeSysDup.v.  Walk: ProofSysDupAU.v. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import VcGen.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl WpSmodeIntr.
Require Import StackOwn.
Require Import ProcGeom CpuOwn.
Require Import FdSlots ProcInv.
Require Import FileInvDefs.
Require Import SpecArgfd SpecFdalloc SpecSysDup.
Require Import KernelRvcDecode.
Require Import CodeSysDup.
Require Import ProofSysDup.   (* the landed walk: its TOP-LEVEL pure side
                                 conditions ([sd_addr_f] and friends) are
                                 outside the sealed functor *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Local Open Scope Z_scope.


Section ProofSysDupAUTail.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation Rra  := (mword_of_int 1  : mword 5).
  Notation Rs0  := (mword_of_int 8  : mword 5).
  Notation Rs1  := (mword_of_int 9  : mword 5).
  Notation Rs2  := (mword_of_int 18 : mword 5).
  Notation Ra0  := (mword_of_int 10 : mword 5).
  Notation Ra1  := (mword_of_int 11 : mword 5).
  Notation Ra2  := (mword_of_int 12 : mword 5).
  Notation Ra5  := (mword_of_int 15 : mword 5).

  (* the current sp's bounds, out of the stack capability.  THE CARVE THIS
     READS IS ARM-DEPENDENT, hence the [0 < k] premise -- [ProofSysDup]'s
     [sd_sp_bounds]' note verbatim. *)
  Lemma sda_sp_bounds `{CID0 : CpuId} (mm : regfile) (k : nat)
      (bb : bool) (pp : mword 64) :
    (0 < k)%nat ->
    sie_cap_gpr KT1 mm k bb pp -∗
    ⌜(8 <= uint (mm !!! Regidx csp_rs1) < 274877906944 + 8)%Z⌝.
  Proof.
    iIntros (Hk) "(_ & _ & (Hstk & _ & _) & _)".
    iApply (stack_own_sp_bounds (KTR := KT1) _ (trap_res bb + k)%nat with "Hstk").
    destruct bb; unfold trap_res; lia.
  Qed.

  (* =================================================================== *)
  (*  The shared tail at +0x3c, entered by all THREE arms.                *)
  (* =================================================================== *)
  (* Only ra and s0 are popped here: s1/s2 are handled by whichever arm got
     here (restored, or never touched), which is why they arrive already in
     agreement with [m] and why slots 3..6 are arbitrary.

     ABSTRACT CONTINUATION: the exit promises registers, pc and nothing
     about any postcondition, which is exactly what lets both the landed
     walk and the AU walk end here. *)
  Lemma sda_tail `{CID0 : CpuId}
      (m Mt : regfile) (av : nat) (rv : mword 64)
      (sp0 ra0 s00 : mword 64) (w3 w4 w5 w6 : bv 64)
      (p : mword 64) (b : bool) :
    (6 <= av)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 6 ->
    Mt !!! Regidx Ra5 = rv ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
        Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr KT1 Mt (av - 6)%nat b p -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.sys_dup + 0x3c) : mword 64) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 3) (DfracOwn 1) w3 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 4) (DfracOwn 1) w4 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 5) (DfracOwn 1) w5 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 6) (DfracOwn 1) w6 -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf /\ mf !!! Regidx Ra0 = rv⌝ -∗
        sie_cap_gpr KT1 mf av b p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hav Hsp0 Hra0 Hs00 Hmtsp Hmta5 Hthr.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hcont".
    (* ---- +0x3c: c.mv a0,a5 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x3c)) Ra0 Ra5 Mt (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (sdi_3c with "Htext"). }
    iIntros (CIDt0 Hkt0) "Hcg Hpc".
    set (T0 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (Mt !!! Regidx Ra5))]> Mt).
    change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (Mt !!! Regidx Ra5))]> Mt) with T0.
    assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x3c) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_dup + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3e) in "Hpc".
    assert (HT0a0 : T0 !!! Regidx Ra0 = rv).
    { rewrite /T0 upd_eq Hmta5. apply add_vec_zero_l. }
    assert (HT0sp : T0 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T0 upd_ne; [exact Hmtsp | vm_compute; discriminate]).
    (* ---- +0x3e: c.ldsp ra,40(sp) ---- *)
    assert (Hpa1 : add_vec (T0 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HT0sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x3e))
              (mword_of_int 5 : mword 6) Rra T0 (av - 6)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hb1").
    { iApply (sdi_3e with "Htext"). }
    iIntros (CIDt1 Hkt1) "Hcg Hpc Hb1".
    iEval (rewrite Hpa1) in "Hb1".
    set (T1 := <[Regidx Rra := regval_into_reg ra0]> T0).
    change (<[Regidx Rra := regval_into_reg ra0]> T0) with T1.
    assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x3e) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_dup + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp40) in "Hpc".
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T1 upd_ne; [exact HT0sp | vm_compute; discriminate]).
    (* ---- +0x40: c.ldsp s0,32(sp) ---- *)
    assert (Hpa2 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HT1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x40))
              (mword_of_int 4 : mword 6) Rs0 T1 (av - 6)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hb2").
    { iApply (sdi_40 with "Htext"). }
    iIntros (CIDt2 Hkt2) "Hcg Hpc Hb2".
    iEval (rewrite Hpa2) in "Hb2".
    set (T2 := <[Regidx Rs0 := regval_into_reg s00]> T1).
    change (<[Regidx Rs0 := regval_into_reg s00]> T1) with T2.
    assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x40) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_dup + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp42) in "Hpc".
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T2 upd_ne; [exact HT1sp | vm_compute; discriminate]).
    (* ---- +0x42: c.addi16sp sp,48 (frame pop) ---- *)
    assert (Hwv : add_vec (T2 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0)
      by (rewrite HT2sp; apply stk_pop_48).
    assert (Hpop : T2 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T2 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6)
      by (rewrite Hwv; exact HT2sp).
    assert (E5 : pa_stk (pa_stk sp0 4) 1 = pa_stk sp0 5) by (rewrite pa_stk_assoc; reflexivity).
    assert (E6 : pa_stk (pa_stk sp0 4) 2 = pa_stk sp0 6) by (rewrite pa_stk_assoc; reflexivity).
    iEval (rewrite -E5) in "Hb5".
    iEval (rewrite -E6) in "Hb6".
    iDestruct (stack_own_4_intro sp0 ra0 s00 w3 w4 with "Hb1 Hb2 Hb3 Hb4") as "Hf14".
    iDestruct (stack_own_2_intro (pa_stk sp0 4) w5 w6 with "Hb5 Hb6") as "Hf56".
    iAssert (stack_own (KTR := KT1) sp0 6) with "[Hf14 Hf56]" as "Hframe".
    { rewrite (stack_own_split (KTR := KT1) sp0 4 6 ltac:(lia)). change (6 - 4)%nat with 2%nat. iFrame. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x42))
              (mword_of_int 3 : mword 6) T2 (av - 6)%nat 6 b Hpop
              with "Hcg Hpc [] Hframe").
    { iApply (sdi_42 with "Htext"). }
    iIntros (CIDt3 Hkt3) "Hcg Hpc".
    assert (Hnk : ((av - 6) + 6)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.sys_dup + 0x42) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_dup + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp44) in "Hpc".
    set (T3 := <[Regidx csp_rs1 := regval_into_reg (add_vec (T2 !!! Regidx csp_rs1)
                  (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> T2).
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (T2 !!! Regidx csp_rs1)
              (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> T2) with T3.
    (* ---- +0x44: c.ret ---- *)
    assert (HT3ra : T3 !!! Regidx Rra = ra0).
    { rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.sys_dup + 0x44)) Rra T3 av b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc []").
    { iApply (sdi_44 with "Htext"). }
    iIntros (CIDt4 Hkt4) "Hcg Hpc".
    iEval (rewrite (rget_ne (CID := CIDt3) T3 Rra ltac:(vm_compute; discriminate))) in "Hpc".
    iEval (rewrite HT3ra) in "Hpc".
    (* ---- the postcondition ---- *)
    assert (HT3sp : T3 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite /T3 upd_eq Hwv; symmetry; exact Hsp0).
    assert (HT3s0 : T3 !!! Regidx Rs0 = m !!! Regidx Rs0).
    { rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_eq. symmetry; exact Hs00. }
    assert (HT3a0 : T3 !!! Regidx Ra0 = rv).
    { rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1 upd_ne; [| vm_compute; discriminate]. exact HT0a0. }
    assert (Hthr3 : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> T3 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /T3 upd_ne; [| congruence].
      rewrite /T2 upd_ne; [| congruence].
      rewrite /T1 upd_ne; [| congruence].
      rewrite /T0 upd_ne; [| congruence].
      apply Hthr; assumption. }
    iSpecialize ("Hcont" $! CIDt4 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! T3 with "[%] Hcg Hpc").
    split; [| exact HT3a0].
    unfold callee_saved.
    split; [exact HT3sp|].
    split; [exact HT3s0|].
    split; [apply Hthr3; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr3; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr3; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr3; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr3; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr3; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr3; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr3; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr3; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr3; vm_compute; first [reflexivity | discriminate]|].
    apply Hthr3; vm_compute; first [reflexivity | discriminate].
  Qed.

End ProofSysDupAUTail.
