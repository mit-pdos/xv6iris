(* ProofFetchstr.v -- the whole-function WP for xv6's fetchstr().

     int fetchstr(uint64 addr, char *buf, int max) {
       struct proc *p = myproc();
       if (copyinstr(p->pagetable, buf, addr, max) < 0)
         return -1;
       return strlen(buf);
     }

   Thirty-two instructions, a 48-byte (6-slot) frame with five slots used,
   two arms joining at the epilogue (+0x2e).  The contract is SpecFetchstr.v.

   THE STRUCTURAL IDEA, as in ProofFetchaddr: the body is ONE borrow out of
   [proc_priv].  [ProcInv.proc_priv_copy] is taken right after myproc returns
   and closed on both arms -- but here it closes at [P' := pv_upt V] on BOTH,
   because copyinstr does not fault pages in, so the descriptor never moves.
   [fs_upd_upt_id] is the record-eta step that turns [upd_upt V (pv_upt V)]
   back into [V], which is what lets the contract say [proc_priv γf p pid V]
   with no [upd_upt] wrapper at all.

   THREE THINGS WORTH KEEPING.

   1. THE TWO CALLEES' VOCABULARIES ALREADY AGREE.  copyinstr hands back
      [∃ k, k < max /\ bb_cstr new k]; strlen takes exactly [k < n] and
      [bb_cstr f k] and answers [k].  So the success arm is a [destruct] of
      copyinstr's postcondition followed by passing its two components
      straight into strlen -- there is no intermediate lemma, and the buffer
      resource is handed over unsplit (SpecStrlen.v's "the buffer may be
      longer than the string" is what makes that possible).

   2. THE BRANCH IS DECIDED BY THE CALLEE'S POSTCONDITION, not by a case
      split on a register.  [copyinstr_ret] says the answer is 0 or -1, so
      [destruct]ing it FIRST makes the [bltz a0] condition a closed literal
      in each arm and [vm_compute] settles it -- the same discipline
      ProofFetchaddr uses for [snez]/[negw].

   3. BOTH ENDS OF THE FRAME ARE [c.addi16sp].  Unlike fetchaddr (whose push
      is a plain [c.addi]), fetchstr's 48-byte frame is pushed and popped by
      the same encoding, so [wp_caddi16sp_push_s_sconf] /
      [wp_caddi16sp_pop_s_sconf] pair up directly.  The sixth slot is never
      written; it is carried through the proof as an anonymous cell. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved KernelText.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl WpSmodeIntr.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import FdSlots ProcInv.
Require Import FileInvDefs.
Require Import CodeFetchstr.
Require Import SpecMyproc SpecCopyinstr SpecStrlen.
Require Import SpecFetchstr.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.


(* [max < 2^31] is what the caller supplies; copyinstr wants [< 2^64] and
   strlen [< 2^31] of the ANSWER.  [lia] cannot evaluate the powers. *)
Lemma fs_z_31_64 (z : Z) : (0 <= z)%Z -> (z < 2 ^ 31)%Z -> (z < 2 ^ 64)%Z.
Proof.
  intros H0 H31.
  assert (E31 : (2 ^ 31)%Z = 2147483648%Z) by (vm_compute; reflexivity).
  assert (E64 : (2 ^ 64)%Z = 18446744073709551616%Z) by (vm_compute; reflexivity).
  rewrite E31 in H31. rewrite E64. lia.
Qed.

Lemma fs_z_lt_of_nat_lt (k maxn : Z) : (k < maxn)%Z -> (maxn < 2 ^ 31)%Z -> (k < 2 ^ 31)%Z.
Proof. lia. Qed.

(* writing back the descriptor that was borrowed is a no-op on [pprivate] --
   the record-eta step [ProcInv.upd_ofile_id] performs for the fd slots. *)
Lemma fs_upd_upt_id (V : pprivate) : upd_upt V (pv_upt V) = V.
Proof. unfold upd_upt. by destruct V. Qed.

Module FetchstrProof (Myproc : MYPROC) (Copyinstr : COPYINSTR) (Strlen : STRLEN) : FETCHSTR.

Section ProofFetchstr.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rtp := (mword_of_int 4 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).

  (* =================================================================== *)
  (*  The shared tail at +0x2e: the epilogue, entered by both arms.       *)
  (*  DECOMPOSED HELPER: its own fresh [CID0], shadowing the Section's own *)
  (*  [CID], a [b] parameter, and its trailing continuation wrapped in     *)
  (*  [wp_next b] -- see the porting guide's decomposed-helper recipe.     *)
  (* =================================================================== *)
  Lemma fs_tail `{CID0 : CpuId}
      (m Mt : regfile) (av : nat) (rv : mword 64)
      (sp0 ra0 s00 s10 s20 s30 gap : mword 64) (p : mword 64) (b : bool) :
    (6 <= av)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs2 = s20 ->
    m !!! Regidx Rs3 = s30 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 6 ->
    Mt !!! Regidx Ra0 = rv ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 ->
        Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr Mt (av - 6)%nat b p -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.fetchstr + 0x2e) : mword 64) -∗
    word_pointsto (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (pa_stk sp0 3) (DfracOwn 1) s10 -∗
    word_pointsto (pa_stk sp0 4) (DfracOwn 1) s20 -∗
    word_pointsto (pa_stk sp0 5) (DfracOwn 1) s30 -∗
    word_pointsto (pa_stk sp0 6) (DfracOwn 1) gap -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf /\ mf !!! Regidx Ra0 = rv⌝ -∗
        sie_cap_gpr mf av b p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hav Hsp0 Hra0 Hs00 Hs10 Hs20 Hs30 Hmtsp Hmta0 Hthr.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hcont".
    iPoseProof (fsi_2e with "Htext") as "Hi2e".
    iPoseProof (fsi_30 with "Htext") as "Hi30".
    iPoseProof (fsi_32 with "Htext") as "Hi32".
    iPoseProof (fsi_34 with "Htext") as "Hi34".
    iPoseProof (fsi_36 with "Htext") as "Hi36".
    iPoseProof (fsi_38 with "Htext") as "Hi38".
    iPoseProof (fsi_3a with "Htext") as "Hi3a".
    (* ---- +0x2e: c.ldsp ra,40(sp) ---- *)
    assert (Hpa1 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hmtsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x2e))
              (mword_of_int 5 : mword 6) Rra Mt (av - 6)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2e Hb1 [-]").
    iIntros (CID1 Hk1) "Hcg Hpc Hb1".
    iEval (rewrite Hpa1) in "Hb1".
    set (T1 := <[Regidx Rra := regval_into_reg ra0]> Mt).
    change (<[Regidx Rra := regval_into_reg ra0]> Mt) with T1.
    assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x2e) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchstr + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T1 upd_ne; [exact Hmtsp | reg_neq]).
    (* ---- +0x30: c.ldsp s0,32(sp) ---- *)
    assert (Hpa2 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HT1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x30))
              (mword_of_int 4 : mword 6) Rs0 T1 (av - 6)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi30 Hb2 [-]").
    iIntros (CID2 Hk2) "Hcg Hpc Hb2".
    iEval (rewrite Hpa2) in "Hb2".
    set (T2 := <[Regidx Rs0 := regval_into_reg s00]> T1).
    change (<[Regidx Rs0 := regval_into_reg s00]> T1) with T2.
    assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x30) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchstr + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T2 upd_ne; [exact HT1sp | reg_neq]).
    (* ---- +0x32: c.ldsp s1,24(sp) ---- *)
    assert (Hpa3 : add_vec (T2 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HT2sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa3) in "Hb3".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x32))
              (mword_of_int 3 : mword 6) Rs1 T2 (av - 6)%nat s10 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi32 Hb3 [-]").
    iIntros (CID3 Hk3) "Hcg Hpc Hb3".
    iEval (rewrite Hpa3) in "Hb3".
    set (T3 := <[Regidx Rs1 := regval_into_reg s10]> T2).
    change (<[Regidx Rs1 := regval_into_reg s10]> T2) with T3.
    assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x32) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchstr + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp34) in "Hpc".
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T3 upd_ne; [exact HT2sp | reg_neq]).
    (* ---- +0x34: c.ldsp s2,16(sp) ---- *)
    assert (Hpa4 : add_vec (T3 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HT3sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa4) in "Hb4".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x34))
              (mword_of_int 2 : mword 6) Rs2 T3 (av - 6)%nat s20 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi34 Hb4 [-]").
    iIntros (CID4 Hk4) "Hcg Hpc Hb4".
    iEval (rewrite Hpa4) in "Hb4".
    set (T4 := <[Regidx Rs2 := regval_into_reg s20]> T3).
    change (<[Regidx Rs2 := regval_into_reg s20]> T3) with T4.
    assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x34) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchstr + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp36) in "Hpc".
    assert (HT4sp : T4 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T4 upd_ne; [exact HT3sp | reg_neq]).
    (* ---- +0x36: c.ldsp s3,8(sp) ---- *)
    assert (Hpa5 : add_vec (T4 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { rewrite HT4sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa5) in "Hb5".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x36))
              (mword_of_int 1 : mword 6) Rs3 T4 (av - 6)%nat s30 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi36 Hb5 [-]").
    iIntros (CID5 Hk5) "Hcg Hpc Hb5".
    iEval (rewrite Hpa5) in "Hb5".
    set (T5 := <[Regidx Rs3 := regval_into_reg s30]> T4).
    change (<[Regidx Rs3 := regval_into_reg s30]> T4) with T5.
    assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x36) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchstr + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp38) in "Hpc".
    assert (HT5sp : T5 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T5 upd_ne; [exact HT4sp | reg_neq]).
    (* ---- +0x38: c.addi16sp sp,48 (the frame pop) ---- *)
    assert (Hwv : add_vec (T5 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0)
      by (rewrite HT5sp; apply stk_pop_48).
    assert (Hpop : T5 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T5 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6)
      by (rewrite Hwv; exact HT5sp).
    iAssert (stack_own sp0 6) with "[Hb1 Hb2 Hb3 Hb4 Hb5 Hb6]" as "Hframe".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hb1"; [iExists _; iExact "Hb1"|].
      iSplitL "Hb2"; [iExists _; iExact "Hb2"|].
      iSplitL "Hb3"; [iExists _; iExact "Hb3"|].
      iSplitL "Hb4"; [iExists _; iExact "Hb4"|].
      iSplitL "Hb5"; [iExists _; iExact "Hb5"|].
      iSplitL "Hb6"; [iExists _; iExact "Hb6"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x38))
              (mword_of_int 3 : mword 6) T5 (av - 6)%nat 6 b Hpop
              with "Hcg Hpc Hi38 Hframe [-]").
    iIntros (CID6 Hk6) "Hcg Hpc".
    assert (Hnk : ((av - 6) + 6)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x38) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchstr + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3a) in "Hpc".
    set (T6 := <[Regidx csp_rs1 := regval_into_reg (add_vec (T5 !!! Regidx csp_rs1)
                  (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> T5).
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (T5 !!! Regidx csp_rs1)
              (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> T5) with T6.
    (* ---- +0x3a: c.ret ---- *)
    assert (HT6ra : T6 !!! Regidx Rra = ra0).
    { rewrite /T6 upd_ne; [| reg_neq].
      rewrite /T5 upd_ne; [| reg_neq].
      rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_ne; [| reg_neq].
      rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x3a))
              Rra T6 av b ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi3a [-]").
    iIntros (CID7 Hk7) "Hcg Hpc".
    iEval (rewrite (rget_ne (CID := CID6) T6 Rra ltac:(vm_compute; discriminate))) in "Hpc".
    iEval (rewrite HT6ra) in "Hpc".
    (* ---- the postcondition ---- *)
    assert (HT6sp : T6 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite /T6 upd_eq Hwv; symmetry; exact Hsp0).
    assert (HT6s0 : T6 !!! Regidx Rs0 = m !!! Regidx Rs0).
    { rewrite /T6 upd_ne; [| reg_neq].
      rewrite /T5 upd_ne; [| reg_neq].
      rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_ne; [| reg_neq].
      rewrite /T2 upd_eq. symmetry; exact Hs00. }
    assert (HT6s1 : T6 !!! Regidx Rs1 = m !!! Regidx Rs1).
    { rewrite /T6 upd_ne; [| reg_neq].
      rewrite /T5 upd_ne; [| reg_neq].
      rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_eq. symmetry; exact Hs10. }
    assert (HT6s2 : T6 !!! Regidx Rs2 = m !!! Regidx Rs2).
    { rewrite /T6 upd_ne; [| reg_neq].
      rewrite /T5 upd_ne; [| reg_neq].
      rewrite /T4 upd_eq. symmetry; exact Hs20. }
    assert (HT6s3 : T6 !!! Regidx Rs3 = m !!! Regidx Rs3).
    { rewrite /T6 upd_ne; [| reg_neq].
      rewrite /T5 upd_eq. symmetry; exact Hs30. }
    assert (HT6a0 : T6 !!! Regidx Ra0 = rv).
    { rewrite /T6 upd_ne; [| reg_neq].
      rewrite /T5 upd_ne; [| reg_neq].
      rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_ne; [| reg_neq].
      rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_ne; [| reg_neq]. exact Hmta0. }
    assert (Hthr6 : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 ->
              T6 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18 N19.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /T6 upd_ne; [| congruence].
      rewrite /T5 upd_ne; [| congruence].
      rewrite /T4 upd_ne; [| congruence].
      rewrite /T3 upd_ne; [| congruence].
      rewrite /T2 upd_ne; [| congruence].
      rewrite /T1 upd_ne; [| congruence].
      apply Hthr; assumption. }
    iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! T6 with "[%] Hcg Hpc").
    split; [| exact HT6a0].
    unfold callee_saved.
    split; [exact HT6sp|].
    split; [exact HT6s0|].
    split; [exact HT6s1|].
    split; [exact HT6s2|].
    split; [exact HT6s3|].
    split; [apply Hthr6; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr6; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr6; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr6; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr6; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr6; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr6; vm_compute; first [reflexivity | discriminate]|].
    apply Hthr6; vm_compute; first [reflexivity | discriminate].
  Qed.

  (* =================================================================== *)
  (*  THE CAPSTONE.                                                       *)
  (* =================================================================== *)
  Lemma wp_fetchstr_sconf (γf : gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (maxn : nat) (buf_olds : nat -> bv 8) (b : bool)
    : wp_fetchstr_sconf_body γf m av n eb p C pid V maxn buf_olds b.
  Proof.
    cbv beta delta [wp_fetchstr_sconf_body].
    intros pcE buf ret_tgt Hn Hav Hmax Hmax31.
    unfold fetchstr_stack in Hav.
    set (sp0 := m !!! Regidx csp_rs1).
    set (ra0 := m !!! Regidx Rra).
    set (s00 := m !!! Regidx Rs0).
    set (s10 := m !!! Regidx Rs1).
    set (s20 := m !!! Regidx Rs2).
    set (s30 := m !!! Regidx Rs3).
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    iIntros "Hcg Hcpu #Htext Hpc Hpriv Hbuf Hcont".
    iPoseProof (fsi_00 with "Htext") as "Hi00".
    iPoseProof (fsi_02 with "Htext") as "Hi02".
    iPoseProof (fsi_04 with "Htext") as "Hi04".
    iPoseProof (fsi_06 with "Htext") as "Hi06".
    iPoseProof (fsi_08 with "Htext") as "Hi08".
    iPoseProof (fsi_0a with "Htext") as "Hi0a".
    iPoseProof (fsi_0c with "Htext") as "Hi0c".
    iPoseProof (fsi_0e with "Htext") as "Hi0e".
    iPoseProof (fsi_10 with "Htext") as "Hi10".
    iPoseProof (fsi_12 with "Htext") as "Hi12".
    iPoseProof (fsi_14 with "Htext") as "Hi14".
    iPoseProof (fsi_18 with "Htext") as "Hi18".
    iPoseProof (fsi_1a with "Htext") as "Hi1a".
    iPoseProof (fsi_1c with "Htext") as "Hi1c".
    iPoseProof (fsi_1e with "Htext") as "Hi1e".
    iPoseProof (fsi_20 with "Htext") as "Hi20".
    iPoseProof (fsi_24 with "Htext") as "Hi24".
    iPoseProof (fsi_28 with "Htext") as "Hi28".
    iPoseProof (fsi_2a with "Htext") as "Hi2a".
    iPoseProof (fsi_3c with "Htext") as "Hi3c".
    iPoseProof (fsi_3e with "Htext") as "Hi3e".
    (* ---- +0x00: c.addi16sp sp,-48 (frame push) ---- *)
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 61 : mword 6) m av 6 b
              ltac:(lia) (stk_push_48 (m !!! Regidx csp_rs1))
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hk1) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
              (add_vec (m !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m) with M1.
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.fetchstr + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /M1 upd_eq; apply stk_push_48).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(C1 & C2 & C3 & C4 & C5 & C6 & _)".
    iDestruct "C1" as (u1) "Hs1".
    iDestruct "C2" as (u2) "Hs2".
    iDestruct "C3" as (u3) "Hs3".
    iDestruct "C4" as (u4) "Hs4".
    iDestruct "C5" as (u5) "Hs5".
    iDestruct "C6" as (u6) "Hs6".
    (* ---- +0x02 .. +0x0a: save ra / s0 / s1 / s2 / s3 ---- *)
    assert (Hpa1 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa2 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa3 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa4 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa5 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa1) in "Hs1".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x02))
              (mword_of_int 5 : mword 6) Rra M1 (av - 6)%nat u1 b
              with "Hcg Hpc Hi02 Hs1 [-]").
    iIntros (CID2 Hk2) "Hcg Hpc Hs1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchstr + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    iEval (rewrite -Hpa2) in "Hs2".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x04))
              (mword_of_int 4 : mword 6) Rs0 M1 (av - 6)%nat u2 b
              with "Hcg Hpc Hi04 Hs2 [-]").
    iIntros (CID3 Hk3) "Hcg Hpc Hs2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchstr + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    iEval (rewrite -Hpa3) in "Hs3".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x06))
              (mword_of_int 3 : mword 6) Rs1 M1 (av - 6)%nat u3 b
              with "Hcg Hpc Hi06 Hs3 [-]").
    iIntros (CID4 Hk4) "Hcg Hpc Hs3".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchstr + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    iEval (rewrite -Hpa4) in "Hs4".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x08))
              (mword_of_int 2 : mword 6) Rs2 M1 (av - 6)%nat u4 b
              with "Hcg Hpc Hi08 Hs4 [-]").
    iIntros (CID5 Hk5) "Hcg Hpc Hs4".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x08) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchstr + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    iEval (rewrite -Hpa5) in "Hs5".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x0a))
              (mword_of_int 1 : mword 6) Rs3 M1 (av - 6)%nat u5 b
              with "Hcg Hpc Hi0a Hs5 [-]").
    iIntros (CID6 Hk6) "Hcg Hpc Hs5".
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x0a) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchstr + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* name the five saved values *)
    assert (HM1ra : M1 !!! Regidx Rra = ra0)
      by (rewrite /M1 upd_ne; [reflexivity | reg_neq]).
    assert (HM1s0 : M1 !!! Regidx Rs0 = s00)
      by (rewrite /M1 upd_ne; [reflexivity | reg_neq]).
    assert (HM1s1 : M1 !!! Regidx Rs1 = s10)
      by (rewrite /M1 upd_ne; [reflexivity | reg_neq]).
    assert (HM1s2 : M1 !!! Regidx Rs2 = s20)
      by (rewrite /M1 upd_ne; [reflexivity | reg_neq]).
    assert (HM1s3 : M1 !!! Regidx Rs3 = s30)
      by (rewrite /M1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite (rget_ne (CID := CID1) M1 Rra ltac:(vm_compute; discriminate)) Hpa1 HM1ra) in "Hs1".
    iEval (rewrite (rget_ne (CID := CID2) M1 Rs0 ltac:(vm_compute; discriminate)) Hpa2 HM1s0) in "Hs2".
    iEval (rewrite (rget_ne (CID := CID3) M1 Rs1 ltac:(vm_compute; discriminate)) Hpa3 HM1s1) in "Hs3".
    iEval (rewrite (rget_ne (CID := CID4) M1 Rs2 ltac:(vm_compute; discriminate)) Hpa4 HM1s2) in "Hs4".
    iEval (rewrite (rget_ne (CID := CID5) M1 Rs3 ltac:(vm_compute; discriminate)) Hpa5 HM1s3) in "Hs5".
    (* ---- +0x0c: c.addi4spn s0,sp,48 (s0's VALUE is never read) ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x0c))
              (Cregidx (mword_of_int 0)) (mword_of_int 12 : mword 8) Rs0
              M1 (av - 6)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c [-]").
    iIntros (CID7 Hk7) "Hcg Hpc".
    set (M2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> M1).
    change (<[Regidx Rs0 := regval_into_reg
              (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> M1) with M2.
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x0c) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchstr + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* ---- +0x0e: c.mv s3,a0 -- s3 := addr ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x0e))
              Rs3 Ra0 M2 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e [-]").
    iIntros (CID8 Hk8) "Hcg Hpc".
    set (M3 := <[Regidx Rs3 := regval_into_reg (add_vec zero_reg (M2 !!! Regidx Ra0))]> M2).
    change (<[Regidx Rs3 := regval_into_reg (add_vec zero_reg (M2 !!! Regidx Ra0))]> M2) with M3.
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x0e) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchstr + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* ---- +0x10: c.mv s1,a1 -- s1 := buf ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x10))
              Rs1 Ra1 M3 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10 [-]").
    iIntros (CID9 Hk9) "Hcg Hpc".
    set (M4 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (M3 !!! Regidx Ra1))]> M3).
    change (<[Regidx Rs1 := regval_into_reg (add_vec zero_reg (M3 !!! Regidx Ra1))]> M3) with M4.
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x10) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchstr + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* ---- +0x12: c.mv s2,a2 -- s2 := max ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x12))
              Rs2 Ra2 M4 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12 [-]").
    iIntros (CID10 Hk10) "Hcg Hpc".
    set (M5 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (M4 !!! Regidx Ra2))]> M4).
    change (<[Regidx Rs2 := regval_into_reg (add_vec zero_reg (M4 !!! Regidx Ra2))]> M4) with M5.
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x12) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchstr + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* what the three [c.mv]s parked *)
    assert (HM2a0 : M2 !!! Regidx Ra0 = m !!! Regidx Ra0).
    { rewrite /M2 upd_ne; [| reg_neq]. rewrite /M1 upd_ne; [reflexivity | reg_neq]. }
    assert (HM3s3 : M3 !!! Regidx Rs3 = m !!! Regidx Ra0)
      by (rewrite /M3 upd_eq HM2a0; apply add_vec_zero_l).
    assert (HM3a1 : M3 !!! Regidx Ra1 = buf).
    { rewrite /M3 upd_ne; [| reg_neq]. rewrite /M2 upd_ne; [| reg_neq].
      rewrite /M1 upd_ne; [reflexivity | reg_neq]. }
    assert (HM4s1 : M4 !!! Regidx Rs1 = buf)
      by (rewrite /M4 upd_eq HM3a1; apply add_vec_zero_l).
    assert (HM4a2 : M4 !!! Regidx Ra2 = (mword_of_int (Z.of_nat maxn) : mword 64)).
    { rewrite /M4 upd_ne; [| reg_neq]. rewrite /M3 upd_ne; [| reg_neq].
      rewrite /M2 upd_ne; [| reg_neq]. rewrite /M1 upd_ne; [exact Hmax | reg_neq]. }
    assert (HM5s2 : M5 !!! Regidx Rs2 = (mword_of_int (Z.of_nat maxn) : mword 64))
      by (rewrite /M5 upd_eq HM4a2; apply add_vec_zero_l).
    assert (HM5s1 : M5 !!! Regidx Rs1 = buf)
      by (rewrite /M5 upd_ne; [exact HM4s1 | reg_neq]).
    assert (HM5s3 : M5 !!! Regidx Rs3 = m !!! Regidx Ra0).
    { rewrite /M5 upd_ne; [| reg_neq]. rewrite /M4 upd_ne; [exact HM3s3 | reg_neq]. }
    assert (HM5sp : M5 !!! Regidx csp_rs1 = pa_stk sp0 6).
    { rewrite /M5 upd_ne; [| reg_neq]. rewrite /M4 upd_ne; [| reg_neq].
      rewrite /M3 upd_ne; [| reg_neq]. rewrite /M2 upd_ne; [| reg_neq]. exact HM1sp. }
    (* ---- +0x14: jal ra,myproc ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x14))
              Rra (mword_of_int 2093302 : mword 21) M5 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi14 [-]").
    iIntros (CID11 Hk11) "Hcg Hpc".
    set (M6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x14) : mword 64) 4)]> M5).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x14) : mword 64) 4)]> M5) with M6.
    assert (Hjmp : add_vec (mword_of_int (KernelSyms.fetchstr + 0x14) : mword 64)
                     (sign_extend' 64 (mword_of_int 2093302 : mword 21)) = mword_of_int KernelSyms.myproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmp) in "Hpc".
    assert (HM6ra : M6 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x14) : mword 64) 4)
      by (rewrite /M6 upd_eq; reflexivity).
    assert (HM6sp : M6 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /M6 upd_ne; [exact HM5sp | reg_neq]).
    assert (HM6s1 : M6 !!! Regidx Rs1 = buf)
      by (rewrite /M6 upd_ne; [exact HM5s1 | reg_neq]).
    assert (HM6s2 : M6 !!! Regidx Rs2 = (mword_of_int (Z.of_nat maxn) : mword 64))
      by (rewrite /M6 upd_ne; [exact HM5s2 | reg_neq]).
    assert (HM6s3 : M6 !!! Regidx Rs3 = m !!! Regidx Ra0)
      by (rewrite /M6 upd_ne; [exact HM5s3 | reg_neq]).
    (* ---- myproc(): a0 = p ---- *)
    (* [Hcpu] was established at the entry hart; the eleven leaf steps above
       may have moved us to a different one, so it must be transported before
       it can be fed to [myproc]'s own [cpu_own] premise. *)
    iDestruct (cpu_own_transport CID CID11 n eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Myproc.wp_myproc_sconf M6 (av - 6)%nat n eb p C b
              Hn ltac:(lia)
              with "Hcg Hcpu Htext Hpc [-]").
    iIntros (CID12 Hk12 ms A) "%Hms Hcg Hcpu Hpc %HcsA".
    destruct HcsA as [HcsA HAa0].
    assert (Hpc18 : ret_pc (M6 !!! Regidx Rra) = mword_of_int (KernelSyms.fetchstr + 0x18))
      by (rewrite HM6ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc18) in "Hpc".
    (* what fetchstr parked across the call *)
    assert (HAsp : A !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite (callee_saved_lookup HcsA csp_rs1 ltac:(vm_compute; reflexivity)); exact HM6sp).
    assert (HAs1 : A !!! Regidx Rs1 = buf)
      by (rewrite (callee_saved_lookup HcsA (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HM6s1).
    assert (HAs2 : A !!! Regidx Rs2 = (mword_of_int (Z.of_nat maxn) : mword 64))
      by (rewrite (callee_saved_lookup HcsA (mword_of_int 18) ltac:(vm_compute; reflexivity)); exact HM6s2).
    assert (HAs3 : A !!! Regidx Rs3 = m !!! Regidx Ra0)
      by (rewrite (callee_saved_lookup HcsA (mword_of_int 19) ltac:(vm_compute; reflexivity)); exact HM6s3).
    (* the residual threading fact every arm hands to [fs_tail] *)
    assert (HthrA : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> A !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18 N19.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite (callee_saved_lookup HcsA r Hr).
      rewrite /M6 upd_ne; [| congruence].
      rewrite /M5 upd_ne; [| congruence].
      rewrite /M4 upd_ne; [| congruence].
      rewrite /M3 upd_ne; [| congruence].
      rewrite /M2 upd_ne; [| congruence].
      rewrite /M1 upd_ne; [| congruence]. reflexivity. }
    (* ---- the ONE borrow out of [proc_priv] ---- *)
    iDestruct (proc_priv_copy with "Hpriv") as "(Hszc & Hptc & Hpt & Hpback)".
    (* ---- +0x18: c.mv a3,s2 -- a3 := max ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x18))
              Ra3 Rs2 A (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18 [-]").
    iIntros (CID13 Hk13) "Hcg Hpc".
    set (A1 := <[Regidx Ra3 := regval_into_reg (add_vec zero_reg (A !!! Regidx Rs2))]> A).
    change (<[Regidx Ra3 := regval_into_reg (add_vec zero_reg (A !!! Regidx Rs2))]> A) with A1.
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x18) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchstr + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* ---- +0x1a: c.mv a2,s3 -- a2 := addr ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x1a))
              Ra2 Rs3 A1 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a [-]").
    iIntros (CID14 Hk14) "Hcg Hpc".
    set (A2 := <[Regidx Ra2 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx Rs3))]> A1).
    change (<[Regidx Ra2 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx Rs3))]> A1) with A2.
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x1a) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchstr + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* ---- +0x1c: c.mv a1,s1 -- a1 := buf ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x1c))
              Ra1 Rs1 A2 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c [-]").
    iIntros (CID15 Hk15) "Hcg Hpc".
    set (A3 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (A2 !!! Regidx Rs1))]> A2).
    change (<[Regidx Ra1 := regval_into_reg (add_vec zero_reg (A2 !!! Regidx Rs1))]> A2) with A3.
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x1c) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchstr + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    assert (HA2s1 : A2 !!! Regidx Rs1 = buf).
    { rewrite /A2 upd_ne; [| reg_neq]. rewrite /A1 upd_ne; [exact HAs1 | reg_neq]. }
    assert (HA3a1 : A3 !!! Regidx Ra1 = buf)
      by (rewrite /A3 upd_eq HA2s1; apply add_vec_zero_l).
    assert (HA3a0 : A3 !!! Regidx Ra0 = p).
    { rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
      rewrite /A1 upd_ne; [exact HAa0 | reg_neq]. }
    (* ---- +0x1e: c.ld a0,80(a0) -- a0 := p->pagetable ---- *)
    assert (Hptaddr : add_vec (A3 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 80 : mword 12))
                      = p_pagetable p)
      by (rewrite HA3a0; reflexivity).
    iEval (rewrite -Hptaddr) in "Hptc".
    iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x1e)) Ra0 Ra0
              (mword_of_int 80 : mword 12) A3 (av - 6)%nat (page_base (ud_root (pv_upt V))) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e Hptc [-]").
    iIntros (CID16 Hk16) "Hcg Hpc Hptc".
    iEval (rewrite Hptaddr) in "Hptc".
    set (A4 := <[Regidx Ra0 := regval_into_reg (page_base (ud_root (pv_upt V)))]> A3).
    change (<[Regidx Ra0 := regval_into_reg (page_base (ud_root (pv_upt V)))]> A3) with A4.
    assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x1e) : mword 64) 2
                    = mword_of_int (KernelSyms.fetchstr + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* ---- +0x20: jal ra,copyinstr ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x20))
              Rra (mword_of_int 2092206 : mword 21) A4 (av - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi20 [-]").
    iIntros (CID17 Hk17) "Hcg Hpc".
    set (A5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x20) : mword 64) 4)]> A4).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x20) : mword 64) 4)]> A4) with A5.
    assert (Hjcis : add_vec (mword_of_int (KernelSyms.fetchstr + 0x20) : mword 64)
                      (sign_extend' 64 (mword_of_int 2092206 : mword 21)) = mword_of_int KernelSyms.copyinstr)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjcis) in "Hpc".
    assert (HA5ra : A5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x20) : mword 64) 4)
      by (rewrite /A5 upd_eq; reflexivity).
    assert (HA5a0 : A5 !!! Regidx Ra0 = page_base (ud_root (pv_upt V))).
    { rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_eq. reflexivity. }
    assert (HA5a1 : A5 !!! Regidx Ra1 = buf).
    { rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq]. exact HA3a1. }
    assert (HA5a3 : A5 !!! Regidx Ra3 = (mword_of_int (Z.of_nat maxn) : mword 64)).
    { rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
      rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
      rewrite /A1 upd_eq HAs2. apply add_vec_zero_l. }
    assert (HA5sp : A5 !!! Regidx csp_rs1 = pa_stk sp0 6).
    { rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
      rewrite /A3 upd_ne; [| reg_neq]. rewrite /A2 upd_ne; [| reg_neq].
      rewrite /A1 upd_ne; [exact HAsp | reg_neq]. }
    assert (HA5s1 : A5 !!! Regidx Rs1 = buf).
    { rewrite /A5 upd_ne; [| reg_neq]. rewrite /A4 upd_ne; [| reg_neq].
      rewrite /A3 upd_ne; [| reg_neq]. exact HA2s1. }
    assert (HthrA5 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> A5 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18 N19.
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
      rewrite /A5 upd_ne; [| congruence].
      rewrite /A4 upd_ne; [| congruence].
      rewrite /A3 upd_ne; [| congruence].
      rewrite /A2 upd_ne; [| congruence].
      rewrite /A1 upd_ne; [| congruence]. apply HthrA; assumption. }
    assert (HK20 : (20 <= av - 6)%nat) by lia.
    assert (Hmax64 : (Z.of_nat maxn < 2 ^ 64)%Z)
      by (apply fs_z_31_64; [apply Nat2Z.is_nonneg | exact Hmax31]).
    iEval (rewrite -HA5a1) in "Hbuf".
    (* ---- copyinstr(p->pagetable, buf, addr, max) ---- *)
    iApply (Copyinstr.wp_copyinstr_sconf A5 (pv_upt V) maxn buf_olds (av - 6)%nat b p
              HK20 HA5a0 HA5a3 Hmax64
              with "Hcg Htext Hpc Hpt Hbuf [-]").
    iIntros (CID18 Hk18 mr dst_new) "Hcg Hpc Hpt Hbuf %Hcsr %Hret".
    iEval (rewrite HA5a1) in "Hbuf".
    assert (Hpc24 : ret_pc (A5 !!! Regidx Rra) = mword_of_int (KernelSyms.fetchstr + 0x24))
      by (rewrite HA5ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc24) in "Hpc".
    (* the frame and the callee-saved set survived copyinstr *)
    assert (Hrsp : mr !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite (callee_saved_lookup Hcsr csp_rs1 ltac:(vm_compute; reflexivity)); exact HA5sp).
    assert (Hrs1 : mr !!! Regidx Rs1 = buf)
      by (rewrite (callee_saved_lookup Hcsr (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HA5s1).
    assert (Hthrr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> mr !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18 N19.
      rewrite (callee_saved_lookup Hcsr r Hr). apply HthrA5; assumption. }
    (* close the [proc_priv] borrow: the descriptor never moved *)
    iAssert (⌜uptd_ext_sz (pv_sz V) (pv_upt V) (pv_upt V)⌝)%I as "#Hxr";
      [iPureIntro; apply uptd_ext_sz_refl|].
    iDestruct ("Hpback" $! (pv_upt V) with "Hxr Hszc Hptc Hpt") as "Hpriv".
    iEval (rewrite fs_upd_upt_id) in "Hpriv".
    (* ---- +0x24: bltz a0 -- copyinstr's answer decides the branch ---- *)
    destruct Hret as [[H0 (k & Hkmax & Hcstr)] | Hm1].
    - (* ======= copyinstr returned 0: fall through to strlen ======= *)
      assert (Hfall : zopz0zI_s (mr !!! Regidx Ra0) zero_reg = false)
        by (rewrite H0; vm_compute; reflexivity).
      iApply (wp_blt_x0_fall_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x24))
                (mword_of_int 24 : mword 13) Ra0 mr (av - 6)%nat b
                ltac:(vm_compute; discriminate) Hfall
                with "Hcg Hpc Hi24 [-]").
      iIntros (CID19 Hk19) "Hcg Hpc".
      assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x24) : mword 64) 4
                      = mword_of_int (KernelSyms.fetchstr + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp28) in "Hpc".
      (* ---- +0x28: c.mv a0,s1 -- a0 := buf ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x28))
                Ra0 Rs1 mr (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi28 [-]").
      iIntros (CID20 Hk20) "Hcg Hpc".
      set (B1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mr !!! Regidx Rs1))]> mr).
      change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mr !!! Regidx Rs1))]> mr) with B1.
      assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x28) : mword 64) 2
                      = mword_of_int (KernelSyms.fetchstr + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2a) in "Hpc".
      assert (HB1a0 : B1 !!! Regidx Ra0 = buf)
        by (rewrite /B1 upd_eq Hrs1; apply add_vec_zero_l).
      assert (HB1sp : B1 !!! Regidx csp_rs1 = pa_stk sp0 6)
        by (rewrite /B1 upd_ne; [exact Hrsp | reg_neq]).
      assert (HthrB1 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> B1 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18 N19.
        assert (N10 : r <> mword_of_int 10)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /B1 upd_ne; [| congruence]. apply Hthrr; assumption. }
      (* ---- +0x2a: jal ra,strlen ---- *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x2a))
                Rra (mword_of_int 2090540 : mword 21) B1 (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi2a [-]").
      iIntros (CID21 Hk21) "Hcg Hpc".
      set (B2 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x2a) : mword 64) 4)]> B1).
      change (<[Regidx Rra := regval_into_reg
                (add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x2a) : mword 64) 4)]> B1) with B2.
      assert (Hjsl : add_vec (mword_of_int (KernelSyms.fetchstr + 0x2a) : mword 64)
                       (sign_extend' 64 (mword_of_int 2090540 : mword 21)) = mword_of_int KernelSyms.strlen)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjsl) in "Hpc".
      assert (HB2ra : B2 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x2a) : mword 64) 4)
        by (rewrite /B2 upd_eq; reflexivity).
      assert (HB2a0 : B2 !!! Regidx Ra0 = buf)
        by (rewrite /B2 upd_ne; [exact HB1a0 | reg_neq]).
      assert (HB2sp : B2 !!! Regidx csp_rs1 = pa_stk sp0 6)
        by (rewrite /B2 upd_ne; [exact HB1sp | reg_neq]).
      assert (HthrB2 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> B2 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18 N19.
        assert (N1 : r <> mword_of_int 1)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /B2 upd_ne; [| congruence]. apply HthrB1; assumption. }
      assert (Hk31 : (Z.of_nat k < 2 ^ 31)%Z).
      { apply (fs_z_lt_of_nat_lt _ (Z.of_nat maxn)); [| exact Hmax31].
        apply Nat2Z.inj_lt. exact Hkmax. }
      iEval (rewrite -HB2a0) in "Hbuf".
      (* ---- strlen(buf) ---- *)
      iApply (Strlen.wp_strlen_sconf B2 maxn k dst_new (av - 6)%nat (DfracOwn 1) b p
                ltac:(lia) Hkmax Hcstr Hk31
                with "Hcg Htext Hpc Hbuf [-]").
      iIntros (CID22 Hk22 msl) "Hcg Hpc Hbuf %Hcssl %Hsla0".
      iEval (rewrite HB2a0) in "Hbuf".
      assert (Hpc2e : ret_pc (B2 !!! Regidx Rra) = mword_of_int (KernelSyms.fetchstr + 0x2e))
        by (rewrite HB2ra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc2e) in "Hpc".
      assert (Hslsp : msl !!! Regidx csp_rs1 = pa_stk sp0 6)
        by (rewrite (callee_saved_lookup Hcssl csp_rs1 ltac:(vm_compute; reflexivity)); exact HB2sp).
      assert (Hthrsl : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> msl !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18 N19.
        rewrite (callee_saved_lookup Hcssl r Hr). apply HthrB2; assumption. }
      iApply (fs_tail m msl av (mword_of_int (Z.of_nat k) : mword 64)
                sp0 ra0 s00 s10 s20 s30 u6 p b
                ltac:(lia) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                Hslsp Hsla0 Hthrsl
                with "Hcg Htext Hpc Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 [-]").
      iIntros (CID23 Hk23 mf) "[%Hcsf %Hfa0] Hcg Hpc".
      (* [Hcpu] has been sitting at [CID12] (myproc's exit hart) ever since;
         re-anchor it at the final hart before it can feed the function's own
         [Hcont]. *)
      iDestruct (cpu_own_transport CID12 CID23 n eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iSpecialize ("Hcont" $! CID23 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf dst_new with "[%] Hcg Hcpu Hpc Hpriv Hbuf [%]").
      { exact Hcsf. }
      left. exists k. split; [exact Hkmax|]. split; [exact Hcstr | exact Hfa0].
    - (* ======= copyinstr returned -1: take the branch ======= *)
      assert (Htk : zopz0zI_s (mr !!! Regidx Ra0) zero_reg = true)
        by (rewrite Hm1; vm_compute; reflexivity).
      iApply (wp_blt_x0_taken_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x24))
                (mword_of_int 24 : mword 13) Ra0 mr (av - 6)%nat b
                ltac:(vm_compute; discriminate) Htk ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi24 [-]").
      iNext. iIntros (CID19 Hk19) "Hcg Hpc".
      assert (Hjb : add_vec (mword_of_int (KernelSyms.fetchstr + 0x24) : mword 64)
                      (sign_extend' 64 (mword_of_int 24 : mword 13))
                    = mword_of_int (KernelSyms.fetchstr + 0x3c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjb) in "Hpc".
      (* ---- +0x3c: c.li a0,-1 ---- *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x3c))
                Ra0 (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64) mr (av - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi3c [-]").
      iIntros (CID20 Hk20) "Hcg Hpc".
      set (E1 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> mr).
      change (<[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> mr) with E1.
      assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.fetchstr + 0x3c) : mword 64) 2
                      = mword_of_int (KernelSyms.fetchstr + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3e) in "Hpc".
      (* ---- +0x3e: c.j -0x0c ---- *)
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.fetchstr + 0x3e))
                (sign_extend' 21 (concat_vec (mword_of_int 2040 : mword 11) ('b"0")))
                E1 (av - 6)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi3e [-]").
      iIntros (CID21 Hk21). iNext. iIntros "Hcg Hpc".
      assert (Hjc : add_vec (mword_of_int (KernelSyms.fetchstr + 0x3e) : mword 64)
                      (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2040 : mword 11) ('b"0"))))
                    = mword_of_int (KernelSyms.fetchstr + 0x2e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjc) in "Hpc".
      assert (HE1sp : E1 !!! Regidx csp_rs1 = pa_stk sp0 6)
        by (rewrite /E1 upd_ne; [exact Hrsp | reg_neq]).
      assert (HE1a0 : E1 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64))
        by (rewrite /E1 upd_eq; reflexivity).
      assert (HthrE1 : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> E1 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18 N19.
        assert (N10 : r <> mword_of_int 10)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /E1 upd_ne; [| congruence]. apply Hthrr; assumption. }
      iApply (fs_tail m E1 av (mword_of_int (-1) : mword 64)
                sp0 ra0 s00 s10 s20 s30 u6 p b
                ltac:(lia) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                HE1sp HE1a0 HthrE1
                with "Hcg Htext Hpc Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 [-]").
      iIntros (CID22 Hk22 mf) "[%Hcsf %Hfa0] Hcg Hpc".
      iDestruct (cpu_own_transport CID12 CID22 n eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
      iSpecialize ("Hcont" $! CID22 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf dst_new with "[%] Hcg Hcpu Hpc Hpriv Hbuf [%]").
      { exact Hcsf. }
      right. exact Hfa0.
  Qed.

End ProofFetchstr.

End FetchstrProof.
