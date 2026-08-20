(* ProofIinit.v -- the whole-function WP for xv6's iinit() over the SIE-agnostic
   sconf world.

     void iinit(void) {
       initlock(&itable.lock, "itable");
       for (int i = 0; i < NINODE; i++)
         initsleeplock(&itable.inode[i].lock, "inode");
     }

   Two parts: the thin-initlock-wrapper prologue (6-slot frame, ra/s0/s1/s2/s3
   saved, the two auipc/addi argument pairs, jal initlock) and then a BOUNDED
   loop over initsleeplock, proved -- like freerange's loop over kfree -- by
   ordinary Coq fuel induction on the number of inodes left, NOT iLoeb (the
   packaged sconf leaves strip the step's later, so a later-guarded IH could
   never be applied).  The loop cursor is [ArrCursor]'s [inode_lock i], so the
   [bne s1,s3] back edge becomes the index test [S j =? NINODE] ([acur_neq])
   and the [addi s1,s1,136] bump becomes [S j] ([acur_step]). *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import KernelText KernelDataInv.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import WpLock SleepLock.
Require Import ArrCursor.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import SpecInitlock SpecInitsleeplock.
Require Import CodeIinit.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecIinit.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.
Import Defs.

Module IinitProof (Initlock : INITLOCK) (Initsleeplock : INITSLEEPLOCK) : IINIT.

Section ProofIinit.
  Context `{!riscvGS Σ}.
  Context `{!xv6G Σ}.
  (* NOTE: no shared [Context `{GEN : GenId} `{CID : CpuId}] here -- the epilogue/loop
     lemmas below apply EACH OTHER at a hart that a [wp_next] crossing may
     have migrated to, so each needs its OWN implicit per-lemma [CID]
     binder (shadowing what a section Context would give) rather than
     sharing one rigid section-wide hart; see the porting guide's "Two
     things a DECOMPOSED proof needs" (worked example: ProofProcMapstacks.v). *)


  (* the two register indices the loop keeps live besides s0/s1 *)
  Notation s2i := (mword_of_int 18 : mword 5).
  Notation s3i := (mword_of_int 19 : mword 5).

  (* ================================================================= *)
  (*  The epilogue (+0x4a..+0x56): restore ra/s0/s1/s2/s3, give the      *)
  (*  6-slot frame back, ret.  Factored out because both the loop's exit *)
  (*  arm reaches it and it is 40 lines of frame arithmetic; payload-free *)
  (*  (the caller's postcondition resources ride in the framed [-]).      *)
  (* ================================================================= *)
  (* [CID0] is its OWN binder here (shadowing what a section Context would
     give): this "post-resume half" gets applied at whichever hart the
     loop's own leaf steps actually migrated to, not necessarily the entry
     hart of [wp_iinit_sconf] -- the same rule ProofConsputc.wp_consputc_epi
     follows. *)
  Lemma iiepi `{GEN : GenId} `{CID0 : CpuId} (m Me : regfile) (K : nat) (b : bool) (p : mword 64) :
    let sp0 := m !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))) in
    let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
    (6 <= K)%nat ->
    Me !!! Regidx csp_rs1 = spr ->
    (forall c : mword 5, is_cs_idx c = true ->
       c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> s2i -> c <> s3i -> c <> csp_rs1 ->
       Me !!! Regidx c = m !!! Regidx c) ->
    kernel_text -∗
    sie_cap_gpr KT1 Me (K - 6) b p -∗
    pc_is (mword_of_int (KernelSyms.iinit + 0x4a)) -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx (mword_of_int 8 : mword 5) : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx (mword_of_int 9 : mword 5) : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx s2i : mword 64) -∗
    (pa_stk sp0 5) ↦₈[KT1] (m !!! Regidx s3i : mword 64) -∗
    (∃ v : mword 64, (pa_stk sp0 6) ↦₈[KT1] v) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mr,
      sie_cap_gpr KT1 mr K b p -∗
      pc_is ret_tgt -∗ ⌜ callee_saved m mr ⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 spr ret_tgt HK6 HMesp HMecs.
    assert (Hspr6 : spr = pa_stk sp0 6).
    { unfold spr, pa_stk, add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iIntros "#Htext Hcg Hpc Hc1 Hc2 Hc3 Hc4 Hc5 Hf6 Hcont".
    iPoseProof (iii_4a with "Htext") as "Hi4a".
    iPoseProof (iii_4c with "Htext") as "Hi4c".
    iPoseProof (iii_4e with "Htext") as "Hi4e".
    iPoseProof (iii_50 with "Htext") as "Hi50".
    iPoseProof (iii_52 with "Htext") as "Hi52".
    iPoseProof (iii_54 with "Htext") as "Hi54".
    iPoseProof (iii_56 with "Htext") as "Hi56".
    (* +0x4a c.ldsp ra,40(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iinit + 0x4a)) (mword_of_int 5 : mword 6) (mword_of_int 1 : mword 5)
              Me (K - 6)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4a [Hc1]").
    { iEval (rewrite HMesp Hb1). iExact "Hc1". }
    iIntros (CID1 Hs1) "Hcg Hpc Hc1".
    iEval (rewrite HMesp Hb1) in "Hc1".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> Me).
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spr) by (rewrite /E1 upd_ne; [exact HMesp | vm_compute; discriminate]).
    assert (Hpp4c : add_vec_int (mword_of_int (KernelSyms.iinit + 0x4a) : mword 64) 2 = mword_of_int (KernelSyms.iinit + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4c) in "Hpc".
    (* +0x4c c.ldsp s0,32(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iinit + 0x4c)) (mword_of_int 4 : mword 6) (mword_of_int 8 : mword 5)
              E1 (K - 6)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4c [Hc2]").
    { iEval (rewrite HE1sp Hb2). iExact "Hc2". }
    iIntros (CID2 Hs2) "Hcg Hpc Hc2".
    iEval (rewrite HE1sp Hb2) in "Hc2".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spr) by (rewrite /E2 upd_ne; [exact HE1sp | vm_compute; discriminate]).
    assert (Hpp4e : add_vec_int (mword_of_int (KernelSyms.iinit + 0x4c) : mword 64) 2 = mword_of_int (KernelSyms.iinit + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4e) in "Hpc".
    (* +0x4e c.ldsp s1,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iinit + 0x4e)) (mword_of_int 3 : mword 6) (mword_of_int 9 : mword 5)
              E2 (K - 6)%nat (m !!! Regidx (mword_of_int 9 : mword 5)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4e [Hc3]").
    { iEval (rewrite HE2sp Hb3). iExact "Hc3". }
    iIntros (CID3 Hs3) "Hcg Hpc Hc3".
    iEval (rewrite HE2sp Hb3) in "Hc3".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    assert (HE3sp : E3 !!! Regidx csp_rs1 = spr) by (rewrite /E3 upd_ne; [exact HE2sp | vm_compute; discriminate]).
    assert (Hpp50 : add_vec_int (mword_of_int (KernelSyms.iinit + 0x4e) : mword 64) 2 = mword_of_int (KernelSyms.iinit + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp50) in "Hpc".
    (* +0x50 c.ldsp s2,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iinit + 0x50)) (mword_of_int 2 : mword 6) s2i
              E3 (K - 6)%nat (m !!! Regidx s2i) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi50 [Hc4]").
    { iEval (rewrite HE3sp Hb4). iExact "Hc4". }
    iIntros (CID4 Hs4) "Hcg Hpc Hc4".
    iEval (rewrite HE3sp Hb4) in "Hc4".
    set (E4 := <[Regidx s2i := regval_into_reg (m !!! Regidx s2i)]> E3).
    assert (HE4sp : E4 !!! Regidx csp_rs1 = spr) by (rewrite /E4 upd_ne; [exact HE3sp | vm_compute; discriminate]).
    assert (Hpp52 : add_vec_int (mword_of_int (KernelSyms.iinit + 0x50) : mword 64) 2 = mword_of_int (KernelSyms.iinit + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp52) in "Hpc".
    (* +0x52 c.ldsp s3,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iinit + 0x52)) (mword_of_int 1 : mword 6) s3i
              E4 (K - 6)%nat (m !!! Regidx s3i) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi52 [Hc5]").
    { iEval (rewrite HE4sp Hb5). iExact "Hc5". }
    iIntros (CID5 Hs5) "Hcg Hpc Hc5".
    iEval (rewrite HE4sp Hb5) in "Hc5".
    set (E5 := <[Regidx s3i := regval_into_reg (m !!! Regidx s3i)]> E4).
    assert (HE5sp : E5 !!! Regidx csp_rs1 = spr) by (rewrite /E5 upd_ne; [exact HE4sp | vm_compute; discriminate]).
    assert (Hpp54 : add_vec_int (mword_of_int (KernelSyms.iinit + 0x52) : mword 64) 2 = mword_of_int (KernelSyms.iinit + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp54) in "Hpc".
    (* +0x54 c.addi16sp sp,48 -- the frame trade back (pop 6) *)
    iDestruct "Hf6" as (v6) "Hc6".
    set (E6 := <[Regidx csp_rs1 := regval_into_reg (add_vec (E5 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E5).
    assert (HE6sp : E6 !!! Regidx csp_rs1 = sp0).
    { rewrite /E6 upd_eq. rewrite HE5sp.
      unfold spr. rewrite pa_stk_off2.
      replace (mword_of_int (bv_wrap 64 (uint (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)) : mword 64) + uint (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)) : mword 64))) : mword 64) with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      change (add_vec sp0 (mword_of_int 0)) with (add_vec_int sp0 0). apply avi0. }
    assert (Hup : E5 !!! Regidx csp_rs1 = pa_stk (E6 !!! Regidx csp_rs1) 6).
    { rewrite HE5sp HE6sp Hspr6. reflexivity. }
    assert (Hwv : add_vec (E5 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0).
    { rewrite -HE6sp /E6 upd_eq. reflexivity. }
    assert (Hpop : E5 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E5 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6).
    { rewrite Hwv Hup HE6sp. reflexivity. }
    iAssert (stack_own (KTR := KT1) sp0 6) with "[Hc1 Hc2 Hc3 Hc4 Hc5 Hc6]" as "Hframe6".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hc1"; [iExists _; iExact "Hc1"|].
      iSplitL "Hc2"; [iExists _; iExact "Hc2"|].
      iSplitL "Hc3"; [iExists _; iExact "Hc3"|].
      iSplitL "Hc4"; [iExists _; iExact "Hc4"|].
      iSplitL "Hc5"; [iExists _; iExact "Hc5"|].
      iSplitL "Hc6"; [iExists _; iExact "Hc6"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe6".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.iinit + 0x54)) (mword_of_int 3 : mword 6) E5 (K - 6)%nat 6 b Hpop
              with "Hcg Hpc Hi54 Hframe6").
    iIntros (CID6 Hs6) "Hcg Hpc".
    assert (Hnk : ((K - 6) + 6)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E5 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E5) with E6.
    assert (Hpp56 : add_vec_int (mword_of_int (KernelSyms.iinit + 0x54) : mword 64) 2 = mword_of_int (KernelSyms.iinit + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp56) in "Hpc".
    (* +0x56 c.ret *)
    assert (HE6ra : E6 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /E6 upd_ne; [| vm_compute; discriminate].
      rewrite /E5 upd_ne; [| vm_compute; discriminate].
      rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_eq; reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.iinit + 0x56)) (mword_of_int 1 : mword 5) E6 K b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi56").
    iIntros (CID7 Hs7) "Hcg Hpc".
    assert (Hretf : ret_pc (E6 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
      by (rewrite HE6ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E6 with "Hcg Hpc [%]").
    (* callee_saved m E6 *)
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> s2i -> c <> s3i -> c <> csp_rs1 ->
              E6 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N8 N9 N18 N19 Nsp.
      pose proof (is_cs_idx_true_neq (mword_of_int 1 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Nra.
      rewrite /E6 upd_ne; [| congruence].
      rewrite /E5 upd_ne; [| congruence].
      rewrite /E4 upd_ne; [| congruence].
      rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      apply HMecs; assumption. }
    assert (Hcs_s0 : E6 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5)).
    { rewrite /E6 upd_ne; [| vm_compute; discriminate].
      rewrite /E5 upd_ne; [| vm_compute; discriminate].
      rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_eq; reflexivity. }
    assert (Hcs_s1 : E6 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5)).
    { rewrite /E6 upd_ne; [| vm_compute; discriminate].
      rewrite /E5 upd_ne; [| vm_compute; discriminate].
      rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_eq; reflexivity. }
    assert (Hcs_s2 : E6 !!! Regidx s2i = m !!! Regidx s2i).
    { rewrite /E6 upd_ne; [| vm_compute; discriminate].
      rewrite /E5 upd_ne; [| vm_compute; discriminate].
      rewrite /E4 upd_eq; reflexivity. }
    assert (Hcs_s3 : E6 !!! Regidx s3i = m !!! Regidx s3i).
    { rewrite /E6 upd_ne; [| vm_compute; discriminate].
      rewrite /E5 upd_eq; reflexivity. }
    unfold callee_saved.
    split. { exact HE6sp. }
    split. { exact Hcs_s0. }
    split. { exact Hcs_s1. }
    split. { exact Hcs_s2. }
    split. { exact Hcs_s3. }
    repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate].
  Qed.

  (* ================================================================= *)
  (*  THE LOOP (+0x3a entry): fuel induction on the inodes left, its OWN
      top-level lemma with its OWN [CID] binder (shadowing what a section
      Context would give) -- the same "no shared Context" rule as [iiepi],
      and the recursive/loop case of the porting guide's "Two things a
      DECOMPOSED proof needs": [CID] rides the SAME [forall] as the other
      per-iteration state ([j], [M], ...) so [induction fuel] auto-
      generalizes it, and each step re-anchors the caller's continuation
      to the hart THIS iteration's own leaves migrated to via
      [wp_next_shift] before recursing or handing off to [iiepi] (worked
      example for both: ProofProcMapstacks.v's loop). *)
  (* ================================================================= *)
  Lemma iinit_loop `{GEN : GenId} `{CID : CpuId} (m : regfile) (K : nat) (b : bool) (p : mword 64)
      (fuel : nat) :
    let sp0 := m !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))) in
    let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
    let name_inode := (mword_of_int inode_name_str : mword 64) in
    forall (j : nat) (M : regfile),
    (12 <= K)%nat ->
    (NINODE - j <= fuel)%nat ->
    (j < NINODE)%nat ->
    M !!! Regidx (mword_of_int 9 : mword 5) = inode_lock j ->
    M !!! Regidx s2i = name_inode ->
    M !!! Regidx s3i = inode_lock NINODE ->
    M !!! Regidx csp_rs1 = spr ->
    (forall c : mword 5, is_cs_idx c = true ->
       c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> s2i -> c <> s3i -> c <> csp_rs1 ->
       M !!! Regidx c = m !!! Regidx c) ->
    sie_cap_gpr KT1 M (K - 6) b p -∗
    kernel_text -∗
    sl_str_addr ↦ₛ□ "sleep lock"%string -∗
    name_inode ↦ₛ□ "inode"%string -∗
    pc_is (mword_of_int (KernelSyms.iinit + 0x3a)) -∗
    ([∗ list] i ∈ seq 0 j, sl_fresh (inode_lock i) "inode"%string) -∗
    ([∗ list] i ∈ seq j (NINODE - j), sl_raw (inode_lock i)) -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx (mword_of_int 8 : mword 5) : mword 64) -∗
    (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx (mword_of_int 9 : mword 5) : mword 64) -∗
    (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx s2i : mword 64) -∗
    (pa_stk sp0 5) ↦₈[KT1] (m !!! Regidx s3i : mword 64) -∗
    (∃ v : mword 64, (pa_stk sp0 6) ↦₈[KT1] v) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mr, sie_cap_gpr KT1 mr K b p -∗ pc_is ret_tgt -∗ ⌜ callee_saved m mr ⌝ -∗
        ([∗ list] i ∈ seq 0 NINODE, sl_fresh (inode_lock i) "inode"%string) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 spr ret_tgt name_inode.
    revert CID.
    induction fuel as [|fuel IHf]; intros CID j M HK Hlen Hj HMs1 HMs2 HMs3 HMsp HMcs.
    { exfalso. lia. }
    iIntros "Hcg #Htext #Hstr_sl #Hstr_inode Hpc Hdone Hraw Hc1 Hc2 Hc3 Hc4 Hc5 Hf6 Hpost".
    (* peel the head raw sleeplock off the remaining list *)
    assert (Hsplit : (NINODE - j)%nat = S (NINODE - S j)) by lia.
    iEval (rewrite Hsplit) in "Hraw".
    iEval (cbn [seq]) in "Hraw".
    iDestruct "Hraw" as "[Hraw0 Hraw]".
    iDestruct "Hraw0" as (vlocked vlk vpid vlkname vcpu' vname') "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6p)".
    iPoseProof (iii_3a with "Htext") as "Hi3a".
    iPoseProof (iii_3c with "Htext") as "Hi3c".
    iPoseProof (iii_3e with "Htext") as "Hi3e".
    iPoseProof (iii_42 with "Htext") as "Hi42".
    iPoseProof (iii_46 with "Htext") as "Hi46".
    (* +0x3a c.mv a1,s2 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iinit + 0x3a)) (mword_of_int 11 : mword 5) s2i
              M (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3a").
    iIntros (CIDa Hsa) "Hcg Hpc".
    set (M1 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec zero_reg (M !!! Regidx s2i))]> M).
    assert (HM1a1 : M1 !!! Regidx (mword_of_int 11 : mword 5) = name_inode).
    { rewrite /M1 upd_eq. rewrite HMs2. apply add_vec_zero_l. }
    assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.iinit + 0x3a) : mword 64) 2 = mword_of_int (KernelSyms.iinit + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3c) in "Hpc".
    (* +0x3c c.mv a0,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iinit + 0x3c)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              M1 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3c").
    iIntros (CIDb Hsb) "Hcg Hpc".
    set (M2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (M1 !!! Regidx (mword_of_int 9 : mword 5)))]> M1).
    assert (HM1s1 : M1 !!! Regidx (mword_of_int 9 : mword 5) = inode_lock j)
      by (rewrite /M1 upd_ne; [exact HMs1 | vm_compute; discriminate]).
    assert (HM2a0 : M2 !!! Regidx (mword_of_int 10 : mword 5) = inode_lock j).
    { rewrite /M2 upd_eq. rewrite HM1s1. apply add_vec_zero_l. }
    assert (HM2a1 : M2 !!! Regidx (mword_of_int 11 : mword 5) = name_inode)
      by (rewrite /M2 upd_ne; [exact HM1a1 | vm_compute; discriminate]).
    assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.iinit + 0x3c) : mword 64) 2 = mword_of_int (KernelSyms.iinit + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3e) in "Hpc".
    (* +0x3e jal ra,initsleeplock *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iinit + 0x3e)) (mword_of_int 1 : mword 5) (mword_of_int 3802 : mword 21)
              M2 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi3e").
    iIntros (CIDc Hsc) "Hcg Hpc".
    set (M3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.iinit + 0x3e) : mword 64) 4)]> M2).
    assert (Htgtisl : add_vec (mword_of_int (KernelSyms.iinit + 0x3e) : mword 64) (sign_extend' 64 (mword_of_int 3802 : mword 21)) = mword_of_int KernelSyms.initsleeplock)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtisl) in "Hpc".
    assert (HM3a0 : M3 !!! Regidx (mword_of_int 10 : mword 5) = inode_lock j)
      by (rewrite /M3 upd_ne; [exact HM2a0 | vm_compute; discriminate]).
    assert (HM3a1 : M3 !!! Regidx (mword_of_int 11 : mword 5) = name_inode)
      by (rewrite /M3 upd_ne; [exact HM2a1 | vm_compute; discriminate]).
    assert (HM3s1 : M3 !!! Regidx (mword_of_int 9 : mword 5) = inode_lock j).
    { rewrite /M3 upd_ne; [| vm_compute; discriminate].
      rewrite /M2 upd_ne; [exact HM1s1 | vm_compute; discriminate]. }
    assert (HM3s2 : M3 !!! Regidx s2i = name_inode).
    { rewrite /M3 upd_ne; [| vm_compute; discriminate].
      rewrite /M2 upd_ne; [| vm_compute; discriminate].
      rewrite /M1 upd_ne; [exact HMs2 | vm_compute; discriminate]. }
    assert (HM3s3 : M3 !!! Regidx s3i = inode_lock NINODE).
    { rewrite /M3 upd_ne; [| vm_compute; discriminate].
      rewrite /M2 upd_ne; [| vm_compute; discriminate].
      rewrite /M1 upd_ne; [exact HMs3 | vm_compute; discriminate]. }
    assert (HM3sp : M3 !!! Regidx csp_rs1 = spr).
    { rewrite /M3 upd_ne; [| vm_compute; discriminate].
      rewrite /M2 upd_ne; [| vm_compute; discriminate].
      rewrite /M1 upd_ne; [exact HMsp | vm_compute; discriminate]. }
    assert (HM3cs : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> s2i -> c <> s3i -> c <> csp_rs1 ->
              M3 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N8 N9 N18 N19 Nsp.
      pose proof (is_cs_idx_true_neq (mword_of_int 1 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Nra.
      pose proof (is_cs_idx_true_neq (mword_of_int 10 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na0.
      pose proof (is_cs_idx_true_neq (mword_of_int 11 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na1.
      rewrite /M3 upd_ne; [| congruence].
      rewrite /M2 upd_ne; [| congruence].
      rewrite /M1 upd_ne; [| congruence].
      apply HMcs; assumption. }
    assert (HM3ra : M3 !!! Regidx (mword_of_int 1 : mword 5) = mword_of_int (KernelSyms.iinit + 0x42)).
    { rewrite /M3 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    (* ---- initsleeplock(&inode[j].lock, "inode") ---- *)
    iApply (Initsleeplock.wp_initsleeplock_sconf M3 "inode"%string
              vlocked vlk vpid vlkname vcpu' vname' (K - 6) b p
              ltac:(lia)
              with "Hcg Htext Hpc Hstr_sl [] [Hf1] [Hf2] [Hf3] [Hf4] [Hf5] [Hf6p]").
    { iEval (rewrite HM3a1). iExact "Hstr_inode". }
    { iEval (rewrite HM3a0). iExact "Hf1". }
    { iEval (rewrite HM3a0). iExact "Hf2". }
    { iEval (rewrite HM3a0). iExact "Hf3". }
    { iEval (rewrite HM3a0). iExact "Hf4". }
    { iEval (rewrite HM3a0). iExact "Hf5". }
    { iEval (rewrite HM3a0). iExact "Hf6p". }
    iIntros (CIDd Hsd msl) "Hcg Hpc %Hslcs Hg1 Hg2 Hg3 Hg4 Hg5 Hg6".
    iEval (rewrite HM3a0) in "Hg1". iEval (rewrite HM3a0) in "Hg2".
    iEval (rewrite HM3a0) in "Hg3". iEval (rewrite HM3a0) in "Hg4".
    iEval (rewrite HM3a0) in "Hg5". iEval (rewrite HM3a0) in "Hg6".
    assert (Hpcsl : ret_pc (M3 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.iinit + 0x42)).
    { rewrite HM3ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcsl) in "Hpc".
    (* the freshly initialized sleeplock joins the accumulator *)
    iAssert (sl_fresh (inode_lock j) "inode"%string) with "[Hg1 Hg2 Hg3 Hg4 Hg5 Hg6]" as "Hfr".
    { rewrite /sl_fresh. iFrame "Hg1 Hg2 Hg3 Hg4 Hg5 Hg6". }
    iAssert ([∗ list] i ∈ seq 0 (S j), sl_fresh (inode_lock i) "inode"%string)%I
      with "[Hdone Hfr]" as "Hdone".
    { rewrite seq_S. rewrite big_sepL_app. iFrame "Hdone".
      rewrite Nat.add_0_l. cbn [seq]. by iFrame "Hfr". }
    pose proof Hslcs as Hslcs_full.
    assert (Hslsp : msl !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hslcs_full csp_rs1 ltac:(vm_compute; reflexivity)); exact HM3sp).
    assert (Hsls1 : msl !!! Regidx (mword_of_int 9 : mword 5) = inode_lock j)
      by (rewrite (callee_saved_lookup Hslcs_full (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)); exact HM3s1).
    assert (Hsls2 : msl !!! Regidx s2i = name_inode)
      by (rewrite (callee_saved_lookup Hslcs_full s2i ltac:(vm_compute; reflexivity)); exact HM3s2).
    assert (Hsls3 : msl !!! Regidx s3i = inode_lock NINODE)
      by (rewrite (callee_saved_lookup Hslcs_full s3i ltac:(vm_compute; reflexivity)); exact HM3s3).
    assert (Hslcs' : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> s2i -> c <> s3i -> c <> csp_rs1 ->
              msl !!! Regidx c = m !!! Regidx c).
    { intros c Hc N8 N9 N18 N19 Nsp.
      rewrite (callee_saved_lookup Hslcs_full c Hc). apply HM3cs; assumption. }
    (* +0x42 addi s1,s1,136 -- bump the cursor to inode j+1 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iinit + 0x42)) (mword_of_int 9 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 136 : mword 12)
              msl (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi42").
    iIntros (CIDe Hse) "Hcg Hpc".
    set (N1 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec (msl !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 136 : mword 12)))]> msl).
    assert (HN1s1 : N1 !!! Regidx (mword_of_int 9 : mword 5) = inode_lock (S j)).
    { rewrite /N1 upd_eq. rewrite Hsls1. unfold inode_lock.
      apply (acur_step inode_lock_base inode_stride j).
      unfold inode_stride. apply bv_eq; vm_compute; reflexivity. }
    assert (HN1s2 : N1 !!! Regidx s2i = name_inode)
      by (rewrite /N1 upd_ne; [exact Hsls2 | vm_compute; discriminate]).
    assert (HN1s3 : N1 !!! Regidx s3i = inode_lock NINODE)
      by (rewrite /N1 upd_ne; [exact Hsls3 | vm_compute; discriminate]).
    assert (HN1sp : N1 !!! Regidx csp_rs1 = spr)
      by (rewrite /N1 upd_ne; [exact Hslsp | vm_compute; discriminate]).
    assert (HN1cs : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> s2i -> c <> s3i -> c <> csp_rs1 ->
              N1 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N8 N9 N18 N19 Nsp.
      rewrite /N1 upd_ne; [| congruence]. apply Hslcs'; assumption. }
    assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.iinit + 0x42) : mword 64) 4 = mword_of_int (KernelSyms.iinit + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp46) in "Hpc".
    (* +0x46 bne s1,s3 -- back edge unless the cursor reached the end *)
    assert (Hcmp : neq_vec (rget N1 (mword_of_int 9 : mword 5)) (rget N1 s3i)
                   = negb (Nat.eqb (S j) NINODE)).
    { rgne. rgne. rewrite HN1s1 HN1s3. unfold inode_lock.
      apply (acur_neq inode_lock_base inode_stride (S j) NINODE
               inode_lock_base_nonneg inode_stride_pos inode_lock_end_fits).
      lia. }
    (* [decide], NOT [Nat.eqb_spec]: destructing the reflect would abstract
       [S j =? NINODE] out of [Hcmp] too, leaving the branch conditions in a
       shape the [negb] rewrites below no longer match. *)
    destruct (decide (S j = NINODE)) as [Hend | Hne].
    - (* the last inode: bne FALLS -> straight into the epilogue *)
      assert (Hfall : neq_vec (rget N1 (mword_of_int 9 : mword 5)) (rget N1 s3i) = false).
      { rewrite Hcmp. rewrite (proj2 (Nat.eqb_eq (S j) NINODE) Hend). reflexivity. }
      iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.iinit + 0x46)) (mword_of_int 8180 : mword 13) s3i (mword_of_int 9 : mword 5)
                N1 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hfall
                with "Hcg Hpc Hi46").
      iIntros (CIDf Hsf) "Hcg Hpc".
      assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.iinit + 0x46) : mword 64) 4 = mword_of_int (KernelSyms.iinit + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4a) in "Hpc".
      (* the remaining-raw list is empty and the accumulator is the full one *)
      assert (Hnone : (NINODE - S j)%nat = 0%nat) by lia.
      iEval (rewrite Hnone) in "Hraw". iEval (cbn [seq]) in "Hraw".
      iEval (rewrite Hend) in "Hdone".
      (* re-anchor the caller's continuation to the hart this iteration's own
         leaves + initsleeplock migrated to, THEN hand it to [iiepi] --
         which itself is [wp_next]-wrapped, so [[-]] leaves exactly that
         obligation, discharged the ProofConsputc.wp_consputc_epi way. *)
      assert (Hshift : b = false \/ p = zero_reg -> (CIDf : CPU) = (CID : CPU)) by wp_next_chain.
      iDestruct (wp_next_shift Hshift with "Hpost") as "Hpost".
      iApply (iiepi m N1 K b p ltac:(lia) HN1sp HN1cs
                with "Htext Hcg Hpc Hc1 Hc2 Hc3 Hc4 Hc5 Hf6").
      iIntros (CIDg Hsg mr) "Hcg Hpc %Hcs".
      iSpecialize ("Hpost" $! CIDg with "[%]"); [wp_next_chain|].
      iApply ("Hpost" $! mr with "Hcg Hpc [//] Hdone").
    - (* more inodes: bne TAKEN -> back edge to +0x3a at cursor S j *)
      assert (Htgt3a : add_vec (mword_of_int (KernelSyms.iinit + 0x46) : mword 64) (sign_extend' 64 (mword_of_int 8180 : mword 13)) = mword_of_int (KernelSyms.iinit + 0x3a))
        by (apply bv_eq; vm_compute; reflexivity).
      assert (Htaken : neq_vec (rget N1 (mword_of_int 9 : mword 5)) (rget N1 s3i) = true).
      { rewrite Hcmp. rewrite (proj2 (Nat.eqb_neq (S j) NINODE) Hne). reflexivity. }
      iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.iinit + 0x46)) (mword_of_int 8180 : mword 13) s3i (mword_of_int 9 : mword 5)
                N1 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Htaken
                ltac:(rewrite Htgt3a; vm_compute; reflexivity)
                with "Hcg Hpc Hi46").
      iNext. iIntros (CIDh Hsh) "Hcg Hpc".
      iEval (rewrite Htgt3a) in "Hpc".
      (* recurse via [IHf] at the hart THIS iteration ended up on: re-anchor
         [Hpost] there first ([wp_next_shift]), matching
         ProofProcMapstacks.v's loop. *)
      assert (Hshift2 : b = false \/ p = zero_reg -> (CIDh : CPU) = (CID : CPU)) by wp_next_chain.
      iDestruct (wp_next_shift Hshift2 with "Hpost") as "Hpost".
      iApply (IHf CIDh (S j) N1 HK ltac:(lia) ltac:(lia) HN1s1 HN1s2 HN1s3 HN1sp HN1cs
                with "Hcg Htext Hstr_sl Hstr_inode Hpc Hdone Hraw Hc1 Hc2 Hc3 Hc4 Hc5 Hf6 Hpost").
  Qed.

  (* ================================================================= *)
  (*  iinit's whole-function WP.                                        *)
  (* ================================================================= *)
  Lemma wp_iinit_sconf `{GEN : GenId} `{CID : CpuId}
      (m : regfile) (K : nat)
      (vlock : mword 32) (vname vcpu : mword 64) (b : bool) (p : mword 64)
    : wp_iinit_sconf_body m K vlock vname vcpu b p.
  Proof.
    cbv beta delta [wp_iinit_sconf_body].
    intros pcE ret_tgt lk c_name c_cpu HK.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))).
    pose (name_itable := (mword_of_int itable_name_str : mword 64)).
    pose (name_inode := (mword_of_int inode_name_str : mword 64)).
    iIntros "Hcg #Htext #Hkdata Hpc Hlock Hname Hcpu Hraws Hcont".
    (* ---- the three string literals, read out of the data image ---- *)
    assert (Hitable : forall j bt, cstring_bytes "itable"%string !! j = Some bt ->
                       KernelData.kernel_data !! (itable_name_str + Z.of_nat j)%Z = Some bt).
    { intros j bt Hj.
      do 7 (destruct j as [|j];
            [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
      vm_compute in Hj; discriminate. }
    iPoseProof (kernel_data_string itable_name_str "itable"%string name_itable eq_refl ltac:(unfold text_end, itable_name_str; lia)
                                                                                       ltac:(vm_compute; discriminate) Hitable
                  with "Hkdata") as "#Hstr_itable".
    assert (Hinode : forall j bt, cstring_bytes "inode"%string !! j = Some bt ->
                      KernelData.kernel_data !! (inode_name_str + Z.of_nat j)%Z = Some bt).
    { intros j bt Hj.
      do 6 (destruct j as [|j];
            [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
      vm_compute in Hj; discriminate. }
    iPoseProof (kernel_data_string inode_name_str "inode"%string name_inode eq_refl ltac:(unfold text_end, inode_name_str; lia)
                                                                                    ltac:(vm_compute; discriminate) Hinode
                  with "Hkdata") as "#Hstr_inode".
    assert (Hslstr : forall j bt, cstring_bytes "sleep lock"%string !! j = Some bt ->
                      KernelData.kernel_data !! (0x80007568 + Z.of_nat j)%Z = Some bt).
    { intros j bt Hj.
      do 11 (destruct j as [|j];
             [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
      vm_compute in Hj; discriminate. }
    iPoseProof (kernel_data_string 0x80007568 "sleep lock"%string sl_str_addr eq_refl ltac:(unfold text_end; lia)
                                                                                      ltac:(vm_compute; discriminate) Hslstr
                  with "Hkdata") as "#Hstr_sl".
    (* ---- the frame geometry ---- *)
    assert (Hspr6 : spr = pa_stk sp0 6).
    { unfold spr, pa_stk, add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (iii_00 with "Htext") as "Hi00".
    iPoseProof (iii_02 with "Htext") as "Hi02".
    iPoseProof (iii_04 with "Htext") as "Hi04".
    iPoseProof (iii_06 with "Htext") as "Hi06".
    iPoseProof (iii_08 with "Htext") as "Hi08".
    iPoseProof (iii_0a with "Htext") as "Hi0a".
    iPoseProof (iii_0c with "Htext") as "Hi0c".
    iPoseProof (iii_0e with "Htext") as "Hi0e".
    iPoseProof (iii_12 with "Htext") as "Hi12".
    iPoseProof (iii_16 with "Htext") as "Hi16".
    iPoseProof (iii_1a with "Htext") as "Hi1a".
    iPoseProof (iii_1e with "Htext") as "Hi1e".
    iPoseProof (iii_22 with "Htext") as "Hi22".
    iPoseProof (iii_26 with "Htext") as "Hi26".
    iPoseProof (iii_2a with "Htext") as "Hi2a".
    iPoseProof (iii_2e with "Htext") as "Hi2e".
    iPoseProof (iii_32 with "Htext") as "Hi32".
    iPoseProof (iii_36 with "Htext") as "Hi36".
    (* ===== PROLOGUE: 6-slot frame push + save ra/s0/s1/s2/s3 ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    assert (Hpush : add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))) = pa_stk sp0 6)
      by (exact Hspr6).
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 61 : mword 6) m K 6 b ltac:(lia) Hpush
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & _)".
    iDestruct "S1" as (vra0) "Hc1". iDestruct "S2" as (vs00) "Hc2".
    iDestruct "S3" as (vs10) "Hc3". iDestruct "S4" as (vs20) "Hc4".
    iDestruct "S5" as (vs30) "Hc5".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.iinit + 0x02)) by (unfold pcE; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* the saved values are the ORIGINAL ra/s0/s1/s2/s3 *)
    assert (Hra_v : R1 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0_v : R1 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1_v : R1 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs2_v : R1 !!! Regidx s2i = m !!! Regidx s2i)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs3_v : R1 !!! Regidx s3i = m !!! Regidx s3i)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    (* +0x02 c.sdsp ra,40(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iinit + 0x02)) (mword_of_int 5 : mword 6) (mword_of_int 1 : mword 5)
              R1 (K - 6)%nat vra0 b with "Hcg Hpc Hi02 [Hc1]").
    { iEval (rewrite HspR1 Hb1). iExact "Hc1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hc1".
    iEval (rgne) in "Hc1". iEval (rewrite HspR1 Hb1 Hra_v) in "Hc1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.iinit + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.iinit + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,32(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iinit + 0x04)) (mword_of_int 4 : mword 6) (mword_of_int 8 : mword 5)
              R1 (K - 6)%nat vs00 b with "Hcg Hpc Hi04 [Hc2]").
    { iEval (rewrite HspR1 Hb2). iExact "Hc2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hc2".
    iEval (rgne) in "Hc2". iEval (rewrite HspR1 Hb2 Hs0_v) in "Hc2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.iinit + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.iinit + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,24(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iinit + 0x06)) (mword_of_int 3 : mword 6) (mword_of_int 9 : mword 5)
              R1 (K - 6)%nat vs10 b with "Hcg Hpc Hi06 [Hc3]").
    { iEval (rewrite HspR1 Hb3). iExact "Hc3". }
    iIntros (CID4 Hs4) "Hcg Hpc Hc3".
    iEval (rgne) in "Hc3". iEval (rewrite HspR1 Hb3 Hs1_v) in "Hc3".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.iinit + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.iinit + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp s2,16(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iinit + 0x08)) (mword_of_int 2 : mword 6) s2i
              R1 (K - 6)%nat vs20 b with "Hcg Hpc Hi08 [Hc4]").
    { iEval (rewrite HspR1 Hb4). iExact "Hc4". }
    iIntros (CID5 Hs5) "Hcg Hpc Hc4".
    iEval (rgne) in "Hc4". iEval (rewrite HspR1 Hb4 Hs2_v) in "Hc4".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.iinit + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.iinit + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.sdsp s3,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iinit + 0x0a)) (mword_of_int 1 : mword 6) s3i
              R1 (K - 6)%nat vs30 b with "Hcg Hpc Hi0a [Hc5]").
    { iEval (rewrite HspR1 Hb5). iExact "Hc5". }
    iIntros (CID6 Hs6) "Hcg Hpc Hc5".
    iEval (rgne) in "Hc5". iEval (rewrite HspR1 Hb5 Hs3_v) in "Hc5".
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.iinit + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.iinit + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c c.addi4spn s0,sp,48 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.iinit + 0x0c)) (Cregidx (mword_of_int 0)) (mword_of_int 12 : mword 8) (mword_of_int 8 : mword 5)
              R1 (K - 6)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> R1).
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.iinit + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.iinit + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* ===== a1 := &"itable", a0 := &itable (0x0e..0x1a) ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.iinit + 0x0e)) (mword_of_int 11 : mword 5) (mword_of_int 4 : mword 20)
              R2 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e").
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (R3 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.iinit + 0x0e) : mword 64) (auipc_off (mword_of_int 4 : mword 20)))]> R2).
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.iinit + 0x0e) : mword 64) 4 = mword_of_int (KernelSyms.iinit + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iinit + 0x12)) (mword_of_int 11 : mword 5) (mword_of_int 11 : mword 5) (mword_of_int 1028 : mword 12)
              R3 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (R4 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (R3 !!! Regidx (mword_of_int 11 : mword 5)) (sign_extend' 64 (mword_of_int 1028 : mword 12)))]> R3).
    assert (HR4a1 : R4 !!! Regidx (mword_of_int 11 : mword 5) = name_itable).
    { rewrite /R4 upd_eq. rewrite /R3 upd_eq. unfold name_itable, itable_name_str.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.iinit + 0x12) : mword 64) 4 = mword_of_int (KernelSyms.iinit + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.iinit + 0x16)) (mword_of_int 10 : mword 5) (mword_of_int 30 : mword 20)
              R4 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16").
    iIntros (CID10 Hs10) "Hcg Hpc".
    set (R5 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.iinit + 0x16) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> R4).
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.iinit + 0x16) : mword 64) 4 = mword_of_int (KernelSyms.iinit + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iinit + 0x1a)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 2220 : mword 12)
              R5 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (R6 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (R5 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 2220 : mword 12)))]> R5).
    assert (HR6a0 : R6 !!! Regidx (mword_of_int 10 : mword 5) = lk).
    { rewrite /R6 upd_eq. rewrite /R5 upd_eq. unfold lk, itable_addr, KernelSyms.itable.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HR6a1 : R6 !!! Regidx (mword_of_int 11 : mword 5) = name_itable).
    { rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [exact HR4a1 | vm_compute; discriminate]. }
    assert (HR6sp : R6 !!! Regidx csp_rs1 = spr).
    { rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [exact HspR1 | vm_compute; discriminate]. }
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.iinit + 0x1a) : mword 64) 4 = mword_of_int (KernelSyms.iinit + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* ===== jal initlock ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iinit + 0x1e)) (mword_of_int 1 : mword 5) (mword_of_int 2087662 : mword 21)
              R6 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1e").
    iIntros (CID12 Hs12) "Hcg Hpc".
    set (R7 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.iinit + 0x1e) : mword 64) 4)]> R6).
    assert (Htgtil : add_vec (mword_of_int (KernelSyms.iinit + 0x1e) : mword 64) (sign_extend' 64 (mword_of_int 2087662 : mword 21)) = mword_of_int KernelSyms.initlock)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtil) in "Hpc".
    assert (HR7a0 : R7 !!! Regidx (mword_of_int 10 : mword 5) = lk)
      by (rewrite /R7 upd_ne; [exact HR6a0 | vm_compute; discriminate]).
    assert (HR7a1 : R7 !!! Regidx (mword_of_int 11 : mword 5) = name_itable)
      by (rewrite /R7 upd_ne; [exact HR6a1 | vm_compute; discriminate]).
    assert (HR7sp : R7 !!! Regidx csp_rs1 = spr)
      by (rewrite /R7 upd_ne; [exact HR6sp | vm_compute; discriminate]).
    assert (HR7ra : R7 !!! Regidx (mword_of_int 1 : mword 5) = mword_of_int (KernelSyms.iinit + 0x22)).
    { rewrite /R7 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    (* the callee-saved registers iinit has not yet touched (tp, s1..s11) *)
    assert (HR7cs : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 8 -> c <> csp_rs1 -> R7 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N8 Nsp.
      pose proof (is_cs_idx_true_neq (mword_of_int 1 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Nra.
      pose proof (is_cs_idx_true_neq (mword_of_int 10 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na0.
      pose proof (is_cs_idx_true_neq (mword_of_int 11 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na1.
      rewrite /R7 upd_ne; [| congruence].
      rewrite /R6 upd_ne; [| congruence].
      rewrite /R5 upd_ne; [| congruence].
      rewrite /R4 upd_ne; [| congruence].
      rewrite /R3 upd_ne; [| congruence].
      rewrite /R2 upd_ne; [| congruence].
      rewrite /R1 upd_ne; [reflexivity | congruence]. }
    iApply (Initlock.wp_initlock_sconf KT1 R7 vlock vname vcpu "itable"%string (K - 6) b p
              ltac:(lia)
              with "Hcg Htext Hpc [] [Hlock] [Hname] [Hcpu]").
    { iEval (rewrite HR7a1). iExact "Hstr_itable". }
    { iEval (rewrite HR7a0). iExact "Hlock". }
    { iEval (rewrite HR7a0). iExact "Hname". }
    { iEval (rewrite HR7a0). iExact "Hcpu". }
    iIntros (CID13 Hs13 mil) "Hcg Hpc %Hilcs Hlock Hlname Hcpu".
    iEval (rewrite HR7a0) in "Hlock".
    iEval (rewrite HR7a0 HR7a1) in "Hlname".
    iMod (lock_name_intro with "Hstr_itable Hlname") as "#Hlnm".
    iEval (rewrite HR7a0) in "Hcpu".
    assert (Hpcil : ret_pc (R7 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.iinit + 0x22)).
    { rewrite HR7ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcil) in "Hpc".
    pose proof Hilcs as Hilcs_full.
    assert (Hilsp : mil !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hilcs_full csp_rs1 ltac:(vm_compute; reflexivity)); exact HR7sp).
    assert (Hilcs' : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 8 -> c <> csp_rs1 -> mil !!! Regidx c = m !!! Regidx c).
    { intros c Hc N8 Nsp.
      rewrite (callee_saved_lookup Hilcs_full c Hc). apply HR7cs; assumption. }
    (* ===== loop setup: s1 := &inode[0].lock, s3 := end, s2 := &"inode" ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.iinit + 0x22)) (mword_of_int 9 : mword 5) (mword_of_int 30 : mword 20)
              mil (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22").
    iIntros (CID14 Hs14) "Hcg Hpc".
    set (T1 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.iinit + 0x22) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> mil).
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.iinit + 0x22) : mword 64) 4 = mword_of_int (KernelSyms.iinit + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iinit + 0x26)) (mword_of_int 9 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 2248 : mword 12)
              T1 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26").
    iIntros (CID15 Hs15) "Hcg Hpc".
    set (T2 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec (T1 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 2248 : mword 12)))]> T1).
    assert (HT2s1 : T2 !!! Regidx (mword_of_int 9 : mword 5) = inode_lock 0).
    { rewrite /T2 upd_eq. rewrite /T1 upd_eq.
      unfold inode_lock, acur, inode_lock_base, inode_stride, KernelSyms.itable.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.iinit + 0x26) : mword 64) 4 = mword_of_int (KernelSyms.iinit + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2a) in "Hpc".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.iinit + 0x2a)) s3i (mword_of_int 31 : mword 20)
              T2 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2a").
    iIntros (CID16 Hs16) "Hcg Hpc".
    set (T3 := <[Regidx s3i := regval_into_reg (add_vec (mword_of_int (KernelSyms.iinit + 0x2a) : mword 64) (auipc_off (mword_of_int 31 : mword 20)))]> T2).
    assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.iinit + 0x2a) : mword 64) 4 = mword_of_int (KernelSyms.iinit + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iinit + 0x2e)) s3i s3i (mword_of_int 848 : mword 12)
              T3 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2e").
    iIntros (CID17 Hs17) "Hcg Hpc".
    set (T4 := <[Regidx s3i := regval_into_reg (add_vec (T3 !!! Regidx s3i) (sign_extend' 64 (mword_of_int 848 : mword 12)))]> T3).
    assert (HT4s3 : T4 !!! Regidx s3i = inode_lock NINODE).
    { rewrite /T4 upd_eq. rewrite /T3 upd_eq.
      unfold inode_lock, acur, inode_lock_base, inode_stride, NINODE, KernelSyms.itable.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.iinit + 0x2e) : mword 64) 4 = mword_of_int (KernelSyms.iinit + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.iinit + 0x32)) s2i (mword_of_int 4 : mword 20)
              T4 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi32").
    iIntros (CID18 Hs18) "Hcg Hpc".
    set (T5 := <[Regidx s2i := regval_into_reg (add_vec (mword_of_int (KernelSyms.iinit + 0x32) : mword 64) (auipc_off (mword_of_int 4 : mword 20)))]> T4).
    assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.iinit + 0x32) : mword 64) 4 = mword_of_int (KernelSyms.iinit + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp36) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iinit + 0x36)) s2i s2i (mword_of_int 1000: mword 12)
              T5 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi36").
    iIntros (CID19 Hs19) "Hcg Hpc".
    set (T6 := <[Regidx s2i := regval_into_reg (add_vec (T5 !!! Regidx s2i) (sign_extend' 64 (mword_of_int 1000 : mword 12)))]> T5).
    assert (HT6s2 : T6 !!! Regidx s2i = name_inode).
    { rewrite /T6 upd_eq. rewrite /T5 upd_eq. unfold name_inode, inode_name_str.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HT6s1 : T6 !!! Regidx (mword_of_int 9 : mword 5) = inode_lock 0).
    { rewrite /T6 upd_ne; [| vm_compute; discriminate].
      rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [exact HT2s1 | vm_compute; discriminate]. }
    assert (HT6s3 : T6 !!! Regidx s3i = inode_lock NINODE).
    { rewrite /T6 upd_ne; [| vm_compute; discriminate].
      rewrite /T5 upd_ne; [exact HT4s3 | vm_compute; discriminate]. }
    assert (HT6sp : T6 !!! Regidx csp_rs1 = spr).
    { rewrite /T6 upd_ne; [| vm_compute; discriminate].
      rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1 upd_ne; [exact Hilsp | vm_compute; discriminate]. }
    assert (HT6cs : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> s2i -> c <> s3i -> c <> csp_rs1 ->
              T6 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N8 N9 N18 N19 Nsp.
      rewrite /T6 upd_ne; [| congruence].
      rewrite /T5 upd_ne; [| congruence].
      rewrite /T4 upd_ne; [| congruence].
      rewrite /T3 upd_ne; [| congruence].
      rewrite /T2 upd_ne; [| congruence].
      rewrite /T1 upd_ne; [| congruence].
      apply Hilcs'; assumption. }
    assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.iinit + 0x36) : mword 64) 4 = mword_of_int (KernelSyms.iinit + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3a) in "Hpc".
    (* fold the lock's returned cells into the shape the loop hands on --
       [wp_next]-wrapped, since the ORIGINAL "Hcont" (wp_iinit_sconf's own)
       is generic in [b] and its wp_next stays deferred until [iinit_loop]'s
       exit arm resolves it. *)
    iAssert (wp_next (CID0 := CID) b p (fun (CID' : CpuId) =>
              ∀ mr, sie_cap_gpr KT1 mr K b p -∗ pc_is ret_tgt -∗ ⌜ callee_saved m mr ⌝ -∗
              ([∗ list] i ∈ seq 0 NINODE, sl_fresh (inode_lock i) "inode"%string) -∗
              WP (Loop : expr riscv_lang)))%I
      with "[Hcont Hlock Hcpu]" as "Hpost".
    { iIntros (CID' Hs' mr) "Hcg Hpc %Hcs Hfresh".
      iSpecialize ("Hcont" $! CID' with "[%]"); [exact Hs'|].
      iApply ("Hcont" $! mr with "Hcg Hpc [//] Hlock Hlnm Hcpu Hfresh"). }
    (* the loop is entered at the hart the loop-setup leaves migrated to
       (CID19); [Hpost] is still anchored at wp_iinit_sconf's own entry
       hart, so shift it there once before the call. *)
    assert (Hshift0 : b = false \/ p = zero_reg -> (CID19 : CPU) = (CID : CPU)) by wp_next_chain.
    iDestruct (wp_next_shift Hshift0 with "Hpost") as "Hpost".
    (* enter the loop at cursor 0 with NINODE units of fuel *)
    iApply (iinit_loop m K b p NINODE 0%nat T6 HK ltac:(lia) ltac:(unfold NINODE; lia)
              HT6s1 HT6s2 HT6s3 HT6sp HT6cs
              with "Hcg Htext Hstr_sl Hstr_inode Hpc [] [Hraws] Hc1 Hc2 Hc3 Hc4 Hc5 [S6] Hpost").
    { cbn [seq]. done. }
    { rewrite Nat.sub_0_r. iExact "Hraws". }
    { iDestruct "S6" as (v6) "Hc6". iExists _. iExact "Hc6". }
  Qed.

End ProofIinit.

End IinitProof.
