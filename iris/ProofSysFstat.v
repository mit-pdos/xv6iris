(* ProofSysFstat.v -- whole-function WP for sys_fstat(), the FIRST syscall
   shell over the B2-converted file.c contracts (fs-sysfile S4c).

     uint64 sys_fstat(void) {
       struct file *f;
       uint64 st;
       argaddr(1, &st);
       if (argfd(0, 0, &f) < 0) return -1;
       return filestat(f, st);
     }

   Twenty-one instructions; CodeSysFstat.v has the listing and SpecSysFstat.v
   the shape notes.  Three things are worth stating here because they are what
   this file demonstrates, and sys_read and sys_write repeat all three:

   * THE B1 SEAM, and it needs no new lemma.  filestat takes
     [proc_priv_core], not [proc_priv], and the reference it needs is INSIDE
     the descriptor array of the very block it is being handed.
     [ProcInv.proc_priv_lend] takes the block apart at the descriptor argfd
     resolved, [proc_ofiles_repay] settles the loan when filestat returns and
     [proc_priv_join] puts the block back.  The [upd_upt] crossing is free:
     [pv_ofile (upd_upt V P') = pv_ofile V] by [cbn], so the deficit the loan
     opened is literally the deficit the repayment closes even though
     filestat handed the core back at an EXTENDED page table.

   * THE ENVIRONMENT IS OWNED, NOT OPENED.  Because [filestat_fs_env] is now
     content-independent (S4'), this syscall simply HOLDS it and hands over
     whichever of the two arms the file's type selects ([sfs_env_frame],
     below, is [SpecFileclose.fileclose_env_frame]'s move).  The wand-shaped
     "opener" S4 froze is gone, and with it the unsatisfiable promise to
     return a [file_ref] at a smaller fraction.

   * THE ERROR RETURN IS HOISTED, so the epilogue is ONE lemma.  [c.li a0,-1]
     at +0x20 runs BEFORE the branch, and nothing between there and +0x32
     touches a0 on the failure arm -- so [sfs_tail] is parameterized by the
     value the arm left in a0 rather than duplicated.  (sys_close does the
     same with a5 and needs a [c.mv] on the join; sys_fstat does not, because
     the hoisted constant is already in the return register.) *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
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
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSmodeIntr.
Require Import IntrDefs HartTp WpNext WpLock.
Require Import ProcGeom CpuOwn.
Require Import ProcInv.
Require Import FdSlots ProcInv.
Require Import ProofKforkParts.
Require Import FileInvDefs.
Require Import KallocInv.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import WpUart.
Require Import DiskPtsto.
Require Import BioDefs.
Require Import FsBlocks LogInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import SpecArgfd SpecArgaddr SpecFilestat.
Require Import SpecSysFstat.
Require Import CodeSysFstat.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Import Defs.
Local Open Scope Z_scope.

(* a failing tactic in a whole-function WP over [proc_priv] otherwise spends
   tens of minutes formatting the goal (durable-notes) *)
Set Printing Depth 40.

(* ===================================================================== *)
(*  Pure arithmetic: the frame and the two local addresses.               *)
(* ===================================================================== *)

(* the record-eta step: nothing on the -1 path touches the page table *)
Lemma sfs_upd_upt_id (V : pprivate) : upd_upt V (pv_upt V) = V.
Proof. destruct V; reflexivity. Qed.

(* [c.addi4spn s0,sp,32] takes the 32-byte push straight back: s0 IS the
   entry sp.  Verbatim [ProofSysClose.sc_s0_entry] -- the two functions have
   the same frame. *)
Lemma sfs_s0_entry (X : mword 64) :
  add_vec (pa_stk X 4) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))) = X.
Proof.
  rewrite <- stk_push_32. apply frame_cancel.
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* [addi a1,s0,-32] / [ld a1,-32(s0)] : &st, the whole of frame slot 4 *)
Lemma sfs_addr_st (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 0xfe0 : mword 12)) = pa_stk X 4.
Proof.
  unfold pa_stk, add_vec_int. apply f_equal.
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* [addi a2,s0,-24] / [ld a0,-24(s0)] : &f, the whole of frame slot 3.
   sys_close's [f] is slot 4 and its [int fd] the upper word of slot 3;
   sys_fstat's two locals are the other way round and BOTH are full words,
   which is why nothing here needs [word_pointsto_split4]. *)
Lemma sfs_addr_f (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 0xfe8 : mword 12)) = pa_stk X 3.
Proof.
  unfold pa_stk, add_vec_int. apply f_equal.
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* ...and slot 3 is 8 bytes above the frame base, the form the non-null
   argument needs ([StackOwn.stack_off_nonzero] is anchored at sp). *)
Lemma sfs_addr_f_base (X : mword 64) :
  pa_stk X 3 = add_vec_int (pa_stk X 4) 8.
Proof. unfold pa_stk. rewrite avi_assoc. f_equal; lia. Qed.

Module SysFstatProof (Argaddr : ARGADDR) (Argfd : ARGFD)
                     (Filestat : FILESTAT) : SYSFSTAT.

Section ProofSysFstat.
  (* NO [!icacheG Σ]: [fileG] bundles it (SpecFilestat.v's note, and the
     trap that cost S4' the most). *)
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !irefslotG Σ, !pavG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.

  (* THE CARVE THIS READS IS ARM-DEPENDENT, hence the [0 < k] premise --
     [ProofSysClose.sc_sp_bounds]'s note verbatim. *)
  Lemma sfs_sp_bounds `{CID0 : CpuId} (mm : regfile) (kk : nat)
      (b : bool) (pp : mword 64) :
    (0 < kk)%nat ->
    sie_cap_gpr mm kk b pp -∗
    ⌜(8 <= uint (mm !!! Regidx csp_rs1) < 274877906944 + 8)%Z⌝.
  Proof.
    iIntros (Hk) "(_ & _ & (Hstk & _ & _) & _)".
    iApply (stack_own_sp_bounds _ (trap_res b + kk)%nat with "Hstk").
    destruct b; unfold trap_res, kv_frame_slots; lia.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  HAND OVER WHICHEVER ARM THE TYPE SELECTS, AND KEEP THE OTHER.       *)
  (* ------------------------------------------------------------------- *)
  (* This is the whole of what S4's "descriptor environment" opener was
     trying to be, and it is a one-liner now that [filestat_fs_env] does not
     mention the content: the syscall owns the bundle, filestat's [if]
     decides whether it is consumed, and either way [filestat_fs_out] comes
     back -- on the [emp] branch out of the bundle the syscall still holds
     ([filestat_fs_env_out]), on the other out of filestat's own post. *)
  Local Lemma sfs_env_frame (fn : fstat_names) (Cf : fcontent) :
    filestat_fs_env fn -∗
    filestat_env fn Cf ∗ (filestat_env_out fn Cf -∗ filestat_fs_out fn).
  Proof.
    rewrite /filestat_env /filestat_env_out. case_decide.
    - iIntros "H". iSplitL "H"; [iExact "H"|]. iIntros "$".
    - iIntros "H". iSplitR; [done|]. iIntros "_".
      iApply (filestat_fs_env_out with "H").
  Qed.

  (* =================================================================== *)
  (*  The shared tail at +0x32: the epilogue, over whatever is in a0.     *)
  (* =================================================================== *)
  (* A DECOMPOSED helper (porting guide): its own fresh [CID0] binder -- it
     is entered at a MIGRATED hart -- its own [b] and [pp], and its
     continuation wrapped in [wp_next].  It does NOT carry [cpu_own]: the
     epilogue never touches it, so the caller transports it afterwards. *)
  Lemma sfs_tail `{CID0 : CpuId}
      (m Mt : regfile) (av : nat) (rv : mword 64)
      (sp0 ra0 s00 : mword 64) (w3 w4 : bv 64) (b : bool) (pp : mword 64) :
    (4 <= av)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 4 ->
    Mt !!! Regidx Ra0 = rv ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr Mt (av - 4)%nat b pp -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.sys_fstat + 0x32) : mword 64) -∗
    word_pointsto (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (pa_stk sp0 3) (DfracOwn 1) w3 -∗
    word_pointsto (pa_stk sp0 4) (DfracOwn 1) w4 -∗
    wp_next (CID0 := CID0) b pp (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf /\ mf !!! Regidx Ra0 = rv⌝ -∗
        sie_cap_gpr mf av b pp -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hav Hsp0 Hra0 Hs00 Hmtsp Hmta0 Hthr.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hb3 Hb4 Hcont".
    iPoseProof (sfsi_32 with "Htext") as "Hi32".
    iPoseProof (sfsi_34 with "Htext") as "Hi34".
    iPoseProof (sfsi_36 with "Htext") as "Hi36".
    iPoseProof (sfsi_38 with "Htext") as "Hi38".
    (* ---- +0x32: c.ldsp ra,24(sp) ---- *)
    assert (Hpa1 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hmtsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_fstat + 0x32))
              (mword_of_int 3 : mword 6) Rra Mt (av - 4)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi32 Hb1").
    iIntros (CID1 Hs1) "Hcg Hpc Hb1".
    iEval (rewrite Hpa1) in "Hb1".
    set (T1 := <[Regidx Rra := regval_into_reg ra0]> Mt).
    change (<[Regidx Rra := regval_into_reg ra0]> Mt) with T1.
    assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.sys_fstat + 0x32) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_fstat + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp34) in "Hpc".
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T1 upd_ne; [exact Hmtsp | reg_neq]).
    (* ---- +0x34: c.ldsp s0,16(sp) ---- *)
    assert (Hpa2 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HT1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sys_fstat + 0x34))
              (mword_of_int 2 : mword 6) Rs0 T1 (av - 4)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi34 Hb2").
    iIntros (CID2 Hs2) "Hcg Hpc Hb2".
    iEval (rewrite Hpa2) in "Hb2".
    set (T2 := <[Regidx Rs0 := regval_into_reg s00]> T1).
    change (<[Regidx Rs0 := regval_into_reg s00]> T1) with T2.
    assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.sys_fstat + 0x34) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_fstat + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp36) in "Hpc".
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T2 upd_ne; [exact HT1sp | reg_neq]).
    (* ---- +0x36: c.addi16sp sp,32 (frame pop) ---- *)
    assert (Hwv : add_vec (T2 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HT2sp. rewrite <- stk_push_32. apply frame_cancel.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpop : T2 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T2 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4)
      by (rewrite Hwv; exact HT2sp).
    iDestruct (stack_own_4_intro sp0 ra0 s00 w3 w4 with "Hb1 Hb2 Hb3 Hb4") as "Hframe".
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.sys_fstat + 0x36))
              (mword_of_int 2 : mword 6) T2 (av - 4)%nat 4 b Hpop
              with "Hcg Hpc Hi36 Hframe").
    iIntros (CID3 Hs3) "Hcg Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.sys_fstat + 0x36) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_fstat + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp38) in "Hpc".
    set (T3 := <[Regidx csp_rs1 := regval_into_reg (add_vec (T2 !!! Regidx csp_rs1)
                  (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> T2).
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (T2 !!! Regidx csp_rs1)
              (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> T2) with T3.
    (* ---- +0x38: c.ret ---- *)
    assert (HT3ra : T3 !!! Regidx Rra = ra0).
    { rewrite /T3 upd_ne; [| reg_neq].
      rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.sys_fstat + 0x38))
              Rra T3 av b ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi38").
    iIntros (CID4 Hs4) "Hcg Hpc".
    iEval (rgne; rewrite HT3ra) in "Hpc".
    (* ---- the postcondition ---- *)
    assert (HT3sp : T3 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite /T3 upd_eq Hwv; symmetry; exact Hsp0).
    assert (HT3s0 : T3 !!! Regidx Rs0 = m !!! Regidx Rs0).
    { rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_eq. symmetry; exact Hs00. }
    assert (HT3a0 : T3 !!! Regidx Ra0 = rv).
    { rewrite /T3 upd_ne; [| reg_neq].
      rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_ne; [| reg_neq]. exact Hmta0. }
    assert (Hthr3 : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> T3 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /T3 upd_ne; [| congruence].
      rewrite /T2 upd_ne; [| congruence].
      rewrite /T1 upd_ne; [| congruence].
      apply Hthr; assumption. }
    iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain|].
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

  (* =================================================================== *)
  (*  THE CAPSTONE.                                                       *)
  (* =================================================================== *)
  Lemma wp_sys_fstat_sconf
      (γa γf : gname) (γs : list gname) (j : nat) (γlp : gname)
      (fn : fstat_names) (pidv : mword 32) (V : pprivate) (v : mword 64)
      (m : regfile) (av : nat) (eb : bool) (b : bool) (lks : gset string)
    : wp_sys_fstat_sconf_body γa γf γs j γlp fn pidv V v m av eb b lks.
  Proof.
    cbv beta delta [wp_sys_fstat_sconf_body].
    intros pcE pj ret_tgt Hav Hj Hgs Hlens Harg0 Harg1 Heb.
    (* BOTH budgets, or [lia] cannot see past [filestat_stack] -- it is an
       expression, not a literal, on purpose (SpecSysFstat.v). *)
    unfold sys_fstat_stack, filestat_stack in Hav.
    (* the push_off bound, with [2^31] evaluated by hand: [lia] cannot reduce
       a power (durable-notes.md). *)
    assert (Hnoff : (Z.of_nat 0 + 1 < 2 ^ 31)%Z)
      by (change (2 ^ 31)%Z with 2147483648%Z; lia).
    destruct Harg1 as [v1 Harg1].
    set (sp0 := m !!! Regidx csp_rs1).
    set (ra0 := m !!! Regidx Rra).
    set (s00 := m !!! Regidx Rs0).
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    (* [KvmSpec.kalloc_env γa None] IS PERSISTENT (durable-notes.md): filestat
       consumes it and does not give it back, and this contract's post owes it
       -- so it must be introduced with [#], not threaded. *)
    iIntros "Hcg Hcpu #Htext #Hdata Hpc #Hpanic Hpriv #Hkenv #Hprocs Henv Hcont".
    (* depth 0 forces the held set empty, so this body needs no order
       premise of its own -- every [locks_below] its callees raise is
       [locks_below ∅ _], which [lkbelow] closes outright. *)
    iDestruct (cpu_own_zero_empty with "Hcpu") as "[%Hlkempty Hcpu]".
    (* PIN THE INDEX.  [eb = true] plus [cpu_own_eb_agree] at level 0 makes
       [b] the literal [true], which is what lets argaddr's and argfd's
       [wp_next b] crossings meet filestat's and this contract's [wp_next
       true]. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcpu") as %Hbm.
    assert (Hb : b = true) by (rewrite -Hbm; exact Heb).
    iPoseProof (sfsi_00 with "Htext") as "Hi00".
    iPoseProof (sfsi_02 with "Htext") as "Hi02".
    iPoseProof (sfsi_04 with "Htext") as "Hi04".
    iPoseProof (sfsi_06 with "Htext") as "Hi06".
    iPoseProof (sfsi_08 with "Htext") as "Hi08".
    iPoseProof (sfsi_0c with "Htext") as "Hi0c".
    iPoseProof (sfsi_0e with "Htext") as "Hi0e".
    iPoseProof (sfsi_12 with "Htext") as "Hi12".
    iPoseProof (sfsi_16 with "Htext") as "Hi16".
    iPoseProof (sfsi_18 with "Htext") as "Hi18".
    iPoseProof (sfsi_1a with "Htext") as "Hi1a".
    iPoseProof (sfsi_1e with "Htext") as "Hi1e".
    iPoseProof (sfsi_20 with "Htext") as "Hi20".
    iPoseProof (sfsi_22 with "Htext") as "Hi22".
    iPoseProof (sfsi_26 with "Htext") as "Hi26".
    iPoseProof (sfsi_2a with "Htext") as "Hi2a".
    iPoseProof (sfsi_2e with "Htext") as "Hi2e".
    (* ---- +0x00: c.addi sp,-32 (frame push) ---- *)
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m av 4 b
              ltac:(lia) (stk_push_32 (m !!! Regidx csp_rs1))
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.sys_fstat + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /M1 upd_eq; apply stk_push_32).
    iDestruct (stack_own_4_elim with "Hframe") as (u1 u2 w3 w4) "(Hs1 & Hs2 & Hs3 & Hs4)".
    (* ---- +0x02: c.sdsp ra,24(sp) ---- *)
    assert (Hpa1 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa2 : add_vec (M1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HM1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa1) in "Hs1".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sys_fstat + 0x02))
              (mword_of_int 3 : mword 6) Rra M1 (av - 4)%nat u1 b
              with "Hcg Hpc Hi02 Hs1").
    iIntros (CID2 Hs2) "Hcg Hpc Hs1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.sys_fstat + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_fstat + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- +0x04: c.sdsp s0,16(sp) ---- *)
    iEval (rewrite -Hpa2) in "Hs2".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sys_fstat + 0x04))
              (mword_of_int 2 : mword 6) Rs0 M1 (av - 4)%nat u2 b
              with "Hcg Hpc Hi04 Hs2").
    iIntros (CID3 Hs3) "Hcg Hpc Hs2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.sys_fstat + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_fstat + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    assert (HM1ra : forall CID' : CpuId, rget (CID := CID') M1 Rra = ra0).
    { intros CID'; rgne. rewrite /M1 upd_ne; [reflexivity | reg_neq]. }
    assert (HM1s0 : forall CID' : CpuId, rget (CID := CID') M1 Rs0 = s00).
    { intros CID'; rgne. rewrite /M1 upd_ne; [reflexivity | reg_neq]. }
    iEval (rewrite Hpa1 HM1ra) in "Hs1".
    iEval (rewrite Hpa2 HM1s0) in "Hs2".
    (* ---- +0x06: c.addi4spn s0,sp,32 -- s0 := the entry sp ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.sys_fstat + 0x06))
              (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) Rs0
              M1 (av - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06").
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (M2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1).
    change (<[Regidx Rs0 := regval_into_reg
              (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1) with M2.
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.sys_fstat + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_fstat + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    assert (HM2s0 : M2 !!! Regidx Rs0 = sp0).
    { rewrite /M2 upd_eq HM1sp. apply sfs_s0_entry. }
    assert (HM2sp : M2 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /M2 upd_ne; [exact HM1sp | reg_neq]).
    (* ---- +0x08: addi a1,s0,-32 -- a1 := &st ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sys_fstat + 0x08))
              Ra1 Rs0 (mword_of_int 0xfe0 : mword 12) M2 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (M3 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (rget M2 Rs0) (sign_extend' 64 (mword_of_int 0xfe0 : mword 12)))]> M2).
    change (<[Regidx Ra1 := regval_into_reg
              (add_vec (rget M2 Rs0) (sign_extend' 64 (mword_of_int 0xfe0 : mword 12)))]> M2) with M3.
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.sys_fstat + 0x08) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_fstat + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    assert (HM3a1 : M3 !!! Regidx Ra1 = pa_stk sp0 4).
    { rewrite /M3 upd_eq. rgne. rewrite HM2s0. apply sfs_addr_st. }
    assert (HM3s0 : M3 !!! Regidx Rs0 = sp0)
      by (rewrite /M3 upd_ne; [exact HM2s0 | reg_neq]).
    assert (HM3sp : M3 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /M3 upd_ne; [exact HM2sp | reg_neq]).
    (* ---- +0x0c: c.li a0,1 -- the argument index ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_fstat + 0x0c))
              Ra0 (mword_of_int 1 : mword 6)
              (mword_of_int (Z.of_nat 1) : mword 64) M3 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi0c").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (M4 := <[Regidx Ra0 := regval_into_reg (mword_of_int (Z.of_nat 1) : mword 64)]> M3).
    change (<[Regidx Ra0 := regval_into_reg (mword_of_int (Z.of_nat 1) : mword 64)]> M3) with M4.
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.sys_fstat + 0x0c) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_fstat + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* ---- +0x0e: jal ra,argaddr ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_fstat + 0x0e))
              Rra (mword_of_int 2087508 : mword 21) M4 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0e").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (M5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.sys_fstat + 0x0e) : mword 64) 4)]> M4).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.sys_fstat + 0x0e) : mword 64) 4)]> M4) with M5.
    assert (Hjaa : add_vec (mword_of_int (KernelSyms.sys_fstat + 0x0e) : mword 64)
                     (sign_extend' 64 (mword_of_int 2087508 : mword 21)) = mword_of_int KernelSyms.argaddr)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjaa) in "Hpc".
    assert (HM5a0 : M5 !!! Regidx Ra0 = mword_of_int (Z.of_nat 1)).
    { rewrite /M5 upd_ne; [| reg_neq]. rewrite /M4 upd_eq. reflexivity. }
    assert (HM5a1 : M5 !!! Regidx Ra1 = pa_stk sp0 4).
    { rewrite /M5 upd_ne; [| reg_neq]. rewrite /M4 upd_ne; [| reg_neq]. exact HM3a1. }
    assert (HM5s0 : M5 !!! Regidx Rs0 = sp0).
    { rewrite /M5 upd_ne; [| reg_neq]. rewrite /M4 upd_ne; [| reg_neq]. exact HM3s0. }
    assert (HM5sp : M5 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite /M5 upd_ne; [| reg_neq]. rewrite /M4 upd_ne; [| reg_neq]. exact HM3sp. }
    assert (HM5ra : M5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.sys_fstat + 0x0e) : mword 64) 4)
      by (rewrite /M5 upd_eq; reflexivity).
    (* argaddr wants the trapframe pointer fraction and the page, out of the
       block; the wand puts both back the instant it returns. *)
    iDestruct (proc_priv_tfp_valid with "Hpriv") as %Hpv.
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfc & Htfp & Hpback)".
    iEval (rewrite -HM5a1) in "Hs4".
    iDestruct (cpu_own_transport CID CID7 0%nat eb pj b ltac:(rewrite Hb; wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (Argaddr.wp_argaddr_sconf M5 (av - 4)%nat 0%nat eb pj 1%nat
              (ud_tfp (pv_upt V)) (pv_tf V) v1 w4 (DfracOwn (1/4)) b lks
              ltac:(unfold NARG; lia) HM5a0 Harg1 Hnoff
              ltac:(unfold argaddr_stack; lia) Hpv
              with "Hcg Hcpu Htext Hdata Hpc Htfc Htfp Hs4").
    iIntros (CID8 Hs8 A0) "%HcsA0 Hcg Hcpu Hpc Htfc Htfp Hs4".
    iEval (rewrite HM5a1) in "Hs4".
    iDestruct ("Hpback" with "Htfc Htfp") as "Hpriv".
    assert (Hpc12 : ret_pc (M5 !!! Regidx Rra)
                    = mword_of_int (KernelSyms.sys_fstat + 0x12))
      by (rewrite HM5ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    assert (HA0s0 : A0 !!! Regidx Rs0 = sp0)
      by (rewrite (callee_saved_lookup HcsA0 Rs0 ltac:(vm_compute; reflexivity)); exact HM5s0).
    assert (HA0sp : A0 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite (callee_saved_lookup HcsA0 csp_rs1 ltac:(vm_compute; reflexivity)); exact HM5sp).
    (* ---- +0x12: addi a2,s0,-24 -- a2 := &f ---- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.sys_fstat + 0x12))
              Ra2 Rs0 (mword_of_int 0xfe8 : mword 12) A0 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (N1 := <[Regidx Ra2 := regval_into_reg
                  (add_vec (rget A0 Rs0) (sign_extend' 64 (mword_of_int 0xfe8 : mword 12)))]> A0).
    change (<[Regidx Ra2 := regval_into_reg
              (add_vec (rget A0 Rs0) (sign_extend' 64 (mword_of_int 0xfe8 : mword 12)))]> A0) with N1.
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.sys_fstat + 0x12) : mword 64) 4
                    = mword_of_int (KernelSyms.sys_fstat + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    assert (HN1a2 : N1 !!! Regidx Ra2 = pa_stk sp0 3).
    { rewrite /N1 upd_eq. rgne. rewrite HA0s0. apply sfs_addr_f. }
    assert (HN1s0 : N1 !!! Regidx Rs0 = sp0)
      by (rewrite /N1 upd_ne; [exact HA0s0 | reg_neq]).
    assert (HN1sp : N1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /N1 upd_ne; [exact HA0sp | reg_neq]).
    (* ---- +0x16: c.li a1,0 -- pfd = NULL ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_fstat + 0x16))
              Ra1 (mword_of_int 0 : mword 6) (zero_reg : mword 64) N1 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi16").
    iIntros (CID10 Hs10) "Hcg Hpc".
    set (N2 := <[Regidx Ra1 := regval_into_reg (zero_reg : mword 64)]> N1).
    change (<[Regidx Ra1 := regval_into_reg (zero_reg : mword 64)]> N1) with N2.
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.sys_fstat + 0x16) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_fstat + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* ---- +0x18: c.li a0,0 -- the argument index ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_fstat + 0x18))
              Ra0 (mword_of_int 0 : mword 6)
              (mword_of_int (Z.of_nat 0) : mword 64) N2 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi18").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (N3 := <[Regidx Ra0 := regval_into_reg (mword_of_int (Z.of_nat 0) : mword 64)]> N2).
    change (<[Regidx Ra0 := regval_into_reg (mword_of_int (Z.of_nat 0) : mword 64)]> N2) with N3.
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.sys_fstat + 0x18) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_fstat + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* ---- +0x1a: jal ra,argfd ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_fstat + 0x1a))
              Rra (mword_of_int 2096328 : mword 21) N3 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1a").
    iIntros (CID12 Hs12) "Hcg Hpc".
    set (N4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.sys_fstat + 0x1a) : mword 64) 4)]> N3).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KernelSyms.sys_fstat + 0x1a) : mword 64) 4)]> N3) with N4.
    assert (Hjafd : add_vec (mword_of_int (KernelSyms.sys_fstat + 0x1a) : mword 64)
                      (sign_extend' 64 (mword_of_int 2096328 : mword 21)) = mword_of_int KernelSyms.argfd)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjafd) in "Hpc".
    assert (HN4a0 : N4 !!! Regidx Ra0 = mword_of_int (Z.of_nat 0)).
    { rewrite /N4 upd_ne; [| reg_neq]. rewrite /N3 upd_eq. reflexivity. }
    assert (HN4a1 : N4 !!! Regidx Ra1 = (zero_reg : mword 64)).
    { rewrite /N4 upd_ne; [| reg_neq]. rewrite /N3 upd_ne; [| reg_neq].
      rewrite /N2 upd_eq. reflexivity. }
    assert (HN4a2 : N4 !!! Regidx Ra2 = pa_stk sp0 3).
    { rewrite /N4 upd_ne; [| reg_neq]. rewrite /N3 upd_ne; [| reg_neq].
      rewrite /N2 upd_ne; [| reg_neq]. exact HN1a2. }
    assert (HN4s0 : N4 !!! Regidx Rs0 = sp0).
    { rewrite /N4 upd_ne; [| reg_neq]. rewrite /N3 upd_ne; [| reg_neq].
      rewrite /N2 upd_ne; [| reg_neq]. exact HN1s0. }
    assert (HN4sp : N4 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite /N4 upd_ne; [| reg_neq]. rewrite /N3 upd_ne; [| reg_neq].
      rewrite /N2 upd_ne; [| reg_neq]. exact HN1sp. }
    assert (HN4ra : N4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.sys_fstat + 0x1a) : mword 64) 4)
      by (rewrite /N4 upd_eq; reflexivity).
    (* [pf] is not null: the frame's own geometry, no assumption about where
       the kernel stack lives. *)
    assert (Hkpos : (0 < (av - 4)%nat)%nat) by lia.
    iDestruct (sfs_sp_bounds _ _ _ _ Hkpos with "Hcg") as %Hspb.
    rewrite HN4sp in Hspb.
    assert (Hnzf : N4 !!! Regidx Ra2 <> (zero_reg : mword 64)).
    { rewrite HN4a2 sfs_addr_f_base. apply stack_off_nonzero; [exact Hspb | lia]. }
    iEval (rewrite -HN4a2) in "Hs3".
    iDestruct (cpu_own_transport CID8 CID12 0%nat eb pj b ltac:(rewrite Hb; wp_next_chain)
                 with "Hcpu") as "Hcpu".
    (* ---- argfd(0, 0, &f).  [pfd] IS NULL and carries no resource --
       [SpecArgfd.ofd_out_null] is exactly this case. ---- *)
    iApply (Argfd.wp_argfd_sconf γf N4 (av - 4)%nat 0%nat eb pj 0%nat v
              pidv V (bv_0 32) w3 b lks
              ltac:(unfold NARG; lia) HN4a0 Harg0 Hnzf Hnoff
              ltac:(unfold argfd_stack; lia)
              with "Hcg Hcpu Htext Hdata Hpc Hpriv [] Hs3").
    { iApply (ofd_out_null _ _ HN4a1). }
    iIntros (CID13 Hs13 A) "%HcsA Hcg Hcpu Hpc Hpriv Hpost".
    assert (Hpc1e : ret_pc (N4 !!! Regidx Rra)
                    = mword_of_int (KernelSyms.sys_fstat + 0x1e))
      by (rewrite HN4ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1e) in "Hpc".
    (* ---- +0x1e: c.mv a5,a0 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sys_fstat + 0x1e))
              Ra5 Ra0 A (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e").
    iIntros (CID14 Hs14) "Hcg Hpc".
    set (A1 := <[Regidx Ra5 := regval_into_reg (add_vec zero_reg (rget A Ra0))]> A).
    change (<[Regidx Ra5 := regval_into_reg (add_vec zero_reg (rget A Ra0))]> A) with A1.
    assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.sys_fstat + 0x1e) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_fstat + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    assert (HA1a5 : A1 !!! Regidx Ra5 = A !!! Regidx Ra0).
    { rewrite /A1 upd_eq. rgne. apply add_vec_zero_l. }
    (* ---- +0x20: c.li a0,-1 (the error return, HOISTED above the branch) ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.sys_fstat + 0x20))
              Ra0 (mword_of_int 63 : mword 6)
              (mword_of_int (-1) : mword 64) A1 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi20").
    iIntros (CID15 Hs15) "Hcg Hpc".
    set (A2 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> A1).
    change (<[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> A1) with A2.
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.sys_fstat + 0x20) : mword 64) 2
                    = mword_of_int (KernelSyms.sys_fstat + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    assert (HA2a0 : A2 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64))
      by (rewrite /A2 upd_eq; reflexivity).
    assert (HA2a5 : A2 !!! Regidx Ra5 = A !!! Regidx Ra0)
      by (rewrite /A2 upd_ne; [exact HA1a5 | reg_neq]).
    assert (HA2sp : A2 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite /A2 upd_ne; [| reg_neq]. rewrite /A1 upd_ne; [| reg_neq].
      rewrite (callee_saved_lookup HcsA csp_rs1 ltac:(vm_compute; reflexivity)). exact HN4sp. }
    assert (HA2s0 : A2 !!! Regidx Rs0 = sp0).
    { rewrite /A2 upd_ne; [| reg_neq]. rewrite /A1 upd_ne; [| reg_neq].
      rewrite (callee_saved_lookup HcsA Rs0 ltac:(vm_compute; reflexivity)). exact HN4s0. }
    (* the residual threading fact both arms hand on *)
    assert (HthrA : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> A2 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8.
      assert (N15 : r <> mword_of_int 15)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N1' : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N11 : r <> mword_of_int 11)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N12 : r <> mword_of_int 12)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /A2 upd_ne; [| congruence].
      rewrite /A1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup HcsA r Hr).
      rewrite /N4 upd_ne; [| congruence].
      rewrite /N3 upd_ne; [| congruence].
      rewrite /N2 upd_ne; [| congruence].
      rewrite /N1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup HcsA0 r Hr).
      rewrite /M5 upd_ne; [| congruence].
      rewrite /M4 upd_ne; [| congruence].
      rewrite /M3 upd_ne; [| congruence].
      rewrite /M2 upd_ne; [| congruence].
      rewrite /M1 upd_ne; [| congruence]. reflexivity. }
    (* ---- +0x22: blt a5,x0 -- the two arms ---- *)
    rewrite /argfd_post. iDestruct "Hpost" as "[Hfail | Hsucc]".
    - (* ================= FAILURE: argfd returned -1 ================= *)
      iDestruct "Hfail" as "([%Hr %Hnone] & _ & Hfcell)".
      assert (HA2a5' : A2 !!! Regidx Ra5 = (mword_of_int (-1) : mword 64))
        by (rewrite HA2a5; exact Hr).
      iApply (wp_blt_x0_taken_s_sconf (mword_of_int (KernelSyms.sys_fstat + 0x22))
                (mword_of_int 16 : mword 13) Ra5 A2 (av - 4)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HA2a5'; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi22").
      iNext. iIntros (CID16 Hs16) "Hcg Hpc".
      assert (Htgt32 : add_vec (mword_of_int (KernelSyms.sys_fstat + 0x22) : mword 64)
                (sign_extend' 64 (mword_of_int 16 : mword 13))
                = mword_of_int (KernelSyms.sys_fstat + 0x32))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt32) in "Hpc".
      iEval (rewrite HN4a2) in "Hfcell".
      iApply (sfs_tail (CID0 := CID16) m A2 av (mword_of_int (-1) : mword 64)
                sp0 ra0 s00 _ _ b pj
                ltac:(lia) eq_refl eq_refl eq_refl HA2sp HA2a0 HthrA
                with "Hcg Htext Hpc Hs1 Hs2 Hfcell Hs4").
      iIntros (CID17 Hs17 mf) "[%Hcsf %Hmfa0] Hcg Hpc".
      iDestruct (cpu_own_transport CID13 CID17 0%nat eb pj b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcpu") as "Hcpu".
      iSpecialize ("Hcont" $! CID17 with "[%]"); [wp_next_chain|].
      (* nothing ran, so the page table is its own extension *)
      iApply ("Hcont" $! mf (mword_of_int (-1) : mword 64) (pv_upt V)
                with "[%] [%] [%] [%] Hcg Hcpu Hpc [Hpriv] Hkenv [Henv]").
      { exact Hcsf. }
      { apply uptd_ext_refl. }
      { left. split; [reflexivity | exact Hnone]. }
      { exact Hmfa0. }
      { rewrite sfs_upd_upt_id. iExact "Hpriv". }
      { iApply (filestat_fs_env_out with "Henv"). }
    - (* ================= SUCCESS: the descriptor resolved ============= *)
      iDestruct "Hsucc" as (fd fv) "([%Hr %Hsome] & _ & Hfcell)".
      pose proof (arg_fd_lookup v (pv_ofile V) fd fv Hsome)
        as (Hfdlt & Hlk & Hfvnz & _).
      assert (HA2a5' : A2 !!! Regidx Ra5 = (zero_reg : mword 64))
        by (rewrite HA2a5; exact Hr).
      iApply (wp_blt_x0_fall_s_sconf (mword_of_int (KernelSyms.sys_fstat + 0x22))
                (mword_of_int 16 : mword 13) Ra5 A2 (av - 4)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HA2a5'; vm_compute; reflexivity)
                with "Hcg Hpc Hi22").
      iIntros (CID16 Hs16) "Hcg Hpc".
      assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.sys_fstat + 0x22) : mword 64) 4
                      = mword_of_int (KernelSyms.sys_fstat + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp26) in "Hpc".
      (* ---- +0x26: ld a1,-32(s0) -- reload st ---- *)
      assert (Haddrst : forall CID' : CpuId,
                add_vec (rget (CID := CID') A2 Rs0)
                        (sign_extend' 64 (mword_of_int 0xfe0 : mword 12)) = pa_stk sp0 4).
      { intros CID'; rgne. rewrite HA2s0. apply sfs_addr_st. }
      iEval (rewrite -(Haddrst CID16)) in "Hs4".
      iApply (wp_ld_s_sconf (CID := CID16) (mword_of_int (KernelSyms.sys_fstat + 0x26))
                Ra1 Rs0 (mword_of_int 0xfe0 : mword 12) A2 (av - 4)%nat v1 b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi26 Hs4").
      iIntros (CID17 Hs17) "Hcg Hpc Hs4".
      iEval (rewrite (Haddrst CID16)) in "Hs4".
      set (S1 := <[Regidx Ra1 := regval_into_reg v1]> A2).
      change (<[Regidx Ra1 := regval_into_reg v1]> A2) with S1.
      assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.sys_fstat + 0x26) : mword 64) 4
                      = mword_of_int (KernelSyms.sys_fstat + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2a) in "Hpc".
      assert (HS1s0 : S1 !!! Regidx Rs0 = sp0)
        by (rewrite /S1 upd_ne; [exact HA2s0 | reg_neq]).
      assert (HS1sp : S1 !!! Regidx csp_rs1 = pa_stk sp0 4)
        by (rewrite /S1 upd_ne; [exact HA2sp | reg_neq]).
      (* ---- +0x2a: ld a0,-24(s0) -- reload f ---- *)
      assert (Haddrf : forall CID' : CpuId,
                add_vec (rget (CID := CID') S1 Rs0)
                        (sign_extend' 64 (mword_of_int 0xfe8 : mword 12)) = pa_stk sp0 3).
      { intros CID'; rgne. rewrite HS1s0. apply sfs_addr_f. }
      iEval (rewrite HN4a2) in "Hfcell".
      iEval (rewrite -(Haddrf CID17)) in "Hfcell".
      iApply (wp_ld_s_sconf (CID := CID17) (mword_of_int (KernelSyms.sys_fstat + 0x2a))
                Ra0 Rs0 (mword_of_int 0xfe8 : mword 12) S1 (av - 4)%nat fv b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi2a Hfcell").
      iIntros (CID18 Hs18) "Hcg Hpc Hfcell".
      iEval (rewrite (Haddrf CID17)) in "Hfcell".
      set (S2 := <[Regidx Ra0 := regval_into_reg fv]> S1).
      change (<[Regidx Ra0 := regval_into_reg fv]> S1) with S2.
      assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.sys_fstat + 0x2a) : mword 64) 4
                      = mword_of_int (KernelSyms.sys_fstat + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2e) in "Hpc".
      assert (HS2s0 : S2 !!! Regidx Rs0 = sp0)
        by (rewrite /S2 upd_ne; [exact HS1s0 | reg_neq]).
      assert (HS2sp : S2 !!! Regidx csp_rs1 = pa_stk sp0 4)
        by (rewrite /S2 upd_ne; [exact HS1sp | reg_neq]).
      (* ---- +0x2e: jal ra,filestat ---- *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sys_fstat + 0x2e))
                Rra (mword_of_int 2093968 : mword 21) S2 (av - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi2e").
      iIntros (CID19 Hs19) "Hcg Hpc".
      set (S3 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.sys_fstat + 0x2e) : mword 64) 4)]> S2).
      change (<[Regidx Rra := regval_into_reg
                (add_vec_int (mword_of_int (KernelSyms.sys_fstat + 0x2e) : mword 64) 4)]> S2) with S3.
      assert (Hjfs : add_vec (mword_of_int (KernelSyms.sys_fstat + 0x2e) : mword 64)
                       (sign_extend' 64 (mword_of_int 2093968 : mword 21)) = mword_of_int KernelSyms.filestat)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjfs) in "Hpc".
      assert (HS3ra : S3 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KernelSyms.sys_fstat + 0x2e) : mword 64) 4)
        by (rewrite /S3 upd_eq; reflexivity).
      assert (HS3a0 : S3 !!! Regidx Ra0 = fv).
      { rewrite /S3 upd_ne; [| reg_neq]. rewrite /S2 upd_eq. reflexivity. }
      assert (HS3sp : S3 !!! Regidx csp_rs1 = pa_stk sp0 4)
        by (rewrite /S3 upd_ne; [exact HS2sp | reg_neq]).
      (* ---- THE B1 SEAM.  Lend the descriptor's reference out of the block,
         keep the core for filestat, and settle the loan when it returns. ---- *)
      iDestruct (proc_priv_lend γf pj pidv V fd fv Hlk Hfvnz with "Hpriv")
        as (kk qq Cf) "([%Hfvk %Hkk] & Href & Hcore & Howe)".
      assert (HS3a0' : S3 !!! Regidx Ra0 = fnode kk) by (rewrite HS3a0; exact Hfvk).
      iDestruct (sfs_env_frame fn Cf with "Henv") as "[Hfenv Hfback]".
      iDestruct (cpu_own_transport CID13 CID19 0%nat eb pj b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcpu") as "Hcpu".
      iApply (Filestat.wp_filestat_sconf γa γf γs j γlp kk qq Cf fn pidv V
                S3 (av - 4)%nat eb b lks
                ltac:(unfold filestat_stack; lia) Hkk Hj Hgs Hlens HS3a0' Heb
                with "Hcg Hcpu Htext Hpc Hpanic Href Hcore Hkenv Hprocs Hfenv").
      all: try lkbelow.
      iIntros (CID20 Hs20 mf rv P')
        "%Hcsf %Hupt %Hrvok %Hrva Hcg Hcpu Hpc Href Hcore Hfout".
      iDestruct ("Hfback" with "Hfout") as "Henv".
      (* SETTLE THE LOAN.  [pv_ofile (upd_upt V P') = pv_ofile V] by [cbn], so
         the deficit the lend opened is literally the one this closes. *)
      assert (Hlkk : pv_ofile V !! fd = Some (fnode kk))
        by (rewrite Hlk Hfvk; reflexivity).
      iDestruct (proc_ofiles_repay γf pj (pv_ofile V) ∅ fd kk qq Cf
                   ltac:(apply not_elem_of_empty) Hlkk Hkk with "[Howe] Href")
        as "Howe".
      { rewrite (union_empty_r_L {[fd]}). iExact "Howe". }
      iDestruct (proc_priv_join γf pj pidv (upd_upt V P') with "[Hcore] [Howe]")
        as "Hpriv".
      { iExact "Hcore". }
      { cbn [upd_upt pv_ofile]. iExact "Howe". }
      assert (Hpc32 : ret_pc (S3 !!! Regidx Rra)
                      = mword_of_int (KernelSyms.sys_fstat + 0x32))
        by (rewrite HS3ra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc32) in "Hpc".
      assert (HMfsp : mf !!! Regidx csp_rs1 = pa_stk sp0 4)
        by (rewrite (callee_saved_lookup Hcsf csp_rs1 ltac:(vm_compute; reflexivity)); exact HS3sp).
      assert (HthrF : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> mf !!! Regidx r = m !!! Regidx r).
      { intros r Hrcs Ncsp N8.
        assert (N1' : r <> mword_of_int 1)
          by (intro He; rewrite He in Hrcs; vm_compute in Hrcs; discriminate).
        assert (N10 : r <> mword_of_int 10)
          by (intro He; rewrite He in Hrcs; vm_compute in Hrcs; discriminate).
        assert (N11 : r <> mword_of_int 11)
          by (intro He; rewrite He in Hrcs; vm_compute in Hrcs; discriminate).
        rewrite (callee_saved_lookup Hcsf r Hrcs).
        rewrite /S3 upd_ne; [| congruence].
        rewrite /S2 upd_ne; [| congruence].
        rewrite /S1 upd_ne; [| congruence].
        apply HthrA; assumption. }
      iApply (sfs_tail (CID0 := CID20) m mf av rv sp0 ra0 s00 _ _ b pj
                ltac:(lia) eq_refl eq_refl eq_refl HMfsp Hrva HthrF
                with "Hcg Htext Hpc Hs1 Hs2 Hfcell Hs4").
      iIntros (CID21 Hs21 mg) "[%Hcsg %Hmga0] Hcg Hpc".
      iDestruct (cpu_own_transport CID20 CID21 0%nat eb pj b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcpu") as "Hcpu".
      iSpecialize ("Hcont" $! CID21 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mg rv P' with "[%] [%] [%] [%] Hcg Hcpu Hpc Hpriv Hkenv Henv").
      { exact Hcsg. }
      { exact Hupt. }
      { right. exists fd, fv. split; [exact Hsome | exact Hrvok]. }
      { exact Hmga0. }
  Qed.

End ProofSysFstat.

End SysFstatProof.
